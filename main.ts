// Room-decomposed push-optimal Sokoban solver.
//
// One program answers a set of 5 levels in a single run. Every level the
// generator draws is a hallway with one to four small rooms off it, each
// room holding 3 or 4 boxes and as many goals, joined to the hallway by a
// single door. A box pushed out of a room can never come back, so every box
// stays in its room and the level's push optimum is the sum of its rooms'
// optima. This program therefore splits each level into rooms and solves
// every room on its own, push-optimally, with A* over pushes:
//
//   * a state is the boxes' squares plus the player's reachable region
//     (canonicalised to its lowest square), so walks between pushes cost
//     nothing in the search and never appear as states;
//   * the estimate is the cheapest assignment of boxes to goals under the
//     exact single-box push distance (a reverse 0-1 search per goal, which
//     counts the pushes one box needs when the others are ignored), so it
//     never overestimates and already prices walls and detours;
//   * dead squares (no goal reachable), 2x2 blocks and frozen boxes prune
//     positions no push can save, before they are ever queued;
//   * the search is budgeted by expansions, never by the clock, so two runs
//     on one set write the same bytes.
//
// The rooms' push lists are then stitched together with plain walks: out of
// one room's door, along the hallway, into the next room. Walks are shortest
// paths found by breadth-first search in a fixed neighbour order.
//
// If the optimal search runs out of budget on a room, a weighted search runs
// after it and the best solution found is kept: a slightly long solution is
// still worth about half the instance's points, an unsolved one none.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

const INPUT = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const OUTPUT = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';

// Neighbour order is fixed everywhere (up, down, left, right): the program
// is deterministic, two runs on one set write the same bytes.
const DX = [0, 0, -1, 1];
const DY = [-1, 1, 0, 0];
const LETTER = ['u', 'd', 'l', 'r'];
const OPP = [1, 0, 3, 2];
const INF = 1e9;

// Work budgets (expansions, never seconds: the run must not read a clock).
const ASTAR_BUDGET = 400000;
const WEIGHTED_BUDGET = 150000;
const GREEDY_BUDGET = 150000;
const GLOBAL_BUDGET = 4000000;

const spent = { n: 0 };

// ---------------------------------------------------------------------------
// Small helpers
// ---------------------------------------------------------------------------

/** A binary heap of [priority, g, node] ordered by priority, then deeper g, then node. */
class Heap {
  a: number[][] = [];
  get size(): number {
    return this.a.length;
  }
  push(e: number[]): void {
    const a = this.a;
    let i = a.length;
    a.push(e);
    while (i > 0) {
      const p = (i - 1) >> 1;
      if (Heap.less(a[i]!, a[p]!)) {
        const t = a[i]!;
        a[i] = a[p]!;
        a[p] = t;
        i = p;
      } else break;
    }
  }
  pop(): number[] {
    const a = this.a;
    const top = a[0]!;
    const last = a.pop()!;
    if (a.length > 0) {
      a[0] = last;
      for (let i = 0; ; ) {
        let c = 2 * i + 1;
        if (c >= a.length) break;
        if (c + 1 < a.length && Heap.less(a[c + 1]!, a[c]!)) c++;
        if (!Heap.less(a[c]!, a[i]!)) break;
        const t = a[i]!;
        a[i] = a[c]!;
        a[c] = t;
        i = c;
      }
    }
    return top;
  }
  static less(x: number[], y: number[]): boolean {
    return x[0] < y[0] || (x[0] === y[0] && (x[1] > y[1] || (x[1] === y[1] && x[2] < y[2])));
  }
}

/** All permutations of 0..k-1, for the assignment estimate (k is 3 or 4). */
function permutations(k: number): number[][] {
  const out: number[][] = [];
  const cur: number[] = [];
  const used = new Uint8Array(k);
  const rec = (): void => {
    if (cur.length === k) {
      out.push(cur.slice());
      return;
    }
    for (let i = 0; i < k; i++) {
      if (used[i]) continue;
      used[i] = 1;
      cur.push(i);
      rec();
      cur.pop();
      used[i] = 0;
    }
  };
  rec();
  return out;
}

// ---------------------------------------------------------------------------
// Level parsing and room splitting
// ---------------------------------------------------------------------------

interface Level {
  w: number;
  h: number;
  wall: Uint8Array;
  goals: number[];
  boxes: number[];
  player: number;
}

function parseLevel(text: string): Level {
  const rows = text.split('\n').filter((r) => r.length > 0);
  const w = Math.max(...rows.map((r) => r.length));
  const h = rows.length;
  const wall = new Uint8Array(w * h).fill(1);
  const goals: number[] = [];
  const boxes: number[] = [];
  let player = 0;
  rows.forEach((row, y) => {
    for (let x = 0; x < w; x++) {
      const ch = row[x] ?? '#';
      const i = y * w + x;
      if (ch === '#') continue;
      wall[i] = 0;
      if (ch === '.' || ch === '*' || ch === '+') goals.push(i);
      if (ch === '$' || ch === '*') boxes.push(i);
      if (ch === '@' || ch === '+') player = i;
    }
  });
  boxes.sort((a, b) => a - b);
  return { w, h, wall, goals, boxes, player };
}

/**
 * Split a level into its rooms. The hallway is the player's row; removing
 * it leaves one connected component per room, each with one door cell next
 * to the hallway and as many boxes as goals. Returns null when the shape is
 * not a hallway with rooms, so the caller can fall back to the whole level.
 */
function splitRooms(lv: Level): { cells: number[]; door: number; entry: number }[] | null {
  const hallRow = Math.floor(lv.player / lv.w);
  const seen = new Uint8Array(lv.w * lv.h);
  const rooms: { cells: number[]; door: number; entry: number }[] = [];
  for (let s = 0; s < lv.w * lv.h; s++) {
    if (Math.floor(s / lv.w) === hallRow || lv.wall[s] || seen[s]) continue;
    const cells: number[] = [];
    const stack = [s];
    seen[s] = 1;
    while (stack.length > 0) {
      const c = stack.pop()!;
      cells.push(c);
      const x = c % lv.w;
      const y = Math.floor(c / lv.w);
      for (let d = 0; d < 4; d++) {
        const nx = x + DX[d];
        const ny = y + DY[d];
        if (nx < 0 || nx >= lv.w || ny < 0 || ny >= lv.h) continue;
        const q = ny * lv.w + nx;
        if (ny === hallRow || lv.wall[q] || seen[q]) continue;
        seen[q] = 1;
        stack.push(q);
      }
    }
    const boxes = cells.filter((c) => lv.boxes.includes(c)).length;
    const goals = cells.filter((c) => lv.goals.includes(c)).length;
    if (boxes === 0 || boxes !== goals) return null;
    const doors = cells.filter((c) => Math.abs(Math.floor(c / lv.w) - hallRow) === 1);
    if (doors.length !== 1) return null;
    const door = doors[0]!;
    const entry = hallRow * lv.w + (door % lv.w);
    if (lv.wall[entry]) return null;
    rooms.push({ cells, door, entry });
  }
  if (rooms.length === 0) return null;
  if (rooms.reduce((a, r) => a + r.cells.filter((c) => lv.boxes.includes(c)).length, 0) !== lv.boxes.length) return null;
  rooms.sort((a, b) => {
    const ay = Math.min(...a.cells.map((c) => Math.floor(c / lv.w)));
    const by = Math.min(...b.cells.map((c) => Math.floor(c / lv.w)));
    if (ay !== by) return ay - by;
    return Math.min(...a.cells) - Math.min(...b.cells);
  });
  return rooms;
}

// ---------------------------------------------------------------------------
// One room: push-optimal A* over pushes
// ---------------------------------------------------------------------------

interface Room {
  n: number; // local cells: the room's floor plus the hallway square outside its door
  w: number; // the level's width, for the 2x2 test's global coordinates
  h: number; // the level's height
  nbr: Int32Array; // n * 4, neighbour local index or -1
  boxCell: Uint8Array; // 1 where a box may rest (the room's own floor, never the hallway square)
  isGoal: Uint8Array;
  goals: number[]; // local goal cells
  boxes0: number[]; // local start boxes, sorted
  entry: number; // local index of the hallway square outside the door
  g2l: Int32Array; // global cell -> local index, -1 outside the room
  l2g: number[]; // local index -> global cell
  dist: Int32Array; // n * goals.length: exact single-box push distance to each goal
  dead: Uint8Array; // 1 where a box can reach no goal
  perms: number[][];
  hCache: Map<number, number>;
}

function buildRoom(lv: Level, room: { cells: number[]; door: number; entry: number }): Room {
  const cells = room.cells.slice();
  const g2l = new Int32Array(lv.w * lv.h).fill(-1);
  cells.forEach((c, i) => {
    g2l[c] = i;
  });
  // The hallway square outside the door is an extra local cell, unless it
  // is already one of the floor cells (the whole-level fallback).
  const already = g2l[room.entry];
  const entry = already >= 0 ? already : cells.length;
  if (already < 0) g2l[room.entry] = entry;
  const l2g = already >= 0 ? cells.slice() : cells.concat([room.entry]);
  const n = l2g.length;
  const nbr = new Int32Array(n * 4).fill(-1);
  const boxCell = new Uint8Array(n);
  for (let i = 0; i < cells.length; i++) boxCell[i] = 1;
  const isGoal = new Uint8Array(n);
  const goals: number[] = [];
  for (const g of lv.goals) {
    const li = g2l[g];
    if (li >= 0 && li < cells.length) {
      isGoal[li] = 1;
      goals.push(li);
    }
  }
  goals.sort((a, b) => a - b);
  const boxes0 = lv.boxes.filter((b) => g2l[b] >= 0 && g2l[b] < cells.length).map((b) => g2l[b]);
  boxes0.sort((a, b) => a - b);
  for (let i = 0; i < n; i++) {
    const g = l2g[i]!;
    const x = g % lv.w;
    const y = Math.floor(g / lv.w);
    for (let d = 0; d < 4; d++) {
      const nx = x + DX[d];
      const ny = y + DY[d];
      if (nx < 0 || nx >= lv.w || ny < 0 || ny >= lv.h) continue;
      const q = ny * lv.w + nx;
      const li = g2l[q];
      if (li >= 0) nbr[i * 4 + d] = li;
    }
  }
  // Exact single-box push distance to each goal: a reverse 0-1 search over
  // (box, player) states. From the goal with the player anywhere (cost 0),
  // walking is free and undoing a push costs 1.
  const G = goals.length;
  const dist = new Int32Array(n * G).fill(INF);
  const stateDist = new Int32Array(n * n).fill(INF);
  const deque: number[] = [];
  for (let gi = 0; gi < G; gi++) {
    const goal = goals[gi]!;
    stateDist.fill(INF);
    deque.length = 0;
    let head = 0;
    for (let p = 0; p < n; p++) {
      if (p === goal) continue;
      const s = goal * n + p;
      stateDist[s] = 0;
      deque.push(s);
    }
    while (head < deque.length) {
      const s = deque[head++]!;
      const b = Math.floor(s / n);
      const p = s % n;
      const cur = stateDist[s]!;
      // Walk the player, free: to any neighbouring floor square but the box's.
      for (let d = 0; d < 4; d++) {
        const q = nbr[p * 4 + d]!;
        if (q < 0 || q === b) continue;
        const ns = b * n + q;
        if (stateDist[ns]! > cur) {
          stateDist[ns] = cur;
          deque.splice(head, 0, ns);
        }
      }
      // Undo a push: the box was at p, pushed in direction d to b, so the
      // player stood at p's far side in direction d.
      if (!boxCell[p]) continue;
      for (let d = 0; d < 4; d++) {
        if (nbr[b * 4 + OPP[d]]! !== p) continue;
        const prevPlayer = nbr[p * 4 + OPP[d]]!;
        if (prevPlayer < 0) continue;
        const ns = p * n + prevPlayer;
        if (stateDist[ns]! > cur + 1) {
          stateDist[ns] = cur + 1;
          deque.push(ns);
        }
      }
    }
    for (let c = 0; c < n; c++) {
      let best = INF;
      for (let p = 0; p < n; p++) {
        if (p === c) continue;
        const v = stateDist[c * n + p]!;
        if (v < best) best = v;
      }
      dist[c * G + gi] = best;
    }
  }
  const dead = new Uint8Array(n);
  for (let c = 0; c < n; c++) {
    let any = false;
    for (let gi = 0; gi < G; gi++) if (dist[c * G + gi]! < INF) any = true;
    if (!any) dead[c] = 1;
  }
  return {
    n, w: lv.w, h: lv.h, nbr, boxCell, isGoal, goals, boxes0, entry, g2l, l2g,
    dist, dead, perms: permutations(G), hCache: new Map(),
  };
}

/** Cheapest assignment of boxes to goals under the push-distance table. */
function heuristic(r: Room, packed: number): number {
  const hit = r.hCache.get(packed);
  if (hit !== undefined) return hit;
  const k = r.goals.length;
  const boxes: number[] = [];
  for (let i = 0; i < k; i++) boxes.push((packed >> (6 * i)) & 63);
  const G = r.goals.length;
  let best = INF;
  for (const perm of r.perms) {
    let sum = 0;
    let ok = true;
    for (let i = 0; i < k; i++) {
      const d = r.dist[boxes[i]! * G + perm[i]!]!;
      if (d >= INF) {
        ok = false;
        break;
      }
      sum += d;
    }
    if (ok && sum < best) best = sum;
  }
  r.hCache.set(packed, best);
  return best;
}

function packBoxes(boxes: number[]): number {
  let p = 0;
  for (let i = 0; i < boxes.length; i++) p |= boxes[i]! << (6 * i);
  for (let i = boxes.length; i < 4; i++) p |= 63 << (6 * i);
  return p;
}

/** The player's reachable region from `from` given the boxes; returns its lowest cell. */
function regionMin(r: Room, from: number, boxSet: Uint8Array): number {
  const seen = new Uint8Array(r.n);
  const stack = [from];
  seen[from] = 1;
  let min = from;
  while (stack.length > 0) {
    const c = stack.pop()!;
    if (c < min) min = c;
    for (let d = 0; d < 4; d++) {
      const q = r.nbr[c * 4 + d]!;
      if (q < 0 || seen[q] || boxSet[q]) continue;
      seen[q] = 1;
      stack.push(q);
    }
  }
  return min;
}

/** The player's reachable region as a mask, for push generation. */
function regionMask(r: Room, from: number, boxSet: Uint8Array): Uint8Array {
  const seen = new Uint8Array(r.n);
  const stack = [from];
  seen[from] = 1;
  while (stack.length > 0) {
    const c = stack.pop()!;
    for (let d = 0; d < 4; d++) {
      const q = r.nbr[c * 4 + d]!;
      if (q < 0 || seen[q] || boxSet[q]) continue;
      seen[q] = 1;
      stack.push(q);
    }
  }
  return seen;
}

/**
 * True when the boxes hold a position no push can save:
 * a box on a dead square, a box frozen inside a 2x2 block of wall and
 * boxes, or a box frozen by walls and frozen boxes on every side.
 * Every test here is sound: it never fires on a position that can still
 * be solved.
 */
function isDead(r: Room, boxes: number[], boxSet: Uint8Array): boolean {
  for (const b of boxes) if (r.dead[b]) return true;
  // 2x2 blocks: a box in a 2x2 square of wall-or-box can never move, since
  // two of its neighbours are blocked both as targets and as stands.
  // A cell counts as blocking when it is no floor square of this room at
  // all (the hallway square counts as free: the player can stand there).
  for (const b of boxes) {
    if (r.isGoal[b]) continue;
    const g = r.l2g[b]!;
    const x = g % r.w;
    const y = (g / r.w) | 0;
    for (let oy = -1; oy <= 0; oy++) {
      for (let ox = -1; ox <= 0; ox++) {
        let blocked = 0;
        for (let dy = 0; dy < 2; dy++) {
          for (let dx = 0; dx < 2; dx++) {
            const cx = x + ox + dx;
            const cy = y + oy + dy;
            if (cx < 0 || cy < 0 || cx >= r.w || cy >= r.h) {
              blocked++;
              continue;
            }
            const cell = cy * r.w + cx;
            const li = cell < r.g2l.length ? r.g2l[cell] : -1;
            if (li < 0 || boxSet[li]) blocked++;
          }
        }
        if (blocked === 4) return true;
      }
    }
  }
  // Frozen boxes: iterate to a fixpoint. A box is frozen when every push
  // is blocked by a wall or a frozen box, on the target side or the stand
  // side. A frozen box off its goal can never be solved.
  const frozen = new Uint8Array(r.n);
  let changed = true;
  while (changed) {
    changed = false;
    for (const b of boxes) {
      if (frozen[b] || r.isGoal[b]) continue;
      let stuck = true;
      for (let d = 0; d < 4; d++) {
        const t = r.nbr[b * 4 + d]!;
        const s = r.nbr[b * 4 + OPP[d]]!;
        const tBlocked = t < 0 || frozen[t] === 1;
        const sBlocked = s < 0 || frozen[s] === 1;
        if (!tBlocked && !sBlocked) {
          stuck = false;
          break;
        }
      }
      if (stuck) {
        frozen[b] = 1;
        changed = true;
      }
    }
  }
  for (const b of boxes) if (frozen[b] && !r.isGoal[b]) return true;
  return false;
}

interface SearchResult {
  pushes: { box: number; dir: number }[];
  optimal: boolean;
}

/**
 * A* over pushes for one room. `weight` scales the estimate: 1 is the
 * optimal search, more is a weighted search that finds a solution sooner
 * without proving it cheapest. Returns the best solution found within the
 * expansion budget, or null when none was found.
 */
function searchRoom(r: Room, budget: number, weight: number): SearchResult | null {
  const k = r.goals.length;
  const startPacked = packBoxes(r.boxes0);
  if (r.boxes0.every((b) => r.isGoal[b])) return { pushes: [], optimal: true };
  const startH = heuristic(r, startPacked);
  if (startH >= INF) return null;

  // Node storage: packed boxes, canonical player, g, parent, push that made it.
  const packs: number[] = [startPacked];
  const players: number[] = [regionMin(r, r.entry, boxesToSet(r, r.boxes0))];
  const gs: number[] = [0];
  const parents: number[] = [-1];
  const moves: number[] = [-1]; // box * 4 + dir, -1 at the root
  const best = new Map<number, number>();
  best.set(startPacked | (players[0]! << 24), 0);
  const heap = new Heap();
  heap.push([startH * weight, 0, 0]);

  const boxSet = new Uint8Array(r.n);
  const nbSet = new Uint8Array(r.n);
  let bestGoal: number[] | null = null;
  let bestGoalG = INF;
  let expanded = 0;

  while (heap.size > 0 && expanded < budget && spent.n < GLOBAL_BUDGET) {
    const [, g, u] = heap.pop();
    const key = packs[u]! | (players[u]! << 24);
    if (best.get(key) !== u) continue;
    if (gs[u] !== g) continue;
    expanded++;
    spent.n++;
    const boxes = unpackBoxes(packs[u]!, k);
    if (boxes.every((b) => r.isGoal[b])) {
      return { pushes: tracePushes(u, parents, moves), optimal: weight === 1 };
    }
    // The player's region from the canonical square, with these boxes.
    for (let i = 0; i < r.n; i++) boxSet[i] = 0;
    for (const b of boxes) boxSet[b] = 1;
    const region = regionMask(r, players[u]!, boxSet);
    for (const b of boxes) {
      for (let d = 0; d < 4; d++) {
        const t = r.nbr[b * 4 + d]!;
        if (t < 0 || !r.boxCell[t] || boxSet[t]) continue;
        const s = r.nbr[b * 4 + OPP[d]]!;
        if (s < 0 || !region[s]) continue;
        const nb = boxes.slice();
        nb[nb.indexOf(b)] = t;
        nb.sort((a, b2) => a - b2);
        const np = packBoxes(nb);
        for (let i = 0; i < r.n; i++) nbSet[i] = 0;
        for (const x of nb) nbSet[x] = 1;
        if (isDead(r, nb, nbSet)) continue;
        const h = heuristic(r, np);
        if (h >= INF) continue;
        const nPlayer = regionMin(r, b, nbSet);
        const nKey = np | (nPlayer << 24);
        const ng = g + 1;
        const seen = best.get(nKey);
        if (seen !== undefined && gs[seen]! <= ng) continue;
        const idx = packs.length;
        packs.push(np);
        players.push(nPlayer);
        gs.push(ng);
        parents.push(u);
        moves.push(b * 4 + d);
        best.set(nKey, idx);
        heap.push([ng + h * weight, ng, idx]);
        if (nb.every((x) => r.isGoal[x]) && ng < bestGoalG) {
          bestGoalG = ng;
          bestGoal = tracePushes(idx, parents, moves);
        }
      }
    }
  }
  if (bestGoal !== null) return { pushes: bestGoal, optimal: false };
  return null;
}

function boxesToSet(r: Room, boxes: number[]): Uint8Array {
  const s = new Uint8Array(r.n);
  for (const b of boxes) s[b] = 1;
  return s;
}

function unpackBoxes(packed: number, k: number): number[] {
  const out: number[] = [];
  for (let i = 0; i < k; i++) out.push((packed >> (6 * i)) & 63);
  return out;
}

function tracePushes(u: number, parents: number[], moves: number[]): { box: number; dir: number }[] {
  const out: { box: number; dir: number }[] = [];
  for (let t = u; t > 0; t = parents[t]!) {
    const m = moves[t]!;
    out.push({ box: (m / 4) | 0, dir: m % 4 });
  }
  out.reverse();
  return out;
}

/** Solve one room: optimal search first, weighted and greedy after it. */
function solveRoom(r: Room): { box: number; dir: number }[] | null {
  let res = searchRoom(r, ASTAR_BUDGET, 1);
  if (res !== null && res.optimal) return res.pushes;
  let bestRes: SearchResult | null = res;
  res = searchRoom(r, WEIGHTED_BUDGET, 4);
  if (res !== null && (bestRes === null || res.pushes.length < bestRes.pushes.length)) bestRes = res;
  if (bestRes !== null && bestRes.optimal) return bestRes.pushes;
  if (bestRes === null) {
    res = searchRoom(r, GREEDY_BUDGET, 100);
    if (res !== null) bestRes = res;
  }
  return bestRes === null ? null : bestRes.pushes;
}

// ---------------------------------------------------------------------------
// Stitching rooms together with walks
// ---------------------------------------------------------------------------

/** Shortest walk from `from` to `to` on the level, never stepping on a box. */
function walkPath(lv: Level, from: number, to: number, boxes: number[]): string | null {
  if (from === to) return '';
  const blocked = new Uint8Array(lv.w * lv.h);
  for (let i = 0; i < lv.w * lv.h; i++) blocked[i] = lv.wall[i];
  for (const b of boxes) blocked[b] = 1;
  blocked[from] = 0;
  const prev = new Int32Array(lv.w * lv.h).fill(-2);
  const prevDir = new Int8Array(lv.w * lv.h);
  prev[from] = -1;
  const queue = [from];
  for (let qi = 0; qi < queue.length; qi++) {
    const c = queue[qi]!;
    if (c === to) break;
    const x = c % lv.w;
    const y = (c / lv.w) | 0;
    for (let d = 0; d < 4; d++) {
      const nx = x + DX[d];
      const ny = y + DY[d];
      if (nx < 0 || nx >= lv.w || ny < 0 || ny >= lv.h) continue;
      const q = ny * lv.w + nx;
      if (blocked[q] || prev[q] !== -2) continue;
      prev[q] = c;
      prevDir[q] = d;
      queue.push(q);
    }
  }
  if (prev[to] === -2) return null;
  let out = '';
  for (let c = to; c !== from; c = prev[c]!) out = LETTER[prevDir[c]!] + out;
  return out;
}

/** Solve one whole level: split into rooms, solve each, stitch with walks. */
function solveLevel(text: string): string {
  const lv = parseLevel(text);
  const rooms = splitRooms(lv);
  if (rooms === null) return '';
  const boxes = lv.boxes.slice();
  let player = lv.player;
  let moves = '';

  for (const roomSpec of rooms) {
    const r = buildRoom(lv, roomSpec);
    if (r.n >= 63) return '';
    const pushes = solveRoom(r);
    if (pushes === null) return '';
    // Walk to the hallway square outside this room's door.
    const w1 = walkPath(lv, player, roomSpec.entry, boxes);
    if (w1 === null) return '';
    moves += w1;
    player = roomSpec.entry;
    // Each push: walk to the stand square, then push.
    for (const { box, dir } of pushes) {
      const gBox = r.l2g[box]!;
      const stand = gBox - DY[dir] * lv.w - DX[dir];
      const w2 = walkPath(lv, player, stand, boxes);
      if (w2 === null) return '';
      moves += w2;
      moves += LETTER[dir];
      const nb = gBox + DY[dir] * lv.w + DX[dir];
      const at = boxes.indexOf(gBox);
      boxes[at] = nb;
      boxes.sort((a, b) => a - b);
      player = gBox;
    }
  }
  return moves;
}

// ---------------------------------------------------------------------------
// Entry point: one run answers every instance in the input directory.
// ---------------------------------------------------------------------------

for (const id of readdirSync(INPUT).sort()) {
  const moves = solveLevel(readFileSync(join(INPUT, id, 'level.txt'), 'utf8'));
  mkdirSync(join(OUTPUT, id), { recursive: true });
  writeFileSync(join(OUTPUT, id, 'solution.txt'), `${moves}\n`);
}

