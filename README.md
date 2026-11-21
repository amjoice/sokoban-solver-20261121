# Sokoban Solver — push-optimal, room by room

[![make.fun](https://make.fun/badge/sokoban-solver-01-run-20261121.svg)](https://make.fun/bounty/sokoban-solver-01-run-20261121)
[![rank](https://make.fun/badge/sokoban-solver-01-run-20261121/amjoice/sokoban-solver-20261121/rank.svg)](https://make.fun/bounty/sokoban-solver-01-run-20261121)
[![reward](https://make.fun/badge/sokoban-solver-01-run-20261121/amjoice/sokoban-solver-20261121/reward.svg)](https://make.fun/bounty/sokoban-solver-01-run-20261121)

A Sokoban solver for make.fun's
[Build the best Sokoban solver, 21 November 2026](https://make.fun/bounty/sokoban-solver-01-run-20261121)
bounty ($100 in USDC).

## How it works

Every level the generator draws is a hallway with one to four small rooms
off it, each room holding 3 or 4 boxes and as many goals, joined to the
hallway by a single door. A box pushed out of a room can never come back,
so every box stays in its room and the level's push optimum is the sum of
its rooms' optima. `main.ts` therefore splits each level into rooms and
solves every room on its own, push-optimally:

- **A\* over pushes.** A state is the boxes' squares plus the player's
  reachable region (canonicalised to its lowest square), so walks between
  pushes cost nothing in the search and never appear as states.
- **Exact push-distance estimate.** For each goal, a reverse 0-1 search
  over (box, player) states counts the pushes one box needs when the
  others are ignored. The cheapest assignment of boxes to goals under
  that table never overestimates, and already prices walls and detours.
- **Deadlock pruning.** Dead squares (no goal reachable), 2x2 blocks of
  wall and boxes, and frozen boxes are all pruned before they are queued.
- **Work budgets, never the clock.** The search is budgeted by
  expansions, so two runs on one set write the same bytes. If the optimal
  search runs out of budget on a room, a weighted search runs after it
  and the best solution found is kept.

The rooms' push lists are stitched together with plain walks: out of one
room's door, along the hallway, into the next room.

## Practice results

On the kit's practice set the solver answers all 5 instances in exactly
the push-optimal count (13, 16, 29, 47, 60 pushes), scoring 1,000,000
against the house baseline's 200,000, in about 0.3 s for the whole set.
It also scores 1,000,000 on freshly drawn sets from the kit's generator.

## Run

```sh
node main.ts   # reads /input/<id>/level.txt, writes /output/<id>/solution.txt
```

Node 22, no dependencies, no network. `main.ts` is the whole entry.
