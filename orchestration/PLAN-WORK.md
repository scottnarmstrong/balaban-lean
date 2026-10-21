# Work plan from 2026-10-20 21:40 UTC (Scott: "make a plan for actually doing work")

Constraints: 2 Opus + 2 Sonnet workers; 6 Lean compiles project-wide.
Measure of progress: the statements in docs/BLOCKERS.md "What closes each blocker", proved and merged.

## Slots
| Slot | Worker | Target statement | Next checkpoints |
|---|---|---|---|
| Opus 1 | W1146r | blocker 6: (A1)–(A5) on the local sets (A4-1b (iii), `SFNewLevelInput`) | rest of L4-3 → L4-4 → L5 → the theorem |
| Opus 2 | W1149r | blocker 1 (no-step): `KfZeroInput` via route FR | two-torus agreement → lift → parameters → `kfZeroInput_of_typing` |
| Sonnet 1 | W1148r | blocker 4 (vacuum): `RVacuumB0Input` via the `vacTie` field of `PreRec`; then A4-2ab (d)(e) | field + producers → `RVacuumB0Input` → (d)(e) |
| Sonnet 2 | W1151r | blocker 5 (small-field half): `FinalSmallFieldInput` except item (d) | A6-3 (a) → (c) → (e) → (b) |

When an Opus slot frees, in order: W1154 blocker 3 (`LFBdryOldInput`: build the old boundary terms, then P6 (4.34)); W1156 removal-history audit (decides whether blockers 4–5 are stated correctly; ruling to Scott); W1155 blocker 4 window estimates (P7 (2.11)–(2.16)); W1152 blocker 7; then blocker 2 (switch at k₀, source radius).
When a Sonnet slot frees: the remaining bounded rows of the blocker inputs (A4-2ab kept, gas, (f); A6-3 (c)/(e) if not done; LFBdryInput parts (i), (ii)).

## Discipline
- Every worker hands off a piece as soon as its modules build; I land it within 30 minutes (one landing queue, seeding all worktrees after each landing).
- Workers never wait idle on a build; after every merge of main they seed from main.
- Hourly check: a worker with no commit for 90 minutes gets a direct intervention (find the blocker; split the task).
- Status reports name only proved, merged statements, and the next checkpoint.
