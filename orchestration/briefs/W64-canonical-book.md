# Brief W64 — large fields: bookkeeping as a function of the localized record (hpos)

**Goal.** The landed labelled summability `sum_inv_logC_labelled` (`Balaban/LargeField/Budget/Labelled.lean`,
W61) assumes `hpos`: the positions (and labels) of the kept ripe components are a function of the localized
record `a = localHistory H M K k Y`. `notes/phase1/LF-RECONSTRUCTION.md` gets this from deterministic
bookkeeping (Def I.4.7, R3-12, O-9: "the bookkeeping is a function of the region history"), but in Lean the
spines in `RegionHistory.nextSpine` are chosen with `Classical.choose` on data that may involve the whole
history, so ripeness is not visibly a function of the localized record.
1. Refactor (or add a canonical variant of) the spine choice and the book (`nextSpine`, `nextBook`,
   `Setting.nextBook`, `bk`, `pb` in `Balaban/LargeField/History/*`) so that the spine, clock and window
   state of a component at scale `k` are functions of the localized record of that component (its lineage:
   W55's `locRH`, W59's `localHistory`) — e.g. choose spines by `Classical.choose` applied to an
   existence statement whose parameters are exactly the local data; then prove `IsRipe`/kept positions are
   functions of the localized record.
2. Discharge `hpos` and state the labelled summability without it.
3. Re-check that `RegionHistory.toLF2Hyp`, `toLF2HypBudget`, `ripe_window`, `cover_inv` still hold (with
   the canonical choice) — keep their statements.

**Ownership.** Edits to `Balaban/LargeField/History/*`, `Balaban/LargeField/Counter/Instantiation*.lean`,
`Balaban/LargeField/Budget/*` and new files there, in your worktree `/home/scott/Balaban-worktrees/W64`
(branch `w64-canonical-book`). Worker W60 writes `Balaban/LargeField/Operators/*`: do not touch. Never
import `Balaban/Frozen/Roots/*` or `Balaban/Provider/*`.

**Checks.** Before handoff merge the current `main` and build the whole default target (`lake build`;
AGENTS.md rule 8; at most one build at a time; throttled; never bypass); zero warnings; `#print axioms`
standard; `python3 -I scripts/check_lean_modules.py --root .`; no name clashes.

**Stop condition.** Items 1–3, or about 2,500 lines changed, or a precise obstruction.

**Do not launch subagents (no Agent tool); work directly.**

**Hard rules** (from `AGENTS.md`): every `.lean` file is a module; no `axiom`, no `sorry`/`admit`,
no heartbeat overrides, no placeholder definitions, zero warnings; frozen files read-only; no file
over 10,000 lines; commit on your branch only, never push to `main`.

**Handoff.** Files; what changed; the new labelled summability statement; checks; axioms; last commit hash.
