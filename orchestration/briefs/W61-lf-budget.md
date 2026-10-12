# Brief W61 — large fields, Lean block K1, K2, K5: exponents, Lemma B, summability (1.27)

**Goal.** Formalize items K1, K2, K5 of `notes/phase1/LF-RECONSTRUCTION.md` §II.L (Part II §II.5): K1
`kappaStep`, `kappa`, `logC`, `budgetG` (Def II.5.11; κ, C, G along a localized history), K2 **`lemmaB`**
(Lemma II.5.12: the budget recursion including hull cubes — this is the (B) hypothesis of the landed
`RegionHistory.toLF2Hyp`; state it in exactly the form of `toLF2Hyp`'s `budget` argument so it can be
plugged in), K5 `sum_inv_logC_le_one` (Lemma II.5.15: the summability (1.27) over localized histories,
including kept labels; four region families). Use the landed running constants
(`Balaban/LargeField/Analytic/Constants.lean`), the history and counter layers
(`Balaban/LargeField/History/*`, `Balaban/LargeField/Counter/*`: `LF2Hyp`, `toLF2Hyp`, `Setting`, the
cost functions), and Part I's constants. K3/K4 are not in this package (they depend on block J, being
written by W60).

**Ownership.** New files under `Balaban/LargeField/Budget/` in your worktree
`/home/scott/Balaban-worktrees/W61` (branch `w61-lf-budget`), plus import lines. Worker W60 writes
`Balaban/LargeField/Operators/*`: do not touch. Never import `Balaban/Frozen/Roots/*` or
`Balaban/Provider/*`.

**Checks.** Before handoff merge the current `main` and build the whole default target (`lake build`;
AGENTS.md rule 8; at most one build at a time; throttled; never bypass); zero warnings; `#print axioms`
standard; `python3 -I scripts/check_lean_modules.py --root .`; no name clashes.

**Stop condition.** K1, K2, K5, or about 2,000 lines, or a precise obstruction.

**Do not launch subagents (no Agent tool); work directly.**

**Hard rules** (from `AGENTS.md`): every `.lean` file is a module; no `axiom`, no `sorry`/`admit`,
no heartbeat overrides, no placeholder definitions, zero warnings; frozen files read-only; no file
over 10,000 lines; commit on your branch only, never push to `main`.

**Handoff.** Files; definitions; main theorem names with statements (full statement of `lemmaB`);
checks; axioms; last commit hash.
