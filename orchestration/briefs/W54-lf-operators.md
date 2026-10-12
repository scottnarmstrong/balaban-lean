# Brief W54 — large fields, Lean block J1–J2: variables, reference measure, kernels and the bound (1.26)

**Goal.** Formalize items J1–J2 of `notes/phase1/LF-RECONSTRUCTION.md` §II.L (Part II §II.5, as amended
in v1.2 / Part IV): J1 `InternalVars` (the index sets of the internal variables of a localized history,
`Fintype`), `refMeasure` (the reference measure: `aprioriMeasure` on spins × Lebesgue on the other
variables; v1.2 D-IV.4: `toSphere`, total mass `N v_N`, not normalized), `multiscaleField` (II.3)
(Def II.5.1); J2 `LFKernel` (structure: non-negative Borel kernel `K`, factor `e^b` with `b` analytic in
`g` — the P2-04 convention: operators depend on `g` only through `e^b`), `LFKernel.op`, `Bound126`
(P5 (1.26) in the v1.2 form with Gaussian witness functions `F^w_k(u)` and measures `m^w_k` — read
Part IV D-IV.3 and the amended (S1)–(S2)), `LFKernel.comp`, `LFKernel.tensor`, `op_comm`, and
**Lemma II.5.3** (products and compositions of operators: the bound (1.26) is preserved, in the
integration order of the v1.1 fix P2-06). Build on the landed `Balaban/Frozen/Model/AprioriMeasure.lean`
(`aprioriMeasure`), `Balaban/LargeField/History/*` (histories, localized histories), Mathlib measure
theory.

**Ownership.** New files under `Balaban/LargeField/Operators/` in your worktree
`/home/scott/Balaban-worktrees/W54` (branch `w54-lf-operators`), plus import lines in `Balaban.lean`.
Workers W50 (`LargeField/Analytic/Constants.lean`, `LargeField/LF1.lean`) and W51
(`LargeField/Background/*`) are active: do not touch their files. Never import `Balaban/Frozen/Roots/*`
or `Balaban/Provider/*` (importing `Balaban/Frozen/Model/*` definitions is fine).

**Checks.** Before handoff merge the current `main` and build the whole default target
(`lake build`; AGENTS.md rule 8; at most one build at a time; compiles are throttled machine-wide
and may wait; never bypass the throttle); zero warnings; `#print axioms` standard;
`python3 -I scripts/check_lean_modules.py --root .`; no name clashes (search `Balaban/` first).

**Stop condition.** J1–J2 with Lemma II.5.3, or about 2,000 lines, or a precise obstruction.

**Do not launch subagents (no Agent tool); work directly.**

**Hard rules** (from `AGENTS.md`): every `.lean` file is a module; no `axiom`, no `sorry`/`admit`,
no heartbeat overrides, no placeholder definitions, zero warnings; frozen files read-only; no file
over 10,000 lines; commit on your branch only, never push to `main`.

**Handoff.** Files; definitions (full text of `LFKernel` and `Bound126`); main theorem names with
statements; checks and results; axioms; last commit hash.
