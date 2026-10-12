# Brief W50 — large fields, Lean blocks F and I: running constants and LF-1 (action lower bound)

**Goal.** Formalize blocks **F** and **I** of `notes/phase1/LF-RECONSTRUCTION.md` §II.L (Part II, as
amended by v1.2 / Part IV):
- **F** (`Balaban/LargeField/Analytic/Constants.lean`): F1 `runLam`, `runR`, `pZero`, `pOne`, `deltaRun`,
  `epsRun`, `bgMass`, `betaCanon`, `kZero` (the **a-priori** regime index of Part IV D-IV.11:
  `k₀ := max{k : βνL^{kd} ≤ 1}`), `kZeroGenuine`, `kF` (Def II.1.1 as amended); F2 Lemma II.1.2
  (`runLam_le_hat`, `hat_le_runLam_add_two`, `runR_ge_base`, `logBeta_ge`, `gain_conv`,
  `logBeta_succ_le`) from the landed `Balaban/Flow/RunningCoefficients.lean` (`betaSeq_eq`,
  `norm_gammaSeq_le`); F3 the conditions (Λ15)–(Λ17).
- **I** (`Balaban/LargeField/LF1.lean`): **LF-1, Theorem II.4.1** (P6 Prop 3.1 for hard spins,
  γ₀ = 1/(28d), no condition on the multiplier) with Lemmas II.4.2–II.4.3 (`adjacent_blockAvg_sq_le`,
  `hardSpin_one_sub_sq_le`) from the landed `Balaban.Multiscale.blockPoincare_sharp`, and the action
  `actionG` on a `GeneratingSet` with admissible weights (`IsAdmissibleWeights`): the gradient bound
  (`lf1_gradient`) and the hard-spin bound (`lf1_hardSpin`) exactly as stated in Theorem II.4.1.

If a statement of the document is false as printed, stop that item and report it with a counterexample.

**Ownership.** New files `Balaban/LargeField/Analytic/Constants.lean`, `Balaban/LargeField/LF1.lean`
(and helpers) in your worktree `/home/scott/Balaban-worktrees/W50` (branch `w50-lf-constants-lf1`),
plus import lines in `Balaban.lean`. Worker W48 is writing `Balaban/LargeField/History/*` (new files)
and `Balaban/LargeField/Counter/Instantiation*.lean`; do not touch those. Never import
`Balaban/Frozen/Roots/*` or `Balaban/Provider/*`.

**Checks.** Before handoff merge the current `main` and build the whole default target
(`lake build`; AGENTS.md rule 8; at most one build at a time; compiles are throttled machine-wide
and may wait; never bypass the throttle); zero warnings; `#print axioms` standard;
`python3 -I scripts/check_lean_modules.py --root .`; no name clashes (search `Balaban/` first).

**Stop condition.** Blocks F and I, or about 1,800 lines, or a precise obstruction.

**Do not launch subagents (no Agent tool); work directly.**

**Hard rules** (from `AGENTS.md`): every `.lean` file is a module; no `axiom`, no `sorry`/`admit`,
no heartbeat overrides, no placeholder definitions, zero warnings; frozen files read-only; no file
over 10,000 lines; commit on your branch only, never push to `main`.

**Handoff.** Files; definitions; main theorem names with statements (full statement of LF-1);
checks and results; axioms; last commit hash.
