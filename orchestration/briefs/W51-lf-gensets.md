# Brief W51 — large fields, Lean block G: generating sets and backgrounds of a step (Part II §II.2)

**Goal.** Formalize block **G** of `notes/phase1/LF-RECONSTRUCTION.md` §II.L (Part II as amended by v1.2):
G1 P3's minimal generating sets (`minimalGenSet` as a `GeneratingSet`, monotonicity to `Precedes`,
range one cube, disjoint unions; Def II.2.2, Lemma II.2.3), G2 lifts (`liftSingle`, `liftMixed` to
`BgData`, layer-constancy; Def II.2.1), G3 the generating sets of a step (`genCube`, `genCubeMixed`,
`genSF`, `genBoundary`, `genBoundaryLocal`, generating-set/range/agreement lemmas; Def II.2.4, Lemma
II.2.5, using the region calculus of Part I block B), G4 **exact factorization of the local minimizer**
(`isEL_local_iff`, `bgFieldC_local_eq`; Lemma II.2.6, from the landed Def-5 `bgField`/`bgFieldC`,
`theorem72`, `IsEL`, `IsSmallSolution`), G5 the backgrounds used by Def-7 (`bgCube`, `bgCubeMixed`,
`bgSF`, `psiSF` via `composeField`, `bgLoc`; Def II.2.7).

Landed inputs: `Balaban/Multiscale/GeneratingSet.lean`, `Balaban/Background/*` (Def-5, Theorem 7.3,
`composeField`, `Precedes`), `Balaban/LargeField/Region/*` (block B: `RegionStep`, `flowGeneratingSet`),
`Balaban/LargeField/Geometry/*`. If a statement of the document is false as printed, stop that item and
report it.

**Ownership.** New files under `Balaban/LargeField/Background/` in your worktree
`/home/scott/Balaban-worktrees/W51` (branch `w51-lf-gensets`), plus import lines in `Balaban.lean`.
Workers W48 (`LargeField/History/*` new files, `Counter/Instantiation*`) and W50
(`LargeField/Analytic/Constants.lean`, `LargeField/LF1.lean`) are active: do not touch their files.
Never import `Balaban/Frozen/Roots/*` or `Balaban/Provider/*`.

**Checks.** Before handoff merge the current `main` and build the whole default target
(`lake build`; AGENTS.md rule 8; at most one build at a time; compiles are throttled machine-wide
and may wait; never bypass the throttle); zero warnings; `#print axioms` standard;
`python3 -I scripts/check_lean_modules.py --root .`; no name clashes (search `Balaban/` first).
Commit after each module.

**Stop condition.** G1–G5, or about 2,500 lines, or a precise obstruction.

**Do not launch subagents (no Agent tool); work directly.**

**Hard rules** (from `AGENTS.md`): every `.lean` file is a module; no `axiom`, no `sorry`/`admit`,
no heartbeat overrides, no placeholder definitions, zero warnings; frozen files read-only; no file
over 10,000 lines; commit on your branch only, never push to `main`.

**Handoff.** Files; definitions; main theorem names with statements; any statement found false;
checks and results; axioms; last commit hash.
