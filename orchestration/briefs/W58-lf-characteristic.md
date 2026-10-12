# Brief W58 — large fields, Lean block H: characteristic functions and domains (Part II §II.3)

**Goal.** Formalize block **H** of `notes/phase1/LF-RECONSTRUCTION.md` §II.L (Part II §II.3, as amended
in v1.2 / Part IV): H1 `Reg`, `chiK`, `chiPrimeOld` (P5 (2.5)), `chiPrimeNew` (2.13), `chiFluct` (2.42),
`chiNext` (P6 (2.1)), products over cube sets (Defs II.3.1–II.3.2); H2 `measurableSet_chi`, `chi_stencil`
(Lemma II.3.3: measurability and the stencils of the characteristic functions); H3 `chiDom` (the operator
domain P5 (1.24)–(1.25)), `PsiTildeMulti` (Def II.3.4); H4 `DeltaC`, `DeltaPrimeC`, `H7Domain` (the
analyticity spaces P5 (1.36)–(1.37), Def II.3.5). Build on the landed block G
(`Balaban/LargeField/Background/*`: `bgCube`, `bgSF`, `psiSF`, `bgLocUnion`), the background layer
(`Balaban/Background/*`: `bgField`, `bgFieldC`, `theorem72`, `InPsiTilde`, `InPsiTildeC`), the Ξ spaces
(`Balaban/SmallField/Xi*.lean`), the region calculus (`Balaban/LargeField/Region/*`), the operator variables
(`Balaban/LargeField/Operators/Variables.lean`: `InternalVars`, `multiscaleField`).
Characteristic functions are indicator functions of real configurations (they are never continued
analytically — see the Part III audit P3-02/P3-03: keep them as functions of the real integration
variables). If a statement of the document is false as printed, stop that item and report it.

**Ownership.** New files under `Balaban/LargeField/Characteristic/` in your worktree
`/home/scott/Balaban-worktrees/W58` (branch `w58-lf-characteristic`), plus import lines in
`Balaban.lean`. Worker W55 is writing new `Balaban/LargeField/History/*` files; do not touch. Never import
`Balaban/Frozen/Roots/*` or `Balaban/Provider/*`.

**Checks.** Before handoff merge the current `main` and build the whole default target
(`lake build`; AGENTS.md rule 8; at most one build at a time; compiles are throttled machine-wide
and may wait; never bypass the throttle); zero warnings; `#print axioms` standard;
`python3 -I scripts/check_lean_modules.py --root .`; no name clashes (search `Balaban/` first).

**Stop condition.** H1–H4, or about 2,000 lines, or a precise obstruction.

**Do not launch subagents (no Agent tool); work directly.**

**Hard rules** (from `AGENTS.md`): every `.lean` file is a module; no `axiom`, no `sorry`/`admit`,
no heartbeat overrides, no placeholder definitions, zero warnings; frozen files read-only; no file
over 10,000 lines; commit on your branch only, never push to `main`.

**Handoff.** Files; definitions; main theorem names with statements; checks and results; axioms;
last commit hash.
