# Brief W60 — large fields, Lean block J3–J7: main action, quiet kernels, step data, local operators

**Goal.** Formalize items J3–J7 of `notes/phase1/LF-RECONSTRUCTION.md` §II.L (Part II §II.5, amended in
v1.2 / Part IV and per the Part III audit): J3 `mainActionLoc` (Def II.5.4), J4 `IsQuiet`, `quietKernel`
(Defs II.5.5–II.5.6), J5 `StepData`, `KeptData` (structures with fields (S0)–(S3) in the v1.2 form,
indexing by localized prefixes (S4); Def II.5.7), J6 `locOp` by recursion along the lineage with
`locOp_support`, `locOp_factor`, `locOp_level`, `locOp_domain` (Def II.5.8, **Lemma II.5.9 = the structural
half of Lemma F**), J7 `locOp_rot_invariant`, `locOp_euclid_invariant` (Lemma II.5.10). Also: link the
block-indexed fields of block H (`MultiField`, `MultiFieldC` in `Balaban/LargeField/Characteristic/*`)
with `Operators/Variables.lean` (`InternalVars`, `multiscaleField`, which index ψ_j by cubes of 𝕋_j while
the document's `T^{(j)}` is the set of j-blocks) — choose one convention and bridge the other.

Landed inputs: `Balaban/LargeField/Operators/*` (W54: `LFKernel`, `Bound126`, `StepBound`, `comp`,
`tensor`), `Balaban/LargeField/Characteristic/*` (W58: `chiK`…, `chiDom`, `H7Domain`),
`Balaban/LargeField/Background/*` (W51), `Balaban/LargeField/LF1.lean` (W50: `actionG`),
`Balaban/LargeField/History/*` (incl. W59's `localHistory` from `locRH`), `Balaban/Model/Symmetry*`.

**Ownership.** New files under `Balaban/LargeField/Operators/` (edits to `Variables.lean` allowed for the
link) in your worktree `/home/scott/Balaban-worktrees/W60` (branch `w60-lf-locop`), plus import lines.
Worker W61 writes `Balaban/LargeField/Budget/*`: do not touch. Never import `Balaban/Frozen/Roots/*` or
`Balaban/Provider/*`.

**Checks.** Before handoff merge the current `main` and build the whole default target (`lake build`;
AGENTS.md rule 8; at most one build at a time; throttled; never bypass); zero warnings; `#print axioms`
standard; `python3 -I scripts/check_lean_modules.py --root .`; no name clashes.

**Stop condition.** J3–J7 + the link, or about 3,000 lines, or a precise obstruction.

**Do not launch subagents (no Agent tool); work directly.**

**Hard rules** (from `AGENTS.md`): every `.lean` file is a module; no `axiom`, no `sorry`/`admit`,
no heartbeat overrides, no placeholder definitions, zero warnings; frozen files read-only; no file
over 10,000 lines; commit on your branch only, never push to `main`.

**Handoff.** Files; definitions; main theorem names with statements; checks; axioms; last commit hash.
