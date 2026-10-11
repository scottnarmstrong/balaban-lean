# Brief W38 — localization: the polymer geometry D(P), Y[𝒞] and GM1–GM2 on the cover

**Goal.** Formalize Lemma GM of `notes/phase1/LOCALIZATION.md` v2 §4.2 on the landed cover:
the construction (4.44)–(4.45) — for a parameter cube `P` of layer `n`, `D(P)` = the union of the
`π′_n`-cubes `□′ ⊃ □ ⊃ P` inside `Λ_n` (at most `G₀ = (2L+1)^d` cubes of `π_n`), and
`Y[𝒞] = X₁ ∪ ⋃_{P∈𝒞} D(P)` for connected `𝒞` — then (GM1) (layer-`n` cube count of `Y[𝒞] ∖ X₁` is at most
`G₀|𝒞_n|`), connectedness of `Y[𝒞]` and `Y[𝒞] ⊃ Y(𝒞) ⊃ X₁`, and (GM2) the tree-length bound
`d̃_{k+1}(Y[𝒞]) ≤ L⁻¹ d_j(X) + d(2L+1)^d |𝒞|` (sketched in the document: the spanning-tree argument,
with the normalization of P1 (2.27) flagged UNCERTAIN — state exactly the tree-length notion you use
and prove the bound for it; if the P1 normalization cannot be matched, say so).

Build on the landed `Balaban/Localization/{CubeAligned,CubeBump,Cover,CutCommutator}.lean` (W32:
`CubeAligned`, `dropTop`, centres `cubeIdx`, `InBox`, `Qset`), the abstract
`Balaban/Localization/{AbstractExpansion,Peierls,Geometry}.lean` (W25: `patchUnion`, `componentOf`,
`card_layer_biUnion_le` = abstract GM1, `peierls_count_layers`, `exponent_inequality`), and the
landed `GeneratingSet`. Then instantiate the landed abstract GM1/GM3 with the concrete construction.
Small helper lemma also wanted: the weights `compWeight L a₁` are admissible (`IsAdmissibleWeights`)
for `L ≥ 3`, `a₁ ∈ [9/16, 2]` (`Balaban/Background/Composition.lean`), in a file of your own.

**Ownership.** New files under `Balaban/Localization/` (e.g. `PolymerGeometry.lean`, `TreeLength.lean`)
in your worktree `/home/scott/Balaban-worktrees/W38` (branch `w38-localization-gm`), plus import lines
in `Balaban.lean`. Worker W36 owns new reflection/NC3 files; do not touch them. Never import
`Balaban/Frozen/Roots/*` or `Balaban/Provider/*`.

**Checks.** Before handoff merge the current `main` and build the whole default target
(`lake build`; AGENTS.md rule 8; at most one build at a time; compiles are throttled machine-wide
and may wait; never bypass the throttle); zero warnings; `#print axioms` standard;
`python3 -I scripts/check_lean_modules.py --root .`; no name clashes (search `Balaban/` first).

**Stop condition.** The construction, GM1, connectedness, GM2, the instantiation of GM1/GM3, and the
weight lemma; or about 2,500 lines; or a precise obstruction (GM2 failing as stated — quote it).

**Do not launch subagents (no Agent tool); work directly.**

**Hard rules** (from `AGENTS.md`): every `.lean` file is a module; no `axiom`, no `sorry`/`admit`,
no heartbeat overrides, no placeholder definitions, zero warnings; frozen files read-only; no file
over 10,000 lines; commit on your branch only, never push to `main`.

**Handoff.** Files; definitions; main theorem names with statements; checks and results; axioms;
open questions; last commit hash.
