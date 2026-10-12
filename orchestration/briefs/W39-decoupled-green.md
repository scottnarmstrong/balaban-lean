# Brief W39 — localization: the decoupled Green's operator DG (DG1–DG6)

**Goal.** Formalize Theorem DG of `notes/phase1/LOCALIZATION.md` v2 §3.1 (statements (DG1)–(DG6) and
their proofs, including "Weighted form of (NC3)"), the Green's-function input of I-4: the parametrix
`G_s(A) f = Σ_z s_z χ_z G^{(z)}(A) c_z (1 − 𝒦_s(A))⁻¹ f` with `𝒦_s = Σ_z s_z K_z G^{(z)} c_z`, built from the cube
Green's functions `G^{(z)} = (cutOperator …)⁻¹` restricted to the interaction cube, with: (DG1)
`‖𝒦_s‖ ≤ 1/4` in the weighted `|·|_{2,w}` norm for `M₁ ≥ c_* e^{N₀κ₁}` and `G₁ = G_D` (parametrix
identity §1.3); (DG2)/(DG3) the bounds `‖G_s f‖_* + |Δ^D G_s f|₂ + Hölder ≤ B|f|₂` and the weighted
form; (DG4) analyticity in `(s, A)` on `|s_P| < e^{κ₁}`, `|A|₂ < γ₁` and the Lipschitz bound in `A`;
(DG5)/(DG5′) locality (comparison form with the thickening of v2); (DG6) as stated.

Landed inputs: `Balaban/Multiscale/{CutOperator,CutCoercivity,CutAgmon,CutPointwise,CutCube}.lean`
(NC1, NC2, `cutOperator_inv_supported`), `Balaban/Localization/{NC3,NC3Small,Reflection*}.lean`
(NC3: `pointwise_cut_cube`, `laplacian_cut_cube`, `holder_pair_cut_cube`, `small_*_cut`;
namespace `Balaban.Reflection`), `Balaban/Localization/{CubeAligned,Cover,CutCommutator}.lean` (cover
`chi`, (Cov1)–(Cov4), `card_inBox_le`, `card_Qset_le`, `norm_sProd_le`, `cutCommutator_bound`),
`Balaban/Multiscale/{GlobalBound,HolderGlobal}.lean`, `Balaban/Analysis/*` (analyticity, Cauchy),
`Balaban/Multiscale/Analyticity.lean`. Where an NC3 statement covers only forward bonds or one
chart chamber (W36 open items), state what DG needs and prove the missing piece (e.g. the backward-
bond gradient via `ℓ(x) ≤ L ℓ(x − e_μ)`).

**Ownership.** New files under `Balaban/Localization/` (e.g. `Decoupled.lean`, `DecoupledBounds.lean`,
`DecoupledAnalytic.lean`) in your worktree `/home/scott/Balaban-worktrees/W39` (branch
`w39-decoupled-green`), plus import lines in `Balaban.lean`. Worker W38 owns
`Balaban/Localization/{PolymerGeometry,TreeLength}.lean`; do not touch. Never import
`Balaban/Frozen/Roots/*` or `Balaban/Provider/*`.

**Checks.** Before handoff merge the current `main` and build the whole default target
(`lake build`; AGENTS.md rule 8; at most one build at a time; compiles are throttled machine-wide
and may wait; never bypass the throttle); zero warnings; `#print axioms` standard;
`python3 -I scripts/check_lean_modules.py --root .`; no name clashes (search `Balaban/` first).
Commit after each module.

**Stop condition.** DG1–DG6, or about 3,000 lines, or a precise obstruction (quote it and stop).

**Do not launch subagents (no Agent tool); work directly.**

**Hard rules** (from `AGENTS.md`): every `.lean` file is a module; no `axiom`, no `sorry`/`admit`,
no heartbeat overrides, no placeholder definitions, zero warnings; frozen files read-only; no file
over 10,000 lines; commit on your branch only, never push to `main`.

**Handoff.** Files; definitions; main theorem names with statements; checks and results; axioms;
open questions; last commit hash.
