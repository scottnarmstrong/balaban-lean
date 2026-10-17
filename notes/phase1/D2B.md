# D2(b): the step charts lie in the birth-mass domain (W881)

Question. `ClassOldCover.hchart`: `XiCRaw(𝔹_j(X); a; ν_k; j; C₀; C₀²ε′+K₂δ₃+K₂δfl)` ⊆ `XiDom(𝔹_j(X); a; μ_j; j; ε_j)` (`xiFieldDom` at the birth mass `μ_j`, `a = aIdeal L k (compWeight L a₁ k)`, `k`-independent by `aIdeal_compWeight`).

## 1. How the mass enters (refute-first: it enters through BOTH the backgrounds and the weights)
- Backgrounds: `XiAt`/`XiC` (`SmallField/Xi.lean`) use `bgField G a ν Dr`, `bgMult`, `bgFieldC`, `bgMultC` (solutions of the system with `-Δ^D + Q*aQ + ν`; the datum `Dr, Dc` is the same, the solution changes with `ν`), and `InUnionDomainR/C … ν` (`ν L^{2K} ≤ 1`-type clause).
- Weights: `XiBounds.mass` (`√ν ℓ |φ−h₀| < σε`), `XiBounds.hnorm` (`ν L^{2n} ||h₀|²−1| < (σε)²`), `XiCBounds.hAbs`, `hDot` (`ν ℓ² …`), the last also through `φr` (the real background at mass `ν`). `grad, lap, mult, val, close, collarBond` involve `ν` only through the background `φ`.
- Hence the inclusion is NOT a monotonicity statement: the same raw datum has a different background at `μ_j` and at `ν_k`. The two real facts that survive: `μ_j` and `ν_k` are real and positive; XiDom is a plain definition (no `BgHyp`), but any proof that moves the mass needs `BgHyp` at `μ_j`, i.e. `μ_j L^{2K} ≤ 1` (`GreenSetting.withMass`, `massLe`). This is NOT implied by `ν_k L^{2K} ≤ 1` when `μ_j > ν_k`: a margin (`ν_k L^{2K}(1+c) ≤ 1`) is an additional input; it is not in `hchart`'s data.

## 2. The exact inclusion, with constants
Step 1 (landed, application): `xiC_rescale` (`GeneralClassMatch`): `Ξ^c_j(C₀, e) ⊆ Ξ^c_j(1, C₀² e)`, `e = C₀²ε′`-part of the radius; with the `Ψ'' := D.Ψ−Ψ₀` repackaging of `rayInDomain_dom_of_xiCData` (same mass `ν_k`).
Step 2 (MISSING, mass response at level `j`): for `ν = ν_k`, `μ = μ_j = ν(1+t)`, `t = δ_j/δ_k − 1`: `XiC G a ν j 1 e Ψ₀ h₀ Ψ'' h'' → XiC G a μ j 1 (e(1+K_m|t|)) Ψ₀ h₀ Ψ'' h''`, `K_m` depending on `d,L,N` only (expected `≈ 8K₂ + 2`: `δ₁ = 8e|t|` in `exists_isRenSol`; the weights give factor `(1+|t|)`, the real part `Dr` moves by the same Prop. 5.1 estimate), under `μ L^{2K} ≤ 1`, `K₁(C₁e) + K₂ …` smallness as in `xiC_perturb`.
Step 3 (landed): `xiC_mono_eps`: radius `e(1+K_m|t|) ≤ ε_j` suffices; `xiFieldDom_dom_of_eps_le` is the same at the level of `dom`.
Room: DL-gap (FLUCTUATION §1.4) gives `C₀²(C₀²ε′+K₂δ₃) < ε_j` with the half-margin `C₀⁴ε_{k+1} < ε_k/2` and `C₀²K₂δ₃ < ε_k/2`; so `e ≤ ε_j/2·(1−)`-type room and Step 3 needs only `K_m|t| ≤ 1` (plus the `δfl` term, which belongs to the fluctuation variant and is `O(β^{-3/8}) ε_k`, OPEN with it). No Lean statement of (DL-gap) is landed (`ChainNum` has the pieces `small₂, th2, c1`; the inequality `C₀²·radius < ε_j` is not a field).

## 3. Classification of the steps
- scale `C₀ → 1`: landed (`xiC_rescale`, `xiC_scale`). Level-mono in `n` is landed (`xiC_level_mono`), so the level `j` vs the top level `k` costs nothing.
- radius monotone: landed (`xiC_mono_eps`, `xiFieldDom_dom_of_eps_le`).
- mass response for XiC at fixed level `j` and generating set `𝔹_j(X)`: NOT an application. `IsRenSol`/`exists_isRenSol` (`RenormExpLemma35`) are generic in `G` (BgHyp at `ν`) but are stated on `XiCOne` (level `n = K`), give only `(δφ, δα)` with `‖δφ‖_*,|δα|₂ ≤ 8K₂ e|ξ|`, and the identification `eq_bg` is for real `ξ`; converting `(δφ,δα)` to the 15 inequalities of `XiAt`+`XiCBounds` at mass `μ` (as `xiC_perturb` does for a perturbation of `Ψ''`) and to `InUnionDomainR/C` at `μ` is a new proof. Missing lemma (exact): `XiC` mass response above, with the real part `Dr` treated by the same estimate (real `ξ`, `h''=0`) and the complex part by `IsRenSol`.
- cumulated factor: landed ingredients suffice (proved in `LocalClassBirth.lean`): `ν_k = ν L^{2k} δ_k` (`nuSeq_eq`); with `‖ξ_n‖ ≤ (c₈/4)q^{n+1}`, `c₈ = 4C/β` (`rg_flow_infty` hypothesis shape) the ratio `Π_{n=j}^{k−1}(1+ξ₃)/(1+ξ₂) = δ_k/δ_j` satisfies `|ratio−1| ≤ exp(3c₈q^{j+1}/(4(1−q)))−1 = O(β⁻¹ q^{j+1})`, even decaying in `j`. The hypothesis `‖ξ_n‖ ≤ (c₈/4)q^{n+1}` is the landed P4 (5.31) form (`Flow.RGInfty`, `RunningCoefficients`); it is an input about the actual flow, not proved here for the actual `ξ`.

## Status (W882)
Step 2 proved: `xiC_massResponse` (`SmallField/XiMassResponseXi.lean`), `K_m = 1 + 16 (N+1) K₂`, from `massResponse_single`/`massResponse_real` (`exists_isRenSol` + `IsRenSol.eq_bg`, `ξ = (0,t,0)`) and `xiBounds_massResponse`/`xiCBounds_massResponse` (`XiMassResponseBounds.lean`).
Birth inclusion: `xiDom_birth` (`Fluctuation/LocalClassBirthResponse.lean`). Correction to §2: for `j < k` it needs the top-level clause `ν L^{2k}||h₀|²-1| < e₁²` (D1-top, MASS-LEVEL.md) since the BG theory sees `Ψ̃^c_k`; automatic for `j = k` (`xiDom_birth_top`) and unit `h₀` (`xiDom_birth_of_unit`).
Open: `hk` for the actual chart data when `j < k`, `h₀` nonunit; the smallness hypotheses (`hsm`, `hc1`, `hK`, `hζ`, `hee`) are not yet discharged from DL-gap.

## Status (W885)
`Fluctuation/LocalClassBirthChart.lean`: `xiDom_birth_of_unit_realization` (unit real witness needed for ONE realization of the chart point), `xiDom_birth_chart`, `xiCRaw_dom_birth` (hchart ⊆ `xiFieldDom A μ ε`), `xiCRaw_dom_birth_flow` (μ from the flow product, τ = exp(3c₈q^{j+1}/(4(1-q))) − 1), `xiDom_birth_chart_top` (j = top, no witness condition). (DL-gap), exact: `C₀²(C₀²ε′+K₂δ₃+K₂δfl)(1+K_m τ) ≤ ε_j`, `K_m = 1+16(N+1)cK2`; not a `ChainNum` field (small₂, th2, c1, K1s lack the factor C₀² and δfl), so smallness is stated for ε_j (`hsmε hc1ε hKε hζε`, τ < r ≤ 1/16).
Unit witness: NOT forced and NOT provable from landed data (nonunit h₀ allowed by XiC at level j, MASS-LEVEL §3); re-realizing at h_* needs a response of the real background to a change of h₀ (not landed). It is the explicit hypothesis `hunit` (D is realized with ∑h₀²=1, the pinned scheme).

## Status (W886)
`SmallField/XiUnitWitness.lean`: the unit witness is no longer a hypothesis. `unitWitness_real` (real background at h₀' = h₀/|h₀| = old one + (δφ,δα), K₂e², source ν(h₀'−h₀) through Prop 5.1; needs Ω_{j+1}=∅ and N ≥ 1), `xiC_unitWitness` (same complex datum, h''' = h''+h₀−h₀', XiC radius E = 2e+2(N+1)K₂e²; the factor 2 is the mass clause √νℓ|φ−h₀'|, unavoidable for h₀ = 0), `xiDom_birth_of_realization`, `xiCRaw_dom_birth_unitfree` (+ `_flow_unitfree`): hunit removed, (DL-gap) becomes (2E₁+2(N+1)K₂E₁²)(1+K_mτ) ≤ ε_j, E₁ = C₀²(C₀²ε′+K₂δ₃+K₂δfl), plus G.Ω(j+1)=∅ (automatic for j = k).

W893 (D2(b) wiring): `Fluctuation/ClassOldCoverBirth.lean`: `gs_top_layer_empty_of_clauses` (hΩ from `gs_spec`, in scope via `hcl`), `classOldDec_expansion_cover_birth` (Dom = xiFieldDom (compWeight L a₁) μ εs, hchart from `xiCRaw_dom_birth_flow_unitfree`).
Remaining named hypotheses: `hcl` on the birth domain (full clauses, not only `inherit_le` slices), BgHyp at ν and μ, the flow bound hξ and hμ, hDL, hsmε, hc1ε, hKε, hζε, hτr, hr; none follows from landed class constants.

Status (W894): the cover expansion uses only the level-j slices `analyticE`, `boundE` at the label (no level-(k+1) field, no other label; `gs_spec` only for the birth chart inclusion). Core `classOldDec_expansion_cover_of_slices` (`Fluctuation/ClassOldCover.lean`); `classOldDec_expansion_cover` is an application.
Birth: `classOldDec_expansion_cover_birth_slices` (`Fluctuation/ClassOldCoverSlices.lean`) takes the `gs_spec`, `analyticE`, `boundE` slices at the label on the birth domain; `classOldDec_expansion_cover_birth` is an application of it.

Status (W896): `Fluctuation/ClassOldBirthConsts.lean`: `dlGap_of_consts` (DL-gap from `ε′ ≤ ε_j/Λ`, `Λ ≥ 16C₀⁴`, `δ₃,δfl ≤ c ε_j`, `16C₀²K₂'(c₃+c_fl) ≤ 1`, `K_m r ≤ 1`, `(N+1)K₂A ≤ 4`, `A = α₀ epsTail 0`), `epsSeq_anti`, `epsSeq_succ_le_of_le`, `epsSeq_le_tail_zero`.
`classOldDec_expansion_cover_birth_consts`: the slices theorem with `hDL`, `hsmε`, `hc1ε`, `hKε`, `hζε` replaced by constant conditions (`hLα`, `hcc`, `hAK`, `hrK`, `hsmA`, `hc1A`, `hKA`, `hζA`) and `eps ≤ ε_{k+1}`, `δ₃,δfl ≤ c·ε_k`; the bounds `δ₃ ≤ c₃ε_k`, `δfl ≤ c_flε_k` are NOT derived from `ChainNum`/fluctuation bounds (hypotheses).

Status (W897): `Fluctuation/ClassOldBirthDelta.lean`: `delta3_le_of_close` (δ₃ = N·composedCloseBound(…, C_{Ξ1}ε′, r₀) ≤ c₃ε_k, c₃ = N C_{Ξ1} L^{-α} composedCloseBound(…,1,r₀)), `c3_le_of_decay` (c₃ ≤ η iff-type condition log(Λ₀/η) ≤ γ_w(r₀−4dL³)L^{m₁}/L), `deltafl_le_of_flb` (δfl = N(5K₂″δ₁+δ₁) ≤ c_fl ε_k for δ₁ ≤ c_δ ε_k; no landed β^{-3/8} bound, it enters through cψ/δ₁).
`classOldDec_expansion_cover_birth_consts_delta`: the consts theorem with δ₃, δfl given by these formulas; hypotheses δ₁ ≤ c_δ ε_k, c₃/c_fl definitions, hcc, and the constant conditions.
