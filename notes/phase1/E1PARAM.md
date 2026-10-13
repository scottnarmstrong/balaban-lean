# E1PARAM — parameterized energy marks and renormalized datum

Status at `/home/scott/Balaban` commit `28123fb` (read only). **PROVED** means a cited Lean declaration exists, or the indicated finite algebra follows from it. **OPEN** names a missing physical specialization or assembly. **REFUTED** marks a proposed shortcut contradicted by a declaration's binders. This is a blueprint, not a declaration of the physical `expE0` field.

## T1. A single parameter family at each root

Fix the tower scale and set `S := T.step k hk N₁ ν β p₁`, `BS := S.blockSplit 1 hp`, `V := physV S S.a₁ S.ν T.t`, `U := Metric.ball (0 : ℂ) corrU`, `Q := physCarrier S 1 hp`. Take the **one** `Jr,val,I,A₀` furnished by `zeroSourceActivity_common_fromTower` at `q=1`, with `reads := fun _ => Set.univ`, `dom := e1Dom S`, and `hdomR := e1Dom_isDj T D`. Write `Lab` for its `commonLabels (thickLabels I.𝒴 I.dom) ... reads dom`, `κH = κG := 2*T.κdec-1`, `κ0 := T.κ0`, `Kc := T.marksKc'`, `εH` for the displayed common activity amplitude, and `κ' := T.κ'`. **PROVED:** the activity output is one `A₀ : physParam 2 S → ℂ → LabelAct Lab BS.Ωb εH κH κ0 Kc`, chosen before the root and before any datum (`ZeroSourceActivityCommon.lean:zeroSourceActivity_common_fromTower`).

Choose **once**, before any raw datum, `(F₁,Sol)` from `DecMarkCorrFamilyFromTower.lean:markCorrFamily_fromTower`. Its indices are `(z,b)`; its value can depend on `z` through `S.blockU z`, but the *functions* are chosen before `∀ z` and before `∀ Θ ∈ XiCRaw`. The theorem's `hJ2` and `hJ4` are chart statements, and `hJ4` gives analyticity on `physV × ball 0 a`; `markedOutDecCorr_fields` transfers this to rooted outputs. **PROVED. REFUTED:** these pairs are chosen afresh for every datum, or are analytic only at `rawOf S.D'`.

For a fixed root `z`, let `ιz := {Y' // Y' ∈ bridgeFamily 1 reads dom z}`, `y₀ i := commonAnchor _ reads dom z i`, and `F₀ i := corrF0 T k β p₁`. Define the raw rooted output

`O_z(Θ,u,Φ,Y') := markedOutDec 1 reads dom z (decMarkCorrTerm S ... (fun b => F₁(z,b)) (fun b => Sol(z,b)) (S.blockU z) p₁ hp (S.β : ℂ) Θ u Φ) Y'`.

Here `...` is exactly the `LocalCover.nbhdF 1 (LocalCover.blockSite k b)`, `k`, `LocalCover.fam 1 (LocalCover.blockSite k b)`, `S.a₁`, `S.ν`, and `S.betaU^(-1/2)` arguments in `E1MarksCommon.lean:e1MarkG`; the only change is replacing its hardwired `rawOf S.D'` by `θ.1.1`. Put

`Gz θ i u Φ := if θ ∈ V ∧ ‖u‖ < corrU then O_z(θ.1.1,u,Φ,i.1) else 0`.

This is the proposed new `e1MarkGParam`. The parameter is the full `physParam 2 S`; on the physical zero-source slice it is `θ=((rawOf D', proof),0)`. The outer chart cutoff is required: `ParamMarkFamily.bound`, `.meas`, and the configuration locality used later quantify over *all* `θ,u`, whereas `markCorrFamily_fromTower` supplies its count bound only for `Θ ∈ XiCRaw` and `‖u‖≤corrU`. The cutoff equals the analytic rooted output throughout the open set `V×U`; `U⊂ball 0 2` makes the zero-source activity's larger source disc compatible. At `s∈[0,1]`, `s∈U`, so the cutoff does not alter the physical sum. **PROVED:** `corrU=17/16>1`, and `E1MarksCommon.lean:e1Marks_common_fromTower` gives segment inclusion. **REFUTED:** using `e1MarkG` itself as the parameter mark; its definition fixes `rawOf S.D'`.

The desired Lean term, for each `z`, has type `ParamMarkFamily BS.μ Lab A₀ y₀ Gz κG F₀ V U Q` and constructor

`⟨hV, hU, hseg, hQcompact, hQmeas, hQcarried, hGmeas, hGbound, hAhol, hGhol, hAcont, hGcont⟩`.

Here the twelve `h` names denote the proofs in the table below, in the exact field order of `Thm31CoeffAnalytic.lean:ParamMarkFamily`. `A₀` already has common labels: applying `commonAct` or `paramMarkFamily_common` to it a second time would change the label type. **REFUTED** as a construction. The following table gives *all* fields.

| Field | Supplier and exact remaining work | Status |
|---|---|---|
| `isOpenV` | `physV` openness, also in the empty-mark `ParamMarkFamily` returned by `zeroSourceActivity_common_fromTower` | **PROVED** |
| `isOpenU`, `seg` | `Metric.isOpen_ball` and `e1Marks_common_fromTower`'s segment clause | **PROVED** |
| `compact`, `measQ`, `carried` | copy the empty-mark family's carrier fields (`Q` and `BS.μ` are identical) | **PROVED** |
| `meas` | split the two scalar predicates; inside use `markedOutDecCorr_fields` at `Θ=θ.1.1`, outside measurable zero | **OPEN** short parameter wrapper; rooted theorem **PROVED** |
| `bound` | outside cutoff zero; inside `markCorrFamily_fromTower` count bound, then `commonAnchor_dl`; positivity of `corrF0` from `E1LabelsBudget.lean:corrF0_pos` | **OPEN** wrapper; ingredients **PROVED** |
| `holA` | restrict the empty-mark family's `holA` from `V×ball 0 2` to `V×U` | **PROVED** |
| `holG` | on `V×U`, discard cutoff locally; `markedOutDecCorr_fields` with `a=corrU`, a positive spare radius `b'` supplied by `2*corrR*markedRad<T.t` and `2*corrU≤corrR` | **OPEN** wrapper; analytic theorem **PROVED** |
| `contA` | restrict the empty-mark family's `contA` to `U` | **PROVED** |
| `contG` | `markedOutDec_decMarkCorrTerm_eq` writes a finite sum of `decMarkCorr`; apply `decMarkCorr_fields_of_pair`'s continuity in `Φ` term by term | **OPEN** finite-sum wrapper; block continuity **PROVED** |

For `paramMarked_analytic_local_bound`, additionally show `hGdep : ∀ θ i s, DepOn (blocksOf ... (Lab.ysite (y₀ i))) (Gz θ i s)`. Split the cutoffs; inside use `markedOutDecCorr_fields` and `commonAnchor_ysite`; outside use constant zero. This is configuration locality, not datum locality. **OPEN** wrapper with **PROVED** block ingredients. `E1LabelsBudget.lean:e1Dom_bridgeFamily_nonempty` supplies `Nonempty ιz`; `corrBudget_fromTower` supplies the uniform prefactor inequality, at every root. **PROVED.**

## T2. Canonical coefficients and the all-fibre value

Define, for each root and finite cube set `C`,

`c_z(θ,C) := gsumCoeff BS.μ Lab (A₀ θ) y₀ (Gz θ) C`.

This is the *interpolation* coefficient. `Thm31CoeffA.lean:gsumCoeff` is the integral over `s∈[0,1]` of `Gsum`; `interpCoeff I C` is definitionally this value when `I` has the same `A₀,y₀,Gz` at a fixed datum. `ParamDatumFamily.lean:e1CoeffC_eq` says `e1CoeffC I Det C = Det.term C + interpCoeff I C`; `e1CoeffC` belongs to `E0locC`, while `c_z` alone belongs to `E1locC`. **PROVED.**

`ParamCarrierLocal.lean:paramMarked_analytic_local_bound` gives for every `C`: `AnalyticOnNhd ℂ (fun θ => c_z(θ,C)) V`, equality at `θ,θ'∈V` whenever `π θ=π θ'`, and

`‖c_z(θ,C)‖ ≤ CPE 3 3 Kc κH κ0 κ' * (∑ i:ιz, F₀ i * exp(-κ0*Lab.dl(y₀ i))) * exp(-κ'*dExt C)`.

Use `corrBudget_fromTower` to bound the first two factors by the tower's fixed `K0`. Its numeric hypotheses (`hκ0,hKc,hεpos,hF0,hκ',hκG,hκ,hε`) come from the common activity/tower budget; `hGdep` is the configuration-locality clause above. The theorem also requires two *separate* raw-parameter locality clauses: for any `θ,θ'∈V` with `π θ=π θ'`, all real `s∈[0,1]`, each activity label or mark anchor whose `ysite⊆Yhat Set.univ (sitesOf C)`, the corresponding functions of `Φ` are equal. Take `π θ` to retain the source parameter and the restriction of `θ.1.1` to that `Yhat`; for the physical zero-source slice the sources already agree. `ParamActivitySubspace.lean:physical_labelActFamilyOn_local` concerns an unscaled family; the zero-source `A₀` here comes from `physInclScaled 2 S (1/S.β)` and then `commonAct`. A specialized transfer for this **exact** `A₀`, together with raw locality of each corrected pair output, is **OPEN**. `paramMarked_analytic_local_bound` does not provide these premises by itself. Analyticity and the displayed bound can already be obtained from its landed `gsumCoeff_analyticOnNhd` and `norm_gsumCoeff_le` once the T1 record is built. **PROVED conditional on T1; parameter locality OPEN.**

The required all-fibre identification is the explicit goal

`∀ D' hDh hD z,  (S.withDatum D' hDh).E1locC zeroClass z = ∑ C, c_z(((⟨rawOf D',...⟩ : rawSub 2 S.G'),0),C)`

for `hD : XiCData ... T.t D'`. It is enough to assemble an `E1MarksC (S.withDatum D' hDh) zeroClass BS z` whose `A,y₀,G` are the **same** `A₀,y₀,Gz` evaluated at that fibre point, then apply `Thm31CoeffA.lean:interpCoeff_spec` or `ParamDatumFamily.lean:thm31aC_coeff` and `interpCoeff`'s definition. The `hW` activity identity already has `∀ D' hDh hD` and every source `g` in `zeroSourceActivity_common_fromTower`; extend it to common labels by `MarkedCommonLabels.lean:commonAct_hW_interp`. **PROVED.** `DecMarkCorrTotalFromTower.lean:fderiv_mask_corrected_total_fromTower` and `sum_blockEnergy_eq_VkC_add_delta_fromTower` likewise quantify over **every** `D'` in the chart with constant `h₀`. **PROVED.** The same-pair decoupled sum bridge for `hF`, and its specialization uniformly in `D'` to the pair family already chosen, is **OPEN** (W512); no landed `e1MarksC_zeroClass_fromTower` supplies it. `Thm31cde.lean:InterpMarks.hF` is pointwise in every real `s∈[0,1]` and almost every `x`; proving it only at `S.D'` would be insufficient. **REFUTED:** `ParamDatumFamily.lean:thm31aC_coeff_withDatum` constructs this fibre record; it *takes* a separate `I : E1MarksC (S.withDatum D' hDh) ...` as input.

## T3. Support, collar hull, fibre map, determinant

For any fixed `θ`, the `Gsum` expansion has active connected support: if `c_z(θ,C)≠0`, some mark label's blocks lie in `C`; hence `C` is nonempty, `dOmega 1 (k+1) Set.univ (sitesOf C)≠⊤`, `IsPolyDom 1 (k+1) (sitesOf C)`, and `dExt C=sizeJ 1 (k+1) (sitesOf C)`. This is the argument formalized for `interpCoeff` by `RootActiveSize.lean:exists_blocksOf_subset_of_interpCoeff_ne_zero`, `interpCoeff_ne_zero_active`, and `norm_interpCoeff_le_sizeJ`; the underlying `gsumCoeff_eq_zero_of_dOmega_top` is already generic in activities/marks. A direct parameterized `gsumCoeff_ne_zero_active` lemma, or a fixed-`θ` `InterpMarks` record for **every** `θ∈V`, remains **OPEN** as Lean assembly. The mathematical connectedness assertion is **PROVED** by that same finite expansion argument; mere vanishing at `C=∅` alone would not establish it. On nonzero support the `K0 exp(-κ' dExt C)` estimate becomes `K0 exp(-κ' sizeJ(sitesOf C))`.

For each `θ`, define `b_z(θ,X) := detCollarGrouped (c_z(θ,·)) X`. `DetCollarHull.lean:sum_detCollarGrouped` preserves the total for every coefficient function. Its `detCollarGrouped_bound` needs exactly the connected-support premise above and yields `‖b_z(θ,X)‖≤hullConst 3 3 κ' K0 * exp(-hullRate 3 3 κ' * sizeJ X)`. **PROVED conditional on the active-support transfer and T1 bounds.** Finite fibre sums preserve analyticity and parameter locality, provided both are proved for `c_z`.

The second regrouping is `∑_{X:renFibreMap ... X=Y} b_z(θ,X)` over the landed `renYs`. `RenormDetFibreMap.lean:sum_renRegroup` preserves the total and `renRegroup_norm_le` gives constant `H*exp(c1 3 3*log 2)*exp λ` at any rate `κ≤λ/renDetA 3 3 1-c1 3 3*log 2`, where `H=hullConst 3 3 κ' K0`, `λ=hullRate 3 3 κ'`. It requires `b_z(θ,X)=0` off **both** `IsPolyDom X` and `X∩X1(z)≠∅`. The first follows from connected support and the collar hull; the second needs the root anchor. `MarkedRootGeometry.lean:bridgeFamily_spec` puts `rootCube z` in every bridge label's blocks, and `RootMarkedBound.lean:anchor_of_labels` converts a nonzero interpolation coefficient to `rootCube z∈C`. Transfer that statement to the parameterized `gsumCoeff`; then `DetCollarHull.lean:sitesOf_subset_detCollarHull` retains its sites and the root cover must meet `X1(z)`. The latter geometric incidence and the exact rate inequality for the chosen physical `κ` are **OPEN**; neither is an assumption of `detCollarGrouped_bound`.

Evaluate at the renormalized datum through `RenormThetaDatum.lean:analyticOnNhd_renThetaRaw` and `renThetaRaw_rawAgree`. `StepTowerRadius.lean:StepTowerTheta.renDatum_half_mem_xiCData` places `renThetaDatum S (T.t/2) D ξ` in the chart for `D∈XiCOneReal(T.t/2)`, `‖ξ‖<r₀`; the source remains zero. The physical fibre expansion then follows by composition and finite regrouping *if* the parameter locality and all-fibre identity above are present. At `ξ=0`, use `renThetaDatum_zero`, so the sum is the physical marked `E1locC` at the base datum. **PROVED conditional on those OPEN inputs.**

`RenormE0FibreDetRadius.lean:expE0_det_scale_of_tower_at` supplies only the determinant summand on the `XiCOneReal` fibre, with rate `3*T.κdec/2`. Restrict its domain/radius as needed, align the marked rate and `renYs`, and add the two `IsLocExp` records via `RenormExpCauchy.lean:IsLocExp.add`; its type requires exactly the same domain, radius, `Ys`, distance and rate. The value equality is `E0locC =` determinant `+ E1locC`, not a second use of `e1CoeffC` after determinant addition. **OPEN:** complete physical `expE0`; **PROVED:** determinant record and additive API.

## T4. Ordered Lean targets (each at most 300 lines)

1. **Start now, 160–220 lines, Sonnet:** `E1MarkParamCommon.lean`; define the double-cutoff `Gz` and prove all `ParamMarkFamily` fields and `hGdep` using the chosen pair family and empty-mark activity package. Keep the choice of `F₁,Sol` *outside* `∀D'`. No need for `e1MarksC_zeroClass_fromTower`.
2. **Start now, 100–180 lines, Sonnet:** `GsumActiveParam.lean`; lift `RootActiveSize`'s connected-support and active-size arguments directly to parameterized `gsumCoeff`, then prove the common-anchor root-cube implication. No physical `hF` is needed.
3. **Start now, 180–260 lines, strong:** `E1ParamRawLocal.lean`; prove the two exact parameter-locality premises of `paramMarked_analytic_local_bound` for `A₀` and corrected `Gz` on `Yhat(sitesOf C)`. Check `physInclScaled`, zero-source restriction, and the pair's raw read set. No physical `hF` is needed.
4. **After W512, 180–260 lines, strong:** `E1ParamFibreValue.lean`; use the *same* pair family to prove `InterpMarks.hF` and the all-fibre sum identity. Specialize W505 with each `D'` and the zero-source `hW`. This is the **single hardest step**, since a value identity for a newly chosen pair or just the base datum would not identify the parameter coefficient family.
5. **After 1–4, 180–270 lines, strong:** `E1ParamRenFibre.lean`; prove collar support and root incidence, the rate inequality, both regroupings, composition with `renThetaRaw`, and the marked `IsLocExp` on the half-radius fibre.
6. **After 5, 80–140 lines, Sonnet:** align determinant and marked records, apply `IsLocExp.add`, and check the value at `ξ=0` against `E0locC`.

The first three targets can start before `e1MarksC_zeroClass_fromTower` is assembled. Their outputs should retain the same fixed `A₀,F₁,Sol,Lab,ιz` and the tower's numerical constants; changing any of these between stages breaks the intended all-fibre identity.
