# MARKASM: marked decoupling and connected assembly

13 October 2026. Repository paths below are relative to `Balaban/`; that tree was read only. **PROVED** means a deduction below or a landed declaration; **PROVED CONDITIONAL ON** names its input; **OPEN** means no such theorem has been established; **REFUTED**
means the proposed implication fails.

## 1. The row set and the output label

**PROVED.** For a participating family use the actual block data `X₁f`, its parameter set `C : Finset (ParIdx Gp X₁f)`, the map `c i = i.1.1`, and `𝒞 = C.image c`. Put `Yc = compY c X₁f C` and let `Y` be its finite set of sites. The proof of
`Fluctuation/SharpEngine.lean`, `fanHL_local_dir`, establishes `IsNnComp ((Vset X₁f 𝒞).filter (· ∈ Gp.Ω 1)) Y` at this exact stage. It also supplies `X₁f` as a complete cell union and `𝒞 ⊆ cubeIdx Gp`.

**PROVED.** `Fluctuation/RowsCompose.lean`, `hatPsiF_rows`, and `Fluctuation/MarkedHatRows.lean`, `markedHatPsiF_rows`, apply to that `Y`. Their comparison assumes `D.Ψ=D'.Ψ` on `Y`, `D.h=D'.h` on `Y∩Ω₁`, and equality of the hat inputs at every `UnitOut Gp Y`
unit point. For cuts `s,s'`, both extended cuts are 1 outside `parCubes Gp X₁f`, both are 0 on `parCubes Gp X₁f \ 𝒞`, and they agree at each `P∈𝒞` with `SubI Gp (cubeP P) Y`; both lie in the open `exp κ` polydisc. The conclusion is pointwise equality of the
**masked** tangent on `Y`, for fixed `Z,u,t`. The proof is the pointwise identity `markedHatPsiF_apply`: multiply equal `hatPsiF` values by the same scalar `u+t 1[unitPt(y)∈Z]`.

**REFUTED.** `bridge m₀ z Y` is generally not such a component. Its added aligned cubes can be outside `Vset X₁f 𝒞`, even outside `Ω₁`. Thus neither the bridge nor `psiThick (bridge m₀ z Y)` is automatically covered by components of this participating family.
`markedHatPsiF_rows_bridge_of_cover` has a real cover hypothesis; it does not prove that cover. Adding all components that meet `psiThick Y` also fails: some sites of `psiThick Y` are outside `Vset`, and another component meeting it can have unbounded covering
size. No fixed replacement for `cBr` follows from that rule.

**PROVED CONDITIONAL ON `MARK-FAN` below.** Keep the **original** component for the row argument. The marked analogue of `fanHL_local_dir` uses the same `Yc`, `X₁f`, `𝒞` and cut comparison just specified. Data agreement is on `thickSet Gp Yc`, hat agreement on
the unit points of `Yc`, precisely `AgHatDir hG' Yc` from `Fluctuation/SharpAE.lean`. The background rows use the data and cut hypotheses above; in the fluctuation rows replace `hatPsiF_rows` by `markedHatPsiF_rows` and invoke
`Dec2.RowsFl.i4a_local_fpS_rows_level` with that paired tangent agreement. The functional reads its fine tangent on its original `readSites` set; `BlockMargin` and `readSites ⊆ X₁f ⊆ Yc` close that last locality step. This proves the **decoupled coefficient**
local on `Yc`, without reading a bridge.

**PROVED CONDITIONAL ON `MARK-FAN` and `MARK-COUNT`.** After the cut expansion, write its finite marked coefficient as `R_{z;b,Y}(Θ,u,t;ψ̂)` on an original `Y ∈ polymerDomains(c,Gp,m₀,X₁)`. Its output label is `Y' = bridge m₀ z Y`, attached **after** sharp
locality on `Y` is obtained. The marked coefficient is invariant if raw data agree on `thickSet Gp Y'` and hat inputs agree at `unitPt(y)` for all `y∈Y'`; at its cut stage use the three cut agreements above on `Yc`, before integrating those cuts. Indeed `Y⊆Y'`
(`MarkedRootGeometry.subset_bridge`), so `SharpAE.agHatDir_mono` reduces agreement on `Y'` to agreement on `Y`. The finite integral, cubic Taylor operation, difference and `∂t|₀` preserve an equality holding for every admissible `t`; no row lemma on `Y'` is
needed.

**PROVED.** `MarkedRootGeometry.bridge_isDj_and_le` gives `d(Y')≤d(Y)+cBr`, `cBr=L^d(2dL)=2dL^{d+1}`. If `psiThick Y` meets `fineBlock z`, `rootCube_mem_blocksOf_bridge` anchors `Y'`. `card_fibre_bridge_le` bounds each fibre by `nFibre=2^(L^d L^d)`, and
`fibre_weighted_le` gives the exact weighted cost `nFibre exp(a cBr)` at any nonnegative rate `a`. No alternate component enlargement, size cost or fibre theorem is required.

**PROVED CONDITIONAL ON `MARK-COUNT`.** A nonzero marked difference has `psiThick Y ∩ fineBlock z ≠ ∅`: the general-tangent block locality in `Localization/I5Fluct.lean` reads its tangent only on `psiThick Y`; outside `fineBlock z`, `markedHatPsiF_apply` makes the two tangents identical. If the intersection is empty, every cut integrand and hence its finite assembled difference is zero. This supplies the hypothesis of `rootCube_mem_blocksOf_bridge` for every contributing label.

## 2. What the scaled assembly needs

**PROVED.** `SharpAssemblyScaled.vblock_expansion_hat_dir_scaled` calls `i5_functional_hat_dir`; the latter uses `hatPsiF_mem_flBallLC` on every cut in `|s_P|<exp κ`, the analytic fan `fanH_analytic`, and `fanHL_local_dir` with `hatPsiF_rows` and fluctuation
row uniqueness. Its output `Ev_Y` is analytic on a neighbourhood and local for `AgHatDir Y`; its bound is `E*_k exp(-2κdec d(Y))`. `hat_vpart_bound_dm_dir_scaled` then uses the arbitrary tangent realization `hreal`, the `FlBall` and `IsLayerConstant`
conditions, radial Cauchy of radius `r`, Taylor weight `(1-s)^2/2`, and `card_blocks_filter_le`. The old-block count costs `c1(d,L)L^{(m₀+m₁)d}(1+d(Y))`; absorbing the last factor changes the rate from `2κdec` to `a=2κdec-1`. `physical_directTerms_eta_scaled`
adds the source slice and packages `PhysicalSharpLocEta`; its proof does not introduce a masked tangent.

**PROVED.** `MarkedHatRows.markedHatPsiF_apply`, `markedHatPsiF_zero_t`, and `markedHatPsiF_one` give respectively the output mask, the unmarked zero mark, and the physical tangent at all cuts equal to 1. `MarkedTangent.isLayerConstant_liftC_markedTangentC`,
`liftC_markedTangentC_mem_flBallLC`, and `markedDisc_mem_flBallLC` give physical layer constancy and open radial discs; `MarkedCubicTaylor` proves marked Taylor and the per-term Cauchy estimate under their hypotheses. `hreal` is already quantified over
**every** admissible layer-constant tangent; it can be applied to a marked tangent once its ball and layer hypotheses hold.

**OPEN (`MARK-BALL`, `MARK-AN`, `MARK-FAN`).** On every cut and every radial circle, the decoupled marked tangent still needs a strict uniform ball bound, joint analyticity in cuts, `Θ,u,t,ψ̂`, and a marked fan locality theorem. The required sufficient
inequality is `(R₁+r)(Rσ+t₁) sqrt(N)|cc| covSupConstC cψ < δ₁`, with `0<t₀<t₁`. It follows by the triangle inequality and `‖M_Zv‖∞≤‖v‖∞`; strictness gives an open neighbourhood of the Cauchy circle. The unit mask preserves lower layer constancy because each
layer block has constant `unitPt`. Analyticity follows pointwise from `hatSqrtF` and the fixed linear mask, but the corresponding joint cut-domain theorem is not landed. `MARK-FAN` must also replace the hard-coded `hatPsiF` in
`RowsCompose.fluct_correction_rows_of_agree_on_component` and `SharpEngine.fanHL_local_dir`; `markedHatPsiF_rows` alone does not do this.

**OPEN (`MARK-COUNT`).** Rerun `SharpAE.i5_functional_hat_dir_of_fan`, the scaled block expansion and the `hat_vpart_bound_dm_dir_scaled` resummation for the joint marked family, then take the cubic difference at the **same** `(Θ,u,t)` before differentiating.
`physical_directTerms_eta_scaled` cannot be applied verbatim to obtain these marked coefficients. The fixed label family and all estimates must hold uniformly on `|t|<t₁`.

**PROVED CONDITIONAL ON `MARK-BALL`, `MARK-AN`, `MARK-FAN`, `MARK-COUNT` and the zero-class chart hypotheses of `MARKCUBIC.md`.** Let `εsc = β[3 c1(d,L)L^{(m₀+m₁)d} E*_k/r³ + ηs Qδ₁/r]`, where `ηs=1/β`, `Qδ₁=cK2' δ₁`, and `a=2κdec-1`. This is the zero-class
amplitude supplied by the scaled count **if** its marked uniform version is established; the positive source slice is retained. For `Y'` in the finite `bridgeFamily`, set `G_{z,Y'}(Θ,u;Φ)=∂t[Σ_{b,Y:bridge_zY=Y'} R_{z;b,Y}(Θ,u,t;Φ)]_{t=0}`. The claimed bound is
`|G_{z,Y'}|≤F₀ exp(-a d(Y'))`, with `F₀=(2 εsc/t₀) nFibre exp(a cBr)`. The factor 2 bounds a difference of two cubic terms; Cauchy contributes `1/t₀`; the old-block count consumes one unit of exponential rate; the cut polydisc `|s_P|<exp κ` is paid by the
displayed `κdec` hypotheses of the scaled assembler and creates no further factor after they are met. `MarkedRootGeometry.fibre_weighted_le` proves the bridge factor exactly. Finite summation and `MarkedCubicTaylor.VkC_marked_eq_block_terms` give
`Σ_{Y'}G_{z,Y'}=f_z`, where `f_z=DΦ₁ᶜ(Θ,u y_Φ)[M_z y_Φ]` is the `E1MarksC` integrand, including `u=0` (`MarkedCubicTaylor.deriv_Phi1C_marked_eq_E1MarksC_integrand`). Every nonzero label contains `rootCube z`, locality is the `AgHatDir Y'` statement above, and joint analyticity follows by Cauchy's integral on `|t|=t₀` on a common open chart. These are
conditional output clauses, not a landed marked `DirectTerms` or `E1MarksC` family.

**PROVED CONDITIONAL ON the same inputs.** On physical variables, sharp locality means equality under `physAgΘ S Y'` for the data and source, plus agreement of the block configurations on `blocksOf m₀ (k+1) Set.univ Y'`. `StepSetting.agHatFDir_hatOf` turns the latter into hat agreement on `Y'` because `bridge_isDj` makes `Y'` a complete cell union. Cut parameters have already been integrated and are not additional physical inputs.

## 3. A source-like hat input

**REFUTED.** In general `K_Θ M_z ≠ M_z K_Θ`. For example, with `K=[[1,q],[q,1]]`, `0<q<1`, `M=diag(1,0)`, and `x=e₂`, `K M x=0` while `M K x=q e₁`; this is a positive square root. Thus replacing `ψ̂` by `(u+tM_z)ψ̂` marks **before** the square root and does
not produce the `E1Marks` direction.

**PROVED CONDITIONAL ON** invertibility of `K_Θ(s)` on a common chart: `ψ̂_t=uψ̂+t K_Θ(s)^{-1}M_z K_Θ(s)ψ̂` does satisfy `K_Θ(s)ψ̂_t=uK_Θ(s)ψ̂+tM_zK_Θ(s)ψ̂` exactly, even at `u=0`. At the physical cut point, differentiating `Phi1C(Θ,K_Θψ̂_t)` therefore
recovers `E1MarksC` by `MarkedCubicTaylor.deriv_Phi1C_marked_eq_E1MarksC_integrand`. **OPEN.** A common analytic inverse and its admissible hat-input radius are not supplied; more decisively, `K^{-1}M_zK` generally spreads a local input across blocks and
depends on cuts and data. Composing the unmarked `Ev_Y` with this map does not retain `AgHatDir Y` or a rooted fibre bound. So this exact reparametrization does not make the landed assembly apply verbatim with its needed sharp output.

## 4. Lean packages, one main theorem each

**OPEN.** Keep each package at most 300 physical lines; split any auxiliary claim into its own package rather than enlarging a file. In dependency order:

1. `MarkedDecBall`: `markedHatPsiF_mem_flBallLC` on the full cut and radial discs (`MARK-BALL`); independent of class generators.
2. `MarkedDecAnalytic`: `analyticOnNhd_markedHatPsiF` jointly on the open polydisc and chart (`MARK-AN`); independent.
3. `MarkedFluctRows`: `fluct_correction_rows_marked` using `markedHatPsiF_rows` and `RowsFl.i4a_local_fpS_rows_level`; independent.
4. `MarkedFanLocal`: `fanHL_local_marked` on the original `compY`, with the exact cut and `AgHatDir` hypotheses above (`MARK-FAN`); independent.
5. `MarkedI5Functional`: `i5_functional_hat_marked` through `i5_functional_hat_dir_of_fan`, uniform in `t`; independent.
6. `MarkedScaledCount`: `hat_vpart_bound_dm_marked_scaled`, including cubic difference, `hreal`, and the old-block count (`MARK-COUNT`); independent in the zero class.
7. `MarkedRootAttach`: `marked_bridge_family_bound`, using `subset_bridge`, `bridge_isDj_and_le`, `fibre_weighted_le` and locality monotonicity; independent.
8. `MarkedParamFamily`: `E1MarksC_zeroClass_family`, finite identity, bound, anchor, locality and joint analytic chart; independent in the zero class.
9. `MarkedClassTerms`: `E1MarksC_general_family`, old energy and determinant terms; dependent on local versus global generating sets and the amended class domain.

**OPEN final status.** The marked row lemma, physical Taylor identity and bridge geometry are landed. The exact missing assertions are `MARK-BALL`, `MARK-AN`, `MARK-FAN`, `MARK-COUNT`, and their joint parameter composition. Consequently the rooted sharp marked
family above is proved only conditional on them.
