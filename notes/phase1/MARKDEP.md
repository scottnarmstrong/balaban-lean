# MARKDEP: configuration locality of the energy marks

13 October 2026. Read-only source tree: `/home/scott/Balaban`. **PROVED** means a landed declaration or the elementary
deduction stated here. **PROVED CONDITIONAL ON** names the hypotheses of a landed declaration. **OPEN** names a missing
physical or record-level assertion. **REFUTED** identifies an invalid inference, not a formal Lean negation. All Lean names
below were checked against declarations in that tree.

## The consumer and the obstruction

**PROVED.** `Fluctuation/Thm31cde.lean`, `InterpMarks`, has `G : ι → ℂ → (∀ b, BS.Ωb b) → ℂ` and `dep : ∀ i u, DepOn
(blocksOf m₀ K Set.univ (Lab.ysite (y0 i))) (G i u)`. The variable in `dep` is the product **block configuration** `Φ`. It is
not the old unit fluctuation field `ψ′`. The same record asks for `meas`, a bound for **all** `u,Φ`, `holG` on open `𝒰`, and
`hF : ∀ s ∈ [0,1], ∀ᵐ x ∂ν, f s x = ∑ i, G i (s:ℂ) (BS.restr x)`. Its `hκG` is `κH ≤ κG`; `hκ` is `κ′+3κ0+c1 d L+3/2 ≤ κH`.
Its `hε` constrains `εH,Kc,κH,κ0,κ′`, and does **not** contain `F0`.

**PROVED.** `StepComplexThm31.E1MarksC S C BS z` abbreviates this record with `W = S.WoneC C` and `f s x = (fderiv ℂ (S.Phi1C
C) ((s:ℂ) • S.shiftUC x)) (S.maskUC z (S.shiftUC x))`. Thus `hF` identifies the exact masked derivative of the exponent, on
the physical slice. For `C = zeroClass`, `StepComplexSmall.dEC_zeroClass` and `MarkedCubicTaylor.Phi1C_zeroClass` reduce
`Phi1C` to `-β VkC`. They do not identify a decoupled block energy sum with `VkC` by themselves.

**PROVED.** `Thm31CoeffAnalytic.ParamMarkFamily` has **no locality field**. Its fields are open parameter sets `V,𝒰`, a
compact carried configuration set `Q`, global `meas` and `bound`, joint `holA,holG` on `V×𝒰` at `Φ∈Q`, and `contA,contG` on
`Q`. Locality is passed separately to `Thm31CoeffAnalytic.norm_gsumCoeff_le` and
`ParamCarrierLocal.paramMarked_analytic_local_bound`. Hence the follow-up's phrase “`ParamMarkFamily`'s locality fields” is
**REFUTED**.

**PROVED.** `MarkedFieldCount.markedOut_field_congr` reads the **unit field** only through its lift on `psiThick Y′`, and the
datum on `thickSet Y′`. But `StepComplex.shiftUC x = β_k^{-1/2} KC(yhat x)`; `KC` is the uncut covariance square root and
generally has off-site matrix entries. Agreement of two `Φ` on the blocks of `Y′` need not imply agreement of their `shiftUC`
fields on `psiThick Y′`. **REFUTED:** composing the cubic `markedOut` with `shiftUC` and citing `markedOut_field_congr`
proves `InterpMarks.dep`. `MarkedRootAssembly.markedRootAssembly_zero` proves an analytic `M`, one cubic `Ev`, root geometry
and the physical `hF` identity under its hypotheses, but does not repair this gap.

## What the source formulas say

**PROVED (source check).** P4, printed pp. 694–695, (2.51)–(2.60), first makes the Gaussian change of variables and then
expresses the local energy contribution through the interpolation derivative in (2.57), with the block sum (2.56). P5,
printed p. 519, (3.14)–(3.17), uses the same derivative after substituting `β_k^{-1/2} C^{(k)1/2} ψ` and pre-localizes the
resulting function. P5 explicitly says the remaining localization details are deferred in its §3. These formulas support
localization of the **composite function of the hat field**; they do not assert that a locality estimate in the old unit
field survives substitution. Proposition 2.6 of `FLUCTUATION.md` §2.6 is the algebraic
interpolation/change-of-variable statement derived from P4, not a termwise hat-locality theorem. The theorem 3.1(c)–(e) consumers in
`Thm31cde.lean` are conditional on `InterpMarks` and the additional respective output-size inequalities.

**PROVED CONDITIONAL ON** the sharp expansion's covariance and chart hypotheses: `SharpVF.fsite_expansion_hat_dir` expands
the composite `flFieldOne D (hatLift D ψ̂)` into terms `Ev Y (rawOf D,ψ̂)` local under `AgHatDir Y`.
`SharpAssembly.interaction_expansion_hat_dm_dir` and `InteractionHatAssemble.interaction_expansion_hat` assemble such hat
terms. `SharpAE.AgHatDir` requires raw-data agreement on `thickSet Y` and hat-field agreement on the unit points of `Y`. This
is where the square-root dependence is localized: cut parameters in `Localization.I5Expansion.localization_expansion` act on
the full composite containing `hatLift`; `StepComplexHat.hatLift_eq_liftC` identifies the uncut value. No claim that
`hatCovSqrt` has a stand-alone exact finite-range kernel is needed. `HatLabelsDirect.labelAct_of_directTerms` then transfers
hat locality to `Φ` using the `DirectTerms` agreement map `hag`, and proves `DepOn (blocksOf Y)`. This is the activity-side
model for the marked bridge.

## The decoupled marks and their exact reach

**PROVED.** `MarkedVBlockDec.markedTangDec` is the lift of `u cc decCovSqrt(1) ψ̂ + t maskBlock Zm (cc decCovSqrt(1) ψ̂)`.
`MarkedVBlockDec.evDec` is a cut-expansion coefficient of `markedFunDec`, the block energy along that tangent, rather than a
cubic Taylor coefficient in `ψ′`. `MarkedTwoMarkLocal.vblock_expansion_hat_marked_scaled_two` uses one `F₁,Sol` for all
admissible `(u,t)` and makes the coefficients local under `AgHatDir Y`. Its eighth clause makes a coefficient independent of
`t` if its read set misses `Zm`. This expansion therefore localizes the covariance square root **inside** the mark.

**PROVED CONDITIONAL ON** all hypotheses displayed in `MarkedScaledCountDec.marked_count_scaled_dec`: the derivative at `t=0`
of the sum of `markedFunDec` over old blocks equals the double sum of the derivatives of `evDec` over their old polymer
domains. The equality of that double sum with the rooted sum requires its `hzero` antecedent: if `psiThick Y ∩ fineBlock zr =
∅`, then `∂_t evDec(b,Y)|₀=0`. **PROVED CONDITIONAL ON** the additional root-mask hypothesis `hZm : ∀ p∈Zm, ∀ y, unitPt hG′
y=p → y∈fineBlock zr`, `MarkedTwoMarkLocal.marked_count_scaled_dec_resummed` discharges `hzero` using the eighth clause above
and gives the rooted identity unconditionally. `MarkedRootAssembly.markRealAt_of_chart` and
`WoneChartIdentity.vkC_ray_vanish_chart` address the cubic/physical identity; they are not the proof of this decoupled
`hzero`.

**PROVED CONDITIONAL ON** the same count hypotheses: put `a=2κdec−1`, `M=L^(m₀+m₁)`, and `E_*=energyBdScaled …` with the
exact `cK2′`, `famConst`, `rho4` arguments of `marked_count_scaled_dec_resummed`. For each output `Y′`, its decoupled mark is
bounded by `F_dec exp(-a d(Y′))`, where `F_dec=(‖E_*‖/t₀)c1(d,L)M^d nFibre(d,L) exp(a cBr(d,L))`. The count also proves
`markedOutDec≠0 → IsDj Y′ ∧ rootCube zr∈blocksOf Y′` and the weighted rooted entropy sum when `aEnt+1≤a-a′′`. The root factor
and bridge/fibre costs are present; the `r^-3` factor is absent. For the exponent `Phi1C=-β VkC`, the candidate constant is
`β F_dec`.

**PROVED CONDITIONAL ON** `MarkedEvJoint.markedEv_joint_param` and `MarkedEvJoint.markedEv_joint_physV`: one choice of
`F₁,Sol` has joint analyticity of `evDec` in datum, hat field, and `(u,t)` on the stated open marked-radius domain, and
analytic `t`-derivative marks on `physV`. This gives the analytic input for a finite rooted sum on a fixed carrier. It does
not itself give `DepOn` of that rooted sum as a function of every block `Φ`, nor global `meas`, `bound`, `contG`, or the
physical `hF` identity.

**OPEN (configuration bridge).** For a shared label `Y′=bridge zr Y`, prove that block agreement of `Φ,Φ′` on `blocksOf Y′`
implies `AgHatDir Y` for `(rawOf D,hatOf Φ)` and `(rawOf D,hatOf Φ′)` on the carrier. At fixed datum the raw-data component
is automatic; `Y⊆Y′` handles the hat sites. Then use the same `evDec` locality for every `t` near zero, differentiate the
equality, sum the finite bridge fibre, and clamp/extend to **all** product configurations. The clamp must preserve block
dependence and be measurable, and agree with the physical `hatOf` on the measure-carrying set.
`HatLabelsDirect.labelAct_of_directTerms` shows the corresponding transfer for activities, not for these marks.

**OPEN (physical identity).** On constant-`h₀` data and the real hat ball, prove `-β ∂_t Σ_b markedFunDec(b,D,ψ̂;s,t)|₀ =
(fderiv ℂ (S.Phi1C zeroClass) (s • S.shiftUC x)) (S.maskUC zr (S.shiftUC x))`, with `ψ̂=yhat x`. Identify `decCovSqrt(1)`
with `S.covSqrtC` by their definitions (or the applicable `Localization.decCovSqrt_one_eq_real` under its positivity
hypotheses), identify `Zm` with `blockU zr`, and match the block-energy sum with `VkC`. Then
`marked_count_scaled_dec_resummed` and finite differentiation give `hF`. The cubic `markedRootAssembly_zero` supplies a
separate proved physical identity; equality of the two rooted sums follows only after the common total-derivative identity.
Neither equality of individual cubic and decoupled coefficients nor `hF` for varying external `h` is asserted.

## Numerical decision and alternative

**PROVED.** The `InterpMarks` record itself needs only positive `F0` and `κG≥κH`; it does not demand `r^-3`. But
`Thm31cde.interpAvg_expansion_bound` requires `CPE Σ_i F0(i) exp(-κ0 dl(y0 i)) ≤ B` for a chosen output budget `B`. For
Theorem 3.1(c), `Thm31cde.thm31c_of_input` sets `B=β_k^-1`. With bridge entropy, the available decoupled estimate gives the
sufficient test `CPE K0 β F_dec ≤ B` (plus the activity and rate inequalities). **OPEN:** no landed physical numerical
theorem proves this test. For the usual `cc=β_k^-1/2`, `cψ=p₁`, the mark radius is proportional to `β_k^-1/2 p₁`; a `t₀`
admitted by `(‖u‖+t₀)markedRad<δ₁` is at most of order `√β_k/p₁` when the fixed constants are positive. Thus optimizing this
**available upper bound** still leaves a scale of order `√β_k p₁` after multiplying by `β`; it cannot certify `β_k^-1`. This
does not rule out cancellation or a sharper decoupled estimate. The cubic count's `r^-3` improves that estimate, but its
composition locality is open.

**OPEN alternative.** Start with a cubic `markedBlockTerm` of the general-tangent block expansion; compose its tangent with
`liftC((u+t M_z) cc M(Θ) ψ̂)` **before** applying the cut expansion. Use `Localization.I5Expansion.localization_expansion` or
the marked wrapper `MarkedEvParam.i5_functional_hat_marked_exposed` on parameter `((Θ,ψ̂),(u,t))`; prove sharp `AgHatDir` and
analytic/Cauchy bounds. No declaration named `marked_expansion_product_pair` was found. One must account for an additional
cut sum, its rate loss and coefficient constant, retain the root vanishing, and reprove the physical derivative identity.
There is no licensed claim that its old `3E_*/(r³t₀)` constant survives unchanged.

## Recommended leaves (each at most 300 Lean lines)

| Leaf | Exact deliverable and inputs | Status / assignment |
|---|---|---|
| `decMarkHatToBlocks` | Transfer `AgHatDir` locality of `evDec` derivatives through `hatOf` and `bridge`, with one carrier clamp; use `MarkedEvJointPhysV`, `MarkedCommonLabels` geometry and the `HatLabelsDirect` transfer pattern. | **OPEN**, strong; start now. |
| `decMarkPhysicalTotal` | Equality of the derivative of the decoupled block sum and the `E1MarksC` integrand on the constant-`h₀` slice; use `shiftUC`, `covSqrtC`, `Phi1C_zeroClass`, `markRealAt_of_chart`, and `marked_count_scaled_dec_resummed`. | **OPEN**, strong; start now. |
| `decMarkGlobalFields` | One global measurable and bounded clamped `G_z`, with `dep`, `holG`, `contG` and common labels, parameter sets and carrier; use the preceding two leaves and `markedEv_joint_physV`. | **OPEN**, strong; after locality bridge. |
| `markBudgetOrCubicCuts` | Either sharpen the decoupled count enough to prove `CPE K0 β F0≤B`, or cut-expand the cubic composite with an explicit rate and prefactor; preserve `hzero`. | **OPEN**, strong; begin numerical audit now, then choose branch. |
| `e1MarksCFromLocalizedMarks` | Assemble one activity `hW`, all-root marks `hF`, and every `InterpMarks` field at the physical scale; retain `ParamMarkFamily` separately for joint analytic coefficients. | **PROVED CONDITIONAL ON** the preceding OPEN leaves and the zero-source activity package; strong integration. |

**Recommendation.** Use decoupled `evDec` for the first configuration-locality leaf: its cut expansion already contains the
square root and its root vanishing is landed. Run the numerical leaf in parallel with the exact physical identity. If its
output bound cannot meet the selected budget, use the cubic cut alternative; do not substitute the unit-field `markedOut` for
a block-local `G` meanwhile.
