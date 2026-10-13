# STEPSTATEMENT — zero-class output at one shared tower

**PROVED. Snapshot.** Read-only statement and consumer inspection at `/home/scott/Balaban` commit `956241c6d2cc7f0b805d187e315d8f77f73043d4` (2026-10-13 UTC). All cited declaration names were checked by `rg` in that tree. This is a proposed assembly target, not a frozen or elaborated Lean declaration.
**OPEN. Exactness limit.** No current definition characterizes the physical `E0θ`, `M0θ`, or the summed `IsDj` energy family on their full carriers. Consequently there is no honest *final exact* Lean theorem command for all six requested clauses today. The following Lean fragments fix every binder and landed carrier; the three marked gaps must be replaced by source-characterized definitions and equality clauses before freezing. Existentially choosing arbitrary functions would make the renormalization record too weak.

## 1. Statement to assemble

**OPEN. Outer binder spine.** The inheritance chain is `StepTowerRenSol → StepTowerRenEnd → StepTowerRen → StepTower`; set `T` once and use it in every lane. `D` is an existential conclusion, not an unproduced hypothesis. The chosen `β₀` dominates the tower ray threshold and all later activity/mark thresholds; scalar constants precede `k,N₁,ν,β,p₁`.

```lean
theorem zeroClassStep_output_fromTower
    {κmin : ℝ} (R : StepTowerRenSol κmin) (hHull : stepHullMin ≤ κmin)
    (A₁ : ℝ) (hA : 0 < A₁) (p : ℕ) :
    let T : StepTower κmin := R.toStepTowerRenEnd.toStepTowerRen.toStepTower
    let O : StepOutputConsts 3 3 := stepOutputPhysical T hHull
    ∃ β₀ CE CF CE' CF' : ℝ,
      2 ≤ β₀ ∧ 0 < CE ∧ 0 < CF ∧ 0 < CE' ∧ 0 < CF' ∧
      (∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁]
         (h3N : 3 ∣ N₁) (hN : 5 < N₁) (ν : ℝ)
         (hν0 : 0 < ν) (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1)
         (β : ℝ) (hβ : β₀ ≤ β) (p₁ : ℝ) (hp₁ : 0 < p₁)
         (hpLog : p₁ ≤ pLog A₁ p (β * 3 ^ k)),
        ∃ D : StepScaleData T k hk N₁ ν β p₁,
          let S := T.step k hk N₁ ν β p₁
          let C := zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)
          let G := lvTop N₁ T.m₁ k (rhoSep T.m₁)
          -- The following six conjuncts are expanded below, with gaps marked.
          SourceExponent S C D O CE CF ∧
          EnergyTerms S C D O ∧
          CommonMarks S C D O ∧
          ObservableMarks S C D O ∧
          RenormInput G S C D R O ∧
          O = stepOutputPhysical T hHull)
```

**OPEN. Placeholder warning.** `SourceExponent`, `EnergyTerms`, `CommonMarks`, `ObservableMarks`, and `RenormInput` above are *names for the immediately following conjunctions*, not Lean definitions or admissible hypotheses. The outer block is a binder blueprint, deliberately non-elaborable until those clauses and the missing physical definitions are supplied. It must never be installed as a theorem with `sorry` or a generic Prop bundle.
**OPEN. Rate choice.** Fix `κa=O.kout` and `κb=O.kout` from the tower before scale; `O.kout=3/2*T.κdec≤2*T.κdec` meets `renLocC1_scale_of_tower_of_le` and gives one intended output rate. The scalar majorants `BE0,BM0` may vary with `β,k,p₁`, but their formulas and constants must be selected before the scale and verified after the physical fibre estimates.

**PROVED. Source/activity type fragment.** The landed `stepPieces_fromTower` already gives one `𝒴,hdom` before `∀g`; its exact shared-label equalities should be retained, together with the `StepActivityBoundC` and `prop26C_step` conclusions at each `g∈l1Ball`. The equation below is the actual landed Prop 2.6 conclusion, with `S` and `C` as above:

```lean
∃ 𝒴 : Finset (Set (CTorus 3 3 N₁ T.m₁ (k + 1))),
∃ hdom : ∀ Y ∈ 𝒴, IsDj 1 (k + 1) Y,
∀ g : Fld 3 3 N₁ T.m₁ (k + 1) 2, g ∈ l1Ball 3 3 N₁ T.m₁ (k + 1) 2 →
  ∃ BR : StepActivityBound S C g, ∃ BC : StepActivityBoundC S C g,
    BR.m₀ = 1 ∧ BC.m₀ = 1 ∧
    BR.Lb = ({Y // Y ∈ 𝒴} ⊕ {Y // Y ∈ 𝒴}) ∧ BC.Lb = BR.Lb ∧
    HEq BR.Lab ((thickLabels 𝒴 hdom).sum (thickLabels 𝒴 hdom)) ∧
    HEq BC.Lab BR.Lab ∧
    HEq BR.BS (S.blockSplit 1 hp₁) ∧ HEq BC.BS BR.BS ∧
    S.StepRegularC C g ∧ S.StepNonvanishingC C g ∧
    S.TstepC C g = Complex.exp (-(S.β : ℂ) * S.AnewC +
      EcompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k) S.psiKdC -
      (S.Eppp C : ℂ) * (S.nU : ℂ) +
      FcompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k) S.psiKdC g +
      S.E0C C + S.F0C C g)
```

**OPEN. Source chart strengthening.** Add one `JointRep` and one direct-term family on `physV S 1 ν T.t` using the *same* `𝒴`, with `Jr.W1+Jr.W2` equal a.e. to the label sum on both segments. The current `sourcePhysVal_jointRep_zero` proves a two-segment `physVal` formula only on the constant-`h₀` fibre; the chart-wide a.e. equality has no named producer. This requirement belongs in the conclusion before the marked family is constructed.

**OPEN. Energy type fragment.** `DetExpansionLocC S 1 z T.t (towerDetRate T.κ) (towerDetConst T.κ)` is the exact landed determinant family. `E1MarksC S C (S.blockSplit 1 hp₁) z` is the exact fixed-step mark type. At the central datum, `e1CoeffC I ((E z).toDetExpansionC hD) U` is the raw cube coefficient. The requested output instead needs a *single* jointly analytic function `ePlus z X q` on rooted `IsDj` polymers `X`, obtained by regrouping mark supports and `detCollarHull` supports, with all of these conclusion fields:

```lean
-- Missing physical definition: ePlus : Root → IsDjPolymer → physParam 2 S → ℂ.
-- Required central-slice equality, once ePlus and finite support 𝒳 are defined:
∀ z, (∑ X ∈ 𝒳 z, ePlus z X (⟨rawOf S.D', rawOf_mem_rawSub _⟩, 0)) =
  S.E0locC C z
-- Required on every q ∈ physV S 1 ν T.t: AnalyticOnNhd in q,
-- equality under agreement on X, bound by B_E * exp (-O.kout * sizeJ 1 (k+1) X),
-- IsDj 1 (k+1) X, rootCube z ∈ blocksOf 1 (k+1) Set.univ X,
-- generated lattice covariance and complex spin-rotation invariance.
```

**REFUTED. Energy shortcut.** `thm31aC_coeff` supplies the fixed-datum sum of `e1CoeffC`, while `detPackage_fromTower` supplies determinant hull terms across a chart. Neither constructs `ePlus`, and a third additive activity coefficient would double-count the mark part. The energy sum is `E0locC C z`; summing roots then gives `E0C C`, not the whole exponent of `TstepC`.

**OPEN. Mark and observable type fragments.** The exact all-root requirement is `∀ z, E1MarksC S C (S.blockSplit 1 hp₁) z` with one `ParamMarkFamily` on the same enlarged root labels and with the same `A0` underlying the source activity. The observable requirement is `∀ g∈l1Ball, ∀ y i, ∃ I : ObsMarks S.nuFl (S.blockSplit 1 hp₁) (fun t x => S.WoneC C 1 x + S.WtwoC C g t x) (fun t x => deriv (fun r => McompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k) (S.dataUC (S.psiAtC r x)) g y i) t) (rootCube (m₀ := 1) (blockIndex y)), I.Kc ≤ O.Ktot ∧ I.κ0 = O.k0 ∧ I.κH = O.kH`. Its activity half must be transported to `obsLab`; `ObsMarks.toConsumer` transports the integrand after the physical record exists.

**OPEN. Renormalization type fragment.** The record must bind one `F` supplied by `renEndpoint_scale_of_tower`, the same `R.r₀`, `cK=renCK 3 3 2 R.BG R.κ`, `B=8*R.t`, `Kloc=1`, `blk z=blockSites 3 3 N₁ T.m₁ (k+1) k z`, `Ys z=renYs (renCube G (X1 G 1 k (fam 1 (blockSite k z)))) G 1 (X1 G 1 k (fam 1 (blockSite k z)))`, `dY=renDY G 1`, and one site-root cover `YsM`. Set `κa=κb=O.kout`; both meet the landed `≤2*T.κdec` bound. Its complete landed type is:

```lean
RenormExpInput G (compWeight 3 1) ν R.t R.r₀
  (renCK 3 3 2 R.BG R.κ) (8 * R.t) F blk Ys YsM (renDY G 1)
  O.kout O.kout 1 BE0 0 BM0 0 E0θ (fun _ _ _ => 0) M0θ (fun _ _ _ => 0)
```

**OPEN. Physical definitions.** Here `E0θ : Root → BgData G 2 → (Fin 3 → ℂ) → ℂ` and `M0θ : G.Ω 1 × Fin 2 → BgData G 2 → (Fin 3 → ℂ) → ℂ` need source-characterized definitions before this is a final theorem. `RenormExpInput` has seven fields: `locC1`, `locC2`, `expE0`, `expOld`, `locDφ`, `expM0`, `expOldM`. `renormExpInput_zero_of_fields` supplies the two old fields once the other five are proved, and it never supplies physical `E0θ` or `M0θ`.

**PROVED. Constants fragment.** `O = stepOutputPhysical T hHull` is already definitional; keep `O.kout=3/2*T.κdec`, `O.kH=2*T.κdec-1`, `O.Ktot=O.Kc+O.Kall`, `O.kout≤O.lhull`, and `R.r₀` fixed from the same tower. `StepTower.marks_Kc'_le_Ktot`, `marks_theta_le_stepTheta`, and `exists_beta0_marks` are the numerical bridges; their inputs are the chosen activity constants, so the final maximum threshold is selected only after those constants.

## 2. Producer map

| Clause | Status at the pinned tree | Exact producer or needed wrapper |
|---|---|---|
| Shared `R,T,D`, constants and threshold order | LANDED BUT NEEDS A WRAPPER | `exists_stepTowerRenSol`, `StepTower.scale`, `stepPieces_fromTower`, `stepOutputPhysical`; take a maximum of ray, source, mark and radius thresholds before scale. |
| Shared real/complex source activity labels | LANDED | `stepPieces_fromTower` yields `𝒴,hdom` before `∀g`, doubled labels and `HEq` fields; `sourceActivityC_scale_fromTower` is its activity leaf. |
| Prop 2.6 exponent at each source | LANDED BUT NEEDS A WRAPPER | `prop26C_zeroClass_of_activity` then `prop26C_step`; specialize the common `BC` and record the `StepRegularC` and `StepNonvanishingC` inputs. |
| Full chart source exponent family | IN FLIGHT | `W1_zeroClass_eq_hat_chart`, `sourcePhysVal_jointRep_zero`, `DirectTermsFamilyOn`; prove `physVal` to common label-sum and the a.e. two-segment `hW`. |
| Determinant root/hull family | LANDED | `detPackage_fromTower`, `detGrouped_chart_family_fromTower`, `StepTower.kout_le_hullRate`; family `E z` is chosen once per scale. |
| Physical marked energy family, all roots | IN FLIGHT | `markReal_slice_of_count`, `paramMarkFamily_common`, `markedEv_joint_physV`; missing physical `G`, `hF`, and common chart activity. |
| Summed `ePlus` on one `IsDj` index | OPEN | Define physical mark plus determinant family and two support maps; prove summed identity, chart locality, rate, anchor and symmetries; split into ≤300-line leaves below. |
| Physical `ObsMarks` for every `(g,y,i)` | IN FLIGHT | `obsMarks_of_tilt`, `ObsMarks.toConsumer`, `obsLab`; needs the activity tilt with `holt`, `holσ`, `zero`, `hW` on the same labels. |
| Renormalized `F`, unit endpoint and `locC1` | LANDED BUT NEEDS A WRAPPER | `renEndpoint_scale_of_tower`, `renLocC1_scale_of_tower_of_le`, `renCK_ge`; select the proper `X1` and shared `R.r₀`. |
| `locC2`, `locDφ` on shared `F`/cuts | IN FLIGHT | `renC2_local_cut`, `renDphi_local_cut`, `renDec_solution_family_exists`; prove one cut family agrees with the endpoint `F`. |
| Physical `expE0`, `expM0` | OPEN | Define `E0θ,M0θ`; prove `IsLocExp` on `Ys,YsM`, including chart inclusion and fibre bounds. |
| `expOld`, `expOldM`; complete record | LANDED BUT NEEDS A WRAPPER | `renormExpInput_zero_of_fields` fills old fields after the five physical fields; assemble at `cK=renCK`, `Kloc=1`. |

## 3. Adjacent-conjunct acceptance check

**PROVED. Tower/scale → activity.** `stepPieces_fromTower` uses the *same* inherited `T.step k hk N₁ ν β p₁` and `StepScaleData T ...`. `R` must be projected once; a separately chosen `exists_stepTower` would change `m₁,BG,κ,t`. Wrapper: project and pass `D`; about 40 lines.
**PROVED. Activity → Prop 2.6.** `BR` and `BC` share `𝒴`, `Lab`, `BS` by the stated `HEq` fields; transport over those equalities before invoking `prop26C_zeroClass_of_activity`. This is a wrapper, about 60–100 lines.
**REFUTED. Activity → energy mark.** The `BR/BC` label type is `{Y∈𝒴} ⊕ {Y∈𝒴}` at each fixed source; `E1MarksC` wants an interpolation activity on root-union labels, jointly analytic in chart datum and complex interpolation variable. Extend the zero-source activity by `commonLabels`, then prove `hW` and `holA` on the same `ParamMarkFamily`; about 200–300 lines after the physical family exists.
**REFUTED. Source chart → mark chart.** `physVq` in `stepPieces_fromTower` varies raw data and scaled source with radius `q≤1`, while `WoneChartIdentity` and `markReal_slice_of_count` establish identities on the constant-`h₀` fibre; `physV` admits varying complex `h`. Strengthen the source/mark family side to full `physV` or state the energy sum only on the honest fibre; 150–250 lines plus a new analytic family.
**REFUTED. Mark → determinant energy.** `thm31aC_coeff` joins mark and determinant at one datum and a `CubeB` index; `detGrouped` is on collar hulls, and mark terms read `Yhat(sitesOf U)`. Change the output side: define `H_mark(U)` and `H_det(U)=detCollarHull U`, then sum fibres into one `IsDj` index; two leaves of 180–300 lines each.
**REFUTED. Energy → observable.** `E1MarksC` uses `WoneC C` and a masked `fderiv Phi1C`; `ObsMarks` uses `WoneC C 1 + WtwoC C g t` and the source derivative of `McompAtC`, with `obsLab` and a site root. Construct a separate tilt on the extended base activity and prove its four activity fields; about 200–300 lines. Reusing the energy mark record is ill typed.
**REFUTED. Base labels → `obsLab`.** The observable label type is `ObsLb Lb₀ 1 𝒴`, whose `obsLab` adds source-domain and single-cube labels to the base `Lab₀`; it is not definitionally the doubled `{Y∈𝒴} ⊕ {Y∈𝒴}`. Extend the activity by zero and transport `hW`, bounds and entropy cost to `obsLab`; about 100–180 lines after the tilt exists.
**REFUTED. Observable → renormalized `M0θ`.** `ObsMarks.toConsumer` yields a fixed-step integrand record; `RenormExpInput.expM0` needs an `IsLocExp` family for every `D∈XiCOneReal` and `‖ξ‖<R.r₀` on `YsM`. Define `M0θ` and prove chart inclusion, site-root regrouping and bounds; three leaves of 180–300 lines.
**REFUTED. Energy → renormalized `E0θ`.** `E0locC` is a fixed-step value; `expE0` needs a function of `D,ξ` on the complete renormalized chart. Define `E0θ` from the physical marked plus determinant family at the shifted datum, prove its zero-parameter identity, then regroup into `renYs`; three leaves of 180–300 lines.
**REFUTED. Cut endpoint → localization fields.** `renEndpoint_scale_of_tower` gives an `Fcut` for any `X₁`, while `renLocC1_scale_of_tower_of_le` fixes `X₁=X1 G 1 k (fam 1 (blockSite k z))` per root. Choose one compatible *family* of cuts before building `locC2` and `locDφ`; an arbitrary per-root `Fcut` need not agree with the single `F`; 150–250 lines.
**REFUTED. Class constants → renormalization record.** `locC1` was proved first at `2+2K4 ξ1`, while perturbation uses `renCK`; applying `renLocC1_scale_of_tower_of_le` changes the `locC1` side to `renCK`. `renCK_mul_ge` supplies the perturbative comparison; wrapper about 60–100 lines.
**REFUTED. Radii and rates.** The step source chart uses `p₁`, direct terms need `2p₁`, marked discs use `17/16`, and the renormalization chart uses `R.r₀≤1/16`; none are definitionally the same. Prove the required inclusions separately, with one `β₀` dominating their thresholds; 120–220 lines. `O.kout`, `O.k'`, `O.lhull`, `κa`, and `κb` have distinct meanings and need explicit inequalities.

## 4. Scope still outside this generator theorem

**OPEN. Uniform roots.** The displayed conclusion quantifies every root at one finite step; the later class bound needs its constants independent of the chosen root and compatible with restriction to subregions.
**OPEN. Torus coherence.** Coefficients chosen separately for `N₁` must agree on overlapping tori under the frozen Root-F coherence clause; no pointwise step theorem supplies that automatically.
**OPEN. Mass interval.** This theorem assumes `ν*3^(2*(k+1))≤1`; Root-F permits every `0<ν≤1`, so a scale transition or a separate mass regime is still needed.
**OPEN. Dimensions and spin.** The tower fixes `d=L=3,N=2`; frozen Root-F quantifies `d≥3,N≥2` with its own admissible `L` and unit field `h`.

## 5. Ordered bounded leaves

| Order | Leaf, each ≤300 Lean lines | Dependencies |
|---|---|---|
| 1 | One `β₀` and projected `R→T` wrapper, preserving `CE,CF,CE',CF'` and the mark threshold. | `stepPieces_fromTower`, `StepTower.scale`, `exists_beta0_marks`; **OPEN**. |
| 2 | Common chart `hW`: identify the two-segment `physVal` formula with the common direct-term activity sum and specialize to `BC.hW`. | `sourcePhysVal_jointRep_zero`, `DirectTermsFamilyOn`, leaf 1; **OPEN**. |
| 3 | Physical `ParamMarkFamily` with one root-union label system, marked `G`, `hF`, `holG`, `contG`; restrict it to `E1MarksC` for every root. | `markReal_slice_of_count`, `paramMarkFamily_common`, leaf 2; **OPEN**. |
| 4 | Define the physical `ePlus` mark and determinant support maps and prove its central sum, chart analyticity, locality, anchor, symmetry and `O.kout` bound in separate ≤300-line files. | `thm31aC_coeff`, `detPackage_fromTower`, `detGrouped_chart_family_fromTower`, leaf 3; **OPEN**. |
| 5 | Physical observable tilt and all `(g,y,i)` `ObsMarks` on `obsLab`, then `ObsMarks.toConsumer`. | `obsMarks_of_tilt`, `ObsRayAnalytic`, `ObsIntegrandBridge`, leaves 2–3; **OPEN**. |
| 6 | One shared cut family for `F`, `locC2`, `locDφ`, plus `locC1` at `renCK`. | `renEndpoint_scale_of_tower`, `RenormC2Local`, `renLocC1_scale_of_tower_of_le`; **OPEN**. |
| 7 | Define and characterize physical `E0θ,M0θ`; prove chart inclusion and zero-parameter identities. | Leaves 4–6, `RenormExpInput` carriers; **OPEN**. |
| 8 | Prove `expE0` and `expM0` fibre bounds on `renYs,YsM`, then assemble the seven-field record with zero old terms. | `renormExpInput_zero_of_fields`, leaves 6–7; **OPEN**. |
| 9 | Assemble the final conjunction without extra hypotheses; compare each field against the exact consumer type. | Leaves 1–8; **OPEN**. |

**OPEN. Acceptance verdict.** The binder order, tower projection, shared activity labels, determinant lane and numerical record are composable as stated. The full theorem cannot yet be frozen because the marked energy, observable and renormalized physical families lack source-characterized definitions and the chart/index joins above are unresolved.
