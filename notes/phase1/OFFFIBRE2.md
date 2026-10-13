# OFFFIBRE2: first Lean targets for the joint $(\Psi,h)$ chart

**PROVED (scope).** Read-only main commit `a45f885052266f196a68cd4bb8dcc0f369d8855e`; no build. “PROVED” describes declarations inspected at that commit. The Lean blocks below are **OPEN target declarations**, with new names explicitly identified; they are specifications, not claims of elaboration.

## T1. Minimum type change and the old datum

**REFUTED.** `StepSetting.withDatumH D : StepSetting …` cannot be defined for arbitrary `D : BgData S.G' N`: `StepSetting.hh₀` requires `∀ x i, D.h x i=(S.h₀ i:ℂ)` (`Fluctuation/StepObjects.lean:241–251`; `StepComplexAnalytic.lean:324–327`). Nor can `withDatumH D = withDatum D hDh` be literal equality if `withDatumH` has a successor type. The cheap compatible choice is a chart wrapper containing the old physical setting and one free datum; its *datum projection* and all new complex objects agree with the old setting on the fibre. Replacing `StepSetting` itself would retype its many real cutoffs, domains, measures, and the tower's constructors.

**OPEN (leaf 1, `Fluctuation/StepSettingH.lean`, 150–230 lines).** These are the carrier and first exact target signatures. `dataUCH` is a **new definition**: form the old-level `BgData` with spin `liftC S.hG' ψ` and field inherited from `D`; `Background/Composition.lean:composeData` supplies the correctly clipped old field and its `h_layerConst` proof, while `isLayerConstant_liftC` supplies the spin proof. Since `stepG.Ω 1` is the whole torus (`S.hG`), its $h$ component equals `D.h` at every site. Keep `S.dataUC` and `S.dataU` unchanged.

```lean
namespace Balaban.Fluctuation
variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
variable (S : StepSetting d L N₁ m₁ k N ϱ)

structure StepSettingH (S : StepSetting d L N₁ m₁ k N ϱ) where
  D' : BgData S.G' N

namespace StepSetting
def withDatumH (D : BgData S.G' N) : StepSettingH S := ⟨D⟩

theorem withDatumH_fibre_datum (D : BgData S.G' N)
    (hD : ∀ x i, D.h x i = (S.h₀ i : ℂ)) :
    (S.withDatumH D).D' = (S.withDatum D hD).D' := rfl
end StepSetting

namespace StepSettingH
noncomputable def dataUCH (H : StepSettingH S) (ψ : S.EC) :
    BgData (stepG d L N₁ m₁ k ϱ) N := by
  let B := composeData (S.hG.precedes S.hG' (le_refl (k + 1))) S.a
    (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D') H.D'
  exact BgData.clip (stepG d L N₁ m₁ k ϱ) (liftC S.hG' ψ) B.h
    (isLayerConstant_liftC S.hG S.hG' ψ) B.h_layerConst

theorem dataUCH_h (H : StepSettingH S) (ψ : S.EC) (x i) :
    (H.dataUCH ψ).h x i = H.D'.h x i := by
  -- prove using S.hG and composeData's clipped h
  sorry

theorem dataUCH_fibre (D : BgData S.G' N)
    (hD : ∀ x i, D.h x i = (S.h₀ i : ℂ)) (ψ : S.EC) :
    (S.withDatumH D).dataUCH ψ = (S.withDatum D hD).dataUC ψ := by
  -- compare both raw components, then use BgData.eq_of_raw
  sorry
end StepSettingH
end Balaban.Fluctuation
```

**PROVED (body audit).** The landed definitions whose *bodies* explicitly insert `S.h₀` are `StepObjects.lean:dataU` line 317 and `rhoStep` line 355 (real physical objects), `StepIdentityReg.lean:rawU` line 112 (real), `StepComplex.lean:dataUC` line 302 (complex), and `StepComplexProp26.lean:rawUC` line 201 (complex). `withDatum` at `StepComplexAnalytic.lean:324` has the constant-field condition in its binder and writes `hh₀`, not in an independently variable field expression. `ParamDatumFamily.lean:paramSlice` line 151 and `SourceRadiusCarriers.lean:physFibreRho` line 103 intentionally *define fibre subsets*; they should remain so. The real `dataU/rhoStep/rawU` also remain physical-fibre definitions; only new `dataUCH/rawUCH` and their dependent complex `…H` objects read `H.D'.h`. Replacing the bodies of the existing definitions would break their definitional equalities, including `StepComplex.dataUC_yhat`; use new definitions plus fibre equality lemmas.

**OPEN (exact extra equality).** Add `rawUCH (H) ψ := (liftC S.hG' ψ,H.D'.h)` and prove `((H.dataUCH ψ).Ψ,(H.dataUCH ψ).h)=H.rawUCH ψ`. This replaces `StepComplexProp26.rawUC` in the new lane. `psiKdCH` is `composeData … (bgFieldC … H.D') H.D'`; `covSqrtCH`, `AnewCH`, `AoldCH`, `rhoExpCH`, `tKernelCH`, `TstepCH`, `WoneCH`, `WtwoCH`, `E0CH`, and `F0CH` must be new chart objects or be defined by the corresponding `JointRep` raw functions. Every one has a fibre comparison to the old complex object. No old definition needs mutation.

## T2. The next two leaves and their exact theorem heads

**PROVED (where constancy is used).** `StepComplex.lean:dataUC_psi0C` lines 383–405 uses `S.hh₀` only to identify the old critical datum's field. `StepComplexJoint.lean:rawOf_dataUC_psiHat` lines 148–160 does the same. In `StepComplexProp26.lean`, `dataUC_psiAtC_inUnionDomainC_plus` line 270 supplies the equality of old/new fields to the general `inUnionDomainC_of_tangent_hatLift`, and `JbgC_expansion` lines 401–415 supplies it to `expansion_quadratic`. These are the explicit uses of `S.hh₀` in that file; replacing them by `dataUCH_h` is the main algebraic lift. The Gaussian integral, determinant identity, and two-stage interpolation in `prop26C_step` lines 491–610 otherwise use the datum through the complex background and old-spin objects. This does **not** prove their numerical/chart premises or class regularity off the fibre.

**OPEN (leaf 2, `Fluctuation/StepProp26H.lean`, 220–300 lines, perhaps split once).** Define the `…H` objects by replacing `S.D'` with `H.D'` and the old `dataUC/rawUC` by `H.dataUCH/rawUCH` in the *complex* definitions, or identify them with `JointRep` at `rawOf H.D'`. New `ClassRegularCH` and `StepNonvanishingCH` must be the literal analogues of `StepComplexOut.lean:ClassRegularC/StepNonvanishingC` for `H.WoneCH/H.WtwoCH`; they are inputs, not conclusions. The target below packages only the unchanged numerical hypotheses in `ChartNum`. Its fields are exactly those of the `StepComplexProp26.prop26C_class` section; it contains no value identity.

```lean
variable {c BG κ eps Kc Cx c₂ BG₂ δ₁ δc R pp : ℝ}

structure ChartNum (S : StepSetting d L N₁ m₁ k N ϱ)
    (c BG κ eps Kc Cx c₂ BG₂ δ₁ δc R pp : ℝ) : Prop where
  hC : FlCore N S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν
    c BG κ eps Kc Cx c₂ BG₂ δ₁
  hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁
  hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc
  hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2
  hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4
  ha₁ : 0 < S.a₁
  hc7 : c7 d L N BG κ ≤ thm73C3 d L N
  hR : 1 < R
  hsmR : 2 * (compC4 d * (bgK1 d L N * (xiC1 d * eps))) +
    5 * (R * δ₁) ≤ bgC1 d L N
  hβ : 0 < S.β
  hp₁ : 0 < S.p₁
  hlt : S.p₁ < pp
  hδ₁ : Real.sqrt N * (S.betaU ^ (-(1 / 2 : ℝ)) *
    (covSupConstC d L N (compWeight L S.a₁ k) κ * pp)) < δ₁

theorem StepSettingH.prop26C_classH
    (H : StepSettingH S) (C : StepClass d L N₁ m₁ k N ϱ)
    (num : ChartNum S c BG κ eps Kc Cx c₂ BG₂ δ₁ δc R pp)
    (hX : XiCData S.G' S.a S.ν (k + 1) 1 eps H.D')
    (g : Fld d L N₁ m₁ (k + 1) N)
    (hc : H.ClassRegularCH C g) (hnv : H.StepNonvanishingCH C g) :
    H.TstepCH C g = Complex.exp (-(S.β : ℂ) * H.AnewCH +
      EcompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k) H.psiKdCH -
      (S.Eppp C : ℂ) * (S.nU : ℂ) +
      FcompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k) H.psiKdCH g +
      H.E0CH C + H.F0CH C g) := by
  sorry
```

**OPEN (proof route for leaf 2).** First generalize `dataUC_psi0C`, `compTangent_dataUC`, the plus-domain lemma and `JbgC_expansion`, keeping the unchanged numerical hypotheses. Then move the proof of `prop26C_step` to the H objects and make the old `prop26C_class` its fibre specialization using all `…H_fibre` equalities. A search for `S.hh₀` alone understates the work: `StepComplexJoint.JointRep.withDatum` and `StepComplexOutAnalytic.TstepJ_withDatum`, `W1_withDatum`, `W2_withDatum`, `PJ_withDatum`, `E1J_withDatum`, `F0J_withDatum` all have an `hD` binder and need new H comparison lemmas. The existing `prop26C_class` cannot be applied to an H datum by definitional reduction.

**PROVED (analyticity already available).** `StepComplexJoint.lean:JointRep.gJ` lines 307–313 sets the old raw field to `q.1.2`, the incoming raw $h$; `PJ`, `EJ`, `FcJ`, `rhoJ` retain it. `StepComplexOutAnalytic.lean:JointRep.TstepJ` lines 385–389 is a function of *all* raw $(\Psi,h)$, and `analyticAt_TstepJ` lines 415–454 proves its ambient analyticity at any `Θ∈XiCRaw` under exact path analyticity hypotheses for old `Edens/Floc`. Therefore `exists_analyticAt_TstepC_of_analyticAt_class` already constructs a jointly analytic **representative**, but its equality clause, lines 638–641, is restricted by `hD`. The new task is equality of that representative with the off-fibre step, not another parameter-integral proof.

**OPEN (leaf 3, `Fluctuation/StepAnalyticH.lean`, 90–160 lines after leaf 1).** Prove the pointwise comparison for every chart datum; then the full joint-analytic target follows directly from `JointRep.analyticAt_TstepJ`. The displayed `F` is the *same* function on the full raw space for every `D`, so this is joint $(\Psi,h)$ analyticity, not analyticity of a restriction to the fibre. `hPathE/hPathF` below have exactly the two path-premise types of `JointRep.analyticAt_TstepJ` (lines 418–426), with `Θ=rawOf D`.

```lean
theorem JointRep.TstepJ_withDatumH (Jr : S.JointRep eps pp)
    (hp₁ : 0 < S.p₁) (hle : S.p₁ ≤ pp)
    (C : StepClass d L N₁ m₁ k N ϱ)
    (D : BgData S.G' N)
    (hX : XiCData S.G' S.a S.ν (k + 1) 1 eps D)
    (g : Fld d L N₁ m₁ (k + 1) N) :
    Jr.TstepJ C g (rawOf D) = (S.withDatumH D).TstepCH C g := by
  sorry

theorem StepSettingH.analyticAt_TstepCH (Jr : S.JointRep eps pp)
    (hp₁ : 0 < S.p₁) (hle : S.p₁ ≤ pp)
    (C : StepClass d L N₁ m₁ k N ϱ)
    (D : BgData S.G' N)
    (hX : XiCData S.G' S.a S.ν (k + 1) 1 eps D)
    (g : Fld d L N₁ m₁ (k + 1) N)
    (hPathE : ∀ x : S.E, ‖x‖ ≤ S.p₁ → ∀ j ∈ Finset.Icc 1 k,
      AnalyticAt ℂ (fun p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N =>
        Edens C.m₀ C.Tm j p.1 p.2) (Jr.PJ j (rawOf D, yhat x)))
    (hPathF : ∀ x : S.E, ‖x‖ ≤ S.p₁ → ∀ j ∈ Finset.Icc 1 k,
      AnalyticAt ℂ (fun p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N =>
        Floc C.m₀ C.Tm j p.1 p.2 g) (Jr.PJ j (rawOf D, yhat x))) :
    (Jr.TstepJ C g (rawOf D) = (S.withDatumH D).TstepCH C g) ∧
    AnalyticAt ℂ (Jr.TstepJ C g) (rawOf D) := by
  sorry
```

## T3. Coefficient families: what is already off-fibre

**PROVED.** `RawData` (`Background/ApproxAnalytic.lean:36`) is a pair $(\Psi,h)$; its second projection is $h$. In `SharpENu.lean:eterm_expansion_hat_rawY` the parameter `u` is instead `(RawData,hat)`, so `u.1.2` is $h$ and `u.2` is the hat variable; its locality clauses explicitly compare the full raw pair and the hat field. `XiCRaw` does not impose `h=h₀`. `ParamActivitySubspace.lean:physParam/physV` and `PhysicalTerms.lean:physSΛ` retain the whole raw datum and the separate source, and are open in the raw subspace. This confirms the expansion/analytic parameter layer already accepts nonconstant complex $h$.

**PROVED with a boundary.** `Inhabited/E1CoeffFamily.lean:e1CoeffFamily_value_fromTower` gives analytic coefficients `c θ C` on `physV`, locality/bounds there, and a `WoneC`/`E1locC` value only under `hDh` (lines 349–353, 406–412). `Inhabited/E0CoeffFamily.lean:e0CoeffFamily_value_fromTower` has the same pattern for the energy sum; `Inhabited/ObsFamilyJoint.lean:obsFamily_full_fromTower` gives coefficient analyticity on `physVq` and its `M0C` value under `hDh` (lines 811–815). The raw observable `Ev` itself is analytic/bounded on `XiCRaw` for arbitrary data (lines 72–82). Thus the brief's “only VALUE clauses” is right for the final coefficient-versus-step identification; earlier activity/value bridges `WoneC`, `WtwoC`, `ObsMarks.toConsumer` are also fibre-restricted and must be lifted before those final clauses. Existing coefficient bounds need chart inclusion checks, not rederivation from scratch.

**OPEN (first family lift).** Prove `WoneC`/`WtwoC` physical activity equals the already constructed raw activity at every `D∈XiCData`, using `JointRep.gJ/PJ` and the H bridge. Then restate the final `E1locCH` and `M0CH` value clauses without `hDh`; keep the same `c`, `e0`, `Ev`, and `obsCoeffParam`. The energy branch also needs its determinant `halfLogDetC` comparison and logarithm choice on a common open domain. The zero-class identity remains an equality of exponentials until that choice is made.

## T4. Size and order

**OPEN (estimate, basis).** Carrier/old-datum leaf: 150–230 lines, using `composeData` and two raw-component comparisons. Joint-representative H comparison and analyticity leaf: 90–160 lines because `analyticAt_TstepJ` is landed; `TstepJ_withDatum` and the `W1/W2/PJ` comparisons show the proof pattern. Proposition 2.6 H leaf: 220–300 lines *after* H definitions and field-equality replacements, possibly two leaves because `prop26C_step` is roughly 120 lines plus the domain/expansion bridges. Activity and final family-value lifts: at least two 180–300-line leaves, one energy and one observable, with new off-fibre value proofs; their analytic/bound coefficient construction is reused. Total is more than the three initial leaves, but materially less than rebuilding all expansions. No source-level line estimate certifies that physical nonvanishing or class chart inclusion can be closed without additional hypotheses.

**OPEN (dependency order).** Start `StepSettingH/dataUCH` now. The H-to-`JointRep` comparisons and analytic representative can follow immediately; the off-fibre quadratic expansion/domain input then supports `prop26C_classH`; physical activity-to-family value lifts follow. The general-class lane can meanwhile work on `StepClass` old-term path-analyticity and raw E/M mark interfaces, but its nonzero old-term value identity and next-step `IsSFFamily2` membership depend on this H bridge plus their separate class-domain, numerical, symmetry, and density inputs (`GENCLASS.md` §T3). No zero-class off-fibre theorem by itself closes that lane.
