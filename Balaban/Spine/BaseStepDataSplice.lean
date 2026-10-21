/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Operators.QuietLocalInput
public import Balaban.LargeField.Operators.QuietStepData
public import Balaban.LargeField.Def7Inhabited

/-!
# The step data of the first step as a splice (A3-1 (b), (d))

The step data `StepData` of the first-step record are indexed by every scale `k < K`. At the first
step only the scale `0` is a real step (the base kernels `K₀`, LFR Definition II.7.6, (II.7.4)); the
scale `0 → 1` is never quiet (LFR Lemma II.7.2 (c), `not_isQuiet_zero`), and the scales `k ≥ 1`
are the quiet steps of the landed `quietStepData'`.

* `StepSlice0`: the fields of `StepData` at the scale `k = 0` (all of them except `quiet`);
  `StepSlice0.zero` is the zero slice (rule 10);
* `StepData.spliceZero`: from a scale-`0` slice and a step data `SD₁` for the scales `k ≥ 1`
  (with the Gaussian bound of `SD₁` at the exponents `κs`), the step data whose kernel at `0` is the
  slice's and at `k ≥ 1` is `SD₁`'s;
* `GaussStepSpec.mono`: the one-step bound is monotone in the exponent.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open MeasureTheory Balaban Balaban.Multiscale Balaban.Background RegionHistory ENNReal
  Balaban.LargeField.Def7

section Mono

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ}

/-- **The one-step bound is monotone in the exponent**: `κ' ≤ κ` weakens `≤ e^{-κ}` to
`≤ e^{-κ'}`. -/
theorem GaussStepSpec.mono {cs : OpConsts} {a : LocalHistory S n M K} {k : ℕ} {κ κ' : ℝ}
    {T : LFKernel (OutT N R a (k + 1)) (NewCfg N a k) (EuclideanSpace ℝ (Fin N))
      (GIdx S n M K N)}
    {wit : GaussWit N R a k} (h : GaussStepSpec cs R a k κ T wit) (hκ : κ' ≤ κ) :
    GaussStepSpec cs R a k κ' T wit := by
  obtain ⟨h1, h2, h3, h4, h5, Sw, hS1, hS2, hS3⟩ := h
  refine ⟨h1, h2, h3, h4, h5, Sw, hS1, hS2, fun par hv g hg => (hS3 par hv g hg).trans ?_⟩
  exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (neg_le_neg hκ))

end Mono

section Slice

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ}

variable (k0) in
/-- **The scale-`0` slice of the step data** (LFR Definition II.5.7 (S0)-(S2) at `k = 0`; for the
first step, the base kernel `K₀` and boundary factor `b₀` of LFR Definition II.7.6): the fields of
`StepData` specialized to `k = 0`, except `quiet` (the step `0 → 1` is never quiet,
`not_isQuiet_zero`). `κ0` is the step exponent at the scale `0`. -/
structure StepSlice0 (geo : Geo S n R M) (cs : OpConsts) (N : ℕ)
    (κ0 : LocalHistory S n M K → ℝ) where
  ker : ∀ (a : LocalHistory S n M K),
    LFKernel (OutT N R a (0 + 1)) (NewCfg N a 0) (EuclideanSpace ℝ (Fin N)) (GIdx S n M K N)
  wit : ∀ (a : LocalHistory S n M K), GaussWit N R a 0
  b_supp : ∀ a o x hv (g g' : GIdx S n M K N → ℂ),
    (∀ i : GIdx S n M K N, i.1 ∈ Vsites R a (0 + 1) → g i = g' i) →
      (ker a).b o x hv g = (ker a).b o x hv g'
  rot_K : ∀ a (ρ : OrthN N) o x hv,
    (ker a).K (rotOut ρ o) (rotSub ρ x) (ρ hv) = (ker a).K o x hv
  rot_b : ∀ a (ρ : OrthN N) o x hv g,
    (ker a).b (rotOut ρ o) (rotSub ρ x) (ρ hv) (rotG ρ g) = (ker a).b o x hv g
  euclid_K : ∀ (σ : LatTorusSym S n M K) (a a' : LocalHistory S n M K)
    (hI : HistImage σ.toTorusSym a a') (hk : 0 + 1 ≤ K) o o' x x' hv,
    RelOut σ.toTorusSym o o' → RelSub hI hk x x' → (ker a').K o' x' hv = (ker a).K o x hv
  euclid_b : ∀ (σ : LatTorusSym S n M K) (a a' : LocalHistory S n M K)
    (hI : HistImage σ.toTorusSym a a') (hk : 0 + 1 ≤ K) o o' x x' hv g g',
    RelOut σ.toTorusSym o o' → RelSub hI hk x x' → RelG σ.toTorusSym g g' →
      (ker a').b o' x' hv g' = (ker a).b o x hv g
  vacE : ∀ (_a : LocalHistory S n M K), ℝ
  vacEpp : ∀ (_a : LocalHistory S n M K), ℝ
  vacEppp : ∀ (_a : LocalHistory S n M K), ℝ
  b0 : ∀ (a : LocalHistory S n M K), OutT N R a (0 + 1) → NewCfg N a 0 →
    EuclideanSpace ℝ (Fin N) → (GIdx S n M K N → ℂ) → ℂ
  b_vac : ∀ a o x hv g,
    (ker a).b o x hv g = b0 a o x hv g -
      (stepVacuumTerm a 0 (vacE a) (vacEpp a) (vacEppp a) : ℂ)
  b0_bound : ∀ (H : RegionHistory S n R k0 K), H.Admissible →
    ∀ (Z' : H.Comp (0 + 1)) o x hv (g : GIdx S n M K N → ℂ), g ∈ l1Ball (GIdx S n M K N) →
    ChiNewAt geo cs H 0 Z' o x →
    ‖b0 (H.localHistory M K (0 + 1) Z') o x hv g‖ ≤
      (cs.Cb * Real.log (cs.beta 0) + cs.Cb * cs.B0) *
        volScale S (0 + 1) {z | z ∈ (H.localHistory M K (0 + 1) Z').Z (0 + 1) ∧
          z ∉ (H.localHistory M K (0 + 1) Z').Z 0}
  b_bound : ∀ (H : RegionHistory S n R k0 K), H.Admissible →
    ∀ (Z' : H.Comp (0 + 1)) o x hv (g : GIdx S n M K N → ℂ), g ∈ l1Ball (GIdx S n M K N) →
    ChiNewAt geo cs H 0 Z' o x →
    ‖(ker (H.localHistory M K (0 + 1) Z')).b o x hv g‖ ≤
      (cs.Cb * Real.log (cs.beta 0) + cs.Cb * cs.B0) *
        volScale S (0 + 1) {z | z ∈ (H.localHistory M K (0 + 1) Z').Z (0 + 1) ∧
          z ∉ (H.localHistory M K (0 + 1) Z').Z 0}
  dom : ∀ (H : RegionHistory S n R k0 K), H.Admissible →
    ∀ (Z' : H.Comp (0 + 1)) o x hv, ¬ ChiNewAt geo cs H 0 Z' o x →
    (ker (H.localHistory M K (0 + 1) Z')).K o x hv = 0
  gauss : ∀ (H : RegionHistory S n R k0 K), H.Admissible → ∀ (Z' : H.Comp (0 + 1)),
    GaussStepSpec cs R (H.localHistory M K (0 + 1) Z') 0 (κ0 (H.localHistory M K (0 + 1) Z'))
      (ker (H.localHistory M K (0 + 1) Z')) (wit (H.localHistory M K (0 + 1) Z'))

/-- **The zero slice** (rule 10; the scale-`0` fields of `zeroStepData`, which holds for every
horizon at the scale `0`): zero kernels and boundary factors, `C_b = 0`. -/
noncomputable def StepSlice0.zero (geo : Geo S n R M) (cs : OpConsts) (hCb : cs.Cb = 0)
    (κ0 : LocalHistory S n M K → ℝ) : StepSlice0 k0 geo cs N κ0 where
  ker := fun _ => zeroKer _ _ _ _
  wit := fun a => emptyWit a 0
  b_supp := fun _ _ _ _ _ _ _ => rfl
  rot_K := fun _ _ _ _ _ => rfl
  rot_b := fun _ _ _ _ _ _ => rfl
  euclid_K := fun _ _ _ _ _ _ _ _ _ _ _ _ => rfl
  euclid_b := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl
  vacE := fun _ => 0
  vacEpp := fun _ => 0
  vacEppp := fun _ => 0
  b0 := fun _ _ _ _ _ => 0
  b_vac := fun _ _ _ _ _ => by simp [zeroKer, stepVacuumTerm]
  b0_bound := fun _ _ _ _ _ _ _ _ _ => by simp [hCb]
  b_bound := fun _ _ _ _ _ _ _ _ _ => by simp [zeroKer, hCb]
  dom := fun _ _ _ _ _ _ _ => rfl
  gauss := fun _ _ _ => by
    refine ⟨fun w => w.elim, fun w => w.elim, fun w => w.elim, fun w => w.elim,
      fun _ _ _ => by rw [sum_emptyWit, mul_zero]; rfl, fun w => w.elim,
      fun w => w.elim, fun w => w.elim, fun _ _ _ _ => by rw [sum_emptyWit]; exact zero_le⟩

end Slice


section Splice

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {geo : Geo S n R M} {cs : OpConsts}
  {κ1 κs : ℕ → LocalHistory S n M K → ℝ}

/-- **The splice of a scale-`0` slice with step data for the scales `k ≥ 1`**: the kernel at `0` is
the slice's, at `k ≥ 1` that of `SD₁`. The field `quiet` at `k = 0` is `not_isQuiet_zero` (LFR
Lemma II.7.2 (c)); the Gaussian bound at the scales `k ≥ 1` is asked at the exponents `κs`
(`hg`; from the exponents of `SD₁` by `GaussStepSpec.mono`). -/
noncomputable def StepData.spliceZero (sl : StepSlice0 k0 geo cs N (κs 0))
    (SD₁ : StepData k0 geo cs N κ1)
    (hg : ∀ (H : RegionHistory S n R k0 K), H.Admissible → ∀ (k : ℕ) (Z' : H.Comp (k + 1 + 1)),
      GaussStepSpec cs R (H.localHistory M K (k + 1 + 1) Z') (k + 1)
        (κs (k + 1) (H.localHistory M K (k + 1 + 1) Z'))
        (SD₁.ker (k + 1) (H.localHistory M K (k + 1 + 1) Z'))
        (SD₁.wit (k + 1) (H.localHistory M K (k + 1 + 1) Z'))) :
    StepData k0 geo cs N κs where
  ker := fun k a => match k with
    | 0 => sl.ker a
    | k + 1 => SD₁.ker (k + 1) a
  wit := fun k a => match k with
    | 0 => sl.wit a
    | k + 1 => SD₁.wit (k + 1) a
  b_supp := fun k => by
    cases k with
    | zero => exact sl.b_supp
    | succ k => exact SD₁.b_supp (k + 1)
  rot_K := fun k => by
    cases k with
    | zero => exact sl.rot_K
    | succ k => exact SD₁.rot_K (k + 1)
  rot_b := fun k => by
    cases k with
    | zero => exact sl.rot_b
    | succ k => exact SD₁.rot_b (k + 1)
  euclid_K := fun k => by
    cases k with
    | zero => exact sl.euclid_K
    | succ k => exact SD₁.euclid_K (k + 1)
  euclid_b := fun k => by
    cases k with
    | zero => exact sl.euclid_b
    | succ k => exact SD₁.euclid_b (k + 1)
  vacE := fun k a => match k with
    | 0 => sl.vacE a
    | k + 1 => SD₁.vacE (k + 1) a
  vacEpp := fun k a => match k with
    | 0 => sl.vacEpp a
    | k + 1 => SD₁.vacEpp (k + 1) a
  vacEppp := fun k a => match k with
    | 0 => sl.vacEppp a
    | k + 1 => SD₁.vacEppp (k + 1) a
  b0 := fun k a => match k with
    | 0 => sl.b0 a
    | k + 1 => SD₁.b0 (k + 1) a
  b_vac := fun k => by
    cases k with
    | zero => exact sl.b_vac
    | succ k => exact SD₁.b_vac (k + 1)
  b0_bound := fun H hH k => by
    cases k with
    | zero => exact sl.b0_bound H hH
    | succ k => exact SD₁.b0_bound H hH (k + 1)
  b_bound := fun H hH k => by
    cases k with
    | zero => exact sl.b_bound H hH
    | succ k => exact SD₁.b_bound H hH (k + 1)
  quiet := fun H hH k => by
    cases k with
    | zero => exact fun hk Z' hq => absurd hq (not_isQuiet_zero H hk Z')
    | succ k => exact SD₁.quiet H hH (k + 1)
  dom := fun H hH k => by
    cases k with
    | zero => exact sl.dom H hH
    | succ k => exact SD₁.dom H hH (k + 1)
  gauss := fun H hH k => by
    cases k with
    | zero => exact sl.gauss H hH
    | succ k => exact hg H hH k

/-- The kernel of the splice at `0` is the slice's. -/
theorem StepData.spliceZero_ker_zero (sl : StepSlice0 k0 geo cs N (κs 0))
    (SD₁ : StepData k0 geo cs N κ1) (hg) (a : LocalHistory S n M K) :
    (StepData.spliceZero sl SD₁ hg).ker 0 a = sl.ker a := rfl

/-- The kernel of the splice at `k + 1` is that of `SD₁`. -/
theorem StepData.spliceZero_ker_succ (sl : StepSlice0 k0 geo cs N (κs 0))
    (SD₁ : StepData k0 geo cs N κ1) (hg) (k : ℕ) (a : LocalHistory S n M K) :
    (StepData.spliceZero sl SD₁ hg).ker (k + 1) a = SD₁.ker (k + 1) a := rfl

end Splice


section QuietGauss

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {geo : Geo S n R M} {cs : OpConsts}

/-- **The Gaussian bound of the quiet step data at a smaller exponent**: at the localized histories
of quiet steps the exponent `κs` may be any number at most `quietKappaStep` (the one-step bound is
monotone, `GaussStepSpec.mono`); elsewhere the kernel is zero and every exponent is allowed. -/
theorem quietStepData'_gauss_le [NeZero N] (inp : QuietStepInput' K k0 geo cs N)
    (hz : ∀ k, 0 ≤ cs.z (k + 1)) (hc : ∀ k, 0 ≤ cs.beta k * cs.aKer * (S.L : ℝ) ^ (S.d - 2))
    (hβ : ∀ k, 0 ≤ cs.beta (k + 1)) (haw : ∀ n, 0 ≤ cs.aw n) (hμ : ∀ k, 0 ≤ cs.muAct (k + 1))
    (hbg : ∀ q, BgHyp S.d S.L q (minSep S.L geo.M1) cs.aw (cs.mu q))
    (hbgB : ∀ q, BgHyp S.d S.L q (minSep S.L geo.M1) cs.aw (cs.muBg q))
    (hN : 2 ≤ N) (c1 c2 : ℝ) (hc1 : cs.Cb ≤ c1) (hc2 : cs.Cb * cs.B0 ≤ c2)
    (hlog : ∀ k, 0 ≤ Real.log (cs.beta k))
    (hcpos : ∀ k, 0 < cs.beta k * cs.aKer * (S.L : ℝ) ^ (S.d - 2))
    (hδ : ∀ k, 0 < cs.delta k) (hδ1 : ∀ k, 3 * S.d * S.L * cs.delta k ≤ 1 / 2)
    (hΛ : ∀ k, 3 * S.d * S.L * cShell N * cs.delta k ≤ 1 / 2)
    (hCb : 0 ≤ cs.Cb) (hB0 : 0 ≤ cs.B0)
    {κs : ℕ → LocalHistory S n M K → ℝ}
    (hκ : ∀ k a, QuietRealized R k0 k a → κs k a ≤ quietKappaStep cs c1 c2 k a)
    (H : RegionHistory S n R k0 K) (hH : H.Admissible) (k : ℕ) (Z' : H.Comp (k + 1 + 1)) :
    GaussStepSpec cs R (H.localHistory M K (k + 1 + 1) Z') (k + 1)
      (κs (k + 1) (H.localHistory M K (k + 1 + 1) Z'))
      ((quietStepData' inp hz hc hβ haw hμ hbg hbgB hN c1 c2 hc1 hc2 hlog hcpos hδ hδ1 hΛ hCb
        hB0).ker (k + 1) (H.localHistory M K (k + 1 + 1) Z'))
      ((quietStepData' inp hz hc hβ haw hμ hbg hbgB hN c1 c2 hc1 hc2 hlog hcpos hδ hδ1 hΛ hCb
        hB0).wit (k + 1) (H.localHistory M K (k + 1 + 1) Z')) := by
  classical
  by_cases hr : QuietRealized R k0 (k + 1) (H.localHistory M K (k + 1 + 1) Z')
  · exact (quietStepData' inp hz hc hβ haw hμ hbg hbgB hN c1 c2 hc1 hc2 hlog hcpos hδ hδ1 hΛ hCb
      hB0).gauss H hH (k + 1) Z' |>.mono (hκ _ _ hr)
  · have hw : (quietStepData' inp hz hc hβ haw hμ hbg hbgB hN c1 c2 hc1 hc2 hlog hcpos hδ hδ1 hΛ
        hCb hB0).wit (k + 1) (H.localHistory M K (k + 1 + 1) Z') =
        zeroWit N R (H.localHistory M K (k + 1 + 1) Z') (k + 1) := by
      show quietWit inp.toInput hz hc hβ haw hμ hbg hbgB hN c1 c2 hc1 hc2 hlog hcpos hδ hδ1 hΛ (k + 1) _ = _
      unfold quietWit
      simp only [hr, ↓reduceDIte]
    rw [hw]
    refine gaussSpec_zero cs _ (k + 1) _ _ fun o x hv => ?_
    show (quietKer inp.toInput hz hc hβ haw hμ hbg hbgB (k + 1) _).K o x hv = 0
    rw [quietKer_K]
    simp only [hr, ↓reduceIte]

end QuietGauss

end Balaban.LargeField
