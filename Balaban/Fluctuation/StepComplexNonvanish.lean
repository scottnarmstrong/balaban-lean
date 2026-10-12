/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.StepComplexAgree
public import Balaban.Fluctuation.StepNonvanishInhab
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Nonvanishing of the partition functions of the complex step (COMPLETE-STEP §2; ACTIVITY §4)

`StepActivityBoundC` is `StepActivityBound` for the exponents `WoneC`, `WtwoC` of the step at a
complex block datum (`StepComplex`): the same fields, with the almost-everywhere identity (2.1) for
`W₁(s,ψ̂) + W₂(t,ψ̂; g)` of the complex step.

* `StepActivityBoundC.ZstC_eq_exp`, `ZstC_ne_zero`: `Z_{s,t} = exp 𝓛_{s,t}` with
  `‖𝓛_{s,t}‖ ≤ |𝔅| ε_H K_c C_PE` on the two segments;
* `StepNonvanishingC`, `stepNonvanishingC_of_activityBoundC`;
* `StepActivityBound.toC`, `StepActivityBoundC.toReal`, `stepActivityBoundEquiv`: the two
  structures are equivalent as soon as the exponents agree almost everywhere on the segments;
  `stepActivityBoundEquivReal`, `stepNonvanishingC_iff`, `stepNonvanishing_of_activityBoundC`,
  `prop26_complex_class_of_activityC`: on real data (the hypotheses of the landed step) they are
  equivalent, and `StepActivityBoundC` is an input of Proposition 2.6;
* `nonempty_stepActivityBoundC` (rule 10): the degenerate witness of `StepActivityBound`,
  transported.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Polymer Balaban.Multiscale Balaban.SmallField.Def6
  Balaban.Background Balaban.SmallField MeasureTheory

section Bound

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- **The physical complex activity bound of the step at a complex block datum**
(COMPLETE-STEP §2, (2.1)-(2.2); P5 Theorem 3.4 (a), (e) and Proposition 3.3).  The fields are those
of `StepActivityBound`; the identity (2.1) is for the exponents of the complex step:

* (2.1): for each `(s,t)` on the two segments (`stepSegments`) the exponent
  `W₁(s,ψ̂) + W₂(t,ψ̂; g)` (`WoneC`, `WtwoC`: the substitution (2.7) with the complex square root
  `C^{(k)1/2}(θ)` and the critical point `ψ^{(k)}(θ)` of the complex small solution) is
  `ν_{p₁}`-almost everywhere the sum `∑_y H(y; s, t; ψ̂|_b)` of the block-local activities
  `A (s,t)`;
* (2.2): the numerical conditions on `ε_H, κ_H, κ₀, κ', K_c` of `StepActivityBound`. -/
structure StepActivityBoundC (S : StepSetting d L N₁ m₁ k N ϱ) (C : StepClass d L N₁ m₁ k N ϱ)
    (g : Fld d L N₁ m₁ (k + 1) N) where
  /-- the scale of the block cubes -/
  m₀ : ℕ
  hN : L ^ m₀ ∣ N₁
  /-- the identification of `ν_{p₁}` with the product of the block measures -/
  BS : BlockSplit S m₀
  Lb : Type
  [fin : Fintype Lb]
  Lab : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1) Set.univ Lb
  εH : ℝ
  κH : ℝ
  κ0 : ℝ
  κ' : ℝ
  Kc : ℝ
  /-- the complex activities at `(s,t)` -/
  A : ℝ × ℝ → LabelAct Lab BS.Ωb εH κH κ0 Kc
  hκ0 : aEnt d L + 1 ≤ κ0
  hKc : K0 d L κ0 + 1 ≤ Kc
  hεpos : 0 < εH
  hκ' : 0 ≤ κ'
  hκ : κ' + 3 * κ0 + c1 d L + 3 / 2 ≤ κH
  hε : εH ≤ 1 / (8 * Kc ^ 3 * c1 d L *
    Real.exp ((κH - 2 * κ0) * cG d L + c1 d L + κ' * cG d L))
  hW : ∀ p ∈ stepSegments, ∀ᵐ x ∂S.nuFl,
    S.WoneC C p.1 x + S.WtwoC C g p.2 x = ∑ y, (A p).H y (BS.restr x)

attribute [instance] StepActivityBoundC.fin

/-- The two segments of the interpolation lie in the square `[0,1]²`. -/
theorem mem_Icc_of_mem_stepSegments {p : ℝ × ℝ} (hp : p ∈ stepSegments) :
    p.1 ∈ Set.Icc (0 : ℝ) 1 ∧ p.2 ∈ Set.Icc (0 : ℝ) 1 := by
  rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨h1, by rw [h2]; exact Set.left_mem_Icc.2 zero_le_one⟩
  · exact ⟨by rw [h1]; exact Set.right_mem_Icc.2 zero_le_one, h2⟩

variable {S : StepSetting d L N₁ m₁ k N ϱ} {C : StepClass d L N₁ m₁ k N ϱ}
  {g : Fld d L N₁ m₁ (k + 1) N}

/-- **`Z_{s,t}` of the complex step is the product-measure integral of the exponentiated block
activities** (the complex form of `Zst_eq_integral_pi`). -/
theorem StepSetting.ZstC_eq_integral_pi (S : StepSetting d L N₁ m₁ k N ϱ)
    (C : StepClass d L N₁ m₁ k N ϱ) (g : Fld d L N₁ m₁ (k + 1) N) {m₀ : ℕ} (BS : BlockSplit S m₀)
    {Lb : Type*} [Fintype Lb] (H : Lb → (∀ b, BS.Ωb b) → ℂ)
    (hHm : ∀ y, Measurable (H y)) (s t : ℝ)
    (hW : ∀ᵐ x ∂S.nuFl, S.WoneC C s x + S.WtwoC C g t x = ∑ y, H y (BS.restr x)) :
    S.ZstC C g s t = ∫ Φ, Complex.exp (∑ y, H y Φ) ∂(Measure.pi BS.μ) := by
  have hmeas : Measurable (fun Φ : ∀ b, BS.Ωb b => Complex.exp (∑ y, H y Φ)) :=
    Complex.measurable_exp.comp (Finset.measurable_sum _ fun y _ => hHm y)
  rw [← BS.map_eq, integral_map BS.meas.aemeasurable hmeas.aestronglyMeasurable]
  unfold StepSetting.ZstC partFun₂
  refine integral_congr_ae ?_
  filter_upwards [hW] with x hx
  rw [hx]

/-- **`Z_{s,t} = exp 𝓛_{s,t}` with `‖𝓛_{s,t}‖ ≤ |𝔅| ε_H K_c C_PE`** on the two segments
(COMPLETE-STEP (2.3)), for the step at a complex block datum. -/
theorem StepActivityBoundC.ZstC_eq_exp (I : StepActivityBoundC S C g) {s t : ℝ}
    (hst : (s, t) ∈ stepSegments) :
    ∃ Lg : ℂ, S.ZstC C g s t = Complex.exp Lg ∧
      ‖Lg‖ ≤ Fintype.card (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) I.m₀
        (k + 1) Set.univ) * (I.εH * I.Kc * CPE d L I.Kc I.κH I.κ0 I.κ') := by
  obtain ⟨Lg, h1, h2⟩ := labelAct_integral_eq_exp I.BS.μ I.hN (I.A (s, t)) I.hκ0 I.hKc I.hεpos
    I.hκ' I.hκ I.hε
  exact ⟨Lg, (StepSetting.ZstC_eq_integral_pi S C g I.BS (I.A (s, t)).H (I.A (s, t)).meas s t
    (I.hW (s, t) hst)).trans h1, h2⟩

/-- **`Z_{s,t} ≠ 0`** on the two segments, for the step at a complex block datum. -/
theorem StepActivityBoundC.ZstC_ne_zero (I : StepActivityBoundC S C g) {s t : ℝ}
    (hst : (s, t) ∈ stepSegments) : S.ZstC C g s t ≠ 0 := by
  obtain ⟨Lg, h, -⟩ := I.ZstC_eq_exp hst
  rw [h]; exact Complex.exp_ne_zero _

/-- **Nonvanishing of the partition functions of the complex step** (the cluster expansion,
Theorem 3.4 (a), (e)) along the two segments of the interpolation: `Z_{s,0} ≠ 0` and
`Z_{1,t} ≠ 0`, `s, t ∈ [0,1]`; `StepNonvanishing` for `ZstC`. -/
structure StepSetting.StepNonvanishingC (S : StepSetting d L N₁ m₁ k N ϱ)
    (C : StepClass d L N₁ m₁ k N ϱ) (g : Fld d L N₁ m₁ (k + 1) N) : Prop where
  seg1 : ∀ s ∈ Set.Icc (0 : ℝ) 1, S.ZstC C g s 0 ≠ 0
  seg2 : ∀ t ∈ Set.Icc (0 : ℝ) 1, S.ZstC C g 1 t ≠ 0

/-- **`StepNonvanishingC` from the activity bound of the complex step.** -/
theorem stepNonvanishingC_of_activityBoundC (I : StepActivityBoundC S C g) :
    S.StepNonvanishingC C g :=
  ⟨fun _ hs => I.ZstC_ne_zero (Or.inl ⟨hs, rfl⟩),
    fun _ ht => I.ZstC_ne_zero (Or.inr ⟨rfl, ht⟩)⟩

/-! ### Transport between the two activity bounds -/

/-- The activity bound of the complex step from the landed one, when the two exponents agree
almost everywhere on the segments. -/
def StepActivityBound.toC (I : StepActivityBound S C g)
    (h : ∀ p ∈ stepSegments, ∀ᵐ x ∂S.nuFl,
      S.WoneC C p.1 x + S.WtwoC C g p.2 x = S.Wone C p.1 x + S.Wtwo C g p.2 x) :
    StepActivityBoundC S C g where
  m₀ := I.m₀
  hN := I.hN
  BS := I.BS
  Lb := I.Lb
  Lab := I.Lab
  εH := I.εH
  κH := I.κH
  κ0 := I.κ0
  κ' := I.κ'
  Kc := I.Kc
  A := I.A
  hκ0 := I.hκ0
  hKc := I.hKc
  hεpos := I.hεpos
  hκ' := I.hκ'
  hκ := I.hκ
  hε := I.hε
  hW := fun p hp => by
    filter_upwards [h p hp, I.hW p hp] with x h1 h2
    rw [h1, h2]

/-- The landed activity bound from the one of the complex step, when the two exponents agree
almost everywhere on the segments. -/
def StepActivityBoundC.toReal (I : StepActivityBoundC S C g)
    (h : ∀ p ∈ stepSegments, ∀ᵐ x ∂S.nuFl,
      S.WoneC C p.1 x + S.WtwoC C g p.2 x = S.Wone C p.1 x + S.Wtwo C g p.2 x) :
    StepActivityBound S C g where
  m₀ := I.m₀
  hN := I.hN
  BS := I.BS
  Lb := I.Lb
  Lab := I.Lab
  εH := I.εH
  κH := I.κH
  κ0 := I.κ0
  κ' := I.κ'
  Kc := I.Kc
  A := I.A
  hκ0 := I.hκ0
  hKc := I.hKc
  hεpos := I.hεpos
  hκ' := I.hκ'
  hκ := I.hκ
  hε := I.hε
  hW := fun p hp => by
    filter_upwards [h p hp, I.hW p hp] with x h1 h2
    rw [← h1, h2]

/-- **The two activity bounds are equivalent** when the exponents of the complex step and of the
landed step agree almost everywhere on the segments. -/
def stepActivityBoundEquiv
    (h : ∀ p ∈ stepSegments, ∀ᵐ x ∂S.nuFl,
      S.WoneC C p.1 x + S.WtwoC C g p.2 x = S.Wone C p.1 x + S.Wtwo C g p.2 x) :
    StepActivityBoundC S C g ≃ StepActivityBound S C g where
  toFun I := I.toReal h
  invFun I := I.toC h
  left_inv I := by cases I; rfl
  right_inv I := by cases I; rfl

section Real

variable (S) (C) (ha₁ : 0 < S.a₁) (H : BgHyp d L (k + 1) ϱ S.a S.ν)
  {δ' : ℝ} (hδ'0 : 0 < δ') (hδ' : δ' ≤ thm73C3 d L N / 2) (hD'R : InDomainR S.G' S.ν δ' S.D')
  (hδ0 : 0 < S.δ)
  (hfam : ∀ x, 0 ≤ x → XData S.G' S.a S.a₁ S.ν x (bgMult S.G' S.a S.ν S.D') 0 (fun _ => 1))
  (hsm : S.δ ^ 2 * smallConstX d L 0 ≤ 1 / 4)
  (hχu : chiU S.G' S.a S.ν S.δ S.D' = 1)
  (hnorm : S.ν * ((L : ℝ) ^ k) ^ 2 * |∑ i, S.h₀ i ^ 2 - 1| < (1 * S.δ) ^ 2)
  (hβ : 0 < S.β) (hp₁ : 0 < S.p₁)
  {B₅ K₂ : ℝ} (hB5 : max 1 (Real.sqrt N * covSupConst d L N (S.a k)) ≤ B₅)
  (hK2 : max (max 1 (cK2 d L N)) (Real.sqrt N * cK2 d L N) ≤ K₂)
  (hp40 : S.p₁ / (S.betaU ^ (1 / 2 : ℝ) * S.δ) ≤ (3 * B₅ * K₂)⁻¹)
  (hrad : B₅ * S.betaU ^ (-(1 / 2 : ℝ)) * S.p₁ ≤ fluctRadius d L N)

include S C ha₁ H hδ'0 hδ' hD'R hδ0 hfam hsm hχu hnorm hβ hp₁ hB5 hK2 hp40 hrad in
/-- **Real data: on the two segments the exponents of the complex step are the landed ones
almost everywhere.** -/
theorem StepSetting.ae_exponentsC_eq (g : Fld d L N₁ m₁ (k + 1) N) :
    ∀ p ∈ stepSegments, ∀ᵐ x ∂S.nuFl,
      S.WoneC C p.1 x + S.WtwoC C g p.2 x = S.Wone C p.1 x + S.Wtwo C g p.2 x := fun _ hp =>
  S.ae_WoneC_add_WtwoC_eq C ha₁ H hδ'0 hδ' hD'R hδ0 hfam hsm hχu hnorm hβ hp₁ hB5 hK2 hp40 hrad g
    (mem_Icc_of_mem_stepSegments hp).1 (mem_Icc_of_mem_stepSegments hp).2

include S C ha₁ H hδ'0 hδ' hD'R hδ0 hfam hsm hχu hnorm hβ hp₁ hB5 hK2 hp40 hrad in
/-- **Real data: the activity bound of the complex step is the landed `StepActivityBound`**
(an equivalence which keeps the labels, the block split, the activities and the constants). -/
noncomputable def stepActivityBoundEquivReal (g : Fld d L N₁ m₁ (k + 1) N) :
    StepActivityBoundC S C g ≃ StepActivityBound S C g :=
  stepActivityBoundEquiv
    (S.ae_exponentsC_eq C ha₁ H hδ'0 hδ' hD'R hδ0 hfam hsm hχu hnorm hβ hp₁ hB5 hK2 hp40 hrad g)

include S C ha₁ H hδ'0 hδ' hD'R hδ0 hfam hsm hχu hnorm hβ hp₁ hB5 hK2 hp40 hrad in
/-- **Real data: `StepNonvanishingC` is the landed `StepNonvanishing`.** -/
theorem stepNonvanishingC_iff (g : Fld d L N₁ m₁ (k + 1) N) :
    S.StepNonvanishingC C g ↔ S.StepNonvanishing C g := by
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := Set.left_mem_Icc.2 zero_le_one
  have h1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := Set.right_mem_Icc.2 zero_le_one
  have hZ : ∀ {s t : ℝ}, s ∈ Set.Icc (0 : ℝ) 1 → t ∈ Set.Icc (0 : ℝ) 1 →
      S.ZstC C g s t = S.Zst C g s t := fun hs ht =>
    S.ZstC_eq C ha₁ H hδ'0 hδ' hD'R hδ0 hfam hsm hχu hnorm hβ hp₁ hB5 hK2 hp40 hrad g hs ht
  constructor
  · intro h
    exact ⟨fun s hs => by rw [← hZ hs h0]; exact h.seg1 s hs,
      fun t ht => by rw [← hZ h1 ht]; exact h.seg2 t ht⟩
  · intro h
    exact ⟨fun s hs => by rw [hZ hs h0]; exact h.seg1 s hs,
      fun t ht => by rw [hZ h1 ht]; exact h.seg2 t ht⟩

include S C ha₁ H hδ'0 hδ' hD'R hδ0 hfam hsm hχu hnorm hβ hp₁ hB5 hK2 hp40 hrad in
/-- **Real data: the landed `StepNonvanishing` from the activity bound of the complex step.** -/
theorem stepNonvanishing_of_activityBoundC (g : Fld d L N₁ m₁ (k + 1) N)
    (I : StepActivityBoundC S C g) : S.StepNonvanishing C g :=
  (stepNonvanishingC_iff S C ha₁ H hδ'0 hδ' hD'R hδ0 hfam hsm hχu hnorm hβ hp₁ hB5 hK2 hp40 hrad
    g).1 (stepNonvanishingC_of_activityBoundC I)

end Real

section Public

variable (S) (C) (ha₁ : 0 < S.a₁) (H : BgHyp d L (k + 1) ϱ S.a S.ν)
  {δ' : ℝ} (hδ'0 : 0 < δ') (hδ' : δ' ≤ thm73C3 d L N / 2) (hD'R : InDomainR S.G' S.ν δ' S.D')
  (hδ0 : 0 < S.δ)
  (hfam : ∀ x, 0 ≤ x → XData S.G' S.a S.a₁ S.ν x (bgMult S.G' S.a S.ν S.D') 0 (fun _ => 1))
  (hsm : S.δ ^ 2 * smallConstX d L 0 ≤ 1 / 4)
  (hχu : chiU S.G' S.a S.ν S.δ S.D' = 1)
  (hnorm : S.ν * ((L : ℝ) ^ k) ^ 2 * |∑ i, S.h₀ i ^ 2 - 1| < (1 * S.δ) ^ 2)
  (hβ : 0 < S.β) (hp₁ : 0 < S.p₁) {pp : ℝ} (hlt : S.p₁ < pp)
  {B₅ K₂ : ℝ} (hB5 : max 1 (Real.sqrt N * covSupConst d L N (S.a k)) ≤ B₅)
  (hK2 : max (max 1 (cK2 d L N)) (Real.sqrt N * cK2 d L N) ≤ K₂)
  (hp40 : pp / (S.betaU ^ (1 / 2 : ℝ) * S.δ) ≤ (3 * B₅ * K₂)⁻¹)
  (hrad : B₅ * S.betaU ^ (-(1 / 2 : ℝ)) * pp ≤ fluctRadius d L N)

include S C ha₁ H hδ'0 hδ' hD'R hδ0 hfam hsm hχu hnorm hβ hp₁ hlt hB5 hK2 hp40 hrad in
/-- **Proposition 2.6 (whole lattice, `λ = ∞`, complete convention, real block datum, complex
class data and source)** with the activity bound of the complex step as the input: on real data
`StepActivityBoundC` replaces `StepActivityBound` in `prop26_complex_class_of_activity`. -/
theorem prop26_complex_class_of_activityC (g : Fld d L N₁ m₁ (k + 1) N)
    (hc : S.ClassRegular C g) (hact : StepActivityBoundC S C g) :
    S.Tstep C g = Complex.exp (-(S.β : ℂ) * (S.Anew : ℂ) +
      EcompAt C.m₀ C.Tm S.a S.ν (Nat.le_succ k) S.psiKd - (S.Eppp C : ℂ) * (S.nU : ℂ) +
      FcompAt C.m₀ C.Tm S.a S.ν (Nat.le_succ k) S.psiKd g + S.E0 C + S.F0 C g) := by
  obtain ⟨h40, hr⟩ := S.margin_small hδ0 hβ hlt hB5 hp40 hrad
  exact S.prop26_complex_class C ha₁ H hδ'0 hδ' hD'R hδ0 hfam hsm hχu hnorm hβ hp₁ hlt hB5 hK2 hp40
    hrad g hc (stepNonvanishing_of_activityBoundC S C ha₁ H hδ'0 hδ' hD'R hδ0 hfam hsm hχu hnorm hβ
      hp₁ hB5 hK2 h40 hr g hact)

end Public

end Bound

section Inhab

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

theorem EcompAtC_zero (m₀ : ℕ) (a : ℕ → ℝ) (ν : ℝ) {K j : ℕ} (hj : j ≤ K)
    (D : BgData (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j hj) N) :
    EcompAtC m₀ (zeroTerms d L N₁ m₁ K N ϱ) a ν hj D = 0 := by
  simp [EcompAtC, Edens_zero]

theorem FcompAtC_zero_eq (m₀ : ℕ) (a : ℕ → ℝ) (ν : ℝ) {K j : ℕ} (hj : j ≤ K)
    (D : BgData (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j hj) N)
    (g : Fld d L N₁ m₁ K N) :
    FcompAtC m₀ (zeroTerms d L N₁ m₁ K N ϱ) a ν hj D g =
      ∑ x : CTorus d L N₁ m₁ K, ∑ i, g x i *
        svec (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j hj)
          (bgFieldC (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j hj) a ν
            (bgC0 d L N) D) x i := by
  simp [FcompAtC, Floc_zero]

/-- For the zero effective action and `β = 0` the exponent `W₁` of the complex step vanishes. -/
theorem WoneC_zero_of_beta (S : StepSetting d L N₁ m₁ k N ϱ) (hβ : S.β = 0) (s : ℝ) (x : S.E) :
    S.WoneC (zeroClass d L N₁ m₁ k N ϱ) s x = 0 := by
  unfold StepSetting.WoneC StepSetting.dEC
  show -(S.β : ℂ) * _ + (EcompAtC 0 (zeroTerms d L N₁ m₁ (k + 1) N ϱ) S.a S.ν (Nat.le_succ k) _ -
    EcompAtC 0 (zeroTerms d L N₁ m₁ (k + 1) N ϱ) S.a S.ν (Nat.le_succ k) _) = 0
  rw [hβ, EcompAtC_zero, EcompAtC_zero]; simp

/-- For the zero effective action and the source `g = 0` the exponent `W₂` of the complex step
vanishes. -/
theorem WtwoC_zero_class (S : StepSetting d L N₁ m₁ k N ϱ) (t : ℝ) (x : S.E) :
    S.WtwoC (zeroClass d L N₁ m₁ k N ϱ) 0 t x = 0 := by
  unfold StepSetting.WtwoC StepSetting.dFC
  show FcompAtC 0 (zeroTerms d L N₁ m₁ (k + 1) N ϱ) S.a S.ν (Nat.le_succ k) _ 0 -
    FcompAtC 0 (zeroTerms d L N₁ m₁ (k + 1) N ϱ) S.a S.ν (Nat.le_succ k) _ 0 = 0
  rw [FcompAtC_zero_eq, FcompAtC_zero_eq]
  simp

/-- **`StepActivityBoundC` is inhabited** (rule 10), at the zero-interaction datum of
`nonempty_stepActivityBound`: `N₁ = 1`, the step datum `θ = 0` of `nonempty_stepSetting` with
`β = 0`, `p₁ = 1`, the zero class and source `g = 0`.  DEGENERATE: all exponents and activities
vanish, for the complex step as for the landed one; the witness is the landed one, transported by
`StepActivityBound.toC`. -/
theorem nonempty_stepActivityBoundC (hk1 : 1 ≤ k) (a₁ ν δ : ℝ) :
    ∃ S : StepSetting d L 1 m₁ k N ϱ,
      Nonempty (StepActivityBoundC S (zeroClass d L 1 m₁ k N ϱ) 0) := by
  obtain ⟨S₀⟩ := nonempty_stepSetting (d := d) (L := L) (N₁ := 1) (m₁ := m₁) (k := k) (N := N)
    (ϱ := ϱ) hk1 a₁ ν 0 1 δ
  let S : StepSetting d L 1 m₁ k N ϱ := { S₀ with β := 0, p₁ := 1 }
  have hβ : S.β = 0 := rfl
  have h0 : ∀ p : ℝ × ℝ, (fun x => S.WoneT (zeroClass d L 1 m₁ k N ϱ) p.1 x +
      S.WtwoT (zeroClass d L 1 m₁ k N ϱ) 0 p.2 x) = fun _ => 0 := by
    intro p
    funext x
    simp [StepSetting.WoneT, StepSetting.WtwoT, Wone_zero_of_beta S hβ, Wtwo_zero_class]
  obtain ⟨I⟩ := stepActivityBound_of_small S (zeroClass d L 1 m₁ k N ϱ) 0 rfl one_pos
    (fun p _ => by rw [h0 p]; exact measurable_const)
    (fun p _ x => by
      have := congrFun (h0 p) x
      rw [this, norm_zero]
      exact stepActivityThreshold_nonneg _ _ _ _ _)
  refine ⟨S, ⟨I.toC fun p _ => Filter.Eventually.of_forall fun x => ?_⟩⟩
  rw [WoneC_zero_of_beta S hβ, WtwoC_zero_class, Wone_zero_of_beta S hβ, Wtwo_zero_class]

/-- **`StepNonvanishingC` is not contradictory**: it holds at the witness of
`nonempty_stepActivityBoundC`. -/
theorem nonempty_stepNonvanishingC (hk1 : 1 ≤ k) (a₁ ν δ : ℝ) :
    ∃ S : StepSetting d L 1 m₁ k N ϱ, S.StepNonvanishingC (zeroClass d L 1 m₁ k N ϱ) 0 := by
  obtain ⟨S, ⟨I⟩⟩ := nonempty_stepActivityBoundC (d := d) (L := L) (m₁ := m₁) (N := N) (ϱ := ϱ)
    hk1 a₁ ν δ
  exact ⟨S, stepNonvanishingC_of_activityBoundC I⟩

end Inhab

end Balaban.Fluctuation
