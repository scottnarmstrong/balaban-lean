/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.StepNonvanishCluster
public import Balaban.Fluctuation.StepIdentityReg
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# `StepNonvanishing` from the physical complex activity bound

`StepActivityBound` is the single named input replacing `StepNonvanishing` for complex data
(COMPLETE-STEP §2, (2.1)-(2.2), §5 row 6 `completeStepNonvanishing`).  From it,
`Zst_eq_exp_of_activityBound` shows `Z_{s,t} = exp 𝓛_{s,t}` with `‖𝓛_{s,t}‖ ≤ |𝔅| · A` on the two
segments, `stepNonvanishing_of_activityBound` gives `StepNonvanishing`, and
`prop26_complex_class_of_activity` is `prop26_complex_class` with `StepNonvanishing` replaced by
`StepActivityBound`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Polymer Balaban.Multiscale Balaban.SmallField.Def6
  Balaban.Background Balaban.SmallField MeasureTheory

section Bound

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- The two segments of the interpolation along which `Z_{s,t}` is needed:
`{(s,0) : s ∈ [0,1]} ∪ {(1,t) : t ∈ [0,1]}`. -/
def stepSegments : Set (ℝ × ℝ) :=
  {p | p.1 ∈ Set.Icc (0 : ℝ) 1 ∧ p.2 = 0} ∪ {p | p.1 = 1 ∧ p.2 ∈ Set.Icc (0 : ℝ) 1}

/-- **The physical complex activity bound of the step** (COMPLETE-STEP §2, (2.1)-(2.2)).

Source: Balaban, *P5* (Theorem 3.4 (a), (e) and Proposition 3.3; the cluster expansion of the
partition functions `Z_{s,0}`, `Z_{1,t}`), with the numerical hypotheses (3.5) of Theorem 3.4 as in
`InterpMarks`; the form of the identification of `ν_{p₁}` with the product of the block measures is
`BlockSplit` (Thm31a).  It is the open physical estimate `OPEN-PHYSICAL-ACTIVITIES` of
`notes/phase1/COMPLETE-STEP.md` §2:

* (2.1): for each `(s,t)` on the two segments (`stepSegments`) the exponent
  `W₁(s,ψ̂) + W₂(t,ψ̂; g)` is `ν_{p₁}`-almost everywhere the sum `∑_y H(y; s, t; ψ̂|_b)` of the
  block-local activities `A (s,t)` (measurable, depending on the cubes of the label only, bounded
  by `ε_H e^{-κ_H 𝗱(y)}`, entropy bound `K_c`), complex valued;
* (2.2): the numerical conditions on `ε_H, κ_H, κ₀, κ', K_c`, uniform in `(s,t)`, that imply the
  rate conditions `2H₀K₀e^{κ₁c}c₁ ≤ ½` and `2(2H₀K₀e^{κ₁c})c₁K_{0P}e^{c₁+κ'c_P} ≤ 1` of
  `mayer_pe` (see `numerics_PE`). -/
structure StepActivityBound (S : StepSetting d L N₁ m₁ k N ϱ) (C : StepClass d L N₁ m₁ k N ϱ)
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
    S.Wone C p.1 x + S.Wtwo C g p.2 x = ∑ y, (A p).H y (BS.restr x)

attribute [instance] StepActivityBound.fin

variable {S : StepSetting d L N₁ m₁ k N ϱ} {C : StepClass d L N₁ m₁ k N ϱ}
  {g : Fld d L N₁ m₁ (k + 1) N}

/-- **`Z_{s,t} = exp 𝓛_{s,t}` with `‖𝓛_{s,t}‖ ≤ |𝔅| ε_H K_c C_PE`** on the two segments
(COMPLETE-STEP (2.3)), for complex data. -/
theorem StepActivityBound.Zst_eq_exp (I : StepActivityBound S C g) {s t : ℝ}
    (hst : (s, t) ∈ stepSegments) :
    ∃ Lg : ℂ, S.Zst C g s t = Complex.exp Lg ∧
      ‖Lg‖ ≤ Fintype.card (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) I.m₀
        (k + 1) Set.univ) * (I.εH * I.Kc * CPE d L I.Kc I.κH I.κ0 I.κ') := by
  obtain ⟨Lg, h1, h2⟩ := labelAct_integral_eq_exp I.BS.μ I.hN (I.A (s, t)) I.hκ0 I.hKc I.hεpos
    I.hκ' I.hκ I.hε
  exact ⟨Lg, (StepSetting.Zst_eq_integral_pi S C g I.BS (I.A (s, t)).H (I.A (s, t)).meas s t
    (I.hW (s, t) hst)).trans h1, h2⟩

theorem StepActivityBound.Zst_ne_zero (I : StepActivityBound S C g) {s t : ℝ}
    (hst : (s, t) ∈ stepSegments) : S.Zst C g s t ≠ 0 := by
  obtain ⟨Lg, h, -⟩ := I.Zst_eq_exp hst
  rw [h]; exact Complex.exp_ne_zero _

/-- **`StepNonvanishing` from the activity bound.** -/
theorem stepNonvanishing_of_activityBound (I : StepActivityBound S C g) :
    S.StepNonvanishing C g :=
  ⟨fun _ hs => I.Zst_ne_zero (Or.inl ⟨hs, rfl⟩),
    fun _ ht => I.Zst_ne_zero (Or.inr ⟨rfl, ht⟩)⟩

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
/-- **Proposition 2.6 (whole lattice, `λ = ∞`, complete convention, complex data)** with the
class regularity `ClassRegular` and the physical complex activity bound `StepActivityBound` as the
inputs (in place of `StepNonvanishing` in `prop26_complex_class`). -/
theorem prop26_complex_class_of_activity (g : Fld d L N₁ m₁ (k + 1) N)
    (hc : S.ClassRegular C g) (hact : StepActivityBound S C g) :
    S.Tstep C g = Complex.exp (-(S.β : ℂ) * (S.Anew : ℂ) +
      EcompAt C.m₀ C.Tm S.a S.ν (Nat.le_succ k) S.psiKd - (S.Eppp C : ℂ) * (S.nU : ℂ) +
      FcompAt C.m₀ C.Tm S.a S.ν (Nat.le_succ k) S.psiKd g + S.E0 C + S.F0 C g) :=
  S.prop26_complex_class C ha₁ H hδ'0 hδ' hD'R hδ0 hfam hsm hχu hnorm hβ hp₁ hlt hB5 hK2 hp40
    hrad g hc (stepNonvanishing_of_activityBound hact)

end Public

end Bound

end Balaban.Fluctuation
