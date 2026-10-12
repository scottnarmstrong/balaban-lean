/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.StepComplexOut
public import Balaban.Fluctuation.Thm31bStep
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Theorem 3.1 fed with the holomorphic step (FLUCTUATION.md §3.5)

The engines of Theorem 3.1 are abstract in the exponent: `interpAvg_expansion_of_input`,
`thm31c_of_input`, `thm31d_of_input`, `thm31e_of_input` (`Thm31cde`) and `thm31b_of_input`
(`Thm31b`) take an arbitrary family `W : ℝ → X → ℂ` and integrand `f`.  They apply verbatim to the
exponents `WoneC`, `WtwoC` of the complex step (parts (c), (d), (e) need no new statement: they are
`thm31c_of_input I`, … for `I : InterpMarks S.nuFl BS (S.WoneC C) f`).

Two landed consumers are stated for the real objects `E0loc`, `E1loc`, `logA`, `M0` and are
restated here for the holomorphic ones:

* `E1MarksC`, `e1locC_expansion_of_input`, `DetExpansionC`, `nonempty_detExpansionC`,
  `thm31aC_of_input`, `thm31aC_of_input_const`: Theorem 3.1 (a) for `E0locC`;
* `sum_E0locC_of_sum_E1locC`: `∑_z ℰ₀(z) = ℰ₀` for the complex step, reduced to the interpolation
  part;
* `thm31bC_of_input_M0`: Theorem 3.1 (b) for `M0C`;
* `thm31cC_of_input`: Theorem 3.1 (c) for an interpolation average with the exponent `WoneC` (the
  instance of the abstract statement, recorded for the consumers).
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Polymer Balaban.Multiscale Balaban.Background
  Balaban.SmallField.Def6 MeasureTheory

section MarksC

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- **Proposition 3.3 for the complex step, in the fluctuation variable `ψ̂`, for the integrand of
`ℰ₁^{(k+1)}(z)`** (§3.5 (a); `E1Marks` for the objects of the complex step): the landed input
structure `InterpMarks` for the exponent `W₁(s,ψ̂) = WoneC` of `μ_{s,0}` and the mark
`DΦ₁(sψ')[1_{B(z)}ψ']` with the complex shift `ψ' = shiftUC ψ̂` and the complex derivative of
`Φ₁ = Phi1C`.  (`InterpMarks` is inhabited, `nonempty_interpMarks`.) -/
abbrev E1MarksC (S : StepSetting d L N₁ m₁ k N ϱ) (C : StepClass d L N₁ m₁ k N ϱ) {m₀ : ℕ}
    (BS : BlockSplit S m₀) (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))) : Type _ :=
  InterpMarks S.nuFl BS (S.WoneC C) (fun s x =>
    (fderiv ℂ (S.Phi1C C) ((s : ℂ) • S.shiftUC x)) (S.maskUC z (S.shiftUC x)))

end MarksC

section ThmC

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  {S : StepSetting d L N₁ m₁ k N ϱ} {C : StepClass d L N₁ m₁ k N ϱ} {m₀ : ℕ}
  {BS : BlockSplit S m₀} {z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))}

open Classical in
/-- **The interpolation integral `ℰ₁^{(k+1)}(z)` of the complex step has a localization expansion**
(§3.5 (a); the complex form of `e1loc_expansion_of_input`), conditional on `E1MarksC`. -/
theorem e1locC_expansion_of_input (I : E1MarksC S C BS z) :
    ∃ E : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
        Set.univ) → ℂ,
      S.E1locC C z = ∑ T, E T ∧
      ∀ T, ‖E T‖ ≤ CPE d L I.Kc I.κH I.κ0 I.κ' *
          (∑ i, I.F0 i * Real.exp (-I.κ0 * I.Lab.dl (I.y0 i))) * Real.exp (-I.κ' * dExt T) :=
  interpAvg_expansion_of_input I

open Classical in
/-- **Theorem 3.1 (c) for the complex step**: an interpolation average `∫₀¹ ⟨f(u)⟩_{u,0} du` in the
measures of the complex step (exponent `WoneC`) is `∑_S E(S)` with
`|E(S)| ≤ β_k^{-1} e^{-κ_a d_Ω(S)}`; the instance of the abstract `thm31c_of_input`. -/
theorem thm31cC_of_input {f : ℝ → S.E → ℂ} (I : InterpMarks S.nuFl BS (S.WoneC C) f) {κa βk : ℝ}
    (hκa : I.κ' = κa)
    (hB : CPE d L I.Kc I.κH I.κ0 I.κ' *
      (∑ i, I.F0 i * Real.exp (-I.κ0 * I.Lab.dl (I.y0 i))) ≤ βk⁻¹) :
    ∃ E : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
        Set.univ) → ℂ,
      interpAvg S.nuFl (S.WoneC C) f = ∑ T, E T ∧ ∀ T, ‖E T‖ ≤ βk⁻¹ * Real.exp (-κa * dExt T) :=
  thm31c_of_input I hκa hB

end ThmC

section DetC

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  {S : StepSetting d L N₁ m₁ k N ϱ} {C : StepClass d L N₁ m₁ k N ϱ} {m₀ : ℕ}

/-- **The expansion of `-½ ∑_{y ∈ B(z)} tr 𝕃(y,y)` at a complex datum** (§3.5 (a): LOC V3 with
`F(s) = 𝕃(s)(y,y)`, Lemma AE; Lemma 2.4 (c)): `DetExpansion` for `𝕃 = logAC`. -/
structure DetExpansionC (S : StepSetting d L N₁ m₁ k N ϱ) (m₀ : ℕ)
    (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))) (κ'' cdet : ℝ) where
  term : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
    Set.univ) → ℂ
  sum_eq : -(1 / 2 : ℂ) * ∑ y ∈ S.blockU z, ∑ i, S.logAC (y, i) (y, i) = ∑ T, term T
  bound : ∀ T, ‖term T‖ ≤ cdet * Real.exp (-κ'' * dExt T)

/-- `DetExpansionC` is inhabited (a single term carries the whole value), for every step, every `z`
and every `κ'' ≥ 0`. -/
theorem nonempty_detExpansionC (S : StepSetting d L N₁ m₁ k N ϱ) (m₀ : ℕ)
    (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))) {κ'' : ℝ} (hκ : 0 ≤ κ'') :
    ∃ cdet, Nonempty (DetExpansionC S m₀ z κ'' cdet) := by
  classical
  set v : ℂ := -(1 / 2 : ℂ) * ∑ y ∈ S.blockU z, ∑ i, S.logAC (y, i) (y, i) with hv
  set T0 : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
    Set.univ) := ∅
  refine ⟨‖v‖ * Real.exp (κ'' * Mbig d L N₁ m₁ (k + 1)), ⟨⟨fun T => if T = T0 then v else 0,
    by simp [hv, Finset.sum_ite_eq'], fun T => ?_⟩⟩⟩
  by_cases hT : T = T0
  · simp only [hT, ite_true]
    have h1 : Real.exp (-κ'' * dExt T0) ≥ Real.exp (-κ'' * Mbig d L N₁ m₁ (k + 1)) :=
      Real.exp_le_exp.2 (by nlinarith [dExt_le_Mbig (m₀ := m₀) (j := k + 1) (Ω := Set.univ) T0])
    calc ‖v‖ = ‖v‖ * Real.exp (κ'' * Mbig d L N₁ m₁ (k + 1)) *
          Real.exp (-κ'' * Mbig d L N₁ m₁ (k + 1)) := by
          rw [mul_assoc, ← Real.exp_add]; simp
      _ ≤ _ := mul_le_mul_of_nonneg_left h1 (by positivity)
  · simp only [hT, ite_false, norm_zero]
    exact mul_nonneg (mul_nonneg (norm_nonneg _) (Real.exp_pos _).le) (Real.exp_pos _).le

open Classical in
/-- **Theorem 3.1 (a) for the complex step, whole-lattice case, conditional on its inputs** (the
complex form of `thm31a_of_input`): `ℰ₀^{(k+1)}(z) = ∑_S ℰ₀(z,S)` for the holomorphic `E0locC`, with
`|ℰ₀(z,S)| ≤ (c_mark + c_det) e^{-κ' d_Ω(S)}`.  The named inputs are `E1MarksC` and
`DetExpansionC`. -/
theorem thm31aC_of_input {BS : BlockSplit S m₀}
    {z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))}
    (I : E1MarksC S C BS z) {κ'' cdet : ℝ} (hκ'' : I.κ' ≤ κ'') (D : DetExpansionC S m₀ z κ'' cdet) :
    ∃ E : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
        Set.univ) → ℂ,
      S.E0locC C z = ∑ T, E T ∧
      ∀ T, ‖E T‖ ≤ (CPE d L I.Kc I.κH I.κ0 I.κ' *
          (∑ i, I.F0 i * Real.exp (-I.κ0 * I.Lab.dl (I.y0 i))) + cdet) *
        Real.exp (-I.κ' * dExt T) := by
  obtain ⟨E1, h1, h2⟩ := e1locC_expansion_of_input I
  refine ⟨fun T => D.term T + E1 T, ?_, fun T => ?_⟩
  · rw [Finset.sum_add_distrib, ← D.sum_eq, ← h1]
    rfl
  · refine (norm_add_le _ _).trans ?_
    have hd : ‖D.term T‖ ≤ cdet * Real.exp (-I.κ' * dExt T) := by
      refine (D.bound T).trans ?_
      have hc : 0 ≤ cdet := by
        have := (D.bound T).trans' (norm_nonneg _)
        rcases le_or_gt 0 cdet with h | h
        · exact h
        · nlinarith [Real.exp_pos (-κ'' * dExt T)]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hc
      nlinarith [dExt_nonneg (m₀ := m₀) (j := k + 1) (Ω := Set.univ) T]
    nlinarith [h2 T]

/-- **Theorem 3.1 (a) for the complex step with the stated constant**, conditional on the same
inputs (the complex form of `thm31a_of_input_const`). -/
theorem thm31aC_of_input_const {BS : BlockSplit S m₀}
    {z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))}
    (I : E1MarksC S C BS z) {κ'' cdet : ℝ} (hκ'' : I.κ' ≤ κ'') (D : DetExpansionC S m₀ z κ'' cdet)
    {BL K0c : ℝ}
    (hmark : CPE d L I.Kc I.κH I.κ0 I.κ' *
      (∑ i, I.F0 i * Real.exp (-I.κ0 * I.Lab.dl (I.y0 i))) ≤ K0c)
    (hdet : cdet ≤ N * (L : ℝ) ^ d * BL * K0c) :
    ∃ E : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
        Set.univ) → ℂ,
      S.E0locC C z = ∑ T, E T ∧
      ∀ T, ‖E T‖ ≤ (N * (L : ℝ) ^ d * BL + 1) * K0c * Real.exp (-I.κ' * dExt T) := by
  obtain ⟨E, h1, h2⟩ := thm31aC_of_input I hκ'' D
  refine ⟨E, h1, fun T => (h2 T).trans ?_⟩
  exact mul_le_mul_of_nonneg_right (by nlinarith) (Real.exp_pos _).le

/-- **`∑_z ℰ₀^{(k+1)}(z) = ℰ₀^{(k+1)}` for the complex step, reduced to the interpolation part**
(P4 (2.56); the complex form of `sum_E0loc`): the trace parts add up to `halfLogDetCC`
(`sum_trace_E0locC`, at every datum), so the identity for `E0locC` follows from the one for
`E1locC`, `∑_z ℰ₁^{(k+1)}(z) = ℰ₁^{(k+1)}` (the complex form of `sum_E1loc`, which needs the complex
differentiability of `Φ₁ = Phi1C` near the segments and is not proved here). -/
theorem sum_E0locC_of_sum_E1locC (S : StepSetting d L N₁ m₁ k N ϱ) (C : StepClass d L N₁ m₁ k N ϱ)
    (h : ∑ z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))), S.E1locC C z = S.E1C C) :
    ∑ z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))), S.E0locC C z = S.E0C C := by
  unfold StepSetting.E0locC StepSetting.E0C
  rw [Finset.sum_add_distrib, h, S.sum_trace_E0locC]

open Classical in
/-- **Theorem 3.1 (b) for the complex step, conditional on `ObsMarks`** (the complex form of
`thm31b_of_input_M0`): `β_k^{-1/2} ℳ₀^{(k+1)}(y; g) = ∑_W E(W)` for the holomorphic `M0C`, with
`E(W) = 0` unless `W ∋ x` and `|E(W)| ≤ (B₁ + B₂) e^{-κ_b d_Ω(W)}`. -/
theorem thm31bC_of_input_M0 (S : StepSetting d L N₁ m₁ k N ϱ) (C : StepClass d L N₁ m₁ k N ϱ)
    {m₀ : ℕ} (BS : BlockSplit S m₀) (g : Fld d L N₁ m₁ (k + 1) N)
    (y : CTorus d L N₁ m₁ (k + 1)) (i : Fin N)
    {bx : CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1) Set.univ}
    (I : ObsMarks S.nuFl BS (fun t x => S.WoneC C 1 x + S.WtwoC C g t x)
      (fun t x => deriv (fun r => McompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k)
        (S.dataUC (S.psiAtC r x)) g y i) t) bx)
    {κb : ℝ} (hκb : κb ≤ min I.κh I.κ' - I.κ0 - 1) :
    ∃ E : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
        Set.univ) → ℂ,
      S.M0C C g y i = ((S.betaU ^ (1 / 2 : ℝ) : ℝ) : ℂ) * ∑ T, E T ∧ (∀ T, bx ∉ T → E T = 0) ∧
      ∀ T, ‖E T‖ ≤ (I.B1 + I.B2) * Real.exp (-κb * dExt T) := by
  obtain ⟨E, h1, h2, h3⟩ := thm31b_of_input I hκb
  refine ⟨E, ?_, h2, h3⟩
  rw [← h1]
  rfl

end DetC

end Balaban.Fluctuation
