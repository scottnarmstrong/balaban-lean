/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.MarkedCubesLocal
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The marked first integral: exact transfer (BASE-KERNEL-3 §3)

* `sum_gst_marks_bound` (BASE-KERNEL-3 Lemma 3.1): summing the one-mark coefficients `Gst` of
  `marked_cubes_explicit` over a finite family of marks `G_y` gives a coefficient `R(Y)` that
  vanishes unless `Y` contains the block support of a mark and satisfies (3.4).
* `half_budget` (Corollary 3.2): the arithmetic (3.7)-(3.9).
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Polymer MeasureTheory

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ j : ℕ} {Ω : Set (CTorus d L N₁ m₁ K)}

local notation "𝔅" => CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω

open Classical in
/-- **BASE-KERNEL-3 Lemma 3.1 (3.3).** The summed one-mark coefficient
`R(Y) = ∑_y Gst(μ, Lab, A.H, blocksOf(y), G_y; Y)`. -/
noncomputable def markSum {Lb : Type*} [Fintype Lb] {Ωb : 𝔅 → Type*}
    [∀ b, MeasurableSpace (Ωb b)] (μ : ∀ b, Measure (Ωb b)) [∀ b, IsProbabilityMeasure (μ b)]
    (Lab : CubeLabels m₀ j Ω Lb) (H : Lb → (∀ b, Ωb b) → ℂ)
    (G : Lb → (∀ b, Ωb b) → ℂ) (Y : Finset 𝔅) : ℂ :=
  ∑ y, Gst μ Lab H (blocksOf m₀ j Ω (Lab.ysite y)) (G y) Y

open Classical in
/-- **BASE-KERNEL-3 Lemma 3.1.** Under the premises (3.1)-(3.2) of the note and `κ' ≥ 1`, for
every nonempty `Y`: `R(Y) = 0` unless `Y` contains the block support of some mark, and (3.4)
holds with `κ_b = κ' - 1`. -/
theorem sum_gst_marks_bound {Lb : Type*} [Fintype Lb] {Ωb : 𝔅 → Type*}
    [∀ b, MeasurableSpace (Ωb b)]
    (μ : ∀ b, Measure (Ωb b)) [∀ b, IsProbabilityMeasure (μ b)]
    (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K) (hΩ : IsPiUnion m₀ j Ω)
    {Lab : CubeLabels m₀ j Ω Lb} {εH κH κG κ0 κ' Kc F0 : ℝ}
    (A : LabelAct Lab Ωb εH κH κ0 Kc) (G : Lb → (∀ b, Ωb b) → ℂ)
    (hGm : ∀ y, Measurable (G y))
    (hGdep : ∀ y, DepOn (blocksOf m₀ j Ω (Lab.ysite y)) (G y))
    (hG : ∀ y Φ, ‖G y Φ‖ ≤ F0 * Real.exp (-κG * Lab.dl y))
    (hκ0 : aEnt d L + 1 ≤ κ0) (hKc : K0 d L κ0 + 1 ≤ Kc) (hεpos : 0 < εH) (hF0 : 0 < F0)
    (hκ' : 1 ≤ κ') (hκG : κH ≤ κG)
    (hκ : κ' + 3 * κ0 + c1 d L + 3 / 2 ≤ κH)
    (hε : εH ≤ 1 / (8 * Kc ^ 3 * c1 d L *
      Real.exp ((κH - 2 * κ0) * cG d L + c1 d L + κ' * cG d L)))
    (Y : Finset 𝔅) (hY : Y.Nonempty) :
    ((∀ y, ¬ blocksOf m₀ j Ω (Lab.ysite y) ⊆ Y) → markSum μ Lab A.H G Y = 0) ∧
    ‖markSum μ Lab A.H G Y‖ ≤
      CPE d L Kc κH κ0 κ' * Kc * c1 d L * F0 * Real.exp (-(κ' - 1) * dExt Y) := by
  have hκ'0 : 0 ≤ κ' := by linarith
  have hone := fun y => marked_cubes_explicit (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K)
    (m₀ := m₀) (j := j) (Ω := Ω) μ hN hj hΩ A y (G y) (hGm y) (hGdep y) (hG y) hκ0 hKc hεpos hF0
    hκ'0 hκG hκ hε
  obtain ⟨b0, hb0⟩ := hY
  have hKc0 : 0 ≤ Kc := le_trans (Finset.sum_nonneg fun y _ => by split_ifs <;> positivity)
    (A.entropy b0)
  constructor
  · intro h
    unfold markSum
    exact Finset.sum_eq_zero fun y _ => (hone y).2.2.2.1 Y (h y)
  · set E := Real.exp (-κ' * dExt Y) with hE
    have hCPE : 0 ≤ CPE d L Kc κH κ0 κ' := by
      unfold CPE; have := one_le_c1 d L; positivity
    have hterm : ∀ y, ‖Gst μ Lab A.H (blocksOf m₀ j Ω (Lab.ysite y)) (G y) Y‖ ≤
        (if blocksOf m₀ j Ω (Lab.ysite y) ⊆ Y then
          CPE d L Kc κH κ0 κ' * F0 * E * Real.exp (-κ0 * Lab.dl y) else 0) := by
      intro y
      split_ifs with h
      · have := (hone y).2.2.2.2 Y
        calc _ ≤ _ := this
          _ = _ := by rw [hE]; ring
      · rw [(hone y).2.2.2.1 Y h]; simp
    have hent : ∑ y : Lb, (if blocksOf m₀ j Ω (Lab.ysite y) ⊆ Y then
          Real.exp (-κ0 * Lab.dl y) else 0) ≤ Y.card * Kc := by
      calc _ ≤ ∑ y : Lb, ∑ b ∈ Y, (if box b.1 (cellSide L m₀ m₁ j) ⊆ Lab.ysite y then
              Real.exp (-κ0 * Lab.dl y) else 0) := by
            refine Finset.sum_le_sum fun y _ => ?_
            split_ifs with h
            · obtain ⟨b, hb⟩ := Lab.blocksOf_nonempty hN hj hΩ y
              have hbY : b ∈ Y := h hb
              have hbs := mem_blocksOf.1 hb
              calc Real.exp (-κ0 * Lab.dl y)
                  = (if box b.1 (cellSide L m₀ m₁ j) ⊆ Lab.ysite y then
                      Real.exp (-κ0 * Lab.dl y) else 0) := by simp [hbs]
                _ ≤ _ := Finset.single_le_sum (f := fun b : 𝔅 =>
                      if box b.1 (cellSide L m₀ m₁ j) ⊆ Lab.ysite y then
                        Real.exp (-κ0 * Lab.dl y) else 0)
                      (fun _ _ => by split_ifs <;> positivity) hbY
            · exact Finset.sum_nonneg fun b _ => by split_ifs <;> positivity
        _ = ∑ b ∈ Y, ∑ y : Lb, (if box b.1 (cellSide L m₀ m₁ j) ⊆ Lab.ysite y then
              Real.exp (-κ0 * Lab.dl y) else 0) := Finset.sum_comm
        _ ≤ ∑ b ∈ Y, Kc := Finset.sum_le_sum fun b _ => A.entropy b
        _ = _ := by simp
    have hcard := card_le_dExt (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) (m₀ := m₀)
      (j := j) (Ω := Ω) hN hj Y
    have hdE := dExt_nonneg (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) (m₀ := m₀)
      (j := j) (Ω := Ω) Y
    have h1t : 1 + dExt Y ≤ Real.exp (dExt Y) := by
      have := Real.add_one_le_exp (dExt Y); linarith
    have hc1 := one_le_c1 d L
    have hEexp : Real.exp (-(κ' - 1) * dExt Y) = E * Real.exp (dExt Y) := by
      rw [hE, ← Real.exp_add]; congr 1; ring
    have hEpos : 0 < E := Real.exp_pos _
    unfold markSum
    calc ‖∑ y, Gst μ Lab A.H (blocksOf m₀ j Ω (Lab.ysite y)) (G y) Y‖
        ≤ ∑ y, ‖Gst μ Lab A.H (blocksOf m₀ j Ω (Lab.ysite y)) (G y) Y‖ := norm_sum_le _ _
      _ ≤ ∑ y, (if blocksOf m₀ j Ω (Lab.ysite y) ⊆ Y then
          CPE d L Kc κH κ0 κ' * F0 * E * Real.exp (-κ0 * Lab.dl y) else 0) :=
          Finset.sum_le_sum fun y _ => hterm y
      _ = CPE d L Kc κH κ0 κ' * F0 * E * ∑ y : Lb, (if blocksOf m₀ j Ω (Lab.ysite y) ⊆ Y then
          Real.exp (-κ0 * Lab.dl y) else 0) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun y _ => ?_
          split_ifs <;> simp
      _ ≤ CPE d L Kc κH κ0 κ' * F0 * E * (Y.card * Kc) :=
          mul_le_mul_of_nonneg_left hent (by positivity)
      _ ≤ CPE d L Kc κH κ0 κ' * F0 * E * ((c1 d L * Real.exp (dExt Y)) * Kc) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ?_ hKc0) (by positivity)
          calc (Y.card : ℝ) ≤ c1 d L * (1 + dExt Y) := hcard
            _ ≤ _ := mul_le_mul_of_nonneg_left h1t (by linarith)
      _ = _ := by rw [hEexp]; ring

/-- **BASE-KERNEL-3 Corollary 3.2 (half-budget arithmetic), (3.7)-(3.9).** If the marked part is
bounded by `C_PE K_c c_1 F₀ e^{-κ_b d_Ext}` with `F₀ = C_m β₀^{-m-3/2}` and the determinant part by
`C_det β₀^{-m-3/2} e^{-κ_b d_Ext}`, and `β₁/β₀ ≤ B_L = 2L^{d-2}`, `β₀ ≥ (2 C_mark B_L^{m+1})²`,
then the sum is at most `½ β₁^{-m-1} e^{-κ_b d_Ext}`. -/
theorem half_budget {d L m : ℕ} (hL : 0 < L) {β0 β1 Cm Cdet CPEKc κb dE : ℝ} {r det : ℝ}
    (hβ0 : 0 < β0) (hβ1 : 0 < β1) (hCm : 0 ≤ Cm) (hCdet : 0 ≤ Cdet) (hP : 0 ≤ CPEKc)
    (hr : r ≤ CPEKc * (Cm * β0 ^ (-(m : ℝ) - 3 / 2)) * Real.exp (-κb * dE))
    (hdet : det ≤ Cdet * β0 ^ (-(m : ℝ) - 3 / 2) * Real.exp (-κb * dE))
    (hratio : β1 / β0 ≤ 2 * (L : ℝ) ^ (d - 2))
    (hβ : (2 * (CPEKc * Cm + Cdet) * (2 * (L : ℝ) ^ (d - 2)) ^ (m + 1)) ^ 2 ≤ β0) :
    r + det ≤ 1 / 2 * (β1 ^ (m + 1))⁻¹ * Real.exp (-κb * dE) := by
  set B : ℝ := 2 * (L : ℝ) ^ (d - 2) with hB
  have hBpos : 0 < B := by rw [hB]; have : (0 : ℝ) < L := by exact_mod_cast hL
                           positivity
  set C : ℝ := CPEKc * Cm + Cdet with hC
  have hC0 : 0 ≤ C := by rw [hC]; positivity
  set s := Real.sqrt β0 with hs
  have hspos : 0 < s := Real.sqrt_pos.2 hβ0
  have hss : s * s = β0 := Real.mul_self_sqrt hβ0.le
  have hsge : 2 * C * B ^ (m + 1) ≤ s := by
    have : (2 * C * B ^ (m + 1)) ^ 2 ≤ s ^ 2 := by rw [sq s, hss]; exact hβ
    exact le_of_sq_le_sq (by simpa using this) hspos.le |> fun h => h
  have hpow : β0 ^ (-(m : ℝ) - 3 / 2) = (β0 ^ (m + 1))⁻¹ * s⁻¹ := by
    have h1 : -(m : ℝ) - 3 / 2 = (-((m + 1 : ℕ) : ℝ)) + (-(1 / 2 : ℝ)) := by push_cast; ring
    rw [h1, Real.rpow_add hβ0, Real.rpow_neg hβ0.le, Real.rpow_natCast, Real.rpow_neg hβ0.le,
      hs, ← Real.sqrt_eq_rpow]
  have hβ1le : β1 ≤ B * β0 := by
    have := (div_le_iff₀ hβ0).1 hratio; linarith
  have hβ1pow : β1 ^ (m + 1) ≤ B ^ (m + 1) * β0 ^ (m + 1) := by
    rw [← mul_pow]; exact pow_le_pow_left₀ hβ1.le hβ1le _
  have hkey : C * s⁻¹ * (β0 ^ (m + 1))⁻¹ ≤ 1 / 2 * (β1 ^ (m + 1))⁻¹ := by
    have hP0 : 0 < β0 ^ (m + 1) := by positivity
    have hP1 : 0 < β1 ^ (m + 1) := by positivity
    have hBp : 0 < B ^ (m + 1) := by positivity
    have h : C * (2 * β1 ^ (m + 1)) ≤ s * β0 ^ (m + 1) :=
      calc C * (2 * β1 ^ (m + 1)) ≤ C * (2 * (B ^ (m + 1) * β0 ^ (m + 1))) := by gcongr
        _ = (2 * C * B ^ (m + 1)) * β0 ^ (m + 1) := by ring
        _ ≤ s * β0 ^ (m + 1) := by gcongr
    have h2 : (C * (2 * β1 ^ (m + 1))) / (s * β0 ^ (m + 1)) ≤ 1 :=
      (div_le_one (by positivity)).2 h
    calc C * s⁻¹ * (β0 ^ (m + 1))⁻¹
        = (C * (2 * β1 ^ (m + 1))) / (s * β0 ^ (m + 1)) * (1 / 2 * (β1 ^ (m + 1))⁻¹) := by
          field_simp
      _ ≤ 1 * (1 / 2 * (β1 ^ (m + 1))⁻¹) := by gcongr
      _ = _ := one_mul _
  have hE := Real.exp_pos (-κb * dE)
  calc r + det ≤ CPEKc * (Cm * β0 ^ (-(m : ℝ) - 3 / 2)) * Real.exp (-κb * dE) +
        Cdet * β0 ^ (-(m : ℝ) - 3 / 2) * Real.exp (-κb * dE) := add_le_add hr hdet
    _ = (C * ((β0 ^ (m + 1))⁻¹ * s⁻¹)) * Real.exp (-κb * dE) := by rw [hpow, hC]; ring
    _ ≤ 1 / 2 * (β1 ^ (m + 1))⁻¹ * Real.exp (-κb * dE) := by
        refine mul_le_mul_of_nonneg_right ?_ hE.le
        calc C * ((β0 ^ (m + 1))⁻¹ * s⁻¹) = C * s⁻¹ * (β0 ^ (m + 1))⁻¹ := by ring
          _ ≤ _ := hkey

open Classical in
/-- **BASE-KERNEL-3 Corollary 3.2** assembled: the summed mark coefficient `R(Y)` of Lemma 3.1
(with `F₀ = C_m β₀^{-m-3/2}`) plus a determinant coefficient `det` of norm at most
`C_det β₀^{-m-3/2} e^{-κ_b d_Ext(Y)}` is at most `½ β₁^{-m-1} e^{-κ_b d_Ext(Y)}`. -/
theorem markSum_add_det_half {Lb : Type*} [Fintype Lb] {Ωb : 𝔅 → Type*}
    [∀ b, MeasurableSpace (Ωb b)]
    (μ : ∀ b, Measure (Ωb b)) [∀ b, IsProbabilityMeasure (μ b)]
    (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K) (hΩ : IsPiUnion m₀ j Ω)
    {Lab : CubeLabels m₀ j Ω Lb} {εH κH κG κ0 κ' Kc : ℝ}
    (A : LabelAct Lab Ωb εH κH κ0 Kc) (G : Lb → (∀ b, Ωb b) → ℂ)
    (hGm : ∀ y, Measurable (G y))
    (hGdep : ∀ y, DepOn (blocksOf m₀ j Ω (Lab.ysite y)) (G y))
    {m : ℕ} {β0 β1 Cm Cdet : ℝ} (hβ0 : 0 < β0) (hβ1 : 0 < β1) (hCm : 0 < Cm) (hCdet : 0 ≤ Cdet)
    (hG : ∀ y Φ, ‖G y Φ‖ ≤ Cm * β0 ^ (-(m : ℝ) - 3 / 2) * Real.exp (-κG * Lab.dl y))
    (hκ0 : aEnt d L + 1 ≤ κ0) (hKc : K0 d L κ0 + 1 ≤ Kc) (hεpos : 0 < εH)
    (hκ' : 1 ≤ κ') (hκG : κH ≤ κG)
    (hκ : κ' + 3 * κ0 + c1 d L + 3 / 2 ≤ κH)
    (hε : εH ≤ 1 / (8 * Kc ^ 3 * c1 d L *
      Real.exp ((κH - 2 * κ0) * cG d L + c1 d L + κ' * cG d L)))
    (hratio : β1 / β0 ≤ 2 * (L : ℝ) ^ (d - 2))
    (hβ : (2 * (CPE d L Kc κH κ0 κ' * Kc * c1 d L * Cm + Cdet) *
      (2 * (L : ℝ) ^ (d - 2)) ^ (m + 1)) ^ 2 ≤ β0)
    (Y : Finset 𝔅) (hY : Y.Nonempty) (det : ℂ)
    (hdet : ‖det‖ ≤ Cdet * β0 ^ (-(m : ℝ) - 3 / 2) * Real.exp (-(κ' - 1) * dExt Y)) :
    ‖markSum μ Lab A.H G Y + det‖ ≤
      1 / 2 * (β1 ^ (m + 1))⁻¹ * Real.exp (-(κ' - 1) * dExt Y) := by
  have hF0 : 0 < Cm * β0 ^ (-(m : ℝ) - 3 / 2) := by positivity
  have h1 := (sum_gst_marks_bound μ hN hj hΩ A G hGm hGdep hG hκ0 hKc hεpos hF0 hκ' hκG hκ hε
    Y hY).2
  have hP : 0 ≤ CPE d L Kc κH κ0 κ' * Kc * c1 d L := by
    have hKc0 : 0 ≤ Kc := by
      obtain ⟨b0, -⟩ := hY
      exact le_trans (Finset.sum_nonneg fun y _ => by split_ifs <;> positivity) (A.entropy b0)
    unfold CPE; have := one_le_c1 d L; positivity
  refine (norm_add_le _ _).trans ?_
  have := half_budget (d := d) (L := L) (m := m) (Nat.pos_of_ne_zero (NeZero.ne L)) hβ0 hβ1
    hCm.le hCdet hP (r := ‖markSum μ Lab A.H G Y‖) (det := ‖det‖) (κb := κ' - 1)
    (dE := dExt Y) (by linarith [h1, show CPE d L Kc κH κ0 κ' * Kc * c1 d L *
      (Cm * β0 ^ (-(m : ℝ) - 3 / 2)) = CPE d L Kc κH κ0 κ' * Kc * c1 d L *
      (Cm * β0 ^ (-(m : ℝ) - 3 / 2)) from rfl]) hdet hratio hβ
  exact this

end Balaban.Fluctuation
