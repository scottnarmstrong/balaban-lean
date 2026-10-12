/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.Decoupled2XGreen
public import Balaban.Localization.DecoupledXGrad

/-!
# (DG2): the weighted gradient of `G_{k,x,s} f`, for a cover `C` and an operator `H`

The Leibniz rule for `P_q = χ_q ũ` (`P_bond_bound`, `P_fwd_bound`, `P_bwd_bound`, `gradP_le`) and the
bounds `XData.dg2_grad`, `XData.dg2_cwsq`.
-/

@[expose] public section

namespace Balaban.Localization.Dec2

open Balaban Balaban.Multiscale Balaban.Background Finset Matrix

variable {d L N₁ m₁ k : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {C : DecCover d L N₁ m₁ (k + 1)} {H : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
  {a : ℕ → ℝ} {aT x ν Cx : ℝ} {α : H.Ω 1 → ℂ} {κ : ℝ}
  {s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ} {ε : ℝ} {r : CTorus d L N₁ m₁ (k + 1) → ℝ}


theorem chi_diff_le {q : ℕ × CTorus d L N₁ m₁ (k + 1)} {δ : ℝ}
    (hsm : IsSmoothField H δ (C.chiField q)) (y : H.Ω 1) {b : CTorus d L N₁ m₁ (k + 1)}
    (hadj : Adj (y : CTorus d L N₁ m₁ (k + 1)) b) :
    |C.chi q b - C.chi q y| ≤ δ / H.spacing (y : CTorus d L N₁ m₁ (k + 1)) := by
  have key : ∀ z : CTorus d L N₁ m₁ (k + 1),
      vn (C.chiField q z - C.chiField q y) = |C.chi q z - C.chi q y| := by
    intro z
    have e : C.chiField q z - C.chiField q y = fun _ : Fin 1 => (((C.chi q z - C.chi q y : ℝ)) : ℂ) := by
      funext i; simp [DecCover.chiField]
    rw [e, vn_const_one]
  obtain ⟨μ, h | h⟩ := hadj
  · rw [← key, h]; exact (hsm.grad y y.2 μ).1
  · have hb : b = (y : CTorus d L N₁ m₁ (k + 1)) - Pi.single μ 1 := eq_sub_of_add_eq h.symm
    rw [← key, hb]; exact (hsm.grad y y.2 μ).2

/-- **The bond bound for `P = χ ũ`** (no cut). -/
theorem P_bond_bound (S : XCover C H a aT ν Cx) {q : ℕ × CTorus d L N₁ m₁ (k + 1)}
    (hq : q ∈ C.cubeIdx) {δ : ℝ} (hsm : IsSmoothField H δ (C.chiField q))
    {r : CTorus d L N₁ m₁ (k + 1) → ℝ} (hr : IsAgmonWeight H r) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ 1 / 2) (u : H.Ω 1 → ℂ) (y : H.Ω 1) {b : CTorus d L N₁ m₁ (k + 1)}
    (hadj : Adj (y : CTorus d L N₁ m₁ (k + 1)) b) :
    Real.exp (ε * r y) ^ 2 * ‖((C.chi q b : ℝ) : ℂ) * zeroExt (H.Ω 1) u b -
        ((C.chi q y : ℝ) : ℂ) * zeroExt (H.Ω 1) u y‖ ^ 2 ≤
      4 * ‖agmonField H ε r u b - agmonField H ε r u y‖ ^ 2 +
        16 * ε ^ 2 * (invSqSpacing H b * ‖agmonField H ε r u b‖ ^ 2) +
        2 * δ ^ 2 * (invSqSpacing H y * ‖agmonField H ε r u y‖ ^ 2) := by
  have hbond := agmon_bond_pointwise H hr hε0 hε1 u y.2 hadj
  have hw0 : 0 < Real.exp (ε * r y) := Real.exp_pos _
  have hsp : 0 < H.spacing (y : CTorus d L N₁ m₁ (k + 1)) := spacing_pos H
  have hinv : invSqSpacing H (y : CTorus d L N₁ m₁ (k + 1)) =
      (H.spacing (y : CTorus d L N₁ m₁ (k + 1)) ^ 2)⁻¹ := invSqSpacing_eq H y.2
  have hvy : ‖agmonField H ε r u y‖ = Real.exp (ε * r y) * ‖zeroExt (H.Ω 1) u y‖ :=
    norm_agmonField H ε r u y
  have hnn : 0 ≤ 8 * ε ^ 2 * (invSqSpacing H b * ‖agmonField H ε r u b‖ ^ 2) := by
    have := invSqSpacing_nonneg H b
    positivity
  by_cases hb : b ∈ H.Ω 1
  · have hc := chi_mem_Icc S hq ⟨b, hb⟩
    have hd := chi_diff_le hsm y hadj
    set ub := zeroExt (H.Ω 1) u b with hub
    set uy := zeroExt (H.Ω 1) u y with huy
    have hdec : ((C.chi q b : ℝ) : ℂ) * ub - ((C.chi q y : ℝ) : ℂ) * uy =
        ((C.chi q b : ℝ) : ℂ) * (ub - uy) + uy * (((C.chi q b - C.chi q y : ℝ)) : ℂ) := by
      push_cast; ring
    have h1 : ‖((C.chi q b : ℝ) : ℂ) * ub - ((C.chi q y : ℝ) : ℂ) * uy‖ ≤
        ‖ub - uy‖ + ‖uy‖ * (δ / H.spacing (y : CTorus d L N₁ m₁ (k + 1))) := by
      rw [hdec]
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hc.1]
        calc C.chi q b * ‖ub - uy‖ ≤ 1 * ‖ub - uy‖ :=
              mul_le_mul_of_nonneg_right hc.2 (norm_nonneg _)
          _ = _ := one_mul _
      · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left hd (norm_nonneg _)
    have h2 : ‖((C.chi q b : ℝ) : ℂ) * ub - ((C.chi q y : ℝ) : ℂ) * uy‖ ^ 2 ≤
        2 * ‖ub - uy‖ ^ 2 + 2 * (‖uy‖ * (δ / H.spacing (y : CTorus d L N₁ m₁ (k + 1)))) ^ 2 := by
      have h := pow_le_pow_left₀ (norm_nonneg _) h1 2
      nlinarith [sq_nonneg (‖ub - uy‖ - ‖uy‖ * (δ / H.spacing (y : CTorus d L N₁ m₁ (k + 1))))]
    have h3 : Real.exp (ε * r y) ^ 2 * (2 * (‖uy‖ * (δ / H.spacing (y : CTorus d L N₁ m₁ (k + 1)))) ^ 2) =
        2 * δ ^ 2 * (invSqSpacing H y * ‖agmonField H ε r u y‖ ^ 2) := by
      rw [hinv, hvy]
      field_simp
    calc Real.exp (ε * r y) ^ 2 * ‖((C.chi q b : ℝ) : ℂ) * ub - ((C.chi q y : ℝ) : ℂ) * uy‖ ^ 2
        ≤ Real.exp (ε * r y) ^ 2 * (2 * ‖ub - uy‖ ^ 2 +
          2 * (‖uy‖ * (δ / H.spacing (y : CTorus d L N₁ m₁ (k + 1)))) ^ 2) :=
          mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
      _ = 2 * (Real.exp (ε * r y) ^ 2 * ‖ub - uy‖ ^ 2) +
          2 * δ ^ 2 * (invSqSpacing H y * ‖agmonField H ε r u y‖ ^ 2) := by
          rw [← h3]; ring
      _ ≤ 2 * (2 * ‖agmonField H ε r u b - agmonField H ε r u y‖ ^ 2 +
          8 * ε ^ 2 * (invSqSpacing H b * ‖agmonField H ε r u b‖ ^ 2)) +
          2 * δ ^ 2 * (invSqSpacing H y * ‖agmonField H ε r u y‖ ^ 2) := by
          have := mul_le_mul_of_nonneg_left hbond (by norm_num : (0 : ℝ) ≤ 2)
          linarith
      _ = _ := by ring
  · have hub : zeroExt (H.Ω 1) u b = 0 := zeroExt_not_mem _ _ hb
    have hc := chi_mem_Icc S hq y
    rw [hub, mul_zero, zero_sub, norm_neg, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg hc.1, mul_pow]
    rw [hub, zero_sub, norm_neg] at hbond
    have h1 : Real.exp (ε * r y) ^ 2 * (C.chi q y ^ 2 * ‖zeroExt (H.Ω 1) u y‖ ^ 2) ≤
        Real.exp (ε * r y) ^ 2 * ‖zeroExt (H.Ω 1) u y‖ ^ 2 := by
      have : C.chi q y ^ 2 ≤ 1 := by nlinarith [hc.1, hc.2]
      calc _ ≤ Real.exp (ε * r y) ^ 2 * (1 * ‖zeroExt (H.Ω 1) u y‖ ^ 2) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right this (sq_nonneg _))
              (sq_nonneg _)
        _ = _ := by ring
    have hv : agmonField H ε r u b = 0 := by
      unfold agmonField; rw [hub]; simp
    rw [hv, zero_sub, norm_neg]
    have h00 : 0 ≤ 2 * δ ^ 2 * (invSqSpacing H y * ‖agmonField H ε r u y‖ ^ 2) := by
      have := invSqSpacing_nonneg H (y : CTorus d L N₁ m₁ (k + 1))
      positivity
    have hvy2 : ‖agmonField H ε r u y‖ ^ 2 = Real.exp (ε * r y) ^ 2 *
        ‖zeroExt (H.Ω 1) u y‖ ^ 2 := by rw [hvy]; ring
    rw [← hvy2] at h1
    simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
      add_zero]
    nlinarith



/-! ### The cutoff piece `P_q = χ_q ũ_q` and the removed bonds -/


/-- `P_q = χ_q ũ` as a field on the torus. -/
noncomputable def Pq (C : DecCover d L N₁ m₁ (k + 1)) (H : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ)
    (q : ℕ × CTorus d L N₁ m₁ (k + 1)) (u : H.Ω 1 → ℂ) (z : CTorus d L N₁ m₁ (k + 1)) : ℂ :=
  ((C.chi q z : ℝ) : ℂ) * zeroExt (H.Ω 1) u z

theorem Pq_eq_zero_of_not_inner (S : XCover C H a aT ν Cx) {q : ℕ × CTorus d L N₁ m₁ (k + 1)}
    (hq : q ∈ C.cubeIdx) (u : H.Ω 1 → ℂ) {z : CTorus d L N₁ m₁ (k + 1)} (hz : ¬ Inner q z) :
    Pq C H q u z = 0 := by
  unfold Pq
  by_cases hzΩ : z ∈ H.Ω 1
  · have : C.chi q z = 0 := by
      by_contra h; exact hz (S.inner_near q hq hzΩ h (Or.inr (SameCell.refl _ _)))
    simp [this]
  · rw [zeroExt_not_mem _ _ hzΩ]; simp

theorem Pq_ne_zero (S : XCover C H a aT ν Cx) (hα : AdmPot H α) (hx : 0 ≤ x)
    {q : ℕ × CTorus d L N₁ m₁ (k + 1)} (hq : q ∈ C.cubeIdx) (g : H.Ω 1 → ℂ)
    {z : CTorus d L N₁ m₁ (k + 1)}
    (h : Pq C H q (cubeGx H a aT x ν α q *ᵥ g) z ≠ 0) : z ∈ H.Ω 1 ∧ z ∈ intBox q := by
  unfold Pq at h
  have hz : zeroExt (H.Ω 1) (cubeGx H a aT x ν α q *ᵥ g) z ≠ 0 := right_ne_zero_of_mul h
  by_cases hzΩ : z ∈ H.Ω 1
  · refine ⟨hzΩ, ?_⟩
    by_contra hb
    apply hz
    rw [zeroExt_mem' _ hzΩ]
    exact cubeGx_supp S hα hx hq g ⟨z, hzΩ⟩ hb
  · exact absurd (zeroExt_not_mem _ _ hzΩ) hz

variable {δ : ℝ}

theorem P_fwd_bound (S : XCover C H a aT ν Cx) {q : ℕ × CTorus d L N₁ m₁ (k + 1)}
    (hq : q ∈ C.cubeIdx) (hsm : IsSmoothField H δ (C.chiField q)) (hr : IsAgmonWeight H r)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 2) (u : H.Ω 1 → ℂ) (y : H.Ω 1) (μ : Fin d) :
    Real.exp (ε * r y) ^ 2 * ‖Pq C H q u ((y : CTorus d L N₁ m₁ (k + 1)) + Pi.single μ 1) -
        Pq C H q u y‖ ^ 2 ≤
      4 * (if ((y : CTorus d L N₁ m₁ (k + 1)), μ) ∈ cubeCut H (intBox q) then 0 else
          ‖agmonField H ε r u ((y : CTorus d L N₁ m₁ (k + 1)) + Pi.single μ 1) -
            agmonField H ε r u y‖ ^ 2) +
        16 * ε ^ 2 * (invSqSpacing H ((y : CTorus d L N₁ m₁ (k + 1)) + Pi.single μ 1) *
          ‖agmonField H ε r u ((y : CTorus d L N₁ m₁ (k + 1)) + Pi.single μ 1)‖ ^ 2) +
        2 * δ ^ 2 * (invSqSpacing H y * ‖agmonField H ε r u y‖ ^ 2) := by
  have hinv1 := invSqSpacing_nonneg H ((y : CTorus d L N₁ m₁ (k + 1)) + Pi.single μ 1)
  have hinv2 := invSqSpacing_nonneg H (y : CTorus d L N₁ m₁ (k + 1))
  by_cases hc : ((y : CTorus d L N₁ m₁ (k + 1)), μ) ∈ cubeCut H (intBox q)
  · have hy : ¬ Inner q (y : CTorus d L N₁ m₁ (k + 1)) := fun h => (h.noCut μ).1 hc
    have hb : ¬ Inner q ((y : CTorus d L N₁ m₁ (k + 1)) + Pi.single μ 1) := fun h =>
      (h.noCut μ).2 (by simpa using hc)
    rw [Pq_eq_zero_of_not_inner S hq u hy, Pq_eq_zero_of_not_inner S hq u hb]
    simp only [hc, ↓reduceIte, sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, mul_zero, zero_add, mul_zero]
    positivity
  · simp only [hc, ↓reduceIte]
    exact P_bond_bound S hq hsm hr hε0 hε1 u y ⟨μ, Or.inl rfl⟩

theorem P_bwd_bound (S : XCover C H a aT ν Cx) {q : ℕ × CTorus d L N₁ m₁ (k + 1)}
    (hq : q ∈ C.cubeIdx) (hsm : IsSmoothField H δ (C.chiField q)) (hr : IsAgmonWeight H r)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 2) (u : H.Ω 1 → ℂ) (y : H.Ω 1) (μ : Fin d) :
    Real.exp (ε * r y) ^ 2 * ‖Pq C H q u ((y : CTorus d L N₁ m₁ (k + 1)) - Pi.single μ 1) -
        Pq C H q u y‖ ^ 2 ≤
      4 * (if ((y : CTorus d L N₁ m₁ (k + 1)) - Pi.single μ 1, μ) ∈ cubeCut H (intBox q) then 0
          else ‖agmonField H ε r u ((y : CTorus d L N₁ m₁ (k + 1)) - Pi.single μ 1) -
            agmonField H ε r u y‖ ^ 2) +
        16 * ε ^ 2 * (invSqSpacing H ((y : CTorus d L N₁ m₁ (k + 1)) - Pi.single μ 1) *
          ‖agmonField H ε r u ((y : CTorus d L N₁ m₁ (k + 1)) - Pi.single μ 1)‖ ^ 2) +
        2 * δ ^ 2 * (invSqSpacing H y * ‖agmonField H ε r u y‖ ^ 2) := by
  have hinv1 := invSqSpacing_nonneg H ((y : CTorus d L N₁ m₁ (k + 1)) - Pi.single μ 1)
  have hinv2 := invSqSpacing_nonneg H (y : CTorus d L N₁ m₁ (k + 1))
  by_cases hc : ((y : CTorus d L N₁ m₁ (k + 1)) - Pi.single μ 1, μ) ∈ cubeCut H (intBox q)
  · have hy : ¬ Inner q (y : CTorus d L N₁ m₁ (k + 1)) := fun h => (h.noCut μ).2 hc
    have hb : ¬ Inner q ((y : CTorus d L N₁ m₁ (k + 1)) - Pi.single μ 1) := fun h =>
      (h.noCut μ).1 hc
    rw [Pq_eq_zero_of_not_inner S hq u hy, Pq_eq_zero_of_not_inner S hq u hb]
    simp only [hc, ↓reduceIte, sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, mul_zero, zero_add, mul_zero]
    positivity
  · simp only [hc, ↓reduceIte]
    exact P_bond_bound S hq hsm hr hε0 hε1 u y ⟨μ, Or.inr (by simp)⟩


/-- The weighted gradient of `P_q` (all bonds at the points of `Ω₁`). -/
noncomputable def gradP (C : DecCover d L N₁ m₁ (k + 1)) (H : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ)
    (q : ℕ × CTorus d L N₁ m₁ (k + 1)) (ε : ℝ) (r : CTorus d L N₁ m₁ (k + 1) → ℝ)
    (u : H.Ω 1 → ℂ) : ℝ :=
  ∑ y ∈ H.Ω 1, ∑ μ : Fin d, Real.exp (ε * r y) ^ 2 *
    (‖Pq C H q u ((y : CTorus d L N₁ m₁ (k + 1)) + Pi.single μ 1) - Pq C H q u y‖ ^ 2 +
      ‖Pq C H q u ((y : CTorus d L N₁ m₁ (k + 1)) - Pi.single μ 1) - Pq C H q u y‖ ^ 2)

/-- **The gradient of `χ_q ũ_q`**: `Φ_q ≤ 8 E_q + (32 ε² d + 4 d δ²) W_q`. -/
theorem gradP_le (S : XCover C H a aT ν Cx) {q : ℕ × CTorus d L N₁ m₁ (k + 1)}
    (hq : q ∈ C.cubeIdx) (hsm : IsSmoothField H δ (C.chiField q)) (hr : IsAgmonWeight H r)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 2) (u : H.Ω 1 → ℂ) :
    gradP C H q ε r u ≤ 8 * cutEnergy (cubeCut H (intBox q)) (agmonField H ε r u) +
      (32 * ε ^ 2 * d + 4 * d * δ ^ 2) * cwsq H (agmonField H ε r u) := by
  classical
  set v := agmonField H ε r u with hv
  set cut := cubeCut H (intBox q) with hcut
  set T₁ : CTorus d L N₁ m₁ (k + 1) → Fin d → ℝ := fun y μ =>
      4 * (if (y, μ) ∈ cut then 0 else ‖v (y + Pi.single μ 1) - v y‖ ^ 2) +
        16 * ε ^ 2 * (invSqSpacing H (y + Pi.single μ 1) * ‖v (y + Pi.single μ 1)‖ ^ 2) with hT₁
  set T₂ : CTorus d L N₁ m₁ (k + 1) → Fin d → ℝ := fun y μ =>
      4 * (if (y - Pi.single μ 1, μ) ∈ cut then 0 else ‖v (y - Pi.single μ 1) - v y‖ ^ 2) +
        16 * ε ^ 2 * (invSqSpacing H (y - Pi.single μ 1) * ‖v (y - Pi.single μ 1)‖ ^ 2) with hT₂
  set B : CTorus d L N₁ m₁ (k + 1) → ℝ := fun y => ∑ μ : Fin d, (T₁ y μ + T₂ y μ) +
      4 * d * δ ^ 2 * (invSqSpacing H y * ‖v y‖ ^ 2) with hB
  have hT0 : ∀ y μ, 0 ≤ T₁ y μ + T₂ y μ := fun y μ => by
    have h1 := invSqSpacing_nonneg H (y + Pi.single μ 1)
    have h2 := invSqSpacing_nonneg H (y - Pi.single μ 1)
    have h3 : 0 ≤ (if (y, μ) ∈ cut then (0 : ℝ) else ‖v (y + Pi.single μ 1) - v y‖ ^ 2) := by
      split_ifs <;> positivity
    have h4 : 0 ≤ (if (y - Pi.single μ 1, μ) ∈ cut then (0 : ℝ) else
        ‖v (y - Pi.single μ 1) - v y‖ ^ 2) := by
      split_ifs <;> positivity
    simp only [hT₁, hT₂]
    positivity
  have hB0 : ∀ y, 0 ≤ B y := fun y => by
    have h5 := invSqSpacing_nonneg H y
    simp only [hB]
    have := Finset.sum_nonneg fun μ (_ : μ ∈ (Finset.univ : Finset (Fin d))) => hT0 y μ
    positivity
  have hpt : ∀ y ∈ H.Ω 1, ∑ μ : Fin d, Real.exp (ε * r y) ^ 2 *
      (‖Pq C H q u ((y : CTorus d L N₁ m₁ (k + 1)) + Pi.single μ 1) - Pq C H q u y‖ ^ 2 +
        ‖Pq C H q u ((y : CTorus d L N₁ m₁ (k + 1)) - Pi.single μ 1) - Pq C H q u y‖ ^ 2) ≤
      B y := by
    intro y hy
    have hμ : ∑ μ : Fin d, ((T₁ y μ + 2 * δ ^ 2 * (invSqSpacing H y * ‖v y‖ ^ 2)) +
        (T₂ y μ + 2 * δ ^ 2 * (invSqSpacing H y * ‖v y‖ ^ 2))) = B y := by
      have : ∀ μ : Fin d, ((T₁ y μ + 2 * δ ^ 2 * (invSqSpacing H y * ‖v y‖ ^ 2)) +
          (T₂ y μ + 2 * δ ^ 2 * (invSqSpacing H y * ‖v y‖ ^ 2))) =
          (T₁ y μ + T₂ y μ) + 4 * δ ^ 2 * (invSqSpacing H y * ‖v y‖ ^ 2) := fun μ => by ring
      simp only [this, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, hB]
      ring
    rw [← hμ]
    refine Finset.sum_le_sum fun μ _ => ?_
    have h1 := P_fwd_bound S hq hsm hr hε0 hε1 u ⟨y, hy⟩ μ
    have h2 := P_bwd_bound S hq hsm hr hε0 hε1 u ⟨y, hy⟩ μ
    rw [mul_add]
    exact add_le_add h1 h2
  have hsum : gradP C H q ε r u ≤ ∑ y, B y := by
    calc gradP C H q ε r u ≤ ∑ y ∈ H.Ω 1, B y := Finset.sum_le_sum fun y hy => hpt y hy
      _ ≤ ∑ y, B y := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          fun y _ _ => hB0 y
  have hBsum : ∑ y, B y = 8 * cutEnergy cut v + (32 * ε ^ 2 * d + 4 * d * δ ^ 2) * cwsq H v := by
    have e1 : ∑ y : CTorus d L N₁ m₁ (k + 1), ∑ μ : Fin d,
        (if (y, μ) ∈ cut then 0 else ‖v (y + Pi.single μ 1) - v y‖ ^ 2) = cutEnergy cut v := rfl
    have e2 := sum_shift_cutEnergy_back cut v
    have e3 := sum_shift_cwsq H v
    have e4 := sum_shift_cwsq_back H v
    have hS1 : ∑ y : CTorus d L N₁ m₁ (k + 1), ∑ μ : Fin d, T₁ y μ =
        4 * cutEnergy cut v + 16 * ε ^ 2 * (d * cwsq H v) := by
      simp only [hT₁, Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [e1, e3]
    have hS2 : ∑ y : CTorus d L N₁ m₁ (k + 1), ∑ μ : Fin d, T₂ y μ =
        4 * cutEnergy cut v + 16 * ε ^ 2 * (d * cwsq H v) := by
      simp only [hT₂, Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [e2, e4]
    simp only [hB, Finset.sum_add_distrib]
    rw [hS1, hS2]
    have : ∑ y : CTorus d L N₁ m₁ (k + 1), 4 * d * δ ^ 2 * (invSqSpacing H y * ‖v y‖ ^ 2) =
        4 * d * δ ^ 2 * cwsq H v := by
      rw [← Finset.mul_sum]; rfl
    rw [this]
    ring
  rw [hBsum] at hsum
  exact hsum


/-! ### The overlap at a bond and the gradient of `G*_{x,s} g` -/


variable {κ : ℝ} {s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ} {ε : ℝ}
  {r : CTorus d L N₁ m₁ (k + 1) → ℝ} {δ : ℝ}

theorem sq_norm_sum_overlap2 (S : XCover C H a aT ν Cx)
    {F : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ} (y : H.Ω 1) (b : CTorus d L N₁ m₁ (k + 1))
    (hF : ∀ q ∈ C.cubeIdx, F q ≠ 0 → ((y : CTorus d L N₁ m₁ (k + 1)) ∈ intBox q ∨
      (b ∈ H.Ω 1 ∧ b ∈ intBox q))) :
    ‖∑ q ∈ C.cubeIdx, F q‖ ^ 2 ≤ (2 * (3 * 5 ^ d) : ℝ) * ∑ q ∈ C.cubeIdx, ‖F q‖ ^ 2 := by
  classical
  set Q1 := (C.cubeIdx).filter (fun q => (y : CTorus d L N₁ m₁ (k + 1)) ∈ intBox q) with hQ1
  set Q2 := (C.cubeIdx).filter (fun q => b ∈ H.Ω 1 ∧ b ∈ intBox q) with hQ2
  set Q := Q1 ∪ Q2 with hQ
  have hsum : ∑ q ∈ C.cubeIdx, F q = ∑ q ∈ Q, F q := by
    symm
    refine Finset.sum_subset (Finset.union_subset (Finset.filter_subset _ _)
      (Finset.filter_subset _ _)) fun q hq hnq => ?_
    by_contra hne
    apply hnq
    rcases hF q hq hne with h | h
    · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hq, h⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hq, h⟩)
  have hc1 : (Q1.card : ℝ) ≤ 3 * 5 ^ d := by exact_mod_cast card_overlap_le S y
  have hc2 : (Q2.card : ℝ) ≤ 3 * 5 ^ d := by
    by_cases hb : b ∈ H.Ω 1
    · have := card_overlap_le S ⟨b, hb⟩
      have e : Q2 = (C.cubeIdx).filter (fun q => b ∈ intBox q) :=
        Finset.filter_congr fun q _ => by simp [hb]
      rw [e]
      exact_mod_cast this
    · have : Q2 = ∅ := by
        refine Finset.filter_false_of_mem fun q _ => ?_
        simp [hb]
      rw [this]; simp
  have hcQ : (Q.card : ℝ) ≤ 2 * (3 * 5 ^ d) := by
    have := Finset.card_union_le Q1 Q2
    have h : (Q.card : ℝ) ≤ Q1.card + Q2.card := by exact_mod_cast this
    linarith
  rw [hsum]
  have h1 : ‖∑ q ∈ Q, F q‖ ≤ ∑ q ∈ Q, ‖F q‖ := norm_sum_le _ _
  have h2 : (∑ q ∈ Q, ‖F q‖) ^ 2 ≤ (Q.card : ℝ) * ∑ q ∈ Q, ‖F q‖ ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  have h4 : ∑ q ∈ Q, ‖F q‖ ^ 2 ≤ ∑ q ∈ C.cubeIdx, ‖F q‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.union_subset (Finset.filter_subset _ _)
      (Finset.filter_subset _ _)) fun _ _ _ => sq_nonneg _
  have h5 : 0 ≤ ∑ q ∈ Q, ‖F q‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  calc ‖∑ q ∈ Q, F q‖ ^ 2 ≤ (∑ q ∈ Q, ‖F q‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ (Q.card : ℝ) * ∑ q ∈ Q, ‖F q‖ ^ 2 := h2
    _ ≤ (2 * (3 * 5 ^ d) : ℝ) * ∑ q ∈ Q, ‖F q‖ ^ 2 := mul_le_mul_of_nonneg_right hcQ h5
    _ ≤ (2 * (3 * 5 ^ d) : ℝ) * ∑ q ∈ C.cubeIdx, ‖F q‖ ^ 2 :=
        mul_le_mul_of_nonneg_left h4 (by positivity)

theorem bond_overlap_bound (D : XData C H a aT ν x α κ s Cx) (g : H.Ω 1 → ℂ) (y : H.Ω 1)
    (b : CTorus d L N₁ m₁ (k + 1)) :
    ‖zeroExt (H.Ω 1) (Gstarx C H a aT x ν α s *ᵥ g) b - zeroExt (H.Ω 1) (Gstarx C H a aT x ν α s *ᵥ g) y‖
        ^ 2 ≤ (2 * (3 * 5 ^ d) : ℝ) * (Real.exp (N0 d L * κ) ^ 2 * ∑ q ∈ C.cubeIdx,
          ‖Pq C H q (cubeGx H a aT x ν α q *ᵥ g) b - Pq C H q (cubeGx H a aT x ν α q *ᵥ g) y‖ ^ 2) := by
  have hL1 : 1 ≤ L := by have := D.st.hL; omega
  set F : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ := fun q => C.sProd s q *
    (Pq C H q (cubeGx H a aT x ν α q *ᵥ g) b - Pq C H q (cubeGx H a aT x ν α q *ᵥ g) y) with hF
  have hsum : zeroExt (H.Ω 1) (Gstarx C H a aT x ν α s *ᵥ g) b -
      zeroExt (H.Ω 1) (Gstarx C H a aT x ν α s *ᵥ g) y = ∑ q ∈ C.cubeIdx, F q := by
    rw [zeroExt_Gstarx, zeroExt_Gstarx, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    simp only [hF, Pq]
    ring
  rw [hsum]
  have hsupp : ∀ q ∈ C.cubeIdx, F q ≠ 0 → ((y : CTorus d L N₁ m₁ (k + 1)) ∈ intBox q ∨
      (b ∈ H.Ω 1 ∧ b ∈ intBox q)) := by
    intro q hq hne
    by_contra hcon
    push Not at hcon
    apply hne
    have h1 : Pq C H q (cubeGx H a aT x ν α q *ᵥ g) y = 0 := by
      by_contra h
      exact hcon.1 (Pq_ne_zero D.st D.pot D.x0 hq g h).2
    have h2 : Pq C H q (cubeGx H a aT x ν α q *ᵥ g) b = 0 := by
      by_contra h
      have := Pq_ne_zero D.st D.pot D.x0 hq g h
      exact hcon.2 this.1 this.2
    simp only [hF, h1, h2, sub_self, mul_zero]
  refine (sq_norm_sum_overlap2 D.st y b hsupp).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun q hq => ?_
  have hsp : ‖C.sProd s q‖ ≤ Real.exp (N0 d L * κ) :=
    C.norm_sProd_le (D.st.card_qset q hq) D.κ0 D.sb
  simp only [hF, norm_mul, mul_pow]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hsp 2) (sq_nonneg _)


theorem Cchi_le_cstarX (d L : ℕ) (hCx : 0 ≤ Cx) : Cx ≤ cstarX d L Cx := by
  have h1 := commXConst_nonneg d L
  have h2 := hCx
  have h5 : (1 : ℝ) ≤ 5 ^ d := one_le_pow₀ (by norm_num)
  unfold cstarX
  nlinarith [mul_nonneg h1 h2, mul_nonneg (mul_nonneg h1 h2) (by positivity : (0 : ℝ) ≤ 5 ^ d)]

theorem delta_le_one (D : XData C H a aT ν x α κ s Cx) : Cx / (L : ℝ) ^ m₁ ≤ 1 := by
  have hL1 : 1 ≤ L := by have := D.st.hL; omega
  have hM0 : (0 : ℝ) < (L : ℝ) ^ m₁ := by
    have : (0 : ℝ) < L := by exact_mod_cast hL1
    positivity
  rw [div_le_one hM0]
  have hE : 1 ≤ Real.exp (N0 d L * κ) := Real.one_le_exp (by have := D.κ0; positivity)
  have hc := cstarX_pos d L D.Cx_nn
  calc Cx ≤ cstarX d L Cx := Cchi_le_cstarX d L D.Cx_nn
    _ ≤ cstarX d L Cx * Real.exp (N0 d L * κ) := by nlinarith
    _ ≤ _ := D.big


theorem gradOn_Gstarx_le (D : XData C H a aT ν x α κ s Cx) (g : H.Ω 1 → ℂ) :
    gradOn H ε r Finset.univ (Gstarx C H a aT x ν α s *ᵥ g) ≤
      (2 * (3 * 5 ^ d) : ℝ) * (Real.exp (N0 d L * κ) ^ 2 * ∑ q ∈ C.cubeIdx,
        gradP C H q ε r (cubeGx H a aT x ν α q *ᵥ g)) := by
  classical
  unfold gradOn gradP
  simp only [Finset.mem_univ, ↓reduceIte]
  set K₀ : ℝ := 2 * (3 * 5 ^ d) with hK₀
  set E₀ : ℝ := Real.exp (N0 d L * κ) ^ 2 with hE₀
  set U := zeroExt (H.Ω 1) (Gstarx C H a aT x ν α s *ᵥ g) with hU
  set c : (ℕ × CTorus d L N₁ m₁ (k + 1)) → CTorus d L N₁ m₁ (k + 1) → Fin d → ℝ := fun q y μ =>
    (‖Pq C H q (cubeGx H a aT x ν α q *ᵥ g) (y + Pi.single μ 1) -
        Pq C H q (cubeGx H a aT x ν α q *ᵥ g) y‖ ^ 2 +
      ‖Pq C H q (cubeGx H a aT x ν α q *ᵥ g) (y - Pi.single μ 1) -
        Pq C H q (cubeGx H a aT x ν α q *ᵥ g) y‖ ^ 2) with hc
  have hpt : ∀ y ∈ H.Ω 1, Real.exp (ε * r y) ^ 2 * ∑ μ : Fin d,
      (‖U (y + Pi.single μ 1) - U y‖ ^ 2 + ‖U (y - Pi.single μ 1) - U y‖ ^ 2) ≤
      K₀ * (E₀ * ∑ q ∈ C.cubeIdx, ∑ μ : Fin d, Real.exp (ε * r y) ^ 2 * c q y μ) := by
    intro y hy
    have hμ : ∀ μ : Fin d, ‖U (y + Pi.single μ 1) - U y‖ ^ 2 + ‖U (y - Pi.single μ 1) - U y‖ ^ 2 ≤
        K₀ * (E₀ * ∑ q ∈ C.cubeIdx, c q y μ) := by
      intro μ
      have h1 := bond_overlap_bound D g ⟨y, hy⟩ (y + Pi.single μ 1)
      have h2 := bond_overlap_bound D g ⟨y, hy⟩ (y - Pi.single μ 1)
      simp only [hc, Finset.sum_add_distrib]
      simp only [hK₀, hE₀, hU]
      linarith
    calc Real.exp (ε * r y) ^ 2 * ∑ μ : Fin d,
          (‖U (y + Pi.single μ 1) - U y‖ ^ 2 + ‖U (y - Pi.single μ 1) - U y‖ ^ 2)
        = ∑ μ : Fin d, Real.exp (ε * r y) ^ 2 *
          (‖U (y + Pi.single μ 1) - U y‖ ^ 2 + ‖U (y - Pi.single μ 1) - U y‖ ^ 2) := by
          rw [Finset.mul_sum]
      _ ≤ ∑ μ : Fin d, Real.exp (ε * r y) ^ 2 *
          (K₀ * (E₀ * ∑ q ∈ C.cubeIdx, c q y μ)) :=
          Finset.sum_le_sum fun μ _ => mul_le_mul_of_nonneg_left (hμ μ) (sq_nonneg _)
      _ = _ := sum_swap_aux _ _ _ _ _ _
  calc _ ≤ ∑ y ∈ H.Ω 1, K₀ * (E₀ * ∑ q ∈ C.cubeIdx, ∑ μ : Fin d,
        Real.exp (ε * r y) ^ 2 * c q y μ) := Finset.sum_le_sum fun y hy => hpt y hy
    _ = K₀ * (E₀ * ∑ q ∈ C.cubeIdx, ∑ y ∈ H.Ω 1, ∑ μ : Fin d,
        Real.exp (ε * r y) ^ 2 * c q y μ) := by
        rw [← Finset.mul_sum, ← Finset.mul_sum]
        congr 2
        rw [Finset.sum_comm]



/-! ### (DG2) -/


theorem XData.gradP_cube_le (D : XData C H a aT ν x α κ s Cx) (W : XWeight H ε r)
    {q : ℕ × CTorus d L N₁ m₁ (k + 1)} (hq : q ∈ C.cubeIdx) (g : H.Ω 1 → ℂ) :
    gradP C H q ε r (cubeGx H a aT x ν α q *ᵥ g) ≤
      (136 + 1024 * d) * agmonSource H ε r (cD H q *ᵥ g) := by
  have hd : 0 < d := by have := D.st.hd; omega
  have hL1 : 1 ≤ L := by have := D.st.hL; omega
  have hε2 : ε ≤ agmonRate d := W.ε1.trans (xAgmonRate_le_agmonRate hd hL1)
  have hsm := D.st.chi_smooth q hq
  have hg := gradP_le D.st hq hsm W.agm W.ε0 (by linarith [agmonRate_le hd]) (cubeGx H a aT x ν α q *ᵥ g)
  have hE := cube_cutEnergy_le D.st D.pot D.x0 hq W.agm W.ε0 W.ε1 g
  have hWq := cube_cwsq_le D.st D.pot D.x0 hq W.agm W.ε0 W.ε1 g
  have hS0 := agmonSource_nonneg H ε r (cD H q *ᵥ g)
  have hW0 := cwsq_nonneg H (agmonField H ε r (cubeGx H a aT x ν α q *ᵥ g))
  have hδ1 := delta_le_one D
  have hδ0 : 0 ≤ Cx / (L : ℝ) ^ m₁ := by
    have : (0 : ℝ) < (L : ℝ) ^ m₁ := by
      have : (0 : ℝ) < L := by exact_mod_cast hL1
      positivity
    exact div_nonneg D.Cx_nn this.le
  have hdd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hε3 : ε ^ 2 * d ≤ 1 / 1024 := by
    have h1 := rate_mul_le hd hε2
    have h2 : ε ≤ 1 / 32 := hε2.trans (agmonRate_le hd)
    have := mul_le_mul h2 h1 (mul_nonneg W.ε0 hdd) (by norm_num : (0 : ℝ) ≤ 1 / 32)
    calc ε ^ 2 * d = ε * (ε * d) := by ring
      _ ≤ 1 / 32 * (1 / 32) := this
      _ = 1 / 1024 := by norm_num
  have hδ2 : (Cx / (L : ℝ) ^ m₁) ^ 2 ≤ 1 := by nlinarith
  have hcoef : 32 * ε ^ 2 * d + 4 * d * (Cx / (L : ℝ) ^ m₁) ^ 2 ≤ 1 / 32 + 4 * d := by
    nlinarith [mul_nonneg hdd (by linarith : (0 : ℝ) ≤ 1 - (Cx / (L : ℝ) ^ m₁) ^ 2)]
  have hc0 : 0 ≤ 32 * ε ^ 2 * d + 4 * d * (Cx / (L : ℝ) ^ m₁) ^ 2 := by positivity
  calc _ ≤ _ := hg
    _ ≤ 8 * (16 * agmonSource H ε r (cD H q *ᵥ g)) + (1 / 32 + 4 * d) *
        (256 * agmonSource H ε r (cD H q *ᵥ g)) := by
        refine add_le_add (mul_le_mul_of_nonneg_left hE (by norm_num)) ?_
        exact mul_le_mul hcoef hWq hW0 (by positivity)
    _ = _ := by ring

theorem XData.dg2_grad (D : XData C H a aT ν x α κ s Cx) (W : XWeight H ε r) (f : H.Ω 1 → ℂ) :
    gradOn H ε r Finset.univ (Gsx C H a aT x ν α s *ᵥ f) ≤
      gradConstX d * Real.exp (N0 d L * κ) ^ 2 * agmonSource H ε r f := by
  rw [Gsx_mulVec]
  set g := (1 - Kcalx C H a aT x ν α s)⁻¹ *ᵥ f with hg
  have h1 := gradOn_Gstarx_le (ε := ε) (r := r) D g
  have h2 := D.neumann_src W f
  have h3 := sum_agmonSource_cD_le D.st ε r g
  have h4 : ∑ q ∈ C.cubeIdx, gradP C H q ε r (cubeGx H a aT x ν α q *ᵥ g) ≤
      (136 + 1024 * d) * ((3 * 5 ^ d : ℝ) * agmonSource H ε r g) := by
    calc _ ≤ ∑ q ∈ C.cubeIdx, (136 + 1024 * d) * agmonSource H ε r (cD H q *ᵥ g) :=
          Finset.sum_le_sum fun q hq => D.gradP_cube_le W hq g
      _ = (136 + 1024 * d) * ∑ q ∈ C.cubeIdx, agmonSource H ε r (cD H q *ᵥ g) := by
          rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left h3 (by positivity)
  have hE0 : 0 ≤ Real.exp (N0 d L * κ) ^ 2 := sq_nonneg _
  have hS0 := agmonSource_nonneg H ε r f
  calc _ ≤ _ := h1
    _ ≤ (2 * (3 * 5 ^ d) : ℝ) * (Real.exp (N0 d L * κ) ^ 2 *
        ((136 + 1024 * d) * ((3 * 5 ^ d : ℝ) * ((16 / 9) * agmonSource H ε r f)))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (h4.trans ?_) hE0)
          (by positivity)
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 (by positivity))
          (by positivity)
    _ = _ := by unfold gradConstX; ring

theorem XData.dg2_cwsq (D : XData C H a aT ν x α κ s Cx) (W : XWeight H ε r) (f : H.Ω 1 → ℂ) :
    cwsq H (agmonField H ε r (Gsx C H a aT x ν α s *ᵥ f)) ≤
      valConstX d * Real.exp (N0 d L * κ) ^ 2 * agmonSource H ε r f := by
  rw [Gsx_mulVec]
  have h1 := cwsq_Gstarx_le D W ((1 - Kcalx C H a aT x ν α s)⁻¹ *ᵥ f)
  have h2 := D.neumann_src W f
  have hE0 : 0 ≤ Real.exp (N0 d L * κ) ^ 2 := sq_nonneg _
  calc _ ≤ _ := h1
    _ ≤ 256 * (3 * 5 ^ d : ℝ) ^ 2 * Real.exp (N0 d L * κ) ^ 2 *
        ((16 / 9) * agmonSource H ε r f) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = _ := by unfold valConstX; ring


end Balaban.Localization.Dec2
