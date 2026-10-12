/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.DecoupledXGreen
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# (DG2): the weighted gradient of `G_{k,x,s} f`

For a cube `q` and `u = G^{(z)}_x c_z g` put `P_q = χ_q ũ`.  The Leibniz rule bounds the weighted
gradient of `P_q` by the retained energy of `w ũ`, its weighted `L²` norm and the cutoff gradient
`δ = C_χ / M₁`; the pieces of the decomposition `G*_{x,s} g = ∑_q s_q P_q` overlap at most
`2 · 3 · 5^d` times at a bond.

* `P_bond_bound`: the bond bound without the cut;
* `P_fwd_bound`, `P_bwd_bound`: with the cut (`P_q` vanishes at the endpoints of a removed bond);
* `gradP_le`: `Φ_q ≤ 8 E_q + (32 ε² d + 4 d δ²) W_q`;
* `XData.dg2_grad`: `‖w ∂ G_{k,x,s} f‖² ≤ B ‖ℓ w f‖²`.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Finset Matrix

variable {d L N₁ m₁ k : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} {a : ℕ → ℝ} {aT x ν : ℝ}
  {α : G.Ω 1 → ℂ}

section Bond

theorem chi_diff_le {q : ℕ × CTorus d L N₁ m₁ (k + 1)} {δ : ℝ}
    (hsm : IsSmoothField G δ (chiField G q)) (y : G.Ω 1) {b : CTorus d L N₁ m₁ (k + 1)}
    (hadj : Adj (y : CTorus d L N₁ m₁ (k + 1)) b) :
    |chi G q b - chi G q y| ≤ δ / G.spacing (y : CTorus d L N₁ m₁ (k + 1)) := by
  have key : ∀ z : CTorus d L N₁ m₁ (k + 1),
      vn (chiField G q z - chiField G q y) = |chi G q z - chi G q y| := by
    intro z
    have e : chiField G q z - chiField G q y = fun _ : Fin 1 => (((chi G q z - chi G q y : ℝ)) : ℂ) := by
      funext i; simp [chiField]
    rw [e, vn_const_one]
  obtain ⟨μ, h | h⟩ := hadj
  · rw [← key, h]; exact (hsm.grad y y.2 μ).1
  · have hb : b = (y : CTorus d L N₁ m₁ (k + 1)) - Pi.single μ 1 := eq_sub_of_add_eq h.symm
    rw [← key, hb]; exact (hsm.grad y y.2 μ).2

/-- **The bond bound for `P = χ ũ`** (no cut). -/
theorem P_bond_bound (S : XSetting G a aT ν) {q : ℕ × CTorus d L N₁ m₁ (k + 1)}
    (hq : q ∈ cubeIdx G) {δ : ℝ} (hsm : IsSmoothField G δ (chiField G q))
    {r : CTorus d L N₁ m₁ (k + 1) → ℝ} (hr : IsAgmonWeight G r) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ 1 / 2) (u : G.Ω 1 → ℂ) (y : G.Ω 1) {b : CTorus d L N₁ m₁ (k + 1)}
    (hadj : Adj (y : CTorus d L N₁ m₁ (k + 1)) b) :
    Real.exp (ε * r y) ^ 2 * ‖((chi G q b : ℝ) : ℂ) * zeroExt (G.Ω 1) u b -
        ((chi G q y : ℝ) : ℂ) * zeroExt (G.Ω 1) u y‖ ^ 2 ≤
      4 * ‖agmonField G ε r u b - agmonField G ε r u y‖ ^ 2 +
        16 * ε ^ 2 * (invSqSpacing G b * ‖agmonField G ε r u b‖ ^ 2) +
        2 * δ ^ 2 * (invSqSpacing G y * ‖agmonField G ε r u y‖ ^ 2) := by
  have hbond := agmon_bond_pointwise G hr hε0 hε1 u y.2 hadj
  have hw0 : 0 < Real.exp (ε * r y) := Real.exp_pos _
  have hsp : 0 < G.spacing (y : CTorus d L N₁ m₁ (k + 1)) := spacing_pos G
  have hinv : invSqSpacing G (y : CTorus d L N₁ m₁ (k + 1)) =
      (G.spacing (y : CTorus d L N₁ m₁ (k + 1)) ^ 2)⁻¹ := invSqSpacing_eq G y.2
  have hvy : ‖agmonField G ε r u y‖ = Real.exp (ε * r y) * ‖zeroExt (G.Ω 1) u y‖ :=
    norm_agmonField G ε r u y
  have hnn : 0 ≤ 8 * ε ^ 2 * (invSqSpacing G b * ‖agmonField G ε r u b‖ ^ 2) := by
    have := invSqSpacing_nonneg G b
    positivity
  by_cases hb : b ∈ G.Ω 1
  · have hc := chi_mem_Icc S hq ⟨b, hb⟩
    have hd := chi_diff_le hsm y hadj
    set ub := zeroExt (G.Ω 1) u b with hub
    set uy := zeroExt (G.Ω 1) u y with huy
    have hdec : ((chi G q b : ℝ) : ℂ) * ub - ((chi G q y : ℝ) : ℂ) * uy =
        ((chi G q b : ℝ) : ℂ) * (ub - uy) + uy * (((chi G q b - chi G q y : ℝ)) : ℂ) := by
      push_cast; ring
    have h1 : ‖((chi G q b : ℝ) : ℂ) * ub - ((chi G q y : ℝ) : ℂ) * uy‖ ≤
        ‖ub - uy‖ + ‖uy‖ * (δ / G.spacing (y : CTorus d L N₁ m₁ (k + 1))) := by
      rw [hdec]
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hc.1]
        calc chi G q b * ‖ub - uy‖ ≤ 1 * ‖ub - uy‖ :=
              mul_le_mul_of_nonneg_right hc.2 (norm_nonneg _)
          _ = _ := one_mul _
      · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left hd (norm_nonneg _)
    have h2 : ‖((chi G q b : ℝ) : ℂ) * ub - ((chi G q y : ℝ) : ℂ) * uy‖ ^ 2 ≤
        2 * ‖ub - uy‖ ^ 2 + 2 * (‖uy‖ * (δ / G.spacing (y : CTorus d L N₁ m₁ (k + 1)))) ^ 2 := by
      have h := pow_le_pow_left₀ (norm_nonneg _) h1 2
      nlinarith [sq_nonneg (‖ub - uy‖ - ‖uy‖ * (δ / G.spacing (y : CTorus d L N₁ m₁ (k + 1))))]
    have h3 : Real.exp (ε * r y) ^ 2 * (2 * (‖uy‖ * (δ / G.spacing (y : CTorus d L N₁ m₁ (k + 1)))) ^ 2) =
        2 * δ ^ 2 * (invSqSpacing G y * ‖agmonField G ε r u y‖ ^ 2) := by
      rw [hinv, hvy]
      field_simp
    calc Real.exp (ε * r y) ^ 2 * ‖((chi G q b : ℝ) : ℂ) * ub - ((chi G q y : ℝ) : ℂ) * uy‖ ^ 2
        ≤ Real.exp (ε * r y) ^ 2 * (2 * ‖ub - uy‖ ^ 2 +
          2 * (‖uy‖ * (δ / G.spacing (y : CTorus d L N₁ m₁ (k + 1)))) ^ 2) :=
          mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
      _ = 2 * (Real.exp (ε * r y) ^ 2 * ‖ub - uy‖ ^ 2) +
          2 * δ ^ 2 * (invSqSpacing G y * ‖agmonField G ε r u y‖ ^ 2) := by
          rw [← h3]; ring
      _ ≤ 2 * (2 * ‖agmonField G ε r u b - agmonField G ε r u y‖ ^ 2 +
          8 * ε ^ 2 * (invSqSpacing G b * ‖agmonField G ε r u b‖ ^ 2)) +
          2 * δ ^ 2 * (invSqSpacing G y * ‖agmonField G ε r u y‖ ^ 2) := by
          have := mul_le_mul_of_nonneg_left hbond (by norm_num : (0 : ℝ) ≤ 2)
          linarith
      _ = _ := by ring
  · have hub : zeroExt (G.Ω 1) u b = 0 := zeroExt_not_mem _ _ hb
    have hc := chi_mem_Icc S hq y
    rw [hub, mul_zero, zero_sub, norm_neg, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg hc.1, mul_pow]
    rw [hub, zero_sub, norm_neg] at hbond
    have h1 : Real.exp (ε * r y) ^ 2 * (chi G q y ^ 2 * ‖zeroExt (G.Ω 1) u y‖ ^ 2) ≤
        Real.exp (ε * r y) ^ 2 * ‖zeroExt (G.Ω 1) u y‖ ^ 2 := by
      have : chi G q y ^ 2 ≤ 1 := by nlinarith [hc.1, hc.2]
      calc _ ≤ Real.exp (ε * r y) ^ 2 * (1 * ‖zeroExt (G.Ω 1) u y‖ ^ 2) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right this (sq_nonneg _))
              (sq_nonneg _)
        _ = _ := by ring
    have hv : agmonField G ε r u b = 0 := by
      unfold agmonField; rw [hub]; simp
    rw [hv, zero_sub, norm_neg]
    have h00 : 0 ≤ 2 * δ ^ 2 * (invSqSpacing G y * ‖agmonField G ε r u y‖ ^ 2) := by
      have := invSqSpacing_nonneg G (y : CTorus d L N₁ m₁ (k + 1))
      positivity
    have hvy2 : ‖agmonField G ε r u y‖ ^ 2 = Real.exp (ε * r y) ^ 2 *
        ‖zeroExt (G.Ω 1) u y‖ ^ 2 := by rw [hvy]; ring
    rw [← hvy2] at h1
    simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
      add_zero]
    nlinarith

end Bond


/-! ### The cutoff piece `P_q = χ_q ũ_q` and the removed bonds -/

section Cut

/-- `P_q = χ_q ũ` as a field on the torus. -/
noncomputable def Pq (G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ)
    (q : ℕ × CTorus d L N₁ m₁ (k + 1)) (u : G.Ω 1 → ℂ) (z : CTorus d L N₁ m₁ (k + 1)) : ℂ :=
  ((chi G q z : ℝ) : ℂ) * zeroExt (G.Ω 1) u z

theorem Pq_eq_zero_of_not_inner (S : XSetting G a aT ν) {q : ℕ × CTorus d L N₁ m₁ (k + 1)}
    (hq : q ∈ cubeIdx G) (u : G.Ω 1 → ℂ) {z : CTorus d L N₁ m₁ (k + 1)} (hz : ¬ Inner q z) :
    Pq G q u z = 0 := by
  unfold Pq
  by_cases hzΩ : z ∈ G.Ω 1
  · have : chi G q z = 0 := by
      by_contra h; exact hz (inner_of_chi_ne_zero S.dg hq hzΩ h)
    simp [this]
  · rw [zeroExt_not_mem _ _ hzΩ]; simp

theorem Pq_ne_zero (S : XSetting G a aT ν) (hα : AdmPot G α) (hx : 0 ≤ x)
    {q : ℕ × CTorus d L N₁ m₁ (k + 1)} (hq : q ∈ cubeIdx G) (g : G.Ω 1 → ℂ)
    {z : CTorus d L N₁ m₁ (k + 1)}
    (h : Pq G q (cubeGx G a aT x ν α q *ᵥ g) z ≠ 0) : z ∈ G.Ω 1 ∧ z ∈ intBox q := by
  unfold Pq at h
  have hz : zeroExt (G.Ω 1) (cubeGx G a aT x ν α q *ᵥ g) z ≠ 0 := right_ne_zero_of_mul h
  by_cases hzΩ : z ∈ G.Ω 1
  · refine ⟨hzΩ, ?_⟩
    by_contra hb
    apply hz
    rw [zeroExt_mem' _ hzΩ]
    exact cubeGx_supp S hα hx hq g ⟨z, hzΩ⟩ hb
  · exact absurd (zeroExt_not_mem _ _ hzΩ) hz

variable {δ : ℝ} {r : CTorus d L N₁ m₁ (k + 1) → ℝ} {ε : ℝ}

theorem P_fwd_bound (S : XSetting G a aT ν) {q : ℕ × CTorus d L N₁ m₁ (k + 1)}
    (hq : q ∈ cubeIdx G) (hsm : IsSmoothField G δ (chiField G q)) (hr : IsAgmonWeight G r)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 2) (u : G.Ω 1 → ℂ) (y : G.Ω 1) (μ : Fin d) :
    Real.exp (ε * r y) ^ 2 * ‖Pq G q u ((y : CTorus d L N₁ m₁ (k + 1)) + Pi.single μ 1) -
        Pq G q u y‖ ^ 2 ≤
      4 * (if ((y : CTorus d L N₁ m₁ (k + 1)), μ) ∈ cubeCut G (intBox q) then 0 else
          ‖agmonField G ε r u ((y : CTorus d L N₁ m₁ (k + 1)) + Pi.single μ 1) -
            agmonField G ε r u y‖ ^ 2) +
        16 * ε ^ 2 * (invSqSpacing G ((y : CTorus d L N₁ m₁ (k + 1)) + Pi.single μ 1) *
          ‖agmonField G ε r u ((y : CTorus d L N₁ m₁ (k + 1)) + Pi.single μ 1)‖ ^ 2) +
        2 * δ ^ 2 * (invSqSpacing G y * ‖agmonField G ε r u y‖ ^ 2) := by
  have hinv1 := invSqSpacing_nonneg G ((y : CTorus d L N₁ m₁ (k + 1)) + Pi.single μ 1)
  have hinv2 := invSqSpacing_nonneg G (y : CTorus d L N₁ m₁ (k + 1))
  by_cases hc : ((y : CTorus d L N₁ m₁ (k + 1)), μ) ∈ cubeCut G (intBox q)
  · have hy : ¬ Inner q (y : CTorus d L N₁ m₁ (k + 1)) := fun h => (h.noCut μ).1 hc
    have hb : ¬ Inner q ((y : CTorus d L N₁ m₁ (k + 1)) + Pi.single μ 1) := fun h =>
      (h.noCut μ).2 (by simpa using hc)
    rw [Pq_eq_zero_of_not_inner S hq u hy, Pq_eq_zero_of_not_inner S hq u hb]
    simp only [hc, ↓reduceIte, sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, mul_zero, zero_add, mul_zero]
    positivity
  · simp only [hc, ↓reduceIte]
    exact P_bond_bound S hq hsm hr hε0 hε1 u y ⟨μ, Or.inl rfl⟩

theorem P_bwd_bound (S : XSetting G a aT ν) {q : ℕ × CTorus d L N₁ m₁ (k + 1)}
    (hq : q ∈ cubeIdx G) (hsm : IsSmoothField G δ (chiField G q)) (hr : IsAgmonWeight G r)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 2) (u : G.Ω 1 → ℂ) (y : G.Ω 1) (μ : Fin d) :
    Real.exp (ε * r y) ^ 2 * ‖Pq G q u ((y : CTorus d L N₁ m₁ (k + 1)) - Pi.single μ 1) -
        Pq G q u y‖ ^ 2 ≤
      4 * (if ((y : CTorus d L N₁ m₁ (k + 1)) - Pi.single μ 1, μ) ∈ cubeCut G (intBox q) then 0
          else ‖agmonField G ε r u ((y : CTorus d L N₁ m₁ (k + 1)) - Pi.single μ 1) -
            agmonField G ε r u y‖ ^ 2) +
        16 * ε ^ 2 * (invSqSpacing G ((y : CTorus d L N₁ m₁ (k + 1)) - Pi.single μ 1) *
          ‖agmonField G ε r u ((y : CTorus d L N₁ m₁ (k + 1)) - Pi.single μ 1)‖ ^ 2) +
        2 * δ ^ 2 * (invSqSpacing G y * ‖agmonField G ε r u y‖ ^ 2) := by
  have hinv1 := invSqSpacing_nonneg G ((y : CTorus d L N₁ m₁ (k + 1)) - Pi.single μ 1)
  have hinv2 := invSqSpacing_nonneg G (y : CTorus d L N₁ m₁ (k + 1))
  by_cases hc : ((y : CTorus d L N₁ m₁ (k + 1)) - Pi.single μ 1, μ) ∈ cubeCut G (intBox q)
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
noncomputable def gradP (G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ)
    (q : ℕ × CTorus d L N₁ m₁ (k + 1)) (ε : ℝ) (r : CTorus d L N₁ m₁ (k + 1) → ℝ)
    (u : G.Ω 1 → ℂ) : ℝ :=
  ∑ y ∈ G.Ω 1, ∑ μ : Fin d, Real.exp (ε * r y) ^ 2 *
    (‖Pq G q u ((y : CTorus d L N₁ m₁ (k + 1)) + Pi.single μ 1) - Pq G q u y‖ ^ 2 +
      ‖Pq G q u ((y : CTorus d L N₁ m₁ (k + 1)) - Pi.single μ 1) - Pq G q u y‖ ^ 2)

/-- **The gradient of `χ_q ũ_q`**: `Φ_q ≤ 8 E_q + (32 ε² d + 4 d δ²) W_q`. -/
theorem gradP_le (S : XSetting G a aT ν) {q : ℕ × CTorus d L N₁ m₁ (k + 1)}
    (hq : q ∈ cubeIdx G) (hsm : IsSmoothField G δ (chiField G q)) (hr : IsAgmonWeight G r)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 2) (u : G.Ω 1 → ℂ) :
    gradP G q ε r u ≤ 8 * cutEnergy (cubeCut G (intBox q)) (agmonField G ε r u) +
      (32 * ε ^ 2 * d + 4 * d * δ ^ 2) * cwsq G (agmonField G ε r u) := by
  classical
  set v := agmonField G ε r u with hv
  set cut := cubeCut G (intBox q) with hcut
  set T₁ : CTorus d L N₁ m₁ (k + 1) → Fin d → ℝ := fun y μ =>
      4 * (if (y, μ) ∈ cut then 0 else ‖v (y + Pi.single μ 1) - v y‖ ^ 2) +
        16 * ε ^ 2 * (invSqSpacing G (y + Pi.single μ 1) * ‖v (y + Pi.single μ 1)‖ ^ 2) with hT₁
  set T₂ : CTorus d L N₁ m₁ (k + 1) → Fin d → ℝ := fun y μ =>
      4 * (if (y - Pi.single μ 1, μ) ∈ cut then 0 else ‖v (y - Pi.single μ 1) - v y‖ ^ 2) +
        16 * ε ^ 2 * (invSqSpacing G (y - Pi.single μ 1) * ‖v (y - Pi.single μ 1)‖ ^ 2) with hT₂
  set B : CTorus d L N₁ m₁ (k + 1) → ℝ := fun y => ∑ μ : Fin d, (T₁ y μ + T₂ y μ) +
      4 * d * δ ^ 2 * (invSqSpacing G y * ‖v y‖ ^ 2) with hB
  have hT0 : ∀ y μ, 0 ≤ T₁ y μ + T₂ y μ := fun y μ => by
    have h1 := invSqSpacing_nonneg G (y + Pi.single μ 1)
    have h2 := invSqSpacing_nonneg G (y - Pi.single μ 1)
    have h3 : 0 ≤ (if (y, μ) ∈ cut then (0 : ℝ) else ‖v (y + Pi.single μ 1) - v y‖ ^ 2) := by
      split_ifs <;> positivity
    have h4 : 0 ≤ (if (y - Pi.single μ 1, μ) ∈ cut then (0 : ℝ) else
        ‖v (y - Pi.single μ 1) - v y‖ ^ 2) := by
      split_ifs <;> positivity
    simp only [hT₁, hT₂]
    positivity
  have hB0 : ∀ y, 0 ≤ B y := fun y => by
    have h5 := invSqSpacing_nonneg G y
    simp only [hB]
    have := Finset.sum_nonneg fun μ (_ : μ ∈ (Finset.univ : Finset (Fin d))) => hT0 y μ
    positivity
  have hpt : ∀ y ∈ G.Ω 1, ∑ μ : Fin d, Real.exp (ε * r y) ^ 2 *
      (‖Pq G q u ((y : CTorus d L N₁ m₁ (k + 1)) + Pi.single μ 1) - Pq G q u y‖ ^ 2 +
        ‖Pq G q u ((y : CTorus d L N₁ m₁ (k + 1)) - Pi.single μ 1) - Pq G q u y‖ ^ 2) ≤
      B y := by
    intro y hy
    have hμ : ∑ μ : Fin d, ((T₁ y μ + 2 * δ ^ 2 * (invSqSpacing G y * ‖v y‖ ^ 2)) +
        (T₂ y μ + 2 * δ ^ 2 * (invSqSpacing G y * ‖v y‖ ^ 2))) = B y := by
      have : ∀ μ : Fin d, ((T₁ y μ + 2 * δ ^ 2 * (invSqSpacing G y * ‖v y‖ ^ 2)) +
          (T₂ y μ + 2 * δ ^ 2 * (invSqSpacing G y * ‖v y‖ ^ 2))) =
          (T₁ y μ + T₂ y μ) + 4 * δ ^ 2 * (invSqSpacing G y * ‖v y‖ ^ 2) := fun μ => by ring
      simp only [this, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, hB]
      ring
    rw [← hμ]
    refine Finset.sum_le_sum fun μ _ => ?_
    have h1 := P_fwd_bound S hq hsm hr hε0 hε1 u ⟨y, hy⟩ μ
    have h2 := P_bwd_bound S hq hsm hr hε0 hε1 u ⟨y, hy⟩ μ
    rw [mul_add]
    exact add_le_add h1 h2
  have hsum : gradP G q ε r u ≤ ∑ y, B y := by
    calc gradP G q ε r u ≤ ∑ y ∈ G.Ω 1, B y := Finset.sum_le_sum fun y hy => hpt y hy
      _ ≤ ∑ y, B y := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          fun y _ _ => hB0 y
  have hBsum : ∑ y, B y = 8 * cutEnergy cut v + (32 * ε ^ 2 * d + 4 * d * δ ^ 2) * cwsq G v := by
    have e1 : ∑ y : CTorus d L N₁ m₁ (k + 1), ∑ μ : Fin d,
        (if (y, μ) ∈ cut then 0 else ‖v (y + Pi.single μ 1) - v y‖ ^ 2) = cutEnergy cut v := rfl
    have e2 := sum_shift_cutEnergy_back cut v
    have e3 := sum_shift_cwsq G v
    have e4 := sum_shift_cwsq_back G v
    have hS1 : ∑ y : CTorus d L N₁ m₁ (k + 1), ∑ μ : Fin d, T₁ y μ =
        4 * cutEnergy cut v + 16 * ε ^ 2 * (d * cwsq G v) := by
      simp only [hT₁, Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [e1, e3]
    have hS2 : ∑ y : CTorus d L N₁ m₁ (k + 1), ∑ μ : Fin d, T₂ y μ =
        4 * cutEnergy cut v + 16 * ε ^ 2 * (d * cwsq G v) := by
      simp only [hT₂, Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [e2, e4]
    simp only [hB, Finset.sum_add_distrib]
    rw [hS1, hS2]
    have : ∑ y : CTorus d L N₁ m₁ (k + 1), 4 * d * δ ^ 2 * (invSqSpacing G y * ‖v y‖ ^ 2) =
        4 * d * δ ^ 2 * cwsq G v := by
      rw [← Finset.mul_sum]; rfl
    rw [this]
    ring
  rw [hBsum] at hsum
  exact hsum

end Cut

end Balaban.Localization
