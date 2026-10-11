/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Background.Weights
public import Balaban.Background.BumpMixed
public import Balaban.Background.Interpolation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# Mixed second differences of the weights and of the interpolated vector

For a site `y` of layer `n ≥ 3` and the unit square `y, y + e_μ, y + e_ν, y + e_μ + e_ν`
(all four corners lie in layers `≥ n - 1 ≥ 2`):

* `sq_layers`: the layers of the corners;
* `supp4`: the blocks active at some corner; its cardinality is at most `12 · 3^d` and its layers
  are in `[n - 1, n + 1]`;
* `weight_sq`: the mixed second difference of every weight is at most `H_m / ℓ(y)²`, `ℓ(y) = L^n`;
* `interp_sq_le`: the mixed second difference of `interp G Φ` against a reference `ref`.
-/

@[expose] public section

namespace Balaban.Background

open Balaban.Multiscale Finset

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

omit [NeZero N₀] [NeZero L] in
theorem adj_add_add_left (x : Torus d (N₀ * L ^ k)) (μ ν : Fin d) :
    Adj (x + Pi.single μ 1) (x + Pi.single μ 1 + Pi.single ν 1) := adj_add _ ν

omit [NeZero N₀] [NeZero L] in
theorem adj_add_add_right (x : Torus d (N₀ * L ^ k)) (μ ν : Fin d) :
    Adj (x + Pi.single ν 1) (x + Pi.single μ 1 + Pi.single ν 1) := by
  rw [add_right_comm]; exact adj_add _ μ

theorem torusDist_sq_le (x : Torus d (N₀ * L ^ k)) (μ ν : Fin d) :
    Green.torusDist d (N₀ * L ^ k) x (x + Pi.single μ 1 + Pi.single ν 1) ≤ 2 := by
  have h1 := (adj_add x μ).torusDist_le
  have h2 := (adj_add_add_left x μ ν).torusDist_le
  have := Green.torusDist_triangle_gen x (x + Pi.single μ 1) (x + Pi.single μ 1 + Pi.single ν 1)
  linarith

section Geometry

variable (G : GeneratingSet d L N₀ k ϱ)

/-- Layers of adjacent sites differ by at most one. -/
theorem layer_adj_bounds (hϱ : (4 * d * L : ℝ) ≤ ϱ) (hd : 1 ≤ d) (hL : 1 ≤ L) {n n' : ℕ}
    (hn1 : 1 ≤ n) (hnk : n ≤ k) (hn1' : 1 ≤ n') (hnk' : n' ≤ k) {x x' : Torus d (N₀ * L ^ k)}
    (hx : x ∈ G.layer n) (hx' : x' ∈ G.layer n') (h : Adj x x') : n ≤ n' + 1 ∧ n' ≤ n + 1 := by
  have a1 : x ∈ G.Ω 1 := G.layer_subset hn1 hnk hx
  have a2 : x' ∈ G.Ω 1 := G.layer_subset hn1' hnk' hx'
  have := layerIndex_le_succ_of_adj G hϱ hd hL a1 a2 h
  have := layerIndex_le_succ_of_adj G hϱ hd hL a2 a1 h.symm
  rw [G.layerIndex_eq hn1 hnk hx, G.layerIndex_eq hn1' hnk' hx'] at *
  omega

/-- The layer of the corner `x + e_μ + e_ν` of a square at a site of layer `n ≥ 3`. -/
theorem layer_corner (hϱ : (4 * d * L : ℝ) ≤ ϱ) (hd : 1 ≤ d) (hL : 1 ≤ L) {n : ℕ} (hn3 : 3 ≤ n)
    (hnk : n ≤ k) {y : Torus d (N₀ * L ^ k)} (hy : y ∈ G.layer n) (μ ν : Fin d) :
    ∃ n', 2 ≤ n' ∧ n' ≤ k ∧ y + Pi.single μ 1 + Pi.single ν 1 ∈ G.layer n' ∧
      n ≤ n' + 1 ∧ n' ≤ n + 1 := by
  obtain ⟨n₁, h11, h1k, hy₁⟩ := exists_layer_adj G hϱ hd hL (by omega) hnk hy (adj_add y μ)
  obtain ⟨b1, b2⟩ := layer_adj_bounds G hϱ hd hL (by omega) hnk h11 h1k hy hy₁ (adj_add y μ)
  obtain ⟨n₂, h21, h2k, hy₂⟩ := exists_layer_adj G hϱ hd hL (by omega) h1k hy₁
    (adj_add_add_left y μ ν)
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hp : (1 : ℝ) ≤ (L : ℝ) ^ n₂ := one_le_pow₀ hL'
  have hdist := torusDist_sq_le y μ ν
  obtain ⟨c1, c2⟩ := layer_bounds_of_dist G hϱ h21 h2k (by omega) hnk hy hy₂
    (by nlinarith) hL
  exact ⟨n₂, by omega, h2k, hy₂, c1, c2⟩

/-- The layer of the corner `x + e_μ` (any direction), `n ≥ 3`. -/
theorem layer_edge (hϱ : (4 * d * L : ℝ) ≤ ϱ) (hd : 1 ≤ d) (hL : 1 ≤ L) {n : ℕ} (hn3 : 3 ≤ n)
    (hnk : n ≤ k) {y : Torus d (N₀ * L ^ k)} (hy : y ∈ G.layer n) (μ : Fin d) :
    ∃ n', 2 ≤ n' ∧ n' ≤ k ∧ y + Pi.single μ 1 ∈ G.layer n' ∧ n ≤ n' + 1 ∧ n' ≤ n + 1 := by
  obtain ⟨n₁, h11, h1k, hy₁⟩ := exists_layer_adj G hϱ hd hL (by omega) hnk hy (adj_add y μ)
  obtain ⟨b1, b2⟩ := layer_adj_bounds G hϱ hd hL (by omega) hnk h11 h1k hy hy₁ (adj_add y μ)
  exact ⟨n₁, by omega, h1k, hy₁, b1, b2⟩

/-- A block active at the corner `x + e_μ + e_ν`, for `x` of layer `n`, has layer in
`[n - 1, n + 1]`. -/
theorem active_layer_bounds_sq (hϱ : (4 * d * L : ℝ) ≤ ϱ) (hd : 1 ≤ d) (hL : 1 ≤ L) {n : ℕ}
    (hn1 : 1 ≤ n) (hnk : n ≤ k) {y : Torus d (N₀ * L ^ k)} (hy : y ∈ G.layer n) (μ ν : Fin d)
    {q : ℕ × Torus d (N₀ * L ^ k)} (hq : q ∈ active G (y + Pi.single μ 1 + Pi.single ν 1)) :
    n ≤ q.1 + 1 ∧ q.1 ≤ n + 1 := by
  obtain ⟨hqi, hne⟩ := (mem_active G).1 hq
  obtain ⟨⟨hm1, hmk⟩, -, -⟩ := (mem_blockIdx G).1 hqi
  obtain ⟨z, hz, hdz⟩ := active_dist G hqi hne
  have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have h1 : (1 : ℝ) ≤ (L : ℝ) ^ q.1 := one_le_pow₀ hL'
  have htri := Green.torusDist_triangle_gen y (y + Pi.single μ 1 + Pi.single ν 1) z
  have h2 := torusDist_sq_le y μ ν
  refine layer_bounds_of_dist G hϱ hm1 hmk hn1 hnk hy hz (htri.trans ?_) hL
  nlinarith

open Classical in
/-- The blocks whose bump is nonzero at one of the four corners of the unit square at `y`. -/
noncomputable def supp4 (y : Torus d (N₀ * L ^ k)) (μ ν : Fin d) :
    Finset (ℕ × Torus d (N₀ * L ^ k)) :=
  active G y ∪ active G (y + Pi.single μ 1) ∪ active G (y + Pi.single ν 1) ∪
    active G (y + Pi.single μ 1 + Pi.single ν 1)

theorem supp4_subset (y : Torus d (N₀ * L ^ k)) (μ ν : Fin d) : supp4 G y μ ν ⊆ blockIdx G := by
  intro q hq
  simp only [supp4, Finset.mem_union] at hq
  rcases hq with ((h | h) | h) | h <;> exact ((mem_active G).1 h).1

theorem not_mem_supp4 {y : Torus d (N₀ * L ^ k)} {μ ν : Fin d} {q : ℕ × Torus d (N₀ * L ^ k)}
    (hq : q ∈ blockIdx G) (h : q ∉ supp4 G y μ ν) :
    bump q.1 q.2 y = 0 ∧ bump q.1 q.2 (y + Pi.single μ 1) = 0 ∧
      bump q.1 q.2 (y + Pi.single ν 1) = 0 ∧
      bump q.1 q.2 (y + Pi.single μ 1 + Pi.single ν 1) = 0 := by
  simp only [supp4, Finset.mem_union, not_or] at h
  exact ⟨bump_eq_zero_of_not_active G hq h.1.1.1, bump_eq_zero_of_not_active G hq h.1.1.2,
    bump_eq_zero_of_not_active G hq h.1.2, bump_eq_zero_of_not_active G hq h.2⟩

theorem card_supp4_le (hϱ : (4 * d * L : ℝ) ≤ ϱ) (hd : 1 ≤ d) (hL : 1 ≤ L) {n : ℕ} (hn3 : 3 ≤ n)
    (hnk : n ≤ k) {y : Torus d (N₀ * L ^ k)} (hy : y ∈ G.layer n) (μ ν : Fin d) :
    (supp4 G y μ ν).card ≤ 12 * 3 ^ d := by
  obtain ⟨n₁, h21, h1k, hy₁⟩ := exists_layer_adj G hϱ hd hL (by omega) hnk hy (adj_add y μ)
  have c1 := card_active_le G hϱ hd hL (by omega) hnk hy (torusDist_self_le y)
  have c2 := card_active_le G hϱ hd hL (by omega) hnk hy (adj_add y μ).torusDist_le
  have c3 := card_active_le G hϱ hd hL (by omega) hnk hy (adj_add y ν).torusDist_le
  have c4 := card_active_le G hϱ hd hL (by omega) h1k hy₁ (adj_add_add_left y μ ν).torusDist_le
  unfold supp4
  have u1 := card_union_le (active G y) (active G (y + Pi.single μ 1))
  have u2 := card_union_le (active G y ∪ active G (y + Pi.single μ 1))
    (active G (y + Pi.single ν 1))
  have u3 := card_union_le (active G y ∪ active G (y + Pi.single μ 1) ∪
    active G (y + Pi.single ν 1)) (active G (y + Pi.single μ 1 + Pi.single ν 1))
  omega

theorem supp4_layer_bounds (hϱ : (4 * d * L : ℝ) ≤ ϱ) (hd : 1 ≤ d) (hL : 1 ≤ L) {n : ℕ}
    (hn1 : 1 ≤ n) (hnk : n ≤ k) {y : Torus d (N₀ * L ^ k)} (hy : y ∈ G.layer n) (μ ν : Fin d)
    {q : ℕ × Torus d (N₀ * L ^ k)} (hq : q ∈ supp4 G y μ ν) : n ≤ q.1 + 1 ∧ q.1 ≤ n + 1 := by
  simp only [supp4, Finset.mem_union] at hq
  rcases hq with ((h | h) | h) | h
  · exact active_layer_bounds G hϱ hd hL hn1 hnk hy (torusDist_self_le y) h
  · exact active_layer_bounds G hϱ hd hL hn1 hnk hy (adj_add y μ).torusDist_le h
  · exact active_layer_bounds G hϱ hd hL hn1 hnk hy (adj_add y ν).torusDist_le h
  · exact active_layer_bounds_sq G hϱ hd hL hn1 hnk hy μ ν h

end Geometry

section Alg

/-- Algebra of the mixed second difference of a quotient `b / D`. -/
theorem weight_mixed_alg {b00 b10 b01 b11 D00 D10 D01 D11 q0 B1 U1 B2 V : ℝ} (hq0 : 0 < q0)
    (h00 : q0 ≤ D00) (h10 : q0 ≤ D10) (h01 : q0 ≤ D01) (h11 : q0 ≤ D11)
    (hb00 : 0 ≤ b00) (hbD00 : b00 ≤ D00)
    (hB10 : |b10 - b00| ≤ B1) (hB01 : |b01 - b00| ≤ B1) (hB11 : |b11 - b00| ≤ B1)
    (hU10 : |D10 - D00| ≤ U1) (hU01 : |D01 - D00| ≤ U1) (hU11 : |D11 - D00| ≤ U1)
    (hB2 : |b11 - b10 - b01 + b00| ≤ B2) (hV : |D11 - D10 - D01 + D00| ≤ V) :
    |b11 / D11 - b10 / D10 - b01 / D01 + b00 / D00| ≤
      (B2 + V + 3 * ((B1 + U1) / q0) * U1) / q0 := by
  have hD00 : 0 < D00 := lt_of_lt_of_le hq0 h00
  have hD10 : 0 < D10 := lt_of_lt_of_le hq0 h10
  have hD01 : 0 < D01 := lt_of_lt_of_le hq0 h01
  have hD11 : 0 < D11 := lt_of_lt_of_le hq0 h11
  have s10 := weight_step hq0 h10 h00 hb00 hbD00 hB10 hU10
  have s01 := weight_step hq0 h01 h00 hb00 hbD00 hB01 hU01
  have s11 := weight_step hq0 h11 h00 hb00 hbD00 hB11 hU11
  have hw0 : 0 ≤ b00 / D00 := div_nonneg hb00 hD00.le
  have hw1 : b00 / D00 ≤ 1 := (div_le_one hD00).2 hbD00
  have e11 : b11 = b11 / D11 * D11 := by field_simp
  have e10 : b10 = b10 / D10 * D10 := by field_simp
  have e01 : b01 = b01 / D01 * D01 := by field_simp
  have e00 : b00 = b00 / D00 * D00 := by field_simp
  set w00 := b00 / D00
  set w10 := b10 / D10
  set w01 := b01 / D01
  set w11 := b11 / D11
  have hid : D00 * (w11 - w10 - w01 + w00) = (b11 - b10 - b01 + b00) -
      w00 * (D11 - D10 - D01 + D00) - ((D11 - D00) * (w11 - w00) -
        (D10 - D00) * (w10 - w00) - (D01 - D00) * (w01 - w00)) := by
    linear_combination (-1 : ℝ) * e11 + e10 + e01 - e00
  have hH0 : 0 ≤ (B1 + U1) / q0 := by
    have : 0 ≤ B1 := (abs_nonneg _).trans hB10
    have : 0 ≤ U1 := (abs_nonneg _).trans hU10
    positivity
  have hU0 : 0 ≤ U1 := (abs_nonneg _).trans hU10
  have a1 : |w00 * (D11 - D10 - D01 + D00)| ≤ V := by
    rw [abs_mul, abs_of_nonneg hw0]
    calc w00 * |D11 - D10 - D01 + D00| ≤ 1 * V :=
          mul_le_mul hw1 hV (abs_nonneg _) zero_le_one
      _ = V := one_mul V
  have a2 : ∀ (g o : ℝ), |g| ≤ U1 → |o| ≤ (B1 + U1) / q0 → |g * o| ≤ U1 * ((B1 + U1) / q0) :=
    fun g o hg ho => by
      rw [abs_mul]; exact mul_le_mul hg ho (abs_nonneg _) hU0
  have a11 := a2 (D11 - D00) (w11 - w00) hU11 s11
  have a10 := a2 (D10 - D00) (w10 - w00) hU10 s10
  have a01 := a2 (D01 - D00) (w01 - w00) hU01 s01
  have h1 : |D00 * (w11 - w10 - w01 + w00)| ≤ B2 + V + 3 * ((B1 + U1) / q0) * U1 := by
    rw [hid]
    have t1 := abs_sub (b11 - b10 - b01 + b00) (w00 * (D11 - D10 - D01 + D00))
    have t2 := abs_sub (b11 - b10 - b01 + b00 - w00 * (D11 - D10 - D01 + D00))
      ((D11 - D00) * (w11 - w00) - (D10 - D00) * (w10 - w00) - (D01 - D00) * (w01 - w00))
    have t3 := abs_sub ((D11 - D00) * (w11 - w00) - (D10 - D00) * (w10 - w00))
      ((D01 - D00) * (w01 - w00))
    have t4 := abs_sub ((D11 - D00) * (w11 - w00)) ((D10 - D00) * (w10 - w00))
    nlinarith
  rw [abs_mul, abs_of_pos hD00] at h1
  rw [le_div_iff₀ hq0]
  nlinarith [abs_nonneg (w11 - w10 - w01 + w00)]

end Alg

/-- Constants of the mixed differences of bumps, denominators and weights. -/
noncomputable def wc1 (d L : ℕ) : ℝ := 2 * wb1 d * L
noncomputable def wcU (d L : ℕ) : ℝ := 12 * 3 ^ d * wc1 d L
noncomputable def wcB (d L : ℕ) : ℝ := 22500 * 4 ^ d * (L : ℝ) ^ 2
noncomputable def wcV (d L : ℕ) : ℝ := 12 * 3 ^ d * wcB d L
noncomputable def wcH (d L : ℕ) : ℝ := (wc1 d L + wcU d L) / (1 / 2 : ℝ) ^ d
noncomputable def wcM (d L : ℕ) : ℝ :=
  (wcB d L + wcV d L + 3 * wcH d L * wcU d L) / (1 / 2 : ℝ) ^ d

theorem wc1_nonneg (d L : ℕ) : 0 ≤ wc1 d L := by unfold wc1; have := wb1_nonneg d; positivity
theorem wcU_nonneg (d L : ℕ) : 0 ≤ wcU d L := by unfold wcU; have := wc1_nonneg d L; positivity
theorem wcB_nonneg (d L : ℕ) : 0 ≤ wcB d L := by unfold wcB; positivity
theorem wcV_nonneg (d L : ℕ) : 0 ≤ wcV d L := by unfold wcV; have := wcB_nonneg d L; positivity
theorem wcH_nonneg (d L : ℕ) : 0 ≤ wcH d L := by
  unfold wcH; have := wc1_nonneg d L; have := wcU_nonneg d L; positivity
theorem wcM_nonneg (d L : ℕ) : 0 ≤ wcM d L := by
  unfold wcM; have := wcB_nonneg d L; have := wcV_nonneg d L; have := wcH_nonneg d L
  have := wcU_nonneg d L; positivity

section Quotient

variable (G : GeneratingSet d L N₀ k ϱ)

/-- Differences of a bump of a block active somewhere on the square. -/
theorem bump_sq_supp (hϱ : (4 * d * L : ℝ) ≤ ϱ) (hd : 1 ≤ d) (hL : 2 ≤ L) {n : ℕ} (hn3 : 3 ≤ n)
    (hnk : n ≤ k) {y : Torus d (N₀ * L ^ k)} (hy : y ∈ G.layer n) (μ ν : Fin d)
    {q : ℕ × Torus d (N₀ * L ^ k)} (hq : q ∈ supp4 G y μ ν) :
    |bump q.1 q.2 (y + Pi.single μ 1) - bump q.1 q.2 y| ≤ wc1 d L / (L : ℝ) ^ n ∧
    |bump q.1 q.2 (y + Pi.single ν 1) - bump q.1 q.2 y| ≤ wc1 d L / (L : ℝ) ^ n ∧
    |bump q.1 q.2 (y + Pi.single μ 1 + Pi.single ν 1) - bump q.1 q.2 y| ≤
      wc1 d L / (L : ℝ) ^ n ∧
    |bump q.1 q.2 (y + Pi.single μ 1 + Pi.single ν 1) - bump q.1 q.2 (y + Pi.single μ 1) -
        bump q.1 q.2 (y + Pi.single ν 1) + bump q.1 q.2 y| ≤
      wcB d L / ((L : ℝ) ^ n) ^ 2 := by
  have hbl := supp4_layer_bounds G hϱ hd (by omega) (by omega) hnk hy μ ν hq
  obtain ⟨⟨hm1, hmk⟩, -, -⟩ := (mem_blockIdx G).1 (supp4_subset G y μ ν hq)
  have hlam : 2 ≤ L ^ q.1 := by
    calc 2 ≤ L := hL
      _ = L ^ 1 := (pow_one L).symm
      _ ≤ L ^ q.1 := Nat.pow_le_pow_right (by omega) hm1
  have hs := scale_ge hbl.1 (by omega : 1 ≤ L)
  have hLm : (0 : ℝ) < (L : ℝ) ^ q.1 := by
    have : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
    positivity
  have hLn : (0 : ℝ) < (L : ℝ) ^ n := by
    have : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
    positivity
  have key1 : 150 * (4 : ℝ) ^ d / (L : ℝ) ^ q.1 ≤ wb1 d * L / (L : ℝ) ^ n := by
    unfold wb1
    rw [div_le_div_iff₀ hLm hLn]
    have : (0 : ℝ) ≤ 150 * 4 ^ d := by positivity
    nlinarith
  have key1' : wb1 d * L / (L : ℝ) ^ n ≤ wc1 d L / (L : ℝ) ^ n := by
    refine div_le_div_of_nonneg_right ?_ hLn.le
    unfold wc1; have := wb1_nonneg d; have : (0 : ℝ) ≤ L := Nat.cast_nonneg L; nlinarith
  have key2 : 22500 * (4 : ℝ) ^ d / ((L : ℝ) ^ q.1) ^ 2 ≤ wcB d L / ((L : ℝ) ^ n) ^ 2 := by
    unfold wcB
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : (0 : ℝ) ≤ 22500 * 4 ^ d := by positivity
    have h3 : ((L : ℝ) ^ n) ^ 2 ≤ ((L : ℝ) * (L : ℝ) ^ q.1) ^ 2 :=
      pow_le_pow_left₀ hLn.le hs 2
    nlinarith
  have d1 := (bump_diff1 hmk hlam q.2 y μ).1
  have d2 := (bump_diff1 hmk hlam q.2 y ν).1
  have d3 := (bump_diff1 hmk hlam q.2 (y + Pi.single μ 1) ν).1
  have d4 := bump_sq_diff hmk hlam q.2 y μ ν
  have c1 : |bump q.1 q.2 (y + Pi.single μ 1) - bump q.1 q.2 y| ≤ wb1 d * L / (L : ℝ) ^ n :=
    d1.trans key1
  have c2 : |bump q.1 q.2 (y + Pi.single ν 1) - bump q.1 q.2 y| ≤ wb1 d * L / (L : ℝ) ^ n :=
    d2.trans key1
  have c3 : |bump q.1 q.2 (y + Pi.single μ 1 + Pi.single ν 1) -
      bump q.1 q.2 (y + Pi.single μ 1)| ≤ wb1 d * L / (L : ℝ) ^ n := d3.trans key1
  refine ⟨c1.trans key1', c2.trans key1', ?_, d4.trans key2⟩
  have e : bump q.1 q.2 (y + Pi.single μ 1 + Pi.single ν 1) - bump q.1 q.2 y =
      (bump q.1 q.2 (y + Pi.single μ 1 + Pi.single ν 1) - bump q.1 q.2 (y + Pi.single μ 1)) +
        (bump q.1 q.2 (y + Pi.single μ 1) - bump q.1 q.2 y) := by ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  have : wc1 d L / (L : ℝ) ^ n = wb1 d * L / (L : ℝ) ^ n + wb1 d * L / (L : ℝ) ^ n := by
    unfold wc1; ring
  rw [this]
  exact add_le_add c3 c1

theorem sum_abs_le_supp4 {y : Torus d (N₀ * L ^ k)} {μ ν : Fin d}
    {f : ℕ × Torus d (N₀ * L ^ k) → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (h0 : ∀ q ∈ blockIdx G, q ∉ supp4 G y μ ν → f q = 0) (h1 : ∀ q ∈ supp4 G y μ ν, |f q| ≤ c)
    (hcard : (supp4 G y μ ν).card ≤ 12 * 3 ^ d) :
    |∑ q ∈ blockIdx G, f q| ≤ 12 * 3 ^ d * c := by
  rw [← Finset.sum_subset (supp4_subset G y μ ν) h0]
  calc |∑ q ∈ supp4 G y μ ν, f q| ≤ ∑ q ∈ supp4 G y μ ν, |f q| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _q ∈ supp4 G y μ ν, c := Finset.sum_le_sum h1
    _ = (supp4 G y μ ν).card * c := by simp
    _ ≤ (12 * 3 ^ d : ℕ) * c := by
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hc
    _ = 12 * 3 ^ d * c := by push_cast; ring

/-- Differences of the denominator over the square. -/
theorem denom_sq (hϱ : (4 * d * L : ℝ) ≤ ϱ) (hd : 1 ≤ d) (hL : 2 ≤ L) {n : ℕ} (hn3 : 3 ≤ n)
    (hnk : n ≤ k) {y : Torus d (N₀ * L ^ k)} (hy : y ∈ G.layer n) (μ ν : Fin d) :
    |denom G (y + Pi.single μ 1) - denom G y| ≤ wcU d L / (L : ℝ) ^ n ∧
    |denom G (y + Pi.single ν 1) - denom G y| ≤ wcU d L / (L : ℝ) ^ n ∧
    |denom G (y + Pi.single μ 1 + Pi.single ν 1) - denom G y| ≤ wcU d L / (L : ℝ) ^ n ∧
    |denom G (y + Pi.single μ 1 + Pi.single ν 1) - denom G (y + Pi.single μ 1) -
        denom G (y + Pi.single ν 1) + denom G y| ≤ wcV d L / ((L : ℝ) ^ n) ^ 2 := by
  have hcard := card_supp4_le G hϱ hd (by omega) hn3 hnk hy μ ν
  have hLn : (0 : ℝ) < (L : ℝ) ^ n := by
    have : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
    positivity
  have hb := fun q (hq : q ∈ supp4 G y μ ν) => bump_sq_supp G hϱ hd hL hn3 hnk hy μ ν hq
  have hc1 := wc1_nonneg d L
  have hcB := wcB_nonneg d L
  have z : ∀ q ∈ blockIdx G, q ∉ supp4 G y μ ν →
      bump q.1 q.2 y = 0 ∧ bump q.1 q.2 (y + Pi.single μ 1) = 0 ∧
        bump q.1 q.2 (y + Pi.single ν 1) = 0 ∧
        bump q.1 q.2 (y + Pi.single μ 1 + Pi.single ν 1) = 0 :=
    fun q hq hqs => not_mem_supp4 G hq hqs
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := sum_abs_le_supp4 G (y := y) (μ := μ) (ν := ν)
      (f := fun q => bump q.1 q.2 (y + Pi.single μ 1) - bump q.1 q.2 y)
      (c := wc1 d L / (L : ℝ) ^ n) (by positivity)
      (fun q hq hqs => by obtain ⟨a, b, c, e⟩ := z q hq hqs; simp [a, b]) (fun q hq => (hb q hq).1)
      hcard
    unfold denom
    rw [← Finset.sum_sub_distrib]
    refine this.trans (le_of_eq ?_)
    unfold wcU; ring
  · have := sum_abs_le_supp4 G (y := y) (μ := μ) (ν := ν)
      (f := fun q => bump q.1 q.2 (y + Pi.single ν 1) - bump q.1 q.2 y)
      (c := wc1 d L / (L : ℝ) ^ n) (by positivity)
      (fun q hq hqs => by obtain ⟨a, b, c, e⟩ := z q hq hqs; simp [a, c])
      (fun q hq => (hb q hq).2.1) hcard
    unfold denom
    rw [← Finset.sum_sub_distrib]
    refine this.trans (le_of_eq ?_)
    unfold wcU; ring
  · have := sum_abs_le_supp4 G (y := y) (μ := μ) (ν := ν)
      (f := fun q => bump q.1 q.2 (y + Pi.single μ 1 + Pi.single ν 1) - bump q.1 q.2 y)
      (c := wc1 d L / (L : ℝ) ^ n) (by positivity)
      (fun q hq hqs => by obtain ⟨a, b, c, e⟩ := z q hq hqs; simp [a, e])
      (fun q hq => (hb q hq).2.2.1) hcard
    unfold denom
    rw [← Finset.sum_sub_distrib]
    refine this.trans (le_of_eq ?_)
    unfold wcU; ring
  · have := sum_abs_le_supp4 G (y := y) (μ := μ) (ν := ν)
      (f := fun q => bump q.1 q.2 (y + Pi.single μ 1 + Pi.single ν 1) -
        bump q.1 q.2 (y + Pi.single μ 1) - bump q.1 q.2 (y + Pi.single ν 1) + bump q.1 q.2 y)
      (c := wcB d L / ((L : ℝ) ^ n) ^ 2) (by positivity)
      (fun q hq hqs => by obtain ⟨a, b, c, e⟩ := z q hq hqs; simp [a, b, c, e])
      (fun q hq => (hb q hq).2.2.2) hcard
    unfold denom
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine this.trans (le_of_eq ?_)
    unfold wcV; ring

end Quotient

section WeightSq

variable (G : GeneratingSet d L N₀ k ϱ)

theorem bump_le_denom {q : ℕ × Torus d (N₀ * L ^ k)} (hq : q ∈ blockIdx G)
    (x : Torus d (N₀ * L ^ k)) : bump q.1 q.2 x ≤ denom G x := by
  have := Finset.single_le_sum (f := fun q : ℕ × Torus d (N₀ * L ^ k) => bump q.1 q.2 x)
    (fun q hq => bump_nonneg_of_mem G hq x) hq
  exact this

/-- **The mixed second difference of every weight** at a site `y` of layer `n ≥ 3`:
`|h(y+e_μ+e_ν) - h(y+e_μ) - h(y+e_ν) + h(y)| ≤ H_m / ℓ(y)²`, `ℓ(y) = L^n`. -/
theorem weight_sq (hϱ : (4 * d * L : ℝ) ≤ ϱ) (hd : 1 ≤ d) (hL : 2 ≤ L) {n : ℕ} (hn3 : 3 ≤ n)
    (hnk : n ≤ k) {y : Torus d (N₀ * L ^ k)} (hy : y ∈ G.layer n) (μ ν : Fin d)
    {q : ℕ × Torus d (N₀ * L ^ k)} (hq : q ∈ blockIdx G) :
    |weight G q (y + Pi.single μ 1 + Pi.single ν 1) - weight G q (y + Pi.single μ 1) -
        weight G q (y + Pi.single ν 1) + weight G q y| ≤ wcM d L / ((L : ℝ) ^ n) ^ 2 := by
  have hLn : (0 : ℝ) < (L : ℝ) ^ n := by
    have : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
    positivity
  by_cases hs : q ∈ supp4 G y μ ν
  · obtain ⟨n₁, -, h1k, hy₁⟩ := layer_edge G hϱ hd (by omega) hn3 hnk hy μ
    obtain ⟨n₂, -, h2k, hy₂⟩ := layer_edge G hϱ hd (by omega) hn3 hnk hy ν
    obtain ⟨n₃, -, h3k, hy₃⟩ := layer_corner G hϱ hd (by omega) hn3 hnk hy μ ν
    have hq0 : (0 : ℝ) < (1 / 2 : ℝ) ^ d := by positivity
    have h00 := denom_ge G (by omega) hnk hy
    have h10 := denom_ge G (by omega) h1k hy₁.1
    have h01 := denom_ge G (by omega) h2k hy₂.1
    have h11 := denom_ge G (by omega) h3k hy₃.1
    obtain ⟨u10, u01, u11, uV⟩ := denom_sq G hϱ hd hL hn3 hnk hy μ ν
    obtain ⟨c10, c01, c11, cB⟩ := bump_sq_supp G hϱ hd hL hn3 hnk hy μ ν hs
    have := weight_mixed_alg (q0 := (1 / 2 : ℝ) ^ d) (B1 := wc1 d L / (L : ℝ) ^ n)
      (U1 := wcU d L / (L : ℝ) ^ n) (B2 := wcB d L / ((L : ℝ) ^ n) ^ 2)
      (V := wcV d L / ((L : ℝ) ^ n) ^ 2) hq0 h00 h10 h01 h11
      (bump_nonneg_of_mem G hq y) (bump_le_denom G hq y) c10 c01 c11 u10 u01 u11 cB uV
    refine this.trans (le_of_eq ?_)
    unfold wcM wcH
    field_simp
  · obtain ⟨a, b, c, e⟩ := not_mem_supp4 G hq hs
    have z0 : weight G q y = 0 := by unfold weight; rw [a, zero_div]
    have z1 : weight G q (y + Pi.single μ 1) = 0 := by unfold weight; rw [b, zero_div]
    have z2 : weight G q (y + Pi.single ν 1) = 0 := by unfold weight; rw [c, zero_div]
    have z3 : weight G q (y + Pi.single μ 1 + Pi.single ν 1) = 0 := by
      unfold weight; rw [e, zero_div]
    rw [z0, z1, z2, z3]
    simp only [sub_zero, abs_zero, add_zero]
    have := wcM_nonneg d L
    positivity

end WeightSq

section InterpSq

variable {N : ℕ} (G : GeneratingSet d L N₀ k ϱ)

/-- **Mixed second difference of the interpolated vector** at a site of layer `n ≥ 3`. -/
theorem interp_sq_le (hϱ : (4 * d * L : ℝ) ≤ ϱ) (hd : 1 ≤ d) (hL : 2 ≤ L) {n : ℕ} (hn3 : 3 ≤ n)
    (hnk : n ≤ k) {y : Torus d (N₀ * L ^ k)} (hy : y ∈ G.layer n) (μ ν : Fin d)
    (Φ : Torus d (N₀ * L ^ k) → Fin N → ℂ) (ref : Fin N → ℂ) {r : ℝ} (hr : 0 ≤ r)
    (h : ∀ q ∈ supp4 G y μ ν, cNorm (Φ q.2 - ref) ≤ r) :
    cNorm (interp G Φ (y + Pi.single μ 1 + Pi.single ν 1) - interp G Φ (y + Pi.single μ 1) -
        interp G Φ (y + Pi.single ν 1) + interp G Φ y) ≤
      12 * 3 ^ d * (wcM d L / ((L : ℝ) ^ n) ^ 2 * r) := by
  have hn1 : 1 ≤ n := by omega
  obtain ⟨n₁, h11, h1k, hy₁⟩ := layer_edge G hϱ hd (by omega) hn3 hnk hy μ
  obtain ⟨n₂, h21, h2k, hy₂⟩ := layer_edge G hϱ hd (by omega) hn3 hnk hy ν
  obtain ⟨n₃, h31, h3k, hy₃⟩ := layer_corner G hϱ hd (by omega) hn3 hnk hy μ ν
  have hcard := card_supp4_le G hϱ hd (by omega) hn3 hnk hy μ ν
  have hLn : (0 : ℝ) < (L : ℝ) ^ n := by
    have : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
    positivity
  have hM := wcM_nonneg d L
  have e : interp G Φ (y + Pi.single μ 1 + Pi.single ν 1) - interp G Φ (y + Pi.single μ 1) -
      interp G Φ (y + Pi.single ν 1) + interp G Φ y =
      ∑ q ∈ blockIdx G, ((weight G q (y + Pi.single μ 1 + Pi.single ν 1) -
        weight G q (y + Pi.single μ 1) - weight G q (y + Pi.single ν 1) + weight G q y : ℝ) : ℂ) •
        (Φ q.2 - ref) := by
    have e1 := interp_sub_ref G Φ ref (by omega : 1 ≤ n₃) h3k hy₃.1
    have e2 := interp_sub_ref G Φ ref (by omega : 1 ≤ n₁) h1k hy₁.1
    have e3 := interp_sub_ref G Φ ref (by omega : 1 ≤ n₂) h2k hy₂.1
    have e4 := interp_sub_ref G Φ ref hn1 hnk hy
    have : interp G Φ (y + Pi.single μ 1 + Pi.single ν 1) - interp G Φ (y + Pi.single μ 1) -
        interp G Φ (y + Pi.single ν 1) + interp G Φ y =
        (interp G Φ (y + Pi.single μ 1 + Pi.single ν 1) - ref) -
          (interp G Φ (y + Pi.single μ 1) - ref) - (interp G Φ (y + Pi.single ν 1) - ref) +
          (interp G Φ y - ref) := by
      funext i; simp [Pi.sub_apply, Pi.add_apply]; ring
    rw [this, e1, e2, e3, e4, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    push_cast
    simp only [sub_smul, add_smul]
  rw [e, ← Finset.sum_subset (supp4_subset G y μ ν) (fun q hq hqs => by
    obtain ⟨a, b, c, e⟩ := not_mem_supp4 G hq hqs
    have z0 : weight G q y = 0 := by unfold weight; rw [a, zero_div]
    have z1 : weight G q (y + Pi.single μ 1) = 0 := by unfold weight; rw [b, zero_div]
    have z2 : weight G q (y + Pi.single ν 1) = 0 := by unfold weight; rw [c, zero_div]
    have z3 : weight G q (y + Pi.single μ 1 + Pi.single ν 1) = 0 := by
      unfold weight; rw [e, zero_div]
    rw [z0, z1, z2, z3]; simp)]
  refine (weighted_sum_le (C := wcM d L / ((L : ℝ) ^ n) ^ 2) (r := r) (fun q hq => ⟨?_, h q hq⟩)
    (by positivity)).trans ?_
  · exact weight_sq G hϱ hd hL hn3 hnk hy μ ν (supp4_subset G y μ ν hq)
  · have cardR : ((supp4 G y μ ν).card : ℝ) ≤ 12 * 3 ^ d := by exact_mod_cast hcard
    exact mul_le_mul_of_nonneg_right cardR (by positivity)

end InterpSq

end Balaban.Background
