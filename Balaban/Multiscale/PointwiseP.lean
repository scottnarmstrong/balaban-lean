/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Multiscale.PointwiseCase2d

/-!
# Lemma P (GREEN.md §4.5, (4.3))

For `u = G_D(α) f`, `f` supported in the `j'`-block of `y'`, and `U(x) = |ũ(x)| + ℓ(x) ∑_μ |∂_μ ũ(x)|`:

`U(x) ≤ K₁ e^{-(ε₀/2) t} ℓ_{j'}² ‖f‖_∞ + θ* M`

for every `0 ≤ t ≤ d(x, y')` and every `M` bounding `U` on the `(2d+1)`-neighbourhood of `x`
(path metric), with `θ* = ¼ e^{-(ε₀/2)(2d+1)}` and `K₁` depending only on `d` and `L`.
-/

@[expose] public section

noncomputable section

namespace Balaban.Multiscale

open Finset Matrix Balaban Balaban.LatticeGreen

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- The contraction constant `θ* = ¼ e^{-(ε₀/2)(2d+1)}`. -/
def thetaStar (d : ℕ) : ℝ := 1 / 4 * Real.exp (-(agmonRate d / 2 * (2 * d + 1)))

theorem thetaStar_pos (d : ℕ) : 0 < thetaStar d := by
  unfold thetaStar; positivity

/-- **Lemma P** (GREEN.md (4.3)). -/
theorem lemmaP (hd : 3 ≤ d) (hL : 3 ≤ L) :
    ∃ K1 : ℝ, 0 ≤ K1 ∧ ∀ {k N₀ : ℕ} [NeZero N₀] {ϱ : ℝ} (G : GeneratingSet d L N₀ k ϱ)
      (S : PtSetting G) {Mf : ℝ}, 0 ≤ Mf → (∀ i, ‖S.f i‖ ≤ Mf) → ∀ {x : Torus d (N₀ * L ^ k)},
      x ∈ G.Ω 1 → ∀ {t : ℝ}, 0 ≤ t → ENNReal.ofReal t ≤ G.pathDist x S.y' → ∀ {M : ℝ}, 0 ≤ M →
      (∀ z ∈ G.Ω 1, G.pathDist z x ≤ ENNReal.ofReal (2 * d + 1) → S.U z ≤ M) →
      S.U x ≤ K1 * Real.exp (-(agmonRate d / 2 * t)) * ((L : ℝ) ^ (2 * S.j') * Mf) +
        thetaStar d * M := by
  obtain ⟨Ca, Cb, hCa, hCb, hLoc⟩ := loc_lift (d := d) hd
  obtain ⟨cG, hcG, hGs⟩ := green_sum_le hd
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
  have hd0 : (0 : ℝ) < d := by linarith
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have hL0 : (0 : ℝ) < L := by linarith
  have hc := poincareConst_pos (by omega : 0 < d)
  have hθ := thetaStar_pos d
  set CG := cG * (36 + 12 * L) + 1 with hCG
  have hCG0 : 0 < CG := by positivity
  set c0 := min (1 / 4 : ℝ) (thetaStar d / CG) with hc0def
  have hc0 : 0 < c0 := lt_min (by norm_num) (by positivity)
  have hc04 : c0 ≤ 1 / 4 := min_le_left _ _
  have hc0θ : cG * (36 + 12 * L) * c0 ≤ thetaStar d := by
    have h1 : c0 ≤ thetaStar d / CG := min_le_right _ _
    have h2 : c0 * CG ≤ thetaStar d := by
      rwa [le_div_iff₀ hCG0] at h1
    have h3 : cG * (36 + 12 * L) * c0 ≤ CG * c0 := by
      rw [hCG]; nlinarith
    nlinarith
  set J0 := 8 * d * L / c0 with hJ0
  set Kc2 := ((Ca + d * (d * L / c0) * Cb) *
        (2 / poincareConst d * Real.exp (agmonRate d * (1 + 2 * d)) * (L : ℝ) ^ 2 * bd d L ^ 2 /
          Real.sqrt ((c0 / d) ^ d)) +
        cG * (4 + 2 * d * L) * Real.exp (agmonRate d / 2 * (2 * d + 1))) with hKc2
  set Kc1 := 2 / poincareConst d * (1 + d) * Real.exp (2 * agmonRate d * d) * bd d L *
    Real.sqrt (J0 ^ d) with hKc1
  have hb1 := one_le_bd (d := d) (L := L)
  have hb0 : 0 < bd d L := by linarith
  have hKc2n : 0 ≤ Kc2 := by positivity
  have hKc1n : 0 ≤ Kc1 := by positivity
  refine ⟨max Kc1 Kc2, le_max_of_le_left hKc1n, ?_⟩
  intro k N₀ _ ϱ G S Mf hMf0 hMf x hx t ht0 ht M hM0 hM
  obtain ⟨hj1, hjk, hxl⟩ := G.layerIndex_spec hx
  set j := G.layerIndex x with hj
  have hFnn : 0 ≤ Real.exp (-(agmonRate d / 2 * t)) * ((L : ℝ) ^ (2 * S.j') * Mf) := by
    positivity
  have hθM : 0 ≤ thetaStar d * M := by positivity
  by_cases hρ : 8 ≤ c0 * (L : ℝ) ^ (j - 1) / d
  · -- Case 2
    have hj2 : 2 ≤ j := by
      by_contra hlt
      have : j = 1 := by omega
      rw [this] at hρ
      simp only [Nat.sub_self, pow_zero, mul_one] at hρ
      have : c0 / d ≤ 1 / 4 := by
        rw [div_le_iff₀ hd0]; nlinarith
      linarith
    obtain ⟨j₀, hj₀⟩ : ∃ j₀, j = j₀ + 1 := ⟨j - 1, by omega⟩
    have hj01 : 1 ≤ j₀ := by omega
    rw [hj₀] at hxl hjk hρ
    simp only [Nat.add_sub_cancel] at hρ
    obtain ⟨hLa, hLb⟩ := hLoc (L := L) (N₀ := N₀) (k := k) x S.ut (ρ := c0 * (L : ℝ) ^ j₀ / d) hρ
    have h2 := S.case2_bound hCa hCb hcG hc0 hc04 hj01 hjk hxl hρ hMf0 hMf ht0 ht hM0 hM
      hLa hLb hGs
    refine h2.trans ?_
    have h3 : Kc2 * Real.exp (-(agmonRate d / 2 * t)) * ((L : ℝ) ^ (2 * S.j') * Mf) ≤
        max Kc1 Kc2 * Real.exp (-(agmonRate d / 2 * t)) * ((L : ℝ) ^ (2 * S.j') * Mf) := by
      rw [mul_assoc, mul_assoc]
      exact mul_le_mul_of_nonneg_right (le_max_right _ _) hFnn
    have h4 : cG * (36 + 12 * L) * c0 * M ≤ thetaStar d * M :=
      mul_le_mul_of_nonneg_right hc0θ hM0
    linarith
  · -- Case 1
    have h1 := S.case1_bound hMf0 hMf hx ht0 ht
    rw [← hj] at h1
    have hLj : (L : ℝ) ^ j ≤ J0 := by
      have h2 : (L : ℝ) ^ (j - 1) < 8 * d / c0 := by
        push Not at hρ
        rw [lt_div_iff₀ hc0]
        rw [div_lt_iff₀ hd0] at hρ
        nlinarith
      have h3 : (L : ℝ) ^ j = L * (L : ℝ) ^ (j - 1) := by
        rw [← pow_succ']; congr 1; omega
      rw [h3, hJ0]
      have : (L : ℝ) * (8 * d / c0) = 8 * d * L / c0 := by ring
      rw [← this]
      exact mul_le_mul_of_nonneg_left h2.le hL0.le
    have hsq : (L : ℝ) ^ j * bd d L ^ j ≤ Real.sqrt (J0 ^ d) := by
      rw [← sqrt_L_pow_eq (by omega : 2 ≤ d) j]
      exact Real.sqrt_le_sqrt (pow_le_pow_left₀ (by positivity) hLj d)
    refine h1.trans ?_
    have h5' : 2 / poincareConst d * (1 + d) * Real.exp (2 * agmonRate d * d) * bd d L *
        ((L : ℝ) ^ j * bd d L ^ j) ≤ Kc1 := by
      rw [hKc1]
      exact mul_le_mul_of_nonneg_left hsq (by positivity)
    have h5 : 2 / poincareConst d * (1 + d) * Real.exp (2 * agmonRate d * d) * bd d L *
        ((L : ℝ) ^ j * bd d L ^ j) * Real.exp (-(agmonRate d / 2 * t)) *
          ((L : ℝ) ^ (2 * S.j') * Mf) ≤
        Kc1 * Real.exp (-(agmonRate d / 2 * t)) * ((L : ℝ) ^ (2 * S.j') * Mf) := by
      calc _ = (2 / poincareConst d * (1 + d) * Real.exp (2 * agmonRate d * d) * bd d L *
            ((L : ℝ) ^ j * bd d L ^ j)) * (Real.exp (-(agmonRate d / 2 * t)) *
              ((L : ℝ) ^ (2 * S.j') * Mf)) := by ring
        _ ≤ Kc1 * (Real.exp (-(agmonRate d / 2 * t)) * ((L : ℝ) ^ (2 * S.j') * Mf)) :=
            mul_le_mul_of_nonneg_right h5' hFnn
        _ = _ := by ring
    have h6 : Kc1 * Real.exp (-(agmonRate d / 2 * t)) * ((L : ℝ) ^ (2 * S.j') * Mf) ≤
        max Kc1 Kc2 * Real.exp (-(agmonRate d / 2 * t)) * ((L : ℝ) ^ (2 * S.j') * Mf) := by
      calc Kc1 * Real.exp (-(agmonRate d / 2 * t)) * ((L : ℝ) ^ (2 * S.j') * Mf)
          = Kc1 * (Real.exp (-(agmonRate d / 2 * t)) * ((L : ℝ) ^ (2 * S.j') * Mf)) := by ring
        _ ≤ max Kc1 Kc2 * (Real.exp (-(agmonRate d / 2 * t)) * ((L : ℝ) ^ (2 * S.j') * Mf)) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) hFnn
        _ = _ := by ring
    linarith

end Balaban.Multiscale
