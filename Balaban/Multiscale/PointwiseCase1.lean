/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Multiscale.PointwiseScale

/-!
# Lemma P, Case 1: the inverse inequality

`PtSetting.U x = |ũ(x)| + ℓ(x) ∑_μ |ũ(x + e_μ) - ũ(x)|` (the gradient over the `d` forward bonds
at `x`).  For `x` in layer `j` and `0 ≤ t ≤ d(x, y')` the weighted Agmon bounds give
`U(x) ≤ C ℓ_j bd^j e^{-(ε₀/2) t} ℓ_{j'}² bd ‖f‖_∞` (`case1_bound`); this is the pointwise bound with
no recursion term for the layers with `ℓ_j` bounded.
-/

@[expose] public section

noncomputable section

namespace Balaban.Multiscale

open Finset Matrix Balaban Balaban.LatticeGreen

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

namespace PtSetting

variable {G : GeneratingSet d L N₀ k ϱ} {Λ : ℝ} (S : PtSetting G Λ)

/-- `U(x) = |ũ(x)| + ℓ(x) ∑_μ |ũ(x + e_μ) - ũ(x)|`. -/
def U (x : Torus d (N₀ * L ^ k)) : ℝ :=
  ‖S.ut x‖ + G.spacing x * ∑ μ : Fin d, ‖S.ut (x + Pi.single μ 1) - S.ut x‖

theorem U_nonneg (x : Torus d (N₀ * L ^ k)) : 0 ≤ S.U x := by
  unfold U
  have := spacing_pos G (x := x)
  positivity

theorem norm_ut_le_U (x : Torus d (N₀ * L ^ k)) : ‖S.ut x‖ ≤ S.U x := by
  unfold U
  have h : 0 ≤ G.spacing x * ∑ μ : Fin d, ‖S.ut (x + Pi.single μ 1) - S.ut x‖ := by
    have := spacing_pos G (x := x)
    positivity
  linarith

/-- **Case 1.** -/
theorem case1_bound {Mf : ℝ} (hMf0 : 0 ≤ Mf) (hMf : ∀ i, ‖S.f i‖ ≤ Mf)
    {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.Ω 1) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : ENNReal.ofReal t ≤ G.pathDist x S.y') :
    S.U x ≤ 2 / poincareConst d * (1 + d) * Real.exp (2 * agmonRate d * d) * bd d L *
      ((L : ℝ) ^ G.layerIndex x * bd d L ^ G.layerIndex x) * Real.exp (-(agmonRate d / 2 * t)) *
        ((L : ℝ) ^ (2 * S.j') * Mf) := by
  obtain ⟨hj1, hjk, hxl⟩ := G.layerIndex_spec hx
  set j := G.layerIndex x with hj
  obtain ⟨t₂, htt, ht2, habs⟩ := scale_abs S hj1 hxl ht0 ht
  have ht20 : 0 ≤ t₂ := ht0.trans htt
  have hc := poincareConst_pos S.hd0
  have hr : G.truncDist S.y' t₂ x = t₂ := G.truncDist_eq_of_le ht20 ht2
  have hsp : G.spacing x = (L : ℝ) ^ j := G.spacing_eq hj1 hjk hxl
  have hp := S.pt_bound t₂ hx
  rw [hr] at hp
  have hg : ∀ μ : Fin d, ‖S.ut (x + Pi.single μ 1) - S.ut x‖ ≤ 2 / poincareConst d *
      Real.exp (-(agmonRate d * t₂)) * S.amp := fun μ => by
    have := S.grad_bound t₂ hx μ
    rwa [hr] at this
  have hA := amp_le S hMf0 hMf
  have hE : 0 ≤ Real.exp (-(agmonRate d * t₂)) := (Real.exp_pos _).le
  have hAn := S.amp_nonneg
  have hLj : 0 ≤ (L : ℝ) ^ j := by positivity
  unfold U
  rw [hsp] at hp ⊢
  have hsum : ∑ μ : Fin d, ‖S.ut (x + Pi.single μ 1) - S.ut x‖ ≤ d * (2 / poincareConst d *
      Real.exp (-(agmonRate d * t₂)) * S.amp) := by
    calc _ ≤ ∑ _μ : Fin d, (2 / poincareConst d * Real.exp (-(agmonRate d * t₂)) * S.amp) :=
          Finset.sum_le_sum fun μ _ => hg μ
      _ = _ := by simp
  have hK : 0 ≤ 2 / poincareConst d * Real.exp (-(agmonRate d * t₂)) * S.amp := by positivity
  calc ‖S.ut x‖ + (L : ℝ) ^ j * ∑ μ : Fin d, ‖S.ut (x + Pi.single μ 1) - S.ut x‖
      ≤ 2 / poincareConst d * (L : ℝ) ^ j * Real.exp (-(agmonRate d * t₂)) * S.amp +
        (L : ℝ) ^ j * (d * (2 / poincareConst d * Real.exp (-(agmonRate d * t₂)) * S.amp)) :=
        add_le_add hp (mul_le_mul_of_nonneg_left hsum hLj)
    _ = 2 / poincareConst d * (1 + d) * (L : ℝ) ^ j * Real.exp (-(agmonRate d * t₂)) * S.amp := by
        ring
    _ ≤ 2 / poincareConst d * (1 + d) * (L : ℝ) ^ j * Real.exp (-(agmonRate d * t₂)) *
        (Real.exp (2 * agmonRate d * d) * ((L : ℝ) ^ S.j') ^ 2 * bd d L ^ S.j' * Mf) :=
        mul_le_mul_of_nonneg_left hA (by positivity)
    _ = 2 / poincareConst d * (1 + d) * Real.exp (2 * agmonRate d * d) * (L : ℝ) ^ j *
        (bd d L ^ S.j' * Real.exp (-(agmonRate d * t₂))) * (((L : ℝ) ^ S.j') ^ 2 * Mf) := by
        ring
    _ ≤ 2 / poincareConst d * (1 + d) * Real.exp (2 * agmonRate d * d) * (L : ℝ) ^ j *
        (bd d L ^ j * bd d L * Real.exp (-(agmonRate d / 2 * t))) *
        (((L : ℝ) ^ S.j') ^ 2 * Mf) := by
        gcongr
    _ = _ := by
        rw [pow_mul']
        ring

end PtSetting

end Balaban.Multiscale
