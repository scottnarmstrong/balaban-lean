/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.NewLevelCanonCastGeom
public import Balaban.Localization.I5Fan

/-!
# The region of a term contains the ball around its data sites

`reg_of_bgSetting`: `BgSetting.hN` (the `ℓ¹`-ball of radius `r₀ L^{m₁} ⋅ spacing` around the sites
of `X₀ ⊇ dataSites(Gk)` lies in `X₁`) gives, for the top level `Gp` (spacing `L^{k+1}`) and
`r₀ ≥ 4 d L³`, the hypothesis `hreg` of `hgeom_of_cast`: the sites at integer distance `8 L^{k+1+m₁}` of a
data site of `Gk` lie in `X₁`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.Fluctuation

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱ₁ : ℝ}

/-- **`hreg` from `BgSetting.hN`.** -/
theorem reg_of_hN {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} (hG : IsLevel Gp (k + 1))
    {r₀ : ℝ} (hr₀ : 4 * d * (L : ℝ) ^ 3 ≤ r₀) (hL : 3 ≤ L) (hd : 1 ≤ d)
    {X₀ X₁f : Finset (CTorus d L N₁ m₁ (k + 1))}
    (hN : ∀ x ∈ X₀, x ∈ Gp.Ω 1 → ∀ y : CTorus d L N₁ m₁ (k + 1),
      Green.torusDist d ((N₁ * L ^ m₁) * L ^ (k + 1)) x y < r₀ * (L : ℝ) ^ m₁ * Gp.spacing x →
      y ∈ X₁f)
    {p : CTorus d L N₁ m₁ (k + 1)} (hp : p ∈ X₀) (v : Fin d → ℤ)
    (hv : ∀ μ, |v μ| ≤ ((8 * L ^ ((k + 1) + m₁) : ℕ) : ℤ)) :
    p + (intTorus v : CTorus d L N₁ m₁ (k + 1)) ∈ (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) := by
  rw [Finset.mem_coe]
  refine hN p hp (hG p).1 _ ?_
  have hsp : Gp.spacing p = (L : ℝ) ^ (k + 1) := by
    unfold GeneratingSet.spacing; rw [(hG p).2]
  rw [hsp]
  have hdist : Green.torusDist d ((N₁ * L ^ m₁) * L ^ (k + 1)) p (p + (intTorus v : CTorus d L N₁ m₁ (k + 1))) ≤
      ∑ μ, ((v μ).natAbs : ℝ) := by
    have := torusDist_le_of_lift (x := p) (z := p + (intTorus v : CTorus d L N₁ m₁ (k + 1)))
      (fun μ => ((p μ).val : ℤ)) (fun μ => ((p μ).val : ℤ) + v μ)
      (fun μ => by simp) (fun μ => by simp [intTorus_apply])
    refine this.trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun μ _ => ?_
    congr 1
    rw [show ((p μ).val : ℤ) - (((p μ).val : ℤ) + v μ) = -v μ by ring, Int.natAbs_neg]
  have hsum : ∑ μ, ((v μ).natAbs : ℝ) ≤ d * (8 * (L : ℝ) ^ ((k + 1) + m₁)) := by
    have h1 : ∀ μ, ((v μ).natAbs : ℝ) ≤ 8 * (L : ℝ) ^ ((k + 1) + m₁) := fun μ => by
      have := hv μ
      have h2 : ((v μ).natAbs : ℤ) ≤ ((8 * L ^ ((k + 1) + m₁) : ℕ) : ℤ) := by
        rw [Int.natCast_natAbs]; exact this
      have h3 : (v μ).natAbs ≤ 8 * L ^ ((k + 1) + m₁) := by exact_mod_cast h2
      exact_mod_cast h3
    calc ∑ μ, ((v μ).natAbs : ℝ) ≤ ∑ _μ : Fin d, 8 * (L : ℝ) ^ ((k + 1) + m₁) :=
          Finset.sum_le_sum fun μ _ => h1 μ
      _ = d * (8 * (L : ℝ) ^ ((k + 1) + m₁)) := by simp
  refine lt_of_le_of_lt (hdist.trans hsum) ?_
  have hLr : (3 : ℝ) ≤ L := by exact_mod_cast hL
  have hdr : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hpos : 0 < (L : ℝ) ^ ((k + 1) + m₁) := by positivity
  have e : (L : ℝ) ^ ((k + 1) + m₁) = (L : ℝ) ^ m₁ * (L : ℝ) ^ (k + 1) := by
    rw [pow_add]; ring
  have hL3 : (27 : ℝ) ≤ (L : ℝ) ^ 3 := by nlinarith [sq_nonneg (L : ℝ)]
  calc (d : ℝ) * (8 * (L : ℝ) ^ ((k + 1) + m₁)) < 4 * d * (L : ℝ) ^ 3 * (L : ℝ) ^ ((k + 1) + m₁) := by
        nlinarith [mul_pos (by linarith : (0 : ℝ) < d) hpos]
    _ ≤ r₀ * (L : ℝ) ^ ((k + 1) + m₁) := by
        exact mul_le_mul_of_nonneg_right hr₀ hpos.le
    _ = r₀ * (L : ℝ) ^ m₁ * (L : ℝ) ^ (k + 1) := by rw [e]; ring

end Balaban.Inhabited
