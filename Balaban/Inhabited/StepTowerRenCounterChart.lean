/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepTowerRenCounterSmall

/-!
# The renormalized datum lies in the step chart of the tower

At a step radius `t = λ ε_{k+1}`, `λ = 1 + ξ₂ (3/2) r₀` (the radii of the towers of
`e0CoeffFamily_class_exists_tower_struct_step_collar_classEps_ren_phi`), the renormalized datum
`θ_ξ` of a class-chart datum at radius `ε_{k+1}` with `‖ξ‖ < r₀ ≤ 1` lies in the step chart
`XiCData` of radius `t`, as soon as `ε_1 ≤ ε*` (`classEps_theta_small`).
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.SmallField.Def6
  Balaban.Fluctuation Balaban.Localization

/-- **The chart inclusion at the towers.**  There is `ε* > 0` such that for class constants with
`0 < α₀`, `0 ≤ α`, `ε_1 ≤ ε*`, every `k ≥ 1`, every step radius `t = λ ε_{k+1}` with
`λ = 1 + ξ₂ (3/2) r₀`, `0 < r₀ ≤ 1`, every step setting `S` with `BgHyp`, every class-chart datum
`D` at radius `ε_{k+1}` and `‖ξ‖ < r₀`, the datum `renThetaDatum S ε_{k+1} D ξ` lies in
`XiCData` of level `k + 1` and radius `t`. -/
theorem renThetaDatum_xiCData_classEps (L N : ℕ) [NeZero L] :
    ∃ εs : ℝ, 0 < εs ∧ ∀ P : Consts, 0 < P.α₀ → 0 ≤ P.alpha 3 → P.eps 3 3 1 ≤ εs →
      ∀ {N₁ m₁ k : ℕ} [NeZero N₁] {ϱ : ℝ} (S : StepSetting 3 L N₁ m₁ k N ϱ),
      1 ≤ k → BgHyp 3 L (k + 1) ϱ S.a S.ν → ∀ {r₀ t lam : ℝ}, 0 < r₀ → r₀ ≤ 1 →
      lam = 1 + xiK2 3 L N * ((3 / 2 : ℝ) * r₀) → t = lam * P.eps 3 3 (k + 1) →
      ∀ D : BgData S.G' N, XiCOneReal S.G' S.a S.ν (P.eps 3 3 (k + 1)) D →
      ∀ ξ : Fin 3 → ℂ, ‖ξ‖ < r₀ →
      XiCData S.G' S.a S.ν (k + 1) 1 t (renThetaDatum S (P.eps 3 3 (k + 1)) D ξ) := by
  obtain ⟨εs, hεs, H⟩ := classEps_theta_small L N
  refine ⟨εs, hεs, fun P hα₀ hα h1 N₁ m₁ k _ ϱ S hk Hb r₀ t lam hr hr1 hlam ht D hD ξ hξ => ?_⟩
  obtain ⟨hpos, a1, a2, a3, a4, a5, a6⟩ := H P hα₀ hα h1 (k + 1) (by omega)
  have a2' : (4 * (3 : ℕ) + 6 : ℝ) * ((2 * (3 : ℕ) + 1) * P.eps 3 3 (k + 1)) ≤ 1 := by
    push_cast; exact a2
  exact renThetaDatum_xiCData_tower S Hb hpos hr hr1 a1 a2' a3 a4 a5 a6 hlam ht D hD ξ hξ

end Balaban.Inhabited
