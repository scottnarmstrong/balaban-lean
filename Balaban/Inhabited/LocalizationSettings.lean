/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.I5Inhabited
public import Balaban.Localization.Decoupled2Self
public import Balaban.Localization.Decoupled2XGreen
public import Balaban.Localization.DecoupledXGreen
public import Balaban.Localization.DecoupledCovLocal
import Mathlib.Tactic.Positivity

/-!
# Inhabitation witnesses for the decoupled-layer hypothesis structures

At the positive scale of `I5Inhabited` (`d = L = 3`, `N₁ = 6`, level `K = 2`, `a = compWeight 3 1`,
`ν = 0`, `ϱ = rhoSep m₁`, `m₁ ≥ 4` large): `OpSetting`, `XSetting`, `Dec2.XCover`,
`Dec2.CoverLocalGeom`, `Dec2.XData`, `Localization.XData`.  `LocHyp` is inhabited for every
generating set with `HatConn`, any `X₁`, with `𝒞 = ∅` and `Y` the whole filtered set.

Degeneracy: the operator, cover and generating set are genuine (full torus, `Ω₁ = 𝕋`); the
potential `α` is `0` and the decoupling vector is constant, `κ = 0`, `x = 0`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.Localization.I5Inhabited

/-- **`LocHyp` is inhabited** for every generating set with `HatConn` and every `X₁`:
`𝒞 = ∅`, `Y = (X₁ ∪ ⋃_{P∈𝒞} P) ∩ Ω₁` (a component of itself), `α = 0`, and
`s = s' = 1_{P ∉ parCubes ∖ 𝒞}`. -/
theorem locHyp_nonempty {d L N₁ m₁ k : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
    (hd : 0 < d) (G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ) (hG : HatConn G)
    (X₁ : Finset (CTorus d L N₁ m₁ (k + 1))) :
    ∃ (Y : Finset (CTorus d L N₁ m₁ (k + 1))) (α : G.Ω 1 → ℂ)
      (s s' : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ),
      Nonempty (LocHyp G X₁ ∅ Y α s s') := by
  classical
  refine ⟨(Vset X₁ ∅).filter fun x => x ∈ G.Ω 1, 0,
    fun P => if P ∈ parCubes G X₁ then 0 else 1, fun P => if P ∈ parCubes G X₁ then 0 else 1,
    ⟨hG, ⟨Finset.Subset.refl _, fun x hx y hy _ => hy⟩, ?_, ?_, ?_, ?_⟩⟩
  · intro x
    simp only [Pi.zero_apply, norm_zero]
    have := coerciveConst_pos hd
    have hs := spacing_pos G (x := (x : CTorus d L N₁ m₁ (k + 1)))
    positivity
  · intro P _ hP; simp [hP]
  · intro P hP _; simp [hP]
  · intro P _ _; rfl

section Pos

/-- A positive-scale parameter choice: `m₁ ≥ 4` with `c* ≤ 3^{m₁}`. -/
theorem exists_m₁_cstar : ∃ m₁ : ℕ, 4 ≤ m₁ ∧ cstarX 3 3 ≤ (3 : ℝ) ^ m₁ :=
  exists_m₁ _

theorem xSetting_pos {m₁ : ℕ} (h4 : 4 ≤ m₁) :
    XSetting (k := 1) (GP m₁ (rhoSep m₁)) (compWeight 3 1) 1 0 :=
  ⟨dgSetting_rho h4, by rw [compWeight_one (by norm_num)]; norm_num,
    by rw [compWeight_one (by norm_num)]; norm_num, by norm_num, by norm_num⟩

/-- **`OpSetting` is inhabited** at positive scale. -/
theorem opSetting_nonempty :
    ∃ (m₁ : ℕ) (ϱ : ℝ) (H : GeneratingSet 3 3 (6 * 3 ^ m₁) 2 ϱ),
      Dec2.OpSetting H (compWeight 3 1) 0 := by
  obtain ⟨m₁, h4, -⟩ := exists_m₁_cstar
  have S := dgSetting_rho h4
  exact ⟨m₁, rhoSep m₁, GP m₁ (rhoSep m₁), ⟨⟨S.hd, S.hL, S.mass, S.weights, S.sep⟩, S.massLe⟩⟩

/-- **`XSetting` is inhabited** at positive scale (`k = 1`, `a_{k+1} = 1`). -/
theorem xSetting_nonempty :
    ∃ (m₁ : ℕ) (ϱ : ℝ) (G : GeneratingSet 3 3 (6 * 3 ^ m₁) (1 + 1) ϱ),
      XSetting G (compWeight 3 1) 1 0 :=
  let ⟨m₁, h4, _⟩ := exists_m₁_cstar
  ⟨m₁, rhoSep m₁, GP m₁ (rhoSep m₁), xSetting_pos h4⟩

/-- **`Dec2.CoverLocalGeom` is inhabited** at positive scale (the self-cover). -/
theorem coverLocalGeom_nonempty :
    ∃ (m₁ : ℕ) (ϱ : ℝ) (H : GeneratingSet 3 3 (6 * 3 ^ m₁) 2 ϱ),
      Dec2.CoverLocalGeom (coverOf H) H (compWeight 3 1) 0 (Cchi 3 3) := by
  obtain ⟨m₁, h4, -⟩ := exists_m₁_cstar
  exact ⟨m₁, rhoSep m₁, GP m₁ (rhoSep m₁), Dec2.coverLocalGeom_self (dgSetting_rho h4)⟩

/-- **`Dec2.XCover` is inhabited** at positive scale (the self-cover). -/
theorem xCover_nonempty :
    ∃ (m₁ : ℕ) (ϱ : ℝ) (H : GeneratingSet 3 3 (6 * 3 ^ m₁) (1 + 1) ϱ),
      Dec2.XCover (k := 1) (coverOf H) H (compWeight 3 1) 1 0 (Cchi 3 3) := by
  obtain ⟨m₁, h4, -⟩ := exists_m₁_cstar
  exact ⟨m₁, rhoSep m₁, GP m₁ (rhoSep m₁), Dec2.xCover_self (xSetting_pos h4)⟩

/-- **`Dec2.XData` is inhabited** at positive scale (`x = 0`, `κ = 0`, `α = 0`, `s ≡ 1`). -/
theorem dec2XData_nonempty :
    ∃ (m₁ : ℕ) (ϱ : ℝ) (H : GeneratingSet 3 3 (6 * 3 ^ m₁) (1 + 1) ϱ),
      Dec2.XData (k := 1) (coverOf H) H (compWeight 3 1) 1 0 0 0 0 (fun _ => 1) (Cchi 3 3) := by
  obtain ⟨m₁, h4, hc⟩ := exists_m₁_cstar
  refine ⟨m₁, rhoSep m₁, GP m₁ (rhoSep m₁), ?_⟩
  refine ⟨Dec2.xCover_self (xSetting_pos h4), Cchi_nonneg 3 3, ?_, le_rfl, le_rfl, ?_, ?_⟩
  · intro x
    simp only [Pi.zero_apply, norm_zero]
    have := coerciveConst_pos (by norm_num : 0 < 3)
    have hs := spacing_pos (GP m₁ (rhoSep m₁)) (x := (x : CTorus 3 3 6 m₁ (1 + 1)))
    positivity
  · simpa [Dec2.cstarX_self] using hc
  · intro P; simp

/-- **`Localization.XData` is inhabited** at positive scale (`x = 0`, `κ = 0`, `α = 0`, `s ≡ 1`). -/
theorem xData_nonempty :
    ∃ (m₁ : ℕ) (ϱ : ℝ) (G : GeneratingSet 3 3 (6 * 3 ^ m₁) (1 + 1) ϱ),
      Localization.XData (k := 1) G (compWeight 3 1) 1 0 0 0 0 (fun _ => 1) := by
  obtain ⟨m₁, h4, hc⟩ := exists_m₁_cstar
  refine ⟨m₁, rhoSep m₁, GP m₁ (rhoSep m₁), xSetting_pos h4, ?_, le_rfl, le_rfl, ?_, ?_⟩
  · intro x
    simp only [Pi.zero_apply, norm_zero]
    have := coerciveConst_pos (by norm_num : 0 < 3)
    have hs := spacing_pos (GP m₁ (rhoSep m₁)) (x := (x : CTorus 3 3 6 m₁ (1 + 1)))
    positivity
  · simpa using hc
  · intro P; simp

end Pos

end Balaban.Inhabited
