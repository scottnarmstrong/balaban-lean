/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseXCover
public import Balaban.Localization.XCutOperator

/-!
# The mass shift: the x-variant at `x = 0` is the first step's operator

At the first step (`k = 0`, one layer) the x-variant operator with `x = 0`, `a₀ = 2` and
`aT = 2 a₁ L² / (2 L² - a₁)` is the first step's Dirichlet operator with weight `a₁`, for every
mass `ν`.
-/

@[expose] public section

namespace Balaban.LargeField.Base

open Balaban Balaban.Multiscale Balaban.Localization

section L1

variable {d L N₀ : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}
  (G : GeneratingSet d L N₀ 1 ϱ)

theorem xAvgMatrix_zero_eq_avgMatrix (hL : 2 ≤ L) {a : ℕ → ℝ} {aT : ℝ} (ha0 : a 0 = 2)
    (ha1 : 0 ≤ a 1) (ha1' : a 1 ≤ 2)
    (haT : aT = 2 * a 1 * (L : ℝ) ^ 2 / (2 * (L : ℝ) ^ 2 - a 1)) :
    xAvgMatrix (k := 0) G a (xS1 (a 0) 0) (xS2 (a 0) (aT / (L : ℝ) ^ 2) 0) = avgMatrix G a := by
  have hL2 : (4 : ℝ) ≤ (L : ℝ) ^ 2 := by
    have : (2 : ℝ) ≤ L := by exact_mod_cast hL
    nlinarith
  have hpos : 0 < 2 * (L : ℝ) ^ 2 - a 1 := by linarith
  have hL0 : (L : ℝ) ^ 2 ≠ 0 := by positivity
  have hs1 : xS1 (a 0) 0 = 0 := by simp [xS1]
  have hs2 : xS2 (a 0) (aT / (L : ℝ) ^ 2) 0 = a 1 / (L : ℝ) ^ 2 := by
    have hden : (0 : ℝ) < 2 + aT / (L : ℝ) ^ 2 := by
      have : 0 ≤ aT / (L : ℝ) ^ 2 := by
        rw [haT]; positivity
      linarith
    unfold xS2
    rw [ha0]
    have hT : aT * (2 * (L : ℝ) ^ 2 - a 1) = 2 * a 1 * (L : ℝ) ^ 2 := by
      rw [haT]; field_simp
    rw [div_eq_div_iff (by linarith) hL0]
    have hb : aT / (L : ℝ) ^ 2 * (L : ℝ) ^ 2 = aT := by field_simp
    have hT' : aT / (L : ℝ) ^ 2 * (2 * (L : ℝ) ^ 2 - a 1) = 2 * a 1 := by
      apply mul_right_cancel₀ hL0
      linear_combination hT + (2 * (L : ℝ) ^ 2 - a 1) * hb
    linear_combination hT'
  have hlay : layerBlockMatrix G 1 1 = layerProjMatrix G 1 := rfl
  unfold xAvgMatrix avgMatrix
  rw [hs1, hs2]
  simp [hlay]

/-- **L1 (cut version).**  At the first step, with `x = 0`, `a₀ = 2` and
`aT = 2 a₁ L² / (2 L² - a₁)`, the cut x-variant operator is the cut Dirichlet operator with
weight `a₁`, for every mass `ν`. -/
theorem cutXOperator_zero_eq_cutOperator (hL : 2 ≤ L) {a : ℕ → ℝ} {aT : ℝ} (ha0 : a 0 = 2)
    (ha1 : 0 ≤ a 1) (ha1' : a 1 ≤ 2)
    (haT : aT = 2 * a 1 * (L : ℝ) ^ 2 / (2 * (L : ℝ) ^ 2 - a 1)) (ν : ℝ)
    (cut : Finset (Torus d (N₀ * L ^ 1) × Fin d)) (α : G.Ω 1 → ℂ) :
    cutXOperator (k := 0) G a aT 0 ν cut α = cutOperator G a ν cut α := by
  unfold cutXOperator cutOperator cutXFullMatrix cutFullMatrix
  rw [xAvgMatrix_zero_eq_avgMatrix G hL ha0 ha1 ha1' haT]

/-- **L1.**  The x-variant Dirichlet operator at `x = 0`, `a₀ = 2`,
`aT = 2 a₁ L² / (2 L² - a₁)` is the first step's Dirichlet operator with weight `a₁`, for every
mass `ν`. -/
theorem xDirichletOperator_zero_eq_dirichletOperator (hL : 2 ≤ L) {a : ℕ → ℝ} {aT : ℝ}
    (ha0 : a 0 = 2) (ha1 : 0 ≤ a 1) (ha1' : a 1 ≤ 2)
    (haT : aT = 2 * a 1 * (L : ℝ) ^ 2 / (2 * (L : ℝ) ^ 2 - a 1)) (ν : ℝ) (α : G.Ω 1 → ℂ) :
    xDirichletOperator (k := 0) G a aT 0 ν α = dirichletOperator G a ν α := by
  unfold xDirichletOperator dirichletOperator xFullMatrix fullMatrix
  rw [xAvgMatrix_zero_eq_avgMatrix G hL ha0 ha1 ha1' haT]

end L1

section L3

/-- **L3, with the mass bound `ν L² ≤ 1` kept (the bound can be dropped once `massLe` has moved
from `OpSetting` to `CoverBase`).**  `XCover` holds at `k = 0` with `a₀ = 2`, `a₁ = 1` and
`aT = 2 L² / (2 L² - 1)`, the weights of `xDirichletOperator_zero_eq_dirichletOperator`. -/
theorem base_xCover_massShift_exists_of_massLe {d L N₁ m₁ : ℕ} [NeZero L] [NeZero N₁]
    (hd : 3 ≤ d) (hL : 3 ≤ L) (hM : 4 * L ^ 2 ≤ L ^ m₁) (hN₁ : 5 < N₁) {ν : ℝ} (hν0 : 0 ≤ ν)
    (hν : ν * (L : ℝ) ^ 2 ≤ 1) :
    ∃ (G : GeneratingSet d L (N₁ * L ^ m₁) 1 (Inhabited.LevelStep.rhoSepG d L m₁))
      (a : ℕ → ℝ) (aT : ℝ), a 0 = 2 ∧ a 1 = 1 ∧
        aT = 2 * a 1 * (L : ℝ) ^ 2 / (2 * (L : ℝ) ^ 2 - a 1) ∧
        Dec2.XCover (coverOf G) G a aT ν (Cchi d L) := by
  obtain ⟨G, -, S⟩ := baseDGSetting_exists (m₁ := m₁) (N₁ := N₁) hd hL hM hN₁ hν0 hν
  have hL2 : 2 ≤ L := by omega
  have hLr : (3 : ℝ) ≤ L := by exact_mod_cast hL
  have hL4 : (9 : ℝ) ≤ (L : ℝ) ^ 2 := by nlinarith
  refine ⟨G, Function.update (Background.compWeight L 1) 0 2, 2 * (L : ℝ) ^ 2 / (2 * (L : ℝ) ^ 2 - 1),
    by simp, ?_, ?_, ?_⟩
  · rw [Function.update_of_ne (by omega)]
    exact Background.compWeight_one hL2 1
  · have : Function.update (Background.compWeight L 1) 0 2 1 = 1 := by
      rw [Function.update_of_ne (by omega)]
      exact Background.compWeight_one hL2 1
    rw [this]; ring
  have hw : IsAdmissibleWeights 1 (Function.update (Background.compWeight L 1) 0 2) := by
    intro j h1 h2
    rw [Function.update_of_ne (by omega)]
    exact S.weights j h1 h2
  have hpos : 0 < 2 * (L : ℝ) ^ 2 - 1 := by linarith
  have haT : 2 * (L : ℝ) ^ 2 / (2 * (L : ℝ) ^ 2 - 1) = 1 + 1 / (2 * (L : ℝ) ^ 2 - 1) := by
    field_simp; ring
  have hle : 1 / (2 * (L : ℝ) ^ 2 - 1) ≤ 1 := by
    rw [div_le_one hpos]; linarith
  have hge : 0 ≤ 1 / (2 * (L : ℝ) ^ 2 - 1) := by positivity
  refine Dec2.xCover_self (k := 0)
    { dg := { S with weights := hw }
      hak1 := by rw [Function.update_self]; norm_num
      hak2 := by rw [Function.update_self]
      haT1 := by rw [haT]; linarith
      haT2 := by rw [haT]; linarith }

end L3

end Balaban.LargeField.Base
