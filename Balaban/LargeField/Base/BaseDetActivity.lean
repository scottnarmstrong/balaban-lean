/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseDetTrace
public import Balaban.Fluctuation.DetCauchyActivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The localized determinant activities of the first step

The activities `baseDetActivity y Y` of the first step are the instance of the core
`detActivityOf` (`DetCauchyActivity`) at the rooted trace `rootTraceBase` of `BaseDetTrace`: the
sum of the mixed differences `Δ_J` of `s ↦ -(1/2) ∑_i baseCovXLogShift(s)_{(y,i),(y,i)}` over the
sets `J` of parameter cubes whose hull is the polymer `Y`.

* `sum_baseDetActivity_eq`: `∑_Y baseDetActivity y Y = rootTraceBase y 1`;
* `baseDetActivity_ne_zero_imp`: support on polymers containing the root cube;
* `norm_baseDetActivity_le`, `sum_norm_baseDetActivity_le`: exponential decay in the size of the
  polymer, `M = ½ N B (1+ν)`, `λ = κ - log 2 - 2 log (detDeg d L + 1)`.
-/

@[expose] public section

namespace Balaban.LargeField.Base

open Matrix Balaban Balaban.Multiscale Balaban.Localization Balaban.Analysis Balaban.Fluctuation
  Balaban.SmallField.Def6

section Activity

variable {d L N₁ m₁ N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ} {m₀ : ℕ}
  {G : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ} {a : ℕ → ℝ} {aT ν Cx : ℝ}
  {φ : Balaban.Localization.CTorus d L N₁ m₁ 1 → Fin N → ℂ} {α : G.Ω 1 → ℂ}

/-- **The activity of the polymer `Y` for the root block `y` of the first step.** -/
noncomputable def baseDetActivity (m₀ : ℕ) (G : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ) (a : ℕ → ℝ)
    (aT ν : ℝ) (φ : Balaban.Localization.CTorus d L N₁ m₁ 1 → Fin N → ℂ) (α : G.Ω 1 → ℂ)
    (y : unitPts G)
    (Y : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := 1) m₀ 1 Set.univ)) : ℂ :=
  detActivityOf m₀ y (rootTraceBase G a aT ν φ α y) Y

/-- **Resummation** (`T2`): the rooted trace of the first step at `s = 1` is the sum of the
activities over all polymers. -/
theorem sum_baseDetActivity_eq (d L N : ℕ) [NeZero L] (m₀ : ℕ) (κ : ℝ) (hκ : 0 < κ) :
    ∀ {N₁ m₁ : ℕ} [NeZero N₁] {ϱ : ℝ} {G : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ}
      {a : ℕ → ℝ} {aT ν Cx : ℝ}
      (_S : Dec2.XCover (coverOf G) G a aT ν Cx) (_hdg : DGSetting G a ν) (_hconn : HatConn G)
      (_hCx : 0 ≤ Cx) (_hM : Dec2.cstarX d L Cx * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
      {δ : ℝ} (_hδ : 0 ≤ δ) (_hsm : δ ^ 2 * smallConstX d L κ ≤ 1 / 4)
      (_ha0 : a 0 = 2) (_ha1 : 0 ≤ a 1) (_ha1' : a 1 ≤ 2)
      (_haT : aT = 2 * a 1 * (L : ℝ) ^ 2 / (2 * (L : ℝ) ^ 2 - a 1))
      {φ : Balaban.Localization.CTorus d L N₁ m₁ 1 → Fin N → ℂ}
      (_hφ : IsConstraintFieldStrict G δ φ) {α : G.Ω 1 → ℂ}
      (_hα : ∀ w, ‖α w‖ < coerciveConst d / (2 * (G.spacing
        (w : Balaban.Localization.CTorus d L N₁ m₁ 1)) ^ 2))
      (y : unitPts G),
      rootTraceBase G a aT ν φ α y (fun _ => 1) =
        ∑ Y, baseDetActivity m₀ G a aT ν φ α y Y := by
  obtain ⟨B, -, H⟩ := rootTraceBase_cut_expansion d L N κ hκ
  intro N₁ m₁ _ ϱ G a aT ν Cx S hdg hconn hCx hM δ hδ hsm ha0 ha1 ha1' haT φ hφ α hα  y
  obtain ⟨hsum, -⟩ := H S hCx hM hδ hsm ha0 ha1 ha1' haT hφ hα y
  exact sum_detActivityOf_eq m₀ y (F := rootTraceBase G a aT ν φ α y) hsum

/-- **Support** (`T3`): a non-zero activity of the first step is supported on a polymer
containing the root cube. -/
theorem baseDetActivity_ne_zero_imp (d L N : ℕ) [NeZero L] (m₀ : ℕ) (κ : ℝ) :
    ∀ {N₁ m₁ : ℕ} [NeZero N₁] {ϱ : ℝ} {G : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ}
      {a : ℕ → ℝ} {aT ν Cx : ℝ}
      (_S : Dec2.XCover (coverOf G) G a aT ν Cx) (_hdg : DGSetting G a ν) (_hconn : HatConn G)
      (_hCx : 0 ≤ Cx) (_hM : Dec2.cstarX d L Cx * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
      {δ : ℝ} (_hδ : 0 ≤ δ) (_hsm : δ ^ 2 * smallConstX d L κ ≤ 1 / 4)
      (_ha0 : a 0 = 2) (_ha1 : 0 ≤ a 1) (_ha1' : a 1 ≤ 2)
      (_haT : aT = 2 * a 1 * (L : ℝ) ^ 2 / (2 * (L : ℝ) ^ 2 - a 1))
      {φ : Balaban.Localization.CTorus d L N₁ m₁ 1 → Fin N → ℂ}
      (_hφ : IsConstraintFieldStrict G δ φ) {α : G.Ω 1 → ℂ}
      (_hα : ∀ w, ‖α w‖ < coerciveConst d / (2 * (G.spacing
        (w : Balaban.Localization.CTorus d L N₁ m₁ 1)) ^ 2))
      (_hN : L ^ m₀ ∣ N₁) (_hκ : 0 ≤ κ) (y : unitPts G)
      (Y : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := 1) m₀ 1 Set.univ)),
      baseDetActivity m₀ G a aT ν φ α y Y ≠ 0 →
        rootCube (m₀ := m₀) (rootIdxOf y) ∈ Y ∧ IsPolyDom m₀ 1 (sitesOf Y) := by
  intro N₁ m₁ _ ϱ G a aT ν Cx S hdg hconn hCx hM δ hδ hsm ha0 ha1 ha1' haT φ hφ α hα  hN hκ0 y Y h
  exact detActivityOf_ne_zero_imp (m₀ := m₀) hdg hconn hN
    (rootSupported_rootTraceBase hdg S hCx hκ0 hM hδ hsm (fun w => (hα w).le) hφ.toIsConstraintField
      hconn y) h

/-- **Decay** (`T4`): the activity of the first step decays exponentially in the size of the
polymer: with `Δ = detDeg d L + 1`, `z = Δ² · 2 / e^κ < 1` and `λ = κ - log 2 - 2 log Δ`,
`‖baseDetActivity y Y‖ ≤ M / (1 - z) exp(-(λ/(2 d L)) dExt Y)`, `M = ½ N B (1+ν)`. -/
theorem norm_baseDetActivity_le (d L N : ℕ) [NeZero L] (m₀ : ℕ) (κ : ℝ) (hκ : 0 < κ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ {N₁ m₁ : ℕ} [NeZero N₁] {ϱ : ℝ}
      {G : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ} {a : ℕ → ℝ} {aT ν Cx : ℝ}
      (_S : Dec2.XCover (coverOf G) G a aT ν Cx) (_hdg : DGSetting G a ν) (_hconn : HatConn G)
      (_hCx : 0 ≤ Cx) (_hM : Dec2.cstarX d L Cx * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
      {δ : ℝ} (_hδ : 0 ≤ δ) (_hsm : δ ^ 2 * smallConstX d L κ ≤ 1 / 4)
      (_ha0 : a 0 = 2) (_ha1 : 0 ≤ a 1) (_ha1' : a 1 ≤ 2)
      (_haT : aT = 2 * a 1 * (L : ℝ) ^ 2 / (2 * (L : ℝ) ^ 2 - a 1))
      {φ : Balaban.Localization.CTorus d L N₁ m₁ 1 → Fin N → ℂ}
      (_hφ : IsConstraintFieldStrict G δ φ) {α : G.Ω 1 → ℂ}
      (_hα : ∀ w, ‖α w‖ < coerciveConst d / (2 * (G.spacing
        (w : Balaban.Localization.CTorus d L N₁ m₁ 1)) ^ 2))
      (_hN : L ^ m₀ ∣ N₁) (_hz : ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp κ) < 1)
      (y : unitPts G)
      (Y : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := 1) m₀ 1 Set.univ)),
      ‖baseDetActivity m₀ G a aT ν φ α y Y‖ ≤
        ((1 / 2 : ℝ) * N * (B * (1 + ν))) /
          (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp κ)) *
        Real.exp (-((κ - Real.log 2 - 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) /
          (2 * d * L)) * dExt Y) := by
  obtain ⟨B, hB0, H⟩ := rootTraceBase_cut_expansion d L N κ hκ
  refine ⟨B, hB0, ?_⟩
  intro N₁ m₁ _ ϱ G a aT ν Cx S hdg hconn hCx hM δ hδ hsm ha0 ha1 ha1' haT φ hφ α hα  hN hz y Y
  obtain ⟨-, hbound⟩ := H S hCx hM hδ hsm ha0 ha1 ha1' haT hφ hα y
  exact norm_detActivityOf_le (m₀ := m₀) hdg hconn hN y
    (rootSupported_rootTraceBase hdg S hCx hκ.le hM hδ hsm (fun w => (hα w).le)
      hφ.toIsConstraintField hconn y) hbound hz Y

/-- **Decay, summed form** (`T5`). -/
theorem sum_norm_baseDetActivity_le (d L N : ℕ) [NeZero L] (m₀ : ℕ) (κ : ℝ) (hκ : 0 < κ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ {N₁ m₁ : ℕ} [NeZero N₁] {ϱ : ℝ}
      {G : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ} {a : ℕ → ℝ} {aT ν Cx : ℝ}
      (_S : Dec2.XCover (coverOf G) G a aT ν Cx) (_hdg : DGSetting G a ν) (_hconn : HatConn G)
      (_hCx : 0 ≤ Cx) (_hM : Dec2.cstarX d L Cx * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
      {δ : ℝ} (_hδ : 0 ≤ δ) (_hsm : δ ^ 2 * smallConstX d L κ ≤ 1 / 4)
      (_ha0 : a 0 = 2) (_ha1 : 0 ≤ a 1) (_ha1' : a 1 ≤ 2)
      (_haT : aT = 2 * a 1 * (L : ℝ) ^ 2 / (2 * (L : ℝ) ^ 2 - a 1))
      {φ : Balaban.Localization.CTorus d L N₁ m₁ 1 → Fin N → ℂ}
      (_hφ : IsConstraintFieldStrict G δ φ) {α : G.Ω 1 → ℂ}
      (_hα : ∀ w, ‖α w‖ < coerciveConst d / (2 * (G.spacing
        (w : Balaban.Localization.CTorus d L N₁ m₁ 1)) ^ 2))
      (_hN : L ^ m₀ ∣ N₁) (y : unitPts G) {κ'' : ℝ} (_hκ0 : 0 ≤ κ'')
      (_hκ'' : κ'' * (2 * d * L) <
        κ - Real.log 2 - 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)),
      ∑ Y, ‖baseDetActivity m₀ G a aT ν φ α y Y‖ * Real.exp (κ'' * dExt Y) ≤
        ((1 / 2 : ℝ) * N * (B * (1 + ν))) /
          (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 *
            (2 / Real.exp κ * Real.exp (κ'' * (2 * d * L)))) := by
  obtain ⟨B, hB0, H⟩ := rootTraceBase_cut_expansion d L N κ hκ
  refine ⟨B, hB0, ?_⟩
  intro N₁ m₁ _ ϱ G a aT ν Cx S hdg hconn hCx hM δ hδ hsm ha0 ha1 ha1' haT φ hφ α hα  hN y κ'' hκ0 hκ''
  obtain ⟨-, hbound⟩ := H S hCx hM hδ hsm ha0 ha1 ha1' haT hφ hα y
  exact sum_norm_detActivityOf_le (m₀ := m₀) hdg hconn hN y
    (rootSupported_rootTraceBase hdg S hCx hκ.le hM hδ hsm (fun w => (hα w).le)
      hφ.toIsConstraintField hconn y) hbound hκ0 hκ''

end Activity

end Balaban.LargeField.Base
