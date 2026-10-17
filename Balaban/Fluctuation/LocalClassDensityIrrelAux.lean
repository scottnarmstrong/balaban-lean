/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalClassDensityFamilySetCast

/-!
# Auxiliary facts for the class chain with irrelevant parts as labels (`LocalClassDensityIrrelAux`)

* `exists_finer_torus`: for `3^4 ∣ N₁` there is `N₁'` with `N₁' 3^{m₁+4} = N₁ 3^{m₁}`
  (the finer cube torus of `settings_family_castLocalB`);
* `bgR0_le_rhoSep`: `bgR0 3 3 ≤ rhoSep m₁`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Multiscale Balaban.Background Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.SmallField.Def6v2 Finset

/-- A finer cube torus with the same number of sites. -/
theorem exists_finer_torus {N₁ : ℕ} [NeZero N₁] (m₁ : ℕ) (h : 3 ^ 4 ∣ N₁) :
    ∃ (N₁' : ℕ) (_ : NeZero N₁'), N₁' * 3 ^ (m₁ + 4) = N₁ * 3 ^ m₁ := by
  obtain ⟨c, hc⟩ := h
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact NeZero.ne N₁ (by simpa using hc)
  refine ⟨c, ⟨hc0⟩, ?_⟩
  rw [hc, pow_add]
  ring

theorem bgR0_le_rhoSep (m₁ : ℕ) : bgR0 3 3 ≤ Localization.I5Inhabited.rhoSep m₁ := by
  unfold Localization.I5Inhabited.rhoSep
  have := Localization.I5Inhabited.rhoSep_tail_nonneg
  have h3 : (0 : ℝ) ≤ 3 ^ m₁ := by positivity
  linarith

end Balaban.Fluctuation
