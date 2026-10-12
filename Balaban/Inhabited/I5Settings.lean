/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.I5Inhabited
public import Balaban.Localization.I5FluctStep

/-!
# `BgSetting` and `DataAgreeS` are inhabited

* `bgSetting_nonempty`: `BgSetting` (hypotheses of Lemma DL, background part) has a member at
  positive scale (`d = L = 3`, `N₁ = 6`, `K = 2`, `j = 1`, `N = 2`, `ν = 0`, `a₁ = 1`), obtained from
  the `I5Witness` of `I5Inhabited`;
* `dataAgreeS_self`: every data set agrees with itself on every `Y`, `S` (the structure holds for
  any parameters with the two data sets equal).
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Localization

/-- **`BgSetting` is inhabited at positive scale.** -/
theorem bgSetting_nonempty :
    ∃ (m₁ : ℕ) (ϱ ϱ₁ ϱ₂ : ℝ) (Gp : GeneratingSet 3 3 (6 * 3 ^ m₁) 2 ϱ)
      (Gk : GeneratingSet 3 3 (6 * 3 ^ m₁) 2 ϱ₁) (Gj : GeneratingSet 3 3 (6 * 3 ^ m₁) 2 ϱ₂)
      (c BG κ r₀ eps δ₃ : ℝ) (X₀ X₁f : Finset (CTorus 3 3 6 m₁ 2)),
      Nonempty (BgSetting 2 Gp Gk Gj 1 0 c BG κ r₀ eps δ₃ X₀ X₁f 1) := by
  obtain ⟨W⟩ := I5Inhabited.nonempty_i5Witness
  exact ⟨W.m₁, W.ϱ, W.ϱ₁, W.ϱ₂, W.Gp, W.Gk, W.Gj, W.c, W.BG, W.κ, W.r₀, W.eps, W.δ₃, W.X₀, W.X₁f,
    ⟨W.hB⟩⟩

section DataAgree

open Dec2

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}

/-- **`DataAgreeS` is inhabited**: a data set agrees with itself. -/
theorem dataAgreeS_self (H : GeneratingSet d L (N₁ * L ^ m₁) K ϱ)
    (Y S : Finset (CTorus d L N₁ m₁ K)) (α₀ : H.Ω 1 → ℂ)
    (φ₀ δΨ : CTorus d L N₁ m₁ K → Fin N → ℂ) (f₁ : H.Ω 1 × Fin N → ℂ) :
    DataAgreeS H N Y S α₀ α₀ φ₀ φ₀ δΨ δΨ f₁ f₁ :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl⟩

end DataAgree

end Balaban.Inhabited
