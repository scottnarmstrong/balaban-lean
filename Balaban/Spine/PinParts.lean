/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.AgreeTransportRep
public import Balaban.Spine.FrozenLFStep
public import Balaban.Spine.LFStep

/-!
# The pins of the successor (row (g4)), pre-`R` and frozen

`lfPinInput` and `frozenPinInput` prove `LFPinInput` and `FrozenPinInput` for every step map: the
kept exponents and kept data of the successor are those of the input (`KeptData.upTo`), every
history of the successor agrees up to `k` with a history of the input (completeness of the input),
and the pin of the input is transported along `Agree` (`d4Pin_of_agree`). In a frozen step the new
scale `k + 1` lies above `k₀`, where no component is kept, so the pin there is vacuous.
-/

@[expose] public section

open Balaban Balaban.LargeField Balaban.LargeField.Def7 Balaban.LargeField.Def7v2 Balaban.Multiscale
  Balaban.SmallField Balaban.SmallField.Def6v2

namespace Balaban.RootFSpine

section

variable {d N : ℕ} {T : ℝ → ℝ → Typing} {P6 : ℝ → ℝ → Def6.Consts}
  {C7 : ℝ → ℝ → Consts7} {PB : ℝ → ℝ → BudgetConsts} {cs₀ : ℝ → ℝ → OpConsts}
  {M1 c : ℝ → ℝ → ℕ} {rH ϱ : ℝ → ℝ → ℝ}
  {Φ : ∀ (κ c₉ _ _ : ℝ) (k : ℕ) [NeZero (T κ c₉).L],
    SFData d (T κ c₉).L (C7 κ c₉).m₁ k N (ϱ κ c₉) →
      SFData d (T κ c₉).L (C7 κ c₉).m₁ (k + 1) N (ϱ κ c₉)}

/-- **`LFPinInput` for every step map** (row (g4), (D4)). -/
theorem lfPinInput (Λ : LFStepMap d N T P6 C7 PB cs₀ M1 c rH ϱ) :
    LFPinInput d N T P6 C7 PB cs₀ M1 c rH ϱ Φ Λ := by
  intro κ _ c₉ _
  refine ⟨0, fun β _ ν _ _ h _ kf _ _ _ k hk1 hk ρ νk rec _ _ _ _ _ hkK' SD hM nK _ => ?_⟩
  exact d4Pin_of_agree (rec.F.lf nK) _ k rfl (fun _ _ => rfl) rfl rfl
    (fun i hi => vacExt_of_le _ hi.le) (rec.rep.pin nK) fun A _ => by
      obtain ⟨B, ⟨hB, hAB⟩, -⟩ := rec.rep.complete nK A
      exact ⟨B, hB, hAB⟩

/-- **`FrozenPinInput` for every frozen step map** (row (g4), (D4)): `D4Pin (k+1)` of the successor is
the transport of the input's pin, and at the new scale `k + 1 > k₀` no component is kept. -/
theorem frozenPinInput (Λ : FrozenLFStepMap d N T P6 C7 PB cs₀ M1 c rH ϱ) :
    FrozenPinInput d N T P6 C7 PB cs₀ M1 c rH ϱ Φ Λ := by
  intro κ _ c₉ _
  refine ⟨0, fun β _ ν _ _ h _ kf _ _ _ k hk1 hk0 hk ρ νk hM6 hkK R geo cs P F St vc hF _ _ _ _ _ _
    hkK' SD hM nK _ => ?_⟩
  obtain ⟨-, -, -, -, -, -, -, -, hrepF, -⟩ := hF
  rw [d4Pin_succ_iff]
  refine ⟨d4Pin_of_agree (F.lf nK) _ k rfl (fun _ _ => rfl) rfl rfl
    (fun i hi => vacExt_of_le _ hi.le) (hrepF.pin nK) fun A _ => by
      obtain ⟨B, ⟨hB, hAB⟩, -⟩ := hrepF.complete nK A
      exact ⟨B, hB, hAB⟩, fun _ A _ Z hK _ => ?_⟩
  exact absurd hK.2.1 (by omega)

end

end Balaban.RootFSpine
