/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.NewLevelSystem

/-!
# Uniqueness of the pinned fields of a new-level system

The decoupled fields `F₁L`, `SolL`, `FkL`, `F₂`, `Sol₂`, `F₁`, `Sol` of a `NewLevelSystem` are returned
by the chain existentially, with the pins `DecFieldPin`, `DecSolPin`, `FkPin` as their only
properties. Two fields with the same pin agree on the domain of the pin
(`DecFieldPin.unique`, `DecSolPin.unique`, `FkPin.unique`): the values of a system's objects at the
arguments of its formulas do not depend on the choice of the pinned fields. This is the first rung of
the value-uniqueness of `AC`, `G₁` and the bridge marks (`notes/phase1/SPINE.md`, A4-1f).
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Fluctuation Balaban.Multiscale Balaban.Background Balaban.Localization
  Balaban.Polymer Balaban.SmallField Balaban.SmallField.Def6 MeasureTheory

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- Two decoupled background fields with the same pin agree at every datum of the pin's domain that
admits a decoupled background. -/
theorem DecFieldPin.unique {S : StepSetting d L N₁ m₁ k N ϱ} {κ BG : ℝ}
    {F F' : DecParams S.G' × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ)}
    (h : DecFieldPin S κ BG F) (h' : DecFieldPin S κ BG F') (s : DecParams S.G')
    (D : BgData S.G' N) (hs : ∀ P, ‖s P‖ < Real.exp κ)
    (hD : InUnionDomainC S.G' (bgC0 d L N) (c7 d L N BG κ) S.ν D)
    (φ : S.G'.Ω 1 × Fin N → ℂ) (α : S.G'.Ω 1 → ℂ)
    (hdec : IsDecBg S.G' (compWeight L S.a₁) S.ν (rho4 d L N BG κ) s D φ α) :
    F (s, rawOf D) = F' (s, rawOf D) :=
  (h s D hs hD φ α hdec).trans (h' s D hs hD φ α hdec).symm

/-- Two decoupled fluctuation fields with the same pin agree on the strict data. -/
theorem DecSolPin.unique {S : StepSetting d L N₁ m₁ k N ϱ} {κ BG₂ δ₀ δ₁ : ℝ}
    {Sol Sol' : Dec2.DecParams (coverOf S.G') × Edat (stepG d L N₁ m₁ k ϱ) N →
      ((stepG d L N₁ m₁ k ϱ).Ω 1 × Fin N → ℂ) × ((stepG d L N₁ m₁ k ϱ).Ω 1 → ℂ)}
    (h : DecSolPin S κ BG₂ δ₀ δ₁ Sol) (h' : DecSolPin S κ BG₂ δ₀ δ₁ Sol')
    (p : Dec2.DecParams (coverOf S.G') × Edat (stepG d L N₁ m₁ k ϱ) N)
    (hp : ∀ P, ‖p.1 P‖ < Real.exp κ) (hd : StrictDataM (stepG d L N₁ m₁ k ϱ) N false δ₀ δ₁ p.2) :
    Sol p = Sol' p := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := h p hp hd
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := h' p hp hd
  have h2 : (Sol' p).2 = (Sol p).2 := a6 (Sol' p).2 b3 b2
  refine Prod.ext ?_ h2.symm
  rw [a1, b1, h2]

/-- Two background fields of a generating set with the same pin agree on the union domain. -/
theorem FkPin.unique {S : StepSetting d L N₁ m₁ k N ϱ} {ϱ₁ : ℝ}
    {Gk : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁}
    {Fk Fk' : RawData d L (N₁ * L ^ m₁) (k + 1) N → ((Gk).Ω 1 × Fin N → ℂ) × ((Gk).Ω 1 → ℂ)}
    (h : FkPin S Gk Fk) (h' : FkPin S Gk Fk') (D : BgData Gk N)
    (hD : InUnionDomainC Gk (bgC0 d L N) (bgC1 d L N) S.ν D) : Fk (rawOf D) = Fk' (rawOf D) :=
  (h D hD).trans (h' D hD).symm

end Balaban.Inhabited
