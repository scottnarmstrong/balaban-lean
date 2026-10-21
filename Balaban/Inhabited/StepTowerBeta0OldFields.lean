/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.NewLevelSystem
public import Balaban.Localization.DecoupledBackground
public import Balaban.Localization.Decoupled2Solve

/-!
# The pinned decoupled fields of the inherited levels

Standalone existence of the decoupled fields `F₁L`, `SolL`, `FkL` of an `OldTermSystem` with their
pins `DecFieldPin`, `DecSolPin`, `FkPin`, from the core hypotheses `FlCore` of the step and the
background hypothesis `BgHyp` of the generating set `Gk`.  The chain
(`StepTowerCollarStruct`) obtains the same fields, analytic as well, from `i4b_analytic`,
`Dec2.i4a_analytic` and `theorem72_analytic`; the pins of `OldTermSystem` ask no analyticity.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Fluctuation Balaban.Multiscale Balaban.Background Balaban.Localization
  Balaban.SmallField Balaban.SmallField.Def6

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- **The decoupled background field of the step exists with its pin.** -/
theorem exists_decFieldPin (S : StepSetting d L N₁ m₁ k N ϱ)
    {c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ}
    (hC : FlCore N S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁) :
    ∃ F, DecFieldPin S κ BG F := by
  obtain ⟨F, -, hF⟩ := i4b_analytic hC.hS hC.Sp hC.HBp hC.hκ.le hC.hM
  exact ⟨F, fun s D hs hD φ α hdec => hF s D hs hD φ α hdec⟩

/-- **The decoupled fluctuation field of the step exists with its pin** (radii `δ₀ = 2 K₄ ξ ε`,
`δ₁`). -/
theorem exists_decSolPin (S : StepSetting d L N₁ m₁ k N ϱ)
    {c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ}
    (hC : FlCore N S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁) :
    ∃ Sol, DecSolPin S κ BG₂ (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ Sol := by
  have hd0 : 0 < d := by have := hC.HBp.hd; omega
  have hδ0 : 0 < xiC1 d * eps := by have := hC.eps_pos; have := one_le_xiC1 d; positivity
  have hB0 : 0 ≤ 2 * (K4 d L N BG κ * (xiC1 d * eps)) :=
    mul_nonneg (by norm_num) (mul_nonneg (K4_pos hC.hS.fam.2.1 hd0).le hδ0.le)
  obtain ⟨Sol, -, hSol⟩ := Dec2.i4a_analytic (N := N) hC.hS2.fam hC.hS2.an
    hC.SM.toCoverBase hC.hκ.le hC.hM2 false hB0 hC.δ₁_pos.le hC.B_le hC.δ₁_le
  exact ⟨Sol, fun p hp hd => hSol p hp hd⟩

/-- **The background field of a generating set exists with its pin.** -/
theorem exists_fkPin (S : StepSetting d L N₁ m₁ k N ϱ) {ϱ₁ : ℝ}
    (Gk : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁)
    (H : BgHyp d L (k + 1) ϱ₁ (compWeight L S.a₁) S.ν) : ∃ Fk, FkPin S Gk (N := N) Fk := by
  obtain ⟨F, -, hF⟩ := theorem72_analytic (G := Gk) (N := N) (a := compWeight L S.a₁) (ν := S.ν) H
  exact ⟨F, fun D hD => hF D hD⟩

end Balaban.Inhabited
