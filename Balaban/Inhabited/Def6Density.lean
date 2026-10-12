/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.Def6Inhabited
public import Balaban.Inhabited.XiCDomains
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The small-field density witness is not identically zero

`rhoZero` (`Balaban/SmallField/Def6Inhabited.lean`) is the density `χ_k exp[-β_k A_k + ⟨g, φ_k⟩]`
of the zero effective action; it vanishes off the support `Ξ_k` of `χ_k`.  This file proves that the
domain `Ξ_k(𝔹_k; 1, p(β_k)/√β_k)` is non-empty for the witness parameters (`exists_xi`: the constant
unit datum is a member for every `ε > 0`), hence `rhoZero > 0` there (`rhoZero_pos`), so the
density of the class witness `isSFFamily_witness` is not identically zero
(`rhoZero_witness_ne_zero`).
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.SmallField.Def6
  Balaban.Localization Balaban.Fluctuation

section Xi

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- **`Ξ_k(𝔹; 1, ε)` is non-empty for every `ε > 0`** (real data): the constant unit datum. -/
theorem exists_xi {a : ℕ → ℝ} {ν : ℝ} (H : BgHyp d L k ϱ a ν) (G : GeneratingSet d L N₀ k ϱ)
    (hN : 0 < N) {ε : ℝ} (hε : 0 < ε) :
    Xi G a ν k 1 ε (fun _ : Torus d (N₀ * L ^ k) => unitVec hN) (unitVec hN) := by
  have hK := bgK1_pos d L N
  have hc1 := bgC1_pos' (d := d) (L := L) (N := N) (by have := H.hd; omega)
  set δ : ℝ := min (ε / (bgK1 d L N + 1)) (bgC1 d L N) with hδ
  have hden : 0 < bgK1 d L N + 1 := by positivity
  have hδ0 : 0 < δ := by positivity
  have hδc : δ ≤ bgC1 d L N := min_le_right _ _
  have hδε : δ ≤ ε / (bgK1 d L N + 1) := min_le_left _ _
  have hP := (exists_inPsiTildeC (G := G) (N := N) hN ν hδ0 hδ0).toInPsiTilde
  have hX := psiTilde_subset_xiAt (a := a) H hδ0 hδc hP (εb := ε) (by
    rw [le_div_iff₀ hden] at hδε; nlinarith)
  exact ⟨one_pos, hε, _, hX⟩

end Xi

section Density

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- `rhoZero` is strictly positive wherever `Ξ_k` holds. -/
theorem rhoZero_pos (P : Consts) (β ν a : ℕ → ℝ)
    (Ψ₀ : CTorus d L N₁ m₁ k → Fin N → ℝ) (h₀ : Fin N → ℝ)
    (g : CTorus d L N₁ m₁ k → Fin N → ℝ)
    (hX : Xi (topGS d L N₁ m₁ k ϱ) (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) k 1
      (P.p (β k) / Real.sqrt (β k)) Ψ₀ h₀) :
    0 < rhoZero (N₁ := N₁) (m₁ := m₁) (N := N) (ϱ := ϱ) P β ν a Ψ₀ h₀ g := by
  classical
  unfold rhoZero
  simp only [hX, ↓reduceDIte]
  exact Real.exp_pos _

end Density

section Witness

/-- **The density of the class witness is not identically zero**: for the witness parameters of
`isSFFamily_witness` the domain `Ξ_k` is non-empty (the constant unit datum) and `rhoZero > 0`
there. -/
theorem rhoZero_witness_ne_zero (m₁ k j : ℕ) (ϱ : ℝ) (hϱ : bgR0 3 3 ≤ ϱ) (N₁ : ℕ) [NeZero N₁] :
    ∃ (Ψ₀ : CTorus 3 3 N₁ m₁ k → Fin 2 → ℝ) (h₀ : Fin 2 → ℝ)
      (g : CTorus 3 3 N₁ m₁ k → Fin 2 → ℝ),
      Xi (topGS 3 3 N₁ m₁ k ϱ) (aIdeal 3 k (witnessa k)) (bgMass 3 k (witnessβ k) (witnessν k k)) k 1
        ((witnessConsts (witnessα₀ j)).p (witnessβ k) / Real.sqrt (witnessβ k)) Ψ₀ h₀ ∧
      0 < rhoZero (N₁ := N₁) (m₁ := m₁) (N := 2) (ϱ := ϱ) (witnessConsts (witnessα₀ j)) witnessβ
        (witnessν k) witnessa Ψ₀ h₀ g := by
  have H := bgHyp_of_class (witnessConsts_admissible (witnessα₀_pos j))
    (witness_coeff k) le_rfl le_rfl hϱ
  have hε : 0 < (witnessConsts (witnessα₀ j)).p (witnessβ k) / Real.sqrt (witnessβ k) := by
    simp only [witnessConsts, witnessβ]; positivity
  have hX := exists_xi (N := 2) H (topGS 3 3 N₁ m₁ k ϱ) (by norm_num) hε
  exact ⟨_, _, fun _ _ => 0, hX, rhoZero_pos _ _ _ _ _ _ _ hX⟩

end Witness

end Balaban.Inhabited
