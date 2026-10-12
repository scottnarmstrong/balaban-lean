/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.MassChangeWall

/-!
# The whole-lattice mass-change chord (INTERFACE-A (1.1)-(1.2))

For `D` the whole torus the flux vanishes (`starPair_univ`), so `A(φ⁰) - A(φᵐ)` is the stationary
chord (`massChange_univ_chord`), and the chord bound
`β|ΔA| ≤ 2 C_H K₂² B_h² β m² n` follows from the mass response `|w| ≤ 2 K₂ B_h m` and the Hessian
bound.  The response is the open input: `WeightedProp51S` / `lemma41_uncond` compare data at fixed
`ν` and `h` and do not apply to the mass source `m(φᵐ - h)` directly (WALL-COLLAR §1).
-/

@[expose] public section

namespace Balaban.LargeField.ActionConv

open Balaban.Multiscale Balaban.Background Balaban.Fluctuation Finset

variable {d L N₀ K N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ K ϱ}

/-- **The whole-lattice chord bound** (INTERFACE-A (1.2)); hypotheses `hresp` (mass response,
`K₂ B_h` as in the note) and `hHess` (`|⟨w,(H+α)w⟩| ≤ C_H n (2 K₂ B_h m)²`) are the open inputs. -/
theorem massChange_univ_bound (D : Region G) (hD : D.sites = Finset.univ) {a : ℕ → ℝ} {ν : ℝ}
    {Dat : BgData G N} {φ0 φm : G.Ω 1 × Fin N → ℂ} {α : G.Ω 1 → ℂ} (hEL : IsEL G a ν Dat φm α)
    (hφ0 : ∀ x : G.Ω 1, ∑ i, φ0 (x, i) * φ0 (x, i) = 1)
    {β m K2 Bh CH n : ℝ} (hβ : 0 ≤ β)
    (hHess : ‖2 * massChangeChord D a ν Dat φ0 φm α‖ ≤ CH * n * (2 * K2 * Bh * m) ^ 2) :
    β * ‖actionRegionC D a ν Dat φ0 - actionRegionC D a ν Dat φm‖ ≤
      2 * CH * K2 ^ 2 * Bh ^ 2 * β * m ^ 2 * n := by
  rw [massChange_univ_chord D hD hEL hφ0]
  have hc : ‖massChangeChord D a ν Dat φ0 φm α‖ ≤ (1 / 2) * (CH * n * (2 * K2 * Bh * m) ^ 2) := by
    rw [norm_mul] at hHess
    have : ‖(2 : ℂ)‖ = 2 := by simp
    rw [this] at hHess
    linarith
  calc β * ‖massChangeChord D a ν Dat φ0 φm α‖
      ≤ β * ((1 / 2) * (CH * n * (2 * K2 * Bh * m) ^ 2)) := mul_le_mul_of_nonneg_left hc hβ
    _ = _ := by ring

end Balaban.LargeField.ActionConv
