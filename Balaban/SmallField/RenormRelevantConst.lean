/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.RenormExpBounds

/-!
# The background of constant data on a whole-lattice level

For a whole-lattice generating set of level `n` (`IsLevel G n`: `Ω₁` is the whole torus, the collar is
empty) and constant data `Ψ ≡ c e`, `h̃ ≡ c' e` along a unit direction `e`, the constant field
`φ ≡ e` solves (EL) with the constant multiplier
`α = a_n L^{-2n} (c − 1) + ν (c' − 1)`.  This is the explicit reference background of the relevant
parts of the renormalization conditions (no Green function is needed).
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Background Matrix

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ k ϱ} {n : ℕ}

theorem IsLevel.collar_eq (hG : IsLevel G n) : collar G = ∅ := by
  ext x
  simp only [Finset.notMem_empty, iff_false]
  intro hx
  exact ((mem_collar G).1 hx).1 (hG x).1

theorem IsLevel.dataSites_eq (hG : IsLevel G n) : dataSites G = Finset.univ := by
  ext x
  simp only [Finset.mem_univ, iff_true]
  exact (mem_dataSites G).2 (Or.inl (hG x).1)

/-- The constant datum `(Ψ, h̃) ≡ (ψ, h)` on a whole-lattice level. -/
noncomputable def constBg (hG : IsLevel G n) (ψ h : Fin N → ℂ) : BgData G N where
  Ψ := fun _ => ψ
  h := fun _ => h
  Ψ_layerConst := fun _ _ _ _ _ _ _ => rfl
  h_layerConst := fun _ _ _ _ _ _ _ => rfl
  Ψ_zero := fun x hx => absurd (by rw [hG.dataSites_eq]; exact Finset.mem_univ x) hx
  h_zero := fun x hx => absurd (hG x).1 hx

/-- **The constant background solves (EL)**: `φ ≡ e` with the multiplier
`α ≡ a_n L^{-2n}(c − 1) + ν (c' − 1)`. -/
theorem isEL_const (hG : IsLevel G n) (a : ℕ → ℝ) (ν : ℝ) (e : Fin N → ℂ) (he : ∑ i, e i * e i = 1)
    (c c' : ℂ) :
    IsEL G a ν (constBg hG (c • e) (c' • e)) (fun p => e p.2)
      (fun _ => ((a n / ((L : ℝ) ^ n) ^ 2 : ℝ) : ℂ) * (c - 1) + ν * (c' - 1)) := by
  refine ⟨?_, fun x => he⟩
  funext ⟨x, i⟩
  rw [liftOp_mulVec, dirichlet_apply]
  have hz : zeroExt (G.Ω 1) (fun z : G.Ω 1 => e i) = fun _ => e i := by
    funext y; exact zeroExt_mem _ _ ⟨y, (hG y).1⟩
  rw [hz]
  have hx : G.layerIndex (x : Torus d (N₀ * L ^ k)) = n := (hG x).2
  have hcard := card_blk_cast G (G.layerIndex (x : Torus d (N₀ * L ^ k)))
    (G.layerIndex_spec x.2).2.1 x
  have hLd : (0 : ℝ) < ((L : ℝ) ^ n) ^ d := by
    have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  have hnl : negLap (fun _ : Torus d (N₀ * L ^ k) => e i) x = 0 := by
    simp [negLap]; ring
  have hbt : blockTerm G a (fun _ : Torus d (N₀ * L ^ k) => e i) x =
      ((a n / ((L : ℝ) ^ n) ^ 2 : ℝ) : ℂ) * e i := by
    unfold blockTerm
    rw [hx]
    rw [hx] at hcard
    simp only [Finset.sum_const, nsmul_eq_mul]
    have : ((G.blk n x).card : ℂ) = (((L : ℝ) ^ n) ^ d : ℝ) := by exact_mod_cast hcard
    rw [this]
    push_cast
    have hL0 : ((L : ℂ) ^ n) ≠ 0 := pow_ne_zero _ (by exact_mod_cast NeZero.ne L)
    have hLd0 : ((L : ℂ) ^ n) ^ d ≠ 0 := pow_ne_zero _ hL0
    field_simp
  rw [hnl, hbt]
  simp only [source, qStar, boundaryTerm, constBg, hG.collar_eq, Finset.notMem_empty, ↓reduceIte,
    Finset.sum_const_zero, add_zero, hx, Pi.smul_apply, smul_eq_mul]
  push_cast
  ring

end Balaban.Fluctuation
