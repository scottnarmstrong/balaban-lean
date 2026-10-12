/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.PsiZeroWitnessSpec

/-!
# A non-constant datum for `psiZero_exists_unique` (instance of `PsiZeroWitness`)

The block datum `ψ_θ` equals `e₀ = (1, 0)` except on the blocks `z` with `z_{i₀} = 2` (a slab outside the
box `box 0 (2,…,2)`), where it equals the rotated unit vector `(cos θ, sin θ)`.  For `0 < θ < δ` it lies in the
tube `Ψ̃(X ∖ Z₀; δ)` (strict inequalities), so `psiZero_exists_unique` applies to it for every `δ ≤ c₁₁`:
the reference minimizer exists and is unique for a datum that is not constant, even on the layer of the box.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField.Def6 Balaban.Fluctuation
  Balaban.Inhabited

namespace PsiZeroWitness

variable {d L N₁ m₁ k : ℕ} [NeZero L] [NeZero N₁]

/-- The rotated unit vector `(cos θ, sin θ)`. -/
noncomputable def rotVec (θ : ℝ) : Fin 2 → ℝ := ![Real.cos θ, Real.sin θ]

/-- The tilted datum: `(cos θ, sin θ)` on the slab `z_{i₀} = 2`, `e₀` elsewhere. -/
noncomputable def ψTilt (i0 : Fin d) (θ : ℝ) : BlockField d L (N₁ * L ^ m₁) k 2 :=
  fun z => if z i0 = 2 then rotVec θ else ![1, 0]

theorem rn_rot_sub_e0 {θ δ : ℝ} (hθ : 0 < θ) (hδ : θ < δ) :
    rn (fun i => rotVec θ i - ![(1 : ℝ), 0] i) < δ := by
  unfold rn
  rw [Real.sqrt_lt' (by linarith)]
  simp only [Fin.sum_univ_two, rotVec]
  simp
  have h1 := Real.one_sub_sq_div_two_le_cos (x := θ)
  have h2 := Real.sin_sq_add_cos_sq θ
  nlinarith

theorem tube_ψTilt (i0 : Fin d) {θ δ : ℝ} (hθ : 0 < θ) (hδ : θ < δ)
    (Y : Set (Torus d (N₁ * L ^ m₁ * L ^ (k - k)))) :
    TubeOn (G d L N₁ m₁ k) Y δ (ψTilt (m₁ := m₁) (k := k) i0 θ) := by
  have hδ0 : 0 < δ := hθ.trans hδ
  have hsub : rn (fun i => ![(1 : ℝ), 0] i - rotVec θ i) < δ := by
    unfold rn
    rw [Real.sqrt_lt' (by linarith)]
    simp only [Fin.sum_univ_two, rotVec]
    simp
    have h1 := Real.one_sub_sq_div_two_le_cos (x := θ)
    have h2 := Real.sin_sq_add_cos_sq θ
    nlinarith
  refine ⟨fun x x' _ _ _ => ?_, fun x _ _ => ?_⟩
  · unfold liftR ψTilt
    by_cases h1 : jBlock d L (N₁ * L ^ m₁) k k x i0 = 2 <;>
      by_cases h2 : jBlock d L (N₁ * L ^ m₁) k k x' i0 = 2 <;> simp only [h1, h2, ite_true, ite_false]
    · simpa [rn] using hδ0
    · exact rn_rot_sub_e0 hθ hδ
    · exact hsub
    · simpa [rn] using hδ0
  · unfold ψTilt
    by_cases h1 : jBlock d L (N₁ * L ^ m₁) k k x i0 = 2
    · simp only [h1, ite_true, rotVec, Fin.sum_univ_two]
      simpa [Real.sin_sq_add_cos_sq θ, add_comm] using hδ0
    · simpa [h1, Fin.sum_univ_two] using hδ0

/-- **Existence and uniqueness of `ψ⁰_k` for a non-constant datum**: for every `δ ≤ c₁₁` and every
`0 < θ < δ`, the tilted datum lies in the tube and there is exactly one solution of (2.34) in `Ψ̃(X; K₆ δ)`. -/
theorem psiZero_tilt (hd3 : 3 ≤ d) (hL : 3 ≤ L) (hN : 4 ≤ N₁) (hk : 1 ≤ k) (i0 : Fin d) :
    ∃ K c11 : ℝ, 0 < K ∧ 0 < c11 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ c11 → ∀ θ : ℝ, 0 < θ → θ < δ →
      TubeOn (G d L N₁ m₁ k) (X d L N₁ m₁ k \ box (b0 d L N₁ m₁ k) (w d)) δ
          (ψTilt (m₁ := m₁) (k := k) i0 θ) ∧
        ∃! ψ, PsiZeroSol (G d L N₁ m₁ k) (a L) (b0 d L N₁ m₁ k) (w d) (X d L N₁ m₁ k) (K * δ)
          (ψTilt (m₁ := m₁) (k := k) i0 θ) ψ := by
  obtain ⟨K, c11, hK, hc, h⟩ := psiZero_exists_unique (N := 2) (D := 2) (G d L N₁ m₁ k) (a L)
    (by omega) hk (b0 d L N₁ m₁ k) (w d) (hw1 d) (hwD d) (hm hN) (hXreg d L N₁ m₁ k)
    (hΩ d L N₁ m₁ k) (hdata d L N₁ m₁ k) (H hd3 hL)
  exact ⟨K, c11, hK, hc, fun δ h0 h1 θ hθ hθδ =>
    ⟨tube_ψTilt i0 hθ hθδ _, h δ h0 h1 _ (tube_ψTilt i0 hθ hθδ _)⟩⟩

/-- The tilted datum is not constant. -/
theorem ψTilt_ne_const (i0 : Fin d) {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (hN : 4 ≤ N₁) :
    ∃ y y' : Torus d (N₁ * L ^ m₁ * L ^ (k - k)),
      ψTilt (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) i0 θ y ≠ ψTilt i0 θ y' := by
  have hn : 4 ≤ N₁ * L ^ m₁ * L ^ (k - k) := by
    have : 1 ≤ L ^ m₁ := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (NeZero.ne L))
    simp only [Nat.sub_self, pow_zero, mul_one]
    nlinarith
  have h20 : (2 : ZMod (N₁ * L ^ m₁ * L ^ (k - k))) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod (N₁ * L ^ m₁ * L ^ (k - k))) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    have := Nat.le_of_dvd (by norm_num) h'
    omega
  refine ⟨fun _ => 2, fun _ => 0, fun h => ?_⟩
  have h0 := congrFun h 1
  simp [ψTilt, rotVec, h20.symm] at h0
  have h1 : Real.sin θ = 0 := h0
  have : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ (by linarith [Real.pi_gt_three])
  linarith

end PsiZeroWitness

end Balaban.LargeField
