/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.XiCompose
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The quadratic complex square estimate in scaled composition

The proof of scaled composition bounds the real and complex square deficits separately at
order theta squared. Their difference has the same order, although the field of ScaledPsiC
records a weaker estimate.
-/

@[expose] public section

namespace Balaban.SmallField

open Balaban.Background Balaban.Multiscale Matrix Finset

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ ϱ' : ℝ}
  {G : GeneratingSet d L N₀ k ϱ} {G' : GeneratingSet d L N₀ k ϱ'}
  {a₁ ν δ ε η θ : ℝ} {j : ℕ}
  {Ψ0 : Torus d (N₀ * L ^ k) → Fin N → ℝ} {h0 : Fin N → ℝ}
  {Ψ'' h'' : Torus d (N₀ * L ^ k) → Fin N → ℂ}
  {φr φc : G'.Ω 1 × Fin N → ℂ}

/-- The complex square displacement of a composed datum has two powers of the scale gap. -/
theorem HypS.comp_square_sharp
    (H : HypS G G' a₁ ν δ ε η θ j Ψ0 h0 Ψ'' h'' φr φc)
    {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.Ω 1) :
    ‖∑ i, ccv G G' a₁ φc Ψ0 Ψ'' x i * ccv G G' a₁ φc Ψ0 Ψ'' x i -
      ∑ i, crv G G' a₁ φr Ψ0 x i * crv G G' a₁ φr Ψ0 x i‖
      ≤ θ ^ 2 * η * (2 * d + 10) := by
  have hP := H.hPC.toInPsiTilde
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hη6 : η ≤ 1 / 6 := by nlinarith [H.hsmall]
  have hδ0 := H.hδ
  have hMr : ∀ y ∈ G.blk (G.layerIndex x) x,
      vn (barVec G' (psiR Ψ0) φr y) ≤ 1 := fun y hy =>
    (barVec_vn_eq_one H.hφr H.hbr.unit _ (blk_mem_Ω1' H.prec hx hy).2).le
  have hMc : ∀ y ∈ G.blk (G.layerIndex x) x,
      vn (barVec G' (psiC Ψ0 Ψ'') φc y) ≤ 3 := by
    intro y hy
    have hy2 := (blk_mem_Ω1' H.prec hx hy).2
    have hyd : y ∈ dataSites G' := (mem_dataSites G').2 (Or.inl hy2)
    have e : barVec G' (psiC Ψ0 Ψ'') φc y =
        fun i => (φc (⟨y, hy2⟩, i) - psiC Ψ0 Ψ'' y i) + psiC Ψ0 Ψ'' y i := by
      funext i
      rw [barVec_of_mem _ φc hy2]
      ring
    rw [e]
    refine (vn_add' _ _).trans ?_
    have h1 := H.hbc.close ⟨y, hy2⟩
    have e2 : psiC Ψ0 Ψ'' y = fun i => (psiR Ψ0 y i) + Ψ'' y i := by
      funext i
      simp [psiC, psiR]
    have h2 : vn (psiC Ψ0 Ψ'' y) ≤ vn (psiR Ψ0 y) + vn (Ψ'' y) := by
      rw [e2]
      exact vn_add' _ _
    have h3 : vn (psiR Ψ0 y) ≤ 1 + δ := by
      have e3 : psiR Ψ0 y = fun i => (Ψ0 y i : ℂ) := rfl
      rw [e3, vn_ofReal]
      have hh := hP.r2 y hyd
      rw [← rn_sq_sum] at hh
      have h4 := rn_nonneg (Ψ0 y)
      have h5 := (abs_lt.1 hh).2
      by_contra hcon
      push Not at hcon
      nlinarith [sq_nonneg δ]
    have h6 := H.hPC.c2a y hyd
    have h7 : vn (fun i => φc (⟨y, hy2⟩, i) - psiC Ψ0 Ψ'' y i) ≤ η := h1
    linarith [H.hε1, H.hδη, hη6]
  have hc := H.hc.dot_sub_one hx hMc
  have hr := H.hr.dot_sub_one hx hMr
  have hc' : ‖∑ i, ccv G G' a₁ φc Ψ0 Ψ'' x i * ccv G G' a₁ φc Ψ0 Ψ'' x i - 1‖ ≤
      (2 * d * (θ * η)) ^ 2 + 2 * θ ^ 2 * 3 * η + (θ ^ 2) ^ 2 * η ^ 2 := by
    simpa only [ccv] using hc
  have hr' : ‖∑ i, crv G G' a₁ φr Ψ0 x i * crv G G' a₁ φr Ψ0 x i - 1‖ ≤
      (2 * d * (θ * η)) ^ 2 + 2 * θ ^ 2 * 1 * η + (θ ^ 2) ^ 2 * η ^ 2 := by
    simpa only [crv] using hr
  have e : ∑ i, ccv G G' a₁ φc Ψ0 Ψ'' x i * ccv G G' a₁ φc Ψ0 Ψ'' x i -
      ∑ i, crv G G' a₁ φr Ψ0 x i * crv G G' a₁ φr Ψ0 x i =
      (∑ i, ccv G G' a₁ φc Ψ0 Ψ'' x i * ccv G G' a₁ φc Ψ0 Ψ'' x i - 1) -
      (∑ i, crv G G' a₁ φr Ψ0 x i * crv G G' a₁ φr Ψ0 x i - 1) := by ring
  rw [e]
  calc
    _ ≤ ‖∑ i, ccv G G' a₁ φc Ψ0 Ψ'' x i * ccv G G' a₁ φc Ψ0 Ψ'' x i - 1‖ +
        ‖∑ i, crv G G' a₁ φr Ψ0 x i * crv G G' a₁ φr Ψ0 x i - 1‖ :=
      norm_sub_le _ _
    _ ≤ θ ^ 2 * η * (d + 7) + θ ^ 2 * η * (d + 3) := by
      have b3 := b2_le hd0 H.ηpos H.hθ0 H.hθ1 H.hsmall (M := 3)
      have b1 := b2_le hd0 H.ηpos H.hθ0 H.hθ1 H.hsmall (M := 1)
      nlinarith only [hc', hr', b3, b1]
    _ = θ ^ 2 * η * (2 * d + 10) := by ring

end Balaban.SmallField
