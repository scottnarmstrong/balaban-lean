/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Background.Def5

/-!
# The Def-5 background is transported by an equivalence of the regions `Ω₁`

Let `G₁`, `G₂` be generating sets on two tori (possibly of different sizes) with data `D₁`, `D₂`.
An equivalence `e : Ω₁(G₁) ≃ Ω₁(G₂)` of the regions that carries the entries of the operator
`-Δ + ν + Q* a Q`, the source `S(Ψ, h̃)` and the spacing `ℓ(x)` carries the small solutions of (EL)
of `(G₁, D₁)` onto those of `(G₂, D₂)` (`isSmallSolution_equiv_iff`). Hence the two backgrounds
`bgFieldC` agree at corresponding sites (`bgFieldC_equiv`), including the case where the `∃!`
fails on both.
-/

@[expose] public section

namespace Balaban.Background

open Balaban.Multiscale Matrix Finset

section Equiv

variable {d L N₁ N₂ k N : ℕ} [NeZero N₁] [NeZero N₂] [NeZero L] {ϱ₁ ϱ₂ : ℝ}
  {G₁ : GeneratingSet d L N₁ k ϱ₁} {G₂ : GeneratingSet d L N₂ k ϱ₂} {a : ℕ → ℝ} {ν c₀ : ℝ}

/-- `(liftOp A φ)(x, i) = ∑_y A(x, y) φ(y, i)`. -/
theorem liftOp_mulVec_apply {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ)
    (φ : ι × Fin N → ℂ) (x : ι) (i : Fin N) :
    (liftOp N A *ᵥ φ) (x, i) = ∑ y, A x y * φ (y, i) := by
  classical
  simp only [Matrix.mulVec, dotProduct, liftOp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [Ne.symm hj]
  · simp

/-- The entries of the Dirichlet operator are entries of the whole-torus matrix plus `α`. -/
theorem dirichletOperator_apply (G : GeneratingSet d L N₁ k ϱ₁) (a : ℕ → ℝ) (ν : ℝ)
    (α : G.Ω 1 → ℂ) (x y : G.Ω 1) :
    dirichletOperator G a ν α x y =
      (fullMatrix G a ν (x : Torus d (N₁ * L ^ k)) (y : Torus d (N₁ * L ^ k)) : ℂ) +
        if x = y then α x else 0 := by
  classical
  simp [dirichletOperator, Green.restrictOp, Matrix.diagonal_apply]

variable (e : G₁.Ω 1 ≃ G₂.Ω 1)
  (hF : ∀ x y : G₁.Ω 1, fullMatrix G₂ a ν (e x : Torus d (N₂ * L ^ k)) (e y) =
    fullMatrix G₁ a ν (x : Torus d (N₁ * L ^ k)) y)
  {D₁ : BgData G₁ N} {D₂ : BgData G₂ N}
  (hS : ∀ (x : G₁.Ω 1) (i : Fin N), source G₂ a ν D₂ (e x, i) = source G₁ a ν D₁ (x, i))
  (hsp : ∀ x : G₁.Ω 1, G₂.spacing (e x : Torus d (N₂ * L ^ k)) = G₁.spacing (x : Torus d (N₁ * L ^ k)))

include hF hS in
/-- A solution of (EL) of `(G₁, D₁)`, pulled back to `G₂` along `e`, is a solution of (EL) of
`(G₂, D₂)` (and conversely). -/
theorem isEL_equiv_iff (φ : G₁.Ω 1 × Fin N → ℂ) (α : G₁.Ω 1 → ℂ) :
    IsEL G₂ a ν D₂ (fun p => φ (e.symm p.1, p.2)) (fun y => α (e.symm y)) ↔
      IsEL G₁ a ν D₁ φ α := by
  classical
  have hrow : ∀ (x : G₁.Ω 1) (i : Fin N),
      (liftOp N (dirichletOperator G₂ a ν (fun y => α (e.symm y))) *ᵥ
          (fun p : G₂.Ω 1 × Fin N => φ (e.symm p.1, p.2))) (e x, i) =
        (liftOp N (dirichletOperator G₁ a ν α) *ᵥ φ) (x, i) := by
    intro x i
    rw [liftOp_mulVec_apply, liftOp_mulVec_apply]
    refine Fintype.sum_equiv e.symm _ _ fun y => ?_
    rw [dirichletOperator_apply, dirichletOperator_apply]
    have h1 : (e x = y) ↔ (x = e.symm y) := by
      constructor
      · rintro rfl; simp
      · rintro rfl; simp
    have h2 := hF x (e.symm y)
    rw [Equiv.apply_symm_apply] at h2
    simp only [Equiv.symm_apply_apply, h2]
    by_cases hxy : x = e.symm y
    · simp [hxy]
    · simp [hxy, h1]
  unfold IsEL
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, fun x => ?_⟩
    · funext p
      obtain ⟨x, i⟩ := p
      rw [← hrow x i, ← hS x i]
      exact congrFun h1 (e x, i)
    · have := h2 (e x)
      simpa using this
  · rintro ⟨h1, h2⟩
    refine ⟨?_, fun y => ?_⟩
    · funext p
      obtain ⟨y, i⟩ := p
      obtain ⟨x, rfl⟩ := e.surjective y
      rw [hrow x i, hS x i]
      exact congrFun h1 (x, i)
    · have := h2 (e.symm y)
      simpa using this

include hF hS hsp in
theorem isSmallSolution_equiv_iff (φ : G₁.Ω 1 × Fin N → ℂ) (α : G₁.Ω 1 → ℂ) :
    IsSmallSolution G₂ a ν c₀ D₂ (fun p => φ (e.symm p.1, p.2)) (fun y => α (e.symm y)) ↔
      IsSmallSolution G₁ a ν c₀ D₁ φ α := by
  unfold IsSmallSolution
  rw [isEL_equiv_iff e hF hS]
  refine and_congr_right fun _ => ⟨fun h x => ?_, fun h y => ?_⟩
  · have h1 := h (e x)
    simp only [Equiv.symm_apply_apply] at h1
    rw [hsp x] at h1
    exact h1
  · obtain ⟨x, rfl⟩ := e.surjective y
    have h1 := h x
    simp only [Equiv.symm_apply_apply]
    rw [hsp x]
    exact h1

/-- The pullback of a pair `(φ, α)` on `G₁` to `G₂` along `e`. -/
def solMap (e : G₁.Ω 1 ≃ G₂.Ω 1) (s : (G₁.Ω 1 × Fin N → ℂ) × (G₁.Ω 1 → ℂ)) :
    (G₂.Ω 1 × Fin N → ℂ) × (G₂.Ω 1 → ℂ) :=
  (fun p => s.1 (e.symm p.1, p.2), fun y => s.2 (e.symm y))

theorem solMap_injective (e : G₁.Ω 1 ≃ G₂.Ω 1) :
    Function.Injective (solMap (N := N) e) := by
  intro s s' h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  refine Prod.ext (funext fun p => ?_) (funext fun y => ?_)
  · obtain ⟨y, j⟩ := p
    have := congrFun h1 (e y, j)
    simpa [solMap] using this
  · have := congrFun h2 (e y)
    simpa [solMap] using this

theorem solMap_surjective (e : G₁.Ω 1 ≃ G₂.Ω 1) :
    Function.Surjective (solMap (N := N) e) := by
  intro s'
  refine ⟨(fun p => s'.1 (e p.1, p.2), fun y => s'.2 (e y)), ?_⟩
  refine Prod.ext (funext fun p => ?_) (funext fun y => ?_) <;> simp [solMap]

include hF hS hsp in
/-- **Transport of the background along an equivalence of the regions.** -/
theorem bgFieldC_equiv (x : G₁.Ω 1) (i : Fin N) :
    bgFieldC G₂ a ν c₀ D₂ (e x, i) = bgFieldC G₁ a ν c₀ D₁ (x, i) := by
  classical
  have hiff : ∀ s, IsSmallSolution G₂ a ν c₀ D₂ (solMap e s).1 (solMap e s).2 ↔
      IsSmallSolution G₁ a ν c₀ D₁ s.1 s.2 := fun s =>
    isSmallSolution_equiv_iff e hF hS hsp s.1 s.2
  by_cases H : ∃! s : (G₁.Ω 1 × Fin N → ℂ) × (G₁.Ω 1 → ℂ), IsSmallSolution G₁ a ν c₀ D₁ s.1 s.2
  · obtain ⟨s, hs, hu⟩ := H
    have hs2 : IsSmallSolution G₂ a ν c₀ D₂ (solMap e s).1 (solMap e s).2 := (hiff s).2 hs
    have H' : ∃! s' : (G₂.Ω 1 × Fin N → ℂ) × (G₂.Ω 1 → ℂ),
        IsSmallSolution G₂ a ν c₀ D₂ s'.1 s'.2 := by
      refine ⟨solMap e s, hs2, fun s' hs' => ?_⟩
      obtain ⟨t, rfl⟩ := solMap_surjective e s'
      rw [hu t ((hiff t).1 hs')]
    have e1 := bgFieldC_eq (G := G₁) (a := a) (ν := ν) (c₀ := c₀) (D := D₁) (φ := s.1) (α := s.2)
      hs (fun φ' α' h => by
        have := hu (φ', α') h
        exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩)
    have e2 := bgFieldC_eq (G := G₂) (a := a) (ν := ν) (c₀ := c₀) (D := D₂)
      (φ := (solMap e s).1) (α := (solMap e s).2) hs2 (fun φ' α' h => by
        have := H'.unique (y₁ := (φ', α')) (y₂ := solMap e s) h hs2
        exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩)
    rw [e1.1, e2.1]
    simp [solMap]
  · have H' : ¬ ∃! s' : (G₂.Ω 1 × Fin N → ℂ) × (G₂.Ω 1 → ℂ),
        IsSmallSolution G₂ a ν c₀ D₂ s'.1 s'.2 := by
      rintro ⟨s', hs', hu'⟩
      obtain ⟨s, rfl⟩ := solMap_surjective e s'
      refine H ⟨s, (hiff s).1 hs', fun t ht => ?_⟩
      exact solMap_injective e (hu' (solMap e t) ((hiff t).2 ht))
    unfold bgFieldC
    simp [H, H']

end Equiv

end Balaban.Background
