/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Background.Def5

/-!
# The background field under an isomorphism of the Euler-Lagrange systems

Let `G`, `G'` be generating sets and `e : Ω₁(G) ≃ Ω₁(G')` a bijection of the unit-sphere sites that
carries the spacing, the entries of the Dirichlet operator at `α = 0` and the source.  Then the
Euler-Lagrange system of `(G, D)` is the transport of that of `(G', D')`, the small solutions
correspond, and the background field and multiplier `bgFieldC`, `bgMultC` correspond:

* `isSmallSolution_transport`: `(φ, α)` is a small solution on `G` iff its transport is one on `G'`;
* `bgFieldC_transport`, `bgMultC_transport`: the values correspond.

This is the exact locality of the background field of a localized generating set: when the
localized sets of two tori are carried onto each other by the box map (the sites of `Ω₁`, the
neighbouring collar and the data agree), no estimate is needed.
-/

@[expose] public section

namespace Balaban.Background

open Balaban.Multiscale Matrix Finset

variable {d L N₀ N₀' k k' N : ℕ} [NeZero N₀] [NeZero N₀'] [NeZero L] {ϱ ϱ' : ℝ}
variable {G : GeneratingSet d L N₀ k ϱ} {G' : GeneratingSet d L N₀' k' ϱ'}

/-- The transport of a field on `Ω₁(G)` to `Ω₁(G')`. -/
def transFld (e : G.Ω 1 ≃ G'.Ω 1) (φ : G.Ω 1 × Fin N → ℂ) : G'.Ω 1 × Fin N → ℂ :=
  fun p => φ (e.symm p.1, p.2)

/-- The transport of a multiplier on `Ω₁(G)` to `Ω₁(G')`. -/
def transMult (e : G.Ω 1 ≃ G'.Ω 1) (α : G.Ω 1 → ℂ) : G'.Ω 1 → ℂ :=
  fun x => α (e.symm x)

theorem liftOp_mulVec_apply {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) (φ : ι × Fin N → ℂ)
    (x : ι) (i : Fin N) :
    (liftOp N A *ᵥ φ) (x, i) = ∑ y, A x y * φ (y, i) := by
  simp only [Matrix.mulVec, dotProduct, liftOp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj; simp [Ne.symm hj]
  · simp

variable (a : ℕ → ℝ) (ν : ℝ)

theorem dirichletOperator_apply_zero_add (α : G.Ω 1 → ℂ) (x y : G.Ω 1) :
    dirichletOperator G a ν α x y = dirichletOperator G a ν 0 x y + if x = y then α x else 0 := by
  simp [dirichletOperator, Matrix.diagonal_apply]

variable {a ν}

/-- The transported Dirichlet operator acts as the transport of the original on a field. -/
theorem dirichletOp_mulVec_transport (e : G.Ω 1 ≃ G'.Ω 1)
    (hop : ∀ x y, dirichletOperator G' a ν 0 (e x) (e y) = dirichletOperator G a ν 0 x y)
    (α : G.Ω 1 → ℂ) (φ : G.Ω 1 × Fin N → ℂ) (x : G.Ω 1) (i : Fin N) :
    (liftOp N (dirichletOperator G' a ν (transMult e α)) *ᵥ transFld e φ) (e x, i) =
      (liftOp N (dirichletOperator G a ν α) *ᵥ φ) (x, i) := by
  rw [liftOp_mulVec_apply, liftOp_mulVec_apply]
  rw [← e.sum_comp]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [dirichletOperator_apply_zero_add (G := G') a ν (transMult e α) (e x) (e y),
    dirichletOperator_apply_zero_add (G := G) a ν α x y, hop]
  simp [transFld, transMult, e.injective.eq_iff]

variable {D : BgData G N} {D' : BgData G' N}

/-- **The Euler-Lagrange system under the isomorphism.** -/
theorem isEL_transport_iff (e : G.Ω 1 ≃ G'.Ω 1)
    (hop : ∀ x y, dirichletOperator G' a ν 0 (e x) (e y) = dirichletOperator G a ν 0 x y)
    (hsrc : ∀ (x : G.Ω 1) (i : Fin N), source G' a ν D' (e x, i) = source G a ν D (x, i))
    (φ : G.Ω 1 × Fin N → ℂ) (α : G.Ω 1 → ℂ) :
    IsEL G a ν D φ α ↔ IsEL G' a ν D' (transFld e φ) (transMult e α) := by
  unfold IsEL
  refine and_congr ?_ ?_
  · constructor
    · intro h
      funext ⟨x', i⟩
      obtain ⟨x, rfl⟩ := e.surjective x'
      rw [dirichletOp_mulVec_transport e hop, h, hsrc]
    · intro h
      funext ⟨x, i⟩
      have := congrFun h (e x, i)
      rw [dirichletOp_mulVec_transport e hop, hsrc] at this
      exact this
  · constructor
    · intro h x'
      obtain ⟨x, rfl⟩ := e.surjective x'
      simpa [transFld] using h x
    · intro h x
      simpa [transFld] using h (e x)

/-- **Small solutions under the isomorphism.** -/
theorem isSmallSolution_transport_iff (e : G.Ω 1 ≃ G'.Ω 1)
    (hop : ∀ x y, dirichletOperator G' a ν 0 (e x) (e y) = dirichletOperator G a ν 0 x y)
    (hsrc : ∀ (x : G.Ω 1) (i : Fin N), source G' a ν D' (e x, i) = source G a ν D (x, i))
    (hsp : ∀ x : G.Ω 1, G'.spacing (e x : Torus d (N₀' * L ^ k')) =
      G.spacing (x : Torus d (N₀ * L ^ k)))
    (c₀ : ℝ) (φ : G.Ω 1 × Fin N → ℂ) (α : G.Ω 1 → ℂ) :
    IsSmallSolution G a ν c₀ D φ α ↔
      IsSmallSolution G' a ν c₀ D' (transFld e φ) (transMult e α) := by
  unfold IsSmallSolution
  refine and_congr (isEL_transport_iff e hop hsrc φ α) ?_
  constructor
  · intro h x'
    obtain ⟨x, rfl⟩ := e.surjective x'
    simpa [transMult, hsp x] using h x
  · intro h x
    simpa [transMult, hsp x] using h (e x)

/-- The pair of a field and a multiplier, transported. -/
def transPair (e : G.Ω 1 ≃ G'.Ω 1) :
    ((G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ)) ≃ ((G'.Ω 1 × Fin N → ℂ) × (G'.Ω 1 → ℂ)) :=
  Equiv.prodCongr (Equiv.arrowCongr (e.prodCongr (Equiv.refl (Fin N))) (Equiv.refl ℂ))
    (Equiv.arrowCongr e (Equiv.refl ℂ))

theorem transPair_fst (e : G.Ω 1 ≃ G'.Ω 1) (s : (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ)) :
    (transPair e s).1 = transFld e s.1 := rfl

theorem transPair_snd (e : G.Ω 1 ≃ G'.Ω 1) (s : (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ)) :
    (transPair e s).2 = transMult e s.2 := rfl

/-- **The background field under the isomorphism**: `bgFieldC` and `bgMultC` of `(G', D')` are the
transports of those of `(G, D)`. -/
theorem bgFieldC_transport (e : G.Ω 1 ≃ G'.Ω 1)
    (hop : ∀ x y, dirichletOperator G' a ν 0 (e x) (e y) = dirichletOperator G a ν 0 x y)
    (hsrc : ∀ (x : G.Ω 1) (i : Fin N), source G' a ν D' (e x, i) = source G a ν D (x, i))
    (hsp : ∀ x : G.Ω 1, G'.spacing (e x : Torus d (N₀' * L ^ k')) =
      G.spacing (x : Torus d (N₀ * L ^ k)))
    (c₀ : ℝ) :
    bgFieldC G' a ν c₀ D' = transFld e (bgFieldC G a ν c₀ D) ∧
      bgMultC G' a ν c₀ D' = transMult e (bgMultC G a ν c₀ D) := by
  classical
  have hP : ∀ s : (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ),
      IsSmallSolution G a ν c₀ D s.1 s.2 ↔
        IsSmallSolution G' a ν c₀ D' (transPair e s).1 (transPair e s).2 := fun s =>
    isSmallSolution_transport_iff e hop hsrc hsp c₀ s.1 s.2
  unfold bgFieldC bgMultC
  by_cases H : ∃! s : (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ), IsSmallSolution G a ν c₀ D s.1 s.2
  · have H' : ∃! s : (G'.Ω 1 × Fin N → ℂ) × (G'.Ω 1 → ℂ),
        IsSmallSolution G' a ν c₀ D' s.1 s.2 := by
      obtain ⟨s0, h0, hu⟩ := H
      refine ⟨transPair e s0, (hP s0).1 h0, fun s' hs' => ?_⟩
      have := hu ((transPair e).symm s') ((hP _).2 (by simpa using hs'))
      rw [← this]; simp
    have hs0 := H.exists.choose_spec
    have hs0' : H'.exists.choose = transPair e H.exists.choose :=
      H'.unique H'.exists.choose_spec ((hP _).1 hs0)
    refine ⟨?_, ?_⟩
    · rw [dite_eq_left_of_eq_true (eq_true H), dite_eq_left_of_eq_true (eq_true H'), hs0']; rfl
    · rw [dite_eq_left_of_eq_true (eq_true H), dite_eq_left_of_eq_true (eq_true H'), hs0']; rfl
  · have H' : ¬ ∃! s : (G'.Ω 1 × Fin N → ℂ) × (G'.Ω 1 → ℂ),
        IsSmallSolution G' a ν c₀ D' s.1 s.2 := by
      intro h
      apply H
      obtain ⟨s0', h0, hu⟩ := h
      refine ⟨(transPair e).symm s0', (hP _).2 (by simpa using h0), fun s hs => ?_⟩
      have := hu (transPair e s) ((hP s).1 hs)
      rw [← this]; simp
    refine ⟨?_, ?_⟩
    · rw [dite_eq_right_of_eq_false (eq_false H), dite_eq_right_of_eq_false (eq_false H')]; rfl
    · rw [dite_eq_right_of_eq_false (eq_false H), dite_eq_right_of_eq_false (eq_false H')]; rfl

/-- **A site map identifying the localized data of two generating sets** (the localized set of a
polymer and of its image under a box map).  `σ` carries `Ω₁(G)` bijectively onto `Ω₁(G')`, preserves
the spacing and the entries of the Dirichlet operator at `α = 0`, and the source of data that agree
under `σ` on the read region `R` agree.  `GSIso` is the geometric input of the two-torus statements
for localized generating sets; it is satisfied by the localized sets of corresponding polymers. -/
structure GSIso (a : ℕ → ℝ) (ν : ℝ) (G : GeneratingSet d L N₀ k ϱ) (G' : GeneratingSet d L N₀' k' ϱ')
    (σ : Torus d (N₀ * L ^ k) → Torus d (N₀' * L ^ k')) (R : Set (Torus d (N₀ * L ^ k))) :
    Prop where
  mapsTo : ∀ x ∈ G.Ω 1, σ x ∈ G'.Ω 1
  injOn : ∀ x ∈ G.Ω 1, ∀ y ∈ G.Ω 1, σ x = σ y → x = y
  surjOn : ∀ x' ∈ G'.Ω 1, ∃ x ∈ G.Ω 1, σ x = x'
  spacing : ∀ x ∈ G.Ω 1, G'.spacing (σ x) = G.spacing x
  op : ∀ (x y : G.Ω 1) (hx : σ x ∈ G'.Ω 1) (hy : σ y ∈ G'.Ω 1),
    dirichletOperator G' a ν 0 ⟨σ x, hx⟩ ⟨σ y, hy⟩ = dirichletOperator G a ν 0 x y
  source : ∀ (N : ℕ) (D : BgData G N) (D' : BgData G' N),
    (∀ z ∈ R, D.Ψ z = D'.Ψ (σ z) ∧ D.h z = D'.h (σ z)) →
    ∀ (x : G.Ω 1) (hx : σ x ∈ G'.Ω 1) (i : Fin N),
      source G' a ν D' (⟨σ x, hx⟩, i) = source G a ν D (x, i)

/-- The bijection of the sites of `Ω₁` induced by a `GSIso`. -/
noncomputable def GSIso.equiv {a ν} {σ} {R} (h : GSIso a ν G G' σ R) : G.Ω 1 ≃ G'.Ω 1 :=
  Equiv.ofBijective (fun x => ⟨σ x, h.mapsTo x x.2⟩)
    ⟨fun x y hxy => Subtype.ext (h.injOn x x.2 y y.2 (congrArg Subtype.val hxy)),
      fun x' => by
        obtain ⟨x, hx, hxx⟩ := h.surjOn x' x'.2
        exact ⟨⟨x, hx⟩, Subtype.ext hxx⟩⟩

/-- **The background field of corresponding localized sets.**  For data that agree under `σ` on the
read region, `bgFieldC` and `bgMultC` of the two sets correspond at corresponding sites. -/
theorem bgFieldC_of_gsIso {σ : Torus d (N₀ * L ^ k) → Torus d (N₀' * L ^ k')}
    {R : Set (Torus d (N₀ * L ^ k))} (h : GSIso a ν G G' σ R)
    (hD : ∀ z ∈ R, D.Ψ z = D'.Ψ (σ z) ∧ D.h z = D'.h (σ z)) (c₀ : ℝ) :
    (∀ (x : G.Ω 1) (hx : σ x ∈ G'.Ω 1) (i : Fin N),
      bgFieldC G' a ν c₀ D' (⟨σ x, hx⟩, i) = bgFieldC G a ν c₀ D (x, i)) ∧
    (∀ (x : G.Ω 1) (hx : σ x ∈ G'.Ω 1),
      bgMultC G' a ν c₀ D' ⟨σ x, hx⟩ = bgMultC G a ν c₀ D x) := by
  have hT := bgFieldC_transport (D := D) (D' := D') h.equiv
    (fun x y => h.op x y _ _) (fun x i => h.source N D D' hD x _ i)
    (fun x => h.spacing x x.2) c₀
  refine ⟨fun x hx i => ?_, fun x hx => ?_⟩
  · have := congrFun hT.1 (h.equiv x, i)
    rw [show (⟨σ x, hx⟩ : G'.Ω 1) = h.equiv x from rfl]
    simpa [transFld] using this
  · have := congrFun hT.2 (h.equiv x)
    rw [show (⟨σ x, hx⟩ : G'.Ω 1) = h.equiv x from rfl]
    simpa [transMult] using this

end Balaban.Background
