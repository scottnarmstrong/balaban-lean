/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Background.Def5
public import Balaban.Background.BgFieldTwoTorusEquiv

/-!
# The background field of corresponding localized generating sets

`GSIso a ν G G' σ R`: a site map `σ` carries `Ω₁(G)` bijectively onto `Ω₁(G')`, preserves the
spacing and the entries of the Dirichlet operator at `α = 0`, and the sources of data that agree
under `σ` on the read region `R` agree.  Then the Euler-Lagrange systems are isomorphic, and
`bgFieldC`, `bgMultC` correspond at corresponding sites (`bgFieldC_of_gsIso`), by the landed
`bgPairC_equiv` of `BgFieldTwoTorusEquiv`.

This is the exact locality of the background field of a localized generating set: when the
localized sets of two tori are carried onto each other by the box map (the sites of `Ω₁`, the
collar and the data agree), no estimate is needed.
-/

@[expose] public section

namespace Balaban.Background

open Balaban.Multiscale Matrix Finset

variable {d L N₀ N₀' k N : ℕ} [NeZero N₀] [NeZero N₀'] [NeZero L] {ϱ ϱ' : ℝ}
variable {G : GeneratingSet d L N₀ k ϱ} {G' : GeneratingSet d L N₀' k ϱ'}
variable {a : ℕ → ℝ} {ν : ℝ}
variable {D : BgData G N} {D' : BgData G' N}

/-- **A site map identifying the localized data of two generating sets** (the localized set of a
polymer and of its image under a box map).  `σ` carries `Ω₁(G)` bijectively onto `Ω₁(G')`, preserves
the spacing and the entries of the Dirichlet operator at `α = 0`, and the source of data that agree
under `σ` on the read region `R` agree.  `GSIso` is the geometric input of the two-torus statements
for localized generating sets; it is satisfied by the localized sets of corresponding polymers. -/
structure GSIso (a : ℕ → ℝ) (ν : ℝ) (G : GeneratingSet d L N₀ k ϱ) (G' : GeneratingSet d L N₀' k ϱ')
    (σ : Torus d (N₀ * L ^ k) → Torus d (N₀' * L ^ k)) (R : Set (Torus d (N₀ * L ^ k))) :
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
theorem bgFieldC_of_gsIso {σ : Torus d (N₀ * L ^ k) → Torus d (N₀' * L ^ k)}
    {R : Set (Torus d (N₀ * L ^ k))} (h : GSIso a ν G G' σ R)
    (hD : ∀ z ∈ R, D.Ψ z = D'.Ψ (σ z) ∧ D.h z = D'.h (σ z)) (c₀ : ℝ) :
    (∀ (x : G.Ω 1) (hx : σ x ∈ G'.Ω 1) (i : Fin N),
      bgFieldC G' a ν c₀ D' (⟨σ x, hx⟩, i) = bgFieldC G a ν c₀ D (x, i)) ∧
    (∀ (x : G.Ω 1) (hx : σ x ∈ G'.Ω 1),
      bgMultC G' a ν c₀ D' ⟨σ x, hx⟩ = bgMultC G a ν c₀ D x) := by
  have hF : ∀ x y : G.Ω 1, fullMatrix G' a ν (h.equiv x : Torus d (N₀' * L ^ k)) (h.equiv y) =
      fullMatrix G a ν (x : Torus d (N₀ * L ^ k)) y := by
    intro x y
    have := h.op x y (h.mapsTo x x.2) (h.mapsTo y y.2)
    rw [dirichletOperator_apply, dirichletOperator_apply] at this
    simp only [Pi.zero_apply, ite_self, add_zero] at this
    exact_mod_cast this
  have hT := bgPairC_equiv (D₁ := D) (D₂ := D') (c₀ := c₀) h.equiv hF
    (fun x i => h.source N D D' hD x _ i) (fun x => h.spacing x x.2)
  exact ⟨fun x hx i => hT.1 x i, fun x hx => hT.2 x⟩

end Balaban.Background
