/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Background.Composition

/-!
# The composed field at corresponding sites of two tori

For generating sets `G ≺ G'` of one torus and `H ≺ H'` of another, a site map `σ`, and a site `x`
of `Ω₁(G)` at which the layers and blocks of `G`, `G'` correspond to those of `H`, `H'`
(`SiteCorr`), the composed field `composeField` at `σ x` equals that at `x`, when the fields
`φ'`, `φ''` correspond on the block of `x` and the data agree at `x`:

* `blockMean_corr`: the block average at corresponding sites;
* `composeField_corr_mem`: the composed field at a site of `Ω₁`;
* `composeField_corr_collar`, `composeField_corr_out`: at a collar site and off the collar.
-/

@[expose] public section

namespace Balaban.Background

open Balaban.Multiscale Matrix Finset

variable {d L N₀ N₀' k : ℕ} [NeZero N₀] [NeZero N₀'] [NeZero L] {ϱ ϱ' ϱ₂ ϱ₃ : ℝ}

/-- **The layer and block of a generating set at a site correspond to those of another under a
site map `σ`.** -/
structure SiteCorr (G : GeneratingSet d L N₀ k ϱ) (H : GeneratingSet d L N₀' k ϱ₂)
    (σ : Torus d (N₀ * L ^ k) → Torus d (N₀' * L ^ k)) (x : Torus d (N₀ * L ^ k)) : Prop where
  mem : x ∈ G.Ω 1 → σ x ∈ H.Ω 1
  layer : x ∈ G.Ω 1 → H.layerIndex (σ x) = G.layerIndex x
  blk : x ∈ G.Ω 1 → (G.blk (G.layerIndex x) x).image σ = H.blk (G.layerIndex x) (σ x)
  inj : x ∈ G.Ω 1 → Set.InjOn σ ↑(G.blk (G.layerIndex x) x)

theorem blockMean_corr {G : GeneratingSet d L N₀ k ϱ} {H : GeneratingSet d L N₀' k ϱ₂}
    {σ : Torus d (N₀ * L ^ k) → Torus d (N₀' * L ^ k)} {x : Torus d (N₀ * L ^ k)}
    (hx : x ∈ G.Ω 1) (h : SiteCorr G H σ x) {w : Torus d (N₀ * L ^ k) → ℂ}
    {w' : Torus d (N₀' * L ^ k) → ℂ} (hw : ∀ y ∈ G.blk (G.layerIndex x) x, w' (σ y) = w y) :
    blockMean H (G.layerIndex x) w' (σ x) = blockMean G (G.layerIndex x) w x := by
  unfold blockMean
  congr 1
  rw [← h.blk hx, Finset.sum_image (fun a ha b hb hab => h.inj hx ha hb hab)]
  exact Finset.sum_congr rfl hw

variable {G : GeneratingSet d L N₀ k ϱ} {G' : GeneratingSet d L N₀ k ϱ'}
  {H : GeneratingSet d L N₀' k ϱ₂} {H' : GeneratingSet d L N₀' k ϱ₃}
  {σ : Torus d (N₀ * L ^ k) → Torus d (N₀' * L ^ k)} {N : ℕ}

/-- **The composed field at a site of `Ω₁(G)`.** -/
theorem composeField_corr_mem (a : ℕ → ℝ) {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.Ω 1)
    (hG : SiteCorr G H σ x) (hG' : SiteCorr G' H' σ x) (hx' : x ∈ G'.Ω 1)
    {φ' : G'.Ω 1 × Fin N → ℂ} {φ'' : H'.Ω 1 × Fin N → ℂ}
    (hφ : ∀ y ∈ G'.blk (G'.layerIndex x) x, ∀ i, svec H' φ'' (σ y) i = svec G' φ' y i)
    (hφG : ∀ y ∈ G.blk (G.layerIndex x) x, ∀ i, svec H' φ'' (σ y) i = svec G' φ' y i)
    {Ψ' : Torus d (N₀ * L ^ k) → Fin N → ℂ} {Ψ'' : Torus d (N₀' * L ^ k) → Fin N → ℂ}
    (hΨ : Ψ'' (σ x) = Ψ' x) (i : Fin N) :
    composeField H H' a φ'' Ψ'' (σ x) i = composeField G G' a φ' Ψ' x i := by
  classical
  unfold composeField
  have hl : H.layerIndex (σ x) = G.layerIndex x := hG.layer hx
  have hl' : H'.layerIndex (σ x) = G'.layerIndex x := hG'.layer hx'
  simp only [hx, hG.mem hx, ite_true, hl, hl']
  rw [blockMean_corr hx hG (w := fun y => svec G' φ' y i) (w' := fun y => svec H' φ'' y i)
      (fun y hy => hφG y hy i),
    blockMean_corr hx' hG' (w := fun y => svec G' φ' y i) (w' := fun y => svec H' φ'' y i)
      (fun y hy => hφ y hy i), hΨ]

/-- **The extension of a field by the data at corresponding sites.** -/
theorem barField_corr {x : Torus d (N₀ * L ^ k)} (h1 : σ x ∈ H'.Ω 1 ↔ x ∈ G'.Ω 1)
    {φ' : G'.Ω 1 × Fin N → ℂ} {φ'' : H'.Ω 1 × Fin N → ℂ}
    {Ψ' : Torus d (N₀ * L ^ k) → Fin N → ℂ} {Ψ'' : Torus d (N₀' * L ^ k) → Fin N → ℂ}
    (i : Fin N)
    (hφ : ∀ (hx : x ∈ G'.Ω 1) (hy : σ x ∈ H'.Ω 1), φ'' (⟨σ x, hy⟩, i) = φ' (⟨x, hx⟩, i))
    (hΨ : x ∉ G'.Ω 1 → Ψ'' (σ x) i = Ψ' x i) :
    barField H' Ψ'' φ'' (σ x) i = barField G' Ψ' φ' x i := by
  classical
  unfold barField
  by_cases hx : x ∈ G'.Ω 1
  · simp only [hx, h1.2 hx, dite_true]
    exact hφ hx _
  · have hy : σ x ∉ H'.Ω 1 := fun h => hx (h1.1 h)
    simp only [hx, hy, dite_false]
    exact hΨ hx

/-- **The composed field at a collar site.** -/
theorem composeField_corr_collar (a : ℕ → ℝ) {x : Torus d (N₀ * L ^ k)} (hx : x ∉ G.Ω 1)
    (hxc : x ∈ collar G) (hσ : σ x ∉ H.Ω 1) (hσc : σ x ∈ collar H)
    {φ' : G'.Ω 1 × Fin N → ℂ} {φ'' : H'.Ω 1 × Fin N → ℂ}
    {Ψ' : Torus d (N₀ * L ^ k) → Fin N → ℂ} {Ψ'' : Torus d (N₀' * L ^ k) → Fin N → ℂ}
    (i : Fin N) (hbar : barField H' Ψ'' φ'' (σ x) i = barField G' Ψ' φ' x i) :
    composeField H H' a φ'' Ψ'' (σ x) i = composeField G G' a φ' Ψ' x i := by
  classical
  unfold composeField
  simp only [hx, hσ, hxc, hσc, ite_true, ite_false]
  exact hbar

/-- **The composed field off `Ω₁ ∪` collar.** -/
theorem composeField_corr_out (a : ℕ → ℝ) {x : Torus d (N₀ * L ^ k)} (hx : x ∉ G.Ω 1)
    (hxc : x ∉ collar G) (hσ : σ x ∉ H.Ω 1) (hσc : σ x ∉ collar H)
    {φ' : G'.Ω 1 × Fin N → ℂ} {φ'' : H'.Ω 1 × Fin N → ℂ}
    {Ψ' : Torus d (N₀ * L ^ k) → Fin N → ℂ} {Ψ'' : Torus d (N₀' * L ^ k) → Fin N → ℂ}
    (i : Fin N) :
    composeField H H' a φ'' Ψ'' (σ x) i = composeField G G' a φ' Ψ' x i := by
  classical
  unfold composeField
  simp only [hx, hσ, hxc, hσc, ite_false]

/-- **A generating set corresponds to another on a set `R` of sites** under the site map `σ`:
the membership in `Ω₁` and in the collar, and the layer and block at the sites of `Ω₁`. -/
structure GSCorr (G : GeneratingSet d L N₀ k ϱ) (H : GeneratingSet d L N₀' k ϱ₂)
    (σ : Torus d (N₀ * L ^ k) → Torus d (N₀' * L ^ k)) (R : Set (Torus d (N₀ * L ^ k))) :
    Prop where
  mem_iff : ∀ z ∈ R, σ z ∈ H.Ω 1 ↔ z ∈ G.Ω 1
  collar_iff : ∀ z ∈ R, σ z ∈ collar H ↔ z ∈ collar G
  site : ∀ z ∈ R, SiteCorr G H σ z

theorem GSCorr.mono {G : GeneratingSet d L N₀ k ϱ} {H : GeneratingSet d L N₀' k ϱ₂}
    {σ : Torus d (N₀ * L ^ k) → Torus d (N₀' * L ^ k)} {R R' : Set (Torus d (N₀ * L ^ k))}
    (h : GSCorr G H σ R) (hR : R' ⊆ R) : GSCorr G H σ R' :=
  ⟨fun z hz => h.mem_iff z (hR hz), fun z hz => h.collar_iff z (hR hz),
    fun z hz => h.site z (hR hz)⟩

/-- **The composed field at every site of a set of correspondence.** -/
theorem composeField_corr (a : ℕ → ℝ) {R : Set (Torus d (N₀ * L ^ k))}
    (hG : GSCorr G H σ R) (hG' : GSCorr G' H' σ R) {z : Torus d (N₀ * L ^ k)} (hz : z ∈ R)
    (hprec : z ∈ G.Ω 1 → z ∈ G'.Ω 1)
    {φ' : G'.Ω 1 × Fin N → ℂ} {φ'' : H'.Ω 1 × Fin N → ℂ}
    (hφ : z ∈ G.Ω 1 → ∀ y ∈ G'.blk (G'.layerIndex z) z, ∀ i,
      svec H' φ'' (σ y) i = svec G' φ' y i)
    (hφG : z ∈ G.Ω 1 → ∀ y ∈ G.blk (G.layerIndex z) z, ∀ i,
      svec H' φ'' (σ y) i = svec G' φ' y i)
    {Ψ' : Torus d (N₀ * L ^ k) → Fin N → ℂ} {Ψ'' : Torus d (N₀' * L ^ k) → Fin N → ℂ}
    (hΨ : Ψ'' (σ z) = Ψ' z)
    (hbar : z ∈ collar G → ∀ i, barField H' Ψ'' φ'' (σ z) i = barField G' Ψ' φ' z i) (i : Fin N) :
    composeField H H' a φ'' Ψ'' (σ z) i = composeField G G' a φ' Ψ' z i := by
  by_cases h1 : z ∈ G.Ω 1
  · exact composeField_corr_mem a h1 (hG.site z hz) (hG'.site z hz) (hprec h1) (hφ h1) (hφG h1) hΨ i
  · by_cases h2 : z ∈ collar G
    · exact composeField_corr_collar a h1 h2 (fun h => h1 ((hG.mem_iff z hz).1 h))
        ((hG.collar_iff z hz).2 h2) i (hbar h2 i)
    · exact composeField_corr_out a h1 h2 (fun h => h1 ((hG.mem_iff z hz).1 h))
        (fun h => h2 ((hG.collar_iff z hz).1 h)) i

/-- The zero extensions of corresponding fields at corresponding sites. -/
theorem svec_corr {y : Torus d (N₀ * L ^ k)} (h1 : σ y ∈ H'.Ω 1 ↔ y ∈ G'.Ω 1)
    {φ' : G'.Ω 1 × Fin N → ℂ} {φ'' : H'.Ω 1 × Fin N → ℂ}
    (hφ : ∀ (hy : y ∈ G'.Ω 1) (hy' : σ y ∈ H'.Ω 1) (i : Fin N),
      φ'' (⟨σ y, hy'⟩, i) = φ' (⟨y, hy⟩, i)) (i : Fin N) :
    svec H' φ'' (σ y) i = svec G' φ' y i := by
  classical
  unfold svec zeroExt
  by_cases hy : y ∈ G'.Ω 1
  · simp only [hy, h1.2 hy, dite_true]
    exact hφ hy _ i
  · have hy' : σ y ∉ H'.Ω 1 := fun h => hy (h1.1 h)
    simp only [hy, hy', dite_false]

end Balaban.Background
