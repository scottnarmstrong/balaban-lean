/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Multiscale.CutCoercivity
public import Balaban.Multiscale.PointwisePotential
import Mathlib.Tactic.Linarith

/-!
# The cube cut decouples `Ω₁` into the cube and its complement (LOCALIZATION.md §1.3)

For a set `Λ ⊆ Ω₁` that is a union of blocks of every layer (`BlockAligned`) and
`cut = cubeCut G Λ`, the matrix `-Δ_cut + ν + Q* a Q` has no matrix element between a point of `Λ`
and a point of `Ω₁ \ Λ`: the removed bonds are exactly the bonds joining the two sets and the
blocks do not straddle them.  Consequently:

* `cutOperator_mulVec_apply_of_not_mem`, `cutOperator_mulVec_apply_of_mem`: the operator
  `cutOperator G a ν (cubeCut G Λ) α` is block diagonal for `Ω₁ = Λ ⊔ (Ω₁ \ Λ)`;
* `cutOperator_inv_supported`: for `f` supported in `Λ`, `u = H_cut(α)⁻¹ f` is supported in `Λ`;
  it is the Green's function `G^{(z)}(A) c_z f` of the Neumann cube operator `H_z(A)` (the
  restriction of `H_cut` to `Λ`) extended by zero, and it depends on `α` only through `α|_Λ`.
-/

@[expose] public section

namespace Balaban.Multiscale

open Finset Matrix Balaban

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

variable (G : GeneratingSet d L N₀ k ϱ)

/-- The bilinear form of the cut Laplacian between fields supported on the two sides of the cube
cut vanishes. -/
theorem cutLaplacian_bilinear_decouple {Λ : Finset (Torus d (N₀ * L ^ k))} (s : Prop)
    (ν : ℝ) {g φ : Torus d (N₀ * L ^ k) → ℝ}
    (hg : ∀ z, g z ≠ 0 → z ∈ G.Ω 1 ∧ (z ∈ Λ ↔ s))
    (hφ : ∀ z, φ z ≠ 0 → z ∈ G.Ω 1 ∧ (z ∈ Λ ↔ ¬ s)) :
    g ⬝ᵥ cutLaplacian ν (cubeCut G Λ) *ᵥ φ = 0 := by
  have hgφ : ∀ z, g z * φ z = 0 := by
    intro z
    by_contra h
    have h1 := (hg z (left_ne_zero_of_mul h)).2
    have h2 := (hφ z (right_ne_zero_of_mul h)).2
    tauto
  rw [cutLaplacian_bilinear]
  have h0 : ∑ x, g x * φ x = 0 := Finset.sum_eq_zero fun z _ => hgφ z
  rw [h0, mul_zero, add_zero]
  refine Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun μ _ => ?_
  split_ifs with hc
  · rfl
  · by_contra hne
    have hne1 := left_ne_zero_of_mul hne
    have hne2 := right_ne_zero_of_mul hne
    set y := x + Pi.single μ 1 with hy
    have hmem := (mem_cubeCut G (Λ := Λ) (x := x) (μ := μ)).not.1 hc
    rw [← hy] at hmem
    have hgx : g y ≠ 0 ∨ g x ≠ 0 := by
      by_contra h
      push Not at h
      exact hne1 (by rw [h.1, h.2, sub_self])
    have hφx : φ y ≠ 0 ∨ φ x ≠ 0 := by
      by_contra h
      push Not at h
      exact hne2 (by rw [h.1, h.2, sub_self])
    rcases hgx with hgy | hgx <;> rcases hφx with hφy | hφx
    · have := hgφ y; exact mul_ne_zero hgy hφy this
    · obtain ⟨a1, a2⟩ := hg y hgy
      obtain ⟨b1, b2⟩ := hφ x hφx
      exact hmem (Or.inr ⟨by tauto, b1, by tauto⟩)
    · obtain ⟨a1, a2⟩ := hg x hgx
      obtain ⟨b1, b2⟩ := hφ y hφy
      exact hmem (Or.inl ⟨by tauto, b1, by tauto⟩)
    · have := hgφ x; exact mul_ne_zero hgx hφx this

/-- The bilinear form of the block average term between fields supported on the two sides of a
block-aligned set vanishes. -/
theorem avgMatrix_bilinear_decouple {Λ : Finset (Torus d (N₀ * L ^ k))} (hΛ : BlockAligned G Λ)
    (s : Prop) (a : ℕ → ℝ) {g φ : Torus d (N₀ * L ^ k) → ℝ}
    (hg : ∀ z, g z ≠ 0 → z ∈ G.Ω 1 ∧ (z ∈ Λ ↔ s))
    (hφ : ∀ z, φ z ≠ 0 → z ∈ G.Ω 1 ∧ (z ∈ Λ ↔ ¬ s)) :
    g ⬝ᵥ avgMatrix G a *ᵥ φ = 0 := by
  simp only [dotProduct, Matrix.mulVec]
  refine Finset.sum_eq_zero fun x _ => ?_
  by_cases hgx : g x = 0
  · simp [hgx]
  obtain ⟨hxΩ, hxs⟩ := hg x hgx
  obtain ⟨hm1, hmk, hxl⟩ := G.layerIndex_spec hxΩ
  have : ∑ x', avgMatrix G a x x' * φ x' = 0 := by
    refine Finset.sum_eq_zero fun x' _ => ?_
    by_cases hφx : φ x' = 0
    · simp [hφx]
    obtain ⟨hx'Ω, hx's⟩ := hφ x' hφx
    rw [avgMatrix_apply_layer_block G a hm1 hmk hxl]
    by_cases hx'l : x' ∈ G.layer (G.layerIndex x)
    · by_cases hbm : jBlock d L N₀ k (G.layerIndex x) x' = jBlock d L N₀ k (G.layerIndex x) x
      · exfalso
        have := hΛ _ hm1 hmk x x' hxl hbm
        tauto
      · have : blockProjMatrix d (N₀ * L ^ k) (L ^ G.layerIndex x) (N₀ * L ^ (k - G.layerIndex x))
            x x' = 0 := by
          unfold blockProjMatrix
          have : blockMap (L ^ G.layerIndex x) (N₀ * L ^ (k - G.layerIndex x)) x ≠
              blockMap (L ^ G.layerIndex x) (N₀ * L ^ (k - G.layerIndex x)) x' :=
            fun h => hbm h.symm
          simp [this]
        simp [hx'l, this]
    · simp [hx'l]
  rw [this, mul_zero]

/-- **Decoupling of the form.** -/
theorem cutFullMatrix_bilinear_decouple {Λ : Finset (Torus d (N₀ * L ^ k))}
    (hΛ : BlockAligned G Λ) (s : Prop) (a : ℕ → ℝ) (ν : ℝ) {g φ : Torus d (N₀ * L ^ k) → ℝ}
    (hg : ∀ z, g z ≠ 0 → z ∈ G.Ω 1 ∧ (z ∈ Λ ↔ s))
    (hφ : ∀ z, φ z ≠ 0 → z ∈ G.Ω 1 ∧ (z ∈ Λ ↔ ¬ s)) :
    g ⬝ᵥ cutFullMatrix G a ν (cubeCut G Λ) *ᵥ φ = 0 := by
  unfold cutFullMatrix
  rw [Matrix.add_mulVec, dotProduct_add, cutLaplacian_bilinear_decouple G s ν hg hφ,
    avgMatrix_bilinear_decouple G hΛ s a hg hφ, add_zero]

/-- A row of the cut matrix at `x ∈ Ω₁` vanishes on a field supported on the other side. -/
theorem cutFullMatrix_row_decouple {Λ : Finset (Torus d (N₀ * L ^ k))} (hΛ : BlockAligned G Λ)
    (s : Prop) (a : ℕ → ℝ) (ν : ℝ) {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.Ω 1) (hxs : x ∈ Λ ↔ s)
    {ψ : Torus d (N₀ * L ^ k) → ℂ} (hψ : ∀ z, ψ z ≠ 0 → z ∈ G.Ω 1 ∧ (z ∈ Λ ↔ ¬ s)) :
    ((cutFullMatrix G a ν (cubeCut G Λ)).map (algebraMap ℝ ℂ) *ᵥ ψ) x = 0 := by
  have key : ∀ φ : Torus d (N₀ * L ^ k) → ℝ, (∀ z, φ z ≠ 0 → z ∈ G.Ω 1 ∧ (z ∈ Λ ↔ ¬ s)) →
      (cutFullMatrix G a ν (cubeCut G Λ) *ᵥ φ) x = 0 := by
    intro φ hφ
    have h := cutFullMatrix_bilinear_decouple G hΛ s a ν (g := Pi.single x 1) (φ := φ)
      (fun z hz => by
        have : z = x := by
          by_contra hne
          exact hz (by simp [hne])
        subst this
        exact ⟨hx, hxs⟩) hφ
    simpa [single_dotProduct] using h
  apply Complex.ext
  · rw [re_mulVec_map]
    exact (key _ fun z hz => hψ z fun h0 => hz (by simp [h0])).trans (by simp)
  · rw [im_mulVec_map]
    exact (key _ fun z hz => hψ z fun h0 => hz (by simp [h0])).trans (by simp)

/-- **Block diagonality (outside).** If `u` vanishes off `Λ`, `H_cut u` vanishes on `Ω₁ \ Λ`. -/
theorem cutOperator_mulVec_apply_of_not_mem {Λ : Finset (Torus d (N₀ * L ^ k))}
    (hΛ : BlockAligned G Λ) {a : ℕ → ℝ} {ν : ℝ} (α : G.Ω 1 → ℂ) {u : G.Ω 1 → ℂ}
    (hu : ∀ z : G.Ω 1, (z : Torus d (N₀ * L ^ k)) ∉ Λ → u z = 0) (x : G.Ω 1)
    (hx : (x : Torus d (N₀ * L ^ k)) ∉ Λ) :
    (cutOperator G a ν (cubeCut G Λ) α *ᵥ u) x = 0 := by
  have h := cutOperator_eq G (u := u) (f := cutOperator G a ν (cubeCut G Λ) α *ᵥ u) rfl x
  rw [hu x hx, mul_zero, add_zero] at h
  rw [← h]
  refine cutFullMatrix_row_decouple G hΛ False a ν x.2 (by simpa using hx) fun z hz => ?_
  by_cases hzΩ : z ∈ G.Ω 1
  · refine ⟨hzΩ, ?_⟩
    simp only [not_false_eq_true, iff_true]
    by_contra hzΛ
    exact hz (by simp only [zeroExt, hzΩ, ↓reduceDIte]; exact hu ⟨z, hzΩ⟩ hzΛ)
  · exact absurd (by simp [zeroExt, hzΩ]) hz

/-- **Block diagonality (inside).** If `u` vanishes on `Λ`, `H_cut u` vanishes on `Λ`. -/
theorem cutOperator_mulVec_apply_of_mem {Λ : Finset (Torus d (N₀ * L ^ k))}
    (hΛ : BlockAligned G Λ) {a : ℕ → ℝ} {ν : ℝ} (α : G.Ω 1 → ℂ) {u : G.Ω 1 → ℂ}
    (hu : ∀ z : G.Ω 1, (z : Torus d (N₀ * L ^ k)) ∈ Λ → u z = 0) (x : G.Ω 1)
    (hx : (x : Torus d (N₀ * L ^ k)) ∈ Λ) :
    (cutOperator G a ν (cubeCut G Λ) α *ᵥ u) x = 0 := by
  have h := cutOperator_eq G (u := u) (f := cutOperator G a ν (cubeCut G Λ) α *ᵥ u) rfl x
  rw [hu x hx, mul_zero, add_zero] at h
  rw [← h]
  refine cutFullMatrix_row_decouple G hΛ True a ν x.2 (by simpa using hx) fun z hz => ?_
  by_cases hzΩ : z ∈ G.Ω 1
  · refine ⟨hzΩ, ?_⟩
    simp only [not_true_eq_false, iff_false]
    intro hzΛ
    exact hz (by simp only [zeroExt, hzΩ, ↓reduceDIte]; exact hu ⟨z, hzΩ⟩ hzΛ)
  · exact absurd (by simp [zeroExt, hzΩ]) hz

/-- **The Green's function of the cube is supported in the cube.** If `H_cut(α)` is invertible,
`f` is supported in `Λ` and `H_cut(α) u = f`, then `u` is supported in `Λ`. -/
theorem cutOperator_inv_supported {Λ : Finset (Torus d (N₀ * L ^ k))} (hΛ : BlockAligned G Λ)
    {a : ℕ → ℝ} {ν : ℝ} (α : G.Ω 1 → ℂ) (hU : IsUnit (cutOperator G a ν (cubeCut G Λ) α))
    {f : G.Ω 1 → ℂ} (hf : ∀ z : G.Ω 1, (z : Torus d (N₀ * L ^ k)) ∉ Λ → f z = 0)
    {u : G.Ω 1 → ℂ} (hu : cutOperator G a ν (cubeCut G Λ) α *ᵥ u = f) :
    ∀ z : G.Ω 1, (z : Torus d (N₀ * L ^ k)) ∉ Λ → u z = 0 := by
  classical
  set H := cutOperator G a ν (cubeCut G Λ) α with hH
  set w : G.Ω 1 → ℂ := fun z => if (z : Torus d (N₀ * L ^ k)) ∈ Λ then u z else 0 with hw
  set v : G.Ω 1 → ℂ := fun z => if (z : Torus d (N₀ * L ^ k)) ∈ Λ then 0 else u z with hv
  have huv : u = w + v := by
    funext z
    by_cases h : (z : Torus d (N₀ * L ^ k)) ∈ Λ <;> simp [hw, hv, h]
  have hHv : H *ᵥ v = 0 := by
    funext x
    have hsplit : (H *ᵥ u) x = (H *ᵥ w) x + (H *ᵥ v) x := by
      rw [huv, Matrix.mulVec_add]; rfl
    by_cases hx : (x : Torus d (N₀ * L ^ k)) ∈ Λ
    · exact cutOperator_mulVec_apply_of_mem G hΛ α (fun z hz => by simp [hv, hz]) x hx
    · have h1 : (H *ᵥ w) x = 0 :=
        cutOperator_mulVec_apply_of_not_mem G hΛ α (fun z hz => by simp [hw, hz]) x hx
      have h2 : (H *ᵥ u) x = 0 := by rw [hu]; exact hf x hx
      rw [h1, h2, zero_add] at hsplit
      exact hsplit.symm
  have hdet : H.det ≠ 0 := by
    have := (Matrix.isUnit_iff_isUnit_det _).1 hU
    exact this.ne_zero
  have hv0 : v = 0 := Matrix.eq_zero_of_mulVec_eq_zero hdet hHv
  intro z hz
  have := congrFun hv0 z
  simpa [hv, hz] using this

end Balaban.Multiscale
