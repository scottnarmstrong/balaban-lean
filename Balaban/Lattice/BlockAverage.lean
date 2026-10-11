module

public import Balaban.Lattice.Blocks
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Block averaging and its adjoint

The block averaging operator `Q` of P1 §1 (pp. 103–110) on real fields on the torus, its adjoint
`Q*` for the weighted inner products of P1, and the orthogonal projection `Q* Q` onto
block-constant fields.

Conventions.
* A field is a function `Torus d ℓ → ℝ`; no measurability or topology is involved.
* `blockAverage N m` averages over the `N ^ d` sites of each block of side `N`
  (`ℓ = N * m`): `(Q φ) y = (N ^ d)⁻¹ ∑_{x ∈ block y} φ x`.
* `latticeInner w φ ψ = w * ∑ x, φ x * ψ x`. On the fine lattice of spacing `η` the weight is
  `w = η ^ d`; on the block lattice of spacing `N * η` it is `(N * η) ^ d = N ^ d * η ^ d`.
* The adjoint for these weights is the pull-back `(Q* ψ) x = ψ (block x)`
  (`blockAverage_adjoint`); hence `Q Q* = 1` (`blockAverage_blockPullback`).
* Powers `Q_j = Q ∘ ⋯ ∘ Q` are expressed by `blockAverage_comp` (and `blockAverage_pow_add`).
-/

@[expose] public section

namespace Balaban

open Finset

/-- The weighted inner product `w * ∑ᵢ φ i * ψ i`. -/
def latticeInner {ι : Type*} [Fintype ι] (w : ℝ) (φ ψ : ι → ℝ) : ℝ := w * ∑ i, φ i * ψ i

variable {d ℓ N m : ℕ} [NeZero ℓ] [NeZero m]

/-- The block averaging `Q`: average over the `N ^ d` sites of each block. -/
noncomputable def blockAverage (N m : ℕ) :
    (Torus d ℓ → ℝ) →ₗ[ℝ] (Torus d m → ℝ) where
  toFun φ y := ((N : ℝ) ^ d)⁻¹ * ∑ x ∈ blockFibre N m y, φ x
  map_add' φ ψ := by
    funext y
    simp [Finset.sum_add_distrib, mul_add]
  map_smul' c φ := by
    funext y
    simp [← Finset.mul_sum]
    ring

/-- The adjoint `Q*` of the block averaging (pull-back along the block map). -/
def blockPullback (N m : ℕ) : (Torus d m → ℝ) →ₗ[ℝ] (Torus d ℓ → ℝ) where
  toFun ψ x := ψ (blockMap N m x)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [NeZero m] in
theorem blockAverage_apply (φ : Torus d ℓ → ℝ) (y : Torus d m) :
    blockAverage N m φ y = ((N : ℝ) ^ d)⁻¹ * ∑ x ∈ blockFibre N m y, φ x := rfl

omit [NeZero ℓ] [NeZero m] in
theorem blockPullback_apply (ψ : Torus d m → ℝ) (x : Torus d ℓ) :
    blockPullback N m ψ x = ψ (blockMap N m x) := rfl

/-- Summing over blocks and then within blocks is summing over the torus. -/
theorem sum_blockFibre (f : Torus d ℓ → ℝ) (g : Torus d m → ℝ) :
    ∑ y, (∑ x ∈ blockFibre N m y, f x) * g y = ∑ x, f x * g (blockMap N m x) := by
  rw [← Finset.sum_fiberwise Finset.univ (blockMap N m) (fun x => f x * g (blockMap N m x))]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [(mem_blockFibre.mp hx)]

/-- `Q` and `Q*` are adjoint for the weights `w_c = N ^ d * w_f`
(the lattice spacings `η` and `N η` give `w_f = η ^ d`, `w_c = (N η) ^ d`). -/
theorem blockAverage_adjoint (hN : 0 < N)
    {wf wc : ℝ} (hw : wc = (N : ℝ) ^ d * wf) (φ : Torus d ℓ → ℝ) (ψ : Torus d m → ℝ) :
    latticeInner wc (blockAverage N m φ) ψ = latticeInner wf φ (blockPullback N m ψ) := by
  have hNd : ((N : ℝ) ^ d) ≠ 0 := by positivity
  unfold latticeInner
  simp only [blockAverage_apply, blockPullback_apply]
  rw [← sum_blockFibre (N := N) (m := m) φ ψ, hw, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  field_simp

/-- The adjoint relation in terms of the lattice spacings: `η ^ d` on the fine lattice and
`(N * η) ^ d` on the block lattice. -/
theorem blockAverage_adjoint_spacing (hN : 0 < N) (η : ℝ) (φ : Torus d ℓ → ℝ)
    (ψ : Torus d m → ℝ) :
    latticeInner (((N : ℝ) * η) ^ d) (blockAverage N m φ) ψ =
      latticeInner (η ^ d) φ (blockPullback N m ψ) :=
  blockAverage_adjoint hN (mul_pow _ _ _) φ ψ

theorem latticeInner_comm {ι : Type*} [Fintype ι] (w : ℝ) (φ ψ : ι → ℝ) :
    latticeInner w φ ψ = latticeInner w ψ φ := by
  unfold latticeInner
  simp only [mul_comm]

/-- `Q Q* = 1`. -/
theorem blockAverage_blockPullback (hℓ : ℓ = N * m) (hN : 0 < N) (ψ : Torus d m → ℝ) :
    blockAverage N m (blockPullback N m ψ : Torus d ℓ → ℝ) = ψ := by
  have hNd : ((N : ℝ) ^ d) ≠ 0 := by positivity
  funext y
  rw [blockAverage_apply]
  have : ∀ x ∈ (blockFibre N m y : Finset (Torus d ℓ)), blockPullback N m ψ x = ψ y := by
    intro x hx
    rw [blockPullback_apply, mem_blockFibre.mp hx]
  rw [Finset.sum_congr rfl this, Finset.sum_const, card_blockFibre hℓ]
  simp [hNd]

/-- A field is constant on the blocks of side `N`. -/
def IsBlockConstant (N m : ℕ) (φ : Torus d ℓ → ℝ) : Prop :=
  ∀ x x' : Torus d ℓ, blockMap N m x = blockMap N m x' → φ x = φ x'

/-- The projection `P = Q* Q` onto block-constant fields. -/
noncomputable def blockProjection (N m : ℕ) : (Torus d ℓ → ℝ) →ₗ[ℝ] (Torus d ℓ → ℝ) :=
  blockPullback N m ∘ₗ blockAverage N m

omit [NeZero m] in
theorem blockProjection_apply (φ : Torus d ℓ → ℝ) (x : Torus d ℓ) :
    blockProjection N m φ x = blockAverage N m φ (blockMap N m x) := rfl

/-- `P` is idempotent. -/
theorem blockProjection_idem (hℓ : ℓ = N * m) (hN : 0 < N) (φ : Torus d ℓ → ℝ) :
    blockProjection N m (blockProjection N m φ) = blockProjection N m φ := by
  unfold blockProjection
  simp only [LinearMap.comp_apply]
  rw [blockAverage_blockPullback hℓ hN]

/-- `P` is self-adjoint for the fine inner product, when the weights are compatible. -/
theorem blockProjection_selfAdjoint (hN : 0 < N) {wf wc : ℝ} (hw : wc = (N : ℝ) ^ d * wf)
    (φ ψ : Torus d ℓ → ℝ) :
    latticeInner wf (blockProjection N m φ) ψ = latticeInner wf φ (blockProjection N m ψ) := by
  unfold blockProjection
  simp only [LinearMap.comp_apply]
  rw [latticeInner_comm wf, ← blockAverage_adjoint hN hw (N := N) (m := m) ψ (blockAverage N m φ),
    ← blockAverage_adjoint hN hw (N := N) (m := m) φ (blockAverage N m ψ), latticeInner_comm]

omit [NeZero m] in
/-- The range of `P` consists of block-constant fields. -/
theorem blockProjection_isBlockConstant (φ : Torus d ℓ → ℝ) :
    IsBlockConstant N m (blockProjection N m φ) := by
  intro x x' h
  rw [blockProjection_apply, blockProjection_apply, h]

/-- The fixed points of `P` are exactly the block-constant fields. -/
theorem blockProjection_eq_self_iff (hℓ : ℓ = N * m) (hN : 0 < N) (φ : Torus d ℓ → ℝ) :
    blockProjection N m φ = φ ↔ IsBlockConstant N m φ := by
  constructor
  · intro h
    rw [← h]
    exact blockProjection_isBlockConstant φ
  · intro h
    have hNd : ((N : ℝ) ^ d) ≠ 0 := by positivity
    funext x
    rw [blockProjection_apply, blockAverage_apply]
    have : ∀ x' ∈ (blockFibre N m (blockMap N m x) : Finset (Torus d ℓ)), φ x' = φ x := fun x' hx' =>
      h x' x (mem_blockFibre.mp hx')
    rw [Finset.sum_congr rfl this, Finset.sum_const, card_blockFibre hℓ]
    simp [hNd]

/-- `φ - P φ` is orthogonal to every block-constant field. -/
theorem blockProjection_orthogonal (hℓ : ℓ = N * m) (hN : 0 < N) {wf wc : ℝ}
    (hw : wc = (N : ℝ) ^ d * wf) (φ χ : Torus d ℓ → ℝ) (hχ : IsBlockConstant N m χ) :
    latticeInner wf (φ - blockProjection N m φ) χ = 0 := by
  have h1 := blockProjection_selfAdjoint (m := m) hN hw φ χ
  rw [(blockProjection_eq_self_iff hℓ hN χ).mpr hχ] at h1
  unfold latticeInner at *
  simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib, mul_sub]
  rw [h1]
  ring

omit [NeZero m] in
/-- Composition of block averagings: `Q_{N M} = Q_M ∘ Q_N` (the power form is
`blockAverage_pow_add`). -/
theorem blockAverage_comp {m₁ m₂ M : ℕ} [NeZero m₁] [NeZero m₂] (hℓ : ℓ = N * m₁)
    (hm : m₁ = M * m₂) (φ : Torus d ℓ → ℝ) :
    blockAverage M m₂ (blockAverage N m₁ φ) = (blockAverage (N * M) m₂ φ : Torus d m₂ → ℝ) := by
  funext z
  simp only [blockAverage_apply]
  rw [← Finset.mul_sum, ← mul_assoc, Nat.cast_mul, mul_pow, mul_inv, mul_comm ((M : ℝ) ^ d)⁻¹]
  congr 1
  have hsum := Finset.sum_fiberwise_of_maps_to (s := (blockFibre (N * M) m₂ z : Finset (Torus d ℓ)))
    (t := (blockFibre M m₂ z : Finset (Torus d m₁))) (g := blockMap N m₁) (f := φ) (by
      intro x hx
      rw [mem_blockFibre] at hx ⊢
      rw [blockMap_comp hℓ hm, hx])
  rw [← hsum]
  refine Finset.sum_congr rfl fun y hy => ?_
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext x
  simp only [Finset.mem_filter, mem_blockFibre]
  constructor
  · intro h
    refine ⟨?_, h⟩
    rw [← blockMap_comp hℓ hm, h]
    exact mem_blockFibre.mp hy
  · exact fun h => h.2

/-- Power form: `Q_{L^{j+k}} = Q_{L^k} ∘ Q_{L^j}`. -/
theorem blockAverage_pow_add {m₁ m₂ L j k : ℕ} [NeZero m₁] [NeZero m₂]
    (hℓ : ℓ = L ^ j * m₁) (hm : m₁ = L ^ k * m₂) (φ : Torus d ℓ → ℝ) :
    blockAverage (L ^ k) m₂ (blockAverage (L ^ j) m₁ φ) =
      (blockAverage (L ^ (j + k)) m₂ φ : Torus d m₂ → ℝ) := by
  rw [blockAverage_comp hℓ hm, pow_add]

/-- The adjoints compose in the opposite order. -/
theorem blockPullback_comp {m₁ m₂ M : ℕ} [NeZero m₁] [NeZero m₂] (hℓ : ℓ = N * m₁)
    (hm : m₁ = M * m₂) (ψ : Torus d m₂ → ℝ) :
    blockPullback N m₁ (blockPullback M m₂ ψ : Torus d m₁ → ℝ) =
      (blockPullback (N * M) m₂ ψ : Torus d ℓ → ℝ) := by
  funext x
  simp only [blockPullback_apply]
  rw [blockMap_comp hℓ hm]

end Balaban
