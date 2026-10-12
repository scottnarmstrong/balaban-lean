module

public import Balaban.LargeField.Operators.MainAction
public import Balaban.Background.EquivarianceLat

/-!
# Lattice-symmetry covariance of the multiscale action

For a lattice symmetry `S : LatSymm G G' σ` of the torus (a signed permutation of the coordinate
directions composed with a translation, preserving the generating sets): the bond energies
`bondE`, `starBondE`, the block averages `bavgL` and the multiscale action `actionG` of
`LF1/Setup.lean` are covariant (`bondE_sym`, `starBondE_sym`, `bavgL_sym`, `actionG_sym`).  The
block permutations `β n` induced on the `n`-blocks enter as data: `β n (blkMap n x) = blkMap n (σ x)`.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background

set_option linter.unusedSectionVars false

section ActionSymm

variable {d L N₀ q : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}
  {G G' : GeneratingSet d L N₀ q ϱ} {σ : Equiv.Perm (Torus d (N₀ * L ^ q))}
  (S : LatSymm G G' σ)

include S

/-- bonds with both ends in `X`. -/
theorem _root_.Balaban.Background.LatSymm.bondE_sym {E : Type*} [NormedAddCommGroup E]
    (X : Finset (Torus d (N₀ * L ^ q))) (φ : Torus d (N₀ * L ^ q) → E) :
    bondE (X.map σ.toEmbedding) (fun z => φ (σ.symm z)) = bondE X φ := by
  classical
  unfold bondE bondEdir bondTerm
  rw [← Equiv.sum_comp S.perm]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [← Equiv.sum_comp σ]
  have hmem : ∀ z, σ z ∈ X.map σ.toEmbedding ↔ z ∈ X := fun z => by simp
  cases hf : S.flip μ
  · refine Finset.sum_congr rfl fun y _ => ?_
    have e := S.step y μ
    simp only [hf, Bool.false_eq_true, ↓reduceIte] at e
    rw [← e]
    simp only [hmem, Equiv.symm_apply_apply]
  · conv_rhs => rw [← Equiv.sum_comp (Equiv.subRight (Pi.single μ 1 : Torus d (N₀ * L ^ q)))]
    refine Finset.sum_congr rfl fun y _ => ?_
    have e := S.step_sub y μ
    simp only [hf, ↓reduceIte] at e
    rw [← e]
    simp only [hmem, Equiv.symm_apply_apply, Equiv.subRight_apply, sub_add_cancel]
    exact if_congr and_comm (by rw [norm_sub_rev]) rfl


theorem _root_.Balaban.Background.LatSymm.starBondE_sym {E : Type*} [NormedAddCommGroup E]
    (X : Finset (Torus d (N₀ * L ^ q))) (φ : Torus d (N₀ * L ^ q) → E) :
    starBondE (X.map σ.toEmbedding) (fun z => φ (σ.symm z)) = starBondE X φ := by
  classical
  unfold starBondE bondTerm
  rw [← Equiv.sum_comp S.perm]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [← Equiv.sum_comp σ]
  have hmem : ∀ z, σ z ∈ X.map σ.toEmbedding ↔ z ∈ X := fun z => by simp
  cases hf : S.flip μ
  · refine Finset.sum_congr rfl fun y _ => ?_
    have e := S.step y μ
    simp only [hf, Bool.false_eq_true, ↓reduceIte] at e
    rw [← e]
    simp only [hmem, Equiv.symm_apply_apply]
  · conv_rhs => rw [← Equiv.sum_comp (Equiv.subRight (Pi.single μ 1 : Torus d (N₀ * L ^ q)))]
    refine Finset.sum_congr rfl fun y _ => ?_
    have e := S.step_sub y μ
    simp only [hf, ↓reduceIte] at e
    rw [← e]
    simp only [hmem, Equiv.symm_apply_apply, Equiv.subRight_apply, sub_add_cancel]
    exact if_congr (by tauto) (by rw [norm_sub_rev]) rfl


theorem _root_.Balaban.Background.LatSymm.bavgL_sym {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (n : ℕ) (β : Equiv.Perm (Blk d L N₀ q n))
    (hβ : ∀ x, blkMap d L N₀ q n (σ x) = β (blkMap d L N₀ q n x))
    (φ : Site d L N₀ q → E) (y : Blk d L N₀ q n) :
    bavgL d L N₀ q n (fun z => φ (σ.symm z)) (β y) = bavgL d L N₀ q n φ y := by
  unfold bavgL bavg
  congr 1
  refine Finset.sum_equiv σ.symm (fun x' => ?_) (fun x' _ => rfl)
  rw [mem_blockFibre, mem_blockFibre]
  have h := hβ (σ.symm x')
  rw [Equiv.apply_symm_apply] at h
  change blkMap d L N₀ q n x' = β y ↔ blkMap d L N₀ q n (σ.symm x') = y
  rw [h]
  exact β.injective.eq_iff

theorem _root_.Balaban.Background.LatSymm.tBlocks_sym (n : ℕ) (hn : 1 ≤ n)
    (hnq : n ≤ q) (β : Equiv.Perm (Blk d L N₀ q n))
    (hβ : ∀ x, blkMap d L N₀ q n (σ x) = β (blkMap d L N₀ q n x))
    (X : Finset (Site d L N₀ q)) (y : Blk d L N₀ q n) :
    y ∈ tBlocks d L N₀ q n (lam G' n ∩ X.map σ.toEmbedding) ↔
      β.symm y ∈ tBlocks d L N₀ q n (lam G n ∩ X) := by
  unfold tBlocks lam
  simp only [Finset.mem_image, Finset.mem_inter, Finset.mem_map_equiv, show n ≠ 0 by omega,
    ↓reduceIte]
  constructor
  · rintro ⟨x', ⟨hx1, hx2⟩, rfl⟩
    refine ⟨σ.symm x', ⟨?_, hx2⟩, ?_⟩
    · have := (S.mem_layer hn hnq (σ.symm x')).1
      rw [Equiv.apply_symm_apply] at this
      exact this hx1
    · have h := hβ (σ.symm x')
      rw [Equiv.apply_symm_apply] at h
      rw [h]; simp
  · rintro ⟨x, ⟨hx1, hx2⟩, hx⟩
    refine ⟨σ x, ⟨(S.mem_layer hn hnq x).2 hx1, by simpa using hx2⟩, ?_⟩
    rw [hβ, hx]; simp


/-- **Lattice-symmetry covariance of the multiscale action** `A_G(X; ψ, φ)` of §II.4: if `σ` is a
lattice symmetry from `G` to `G'` inducing the block permutations `β n` on the `n`-blocks
(`1 ≤ n ≤ q`), then `A_{G'}(σX; ψ', φ ∘ σ⁻¹) = A_G(X; ψ, φ)` for the fields with
`ψ'_n ∘ β_n = ψ_n`. -/
theorem _root_.Balaban.Background.LatSymm.actionG_sym {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (a : ℕ → ℝ) (μ : ℝ) (h : E) (X : Finset (Site d L N₀ q))
    (β : ∀ n, Equiv.Perm (Blk d L N₀ q n))
    (hβ : ∀ n, 1 ≤ n → n ≤ q → ∀ x, blkMap d L N₀ q n (σ x) = β n (blkMap d L N₀ q n x))
    (ψ ψ' : (m : ℕ) → Blk d L N₀ q m → E) (hψ : ∀ n y, ψ' n (β n y) = ψ n y)
    (φ : Site d L N₀ q → E) :
    actionG G' a μ h (X.map σ.toEmbedding) ψ' (fun z => φ (σ.symm z)) = actionG G a μ h X ψ φ := by
  unfold actionG
  congr 1
  congr 1
  · congr 1
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [Finset.mem_Icc] at hn
    refine Finset.sum_equiv (β n).symm (fun y => S.tBlocks_sym n hn.1 hn.2 (β n) (hβ n hn.1 hn.2) X y)
      (fun y _ => ?_)
    obtain ⟨y0, rfl⟩ := (β n).surjective y
    rw [Equiv.symm_apply_apply, hψ, S.bavgL_sym n (β n) (hβ n hn.1 hn.2) φ y0]
  · rw [S.bondE_sym]
  · rw [Finset.sum_map]
    simp

end ActionSymm
end Balaban.LargeField
