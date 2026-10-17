module

public import Balaban.LargeField.R.SmallFactorChi
public import Balaban.LargeField.R.Outcome

/-!
# Support of the third kept outcome

The factor `1 - chiZero` in `ϰ₃` forces failure of the scale-`k₁` cube
characteristic function on the modified field `psiPrime`.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale RegionHistory

/-- A finite product of characteristic values is again zero or one. -/
theorem finset_prod_zero_or_one {ι : Type*} (A : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ A, f i = 0 ∨ f i = 1) :
    (∏ i ∈ A, f i) = 0 ∨ (∏ i ∈ A, f i) = 1 := by
  classical
  by_cases hex : ∃ i ∈ A, f i = 0
  · obtain ⟨i, hi, h0⟩ := hex
    left
    exact Finset.prod_eq_zero hi h0
  · right
    have h1 : ∀ i ∈ A, f i = 1 := by
      intro i hi
      rcases hf i hi with h0 | h1
      · exact False.elim (hex ⟨i, hi, h0⟩)
      · exact h1
    exact Finset.prod_eq_one h1

/-- The landed `chiZero` is a characteristic value, despite its product
presentation. -/
theorem chiZero_eq_zero_or_one {S : Setting} {n : ℕ → ℕ}
    [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K N : ℕ} [NeZero M] [NeZero S.L]
    (g : Geo S n R M)
    (hnn : ∀ i, i < K → n i = S.L * n (i + 1))
    (cs : OpConsts) (hv : EuclideanSpace ℝ (Fin N))
    (k1 : ℕ) (hk1K : k1 ≤ K) (U : Set (Torus S.d (n k1)))
    (Lam U3 : Set (Torus S.d (M * n K * S.L ^ K)))
    (psi0 : EuclideanSpace ℝ (Fin N))
    (ψ : BlockAt S n M K k1 → EuclideanSpace ℝ (Fin N)) :
    chiZero g hnn cs hv k1 hk1K U Lam U3 psi0 ψ = 0 ∨
      chiZero g hnn cs hv k1 hk1K U Lam U3 psi0 ψ = 1 := by
  unfold chiZero chiProd cubeProd
  apply finset_prod_zero_or_one
  intro y hy
  exact charFn_eq_zero_or_one _ _

/-- A nonzero `ϰ₃` weight forces `chiZero = 0`, for arbitrary values of the
other outcome factors. -/
theorem kept_three_weight_support {S : Setting} {n : ℕ → ℕ}
    [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K N : ℕ} [NeZero M] [NeZero S.L]
    (g : Geo S n R M)
    (hnn : ∀ i, i < K → n i = S.L * n (i + 1))
    (cs : OpConsts) (hv : EuclideanSpace ℝ (Fin N))
    (k1 : ℕ) (hk1K : k1 ≤ K) (U : Set (Torus S.d (n k1)))
    (Lam U3 : Set (Torus S.d (M * n K * S.L ^ K)))
    (psi0 : EuclideanSpace ℝ (Fin N))
    (ψ : BlockAt S n M K k1 → EuclideanSpace ℝ (Fin N))
    (t s w u : ℝ)
    (hweight : Outcome.weight t s
      (chiZero g hnn cs hv k1 hk1K U Lam U3 psi0 ψ) w u Outcome.kappa3 ≠ 0) :
    chiZero g hnn cs hv k1 hk1K U Lam U3 psi0 ψ = 0 := by
  rcases chiZero_eq_zero_or_one g hnn cs hv k1 hk1K U Lam U3 psi0 ψ with h0 | h1
  · exact h0
  · simp [Outcome.weight, h1] at hweight

/-- Failure of `chiZero` occurs at one cube of `Uᶜ ∩ U^{∼6}` for the
modified field `psiPrime`. This is the cube to which the local and chain
cases of Lemma III.5.3 (c) apply. -/
theorem chiZero_zero_has_bad_cube {S : Setting} {n : ℕ → ℕ}
    [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K N : ℕ} [NeZero M] [NeZero S.L]
    (g : Geo S n R M) (hnn : ∀ i, i < K → n i = S.L * n (i + 1))
    (cs : OpConsts) (hv : EuclideanSpace ℝ (Fin N))
    (k1 : ℕ) (hk1K : k1 ≤ K) (U : Set (Torus S.d (n k1)))
    (Lam U3 : Set (Torus S.d (M * n K * S.L ^ K)))
    (psi0 : EuclideanSpace ℝ (Fin N))
    (ψ : BlockAt S n M K k1 → EuclideanSpace ℝ (Fin N))
    (hzero : chiZero g hnn cs hv k1 hk1K U Lam U3 psi0 ψ = 0) :
    ∃ y ∈ cubeFin (S := S) (chiZeroCubes (S := S) (n := n) k1 U),
      chiK (M1 := g.M1) (N₁ := g.c * n k1) (L := S.L) (q := k1) (N := N)
        cs.aw (cs.mu k1) (cs.delta k1 / 2) (fun i => hv i) g.c (n k1) y
        (blockCfgOf g hnn le_rfl hk1K (psiPrime (S := S) (n := n) (M := M) (K := K)
          k1 Lam U3 psi0 ψ)) = 0 := by
  unfold chiZero chiProd cubeProd at hzero
  exact Finset.prod_eq_zero_iff.mp hzero

end Balaban.LargeField
