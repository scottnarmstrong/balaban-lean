module

public import Balaban.LargeField.R.KeptOutcomeThreeLocal

/-!
# Local consequences of nonzero third kept weight

The third outcome weight has the factor `1 - chiZero`. Thus a nonzero
weight gives a failed cube characteristic for `psiPrime`. The landed BG
bridge then gives a local small-field violation on the tested blocks.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background RegionHistory

/-- The support of `ϰ₃` contains a failed cube characteristic on the
modified field, with no separate `chiZero = 0` premise. -/
theorem kept_three_weight_has_bad_cube {S : Setting} {n : ℕ → ℕ}
    [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K N : ℕ} [NeZero M] [NeZero S.L]
    (g : Geo S n R M) (hnn : ∀ i, i < K → n i = S.L * n (i + 1))
    (cs : OpConsts) (hv : EuclideanSpace ℝ (Fin N))
    (k1 : ℕ) (hk1K : k1 ≤ K) (U : Set (Torus S.d (n k1)))
    (Lam U3 : Set (Torus S.d (M * n K * S.L ^ K)))
    (psi0 : EuclideanSpace ℝ (Fin N))
    (ψ : BlockAt S n M K k1 → EuclideanSpace ℝ (Fin N))
    (t s w u : ℝ)
    (hweight : Outcome.weight t s
      (chiZero g hnn cs hv k1 hk1K U Lam U3 psi0 ψ) w u Outcome.kappa3 ≠ 0) :
    ∃ y ∈ cubeFin (S := S) (chiZeroCubes (S := S) (n := n) k1 U),
      chiK (M1 := g.M1) (N₁ := g.c * n k1) (L := S.L) (q := k1) (N := N)
        cs.aw (cs.mu k1) (cs.delta k1 / 2) (fun i => hv i) g.c (n k1) y
        (blockCfgOf g hnn le_rfl hk1K (psiPrime (S := S) (n := n) (M := M) (K := K)
          k1 Lam U3 psi0 ψ)) = 0 := by
  exact chiZero_zero_has_bad_cube g hnn cs hv k1 hk1K U Lam U3 psi0 ψ
    (kept_three_weight_support g hnn cs hv k1 hk1K U Lam U3 psi0 ψ t s w u hweight)

/-- The local `PsiTildeSet` violation directly on nonzero `ϰ₃` weight,
without an extra characteristic-function hypothesis. -/
theorem kept_three_not_psiTilde_of_geo {S : Setting} {n : ℕ → ℕ}
    [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K N : ℕ} [NeZero M] [NeZero S.L]
    (g : Geo S n R M)
    (hnn : ∀ i, i < K → n i = S.L * n (i + 1))
    (cs : OpConsts) (hv : EuclideanSpace ℝ (Fin N))
    (k1 : ℕ) (hk1 : 1 ≤ k1) (hk1K : k1 ≤ K)
    (U : Set (Torus S.d (n k1)))
    (Lam U3 : Set (Torus S.d (M * n K * S.L ^ K)))
    (psi0 : EuclideanSpace ℝ (Fin N))
    (ψ : BlockAt S n M K k1 → EuclideanSpace ℝ (Fin N))
    (Hbg : BgHyp S.d S.L k1 (minSep S.L g.M1) cs.aw 0)
    (K1 : ℝ) (hδ : 0 < cs.delta k1) (hK1 : 0 < K1)
    (hK1b : bgK1 S.d S.L N ≤ K1)
    (hδ1 : cs.delta k1 ≤ 6 * K1)
    (hδc : cs.delta k1 ≤ 2 * K1 * bgC1 S.d S.L N)
    (hmu : cs.mu k1 = 0)
    {X : Finset (Site S.d S.L (g.M1 * (g.c * n k1)) k1)}
    (hX : IsBlockUnion S.L (g.M1 * (g.c * n k1)) k1 k1 X)
    (hgeo : ∀ y0 ∈ cubeFin (S := S) (chiZeroCubes (S := S) (n := n) k1 U),
      ∀ x ∈ dataSites
        (genCube (M1 := g.M1) (N₁ := g.c * n k1) (L := S.L) (q := k1)
          g.c (n k1) y0), x ∈ X)
    (t s w u : ℝ)
    (hweight : Outcome.weight t s
      (chiZero g hnn cs hv k1 hk1K U Lam U3 psi0 ψ) w u Outcome.kappa3 ≠ 0) :
    ¬ PsiTildeSet
      {y : Blk S.d S.L (g.M1 * (g.c * n k1)) k1 k1 |
        fib S.d S.L (g.M1 * (g.c * n k1)) k1 k1 y ⊆ X}
      (fun z => (WithLp.toLp 2
        (blockCfgOf g hnn le_rfl hk1K (psiPrime (S := S) (n := n) (M := M) (K := K)
          k1 Lam U3 psi0 ψ) z) : EuclideanSpace ℝ (Fin N)))
      ((cs.delta k1 / 2) / (6 * K1)) := by
  exact chiZero_not_psiTilde_of_geo g hnn cs hv k1 hk1 hk1K U Lam U3 psi0 ψ
    Hbg K1 hδ hK1 hK1b hδ1 hδc hmu hX hgeo
    (kept_three_weight_support g hnn cs hv k1 hk1K U Lam U3 psi0 ψ t s w u hweight)

end Balaban.LargeField
