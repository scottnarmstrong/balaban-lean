module

public import Balaban.LargeField.R.ChiBridge
public import Balaban.LargeField.R.KeptOutcomeThreeSupport
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The local violation behind the third kept outcome

This is the BG Theorem 5.2 (3) part of Lemma III.5.3 (c): failure of
`chiZero` gives a `PsiTildeSet` violation for the modified field `psiPrime`
on any union of `k₁` blocks containing the cube data sites. The further
boundary disagreement and chain argument are separate.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ}
  {M K N : ℕ} [NeZero S.L]

/-- A failed `chiZero` gives a violation at scale `k₁` of size
`(δ_{k₁}/2)/(6 K₁) = δ_{k₁}/(12 K₁)`. The geometric input states that the
data sites of each tested cube belong to `X`. -/
theorem chiZero_not_psiTilde_of_geo (g : Geo S n R M)
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
    (hχ : chiZero g hnn cs hv k1 hk1K U Lam U3 psi0 ψ = 0) :
    ¬ PsiTildeSet
      {y : Blk S.d S.L (g.M1 * (g.c * n k1)) k1 k1 |
        fib S.d S.L (g.M1 * (g.c * n k1)) k1 k1 y ⊆ X}
      (fun z => (WithLp.toLp 2
        (blockCfgOf g hnn le_rfl hk1K (psiPrime (S := S) (n := n) (M := M) (K := K)
          k1 Lam U3 psi0 ψ) z) : EuclideanSpace ℝ (Fin N)))
      ((cs.delta k1 / 2) / (6 * K1)) := by
  have hδhalf : 0 < cs.delta k1 / 2 := by positivity
  have hδhalf1 : cs.delta k1 / 2 ≤ 6 * K1 := by linarith
  have hδhalfc : cs.delta k1 / 2 ≤ 2 * K1 * bgC1 S.d S.L N := by linarith
  have hχ' := hχ
  unfold chiZero chiProd at hχ'
  rw [hmu] at hχ'
  exact not_psiTilde_of_cubeProd_eq_zero (c := g.c) (n := n k1)
    Hbg hk1 (by simp) hδhalf hK1 hK1b hδhalf1 hδhalfc
    (fun i => hv i) (cubeFin (S := S) (chiZeroCubes (S := S) (n := n) k1 U))
    (blockCfgOf g hnn le_rfl hk1K (psiPrime (S := S) (n := n) (M := M) (K := K)
      k1 Lam U3 psi0 ψ)) hX hgeo hχ'

end Balaban.LargeField
