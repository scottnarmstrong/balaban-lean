/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RRemovedHidGaussEqConst
public import Balaban.LargeField.R.WindowIdeal

/-!
# The composed mean of a block tree is the site average (W940)

`notes/phase1/LF4R-PLAN.md` §8.5.  `tree_mean_eq_site_avg`: if a finite set `X` of sites is partitioned into the
leaves of a block tree `B` (a map `lf` with `m^{n_x}` sites over the leaf `x` of scale `n_x`, `m = L^d`), then
`V⁻¹ ∑_s ϖ_{n_{lf s}} ψ^G(lf s) = 𝒬^♮_z ψ^G` (`composedMean`), `V = m^k`.
`compMeanT_re_eq_composedMean`: the same for `compMeanT` (`CancelIdentity.lean`) of real data: the real part of
`compMeanT G ϖ Ψ z i` is the component `i` of the composed mean, given the leaf correspondence `lf` of the sites
of `fib z` (the hypotheses `hcard`, `hscale`, `hval`, the identification of the history's block tree with the
generating set `G`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background

section Mean

variable {m k1 k N : ℕ} (B : BlockTree m k1 k)

open Classical in
theorem tree_mean_eq_site_avg {X : Type*} [Fintype X] (lf : X → Fin B.nLeaf)
    (hcard : ∀ x, (Finset.univ.filter fun s : X => lf s = x).card = m ^ B.leafScale x)
    (hm : 0 < m) (z : ℕ → ℝ) (ψG : Fin B.nLeaf → EuclideanSpace ℝ (Fin N)) :
    ((m : ℝ) ^ k)⁻¹ • ∑ s : X, varpi k z (B.leafScale (lf s)) • ψG (lf s) =
      B.composedMean z ψG := by
  have h1 : ∑ s : X, varpi k z (B.leafScale (lf s)) • ψG (lf s) =
      ∑ x : Fin B.nLeaf, ((m : ℝ) ^ B.leafScale x) • (varpi k z (B.leafScale x) • ψG x) := by
    rw [← Finset.sum_fiberwise Finset.univ lf]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_congr rfl (fun s hs => by rw [(Finset.mem_filter.mp hs).2]), Finset.sum_const,
      hcard x, ← Nat.cast_smul_eq_nsmul ℝ]
    push_cast
    rfl
  rw [h1, Finset.smul_sum]
  unfold BlockTree.composedMean
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [smul_smul, smul_smul]
  congr 1
  have hn := (B.leafScale_lt x).le
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  unfold blockFrac
  have key : (m : ℝ) ^ k = (m : ℝ) ^ B.leafScale x * (m : ℝ) ^ (k - B.leafScale x) := by
    rw [← pow_add]; congr 1; omega
  rw [key]
  field_simp

end Mean


section Comp

open Balaban.LargeField.ActionConv

variable {d L N₀ k k1 N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

open Classical in
theorem compMeanT_re_eq_composedMean (G : GeneratingSet d L N₀ k ϱ) (B : BlockTree (L ^ d) k1 k)
    (hm : 0 < L ^ d) (zz : ℕ → ℝ) (Ψ : Torus d (N₀ * L ^ k) → Fin N → ℂ)
    (z : Torus d (N₀ * L ^ (k - k))) (ψG : Fin B.nLeaf → EuclideanSpace ℝ (Fin N))
    (lf : ↥(fib d L N₀ k k z) → Fin B.nLeaf)
    (hcard : ∀ x, (Finset.univ.filter fun s : ↥(fib d L N₀ k k z) => lf s = x).card =
      (L ^ d) ^ B.leafScale x)
    (hscale : ∀ s : ↥(fib d L N₀ k k z), G.layerIndex s.1 = B.leafScale (lf s))
    (hval : ∀ s : ↥(fib d L N₀ k k z), ∀ i, (Ψ s.1 i).re = ψG (lf s) i) (i : Fin N) :
    (compMeanT G (varpi k zz) Ψ z i).re = (B.composedMean zz ψG) i := by
  have h := congrFun (congrArg (fun v : EuclideanSpace ℝ (Fin N) => (v : Fin N → ℝ))
    (tree_mean_eq_site_avg B lf hcard hm zz ψG)) i
  simp only [PiLp.smul_apply, WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul] at h
  rw [← h]
  unfold compMeanT
  have hV : (blockVol d L k : ℝ) = ((L ^ d : ℕ) : ℝ) ^ k := by
    unfold blockVol; push_cast; rw [← pow_mul, ← pow_mul, mul_comm]
  rw [hV, ← Finset.sum_coe_sort (fib d L N₀ k k z)]
  rw [← Complex.ofReal_inv, Complex.re_ofReal_mul, Complex.re_sum]
  congr 1
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Complex.re_ofReal_mul, hval s i, hscale s]

end Comp


section Weight

variable {d L N₀ k k1 : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

open Classical in
/-- **`compWeightZ` is the block-tree weight** (`blockWeight`, `WindowIdeal.lean`): with the leaf correspondence
`lf` of the sites of `fib z`, `a_z⁻¹ = V⁻¹ ∑_{s ∈ z} u_{k - n_s} = ∑_x w_x u_{k - n_x}`.  With
`composedWeight_ideal` this gives `β_k a^♮_z = β_k a_z` for `z ≡ 1` and the ideal coefficients. -/
theorem compWeightZ_eq_blockWeight (G : GeneratingSet d L N₀ k ϱ) (B : BlockTree (L ^ d) k1 k)
    (hm : 0 < L ^ d) (a₁ : ℝ) (z : Blk d L N₀ k k)
    (lf : ↥(fib d L N₀ k k z) → Fin B.nLeaf)
    (hcard : ∀ x, (Finset.univ.filter fun s : ↥(fib d L N₀ k k z) => lf s = x).card =
      (L ^ d) ^ B.leafScale x)
    (hscale : ∀ s : ↥(fib d L N₀ k k z), G.layerIndex s.1 = B.leafScale (lf s)) :
    compWeightZ G a₁ z = B.blockWeight L a₁ := by
  unfold compWeightZ BlockTree.blockWeight
  congr 1
  have hV : (blockVol d L k : ℝ) = ((L ^ d : ℕ) : ℝ) ^ k := by
    unfold blockVol; push_cast; rw [← pow_mul, ← pow_mul, mul_comm]
  rw [hV, ← Finset.sum_coe_sort (fib d L N₀ k k z)]
  have h1 : ∑ s : ↥(fib d L N₀ k k z), (compWeight L a₁ (k - G.layerIndex s.1))⁻¹ =
      ∑ x : Fin B.nLeaf, (((L ^ d : ℕ) : ℝ) ^ B.leafScale x) *
        (compWeight L a₁ (k - B.leafScale x))⁻¹ := by
    rw [Finset.sum_congr rfl (fun s _ => by rw [hscale s]),
      ← Finset.sum_fiberwise Finset.univ lf]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_congr rfl (fun s hs => by rw [(Finset.mem_filter.mp hs).2]), Finset.sum_const,
      hcard x]
    simp
  rw [h1, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hn := (B.leafScale_lt x).le
  have hm' : ((L ^ d : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  unfold blockFrac
  have key : ((L ^ d : ℕ) : ℝ) ^ k = ((L ^ d : ℕ) : ℝ) ^ B.leafScale x *
      ((L ^ d : ℕ) : ℝ) ^ (k - B.leafScale x) := by
    rw [← pow_add]; congr 1; omega
  rw [key]
  field_simp

end Weight

theorem composedPrecision_eq_mul_composedWeight {m k1 k : ℕ} (B : BlockTree m k1 k) {βk : ℝ}
    (hβ : βk ≠ 0) (c z : ℕ → ℝ) :
    B.composedPrecision c z = βk * B.composedWeight βk c z := by
  unfold BlockTree.composedWeight
  field_simp

end Balaban.LargeField
