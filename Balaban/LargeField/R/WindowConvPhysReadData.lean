/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.WindowConvPhysReadPiece
public import Balaban.LargeField.R.WindowConvPhysReadGlue
public import Balaban.LargeField.Operators.MainAction
public import Balaban.LargeField.R.WindowCompose
public import Balaban.LargeField.R.DeltaPsiCollar
public import Balaban.LargeField.R.RRemovedHidLeaf

/-!
# The data of a piece, read on the window

The datum `locData` of a piece is real on its data sites and constant on the blocks of the layers of
its generating set; the blocks of the torus identified with the window torus correspond.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Fluctuation RegionHistory Balaban.Background

section Real

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} (g : Geo S n R M) (Hl : RegionHistory S n R k0 K) (k : ℕ)
  (Zc : Finset (Torus S.d (n (k + 1)))) (hZc : Zc ∈ comps (S.omega (k + 1)) (Hl.F.Zp (k + 1)))
  (hk : k + 1 ≤ K)

/-- The datum of a piece is a real vector at every data site (P7 (2.14)). -/
theorem locData_Ψ_real (o : OutT N R (locHist Hl M K (k + 1) Zc) (k + 1))
    (x : NewCfg N (locHist Hl M K (k + 1) Zc) k) (hv : EuclideanSpace ℝ (Fin N))
    {y : Torus S.d (g.M1 * (g.c * n (k + 1)) * S.L ^ (k + 1))}
    (hy : y ∈ dataSites (locGen g Hl k Zc hZc hk)) :
    ∃ r : Fin N → ℝ, (locData g Hl k Zc hZc hk o x hv).Ψ y = fun q => (r q : ℂ) := by
  unfold locData
  rw [liftMixed_Ψ _ _ _ _ _ _ hy]
  unfold mixedLift
  split_ifs
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

end Real

section Blocks

variable {d L N₀w kw N₀l kl : ℕ} [NeZero N₀w] [NeZero N₀l] [NeZero L] {ϱw ϱl : ℝ}

/-- The blocks of two generating sets on identified tori correspond. -/
theorem torusCast_mem_blk (Gw : GeneratingSet d L N₀w kw ϱw) (Gl : GeneratingSet d L N₀l kl ϱl)
    (hT : N₀w * L ^ kw = N₀l * L ^ kl) {q : ℕ} (hqw : q ≤ kw) (hql : q ≤ kl)
    (hB : N₀w * L ^ (kw - q) = N₀l * L ^ (kl - q)) (x x' : Torus d (N₀w * L ^ kw)) :
    x' ∈ Gw.blk q x ↔ torusCast hT x' ∈ Gl.blk q (torusCast hT x) := by
  rw [GeneratingSet.mem_blk, GeneratingSet.mem_blk, jBlock_torusCast hqw hql hT hB,
    jBlock_torusCast hqw hql hT hB]
  exact (torusCast_injective hB).eq_iff.symm

end Blocks

end Balaban.LargeField
