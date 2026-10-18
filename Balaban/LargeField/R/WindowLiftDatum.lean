/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.WindowLiftGeom
public import Balaban.LargeField.R.WindowRegion
public import Balaban.LargeField.R.WindowConvPhysReadData
public import Balaban.LargeField.R.RRemovedHidLeafRoot
public import Balaban.LargeField.R.RRemovedHidLeafSite

/-!
# The datum of a piece at a window site, in terms of blocks of the history torus

P7 p. 501 (2.14).  At a data site of the local generating set of the piece `(j, c)` the datum
`locData` is `ψ_{j+1}` of the output on the `(j+1)`-block of the site if the site lies over
`Ω` of the step `j`, and `ψ_j` of the new variables on its `j`-block otherwise.  Read on the
window torus the blocks are the casts of the blocks of the window site.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale RegionHistory Balaban.Background

theorem torusCast_torusCast_comp {d a b c : ℕ} (h1 : a = b) (h2 : b = c) (x : Torus d a) :
    torusCast h2 (torusCast h1 x) = torusCast (h1.trans h2) x := by
  subst h1; subst h2; rfl

section Datum

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {H : RegionHistory S n R k0 K} {N : ℕ}

open Classical in
/-- **The datum of a piece at a data site, read on the window torus.** -/
theorem locData_Ψ_window (g : Geo S n R M) {m' j : ℕ} (hmK : m' + 1 ≤ K) (hj : j ≤ m')
    (c : H.Comp (j + 1)) (hK : j + 1 ≤ K)
    (o : OutT N R (locHist (H.locRH (j + 1) c) M K (j + 1) c.1) (j + 1))
    (x : NewCfg N (locHist (H.locRH (j + 1) c) M K (j + 1) c.1) j) (hv : EuclideanSpace ℝ (Fin N))
    {y : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1))}
    (hy : torusCast (piece_torus_eq g H.F.hnn hmK hj) y ∈
      dataSites (locGen g (H.locRH (j + 1) c) j c.1 (locComp_mem H hK c) hK)) :
    (locData g (H.locRH (j + 1) c) j c.1 (locComp_mem H hK c) hK o x hv).Ψ
        (torusCast (piece_torus_eq g H.F.hnn hmK hj) y) =
      fun q => (((if torusCast (piece_torus_eq g H.F.hnn hmK hj) y ∈
          fineK1 g.M1 g.c (n (j + 1)) S.L j ((H.locRH (j + 1) c).step j).Omega
        then outField N o (torusCast (blk_eq_top H.F.hnn hmK (Nat.succ_le_succ hj))
          (jBlock S.d S.L (M * n (m' + 1)) (m' + 1) (j + 1) y))
        else subVarField N x j (torusCast (blk_eq_top H.F.hnn hmK (hj.trans (Nat.le_succ _)))
          (jBlock S.d S.L (M * n (m' + 1)) (m' + 1) j y))) q : ℝ) : ℂ) := by
  classical
  unfold locData
  rw [liftMixed_Ψ _ _ _ _ _ _ hy]
  unfold mixedLift
  split_ifs with h
  · funext q
    unfold blockLift locLiftTheta blockCfgOf BlockCfg.toC
    simp only
    rw [jBlock_torusCast (Nat.succ_le_succ hj) le_rfl (piece_torus_eq g H.F.hnn hmK hj)
      (piece_block_eq g H.F.hnn hmK hj le_rfl)]
    rw [torusCast_torusCast_comp]
  · funext q
    unfold blockLift locLiftPsi blockCfgOf BlockCfg.toC
    simp only
    rw [jBlock_torusCast (hj.trans (Nat.le_succ _)) (Nat.le_succ _) (piece_torus_eq g H.F.hnn hmK hj)
      (piece_block_eq g H.F.hnn hmK hj (Nat.le_succ _))]
    rw [torusCast_torusCast_comp]

end Datum

end Balaban.LargeField
