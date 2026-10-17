/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RRemovedHidLeafRootMap
public import Balaban.LargeField.R.CancelIdentity

/-!
# The tree mean of a root of the window is the site average of the window generating set (W942)

`notes/phase1/LF4R-PLAN.md` §8.5.  `root_mean`: `hμ` of `prod_roots_eq_constNat_exp` for a fixed root `r` of the forest of
the window: `ut r - 𝒬^♮_r ψ^G = (ψ_k(z) - compMeanT G ϖ Ψ z)` (real parts), with the leaf values `fldv` of the tree and the
data relation `hΨ` (`Ψ` is the multiscale field `fldv` on the layers of the sites of the block `z`) and `hGlay`
(the layers of `G` and of the window's `full` agree on the block).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale RegionHistory

section RootMean

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {H : RegionHistory S n R k0 K} {m' : ℕ}

theorem root_mean (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) (hmK : m' + 1 ≤ K) (hL : 2 ≤ S.L)
    (hR : ∀ j, 1 ≤ j → j < m' + 1 → S.Rb ≤ R j) {Z : H.Comp (m' + 1)} {k1 : ℕ} (hk1p : 1 ≤ k1)
    (hk1 : k1 ≤ m') (nd : (Σ s, BlockAt S n M K s) → Prop)
    (hnd : ∀ j (y : BlockAt S n M K (j + 1)), nd ⟨j + 1, y⟩ ↔ (k1 ≤ j ∧ j ≤ m' ∧
      ∃ c ∈ H.ancFin (j + 1) (m' + 1) Z, y ∈ gaussBlocks (H.localHistory M K (j + 1) c) j))
    (hnd0 : ∀ y : BlockAt S n M K 0, ¬ nd ⟨0, y⟩)
    [Fintype {b : Σ s, BlockAt S n M K s // nd b}]
    [Fintype {q : (Σ s, BlockAt S n M K s) × {b : Σ s, BlockAt S n M K s // nd b} //
      (⟨q.1.1 + 1, blockMap S.L (M * n K * S.L ^ (K - (q.1.1 + 1))) q.1.2⟩ :
        Σ s, BlockAt S n M K s) = q.2.1 ∧ ¬ nd q.1}]
    (pa : {b : Σ s, BlockAt S n M K s // nd b} → {b : Σ s, BlockAt S n M K s // nd b})
    (hpa : ∀ b : {b : Σ s, BlockAt S n M K s // nd b},
      (nd ⟨b.1.1 + 1, blockMap S.L (M * n K * S.L ^ (K - (b.1.1 + 1))) b.1.2⟩ ∧ b.1.1 + 1 ≤ m' + 1 →
        (pa b).1 = ⟨b.1.1 + 1, blockMap S.L (M * n K * S.L ^ (K - (b.1.1 + 1))) b.1.2⟩) ∧
      (¬ (nd ⟨b.1.1 + 1, blockMap S.L (M * n K * S.L ^ (K - (b.1.1 + 1))) b.1.2⟩ ∧
        b.1.1 + 1 ≤ m' + 1) → pa b = b))
    (r : {r : {b : Σ s, BlockAt S n M K s // nd b} // pa r = r}) (y : BlockAt S n M K (m' + 1))
    (hry : r.1.1 = ⟨m' + 1, y⟩) (B : BlockTree (S.L ^ S.d) k1 r.1.1.1)
    (e : {i : {b : Σ s, BlockAt S n M K s // nd b} //
      pa^[Fintype.card {b : Σ s, BlockAt S n M K s // nd b}] i = r.1} ≃ Fin (B.n + 1))
    (el : {l : {q : (Σ s, BlockAt S n M K s) × {b : Σ s, BlockAt S n M K s // nd b} //
        (⟨q.1.1 + 1, blockMap S.L (M * n K * S.L ^ (K - (q.1.1 + 1))) q.1.2⟩ :
          Σ s, BlockAt S n M K s) = q.2.1 ∧ ¬ nd q.1} //
      pa^[Fintype.card {b : Σ s, BlockAt S n M K s // nd b}] l.1.2 = r.1} ≃ Fin B.nLeaf)
    (hsc : ∀ i, B.scale (e i) = i.1.1.1)
    (hleaf : ∀ l, B.leafPar (el l) = e ⟨l.1.1.2, l.2⟩)
    (hyk1 : ∀ x : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1)),
      jBlock S.d S.L (M * n K) K (m' + 1) (torusCast (fine_eq_top hnn hmK).symm x) = y →
        x ∉ H.locFine Z M k1)
    (z : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1 - (m' + 1))))
    (hzy : ∀ s, s ∈ fib S.d S.L (M * n (m' + 1)) (m' + 1) (m' + 1) z ↔
      jBlock S.d S.L (M * n K) K (m' + 1) (torusCast (fine_eq_top hnn hmK).symm s) = y)
    {ϱ : ℝ} (G : GeneratingSet S.d S.L (M * n (m' + 1)) (m' + 1) ϱ)
    (hGlay : ∀ s ∈ fib S.d S.L (M * n (m' + 1)) (m' + 1) (m' + 1) z,
      G.layerIndex s = (H.locGen Z M hmK hL hR).layerIndex s)
    {N : ℕ} (zz : ℕ → ℝ) (Ψ : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1)) → Fin N → ℂ)
    (ψk : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1 - (m' + 1))) → Fin N → ℂ)
    (fldv : ∀ s, BlockAt S n M K s → EuclideanSpace ℝ (Fin N))
    (ut : {b : Σ s, BlockAt S n M K s // nd b} → EuclideanSpace ℝ (Fin N))
    (hΨ : ∀ s ∈ fib S.d S.L (M * n (m' + 1)) (m' + 1) (m' + 1) z, ∀ i,
      Ψ s i = ((fldv ((H.locGen Z M hmK hL hR).layerIndex s)
        (jBlock S.d S.L (M * n K) K ((H.locGen Z M hmK hL hR).layerIndex s)
          (torusCast (fine_eq_top hnn hmK).symm s)) i : ℝ) : ℂ))
    (hψk : ∀ i, ψk z i = ((ut r.1 i : ℝ) : ℂ)) :
    ut r.1 - B.composedMean zz (fun x => fldv ((el.symm x).1.1.1.1) ((el.symm x).1.1.1.2)) =
      (WithLp.toLp 2 fun i => (ψk z i - ActionConv.compMeanT G (varpi (m' + 1) zz) Ψ z i).re :
        EuclideanSpace ℝ (Fin N)) := by
  classical
  have hm : 0 < S.L ^ S.d := by have := NeZero.pos S.L; positivity
  obtain ⟨lf, hcard, hscale, hblk⟩ := root_leaf_map hnn hmK hL hR hk1p hk1 nd hnd hnd0 pa hpa r y hry B e el
    hsc hleaf hyk1 z hzy
  have hkey : ∀ i, (ActionConv.compMeanT G (varpi (m' + 1) zz) Ψ z i).re =
      (B.composedMean zz (fun x => fldv ((el.symm x).1.1.1.1) ((el.symm x).1.1.1.2))) i := by
    intro i
    obtain ⟨⟨⟨s0, y0⟩, hnd'⟩, hpr⟩ := r
    obtain ⟨hs0, hy0⟩ := Sigma.mk.inj_iff.mp hry
    subst hs0
    exact compMeanT_re_eq_composedMean G B hm zz Ψ z
      (fun x => fldv ((el.symm x).1.1.1.1) ((el.symm x).1.1.1.2)) lf hcard
      (fun s => (hGlay s.1 s.2).trans (hscale s))
      (fun s i => by
        rw [hΨ s.1 s.2 i, Complex.ofReal_re]
        have := hblk s
        show _ = (fldv ((el.symm (lf s)).1.1.1.1) ((el.symm (lf s)).1.1.1.2)) i
        rw [this])
      i
  ext i
  simp only [PiLp.sub_apply, Complex.sub_re, hψk, Complex.ofReal_re, hkey]

end RootMean

end Balaban.LargeField
