/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RRemovedHidLeafRoot
public import Balaban.LargeField.R.RRemovedChainNodes

/-!
# The leaf map of a root of the window's forest (W942)

`notes/phase1/LF4R-PLAN.md` §8.5.  `root_leaf_map`: for a fixed root `r` (the top block `y` of scale `m' + 1`, not in
the box `Z₀ ⊇ Z_{k₁}`, hypothesis `hyk1`) of the forest of the Gaussian nodes of the window, with the numbering `e`, `el`
of its tree, the sites `s` of the `(m'+1)`-block `z` of `y` have a leaf map `lf` onto the leaves of the tree with
`(L^d)^{n}` sites over every leaf of scale `n` (`hcard`) and `layerIndex s` equal to the leaf scale (`hscale`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale RegionHistory

section RootMap

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {H : RegionHistory S n R k0 K} {m' : ℕ}

theorem root_leaf_map (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) (hmK : m' + 1 ≤ K) (hL : 2 ≤ S.L)
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
      jBlock S.d S.L (M * n K) K (m' + 1) (torusCast (fine_eq_top hnn hmK).symm s) = y) :
    ∃ lf : ↥(fib S.d S.L (M * n (m' + 1)) (m' + 1) (m' + 1) z) → Fin B.nLeaf,
      (∀ x, (Finset.univ.filter fun s => lf s = x).card = (S.L ^ S.d) ^ B.leafScale x) ∧
      (∀ s, (H.locGen Z M hmK hL hR).layerIndex s.1 = B.leafScale (lf s)) ∧
      ∀ s, (el.symm (lf s)).1.1.1 = ⟨(H.locGen Z M hmK hL hR).layerIndex s.1,
        jBlock S.d S.L (M * n K) K ((H.locGen Z M hmK hL hR).layerIndex s.1)
          (torusCast (fine_eq_top hnn hmK).symm s.1)⟩ := by
  classical
  have hnr : nd ⟨m' + 1, y⟩ := by
    have := r.1.2
    rwa [hry] at this
  have hsite : ∀ s : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1)),
      jBlock S.d S.L (M * n K) K (m' + 1) (torusCast (fine_eq_top hnn hmK).symm s) = y →
        s ∉ H.locFine Z M k1 ∧ s ∉ (H.locGen Z M hmK hL hR).Ω (m' + 1) := by
    intro s hs
    refine ⟨hyk1 s hs, ?_⟩
    obtain ⟨-, -, c, hc, hg⟩ := (hnd m' y).mp hnr
    have hxy := blockCube_castSite hnn hmK (j := m' + 1) hmK s
    rw [hs] at hxy
    exact ((gaussBlocks_iff_locGen (by omega) hmK (by omega) hL hR hc y s hxy.symm).mp hg).2
  have hex : ∀ s : ↥(fib S.d S.L (M * n (m' + 1)) (m' + 1) (m' + 1) z),
      ∃ l : {q : (Σ s, BlockAt S n M K s) × {b : Σ s, BlockAt S n M K s // nd b} //
        (⟨q.1.1 + 1, blockMap S.L (M * n K * S.L ^ (K - (q.1.1 + 1))) q.1.2⟩ :
          Σ s, BlockAt S n M K s) = q.2.1 ∧ ¬ nd q.1},
        l.1.1 = ⟨(H.locGen Z M hmK hL hR).layerIndex s.1,
          jBlock S.d S.L (M * n K) K ((H.locGen Z M hmK hL hR).layerIndex s.1)
            (torusCast (fine_eq_top hnn hmK).symm s.1)⟩ := by
    intro s
    have hs := (hzy s.1).mp s.2
    obtain ⟨h1, h2⟩ := hsite s.1 hs
    obtain ⟨hr1, hr2, hr3, hr4⟩ := site_range hmK hL hR hk1p hk1 h1 h2
    refine exists_leaf nd (yq := jBlock S.d S.L (M * n K) K
      ((H.locGen Z M hmK hL hR).layerIndex s.1) (torusCast (fine_eq_top hnn hmK).symm s.1)) ?_ ?_
    · have hndn := nd_block_of_not_mem hnn hmK hL hR nd hnd hr1 hr2
        (hr4 _ (Nat.lt_succ_self _) (by omega))
      rw [jBlock_succ_eq_blockMap (d := S.d) (L := S.L) (N₀ := M * n K) (k := K) (by omega)] at hndn
      exact hndn
    · exact not_nd_block_of_mem hnn hmK hL hR hk1p nd hnd hr1 (by omega) hr3
  choose ls hls using hex
  have hroot : ∀ s, pa^[Fintype.card {b : Σ s, BlockAt S n M K s // nd b}] (ls s).1.2 = r.1 := by
    intro s
    have hs := (hzy s.1).mp s.2
    obtain ⟨h1, h2⟩ := hsite s.1 hs
    obtain ⟨hr1, hr2, hr3, hr4⟩ := site_range hmK hL hR hk1p hk1 h1 h2
    have hpar := leaf_parent nd (ls s) (hls s)
    have h0 : (ls s).1.2.1 = ⟨(H.locGen Z M hmK hL hR).layerIndex s.1 + 1,
        jBlock S.d S.L (M * n K) K ((H.locGen Z M hmK hL hR).layerIndex s.1 + 1)
          (torusCast (fine_eq_top hnn hmK).symm s.1)⟩ := by
      rw [hpar, jBlock_succ_eq_blockMap (d := S.d) (L := S.L) (N₀ := M * n K) (k := K) (by omega)]
    have := chain_root hnn hmK hL hR hk1p hk1 nd hnd hnd0 pa hpa h1 h2 (ls s).1.2 h0
    exact Subtype.ext (this.trans (by rw [hs, hry]))
  have hcardL : ∀ l : {q : (Σ s, BlockAt S n M K s) × {b : Σ s, BlockAt S n M K s // nd b} //
        (⟨q.1.1 + 1, blockMap S.L (M * n K * S.L ^ (K - (q.1.1 + 1))) q.1.2⟩ :
          Σ s, BlockAt S n M K s) = q.2.1 ∧ ¬ nd q.1},
      pa^[Fintype.card {b : Σ s, BlockAt S n M K s // nd b}] l.1.2 = r.1 →
      (Finset.univ.filter fun s => ls s = l).card =
        (S.L ^ S.d) ^ ((fun i : {b : Σ s, BlockAt S n M K s // nd b} => i.1.1) l.1.2 - 1) := by
    suffices hmain : ∀ (q : ℕ) (yq : BlockAt S n M K q)
        (l : {q : (Σ s, BlockAt S n M K s) × {b : Σ s, BlockAt S n M K s // nd b} //
          (⟨q.1.1 + 1, blockMap S.L (M * n K * S.L ^ (K - (q.1.1 + 1))) q.1.2⟩ :
            Σ s, BlockAt S n M K s) = q.2.1 ∧ ¬ nd q.1}),
        l.1.1 = ⟨q, yq⟩ →
        pa^[Fintype.card {b : Σ s, BlockAt S n M K s // nd b}] l.1.2 = r.1 →
        (Finset.univ.filter fun s => ls s = l).card = (S.L ^ S.d) ^ q by
      intro l hl
      have hl2 := leaf_parent nd l (rfl : l.1.1 = ⟨l.1.1.1, l.1.1.2⟩)
      have : (fun i : {b : Σ s, BlockAt S n M K s // nd b} => i.1.1) l.1.2 - 1 = l.1.1.1 := by
        show l.1.2.1.1 - 1 = _
        rw [hl2]; rfl
      rw [this]
      exact hmain _ _ l rfl hl
    intro q yq l hl1 hl
    have hl2 := leaf_parent nd l hl1
    have hnode : nd ⟨q + 1, blockMap S.L (M * n K * S.L ^ (K - (q + 1))) yq⟩ := by
      have := l.1.2.2
      rwa [hl2] at this
    obtain ⟨hk1q, hqm, -⟩ := (hnd q _).mp hnode
    have hnot : ¬ nd ⟨q, yq⟩ := by
      have := l.2.2
      rwa [hl1] at this
    have key : ∀ s : ↥(fib S.d S.L (M * n (m' + 1)) (m' + 1) (m' + 1) z),
        ls s = l ↔ jBlock S.d S.L (M * n K) K q (torusCast (fine_eq_top hnn hmK).symm s.1) = yq := by
      intro s
      constructor
      · intro h
        have := hls s
        rw [h, hl1] at this
        exact eq_of_sigma_jBlock _ yq this.symm
      · intro hb
        have hs := (hzy s.1).mp s.2
        obtain ⟨h1, h2⟩ := hsite s.1 hs
        have hs1 : s.1 ∈ (H.locGen Z M hmK hL hR).Ω 1 :=
          (H.locGen Z M hmK hL hR).Ω_antitone le_rfl hk1p (by omega)
            (mem_locGen_of_not_locFine hmK hL hR hk1p hk1 h1)
        have hiff := fun {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ m' + 1) =>
          Balaban.Background.mem_Ω_iff_le_layerIndex (H.locGen Z M hmK hL hR) hs1 hj1 hjk
        have hq1 : s.1 ∉ (H.locGen Z M hmK hL hR).Ω (q + 1) := by
          obtain ⟨-, -, c, hc, hg⟩ := (hnd q _).mp hnode
          have hsucc : jBlock S.d S.L (M * n K) K (q + 1) (torusCast (fine_eq_top hnn hmK).symm s.1) =
              blockMap S.L (M * n K * S.L ^ (K - (q + 1))) yq := by
            rw [jBlock_succ_eq_blockMap (d := S.d) (L := S.L) (N₀ := M * n K) (k := K) (by omega), hb]
          have hxy := blockCube_castSite hnn hmK (j := q + 1) (by omega) s.1
          rw [hsucc] at hxy
          exact ((gaussBlocks_iff_locGen (by omega) hmK (by omega) hL hR hc _ s.1 hxy.symm).mp hg).2
        have hq0 : s.1 ∈ (H.locGen Z M hmK hL hR).Ω q := by
          by_cases hqk : q = k1
          · subst hqk
            exact mem_locGen_of_not_locFine hmK hL hR hk1p hk1 h1
          · by_contra hsn
            obtain ⟨j, hj⟩ : ∃ j, q = j + 1 := ⟨q - 1, by omega⟩
            subst hj
            have := nd_block_of_not_mem hnn hmK hL hR nd hnd (j := j) (by omega) (by omega) hsn
            rw [hb] at this
            exact hnot this
        have hnS : (H.locGen Z M hmK hL hR).layerIndex s.1 = q := by
          have a1 := (hiff (by omega) (by omega : q ≤ m' + 1)).1 hq0
          have a2 : ¬ (q + 1 ≤ (H.locGen Z M hmK hL hR).layerIndex s.1) := fun h =>
            hq1 ((hiff (by omega) (by omega)).2 h)
          omega
        exact leaf_ext nd _ _ ((hls s).trans ((sigma_jBlock_eq _ hnS yq hb).trans hl1.symm))
    have hsub : ∀ s, jBlock S.d S.L (M * n K) K q (torusCast (fine_eq_top hnn hmK).symm s) = yq →
        s ∈ fib S.d S.L (M * n (m' + 1)) (m' + 1) (m' + 1) z := by
      intro s hb
      refine (hzy s).mpr (chain_top hmK nd pa hpa (torusCast (fine_eq_top hnn hmK).symm s) l.1.2 (q + 1)
        ?_ y ?_)
      · rw [hl2, jBlock_succ_eq_blockMap (d := S.d) (L := S.L) (N₀ := M * n K) (k := K) (by omega), hb]
      · rw [hl, hry]
    rw [Finset.filter_congr (fun s _ => key s)]
    exact card_leaf_sites hnn hmK (by omega) yq _ hsub
  obtain ⟨lf, hc, hs, hlf⟩ := forest_leaf_map (m := S.L ^ S.d) (fun i : {b : Σ s, BlockAt S n M K s // nd b} => i.1.1) pa
    (fun l => l.1.2) r B e el hsc hleaf ls hroot (fun l hl => by convert hcardL l hl)
  refine ⟨lf, hc, fun s => ?_, fun s => ?_⟩
  swap
  · rw [hlf s]; exact hls s
  rw [hs s]
  have hpar := leaf_parent nd (ls s) (hls s)
  show _ = (ls s).1.2.1.1 - 1
  rw [hpar]
  rfl

end RootMap

end Balaban.LargeField
