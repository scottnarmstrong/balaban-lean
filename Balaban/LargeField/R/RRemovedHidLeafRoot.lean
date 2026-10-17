/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RRemovedHidLeafChain
public import Balaban.LargeField.R.ChiBridgeHist

/-!
# The leaf map of a root of the window's forest (W942)

`notes/phase1/LF4R-PLAN.md` §8.5.  Leaves of the forest of the Gaussian nodes are determined by their block
(`leaf_ext`); a site of the Gaussian region of the window determines its leaf (block of scale
`n = layerIndex`, parent the node of scale `n + 1`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale RegionHistory

section Root

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {H : RegionHistory S n R k0 K} {m' : ℕ}

theorem leaf_ext (nd : (Σ s, BlockAt S n M K s) → Prop)
    (l l' : {q : (Σ s, BlockAt S n M K s) × {b : Σ s, BlockAt S n M K s // nd b} //
      (⟨q.1.1 + 1, blockMap S.L (M * n K * S.L ^ (K - (q.1.1 + 1))) q.1.2⟩ :
        Σ s, BlockAt S n M K s) = q.2.1 ∧ ¬ nd q.1}) (h : l.1.1 = l'.1.1) : l = l' := by
  obtain ⟨⟨q1, b1⟩, h1, h2⟩ := l
  obtain ⟨⟨q1', b1'⟩, h1', h2'⟩ := l'
  simp only at h h1 h1'
  subst h
  have : b1 = b1' := Subtype.ext (h1.symm.trans h1')
  subst this
  rfl

theorem exists_leaf (nd : (Σ s, BlockAt S n M K s) → Prop) {q : ℕ} (yq : BlockAt S n M K q)
    (hnode : nd ⟨q + 1, blockMap S.L (M * n K * S.L ^ (K - (q + 1))) yq⟩) (hnot : ¬ nd ⟨q, yq⟩) :
    ∃ l : {q : (Σ s, BlockAt S n M K s) × {b : Σ s, BlockAt S n M K s // nd b} //
      (⟨q.1.1 + 1, blockMap S.L (M * n K * S.L ^ (K - (q.1.1 + 1))) q.1.2⟩ :
        Σ s, BlockAt S n M K s) = q.2.1 ∧ ¬ nd q.1}, l.1.1 = ⟨q, yq⟩ :=
  ⟨⟨(⟨q, yq⟩, ⟨_, hnode⟩), rfl, hnot⟩, rfl⟩

theorem sigma_jBlock_eq (x : Torus S.d (M * n K * S.L ^ K)) {a q : ℕ} (h : a = q)
    (yq : BlockAt S n M K q) (hy : jBlock S.d S.L (M * n K) K q x = yq) :
    (⟨a, jBlock S.d S.L (M * n K) K a x⟩ : Σ s, BlockAt S n M K s) = ⟨q, yq⟩ := by
  subst h; rw [hy]

theorem site_range (hmK : m' + 1 ≤ K) (hL : 2 ≤ S.L) (hR : ∀ j, 1 ≤ j → j < m' + 1 → S.Rb ≤ R j)
    {Z : H.Comp (m' + 1)} {k1 : ℕ} (hk1p : 1 ≤ k1) (hk1 : k1 ≤ m')
    {x : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1))} (hx1 : x ∉ H.locFine Z M k1)
    (hxk : x ∉ (H.locGen Z M hmK hL hR).Ω (m' + 1)) :
    k1 ≤ (H.locGen Z M hmK hL hR).layerIndex x ∧ (H.locGen Z M hmK hL hR).layerIndex x ≤ m' ∧
      x ∈ (H.locGen Z M hmK hL hR).Ω ((H.locGen Z M hmK hL hR).layerIndex x) ∧
      ∀ j, (H.locGen Z M hmK hL hR).layerIndex x < j → j ≤ m' + 1 →
        x ∉ (H.locGen Z M hmK hL hR).Ω j := by
  have hk := mem_locGen_of_not_locFine hmK hL hR hk1p hk1 hx1
  have h1 : x ∈ (H.locGen Z M hmK hL hR).Ω 1 :=
    (H.locGen Z M hmK hL hR).Ω_antitone le_rfl hk1p (by omega) hk
  obtain ⟨hn1, hnk, -⟩ := (H.locGen Z M hmK hL hR).layerIndex_spec h1
  have hiff := fun {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ m' + 1) =>
    Balaban.Background.mem_Ω_iff_le_layerIndex (H.locGen Z M hmK hL hR) h1 hj1 hjk
  have hlt : (H.locGen Z M hmK hL hR).layerIndex x < m' + 1 := by
    by_contra hge
    exact hxk ((hiff (by omega) le_rfl).2 (by omega))
  refine ⟨(hiff hk1p (by omega)).1 hk, by omega, (hiff hn1 hnk).2 le_rfl, fun j hj hjk hmem => ?_⟩
  have := (hiff (by omega) hjk).1 hmem
  omega

theorem chain_root (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) (hmK : m' + 1 ≤ K) (hL : 2 ≤ S.L)
    (hR : ∀ j, 1 ≤ j → j < m' + 1 → S.Rb ≤ R j) {Z : H.Comp (m' + 1)} {k1 : ℕ} (hk1p : 1 ≤ k1)
    (hk1 : k1 ≤ m') (nd : (Σ s, BlockAt S n M K s) → Prop)
    (hnd : ∀ j (y : BlockAt S n M K (j + 1)), nd ⟨j + 1, y⟩ ↔ (k1 ≤ j ∧ j ≤ m' ∧
      ∃ c ∈ H.ancFin (j + 1) (m' + 1) Z, y ∈ gaussBlocks (H.localHistory M K (j + 1) c) j))
    (hnd0 : ∀ y : BlockAt S n M K 0, ¬ nd ⟨0, y⟩)
    [Fintype {b : Σ s, BlockAt S n M K s // nd b}]
    (pa : {b : Σ s, BlockAt S n M K s // nd b} → {b : Σ s, BlockAt S n M K s // nd b})
    (hpa : ∀ b : {b : Σ s, BlockAt S n M K s // nd b},
      (nd ⟨b.1.1 + 1, blockMap S.L (M * n K * S.L ^ (K - (b.1.1 + 1))) b.1.2⟩ ∧ b.1.1 + 1 ≤ m' + 1 →
        (pa b).1 = ⟨b.1.1 + 1, blockMap S.L (M * n K * S.L ^ (K - (b.1.1 + 1))) b.1.2⟩) ∧
      (¬ (nd ⟨b.1.1 + 1, blockMap S.L (M * n K * S.L ^ (K - (b.1.1 + 1))) b.1.2⟩ ∧
        b.1.1 + 1 ≤ m' + 1) → pa b = b))
    {x : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1))} (hx1 : x ∉ H.locFine Z M k1)
    (hxk : x ∉ (H.locGen Z M hmK hL hR).Ω (m' + 1))
    (b0 : {b : Σ s, BlockAt S n M K s // nd b})
    (hb0 : b0.1 = ⟨(H.locGen Z M hmK hL hR).layerIndex x + 1,
      jBlock S.d S.L (M * n K) K ((H.locGen Z M hmK hL hR).layerIndex x + 1)
        (torusCast (fine_eq_top hnn hmK).symm x)⟩) :
    (pa^[Fintype.card {b : Σ s, BlockAt S n M K s // nd b}] b0).1 =
      ⟨m' + 1, jBlock S.d S.L (M * n K) K (m' + 1) (torusCast (fine_eq_top hnn hmK).symm x)⟩ := by
  classical
  have g1 : ∀ i, pa i ≠ i → (fun i : {b : Σ s, BlockAt S n M K s // nd b} => i.1.1) (pa i) =
      (fun i : {b : Σ s, BlockAt S n M K s // nd b} => i.1.1) i + 1 := by
    intro i hne
    by_cases hp : nd ⟨i.1.1 + 1, blockMap S.L (M * n K * S.L ^ (K - (i.1.1 + 1))) i.1.2⟩ ∧
        i.1.1 + 1 ≤ m' + 1
    · have := (hpa i).1 hp
      show (pa i).1.1 = i.1.1 + 1
      rw [this]
    · exact absurd ((hpa i).2 hp) hne
  obtain ⟨hr1, hr2, hr3, hr4⟩ := site_range hmK hL hR hk1p hk1 hx1 hxk
  obtain ⟨i, hi, hb⟩ := chain_inv hmK nd pa hpa (torusCast (fine_eq_top hnn hmK).symm x) b0
    ((H.locGen Z M hmK hL hR).layerIndex x + 1) hb0 (Fintype.card {b : Σ s, BlockAt S n M K s // nd b})
  have hfix := pa_iter_card_fixed (fun i : {b : Σ s, BlockAt S n M K s // nd b} => i.1.1) pa g1 b0
  set b' := pa^[Fintype.card {b : Σ s, BlockAt S n M K s // nd b}] b0 with hb'
  have hnb : nd ⟨i, jBlock S.d S.L (M * n K) K i (torusCast (fine_eq_top hnn hmK).symm x)⟩ := by
    rw [← hb]; exact b'.2
  have hile : i ≤ m' + 1 := by
    rcases i with _ | j
    · exact absurd hnb (hnd0 _)
    · exact Nat.succ_le_succ ((hnd j _).mp hnb).2.1
  have hieq : i = m' + 1 := by
    by_contra hne
    have him : i ≤ m' := by omega
    have hk1i : k1 ≤ i := by omega
    have hndi := nd_block_of_not_mem hnn hmK hL hR nd hnd hk1i him (hr4 (i + 1) (by omega) (by omega))
    have hiK : i + 1 ≤ K := by omega
    rw [jBlock_succ_eq_blockMap (d := S.d) (L := S.L) (N₀ := M * n K) (k := K) hiK] at hndi
    have hp1 := (hpa b').1 (by
      rw [hb]
      exact ⟨hndi, (by show i + 1 ≤ m' + 1; omega)⟩)
    rw [hfix, hb] at hp1
    have := congrArg Sigma.fst hp1
    simp only at this
    omega
  subst hieq
  exact hb

theorem chain_top (hmK : m' + 1 ≤ K) (nd : (Σ s, BlockAt S n M K s) → Prop)
    [Fintype {b : Σ s, BlockAt S n M K s // nd b}]
    (pa : {b : Σ s, BlockAt S n M K s // nd b} → {b : Σ s, BlockAt S n M K s // nd b})
    (hpa : ∀ b : {b : Σ s, BlockAt S n M K s // nd b},
      (nd ⟨b.1.1 + 1, blockMap S.L (M * n K * S.L ^ (K - (b.1.1 + 1))) b.1.2⟩ ∧ b.1.1 + 1 ≤ m' + 1 →
        (pa b).1 = ⟨b.1.1 + 1, blockMap S.L (M * n K * S.L ^ (K - (b.1.1 + 1))) b.1.2⟩) ∧
      (¬ (nd ⟨b.1.1 + 1, blockMap S.L (M * n K * S.L ^ (K - (b.1.1 + 1))) b.1.2⟩ ∧
        b.1.1 + 1 ≤ m' + 1) → pa b = b))
    (xK : Torus S.d (M * n K * S.L ^ K)) (b0 : {b : Σ s, BlockAt S n M K s // nd b}) (i0 : ℕ)
    (h0 : b0.1 = ⟨i0, jBlock S.d S.L (M * n K) K i0 xK⟩) (y : BlockAt S n M K (m' + 1))
    (hy : (pa^[Fintype.card {b : Σ s, BlockAt S n M K s // nd b}] b0).1 = ⟨m' + 1, y⟩) :
    jBlock S.d S.L (M * n K) K (m' + 1) xK = y := by
  obtain ⟨i, -, hb⟩ := chain_inv hmK nd pa hpa xK b0 i0 h0
    (Fintype.card {b : Σ s, BlockAt S n M K s // nd b})
  rw [hb] at hy
  obtain ⟨h1, h2⟩ := Sigma.mk.inj_iff.mp hy
  subst h1
  exact eq_of_heq h2

end Root

end Balaban.LargeField
