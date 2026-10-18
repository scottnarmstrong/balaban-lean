/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Background.TwoTorusPsiTilde
public import Balaban.LargeField.Background.TwoTorusRegSites

/-!
# Blocks of the sites of a set, and their adjacency, on two tori

If the sites of sets `T_j` of two tori (`j`-blocks over `T_j`) have the margin `L^j + 1` in the box
and correspond (`PtCorr`), then the sets of blocks over them correspond (`BlkCorr`) and so does the
adjacency of blocks (`blockAdj_ptCorr`, `blocksOver_corr`).
-/

@[expose] public section

namespace Balaban.RootFSpine

open Balaban Balaban.LargeField

section Blocks

variable {S : Setting} {n₁ n₂ : ℕ → ℕ} [∀ k, NeZero (n₁ k)] [∀ k, NeZero (n₂ k)] {M K N : ℕ}
  [NeZero M] [NeZero S.L] {cc : Fin S.d → ℤ}

omit [∀ k, NeZero (n₁ k)] [∀ k, NeZero (n₂ k)] [NeZero M] [NeZero S.L] in
theorem blkCorr_symm {j₁ j₂ : ℕ} {y₁ : BlockAt S n₁ M K j₁} {y₂ : BlockAt S n₂ M K j₂}
    (h : BlkCorr cc j₁ j₂ y₁ y₂) : BlkCorr cc j₂ j₁ y₂ y₁ := by
  obtain ⟨hj, x₁, x₂, h1, h2, hp⟩ := h
  exact ⟨hj.symm, x₂, x₁, h2, h1, ptCorr_symm hp⟩

omit [∀ k, NeZero (n₁ k)] [∀ k, NeZero (n₂ k)] [NeZero M] [NeZero S.L] in
theorem blkCorr_jBlock {j : ℕ} {x₁ : Torus S.d (M * n₁ K * S.L ^ K)}
    {x₂ : Torus S.d (M * n₂ K * S.L ^ K)} (hp : PtCorr cc x₁ x₂) :
    BlkCorr cc j j (Multiscale.jBlock S.d S.L (M * n₁ K) K j x₁)
      (Multiscale.jBlock S.d S.L (M * n₂ K) K j x₂) :=
  ⟨rfl, x₁, x₂, rfl, rfl, hp⟩

/-- A site in the block of a site with margin `L^j + 1` has margin `1`, and the same block index
vector. -/
theorem block_site_margin {j : ℕ} (hj : j ≤ K) (hq : 4 ≤ M * n₁ K * S.L ^ (K - j)) {ℓ' : ℕ}
    {x s : Torus S.d (M * n₁ K * S.L ^ K)}
    (hx : InBoxK (S.L ^ j + 1) (M * n₁ K * S.L ^ K) ℓ' cc (liftNear cc x))
    (hs : Multiscale.jBlock S.d S.L (M * n₁ K) K j s = Multiscale.jBlock S.d S.L (M * n₁ K) K j x) :
    InBoxK 1 (M * n₁ K * S.L ^ K) ℓ' cc (liftNear cc s) ∧
      bidx (S.L ^ j) (liftNear cc s) = bidx (S.L ^ j) (liftNear cc x) := by
  have hP : 0 < S.L ^ j := pow_pos (Nat.pos_of_ne_zero (NeZero.ne _)) j
  have hx' : x = zcast (M * n₁ K * S.L ^ K) (liftNear cc x) := (zcast_liftNear x).symm
  have hs' : s = zcast (M * n₁ K * S.L ^ K) (liftNear cc s) := (zcast_liftNear s).symm
  rw [hx', hs', jBlock_zcast hj, jBlock_zcast hj] at hs
  have hb : bidx (S.L ^ j) (liftNear cc s) = bidx (S.L ^ j) (liftNear cc x) :=
    (bidx_eq_of_zcast hP (Multiscale.side_eq hj) hq
      (fun μ => by have := (hx μ).1; omega) (fun μ => liftNear_abs_le cc s μ) hs.symm).symm
  refine ⟨fun μ => ?_, hb⟩
  have h1 := abs_ediv_eq_le (P := S.L ^ j) hP (a := liftNear cc s μ) (b := liftNear cc x μ)
    (congrFun hb μ)
  have h2 := hx μ
  have h3 : |liftNear cc s μ - cc μ| ≤ |liftNear cc s μ - liftNear cc x μ| + |liftNear cc x μ - cc μ| := by
    have := abs_sub_le (liftNear cc s μ) (liftNear cc x μ) (cc μ); exact this
  push_cast at h1 h2 ⊢
  constructor <;> nlinarith [h2.1, h2.2]

/-- **Adjacency of the blocks of corresponding sites with margin.** -/
theorem blockAdj_ptCorr {j j' : ℕ} (hj : j ≤ K) (hj' : j' ≤ K)
    (hq : 4 ≤ M * n₁ K * S.L ^ (K - j)) (hq' : 4 ≤ M * n₁ K * S.L ^ (K - j'))
    {x₁ x₁' : Torus S.d (M * n₁ K * S.L ^ K)} {x₂ x₂' : Torus S.d (M * n₂ K * S.L ^ K)}
    (hp : PtCorr cc x₁ x₂) (hp' : PtCorr cc x₁' x₂')
    (hm : InBoxK (S.L ^ j + 1) (M * n₁ K * S.L ^ K) (M * n₂ K * S.L ^ K) cc (liftNear cc x₁))
    (hm' : InBoxK (S.L ^ j' + 1) (M * n₁ K * S.L ^ K) (M * n₂ K * S.L ^ K) cc (liftNear cc x₁'))
    (h : BlockAdj (⟨j, Multiscale.jBlock S.d S.L (M * n₁ K) K j x₁⟩ : BlockPt S n₁ M K)
      ⟨j', Multiscale.jBlock S.d S.L (M * n₁ K) K j' x₁'⟩) :
    BlockAdj (⟨j, Multiscale.jBlock S.d S.L (M * n₂ K) K j x₂⟩ : BlockPt S n₂ M K)
      ⟨j', Multiscale.jBlock S.d S.L (M * n₂ K) K j' x₂'⟩ := by
  obtain ⟨s, s', hs, hs', hadj⟩ := h
  obtain ⟨hms, hb⟩ := block_site_margin hj hq hm hs
  obtain ⟨hms', hb'⟩ := block_site_margin hj' hq' hm' hs'
  have hps := ptCorr_transp (m₂ := M * n₂ K * S.L ^ K) hms.inBox
  have hps' := ptCorr_transp (m₂ := M * n₂ K * S.L ^ K) hms'.inBox
  have ex₂ := ptCorr_eq_transp hp
  have ex₂' := ptCorr_eq_transp hp'
  refine ⟨transp (M * n₂ K * S.L ^ K) cc s, transp (M * n₂ K * S.L ^ K) cc s', ?_, ?_,
    (adj_ptCorr hps hps' hms).1 hadj⟩
  · simp only [transp, ex₂]
    rw [jBlock_zcast hj, jBlock_zcast hj]
    unfold bidx at hb
    rw [hb]
  · simp only [transp, ex₂']
    rw [jBlock_zcast hj', jBlock_zcast hj']
    unfold bidx at hb'
    rw [hb']

/-- The blocks over the sites of the sets `T j`: `⟨j, jBlock j x⟩`, `x ∈ T j`. -/
def blocksOver (T : ℕ → Set (Torus S.d (M * n₁ K * S.L ^ K))) : Set (BlockPt S n₁ M K) :=
  {b | ∃ x ∈ T b.1, Multiscale.jBlock S.d S.L (M * n₁ K) K b.1 x = b.2}

omit [∀ k, NeZero (n₁ k)] [NeZero M] [NeZero S.L] in
theorem mem_blocksOver {T : ℕ → Set (Torus S.d (M * n₁ K * S.L ^ K))} {j : ℕ}
    {x : Torus S.d (M * n₁ K * S.L ^ K)} (hx : x ∈ T j) :
    (⟨j, Multiscale.jBlock S.d S.L (M * n₁ K) K j x⟩ : BlockPt S n₁ M K) ∈ blocksOver T :=
  ⟨x, hx, rfl⟩

theorem jBlock_unique_right {j : ℕ} (hj : j ≤ K) (hq : 4 ≤ M * n₁ K * S.L ^ (K - j))
    {x₁ : Torus S.d (M * n₁ K * S.L ^ K)} {x₂ x₂' : Torus S.d (M * n₂ K * S.L ^ K)}
    (hp : PtCorr cc x₁ x₂)
    (hc : BlkCorr cc j j (Multiscale.jBlock S.d S.L (M * n₁ K) K j x₁)
      (Multiscale.jBlock S.d S.L (M * n₂ K) K j x₂')) :
    Multiscale.jBlock S.d S.L (M * n₂ K) K j x₂ = Multiscale.jBlock S.d S.L (M * n₂ K) K j x₂' :=
  CCorr.right_unique (pow_pos (Nat.pos_of_ne_zero (NeZero.ne _)) j) (Multiscale.side_eq hj) hq
    ((blkCorr_iff_ccorr hj).1 (blkCorr_jBlock hp)) ((blkCorr_iff_ccorr hj).1 hc)

theorem jBlock_unique_left {j : ℕ} (hj : j ≤ K) (hq : 4 ≤ M * n₂ K * S.L ^ (K - j))
    {x₁ x₁' : Torus S.d (M * n₁ K * S.L ^ K)} {x₂ : Torus S.d (M * n₂ K * S.L ^ K)}
    (hp : PtCorr cc x₁ x₂)
    (hc : BlkCorr cc j j (Multiscale.jBlock S.d S.L (M * n₁ K) K j x₁')
      (Multiscale.jBlock S.d S.L (M * n₂ K) K j x₂)) :
    Multiscale.jBlock S.d S.L (M * n₁ K) K j x₁ = Multiscale.jBlock S.d S.L (M * n₁ K) K j x₁' :=
  CCorr.left_unique (pow_pos (Nat.pos_of_ne_zero (NeZero.ne _)) j) (Multiscale.side_eq hj) hq
    ((blkCorr_iff_ccorr hj).1 (blkCorr_jBlock hp)) ((blkCorr_iff_ccorr hj).1 hc)

/-- **The blocks over corresponding sets of sites correspond, and so does their adjacency.** -/
theorem blocksOver_corr {J : ℕ} (hJ : J ≤ K) {T₁ : ℕ → Set (Torus S.d (M * n₁ K * S.L ^ K))}
    {T₂ : ℕ → Set (Torus S.d (M * n₂ K * S.L ^ K))}
    (hT₁ : ∀ j x, x ∈ T₁ j → j ≤ J ∧
      InBoxK (S.L ^ j + 1) (M * n₁ K * S.L ^ K) (M * n₂ K * S.L ^ K) cc (liftNear cc x))
    (hT₂ : ∀ j x, x ∈ T₂ j → j ≤ J ∧
      InBoxK (S.L ^ j + 1) (M * n₁ K * S.L ^ K) (M * n₂ K * S.L ^ K) cc (liftNear cc x))
    (hiff : ∀ j x₁ x₂, PtCorr cc x₁ x₂ → (x₁ ∈ T₁ j ↔ x₂ ∈ T₂ j))
    (hq₁ : ∀ j, j ≤ J → 4 ≤ M * n₁ K * S.L ^ (K - j))
    (hq₂ : ∀ j, j ≤ J → 4 ≤ M * n₂ K * S.L ^ (K - j)) :
    (∀ b ∈ blocksOver T₁, ∃ b' ∈ blocksOver T₂, BlkCorr cc b.1 b'.1 b.2 b'.2) ∧
    (∀ b' ∈ blocksOver T₂, ∃ b ∈ blocksOver T₁, BlkCorr cc b.1 b'.1 b.2 b'.2) ∧
    (∀ b₁ ∈ blocksOver T₁, ∀ b₁' ∈ blocksOver T₁, ∀ b₂ ∈ blocksOver T₂, ∀ b₂' ∈ blocksOver T₂,
      BlkCorr cc b₁.1 b₂.1 b₁.2 b₂.2 → BlkCorr cc b₁'.1 b₂'.1 b₁'.2 b₂'.2 →
        (BlockAdj b₁ b₁' ↔ BlockAdj b₂ b₂')) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨j, y⟩ ⟨x₁, hx₁, hb⟩
    dsimp only at hx₁ hb
    subst hb
    obtain ⟨hjJ, hm⟩ := hT₁ _ _ hx₁
    have hp := ptCorr_transp (m₂ := M * n₂ K * S.L ^ K) hm.inBox
    exact ⟨⟨j, Multiscale.jBlock S.d S.L (M * n₂ K) K j (transp (M * n₂ K * S.L ^ K) cc x₁)⟩,
      mem_blocksOver ((hiff j _ _ hp).1 hx₁), blkCorr_jBlock hp⟩
  · rintro ⟨j, y⟩ ⟨x₂, hx₂, hb⟩
    dsimp only at hx₂ hb
    subst hb
    obtain ⟨hjJ, hm⟩ := hT₂ _ _ hx₂
    have hp := ptCorr_transp (m₁ := M * n₂ K * S.L ^ K) (m₂ := M * n₁ K * S.L ^ K) hm.symm.inBox
    exact ⟨⟨j, Multiscale.jBlock S.d S.L (M * n₁ K) K j (transp (M * n₁ K * S.L ^ K) cc x₂)⟩,
      mem_blocksOver ((hiff j _ _ (ptCorr_symm hp)).2 hx₂), blkCorr_jBlock (ptCorr_symm hp)⟩
  · rintro ⟨j, y₁⟩ ⟨x₁, hx₁, hb₁⟩ ⟨j', y₁'⟩ ⟨x₁', hx₁', hb₁'⟩ ⟨j₂, y₂⟩ ⟨x₂, hx₂, hb₂⟩
      ⟨j₂', y₂'⟩ ⟨x₂', hx₂', hb₂'⟩ hc hc'
    dsimp only at hx₁ hb₁ hx₁' hb₁' hx₂ hb₂ hx₂' hb₂' hc hc'
    subst hb₁ hb₁' hb₂ hb₂'
    obtain rfl : j = j₂ := hc.1
    obtain rfl : j' = j₂' := hc'.1
    obtain ⟨hjJ, hm⟩ := hT₁ _ _ hx₁
    obtain ⟨hjJ', hm'⟩ := hT₁ _ _ hx₁'
    obtain ⟨hjJ₂, hm₂⟩ := hT₂ _ _ hx₂
    obtain ⟨hjJ₂', hm₂'⟩ := hT₂ _ _ hx₂'
    have hp := ptCorr_transp (m₂ := M * n₂ K * S.L ^ K) hm.inBox
    have hp' := ptCorr_transp (m₂ := M * n₂ K * S.L ^ K) hm'.inBox
    have hq := ptCorr_transp (m₁ := M * n₂ K * S.L ^ K) (m₂ := M * n₁ K * S.L ^ K) hm₂.symm.inBox
    have hq' := ptCorr_transp (m₁ := M * n₂ K * S.L ^ K) (m₂ := M * n₁ K * S.L ^ K) hm₂'.symm.inBox
    constructor
    · intro h
      have e := jBlock_unique_right (le_trans hjJ hJ) (hq₁ _ hjJ) hp hc
      have e' := jBlock_unique_right (le_trans hjJ' hJ) (hq₁ _ hjJ') hp' hc'
      have := blockAdj_ptCorr (le_trans hjJ hJ) (le_trans hjJ' hJ) (hq₁ _ hjJ) (hq₁ _ hjJ') hp hp'
        hm hm' h
      simp only [← e, ← e'] at *
      exact this
    · intro h
      have e := jBlock_unique_left (le_trans hjJ hJ) (hq₂ _ hjJ₂) (ptCorr_symm hq) hc
      have e' := jBlock_unique_left (le_trans hjJ' hJ) (hq₂ _ hjJ₂') (ptCorr_symm hq') hc'
      have := blockAdj_ptCorr (cc := cc) (n₁ := n₂) (n₂ := n₁) (le_trans hjJ hJ)
        (le_trans hjJ' hJ) (hq₂ _ hjJ₂) (hq₂ _ hjJ₂') hq hq' hm₂.symm hm₂'.symm h
      simp only [← e, ← e'] at *
      exact this

end Blocks

end Balaban.RootFSpine
