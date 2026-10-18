/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Background.TwoTorusChi
public import Balaban.LargeField.Background.TwoTorusRoom
public import Balaban.LargeField.Background.TwoTorusQuietSets

/-!
# Products of the characteristic functions of cubes on two tori

`cubeProd_chiK_corr` and `cubeProd_chiPrimeNew_corr`: the products over corresponding sets of cubes
of the characteristic functions `χ_q(□)` (`chiK`) and `χ'_{k+1}(□')` (`chiPrimeNew`) of the quiet
kernel agree on two tori, when the block fields agree at corresponding blocks.
-/

@[expose] public section

namespace Balaban.RootFSpine

open Balaban Balaban.Multiscale Balaban.Background Balaban.LargeField RegionHistory

section Bridge

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K N : ℕ} [NeZero M]
  [NeZero S.L]

omit [NeZero M] in
/-- The block field of the level-`q` torus at the `i`-block of the lift of a site. -/
theorem blockCfgOf_zcast_block (g : Geo S n R M) (hnn : ∀ i, i < K → n i = S.L * n (i + 1))
    {q i : ℕ} (hiq : i ≤ q) (hqK : q ≤ K)
    (f : BlockAt S n M K i → EuclideanSpace ℝ (Fin N)) (w : Fin S.d → ℤ) (j : Fin N) :
    blockCfgOf g hnn hiq hqK f
      (jBlock S.d S.L (g.M1 * (g.c * n q)) q i (zcast (g.M1 * (g.c * n q) * S.L ^ q) w)) j =
      f (zcast (M * n K * S.L ^ (K - i)) (bidx (S.L ^ i) w)) j := by
  unfold blockCfgOf
  rw [jBlock_zcast hiq w, torusCast_zcast]
  rfl

end Bridge

section ProdK

variable {S : Setting} {n₁ n₂ : ℕ → ℕ} [∀ k, NeZero (n₁ k)] [∀ k, NeZero (n₂ k)] {R : ℕ → ℝ}
  {M K N : ℕ} [NeZero M] [NeZero S.L]

open Classical in
/-- **The product of `χ_q(□)` over corresponding sets of cubes agrees on two tori.** -/
theorem cubeProd_chiK_corr (g₁ : Geo S n₁ R M) (g₂ : Geo S n₂ R M) (h1 : g₂.M1 = g₁.M1)
    (h2 : g₂.c = g₁.c) (hL : 2 ≤ S.L) (hnn₁ : ∀ i, i < K → n₁ i = S.L * n₁ (i + 1))
    (hnn₂ : ∀ i, i < K → n₂ i = S.L * n₂ (i + 1)) {q : ℕ} (hqK : q ≤ K) (h12₁ : 12 ≤ n₁ q)
    (h12₂ : 12 ≤ n₂ q) {cc : Fin S.d → ℤ} (a : ℕ → ℝ) (μ δ : ℝ) (hv : EuclideanSpace ℝ (Fin N))
    {B₁ : Set (Torus S.d (n₁ q))} {B₂ : Set (Torus S.d (n₂ q))}
    (hB : CSetCorr cc (M * n₁ K * S.L ^ K) (M * n₂ K * S.L ^ K) (S.L ^ q * M) (n₁ q) (n₂ q) B₁ B₂)
    (hmargin : ∀ w₀, InBox (M * n₁ K * S.L ^ K) (M * n₂ K * S.L ^ K) cc w₀ →
      zcast (n₁ q) (bidx (S.L ^ q * M) w₀) ∈ B₁ →
        InBoxK (5 * (S.L ^ q * M) + 2) (M * n₁ K * S.L ^ K) (M * n₂ K * S.L ^ K) cc w₀)
    (f₁ : BlockAt S n₁ M K q → EuclideanSpace ℝ (Fin N))
    (f₂ : BlockAt S n₂ M K q → EuclideanSpace ℝ (Fin N))
    (hf : ∀ y₁ y₂, BlkCorr cc q q y₁ y₂ → f₁ y₁ = f₂ y₂) :
    ∏ y ∈ (Finset.univ.filter fun y => y ∈ B₁),
        chiK (M1 := g₁.M1) (N₁ := g₁.c * n₁ q) (L := S.L) (q := q) (N := N) a μ δ (fun i => hv i)
          g₁.c (n₁ q) y (blockCfgOf g₁ hnn₁ (le_refl q) hqK f₁) =
      ∏ y ∈ (Finset.univ.filter fun y => y ∈ B₂),
        chiK (M1 := g₂.M1) (N₁ := g₂.c * n₂ q) (L := S.L) (q := q) (N := N) a μ δ (fun i => hv i)
          g₂.c (n₂ q) y (blockCfgOf g₂ hnn₂ (le_refl q) hqK f₂) := by
  obtain ⟨M1, c, neM1, nec, hM, hc, hRlow, hRmono⟩ := g₁
  obtain ⟨M1', c', neM1', nec', hM', hc', hRlow', hRmono'⟩ := g₂
  simp only at h1 h2 ⊢
  have h1' := h1.symm
  have h2' := h2.symm
  subst h1' h2'
  subst hM
  have hP := pos_cubeSide (S := S) (M := c * M1) q
  refine prod_cset hP (Balaban.LargeField.fine_eq hnn₁ hqK) (Balaban.LargeField.fine_eq hnn₂ hqK)
    (by omega) (by omega) hB _ _ ?_
  intro y₁ y₂ hy₁ hy₂ hcc
  obtain ⟨w₀, hw, rfl, rfl⟩ := hcc
  have e₁ := site_eq (c := c) (M1 := M1) (L := S.L) (q := q) (n := n₁) rfl hnn₁ hqK
  have e₂ := site_eq (c := c) (M1 := M1) (L := S.L) (q := q) (n := n₂) rfl hnn₂ hqK
  have hw' : InBox (M1 * (c * n₁ q) * S.L ^ q) (M1 * (c * n₂ q) * S.L ^ q) cc w₀ :=
    (inBox_cast e₁ e₂).2 hw
  have hm := hmargin w₀ hw hy₁
  refine chiK_corr hc hL h12₁ h12₂ ((inBoxK_cast e₁ e₂).2 hm) a μ δ (fun i => hv i) _ _ ?_
  intro w hwb i
  rw [blockCfgOf_zcast_block, blockCfgOf_zcast_block]
  have := hf (zcast (c * M1 * n₁ K * S.L ^ (K - q)) (bidx (S.L ^ q) w))
    (zcast (c * M1 * n₂ K * S.L ^ (K - q)) (bidx (S.L ^ q) w))
    ((blkCorr_iff_ccorr hqK).2 ⟨w, (inBox_cast e₁ e₂).1 hwb, rfl, rfl⟩)
  rw [this]

end ProdK

section Omega

variable {S : Setting} {n₁ n₂ : ℕ → ℕ} [∀ k, NeZero (n₁ k)] [∀ k, NeZero (n₂ k)] {M K : ℕ}
  [NeZero M] [NeZero S.L] {cc : Fin S.d → ℤ} {a₁ : LocalHistory S n₁ M K}
  {a₂ : LocalHistory S n₂ M K} {k : ℕ}

/-- **The fine sets of the cubes of `Ω_{k+1}` of two tori correspond.** -/
theorem setIff_omegaLevel {c M1 : ℕ} [NeZero c] [NeZero M1] (hM : M = c * M1)
    (hnn₁ : ∀ i, i < K → n₁ i = S.L * n₁ (i + 1)) (hnn₂ : ∀ i, i < K → n₂ i = S.L * n₂ (i + 1))
    (hk : k + 1 ≤ K) (hH : HistCorr cc a₁ a₂) (hq₁ : 4 ≤ n₁ (k + 1)) (hq₂ : 4 ≤ n₂ (k + 1)) :
    SetIff cc
      ((omegaLevel (S := S) (n := n₁) M1 c (k + 1)
        {z | CubeSub (S := S) (n := n₁) M K (k + 1) z (a₁.Omega k)} :
          Finset (Torus S.d (M1 * (c * n₁ (k + 1)) * S.L ^ (k + 1)))) :
        Set (Torus S.d (M1 * (c * n₁ (k + 1)) * S.L ^ (k + 1))))
      ((omegaLevel (S := S) (n := n₂) M1 c (k + 1)
        {z | CubeSub (S := S) (n := n₂) M K (k + 1) z (a₂.Omega k)} :
          Finset (Torus S.d (M1 * (c * n₂ (k + 1)) * S.L ^ (k + 1)))) :
        Set (Torus S.d (M1 * (c * n₂ (k + 1)) * S.L ^ (k + 1)))) := by
  subst hM
  have e₁ := site_eq (c := c) (M1 := M1) (L := S.L) (q := k + 1) (n := n₁) rfl hnn₁ hk
  have e₂ := site_eq (c := c) (M1 := M1) (L := S.L) (q := k + 1) (n := n₂) rfl hnn₂ hk
  have hmem : ∀ {n : ℕ → ℕ} [∀ k, NeZero (n k)] {a : LocalHistory S n (c * M1) K}
      (x : Torus S.d (M1 * (c * n (k + 1)) * S.L ^ (k + 1))),
      x ∈ omegaLevel (S := S) (n := n) M1 c (k + 1)
        {z | CubeSub (S := S) (n := n) (c * M1) K (k + 1) z (a.Omega k)} ↔
        CubeSub (S := S) (n := n) (c * M1) K (k + 1)
          (blockMap (S.L ^ (k + 1) * (c * M1)) (n (k + 1)) x) (a.Omega k) := by
    intro n _ a x
    unfold omegaLevel
    rw [mem_cubePre]
    rfl
  intro x₁ x₂ hx
  simp only [Finset.mem_coe, hmem]
  by_cases hb : InBox (M1 * (c * n₁ (k + 1)) * S.L ^ (k + 1))
      (M1 * (c * n₂ (k + 1)) * S.L ^ (k + 1)) cc (liftNear cc x₁)
  · have hp : PtCorr cc x₁ x₂ := ⟨hx, hb⟩
    obtain ⟨v, hv, rfl, rfl⟩ := ptCorr_iff_exists.1 hp
    have hcc : CCorr cc (c * M1 * n₁ K * S.L ^ K) (c * M1 * n₂ K * S.L ^ K)
        (S.L ^ (k + 1) * (c * M1)) (n₁ (k + 1)) (n₂ (k + 1))
        (zcast (n₁ (k + 1)) (bidx (S.L ^ (k + 1) * (c * M1)) v))
        (zcast (n₂ (k + 1)) (bidx (S.L ^ (k + 1) * (c * M1)) v)) :=
      ⟨v, (inBox_cast e₁ e₂).1 hv, rfl, rfl⟩
    have hh := cubeSub_corr hnn₁ hnn₂ hk hq₁ hq₂ (hH.Omega_corr k).setIff
      ((cubeCorr_iff_ccorr hnn₁ hnn₂ hk).2 hcc)
    have b1 : blockMap (S.L ^ (k + 1) * (c * M1)) (n₁ (k + 1)) (zcast (M1 * (c * n₁ (k + 1)) *
        S.L ^ (k + 1)) v) = zcast (n₁ (k + 1)) (bidx (S.L ^ (k + 1) * (c * M1)) v) :=
      blockMap_zcast (by ring) (pos_cubeSide (k + 1)) v
    have b2 : blockMap (S.L ^ (k + 1) * (c * M1)) (n₂ (k + 1)) (zcast (M1 * (c * n₂ (k + 1)) *
        S.L ^ (k + 1)) v) = zcast (n₂ (k + 1)) (bidx (S.L ^ (k + 1) * (c * M1)) v) :=
      blockMap_zcast (by ring) (pos_cubeSide (k + 1)) v
    rw [b1, b2]
    exact hh
  · have h1 : ¬ CubeSub (S := S) (n := n₁) (c * M1) K (k + 1)
        (blockMap (S.L ^ (k + 1) * (c * M1)) (n₁ (k + 1)) x₁) (a₁.Omega k) := by
      intro h
      have hx' : torusCast e₁ x₁ ∈ a₁.Omega k :=
        h _ (by
          show blockMap (S.L ^ (k + 1) * (c * M1)) (n₁ (k + 1)) (torusCast e₁ x₁) = _
          rw [blockMap_torusCast])
      have := (hH.Omega_corr k).1 _ hx'
      rw [liftNear_torusCast] at this
      exact hb ((inBox_cast e₁ e₂).2 this)
    have h2 : ¬ CubeSub (S := S) (n := n₂) (c * M1) K (k + 1)
        (blockMap (S.L ^ (k + 1) * (c * M1)) (n₂ (k + 1)) x₂) (a₂.Omega k) := by
      intro h
      have hx' : torusCast e₂ x₂ ∈ a₂.Omega k :=
        h _ (by
          show blockMap (S.L ^ (k + 1) * (c * M1)) (n₂ (k + 1)) (torusCast e₂ x₂) = _
          rw [blockMap_torusCast])
      have := (hH.Omega_corr k).2.1 _ hx'
      rw [liftNear_torusCast, ← hx] at this
      exact hb ((inBox_cast e₁ e₂).2 this)
    exact ⟨fun h => absurd h h1, fun h => absurd h h2⟩

end Omega

section ProdPrime

variable {S : Setting} {n₁ n₂ : ℕ → ℕ} [∀ k, NeZero (n₁ k)] [∀ k, NeZero (n₂ k)] {R : ℕ → ℝ}
  {M K N : ℕ} [NeZero M] [NeZero S.L] {k : ℕ}

open Classical in
/-- **The product of `χ'_{k+1}(□')` over corresponding sets of cubes agrees on two tori.** -/
theorem cubeProd_chiPrimeNew_corr (g₁ : Geo S n₁ R M) (g₂ : Geo S n₂ R M) (h1 : g₂.M1 = g₁.M1)
    (h2 : g₂.c = g₁.c) (hL : 2 ≤ S.L) (hnn₁ : ∀ i, i < K → n₁ i = S.L * n₁ (i + 1))
    (hnn₂ : ∀ i, i < K → n₂ i = S.L * n₂ (i + 1)) (hk : k + 1 ≤ K) (h12₁ : 12 ≤ n₁ (k + 1))
    (h12₂ : 12 ≤ n₂ (k + 1)) {cc : Fin S.d → ℤ} (a : ℕ → ℝ) (μ δ νk : ℝ)
    (hv : EuclideanSpace ℝ (Fin N)) {a₁ : LocalHistory S n₁ M K} {a₂ : LocalHistory S n₂ M K}
    (hH : HistCorr cc a₁ a₂) {B₁ : Set (Torus S.d (n₁ (k + 1)))} {B₂ : Set (Torus S.d (n₂ (k + 1)))}
    (hB : CSetCorr cc (M * n₁ K * S.L ^ K) (M * n₂ K * S.L ^ K) (S.L ^ (k + 1) * M) (n₁ (k + 1))
      (n₂ (k + 1)) B₁ B₂)
    (hmargin : ∀ w₀, InBox (M * n₁ K * S.L ^ K) (M * n₂ K * S.L ^ K) cc w₀ →
      zcast (n₁ (k + 1)) (bidx (S.L ^ (k + 1) * M) w₀) ∈ B₁ →
        InBoxK (5 * (S.L ^ (k + 1) * M) + 2) (M * n₁ K * S.L ^ K) (M * n₂ K * S.L ^ K) cc w₀)
    (ψ₁ : BlockAt S n₁ M K k → EuclideanSpace ℝ (Fin N))
    (ψ₂ : BlockAt S n₂ M K k → EuclideanSpace ℝ (Fin N))
    (θ₁ : BlockAt S n₁ M K (k + 1) → EuclideanSpace ℝ (Fin N))
    (θ₂ : BlockAt S n₂ M K (k + 1) → EuclideanSpace ℝ (Fin N))
    (hψ : ∀ y₁ y₂, BlkCorr cc k k y₁ y₂ → ψ₁ y₁ = ψ₂ y₂)
    (hθ : ∀ y₁ y₂, BlkCorr cc (k + 1) (k + 1) y₁ y₂ → θ₁ y₁ = θ₂ y₂) :
    ∏ y ∈ (Finset.univ.filter fun y => y ∈ B₁),
        chiPrimeNew (M1 := g₁.M1) (N₁ := g₁.c * n₁ (k + 1)) (L := S.L) (N := N) (k := k) a μ δ νk
          (fun i => hv i) (c := g₁.c) (n := n₁ (k + 1)) (by simp) y
          (omegaLevel (S := S) (n := n₁) g₁.M1 g₁.c (k + 1)
            {z | CubeSub (S := S) (n := n₁) M K (k + 1) z (a₁.Omega k)})
          (omegaLevel_blockUnion (S := S) (n := n₁) g₁.M1 g₁.c (k + 1) _)
          (blockCfgOf g₁ hnn₁ (Nat.le_succ k) hk ψ₁, blockCfgOf g₁ hnn₁ le_rfl hk θ₁) =
      ∏ y ∈ (Finset.univ.filter fun y => y ∈ B₂),
        chiPrimeNew (M1 := g₂.M1) (N₁ := g₂.c * n₂ (k + 1)) (L := S.L) (N := N) (k := k) a μ δ νk
          (fun i => hv i) (c := g₂.c) (n := n₂ (k + 1)) (by simp) y
          (omegaLevel (S := S) (n := n₂) g₂.M1 g₂.c (k + 1)
            {z | CubeSub (S := S) (n := n₂) M K (k + 1) z (a₂.Omega k)})
          (omegaLevel_blockUnion (S := S) (n := n₂) g₂.M1 g₂.c (k + 1) _)
          (blockCfgOf g₂ hnn₂ (Nat.le_succ k) hk ψ₂, blockCfgOf g₂ hnn₂ le_rfl hk θ₂) := by
  obtain ⟨M1, c, neM1, nec, hM, hc, hRlow, hRmono⟩ := g₁
  obtain ⟨M1', c', neM1', nec', hM', hc', hRlow', hRmono'⟩ := g₂
  simp only at h1 h2 ⊢
  have h1' := h1.symm
  have h2' := h2.symm
  subst h1' h2'
  subst hM
  have hP := pos_cubeSide (S := S) (M := c * M1) (k + 1)
  have e₁ := site_eq (c := c) (M1 := M1) (L := S.L) (q := k + 1) (n := n₁) rfl hnn₁ hk
  have e₂ := site_eq (c := c) (M1 := M1) (L := S.L) (q := k + 1) (n := n₂) rfl hnn₂ hk
  refine prod_cset hP (Balaban.LargeField.fine_eq hnn₁ hk) (Balaban.LargeField.fine_eq hnn₂ hk)
    (by omega) (by omega) hB _ _ ?_
  intro y₁ y₂ hy₁ hy₂ hcc
  obtain ⟨w₀, hw, rfl, rfl⟩ := hcc
  have hm := hmargin w₀ hw hy₁
  refine chiPrimeNew_corr hc hL h12₁ h12₂ ((inBoxK_cast e₁ e₂).2 hm) a μ δ νk (fun i => hv i)
    _ _ _ _ _ _ (setIff_omegaLevel rfl hnn₁ hnn₂ hk hH (by omega) (by omega)) _ _ _ _ ?_ ?_
  · intro w hwb i
    rw [blockCfgOf_zcast_block, blockCfgOf_zcast_block]
    have := hψ (zcast (c * M1 * n₁ K * S.L ^ (K - k)) (bidx (S.L ^ k) w))
      (zcast (c * M1 * n₂ K * S.L ^ (K - k)) (bidx (S.L ^ k) w))
      ((blkCorr_iff_ccorr (by omega)).2 ⟨w, (inBox_cast e₁ e₂).1 hwb, rfl, rfl⟩)
    rw [this]
  · intro w hwb i
    rw [blockCfgOf_zcast_block, blockCfgOf_zcast_block]
    have := hθ (zcast (c * M1 * n₁ K * S.L ^ (K - (k + 1))) (bidx (S.L ^ (k + 1)) w))
      (zcast (c * M1 * n₂ K * S.L ^ (K - (k + 1))) (bidx (S.L ^ (k + 1)) w))
      ((blkCorr_iff_ccorr hk).2 ⟨w, (inBox_cast e₁ e₂).1 hwb, rfl, rfl⟩)
    rw [this]

end ProdPrime

end Balaban.RootFSpine
