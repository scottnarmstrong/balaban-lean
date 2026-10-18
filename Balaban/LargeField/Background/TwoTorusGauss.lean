/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Background.TwoTorusVars
public import Balaban.LargeField.R.DeltaPsiEdge

/-!
# The Gaussian factors of the quiet kernel on two tori

For corresponding localized histories, configurations and outputs, the coarsened field `Qψ_k`
(`qCoarseK`) agrees at corresponding `(k+1)`-blocks of `Ω^c_{k+1} ∩ Z'`, and the product `gaussProd`
of the Gaussian factors over these blocks agrees (`gaussProd_corr`).
-/

@[expose] public section

namespace Balaban.RootFSpine

open Balaban Balaban.LargeField RegionHistory

section Gauss

variable {S : Setting} {n₁ n₂ : ℕ → ℕ} [∀ k, NeZero (n₁ k)] [∀ k, NeZero (n₂ k)] {M K N : ℕ}
  [NeZero M] [NeZero S.L] {cc : Fin S.d → ℤ} {a₁ : LocalHistory S n₁ M K}
  {a₂ : LocalHistory S n₂ M K} {k : ℕ}

omit [∀ k, NeZero (n₁ k)] [∀ k, NeZero (n₂ k)] [NeZero M] [NeZero S.L] in
theorem newVars_iff (p₁ : InternalVars a₁ (k + 1)) (p₂ : InternalVars a₂ (k + 1))
    (h : VarCorr cc p₁ p₂) : p₁ ∈ newVars a₁ k ↔ p₂ ∈ newVars a₂ k := by
  obtain ⟨-, hj, -⟩ := h
  show p₁.1.1.val = k ↔ p₂.1.1.val = k
  rw [hj]

omit [NeZero S.L] in
theorem coarse_size (hk : k + 1 ≤ K) (m : ℕ) :
    m * S.L ^ (K - k) = S.L * (m * S.L ^ (K - (k + 1))) := by
  rw [show K - k = (K - (k + 1)) + 1 by omega, pow_succ]; ring

theorem blockSub_children {y : BlockAt S n₁ M K (k + 1)} {B : Set (Torus S.d (M * n₁ K * S.L ^ K))}
    (hk : k + 1 ≤ K) (hy : BlockSub (S := S) (n := n₁) (M := M) (K := K) (k + 1) y B)
    {y' : BlockAt S n₁ M K k}
    (hc : blockMap S.L (M * n₁ K * S.L ^ (K - (k + 1))) y' = y) :
    BlockSub (S := S) (n := n₁) (M := M) (K := K) k y' B := by
  intro x hx
  apply hy
  rw [Multiscale.jBlock, ← hc, ← hx]
  exact jBlock_succ_eq_blockMap hk x

/-- **The coarsened field `Qψ_k` of corresponding configurations agrees at corresponding
`(k+1)`-blocks of `Ω^c_{k+1} ∩ Z'`.** -/
theorem qCoarseK_corr {A₁ : Set (InternalVars a₁ (k + 1))} {A₂ : Set (InternalVars a₂ (k + 1))}
    {x₁ : SubCfg N a₁ (k + 1) A₁} {x₂ : SubCfg N a₂ (k + 1) A₂}
    (hH : HistCorr cc a₁ a₂) (hcfg : CfgCorr cc x₁ x₂)
    (hA : ∀ p₁ p₂, VarCorr cc p₁ p₂ → (p₁ ∈ A₁ ↔ p₂ ∈ A₂)) (hk : k + 1 ≤ K)
    (hq₁ : ∀ j, j ≤ k + 1 → 4 ≤ M * n₁ K * S.L ^ (K - j))
    (hq₂ : ∀ j, j ≤ k + 1 → 4 ≤ M * n₂ K * S.L ^ (K - j)) {y₁ : BlockAt S n₁ M K (k + 1)}
    {y₂ : BlockAt S n₂ M K (k + 1)} (hy : BlkCorr cc (k + 1) (k + 1) y₁ y₂)
    (hsub : BlockSub (S := S) (n := n₁) (M := M) (K := K) (k + 1) y₁
      (a₁.Z (k + 1) \ a₁.Omega k)) :
    qCoarseK N x₁ y₁ = qCoarseK N x₂ y₂ := by
  classical
  have hL : 0 < S.L := Nat.pos_of_ne_zero (NeZero.ne _)
  have hPk : 0 < S.L ^ k := pow_pos hL k
  have hkK : k ≤ K := by omega
  have hB : SetCorr cc (a₁.Z (k + 1) \ a₁.Omega k) (a₂.Z (k + 1) \ a₂.Omega k) :=
    (hH.Z_corr (k + 1)).sdiff_iff (hH.Omega_corr k).setIff
  have hyc := (blkCorr_iff_ccorr (by omega)).1 hy
  have hcs₁ := coarse_size (S := S) hk (M * n₁ K)
  have hcs₂ := coarse_size (S := S) hk (M * n₂ K)
  have hco : ∀ {y' : BlockAt S n₁ M K k} {y₂' : BlockAt S n₂ M K k},
      CCorr cc (M * n₁ K * S.L ^ K) (M * n₂ K * S.L ^ K) (S.L ^ k) (M * n₁ K * S.L ^ (K - k))
        (M * n₂ K * S.L ^ (K - k)) y' y₂' →
      blockMap S.L (M * n₁ K * S.L ^ (K - (k + 1))) y' = y₁ →
      blockMap S.L (M * n₂ K * S.L ^ (K - (k + 1))) y₂' = y₂ := by
    intro y' y₂' hc hch
    have h1 := ccorr_coarsen hL hcs₁ hcs₂ hc
    rw [hch, ← pow_succ] at h1
    exact (CCorr.right_unique (pow_pos hL (k + 1)) (Multiscale.side_eq hk) (hq₁ (k + 1) le_rfl) hyc h1).symm
  unfold qCoarseK
  congr 1
  refine sum_of_rel _ _ (fun y₁' y₂' => BlkCorr cc k k y₁' y₂') (fun y' => subVarField N x₁ k y')
    (fun y' => subVarField N x₂ k y') ?_ ?_ ?_ ?_ ?_
  · intro y' hy'
    have hch := (Finset.mem_filter.1 hy').2
    obtain ⟨y₂', hc, -⟩ := exists_ccorr_of_bsub hPk (Multiscale.side_eq hkK) (Multiscale.side_eq hkK)
      (hq₁ k (by omega)) (hq₂ k (by omega)) hB (blockSub_children hk hsub hch)
    exact ⟨y₂', Finset.mem_filter.2 ⟨Finset.mem_univ _, hco hc hch⟩,
      (blkCorr_iff_ccorr hkK).2 hc⟩
  · intro y₂' hy₂'
    have hch₂ := (Finset.mem_filter.1 hy₂').2
    have hsub₂ : BlockSub (S := S) (n := n₂) (M := M) (K := K) (k + 1) y₂
        (a₂.Z (k + 1) \ a₂.Omega k) :=
      (blockSub_corr (by omega) (hq₁ (k + 1) le_rfl) (hq₂ (k + 1) le_rfl) hB.setIff hy).1 hsub
    obtain ⟨y', hc, -⟩ := exists_ccorr_of_bsub' hPk (Multiscale.side_eq hkK) (Multiscale.side_eq hkK)
      (hq₁ k (by omega)) (hq₂ k (by omega)) hB (blockSub_children hk hsub₂ hch₂)
    refine ⟨y', Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩, (blkCorr_iff_ccorr hkK).2 hc⟩
    have h1 := ccorr_coarsen hL hcs₁ hcs₂ hc
    rw [hch₂, ← pow_succ] at h1
    exact (CCorr.left_unique (pow_pos hL (k + 1)) (Multiscale.side_eq hk) (hq₂ (k + 1) le_rfl) hyc h1).symm
  · intro a b b' h h'
    exact CCorr.right_unique hPk (Multiscale.side_eq hkK) (hq₁ k (by omega))
      ((blkCorr_iff_ccorr hkK).1 h) ((blkCorr_iff_ccorr hkK).1 h')
  · intro a a' b h h'
    exact CCorr.left_unique hPk (Multiscale.side_eq hkK) (hq₂ k (by omega))
      ((blkCorr_iff_ccorr hkK).1 h) ((blkCorr_iff_ccorr hkK).1 h')
  · intro y₁' y₂' _ _ h
    exact subVarField_corr hH hcfg hA hkK (hq₁ k (by omega)) (hq₂ k (by omega)) h

open Classical in
/-- **The product of the Gaussian factors of the quiet kernel agrees on two tori.** -/
theorem gaussProd_corr {x₁ : NewCfg N a₁ k} {x₂ : NewCfg N a₂ k}
    (hH : HistCorr cc a₁ a₂) (hcfg : CfgCorr cc x₁ x₂) (hk : k + 1 ≤ K)
    (hq₁ : ∀ j, j ≤ k + 1 → 4 ≤ M * n₁ K * S.L ^ (K - j))
    (hq₂ : ∀ j, j ≤ k + 1 → 4 ≤ M * n₂ K * S.L ^ (K - j)) (cs : OpConsts)
    {V₁ : Set (BlockAt S n₁ M K (k + 1))} {V₂ : Set (BlockAt S n₂ M K (k + 1))}
    {o₁ : OutConfig N V₁} {o₂ : OutConfig N V₂} (hout : OutCorr cc (k + 1) o₁ o₂) :
    gaussProd N a₁ k cs o₁ x₁ = gaussProd N a₂ k cs o₂ x₂ := by
  have hL : 0 < S.L := Nat.pos_of_ne_zero (NeZero.ne _)
  have hB : SetCorr cc (a₁.Z (k + 1) \ a₁.Omega k) (a₂.Z (k + 1) \ a₂.Omega k) :=
    (hH.Z_corr (k + 1)).sdiff_iff (hH.Omega_corr k).setIff
  unfold gaussProd
  rw [← Finset.prod_subtype (Finset.univ.filter fun y => y ∈ gaussBlocks a₁ k) (fun y => by simp)
      (fun y : BlockAt S n₁ M K (k + 1) => cs.z (k + 1) ^ N *
        gaussT N (cs.beta k * cs.aKer * (S.L : ℝ) ^ (S.d - 2)) (cs.z (k + 1) • outField N o₁ y)
          (qCoarseK N x₁ y)),
    ← Finset.prod_subtype (Finset.univ.filter fun y => y ∈ gaussBlocks a₂ k) (fun y => by simp)
      (fun y : BlockAt S n₂ M K (k + 1) => cs.z (k + 1) ^ N *
        gaussT N (cs.beta k * cs.aKer * (S.L : ℝ) ^ (S.d - 2)) (cs.z (k + 1) • outField N o₂ y)
          (qCoarseK N x₂ y))]
  refine prod_cset (pow_pos hL (k + 1)) (Multiscale.side_eq hk) (Multiscale.side_eq hk)
    (hq₁ (k + 1) le_rfl) (hq₂ (k + 1) le_rfl)
    (cSetCorr_bsub_plain (pow_pos hL (k + 1)) (Multiscale.side_eq hk) (Multiscale.side_eq hk)
      (hq₁ (k + 1) le_rfl) (hq₂ (k + 1) le_rfl) hB) _ _ ?_
  intro y₁ y₂ hy₁ _ hc
  have hbc := (blkCorr_iff_ccorr (by omega)).2 hc
  rw [hout y₁ y₂ hbc, qCoarseK_corr hH hcfg (fun p₁ p₂ h => newVars_iff p₁ p₂ h) hk hq₁ hq₂ hbc hy₁]

end Gauss

end Balaban.RootFSpine
