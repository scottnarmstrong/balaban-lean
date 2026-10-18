/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Background.TwoTorusChiNewParts

/-!
# `χ^new_k` on two tori

`chiNew_corr`: at corresponding configurations, the characteristic function `χ^new_k(Z')` of
Definition II.3.4 (new conditions (1.24), (1.25)) of the quiet kernel agrees on two tori.
-/

@[expose] public section

namespace Balaban.RootFSpine

open Balaban Balaban.Multiscale Balaban.LargeField RegionHistory

theorem forall_prem_iff {α β : Type*} {P₁ Q₁ : α → Prop} {P₂ Q₂ : β → Prop} {R : α → β → Prop}
    (ha : ∀ a, P₁ a → ∃ b, R a b) (hb : ∀ b, P₂ b → ∃ a, R a b)
    (hP : ∀ a b, R a b → (P₁ a ↔ P₂ b)) (hQ : ∀ a b, R a b → P₁ a → (Q₁ a ↔ Q₂ b)) :
    (∀ a, P₁ a → Q₁ a) ↔ (∀ b, P₂ b → Q₂ b) := by
  constructor
  · intro h b hb₂
    obtain ⟨a, hab⟩ := hb b hb₂
    have ha₁ := (hP a b hab).2 hb₂
    exact (hQ a b hab ha₁).1 (h a ha₁)
  · intro h a ha₁
    obtain ⟨b, hab⟩ := ha a ha₁
    exact (hQ a b hab ha₁).2 (h b ((hP a b hab).1 ha₁))

section Final

variable {S : Setting} {n₁ n₂ : ℕ → ℕ} [∀ k, NeZero (n₁ k)] [∀ k, NeZero (n₂ k)] {R : ℕ → ℝ}
  {k0 K M N : ℕ} [NeZero M] [NeZero S.L] {k : ℕ} {cc : Fin S.d → ℤ}

omit [∀ k, NeZero (n₁ k)] [NeZero M] [NeZero S.L] in
theorem lhOmegaSim_succ_eq (a : LocalHistory S n₁ M K) :
    lhOmegaSim a (k + 1) (k + 1) =
      nbhd 1 {z | CubeSub (S := S) (n := n₁) M K (k + 1) z (lhOmega a (k + 1) (k + 1))} := by
  unfold lhOmegaSim lhOmegaNb
  have h : ¬ (k + 1 = k + 1 + 1) := by omega
  simp only [h, ↓reduceIte]

omit [∀ k, NeZero (n₁ k)] [NeZero M] [NeZero S.L] in
theorem lhOmegaSim_succ_succ_eq (a : LocalHistory S n₁ M K) :
    lhOmegaSim a (k + 1) (k + 1 + 1) = ∅ := by
  unfold lhOmegaSim lhOmegaNb
  simp only [↓reduceIte]

end Final

section Parts

variable {S : Setting} {n₁ n₂ : ℕ → ℕ} [∀ k, NeZero (n₁ k)] [∀ k, NeZero (n₂ k)] {R : ℕ → ℝ}
  {k0 K M N : ℕ} [NeZero M] [NeZero S.L] {k : ℕ} {cc : Fin S.d → ℤ}
  (Hl₁ : RegionHistory S n₁ R k0 K) (Hl₂ : RegionHistory S n₂ R k0 K)
  (hrem₁ : ∀ j, Hl₁.rem j = ∅) (hrem₂ : ∀ j, Hl₂.rem j = ∅) (hk : k + 1 ≤ K)
  (Zc₁ : Finset (Torus S.d (n₁ (k + 1)))) (Zc₂ : Finset (Torus S.d (n₂ (k + 1))))
  (hZc₁ : Zc₁ ∈ comps (S.omega (k + 1)) (Hl₁.F.Zp (k + 1)))
  (hZc₂ : Zc₂ ∈ comps (S.omega (k + 1)) (Hl₂.F.Zp (k + 1)))
  (hH : HistCorr cc (locHist Hl₁ M K (k + 1) Zc₁) (locHist Hl₂ M K (k + 1) Zc₂))
  (hV : SetCorr cc (Vsites R (locHist Hl₁ M K (k + 1) Zc₁) (k + 1))
    (Vsites R (locHist Hl₂ M K (k + 1) Zc₂) (k + 1)))
  (h32₁ : 32 ≤ n₁ (k + 1)) (h32₂ : 32 ≤ n₂ (k + 1))
  (hL : 2 ≤ S.L) (hR₁ : ∀ j, 1 ≤ j → j < K → S.Rb ≤ R j) (hR₂ : ∀ j, 1 ≤ j → j < K → S.Rb ≤ R j)
  (hω₁ : 2 * ⌊R k⌋₊ + S.L + 11 ≤ S.omega (k + 1)) (hω₂ : 2 * ⌊R k⌋₊ + S.L + 11 ≤ S.omega (k + 1))
  (hR6 : 6 ≤ ⌊R k⌋₊)
  {x₁ : NewCfg N (locHist Hl₁ M K (k + 1) Zc₁) k} {x₂ : NewCfg N (locHist Hl₂ M K (k + 1) Zc₂) k}
  {o₁ : OutT N R (locHist Hl₁ M K (k + 1) Zc₁) (k + 1)}
  {o₂ : OutT N R (locHist Hl₂ M K (k + 1) Zc₂) (k + 1)}
  (hout : OutCorr cc (k + 1) o₁ o₂) (hcfg : CfgCorr cc x₁ x₂)

include hrem₁ hZc₁ hk in
theorem mem_Zc_of_cubeSub {y : Torus S.d (n₁ (k + 1))}
    (hy : CubeSub (S := S) (n := n₁) M K (k + 1) y ((locHist Hl₁ M K (k + 1) Zc₁).Z (k + 1))) :
    y ∈ (Zc₁ : Set (Torus S.d (n₁ (k + 1)))) := by
  have := zcubes_locHist (M := M) Hl₁ hrem₁ hk Zc₁ hZc₁
  exact this.subset hy

include hrem₁ hk hZc₁ hH hV h32₁ h32₂ hR6 in
/-- The neighbourhood `Ω^∼_{k+1}` of the localized histories, at corresponding cubes of `Zc`. -/
theorem lhOmegaSim_iff {y₁ : Torus S.d (n₁ (k + 1))} {y₂ : Torus S.d (n₂ (k + 1))}
    (hy : CCorr cc (M * n₁ K * S.L ^ K) (M * n₂ K * S.L ^ K) (S.L ^ (k + 1) * M) (n₁ (k + 1))
      (n₂ (k + 1)) y₁ y₂) (hy₁ : y₁ ∈ (Zc₁ : Set (Torus S.d (n₁ (k + 1))))) :
    y₁ ∈ lhOmegaSim (locHist Hl₁ M K (k + 1) Zc₁) (k + 1) (k + 1) ↔
      y₂ ∈ lhOmegaSim (locHist Hl₂ M K (k + 1) Zc₂) (k + 1) (k + 1) := by
  obtain ⟨w, hw, rfl, rfl⟩ := hy
  rw [lhOmegaSim_succ_eq, lhOmegaSim_succ_eq]
  have hP : 0 < S.L ^ (k + 1) * M :=
    Nat.mul_pos (pow_pos (Nat.pos_of_ne_zero (NeZero.ne _)) _) (Nat.pos_of_ne_zero (NeZero.ne _))
  have hm := margin₁ Hl₁ Hl₂ hrem₁ hk Zc₁ Zc₂ hZc₁ hV (r := 0) (m := 1) (by omega) (by omega)
    (zcast _ w) (by
      rw [cubeMap_zcast Hl₁.F.hnn hk]
      exact subset_nbhd 0 _ hy₁)
  rw [hw.liftNear_zcast₁] at hm
  refine nbhd_iff_of_margin hP (fun z₁ z₂ hz => ?_) hm
  exact cubeSub_corr Hl₁.F.hnn Hl₂.F.hnn hk (by have := h32₁; omega) (by have := h32₂; omega)
    (hH.lhOmega_iff (k + 1) (k + 1)) ((cubeCorr_iff_ccorr Hl₁.F.hnn Hl₂.F.hnn hk).2 hz)

include hrem₁ hrem₂ hk hZc₁ hZc₂ hH hV h32₁ h32₂ hR6 hL hR₁ hR₂ hω₁ hω₂ hcfg hout in
/-- **The conditions (1.24) of `χ^new_k` agree on two tori.** -/
theorem partA_iff (δ' : ℝ) :
    (∀ y : Torus S.d (n₁ (k + 1)),
      (CubeSub (S := S) (n := n₁) M K (k + 1) y ((locHist Hl₁ M K (k + 1) Zc₁).Z (k + 1)) ∧
        y ∈ lhOmegaSim (locHist Hl₁ M K (k + 1) Zc₁) (k + 1) (k + 1)) →
      PsiTildeMulti (subMultiscaleField N (locHist Hl₁ M K (k + 1) Zc₁) (k + 1)
          (Vblk R (locHist Hl₁ M K (k + 1) Zc₁) (k + 1)) x₁ o₁)
        (genBlocksIn (Hl₁.histGen (M := M) (K' := K) le_rfl hrem₁ hL hR₁) (k + 1)
          (nbhd 1 {y})) δ') ↔
    (∀ y : Torus S.d (n₂ (k + 1)),
      (CubeSub (S := S) (n := n₂) M K (k + 1) y ((locHist Hl₂ M K (k + 1) Zc₂).Z (k + 1)) ∧
        y ∈ lhOmegaSim (locHist Hl₂ M K (k + 1) Zc₂) (k + 1) (k + 1)) →
      PsiTildeMulti (subMultiscaleField N (locHist Hl₂ M K (k + 1) Zc₂) (k + 1)
          (Vblk R (locHist Hl₂ M K (k + 1) Zc₂) (k + 1)) x₂ o₂)
        (genBlocksIn (Hl₂.histGen (M := M) (K' := K) le_rfl hrem₂ hL hR₂) (k + 1)
          (nbhd 1 {y})) δ') := by
  have hq₁ : 4 ≤ n₁ (k + 1) := by omega
  have hq₂ : 4 ≤ n₂ (k + 1) := by omega
  refine forall_prem_iff (R := CCorr cc (M * n₁ K * S.L ^ K) (M * n₂ K * S.L ^ K)
    (S.L ^ (k + 1) * M) (n₁ (k + 1)) (n₂ (k + 1))) ?_ ?_ ?_ ?_
  · intro y₁ hy₁
    obtain ⟨y₂, hc, -⟩ := exists_ccorr_of_bsub (pos_cubeSide (k + 1))
      (Balaban.LargeField.fine_eq Hl₁.F.hnn hk) (Balaban.LargeField.fine_eq Hl₂.F.hnn hk)
      hq₁ hq₂ (hH.Z_corr (k + 1)) hy₁.1
    exact ⟨y₂, hc⟩
  · intro y₂ hy₂
    obtain ⟨y₁, hc, -⟩ := exists_ccorr_of_bsub' (pos_cubeSide (k + 1))
      (Balaban.LargeField.fine_eq Hl₁.F.hnn hk) (Balaban.LargeField.fine_eq Hl₂.F.hnn hk)
      hq₁ hq₂ (hH.Z_corr (k + 1)) hy₂.1
    exact ⟨y₁, hc⟩
  · intro y₁ y₂ hy
    have hcs := cubeSub_corr Hl₁.F.hnn Hl₂.F.hnn hk hq₁ hq₂ (hH.Z_corr (k + 1)).setIff
      ((cubeCorr_iff_ccorr Hl₁.F.hnn Hl₂.F.hnn hk).2 hy)
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨hcs.1 h1, (lhOmegaSim_iff Hl₁ Hl₂ hrem₁ hk Zc₁ Zc₂ hZc₁ hH hV h32₁ h32₂ hR6 hy
        (mem_Zc_of_cubeSub Hl₁ hrem₁ hk Zc₁ hZc₁ h1)).1 h2⟩
    · rintro ⟨h1, h2⟩
      have h1' := hcs.2 h1
      exact ⟨h1', (lhOmegaSim_iff Hl₁ Hl₂ hrem₁ hk Zc₁ Zc₂ hZc₁ hH hV h32₁ h32₂ hR6 hy
        (mem_Zc_of_cubeSub Hl₁ hrem₁ hk Zc₁ hZc₁ h1')).2 h2⟩
  · intro y₁ y₂ hy hP
    exact psiTilde_genBlocks_iff Hl₁ Hl₂ hrem₁ hrem₂ hk Zc₁ Zc₂ hZc₁ hZc₂ hH hV h32₁ h32₂ hL hR₁
      hR₂ hω₁ hω₂ hR6 hout hcfg hy (mem_Zc_of_cubeSub Hl₁ hrem₁ hk Zc₁ hZc₁ hP.1) δ'

include hk hH h32₁ h32₂ hcfg in
/-- **The bound on the fluctuation field of `χ^new_k` agrees on two tori.** -/
theorem partC_iff (c' : ℝ) :
    (∀ y : BlockAt S n₁ M K k,
      BlockSub (S := S) (n := n₁) (M := M) (K := K) k y
        ((locHist Hl₁ M K (k + 1) Zc₁).Omega k \ (locHist Hl₁ M K (k + 1) Zc₁).OmegaDD k) →
      ‖subFluctField N (locHist Hl₁ M K (k + 1) Zc₁) (k + 1) x₁ k y‖ < c') ↔
    (∀ y : BlockAt S n₂ M K k,
      BlockSub (S := S) (n := n₂) (M := M) (K := K) k y
        ((locHist Hl₂ M K (k + 1) Zc₂).Omega k \ (locHist Hl₂ M K (k + 1) Zc₂).OmegaDD k) →
      ‖subFluctField N (locHist Hl₂ M K (k + 1) Zc₂) (k + 1) x₂ k y‖ < c') := by
  have hkK : k ≤ K := by omega
  have hX := (hH.Omega_corr k).sdiff_iff (hH.OmegaDD_corr k).setIff
  have hq₁ := four_le_block (S := S) (M := M) Hl₁.F.hnn hk h32₁ (j := k) (by omega)
  have hq₂ := four_le_block (S := S) (M := M) Hl₂.F.hnn hk h32₂ (j := k) (by omega)
  have hPk : 0 < S.L ^ k := pow_pos (Nat.pos_of_ne_zero (NeZero.ne _)) k
  refine forall_prem_iff (R := fun y₁ y₂ => BlkCorr cc k k y₁ y₂) ?_ ?_ ?_ ?_
  · intro y₁ hy₁
    obtain ⟨y₂, hc, -⟩ := exists_ccorr_of_bsub hPk (Multiscale.side_eq hkK)
      (Multiscale.side_eq hkK) hq₁ hq₂ hX hy₁
    exact ⟨y₂, (blkCorr_iff_ccorr hkK).2 hc⟩
  · intro y₂ hy₂
    obtain ⟨y₁, hc, -⟩ := exists_ccorr_of_bsub' hPk (Multiscale.side_eq hkK)
      (Multiscale.side_eq hkK) hq₁ hq₂ hX hy₂
    exact ⟨y₁, (blkCorr_iff_ccorr hkK).2 hc⟩
  · intro y₁ y₂ hy
    exact blockSub_corr hkK hq₁ hq₂ hX.setIff hy
  · intro y₁ y₂ hy _
    rw [subFluctField_corr hH hcfg (fun p₁ p₂ h => newVars_iff p₁ p₂ h) hkK hq₁ hq₂ hy]

omit [∀ k, NeZero (n₂ k)] in
theorem p3_descent (hnn : ∀ i, i < K → n₁ i = S.L * n₁ (i + 1)) (hk : k + 1 ≤ K)
    (y : Torus S.d (n₁ k)) (E : Set (Torus S.d (n₁ (k + 1)))) :
    (∀ x, cubeMap n₁ S.L M K k x = y → cubeMap n₁ S.L M K (k + 1) x ∉ E) ↔
      blockMap S.L (n₁ (k + 1)) y ∉ E := by
  constructor
  · intro h hE
    obtain ⟨x, hx⟩ := exists_site_cube (M := M) hnn (by omega : k ≤ K) y
    apply h x hx
    rw [← cubeMap_succ (fun i hi => hnn i hi) hk, hx]
    exact hE
  · intro h x hx hE
    apply h
    rw [← hx, cubeMap_succ (fun i hi => hnn i hi) hk]
    exact hE

include hrem₁ hrem₂ hk hZc₁ hZc₂ hH hV h32₁ h32₂ hR6 hcfg hout in
/-- **The conditions (1.25) of `χ^new_k` agree on two tori** (the scale `j ∈ {k, k + 1}`). -/
theorem partB_iff {j : ℕ} (hj : j = k ∨ j = k + 1) (δ' : ℝ) :
    (∀ y : Torus S.d (n₁ j),
      (CubeSub (S := S) (n := n₁) M K j y
          (fineSet (S := S) (n := n₁) M K (k + 1) (Zc₁ : Set (Torus S.d (n₁ (k + 1))))) ∧
        (∀ x, cubeMap n₁ S.L M K j x = y → x ∉ (locHist Hl₁ M K (k + 1) Zc₁).Z j) ∧
        (∀ x, cubeMap n₁ S.L M K j x = y →
          cubeMap n₁ S.L M K (j + 1) x ∉ lhOmegaSim (locHist Hl₁ M K (k + 1) Zc₁) (k + 1) (j + 1))) →
      PsiTildeMulti (subMultiscaleField N (locHist Hl₁ M K (k + 1) Zc₁) (k + 1)
          (Vblk R (locHist Hl₁ M K (k + 1) Zc₁) (k + 1)) x₁ o₁)
        (scaleBlocksIn (S := S) (n := n₁) (M := M) (K := K) j (nbhd 1 {y})) δ') ↔
    (∀ y : Torus S.d (n₂ j),
      (CubeSub (S := S) (n := n₂) M K j y
          (fineSet (S := S) (n := n₂) M K (k + 1) (Zc₂ : Set (Torus S.d (n₂ (k + 1))))) ∧
        (∀ x, cubeMap n₂ S.L M K j x = y → x ∉ (locHist Hl₂ M K (k + 1) Zc₂).Z j) ∧
        (∀ x, cubeMap n₂ S.L M K j x = y →
          cubeMap n₂ S.L M K (j + 1) x ∉ lhOmegaSim (locHist Hl₂ M K (k + 1) Zc₂) (k + 1) (j + 1))) →
      PsiTildeMulti (subMultiscaleField N (locHist Hl₂ M K (k + 1) Zc₂) (k + 1)
          (Vblk R (locHist Hl₂ M K (k + 1) Zc₂) (k + 1)) x₂ o₂)
        (scaleBlocksIn (S := S) (n := n₂) (M := M) (K := K) j (nbhd 1 {y})) δ') := by
  have hjK : j ≤ K := by omega
  have hq₁ : 4 ≤ n₁ j := by have := n_ge_of_le (S := S) Hl₁.F.hnn hk (j := j) (by omega); omega
  have hq₂ : 4 ≤ n₂ j := by have := n_ge_of_le (S := S) Hl₂.F.hnn hk (j := j) (by omega); omega
  have hF := setIff_fineSet_Zc Hl₁ Hl₂ hrem₁ hrem₂ Zc₁ Zc₂ hZc₁ hZc₂ hH
  have hFc : SetCorr cc
      (fineSet (S := S) (n := n₁) M K (k + 1) (Zc₁ : Set (Torus S.d (n₁ (k + 1)))))
      (fineSet (S := S) (n := n₂) M K (k + 1) (Zc₂ : Set (Torus S.d (n₂ (k + 1))))) := by
    have := hH.Z_corr (k + 1)
    rw [locHist_Z_top Hl₁ hrem₁ Zc₁ hZc₁, locHist_Z_top Hl₂ hrem₂ Zc₂ hZc₂] at this
    exact this
  refine forall_prem_iff (R := CCorr cc (M * n₁ K * S.L ^ K) (M * n₂ K * S.L ^ K)
    (S.L ^ j * M) (n₁ j) (n₂ j)) ?_ ?_ ?_ ?_
  · intro y₁ hy₁
    obtain ⟨y₂, hc, -⟩ := exists_ccorr_of_bsub (pos_cubeSide j)
      (Balaban.LargeField.fine_eq Hl₁.F.hnn hjK) (Balaban.LargeField.fine_eq Hl₂.F.hnn hjK)
      hq₁ hq₂ hFc hy₁.1
    exact ⟨y₂, hc⟩
  · intro y₂ hy₂
    obtain ⟨y₁, hc, -⟩ := exists_ccorr_of_bsub' (pos_cubeSide j)
      (Balaban.LargeField.fine_eq Hl₁.F.hnn hjK) (Balaban.LargeField.fine_eq Hl₂.F.hnn hjK)
      hq₁ hq₂ hFc hy₂.1
    exact ⟨y₁, hc⟩
  · intro y₁ y₂ hy
    have hcc := (cubeCorr_iff_ccorr Hl₁.F.hnn Hl₂.F.hnn hjK).2 hy
    have e1 := cubeSub_corr Hl₁.F.hnn Hl₂.F.hnn hjK hq₁ hq₂ hF hcc
    have e2 := cubeSub_corr Hl₁.F.hnn Hl₂.F.hnn hjK hq₁ hq₂ (hH.Z_corr j).setIff.compl hcc
    have hP3 : CubeSub (S := S) (n := n₁) M K j y₁
        (fineSet (S := S) (n := n₁) M K (k + 1) (Zc₁ : Set (Torus S.d (n₁ (k + 1))))) →
        ((∀ x, cubeMap n₁ S.L M K j x = y₁ →
          cubeMap n₁ S.L M K (j + 1) x ∉ lhOmegaSim (locHist Hl₁ M K (k + 1) Zc₁) (k + 1) (j + 1)) ↔
        (∀ x, cubeMap n₂ S.L M K j x = y₂ →
          cubeMap n₂ S.L M K (j + 1) x ∉ lhOmegaSim (locHist Hl₂ M K (k + 1) Zc₂) (k + 1) (j + 1))) := by
      intro h1
      rcases hj with hj' | hj'
      · subst hj'
        rw [p3_descent Hl₁.F.hnn hk y₁ _, p3_descent Hl₂.F.hnn hk y₂ _]
        have hy₁' : blockMap S.L (n₁ (j + 1)) y₁ ∈ (Zc₁ : Set (Torus S.d (n₁ (j + 1)))) := by
          obtain ⟨s, hs⟩ := exists_site_cube (M := M) Hl₁.F.hnn (by omega : j ≤ K) y₁
          have := h1 s hs
          have h2 : cubeMap n₁ S.L M K (j + 1) s ∈ (Zc₁ : Set (Torus S.d (n₁ (j + 1)))) := this
          rw [← cubeMap_succ (fun i hi => Hl₁.F.hnn i hi) hk, hs] at h2
          exact h2
        have hc' := ccorr_coarsen (Nat.pos_of_ne_zero (NeZero.ne S.L)) (Hl₁.F.hnn j (by omega))
          (Hl₂.F.hnn j (by omega)) hy
        have e : S.L ^ j * M * S.L = S.L ^ (j + 1) * M := by ring
        rw [e] at hc'
        exact not_congr (lhOmegaSim_iff Hl₁ Hl₂ hrem₁ hk Zc₁ Zc₂ hZc₁ hH hV h32₁ h32₂ hR6 hc' hy₁')
      · subst hj'
        constructor
        · intro _ x _ h
          rw [lhOmegaSim_succ_succ_eq] at h; exact h
        · intro _ x _ h
          rw [lhOmegaSim_succ_succ_eq] at h; exact h
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨e1.1 h1, e2.1 h2, (hP3 h1).1 h3⟩
    · rintro ⟨h1, h2, h3⟩
      have h1' := e1.2 h1
      exact ⟨h1', e2.2 h2, (hP3 h1').2 h3⟩
  · intro y₁ y₂ hy hP
    exact psiTilde_scaleBlocks_iff Hl₁ Hl₂ hrem₁ hrem₂ hk Zc₁ Zc₂ hZc₁ hZc₂ hH hV h32₁ h32₂ hR6
      hout hcfg hj hy hP.1 δ'

include hrem₁ hrem₂ hk hZc₁ hZc₂ hH hV h32₁ h32₂ hR6 hL hR₁ hR₂ hω₁ hω₂ hcfg hout in
/-- **`χ^new_k(Z')` of the quiet kernel agrees on two tori.** -/
theorem chiNew_corr (cs : OpConsts) :
    chiNew (locHist Hl₁ M K (k + 1) Zc₁) k
      (Hl₁.histGen (M := M) (K' := K) le_rfl hrem₁ hL hR₁)
      (fineSet (S := S) (n := n₁) M K (k + 1) (Zc₁ : Set (Torus S.d (n₁ (k + 1)))))
      cs.delta cs.p0 cs.Cpsi
      (subMultiscaleField N (locHist Hl₁ M K (k + 1) Zc₁) (k + 1)
          (Vblk R (locHist Hl₁ M K (k + 1) Zc₁) (k + 1)) x₁ o₁,
        subFluctField N (locHist Hl₁ M K (k + 1) Zc₁) (k + 1) x₁) =
    chiNew (locHist Hl₂ M K (k + 1) Zc₂) k
      (Hl₂.histGen (M := M) (K' := K) le_rfl hrem₂ hL hR₂)
      (fineSet (S := S) (n := n₂) M K (k + 1) (Zc₂ : Set (Torus S.d (n₂ (k + 1)))))
      cs.delta cs.p0 cs.Cpsi
      (subMultiscaleField N (locHist Hl₂ M K (k + 1) Zc₂) (k + 1)
          (Vblk R (locHist Hl₂ M K (k + 1) Zc₂) (k + 1)) x₂ o₂,
        subFluctField N (locHist Hl₂ M K (k + 1) Zc₂) (k + 1) x₂) := by
  unfold chiNew
  refine charFn_eq_of_iff ?_
  unfold ChiNewProp
  refine and_congr ?_ (and_congr ?_ ?_)
  · have := partA_iff Hl₁ Hl₂ hrem₁ hrem₂ hk Zc₁ Zc₂ hZc₁ hZc₂ hH hV h32₁ h32₂ hL hR₁ hR₂ hω₁ hω₂
      hR6 hout hcfg (3 * S.d * S.L * cs.delta k)
    exact Iff.trans (forall_congr' fun y => and_imp.symm)
      (this.trans (forall_congr' fun y => and_imp))
  · refine forall_congr' fun j => imp_congr_right fun hj1 => imp_congr_right fun hj => ?_
    have := partB_iff Hl₁ Hl₂ hrem₁ hrem₂ hk Zc₁ Zc₂ hZc₁ hZc₂ hH hV h32₁ h32₂ hR6 hout hcfg hj
      (3 * cs.delta j)
    refine Iff.trans (forall_congr' fun y => ?_) (this.trans (forall_congr' fun y => ?_))
    · tauto
    · tauto
  · exact partC_iff Hl₁ Hl₂ hk Zc₁ Zc₂ hH h32₁ h32₂ hcfg (cs.Cpsi * cs.p0 k)

end Parts

end Balaban.RootFSpine
