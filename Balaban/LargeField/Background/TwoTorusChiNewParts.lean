/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Background.TwoTorusChiNew
public import Balaban.LargeField.Background.TwoTorusGauss

/-!
# The conditions (1.24), (1.25) of `χ^new_k` on two tori

The three groups of conditions of `ChiNewProp` (Definition II.3.4) agree on two tori at
corresponding configurations: the conditions on the blocks of the generating set of the history
over a cube of `Zc` (`psiTilde_genBlocks_iff`), the conditions on the blocks of a scale over a
cube (`psiTilde_scaleBlocks_iff`) and the bound on the fluctuation field.
-/

@[expose] public section

namespace Balaban.RootFSpine

open Balaban Balaban.Multiscale Balaban.LargeField RegionHistory

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

theorem genBlocksIn_eq_blocksOver {ϱ : ℝ} (B : GeneratingSet S.d S.L (M * n₁ K) K ϱ) (j' : ℕ)
    (W : Set (Torus S.d (n₁ j'))) :
    genBlocksIn B j' W = blocksOver (fun j => {x | 1 ≤ j ∧ j ≤ K ∧ x ∈ B.layer j ∧
      cubeMap n₁ S.L M K j' x ∈ W}) := by
  ext b
  simp only [genBlocksIn, blocksOver, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h1, h2, x, hx, hb, hW⟩
    exact ⟨x, ⟨h1, h2, hx, hW⟩, hb⟩
  · rintro ⟨x, ⟨h1, h2, hx, hW⟩, hb⟩
    exact ⟨h1, h2, x, hx, hb, hW⟩

include hrem₁ hrem₂ hk hZc₁ hZc₂ hH hV h32₁ h32₂ hR6 in
/-- **A cube of `Zc₁` and its partner: the neighbourhoods of corresponding sites agree.** -/
theorem cubeNbhd_single_iff {r : ℕ} (hr : r ≤ 3) {y₁ : Torus S.d (n₁ (k + 1))}
    {y₂ : Torus S.d (n₂ (k + 1))}
    (hy : CCorr cc (M * n₁ K * S.L ^ K) (M * n₂ K * S.L ^ K) (S.L ^ (k + 1) * M) (n₁ (k + 1))
      (n₂ (k + 1)) y₁ y₂) (hy₁ : y₁ ∈ (Zc₁ : Set (Torus S.d (n₁ (k + 1)))))
    {x₁ : Torus S.d (M * n₁ K * S.L ^ K)} {x₂ : Torus S.d (M * n₂ K * S.L ^ K)}
    (hp : PtCorr cc x₁ x₂) :
    cubeMap n₁ S.L M K (k + 1) x₁ ∈ nbhd r ({y₁} : Set (Torus S.d (n₁ (k + 1)))) ↔
      cubeMap n₂ S.L M K (k + 1) x₂ ∈ nbhd r ({y₂} : Set (Torus S.d (n₂ (k + 1)))) := by
  obtain ⟨v, hv, rfl, rfl⟩ := ptCorr_iff_exists.1 hp
  have hP : 0 < S.L ^ (k + 1) * M :=
    Nat.mul_pos (pow_pos (Nat.pos_of_ne_zero (NeZero.ne _)) _) (Nat.pos_of_ne_zero (NeZero.ne _))
  have hC := ciff_singleton hP (Balaban.LargeField.fine_eq Hl₁.F.hnn hk)
    (Balaban.LargeField.fine_eq Hl₂.F.hnn hk) (by omega) (by omega) hy
  have hy₂ : y₂ ∈ (Zc₂ : Set (Torus S.d (n₂ (k + 1)))) :=
    (ciff_Zc Hl₁ Hl₂ hrem₁ hrem₂ hk Zc₁ Zc₂ hZc₁ hZc₂ hH h32₁ h32₂ y₁ y₂ hy).1 hy₁
  rw [cubeMap_zcast Hl₁.F.hnn hk, cubeMap_zcast Hl₂.F.hnn hk]
  constructor
  · intro h
    have hm := margin₁ Hl₁ Hl₂ hrem₁ hk Zc₁ Zc₂ hZc₁ hV (r := r) (m := r) (by omega)
      (by omega) (zcast _ v) (by
        rw [cubeMap_zcast Hl₁.F.hnn hk]
        exact nbhd_mono (le_refl r) (Set.singleton_subset_iff.2 hy₁) h)
    rw [hv.liftNear_zcast₁] at hm
    exact (nbhd_iff_of_margin hP hC hm).1 h
  · intro h
    have hm := margin₂ Hl₁ Hl₂ hrem₂ hk Zc₁ Zc₂ hZc₂ hV (r := r) (m := r) (by omega)
      (by omega) (zcast _ v) (by
        rw [cubeMap_zcast Hl₂.F.hnn hk]
        exact nbhd_mono (le_refl r) (Set.singleton_subset_iff.2 hy₂) h)
    rw [hv.liftNear_zcast₂] at hm
    exact (nbhd_iff_of_margin hP hC hm).2 h

include hrem₁ hrem₂ hk hZc₁ hZc₂ hH hV h32₁ h32₂ hR6 hL hR₁ hR₂ hω₁ hω₂ hcfg hout in
/-- **The conditions (1.24) on the blocks of the generating set over a cube of `Zc`** agree on two
tori at corresponding cubes. -/
theorem psiTilde_genBlocks_iff {y₁ : Torus S.d (n₁ (k + 1))} {y₂ : Torus S.d (n₂ (k + 1))}
    (hy : CCorr cc (M * n₁ K * S.L ^ K) (M * n₂ K * S.L ^ K) (S.L ^ (k + 1) * M) (n₁ (k + 1))
      (n₂ (k + 1)) y₁ y₂) (hy₁ : y₁ ∈ (Zc₁ : Set (Torus S.d (n₁ (k + 1))))) (δ : ℝ) :
    PsiTildeMulti (subMultiscaleField N (locHist Hl₁ M K (k + 1) Zc₁) (k + 1)
        (Vblk R (locHist Hl₁ M K (k + 1) Zc₁) (k + 1)) x₁ o₁)
      (genBlocksIn (Hl₁.histGen (M := M) (K' := K) le_rfl hrem₁ hL hR₁) (k + 1)
        (nbhd 1 {y₁})) δ ↔
    PsiTildeMulti (subMultiscaleField N (locHist Hl₂ M K (k + 1) Zc₂) (k + 1)
        (Vblk R (locHist Hl₂ M K (k + 1) Zc₂) (k + 1)) x₂ o₂)
      (genBlocksIn (Hl₂.histGen (M := M) (K' := K) le_rfl hrem₂ hL hR₂) (k + 1)
        (nbhd 1 {y₂})) δ := by
  have hP : 0 < S.L ^ (k + 1) * M :=
    Nat.mul_pos (pow_pos (Nat.pos_of_ne_zero (NeZero.ne _)) _) (Nat.pos_of_ne_zero (NeZero.ne _))
  have hy₂ : y₂ ∈ (Zc₂ : Set (Torus S.d (n₂ (k + 1)))) :=
    (ciff_Zc Hl₁ Hl₂ hrem₁ hrem₂ hk Zc₁ Zc₂ hZc₁ hZc₂ hH h32₁ h32₂ y₁ y₂ hy).1 hy₁
  have hsmall : ∀ j, j ≤ k + 1 → S.L ^ j + 1 ≤ 2 * (S.L ^ (k + 1) * M) := by
    intro j hj
    have h1 : S.L ^ j ≤ S.L ^ (k + 1) := Nat.pow_le_pow_right (by omega) hj
    have h2 : S.L ^ (k + 1) ≤ S.L ^ (k + 1) * M := Nat.le_mul_of_pos_right _ (by
      exact Nat.pos_of_ne_zero (NeZero.ne _))
    omega
  rw [genBlocksIn_eq_blocksOver, genBlocksIn_eq_blocksOver]
  have key := blocksOver_corr (n₁ := n₁) (n₂ := n₂) (cc := cc) (J := k + 1) hk
    (T₁ := fun j => {x | 1 ≤ j ∧ j ≤ K ∧
      x ∈ (Hl₁.histGen (M := M) (K' := K) le_rfl hrem₁ hL hR₁).layer j ∧
      cubeMap n₁ S.L M K (k + 1) x ∈ nbhd 1 {y₁}})
    (T₂ := fun j => {x | 1 ≤ j ∧ j ≤ K ∧
      x ∈ (Hl₂.histGen (M := M) (K' := K) le_rfl hrem₂ hL hR₂).layer j ∧
      cubeMap n₂ S.L M K (k + 1) x ∈ nbhd 1 {y₂}})
    (fun j x ⟨hj1, hjK, hl, hq⟩ => by
      obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      have hx : cubeMap n₁ S.L M K (k + 1) x ∈ nbhd 1 (Zc₁ : Set (Torus S.d (n₁ (k + 1)))) :=
        nbhd_mono (le_refl 1) (Set.singleton_subset_iff.2 hy₁) hq
      have hΩ := ((Hl₁.histGen (M := M) (K' := K) le_rfl hrem₁ hL hR₁).mem_layer.1 hl).1
      have hik := ((histGen_Ω_iff_lhOmega Hl₁ hrem₁ hk hL hR₁ Zc₁ hZc₁ hω₁ (r := 1) (by omega) x
        hx i).1 hΩ).1
      exact ⟨hik, ((margin₁ Hl₁ Hl₂ hrem₁ hk Zc₁ Zc₂ hZc₁ hV (r := 1) (m := 2) (by omega)
        (by omega) x hx).mono (hsmall _ hik))⟩)
    (fun j x ⟨hj1, hjK, hl, hq⟩ => by
      obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      have hx : cubeMap n₂ S.L M K (k + 1) x ∈ nbhd 1 (Zc₂ : Set (Torus S.d (n₂ (k + 1)))) :=
        nbhd_mono (le_refl 1) (Set.singleton_subset_iff.2 hy₂) hq
      have hΩ := ((Hl₂.histGen (M := M) (K' := K) le_rfl hrem₂ hL hR₂).mem_layer.1 hl).1
      have hik := ((histGen_Ω_iff_lhOmega Hl₂ hrem₂ hk hL hR₂ Zc₂ hZc₂ hω₂ (r := 1) (by omega) x
        hx i).1 hΩ).1
      exact ⟨hik, ((margin₂ Hl₁ Hl₂ hrem₂ hk Zc₁ Zc₂ hZc₂ hV (r := 1) (m := 2) (by omega)
        (by omega) x hx).mono (hsmall _ hik))⟩)
    (fun j x₁' x₂' hp => by
      have hQ := cubeNbhd_single_iff Hl₁ Hl₂ hrem₁ hrem₂ hk Zc₁ Zc₂ hZc₁ hZc₂ hH hV h32₁ h32₂ hR6
        (r := 1) (by omega) hy hy₁ hp
      constructor
      · rintro ⟨hj1, hjK, hl, hq⟩
        refine ⟨hj1, hjK, ?_, hQ.1 hq⟩
        obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
        have hx : cubeMap n₁ S.L M K (k + 1) x₁' ∈ nbhd 1 (Zc₁ : Set (Torus S.d (n₁ (k + 1)))) :=
          nbhd_mono (le_refl 1) (Set.singleton_subset_iff.2 hy₁) hq
        rw [GeneratingSet.mem_layer] at hl ⊢
        refine ⟨(histGen_ptCorr Hl₁ Hl₂ hrem₁ hrem₂ hk Zc₁ Zc₂ hZc₁ hZc₂ hH hV h32₁ h32₂ hL hR₁
          hR₂ hω₁ hω₂ hR6 (r := 1) (by omega) hp hx i).1 hl.1, fun h => hl.2 ?_⟩
        exact (histGen_ptCorr Hl₁ Hl₂ hrem₁ hrem₂ hk Zc₁ Zc₂ hZc₁ hZc₂ hH hV h32₁ h32₂ hL hR₁
          hR₂ hω₁ hω₂ hR6 (r := 1) (by omega) hp hx (i + 1)).2 h
      · rintro ⟨hj1, hjK, hl, hq⟩
        have hq1 := hQ.2 hq
        refine ⟨hj1, hjK, ?_, hq1⟩
        obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
        have hx : cubeMap n₁ S.L M K (k + 1) x₁' ∈ nbhd 1 (Zc₁ : Set (Torus S.d (n₁ (k + 1)))) :=
          nbhd_mono (le_refl 1) (Set.singleton_subset_iff.2 hy₁) hq1
        rw [GeneratingSet.mem_layer] at hl ⊢
        refine ⟨(histGen_ptCorr Hl₁ Hl₂ hrem₁ hrem₂ hk Zc₁ Zc₂ hZc₁ hZc₂ hH hV h32₁ h32₂ hL hR₁
          hR₂ hω₁ hω₂ hR6 (r := 1) (by omega) hp hx i).2 hl.1, fun h => hl.2 ?_⟩
        exact (histGen_ptCorr Hl₁ Hl₂ hrem₁ hrem₂ hk Zc₁ Zc₂ hZc₁ hZc₂ hH hV h32₁ h32₂ hL hR₁
          hR₂ hω₁ hω₂ hR6 (r := 1) (by omega) hp hx (i + 1)).1 h)
    (fun j hj => four_le_block Hl₁.F.hnn hk h32₁ hj)
    (fun j hj => four_le_block Hl₂.F.hnn hk h32₂ hj)
  refine psiTildeMulti_iff key.1 key.2.1 ?_ key.2.2
  rintro ⟨j, y⟩ _ ⟨j', y'⟩ _ hc
  obtain rfl : j = j' := hc.1
  exact subMultiscaleField_corr hH hcfg (fun p₁ p₂ h => newVars_iff p₁ p₂ h) hk
    (fun j hj => four_le_block Hl₁.F.hnn hk h32₁ hj) (fun j hj => four_le_block Hl₂.F.hnn hk h32₂ hj)
    hout j y y' hc

omit [∀ k, NeZero (n₁ k)] [NeZero M] [NeZero S.L] in
theorem scaleBlocksIn_eq_blocksOver (j : ℕ) (W : Set (Torus S.d (n₁ j))) :
    scaleBlocksIn (S := S) (n := n₁) (M := M) (K := K) j W =
      blocksOver (fun j' => {x | j' = j ∧ cubeMap n₁ S.L M K j x ∈ W}) := by
  ext ⟨j₀, y₀⟩
  simp only [scaleBlocksIn, blocksOver, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨y, hb, x, hx, hW⟩
    cases hb
    exact ⟨x, ⟨rfl, hW⟩, hx⟩
  · rintro ⟨x, ⟨hj, hW⟩, hx⟩
    subst hj
    exact ⟨y₀, rfl, x, hx, hW⟩

omit [∀ k, NeZero (n₂ k)] in
/-- A site in a cube of the neighbourhood of a cube of `Zc` (at the scale `k` or `k + 1`) is near
`Zc` at the scale `k + 1`. -/
theorem near_of_level (hnn : ∀ i, i < K → n₁ i = S.L * n₁ (i + 1)) (hk : k + 1 ≤ K) {j : ℕ}
    (hj : j = k ∨ j = k + 1) {Z : Set (Torus S.d (n₁ (k + 1)))} {y : Torus S.d (n₁ j)}
    (hX : CubeSub (S := S) (n := n₁) M K j y (fineSet (S := S) (n := n₁) M K (k + 1) Z))
    {x : Torus S.d (M * n₁ K * S.L ^ K)}
    (hx : cubeMap n₁ S.L M K j x ∈ nbhd 1 ({y} : Set (Torus S.d (n₁ j)))) :
    cubeMap n₁ S.L M K (k + 1) x ∈ nbhd 1 Z := by
  obtain ⟨s, hs⟩ := exists_site_cube (M := M) hnn (by omega : j ≤ K) y
  have hsZ : cubeMap n₁ S.L M K (k + 1) s ∈ Z := hX s hs
  rcases hj with rfl | rfl
  · obtain ⟨z, hz, hd⟩ := mem_nbhd.1 hx
    rw [Set.mem_singleton_iff] at hz
    subst hz
    have hnk := hnn j (by omega)
    have h1 := supDist_blockMap_le (L := S.L) hnk (cubeMap n₁ S.L M K j x) (cubeMap n₁ S.L M K j s)
    rw [cubeMap_succ (fun i hi => hnn i hi) hk, cubeMap_succ (fun i hi => hnn i hi) hk] at h1
    have hd' : supDist (cubeMap n₁ S.L M K j x) (cubeMap n₁ S.L M K j s) ≤ 1 := by rw [hs]; exact hd
    have hL : 0 < S.L := Nat.pos_of_ne_zero (NeZero.ne _)
    refine mem_nbhd.2 ⟨_, hsZ, h1.trans ?_⟩
    calc (supDist (cubeMap n₁ S.L M K j x) (cubeMap n₁ S.L M K j s) + S.L - 1) / S.L
        ≤ (1 + S.L - 1) / S.L := by apply Nat.div_le_div_right; omega
      _ = 1 := by rw [show 1 + S.L - 1 = S.L by omega, Nat.div_self hL]
  · exact nbhd_mono (le_refl 1) (by
      intro z hz; rw [Set.mem_singleton_iff] at hz; subst hz; rw [← hs]; exact hsZ) hx

include hrem₁ hrem₂ hk hZc₁ hZc₂ hV h32₁ h32₂ hR6 in
/-- The neighbourhood of a cube of `Zc` at the scale `j ∈ {k, k + 1}`, of corresponding sites. -/
theorem cubeNbhd_level_iff {j : ℕ} (hj : j = k ∨ j = k + 1) {y₁ : Torus S.d (n₁ j)}
    {y₂ : Torus S.d (n₂ j)}
    (hy : CCorr cc (M * n₁ K * S.L ^ K) (M * n₂ K * S.L ^ K) (S.L ^ j * M) (n₁ j) (n₂ j) y₁ y₂)
    (hX₁ : CubeSub (S := S) (n := n₁) M K j y₁
      (fineSet (S := S) (n := n₁) M K (k + 1) (Zc₁ : Set (Torus S.d (n₁ (k + 1))))))
    (hX₂ : CubeSub (S := S) (n := n₂) M K j y₂
      (fineSet (S := S) (n := n₂) M K (k + 1) (Zc₂ : Set (Torus S.d (n₂ (k + 1))))))
    {x₁ : Torus S.d (M * n₁ K * S.L ^ K)} {x₂ : Torus S.d (M * n₂ K * S.L ^ K)}
    (hp : PtCorr cc x₁ x₂) :
    cubeMap n₁ S.L M K j x₁ ∈ nbhd 1 ({y₁} : Set (Torus S.d (n₁ j))) ↔
      cubeMap n₂ S.L M K j x₂ ∈ nbhd 1 ({y₂} : Set (Torus S.d (n₂ j))) := by
  obtain ⟨v, hv, rfl, rfl⟩ := ptCorr_iff_exists.1 hp
  have hjK : j ≤ K := by omega
  have hP : 0 < S.L ^ j * M :=
    Nat.mul_pos (pow_pos (Nat.pos_of_ne_zero (NeZero.ne _)) _) (Nat.pos_of_ne_zero (NeZero.ne _))
  have hq₁ : 4 ≤ n₁ j := by have := n_ge_of_le (S := S) Hl₁.F.hnn hk (j := j) (by omega); omega
  have hq₂ : 4 ≤ n₂ j := by have := n_ge_of_le (S := S) Hl₂.F.hnn hk (j := j) (by omega); omega
  have hC := ciff_singleton hP (Balaban.LargeField.fine_eq Hl₁.F.hnn hjK)
    (Balaban.LargeField.fine_eq Hl₂.F.hnn hjK) hq₁ hq₂ hy
  have hsm : 1 * (S.L ^ j * M) ≤ 2 * (S.L ^ (k + 1) * M) := by
    have : S.L ^ j ≤ S.L ^ (k + 1) := Nat.pow_le_pow_right (Nat.pos_of_ne_zero (NeZero.ne _)) (by omega)
    have := Nat.mul_le_mul_right M this
    omega
  rw [cubeMap_zcast Hl₁.F.hnn hjK, cubeMap_zcast Hl₂.F.hnn hjK]
  constructor
  · intro h
    have hnear := near_of_level Hl₁.F.hnn hk hj hX₁ (x := zcast _ v) (by
      rw [cubeMap_zcast Hl₁.F.hnn hjK]; exact h)
    have hm := margin₁ Hl₁ Hl₂ hrem₁ hk Zc₁ Zc₂ hZc₁ hV (r := 1) (m := 2) (by omega) (by omega)
      (zcast _ v) hnear
    rw [hv.liftNear_zcast₁] at hm
    exact (nbhd_iff_of_margin hP hC (hm.mono hsm)).1 h
  · intro h
    have hnear := near_of_level Hl₂.F.hnn hk hj hX₂ (x := zcast _ v) (by
      rw [cubeMap_zcast Hl₂.F.hnn hjK]; exact h)
    have hm := margin₂ Hl₁ Hl₂ hrem₂ hk Zc₁ Zc₂ hZc₂ hV (r := 1) (m := 2) (by omega) (by omega)
      (zcast _ v) hnear
    rw [hv.liftNear_zcast₂] at hm
    exact (nbhd_iff_of_margin hP hC (hm.mono hsm)).2 h

omit [NeZero M] [NeZero S.L] in
include hrem₁ hrem₂ hZc₁ hZc₂ hH in
theorem setIff_fineSet_Zc :
    SetIff cc (fineSet (S := S) (n := n₁) M K (k + 1) (Zc₁ : Set (Torus S.d (n₁ (k + 1)))))
      (fineSet (S := S) (n := n₂) M K (k + 1) (Zc₂ : Set (Torus S.d (n₂ (k + 1))))) := by
  have := (hH.Z_corr (k + 1)).setIff
  rw [locHist_Z_top Hl₁ hrem₁ Zc₁ hZc₁, locHist_Z_top Hl₂ hrem₂ Zc₂ hZc₂] at this
  exact this

include hrem₁ hrem₂ hk hZc₁ hZc₂ hH hV h32₁ h32₂ hR6 hcfg hout in
/-- **The conditions (1.25) on the blocks of a scale over a cube** agree on two tori at
corresponding cubes of `Zc` (the scale `j = k` or `k + 1`). -/
theorem psiTilde_scaleBlocks_iff {j : ℕ} (hj : j = k ∨ j = k + 1) {y₁ : Torus S.d (n₁ j)}
    {y₂ : Torus S.d (n₂ j)}
    (hy : CCorr cc (M * n₁ K * S.L ^ K) (M * n₂ K * S.L ^ K) (S.L ^ j * M) (n₁ j) (n₂ j) y₁ y₂)
    (hX₁ : CubeSub (S := S) (n := n₁) M K j y₁
      (fineSet (S := S) (n := n₁) M K (k + 1) (Zc₁ : Set (Torus S.d (n₁ (k + 1))))))
    (δ : ℝ) :
    PsiTildeMulti (subMultiscaleField N (locHist Hl₁ M K (k + 1) Zc₁) (k + 1)
        (Vblk R (locHist Hl₁ M K (k + 1) Zc₁) (k + 1)) x₁ o₁)
      (scaleBlocksIn (S := S) (n := n₁) (M := M) (K := K) j (nbhd 1 {y₁})) δ ↔
    PsiTildeMulti (subMultiscaleField N (locHist Hl₂ M K (k + 1) Zc₂) (k + 1)
        (Vblk R (locHist Hl₂ M K (k + 1) Zc₂) (k + 1)) x₂ o₂)
      (scaleBlocksIn (S := S) (n := n₂) (M := M) (K := K) j (nbhd 1 {y₂})) δ := by
  have hjK : j ≤ K := by omega
  have hq₁ : 4 ≤ n₁ j := by have := n_ge_of_le (S := S) Hl₁.F.hnn hk (j := j) (by omega); omega
  have hq₂ : 4 ≤ n₂ j := by have := n_ge_of_le (S := S) Hl₂.F.hnn hk (j := j) (by omega); omega
  have hX₂ : CubeSub (S := S) (n := n₂) M K j y₂
      (fineSet (S := S) (n := n₂) M K (k + 1) (Zc₂ : Set (Torus S.d (n₂ (k + 1))))) :=
    (cubeSub_corr Hl₁.F.hnn Hl₂.F.hnn hjK hq₁ hq₂
      (setIff_fineSet_Zc Hl₁ Hl₂ hrem₁ hrem₂ Zc₁ Zc₂ hZc₁ hZc₂ hH)
      ((cubeCorr_iff_ccorr Hl₁.F.hnn Hl₂.F.hnn hjK).2 hy)).1 hX₁
  have hsmall : S.L ^ j + 1 ≤ 2 * (S.L ^ (k + 1) * M) := by
    have hP : 0 < S.L ^ (k + 1) * M :=
      Nat.mul_pos (pow_pos (Nat.pos_of_ne_zero (NeZero.ne _)) _) (Nat.pos_of_ne_zero (NeZero.ne _))
    have h1 : S.L ^ j ≤ S.L ^ (k + 1) :=
      Nat.pow_le_pow_right (Nat.pos_of_ne_zero (NeZero.ne _)) (by omega)
    have h2 : S.L ^ (k + 1) ≤ S.L ^ (k + 1) * M := Nat.le_mul_of_pos_right _ (by
      exact Nat.pos_of_ne_zero (NeZero.ne _))
    omega
  rw [scaleBlocksIn_eq_blocksOver, scaleBlocksIn_eq_blocksOver]
  have key := blocksOver_corr (n₁ := n₁) (n₂ := n₂) (cc := cc) (J := k + 1) hk
    (T₁ := fun j' => {x | j' = j ∧ cubeMap n₁ S.L M K j x ∈ nbhd 1 {y₁}})
    (T₂ := fun j' => {x | j' = j ∧ cubeMap n₂ S.L M K j x ∈ nbhd 1 {y₂}})
    (fun j' x ⟨hj', hq⟩ => by
      subst hj'
      have hnear := near_of_level Hl₁.F.hnn hk hj hX₁ hq
      exact ⟨by omega, ((margin₁ Hl₁ Hl₂ hrem₁ hk Zc₁ Zc₂ hZc₁ hV (r := 1) (m := 2) (by omega)
        (by omega) x hnear).mono hsmall)⟩)
    (fun j' x ⟨hj', hq⟩ => by
      subst hj'
      have hnear := near_of_level Hl₂.F.hnn hk hj hX₂ hq
      exact ⟨by omega, ((margin₂ Hl₁ Hl₂ hrem₂ hk Zc₁ Zc₂ hZc₂ hV (r := 1) (m := 2) (by omega)
        (by omega) x hnear).mono hsmall)⟩)
    (fun j' x₁' x₂' hp => by
      have hQ := cubeNbhd_level_iff Hl₁ Hl₂ hrem₁ hrem₂ hk Zc₁ Zc₂ hZc₁ hZc₂ hV h32₁ h32₂ hR6
        hj hy hX₁ hX₂ hp
      exact and_congr_right fun _ => hQ)
    (fun j' hj' => four_le_block Hl₁.F.hnn hk h32₁ hj')
    (fun j' hj' => four_le_block Hl₂.F.hnn hk h32₂ hj')
  refine psiTildeMulti_iff key.1 key.2.1 ?_ key.2.2
  rintro ⟨j₀, y⟩ _ ⟨j', y'⟩ _ hc
  obtain rfl : j₀ = j' := hc.1
  exact subMultiscaleField_corr hH hcfg (fun p₁ p₂ h => newVars_iff p₁ p₂ h) hk
    (fun j hj => four_le_block Hl₁.F.hnn hk h32₁ hj) (fun j hj => four_le_block Hl₂.F.hnn hk h32₂ hj)
    hout j₀ y y' hc

end Parts

end Balaban.RootFSpine
