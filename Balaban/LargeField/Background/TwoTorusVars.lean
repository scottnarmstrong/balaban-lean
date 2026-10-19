/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Background.TwoTorusCubeLift

/-!
# The variables of two corresponding localized histories

For corresponding localized histories (`HistCorr`), configurations (`CfgCorr`) and outputs
(`OutCorr`), the fields read from them agree at corresponding blocks: `subVarField`,
`subFluctVarField`, `subFluctField`, `subMultiscaleField` (`MultiCorr`). The block conditions
`BlockSub`, `CubeSub` correspond (`blockSub_corr`, `cubeSub_corr`).
-/

@[expose] public section

namespace Balaban.RootFSpine

open Balaban Balaban.LargeField RegionHistory

section Sub

variable {S : Setting} {n₁ n₂ : ℕ → ℕ} [∀ k, NeZero (n₁ k)] [∀ k, NeZero (n₂ k)] {M K : ℕ}
  [NeZero M] [NeZero S.L] {cc : Fin S.d → ℤ}

theorem blockSub_corr {j : ℕ} (hj : j ≤ K) (hq₁ : 4 ≤ M * n₁ K * S.L ^ (K - j))
    (hq₂ : 4 ≤ M * n₂ K * S.L ^ (K - j)) {B₁ : Set (Torus S.d (M * n₁ K * S.L ^ K))}
    {B₂ : Set (Torus S.d (M * n₂ K * S.L ^ K))} (hB : SetIff cc B₁ B₂)
    {y₁ : BlockAt S n₁ M K j} {y₂ : BlockAt S n₂ M K j} (h : BlkCorr cc j j y₁ y₂) :
    BlockSub (S := S) (n := n₁) (M := M) (K := K) j y₁ B₁ ↔
      BlockSub (S := S) (n := n₂) (M := M) (K := K) j y₂ B₂ := by
  obtain ⟨w, hw, rfl, rfl⟩ := (blkCorr_iff_ccorr hj).1 h
  exact bsub_corr_iff (Nat.pos_of_ne_zero (NeZero.ne _)) (Multiscale.side_eq hj)
    (Multiscale.side_eq hj) hq₁ hq₂ hB hw

theorem cubeSub_corr (hnn₁ : ∀ i, i < K → n₁ i = S.L * n₁ (i + 1))
    (hnn₂ : ∀ i, i < K → n₂ i = S.L * n₂ (i + 1)) {j : ℕ} (hj : j ≤ K) (hq₁ : 4 ≤ n₁ j)
    (hq₂ : 4 ≤ n₂ j) {B₁ : Set (Torus S.d (M * n₁ K * S.L ^ K))}
    {B₂ : Set (Torus S.d (M * n₂ K * S.L ^ K))} (hB : SetIff cc B₁ B₂) {y₁ : Torus S.d (n₁ j)}
    {y₂ : Torus S.d (n₂ j)} (h : CubeCorr (M := M) (K := K) cc j y₁ y₂) :
    CubeSub (S := S) (n := n₁) M K j y₁ B₁ ↔ CubeSub (S := S) (n := n₂) M K j y₂ B₂ := by
  obtain ⟨w, hw, rfl, rfl⟩ := (cubeCorr_iff_ccorr hnn₁ hnn₂ hj).1 h
  exact bsub_corr_iff (Nat.mul_pos (pow_pos (Nat.pos_of_ne_zero (NeZero.ne _)) _)
    (Nat.pos_of_ne_zero (NeZero.ne _))) (Balaban.LargeField.fine_eq hnn₁ hj)
    (Balaban.LargeField.fine_eq hnn₂ hj) hq₁ hq₂ hB hw

end Sub

section HC

variable {S : Setting} {n₁ n₂ : ℕ → ℕ} {M K : ℕ} {cc : Fin S.d → ℤ}
  {a₁ : LocalHistory S n₁ M K} {a₂ : LocalHistory S n₂ M K}

theorem HistCorr.Z_corr (h : HistCorr cc a₁ a₂) (j : ℕ) : SetCorr cc (a₁.Z j) (a₂.Z j) := (h j).1

theorem HistCorr.Omega_corr (h : HistCorr cc a₁ a₂) (j : ℕ) :
    SetCorr cc (a₁.Omega j) (a₂.Omega j) := (h j).2.2.2.2.2.2.1

theorem HistCorr.OmegaDD_corr (h : HistCorr cc a₁ a₂) (j : ℕ) :
    SetCorr cc (a₁.OmegaDD j) (a₂.OmegaDD j) := (h j).2.2.2.2.2.2.2


theorem HistCorr.varSet_iff (h : HistCorr cc a₁ a₂) (j : ℕ) (κ : VarKind) :
    SetIff cc (varSet a₁ j κ) (varSet a₂ j κ) := by
  cases κ
  · exact (h.Z_corr (j + 1)).setIff.diff (h.Omega_corr j).setIff
  · exact (h.Omega_corr j).setIff.diff (h.OmegaDD_corr j).setIff

theorem HistCorr.lhOmega_iff (h : HistCorr cc a₁ a₂) (k j : ℕ) :
    SetIff cc (lhOmega a₁ k j) (lhOmega a₂ k j) :=
  (h.Omega_corr (j - 1)).setIff.union (h.Z_corr k).setIff.compl

end HC

section Fields

variable {S : Setting} {n₁ n₂ : ℕ → ℕ} [∀ k, NeZero (n₁ k)] [∀ k, NeZero (n₂ k)] {M K N : ℕ}
  [NeZero M] [NeZero S.L] {cc : Fin S.d → ℤ} {a₁ : LocalHistory S n₁ M K}
  {a₂ : LocalHistory S n₂ M K}

variable {k j : ℕ} {A₁ : Set (InternalVars a₁ k)} {A₂ : Set (InternalVars a₂ k)}
  {x₁ : SubCfg N a₁ k A₁} {x₂ : SubCfg N a₂ k A₂}

open Classical in
theorem subVar_corr_core (κ : VarKind) (hH : HistCorr cc a₁ a₂) (hcfg : CfgCorr cc x₁ x₂)
    (hA : ∀ p₁ p₂, VarCorr cc p₁ p₂ → (p₁ ∈ A₁ ↔ p₂ ∈ A₂)) (hj : j ≤ K)
    (hq₁ : 4 ≤ M * n₁ K * S.L ^ (K - j)) (hq₂ : 4 ≤ M * n₂ K * S.L ^ (K - j))
    {y₁ : BlockAt S n₁ M K j} {y₂ : BlockAt S n₂ M K j} (h : BlkCorr cc j j y₁ y₂) :
    (if hh : ∃ hj : j < k, ∃ hb : BlockSub (S := S) (n := n₁) (M := M) (K := K) j y₁
        (varSet a₁ j κ), mkVar a₁ k j κ y₁ hj hb ∈ A₁ then
      VarVal.toEuc (x₁ ⟨mkVar a₁ k j κ y₁ hh.1 hh.2.1, hh.2.2⟩) else 0) =
    (if hh : ∃ hj : j < k, ∃ hb : BlockSub (S := S) (n := n₂) (M := M) (K := K) j y₂
        (varSet a₂ j κ), mkVar a₂ k j κ y₂ hj hb ∈ A₂ then
      VarVal.toEuc (x₂ ⟨mkVar a₂ k j κ y₂ hh.1 hh.2.1, hh.2.2⟩) else 0) := by
  have hsub := blockSub_corr hj hq₁ hq₂ (hH.varSet_iff j κ) h
  by_cases hex : ∃ hj : j < k, ∃ hb : BlockSub (S := S) (n := n₁) (M := M) (K := K) j y₁
      (varSet a₁ j κ), mkVar a₁ k j κ y₁ hj hb ∈ A₁
  · obtain ⟨hjk, hb₁, hm₁⟩ := hex
    have hb₂ := hsub.1 hb₁
    have hm₂ : mkVar a₂ k j κ y₂ hjk hb₂ ∈ A₂ := (hA _ _ ⟨rfl, h⟩).1 hm₁
    have hex₂ : ∃ hj : j < k, ∃ hb : BlockSub (S := S) (n := n₂) (M := M) (K := K) j y₂
        (varSet a₂ j κ), mkVar a₂ k j κ y₂ hj hb ∈ A₂ := ⟨hjk, hb₂, hm₂⟩
    have hex₁ : ∃ hj : j < k, ∃ hb : BlockSub (S := S) (n := n₁) (M := M) (K := K) j y₁
        (varSet a₁ j κ), mkVar a₁ k j κ y₁ hj hb ∈ A₁ := ⟨hjk, hb₁, hm₁⟩
    simp only [hex₁, hex₂, ↓reduceDIte]
    exact hcfg ⟨_, hm₁⟩ ⟨_, hm₂⟩ ⟨rfl, h⟩
  · have hex₂ : ¬ ∃ hj : j < k, ∃ hb : BlockSub (S := S) (n := n₂) (M := M) (K := K) j y₂
        (varSet a₂ j κ), mkVar a₂ k j κ y₂ hj hb ∈ A₂ := by
      rintro ⟨hjk, hb₂, hm₂⟩
      exact hex ⟨hjk, hsub.2 hb₂, (hA _ _ ⟨rfl, h⟩).2 hm₂⟩
    simp only [hex, hex₂, ↓reduceDIte]

theorem subVarField_corr (hH : HistCorr cc a₁ a₂) (hcfg : CfgCorr cc x₁ x₂)
    (hA : ∀ p₁ p₂, VarCorr cc p₁ p₂ → (p₁ ∈ A₁ ↔ p₂ ∈ A₂)) (hj : j ≤ K)
    (hq₁ : 4 ≤ M * n₁ K * S.L ^ (K - j)) (hq₂ : 4 ≤ M * n₂ K * S.L ^ (K - j))
    {y₁ : BlockAt S n₁ M K j} {y₂ : BlockAt S n₂ M K j} (h : BlkCorr cc j j y₁ y₂) :
    subVarField N x₁ j y₁ = subVarField N x₂ j y₂ :=
  subVar_corr_core .large hH hcfg hA hj hq₁ hq₂ h

theorem subFluctVarField_corr (hH : HistCorr cc a₁ a₂) (hcfg : CfgCorr cc x₁ x₂)
    (hA : ∀ p₁ p₂, VarCorr cc p₁ p₂ → (p₁ ∈ A₁ ↔ p₂ ∈ A₂)) (hj : j ≤ K)
    (hq₁ : 4 ≤ M * n₁ K * S.L ^ (K - j)) (hq₂ : 4 ≤ M * n₂ K * S.L ^ (K - j))
    {y₁ : BlockAt S n₁ M K j} {y₂ : BlockAt S n₂ M K j} (h : BlkCorr cc j j y₁ y₂) :
    subFluctVarField N x₁ j y₁ = subFluctVarField N x₂ j y₂ :=
  subVar_corr_core .fluct hH hcfg hA hj hq₁ hq₂ h

theorem subFluctField_corr (hH : HistCorr cc a₁ a₂) (hcfg : CfgCorr cc x₁ x₂)
    (hA : ∀ p₁ p₂, VarCorr cc p₁ p₂ → (p₁ ∈ A₁ ↔ p₂ ∈ A₂))
    (hj : j ≤ K) (hq₁ : 4 ≤ M * n₁ K * S.L ^ (K - j)) (hq₂ : 4 ≤ M * n₂ K * S.L ^ (K - j))
    {y₁ : BlockAt S n₁ M K j} {y₂ : BlockAt S n₂ M K j} (h : BlkCorr cc j j y₁ y₂) :
    subFluctField N a₁ k x₁ j y₁ = subFluctField N a₂ k x₂ j y₂ :=
  subFluctVarField_corr hH hcfg hA hj hq₁ hq₂ h

open Classical in
/-- **The multiscale field of corresponding configurations agrees at corresponding blocks.** -/
theorem subMultiscaleField_corr (hH : HistCorr cc a₁ a₂) (hcfg : CfgCorr cc x₁ x₂)
    (hA : ∀ p₁ p₂, VarCorr cc p₁ p₂ → (p₁ ∈ A₁ ↔ p₂ ∈ A₂)) (hkK : k ≤ K)
    (hq₁ : ∀ j, j ≤ k → 4 ≤ M * n₁ K * S.L ^ (K - j))
    (hq₂ : ∀ j, j ≤ k → 4 ≤ M * n₂ K * S.L ^ (K - j)) {V₁ : Set (BlockAt S n₁ M K k)}
    {V₂ : Set (BlockAt S n₂ M K k)} {o₁ : OutConfig N V₁} {o₂ : OutConfig N V₂}
    (hout : OutCorr cc k o₁ o₂) (j : ℕ) (y₁ : BlockAt S n₁ M K j) (y₂ : BlockAt S n₂ M K j)
    (h : BlkCorr cc j j y₁ y₂) :
    subMultiscaleField N a₁ k V₁ x₁ o₁ j y₁ = subMultiscaleField N a₂ k V₂ x₂ o₂ j y₂ := by
  unfold subMultiscaleField
  by_cases hjk : j < k
  · have hjK : j ≤ K := by omega
    have hjk' : j ≤ k := by omega
    have hcond : (j = 0 ∨ BlockSub (S := S) (n := n₁) (M := M) (K := K) j y₁ (lhOmega a₁ k j)) ↔
        (j = 0 ∨ BlockSub (S := S) (n := n₂) (M := M) (K := K) j y₂ (lhOmega a₂ k j)) :=
      or_congr_right (blockSub_corr hjK (hq₁ j hjk') (hq₂ j hjk') (hH.lhOmega_iff k j) h)
    simp only [hjk, ↓reduceIte]
    exact if_congr hcond (subVarField_corr hH hcfg hA hjK (hq₁ j hjk') (hq₂ j hjk') h) rfl
  · by_cases hjk' : j = k
    · subst hjk'
      have hjK : j ≤ K := hkK
      have hcond : (j = 0 ∨ BlockSub (S := S) (n := n₁) (M := M) (K := K) j y₁
            (lhOmega a₁ j j)) ↔
          (j = 0 ∨ BlockSub (S := S) (n := n₂) (M := M) (K := K) j y₂ (lhOmega a₂ j j)) :=
        or_congr_right (blockSub_corr hjK (hq₁ j le_rfl) (hq₂ j le_rfl) (hH.lhOmega_iff j j) h)
      simp only [hjk, ↓reduceIte, ↓reduceDIte]
      exact if_congr hcond (hout y₁ y₂ h) rfl
    · simp only [hjk, hjk', ↓reduceIte, ↓reduceDIte]

end Fields

end Balaban.RootFSpine
