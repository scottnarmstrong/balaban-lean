/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Background.TwoTorusVars
public import Balaban.LargeField.Characteristic.OperatorDomain

/-!
# The conditions `Ψ̃(Y; δ)` on two tori

`PsiTildeMulti ψ Y δ` for sets `Y₁`, `Y₂` of blocks of two tori that correspond (`BlkCorr`), with
values and adjacency of blocks that correspond, are equivalent
(`psiTildeMulti_iff`).
-/

@[expose] public section

namespace Balaban.RootFSpine

open Balaban Balaban.LargeField

section PsiTilde

variable {S : Setting} {n₁ n₂ : ℕ → ℕ} [∀ k, NeZero (n₁ k)] [∀ k, NeZero (n₂ k)] {M K N : ℕ}
  [NeZero M] [NeZero S.L] {cc : Fin S.d → ℤ}

omit [∀ k, NeZero (n₁ k)] [∀ k, NeZero (n₂ k)] [NeZero M] [NeZero S.L] in
theorem psiTildeMulti_iff {ψ₁ : MultiField S n₁ M K N} {ψ₂ : MultiField S n₂ M K N}
    {Y₁ : Set (BlockPt S n₁ M K)} {Y₂ : Set (BlockPt S n₂ M K)} {δ : ℝ}
    (h1 : ∀ b ∈ Y₁, ∃ b' ∈ Y₂, BlkCorr cc b.1 b'.1 b.2 b'.2)
    (h2 : ∀ b' ∈ Y₂, ∃ b ∈ Y₁, BlkCorr cc b.1 b'.1 b.2 b'.2)
    (hψ : ∀ b ∈ Y₁, ∀ b' ∈ Y₂, BlkCorr cc b.1 b'.1 b.2 b'.2 → ψ₁ b.1 b.2 = ψ₂ b'.1 b'.2)
    (hadj : ∀ b₁ ∈ Y₁, ∀ b₁' ∈ Y₁, ∀ b₂ ∈ Y₂, ∀ b₂' ∈ Y₂, BlkCorr cc b₁.1 b₂.1 b₁.2 b₂.2 →
      BlkCorr cc b₁'.1 b₂'.1 b₁'.2 b₂'.2 → (BlockAdj b₁ b₁' ↔ BlockAdj b₂ b₂')) :
    PsiTildeMulti ψ₁ Y₁ δ ↔ PsiTildeMulti ψ₂ Y₂ δ := by
  constructor
  · rintro ⟨hr1, hr2⟩
    refine ⟨fun b₂ hb₂ b₂' hb₂' hl hadj₂ => ?_, fun b₂ hb₂ => ?_⟩
    · obtain ⟨b₁, hb₁, hc⟩ := h2 b₂ hb₂
      obtain ⟨b₁', hb₁', hc'⟩ := h2 b₂' hb₂'
      have e1 : b₁.1 = b₂.1 := hc.1
      have e2 : b₁'.1 = b₂'.1 := hc'.1
      have := hr1 b₁ hb₁ b₁' hb₁' (by rw [e1, e2]; exact hl)
        ((hadj b₁ hb₁ b₁' hb₁' b₂ hb₂ b₂' hb₂' hc hc').2 hadj₂)
      rwa [hψ b₁ hb₁ b₂ hb₂ hc, hψ b₁' hb₁' b₂' hb₂' hc'] at this
    · obtain ⟨b₁, hb₁, hc⟩ := h2 b₂ hb₂
      have := hr2 b₁ hb₁
      rwa [hψ b₁ hb₁ b₂ hb₂ hc] at this
  · rintro ⟨hr1, hr2⟩
    refine ⟨fun b₁ hb₁ b₁' hb₁' hl hadj₁ => ?_, fun b₁ hb₁ => ?_⟩
    · obtain ⟨b₂, hb₂, hc⟩ := h1 b₁ hb₁
      obtain ⟨b₂', hb₂', hc'⟩ := h1 b₁' hb₁'
      have e1 : b₁.1 = b₂.1 := hc.1
      have e2 : b₁'.1 = b₂'.1 := hc'.1
      have := hr1 b₂ hb₂ b₂' hb₂' (by rw [← e1, ← e2]; exact hl)
        ((hadj b₁ hb₁ b₁' hb₁' b₂ hb₂ b₂' hb₂' hc hc').1 hadj₁)
      rwa [← hψ b₁ hb₁ b₂ hb₂ hc, ← hψ b₁' hb₁' b₂' hb₂' hc'] at this
    · obtain ⟨b₂, hb₂, hc⟩ := h1 b₁ hb₁
      have := hr2 b₂ hb₂
      rwa [← hψ b₁ hb₁ b₂ hb₂ hc] at this

end PsiTilde

end Balaban.RootFSpine
