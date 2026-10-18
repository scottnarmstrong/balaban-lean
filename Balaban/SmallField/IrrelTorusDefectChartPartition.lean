/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, GPT-6-Sol
-/
module

public import Balaban.SmallField.IrrelTorusDefectInverse
public import Balaban.SmallField.IrrelTorusDefectCoordSmall

/-!
# A single centred-chart partition for finite and infinite shape families

One `ZSmall` predicate defines the common shapes. A finite shape outside it has large `sizeJ`;
an infinite shape outside it has large `dInf`. The partition does not require identifying
`dInf`, a supremum over all good sequence tori, with the covering size on one fixed torus.
-/

@[expose] public section

namespace Balaban.SmallField.Def6

open Balaban Balaban.Multiscale Balaban.SmallField

variable {d L N₁ m₁ k : ℕ} [NeZero L] [NeZero N₁]

open Classical in
/-- The common centred-chart shapes and quantitative radius bounds for both excluded
families. Both lower bounds use the same side threshold, in each family's own radius. -/
theorem exists_common_chart_shapes {P : Consts} {j : ℕ}
    (hd : 0 < d) (hjk : j ≤ k) (hN : L ^ P.m₀ ∣ N₁) :
    ∃ S : Finset (Finset (Site d)),
      (∀ X', X' ∈ S ↔
        (0 : Site d) ∈ X' ∧
        InfPoly (L := L) (m₁ := m₁) (k := k) P.m₀ j X' ∧
        ZSmall (N₁ * L ^ m₁ * L ^ (k - j))
          (L * L ^ (P.m₀ + m₁)) X') ∧
      (∀ X', X' ∈ liftPolys (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P j →
        X' ∉ S →
        (((N₁ * L ^ m₁ * L ^ (k - j) : ℕ) : ℝ) -
          4 * ((L * L ^ (P.m₀ + m₁) : ℕ) : ℝ) - 4) /
            (4 * diamA d L P.m₀ m₁) - 1 ≤
          sizeJ (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P.m₀ j
            (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X')) ∧
      (∀ X', (0 : Site d) ∈ X' →
        InfPoly (L := L) (m₁ := m₁) (k := k) P.m₀ j X' →
        X' ∉ S →
        (((N₁ * L ^ m₁ * L ^ (k - j) : ℕ) : ℝ) -
          4 * ((L * L ^ (P.m₀ + m₁) : ℕ) : ℝ) - 4) /
            (4 * diamA d L P.m₀ m₁) - 1 ≤
          dInf L m₁ k P.m₀ j X') := by
  let S : Finset (Finset (Site d)) :=
    (liftPolys_finite (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (k := k) P j).toFinset.filter (fun X' =>
        ZSmall (N₁ * L ^ m₁ * L ^ (k - j))
          (L * L ^ (P.m₀ + m₁)) X')
  have hmem : ∀ X', X' ∈ S ↔
      (0 : Site d) ∈ X' ∧
      InfPoly (L := L) (m₁ := m₁) (k := k) P.m₀ j X' ∧
      ZSmall (N₁ * L ^ m₁ * L ^ (k - j))
        (L * L ^ (P.m₀ + m₁)) X' := by
    intro X'
    simp only [S, Finset.mem_filter, Set.Finite.mem_toFinset]
    constructor
    · rintro ⟨hFin, hs⟩
      exact ⟨hFin.1, infPoly_of_zsmall_of_isPolyDom hjk hN hs hFin.2.2, hs⟩
    · rintro ⟨h0, hInf, hs⟩
      obtain ⟨hnw, hpd⟩ := fixedPoly_of_infPoly_zsmall hjk hN hInf hs
      exact ⟨⟨h0, hnw, hpd⟩, hs⟩
  refine ⟨S, hmem, ?_, ?_⟩
  · intro X' hFin hmiss
    have hnotSmall : ¬ 4 * (diamA d L P.m₀ m₁ *
        (1 + sizeJ (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P.m₀ j
          (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X')) +
        ((L * L ^ (P.m₀ + m₁) : ℕ) : ℝ) + 1) <
        ((N₁ * L ^ m₁ * L ^ (k - j) : ℕ) : ℝ) := by
      intro hs
      have hzs := zsmall_of_liftPolys_small hjk hFin hs
      exact hmiss ((hmem X').2 ⟨hFin.1,
        infPoly_of_zsmall_of_isPolyDom hjk hN hzs hFin.2.2, hzs⟩)
    exact side_threshold_le (diamA_pos hd (NeZero.pos L) P.m₀ m₁) hnotSmall
  · intro X' h0 hInf hmiss
    have hnotSmall : ¬ 4 * (diamA d L P.m₀ m₁ *
        (1 + dInf L m₁ k P.m₀ j X') +
        ((L * L ^ (P.m₀ + m₁) : ℕ) : ℝ) + 1) <
        ((N₁ * L ^ m₁ * L ^ (k - j) : ℕ) : ℝ) := by
      intro hs
      exact hmiss ((hmem X').2 ⟨h0, hInf,
        zsmall_of_infPoly_small hjk h0 hInf hs⟩)
    exact side_threshold_le (diamA_pos hd (NeZero.pos L) P.m₀ m₁) hnotSmall

end Balaban.SmallField.Def6
