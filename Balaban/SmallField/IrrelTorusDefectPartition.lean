/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, GPT-6-Sol
-/
module

public import Balaban.SmallField.IrrelTorusDefectSmallSum

/-!
# The common small-shape region at the origin

The two landed transfer lemmas give both inclusions below their respective geometric
thresholds. Their contrapositives locate unmatched shapes in the large-size tails.
-/

@[expose] public section

namespace Balaban.SmallField.Def6

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField

variable {d L N₁ m₁ k : ℕ} [NeZero L] [NeZero N₁]

/-- An infinite shape that is absent from the fixed torus has infinite-volume covering size
at least the side threshold. -/
theorem dInf_ge_torus_threshold_of_not_liftPolys {P : Consts} {j : ℕ}
    (hd : 0 < d) (hjk : j ≤ k) (hN : L ^ P.m₀ ∣ N₁)
    {X' : Finset (Site d)} (h0 : (0 : Site d) ∈ X')
    (hInf : InfPoly (L := L) (m₁ := m₁) (k := k) P.m₀ j X')
    (hmiss : X' ∉ liftPolys (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P j) :
    (((N₁ * L ^ m₁ * L ^ (k - j) : ℕ) : ℝ) -
      4 * ((L * L ^ (P.m₀ + m₁) : ℕ) : ℝ) - 4) /
        (4 * diamA d L P.m₀ m₁) - 1 ≤ dInf L m₁ k P.m₀ j X' := by
  have hA : 0 < diamA d L P.m₀ m₁ := diamA_pos hd (NeZero.pos L) P.m₀ m₁
  have hs : ¬ 4 * (diamA d L P.m₀ m₁ * (1 + dInf L m₁ k P.m₀ j X') +
      ((L * L ^ (P.m₀ + m₁) : ℕ) : ℝ) + 1) <
      ((N₁ * L ^ m₁ * L ^ (k - j) : ℕ) : ℝ) := by
    intro hs
    exact hmiss (liftPolys_of_infPoly_small hjk hN h0 hInf hs)
  apply (sub_le_iff_le_add).2
  apply (div_le_iff₀ (by positivity : 0 < 4 * diamA d L P.m₀ m₁)).2
  have hle := le_of_not_gt hs
  nlinarith

/-- A fixed-torus polymer which is absent from the infinite family has finite covering size
at least the side threshold. -/
theorem sizeJ_ge_torus_threshold_of_not_infPoly {P : Consts} {j : ℕ}
    (hd : 0 < d) (hjk : j ≤ k) (hN : L ^ P.m₀ ∣ N₁)
    {X' : Finset (Site d)}
    (hFin : X' ∈ liftPolys (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P j)
    (hmiss : ¬ InfPoly (L := L) (m₁ := m₁) (k := k) P.m₀ j X') :
    (((N₁ * L ^ m₁ * L ^ (k - j) : ℕ) : ℝ) -
      4 * ((L * L ^ (P.m₀ + m₁) : ℕ) : ℝ) - 4) /
        (4 * diamA d L P.m₀ m₁) - 1 ≤
      sizeJ (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P.m₀ j
        (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X') := by
  apply sizeJ_ge_torus_threshold_of_not_small hd
  intro hs
  exact hmiss (infPoly_of_liftPolys_small hjk hN hFin hs)

/-- The finite and infinite polymer predicates agree on shapes which meet both covering-size
thresholds. The two thresholds are kept separate because `dInf` is a supremum over a sequence
of tori and equality with `sizeJ` on an arbitrary torus is not yet available. -/
theorem liftPolys_iff_infPoly_of_both_small {P : Consts} {j : ℕ}
    (hjk : j ≤ k) (hN : L ^ P.m₀ ∣ N₁) {X' : Finset (Site d)}
    (h0 : (0 : Site d) ∈ X')
    (hFinSmall : 4 * (diamA d L P.m₀ m₁ *
        (1 + sizeJ (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P.m₀ j
          (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X')) +
        ((L * L ^ (P.m₀ + m₁) : ℕ) : ℝ) + 1) <
      ((N₁ * L ^ m₁ * L ^ (k - j) : ℕ) : ℝ))
    (hInfSmall : 4 * (diamA d L P.m₀ m₁ *
        (1 + dInf L m₁ k P.m₀ j X') +
        ((L * L ^ (P.m₀ + m₁) : ℕ) : ℝ) + 1) <
      ((N₁ * L ^ m₁ * L ^ (k - j) : ℕ) : ℝ)) :
    X' ∈ liftPolys (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P j ↔
      InfPoly (L := L) (m₁ := m₁) (k := k) P.m₀ j X' := by
  constructor
  · intro hFin
    exact infPoly_of_liftPolys_small hjk hN hFin hFinSmall
  · intro hInf
    exact liftPolys_of_infPoly_small hjk hN h0 hInf hInfSmall

open Classical in
/-- A canonical finite common region: filter the finite torus shapes by both quantitative
side thresholds. On that region membership is exactly the infinite polymer condition, with
the root and the two thresholds displayed. -/
theorem exists_common_small_shapes {P : Consts} {j : ℕ}
    (hjk : j ≤ k) (hN : L ^ P.m₀ ∣ N₁) :
    ∃ S : Finset (Finset (Site d)), ∀ X', X' ∈ S ↔
      (0 : Site d) ∈ X' ∧
      InfPoly (L := L) (m₁ := m₁) (k := k) P.m₀ j X' ∧
      4 * (diamA d L P.m₀ m₁ *
        (1 + sizeJ (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P.m₀ j
          (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X')) +
        ((L * L ^ (P.m₀ + m₁) : ℕ) : ℝ) + 1) <
        ((N₁ * L ^ m₁ * L ^ (k - j) : ℕ) : ℝ) ∧
      4 * (diamA d L P.m₀ m₁ * (1 + dInf L m₁ k P.m₀ j X') +
        ((L * L ^ (P.m₀ + m₁) : ℕ) : ℝ) + 1) <
        ((N₁ * L ^ m₁ * L ^ (k - j) : ℕ) : ℝ) := by
  refine ⟨(liftPolys_finite (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
    (k := k) P j).toFinset.filter (fun X' =>
      4 * (diamA d L P.m₀ m₁ *
        (1 + sizeJ (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P.m₀ j
          (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X')) +
        ((L * L ^ (P.m₀ + m₁) : ℕ) : ℝ) + 1) <
        ((N₁ * L ^ m₁ * L ^ (k - j) : ℕ) : ℝ) ∧
      4 * (diamA d L P.m₀ m₁ * (1 + dInf L m₁ k P.m₀ j X') +
        ((L * L ^ (P.m₀ + m₁) : ℕ) : ℝ) + 1) <
        ((N₁ * L ^ m₁ * L ^ (k - j) : ℕ) : ℝ)), ?_⟩
  intro X'
  simp only [Finset.mem_filter, Set.Finite.mem_toFinset]
  constructor
  · rintro ⟨hFin, hFinSmall, hInfSmall⟩
    exact ⟨hFin.1, infPoly_of_liftPolys_small hjk hN hFin hFinSmall,
      hFinSmall, hInfSmall⟩
  · rintro ⟨h0, hInf, hFinSmall, hInfSmall⟩
    exact ⟨liftPolys_of_infPoly_small hjk hN h0 hInf hInfSmall,
      hFinSmall, hInfSmall⟩

end Balaban.SmallField.Def6
