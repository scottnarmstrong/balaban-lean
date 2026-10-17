/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, GPT-6-Sol
-/
module

public import Balaban.SmallField.IrrelTorusDefectRawSymm

/-!
# Corrected finite-volume coordinate weights for the raw matrix

At an antipodal torus displacement the shortest signed representative has two choices.
Assigning zero at that tie gives an odd weight, so reflection cancels mixed matrix entries
exactly on each finite torus. The weight agrees with the integer displacement on small shapes.
-/

@[expose] public section

namespace Balaban.SmallField.Def6

open Balaban Balaban.Multiscale Balaban.Localization Balaban.SmallField Filter Metric Set

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ} {P : Consts}
  {β ν a : ℕ → ℝ} {Ek : ℝ} {Tm : Terms d L N₁ m₁ k N ϱ}
  {ρd : (CTorus d L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) →
    (CTorus d L N₁ m₁ k → Fin N → ℝ) → ℝ} {j : ℕ} {ρ : ℝ}

/-- The corrected and rescaled signed torus coordinate is odd. -/
theorem corrected_weight_odd (x : ZMod (N₁ * L ^ m₁ * L ^ k)) :
    (((if 2 * (-x).val = N₁ * L ^ m₁ * L ^ k then (0 : ℤ)
       else (-x).valMinAbs) : ℂ) / ((L : ℂ) ^ j)) =
      -(((if 2 * x.val = N₁ * L ^ m₁ * L ^ k then (0 : ℤ)
       else x.valMinAbs) : ℂ) / ((L : ℂ) ^ j)) := by
  have h := corrected_valMinAbs_neg x
  have h' := congrArg (fun t : ℤ => (t : ℂ)) h
  simp only [Int.cast_ite, Int.cast_zero, Int.cast_neg] at h'
  simp only [Int.cast_zero]
  rw [h']
  ring

/-- The base point of an integer block is aligned to its scale lattice. -/
theorem aligned_blockPt (hjk : j ≤ k) (y : Site d) :
    Aligned (L ^ j) (blockPt (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j y) := by
  have hb : blockPt (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j y =
      ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j y := by
    funext ξ
    simp only [blockPt, ibase]
    ring_nf
  rw [hb]
  exact ibase_aligned hjk y

open Classical in
/-- The weighted shape expansion turns finite reflection symmetry into exact
off-diagonal cancellation of the polymer tensor sum. -/
theorem LiftCtx.weighted_shape_offdiag_zero (ctx : LiftCtx P β ν a Tm ρd Ek j ρ)
    (hN : L ^ P.m₀ ∣ N₁) (i₀ i₁ : Fin N) (y : Site d)
    (hyu : unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (blockPt j y) = y)
    (q : ZMod (N₁ * L ^ m₁ * L ^ k) → ℂ) (hq : ∀ x, q (-x) = -q x)
    (μ η : Fin d) (hne : η ≠ μ) :
    (∑ᶠ X' ∈ {X' : Finset (Site d) | y ∈ X' ∧ NonWind L N₁ m₁ k j X' ∧
        IsPolyDom P.m₀ j (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X')},
      ∑ z : ↥X', ∑ z' : ↥X',
        tensB i₀ i₁ (nuIdeal L k (ν k) j) X'
          (EauxC Tm j i₀ (nuIdeal L k (ν k) j) y X') z z' *
          (q ((ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j z.1 -
            ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j z'.1) μ) *
            q ((ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j z.1 -
              ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j z'.1) η))) = 0 := by
  have hyalign := aligned_blockPt (L := L) (N₁ := N₁) (m₁ := m₁) ctx.jk y
  rw [← ctx.weightedHessian_shapes_centre hN (i₀ := i₀) (i₁ := i₁) y hyu
    (fun u v => q ((u - v) μ) * q ((u - v) η))]
  exact ctx.weightedHessian_pair_offdiag_zero_at i₀ i₁ hyalign q hq μ η hne

open Classical in
/-- The same shape expansion identifies every two diagonal entries on a finite torus. -/
theorem LiftCtx.weighted_shape_diag_eq (ctx : LiftCtx P β ν a Tm ρd Ek j ρ)
    (hN : L ^ P.m₀ ∣ N₁) (i₀ i₁ : Fin N) (y : Site d)
    (hyu : unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (blockPt j y) = y)
    (q : ZMod (N₁ * L ^ m₁ * L ^ k) → ℂ) (μ η : Fin d) :
    (∑ᶠ X' ∈ {X' : Finset (Site d) | y ∈ X' ∧ NonWind L N₁ m₁ k j X' ∧
        IsPolyDom P.m₀ j (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X')},
      ∑ z : ↥X', ∑ z' : ↥X',
        tensB i₀ i₁ (nuIdeal L k (ν k) j) X'
          (EauxC Tm j i₀ (nuIdeal L k (ν k) j) y X') z z' *
          q ((ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j z.1 -
            ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j z'.1) μ) ^ 2) =
    (∑ᶠ X' ∈ {X' : Finset (Site d) | y ∈ X' ∧ NonWind L N₁ m₁ k j X' ∧
        IsPolyDom P.m₀ j (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X')},
      ∑ z : ↥X', ∑ z' : ↥X',
        tensB i₀ i₁ (nuIdeal L k (ν k) j) X'
          (EauxC Tm j i₀ (nuIdeal L k (ν k) j) y X') z z' *
          q ((ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j z.1 -
            ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j z'.1) η) ^ 2) := by
  have hyalign := aligned_blockPt (L := L) (N₁ := N₁) (m₁ := m₁) ctx.jk y
  rw [← ctx.weightedHessian_shapes_centre hN (i₀ := i₀) (i₁ := i₁) y hyu
      (fun u v => q ((u - v) μ) ^ 2),
    ← ctx.weightedHessian_shapes_centre hN (i₀ := i₀) (i₁ := i₁) y hyu
      (fun u v => q ((u - v) η) ^ 2)]
  exact ctx.weightedHessian_pair_diag_eq_at i₀ i₁ hyalign q μ η

section Limit

variable {Ek' : ℕ → ℝ}
  {Tm' : ∀ (N₁ : ℕ) [NeZero N₁], Terms d L N₁ m₁ k N ϱ}
  {ρd' : ∀ (N₁ : ℕ) [NeZero N₁], (CTorus d L N₁ m₁ k → Fin N → ℝ) →
    (Fin N → ℝ) → (CTorus d L N₁ m₁ k → Fin N → ℝ) → ℝ}

omit [NeZero N₁] in
/-- The corrected finite-volume weight converges entrywise to the raw integer matrix
weight. On small shapes this is exact; on all shapes its norm obeys the Cauchy bound. -/
theorem corrected_pair_tendsto (hF : IsSFFamily P β ν a Tm' ρd' Ek')
    (hn : MomNum d L N k j ϱ P) (i₀ i₁ : Fin N) (y : Site d) (μ η : Fin d) :
    let qN : (n : ℕ) → ZMod (torusSeq L P.m₀ n * L ^ m₁ * L ^ k) → ℂ :=
      fun n =>
        haveI : NeZero (torusSeq L P.m₀ n * L ^ m₁ * L ^ k) := ⟨by
          have := torusSeq_ne_zero (L := L) P.m₀ n
          have := NeZero.ne L
          positivity⟩
        fun x => ((if 2 * x.val = torusSeq L P.m₀ n * L ^ m₁ * L ^ k
          then (0 : ℤ) else x.valMinAbs) : ℂ) / ((L : ℂ) ^ j)
    Tendsto
      (fun n => ∑ᶠ X' ∈ ShAt (d := d) L m₁ k P.m₀ j y n,
        haveI : NeZero (torusSeq L P.m₀ n) := ⟨torusSeq_ne_zero P.m₀ n⟩
        ∑ z : ↥X', ∑ z' : ↥X',
          tensB i₀ i₁ (nuIdeal L k (ν k) j) X'
            (EauxC (Tm' (torusSeq L P.m₀ n)) j i₀ (nuIdeal L k (ν k) j) y X') z z' *
          (qN n ((ibase (L := L) (N₁ := torusSeq L P.m₀ n) (m₁ := m₁) (k := k) j z.1 -
            ibase (L := L) (N₁ := torusSeq L P.m₀ n) (m₁ := m₁) (k := k) j z'.1) μ) *
           qN n ((ibase (L := L) (N₁ := torusSeq L P.m₀ n) (m₁ := m₁) (k := k) j z.1 -
            ibase (L := L) (N₁ := torusSeq L P.m₀ n) (m₁ := m₁) (k := k) j z'.1) η))) atTop
      (nhds (∑' X' : Finset (Site d),
        ∑ z : ↥X', ∑ z' : ↥X',
          tensB i₀ i₁ (nuIdeal L k (ν k) j) X'
            (GE P β ν a Tm' j i₀ (nuIdeal L k (ν k) j) y X') z z' *
          (((z.1 μ - z'.1 μ : ℤ) : ℂ) * (((z.1 η - z'.1 η : ℤ) : ℂ))))) := by
  apply weighted_pair_tendsto_var hF hn i₀ i₁ y
    (fun n X' z z' =>
      haveI : NeZero (torusSeq L P.m₀ n) := ⟨torusSeq_ne_zero P.m₀ n⟩
      let q : ZMod (torusSeq L P.m₀ n * L ^ m₁ * L ^ k) → ℂ := fun x =>
        ((if 2 * x.val = torusSeq L P.m₀ n * L ^ m₁ * L ^ k then (0 : ℤ)
          else x.valMinAbs) : ℂ) / ((L : ℂ) ^ j)
      q ((ibase (L := L) (N₁ := torusSeq L P.m₀ n) (m₁ := m₁) (k := k) j z.1 -
        ibase (L := L) (N₁ := torusSeq L P.m₀ n) (m₁ := m₁) (k := k) j z'.1) μ) *
      q ((ibase (L := L) (N₁ := torusSeq L P.m₀ n) (m₁ := m₁) (k := k) j z.1 -
        ibase (L := L) (N₁ := torusSeq L P.m₀ n) (m₁ := m₁) (k := k) j z'.1) η))
    (fun _ z z' => (((z.1 μ - z'.1 μ : ℤ) : ℂ) *
      (((z.1 η - z'.1 η : ℤ) : ℂ))))
  · intro n X' hy hgood hsz z z'
    have hμ := pair_small_of_tauY hn.hjk hy hgood hsz z.2 z'.2 μ
    have hη := pair_small_of_tauY hn.hjk hy hgood hsz z.2 z'.2 η
    simp only [corrected_ibase_sub_of_small hn.hjk z.1 z'.1 μ hμ,
      corrected_ibase_sub_of_small hn.hjk z.1 z'.1 η hη]
  · intro n X' z z'
    exact norm_corrected_pair_le_sq z.1 z'.1 μ η
  · intro X' z z'
    exact norm_pair_coord_mul_le_sq z.1 z'.1 μ η

omit [NeZero N₁] in
/-- Every torus in the stabilizing sequence has an exactly vanishing corrected mixed
pair sum, as soon as the integer centre has its expected block lift. -/
theorem corrected_pair_sum_offdiag_zero (hF : IsSFFamily P β ν a Tm' ρd' Ek')
    (hn : MomNum d L N k j ϱ P) (i₀ i₁ : Fin N) (y : Site d)
    (μ η : Fin d) (hne : η ≠ μ) (n : ℕ)
    (hyu : unlift (L := L) (N₁ := torusSeq L P.m₀ n) (m₁ := m₁) (k := k) j
      (blockPt j y) = y) :
    let q : ZMod (torusSeq L P.m₀ n * L ^ m₁ * L ^ k) → ℂ :=
      fun x => ((if 2 * x.val = torusSeq L P.m₀ n * L ^ m₁ * L ^ k
        then (0 : ℤ) else x.valMinAbs) : ℂ) / ((L : ℂ) ^ j)
    (∑ᶠ X' ∈ ShAt (d := d) L m₁ k P.m₀ j y n,
      haveI : NeZero (torusSeq L P.m₀ n) := ⟨torusSeq_ne_zero P.m₀ n⟩
      ∑ z : ↥X', ∑ z' : ↥X',
        tensB i₀ i₁ (nuIdeal L k (ν k) j) X'
          (EauxC (Tm' (torusSeq L P.m₀ n)) j i₀ (nuIdeal L k (ν k) j) y X') z z' *
        (q ((ibase (L := L) (N₁ := torusSeq L P.m₀ n) (m₁ := m₁) (k := k) j z.1 -
          ibase (L := L) (N₁ := torusSeq L P.m₀ n) (m₁ := m₁) (k := k) j z'.1) μ) *
         q ((ibase (L := L) (N₁ := torusSeq L P.m₀ n) (m₁ := m₁) (k := k) j z.1 -
          ibase (L := L) (N₁ := torusSeq L P.m₀ n) (m₁ := m₁) (k := k) j z'.1) η))) = 0 := by
  have ctx := hF.ctxSeq hn i₀ n
  let q : ZMod (torusSeq L P.m₀ n * L ^ m₁ * L ^ k) → ℂ :=
    fun x => ((if 2 * x.val = torusSeq L P.m₀ n * L ^ m₁ * L ^ k
      then (0 : ℤ) else x.valMinAbs) : ℂ) / ((L : ℂ) ^ j)
  have hq : ∀ x, q (-x) = -q x :=
    fun x => corrected_weight_odd (L := L) (N₁ := torusSeq L P.m₀ n)
      (m₁ := m₁) (k := k) (j := j) x
  exact ctx.weighted_shape_offdiag_zero (torusSeq_dvd P.m₀ n) i₀ i₁ y hyu q hq μ η hne

omit [NeZero N₁] in
/-- Reflection symmetry kills every off-diagonal entry of the infinite raw matrix. -/
theorem raw_second_entry_offdiag_zero (hF : IsSFFamily P β ν a Tm' ρd' Ek')
    (hn : MomNum d L N k j ϱ P) (i₀ i₁ : Fin N) (y : Site d)
    (μ η : Fin d) (hne : η ≠ μ) :
    (∑' X' : Finset (Site d),
      ∑ z : ↥X', ∑ z' : ↥X',
        tensB i₀ i₁ (nuIdeal L k (ν k) j) X'
          (GE P β ν a Tm' j i₀ (nuIdeal L k (ν k) j) y X') z z' *
        (((z.1 μ - z'.1 μ : ℤ) : ℂ) * (((z.1 η - z'.1 η : ℤ) : ℂ)))) = 0 := by
  refine tendsto_nhds_unique (corrected_pair_tendsto hF hn i₀ i₁ y μ η) ?_
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_unlift_blockPt (L := L) (m₁ := m₁)
    (k := k) hn.hjk P.m₀ y] with n hyu
  exact (corrected_pair_sum_offdiag_zero hF hn i₀ i₁ y μ η hne n hyu).symm

omit [NeZero N₁] in
/-- The corrected diagonal pair sums agree on each torus in the stabilizing sequence. -/
theorem corrected_pair_sum_diag_eq (hF : IsSFFamily P β ν a Tm' ρd' Ek')
    (hn : MomNum d L N k j ϱ P) (i₀ i₁ : Fin N) (y : Site d)
    (μ η : Fin d) (n : ℕ)
    (hyu : unlift (L := L) (N₁ := torusSeq L P.m₀ n) (m₁ := m₁) (k := k) j
      (blockPt j y) = y) :
    let q : ZMod (torusSeq L P.m₀ n * L ^ m₁ * L ^ k) → ℂ :=
      fun x => ((if 2 * x.val = torusSeq L P.m₀ n * L ^ m₁ * L ^ k
        then (0 : ℤ) else x.valMinAbs) : ℂ) / ((L : ℂ) ^ j)
    (∑ᶠ X' ∈ ShAt (d := d) L m₁ k P.m₀ j y n,
      haveI : NeZero (torusSeq L P.m₀ n) := ⟨torusSeq_ne_zero P.m₀ n⟩
      ∑ z : ↥X', ∑ z' : ↥X',
        tensB i₀ i₁ (nuIdeal L k (ν k) j) X'
          (EauxC (Tm' (torusSeq L P.m₀ n)) j i₀ (nuIdeal L k (ν k) j) y X') z z' *
        (q ((ibase (L := L) (N₁ := torusSeq L P.m₀ n) (m₁ := m₁) (k := k) j z.1 -
          ibase (L := L) (N₁ := torusSeq L P.m₀ n) (m₁ := m₁) (k := k) j z'.1) μ) *
         q ((ibase (L := L) (N₁ := torusSeq L P.m₀ n) (m₁ := m₁) (k := k) j z.1 -
          ibase (L := L) (N₁ := torusSeq L P.m₀ n) (m₁ := m₁) (k := k) j z'.1) μ))) =
    (∑ᶠ X' ∈ ShAt (d := d) L m₁ k P.m₀ j y n,
      haveI : NeZero (torusSeq L P.m₀ n) := ⟨torusSeq_ne_zero P.m₀ n⟩
      ∑ z : ↥X', ∑ z' : ↥X',
        tensB i₀ i₁ (nuIdeal L k (ν k) j) X'
          (EauxC (Tm' (torusSeq L P.m₀ n)) j i₀ (nuIdeal L k (ν k) j) y X') z z' *
        (q ((ibase (L := L) (N₁ := torusSeq L P.m₀ n) (m₁ := m₁) (k := k) j z.1 -
          ibase (L := L) (N₁ := torusSeq L P.m₀ n) (m₁ := m₁) (k := k) j z'.1) η) *
         q ((ibase (L := L) (N₁ := torusSeq L P.m₀ n) (m₁ := m₁) (k := k) j z.1 -
          ibase (L := L) (N₁ := torusSeq L P.m₀ n) (m₁ := m₁) (k := k) j z'.1) η))) := by
  have ctx := hF.ctxSeq hn i₀ n
  let q : ZMod (torusSeq L P.m₀ n * L ^ m₁ * L ^ k) → ℂ :=
    fun x => ((if 2 * x.val = torusSeq L P.m₀ n * L ^ m₁ * L ^ k
      then (0 : ℤ) else x.valMinAbs) : ℂ) / ((L : ℂ) ^ j)
  simpa only [ShAt, GoodAt, pow_two] using
    ctx.weighted_shape_diag_eq (torusSeq_dvd P.m₀ n) i₀ i₁ y hyu q μ η

omit [NeZero N₁] in
/-- Coordinate exchange identifies all diagonal entries of the infinite raw matrix. -/
theorem raw_second_entry_diag_eq (hF : IsSFFamily P β ν a Tm' ρd' Ek')
    (hn : MomNum d L N k j ϱ P) (i₀ i₁ : Fin N) (y : Site d)
    (μ η : Fin d) :
    (∑' X' : Finset (Site d),
      ∑ z : ↥X', ∑ z' : ↥X',
        tensB i₀ i₁ (nuIdeal L k (ν k) j) X'
          (GE P β ν a Tm' j i₀ (nuIdeal L k (ν k) j) y X') z z' *
        (((z.1 μ - z'.1 μ : ℤ) : ℂ) * (((z.1 μ - z'.1 μ : ℤ) : ℂ)))) =
    (∑' X' : Finset (Site d),
      ∑ z : ↥X', ∑ z' : ↥X',
        tensB i₀ i₁ (nuIdeal L k (ν k) j) X'
          (GE P β ν a Tm' j i₀ (nuIdeal L k (ν k) j) y X') z z' *
        (((z.1 η - z'.1 η : ℤ) : ℂ) * (((z.1 η - z'.1 η : ℤ) : ℂ)))) := by
  refine tendsto_nhds_unique (corrected_pair_tendsto hF hn i₀ i₁ y μ μ) ?_
  refine (corrected_pair_tendsto hF hn i₀ i₁ y η η).congr' ?_
  filter_upwards [eventually_unlift_blockPt (L := L) (m₁ := m₁)
    (k := k) hn.hjk P.m₀ y] with n hyu
  exact (corrected_pair_sum_diag_eq hF hn i₀ i₁ y μ η n hyu).symm

omit [NeZero N₁] in
/-- The complete raw infinite-volume pair-moment matrix vanishes entrywise at every
integer centre. Reflection kills mixed entries, exchange identifies diagonal entries,
and the renormalization condition kills their trace. -/
theorem raw_second_matrix_zero (hF : IsSFFamily P β ν a Tm' ρd' Ek')
    (hn : MomNum d L N k j ϱ P) {i₀ i₁ : Fin N} (hne : i₁ ≠ i₀) (y : Site d) :
    ∀ μ η : Fin d,
      (∑' X' : Finset (Site d),
        ∑ z : ↥X', ∑ z' : ↥X',
          tensB i₀ i₁ (nuIdeal L k (ν k) j) X'
            (GE P β ν a Tm' j i₀ (nuIdeal L k (ν k) j) y X') z z' *
          (((z.1 μ - z'.1 μ : ℤ) : ℂ) * (((z.1 η - z'.1 η : ℤ) : ℂ)))) = 0 := by
  let M : Fin d → Fin d → ℂ := fun μ η =>
    ∑' X' : Finset (Site d),
      ∑ z : ↥X', ∑ z' : ↥X',
        tensB i₀ i₁ (nuIdeal L k (ν k) j) X'
          (GE P β ν a Tm' j i₀ (nuIdeal L k (ν k) j) y X') z z' *
        (((z.1 μ - z'.1 μ : ℤ) : ℂ) * (((z.1 η - z'.1 η : ℤ) : ℂ)))
  change ∀ μ η, M μ η = 0
  apply Def6v2.matrix_zero_of_hypercubic_symmetry
    (lt_of_lt_of_le (by decide : 0 < 3) hn.hd) M
  · exact raw_second_matrix_trace_zero hF hn hne y
  · intro μ η hneq
    exact raw_second_entry_offdiag_zero hF hn i₀ i₁ y μ η hneq.symm
  · intro μ η
    exact raw_second_entry_diag_eq hF hn i₀ i₁ y μ η

end Limit

end Balaban.SmallField.Def6
