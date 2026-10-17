/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, GPT-6-Sol
-/
module

public import Balaban.SmallField.Def6AvgMomLimit

/-!
# Thermodynamic limit for weighted raw pair moments

The scalar second moment and every matrix entry use the same shape convergence argument.
The weight below is independent of the torus size and is bounded by the squared pair length.
-/

@[expose] public section

namespace Balaban.SmallField.Def6

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.Fluctuation Balaban.SmallField
  Filter Metric Set

variable {d L m₁ k N : ℕ} [NeZero L] {ϱ : ℝ} {P : Consts} {β ν a : ℕ → ℝ}
  {Ek : ℕ → ℝ}
  {Tm : ∀ (N₁ : ℕ) [NeZero N₁], Terms d L N₁ m₁ k N ϱ}
  {ρd : ∀ (N₁ : ℕ) [NeZero N₁], (CTorus d L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) →
    (CTorus d L N₁ m₁ k → Fin N → ℝ) → ℝ}
  {j : ℕ}

/-- A coordinate product is bounded by the squared Euclidean length of the pair. -/
theorem norm_pair_coord_mul_le_sq (z z' : Site d) (μ ν : Fin d) :
    ‖(((z μ - z' μ : ℤ) : ℂ) * (((z ν - z' ν : ℤ) : ℂ)))‖ ≤
      ∑ ξ, (((z ξ - z' ξ : ℤ) : ℝ)) ^ 2 := by
  have hμ : (((z μ - z' μ : ℤ) : ℝ)) ^ 2 ≤
      ∑ ξ, (((z ξ - z' ξ : ℤ) : ℝ)) ^ 2 := by
    exact Finset.single_le_sum
      (f := fun ξ : Fin d => (((z ξ - z' ξ : ℤ) : ℝ)) ^ 2)
      (fun ξ _ => sq_nonneg _) (Finset.mem_univ μ)
  have hν : (((z ν - z' ν : ℤ) : ℝ)) ^ 2 ≤
      ∑ ξ, (((z ξ - z' ξ : ℤ) : ℝ)) ^ 2 := by
    exact Finset.single_le_sum
      (f := fun ξ : Fin d => (((z ξ - z' ξ : ℤ) : ℝ)) ^ 2)
      (fun ξ _ => sq_nonneg _) (Finset.mem_univ ν)
  rw [norm_mul, Complex.norm_intCast, Complex.norm_intCast]
  change |((z μ - z' μ : ℤ) : ℝ)| * |((z ν - z' ν : ℤ) : ℝ)| ≤ _
  nlinarith [sq_nonneg (|((z μ - z' μ : ℤ) : ℝ)| - |((z ν - z' ν : ℤ) : ℝ)|),
    sq_abs ((z μ - z' μ : ℤ) : ℝ), sq_abs ((z ν - z' ν : ℤ) : ℝ)]

/-- Thermodynamic transfer for finite-volume pair weights which may depend on the torus size.
Only their equality on shapes below the chart threshold and the squared-length bound are used. -/
theorem weighted_pair_tendsto_var (hF : IsSFFamily P β ν a Tm ρd Ek)
    (hn : MomNum d L N k j ϱ P) (i₀ i₁ : Fin N) (y : Site d)
    (wN : (n : ℕ) → (X' : Finset (Site d)) → ↥X' → ↥X' → ℂ)
    (wY : (X' : Finset (Site d)) → ↥X' → ↥X' → ℂ)
    (hmatch : ∀ n X', y ∈ X' → GoodAt L m₁ k P.m₀ j X' n →
      sizeSeq L m₁ k P.m₀ j X' n < tauY d L m₁ k P.m₀ j n y →
      ∀ z z', wN n X' z z' = wY X' z z')
    (hwN : ∀ n X' z z', ‖wN n X' z z'‖ ≤
      ∑ μ, (((z.1 μ - z'.1 μ : ℤ) : ℝ)) ^ 2)
    (hwY : ∀ X' z z', ‖wY X' z z'‖ ≤
      ∑ μ, (((z.1 μ - z'.1 μ : ℤ) : ℝ)) ^ 2) :
    Tendsto
      (fun n => ∑ᶠ X' ∈ ShAt (d := d) L m₁ k P.m₀ j y n,
        haveI : NeZero (torusSeq L P.m₀ n) := ⟨torusSeq_ne_zero P.m₀ n⟩
        ∑ z : ↥X', ∑ z' : ↥X',
          tensB i₀ i₁ (nuIdeal L k (ν k) j) X'
            (EauxC (Tm (torusSeq L P.m₀ n)) j i₀ (nuIdeal L k (ν k) j) y X') z z' *
            wN n X' z z') atTop
      (nhds (∑' X' : Finset (Site d),
        ∑ z : ↥X', ∑ z' : ↥X',
          tensB i₀ i₁ (nuIdeal L k (ν k) j) X'
            (GE P β ν a Tm j i₀ (nuIdeal L k (ν k) j) y X') z z' *
            wY X' z z')) := by
  have hC : 0 ≤ momC (d := d) L m₁ P (liftRadius d L N P j) y *
      (24 * Real.exp 1) := by
    have := momC_nonneg hF (y := y) (L := L) (m₁ := m₁) (j := j)
    positivity
  apply tendsto_shapeSum (L := L) (m₁ := m₁) (k := k) (m₀ := P.m₀) (j := j)
    hn.hjk (κ := P.κ - 1) (by linarith [hn.hκ, aEnt_nonneg d L]) y
    (fun n X' =>
      haveI : NeZero (torusSeq L P.m₀ n) := ⟨torusSeq_ne_zero P.m₀ n⟩
      ∑ z : ↥X', ∑ z' : ↥X',
        tensB i₀ i₁ (nuIdeal L k (ν k) j) X'
          (EauxC (Tm (torusSeq L P.m₀ n)) j i₀ (nuIdeal L k (ν k) j) y X') z z' *
          wN n X' z z')
    (fun X' => ∑ z : ↥X', ∑ z' : ↥X',
      tensB i₀ i₁ (nuIdeal L k (ν k) j) X'
        (GE P β ν a Tm j i₀ (nuIdeal L k (ν k) j) y X') z z' * wY X' z z') hC
  · intro n X' hy hgood hsz
    exact weightedMomN_eq_weightedMomY hF hn hy
      (infPoly_of_small hn.hjk hy hgood hsz) hgood (wN n X') (wY X')
      (hmatch n X' hy hgood hsz)
  · intro n X' hy hgood
    exact weightedMomN_bound hF hn hy hgood (wN n X') (hwN n X')
  · intro X' hy hX
    exact weightedMomY_bound hF hn hy hX (wY X') (hwY X')
  · intro X' h
    exact weightedMomY_eq_zero (fun h' => h ⟨h'.2, h'.1⟩) (wY X')

/-- The fixed-weight instance of `weighted_pair_tendsto_var`. -/
theorem weighted_pair_tendsto (hF : IsSFFamily P β ν a Tm ρd Ek)
    (hn : MomNum d L N k j ϱ P) (i₀ i₁ : Fin N) (y : Site d)
    (w : (X' : Finset (Site d)) → ↥X' → ↥X' → ℂ)
    (hw : ∀ X' z z', ‖w X' z z'‖ ≤
      ∑ μ, (((z.1 μ - z'.1 μ : ℤ) : ℝ)) ^ 2) :
    Tendsto
      (fun n => ∑ᶠ X' ∈ ShAt (d := d) L m₁ k P.m₀ j y n,
        haveI : NeZero (torusSeq L P.m₀ n) := ⟨torusSeq_ne_zero P.m₀ n⟩
        ∑ z : ↥X', ∑ z' : ↥X',
          tensB i₀ i₁ (nuIdeal L k (ν k) j) X'
            (EauxC (Tm (torusSeq L P.m₀ n)) j i₀ (nuIdeal L k (ν k) j) y X') z z' *
            w X' z z') atTop
      (nhds (∑' X' : Finset (Site d),
        ∑ z : ↥X', ∑ z' : ↥X',
          tensB i₀ i₁ (nuIdeal L k (ν k) j) X'
            (GE P β ν a Tm j i₀ (nuIdeal L k (ν k) j) y X') z z' *
            w X' z z')) := by
  exact weighted_pair_tendsto_var hF hn i₀ i₁ y (fun _ => w) w
    (fun _ _ _ _ _ _ _ => rfl) (fun _ => hw) hw

/-- Every ordered entry of the raw second-moment matrix is the thermodynamic limit of
the corresponding finite-volume pair sum. No symmetry or vanishing is asserted here. -/
theorem raw_second_entry_tendsto (hF : IsSFFamily P β ν a Tm ρd Ek)
    (hn : MomNum d L N k j ϱ P) (i₀ i₁ : Fin N) (y : Site d) (μ η : Fin d) :
    Tendsto
      (fun n => ∑ᶠ X' ∈ ShAt (d := d) L m₁ k P.m₀ j y n,
        haveI : NeZero (torusSeq L P.m₀ n) := ⟨torusSeq_ne_zero P.m₀ n⟩
        ∑ z : ↥X', ∑ z' : ↥X',
          tensB i₀ i₁ (nuIdeal L k (ν k) j) X'
            (EauxC (Tm (torusSeq L P.m₀ n)) j i₀ (nuIdeal L k (ν k) j) y X') z z' *
            (((z.1 μ - z'.1 μ : ℤ) : ℂ) * (((z.1 η - z'.1 η : ℤ) : ℂ)))) atTop
      (nhds (∑' X' : Finset (Site d),
        ∑ z : ↥X', ∑ z' : ↥X',
          tensB i₀ i₁ (nuIdeal L k (ν k) j) X'
            (GE P β ν a Tm j i₀ (nuIdeal L k (ν k) j) y X') z z' *
            (((z.1 μ - z'.1 μ : ℤ) : ℂ) * (((z.1 η - z'.1 η : ℤ) : ℂ))))) := by
  exact weighted_pair_tendsto hF hn i₀ i₁ y
    (fun _ z z' => (((z.1 μ - z'.1 μ : ℤ) : ℂ) *
      (((z.1 η - z'.1 η : ℤ) : ℂ))))
    (fun _ z z' => norm_pair_coord_mul_le_sq z.1 z'.1 μ η)

/-- Absolute summability of every raw matrix entry at a fixed centre. -/
theorem raw_second_entry_summable (hF : IsSFFamily P β ν a Tm ρd Ek)
    (hn : MomNum d L N k j ϱ P) (i₀ i₁ : Fin N) (y : Site d) (μ η : Fin d) :
    Summable fun X' : Finset (Site d) =>
      ∑ z : ↥X', ∑ z' : ↥X',
        tensB i₀ i₁ (nuIdeal L k (ν k) j) X'
          (GE P β ν a Tm j i₀ (nuIdeal L k (ν k) j) y X') z z' *
          (((z.1 μ - z'.1 μ : ℤ) : ℂ) * (((z.1 η - z'.1 η : ℤ) : ℂ))) := by
  have hC : 0 ≤ momC (d := d) L m₁ P (liftRadius d L N P j) y *
      (24 * Real.exp 1) := by
    have := momC_nonneg hF (y := y) (L := L) (m₁ := m₁) (j := j)
    positivity
  refine Summable.of_norm ?_
  refine (summable_shapes (L := L) (m₁ := m₁) (m₀ := P.m₀) (j := j) hn.hjk
    (κ := P.κ - 1) (by linarith [hn.hκ, aEnt_nonneg d L]) y
    (fun X' => ∑ z : ↥X', ∑ z' : ↥X',
      tensB i₀ i₁ (nuIdeal L k (ν k) j) X'
        (GE P β ν a Tm j i₀ (nuIdeal L k (ν k) j) y X') z z' *
        (((z.1 μ - z'.1 μ : ℤ) : ℂ) * (((z.1 η - z'.1 η : ℤ) : ℂ)))) hC
    (fun X' hy hX => weightedMomY_bound hF hn hy hX _
      (fun z z' => norm_pair_coord_mul_le_sq z.1 z'.1 μ η))
    (fun X' h => weightedMomY_eq_zero
      (fun h' => h ⟨h'.2, h'.1⟩) _)).1

/-- The trace of the raw infinite-volume matrix is the scalar moment renormalization
condition. The ordered matrix entries are summed without averaging. -/
theorem raw_second_matrix_trace_zero (hF : IsSFFamily P β ν a Tm ρd Ek)
    (hn : MomNum d L N k j ϱ P) {i₀ i₁ : Fin N} (hne : i₁ ≠ i₀) (y : Site d) :
    (∑ μ : Fin d, ∑' X' : Finset (Site d),
      ∑ z : ↥X', ∑ z' : ↥X',
        tensB i₀ i₁ (nuIdeal L k (ν k) j) X'
          (GE P β ν a Tm j i₀ (nuIdeal L k (ν k) j) y X') z z' *
          (((z.1 μ - z'.1 μ : ℤ) : ℂ) * (((z.1 μ - z'.1 μ : ℤ) : ℂ)))) = 0 := by
  have hs : ∀ μ ∈ (Finset.univ : Finset (Fin d)), Summable fun X' : Finset (Site d) =>
      ∑ z : ↥X', ∑ z' : ↥X',
        tensB i₀ i₁ (nuIdeal L k (ν k) j) X'
          (GE P β ν a Tm j i₀ (nuIdeal L k (ν k) j) y X') z z' *
          (((z.1 μ - z'.1 μ : ℤ) : ℂ) * (((z.1 μ - z'.1 μ : ℤ) : ℂ))) :=
    fun μ _ => raw_second_entry_summable hF hn i₀ i₁ y μ μ
  rw [(Summable.tsum_finsetSum hs).symm]
  have hshape : ∀ X' : Finset (Site d),
      (∑ μ : Fin d, ∑ z : ↥X', ∑ z' : ↥X',
        tensB i₀ i₁ (nuIdeal L k (ν k) j) X'
          (GE P β ν a Tm j i₀ (nuIdeal L k (ν k) j) y X') z z' *
          (((z.1 μ - z'.1 μ : ℤ) : ℂ) * (((z.1 μ - z'.1 μ : ℤ) : ℂ)))) =
        MomY P β ν a Tm j i₀ i₁ y X' := by
    intro X'
    unfold MomY
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun z' _ => ?_
    rw [← Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun μ _ => by ring
  rw [tsum_congr hshape]
  exact momY_tsum_zero hF hn hne y

end Balaban.SmallField.Def6
