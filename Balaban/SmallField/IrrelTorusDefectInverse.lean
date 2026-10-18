/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, GPT-6-Sol
-/
module

public import Balaban.SmallField.IrrelTorusDefectGeom
public import Balaban.SmallField.Def6AvgGeom
public import Balaban.SmallField.IrrelTorusDefectCoordSmall

/-!
# Infinite polymers below the torus side threshold

The reverse inclusion uses eventual smallness on the stabilizing sequence, then transfers the
polymer condition to a fixed torus. The quantitative threshold is stated using `dInf`.
-/

@[expose] public section

namespace Balaban.SmallField.Def6

open Balaban Balaban.Multiscale Filter

variable {d L N₁ m₁ k : ℕ} [NeZero L] [NeZero N₁]

/-- Every fixed integer shape eventually fits with any prescribed paving margin. -/
theorem eventually_zsmall_margin (m₀ j Q : ℕ) (X' : Finset (Site d)) :
    ∀ᶠ n in atTop, ZSmall (torusSeq L m₀ n * L ^ m₁ * L ^ (k - j)) Q X' := by
  unfold ZSmall
  rw [Filter.eventually_all_finset]
  intro z _
  rw [Filter.eventually_all]
  intro μ
  filter_upwards [Filter.eventually_ge_atTop (2 * ((z μ).natAbs + Q + 1))] with n hn
  have hR := (succ_le_torusSeq (L := L) m₀ n).trans
    (torusSeq_le_side (L := L) (m₁ := m₁) (k := k) m₀ n j)
  have habs : |z μ| = ((z μ).natAbs : ℤ) := Int.abs_eq_natAbs _
  rw [habs]
  have hn' : (2 * ((z μ).natAbs + Q + 1) : ℤ) ≤ n := by exact_mod_cast hn
  have hR' : (n : ℤ) + 1 ≤ ((torusSeq L m₀ n * L ^ m₁ * L ^ (k - j) : ℕ) : ℤ) := by
    exact_mod_cast hR
  omega

/-- An infinite polymer that fits with the paving margin is a nonwinding polymer of the fixed
torus, irrespective of the position of its distinguished centre. -/
theorem fixedPoly_of_infPoly_zsmall {P : Consts} {j : ℕ} (hjk : j ≤ k)
    (hN : L ^ P.m₀ ∣ N₁) {X' : Finset (Site d)}
    (hX : InfPoly (L := L) (m₁ := m₁) (k := k) P.m₀ j X')
    (hs : ZSmall (N₁ * L ^ m₁ * L ^ (k - j)) (L * L ^ (P.m₀ + m₁)) X') :
    NonWind L N₁ m₁ k j X' ∧
      IsPolyDom (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P.m₀ j
        (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X') := by
  have hNw : NonWind L N₁ m₁ k j X' := by
    intro z hz μ
    have hsm := hs z hz μ
    have hq : (0 : ℤ) ≤ ((L * L ^ (P.m₀ + m₁) : ℕ) : ℤ) := Int.natCast_nonneg _
    have habs := abs_nonneg (z μ)
    have hlt : 2 * |z μ| < ((N₁ * L ^ m₁ * L ^ (k - j) : ℕ) : ℤ) := by omega
    exact valMinAbs_intCast_of_small hlt
  have hs0 : ZSmall (N₁ * L ^ m₁ * L ^ (k - j)) 0 X' := by
    intro z hz μ
    have hsm := hs z hz μ
    have hq : (0 : ℤ) ≤ ((L * L ^ (P.m₀ + m₁) : ℕ) : ℤ) := Int.natCast_nonneg _
    have habs := abs_nonneg (z μ)
    simpa only [Nat.cast_zero, add_zero] using (show 2 * (|z μ| + (0 : ℤ) + 1) <
      ((N₁ * L ^ m₁ * L ^ (k - j) : ℕ) : ℤ) by omega)
  obtain ⟨n, hgood, hsrc⟩ :=
    (hX.and (eventually_zsmall_margin (L := L) (m₁ := m₁) (k := k) P.m₀ j
      (L * L ^ (P.m₀ + m₁)) X')).exists
  have : NeZero (torusSeq L P.m₀ n) := ⟨torusSeq_ne_zero P.m₀ n⟩
  have hpd := isPolyDom_transfer hjk (torusSeq_dvd P.m₀ n) hN hsrc hs0 hgood.2
  exact ⟨hNw, hpd⟩

/-- Reverse inclusion of an infinite polymer into a fixed torus when its coordinates fit with
the paving margin. This is the inverse to `infPoly_of_zsmall_of_isPolyDom`. -/
theorem liftPolys_of_infPoly_zsmall {P : Consts} {j : ℕ} (hjk : j ≤ k)
    (hN : L ^ P.m₀ ∣ N₁) {X' : Finset (Site d)} (h0 : (0 : Site d) ∈ X')
    (hX : InfPoly (L := L) (m₁ := m₁) (k := k) P.m₀ j X')
    (hs : ZSmall (N₁ * L ^ m₁ * L ^ (k - j)) (L * L ^ (P.m₀ + m₁)) X') :
    X' ∈ liftPolys (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P j := by
  obtain ⟨hnw, hpd⟩ := fixedPoly_of_infPoly_zsmall hjk hN hX hs
  exact ⟨h0, hnw, hpd⟩

/-- A side threshold in terms of infinite-volume covering size gives the reverse inclusion.
The factor four leaves the same paving margin as the finite-to-infinite comparison. -/
theorem liftPolys_of_infPoly_small {P : Consts} {j : ℕ} (hjk : j ≤ k)
    (hN : L ^ P.m₀ ∣ N₁) {X' : Finset (Site d)} (h0 : (0 : Site d) ∈ X')
    (hX : InfPoly (L := L) (m₁ := m₁) (k := k) P.m₀ j X')
    (hs : 4 * (diamA d L P.m₀ m₁ *
        (1 + dInf L m₁ k P.m₀ j X') +
        ((L * L ^ (P.m₀ + m₁) : ℕ) : ℝ) + 1) <
      ((N₁ * L ^ m₁ * L ^ (k - j) : ℕ) : ℝ)) :
    X' ∈ liftPolys (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P j := by
  exact liftPolys_of_infPoly_zsmall hjk hN h0 hX
    (zsmall_of_infPoly_small hjk h0 hX hs)

/-- The inverse inclusion at an arbitrary integer centre. The additional absolute-coordinate
term records the position of that centre in the fixed torus chart. -/
theorem fixedPoly_of_infPoly_small_at {P : Consts} {j : ℕ} (hjk : j ≤ k)
    (hN : L ^ P.m₀ ∣ N₁) {X' : Finset (Site d)} {y : Site d} (hy : y ∈ X')
    (hX : InfPoly (L := L) (m₁ := m₁) (k := k) P.m₀ j X')
    (hs : 4 * ((∑ μ, (((|y μ| : ℤ) : ℝ))) +
        diamA d L P.m₀ m₁ * (1 + dInf L m₁ k P.m₀ j X') +
        ((L * L ^ (P.m₀ + m₁) : ℕ) : ℝ) + 1) <
      ((N₁ * L ^ m₁ * L ^ (k - j) : ℕ) : ℝ)) :
    NonWind L N₁ m₁ k j X' ∧
      IsPolyDom (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P.m₀ j
        (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X') := by
  apply fixedPoly_of_infPoly_zsmall hjk hN hX
  intro z hz μ
  have hdiam := infPoly_diam2 hjk hX hz hy
  have hcoord : (|z μ - y μ| : ℤ) ≤ ∑ ν, |z ν - y ν| :=
    Finset.single_le_sum (f := fun ν => |z ν - y ν|) (fun ν _ => abs_nonneg _)
      (Finset.mem_univ μ)
  have hycoord : (((|y μ| : ℤ) : ℝ)) ≤ ∑ ν, (((|y ν| : ℤ) : ℝ)) :=
    Finset.single_le_sum (f := fun ν => (((|y ν| : ℤ) : ℝ)))
      (fun ν _ => by exact_mod_cast abs_nonneg (y ν)) (Finset.mem_univ μ)
  have hzcoord : ((|z μ| : ℤ) : ℝ) ≤ ((|z μ - y μ| : ℤ) : ℝ) + ((|y μ| : ℤ) : ℝ) := by
    exact_mod_cast (show |z μ| ≤ |z μ - y μ| + |y μ| from by
      simpa only [sub_add_cancel] using (abs_add_le (z μ - y μ) (y μ)))
  have hcoord' : ((|z μ - y μ| : ℤ) : ℝ) ≤
      diamA d L P.m₀ m₁ * (1 + dInf L m₁ k P.m₀ j X') :=
    (show ((|z μ - y μ| : ℤ) : ℝ) ≤
      ((∑ ν, |z ν - y ν| : ℤ) : ℝ) from by exact_mod_cast hcoord).trans hdiam
  have hq : (0 : ℝ) ≤ (L * L ^ (P.m₀ + m₁) : ℕ) := Nat.cast_nonneg _
  have hz0 : (0 : ℝ) ≤ (|z μ| : ℤ) := by exact_mod_cast abs_nonneg (z μ)
  have hreal : (2 : ℝ) * (((|z μ| : ℤ) : ℝ) +
      ((L * L ^ (P.m₀ + m₁) : ℕ) : ℝ) + 1) <
      ((N₁ * L ^ m₁ * L ^ (k - j) : ℕ) : ℝ) := by linarith
  exact_mod_cast hreal

end Balaban.SmallField.Def6
