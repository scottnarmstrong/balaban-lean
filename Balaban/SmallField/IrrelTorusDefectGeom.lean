/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, GPT-6-Sol
-/
module

public import Balaban.SmallField.Def6InfPoly
public import Balaban.SmallField.Def6BridgeGeom

/-!
# Small finite shapes persist in infinite volume

The converse transfer needed when comparing the finite and infinite reference jets: a polymer
whose centred coordinates are inside the torus with the paving margin is a polymer of `T∞`.
The destination torus is eventually large enough for every coordinate of the fixed finite shape;
`isPolyDom_transfer` then carries the polymer condition. The winding condition is supplied by
`eventually_nonWind`.
-/

@[expose] public section

namespace Balaban.SmallField.Def6

open Balaban Filter

variable {d L N₁ m₁ k : ℕ} [NeZero L] [NeZero N₁]

/-- Every fixed finite shape eventually satisfies the block-coordinate margin of `ZSmall` on
the stabilizing torus sequence. -/
theorem eventually_zsmall_zero (m₀ j : ℕ) (X' : Finset (Fin d → ℤ)) :
    ∀ᶠ n in atTop,
      ZSmall (torusSeq L m₀ n * L ^ m₁ * L ^ (k - j)) 0 X' := by
  unfold ZSmall
  rw [Filter.eventually_all_finset]
  intro z _
  rw [Filter.eventually_all]
  intro μ
  filter_upwards [Filter.eventually_ge_atTop (2 * ((z μ).natAbs + 1))] with n hn
  have hR := (succ_le_torusSeq (L := L) m₀ n).trans
    (torusSeq_le_side (L := L) (m₁ := m₁) (k := k) m₀ n j)
  have habs : |z μ| = ((z μ).natAbs : ℤ) := Int.abs_eq_natAbs _
  rw [habs]
  have hn' : (2 * ((z μ).natAbs + 1) : ℤ) ≤ n := by exact_mod_cast hn
  have hR' : (n : ℤ) + 1 ≤ ((torusSeq L m₀ n * L ^ m₁ * L ^ (k - j) : ℕ) : ℤ) := by
    exact_mod_cast hR
  omega

/-- A shape that is a polymer on one torus and lies within its paving margin belongs to the
infinite-volume polymer family. This is the finite-to-infinite half of the small-shape bijection;
no thermodynamic convergence assumption is used. -/
theorem infPoly_of_zsmall_of_isPolyDom {m₀ j : ℕ} (hjk : j ≤ k)
    (hN : L ^ m₀ ∣ N₁) {X' : Finset (Fin d → ℤ)}
    (hs : ZSmall (N₁ * L ^ m₁ * L ^ (k - j)) (L * L ^ (m₀ + m₁)) X')
    (hpd : IsPolyDom (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) m₀ j
      (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X')) :
    InfPoly (L := L) (m₁ := m₁) (k := k) m₀ j X' := by
  apply (infPoly_iff (L := L) (m₁ := m₁) (k := k) m₀ j X').2
  filter_upwards [eventually_zsmall_zero (L := L) (m₁ := m₁) (k := k) m₀ j X'] with n hn
  have : NeZero (torusSeq L m₀ n) := ⟨torusSeq_ne_zero m₀ n⟩
  exact isPolyDom_transfer hjk hN (torusSeq_dvd m₀ n) hs hn hpd

/-- The explicit covering-size threshold gives the margin needed for polymer transfer. The
factor four is stronger than the factor two in `ZSmall`; it also leaves room for block
boundaries in the paving comparison. -/
theorem zsmall_of_liftPolys_small {P : Consts} {j : ℕ} (hjk : j ≤ k)
    {X' : Finset (Site d)}
    (hX : X' ∈ liftPolys (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P j)
    (hs : 4 * (diamA d L P.m₀ m₁ *
        (1 + sizeJ (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P.m₀ j
          (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X')) +
        ((L * L ^ (P.m₀ + m₁) : ℕ) : ℝ) + 1) <
      ((N₁ * L ^ m₁ * L ^ (k - j) : ℕ) : ℝ)) :
    ZSmall (N₁ * L ^ m₁ * L ^ (k - j)) (L * L ^ (P.m₀ + m₁)) X' := by
  intro z hz μ
  have hdiam := liftPolys_diam hjk hX hz
  have hcoord : (|z μ| : ℤ) ≤ ∑ ν, |z ν| :=
    Finset.single_le_sum (f := fun ν => |z ν|) (fun ν _ => abs_nonneg _)
      (Finset.mem_univ μ)
  have hcoord' : ((|z μ| : ℤ) : ℝ) ≤ diamA d L P.m₀ m₁ *
      (1 + sizeJ (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P.m₀ j
        (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X')) :=
    (show ((|z μ| : ℤ) : ℝ) ≤ ((∑ ν, |z ν| : ℤ) : ℝ) from by
      exact_mod_cast hcoord).trans hdiam
  have hreal : (2 : ℝ) * (((|z μ| : ℤ) : ℝ) +
      ((L * L ^ (P.m₀ + m₁) : ℕ) : ℝ) + 1) <
      ((N₁ * L ^ m₁ * L ^ (k - j) : ℕ) : ℝ) := by
    have hq : (0 : ℝ) ≤ (L * L ^ (P.m₀ + m₁) : ℕ) := Nat.cast_nonneg _
    have hz0 : (0 : ℝ) ≤ (|z μ| : ℤ) := by exact_mod_cast abs_nonneg (z μ)
    linarith
  exact_mod_cast hreal

/-- A finite nonwinding shape below the explicit threshold is an infinite-volume polymer.
This supplies the finite-to-infinite small-shape inclusion used by the reference-jet comparison. -/
theorem infPoly_of_liftPolys_small {P : Consts} {j : ℕ} (hjk : j ≤ k)
    (hN : L ^ P.m₀ ∣ N₁) {X' : Finset (Site d)}
    (hX : X' ∈ liftPolys (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P j)
    (hs : 4 * (diamA d L P.m₀ m₁ *
        (1 + sizeJ (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P.m₀ j
          (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X')) +
        ((L * L ^ (P.m₀ + m₁) : ℕ) : ℝ) + 1) <
      ((N₁ * L ^ m₁ * L ^ (k - j) : ℕ) : ℝ)) :
    InfPoly (L := L) (m₁ := m₁) (k := k) P.m₀ j X' :=
  infPoly_of_zsmall_of_isPolyDom hjk hN (zsmall_of_liftPolys_small hjk hX hs) hX.2.2

omit [NeZero N₁] in
/-- A shape outside the small region has covering size at least the side-dependent threshold.
The threshold may be negative on small tori, in which case the inequality is still valid. -/
theorem sizeJ_ge_torus_threshold_of_not_small {P : Consts} {j : ℕ} (hd : 0 < d)
    {X' : Finset (Site d)}
    (hs : ¬ 4 * (diamA d L P.m₀ m₁ *
        (1 + sizeJ (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P.m₀ j
          (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X')) +
        ((L * L ^ (P.m₀ + m₁) : ℕ) : ℝ) + 1) <
      ((N₁ * L ^ m₁ * L ^ (k - j) : ℕ) : ℝ)) :
    (((N₁ * L ^ m₁ * L ^ (k - j) : ℕ) : ℝ) -
        4 * ((L * L ^ (P.m₀ + m₁) : ℕ) : ℝ) - 4) /
        (4 * diamA d L P.m₀ m₁) - 1 ≤
      sizeJ (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P.m₀ j
        (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X') := by
  have hA : 0 < diamA d L P.m₀ m₁ := by
    have hd' : (0 : ℝ) < d := by exact_mod_cast hd
    have hL' : (0 : ℝ) < L := by exact_mod_cast NeZero.pos L
    have hsqrt : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.2 hd'
    unfold diamA
    positivity
  have hle := le_of_not_gt hs
  have hdiv : (((N₁ * L ^ m₁ * L ^ (k - j) : ℕ) : ℝ) -
        4 * ((L * L ^ (P.m₀ + m₁) : ℕ) : ℝ) - 4) /
        (4 * diamA d L P.m₀ m₁) ≤
      1 + sizeJ (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P.m₀ j
        (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X') := by
    apply (div_le_iff₀ (by positivity : 0 < 4 * diamA d L P.m₀ m₁)).2
    nlinarith
  linarith

end Balaban.SmallField.Def6
