/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, GPT-6-Sol
-/
module

public import Balaban.Polymer.TwoTorusStepGeometry
public import Balaban.SmallField.IrrelTorusDefectInverse

/-!
# Transport of a small shape between two tori

The centred-box map sends the fine thickening of an integer shape to the same thickening
on another sufficiently large torus. The covering size is then preserved by the landed
two-torus geometry theorem.
-/

@[expose] public section

namespace Balaban.SmallField.Def6

open Balaban Balaban.Localization Balaban.Polymer Balaban.Polymer.TwoTorusStep Filter

variable {d L N₁ N₁' m₁ k j m₀ r : ℕ} [NeZero L] [NeZero N₁] [NeZero N₁']

omit [NeZero L] [NeZero N₁] [NeZero N₁'] in
/-- The box map leaves the integer coordinates of a site unchanged while the site is inside
the centred chart. -/
theorem boxMap_toTorus_small (hm : 2 * r + 1 < N₁ * L ^ m₁ * L ^ k)
    (x : Site d) (hx : ∀ μ, |x μ| ≤ r) :
    boxMap (N₁ * L ^ m₁ * L ^ k) (N₁' * L ^ m₁ * L ^ k)
      (toTorus L N₁ m₁ k x) = toTorus L N₁' m₁ k x := by
  funext μ
  exact congrArg (fun z : ℤ => (z : ZMod (N₁' * L ^ m₁ * L ^ k)))
    (valMinAbs_intCast_of_abs_le hm (hx μ))

/-- Exact transport of the fine polymer of a small integer shape. -/
theorem Ypoly_boxMap_of_small (hjk : j ≤ k) {X' : Finset (Site d)}
    (hs : ZSmall (N₁ * L ^ m₁ * L ^ (k - j)) 0 X')
    (hs' : ZSmall (N₁' * L ^ m₁ * L ^ (k - j)) 0 X')
    (hbound : ∀ x ∈ yhat L j X', ∀ μ, |x μ| ≤ r)
    (hm : 2 * r + 1 < N₁ * L ^ m₁ * L ^ k) :
    boxMap (N₁ * L ^ m₁ * L ^ k) (N₁' * L ^ m₁ * L ^ k) ''
      Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X' =
      Ypoly (L := L) (N₁ := N₁') (m₁ := m₁) (k := k) j X' := by
  rw [Ypoly_eq_image hjk hs, Ypoly_eq_image hjk hs', Set.image_image]
  exact Set.image_congr (fun x hx => boxMap_toTorus_small hm x (hbound x hx))

/-- Equal covering sizes for a shape fitting in the centred boxes of two tori. -/
theorem sizeJ_Ypoly_eq_of_small (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁')
    (hjk : j ≤ k) {X' : Finset (Site d)}
    (hs : ZSmall (N₁ * L ^ m₁ * L ^ (k - j)) 0 X')
    (hs' : ZSmall (N₁' * L ^ m₁ * L ^ (k - j)) 0 X')
    (hbound : ∀ x ∈ yhat L j X', ∀ μ, |x μ| ≤ r)
    (hr : 2 * r + L * cellSide L m₀ m₁ j < (N₁ * L ^ m₁) * L ^ k)
    (hr' : 2 * r + L * cellSide L m₀ m₁ j < (N₁' * L ^ m₁) * L ^ k) :
    sizeJ (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) m₀ j
      (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X') =
    sizeJ (L := L) (N₁ := N₁') (m₁ := m₁) (k := k) m₀ j
      (Ypoly (L := L) (N₁ := N₁') (m₁ := m₁) (k := k) j X') := by
  have hcell : 0 < L * cellSide L m₀ m₁ j := by
    exact Nat.mul_pos (NeZero.pos L) (cellSide_pos m₀ m₁ j)
  have hm : 2 * r + 1 < N₁ * L ^ m₁ * L ^ k := by
    omega
  have hbox : ∀ z ∈ Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X',
      InBox d r (N₁ * L ^ m₁ * L ^ k) z := by
    intro z hz
    rw [Ypoly_eq_image hjk hs] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    intro μ
    rw [show (toTorus L N₁ m₁ k x μ).valMinAbs = x μ from
      valMinAbs_intCast_of_abs_le hm (hbound x hx μ)]
    exact hbound x hx μ
  have hsize := sizeJ_image (d := d) (L := L) (N₁ := N₁) (N₁' := N₁')
    (m₁ := m₁) (K := k) (m₀ := m₀) (j := j) (r := r)
    hN hN' hjk hr hr' hbox
  rw [Ypoly_boxMap_of_small hjk hs hs' hbound hm] at hsize
  exact hsize.symm

/-- For a fixed shape fitting one centred torus chart, the covering size on the stabilizing
torus sequence is eventually equal to the fixed-torus covering size. -/
theorem eventually_sizeSeq_eq_fixed (hN : L ^ m₀ ∣ N₁) (hjk : j ≤ k)
    {X' : Finset (Site d)}
    (hs : ZSmall (N₁ * L ^ m₁ * L ^ (k - j)) 0 X')
    (hbound : ∀ x ∈ yhat L j X', ∀ μ, |x μ| ≤ r)
    (hr : 2 * r + L * cellSide L m₀ m₁ j < (N₁ * L ^ m₁) * L ^ k) :
    ∀ᶠ n in atTop,
      sizeSeq L m₁ k m₀ j X' n =
        sizeJ (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) m₀ j
          (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X') := by
  filter_upwards [eventually_zsmall_margin (L := L) (m₁ := m₁) (k := k)
      m₀ j 0 X',
    Filter.eventually_ge_atTop (2 * r + L * cellSide L m₀ m₁ j)] with n hs' hn
  have : NeZero (torusSeq L m₀ n) := ⟨torusSeq_ne_zero m₀ n⟩
  have hside := (succ_le_torusSeq (L := L) m₀ n).trans
    (torusSeq_le_side (L := L) (m₁ := m₁) (k := k) m₀ n 0)
  simp only [Nat.sub_zero] at hside
  have hr' : 2 * r + L * cellSide L m₀ m₁ j <
      (torusSeq L m₀ n * L ^ m₁) * L ^ k := by omega
  have heq := sizeJ_Ypoly_eq_of_small (d := d) (L := L) (N₁ := N₁)
    (N₁' := torusSeq L m₀ n) (m₁ := m₁) (k := k) (j := j) (m₀ := m₀) (r := r)
    hN (torusSeq_dvd m₀ n) hjk hs hs' hbound hr hr'
  exact heq.symm

/-- The fixed-torus size of a centred small shape is bounded by `dInf`, since the same
size occurs on a good torus of the stabilizing sequence. -/
theorem sizeJ_Ypoly_le_dInf_of_small (hN : L ^ m₀ ∣ N₁) (hjk : j ≤ k)
    {X' : Finset (Site d)}
    (hInf : InfPoly (L := L) (m₁ := m₁) (k := k) m₀ j X')
    (hs : ZSmall (N₁ * L ^ m₁ * L ^ (k - j)) 0 X')
    (hbound : ∀ x ∈ yhat L j X', ∀ μ, |x μ| ≤ r)
    (hr : 2 * r + L * cellSide L m₀ m₁ j < (N₁ * L ^ m₁) * L ^ k) :
    sizeJ (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) m₀ j
      (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X') ≤
      dInf L m₁ k m₀ j X' := by
  obtain ⟨n, hgood, heq⟩ :=
    (hInf.and (eventually_sizeSeq_eq_fixed hN hjk hs hbound hr)).exists
  rw [← heq]
  exact sizeSeq_le_dInf hjk hgood

end Balaban.SmallField.Def6
