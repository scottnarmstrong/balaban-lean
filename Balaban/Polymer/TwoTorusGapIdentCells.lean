/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.BoxTransport
public import Balaban.Polymer.TwoTorusResumInstance
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The sites of a set of cells, on two tori (item 24, blocker 7)

On the torus `Torus d (a K)` of side `a K` (cells of side `a`, `K` cells per side) the cell of a site
`x` has the centred coordinates `((x μ).val / a : ZMod K).valMinAbs`.  The sites of a set `X` of
cells (centred coordinates) are `{x | cell x ∈ X}`.  For `X` in the quarter box (`|c μ| ≤ K / 4`) and
`K ≤ K'` the box map `boxMap (a K) (a K')` maps the sites of `X` on the first torus onto the sites of
`X` on the second (`boxMap_image_cellSites`).
-/

@[expose] public section

namespace Balaban.Polymer.TwoTorusStep

open Balaban Balaban.Polymer

section Scalar

/-- The cell of a point of `ZMod (a K)` is the integer part of its centred representative divided by
`a`, modulo `K`. -/
theorem cell_cast {a K : ℕ} [NeZero a] [NeZero K] (x : ZMod (a * K)) :
    (((x.val / a : ℕ) : ZMod K)) = (((x.valMinAbs / (a : ℤ) : ℤ)) : ZMod K) := by
  have h := ZMod.val_eq_ite_valMinAbs x
  have hdiv : (((x.val / a : ℕ) : ℕ) : ℤ) = x.valMinAbs / (a : ℤ) +
      (if x.val ≤ a * K / 2 then 0 else (K : ℤ)) := by
    rw [Int.natCast_div, h]
    split_ifs with hc
    · simp
    · have : ((a * K : ℕ) : ℤ) = (a : ℤ) * K := by push_cast; ring
      rw [this, Int.add_mul_ediv_left _ _ (by exact_mod_cast NeZero.ne a)]
  rw [← Int.cast_natCast, hdiv]
  split_ifs <;> simp

/-- **The cell of a point, by its centred representative.**  For `|c| ≤ K / 4`, `K ≥ 8`: the cell
of `x ∈ ZMod (a K)` is `c` iff the centred representative `v` of `x` satisfies `a c ≤ v < a c + a`. -/
theorem cell_valMinAbs_iff {a K : ℕ} [NeZero a] [NeZero K] (hK : 8 ≤ K) {c : ℤ}
    (hc : c.natAbs ≤ K / 4) (x : ZMod (a * K)) :
    (((x.val / a : ℕ) : ZMod K)).valMinAbs = c ↔
      (a : ℤ) * c ≤ x.valMinAbs ∧ x.valMinAbs < (a : ℤ) * c + a := by
  have hapos : (0 : ℤ) < a := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne a)
  rw [cell_cast]
  set v := x.valMinAbs with hv
  set w := v / (a : ℤ) with hw
  have hv2 := ZMod.valMinAbs_mem_Ioc x
  rw [← hv] at hv2
  have hn : ((a * K : ℕ) : ℤ) = (a : ℤ) * K := by push_cast; ring
  rw [hn] at hv2
  obtain ⟨hv2a, hv2b⟩ := hv2
  have hw1 : w * a ≤ v := Int.ediv_mul_le v (ne_of_gt hapos)
  have hw2 : v < (w + 1) * a := Int.lt_ediv_add_one_mul_self v hapos
  have hK4 : (4 : ℤ) * (K / 4 : ℕ) ≤ K := by exact_mod_cast Nat.mul_div_le K 4
  have hcle : |c| ≤ ((K / 4 : ℕ) : ℤ) := by
    have := hc; rw [Int.abs_eq_natAbs]; exact_mod_cast this
  have hcK : 2 * ((K / 4 : ℕ) : ℤ) + 1 < K := by omega
  constructor
  · intro h
    have h1 : (((((w : ℤ)) : ZMod K)).valMinAbs : ℤ) = c := h
    have h2 : ((c : ℤ) : ZMod K) = ((w : ℤ) : ZMod K) := by
      rw [← h1, ZMod.coe_valMinAbs]
    have h3 := (ZMod.intCast_eq_intCast_iff_dvd_sub c w K).1 h2
    have hKpos : (0 : ℤ) < K := by omega
    have hwl : w * 2 ≤ K := by
      have : (w * 2) * a ≤ K * a := by nlinarith
      exact le_of_mul_le_mul_right this hapos
    have hwg : -(K : ℤ) < (w + 1) * 2 := by
      have : -(K : ℤ) * a < ((w + 1) * 2) * a := by nlinarith
      exact lt_of_mul_lt_mul_right this hapos.le
    have habs : |(w - c)| < K := by
      rw [abs_lt]; constructor <;> (rw [abs_le] at hcle; omega)
    have h4 : w - c = 0 := Int.eq_zero_of_abs_lt_dvd h3 habs
    have h5 : w = c := by omega
    rw [h5] at hw1 hw2
    constructor <;> nlinarith
  · rintro ⟨h1, h2⟩
    have h5 : w = c := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have : (w + 1) * a ≤ c * a := by nlinarith
        nlinarith
      · have : (c + 1) * a ≤ w * a := by nlinarith
        nlinarith
    show ((((w : ℤ)) : ZMod K)).valMinAbs = c
    rw [h5]
    exact valMinAbs_intCast_of_abs_le (by omega) hcle

/-- An integer in a cell `c` of the quarter box has `v` as centred representative in `ZMod (a K)`. -/
theorem valMinAbs_intCast_of_cell {a K : ℕ} [NeZero a] [NeZero K] (hK : 26 ≤ K) {c v : ℤ}
    (hc : c.natAbs ≤ K / 4) (h1 : (a : ℤ) * c ≤ v) (h2 : v < (a : ℤ) * c + a) :
    ((v : ℤ) : ZMod (a * K)).valMinAbs = v := by
  have hapos : 0 < a := Nat.pos_of_ne_zero (NeZero.ne a)
  have h4 : a * (4 * (K / 4)) ≤ a * K := Nat.mul_le_mul_left a (by omega)
  have h26 : a * 26 ≤ a * K := Nat.mul_le_mul_left a hK
  have hr : 2 * (a * (K / 4) + a) + 1 < a * K := by
    have : a * (4 * (K / 4)) = 4 * (a * (K / 4)) := by ring
    omega
  refine valMinAbs_intCast_of_abs_le (r := a * (K / 4) + a) hr ?_
  have hcl : |c| ≤ ((K / 4 : ℕ) : ℤ) := by
    rw [Int.abs_eq_natAbs]; exact_mod_cast hc
  rw [abs_le] at hcl ⊢
  have hA : (a : ℤ) * (K / 4 : ℕ) ≥ a * c := by nlinarith
  have hB : (a : ℤ) * -((K / 4 : ℕ) : ℤ) ≤ a * c := by nlinarith
  rw [Nat.cast_add, Nat.cast_mul]
  constructor <;> nlinarith

end Scalar

section Image

variable {d : ℕ}

/-- **The sites of a set of cells on two tori.**  Let `X` be a set of cells of the quarter box of the
torus with `K` cells per side, `26 ≤ K ≤ K'`.  The box map `boxMap (a K) (a K')` maps the sites of `X`
of the first torus onto the sites of `X` of the second (the cell of a site: the centred coordinates
of `(x_μ).val / a` modulo the number of cells per side). -/
theorem boxMap_image_cellSites {n n' a K K' : ℕ} [NeZero n] [NeZero n'] [NeZero a] [NeZero K]
    [NeZero K'] (hn : n = a * K) (hn' : n' = a * K') (hK : 26 ≤ K) (hKK' : K ≤ K')
    (X : Set (Fin d → ℤ)) (hX : ∀ c ∈ X, ∀ μ, (c μ).natAbs ≤ K / 4) :
    boxMap n n' '' {x : Balaban.Torus d n |
        (fun μ => (((((x μ).val / a : ℕ)) : ZMod K)).valMinAbs) ∈ X} =
      {x' : Balaban.Torus d n' |
        (fun μ => (((((x' μ).val / a : ℕ)) : ZMod K')).valMinAbs) ∈ X} := by
  subst hn hn'
  have hK' : 26 ≤ K' := hKK'.trans' hK
  have hdiv : K / 4 ≤ K' / 4 := Nat.div_le_div_right hKK'
  ext x'
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hc := hX _ hx
    suffices h : (fun μ => (((((boxMap (a * K) (a * K') x μ).val / a : ℕ)) : ZMod K')).valMinAbs) =
        fun μ => (((((x μ).val / a : ℕ)) : ZMod K)).valMinAbs by
      show (fun μ => (((((boxMap (a * K) (a * K') x μ).val / a : ℕ)) : ZMod K')).valMinAbs) ∈ X
      rw [h]; exact hx
    funext μ
    have h1 := (cell_valMinAbs_iff (a := a) (by omega) (hc μ) (x μ)).1 rfl
    have h2 : ((boxMap (a * K) (a * K') x) μ).valMinAbs = (x μ).valMinAbs :=
      valMinAbs_intCast_of_cell hK' ((hc μ).trans hdiv) h1.1 h1.2
    exact (cell_valMinAbs_iff (a := a) (K := K') (by omega) ((hc μ).trans hdiv)
      (boxMap (a * K) (a * K') x μ)).2 (by rw [h2]; exact h1)
  · intro hx'
    have hx'' : (fun μ => (((((x' μ).val / a : ℕ)) : ZMod K')).valMinAbs) ∈ X := hx'
    have hc := hX _ hx''
    refine ⟨boxMap (a * K') (a * K) x', ?_, ?_⟩
    · have h1 : ∀ μ, (a : ℤ) * (((((x' μ).val / a : ℕ)) : ZMod K')).valMinAbs ≤
          (x' μ).valMinAbs ∧ (x' μ).valMinAbs < (a : ℤ) *
            (((((x' μ).val / a : ℕ)) : ZMod K')).valMinAbs + a := fun μ =>
        (cell_valMinAbs_iff (a := a) (K := K') (by omega)
          ((hc μ).trans hdiv) (x' μ)).1 rfl
      have h2 : ∀ μ, ((boxMap (a * K') (a * K) x') μ).valMinAbs = (x' μ).valMinAbs := fun μ =>
        valMinAbs_intCast_of_cell hK (hc μ) (h1 μ).1 (h1 μ).2
      show (fun μ => (((((boxMap (a * K') (a * K) x' μ).val / a : ℕ)) : ZMod K)).valMinAbs) ∈ X
      have : (fun μ => (((((boxMap (a * K') (a * K) x' μ).val / a : ℕ)) : ZMod K)).valMinAbs) =
          fun μ => (((((x' μ).val / a : ℕ)) : ZMod K')).valMinAbs := by
        funext μ
        exact (cell_valMinAbs_iff (a := a) (K := K) (by omega) (hc μ)
          (boxMap (a * K') (a * K) x' μ)).2 (by rw [h2]; exact h1 μ)
      rw [this]; exact hx''
    · funext μ
      show (((boxMap (a * K') (a * K) x' μ).valMinAbs : ℤ) : ZMod (a * K')) = x' μ
      have h1 : ∀ μ, (a : ℤ) * (((((x' μ).val / a : ℕ)) : ZMod K')).valMinAbs ≤
          (x' μ).valMinAbs ∧ (x' μ).valMinAbs < (a : ℤ) *
            (((((x' μ).val / a : ℕ)) : ZMod K')).valMinAbs + a := fun μ =>
        (cell_valMinAbs_iff (a := a) (K := K') (by omega)
          ((hc μ).trans hdiv) (x' μ)).1 rfl
      have h2 : ((boxMap (a * K') (a * K) x') μ).valMinAbs = (x' μ).valMinAbs :=
        valMinAbs_intCast_of_cell hK (hc μ) (h1 μ).1 (h1 μ).2
      rw [h2, ZMod.coe_valMinAbs]

end Image

section Margins

variable {d : ℕ}

/-- **The spread of the sites of a compact set of cells.**  Two sites whose cells lie in a set `X`
of cells with spread at most `Dc ≤ (K - 26) / 25` and in the quarter box have centred coordinate
differences of absolute value at most `a (Dc + 1) - 1`. -/
theorem cell_spread_le {n a K Dc : ℕ} [NeZero n] [NeZero a] [NeZero K] (hn : n = a * K)
    (hK : 26 ≤ K) (hD : Dc ≤ (K - 26) / 25) (X : Set (Fin d → ℤ))
    (hX : ∀ c ∈ X, ∀ μ, (c μ).natAbs ≤ K / 4)
    (hXs : ∀ c ∈ X, ∀ c' ∈ X, ∀ μ, |c μ - c' μ| ≤ Dc) {x y : Balaban.Torus d n}
    (hx : (fun μ => (((((x μ).val / a : ℕ)) : ZMod K)).valMinAbs) ∈ X)
    (hy : (fun μ => (((((y μ).val / a : ℕ)) : ZMod K)).valMinAbs) ∈ X) (μ : Fin d) :
    |(x μ - y μ).valMinAbs| ≤ ((a * (Dc + 1) - 1 : ℕ) : ℤ) := by
  subst hn
  have hapos : 0 < a := Nat.pos_of_ne_zero (NeZero.ne a)
  have h1 := (cell_valMinAbs_iff (a := a) (by omega) (hX _ hx μ) (x μ)).1 rfl
  have h2 := (cell_valMinAbs_iff (a := a) (by omega) (hX _ hy μ) (y μ)).1 rfl
  have h3 := hXs _ hx _ hy μ
  rw [abs_le] at h3
  set c := (((((x μ).val / a : ℕ)) : ZMod K)).valMinAbs
  set c' := (((((y μ).val / a : ℕ)) : ZMod K)).valMinAbs
  have hKD : 25 * Dc + 26 ≤ K := by omega
  have hdiff : x μ - y μ = (((x μ).valMinAbs - (y μ).valMinAbs : ℤ) : ZMod (a * K)) := by
    push_cast; rfl
  have hbound : |(x μ).valMinAbs - (y μ).valMinAbs| ≤ ((a * (Dc + 1) - 1 : ℕ) : ℤ) := by
    have hpos : 1 ≤ a * (Dc + 1) := Nat.one_le_iff_ne_zero.2 (by positivity)
    rw [Nat.cast_sub hpos, abs_le]
    push_cast
    constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]
  have hsmall : 2 * (a * (Dc + 1) - 1) + 1 < a * K := by
    have h25 : a * (25 * Dc + 26) ≤ a * K := Nat.mul_le_mul_left a hKD
    have : a * (25 * Dc + 26) = 25 * (a * Dc) + 26 * a := by ring
    have : a * (Dc + 1) = a * Dc + a := by ring
    omega
  rw [hdiff, valMinAbs_intCast_of_abs_le hsmall hbound]
  exact hbound

/-- The centred coordinates of a site whose cell lies in the quarter box have absolute value at
most `a (K / 4 + 1)`. -/
theorem cell_box_le {n a K : ℕ} [NeZero n] [NeZero a] [NeZero K] (hn : n = a * K) (hK : 26 ≤ K)
    (X : Set (Fin d → ℤ)) (hX : ∀ c ∈ X, ∀ μ, (c μ).natAbs ≤ K / 4) {x : Balaban.Torus d n}
    (hx : (fun μ => (((((x μ).val / a : ℕ)) : ZMod K)).valMinAbs) ∈ X) (μ : Fin d) :
    |(x μ).valMinAbs| ≤ ((a * (K / 4 + 1) : ℕ) : ℤ) := by
  subst hn
  have h1 := (cell_valMinAbs_iff (a := a) (by omega) (hX _ hx μ) (x μ)).1 rfl
  set c := (((((x μ).val / a : ℕ)) : ZMod K)).valMinAbs
  have hc := hX _ hx μ
  have hcl : |c| ≤ ((K / 4 : ℕ) : ℤ) := by
    rw [Int.abs_eq_natAbs]; exact_mod_cast hc
  rw [abs_le] at hcl ⊢
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hapos : (0 : ℤ) < a := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne a)
  constructor <;> nlinarith [h1.1, h1.2, hcl.1, hcl.2]

/-- **The margins of the recentred transport at the gap scale.**  For the sites of a compact set of
cells (`K ≤ K'`, `26 ≤ K`, cells of side `a`, `a ≥ P`): the radius `ρ = Ds + (Ds + 1) / 4` with
`Ds = a (Dc + 1) - 1` satisfies the margin of the block-energy correspondence
`2 (ρ + P) + 3 P + 5 < a K`. -/
theorem margin_blockEnergy {a K Dc P : ℕ} (hK : 26 ≤ K) (hD : Dc ≤ (K - 26) / 25) (hP : P ≤ a)
    (ha : 0 < a) :
    2 * ((a * (Dc + 1) - 1 + (a * (Dc + 1) - 1 + 1) / 4) + P) + 3 * P + 5 < a * K := by
  have hKD : 25 * Dc + 26 ≤ K := by omega
  have h25 : a * (25 * Dc + 26) ≤ a * K := Nat.mul_le_mul_left a hKD
  have h26 : a * 26 ≤ a * K := Nat.mul_le_mul_left a hK
  have e1 : a * (25 * Dc + 26) = 25 * (a * Dc) + 26 * a := by ring
  have e2 : a * (Dc + 1) = a * Dc + a := by ring
  omega

end Margins

end Balaban.Polymer.TwoTorusStep
