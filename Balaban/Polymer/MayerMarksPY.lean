/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.MayerMarked
import Mathlib.Tactic.Positivity

/-!
# Analyticity of the local terms of the Mayer gas in the marks

For potentials `H_l t = a t + ∑_j l_j g_j t`, affine in the marks `l` and bounded as in `mayer_pe`
on a polydisc of marks, `mayer_marks_pe` shows that the local terms `P(Y)` of the polymer gas of
the Mayer activities are analytic in `l` on the polydisc and that the logarithm series is their sum
over all block sets. The proof is that of `mayer_marked` up to the Kotecký–Preiss bound
(`analyticOnNhd_mayerK_marks`, `mayer_activity_bound`, `size_entropy`, `kp_of_entropy`), followed by
`analyticOnNhd_Ff` and `logSeries_eq_sum_PY`.
-/

@[expose] public section

noncomputable section

open scoped Classical

open Finset MeasureTheory Balaban.Analysis

namespace Balaban.Polymer

section Main

variable {B : Type*} [Fintype B] {Ω : B → Type*} [∀ b, MeasurableSpace (Ω b)]
  (μ : ∀ b, Measure (Ω b)) [∀ b, IsProbabilityMeasure (μ b)]
  {T : Type*} [Fintype T] (sup : T → Finset B) {ι : Type*} [Fintype ι] [DecidableEq ι]
  {a : T → (∀ b, Ω b) → ℂ} {g : ι → T → (∀ b, Ω b) → ℂ} {d : Finset B → ℝ}
  {H0 κ0 κ1 c K0 c1 κ' κ0P K0P cP : ℝ} {r : ι → ℝ}

/-- **Analyticity of the local terms in the marks, and the series for the logarithm.**  For
potentials `a t + ∑_j l_j g_j t` bounded as in `mayer_pe` for every mark `l` of a polydisc, the
local terms `P(Y)` of the polymer gas of the Mayer activities are analytic in the marks on the
polydisc, and the logarithm series is their sum over all block sets. -/
theorem mayer_marks_pe (hne : ∀ t, (sup t).Nonempty)
    (ha : ∀ t, Measurable (a t)) (hab : ∀ t, Bdd (a t))
    (hg : ∀ j t, Measurable (g j t)) (hgb : ∀ j t, Bdd (g j t))
    (hH0 : 0 ≤ H0) (hH0' : H0 ≤ Real.log 2) (hκ0 : 0 ≤ κ0) (hκ1 : 0 ≤ κ1) (hc : 0 ≤ c)
    (hd : ∀ Y, 0 ≤ d Y)
    (hH : ∀ l ∈ polydisc (0 : ι → ℂ) r, ∀ t Φ,
      ‖Hlam a g l t Φ‖ ≤ H0 * Real.exp (-(κ0 + κ1) * d (sup t)))
    (hK0 : 0 ≤ K0)
    (hG2T : ∀ b : B, ∑ t ∈ Finset.univ.filter (fun t => b ∈ sup t),
      Real.exp (-κ0 * d (sup t)) ≤ K0)
    (hG3T : ∀ C : Finset T, ConnSet sup C →
      d (unionCs sup C) ≤ ∑ t ∈ C, d (sup t) + c * ((C.card : ℝ) - 1))
    (hc1 : 0 ≤ c1) (hq : 2 * H0 * K0 * Real.exp (κ1 * c) * c1 ≤ 1 / 2)
    (hG1 : ∀ Y : NePoly B, (Y.1.card : ℝ) ≤ c1 * (1 + d Y.1))
    (hκ' : 0 ≤ κ') (hcP : 0 ≤ cP)
    (hG2P : ∀ b : B, ∑ Y : NePoly B, (if b ∈ Y.1 then Real.exp (-κ0P * d Y.1) else 0) ≤ K0P)
    (hκ : κ' + κ0P + c1 ≤ κ1 - 3 / 2)
    (hα : 2 * (2 * H0 * K0 * Real.exp (κ1 * c)) * c1 * K0P * Real.exp (c1 + κ' * cP) ≤ 1) :
    (∀ Y : Finset B, AnalyticOnNhd ℂ (Ff (shareBlock (Subtype.val : NePoly B → Finset B))
        Subtype.val (marksK μ sup a g) Y) (polydisc 0 r)) ∧
    ∀ l ∈ polydisc (0 : ι → ℂ) r,
      logSeries (shareBlock (Subtype.val : NePoly B → Finset B)) (fun Z => marksK μ sup a g Z l) =
        ∑ Y : Finset B, Ff (shareBlock (Subtype.val : NePoly B → Finset B)) Subtype.val
          (marksK μ sup a g) Y l := by
  set inc : NePoly B → NePoly B → Prop := shareBlock (Subtype.val : NePoly B → Finset B) with hinc
  set ε : ℝ := 2 * (2 * H0 * K0 * Real.exp (κ1 * c)) * c1 with hε
  have hε0 : 0 ≤ ε := by positivity
  have hα1 : ε * K0P * Real.exp (c1 + κ' * cP) ≤ 1 := hα
  have hq0 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hq1 : Real.log 2 < 1 := Real.log_two_lt_d9.trans (by norm_num)
  have hb_le : ∀ l ∈ polydisc (0 : ι → ℂ) r, ∀ t Φ, ‖Hlam a g l t Φ‖ ≤ Real.log 2 := by
    intro l hl t Φ
    refine (hH l hl t Φ).trans ?_
    calc H0 * Real.exp (-(κ0 + κ1) * d (sup t)) ≤ H0 * 1 := by
          gcongr
          exact Real.exp_le_one_iff.mpr (by nlinarith [hd (sup t)])
      _ ≤ _ := by rw [mul_one]; exact hH0'
  have hKan : ∀ Z : NePoly B, AnalyticOnNhd ℂ (marksK μ sup a g Z) (polydisc 0 r) := fun Z =>
    analyticOnNhd_mayerK_marks μ sup hq0 hq1 r ha hab hg hgb hb_le Z
  have hKbd : ∀ (Z : NePoly B), ∀ l ∈ polydisc (0 : ι → ℂ) r,
      ‖marksK μ sup a g Z l‖ ≤ ε * Real.exp (-(κ1 - 3 / 2) * d Z.1) := fun Z l hl =>
    mayer_activity_bound μ hH0 hH0' hκ0 hκ1 hc hd hne (hH l hl) hG2T hG3T hc1 hq Z (hG1 Z)
  have hW := sizeW_nonneg (κ := κ1 - 3 / 2) (κ' := κ') (c := cP)
    (Subtype.val : NePoly B → Finset B) d hε0
  have hent := size_entropy (Subtype.val : NePoly B → Finset B) d (κ := κ1 - 3 / 2) (κ' := κ')
    (κ0 := κ0P) (K0 := K0P) (c := cP) (c1 := c1) hε0 hd hG1 hG2P hκ hα1
  have hKP := kp_of_entropy (Subtype.val : NePoly B → Finset B) _ hW hent
  have hg0 : ∀ Y : Finset B, 0 ≤ κ' * (d Y + cP) := fun Y => by have := hd Y; positivity
  have hb : ∀ (Z : NePoly B), ∀ l ∈ polydisc (0 : ι → ℂ) r,
      ‖marksK μ sup a g Z l‖ ≤
        sizeW (Subtype.val : NePoly B → Finset B) d ε (κ1 - 3 / 2) κ' cP Z := by
    intro Z l hl
    refine (hKbd Z l hl).trans ?_
    unfold sizeW
    calc ε * Real.exp (-(κ1 - 3 / 2) * d Z.1) = ε * Real.exp (-(κ1 - 3 / 2) * d Z.1) * 1 := by
          rw [mul_one]
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.one_le_exp (by
          have := hg0 Z.1; simpa using this)) (by positivity)
  refine ⟨fun Y => analyticOnNhd_Ff inc Subtype.val hKP hKan hb Y, fun l hl => ?_⟩
  exact logSeries_eq_sum_PY inc Subtype.val hKP (fun Z => marksK μ sup a g Z l)
    (fun Z => hb Z l hl)

end Main

end Balaban.Polymer
