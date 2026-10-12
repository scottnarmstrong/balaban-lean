/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.MarkedHolo

/-!
# Truncated second moment, termwise (PE-M, two marks)

Under the hypotheses of `mayer_marked_termwise`, the partition function with marks is analytic in the
marks, does not vanish at `0`, its truncated second moment is the sum of the local terms
`∂_j ∂_i P(Y)`, those vanish unless `Y ⊇ S i ∪ S j`, and each obeys the Cauchy bound
`‖∂_j ∂_i P(Y)‖ e^{κ'(d Y + c_P)} ≤ α / (r_i r_j)` for `Y ∋ b`, `b ∈ S i`
(`mayer_marked_second`).
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
  {H0 κ0 κ1 c K0 c1 κ' κ0P K0P cP : ℝ} {r : ι → ℝ} {S : ι → Finset B}

/-- **Second moment, termwise** (see the module docstring). -/
theorem mayer_marked_second (hne : ∀ t, (sup t).Nonempty) (hr : ∀ i, 0 < r i)
    (ha : ∀ t, Measurable (a t)) (hab : ∀ t, Bdd (a t))
    (hg : ∀ j t, Measurable (g j t)) (hgb : ∀ j t, Bdd (g j t))
    (hloca : ∀ t, DepOn (sup t) (a t)) (hlocg : ∀ j t, DepOn (sup t) (g j t))
    (hS : ∀ j t Φ, ¬ S j ⊆ sup t → g j t Φ = 0)
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
    (hG3P : ∀ (n : ℕ) (X : Fin (n + 1) → NePoly B),
      (clusterGraph (shareBlock (Subtype.val : NePoly B → Finset B)) X).Connected →
        d (unionOf (Subtype.val : NePoly B → Finset B) X) ≤ ∑ i, d (X i).1 + cP * n)
    (hκ : κ' + κ0P + c1 ≤ κ1 - 3 / 2)
    (hα : 2 * (2 * H0 * K0 * Real.exp (κ1 * c)) * c1 * K0P * Real.exp (c1 + κ' * cP) ≤ 1) :
    AnalyticOnNhd ℂ (marksXi μ a g) (polydisc 0 r) ∧ marksXi μ a g 0 ≠ 0 ∧
    (∀ {i j : ι}, i ≠ j →
      D2 i j (marksXi μ a g) / marksXi μ a g 0 -
          (D1 i (marksXi μ a g) / marksXi μ a g 0) * (D1 j (marksXi μ a g) / marksXi μ a g 0) =
        ∑ Y : Finset B, D2 i j (Ff (shareBlock (Subtype.val : NePoly B → Finset B)) Subtype.val
          (marksK μ sup a g) Y)) ∧
    (∀ {i j : ι} {Y : Finset B}, (¬ S i ⊆ Y ∨ ¬ S j ⊆ Y) →
      D2 i j (Ff (shareBlock (Subtype.val : NePoly B → Finset B)) Subtype.val
        (marksK μ sup a g) Y) = 0) ∧
    ∀ {i j : ι}, i ≠ j → ∀ {b : B}, b ∈ S i → ∀ Y : Finset B, b ∈ Y →
      ‖D2 i j (Ff (shareBlock (Subtype.val : NePoly B → Finset B)) Subtype.val
        (marksK μ sup a g) Y)‖ * Real.exp (κ' * (d Y + cP)) ≤
        (2 * (2 * H0 * K0 * Real.exp (κ1 * c)) * c1 * K0P * Real.exp (c1 + κ' * cP)) / r i / r j := by
  set inc : NePoly B → NePoly B → Prop := shareBlock (Subtype.val : NePoly B → Finset B) with hinc
  set ε : ℝ := 2 * (2 * H0 * K0 * Real.exp (κ1 * c)) * c1 with hε
  have hε0 : 0 ≤ ε := by positivity
  set α : ℝ := ε * K0P * Real.exp (c1 + κ' * cP) with hαdef
  have hα1 : ε * K0P * Real.exp (c1 + κ' * cP) ≤ 1 := hα
  have hlocl : ∀ l t, DepOn (sup t) (Hlam a g l t) := fun l t Φ Φ' h => by
    unfold Hlam
    rw [hloca t Φ Φ' h]
    congr 1
    exact Finset.sum_congr rfl (fun j _ => by rw [hlocg j t Φ Φ' h])
  obtain ⟨hKan, hKbd, hb⟩ := marked_bounds μ sup hne ha hab hg hgb hH0 hH0' hκ0 hκ1 hc hd hH
    hG2T hG3T hc1 hq hG1 hK0 hκ' hcP
  have hKP := marked_kp (B := B) (d := d) (c1 := c1) (κ' := κ') (κ0P := κ0P) (K0P := K0P)
    (cP := cP) (κ1 := κ1) hε0 hd hG1 hG2P hκ hα1
  have hg0 : ∀ Y : Finset B, 0 ≤ κ' * (d Y + cP) := fun Y => by have := hd Y; positivity
  have hrefl : ∀ x : NePoly B, inc x x := shareBlock_refl _ (fun Y => Y.2)
  have hdep : MarkDep (Subtype.val : NePoly B → Finset B) S (marksK μ sup a g) :=
    fun i Z hZ l s => marksK_indep μ sup hS i Z hZ l s
  have hZ : ∀ l ∈ polydisc (0 : ι → ℂ) r, marksXi μ a g l = Xi inc (fun Z => marksK μ sup a g Z l) := by
    intro l hl
    exact mayer_integral_eq μ hne (hlocl l) (measurable_Hlam ha hg l)
      (fun t => ⟨_, hH l hl t⟩)
  have hG3' := size_g_G3 (Subtype.val : NePoly B → Finset B) d (c := cP) hκ' hG3P
  have hent' : ∀ b : B, ∑ x : NePoly B, (if b ∈ x.1 then
      sizeW (Subtype.val : NePoly B → Finset B) d ε (κ1 - 3 / 2) κ' cP x *
        Real.exp (α * (x.1.card : ℝ)) else 0) ≤ α :=
    size_entropy (Subtype.val : NePoly B → Finset B) d (κ := κ1 - 3 / 2) (κ' := κ')
      (κ0 := κ0P) (K0 := K0P) (c := cP) (c1 := c1) hε0 hd hG1 hG2P hκ hα1
  have h0 := zero_mem_polydisc hr
  refine ⟨?_, Zf_zero_ne inc hKP hr hb hrefl _ hZ, fun {i j} _ =>
    D2_Zf_div inc Subtype.val hKP hr hKan hb hrefl _ hZ i j, fun {i j Y} hY =>
    D2_Ff_eq_zero inc Subtype.val hKP hr hKan hb hdep hY, ?_⟩
  · intro w hw
    have hev : marksXi μ a g =ᶠ[nhds w] fun l => Complex.exp (Lf inc (marksK μ sup a g) l) := by
      filter_upwards [(isOpen_polydisc (0 : ι → ℂ) r).mem_nhds hw] with l hl
      exact Zf_eq_exp inc hKP hb hrefl _ hZ hl
    exact ((analyticOnNhd_Lf inc hKP hKan hb w hw).cexp).congr hev.symm
  intro i j hij b hbS Y hbY
  have hsumb := sum_norm_D2_Ff_le inc Subtype.val hKP hr hKan hb
    (fun Y : Finset B => κ' * (d Y + cP)) 0 le_rfl hg0 hG3' (κ0 := fun x => ε * Real.exp (-(κ1 - 3 / 2) * d x.1))
    (fun x => rfl) (fun x l hl => hKbd x l hl) b hij
  have h1 : Real.exp (κ' * (d Y + cP)) *
      ‖D2 i j (Ff inc Subtype.val (marksK μ sup a g) Y)‖ ≤
      ∑ Y ∈ (Finset.univ : Finset (Finset B)).filter (fun Y => b ∈ Y),
        Real.exp (κ' * (d Y + cP)) * ‖D2 i j (Ff inc Subtype.val (marksK μ sup a g) Y)‖ :=
    Finset.single_le_sum (f := fun Y => Real.exp (κ' * (d Y + cP)) *
      ‖D2 i j (Ff inc Subtype.val (marksK μ sup a g) Y)‖) (fun _ _ => by positivity)
      (Finset.mem_filter.2 ⟨Finset.mem_univ _, hbY⟩)
  rw [mul_comm]
  exact h1.trans (hsumb.trans (div_le_div_of_nonneg_right
    (div_le_div_of_nonneg_right (hent' b) (hr i).le) (hr j).le))

end Main

end Balaban.Polymer
