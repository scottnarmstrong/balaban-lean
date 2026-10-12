module

public import Balaban.Polymer.MayerMarked

/-!
# Termwise bound for the marked local terms (PE-M, Cauchy estimate)

`mayer_marked_termwise`: under the hypotheses of `mayer_marked`, each local term obeys
`‖∂_i P(Y)‖ e^{κ'(d Y + c_P)} ≤ α / r_i` for `Y ∋ b`, `b ∈ S_i` (the Cauchy estimate
`sum_norm_D1_Ff_le`, applied to a single term).
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

/-- **Termwise Cauchy bound** for the local terms `∂_i P(Y)` of `mayer_marked`:
`‖∂_i P(Y)‖ e^{κ'(d Y + c_P)} ≤ α / r_i` for `Y ∋ b`, `b ∈ S_i`. -/
theorem mayer_marked_termwise (hne : ∀ t, (sup t).Nonempty) (hr : ∀ i, 0 < r i)
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
    (marksXi μ a g 0 = Complex.exp (∑ Y : Finset B,
      Ff (shareBlock (Subtype.val : NePoly B → Finset B)) Subtype.val (marksK μ sup a g) Y 0)) ∧
    (∀ (b : B) (Y : Finset B), b ∈ Y →
      ‖Ff (shareBlock (Subtype.val : NePoly B → Finset B)) Subtype.val (marksK μ sup a g) Y 0‖ *
        Real.exp (κ' * (d Y + cP)) ≤
        2 * (2 * H0 * K0 * Real.exp (κ1 * c)) * c1 * K0P * Real.exp (c1 + κ' * cP)) ∧
    (∀ i, D1 i (marksXi μ a g) / marksXi μ a g 0 =
      ∑ Y : Finset B, D1 i (Ff (shareBlock (Subtype.val : NePoly B → Finset B)) Subtype.val
        (marksK μ sup a g) Y)) ∧
    (∀ (i : ι) (Y : Finset B), ¬ S i ⊆ Y →
      D1 i (Ff (shareBlock (Subtype.val : NePoly B → Finset B)) Subtype.val
        (marksK μ sup a g) Y) = 0) ∧
    ∀ (i : ι) {b : B}, b ∈ S i → ∀ Y : Finset B, b ∈ Y →
      ‖D1 i (Ff (shareBlock (Subtype.val : NePoly B → Finset B)) Subtype.val
        (marksK μ sup a g) Y)‖ * Real.exp (κ' * (d Y + cP)) ≤
        (2 * (2 * H0 * K0 * Real.exp (κ1 * c)) * c1 * K0P * Real.exp (c1 + κ' * cP)) / r i := by
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
  have hW := sizeW_nonneg (κ := κ1 - 3 / 2) (κ' := κ') (c := cP) (Subtype.val : NePoly B → Finset B) d hε0
  have hent := size_entropy (Subtype.val : NePoly B → Finset B) d (κ := κ1 - 3 / 2) (κ' := κ')
    (κ0 := κ0P) (K0 := K0P) (c := cP) (c1 := c1) hε0 hd hG1 hG2P hκ hα1
  have hKP := kp_of_entropy (Subtype.val : NePoly B → Finset B) _ hW hent
  have hg0 : ∀ Y : Finset B, 0 ≤ κ' * (d Y + cP) := fun Y => by have := hd Y; positivity
  have hb : ∀ (Z : NePoly B), ∀ l ∈ polydisc (0 : ι → ℂ) r,
      ‖marksK μ sup a g Z l‖ ≤ sizeW (Subtype.val : NePoly B → Finset B) d ε (κ1 - 3 / 2) κ' cP Z := by
    intro Z l hl
    refine (hKbd Z l hl).trans ?_
    unfold sizeW
    calc ε * Real.exp (-(κ1 - 3 / 2) * d Z.1) = ε * Real.exp (-(κ1 - 3 / 2) * d Z.1) * 1 := by
          rw [mul_one]
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.one_le_exp (by
          have := hg0 Z.1; simpa using this)) (by positivity)
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
        Real.exp (α * (x.1.card : ℝ)) else 0) ≤ α := hent
  have h0 := zero_mem_polydisc hr
  refine ⟨?_, ?_, fun i => D1_Zf_div inc Subtype.val hKP hr hKan hb hrefl _ hZ i,
    fun i Y hY => D1_Ff_eq_zero inc Subtype.val hKP hr hKan hb hdep hY, ?_⟩
  · rw [Zf_eq_exp inc hKP hb hrefl _ hZ h0, Lf_eq_sum_Ff inc Subtype.val hKP hb h0]
  · intro b Y hbY
    have hsum0 := pe_PY_bound inc Subtype.val (fun Y : Finset B => κ' * (d Y + cP)) 0 le_rfl hg0 hG3'
      (κ0 := fun x => ε * Real.exp (-(κ1 - 3 / 2) * d x.1)) (fun x => rfl) hKP
      (fun Z => marksK μ sup a g Z 0) (fun x => hKbd x 0 h0) b
    have h1 : ‖PY inc Subtype.val (fun Z => marksK μ sup a g Z 0) Y‖ * Real.exp (κ' * (d Y + cP)) ≤
        ∑ Y ∈ (Finset.univ : Finset (Finset B)).filter (fun Y => b ∈ Y),
          ‖PY inc Subtype.val (fun Z => marksK μ sup a g Z 0) Y‖ * Real.exp (κ' * (d Y + cP)) :=
      Finset.single_le_sum (f := fun Y => ‖PY inc Subtype.val (fun Z => marksK μ sup a g Z 0) Y‖ *
        Real.exp (κ' * (d Y + cP))) (fun _ _ => by positivity)
        (Finset.mem_filter.2 ⟨Finset.mem_univ _, hbY⟩)
    exact h1.trans (hsum0.trans (hent' b))
  intro i b hbS Y hbY
  have hsumb := sum_norm_D1_Ff_le inc Subtype.val hKP hr hKan hb
    (fun Y : Finset B => κ' * (d Y + cP)) 0 le_rfl hg0 hG3'
    (κ0 := fun x => ε * Real.exp (-(κ1 - 3 / 2) * d x.1)) (fun x => rfl)
    (fun x l hl => hKbd x l hl) b i
  have h1 : Real.exp (κ' * (d Y + cP)) * ‖D1 i (Ff inc Subtype.val (marksK μ sup a g) Y)‖ ≤
      ∑ Y ∈ (Finset.univ : Finset (Finset B)).filter (fun Y => b ∈ Y),
        Real.exp (κ' * (d Y + cP)) * ‖D1 i (Ff inc Subtype.val (marksK μ sup a g) Y)‖ :=
    Finset.single_le_sum (f := fun Y => Real.exp (κ' * (d Y + cP)) *
      ‖D1 i (Ff inc Subtype.val (marksK μ sup a g) Y)‖) (fun _ _ => by positivity)
      (Finset.mem_filter.2 ⟨Finset.mem_univ _, hbY⟩)
  rw [mul_comm]
  exact h1.trans (hsumb.trans (div_le_div_of_nonneg_right (hent' b) (hr i).le))

end Main

end Balaban.Polymer
