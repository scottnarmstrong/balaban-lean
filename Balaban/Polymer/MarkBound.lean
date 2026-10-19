/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.Mayer
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Product bounds for the Mayer terms from ordinary and heavy marks

`notes/phase1/KF0-FR.md` (G2). Let the variables of a product of probability measures be indexed by
sites `x ∈ V`, each with an *ordinary* set `O_x`. Let terms `f_t` read the sites `S_t`. Suppose

* (ordinary) `‖f_t‖ ≤ ε_t` whenever all the sites of `S_t` are ordinary;
* (heavy) for every family `C` of terms and every set `H` of sites read by `C`, the expectation of
  the product of the norms of the terms of `C` that read `H`, on the event that the sites of `H`
  are not ordinary and the other sites read by `C` are, is at most `θ^{|H|}`;
* every site is read by at most `k` terms.

Then every family `C` has `‖∫ ∏_{t ∈ C} f_t‖ ≤ ∏_{t ∈ C} (1 + √θ)^{|S_t|} (ε_t + θ^{1/(2k)} |S_t|)`
(`norm_integral_prod_le_marks`). The heavy smallness `θ` is spread over the at most `k` terms that
read a heavy site (`sum_marks_le`, the combinatorial part). This is the product bound consumed by
`mayerGen_activity_bound`.
-/

@[expose] public section

noncomputable section

open scoped Classical

open Finset MeasureTheory

namespace Balaban.Polymer

section Comb

variable {T V : Type*}

/-- **The combinatorial part of the mark bound**: for `0 < θ ≤ 1`, `a = θ^{1/(2k)}` and every site
read by at most `k` terms of `C`,
`∑_{H ⊆ V(C)} θ^{|H|} ∏_{t ∈ C, S_t ∩ H = ∅} ε_t ≤ ∏_{t ∈ C} (1 + √θ)^{|S_t|} (ε_t + a |S_t|)`. -/
theorem sum_marks_le (C : Finset T) (S : T → Finset V) (ε : T → ℝ) (hε : ∀ t, 0 ≤ ε t)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) {k : ℕ} (hk : 1 ≤ k)
    (hmult : ∀ x, (C.filter (fun t => x ∈ S t)).card ≤ k) :
    ∑ H ∈ (C.biUnion S).powerset, θ ^ H.card * ∏ t ∈ C.filter (fun t => Disjoint (S t) H), ε t ≤
      ∏ t ∈ C, ((1 + Real.sqrt θ) ^ (S t).card *
        (ε t + θ ^ ((1 : ℝ) / (2 * k)) * (S t).card)) := by
  set a : ℝ := θ ^ ((1 : ℝ) / (2 * k)) with ha
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have ha0 : 0 < a := Real.rpow_pos_of_pos hθ0 _
  have ha1 : a ≤ 1 := Real.rpow_le_one hθ0.le hθ1 (by positivity)
  have hak : a ^ k = Real.sqrt θ := by
    rw [ha, ← Real.rpow_natCast, ← Real.rpow_mul hθ0.le, Real.sqrt_eq_rpow]
    congr 1; field_simp
  have hs0 : 0 < Real.sqrt θ := Real.sqrt_pos.2 hθ0
  -- the bound for one set `H`
  have hH : ∀ H : Finset V, θ ^ H.card * ∏ t ∈ C.filter (fun t => Disjoint (S t) H), ε t ≤
      Real.sqrt θ ^ H.card * ∏ t ∈ C, (ε t + a * (S t).card) := by
    intro H
    have hpt : ∀ t ∈ C, (if Disjoint (S t) H then ε t else 1) ≤
        (ε t + a * (S t).card) * (if Disjoint (S t) H then 1 else a⁻¹) := by
      intro t _
      split_ifs with hd
      · simp only [mul_one]; nlinarith [hε t, ha0.le, (Nat.cast_nonneg (S t).card : (0 : ℝ) ≤ _)]
      · have hne : (S t).Nonempty := by
          by_contra h0
          rw [Finset.not_nonempty_iff_eq_empty] at h0
          exact hd (h0 ▸ Finset.disjoint_empty_left H)
        have hc : (1 : ℝ) ≤ (S t).card := by exact_mod_cast hne.card_pos
        have hca : a * ((S t).card * a⁻¹) = (S t).card := by field_simp
        rw [add_mul, mul_assoc, hca]
        nlinarith [mul_nonneg (hε t) (inv_nonneg.2 ha0.le)]
    have h1 : ∏ t ∈ C.filter (fun t => Disjoint (S t) H), ε t =
        ∏ t ∈ C, (if Disjoint (S t) H then ε t else 1) := by rw [Finset.prod_ite, Finset.prod_const_one, mul_one]
    have h2 : ∏ t ∈ C, (if Disjoint (S t) H then ε t else 1) ≤
        ∏ t ∈ C, ((ε t + a * (S t).card) * (if Disjoint (S t) H then 1 else a⁻¹)) :=
      Finset.prod_le_prod₀ (fun t _ => by split_ifs <;> [exact hε t; exact zero_le_one]) hpt
    have hcard : (C.filter (fun t => ¬ Disjoint (S t) H)).card ≤ k * H.card := by
      have hsub : C.filter (fun t => ¬ Disjoint (S t) H) ⊆
          H.biUnion (fun x => C.filter (fun t => x ∈ S t)) := by
        intro t ht
        rw [Finset.mem_filter, Finset.not_disjoint_iff] at ht
        obtain ⟨htC, x, hxS, hxH⟩ := ht
        exact Finset.mem_biUnion.2 ⟨x, hxH, Finset.mem_filter.2 ⟨htC, hxS⟩⟩
      refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
      calc ∑ x ∈ H, (C.filter (fun t => x ∈ S t)).card ≤ ∑ _x ∈ H, k :=
            Finset.sum_le_sum fun x _ => hmult x
        _ = k * H.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    have h3 : ∏ t ∈ C, (if Disjoint (S t) H then (1 : ℝ) else a⁻¹) ≤ (a⁻¹) ^ (k * H.card) := by
      rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]
      exact pow_le_pow_right₀ (one_le_inv₀ ha0 |>.2 ha1) hcard
    have h4 : θ ^ H.card * (a⁻¹) ^ (k * H.card) = Real.sqrt θ ^ H.card := by
      rw [pow_mul, inv_pow, hak, show θ ^ H.card = Real.sqrt θ ^ H.card * Real.sqrt θ ^ H.card by
        rw [← mul_pow, Real.mul_self_sqrt hθ0.le]]
      rw [mul_assoc, ← mul_pow, mul_inv_cancel₀ hs0.ne', one_pow, mul_one]
    rw [h1]
    calc θ ^ H.card * ∏ t ∈ C, (if Disjoint (S t) H then ε t else 1)
        ≤ θ ^ H.card * ∏ t ∈ C, ((ε t + a * (S t).card) * (if Disjoint (S t) H then 1 else a⁻¹)) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = θ ^ H.card * (∏ t ∈ C, (if Disjoint (S t) H then (1 : ℝ) else a⁻¹)) *
            ∏ t ∈ C, (ε t + a * (S t).card) := by
          rw [Finset.prod_mul_distrib, mul_comm (∏ t ∈ C, (ε t + a * (S t).card)), ← mul_assoc]
      _ ≤ θ ^ H.card * (a⁻¹) ^ (k * H.card) * ∏ t ∈ C, (ε t + a * (S t).card) := by
          gcongr
          · exact Finset.prod_nonneg fun t _ => add_nonneg (hε t) (mul_nonneg ha0.le (Nat.cast_nonneg _))
      _ = Real.sqrt θ ^ H.card * ∏ t ∈ C, (ε t + a * (S t).card) := by rw [h4]
  have hsum : ∑ H ∈ (C.biUnion S).powerset, Real.sqrt θ ^ H.card =
      (1 + Real.sqrt θ) ^ (C.biUnion S).card := by
    have := Finset.prod_one_add (f := fun _ : V => Real.sqrt θ) (C.biUnion S)
    simp only [Finset.prod_const] at this
    rw [← this]
  calc ∑ H ∈ (C.biUnion S).powerset, θ ^ H.card * ∏ t ∈ C.filter (fun t => Disjoint (S t) H), ε t
      ≤ ∑ H ∈ (C.biUnion S).powerset, Real.sqrt θ ^ H.card * ∏ t ∈ C, (ε t + a * (S t).card) :=
        Finset.sum_le_sum fun H _ => hH H
    _ = (1 + Real.sqrt θ) ^ (C.biUnion S).card * ∏ t ∈ C, (ε t + a * (S t).card) := by
        rw [← Finset.sum_mul, hsum]
    _ ≤ (1 + Real.sqrt θ) ^ (∑ t ∈ C, (S t).card) * ∏ t ∈ C, (ε t + a * (S t).card) := by
        gcongr
        · exact Finset.prod_nonneg fun t _ => add_nonneg (hε t) (mul_nonneg ha0.le (Nat.cast_nonneg _))
        · linarith
        · exact Finset.card_biUnion_le
    _ = ∏ t ∈ C, ((1 + Real.sqrt θ) ^ (S t).card * (ε t + a * (S t).card)) := by
        rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]

end Comb

section Measure

variable {V : Type*} [Fintype V] {Ω : V → Type*} [∀ x, MeasurableSpace (Ω x)]
  (μ : ∀ x, Measure (Ω x)) [∀ x, IsProbabilityMeasure (μ x)]
  {T : Type*}

/-- The event that the sites of `H` are not ordinary and the other sites of `W` are. -/
def MarkEvent (O : ∀ x, Set (Ω x)) (W H : Finset V) (ω : ∀ x, Ω x) : Prop :=
  (∀ x ∈ H, ω x ∉ O x) ∧ ∀ x ∈ W, x ∉ H → ω x ∈ O x

omit [Fintype V] in
theorem measurableSet_markEvent {O : ∀ x, Set (Ω x)} (hO : ∀ x, MeasurableSet (O x))
    (W H : Finset V) : MeasurableSet {ω : ∀ x, Ω x | MarkEvent O W H ω} := by
  have : {ω : ∀ x, Ω x | MarkEvent O W H ω} =
      (⋂ x ∈ H, Function.eval x ⁻¹' (O x)ᶜ) ∩ ⋂ x ∈ W.filter (fun x => x ∉ H),
        Function.eval x ⁻¹' O x := by
    ext ω
    simp only [MarkEvent, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage,
      Function.eval, Set.mem_compl_iff, Finset.mem_filter]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, fun x ⟨hx, hxH⟩ => h2 x hx hxH⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, fun x hx hxH => h2 x ⟨hx, hxH⟩⟩
  rw [this]
  refine MeasurableSet.inter (Finset.measurableSet_biInter _ fun x _ =>
    measurable_pi_apply x (hO x).compl) (Finset.measurableSet_biInter _ fun x _ =>
      measurable_pi_apply x (hO x))

omit [Fintype V] [∀ x, MeasurableSpace (Ω x)] in
/-- Every configuration is in exactly one mark event: the one of its non-ordinary sites. -/
theorem sum_markEvent_indicator (O : ∀ x, Set (Ω x)) (W : Finset V) (ω : ∀ x, Ω x) :
    ∑ H ∈ W.powerset, (if MarkEvent O W H ω then (1 : ℂ) else 0) = 1 := by
  set H₀ := W.filter (fun x => ω x ∉ O x)
  have h0 : MarkEvent O W H₀ ω := by
    refine ⟨fun x hx => (Finset.mem_filter.1 hx).2, fun x hx hxH => ?_⟩
    by_contra hxO
    exact hxH (Finset.mem_filter.2 ⟨hx, hxO⟩)
  have huniq : ∀ H ∈ W.powerset, MarkEvent O W H ω → H = H₀ := by
    intro H hH hm
    rw [Finset.mem_powerset] at hH
    ext x
    constructor
    · intro hx; exact Finset.mem_filter.2 ⟨hH hx, hm.1 x hx⟩
    · intro hx
      obtain ⟨hxW, hxO⟩ := Finset.mem_filter.1 hx
      by_contra hxH
      exact hxO (hm.2 x hxW hxH)
  rw [Finset.sum_eq_single H₀ (fun H hH hne => by rw [ite_eq_right (fun h => hne (huniq H hH h))])
    (fun h => absurd (Finset.mem_powerset.2 (Finset.filter_subset _ _)) h), ite_eq_left h0]

omit [∀ x, IsProbabilityMeasure (μ x)] in
/-- **The product bound from ordinary and heavy marks.** -/
theorem norm_integral_prod_le_marks (O : ∀ x, Set (Ω x)) (hO : ∀ x, MeasurableSet (O x))
    (S : T → Finset V) (f : T → (∀ x, Ω x) → ℂ) (hfm : ∀ t, Measurable (f t)) (C : Finset T)
    (hint : Integrable (fun ω => ∏ t ∈ C, f t ω) (Measure.pi μ))
    (ε : T → ℝ) (hε0 : ∀ t, 0 ≤ ε t)
    (hord : ∀ t ω, (∀ x ∈ S t, ω x ∈ O x) → ‖f t ω‖ ≤ ε t)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) {k : ℕ} (hk : 1 ≤ k)
    (hmult : ∀ x, (C.filter (fun t => x ∈ S t)).card ≤ k)
    (hheavy : ∀ H ⊆ C.biUnion S, ∫⁻ ω, Set.indicator {ω | MarkEvent O (C.biUnion S) H ω}
        (fun ω => ∏ t ∈ C.filter (fun t => ¬ Disjoint (S t) H), ‖f t ω‖ₑ) ω ∂(Measure.pi μ) ≤
      ENNReal.ofReal (θ ^ H.card)) :
    ‖∫ ω, ∏ t ∈ C, f t ω ∂(Measure.pi μ)‖ ≤
      ∏ t ∈ C, ((1 + Real.sqrt θ) ^ (S t).card *
        (ε t + θ ^ ((1 : ℝ) / (2 * k)) * (S t).card)) := by
  set W := C.biUnion S
  have hsplit : ∫ ω, ∏ t ∈ C, f t ω ∂(Measure.pi μ) =
      ∑ H ∈ W.powerset, ∫ ω, (if MarkEvent O W H ω then (1 : ℂ) else 0) * ∏ t ∈ C, f t ω
        ∂(Measure.pi μ) := by
    rw [← integral_finsetSum]
    · refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
      simp only
      rw [← Finset.sum_mul, sum_markEvent_indicator, one_mul]
    · intro H _
      refine hint.mono ((Measurable.ite (measurableSet_markEvent hO W H) measurable_const
        measurable_const).mul (Finset.measurable_prod _ fun t _ => hfm t)).aestronglyMeasurable
        (Filter.Eventually.of_forall fun ω => ?_)
      rw [norm_mul]
      split_ifs
      · simp
      · simp only [norm_zero, zero_mul]
        exact norm_nonneg _
  have hterm : ∀ H ∈ W.powerset, ‖∫ ω, (if MarkEvent O W H ω then (1 : ℂ) else 0) *
      ∏ t ∈ C, f t ω ∂(Measure.pi μ)‖ ≤
      θ ^ H.card * ∏ t ∈ C.filter (fun t => Disjoint (S t) H), ε t := by
    intro H hH
    rw [Finset.mem_powerset] at hH
    have hpt : ∀ ω, ‖(if MarkEvent O W H ω then (1 : ℂ) else 0) * ∏ t ∈ C, f t ω‖ₑ ≤
        ENNReal.ofReal (∏ t ∈ C.filter (fun t => Disjoint (S t) H), ε t) *
          Set.indicator {ω | MarkEvent O W H ω}
            (fun ω => ∏ t ∈ C.filter (fun t => ¬ Disjoint (S t) H), ‖f t ω‖ₑ) ω := by
      intro ω
      by_cases hm : MarkEvent O W H ω
      · have henorm : ‖∏ t ∈ C, f t ω‖ₑ = ∏ t ∈ C, ‖f t ω‖ₑ := by
          rw [← ofReal_norm, norm_prod, ENNReal.ofReal_prod_of_nonneg (fun _ _ => norm_nonneg _)]
          simp only [ofReal_norm]
        rw [ite_eq_left hm, one_mul, Set.indicator_of_mem (by exact hm), henorm,
          ← Finset.prod_filter_mul_prod_filter_not C (fun t => Disjoint (S t) H)]
        refine mul_le_mul' ?_ le_rfl
        rw [ENNReal.ofReal_prod_of_nonneg (fun t _ => hε0 t)]
        refine Finset.prod_le_prod fun t ht => ?_
        rw [← ofReal_norm]
        refine ENNReal.ofReal_le_ofReal (hord t ω fun x hx => ?_)
        have htC := (Finset.mem_filter.1 ht).1
        have hdisj := (Finset.mem_filter.1 ht).2
        refine hm.2 x (Finset.mem_biUnion.2 ⟨t, htC, hx⟩) fun hxH => ?_
        exact Finset.disjoint_left.1 hdisj hx hxH
      · rw [ite_eq_right hm, zero_mul, enorm_zero]
        exact bot_le
    have hle : ‖∫ ω, (if MarkEvent O W H ω then (1 : ℂ) else 0) * ∏ t ∈ C, f t ω
        ∂(Measure.pi μ)‖ₑ ≤ ENNReal.ofReal (∏ t ∈ C.filter (fun t => Disjoint (S t) H), ε t) *
          ENNReal.ofReal (θ ^ H.card) := by
      refine (enorm_integral_le_lintegral_enorm _).trans ((lintegral_mono hpt).trans ?_)
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      exact mul_le_mul' le_rfl (hheavy H hH)
    rw [← ENNReal.ofReal_mul (Finset.prod_nonneg fun t _ => hε0 t)] at hle
    have := (ENNReal.toReal_le_toReal enorm_ne_top ENNReal.ofReal_ne_top).2 hle
    rw [toReal_enorm, ENNReal.toReal_ofReal (mul_nonneg (Finset.prod_nonneg fun t _ => hε0 t)
      (pow_nonneg hθ0.le _))] at this
    linarith
  rw [hsplit]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hterm).trans ?_)
  exact sum_marks_le C S ε hε0 hθ0 hθ1 hk hmult

end Measure

end Balaban.Polymer
