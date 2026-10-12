module

public import Balaban.LargeField.Analytic.Constants
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Admissible sequences for Lemma CH, and the sequences `δ_j`, `δ_{j,1}` (Part III, Lemma III.4.5)

`IsAdmDelta d L ε k₁ k δ̄` collects the hypotheses of Lemma III.4.4 on the sequence
`(δ̄_i)_{k₁ ≤ i ≤ k}`: positive, nonincreasing, `δ̄_i ≤ e^ε L^{(d-2)/2 (j-i)} δ̄_j` for `i ≤ j`, and
`∑_{i ≥ i₀} δ̄_i ≤ 4 δ̄_{i₀}`.

`deltaRun_decay`, `deltaRun_growth`: the two estimates of the proof of Lemma III.4.5, in the running
notation of `Analytic/Constants.lean` (`runLam`, `deltaRun`, `RunningHyp`); `deltaSeq_admissible`
is Lemma III.4.5 for `δ̄ = δ`, and `deltaSeqOne_admissible` for `δ̄ = (δ_{i,1}) = (A₁/A₀) δ`.
-/

@[expose] public section

namespace Balaban.LargeField

open Finset

/-- The hypotheses of Lemma III.4.4 on a positive sequence `(δ̄_i)_{k₁ ≤ i ≤ k}`. -/
structure IsAdmDelta (d L : ℕ) (ε : ℝ) (k1 k : ℕ) (δ : ℕ → ℝ) : Prop where
  pos : ∀ i, k1 ≤ i → i ≤ k → 0 < δ i
  anti : ∀ i, k1 ≤ i → i < k → δ (i + 1) ≤ δ i
  growth : ∀ i j, k1 ≤ i → i ≤ j → j ≤ k →
    δ i ≤ Real.exp ε * (L : ℝ) ^ (((d : ℝ) - 2) / 2 * ((j : ℝ) - i)) * δ j
  tail : ∀ i, k1 ≤ i → i ≤ k → ∑ n ∈ Icc i k, δ n ≤ 4 * δ i

theorem IsAdmDelta.smul {d L : ℕ} {ε : ℝ} {k1 k : ℕ} {δ : ℕ → ℝ} (h : IsAdmDelta d L ε k1 k δ)
    {c : ℝ} (hc : 0 < c) : IsAdmDelta d L ε k1 k (fun i => c * δ i) where
  pos i h1 h2 := mul_pos hc (h.pos i h1 h2)
  anti i h1 h2 := mul_le_mul_of_nonneg_left (h.anti i h1 h2) hc.le
  growth i j h1 h2 h3 := by
    have := mul_le_mul_of_nonneg_left (h.growth i j h1 h2 h3) hc.le
    linarith
  tail i h1 h2 := by
    rw [← Finset.mul_sum]
    have := mul_le_mul_of_nonneg_left (h.tail i h1 h2) hc.le
    linarith

section Running

variable {d L p0 : ℕ} {β ν a ε A0 : ℝ} {b n : ℕ → ℝ}

omit n in
/-- `log L > 1` for `L ≥ 3`. -/
theorem one_lt_log_of_three_le (hL : 3 ≤ L) : 1 < Real.log L := by
  have h3 : (3 : ℝ) ≤ L := by exact_mod_cast hL
  have : Real.exp 1 < L := lt_of_lt_of_le Real.exp_one_lt_three h3
  rwa [Real.lt_log_iff_exp_lt (by linarith)]

/-- `λ_j - λ_i = (j - i) θ + log γ_j - log γ_i`: the two-sided bound used in Lemma III.4.5. -/
theorem RunningHyp.runLam_sub (h : RunningHyp d L β ν a ε b n) (i j : ℕ) :
    ((j : ℝ) - i) * thetaOf d L - 2 * ε ≤ runLam a b j - runLam a b i ∧
    runLam a b j - runLam a b i ≤ ((j : ℝ) - i) * thetaOf d L + 2 * ε := by
  obtain ⟨γ, hγ, he⟩ := h.runLam_eq j
  obtain ⟨γ', hγ', he'⟩ := h.runLam_eq i
  have e : runLam a b j - runLam a b i =
      ((j : ℝ) - i) * thetaOf d L + (Real.log γ - Real.log γ') := by
    rw [he, he']; unfold lamHat; ring
  rw [e]
  have h1 := abs_le.1 hγ
  have h2 := abs_le.1 hγ'
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- Bound `(1 + x)^p ≤ exp (p x)`. -/
theorem one_add_pow_le_exp {x : ℝ} (hx : 0 ≤ x) (p : ℕ) :
    (1 + x) ^ p ≤ Real.exp (p * x) := by
  calc (1 + x) ^ p ≤ (Real.exp x) ^ p :=
        pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp x]) p
    _ = Real.exp (p * x) := by rw [← Real.exp_nat_mul]

/-- The one-step comparison of `x ↦ A₀ e^{-x/2} x^{p₀}`: if `y ≤ x + c`, `12 p₀ ≤ x`, `0 ≤ y`,
`0 ≤ c`, then `δ(y) ≤ δ(x) e^{-(y-x)/2} e^{c/12}`. -/
theorem delta_exp_le {A0 : ℝ} (hA0 : 0 ≤ A0) {p0 : ℕ} {x y c : ℝ} (hx : 12 * (p0 : ℝ) ≤ x)
    (hy : 0 ≤ y) (hc : 0 ≤ c) (hyc : y ≤ x + c) :
    Real.exp (-y / 2) * (A0 * y ^ p0) ≤
      (Real.exp (-x / 2) * (A0 * x ^ p0)) * (Real.exp (-(y - x) / 2) * Real.exp (c / 12)) := by
  have hp : (0 : ℝ) ≤ p0 := Nat.cast_nonneg _
  have hxpos : 0 < x ∨ p0 = 0 := by
    rcases Nat.eq_zero_or_pos p0 with h0 | h0
    · exact Or.inr h0
    · left; have : (0 : ℝ) < p0 := by exact_mod_cast h0
      linarith
  rcases hxpos with hxpos | h0
  · have h1 : y ^ p0 ≤ x ^ p0 * Real.exp (c / 12) := by
      have h2 : y ^ p0 ≤ (x + c) ^ p0 := pow_le_pow_left₀ hy hyc p0
      have h3 : (x + c) ^ p0 = x ^ p0 * (1 + c / x) ^ p0 := by
        rw [← mul_pow]; congr 1; field_simp
      have h4 : (1 + c / x) ^ p0 ≤ Real.exp (p0 * (c / x)) :=
        one_add_pow_le_exp (div_nonneg hc hxpos.le) p0
      have h5 : (p0 : ℝ) * (c / x) ≤ c / 12 := by
        rw [← mul_div_assoc, div_le_iff₀ hxpos]
        nlinarith
      calc y ^ p0 ≤ (x + c) ^ p0 := h2
        _ = x ^ p0 * (1 + c / x) ^ p0 := h3
        _ ≤ x ^ p0 * Real.exp (c / 12) :=
          mul_le_mul_of_nonneg_left (h4.trans (Real.exp_le_exp.2 h5)) (by positivity)
    have e : Real.exp (-y / 2) = Real.exp (-x / 2) * Real.exp (-(y - x) / 2) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [e]
    calc Real.exp (-x / 2) * Real.exp (-(y - x) / 2) * (A0 * y ^ p0)
        ≤ Real.exp (-x / 2) * Real.exp (-(y - x) / 2) * (A0 * (x ^ p0 * Real.exp (c / 12))) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_left h1 hA0
      _ = _ := by ring
  · subst h0
    have e : Real.exp (-y / 2) = Real.exp (-x / 2) * Real.exp (-(y - x) / 2) := by
      rw [← Real.exp_add]; congr 1; ring
    have h12 : 1 ≤ Real.exp (c / 12) := Real.one_le_exp (by positivity)
    simp only [pow_zero, mul_one]
    rw [e]
    calc Real.exp (-x / 2) * Real.exp (-(y - x) / 2) * A0
        = Real.exp (-x / 2) * A0 * Real.exp (-(y - x) / 2) * 1 := by ring
      _ ≤ Real.exp (-x / 2) * A0 * Real.exp (-(y - x) / 2) * Real.exp (c / 12) :=
        mul_le_mul_of_nonneg_left h12 (by positivity)
      _ = _ := by ring

/-- `δ_{i+n} ≤ e^ε L^{-n/3} δ_i` (P7 (2.25)), the first estimate of Lemma III.4.5. -/
theorem deltaRun_decay (h : RunningHyp d L β ν a ε b n) (hd : 3 ≤ d) (hL : 3 ≤ L)
    (hA0 : 0 ≤ A0) (hlam : ∀ i, 12 * (p0 : ℝ) ≤ runLam a b i) (i m : ℕ) :
    deltaRun A0 p0 a b (i + m) ≤
      Real.exp ε * (L : ℝ) ^ (-(m : ℝ) / 3) * deltaRun A0 p0 a b i := by
  have ha : 0 < a := by linarith [h.ha1]
  rw [deltaRun_eq A0 p0 a b _ (mul_pos (h.betaRun_pos _) ha),
    deltaRun_eq A0 p0 a b _ (mul_pos (h.betaRun_pos _) ha)]
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have hlog := one_lt_log_of_three_le hL
  have hθ : Real.log L ≤ thetaOf d L := by
    unfold thetaOf
    have : (1 : ℝ) ≤ ((d - 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ d - 2)
    nlinarith
  have hε0 := h.hε0
  have hε1 := h.hε
  obtain ⟨hl1, hl2⟩ := h.runLam_sub i (i + m)
  have hm : ((i + m : ℕ) : ℝ) - i = m := by push_cast; ring
  rw [hm] at hl1 hl2
  have hx := hlam i
  have hy : 0 ≤ runLam a b (i + m) := by
    have := hlam (i + m); have : (0 : ℝ) ≤ p0 := Nat.cast_nonneg _; linarith
  set θ := thetaOf d L with hθdef
  have hmθ : 0 ≤ (m : ℝ) * θ := mul_nonneg (Nat.cast_nonneg _) (by linarith)
  have key := delta_exp_le hA0 hx hy (c := (m : ℝ) * θ + 2 * ε) (by linarith) (by linarith)
  have hXn : 0 ≤ Real.exp (-runLam a b i / 2) * (A0 * runLam a b i ^ p0) := by
    have : 0 ≤ runLam a b i := by
      have := hlam i; have : (0 : ℝ) ≤ p0 := Nat.cast_nonneg _; linarith
    positivity
  rcases Nat.eq_zero_or_pos m with h0 | hm0
  · subst h0
    simp only [Nat.add_zero, Nat.cast_zero, neg_zero, zero_div, Real.rpow_zero, mul_one]
    have : 1 ≤ Real.exp ε := Real.one_le_exp hε0
    nlinarith
  · refine key.trans ?_
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm0
    have hfac : Real.exp (-(runLam a b (i + m) - runLam a b i) / 2) * Real.exp (((m : ℝ) * θ + 2 * ε) / 12)
        ≤ Real.exp ε * (L : ℝ) ^ (-(m : ℝ) / 3) := by
      rw [← Real.exp_add, Real.rpow_def_of_pos hLpos, ← Real.exp_add]
      apply Real.exp_le_exp.2
      have h1 : (m : ℝ) * Real.log L ≤ (m : ℝ) * θ := mul_le_mul_of_nonneg_left hθ (Nat.cast_nonneg _)
      have h2 : (1 : ℝ) ≤ (m : ℝ) * Real.log L := by nlinarith
      nlinarith
    exact mul_le_mul_of_nonneg_left hfac hXn |>.trans_eq (by ring)

/-- `δ_i ≤ e^ε L^{(d-2)(j-i)/2} δ_j` for `i ≤ j` (the third estimate of Lemma III.4.5). -/
theorem deltaRun_growth (h : RunningHyp d L β ν a ε b n) (hd : 3 ≤ d) (hL : 3 ≤ L)
    (hA0 : 0 ≤ A0) (hlam : ∀ i, 12 * (p0 : ℝ) ≤ runLam a b i) {i j : ℕ} (hij : i ≤ j) :
    deltaRun A0 p0 a b i ≤
      Real.exp ε * (L : ℝ) ^ (((d : ℝ) - 2) / 2 * ((j : ℝ) - i)) * deltaRun A0 p0 a b j := by
  have ha : 0 < a := by linarith [h.ha1]
  rw [deltaRun_eq A0 p0 a b _ (mul_pos (h.betaRun_pos _) ha),
    deltaRun_eq A0 p0 a b _ (mul_pos (h.betaRun_pos _) ha)]
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have hlog := one_lt_log_of_three_le hL
  have hε0 := h.hε0
  have hε1 := h.hε
  obtain ⟨hl1, hl2⟩ := h.runLam_sub i j
  have hθe : thetaOf d L = ((d : ℝ) - 2) * Real.log L := by
    unfold thetaOf; congr 1; rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hθ1 : Real.log L ≤ thetaOf d L := by
    unfold thetaOf
    have : (1 : ℝ) ≤ ((d - 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ d - 2)
    nlinarith
  have hp : (0 : ℝ) ≤ p0 := Nat.cast_nonneg _
  have hxi := hlam i
  have hxj := hlam j
  have hxi0 : 0 ≤ runLam a b i := by linarith
  rcases Nat.eq_or_lt_of_le hij with he | hlt
  · subst he
    simp only [sub_self, mul_zero, Real.rpow_zero, mul_one]
    have : 0 ≤ Real.exp (-runLam a b i / 2) * (A0 * runLam a b i ^ p0) := by positivity
    nlinarith [Real.one_le_exp hε0]
  · have hm1 : (1 : ℝ) ≤ (j : ℝ) - i := by
      have : ((i + 1 : ℕ) : ℝ) ≤ j := by exact_mod_cast hlt
      push_cast at this; linarith
    have hlam_le : runLam a b i ≤ runLam a b j := by
      have : 0 ≤ ((j : ℝ) - i) * (thetaOf d L - 1) := by
        apply mul_nonneg (by linarith); linarith
      nlinarith
    have e1 : Real.exp (-runLam a b i / 2) =
        Real.exp (-runLam a b j / 2) * Real.exp ((runLam a b j - runLam a b i) / 2) := by
      rw [← Real.exp_add]; congr 1; ring
    have e2 : Real.exp ((runLam a b j - runLam a b i) / 2) ≤
        Real.exp ε * (L : ℝ) ^ (((d : ℝ) - 2) / 2 * ((j : ℝ) - i)) := by
      rw [Real.rpow_def_of_pos hLpos, ← Real.exp_add]
      apply Real.exp_le_exp.2
      rw [hθe] at hl2
      nlinarith
    have e3 : runLam a b i ^ p0 ≤ runLam a b j ^ p0 := pow_le_pow_left₀ hxi0 hlam_le p0
    rw [e1]
    have hE : 0 ≤ Real.exp (-runLam a b j / 2) := by positivity
    calc Real.exp (-runLam a b j / 2) * Real.exp ((runLam a b j - runLam a b i) / 2) *
          (A0 * runLam a b i ^ p0)
        ≤ Real.exp (-runLam a b j / 2) * (Real.exp ε * (L : ℝ) ^ (((d : ℝ) - 2) / 2 * ((j : ℝ) - i))) *
          (A0 * runLam a b j ^ p0) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left e2 hE) (mul_le_mul_of_nonneg_left e3 hA0)
            (by positivity) (by positivity)
      _ = _ := by ring

theorem deltaRun_pos (h : RunningHyp d L β ν a ε b n) (hA0 : 0 < A0) (hp0 : 1 ≤ p0)
    (hlam : ∀ i, 12 * (p0 : ℝ) ≤ runLam a b i) (i : ℕ) : 0 < deltaRun A0 p0 a b i := by
  have ha : 0 < a := by linarith [h.ha1]
  rw [deltaRun_eq A0 p0 a b _ (mul_pos (h.betaRun_pos _) ha)]
  have : (1 : ℝ) ≤ p0 := by exact_mod_cast hp0
  have : 0 < runLam a b i := by linarith [hlam i]
  positivity

/-- `L^{-1/3} ≤ 14/19` for `L ≥ 3`. -/
theorem rpow_neg_third_le {L : ℕ} (hL : 3 ≤ L) : (L : ℝ) ^ (-(1 : ℝ) / 3) ≤ 14 / 19 := by
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  set q := (L : ℝ) ^ (-(1 : ℝ) / 3) with hq
  have hq0 : 0 < q := Real.rpow_pos_of_pos hLpos _
  have hq3 : q ^ 3 = (L : ℝ)⁻¹ := by
    rw [hq, ← Real.rpow_natCast, ← Real.rpow_mul hLpos.le]
    norm_num
    exact Real.rpow_neg_one _
  have hL3 : (3 : ℝ) ≤ L := by exact_mod_cast hL
  have : q ^ 3 ≤ 1 / 3 := by
    rw [hq3]; rw [inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) hL3
  by_contra hcon
  push Not at hcon
  have := pow_lt_pow_left₀ hcon (by norm_num) (by norm_num : (3 : ℕ) ≠ 0)
  norm_num at this
  linarith

theorem rpow_neg_div_three {L : ℕ} (hL : 0 < L) (m : ℕ) :
    (L : ℝ) ^ (-(m : ℝ) / 3) = ((L : ℝ) ^ (-(1 : ℝ) / 3)) ^ m := by
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
  rw [← Real.rpow_natCast, ← Real.rpow_mul hLpos.le]
  congr 1; ring

/-- `∑_{n ≥ i} δ_n ≤ 4 δ_i` (the second estimate of Lemma III.4.5; truncated at `k`). -/
theorem deltaRun_tail (h : RunningHyp d L β ν a ε b n) (hd : 3 ≤ d) (hL : 3 ≤ L)
    (hA0 : 0 < A0) (hp0 : 1 ≤ p0) (hlam : ∀ i, 12 * (p0 : ℝ) ≤ runLam a b i) (i k : ℕ) :
    ∑ m ∈ Icc i k, deltaRun A0 p0 a b m ≤ 4 * deltaRun A0 p0 a b i := by
  have hLpos : 0 < L := by omega
  set q := (L : ℝ) ^ (-(1 : ℝ) / 3) with hq
  have hq0 : 0 < q := Real.rpow_pos_of_pos (by exact_mod_cast hLpos) _
  have hq1 : q ≤ 14 / 19 := rpow_neg_third_le hL
  have hdp := deltaRun_pos h hA0 hp0 hlam i
  have hε0 := h.hε0
  have hε1 := h.hε
  have hE : Real.exp ε ≤ 20 / 19 := by
    have := Real.exp_bound_div_one_sub_of_interval hε0 (by linarith : ε < 1)
    refine this.trans ?_
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  have hIcc : Icc i k = Ico i (k + 1) := by ext x; simp only [mem_Icc, mem_Ico]; omega
  rw [hIcc, Finset.sum_Ico_eq_sum_range]
  have hterm : ∀ t, deltaRun A0 p0 a b (i + t) ≤ Real.exp ε * q ^ t * deltaRun A0 p0 a b i := by
    intro t
    have := deltaRun_decay h hd hL hA0.le hlam i t
    rwa [rpow_neg_div_three hLpos] at this
  have hgeo : (1 - q) * ∑ t ∈ range (k + 1 - i), q ^ t ≤ 1 := by
    rw [mul_neg_geom_sum]
    have : 0 ≤ q ^ (k + 1 - i) := by positivity
    linarith
  calc ∑ t ∈ range (k + 1 - i), deltaRun A0 p0 a b (i + t)
      ≤ ∑ t ∈ range (k + 1 - i), Real.exp ε * q ^ t * deltaRun A0 p0 a b i :=
        Finset.sum_le_sum fun t _ => hterm t
    _ = Real.exp ε * deltaRun A0 p0 a b i * ∑ t ∈ range (k + 1 - i), q ^ t := by
        rw [Finset.mul_sum]; congr 1; ext t; ring
    _ ≤ 4 * deltaRun A0 p0 a b i := by
        set G := ∑ t ∈ range (k + 1 - i), q ^ t with hG
        have hG0 : 0 ≤ G := Finset.sum_nonneg fun t _ => by positivity
        have h1 : G ≤ 1 / (1 - q) := by
          rw [le_div_iff₀ (by linarith)]; linarith
        have h2 : G ≤ 19 / 5 := by
          refine h1.trans ?_
          rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
        have h3 : Real.exp ε * G ≤ 4 := by
          have : Real.exp ε * G ≤ (20 / 19) * (19 / 5) :=
            mul_le_mul hE h2 hG0 (by norm_num)
          linarith
        nlinarith

/-- **Lemma III.4.5.** If the running `λ_i ≥ 12 p₀` for all `i` ((Λ20)), then `δ̄ = δ` satisfies the
hypotheses of Lemma III.4.4 on every range `k₁ ≤ i ≤ k`. -/
theorem deltaSeq_admissible (h : RunningHyp d L β ν a ε b n) (hd : 3 ≤ d) (hL : 3 ≤ L)
    (hA0 : 0 < A0) (hp0 : 1 ≤ p0) (hlam : ∀ i, 12 * (p0 : ℝ) ≤ runLam a b i) (k1 k : ℕ) :
    IsAdmDelta d L ε k1 k (deltaRun A0 p0 a b) where
  pos i _ _ := deltaRun_pos h hA0 hp0 hlam i
  anti i _ _ := by
    have h1 := deltaRun_decay h hd hL hA0.le hlam i 1
    have hLpos : 0 < L := by omega
    rw [rpow_neg_div_three hLpos] at h1
    have hq1 := rpow_neg_third_le hL
    have hq0 : 0 < (L : ℝ) ^ (-(1 : ℝ) / 3) := Real.rpow_pos_of_pos (by exact_mod_cast hLpos) _
    have hε0 := h.hε0
    have hε1 := h.hε
    have hE : Real.exp ε ≤ 20 / 19 := by
      have := Real.exp_bound_div_one_sub_of_interval hε0 (by linarith : ε < 1)
      refine this.trans ?_
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]
      linarith
    have hd0 := deltaRun_pos h hA0 hp0 hlam i
    have : Real.exp ε * (L : ℝ) ^ (-(1 : ℝ) / 3) ≤ 1 := by
      have := mul_le_mul hE hq1 hq0.le (by norm_num)
      linarith
    calc deltaRun A0 p0 a b (i + 1) ≤ Real.exp ε * ((L : ℝ) ^ (-(1 : ℝ) / 3)) ^ 1 *
          deltaRun A0 p0 a b i := h1
      _ ≤ deltaRun A0 p0 a b i := by
        rw [pow_one]; nlinarith
  growth i j _ hij _ := deltaRun_growth h hd hL hA0.le hlam hij
  tail i _ _ := deltaRun_tail h hd hL hA0 hp0 hlam i k

/-- Lemma III.4.5 for `δ̄ = (δ_{i,1}) = (A₁/A₀) δ`. -/
theorem deltaSeqOne_admissible (h : RunningHyp d L β ν a ε b n) (hd : 3 ≤ d) (hL : 3 ≤ L)
    (hA0 : 0 < A0) {A1 : ℝ} (hA1 : 0 < A1) (hp0 : 1 ≤ p0)
    (hlam : ∀ i, 12 * (p0 : ℝ) ≤ runLam a b i) (k1 k : ℕ) :
    IsAdmDelta d L ε k1 k (fun i => A1 / A0 * deltaRun A0 p0 a b i) :=
  (deltaSeq_admissible h hd hL hA0 hp0 hlam k1 k).smul (div_pos hA1 hA0)

end Running

end Balaban.LargeField
