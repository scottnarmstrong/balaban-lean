/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.Local

/-!
# Closeness of the local terms of the cluster sum

Two activities `K, K₂` on the same polymer system, both dominated by `κ₀`, whose difference on a
polymer `x` is at most `κ₀(x) e^{-λ m(supp x)}` for a nonnegative function `m` of the supports that
decreases under inclusion (a margin: `m(Y) ≤ m(X)` for `X ⊆ Y`), have local terms of the cluster sum
`P(Y)` (`PY`) with

`∑_{Y ∋ □} |P_K(Y) - P_{K₂}(Y)| e^{g(Y) + λ m(Y)} ≤ ∑_{x ∋ □} κ(x) e^{a(x)}`,

`κ = 2 κ₀ e^{g + c}` with the Kotecký–Preiss condition (`pe_PY_sub_bound`): the bound of
`pe_PY_bound` with the weights doubled, and the margin factor `e^{-λ m(Y)}` of the union. The
difference of the products of the activities of a cluster is telescoped (`norm_prod_sub_prod_le`,
`norm_prod_sub_prod_le_two`) and the cluster sum is bounded by the general-coefficient core
`pe_PYGen_bound` (`Polymer/Local.lean`). For two polymer systems related by a map of blocks
injective on the support, the transport `PY_transport` reduces the comparison to one system
(`PY_sub_bound_of_transport`).
-/

@[expose] public section

noncomputable section

open scoped Classical

open Finset

namespace Balaban.Polymer

section Telescope

variable {ι : Type*}

/-- **Telescoping of a product.** If `|a_i|, |b_i| ≤ w_i` and `|a_i - b_i| ≤ r w_i` on `s`, then
`|∏_s a - ∏_s b| ≤ |s| r ∏_s w`. -/
theorem norm_prod_sub_prod_le (s : Finset ι) (a b : ι → ℂ) (w : ι → ℝ) {r : ℝ} (hr : 0 ≤ r)
    (ha : ∀ i ∈ s, ‖a i‖ ≤ w i) (hb : ∀ i ∈ s, ‖b i‖ ≤ w i)
    (hab : ∀ i ∈ s, ‖a i - b i‖ ≤ r * w i) :
    ‖∏ i ∈ s, a i - ∏ i ∈ s, b i‖ ≤ (s.card : ℝ) * r * ∏ i ∈ s, w i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    have ha' : ∀ i ∈ s, ‖a i‖ ≤ w i := fun i hi => ha i (Finset.mem_insert_of_mem hi)
    have hb' : ∀ i ∈ s, ‖b i‖ ≤ w i := fun i hi => hb i (Finset.mem_insert_of_mem hi)
    have hab' : ∀ i ∈ s, ‖a i - b i‖ ≤ r * w i := fun i hi => hab i (Finset.mem_insert_of_mem hi)
    have hw : ∀ i ∈ insert j s, 0 ≤ w i := fun i hi => (norm_nonneg _).trans (ha i hi)
    have hwj := hw j (Finset.mem_insert_self j s)
    have hPw : 0 ≤ ∏ i ∈ s, w i := Finset.prod_nonneg fun i hi => hw i (Finset.mem_insert_of_mem hi)
    have hPa : ‖∏ i ∈ s, a i‖ ≤ ∏ i ∈ s, w i := by
      rw [norm_prod]
      exact Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) ha'
    rw [Finset.prod_insert hj, Finset.prod_insert hj, Finset.prod_insert hj,
      Finset.card_insert_of_notMem hj]
    have e : a j * ∏ i ∈ s, a i - b j * ∏ i ∈ s, b i =
        (a j - b j) * ∏ i ∈ s, a i + b j * (∏ i ∈ s, a i - ∏ i ∈ s, b i) := by ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    have h1 : ‖a j - b j‖ * ‖∏ i ∈ s, a i‖ ≤ r * w j * ∏ i ∈ s, w i :=
      mul_le_mul (hab j (Finset.mem_insert_self j s)) hPa (norm_nonneg _) (by positivity)
    have h2 : ‖b j‖ * ‖∏ i ∈ s, a i - ∏ i ∈ s, b i‖ ≤ w j * ((s.card : ℝ) * r * ∏ i ∈ s, w i) :=
      mul_le_mul (hb j (Finset.mem_insert_self j s)) (ih ha' hb' hab') (norm_nonneg _) hwj
    push_cast
    nlinarith

/-- The telescoping bound with the cardinality absorbed into doubled weights:
`|∏_s a - ∏_s b| ≤ r ∏_s (2 w)`. -/
theorem norm_prod_sub_prod_le_two (s : Finset ι) (a b : ι → ℂ) (w : ι → ℝ) {r : ℝ} (hr : 0 ≤ r)
    (ha : ∀ i ∈ s, ‖a i‖ ≤ w i) (hb : ∀ i ∈ s, ‖b i‖ ≤ w i)
    (hab : ∀ i ∈ s, ‖a i - b i‖ ≤ r * w i) :
    ‖∏ i ∈ s, a i - ∏ i ∈ s, b i‖ ≤ r * ∏ i ∈ s, (2 * w i) := by
  refine (norm_prod_sub_prod_le s a b w hr ha hb hab).trans ?_
  have hw : 0 ≤ ∏ i ∈ s, w i := Finset.prod_nonneg fun i hi => (norm_nonneg _).trans (ha i hi)
  rw [Finset.prod_mul_distrib, Finset.prod_const]
  have hc : (s.card : ℝ) ≤ 2 ^ s.card := by
    exact_mod_cast (Nat.lt_two_pow_self).le
  calc (s.card : ℝ) * r * ∏ i ∈ s, w i ≤ 2 ^ s.card * r * ∏ i ∈ s, w i := by gcongr
    _ = _ := by ring

end Telescope

section Close

variable {P : Type*} [Fintype P] (inc : P → P → Prop) {B : Type*} [Fintype B]
  (supp : P → Finset B) {κ0 κ a : P → ℝ}

omit [Fintype B] in
/-- The local terms of the difference: `P_K(Y) - P_{K₂}(Y)` is the sum of the cluster terms with
the coefficients `∏ K - ∏ K₂`. -/
theorem PY_sub_eq_tsum_PtermGen (h : KPCond inc κ a) (K K₂ : P → ℂ) (hK : ∀ x, ‖K x‖ ≤ κ x)
    (hK₂ : ∀ x, ‖K₂ x‖ ≤ κ x) (Y : Finset B) :
    PY inc supp K Y - PY inc supp K₂ Y =
      ∑' n, PtermGen inc supp (fun _ X => ∏ i, K (X i) - ∏ i, K₂ (X i)) Y n := by
  have hs : ∀ K' : P → ℂ, (∀ x, ‖K' x‖ ≤ κ x) → Summable (fun n => Pterm inc supp K' Y n) :=
    fun K' hK' => Summable.of_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (norm_Pterm_le inc supp K' hK' Y) (summable_sp inc h (fun _ => True)))
  unfold PY
  rw [← (hs K hK).tsum_sub (hs K₂ hK₂)]
  refine tsum_congr fun n => ?_
  unfold Pterm PtermGen
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  exact Finset.sum_congr rfl fun X _ => by ring

/-- **Closeness of the local terms of the cluster sum** (margin form). If `|K|, |K₂| ≤ κ₀` and
`|K(x) - K₂(x)| ≤ κ₀(x) e^{-λ m(supp x)}` with `m ≥ 0` decreasing under inclusion and `λ ≥ 0`, and the
doubled weights `κ = 2 κ₀ e^{g + c}` satisfy the Kotecký–Preiss condition, then
`∑_{Y ∋ □} |P_K(Y) - P_{K₂}(Y)| e^{g(Y) + λ m(Y)} ≤ ∑_{x ∋ □} κ(x) e^{a(x)}`. -/
theorem pe_PY_sub_bound (g : Finset B → ℝ) (c : ℝ) (hc : 0 ≤ c) (hg : ∀ Y, 0 ≤ g Y)
    (hG3 : ∀ (n : ℕ) (X : Fin (n + 1) → P), (clusterGraph inc X).Connected →
      g (unionOf supp X) ≤ ∑ i, g (supp (X i)) + c * n)
    (m : Finset B → ℝ) (hm : ∀ Y, 0 ≤ m Y) (hmono : ∀ X Y, X ⊆ Y → m Y ≤ m X) {lam : ℝ}
    (hlam : 0 ≤ lam) (hκ : ∀ x, κ x = 2 * κ0 x * Real.exp (g (supp x) + c)) (h : KPCond inc κ a)
    (K K₂ : P → ℂ) (hK : ∀ x, ‖K x‖ ≤ κ0 x) (hK₂ : ∀ x, ‖K₂ x‖ ≤ κ0 x)
    (hKK : ∀ x, ‖K x - K₂ x‖ ≤ κ0 x * Real.exp (-lam * m (supp x))) (b : B) :
    ∑ Y ∈ (Finset.univ : Finset (Finset B)).filter (fun Y => b ∈ Y),
        ‖PY inc supp K Y - PY inc supp K₂ Y‖ * Real.exp (g Y + lam * m Y) ≤
      ∑ x, (if b ∈ supp x then κ x * Real.exp (a x) else 0) := by
  have hκ0 : ∀ x, 0 ≤ κ0 x := fun x => (norm_nonneg _).trans (hK x)
  have hκκ : ∀ x, κ0 x ≤ κ x := fun x => by
    rw [hκ x]
    have : 1 ≤ Real.exp (g (supp x) + c) := Real.one_le_exp (add_nonneg (hg _) hc)
    nlinarith [hκ0 x]
  have hsub := PY_sub_eq_tsum_PtermGen inc supp h K K₂ (fun x => (hK x).trans (hκκ x))
    (fun x => (hK₂ x).trans (hκκ x))
  have hcore := pe_PYGen_bound inc supp (fun Y => g Y + lam * m Y)
    (fun Y => add_nonneg (hg Y) (mul_nonneg hlam (hm Y))) h
    (fun _ X => ∏ i, K (X i) - ∏ i, K₂ (X i)) (fun n X => ?_) b
  · refine le_trans (le_of_eq ?_) hcore
    exact Finset.sum_congr rfl fun Y _ => by rw [hsub Y]
  · -- the coefficient bound of one cluster
    set U := unionOf supp X with hU
    have hsubU : ∀ i, supp (X i) ⊆ U := fun i =>
      Finset.subset_biUnion_of_mem (fun i => supp (X i)) (Finset.mem_univ i)
    have hr : 0 ≤ Real.exp (-lam * m U) := (Real.exp_pos _).le
    have htel := norm_prod_sub_prod_le_two Finset.univ (fun i => K (X i)) (fun i => K₂ (X i))
      (fun i => κ0 (X i)) hr (fun i _ => hK _) (fun i _ => hK₂ _) (fun i _ => by
        refine (hKK (X i)).trans ?_
        rw [mul_comm]
        refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) (hκ0 _)
        have := hmono _ _ (hsubU i)
        nlinarith)
    set z : ℂ := (Real.exp (lam * m U) : ℂ) * (∏ i, K (X i) - ∏ i, K₂ (X i)) with hz
    have hzb : ‖z‖ ≤ ∏ i, (2 * κ0 (X i)) := by
      rw [hz, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
      calc Real.exp (lam * m U) * ‖∏ i, K (X i) - ∏ i, K₂ (X i)‖
          ≤ Real.exp (lam * m U) * (Real.exp (-lam * m U) * ∏ i, (2 * κ0 (X i))) :=
            mul_le_mul_of_nonneg_left htel (Real.exp_pos _).le
        _ = ∏ i, (2 * κ0 (X i)) := by
            rw [← mul_assoc, ← Real.exp_add]
            simp
    have hκ' : ∀ x, κ x = (2 * κ0 x) * Real.exp (g (supp x) + c) := hκ
    have hb := term_bound_core inc supp g c hc hG3 hκ' (fun x => by have := hκ0 x; positivity) X z
      hzb
    calc ‖(clusterUrsell inc X Finset.univ : ℂ) * (∏ i, K (X i) - ∏ i, K₂ (X i))‖ *
          Real.exp (g (unionOf supp X) + lam * m (unionOf supp X))
        = ‖(clusterUrsell inc X Finset.univ : ℂ) * z‖ * Real.exp (g (unionOf supp X)) := by
          rw [hz, Real.exp_add, ← hU, mul_left_comm (_ : ℂ), norm_mul (Real.exp _ : ℂ),
            Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
          ring
      _ ≤ aaw inc X * ∏ i, κ (X i) := hb

end Close

end Balaban.Polymer
