/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepTowerNewLevelE0Sum

/-!
# The sum of the constants of the marks, uniformly in the torus (`StepTowerNewLevelE0Bound`)

`marksConst_sum_le`: for the constants `F1 q = (A(q) + ϖ(b) e^{-κ₀ t(Y) - (κ_G - κ₀) t(bridge z Y)})
e^{κ_G d(q)}` of the marks of the contributing pairs `q = (b, Y)` of a root,
`d(q) = d^cov(bridge z Y)`, one has `∑_q F1 q e^{-κ₀ d(q)} ≤ c n_fibre e^{κ_G c_Br} K₀ +
(∑_b ϖ(b)) n_fibre e^{κ₀ c_Br} K₀` whenever the weights `A(b, Y)` of the `b` with `Y ∈ dom b` sum to
at most `c e^{-κ_G t(Y)}`.  The bound does not depend on the torus.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Polymer Balaban.Multiscale

/-- `∑_{τ} (1/2)^{rank τ + 1} ≤ 1` for a finite type with a fixed enumeration. -/
theorem sum_half_pow_le_one (ι : Type*) [Fintype ι] :
    ∑ τ : ι, ((1 : ℝ) / 2) ^ ((Fintype.equivFin ι τ : ℕ) + 1) ≤ 1 := by
  have h : ∀ n : ℕ, ∑ i ∈ Finset.range n, ((1 : ℝ) / 2) ^ (i + 1) = 1 - ((1 : ℝ) / 2) ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      ring
  calc ∑ τ : ι, ((1 : ℝ) / 2) ^ ((Fintype.equivFin ι τ : ℕ) + 1)
      = ∑ i : Fin (Fintype.card ι), ((1 : ℝ) / 2) ^ ((i : ℕ) + 1) :=
        Equiv.sum_comp (Fintype.equivFin ι) (fun i : Fin (Fintype.card ι) =>
          ((1 : ℝ) / 2) ^ ((i : ℕ) + 1))
    _ = ∑ i ∈ Finset.range (Fintype.card ι), ((1 : ℝ) / 2) ^ (i + 1) :=
        Fin.sum_univ_eq_sum_range (fun i => ((1 : ℝ) / 2) ^ (i + 1)) _
    _ ≤ 1 := by
        rw [h]
        have : (0 : ℝ) ≤ ((1 : ℝ) / 2) ^ Fintype.card ι := by positivity
        linarith

section Sum

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ : ℕ} {β : Type*} [Fintype β]

open Classical in
/-- **The constants of the marks sum to a bound independent of the torus.**  See the module
doc-string. -/
theorem marksConst_sum_le (hN : L ^ m₀ ∣ N₁) (hL : 2 ≤ L)
    (reads : β → Set (CTorus d L N₁ m₁ K)) (dom : β → Finset (Set (CTorus d L N₁ m₁ K)))
    (hdom : ∀ b, ∀ Y ∈ dom b, IsDj m₀ K Y) (z : RootIdx d L N₁ m₁ K) {κ0 κG c : ℝ}
    (hκ0 : aEnt d L + 1 ≤ κ0) (hκG : κ0 ≤ κG) (hc : 0 ≤ c)
    (A : β → Set (CTorus d L N₁ m₁ K) → ℝ) (hA : ∀ b Y, 0 ≤ A b Y)
    (hY : ∀ Y ∈ (markedIdx reads dom z).image Prod.snd,
      ∑ b, (if Y ∈ dom b then A b Y else 0) ≤ c * Real.exp (-κG * treeLenCovOne m₀ K Y))
    (ϖ : β → ℝ) (hϖ : ∀ b, 0 ≤ ϖ b)
    (dlf : {q // q ∈ markedIdx reads dom z} → ℝ)
    (hdl : ∀ q, dlf q = treeLenCovOne m₀ K (bridge m₀ z q.1.2))
    (F1 : {q // q ∈ markedIdx reads dom z} → ℝ)
    (hF1 : ∀ q, F1 q = (A q.1.1 q.1.2 + ϖ q.1.1 * Real.exp (-κ0 * treeLenCovOne m₀ K q.1.2) *
      Real.exp (-(κG - κ0) * treeLenCovOne m₀ K (bridge m₀ z q.1.2))) *
      Real.exp (κG * dlf q)) :
    ∑ q, F1 q * Real.exp (-κ0 * dlf q) ≤
      c * ((nFibre d L : ℝ) * Real.exp (κG * cBr d L)) * K0 d L κ0 +
        (∑ b, ϖ b) * ((nFibre d L : ℝ) * Real.exp (κ0 * cBr d L) * K0 d L κ0) := by
  have hterm : ∀ q : {q // q ∈ markedIdx reads dom z}, F1 q * Real.exp (-κ0 * dlf q) =
      A q.1.1 q.1.2 * Real.exp ((κG - κ0) * treeLenCovOne m₀ K (bridge m₀ z q.1.2)) +
        ϖ q.1.1 * Real.exp (-κ0 * treeLenCovOne m₀ K q.1.2) := fun q => by
    rw [hF1 q, hdl q]
    have e1 : Real.exp (κG * treeLenCovOne m₀ K (bridge m₀ z q.1.2)) *
        Real.exp (-κ0 * treeLenCovOne m₀ K (bridge m₀ z q.1.2)) =
        Real.exp ((κG - κ0) * treeLenCovOne m₀ K (bridge m₀ z q.1.2)) := by
      rw [← Real.exp_add]; congr 1; ring
    have e2 : Real.exp (-(κG - κ0) * treeLenCovOne m₀ K (bridge m₀ z q.1.2)) *
        Real.exp ((κG - κ0) * treeLenCovOne m₀ K (bridge m₀ z q.1.2)) = 1 := by
      rw [← Real.exp_add]
      have : -(κG - κ0) * treeLenCovOne m₀ K (bridge m₀ z q.1.2) +
          (κG - κ0) * treeLenCovOne m₀ K (bridge m₀ z q.1.2) = 0 := by ring
      rw [this, Real.exp_zero]
    calc (A q.1.1 q.1.2 + ϖ q.1.1 * Real.exp (-κ0 * treeLenCovOne m₀ K q.1.2) *
          Real.exp (-(κG - κ0) * treeLenCovOne m₀ K (bridge m₀ z q.1.2))) *
          Real.exp (κG * treeLenCovOne m₀ K (bridge m₀ z q.1.2)) *
          Real.exp (-κ0 * treeLenCovOne m₀ K (bridge m₀ z q.1.2))
        = (A q.1.1 q.1.2 + ϖ q.1.1 * Real.exp (-κ0 * treeLenCovOne m₀ K q.1.2) *
          Real.exp (-(κG - κ0) * treeLenCovOne m₀ K (bridge m₀ z q.1.2))) *
          (Real.exp (κG * treeLenCovOne m₀ K (bridge m₀ z q.1.2)) *
          Real.exp (-κ0 * treeLenCovOne m₀ K (bridge m₀ z q.1.2))) := by ring
      _ = _ := by
        rw [e1]
        have : Real.exp (-κ0 * treeLenCovOne m₀ K q.1.2) *
            Real.exp (-(κG - κ0) * treeLenCovOne m₀ K (bridge m₀ z q.1.2)) *
            Real.exp ((κG - κ0) * treeLenCovOne m₀ K (bridge m₀ z q.1.2)) =
            Real.exp (-κ0 * treeLenCovOne m₀ K q.1.2) := by
          rw [mul_assoc, e2, mul_one]
        calc _ = A q.1.1 q.1.2 * Real.exp ((κG - κ0) * treeLenCovOne m₀ K
              (bridge m₀ z q.1.2)) + ϖ q.1.1 * (Real.exp (-κ0 * treeLenCovOne m₀ K q.1.2) *
              Real.exp (-(κG - κ0) * treeLenCovOne m₀ K (bridge m₀ z q.1.2)) *
              Real.exp ((κG - κ0) * treeLenCovOne m₀ K (bridge m₀ z q.1.2))) := by ring
          _ = _ := by rw [this]
  rw [Finset.sum_congr rfl fun q _ => hterm q, Finset.sum_add_distrib]
  refine add_le_add ?_ ?_
  · rw [Finset.sum_coe_sort (markedIdx reads dom z) (fun q => A q.1 q.2 *
      Real.exp ((κG - κ0) * treeLenCovOne m₀ K (bridge m₀ z q.2)))]
    exact markedIdx_sum_exp_bridge_le_of_weights hN hL reads dom hdom z hκ0 hκG hc A hA hY
  · rw [Finset.sum_coe_sort (markedIdx reads dom z) (fun q => ϖ q.1 *
      Real.exp (-κ0 * treeLenCovOne m₀ K q.2))]
    exact markedIdx_sum_weight_le hN hL reads dom hdom z hκ0 ϖ hϖ

end Sum

end Balaban.Fluctuation
