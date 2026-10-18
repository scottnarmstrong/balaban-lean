/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepTowerNewLevelE0Sum
public import Balaban.Fluctuation.DARateNumerics

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

open Classical in
/-- **The constants of the marks, from the activity bound of the inherited labels.**  The weights
`2 B_τ e^{E(τ, Y)}` of the labels `τ` with `Y ∈ dom τ`, times `c_U/a`, are at most
`ε_C e^{-κ_G d^cov(Y)}` for every domain `Y` of a contributing pair (the hypothesis
`hnumR` of the chain), and `F1 q = (‖β‖ β⁻¹ B_τ e^{E}/b + ϖ e^{…}) e^{κ_G d(q)}`: then
`∑_q F1 q e^{-κ₀ d(q)} ≤ ε_C a/(2 b c_U) · n_fibre e^{κ_G c_Br} K₀ + n_fibre e^{κ₀ c_Br} K₀`. -/
theorem marksConst_sum_le_of_hnumR {ι : Type*} [Fintype ι] (hN : L ^ m₀ ∣ N₁) (hL : 2 ≤ L)
    (dom : ι → Finset (Set (CTorus d L N₁ m₁ K)))
    (hdom : ∀ τ, ∀ Y ∈ dom τ, IsDj m₀ K Y) (z : RootIdx d L N₁ m₁ K)
    {κ0 κG εC aR cU sβ bb : ℝ} (hκ0 : aEnt d L + 1 ≤ κ0) (hκG : κ0 ≤ κG) (hεC : 0 ≤ εC)
    (haR : 0 < aR) (hcU : 0 < cU) (hbb : 0 < bb) (hsβ : 0 < sβ)
    (Bτ : ι → ℝ) (hBτ : ∀ τ, 0 ≤ Bτ τ) (E : ι → Set (CTorus d L N₁ m₁ K) → ℝ)
    (hnum : ∀ Y ∈ (markedIdx (fun _ => (Set.univ : Set (CTorus d L N₁ m₁ K))) dom z).image
        Prod.snd, cU / aR * (∑ τ, if Y ∈ dom τ then 2 * Bτ τ * Real.exp (E τ Y) else 0) ≤
        εC * Real.exp (-κG * treeLenCovOne m₀ K Y))
    (ϖ : ι → ℝ) (hϖ : ∀ b, 0 ≤ ϖ b) (hϖs : ∑ b, ϖ b ≤ 1)
    (dlf : {q // q ∈ markedIdx (fun _ => (Set.univ : Set (CTorus d L N₁ m₁ K))) dom z} → ℝ)
    (hdl : ∀ q, dlf q = treeLenCovOne m₀ K (bridge m₀ z q.1.2))
    (F1 : {q // q ∈ markedIdx (fun _ => (Set.univ : Set (CTorus d L N₁ m₁ K))) dom z} → ℝ)
    (hF1 : ∀ q, F1 q = (‖(sβ : ℂ)‖ * ((sβ⁻¹ * Bτ q.1.1) * Real.exp (E q.1.1 q.1.2) / bb) +
      ϖ q.1.1 * Real.exp (-κ0 * treeLenCovOne m₀ K q.1.2) *
        Real.exp (-(κG - κ0) * treeLenCovOne m₀ K (bridge m₀ z q.1.2))) *
      Real.exp (κG * dlf q)) :
    ∑ q, F1 q * Real.exp (-κ0 * dlf q) ≤
      εC * aR / (2 * bb * cU) * ((nFibre d L : ℝ) * Real.exp (κG * cBr d L)) * K0 d L κ0 +
        (nFibre d L : ℝ) * Real.exp (κ0 * cBr d L) * K0 d L κ0 := by
  have hnorm : ‖(sβ : ℂ)‖ = sβ := by
    rw [Complex.norm_real, Real.norm_of_nonneg hsβ.le]
  have hc0 : 0 ≤ εC * aR / (2 * bb * cU) := by positivity
  have hAeq : ∀ τ Y, ‖(sβ : ℂ)‖ * ((sβ⁻¹ * Bτ τ) * Real.exp (E τ Y) / bb) =
      (1 / (2 * bb)) * (2 * Bτ τ * Real.exp (E τ Y)) := fun τ Y => by
    rw [hnorm]
    field_simp
  have h1 := marksConst_sum_le hN hL (fun _ => (Set.univ : Set (CTorus d L N₁ m₁ K))) dom hdom z
    hκ0 hκG hc0 (fun τ Y => ‖(sβ : ℂ)‖ * ((sβ⁻¹ * Bτ τ) * Real.exp (E τ Y) / bb))
    (fun τ Y => by
      have := hBτ τ
      positivity)
    (fun Y hY => by
      have e1 : ∑ b, (if Y ∈ dom b then ‖(sβ : ℂ)‖ * ((sβ⁻¹ * Bτ b) * Real.exp (E b Y) / bb)
          else 0) = (1 / (2 * bb)) * ∑ b, (if Y ∈ dom b then 2 * Bτ b * Real.exp (E b Y)
          else 0) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        split_ifs
        · exact hAeq b Y
        · simp
      rw [e1]
      have h2 := hnum Y hY
      have h3 : ∑ b, (if Y ∈ dom b then 2 * Bτ b * Real.exp (E b Y) else 0) ≤
          εC * Real.exp (-κG * treeLenCovOne m₀ K Y) * (aR / cU) := by
        have : cU / aR * ∑ b, (if Y ∈ dom b then 2 * Bτ b * Real.exp (E b Y) else 0) ≤
            εC * Real.exp (-κG * treeLenCovOne m₀ K Y) := h2
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)] at this
        rw [mul_div_assoc'] 
        rw [le_div_iff₀ hcU]
        nlinarith [this]
      calc (1 / (2 * bb)) * ∑ b, (if Y ∈ dom b then 2 * Bτ b * Real.exp (E b Y) else 0)
          ≤ (1 / (2 * bb)) * (εC * Real.exp (-κG * treeLenCovOne m₀ K Y) * (aR / cU)) :=
            mul_le_mul_of_nonneg_left h3 (by positivity)
        _ = εC * aR / (2 * bb * cU) * Real.exp (-κG * treeLenCovOne m₀ K Y) := by
            field_simp)
    ϖ hϖ dlf hdl F1 hF1
  refine h1.trans ?_
  have hnn : 0 ≤ (nFibre d L : ℝ) * Real.exp (κ0 * cBr d L) * K0 d L κ0 := by
    have := K0_pos d L κ0
    positivity
  have : (∑ b, ϖ b) * ((nFibre d L : ℝ) * Real.exp (κ0 * cBr d L) * K0 d L κ0) ≤
      (nFibre d L : ℝ) * Real.exp (κ0 * cBr d L) * K0 d L κ0 := by
    simpa using mul_le_mul_of_nonneg_right hϖs hnn
  linarith

end Sum

end Balaban.Fluctuation
