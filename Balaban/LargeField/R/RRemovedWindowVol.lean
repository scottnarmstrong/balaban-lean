/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RRemovedShellVol
public import Balaban.LargeField.R.RRemovedWindowGen
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr

/-!
# The window integral: the volumes (Lemma III.8.7 (3)) (W905)

`notes/phase1/LF4R-PLAN.md`, leaf 6, step (3).  The volume of the support set `E` of the window
variables, with the weights that multiply it in the integrand, as a product over the groups of
variables:

* `vol_weight_le`: `∏ wt_i · μ(B) ≤ e^{c |ι|}` when `μ(B) ≤ vol B(0, r)^{|ι|}` and
  `v_N r^N wt_i ≤ e^c` for each block;
* `zero_group_vol_le`: `ψ_k↾Z₀` in the balls of `χ_{Z₀}` (radius `C₆ β^{-1/2} p₀`) with the weight
  `e^{(N/2) log β}` per block (`zero_block_factor_le`);
* `tree_group_vol_le`: `ψ_k` on `Z^c_0 ∩ Z ∩ Ω_k^c` in the spanning-tree balls of `χ̃_k` (radius
  `3 δ_k`) with the weight `(w_z/π)^{N/2}`, `w_z ≤ 2β` per block (`tree_block_factor_le`);
* `weighted_prod_le`: the product of two groups; shells and balls of volume at most `1` are the
  landed `outPartMeasure_shell_le_one`, `subMeasure_ball_le_one`, ….
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open MeasureTheory ENNReal Balaban RegionHistory

section Weights

variable {N : ℕ}

/-- The per-block weighted volume bound. -/
theorem vol_weight_le {ι : Type*} [Fintype ι] (hN : 0 < N) {r : ℝ} (hr : 0 ≤ r) (wt : ι → ℝ)
    (hwt : ∀ i, 0 ≤ wt i) {c : ℝ}
    (h : ∀ i, (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin N)) 1)).toReal * r ^ N * wt i ≤
      Real.exp c)
    {μB : ℝ≥0∞} (hμ : μB ≤ volume (Metric.ball (0 : EuclideanSpace ℝ (Fin N)) r) ^
      Fintype.card ι) :
    ENNReal.ofReal (∏ i, wt i) * μB ≤ ENNReal.ofReal (Real.exp (c * Fintype.card ι)) := by
  set V := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin N)) 1)).toReal with hV
  rw [volume_ball_eq_ofReal hN hr] at hμ
  calc ENNReal.ofReal (∏ i, wt i) * μB
      ≤ ENNReal.ofReal (∏ i, wt i) * ENNReal.ofReal (V * r ^ N) ^ Fintype.card ι := by gcongr
    _ = ∏ i : ι, ENNReal.ofReal (V * r ^ N * wt i) := by
        have hVr : 0 ≤ V * r ^ N := by
          have : 0 ≤ V := ENNReal.toReal_nonneg
          positivity
        rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => hwt i)]
        simp_rw [ENNReal.ofReal_mul hVr]
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, mul_comm]
    _ ≤ ∏ _i : ι, ENNReal.ofReal (Real.exp c) :=
        Finset.prod_le_prod fun i _ => ENNReal.ofReal_le_ofReal (h i)
    _ = ENNReal.ofReal (Real.exp (c * Fintype.card ι)) := by
        rw [Finset.prod_const, Finset.card_univ, ← ENNReal.ofReal_pow (Real.exp_pos c).le,
          ← Real.exp_nat_mul, mul_comm]

/-- **The balls of `χ_{Z₀}`** (step (3), `ψ_k↾Z₀`): the configurations with `‖ψ_k(y) - ψ⁰_k(y)‖ < r`
on all the blocks have measure at most `vol B(0, r)^{#blocks}`. -/
theorem outPartMeasure_ball_le_pow (hN : 0 < N) {α : Type} [Finite α] (V : Set α) (P : α → Prop)
    (cen : {y : α // y ∈ V ∧ P y} → EuclideanSpace ℝ (Fin N)) (r : ℝ) :
    outPartMeasure N V P {o | ∀ i, ‖o i - cen i‖ < r} ≤
      volume (Metric.ball (0 : EuclideanSpace ℝ (Fin N)) r) ^
        Nat.card {y : α // y ∈ V ∧ P y} := by
  classical
  let _ : Fintype {y : α // y ∈ V ∧ P y} := Fintype.ofFinite _
  have h := outPartMeasure_tree_le hN V P (ρ := {y : α // y ∈ V ∧ P y}) cen
    (fun i => Sum.inr i) (fun _ => 0) (fun i j h => by simp at h) (fun _ => r)
  simp only [Sum.elim_inr] at h
  rw [Finset.prod_const, Finset.card_univ] at h
  rwa [Nat.card_eq_fintype_card]

/-- **The `Z₀` group with its weight** (step (3)): `e^{(N/2) log β · #Z₀-blocks}` times the measure
of the `χ_{Z₀}` balls is at most `e^{(N p₀ log λ + C_vol) #Z₀-blocks}`
(`zero_block_factor_le`; `C_vol ≥ log (v_N max {3, C₆}^N A₀^N)`). -/
theorem zero_group_vol_le (hN : 0 < N) {α : Type} [Finite α] (V : Set α) (P : α → Prop)
    (cen : {y : α // y ∈ V ∧ P y} → EuclideanSpace ℝ (Fin N)) {β A0 lam C6 : ℝ} (pe : ℕ)
    (hβ : 0 < β) (hC6 : 0 ≤ C6) (hA0 : 0 < A0) (hlam : 0 < lam) {cc : ℝ}
    (hcc : Real.log ((volume (Metric.ball (0 : EuclideanSpace ℝ (Fin N)) 1)).toReal *
      (max 3 C6) ^ N * A0 ^ N) ≤ cc) :
    ENNReal.ofReal (Real.exp ((N : ℝ) / 2 * Real.log β * Nat.card {y : α // y ∈ V ∧ P y})) *
      outPartMeasure N V P {o | ∀ i, ‖o i - cen i‖ < C6 * β ^ (-(1 / 2 : ℝ)) * (A0 * lam ^ pe)} ≤
      ENNReal.ofReal (Real.exp (((N : ℝ) * pe * Real.log lam + cc) *
        Nat.card {y : α // y ∈ V ∧ P y})) := by
  classical
  let _ : Fintype {y : α // y ∈ V ∧ P y} := Fintype.ofFinite _
  set r : ℝ := C6 * β ^ (-(1 / 2 : ℝ)) * (A0 * lam ^ pe) with hrdef
  have hr : 0 ≤ r := by rw [hrdef]; positivity
  have hb : ∀ _i : {y : α // y ∈ V ∧ P y},
      (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin N)) 1)).toReal * r ^ N *
        Real.exp ((N : ℝ) / 2 * Real.log β) ≤ Real.exp ((N : ℝ) * pe * Real.log lam + cc) :=
    fun _ => (zero_block_factor_le (N := N) pe hβ hC6 hA0 hlam).trans
      (Real.exp_le_exp.2 (by linarith))
  have h := vol_weight_le (ι := {y : α // y ∈ V ∧ P y}) hN hr
    (fun _ => Real.exp ((N : ℝ) / 2 * Real.log β)) (fun _ => (Real.exp_pos _).le) hb
    (μB := outPartMeasure N V P {o | ∀ i, ‖o i - cen i‖ < r})
    (by rw [← Nat.card_eq_fintype_card]; exact outPartMeasure_ball_le_pow hN V P cen r)
  rw [Finset.prod_const, Finset.card_univ, ← Real.exp_nat_mul, mul_comm (Fintype.card _ : ℝ)] at h
  rwa [Nat.card_eq_fintype_card]

/-- **The tree group with its weight** (step (3), `ψ_k` on `Z^c_0 ∩ Z ∩ Ω_k^c`): the weight
`∏_z (w_z/π)^{N/2}` (`0 ≤ w_z ≤ 2β`, the constant of the composed Gaussian) times the measure of
the spanning-tree balls of `χ̃_k` (`outPartMeasure_chiTilde_le`) is at most
`e^{(N p₀ log λ + C_vol) #blocks}` (`tree_block_factor_le`). -/
theorem tree_group_vol_le {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {M K : ℕ} [NeZero M]
    [NeZero S.L] (hN : 0 < N) (a : LocalHistory S n M K) (k : ℕ)
    (Z0 : Set (Torus S.d (M * n K * S.L ^ K))) (δk : ℝ) (V : Set (BlockAt S n M K k))
    (P : BlockAt S n M K k → Prop) {ρ : Type} (e : ρ → EuclideanSpace ℝ (Fin N))
    (cb : ρ → BlockAt S n M K k)
    (par : {y : BlockAt S n M K k // y ∈ V ∧ P y} →
      {y : BlockAt S n M K k // y ∈ V ∧ P y} ⊕ ρ)
    (rk : {y : BlockAt S n M K k // y ∈ V ∧ P y} → ℕ)
    (hrk : ∀ i j, par i = Sum.inl j → rk j < rk i)
    (hreg : ∀ i : {y : BlockAt S n M K k // y ∈ V ∧ P y},
      BlockSub (S := S) (n := n) (M := M) (K := K) k i.1 (tildeRegion a k Z0))
    (hregc : ∀ c, BlockSub (S := S) (n := n) (M := M) (K := K) k (cb c) (tildeRegion a k Z0))
    (hadj : ∀ i j, par i = Sum.inl j → AdjT i.1 j.1)
    (hadjc : ∀ i c, par i = Sum.inr c → AdjT i.1 (cb c))
    {β A0 lam C6 : ℝ} (pe : ℕ) (hβ : 0 < β) (hA0 : 0 < A0) (hlam : 0 < lam)
    (hδ : δk = β ^ (-(1 / 2 : ℝ)) * (A0 * lam ^ pe))
    (wz : {y : BlockAt S n M K k // y ∈ V ∧ P y} → ℝ) (hw0 : ∀ i, 0 ≤ wz i)
    (hw : ∀ i, wz i ≤ 2 * β) {cc : ℝ}
    (hcc : Real.log ((volume (Metric.ball (0 : EuclideanSpace ℝ (Fin N)) 1)).toReal *
      (max 3 C6) ^ N * A0 ^ N) ≤ cc) :
    ENNReal.ofReal (∏ i, (wz i / Real.pi) ^ ((N : ℝ) / 2)) *
      outPartMeasure N V P {o | ∃ ψ : BlockAt S n M K k → EuclideanSpace ℝ (Fin N),
        (∀ i, ψ i.1 = o i) ∧ (∀ c, ψ (cb c) = e c) ∧ ChiTildeProp a k Z0 δk ψ} ≤
      ENNReal.ofReal (Real.exp (((N : ℝ) * pe * Real.log lam + cc) *
        Nat.card {y : BlockAt S n M K k // y ∈ V ∧ P y})) := by
  classical
  let _ : Fintype {y : BlockAt S n M K k // y ∈ V ∧ P y} := Fintype.ofFinite _
  have hδ0 : 0 ≤ δk := by rw [hδ]; positivity
  have h := vol_weight_le (ι := {y : BlockAt S n M K k // y ∈ V ∧ P y}) hN
    (r := 3 * δk) (by positivity) (fun i => (wz i / Real.pi) ^ ((N : ℝ) / 2))
    (fun i => Real.rpow_nonneg (div_nonneg (hw0 i) Real.pi_pos.le) _) (c := (N : ℝ) * pe *
      Real.log lam + cc)
    (fun i => (tree_block_factor_le (N := N) (C6 := C6) pe hβ (hw0 i) (hw i) hδ hA0 hlam).trans
      (Real.exp_le_exp.2 (by linarith)))
    (μB := outPartMeasure N V P {o | ∃ ψ : BlockAt S n M K k → EuclideanSpace ℝ (Fin N),
        (∀ i, ψ i.1 = o i) ∧ (∀ c, ψ (cb c) = e c) ∧ ChiTildeProp a k Z0 δk ψ})
    (by
      rw [← Nat.card_eq_fintype_card]
      exact outPartMeasure_chiTilde_le hN a k Z0 δk V P e cb par rk hrk hreg hregc hadj hadjc)
  rwa [← Nat.card_eq_fintype_card] at h

end Weights

section Product

variable {W1 W2 : Type*} [MeasurableSpace W1] [MeasurableSpace W2]

/-- **Two groups of window variables**: the weighted volumes multiply. -/
theorem weighted_prod_le {μ1 : Measure W1} {μ2 : Measure W2} [SFinite μ2] {E1 : Set W1}
    {E2 : Set W2} {L1 L2 V1 V2 : ℝ}
    (h1 : ENNReal.ofReal (Real.exp L1) * μ1 E1 ≤ ENNReal.ofReal (Real.exp V1))
    (h2 : ENNReal.ofReal (Real.exp L2) * μ2 E2 ≤ ENNReal.ofReal (Real.exp V2)) :
    ENNReal.ofReal (Real.exp (L1 + L2)) * (μ1.prod μ2) (E1 ×ˢ E2) ≤
      ENNReal.ofReal (Real.exp (V1 + V2)) := by
  rw [Measure.prod_prod, Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le,
    Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]
  calc ENNReal.ofReal (Real.exp L1) * ENNReal.ofReal (Real.exp L2) * (μ1 E1 * μ2 E2)
      = (ENNReal.ofReal (Real.exp L1) * μ1 E1) * (ENNReal.ofReal (Real.exp L2) * μ2 E2) := by
        ring
    _ ≤ _ := by gcongr

/-- A weighted volume bound gives the volume bound `μ(E) ≤ e^{V - L}` used in
`lintegral_window_core_le` (the weight `e^L` is part of the integrand). -/
theorem vol_of_weighted {μ : Measure W1} {E : Set W1} {L V : ℝ}
    (h : ENNReal.ofReal (Real.exp L) * μ E ≤ ENNReal.ofReal (Real.exp V)) :
    μ E ≤ ENNReal.ofReal (Real.exp (V - L)) := by
  have h1 : ENNReal.ofReal (Real.exp (V - L)) =
      ENNReal.ofReal (Real.exp (-L)) * ENNReal.ofReal (Real.exp V) := by
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]; congr 2; ring
  have h2 : μ E = ENNReal.ofReal (Real.exp (-L)) *
      (ENNReal.ofReal (Real.exp L) * μ E) := by
    rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    simp
  rw [h1, h2]
  gcongr

end Product


end Balaban.LargeField
