/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.CubeSystem
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Theorem 3.1 (b): the product of the kernel with `G*` and the connected-union resummation

"The products `h(x,y;Y′) G*(y,S)` are resummed over the connected unions `Y′ ∪ Ŷ(S)` (they share
the cube of `y`): rate `min{2κ−1, κ_a} − κ₀ − 1 = κ_b` (entropy and one volume factor)."

`kernel_mark_resum`: for the sets `T` (labels of the kernel `h(i, T)`, supported on the cube `b i`
of the mark `i`) and `S` (the terms `E(i, S)` of the marked expansion, also containing `b i`), the
local terms `M(W) = ∑_i ∑_{T ∪ S = W} h(i,T) E(i,S)` satisfy
`|M(W)| ≤ B e^{-(κ - κ₀ - 1) d_Ω(W)}`, `κ = min(κ_h, κ_E)`; the three ingredients are
(G3) (`dExt_union_le`), (G2) (`sum_exp_dExt_le`) and (G1) (`card_le_dExt`).
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Polymer

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ j : ℕ} {Ω : Set (CTorus d L N₁ m₁ K)}

local notation "𝔅" => CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω

section Resum

open Classical in
/-- **The resummed local terms**: `M(W) = ∑_i ∑_{T ∪ S = W} h(i,T) E(i,S)`. -/
noncomputable def kernelMarkSum {ι : Type*} [Fintype ι] (h E : ι → Finset 𝔅 → ℂ)
    (W : Finset 𝔅) : ℂ :=
  ∑ i, ∑ T : Finset 𝔅, ∑ S : Finset 𝔅, if T ∪ S = W then h i T * E i S else 0

theorem sum_finset_eq_sum_nePoly (b : 𝔅) (g : Finset 𝔅 → ℝ) :
    ∑ T : Finset 𝔅, (if b ∈ T then g T else 0) =
      ∑ Y : NePoly 𝔅, (if b ∈ Y.1 then g Y.1 else 0) := by
  classical
  rw [← Finset.sum_filter_of_ne (p := fun T : Finset 𝔅 => T.Nonempty)
    (fun T _ hT => by
      by_contra hne
      rw [Finset.not_nonempty_iff_eq_empty] at hne
      subst hne
      simp at hT)]
  exact Finset.sum_subtype (Finset.univ.filter fun T : Finset 𝔅 => T.Nonempty)
    (p := fun T : Finset 𝔅 => T.Nonempty) (by simp) (fun T => if b ∈ T then g T else 0)

theorem entropy_sum_finset (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K) (b : 𝔅) {κ0 Kc : ℝ}
    (hκ0 : aEnt d L + 1 ≤ κ0) (hKc : K0 d L κ0 + 1 ≤ Kc) :
    ∑ T : Finset 𝔅, (if b ∈ T then Real.exp (-κ0 * dExt T) else 0) ≤ Kc := by
  exact (le_of_eq (sum_finset_eq_sum_nePoly b (fun T => Real.exp (-κ0 * dExt T)))).trans
    ((sum_exp_dExt_le hN hj b hκ0).trans hKc)

open Classical in
/-- **The kernel-times-mark resummation** (§3.5 (b)): rate `κ - κ₀ - 1`. -/
theorem kernel_mark_resum (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K) {ι : Type*} [Fintype ι]
    (b : ι → 𝔅) {nmax : ℝ} (hnmax : 0 ≤ nmax) (hcount : ∀ c : 𝔅, ((Finset.univ.filter fun i => b i = c).card : ℝ) ≤ nmax)
    (h E : ι → Finset 𝔅 → ℂ) {Ch Cg κh κg κ0 Kc : ℝ} (hCh : 0 ≤ Ch) (hCg : 0 ≤ Cg)
    (hh : ∀ i T, ‖h i T‖ ≤ Ch * Real.exp (-κh * dExt T)) (hhs : ∀ i T, b i ∉ T → h i T = 0)
    (hE : ∀ i S, ‖E i S‖ ≤ Cg * Real.exp (-κg * dExt S)) (hEs : ∀ i S, b i ∉ S → E i S = 0)
    (hκ0 : aEnt d L + 1 ≤ κ0) (hKc : K0 d L κ0 + 1 ≤ Kc) (hκh : κ0 ≤ κh) (hκg : κ0 ≤ κg)
    (W : Finset 𝔅) :
    ‖kernelMarkSum h E W‖ ≤
      Ch * Cg * (nmax * c1 d L) * Kc ^ 2 * Real.exp ((min κh κg - κ0) * cG d L) *
        Real.exp (-(min κh κg - κ0 - 1) * dExt W) := by
  set κ := min κh κg with hκdef
  have hκκ0 : κ0 ≤ κ := le_min hκh hκg
  have hc1 := one_le_c1 d L
  have hcG : 0 ≤ cG d L := by unfold cG; positivity
  have hKc0 : 0 ≤ Kc := by
    have : 0 ≤ K0 d L κ0 := by
      unfold K0
      have : Real.exp (-1) < 1 := by rw [Real.exp_lt_one_iff]; norm_num
      exact div_nonneg (Real.exp_pos _).le (by linarith)
    linarith
  set dW := dExt W with hdW
  set C' : ℝ := Ch * Cg * Real.exp ((κ - κ0) * cG d L) * Real.exp (-(κ - κ0) * dW) with hC'
  have hC'0 : 0 ≤ C' := by positivity
  set cw : ι → ℝ := fun i => if b i ∈ W then C' else 0 with hcw
  set p : ι → Finset 𝔅 → ℝ := fun i T => if b i ∈ T then Real.exp (-κ0 * dExt T) else 0 with hp
  have hp0 : ∀ i T, 0 ≤ p i T := fun i T => by simp only [hp]; split_ifs <;> positivity
  have hcw0 : ∀ i, 0 ≤ cw i := fun i => by simp only [hcw]; split_ifs <;> positivity
  -- pointwise bound
  have hpt : ∀ i T S, ‖if T ∪ S = W then h i T * E i S else 0‖ ≤ cw i * (p i T * p i S) := by
    intro i T S
    have hnn : 0 ≤ cw i * (p i T * p i S) := mul_nonneg (hcw0 i) (mul_nonneg (hp0 i T) (hp0 i S))
    by_cases hW : T ∪ S = W
    · simp only [hW, ite_true]
      by_cases hT : b i ∈ T
      · by_cases hS : b i ∈ S
        · have hbW : b i ∈ W := hW ▸ Finset.mem_union_left _ hT
          have hnd : ¬ Disjoint T S := Finset.not_disjoint_iff.2 ⟨b i, hT, hS⟩
          have hU := dExt_union_le T S hnd
          rw [hW] at hU
          have hdT := dExt_nonneg T
          have hdS := dExt_nonneg S
          rw [norm_mul]
          have h1 : ‖h i T‖ * ‖E i S‖ ≤ (Ch * Real.exp (-κh * dExt T)) * (Cg * Real.exp (-κg * dExt S)) :=
            mul_le_mul (hh i T) (hE i S) (norm_nonneg _) (by positivity)
          refine h1.trans ?_
          simp only [hcw, hp, hbW, hT, hS, ite_true]
          have hkk : 0 ≤ κ - κ0 := by linarith
          have e1 : 0 ≤ (κh - κ) * dExt T := mul_nonneg (by linarith [min_le_left κh κg]) hdT
          have e2 : 0 ≤ (κg - κ) * dExt S := mul_nonneg (by linarith [min_le_right κh κg]) hdS
          have e3 : 0 ≤ (κ - κ0) * (dExt T + dExt S + cG d L - dW) :=
            mul_nonneg hkk (by linarith)
          have hexp : Real.exp (-κh * dExt T) * Real.exp (-κg * dExt S) ≤
              Real.exp ((κ - κ0) * cG d L) * Real.exp (-(κ - κ0) * dW) *
                (Real.exp (-κ0 * dExt T) * Real.exp (-κ0 * dExt S)) := by
            rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
            refine Real.exp_le_exp.2 ?_
            nlinarith [e1, e2, e3]
          calc Ch * Real.exp (-κh * dExt T) * (Cg * Real.exp (-κg * dExt S))
              = Ch * Cg * (Real.exp (-κh * dExt T) * Real.exp (-κg * dExt S)) := by ring
            _ ≤ Ch * Cg * (Real.exp ((κ - κ0) * cG d L) * Real.exp (-(κ - κ0) * dW) *
                (Real.exp (-κ0 * dExt T) * Real.exp (-κ0 * dExt S))) :=
                mul_le_mul_of_nonneg_left hexp (by positivity)
            _ = _ := by rw [hC']; ring
        · rw [hEs i S hS]; simpa using hnn
      · rw [hhs i T hT]; simpa using hnn
    · simp only [hW, ite_false, norm_zero]; exact hnn
  -- summation
  have hsum : ∀ i, ∑ T : Finset 𝔅, ∑ S : Finset 𝔅, cw i * (p i T * p i S) ≤ cw i * Kc ^ 2 := by
    intro i
    have hKT : ∑ T : Finset 𝔅, p i T ≤ Kc := entropy_sum_finset hN hj (b i) hκ0 hKc
    have : ∑ T : Finset 𝔅, ∑ S : Finset 𝔅, cw i * (p i T * p i S) =
        cw i * ((∑ T : Finset 𝔅, p i T) * (∑ S : Finset 𝔅, p i S)) := by
      rw [Finset.sum_mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun T _ => ?_
      rw [Finset.mul_sum]
    rw [this]
    refine mul_le_mul_of_nonneg_left ?_ (hcw0 i)
    rw [sq]
    exact mul_le_mul hKT hKT (Finset.sum_nonneg fun S _ => hp0 i S) hKc0
  have hcount' : ∑ i, cw i = C' * ((Finset.univ.filter fun i => b i ∈ W).card : ℝ) := by
    simp only [hcw]
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hcard : ((Finset.univ.filter fun i => b i ∈ W).card : ℝ) ≤ nmax * (W.card : ℝ) := by
    have h1 := Finset.card_eq_sum_card_fiberwise (f := b) (s := Finset.univ.filter fun i => b i ∈ W)
      (t := W) (fun i hi => (Finset.mem_filter.1 hi).2)
    have h2 : ∀ c ∈ W, (((Finset.univ.filter fun i => b i ∈ W).filter fun i => b i = c).card : ℝ) ≤ nmax := by
      intro c hc
      refine le_trans ?_ (hcount c)
      exact_mod_cast Finset.card_le_card (fun i hi => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢; exact hi.2)
    rw [h1]
    push_cast
    calc ∑ c ∈ W, (((Finset.univ.filter fun i => b i ∈ W).filter fun i => b i = c).card : ℝ)
        ≤ ∑ _c ∈ W, nmax := Finset.sum_le_sum h2
      _ = nmax * (W.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hW1 : (W.card : ℝ) ≤ c1 d L * Real.exp dW := by
    refine (card_le_dExt hN hj W).trans ?_
    exact mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp dW]) (by linarith)
  calc ‖kernelMarkSum h E W‖
      ≤ ∑ i, ∑ T : Finset 𝔅, ∑ S : Finset 𝔅,
          ‖if T ∪ S = W then h i T * E i S else 0‖ := by
        unfold kernelMarkSum
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun T _ => ?_)
        exact norm_sum_le _ _
    _ ≤ ∑ i, ∑ T : Finset 𝔅, ∑ S : Finset 𝔅, cw i * (p i T * p i S) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun T _ => Finset.sum_le_sum fun S _ =>
          hpt i T S
    _ ≤ ∑ i, cw i * Kc ^ 2 := Finset.sum_le_sum fun i _ => hsum i
    _ = C' * ((Finset.univ.filter fun i => b i ∈ W).card : ℝ) * Kc ^ 2 := by
        rw [← Finset.sum_mul, hcount']
    _ ≤ C' * (nmax * (c1 d L * Real.exp dW)) * Kc ^ 2 := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hcard.trans ?_) hC'0)
          (sq_nonneg _)
        exact mul_le_mul_of_nonneg_left hW1 hnmax
    _ = _ := by
        rw [hC']
        have : Real.exp (-(κ - κ0) * dW) * Real.exp dW = Real.exp (-(κ - κ0 - 1) * dW) := by
          rw [← Real.exp_add]; congr 1; ring
        calc Ch * Cg * Real.exp ((κ - κ0) * cG d L) * Real.exp (-(κ - κ0) * dW) *
              (nmax * (c1 d L * Real.exp dW)) * Kc ^ 2
            = Ch * Cg * (nmax * c1 d L) * Kc ^ 2 * Real.exp ((κ - κ0) * cG d L) *
                (Real.exp (-(κ - κ0) * dW) * Real.exp dW) := by ring
          _ = _ := by rw [this]

end Resum

end Balaban.Fluctuation
