/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusQuarterBox
public import Balaban.Polymer.TwoTorusFibre
public import Balaban.Green.FinalCoefWeighted
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The last-integral coefficients on the quarter box, uniformly in the size of the support

Blocker 7 (W860).  The coefficients of the logarithm of the perturbed defect and of the cutoff
interaction of the final operators on two tori have, for supports in the quarter box, the weighted
bounds `finalCoef_close_quarterBox_weighted`: the constants `P`, `C₀`, `c₀` do not depend on the
number of cells `|C|` (no premise `|C| ≤ nC`).  The polynomial factor in `|C|` of
`final_coef_logdet_close_twoTorus_unif_weighted` and of
`final_coef_cutoffInteraction_close_twoTorus_unif_weighted` is absorbed by the geometric factor
`(e^κ - 1)^{-|C|}` at the price of half the rate: the denominator is `√(e^κ - 1)^{|C|}`, that is
`(e^{κ₁} - 1)^{|C|}` with `κ₁ = log (1 + √(e^κ - 1))`.  The error of the operators enters through
`√εE` instead of `εE`.  `fibre_hcoef_of_quarterBox_weighted` gives the closeness of the last-scale
terms in the form consumed by `rootF_hcoef_limit` (with `ε` replaced by `√ε`).
-/

@[expose] public section

open Finset Matrix MeasureTheory Balaban.Localization Balaban.Analysis

namespace Balaban.Green

/-- A polynomial in `n` is bounded by a constant times `√ρ^{-n}` after division by `ρ^n`. -/
theorem exists_pow_div_le_sqrt {ρ : ℝ} (hρ : 1 < ρ) (j : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ n : ℕ, (n : ℝ) ^ j / ρ ^ n ≤ A / (Real.sqrt ρ) ^ n := by
  have hr : 1 < Real.sqrt ρ := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt zero_le_one hρ
  obtain ⟨A, hA⟩ := (tendsto_pow_const_div_const_pow_of_one_lt j hr).bddAbove_range
  refine ⟨max A 0, le_max_right _ _, fun n => ?_⟩
  have h1 : (n : ℝ) ^ j / (Real.sqrt ρ) ^ n ≤ max A 0 := (hA ⟨n, rfl⟩).trans (le_max_left _ _)
  have hρn : ρ ^ n = (Real.sqrt ρ) ^ n * (Real.sqrt ρ) ^ n := by
    rw [← mul_pow, Real.mul_self_sqrt (by linarith)]
  have hpos : 0 < (Real.sqrt ρ) ^ n := pow_pos (by linarith) n
  rw [hρn, ← div_div]
  exact div_le_div_of_nonneg_right h1 hpos.le

theorem sqrt_exp_eq_exp_half (a : ℝ) : Real.sqrt (Real.exp a) = Real.exp (a / 2) := by
  have : Real.exp a = Real.exp (a / 2) * Real.exp (a / 2) := by
    rw [← Real.exp_add]; ring_nf
  rw [this, Real.sqrt_mul_self (Real.exp_pos _).le]

theorem sqrt_mul_exp_neg (C₀ c₀ y : ℝ) (hC : 0 ≤ C₀) :
    Real.sqrt (C₀ * Real.exp (-c₀ * y)) = Real.sqrt C₀ * Real.exp (-(c₀ / 2) * y) := by
  rw [Real.sqrt_mul hC, sqrt_exp_eq_exp_half]
  congr 2
  ring

theorem bound_mono_aux {Q Q' K K' c c' y : ℝ} (hQ : 0 ≤ Q) (hQQ : Q ≤ Q') (hK : 0 ≤ K)
    (hKK : K ≤ K') (hcc : c' ≤ c) (hy : 0 ≤ y) :
    Q * (K * Real.exp (-c * y)) ≤ Q' * (K' * Real.exp (-c' * y)) := by
  have hexp : Real.exp (-c * y) ≤ Real.exp (-c' * y) :=
    Real.exp_le_exp.2 (by nlinarith)
  have hQ0 : 0 ≤ Q' := hQ.trans hQQ
  exact mul_le_mul hQQ (mul_le_mul hKK hexp (Real.exp_pos _).le (hK.trans hKK))
    (mul_nonneg hK (Real.exp_pos _).le) hQ0

/-- The final inequality of the cutoff-interaction clause: absorption of `n³ + n⁵`. -/
theorem cutoff_absorb_aux {Lip nB P2 Kc gs rJ G X' D Dr A3 A5 : ℝ} {n : ℕ}
    (hLip : 0 ≤ Lip) (hnB : 0 ≤ nB) (hP2 : 0 ≤ P2) (hKc : 0 ≤ Kc) (hgs : 0 < gs)
    (hrJ : 0 ≤ rJ) (hG : 0 ≤ G) (hDr : 0 < Dr)
    (h3 : (n : ℝ) ^ 3 / D ≤ A3 / Dr) (h5 : (n : ℝ) ^ 5 / D ≤ A5 / Dr)
    (hX : P2 * (A3 + A5) * Kc ≤ X') :
    Lip * (((n : ℝ) * nB) * (P2 * ((n : ℝ) ^ 2 + (n : ℝ) ^ 4) * Kc / gs) * rJ) * G / D ≤
      Lip * (nB * (X' / gs) * rJ) * G / Dr := by
  set W : ℝ := Lip * (nB * (P2 * Kc / gs) * rJ) * G with hW
  have hW0 : 0 ≤ W := by positivity
  have e1 : Lip * (((n : ℝ) * nB) * (P2 * ((n : ℝ) ^ 2 + (n : ℝ) ^ 4) * Kc / gs) * rJ) * G / D =
      W * ((n : ℝ) ^ 3 / D + (n : ℝ) ^ 5 / D) := by
    rw [hW]; ring
  have e2 : W * (A3 + A5) / Dr = Lip * (nB * (P2 * (A3 + A5) * Kc / gs) * rJ) * G / Dr := by
    rw [hW]; ring
  rw [e1]
  calc W * ((n : ℝ) ^ 3 / D + (n : ℝ) ^ 5 / D) ≤ W * (A3 / Dr + A5 / Dr) :=
        mul_le_mul_of_nonneg_left (add_le_add h3 h5) hW0
    _ = W * (A3 + A5) / Dr := by ring
    _ = Lip * (nB * (P2 * (A3 + A5) * Kc / gs) * rJ) * G / Dr := e2
    _ ≤ Lip * (nB * (X' / gs) * rJ) * G / Dr := by
        refine div_le_div_of_nonneg_right ?_ hDr.le
        refine mul_le_mul_of_nonneg_right ?_ hG
        refine mul_le_mul_of_nonneg_left ?_ hLip
        refine mul_le_mul_of_nonneg_right ?_ hrJ
        refine mul_le_mul_of_nonneg_left ?_ hnB
        exact div_le_div_of_nonneg_right hX hgs.le

/-- **The two last-integral coefficient families on the quarter box, uniformly in the size of the
support (blocker 7).**  As `finalCoef_close_quarterBox`, without the bound `nC` of the number of
cells: for every support `C` in the box (no premise `|C| ≤ nC`) the coefficients of the logarithm
of the perturbed defect, and those of the cutoff interaction, of the final operators on the tori
`N ≤ N'` differ by at most `P (C₀ e^{-c₀ M (2t - 7)} + √εE) / √(e^κ - 1)^{|C|}`, respectively
`Lip (8M+1)^d (P C₀ e^{-c₀ M (2t - 7)} / √g) ρ γ(box ρ) / √(e^κ - 1)^{|C|}`, with `P, C₀, c₀`
independent of the scale `k ≥ 1`, of the tori, of `m`, `t` and of `C`.  The polynomial factor in
`|C|` is absorbed by the decay: the base of the denominator is `√(e^κ - 1) = e^{κ₁} - 1`,
`κ₁ = log (1 + √(e^κ - 1))`, instead of `e^κ - 1`. -/
theorem finalCoef_close_quarterBox_weighted {d M L : ℕ} [NeZero L] (hd : 0 < d) (hM : 0 < M)
    {κ : ℝ} (hκ : 1 ≤ κ)
    (hMB : 4 * (pdB d L * Real.exp (pdH d * κ)) ≤ M) (hMκ : 8 * κ * 7 ^ d ≤ pdEps d L * M)
    {rE η : ℝ} (hrE : pdEps d L / 4 ≤ rE) (hη0 : 0 ≤ η)
    (hη : 4 * (Real.exp (pdH d * κ) * (2 / finalGap d L * η *
      ballConst d (3 * pdEps d L / 4))) ≤ 1) :
    ∃ P C₀ c₀ : ℝ, 0 ≤ P ∧ 0 < C₀ ∧ 0 < c₀ ∧ ∀ {k : ℕ}, 1 ≤ k →
      ∀ {N N' : ℕ} [NeZero N] [NeZero N'], M ∣ N → M ∣ N' → N ≤ N' →
      ∀ {m t : ℕ}, 5 ≤ t → 4 * (m + t) ≤ macK N M →
      ∀ {f : L1Torus d N → L1Torus d N'},
      (∀ x μ, f x μ + ((M * (m + 4) : ℕ) : ZMod N') =
        ((((x μ + ((M * (m + 4) : ℕ) : ZMod N)).val : ℕ)) : ZMod N')) →
      ∀ {e : MacIdx d N M → MacIdx d N' M},
      (∀ z i, ((z i : ℕ) + (m + 4)) % macK N M ≤ 2 * m + 8 →
        ((e z i : ℕ) + (m + 4)) % macK N' M = ((z i : ℕ) + (m + 4)) % macK N M) →
      ∀ {C : Finset (MacIdx d N M)},
      (∀ z ∈ C, ∀ i, (z i : ℕ) ≤ m ∨ macK N M - m ≤ (z i : ℕ)) →
      ∀ {v a : ℝ}, 0 ≤ v → v ≤ 1 → 1 / 2 ≤ a → a ≤ 2 → 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v →
      ((∀ {s : ℝ}, 0 ≤ s →
        ∀ {E : Matrix (L1Torus d N) (L1Torus d N) ℂ} {E' : Matrix (L1Torus d N') (L1Torus d N') ℂ},
        WSmall rE η E → WSmall rE η E' → ∀ {εE : ℝ}, 0 ≤ εE →
        (∀ x ∈ macRegion d N M C, ∀ y ∈ macRegion d N M C,
          ‖E x y - E' (f x) (f y)‖ ≤ εE) →
        ∀ {ρ ρ' : ℝ}, Real.exp κ < ρ → Real.exp κ < ρ' →
        ∀ {ell : (MacIdx d N M → ℂ) → ℂ} {ell' : (MacIdx d N' M → ℂ) → ℂ},
        AnalyticOnNhd ℂ ell (Metric.ball 0 ρ) → AnalyticOnNhd ℂ ell' (Metric.ball 0 ρ') →
        ell 0 = 0 → ell' 0 = 0 →
        (∀ s' ∈ Metric.ball (0 : MacIdx d N M → ℂ) ρ,
          (1 - taggedMat Finset.univ (macTags d N M)
            (fun z => boxR (finalOp d L N k v a) (macBoxF d N M z)
                (fun u => ((macChi d N M z u : ℝ) : ℂ)) s -
              E * (Matrix.diagonal (fun u => ((macChi d N M z u : ℝ) : ℂ)) *
                boxG (finalOp d L N k v a) (macBoxF d N M z) s)) s').det =
            Complex.exp (ell s')) →
        (∀ s' ∈ Metric.ball (0 : MacIdx d N' M → ℂ) ρ',
          (1 - taggedMat Finset.univ (macTags d N' M)
            (fun z => boxR (finalOp d L N' k v a) (macBoxF d N' M z)
                (fun u => ((macChi d N' M z u : ℝ) : ℂ)) s -
              E' * (Matrix.diagonal (fun u => ((macChi d N' M z u : ℝ) : ℂ)) *
                boxG (finalOp d L N' k v a) (macBoxF d N' M z) s)) s').det =
            Complex.exp (ell' s')) →
        ‖coef ell C - coef ell' (C.image e)‖ ≤
          P * (C₀ * Real.exp (-c₀ * ((M : ℝ) * (2 * (t : ℝ) - 7))) + Real.sqrt εE) /
            (Real.sqrt (Real.exp κ - 1)) ^ C.card) ∧
       (∀ {γ : Measure (L1Torus d N → ℝ)} {γ' : Measure (L1Torus d N' → ℝ)} {ρ RF B' Lip : ℝ},
        0 ≤ ρ →
        γ {ψ : L1Torus d N → ℝ | ∀ y, |ψ y| ≤ ρ} < ⊤ →
        γ' {ψ : L1Torus d N' → ℝ | ∀ y, |ψ y| ≤ ρ} < ⊤ →
        (4 / 3 * (2 * Real.exp (pdH d * κ) * ballConst d (pdEps d L / 2)) /
          Real.sqrt (finalGap d L)) * ρ < RF →
        ∀ {F : (L1Torus d N → ℂ) → ℂ} {F' : (L1Torus d N' → ℂ) → ℂ},
        AnalyticOnNhd ℂ F (polydisc (0 : L1Torus d N → ℂ) (fun _ => RF)) →
        (∀ w ∈ polydisc (0 : L1Torus d N → ℂ) (fun _ => RF), ‖F w‖ ≤ B') →
        AnalyticOnNhd ℂ F' (polydisc (0 : L1Torus d N' → ℂ) (fun _ => RF)) →
        (∀ w ∈ polydisc (0 : L1Torus d N' → ℂ) (fun _ => RF), ‖F' w‖ ≤ B') →
        Measurable F → Measurable F' →
        (∀ (w : L1Torus d N → ℂ) (w' : L1Torus d N' → ℂ),
          (∀ x, x ∉ macRegion d N M C → w x = 0) →
          (∀ x', x' ∉ macRegion d N' M (C.image e) → w' x' = 0) →
          (∀ x, ‖w x‖ ≤ (4 / 3 * (2 * Real.exp (pdH d * κ) * ballConst d (pdEps d L / 2)) /
            Real.sqrt (finalGap d L)) * ρ) →
          (∀ x', ‖w' x'‖ ≤ (4 / 3 * (2 * Real.exp (pdH d * κ) * ballConst d (pdEps d L / 2)) /
            Real.sqrt (finalGap d L)) * ρ) → ∀ η : ℝ, 0 ≤ η →
          (∀ x ∈ macRegion d N M C, ‖w' (f x) - w x‖ ≤ η) → ‖F' w' - F w‖ ≤ Lip * η) →
        Measure.map (fun (ψ : L1Torus d N → ℝ) (q : ↥(macRegion d N M C)) => ψ q)
            (γ.restrict {ψ : L1Torus d N → ℝ | ∀ y, |ψ y| ≤ ρ}) =
          Measure.map (fun (ψ' : L1Torus d N' → ℝ) (q : ↥(macRegion d N M C)) => ψ' (f q))
            (γ'.restrict {ψ' : L1Torus d N' → ℝ | ∀ y, |ψ' y| ≤ ρ}) →
        ‖coef (fun s : MacIdx d N M → ℂ => ∫ ψ in {ψ : L1Torus d N → ℝ | ∀ y, |ψ y| ≤ ρ},
            F (fun x => ∑ y, taggedCfin d L N k M v a s x y * ((ψ y : ℝ) : ℂ)) ∂γ) C -
          coef (fun s' : MacIdx d N' M → ℂ => ∫ ψ' in {ψ' : L1Torus d N' → ℝ | ∀ y, |ψ' y| ≤ ρ},
            F' (fun x => ∑ y, taggedCfin d L N' k M v a s' x y * ((ψ' y : ℝ) : ℂ)) ∂γ')
            (C.image e)‖ ≤
          Lip * ((((8 * M + 1) ^ d : ℕ) : ℝ) *
            (P * (C₀ * Real.exp (-c₀ * ((M : ℝ) * (2 * (t : ℝ) - 7)))) /
              Real.sqrt (finalGap d L)) * ρ) *
            (γ {ψ : L1Torus d N → ℝ | ∀ y, |ψ y| ≤ ρ}).toReal /
              (Real.sqrt (Real.exp κ - 1)) ^ C.card))
 := by
  classical
  have hκ0 : 0 < κ := by linarith
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hg : 0 < Real.sqrt (finalGap d L) := Real.sqrt_pos.2 (finalGap_pos (d := d) hL)
  obtain ⟨P1, C1, c1, hP1, hC1, hc1, hu1⟩ :=
    final_coef_logdet_close_twoTorus_unif_weighted (L := L) hd hM hκ0 hMB hMκ hrE hη0 hη
  obtain ⟨P2, C2, c2, hP2, hC2, hc2, hu2⟩ :=
    final_coef_cutoffInteraction_close_twoTorus_unif_weighted (L := L) hd hM hκ hMB hMκ
  have hρ1 : 1 < Real.exp κ - 1 := by
    have h1 : (1 : ℝ) + 1 < Real.exp 1 := Real.add_one_lt_exp (by norm_num)
    have h2 : Real.exp 1 ≤ Real.exp κ := Real.exp_le_exp.2 hκ
    linarith
  have hden : ∀ c : ℕ, 0 < (Real.exp κ - 1) ^ c := fun c => pow_pos (by linarith) c
  have hdenr : ∀ c : ℕ, 0 < (Real.sqrt (Real.exp κ - 1)) ^ c := fun c =>
    pow_pos (Real.sqrt_pos.2 (by linarith)) c
  obtain ⟨A3, hA3, h3⟩ := exists_pow_div_le_sqrt hρ1 3
  obtain ⟨A5, hA5, h5⟩ := exists_pow_div_le_sqrt hρ1 5
  refine ⟨max (P1 * A3) (P2 * (A3 + A5)), max (Real.sqrt C1) (Real.sqrt C2),
    min (c1 / 2) (c2 / 2), le_max_of_le_left (mul_nonneg hP1 hA3),
    lt_max_of_lt_left (Real.sqrt_pos.2 hC1), lt_min (half_pos hc1) (half_pos hc2), ?_⟩
  intro k hk N N' _ _ hMN hMN' hNN m t ht hbox f hf e he C hC v a hv0 hv1 ha1 ha2 hmass
  have hy : (0 : ℝ) ≤ (M : ℝ) * (2 * (t : ℝ) - 7) := by
    have : (5 : ℝ) ≤ t := by exact_mod_cast ht
    have : (0 : ℝ) ≤ M := by positivity
    nlinarith
  set y : ℝ := (M : ℝ) * (2 * (t : ℝ) - 7) with hydef
  refine ⟨?_, ?_⟩
  · intro s hs E E' hE hE' εE hεE hEcl ρ ρ' hρ hρ' ell ell' hell hell' h0 h0' hdet hdet'
    set Φ1 : ℝ → ℝ → ℕ → ℝ := fun X εE' c => P1 * (C.card : ℝ) ^ 3 *
      (Real.sqrt (C1 * Real.exp (-c1 * X)) + Real.sqrt εE') / (Real.exp κ - 1) ^ c with hΦ1
    have hΦ1m : ∀ {X X' : ℝ} (εE' : ℝ) (c : ℕ), X ≤ X' → Φ1 X' εE' c ≤ Φ1 X εE' c := by
      intro X X' εE' c hX
      refine div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
        (add_le_add_left (Real.sqrt_le_sqrt ?_) _) (by positivity)) (hden c).le
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by nlinarith)) hC1.le
    have hq := @finalCoef_logdet_close_quarterBox_of d M L _ hM κ rE η C.card Φ1 hΦ1m
      (@final_coef_logdet_close_twoTorus_box_of d M L _ κ hκ0 rE η C.card Φ1 (hu1 C.card))
    have key := hq hk hMN hMN' hNN ht hbox hf he le_rfl hC hv0 hv1 ha1 ha2 hmass hs hE hE' hεE
      hEcl hρ hρ' hell hell' h0 h0' hdet hdet'
    refine key.trans ?_
    show P1 * (C.card : ℝ) ^ 3 * (Real.sqrt (C1 * Real.exp (-c1 * y)) + Real.sqrt εE) /
      (Real.exp κ - 1) ^ C.card ≤ _
    rw [sqrt_mul_exp_neg C1 c1 y hC1.le]
    set Z : ℝ := Real.sqrt C1 * Real.exp (-(c1 / 2) * y) + Real.sqrt εE with hZ
    have hZ0 : 0 ≤ Z := by positivity
    have hZZ : Z ≤ max (Real.sqrt C1) (Real.sqrt C2) * Real.exp (-(min (c1 / 2) (c2 / 2)) * y) +
        Real.sqrt εE := by
      refine add_le_add ?_ le_rfl
      have := bound_mono_aux (Q := 1) (Q' := 1) (K := Real.sqrt C1)
        (K' := max (Real.sqrt C1) (Real.sqrt C2)) (c := c1 / 2) (c' := min (c1 / 2) (c2 / 2)) (y := y)
        zero_le_one le_rfl (Real.sqrt_nonneg _) (le_max_left _ _) (min_le_left _ _) hy
      simpa using this
    calc P1 * (C.card : ℝ) ^ 3 * Z / (Real.exp κ - 1) ^ C.card
        = P1 * Z * ((C.card : ℝ) ^ 3 / (Real.exp κ - 1) ^ C.card) := by ring
      _ ≤ P1 * Z * (A3 / (Real.sqrt (Real.exp κ - 1)) ^ C.card) :=
          mul_le_mul_of_nonneg_left (h3 C.card) (by positivity)
      _ = (P1 * A3) * Z / (Real.sqrt (Real.exp κ - 1)) ^ C.card := by ring
      _ ≤ max (P1 * A3) (P2 * (A3 + A5)) *
            (max (Real.sqrt C1) (Real.sqrt C2) * Real.exp (-(min (c1 / 2) (c2 / 2)) * y) +
              Real.sqrt εE) / (Real.sqrt (Real.exp κ - 1)) ^ C.card :=
          div_le_div_of_nonneg_right (mul_le_mul (le_max_left _ _) hZZ hZ0
            (le_max_of_le_left (mul_nonneg hP1 hA3))) (hdenr C.card).le
  · intro γ γ' ρ RF B' Lip hρ hγfin hγfin' hBR F F' hFan hFB hFan' hFB' hFm hFm' hFclose hγ
    set Ψ2 : ℝ → ℝ := fun X => P2 * ((C.card : ℝ) ^ 2 + (C.card : ℝ) ^ 4) *
      Real.sqrt (C2 * Real.exp (-c2 * X)) / Real.sqrt (finalGap d L) with hΨ2
    have hΨ2m : ∀ {X X' : ℝ}, X ≤ X' → Ψ2 X' ≤ Ψ2 X := by
      intro X X' hX
      refine div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_)
        (by positivity)) hg.le
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by nlinarith)) hC2.le
    have hq := @finalCoef_cutoff_close_quarterBox_of d M L _ hd κ hκ C.card Ψ2 hΨ2m
      (@final_coef_cutoffInteraction_close_twoTorus_box_of d M L _ hd hM κ hκ hMB hMκ C.card Ψ2
        (hu2 C.card))
    have key := hq hk hMN hMN' hNN ht hbox hf he le_rfl hC hv0 hv1 ha1 ha2 hmass hρ hγfin hγfin'
      hBR hFan hFB hFan' hFB' hFm hFm' hFclose hγ
    have hBc0 : 0 ≤ 4 / 3 * (2 * Real.exp (pdH d * κ) * ballConst d (pdEps d L / 2)) /
        Real.sqrt (finalGap d L) := by
      have : 0 ≤ ballConst d (pdEps d L / 2) :=
        ballConst_decay_nonneg (by have := pdEps_pos (d := d) (L := L) hd; positivity)
      positivity
    have hLip : 0 ≤ Lip := by
      have := hFclose 0 0 (fun _ _ => rfl) (fun _ _ => rfl)
        (fun x => by simpa using mul_nonneg hBc0 hρ)
        (fun x => by simpa using mul_nonneg hBc0 hρ) 1 zero_le_one (fun x _ => by simp)
      exact le_trans (norm_nonneg _) (by simpa using this)
    refine key.trans ?_
    show Lip * (((C.card * (8 * M + 1) ^ d : ℕ) : ℝ) * (P2 * ((C.card : ℝ) ^ 2 +
        (C.card : ℝ) ^ 4) * Real.sqrt (C2 * Real.exp (-c2 * y)) / Real.sqrt (finalGap d L)) * ρ) *
      (γ {ψ : L1Torus d N → ℝ | ∀ y, |ψ y| ≤ ρ}).toReal / (Real.exp κ - 1) ^ C.card ≤ _
    rw [Nat.cast_mul, sqrt_mul_exp_neg C2 c2 y hC2.le]
    refine cutoff_absorb_aux (n := C.card) hLip (by positivity) hP2 (by positivity) hg hρ
      ENNReal.toReal_nonneg (hdenr C.card) (h3 C.card) (h5 C.card) ?_
    exact bound_mono_aux (Q := P2 * (A3 + A5)) (Q' := max (P1 * A3) (P2 * (A3 + A5)))
      (K := Real.sqrt C2) (K' := max (Real.sqrt C1) (Real.sqrt C2)) (c := c2 / 2)
      (c' := min (c1 / 2) (c2 / 2)) (y := y) (mul_nonneg hP2 (add_nonneg hA3 hA5))
      (le_max_right _ _) (Real.sqrt_nonneg _) (le_max_right _ _) (min_le_right _ _) hy

end Balaban.Green
