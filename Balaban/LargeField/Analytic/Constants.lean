/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Flow.RunningCoefficients
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Running constants and the a priori sequence (LF-RECONSTRUCTION §II.1, blocks F1–F3)

Definition II.1.1: the quantities derived from the running coefficients `β_j`, `ν_j` of the flow,

* `runLam`, `runR`, `pZero`, `pOne`, `deltaRun`, `epsRun`, `epsOneRun`, `p2Run`, `HRun`;
* `bgMass` (`μ_j`), `betaCanon` (`β^{(q)}_n`), `aCanon` (`a^{(q)}_n`);
* `kZero` (the a priori regime index `k₀ = max {k : β ν L^{kd} ≤ 1}`, Part IV D-IV.11; `0` when the
  set is empty), `KZeroGenuine` (`β ν ≤ 1`), `kF` (first `k` with `ν_k > 7/8 L⁻²`).

The a priori sequence `lamHat` (`λ̂_j = log (β a) + 1 + j θ`, `θ = (d-2) log L`) and the hypothesis
`RunningHyp` (P4 (H.6), (I.2): `β_k = β L^{k(d-2)} γ_k`, `ν_k = ν L^{2k} δ_k`, `|log γ_k|,
|log δ_k| ≤ ε`), which is derived from the landed `betaSeq_eq`, `nuSeq_eq`, `norm_gammaSeq_le` by
`RunningHyp.of_flow`.

Lemma II.1.2 (a)-(e) is `runLam_le_hat`, `hat_le_runLam_add_two`, `runR_ge_base`, `runR_le_hat`,
`logBeta_ge`, `logBeta_le`, `p2Run_le`, `HRun_ge`, `HRun_le`, `deltaRun_le_bar`,
`deltaBar_antitoneOn`, `gain_conv`, `logBeta_succ_le`.  Part F3: `AnalyticLamAt`,
`AnalyticLamConditions` ((Λ15)-(Λ17), (Λ17′)).
-/

@[expose] public section

open Finset

namespace Balaban.LargeField

/-! ### The a priori sequence and the hypothesis (I.2) -/

/-- `θ = (d - 2) log L`. -/
noncomputable def thetaOf (d L : ℕ) : ℝ := ((d - 2 : ℕ) : ℝ) * Real.log L

/-- The a priori sequence `λ̂_j = log (β a) + 1 + j θ` (I.1). -/
noncomputable def lamHat (d L : ℕ) (β a : ℝ) (j : ℕ) : ℝ :=
  Real.log (β * a) + 1 + (j : ℝ) * thetaOf d L

/-- The a priori radii `R̂_j = R_base λ̂_j²`. -/
noncomputable def hatR (d L : ℕ) (Rb β a : ℝ) (j : ℕ) : ℝ := Rb * lamHat d L β a j ^ 2

/-- The a priori `k̂_f = min {k : ν L^{2k+2} ≥ 1}` (`0` if there is none). -/
noncomputable def kFHat (L : ℕ) (ν : ℝ) : ℕ := sInf {k : ℕ | 1 ≤ ν * (L : ℝ) ^ (2 * k + 2)}

/-- The hypotheses (I.2) on the running coefficients: `β_k = β L^{k(d-2)} γ_k`,
`ν_k = ν L^{2k} δ_k`, with `|log γ_k|, |log δ_k| ≤ ε`, `ε ≤ 1/20`; `a ∈ (1, 3/2)`. -/
structure RunningHyp (d L : ℕ) (β ν a ε : ℝ) (betaRun nuRun : ℕ → ℝ) : Prop where
  hd : 2 ≤ d
  hL : 2 ≤ L
  hβ : 0 < β
  hν : 0 < ν
  ha1 : 1 < a
  ha2 : a < 3 / 2
  hε0 : 0 ≤ ε
  hε : ε ≤ 1 / 20
  beta_eq : ∀ k, ∃ γ : ℝ, 0 < γ ∧ |Real.log γ| ≤ ε ∧
    betaRun k = β * (L : ℝ) ^ (k * (d - 2)) * γ
  nu_eq : ∀ k, ∃ δ : ℝ, 0 < δ ∧ |Real.log δ| ≤ ε ∧ nuRun k = ν * (L : ℝ) ^ (2 * k) * δ

/-! ### Definition II.1.1 -/

/-- `λ_j = log (β_j a)` (running). -/
noncomputable def runLam (a : ℝ) (b : ℕ → ℝ) (j : ℕ) : ℝ := Real.log (b j * a)

/-- `R_j = R_base λ_j²` (running). -/
noncomputable def runR (Rb a : ℝ) (b : ℕ → ℝ) (j : ℕ) : ℝ := Rb * runLam a b j ^ 2

/-- `p₀(β_j) = A₀ λ_j^{p₀}`. -/
noncomputable def pZero (A0 : ℝ) (p0 : ℕ) (a : ℝ) (b : ℕ → ℝ) (j : ℕ) : ℝ :=
  A0 * runLam a b j ^ p0

/-- `p₁(β_j) = A₁ λ_j^{p₁}` with `p₁ = p₀` (P6 (3.9)). -/
noncomputable def pOne (A1 : ℝ) (p0 : ℕ) (a : ℝ) (b : ℕ → ℝ) (j : ℕ) : ℝ :=
  A1 * runLam a b j ^ p0

/-- `δ_j = (β_j a)^{-1/2} p₀(β_j)` (P5 p. 498). -/
noncomputable def deltaRun (A0 : ℝ) (p0 : ℕ) (a : ℝ) (b : ℕ → ℝ) (j : ℕ) : ℝ :=
  (b j * a) ^ (-(1 / 2 : ℝ)) * pZero A0 p0 a b j

/-- `ε_j = α₀ (1 + Σ_{n ≥ j} n⁻²) L^{-jα}` (SF §1.7). -/
noncomputable def epsRun (α0 α : ℝ) (L : ℕ) (j : ℕ) : ℝ :=
  α0 * (1 + ∑' n : ℕ, ((n + j : ℕ) : ℝ)⁻¹ ^ 2) * (L : ℝ) ^ (-((j : ℝ) * α))

/-- `ε_{1,j} = (A₁/A₀) ε_j`. -/
noncomputable def epsOneRun (A0 A1 α0 α : ℝ) (L : ℕ) (j : ℕ) : ℝ := A1 / A0 * epsRun α0 α L j

/-- `p₂(β_j) = A₂ (log β_j)^{p₂}`. -/
noncomputable def p2Run (A2 : ℝ) (p2 : ℕ) (b : ℕ → ℝ) (j : ℕ) : ℝ := A2 * Real.log (b j) ^ p2

/-- `H_j = H₀ log β_j`. -/
noncomputable def HRun (H0 : ℝ) (b : ℕ → ℝ) (j : ℕ) : ℝ := H0 * Real.log (b j)

/-- The fine-unit mass of the backgrounds at scale `j`: `0` if `j ≤ k₀`, `ν_j L^{-2j}` otherwise
(P5 (1.9); `k₀` the a priori index, D-IV.11). -/
noncomputable def bgMass (k0 : ℕ) (L : ℕ) (n : ℕ → ℝ) (j : ℕ) : ℝ :=
  if j ≤ k0 then 0 else n j / (L : ℝ) ^ (2 * j)

/-- `β^{(q)}_n = β_q L^{-(q-n)(d-2)}` (P5 (1.41)). -/
noncomputable def betaCanon (d L : ℕ) (βq : ℝ) (q n : ℕ) : ℝ := βq / (L : ℝ) ^ ((q - n) * (d - 2))

/-- `a^{(q)}_n = a_q (1 - L^{-2q})/(1 - L^{-2n})` (P5 (1.41)). -/
noncomputable def aCanon (L : ℕ) (aq : ℝ) (q n : ℕ) : ℝ :=
  aq * (1 - ((L : ℝ) ^ (2 * q))⁻¹) / (1 - ((L : ℝ) ^ (2 * n))⁻¹)

/-- The a priori regime index `k₀ = max {k : β ν L^{kd} ≤ 1}` (Part IV D-IV.11); `0` if the set is
empty (the conventional value for `β ν > 1`). -/
noncomputable def kZero (d L : ℕ) (β ν : ℝ) : ℕ :=
  sSup {k : ℕ | β * ν * (L : ℝ) ^ (k * d) ≤ 1}

/-- `k₀` is *genuine* if `β ν ≤ 1`; for `β ν > 1`, `k₀ = 0` is conventional. -/
def KZeroGenuine (β ν : ℝ) : Prop := β * ν ≤ 1

/-- `k_f`: the first `k` with `ν_k > 7/8 L⁻²` (`0` if there is none). -/
noncomputable def kF (L : ℕ) (n : ℕ → ℝ) : ℕ := sInf {k : ℕ | 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < n k}

section KZero

variable {d L : ℕ} {β ν : ℝ}

theorem kZero_bddAbove (hd : 1 ≤ d) (hL : 2 ≤ L) (hβν : 0 < β * ν) :
    BddAbove {k : ℕ | β * ν * (L : ℝ) ^ (k * d) ≤ 1} := by
  have hL' : (1 : ℝ) < L := by exact_mod_cast hL
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (1 / (β * ν)) hL'
  refine ⟨n, fun k hk => ?_⟩
  by_contra hlt
  push Not at hlt
  have h1 : (L : ℝ) ^ n ≤ (L : ℝ) ^ (k * d) :=
    pow_le_pow_right₀ hL'.le (le_trans hlt.le (Nat.le_mul_of_pos_right k hd))
  have h2 : 1 / (β * ν) < (L : ℝ) ^ (k * d) := lt_of_lt_of_le hn h1
  rw [div_lt_iff₀ hβν] at h2
  exact absurd hk (by simp only [Set.mem_ofPred_eq, not_le]; linarith)

/-- If `β ν ≤ 1` (genuine case), `k₀` satisfies `β ν L^{k₀ d} ≤ 1`. -/
theorem kZero_spec (hd : 1 ≤ d) (hL : 2 ≤ L) (hβν : 0 < β * ν) (hg : KZeroGenuine β ν) :
    β * ν * (L : ℝ) ^ (kZero d L β ν * d) ≤ 1 := by
  have hne : ({k : ℕ | β * ν * (L : ℝ) ^ (k * d) ≤ 1}).Nonempty :=
    ⟨0, by have h : β * ν ≤ 1 := hg; simpa using h⟩
  exact Nat.sSup_mem hne (kZero_bddAbove hd hL hβν)

/-- Maximality: `β ν L^{(k₀+1) d} > 1`. -/
theorem lt_kZero_succ (hd : 1 ≤ d) (hL : 2 ≤ L) (hβν : 0 < β * ν) :
    1 < β * ν * (L : ℝ) ^ ((kZero d L β ν + 1) * d) := by
  by_contra h
  push Not at h
  have h2 : kZero d L β ν + 1 ≤ kZero d L β ν := le_csSup (kZero_bddAbove hd hL hβν) h
  omega

/-- In the non-genuine case `k₀ = 0` (the convention). -/
theorem kZero_of_not_genuine (hL : 2 ≤ L) (hg : ¬ KZeroGenuine β ν) :
    kZero d L β ν = 0 := by
  have hL' : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have : {k : ℕ | β * ν * (L : ℝ) ^ (k * d) ≤ 1} = ∅ := by
    ext k
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le]
    have := one_le_pow₀ (n := k * d) hL'
    unfold KZeroGenuine at hg
    push Not at hg
    nlinarith
  simp [kZero, this]

end KZero

/-! ### Lemma II.1.2 -/

namespace RunningHyp

variable {d L : ℕ} {β ν a ε : ℝ} {b n : ℕ → ℝ}

theorem theta_nonneg (h : RunningHyp d L β ν a ε b n) : 0 ≤ thetaOf d L := by
  unfold thetaOf
  have : (1 : ℝ) ≤ L := by exact_mod_cast (by have := h.hL; omega : 1 ≤ L)
  exact mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg this)

theorem betaRun_pos (h : RunningHyp d L β ν a ε b n) (j : ℕ) : 0 < b j := by
  obtain ⟨γ, hγ, -, he⟩ := h.beta_eq j
  rw [he]
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (by have := h.hL; omega : 0 < L)
  exact mul_pos (mul_pos h.hβ (pow_pos hLpos _)) hγ

/-- `log β_j = log β + j (d-2) log L + log γ_j`; hence `λ_j = λ̂_j - 1 + log γ_j`. -/
theorem runLam_eq (h : RunningHyp d L β ν a ε b n) (j : ℕ) :
    ∃ γ : ℝ, |Real.log γ| ≤ ε ∧ runLam a b j = lamHat d L β a j - 1 + Real.log γ := by
  obtain ⟨γ, hγ, hlog, he⟩ := h.beta_eq j
  refine ⟨γ, hlog, ?_⟩
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (by have := h.hL; omega : 0 < L)
  have ha : 0 < a := by linarith [h.ha1]
  unfold runLam lamHat thetaOf
  rw [he]
  have e1 : β * (L : ℝ) ^ (j * (d - 2)) * γ * a = (β * a) * (L : ℝ) ^ (j * (d - 2)) * γ := by ring
  have hβa : 0 < β * a := mul_pos h.hβ ha
  have hLp : 0 < (L : ℝ) ^ (j * (d - 2)) := pow_pos hLpos _
  rw [e1, Real.log_mul (mul_pos hβa hLp).ne' hγ.ne', Real.log_mul hβa.ne' hLp.ne', Real.log_pow]
  have : ((j * (d - 2) : ℕ) : ℝ) = (j : ℝ) * ((d - 2 : ℕ) : ℝ) := by push_cast; ring
  rw [this]
  ring

theorem runLam_le_hat (h : RunningHyp d L β ν a ε b n) (j : ℕ) :
    runLam a b j ≤ lamHat d L β a j := by
  obtain ⟨γ, hγ, he⟩ := h.runLam_eq j
  have := (abs_le.1 hγ).2
  have := h.hε
  rw [he]; linarith

theorem hat_le_runLam_add_two (h : RunningHyp d L β ν a ε b n) (j : ℕ) :
    lamHat d L β a j ≤ runLam a b j + 2 := by
  obtain ⟨γ, hγ, he⟩ := h.runLam_eq j
  have := (abs_le.1 hγ).1
  have := h.hε
  rw [he]; linarith

theorem lamHat_mono (h : RunningHyp d L β ν a ε b n) (j : ℕ) :
    lamHat d L β a 0 ≤ lamHat d L β a j := by
  unfold lamHat
  have := h.theta_nonneg
  have : (0 : ℝ) ≤ (j : ℝ) * thetaOf d L := mul_nonneg (Nat.cast_nonneg _) this
  simp only [Nat.cast_zero, zero_mul]
  linarith

/-- `λ_j ≥ 1` when `λ̂_0 ≥ 3`. -/
theorem one_le_runLam (h : RunningHyp d L β ν a ε b n) (h3 : 3 ≤ lamHat d L β a 0) (j : ℕ) :
    1 ≤ runLam a b j := by
  have := h.hat_le_runLam_add_two j
  have := h.lamHat_mono j
  linarith

/-- `R_base ≤ R_j` (Lemma II.1.2 (a)). -/
theorem runR_ge_base (h : RunningHyp d L β ν a ε b n) {Rb : ℝ} (hR : 0 ≤ Rb)
    (h3 : 3 ≤ lamHat d L β a 0) (j : ℕ) : Rb ≤ runR Rb a b j := by
  have h1 := h.one_le_runLam h3 j
  unfold runR
  nlinarith [mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ runLam a b j ^ 2 by nlinarith) hR]

/-- `R_j ≤ R̂_j` (Lemma II.1.2 (a)). -/
theorem runR_le_hat (h : RunningHyp d L β ν a ε b n) {Rb : ℝ} (hR : 0 ≤ Rb)
    (h3 : 3 ≤ lamHat d L β a 0) (j : ℕ) : runR Rb a b j ≤ hatR d L Rb β a j := by
  have h1 := h.one_le_runLam h3 j
  have h2 := h.runLam_le_hat j
  unfold runR hatR
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) h2 2) hR

theorem log_a_lt (h : RunningHyp d L β ν a ε b n) : Real.log a < 1 / 2 := by
  have := Real.log_le_sub_one_of_pos (show 0 < a by linarith [h.ha1])
  linarith [h.ha2]

theorem log_a_nonneg (h : RunningHyp d L β ν a ε b n) : 0 ≤ Real.log a :=
  Real.log_nonneg h.ha1.le

theorem log_betaRun (h : RunningHyp d L β ν a ε b n) (j : ℕ) :
    Real.log (b j) = runLam a b j - Real.log a := by
  have ha : 0 < a := by linarith [h.ha1]
  unfold runLam
  rw [Real.log_mul (h.betaRun_pos j).ne' ha.ne']; ring

/-- Lemma II.1.2 (b): `λ̂_j - 3 ≤ log β_j`. -/
theorem logBeta_ge (h : RunningHyp d L β ν a ε b n) (j : ℕ) :
    lamHat d L β a j - 3 ≤ Real.log (b j) := by
  have := h.hat_le_runLam_add_two j
  have := h.log_a_lt
  rw [h.log_betaRun]; linarith

/-- Lemma II.1.2 (b): `log β_j ≤ λ̂_j`. -/
theorem logBeta_le (h : RunningHyp d L β ν a ε b n) (j : ℕ) :
    Real.log (b j) ≤ lamHat d L β a j := by
  have := h.runLam_le_hat j
  have := h.log_a_nonneg
  rw [h.log_betaRun]; linarith

/-- `p₂(β_j) ≤ A₂ λ̂_j^{p₂}` (so `τ_j = 2 A₂ λ̂_j^{p₂} ≥ 2 p₂(β_j)`). -/
theorem p2Run_le (h : RunningHyp d L β ν a ε b n) {A2 : ℝ} (hA : 0 ≤ A2) (p2 : ℕ)
    (h3 : 3 ≤ lamHat d L β a 0) (j : ℕ) : p2Run A2 p2 b j ≤ A2 * lamHat d L β a j ^ p2 := by
  have h1 := h.logBeta_ge j
  have h2 := h.logBeta_le j
  have h4 := h.lamHat_mono j
  unfold p2Run
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) h2 p2) hA

theorem HRun_ge (h : RunningHyp d L β ν a ε b n) {H0 : ℝ} (hH : 0 ≤ H0) (j : ℕ) :
    H0 * (lamHat d L β a j - 3) ≤ HRun H0 b j :=
  mul_le_mul_of_nonneg_left (h.logBeta_ge j) hH

theorem HRun_le (h : RunningHyp d L β ν a ε b n) {H0 : ℝ} (hH : 0 ≤ H0) (j : ℕ) :
    HRun H0 b j ≤ H0 * lamHat d L β a j :=
  mul_le_mul_of_nonneg_left (h.logBeta_le j) hH

/-- Lemma II.1.2 (e): `log β_{k+1} - log β_k ≤ (d-2) log L + 2ε`. -/
theorem logBeta_succ_le (h : RunningHyp d L β ν a ε b n) (k : ℕ) :
    Real.log (b (k + 1)) - Real.log (b k) ≤ thetaOf d L + 2 * ε := by
  obtain ⟨γ, hγ, he⟩ := h.runLam_eq k
  obtain ⟨γ', hγ', he'⟩ := h.runLam_eq (k + 1)
  rw [h.log_betaRun, h.log_betaRun, he, he']
  have := (abs_le.1 hγ).1
  have := (abs_le.1 hγ').2
  unfold lamHat
  push_cast
  linarith

/-- Lemma II.1.2 (d): under (Λ15), `A₃ (log β_k)^{2p₀} ≥ ½ A₃ λ̂_k^{2p₀}`. -/
theorem gain_conv (h : RunningHyp d L β ν a ε b n) {A3 : ℝ} (hA : 0 ≤ A3) {p0 : ℕ} (hp : 1 ≤ p0)
    (k : ℕ) (hk : 3 / (1 - (2 : ℝ) ^ (-(1 / (2 * (p0 : ℝ))))) ≤ lamHat d L β a k) :
    1 / 2 * A3 * lamHat d L β a k ^ (2 * p0) ≤ A3 * Real.log (b k) ^ (2 * p0) := by
  set x := lamHat d L β a k with hx
  have hp' : (0 : ℝ) < 2 * p0 := by positivity
  set c : ℝ := (2 : ℝ) ^ (-(1 / (2 * (p0 : ℝ)))) with hc
  have hc1 : c < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by
    have : 0 < 1 / (2 * (p0 : ℝ)) := by positivity
    linarith)
  have hc0 : 0 < c := Real.rpow_pos_of_pos (by norm_num) _
  have hcp : c ^ (2 * p0) = 1 / 2 := by
    rw [hc, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have : -(1 / (2 * (p0 : ℝ))) * ((2 * p0 : ℕ) : ℝ) = -1 := by
      push_cast; field_simp
    rw [this, Real.rpow_neg_one]; norm_num
  have hxpos : 3 ≤ x := by
    have : 3 / (1 - c) ≥ 3 := by
      rw [ge_iff_le, le_div_iff₀ (by linarith)]; nlinarith
    linarith
  have h1 : c ≤ 1 - 3 / x := by
    have : 3 / x ≤ 1 - c := by
      rw [div_le_iff₀ (by linarith)]
      have := (div_le_iff₀ (by linarith : 0 < 1 - c)).1 hk
      linarith
    linarith
  have h2 : c ^ (2 * p0) ≤ (1 - 3 / x) ^ (2 * p0) := pow_le_pow_left₀ hc0.le h1 _
  have h3 : (x - 3) ^ (2 * p0) = x ^ (2 * p0) * (1 - 3 / x) ^ (2 * p0) := by
    rw [← mul_pow]; congr 1; field_simp
  have h4 : (x - 3) ^ (2 * p0) ≤ Real.log (b k) ^ (2 * p0) :=
    pow_le_pow_left₀ (by linarith) (h.logBeta_ge k) _
  have h5 : 1 / 2 * x ^ (2 * p0) ≤ (x - 3) ^ (2 * p0) := by
    rw [h3]
    have := mul_le_mul_of_nonneg_left h2 (pow_nonneg (by linarith : 0 ≤ x) (2 * p0))
    rw [hcp] at this; linarith
  nlinarith [mul_le_mul_of_nonneg_left (h5.trans h4) hA]

end RunningHyp

/-- `δ̄(x) = e A₀ x^{p₀} e^{-x/2}` (Lemma II.1.2 (c)). -/
noncomputable def deltaBar (A0 : ℝ) (p0 : ℕ) (x : ℝ) : ℝ :=
  Real.exp 1 * A0 * x ^ p0 * Real.exp (-x / 2)

theorem deltaRun_eq (A0 : ℝ) (p0 : ℕ) (a : ℝ) (b : ℕ → ℝ) (j : ℕ) (hb : 0 < b j * a) :
    deltaRun A0 p0 a b j = Real.exp (-runLam a b j / 2) * (A0 * runLam a b j ^ p0) := by
  unfold deltaRun pZero runLam
  rw [Real.rpow_def_of_pos hb]
  congr 2
  ring

namespace RunningHyp

variable {d L : ℕ} {β ν a ε : ℝ} {b n : ℕ → ℝ}

/-- Lemma II.1.2 (c): `δ_j ≤ δ̄(λ̂_j)`. -/
theorem deltaRun_le_bar (h : RunningHyp d L β ν a ε b n) {A0 : ℝ} (hA : 0 ≤ A0) (p0 : ℕ)
    (h3 : 3 ≤ lamHat d L β a 0) (j : ℕ) :
    deltaRun A0 p0 a b j ≤ deltaBar A0 p0 (lamHat d L β a j) := by
  have ha : 0 < a := by linarith [h.ha1]
  rw [deltaRun_eq A0 p0 a b j (mul_pos (h.betaRun_pos j) ha)]
  have h1 := h.one_le_runLam h3 j
  have h2 := h.runLam_le_hat j
  have h4 := h.hat_le_runLam_add_two j
  unfold deltaBar
  have e1 : Real.exp (-runLam a b j / 2) ≤ Real.exp 1 * Real.exp (-lamHat d L β a j / 2) := by
    rw [← Real.exp_add]; exact Real.exp_le_exp.2 (by linarith)
  have e2 : runLam a b j ^ p0 ≤ lamHat d L β a j ^ p0 := pow_le_pow_left₀ (by linarith) h2 p0
  have e3 : 0 ≤ A0 * runLam a b j ^ p0 := mul_nonneg hA (by positivity)
  calc Real.exp (-runLam a b j / 2) * (A0 * runLam a b j ^ p0)
      ≤ (Real.exp 1 * Real.exp (-lamHat d L β a j / 2)) * (A0 * lamHat d L β a j ^ p0) :=
        mul_le_mul e1 (mul_le_mul_of_nonneg_left e2 hA) e3 (by positivity)
    _ = _ := by ring

end RunningHyp

/-- `δ̄` is decreasing for `x ≥ 2 p₀` (Lemma II.1.2 (c)). -/
theorem deltaBar_antitoneOn {A0 : ℝ} (hA : 0 ≤ A0) {p0 : ℕ} (hp : 1 ≤ p0) :
    AntitoneOn (deltaBar A0 p0) (Set.Ici (2 * (p0 : ℝ))) := by
  intro x hx y hy hxy
  have hx' : (2 * (p0 : ℝ)) ≤ x := hx
  have hp0 : (0 : ℝ) < p0 := by exact_mod_cast hp
  have hxpos : 0 < x := by linarith
  have key : y ^ p0 * Real.exp (-y / 2) ≤ x ^ p0 * Real.exp (-x / 2) := by
    -- compare logarithms: `f t = p₀ log t - t/2` is antitone on `[2 p₀, ∞)`
    have hf : AntitoneOn (fun t : ℝ => (p0 : ℝ) * Real.log t - t / 2) (Set.Ici (2 * (p0 : ℝ))) := by
      refine antitoneOn_of_deriv_nonpos (convex_Ici _) ?_ ?_ ?_
      · exact (continuousOn_const.mul (Real.continuousOn_log.mono (fun t ht => by
          have : (2 * (p0 : ℝ)) ≤ t := ht
          exact ne_of_gt (by linarith)))).sub (continuousOn_id.div_const 2)
      · intro t ht
        have : 2 * (p0 : ℝ) < t := by simpa using ht
        have htne : t ≠ 0 := by intro h0; rw [h0] at this; linarith
        exact ((differentiableAt_const _).mul (Real.differentiableAt_log htne)).sub
          ((differentiableAt_id).div_const 2) |>.differentiableWithinAt
      · intro t ht
        have h2 : 2 * (p0 : ℝ) < t := by simpa using ht
        have htne : t ≠ 0 := by intro h0; rw [h0] at h2; linarith
        have hd : HasDerivAt (fun t : ℝ => (p0 : ℝ) * Real.log t - t / 2) ((p0 : ℝ) * t⁻¹ - 1 / 2) t := by
          have := ((Real.hasDerivAt_log htne).const_mul (p0 : ℝ)).sub ((hasDerivAt_id t).div_const 2)
          convert this using 1
          funext y; simp
        rw [hd.deriv]
        have htpos : 0 < t := by linarith
        have : (p0 : ℝ) * t⁻¹ ≤ 1 / 2 := by
          rw [← div_eq_mul_inv, div_le_iff₀ htpos]; linarith
        linarith
    have := hf hx hy hxy
    have hypos : 0 < y := by linarith
    have e : ∀ t : ℝ, 0 < t → t ^ p0 * Real.exp (-t / 2) =
        Real.exp ((p0 : ℝ) * Real.log t - t / 2) := by
      intro t ht
      rw [show (p0 : ℝ) * Real.log t - t / 2 = (p0 : ℝ) * Real.log t + (-t / 2) by ring,
        Real.exp_add, ← Real.log_pow, Real.exp_log (pow_pos ht _)]
    rw [e x hxpos, e y hypos]
    exact Real.exp_le_exp.2 this
  unfold deltaBar
  have := mul_le_mul_of_nonneg_left key (mul_nonneg (Real.exp_pos 1).le hA)
  nlinarith [this]

/-! ### F3: the analytic conditions (Λ15)-(Λ17) -/

/-- The fixed constants entering (Λ15)-(Λ17): `H₀`, `c₂`, `p₀`, `A₀`, `c₁^{BG}`, `c₁₁`, `C₃`, `C₄`,
`δ_{**}`, `δ_*`, `N`. -/
structure AnalyticConsts where
  d : ℕ
  L : ℕ
  N : ℕ
  p0 : ℕ
  A0 : ℝ
  H0 : ℝ
  c2 : ℝ
  c1BG : ℝ
  c11 : ℝ
  C3 : ℝ
  C4 : ℝ
  deltaSS : ℝ
  deltaS : ℝ

/-- `c_N = N v_N (3/2)^{N/2}`, `v_N` the volume of the unit ball of `ℝ^N`. -/
noncomputable def cN (N : ℕ) : ℝ :=
  (N : ℝ) * (MeasureTheory.volume (Metric.ball (0 : EuclideanSpace ℝ (Fin N)) 1)).toReal *
    (3 / 2 : ℝ) ^ ((N : ℝ) / 2)

/-- The conditions (Λ15), (Λ16), (Λ17), (Λ17′) at the real number `x`. -/
structure AnalyticLamAt (K : AnalyticConsts) (x : ℝ) : Prop where
  lam15 : 3 / (1 - (2 : ℝ) ^ (-(1 / (2 * (K.p0 : ℝ))))) ≤ x
  lam16a : 1 ≤ K.H0 * ((1 - ((K.L : ℝ) ^ K.d)⁻¹) * (x - 3) -
    ((K.L : ℝ) ^ K.d)⁻¹ * (thetaOf K.d K.L + 1))
  lam16b : K.c2 + 2 ≤ x
  lam17a : 3 * K.d * K.L * deltaBar K.A0 K.p0 x ≤ min K.c1BG K.c11 / K.C4
  lam17b : deltaBar K.A0 K.p0 x ≤ min K.deltaSS K.deltaS / (K.C3 * K.C4)
  lam17c : 3 * K.d * K.L * cN K.N * deltaBar K.A0 K.p0 x ≤ 1 / 2

/-- (Λ15)-(Λ17′) hold for all real `x ≥ λ*^{II}`. -/
def AnalyticLamConditions (K : AnalyticConsts) (lamStarII : ℝ) : Prop :=
  ∀ x : ℝ, lamStarII ≤ x → AnalyticLamAt K x

theorem AnalyticLamConditions.at {K : AnalyticConsts} {l : ℝ} (h : AnalyticLamConditions K l)
    {x : ℝ} (hx : l ≤ x) : AnalyticLamAt K x := h x hx

/-! ### Bridge to the landed flow -/

section Bridge

open Balaban.Flow

/-- The hypotheses (I.2) hold for a real flow: if `ξ` satisfies the standing hypotheses of
`norm_gammaSeq_le` (with `c₈ q/(1-q) ≤ ε`) and the complex sequences `betaSeq`, `nuSeq` are real
(`= betaRun k`, `nuRun k`) with positive values, then `|log γ_k|, |log δ_k| ≤ ε`. -/
theorem RunningHyp.of_flow {d L : ℕ} {β ν a ε : ℝ} {betaRun nuRun : ℕ → ℝ}
    {ξ : ℕ → Fin 3 → ℂ} {q c₈ : ℝ}
    (hd : 2 ≤ d) (hL : 2 ≤ L) (hβ : 0 < β) (hν : 0 < ν) (ha1 : 1 < a) (ha2 : a < 3 / 2)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 20)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hc : 0 ≤ c₈) (hs : c₈ * q ≤ 1 - q)
    (hξ : ∀ k, ‖ξ k‖ ≤ c₈ / 4 * q ^ (k + 1)) (hεq : c₈ * (q / (1 - q)) ≤ ε)
    (hb : ∀ k, betaSeq (L : ℝ) d ξ (β : ℂ) k = (betaRun k : ℂ))
    (hn : ∀ k, nuSeq (L : ℝ) ξ (ν : ℂ) k = (nuRun k : ℂ))
    (hbpos : ∀ k, 0 < betaRun k) (hnpos : ∀ k, 0 < nuRun k) :
    RunningHyp d L β ν a ε betaRun nuRun := by
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have hS : ∀ k, c₈ * ratePartialSum q k ≤ ε := fun k =>
    (mul_le_mul_of_nonneg_left (ratePartialSum_le hq0 hq1 k) hc).trans hεq
  refine ⟨hd, hL, hβ, hν, ha1, ha2, hε0, hε, ?_, ?_⟩
  · intro k
    have h1 := betaSeq_eq (L : ℝ) d ξ (β : ℂ) k
    rw [hb k] at h1
    push_cast at h1
    have hP : (0 : ℝ) < β * (L : ℝ) ^ (k * (d - 2)) := by positivity
    set γ : ℝ := betaRun k / (β * (L : ℝ) ^ (k * (d - 2))) with hγdef
    have hγpos : 0 < γ := div_pos (hbpos k) hP
    have hγc : gammaSeq ξ k = (γ : ℂ) := by
      have hPc : ((β : ℂ) * (L : ℂ) ^ (k * (d - 2))) ≠ 0 := by
        have : ((β * (L : ℝ) ^ (k * (d - 2)) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hP.ne'
        simpa using this
      have : (betaRun k : ℂ) = ((β : ℂ) * (L : ℂ) ^ (k * (d - 2))) * gammaSeq ξ k := by
        rw [h1]
      rw [hγdef]; push_cast
      rw [this, mul_div_cancel_left₀ _ hPc]
    obtain ⟨b1, b2, -, -⟩ := norm_gammaSeq_le hq0 hq1 hc hs hξ k
    rw [hγc, Complex.norm_real, Real.norm_of_nonneg hγpos.le] at b1
    rw [hγc, ← Complex.ofReal_inv, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.2 hγpos.le)] at b2
    refine ⟨γ, hγpos, ?_, by rw [hγdef]; field_simp⟩
    rw [abs_le]
    constructor
    · have : γ⁻¹ ≤ Real.exp ε := b2.trans (Real.exp_le_exp.2 (hS k))
      have := Real.log_le_log (inv_pos.2 hγpos) this
      rw [Real.log_inv, Real.log_exp] at this; linarith
    · have : γ ≤ Real.exp ε := b1.trans (Real.exp_le_exp.2 (hS k))
      have := Real.log_le_log hγpos this
      rwa [Real.log_exp] at this
  · intro k
    have h1 := nuSeq_eq (L : ℝ) ξ (ν : ℂ) k
    rw [hn k] at h1
    push_cast at h1
    have hP : (0 : ℝ) < ν * (L : ℝ) ^ (2 * k) := by positivity
    set δ : ℝ := nuRun k / (ν * (L : ℝ) ^ (2 * k)) with hδdef
    have hδpos : 0 < δ := div_pos (hnpos k) hP
    have hδc : deltaSeq ξ k = (δ : ℂ) := by
      have hPc : ((ν : ℂ) * (L : ℂ) ^ (2 * k)) ≠ 0 := by
        have : ((ν * (L : ℝ) ^ (2 * k) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hP.ne'
        simpa using this
      have : (nuRun k : ℂ) = ((ν : ℂ) * (L : ℂ) ^ (2 * k)) * deltaSeq ξ k := by
        rw [h1]
      rw [hδdef]; push_cast
      rw [this, mul_div_cancel_left₀ _ hPc]
    obtain ⟨-, -, b1, b2⟩ := norm_gammaSeq_le hq0 hq1 hc hs hξ k
    rw [hδc, Complex.norm_real, Real.norm_of_nonneg hδpos.le] at b1
    rw [hδc, ← Complex.ofReal_inv, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.2 hδpos.le)] at b2
    refine ⟨δ, hδpos, ?_, by rw [hδdef]; field_simp⟩
    rw [abs_le]
    constructor
    · have : δ⁻¹ ≤ Real.exp ε := b2.trans (Real.exp_le_exp.2 (hS k))
      have := Real.log_le_log (inv_pos.2 hδpos) this
      rw [Real.log_inv, Real.log_exp] at this; linarith
    · have : δ ≤ Real.exp ε := b1.trans (Real.exp_le_exp.2 (hS k))
      have := Real.log_le_log hδpos this
      rwa [Real.log_exp] at this

end Bridge

end Balaban.LargeField
