/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.Def6
public import Balaban.LargeField.Analytic.Constants
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Def-6 v2, part 1: the regime record (CLASS-RULINGS-2 items 1, 2) -- DRAFT

**Draft, pending Roland's answer to Q13** (`notes/QUESTIONS-ROLAND-2.md` item 13;
`notes/phase1/Q13-ANSWER-astra.md`).  Second version of the inductive classes, implementing
`notes/phase1/CLASS-RULINGS-2.md`; the landed classes `Def6.IsSF`, `Def6.IsSFFamily` are unchanged.

CLASS-RULINGS-2 "Ruling": one **physical** mass sequence `ν_j` in the action and in the source
`b_j = ν_j h`, and a separate **background** mass `μ_k`, fixed from the a priori index `k₀` before the
step.

* `physMass L k ν_k = ν_k L^{-2k}`: the physical mass in fine units (item 1: the mass argument of
  the fine-unit `action`);
* `bgMassAt L k₀ k ν_k`: `0` for `k ≤ k₀`, `ν_k L^{-2k}` for `k > k₀` (item 2), the mass of the
  background solutions, compositions and characteristic sets;
* `betaFine d L k β_k = β_k L^{-k(d-2)}`: the fine-unit coefficient of the action (item 1;
  LF-RECONSTRUCTION Definition II.5.4, `β^{(k)}_0`);
* `Regime L`: the regime record (the a priori `kZero` and the physical masses), with
  `Regime.physMass`, `Regime.bgMass`; `Regime.aPriori`: the regime of LF-RECONSTRUCTION D-IV.11,
  `k₀ = max {k : β ν L^{kd} ≤ 1}` (`LargeField.kZero`); `Regime.IsFlow`: the regime of a flow.

The flow facts (LF-RECONSTRUCTION Lemma IV.3.3 (a), from (I.2) = `LargeField.RunningHyp`):
`RunningHyp.beta_mul_nu_le` (`β_j ν_j ≤ e^{2ε}` for `j ≤ k₀`, genuine `k₀`),
`RunningHyp.beta_mul_nu_succ_le` (`β_{k₀+1} ν_{k₀+1} ≤ e^{2ε} L^d`),
`RunningHyp.lt_beta_mul_nu` (`β_j ν_j > e^{-2ε}` for `j > k₀`).  As ruled in item 2, `β_k ν_k ≤ 1`
is **not** claimed.
-/

@[expose] public section

namespace Balaban.SmallField.Def6v2

open Balaban Balaban.SmallField.Def6 Balaban.LargeField

/-! ### Masses and the fine-unit coefficient -/

/-- **The physical mass in fine units**, `ν_k L^{-2k}` (CLASS-RULINGS-2 item 1): the mass argument
of the fine-unit `action` and the coefficient of the field term, at every scale, whatever the
background convention (P5 p. 490: "we keep it in the main action").  Draft pending Q13. -/
noncomputable def physMass (L k : ℕ) (νk : ℝ) : ℝ := νk * ((L : ℝ) ^ k)⁻¹ ^ 2

/-- **The background mass** `bgMassAt(k₀, k, ν_k)` (CLASS-RULINGS-2 item 2): `0` for `k ≤ k₀` and
`ν_k L^{-2k}` for `k > k₀`, a function of the **fixed regime input** `k₀` (the a priori index of
LF-RECONSTRUCTION D-IV.11), not of the running product `β_k ν_k`.  It is used only in the background
solutions, compositions and characteristic sets.  Draft pending Q13. -/
noncomputable def bgMassAt (L k₀ k : ℕ) (νk : ℝ) : ℝ := if k ≤ k₀ then 0 else physMass L k νk

/-- **The fine-unit coefficient of the action**, `β_k L^{-k(d-2)}` (CLASS-RULINGS-2 item 1; P4
p. 676 (1.1), (H.1) writes `-β_k A_k` in scale-`k` units, LF-RECONSTRUCTION Definition II.5.4
identifies the fine-unit coefficient `β^{(k)}_0`).  Draft pending Q13. -/
noncomputable def betaFine (d L k : ℕ) (βk : ℝ) : ℝ := βk / (L : ℝ) ^ (k * (d - 2))

theorem betaFine_eq_betaCanon (d L k : ℕ) (βk : ℝ) : betaFine d L k βk = betaCanon d L βk k 0 := by
  simp [betaFine, betaCanon]

theorem bgMassAt_of_le {L k₀ k : ℕ} (h : k ≤ k₀) (νk : ℝ) : bgMassAt L k₀ k νk = 0 := by
  simp [bgMassAt, h]

theorem bgMassAt_of_lt {L k₀ k : ℕ} (h : k₀ < k) (νk : ℝ) :
    bgMassAt L k₀ k νk = physMass L k νk := by
  simp [bgMassAt, Nat.not_le.2 h]

theorem physMass_nonneg (L k : ℕ) {νk : ℝ} (h : 0 ≤ νk) : 0 ≤ physMass L k νk := by
  unfold physMass; positivity

theorem physMass_pos {L : ℕ} [NeZero L] (k : ℕ) {νk : ℝ} (h : 0 < νk) : 0 < physMass L k νk := by
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  unfold physMass; positivity

theorem bgMassAt_nonneg (L k₀ k : ℕ) {νk : ℝ} (h : 0 ≤ νk) : 0 ≤ bgMassAt L k₀ k νk := by
  unfold bgMassAt; split_ifs
  · exact le_rfl
  · exact physMass_nonneg L k h

/-- The background mass never exceeds the physical mass. -/
theorem bgMassAt_le_physMass (L k₀ k : ℕ) {νk : ℝ} (h : 0 ≤ νk) :
    bgMassAt L k₀ k νk ≤ physMass L k νk := by
  unfold bgMassAt; split_ifs
  · exact physMass_nonneg L k h
  · exact le_rfl

/-- `ν_k L^{-2k} · L^{2k} = ν_k`. -/
theorem physMass_mul_sq {L : ℕ} [NeZero L] (k : ℕ) (νk : ℝ) :
    physMass L k νk * ((L : ℝ) ^ k) ^ 2 = νk := by
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  unfold physMass; field_simp

/-- The physical fine mass is the same at every level of the ideal flow matched at `k`:
`ν_j L^{-2j} = ν_k L^{-2k}` for `ν_j = ν_k L^{-2(k-j)}` (`nuIdeal`), `j ≤ k`. -/
theorem physMass_nuIdeal {L : ℕ} [NeZero L] {j k : ℕ} (hjk : j ≤ k) (νk : ℝ) :
    physMass L j (nuIdeal L k νk j) = physMass L k νk := by
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hjk
  unfold physMass nuIdeal
  rw [Nat.add_sub_cancel_left, pow_add]
  field_simp

/-- `bgMassAt` is the landed fine-unit background mass of LF-RECONSTRUCTION Definition II.1.1
(`LargeField.bgMass`, used by Def-7's `FieldClauses.mu_eq`). -/
theorem bgMassAt_eq_lfBgMass (L k₀ : ℕ) (ν : ℕ → ℝ) (k : ℕ) :
    bgMassAt L k₀ k (ν k) = LargeField.bgMass k₀ L ν k := by
  unfold bgMassAt LargeField.bgMass physMass
  split_ifs
  · rfl
  · rw [pow_mul, div_eq_mul_inv, inv_pow, ← pow_mul, ← pow_mul, mul_comm k 2]

/-- **Agreement with the running-test mass of the landed class** (`Def6.bgMass`, P5 (1.9)): the two
masses coincide exactly when the a priori test `k ≤ k₀` and the running test `β_k ν_k ≤ 1` agree at
`k`.  (CLASS-RULINGS-2 item 2: the two indices differ by at most one, and the criteria cannot be
interchanged inside an induction.) -/
theorem bgMassAt_eq_bgMass {L k₀ k : ℕ} {βk νk : ℝ} (h : k ≤ k₀ ↔ βk * νk ≤ 1) :
    bgMassAt L k₀ k νk = Def6.bgMass L k βk νk := by
  unfold bgMassAt Def6.bgMass physMass
  by_cases hk : k ≤ k₀
  · simp [hk, h.1 hk]
  · have h1 : ¬ βk * νk ≤ 1 := fun h' => hk (h.2 h')
    simp [hk, h1]

/-! ### The regime record -/

/-- **The regime record** (CLASS-RULINGS-2 "Lean-ready class interface"): the a priori switch
index `kZero` (LF-RECONSTRUCTION D-IV.11) and the running physical masses `ν_j` (dimensionless, in
the units of scale `j`).  The same record is passed to Def-6 v2, the observable layer v2 and Def-7
v2 (item 2: "pass the same `k₀` to Def-6, IsObs, Def-7, characteristic domains, and the LF
history").  Draft pending Roland's answer to Q13. -/
structure Regime (L : ℕ) where
  /-- the a priori switch index `k₀` -/
  kZero : ℕ
  /-- the running physical masses `ν_j` -/
  ν : ℕ → ℝ

namespace Regime

variable {L : ℕ} (Rg : Regime L)

/-- The physical fine mass `ν_k L^{-2k}` of the regime (item 1). -/
noncomputable def physMass (k : ℕ) : ℝ := Def6v2.physMass L k (Rg.ν k)

/-- The background mass `μ_k = bgMassAt(k₀, k, ν_k)` of the regime (item 2). -/
noncomputable def bgMass (k : ℕ) : ℝ := bgMassAt L Rg.kZero k (Rg.ν k)

theorem bgMass_of_le {k : ℕ} (h : k ≤ Rg.kZero) : Rg.bgMass k = 0 := bgMassAt_of_le h _

theorem bgMass_of_lt {k : ℕ} (h : Rg.kZero < k) : Rg.bgMass k = Rg.physMass k :=
  bgMassAt_of_lt h _

theorem bgMass_nonneg {k : ℕ} (h : 0 ≤ Rg.ν k) : 0 ≤ Rg.bgMass k := bgMassAt_nonneg _ _ _ h

theorem bgMass_le_physMass {k : ℕ} (h : 0 ≤ Rg.ν k) : Rg.bgMass k ≤ Rg.physMass k :=
  bgMassAt_le_physMass _ _ _ h

/-- Below the switch the physical mass term is still present (item 1: "at `μ_k = 0` the physical
mass term is still present"): the two masses differ as soon as `ν_k > 0`. -/
theorem bgMass_lt_physMass [NeZero L] {k : ℕ} (hk : k ≤ Rg.kZero) (h : 0 < Rg.ν k) :
    Rg.bgMass k < Rg.physMass k := by
  rw [Rg.bgMass_of_le hk]; exact physMass_pos k h

/-- **The a priori regime** of LF-RECONSTRUCTION D-IV.11: `k₀ = max {k : β ν L^{kd} ≤ 1}`
(`LargeField.kZero`; `0` by convention if `β ν > 1`), a function of the initial couplings `(β, ν)`
fixed before the flow, with the running masses `νrun`. -/
noncomputable def aPriori (d L : ℕ) (β ν : ℝ) (νrun : ℕ → ℝ) : Regime L :=
  ⟨LargeField.kZero d L β ν, νrun⟩

/-- **The regime of a flow** (D-IV.11 with (I.2)): the switch index is the a priori index of the
initial couplings `(β, ν)`, and the running coefficients `β_k = βrun k`, `ν_k = Rg.ν k` satisfy
(I.2) (`LargeField.RunningHyp`: `β_k = β L^{k(d-2)} γ_k`, `ν_k = ν L^{2k} δ_k`,
`|log γ_k|, |log δ_k| ≤ ε`), the form in which the flow gives them (FLUCTUATION Theorem 5.3). -/
structure IsFlow (d : ℕ) (β ν a ε : ℝ) (βrun : ℕ → ℝ) : Prop where
  kZero_eq : Rg.kZero = LargeField.kZero d L β ν
  running : RunningHyp d L β ν a ε βrun Rg.ν

end Regime

/-- For a conventional `k₀ = 0` (`β ν > 1`) the flow starts in the complete regime (item 2): the
background mass is the physical mass at every scale `k ≥ 1`. -/
theorem bgMass_aPriori_of_not_genuine {d L : ℕ} {β ν : ℝ} (hL : 2 ≤ L) (hg : ¬ KZeroGenuine β ν)
    (νrun : ℕ → ℝ) {k : ℕ} (hk : 1 ≤ k) :
    (Regime.aPriori d L β ν νrun).bgMass k = (Regime.aPriori d L β ν νrun).physMass k := by
  refine Regime.bgMass_of_lt _ ?_
  show kZero d L β ν < k
  rw [kZero_of_not_genuine hL hg]; exact hk

/-! ### The flow facts at the switch (LF-RECONSTRUCTION Lemma IV.3.3 (a)) -/

section Flow

variable {d L : ℕ} {β ν a ε : ℝ} {b n : ℕ → ℝ}

theorem le_exp_of_abs_log {x ε : ℝ} (hx : 0 < x) (h : |Real.log x| ≤ ε) : x ≤ Real.exp ε :=
  calc x = Real.exp (Real.log x) := (Real.exp_log hx).symm
    _ ≤ Real.exp ε := Real.exp_le_exp.2 (abs_le.1 h).2

theorem exp_neg_le_of_abs_log {x ε : ℝ} (hx : 0 < x) (h : |Real.log x| ≤ ε) :
    Real.exp (-ε) ≤ x :=
  calc Real.exp (-ε) ≤ Real.exp (Real.log x) := Real.exp_le_exp.2 (abs_le.1 h).1
    _ = x := Real.exp_log hx

end Flow

end Balaban.SmallField.Def6v2

namespace Balaban.LargeField.RunningHyp

open Balaban.SmallField.Def6v2

variable {d L : ℕ} {β ν a ε : ℝ} {b n : ℕ → ℝ}

/-- (I.2): `β_k ν_k = β ν L^{kd} γ_k δ_k` with `|log γ_k|, |log δ_k| ≤ ε`. -/
theorem beta_mul_nu_eq (h : RunningHyp d L β ν a ε b n) (k : ℕ) :
    ∃ γ δ : ℝ, 0 < γ ∧ 0 < δ ∧ |Real.log γ| ≤ ε ∧ |Real.log δ| ≤ ε ∧
      b k * n k = β * ν * (L : ℝ) ^ (k * d) * (γ * δ) := by
  obtain ⟨γ, hγ, hlγ, hb⟩ := h.beta_eq k
  obtain ⟨δ, hδ, hlδ, hn⟩ := h.nu_eq k
  refine ⟨γ, δ, hγ, hδ, hlγ, hlδ, ?_⟩
  have hd : k * d = k * (d - 2) + 2 * k := by
    have h2 : d - 2 + 2 = d := Nat.sub_add_cancel h.hd
    calc k * d = k * (d - 2 + 2) := by rw [h2]
      _ = k * (d - 2) + 2 * k := by ring
  rw [hb, hn, hd, pow_add]; ring

theorem gamma_mul_delta_le {γ δ : ℝ} (hγ : 0 < γ) (hδ : 0 < δ) (hlγ : |Real.log γ| ≤ ε)
    (hlδ : |Real.log δ| ≤ ε) : γ * δ ≤ Real.exp (2 * ε) := by
  rw [two_mul, Real.exp_add]
  exact mul_le_mul (le_exp_of_abs_log hγ hlγ) (le_exp_of_abs_log hδ hlδ) hδ.le
    (Real.exp_pos _).le

/-- **`β_j ν_j ≤ e^{2ε}` for `j ≤ k₀`** (LF-RECONSTRUCTION Lemma IV.3.3 (a); CLASS-RULINGS-2
item 2), for a genuine a priori index (`β ν ≤ 1`).  This is what the flow gives; `β_j ν_j ≤ 1` is
not claimed, and the estimates at `k ≤ k₀` must allow `e^{2ε}` in place of `1`. -/
theorem beta_mul_nu_le (h : RunningHyp d L β ν a ε b n) (hg : KZeroGenuine β ν) {j : ℕ}
    (hj : j ≤ kZero d L β ν) : b j * n j ≤ Real.exp (2 * ε) := by
  obtain ⟨γ, δ, hγ, hδ, hlγ, hlδ, he⟩ := h.beta_mul_nu_eq j
  have hβν : 0 < β * ν := mul_pos h.hβ h.hν
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by have := h.hL; omega : 1 ≤ L)
  have h1 : β * ν * (L : ℝ) ^ (j * d) ≤ 1 :=
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL1 (Nat.mul_le_mul_right d hj)) hβν.le).trans
      (kZero_spec (by have := h.hd; omega) h.hL hβν hg)
  rw [he]
  calc β * ν * (L : ℝ) ^ (j * d) * (γ * δ) ≤ 1 * Real.exp (2 * ε) :=
        mul_le_mul h1 (gamma_mul_delta_le hγ hδ hlγ hlδ) (mul_pos hγ hδ).le zero_le_one
    _ = _ := one_mul _

/-- **`β_{k₀+1} ν_{k₀+1} ≤ e^{2ε} L^d`** at a genuine crossing (LF-RECONSTRUCTION lines 4164,
4656 ff.; CLASS-RULINGS-2 items 2, 5). -/
theorem beta_mul_nu_succ_le (h : RunningHyp d L β ν a ε b n) (hg : KZeroGenuine β ν) :
    b (kZero d L β ν + 1) * n (kZero d L β ν + 1) ≤ Real.exp (2 * ε) * (L : ℝ) ^ d := by
  obtain ⟨γ, δ, hγ, hδ, hlγ, hlδ, he⟩ := h.beta_mul_nu_eq (kZero d L β ν + 1)
  have hβν : 0 < β * ν := mul_pos h.hβ h.hν
  have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg L
  have h1 : β * ν * (L : ℝ) ^ ((kZero d L β ν + 1) * d) ≤ (L : ℝ) ^ d := by
    rw [Nat.add_mul, one_mul, pow_add, ← mul_assoc]
    exact mul_le_of_le_one_left (pow_nonneg hL0 d)
      (kZero_spec (by have := h.hd; omega) h.hL hβν hg)
  rw [he]
  calc β * ν * (L : ℝ) ^ ((kZero d L β ν + 1) * d) * (γ * δ)
      ≤ (L : ℝ) ^ d * Real.exp (2 * ε) :=
        mul_le_mul h1 (gamma_mul_delta_le hγ hδ hlγ hlδ) (mul_pos hγ hδ).le (pow_nonneg hL0 d)
    _ = _ := mul_comm _ _

/-- **`β_j ν_j > e^{-2ε}` for `j > k₀`** (LF-RECONSTRUCTION Lemma IV.3.3 (a)). -/
theorem lt_beta_mul_nu (h : RunningHyp d L β ν a ε b n) {j : ℕ} (hj : kZero d L β ν < j) :
    Real.exp (-(2 * ε)) < b j * n j := by
  obtain ⟨γ, δ, hγ, hδ, hlγ, hlδ, he⟩ := h.beta_mul_nu_eq j
  have hβν : 0 < β * ν := mul_pos h.hβ h.hν
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by have := h.hL; omega : 1 ≤ L)
  have h1 : 1 < β * ν * (L : ℝ) ^ (j * d) :=
    (lt_kZero_succ (by have := h.hd; omega) h.hL hβν).trans_le
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL1 (Nat.mul_le_mul_right d hj)) hβν.le)
  have h2 : Real.exp (-(2 * ε)) ≤ γ * δ := by
    rw [show -(2 * ε) = -ε + -ε by ring, Real.exp_add]
    exact mul_le_mul (exp_neg_le_of_abs_log hγ hlγ) (exp_neg_le_of_abs_log hδ hlδ)
      (Real.exp_pos _).le hγ.le
  rw [he]
  calc Real.exp (-(2 * ε)) ≤ γ * δ := h2
    _ = 1 * (γ * δ) := (one_mul _).symm
    _ < β * ν * (L : ℝ) ^ (j * d) * (γ * δ) := mul_lt_mul_of_pos_right h1 (mul_pos hγ hδ)

end Balaban.LargeField.RunningHyp

namespace Balaban.SmallField.Def6v2

open Balaban Balaban.LargeField

/-- The flow facts for the regime of a flow: `β_j ν_j ≤ e^{2ε}` at the scales `j ≤ k₀` with zero
background mass. -/
theorem Regime.IsFlow.beta_mul_nu_le {L d : ℕ} {Rg : Regime L} {β ν a ε : ℝ} {βrun : ℕ → ℝ}
    (h : Rg.IsFlow d β ν a ε βrun) (hg : KZeroGenuine β ν) {j : ℕ} (hj : j ≤ Rg.kZero) :
    βrun j * Rg.ν j ≤ Real.exp (2 * ε) :=
  h.running.beta_mul_nu_le hg (h.kZero_eq ▸ hj)

/-- **The regime of a flow is inhabited at a genuine crossing with positive masses**
(`d = L = 3`, `β = 3`, `ν = 1/81`, the free flow `β_k = β 3^k`, `ν_k = ν 9^k`): `β ν L^d = 1`, so
`k₀ ≥ 1` is genuine and the background mass vanishes at scale `1` while the physical mass does
not. -/
theorem regime_isFlow_witness :
    ∃ Rg : Regime 3, Rg.IsFlow 3 3 (1 / 81) (5 / 4) 0 (fun k => 3 * 3 ^ (k * (3 - 2))) ∧
      KZeroGenuine (3 : ℝ) (1 / 81) ∧ 1 ≤ Rg.kZero ∧ Rg.bgMass 1 = 0 ∧ 0 < Rg.physMass 1 := by
  have hk : 1 ≤ kZero 3 3 (3 : ℝ) (1 / 81) := by
    refine le_csSup (kZero_bddAbove (by norm_num) (by norm_num) (by norm_num)) ?_
    show (3 : ℝ) * (1 / 81) * ((3 : ℕ) : ℝ) ^ (1 * 3) ≤ 1
    norm_num
  refine ⟨Regime.aPriori 3 3 3 (1 / 81) (fun k => 1 / 81 * 3 ^ (2 * k)), ⟨rfl, ?_⟩, ?_, hk,
    Regime.bgMass_of_le _ hk, ?_⟩
  · refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, le_rfl,
      by norm_num, fun k => ⟨1, one_pos, by simp, by simp⟩, fun k => ⟨1, one_pos, by simp, ?_⟩⟩
    simp [Regime.aPriori]
  · show (3 : ℝ) * (1 / 81) ≤ 1
    norm_num
  · have : (0 : ℝ) < 1 / 81 * 3 ^ (2 * 1) := by norm_num
    exact physMass_pos (L := 3) 1 this

end Balaban.SmallField.Def6v2
