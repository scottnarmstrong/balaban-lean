/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.Witness
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

/-!
# The class step of the spine from three sub-inputs

`classStepInput_of_parts` proves the spine input `ClassStepInput` (A4, `Spine/RootFInputs.lean`)
from three named sub-inputs, following LFR Theorem IV.3.2 (the flow): for `1 ≤ k < k₀` the step
`ℛ_k → ℛ_{k+1}` is LF-3 (Theorem IV.1.1, one full step `T`, `S` with the decompositions of P5 §2 and
the small-field analysis of P4–P6) followed by LF-4 (Theorem III.10.8, the operation `R` of P7 at
the scale `k + 1`), and the running constants at `k + 1` satisfy (I.2) by LF-7 (d).

* `SFStepInput` (LF-3; LFR Theorem IV.1.1 (a)–(e), (h); P5 Theorem 1, P6 Theorem 1, with P4
  Theorem 1 for the small-field data): a member of `ℛ_k` has a successor in the pre-`R` class
  `ℛ^pre_{k+1}` (`IsRepPre2`), torus coherent (`LFCoherent`), whose running constants satisfy (I.2)
  at the scales `≤ k` and start from the bare couplings, with `∫ ρ' = c ∫ ρ`. The flow relation
  (H.6) of the new coefficients `β_{k+1}, ν_{k+1}` (P4 (5.28), `|ξ^{(k)}| ≤ (c₈/4) q^{k+1}`) is the
  clause `CoeffBounds` of `IsSFFamily2` at `k + 1`, part of the output.
* `RInput` (LF-4; LFR Theorem III.10.8, P7 Theorem 2, ruling R4): for `1 ≤ k ≤ k₀`, a torus
  coherent member of `ℛ^pre_k` with (I.2) up to `k` has an image in `ℛ_k` with the same running mass
  and the same integral (`∫ R ρ = ∫ ρ`, P7 (1.7), LFR Lemma III.8.4).
* `FlowRateInput` (the coefficient step; LFR Theorem IV.3.2 (d), prefix row 10): the constant
  condition `c₈ q/(1 - q) ≤ 1/20`, `q = L^{-2γ}`. With it (H.6) at `k + 1` gives (I.2) at `k + 1`
  (`runningHypTo_succ_of_coeffBounds`, proved here from the landed `Flow.norm_gammaSeq_le`).

The assembly `∫ ρ'' = c ∫ ρ` is proved (`IntegralStep.trans_eq`).

**Torus coherence is not a separate sub-input.** The large-field half of (D8) at `k + 1`
(`LFCoherent`, LFR D-IV.9) is a property of the representation that the step constructs: LFR
Theorem IV.1.1 (h) and the proof of Theorem III.10.8 derive it from (D8) at `k` and from the
locality of the constructions. No landed operator states which representation the step produces,
so a statement "(D8) at `k + 1` follows from (D8) at `k`" quantified over all representations of
`ℛ^pre_{k+1}` would be false (a family of densities on different tori need not be coherent). The
coherence is therefore a conjunct of the outputs of `SFStepInput` and `RInput`, with (D8) at the
input scale in their hypotheses.

`PreClassAt` is the pre-`R` class at the constants of the prefix, as `RepClassAt` with `IsRepPre2`
in place of `IsRep2` and with (I.2) asked up to a scale `r` (`r = k` for `RInput`, `r = k - 1` for
the output of `SFStepInput`). These sub-inputs are spine-local: they are used as hypotheses only by
`classStepInput_of_parts` and by the theorems that will discharge them. Inhabitation (rule 10):
`preClassAt_witness` (the landed witness of `IsRepPre2`), `flowRateInput_of_lower` (any admissible
constants after lowering `c₈`). The list and the status of each sub-input are in
`notes/phase1/SPINE.md`, section "ClassStepInput sub-inputs". -/

@[expose] public section

namespace Balaban.RootFSpine

open MeasureTheory Balaban Balaban.LargeField Balaban.LargeField.Def7 Balaban.LargeField.Def7v2
  Balaban.SmallField Balaban.SmallField.Def6v2

/-!
### The pre-`R` class at the constants of the prefix
-/

/-- **The pre-`R` class `ℛ^pre_k` at the constants of the prefix** (LFR §II.6.3, first item,
second version `IsRepPre2`: the class of the output of one step before the operation `R`), with the
conventions of `RepClassAt`: `ρ` has a representation `F` on the tori of the horizon `K = kf + 1`
for the a priori setting, the a priori regime index `kZero d L β ν` and the outer constants of the
prefix; its running small-field coefficients start from the bare couplings (`β_0 = β`, `ν_0 = ν`)
and satisfy (I.2) up to the scale `r` (`RunningHypTo`, `ε = 1/20`); its large-field data are torus
coherent (`LFCoherent`); `νk` is its running mass `ν_k` at the scale `k`. -/
def PreClassAt (d N : ℕ) (T : Typing) (P6 : Def6.Consts) (C7 : Consts7) (PB : BudgetConsts)
    (cs₀ : OpConsts) (M1 c : ℕ) (rH ϱ : ℝ) (β ν : ℝ) (h : EuclideanSpace ℝ (Fin N))
    (kf k r : ℕ) [NeZero T.M] [NeZero T.L] (ρ : 𝒟[d, N, T, β, cs₀.aKer, kf + 1, k]) (νk : ℝ) :
    Prop :=
  ∃ (hM6 : T.M = T.L ^ (P6.m₀ + C7.m₁)) (hkK : k ≤ kf + 1) (R : ℕ → ℝ)
    (geo : ∀ (nK : ℕ) [NeZero nK], Geo 𝒮[d, T, β, cs₀.aKer] (sides T.L (kf + 1) nK) R T.M)
    (cs : OpConsts) (P : BudgetConsts)
    (F : RepFam 𝒮[d, T, β, cs₀.aKer] R (kZero d T.L β ν) (kf + 1) T.M N geo cs P k C7.m₁ ϱ)
    (St : ∀ (N₁ : ℕ) [NeZero N₁], SourceTerms d T.L N₁ C7.m₁ k N) (vc : CorrCoef d),
    (∀ (nK : ℕ) [NeZero nK], (geo nK).M1 = M1 ∧ (geo nK).c = c) ∧
    cs.aKer = cs₀.aKer ∧ cs.Cpsi = cs₀.Cpsi ∧ cs.Cb = cs₀.Cb ∧ cs.aw = cs₀.aw ∧
    P.c1 = PB.c1 ∧ P.c2 = PB.c2 ∧ P.H0 = PB.H0 ∧
    IsRepPre2 𝒮[d, T, β, cs₀.aKer] R (kZero d T.L β ν) (kf + 1) T.M N geo cs P P6 C7 β ν h rH k
      hM6 hkK F ρ St vc ∧
    F.sf.β 0 = β ∧ F.sf.ν 0 = ν ∧ F.sf.ν k = νk ∧
    RunningHypTo d T.L β ν cs₀.aKer (1 / 20) F.sf.β F.sf.ν r ∧ LFCoherent F

/-!
### The coefficient step: (H.6) at `k + 1` gives (I.2) at `k + 1`
-/

/-- A positive real `x` whose complex image `z` has `‖z‖ ≤ e^ε` and `‖z⁻¹‖ ≤ e^ε` satisfies
`|log x| ≤ ε`. -/
theorem abs_log_le_of_ofReal_eq {x ε : ℝ} {z : ℂ} (hz : (x : ℂ) = z) (hx : 0 < x)
    (h1 : ‖z‖ ≤ Real.exp ε) (h2 : ‖z⁻¹‖ ≤ Real.exp ε) : |Real.log x| ≤ ε := by
  subst hz
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx] at h1
  rw [← Complex.ofReal_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (inv_pos.2 hx)] at h2
  rw [abs_le]
  refine ⟨?_, ?_⟩
  · have := Real.log_le_log (inv_pos.2 hx) h2
    rw [Real.log_exp, Real.log_inv] at this
    linarith
  · have := Real.log_le_log hx h1
    rwa [Real.log_exp] at this

/-- **The coefficient step** (LFR Theorem IV.3.2 (d): (H.6) with `|ξ^{(j)}| ≤ (c₈/4) q^{j+1}` gives
(I.2) with `ε ≥ c₈ q/(1 - q)`; P4 (5.28), (5.32)). If the running coefficients satisfy (I.2) up to
the scale `k`, start from the bare couplings (`β_0 = β`, `ν_0 = ν`) and satisfy the coefficient
bounds (H.6) of Def-6 at the scale `k + 1` with `c₈ q ≤ ε (1 - q)`, `q = L^{-2γ}`, then they satisfy
(I.2) up to the scale `k + 1`. The new factors are `γ_{k+1} = γ_k (1 + ξ₃^{(k)})⁻¹` and
`δ_{k+1} = ν_{k+1}/(ν L^{2(k+1)})`; their positivity comes from `|ξ^{(k)}| ≤ 1/4` and `ν_{k+1} > 0`,
and their bounds from `Flow.norm_gammaSeq_le`. -/
theorem runningHypTo_succ_of_coeffBounds {d L : ℕ} {β ν a ε : ℝ} {P : Def6.Consts}
    {βs νs as : ℕ → ℝ} {k : ℕ} (hP : P.Admissible d L)
    (hε : P.c₈ * Flow.rate (L : ℝ) P.γ ≤ ε * (1 - Flow.rate (L : ℝ) P.γ))
    (hC : Def6.CoeffBounds d L (k + 1) P βs νs as) (hβ0 : βs 0 = β) (hν0 : νs 0 = ν)
    (hrun : RunningHypTo d L β ν a ε βs νs k) :
    RunningHypTo d L β ν a ε βs νs (k + 1) := by
  obtain ⟨hd, hL, hβ, hν, ha1, ha2, hε0, hε1, hγs, hδs⟩ := hrun
  obtain ⟨ξ, β₀, ν₀, hξ, hs, hseq⟩ := hC.flow
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have hL1 : (1 : ℝ) < L := by exact_mod_cast (by omega : 1 < L)
  have hq0 : 0 < Flow.rate (L : ℝ) P.γ := Flow.rate_pos hLpos _
  have hq1 : Flow.rate (L : ℝ) P.γ < 1 := Flow.rate_lt_one hL1 hP.γ_pos
  have hc8 : 0 ≤ P.c₈ := hP.c₈_pos.le
  have hexp : Real.exp (P.c₈ * Flow.ratePartialSum (Flow.rate (L : ℝ) P.γ) (k + 1)) ≤
      Real.exp ε := by
    refine Real.exp_le_exp.2 ?_
    have h1 := mul_le_mul_of_nonneg_left (Flow.ratePartialSum_le hq0.le hq1 (k + 1)) hc8
    have h2 : P.c₈ * (Flow.rate (L : ℝ) P.γ / (1 - Flow.rate (L : ℝ) P.γ)) ≤ ε := by
      rw [← mul_div_assoc, div_le_iff₀ (by linarith)]
      exact hε
    linarith
  obtain ⟨hg1, hg2, hd1, hd2⟩ := Flow.norm_gammaSeq_le hq0.le hq1 hc8 hs hξ (k + 1)
  have hb0 : ((β₀ : ℝ) : ℂ) = (β : ℂ) := by
    have := (hseq 0 (Nat.zero_le _)).1
    rw [hβ0] at this
    simpa [Flow.betaSeq] using this.symm
  have hn0 : ((ν₀ : ℝ) : ℂ) = (ν : ℂ) := by
    have := (hseq 0 (Nat.zero_le _)).2
    rw [hν0] at this
    simpa [Flow.nuSeq] using this.symm
  have hLne : ((L : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hβne : (β : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hβ.ne'
  have hνne : (ν : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hν.ne'
  refine ⟨hd, hL, hβ, hν, ha1, ha2, hε0, hε1, fun j hj => ?_, fun j hj => ?_⟩
  · rcases Nat.lt_or_ge j (k + 1) with hjk | hjk
    · exact hγs j (by omega)
    obtain rfl : j = k + 1 := by omega
    obtain ⟨γk, hγk0, -, hβk⟩ := hγs k le_rfl
    obtain ⟨γ', hβk1⟩ : ∃ γ' : ℝ, βs (k + 1) = β * (L : ℝ) ^ ((k + 1) * (d - 2)) * γ' :=
      ⟨βs (k + 1) / (β * (L : ℝ) ^ ((k + 1) * (d - 2))), by field_simp⟩
    have ek : ((γk : ℝ) : ℂ) = Flow.gammaSeq ξ k := by
      have h := (hseq k (by omega)).1
      rw [Flow.betaSeq_eq, hb0, hβk] at h
      push_cast at h
      exact mul_left_cancel₀ (mul_ne_zero hβne (pow_ne_zero _ hLne)) h
    have ek1 : ((γ' : ℝ) : ℂ) = Flow.gammaSeq ξ (k + 1) := by
      have h := (hseq (k + 1) le_rfl).1
      rw [Flow.betaSeq_eq, hb0, hβk1] at h
      push_cast at h
      exact mul_left_cancel₀ (mul_ne_zero hβne (pow_ne_zero _ hLne)) h
    have hrec : Flow.gammaSeq ξ (k + 1) = Flow.gammaSeq ξ k * (1 + ξ k 2)⁻¹ := by
      simp only [Flow.gammaSeq, Finset.prod_range_succ]
    have hξq : ‖ξ k 2‖ ≤ 1 / 4 :=
      (norm_le_pi_norm (ξ k) 2).trans (Flow.norm_le_quarter hq0.le hq1 hc8 hs hξ k)
    have hne1 : (1 + ξ k 2) ≠ 0 := by
      intro h0
      have : ξ k 2 = -1 := by linear_combination h0
      rw [this] at hξq
      norm_num at hξq
    have hmul : ((γ' : ℝ) : ℂ) * (1 + ξ k 2) = ((γk : ℝ) : ℂ) := by
      rw [ek1, hrec, ← ek, mul_assoc, inv_mul_cancel₀ hne1, mul_one]
    have hre : γ' * (1 + (ξ k 2).re) = γk := by
      have := congrArg Complex.re hmul
      simpa [Complex.re_ofReal_mul] using this
    have hre4 : -(1 / 4 : ℝ) ≤ (ξ k 2).re :=
      (abs_le.1 ((Complex.abs_re_le_norm _).trans hξq)).1
    have hγ'pos : 0 < γ' := by nlinarith
    exact ⟨γ', hγ'pos, abs_log_le_of_ofReal_eq ek1 hγ'pos (hg1.trans hexp) (hg2.trans hexp),
      hβk1⟩
  · rcases Nat.lt_or_ge j (k + 1) with hjk | hjk
    · exact hδs j (by omega)
    obtain rfl : j = k + 1 := by omega
    obtain ⟨δ', hνk1⟩ : ∃ δ' : ℝ, νs (k + 1) = ν * (L : ℝ) ^ (2 * (k + 1)) * δ' :=
      ⟨νs (k + 1) / (ν * (L : ℝ) ^ (2 * (k + 1))), by field_simp⟩
    have ed1 : ((δ' : ℝ) : ℂ) = Flow.deltaSeq ξ (k + 1) := by
      have h := (hseq (k + 1) le_rfl).2
      rw [Flow.nuSeq_eq, hn0, hνk1] at h
      push_cast at h
      exact mul_left_cancel₀ (mul_ne_zero hνne (pow_ne_zero _ hLne)) h
    have hδ'pos : 0 < δ' := by
      have h := hC.nu_pos
      rw [hνk1] at h
      have hp : 0 < ν * (L : ℝ) ^ (2 * (k + 1)) := by positivity
      exact pos_of_mul_pos_right h hp.le
    exact ⟨δ', hδ'pos, abs_log_le_of_ofReal_eq ed1 hδ'pos (hd1.trans hexp) (hd2.trans hexp),
      hνk1⟩

/-- **(I.2) at the scale of the output of a step.** A member of the pre-`R` class at the scale
`k + 1` whose running constants satisfy (I.2) up to `k` satisfies it up to `k + 1`, when the
constants have `c₈ q ≤ (1 - q)/20` (the coefficient step, `runningHypTo_succ_of_coeffBounds`
applied to the coefficient bounds (H.6) of its small-field data, `IsSFFamily2.coeff`). -/
theorem PreClassAt.succ {d N : ℕ} {T : Typing} {P6 : Def6.Consts} {C7 : Consts7}
    {PB : BudgetConsts} {cs₀ : OpConsts} {M1 c : ℕ} {rH ϱ β ν : ℝ}
    {h : EuclideanSpace ℝ (Fin N)} {kf k : ℕ} [NeZero T.M] [NeZero T.L]
    {ρ : 𝒟[d, N, T, β, cs₀.aKer, kf + 1, k + 1]} {νk : ℝ}
    (hρ : PreClassAt d N T P6 C7 PB cs₀ M1 c rH ϱ β ν h kf (k + 1) k ρ νk)
    (hq : P6.c₈ * Flow.rate (T.L : ℝ) P6.γ ≤ 1 / 20 * (1 - Flow.rate (T.L : ℝ) P6.γ)) :
    PreClassAt d N T P6 C7 PB cs₀ M1 c rH ϱ β ν h kf (k + 1) (k + 1) ρ νk := by
  obtain ⟨hM6, hkK, R, geo, cs, P, F, St, vc, hgeo, h1, h2, h3, h4, h5, h6, h7, hpre, hβ0, hν0,
    hνk, hrun, hcoh⟩ := hρ
  obtain ⟨_, hsf⟩ := hpre.sfData.sfClass
  exact ⟨hM6, hkK, R, geo, cs, P, F, St, vc, hgeo, h1, h2, h3, h4, h5, h6, h7, hpre, hβ0, hν0, hνk,
    runningHypTo_succ_of_coeffBounds hsf.admissible hq hsf.coeff hβ0 hν0 hrun, hcoh⟩

/-!
### The assembly of the integral
-/

section Normalization

variable {d N : ℕ} {T : Typing} {β a : ℝ} {K k : ℕ} [NeZero T.M] [NeZero T.L]

/-- `∫ ρ' = c ∫ ρ` and `∫ ρ'' = ∫ ρ'` at the same scale give `∫ ρ'' = c ∫ ρ`. -/
theorem IntegralStep.trans_eq {ρ : 𝒟[d, N, T, β, a, K, k]} {ρ' ρ'' : 𝒟[d, N, T, β, a, K, k + 1]}
    (hs : IntegralStep d N T β a K k ρ ρ')
    (he : ∀ (nK : ℕ) [NeZero nK] (g : GIdx 𝒮[d, T, β, a] (sides T.L K nK) T.M K N → ℂ),
      g ∈ l1Ball _ → ∫ ψ, ρ'' nK ψ g = ∫ ψ, ρ' nK ψ g) :
    IntegralStep d N T β a K k ρ ρ'' := by
  obtain ⟨C, hC, hI⟩ := hs
  exact ⟨C, hC, fun nK _ g hg => by rw [he nK g hg, hI nK g hg]⟩

end Normalization

/-!
### The sub-inputs
-/

section Inputs

variable (d N : ℕ) (T : ℝ → ℝ → Typing) (P6 : ℝ → ℝ → Def6.Consts)
  (C7 : ℝ → ℝ → Consts7) (PB : ℝ → ℝ → BudgetConsts) (cs₀ : ℝ → ℝ → OpConsts)
  (M1 c : ℝ → ℝ → ℕ) (rH ϱ : ℝ → ℝ → ℝ)

/-- **A4-1, the small-field step (LF-3; LFR Theorem IV.1.1 (a)–(e), (h); P5 Theorem 1 and P6
Theorem 1, pp. 499 and 2; P4 Theorem 1 for the small-field data).** For `1 ≤ k < k₀`, every member
`ρ` of `ℛ_k` has a successor `ρ' = S^{(k)} T^{(k)} ρ` (`ρ'(ψ_{k+1}) = z_{k+1}^{N|T^{(k+1)}|}
(T^{(k)} ρ)(z_{k+1} ψ_{k+1})`) in the pre-`R` class `ℛ^pre_{k+1}`: a representation `IsRepPre2` at
the scale `k + 1` (the histories of `ρ` followed by every step record and the hull closure; the
quiet kernels and the kernels of P5 (2.47)·P6 (3.2) as step data; the small-field data of P4 Theorem
1 on `Z^c_{k+1}`, whose coefficient bounds (H.6) at `k + 1` contain the flow relation of P4 (5.28)
for `β_{k+1}, ν_{k+1}`; boundary terms with rate `3κ/2` and the constant `B_st`; the budget
(H6′)^pre), with running constants that start from `β, ν` and satisfy (I.2) at the scales `≤ k`,
with torus coherent large-field data (LF-3 (h), D-IV.9), and with `∫ ρ' = c ∫ ρ` (LF-3 (a)). -/
def SFStepInput : Prop :=
  ∀ κ : ℝ, 0 < κ → ∀ c₉ : ℝ, 0 < c₉ → ∃ β₀ : ℝ, ∀ β : ℝ, β₀ ≤ β →
  ∀ ν : ℝ, 0 < ν → ν * ((T κ c₉).L : ℝ) ^ 2 ≤ 7 / 8 →
  ∀ h : EuclideanSpace ℝ (Fin N), ‖h‖ = 1 → ∀ kf : ℕ, IsHorizon (T κ c₉).L ν kf →
  ∀ [NeZero (T κ c₉).L] [NeZero (T κ c₉).M],
  ∀ k : ℕ, 1 ≤ k → k < kZero d (T κ c₉).L β ν →
  ∀ (ρ : 𝒟[d, N, T κ c₉, β, (cs₀ κ c₉).aKer, kf + 1, k]) (νk : ℝ),
    RepClassAt d N (T κ c₉) (P6 κ c₉) (C7 κ c₉) (PB κ c₉) (cs₀ κ c₉) (M1 κ c₉) (c κ c₉)
      (rH κ c₉) (ϱ κ c₉) β ν h kf k ρ νk →
    ∃ (ρ' : 𝒟[d, N, T κ c₉, β, (cs₀ κ c₉).aKer, kf + 1, k + 1]) (νk' : ℝ),
      PreClassAt d N (T κ c₉) (P6 κ c₉) (C7 κ c₉) (PB κ c₉) (cs₀ κ c₉) (M1 κ c₉) (c κ c₉)
        (rH κ c₉) (ϱ κ c₉) β ν h kf (k + 1) k ρ' νk' ∧
      IntegralStep d N (T κ c₉) β (cs₀ κ c₉).aKer (kf + 1) k ρ ρ'

/-- **A4-2, the large-field operation `R` (LF-4; LFR Theorem III.10.8, P7 Theorem 2 = P5 Theorem 2,
P7 (1.3)–(1.7), pp. 497–529; ruling R4).** For `1 ≤ k ≤ k₀`, every member `ρ` of `ℛ^pre_k` whose
running constants satisfy (I.2) up to `k` and whose large-field data are torus coherent has an image
`ρ' = R^{(k)} ρ` in `ℛ_k` with the same running mass `ν_k` and the same integral
(`∫ R ρ = ∫ ρ`, P7 (1.7), LFR Lemma III.8.4): the ripe components are removed or kept with a label;
the removed clusters are summed as a gas whose activities are bounded through the small factor
(3.10″) of the removed operators (ruling R4); the gas gives the new term `ℛ''^{(k)}_m` and the new
boundary terms (LFR Lemma III.10.5, Definition III.10.6); the other small-field data, the running
constants and (I.2) are unchanged (Theorem III.10.8 (c)); the output is torus coherent (proof of
Theorem III.10.8, (D8)). -/
def RInput : Prop :=
  ∀ κ : ℝ, 0 < κ → ∀ c₉ : ℝ, 0 < c₉ → ∃ β₀ : ℝ, ∀ β : ℝ, β₀ ≤ β →
  ∀ ν : ℝ, 0 < ν → ν * ((T κ c₉).L : ℝ) ^ 2 ≤ 7 / 8 →
  ∀ h : EuclideanSpace ℝ (Fin N), ‖h‖ = 1 → ∀ kf : ℕ, IsHorizon (T κ c₉).L ν kf →
  ∀ [NeZero (T κ c₉).L] [NeZero (T κ c₉).M],
  ∀ k : ℕ, 1 ≤ k → k ≤ kZero d (T κ c₉).L β ν →
  ∀ (ρ : 𝒟[d, N, T κ c₉, β, (cs₀ κ c₉).aKer, kf + 1, k]) (νk : ℝ),
    PreClassAt d N (T κ c₉) (P6 κ c₉) (C7 κ c₉) (PB κ c₉) (cs₀ κ c₉) (M1 κ c₉) (c κ c₉)
      (rH κ c₉) (ϱ κ c₉) β ν h kf k k ρ νk →
    ∃ ρ' : 𝒟[d, N, T κ c₉, β, (cs₀ κ c₉).aKer, kf + 1, k],
      RepClassAt d N (T κ c₉) (P6 κ c₉) (C7 κ c₉) (PB κ c₉) (cs₀ κ c₉) (M1 κ c₉) (c κ c₉)
        (rH κ c₉) (ϱ κ c₉) β ν h kf k ρ' νk ∧
      ∀ (nK : ℕ) [NeZero nK]
        (g : GIdx 𝒮[d, T κ c₉, β, (cs₀ κ c₉).aKer] (sides (T κ c₉).L (kf + 1) nK) (T κ c₉).M
          (kf + 1) N → ℂ), g ∈ l1Ball _ →
        ∫ ψ, ρ' nK ψ g = ∫ ψ, ρ nK ψ g

/-- **A4-3, the coefficient step (LFR Theorem IV.3.2 (d); prefix row 10, `c₈ ∈ (0, c₈′]`).** For
every `κ, c₉ > 0` the Def-6 constants satisfy `c₈ q ≤ (1 - q)/20` with `q = L^{-2γ}`, i.e. the
bound `ε = c₈ q/(1 - q) ≤ 1/20` that turns the flow bound `|ξ^{(j)}| ≤ (c₈/4) q^{j+1}` of (H.6) into
(I.2) (`runningHypTo_succ_of_coeffBounds`). The flow of P4 satisfies the flow bound with
`c₈ = c_ξ/β`, so a fixed `c₈` costs only the threshold `β ≥ c_ξ/c₈`. -/
def FlowRateInput : Prop :=
  ∀ κ : ℝ, 0 < κ → ∀ c₉ : ℝ, 0 < c₉ →
    (P6 κ c₉).c₈ * Flow.rate ((T κ c₉).L : ℝ) (P6 κ c₉).γ ≤
      1 / 20 * (1 - Flow.rate ((T κ c₉).L : ℝ) (P6 κ c₉).γ)

/-- **The class step from its sub-inputs** (LFR Theorem IV.3.2 (a)–(d) for `1 ≤ k < k₀`): LF-3
(`SFStepInput`) gives `ρ' ∈ ℛ^pre_{k+1}` with `∫ ρ' = c ∫ ρ`; the coefficient step
(`FlowRateInput`, `PreClassAt.succ`) gives (I.2) at `k + 1`; LF-4 at the scale `k + 1 ≤ k₀`
(`RInput`) gives `ρ'' = R ρ' ∈ ℛ_{k+1}` with `∫ ρ'' = ∫ ρ'`. The threshold is the larger of the
two thresholds. -/
theorem classStepInput_of_parts (hSF : SFStepInput d N T P6 C7 PB cs₀ M1 c rH ϱ)
    (hR : RInput d N T P6 C7 PB cs₀ M1 c rH ϱ) (hQ : FlowRateInput T P6) :
    ClassStepInput d N T P6 C7 PB cs₀ M1 c rH ϱ := by
  intro κ hκ c₉ hc₉
  obtain ⟨β₁, hβ₁⟩ := hSF κ hκ c₉ hc₉
  obtain ⟨β₂, hβ₂⟩ := hR κ hκ c₉ hc₉
  refine ⟨max β₁ β₂, fun β hβ ν hν hνL h hh kf hkf _ _ k hk1 hk ρ νk hρ => ?_⟩
  obtain ⟨ρ', νk', hpre, hint⟩ :=
    hβ₁ β (le_of_max_le_left hβ) ν hν hνL h hh kf hkf k hk1 hk ρ νk hρ
  obtain ⟨ρ'', hcl, hint'⟩ :=
    hβ₂ β (le_of_max_le_right hβ) ν hν hνL h hh kf hkf (k + 1) (by omega) hk ρ' νk'
      (hpre.succ (hQ κ hκ c₉ hc₉))
  exact ⟨ρ'', νk', hcl, hint.trans_eq hint'⟩

end Inputs

/-!
### Inhabitation (rule 10)
-/

open Balaban.LargeField.Def7.Wit Balaban.LargeField.Def7v2.Wit in
/-- The body of `PreClassAt` at the witness constants, for any setting equal to the witness setting
`wS` and every `r ≤ 1`. -/
theorem preClassAt_witness_aux (rH : ℝ) (r : ℕ) (hr : r ≤ 1) (S : Setting) (hS : S = wS)
    [NeZero S.L] :
    ∃ (ρ : ∀ (nK : ℕ) [NeZero nK], (BlockAt S (sides S.L 1 nK) 27 1 1 → EuclideanSpace ℝ (Fin 2)) →
        (GIdx S (sides S.L 1 nK) 27 1 2 → ℂ) → ℂ) (νk : ℝ)
      (hM6 : (27 : ℕ) = S.L ^ (wP6.m₀ + wC7.m₁)) (hkK : 1 ≤ 1) (R : ℕ → ℝ)
      (geo : ∀ (nK : ℕ) [NeZero nK], Geo S (sides S.L 1 nK) R 27) (cs : OpConsts)
      (P : BudgetConsts) (F : RepFam S R (kZero S.d S.L wβ wν₀) 1 27 2 geo cs P 1 wC7.m₁
        (Background.bgR0 3 3))
      (St : ∀ (N₁ : ℕ) [NeZero N₁], Def6v2.SourceTerms S.d S.L N₁ wC7.m₁ 1 2) (vc : CorrCoef S.d),
      (∀ (nK : ℕ) [NeZero nK], (geo nK).M1 = 1 ∧ (geo nK).c = 27) ∧
      cs.aKer = (wCs wν₀ (kZero 3 3 wβ wν₀)).aKer ∧ cs.Cpsi = (wCs wν₀ (kZero 3 3 wβ wν₀)).Cpsi ∧
      cs.Cb = (wCs wν₀ (kZero 3 3 wβ wν₀)).Cb ∧ cs.aw = (wCs wν₀ (kZero 3 3 wβ wν₀)).aw ∧
      P.c1 = (budgetConsts wβ).c1 ∧ P.c2 = (budgetConsts wβ).c2 ∧ P.H0 = (budgetConsts wβ).H0 ∧
      IsRepPre2 S R (kZero S.d S.L wβ wν₀) 1 27 2 geo cs P wP6 wC7 wβ wν₀ whv rH 1 hM6 hkK F ρ St
        vc ∧
      F.sf.β 0 = wβ ∧ F.sf.ν 0 = wν₀ ∧ F.sf.ν 1 = νk ∧
      RunningHypTo S.d S.L wβ wν₀ (wCs wν₀ (kZero 3 3 wβ wν₀)).aKer (1 / 20) F.sf.β F.sf.ν r ∧
      LFCoherent F := by
  subst hS
  exact ⟨wRhoPre2 wν₀ (kZero 3 3 wβ wν₀) 1, wνs wν₀ 1, wM6, le_rfl, wR, wGeoF,
    wCs wν₀ (kZero 3 3 wβ wν₀), budgetConsts wβ, wFam2 wν₀ (kZero 3 3 wβ wν₀) 1, wSt wν₀,
    wVc, fun _ _ => ⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    wIsRepPre2 wν₀ wν₀_pos wν₀_mul.le rH, by simp [wFam2, wSF2, wβs], by simp [wFam2, wSF2, wνs],
    rfl, witness_runningHypTo.mono hr, wFam2_lfCoherent _ _ _⟩

open Balaban.LargeField.Def7.Wit Balaban.LargeField.Def7v2.Wit in
/-- **`PreClassAt` is inhabited**: the landed witness of `IsRepPre2` at `ν = 1/(27β)`, horizon
`kf = 0`, scale `k = 1`, with (I.2) up to `r = 0` (the form of the output of `SFStepInput`) or
`r = 1` (the form of the hypothesis of `RInput`). -/
theorem preClassAt_witness (rH : ℝ) (r : ℕ) (hr : r ≤ 1) :
    ∃ (ρ : 𝒟[3, 2, typing, wβ, (wCs wν₀ (kZero 3 3 wβ wν₀)).aKer, 0 + 1, 1]) (νk : ℝ),
      @PreClassAt 3 2 typing wP6 wC7 (budgetConsts wβ) (wCs wν₀ (kZero 3 3 wβ wν₀)) 1 27 rH
        (Background.bgR0 3 3) wβ wν₀ whv 0 1 r ⟨by norm_num [typing, typing0]⟩
        ⟨by norm_num [typing, typing0]⟩ ρ νk :=
  @preClassAt_witness_aux rH r hr _ spineSetting_eq_wS ⟨by norm_num [typing, typing0]⟩

/-- **`FlowRateInput` costs only a smaller `c₈`**: for every family of admissible Def-6 constants
on block sizes `L ≥ 2`, lowering `c₈` to `min(c₈, (1 - q)/(20 q))` keeps the constants admissible
and gives `FlowRateInput`. -/
theorem flowRateInput_of_lower (d : ℕ) (T : ℝ → ℝ → Typing) (P6 : ℝ → ℝ → Def6.Consts)
    (hL : ∀ κ c₉, 2 ≤ (T κ c₉).L) (hP : ∀ κ c₉, (P6 κ c₉).Admissible d (T κ c₉).L) :
    ∃ c₈ : ℝ → ℝ → ℝ, (∀ κ c₉, 0 < c₈ κ c₉ ∧ c₈ κ c₉ ≤ (P6 κ c₉).c₈) ∧
      (∀ κ c₉, ({ P6 κ c₉ with c₈ := c₈ κ c₉ } : Def6.Consts).Admissible d (T κ c₉).L) ∧
      FlowRateInput T (fun κ c₉ => { P6 κ c₉ with c₈ := c₈ κ c₉ }) := by
  have hq : ∀ κ c₉, 0 < Flow.rate ((T κ c₉).L : ℝ) (P6 κ c₉).γ ∧
      Flow.rate ((T κ c₉).L : ℝ) (P6 κ c₉).γ < 1 := fun κ c₉ =>
    ⟨Flow.rate_pos (by exact_mod_cast (by have := hL κ c₉; omega : 0 < (T κ c₉).L)) _,
      Flow.rate_lt_one (by exact_mod_cast (by have := hL κ c₉; omega : 1 < (T κ c₉).L))
        (hP κ c₉).γ_pos⟩
  refine ⟨fun κ c₉ => min (P6 κ c₉).c₈ ((1 - Flow.rate ((T κ c₉).L : ℝ) (P6 κ c₉).γ) /
      (20 * Flow.rate ((T κ c₉).L : ℝ) (P6 κ c₉).γ)), fun κ c₉ => ⟨?_, min_le_left _ _⟩,
    fun κ c₉ => ?_, fun κ _ c₉ _ => ?_⟩
  · obtain ⟨hq0, hq1⟩ := hq κ c₉
    exact lt_min (hP κ c₉).c₈_pos (div_pos (by linarith) (by positivity))
  · obtain ⟨hq0, hq1⟩ := hq κ c₉
    have H := hP κ c₉
    exact ⟨H.γ_pos, H.γ_lt, H.α₁_pos, H.α₁_lt, H.α₀_pos, H.κ_pos, H.νbar_pos, H.νbar_le,
      lt_min H.c₈_pos (div_pos (by linarith) (by positivity)), H.E₀_nonneg⟩
  · obtain ⟨hq0, hq1⟩ := hq κ c₉
    show min (P6 κ c₉).c₈ ((1 - Flow.rate ((T κ c₉).L : ℝ) (P6 κ c₉).γ) /
        (20 * Flow.rate ((T κ c₉).L : ℝ) (P6 κ c₉).γ)) * Flow.rate ((T κ c₉).L : ℝ) (P6 κ c₉).γ ≤
      1 / 20 * (1 - Flow.rate ((T κ c₉).L : ℝ) (P6 κ c₉).γ)
    have h1 := mul_le_mul_of_nonneg_right (min_le_right (P6 κ c₉).c₈
      ((1 - Flow.rate ((T κ c₉).L : ℝ) (P6 κ c₉).γ) /
        (20 * Flow.rate ((T κ c₉).L : ℝ) (P6 κ c₉).γ))) hq0.le
    have h2 : (1 - Flow.rate ((T κ c₉).L : ℝ) (P6 κ c₉).γ) /
        (20 * Flow.rate ((T κ c₉).L : ℝ) (P6 κ c₉).γ) * Flow.rate ((T κ c₉).L : ℝ) (P6 κ c₉).γ =
        1 / 20 * (1 - Flow.rate ((T κ c₉).L : ℝ) (P6 κ c₉).γ) := by
      field_simp
    linarith

end Balaban.RootFSpine
