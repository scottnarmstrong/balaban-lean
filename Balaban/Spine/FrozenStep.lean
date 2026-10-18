/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.ClassStep
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The frozen step of the spine from two sub-inputs

`frozenStepInput_of_parts` proves the spine input `FrozenStepInput` (A4, `Spine/RootFInputs.lean`)
from two named sub-inputs, following LFR Theorem IV.2.2 (LF-5, one frozen step): for
`max(k₀, 1) ≤ k < k_f` the step `ℛ♭_k → ℛ♭_{k+1}` is one full step `S^{(k)} T^{(k)}` with complete
backgrounds, **with no operation `R`** ((c): "no hull, no `R`"; the operator `R` of LF-4 acts only
below `k₀`). The running constants at `k + 1` satisfy (I.2) and the mass bound (D9♭) by the flow.

* `FrozenSFStepInput` (LF-5 (a)–(f); P5/P6 Theorem 4 repaired, P4 Theorem 1 and FLUCTUATION
  Theorem 5.3 for the small-field data, Lemma 2.9 for the switch at `k = k₀`): a member of `ℛ♭_k`
  with `ν_k ≤ 7/8 L⁻²` has a successor in the class `FlatPreAt` (the frozen class at `k + 1` with
  (I.2) asked up to `k` only and no mass bound), whose running mass at the scale `k` is the old one,
  with `∫ ρ' = c ∫ ρ`. The flow relation (H.6) of the new coefficients is the clause `coeff` of
  `IsRepFlat2` at `k + 1`.
* `FlowRateInput` (`Spine/ClassStep.lean`): the constant condition `c₈ q/(1 - q) ≤ 1/20`.

Proved here, from the landed flow lemmas: (I.2) at `k + 1` (`runningHypTo_succ_of_coeffBounds_core`
at the constants `massOne P6`, which have the `γ` and `c₈` of `P6`), and the mass bound
`ν_{k+1} = ν_k L² (1 + ξ₃)/(1 + ξ₂) ≤ (81/79) ν_k L² ≤ 9/10` (`nu_succ_le_of_coeffBounds`): the
flow bound `|ξ^{(k)}| ≤ (c₈/4) q^{k+1}` and `c₈ q ≤ (1 - q)/20` give `|ξ^{(k)}| ≤ 1/80`, and
`(7/8)(81/79) < 9/10`.

**Coherence** is a conjunct of the output of `FrozenSFStepInput`, for the reason given in
`Spine/ClassStep.lean` (the representation that the step builds is not named by any landed
operator). The scale of (I.2) and the mass clause of the output are the parameters `r, X` of
`FlatRepGen`. Inhabitation (rule 10): `flatPreAt_witness`. The list and the status of the
sub-inputs are in `notes/phase1/SPINE.md`, section "FrozenStepInput sub-inputs". -/

@[expose] public section

namespace Balaban.RootFSpine

open MeasureTheory Balaban Balaban.LargeField Balaban.LargeField.Def7 Balaban.LargeField.Def7v2
  Balaban.SmallField Balaban.SmallField.Def6v2

/-!
### The mass bound (D9♭) at `k + 1`
-/

/-- **(D9♭) at `k + 1` from the flow**: if `ν_k > 0`, the flow bound `|ξ^{(k)}| ≤ (c₈/4) q^{k+1}`
with `c₈ q ≤ (1 - q)/20` holds (the clause `flow` of `CoeffBounds` at `k + 1`), then
`ν_{k+1} = ν_k L² (1 + ξ₃)/(1 + ξ₂) ≤ (81/79) ν_k L²`. -/
theorem nu_succ_le_of_coeffBounds {d L : ℕ} {P : Def6.Consts} {βs νs as : ℕ → ℝ} {k : ℕ}
    (hL : 2 ≤ L) (hγ : 0 < P.γ)
    (hε : P.c₈ * Flow.rate (L : ℝ) P.γ ≤ 1 / 20 * (1 - Flow.rate (L : ℝ) P.γ))
    (hC : Def6.CoeffBounds d L (k + 1) P βs νs as) (hνk : 0 < νs k) :
    νs (k + 1) ≤ 81 / 79 * (νs k * (L : ℝ) ^ 2) := by
  obtain ⟨ξ, β₀, ν₀, hξ, -, hseq⟩ := hC.flow
  have hL1 : (1 : ℝ) < L := by exact_mod_cast (by omega : 1 < L)
  have hq0 : 0 < Flow.rate (L : ℝ) P.γ := Flow.rate_pos (by linarith) _
  have hq1 : Flow.rate (L : ℝ) P.γ < 1 := Flow.rate_lt_one hL1 hγ
  have hqk : Flow.rate (L : ℝ) P.γ ^ (k + 1) ≤ Flow.rate (L : ℝ) P.γ := by
    rw [pow_succ']
    exact mul_le_of_le_one_right hq0.le (pow_le_one₀ hq0.le hq1.le)
  have hc8 : 0 ≤ P.c₈ := by
    by_contra hneg0
    have hneg : P.c₈ < 0 := not_le.mp hneg0
    have := hξ 0
    have h0 : 0 ≤ ‖ξ 0‖ := norm_nonneg _
    have h1 : 0 < Flow.rate (L : ℝ) P.γ ^ (0 + 1) := pow_pos hq0 _
    nlinarith
  have hw : ‖ξ k‖ ≤ 1 / 80 := by
    refine (hξ k).trans ?_
    have := mul_le_mul_of_nonneg_left hqk hc8
    nlinarith
  set w := ‖ξ k‖ with hwdef
  have hw0 : 0 ≤ w := norm_nonneg _
  have hx : ‖(ξ k) 2‖ ≤ w := norm_le_pi_norm (ξ k) 2
  have hy : ‖(ξ k) 1‖ ≤ w := norm_le_pi_norm (ξ k) 1
  have h1 : ‖(1 : ℂ) + ξ k 2‖ ≤ 1 + w := by
    calc ‖(1 : ℂ) + ξ k 2‖ ≤ ‖(1 : ℂ)‖ + ‖ξ k 2‖ := norm_add_le _ _
      _ ≤ 1 + w := by rw [norm_one]; linarith
  have h2 : 1 - w ≤ ‖(1 : ℂ) + ξ k 1‖ := by
    have := norm_sub_norm_le (1 : ℂ) (-ξ k 1)
    simp only [sub_neg_eq_add, norm_neg, norm_one] at this
    linarith
  have hk := (hseq k (Nat.le_succ k)).2
  have hk1 := (hseq (k + 1) le_rfl).2
  have hrec : ((νs (k + 1) : ℝ) : ℂ) =
      ((νs k : ℝ) : ℂ) * (L : ℂ) ^ 2 * (1 + ξ k 2) / (1 + ξ k 1) := by
    rw [hk1, Flow.nuSeq, hk]
    push_cast
    rfl
  have hnorm : νs (k + 1) * ‖(1 : ℂ) + ξ k 1‖ =
      νs k * (L : ℝ) ^ 2 * ‖(1 : ℂ) + ξ k 2‖ := by
    have hne : (1 : ℂ) + ξ k 1 ≠ 0 := by
      intro h0
      have : ‖(1 : ℂ) + ξ k 1‖ = 0 := by rw [h0, norm_zero]
      linarith
    have hν1 : 0 < νs (k + 1) := hC.nu_pos
    have := congrArg norm (by rw [hrec, div_mul_cancel₀ _ hne] : ((νs (k + 1) : ℝ) : ℂ) *
      (1 + ξ k 1) = ((νs k : ℝ) : ℂ) * (L : ℂ) ^ 2 * (1 + ξ k 2))
    simpa [norm_mul, abs_of_pos hν1, abs_of_pos hνk] using this
  have hν1 : 0 < νs (k + 1) := hC.nu_pos
  have hA : 0 < νs k * (L : ℝ) ^ 2 := by positivity
  have hb : 79 / 80 ≤ ‖(1 : ℂ) + ξ k 1‖ := by linarith
  have h3 : νs k * (L : ℝ) ^ 2 * ‖(1 : ℂ) + ξ k 2‖ ≤ νs k * (L : ℝ) ^ 2 * (81 / 80) := by
    exact mul_le_mul_of_nonneg_left (h1.trans (by linarith)) hA.le
  nlinarith [mul_le_mul_of_nonneg_left hb hν1.le]

/-!
### The frozen class at `k + 1` before the coefficient step
-/

/-- **The frozen class `ℛ♭_k` with (I.2) up to a scale `r` and a clause `X` on the running masses**
(`FlatRepGen`), at the constants of the prefix and with the conventions of `FlatClassAt`, which is
the case `r = k`, `X = (νk ≤ 9/10)` (`flatPreAt_iff_flatClassAt` is not needed: the frozen step
uses `FlatClassAt` as input and `FlatPreAt` as the output of its small-field half). -/
def FlatPreAt (d N : ℕ) (T : Typing) (P6 : Def6.Consts) (C7 : Consts7) (PB : BudgetConsts)
    (cs₀ : OpConsts) (M1 c : ℕ) (rH ϱ : ℝ) (β ν : ℝ) (h : EuclideanSpace ℝ (Fin N)) (kf k r : ℕ)
    (X : (ℕ → ℝ) → Prop) [NeZero T.M] [NeZero T.L] (ρ : 𝒟[d, N, T, β, cs₀.aKer, kf + 1, k])
    (νk : ℝ) : Prop :=
  ∃ (hM6 : T.M = T.L ^ (P6.m₀ + C7.m₁)) (hkK : k ≤ kf + 1) (R : ℕ → ℝ)
    (geo : ∀ (nK : ℕ) [NeZero nK], Geo 𝒮[d, T, β, cs₀.aKer] (sides T.L (kf + 1) nK) R T.M)
    (cs : OpConsts) (P : BudgetConsts)
    (F : RepFam 𝒮[d, T, β, cs₀.aKer] R (kZero d T.L β ν) (kf + 1) T.M N geo cs P k C7.m₁ ϱ)
    (St : ∀ (N₁ : ℕ) [NeZero N₁], SourceTerms d T.L N₁ C7.m₁ k N) (vc : CorrCoef d),
    FlatRepGen d N T P6 C7 PB cs₀ M1 c rH ϱ β ν h kf k r X hM6 hkK R geo cs P F St vc ρ νk

/-!
### The sub-input
-/

section Inputs

variable (d N : ℕ) (T : ℝ → ℝ → Typing) (P6 : ℝ → ℝ → Def6.Consts)
  (C7 : ℝ → ℝ → Consts7) (PB : ℝ → ℝ → BudgetConsts) (cs₀ : ℝ → ℝ → OpConsts)
  (M1 c : ℝ → ℝ → ℕ) (rH ϱ : ℝ → ℝ → ℝ)

/-- **A4f-1, the frozen small-field step (LF-5; LFR Theorem IV.2.2 (a)–(f); P5/P6 Theorem 4
repaired, P4 Theorem 1 with FLUCTUATION Theorem 5.3 and Lemma 2.9 for the small-field data).** For
`max(k₀, 1) ≤ k < k_f` and `ρ ∈ ℛ♭_k` with `ν_k ≤ 7/8 L⁻²`, the density
`ρ' = S^{(k)} T^{(k)} ρ` has a representation in the frozen class at `k + 1` (the histories of `ρ`
followed by every step record, with no hull and no `R`; the step data of P5 (2.47)·P6 (3.2) at the
complete backgrounds of mass `μ_{k+1} = ν_{k+1} L^{-2(k+1)}`; the small-field data of P4 Theorem 1,
whose coefficient bounds (H.6) at `k + 1` contain the flow relation of P4 (5.28); (D7) with
`B_st ≤ B_0 - 1`; (H6♭) by LF-2 (ii)), torus coherent, with `β_0 = β`, `ν_0 = ν`, (I.2) up to `k`,
the running mass at the scale `k` equal to that of `ρ` (the new small-field coefficients extend the
old ones), and `∫ ρ' = c ∫ ρ`. (I.2) at `k + 1` and the mass bound `ν_{k+1} ≤ 9/10` are not part of
the output: they follow from (H.6) at `k + 1` (`frozenStepInput_of_parts`). -/
def FrozenSFStepInput : Prop :=
  ∀ κ : ℝ, 0 < κ → ∀ c₉ : ℝ, 0 < c₉ → ∃ β₀ : ℝ, ∀ β : ℝ, β₀ ≤ β →
  ∀ ν : ℝ, 0 < ν → ν * ((T κ c₉).L : ℝ) ^ 2 ≤ 7 / 8 →
  ∀ h : EuclideanSpace ℝ (Fin N), ‖h‖ = 1 → ∀ kf : ℕ, IsHorizon (T κ c₉).L ν kf →
  ∀ [NeZero (T κ c₉).L] [NeZero (T κ c₉).M],
  ∀ k : ℕ, 1 ≤ k → kZero d (T κ c₉).L β ν ≤ k → k < kf →
  ∀ (ρ : 𝒟[d, N, T κ c₉, β, (cs₀ κ c₉).aKer, kf + 1, k]) (νk : ℝ),
    FlatClassAt d N (T κ c₉) (P6 κ c₉) (C7 κ c₉) (PB κ c₉) (cs₀ κ c₉) (M1 κ c₉) (c κ c₉)
      (rH κ c₉) (ϱ κ c₉) β ν h kf k ρ νk →
    νk * ((T κ c₉).L : ℝ) ^ 2 ≤ 7 / 8 →
    ∃ (ρ' : 𝒟[d, N, T κ c₉, β, (cs₀ κ c₉).aKer, kf + 1, k + 1]) (νk' : ℝ),
      FlatPreAt d N (T κ c₉) (P6 κ c₉) (C7 κ c₉) (PB κ c₉) (cs₀ κ c₉) (M1 κ c₉) (c κ c₉)
        (rH κ c₉) (ϱ κ c₉) β ν h kf (k + 1) k (fun νs => νs k = νk) ρ' νk' ∧
      IntegralStep d N (T κ c₉) β (cs₀ κ c₉).aKer (kf + 1) k ρ ρ'

/-- **The frozen step from its sub-inputs** (LFR Theorem IV.2.2 for `max(k₀, 1) ≤ k < k_f`): LF-5
(`FrozenSFStepInput`) gives `ρ' ∈ ℛ♭_{k+1}` with (I.2) up to `k`, `∫ ρ' = c ∫ ρ`; the coefficient step
(`FlowRateInput`, `runningHypTo_succ_of_coeffBounds_core` at `massOne P6`) gives (I.2) at `k + 1`;
the mass bound (D9♭) `ν_{k+1} ≤ 9/10` is `nu_succ_le_of_coeffBounds` with `ν_k L² ≤ 7/8`,
`(7/8)(81/79) ≤ 9/10`. -/
theorem frozenStepInput_of_parts (hSF : FrozenSFStepInput d N T P6 C7 PB cs₀ M1 c rH ϱ)
    (hQ : FlowRateInput T P6) : FrozenStepInput d N T P6 C7 PB cs₀ M1 c rH ϱ := by
  intro κ hκ c₉ hc₉
  obtain ⟨β₁, hβ₁⟩ := hSF κ hκ c₉ hc₉
  refine ⟨β₁, fun β hβ ν hν hνL h hh kf hkf _ _ k hk1 hk0 hk ρ νk hρ hνk => ?_⟩
  obtain ⟨ρ', νk', hpre, hint⟩ := hβ₁ β hβ ν hν hνL h hh kf hkf k hk1 hk0 hk ρ νk hρ hνk
  refine ⟨ρ', νk', ?_, hint⟩
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hrep0, _, _, hνk0, _, _, _⟩ := hρ
  have hνpos : 0 < νk := hνk0 ▸ hrep0.coeff.nu_pos
  obtain ⟨hM6, hkK, R, geo, cs, P, F, St, vc, hgeo, h1, h2, h3, h4, h5, h6, h7, hrep, hβ0, hν0,
    hνk', hrun, hcoh, hX⟩ := hpre
  have hX' : F.sf.ν k = νk := hX
  have hC := hrep.sfData.coeff
  have hL : 2 ≤ (T κ c₉).L := hrun.hL
  have hrun' := runningHypTo_succ_of_coeffBounds_core (P := massOne (P6 κ c₉))
    hrep.sfData.admissible.γ_pos hrep.sfData.admissible.c₈_pos (hQ κ hκ c₉ hc₉) hC hβ0 hν0 hrun
  have hmass := nu_succ_le_of_coeffBounds (P := massOne (P6 κ c₉)) hL hrep.sfData.admissible.γ_pos (hQ κ hκ c₉ hc₉) hC
    (hX'.symm ▸ hνpos)
  rw [hνk', hX'] at hmass
  refine ⟨hM6, hkK, R, geo, cs, P, F, St, vc, ?_⟩
  unfold FlatRep FlatRepGen
  exact ⟨hgeo, h1, h2, h3, h4, h5, h6, h7, hrep, hβ0, hν0, hνk', hrun', hcoh, by
    show νk' ≤ 9 / 10
    nlinarith⟩

/-- **The frozen step from its sub-input and the prefix**: `frozenStepInput_of_parts`, the rate
condition `FlowRateInput` being a clause of `PrefixInput`. -/
theorem frozenStepInput_of_prefix {δ : ℝ} (hA1 : PrefixInput d δ T P6 C7 PB cs₀ M1 c ϱ)
    (hSF : FrozenSFStepInput d N T P6 C7 PB cs₀ M1 c rH ϱ) :
    FrozenStepInput d N T P6 C7 PB cs₀ M1 c rH ϱ :=
  frozenStepInput_of_parts d N T P6 C7 PB cs₀ M1 c rH ϱ hSF (flowRateInput_of_prefix hA1)

end Inputs

/-!
### Inhabitation (rule 10)
-/

/-- A member of `ℛ♭_k` is a member of `FlatPreAt` with `r = k` and the clause `ν_0 = ν`. -/
theorem FlatClassAt.toFlatPreAt {d N : ℕ} {T : Typing} {P6 : Def6.Consts} {C7 : Consts7}
    {PB : BudgetConsts} {cs₀ : OpConsts} {M1 c : ℕ} {rH ϱ β ν : ℝ}
    {h : EuclideanSpace ℝ (Fin N)} {kf k : ℕ} [NeZero T.M] [NeZero T.L]
    {ρ : 𝒟[d, N, T, β, cs₀.aKer, kf + 1, k]} {νk : ℝ}
    (hρ : FlatClassAt d N T P6 C7 PB cs₀ M1 c rH ϱ β ν h kf k ρ νk) :
    FlatPreAt d N T P6 C7 PB cs₀ M1 c rH ϱ β ν h kf k k (fun νs => νs 0 = ν) ρ νk := by
  obtain ⟨hM6, hkK, R, geo, cs, P, F, St, vc, hgeo, h1, h2, h3, h4, h5, h6, h7, hrep, hβ0, hν0,
    hνk, hrun, hcoh, -⟩ := hρ
  exact ⟨hM6, hkK, R, geo, cs, P, F, St, vc, hgeo, h1, h2, h3, h4, h5, h6, h7, hrep, hβ0, hν0,
    hνk, hrun, hcoh, hν0⟩

open Balaban.LargeField.Def7.Wit Balaban.LargeField.Def7v2.Wit in
/-- **`FlatPreAt` is inhabited**: the landed witness of `FlatClassAt` (`flatClassAt_witness`, `ν =
1/(27β)`, horizon `kf = 0`, scale `k = 1`) with `r = 1` and the clause `ν_0 = ν`. -/
theorem flatPreAt_witness (rH : ℝ) :
    ∃ (ρ : 𝒟[3, 2, typing, wβ, (wCs wν₀ (kZero 3 3 wβ wν₀)).aKer, 0 + 1, 1]) (νk : ℝ),
      @FlatPreAt 3 2 typing wP6 wC7 (budgetConsts wβ) (wCs wν₀ (kZero 3 3 wβ wν₀)) 1 27 rH
        (Background.bgR0 3 3) wβ wν₀ whv 0 1 1 (fun νs => νs 0 = wν₀)
        ⟨by norm_num [typing, typing0]⟩ ⟨by norm_num [typing, typing0]⟩ ρ νk := by
  obtain ⟨ρ, νk, hρ⟩ := flatClassAt_witness rH
  have : NeZero typing.M := ⟨by norm_num [typing, typing0]⟩
  have : NeZero typing.L := ⟨by norm_num [typing, typing0]⟩
  exact ⟨ρ, νk, hρ.toFlatPreAt⟩

end Balaban.RootFSpine
