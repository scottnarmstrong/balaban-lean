/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.Activities
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The Root-F spine

`rootF_of_spine`: the statement of Root-F (`Balaban.logPartition_multiscale`, its body copied
verbatim) from the named inputs of `Balaban/Spine/RootFInputs.lean` (A1, A3, A4 (three parts), A6,
A7). Proved here (no other hypothesis):

* A1 (choice of the constants in Root-F's order): `δ`, then `L = Ty.L`, `M = Ty.M` and one `β₀` (the
  maximum of the thresholds of the inputs and `2`) for every `κ, c₉`, then `kf = k̂_f` from `ν`
  (`exists_isHorizon`, `IsHorizon.scale`); `k₀ ≤ k̂_f` (`kZero_le_of_isHorizon`);
* A5 (the flow induction, LFR Theorem IV.3.2 (b), (c)): `ρ₁` from A3, the steps `k → k+1` of `ℛ_k`
  for `k < k₀` (`class_flow`), the transfer at `k₀`, the frozen steps of `ℛ♭_k` until the running
  mass passes `7/8 L⁻²` (`frozen_flow`), with the normalization `∫ ρ_k = c Z(g)` carried along
  (`IntegralIsZ.step`); the flow stops by the horizon `k̂_f` (`stop_of_flatClassAt`, from the
  coefficient bounds (H.6) of the class and `c₈ q/(1 - q) ≤ 1/20`);
* A8 (the logarithm and the conversion): the exponential identity of `Z(g)/Z(0)` from the last
  integral (`ratio_eq_exp`), its transport to every admissible torus (`sideOf_eq`), and the clauses
  of Root-F for `activityTerm` (`rootFClauses_of_activities`, `Spine/Activities.lean`);
* A12: the assembly, in the two regimes `ν ≤ 7/8 L⁻²` (the flow, A3–A6) and `ν > 7/8 L⁻²` (A7). -/

@[expose] public section

namespace Balaban.RootFSpine

open MeasureTheory Balaban Balaban.Correlations Balaban.LargeField Balaban.LargeField.Def7
  Balaban.LargeField.Def7v2 Balaban.SmallField Balaban.SmallField.Def6v2

/-!
### The horizon `k̂_f` and the regime index `k₀`
-/

/-- The horizon exists: `k̂_f` is the least `k` with `ν L^{2k+2} ≥ 1`. -/
theorem exists_isHorizon {L : ℕ} (hL : 2 ≤ L) {ν : ℝ} (hν : 0 < ν) : ∃ kf, IsHorizon L ν kf := by
  classical
  have hL1 : (1 : ℝ) < L := by exact_mod_cast (by omega : 1 < L)
  have hex : ∃ k : ℕ, 1 ≤ ν * (L : ℝ) ^ (2 * k + 2) := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (1 / ν) hL1
    refine ⟨n, ?_⟩
    have h1 : (L : ℝ) ^ n ≤ (L : ℝ) ^ (2 * n + 2) := pow_le_pow_right₀ hL1.le (by omega)
    rw [div_lt_iff₀ hν] at hn
    nlinarith
  exact ⟨Nat.find hex, Nat.find_spec hex, fun k hk => not_le.1 (Nat.find_min hex hk)⟩

/-- The horizon satisfies Root-F's scale clauses `L^{kf} √ν ≤ L` and `1/2 ≤ L^{kf+1} √ν` (LFR Lemma
IV.5.1 (a)). -/
theorem IsHorizon.scale {L : ℕ} (hL : 2 ≤ L) {ν : ℝ} (hν : 0 < ν) (hν1 : ν ≤ 1) {kf : ℕ}
    (h : IsHorizon L ν kf) :
    (L : ℝ) ^ kf * Real.sqrt ν ≤ L ∧ 1 / 2 ≤ (L : ℝ) ^ (kf + 1) * Real.sqrt ν := by
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have hs0 : 0 ≤ Real.sqrt ν := Real.sqrt_nonneg ν
  have hs2 : Real.sqrt ν ^ 2 = ν := Real.sq_sqrt hν.le
  constructor
  · rcases Nat.eq_zero_or_pos kf with h0 | hpos
    · subst h0
      have : Real.sqrt ν ≤ 1 := Real.sqrt_le_one.2 hν1
      simp only [pow_zero, one_mul]
      linarith
    · obtain ⟨k, rfl⟩ : ∃ k, kf = k + 1 := ⟨kf - 1, by omega⟩
      have hk := h.2 k (by omega)
      set a : ℝ := (L : ℝ) ^ (k + 1) with ha
      have ha0 : 0 ≤ a := by positivity
      have hsq : (a * Real.sqrt ν) ^ 2 < 1 := by
        rw [mul_pow, hs2, ha, ← pow_mul]
        have : (k + 1) * 2 = 2 * k + 2 := by ring
        rw [this]
        linarith
      have hprod : a * Real.sqrt ν < 1 := by
        nlinarith [mul_nonneg ha0 hs0]
      linarith
  · set a : ℝ := (L : ℝ) ^ (kf + 1) with ha
    have ha0 : 0 ≤ a := by positivity
    have hsq : 1 ≤ (a * Real.sqrt ν) ^ 2 := by
      rw [mul_pow, hs2, ha, ← pow_mul]
      have : (kf + 1) * 2 = 2 * kf + 2 := by ring
      rw [this]
      linarith [h.1]
    nlinarith [mul_nonneg ha0 hs0]

/-- Below the stopping threshold (`ν L² ≤ 7/8`) the horizon is at least `1`. -/
theorem IsHorizon.one_le {L : ℕ} {ν : ℝ} (hν : ν * (L : ℝ) ^ 2 ≤ 7 / 8) {kf : ℕ}
    (h : IsHorizon L ν kf) : 1 ≤ kf := by
  by_contra h0
  have : kf = 0 := by omega
  have h1 := h.1
  rw [this] at h1
  norm_num at h1
  linarith

/-- The a priori regime index is at most the horizon (`k₀ < k_f ≤ k̂_f`, LFR Lemma IV.3.3 (b); here
only `β > 1`, `d ≥ 2` are used): `β ν L^{k d} ≤ 1` and `k ≥ k̂_f + 1` would give
`ν L^{2 k̂_f + 2} < 1`. -/
theorem kZero_le_of_isHorizon {d L : ℕ} (hd : 2 ≤ d) (hL : 2 ≤ L) {β ν : ℝ} (hβ : 1 < β)
    (hν : 0 < ν) {kf : ℕ} (h : IsHorizon L ν kf) : kZero d L β ν ≤ kf := by
  unfold kZero
  refine csSup_le' fun k hk => ?_
  have hk' : β * ν * (L : ℝ) ^ (k * d) ≤ 1 := hk
  by_contra hlt
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have hexp : 2 * kf + 2 ≤ k * d := by nlinarith [not_le.1 hlt]
  have hpow : (L : ℝ) ^ (2 * kf + 2) ≤ (L : ℝ) ^ (k * d) := pow_le_pow_right₀ hL1 hexp
  have h1 := h.1
  have hνL : 1 ≤ ν * (L : ℝ) ^ (k * d) := le_trans h1 (mul_le_mul_of_nonneg_left hpow hν.le)
  nlinarith

/-!
### The two inductions of the flow (LFR Theorem IV.3.2), in abstract form
-/

/-- **The steps below `k₀`** (A5, first part): a state at scale `1` and steps `k → k + 1` for
`1 ≤ k < k₀` give a state at every scale `1 ≤ k ≤ k₀`. -/
theorem class_flow {Dens : ℕ → Type*} {P : ∀ k, Dens k → ℝ → Prop} {k₀ : ℕ}
    (hbase : ∃ ρ νk, P 1 ρ νk)
    (hstep : ∀ k, 1 ≤ k → k < k₀ → ∀ ρ νk, P k ρ νk → ∃ ρ' νk', P (k + 1) ρ' νk') :
    ∀ k, 1 ≤ k → k ≤ k₀ → ∃ ρ νk, P k ρ νk := by
  intro k hk1 hk
  induction k with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0; exact hbase
    · obtain ⟨ρ, νk, hP⟩ := ih hpos (by omega)
      exact hstep n hpos (by omega) ρ νk hP

/-- **The frozen steps until the stop** (A5, second part): from a state at a scale
`max(k₀, 1) ≤ k ≤ kf`, frozen steps while the running mass is below the threshold, the stop at `kf`
and the last integral at the stopping scale give the conclusion. -/
theorem frozen_flow {Dens : ℕ → Type*} {P : ∀ k, Dens k → ℝ → Prop} {Stop : ℝ → Prop} {Q : Prop}
    {k₀ kf : ℕ}
    (hstep : ∀ k, 1 ≤ k → k₀ ≤ k → k < kf → ∀ ρ νk, P k ρ νk → ¬ Stop νk →
      ∃ ρ' νk', P (k + 1) ρ' νk')
    (hstop : ∀ ρ νk, P kf ρ νk → Stop νk)
    (hlast : ∀ k, 1 ≤ k → k ≤ kf → ∀ ρ νk, P k ρ νk → Stop νk → Q) :
    ∀ k, 1 ≤ k → k₀ ≤ k → k ≤ kf → ∀ ρ νk, P k ρ νk → Q := by
  suffices H : ∀ m k, kf - k = m → 1 ≤ k → k₀ ≤ k → k ≤ kf → ∀ ρ νk, P k ρ νk → Q from
    fun k hk1 hk0 hkf ρ νk hP => H _ k rfl hk1 hk0 hkf ρ νk hP
  intro m
  induction m with
  | zero =>
    intro k hm hk1 _ hkf ρ νk hP
    have hk : k = kf := by omega
    subst hk
    exact hlast k hk1 le_rfl ρ νk hP (hstop ρ νk hP)
  | succ n ih =>
    intro k hm hk1 hk0 hkf ρ νk hP
    by_cases hS : Stop νk
    · exact hlast k hk1 hkf ρ νk hP hS
    · obtain ⟨ρ', νk', hP'⟩ := hstep k hk1 hk0 (by omega) ρ νk hP hS
      exact ih (k + 1) (by omega) (by omega) (by omega) (by omega) ρ' νk' hP'

/-!
### The normalization along the flow
-/

section Normalization

variable {d N : ℕ} {T : Typing} {β ν a : ℝ} {h : EuclideanSpace ℝ (Fin N)} {K k : ℕ}
  [NeZero T.M] [NeZero T.L]

/-- `∫ ρ_k = c Z` and `∫ ρ_{k+1} = c' ∫ ρ_k` give `∫ ρ_{k+1} = c' c Z`. -/
theorem IntegralIsZ.step {ρ : 𝒟[d, N, T, β, a, K, k]} {ρ' : 𝒟[d, N, T, β, a, K, k + 1]}
    (hρ : IntegralIsZ d N T β ν a h K k ρ) (hs : IntegralStep d N T β a K k ρ ρ') :
    IntegralIsZ d N T β ν a h K (k + 1) ρ' := by
  obtain ⟨C, hC, hZ⟩ := hρ
  obtain ⟨C', hC', hI⟩ := hs
  refine ⟨fun nK => C' nK * C nK, fun nK => mul_pos (hC' nK) (hC nK), fun nK _ g hg => ?_⟩
  rw [hI nK g hg, hZ nK g hg]
  push_cast
  ring

end Normalization

/-!
### The exponential identity of `Z(g)/Z(0)` and its transport
-/

/-- From `I(g) = C Z(g)` with `C > 0` and `I(g) = exp(E + ⟨g, h⟩ + ∑_{j=1}^{J} ∑_X q_j(X; g))` on
the unit `ℓ¹` ball, with `q_j = 0` for `j ∉ [1, J]` and `J ≤ kf + 1`:
`Z(g)/Z(0) = exp(⟨g, h⟩ + ∑_{j=1}^{kf+1} ∑_X (q_j(X; g) - q_j(X; 0)))`. -/
theorem ratio_eq_exp {d N ℓ : ℕ} [NeZero ℓ] {Z I : (Torus d ℓ → Fin N → ℂ) → ℂ} {C : ℝ}
    (hC : 0 < C) {E : ℂ} {h : EuclideanSpace ℝ (Fin N)} {J kf : ℕ} (hJ : J ≤ kf + 1)
    {q : ℕ → Finset (Torus d ℓ) → (Torus d ℓ → Fin N → ℂ) → ℂ}
    (hq : ∀ j X g, j ∉ Finset.Icc 1 J → q j X g = q j X 0)
    (hI : ∀ g : Torus d ℓ → Fin N → ℂ, ∑ y, ∑ i, ‖g y i‖ < 1 → I g = (C : ℂ) * Z g)
    (hE : ∀ g : Torus d ℓ → Fin N → ℂ, ∑ y, ∑ i, ‖g y i‖ < 1 →
      I g = Complex.exp (E + ∑ x, ∑ i, g x i * (h i : ℂ)
        + ∑ j ∈ Finset.Icc 1 J, ∑ X, q j X g))
    (g : Torus d ℓ → Fin N → ℂ) (hg : ∑ y, ∑ i, ‖g y i‖ < 1) :
    Z g / Z 0 = Complex.exp (∑ x, ∑ i, g x i * (h i : ℂ)
      + ∑ j ∈ Finset.Icc 1 (kf + 1), ∑ X, (q j X g - q j X 0)) := by
  have h0 : ∑ y, ∑ i, ‖(0 : Torus d ℓ → Fin N → ℂ) y i‖ < 1 := by simp
  have hC' : (C : ℂ) ≠ 0 := by exact_mod_cast hC.ne'
  have hZ : ∀ g' : Torus d ℓ → Fin N → ℂ, ∑ y, ∑ i, ‖g' y i‖ < 1 →
      Z g' = Complex.exp (E + ∑ x, ∑ i, g' x i * (h i : ℂ)
        + ∑ j ∈ Finset.Icc 1 J, ∑ X, q j X g') / (C : ℂ) := by
    intro g' hg'
    rw [← hE g' hg', hI g' hg']
    field_simp
  -- extend the sum of the increments over scales from `[1, J]` to `[1, kf + 1]`
  have hext : ∑ j ∈ Finset.Icc 1 J, ∑ X, (q j X g - q j X 0) =
      ∑ j ∈ Finset.Icc 1 (kf + 1), ∑ X, (q j X g - q j X 0) :=
    Finset.sum_subset (Finset.Icc_subset_Icc le_rfl hJ) fun j _ hj =>
      Finset.sum_eq_zero fun X _ => by rw [hq j X g hj, sub_self]
  rw [hZ g hg, hZ 0 h0, div_div_div_cancel_right₀ hC', ← Complex.exp_sub, ← hext]
  congr 1
  simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero, Finset.sum_sub_distrib]
  ring

/-- The torus of the family with `n_K = q` top cubes is the admissible torus `M L^{kf+1} q`. -/
theorem sideOf_eq (M L kf q : ℕ) :
    M * sides L (kf + 1) q (kf + 1) * L ^ (kf + 1) = M * L ^ (kf + 1) * q := by
  simp only [sides, Nat.sub_self, pow_zero, mul_one]
  ring

/-!
### The stop of the flow by the horizon (LFR Lemma IV.5.1 (b))
-/

/-- **The flow stops by the horizon** (LFR Lemma IV.5.1 (b), Lemma I.5.6 (a): `k_f ≤ k̂_f`): a
member of `ℛ♭_{k̂_f}` has `ν_{k̂_f} > 7/8 L⁻²`. By (I.2) up to the scale `k̂_f` (`RunningHypTo`, a
clause of `FlatClassAt`) `ν_{k̂_f} = ν L^{2 k̂_f} δ` with `|log δ| ≤ 1/20`, so `δ ≥ 19/20`, and
`ν L^{2 k̂_f + 2} ≥ 1`. -/
theorem stop_of_flatClassAt {d N : ℕ} {T : Typing} {P6 : Def6.Consts} {C7 : Consts7}
    {PB : BudgetConsts} {cs₀ : OpConsts} {M1 c : ℕ} {rH ϱ β ν : ℝ}
    {h : EuclideanSpace ℝ (Fin N)} {kf : ℕ} [NeZero T.M] [NeZero T.L]
    (hkf : IsHorizon T.L ν kf) {ρ : 𝒟[d, N, T, β, cs₀.aKer, kf + 1, kf]} {νk : ℝ}
    (hρ : FlatClassAt d N T P6 C7 PB cs₀ M1 c rH ϱ β ν h kf kf ρ νk) :
    7 / 8 < νk * (T.L : ℝ) ^ 2 := by
  obtain ⟨_, _, _, _, _, _, F, _, _, _, _, _, _, _, _, _, _, _, _, _, hνk, hrun, -⟩ := hρ
  obtain ⟨-, -, -, -, -, -, -, -, -, hnu⟩ := hrun
  obtain ⟨δ', hδ0, hδlog, hνeq⟩ := hnu kf le_rfl
  have hδ : 19 / 20 ≤ δ' := by
    have h1 : -(1 / 20 : ℝ) ≤ Real.log δ' := by
      have := neg_abs_le (Real.log δ')
      linarith
    have h2 := LargeField.StopIndex.exp_neg_eps_ge (ε := 1 / 20) le_rfl
    calc (19 / 20 : ℝ) ≤ Real.exp (-(1 / 20)) := h2
      _ ≤ Real.exp (Real.log δ') := Real.exp_le_exp.2 h1
      _ = δ' := Real.exp_log hδ0
  have hH : 1 ≤ ν * (T.L : ℝ) ^ (2 * kf) * (T.L : ℝ) ^ 2 := by
    rw [mul_assoc, ← pow_add]
    exact hkf.1
  rw [← hνk, hνeq]
  nlinarith [mul_nonneg (sub_nonneg.2 hH) (sub_nonneg.2 hδ)]

/-!
### The assembly
-/

/-- The ranges `2 ≤ L` and `1 ≤ M` of Root-F from the prefix (`L ≥ 3`, `M = c M₁`, `c ≥ 14`,
`M₁ ≥ 1`). -/
theorem prefix_ranges {d : ℕ} {δ : ℝ} {Ty : ℝ → ℝ → Typing} {P6 : ℝ → ℝ → Def6.Consts}
    {C7 : ℝ → ℝ → Consts7} {PB : ℝ → ℝ → BudgetConsts} {cs₀ : ℝ → ℝ → OpConsts}
    {M1 c : ℝ → ℝ → ℕ} {ϱ : ℝ → ℝ → ℝ}
    (hA1 : PrefixInput d δ Ty P6 C7 PB cs₀ M1 c ϱ) {κ : ℝ} (hκ : 0 < κ) {c₉ : ℝ} (hc₉ : 0 < c₉) :
    2 ≤ (Ty κ c₉).L ∧ 1 ≤ (Ty κ c₉).M := by
  obtain ⟨hL3, -, -, -, hMc, hc14, hM11, -⟩ := hA1 κ hκ c₉ hc₉
  refine ⟨by omega, ?_⟩
  rw [hMc]
  have := Nat.mul_le_mul hc14 hM11
  omega

/-- **The Root-F spine, for one pair `κ, c₉`.** From the named inputs of
`Balaban/Spine/RootFInputs.lean` at the constants `δ, Ty, P6, C7, PB, cs₀, M1, c, rH, ϱ` of the
prefix (A1 `PrefixInput`, A3 `BaseStepInput`, A4 `ClassStepInput`, `TransferInput`,
`FrozenStepInput`, A6 `LastIntegralInput`, A7 `KfZeroInput`): there is `β₀` such that for every
`β ≥ β₀`, `ν ∈ (0, 1]` and unit `h` the horizon `kf = k̂_f` satisfies the scale clauses and Root-F's
clauses `RootFClauses` hold with `L = Ty.L`, `M = Ty.M` (at `κ, c₉`), for the terms `activityTerm`
of the activities of the last integral (`ν ≤ 7/8 L⁻²`) or of A7 (`ν > 7/8 L⁻²`). -/
theorem rootF_clauses_of_spine (d N : ℕ) (hd : 3 ≤ d) (hN : 2 ≤ N) (δ : ℝ)
    (Ty : ℝ → ℝ → Typing) (P6 : ℝ → ℝ → Def6.Consts) (C7 : ℝ → ℝ → Consts7)
    (PB : ℝ → ℝ → BudgetConsts) (cs₀ : ℝ → ℝ → OpConsts) (M1 c : ℝ → ℝ → ℕ)
    (rH ϱ : ℝ → ℝ → ℝ)
    (hA1 : PrefixInput d δ Ty P6 C7 PB cs₀ M1 c ϱ)
    (hA3 : BaseStepInput d N Ty P6 C7 PB cs₀ M1 c rH ϱ)
    (hA4 : ClassStepInput d N Ty P6 C7 PB cs₀ M1 c rH ϱ)
    (hA4t : TransferInput d N Ty P6 C7 PB cs₀ M1 c rH ϱ)
    (hA4f : FrozenStepInput d N Ty P6 C7 PB cs₀ M1 c rH ϱ)
    (hA6 : LastIntegralInput d N δ Ty P6 C7 PB cs₀ M1 c rH ϱ)
    (hA7 : KfZeroInput d N δ Ty) (κ : ℝ) (hκ : 0 < κ) (c₉ : ℝ) (hc₉ : 0 < c₉) :
    ∃ β₀ : ℝ, ∀ β : ℝ, β₀ ≤ β →
    ∀ ν : ℝ, 0 < ν → ν ≤ 1 → ∀ h : EuclideanSpace ℝ (Fin N), ‖h‖ = 1 →
    ∃ kf : ℕ, ((Ty κ c₉).L : ℝ) ^ kf * Real.sqrt ν ≤ (Ty κ c₉).L ∧
      1 / 2 ≤ ((Ty κ c₉).L : ℝ) ^ (kf + 1) * Real.sqrt ν ∧
      ∃ T : RootFFamily d N, RootFClauses d N (Ty κ c₉).L (Ty κ c₉).M β ν h kf κ c₉ δ T := by
  have : NeZero N := ⟨by omega⟩
  obtain ⟨hL2, hM1⟩ := prefix_ranges hA1 hκ hc₉
  have : NeZero (Ty κ c₉).L := ⟨by omega⟩
  have : NeZero (Ty κ c₉).M := ⟨by omega⟩
  obtain ⟨β₃, hβ₃⟩ := hA3 κ hκ c₉ hc₉
  obtain ⟨β₄, hβ₄⟩ := hA4 κ hκ c₉ hc₉
  obtain ⟨β₄t, hβ₄t⟩ := hA4t κ hκ c₉ hc₉
  obtain ⟨β₄f, hβ₄f⟩ := hA4f κ hκ c₉ hc₉
  obtain ⟨β₆, hβ₆⟩ := hA6 κ hκ c₉ hc₉
  obtain ⟨β₇, hβ₇⟩ := hA7 κ hκ c₉ hc₉
  refine ⟨max 2 (max β₃ (max β₄ (max β₄t (max β₄f (max β₆ β₇))))), ?_⟩
  intro β hβ ν hν0 hν1 h hh
  simp only [max_le_iff] at hβ
  obtain ⟨hβ2, hβ₃', hβ₄', hβ₄t', hβ₄f', hβ₆', hβ₇'⟩ := hβ
  obtain ⟨kf, hkf⟩ := exists_isHorizon hL2 hν0
  obtain ⟨hsc1, hsc2⟩ := hkf.scale hL2 hν0 hν1
  refine ⟨kf, hsc1, hsc2, ?_⟩
  -- the activities and the exponential identity on every admissible torus
  suffices H : ∃ (J : ℕ) (p : (ℓ : ℕ) → ℕ → Finset (Torus d ℓ) → (Torus d ℓ → Fin N → ℂ) → ℂ),
      ObservableActivities d N (Ty κ c₉).L (Ty κ c₉).M κ c₉ δ J kf p ∧
      ∀ (ℓ : ℕ) [NeZero ℓ], (Ty κ c₉).M * (Ty κ c₉).L ^ (kf + 1) ∣ ℓ →
        ∀ g : Torus d ℓ → Fin N → ℂ, ∑ y, ∑ i, ‖g y i‖ < 1 →
          partitionFunction d N ℓ β ν h g / partitionFunction d N ℓ β ν h 0 =
            Complex.exp (∑ x, ∑ i, g x i * (h i : ℂ)
              + ∑ j ∈ Finset.Icc 1 (kf + 1), ∑ X : Finset (Torus d ℓ),
                (p ℓ j X g - p ℓ j X 0)) by
    obtain ⟨J, p, hobs, hexp⟩ := H
    exact ⟨_, rootFClauses_of_activities hc₉ hobs hexp⟩
  by_cases hflow : ν * ((Ty κ c₉).L : ℝ) ^ 2 ≤ 7 / 8
  · -- the flow (A3–A6)
    have hkf1 : 1 ≤ kf := hkf.one_le hflow
    have hk₀kf : kZero d (Ty κ c₉).L β ν ≤ kf :=
      kZero_le_of_isHorizon (by omega) hL2 (by linarith) hν0 hkf
    have hbase := hβ₃ β hβ₃' ν hν0 hflow h hh kf hkf
    have hstepA := hβ₄ β hβ₄' ν hν0 hflow h hh kf hkf
    have htrans := hβ₄t β hβ₄t' ν hν0 hflow h hh kf hkf
    have hstepB := hβ₄f β hβ₄f' ν hν0 hflow h hh kf hkf
    have hlast := hβ₆ β hβ₆' ν hν0 hflow h hh kf hkf
    generalize kZero d (Ty κ c₉).L β ν = k₀ at hk₀kf hbase hstepA htrans hstepB
    -- the state of the frozen regime at the scale `max k₀ 1`
    have hstart : ∃ (ρ : 𝒟[d, N, Ty κ c₉, β, (cs₀ κ c₉).aKer, kf + 1, max k₀ 1]) (νk : ℝ),
        FlatClassAt d N (Ty κ c₉) (P6 κ c₉) (C7 κ c₉) (PB κ c₉) (cs₀ κ c₉) (M1 κ c₉) (c κ c₉)
          (rH κ c₉) (ϱ κ c₉) β ν h kf (max k₀ 1) ρ νk ∧
        IntegralIsZ d N (Ty κ c₉) β ν (cs₀ κ c₉).aKer h (kf + 1) (max k₀ 1) ρ := by
      rcases Nat.eq_zero_or_pos k₀ with h0 | hpos
      · subst h0
        exact hbase.2 rfl
      · have hmax : max k₀ 1 = k₀ := max_eq_left hpos
        rw [hmax]
        obtain ⟨ρ, νk, hR, hZ⟩ := class_flow
          (Dens := fun k => 𝒟[d, N, Ty κ c₉, β, (cs₀ κ c₉).aKer, kf + 1, k])
          (P := fun k (ρ : 𝒟[d, N, Ty κ c₉, β, (cs₀ κ c₉).aKer, kf + 1, k]) νk =>
            RepClassAt d N (Ty κ c₉) (P6 κ c₉) (C7 κ c₉) (PB κ c₉) (cs₀ κ c₉) (M1 κ c₉)
              (c κ c₉) (rH κ c₉) (ϱ κ c₉) β ν h kf k ρ νk ∧
            IntegralIsZ d N (Ty κ c₉) β ν (cs₀ κ c₉).aKer h (kf + 1) k ρ) (k₀ := k₀)
          (hbase.1 hpos)
          (fun k hk1 hk ρ νk hP => by
            obtain ⟨ρ', νk', hR', hS⟩ := hstepA k hk1 hk ρ νk hP.1
            exact ⟨ρ', νk', hR', hP.2.step hS⟩)
          k₀ hpos le_rfl
        exact ⟨ρ, νk, htrans hpos ρ νk hR, hZ⟩
    obtain ⟨ρ₀, νk₀, hF₀, hZ₀⟩ := hstart
    refine frozen_flow
      (Dens := fun k => 𝒟[d, N, Ty κ c₉, β, (cs₀ κ c₉).aKer, kf + 1, k])
      (P := fun k (ρ : 𝒟[d, N, Ty κ c₉, β, (cs₀ κ c₉).aKer, kf + 1, k]) νk =>
        FlatClassAt d N (Ty κ c₉) (P6 κ c₉) (C7 κ c₉) (PB κ c₉) (cs₀ κ c₉) (M1 κ c₉)
          (c κ c₉) (rH κ c₉) (ϱ κ c₉) β ν h kf k ρ νk ∧
        IntegralIsZ d N (Ty κ c₉) β ν (cs₀ κ c₉).aKer h (kf + 1) k ρ)
      (Stop := fun νk => 7 / 8 < νk * ((Ty κ c₉).L : ℝ) ^ 2) (k₀ := k₀) (kf := kf)
      (fun k hk1 hk0 hk ρ νk hP hS => by
        obtain ⟨ρ', νk', hF', hS'⟩ := hstepB k hk1 hk0 hk ρ νk hP.1 (not_lt.1 hS)
        exact ⟨ρ', νk', hF', hP.2.step hS'⟩)
      (fun ρ νk hP => stop_of_flatClassAt hkf hP.1)
      (fun k hk1 hk ρ νk hP hS => ?_)
      (max k₀ 1) (le_max_right _ _) (le_max_left _ _) (max_le hk₀kf hkf1) ρ₀ νk₀ ⟨hF₀, hZ₀⟩
    -- the last integral at the stopping scale `k`
    obtain ⟨p, E, hobs, hint⟩ := hlast k hk1 hk ρ νk hP.1 hS
    obtain ⟨C, hC, hZ⟩ := hP.2
    refine ⟨k + 1, p, hobs, fun ℓ _ hℓ g hg => ?_⟩
    obtain ⟨q, hq⟩ := hℓ
    have hq0 : q ≠ 0 := by
      rintro rfl
      exact NeZero.ne ℓ (by rw [hq]; simp)
    have : NeZero q := ⟨hq0⟩
    have hside : (Ty κ c₉).M * sides (Ty κ c₉).L (kf + 1) q (kf + 1) * (Ty κ c₉).L ^ (kf + 1)
        = ℓ := by
      rw [hq]; exact sideOf_eq _ _ kf q
    -- the identity on the torus of the family with `n_K = q`, then transported to `ℓ`
    have hadm : (Ty κ c₉).M * (Ty κ c₉).L ^ (kf + 1) ∣
        (Ty κ c₉).M * sides (Ty κ c₉).L (kf + 1) q (kf + 1) * (Ty κ c₉).L ^ (kf + 1) := by
      rw [sideOf_eq]; exact dvd_mul_right _ _
    have key := ratio_eq_exp (C := C q) (hC q) (E := E q) (J := k + 1) (kf := kf) (by omega)
      (I := fun g => ∫ ψ, ρ q ψ (fun xi => g xi.1 xi.2))
      (Z := partitionFunction d N
        ((Ty κ c₉).M * sides (Ty κ c₉).L (kf + 1) q (kf + 1) * (Ty κ c₉).L ^ (kf + 1)) β ν h)
      (fun j X g hj => (hobs.1 _ hadm).1 j X (fun h' => hj h'.1) g)
      (fun g hg => hZ q (fun xi => g xi.1 xi.2) (by
        show ∑ xi : _ × Fin N, ‖g xi.1 xi.2‖ < 1
        rw [Fintype.sum_prod_type]
        exact hg))
      (fun g hg => hint q (fun xi => g xi.1 xi.2) (by
        show ∑ xi : _ × Fin N, ‖g xi.1 xi.2‖ < 1
        rw [Fintype.sum_prod_type]
        exact hg))
    subst hside
    exact key g hg
  · -- the case `k_f = 0` (A7)
    have hflow' : 7 / 8 < ν * ((Ty κ c₉).L : ℝ) ^ 2 := not_le.1 hflow
    obtain ⟨p, E, hobs, hZ⟩ := hβ₇ β hβ₇' ν hflow' hν1 h hh kf hkf
    refine ⟨1, p, hobs, fun ℓ _ hℓ g hg => ?_⟩
    refine ratio_eq_exp (C := 1) one_pos (E := E ℓ) (J := 1) (kf := kf) (by omega)
      (I := partitionFunction d N ℓ β ν h)
      (fun j X g hj => (hobs.1 ℓ hℓ).1 j X (fun h' => hj h'.1) g)
      (fun g _ => by simp) (fun g hg => ?_) g hg
    rw [hZ ℓ hℓ g hg]
    simp

/-- **The Root-F spine.** Root-F (the body of `Balaban.logPartition_multiscale`, verbatim) from the
named inputs of `Balaban/Spine/RootFInputs.lean` at the constants
`δ, Ty, P6, C7, PB, cs₀, M1, c, rH, ϱ` of the prefix: A1 `PrefixInput`, A3 `BaseStepInput`, A4
`ClassStepInput`, `TransferInput`, `FrozenStepInput`, A6 `LastIntegralInput`, A7 `KfZeroInput`.
Root-F's `L, M` are `Ty.L, Ty.M` (at `κ, c₉`), its `kf` is the horizon `k̂_f`, and its terms are
`activityTerm` of the activities of the last integral (`ν ≤ 7/8 L⁻²`) or of A7 (`ν > 7/8 L⁻²`)
(`rootF_clauses_of_spine`). -/
theorem rootF_of_spine (d N : ℕ) (hd : 3 ≤ d) (hN : 2 ≤ N) (δ : ℝ) (hδ : 0 < δ)
    (Ty : ℝ → ℝ → Typing) (P6 : ℝ → ℝ → Def6.Consts) (C7 : ℝ → ℝ → Consts7)
    (PB : ℝ → ℝ → BudgetConsts) (cs₀ : ℝ → ℝ → OpConsts) (M1 c : ℝ → ℝ → ℕ)
    (rH ϱ : ℝ → ℝ → ℝ)
    (hA1 : PrefixInput d δ Ty P6 C7 PB cs₀ M1 c ϱ)
    (hA3 : BaseStepInput d N Ty P6 C7 PB cs₀ M1 c rH ϱ)
    (hA4 : ClassStepInput d N Ty P6 C7 PB cs₀ M1 c rH ϱ)
    (hA4t : TransferInput d N Ty P6 C7 PB cs₀ M1 c rH ϱ)
    (hA4f : FrozenStepInput d N Ty P6 C7 PB cs₀ M1 c rH ϱ)
    (hA6 : LastIntegralInput d N δ Ty P6 C7 PB cs₀ M1 c rH ϱ)
    (hA7 : KfZeroInput d N δ Ty) :
    ∃ δ : ℝ, 0 < δ ∧
    ∀ κ : ℝ, 0 < κ → ∀ c₉ : ℝ, 0 < c₉ →
    ∃ L M : ℕ, 2 ≤ L ∧ 1 ≤ M ∧ ∃ β₀ : ℝ, ∀ β : ℝ, β₀ ≤ β →
    ∀ ν : ℝ, 0 < ν → ν ≤ 1 → ∀ h : EuclideanSpace ℝ (Fin N), ‖h‖ = 1 →
    ∃ kf : ℕ, (L : ℝ) ^ kf * Real.sqrt ν ≤ L ∧ 1 / 2 ≤ (L : ℝ) ^ (kf + 1) * Real.sqrt ν ∧
    ∃ T : (ℓ : ℕ) → ℕ → Torus d ℓ → Finset (Torus d ℓ) → (Torus d ℓ → Fin N → ℂ) →
        (Fin N → ℂ),
      (∀ (ℓ : ℕ) [NeZero ℓ], M * L ^ (kf + 1) ∣ ℓ →
        (∀ j x X, ¬ (j ∈ Finset.Icc 1 (kf + 1) ∧ x ∈ X ∧ IsPolymer d ℓ (M * L ^ j) X) →
          T ℓ j x X = 0) ∧
        (∀ j x X (g g' : Torus d ℓ → Fin N → ℂ), (∀ y ∈ X, g y = g' y) →
          T ℓ j x X g = T ℓ j x X g') ∧
        (∀ j x X, AnalyticOnNhd ℂ (T ℓ j x X) {g | ∑ y, ∑ i, ‖g y i‖ < 1}) ∧
        (∀ j ∈ Finset.Icc 1 (kf + 1), ∀ x X (g : Torus d ℓ → Fin N → ℂ),
          ∑ y, ∑ i, ‖g y i‖ ≤ 1 / 2 →
          ‖T ℓ j x X g‖ ≤ c₉ * (L : ℝ) ^ (-((j : ℝ) * (((d : ℝ) - 2) / 2 + δ)))
            * Real.exp (-κ * (X.card : ℝ) / ((M : ℝ) * (L : ℝ) ^ j) ^ d)) ∧
        ∀ g : Torus d ℓ → Fin N → ℂ, ∑ y, ∑ i, ‖g y i‖ < 1 →
          Complex.log (partitionFunction d N ℓ β ν h g / partitionFunction d N ℓ β ν h 0) =
            ∑ x, ∑ i, g x i * (h i : ℂ)
              + ∑ j ∈ Finset.Icc 1 (kf + 1), ∑ x, ∑ X : Finset (Torus d ℓ), ∑ i,
                  g x i * T ℓ j x X g i) ∧
      ∀ (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ'], M * L ^ (kf + 1) ∣ ℓ → M * L ^ (kf + 1) ∣ ℓ' →
        ∀ (j : ℕ) (a : Fin d → ℤ) (A : Finset (Fin d → ℤ)) (g : (Fin d → ℤ) → Fin N → ℂ),
          a ∈ A → (∀ y ∈ A, ∀ μ, 4 * |y μ| < (ℓ : ℤ) ∧ 4 * |y μ| < (ℓ' : ℤ)) →
          T ℓ j (fun μ => (a μ : ZMod ℓ)) (A.image fun y μ => (y μ : ZMod ℓ))
              (fun z => g fun μ => ZMod.valMinAbs (n := ℓ) (z μ)) =
            T ℓ' j (fun μ => (a μ : ZMod ℓ')) (A.image fun y μ => (y μ : ZMod ℓ'))
              (fun z => g fun μ => ZMod.valMinAbs (n := ℓ') (z μ)) := by
  refine ⟨δ, hδ, fun κ hκ c₉ hc₉ => ?_⟩
  obtain ⟨hL2, hM1⟩ := prefix_ranges hA1 hκ hc₉
  exact ⟨(Ty κ c₉).L, (Ty κ c₉).M, hL2, hM1, rootF_clauses_of_spine d N hd hN δ Ty P6 C7 PB cs₀
    M1 c rH ϱ hA1 hA3 hA4 hA4t hA4f hA6 hA7 κ hκ c₉ hc₉⟩


end Balaban.RootFSpine
