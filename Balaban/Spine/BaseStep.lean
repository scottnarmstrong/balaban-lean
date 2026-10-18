/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.ClassStep
public import Balaban.LargeField.Base.BasePhysicalDensity

/-!
# The base step of the spine from its sub-inputs

`baseStepInput_of_parts` proves the spine input `BaseStepInput` (A3, LF-6,
`Spine/RootFInputs.lean`) following LFR §II.7 (Theorem II.7.10). The density of the first step is
the physical one (LFR (II.7.1); P4 (2.42); P1 (1.11) at `λ = ∞`):
`ρ₁(ψ₁; g) = z₁^{N|T^{(1)}|} ∫ ∏_y t₀(z₁ ψ₁(y), (Qφ)(y)) e^{-β H(φ) + ⟨g, φ⟩} dσ(φ)`, the landed
`baseRho1` read on the tori of the family (`firstDensity`). Its integral is `Z(g)` (Theorem II.7.10
(a)); this is proved here from the landed exact starting identity `basePhysicalDensity`
(`integralIsZ_firstDensity`). What is asserted of `ρ₁` is its membership in the class at the scale
`1` (Theorem II.7.10 (b)–(d)), in the two regimes of LFR §II.7.1:

* `BasePreStepInput` (regime (A), `k₀ ≥ 1`; LFR Definition II.7.6, Lemmas II.7.7, II.7.8,
  Proposition II.7.9, Theorem II.7.10 (b)–(d) before the operation `R`): for some field
  renormalization `z₁ > 0`, `ρ₁` is a member of the pre-`R` class `ℛ^pre_1` (`PreClassAt` with
  (I.2) at the scale `0`): the base records and the base kernels `K₀(Z'), b₀(Z')` as step data;
  the small-field data of the first step (ν-free backgrounds, the ν-free renormalization system)
  with the boundary terms `ℬ^{(1)}` of rate `3κ/2` and constant `B_st` and `ℛ^{(1)}_m` bounded by
  `½ β₁^{-m-1}` (the form in which Proposition II.7.9 states them); the budget (H6′)^pre; `β_0 = β`,
  `ν_0 = ν`; the torus coherence (D8) (Theorem II.7.10 (d): every datum is the same formula on
  `ℤ^d`).
* `BaseFlatStepInput` (regime (B), `k₀ = 0`; the same sources, with complete backgrounds and
  P4's renormalization system): for some `z₁ > 0`, `ρ₁` is a member of `ℛ♭_1` (`FlatClassAt`, with
  its mass bound `ν₁ ≤ 9/10`).

In regime (A) the output of the first step enters the class `ℛ_1` through the operation `R` at the
scale `1` and the coefficient step, which are the sub-inputs `RInput` and `FlowRateInput` of the
class step (`Spine/ClassStep.lean`), used here at `k = 1`: (H.6) at the scale `1` (a clause of
`ℛ^pre_1`) gives (I.2) at the scale `1` (`PreClassAt.succ`), and `R` at the scale `1 ≤ k₀` gives a
member of `ℛ_1` with the same integral. (At the scale `1` no component is ripe, LFR Lemma II.7.2
(c), so the operation `R` keeps the density; `RInput` asserts only a member with the same integral.)

The sub-inputs are spine-local; the list and the status of each are in `notes/phase1/SPINE.md`,
section "BaseStepInput sub-inputs". The two new ones need the exemption of the seven inputs (rule
10): their truth is the open work of the base case (blocker 1). -/

@[expose] public section

namespace Balaban.RootFSpine

open MeasureTheory Balaban Balaban.LargeField Balaban.LargeField.Def7 Balaban.LargeField.Def7v2
  Balaban.SmallField Balaban.SmallField.Def6v2

/-!
### The density of the first step
-/

section Density

/-- **The density of the first step on a fine torus of side `ℓ = L n`** (LFR (II.7.1)): the landed
`baseRho1` on the coarse torus `𝕋_n` of the `1`-blocks, with the source `g` of the fine torus
`𝕋_ℓ` read on `𝕋_{L n}` through `ℓ = L n`:
`ρ₁(ψ; g) = z₁^{N|𝕋_n|} ∫ ∏_y t₀(z₁ ψ(y), (Qφ)(y)) e^{-β H(φ) + ⟨g, φ⟩} dσ(φ)`, with the Gaussian
kernel `t₀` of constant `β a L^{d-2}`. -/
noncomputable def firstDensityAt (d N L : ℕ) [NeZero L] {n ℓ : ℕ} [NeZero n] (hℓ : L * n = ℓ)
    (β a z₁ ν : ℝ) (h : EuclideanSpace ℝ (Fin N)) (ψ : Torus d n → EuclideanSpace ℝ (Fin N))
    (g : Torus d ℓ → Fin N → ℂ) : ℂ :=
  baseRho1 d N L n β a z₁ ν h ψ (fun x => g (cast (congrArg (Torus d) hℓ) x))

/-- **`∫ ρ₁ dψ₁ = Z(g)`** (LFR Theorem II.7.10 (a), (II.7.1)): the landed exact starting identity
`basePhysicalDensity`, read on the fine torus of side `ℓ = L n`. -/
theorem integral_firstDensityAt {d N L : ℕ} [NeZero L] [NeZero N] {n ℓ : ℕ} [NeZero n]
    [NeZero ℓ] (hℓ : L * n = ℓ) {β a z₁ ν : ℝ} (hβ : 0 < β) (ha : 0 < a) (hz : 0 < z₁)
    (h : EuclideanSpace ℝ (Fin N)) (g : Torus d ℓ → Fin N → ℂ) :
    ∫ ψ, firstDensityAt d N L hℓ β a z₁ ν h ψ g ∂(Measure.pi fun _ => volume) =
      partitionFunction d N ℓ β ν h g := by
  subst hℓ
  exact (basePhysicalDensity hβ ha hz h g).symm

/-- The fine torus of the family at the horizon `K = kf + 1` (side `ℓ = M n_K L^K`) is `L` times
the torus of its `1`-blocks (side `M n_K L^{K-1}`). -/
theorem firstSide_eq (L M nK kf : ℕ) :
    L * (M * sides L (kf + 1) nK (kf + 1) * L ^ (kf + 1 - 1)) =
      M * sides L (kf + 1) nK (kf + 1) * L ^ (kf + 1) := by
  rw [Nat.add_sub_cancel, pow_succ]
  ring

/-- **The density of the first step on the tori of the family** (LFR (II.7.1)): on the torus with
`n_K` top cubes, `ρ₁ = firstDensityAt` with the field `ψ₁` of the `1`-blocks and the source
`g : 𝕋_ℓ × {1, …, N} → ℂ` of the fine torus, `ℓ = M n_K L^K`, `K = kf + 1`. The kernel constant is
`a`, the field renormalization `z₁`. -/
noncomputable def firstDensity (d N : ℕ) (T : Typing) (β a z₁ ν : ℝ)
    (h : EuclideanSpace ℝ (Fin N)) (kf : ℕ) [NeZero T.M] [NeZero T.L] :
    𝒟[d, N, T, β, a, kf + 1, 1] :=
  fun nK _ ψ g => firstDensityAt d N T.L (firstSide_eq T.L T.M nK kf) β a z₁ ν h ψ
    (fun x i => g (x, i))

/-- **The normalization of the first step** (LFR Theorem II.7.10 (a)): on every torus of the
family, `∫ ρ₁ dψ₁ = Z(g)`, i.e. `IntegralIsZ` with the constant `1`. -/
theorem integralIsZ_firstDensity {d N : ℕ} [NeZero N] {T : Typing} {β a z₁ ν : ℝ}
    {h : EuclideanSpace ℝ (Fin N)} {kf : ℕ} [NeZero T.M] [NeZero T.L] (hβ : 0 < β) (ha : 0 < a)
    (hz : 0 < z₁) : IntegralIsZ d N T β ν a h (kf + 1) 1 (firstDensity d N T β a z₁ ν h kf) := by
  refine ⟨fun _ => 1, fun _ => one_pos, fun nK _ g _ => ?_⟩
  rw [Complex.ofReal_one, one_mul]
  exact integral_firstDensityAt (firstSide_eq T.L T.M nK kf) hβ ha hz h (fun x i => g (x, i))

/-- The normalization passes to a density with the same integrals. -/
theorem IntegralIsZ.of_integral_eq {d N : ℕ} {T : Typing} {β ν a : ℝ}
    {h : EuclideanSpace ℝ (Fin N)} {K k : ℕ} [NeZero T.M] [NeZero T.L]
    {ρ ρ' : 𝒟[d, N, T, β, a, K, k]} (hρ : IntegralIsZ d N T β ν a h K k ρ)
    (he : ∀ (nK : ℕ) [NeZero nK] (g : GIdx 𝒮[d, T, β, a] (sides T.L K nK) T.M K N → ℂ),
      g ∈ l1Ball _ → ∫ ψ, ρ' nK ψ g = ∫ ψ, ρ nK ψ g) :
    IntegralIsZ d N T β ν a h K k ρ' := by
  obtain ⟨C, hC, hZ⟩ := hρ
  exact ⟨C, hC, fun nK _ g hg => by rw [he nK g hg, hZ nK g hg]⟩

/-- A unit vector of `ℝ^N` forces `N ≠ 0`. -/
theorem neZero_of_norm_eq_one {N : ℕ} {h : EuclideanSpace ℝ (Fin N)} (hh : ‖h‖ = 1) :
    NeZero N := by
  refine ⟨fun hN => ?_⟩
  subst hN
  rw [Subsingleton.elim h 0, norm_zero] at hh
  exact zero_ne_one hh

end Density

/-!
### The sub-inputs
-/

section Inputs

variable (d N : ℕ) (T : ℝ → ℝ → Typing) (P6 : ℝ → ℝ → Def6.Consts)
  (C7 : ℝ → ℝ → Consts7) (PB : ℝ → ℝ → BudgetConsts) (cs₀ : ℝ → ℝ → OpConsts)
  (M1 c : ℝ → ℝ → ℕ) (rH ϱ : ℝ → ℝ → ℝ)

/-- **A3-1, the first step in regime (A) before `R` (LF-6; LFR Definition II.7.6, Lemmas II.7.7 and
II.7.8, Proposition II.7.9, Theorem II.7.10 (b)–(d); P4 (2.42)–(2.54), pp. 691–694; P5 p. 487 and
(2.47), P6 (3.2) at `k = 0`).** For `β ≥ β₀`, `0 < ν ≤ 7/8 L⁻²`, every unit field `h`, the horizon
`kf = k̂_f` and `k₀ ≥ 1`: for some field renormalization `z₁ > 0`, the density of the first step
`ρ₁` (`firstDensity`, kernel constant `a`) is a member of the pre-`R` class `ℛ^pre_1` with (I.2) at
the scale `0` (`PreClassAt … kf 1 0`). Its representation: all admissible histories up to the scale
`1` (the base records `(𝖯₁, 𝖰₁, 𝖱₁, 𝖲₁)`, Lemma II.7.2); the base kernels `K₀(Z')` of (II.7.4) and
boundary factors `b₀(Z')` (Definition II.7.6) as step data, with (S0)–(S5) and the bound (II.7.5)
with the gain `κ^{(0)}` from the level-0 threshold (Lemmas II.7.7, II.7.8; P5 (1.31) for the first
components); the small-field data of the first step on `Z^c_1` (hemisphere charts around the
background, the covariance `C^{(0)}`, the chart Jacobian; ν-free backgrounds and the ν-free
renormalization system), with (H.6) at the scale `1`, the boundary terms `ℬ^{(1)}` of rate `3κ/2`
and constant `B_st`, and `ℛ^{(1)}_m` bounded by `½ β₁^{-m-1}` (Proposition II.7.9); the budget
(H6′)^pre at the scale `1` (LF-2 (i), base case Lemma II.7.2 (e)); `β_0 = β`, `ν_0 = ν`; and the
torus coherence (D8) (Theorem II.7.10 (d)). -/
def BasePreStepInput : Prop :=
  ∀ κ : ℝ, 0 < κ → ∀ c₉ : ℝ, 0 < c₉ → ∃ β₀ : ℝ, ∀ β : ℝ, β₀ ≤ β →
  ∀ ν : ℝ, 0 < ν → ν * ((T κ c₉).L : ℝ) ^ 2 ≤ 7 / 8 →
  ∀ h : EuclideanSpace ℝ (Fin N), ‖h‖ = 1 → ∀ kf : ℕ, IsHorizon (T κ c₉).L ν kf →
  ∀ [NeZero (T κ c₉).L] [NeZero (T κ c₉).M],
  1 ≤ kZero d (T κ c₉).L β ν →
    ∃ z₁ : ℝ, 0 < z₁ ∧ ∃ νk : ℝ,
      PreClassAt d N (T κ c₉) (P6 κ c₉) (C7 κ c₉) (PB κ c₉) (cs₀ κ c₉) (M1 κ c₉) (c κ c₉)
        (rH κ c₉) (ϱ κ c₉) β ν h kf 1 0
        (firstDensity d N (T κ c₉) β (cs₀ κ c₉).aKer z₁ ν h kf) νk

/-- **A3-2, the first step in regime (B) (LF-6; LFR §II.7.1 regime (B), Definition II.7.6, Lemmas
II.7.7 and II.7.8, Proposition II.7.9, Theorem II.7.10 (b)–(d); P4 (2.42)–(2.54) with `ν_0`).** For
`β ≥ β₀`, `0 < ν ≤ 7/8 L⁻²`, every unit field `h`, the horizon `kf = k̂_f` and `k₀ = 0`: for some
`z₁ > 0`, the density of the first step `ρ₁` (`firstDensity`) is a member of `ℛ♭_1`
(`FlatClassAt … kf 1`): the representation of `BasePreStepInput` with complete backgrounds of scale
`1` from the start (the switch at the step `0 → 1` is vacuous) and P4's renormalization system,
(D2♭), (D9♭), the budget (H6♭) at the scale `1` (LF-2 (ii) with `k₀ = 0`, the frozen base step
(I.6) with the threshold `A₂ λ̂₀^{p₂} ≥ p₂(β)`), the boundary terms with rate `κ` and constant `B₀`,
`β_0 = β`, `ν_0 = ν`, (I.2) at the scales `0, 1`, (D8), and the mass bound `ν₁ ≤ 9/10` of the frozen
class (Theorem II.7.10, (D9♭): `ν₁ = ν L² δ₁` with `ν L² ≤ 7/8` and the flow factor
`δ₁ = (1 + ξ₃)/(1 + ξ₂) ≤ e^{c/β}`, so `ν₁ ≤ (7/8) e^{c/β} ≤ 9/10` for `β ≥ β₀`). -/
def BaseFlatStepInput : Prop :=
  ∀ κ : ℝ, 0 < κ → ∀ c₉ : ℝ, 0 < c₉ → ∃ β₀ : ℝ, ∀ β : ℝ, β₀ ≤ β →
  ∀ ν : ℝ, 0 < ν → ν * ((T κ c₉).L : ℝ) ^ 2 ≤ 7 / 8 →
  ∀ h : EuclideanSpace ℝ (Fin N), ‖h‖ = 1 → ∀ kf : ℕ, IsHorizon (T κ c₉).L ν kf →
  ∀ [NeZero (T κ c₉).L] [NeZero (T κ c₉).M],
  kZero d (T κ c₉).L β ν = 0 →
    ∃ z₁ : ℝ, 0 < z₁ ∧ ∃ νk : ℝ,
      FlatClassAt d N (T κ c₉) (P6 κ c₉) (C7 κ c₉) (PB κ c₉) (cs₀ κ c₉) (M1 κ c₉) (c κ c₉)
        (rH κ c₉) (ϱ κ c₉) β ν h kf 1
        (firstDensity d N (T κ c₉) β (cs₀ κ c₉).aKer z₁ ν h kf) νk

/-- **The base step from its sub-inputs** (LFR Theorem II.7.10 (a), (b)). Regime (A): the first step
(`BasePreStepInput`) gives `ρ₁ ∈ ℛ^pre_1`; the coefficient step (`FlowRateInput`,
`PreClassAt.succ`) gives (I.2) at the scale `1`; the operation `R` at the scale `1 ≤ k₀`
(`RInput`) gives a member of `ℛ_1` with the same integral. Regime (B): `BaseFlatStepInput`. In both
regimes `∫ ρ₁ = Z(g)` is proved (`integralIsZ_firstDensity`, from `basePhysicalDensity`). The
threshold is the largest of the three thresholds. -/
theorem baseStepInput_of_parts (hP : BasePreStepInput d N T P6 C7 PB cs₀ M1 c rH ϱ)
    (hR : RInput d N T P6 C7 PB cs₀ M1 c rH ϱ) (hQ : FlowRateInput T P6)
    (hF : BaseFlatStepInput d N T P6 C7 PB cs₀ M1 c rH ϱ) :
    BaseStepInput d N T P6 C7 PB cs₀ M1 c rH ϱ := by
  intro κ hκ c₉ hc₉
  obtain ⟨β₁, h₁⟩ := hP κ hκ c₉ hc₉
  obtain ⟨β₂, h₂⟩ := hR κ hκ c₉ hc₉
  obtain ⟨β₃, h₃⟩ := hF κ hκ c₉ hc₉
  refine ⟨max (max β₁ β₂) β₃, fun β hβ ν hν hνL h hh kf hkf _ _ => ?_⟩
  simp only [max_le_iff] at hβ
  obtain ⟨⟨hβ₁, hβ₂⟩, hβ₃⟩ := hβ
  have := neZero_of_norm_eq_one hh
  refine ⟨fun hk0 => ?_, fun hk0 => ?_⟩
  · obtain ⟨z₁, hz₁, νk, hpre⟩ := h₁ β hβ₁ ν hν hνL h hh kf hkf hk0
    obtain ⟨recp⟩ := id hpre
    have hrun := recp.run
    obtain ⟨ρ', hcl, hint⟩ := h₂ β hβ₂ ν hν hνL h hh kf hkf 1 le_rfl hk0 _ νk
      (PreClassAt.succ (k := 0) hpre (hQ κ hκ c₉ hc₉))
    exact ⟨ρ', νk, hcl, (integralIsZ_firstDensity hrun.hβ (zero_lt_one.trans hrun.ha1)
      hz₁).of_integral_eq hint⟩
  · obtain ⟨z₁, hz₁, νk, hflat⟩ := h₃ β hβ₃ ν hν hνL h hh kf hkf hk0
    obtain ⟨_, _, _, _, _, _, _, _, _, hbody⟩ := id hflat
    have hrun := hbody.2.2.2.2.2.2.2.2.2.2.2.2.1
    exact ⟨_, νk, hflat, integralIsZ_firstDensity hrun.hβ (zero_lt_one.trans hrun.ha1) hz₁⟩

/-- **The base step from its sub-inputs and the prefix**: `baseStepInput_of_parts`, the rate
condition `FlowRateInput` being a clause of `PrefixInput`. -/
theorem baseStepInput_of_prefix {δ : ℝ} (hA1 : PrefixInput d δ T P6 C7 PB cs₀ M1 c ϱ)
    (hP : BasePreStepInput d N T P6 C7 PB cs₀ M1 c rH ϱ)
    (hR : RInput d N T P6 C7 PB cs₀ M1 c rH ϱ)
    (hF : BaseFlatStepInput d N T P6 C7 PB cs₀ M1 c rH ϱ) :
    BaseStepInput d N T P6 C7 PB cs₀ M1 c rH ϱ :=
  baseStepInput_of_parts d N T P6 C7 PB cs₀ M1 c rH ϱ hP hR (flowRateInput_of_prefix hA1) hF

end Inputs

end Balaban.RootFSpine
