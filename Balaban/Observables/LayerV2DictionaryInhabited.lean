/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Observables.LayerV2Dictionary
public import Balaban.Observables.LayerV2Improved
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The ports of Lemma 2.2, (4.10) and Lemma 3.4 to the second version are non-vacuous

Instantiation of `IsObs2.mscript_bound_xi`, `IsSFObs2.improved_second_bound` and
`IsSFObs2.improved_first_of_const_strong` at the witnesses of the second version, at a scale
`k = 1` with `β_1 ν_1 ≤ 1`, below the switch of the landed class: there the running-test mass of
the landed class is `0` (`Def6.bgMass 3 1 (β 1) (ν 1 1) = 0`) while the mass of the second version is
positive.

* The members `isSFObs2_xi_witness` (`β_n = 3^n`, `β_1 ν_1 = 7/24`) instantiate the statements
  of Lemma 3.4: `improved_second_bound_witness`, `improved_first_of_const_witness`
  (the strong form: no `hlayer`).
* `mscript_bound` carries the largeness hypothesis `√e L^{(d-2)/2} (1 + C_φ) β_0^{-3/4+ρ₁} ≤ 1`,
  which fails for `β_0 = 1` (the coefficients of `witnessβ`; `√e √3 > 1`).  It is instantiated at
  the coefficients `bigβ_n = 10^4 · 3^n`, `bigν_k(n) = (7/720000) 9^{n-k}`, which satisfy
  `CoeffBounds` with the constants of the witness (`bigβ_coeff`), at the layer
  `isObs2_big_witness` (zero terms), with `β_1 ν_1 = 7/24 · ... ≤ 1`: `mscript_bound_witness`.
-/

@[expose] public section

namespace Balaban.Observables

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
open Balaban.SmallField.Def6 Balaban.SmallField.Def6v2 Balaban.SmallField.GsSpec Finset

/-- Large running coupling: `β_n = 10^4 · 3^n`. -/
noncomputable def bigβ : ℕ → ℝ := fun n => 10000 * (3 : ℝ) ^ n

/-- Small mass flow: `ν_n = (7/720000) 9^{n-k}`. -/
noncomputable def bigν (k : ℕ) : ℕ → ℝ := fun n => 7 / 720000 * 9 ^ n / 9 ^ k

theorem bigβ_coeff (k : ℕ) {α₀ : ℝ} :
    CoeffBounds 3 3 k (witnessConsts α₀) bigβ (bigν k) witnessa where
  flow := by
    refine ⟨fun _ => 0, 10000, 7 / 720000 / 9 ^ k, fun n => ?_, ?_, fun n _ => ?_⟩
    · have := rate3_pos; have := rate3_lt
      simp only [witnessConsts, norm_zero]
      positivity
    · have := rate3_pos; have := rate3_lt
      simp only [witnessConsts]
      nlinarith
    · refine ⟨?_, ?_⟩
      · rw [betaSeq_zero]; simp [bigβ]
      · rw [nuSeq_zero]
        simp only [bigν]
        push_cast
        rw [pow_mul]
        norm_num
        ring
  beta_gt := by simp only [witnessConsts, bigβ, zero_mul]; positivity
  nu_pos := by simp only [bigν]; positivity
  nu_le := by
    simp only [bigν, witnessConsts]
    rw [mul_div_assoc, div_self (by positivity)]; norm_num
  a_ge := by norm_num [witnessa]
  a_lt := by norm_num [witnessa]

/-- The observable layer of the second version with zero terms, at the large coupling `bigβ`, on
every field domain, for every regime. -/
theorem isObs2_big_witness (N₁ m₁ k : ℕ) [NeZero N₁] (ϱ : ℝ) {α₀ : ℝ} (hα : 0 < α₀) (Rg : Regime 3)
    (Dom : FieldDom 3 3 N₁ m₁ k 2 ϱ) :
    IsObs2 (d := 3) (L := 3) (N₁ := N₁) (m₁ := m₁) (k := k) (N := 2) (ϱ := ϱ)
      (witnessConsts α₀) witQ Rg bigβ witnessa Dom
      (pinTerms 3 3 N₁ m₁ k 2 ϱ (witnessConsts α₀).κ (fun _ => 0))
      (pinObs 3 3 N₁ m₁ k 2 (witnessConsts α₀).κ (obsCoef bigβ (fun _ => 0)))
      (fun _ _ _ _ _ => 0) :=
  isObs2_pinObs (witnessConsts_admissible hα).κ_pos.le (fun _ => le_rfl) (by simp [bigβ])
    (fun j _ => by simp only [bigβ]; positivity)
    (fun j => by
      have h1 : obsCoef bigβ (fun _ => 0) j = 0 := by simp [obsCoef]
      rw [h1, mul_zero]
      exact mul_nonneg (Real.rpow_nonneg (by simp [bigβ]) _)
        (Real.rpow_nonneg (Nat.cast_nonneg 3) _))
    (fun j hj => absurd rfl hj)


theorem bigβ_hsmall :
    Real.sqrt (Real.exp 1) * ((3 : ℕ) : ℝ) ^ ((((3 : ℕ) : ℝ) - 2) / 2) * (1 + 0) *
      (bigβ 0) ^ (-(3 / 4 : ℝ) + witQ.ρ₁) ≤ 1 := by
  have h1 : Real.sqrt (Real.exp 1) ≤ 2 := by
    rw [Real.sqrt_le_iff]
    refine ⟨by norm_num, ?_⟩
    have := Real.exp_one_lt_d9
    nlinarith
  have h2 : ((3 : ℕ) : ℝ) ^ ((((3 : ℕ) : ℝ) - 2) / 2) ≤ 2 := by
    have : ((3 : ℕ) : ℝ) ^ ((((3 : ℕ) : ℝ) - 2) / 2) = Real.sqrt 3 := by
      rw [Real.sqrt_eq_rpow]; norm_num
    rw [this, Real.sqrt_le_iff]
    exact ⟨by norm_num, by norm_num⟩
  have h3 : (bigβ 0) ^ (-(3 / 4 : ℝ) + witQ.ρ₁) = 1 / 10 := by
    have e : -(3 / 4 : ℝ) + witQ.ρ₁ = -(1 / 4) := by norm_num [witQ]
    rw [e]
    have : bigβ 0 = (10 : ℝ) ^ (4 : ℝ) := by
      simp only [bigβ]; norm_num
    rw [this, ← Real.rpow_mul (by norm_num)]
    norm_num
  rw [h3]
  have h1' := Real.sqrt_nonneg (Real.exp 1)
  have h2' : 0 ≤ ((3 : ℕ) : ℝ) ^ ((((3 : ℕ) : ℝ) - 2) / 2) := by positivity
  nlinarith [mul_le_mul h1 h2 h2' (by norm_num : (0 : ℝ) ≤ 2)]

/-- **Below the switch**: at `k = 1`, `β_1 ν_1 = 7/24 ≤ 1`, so the running-test mass of the landed
class is `0` (`Def6.bgMass`), while the mass of the second version is positive. -/
theorem big_witness_mass (k₀ : ℕ) :
    bigβ 1 * bigν 1 1 ≤ 1 ∧ Def6.bgMass 3 1 (bigβ 1) (bigν 1 1) = 0 ∧
      0 < (⟨k₀, bigν 1⟩ : Regime 3).sfBgMass 1 := by
  have hβν : bigβ 1 * bigν 1 1 ≤ 1 := by simp only [bigβ, bigν]; norm_num
  refine ⟨hβν, by simp [Def6.bgMass, hβν], Regime.sfBgMass_pos (⟨k₀, bigν 1⟩ : Regime 3) ?_⟩
  show 0 < bigν 1 1
  simp only [bigν]; norm_num

/-- **Lemma 2.2 (`IsObs2.mscript_bound_xi`) is non-vacuous below the switch**: for the member
`isObs2_big_witness` at `k = 1` (large coupling `bigβ`, `β_1 ν_1 = 7/24 ≤ 1`, background mass
`sfBgMass 1 > 0`, `big_witness_mass`), with `C_φ = 0`, `φ = 0`, every level-`1` term satisfies the
bound `β_0^{-1/4} (L^{-1})^{(d-2)/2+γ-α₁} e^{-κ d_1(X)}`. -/
theorem mscript_bound_witness (N₁ m₁ k₀ : ℕ) [NeZero N₁] (ϱ : ℝ) {α₀ : ℝ} (hα : 0 < α₀)
    (x : CTorus 3 3 N₁ m₁ 1) (X : Set (CTorus 3 3 N₁ m₁ 1))
    (hX : IsPolyDom (witnessConsts α₀).m₀ 1 X) (hxX : x ∈ X) (Ψ h : Fld 3 3 N₁ m₁ 1 2)
    (hdom : XiDom ((pinTerms 3 3 N₁ m₁ 1 2 ϱ (witnessConsts α₀).κ (fun _ => 0)).gs 1 X)
      (aIdeal 3 1 (witnessa 1)) ((⟨k₀, bigν 1⟩ : Regime 3).sfBgMass 1) 1
      ((witnessConsts α₀).eps 3 3 1) Ψ h) :
    vn (((Real.sqrt (bigβ (1 - 1)))⁻¹ : ℂ) •
        ((pinObs 3 3 N₁ m₁ 1 2 (witnessConsts α₀).κ (obsCoef bigβ (fun _ => 0))).M 1 x X Ψ h -
          ((pinObs 3 3 N₁ m₁ 1 2 (witnessConsts α₀).κ (obsCoef bigβ (fun _ => 0))).μ 1 x : ℂ) •
            (0 : Fin 2 → ℂ))) ≤
      (bigβ 0) ^ (-(1 / 4 : ℝ)) * ((((3 : ℕ) : ℝ) ^ 1)⁻¹) ^
          ((((3 : ℕ) : ℝ) - 2) / 2 + (witnessConsts α₀).γ - (witnessConsts α₀).α₁) *
        Real.exp (-(witnessConsts α₀).κ * sizeJ (witnessConsts α₀).m₀ 1 X) :=
  (isObs2_big_witness N₁ m₁ 1 ϱ hα (⟨k₀, bigν 1⟩ : Regime 3)
    (xiFieldDom (aIdeal 3 1 (witnessa 1)) ((⟨k₀, bigν 1⟩ : Regime 3).sfBgMass 1)
      ((witnessConsts α₀).eps 3 3))).mscript_bound_xi
    (by norm_num) (by norm_num) (witnessConsts_admissible hα) (bigβ_coeff 1)
    (by simp only [bigβ]; norm_num) (by norm_num [witnessConsts, witQ]) le_rfl
    (fun _ _ _ _ _ => 0) (fun _ _ _ _ _ _ _ _ _ _ => by simp [vn_zero]) bigβ_hsmall le_rfl le_rfl x X hX hxX
    Ψ h hdom


/-- The zero small-field terms of the witness. -/
noncomputable abbrev witTm (α₀ : ℝ) (N₁ m₁ k : ℕ) [NeZero N₁] (ϱ : ℝ) :
    Terms 3 3 N₁ m₁ k 2 ϱ :=
  pinTerms 3 3 N₁ m₁ k 2 ϱ (witnessConsts α₀).κ (fun _ => 0)

/-- The zero observable terms of the witness. -/
noncomputable abbrev witObs (α₀ : ℝ) (N₁ m₁ k : ℕ) [NeZero N₁] : ObsTerms 3 3 N₁ m₁ k 2 :=
  pinObs 3 3 N₁ m₁ k 2 (witnessConsts α₀).κ (obsCoef witnessβ (fun _ => 0))

theorem witObs_M_zero (α₀ : ℝ) (N₁ m₁ k : ℕ) [NeZero N₁] (j : ℕ) (x : CTorus 3 3 N₁ m₁ k)
    (X : Set (CTorus 3 3 N₁ m₁ k)) (Ψ h : Fld 3 3 N₁ m₁ k 2) :
    (witObs α₀ N₁ m₁ k).M j x X Ψ h = 0 := by
  simp [witObs, pinObs, wCoef, obsCoef]

/-- **Lemma 3.4 (2.22) (`IsSFObs2.improved_second_bound`) is non-vacuous below the switch**: for
the member `isSFObs2_xi_witness` at `k = 1` (`β_1 ν_1 = 7/24 ≤ 1`, see
`renorm_v2_hypotheses_witness`), every datum obeys the entropy bound (the terms are zero, so the
first-bound hypothesis holds with any `C ≥ 0`). -/
theorem improved_second_bound_witness (m₁ k₀ N₁ : ℕ) [NeZero N₁] (ϱ : ℝ) (hϱ : bgR0 3 3 ≤ ϱ)
    {α₀ : ℝ} (hα : 0 < α₀) {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ 1) (x : CTorus 3 3 N₁ m₁ 1)
    (Ψ h : Fld 3 3 N₁ m₁ 1 2) {C A s K₀ : ℝ} (hC : 0 ≤ C)
    (hK : ∑ᶠ X ∈ polysAt (witnessConsts α₀).m₀ j x,
      Real.exp (-((witnessConsts α₀).κ - 1) * sizeJ (witnessConsts α₀).m₀ j X) ≤ K₀)
    (hAs : 0 ≤ A * s) :
    vn (Mobs (witnessConsts α₀).m₀ (witObs α₀ N₁ m₁ 1) j x Ψ h) ≤ C * K₀ * (A * s) := by
  refine (isSFObs2_xi_witness m₁ 1 k₀ N₁ ϱ hϱ hα).improved_second_bound hj1 hjk x Ψ h
    (v := (Pi.single 0 1 : Fin 2 → ℝ)) (by simp [dotProduct, Pi.single_apply]) hC ?_ hK hAs
  intro X _
  rw [witObs_M_zero, witObs_M_zero, sub_zero, vn_zero]
  have : 0 ≤ Real.exp (-((witnessConsts α₀).κ - 1) * sizeJ (witnessConsts α₀).m₀ j X) :=
    (Real.exp_pos _).le
  have hA : 0 ≤ A * s := hAs
  positivity

/-- **Lemma 3.4 (2.21) from the constant part, strong form
(`IsSFObs2.improved_first_of_const_strong`), is non-vacuous below the switch**: the structural
hypotheses (`IsSFObs2` on the wide domain at the complete mass, `BgHyp`, the strong specification
of the generating sets, so that no `hlayer` is needed) are discharged for the witness at `k = 1`
with `β_1 ν_1 = 7/24 ≤ 1`; what remains are the numerical and typing premises of the landed
statement. -/
theorem improved_first_of_const_witness (m₁ k₀ N₁ : ℕ) [NeZero N₁] (ϱ : ℝ) (hϱ : bgR0 3 3 ≤ ϱ)
    {α₀ : ℝ} (hα : 0 < α₀) {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ 1)
    (hN : 3 ^ (witnessConsts α₀).m₀ ∣ N₁)
    {X : Set (CTorus 3 3 N₁ m₁ 1)} (hX : IsPolyDom (witnessConsts α₀).m₀ j X)
    {x : CTorus 3 3 N₁ m₁ 1} (hx : x ∈ X) {y : CTorus 3 3 N₁ m₁ 1} (hy : y ∈ X)
    {Ψ₀ : CTorus 3 3 N₁ m₁ 1 → Fin 2 → ℝ} {h₀ : Fin 2 → ℝ}
    {Ψ'' : CTorus 3 3 N₁ m₁ 1 → Fin 2 → ℂ} {h' : Fin 2 → ℂ} {δ ε δ₀ : ℝ}
    (hP : InPsiTildeC ((witTm α₀ N₁ m₁ 1 ϱ).gs j X)
      ((⟨k₀, witnessν 1⟩ : Regime 3).sfBgMass 1) δ ε Ψ₀ h₀ Ψ'' (fun _ => h'))
    (hδ : 0 < δ) (hδε : δ ≤ ε) (hε : ε ≤ δ₀) (hc0 : δ₀ ≤ bgC0 3 3 2) (hc1 : δ₀ ≤ bgC1 3 3 2)
    (hεj : δ₀ + (2 * bgK1 3 3 2 + 1) * δ₀ ≤ (witnessConsts α₀).eps 3 3 j)
    (hsmall : 128 * (3 ^ 3 * (((3 : ℕ) : ℝ) ^ ((witnessConsts α₀).m₀ + m₁) * (4 * 3 * 3) + 1)) * δ ≤
      δ₀)
    {v : Fin 2 → ℝ} {bc : ℝ}
    (hconst : vn ((witObs α₀ N₁ m₁ 1).M j x X (constFld (fun i => (Ψ₀ y i : ℂ) + Ψ'' y i))
        (constFld (fun i => (h₀ i : ℂ) + h' i)) -
      (witObs α₀ N₁ m₁ 1).M j x X (constFld (fun i => (v i : ℂ)))
        (constFld (fun i => (v i : ℂ)))) ≤ bc) :
    vn ((witObs α₀ N₁ m₁ 1).M j x X (fun z i => (Ψ₀ z i : ℂ) + Ψ'' z i)
          (constFld (fun i => (h₀ i : ℂ) + h' i)) -
        (witObs α₀ N₁ m₁ 1).M j x X (constFld (fun i => (v i : ℂ)))
          (constFld (fun i => (v i : ℂ)))) ≤
      improvedConst
          (max (3 ^ 3 * (((3 : ℕ) : ℝ) ^ ((witnessConsts α₀).m₀ + m₁) * (4 * 3 * 3) + 1))
            (2 * ((3 : ℕ) : ℝ) * (3 ^ 3 * ((3 : ℕ) : ℝ) ^ ((witnessConsts α₀).m₀ + m₁))))
          (δ₀ / 128) (δ₀ / (128 * (3 ^ 3 * ((3 : ℕ) : ℝ) ^ ((witnessConsts α₀).m₀ + m₁)))) *
        ((witnessβ 0) ^ (-(1 / 2 : ℝ) + witQ.ρ₁) * ((3 : ℕ) : ℝ) ^ (-((j : ℝ) * witQ.ρ₀)) * δ *
          Real.exp (-((witnessConsts α₀).κ - 1) * sizeJ (witnessConsts α₀).m₀ j X)) + bc := by
  have H := bgHyp_of_class2 (ϱ := ϱ) (Rg := (⟨k₀, witnessν 1⟩ : Regime 3))
    (witnessConsts_admissible hα) (witness_coeff 1) le_rfl le_rfl hϱ
  exact (isSFObs2_xi_witness m₁ 1 k₀ N₁ ϱ hϱ hα).improved_first_of_const_strong
    (fun j hj1 hjk X _ => by rw [pinTerms_gs hjk]; exact levelGS_strong hj1 hjk X) H hj1 hjk hN hX
    hx hy hP (by simp [witnessβ]) hδ hδε hε hc0 hc1 hεj hsmall hconst

end Balaban.Observables
