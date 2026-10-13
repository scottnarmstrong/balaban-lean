/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.StepActivityHatGeneral
public import Balaban.Fluctuation.StepActivityDirectPhysical
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The step activity bound of a general class with the preserved decay rate

`StepActivityDirectPhysical.stepActivityBound_zeroClass_direct` is the label-activity bound of one
fluctuation step for the zero class.  Its assembler evaluates the expansion at the hat variable
`ψ̂` and the parameter `σ = s`, and multiplies the activities by `s²`.  That is the step exponent
only when the expansion has no old terms: in `physVal` the potential part and the old-term parts
have the same parameter `σ`, and

`physVal(ψ̂, ψ̂; σ = u) = W₁(u) + W₂(u) + (1 - u²) · (-β) raySrc3(…)`

(`physVal_diag_eq_of_oldHatMatch`): the factor `u²` of the Taylor remainder belongs to the
potential part alone.  No definition is changed here.  The same expansion is evaluated instead at
the scaled hat variables and `σ = 1`, where no rescaling is needed:

`physVal((s ψ̂, t ψ̂), (s ψ̂, t ψ̂); σ = 1; (Θ, g/β)) = W₁(s, ψ̂) + W₂(t, ψ̂; g)`

for all `s, t ∈ [0,1]` on the support of `ν_{p₁}` (`physVal_eq_stepExponent_of_oldHatMatch`).  The
admissible pairs of rays are star-shaped and `1 < R_σ`, so the landed expansion covers this point.

* `DirectTerms.scaled`, `labelAct_scaled_of_directTerms`: the label activities of a `DirectTerms`
  instance at the scaled hat variable `s ψ̂` and `σ = 1`, on the same labels, with the same rate and
  prefactor.
* `stepActivityBound_of_directTerms_scaled`, `stepActivityBound_source_of_directTerms_scaled`: the
  assemblers for an arbitrary class `C` (source `0`: rate `a`, prefactor `R_σ ε_U`; source `g`: two
  instances, prefactor `2 R_σ ε_U`, entropy constant `2 K_c'`, as in the landed zero-class source
  assembler).
* `physVal_scaled_eq_Wone_of_oldEnergyHatMatch`, `physVal_scaled_sub_eq_Wtwo_of_oldObsHatMatch`,
  `physVal_eq_stepExponent_of_oldHatMatch`: the value identities for the physical expansion.
* `stepActivityBound_direct_of_oldEnergyHatMatch`: **the step activity bound of a general class**,
  source `0`, with `κ_H = 2 κ_dec - 1` and `ε_H = R_σ ε_U`;
  `stepActivityBound_direct_source_of_oldHatMatch`: a source `g`;
  `stepActivityBound_direct_rate_of_oldEnergyHatMatch`: the rate statement at `d = L = 3`.

What is proved: for a class `C` whose old terms are represented by the old-term functionals of the
expansion (the named hypotheses `OldEnergyHatMatch`, `OldObsHatMatch` of `StepActivityHatGeneral`),
one fluctuation step preserves the label-activity decay rate.  What is not proved:

* those two hypotheses for functionals on localized generating sets (they are proved for the
  whole-lattice sets in `StepActivityHatLevel`, and for classes whose terms do not depend on the
  spin);
* the hypotheses of the expansion on the old-term functionals, which are no longer vacuous: the
  settings and covers of each old term, and its analyticity and bound on the chart
  `Ξ^c_j(𝔹_j(X); C₀, ε₂)` (for a member of the class on the generating sets of its terms the last
  two follow from the class-radius inequality `C₀² ε₂ ≤ ε_j`, `StepActivityClassChart`; the
  inequality is not proved);
* the domain hypothesis `OldXiDomC` on the physical chart (it is not used: `StepActivityBound` has
  no regularity clause, and the analyticity along the fluctuation is that of the functionals on
  their chart);
* the output terms of the class, and the smallness `(DA)` in the regime of the papers;
* an instance with an old term that varies along the fluctuation (the instances of
  `StepActivityDirectGeneralWitness` are the zero class and a class with a non-zero old energy
  that does not depend on the spin).

The class enters only through `S.Wone C`, `S.Wtwo C g`; no generating set of the class appears.
-/

@[expose] public section

namespace Balaban.Fluctuation

open MeasureTheory Balaban Balaban.Localization Balaban.Multiscale Balaban.Polymer
  Balaban.Background Balaban.SmallField Balaban.SmallField.Def6 Balaban.Analysis Finset Matrix Set
  Metric

section Scaled

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- The clamp of a real number to `[0,1]`. -/
noncomputable def clamp01 (s : ℝ) : ℝ := max 0 (min s 1)

theorem clamp01_mem (s : ℝ) : clamp01 s ∈ Icc (0 : ℝ) 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩

theorem clamp01_of_mem {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : clamp01 s = s := by
  unfold clamp01
  rw [min_eq_left hs.2, max_eq_right hs.1]

/-- The disk of hat variables is star-shaped. -/
theorem smul_mem_hatDisk {U : Type} {ρ : ℝ} {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    {ψ : U × Fin N → ℂ} (hψ : ψ ∈ hatDisk U N ρ) : (s : ℂ) • ψ ∈ hatDisk U N ρ := by
  intro p
  show ‖(s : ℂ) * ψ p‖ ≤ ρ
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hs.1]
  calc s * ‖ψ p‖ ≤ 1 * ‖ψ p‖ := mul_le_mul_of_nonneg_right hs.2 (norm_nonneg _)
    _ ≤ ρ := by rw [one_mul]; exact hψ p

variable (S : StepSetting d L N₁ m₁ k N ϱ) (m₀ : ℕ) {Λ F' : Type}
  [NormedAddCommGroup Λ] [NormedSpace ℂ Λ]

/-- **The direct-label terms at a scaled hat variable.**  If the agreement relation of the terms is
preserved by the scaling `ψ̂ ↦ s ψ̂`, `s ∈ [0,1]`, the terms of a `DirectTerms` instance, read at the
embedding `ψ̂ ↦ emb (s ψ̂)`, are again a `DirectTerms` instance, with the same domains, terms,
bounds and source datum. -/
noncomputable def DirectTerms.scaled {hp : 0 < S.p₁} {emb : (S.U × Fin N → ℂ) → F'}
    {ρ Rσ εU a : ℝ} {Θ₀ : Λ} {SΛ : Set Λ} {XW : Set (F' × F')} {val : F' → F' → ℂ → Λ → ℂ}
    {AgΘ : Set (CTorus d L N₁ m₁ (k + 1)) → Λ → Λ → Prop}
    {AgF : Set (CTorus d L N₁ m₁ (k + 1)) → F' → F' → Prop}
    (I : DirectTerms S m₀ hp emb ρ Rσ εU a Θ₀ SΛ XW val AgΘ AgF) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1)
    (hAgF : ∀ (t : ℝ) (Y : Set (CTorus d L N₁ m₁ (k + 1))) (ψ ψ' : S.U × Fin N → ℂ),
      AgF Y (emb ψ) (emb ψ') → AgF Y (emb ((t : ℂ) • ψ)) (emb ((t : ℂ) • ψ'))) :
    DirectTerms S m₀ hp (fun ψ => emb ((s : ℂ) • ψ)) ρ Rσ εU a Θ₀ SΛ XW val AgΘ AgF where
  𝒴 := I.𝒴
  T := I.T
  b := I.b
  loc := I.loc
  dom := I.dom
  bd := I.bd
  mem := I.mem
  agΘ := I.agΘ
  xw := fun ψ hψ => I.xw _ (smul_mem_hatDisk hs hψ)
  ag := fun Y hY Φ Φ' h => hAgF s Y _ _ (I.ag Y hY Φ Φ' h)
  meas := fun Y hY σ hσ => by
    have hm : Measurable (fun ψ : hatDisk S.U N ρ =>
        (⟨(s : ℂ) • ψ.1, smul_mem_hatDisk hs ψ.2⟩ : hatDisk S.U N ρ)) := by
      refine Measurable.subtype_mk (Measurable.of_eval fun q => ?_)
      have h1 : Measurable (fun ψ : hatDisk S.U N ρ => ψ.1 q) :=
        (measurable_pi_apply q).comp measurable_subtype_coe
      exact h1.const_mul (s : ℂ)
    exact (I.meas Y hY σ hσ).comp hm

/-- **Label activities at the scaled hat variables.**  For a `DirectTerms` instance whose agreement
relation is preserved by the scalings, and `1 < R_σ`, there is a family `A s` of label activities
on the labels of the instance (rate `a`, prefactor `R_σ ε_U`, entropy bound `K_c ≥ K₀`) with

`∑_Y (A s).H Y Φ = val (emb (s ψ̂)) (emb (s ψ̂)) 1 Θ₀`,  `ψ̂ = hatOf Φ`,  `s ∈ [0,1]`:

the expansion at the scaled hat variable and the parameter `σ = 1`. -/
theorem labelAct_scaled_of_directTerms {hp : 0 < S.p₁} {emb : (S.U × Fin N → ℂ) → F'}
    {ρ Rσ εU a : ℝ} {Θ₀ : Λ} {SΛ : Set Λ} {XW : Set (F' × F')} {val : F' → F' → ℂ → Λ → ℂ}
    {AgΘ : Set (CTorus d L N₁ m₁ (k + 1)) → Λ → Λ → Prop}
    {AgF : Set (CTorus d L N₁ m₁ (k + 1)) → F' → F' → Prop}
    (I : DirectTerms S m₀ hp emb ρ Rσ εU a Θ₀ SΛ XW val AgΘ AgF)
    (hAgF : ∀ (t : ℝ) (Y : Set (CTorus d L N₁ m₁ (k + 1))) (ψ ψ' : S.U × Fin N → ℂ),
      AgF Y (emb ψ) (emb ψ') → AgF Y (emb ((t : ℂ) • ψ)) (emb ((t : ℂ) • ψ')))
    (hN : L ^ m₀ ∣ N₁) (hρ : 0 < ρ) (hRσ1 : 1 < Rσ) (hεU : 0 ≤ εU)
    {κ0 Kc : ℝ} (hκ0 : aEnt d L + 1 ≤ κ0) (hKc : K0 d L κ0 ≤ Kc) :
    ∃ A : ℝ → LabelAct (thickLabels I.𝒴 I.dom) (S.blockSplit m₀ hp).Ωb (Rσ * εU) a κ0 Kc,
      ∀ s ∈ Icc (0 : ℝ) 1, ∀ Φ, ∑ y, (A s).H y Φ =
        val (emb ((s : ℂ) • S.hatOf m₀ ρ hp Φ)) (emb ((s : ℂ) • S.hatOf m₀ ρ hp Φ)) 1 Θ₀ := by
  have h : ∀ s : ℝ, ∃ A : LabelAct (thickLabels I.𝒴 I.dom) (S.blockSplit m₀ hp).Ωb (Rσ * εU) a
      κ0 Kc, ∀ Φ, ∑ y, A.H y Φ = val (emb ((clamp01 s : ℂ) • S.hatOf m₀ ρ hp Φ))
        (emb ((clamp01 s : ℂ) • S.hatOf m₀ ρ hp Φ)) 1 Θ₀ := by
    intro s
    obtain ⟨A, -, hid⟩ := labelAct_of_directTerms S m₀ (I.scaled S m₀ (clamp01_mem s) hAgF) hN hρ
      (by linarith) hεU hκ0 hKc
    exact ⟨A 1, fun Φ => hid 1 (by simpa using hRσ1) Φ⟩
  choose A hA using h
  exact ⟨A, fun s hs Φ => by rw [hA s Φ, clamp01_of_mem hs]⟩

end Scaled

section Assemble

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}

/-- For the source `0` the second exponent vanishes, for every class. -/
theorem StepSetting.Wtwo_source_zero (S : StepSetting d L N₁ m₁ k N ϱ)
    (C : StepClass d L N₁ m₁ k N ϱ) (t : ℝ) (x : S.E) : S.Wtwo C 0 t x = 0 := by
  have h0 : ∀ D, FcompAt C.m₀ C.Tm S.a S.ν (Nat.le_succ k) D 0 = 0 := fun D => by
    simp [FcompAt, Floc]
  unfold StepSetting.Wtwo StepSetting.dF
  rw [h0, h0, sub_zero]

variable (S : StepSetting d L N₁ m₁ k N ϱ) (C : StepClass d L N₁ m₁ k N ϱ) {m₀ : ℕ}
  {Λ F' : Type} [NormedAddCommGroup Λ] [NormedSpace ℂ Λ]

/-- **The step activity bound of a class from direct-label terms at the scaled hat variable**
(source `0`).  Let `I` be a `DirectTerms` instance whose agreement relation is preserved by the
scalings and whose expanded function, at the scaled hat variable `s ψ̂` and the parameter `σ = 1`,
is the first exponent of the class `C`:
`val (emb (s ψ̂)) (emb (s ψ̂)) 1 Θ₀ = W₁(s, ψ̂)` for `s ∈ [0,1]` on the support of `ν_{p₁}`.  Under
the numerical hypotheses of `stepActivityBound_zeroClass_of_directTerms_fields` there is a step
activity bound of `C` for the source `0` with rate `κ_H = a` and prefactor `ε_H = R_σ ε_U`.  No
rescaling of the activities is used. -/
theorem stepActivityBound_of_directTerms_scaled {hp : 0 < S.p₁}
    {emb : (S.U × Fin N → ℂ) → F'} {ρ Rσ εU a κ0 κ' Kc' : ℝ} {Θ₀ : Λ} {SΛ : Set Λ}
    {XW : Set (F' × F')} {val : F' → F' → ℂ → Λ → ℂ}
    {AgΘ : Set (CTorus d L N₁ m₁ (k + 1)) → Λ → Λ → Prop}
    {AgF : Set (CTorus d L N₁ m₁ (k + 1)) → F' → F' → Prop}
    (I : DirectTerms S m₀ hp emb ρ Rσ εU a Θ₀ SΛ XW val AgΘ AgF)
    (hAgF : ∀ (t : ℝ) (Y : Set (CTorus d L N₁ m₁ (k + 1))) (ψ ψ' : S.U × Fin N → ℂ),
      AgF Y (emb ψ) (emb ψ') → AgF Y (emb ((t : ℂ) • ψ)) (emb ((t : ℂ) • ψ')))
    (hval : ∀ s ∈ Icc (0 : ℝ) 1, ∀ x : S.E, chiFl S.U N S.p₁ x = 1 →
      val (emb ((s : ℂ) • S.hatC x)) (emb ((s : ℂ) • S.hatC x)) 1 Θ₀ = S.Wone C s x)
    (hN : L ^ m₀ ∣ N₁) (hpρ : S.p₁ ≤ ρ) (hεpos : 0 < εU)
    (hκE : aEnt d L + 1 ≤ κ0) (hKc : K0 d L κ0 + 1 ≤ Kc') (hκ' : 0 ≤ κ')
    (hκa : κ' + 3 * κ0 + c1 d L + 3 / 2 ≤ a)
    (hDA : Rσ * εU ≤ 1 / (8 * Kc' ^ 3 * c1 d L *
      Real.exp ((a - 2 * κ0) * cG d L + c1 d L + κ' * cG d L)))
    (hRσ1 : 1 < Rσ) :
    ∃ B : StepActivityBound S C 0, B.κH = a ∧ B.εH = Rσ * εU := by
  classical
  have hρ : 0 < ρ := lt_of_lt_of_le hp hpρ
  have hK0 : K0 d L κ0 ≤ Kc' := by linarith
  have hRσ : 0 < Rσ := by linarith
  obtain ⟨A, hA⟩ := labelAct_scaled_of_directTerms S m₀ I hAgF hN hρ hRσ1 hεpos.le hκE hK0
  refine ⟨{
    m₀ := m₀
    hN := hN
    BS := S.blockSplit m₀ hp
    Lb := {Y // Y ∈ I.𝒴}
    Lab := thickLabels I.𝒴 I.dom
    εH := Rσ * εU
    κH := a
    κ0 := κ0
    κ' := κ'
    Kc := Kc'
    A := fun p => A p.1
    hκ0 := hκE
    hKc := hKc
    hεpos := by positivity
    hκ' := hκ'
    hκ := hκa
    hε := hDA
    hW := ?_ }, rfl, rfl⟩
  intro p hpS
  have hs : p.1 ∈ Icc (0 : ℝ) 1 := by
    rcases hpS with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact h1
    · rw [h1]; exact ⟨zero_le_one, le_rfl⟩
  filter_upwards [S.ae_hatOf_restr m₀ hρ hp hpρ, S.ae_ball hp] with x hx hχ
  rw [S.Wtwo_source_zero C, add_zero, hA p.1 hs, hx]
  exact (hval p.1 hs x hχ).symm

/-- **The step activity bound of a class with a source from two direct-label families at the
scaled hat variable.**  `I₀` is a direct-label expansion at the source datum `Θ₀` (source `0`) and
`Iᵍ` one at `Θᵍ` (source `g`), both with agreement relations preserved by the scalings.  If, at the
scaled hat variable and the parameter `σ = 1`,

`val₀ (s ψ̂) = W₁(s, ψ̂)` and `valᵍ (t ψ̂) - val₀ (t ψ̂) = W₂(t, ψ̂; g)`

for `s, t ∈ [0,1]` on the support of `ν_{p₁}`, there is a step activity bound of `C` for the source
`g`.  The activity is `A⁰(s)` on `(s, 0)` and `A⁰(1) - A⁰(t) + Aᵍ(t)` on `(1, t)` (`segAct`, with
the constant `1` in place of `s²`), on the sum of the label types, with rate `κ_H = a`, prefactor
`ε_H = 2 R_σ ε_U` and `K_c = 2 K_c'`, as in `stepActivityBound_zeroClass_source_of_directTerms`. -/
theorem stepActivityBound_source_of_directTerms_scaled {hp : 0 < S.p₁}
    (g : Fld d L N₁ m₁ (k + 1) N)
    {emb : (S.U × Fin N → ℂ) → F'} {ρ Rσ εU a κ0 κ' Kc' : ℝ} {Θ₀ Θg : Λ} {SΛ₀ SΛg : Set Λ}
    {XW₀ XWg : Set (F' × F')} {val₀ valg : F' → F' → ℂ → Λ → ℂ}
    {AgΘ₀ AgΘg : Set (CTorus d L N₁ m₁ (k + 1)) → Λ → Λ → Prop}
    {AgF₀ AgFg : Set (CTorus d L N₁ m₁ (k + 1)) → F' → F' → Prop}
    (I₀ : DirectTerms S m₀ hp emb ρ Rσ εU a Θ₀ SΛ₀ XW₀ val₀ AgΘ₀ AgF₀)
    (Ig : DirectTerms S m₀ hp emb ρ Rσ εU a Θg SΛg XWg valg AgΘg AgFg)
    (hAgF₀ : ∀ (t : ℝ) (Y : Set (CTorus d L N₁ m₁ (k + 1))) (ψ ψ' : S.U × Fin N → ℂ),
      AgF₀ Y (emb ψ) (emb ψ') → AgF₀ Y (emb ((t : ℂ) • ψ)) (emb ((t : ℂ) • ψ')))
    (hAgFg : ∀ (t : ℝ) (Y : Set (CTorus d L N₁ m₁ (k + 1))) (ψ ψ' : S.U × Fin N → ℂ),
      AgFg Y (emb ψ) (emb ψ') → AgFg Y (emb ((t : ℂ) • ψ)) (emb ((t : ℂ) • ψ')))
    (hval₀ : ∀ s ∈ Icc (0 : ℝ) 1, ∀ x : S.E, chiFl S.U N S.p₁ x = 1 →
      val₀ (emb ((s : ℂ) • S.hatC x)) (emb ((s : ℂ) • S.hatC x)) 1 Θ₀ = S.Wone C s x)
    (hvalg : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x : S.E, chiFl S.U N S.p₁ x = 1 →
      valg (emb ((t : ℂ) • S.hatC x)) (emb ((t : ℂ) • S.hatC x)) 1 Θg -
        val₀ (emb ((t : ℂ) • S.hatC x)) (emb ((t : ℂ) • S.hatC x)) 1 Θ₀ = S.Wtwo C g t x)
    (hN : L ^ m₀ ∣ N₁) (hpρ : S.p₁ ≤ ρ) (hεpos : 0 < εU)
    (hκE : aEnt d L + 1 ≤ κ0) (hKc : K0 d L κ0 + 1 ≤ Kc') (hκ' : 0 ≤ κ')
    (hκa : κ' + 3 * κ0 + c1 d L + 3 / 2 ≤ a)
    (hDA : 2 * (Rσ * εU) ≤ 1 / (8 * (2 * Kc') ^ 3 * c1 d L *
      Real.exp ((a - 2 * κ0) * cG d L + c1 d L + κ' * cG d L)))
    (hRσ1 : 1 < Rσ) :
    ∃ B : StepActivityBound S C g, B.κH = a ∧ B.εH = 2 * (Rσ * εU) ∧ B.Kc = 2 * Kc' := by
  classical
  have hρ : 0 < ρ := lt_of_lt_of_le hp hpρ
  have hK0 : K0 d L κ0 ≤ Kc' := by linarith
  have hK00 : 0 ≤ K0 d L κ0 := by
    unfold K0
    exact div_nonneg (Real.exp_pos _).le (sub_nonneg.2 (Real.exp_le_one_iff.2 (by norm_num)))
  have hRσ : 0 < Rσ := by linarith
  have hεR : 0 < Rσ * εU := mul_pos hRσ hεpos
  obtain ⟨A0, hA0⟩ := labelAct_scaled_of_directTerms S m₀ I₀ hAgF₀ hN hρ hRσ1 hεpos.le hκE hK0
  obtain ⟨Ag, hAg⟩ := labelAct_scaled_of_directTerms S m₀ Ig hAgFg hN hρ hRσ1 hεpos.le hκE hK0
  have hcfun : ∀ _s : ℝ, ‖(1 : ℂ)‖ ≤ 1 := fun _ => by simp
  have hlt1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hE2 : Rσ * εU + Rσ * εU ≤ 2 * (Rσ * εU) := by linarith
  have hKc2 : Kc' + Kc' = 2 * Kc' := by ring
  refine ⟨{
    m₀ := m₀
    hN := hN
    BS := S.blockSplit m₀ hp
    Lb := {Y // Y ∈ I₀.𝒴} ⊕ {Y // Y ∈ Ig.𝒴}
    Lab := (thickLabels I₀.𝒴 I₀.dom).sum (thickLabels Ig.𝒴 Ig.dom)
    εH := max (2 * (Rσ * εU)) (2 * (Rσ * εU))
    κH := a
    κ0 := κ0
    κ' := κ'
    Kc := Kc' + Kc'
    A := segAct (fun u : ℂ => A0 u.re) (fun u : ℂ => Ag u.re) hεR.le hE2 (fun _ => (1 : ℂ)) hcfun
    hκ0 := hκE
    hKc := by linarith
    hεpos := by rw [max_self]; positivity
    hκ' := hκ'
    hκ := hκa
    hε := by
      rw [max_self, hKc2]
      exact hDA
    hW := ?_ }, rfl, by simp, by simp [hKc2]⟩
  intro p hpS
  by_cases h0 : p.2 = 0
  · have hs : p.1 ∈ Icc (0 : ℝ) 1 := by
      rcases hpS with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact h1
      · rw [h1]; exact hlt1
    filter_upwards [S.ae_hatOf_restr m₀ hρ hp hpρ, S.ae_ball hp] with x hx hχ
    show S.Wone _ p.1 x + S.Wtwo _ g p.2 x = _
    rw [segAct_total_zero _ _ _ _ _ _ h0, h0, S.Wtwo_zero C g x, add_zero, one_mul,
      Complex.ofReal_re, hA0 p.1 hs, hx]
    exact (hval₀ p.1 hs x hχ).symm
  · have ht : p.2 ∈ Icc (0 : ℝ) 1 := by
      rcases hpS with ⟨-, h2⟩ | ⟨-, h2⟩
      · exact absurd h2 h0
      · exact h2
    have h1 : p.1 = 1 := by
      rcases hpS with ⟨-, h2⟩ | ⟨h1, -⟩
      · exact absurd h2 h0
      · exact h1
    filter_upwards [S.ae_hatOf_restr m₀ hρ hp hpρ, S.ae_ball hp] with x hx hχ
    show S.Wone _ p.1 x + S.Wtwo _ g p.2 x = _
    rw [segAct_total_ne _ _ _ _ _ _ h0, h1, Complex.one_re, Complex.ofReal_re, hA0 1 hlt1,
      hA0 p.2 ht, hAg p.2 ht, hx, hval₀ 1 hlt1 x hχ, ← hvalg p.2 ht x hχ]
    ring

end Assemble

section Value

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}

namespace StepSetting

variable (S : StepSetting d L N₁ m₁ k N ϱ) (C : StepClass d L N₁ m₁ k N ϱ)
variable {c BG κ eps Kc Cx c₂ BG₂ δ₁ δc : ℝ} {pp : ℝ}

variable (hC : FlCore N S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
  (R0 : S.RayData pp) (hlt : S.p₁ < pp)
  (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps S.D')
  (hc7 : c7 d L N BG κ ≤ thm73C3 d L N) {R : ℝ} (hR : 2 ≤ R)
  (hsmR : 2 * (compC4 d * (bgK1 d L N * (xiC1 d * eps))) + 5 * (R * δ₁) ≤ bgC1 d L N)
  (hRs : R * δ₁ ≤ deltaStar d L N) (hsmall : cK2 d L N * (R * δ₁) < bgC0 d L N / 2)
  (hnum : cK2 d L N * δ₁ ≤ c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
  (hnum' : cK2' d L N (famConst d L BG₂ κ) * δ₁ ≤
    c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
  (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
  (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
  (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
  (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4) (hp₁ : 0 < S.p₁) {cψ : ℝ} (hcψ : 0 ≤ cψ)
  (hpc : S.p₁ < cψ)
  (hδ₁ : Real.sqrt N * (‖((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ *
    (covSupConstC d L N (compWeight L S.a₁ k) κ * cψ)) < δ₁)

variable {τι : Type*} [DecidableEq τι] (𝒯E : Finset τι) {ϱ₁ ϱ₂ : τι → ℝ}
  {GkE : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₁ τ)}
  {GjE : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₂ τ)} {r₀ δ₃ δfl : ℝ}
  {X₀E X₁E : τι → Finset (CTorus d L N₁ m₁ (k + 1))} {jE : τι → ℕ}
  (hBE : ∀ τ ∈ 𝒯E, BgSetting N S.G' (GkE τ) (GjE τ) S.a₁ S.ν c BG κ r₀ eps δ₃ (X₀E τ) (X₁E τ)
    (jE τ))
  (hFE : ∀ τ ∈ 𝒯E, FlSetting N S.G' (GkE τ) (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν κ BG eps δ₃ Kc Cx c₂
    BG₂ δ₁ δfl (X₁E τ))
  {EE : τι → RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ}
  (hEanE : ∀ τ ∈ 𝒯E, AnalyticOnNhd ℂ (EE τ) (XiCRaw (GjE τ) (compWeight L S.a₁) S.ν (jE τ)
    (scaledC0 d) (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)))
  (hmatchE : OldEnergyHatMatch S C 𝒯E hBE hFE EE)

variable {μι : Type*} [DecidableEq μι] (𝒯M : Finset μι) {ϱ₁M ϱ₂M : μι → ℝ}
  {GkM : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₁M τ)}
  {GjM : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₂M τ)}
  {X₀M X₁M : μι → Finset (CTorus d L N₁ m₁ (k + 1))} {jM : μι → ℕ}
  (ys : μι → CTorus d L N₁ m₁ (k + 1)) (is : μι → Fin N)
  (hBM : ∀ τ ∈ 𝒯M, BgSetting N S.G' (GkM τ) (GjM τ) S.a₁ S.ν c BG κ r₀ eps δ₃ (X₀M τ) (X₁M τ)
    (jM τ))
  (hFM : ∀ τ ∈ 𝒯M, FlSetting N S.G' (GkM τ) (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν κ BG eps δ₃ Kc Cx c₂
    BG₂ δ₁ δfl (X₁M τ))
  {EM : μι → RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ}
  (hEanM : ∀ τ ∈ 𝒯M, AnalyticOnNhd ℂ (EM τ) (XiCRaw (GjM τ) (compWeight L S.a₁) S.ν (jM τ)
    (scaledC0 d) (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)))
  (g : Fld d L N₁ m₁ (k + 1) N)
  (hmatchM : OldObsHatMatch S C g 𝒯M ys is hBM hFM EM)

include hC R0 hlt hD hc7 hR hsmR hRs hsmall hnum hnum' hMX hdm hα hsm hp₁ hcψ hpc hδ₁ hEanE hmatchE in
/-- **The first segment at the scaled hat variable.**  With the hat variable `s ψ̂` and the
parameter `σ = 1` the potential part needs no rescaling: for `s ∈ [0,1]` on the support of
`ν_{p₁}`,
`(-β) raySrc3 (hat expansion) (s ψ̂) (s ψ̂) 1 Θ + β ∑_τ dirTermSrc (old term τ) (s ψ̂) (s ψ̂) 1 Θ
  = W₁(s, ψ̂)`.
(`Wone_eq_hat_of_oldEnergyHatMatch` at the parameter `1` and the fluctuation variable `s ψ̂`.) -/
theorem hatParts_first_scaled_of_oldEnergyHatMatch {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) {x : S.E}
    (hx : chiFl S.U N S.p₁ x = 1) :
    (-(S.β : ℂ)) * raySrc3 (hatFun S.G' S.a₁ S.ν eps S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
        (interactionOne S.hG S.hG' (le_refl (k + 1)) S.a₁ S.ν eps)) taylorWeight
        ((s : ℂ) • S.hatC x) ((s : ℂ) • S.hatC x) 1 (rawOf S.D') +
      (S.β : ℂ) * ∑ τ ∈ 𝒯E, (if h : τ ∈ 𝒯E then
        dirTermSrc (hatFun S.G' S.a₁ S.ν eps S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
          (flComp (hBE τ h) (hFE τ h) (EE τ))) (fun _ => (1 : ℂ)) ((s : ℂ) • S.hatC x)
          ((s : ℂ) • S.hatC x) 1 (rawOf S.D') else 0) = S.Wone C s x := by
  have h := S.Wone_eq_hat_of_oldEnergyHatMatch (C := C) (hC := hC) (R0 := R0) (hlt := hlt) (hD := hD) (hc7 := hc7) (hR := hR)
    (hsmR := hsmR) (hRs := hRs) (hsmall := hsmall) (hnum := hnum) (hnum' := hnum') (hMX := hMX)
    (hdm := hdm) (hα := hα) (hsm := hsm) (hp₁ := hp₁) (hcψ := hcψ) (hpc := hpc) (hδ₁ := hδ₁)
    (𝒯E := 𝒯E) (hBE := hBE) (hFE := hFE) (hEanE := hEanE) (hmatchE := hmatchE) (s := 1) ⟨zero_le_one, le_rfl⟩ (S.chiFl_smul_eq_one hp₁ hs hx)
  rw [S.hatC_smul, S.Wone_one_smul] at h
  simpa only [Complex.ofReal_one, one_pow, one_mul] using h

include hC R0 hlt hD hc7 hR hsmR hRs hsmall hnum hnum' hMX hdm hα hsm hp₁ hcψ hpc hδ₁ hEanM hmatchM in
/-- **The second segment at the scaled hat variable**: for `t ∈ [0,1]` on the support of `ν_{p₁}`,
the source parts of the expansion at the hat variable `t ψ̂` and the parameter `σ = 1` are
`W₂(t, ψ̂; g)`.  (`Wtwo_eq_hat_of_oldObsHatMatch` at the parameter `1` and the fluctuation variable
`t ψ̂`.) -/
theorem hatParts_second_scaled_of_oldObsHatMatch {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) {x : S.E}
    (hx : chiFl S.U N S.p₁ x = 1) :
    (S.β : ℂ) * (∑ s : CTorus d L N₁ m₁ (k + 1) × Fin N, (g s.1 s.2 / (S.β : ℂ)) *
        dirTermSrc (hatFun S.G' S.a₁ S.ν eps S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
          (onXi S.G' S.a₁ S.ν eps
            (fun D ψ' => svec (stepG d L N₁ m₁ k ϱ)
              (flFieldOne S.G' (stepG d L N₁ m₁ k ϱ) BG₂ κ S.a₁ S.ν D ψ') s.1 s.2)))
          (fun _ => (1 : ℂ)) ((t : ℂ) • S.hatC x) ((t : ℂ) • S.hatC x) 1 (rawOf S.D')) +
      (S.β : ℂ) * ∑ τ ∈ 𝒯M, (if h : τ ∈ 𝒯M then
        (g (ys τ) (is τ) / (S.β : ℂ)) *
          dirTermSrc (hatFun S.G' S.a₁ S.ν eps S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
            (flComp (hBM τ h) (hFM τ h) (EM τ))) (fun _ => (1 : ℂ)) ((t : ℂ) • S.hatC x)
            ((t : ℂ) • S.hatC x) 1 (rawOf S.D') else 0) = S.Wtwo C g t x := by
  have h := S.Wtwo_eq_hat_of_oldObsHatMatch (C := C) (hC := hC) (R0 := R0) (hlt := hlt) (hD := hD) (hc7 := hc7) (hR := hR)
    (hsmR := hsmR) (hRs := hRs) (hsmall := hsmall) (hnum := hnum) (hnum' := hnum') (hMX := hMX)
    (hdm := hdm) (hα := hα) (hsm := hsm) (hp₁ := hp₁) (hcψ := hcψ) (hpc := hpc) (hδ₁ := hδ₁)
    (𝒯M := 𝒯M) (ys := ys) (is := is) (hBM := hBM) (hFM := hFM) (hEanM := hEanM) (g := g)
    (hmatchM := hmatchM) (t := 1) ⟨zero_le_one, le_rfl⟩ (S.chiFl_smul_eq_one hp₁ ht hx)
  rw [S.hatC_smul, S.Wtwo_one_smul] at h
  simpa only [Complex.ofReal_one] using h

include hC R0 hlt hD hc7 hR hsmR hRs hsmall hnum hnum' hMX hdm hα hsm hp₁ hcψ hpc hδ₁ hEanE hmatchE in
/-- **T3, source `0`: the function expanded by the physical expansion is the first exponent.**
At the scaled hat variable `s ψ̂` (in both slots), the parameter `σ = 1` and the source datum
`(rawOf D', 0)`, for `s ∈ [0,1]` on the support of `ν_{p₁}`,
`physVal (s ψ̂, s ψ̂) (s ψ̂, s ψ̂) 1 (Θ, 0) = W₁(s, ψ̂)`.
The observable functionals are arbitrary (they are multiplied by the source `0`). -/
theorem physVal_scaled_eq_Wone_of_oldEnergyHatMatch {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) {x : S.E}
    (hx : chiFl S.U N S.p₁ x = 1) :
    physVal (EE := EE) (EM := EM) S (S.β : ℂ) S.hG ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) 𝒯E hBE hFE 𝒯M ys is hBM hFM (0 : ℂ)
        ((s : ℂ) • S.hatC x, (s : ℂ) • S.hatC x) ((s : ℂ) • S.hatC x, (s : ℂ) • S.hatC x) 1
        (rawOf S.D', (0 : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)) = S.Wone C s x := by
  rw [← S.hatParts_first_scaled_of_oldEnergyHatMatch (C := C) (hC := hC) (R0 := R0) (hlt := hlt) (hD := hD) (hc7 := hc7) (hR := hR)
    (hsmR := hsmR) (hRs := hRs) (hsmall := hsmall) (hnum := hnum) (hnum' := hnum') (hMX := hMX)
    (hdm := hdm) (hα := hα) (hsm := hsm) (hp₁ := hp₁) (hcψ := hcψ) (hpc := hpc) (hδ₁ := hδ₁)
    (𝒯E := 𝒯E) (hBE := hBE) (hFE := hFE) (hEanE := hEanE) (hmatchE := hmatchE) hs hx]
  unfold physVal
  simp only [Pi.zero_apply, zero_mul, mul_zero, Finset.sum_const_zero, add_zero, dite_eq_ite,
    ite_self]

include hC R0 hlt hD hc7 hR hsmR hRs hsmall hnum hnum' hMX hdm hα hsm hp₁ hcψ hpc hδ₁ hEanM hmatchM in
/-- **T3, the source part: the difference of the expanded functions at the sources `g` and `0` is
the second exponent.**  At the scaled hat variable `t ψ̂` and the parameter `σ = 1`, for
`t ∈ [0,1]` on the support of `ν_{p₁}`,
`physVal (t ψ̂, t ψ̂) (t ψ̂, t ψ̂) 1 (Θ, g/β) - physVal (t ψ̂, t ψ̂) (t ψ̂, t ψ̂) 1 (Θ, 0) = W₂(t, ψ̂; g)`.
The old energy functionals are arbitrary (they cancel). -/
theorem physVal_scaled_sub_eq_Wtwo_of_oldObsHatMatch {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) {x : S.E}
    (hx : chiFl S.U N S.p₁ x = 1) :
    physVal (EE := EE) (EM := EM) S (S.β : ℂ) S.hG ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) 𝒯E hBE hFE 𝒯M ys is hBM hFM (0 : ℂ)
        ((t : ℂ) • S.hatC x, (t : ℂ) • S.hatC x) ((t : ℂ) • S.hatC x, (t : ℂ) • S.hatC x) 1
        (rawOf S.D', fun y i => g y i / (S.β : ℂ)) -
      physVal (EE := EE) (EM := EM) S (S.β : ℂ) S.hG ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) 𝒯E hBE hFE 𝒯M ys is hBM hFM (0 : ℂ)
        ((t : ℂ) • S.hatC x, (t : ℂ) • S.hatC x) ((t : ℂ) • S.hatC x, (t : ℂ) • S.hatC x) 1
        (rawOf S.D', (0 : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)) = S.Wtwo C g t x := by
  rw [← S.hatParts_second_scaled_of_oldObsHatMatch (C := C) (hC := hC) (R0 := R0) (hlt := hlt) (hD := hD) (hc7 := hc7) (hR := hR)
    (hsmR := hsmR) (hRs := hRs) (hsmall := hsmall) (hnum := hnum) (hnum' := hnum') (hMX := hMX)
    (hdm := hdm) (hα := hα) (hsm := hsm) (hp₁ := hp₁) (hcψ := hcψ) (hpc := hpc) (hδ₁ := hδ₁)
    (𝒯M := 𝒯M) (ys := ys) (is := is) (hBM := hBM) (hFM := hFM) (hEanM := hEanM) (g := g)
    (hmatchM := hmatchM) ht hx]
  unfold physVal
  simp only [Pi.zero_apply, zero_mul, mul_zero, Finset.sum_const_zero, add_zero, dite_eq_ite,
    ite_self]
  ring

include hC R0 hlt hD hc7 hR hsmR hRs hsmall hnum hnum' hMX hdm hα hsm hp₁ hcψ hpc hδ₁ hEanE hmatchE hEanM hmatchM in
/-- **T3: the function expanded by the physical expansion is the step exponent of the class.**
At the hat variables `s ψ̂` (potential and old energy slot) and `t ψ̂` (source slot), the parameter
`σ = 1` and the source datum `(rawOf D', g/β)`, for `s, t ∈ [0,1]` on the support of `ν_{p₁}`,

`physVal (s ψ̂, t ψ̂) (s ψ̂, t ψ̂) 1 (Θ, g/β) = W₁(s, ψ̂) + W₂(t, ψ̂; g)`,

with `c_β = β`, `c_ν = 0` and `cc = β_k^{-1/2}`. -/
theorem physVal_eq_stepExponent_of_oldHatMatch {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (ht : t ∈ Icc (0 : ℝ) 1) {x : S.E} (hx : chiFl S.U N S.p₁ x = 1) :
    physVal (EE := EE) (EM := EM) S (S.β : ℂ) S.hG ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) 𝒯E hBE hFE 𝒯M ys is hBM hFM (0 : ℂ)
        ((s : ℂ) • S.hatC x, (t : ℂ) • S.hatC x) ((s : ℂ) • S.hatC x, (t : ℂ) • S.hatC x) 1
        (rawOf S.D', fun y i => g y i / (S.β : ℂ)) = S.Wone C s x + S.Wtwo C g t x := by
  rw [← S.hatParts_first_scaled_of_oldEnergyHatMatch (C := C) (hC := hC) (R0 := R0) (hlt := hlt) (hD := hD) (hc7 := hc7) (hR := hR)
    (hsmR := hsmR) (hRs := hRs) (hsmall := hsmall) (hnum := hnum) (hnum' := hnum') (hMX := hMX)
    (hdm := hdm) (hα := hα) (hsm := hsm) (hp₁ := hp₁) (hcψ := hcψ) (hpc := hpc) (hδ₁ := hδ₁)
    (𝒯E := 𝒯E) (hBE := hBE) (hFE := hFE) (hEanE := hEanE) (hmatchE := hmatchE) hs hx,
    ← S.hatParts_second_scaled_of_oldObsHatMatch (C := C) (hC := hC) (R0 := R0) (hlt := hlt) (hD := hD) (hc7 := hc7) (hR := hR)
    (hsmR := hsmR) (hRs := hRs) (hsmall := hsmall) (hnum := hnum) (hnum' := hnum') (hMX := hMX)
    (hdm := hdm) (hα := hα) (hsm := hsm) (hp₁ := hp₁) (hcψ := hcψ) (hpc := hpc) (hδ₁ := hδ₁)
    (𝒯M := 𝒯M) (ys := ys) (is := is) (hBM := hBM) (hFM := hFM) (hEanM := hEanM) (g := g)
    (hmatchM := hmatchM) ht hx]
  unfold physVal
  simp only [zero_mul, add_zero]
  ring

include hC R0 hlt hD hc7 hR hsmR hRs hsmall hnum hnum' hMX hdm hα hsm hp₁ hcψ hpc hδ₁ hEanE hmatchE hEanM hmatchM in
/-- **The expanded function at the hat variable `ψ̂` and the parameter `σ = u` is not the step
exponent of a general class.**  For `u ∈ [0,1]` on the support of `ν_{p₁}`,

`physVal (ψ̂, ψ̂) (ψ̂, ψ̂) u (Θ, g/β) = W₁(u, ψ̂) + W₂(u, ψ̂; g) + (1 - u²) · (-β) raySrc3(…) ψ̂ ψ̂ u Θ`.

The Taylor factor `u²` belongs to the potential part alone, so the rescaling of the activities by
`s²` in `stepActivityBound_zeroClass_of_directTerms_fields` gives the first exponent only when the
expansion has no old terms.  This is why the general assembler evaluates the expansion at the
scaled hat variable and `σ = 1` (`physVal_eq_stepExponent_of_oldHatMatch`). -/
theorem physVal_diag_eq_of_oldHatMatch {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) {x : S.E}
    (hx : chiFl S.U N S.p₁ x = 1) :
    physVal (EE := EE) (EM := EM) S (S.β : ℂ) S.hG ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) 𝒯E hBE hFE 𝒯M ys is hBM hFM (0 : ℂ)
        (S.hatC x, S.hatC x) (S.hatC x, S.hatC x) (u : ℂ)
        (rawOf S.D', fun y i => g y i / (S.β : ℂ)) =
      S.Wone C u x + S.Wtwo C g u x + (1 - (u : ℂ) ^ 2) * ((-(S.β : ℂ)) * raySrc3 (hatFun S.G' S.a₁ S.ν eps S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
        (interactionOne S.hG S.hG' (le_refl (k + 1)) S.a₁ S.ν eps)) taylorWeight (S.hatC x)
        (S.hatC x) (u : ℂ) (rawOf S.D')) := by
  rw [← S.Wone_eq_hat_of_oldEnergyHatMatch (C := C) (hC := hC) (R0 := R0) (hlt := hlt) (hD := hD) (hc7 := hc7) (hR := hR)
    (hsmR := hsmR) (hRs := hRs) (hsmall := hsmall) (hnum := hnum) (hnum' := hnum') (hMX := hMX)
    (hdm := hdm) (hα := hα) (hsm := hsm) (hp₁ := hp₁) (hcψ := hcψ) (hpc := hpc) (hδ₁ := hδ₁)
    (𝒯E := 𝒯E) (hBE := hBE) (hFE := hFE) (hEanE := hEanE) (hmatchE := hmatchE) hu hx,
    ← S.Wtwo_eq_hat_of_oldObsHatMatch (C := C) (hC := hC) (R0 := R0) (hlt := hlt) (hD := hD) (hc7 := hc7) (hR := hR)
    (hsmR := hsmR) (hRs := hRs) (hsmall := hsmall) (hnum := hnum) (hnum' := hnum') (hMX := hMX)
    (hdm := hdm) (hα := hα) (hsm := hsm) (hp₁ := hp₁) (hcψ := hcψ) (hpc := hpc) (hδ₁ := hδ₁)
    (𝒯M := 𝒯M) (ys := ys) (is := is) (hBM := hBM) (hFM := hFM) (hEanM := hEanM) (g := g)
    (hmatchM := hmatchM) hu hx]
  unfold physVal
  simp only [zero_mul, add_zero]
  ring

end StepSetting

end Value

section Main

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ} {c BG κ eps : ℝ}

/-- The paired sharp agreement of the diagonal pairs is preserved by the scalings `ψ̂ ↦ t ψ̂`. -/
theorem agFDirPair_smul (S : StepSetting d L N₁ m₁ k N ϱ) (t : ℝ)
    (Y : Set (CTorus d L N₁ m₁ (k + 1))) (ψ ψ' : S.U × Fin N → ℂ)
    (h : AgFDirPair S Y (ψ, ψ) (ψ', ψ')) :
    AgFDirPair S Y ((t : ℂ) • ψ, (t : ℂ) • ψ) ((t : ℂ) • ψ', (t : ℂ) • ψ') := by
  have e : ∀ y ∈ Y, ∀ i, ((t : ℂ) • ψ) (unitPt S.hG' y, i) = ((t : ℂ) • ψ') (unitPt S.hG' y, i) :=
    fun y hy i => by
      have h1 : ψ (unitPt S.hG' y, i) = ψ' (unitPt S.hG' y, i) := h.1 y hy i
      show (t : ℂ) * ψ (unitPt S.hG' y, i) = (t : ℂ) * ψ' (unitPt S.hG' y, i)
      rw [h1]
  exact ⟨e, e⟩

/-- **T4: the step activity bound of a general class with the preserved rate** (source `0`).  Let
`C` be a class whose old energy is represented by the old-term functionals `EE τ` of the expansion
(`OldEnergyHatMatch`, the named open hypothesis).  Under the hypotheses of
`stepActivityBound_zeroClass_direct` on the expansion (now for a nonempty family of old terms), the
rate hypothesis `κ' + 3κ₀ + c₁ + 3/2 ≤ 2κ_dec - 1` and the smallness
`R_σ ε_U ≤ [8 K_c'^3 c₁ exp((2κ_dec - 1 - 2κ₀) c_G + c₁ + κ' c_G)]⁻¹`, there is a step activity
bound of `C` for the source `0` with the rate `κ_H = 2 κ_dec - 1` and prefactor `ε_H = R_σ ε_U`.
The observable functionals `EM τ` are arbitrary (the source is `0`). -/
theorem stepActivityBound_direct_of_oldEnergyHatMatch
    (S : StepSetting d L N₁ m₁ k N ϱ) (C : StepClass d L N₁ m₁ k N ϱ)
    {ρ εU κ0 κ' Kc' : ℝ} {Kc Cx c₂ BG₂ δ₁ : ℝ}
    (hC : FlCore N S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hconn : HatConn S.G')
    (hrow : RowInHat (coverOf S.G') (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) S.ν)
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    {R₁ : ℝ} (hR₁ : 1 < R₁) {r Rσ : ℝ} (hr : 0 < r)
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsmX : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hδ₁ : Real.sqrt N * (‖((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ *
      (covSupConstC d L N (compWeight L S.a₁ k) κ * cψ)) < δ₁)
    (hc7 : c7 d L N BG κ ≤ thm73C3 d L N)
    {R : ℝ} (hR : 2 ≤ R) (hRs : R * δ₁ ≤ deltaStar d L N)
    (hsmall : cK2 d L N * (R * δ₁) < bgC0 d L N / 2)
    (hnum : cK2 d L N * δ₁ ≤ c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hnum' : cK2' d L N (famConst d L BG₂ κ) * δ₁ ≤
      c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hsm : 2 * (compC4 d * (bgK1 d L N * (xiC1 d * eps))) + 5 * (R * δ₁) ≤ bgC1 d L N)
    {m₀ : ℕ} {jV : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → ℕ}
    {XV 𝒦XV : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Set (CTorus d L N₁ m₁ (k + 1))}
    {X₁V : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Finset (CTorus d L N₁ m₁ (k + 1))}
    (hcovV : ∀ z, CovSetup S.G' (m₀) (jV z) (XV z) (𝒦XV z))
    (hX₁V : ∀ z, (↑(X₁V z) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 S.G' (m₀) (jV z) (𝒦XV z))
    (hoptV : ∀ z, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XV z) ∧ MeetsOne (m₀) (jV z) (𝒦XV z) W₀ ∧
        bondCost (scaleW L (m₀) m₁ (jV z)) E₀ = treeLenCovOne (m₀) (jV z) (XV z))
    (hΔV : ∀ z, treeLenCovOne (m₀) (jV z) (XV z) = 0)
    (hlogV : ∀ _z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))),
      Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤
      (κ / 2 - 1) / 2)
    (hZV : ∀ z, readSites (stepG d L N₁ m₁ k ϱ) k z ⊆ ↑(X₁V z))
    (hmarV : ∀ z, BlockMargin S.G' (X₁V z)
      (↑(blockSites d L N₁ m₁ (k + 1) k z) : Set (CTorus d L N₁ m₁ (k + 1))))
    {τι : Type*} [DecidableEq τι] (𝒯E : Finset τι) {ϱ₁ ϱ₂ : τι → ℝ}
    {GkE : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₁ τ)}
    {GjE : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₂ τ)} {r₀ δ₃ δfl : ℝ}
    {X₀E X₁E : τι → Finset (CTorus d L N₁ m₁ (k + 1))} {jE : τι → ℕ}
    {XE 𝒦XE : τι → Set (CTorus d L N₁ m₁ (k + 1))} {EbE : τι → ℝ}
    (hBE : ∀ τ ∈ 𝒯E, BgSetting N S.G' (GkE τ) (GjE τ) S.a₁ S.ν c BG κ r₀ eps δ₃ (X₀E τ)
      (X₁E τ) (jE τ))
    (hFE : ∀ τ ∈ 𝒯E, FlSetting N S.G' (GkE τ) (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν κ BG eps δ₃
      Kc Cx c₂ BG₂ δ₁ δfl (X₁E τ))
    (hcovE : ∀ τ ∈ 𝒯E, CovSetup S.G' (m₀) (jE τ) (XE τ) (𝒦XE τ))
    (hX₁E : ∀ τ ∈ 𝒯E, (↑(X₁E τ) : Set (CTorus d L N₁ m₁ (k + 1))) =
      X1 S.G' (m₀) (jE τ) (𝒦XE τ))
    (hoptE : ∀ τ ∈ 𝒯E, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XE τ) ∧ MeetsOne (m₀) (jE τ) (𝒦XE τ) W₀ ∧
        bondCost (scaleW L (m₀) m₁ (jE τ)) E₀ = treeLenCovOne (m₀) (jE τ) (XE τ))
    (hlogE : ∀ τ ∈ 𝒯E, Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) *
      (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hEbE : ∀ τ ∈ 𝒯E, 0 ≤ EbE τ) {EE : τι → RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ}
    (hEanE : ∀ τ ∈ 𝒯E, AnalyticOnNhd ℂ (EE τ) (XiCRaw (GjE τ) (compWeight L S.a₁) S.ν (jE τ)
      (scaledC0 d) (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)))
    (hEbdE : ∀ τ ∈ 𝒯E, ∀ r ∈ XiCRaw (GjE τ) (compWeight L S.a₁) S.ν (jE τ) (scaledC0 d)
      (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      ‖EE τ r‖ ≤ EbE τ * Real.exp (-(κdec - 1) * treeLenCovOne (m₀) (jE τ) (XE τ)))
    {jF : CTorus d L N₁ m₁ (k + 1) × Fin N → ℕ}
    {XF 𝒦XF : CTorus d L N₁ m₁ (k + 1) × Fin N → Set (CTorus d L N₁ m₁ (k + 1))}
    {X₁F : CTorus d L N₁ m₁ (k + 1) × Fin N → Finset (CTorus d L N₁ m₁ (k + 1))}
    (hcovF : ∀ s, CovSetup S.G' (m₀) (jF s) (XF s) (𝒦XF s))
    (hX₁F : ∀ s, (↑(X₁F s) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 S.G' (m₀) (jF s) (𝒦XF s))
    (hoptF : ∀ s, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XF s) ∧ MeetsOne (m₀) (jF s) (𝒦XF s) W₀ ∧
        bondCost (scaleW L (m₀) m₁ (jF s)) E₀ = treeLenCovOne (m₀) (jF s) (XF s))
    (hΔF : ∀ s, treeLenCovOne (m₀) (jF s) (XF s) = 0)
    (hlogF : ∀ _s : CTorus d L N₁ m₁ (k + 1) × Fin N,
      Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤
      (κ / 2 - 1) / 2)
    (hyF : ∀ s : CTorus d L N₁ m₁ (k + 1) × Fin N, s.1 ∈ X₁F s)
    {μι : Type*} [DecidableEq μι] (𝒯M : Finset μι) {ϱ₁M ϱ₂M : μι → ℝ}
    {GkM : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₁M τ)}
    {GjM : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₂M τ)}
    {X₀M X₁M : μι → Finset (CTorus d L N₁ m₁ (k + 1))} {jM : μι → ℕ}
    {XM 𝒦XM : μι → Set (CTorus d L N₁ m₁ (k + 1))} {EbM : μι → ℝ}
    (ys : μι → CTorus d L N₁ m₁ (k + 1)) (is : μι → Fin N) (hys : ∀ τ ∈ 𝒯M, ys τ ∈ X₁M τ)
    (hBM : ∀ τ ∈ 𝒯M, BgSetting N S.G' (GkM τ) (GjM τ) S.a₁ S.ν c BG κ r₀ eps δ₃ (X₀M τ)
      (X₁M τ) (jM τ))
    (hFM : ∀ τ ∈ 𝒯M, FlSetting N S.G' (GkM τ) (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν κ BG eps δ₃
      Kc Cx c₂ BG₂ δ₁ δfl (X₁M τ))
    (hcovM : ∀ τ ∈ 𝒯M, CovSetup S.G' (m₀) (jM τ) (XM τ) (𝒦XM τ))
    (hX₁M : ∀ τ ∈ 𝒯M, (↑(X₁M τ) : Set (CTorus d L N₁ m₁ (k + 1))) =
      X1 S.G' (m₀) (jM τ) (𝒦XM τ))
    (hoptM : ∀ τ ∈ 𝒯M, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XM τ) ∧ MeetsOne (m₀) (jM τ) (𝒦XM τ) W₀ ∧
        bondCost (scaleW L (m₀) m₁ (jM τ)) E₀ = treeLenCovOne (m₀) (jM τ) (XM τ))
    (hlogM : ∀ τ ∈ 𝒯M, Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) *
      (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hEbM : ∀ τ ∈ 𝒯M, 0 ≤ EbM τ) {EM : μι → RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ}
    (hEanM : ∀ τ ∈ 𝒯M, AnalyticOnNhd ℂ (EM τ) (XiCRaw (GjM τ) (compWeight L S.a₁) S.ν (jM τ)
      (scaledC0 d) (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)))
    (hEbdM : ∀ τ ∈ 𝒯M, ∀ r ∈ XiCRaw (GjM τ) (compWeight L S.a₁) S.ν (jM τ) (scaledC0 d)
      (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      ‖EM τ r‖ ≤ EbM τ * Real.exp (-(κdec - 1) * treeLenCovOne (m₀) (jM τ) (XM τ)))
    (rE : τι → CTorus d L N₁ m₁ (k + 1)) (hrE : ∀ τ ∈ 𝒯E, rE τ ∈ X₁E τ) {ρE : ℝ} (hρE0 : 0 ≤ ρE)
    (hρE : ∀ x : CTorus d L N₁ m₁ (k + 1), ∑ τ ∈ 𝒯E.filter (fun τ => rE τ = x),
      EbE τ * Real.exp (-κ₀ * treeLenCovOne m₀ (jE τ) (XE τ)) ≤ ρE)
    {ρM : ℝ} (hρM0 : 0 ≤ ρM)
    (hρM : ∀ p : CTorus d L N₁ m₁ (k + 1) × Fin N, ∑ τ ∈ 𝒯M.filter (fun τ => (ys τ, is τ) = p),
      EbM τ * Real.exp (-κ₀ * treeLenCovOne m₀ (jM τ) (XM τ)) ≤ ρM)
    {Bh : ℝ} (hBh0 : 0 ≤ Bh)
    (hBh : ∀ D : BgData S.G' N, XiCData S.G' (compWeight L S.a₁) S.ν (k + 1) 1 eps D →
      ∀ x i, ‖D.h x i‖ ≤ Bh)
    (hZν : ∀ z, (↑(blockSites d L N₁ m₁ (k + 1) k z) : Set (CTorus d L N₁ m₁ (k + 1))) ⊆
      ↑(X₁V z))
    (hc : (Rσ * R₁ + r) * ρ < cψ)
    (hD : XiCData S.G' (compWeight L S.a₁) S.ν (k + 1) 1 eps S.D')
    (hN : L ^ m₀ ∣ N₁) (hp : 0 < S.p₁) (hpρ : S.p₁ ≤ ρ)
    (hεpos : 0 < εU)
    (hεb : prop33Eps d L N m₁ k m₀ S.a₁ S.ν BG BG₂ κ δ₁ r ρE ρM * ‖(S.β : ℂ)‖ +
      ‖(0 : ℂ)‖ * (1 * (c1 d L * ((L : ℝ) ^ (m₀ + m₁)) ^ d *
        nuBd d L N k (cK2' d L N (famConst d L BG₂ κ) * δ₁)
          (K4 d L N BG κ * (xiC1 d * eps) + (1 + 3 * (xiC1 d * eps)) + Bh) / r)) ≤ εU)
    (hκE : aEnt d L + 1 ≤ κ0) (hKc : K0 d L κ0 + 1 ≤ Kc') (hκ' : 0 ≤ κ')
    (hκa : κ' + 3 * κ0 + c1 d L + 3 / 2 ≤ 2 * κdec - 1)
    (hDA : Rσ * εU ≤ 1 / (8 * Kc' ^ 3 * c1 d L *
      Real.exp ((2 * κdec - 1 - 2 * κ0) * cG d L + c1 d L + κ' * cG d L)))
    {pp : ℝ} (R0 : S.RayData pp) (hlt : S.p₁ < pp) (hRσ1 : 1 < Rσ)
    (hmatchE : OldEnergyHatMatch S C 𝒯E hBE hFE EE) :
    ∃ B : StepActivityBound S C 0, B.κH = 2 * κdec - 1 ∧ B.εH = Rσ * εU := by
  classical
  have hpc : S.p₁ < cψ := p₁_lt_of_margin hp hpρ hRσ1 hR₁ hr hc
  have hRσ : 0 < Rσ := by linarith
  obtain ⟨I, -, -, -⟩ := physical_directTerms
    (S := S) (cβ := (S.β : ℂ)) (hk := S.hk1) (hG := S.hG)
    (cc := ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) (ha₁ := R0.ha₁) (H := R0.H) (cν := (0 : ℂ))
    (hRσ := hRσ) (Θ₀ := (rawOf S.D', (0 : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)))
    (hΘ₀ := ⟨⟨S.D', hD, rfl⟩, by simp [l1Ball]⟩) (hC := hC) (hconn := hconn) (hrow := hrow)
    (hκ₀ := hκ₀) (hκdec := hκdec) (hκ := hκ) (h1 := h1) (hR₁ := hR₁) (hr := hr) (hcψ := hcψ)
    (hMX := hMX) (hdm := hdm) (hα := hα) (hsmX := hsmX) (hδ₁ := hδ₁) (hc7 := hc7) (hR := hR)
    (hRs := hRs) (hsmall := hsmall) (hnum := hnum) (hnum' := hnum') (hsm := hsm) (hcovV := hcovV)
    (hX₁V := hX₁V) (hoptV := hoptV) (hΔV := hΔV) (hlogV := hlogV) (hZV := hZV) (hmarV := hmarV)
    (𝒯E := 𝒯E) (hBE := hBE) (hFE := hFE) (hcovE := hcovE) (hX₁E := hX₁E) (hoptE := hoptE)
    (hlogE := hlogE) (hEbE := hEbE) (hEanE := hEanE) (hEbdE := hEbdE) (hcovF := hcovF)
    (hX₁F := hX₁F) (hoptF := hoptF) (hΔF := hΔF) (hlogF := hlogF) (hyF := hyF) (𝒯M := 𝒯M)
    (ys := ys) (is := is) (hys := hys) (hBM := hBM) (hFM := hFM) (hcovM := hcovM) (hX₁M := hX₁M)
    (hoptM := hoptM) (hlogM := hlogM) (hEbM := hEbM) (hEanM := hEanM) (hEbdM := hEbdM) (rE := rE)
    (hrE := hrE) (hρE0 := hρE0) (hρE := hρE) (hρM0 := hρM0) (hρM := hρM) (hBh0 := hBh0)
    (hBh := hBh) (hZν := hZν) (hc := hc) (hεb := hεb) (hN := hN) (hp := hp)
  refine stepActivityBound_of_directTerms_scaled S C I
    (fun t Y ψ ψ' h => agFDirPair_smul S t Y ψ ψ' h) ?_ hN hpρ hεpos hκE hKc hκ' hκa hDA hRσ1
  intro s hs x hx
  exact S.physVal_scaled_eq_Wone_of_oldEnergyHatMatch
    (C := C) (hC := hC) (R0 := R0) (hlt := hlt) (hD := hD) (hc7 := hc7) (hR := hR) (hsmR := hsm)
    (hRs := hRs) (hsmall := hsmall) (hnum := hnum) (hnum' := hnum') (hMX := hMX) (hdm := hdm)
    (hα := hα) (hsm := hsmX) (hp₁ := hp) (hcψ := hcψ) (hpc := hpc) (hδ₁ := hδ₁) (𝒯E := 𝒯E)
    (hBE := hBE) (hFE := hFE) (hEanE := hEanE) (hmatchE := hmatchE) (𝒯M := 𝒯M) (ys := ys)
    (is := is) (hBM := hBM) (hFM := hFM) (EM := EM) hs hx

/-- **T4 with a source: the step activity bound of a general class for the source `g`.**  Let the
old energy and the old observable terms of `C` (for the source `g`, with `‖g/β‖₁ < 1`) be
represented by the old-term functionals of the expansion (`OldEnergyHatMatch`, `OldObsHatMatch`).
Under the hypotheses of `stepActivityBound_direct_of_oldEnergyHatMatch` with the smallness
`2 R_σ ε_U ≤ [8 (2K_c')^3 c₁ exp((2κ_dec - 1 - 2κ₀) c_G + c₁ + κ' c_G)]⁻¹`, there is a step
activity bound of `C` for the source `g` with `κ_H = 2 κ_dec - 1`, `ε_H = 2 R_σ ε_U` and
`K_c = 2 K_c'` (two instances of the expansion, at the sources `0` and `g/β`). -/
theorem stepActivityBound_direct_source_of_oldHatMatch
    (S : StepSetting d L N₁ m₁ k N ϱ) (C : StepClass d L N₁ m₁ k N ϱ)
    (g : Fld d L N₁ m₁ (k + 1) N)
    {ρ εU κ0 κ' Kc' : ℝ} {Kc Cx c₂ BG₂ δ₁ : ℝ}
    (hC : FlCore N S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hconn : HatConn S.G')
    (hrow : RowInHat (coverOf S.G') (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) S.ν)
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    {R₁ : ℝ} (hR₁ : 1 < R₁) {r Rσ : ℝ} (hr : 0 < r)
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsmX : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hδ₁ : Real.sqrt N * (‖((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ *
      (covSupConstC d L N (compWeight L S.a₁ k) κ * cψ)) < δ₁)
    (hc7 : c7 d L N BG κ ≤ thm73C3 d L N)
    {R : ℝ} (hR : 2 ≤ R) (hRs : R * δ₁ ≤ deltaStar d L N)
    (hsmall : cK2 d L N * (R * δ₁) < bgC0 d L N / 2)
    (hnum : cK2 d L N * δ₁ ≤ c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hnum' : cK2' d L N (famConst d L BG₂ κ) * δ₁ ≤
      c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hsm : 2 * (compC4 d * (bgK1 d L N * (xiC1 d * eps))) + 5 * (R * δ₁) ≤ bgC1 d L N)
    {m₀ : ℕ} {jV : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → ℕ}
    {XV 𝒦XV : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Set (CTorus d L N₁ m₁ (k + 1))}
    {X₁V : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Finset (CTorus d L N₁ m₁ (k + 1))}
    (hcovV : ∀ z, CovSetup S.G' (m₀) (jV z) (XV z) (𝒦XV z))
    (hX₁V : ∀ z, (↑(X₁V z) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 S.G' (m₀) (jV z) (𝒦XV z))
    (hoptV : ∀ z, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XV z) ∧ MeetsOne (m₀) (jV z) (𝒦XV z) W₀ ∧
        bondCost (scaleW L (m₀) m₁ (jV z)) E₀ = treeLenCovOne (m₀) (jV z) (XV z))
    (hΔV : ∀ z, treeLenCovOne (m₀) (jV z) (XV z) = 0)
    (hlogV : ∀ _z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))),
      Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤
      (κ / 2 - 1) / 2)
    (hZV : ∀ z, readSites (stepG d L N₁ m₁ k ϱ) k z ⊆ ↑(X₁V z))
    (hmarV : ∀ z, BlockMargin S.G' (X₁V z)
      (↑(blockSites d L N₁ m₁ (k + 1) k z) : Set (CTorus d L N₁ m₁ (k + 1))))
    {τι : Type*} [DecidableEq τι] (𝒯E : Finset τι) {ϱ₁ ϱ₂ : τι → ℝ}
    {GkE : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₁ τ)}
    {GjE : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₂ τ)} {r₀ δ₃ δfl : ℝ}
    {X₀E X₁E : τι → Finset (CTorus d L N₁ m₁ (k + 1))} {jE : τι → ℕ}
    {XE 𝒦XE : τι → Set (CTorus d L N₁ m₁ (k + 1))} {EbE : τι → ℝ}
    (hBE : ∀ τ ∈ 𝒯E, BgSetting N S.G' (GkE τ) (GjE τ) S.a₁ S.ν c BG κ r₀ eps δ₃ (X₀E τ)
      (X₁E τ) (jE τ))
    (hFE : ∀ τ ∈ 𝒯E, FlSetting N S.G' (GkE τ) (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν κ BG eps δ₃
      Kc Cx c₂ BG₂ δ₁ δfl (X₁E τ))
    (hcovE : ∀ τ ∈ 𝒯E, CovSetup S.G' (m₀) (jE τ) (XE τ) (𝒦XE τ))
    (hX₁E : ∀ τ ∈ 𝒯E, (↑(X₁E τ) : Set (CTorus d L N₁ m₁ (k + 1))) =
      X1 S.G' (m₀) (jE τ) (𝒦XE τ))
    (hoptE : ∀ τ ∈ 𝒯E, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XE τ) ∧ MeetsOne (m₀) (jE τ) (𝒦XE τ) W₀ ∧
        bondCost (scaleW L (m₀) m₁ (jE τ)) E₀ = treeLenCovOne (m₀) (jE τ) (XE τ))
    (hlogE : ∀ τ ∈ 𝒯E, Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) *
      (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hEbE : ∀ τ ∈ 𝒯E, 0 ≤ EbE τ) {EE : τι → RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ}
    (hEanE : ∀ τ ∈ 𝒯E, AnalyticOnNhd ℂ (EE τ) (XiCRaw (GjE τ) (compWeight L S.a₁) S.ν (jE τ)
      (scaledC0 d) (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)))
    (hEbdE : ∀ τ ∈ 𝒯E, ∀ r ∈ XiCRaw (GjE τ) (compWeight L S.a₁) S.ν (jE τ) (scaledC0 d)
      (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      ‖EE τ r‖ ≤ EbE τ * Real.exp (-(κdec - 1) * treeLenCovOne (m₀) (jE τ) (XE τ)))
    {jF : CTorus d L N₁ m₁ (k + 1) × Fin N → ℕ}
    {XF 𝒦XF : CTorus d L N₁ m₁ (k + 1) × Fin N → Set (CTorus d L N₁ m₁ (k + 1))}
    {X₁F : CTorus d L N₁ m₁ (k + 1) × Fin N → Finset (CTorus d L N₁ m₁ (k + 1))}
    (hcovF : ∀ s, CovSetup S.G' (m₀) (jF s) (XF s) (𝒦XF s))
    (hX₁F : ∀ s, (↑(X₁F s) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 S.G' (m₀) (jF s) (𝒦XF s))
    (hoptF : ∀ s, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XF s) ∧ MeetsOne (m₀) (jF s) (𝒦XF s) W₀ ∧
        bondCost (scaleW L (m₀) m₁ (jF s)) E₀ = treeLenCovOne (m₀) (jF s) (XF s))
    (hΔF : ∀ s, treeLenCovOne (m₀) (jF s) (XF s) = 0)
    (hlogF : ∀ _s : CTorus d L N₁ m₁ (k + 1) × Fin N,
      Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤
      (κ / 2 - 1) / 2)
    (hyF : ∀ s : CTorus d L N₁ m₁ (k + 1) × Fin N, s.1 ∈ X₁F s)
    {μι : Type*} [DecidableEq μι] (𝒯M : Finset μι) {ϱ₁M ϱ₂M : μι → ℝ}
    {GkM : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₁M τ)}
    {GjM : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₂M τ)}
    {X₀M X₁M : μι → Finset (CTorus d L N₁ m₁ (k + 1))} {jM : μι → ℕ}
    {XM 𝒦XM : μι → Set (CTorus d L N₁ m₁ (k + 1))} {EbM : μι → ℝ}
    (ys : μι → CTorus d L N₁ m₁ (k + 1)) (is : μι → Fin N) (hys : ∀ τ ∈ 𝒯M, ys τ ∈ X₁M τ)
    (hBM : ∀ τ ∈ 𝒯M, BgSetting N S.G' (GkM τ) (GjM τ) S.a₁ S.ν c BG κ r₀ eps δ₃ (X₀M τ)
      (X₁M τ) (jM τ))
    (hFM : ∀ τ ∈ 𝒯M, FlSetting N S.G' (GkM τ) (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν κ BG eps δ₃
      Kc Cx c₂ BG₂ δ₁ δfl (X₁M τ))
    (hcovM : ∀ τ ∈ 𝒯M, CovSetup S.G' (m₀) (jM τ) (XM τ) (𝒦XM τ))
    (hX₁M : ∀ τ ∈ 𝒯M, (↑(X₁M τ) : Set (CTorus d L N₁ m₁ (k + 1))) =
      X1 S.G' (m₀) (jM τ) (𝒦XM τ))
    (hoptM : ∀ τ ∈ 𝒯M, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XM τ) ∧ MeetsOne (m₀) (jM τ) (𝒦XM τ) W₀ ∧
        bondCost (scaleW L (m₀) m₁ (jM τ)) E₀ = treeLenCovOne (m₀) (jM τ) (XM τ))
    (hlogM : ∀ τ ∈ 𝒯M, Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) *
      (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hEbM : ∀ τ ∈ 𝒯M, 0 ≤ EbM τ) {EM : μι → RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ}
    (hEanM : ∀ τ ∈ 𝒯M, AnalyticOnNhd ℂ (EM τ) (XiCRaw (GjM τ) (compWeight L S.a₁) S.ν (jM τ)
      (scaledC0 d) (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)))
    (hEbdM : ∀ τ ∈ 𝒯M, ∀ r ∈ XiCRaw (GjM τ) (compWeight L S.a₁) S.ν (jM τ) (scaledC0 d)
      (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      ‖EM τ r‖ ≤ EbM τ * Real.exp (-(κdec - 1) * treeLenCovOne (m₀) (jM τ) (XM τ)))
    (rE : τι → CTorus d L N₁ m₁ (k + 1)) (hrE : ∀ τ ∈ 𝒯E, rE τ ∈ X₁E τ) {ρE : ℝ} (hρE0 : 0 ≤ ρE)
    (hρE : ∀ x : CTorus d L N₁ m₁ (k + 1), ∑ τ ∈ 𝒯E.filter (fun τ => rE τ = x),
      EbE τ * Real.exp (-κ₀ * treeLenCovOne m₀ (jE τ) (XE τ)) ≤ ρE)
    {ρM : ℝ} (hρM0 : 0 ≤ ρM)
    (hρM : ∀ p : CTorus d L N₁ m₁ (k + 1) × Fin N, ∑ τ ∈ 𝒯M.filter (fun τ => (ys τ, is τ) = p),
      EbM τ * Real.exp (-κ₀ * treeLenCovOne m₀ (jM τ) (XM τ)) ≤ ρM)
    {Bh : ℝ} (hBh0 : 0 ≤ Bh)
    (hBh : ∀ D : BgData S.G' N, XiCData S.G' (compWeight L S.a₁) S.ν (k + 1) 1 eps D →
      ∀ x i, ‖D.h x i‖ ≤ Bh)
    (hZν : ∀ z, (↑(blockSites d L N₁ m₁ (k + 1) k z) : Set (CTorus d L N₁ m₁ (k + 1))) ⊆
      ↑(X₁V z))
    (hc : (Rσ * R₁ + r) * ρ < cψ)
    (hD : XiCData S.G' (compWeight L S.a₁) S.ν (k + 1) 1 eps S.D')
    (hN : L ^ m₀ ∣ N₁) (hp : 0 < S.p₁) (hpρ : S.p₁ ≤ ρ)
    (hεpos : 0 < εU)
    (hεb : prop33Eps d L N m₁ k m₀ S.a₁ S.ν BG BG₂ κ δ₁ r ρE ρM * ‖(S.β : ℂ)‖ +
      ‖(0 : ℂ)‖ * (1 * (c1 d L * ((L : ℝ) ^ (m₀ + m₁)) ^ d *
        nuBd d L N k (cK2' d L N (famConst d L BG₂ κ) * δ₁)
          (K4 d L N BG κ * (xiC1 d * eps) + (1 + 3 * (xiC1 d * eps)) + Bh) / r)) ≤ εU)
    (hκE : aEnt d L + 1 ≤ κ0) (hKc : K0 d L κ0 + 1 ≤ Kc') (hκ' : 0 ≤ κ')
    (hκa : κ' + 3 * κ0 + c1 d L + 3 / 2 ≤ 2 * κdec - 1)
    (hDA : 2 * (Rσ * εU) ≤ 1 / (8 * (2 * Kc') ^ 3 * c1 d L *
      Real.exp ((2 * κdec - 1 - 2 * κ0) * cG d L + c1 d L + κ' * cG d L)))
    {pp : ℝ} (R0 : S.RayData pp) (hlt : S.p₁ < pp) (hRσ1 : 1 < Rσ)
    (hg : (fun y i => g y i / (S.β : ℂ)) ∈ l1Ball d L N₁ m₁ (k + 1) N)
    (hmatchE : OldEnergyHatMatch S C 𝒯E hBE hFE EE)
    (hmatchM : OldObsHatMatch S C g 𝒯M ys is hBM hFM EM) :
    ∃ B : StepActivityBound S C g,
      B.κH = 2 * κdec - 1 ∧ B.εH = 2 * (Rσ * εU) ∧ B.Kc = 2 * Kc' := by
  classical
  have hpc : S.p₁ < cψ := p₁_lt_of_margin hp hpρ hRσ1 hR₁ hr hc
  have hRσ : 0 < Rσ := by linarith
  obtain ⟨I₀, -, -, -⟩ := physical_directTerms
    (S := S) (cβ := (S.β : ℂ)) (hk := S.hk1) (hG := S.hG)
    (cc := ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) (ha₁ := R0.ha₁) (H := R0.H) (cν := (0 : ℂ))
    (hRσ := hRσ) (Θ₀ := (rawOf S.D', (0 : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)))
    (hΘ₀ := ⟨⟨S.D', hD, rfl⟩, by simp [l1Ball]⟩) (hC := hC) (hconn := hconn) (hrow := hrow)
    (hκ₀ := hκ₀) (hκdec := hκdec) (hκ := hκ) (h1 := h1) (hR₁ := hR₁) (hr := hr) (hcψ := hcψ)
    (hMX := hMX) (hdm := hdm) (hα := hα) (hsmX := hsmX) (hδ₁ := hδ₁) (hc7 := hc7) (hR := hR)
    (hRs := hRs) (hsmall := hsmall) (hnum := hnum) (hnum' := hnum') (hsm := hsm) (hcovV := hcovV)
    (hX₁V := hX₁V) (hoptV := hoptV) (hΔV := hΔV) (hlogV := hlogV) (hZV := hZV) (hmarV := hmarV)
    (𝒯E := 𝒯E) (hBE := hBE) (hFE := hFE) (hcovE := hcovE) (hX₁E := hX₁E) (hoptE := hoptE)
    (hlogE := hlogE) (hEbE := hEbE) (hEanE := hEanE) (hEbdE := hEbdE) (hcovF := hcovF)
    (hX₁F := hX₁F) (hoptF := hoptF) (hΔF := hΔF) (hlogF := hlogF) (hyF := hyF) (𝒯M := 𝒯M)
    (ys := ys) (is := is) (hys := hys) (hBM := hBM) (hFM := hFM) (hcovM := hcovM) (hX₁M := hX₁M)
    (hoptM := hoptM) (hlogM := hlogM) (hEbM := hEbM) (hEanM := hEanM) (hEbdM := hEbdM) (rE := rE)
    (hrE := hrE) (hρE0 := hρE0) (hρE := hρE) (hρM0 := hρM0) (hρM := hρM) (hBh0 := hBh0)
    (hBh := hBh) (hZν := hZν) (hc := hc) (hεb := hεb) (hN := hN) (hp := hp)
  obtain ⟨Ig, -, -, -⟩ := physical_directTerms
    (S := S) (cβ := (S.β : ℂ)) (hk := S.hk1) (hG := S.hG)
    (cc := ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) (ha₁ := R0.ha₁) (H := R0.H) (cν := (0 : ℂ))
    (hRσ := hRσ) (Θ₀ := (rawOf S.D', fun y i => g y i / (S.β : ℂ))) (hΘ₀ := ⟨⟨S.D', hD, rfl⟩, hg⟩)
    (hC := hC) (hconn := hconn) (hrow := hrow) (hκ₀ := hκ₀) (hκdec := hκdec) (hκ := hκ) (h1 := h1)
    (hR₁ := hR₁) (hr := hr) (hcψ := hcψ) (hMX := hMX) (hdm := hdm) (hα := hα) (hsmX := hsmX)
    (hδ₁ := hδ₁) (hc7 := hc7) (hR := hR) (hRs := hRs) (hsmall := hsmall) (hnum := hnum)
    (hnum' := hnum') (hsm := hsm) (hcovV := hcovV) (hX₁V := hX₁V) (hoptV := hoptV) (hΔV := hΔV)
    (hlogV := hlogV) (hZV := hZV) (hmarV := hmarV) (𝒯E := 𝒯E) (hBE := hBE) (hFE := hFE)
    (hcovE := hcovE) (hX₁E := hX₁E) (hoptE := hoptE) (hlogE := hlogE) (hEbE := hEbE)
    (hEanE := hEanE) (hEbdE := hEbdE) (hcovF := hcovF) (hX₁F := hX₁F) (hoptF := hoptF) (hΔF := hΔF)
    (hlogF := hlogF) (hyF := hyF) (𝒯M := 𝒯M) (ys := ys) (is := is) (hys := hys) (hBM := hBM)
    (hFM := hFM) (hcovM := hcovM) (hX₁M := hX₁M) (hoptM := hoptM) (hlogM := hlogM) (hEbM := hEbM)
    (hEanM := hEanM) (hEbdM := hEbdM) (rE := rE) (hrE := hrE) (hρE0 := hρE0) (hρE := hρE)
    (hρM0 := hρM0) (hρM := hρM) (hBh0 := hBh0) (hBh := hBh) (hZν := hZν) (hc := hc) (hεb := hεb)
    (hN := hN) (hp := hp)
  refine stepActivityBound_source_of_directTerms_scaled S C g I₀ Ig
    (fun t Y ψ ψ' h => agFDirPair_smul S t Y ψ ψ' h)
    (fun t Y ψ ψ' h => agFDirPair_smul S t Y ψ ψ' h) ?_ ?_ hN hpρ hεpos hκE hKc hκ' hκa hDA hRσ1
  · intro s hs x hx
    exact S.physVal_scaled_eq_Wone_of_oldEnergyHatMatch
      (C := C) (hC := hC) (R0 := R0) (hlt := hlt) (hD := hD) (hc7 := hc7) (hR := hR) (hsmR := hsm)
      (hRs := hRs) (hsmall := hsmall) (hnum := hnum) (hnum' := hnum') (hMX := hMX) (hdm := hdm)
      (hα := hα) (hsm := hsmX) (hp₁ := hp) (hcψ := hcψ) (hpc := hpc) (hδ₁ := hδ₁) (𝒯E := 𝒯E)
      (hBE := hBE) (hFE := hFE) (hEanE := hEanE) (hmatchE := hmatchE) (𝒯M := 𝒯M) (ys := ys)
      (is := is) (hBM := hBM) (hFM := hFM) (EM := EM) hs hx
  · intro t ht x hx
    exact S.physVal_scaled_sub_eq_Wtwo_of_oldObsHatMatch
      (C := C) (hC := hC) (R0 := R0) (hlt := hlt) (hD := hD) (hc7 := hc7) (hR := hR) (hsmR := hsm)
      (hRs := hRs) (hsmall := hsmall) (hnum := hnum) (hnum' := hnum') (hMX := hMX) (hdm := hdm)
      (hα := hα) (hsm := hsmX) (hp₁ := hp) (hcψ := hcψ) (hpc := hpc) (hδ₁ := hδ₁) (𝒯E := 𝒯E)
      (hBE := hBE) (hFE := hFE) (EE := EE) (𝒯M := 𝒯M) (ys := ys) (is := is) (hBM := hBM)
      (hFM := hFM) (hEanM := hEanM) (g := g) (hmatchM := hmatchM) ht hx

/-- **The rate statement: the class rate is preserved by the fluctuation step (general class).**
At `d = L = 3` and the constants (8) of `notes/phase1/TRUE-LOCAL.md` (`κ₀ = a_Ent + 1`,
`κ_dec = 100 (κ₀ + c₁ + 10)`, `κ' = (3/2) κ_dec + κ₀ + 1`), under the hypotheses of
`stepActivityBound_direct_of_oldEnergyHatMatch` (the rate hypothesis is a consequence of the
choices), the step activity bound of the class `C` has `κ_H = 2 κ_dec - 1`, hence admits `κ'`, and
the output rate `κ_out = (3/2) κ_dec` satisfies `κ_dec ≤ κ_out ≤ min κ_h κ' - κ₀ - 1` with
`κ_h = κ'`: the output rate is at least the input rate `κ_in = κ_dec`.  The last conjunct is the
landed obstruction `stepRates_landed_impossible` of the halo conversion. -/
theorem stepActivityBound_direct_rate_of_oldEnergyHatMatch
    (S : StepSetting d L N₁ m₁ k N ϱ) (C : StepClass d L N₁ m₁ k N ϱ)
    (hd3 : d = 3) (hL3 : L = 3)
    {ρ εU κ0 κ' Kc' : ℝ} {Kc Cx c₂ BG₂ δ₁ : ℝ}
    (hC : FlCore N S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hconn : HatConn S.G')
    (hrow : RowInHat (coverOf S.G') (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) S.ν)
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    {R₁ : ℝ} (hR₁ : 1 < R₁) {r Rσ : ℝ} (hr : 0 < r)
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsmX : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hδ₁ : Real.sqrt N * (‖((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ *
      (covSupConstC d L N (compWeight L S.a₁ k) κ * cψ)) < δ₁)
    (hc7 : c7 d L N BG κ ≤ thm73C3 d L N)
    {R : ℝ} (hR : 2 ≤ R) (hRs : R * δ₁ ≤ deltaStar d L N)
    (hsmall : cK2 d L N * (R * δ₁) < bgC0 d L N / 2)
    (hnum : cK2 d L N * δ₁ ≤ c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hnum' : cK2' d L N (famConst d L BG₂ κ) * δ₁ ≤
      c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hsm : 2 * (compC4 d * (bgK1 d L N * (xiC1 d * eps))) + 5 * (R * δ₁) ≤ bgC1 d L N)
    {m₀ : ℕ} {jV : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → ℕ}
    {XV 𝒦XV : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Set (CTorus d L N₁ m₁ (k + 1))}
    {X₁V : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Finset (CTorus d L N₁ m₁ (k + 1))}
    (hcovV : ∀ z, CovSetup S.G' (m₀) (jV z) (XV z) (𝒦XV z))
    (hX₁V : ∀ z, (↑(X₁V z) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 S.G' (m₀) (jV z) (𝒦XV z))
    (hoptV : ∀ z, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XV z) ∧ MeetsOne (m₀) (jV z) (𝒦XV z) W₀ ∧
        bondCost (scaleW L (m₀) m₁ (jV z)) E₀ = treeLenCovOne (m₀) (jV z) (XV z))
    (hΔV : ∀ z, treeLenCovOne (m₀) (jV z) (XV z) = 0)
    (hlogV : ∀ _z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))),
      Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤
      (κ / 2 - 1) / 2)
    (hZV : ∀ z, readSites (stepG d L N₁ m₁ k ϱ) k z ⊆ ↑(X₁V z))
    (hmarV : ∀ z, BlockMargin S.G' (X₁V z)
      (↑(blockSites d L N₁ m₁ (k + 1) k z) : Set (CTorus d L N₁ m₁ (k + 1))))
    {τι : Type*} [DecidableEq τι] (𝒯E : Finset τι) {ϱ₁ ϱ₂ : τι → ℝ}
    {GkE : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₁ τ)}
    {GjE : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₂ τ)} {r₀ δ₃ δfl : ℝ}
    {X₀E X₁E : τι → Finset (CTorus d L N₁ m₁ (k + 1))} {jE : τι → ℕ}
    {XE 𝒦XE : τι → Set (CTorus d L N₁ m₁ (k + 1))} {EbE : τι → ℝ}
    (hBE : ∀ τ ∈ 𝒯E, BgSetting N S.G' (GkE τ) (GjE τ) S.a₁ S.ν c BG κ r₀ eps δ₃ (X₀E τ)
      (X₁E τ) (jE τ))
    (hFE : ∀ τ ∈ 𝒯E, FlSetting N S.G' (GkE τ) (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν κ BG eps δ₃
      Kc Cx c₂ BG₂ δ₁ δfl (X₁E τ))
    (hcovE : ∀ τ ∈ 𝒯E, CovSetup S.G' (m₀) (jE τ) (XE τ) (𝒦XE τ))
    (hX₁E : ∀ τ ∈ 𝒯E, (↑(X₁E τ) : Set (CTorus d L N₁ m₁ (k + 1))) =
      X1 S.G' (m₀) (jE τ) (𝒦XE τ))
    (hoptE : ∀ τ ∈ 𝒯E, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XE τ) ∧ MeetsOne (m₀) (jE τ) (𝒦XE τ) W₀ ∧
        bondCost (scaleW L (m₀) m₁ (jE τ)) E₀ = treeLenCovOne (m₀) (jE τ) (XE τ))
    (hlogE : ∀ τ ∈ 𝒯E, Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) *
      (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hEbE : ∀ τ ∈ 𝒯E, 0 ≤ EbE τ) {EE : τι → RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ}
    (hEanE : ∀ τ ∈ 𝒯E, AnalyticOnNhd ℂ (EE τ) (XiCRaw (GjE τ) (compWeight L S.a₁) S.ν (jE τ)
      (scaledC0 d) (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)))
    (hEbdE : ∀ τ ∈ 𝒯E, ∀ r ∈ XiCRaw (GjE τ) (compWeight L S.a₁) S.ν (jE τ) (scaledC0 d)
      (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      ‖EE τ r‖ ≤ EbE τ * Real.exp (-(κdec - 1) * treeLenCovOne (m₀) (jE τ) (XE τ)))
    {jF : CTorus d L N₁ m₁ (k + 1) × Fin N → ℕ}
    {XF 𝒦XF : CTorus d L N₁ m₁ (k + 1) × Fin N → Set (CTorus d L N₁ m₁ (k + 1))}
    {X₁F : CTorus d L N₁ m₁ (k + 1) × Fin N → Finset (CTorus d L N₁ m₁ (k + 1))}
    (hcovF : ∀ s, CovSetup S.G' (m₀) (jF s) (XF s) (𝒦XF s))
    (hX₁F : ∀ s, (↑(X₁F s) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 S.G' (m₀) (jF s) (𝒦XF s))
    (hoptF : ∀ s, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XF s) ∧ MeetsOne (m₀) (jF s) (𝒦XF s) W₀ ∧
        bondCost (scaleW L (m₀) m₁ (jF s)) E₀ = treeLenCovOne (m₀) (jF s) (XF s))
    (hΔF : ∀ s, treeLenCovOne (m₀) (jF s) (XF s) = 0)
    (hlogF : ∀ _s : CTorus d L N₁ m₁ (k + 1) × Fin N,
      Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤
      (κ / 2 - 1) / 2)
    (hyF : ∀ s : CTorus d L N₁ m₁ (k + 1) × Fin N, s.1 ∈ X₁F s)
    {μι : Type*} [DecidableEq μι] (𝒯M : Finset μι) {ϱ₁M ϱ₂M : μι → ℝ}
    {GkM : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₁M τ)}
    {GjM : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₂M τ)}
    {X₀M X₁M : μι → Finset (CTorus d L N₁ m₁ (k + 1))} {jM : μι → ℕ}
    {XM 𝒦XM : μι → Set (CTorus d L N₁ m₁ (k + 1))} {EbM : μι → ℝ}
    (ys : μι → CTorus d L N₁ m₁ (k + 1)) (is : μι → Fin N) (hys : ∀ τ ∈ 𝒯M, ys τ ∈ X₁M τ)
    (hBM : ∀ τ ∈ 𝒯M, BgSetting N S.G' (GkM τ) (GjM τ) S.a₁ S.ν c BG κ r₀ eps δ₃ (X₀M τ)
      (X₁M τ) (jM τ))
    (hFM : ∀ τ ∈ 𝒯M, FlSetting N S.G' (GkM τ) (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν κ BG eps δ₃
      Kc Cx c₂ BG₂ δ₁ δfl (X₁M τ))
    (hcovM : ∀ τ ∈ 𝒯M, CovSetup S.G' (m₀) (jM τ) (XM τ) (𝒦XM τ))
    (hX₁M : ∀ τ ∈ 𝒯M, (↑(X₁M τ) : Set (CTorus d L N₁ m₁ (k + 1))) =
      X1 S.G' (m₀) (jM τ) (𝒦XM τ))
    (hoptM : ∀ τ ∈ 𝒯M, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XM τ) ∧ MeetsOne (m₀) (jM τ) (𝒦XM τ) W₀ ∧
        bondCost (scaleW L (m₀) m₁ (jM τ)) E₀ = treeLenCovOne (m₀) (jM τ) (XM τ))
    (hlogM : ∀ τ ∈ 𝒯M, Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) *
      (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hEbM : ∀ τ ∈ 𝒯M, 0 ≤ EbM τ) {EM : μι → RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ}
    (hEanM : ∀ τ ∈ 𝒯M, AnalyticOnNhd ℂ (EM τ) (XiCRaw (GjM τ) (compWeight L S.a₁) S.ν (jM τ)
      (scaledC0 d) (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)))
    (hEbdM : ∀ τ ∈ 𝒯M, ∀ r ∈ XiCRaw (GjM τ) (compWeight L S.a₁) S.ν (jM τ) (scaledC0 d)
      (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      ‖EM τ r‖ ≤ EbM τ * Real.exp (-(κdec - 1) * treeLenCovOne (m₀) (jM τ) (XM τ)))
    (rE : τι → CTorus d L N₁ m₁ (k + 1)) (hrE : ∀ τ ∈ 𝒯E, rE τ ∈ X₁E τ) {ρE : ℝ} (hρE0 : 0 ≤ ρE)
    (hρE : ∀ x : CTorus d L N₁ m₁ (k + 1), ∑ τ ∈ 𝒯E.filter (fun τ => rE τ = x),
      EbE τ * Real.exp (-κ₀ * treeLenCovOne m₀ (jE τ) (XE τ)) ≤ ρE)
    {ρM : ℝ} (hρM0 : 0 ≤ ρM)
    (hρM : ∀ p : CTorus d L N₁ m₁ (k + 1) × Fin N, ∑ τ ∈ 𝒯M.filter (fun τ => (ys τ, is τ) = p),
      EbM τ * Real.exp (-κ₀ * treeLenCovOne m₀ (jM τ) (XM τ)) ≤ ρM)
    {Bh : ℝ} (hBh0 : 0 ≤ Bh)
    (hBh : ∀ D : BgData S.G' N, XiCData S.G' (compWeight L S.a₁) S.ν (k + 1) 1 eps D →
      ∀ x i, ‖D.h x i‖ ≤ Bh)
    (hZν : ∀ z, (↑(blockSites d L N₁ m₁ (k + 1) k z) : Set (CTorus d L N₁ m₁ (k + 1))) ⊆
      ↑(X₁V z))
    (hc : (Rσ * R₁ + r) * ρ < cψ)
    (hD : XiCData S.G' (compWeight L S.a₁) S.ν (k + 1) 1 eps S.D')
    (hN : L ^ m₀ ∣ N₁) (hp : 0 < S.p₁) (hpρ : S.p₁ ≤ ρ)
    (hεpos : 0 < εU)
    (hεb : prop33Eps d L N m₁ k m₀ S.a₁ S.ν BG BG₂ κ δ₁ r ρE ρM * ‖(S.β : ℂ)‖ +
      ‖(0 : ℂ)‖ * (1 * (c1 d L * ((L : ℝ) ^ (m₀ + m₁)) ^ d *
        nuBd d L N k (cK2' d L N (famConst d L BG₂ κ) * δ₁)
          (K4 d L N BG κ * (xiC1 d * eps) + (1 + 3 * (xiC1 d * eps)) + Bh) / r)) ≤ εU)
    (hKc : K0 d L κ0 + 1 ≤ Kc')
    (hκ0def : κ0 = aEnt d L + 1) (hκdecdef : κdec = 100 * (κ0 + c1 d L + 10))
    (hκ'def : κ' = 3 / 2 * κdec + κ0 + 1)
    (hDA : Rσ * εU ≤ 1 / (8 * Kc' ^ 3 * c1 d L *
      Real.exp ((2 * κdec - 1 - 2 * κ0) * cG d L + c1 d L + κ' * cG d L)))
    {pp : ℝ} (R0 : S.RayData pp) (hlt : S.p₁ < pp) (hRσ1 : 1 < Rσ)
    (hmatchE : OldEnergyHatMatch S C 𝒯E hBE hFE EE) :
    ∃ B : StepActivityBound S C 0,
      B.κH = 2 * κdec - 1 ∧ B.εH = Rσ * εU ∧
      ∃ κout : ℝ, κout = 3 / 2 * κdec ∧ κdec ≤ κout ∧ κout ≤ min κ' κ' - κ0 - 1 ∧
        ¬ ∃ κ0 κ' κH κh κin κdec κout : ℝ, aEnt 3 3 + 1 ≤ κ0 ∧ 0 < κin ∧
          hatKappaH 3 3 (2 * κdec - 1) = κH ∧ κ' + 3 * κ0 + c1 3 3 + 3 / 2 ≤ κH ∧ κ' ≤ κh ∧
          κdec - 1 ≤ κin ∧ κout ≤ min κh κ' - κ0 - 1 ∧ κin ≤ κout := by
  subst hd3 hL3
  have hc1 : 1 ≤ c1 3 3 := one_le_c1 3 3
  have hent : 0 ≤ aEnt 3 3 := aEnt_nonneg 3 3
  have hκ0 : 0 ≤ κ0 := by linarith
  obtain ⟨-, h3, h4, -, h5⟩ := stepRates_direct_closure (κ0 := κ0) (c := c1 3 3) (κin := κdec)
    (κdec := κdec) (κH := 2 * κdec - 1) (κ' := 3 / 2 * κdec + κ0 + 1) (κout := 3 / 2 * κdec)
    hκ0 (by linarith) (by linarith) rfl rfl rfl rfl
  have hκ'0 : 0 ≤ κ' := by rw [hκ'def]; linarith
  obtain ⟨B, hB1, hB2⟩ := stepActivityBound_direct_of_oldEnergyHatMatch S C
    (hC := hC) (hconn := hconn) (hrow := hrow) (hκ₀ := hκ₀) (hκdec := hκdec) (hκ := hκ) (h1 := h1)
    (hR₁ := hR₁) (hr := hr) (hcψ := hcψ) (hMX := hMX) (hdm := hdm) (hα := hα) (hsmX := hsmX)
    (hδ₁ := hδ₁) (hc7 := hc7) (hR := hR) (hRs := hRs) (hsmall := hsmall) (hnum := hnum)
    (hnum' := hnum') (hsm := hsm) (hcovV := hcovV) (hX₁V := hX₁V) (hoptV := hoptV) (hΔV := hΔV)
    (hlogV := hlogV) (hZV := hZV) (hmarV := hmarV) (𝒯E := 𝒯E) (hBE := hBE) (hFE := hFE)
    (hcovE := hcovE) (hX₁E := hX₁E) (hoptE := hoptE) (hlogE := hlogE) (hEbE := hEbE)
    (hEanE := hEanE) (hEbdE := hEbdE) (hcovF := hcovF) (hX₁F := hX₁F) (hoptF := hoptF) (hΔF := hΔF)
    (hlogF := hlogF) (hyF := hyF) (𝒯M := 𝒯M) (ys := ys) (is := is) (hys := hys) (hBM := hBM)
    (hFM := hFM) (hcovM := hcovM) (hX₁M := hX₁M) (hoptM := hoptM) (hlogM := hlogM) (hEbM := hEbM)
    (hEanM := hEanM) (hEbdM := hEbdM) (rE := rE) (hrE := hrE) (hρE0 := hρE0) (hρE := hρE)
    (hρM0 := hρM0) (hρM := hρM) (hBh0 := hBh0) (hBh := hBh) (hZν := hZν) (hc := hc) (hD := hD)
    (hN := hN) (hp := hp) (hpρ := hpρ) (hεpos := hεpos) (hεb := hεb) (hκE := hκ0def.ge)
    (hKc := hKc) (hκ' := hκ'0) (hκa := by rw [hκ'def]; linarith) (hDA := hDA) (R0 := R0)
    (hlt := hlt) (hRσ1 := hRσ1) (hmatchE := hmatchE)
  exact ⟨B, hB1, hB2, 3 / 2 * κdec, rfl, by linarith, by rw [hκ'def, min_self]; linarith,
    stepRates_landed_impossible (by norm_num) (by norm_num)⟩

end Main

end Balaban.Fluctuation
