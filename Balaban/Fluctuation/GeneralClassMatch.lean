/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.StepRegDomain
public import Balaban.SmallField.Def6v2Bridge
public import Balaban.Localization.I5Chain
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The small-field class `IsSF2` and the analyticity input of the step (package `GeneralClassMatch`)

The landed unconditional results about the fluctuation step are for the zero class.  For a general
old class the step theorems of `StepRegTerms`, `StepRegClass`, `StepTaylor`, `StepBaseDomain` take
`StepTermsAnalytic` and `RayInDomain` as hypotheses.  This file derives the first from the current
small-field class `Def6v2.IsSF2` and states precisely what the second requires.

* `ClassParamMatch S C P Rg a Tm`: the typing-level matching data (GENERAL-PARAM-MATCH) between the
  step `S`, its class `C` and a member `IsSF2 P Rg β a Dom Tm ρ E` of the class on the step torus:
  `C.m₀ = P.m₀`, `C.Tm = Tm`, `S.a = aIdeal L (k+1) (a (k+1))` as sequences and
  `S.ν = Rg.sfBgMass (k+1)`.  Only equalities of parameters and terms; inhabited
  (`nonempty_classParamMatch_witness`) at the zero-class witness step.
* `stepTermsAnalytic_of_isSF2_of_subset`: from `IsSF2` on any field domain `Dom` whose level-`j`
  domain contains `XiDom (Tm.gs j X) A μ j (ε_j)`, the terms of the step class are analytic on
  `XiDom`; `stepTermsAnalytic_of_isSF2` is the instance `Dom = completeXiDom` (inclusion by
  definition), `stepTermsAnalytic_of_isSF2_step` states it with the step's own `S.a`, `S.ν`.
  The source premise `‖g‖₁ < 1` of `analyticM` is carried by the domain `{… ∧ l1 g < 1}`
  exactly as in `StepTermsAnalytic`.
* Consequences (one-line compositions with landed theorems that take `StepTermsAnalytic`):
  `contDiffAt_EcompRay_of_isSF2`, `contDiffAt_McompRay_of_isSF2`, `classRegular_of_isSF2`,
  `completeW_taylor_of_isSF2`.  The remaining landed theorems with the hypotheses `RayData`,
  `StepTermsAnalytic`, `RayInDomain` are the same files' `classRegularLoc_of_analytic`,
  `classRegularObs_of_analytic` (`StepRegClass`), `dE_ray_ftc` and its relatives (`StepTaylor`,
  `StepTaylorW`) and `StepBaseDomain.completeW_taylor_of_baseDomain`; each composes with
  `stepTermsAnalytic_of_isSF2` verbatim.
* `xiC_rescale`: the same-centre rescaling `Ξ^c_n(𝔹; σ, ε) ⊆ Ξ^c_n(𝔹; 1, ε')` for `1 ≤ σ` and
  `σ² ε ≤ ε'`; and `rayInDomain_dom_of_xiCData`: the `dom` field of `RayInDomain` follows from
  `XiCData (𝔹_j(X)) … j (scaledC0 d) ε_path` for the composed datum of the real ray, if
  `scaledC0 d ^ 2 * ε_path ≤ ε_j`.

Not covered here (separate packages of `notes/phase1/GENERAL.md`): the proof that the composed datum
of the ray is in `XiCData … ε_path` (GENERAL-OLD-XIDOM), the complex-disc domain inclusion
(GENERAL-OLD-XIDOM-C), the path analyticity predicates, the regularity of the complex step, and the
general hat identity.  The old terms of the class are taken at the step torus (index `k + 1`): an
`IsSF2` at index `k + 1`.  An `IsSFFamily2` at index `k` supplies terms on the torus of index `k`
only, not `Terms … (k + 1) …` (OLD-TERMS-LIFT); this file does not lift them.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization
  Balaban.Localization.I5Inhabited Balaban.Inhabited Balaban.SmallField Balaban.SmallField.Def6 Balaban.SmallField.Def6v2 Finset Set

section Match

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- **The matching data between a step and a member of the class** (GENERAL-PARAM-MATCH): the
step class `C` has the constants' `m₀` and the terms `Tm` of the class on the step torus; the
weights of the step are the ideal ones matched at `k + 1`; the mass of the step is the complete
mass of the regime at `k + 1`.  Equalities only. -/
structure ClassParamMatch (S : StepSetting d L N₁ m₁ k N ϱ) (C : StepClass d L N₁ m₁ k N ϱ)
    (P : Consts) (Rg : Regime L) (a : ℕ → ℝ) (Tm : Terms d L N₁ m₁ (k + 1) N ϱ) : Prop where
  m₀_eq : C.m₀ = P.m₀
  terms_eq : C.Tm = Tm
  weights_eq : S.a = aIdeal L (k + 1) (a (k + 1))
  mass_eq : S.ν = Rg.sfBgMass (k + 1)

end Match

/-- The weights `compWeight L a₁` are the ideal weights matched at `K ≥ 1` with the value at `K`. -/
theorem compWeight_eq_aIdeal {L : ℕ} (hL : 2 ≤ L) {K : ℕ} (hK : 1 ≤ K) (a₁ : ℝ) :
    compWeight L a₁ = aIdeal L K (compWeight L a₁ K) := by
  funext n
  have hL1 : (1 : ℝ) < L := by exact_mod_cast hL
  have hLK : (1 : ℝ) < (L : ℝ) ^ K := one_lt_pow₀ hL1 (by omega)
  have hc : (1 : ℝ) - ((L : ℝ) ^ K)⁻¹ ^ 2 ≠ 0 := by
    have : ((L : ℝ) ^ K)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hLK
    have h0 : 0 < ((L : ℝ) ^ K)⁻¹ := by positivity
    nlinarith
  have hc' : (1 : ℝ) - (((L : ℝ) ^ K) ^ 2)⁻¹ ≠ 0 := by rwa [← inv_pow]
  unfold aIdeal compWeight
  rw [← inv_pow ((L : ℝ) ^ K) 2, ← inv_pow ((L : ℝ) ^ n) 2]
  have h2 : ((L : ℝ) ^ K) ^ 2 - 1 ≠ 0 := by nlinarith
  field_simp

/-- **`ClassParamMatch` is inhabited** at the zero-class witness step of `StepRegWitness` (any
`m₁, β, δ`): the zero class with `m₀ = 0`, the zero regime `ν ≡ 0` (so the complete mass `0` is the
witness mass `ν = 0`) and the kernel sequence `a = compWeight 3 1`. -/
theorem nonempty_classParamMatch_witness (m₁ : ℕ) (β δ : ℝ) :
    ∃ (P : Consts) (Rg : Regime 3) (a : ℕ → ℝ),
      Nonempty (ClassParamMatch (witnessSetting m₁ β δ) (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) P Rg a
        (zeroTerms 3 3 6 m₁ (1 + 1) 2 (rhoSep m₁))) := by
  refine ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, fun _ => 0, 0⟩, ⟨0, fun _ => 0⟩, compWeight 3 1, ⟨?_, ?_, ?_, ?_⟩⟩
  · rfl
  · rfl
  · exact compWeight_eq_aIdeal (by norm_num) (by norm_num) 1
  · show (0 : ℝ) = Regime.sfBgMass ⟨0, fun _ => 0⟩ (1 + 1)
    simp [Regime.sfBgMass, sfBgMassAt, physMass]

section Bridge

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  {S : StepSetting d L N₁ m₁ k N ϱ} {C : StepClass d L N₁ m₁ k N ϱ} {P : Consts}
  {Rg : Regime L} {β a : ℕ → ℝ} {Tm : Terms d L N₁ m₁ (k + 1) N ϱ}
  {ρ : (CTorus d L N₁ m₁ (k + 1) → Fin N → ℝ) → (Fin N → ℝ) →
    (CTorus d L N₁ m₁ (k + 1) → Fin N → ℝ) → ℝ} {E : ℝ}

/-- **The analyticity of the old terms of the step from the class `IsSF2`, for a general field
domain.**  If `Dom` contains, at each level `j`, the domain `Ξ^c_j(𝔹_j(X); 1, ε_j)` at the ideal
weights and the complete mass (the explicit inclusion `hsub`), the clauses `analyticE`,
`analyticM` of `IsSF2` restrict to `StepTermsAnalytic`; the source condition `‖g‖₁ < 1` of
`analyticM` is the same one on both sides. -/
theorem stepTermsAnalytic_of_isSF2_of_subset {Dom : FieldDom d L N₁ m₁ (k + 1) N ϱ}
    (hm : ClassParamMatch S C P Rg a Tm) (h : IsSF2 P Rg β a Dom Tm ρ E)
    (hsub : ∀ j X Ψ h', XiDom (Tm.gs j X) (aIdeal L (k + 1) (a (k + 1))) (Rg.sfBgMass (k + 1)) j
      (P.eps d L j) Ψ h' → Dom.dom j (Tm.gs j X) Ψ h') :
    StepTermsAnalytic C (aIdeal L (k + 1) (a (k + 1))) (Rg.sfBgMass (k + 1))
      (fun j => P.eps d L j) where
  analyticE j h1 hjk y X hX hy := by
    rw [hm.terms_eq]
    exact (h.terms.analyticE j h1 (hjk.trans (Nat.le_succ k)) y X (hm.m₀_eq ▸ hX) hy).mono
      fun p hp => hsub j X _ _ hp
  analyticM j h1 hjk x X hX hx := by
    rw [hm.terms_eq]
    exact (h.terms.analyticM j h1 (hjk.trans (Nat.le_succ k)) x X (hm.m₀_eq ▸ hX) hx).mono
      fun p hp => ⟨hsub j X _ _ hp.1, hp.2⟩

/-- **The analyticity of the old terms of the step from `IsSF2` on the main domain**
`completeXiDom` (the complete mass), for a matched step: the inclusion of the general version
holds by definition. -/
theorem stepTermsAnalytic_of_isSF2
    (hm : ClassParamMatch S C P Rg a Tm)
    (h : IsSF2 P Rg β a (completeXiDom P Rg a N₁) Tm ρ E) :
    StepTermsAnalytic C (aIdeal L (k + 1) (a (k + 1))) (Rg.sfBgMass (k + 1))
      (fun j => P.eps d L j) :=
  stepTermsAnalytic_of_isSF2_of_subset hm h fun _ _ _ _ hx => hx

/-- The same with the weights and the mass of the step itself, `S.a` and `S.ν`, which is the form
in which it combines with `RayInDomain S C g S.a S.ν …`. -/
theorem stepTermsAnalytic_of_isSF2_step
    (hm : ClassParamMatch S C P Rg a Tm)
    (h : IsSF2 P Rg β a (completeXiDom P Rg a N₁) Tm ρ E) :
    StepTermsAnalytic C S.a S.ν (fun j => P.eps d L j) := by
  have := stepTermsAnalytic_of_isSF2 hm h
  rwa [← hm.weights_eq, ← hm.mass_eq] at this

end Bridge

section Consequences

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  {S : StepSetting d L N₁ m₁ k N ϱ} {C : StepClass d L N₁ m₁ k N ϱ} {P : Consts}
  {Rg : Regime L} {β a : ℕ → ℝ} {Tm : Terms d L N₁ m₁ (k + 1) N ϱ}
  {ρ : (CTorus d L N₁ m₁ (k + 1) → Fin N → ℝ) → (Fin N → ℝ) →
    (CTorus d L N₁ m₁ (k + 1) → Fin N → ℝ) → ℝ} {E : ℝ}
  {g : Fld d L N₁ m₁ (k + 1) N} {pp : ℝ}
  (hm : ClassParamMatch S C P Rg a Tm) (h : IsSF2 P Rg β a (completeXiDom P Rg a N₁) Tm ρ E)
  (R : S.RayData pp)
  (hD : S.RayInDomain C g (aIdeal L (k + 1) (a (k + 1))) (Rg.sfBgMass (k + 1))
    (fun j => P.eps d L j) pp)

include hm h R hD in
/-- **The composed old energy of a general class is smooth along the real ray**, from `IsSF2` and
`RayInDomain`. -/
theorem contDiffAt_EcompRay_of_isSF2 {q : ℝ × S.E} (hq : |q.1| * ‖q.2‖ < pp) :
    ContDiffAt ℝ ⊤ (fun q : ℝ × S.E =>
      EcompAt C.m₀ C.Tm S.a S.ν (Nat.le_succ k) (S.dataU (S.psiAt q.1 q.2))) q :=
  StepSetting.contDiffAt_EcompRay C R (stepTermsAnalytic_of_isSF2 hm h) hD hq

include hm h R hD in
/-- **The composed old vector `ℳ_k` of a general class is smooth along the real ray**
componentwise. -/
theorem contDiffAt_McompRay_of_isSF2 {q : ℝ × S.E} (hq : |q.1| * ‖q.2‖ < pp)
    (y : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) :
    ContDiffAt ℝ ⊤ (fun q : ℝ × S.E =>
      McompAt C.m₀ C.Tm S.a S.ν (Nat.le_succ k) (S.dataU (S.psiAt q.1 q.2)) g y i) q :=
  StepSetting.contDiffAt_McompRay C R (stepTermsAnalytic_of_isSF2 hm h) hD hq y i

include hm h R hD in
/-- **`ClassRegular` for a general `IsSF2` class**, from `RayData`, `RayInDomain` and
`0 < p₁ < p⁺`. -/
theorem classRegular_of_isSF2 (hp₁ : 0 < S.p₁) (hlt : S.p₁ < pp) : S.ClassRegular C g :=
  StepSetting.classRegular_of_analytic C R (stepTermsAnalytic_of_isSF2 hm h) hD hp₁ hlt

end Consequences

section Rescale

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ k ϱ}

/-- The numerical comparisons behind the rescaling `(σ, ε) ↦ (1, ε')`, `1 ≤ σ`, `σ² ε ≤ ε'`. -/
theorem rescale_nums {σ ε ε' : ℝ} (hσ : 1 ≤ σ) (he : 0 < ε) (hle : σ ^ 2 * ε ≤ ε') :
    σ * ε ≤ 1 * ε' ∧ σ ^ 2 * ε ≤ 1 ^ 2 * ε' ∧ (σ * ε) ^ 2 ≤ (1 * ε') ^ 2 ∧ ε ≤ ε' ∧
      (σ * ε) ^ 2 / ε ≤ (1 * ε') ^ 2 / ε' := by
  have hσ0 : 0 ≤ σ := by linarith
  have h1 : σ * ε ≤ σ ^ 2 * ε := by
    nlinarith [mul_nonneg (mul_nonneg hσ0 he.le) (sub_nonneg.2 hσ)]
  have h2 : ε ≤ σ * ε := by nlinarith
  have hp : 0 < ε' := lt_of_lt_of_le he (h2.trans (h1.trans hle))
  have h3 : σ * ε ≤ ε' := h1.trans hle
  refine ⟨by linarith, by linarith, ?_, by linarith, ?_⟩
  · have := mul_self_le_mul_self (by positivity : 0 ≤ σ * ε) (by linarith : σ * ε ≤ 1 * ε')
    nlinarith
  · have e1 : (σ * ε) ^ 2 / ε = σ ^ 2 * ε := by field_simp
    have e2 : (1 * ε') ^ 2 / ε' = ε' := by field_simp
    rw [e1, e2]; exact hle

/-- `Ξ_n(𝔹; σ, ε)` inequalities weaken to `(1, ε')` when `1 ≤ σ` and `σ² ε ≤ ε'`
(`grad`, `collarBond`, `mass` carry `σ ε ≤ ε'`; `lap`, `mult`, `close` carry `σ² ε ≤ ε'`; `hnorm`
carries `(σ ε)² ≤ ε'²`). -/
theorem xiBounds_rescale {ν σ ε ε' : ℝ} {n : ℕ} {D : BgData G N} {h₀ : Fin N → ℝ}
    {φ : G.Ω 1 × Fin N → ℂ} {α : G.Ω 1 → ℂ} (hσ : 1 ≤ σ) (he : 0 < ε) (hle : σ ^ 2 * ε ≤ ε')
    (hb : XiBounds G ν n σ ε D h₀ φ α) : XiBounds G ν n 1 ε' D h₀ φ α := by
  obtain ⟨n1, n2, n3, -, -⟩ := rescale_nums hσ he hle
  refine ⟨fun x hx μ => ?_, fun x hx => ?_, fun x => ?_, fun x hx => ?_, fun z hz z' hz' hadj => ?_,
    fun z => ?_, ?_⟩
  · have hs := spacing_pos G (x := x)
    exact ⟨(hb.grad x hx μ).1.trans_le (div_le_div_of_nonneg_right n1 hs.le),
      (hb.grad x hx μ).2.trans_le (div_le_div_of_nonneg_right n1 hs.le)⟩
  · have hs := spacing_pos G (x := x)
    exact (hb.lap x hx).trans_le (div_le_div_of_nonneg_right n2 (by positivity))
  · exact (hb.mult x).trans_le n2
  · exact (hb.close x hx).trans_le n2
  · exact (hb.collarBond z hz z' hz' hadj).trans_le n1
  · exact (hb.mass z).trans_le n1
  · exact hb.hnorm.trans_le n3

/-- `Ξ^c_n(𝔹; σ, ε)` displacement inequalities weaken to `(1, ε')` when `1 ≤ σ`,
`σ² ε ≤ ε'` (and `0 < ε`). -/
theorem xiCBounds_rescale {ν σ ε ε' : ℝ} {Dr Dc : BgData G N}
    {Ψ'' h'' : Torus d (N₀ * L ^ k) → Fin N → ℂ} {φr φc : G.Ω 1 × Fin N → ℂ}
    {αr αc : G.Ω 1 → ℂ} (hσ : 1 ≤ σ) (he : 0 < ε) (hle : σ ^ 2 * ε ≤ ε')
    (hb : XiCBounds G ν σ ε Dr Dc Ψ'' h'' φr φc αr αc) :
    XiCBounds G ν 1 ε' Dr Dc Ψ'' h'' φr φc αr αc := by
  obtain ⟨n1, n2, n3, n4, n5⟩ := rescale_nums hσ he hle
  refine ⟨fun x hx μ => ?_, fun x hx => ?_, fun x => ?_, fun x => ?_, fun x hx => ?_,
    fun z hz z' hz' hadj => ?_, fun x hx => ?_, fun x => ?_⟩
  · have hs := spacing_pos G (x := x)
    exact ⟨(hb.grad x hx μ).1.trans_le (div_le_div_of_nonneg_right n1 hs.le),
      (hb.grad x hx μ).2.trans_le (div_le_div_of_nonneg_right n1 hs.le)⟩
  · have hs := spacing_pos G (x := x)
    exact (hb.lap x hx).trans_le (div_le_div_of_nonneg_right n2 (by positivity))
  · exact (hb.mult x).trans_le n2
  · exact (hb.val x).trans_le n4
  · exact (hb.close x hx).trans_le n2
  · exact (hb.collarBond z hz z' hz' hadj).trans_le n1
  · exact (hb.hAbs x hx).trans_le n5
  · exact (hb.hDot x).trans_le n3

/-- The displacement inequalities depend on the displacements only through their values on
`Ω₁ ∪ C(Ω₁)` (`Ψ''`) and on `Ω₁` (`h''`). -/
theorem xiCBounds_congr {ν σ ε : ℝ} {Dr Dc : BgData G N}
    {Ψ'' h'' Ψ''₂ h''₂ : Torus d (N₀ * L ^ k) → Fin N → ℂ} {φr φc : G.Ω 1 × Fin N → ℂ}
    {αr αc : G.Ω 1 → ℂ} (hΨ : ∀ x ∈ dataSites G, ∀ i, Ψ''₂ x i = Ψ'' x i)
    (hh : ∀ x ∈ G.Ω 1, ∀ i, h''₂ x i = h'' x i)
    (hb : XiCBounds G ν σ ε Dr Dc Ψ'' h'' φr φc αr αc) :
    XiCBounds G ν σ ε Dr Dc Ψ''₂ h''₂ φr φc αr αc where
  grad := hb.grad
  lap := hb.lap
  mult := hb.mult
  val := hb.val
  close x hx := by
    have e : (fun i => Ψ''₂ x i - blockAvg G (φc - φr) x i) =
        fun i => Ψ'' x i - blockAvg G (φc - φr) x i := by
      funext i; rw [hΨ x ((mem_dataSites G).2 (Or.inl hx)) i]
    rw [e]; exact hb.close x hx
  collarBond z hz z' hz' hadj := by
    have e : (fun i => Ψ''₂ z i - Ψ''₂ z' i) = fun i => Ψ'' z i - Ψ'' z' i := by
      funext i
      rw [hΨ z ((mem_dataSites G).2 (Or.inr hz)) i, hΨ z' ((mem_dataSites G).2 (Or.inr hz')) i]
    rw [e]; exact hb.collarBond z hz z' hz' hadj
  hAbs x hx := by
    have e : h''₂ x = h'' x := funext (hh x hx)
    rw [e]; exact hb.hAbs x hx
  hDot x := by
    have e : ∀ i, h''₂ (x : Torus d (N₀ * L ^ k)) i = h'' (x : Torus d (N₀ * L ^ k)) i :=
      hh _ x.2
    simp only [e]; exact hb.hDot x

/-- **Same-centre rescaling of `Ξ^c_n(𝔹; σ, ε)`** (exact statement): for `1 ≤ σ` and
`σ² ε ≤ ε'`, a member of `Ξ^c_n(𝔹; σ, ε)` with centre `(Ψ₀, h₀)` and displacement `(Ψ'', h'')` is
a member of `Ξ^c_n(𝔹; 1, ε')` with the same centre, and with any displacement `(Ψ''₂, h''₂)`
agreeing with `(Ψ'', h'')` on `Ω₁ ∪ C(Ω₁)` (resp. `Ω₁`).  Direction of the monotonicity: every
bound of `XiBounds`/`XiCBounds` is increasing in `ε` and in `σ`; `grad`, `collarBond`, `mass`
scale as `σ ε`, `lap`, `mult`, `close`, `hAbs` as `σ² ε`, `val` as `ε`, `hDot`, `hnorm` as
`(σ ε)²`; the real-part and union-domain conditions do not involve `(σ, ε)`. -/
theorem xiC_rescale_of_agree {a : ℕ → ℝ} {ν σ ε ε' : ℝ} {n : ℕ}
    {Ψ₀ : Torus d (N₀ * L ^ k) → Fin N → ℝ} {h₀ : Fin N → ℝ}
    {Ψ'' h'' Ψ''₂ h''₂ : Torus d (N₀ * L ^ k) → Fin N → ℂ} (hσ : 1 ≤ σ) (hle : σ ^ 2 * ε ≤ ε')
    (hΨ : ∀ x ∈ dataSites G, ∀ i, Ψ''₂ x i = Ψ'' x i) (hh : ∀ x ∈ G.Ω 1, ∀ i, h''₂ x i = h'' x i)
    (hX : XiC G a ν n σ ε Ψ₀ h₀ Ψ'' h'') : XiC G a ν n 1 ε' Ψ₀ h₀ Ψ''₂ h''₂ := by
  obtain ⟨-, he, Dr, Dc, hXr, hR, hU, hb⟩ := hX
  have hε' : ε ≤ ε' := (rescale_nums hσ he hle).2.2.2.1
  refine ⟨one_pos, he.trans_le hε', Dr, Dc,
    ⟨hXr.1, hXr.2.1, xiBounds_rescale hσ he hle hXr.2.2⟩,
    ⟨fun x hx i => by rw [hR.1 x hx i, hΨ x hx i],
      fun x hx i => by rw [hR.2 x hx i, hh x hx i]⟩, hU,
    xiCBounds_congr hΨ hh (xiCBounds_rescale hσ he hle hb)⟩

/-- **Same-centre rescaling of `Ξ^c_n(𝔹; σ, ε)`** with the same displacement. -/
theorem xiC_rescale {a : ℕ → ℝ} {ν σ ε ε' : ℝ} {n : ℕ}
    {Ψ₀ : Torus d (N₀ * L ^ k) → Fin N → ℝ} {h₀ : Fin N → ℝ}
    {Ψ'' h'' : Torus d (N₀ * L ^ k) → Fin N → ℂ} (hσ : 1 ≤ σ) (hle : σ ^ 2 * ε ≤ ε')
    (hX : XiC G a ν n σ ε Ψ₀ h₀ Ψ'' h'') : XiC G a ν n 1 ε' Ψ₀ h₀ Ψ'' h'' :=
  xiC_rescale_of_agree hσ hle (fun _ _ _ => rfl) (fun _ _ _ => rfl) hX

end Rescale

section RayDom

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- **The `dom` field of `RayInDomain` from the class radii and the chart smallness** (conditional).
Suppose for every point `q = (s, x)` of the real ray (`|s| ‖x‖ < p⁺`), every level `1 ≤ j ≤ k` and
every old polymer `X` there is a datum `D` of the generating set `𝔹_j(X) = C.Tm.gs j X` whose
raw data `(D.Ψ, D.h)` are the composed pair `S.pairRay j q`, and `D` realizes a member of
`Ξ^c_j(𝔹_j(X); C₀, ε_path)` (`XiCData`, the output of `InteractionHatE.eTerm_chain` with
`C₀ = scaledC0 d`), and `C₀² ε_path ≤ ε_j`.  Then the composed pair lies in `Ξ^c_j(𝔹_j(X); 1, ε_j)`
(`XiDom`), which is the `dom` field of `RayInDomain`. -/
theorem rayInDomain_dom_of_xiCData (S : StepSetting d L N₁ m₁ k N ϱ)
    (C : StepClass d L N₁ m₁ k N ϱ) (A : ℕ → ℝ) (μ : ℝ) (ε : ℕ → ℝ) (εpath pp : ℝ)
    (hε : ∀ j, 1 ≤ j → j ≤ k → scaledC0 d ^ 2 * εpath ≤ ε j)
    (hX : ∀ q : ℝ × S.E, |q.1| * ‖q.2‖ < pp → ∀ j, 1 ≤ j → j ≤ k → ∀ X, IsPolyDom C.m₀ j X →
      ∃ D : BgData (C.Tm.gs j X) N, D.Ψ = (S.pairRay (N := N) j q).1 ∧
        D.h = (S.pairRay (N := N) j q).2 ∧ XiCData (C.Tm.gs j X) A μ j (scaledC0 d) εpath D) :
    ∀ q : ℝ × S.E, |q.1| * ‖q.2‖ < pp → ∀ j, 1 ≤ j → j ≤ k → ∀ X, IsPolyDom C.m₀ j X →
      XiDom (C.Tm.gs j X) A μ j (ε j) (S.pairRay (N := N) j q).1 (S.pairRay (N := N) j q).2 := by
  intro q hq j h1 hjk X hXd
  obtain ⟨D, hΨ, hh, Ψ₀, h₀, Ψ'', h'', hxc, hR⟩ := hX q hq j h1 hjk X hXd
  have hσ : 1 ≤ scaledC0 d := by
    unfold scaledC0
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  refine ⟨Ψ₀, h₀, fun x i => D.Ψ x i - Ψ₀ x i, fun x i => D.h x i - h₀ i, ?_, ?_,
    xiC_rescale_of_agree hσ (hε j h1 hjk) (fun x hx i => ?_) (fun x hx i => ?_) hxc⟩
  · intro x i
    rw [← hΨ]; ring
  · intro x i
    rw [← hh]; ring
  · rw [hR.1 x hx i]; ring
  · rw [hR.2 x hx i]; ring

end RayDom

end Balaban.Fluctuation
