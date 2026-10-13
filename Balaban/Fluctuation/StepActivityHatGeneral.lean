/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.StepActivityHatSource
public import Balaban.Fluctuation.InteractionHatE
public import Balaban.Fluctuation.StepBaseDomain
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The step exponent of a general class is the value of the hat expansion

`StepActivityHat.Wone_zeroClass_eq_hat` and `StepActivityHatSource.Wtwo_zeroClass_eq_hat` identify
the two segments of the step exponent of the zero class with the potential part and the direct
source part of the function expanded by `interaction_expansion_hat`.  For a general class the
exponents have two more parts,

`W₁(s, ψ̂) = -β V^{(k)}(ψ^{(k)} + s ψ') + δℰ_k(s ψ')`,
`W₂(t, ψ̂; g) = ⟨g, φ_k(ψ^{(k)} + t ψ') - φ_k(ψ^{(k)})⟩ + (old observable increment)`,

and the expanded function has, for each old term `τ`, the part
`c_β · dirTermSrc (hatFun … (flComp (hBE τ) (hFE τ) (EE τ))) 1 ψ̂ ψ̂ u Θ`.

* `analyticAt_flComp_hatRay`: an old-term functional `flComp` is holomorphic along the complex ray
  of the hat variable (from `eTermFun_analytic`, `eTermFun_value` and the holomorphy of
  `flFieldOne` along the ray).
* `dirTermSrc_flComp_ray`: along the real ray its directional term is a difference of values,
  `F_τ(t ψ̂) - F_τ(0)`, with `F_τ(ψ̂) = hatFun … (flComp …) (Θ, ψ̂)` (no factor `t²`).
* `OldEnergyHatMatch`, `OldObsHatMatch`: the two **named open hypotheses**.  They say that the
  old-term functionals `EE τ`, `EM τ` given to the expansion are the old terms of the class `C`
  at the composed data of the step: on the support of `ν_{p₁}`,
  `β ∑_τ (F_τ(ψ̂) - F_τ(0)) = δℰ_k(ψ')` and
  `β ∑_τ (g_τ/β) (F_τ(ψ̂) - F_τ(0)) = δℱ_k(ψ', g) - ⟨g, φ_k(ψ^{(k)} + ψ') - φ_k(ψ^{(k)})⟩`.
  The left sides are evaluated at the datum `flDatumOne` of the generating sets `GkE τ`, `GjE τ`
  of the functional, with the complex solver of `GkE τ`; the right sides at the composed data
  `composedPairAt` of the whole-lattice sets, with the solver of `𝔹_k`.  Nothing in the tree
  compares the two for general generating sets.  Both hypotheses hold for the zero class with no
  old terms (`oldEnergyHatMatch_zeroClass`, `oldObsHatMatch_zeroClass`), and for any class whose
  old energy is constant along the fluctuation (`oldEnergyHatMatch_empty_of_dE_eq_zero`).
* `Wone_eq_hat_of_oldEnergyHatMatch` (first segment) and `Wtwo_eq_hat_of_oldObsHatMatch` (second
  segment): the general forms of the two zero-class identities, in the same normalization
  (`s²` on the potential part only, source factor `g/β`, outer factor `β`).

What is proved: under the two named hypotheses, the step exponent of a general class is the value
of the hat functionals of the physical expansion.  What is not proved: the two named hypotheses
for old-term functionals on localized generating sets.  The class terms enter only through
`S.dE C` and `S.dF C g`; no generating set of the class appears.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Analysis
  Balaban.Fluctuation Finset Matrix Filter Topology

section ERay

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱ₁ ϱ₂ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Gk : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁}
variable {Gj : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₂}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ r₀ eps δ₃ : ℝ} {X₀ X₁f : Finset (CTorus d L N₁ m₁ (k + 1))} {j : ℕ}
variable {Kc Cx c₂ BG₂ δ₁ δfl : ℝ}

/-- **An old-term functional is holomorphic along the complex ray of the hat variable**: for a
datum `D'` of `Ξ^c(𝔹_{k+1}; 1, ε)` and a hat variable `ψ̂` with `‖s ψ̂‖ < c_ψ`, the function
`λ ↦ flComp (rawOf D', hatLift cc D' (λ ψ̂))` is analytic at `λ = s`, for an old term `E` analytic
on `Ξ^c_j(𝔹_j(X); C₀, ε₂)`. -/
theorem analyticAt_flComp_hatRay
    (hB : BgSetting N Gp Gk Gj a₁ ν c BG κ r₀ eps δ₃ X₀ X₁f j)
    (hF : FlSetting N Gp Gk Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl X₁f)
    (hk : 1 ≤ k) (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1))
    (H : BgHyp d L (k + 1) ϱm (compWeight L a₁) ν) (hc7 : c7 d L N BG κ ≤ thm73C3 d L N)
    {R : ℝ} (hR : 2 ≤ R)
    (hsmR : 2 * (compC4 d * (bgK1 d L N * (xiC1 d * eps))) + 5 * (R * δ₁) ≤ bgC1 d L N)
    (hRs : R * δ₁ ≤ deltaStar d L N) (hsmall : cK2 d L N * (R * δ₁) < bgC0 d L N / 2)
    (hnum : cK2 d L N * δ₁ ≤ c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hnum' : cK2' d L N (famConst d L BG₂ κ) * δ₁ ≤
      c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4) (cc : ℂ) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    {E : RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ}
    (hEan : AnalyticOnNhd ℂ E (XiCRaw Gj (compWeight L a₁) ν j (scaledC0 d)
      (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)))
    {D' : BgData Gp N} (hD' : XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D')
    (ψh : unitPts Gp × Fin N → ℂ) {s : ℂ} (hs : ∀ p, ‖s * ψh p‖ < cψ) :
    AnalyticAt ℂ (fun l : ℂ =>
      flComp hB hF E (rawOf D', hatLift Gp a₁ ν hG' cc D' (l • ψh))) s := by
  classical
  have hC := flCore_of hB hF
  obtain ⟨Fk, hFkan, hFk⟩ := theorem72_analytic (G := Gk) (a := compWeight L a₁) (ν := ν)
    (N := N) hB.HBk
  have hU : ∀ᶠ l in 𝓝 s, ∀ p, ‖l * ψh p‖ ≤ cψ := by
    rw [Filter.eventually_all]
    intro p
    have hcont : ContinuousAt (fun l : ℂ => ‖l * ψh p‖) s := by fun_prop
    exact (hcont.eventually_lt continuousAt_const (hs p)).mono fun l hl => hl.le
  have hmem : ∀ l : ℂ, (∀ p, ‖l * ψh p‖ ≤ cψ) →
      hatLift Gp a₁ ν hG' cc D' (l • ψh) ∈ FlBallLC Hm δ₁ := fun l hl =>
    hatLift_mem_flBallLC hC hk hG hG' cc hcψ hMX hdm hα hsm hδ₁ hD'
      (fun p => by simpa using hl p)
  -- the triple of the datum along the ray
  let T : ℂ → ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) × (Hm.Ω 1 × Fin N → ℂ) ×
      (RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)) :=
    fun l => ((bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D',
        bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D'),
      flFieldOne Gp Hm BG₂ κ a₁ ν D' (hatLift Gp a₁ ν hG' cc D' (l • ψh)),
      (rawOf D', hatLift Gp a₁ ν hG' cc D' (l • ψh)))
  have hlift : AnalyticAt ℂ (fun l : ℂ => hatLift Gp a₁ ν hG' cc D' (l • ψh)) s := by
    have e : (fun l : ℂ => hatLift Gp a₁ ν hG' cc D' (l • ψh)) =
        fun l : ℂ => l • hatLift Gp a₁ ν hG' cc D' ψh :=
      funext fun l => hatLift_smul hG' cc D' ψh l
    rw [e]
    exact analyticAt_id.smul analyticAt_const
  have hTan : AnalyticAt ℂ T s := by
    refine AnalyticAt.prod analyticAt_const (AnalyticAt.prod ?_
      (AnalyticAt.prod analyticAt_const hlift))
    exact analyticAt_pi_iff.2 fun q => analyticAt_flFieldOne_hatRay hC hk hG hG' hB.ha₁ H hc7
      hR hsmR hRs hsmall hnum hnum' hMX hdm hα hsm cc hcψ hδ₁ hD' ψh hs q
  have hTs : T s ∈ FlRealLC Gp Hm a₁ ν BG κ eps X₁f BG₂ δ₁ :=
    triple_one_mem hC hD' (hmem s fun p => (hs p).le)
  have han : AnalyticAt ℂ (fun l : ℂ =>
      eTermFun Gp Gk Gj Hm (compWeight L a₁) Fk E (T l).1 (T l).2.1 (T l).2.2) s :=
    (eTermFun_analytic hB hF hFkan hFk hEan (T s) hTs).comp hTan
  refine han.congr ?_
  filter_upwards [hU] with l hl
  exact eTermFun_value hB hF hFk E hD' (hmem l hl)

end ERay

end Balaban.Localization

namespace Balaban.Fluctuation

open MeasureTheory Balaban Balaban.Localization Balaban.Multiscale
  Balaban.Background Balaban.SmallField Balaban.SmallField.Def6 Balaban.Analysis Finset Matrix Set
  Filter Topology

section Step

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

namespace StepSetting

variable (S : StepSetting d L N₁ m₁ k N ϱ)

/-- The path at parameter `1` of the scaled fluctuation variable is the path at parameter `s`:
`ψ^{(k)} + ψ'(s ψ̂) = ψ^{(k)} + s ψ'(ψ̂)`. -/
theorem psiAt_one_smul (s : ℝ) (x : S.E) : S.psiAt 1 (s • x) = S.psiAt s x := by
  unfold psiAt shiftU
  rw [map_smul, one_smul, smul_comm]

/-- The support of `ν_{p₁}` is star-shaped. -/
theorem chiFl_smul_eq_one (hp₁ : 0 < S.p₁) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) {x : S.E}
    (hx : chiFl S.U N S.p₁ x = 1) : chiFl S.U N S.p₁ (s • x) = 1 := by
  rw [chiFl_eq_one_iff hp₁] at hx ⊢
  calc ‖s • x‖ = s * ‖x‖ := by rw [norm_smul, Real.norm_of_nonneg hs.1]
    _ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right hs.2 (norm_nonneg _)
    _ < S.p₁ := by rw [one_mul]; exact hx

/-- The hat variable of the scaled fluctuation variable. -/
theorem hatC_smul (s : ℝ) (x : S.E) : S.hatC (s • x) = (s : ℂ) • S.hatC x :=
  S.yhat_smul s x

/-- `W₁` of a class is `W₁` of the zero class plus the old energy increment. -/
theorem Wone_eq_zeroClass_add_dE (C : StepClass d L N₁ m₁ k N ϱ) (s : ℝ) (x : S.E) :
    S.Wone C s x = S.Wone (zeroClass d L N₁ m₁ k N ϱ) s x + S.dE C (S.psiAt s x) := by
  rw [S.Wone_zeroClass_eq]
  rfl

end StepSetting

section Match

variable {c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ}

/-- **The old energy functionals of the expansion are the old energy of the class** (named open
hypothesis).  For every fluctuation variable `ψ̂` in the support of `ν_{p₁}`,

`β ∑_τ (F_τ(ψ̂) - F_τ(0)) = δℰ_k(ψ')`,  `F_τ(ψ̂) = hatFun … (flComp (hBE τ) (hFE τ) (EE τ)) (Θ, ψ̂)`,

where `Θ = rawOf D'` is the block datum of the step, `ψ' = β_k^{-1/2} C^{(k)1/2} ψ̂` and
`δℰ_k(ψ') = ℰ_k(ψ^{(k)} + ψ') - ℰ_k(ψ^{(k)})` is the old energy increment `S.dE C` of the class.
The factor `β` is the outer factor `c_β` of the expansion: the functionals `EE τ` carry the old
terms divided by `β`. -/
def OldEnergyHatMatch (S : StepSetting d L N₁ m₁ k N ϱ) (C : StepClass d L N₁ m₁ k N ϱ)
    {τι : Type*} [DecidableEq τι] (𝒯E : Finset τι) {ϱ₁ ϱ₂ : τι → ℝ}
    {GkE : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₁ τ)}
    {GjE : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₂ τ)} {r₀ δ₃ δfl : ℝ}
    {X₀E X₁E : τι → Finset (CTorus d L N₁ m₁ (k + 1))} {jE : τι → ℕ}
    (hBE : ∀ τ ∈ 𝒯E, BgSetting N S.G' (GkE τ) (GjE τ) S.a₁ S.ν c BG κ r₀ eps δ₃ (X₀E τ) (X₁E τ)
      (jE τ))
    (hFE : ∀ τ ∈ 𝒯E, FlSetting N S.G' (GkE τ) (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν κ BG eps δ₃ Kc Cx c₂
      BG₂ δ₁ δfl (X₁E τ))
    (EE : τι → RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ) : Prop :=
  ∀ x : S.E, chiFl S.U N S.p₁ x = 1 →
    (S.β : ℂ) * ∑ τ ∈ 𝒯E, (if h : τ ∈ 𝒯E then
      hatFun S.G' S.a₁ S.ν eps S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
          (flComp (hBE τ h) (hFE τ h) (EE τ)) (rawOf S.D', S.hatC x) -
        hatFun S.G' S.a₁ S.ν eps S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
          (flComp (hBE τ h) (hFE τ h) (EE τ)) (rawOf S.D', 0) else 0) =
      S.dE C (S.psiAt 1 x)

/-- **The old observable functionals of the expansion are the old observable terms of the class**
(named open hypothesis), for the source `g`.  For every `ψ̂` in the support of `ν_{p₁}`,

`β ∑_τ (g_{y_τ, i_τ}/β) (F_τ(ψ̂) - F_τ(0)) = δℱ_k(ψ', g) - ⟨g, φ_k(ψ^{(k)} + ψ') - φ_k(ψ^{(k)})⟩`,

with `F_τ(ψ̂) = hatFun … (flComp (hBM τ) (hFM τ) (EM τ)) (Θ, ψ̂)`.  The right side is the increment
`S.dF C g` of the class minus that of the zero class (the direct source part).  The source factor
`g/β` and the outer factor `β` are those of the expansion. -/
def OldObsHatMatch (S : StepSetting d L N₁ m₁ k N ϱ) (C : StepClass d L N₁ m₁ k N ϱ)
    (g : Fld d L N₁ m₁ (k + 1) N)
    {μι : Type*} [DecidableEq μι] (𝒯M : Finset μι) {ϱ₁M ϱ₂M : μι → ℝ}
    {GkM : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₁M τ)}
    {GjM : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₂M τ)} {r₀ δ₃ δfl : ℝ}
    {X₀M X₁M : μι → Finset (CTorus d L N₁ m₁ (k + 1))} {jM : μι → ℕ}
    (ys : μι → CTorus d L N₁ m₁ (k + 1)) (is : μι → Fin N)
    (hBM : ∀ τ ∈ 𝒯M, BgSetting N S.G' (GkM τ) (GjM τ) S.a₁ S.ν c BG κ r₀ eps δ₃ (X₀M τ) (X₁M τ)
      (jM τ))
    (hFM : ∀ τ ∈ 𝒯M, FlSetting N S.G' (GkM τ) (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν κ BG eps δ₃ Kc Cx c₂
      BG₂ δ₁ δfl (X₁M τ))
    (EM : μι → RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ) : Prop :=
  ∀ x : S.E, chiFl S.U N S.p₁ x = 1 →
    (S.β : ℂ) * ∑ τ ∈ 𝒯M, (if h : τ ∈ 𝒯M then
      (g (ys τ) (is τ) / (S.β : ℂ)) *
        (hatFun S.G' S.a₁ S.ν eps S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
            (flComp (hBM τ h) (hFM τ h) (EM τ)) (rawOf S.D', S.hatC x) -
          hatFun S.G' S.a₁ S.ν eps S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
            (flComp (hBM τ h) (hFM τ h) (EM τ)) (rawOf S.D', 0)) else 0) =
      S.dF C g (S.psiAt 1 x) - S.dF (zeroClass d L N₁ m₁ k N ϱ) g (S.psiAt 1 x)

/-- **`OldEnergyHatMatch` holds with no old-term functionals when the old energy is constant along
the fluctuation**: if `δℰ_k(ψ') = 0` on the support of `ν_{p₁}`, the empty family matches. -/
theorem oldEnergyHatMatch_empty_of_dE_eq_zero (S : StepSetting d L N₁ m₁ k N ϱ)
    (C : StepClass d L N₁ m₁ k N ϱ)
    {τι : Type*} [DecidableEq τι] {ϱ₁ ϱ₂ : τι → ℝ}
    {GkE : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₁ τ)}
    {GjE : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₂ τ)} {r₀ δ₃ δfl : ℝ}
    {X₀E X₁E : τι → Finset (CTorus d L N₁ m₁ (k + 1))} {jE : τι → ℕ}
    (hBE : ∀ τ ∈ (∅ : Finset τι), BgSetting N S.G' (GkE τ) (GjE τ) S.a₁ S.ν c BG κ r₀ eps δ₃
      (X₀E τ) (X₁E τ) (jE τ))
    (hFE : ∀ τ ∈ (∅ : Finset τι), FlSetting N S.G' (GkE τ) (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν κ BG eps
      δ₃ Kc Cx c₂ BG₂ δ₁ δfl (X₁E τ))
    (EE : τι → RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ)
    (h0 : ∀ x : S.E, chiFl S.U N S.p₁ x = 1 → S.dE C (S.psiAt 1 x) = 0) :
    OldEnergyHatMatch S C ∅ hBE hFE EE := fun x hx => by
  rw [h0 x hx]
  simp

/-- **`OldEnergyHatMatch` is inhabited**: the zero class with no old-term functionals, at every
step. -/
theorem oldEnergyHatMatch_zeroClass (S : StepSetting d L N₁ m₁ k N ϱ)
    {τι : Type*} [DecidableEq τι] {ϱ₁ ϱ₂ : τι → ℝ}
    {GkE : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₁ τ)}
    {GjE : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₂ τ)} {r₀ δ₃ δfl : ℝ}
    {X₀E X₁E : τι → Finset (CTorus d L N₁ m₁ (k + 1))} {jE : τι → ℕ}
    (hBE : ∀ τ ∈ (∅ : Finset τι), BgSetting N S.G' (GkE τ) (GjE τ) S.a₁ S.ν c BG κ r₀ eps δ₃
      (X₀E τ) (X₁E τ) (jE τ))
    (hFE : ∀ τ ∈ (∅ : Finset τι), FlSetting N S.G' (GkE τ) (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν κ BG eps
      δ₃ Kc Cx c₂ BG₂ δ₁ δfl (X₁E τ))
    (EE : τι → RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ) :
    OldEnergyHatMatch S (zeroClass d L N₁ m₁ k N ϱ) ∅ hBE hFE EE :=
  oldEnergyHatMatch_empty_of_dE_eq_zero S _ hBE hFE EE fun x _ => by
    unfold StepSetting.dE
    show EcompAt 0 (zeroTerms d L N₁ m₁ (k + 1) N ϱ) S.a S.ν (Nat.le_succ k) _ -
      EcompAt 0 (zeroTerms d L N₁ m₁ (k + 1) N ϱ) S.a S.ν (Nat.le_succ k) _ = 0
    rw [EcompAt_zero, EcompAt_zero, sub_zero]

/-- **`OldObsHatMatch` holds with no old-term functionals when the observable increment of the
class is the direct source part** (the old observable terms are constant along the fluctuation). -/
theorem oldObsHatMatch_empty_of_dF_eq (S : StepSetting d L N₁ m₁ k N ϱ)
    (C : StepClass d L N₁ m₁ k N ϱ) (g : Fld d L N₁ m₁ (k + 1) N)
    {μι : Type*} [DecidableEq μι] {ϱ₁M ϱ₂M : μι → ℝ}
    {GkM : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₁M τ)}
    {GjM : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₂M τ)} {r₀ δ₃ δfl : ℝ}
    {X₀M X₁M : μι → Finset (CTorus d L N₁ m₁ (k + 1))} {jM : μι → ℕ}
    (ys : μι → CTorus d L N₁ m₁ (k + 1)) (is : μι → Fin N)
    (hBM : ∀ τ ∈ (∅ : Finset μι), BgSetting N S.G' (GkM τ) (GjM τ) S.a₁ S.ν c BG κ r₀ eps δ₃
      (X₀M τ) (X₁M τ) (jM τ))
    (hFM : ∀ τ ∈ (∅ : Finset μι), FlSetting N S.G' (GkM τ) (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν κ BG eps
      δ₃ Kc Cx c₂ BG₂ δ₁ δfl (X₁M τ))
    (EM : μι → RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ)
    (h0 : ∀ x : S.E, chiFl S.U N S.p₁ x = 1 →
      S.dF C g (S.psiAt 1 x) = S.dF (zeroClass d L N₁ m₁ k N ϱ) g (S.psiAt 1 x)) :
    OldObsHatMatch S C g ∅ ys is hBM hFM EM := fun x hx => by
  rw [h0 x hx]
  simp

/-- **`OldObsHatMatch` is inhabited**: the zero class with no old-term functionals, at every step
and for every source. -/
theorem oldObsHatMatch_zeroClass (S : StepSetting d L N₁ m₁ k N ϱ)
    (g : Fld d L N₁ m₁ (k + 1) N)
    {μι : Type*} [DecidableEq μι] {ϱ₁M ϱ₂M : μι → ℝ}
    {GkM : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₁M τ)}
    {GjM : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₂M τ)} {r₀ δ₃ δfl : ℝ}
    {X₀M X₁M : μι → Finset (CTorus d L N₁ m₁ (k + 1))} {jM : μι → ℕ}
    (ys : μι → CTorus d L N₁ m₁ (k + 1)) (is : μι → Fin N)
    (hBM : ∀ τ ∈ (∅ : Finset μι), BgSetting N S.G' (GkM τ) (GjM τ) S.a₁ S.ν c BG κ r₀ eps δ₃
      (X₀M τ) (X₁M τ) (jM τ))
    (hFM : ∀ τ ∈ (∅ : Finset μι), FlSetting N S.G' (GkM τ) (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν κ BG eps
      δ₃ Kc Cx c₂ BG₂ δ₁ δfl (X₁M τ))
    (EM : μι → RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ) :
    OldObsHatMatch S (zeroClass d L N₁ m₁ k N ϱ) g ∅ ys is hBM hFM EM :=
  oldObsHatMatch_empty_of_dF_eq S _ g ys is hBM hFM EM fun _ _ => rfl

end Match

section Segments

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

include R0 hD hc7 hR hsmR hRs hsmall hnum hnum' hMX hdm hα hsm hp₁ hcψ hpc hδ₁ in
/-- **The directional term of an old-term functional along the real ray is a difference of
values**: for `t ∈ [0,1]` and `χ_fl(ψ̂) = 1`,
`dirTermSrc (hatFun … (flComp …)) 1 ψ̂ ψ̂ t Θ = F(t ψ̂) - F(0)` with
`F(ψ̂) = hatFun … (flComp …) (Θ, ψ̂)`.  There is no factor `t²`. -/
theorem dirTermSrc_flComp_ray {ϱ₁ ϱ₂ : ℝ}
    {Gk : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁}
    {Gj : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₂} {r₀ δ₃ δfl : ℝ}
    {X₀ X₁f : Finset (CTorus d L N₁ m₁ (k + 1))} {j : ℕ}
    (hB : BgSetting N S.G' Gk Gj S.a₁ S.ν c BG κ r₀ eps δ₃ X₀ X₁f j)
    (hF : FlSetting N S.G' Gk (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl X₁f)
    {E : RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ}
    (hEan : AnalyticOnNhd ℂ E (XiCRaw Gj (compWeight L S.a₁) S.ν j (scaledC0 d)
      (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) {x : S.E} (hx : chiFl S.U N S.p₁ x = 1) :
    dirTermSrc (hatFun S.G' S.a₁ S.ν eps S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
        (flComp hB hF E)) (fun _ => (1 : ℂ)) (S.hatC x) (S.hatC x) (t : ℂ) (rawOf S.D') =
      hatFun S.G' S.a₁ S.ν eps S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
          (flComp hB hF E) (rawOf S.D', S.hatC (t • x)) -
        hatFun S.G' S.a₁ S.ν eps S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
          (flComp hB hF E) (rawOf S.D', 0) := by
  set cc : ℂ := ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) with hcc
  let G : ℂ → ℂ := fun l =>
    hatFun S.G' S.a₁ S.ν eps S.hG' cc (flComp hB hF E) (rawOf S.D', l • yhat x)
  have hAn : ∀ r : ℝ, r ∈ Icc (0 : ℝ) 1 → AnalyticAt ℂ G (r : ℂ) := by
    intro r hr
    have hb : ∀ p, ‖(r : ℂ) * yhat x p‖ < cψ := fun p => by
      have := S.norm_smul_yhat_le hp₁ hr hx p
      have e : ((r : ℂ) • yhat x) p = (r : ℂ) * yhat x p := rfl
      rw [e] at this
      exact lt_of_le_of_lt this hpc
    have := analyticAt_flComp_hatRay hB hF S.hk1 S.hG S.hG' R0.H hc7 hR hsmR hRs hsmall hnum
      hnum' hMX hdm hα hsm cc hcψ hδ₁ hEan hD (yhat x) hb
    refine this.congr (Filter.Eventually.of_forall fun l => ?_)
    exact (hatFun_rawOf S.hG' cc _ hD _).symm
  rw [dirTermSrc_ray _ (rawOf S.D') (S.hatC x) G (fun l => rfl) hAn ht, S.hatC_smul]
  show G (t : ℂ) - G 0 = _
  have h0 : G 0 = hatFun S.G' S.a₁ S.ν eps S.hG' cc (flComp hB hF E) (rawOf S.D', 0) := by
    show hatFun S.G' S.a₁ S.ν eps S.hG' cc (flComp hB hF E) (rawOf S.D', (0 : ℂ) • yhat x) = _
    rw [zero_smul]
  rw [h0]
  rfl

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

include hC R0 hlt hD hc7 hR hsmR hRs hsmall hnum hnum' hMX hdm hα hsm hp₁ hcψ hpc hδ₁ hEanE
  hmatchE in
/-- **T1: the first segment of the step exponent of a general class is the value of the hat
expansion.**  Let the old-term functionals `EE τ` of the expansion be analytic on their domains and
represent the old energy of the class `C` (`OldEnergyHatMatch`, the named open hypothesis).  For
`s ∈ [0,1]` and `ψ̂` in the support of `ν_{p₁}`,

`s² · ((-β) · raySrc3 (hatFun … (interactionOne …)) (1-t)²/2 ψ̂ ψ̂ s Θ)
  + β ∑_τ dirTermSrc (hatFun … (flComp (hBE τ) (hFE τ) (EE τ))) 1 ψ̂ ψ̂ s Θ = W₁(s, ψ̂)`.

The factor `s²` multiplies the potential part only; the old-term parts are differences of values
along the ray.  For the zero class and no old terms this is `Wone_zeroClass_eq_hat`. -/
theorem Wone_eq_hat_of_oldEnergyHatMatch {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) {x : S.E}
    (hx : chiFl S.U N S.p₁ x = 1) :
    (s : ℂ) ^ 2 * ((-(S.β : ℂ)) * raySrc3 (hatFun S.G' S.a₁ S.ν eps S.hG'
        ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
        (interactionOne S.hG S.hG' (le_refl (k + 1)) S.a₁ S.ν eps)) taylorWeight (S.hatC x)
        (S.hatC x) (s : ℂ) (rawOf S.D')) +
      (S.β : ℂ) * ∑ τ ∈ 𝒯E, (if h : τ ∈ 𝒯E then
        dirTermSrc (hatFun S.G' S.a₁ S.ν eps S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
          (flComp (hBE τ h) (hFE τ h) (EE τ))) (fun _ => (1 : ℂ)) (S.hatC x) (S.hatC x) (s : ℂ)
          (rawOf S.D') else 0) = S.Wone C s x := by
  have hV := S.Wone_zeroClass_eq_hat hC R0 hlt (baseDomain_of_rayData R0) hD hc7
    (lt_of_lt_of_le one_lt_two hR) hsmR hMX hdm hα hsm hp₁ hcψ hpc hδ₁ hs hx
  have hm := hmatchE (s • x) (S.chiFl_smul_eq_one hp₁ hs hx)
  rw [S.psiAt_one_smul] at hm
  rw [S.Wone_eq_zeroClass_add_dE, ← hV, ← hm]
  congr 2
  refine Finset.sum_congr rfl fun τ hτ => ?_
  rw [dite_eq_left hτ, dite_eq_left hτ]
  exact S.dirTermSrc_flComp_ray R0 hD hc7 hR hsmR hRs hsmall hnum hnum' hMX hdm hα hsm hp₁ hcψ
    hpc hδ₁ (hBE τ hτ) (hFE τ hτ) (hEanE τ hτ) hs hx

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

include hC R0 hlt hD hc7 hR hsmR hRs hsmall hnum hnum' hMX hdm hα hsm hp₁ hcψ hpc hδ₁ hEanM
  hmatchM in
/-- **T2: the second segment of the step exponent of a general class is the value of the hat
expansion.**  Let the old observable functionals `EM τ` of the expansion be analytic on their
domains and represent the old observable terms of the class `C` for the source `g`
(`OldObsHatMatch`, the named open hypothesis).  For `t ∈ [0,1]` and `ψ̂` in the support of `ν_{p₁}`,

`β ∑_s (g_s/β) · dirTermSrc (hatFun … (svec (flFieldOne …) s)) 1 ψ̂ ψ̂ t Θ
  + β ∑_τ (g_{y_τ,i_τ}/β) · dirTermSrc (hatFun … (flComp (hBM τ) (hFM τ) (EM τ))) 1 ψ̂ ψ̂ t Θ
  = W₂(t, ψ̂; g)`,

with the source factor `g/β` and the outer factor `β` of the expansion, and no factor `t²`.  For
the zero class and no old terms this is `Wtwo_zeroClass_eq_hat`. -/
theorem Wtwo_eq_hat_of_oldObsHatMatch {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) {x : S.E}
    (hx : chiFl S.U N S.p₁ x = 1) :
    (S.β : ℂ) * (∑ s : CTorus d L N₁ m₁ (k + 1) × Fin N, (g s.1 s.2 / (S.β : ℂ)) *
        dirTermSrc (hatFun S.G' S.a₁ S.ν eps S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
          (onXi S.G' S.a₁ S.ν eps
            (fun D ψ' => svec (stepG d L N₁ m₁ k ϱ)
              (flFieldOne S.G' (stepG d L N₁ m₁ k ϱ) BG₂ κ S.a₁ S.ν D ψ') s.1 s.2)))
          (fun _ => (1 : ℂ)) (S.hatC x) (S.hatC x) (t : ℂ) (rawOf S.D')) +
      (S.β : ℂ) * ∑ τ ∈ 𝒯M, (if h : τ ∈ 𝒯M then
        (g (ys τ) (is τ) / (S.β : ℂ)) *
          dirTermSrc (hatFun S.G' S.a₁ S.ν eps S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
            (flComp (hBM τ h) (hFM τ h) (EM τ))) (fun _ => (1 : ℂ)) (S.hatC x) (S.hatC x) (t : ℂ)
            (rawOf S.D') else 0) = S.Wtwo C g t x := by
  have hT := S.Wtwo_zeroClass_eq_hat hC R0 hlt hD hc7 hR hsmR hRs hsmall hnum hnum' hMX hdm hα
    hsm hp₁ hcψ hpc hδ₁ g ht hx
  have hm := hmatchM (t • x) (S.chiFl_smul_eq_one hp₁ ht hx)
  rw [S.psiAt_one_smul] at hm
  have hB : (S.β : ℂ) * ∑ τ ∈ 𝒯M, (if h : τ ∈ 𝒯M then
        (g (ys τ) (is τ) / (S.β : ℂ)) *
          dirTermSrc (hatFun S.G' S.a₁ S.ν eps S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
            (flComp (hBM τ h) (hFM τ h) (EM τ))) (fun _ => (1 : ℂ)) (S.hatC x) (S.hatC x) (t : ℂ)
            (rawOf S.D') else 0) =
      S.dF C g (S.psiAt t x) - S.dF (zeroClass d L N₁ m₁ k N ϱ) g (S.psiAt t x) := by
    rw [← hm]
    congr 1
    refine Finset.sum_congr rfl fun τ hτ => ?_
    rw [dite_eq_left hτ, dite_eq_left hτ]
    rw [S.dirTermSrc_flComp_ray R0 hD hc7 hR hsmR hRs hsmall hnum hnum' hMX hdm hα hsm hp₁ hcψ
      hpc hδ₁ (hBM τ hτ) (hFM τ hτ) (hEanM τ hτ) ht hx]
  rw [hT, hB]
  show S.dF (zeroClass d L N₁ m₁ k N ϱ) g (S.psiAt t x) +
    (S.dF C g (S.psiAt t x) - S.dF (zeroClass d L N₁ m₁ k N ϱ) g (S.psiAt t x)) =
      S.dF C g (S.psiAt t x)
  ring

end StepSetting

end Segments

end Step

end Balaban.Fluctuation
