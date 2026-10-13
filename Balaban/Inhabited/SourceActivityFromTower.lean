/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.SourceDirectTermsFromTower
public import Balaban.Inhabited.SourceActivityScale
public import Balaban.Fluctuation.StepActivityDirectBound
public import Balaban.Fluctuation.SourceSliceScaled
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The zero-class source activity at the shared tower, with one label system for all sources

The landed `sourceActivityC_scale` chooses the labels of the activity anew for each source `g`
(the direct terms are re-selected inside `∀ g`), so the activity records at different sources
cannot be combined.  Here, for one tower `T : StepTower κmin` and its per-scale package
`D : StepScaleData T …`, the domain family `𝒴` is chosen once, before the source, from the
direct terms `sourceDirectTerms_scale_fromTower`; the records at every source `g` of the strict
`ℓ¹` ball have the label type `{Y // Y ∈ 𝒴} ⊕ {Y // Y ∈ 𝒴}`, the labels
`(thickLabels 𝒴 hdom).sum (thickLabels 𝒴 hdom)` and the block split `S.blockSplit 1 hp`, the
rates `κ₀ = T.κ0`, `κ' = T.κ'`, `κ_H = 2 T.κdec - 1`, the entropy constant
`2 (K₀(T.κ0) + 1)`, and the same prefactor bound as the landed theorem.

* `stepActivityBound_zeroClass_source_of_directTerms_exposed`: the landed assembler of two
  `DirectTerms` instances with its record fields returned (labels, block split, exponents).
* `stepActivityBound_zeroClass_source_of_directTerms_shared`: the same for instances with the
  same domain family.
* `stepActivityBoundC_of_activityBound_exposed`: the complex record copies all fields.
* `sourceActivityC_scale_fromTower`: the endpoint.

The chart/determinant joint endpoint and the marks are not here.
-/

@[expose] public section

namespace Balaban.Fluctuation

open MeasureTheory Balaban Balaban.Localization Balaban.Multiscale Balaban.Polymer
  Balaban.Background Balaban.SmallField Balaban.SmallField.Def6 Balaban.Analysis Finset Matrix Set
  Metric

section Source

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ} {c BG κ eps : ℝ}

variable
    (S : StepSetting d L N₁ m₁ k N ϱ)
  {ρ εU κ0 κ' Kc' a : ℝ} {Kc Cx c₂ BG₂ δ₁ δc : ℝ}
  (hC : FlCore N S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
  {R₁ : ℝ} (hR₁ : 1 < R₁) {r Rσ : ℝ} (hr : 0 < r)
  {cψ : ℝ} (hcψ : 0 ≤ cψ)
  (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
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
  {m₀ : ℕ}
  (hRσ : 0 < Rσ) (hc : (Rσ * R₁ + r) * ρ < cψ)
  (hD : XiCData S.G' (compWeight L S.a₁) S.ν (k + 1) 1 eps S.D')
  (hN : L ^ m₀ ∣ N₁) (hp : 0 < S.p₁) (hpρ : S.p₁ ≤ ρ)
  (hεpos : 0 < εU)
  (hκE : aEnt d L + 1 ≤ κ0) (hKc : K0 d L κ0 + 1 ≤ Kc') (hκ' : 0 ≤ κ')
  (hκa : κ' + 3 * κ0 + c1 d L + 3 / 2 ≤ a)
  (hDA : 2 * (Rσ * εU) ≤ 1 / (8 * (2 * Kc') ^ 3 * c1 d L *
    Real.exp ((a - 2 * κ0) * cG d L + c1 d L + κ' * cG d L)))
  {pp : ℝ} (R0 : S.RayData pp) (hlt : S.p₁ < pp)
  (hRσ1 : 1 < Rσ)
  {SΛ : Set (RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ))}
  {XW : Set (((S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)) × ((S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)))}
  {val : ((S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)) → ((S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)) →
    ℂ → (RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)) → ℂ}
  {AgΘ : Set (CTorus d L N₁ m₁ (k + 1)) →
    (RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)) →
    (RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)) → Prop}
  {AgF : Set (CTorus d L N₁ m₁ (k + 1)) →
    ((S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)) → ((S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)) → Prop}
  (g : Fld d L N₁ m₁ (k + 1) N)
  {SΛ₀ SΛg : Set (RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ))}
  {XW₀ XWg : Set (((S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)) × ((S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)))}
  {val₀ valg : ((S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)) → ((S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)) →
    ℂ → (RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)) → ℂ}
  {AgΘ₀ AgΘg : Set (CTorus d L N₁ m₁ (k + 1)) →
    (RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)) →
    (RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)) → Prop}
  {AgF₀ AgFg : Set (CTorus d L N₁ m₁ (k + 1)) →
    ((S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)) → ((S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)) → Prop}
  (I₀ : DirectTerms S m₀ hp (fun ψ => (ψ, ψ)) ρ Rσ εU a
    (rawOf S.D', (0 : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)) SΛ₀ XW₀ val₀ AgΘ₀ AgF₀)
  (Ig : DirectTerms S m₀ hp (fun ψ => (ψ, ψ)) ρ Rσ εU a
    (rawOf S.D', fun y i => g y i / (S.β : ℂ)) SΛg XWg valg AgΘg AgFg)
  (hval₀ : ∀ (x : S.E) (u : ℂ), val₀ (S.hatC x, S.hatC x) (S.hatC x, S.hatC x) u
      (rawOf S.D', (0 : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)) =
    (-(S.β : ℂ)) * raySrc3 (hatFun S.G' S.a₁ S.ν eps S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
      (interactionOne S.hG S.hG' (le_refl (k + 1)) S.a₁ S.ν eps)) taylorWeight (S.hatC x)
      (S.hatC x) u (rawOf S.D'))
  (hvalg : ∀ (x : S.E) (u : ℂ), valg (S.hatC x, S.hatC x) (S.hatC x, S.hatC x) u
      (rawOf S.D', fun y i => g y i / (S.β : ℂ)) =
    (-(S.β : ℂ)) * raySrc3 (hatFun S.G' S.a₁ S.ν eps S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
      (interactionOne S.hG S.hG' (le_refl (k + 1)) S.a₁ S.ν eps)) taylorWeight (S.hatC x)
      (S.hatC x) u (rawOf S.D') +
    (S.β : ℂ) * (∑ s : CTorus d L N₁ m₁ (k + 1) × Fin N, (g s.1 s.2 / (S.β : ℂ)) *
      dirTermSrc (hatFun S.G' S.a₁ S.ν eps S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
        (onXi S.G' S.a₁ S.ν eps
          (fun D ψ' => svec (stepG d L N₁ m₁ k ϱ)
            (flFieldOne S.G' (stepG d L N₁ m₁ k ϱ) BG₂ κ S.a₁ S.ν D ψ') s.1 s.2)))
        (fun _ => (1 : ℂ)) (S.hatC x) (S.hatC x) u (rawOf S.D')))

include hC hR₁ hr hcψ hMX hdm hα hsmX hδ₁ hc7 hR hRs hsmall hnum hnum' hsm hRσ hc hD hN hp hpρ hεpos hκE hKc hκ' hκa hDA R0 hlt hRσ1 I₀ Ig hval₀ hvalg

/-- **The assembler of `stepActivityBound_zeroClass_source_of_directTerms` with its label
fields exposed.**  The record is the one built in the landed proof; besides `κ_H = a`,
`ε_H = 2 R_σ ε_U` and `K_c = 2 K_c'`, the conclusion returns the block scale `m₀`, the label type
`{Y // Y ∈ I₀.𝒴} ⊕ {Y // Y ∈ Ig.𝒴}`, the labels `(thickLabels I₀.𝒴 I₀.dom).sum
(thickLabels Ig.𝒴 Ig.dom)`, the block split `S.blockSplit m₀ hp` (the label equality is
`HEq` since `Lab` depends on `Lb`), and the entropy exponents `κ₀`, `κ'`. -/
theorem stepActivityBound_zeroClass_source_of_directTerms_exposed :
    ∃ B : StepActivityBound S (zeroClass d L N₁ m₁ k N ϱ) g,
      B.m₀ = m₀ ∧ B.Lb = ({Y // Y ∈ I₀.𝒴} ⊕ {Y // Y ∈ Ig.𝒴}) ∧
      HEq B.Lab ((thickLabels I₀.𝒴 I₀.dom).sum (thickLabels Ig.𝒴 Ig.dom)) ∧
      HEq B.BS (S.blockSplit m₀ hp) ∧ B.κ0 = κ0 ∧ B.κ' = κ' ∧
      B.κH = a ∧ B.εH = 2 * (Rσ * εU) ∧ B.Kc = 2 * Kc' := by
  classical
  have hbase := StepSetting.baseDomain_of_rayData R0
  have hpc : S.p₁ < cψ := p₁_lt_of_margin hp hpρ hRσ1 hR₁ hr hc
  have hρ : 0 < ρ := lt_of_lt_of_le hp hpρ
  have hK0 : K0 d L κ0 ≤ Kc' := by linarith
  have hK00 : 0 ≤ K0 d L κ0 := by
    unfold K0
    exact div_nonneg (Real.exp_pos _).le (sub_nonneg.2 (Real.exp_le_one_iff.2 (by norm_num)))
  have hεR : 0 < Rσ * εU := mul_pos hRσ hεpos
  obtain ⟨Ahat, hdiff, hid⟩ := labelAct_of_directTerms S m₀ I₀ hN hρ hRσ.le hεpos.le hκE hK0
  obtain ⟨Ag, hdiff', hid'⟩ := labelAct_of_directTerms S m₀ Ig hN hρ hRσ.le hεpos.le hκE hK0
  have hcfun : ∀ s : ℝ, ‖((if s ∈ Icc (0 : ℝ) 1 then s ^ 2 else 0 : ℝ) : ℂ)‖ ≤ 1 :=
    norm_ite_sq_le
  have key0 : ∀ u : ℝ, u ∈ Icc (0 : ℝ) 1 → ∀ᵐ x ∂S.nuFl,
      ∑ y, (Ahat (u : ℂ)).H y ((S.blockSplit m₀ hp).restr x) =
        (-(S.β : ℂ)) * raySrc3 (hatFun S.G' S.a₁ S.ν eps S.hG'
          ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
          (interactionOne S.hG S.hG' (le_refl (k + 1)) S.a₁ S.ν eps)) taylorWeight (S.hatC x)
          (S.hatC x) (u : ℂ) (rawOf S.D') := by
    intro u hu
    filter_upwards [S.ae_hatOf_restr m₀ hρ hp hpρ] with x hx
    rw [hid (u : ℂ) (norm_ofReal_lt_of_mem hu hRσ1), hx, hval₀]
  have keyg : ∀ u : ℝ, u ∈ Icc (0 : ℝ) 1 → ∀ᵐ x ∂S.nuFl,
      ∑ y, (Ag (u : ℂ)).H y ((S.blockSplit m₀ hp).restr x) =
        (-(S.β : ℂ)) * raySrc3 (hatFun S.G' S.a₁ S.ν eps S.hG'
          ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
          (interactionOne S.hG S.hG' (le_refl (k + 1)) S.a₁ S.ν eps)) taylorWeight (S.hatC x)
          (S.hatC x) (u : ℂ) (rawOf S.D') +
        (S.β : ℂ) * (∑ s : CTorus d L N₁ m₁ (k + 1) × Fin N, (g s.1 s.2 / (S.β : ℂ)) *
          dirTermSrc (hatFun S.G' S.a₁ S.ν eps S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
            (onXi S.G' S.a₁ S.ν eps
              (fun D ψ' => svec (stepG d L N₁ m₁ k ϱ)
                (flFieldOne S.G' (stepG d L N₁ m₁ k ϱ) BG₂ κ S.a₁ S.ν D ψ') s.1 s.2)))
            (fun _ => (1 : ℂ)) (S.hatC x) (S.hatC x) (u : ℂ) (rawOf S.D')) := by
    intro u hu
    filter_upwards [S.ae_hatOf_restr m₀ hρ hp hpρ] with x hx
    rw [hid' (u : ℂ) (norm_ofReal_lt_of_mem hu hRσ1), hx, hvalg]
  have hT1 : ∀ s : ℝ, s ∈ Icc (0 : ℝ) 1 → ∀ᵐ x ∂S.nuFl,
      S.Wone (zeroClass d L N₁ m₁ k N ϱ) s x =
        ((if s ∈ Icc (0 : ℝ) 1 then s ^ 2 else 0 : ℝ) : ℂ) * ∑ y, (Ahat (s : ℂ)).H y
          ((S.blockSplit m₀ hp).restr x) := by
    intro s hs
    filter_upwards [key0 s hs, S.ae_ball hp] with x hx hχ
    have hT := S.Wone_zeroClass_eq_hat hC R0 hlt hbase hD hc7 (lt_of_lt_of_le one_lt_two hR) hsm
      hMX hdm hα hsmX hp hcψ hpc hδ₁ hs hχ
    rw [hx, ← hT]
    simp only [hs, ↓reduceIte]
    push_cast
    rfl
  have hT2 : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → ∀ᵐ x ∂S.nuFl,
      S.Wtwo (zeroClass d L N₁ m₁ k N ϱ) g t x =
        (S.β : ℂ) * (∑ s : CTorus d L N₁ m₁ (k + 1) × Fin N, (g s.1 s.2 / (S.β : ℂ)) *
          dirTermSrc (hatFun S.G' S.a₁ S.ν eps S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
            (onXi S.G' S.a₁ S.ν eps
              (fun D ψ' => svec (stepG d L N₁ m₁ k ϱ)
                (flFieldOne S.G' (stepG d L N₁ m₁ k ϱ) BG₂ κ S.a₁ S.ν D ψ') s.1 s.2)))
            (fun _ => (1 : ℂ)) (S.hatC x) (S.hatC x) (t : ℂ) (rawOf S.D')) := by
    intro t ht
    filter_upwards [S.ae_ball hp] with x hx
    exact (S.Wtwo_zeroClass_eq_hat hC R0 hlt hD hc7 hR hsm hRs hsmall hnum hnum' hMX hdm hα hsmX
      hp hcψ hpc hδ₁ g ht hx).symm
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
    A := segAct Ahat Ag hεR.le hE2 (fun s =>
      ((if s ∈ Icc (0 : ℝ) 1 then s ^ 2 else 0 : ℝ) : ℂ)) hcfun
    hκ0 := hκE
    hKc := by linarith
    hεpos := by rw [max_self]; positivity
    hκ' := hκ'
    hκ := hκa
    hε := by
      rw [max_self, hKc2]
      exact hDA
    hW := ?_ }, rfl, rfl, HEq.rfl, HEq.rfl, rfl, rfl, rfl, by simp, by simp [hKc2]⟩
  intro p hpS
  by_cases h0 : p.2 = 0
  · have hs : p.1 ∈ Icc (0 : ℝ) 1 := by
      rcases hpS with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact h1
      · rw [h1]; exact hlt1
    filter_upwards [hT1 p.1 hs] with x hx
    show S.Wone _ p.1 x + S.Wtwo _ g p.2 x = _
    rw [segAct_total_zero _ _ _ _ _ _ h0, h0, ← hx]
    have : S.Wtwo (zeroClass d L N₁ m₁ k N ϱ) g 0 x = 0 := S.Wtwo_zero _ g x
    rw [this, add_zero]
  · have ht : p.2 ∈ Icc (0 : ℝ) 1 := by
      rcases hpS with ⟨-, h2⟩ | ⟨-, h2⟩
      · exact absurd h2 h0
      · exact h2
    have h1 : p.1 = 1 := by
      rcases hpS with ⟨-, h2⟩ | ⟨h1, -⟩
      · exact absurd h2 h0
      · exact h1
    filter_upwards [hT1 1 hlt1, hT2 p.2 ht, key0 1 hlt1, key0 p.2 ht, keyg p.2 ht] with x a b c' d' e
    show S.Wone _ p.1 x + S.Wtwo _ g p.2 x = _
    rw [Complex.ofReal_one] at a c'
    rw [segAct_total_ne _ _ _ _ _ _ h0, h1, a, b, c', d', e]
    simp


/-- **The shared assembler.**  If both instances have the domain family `𝒴`, the label type of the
record is `{Y // Y ∈ 𝒴} ⊕ {Y // Y ∈ 𝒴}` and its labels are
`(thickLabels 𝒴 hdom).sum (thickLabels 𝒴 hdom)`, for the domain proof `hdom` of `𝒴`. -/
theorem stepActivityBound_zeroClass_source_of_directTerms_shared
    {𝒴 : Finset (Set (CTorus d L N₁ m₁ (k + 1)))} (hdom : ∀ Y ∈ 𝒴, IsDj m₀ (k + 1) Y)
    (h𝒴₀ : I₀.𝒴 = 𝒴) (h𝒴g : Ig.𝒴 = 𝒴) :
    ∃ B : StepActivityBound S (zeroClass d L N₁ m₁ k N ϱ) g,
      B.m₀ = m₀ ∧ B.Lb = ({Y // Y ∈ 𝒴} ⊕ {Y // Y ∈ 𝒴}) ∧
      HEq B.Lab ((thickLabels 𝒴 hdom).sum (thickLabels 𝒴 hdom)) ∧
      HEq B.BS (S.blockSplit m₀ hp) ∧ B.κ0 = κ0 ∧ B.κ' = κ' ∧
      B.κH = a ∧ B.εH = 2 * (Rσ * εU) ∧ B.Kc = 2 * Kc' := by
  obtain ⟨B, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ :=
    stepActivityBound_zeroClass_source_of_directTerms_exposed S hC hR₁ hr hcψ hMX hdm hα hsmX hδ₁
      hc7 hR hRs hsmall hnum hnum' hsm hRσ hc hD hN hp hpρ hεpos hκE hKc hκ' hκa hDA R0 hlt hRσ1
      g I₀ Ig hval₀ hvalg
  exact ⟨B, h1, h2.trans (by rw [h𝒴₀, h𝒴g]),
    h3.trans (directTerms_sharedLabels_heq hdom _ _ I₀.dom Ig.dom h𝒴₀ h𝒴g).2.2, h4, h5, h6, h7,
    h8, h9⟩

end Source

section Transport

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  {S : StepSetting d L N₁ m₁ k N ϱ} {C : StepClass d L N₁ m₁ k N ϱ}
  {g : Fld d L N₁ m₁ (k + 1) N}

/-- **The complex record of a real activity bound, with all fields exposed.**  The complex
activity bound copies the block scale, block split, labels, rates, prefactor and entropy constant
of the real one (`StepActivityBound.toC_of_ae`); the labels are equal by `rfl`. -/
theorem stepActivityBoundC_of_activityBound_exposed {pp : ℝ} (R : S.RayData pp) (hp1 : 0 < S.p₁)
    (hlt : S.p₁ < pp) (I : StepActivityBound S C g) :
    ∃ B : StepActivityBoundC S C g, B.m₀ = I.m₀ ∧ B.Lb = I.Lb ∧ HEq B.Lab I.Lab ∧
      HEq B.BS I.BS ∧ B.κ0 = I.κ0 ∧ B.κ' = I.κ' ∧ B.κH = I.κH ∧ B.εH = I.εH ∧
      B.Kc = I.Kc := by
  obtain ⟨h40, hr⟩ := S.margin_small R.hδ0 R.hβ hlt R.hB5 R.hp40 R.hrad
  exact ⟨I.toC_of_ae (S.ae_exponentsC_eq C R.ha₁ R.H R.hδ'0 R.hδ' R.hD'R R.hδ0 R.hfam R.hsm R.hχu
    R.hnorm R.hβ hp1 R.hB5 R.hK2 h40 hr g), rfl, rfl, HEq.rfl, HEq.rfl, rfl, rfl, rfl, rfl, rfl⟩

end Transport

end Balaban.Fluctuation

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep Filter Topology

open Classical in
/-- **The complex zero-class source activity at the shared tower `T`, with one label system for
every source of the strict `l^1` ball.**  After `T` choose `β₀, C_E, C_F`.  For every scale, torus,
mass, `β ≥ β₀`, cutoff `0 < p₁ ≤ A₁ (log β_k)^p` and `D : StepScaleData T …`, there are a domain
family `𝒴` and its proof `hdom` chosen before the source, such that every source `g` with
`∑ |g| < 1` has a real record `BR` and a complex record `BC` at the step `T.step …` with block scale
`1`, label type `{Y // Y ∈ 𝒴} ⊕ {Y // Y ∈ 𝒴}`, labels `(thickLabels 𝒴 hdom).sum (thickLabels 𝒴 hdom)`
and block split `S.blockSplit 1 hp` (`HEq`, as `Lab` depends on `Lb`), exponents `κ₀ = T.κ0`,
`κ' = T.κ'`, `κ_H = 2 T.κdec - 1`, entropy constant `2 (K₀(T.κ0) + 1)`, equal prefactors, and the
prefactor bound of `sourceActivityC_scale`. -/
theorem sourceActivityC_scale_fromTower {κmin : ℝ} (T : StepTower κmin) {A₁ : ℝ}
    (hA : 0 < A₁) (p : ℕ) :
    ∃ β₀ CE CF : ℝ, 2 ≤ β₀ ∧ 0 < CE ∧ 0 < CF ∧
    ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁], 3 ∣ N₁ → 5 < N₁ →
    ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 →
    ∀ β : ℝ, β₀ ≤ β → ∀ (p₁ : ℝ) (hp : 0 < p₁),
    p₁ ≤ pLog A₁ p (β * 3 ^ k) → StepScaleData T k hk N₁ ν β p₁ →
    ∃ 𝒴 : Finset (Set (CTorus 3 3 N₁ T.m₁ (k + 1))),
    ∃ hdom : ∀ Y ∈ 𝒴, IsDj 1 (k + 1) Y,
    ∀ g : Fld 3 3 N₁ T.m₁ (k + 1) 2, g ∈ l1Ball 3 3 N₁ T.m₁ (k + 1) 2 →
    ∃ BR : StepActivityBound (T.step k hk N₁ ν β p₁)
        (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) g,
    ∃ BC : StepActivityBoundC (T.step k hk N₁ ν β p₁)
        (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) g,
      BR.m₀ = 1 ∧ BC.m₀ = 1 ∧ BR.Lb = ({Y // Y ∈ 𝒴} ⊕ {Y // Y ∈ 𝒴}) ∧ BC.Lb = BR.Lb ∧
      HEq BR.Lab ((thickLabels 𝒴 hdom).sum (thickLabels 𝒴 hdom)) ∧ HEq BC.Lab BR.Lab ∧
      HEq BR.BS ((T.step k hk N₁ ν β p₁).blockSplit 1 hp) ∧ HEq BC.BS BR.BS ∧
      BR.κ0 = T.κ0 ∧ BC.κ0 = T.κ0 ∧ BR.κ' = T.κ' ∧ BC.κ' = T.κ' ∧
      BR.κH = 2 * T.κdec - 1 ∧ BC.κH = BR.κH ∧
      BR.Kc = 2 * (K0 3 3 T.κ0 + 1) ∧ BC.Kc = BR.Kc ∧ BR.εH = BC.εH ∧
      BR.εH ≤ CE * (Real.log (β * 3 ^ k)) ^ (3 * p) / Real.sqrt (β * 3 ^ k) +
        CF * (Real.log (β * 3 ^ k)) ^ p / Real.sqrt (β * 3 ^ k) := by
  classical
  have hent := aEnt_nonneg 3 3
  have hc1 := one_le_c1 3 3
  have ht0 := T.t_pos
  have hρ4 := T.rho_nonneg
  have hB0 := T.fam_nonneg
  have hκ0 := T.κ0_nonneg
  obtain ⟨Q, hQdef⟩ : ∃ Q : ℝ, Q = cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) := ⟨_, rfl⟩
  have hQ0 : 0 < Q := by rw [hQdef]; exact cK2'_pos' hB0
  obtain ⟨P, hPdef⟩ : ∃ P : ℝ, P = 3 * c1 3 3 * (((3 : ℕ) : ℝ) ^ (1 + T.m₁)) ^ 3 *
    (((3 : ℕ) : ℝ) ^ 3 * ((((2 : ℕ) : ℝ) / 2) * (2 * (1 + Q) ^ 2 +
      (((3 : ℕ) : ℝ) + 1 + rho4 3 3 2 T.BG T.κ) * Q ^ 2) * T.t ^ 2)) := ⟨_, rfl⟩
  have hP0 : 0 ≤ P := by
    rw [hPdef]; positivity
  have hK0 : 0 < Q * T.t := mul_pos hQ0 ht0
  obtain ⟨β₁, hexpβ₁, hA'⟩ := sourceAmp_scale (A₁ := A₁) (κ := T.κ) (t := T.t) hA p ht0
  obtain ⟨Kc'', hKc''⟩ : ∃ x : ℝ, x = K0 3 3 T.κ0 + 1 := ⟨_, rfl⟩
  have hKc''pos : 0 < Kc'' := by have := K0_pos 3 3 T.κ0; rw [hKc'']; linarith
  have hκdec0 : 0 ≤ T.κdec := by have := T.κdec_lower; linarith
  have hκ'0 : 0 ≤ T.κ' := by rw [T.κ'_eq]; linarith
  have hκa' : T.κ' + 3 * T.κ0 + c1 3 3 + 3 / 2 ≤ 2 * T.κdec - 1 := by
    rw [T.κ'_eq, T.κdec_eq]; linarith
  refine ⟨max (max 2 β₁) (daThreshold ((srcCE A₁ T.κ T.t P + srcCF A₁ T.κ T.t (Q * T.t)) / 4)
      (daT 3 3 4 (2 * Kc'') T.κdec T.κ0 T.κ') (3 * p)),
    srcCE A₁ T.κ T.t P, srcCF A₁ T.κ T.t (Q * T.t),
    le_trans (le_max_left _ _) (le_max_left _ _), srcCE_pos hA ht0 hP0,
    srcCF_pos hA ht0 hK0, ?_⟩
  intro k hk N₁ _ h3N hN ν hνpos hν β hβ p₁ hp0 hp₁ D
  have hν0 : 0 ≤ ν := hνpos.le
  have hβ₁ : β₁ ≤ β := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hβ)
  have hβd : daThreshold ((srcCE A₁ T.κ T.t P + srcCF A₁ T.κ T.t (Q * T.t)) / 4)
      (daT 3 3 4 (2 * Kc'') T.κdec T.κ0 T.κ') (3 * p) ≤ β := le_trans (le_max_right _ _) hβ
  have hβ2 : 2 ≤ β := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hβ)
  have hβ0 : 0 < β := by linarith
  have hβ1 : 1 ≤ β := by linarith
  have h3k : (1 : ℝ) ≤ 3 ^ k := one_le_pow₀ (by norm_num)
  have hbβ : β ≤ β * 3 ^ k := le_mul_of_one_le_right hβ0.le h3k
  have hb0 : 0 < β * 3 ^ k := by positivity
  have hexp : Real.exp 1 ≤ β * 3 ^ k := le_trans hexpβ₁ (hβ₁.trans hbβ)
  have hℓ : 1 ≤ Real.log (β * 3 ^ k) := (Real.le_log_iff_exp_le hb0).2 hexp
  have hamp := (hA' (β * 3 ^ k) (hβ₁.trans hbβ) p₁ hp0 hp₁).2 P (Q * T.t) 1 hP0 hK0.le one_pos.le
  obtain ⟨R0⟩ := D.ray
  have hr0 := D.r_pos
  have hcψ0 := D.cψ_pos
  have hHB := bgHyp_lv (k := k) T.m₁ hν0 hν
  have hC := D.core
  have hD := D.xi
  -- the physical amplitude on the slice `η = 1/β`
  obtain ⟨εU, hεU⟩ : ∃ εU : ℝ, εU = β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 1 T.BG T.BG₂ T.κ T.t
      (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (1 / β) := ⟨_, rfl⟩
  have hid := sourceEta_scaled_identity 3 3 2 T.m₁ k 1 1 T.BG T.BG₂ T.κ T.t
    (lvR T.κ T.t (β * 3 ^ k) p₁) 1 β hβ0.ne'
  rw [← hεU, ← hQdef] at hid
  have hpot : β * (3 * c1 3 3 * (((3 : ℕ) : ℝ) ^ (1 + T.m₁)) ^ 3 *
      ‖energyBdScaled 3 3 2 (compWeight 3 1) k (Q * T.t) T.t (rho4 3 3 2 T.BG T.κ)‖ /
        lvR T.κ T.t (β * 3 ^ k) p₁ ^ 3) ≤ β * 3 ^ k * (P / lvR T.κ T.t (β * 3 ^ k) p₁ ^ 3) := by
    have h := beta_mul_potentialAmp_le (N := 2) (T.step k hk N₁ ν β p₁)
      (by norm_num) le_rfl (compWeight_three_mem hk).2
      (le_trans (by norm_num) (compWeight_three_mem hk).1) hβ0.le hQ0.le ht0.le hρ4 hr0 (1 + T.m₁)
    rw [hatStepK_betaU, ← hPdef] at h
    exact h
  have hterm0 : 0 ≤ β * (3 * c1 3 3 * (((3 : ℕ) : ℝ) ^ (1 + T.m₁)) ^ 3 *
      ‖energyBdScaled 3 3 2 (compWeight 3 1) k (Q * T.t) T.t (rho4 3 3 2 T.BG T.κ)‖ /
        lvR T.κ T.t (β * 3 ^ k) p₁ ^ 3) := by
    have h3 : (0 : ℝ) ≤ 3 * c1 3 3 := by linarith
    positivity
  have hεle : εU ≤ P * (4 * A₁ / lvKappa T.κ T.t) ^ 3 * (Real.log (β * 3 ^ k)) ^ (3 * p) /
        Real.sqrt (β * 3 ^ k) +
      1 * (4 * A₁ * (Q * T.t) / lvKappa T.κ T.t) * (Real.log (β * 3 ^ k)) ^ p /
        Real.sqrt (β * 3 ^ k) := by
    rw [hid]
    linarith
  have hεpos : 0 < εU := by
    rw [hid]
    have : 0 < 1 * (Q * T.t) / lvR T.κ T.t (β * 3 ^ k) p₁ := div_pos (by linarith) hr0
    linarith
  have hε4 := sourceAmp_scale_four (A₁ := A₁) (κ := T.κ) (t := T.t) (P := P) (K := Q * T.t)
    (q := 1) p hb0 (by linarith) hεle
  have hDA0 := sourceAmp_doubled_hDA 3 3 (A₁ := A₁) (κ := T.κ) (t := T.t) (P := P)
    (K := Q * T.t) (q := 1) (b := β * 3 ^ k) (ε := εU) (Kc' := Kc'') p hA ht0 hP0 hK0.le le_rfl
    hℓ hb0 hKc''pos T.κdec T.κ0 T.κ' (hβd.trans hbβ) hεle
  have hN3 : 3 ^ 1 ∣ N₁ := by simpa using h3N
  -- the direct terms, selected once for the slice `η = 1/β`
  obtain ⟨val, 𝒴, Tt, hval, -, -, hI, hmem0, hmemg⟩ := sourceDirectTerms_scale_fromTower T k hk N₁
    h3N hN ν hνpos hν β hβ1 p₁ 1 one_pos le_rfl D (T.step k hk N₁ ν β p₁) rfl hp0
  obtain ⟨I₀, h𝒴₀, -⟩ := hI _ hmem0
  have hdom : ∀ Y ∈ 𝒴, IsDj 1 (k + 1) Y := fun Y hY => I₀.dom Y (h𝒴₀ ▸ hY)
  refine ⟨𝒴, hdom, ?_⟩
  intro g hg
  obtain ⟨Ig, h𝒴g, -⟩ := hI _ (hmemg g hg)
  obtain ⟨BR, hm, hLb, hLab, hBS, hk0, hk', hκH, hεH, hKc⟩ :=
    stepActivityBound_zeroClass_source_of_directTerms_shared (T.step k hk N₁ ν β p₁)
      (ρ := p₁) (κ0 := T.κ0) (κ' := T.κ') (Kc' := Kc'') (a := 2 * T.κdec - 1)
      hC (by norm_num) hr0 hcψ0.le T.large_block T.dom_margin T.coer_margin T.δc_small
      D.fl_radius T.c7_cap (R := 2) le_rfl T.t_cap T.bg0_cap T.cK2_cap T.cK2'_cap T.bg1_cap
      (by norm_num) D.ray_margin hD hN3 hp0 le_rfl (by rw [hεU] at hεpos; exact hεpos) T.κ0_ent hKc''.ge hκ'0 hκa'
      (by rw [hεU] at hDA0; exact hDA0) R0
      D.p_lt (by norm_num) g I₀ Ig
      (fun x u => by rw [hval]; simp)
      (fun x u => hval _ _ _ _) hdom h𝒴₀ h𝒴g
  obtain ⟨BC, hCm, hCLb, hCLab, hCBS, hCk0, hCk', hCκH, hCεH, hCKc⟩ :=
    stepActivityBoundC_of_activityBound_exposed R0 hp0 D.p_lt BR
  have hBε : BR.εH = 4 * εU := by
    rw [hεH, (fun E : ℝ => by ring : ∀ E : ℝ, 2 * (2 * E) = 4 * E)]
    exact congrArg _ hεU.symm
  refine ⟨BR, BC, hm, hCm.trans hm, hLb, hCLb, hLab, hCLab, hBS, hCBS, hk0, hCk0.trans hk0, hk',
    hCk'.trans hk', hκH, hCκH, by rw [hKc, hKc''], hCKc, hCεH.symm, ?_⟩
  rw [hBε]
  have := hε4
  rw [one_mul] at this
  exact this

end Balaban.Inhabited
