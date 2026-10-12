/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.StepIdentity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Regularity of the interaction along the ray (FLUCTUATION.md §2.6, proof of Proposition 2.6)

The interpolation identity needs the exponents `W₁(s, ψ̂) = -β V^{(k)}(s ψ') + δℰ_k(s ψ')`,
`W₂(t, ψ̂) = δℱ_k(t ψ', g)` to be `C¹` in the parameter, bounded with their derivatives, on the
support of `ν_{p₁}`.  For the interaction `V^{(k)}` this is derived here: `V^{(k)}` is a polynomial in
the tangent `ψ'` and the field `φ' = φ_k(ψ) - φ_{k+1}`, and the background field is the restriction
of the analytic function of the raw data of Theorem 7.2.  The only input is the margin
`p₁ < p⁺` in the two conditions "`β` large" (P4 (2.40), the radius of Lemma 2.3 (d)), which makes
the data of the point `s ψ'` lie in the domain also for `|s| ≤ 1 + ε`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban.SmallField.Def6 Balaban.Background Balaban.Multiscale Balaban.Localization
  Balaban.SmallField Finset Matrix

section Smooth

variable {ι κ : Type*} [Fintype ι] [Fintype κ] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

@[fun_prop]
theorem contDiff_mulVec' {n : WithTop ℕ∞} (M : Matrix κ ι ℂ) {f : E → ι → ℂ}
    (hf : ContDiff ℝ n f) : ContDiff ℝ n (fun x => M *ᵥ f x) := by
  refine contDiff_pi.2 fun i => ?_
  simp only [Matrix.mulVec, dotProduct]
  refine ContDiff.sum fun j _ => ?_
  exact contDiff_const.mul ((contDiff_pi.1 hf) j)

end Smooth

section Interaction

variable {d L N₀ K N : ℕ} [NeZero N₀] [NeZero L] {ϱ ϱ' : ℝ}
  {G : GeneratingSet d L N₀ K ϱ} {G' : GeneratingSet d L N₀ K ϱ'}

/-- The interaction `V^{(k)}(ψ', φ')` is a polynomial in the tangent `ψ'` and the field `φ'`. -/
theorem contDiff_interactionV (h : Precedes G G') (a : ℕ → ℝ) (ν : ℝ) (α₁ : G'.Ω 1 → ℂ)
    (φ₁ : G'.Ω 1 × Fin N → ℂ) :
    ContDiff ℝ ⊤ (fun p : (Torus d (N₀ * L ^ K) → Fin N → ℂ) × (G.Ω 1 × Fin N → ℂ) =>
      interactionV h a ν α₁ φ₁ p.1 p.2) := by
  unfold interactionV alphaOne phiOne qStar pair
  fun_prop

end Interaction

section C1Ops

open MeasureTheory Set

variable {X : Type*} [MeasurableSpace X] {U₁ U₂ : Set ℝ} {W₁ W₁' W₂ W₂' : ℝ → X → ℂ}

/-- Restriction of a `C¹` family to a smaller open neighbourhood of `[0,1]`. -/
theorem IsC1Family.restrict (h : IsC1Family U₁ W₁ W₁') {U : Set ℝ} (hU : IsOpen U)
    (hsub : U ⊆ U₁) (hIcc : Icc (0 : ℝ) 1 ⊆ U) : IsC1Family U W₁ W₁' where
  isOpen := hU
  Icc_subset := hIcc
  measurable s hs := h.measurable s (hsub hs)
  measurable' s hs := h.measurable' s (hsub hs)
  hasDerivAt ω s hs := h.hasDerivAt ω s (hsub hs)
  continuousOn := h.continuousOn
  bound := by
    obtain ⟨M, hM⟩ := h.bound
    exact ⟨M, fun ω s hs => hM ω s (hsub hs)⟩

/-- The sum of two `C¹` families. -/
theorem IsC1Family.add' (h₁ : IsC1Family U₁ W₁ W₁') (h₂ : IsC1Family U₁ W₂ W₂') :
    IsC1Family U₁ (fun s ω => W₁ s ω + W₂ s ω) (fun s ω => W₁' s ω + W₂' s ω) where
  isOpen := h₁.isOpen
  Icc_subset := h₁.Icc_subset
  measurable s hs := (h₁.measurable s hs).add (h₂.measurable s hs)
  measurable' s hs := (h₁.measurable' s hs).add (h₂.measurable' s hs)
  hasDerivAt ω s hs := (h₁.hasDerivAt ω s hs).add (h₂.hasDerivAt ω s hs)
  continuousOn ω := (h₁.continuousOn ω).add (h₂.continuousOn ω)
  bound := by
    obtain ⟨M₁, hM₁⟩ := h₁.bound
    obtain ⟨M₂, hM₂⟩ := h₂.bound
    refine ⟨M₁ + M₂, fun ω s hs => ⟨?_, ?_⟩⟩
    · exact (norm_add_le _ _).trans (add_le_add (hM₁ ω s hs).1 (hM₂ ω s hs).1)
    · exact (norm_add_le _ _).trans (add_le_add (hM₁ ω s hs).2 (hM₂ ω s hs).2)

end C1Ops

namespace StepSetting

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ)

/-- The step datum with the radius `p₁` replaced by `pp`. -/
def withRadius (pp : ℝ) : StepSetting d L N₁ m₁ k N ϱ := { S with p₁ := pp }

/-- The raw data `(Ψ, h̃)` of a real field of the unit lattice (with the field `h₀`). -/
def rawU (ψ : S.E) : RawData d L (N₁ * L ^ m₁) (k + 1) N :=
  ((fun z i => ((liftU S.hG' ψ z i : ℝ) : ℂ)), (fun _ i => (S.h₀ i : ℂ)))

theorem dataU_raw (ψ : S.E) : ((S.dataU ψ).Ψ, (S.dataU ψ).h) = S.rawU ψ := by
  refine Prod.ext ?_ ?_
  · funext z i; exact S.dataU_Ψ ψ z i
  · funext z i; exact S.dataU_h ψ z i

theorem contDiff_rawU : ContDiff ℝ ⊤ S.rawU := by
  unfold rawU liftU
  refine ContDiff.prodMk (contDiff_pi.2 fun z => contDiff_pi.2 fun i => ?_) contDiff_const
  have h1 : ContDiff ℝ ⊤ (fun ψ : S.E => ψ (unitPt S.hG' z)) := contDiff_apply ℝ _ _
  have h2 : ContDiff ℝ ⊤ (fun v : Rn N => v i) := by fun_prop
  exact Complex.ofRealCLM.contDiff.comp (h2.comp h1)

end StepSetting

namespace StepSetting

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ)

section Reg

variable (ha₁ : 0 < S.a₁) (H : BgHyp d L (k + 1) ϱ S.a S.ν)
  {δ' : ℝ} (hδ'0 : 0 < δ') (hδ' : δ' ≤ thm73C3 d L N / 2) (hD'R : InDomainR S.G' S.ν δ' S.D')
  (hδ0 : 0 < S.δ)
  (hfam : ∀ x, 0 ≤ x → XData S.G' S.a S.a₁ S.ν x (bgMult S.G' S.a S.ν S.D') 0 (fun _ => 1))
  (hsm : S.δ ^ 2 * smallConstX d L 0 ≤ 1 / 4)
  (hχu : chiU S.G' S.a S.ν S.δ S.D' = 1)
  (hnorm : S.ν * ((L : ℝ) ^ k) ^ 2 * |∑ i, S.h₀ i ^ 2 - 1| < (1 * S.δ) ^ 2)
  (hβ : 0 < S.β) {pp : ℝ} (hpp : 0 < pp)
  {B₅ K₂ : ℝ} (hB5 : max 1 (Real.sqrt N * covSupConst d L N (S.a k)) ≤ B₅)
  (hK2 : max (max 1 (cK2 d L N)) (Real.sqrt N * cK2 d L N) ≤ K₂)
  (hp40 : pp / (S.betaU ^ (1 / 2 : ℝ) * S.δ) ≤ (3 * B₅ * K₂)⁻¹)
  (hrad : B₅ * S.betaU ^ (-(1 / 2 : ℝ)) * pp ≤ fluctRadius d L N)

include S ha₁ H hδ'0 hδ' hD'R hδ0 hfam hsm hχu hnorm hβ hpp hB5 hK2 hp40 hrad in
/-- **The data of the ray lie in the domain, with margin**: if `|s| ‖ψ̂‖ < p⁺` then the datum of
`ψ^{(k)} + s ψ'` is in the real domain. -/
theorem dataU_inDomainR_plus {q : ℝ × S.E} (hq : |q.1| * ‖q.2‖ < pp) :
    InUnionDomainR (stepG d L N₁ m₁ k ϱ) (bgC1 d L N) S.ν (S.dataU (S.psiAt q.1 q.2)) := by
  have hx : chiFl (S.withRadius pp).U N (S.withRadius pp).p₁ (q.1 • q.2) = 1 := by
    show chiFl S.U N pp (q.1 • q.2) = 1
    rw [chiFl_eq_one_iff hpp, norm_smul, Real.norm_eq_abs]
    exact hq
  have h := (S.withRadius pp).dataU_inDomainR ha₁ H hδ'0 hδ' hD'R hδ0 hfam hsm hχu hnorm hβ hpp
    hB5 hK2 hp40 hrad (q.1 • q.2) hx
  have e : (S.withRadius pp).psiAt 1 (q.1 • q.2) = S.psiAt q.1 q.2 := by
    show S.psiAt 1 (q.1 • q.2) = _
    rw [S.psiAt_smul, one_mul]
  rw [e] at h
  exact h

include S ha₁ H hδ'0 hδ' hD'R in
/-- The tangent `ψ' = D.Ψ - ψ^{(k)}` of the datum of the old spin `ψ` is the lift of `ψ - ψ^{(k)}`. -/
theorem tangent_dataU (ψ : S.E) :
    compTangent S.hG S.hG' (le_refl (k + 1)) S.a (bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D') S.D'
      (S.dataU ψ) = fun z i => ((liftU S.hG' ψ z i - liftU S.hG' S.psi0 z i : ℝ) : ℂ) := by
  have hd0 : 0 < d := by have := H.hd; omega
  obtain ⟨hDU', -⟩ := S.D'_domains H hδ'0 hδ' hD'R
  have hpsiReal := (criticalPoint_real ha₁ S.hG S.hG' (le_refl (k + 1)) H H S.D' hDU').1
  obtain ⟨-, -, hδ'c1, -⟩ := theta_consts hd0 hδ'0 hδ'
  have hDU1 : InUnionDomainR S.G' (bgC1 d L N) S.ν S.D' := ⟨δ', hδ'0, hδ'c1, hD'R⟩
  obtain ⟨hf, -⟩ := theorem72_real H hDU1
  funext z i
  unfold compTangent
  rw [hf]
  have hpr : S.psiKd.Ψ z i = (((S.psiKd.Ψ z i).re : ℝ) : ℂ) :=
    Complex.ext (by simp) (by simpa using (show (S.psiKd.Ψ z i).im = 0 from (hpsiReal z i).1))
  show (S.dataU ψ).Ψ z i - S.psiKd.Ψ z i = _
  rw [S.dataU_Ψ, hpr, S.liftU_psi0 z i]
  push_cast
  simp

/-- The polynomial `V^{(k)}(ψ', φ')` of the tangent and the field, with the data of `θ`. -/
noncomputable def Vpoly :
    (Torus d (N₁ * L ^ m₁ * L ^ (k + 1)) → Fin N → ℂ) ×
      ((stepG d L N₁ m₁ k ϱ).Ω 1 × Fin N → ℂ) → ℂ := fun p =>
  interactionV (S.hG.precedes S.hG' (le_refl (k + 1))) S.a S.ν
    (bgMultC S.G' S.a S.ν (bgC0 d L N) S.D') (bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D') p.1 p.2

theorem contDiff_Vpoly : ContDiff ℝ ⊤ S.Vpoly :=
  contDiff_interactionV (S.hG.precedes S.hG' (le_refl (k + 1))) S.a S.ν
    (bgMultC S.G' S.a S.ν (bgC0 d L N) S.D') (bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D')

/-- The tangent `ψ - ψ^{(k)}` as a complex field of the fine torus. -/
noncomputable def tangentOf (ψ : S.E) : Torus d (N₁ * L ^ m₁ * L ^ (k + 1)) → Fin N → ℂ :=
  fun z i => ((liftU S.hG' ψ z i - liftU S.hG' S.psi0 z i : ℝ) : ℂ)

theorem contDiff_tangentOf : ContDiff ℝ ⊤ S.tangentOf := by
  unfold tangentOf
  refine contDiff_pi.2 fun z => contDiff_pi.2 fun i => ?_
  have h1 : ContDiff ℝ ⊤ (fun ψ : S.E => ψ (unitPt S.hG' z) i) := by fun_prop
  exact Complex.ofRealCLM.contDiff.comp (h1.sub contDiff_const)

theorem contDiff_psiAt : ContDiff ℝ ⊤ (fun q : ℝ × S.E => S.psiAt q.1 q.2) := by
  unfold psiAt shiftU
  have hK : ContDiff ℝ ⊤ (fun x : S.E => S.K x) := (LinearMap.toContinuousLinearMap S.K).contDiff
  have h2 : ContDiff ℝ ⊤ (fun q : ℝ × S.E => (S.betaU ^ (-(1 / 2 : ℝ))) • S.K q.2) :=
    (hK.comp contDiff_snd).const_smul (S.betaU ^ (-(1 / 2 : ℝ)))
  exact contDiff_const.add (contDiff_fst.smul h2)

include S ha₁ H hδ'0 hδ' hD'R hδ0 hfam hsm hχu hnorm hβ hpp hB5 hK2 hp40 hrad in
/-- **The interaction is smooth along the ray**: `(s, ψ̂) ↦ V^{(k)}(ψ^{(k)} + s ψ')` is `C^∞` on
`{|s| ‖ψ̂‖ < p⁺}`. -/
theorem contDiffAt_Vjoint {q : ℝ × S.E} (hq : |q.1| * ‖q.2‖ < pp) :
    ContDiffAt ℝ ⊤ (fun q : ℝ × S.E => S.Vk (S.psiAt q.1 q.2)) q := by
  obtain ⟨F, hF, hFe⟩ := theorem72_analytic (G := stepG d L N₁ m₁ k ϱ) (a := S.a) (ν := S.ν) H
  have hpsi := S.contDiff_psiAt
  have hdom := S.dataU_inDomainR_plus ha₁ H hδ'0 hδ' hD'R hδ0 hfam hsm hχu hnorm hβ hpp hB5 hK2
    hp40 hrad hq
  have hdomC := S.inUnionDomainC_of_R' H hdom
  have hFat : AnalyticAt ℂ F (S.rawU (S.psiAt q.1 q.2)) :=
    hF _ ⟨S.dataU (S.psiAt q.1 q.2), hdomC, (S.dataU_raw _).symm⟩
  have hFc : ContDiffAt ℝ ⊤ F (S.rawU (S.psiAt q.1 q.2)) :=
    (hFat.contDiffAt (n := ⊤)).restrict_scalars ℝ
  have hraw : ContDiff ℝ ⊤ (fun q : ℝ × S.E => S.rawU (S.psiAt q.1 q.2)) :=
    S.contDiff_rawU.comp hpsi
  have hG1 : ContDiffAt ℝ ⊤ (fun q : ℝ × S.E => F (S.rawU (S.psiAt q.1 q.2))) q :=
    hFc.comp q hraw.contDiffAt
  have hφ : ContDiffAt ℝ ⊤ (fun q : ℝ × S.E => (F (S.rawU (S.psiAt q.1 q.2))).1 -
      (S.hG.precedes S.hG' (le_refl (k + 1))).restrictφ
        (bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D')) q :=
    (contDiff_fst.contDiffAt.comp q hG1).sub contDiffAt_const
  have hT : ContDiffAt ℝ ⊤ (fun q : ℝ × S.E => S.tangentOf (S.psiAt q.1 q.2)) q :=
    (S.contDiff_tangentOf.comp hpsi).contDiffAt
  have hmodel : ContDiffAt ℝ ⊤ (fun q : ℝ × S.E => S.Vpoly (S.tangentOf (S.psiAt q.1 q.2),
      (F (S.rawU (S.psiAt q.1 q.2))).1 -
      (S.hG.precedes S.hG' (le_refl (k + 1))).restrictφ
        (bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D'))) q :=
    S.contDiff_Vpoly.contDiffAt.comp q (hT.prodMk hφ)
  refine hmodel.congr_of_eventuallyEq ?_
  have hopen : IsOpen {q : ℝ × S.E | |q.1| * ‖q.2‖ < pp} :=
    isOpen_lt (by fun_prop) continuous_const
  filter_upwards [hopen.mem_nhds hq] with q' hq'
  have hdom' := S.dataU_inDomainR_plus ha₁ H hδ'0 hδ' hD'R hδ0 hfam hsm hχu hnorm hβ hpp hB5 hK2
    hp40 hrad hq'
  have hdomC' := S.inUnionDomainC_of_R' H hdom'
  have hFq := hFe (S.dataU (S.psiAt q'.1 q'.2)) hdomC'
  rw [S.dataU_raw] at hFq
  have ht := S.tangent_dataU ha₁ H hδ'0 hδ' hD'R (S.psiAt q'.1 q'.2)
  unfold Vk Vpoly
  rw [ht, hFq]
  rfl

/-- The joint function `(s, ψ̂) ↦ V^{(k)}(ψ^{(k)} + s ψ')`. -/
noncomputable def Vjoint (q : ℝ × S.E) : ℂ := S.Vk (S.psiAt q.1 q.2)

/-- The exponent `-β V^{(k)}` of `W₁`, truncated to the support `{χ_fl = 1}` of `ν_{p₁}`. -/
noncomputable def WVT (s : ℝ) (x : S.E) : ℂ :=
  open Classical in if chiFl S.U N S.p₁ x = 1 then -(S.β : ℂ) * S.Vjoint (s, x) else 0

/-- Its `s`-derivative. -/
noncomputable def dWVT (s : ℝ) (x : S.E) : ℂ :=
  open Classical in
  if chiFl S.U N S.p₁ x = 1 then -(S.β : ℂ) * (fderiv ℝ S.Vjoint (s, x)) (1, 0) else 0

theorem measurableSet_ball : MeasurableSet {x : S.E | chiFl S.U N S.p₁ x = 1} :=
  (measurable_chiFl S.p₁) (measurableSet_singleton 1)

include S ha₁ H hδ'0 hδ' hD'R hδ0 hfam hsm hχu hnorm hβ hpp hB5 hK2 hp40 hrad in
/-- **The interaction exponent is a `C¹` family on a neighbourhood of `[0,1]`, bounded with its
derivative, on the support of `ν_{p₁}`** (needs `p₁ < p⁺`). -/
theorem isC1Family_WVT (hp₁ : 0 < S.p₁) (hlt : S.p₁ < pp) :
    ∃ U : Set ℝ, IsC1Family U S.WVT S.dWVT := by
  classical
  set ε : ℝ := (pp / S.p₁ - 1) / 2 with hε
  have hε0 : 0 < ε := by
    have : 1 < pp / S.p₁ := by rw [lt_div_iff₀ hp₁]; linarith
    rw [hε]; linarith
  have hεp : (1 + ε) * S.p₁ < pp := by
    have h1 : (1 + ε) * S.p₁ = (S.p₁ + pp) / 2 := by
      rw [hε]; field_simp; ring
    rw [h1]; linarith
  have hΩ : ∀ s ∈ Set.Icc (-ε) (1 + ε), ∀ x : S.E, ‖x‖ ≤ S.p₁ → |s| * ‖x‖ < pp := by
    intro s hs x hx
    have hs' : |s| ≤ 1 + ε := abs_le.2 ⟨by linarith [hs.1], hs.2⟩
    calc |s| * ‖x‖ ≤ (1 + ε) * S.p₁ := mul_le_mul hs' hx (norm_nonneg _) (by linarith)
      _ < pp := hεp
  have hCD : ∀ s ∈ Set.Icc (-ε) (1 + ε), ∀ x : S.E, ‖x‖ ≤ S.p₁ →
      ContDiffAt ℝ ⊤ S.Vjoint (s, x) := fun s hs x hx =>
    S.contDiffAt_Vjoint ha₁ H hδ'0 hδ' hD'R hδ0 hfam hsm hχu hnorm hβ hpp hB5 hK2 hp40 hrad
      (q := (s, x)) (hΩ s hs x hx)
  have hball : ∀ x : S.E, chiFl S.U N S.p₁ x = 1 → ‖x‖ ≤ S.p₁ := fun x hx =>
    ((chiFl_eq_one_iff hp₁ x).1 hx).le
  have hIcc : ∀ s ∈ Set.Ioo (-ε) (1 + ε), s ∈ Set.Icc (-ε) (1 + ε) := fun s hs => ⟨hs.1.le, hs.2.le⟩
  -- continuity of the function and of its derivative at points of the ball
  have hcont : ∀ s ∈ Set.Icc (-ε) (1 + ε), ∀ x : S.E, ‖x‖ ≤ S.p₁ →
      ContinuousAt S.Vjoint (s, x) := fun s hs x hx => (hCD s hs x hx).continuousAt
  have hcontd : ∀ s ∈ Set.Icc (-ε) (1 + ε), ∀ x : S.E, ‖x‖ ≤ S.p₁ →
      ContinuousAt (fun q : ℝ × S.E => (fderiv ℝ S.Vjoint q) (1, 0)) (s, x) := by
    intro s hs x hx
    have h1 : ContDiffAt ℝ 0 (fderiv ℝ S.Vjoint) (s, x) :=
      (hCD s hs x hx).fderiv_right (m := 0) (by norm_num)
    have h2 : ContinuousAt (fderiv ℝ S.Vjoint) (s, x) := h1.continuousAt
    exact (ContinuousLinearMap.apply ℝ ℂ ((1 : ℝ), (0 : S.E))).continuous.continuousAt.comp h2
  have hslice : ∀ s ∈ Set.Icc (-ε) (1 + ε), ∀ x : S.E, ‖x‖ ≤ S.p₁ →
      ContinuousAt (fun x : S.E => S.Vjoint (s, x)) x := fun s hs x hx =>
    (hcont s hs x hx).comp (Continuous.prodMk_right s).continuousAt
  have hslice' : ∀ s ∈ Set.Icc (-ε) (1 + ε), ∀ x : S.E, ‖x‖ ≤ S.p₁ →
      ContinuousAt (fun x : S.E => (fderiv ℝ S.Vjoint (s, x)) (1, 0)) x := fun s hs x hx =>
    (hcontd s hs x hx).comp (Continuous.prodMk_right s).continuousAt
  refine ⟨Set.Ioo (-ε) (1 + ε), ?_⟩
  refine
    { isOpen := isOpen_Ioo
      Icc_subset := fun s hs => ⟨by linarith [hs.1], by linarith [hs.2]⟩
      measurable := ?_
      measurable' := ?_
      hasDerivAt := ?_
      continuousOn := ?_
      bound := ?_ }
  · intro s hs
    have hs' := hIcc s hs
    have hpw : S.WVT s = Set.piecewise {x : S.E | chiFl S.U N S.p₁ x = 1}
        (fun x => -(S.β : ℂ) * S.Vjoint (s, x)) 0 := by
      funext x
      by_cases hx : chiFl S.U N S.p₁ x = 1
      · simp [WVT, Set.piecewise, hx]
      · simp [WVT, Set.piecewise, hx]
    rw [hpw]
    refine ContinuousOn.measurable_piecewise (fun x hx => ?_) continuousOn_const
      S.measurableSet_ball
    exact (continuousAt_const.mul (hslice s hs' x (hball x hx))).continuousWithinAt
  · intro s hs
    have hs' := hIcc s hs
    have hpw : S.dWVT s = Set.piecewise {x : S.E | chiFl S.U N S.p₁ x = 1}
        (fun x => -(S.β : ℂ) * (fderiv ℝ S.Vjoint (s, x)) (1, 0)) 0 := by
      funext x
      by_cases hx : chiFl S.U N S.p₁ x = 1
      · simp [dWVT, Set.piecewise, hx]
      · simp [dWVT, Set.piecewise, hx]
    rw [hpw]
    refine ContinuousOn.measurable_piecewise (fun x hx => ?_) continuousOn_const
      S.measurableSet_ball
    exact (continuousAt_const.mul (hslice' s hs' x (hball x hx))).continuousWithinAt
  · intro x s hs
    have hs' := hIcc s hs
    by_cases hx : chiFl S.U N S.p₁ x = 1
    · have hfun : (fun r => S.WVT r x) = fun r => -(S.β : ℂ) * S.Vjoint (r, x) := by
        funext r; simp [WVT, hx]
      have hd : DifferentiableAt ℝ S.Vjoint (s, x) := (hCD s hs' x (hball x hx)).differentiableAt
        (by simp)
      have h1 : HasDerivAt (fun r : ℝ => S.Vjoint (r, x)) ((fderiv ℝ S.Vjoint (s, x)) (1, 0)) s := by
        have hp : HasDerivAt (fun r : ℝ => ((r, x) : ℝ × S.E)) ((1 : ℝ), (0 : S.E)) s :=
          (hasDerivAt_id s).prodMk (hasDerivAt_const s x)
        exact hd.hasFDerivAt.comp_hasDerivAt s hp
      rw [hfun]
      simp only [dWVT, hx, ↓reduceIte]
      exact h1.const_mul _
    · simp only [WVT, dWVT, hx, ↓reduceIte]
      exact hasDerivAt_const s 0
  · intro x
    by_cases hx : chiFl S.U N S.p₁ x = 1
    · have hfun : (fun s => S.dWVT s x) = fun s => -(S.β : ℂ) * (fderiv ℝ S.Vjoint (s, x)) (1, 0) := by
        funext s; simp [dWVT, hx]
      rw [hfun]
      refine fun s hs => ?_
      have hs' : s ∈ Set.Icc (-ε) (1 + ε) := ⟨by linarith [hs.1], by linarith [hs.2]⟩
      have := (hcontd s hs' x (hball x hx)).comp (f := fun s : ℝ => ((s, x) : ℝ × S.E))
        (continuous_id.prodMk continuous_const).continuousAt
      exact (continuousAt_const.mul this).continuousWithinAt
    · have : (fun s => S.dWVT s x) = fun _ => 0 := by
        funext s; simp [dWVT, hx]
      rw [this]
      exact continuousOn_const
  · have hKc : IsCompact (Set.Icc (-ε) (1 + ε) ×ˢ Metric.closedBall (0 : S.E) S.p₁) :=
      isCompact_Icc.prod (isCompact_closedBall _ _)
    have hKm : ∀ q ∈ Set.Icc (-ε) (1 + ε) ×ˢ Metric.closedBall (0 : S.E) S.p₁,
        q.1 ∈ Set.Icc (-ε) (1 + ε) ∧ ‖q.2‖ ≤ S.p₁ := fun q hq =>
      ⟨hq.1, by simpa using hq.2⟩
    obtain ⟨M₀, hM₀⟩ := hKc.exists_bound_of_continuousOn
      (f := S.Vjoint) (fun q hq => (hcont q.1 (hKm q hq).1 q.2 (hKm q hq).2).continuousWithinAt)
    obtain ⟨M₁, hM₁⟩ := hKc.exists_bound_of_continuousOn
      (f := fun q : ℝ × S.E => (fderiv ℝ S.Vjoint q) (1, 0))
      (fun q hq => (hcontd q.1 (hKm q hq).1 q.2 (hKm q hq).2).continuousWithinAt)
    refine ⟨‖(S.β : ℂ)‖ * (max M₀ 0 + max M₁ 0), fun x s hs => ?_⟩
    have hs' := hIcc s hs
    have hB : 0 ≤ ‖(S.β : ℂ)‖ * (max M₀ 0 + max M₁ 0) := by positivity
    by_cases hx : chiFl S.U N S.p₁ x = 1
    · have hq : (s, x) ∈ Set.Icc (-ε) (1 + ε) ×ˢ Metric.closedBall (0 : S.E) S.p₁ :=
        ⟨hs', by simpa using hball x hx⟩
      refine ⟨?_, ?_⟩
      · simp only [WVT, hx, ↓reduceIte, norm_mul, norm_neg]
        exact mul_le_mul_of_nonneg_left ((hM₀ _ hq).trans ((le_max_left _ _).trans
          (le_add_of_nonneg_right (le_max_right _ _)))) (norm_nonneg _)
      · simp only [dWVT, hx, ↓reduceIte, norm_mul, norm_neg]
        exact mul_le_mul_of_nonneg_left ((hM₁ _ hq).trans ((le_max_left _ _).trans
          (le_add_of_nonneg_left (le_max_right _ _)))) (norm_nonneg _)
    · simp only [WVT, dWVT, hx, ↓reduceIte, norm_zero]
      exact ⟨hB, hB⟩

end Reg

variable (C : StepClass d L N₁ m₁ k N ϱ)

/-- The class exponent `δℰ_k(s ψ')` of `W₁`, truncated to the support of `ν_{p₁}`. -/
noncomputable def dET (s : ℝ) (x : S.E) : ℂ :=
  open Classical in if chiFl S.U N S.p₁ x = 1 then S.dE C (S.psiAt s x) else 0

/-- **Regularity of the class terms along the ray** (the analyticity (H.2), (H.7) of `ℰ_k` and
`ℱ_k` on `Ξ^c`, and the inclusion of the composed data in it, along the path `s ↦ ψ^{(k)} + s ψ'`):
the exponents `δℰ_k(s ψ')` and `δℱ_k(t ψ', g)`, truncated to the support of `ν_{p₁}`, are `C¹`
families on an open neighbourhood of `[0,1]`, bounded with their derivatives.  This is the only
analytic input on the class; the interaction `V^{(k)}` and the background field are treated in
`isC1Family_WVT`. -/
structure ClassRegular (g : Fld d L N₁ m₁ (k + 1) N) : Prop where
  c1 : ∃ (U : Set ℝ) (E' F' : ℝ → S.E → ℂ),
    IsC1Family U (S.dET C) E' ∧ IsC1Family U (S.WtwoT C g) F'

theorem WoneT_eq_add (s : ℝ) (x : S.E) : S.WoneT C s x = S.WVT s x + S.dET C s x := by
  by_cases hx : chiFl S.U N S.p₁ x = 1
  · simp [WoneT, WVT, dET, Wone, Vjoint, hx]
  · simp [WoneT, WVT, dET, hx]

section Reg2

variable (ha₁ : 0 < S.a₁) (H : BgHyp d L (k + 1) ϱ S.a S.ν)
  {δ' : ℝ} (hδ'0 : 0 < δ') (hδ' : δ' ≤ thm73C3 d L N / 2) (hD'R : InDomainR S.G' S.ν δ' S.D')
  (hδ0 : 0 < S.δ)
  (hfam : ∀ x, 0 ≤ x → XData S.G' S.a S.a₁ S.ν x (bgMult S.G' S.a S.ν S.D') 0 (fun _ => 1))
  (hsm : S.δ ^ 2 * smallConstX d L 0 ≤ 1 / 4)
  (hχu : chiU S.G' S.a S.ν S.δ S.D' = 1)
  (hnorm : S.ν * ((L : ℝ) ^ k) ^ 2 * |∑ i, S.h₀ i ^ 2 - 1| < (1 * S.δ) ^ 2)
  (hβ : 0 < S.β) {pp : ℝ} (hpp : 0 < pp)
  {B₅ K₂ : ℝ} (hB5 : max 1 (Real.sqrt N * covSupConst d L N (S.a k)) ≤ B₅)
  (hK2 : max (max 1 (cK2 d L N)) (Real.sqrt N * cK2 d L N) ≤ K₂)
  (hp40 : pp / (S.betaU ^ (1 / 2 : ℝ) * S.δ) ≤ (3 * B₅ * K₂)⁻¹)
  (hrad : B₅ * S.betaU ^ (-(1 / 2 : ℝ)) * pp ≤ fluctRadius d L N)

include S C ha₁ H hδ'0 hδ' hD'R hδ0 hfam hsm hχu hnorm hβ hpp hB5 hK2 hp40 hrad in
/-- **The exponents are regular, given the regularity of the class terms**: the interaction part is
derived (`isC1Family_WVT`). -/
theorem stepRegular_of_class (hp₁ : 0 < S.p₁) (hlt : S.p₁ < pp) (g : Fld d L N₁ m₁ (k + 1) N)
    (hc : S.ClassRegular C g) : S.StepRegular C g := by
  obtain ⟨U₁, hV⟩ := S.isC1Family_WVT ha₁ H hδ'0 hδ' hD'R hδ0 hfam hsm hχu hnorm hβ hpp hB5 hK2
    hp40 hrad hp₁ hlt
  obtain ⟨U₂, E', F', hE, hF⟩ := hc.c1
  have hopen : IsOpen (U₁ ∩ U₂) := hV.isOpen.inter hE.isOpen
  have hIcc : Set.Icc (0 : ℝ) 1 ⊆ U₁ ∩ U₂ := fun s hs => ⟨hV.Icc_subset hs, hE.Icc_subset hs⟩
  have hV' := hV.restrict hopen Set.inter_subset_left hIcc
  have hE' := hE.restrict hopen Set.inter_subset_right hIcc
  have hF' := hF.restrict hopen Set.inter_subset_right hIcc
  refine ⟨⟨U₁ ∩ U₂, fun s x => S.dWVT s x + E' s x, F', ?_, hF'⟩⟩
  have : S.WoneT C = fun s x => S.WVT s x + S.dET C s x := by
    funext s x; exact S.WoneT_eq_add C s x
  rw [this]
  exact hV'.add' hE'

end Reg2

section Public

variable (ha₁ : 0 < S.a₁) (H : BgHyp d L (k + 1) ϱ S.a S.ν)
  {δ' : ℝ} (hδ'0 : 0 < δ') (hδ' : δ' ≤ thm73C3 d L N / 2) (hD'R : InDomainR S.G' S.ν δ' S.D')
  (hδ0 : 0 < S.δ)
  (hfam : ∀ x, 0 ≤ x → XData S.G' S.a S.a₁ S.ν x (bgMult S.G' S.a S.ν S.D') 0 (fun _ => 1))
  (hsm : S.δ ^ 2 * smallConstX d L 0 ≤ 1 / 4)
  (hχu : chiU S.G' S.a S.ν S.δ S.D' = 1)
  (hnorm : S.ν * ((L : ℝ) ^ k) ^ 2 * |∑ i, S.h₀ i ^ 2 - 1| < (1 * S.δ) ^ 2)
  (hβ : 0 < S.β) (hp₁ : 0 < S.p₁) {pp : ℝ} (hlt : S.p₁ < pp)
  {B₅ K₂ : ℝ} (hB5 : max 1 (Real.sqrt N * covSupConst d L N (S.a k)) ≤ B₅)
  (hK2 : max (max 1 (cK2 d L N)) (Real.sqrt N * cK2 d L N) ≤ K₂)
  (hp40 : pp / (S.betaU ^ (1 / 2 : ℝ) * S.δ) ≤ (3 * B₅ * K₂)⁻¹)
  (hrad : B₅ * S.betaU ^ (-(1 / 2 : ℝ)) * pp ≤ fluctRadius d L N)

include S hδ0 hβ hlt hB5 hp40 hrad in
theorem margin_small : S.p₁ / (S.betaU ^ (1 / 2 : ℝ) * S.δ) ≤ (3 * B₅ * K₂)⁻¹ ∧
    B₅ * S.betaU ^ (-(1 / 2 : ℝ)) * S.p₁ ≤ fluctRadius d L N := by
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hβU := betaU_pos' S hL hβ
  have hB : 0 < B₅ := lt_of_lt_of_le one_pos ((le_max_left _ _).trans hB5)
  have hsq : 0 < S.betaU ^ (1 / 2 : ℝ) * S.δ := by positivity
  refine ⟨?_, ?_⟩
  · refine le_trans ?_ hp40
    exact div_le_div_of_nonneg_right hlt.le hsq.le
  · refine le_trans ?_ hrad
    have : 0 ≤ B₅ * S.betaU ^ (-(1 / 2 : ℝ)) := by positivity
    exact mul_le_mul_of_nonneg_left hlt.le this

include S C ha₁ H hδ'0 hδ' hD'R hδ0 hfam hsm hχu hnorm hβ hp₁ hlt hB5 hK2 hp40 hrad in
/-- **Proposition 2.6 (whole lattice, `λ = ∞`, complete convention, complex data)** with the
class regularity `ClassRegular` as the analytic input and the nonvanishing of `Z_{s,0}, Z_{1,t}`
(cluster expansion).  The margin `p₁ < p⁺` in the two conditions "`β` large". -/
theorem prop26_complex_class (g : Fld d L N₁ m₁ (k + 1) N) (hc : S.ClassRegular C g)
    (hnv : S.StepNonvanishing C g) :
    S.Tstep C g = Complex.exp (-(S.β : ℂ) * (S.Anew : ℂ) +
      EcompAt C.m₀ C.Tm S.a S.ν (Nat.le_succ k) S.psiKd - (S.Eppp C : ℂ) * (S.nU : ℂ) +
      FcompAt C.m₀ C.Tm S.a S.ν (Nat.le_succ k) S.psiKd g + S.E0 C + S.F0 C g) := by
  have hpp : 0 < pp := hp₁.trans hlt
  obtain ⟨h40, hr⟩ := S.margin_small hδ0 hβ hlt hB5 hp40 hrad
  exact S.prop26_complex C ha₁ H hδ'0 hδ' hD'R hδ0 hfam hsm hχu hnorm hβ hp₁ hB5 hK2 h40 hr g
    (S.stepRegular_of_class C ha₁ H hδ'0 hδ' hD'R hδ0 hfam hsm hχu hnorm hβ hpp hB5 hK2 hp40 hrad
      hp₁ hlt g hc) hnv

include S C ha₁ H hδ'0 hδ' hD'R hδ0 hfam hsm hχu hnorm hβ hp₁ hlt hB5 hK2 hp40 hrad in
/-- **Proposition 2.6 for real data**: the class terms are real on real data (`RealClassTerms`) and
`C¹` along the ray (`ClassRegular`); then `Z_{s,t} > 0` and (2.6) holds. -/
theorem prop26_real_class (g : Fld d L N₁ m₁ (k + 1) N) (hrc : S.RealClassTerms C g)
    (hc : S.ClassRegular C g) :
    S.Tstep C g = Complex.exp (-(S.β : ℂ) * (S.Anew : ℂ) +
      EcompAt C.m₀ C.Tm S.a S.ν (Nat.le_succ k) S.psiKd - (S.Eppp C : ℂ) * (S.nU : ℂ) +
      FcompAt C.m₀ C.Tm S.a S.ν (Nat.le_succ k) S.psiKd g + S.E0 C + S.F0 C g) := by
  have hpp : 0 < pp := hp₁.trans hlt
  obtain ⟨h40, hr⟩ := S.margin_small hδ0 hβ hlt hB5 hp40 hrad
  exact S.prop26_real C ha₁ H hδ'0 hδ' hD'R hδ0 hfam hsm hχu hnorm hβ hp₁ hB5 hK2 h40 hr g hrc
    (S.stepRegular_of_class C ha₁ H hδ'0 hδ' hD'R hδ0 hfam hsm hχu hnorm hβ hpp hB5 hK2 hp40 hrad
      hp₁ hlt g hc)

include S C ha₁ H hδ'0 hδ' hD'R hδ0 hfam hsm hχu hnorm hβ hp₁ hlt hB5 hK2 hp40 hrad in
/-- **The nonvanishing holds for real data**: `StepNonvanishing` is implied by the reality of the
class terms and the regularity along the ray (`Z_{s,t} > 0`). -/
theorem stepNonvanishing_of_real (g : Fld d L N₁ m₁ (k + 1) N) (hrc : S.RealClassTerms C g)
    (hc : S.ClassRegular C g) : S.StepNonvanishing C g := by
  have hpp : 0 < pp := hp₁.trans hlt
  obtain ⟨h40, hr⟩ := S.margin_small hδ0 hβ hlt hB5 hp40 hrad
  have hreg := S.stepRegular_of_class C ha₁ H hδ'0 hδ' hD'R hδ0 hfam hsm hχu hnorm hβ hpp hB5 hK2
    hp40 hrad hp₁ hlt g hc
  have key : ∀ s t : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → t ∈ Set.Icc (0 : ℝ) 1 → S.Zst C g s t ≠ 0 := by
    intro s t hs ht h0
    have h := S.Zst_real_pos C ha₁ H hδ'0 hδ' hD'R hδ0 hfam hsm hχu hnorm hβ hp₁ hB5 hK2 h40 hr g
      hrc hreg hs ht
    rw [h0] at h
    simp at h
  exact ⟨fun s hs => key s 0 hs (Set.left_mem_Icc.2 zero_le_one),
    fun t ht => key 1 t (Set.right_mem_Icc.2 zero_le_one) ht⟩

end Public

end StepSetting

end Balaban.Fluctuation
