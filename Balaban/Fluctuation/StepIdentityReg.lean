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

end Reg

end StepSetting

end Balaban.Fluctuation
