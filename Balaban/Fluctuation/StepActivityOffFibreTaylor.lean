/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.StepActivityOffFibreRay
public import Balaban.Fluctuation.StepTaylorComplex
import Mathlib.Tactic.Linarith

/-!
# The interaction along a free-datum critical ray

The incoming block field is arbitrary.  The critical spin and the perturbation are local
expressions, so the statement uses the existing interaction rather than a second step object.
-/

@[expose] public section

namespace Balaban.Fluctuation.StepSettingH

open Balaban Balaban.Background Balaban.Multiscale Balaban.Localization
  Balaban.SmallField.Def6 Finset Matrix Filter Topology Asymptotics Set

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  {S : StepSetting d L N₁ m₁ k N ϱ}

/-- The tangent to the free-datum critical ray is the lifted spin direction. -/
theorem compTangent_critical_ray (H : StepSettingH S) (v : S.EC) (z : ℂ) :
    let B := composeData (S.hG.precedes S.hG' (le_refl (k + 1))) S.a
      (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D') H.D'
    let ψ₀ : S.EC := fun q => B.Ψ (unitRep (G' := S.G') q.1) q.2
    compTangent S.hG S.hG' (le_refl (k + 1)) S.a
      (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D') H.D'
      (H.dataUCH (ψ₀ + z • v)) = z • liftC S.hG' v := by
  dsimp only
  rw [H.compTangent_dataUCH]
  have h : (fun q =>
      (composeData (S.hG.precedes S.hG' (le_refl (k + 1))) S.a
        (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D') H.D').Ψ
          (unitRep (G' := S.G') q.1) q.2) + z • v -
      (fun q =>
      (composeData (S.hG.precedes S.hG' (le_refl (k + 1))) S.a
        (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D') H.D').Ψ
          (unitRep (G' := S.G') q.1) q.2) = z • v := by abel
  rw [h, map_smul]

/-- A ray with zero background displacement and the predicted first derivative has no
quadratic interaction term. -/
theorem interaction_ray_order_core
    (P : ℝ → (stepG d L N₁ m₁ k ϱ).Ω 1 × Fin N → ℂ)
    (P₁ : (stepG d L N₁ m₁ k ϱ).Ω 1 × Fin N → ℂ)
    (A₁ : (stepG d L N₁ m₁ k ϱ).Ω 1 → ℂ)
    (M : Matrix ((stepG d L N₁ m₁ k ϱ).Ω 1 × Fin N)
      ((stepG d L N₁ m₁ k ϱ).Ω 1 × Fin N) ℂ)
    (hP : ∀ p, HasDerivAt (fun s : ℝ => P s p) (P₁ p) 0)
    (h0 : P 0 = 0) :
    (fun s : ℝ => (1 / 2 : ℂ) * (∑ w, ((s : ℂ) * A₁ w) *
      ∑ i, P s (w, i) * P s (w, i)) +
      (1 / 2 : ℂ) * pair (stepG d L N₁ m₁ k ϱ)
        (P s - (s : ℂ) • P₁) (M *ᵥ (P s - (s : ℂ) • P₁))) =o[𝓝 0]
      fun s : ℝ => s ^ 2 := by
  have hbig : ∀ p, (fun s : ℝ => P s p) =O[𝓝 0] fun s : ℝ => s := by
    intro p
    have := (hP p).hasFDerivAt.isBigO_sub
    simpa [h0] using this
  have hlit : ∀ p, (fun s : ℝ => P s p - (s : ℂ) * P₁ p) =o[𝓝 0]
      fun s : ℝ => s := by
    intro p
    have := hasDerivAt_iff_isLittleO.1 (hP p)
    simpa [h0, Complex.real_smul] using this
  have hs : (fun s : ℝ => (s : ℂ)) =O[𝓝 0] fun s : ℝ => s :=
    IsBigO.of_bound 1 (Eventually.of_forall fun s => by simp)
  have hcube : (fun s : ℝ => s * (s * s)) =o[𝓝 0] fun s : ℝ => s ^ 2 := by
    refine (isLittleO_pow_pow (𝕜 := ℝ) (show 2 < 3 by norm_num)).congr_left (fun s => ?_)
    ring
  have hsq : (fun s : ℝ => s * s) = fun s : ℝ => s ^ 2 := funext fun s => by ring
  have hT1 : (fun s : ℝ => ∑ w, ((s : ℂ) * A₁ w) *
      ∑ i, P s (w, i) * P s (w, i)) =o[𝓝 0] fun s : ℝ => s ^ 2 := by
    refine isLittleO_sum_fn _ fun w _ => ?_
    have e1 : (fun s : ℝ => (s : ℂ) * A₁ w) =O[𝓝 0] fun s : ℝ => s := by
      have := hs.const_mul_left (A₁ w)
      simpa [mul_comm] using this
    have e2 : (fun s : ℝ => ∑ i, P s (w, i) * P s (w, i)) =O[𝓝 0]
        fun s : ℝ => s * s :=
      isBigO_sum_fn _ fun i _ => (hbig (w, i)).mul (hbig (w, i))
    exact (e1.mul e2).trans_isLittleO hcube
  have hT2 : (fun s : ℝ => pair (stepG d L N₁ m₁ k ϱ)
      (P s - (s : ℂ) • P₁) (M *ᵥ (P s - (s : ℂ) • P₁))) =o[𝓝 0]
        fun s : ℝ => s ^ 2 := by
    unfold pair
    refine isLittleO_sum_fn _ fun p _ => ?_
    have e1 : (fun s : ℝ => (P s - (s : ℂ) • P₁) p) =o[𝓝 0]
        fun s : ℝ => s := by
      simpa [Complex.real_smul] using hlit p
    have e2 : (fun s : ℝ => (M *ᵥ (P s - (s : ℂ) • P₁)) p) =o[𝓝 0]
        fun s : ℝ => s := by
      simp only [Matrix.mulVec, dotProduct]
      refine isLittleO_sum_fn _ fun q _ => ?_
      have := (hlit q).const_mul_left (M p q)
      simpa [Complex.real_smul] using this
    have := e1.mul e2
    rwa [hsq] at this
  exact (hT1.const_mul_left (1 / 2 : ℂ)).add (hT2.const_mul_left (1 / 2 : ℂ))

/-- The interaction on the free-datum ray is negligible compared with the quadratic term.
The derivative of the lower background is supplied by the background response theorem. -/
theorem interaction_ray_isLittleO (H : StepSettingH S) (ha₁ : 0 < S.a₁)
    (HB : BgHyp d L (k + 1) ϱ S.a S.ν)
    (hD2 : InUnionDomainC S.G' (bgC0 d L N) (thm73C2 d L N) S.ν H.D')
    (v : S.EC) :
    let B := composeData (S.hG.precedes S.hG' (le_refl (k + 1))) S.a
      (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D') H.D'
    let ψ₀ : S.EC := fun q => B.Ψ (unitRep (G' := S.G') q.1) q.2
    (fun s : ℝ => interactionV (S.hG.precedes S.hG' (le_refl (k + 1))) S.a S.ν
      (bgMultC S.G' S.a S.ν (bgC0 d L N) H.D')
      (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D')
      ((s : ℂ) • liftC S.hG' v)
      (bgFieldC (stepG d L N₁ m₁ k ϱ) S.a S.ν (bgC0 d L N)
        (H.dataUCH (ψ₀ + (s : ℂ) • v)) -
        (S.hG.precedes S.hG' (le_refl (k + 1))).restrictφ
          (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D'))) =o[𝓝 0]
      fun s : ℝ => s ^ 2 := by
  dsimp only
  let B := composeData (S.hG.precedes S.hG' (le_refl (k + 1))) S.a
    (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D') H.D'
  let ψ₀ : S.EC := fun q => B.Ψ (unitRep (G' := S.G') q.1) q.2
  let P : ℝ → (stepG d L N₁ m₁ k ϱ).Ω 1 × Fin N → ℂ := fun s =>
    bgFieldC (stepG d L N₁ m₁ k ϱ) S.a S.ν (bgC0 d L N)
      (H.dataUCH (ψ₀ + (s : ℂ) • v)) -
      (S.hG.precedes S.hG' (le_refl (k + 1))).restrictφ
        (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D')
  let P₁ := phiOne (S.hG.precedes S.hG' (le_refl (k + 1))) S.a S.ν
    (bgMultC S.G' S.a S.ν (bgC0 d L N) H.D')
    (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D')
    (qStar (stepG d L N₁ m₁ k ϱ) S.a (liftC S.hG' v))
  let A₁ := alphaOne (S.hG.precedes S.hG' (le_refl (k + 1))) S.a S.ν
    (bgMultC S.G' S.a S.ν (bgC0 d L N) H.D')
    (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D')
    (qStar (stepG d L N₁ m₁ k ϱ) S.a (liftC S.hG' v))
  let M := liftOp N (opHk (S.hG.precedes S.hG' (le_refl (k + 1))) S.a S.ν
    (bgMultC S.G' S.a S.ν (bgC0 d L N) H.D'))
  have hP : ∀ p, HasDerivAt (fun s : ℝ => P s p) (P₁ p) 0 := by
    intro p
    have hcomplex : HasDerivAt (fun z : ℂ =>
        bgFieldC (stepG d L N₁ m₁ k ϱ) S.a S.ν (bgC0 d L N)
          (H.dataUCH (ψ₀ + z • v)) -
          (S.hG.precedes S.hG' (le_refl (k + 1))).restrictφ
            (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D')) P₁ (((0 : ℝ) : ℂ)) := by
      rw [Complex.ofReal_zero]
      exact H.hasDerivAt_bgC_ray ha₁ HB hD2 v
    have hh : HasDerivAt (fun r : ℝ => (r : ℂ)) (1 : ℂ) (0 : ℝ) :=
      (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).congr_deriv (by simp)
    have h := hcomplex.scomp (0 : ℝ) hh
    rw [one_smul] at h
    exact hasDerivAt_pi.1 h p
  have h0 : P 0 = 0 := by
    obtain ⟨hF, -⟩ := H.lower_bg_psi0C ha₁ HB
      (hD2.mono (thm73C2_le_thm73C1 d L N))
    change _ = _ at hF
    rw [← H.dataUCH_psi0C] at hF
    dsimp [P]
    rw [zero_smul, add_zero, hF]
    exact sub_self _
  have hsum := interaction_ray_order_core P P₁ A₁ M hP h0
  refine hsum.congr_left (fun s => ?_)
  unfold interactionV
  have hq : qStar (stepG d L N₁ m₁ k ϱ) S.a ((s : ℂ) • liftC S.hG' v) =
      (s : ℂ) • qStar (stepG d L N₁ m₁ k ϱ) S.a (liftC S.hG' v) := by
    funext p
    simp only [qStar, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hq]
  simp only [alphaOne_smul, phiOne_smul]
  rfl

/-- The free-datum interaction has a holomorphic representative at every point of its
small-solution ray domain. -/
theorem exists_analyticAt_interaction_ray (H : StepSettingH S) (ha₁ : 0 < S.a₁)
    (HB : BgHyp d L (k + 1) ϱ S.a S.ν)
    (hD2 : InUnionDomainC S.G' (bgC0 d L N) (thm73C2 d L N) S.ν H.D')
    (v : S.EC) {z₀ : ℂ}
    (hz₀ : InUnionDomainC (stepG d L N₁ m₁ k ϱ) (bgC0 d L N) (bgC1 d L N) S.ν
      (H.dataUCH ((fun q =>
        (composeData (S.hG.precedes S.hG' (le_refl (k + 1))) S.a
          (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D') H.D').Ψ
            (unitRep (G' := S.G') q.1) q.2) + z₀ • v))) :
    let B := composeData (S.hG.precedes S.hG' (le_refl (k + 1))) S.a
      (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D') H.D'
    let ψ₀ : S.EC := fun q => B.Ψ (unitRep (G' := S.G') q.1) q.2
    ∃ Φ : ℂ → ℂ, AnalyticAt ℂ Φ z₀ ∧ ∀ z : ℂ,
      InUnionDomainC (stepG d L N₁ m₁ k ϱ) (bgC0 d L N) (bgC1 d L N) S.ν
        (H.dataUCH (ψ₀ + z • v)) →
      interactionV (S.hG.precedes S.hG' (le_refl (k + 1))) S.a S.ν
        (bgMultC S.G' S.a S.ν (bgC0 d L N) H.D')
        (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D')
        (z • liftC S.hG' v)
        (bgFieldC (stepG d L N₁ m₁ k ϱ) S.a S.ν (bgC0 d L N)
          (H.dataUCH (ψ₀ + z • v)) -
          (S.hG.precedes S.hG' (le_refl (k + 1))).restrictφ
            (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D')) = Φ z := by
  dsimp only
  let B := composeData (S.hG.precedes S.hG' (le_refl (k + 1))) S.a
    (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D') H.D'
  let ψ₀ : S.EC := fun q => B.Ψ (unitRep (G' := S.G') q.1) q.2
  let R : BgData (stepG d L N₁ m₁ k ϱ) N :=
    BgData.clip (stepG d L N₁ m₁ k ϱ) (liftC S.hG' v) (fun _ _ => 0)
      (isLayerConstant_liftC S.hG S.hG' v)
      (by intro n _hn1 _hnk x _hx x' _hx'; rfl)
  obtain ⟨F, hF, hFe⟩ := theorem72_analytic (G := stepG d L N₁ m₁ k ϱ)
    (a := S.a) (ν := S.ν) HB
  let raw : ℂ → RawData d L (N₁ * L ^ m₁) (k + 1) N := fun z =>
    ((H.dataUCH ψ₀).Ψ + z • R.Ψ, (H.dataUCH ψ₀).h + z • R.h)
  have hraw : ∀ z, raw z = rawOf (H.dataUCH (ψ₀ + z • v)) := by
    intro z
    rw [H.dataUCH_add_smul]
    rfl
  have hrawan : AnalyticAt ℂ raw z₀ :=
    AnalyticAt.prod (analyticAt_const.add (analyticAt_id.smul analyticAt_const))
      (analyticAt_const.add (analyticAt_id.smul analyticAt_const))
  have hFat : AnalyticAt ℂ F (raw z₀) := hF _ ⟨_, hz₀, hraw z₀⟩
  have hFraw : AnalyticAt ℂ (fun z => F (raw z)) z₀ := hFat.comp hrawan
  obtain ⟨δs, Φ, St, hΦ⟩ := base_standing ha₁ S.hG S.hG' (le_refl (k + 1)) HB HB H.D' hD2
  have hΦ' : restrictField (stepG d L N₁ m₁ k ϱ) Φ =
      fieldBase (S.hG.precedes S.hG' (le_refl (k + 1)))
        (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D') :=
    funext fun x => funext fun i => hΦ x i
  refine ⟨fun z => interactionV (S.hG.precedes S.hG' (le_refl (k + 1))) S.a S.ν
    (bgMultC S.G' S.a S.ν (bgC0 d L N) H.D')
    (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D')
    (z • liftC S.hG' v)
    ((F (raw z)).1 - (S.hG.precedes S.hG' (le_refl (k + 1))).restrictφ
      (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D')), ?_, ?_⟩
  · refine analyticAt_interactionV (S.hG.precedes S.hG' (le_refl (k + 1))) S.a S.ν
      (αF := fun _ => bgMultC S.G' S.a S.ν (bgC0 d L N) H.D')
      (φF := fun _ => bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D')
      (ψF := fun z => z • liftC S.hG' v)
      (φ'F := fun z => (F (raw z)).1 - (S.hG.precedes S.hG' (le_refl (k + 1))).restrictφ
        (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D'))
      (fun y => analyticAt_const) (fun r => analyticAt_const) (fun y i => ?_) (fun r => ?_) ?_ ?_
    · simp only [Pi.smul_apply, smul_eq_mul]
      exact analyticAt_id.mul analyticAt_const
    · exact (analyticAt_pi_iff.1 (analyticAt_fst.comp hFraw) r).sub analyticAt_const
    · exact dirichletOperator_isUnit (stepG d L N₁ m₁ k ϱ) St.pos St.mass St.weights _ St.alpha
    · show IsUnit (constraintForm (opHk (S.hG.precedes S.hG' (le_refl (k + 1))) S.a S.ν
        (bgMultC S.G' S.a S.ν (bgC0 d L N) H.D'))⁻¹
        (fieldBase (S.hG.precedes S.hG' (le_refl (k + 1)))
          (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D')))
      rw [← hΦ']
      exact constraintForm_isUnit St
  · intro z hz
    dsimp only
    rw [hraw z]
    have heq : (F (rawOf (H.dataUCH (ψ₀ + z • v)))).1 =
        bgFieldC (stepG d L N₁ m₁ k ϱ) S.a S.ν (bgC0 d L N)
          (H.dataUCH (ψ₀ + z • v)) := by
      exact congrArg Prod.fst (hFe (H.dataUCH (ψ₀ + z • v)) hz)
    rw [heq]

/-- Smoothness of the free-datum interaction on the real ray. -/
theorem contDiffAt_interaction_ray (H : StepSettingH S) (ha₁ : 0 < S.a₁)
    (HB : BgHyp d L (k + 1) ϱ S.a S.ν)
    (hD2 : InUnionDomainC S.G' (bgC0 d L N) (thm73C2 d L N) S.ν H.D')
    (v : S.EC) {t : ℝ}
    (hray : ∀ᶠ s : ℝ in 𝓝 t,
      InUnionDomainC (stepG d L N₁ m₁ k ϱ) (bgC0 d L N) (bgC1 d L N) S.ν
        (H.dataUCH ((fun q =>
          (composeData (S.hG.precedes S.hG' (le_refl (k + 1))) S.a
            (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D') H.D').Ψ
              (unitRep (G' := S.G') q.1) q.2) + (s : ℂ) • v))) :
    let B := composeData (S.hG.precedes S.hG' (le_refl (k + 1))) S.a
      (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D') H.D'
    let ψ₀ : S.EC := fun q => B.Ψ (unitRep (G' := S.G') q.1) q.2
    ContDiffAt ℝ ⊤ (fun s : ℝ =>
      interactionV (S.hG.precedes S.hG' (le_refl (k + 1))) S.a S.ν
        (bgMultC S.G' S.a S.ν (bgC0 d L N) H.D')
        (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D')
        ((s : ℂ) • liftC S.hG' v)
        (bgFieldC (stepG d L N₁ m₁ k ϱ) S.a S.ν (bgC0 d L N)
          (H.dataUCH (ψ₀ + (s : ℂ) • v)) -
          (S.hG.precedes S.hG' (le_refl (k + 1))).restrictφ
            (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D'))) t := by
  dsimp only
  obtain ⟨Φ, hΦ, hΦe⟩ := H.exists_analyticAt_interaction_ray ha₁ HB hD2 v
    (z₀ := (t : ℂ)) hray.self_of_nhds
  have h1 : ContDiffAt ℝ ⊤ (fun s : ℝ => Φ (s : ℂ)) t :=
    ((hΦ.contDiffAt (n := ⊤)).restrict_scalars ℝ).comp t Complex.ofRealCLM.contDiff.contDiffAt
  refine h1.congr_of_eventuallyEq ?_
  filter_upwards [hray] with s hs
  exact hΦe (s : ℂ) hs

/-- The free-datum interaction has vanishing value and first two real derivatives at the
critical spin. -/
theorem interaction_ray_vanish (H : StepSettingH S) (ha₁ : 0 < S.a₁)
    (HB : BgHyp d L (k + 1) ϱ S.a S.ν)
    (hD2 : InUnionDomainC S.G' (bgC0 d L N) (thm73C2 d L N) S.ν H.D')
    (v : S.EC)
    (hray0 : ∀ᶠ s : ℝ in 𝓝 0,
      InUnionDomainC (stepG d L N₁ m₁ k ϱ) (bgC0 d L N) (bgC1 d L N) S.ν
        (H.dataUCH ((fun q =>
          (composeData (S.hG.precedes S.hG' (le_refl (k + 1))) S.a
            (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D') H.D').Ψ
              (unitRep (G' := S.G') q.1) q.2) + (s : ℂ) • v))) :
    let B := composeData (S.hG.precedes S.hG' (le_refl (k + 1))) S.a
      (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D') H.D'
    let ψ₀ : S.EC := fun q => B.Ψ (unitRep (G' := S.G') q.1) q.2
    let f : ℝ → ℂ := fun s => interactionV
      (S.hG.precedes S.hG' (le_refl (k + 1))) S.a S.ν
      (bgMultC S.G' S.a S.ν (bgC0 d L N) H.D')
      (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D')
      ((s : ℂ) • liftC S.hG' v)
      (bgFieldC (stepG d L N₁ m₁ k ϱ) S.a S.ν (bgC0 d L N)
        (H.dataUCH (ψ₀ + (s : ℂ) • v)) -
        (S.hG.precedes S.hG' (le_refl (k + 1))).restrictφ
          (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D'))
    f 0 = 0 ∧ deriv f 0 = 0 ∧ deriv (deriv f) 0 = 0 := by
  dsimp only
  exact derivs_zero_of_isLittleO_sq
    ((H.contDiffAt_interaction_ray ha₁ HB hD2 v hray0).of_le (by exact_mod_cast le_top))
    (H.interaction_ray_isLittleO ha₁ HB hD2 v)

/-- The free-datum interaction equals its cubic Taylor integral along the real ray. -/
theorem interaction_ray_taylor (H : StepSettingH S) (ha₁ : 0 < S.a₁)
    (HB : BgHyp d L (k + 1) ϱ S.a S.ν)
    (hD2 : InUnionDomainC S.G' (bgC0 d L N) (thm73C2 d L N) S.ν H.D')
    (v : S.EC)
    (hray : ∀ t ∈ Icc (0 : ℝ) 1, ∀ᶠ s : ℝ in 𝓝 t,
      InUnionDomainC (stepG d L N₁ m₁ k ϱ) (bgC0 d L N) (bgC1 d L N) S.ν
        (H.dataUCH ((fun q =>
          (composeData (S.hG.precedes S.hG' (le_refl (k + 1))) S.a
            (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D') H.D').Ψ
              (unitRep (G' := S.G') q.1) q.2) + (s : ℂ) • v)))
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    let B := composeData (S.hG.precedes S.hG' (le_refl (k + 1))) S.a
      (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D') H.D'
    let ψ₀ : S.EC := fun q => B.Ψ (unitRep (G' := S.G') q.1) q.2
    let f : ℝ → ℂ := fun r => interactionV
      (S.hG.precedes S.hG' (le_refl (k + 1))) S.a S.ν
      (bgMultC S.G' S.a S.ν (bgC0 d L N) H.D')
      (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D')
      ((r : ℂ) • liftC S.hG' v)
      (bgFieldC (stepG d L N₁ m₁ k ϱ) S.a S.ν (bgC0 d L N)
        (H.dataUCH (ψ₀ + (r : ℂ) • v)) -
        (S.hG.precedes S.hG' (le_refl (k + 1))).restrictφ
          (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D'))
    f s = ∫ u in (0 : ℝ)..1,
      taylorWeight (u : ℂ) * ((s : ℂ) ^ 3 * (iteratedDeriv 3 f (u * s))) := by
  let B := composeData (S.hG.precedes S.hG' (le_refl (k + 1))) S.a
    (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D') H.D'
  let ψ₀ : S.EC := fun q => B.Ψ (unitRep (G' := S.G') q.1) q.2
  let f : ℝ → ℂ := fun r => interactionV
    (S.hG.precedes S.hG' (le_refl (k + 1))) S.a S.ν
    (bgMultC S.G' S.a S.ν (bgC0 d L N) H.D')
    (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D')
    ((r : ℂ) • liftC S.hG' v)
    (bgFieldC (stepG d L N₁ m₁ k ϱ) S.a S.ν (bgC0 d L N)
      (H.dataUCH (ψ₀ + (r : ℂ) • v)) -
      (S.hG.precedes S.hG' (le_refl (k + 1))).restrictφ
        (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D'))
  have hvan : f 0 = 0 ∧ deriv f 0 = 0 ∧ deriv (deriv f) 0 = 0 :=
    H.interaction_ray_vanish ha₁ HB hD2 v (hray 0 ⟨le_rfl, zero_le_one⟩)
  obtain ⟨h0, h1, h2⟩ := hvan
  have hcont : ∀ t ∈ Icc (0 : ℝ) s, ContDiffAt ℝ 3 f t := by
    intro t ht
    exact (H.contDiffAt_interaction_ray ha₁ HB hD2 v
      (hray t ⟨ht.1, ht.2.trans hs.2⟩)).of_le (by exact_mod_cast le_top)
  have key := taylor3_integral (f := f) hs.1 hcont h0 h1 h2
  change f s = ∫ u in (0 : ℝ)..1,
    taylorWeight (u : ℂ) * ((s : ℂ) ^ 3 * iteratedDeriv 3 f (u * s))
  rw [key]
  refine intervalIntegral.integral_congr fun u _ => ?_
  simp only [taylorWeight]
  push_cast
  ring

end Balaban.Fluctuation.StepSettingH

namespace Balaban.Fluctuation.StepSetting

open Balaban Balaban.Background Balaban.Multiscale Balaban.Localization
  Balaban.SmallField.Def6 Matrix

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  {S : StepSetting d L N₁ m₁ k N ϱ}

/-- The physical hat shift is complex linear in the hat variable. -/
theorem hatField_smul (M : Matrix (S.U × Fin N) (S.U × Fin N) ℂ)
    (x : S.EC) (z : ℂ) : S.hatField M (z • x) = z • S.hatField M x := by
  unfold StepSetting.hatField
  rw [Matrix.mulVec_smul, smul_comm]

end Balaban.Fluctuation.StepSetting

namespace Balaban.Fluctuation.StepSettingH

open Balaban Balaban.Background Balaban.Multiscale Balaban.Localization
  Balaban.SmallField.Def6 Matrix

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ eps : ℝ}
  {S : StepSetting d L N₁ m₁ k N ϱ}

/-- The physical hat interaction at an arbitrary incoming field is the old interaction
along the free-datum critical ray. -/
theorem interaction_hat_ray (H : StepSettingH S)
    (hX : XiCData S.G' S.a S.ν (k + 1) 1 eps H.D') (x : S.E) (r : ℝ) :
    let B := composeData (S.hG.precedes S.hG' (le_refl (k + 1))) S.a
      (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D') H.D'
    let ψ₀ : S.EC := fun q => B.Ψ (unitRep (G' := S.G') q.1) q.2
    let v := S.hatField (hatCovSqrt S.G' S.a₁ S.ν H.D') (yhat x)
    hatFun S.G' S.a₁ S.ν eps S.hG'
      ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
      (interactionOne S.hG S.hG' (le_refl (k + 1)) S.a₁ S.ν eps)
      (rawOf H.D', (r : ℂ) • yhat x) =
    interactionV (S.hG.precedes S.hG' (le_refl (k + 1))) S.a S.ν
      (bgMultC S.G' S.a S.ν (bgC0 d L N) H.D')
      (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D')
      ((r : ℂ) • liftC S.hG' v)
      (bgFieldC (stepG d L N₁ m₁ k ϱ) S.a S.ν (bgC0 d L N)
        (H.dataUCH (ψ₀ + (r : ℂ) • v)) -
        (S.hG.precedes S.hG' (le_refl (k + 1))).restrictφ
          (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D')) := by
  dsimp only
  let v := S.hatField (hatCovSqrt S.G' S.a₁ S.ν H.D') (yhat x)
  let ψ₀ : S.EC := fun q =>
    (composeData (S.hG.precedes S.hG' (le_refl (k + 1))) S.a
      (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D') H.D').Ψ
        (unitRep (G' := S.G') q.1) q.2
  rw [hatFun_rawOf S.hG' _ _ hX]
  rw [hatLift_smul]
  have hlift : hatLift S.G' S.a₁ S.ν S.hG'
      ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) H.D' (yhat x) = liftC S.hG' v := rfl
  rw [hlift]
  have hT := H.compTangent_critical_ray v (r : ℂ)
  have hh : ∀ z i, (H.dataUCH (ψ₀ + (r : ℂ) • v)).h z i = H.D'.h z i :=
    H.dataUCH_h _
  have hi := interactionOne_eq S.hG S.hG' (le_refl (k + 1)) hX hh
  rw [hT] at hi
  exact hi

end Balaban.Fluctuation.StepSettingH
