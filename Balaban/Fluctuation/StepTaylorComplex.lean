/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.StepTaylor
public import Balaban.Fluctuation.StepComplexExponent
public import Balaban.Fluctuation.StepComplexAgree
public import Balaban.Fluctuation.StepTaylorW
import Mathlib.Tactic.Linarith

/-!
# The ray Taylor identities for the holomorphic step at a complex datum (HAT-RATE §2)

The complex analogue of `StepTaylor`.  Along the complex ray `ψ_z = ψ^{(k)}(θ) + z ψ'(ψ̂)`
(`psiAtCc`, `psiAtCc_ofReal : psiAtCc s = psiAtC s`) at a complex block datum `θ`:

* T1 `compTangent_rayC`: the tangent is `z • rayTangentC x` (affine in the complex parameter);
  `dataUC_psiAtCc_eq_lineAt`: the datum is affine.
* T2 `hasDerivAt_bgC_rayC`: the linear response (2.1) at the complex base point
  (`theorem72_linearResponse`), the critical-point identity `lower_bg_psi0C` being derived
  (`criticalPoint_complex`).  Premises: `InUnionDomainC … thm73C1` for `θ` and the base-domain
  witness of radius `bgC2` at `dataUC psi0C`.
* `exists_analyticAt_VkC_rayC`, `contDiffAt_VkC_ray`: the potential is holomorphic in the complex
  parameter at a parameter whose datum is in `𝒟` (analyticity of the small solution and of
  `interactionV`); the regularity is derived, not assumed.
* `VkC_ray_eq` (the splitting (2.2)), T3 `VkC_ray_vanish_of_baseDomain`, T4
  `VkC_ray_taylor_of_baseDomain`.
* T5 (real chart) `VkC_psiAtC_eq_Vk`, `VkC_ray_vanish_of_rayData`, `VkC_ray_taylor_agree`.
* T6 `VkC_ray_taylor_witness`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban.SmallField.Def6 Balaban.Background Balaban.Multiscale Balaban.Localization
  Balaban.SmallField Finset MeasureTheory Set Matrix Filter Topology Asymptotics

namespace StepSetting

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ)

/-- The complex ray with complex parameter. -/
noncomputable def psiAtCc (z : ℂ) (x : S.E) : S.EC := S.psi0C + z • S.shiftUC x

theorem psiAtCc_ofReal (s : ℝ) (x : S.E) : S.psiAtCc (s : ℂ) x = S.psiAtC s x := rfl

theorem psiAtCc_zero (x : S.E) : S.psiAtCc 0 x = S.psi0C := by
  unfold psiAtCc; rw [zero_smul, add_zero]

/-- The tangent of the complex ray. -/
noncomputable def rayTangentC (x : S.E) : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ :=
  liftC S.hG' (S.shiftUC x)

/-- The tangent datum of the complex ray. -/
noncomputable def rayDatumC (x : S.E) : BgData (stepG d L N₁ m₁ k ϱ) N :=
  BgData.clip (stepG d L N₁ m₁ k ϱ) (liftC S.hG' (S.shiftUC x)) (fun _ _ => 0)
    (isLayerConstant_liftC S.hG S.hG' (S.shiftUC x)) (fun _ _ _ _ _ _ _ => rfl)

theorem rayDatumC_Ψ (x : S.E) (y : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) :
    (S.rayDatumC x).Ψ y i = S.shiftUC x (unitPt S.hG' y, i) := by
  have hx : y ∈ dataSites (stepG d L N₁ m₁ k ϱ) := (mem_dataSites _).2 (Or.inl (S.hG y).1)
  simp [rayDatumC, BgData.clip, hx, liftC_apply]

theorem rayDatumC_h (x : S.E) (y : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) :
    (S.rayDatumC x).h y i = 0 := by
  simp [rayDatumC, BgData.clip, (S.hG y).1]

theorem rayDatumC_Ψ_eq (x : S.E) : (S.rayDatumC x).Ψ = S.rayTangentC x := by
  funext y i
  exact S.rayDatumC_Ψ x y i

/-- **T1 (datum affine along the complex ray).** -/
theorem dataUC_psiAtCc_eq_lineAt (z : ℂ) (x : S.E) :
    S.dataUC (S.psiAtCc z x) = (S.dataUC S.psi0C).lineAt (S.rayDatumC x) z := by
  refine bgData_ext' ?_ ?_
  · funext y i
    show _ = (S.dataUC S.psi0C).Ψ y i + z * (S.rayDatumC x).Ψ y i
    rw [S.dataUC_Ψ, S.dataUC_Ψ, S.rayDatumC_Ψ]
    simp [psiAtCc]
  · funext y i
    show _ = (S.dataUC S.psi0C).h y i + z * (S.rayDatumC x).h y i
    rw [S.dataUC_h, S.dataUC_h, S.rayDatumC_h]
    simp

/-- **T1.** `compTangent (dataUC ψ_z) = z • rayTangentC`. -/
theorem compTangent_rayC (z : ℂ) (x : S.E) :
    compTangent S.hG S.hG' (le_refl (k + 1)) S.a
      (bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D') S.D' (S.dataUC (S.psiAtCc z x)) =
      z • S.rayTangentC x := by
  rw [S.compTangent_dataUC]
  have : S.psiAtCc z x - S.psi0C = z • S.shiftUC x := by unfold psiAtCc; abel
  rw [this, map_smul]
  rfl

theorem compTangent_rayC_ofReal (s : ℝ) (x : S.E) :
    compTangent S.hG S.hG' (le_refl (k + 1)) S.a
      (bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D') S.D' (S.dataUC (S.psiAtC s x)) =
      (s : ℂ) • S.rayTangentC x := S.compTangent_rayC (s : ℂ) x

theorem source_rayDatumC (x : S.E) :
    source (stepG d L N₁ m₁ k ϱ) S.a S.ν (S.rayDatumC x) =
      qStar (stepG d L N₁ m₁ k ϱ) S.a (S.rayTangentC x) := by
  funext p
  unfold source
  rw [S.boundaryTerm_stepG]
  have hh : (S.rayDatumC x).h = fun _ _ => 0 := by
    funext y i; exact S.rayDatumC_h x y i
  rw [hh, S.rayDatumC_Ψ_eq]
  simp

section Crit

variable (ha₁ : 0 < S.a₁) (H : BgHyp d L (k + 1) ϱ S.a S.ν)
  (hD' : InUnionDomainC S.G' (bgC0 d L N) (thm73C1 d L N) S.ν S.D')

include ha₁ H hD' in
theorem lower_bg_psi0C :
    bgFieldC (stepG d L N₁ m₁ k ϱ) S.a S.ν (bgC0 d L N) (S.dataUC S.psi0C) =
        (S.hG.precedes S.hG' (le_refl (k + 1))).restrictφ
          (bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D') ∧
      bgMultC (stepG d L N₁ m₁ k ϱ) S.a S.ν (bgC0 d L N) (S.dataUC S.psi0C) =
        (S.hG.precedes S.hG' (le_refl (k + 1))).restrictα
          (bgMultC S.G' S.a S.ν (bgC0 d L N) S.D') := by
  obtain ⟨-, -, hfield, hmult, -⟩ :=
    criticalPoint_complex ha₁ S.hG S.hG' (le_refl (k + 1)) H H S.D' hD'
  rw [S.dataUC_psi0C]
  exact ⟨hfield, hmult⟩

include ha₁ H hD' in
/-- **T2.** -/
theorem hasDerivAt_bgC_rayC
    (hbase : InUnionDomainC (stepG d L N₁ m₁ k ϱ) (bgC0 d L N) (bgC2 d L N) S.ν
      (S.dataUC S.psi0C)) (x : S.E) :
    HasDerivAt (fun z : ℂ =>
      bgFieldC (stepG d L N₁ m₁ k ϱ) S.a S.ν (bgC0 d L N) (S.dataUC (S.psiAtCc z x)) -
        (S.hG.precedes S.hG' (le_refl (k + 1))).restrictφ
          (bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D'))
      (phiOne (S.hG.precedes S.hG' (le_refl (k + 1))) S.a S.ν
        (bgMultC S.G' S.a S.ν (bgC0 d L N) S.D') (bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D')
        (qStar (stepG d L N₁ m₁ k ϱ) S.a (S.rayTangentC x))) 0 := by
  obtain ⟨hF, hM⟩ := S.lower_bg_psi0C ha₁ H hD'
  obtain ⟨φd, αd, h1, -, -, h4, -⟩ := theorem72_linearResponse H hbase (S.rayDatumC x)
  have h3 : HasDerivAt (fun z : ℂ =>
      bgFieldC (stepG d L N₁ m₁ k ϱ) S.a S.ν (bgC0 d L N) (S.dataUC (S.psiAtCc z x))) φd 0 := by
    have e : (fun z : ℂ =>
      bgFieldC (stepG d L N₁ m₁ k ϱ) S.a S.ν (bgC0 d L N) (S.dataUC (S.psiAtCc z x))) =
        fun z : ℂ => bgFieldC (stepG d L N₁ m₁ k ϱ) S.a S.ν (bgC0 d L N)
          ((S.dataUC S.psi0C).lineAt (S.rayDatumC x) z) :=
      funext fun z => by rw [S.dataUC_psiAtCc_eq_lineAt]
    rw [e]; exact h1
  convert h3.sub_const _ using 1
  rw [h4, S.source_rayDatumC]
  unfold phiOne opHk fieldBase bgOp bgVec
  rw [hM]
  congr 3
  funext x i
  exact (congrFun hF _).symm

end Crit


section Reg

variable (ha₁ : 0 < S.a₁) (H : BgHyp d L (k + 1) ϱ S.a S.ν)
  (hD2 : InUnionDomainC S.G' (bgC0 d L N) (thm73C2 d L N) S.ν S.D')

include ha₁ H hD2 in
theorem exists_analyticAt_VkC_rayC (x : S.E) {z₀ : ℂ}
    (hz₀ : InUnionDomainC (stepG d L N₁ m₁ k ϱ) (bgC0 d L N) (bgC1 d L N) S.ν
      (S.dataUC (S.psiAtCc z₀ x))) :
    ∃ Φ : ℂ → ℂ, AnalyticAt ℂ Φ z₀ ∧ ∀ z : ℂ,
      InUnionDomainC (stepG d L N₁ m₁ k ϱ) (bgC0 d L N) (bgC1 d L N) S.ν
        (S.dataUC (S.psiAtCc z x)) → S.VkC (S.psiAtCc z x) = Φ z := by
  obtain ⟨F, hF, hFe⟩ := theorem72_analytic (G := stepG d L N₁ m₁ k ϱ) (a := S.a) (ν := S.ν) H
  let raw : ℂ → RawData d L (N₁ * L ^ m₁) (k + 1) N := fun z =>
    ((S.dataUC S.psi0C).Ψ + z • (S.rayDatumC x).Ψ, (S.dataUC S.psi0C).h + z • (S.rayDatumC x).h)
  have hraw : ∀ z, raw z = ((S.dataUC (S.psiAtCc z x)).Ψ, (S.dataUC (S.psiAtCc z x)).h) := by
    intro z; rw [S.dataUC_psiAtCc_eq_lineAt]; rfl
  have hrawan : AnalyticAt ℂ raw z₀ :=
    AnalyticAt.prod (analyticAt_const.add (analyticAt_id.smul analyticAt_const))
      (analyticAt_const.add (analyticAt_id.smul analyticAt_const))
  have hFat : AnalyticAt ℂ F (raw z₀) := hF _ ⟨_, hz₀, hraw z₀⟩
  have hFraw : AnalyticAt ℂ (fun z => F (raw z)) z₀ := hFat.comp hrawan
  have hD2' := hD2
  obtain ⟨δs, Φ, St, hΦ⟩ := base_standing ha₁ S.hG S.hG' (le_refl (k + 1)) H H S.D' hD2
  have hΦ' : restrictField (stepG d L N₁ m₁ k ϱ) Φ =
      fieldBase (S.hG.precedes S.hG' (le_refl (k + 1)))
        (bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D') :=
    funext fun x => funext fun i => hΦ x i
  refine ⟨fun z => interactionV (S.hG.precedes S.hG' (le_refl (k + 1))) S.a S.ν
    (bgMultC S.G' S.a S.ν (bgC0 d L N) S.D') (bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D')
    (z • S.rayTangentC x)
    ((F (raw z)).1 - (S.hG.precedes S.hG' (le_refl (k + 1))).restrictφ
      (bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D')), ?_, ?_⟩
  · refine analyticAt_interactionV (S.hG.precedes S.hG' (le_refl (k + 1))) S.a S.ν
      (αF := fun _ => bgMultC S.G' S.a S.ν (bgC0 d L N) S.D')
      (φF := fun _ => bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D')
      (ψF := fun z => z • S.rayTangentC x)
      (φ'F := fun z => (F (raw z)).1 - (S.hG.precedes S.hG' (le_refl (k + 1))).restrictφ
        (bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D'))
      (fun y => analyticAt_const) (fun r => analyticAt_const) (fun y i => ?_) (fun r => ?_) ?_ ?_
    · simp only [Pi.smul_apply, smul_eq_mul]
      exact analyticAt_id.mul analyticAt_const
    · exact (analyticAt_pi_iff.1 (analyticAt_fst.comp hFraw) r).sub analyticAt_const
    · exact dirichletOperator_isUnit (stepG d L N₁ m₁ k ϱ) St.pos St.mass St.weights _ St.alpha
    · show IsUnit (constraintForm (opHk (S.hG.precedes S.hG' (le_refl (k + 1))) S.a S.ν
        (bgMultC S.G' S.a S.ν (bgC0 d L N) S.D'))⁻¹
        (fieldBase (S.hG.precedes S.hG' (le_refl (k + 1)))
          (bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D')))
      rw [← hΦ']
      exact constraintForm_isUnit St
  · intro z hz
    unfold VkC
    rw [S.compTangent_rayC]
    beta_reduce
    rw [hraw z, hFe _ hz]


include ha₁ H hD2 in
/-- Smoothness of the complex ray potential along the real parameter. -/
theorem contDiffAt_VkC_ray (x : S.E) {t : ℝ}
    (hray : ∀ᶠ s : ℝ in 𝓝 t, InUnionDomainC (stepG d L N₁ m₁ k ϱ) (bgC0 d L N) (bgC1 d L N) S.ν
      (S.dataUC (S.psiAtC s x))) :
    ContDiffAt ℝ ⊤ (fun s : ℝ => S.VkC (S.psiAtC s x)) t := by
  obtain ⟨Φ, hΦ, hΦe⟩ := S.exists_analyticAt_VkC_rayC ha₁ H hD2 x (z₀ := (t : ℂ))
    hray.self_of_nhds
  have h1 : ContDiffAt ℝ ⊤ (fun s : ℝ => Φ (s : ℂ)) t :=
    ((hΦ.contDiffAt (n := ⊤)).restrict_scalars ℝ).comp t Complex.ofRealCLM.contDiff.contDiffAt
  refine h1.congr_of_eventuallyEq ?_
  filter_upwards [hray] with s hs
  exact hΦe (s : ℂ) hs

end Reg

/-! ### The splitting (2.2) at the complex datum -/

/-- `P_z = φ(ψ_z) - φ₀|` along the complex ray. -/
noncomputable def rayDiffC (x : S.E) (z : ℂ) : (stepG d L N₁ m₁ k ϱ).Ω 1 × Fin N → ℂ :=
  bgFieldC (stepG d L N₁ m₁ k ϱ) S.a S.ν (bgC0 d L N) (S.dataUC (S.psiAtCc z x)) -
    (S.hG.precedes S.hG' (le_refl (k + 1))).restrictφ
      (bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D')

/-- `A₁` of the complex ray. -/
noncomputable def rayA1C (x : S.E) : (stepG d L N₁ m₁ k ϱ).Ω 1 → ℂ :=
  alphaOne (S.hG.precedes S.hG' (le_refl (k + 1))) S.a S.ν
    (bgMultC S.G' S.a S.ν (bgC0 d L N) S.D') (bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D')
    (qStar (stepG d L N₁ m₁ k ϱ) S.a (S.rayTangentC x))

/-- `P₁` of the complex ray. -/
noncomputable def rayP1C (x : S.E) : (stepG d L N₁ m₁ k ϱ).Ω 1 × Fin N → ℂ :=
  phiOne (S.hG.precedes S.hG' (le_refl (k + 1))) S.a S.ν
    (bgMultC S.G' S.a S.ν (bgC0 d L N) S.D') (bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D')
    (qStar (stepG d L N₁ m₁ k ϱ) S.a (S.rayTangentC x))

/-- **(2.2) at the complex datum**, exactly, for every complex parameter. -/
theorem VkC_ray_eq (z : ℂ) (x : S.E) :
    S.VkC (S.psiAtCc z x) =
      (1 / 2) * ∑ w, (z * S.rayA1C x w) * ∑ i, S.rayDiffC x z (w, i) * S.rayDiffC x z (w, i) +
        (1 / 2) * pair (stepG d L N₁ m₁ k ϱ) (S.rayDiffC x z - z • S.rayP1C x)
          (S.rayHk *ᵥ (S.rayDiffC x z - z • S.rayP1C x)) := by
  unfold VkC interactionV
  rw [S.compTangent_rayC]
  have h1 : qStar (stepG d L N₁ m₁ k ϱ) S.a (z • S.rayTangentC x) =
      z • qStar (stepG d L N₁ m₁ k ϱ) S.a (S.rayTangentC x) := by
    funext p
    simp only [qStar, Pi.smul_apply, smul_eq_mul]
    ring
  rw [h1]
  simp only [alphaOne_smul, phiOne_smul]
  rfl

section Order

variable (ha₁ : 0 < S.a₁) (H : BgHyp d L (k + 1) ϱ S.a S.ν)
  (hD' : InUnionDomainC S.G' (bgC0 d L N) (thm73C1 d L N) S.ν S.D')

include ha₁ H hD' in
theorem rayDiffC_zero (x : S.E) : S.rayDiffC x 0 = 0 := by
  obtain ⟨hF, -⟩ := S.lower_bg_psi0C ha₁ H hD'
  unfold rayDiffC
  rw [S.psiAtCc_zero, hF]
  exact sub_self _

include ha₁ H hD' in
/-- The interaction along the complex ray is `o(s²)` at `s = 0`. -/
theorem isLittleO_VkC_ray_of_baseDomain
    (hbase : InUnionDomainC (stepG d L N₁ m₁ k ϱ) (bgC0 d L N) (bgC2 d L N) S.ν
      (S.dataUC S.psi0C)) (x : S.E) :
    (fun s : ℝ => S.VkC (S.psiAtC s x)) =o[𝓝 0] fun s : ℝ => s ^ 2 := by
  have hD0 := (S.hasDerivAt_bgC_rayC ha₁ H hD' hbase x)
  have hD : HasDerivAt (fun s : ℝ => S.rayDiffC x (s : ℂ)) (S.rayP1C x) 0 := by
    have : HasDerivAt (fun z : ℂ => S.rayDiffC x z) (S.rayP1C x) (((0 : ℝ) : ℂ)) := by
      rw [Complex.ofReal_zero]; exact hD0
    have hh : HasDerivAt (fun r : ℝ => (r : ℂ)) (1 : ℂ) (0 : ℝ) :=
      (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).congr_deriv (by simp)
    have h := this.scomp (0 : ℝ) hh
    rw [one_smul] at h
    exact h
  have hP : ∀ p, HasDerivAt (fun s : ℝ => S.rayDiffC x (s : ℂ) p) (S.rayP1C x p) 0 := fun p =>
    hasDerivAt_pi.1 hD p
  have h0 := S.rayDiffC_zero ha₁ H hD' x
  have hbig : ∀ p, (fun s : ℝ => S.rayDiffC x (s : ℂ) p) =O[𝓝 0] fun s : ℝ => s := by
    intro p
    have := (hP p).hasFDerivAt.isBigO_sub
    simpa [h0] using this
  have hlit : ∀ p, (fun s : ℝ => S.rayDiffC x (s : ℂ) p - (s : ℂ) * S.rayP1C x p) =o[𝓝 0]
      fun s : ℝ => s := by
    intro p
    have := (hasDerivAt_iff_isLittleO.1 (hP p))
    simpa [h0, Complex.real_smul] using this
  have hs : (fun s : ℝ => (s : ℂ)) =O[𝓝 0] fun s : ℝ => s :=
    IsBigO.of_bound 1 (Eventually.of_forall fun s => by simp)
  have hcube : (fun s : ℝ => s * (s * s)) =o[𝓝 0] fun s : ℝ => s ^ 2 := by
    refine (isLittleO_pow_pow (𝕜 := ℝ) (show 2 < 3 by norm_num)).congr_left (fun s => ?_)
    ring
  have hsq : (fun s : ℝ => s * s) = fun s : ℝ => s ^ 2 := funext fun s => by ring
  have hT1 : (fun s : ℝ => ∑ w, ((s : ℂ) * S.rayA1C x w) *
      ∑ i, S.rayDiffC x (s : ℂ) (w, i) * S.rayDiffC x (s : ℂ) (w, i)) =o[𝓝 0]
        fun s : ℝ => s ^ 2 := by
    refine isLittleO_sum_fn _ fun w _ => ?_
    have e1 : (fun s : ℝ => (s : ℂ) * S.rayA1C x w) =O[𝓝 0] fun s : ℝ => s := by
      have := hs.const_mul_left (S.rayA1C x w)
      simpa [mul_comm] using this
    have e2 : (fun s : ℝ => ∑ i, S.rayDiffC x (s : ℂ) (w, i) * S.rayDiffC x (s : ℂ) (w, i)) =O[𝓝 0]
        fun s : ℝ => s * s :=
      isBigO_sum_fn _ fun i _ => (hbig (w, i)).mul (hbig (w, i))
    exact (e1.mul e2).trans_isLittleO hcube
  have hT2 : (fun s : ℝ => pair (stepG d L N₁ m₁ k ϱ)
      (S.rayDiffC x (s : ℂ) - (s : ℂ) • S.rayP1C x)
      (S.rayHk *ᵥ (S.rayDiffC x (s : ℂ) - (s : ℂ) • S.rayP1C x))) =o[𝓝 0]
        fun s : ℝ => s ^ 2 := by
    unfold pair
    refine isLittleO_sum_fn _ fun p _ => ?_
    have e1 : (fun s : ℝ => (S.rayDiffC x (s : ℂ) - (s : ℂ) • S.rayP1C x) p) =o[𝓝 0]
        fun s : ℝ => s := by
      simpa [Complex.real_smul] using hlit p
    have e2 : (fun s : ℝ => (S.rayHk *ᵥ (S.rayDiffC x (s : ℂ) - (s : ℂ) • S.rayP1C x)) p) =o[𝓝 0]
        fun s : ℝ => s := by
      simp only [Matrix.mulVec, dotProduct]
      refine isLittleO_sum_fn _ fun q _ => ?_
      have := (hlit q).const_mul_left (S.rayHk p q)
      simpa [Complex.real_smul] using this
    have := e1.mul e2
    rwa [hsq] at this
  have := (hT1.const_mul_left (1 / 2 : ℂ)).add (hT2.const_mul_left (1 / 2 : ℂ))
  refine this.congr_left (fun s => ?_)
  exact (S.VkC_ray_eq (s : ℂ) x).symm

end Order

section Vanish

variable (ha₁ : 0 < S.a₁) (H : BgHyp d L (k + 1) ϱ S.a S.ν)
  (hD2 : InUnionDomainC S.G' (bgC0 d L N) (thm73C2 d L N) S.ν S.D')

include ha₁ H hD2 in
/-- **T3.**  `V(0) = V'(0) = V''(0) = 0` along the complex ray. -/
theorem VkC_ray_vanish_of_baseDomain
    (hbase : InUnionDomainC (stepG d L N₁ m₁ k ϱ) (bgC0 d L N) (bgC2 d L N) S.ν
      (S.dataUC S.psi0C)) (x : S.E)
    (hray0 : ∀ᶠ s : ℝ in 𝓝 0, InUnionDomainC (stepG d L N₁ m₁ k ϱ) (bgC0 d L N) (bgC1 d L N)
      S.ν (S.dataUC (S.psiAtC s x))) :
    S.VkC (S.psiAtC 0 x) = 0 ∧ deriv (fun s : ℝ => S.VkC (S.psiAtC s x)) 0 = 0 ∧
      deriv (deriv (fun s : ℝ => S.VkC (S.psiAtC s x))) 0 = 0 :=
  derivs_zero_of_isLittleO_sq
    (((S.contDiffAt_VkC_ray ha₁ H hD2 x hray0).of_le (by exact_mod_cast le_top)))
    (S.isLittleO_VkC_ray_of_baseDomain ha₁ H (hD2.mono (thm73C2_le_thm73C1 d L N)) hbase x)

include ha₁ H hD2 in
/-- **T4.**  The cubic integral remainder along the complex ray, `s ∈ [0,1]`. -/
theorem VkC_ray_taylor_of_baseDomain
    (hbase : InUnionDomainC (stepG d L N₁ m₁ k ϱ) (bgC0 d L N) (bgC2 d L N) S.ν
      (S.dataUC S.psi0C)) (x : S.E)
    (hray : ∀ t ∈ Icc (0 : ℝ) 1, ∀ᶠ s : ℝ in 𝓝 t,
      InUnionDomainC (stepG d L N₁ m₁ k ϱ) (bgC0 d L N) (bgC1 d L N) S.ν
        (S.dataUC (S.psiAtC s x))) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    S.VkC (S.psiAtC s x) = ∫ u in (0 : ℝ)..1,
      taylorWeight (u : ℂ) * ((s : ℂ) ^ 3 *
        iteratedDeriv 3 (fun r : ℝ => S.VkC (S.psiAtC r x)) (u * s)) := by
  obtain ⟨h0, h1, h2⟩ := S.VkC_ray_vanish_of_baseDomain ha₁ H hD2 hbase x
    (hray 0 ⟨le_rfl, zero_le_one⟩)
  have key := taylor3_integral (f := fun r : ℝ => S.VkC (S.psiAtC r x)) hs.1
    (fun t ht => (S.contDiffAt_VkC_ray ha₁ H hD2 x
      (hray t ⟨ht.1, ht.2.trans hs.2⟩)).of_le (by exact_mod_cast le_top)) h0 h1 h2
  rw [key]
  refine intervalIntegral.integral_congr fun u _ => ?_
  simp only [taylorWeight]
  push_cast
  ring

end Vanish

/-! ### T5: the real chart -/

section RealChart

variable {S} {pp : ℝ}

/-- On the real chart (the premises of `RayData`) the complex potential on the ray is the landed
`Vk` on the ray. -/
theorem VkC_psiAtC_eq_Vk (R : S.RayData pp) (s : ℝ) (x : S.E) :
    S.VkC (S.psiAtC s x) = S.Vk (S.psiAt s x) := by
  have hχ := (chiU_eq_one_iff _ _ _ _).1 R.hχu
  rw [S.psiAtC_eq R.ha₁ R.H R.hδ'0 R.hδ' R.hD'R R.hδ0 hχ R.hfam R.hsm, S.VkC_yhat]

/-- On the real chart the complex base datum is the real one. -/
theorem dataUC_psi0C_eq_dataU (R : S.RayData pp) : S.dataUC S.psi0C = S.dataU S.psi0 := by
  rw [S.psi0C_eq R.ha₁ R.H R.hδ'0 R.hδ' R.hD'R, S.dataUC_yhat]

/-- On the real chart the complex ray lies in `𝒟` near every parameter with `|t| ‖ψ̂‖ < p⁺`. -/
theorem eventually_inUnionDomainC_ray (R : S.RayData pp) {x : S.E} {t : ℝ}
    (ht : |t| * ‖x‖ < pp) :
    ∀ᶠ s : ℝ in 𝓝 t, InUnionDomainC (stepG d L N₁ m₁ k ϱ) (bgC0 d L N) (bgC1 d L N) S.ν
      (S.dataUC (S.psiAtC s x)) := by
  have hχ := (chiU_eq_one_iff _ _ _ _).1 R.hχu
  have hopen : IsOpen {s : ℝ | |s| * ‖x‖ < pp} := isOpen_lt (by fun_prop) continuous_const
  filter_upwards [hopen.mem_nhds ht] with s hs
  have := S.inUnionDomainC_of_R' R.H (R.dom (q := (s, x)) hs)
  rwa [← S.dataUC_yhat, ← S.psiAtC_eq R.ha₁ R.H R.hδ'0 R.hδ' R.hD'R R.hδ0 hχ R.hfam R.hsm] at this

/-- **T5 (vanishing, real chart).**  Under `RayData` and the real base-domain witness, the complex
ray potential vanishes to second order at `s = 0`. -/
theorem VkC_ray_vanish_of_rayData (R : S.RayData pp)
    (hbase : InUnionDomainC (stepG d L N₁ m₁ k ϱ) (bgC0 d L N) (bgC2 d L N) S.ν
      (S.dataU S.psi0)) (x : S.E) :
    S.VkC (S.psiAtC 0 x) = 0 ∧ deriv (fun s : ℝ => S.VkC (S.psiAtC s x)) 0 = 0 ∧
      deriv (deriv (fun s : ℝ => S.VkC (S.psiAtC s x))) 0 = 0 :=
  S.VkC_ray_vanish_of_baseDomain R.ha₁ R.H (S.D'_domains R.H R.hδ'0 R.hδ' R.hD'R).2
    (by rwa [S.dataUC_psi0C_eq_dataU R]) x
    (S.eventually_inUnionDomainC_ray R (by simpa using R.hpp.trans_le' (by simp)))

/-- **T5 (Taylor, real chart).**  The complex Taylor formula along the ray, with the premises of
`Vk_ray_taylor_of_baseDomain` only, and its agreement with the real one: the two functions of `s`
coincide, so the two cubic remainders are the same integral. -/
theorem VkC_ray_taylor_agree (R : S.RayData pp) (hlt : S.p₁ < pp)
    (hbase : InUnionDomainC (stepG d L N₁ m₁ k ϱ) (bgC0 d L N) (bgC2 d L N) S.ν
      (S.dataU S.psi0)) {x : S.E} (hx : ‖x‖ ≤ S.p₁) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    (fun r : ℝ => S.VkC (S.psiAtC r x)) = (fun r : ℝ => S.Vk (S.psiAt r x)) ∧
    S.VkC (S.psiAtC s x) = ∫ u in (0 : ℝ)..1,
      taylorWeight (u : ℂ) * ((s : ℂ) ^ 3 *
        iteratedDeriv 3 (fun r : ℝ => S.VkC (S.psiAtC r x)) (u * s)) ∧
    S.Vk (S.psiAt s x) = ∫ u in (0 : ℝ)..1,
      taylorWeight (u : ℂ) * ((s : ℂ) ^ 3 *
        iteratedDeriv 3 (fun r : ℝ => S.VkC (S.psiAtC r x)) (u * s)) := by
  have hfun : (fun r : ℝ => S.VkC (S.psiAtC r x)) = (fun r : ℝ => S.Vk (S.psiAt r x)) :=
    funext fun r => S.VkC_psiAtC_eq_Vk R r x
  have hC : S.VkC (S.psiAtC s x) = ∫ u in (0 : ℝ)..1,
      taylorWeight (u : ℂ) * ((s : ℂ) ^ 3 *
        iteratedDeriv 3 (fun r : ℝ => S.VkC (S.psiAtC r x)) (u * s)) := by
    refine S.VkC_ray_taylor_of_baseDomain R.ha₁ R.H (S.D'_domains R.H R.hδ'0 R.hδ' R.hD'R).2
      (by rwa [S.dataUC_psi0C_eq_dataU R]) x (fun t ht => ?_) hs
    refine S.eventually_inUnionDomainC_ray R ?_
    rw [abs_of_nonneg ht.1]
    calc t * ‖x‖ ≤ 1 * S.p₁ := mul_le_mul ht.2 hx (norm_nonneg _) zero_le_one
      _ < pp := by linarith
  exact ⟨hfun, hC, by rw [← S.VkC_psiAtC_eq_Vk R s x]; exact hC⟩

end RealChart

end StepSetting

/-! ### T6: non-vacuity -/

open Balaban Balaban.Inhabited Balaban.Localization.I5Inhabited in
/-- **Non-vacuity of the complex ray identities at the real witness.**  For the witness step of
`Vk_ray_taylor_witness`, viewed as a complex datum, the premises of `VkC_ray_vanish_of_baseDomain`
and `VkC_ray_taylor_of_baseDomain` hold (base-domain witness, domain of `θ`, the ray in `𝒟`), and
so do the conclusions. -/
theorem VkC_ray_taylor_witness :
    ∃ (m₁ : ℕ) (β δ : ℝ), 0 < β ∧ Nonempty ((witnessSetting m₁ β δ).RayData 2) ∧
      InUnionDomainC (stepG 3 3 6 m₁ 1 (rhoSep m₁)) (bgC0 3 3 2) (bgC2 3 3 2)
        (witnessSetting m₁ β δ).ν
        ((witnessSetting m₁ β δ).dataUC (witnessSetting m₁ β δ).psi0C) ∧
      ∀ x : (witnessSetting m₁ β δ).E, ‖x‖ ≤ (witnessSetting m₁ β δ).p₁ →
        deriv (fun s : ℝ => (witnessSetting m₁ β δ).VkC
          ((witnessSetting m₁ β δ).psiAtC s x)) 0 = 0 ∧
        deriv (deriv (fun s : ℝ => (witnessSetting m₁ β δ).VkC
          ((witnessSetting m₁ β δ).psiAtC s x))) 0 = 0 ∧
        ∀ s ∈ Set.Icc (0 : ℝ) 1, (witnessSetting m₁ β δ).VkC
            ((witnessSetting m₁ β δ).psiAtC s x) =
          ∫ u in (0 : ℝ)..1, taylorWeight (u : ℂ) * ((s : ℂ) ^ 3 *
            iteratedDeriv 3 (fun r : ℝ => (witnessSetting m₁ β δ).VkC
              ((witnessSetting m₁ β δ).psiAtC r x)) (u * s)) := by
  obtain ⟨m₁, β, δ, hβ, hp, hp2, ⟨R⟩, A, μ, ε, ⟨hT⟩, hD⟩ := exists_witness_rayInDomain
  have hbase := witness_baseDomain R
  refine ⟨m₁, β, δ, hβ, ⟨R⟩, ?_, fun x hx => ?_⟩
  · rwa [StepSetting.dataUC_psi0C_eq_dataU R]
  · obtain ⟨-, h1, h2⟩ := StepSetting.VkC_ray_vanish_of_rayData R hbase x
    exact ⟨h1, h2, fun s hs => (StepSetting.VkC_ray_taylor_agree R hp2 hbase hx hs).2.1⟩

end Balaban.Fluctuation
