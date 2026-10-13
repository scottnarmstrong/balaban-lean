/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.MarkedTangent
public import Balaban.Fluctuation.StepTaylorComplex
public import Balaban.Fluctuation.StepBaseDomain
public import Balaban.Fluctuation.Thm31a
public import Balaban.Fluctuation.StepComplexThm31
public import Balaban.Fluctuation.StepComplexHat
public import Balaban.Fluctuation.StepComplexSmall
public import Balaban.Fluctuation.StepComplexLocal
public import Balaban.Fluctuation.StepComplexLocalAgree
public import Balaban.Fluctuation.StepRegClass
public import Balaban.Fluctuation.StepActivityHatRay
public import Balaban.Fluctuation.InteractionVPart
public import Balaban.Fluctuation.InteractionVBlockScaled
public import Balaban.Inhabited.DAPhysicalTower
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The marked cubic Taylor form of the fluctuation step

Companion of `MarkedTangent.lean` (formulas (1)-(5) of the note `MARKCUBIC`).  The first-order
term of the step at a root `z` is the expectation of `f_z(u, ψ̂) = DΦ₁(u ψ')[1_{B(z)} ψ']`
(`E1Marks`, `E1MarksC`).  With the marked tangent `v_t = u ψ' + t M_z ψ'` of `MarkedTangent.lean`
this file proves:

* **General complex tangents** (`psiAtV`, `VkC_rayV_vanish_of_baseDomain`,
  `VkC_rayV_taylor_of_baseDomain`): the ray identities of `StepTaylorComplex` for an arbitrary
  complex direction `v` of the unit lattice in place of `shiftUC ψ̂` (the proofs are those of the
  landed theorems; the direction enters only through `liftC v`).  So `V^{(k)}` vanishes to second
  order at the critical point along every complex line, in particular along the marked ones.
* **`MARK-REAL`** (`hasDerivAt_Phi1_marked`, `deriv_Phi1_marked_eq_E1Marks_integrand`,
  `hasDerivAt_Phi1C_marked`, `deriv_Phi1C_marked_eq_E1MarksC_integrand`): for every class, the
  `t`-derivative at `0` of `Φ₁(v_t)` is exactly the landed `f_z(u, ψ̂)`; no factor of `u` or `β`
  and no division by `u`.  The differentiability hypothesis holds at the ray points under the
  landed `ClassRegularLoc` (`ClassRegularLocC`).
* **`MARK-TAYLOR`** (`VkC_psi0C_add_eq_interactionOne`, `VkC_taylor_line`, `marked_difference_eq`,
  `VkC_marked_eq_block_terms`, real chart: `Phi1_zeroClass_marked_eq_Phi1C`): for the zero class,
  `V^{(k)}(ψ^{(k)} + v) = ∫₀¹ ω(s) D³f(Θ, s·lift v)[lift v]³ ds` with `f = interactionOne`, the marked
  difference `Δ_z = Φ₁(v_t) - Φ₁(v_0)` is `-β` times the difference of these cubic terms, and,
  given the block expansions of `vblock_expansion_scaled`, the cubic term is the sum over blocks and
  labels of `rayTerm (dl3 E_{b,Y}) ...` (equalities only).
* **T5** (`markedBlockTerm`, `analyticOnNhd_markedBlockTerm`, `norm_markedBlockTerm_le`,
  `norm_deriv_markedBlockTerm_le`, `marked_term_cauchy`, `marked_vblock_term_cauchy`): each marked
  block term `t ↦ ∫₀¹ ω(s) D³E_{b,Y}(Θ, s v_t)[v_t]³ ds` is analytic on `|t| < t₁` and its
  `t`-derivative at `0` is at most `3 E* e^{-2 κ_dec d(Y)}/(r³ t₀)`; `vblock_expansion_scaled` is
  stated for every tangent of `FlBall Hm δ₁`, so it accepts the marked tangent as is.
* **T6** (`marked_radius_and_derivative_at_witness`): non-vacuity at the landed witness step.

No mark family is constructed here and nothing depends on a choice of generating set for the class
terms; the root anchoring, the count and the assembly (`ROOT-BRIDGE`, `ROOT-FIBRE`, `MARK-ROWS`,
`MARK-SCALED-COUNT`, `MARK-ASSEMBLY`, `MARK-PARAM`) are not touched.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban.SmallField.Def6 Balaban.Background Balaban.Multiscale Balaban.Localization
  Balaban.SmallField Finset MeasureTheory Set Matrix Filter Topology Asymptotics

namespace StepSetting

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ)

/-- The complex line through the critical point in the complex direction `v` of the unit lattice:
`ψ^{(k)}(θ) + z · v` (`psiAtCc` with an arbitrary direction in place of `shiftUC ψ̂`). -/
noncomputable def psiAtV (z : ℂ) (v : S.EC) : S.EC := S.psi0C + z • v

theorem psiAtV_zero (v : S.EC) : S.psiAtV 0 v = S.psi0C := by
  unfold psiAtV; rw [zero_smul, add_zero]

theorem psiAtV_shiftUC (z : ℂ) (x : S.E) : S.psiAtV z (S.shiftUC x) = S.psiAtCc z x := rfl

/-- The tangent of the complex ray. -/
noncomputable def rayTangentV (v : S.EC) : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ :=
  liftC S.hG' (v)

/-- The tangent datum of the complex ray. -/
noncomputable def rayDatumV (v : S.EC) : BgData (stepG d L N₁ m₁ k ϱ) N :=
  BgData.clip (stepG d L N₁ m₁ k ϱ) (liftC S.hG' (v)) (fun _ _ => 0)
    (isLayerConstant_liftC S.hG S.hG' (v)) (fun _ _ _ _ _ _ _ => rfl)

theorem rayDatumV_Ψ (v : S.EC) (y : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) :
    (S.rayDatumV v).Ψ y i = v (unitPt S.hG' y, i) := by
  have hx : y ∈ dataSites (stepG d L N₁ m₁ k ϱ) := (mem_dataSites _).2 (Or.inl (S.hG y).1)
  simp [rayDatumV, BgData.clip, hx, liftC_apply]

theorem rayDatumV_h (v : S.EC) (y : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) :
    (S.rayDatumV v).h y i = 0 := by
  simp [rayDatumV, BgData.clip, (S.hG y).1]

theorem rayDatumV_Ψ_eq (v : S.EC) : (S.rayDatumV v).Ψ = S.rayTangentV v := by
  funext y i
  exact S.rayDatumV_Ψ v y i

/-- **T1 (datum affine along the complex ray).** -/
theorem dataUC_psiAtV_eq_lineAt (z : ℂ) (v : S.EC) :
    S.dataUC (S.psiAtV z v) = (S.dataUC S.psi0C).lineAt (S.rayDatumV v) z := by
  refine bgData_ext' ?_ ?_
  · funext y i
    show _ = (S.dataUC S.psi0C).Ψ y i + z * (S.rayDatumV v).Ψ y i
    rw [S.dataUC_Ψ, S.dataUC_Ψ, S.rayDatumV_Ψ]
    simp [psiAtV]
  · funext y i
    show _ = (S.dataUC S.psi0C).h y i + z * (S.rayDatumV v).h y i
    rw [S.dataUC_h, S.dataUC_h, S.rayDatumV_h]
    simp

/-- **T1.** `compTangent (dataUC ψ_z) = z • rayTangentV`. -/
theorem compTangent_rayV (z : ℂ) (v : S.EC) :
    compTangent S.hG S.hG' (le_refl (k + 1)) S.a
      (bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D') S.D' (S.dataUC (S.psiAtV z v)) =
      z • S.rayTangentV v := by
  rw [S.compTangent_dataUC]
  have : S.psiAtV z v - S.psi0C = z • v := by unfold psiAtV; abel
  rw [this, map_smul]
  rfl

theorem compTangent_rayV_ofReal (s : ℝ) (v : S.EC) :
    compTangent S.hG S.hG' (le_refl (k + 1)) S.a
      (bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D') S.D' (S.dataUC (S.psiAtV ((s : ℝ) : ℂ) v)) =
      (s : ℂ) • S.rayTangentV v := S.compTangent_rayV (s : ℂ) v

theorem source_rayDatumV (v : S.EC) :
    source (stepG d L N₁ m₁ k ϱ) S.a S.ν (S.rayDatumV v) =
      qStar (stepG d L N₁ m₁ k ϱ) S.a (S.rayTangentV v) := by
  funext p
  unfold source
  rw [S.boundaryTerm_stepG]
  have hh : (S.rayDatumV v).h = fun _ _ => 0 := by
    funext y i; exact S.rayDatumV_h v y i
  rw [hh, S.rayDatumV_Ψ_eq]
  simp

section Crit

variable (ha₁ : 0 < S.a₁) (H : BgHyp d L (k + 1) ϱ S.a S.ν)
  (hD' : InUnionDomainC S.G' (bgC0 d L N) (thm73C1 d L N) S.ν S.D')


include ha₁ H hD' in
/-- **T2.** -/
theorem hasDerivAt_bgC_rayV
    (hbase : InUnionDomainC (stepG d L N₁ m₁ k ϱ) (bgC0 d L N) (bgC2 d L N) S.ν
      (S.dataUC S.psi0C)) (v : S.EC) :
    HasDerivAt (fun z : ℂ =>
      bgFieldC (stepG d L N₁ m₁ k ϱ) S.a S.ν (bgC0 d L N) (S.dataUC (S.psiAtV z v)) -
        (S.hG.precedes S.hG' (le_refl (k + 1))).restrictφ
          (bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D'))
      (phiOne (S.hG.precedes S.hG' (le_refl (k + 1))) S.a S.ν
        (bgMultC S.G' S.a S.ν (bgC0 d L N) S.D') (bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D')
        (qStar (stepG d L N₁ m₁ k ϱ) S.a (S.rayTangentV v))) 0 := by
  obtain ⟨hF, hM⟩ := S.lower_bg_psi0C ha₁ H hD'
  obtain ⟨φd, αd, h1, -, -, h4, -⟩ := theorem72_linearResponse H hbase (S.rayDatumV v)
  have h3 : HasDerivAt (fun z : ℂ =>
      bgFieldC (stepG d L N₁ m₁ k ϱ) S.a S.ν (bgC0 d L N) (S.dataUC (S.psiAtV z v))) φd 0 := by
    have e : (fun z : ℂ =>
      bgFieldC (stepG d L N₁ m₁ k ϱ) S.a S.ν (bgC0 d L N) (S.dataUC (S.psiAtV z v))) =
        fun z : ℂ => bgFieldC (stepG d L N₁ m₁ k ϱ) S.a S.ν (bgC0 d L N)
          ((S.dataUC S.psi0C).lineAt (S.rayDatumV v) z) :=
      funext fun z => by rw [S.dataUC_psiAtV_eq_lineAt]
    rw [e]; exact h1
  convert h3.sub_const _ using 1
  rw [h4, S.source_rayDatumV]
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
theorem exists_analyticAt_VkC_rayV (v : S.EC) {z₀ : ℂ}
    (hz₀ : InUnionDomainC (stepG d L N₁ m₁ k ϱ) (bgC0 d L N) (bgC1 d L N) S.ν
      (S.dataUC (S.psiAtV z₀ v))) :
    ∃ Φ : ℂ → ℂ, AnalyticAt ℂ Φ z₀ ∧ ∀ z : ℂ,
      InUnionDomainC (stepG d L N₁ m₁ k ϱ) (bgC0 d L N) (bgC1 d L N) S.ν
        (S.dataUC (S.psiAtV z v)) → S.VkC (S.psiAtV z v) = Φ z := by
  obtain ⟨F, hF, hFe⟩ := theorem72_analytic (G := stepG d L N₁ m₁ k ϱ) (a := S.a) (ν := S.ν) H
  let raw : ℂ → RawData d L (N₁ * L ^ m₁) (k + 1) N := fun z =>
    ((S.dataUC S.psi0C).Ψ + z • (S.rayDatumV v).Ψ, (S.dataUC S.psi0C).h + z • (S.rayDatumV v).h)
  have hraw : ∀ z, raw z = ((S.dataUC (S.psiAtV z v)).Ψ, (S.dataUC (S.psiAtV z v)).h) := by
    intro z; rw [S.dataUC_psiAtV_eq_lineAt]; rfl
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
    (z • S.rayTangentV v)
    ((F (raw z)).1 - (S.hG.precedes S.hG' (le_refl (k + 1))).restrictφ
      (bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D')), ?_, ?_⟩
  · refine analyticAt_interactionV (S.hG.precedes S.hG' (le_refl (k + 1))) S.a S.ν
      (αF := fun _ => bgMultC S.G' S.a S.ν (bgC0 d L N) S.D')
      (φF := fun _ => bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D')
      (ψF := fun z => z • S.rayTangentV v)
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
    rw [S.compTangent_rayV]
    beta_reduce
    rw [hraw z, hFe _ hz]


include ha₁ H hD2 in
/-- Smoothness of the complex ray potential along the real parameter. -/
theorem contDiffAt_VkC_rayV (v : S.EC) {t : ℝ}
    (hray : ∀ᶠ s : ℝ in 𝓝 t, InUnionDomainC (stepG d L N₁ m₁ k ϱ) (bgC0 d L N) (bgC1 d L N) S.ν
      (S.dataUC (S.psiAtV ((s : ℝ) : ℂ) v))) :
    ContDiffAt ℝ ⊤ (fun s : ℝ => S.VkC (S.psiAtV ((s : ℝ) : ℂ) v)) t := by
  obtain ⟨Φ, hΦ, hΦe⟩ := S.exists_analyticAt_VkC_rayV ha₁ H hD2 v (z₀ := (t : ℂ))
    hray.self_of_nhds
  have h1 : ContDiffAt ℝ ⊤ (fun s : ℝ => Φ (s : ℂ)) t :=
    ((hΦ.contDiffAt (n := ⊤)).restrict_scalars ℝ).comp t Complex.ofRealCLM.contDiff.contDiffAt
  refine h1.congr_of_eventuallyEq ?_
  filter_upwards [hray] with s hs
  exact hΦe (s : ℂ) hs

end Reg

/-! ### The splitting (2.2) at the complex datum -/

/-- `P_z = φ(ψ_z) - φ₀|` along the complex ray. -/
noncomputable def rayDiffV (v : S.EC) (z : ℂ) : (stepG d L N₁ m₁ k ϱ).Ω 1 × Fin N → ℂ :=
  bgFieldC (stepG d L N₁ m₁ k ϱ) S.a S.ν (bgC0 d L N) (S.dataUC (S.psiAtV z v)) -
    (S.hG.precedes S.hG' (le_refl (k + 1))).restrictφ
      (bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D')

/-- `A₁` of the complex ray. -/
noncomputable def rayA1V (v : S.EC) : (stepG d L N₁ m₁ k ϱ).Ω 1 → ℂ :=
  alphaOne (S.hG.precedes S.hG' (le_refl (k + 1))) S.a S.ν
    (bgMultC S.G' S.a S.ν (bgC0 d L N) S.D') (bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D')
    (qStar (stepG d L N₁ m₁ k ϱ) S.a (S.rayTangentV v))

/-- `P₁` of the complex ray. -/
noncomputable def rayP1V (v : S.EC) : (stepG d L N₁ m₁ k ϱ).Ω 1 × Fin N → ℂ :=
  phiOne (S.hG.precedes S.hG' (le_refl (k + 1))) S.a S.ν
    (bgMultC S.G' S.a S.ν (bgC0 d L N) S.D') (bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D')
    (qStar (stepG d L N₁ m₁ k ϱ) S.a (S.rayTangentV v))

/-- **(2.2) at the complex datum**, exactly, for every complex parameter. -/
theorem VkC_rayV_eq (z : ℂ) (v : S.EC) :
    S.VkC (S.psiAtV z v) =
      (1 / 2) * ∑ w, (z * S.rayA1V v w) * ∑ i, S.rayDiffV v z (w, i) * S.rayDiffV v z (w, i) +
        (1 / 2) * pair (stepG d L N₁ m₁ k ϱ) (S.rayDiffV v z - z • S.rayP1V v)
          (S.rayHk *ᵥ (S.rayDiffV v z - z • S.rayP1V v)) := by
  unfold VkC interactionV
  rw [S.compTangent_rayV]
  have h1 : qStar (stepG d L N₁ m₁ k ϱ) S.a (z • S.rayTangentV v) =
      z • qStar (stepG d L N₁ m₁ k ϱ) S.a (S.rayTangentV v) := by
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
theorem rayDiffV_zero (v : S.EC) : S.rayDiffV v 0 = 0 := by
  obtain ⟨hF, -⟩ := S.lower_bg_psi0C ha₁ H hD'
  unfold rayDiffV
  rw [S.psiAtV_zero, hF]
  exact sub_self _

include ha₁ H hD' in
/-- The interaction along the complex ray is `o(s²)` at `s = 0`. -/
theorem isLittleO_VkC_rayV_of_baseDomain
    (hbase : InUnionDomainC (stepG d L N₁ m₁ k ϱ) (bgC0 d L N) (bgC2 d L N) S.ν
      (S.dataUC S.psi0C)) (v : S.EC) :
    (fun s : ℝ => S.VkC (S.psiAtV ((s : ℝ) : ℂ) v)) =o[𝓝 0] fun s : ℝ => s ^ 2 := by
  have hD0 := (S.hasDerivAt_bgC_rayV ha₁ H hD' hbase v)
  have hD : HasDerivAt (fun s : ℝ => S.rayDiffV v (s : ℂ)) (S.rayP1V v) 0 := by
    have : HasDerivAt (fun z : ℂ => S.rayDiffV v z) (S.rayP1V v) (((0 : ℝ) : ℂ)) := by
      rw [Complex.ofReal_zero]; exact hD0
    have hh : HasDerivAt (fun r : ℝ => (r : ℂ)) (1 : ℂ) (0 : ℝ) :=
      (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).congr_deriv (by simp)
    have h := this.scomp (0 : ℝ) hh
    rw [one_smul] at h
    exact h
  have hP : ∀ p, HasDerivAt (fun s : ℝ => S.rayDiffV v (s : ℂ) p) (S.rayP1V v p) 0 := fun p =>
    hasDerivAt_pi.1 hD p
  have h0 := S.rayDiffV_zero ha₁ H hD' v
  have hbig : ∀ p, (fun s : ℝ => S.rayDiffV v (s : ℂ) p) =O[𝓝 0] fun s : ℝ => s := by
    intro p
    have := (hP p).hasFDerivAt.isBigO_sub
    simpa [h0] using this
  have hlit : ∀ p, (fun s : ℝ => S.rayDiffV v (s : ℂ) p - (s : ℂ) * S.rayP1V v p) =o[𝓝 0]
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
  have hT1 : (fun s : ℝ => ∑ w, ((s : ℂ) * S.rayA1V v w) *
      ∑ i, S.rayDiffV v (s : ℂ) (w, i) * S.rayDiffV v (s : ℂ) (w, i)) =o[𝓝 0]
        fun s : ℝ => s ^ 2 := by
    refine isLittleO_sum_fn _ fun w _ => ?_
    have e1 : (fun s : ℝ => (s : ℂ) * S.rayA1V v w) =O[𝓝 0] fun s : ℝ => s := by
      have := hs.const_mul_left (S.rayA1V v w)
      simpa [mul_comm] using this
    have e2 : (fun s : ℝ => ∑ i, S.rayDiffV v (s : ℂ) (w, i) * S.rayDiffV v (s : ℂ) (w, i)) =O[𝓝 0]
        fun s : ℝ => s * s :=
      isBigO_sum_fn _ fun i _ => (hbig (w, i)).mul (hbig (w, i))
    exact (e1.mul e2).trans_isLittleO hcube
  have hT2 : (fun s : ℝ => pair (stepG d L N₁ m₁ k ϱ)
      (S.rayDiffV v (s : ℂ) - (s : ℂ) • S.rayP1V v)
      (S.rayHk *ᵥ (S.rayDiffV v (s : ℂ) - (s : ℂ) • S.rayP1V v))) =o[𝓝 0]
        fun s : ℝ => s ^ 2 := by
    unfold pair
    refine isLittleO_sum_fn _ fun p _ => ?_
    have e1 : (fun s : ℝ => (S.rayDiffV v (s : ℂ) - (s : ℂ) • S.rayP1V v) p) =o[𝓝 0]
        fun s : ℝ => s := by
      simpa [Complex.real_smul] using hlit p
    have e2 : (fun s : ℝ => (S.rayHk *ᵥ (S.rayDiffV v (s : ℂ) - (s : ℂ) • S.rayP1V v)) p) =o[𝓝 0]
        fun s : ℝ => s := by
      simp only [Matrix.mulVec, dotProduct]
      refine isLittleO_sum_fn _ fun q _ => ?_
      have := (hlit q).const_mul_left (S.rayHk p q)
      simpa [Complex.real_smul] using this
    have := e1.mul e2
    rwa [hsq] at this
  have := (hT1.const_mul_left (1 / 2 : ℂ)).add (hT2.const_mul_left (1 / 2 : ℂ))
  refine this.congr_left (fun s => ?_)
  exact (S.VkC_rayV_eq (s : ℂ) v).symm

end Order

section Vanish

variable (ha₁ : 0 < S.a₁) (H : BgHyp d L (k + 1) ϱ S.a S.ν)
  (hD2 : InUnionDomainC S.G' (bgC0 d L N) (thm73C2 d L N) S.ν S.D')

include ha₁ H hD2 in
/-- **T3.**  `V(0) = V'(0) = V''(0) = 0` along the complex ray. -/
theorem VkC_rayV_vanish_of_baseDomain
    (hbase : InUnionDomainC (stepG d L N₁ m₁ k ϱ) (bgC0 d L N) (bgC2 d L N) S.ν
      (S.dataUC S.psi0C)) (v : S.EC)
    (hray0 : ∀ᶠ s : ℝ in 𝓝 0, InUnionDomainC (stepG d L N₁ m₁ k ϱ) (bgC0 d L N) (bgC1 d L N)
      S.ν (S.dataUC (S.psiAtV ((s : ℝ) : ℂ) v))) :
    S.VkC (S.psiAtV ((0 : ℝ) : ℂ) v) = 0 ∧ deriv (fun s : ℝ => S.VkC (S.psiAtV ((s : ℝ) : ℂ) v)) 0 = 0 ∧
      deriv (deriv (fun s : ℝ => S.VkC (S.psiAtV ((s : ℝ) : ℂ) v))) 0 = 0 :=
  derivs_zero_of_isLittleO_sq
    (((S.contDiffAt_VkC_rayV ha₁ H hD2 v hray0).of_le (by exact_mod_cast le_top)))
    (S.isLittleO_VkC_rayV_of_baseDomain ha₁ H (hD2.mono (thm73C2_le_thm73C1 d L N)) hbase v)

include ha₁ H hD2 in
/-- **T4.**  The cubic integral remainder along the complex ray, `s ∈ [0,1]`. -/
theorem VkC_rayV_taylor_of_baseDomain
    (hbase : InUnionDomainC (stepG d L N₁ m₁ k ϱ) (bgC0 d L N) (bgC2 d L N) S.ν
      (S.dataUC S.psi0C)) (v : S.EC)
    (hray : ∀ t ∈ Icc (0 : ℝ) 1, ∀ᶠ s : ℝ in 𝓝 t,
      InUnionDomainC (stepG d L N₁ m₁ k ϱ) (bgC0 d L N) (bgC1 d L N) S.ν
        (S.dataUC (S.psiAtV ((s : ℝ) : ℂ) v))) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    S.VkC (S.psiAtV ((s : ℝ) : ℂ) v) = ∫ u in (0 : ℝ)..1,
      taylorWeight (u : ℂ) * ((s : ℂ) ^ 3 *
        iteratedDeriv 3 (fun r : ℝ => S.VkC (S.psiAtV ((r : ℝ) : ℂ) v)) (u * s)) := by
  obtain ⟨h0, h1, h2⟩ := S.VkC_rayV_vanish_of_baseDomain ha₁ H hD2 hbase v
    (hray 0 ⟨le_rfl, zero_le_one⟩)
  have key := taylor3_integral (f := fun r : ℝ => S.VkC (S.psiAtV ((r : ℝ) : ℂ) v)) hs.1
    (fun t ht => (S.contDiffAt_VkC_rayV ha₁ H hD2 v
      (hray t ⟨ht.1, ht.2.trans hs.2⟩)).of_le (by exact_mod_cast le_top)) h0 h1 h2
  rw [key]
  refine intervalIntegral.integral_congr fun u _ => ?_
  simp only [taylorWeight]
  push_cast
  ring

end Vanish

/-! ### T3: the exact derivative along the marked family -/

section Derivative

variable (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))) (C : StepClass d L N₁ m₁ k N ϱ)

/-- **`MARK-REAL`, real step.**  If the step exponent `Φ₁` is differentiable at the ray point
`u · ψ'`, then `t ↦ Φ₁(v_t)` has derivative `DΦ₁(u ψ')[1_{B(z)} ψ']` at `t = 0`.  No division by `u`
occurs, so the statement holds at `u = 0`. -/
theorem hasDerivAt_Phi1_marked (u : ℝ) (x : S.E)
    (hd : DifferentiableAt ℝ (S.Phi1 C) (u • S.shiftU x)) :
    HasDerivAt (fun t : ℝ => S.Phi1 C (S.markedTangent z u t x))
      ((fderiv ℝ (S.Phi1 C) (u • S.shiftU x)) (S.maskU z (S.shiftU x))) 0 := by
  have hl : HasDerivAt (fun t : ℝ => S.markedTangent z u t x) (S.maskU z (S.shiftU x)) 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).smul_const (S.maskU z (S.shiftU x))).const_add
      (u • S.shiftU x)
    simpa [markedTangent] using this
  have hd' : HasFDerivAt (S.Phi1 C) (fderiv ℝ (S.Phi1 C) (u • S.shiftU x))
      (S.markedTangent z u 0 x) := by
    rw [S.markedTangent_zero_t]; exact hd.hasFDerivAt
  exact hd'.comp_hasDerivAt (0 : ℝ) hl

/-- **`MARK-REAL`, real step, in the form of `E1Marks`**: the derivative at `t = 0` of
`Φ₁(v_t)` is exactly the integrand `f(u, ψ̂) = DΦ₁(u ψ')[1_{B(z)} ψ']` of `E1Marks` (the function
`fun s x => (fderiv ℝ (S.Phi1 C) (s • S.shiftU x)) (S.maskU z (S.shiftU x))`), with no factor of
`u`, `β` or other normalisation. -/
theorem deriv_Phi1_marked_eq_E1Marks_integrand (u : ℝ) (x : S.E)
    (hd : DifferentiableAt ℝ (S.Phi1 C) (u • S.shiftU x)) :
    deriv (fun t : ℝ => S.Phi1 C (S.markedTangent z u t x)) 0 =
      (fun (s : ℝ) (x : S.E) => (fderiv ℝ (S.Phi1 C) (s • S.shiftU x))
        (S.maskU z (S.shiftU x))) u x :=
  (S.hasDerivAt_Phi1_marked z C u x hd).deriv

/-- The differentiability hypothesis of `hasDerivAt_Phi1_marked` holds at the ray points of the
landed regularity `ClassRegularLoc` (any class): `‖ψ̂‖ ≤ p₁`, `u ∈ [0,1]`. -/
theorem differentiableAt_Phi1_of_classRegularLoc {g : Fld d L N₁ m₁ (k + 1) N}
    (hc : S.ClassRegularLoc C g) {x : S.E} (hx : ‖x‖ ≤ S.p₁) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    DifferentiableAt ℝ (S.Phi1 C) (u • S.shiftU x) := by
  obtain ⟨O, hO, hcd, hmem⟩ := hc.phi1
  exact ((hcd.contDiffAt (hO.mem_nhds (hmem x hx u hu))).differentiableAt (by norm_num))

/-- **`MARK-REAL`, real step, from the landed regularity**: for a class with `ClassRegularLoc`,
the identity holds at every ray point `u ∈ [0,1]`, `‖ψ̂‖ ≤ p₁`. -/
theorem hasDerivAt_Phi1_marked_of_classRegularLoc {g : Fld d L N₁ m₁ (k + 1) N}
    (hc : S.ClassRegularLoc C g) {x : S.E} (hx : ‖x‖ ≤ S.p₁) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (fun t : ℝ => S.Phi1 C (S.markedTangent z u t x))
      ((fderiv ℝ (S.Phi1 C) (u • S.shiftU x)) (S.maskU z (S.shiftU x))) 0 :=
  S.hasDerivAt_Phi1_marked z C u x (S.differentiableAt_Phi1_of_classRegularLoc C hc hx hu)

/-- **`MARK-REAL`, complex step.**  If `Φ₁ = Phi1C` is complex differentiable at `u · ψ'`
(`ψ' = shiftUC ψ̂`), then `t ↦ Φ₁(v_t)`, `t ∈ ℂ`, has derivative
`DΦ₁(u ψ')[1_{B(z)} ψ']` at `t = 0`: the function of `E1MarksC`.  It holds at `u = 0`. -/
theorem hasDerivAt_Phi1C_marked (u : ℂ) (x : S.E)
    (hd : DifferentiableAt ℂ (S.Phi1C C) (u • S.shiftUC x)) :
    HasDerivAt (fun t : ℂ => S.Phi1C C (S.markedTangentC z u t x))
      ((fderiv ℂ (S.Phi1C C) (u • S.shiftUC x)) (S.maskUC z (S.shiftUC x))) 0 := by
  have hl : HasDerivAt (fun t : ℂ => S.markedTangentC z u t x) (S.maskUC z (S.shiftUC x)) 0 := by
    have := ((hasDerivAt_id (0 : ℂ)).smul_const (S.maskUC z (S.shiftUC x))).const_add
      (u • S.shiftUC x)
    simpa [markedTangentC] using this
  have hd' : HasFDerivAt (S.Phi1C C) (fderiv ℂ (S.Phi1C C) (u • S.shiftUC x))
      (S.markedTangentC z u 0 x) := by
    rw [S.markedTangentC_zero_t]; exact hd.hasFDerivAt
  exact hd'.comp_hasDerivAt (0 : ℂ) hl

/-- **`MARK-REAL`, complex step, in the form of `E1MarksC`** (`u = (s : ℂ)` real `s`): the
derivative at `t = 0` of `Φ₁(v_t)` is the integrand
`fun s x => (fderiv ℂ (S.Phi1C C) ((s : ℂ) • S.shiftUC x)) (S.maskUC z (S.shiftUC x))`. -/
theorem deriv_Phi1C_marked_eq_E1MarksC_integrand (s : ℝ) (x : S.E)
    (hd : DifferentiableAt ℂ (S.Phi1C C) ((s : ℂ) • S.shiftUC x)) :
    deriv (fun t : ℂ => S.Phi1C C (S.markedTangentC z (s : ℂ) t x)) 0 =
      (fun (s : ℝ) (x : S.E) => (fderiv ℂ (S.Phi1C C) ((s : ℂ) • S.shiftUC x))
        (S.maskUC z (S.shiftUC x))) s x :=
  (S.hasDerivAt_Phi1C_marked z C (s : ℂ) x hd).deriv

/-- The differentiability hypothesis of `hasDerivAt_Phi1C_marked` at the real ray points, from the
landed `ClassRegularLocC`. -/
theorem differentiableAt_Phi1C_of_classRegularLocC (hc : S.ClassRegularLocC C) {x : S.E}
    (hx : ‖x‖ ≤ S.p₁) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    DifferentiableAt ℂ (S.Phi1C C) ((s : ℂ) • S.shiftUC x) := by
  obtain ⟨O, hO, hcd, hmem⟩ := hc.phi1
  exact ((hcd.contDiffAt (hO.mem_nhds (hmem x hx s hs))).differentiableAt (by norm_num))

end Derivative

/-! ### T4: the cubic Taylor form of the zero-class potential -/

section Taylor

variable {eps : ℝ}

/-- **The potential at a general tangent is the functional `interactionOne`**: for the datum `θ`
of the chart and every complex field `w` of the unit lattice,
`V^{(k)}(ψ^{(k)} + w) = interactionOne (Θ, lift w)`, `Θ = rawOf θ`. -/
theorem VkC_psi0C_add_eq_interactionOne (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps S.D')
    (w : S.EC) :
    S.VkC (S.psi0C + w) = interactionOne S.hG S.hG' (le_refl (k + 1)) S.a₁ S.ν eps
      (rawOf S.D', liftC S.hG' w) := by
  have e : liftC S.hG' w = compTangent S.hG S.hG' (le_refl (k + 1)) S.a
      (bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D') S.D' (S.dataUC (S.psi0C + w)) := by
    rw [S.compTangent_dataUC]; congr 1; abel
  rw [e]
  exact (interactionOne_eq S.hG S.hG' (le_refl (k + 1)) hD
    (D := S.dataUC (S.psi0C + w)) (fun z i => by rw [S.dataUC_h, S.hh₀])).symm

variable (ha₁ : 0 < S.a₁) (H : BgHyp d L (k + 1) ϱ S.a S.ν)
  (hD2 : InUnionDomainC S.G' (bgC0 d L N) (thm73C2 d L N) S.ν S.D')

include ha₁ H hD2 in
/-- **`MARK-TAYLOR`: the cubic Taylor form of the potential at a general complex tangent.**
Let `v` be a complex field of the unit lattice whose complex segment `s ↦ ψ^{(k)} + s v`
has, for every `s ∈ [0,1]`, a complex neighbourhood in the domain `𝒟(𝔹_k)` (radius `bgC1`) of the
small solution (`MARK-REAL`).  Then, with `ω(s) = (1-s)²/2` (`taylorWeight`), `Θ = rawOf θ`,
`f = interactionOne`,
`V^{(k)}(ψ^{(k)} + v) = ∫₀¹ ω(s) D³f(Θ, s·lift v)[lift v, lift v, lift v] ds
  = raySrc3 f ω (lift v) (lift v) 1 Θ`:
`V^{(k)}` vanishes to second order at the critical point (`VkC_rayV_vanish_of_baseDomain`), for the
arbitrary direction `v`, not only for the directions `shiftUC ψ̂`. -/
theorem VkC_taylor_line (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps S.D') (v : S.EC)
    (hdom : ∀ s ∈ Icc (0 : ℝ) 1, ∀ᶠ ζ : ℂ in 𝓝 (s : ℂ),
      InUnionDomainC (stepG d L N₁ m₁ k ϱ) (bgC0 d L N) (bgC1 d L N) S.ν
        (S.dataUC (S.psiAtV ζ v))) :
    S.VkC (S.psi0C + v) = raySrc3 (interactionOne S.hG S.hG' (le_refl (k + 1)) S.a₁ S.ν eps)
      taylorWeight (liftC S.hG' v) (liftC S.hG' v) 1 (rawOf S.D') := by
  have hbase := S.baseDomainC_of_chart ha₁ H hD2
  have hray : ∀ t ∈ Icc (0 : ℝ) 1, ∀ᶠ s : ℝ in 𝓝 t,
      InUnionDomainC (stepG d L N₁ m₁ k ϱ) (bgC0 d L N) (bgC1 d L N) S.ν
        (S.dataUC (S.psiAtV ((s : ℝ) : ℂ) v)) :=
    fun t ht => (Complex.continuous_ofReal.tendsto t).eventually (hdom t ht)
  have hT := S.VkC_rayV_taylor_of_baseDomain ha₁ H hD2 hbase v hray (s := 1)
    ⟨zero_le_one, le_rfl⟩
  set G : ℂ → ℂ := fun ζ => S.VkC (S.psiAtV ζ v) with hG
  have hAn : ∀ t ∈ Icc (0 : ℝ) 1, AnalyticAt ℂ G (t : ℂ) := by
    intro t ht
    obtain ⟨Φ, hΦ, hΦe⟩ := S.exists_analyticAt_VkC_rayV ha₁ H hD2 v (z₀ := (t : ℂ))
      (hdom t ht).self_of_nhds
    refine hΦ.congr ?_
    filter_upwards [hdom t ht] with ζ hζ using (hΦe ζ hζ).symm
  have hlift : ∀ ζ : ℂ, liftC S.hG' (ζ • v) = ζ • liftC S.hG' v := fun ζ => map_smul _ _ _
  have hd3 : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 →
      dirS3 (interactionOne S.hG S.hG' (le_refl (k + 1)) S.a₁ S.ν eps) (liftC S.hG' v)
        (rawOf S.D') (((1 : ℂ) * (t : ℂ)) • liftC S.hG' v) =
        iteratedDeriv 3 (fun r : ℝ => S.VkC (S.psiAtV ((r : ℝ) : ℂ) v)) t := by
    intro t ht
    unfold dirS3
    have e : (fun τ : ℂ => interactionOne S.hG S.hG' (le_refl (k + 1)) S.a₁ S.ν eps
        (rawOf S.D', ((1 : ℂ) * (t : ℂ)) • liftC S.hG' v + τ • liftC S.hG' v)) =
        fun τ : ℂ => G ((t : ℂ) + τ) := by
      funext τ
      have h1 : ((1 : ℂ) * (t : ℂ)) • liftC S.hG' v + τ • liftC S.hG' v =
          liftC S.hG' (((t : ℂ) + τ) • v) := by
        rw [hlift, one_mul, add_smul]
      rw [h1, ← S.VkC_psi0C_add_eq_interactionOne hD]
      rfl
    rw [e]
    have h1 := congrFun (iteratedDeriv_comp_const_add 3 G (t : ℂ)) 0
    rw [h1, add_zero, ← iteratedDeriv_comp_ofReal 3 G t (hAn t ht)]
  have hrs : raySrc3 (interactionOne S.hG S.hG' (le_refl (k + 1)) S.a₁ S.ν eps) taylorWeight
      (liftC S.hG' v) (liftC S.hG' v) 1 (rawOf S.D') = ∫ t in (0 : ℝ)..1, taylorWeight (t : ℂ) *
        iteratedDeriv 3 (fun r : ℝ => S.VkC (S.psiAtV ((r : ℝ) : ℂ) v)) t := by
    unfold raySrc3
    rw [one_mul]
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le zero_le_one] at ht
    rw [hd3 t ht]
  rw [hrs]
  have e1 : S.psi0C + v = S.psiAtV ((1 : ℝ) : ℂ) v := by simp [psiAtV]
  rw [e1, hT]
  refine intervalIntegral.integral_congr fun u _ => ?_
  simp

end Taylor


/-! ### T4 (continued): the difference `Δ_z` of the zero-class exponent -/

section Difference

variable {eps : ℝ}

theorem Phi1C_zeroClass (y : S.EC) :
    S.Phi1C (zeroClass d L N₁ m₁ k N ϱ) y = -(S.β : ℂ) * S.VkC (S.psi0C + y) := by
  unfold Phi1C
  rw [dEC_zeroClass, add_zero]

variable (ha₁ : 0 < S.a₁) (H : BgHyp d L (k + 1) ϱ S.a S.ν)
  (hD2 : InUnionDomainC S.G' (bgC0 d L N) (thm73C2 d L N) S.ν S.D')

include ha₁ H hD2 in
/-- **`MARK-TAYLOR`, complex step: the cubic Taylor form of the marked difference** (formulas
(3)-(4) of the note, at the level of the combined potential).  For the zero class
`Φ₁ = -β V^{(k)}`, and tangents `v_t = u ψ' + t M_z ψ'`, `v_0 = u ψ'` whose complex segments have
complex neighbourhoods in the domain of the small solution (`MARK-REAL`),
`Δ_z(u,t) := Φ₁(v_t) - Φ₁(v_0) = -β (P(v_t) - P(v_0))`, with
`P(v) = raySrc3 f ω (lift v) (lift v) 1 Θ = ∫₀¹ ω(s) D³f(Θ, s·lift v)[lift v]³ ds`,
`f = interactionOne`, `ω(s) = (1-s)²/2`, `Θ = rawOf θ`. -/
theorem marked_difference_eq (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps S.D')
    (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))) (u t : ℂ) (x : S.E)
    (hdom : ∀ s ∈ Icc (0 : ℝ) 1, ∀ᶠ ζ : ℂ in 𝓝 (s : ℂ),
      InUnionDomainC (stepG d L N₁ m₁ k ϱ) (bgC0 d L N) (bgC1 d L N) S.ν
        (S.dataUC (S.psiAtV ζ (S.markedTangentC z u t x))))
    (hdom0 : ∀ s ∈ Icc (0 : ℝ) 1, ∀ᶠ ζ : ℂ in 𝓝 (s : ℂ),
      InUnionDomainC (stepG d L N₁ m₁ k ϱ) (bgC0 d L N) (bgC1 d L N) S.ν
        (S.dataUC (S.psiAtV ζ (S.markedTangentC z u 0 x)))) :
    S.Phi1C (zeroClass d L N₁ m₁ k N ϱ) (S.markedTangentC z u t x) -
        S.Phi1C (zeroClass d L N₁ m₁ k N ϱ) (S.markedTangentC z u 0 x) =
      -(S.β : ℂ) * (raySrc3 (interactionOne S.hG S.hG' (le_refl (k + 1)) S.a₁ S.ν eps)
          taylorWeight (liftC S.hG' (S.markedTangentC z u t x))
          (liftC S.hG' (S.markedTangentC z u t x)) 1 (rawOf S.D') -
        raySrc3 (interactionOne S.hG S.hG' (le_refl (k + 1)) S.a₁ S.ν eps) taylorWeight
          (liftC S.hG' (S.markedTangentC z u 0 x)) (liftC S.hG' (S.markedTangentC z u 0 x)) 1
          (rawOf S.D')) := by
  rw [S.Phi1C_zeroClass, S.Phi1C_zeroClass, S.VkC_taylor_line ha₁ H hD2 hD _ hdom,
    S.VkC_taylor_line ha₁ H hD2 hD _ hdom0]
  ring

end Difference

/-! ### The real chart -/

section RealChart

variable {S} {pp : ℝ}

/-- On the real chart, the complexification of the real marked tangent is the complex marked
tangent at real parameters. -/
theorem yhat_markedTangent {z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))} (x : S.E)
    (hsh : S.shiftUC x = yhat (S.shiftU x)) (u t : ℝ) :
    yhat (S.markedTangent z u t x) = S.markedTangentC z (u : ℂ) (t : ℂ) x := by
  unfold markedTangent markedTangentC
  rw [hsh, StepSetting.maskUC_yhat S z, S.yhat_add, yhat_smul, yhat_smul]

/-- **Real chart: the real exponent along the marked family is the complex one.**  Under
`RayData`, for the zero class, `Φ₁(v_t)` of the landed step equals `Φ₁(v_t)` of the complex step
at real parameters. -/
theorem Phi1_zeroClass_marked_eq_Phi1C (R : S.RayData pp)
    (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))) (u t : ℝ) (x : S.E) :
    S.Phi1 (zeroClass d L N₁ m₁ k N ϱ) (S.markedTangent z u t x) =
      S.Phi1C (zeroClass d L N₁ m₁ k N ϱ) (S.markedTangentC z (u : ℂ) (t : ℂ) x) := by
  have hχ := (chiU_eq_one_iff _ _ _ _).1 R.hχu
  have hsh : S.shiftUC x = yhat (S.shiftU x) :=
    S.shiftUC_eq R.H R.hδ'0 R.hδ' R.hD'R R.hδ0 hχ R.hfam R.hsm x
  rw [← yhat_markedTangent x hsh u t, Phi1_zeroClass, Phi1C_zeroClass,
    S.psi0C_eq R.ha₁ R.H R.hδ'0 R.hδ' R.hD'R, ← S.yhat_add, S.VkC_yhat]

end RealChart

end StepSetting

/-! ### T5: the marked block terms and the Cauchy estimate in `t` -/

section MarkedTerm

variable {Λ : Type*} [NormedAddCommGroup Λ] [NormedSpace ℂ Λ]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- **The marked term** of a block functional `Ev` along the family `w_t = a + t c`: the cubic
Taylor term `P(Θ, w_t) = ∫₀¹ ω(s) D³Ev(Θ, s w_t)[w_t, w_t, w_t] ds` (`rayTerm` of the third
directional derivative at `σ = 1` in the direction `w_t`). -/
noncomputable def markedBlockTerm (Ev : Λ × F → ℂ) (ω : ℂ → ℂ) (a c : F) (Θ : Λ) (t : ℂ) : ℂ :=
  rayTerm (dl3 Ev (a + t • c)) ω (a + t • c) 1 Θ

variable {S : Set Λ} {B : Set F} {Ev : Λ × F → ℂ} {ω : ℂ → ℂ} {a c : F} {Θ : Λ}
  {R₁ r t₁ : ℝ}

/-- The two-variable function `(σ, t) ↦ Ev(Θ, σ (a + t c))` is analytic on `‖t‖ < t₁`,
`‖σ‖ < R₁ + r`, when the whole disc of directions stays in the analytic region `S × B`. -/
theorem analyticAt_marked_H (hEv : AnalyticOnNhd ℂ Ev (S ×ˢ B)) (hΘ : Θ ∈ S)
    (hdom : ∀ t : ℂ, ‖t‖ < t₁ → ∀ σ : ℂ, ‖σ‖ < R₁ + r → σ • (a + t • c) ∈ B)
    {q : ℂ × ℂ} (hq2 : ‖q.2‖ < t₁) (hq1 : ‖q.1‖ < R₁ + r) :
    AnalyticAt ℂ (fun q : ℂ × ℂ => Ev (Θ, q.1 • (a + q.2 • c))) q := by
  have hm : AnalyticAt ℂ (fun q : ℂ × ℂ => ((Θ, q.1 • (a + q.2 • c)) : Λ × F)) q :=
    AnalyticAt.prod analyticAt_const (analyticAt_fst.smul
      (analyticAt_const.add (analyticAt_snd.smul analyticAt_const)))
  exact (hEv _ ⟨hΘ, hdom q.2 hq2 q.1 hq1⟩).comp_of_eq hm rfl

/-- Joint analyticity of the third `σ`-derivative of `Ev(Θ, σ (a + t c))` in `(σ, t)`: it is the
third directional derivative of `Ev` at `s w_t` in the direction `w_t`. -/
theorem dirL3_marked_eq (hr : 0 < r) (hEv : AnalyticOnNhd ℂ Ev (S ×ˢ B)) (hΘ : Θ ∈ S)
    (hdom : ∀ t : ℂ, ‖t‖ < t₁ → ∀ σ : ℂ, ‖σ‖ < R₁ + r → σ • (a + t • c) ∈ B)
    {s t : ℂ} (hs : ‖s‖ < R₁) (ht : ‖t‖ < t₁) :
    dirL3 Ev (a + t • c) Θ (s • (a + t • c)) =
      (lineD ((1 : ℂ), (0 : ℂ)))^[3] (fun q : ℂ × ℂ => Ev (Θ, q.1 • (a + q.2 • c))) (s, t) := by
  have hH : ∀ q : ℂ × ℂ, ‖q.2‖ < t₁ → ‖q.1‖ < R₁ + r →
      AnalyticAt ℂ (fun q : ℂ × ℂ => Ev (Θ, q.1 • (a + q.2 • c))) q := fun q hq2 hq1 =>
    analyticAt_marked_H hEv hΘ hdom hq2 hq1
  have hr' : ∀ τ : ℂ, ‖τ‖ < r → ‖s + τ‖ < R₁ + r := fun τ hτ =>
    (norm_add_le _ _).trans_lt (add_lt_add hs hτ)
  have hf : ∀ τ : ℂ, ‖τ‖ < r →
      AnalyticAt ℂ Ev (Θ, s • (a + t • c) + τ • (a + t • c)) := fun τ hτ => by
    rw [← add_smul]
    exact hEv _ ⟨hΘ, hdom t ht _ (hr' τ hτ)⟩
  rw [dirL3_eq hr hf]
  unfold dirS3
  have e : (fun τ : ℂ => Ev (Θ, s • (a + t • c) + τ • (a + t • c))) =
      fun τ : ℂ => (fun q : ℂ × ℂ => Ev (Θ, q.1 • (a + q.2 • c))) ((s, t) + τ • ((1 : ℂ), (0 : ℂ))) := by
    funext τ
    have h2 : ((s, t) + τ • ((1 : ℂ), (0 : ℂ)) : ℂ × ℂ) = (s + τ, t) := by ext <;> simp
    rw [h2]
    show Ev (Θ, s • (a + t • c) + τ • (a + t • c)) = Ev (Θ, (s + τ) • (a + t • c))
    rw [add_smul]
  rw [e]
  have := iteratedDeriv_line (E := ℂ × ℂ) (s, t) ((1 : ℂ), (0 : ℂ)) (r := r) 3
    (fun q : ℂ × ℂ => Ev (Θ, q.1 • (a + q.2 • c))) (fun τ hτ => hH _ (by simpa using ht)
      (by simpa using hr' τ hτ)) 0 (by simpa using hr)
  simpa using this

/-- **The marked term is analytic in `t`** on `‖t‖ < t₁`, when the discs `σ · w_t`, `‖σ‖ < R₁ + r`,
`‖t‖ < t₁`, lie in the analytic region of `Ev` (formula (2) of the note) and the weight `ω` is
analytic on `‖σ‖ < R₁`, `R₁ > 1`. -/
theorem analyticOnNhd_markedBlockTerm (hR₁ : 1 < R₁) (hr : 0 < r)
    (hω : AnalyticOnNhd ℂ ω (Metric.ball (0 : ℂ) R₁)) (hEv : AnalyticOnNhd ℂ Ev (S ×ˢ B))
    (hΘ : Θ ∈ S) (hdom : ∀ t : ℂ, ‖t‖ < t₁ → ∀ σ : ℂ, ‖σ‖ < R₁ + r → σ • (a + t • c) ∈ B) :
    AnalyticOnNhd ℂ (markedBlockTerm Ev ω a c Θ) (Metric.ball (0 : ℂ) t₁) := by
  set H : ℂ × ℂ → ℂ := fun q => Ev (Θ, q.1 • (a + q.2 • c)) with hHdef
  have hK : ∀ q : ℂ × ℂ, ‖q.1‖ < R₁ + r → ‖q.2‖ < t₁ →
      AnalyticAt ℂ ((lineD ((1 : ℂ), (0 : ℂ)))^[3] H) q := by
    intro q h1 h2
    exact analyticAt_lineD _ (analyticAt_lineD _ (analyticAt_lineD _
      (analyticAt_marked_H hEv hΘ hdom h2 h1)))
  have hint : AnalyticOnNhd ℂ (fun t : ℂ => ∫ s in (0 : ℝ)..1,
      ω (s : ℂ) * ((lineD ((1 : ℂ), (0 : ℂ)))^[3] H) ((s : ℂ), t)) (Metric.ball (0 : ℂ) t₁) := by
    refine analyticOnNhd_unitIntegral (f := fun (t s : ℂ) =>
      ω s * ((lineD ((1 : ℂ), (0 : ℂ)))^[3] H) (s, t)) hR₁ ?_
    rintro ⟨t, s⟩ ⟨ht, hs⟩
    have ht' : ‖t‖ < t₁ := mem_ball_zero_iff.1 ht
    have hs' : ‖s‖ < R₁ := mem_ball_zero_iff.1 hs
    have hm : AnalyticAt ℂ (fun p : ℂ × ℂ => (p.2, p.1)) (t, s) :=
      analyticAt_snd.prod analyticAt_fst
    exact ((hω s hs).comp (analyticAt_snd (𝕜 := ℂ))).mul
      ((hK (s, t) (by simp only; linarith) ht').comp_of_eq hm rfl)
  refine hint.congr Metric.isOpen_ball fun t ht => ?_
  have ht' : ‖t‖ < t₁ := mem_ball_zero_iff.1 ht
  unfold markedBlockTerm rayTerm
  rw [one_mul]
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [Set.uIcc_of_le zero_le_one] at hs
  have hs' : ‖(s : ℂ)‖ < R₁ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs.1]; linarith [hs.2]
  rw [dl3_apply, one_mul, dirL3_marked_eq hr hEv hΘ hdom hs' ht']

/-- **Bound for the marked term** by the Cauchy estimate for the third derivative
(`norm_dirL3_le`): if `|Ev| ≤ b` on `S × B`, `|ω| ≤ Mω` on `[0,1]`, then
`|P(Θ, w_t)| ≤ Mω · 6 b / r³` for `‖t‖ < t₁`. -/
theorem norm_markedBlockTerm_le (hR₁ : 1 < R₁) (hr : 0 < r) (hEv : AnalyticOnNhd ℂ Ev (S ×ˢ B))
    (hΘ : Θ ∈ S) (hdom : ∀ t : ℂ, ‖t‖ < t₁ → ∀ σ : ℂ, ‖σ‖ < R₁ + r → σ • (a + t • c) ∈ B)
    {b Mω : ℝ} (hMω : 0 ≤ Mω) (hωb : ∀ s : ℝ, s ∈ Icc (0 : ℝ) 1 → ‖ω (s : ℂ)‖ ≤ Mω)
    (hb : ∀ u ∈ S ×ˢ B, ‖Ev u‖ ≤ b) {t : ℂ} (ht : ‖t‖ < t₁) :
    ‖markedBlockTerm Ev ω a c Θ t‖ ≤ Mω * (6 * b / r ^ 3) := by
  unfold markedBlockTerm
  have hmem : ∀ s : ℝ, s ∈ Icc (0 : ℝ) 1 → ∀ τ : ℂ, ‖τ‖ ≤ r →
      ((1 : ℂ) * (s : ℂ)) • (a + t • c) + τ • (a + t • c) ∈ B := by
    intro s hs τ hτ
    rw [← add_smul]
    refine hdom t ht _ ?_
    have h1 : ‖(1 : ℂ) * (s : ℂ) + τ‖ ≤ 1 + r := by
      refine (norm_add_le _ _).trans (add_le_add ?_ hτ)
      rw [one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs.1]; exact hs.2
    linarith
  have := norm_rayTerm_le (g := dl3 Ev (a + t • c)) (x₀ := a + t • c) (b := 6 * b / r ^ 3)
    (Θ := Θ) (σ := 1) hMω hωb (fun s hs => ?_)
  · simpa using this
  · rw [dl3_apply]
    exact norm_dirL3_le hr (fun τ hτ => hEv _ ⟨hΘ, hmem s hs τ hτ⟩)
      (fun τ hτ => hb _ ⟨hΘ, hmem s hs τ hτ⟩)

/-- **The Cauchy estimate in `t` for the marked term** (formula (5) of the note, per block term):
`|∂_t P(Θ, w_t)|_{t=0}| ≤ Mω · 6 b / (r³ t₀)` for `0 < t₀ < t₁`.  The constant term `P(Θ, w_0)`
has zero `t`-derivative, so the difference `P(w_t) - P(w_0)` of the note has the same derivative
and no factor `2` is needed. -/
theorem norm_deriv_markedBlockTerm_le (hR₁ : 1 < R₁) (hr : 0 < r)
    (hω : AnalyticOnNhd ℂ ω (Metric.ball (0 : ℂ) R₁)) (hEv : AnalyticOnNhd ℂ Ev (S ×ˢ B))
    (hΘ : Θ ∈ S) (hdom : ∀ t : ℂ, ‖t‖ < t₁ → ∀ σ : ℂ, ‖σ‖ < R₁ + r → σ • (a + t • c) ∈ B)
    {b Mω t₀ : ℝ} (hMω : 0 ≤ Mω) (hωb : ∀ s : ℝ, s ∈ Icc (0 : ℝ) 1 → ‖ω (s : ℂ)‖ ≤ Mω)
    (hb : ∀ u ∈ S ×ˢ B, ‖Ev u‖ ≤ b) (ht₀ : 0 < t₀) (ht₀₁ : t₀ < t₁) :
    ‖deriv (markedBlockTerm Ev ω a c Θ) 0‖ ≤ Mω * (6 * b / r ^ 3) / t₀ := by
  have han := analyticOnNhd_markedBlockTerm hR₁ hr hω hEv hΘ hdom
  have hcl : DiffContOnCl ℂ (markedBlockTerm Ev ω a c Θ) (Metric.ball (0 : ℂ) t₀) := by
    refine DifferentiableOn.diffContOnCl ?_
    rw [closure_ball _ ht₀.ne']
    intro t ht
    have : t ∈ Metric.ball (0 : ℂ) t₁ := by
      rw [mem_ball_zero_iff]
      exact lt_of_le_of_lt (mem_closedBall_zero_iff.1 ht) ht₀₁
    exact (han t this).differentiableAt.differentiableWithinAt
  refine Complex.norm_deriv_le_of_forall_mem_sphere_norm_le ht₀ hcl (fun t ht => ?_)
  refine norm_markedBlockTerm_le hR₁ hr hEv hΘ hdom hMω hωb hb ?_
  rw [mem_sphere_zero_iff_norm.1 ht]; exact ht₀₁

/-- **The marked term of the Taylor weight**: `ω(s) = (1-s)²/2` (`taylorWeight`), `Mω = 1/2`,
so the bound is `3 b / r³` and the Cauchy bound `3 b / (r³ t₀)`. -/
theorem norm_deriv_markedBlockTerm_taylorWeight_le {R₁ r t₁ : ℝ} (hR₁ : 1 < R₁) (hr : 0 < r)
    (hEv : AnalyticOnNhd ℂ Ev (S ×ˢ B)) (hΘ : Θ ∈ S)
    (hdom : ∀ t : ℂ, ‖t‖ < t₁ → ∀ σ : ℂ, ‖σ‖ < R₁ + r → σ • (a + t • c) ∈ B)
    {b t₀ : ℝ} (hb : ∀ u ∈ S ×ˢ B, ‖Ev u‖ ≤ b) (ht₀ : 0 < t₀) (ht₀₁ : t₀ < t₁) :
    ‖deriv (markedBlockTerm Ev taylorWeight a c Θ) 0‖ ≤ 3 * b / (r ^ 3 * t₀) := by
  have := norm_deriv_markedBlockTerm_le hR₁ hr (analyticOnNhd_taylorWeight _) hEv hΘ hdom
    (Mω := 1 / 2) (by norm_num) (fun s hs => norm_taylorWeight_le s hs) hb ht₀ ht₀₁
  refine this.trans (le_of_eq ?_)
  field_simp
  ring

end MarkedTerm

/-! ### T5: the block terms of the marked tangent of the step -/

namespace StepSetting

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱm : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))))

/-- The marked term along the lifted marked tangent: the family `a + t c` of `markedBlockTerm` is the
fine-lattice lift of the marked tangent `v_t = u ψ' + t M_z ψ'`. -/
theorem markedBlockTerm_marked_eq (Ev : RawData d L (N₁ * L ^ m₁) (k + 1) N ×
      (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ) (ω : ℂ → ℂ)
    (Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N) (u t : ℂ) (x : S.E) :
    markedBlockTerm Ev ω (liftC S.hG' (u • S.shiftUC x)) (liftC S.hG' (S.maskUC z (S.shiftUC x))) Θ t =
      rayTerm (dl3 Ev (liftC S.hG' (S.markedTangentC z u t x))) ω
        (liftC S.hG' (S.markedTangentC z u t x)) 1 Θ := by
  unfold markedBlockTerm
  rw [S.liftC_markedTangentC, map_smul]

/-- **T5 for one block term of a given expansion**: let `Ev` be analytic on
`S' × FlBall Hm δ₁` and bounded by `b` there (the properties of the terms of
`vblock_expansion_scaled`), `Θ ∈ S'`, and let the unit-lattice field `y = shiftUC ψ̂` have
Euclidean norm at most `Y ≥ 0` at the unit points, with the radius condition of formula (2),
`(R₁ + r)(|u| + t₁) Y < δ₁`, `1 < R₁`.  Then the marked term
`t ↦ P(Θ, v_t) = ∫₀¹ ω(s) D³Ev(Θ, s v_t)[v_t]³ ds` is analytic on `|t| < t₁`, and for
`0 < t₀ < t₁` its `t`-derivative at `0` is at most `3 b / (r³ t₀)`. -/
theorem marked_term_cauchy {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm} (hG : IsLevel Hm k)
    {δ₁ Y R₁ r t₁ t₀ b : ℝ} (hY0 : 0 ≤ Y) {x : S.E} {u : ℂ}
    (hY : ∀ q : S.U, vn (fun i => S.shiftUC x (q, i)) ≤ Y)
    (hrad : (R₁ + r) * (‖u‖ + t₁) * Y < δ₁) (hR₁ : 1 < R₁) (hr : 0 < r) (ht₀ : 0 < t₀)
    (ht₀₁ : t₀ < t₁) {S' : Set (RawData d L (N₁ * L ^ m₁) (k + 1) N)}
    {Ev : RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ}
    (hEv : AnalyticOnNhd ℂ Ev (S' ×ˢ FlBall Hm δ₁)) (hb : ∀ w ∈ S' ×ˢ FlBall Hm δ₁, ‖Ev w‖ ≤ b)
    {Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N} (hΘ : Θ ∈ S') :
    AnalyticOnNhd ℂ (fun t : ℂ => rayTerm (dl3 Ev (liftC S.hG' (S.markedTangentC z u t x)))
        taylorWeight (liftC S.hG' (S.markedTangentC z u t x)) 1 Θ) (Metric.ball (0 : ℂ) t₁) ∧
      ‖deriv (fun t : ℂ => rayTerm (dl3 Ev (liftC S.hG' (S.markedTangentC z u t x)))
        taylorWeight (liftC S.hG' (S.markedTangentC z u t x)) 1 Θ) 0‖ ≤ 3 * b / (r ^ 3 * t₀) := by
  have hdom : ∀ t : ℂ, ‖t‖ < t₁ → ∀ σ : ℂ, ‖σ‖ < R₁ + r →
      σ • (liftC S.hG' (u • S.shiftUC x) + t • liftC S.hG' (S.maskUC z (S.shiftUC x))) ∈
        FlBall Hm δ₁ := fun t ht σ hσ => S.markedDisc_hdom hG hY0 hY hrad ht hσ
  have e : (fun t : ℂ => rayTerm (dl3 Ev (liftC S.hG' (S.markedTangentC z u t x)))
        taylorWeight (liftC S.hG' (S.markedTangentC z u t x)) 1 Θ) =
      markedBlockTerm Ev taylorWeight (liftC S.hG' (u • S.shiftUC x))
        (liftC S.hG' (S.maskUC z (S.shiftUC x))) Θ := by
    funext t; exact (S.markedBlockTerm_marked_eq z Ev taylorWeight Θ u t x).symm
  rw [e]
  exact ⟨analyticOnNhd_markedBlockTerm hR₁ hr (analyticOnNhd_taylorWeight _) hEv hΘ hdom,
    norm_deriv_markedBlockTerm_taylorWeight_le hR₁ hr hEv hΘ hdom hb ht₀ ht₀₁⟩

section VBlock

open Balaban.Multiscale

variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ eps : ℝ} {X₁f : Finset (CTorus d L N₁ m₁ (k + 1))} {j : ℕ}
variable {Kc Cx c₂ BG₂ δ₁ : ℝ} {m₀ : ℕ} {X 𝒦X : Set (CTorus d L N₁ m₁ (k + 1))}

/-- **T5: the landed block expansion accepts the marked tangent, and the marked terms obey the
Cauchy estimate.**  The hypotheses are those of `vblock_expansion_scaled` for the block `zb` (the
step has `Gp = S.G'` of level `k+1`, `K = k+1`, `n = k`).  Its terms `E_{b,Y}` are analytic on
`XiCRaw × FlBall Hm δ₁` and bounded there by `E* e^{-2 κ_dec d(Y)}`,
`E* = energyBdScaled` (`vblock_expansion_scaled`); the expansion is valid for every tangent of the
ball, in particular for the marked tangent.  Consequently, for every label `Y`, every datum
`Θ ∈ XiCRaw`, and every field `y = shiftUC ψ̂` of Euclidean norm at most `Y₀` at the unit points
with `(R₁ + r)(|u| + t₁) Y₀ < δ₁`, the marked term
`t ↦ P_{b,Y}(Θ, v_t) = ∫₀¹ ω(s) D³E_{b,Y}(Θ, s v_t)[v_t]³ ds` is analytic on `|t| < t₁`, and for
`0 < t₀ < t₁`
`|∂_t P_{b,Y}(Θ, v_t)|_{t=0}| ≤ 3 E* e^{-2 κ_dec d(Y)} / (r³ t₀)`. -/
theorem marked_vblock_term_cauchy
    (hC : FlCore N S.G' Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hcov : CovSetup S.G' m₀ j X 𝒦X)
    (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) = X1 S.G' m₀ j 𝒦X)
    (hconn : HatConn S.G') (hrow : RowInHat (coverOf S.G') Hm (compWeight L a₁) ν)
    (hopt : ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X) ∧ MeetsOne m₀ j 𝒦X W₀ ∧
        bondCost (scaleW L m₀ m₁ j) E₀ = treeLenCovOne m₀ j X)
    (hΔ : treeLenCovOne m₀ j X = 0)
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hHm : IsLevel Hm k) (zb : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))))
    (hZ : readSites Hm k zb ⊆ ↑X₁f)
    (hmar : BlockMargin S.G' X₁f (↑(blockSites d L N₁ m₁ (k + 1) k zb) :
      Set (CTorus d L N₁ m₁ (k + 1)))) :
    ∃ Ev : Set (CTorus d L N₁ m₁ (k + 1)) →
        RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ,
      (∀ D : BgData S.G' N, XiCData S.G' (compWeight L a₁) ν (k + 1) 1 eps D →
        ∀ ψ' ∈ FlBall Hm δ₁,
        energyBlock S.G' Hm (compWeight L a₁) ν k (bgMultC S.G' (compWeight L a₁) ν (bgC0 d L N) D)
          (flFieldOne S.G' Hm BG₂ κ a₁ ν D ψ') ψ' zb =
        ∑ Y ∈ polymerDomains (fun i : ParIdx S.G' (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) =>
          i.1.1) S.G' m₀ (X1 S.G' m₀ j 𝒦X), Ev Y (rawOf D, ψ')) ∧
      ∀ Y, ∀ {Y₀ R₁ r t₁ t₀ : ℝ}, 0 ≤ Y₀ → ∀ {x : S.E} {u : ℂ},
        (∀ q : S.U, vn (fun i => S.shiftUC x (q, i)) ≤ Y₀) →
        (R₁ + r) * (‖u‖ + t₁) * Y₀ < δ₁ → 1 < R₁ → 0 < r → 0 < t₀ → t₀ < t₁ →
        ∀ {Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N},
          Θ ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps →
        AnalyticOnNhd ℂ (fun t : ℂ => rayTerm (dl3 (Ev Y)
            (liftC S.hG' (S.markedTangentC z u t x))) taylorWeight
            (liftC S.hG' (S.markedTangentC z u t x)) 1 Θ) (Metric.ball (0 : ℂ) t₁) ∧
        ‖deriv (fun t : ℂ => rayTerm (dl3 (Ev Y) (liftC S.hG' (S.markedTangentC z u t x)))
            taylorWeight (liftC S.hG' (S.markedTangentC z u t x)) 1 Θ) 0‖ ≤
          3 * (energyBdScaled d L N (compWeight L a₁) k
            (cK2' d L N (famConst d L BG₂ κ) * δ₁) δ₁ (rho4 d L N BG κ) *
            Real.exp (-2 * κdec * treeLenCov S.G' m₀ Y)) / (r ^ 3 * t₀) := by
  obtain ⟨Ev, hsum, -, hbd, han⟩ := vblock_expansion_scaled hC hcov hX₁ hconn hrow hopt hΔ hκ₀
    hκdec hκ h1 hlog S.hk1 le_rfl hHm S.hG' zb hZ hmar
  refine ⟨Ev, hsum, fun Y Y₀ R₁ r t₁ t₀ hY0 x u hY hrad hR₁ hr ht₀ ht₀₁ Θ hΘ => ?_⟩
  exact S.marked_term_cauchy z hHm hY0 hY hrad hR₁ hr ht₀ ht₀₁ (han Y)
    (fun w hw => hbd Y w hw) hΘ

end VBlock

section BlockSum

open Balaban.Multiscale

variable {c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ}

/-- **`MARK-TAYLOR`, equality (4) of the note at the level of labels.**  Let, for every block `zb`,
`E_{zb,Y}` (`Ev zb Y`, `Y ∈ 𝒴 zb`) be analytic terms of the block energy on
`XiCRaw × FlBall`, summing to `blockEnergyOne` there (the output of `vblock_expansion_scaled`).
Let `v` be a complex field of the unit lattice whose segment lies in the domain of the small
solution (`MARK-REAL`) and whose lift `v` has all discs `s·lift v + τ·lift v`, `s ∈ [0,1]`,
`|τ| ≤ r`, in `FlBall` (formula (2)), and let the hypotheses of `dirS3_interactionOne` hold.
Then the potential at the tangent is the sum, over blocks and labels, of the cubic terms:
`V^{(k)}(ψ^{(k)} + v) = ∑_{zb} ∑_{Y ∈ 𝒴 zb} ∫₀¹ ω(s) D³E_{zb,Y}(Θ, s·lift v)[lift v]³ ds`.
Applied to `v_t` and `v_0` this gives `Δ_z = ∑ R_{z;b,Y}`,
`R_{z;b,Y} = -β (P_{b,Y}(v_t) - P_{b,Y}(v_0))`, via `Phi1C_zeroClass`. -/
theorem VkC_marked_eq_block_terms (ha₁ : 0 < S.a₁) (H : BgHyp d L (k + 1) ϱ S.a S.ν)
    (hD2 : InUnionDomainC S.G' (bgC0 d L N) (thm73C2 d L N) S.ν S.D')
    (hC : FlCore N S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hc7 : c7 d L N BG κ ≤ thm73C3 d L N) {R : ℝ} (hR : 2 ≤ R) (hRs : R * δ₁ ≤ deltaStar d L N)
    (hsmall : cK2 d L N * (R * δ₁) < bgC0 d L N / 2)
    (hnum : cK2 d L N * δ₁ ≤ c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hnum' : cK2' d L N (famConst d L BG₂ κ) * δ₁ ≤
      c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps S.D')
    (hreal : ∀ ψ' ∈ FlBall (stepG d L N₁ m₁ k ϱ) δ₁, IsLayerConstant (stepG d L N₁ m₁ k ϱ) ψ' →
      ∃ D : BgData (stepG d L N₁ m₁ k ϱ) N, (∀ x i, D.h x i = S.D'.h x i) ∧
      compTangent S.hG S.hG' (le_refl (k + 1)) S.a
        (bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D') S.D' D = ψ' ∧
      ∀ t : ℂ, ‖t‖ < R → InUnionDomainC (stepG d L N₁ m₁ k ϱ) (bgC0 d L N) (bgC1 d L N) S.ν
        ((composeData (S.hG.precedes S.hG' (le_refl (k + 1))) S.a
          (bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D') S.D').lineAt
          (tangentData D (composeData (S.hG.precedes S.hG' (le_refl (k + 1))) S.a
            (bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D') S.D')) t))
    (𝒴 : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Finset (Set (CTorus d L N₁ m₁ (k + 1))))
    (Ev : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Set (CTorus d L N₁ m₁ (k + 1)) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ)
    (han : ∀ zb Y, AnalyticOnNhd ℂ (Ev zb Y)
      (XiCRaw S.G' S.a S.ν (k + 1) 1 eps ×ˢ FlBall (stepG d L N₁ m₁ k ϱ) δ₁))
    (hsum : ∀ zb, ∀ Θ ∈ XiCRaw S.G' S.a S.ν (k + 1) 1 eps,
      ∀ ψ' ∈ FlBall (stepG d L N₁ m₁ k ϱ) δ₁,
      blockEnergyOne S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν BG₂ κ eps k zb (Θ, ψ') =
        ∑ Y ∈ 𝒴 zb, Ev zb Y (Θ, ψ'))
    (v : S.EC)
    (hdom : ∀ s ∈ Icc (0 : ℝ) 1, ∀ᶠ ζ : ℂ in 𝓝 (s : ℂ),
      InUnionDomainC (stepG d L N₁ m₁ k ϱ) (bgC0 d L N) (bgC1 d L N) S.ν
        (S.dataUC (S.psiAtV ζ v)))
    {r : ℝ} (hr : 0 < r)
    (hline : ∀ t ∈ Icc (0 : ℝ) 1, ∀ τ : ℂ, ‖τ‖ ≤ r →
      ((1 : ℂ) * (t : ℂ)) • liftC S.hG' v + τ • liftC S.hG' v ∈
        FlBall (stepG d L N₁ m₁ k ϱ) δ₁) :
    S.VkC (S.psi0C + v) = ∑ zb, ∑ Y ∈ 𝒴 zb, rayTerm (dl3 (Ev zb Y) (liftC S.hG' v)) taylorWeight
      (liftC S.hG' v) 1 (rawOf S.D') := by
  classical
  have hLC : IsLayerConstant (stepG d L N₁ m₁ k ϱ) (liftC S.hG' v) :=
    isLayerConstant_liftC S.hG S.hG' v
  have hΘ : rawOf S.D' ∈ XiCRaw S.G' S.a S.ν (k + 1) 1 eps := ⟨S.D', hD, rfl⟩
  have hblk : ∀ zb, raySrc3 (blockEnergyOne S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν BG₂ κ eps k zb)
      taylorWeight (liftC S.hG' v) (liftC S.hG' v) 1 (rawOf S.D') =
      ∑ Y ∈ 𝒴 zb, rayTerm (dl3 (Ev zb Y) (liftC S.hG' v)) taylorWeight (liftC S.hG' v) 1
        (rawOf S.D') := fun zb =>
    raySrc3_sum (𝒴 zb) (han zb) (hsum zb) continuous_taylorWeight hΘ hr hline
  have hint : ∀ zb, IntervalIntegrable (fun t : ℝ => taylorWeight (t : ℂ) *
      dirS3 (blockEnergyOne S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν BG₂ κ eps k zb) (liftC S.hG' v)
        (rawOf S.D') (((1 : ℂ) * (t : ℂ)) • liftC S.hG' v)) MeasureTheory.volume 0 1 :=
    fun zb => raySrc3_intervalIntegrable (𝒴 zb) (han zb) (hsum zb) continuous_taylorWeight hΘ hr
      hline
  rw [S.VkC_taylor_line ha₁ H hD2 hD v hdom]
  simp_rw [← hblk]
  unfold raySrc3
  rw [← Finset.mul_sum, ← intervalIntegral.integral_finsetSum (fun zb _ => hint zb)]
  congr 1
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [Set.uIcc_of_le zero_le_one] at ht
  rw [← Finset.mul_sum]
  congr 1
  refine dirS3_interactionOne hC S.hG S.hG' (le_refl (k + 1)) ha₁ H hc7 hR hRs hsmall hnum hnum' hD
    hreal (isLayerConstant_smul hLC _) hLC hr (fun τ hτ => hline t ht τ hτ.le) ?_
  intro zb
  exact contDiffAt_line_of_sum (S := XiCRaw S.G' S.a S.ν (k + 1) 1 eps)
    (B := FlBall (stepG d L N₁ m₁ k ϱ) δ₁) (𝒴 zb) (han zb) (hsum zb) hΘ hr
    (fun τ hτ => hline t ht τ hτ)

end BlockSum

end StepSetting

end Balaban.Fluctuation

/-! ### T6: non-vacuity at the landed witness step -/

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Set

/-- **Non-vacuity of `MARK-RADIUS` and of the exact derivative at the landed witness step.**  At
the witness step `hatStep m₁ β p₁ δ` (`d = L = 3`, `N = 2`, `k = 1`, `p₁ = pLog 1 2 β`, the radii
`towerCpsi`, `towerR = c_ψ/(2 p₁) - 4` of `StepActivityDirectScaledWitness` / `DAPhysicalRadii`,
`R₁ = R_σ = 2`) there are `t₀ < t₁` with `t₀ > 0` for which the radius condition (2) holds,
`(R₁ + r)(R_σ + t₁) · Y < δ₁`, with `Y = √N · |c_c| · covSupConstC · p₁` the hat-field bound for
`‖ψ̂‖ ≤ p₁` and `δ₁ = t`; the step has `RayData` (so the landed regularity holds), and the
exact identity of `MARK-REAL` holds at every mark `z`, every `‖ψ̂‖ ≤ p₁` and every `u ∈ [0,1]`:
`d/ds Φ₁(v_s)|_{s=0} = DΦ₁(u ψ')[1_{B(z)} ψ']`, the integrand of `E1Marks`. -/
theorem marked_radius_and_derivative_at_witness :
    ∃ (m₁ : ℕ) (κ t δ β t₀ : ℝ), 2 ≤ β ∧ 0 < t ∧ 0 < t₀ ∧
      (∃ t₁ : ℝ, t₀ < t₁ ∧
        (2 + towerR κ t β (pLog 1 2 β)) * (2 + t₁) *
          (Real.sqrt ((2 : ℕ) : ℝ) *
            (‖(((hatStep m₁ β (pLog 1 2 β) δ).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ *
              (covSupConstC 3 3 2 (compWeight 3 (1 : ℝ) 1) κ * pLog 1 2 β))) < t) ∧
      Nonempty ((hatStep m₁ β (pLog 1 2 β) δ).RayData (2 * pLog 1 2 β)) ∧
      ∀ (z : Torus 3 (9 * 3 ^ m₁ * 3 ^ (1 + 1 - (1 + 1)))) (x : (hatStep m₁ β (pLog 1 2 β) δ).E),
        ‖x‖ ≤ pLog 1 2 β → ∀ u ∈ Icc (0 : ℝ) 1,
        HasDerivAt (fun s : ℝ => (hatStep m₁ β (pLog 1 2 β) δ).Phi1
            (zeroClass 3 3 9 m₁ 1 2 (rhoSep m₁))
            ((hatStep m₁ β (pLog 1 2 β) δ).markedTangent z u s x))
          ((fderiv ℝ ((hatStep m₁ β (pLog 1 2 β) δ).Phi1 (zeroClass 3 3 9 m₁ 1 2 (rhoSep m₁)))
              (u • (hatStep m₁ β (pLog 1 2 β) δ).shiftU x))
            ((hatStep m₁ β (pLog 1 2 β) δ).maskU z ((hatStep m₁ β (pLog 1 2 β) δ).shiftU x))) 0 := by
  obtain ⟨-, δ, δ', T, -, -, hδ, hsm, hδ'0, hδ'a, hδ'b, hδ'c, hT, -, hT1, hT2⟩ :=
    exists_witness_params (fun _ => 0)
  obtain ⟨m₁, c, BG, κ, t, c₂, BG₂, κdec, κ0, δc, h4, ht0, -, hκ0, hκdec, hκ, -, -, -, hMX, -⟩ :=
    tower_core_fixed 2
  have hbig : cstarX 3 3 ≤ (3 : ℝ) ^ m₁ := by
    have hκdec0 : 0 ≤ κdec := by linarith
    have hκ_nn : 0 ≤ κ := le_trans (by positivity) hκ
    have h := Localization.cstarX_pos 3 3
    have h2 : cstarX 3 3 ≤ cstarX 3 3 * Real.exp ((N0 3 3 : ℝ) * κ) :=
      le_mul_of_one_le_right h.le (Real.one_le_exp (by positivity))
    have h3 : ((3 : ℕ) : ℝ) ^ m₁ = (3 : ℝ) ^ m₁ := by norm_num
    linarith
  obtain ⟨β₀, hβ₀, hitems⟩ := tower_C_items (A₁ := 1) one_pos 2 m₁ h4 hbig κ ht0 hδ hsm hδ'0 hδ'a
    hδ'b hδ'c
  obtain ⟨hp, hcψ, hr, hδ₁, hc, hlt, ⟨R0⟩⟩ := hitems β₀ le_rfl
  set p₁ := pLog 1 2 β₀ with hp₁def
  set cψ := towerCpsi κ t β₀ with hcψdef
  set W : ℝ := Real.sqrt ((2 : ℕ) : ℝ) *
    (‖(((hatStep m₁ β₀ p₁ δ).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ *
      covSupConstC 3 3 2 (compWeight 3 (1 : ℝ) 1) κ) with hW
  have hWc : W * cψ < t := by rw [hW]; nlinarith [hδ₁]
  set t₁ : ℝ := 8 * p₁ / cψ with ht₁
  have ht₁0 : 0 < t₁ := by positivity
  refine ⟨m₁, κ, t, δ, β₀, t₁ / 2, hβ₀, ht0, by positivity, ⟨t₁, by linarith, ?_⟩, ⟨R0⟩, ?_⟩
  · have hmain : (2 + towerR κ t β₀ p₁) * (2 + t₁) * p₁ ≤ cψ := by
      have e : (2 + towerR κ t β₀ p₁) * (2 + t₁) * p₁ = cψ - 16 * p₁ ^ 2 / cψ := by
        unfold towerR
        rw [ht₁]
        field_simp
        ring
      rw [e]
      have : 0 ≤ 16 * p₁ ^ 2 / cψ := by positivity
      linarith
    have e2 : (2 + towerR κ t β₀ p₁) * (2 + t₁) *
        (Real.sqrt ((2 : ℕ) : ℝ) * (‖(((hatStep m₁ β₀ p₁ δ).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ *
          (covSupConstC 3 3 2 (compWeight 3 (1 : ℝ) 1) κ * p₁))) =
        ((2 + towerR κ t β₀ p₁) * (2 + t₁) * p₁) * W := by
      rw [hW]; ring
    rw [e2]
    by_cases hW0 : 0 ≤ W
    · calc ((2 + towerR κ t β₀ p₁) * (2 + t₁) * p₁) * W ≤ cψ * W :=
            mul_le_mul_of_nonneg_right hmain hW0
        _ = W * cψ := by ring
        _ < t := hWc
    · have hneg : W < 0 := not_le.1 hW0
      have hpos : 0 ≤ (2 + towerR κ t β₀ p₁) * (2 + t₁) * p₁ := by
        have : 0 ≤ (2 + towerR κ t β₀ p₁) := by linarith [hr]
        positivity
      nlinarith [mul_nonneg hpos (neg_nonneg.2 hneg.le)]
  · intro z x hx u hu
    have hloc := classRegularLoc_zeroClass R0 hp hlt 0
    exact (hatStep m₁ β₀ p₁ δ).hasDerivAt_Phi1_marked_of_classRegularLoc z
      (zeroClass 3 3 9 m₁ 1 2 (rhoSep m₁)) hloc hx hu

end Balaban.Inhabited
