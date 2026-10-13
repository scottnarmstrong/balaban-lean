/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.OffFibreE1Marks
public import Balaban.Fluctuation.OffFibreBlockEnergyCore

/-!
# The marked first-energy comparison at a free datum

The marked fluctuation disc and the old action use the incoming field at each chart datum.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Fluctuation Balaban.Multiscale Balaban.Background Balaban.Localization
  Balaban.Localization.I5Inhabited Balaban.Inhabited.LevelStep Balaban.SmallField Set Matrix

/-- The marked fluctuation disc is valid for every incoming field in the chart. -/
theorem markReal_disc_slice_raw {κmin : ℝ} (T : StepTower κmin) {k : ℕ}
    {hk : 1 ≤ k} {N₁ : ℕ} [NeZero N₁] {ν β p₁ : ℝ}
    (Dt : StepScaleData T k hk N₁ ν β p₁) (hp : 0 < p₁)
    (D : BgData (T.step k hk N₁ ν β p₁).G' 2)
    (hX : XiCData (T.step k hk N₁ ν β p₁).G' (compWeight 3 1) ν (k + 1) 1 T.t D)
    (x : (T.step k hk N₁ ν β p₁).E) (hx : ‖x‖ ≤ p₁)
    (z : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))))
    {u : ℂ} (hu : ‖u‖ < 17 / 16) :
    ∀ t : ℂ, ‖t‖ < 1 / 16 → ∀ σ : ℂ,
      ‖σ‖ < 17 / 16 + lvR T.κ T.t (β * 3 ^ k) p₁ / 4 →
      σ • (liftC (T.step k hk N₁ ν β p₁).hG'
          (u • (T.step k hk N₁ ν β p₁).hatField
            (hatCovSqrt (T.step k hk N₁ ν β p₁).G'
              (T.step k hk N₁ ν β p₁).a₁ (T.step k hk N₁ ν β p₁).ν D) (yhat x)) +
        t • liftC (T.step k hk N₁ ν β p₁).hG'
          ((T.step k hk N₁ ν β p₁).maskUC z
            ((T.step k hk N₁ ν β p₁).hatField
              (hatCovSqrt (T.step k hk N₁ ν β p₁).G'
                (T.step k hk N₁ ν β p₁).a₁ (T.step k hk N₁ ν β p₁).ν D) (yhat x)))) ∈
        FlBall (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) T.t := by
  intro t ht σ hσ
  let S := T.step k hk N₁ ν β p₁
  obtain ⟨Q, -, hQ, hQb⟩ := exists_analytic_hatField_chart Dt.core hk
    T.large_block T.dom_margin T.coer_margin T.δc_small
    (((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) hp.le
    (fun p => S.yhat_le_of_norm_le hx p)
  have hY := hQb (rawOf D) ⟨D, hX, rfl⟩
  have hQ' : Q (rawOf D) =
      S.hatField (hatCovSqrt S.G' S.a₁ S.ν D) (yhat x) := hQ D hX
  have hY' : ∀ b : S.U,
      vn (fun i => S.hatField (hatCovSqrt S.G' S.a₁ S.ν D) (yhat x) (b, i)) ≤
        markedRad 3 3 2 k S.a₁ T.κ p₁ (((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) := by
    intro b
    have ha : S.a₁ = 1 := rfl
    rw [ha]
    calc
      _ = vn (fun i => Q (rawOf D) (b, i)) :=
        congrArg vn (funext fun i => (congrFun hQ' (b, i)).symm)
      _ ≤ _ := hY b
  exact S.markedDisc_field_mem_flBall z (isLevel_lvLow hk) hY'
    (Dt.marked_radius_lt hp) hu ht hσ

end Balaban.Inhabited

namespace Balaban.Fluctuation.StepSetting

open Balaban Balaban.Background Balaban.Multiscale Balaban.Localization Balaban.Polymer
  Balaban.SmallField Matrix

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ)

/-- The decoupled marked tangent uses the covariance of the free datum. -/
theorem markedTangDec_eq_liftC_raw
    (D : BgData S.G' N) (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))))
    (u t : ℂ) (x : S.E) :
    markedTangDec S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) S.a₁ S.ν
      (S.blockU z) u t D (yhat x) =
      liftC S.hG' (u • S.hatField (hatCovSqrt S.G' S.a₁ S.ν D) (yhat x) +
        t • S.maskUC z (S.hatField (hatCovSqrt S.G' S.a₁ S.ν D) (yhat x))) := by
  have hsh : S.hatField (hatCovSqrt S.G' S.a₁ S.ν D) (yhat x) =
      (((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) •
        (hatCovSqrt S.G' S.a₁ S.ν D *ᵥ yhat x)) := rfl
  have hmask : S.maskUC z (S.hatField (hatCovSqrt S.G' S.a₁ S.ν D) (yhat x)) =
      maskBlock (S.blockU z)
        ((((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) •
          (hatCovSqrt S.G' S.a₁ S.ν D *ᵥ yhat x))) := by rw [hsh]; rfl
  rw [hmask, hsh]
  rfl

/-- A decoupled block functional at a free datum is its raw block energy. -/
theorem markedFunDec_eq_blockEnergyOne_raw {κ eps BG₂ : ℝ}
    (D : BgData S.G' N) (hX : XiCData S.G' S.a S.ν (k + 1) 1 eps D)
    (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))) (u t : ℂ) (x : S.E)
    (b : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))) :
    markedFunDec S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) S.a₁ S.ν BG₂ κ
        (S.blockU z) u t
        (blockEnergyFun S.G' (stepG d L N₁ m₁ k ϱ) S.a S.ν k b) D (yhat x) =
      blockEnergyOne S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν BG₂ κ eps k b
        (rawOf D, liftC S.hG' (u • S.hatField (hatCovSqrt S.G' S.a₁ S.ν D) (yhat x) +
          t • S.maskUC z (S.hatField (hatCovSqrt S.G' S.a₁ S.ν D) (yhat x)))) := by
  rw [blockEnergyOne_rawOf hX k b, ← S.markedTangDec_eq_liftC_raw D z u t x]
  rfl

/-- The decoupled marks at a free chart datum differentiate the raw block-energy sum. -/
theorem sum_decMarkG_eq_deriv_blockEnergyOne_raw
    {BG BG₂ κ eps δ₁ κdec cψ ρ : ℝ}
    {X₁V : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      Finset (CTorus d L N₁ m₁ (k + 1))}
    {jV : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → ℕ}
    {𝒦XV : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      Set (CTorus d L N₁ m₁ (k + 1))}
    {m₀ : ℕ}
    (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))))
    (F₁ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      DecParams S.G' × RawData d L (N₁ * L ^ m₁) (k + 1) N →
        (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ))
    (Sol : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf S.G') × Edat (stepG d L N₁ m₁ k ϱ) N →
        ((stepG d L N₁ m₁ k ϱ).Ω 1 × Fin N → ℂ) ×
          ((stepG d L N₁ m₁ k ϱ).Ω 1 → ℂ))
    (hP : ∀ b, MarkedBlockExpansionDecPair N (stepG d L N₁ m₁ k ϱ) S.hG'
      ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) S.a₁ S.ν BG BG₂ κ eps δ₁ κdec cψ
      (S.blockU z) (X₁V b) m₀ (jV b) (𝒦XV b) b (F₁ b) (Sol b))
    (hρ : 0 < ρ) (hρc : ρ ≤ cψ) (hp : 0 < S.p₁)
    (D : BgData S.G' N) (hX : XiCData S.G' S.a S.ν (k + 1) 1 eps D)
    (x : S.E) (hx : ∀ q, ‖x q‖ ≤ ρ)
    {u : ℂ} (hu : (‖u‖ + ‖(0 : ℂ)‖) *
      markedRad d L N k S.a₁ κ cψ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < δ₁) :
    (∑ b, ∑ Y ∈ polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b),
      decMarkG S (X₁V b) m₀ (jV b) (𝒦XV b) S.a₁ S.ν
        ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁ b) (Sol b)
        (blockEnergyFun S.G' (stepG d L N₁ m₁ k ϱ) S.a S.ν k b)
        (S.blockU z) Y ρ hp (rawOf D) u ((S.blockSplit m₀ hp).restr x)) =
      deriv (fun t : ℂ => ∑ b : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))),
        blockEnergyOne S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν BG₂ κ eps k b
          (rawOf D, liftC S.hG'
            (u • S.hatField (hatCovSqrt S.G' S.a₁ S.ν D) (yhat x) +
              t • S.maskUC z (S.hatField (hatCovSqrt S.G' S.a₁ S.ν D) (yhat x))))) 0 := by
  have hhat : S.hatOf m₀ ρ hp ((S.blockSplit m₀ hp).restr x) = yhat x :=
    S.hatOf_restr m₀ hρ hp x hx
  have hψ : ∀ p, ‖yhat x p‖ ≤ cψ := fun p => by
    rw [← hhat]
    exact (S.hatOf_mem m₀ hρ hp _ p).trans hρc
  have hfun : (fun t : ℂ => ∑ b : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))),
      blockEnergyOne S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν BG₂ κ eps k b
        (rawOf D, liftC S.hG'
          (u • S.hatField (hatCovSqrt S.G' S.a₁ S.ν D) (yhat x) +
            t • S.maskUC z (S.hatField (hatCovSqrt S.G' S.a₁ S.ν D) (yhat x))))) =
      fun t : ℂ => ∑ b : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))),
        markedFunDec S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) S.a₁ S.ν BG₂ κ
          (S.blockU z) u t
          (blockEnergyFun S.G' (stepG d L N₁ m₁ k ϱ) S.a S.ν k b) D (yhat x) :=
    funext fun t => Finset.sum_congr rfl fun b _ =>
      (S.markedFunDec_eq_blockEnergyOne_raw D hX z u t x b).symm
  rw [hfun, deriv_fun_sum fun b _ => differentiableAt_markedFunDec_mark S
    (hP b) hX hψ hu]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [sum_decMarkG_eq_deriv_markedFunDec S (hP b) hρ hρc hp hX hu, hhat]

/-- The quadratic correction on a marked plane has the expected three coefficients. -/
theorem deltaForm_marked_raw
    (D : BgData S.G' N)
    (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))) (y : S.EC)
    (u t : ℂ) :
    let P := liftC S.hG' y
    let Q := liftC S.hG' (S.maskUC z y)
    let δ := deltaForm (S.hG.precedes S.hG' (le_refl (k + 1))) S.a S.ν
      (bgMultC S.G' S.a S.ν (bgC0 d L N) D)
      (bgFieldC S.G' S.a S.ν (bgC0 d L N) D)
    δ (liftC S.hG' (u • y + t • S.maskUC z y)) =
      δ P * u ^ 2 + (δ (fun x i => P x i + Q x i) - δ P - δ Q) * u * t +
        δ Q * t ^ 2 := by
  dsimp only
  have hl : liftC S.hG' (u • y + t • S.maskUC z y) =
      fun x i => u * (liftC S.hG' y) x i +
        t * (liftC S.hG' (S.maskUC z y)) x i := by
    rw [map_add, map_smul, map_smul]
    rfl
  rw [hl]
  exact deltaForm_two (S.hG.precedes S.hG' (le_refl (k + 1))) S.a S.ν
    (bgMultC S.G' S.a S.ν (bgC0 d L N) D)
    (bgFieldC S.G' S.a S.ν (bgC0 d L N) D) _ _ u t

end Balaban.Fluctuation.StepSetting

namespace Balaban.Fluctuation.StepSetting.JointRep

open Balaban Balaban.Background Balaban.Multiscale Balaban.Localization
  Balaban.SmallField Balaban.SmallField.Def6 Matrix Filter Topology

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ eps pp : ℝ}
  {S : StepSetting d L N₁ m₁ k N ϱ} (Jr : S.JointRep eps pp)

/-- For the class with no inherited energy, the first exponent is the interaction. -/
theorem W1_zeroClass_eq_neg_beta_VJ
    (q : RawData d L (N₁ * L ^ m₁) (k + 1) N × S.EC) :
    Jr.W1 (zeroClass d L N₁ m₁ k N ϱ) q = -(S.β : ℂ) * Jr.VJ q := by
  unfold W1 EJ
  have h0 : ∀ (j : ℕ) (a b : Fld d L N₁ m₁ (k + 1) N),
      Edens (zeroClass d L N₁ m₁ k N ϱ).m₀
        (zeroClass d L N₁ m₁ k N ϱ).Tm j a b = 0 :=
    fun j a b => Edens_zero _ _ _ _
  simp only [h0, Finset.sum_const_zero, sub_self, add_zero]

/-- Every real ray of the joint interaction has vanishing first two derivatives at the
critical spin, for any incoming chart field. -/
theorem VJ_ray_vanish_freeDatum
    (D : BgData S.G' N) (hX : XiCData S.G' S.a S.ν (k + 1) 1 eps D)
    (ha₁ : 0 < S.a₁) (HB : BgHyp d L (k + 1) ϱ S.a S.ν)
    (hD2 : InUnionDomainC S.G' (bgC0 d L N) (thm73C2 d L N) S.ν D)
    (hpp : 0 < pp) (w : S.EC) :
    let F : ℝ → ℂ := fun r => Jr.VJ (rawOf D, (r : ℂ) • w)
    deriv F 0 = 0 ∧ deriv (deriv F) 0 = 0 := by
  dsimp only
  let H := S.withDatumH D
  let B := composeData (S.hG.precedes S.hG' (le_refl (k + 1))) S.a
    (bgFieldC S.G' S.a S.ν (bgC0 d L N) D) D
  let ψ₀ : S.EC := fun q => B.Ψ (unitRep (G' := S.G') q.1) q.2
  let v := S.hatField (hatCovSqrt S.G' S.a₁ S.ν D) w
  let I : ℝ → ℂ := fun r => interactionV
    (S.hG.precedes S.hG' (le_refl (k + 1))) S.a S.ν
    (bgMultC S.G' S.a S.ν (bgC0 d L N) D)
    (bgFieldC S.G' S.a S.ν (bgC0 d L N) D)
    ((r : ℂ) • liftC S.hG' v)
    (bgFieldC (stepG d L N₁ m₁ k ϱ) S.a S.ν (bgC0 d L N)
      (H.dataUCH (ψ₀ + (r : ℂ) • v)) -
      (S.hG.precedes S.hG' (le_refl (k + 1))).restrictφ
        (bgFieldC S.G' S.a S.ν (bgC0 d L N) D))
  have hc : Continuous (fun r : ℝ => (r : ℂ) • w) :=
    Complex.continuous_ofReal.smul continuous_const
  have hsmall : ∀ᶠ r : ℝ in 𝓝 0, ‖(r : ℂ) • w‖ < pp := by
    have h0 : ‖(0 : ℂ) • w‖ < pp := by simpa using hpp
    exact hc.continuousAt.eventually
      ((isOpen_lt continuous_norm continuous_const).mem_nhds h0)
  have hdom : ∀ᶠ r : ℝ in 𝓝 0,
      InUnionDomainC (stepG d L N₁ m₁ k ϱ) (bgC0 d L N) (bgC1 d L N) S.ν
        (H.dataUCH (ψ₀ + (r : ℂ) • v)) := by
    filter_upwards [hsmall] with r hr
    have hψ : ∀ p, ‖((r : ℂ) • w) p‖ ≤ pp :=
      fun p => (norm_le_pi_norm _ p).trans hr.le
    have hd := Jr.dataUCH_hat_dom H hX hψ
    rwa [S.hatField_smul] at hd
  obtain ⟨_, h1, h2⟩ := H.interaction_ray_vanish ha₁ HB hD2 v hdom
  have hEq : (fun r : ℝ => Jr.VJ (rawOf D, (r : ℂ) • w)) =ᶠ[𝓝 0] I := by
    filter_upwards [hsmall] with r hr
    have hψ : ∀ p, ‖((r : ℂ) • w) p‖ ≤ pp :=
      fun p => (norm_le_pi_norm _ p).trans hr.le
    have h := Jr.VJ_dataUCH H hX hψ
    dsimp only at h
    rw [H.compTangent_dataUCH] at h
    simp only [add_sub_cancel_left, S.hatField_smul, map_smul] at h
    exact h
  exact ⟨hEq.deriv_eq.trans h1, hEq.deriv.deriv_eq.trans h2⟩

/-- The first Taylor remainder of a marked joint interaction plus a quadratic term is the
marked derivative of the interaction. -/
theorem VJ_mark_taylor1_freeDatum
    (D : BgData S.G' N) (hX : XiCData S.G' S.a S.ν (k + 1) 1 eps D)
    (ha₁ : 0 < S.a₁) (HB : BgHyp d L (k + 1) ϱ S.a S.ν)
    (hD2 : InUnionDomainC S.G' (bgC0 d L N) (thm73C2 d L N) S.ν D)
    (hpp : 0 < pp) (a b : S.EC) (A C Dq : ℂ) (u : ℂ)
    (hu : DifferentiableAt ℂ
      (fun t : ℂ => Jr.VJ (rawOf D, u • a + t • b)) 0) :
    let g : ℂ × ℂ → ℂ := fun w => Jr.VJ (rawOf D, w.1 • a + w.2 • b)
    deriv (fun t : ℂ => g (u, t) + (A * u ^ 2 + C * u * t + Dq * t ^ 2)) 0 -
      deriv (fun t : ℂ => g (0, t) + (A * (0 : ℂ) ^ 2 + C * 0 * t + Dq * t ^ 2)) 0 -
      u * deriv (fun u' : ℂ => deriv (fun t : ℂ => g (u', t) +
        (A * u' ^ 2 + C * u' * t + Dq * t ^ 2)) 0) 0 =
      deriv (fun t : ℂ => g (u, t)) 0 := by
  dsimp only
  let g : ℂ × ℂ → ℂ := fun w => Jr.VJ (rawOf D, w.1 • a + w.2 • b)
  have hΘ : rawOf D ∈ XiCRaw S.G' S.a S.ν (k + 1) 1 eps := ⟨D, hX, rfl⟩
  have hψ0 : ∀ p, ‖(0 : S.EC) p‖ ≤ pp := fun _ => by simpa using hpp.le
  have hlin : AnalyticAt ℂ (fun w : ℂ × ℂ =>
      (rawOf D, w.1 • a + w.2 • b)) 0 := by
    exact analyticAt_const.prod
      ((analyticAt_fst.smul analyticAt_const).add (analyticAt_snd.smul analyticAt_const))
  have hg : AnalyticAt ℂ g 0 :=
    (Jr.analyticAt_VJ hΘ hψ0).comp_of_eq hlin (by simp)
  have hj : ∀ w : ℂ × ℂ,
      deriv (fun r : ℝ => g ((r : ℂ) • w)) 0 = 0 ∧
      deriv (deriv (fun r : ℝ => g ((r : ℂ) • w))) 0 = 0 := by
    intro w
    have he : (fun r : ℝ => g ((r : ℂ) • w)) =
        fun r : ℝ => Jr.VJ (rawOf D, (r : ℂ) • (w.1 • a + w.2 • b)) := by
      funext r
      simp [g, Prod.smul_def, smul_add, smul_smul]
    rw [he]
    exact Jr.VJ_ray_vanish_freeDatum D hX ha₁ HB hD2 hpp _
  obtain ⟨h1, h2⟩ := rayJet_pair_of_real g hg
    (fun w => (hj w).1) (fun w => (hj w).2)
  exact mark_taylor1_add g hg h1 h2 A C Dq u hu

/-- On the free-datum fluctuation ball, the block-energy total is the raw joint
interaction plus the quadratic correction. -/
theorem blockEnergy_eq_VJ_add_delta_raw
    {c BG κ Kc Cx c₂ BG₂ δ₁ : ℝ}
    (hC : FlCore N S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (ha₁ : 0 < S.a₁) (hc7 : c7 d L N BG κ ≤ thm73C3 d L N)
    {R : ℝ} (hR : 2 ≤ R)
    (hsmR : 2 * (compC4 d * (bgK1 d L N * (xiC1 d * eps))) +
      5 * (R * δ₁) ≤ bgC1 d L N)
    (hRs : R * δ₁ ≤ deltaStar d L N)
    (hsmall : cK2 d L N * (R * δ₁) < bgC0 d L N / 2)
    (hnum : cK2 d L N * δ₁ ≤ c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hnum' : cK2' d L N (famConst d L BG₂ κ) * δ₁ ≤
      c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (D : BgData S.G' N) (hX : XiCData S.G' S.a S.ν (k + 1) 1 eps D)
    (w : S.EC) (hw : ∀ p, ‖w p‖ ≤ pp)
    (hball : liftC S.hG' (S.hatField (hatCovSqrt S.G' S.a₁ S.ν D) w) ∈
      FlBall (stepG d L N₁ m₁ k ϱ) δ₁) :
    (∑ b : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))),
      blockEnergyOne S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν BG₂ κ eps k b
        (rawOf D, liftC S.hG' (S.hatField (hatCovSqrt S.G' S.a₁ S.ν D) w))) =
      Jr.VJ (rawOf D, w) +
      (1 / 2) * deltaForm (S.hG.precedes S.hG' (le_refl (k + 1))) S.a S.ν
        (bgMultC S.G' S.a S.ν (bgC0 d L N) D)
        (bgFieldC S.G' S.a S.ν (bgC0 d L N) D)
        (liftC S.hG' (S.hatField (hatCovSqrt S.G' S.a₁ S.ν D) w)) := by
  let H := S.withDatumH D
  have he := H.sum_blockEnergyOne_eq_interaction_add_delta hC ha₁ hc7 hR hsmR
    hRs hsmall hnum hnum' hX _ hball
  have hV := Jr.VJ_dataUCH H hX hw
  dsimp only [H, StepSetting.withDatumH] at he hV
  rw [hV]
  exact he

/-- The inverse covariance coordinates express the physical marked direction. -/
theorem hatField_marked_raw
    {c BG κ Kc Cx c₂ BG₂ δ₁ δc : ℝ}
    (hC : FlCore N S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (D : BgData S.G' N) (hX : XiCData S.G' S.a S.ν (k + 1) 1 eps D)
    (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))) (x : S.E)
    (u t : ℂ) :
    let a := yhat x
    let b := (Jr.Mx (rawOf D))⁻¹ *ᵥ S.maskUC z (Jr.Mx (rawOf D) *ᵥ a)
    let y := S.hatField (hatCovSqrt S.G' S.a₁ S.ν D) a
    S.hatField (hatCovSqrt S.G' S.a₁ S.ν D) (u • a + t • b) =
      u • y + t • S.maskUC z y := by
  dsimp only
  have hM := Jr.Mx_eq D hX
  have hb := Jr.hatField_inv_mask_of_chart (S.withDatumH D)
    hC hMX hdm hα hsm hX z x
  dsimp only [StepSetting.withDatumH] at hb
  rw [hM] at hb ⊢
  have hadd (a b : S.EC) :
      S.hatField (hatCovSqrt S.G' S.a₁ S.ν D) (a + b) =
        S.hatField (hatCovSqrt S.G' S.a₁ S.ν D) a +
          S.hatField (hatCovSqrt S.G' S.a₁ S.ν D) b := by
    unfold StepSetting.hatField
    rw [Matrix.mulVec_add, smul_add]
  rw [hadd, S.hatField_smul, S.hatField_smul, hb]

/-- The free-datum block-energy mark has the masked raw first-exponent derivative as its
first Taylor remainder. The disc premise records the marked fluctuation margin. -/
theorem blockEnergy_mark_taylor_eq_fderiv_W1_raw
    {c BG κ Kc Cx c₂ BG₂ δ₁ : ℝ}
    (hC : FlCore N S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (ha₁ : 0 < S.a₁) (hc7 : c7 d L N BG κ ≤ thm73C3 d L N)
    {R : ℝ} (hR : 2 ≤ R)
    (hsmR : 2 * (compC4 d * (bgK1 d L N * (xiC1 d * eps))) +
      5 * (R * δ₁) ≤ bgC1 d L N)
    (hRs : R * δ₁ ≤ deltaStar d L N)
    (hsmall : cK2 d L N * (R * δ₁) < bgC0 d L N / 2)
    (hnum : cK2 d L N * δ₁ ≤ c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hnum' : cK2' d L N (famConst d L BG₂ κ) * δ₁ ≤
      c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (D : BgData S.G' N) (hX : XiCData S.G' S.a S.ν (k + 1) 1 eps D)
    (hD2 : InUnionDomainC S.G' (bgC0 d L N) (thm73C2 d L N) S.ν D)
    (hpp : 0 < pp) (a b : S.EC) {U V : ℝ} (hU : 0 < U) (hV : 0 < V)
    (hball : ∀ u : ℂ, ‖u‖ < U → ∀ t : ℂ, ‖t‖ < V →
      liftC S.hG' (S.hatField (hatCovSqrt S.G' S.a₁ S.ν D) (u • a + t • b)) ∈
        FlBall (stepG d L N₁ m₁ k ϱ) δ₁)
    (s : ℂ) (hsU : ‖s‖ < U) (hspp : ‖s • a‖ < pp) :
    let e : ℂ × ℂ → ℂ := fun w =>
      ∑ z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))),
        blockEnergyOne S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν BG₂ κ eps k z
          (rawOf D, liftC S.hG' (S.hatField (hatCovSqrt S.G' S.a₁ S.ν D)
            (w.1 • a + w.2 • b)));
    let f : ℂ → ℂ := fun u => deriv (fun t : ℂ => e (u, t)) 0;
    -(S.β : ℂ) * (f s - f 0 - s * deriv f 0) =
      (fderiv ℂ (fun w : S.EC =>
        Jr.W1 (zeroClass d L N₁ m₁ k N ϱ) (rawOf D, w)) (s • a)) b := by
  dsimp only
  let M := hatCovSqrt S.G' S.a₁ S.ν D
  let y := S.hatField M a
  let v := S.hatField M b
  let e : ℂ × ℂ → ℂ := fun w =>
    ∑ z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))),
      blockEnergyOne S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν BG₂ κ eps k z
        (rawOf D, liftC S.hG' (S.hatField M (w.1 • a + w.2 • b)))
  let g : ℂ × ℂ → ℂ := fun w => Jr.VJ (rawOf D, w.1 • a + w.2 • b)
  let δ := deltaForm (S.hG.precedes S.hG' (le_refl (k + 1))) S.a S.ν
    (bgMultC S.G' S.a S.ν (bgC0 d L N) D)
    (bgFieldC S.G' S.a S.ν (bgC0 d L N) D)
  let P := liftC S.hG' y
  let Q := liftC S.hG' v
  let A := (1 / 2 : ℂ) * δ P
  let C := (1 / 2 : ℂ) * (δ (fun x i => P x i + Q x i) - δ P - δ Q)
  let Dq := (1 / 2 : ℂ) * δ Q
  let q : ℂ × ℂ → ℂ := fun w => A * w.1 ^ 2 + C * w.1 * w.2 + Dq * w.2 ^ 2
  let f : ℂ → ℂ := fun u => deriv (fun t : ℂ => e (u, t)) 0
  let F : ℂ → ℂ := fun u => deriv (fun t : ℂ => g (u, t) + q (u, t)) 0
  have hlin (u t : ℂ) : S.hatField M (u • a + t • b) = u • y + t • v := by
    have hadd (a' b' : S.EC) : S.hatField M (a' + b') =
        S.hatField M a' + S.hatField M b' := by
      unfold StepSetting.hatField
      rw [Matrix.mulVec_add, smul_add]
    rw [hadd, S.hatField_smul, S.hatField_smul]
  have hq (u t : ℂ) :
      (1 / 2 : ℂ) * δ (liftC S.hG' (S.hatField M (u • a + t • b))) = q (u, t) := by
    rw [hlin]
    have hl : liftC S.hG' (u • y + t • v) =
        fun x i => u * P x i + t * Q x i := by
      rw [map_add, map_smul, map_smul]
      rfl
    rw [hl]
    dsimp only [δ]
    rw [deltaForm_two (S.hG.precedes S.hG' (le_refl (k + 1))) S.a S.ν
      (bgMultC S.G' S.a S.ν (bgC0 d L N) D)
      (bgFieldC S.G' S.a S.ν (bgC0 d L N) D) P Q u t]
    dsimp only [q, A, C, Dq]
    ring
  have he (u : ℂ) (hu : ‖u‖ < U) (hua : ‖u • a‖ < pp) :
      f u = F u := by
    apply Filter.EventuallyEq.deriv_eq
    have hc : Continuous (fun t : ℂ => u • a + t • b) :=
      continuous_const.add (continuous_id.smul continuous_const)
    have h0 : ‖u • a + (0 : ℂ) • b‖ < pp := by simpa using hua
    have hnear : ∀ᶠ t : ℂ in 𝓝 0, ‖u • a + t • b‖ < pp :=
      hc.continuousAt.eventually ((isOpen_lt continuous_norm continuous_const).mem_nhds h0)
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hV, hnear] with t ht hwt
    have ht' : ‖t‖ < V := by simpa using ht
    have hw : ∀ p, ‖(u • a + t • b) p‖ ≤ pp :=
      fun p => (norm_le_pi_norm _ p).trans hwt.le
    have hv := Jr.blockEnergy_eq_VJ_add_delta_raw hC ha₁ hc7 hR hsmR
      hRs hsmall hnum hnum' D hX (u • a + t • b) hw (hball u hu t ht')
    change e (u, t) = g (u, t) + q (u, t)
    rw [← hq, ← hv]
  have hnearU : ∀ᶠ u : ℂ in 𝓝 0, ‖u‖ < U :=
    (isOpen_lt continuous_norm continuous_const).mem_nhds (by simpa using hU)
  have hnearA : ∀ᶠ u : ℂ in 𝓝 0, ‖u • a‖ < pp := by
    have hc : Continuous (fun u : ℂ => u • a) := continuous_id.smul continuous_const
    exact hc.continuousAt.eventually
      ((isOpen_lt continuous_norm continuous_const).mem_nhds (by simpa using hpp))
  have hf : f =ᶠ[𝓝 0] F := by
    filter_upwards [hnearU, hnearA] with u hu hua
    exact he u hu hua
  have hTaylor := taylor1_remainder_congr hf (he s hsU hspp)
  have hΘ : rawOf D ∈ XiCRaw S.G' S.a S.ν (k + 1) 1 eps := ⟨D, hX, rfl⟩
  have hsbound : ∀ p, ‖(s • a) p‖ ≤ pp := fun p => (norm_le_pi_norm _ p).trans hspp.le
  have hVan : AnalyticAt ℂ (fun w : S.EC => Jr.VJ (rawOf D, w)) (s • a) :=
    (Jr.analyticAt_VJ hΘ hsbound).comp_of_eq
      (analyticAt_const.prod analyticAt_id) rfl
  have hline : HasDerivAt (fun t : ℂ => g (s, t))
      ((fderiv ℂ (fun w : S.EC => Jr.VJ (rawOf D, w)) (s • a)) b) 0 := by
    have hl : HasDerivAt (fun t : ℂ => s • a + t • b) b 0 := by
      simpa using ((hasDerivAt_id (0 : ℂ)).smul_const b).const_add (s • a)
    have hd' : HasFDerivAt (fun w : S.EC => Jr.VJ (rawOf D, w))
        (fderiv ℂ (fun w : S.EC => Jr.VJ (rawOf D, w)) (s • a))
        (s • a + (0 : ℂ) • b) := by
      simpa only [zero_smul, add_zero] using hVan.differentiableAt.hasFDerivAt
    exact hd'.comp_hasDerivAt 0 hl
  have hmark := Jr.VJ_mark_taylor1_freeDatum D hX ha₁ hC.HBp hD2 hpp
    a b A C Dq s hline.differentiableAt
  have hFmark : F s - F 0 - s * deriv F 0 = deriv (fun t : ℂ => g (s, t)) 0 := by
    simpa only [F, q, g] using hmark
  rw [hTaylor, hFmark, hline.deriv]
  have hW : (fun w : S.EC => Jr.W1 (zeroClass d L N₁ m₁ k N ϱ) (rawOf D, w)) =
      fun w => -(S.β : ℂ) * Jr.VJ (rawOf D, w) :=
    funext fun w => Jr.W1_zeroClass_eq_neg_beta_VJ (rawOf D, w)
  rw [hW, fderiv_const_mul hVan.differentiableAt]
  rfl

end Balaban.Fluctuation.StepSetting.JointRep

