/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.StepActivityOffFibreTaylor
public import Balaban.Fluctuation.DecMarkCorrectedTotal
import Mathlib.Tactic.Linarith

/-!
# The block-energy total at a free incoming datum

The marked fluctuation domain and the block-energy comparison use the incoming field
of the chart datum.
-/

@[expose] public section

namespace Balaban.Fluctuation.StepSettingH

open Balaban Balaban.Background Balaban.Multiscale Balaban.Localization Balaban.SmallField Matrix

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  {S : StepSetting d L N₁ m₁ k N ϱ} (H : StepSettingH S)
  {c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ}

/-- The free old datum inherits the marked fluctuation disc supplied by the background
response theorem. -/
theorem dataUCH_line_domain_of_flBall
    (hC : FlCore N S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (ha₁ : 0 < S.a₁) (hc7 : c7 d L N BG κ ≤ thm73C3 d L N)
    {R : ℝ} (hR : 2 ≤ R)
    (hsmR : 2 * (compC4 d * (bgK1 d L N * (xiC1 d * eps))) +
      5 * (R * δ₁) ≤ bgC1 d L N)
    (hX : XiCData S.G' S.a S.ν (k + 1) 1 eps H.D')
    (v : S.EC) (hv : liftC S.hG' v ∈ FlBall (stepG d L N₁ m₁ k ϱ) δ₁) :
    let B := composeData (S.hG.precedes S.hG' (le_refl (k + 1))) S.a
      (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D') H.D'
    let ψ₀ : S.EC := fun q => B.Ψ (unitRep (G' := S.G') q.1) q.2
    let Dv := H.dataUCH (ψ₀ + v)
    ∀ t : ℂ, ‖t‖ < R →
      InUnionDomainC (stepG d L N₁ m₁ k ϱ) (bgC0 d L N) (bgC1 d L N) S.ν
        (B.lineAt (tangentData Dv B) t) := by
  dsimp only
  let B := composeData (S.hG.precedes S.hG' (le_refl (k + 1))) S.a
    (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D') H.D'
  let ψ₀ : S.EC := fun q => B.Ψ (unitRep (G' := S.G') q.1) q.2
  let Dv := H.dataUCH (ψ₀ + v)
  obtain ⟨E, hh, hct, hline⟩ := hreal_level hC S.hG S.hG' (le_refl (k + 1))
    ha₁ hC.HBp hc7 (by linarith : (0 : ℝ) ≤ R) hsmR H.D' hX
    (liftC S.hG' v) hv (isLayerConstant_liftC S.hG S.hG' v)
  have hctDv : compTangent S.hG S.hG' (le_refl (k + 1)) S.a
      (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D') H.D' Dv = liftC S.hG' v := by
    rw [H.compTangent_dataUCH]
    change liftC S.hG' ((ψ₀ + v) - ψ₀) = liftC S.hG' v
    simp only [add_sub_cancel_left]
  have hE : E = Dv := by
    refine BgData.eq_of_raw (Prod.ext ?_ ?_)
    · funext x i
      have he := congrFun (congrFun (hct.trans hctDv.symm) x) i
      dsimp only [compTangent] at he
      exact sub_left_inj.mp he
    · funext x i
      exact (hh x i).trans (H.dataUCH_h (ψ₀ + v) x i).symm
  subst E
  exact hline

/-- The block-energy identity given the marked line domain. -/
theorem sum_blockEnergyOne_eq_interaction_add_delta_of_domain
    (hC : FlCore N S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (ha₁ : 0 < S.a₁) (hc7 : c7 d L N BG κ ≤ thm73C3 d L N)
    {R : ℝ} (hR : 2 ≤ R)
    (hRs : R * δ₁ ≤ deltaStar d L N)
    (hsmall : cK2 d L N * (R * δ₁) < bgC0 d L N / 2)
    (hnum : cK2 d L N * δ₁ ≤ c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hnum' : cK2' d L N (famConst d L BG₂ κ) * δ₁ ≤
      c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hX : XiCData S.G' S.a S.ν (k + 1) 1 eps H.D')
    (v : S.EC) (hv : liftC S.hG' v ∈ FlBall (stepG d L N₁ m₁ k ϱ) δ₁)
    :
    let B := composeData (S.hG.precedes S.hG' (le_refl (k + 1))) S.a
      (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D') H.D'
    let ψ₀ : S.EC := fun q => B.Ψ (unitRep (G' := S.G') q.1) q.2
    let Dv := H.dataUCH (ψ₀ + v)
    (∀ t : ℂ, ‖t‖ < R →
      InUnionDomainC (stepG d L N₁ m₁ k ϱ) (bgC0 d L N) (bgC1 d L N) S.ν
        (B.lineAt (tangentData Dv B) t)) →
    (∑ b : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))),
      blockEnergyOne S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν BG₂ κ eps k b
        (rawOf H.D', liftC S.hG' v)) =
      interactionV (S.hG.precedes S.hG' (le_refl (k + 1))) S.a S.ν
        (bgMultC S.G' S.a S.ν (bgC0 d L N) H.D')
        (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D')
        (compTangent S.hG S.hG' (le_refl (k + 1)) S.a
          (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D') H.D' Dv)
        (bgFieldC (stepG d L N₁ m₁ k ϱ) S.a S.ν (bgC0 d L N) Dv -
          (S.hG.precedes S.hG' (le_refl (k + 1))).restrictφ
            (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D')) +
      (1 / 2) * deltaForm (S.hG.precedes S.hG' (le_refl (k + 1))) S.a S.ν
        (bgMultC S.G' S.a S.ν (bgC0 d L N) H.D')
        (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D') (liftC S.hG' v) := by
  dsimp only
  intro hline
  let B := composeData (S.hG.precedes S.hG' (le_refl (k + 1))) S.a
    (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D') H.D'
  let ψ₀ : S.EC := fun q => B.Ψ (unitRep (G' := S.G') q.1) q.2
  let Dv := H.dataUCH (ψ₀ + v)
  have hct : compTangent S.hG S.hG' (le_refl (k + 1)) S.a
      (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D') H.D' Dv = liftC S.hG' v := by
    rw [H.compTangent_dataUCH]
    change liftC S.hG' ((ψ₀ + v) - ψ₀) = liftC S.hG' v
    simp only [add_sub_cancel_left]
  have he := interactionV_eq_energy hC S.hG S.hG' (le_refl (k + 1)) ha₁
    hC.HBp H.D' hX hc7 Dv (fun x i => H.dataUCH_h (ψ₀ + v) x i) (by rw [hct]; exact hv)
    hR hline hRs hsmall hnum hnum'
  have hsum : (∑ b : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))),
      blockEnergyOne S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν BG₂ κ eps k b
        (rawOf H.D', liftC S.hG' v)) =
      ∑ b : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))),
        energyBlock S.G' (stepG d L N₁ m₁ k ϱ) S.a S.ν k
          (bgMultC S.G' S.a S.ν (bgC0 d L N) H.D')
          (flFieldOne S.G' (stepG d L N₁ m₁ k ϱ) BG₂ κ S.a₁ S.ν H.D'
            (liftC S.hG' v)) (liftC S.hG' v) b :=
    Finset.sum_congr rfl fun b _ => blockEnergyOne_rawOf hX k b _
  rw [hsum, hct] at *
  linear_combination -he


/-- On the free-datum marked disc the block energies are the old interaction plus its
quadratic correction. -/
theorem sum_blockEnergyOne_eq_interaction_add_delta
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
    (hX : XiCData S.G' S.a S.ν (k + 1) 1 eps H.D')
    (v : S.EC) (hv : liftC S.hG' v ∈ FlBall (stepG d L N₁ m₁ k ϱ) δ₁) :
    let B := composeData (S.hG.precedes S.hG' (le_refl (k + 1))) S.a
      (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D') H.D'
    let ψ₀ : S.EC := fun q => B.Ψ (unitRep (G' := S.G') q.1) q.2
    let Dv := H.dataUCH (ψ₀ + v)
    (∑ b : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))),
      blockEnergyOne S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν BG₂ κ eps k b
        (rawOf H.D', liftC S.hG' v)) =
      interactionV (S.hG.precedes S.hG' (le_refl (k + 1))) S.a S.ν
        (bgMultC S.G' S.a S.ν (bgC0 d L N) H.D')
        (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D')
        (compTangent S.hG S.hG' (le_refl (k + 1)) S.a
          (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D') H.D' Dv)
        (bgFieldC (stepG d L N₁ m₁ k ϱ) S.a S.ν (bgC0 d L N) Dv -
          (S.hG.precedes S.hG' (le_refl (k + 1))).restrictφ
            (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D')) +
      (1 / 2) * deltaForm (S.hG.precedes S.hG' (le_refl (k + 1))) S.a S.ν
        (bgMultC S.G' S.a S.ν (bgC0 d L N) H.D')
        (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D') (liftC S.hG' v) := by
  have hd := H.dataUCH_line_domain_of_flBall hC ha₁ hc7 hR hsmR hX v hv
  exact H.sum_blockEnergyOne_eq_interaction_add_delta_of_domain hC ha₁ hc7 hR
    hRs hsmall hnum hnum' hX v hv hd

end Balaban.Fluctuation.StepSettingH


namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Localization
  Balaban.Localization.I5Inhabited Balaban.Polymer Balaban.SmallField.Def6 Matrix Metric Set

namespace StepSetting

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))))

/-- **The block-energy total is `V + ½δ` in the two complex mark variables.**  Under the
hypotheses of `fderiv_mask_eq_neg_beta_deriv_energy_add_delta` (`MarkRealAt` supplies the domain
and the real clause), for complex `u, t` such that the lifted marked tangent lies in the ball
`FlBall`: `∑_b E_b(rawOf θ, lift v_{u,t}) = V^{(k)}(ψ^{(k)} + v_{u,t}) + ½ ⟨ψ', Δ^{(k)} ψ'⟩(v_{u,t})`. -/
theorem sum_blockEnergyOne_eq_VkC_add_delta {c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ}
    (hC : FlCore N S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (ha₁ : 0 < S.a₁) (hc7 : c7 d L N BG κ ≤ thm73C3 d L N) {R : ℝ} (hR : 2 ≤ R)
    (hRs : R * δ₁ ≤ deltaStar d L N) (hsmall : cK2 d L N * (R * δ₁) < bgC0 d L N / 2)
    (hnum : cK2 d L N * δ₁ ≤ c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hnum' : cK2' d L N (famConst d L BG₂ κ) * δ₁ ≤
      c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps S.D') (x : S.E) (hMR : S.MarkRealAt δ₁ R x)
    {u t : ℂ}
    (hball : liftC S.hG' (S.markedTangentC z u t x) ∈ FlBall (stepG d L N₁ m₁ k ϱ) δ₁) :
    (∑ b : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))),
      blockEnergyOne S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν BG₂ κ eps k b
        (rawOf S.D', liftC S.hG' (S.markedTangentC z u t x))) =
      S.VkC (S.psi0C + S.markedTangentC z u t x) +
        (1 / 2) * deltaForm (S.hG.precedes S.hG' (le_refl (k + 1))) (compWeight L S.a₁) S.ν
          (bgMultC S.G' (compWeight L S.a₁) S.ν (bgC0 d L N) S.D')
          (bgFieldC S.G' (compWeight L S.a₁) S.ν (bgC0 d L N) S.D')
          (liftC S.hG' (S.markedTangentC z u t x)) := by
  let H : StepSettingH S := S.withDatumH S.D'
  let v : S.EC := S.markedTangentC z u t x
  have hct : compTangent S.hG S.hG' (le_refl (k + 1)) S.a
      (bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D') S.D'
      (H.dataUCH (S.psi0C + v)) = liftC S.hG' v := by
    change compTangent S.hG S.hG' (le_refl (k + 1)) S.a
      (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D') H.D'
      (H.dataUCH (S.psi0C + v)) = liftC S.hG' v
    rw [H.compTangent_dataUCH]
    change liftC S.hG' ((S.psi0C + v) - S.psi0C) = liftC S.hG' v
    simp only [add_sub_cancel_left]
  obtain ⟨-, hreal, -⟩ := hMR
  obtain ⟨D, hh, hD3, hdisc'⟩ := hreal _ hball (isLayerConstant_liftC S.hG S.hG' _)
  have hDv : D = H.dataUCH (S.psi0C + v) := by
    refine BgData.eq_of_raw (Prod.ext ?_ ?_)
    · funext y i
      have he := congrFun (congrFun (hD3.trans hct.symm) y) i
      dsimp only [compTangent] at he
      exact sub_left_inj.mp he
    · funext y i
      exact (hh y i).trans (H.dataUCH_h (S.psi0C + v) y i).symm
  have hline :
      let B := composeData (S.hG.precedes S.hG' (le_refl (k + 1))) S.a
        (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D') H.D'
      let ψ₀ : S.EC := fun q => B.Ψ (unitRep (G' := S.G') q.1) q.2
      let Dv := H.dataUCH (ψ₀ + v)
      ∀ r : ℂ, ‖r‖ < R →
        InUnionDomainC (stepG d L N₁ m₁ k ϱ) (bgC0 d L N) (bgC1 d L N) S.ν
          (B.lineAt (tangentData Dv B) r) := by
    dsimp only
    change ∀ r : ℂ, ‖r‖ < R →
      InUnionDomainC (stepG d L N₁ m₁ k ϱ) (bgC0 d L N) (bgC1 d L N) S.ν
        (S.psiKdC.lineAt (tangentData (H.dataUCH (S.psi0C + v)) S.psiKdC) r)
    rw [← hDv]
    exact hdisc'
  have he := H.sum_blockEnergyOne_eq_interaction_add_delta_of_domain hC ha₁ hc7 hR
    hRs hsmall hnum hnum' hD v hball hline
  have hI := interactionOne_eq S.hG S.hG' (le_refl (k + 1)) hD
    (D := H.dataUCH (S.psi0C + v)) (fun y i => H.dataUCH_h (S.psi0C + v) y i)
  have hV := S.VkC_psi0C_add_eq_interactionOne hD v
  dsimp only [H, StepSetting.withDatumH] at he
  change (∑ b : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))),
      blockEnergyOne S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν BG₂ κ eps k b
        (rawOf S.D', liftC S.hG' v)) =
    interactionV (S.hG.precedes S.hG' (le_refl (k + 1))) S.a S.ν
      (bgMultC S.G' S.a S.ν (bgC0 d L N) S.D')
      (bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D')
      (compTangent S.hG S.hG' (le_refl (k + 1)) S.a
        (bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D') S.D'
        (H.dataUCH (S.psi0C + v)))
      (bgFieldC (stepG d L N₁ m₁ k ϱ) S.a S.ν (bgC0 d L N)
        (H.dataUCH (S.psi0C + v)) -
        (S.hG.precedes S.hG' (le_refl (k + 1))).restrictφ
          (bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D')) +
      (1 / 2) * deltaForm (S.hG.precedes S.hG' (le_refl (k + 1))) S.a S.ν
        (bgMultC S.G' S.a S.ν (bgC0 d L N) S.D')
        (bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D') (liftC S.hG' v) at he
  rw [hct] at he hI
  unfold StepSetting.a at he
  change (∑ b : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))),
      blockEnergyOne S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν BG₂ κ eps k b
        (rawOf S.D', liftC S.hG' v)) = _
  rw [he]
  rw [← hI, ← hV]

end StepSetting


end Balaban.Fluctuation
