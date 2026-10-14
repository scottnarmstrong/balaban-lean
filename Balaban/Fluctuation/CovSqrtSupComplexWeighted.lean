/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.CovarianceSup
public import Balaban.Localization.DecoupledCovAnalyticFull

/-!
# Weighted decay of the unit-lattice resolvent at complex decoupling parameters

The proof of `cov_weighted_bound` (the case `s ≡ 1`) uses only `Gsx_vec_bounds` and
`decPi_weighted_bounds`, which hold for every `s` with `|s_P| ≤ e^κ`. Here the same argument is
run at general `(κ, s)`: for `x ≥ 0` and an Agmon weight `e^{ε r}`,

* `covC_wA`: `‖e^{ε ρ} A_x h‖ ≤ 2 e^{2dε} (a_k + x)⁻¹ ‖e^{ε ρ} h‖`;
* `covC_wT`: `‖e^{ε ρ} (C_x(s) - A_x) h‖ ≤ T (a_k + x)⁻² ‖e^{ε ρ} h‖`, `T = covTConst …`;
* `covC_wC`: `‖e^{ε ρ} C_x(s) h‖ ≤ K₁ (a_k + x)⁻¹ ‖e^{ε ρ} h‖`;

and the resulting entry decay `covC_entry_of_weighted`.
-/

@[expose] public section

open Balaban Balaban.Localization Balaban.Multiscale Finset Matrix

namespace Balaban.Fluctuation

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
  {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
  {r : CTorus d L N₁ m₁ (k + 1) → ℝ} {a : ℕ → ℝ} {aT ν : ℝ} {α : G.Ω 1 → ℂ} {δ κ : ℝ}
  {s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ}
  {φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ}

/-- The constant of the weighted bound of `C_x(s) - A_x`. -/
noncomputable def covTConst (d L : ℕ) (ak ε κ : ℝ) : ℝ :=
  4 * ak ^ 2 * (L : ℝ) ^ 2 * (Real.sqrt (92 * valConstX d) * Real.exp (N0 d L * κ)) *
    Real.exp (ε * (2 * d)) ^ 3

/-- The constant of the weighted bound of `C_x(s)`. -/
noncomputable def covC1Const (d L : ℕ) (ak ε κ : ℝ) : ℝ :=
  2 * Real.exp (ε * (2 * d)) + covTConst d L ak ε κ / ak

omit [NeZero N₁] [NeZero L] in
theorem covTConst_nonneg (d L : ℕ) (ak ε κ : ℝ) : 0 ≤ covTConst d L ak ε κ := by
  have : 0 ≤ valConstX d := by unfold valConstX; positivity
  unfold covTConst
  positivity

omit [NeZero N₁] [NeZero L] in
theorem covC1Const_nonneg (d L : ℕ) {ak : ℝ} (hak : 0 < ak) (ε κ : ℝ) :
    0 ≤ covC1Const d L ak ε κ := by
  have := covTConst_nonneg d L ak ε κ
  unfold covC1Const
  positivity

theorem covC_wA {ε : ℝ} (hr : XWeight G ε r) {c b x : ℝ} (hcx : 0 < c + x) (hb : 0 ≤ b)
    (g : unitPts G × Fin N → ℂ) :
    n2 (covWVec ε (fun b : unitPts G => unitRho r b.1)
        (covA c b x (liftOp N (unitP G)) *ᵥ g)) ≤
      2 * Real.exp (ε * (2 * d)) * (c + x)⁻¹ *
        n2 (covWVec ε (fun b : unitPts G => unitRho r b.1) g) := by
  have hU := (isUnitLatticeB_unit (G := G)).toIsUnitLattice
  have hA1p : 0 ≤ 2 * Real.exp (ε * (2 * d)) * (c + x)⁻¹ := by
    have := inv_pos.2 hcx
    positivity
  have h1 := sum_w_covA_le (ρ := fun b : unitPts G => unitRho r b.1) (ε := ε) (c₀ := 2 * d)
    hr.ε0 (by positivity) (fun b b' hbb => cov_unitRho_P hr.agm b b' hbb) hU.herm hU.idem
    (fun b b' => unitP_nonneg_real b b') hcx hb g
  exact (sqNorm_le_iff hA1p).1 (by simpa only [covWVec_sqNorm] using h1)

section CoverSup

variable {Cx : ℝ} (Hc : ∀ x, 0 ≤ x → Dec2.XData (coverOf G) G a aT ν x α κ s Cx)
  (hφ : IsConstraintField G δ φ) (hδ : 0 ≤ δ) (hsm : δ ^ 2 * smallConstX d L κ ≤ 1 / 4)

include Hc hφ hδ hsm in
theorem covC_wT_cover {x : ℝ} (hx : 0 ≤ x) {ε : ℝ} (hr : XWeight G ε r)
    (h : unitPts G × Fin N → ℂ) :
    n2 (covWVec ε (fun b : unitPts G => unitRho r b.1)
        ((decCov G a aT x ν α s φ (unitQ G) (unitP G) -
          covA (a k) (aT / (L : ℝ) ^ 2) x (liftOp N (unitP G))) *ᵥ h)) ≤
      covTConst d L (a k) ε κ * ((a k + x)⁻¹) ^ 2 *
        n2 (covWVec ε (fun b : unitPts G => unitRho r b.1) h) := by
  classical
  have D := Hc x hx
  have hU := (isUnitLatticeB_unit (G := G)).toIsUnitLattice
  have hk := D.st.hk
  have hak : a k ∈ Set.Icc (1 / 2 : ℝ) 2 := D.st.ha k hk le_rfl
  have hcx : 0 < a k + x := by have := D.x0; linarith [hak.1]
  have hb : 0 ≤ aT / (L : ℝ) ^ 2 := by
    have := D.st.haT1
    positivity
  set ρ : unitPts G → ℝ := fun b => unitRho r b.1 with hρ
  set Av := covA (a k) (aT / (L : ℝ) ^ 2) x (liftOp N (unitP G)) with hAv
  set cs : ℂ := (((a k) ^ 2 / (L : ℝ) ^ (2 * k) : ℝ) : ℂ) with hcs
  set Λ : ℝ := (L : ℝ) ^ (k + 1) with hΛ
  set α0 : ℝ := (a k + x)⁻¹ with hα0
  have hα0p : 0 < α0 := inv_pos.2 hcx
  have hε0 := hr.ε0
  set A1 : ℝ := 2 * Real.exp (ε * (2 * d)) * α0 with hA1
  have hA1p : 0 ≤ A1 := by positivity
  have hAv' : ∀ g : unitPts G × Fin N → ℂ,
      n2 (covWVec ε ρ (Av *ᵥ g)) ≤ A1 * n2 (covWVec ε ρ g) := fun g =>
    covC_wA hr hcx hb g
  have hdec : (decCov G a aT x ν α s φ (unitQ G) (unitP G) - Av) *ᵥ h =
      cs • (Av *ᵥ (liftRect N (unitQ G) *ᵥ (decZ G a aT x ν α s φ *ᵥ
        ((liftRect N (unitQ G))ᵀ *ᵥ (Av *ᵥ h))))) := by
    unfold decCov decZ
    rw [add_sub_cancel_left, Matrix.smul_mulVec]
    simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
    rfl
  set z := Av *ᵥ h with hz
  set w := (liftRect N (unitQ G))ᵀ *ᵥ z with hw
  set u := decZ G a aT x ν α s φ *ᵥ w with hu
  set v := liftRect N (unitQ G) *ᵥ u with hv
  have hz1 : n2 (covWVec ε ρ z) ≤ A1 * n2 (covWVec ε ρ h) := hAv' h
  have hsrc := cov_vecSrc_QT_le (N := N) hr.agm hr.ε0 z
  have hZ : vecM G ε r u ≤ 92 * (valConstX d * Real.exp (N0 d L * κ) ^ 2) * vecSrc G ε r w := by
    have hG := Gsx_vec_bounds_cover D hr w
    have hP := decPi_weighted_bounds_cover D hr hφ hδ hsm w
    have hsub : u = liftOp N (Gsx G a aT x ν α s) *ᵥ w - decPi G a aT x ν α s φ *ᵥ w := by
      rw [hu]; unfold decZ; rw [Matrix.sub_mulVec]
    have h1 := vecM_sub_le (G := G) ε r (liftOp N (Gsx G a aT x ν α s) *ᵥ w)
      (decPi G a aT x ν α s φ *ᵥ w)
    rw [← hsub] at h1
    nlinarith [hG.1, hP.1]
  have hv1 : Green.sqNorm (covWVec ε ρ v) ≤ Λ ^ 2 * vecM G ε r u := by
    rw [covWVec_sqNorm]
    exact sum_wQ_vec_le hU (fun b y => unitQ_nonneg_real b y)
      (fun b y hby => cov_unitRho_Q b y hby) hr.ε0 u
  have hV0 : 0 ≤ valConstX d := by unfold valConstX; positivity
  set S : ℝ := Real.sqrt (92 * valConstX d) * Real.exp (N0 d L * κ) with hS
  have hS0 : 0 ≤ S := by positivity
  have hS2 : S ^ 2 = 92 * (valConstX d * Real.exp (N0 d L * κ) ^ 2) := by
    rw [hS, mul_pow, Real.sq_sqrt (by positivity)]; ring
  set E : ℝ := Real.exp (ε * (2 * d)) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hvz : n2 (covWVec ε ρ v) ≤ (Λ ^ 2 * S * E) * n2 (covWVec ε ρ z) := by
    rw [← sqNorm_le_iff (by positivity)]
    have hsrc' : vecSrc G ε r w ≤ Λ ^ 2 * E ^ 2 * Green.sqNorm (covWVec ε ρ z) := by
      rw [covWVec_sqNorm]; exact hsrc
    have hΛ0 : 0 ≤ Λ ^ 2 := by positivity
    have hC0 : 0 ≤ 92 * (valConstX d * Real.exp (N0 d L * κ) ^ 2) := by positivity
    calc Green.sqNorm (covWVec ε ρ v) ≤ Λ ^ 2 * vecM G ε r u := hv1
      _ ≤ Λ ^ 2 * (92 * (valConstX d * Real.exp (N0 d L * κ) ^ 2) * vecSrc G ε r w) := by
          gcongr
      _ ≤ Λ ^ 2 * (92 * (valConstX d * Real.exp (N0 d L * κ) ^ 2) *
            (Λ ^ 2 * E ^ 2 * Green.sqNorm (covWVec ε ρ z))) := by gcongr
      _ = (Λ ^ 2 * S * E) ^ 2 * Green.sqNorm (covWVec ε ρ z) := by
          rw [mul_pow, mul_pow, hS2]; ring
  have hy2 : n2 (covWVec ε ρ (Av *ᵥ v)) ≤ A1 * n2 (covWVec ε ρ v) := hAv' v
  have hcsn : ‖cs‖ = (a k) ^ 2 / (L : ℝ) ^ (2 * k) := by
    rw [hcs, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hcsΛ : ‖cs‖ * Λ ^ 2 = (a k) ^ 2 * (L : ℝ) ^ 2 := by
    have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    rw [hcsn, hΛ]; field_simp; ring
  rw [hdec, covWVec_smul, n2_smul]
  have hcs0 : 0 ≤ ‖cs‖ := norm_nonneg _
  have hn0 := n2_nonneg (covWVec ε ρ h)
  have hz0 := n2_nonneg (covWVec ε ρ z)
  have hv0 := n2_nonneg (covWVec ε ρ v)
  calc ‖cs‖ * n2 (covWVec ε ρ (Av *ᵥ v)) ≤ ‖cs‖ * (A1 * ((Λ ^ 2 * S * E) * n2 (covWVec ε ρ z))) :=
        mul_le_mul_of_nonneg_left (hy2.trans (mul_le_mul_of_nonneg_left hvz hA1p)) hcs0
    _ ≤ ‖cs‖ * (A1 * ((Λ ^ 2 * S * E) * (A1 * n2 (covWVec ε ρ h)))) := by gcongr
    _ = (‖cs‖ * Λ ^ 2) * S * E * A1 ^ 2 * n2 (covWVec ε ρ h) := by ring
    _ = _ := by
        rw [hcsΛ, hA1]
        unfold covTConst
        rw [← hE, ← hS]
        ring

include Hc hφ hδ hsm in
theorem covC_wC_cover {x : ℝ} (hx : 0 ≤ x) {ε : ℝ} (hr : XWeight G ε r)
    (h : unitPts G × Fin N → ℂ) :
    n2 (covWVec ε (fun b : unitPts G => unitRho r b.1)
        (decCov G a aT x ν α s φ (unitQ G) (unitP G) *ᵥ h)) ≤
      covC1Const d L (a k) ε κ * (a k + x)⁻¹ *
        n2 (covWVec ε (fun b : unitPts G => unitRho r b.1) h) := by
  have D := Hc x hx
  have hak : a k ∈ Set.Icc (1 / 2 : ℝ) 2 := D.st.ha k D.st.hk le_rfl
  have hak0 : 0 < a k := by linarith [hak.1]
  have hcx : 0 < a k + x := by linarith
  have hb : 0 ≤ aT / (L : ℝ) ^ 2 := by
    have := D.st.haT1
    positivity
  have hα : (a k + x)⁻¹ ≤ (a k)⁻¹ := inv_anti₀ hak0 (by linarith)
  have hα0 : 0 < (a k + x)⁻¹ := inv_pos.2 hcx
  have hT := covC_wT_cover Hc hφ hδ hsm hx hr h
  have hA := covC_wA (N := N) hr hcx hb h
  have hsplit : decCov G a aT x ν α s φ (unitQ G) (unitP G) *ᵥ h =
      covA (a k) (aT / (L : ℝ) ^ 2) x (liftOp N (unitP G)) *ᵥ h +
      (decCov G a aT x ν α s φ (unitQ G) (unitP G) -
        covA (a k) (aT / (L : ℝ) ^ 2) x (liftOp N (unitP G))) *ᵥ h := by
    rw [← Matrix.add_mulVec]; congr 1; abel
  rw [hsplit, covWVec_add]
  refine (n2_add_le _ _).trans ?_
  have hn0 := n2_nonneg (covWVec ε (fun b : unitPts G => unitRho r b.1) h)
  have hT0 := covTConst_nonneg d L (a k) ε κ
  have h2 : covTConst d L (a k) ε κ * ((a k + x)⁻¹) ^ 2 ≤
      covTConst d L (a k) ε κ / a k * (a k + x)⁻¹ := by
    have : ((a k + x)⁻¹) ^ 2 ≤ (a k)⁻¹ * (a k + x)⁻¹ := by
      rw [sq]; exact mul_le_mul_of_nonneg_right hα hα0.le
    calc _ ≤ covTConst d L (a k) ε κ * ((a k)⁻¹ * (a k + x)⁻¹) :=
          mul_le_mul_of_nonneg_left this hT0
      _ = _ := by ring
  calc _ ≤ 2 * Real.exp (ε * (2 * d)) * (a k + x)⁻¹ *
        n2 (covWVec ε (fun b : unitPts G => unitRho r b.1) h) +
      covTConst d L (a k) ε κ * ((a k + x)⁻¹) ^ 2 *
        n2 (covWVec ε (fun b : unitPts G => unitRho r b.1) h) := add_le_add hA hT
    _ ≤ _ := by
        unfold covC1Const
        nlinarith [mul_le_mul_of_nonneg_right h2 hn0]

end CoverSup

section Main

variable (H : ∀ x, 0 ≤ x → XData G a aT ν x α κ s) (hφ : IsConstraintField G δ φ) (hδ : 0 ≤ δ)
  (hsm : δ ^ 2 * smallConstX d L κ ≤ 1 / 4)

include H hφ hδ hsm in
theorem covC_wT {x : ℝ} (hx : 0 ≤ x) {ε : ℝ} (hr : XWeight G ε r)
    (h : unitPts G × Fin N → ℂ) :
    n2 (covWVec ε (fun b : unitPts G => unitRho r b.1)
        ((decCov G a aT x ν α s φ (unitQ G) (unitP G) -
          covA (a k) (aT / (L : ℝ) ^ 2) x (liftOp N (unitP G))) *ᵥ h)) ≤
      covTConst d L (a k) ε κ * ((a k + x)⁻¹) ^ 2 *
        n2 (covWVec ε (fun b : unitPts G => unitRho r b.1) h) :=
  covC_wT_cover (fun x hx => (H x hx).toCover) hφ hδ hsm hx hr h

include H hφ hδ hsm in
theorem covC_wC {x : ℝ} (hx : 0 ≤ x) {ε : ℝ} (hr : XWeight G ε r)
    (h : unitPts G × Fin N → ℂ) :
    n2 (covWVec ε (fun b : unitPts G => unitRho r b.1)
        (decCov G a aT x ν α s φ (unitQ G) (unitP G) *ᵥ h)) ≤
      covC1Const d L (a k) ε κ * (a k + x)⁻¹ *
        n2 (covWVec ε (fun b : unitPts G => unitRho r b.1) h) :=
  covC_wC_cover (fun x hx => (H x hx).toCover) hφ hδ hsm hx hr h

end Main

end Balaban.Fluctuation
