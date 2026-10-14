/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.DecoupledCovX0Sup
public import Balaban.Localization.DecoupledCovAnalyticFull
public import Balaban.Fluctuation.CovSqrtSupComplexDec
public import Balaban.Fluctuation.LocalFluctGen
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The decoupled square root on the cover form: analyticity and the sup bound

The square root `C^{1/2}(s)` of the decoupled covariance (`decCovSqrt`) at a generating set `G`
was proved analytic on the polydisc (I-4c (iii), `analyticOnNhd_decCovSqrt_entry`) and bounded
(`decCovSqrt_bound`) for the standing data `XSetting G …`, which is built on `DGSetting`.  The
literal local generator `𝔹(Y) = localB … Y` carries no `DGSetting`, but its cover satisfies
`Dec2.XCover (coverOf 𝔹) 𝔹` (`localB_xCover`).  Here the two statements are proved for the data
`Dec2.XCover (coverOf G) G …` (cover form), and specialized to `localB`.

* `rectAt_decCov_full_cover`: the entries of `C_x(s)` are analytic in `(s, φ₀, α₀)` on `DecDom`;
* `analyticOnNhd_decCovSqrt_entry_cover`: the same for the entries of `C^{1/2}(s)`;
* `decCovSqrt_bound_cover`: the operator bound `‖C^{1/2}(s) f‖ ≤ B₅ ‖f‖` for the data of the
  cover pair;
* `covC_sqrt_supNorm_cover`, `decCovSqrt_supNorm_cover`: the sup bound `K c`,
  `K = covSupConstC d L N (a k) κ`, on `DecDom`;
* `localLift_mem_flBallLC_of_top_empty`, `localHatLift_mem_flBallLC_cover`: the local hat lift
  (the hat variable on the unit lattice of `G`, `ψ' = cc C^{1/2}(s) ψ̂` extended by zero off the
  unit blocks of `G`) is a block fluctuation of every generating set without layer `k + 1`;
* `localB_analyticOnNhd_decCovSqrt_entry`, `localB_localHatLift_mem_flBallLC`: the instances at the
  literal local generator, at the unit lattice `(unitQ, unitP)`.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Finset Matrix MeasureTheory Set Filter Topology
open scoped Real

section Cover

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} {a : ℕ → ℝ} {aT ν Cx : ℝ}

/-- The data `Dec2.XData` of the pair `(coverOf G, G)` at a point of the polydisc `DecDom`. -/
theorem xData_cover_of_mem (S : Dec2.XCover (coverOf G) G a aT ν Cx) (hCx : 0 ≤ Cx) {x : ℝ}
    (hx : 0 ≤ x) {κ : ℝ} (hκ : 0 ≤ κ)
    (hM : Dec2.cstarX d L Cx * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δ : ℝ} {e : DecData G N}
    (he : e ∈ DecDom G N κ δ) :
    Dec2.XData (coverOf G) G a aT ν x e.2.2 κ (extS G e.1) Cx := by
  have hα : AdmPot G e.2.2 := fun w => (he.2.2 w).le
  have hs : ∀ P, ‖extS G e.1 P‖ ≤ Real.exp κ := by
    intro P
    unfold extS
    split_ifs with h
    · exact (he.1 ⟨P, h⟩).le
    · simpa using Real.one_le_exp hκ
  exact ⟨S, hCx, hα, hx, hκ, hM, hs⟩

/-- **I-4c (iii), the integrand, cover form**: for every `x ≥ 0` the entries of `C_x(s)` are
analytic in `(s, φ₀, α₀)` on `DecDom`. -/
theorem rectAt_decCov_full_cover {x : ℝ} {κι : Type*} [Fintype κι] [DecidableEq κι]
    {Q : Matrix κι (G.Ω 1) ℂ} {P : Matrix κι κι ℂ}
    (S : Dec2.XCover (coverOf G) G a aT ν Cx) (hCx : 0 ≤ Cx) (hx : 0 ≤ x) {κ : ℝ} (hκ : 0 ≤ κ)
    (hM : Dec2.cstarX d L Cx * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δ : ℝ} (hδ : 0 ≤ δ)
    (hsm : δ ^ 2 * smallConstX d L κ ≤ 1 / 4) {e : DecData G N} (he : e ∈ DecDom G N κ δ) :
    RectAt (fun p : DecData G N => decCov G a aT x ν p.2.2 (extS G p.1) p.2.1 Q P) e := by
  have hα : AdmPot G e.2.2 := fun w => (he.2.2 w).le
  have D := xData_cover_of_mem (N := N) S hCx hx hκ hM he
  have hφ : IsConstraintField G δ e.2.1 := he.2.1.toIsConstraintField
  have hpr : AnalyticAt ℂ (fun p : DecData G N => ((p.1, p.2.2) : DecParams G × (G.Ω 1 → ℂ))) e :=
    AnalyticAt.prod analyticAt_fst (analyticAt_snd.comp analyticAt_snd)
  have hHx : RectAt (fun p : DecData G N => xDirichletOperator G a aT x ν p.2.2) e :=
    RectAt.comp' (f := fun p : DecData G N => ((p.1, p.2.2) : DecParams G × (G.Ω 1 → ℂ)))
      (rectAt_xDirichlet (G := G) a aT x ν ((e.1, e.2.2) : DecParams G × (G.Ω 1 → ℂ))) hpr
  have hGs : RectAt (fun p : DecData G N => Gsx G a aT x ν p.2.2 (extS G p.1)) e :=
    RectAt.comp' (f := fun p : DecData G N => ((p.1, p.2.2) : DecParams G × (G.Ω 1 → ℂ)))
      (Dec2.matAt_Gsx S hx hα D.isUnit_one_sub) hpr
  have hGl := hGs.liftOp (N := N)
  have hHl := hHx.liftOp (N := N)
  have hF := rectAt_fieldMul (G := G) (N := N) e
  have hK : RectAt (fun p : DecData G N =>
      commK (xDirichletOperator G a aT x ν p.2.2) (restrictField G p.2.1)) e := by
    unfold commK
    exact (hF.transpose'.mul hHl).sub (hHx.mul hF.transpose')
  have hMa : RectAt (fun p : DecData G N =>
      decM G a aT x ν p.2.2 (extS G p.1) p.2.1) e := by
    unfold decM constraintM
    exact (hF.transpose'.mul hF).sub ((hK.mul hGl).mul hF)
  have hNa : RectAt (fun p : DecData G N =>
      decN G a aT x ν p.2.2 (extS G p.1) p.2.1) e := by
    unfold decN constraintN
    exact hF.transpose'.sub (hK.mul hGl)
  have hdet : (decM G a aT x ν e.2.2 (extS G e.1) e.2.1).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).1 (decM_isUnit_cover D hφ hδ hsm)).ne_zero
  have hMi := hMa.inv hdet
  have hPi : RectAt (fun p : DecData G N =>
      decPi G a aT x ν p.2.2 (extS G p.1) p.2.1) e := by
    unfold decPi
    exact (((hGl.mul hF).mul hMi).mul hNa)
  unfold decCov
  have hA := RectAt.const (E := DecData G N)
    (covA (a k) (aT / (L : ℝ) ^ 2) x (liftOp N P)) e
  refine hA.add (RectAt.smul_const _ ?_)
  exact (((hA.mul (RectAt.const _ e)).mul (hGl.sub hPi)).mul (RectAt.const _ e)).mul hA

variable {κι : Type*} [Fintype κι] [DecidableEq κι] {Q : Matrix κι (G.Ω 1) ℂ}
  {P : Matrix κι κι ℂ}

/-- **I-4c (iii), the square root, cover form**: every entry of `C^{1/2}(s)` is analytic in
`(s, φ₀, α₀)` on the open domain `DecDom`, for the data `Dec2.XCover (coverOf G) G …`. -/
theorem analyticOnNhd_decCovSqrt_entry_cover (S : Dec2.XCover (coverOf G) G a aT ν Cx)
    (hCx : 0 ≤ Cx) {κ : ℝ} (hκ : 0 ≤ κ)
    (hM : Dec2.cstarX d L Cx * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δ : ℝ} (hδ : 0 ≤ δ)
    (hsm : δ ^ 2 * smallConstX d L κ ≤ 1 / 4) (hU : IsUnitLattice G Q P) (p q : κι × Fin N) :
    AnalyticOnNhd ℂ (fun e : DecData G N =>
      decCovSqrt G a aT ν e.2.2 (extS G e.1) e.2.1 Q P p q) (DecDom G N κ δ) := by
  have hak : 0 < a k := by
    have := S.ha k S.hk le_rfl
    linarith [this.1]
  have hB := covB4_nonneg d L (a k) κ
  have hint : AnalyticOnNhd ℂ (fun e : DecData G N => ∫ y in Ioi (0 : ℝ),
      ((y ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * decCov G a aT y ν e.2.2 (extS G e.1) e.2.1 Q P p q)
      (DecDom G N κ δ) := by
    refine analyticOnNhd_integral_Ioi (g := sqrtDom d L (a k) κ) (isOpen_decDom κ δ) ?_ ?_ ?_ ?_ ?_
    · intro y hy e he
      exact analyticAt_const.mul (rectAt_decCov_full_cover S hCx hy.le hκ hM hδ hsm he p q)
    · intro e he
      have hfam := fun (x : ℝ) (hx : 0 ≤ x) => xData_cover_of_mem (N := N) S hCx hx hκ hM he
      refine ContinuousOn.mul ?_
        ((continuousOn_decCov_entry_cover hfam he.2.1.toIsConstraintField hδ hsm p q).mono
          Ioi_subset_Ici_self)
      refine Complex.continuous_ofReal.comp_continuousOn ?_
      exact fun y hy =>
        (Real.continuousAt_rpow_const _ _ (Or.inl (mem_Ioi.mp hy).ne')).continuousWithinAt
    · unfold sqrtDom
      refine ContinuousOn.add ?_ (ContinuousOn.mul continuousOn_const ?_)
      · refine ContinuousOn.mul ?_ ?_
        · exact fun y hy =>
            (Real.continuousAt_rpow_const _ _ (Or.inl (mem_Ioi.mp hy).ne')).continuousWithinAt
        · exact continuousOn_inv_add_Ioi hak
      · refine ContinuousOn.mul ?_ ?_
        · exact fun y hy =>
            (Real.continuousAt_rpow_const _ _ (Or.inl (mem_Ioi.mp hy).ne')).continuousWithinAt
        · exact (continuousOn_inv_add_Ioi hak).pow 2
    · exact integrable_sqrtDom hak d L κ
    · intro y hy e he
      have hfam := fun (x : ℝ) (hx : 0 ≤ x) => xData_cover_of_mem (N := N) S hCx hx hκ hM he
      have h3 : 0 < y ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hy _
      simp only [norm_mul, Complex.norm_real, Real.norm_of_nonneg h3.le]
      have := entry_decCov_le_cover hfam he.2.1.toIsConstraintField hδ hsm hU hy.le p q
      calc y ^ (-(1 / 2 : ℝ)) * ‖decCov G a aT y ν e.2.2 (extS G e.1) e.2.1 Q P p q‖
          ≤ y ^ (-(1 / 2 : ℝ)) * ((a k + y)⁻¹ + covB4 d L (a k) κ * ((a k + y)⁻¹) ^ 2) :=
            mul_le_mul_of_nonneg_left this h3.le
        _ = sqrtDom d L (a k) κ y := by unfold sqrtDom; ring
  intro e he
  have := (analyticAt_const (v := ((1 / Real.pi : ℝ) : ℂ))).mul (hint e he)
  refine this.congr (Filter.Eventually.of_forall fun e' => ?_)
  simp only [decCovSqrt, intMat, decSqrtInt, Matrix.smul_apply, smul_eq_mul, Matrix.smul_apply]
  rfl

section Bound

variable {α : G.Ω 1 → ℂ} {κ δ : ℝ} {s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ}
  {φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ}
  {κι : Type*} [Fintype κι] [DecidableEq κι] {Q : Matrix κι (G.Ω 1) ℂ} {P : Matrix κι κι ℂ}

/-- **I-4c (ii), the square root, cover form**: `‖C^{1/2}(s) f‖ ≤ B₅ ‖f‖` for the data
`Dec2.XData (coverOf G) G …` (no `DGSetting`). -/
theorem decCovSqrt_bound_cover
    (hfam : ∀ x, 0 ≤ x → Dec2.XData (coverOf G) G a aT ν x α κ s Cx)
    (hφ : IsConstraintField G δ φ) (hδ : 0 ≤ δ) (hsm : δ ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hU : IsUnitLattice G Q P) (f : κι × Fin N → ℂ) :
    Green.sqNorm (decCovSqrt G a aT ν α s φ Q P *ᵥ f) ≤
      (covB5 d L (a k) κ) ^ 2 * Green.sqNorm f := by
  have hak := aux_hak_cover hfam
  have hB := covB4_nonneg d L (a k) κ
  have hmain := sqNorm_intMat_le (volume.restrict (Ioi (0 : ℝ)))
    (decSqrtInt G a aT ν α s φ Q P) (fun p q => integrable_decSqrtInt_cover hfam hφ hδ hsm hU p q)
    (sqrtDom d L (a k) κ) (integrable_sqrtDom hak d L κ)
    ((ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun x hx =>
      sqrtDom_nonneg d L (a k) κ (mem_Ioi.mp hx) hak))
    ((ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun x hx f => by
      have hx0 : 0 < x := mem_Ioi.mp hx
      have h1 := standing_decCov_le_cover hfam hφ hδ hsm hU hx0.le f
      have h3 : 0 < x ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hx0 _
      unfold decSqrtInt
      rw [Matrix.smul_mulVec, sqNorm_smul, Complex.norm_real, Real.norm_of_nonneg h3.le]
      have e : sqrtDom d L (a k) κ x = x ^ (-(1 / 2 : ℝ)) *
          ((a k + x)⁻¹ + covB4 d L (a k) κ * ((a k + x)⁻¹) ^ 2) := by
        unfold sqrtDom; ring
      rw [e, mul_pow, mul_assoc]
      exact mul_le_mul_of_nonneg_left h1 (sq_nonneg _))) f
  set I := intMat (volume.restrict (Ioi (0 : ℝ))) (decSqrtInt G a aT ν α s φ Q P) with hI
  set Gi := ∫ x, sqrtDom d L (a k) κ x ∂(volume.restrict (Ioi (0 : ℝ))) with hGi
  have hGi0 : 0 ≤ Gi := integral_nonneg_of_ae
    ((ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun x hx =>
      sqrtDom_nonneg d L (a k) κ (mem_Ioi.mp hx) hak))
  have hGi1 : Gi ≤ π / Real.sqrt (a k) * (1 + covB4 d L (a k) κ / a k) := by
    have e : Gi = (∫ x in Ioi (0 : ℝ), x ^ (-(1 / 2 : ℝ)) * ((a k) + x)⁻¹) +
        covB4 d L (a k) κ * ∫ x in Ioi (0 : ℝ), x ^ (-(1 / 2 : ℝ)) * (((a k) + x)⁻¹) ^ 2 := by
      rw [hGi]
      unfold sqrtDom
      rw [integral_add (integrableOn_rpow_inv_add hak)
        ((integrableOn_rpow_inv_add_sq hak).const_mul _), integral_const_mul]
    rw [e, integral_rpow_inv_add hak]
    have := integral_rpow_inv_add_sq_le hak
    have h2 := mul_le_mul_of_nonneg_left this hB
    have : π / Real.sqrt (a k) * (1 + covB4 d L (a k) κ / a k) =
        π / Real.sqrt (a k) + covB4 d L (a k) κ * ((a k)⁻¹ * (π / Real.sqrt (a k))) := by
      field_simp
    rw [this]
    linarith
  have hpi : 0 < π := Real.pi_pos
  have hB5 : (1 / π) * Gi ≤ covB5 d L (a k) κ := by
    unfold covB5
    calc (1 / π) * Gi ≤ (1 / π) * (π / Real.sqrt (a k) * (1 + covB4 d L (a k) κ / a k)) :=
          mul_le_mul_of_nonneg_left hGi1 (by positivity)
      _ = _ := by field_simp
  unfold decCovSqrt
  rw [Matrix.smul_mulVec, sqNorm_smul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have h0 : 0 ≤ (1 / π) * Gi := by positivity
  have h2 : ((1 / π) * Gi) ^ 2 ≤ (covB5 d L (a k) κ) ^ 2 := pow_le_pow_left₀ h0 hB5 2
  have hs0 := sqNorm_nonneg' f
  calc (1 / π) ^ 2 * Green.sqNorm (I *ᵥ f) ≤ (1 / π) ^ 2 * (Gi ^ 2 * Green.sqNorm f) :=
        mul_le_mul_of_nonneg_left hmain (by positivity)
    _ = ((1 / π) * Gi) ^ 2 * Green.sqNorm f := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right h2 hs0

end Bound

end Cover

end Balaban.Localization

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Multiscale Finset Matrix MeasureTheory Set

section CoverSup

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
  {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
  {a : ℕ → ℝ} {aT ν Cx : ℝ} {α : G.Ω 1 → ℂ} {δ κ : ℝ}
  {s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ}
  {φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ}
  {r : CTorus d L N₁ m₁ (k + 1) → ℝ}

variable (H : ∀ x, 0 ≤ x → Dec2.XData (coverOf G) G a aT ν x α κ s Cx)
  (hφ : IsConstraintField G δ φ) (hδ : 0 ≤ δ) (hsm : δ ^ 2 * smallConstX d L κ ≤ 1 / 4)

include H hφ hδ hsm in
theorem covC_wT_cover {x : ℝ} (hx : 0 ≤ x) {ε : ℝ} (hr : XWeight G ε r)
    (h : unitPts G × Fin N → ℂ) :
    n2 (covWVec ε (fun b : unitPts G => unitRho r b.1)
        ((decCov G a aT x ν α s φ (unitQ G) (unitP G) -
          covA (a k) (aT / (L : ℝ) ^ 2) x (liftOp N (unitP G))) *ᵥ h)) ≤
      covTConst d L (a k) ε κ * ((a k + x)⁻¹) ^ 2 *
        n2 (covWVec ε (fun b : unitPts G => unitRho r b.1) h) := by
  classical
  have D := H x hx
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

include H hφ hδ hsm in
theorem covC_wC_cover {x : ℝ} (hx : 0 ≤ x) {ε : ℝ} (hr : XWeight G ε r)
    (h : unitPts G × Fin N → ℂ) :
    n2 (covWVec ε (fun b : unitPts G => unitRho r b.1)
        (decCov G a aT x ν α s φ (unitQ G) (unitP G) *ᵥ h)) ≤
      covC1Const d L (a k) ε κ * (a k + x)⁻¹ *
        n2 (covWVec ε (fun b : unitPts G => unitRho r b.1) h) := by
  have D := H x hx
  have hak : a k ∈ Set.Icc (1 / 2 : ℝ) 2 := D.st.ha k D.st.hk le_rfl
  have hak0 : 0 < a k := by linarith [hak.1]
  have hcx : 0 < a k + x := by linarith
  have hb : 0 ≤ aT / (L : ℝ) ^ 2 := by
    have := D.st.haT1
    positivity
  have hα : (a k + x)⁻¹ ≤ (a k)⁻¹ := inv_anti₀ hak0 (by linarith)
  have hα0 : 0 < (a k + x)⁻¹ := inv_pos.2 hcx
  have hT := covC_wT_cover H hφ hδ hsm hx hr h
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


include H hφ hδ hsm in
/-- Entry decay of `C_x(s)` at complex `s`, uniform in `x ≥ 0`. -/
theorem covC_entry_decay_cover {x : ℝ} (hx : 0 ≤ x) (p q : unitPts G) (i i' : Fin N) :
    ‖decCov G a aT x ν α s φ (unitQ G) (unitP G) (p, i) (q, i')‖ ≤
      covC1Const d L (a k) (xAgmonRate d L) κ * (a k + x)⁻¹ *
        Real.exp (xAgmonRate d L * d / L) *
        Real.exp (-(xAgmonRate d L / L) *
          Green.torusDist d ((N₁ * L ^ m₁) * L ^ (k + 1 - k)) p.1 q.1) := by
  have D := H x hx
  have hak0 : 0 < a k := (by have := D.st.ha k D.st.hk le_rfl; linarith [this.1])
  have hcx : 0 < a k + x := by linarith
  have hK : 0 ≤ covC1Const d L (a k) (xAgmonRate d L) κ * (a k + x)⁻¹ :=
    mul_nonneg (covC1Const_nonneg d L hak0 _ _) (inv_pos.2 hcx).le
  exact covC_entry_of_weighted ((xAgmonRate_pos (by have := (H 0 le_rfl).st.hd; omega) (H 0 le_rfl).st.hL).le) _ hK
    (fun r hr h => covC_wC_cover H hφ hδ hsm hx hr h) p q i i'

include H hφ hδ hsm in
theorem covC_sqrt_entry_decay_cover (p q : unitPts G) (i i' : Fin N) :
    ‖decCovSqrt G a aT ν α s φ (unitQ G) (unitP G) (p, i) (q, i')‖ ≤
      covSqrtEntryConstC d L (a k) κ *
        Real.exp (-(xAgmonRate d L / L) *
          Green.torusDist d ((N₁ * L ^ m₁) * L ^ (k + 1 - k)) p.1 q.1) := by
  have D0 := H 0 le_rfl
  have hak : 0 < a k := (by have := D0.st.ha k D0.st.hk le_rfl; linarith [this.1])
  set B0 : ℝ := covC1Const d L (a k) (xAgmonRate d L) κ * Real.exp (xAgmonRate d L * d / L) *
    Real.exp (-(xAgmonRate d L / L) *
      Green.torusDist d ((N₁ * L ^ m₁) * L ^ (k + 1 - k)) p.1 q.1) with hB0
  have hB0nn : 0 ≤ B0 := by
    have := covC1Const_nonneg d L hak (xAgmonRate d L) κ
    rw [hB0]; positivity
  unfold decCovSqrt
  simp only [Matrix.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  unfold intMat
  have hint : Integrable (fun y : ℝ => B0 * (y ^ (-(1 / 2 : ℝ)) * (a k + y)⁻¹))
      (volume.restrict (Ioi (0 : ℝ))) := (integrableOn_rpow_inv_add hak).const_mul B0
  have hbound := norm_integral_le_of_norm_le
    (f := fun x => decSqrtInt G a aT ν α s φ (unitQ G) (unitP G) x (p, i) (q, i')) hint
    ((ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun x hx => by
      have hx0 : 0 < x := mem_Ioi.mp hx
      have h3 : 0 < x ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hx0 _
      unfold decSqrtInt
      simp only [Matrix.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg h3.le]
      have := covC_entry_decay_cover H hφ hδ hsm hx0.le p q i i'
      calc x ^ (-(1 / 2 : ℝ)) *
            ‖decCov G a aT x ν α s φ (unitQ G) (unitP G) (p, i) (q, i')‖
          ≤ x ^ (-(1 / 2 : ℝ)) * (B0 * (a k + x)⁻¹) := by
            refine mul_le_mul_of_nonneg_left ?_ h3.le
            refine this.trans (le_of_eq ?_)
            rw [hB0]; ring
        _ = _ := by ring))
  rw [integral_const_mul, integral_rpow_inv_add hak] at hbound
  have hpi : 0 < Real.pi := Real.pi_pos
  have hsq : 0 < Real.sqrt (a k) := Real.sqrt_pos.2 hak
  rw [abs_of_pos (by positivity)]
  calc 1 / Real.pi * ‖∫ x in Ioi (0 : ℝ),
        decSqrtInt G a aT ν α s φ (unitQ G) (unitP G) x (p, i) (q, i')‖
      ≤ 1 / Real.pi * (B0 * (Real.pi / Real.sqrt (a k))) := by gcongr
    _ = _ := by
        rw [hB0]; unfold covSqrtEntryConstC; field_simp


include H hφ hδ hsm in
theorem covC_sqrt_supNorm_cover (v : unitPts G × Fin N → ℂ) {c : ℝ} (hc : 0 ≤ c)
    (hv : ∀ p, ‖v p‖ ≤ c) (p : unitPts G × Fin N) :
    ‖(decCovSqrt G a aT ν α s φ (unitQ G) (unitP G) *ᵥ v) p‖ ≤
      covSupConstC d L N (a k) κ * c := by
  classical
  have D0 := H 0 le_rfl
  have hd : 0 < d := by have := D0.st.hd; omega
  have hr : 0 < xAgmonRate d L / L := by
    have h1 := xAgmonRate_pos hd D0.st.hL
    have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  set E := covSqrtEntryConstC d L (a k) κ with hE
  set f : unitPts G → ℝ := fun q => Real.exp (-(xAgmonRate d L / L) *
    Green.torusDist d ((N₁ * L ^ m₁) * L ^ (k + 1 - k)) p.1.1 q.1) with hf
  have hball : ∑ q, f q ≤ Green.ballConst d (xAgmonRate d L / L) := by
    have h1 : ∑ q : unitPts G, f q = ∑ y ∈ unitPts G, Real.exp (-(xAgmonRate d L / L) *
        Green.torusDist d ((N₁ * L ^ m₁) * L ^ (k + 1 - k)) p.1.1 y) :=
      Finset.sum_coe_sort (unitPts G) (fun y => Real.exp (-(xAgmonRate d L / L) *
        Green.torusDist d ((N₁ * L ^ m₁) * L ^ (k + 1 - k)) p.1.1 y))
    rw [h1]
    exact (Finset.sum_le_univ_sum_of_nonneg fun _ => (Real.exp_pos _).le).trans
      (Green.ballSum_torus d _ hr p.1.1)
  have hE0 : 0 ≤ E := by
    have hak : 0 < a k := (by have := D0.st.ha k D0.st.hk le_rfl; linarith [this.1])
    have := covC1Const_nonneg d L hak (xAgmonRate d L) κ
    rw [hE]; unfold covSqrtEntryConstC; positivity
  calc ‖(decCovSqrt G a aT ν α s φ (unitQ G) (unitP G) *ᵥ v) p‖
      ≤ ∑ q : unitPts G × Fin N,
          ‖decCovSqrt G a aT ν α s φ (unitQ G) (unitP G) p q‖ * c := by
        simp only [Matrix.mulVec, dotProduct]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun q _ => ?_)
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hv q) (norm_nonneg _)
    _ ≤ ∑ q : unitPts G × Fin N, (E * f q.1) * c := by
        refine Finset.sum_le_sum fun q _ => ?_
        refine mul_le_mul_of_nonneg_right ?_ hc
        exact covC_sqrt_entry_decay_cover H hφ hδ hsm p.1 q.1 p.2 q.2
    _ = N * (E * ∑ q, f q) * c := by
        rw [Fintype.sum_prod_type_right]
        simp only [← Finset.sum_mul, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul]
        ring
    _ ≤ N * (E * Green.ballConst d (xAgmonRate d L / L)) * c := by gcongr
    _ = _ := by unfold covSupConstC; rw [← hE]; ring

end CoverSup

end Balaban.Fluctuation

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.LargeField Finset Matrix

section LocalHat

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱl : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Hl : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱl}
variable {a : ℕ → ℝ} {aT ν Cx κ δ δ₁ : ℝ}

/-- **The sup bound of `C^{1/2}(s)` on `DecDom`, cover form**: for `e = (s, φ₀, α₀) ∈ DecDom`,
`|(C^{1/2}(s) v)(p)| ≤ K c` for `|v| ≤ c` on the unit lattice, `K = covSupConstC d L N (a k) κ`. -/
theorem decCovSqrt_supNorm_cover (S : Dec2.XCover (coverOf G) G a aT ν Cx) (hCx : 0 ≤ Cx)
    (hκ : 0 ≤ κ) (hM : Dec2.cstarX d L Cx * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hδ : 0 ≤ δ) (hsm : δ ^ 2 * smallConstX d L κ ≤ 1 / 4) {e : DecData G N}
    (he : e ∈ DecDom G N κ δ) (v : unitPts G × Fin N → ℂ) {c : ℝ} (hc : 0 ≤ c)
    (hv : ∀ p, ‖v p‖ ≤ c) (p : unitPts G × Fin N) :
    ‖(decCovSqrt G a aT ν e.2.2 (extS G e.1) e.2.1 (unitQ G) (unitP G) *ᵥ v) p‖ ≤
      covSupConstC d L N (a k) κ * c :=
  covC_sqrt_supNorm_cover (fun (x : ℝ) (hx : 0 ≤ x) => xData_cover_of_mem (N := N) S hCx hx hκ hM he)
    he.2.1.toIsConstraintField hδ hsm v hc hv p

/-- **A field on the unit lattice of a generating set, extended by zero to the fine lattice and
lifted, is a block fluctuation of every generating set without layer `k + 1`**: the lift is
`ψ'(x) = v(unitBlock x)` on the unit blocks of `G` and `0` elsewhere; it is constant on the blocks
of the layers `n ≤ k`, and lies in `FlBallLC Hl δ₁` when `|v| < δ₁` at the unit points of `G`.
(This is `liftC_mem_flBallLC_of_top_empty` without `IsLevel G (k + 1)`: the local generator has
unit points only over its top layer.) -/
theorem localLift_mem_flBallLC_of_top_empty (hHl : Hl.Ω (k + 1) = ∅) (hδ₁ : 0 < δ₁)
    {v : unitPts G × Fin N → ℂ} (hv : ∀ b : unitPts G, vn (fun i => v (b, i)) < δ₁) :
    (fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
      if h : unitBlock x ∈ unitPts G then v (⟨unitBlock x, h⟩, i) else 0) ∈ FlBallLC Hl δ₁ := by
  classical
  refine ⟨fun x _ => ?_, ?_⟩
  · by_cases h : unitBlock x ∈ unitPts G
    · simpa only [h, dite_true] using hv ⟨unitBlock x, h⟩
    · have : (fun i : Fin N => if h : unitBlock x ∈ unitPts G then v (⟨unitBlock x, h⟩, i)
          else 0) = fun _ => 0 := by
        funext i; simp [h]
      show vn (fun i : Fin N => if h : unitBlock x ∈ unitPts G then v (⟨unitBlock x, h⟩, i)
          else 0) < δ₁
      rw [this, vn_eq_sqrt]
      simpa using hδ₁
  · intro n hn1 hnk x hx x' hx'
    have hn : n ≤ k := by
      by_contra h
      obtain rfl : n = k + 1 := by omega
      rw [GeneratingSet.mem_layer, hHl] at hx
      exact Finset.notMem_empty _ hx.1
    have hb : jBlock d L (N₁ * L ^ m₁) (k + 1) k x' = jBlock d L (N₁ * L ^ m₁) (k + 1) k x :=
      jBlock_eq_of_le hn (by omega) (GeneratingSet.mem_blk.1 hx')
    have hu : unitBlock x' = unitBlock x := hb
    funext i
    simp only [hu]

/-- **The local hat lift lands in the local fluctuation ball** (cover form, any `G` with the
standing data `Dec2.XCover (coverOf G) G …`).  For a datum `e = (s, φ₀, α₀) ∈ DecDom`, a hat
variable `ψ̂` on the unit lattice of `G` with `|ψ̂| ≤ c_ψ`, and the bound
`√N ‖cc‖ K c_ψ < δ₁`, the fluctuation `ψ' = cc C^{1/2}(s) ψ̂` (extended by zero outside the unit
blocks of `G` and lifted to the fine lattice) is a block fluctuation of every generating set
without layer `k + 1`, in particular of `𝔹_k(Y)`. -/
theorem localHatLift_mem_flBallLC_cover (S : Dec2.XCover (coverOf G) G a aT ν Cx) (hCx : 0 ≤ Cx)
    (hκ : 0 ≤ κ) (hM : Dec2.cstarX d L Cx * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hδ : 0 ≤ δ) (hsm : δ ^ 2 * smallConstX d L κ ≤ 1 / 4) {e : DecData G N}
    (he : e ∈ DecDom G N κ δ) (cc : ℂ) {cψ : ℝ} (hcψ : 0 ≤ cψ) (hδ₁0 : 0 < δ₁)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (a k) κ * cψ)) < δ₁)
    {ψh : unitPts G × Fin N → ℂ} (hψh : ∀ p, ‖ψh p‖ ≤ cψ) (hHl : Hl.Ω (k + 1) = ∅) :
    (fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
      if h : unitBlock x ∈ unitPts G then
        (cc • (decCovSqrt G a aT ν e.2.2 (extS G e.1) e.2.1 (unitQ G) (unitP G) *ᵥ ψh))
          (⟨unitBlock x, h⟩, i)
      else 0) ∈ FlBallLC Hl δ₁ := by
  refine localLift_mem_flBallLC_of_top_empty hHl hδ₁0 fun b => ?_
  have hsup := decCovSqrt_supNorm_cover (N := N) S hCx hκ hM hδ hsm he ψh hcψ hψh
  have hcoord : ∀ i, ‖(cc • (decCovSqrt G a aT ν e.2.2 (extS G e.1) e.2.1 (unitQ G) (unitP G) *ᵥ
      ψh)) (b, i)‖ ≤ ‖cc‖ * (covSupConstC d L N (a k) κ * cψ) := by
    intro i
    rw [Pi.smul_apply, smul_eq_mul, norm_mul]
    exact mul_le_mul_of_nonneg_left (hsup (b, i)) (norm_nonneg _)
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    have : vn (fun i : Fin 0 => (cc • (decCovSqrt G a aT ν e.2.2 (extS G e.1) e.2.1 (unitQ G)
        (unitP G) *ᵥ ψh)) (b, i)) = 0 := by
      rw [vn_eq_sqrt]; simp
    rw [this]; exact hδ₁0
  · have hV : 0 ≤ ‖cc‖ * (covSupConstC d L N (a k) κ * cψ) :=
      (norm_nonneg _).trans (hcoord ⟨0, hN⟩)
    exact lt_of_le_of_lt (vn_le_sqrt_mul hV hcoord) hδ₁

end LocalHat

section LocalB

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱl : ℝ}
variable {a : ℕ → ℝ} {aT ν κ δ δ₁ : ℝ}

/-- **The local hat square root is analytic on the polydisc** (instance at the literal local
generator `𝔹(Y) = localB j hj Y`, with `Dec2.XCover (coverOf 𝔹) 𝔹` from `localB_xCover`, `k ≥ 1`):
every entry of `C^{1/2}(s)` at the unit lattice of `𝔹(Y)` is analytic in `(s, φ₀, α₀)` on
`DecDom`. -/
theorem localB_analyticOnNhd_decCovSqrt_entry {j : ℕ} (hj : j ≤ k + 1)
    (Y : Set (CTorus d L N₁ m₁ (k + 1))) (hsep : ϱ ≤ minSep L (L ^ m₁)) (hm₁ : 2 ≤ m₁)
    (hM : 4 * L ^ 2 ≤ L ^ m₁) (hd : 3 ≤ d) (hL : 3 ≤ L) (hν : 0 ≤ ν)
    (hνL : ν * ((L : ℝ) ^ (k + 1)) ^ 2 ≤ 1) (ha : IsAdmissibleWeights (k + 1) a)
    (hag : 2 * d * Real.log L ≤ agmonRate d / 16 * (ϱ - 1)) (hk : 1 ≤ k) (haT1 : 1 / 2 ≤ aT)
    (haT2 : aT ≤ 2) (hκ : 0 ≤ κ)
    (hbig : Dec2.cstarX d L (Cchi d L) * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) (hδ : 0 ≤ δ)
    (hsm : δ ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (p q : unitPts (SmallField.GsSpec.localB j hj Y hsep) × Fin N) :
    AnalyticOnNhd ℂ (fun e : DecData (SmallField.GsSpec.localB j hj Y hsep) N =>
      decCovSqrt (SmallField.GsSpec.localB j hj Y hsep) a aT ν e.2.2
        (extS (SmallField.GsSpec.localB j hj Y hsep) e.1) e.2.1
        (unitQ (SmallField.GsSpec.localB j hj Y hsep))
        (unitP (SmallField.GsSpec.localB j hj Y hsep)) p q)
      (DecDom (SmallField.GsSpec.localB j hj Y hsep) N κ δ) :=
  analyticOnNhd_decCovSqrt_entry_cover
    (localB_xCover hj Y hsep hm₁ hM hd hL hν hνL ha hag hk haT1 haT2) (Cchi_nonneg d L) hκ hbig
    hδ hsm (isUnitLatticeB_unit (G := SmallField.GsSpec.localB j hj Y hsep)).toIsUnitLattice p q

/-- **The local hat lift lands in the local fluctuation ball** (instance at `𝔹(Y) = localB j hj Y`
of `localHatLift_mem_flBallLC_cover`; `H⁻` is any generating set without layer `k + 1`, e.g.
`𝔹_k(Y)` of `GsSpec.localB_drop_top`). -/
theorem localB_localHatLift_mem_flBallLC {j : ℕ} (hj : j ≤ k + 1)
    (Y : Set (CTorus d L N₁ m₁ (k + 1))) (hsep : ϱ ≤ minSep L (L ^ m₁)) (hm₁ : 2 ≤ m₁)
    (hM : 4 * L ^ 2 ≤ L ^ m₁) (hd : 3 ≤ d) (hL : 3 ≤ L) (hν : 0 ≤ ν)
    (hνL : ν * ((L : ℝ) ^ (k + 1)) ^ 2 ≤ 1) (ha : IsAdmissibleWeights (k + 1) a)
    (hag : 2 * d * Real.log L ≤ agmonRate d / 16 * (ϱ - 1)) (hk : 1 ≤ k) (haT1 : 1 / 2 ≤ aT)
    (haT2 : aT ≤ 2) (hκ : 0 ≤ κ)
    (hbig : Dec2.cstarX d L (Cchi d L) * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) (hδ : 0 ≤ δ)
    (hsm : δ ^ 2 * smallConstX d L κ ≤ 1 / 4)
    {e : DecData (SmallField.GsSpec.localB j hj Y hsep) N}
    (he : e ∈ DecDom (SmallField.GsSpec.localB j hj Y hsep) N κ δ) (cc : ℂ) {cψ : ℝ}
    (hcψ : 0 ≤ cψ) (hδ₁0 : 0 < δ₁)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (a k) κ * cψ)) < δ₁)
    {ψh : unitPts (SmallField.GsSpec.localB j hj Y hsep) × Fin N → ℂ}
    (hψh : ∀ p, ‖ψh p‖ ≤ cψ) {Hl : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱl}
    (hHl : Hl.Ω (k + 1) = ∅) :
    (fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
      if h : unitBlock x ∈ unitPts (SmallField.GsSpec.localB j hj Y hsep) then
        (cc • (decCovSqrt (SmallField.GsSpec.localB j hj Y hsep) a aT ν e.2.2
          (extS (SmallField.GsSpec.localB j hj Y hsep) e.1) e.2.1
          (unitQ (SmallField.GsSpec.localB j hj Y hsep))
          (unitP (SmallField.GsSpec.localB j hj Y hsep)) *ᵥ ψh)) (⟨unitBlock x, h⟩, i)
      else 0) ∈ FlBallLC Hl δ₁ :=
  localHatLift_mem_flBallLC_cover
    (localB_xCover hj Y hsep hm₁ hM hd hL hν hνL ha hag hk haT1 haT2) (Cchi_nonneg d L) hκ hbig
    hδ hsm he cc hcψ hδ₁0 hδ₁ hψh hHl

end LocalB

end Balaban.Localization
