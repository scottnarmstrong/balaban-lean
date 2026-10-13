/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.KF0BlockSplit
public import Balaban.LargeField.Base.KF0ShiftedSector
public import Balaban.LargeField.Base.KF0Gaussian
public import Balaban.Green.KF0DetWalks
import Mathlib.Tactic.Linarith

/-!
# The partition function as a sum over sectors, in shifted Gaussian form

Exact identities and a crude bound for FIXED sectors.  The linked expansion and the one-scale
theorem are NOT proved here.

For a set `B` of bad blocks, `D = siteUnion B`, and `G = Dᶜ`, the landed sector identity
(`kf0Sector_iterated`) and the landed shifted form of the inner good-spin integral
(`lintegral_goodInner_shifted`) are composed.

* `kf0SectorLint_eq`: the sector integral (real source, `[0,∞]`-valued) equals
  `(√β)^{-n_G} N_G · ∫ dq_D [bad factor · e^{-reduced constant}] · ∫ dγ_G(ψ) [good factor](m(q) + C_G ψ)`.
* `kwNormRatio`: the ratio of the sector normalizer `(√β)^{-n_G} N_G` to the full-torus normalizer
  `(√β)^{-n_Λ} N_Λ`; `kwNormRatio_eq` expresses it through the determinant ratio
  `det K_Λ / det K_G`, and `kwNormRatio_le`, `kwNormRatio_ge` give the two-sided bounds from
  `kw_det_ratio_bounds`.
* `partitionFunction_eq_sum_kwNormRatio`: the partition function (real source) is the full-torus
  normalizer times `∑_B kwNormRatio(B) · (reduced sector integral)`.
* `kwNormRatio_empty`, `goodMean_empty`, `goodReducedConst_empty`: the empty sector reduces to the
  all-good prefactor.
* `kf0SectorLint_le_peierls`: a crude bound for a sector with the Peierls charge
  `exp(-β ν r² #B / 2)`; the good Gaussian integral with the indicators dropped stays a named
  quantity.
-/

@[expose] public section

set_option linter.unusedSectionVars false

open MeasureTheory Matrix Balaban Balaban.KW

namespace Balaban.LargeField

open SphereChart

open scoped Classical

section Defs

variable {d N ℓ : ℕ} [NeZero ℓ] (D : Finset (Torus d ℓ)) {h : EuclideanSpace ℝ (Fin N)}

/-- The sector integral (real source, `[0,∞]`-valued): the left side of `kf0Sector_iterated`. -/
noncomputable def kf0SectorLint (s m : ℕ) [NeZero m] (r β ν : ℝ) (h : EuclideanSpace ℝ (Fin N))
    (g : Torus d ℓ → Fin N → ℝ) (B : Finset (Torus d m)) : ENNReal :=
  ∫⁻ φ, ENNReal.ofReal (Real.exp (-(β * energy d N ℓ ν h φ) + realSource g φ) *
    sectorWeight s m r h B φ) ∂aprioriMeasure d N ℓ

/-- The factor of the bad spins `q`: `exp(-β H_B(q) + ⟨g_D, q⟩) · ∏_{Q∈B}(1 - χ_Q(q))`. -/
noncomputable def kf0BadFactor (s m : ℕ) [NeZero m] (r β ν : ℝ) (h : EuclideanSpace ℝ (Fin N))
    (g : Torus d ℓ → Fin N → ℝ) (B : Finset (Torus d m)) (q : ↥D → SpinSphere N) : ℝ :=
  Real.exp (-(β * blockEnergyIn D ν h q) + sourceIn D g q) * badWeight D h s m r B q

/-- The good factor at a tangent field `v`: `J_β(v) · ∏_{Q∉B} χ_Q · exp(shifted exponent)`. -/
noncomputable def kf0GoodIntegrand (hh : ‖h‖ = 1) (s m : ℕ) [NeZero m] (r β ν : ℝ)
    (g : Torus d ℓ → Fin N → ℝ) (B : Finset (Torus d m)) (q : ↥D → SpinSphere N)
    (v : Good D → perp h) : ENNReal :=
  ENNReal.ofReal (chartJac β (fun x => ((v x : perp h) : EuclideanSpace ℝ (Fin N)))) *
    ENNReal.ofReal (goodWeight D h s m r B (chartCfgOn h hh ((Real.sqrt β)⁻¹ • v))) *
    ENNReal.ofReal (Real.exp (goodShiftedExponent D β ν g h q v))

/-- The good Gaussian integral of a sector at bad spins `q`:
`∫ dγ_G(ψ) [good factor](m(q) + C_G ψ)`. -/
noncomputable def kf0GoodInner (hh : ‖h‖ = 1) (s m : ℕ) [NeZero m] (r β ν : ℝ)
    (g : Torus d ℓ → Fin N → ℝ) (B : Finset (Torus d m)) (q : ↥D → SpinSphere N) : ENNReal :=
  ∫⁻ ψ, kf0GoodIntegrand D hh s m r β ν g B q
      (goodMean D β ν (goodJ D hh q) + matAct (kwSqrt ν D) ψ) ∂(goodGaussian D h)

/-- The reduced sector integral: `∫ dq_D [bad factor · e^{-goodReducedConst(q)}] · (good Gaussian
integral)(q)`, over the bad spins of `D = siteUnion B`. -/
noncomputable def kf0SectorReduced (hh : ‖h‖ = 1) (s m : ℕ) [NeZero m] (r β ν : ℝ)
    (g : Torus d ℓ → Fin N → ℝ) (B : Finset (Torus d m)) : ENNReal :=
  ∫⁻ q, ENNReal.ofReal (kf0BadFactor (siteUnion (ℓ := ℓ) s m B) s m r β ν h g B q *
        Real.exp (-goodReducedConst (siteUnion (ℓ := ℓ) s m B) hh β ν q)) *
      kf0GoodInner (siteUnion (ℓ := ℓ) s m B) hh s m r β ν g B q
    ∂sigmaIn (siteUnion (ℓ := ℓ) s m B)

/-- The sector normalizer `(√β)^{-n_G} N_G`. -/
noncomputable def kwSectorNorm (d ℓ N : ℕ) [NeZero ℓ] (β ν : ℝ) (D : Finset (Torus d ℓ)) : ℝ :=
  ((Real.sqrt β)⁻¹) ^ (Fintype.card (Good D) * (N - 1)) * kwGaussNorm d ℓ N ν D

/-- The full-torus normalizer `(√β)^{-n_Λ} N_Λ` of the landed all-good formula. -/
noncomputable def fullNorm (d ℓ N : ℕ) [NeZero ℓ] (β ν : ℝ) : ℝ :=
  ((Real.sqrt β)⁻¹) ^ (Fintype.card (Torus d ℓ) * (N - 1)) * kf0GaussNorm d ℓ N ν

/-- The ratio `R_det(D)` of the sector normalizer to the full-torus normalizer. -/
noncomputable def kwNormRatio (d ℓ N : ℕ) [NeZero ℓ] (β ν : ℝ) (D : Finset (Torus d ℓ)) : ℝ :=
  kwSectorNorm d ℓ N β ν D / fullNorm d ℓ N β ν

end Defs

section T1

variable {d N ℓ : ℕ} [NeZero ℓ] {h : EuclideanSpace ℝ (Fin N)}

/-- **T1.**  One sector, assembled: the sector integral equals the sector normalizer times the
reduced sector integral. -/
theorem kf0SectorLint_eq (s m : ℕ) [NeZero m] (r : ℝ) (B : Finset (Torus d m)) {β ν : ℝ}
    (hβ : 0 < β) (hν : 0 < ν) (hh : ‖h‖ = 1) (hr : r ≤ 1) (g : Torus d ℓ → Fin N → ℝ) :
    kf0SectorLint s m r β ν h g B =
      ENNReal.ofReal (kwSectorNorm d ℓ N β ν (siteUnion (ℓ := ℓ) s m B)) *
        kf0SectorReduced hh s m r β ν g B := by
  unfold kf0SectorLint kf0SectorReduced
  rw [kf0Sector_iterated (h := h) (s := s) (m := m) (r := r) (β := β) (ν := ν) (g := g) (B := B), ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun q => ?_
  rw [lintegral_goodInner_shifted (siteUnion (ℓ := ℓ) s m B) s r B rfl hβ hν hh hr g q]
  have hN := kwGaussNorm_pos (d := d) (m := ℓ) (N := N) (siteUnion (ℓ := ℓ) s m B) hν
  have hs : (0 : ℝ) < ((Real.sqrt β)⁻¹) ^ (Fintype.card (Good (siteUnion (ℓ := ℓ) s m B)) * (N - 1)) :=
    pow_pos (inv_pos.2 (Real.sqrt_pos.2 hβ)) _
  unfold kwSectorNorm kf0BadFactor kf0GoodInner
  have e1 : ENNReal.ofReal (Real.exp (-(β * blockEnergyIn (siteUnion (ℓ := ℓ) s m B) ν h q)
        + sourceIn (siteUnion (ℓ := ℓ) s m B) g q) * badWeight (siteUnion (ℓ := ℓ) s m B) h s m r B q
        * Real.exp (-goodReducedConst (siteUnion (ℓ := ℓ) s m B) hh β ν q)) =
      ENNReal.ofReal (Real.exp (-(β * blockEnergyIn (siteUnion (ℓ := ℓ) s m B) ν h q)
        + sourceIn (siteUnion (ℓ := ℓ) s m B) g q) * badWeight (siteUnion (ℓ := ℓ) s m B) h s m r B q) *
        ENNReal.ofReal (Real.exp (-goodReducedConst (siteUnion (ℓ := ℓ) s m B) hh β ν q)) :=
    ENNReal.ofReal_mul (mul_nonneg (Real.exp_pos _).le (badWeight_nonneg _ h s m r B q))
  rw [e1, ENNReal.ofReal_mul hs.le]
  unfold kf0GoodIntegrand
  ring

end T1

section T2

variable {d ℓ : ℕ} [NeZero ℓ]

theorem card_good_add (D : Finset (Torus d ℓ)) :
    Fintype.card (Good D) + D.card = Fintype.card (Torus d ℓ) := by
  simp only [Good]
  rw [Fintype.card_subtype_compl, Fintype.card_coe]
  have := Finset.card_le_univ D
  omega

theorem kwSectorNorm_pos (N : ℕ) {β ν : ℝ} (hβ : 0 < β) (hν : 0 < ν) (D : Finset (Torus d ℓ)) :
    0 < kwSectorNorm d ℓ N β ν D :=
  mul_pos (pow_pos (inv_pos.2 (Real.sqrt_pos.2 hβ)) _) (kwGaussNorm_pos D hν)

theorem fullNorm_pos (N : ℕ) {β ν : ℝ} (hβ : 0 < β) (hν : 0 < ν) :
    0 < fullNorm d ℓ N β ν :=
  mul_pos (pow_pos (inv_pos.2 (Real.sqrt_pos.2 hβ)) _) (kf0GaussNorm_pos hν)

/-- **T2.**  The ratio of normalizers through the determinant ratio:
`R_det(D) = (√β)^{(N-1)|D|} (2π)^{-(N-1)|D|/2} (det K_Λ / det K_G)^{(N-1)/2}`. -/
theorem kwNormRatio_eq (N : ℕ) {β ν : ℝ} (hβ : 0 < β) (hν : 0 < ν) (D : Finset (Torus d ℓ)) :
    kwNormRatio d ℓ N β ν D =
      Real.sqrt β ^ ((N - 1) * D.card) * (2 * Real.pi) ^ (-(((N - 1) * D.card : ℕ) : ℝ) / 2) *
        ((latticeLaplacian d ℓ ν).det / (kwOpSub d ℓ ν D).det) ^ (((N - 1 : ℕ) : ℝ) / 2) := by
  have hcard := card_good_add D
  set n := N - 1 with hn
  set c := D.card with hc
  set a := Fintype.card (Torus d ℓ) with ha
  have hdG := (kwOpSub_posDef ν D hν).det_pos
  have hdL := (latticeLaplacian_posDef (d := d) (ℓ := ℓ) hν).det_pos
  have hx : 0 < Real.sqrt β := Real.sqrt_pos.2 hβ
  have h2pi : 0 < 2 * Real.pi := by positivity
  unfold kwNormRatio kwSectorNorm fullNorm kwGaussNorm kf0GaussNorm
  have hgd : (goodDim D N : ℝ) = (a * n : ℕ) - (c * n : ℕ) := by
    unfold goodDim
    have : Fintype.card (Good D) * n = a * n - c * n := by
      rw [← Nat.sub_mul]; congr 1; omega
    rw [this, Nat.cast_sub (Nat.mul_le_mul_right _ (by omega))]
  have htd : (tangentDim d ℓ N : ℝ) = (a * n : ℕ) := by
    unfold tangentDim; rfl
  have e1 : (Real.sqrt β)⁻¹ ^ (a * n) = (Real.sqrt β)⁻¹ ^ (Fintype.card (Good D) * n) *
      (Real.sqrt β)⁻¹ ^ (c * n) := by
    rw [← pow_add, ← add_mul]; congr 2; omega
  have e2 : (2 * Real.pi) ^ ((a * n : ℕ) / 2 : ℝ) = (2 * Real.pi) ^ ((goodDim D N : ℝ) / 2) *
      (2 * Real.pi) ^ ((c * n : ℕ) / 2 : ℝ) := by
    rw [← Real.rpow_add h2pi, hgd]; congr 1; ring
  rw [htd, e1, e2, ← hn]
  have e3 : (-(((n * c : ℕ)) : ℝ) / 2) = -((c * n : ℕ) / 2 : ℝ) := by
    push_cast; ring
  have e0 : (-(n : ℝ) / 2) = -((n : ℝ) / 2) := by ring
  rw [e3, e0, Real.rpow_neg h2pi.le, Real.div_rpow hdL.le hdG.le, Real.rpow_neg hdG.le,
    Real.rpow_neg hdL.le, inv_pow, mul_comm c n]
  have e4 : ((2 * Real.pi) ^ ((n * c : ℕ) / 2 : ℝ)) > 0 := Real.rpow_pos_of_pos h2pi _
  have : Real.sqrt β ^ (n * c) > 0 := pow_pos hx _
  have e5 : ((latticeLaplacian d ℓ ν).det ^ ((n : ℝ) / 2)) > 0 := Real.rpow_pos_of_pos hdL _
  have e6 : ((kwOpSub d ℓ ν D).det ^ ((n : ℝ) / 2)) > 0 := Real.rpow_pos_of_pos hdG _
  have e7 : ((Real.sqrt β ^ (Fintype.card (Good D) * n))⁻¹) > 0 := by positivity
  have e8 : (2 * Real.pi) ^ ((goodDim D N : ℝ) / 2) > 0 := Real.rpow_pos_of_pos h2pi _
  field_simp
  rw [one_div, inv_pow, inv_mul_cancel₀ (ne_of_gt this)]

theorem det_ratio_bounds' {ν : ℝ} (hν : 0 < ν) (D : Finset (Torus d ℓ)) :
    Real.exp (-(2 * D.card * (2 * d / ν))) * (2 * d + ν) ^ D.card ≤
        (latticeLaplacian d ℓ ν).det / (kwOpSub d ℓ ν D).det ∧
      (latticeLaplacian d ℓ ν).det / (kwOpSub d ℓ ν D).det ≤ (2 * d + ν) ^ D.card := by
  obtain ⟨h1, h2⟩ := kw_det_ratio_bounds hν D
  have ha : 0 < (2 * (d : ℝ) + ν) ^ D.card := pow_pos (kw_a_pos hν) _
  have hdG := (kwOpSub_posDef ν D hν).det_pos
  rw [le_div_iff₀ (mul_pos hdG ha)] at h1
  rw [div_le_one (mul_pos hdG ha)] at h2
  constructor
  · rw [le_div_iff₀ hdG]; nlinarith
  · rw [div_le_iff₀ hdG]; nlinarith

theorem sqrt_pow_mul_eq (β : ℝ) (hβ : 0 < β) (k : ℕ) :
    Real.sqrt β ^ k = β ^ ((k : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hβ.le]
  congr 1; ring

theorem target_eq (β a : ℝ) (hβ : 0 < β) (ha : 0 < a) (w : ℝ) :
    (β * a / (2 * Real.pi)) ^ w = β ^ w * (2 * Real.pi) ^ (-w) * a ^ w := by
  have h2pi : 0 < 2 * Real.pi := by positivity
  rw [Real.div_rpow (mul_pos hβ ha).le h2pi.le, Real.mul_rpow hβ.le ha.le, Real.rpow_neg h2pi.le]
  ring

/-- **T2, upper bound.**  `R_det(D) ≤ [β (2d + ν) / (2π)]^{(N-1)|D|/2}`. -/
theorem kwNormRatio_le (N : ℕ) {β ν : ℝ} (hβ : 0 < β) (hν : 0 < ν) (D : Finset (Torus d ℓ)) :
    kwNormRatio d ℓ N β ν D ≤
      (β * (2 * d + ν) / (2 * Real.pi)) ^ ((((N - 1) * D.card : ℕ) : ℝ) / 2) := by
  have ha : 0 < 2 * (d : ℝ) + ν := kw_a_pos hν
  have hdG := (kwOpSub_posDef ν D hν).det_pos
  have hdL := (latticeLaplacian_posDef (d := d) (ℓ := ℓ) hν).det_pos
  have h2pi : 0 < 2 * Real.pi := by positivity
  rw [kwNormRatio_eq N hβ hν D, target_eq β _ hβ ha, sqrt_pow_mul_eq β hβ,
    neg_div, mul_assoc, mul_assoc]
  have p1 : 0 ≤ β ^ ((((N - 1) * D.card : ℕ) : ℝ) / 2) := (Real.rpow_pos_of_pos hβ _).le
  have p2 : 0 ≤ (2 * Real.pi) ^ (-((((N - 1) * D.card : ℕ) : ℝ) / 2)) :=
    (Real.rpow_pos_of_pos h2pi _).le
  refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ p2) p1
  obtain ⟨_, hu⟩ := det_ratio_bounds' hν D
  calc ((latticeLaplacian d ℓ ν).det / (kwOpSub d ℓ ν D).det) ^ (((N - 1 : ℕ) : ℝ) / 2)
      ≤ ((2 * d + ν) ^ D.card) ^ (((N - 1 : ℕ) : ℝ) / 2) :=
        Real.rpow_le_rpow (div_nonneg hdL.le hdG.le) hu (by positivity)
    _ = (2 * d + ν) ^ ((((N - 1) * D.card : ℕ) : ℝ) / 2) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul ha.le]
        congr 1; push_cast; ring

/-- **T2, lower bound.**  `R_det(D) ≥ exp(-(N-1)|D| · 2d/ν) · [β (2d + ν) / (2π)]^{(N-1)|D|/2}`. -/
theorem kwNormRatio_ge (N : ℕ) {β ν : ℝ} (hβ : 0 < β) (hν : 0 < ν) (D : Finset (Torus d ℓ)) :
    Real.exp (-((((N - 1) * D.card : ℕ) : ℝ) * (2 * d / ν))) *
        (β * (2 * d + ν) / (2 * Real.pi)) ^ ((((N - 1) * D.card : ℕ) : ℝ) / 2) ≤
      kwNormRatio d ℓ N β ν D := by
  have ha : 0 < 2 * (d : ℝ) + ν := kw_a_pos hν
  have hdG := (kwOpSub_posDef ν D hν).det_pos
  have hdL := (latticeLaplacian_posDef (d := d) (ℓ := ℓ) hν).det_pos
  have h2pi : 0 < 2 * Real.pi := by positivity
  rw [kwNormRatio_eq N hβ hν D, target_eq β _ hβ ha, sqrt_pow_mul_eq β hβ]
  obtain ⟨hl, _⟩ := det_ratio_bounds' hν D
  have key : Real.exp (-((((N - 1) * D.card : ℕ) : ℝ) * (2 * d / ν))) *
      (2 * d + ν) ^ ((((N - 1) * D.card : ℕ) : ℝ) / 2) ≤
      ((latticeLaplacian d ℓ ν).det / (kwOpSub d ℓ ν D).det) ^ (((N - 1 : ℕ) : ℝ) / 2) := by
    calc Real.exp (-((((N - 1) * D.card : ℕ) : ℝ) * (2 * d / ν))) *
          (2 * d + ν) ^ ((((N - 1) * D.card : ℕ) : ℝ) / 2)
        = (Real.exp (-(2 * D.card * (2 * d / ν))) * (2 * d + ν) ^ D.card) ^
            (((N - 1 : ℕ) : ℝ) / 2) := by
          rw [Real.mul_rpow (Real.exp_pos _).le (pow_pos ha _).le, ← Real.exp_mul,
            ← Real.rpow_natCast, ← Real.rpow_mul ha.le]
          congr 2
          · push_cast; ring
          · push_cast; ring
      _ ≤ _ := Real.rpow_le_rpow (by positivity) hl (by positivity)
  calc Real.exp (-((((N - 1) * D.card : ℕ) : ℝ) * (2 * d / ν))) *
        (β ^ ((((N - 1) * D.card : ℕ) : ℝ) / 2) *
          (2 * Real.pi) ^ (-((((N - 1) * D.card : ℕ) : ℝ) / 2)) *
            (2 * d + ν) ^ ((((N - 1) * D.card : ℕ) : ℝ) / 2))
      = β ^ ((((N - 1) * D.card : ℕ) : ℝ) / 2) *
          (2 * Real.pi) ^ (-((((N - 1) * D.card : ℕ) : ℝ) / 2)) *
          (Real.exp (-((((N - 1) * D.card : ℕ) : ℝ) * (2 * d / ν))) *
            (2 * d + ν) ^ ((((N - 1) * D.card : ℕ) : ℝ) / 2)) := by ring
    _ ≤ _ := by
        rw [neg_div]
        exact mul_le_mul_of_nonneg_left key (by positivity)

end T2

section T3

variable {d N ℓ : ℕ} [NeZero ℓ] {h : EuclideanSpace ℝ (Fin N)}

/-- The complex sector integral at a real source is the real number `(kf0SectorLint).toReal`. -/
theorem kf0Sector_real (s m : ℕ) [NeZero m] (r β ν : ℝ) (h : EuclideanSpace ℝ (Fin N))
    (g : Torus d ℓ → Fin N → ℝ) (B : Finset (Torus d m)) :
    kf0Sector s m r β ν h B (fun x i => ((g x i : ℝ) : ℂ)) =
      ((kf0SectorLint s m r β ν h g B).toReal : ℂ) := by
  have hE : Measurable fun φ : Cfg d N ℓ => energy d N ℓ ν h φ :=
    (continuous_energy (d := d) (N := N) (ℓ := ℓ) ν h).measurable
  have hmeas : Measurable fun φ : Cfg d N ℓ => Real.exp (-(β * energy d N ℓ ν h φ)
      + realSource g φ) * sectorWeight s m r h B φ :=
    (Real.measurable_exp.comp (((measurable_const.mul hE).neg).add
        (measurable_realSource g))).mul (measurable_sectorWeight s m r h B)
  have hnn : 0 ≤ᵐ[aprioriMeasure d N ℓ] fun φ : Cfg d N ℓ => Real.exp (-(β * energy d N ℓ ν h φ)
      + realSource g φ) * sectorWeight s m r h B φ :=
    Filter.Eventually.of_forall fun φ => mul_nonneg (Real.exp_pos _).le (sectorWeight_nonneg s m r h B φ)
  have h1 : kf0Sector s m r β ν h B (fun x i => ((g x i : ℝ) : ℂ)) =
      ∫ φ, ((Real.exp (-(β * energy d N ℓ ν h φ) + realSource g φ) * sectorWeight s m r h B φ : ℝ) : ℂ)
        ∂aprioriMeasure d N ℓ := by
    unfold kf0Sector sourceIntegral
    refine integral_congr_ae (Filter.Eventually.of_forall fun φ => ?_)
    simp only [sourceIntegrand, sourcePairing, realSource]
    push_cast
    ring
  rw [h1, integral_complex_ofReal, integral_eq_lintegral_of_nonneg_ae hnn hmeas.aestronglyMeasurable]
  rfl

/-- (K0.2) for a real source, in `[0,∞]`: the partition function is the real part of
`∑_B kf0SectorLint`. -/
theorem partitionFunction_real (s m : ℕ) [NeZero m] (r β ν : ℝ) (h : EuclideanSpace ℝ (Fin N))
    (g : Torus d ℓ → Fin N → ℝ) :
    partitionFunction d N ℓ β ν h (fun x i => ((g x i : ℝ) : ℂ)) =
      ((∑ B : Finset (Torus d m), (kf0SectorLint s m r β ν h g B).toReal : ℝ) : ℂ) := by
  rw [partitionFunction_eq_sum_kf0Sector s m r β ν h]
  push_cast
  exact Finset.sum_congr rfl fun B _ => kf0Sector_real s m r β ν h g B

/-- Each sector integral is finite. -/
theorem kf0SectorLint_lt_top (s m : ℕ) [NeZero m] (r β ν : ℝ) (h : EuclideanSpace ℝ (Fin N))
    (g : Torus d ℓ → Fin N → ℝ) (B : Finset (Torus d m)) : kf0SectorLint s m r β ν h g B < ⊤ := by
  have hc : Continuous fun φ : Cfg d N ℓ => Real.exp (-(β * energy d N ℓ ν h φ) + realSource g φ) := by
    refine Real.continuous_exp.comp (((continuous_const.mul
      (continuous_energy (d := d) (N := N) (ℓ := ℓ) ν h)).neg).add ?_)
    unfold realSource
    exact continuous_finsetSum _ fun x _ => continuous_finsetSum _ fun i _ =>
      continuous_const.mul (continuous_spin_coord x i)
  have hint := (integrable_of_continuous (d := d) (N := N) (ℓ := ℓ) hc).lintegral_lt_top
  refine lt_of_le_of_lt (lintegral_mono fun φ => ?_) hint
  refine ENNReal.ofReal_le_ofReal ?_
  calc Real.exp (-(β * energy d N ℓ ν h φ) + realSource g φ) * sectorWeight s m r h B φ
      ≤ Real.exp (-(β * energy d N ℓ ν h φ) + realSource g φ) * 1 :=
        mul_le_mul_of_nonneg_left (sectorWeight_le_one s m r h B φ) (Real.exp_pos _).le
    _ = _ := mul_one _

theorem fullNorm_mul_ratio (N : ℕ) {β ν : ℝ} (hβ : 0 < β) (hν : 0 < ν) (D : Finset (Torus d ℓ)) :
    fullNorm d ℓ N β ν * kwNormRatio d ℓ N β ν D = kwSectorNorm d ℓ N β ν D := by
  unfold kwNormRatio
  have := (fullNorm_pos (d := d) (ℓ := ℓ) N hβ hν).ne'
  field_simp

/-- **T3.**  The exact identity (H37.6): for a real source,
`Z(g) = N_Λ · ∑_B R_det(B) · ∫ dq_D [bad factor e^{-reduced constant}] ∫ dγ_G [good factor](m + C_G ψ)`,
with `N_Λ = (√β)^{-n_Λ} · kf0GaussNorm` the full-torus normalizer; each sector has its own good
Gaussian measure on `Good D`. -/
theorem partitionFunction_eq_sum_kwNormRatio (s m : ℕ) [NeZero m] (r : ℝ) {β ν : ℝ}
    (hβ : 0 < β) (hν : 0 < ν) (hh : ‖h‖ = 1) (hr : r ≤ 1) (g : Torus d ℓ → Fin N → ℝ) :
    partitionFunction d N ℓ β ν h (fun x i => ((g x i : ℝ) : ℂ)) =
      ((ENNReal.ofReal (fullNorm d ℓ N β ν) *
        ∑ B : Finset (Torus d m),
          ENNReal.ofReal (kwNormRatio d ℓ N β ν (siteUnion (ℓ := ℓ) s m B)) *
            kf0SectorReduced hh s m r β ν g B).toReal : ℂ) := by
  rw [partitionFunction_real s m r β ν h g, ← ENNReal.toReal_sum]
  · congr 2
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun B _ => ?_
    rw [kf0SectorLint_eq s m r B hβ hν hh hr g, ← mul_assoc, ← ENNReal.ofReal_mul
      (fullNorm_pos N hβ hν).le, fullNorm_mul_ratio N hβ hν]
  · exact fun B _ => (kf0SectorLint_lt_top s m r β ν h g B).ne

end T3

section T4

variable {d N ℓ : ℕ} [NeZero ℓ] {h : EuclideanSpace ℝ (Fin N)}

theorem siteUnion_empty (s m : ℕ) [NeZero m] :
    siteUnion (ℓ := ℓ) s m (∅ : Finset (Torus d m)) = ∅ := by
  ext x; simp [siteUnion]

theorem card_good_empty : Fintype.card (Good (∅ : Finset (Torus d ℓ))) = Fintype.card (Torus d ℓ) := by
  simp

/-- The sector normalizer of the empty bad set is the full-torus normalizer. -/
theorem kwSectorNorm_empty (N : ℕ) (β ν : ℝ) :
    kwSectorNorm d ℓ N β ν (∅ : Finset (Torus d ℓ)) = fullNorm d ℓ N β ν := by
  unfold kwSectorNorm fullNorm
  rw [kwGaussNorm_empty, card_good_empty]

theorem kwSectorNorm_congr_empty (s m : ℕ) [NeZero m] (β ν : ℝ) :
    ENNReal.ofReal (kwSectorNorm d ℓ N β ν (siteUnion (ℓ := ℓ) s m (∅ : Finset (Torus d m)))) =
      ENNReal.ofReal (fullNorm d ℓ N β ν) := by
  rw [siteUnion_empty, kwSectorNorm_empty]

/-- **T4.**  `R_det(∅) = 1`. -/
theorem kwNormRatio_empty (N : ℕ) {β ν : ℝ} (hβ : 0 < β) (hν : 0 < ν) :
    kwNormRatio d ℓ N β ν (∅ : Finset (Torus d ℓ)) = 1 := by
  unfold kwNormRatio
  rw [kwSectorNorm_empty]
  exact div_self (fullNorm_pos N hβ hν).ne'

theorem goodJ_empty (hh : ‖h‖ = 1) (q : ↥(∅ : Finset (Torus d ℓ)) → SpinSphere N) :
    goodJ (∅ : Finset (Torus d ℓ)) hh q = 0 := by
  funext x
  simp [goodJ]

/-- **T4.**  The shifted mean of the empty sector is `0`. -/
theorem goodMean_empty (hh : ‖h‖ = 1) (β ν : ℝ) (q : ↥(∅ : Finset (Torus d ℓ)) → SpinSphere N) :
    goodMean (∅ : Finset (Torus d ℓ)) β ν (goodJ (∅ : Finset (Torus d ℓ)) hh q) = 0 := by
  rw [goodJ_empty]
  funext x
  simp [goodMean, matAct]

/-- **T4.**  The reduced constant of the empty sector is `0`. -/
theorem goodReducedConst_empty (hh : ‖h‖ = 1) (β ν : ℝ)
    (q : ↥(∅ : Finset (Torus d ℓ)) → SpinSphere N) :
    goodReducedConst (∅ : Finset (Torus d ℓ)) hh β ν q = 0 := by
  unfold goodReducedConst goodBdryConst
  rw [goodJ_empty]
  simp [IsCrossing, goodPair, matAct]

/-- **T4.**  The reduced constant of an empty bad set `D = ∅` is `0`. -/
theorem goodReducedConst_of_eq_empty (D : Finset (Torus d ℓ)) (hD : D = ∅) (hh : ‖h‖ = 1)
    (β ν : ℝ) (q : ↥D → SpinSphere N) : goodReducedConst D hh β ν q = 0 := by
  subst hD
  exact goodReducedConst_empty hh β ν q

/-- **T4.**  An empty bad set `D = ∅` has bad factor `1`. -/
theorem kf0BadFactor_of_eq_empty (D : Finset (Torus d ℓ)) (hD : D = ∅) (s m : ℕ) [NeZero m]
    (r β ν : ℝ) (g : Torus d ℓ → Fin N → ℝ) (q : ↥D → SpinSphere N) :
    kf0BadFactor D s m r β ν h g (∅ : Finset (Torus d m)) q = 1 := by
  subst hD
  simp [kf0BadFactor, blockEnergyIn, sourceIn, badWeight]

/-- **T4.**  The empty sector: the prefactor is `fullNorm` (the prefactor of
`lintegral_restrictedIntegrand_gaussian`), `R_det = 1`, the mean is `0`, the reduced constant is
`0`, the bad factor is `1`; the sector integral is the full-torus normalizer times the integral,
over the (empty) bad configuration, of the good Gaussian integral. -/
theorem kf0SectorLint_empty (s m : ℕ) [NeZero m] (r : ℝ) {β ν : ℝ}
    (hβ : 0 < β) (hν : 0 < ν) (hh : ‖h‖ = 1) (hr : r ≤ 1) (g : Torus d ℓ → Fin N → ℝ) :
    kf0SectorLint s m r β ν h g (∅ : Finset (Torus d m)) =
      ENNReal.ofReal (fullNorm d ℓ N β ν) *
        ∫⁻ q, kf0GoodInner (siteUnion (ℓ := ℓ) s m (∅ : Finset (Torus d m))) hh s m r β ν g ∅ q
          ∂sigmaIn (siteUnion (ℓ := ℓ) s m (∅ : Finset (Torus d m))) := by
  rw [kf0SectorLint_eq s m r ∅ hβ hν hh hr g, kwSectorNorm_congr_empty s m β ν]
  congr 1
  unfold kf0SectorReduced
  refine lintegral_congr fun q => ?_
  rw [kf0BadFactor_of_eq_empty _ (siteUnion_empty s m) s m r β ν g q,
    goodReducedConst_of_eq_empty _ (siteUnion_empty s m) hh β ν q]
  simp

end T4

section T5

variable {d N ℓ : ℕ} [NeZero ℓ] {h : EuclideanSpace ℝ (Fin N)}

/-- The good Gaussian integral with the cutoff indicators dropped (named quantity of the crude
bound): `∫ dγ_G(ψ) J_β(v) · exp(shifted exponent)(v)` at `v = m(q) + C_G ψ`. -/
noncomputable def kf0GoodInnerDropped (D : Finset (Torus d ℓ)) (hh : ‖h‖ = 1) (β ν : ℝ)
    (g : Torus d ℓ → Fin N → ℝ) (q : ↥D → SpinSphere N) : ENNReal :=
  ∫⁻ ψ, ENNReal.ofReal (chartJac β (fun x =>
        (((goodMean D β ν (goodJ D hh q) + matAct (kwSqrt ν D) ψ) x : perp h) :
          EuclideanSpace ℝ (Fin N)))) *
      ENNReal.ofReal (Real.exp (goodShiftedExponent D β ν g h q
        (goodMean D β ν (goodJ D hh q) + matAct (kwSqrt ν D) ψ))) ∂(goodGaussian D h)

theorem goodWeight_le_one (D : Finset (Torus d ℓ)) (s m : ℕ) [NeZero m] (r : ℝ)
    (B : Finset (Torus d m)) (p : {x : Torus d ℓ // x ∉ D} → SpinSphere N) :
    goodWeight D h s m r B p ≤ 1 :=
  Finset.prod_le_one₀ (fun Q _ => (chiOut_nonneg_le D h s m r Q p).1) fun Q _ =>
    (chiOut_nonneg_le D h s m r Q p).2

theorem badWeight_le_one (D : Finset (Torus d ℓ)) (s m : ℕ) [NeZero m] (r : ℝ)
    (B : Finset (Torus d m)) (q : ↥D → SpinSphere N) :
    badWeight D h s m r B q ≤ 1 :=
  Finset.prod_le_one₀ (fun Q _ => by linarith [(chiIn_nonneg_le D h s m r Q q).2])
    fun Q _ => by linarith [(chiIn_nonneg_le D h s m r Q q).1]

theorem kf0GoodInner_le (D : Finset (Torus d ℓ)) (hh : ‖h‖ = 1) (s m : ℕ) [NeZero m] (r β ν : ℝ)
    (g : Torus d ℓ → Fin N → ℝ) (B : Finset (Torus d m)) (q : ↥D → SpinSphere N) :
    kf0GoodInner D hh s m r β ν g B q ≤ kf0GoodInnerDropped D hh β ν g q := by
  refine lintegral_mono fun ψ => ?_
  unfold kf0GoodIntegrand
  have : ENNReal.ofReal (goodWeight D h s m r B
      (chartCfgOn h hh ((Real.sqrt β)⁻¹ • (goodMean D β ν (goodJ D hh q) + matAct (kwSqrt ν D) ψ)))) ≤ 1 := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (goodWeight_le_one D s m r B _)
  calc _ ≤ ENNReal.ofReal (chartJac β (fun x =>
        (((goodMean D β ν (goodJ D hh q) + matAct (kwSqrt ν D) ψ) x : perp h) :
          EuclideanSpace ℝ (Fin N)))) * 1 *
      ENNReal.ofReal (Real.exp (goodShiftedExponent D β ν g h q
        (goodMean D β ν (goodJ D hh q) + matAct (kwSqrt ν D) ψ))) := by gcongr
    _ = _ := by rw [mul_one]
    
/-- **Peierls energy bound on the bad spins.**  If every block of `B` is bad for `q`
(`badWeight ≠ 0`), the bad energy is at least `ν r² #B / 2`. -/
theorem blockEnergyIn_ge (s m : ℕ) [NeZero m] (r : ℝ) (hr : 0 ≤ r) {ν : ℝ} (hν : 0 ≤ ν)
    (B : Finset (Torus d m)) (q : ↥(siteUnion (ℓ := ℓ) s m B) → SpinSphere N)
    (hq : badWeight (siteUnion (ℓ := ℓ) s m B) h s m r B q ≠ 0) :
    ν * r ^ 2 * B.card / 2 ≤ blockEnergyIn (siteUnion (ℓ := ℓ) s m B) ν h q := by
  have hx : ∀ Q : ↥B, ∃ x : ↥(siteUnion (ℓ := ℓ) s m B), blockMap s m x.1 = Q.1 ∧
      r ≤ ‖(q x : EuclideanSpace ℝ (Fin N)) - h‖ := by
    intro Q
    have h1 : (1 - chiIn (siteUnion (ℓ := ℓ) s m B) h s m r Q.1 q) ≠ 0 := fun h0 =>
      hq (Finset.prod_eq_zero Q.2 h0)
    have h2 : chiIn (siteUnion (ℓ := ℓ) s m B) h s m r Q.1 q ≠ 1 := fun h0 => h1 (by rw [h0]; ring)
    unfold chiIn at h2
    by_contra hcon
    push Not at hcon
    exact h2 (by split_ifs <;> rfl)
  choose xs hxs using hx
  have hinj : Function.Injective xs := by
    intro Q Q' he
    apply Subtype.ext
    rw [← (hxs Q).1, ← (hxs Q').1, he]
  have hsum : (B.card : ℝ) * r ^ 2 ≤
      ∑ x : ↥(siteUnion (ℓ := ℓ) s m B), ‖(q x : EuclideanSpace ℝ (Fin N)) - h‖ ^ 2 := by
    calc (B.card : ℝ) * r ^ 2 = ∑ Q : ↥B, r ^ 2 := by simp
      _ ≤ ∑ Q : ↥B, ‖(q (xs Q) : EuclideanSpace ℝ (Fin N)) - h‖ ^ 2 :=
          Finset.sum_le_sum fun Q _ => pow_le_pow_left₀ hr (hxs Q).2 2
      _ = ∑ x ∈ Finset.univ.image xs, ‖(q x : EuclideanSpace ℝ (Fin N)) - h‖ ^ 2 :=
          (Finset.sum_image (f := fun x : ↥(siteUnion (ℓ := ℓ) s m B) =>
            ‖(q x : EuclideanSpace ℝ (Fin N)) - h‖ ^ 2) fun a _ b _ he => hinj he).symm
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun _ _ _ => sq_nonneg _)
  unfold blockEnergyIn
  have hb : 0 ≤ (1 / 2 : ℝ) * ∑ x : ↥(siteUnion (ℓ := ℓ) s m B), ∑ μ : Fin d,
      (if hy : x.1 + Pi.single μ 1 ∈ siteUnion (ℓ := ℓ) s m B then
        ‖(q ⟨x.1 + Pi.single μ 1, hy⟩ : EuclideanSpace ℝ (Fin N)) - q x‖ ^ 2 else 0) :=
    mul_nonneg (by norm_num) (Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun μ _ => by
      split_ifs <;> positivity)
  nlinarith [mul_le_mul_of_nonneg_left hsum hν]

/-- The bad factor carries the Peierls charge `exp(-β ν r² #B / 2)`. -/
theorem kf0BadFactor_le (s m : ℕ) [NeZero m] (r : ℝ) (hr : 0 ≤ r) {β ν : ℝ} (hβ : 0 ≤ β)
    (hν : 0 ≤ ν) (g : Torus d ℓ → Fin N → ℝ) (B : Finset (Torus d m))
    (q : ↥(siteUnion (ℓ := ℓ) s m B) → SpinSphere N) :
    kf0BadFactor (siteUnion (ℓ := ℓ) s m B) s m r β ν h g B q ≤
      Real.exp (-(β * ν * r ^ 2 * B.card / 2)) *
        Real.exp (sourceIn (siteUnion (ℓ := ℓ) s m B) g q) := by
  unfold kf0BadFactor
  by_cases hq : badWeight (siteUnion (ℓ := ℓ) s m B) h s m r B q = 0
  · rw [hq, mul_zero]; positivity
  · have h1 := mul_le_mul_of_nonneg_left (blockEnergyIn_ge s m r hr hν B q hq) hβ
    rw [← Real.exp_add]
    calc _ ≤ Real.exp (-(β * blockEnergyIn (siteUnion (ℓ := ℓ) s m B) ν h q) +
            sourceIn (siteUnion (ℓ := ℓ) s m B) g q) * 1 :=
          mul_le_mul_of_nonneg_left (badWeight_le_one _ s m r B q) (Real.exp_pos _).le
      _ ≤ _ := by
          rw [mul_one]
          refine Real.exp_le_exp.2 ?_
          nlinarith

/-- **T5.**  Crude bound for a fixed sector: no control of the good Gaussian integral is needed.
`Z_B ≤ N_Λ · R_det(B) · exp(-β ν r² #B / 2) · ∫ dq_D e^{⟨g_D,q⟩} ∫ dγ_G J_β e^{shifted exponent}`;
the reduced constant is dropped (`goodReducedConst_nonneg`), the indicators are dropped
(`|goodWeight| ≤ 1`), and the bad energy is bounded below by the Peierls charge. -/
theorem kf0SectorLint_le_peierls (s m : ℕ) [NeZero m] (r : ℝ) (hr0 : 0 ≤ r) (hr : r ≤ 1)
    {β ν : ℝ} (hβ : 0 < β) (hν : 0 < ν) (hh : ‖h‖ = 1) (g : Torus d ℓ → Fin N → ℝ)
    (B : Finset (Torus d m)) :
    kf0SectorLint s m r β ν h g B ≤
      ENNReal.ofReal (fullNorm d ℓ N β ν) *
        ENNReal.ofReal (kwNormRatio d ℓ N β ν (siteUnion (ℓ := ℓ) s m B)) *
        ENNReal.ofReal (Real.exp (-(β * ν * r ^ 2 * B.card / 2))) *
        ∫⁻ q, ENNReal.ofReal (Real.exp (sourceIn (siteUnion (ℓ := ℓ) s m B) g q)) *
          kf0GoodInnerDropped (siteUnion (ℓ := ℓ) s m B) hh β ν g q
          ∂sigmaIn (siteUnion (ℓ := ℓ) s m B) := by
  rw [kf0SectorLint_eq s m r B hβ hν hh hr g, ← fullNorm_mul_ratio N hβ hν,
    ENNReal.ofReal_mul (fullNorm_pos N hβ hν).le]
  refine le_trans (mul_le_mul' le_rfl (?_ : kf0SectorReduced hh s m r β ν g B ≤
    ENNReal.ofReal (Real.exp (-(β * ν * r ^ 2 * B.card / 2))) *
        ∫⁻ q, ENNReal.ofReal (Real.exp (sourceIn (siteUnion (ℓ := ℓ) s m B) g q)) *
          kf0GoodInnerDropped (siteUnion (ℓ := ℓ) s m B) hh β ν g q
          ∂sigmaIn (siteUnion (ℓ := ℓ) s m B))) (le_of_eq (by ring))
  unfold kf0SectorReduced
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun q => ?_
  have hrc := goodReducedConst_nonneg (siteUnion (ℓ := ℓ) s m B) hh hν hβ.le q
  have hred : Real.exp (-goodReducedConst (siteUnion (ℓ := ℓ) s m B) hh β ν q) ≤ 1 :=
    Real.exp_le_one_iff.2 (by linarith)
  have hbad : kf0BadFactor (siteUnion (ℓ := ℓ) s m B) s m r β ν h g B q *
      Real.exp (-goodReducedConst (siteUnion (ℓ := ℓ) s m B) hh β ν q) ≤
      Real.exp (-(β * ν * r ^ 2 * B.card / 2)) *
        Real.exp (sourceIn (siteUnion (ℓ := ℓ) s m B) g q) := by
    calc _ ≤ kf0BadFactor (siteUnion (ℓ := ℓ) s m B) s m r β ν h g B q * 1 :=
          mul_le_mul_of_nonneg_left hred (mul_nonneg (Real.exp_pos _).le
            (badWeight_nonneg _ h s m r B q))
      _ ≤ _ := by rw [mul_one]; exact kf0BadFactor_le s m r hr0 hβ.le hν.le g B q
  calc _ ≤ ENNReal.ofReal (Real.exp (-(β * ν * r ^ 2 * B.card / 2)) *
        Real.exp (sourceIn (siteUnion (ℓ := ℓ) s m B) g q)) *
        kf0GoodInnerDropped (siteUnion (ℓ := ℓ) s m B) hh β ν g q :=
        mul_le_mul' (ENNReal.ofReal_le_ofReal hbad) (kf0GoodInner_le _ hh s m r β ν g B q)
    _ = _ := by rw [ENNReal.ofReal_mul (Real.exp_pos _).le]; ring

end T5

end Balaban.LargeField
