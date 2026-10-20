/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.KF0FRBern
public import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# `KF0FRJacSite`: the chart Jacobians of a set of sites (route FR, (E2))

`notes/phase1/KF0-FR.md` (E2). For a set `D` of sites the whitened chart coordinates
`u_x = β^{-1/2} ∑_y C_R(x,y) ψ_y`, `x ∈ D`, are an affine function of `ψ_D` with matrix
`β^{-1/2} (C_R)_{DD}`, whose determinant is at least `(β^{-1/2} c)^{|D|}` when `⟨v, C_R v⟩ ≥ c|v|²`
(`det_ge_of_form`, `det_submatrix_kf0CR_ge`). Integrating `ψ_D` against any per-site weights with a
bounded density then gives (`lintegral_jac_sites`)

`∫ ∏_{x ∈ D} w(u_x) ∏_x a_x(ψ_x) dψ_D ≤ ∏_{x ∈ D} A_x · |det(β^{-1/2} (C_R)_{DD})|^{-(N-1)} (∫ w)^{|D|}`

uniformly in the exterior variables `ψ_{D^c}`, where `a_x ≤ A_x` pointwise.
-/

@[expose] public section

open MeasureTheory Set Matrix Balaban.Green
open scoped ENNReal

namespace Balaban.LargeField.KF0FR

open SphereChart

noncomputable section

/-! ### Determinants of positive principal submatrices -/

/-- **A symmetric matrix with `⟨v, A v⟩ ≥ c |v|²` has `det A ≥ c^n`.** -/
theorem det_ge_of_form {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ) (hA : Aᵀ = A)
    {c : ℝ} (hc : 0 ≤ c) (hform : ∀ v : ι → ℝ, c * (v ⬝ᵥ v) ≤ v ⬝ᵥ A *ᵥ v) :
    c ^ Fintype.card ι ≤ A.det := by
  have hH : A.IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial, hA]
  rw [hH.det_eq_prod_eigenvalues]
  have hev : ∀ i, c ≤ hH.eigenvalues i := by
    intro i
    rw [hH.eigenvalues_eq]
    set v := hH.eigenvectorBasis i
    have h1 : ‖v‖ = 1 := hH.eigenvectorBasis.orthonormal.1 i
    have h2 : (⇑v : ι → ℝ) ⬝ᵥ (⇑v : ι → ℝ) = 1 := by
      have := EuclideanSpace.inner_eq_star_dotProduct v v
      rw [real_inner_self_eq_norm_sq, h1] at this
      simp only [one_pow, star_trivial] at this
      rw [dotProduct_comm]; exact this.symm
    have := hform v
    rw [h2, mul_one] at this
    simpa using this
  simp only [RCLike.ofReal_real_eq_id, id_eq]
  rw [← Finset.card_univ, ← Finset.prod_const]
  exact Finset.prod_le_prod₀ (fun _ _ => hc) (fun i _ => hev i)

variable {d m : ℕ} [NeZero m]

/-- **The principal submatrices of `C_R` are uniformly positive**: `det (C_R)_{DD} ≥ c^{|D|}` with
`c = (1 - q)(2d+ν)^{-1/2}`, `q = 2d/(2d+ν)`. -/
theorem det_submatrix_kf0CR_ge {ν : ℝ} (hν : 0 < ν) (R : ℕ) (D : Finset (Torus d m)) :
    ((1 - 2 * d / (2 * d + ν)) * (Real.sqrt (2 * d + ν))⁻¹) ^ D.card ≤
      ((kf0CR d m ν R).submatrix (Subtype.val : D → Torus d m) Subtype.val).det := by
  have hc : 0 ≤ (1 - 2 * d / (2 * d + ν)) * (Real.sqrt (2 * d + ν))⁻¹ := by
    have h1 : 2 * (d : ℝ) / (2 * d + ν) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith
    have : 0 ≤ 1 - 2 * (d : ℝ) / (2 * d + ν) := by linarith
    positivity
  rw [← Fintype.card_coe D]
  refine det_ge_of_form _ ?_ hc fun v => ?_
  · ext a b; simp [kf0CR_symm ν R b.1 a.1]
  · set w : Torus d m → ℝ := fun x => if hx : x ∈ D then v ⟨x, hx⟩ else 0 with hw
    have hform := kf0CR_form_ge (d := d) (m := m) hν R w
    have hww : w ⬝ᵥ w = v ⬝ᵥ v := by
      simp only [dotProduct, hw]
      rw [← Finset.sum_subset (Finset.subset_univ D) (fun x _ hx => by simp [hx])]
      rw [← Finset.sum_coe_sort D]
      exact Finset.sum_congr rfl fun x _ => by simp [x.2]
    have hwCw : w ⬝ᵥ kf0CR d m ν R *ᵥ w =
        v ⬝ᵥ ((kf0CR d m ν R).submatrix (Subtype.val : D → Torus d m) Subtype.val) *ᵥ v := by
      simp only [dotProduct, Matrix.mulVec, hw, Matrix.submatrix_apply]
      rw [← Finset.sum_subset (Finset.subset_univ D) (fun x _ hx => by simp [hx])]
      rw [← Finset.sum_coe_sort D]
      refine Finset.sum_congr rfl fun x _ => ?_
      simp only [x.2, dite_true]
      congr 1
      rw [← Finset.sum_subset (Finset.subset_univ D) (fun y _ hy => by simp [hy])]
      rw [← Finset.sum_coe_sort D]
      exact Finset.sum_congr rfl fun y _ => by simp [y.2]
    rw [← hww, ← hwCw]
    exact hform

/-! ### The Jacobian integral of a set of sites -/

variable {N : ℕ} (h : EuclideanSpace ℝ (Fin N))

/-- The standard Gaussian density on `h^⊥`. -/
def gDens (ψ : perp h) : ℝ :=
  (2 * Real.pi) ^ (-(Module.finrank ℝ (perp h) : ℝ) / 2) * Real.exp (-(1 / 2) * ‖ψ‖ ^ 2)

theorem gDens_nonneg (ψ : perp h) : 0 ≤ gDens h ψ := by unfold gDens; positivity

theorem measurable_gDens : Measurable (gDens h) := by unfold gDens; fun_prop

theorem oneSiteGaussian_eq_withDensity :
    oneSiteGaussian (perp h) = (volume : Measure (perp h)).withDensity
      (fun ψ => ENNReal.ofReal (gDens h ψ)) := rfl

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The Jacobian integral against Gaussian variables with bounded weighted density. -/
theorem lintegral_jac_gauss (hh : ‖h‖ = 1) {κ : Type*} [Fintype κ] [DecidableEq κ]
    (S : Matrix κ κ ℝ) (hS : IsUnit S.det) (b : κ → perp h) (c : κ → perp h → ℝ≥0∞)
    (hc : ∀ x, Measurable (c x)) (A : κ → ℝ≥0∞)
    (hA : ∀ x ψ, c x ψ * ENNReal.ofReal (gDens h ψ) ≤ A x) :
    ∫⁻ ψ : κ → perp h, (∏ x, c x (ψ x)) *
        ∏ z, ENNReal.ofReal (chartWeight h (matAct S ψ z + b z))
        ∂(Measure.pi fun _ => oneSiteGaussian (perp h)) ≤
      (∏ x, A x) * ((ENNReal.ofReal |S.det ^ (N - 1)|)⁻¹ *
        (∫⁻ v, ENNReal.ofReal (chartWeight h v)) ^ Fintype.card κ) := by
  have hdens : (Measure.pi fun _ : κ => oneSiteGaussian (perp h)) =
      (Measure.pi fun _ : κ => (volume : Measure (perp h))).withDensity
        (fun ψ => ∏ x, ENNReal.ofReal (gDens h (ψ x))) := by
    simp_rw [oneSiteGaussian_eq_withDensity]
    exact pi_withDensity_eq _ (fun _ => gDens h) (fun _ => measurable_gDens h)
  have hq : Measurable fun v : perp h => ENNReal.ofReal (chartWeight h v) :=
    ENNReal.measurable_ofReal.comp (measurable_chartWeight h)
  have hmS : Measurable fun ψ : κ → perp h => matAct S ψ :=
    (LinearMap.continuous_of_finiteDimensional (matActL (W := perp h) S)).measurable
  have hm1 : Measurable fun ψ : κ → perp h => ∏ x, ENNReal.ofReal (gDens h (ψ x)) :=
    Finset.measurable_prod _ fun x _ => ENNReal.measurable_ofReal.comp
      ((measurable_gDens h).comp (measurable_pi_apply x))
  rw [hdens, lintegral_withDensity_eq_lintegral_mul₀ hm1.aemeasurable]
  · calc ∫⁻ ψ, (∏ x, ENNReal.ofReal (gDens h (ψ x))) * ((∏ x, c x (ψ x)) *
          ∏ z, ENNReal.ofReal (chartWeight h (matAct S ψ z + b z)))
          ∂(Measure.pi fun _ : κ => (volume : Measure (perp h)))
        ≤ ∫⁻ ψ, (∏ x, A x) * ∏ z, ENNReal.ofReal (chartWeight h (matAct S ψ z + b z))
          ∂(Measure.pi fun _ : κ => (volume : Measure (perp h))) := by
          refine lintegral_mono fun ψ => ?_
          rw [← mul_assoc, ← Finset.prod_mul_distrib]
          refine mul_le_mul' (Finset.prod_le_prod fun x _ => ?_) le_rfl
          rw [mul_comm]; exact hA x (ψ x)
      _ = _ := by
          have hmeas : Measurable fun ψ : κ → perp h =>
              ∏ z, ENNReal.ofReal (chartWeight h (matAct S ψ z + b z)) :=
            Finset.measurable_prod _ fun z _ =>
              hq.comp ((measurable_pi_apply z).comp hmS |>.add_const (b z))
          rw [lintegral_const_mul _ hmeas, lintegral_prod_matAct_add h hh S hS b _ hq]
  · refine (Finset.measurable_prod _ fun x _ => (hc x).comp (measurable_pi_apply x)).mul
      (Finset.measurable_prod _ fun z _ => hq.comp ((measurable_pi_apply z).comp hmS
        |>.add_const (b z))) |>.aemeasurable

/-- The Jacobian integral against the site measure (Gaussian variables and sheets). -/
theorem lintegral_jac_site (hh : ‖h‖ = 1) {κ : Type*} [Fintype κ] [DecidableEq κ]
    (S : Matrix κ κ ℝ) (hS : IsUnit S.det) (b : κ → perp h) {ε : ℝ} (hε : 0 ≤ ε)
    (a : κ → perp h × Bool → ℝ≥0∞) (ha : ∀ x, Measurable (a x)) (A : κ → ℝ≥0∞)
    (hA : ∀ x ψ, (∫⁻ σ, a x (ψ, σ) ∂(frBern ε)) * ENNReal.ofReal (gDens h ψ) ≤ A x) :
    ∫⁻ ω : κ → perp h × Bool, (∏ x, a x (ω x)) *
        ∏ z, ENNReal.ofReal (chartWeight h (matAct S (fun y => (ω y).1) z + b z))
        ∂(Measure.pi fun _ => frSiteMeasure h ε) ≤
      (∏ x, A x) * ((ENNReal.ofReal |S.det ^ (N - 1)|)⁻¹ *
        (∫⁻ v, ENNReal.ofReal (chartWeight h v)) ^ Fintype.card κ) := by
  have hπ : IsProbabilityMeasure (frBern ε) := isProbabilityMeasure_frBern hε
  have hmp := measurePreserving_arrowProdEquivProdArrow (perp h) Bool κ
    (fun _ => oneSiteGaussian (perp h)) (fun _ => frBern ε)
  set e := MeasurableEquiv.arrowProdEquivProdArrow (perp h) Bool κ
  have hq : Measurable fun v : perp h => ENNReal.ofReal (chartWeight h v) :=
    ENNReal.measurable_ofReal.comp (measurable_chartWeight h)
  have hmS : Measurable fun ψ : κ → perp h => matAct S ψ :=
    (LinearMap.continuous_of_finiteDimensional (matActL (W := perp h) S)).measurable
  set Q : (κ → perp h) → ℝ≥0∞ := fun ψ =>
    ∏ z, ENNReal.ofReal (chartWeight h (matAct S ψ z + b z)) with hQ
  have hQm : Measurable Q := Finset.measurable_prod _ fun z _ =>
    hq.comp ((measurable_pi_apply z).comp hmS |>.add_const (b z))
  set G : (κ → perp h) × (κ → Bool) → ℝ≥0∞ := fun p =>
    (∏ x, a x (p.1 x, p.2 x)) * Q p.1 with hG
  have hGm : Measurable G := by
    refine (Finset.measurable_prod _ fun x _ => (ha x).comp ?_).mul (hQm.comp measurable_fst)
    exact ((measurable_pi_apply x).comp measurable_fst).prodMk
      ((measurable_pi_apply x).comp measurable_snd)
  have h1 : ∫⁻ ω : κ → perp h × Bool, (∏ x, a x (ω x)) *
      ∏ z, ENNReal.ofReal (chartWeight h (matAct S (fun y => (ω y).1) z + b z))
      ∂(Measure.pi fun _ => frSiteMeasure h ε) =
      ∫⁻ p, G p ∂((Measure.pi fun _ : κ => oneSiteGaussian (perp h)).prod
        (Measure.pi fun _ : κ => frBern ε)) := by
    rw [← hmp.lintegral_comp_emb e.measurableEmbedding]
    rfl
  rw [h1, lintegral_prod _ hGm.aemeasurable]
  have h2 : ∀ ψ : κ → perp h, ∫⁻ σ, G (ψ, σ) ∂(Measure.pi fun _ : κ => frBern ε) =
      (∏ x, ∫⁻ β, a x (ψ x, β) ∂(frBern ε)) * Q ψ := by
    intro ψ
    simp only [hG]
    have hm : Measurable fun σ : κ → Bool => ∏ x, a x (ψ x, σ x) :=
      Finset.measurable_prod _ fun x _ => (ha x).comp (measurable_const.prodMk (measurable_pi_apply x))
    rw [lintegral_mul_const _ hm]
    congr 1
    exact PiTools.lintegral_fintype_prod_eq_prod κ (fun x β => a x (ψ x, β))
      (fun x => (ha x).comp (measurable_const.prodMk measurable_id))
  simp_rw [h2]
  have hcm : ∀ x, Measurable fun ψ : perp h => ∫⁻ β, a x (ψ, β) ∂(frBern ε) := fun x =>
    (ha x).lintegral_prod_right'
  exact lintegral_jac_gauss h hh S hS b (fun x ψ => ∫⁻ β, a x (ψ, β) ∂(frBern ε)) hcm A hA

/-- **The Jacobian integral of the sites of `D`** (with the other sites fixed): integrating the
Gaussian variables and the sheets of `D` against per-site weights `a_x` whose sheet average times
the Gaussian density is at most `A_x`, the chart weights of the whitened coordinates of `D` cost at
most `|det S_D|^{-(N-1)} (∫ w)^{|D|}`. -/
theorem lintegral_jac_sites (hh : ‖h‖ = 1) (S : Matrix ι ι ℝ) (D : Finset ι)
    (hSD : IsUnit (S.submatrix (Subtype.val : D → ι) Subtype.val).det) {ε : ℝ} (hε : 0 ≤ ε)
    (a : ι → perp h × Bool → ℝ≥0∞) (ha : ∀ x, Measurable (a x)) (A : ι → ℝ≥0∞)
    (hA : ∀ x ∈ D, ∀ ψ, (∫⁻ b, a x (ψ, b) ∂(frBern ε)) * ENNReal.ofReal (gDens h ψ) ≤ A x) :
    ∫⁻ ω : ι → perp h × Bool, (∏ x, a x (ω x)) *
        ∏ z ∈ D, ENNReal.ofReal (chartWeight h (matAct S (fun y => (ω y).1) z))
        ∂(Measure.pi fun _ => frSiteMeasure h ε) ≤
      (∏ x : {x // x ∉ D}, ∫⁻ w, a x w ∂(frSiteMeasure h ε)) * (∏ x : D, A x) *
        ((ENNReal.ofReal |(S.submatrix (Subtype.val : D → ι) Subtype.val).det ^ (N - 1)|)⁻¹ *
          (∫⁻ v, ENNReal.ofReal (chartWeight h v)) ^ D.card) := by
  have hμ1 : IsProbabilityMeasure (frSiteMeasure h ε) := isProbabilityMeasure_frSiteMeasure h hε
  set e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => perp h × Bool) (· ∈ D)
  have hmp : MeasurePreserving e (Measure.pi fun _ : ι => frSiteMeasure h ε)
      ((Measure.pi fun _ : D => frSiteMeasure h ε).prod
        (Measure.pi fun _ : {x // x ∉ D} => frSiteMeasure h ε)) := by
    convert measurePreserving_piEquivPiSubtypeProd (fun _ : ι => frSiteMeasure h ε) (· ∈ D)
  set SD := S.submatrix (Subtype.val : D → ι) Subtype.val
  set bD : ({x // x ∉ D} → perp h × Bool) → D → perp h := fun ωc z =>
    ∑ y : {x // x ∉ D}, S z.1 y.1 • (ωc y).1 with hbD
  have hq : Measurable fun v : perp h => ENNReal.ofReal (chartWeight h v) :=
    ENNReal.measurable_ofReal.comp (measurable_chartWeight h)
  set F : (ι → perp h × Bool) → ℝ≥0∞ := fun ω => (∏ x, a x (ω x)) *
    ∏ z ∈ D, ENNReal.ofReal (chartWeight h (matAct S (fun y => (ω y).1) z)) with hF
  have hFm : Measurable F := by
    have hmS : Measurable fun ψ : ι → perp h => matAct S ψ :=
      (LinearMap.continuous_of_finiteDimensional (matActL (W := perp h) S)).measurable
    have hfst : Measurable fun ω : ι → perp h × Bool => fun y => (ω y).1 :=
      measurable_pi_iff.2 fun y => measurable_fst.comp (measurable_pi_apply y)
    exact (Finset.measurable_prod _ fun x _ => (ha x).comp (measurable_pi_apply x)).mul
      (Finset.measurable_prod _ fun z _ => hq.comp ((measurable_pi_apply z).comp (hmS.comp hfst)))
  have hsplit : ∀ p : (D → perp h × Bool) × ({x // x ∉ D} → perp h × Bool), F (e.symm p) =
      (∏ x : {x // x ∉ D}, a x (p.2 x)) * ((∏ x : D, a x (p.1 x)) *
        ∏ z : D, ENNReal.ofReal (chartWeight h (matAct SD (fun y => (p.1 y).1) z + bD p.2 z))) := by
    intro p
    have he : ∀ x, e.symm p x = if hx : x ∈ D then p.1 ⟨x, hx⟩ else p.2 ⟨x, hx⟩ := fun x => rfl
    simp only [hF]
    have h1 : ∏ x, a x (e.symm p x) = (∏ x : D, a x (p.1 x)) * ∏ x : {x // x ∉ D}, a x (p.2 x) := by
      rw [← Fintype.prod_subtype_mul_prod_subtype (· ∈ D) (fun x => a x (e.symm p x))]
      congr 1
      · exact Finset.prod_congr (by ext; simp) fun x _ => by simp [he, x.2]
      · exact Finset.prod_congr (by ext; simp) fun x _ => by simp [he, x.2]
    have h2 : ∏ z ∈ D, ENNReal.ofReal (chartWeight h (matAct S (fun y => (e.symm p y).1) z)) =
        ∏ z : D, ENNReal.ofReal (chartWeight h (matAct SD (fun y => (p.1 y).1) z + bD p.2 z)) := by
      rw [← Finset.prod_coe_sort D]
      refine Finset.prod_congr rfl fun z _ => ?_
      congr 2
      apply Subtype.ext
      simp only [matAct, Submodule.coe_add, Submodule.coe_sum, Submodule.coe_smul, hbD, SD,
        Matrix.submatrix_apply]
      rw [← Fintype.sum_subtype_add_sum_subtype (· ∈ D)
        (fun y => S z.1 y • (((e.symm p y).1 : perp h) : EuclideanSpace ℝ (Fin N)))]
      congr 1
      · exact Finset.sum_congr (by ext; simp) fun y _ => by simp [he, y.2]
      · exact Finset.sum_congr (by ext; simp) fun y _ => by simp [he, y.2]
    rw [h1, h2]
    ring
  have h1 : ∫⁻ ω, F ω ∂(Measure.pi fun _ => frSiteMeasure h ε) =
      ∫⁻ p, F (e.symm p) ∂((Measure.pi fun i : D => frSiteMeasure h ε).prod
        (Measure.pi fun i : {x // x ∉ D} => frSiteMeasure h ε)) := by
    have := hmp.lintegral_comp_emb e.measurableEmbedding (fun p => F (e.symm p))
    simp only [MeasurableEquiv.symm_apply_apply] at this
    exact this
  change ∫⁻ ω, F ω ∂(Measure.pi fun _ => frSiteMeasure h ε) ≤ _
  rw [h1, lintegral_prod_symm (fun p => F (e.symm p)) (hFm.comp e.symm.measurable).aemeasurable]
  simp_rw [hsplit]
  have hinner : ∀ ωc : {x // x ∉ D} → perp h × Bool,
      ∫⁻ ωD : D → perp h × Bool, (∏ x : {x // x ∉ D}, a x (ωc x)) * ((∏ x : D, a x (ωD x)) *
        ∏ z : D, ENNReal.ofReal (chartWeight h (matAct SD (fun y => (ωD y).1) z + bD ωc z)))
        ∂(Measure.pi fun i : D => frSiteMeasure h ε) ≤
      (∏ x : {x // x ∉ D}, a x (ωc x)) * ((∏ x : D, A x) *
        ((ENNReal.ofReal |SD.det ^ (N - 1)|)⁻¹ *
          (∫⁻ v, ENNReal.ofReal (chartWeight h v)) ^ Fintype.card D)) := by
    intro ωc
    have hmSD : Measurable fun ψ : D → perp h => matAct SD ψ :=
      (LinearMap.continuous_of_finiteDimensional (matActL (W := perp h) SD)).measurable
    have hfst : Measurable fun ω : D → perp h × Bool => fun y => (ω y).1 :=
      measurable_pi_iff.2 fun y => measurable_fst.comp (measurable_pi_apply y)
    have hm1 : Measurable fun ωD : D → perp h × Bool => ∏ x : D, a x (ωD x) :=
      Finset.measurable_prod _ fun x _ => (ha x.1).comp (measurable_pi_apply x)
    have hm2 : Measurable fun ωD : D → perp h × Bool =>
        ∏ z : D, ENNReal.ofReal (chartWeight h (matAct SD (fun y => (ωD y).1) z + bD ωc z)) :=
      Finset.measurable_prod _ fun z _ =>
        hq.comp (((measurable_pi_apply z).comp (hmSD.comp hfst)).add_const (bD ωc z))
    have hmeas : Measurable fun ωD : D → perp h × Bool => (∏ x : D, a x (ωD x)) *
        ∏ z : D, ENNReal.ofReal (chartWeight h (matAct SD (fun y => (ωD y).1) z + bD ωc z)) :=
      hm1.mul hm2
    rw [lintegral_const_mul _ hmeas]
    exact mul_le_mul' le_rfl (lintegral_jac_site h hh SD hSD (bD ωc) hε (fun x => a x.1)
      (fun x => ha x.1) (fun x => A x.1) (fun x ψ => hA x.1 x.2 ψ))
  refine (lintegral_mono hinner).trans ?_
  have hmc : Measurable fun ωc : {x // x ∉ D} → perp h × Bool => ∏ x : {x // x ∉ D}, a x (ωc x) :=
    Finset.measurable_prod _ fun x _ => (ha x).comp (measurable_pi_apply x)
  rw [lintegral_mul_const _ hmc, PiTools.lintegral_fintype_prod_eq_prod {x // x ∉ D}
    (fun x w => a x w) (fun x => ha x), Fintype.card_coe, mul_assoc]

end

end Balaban.LargeField.KF0FR
