/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseChartCutTangent

/-!
# The cut chart integral over a component with the exterior held fixed

For a union `U` of first blocks (a proper one is allowed) the cut operator is block diagonal.
The chart integral over the spins on the sites of `U`, with the tangent coordinates of the
other spins fixed, is a Gaussian integral for the real principal submatrix `K_U` of the cut
operator `A(s)`.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Background Balaban.Multiscale Balaban.Green Matrix MeasureTheory SphereChart
  Classical
open Balaban.LargeField.Base Balaban.Localization

section Generic

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] {N : ℕ}

/-- The base operator restricted to an injective family of sites is the base operator of the
restricted data. -/
theorem baseOp_submatrix_comp (f : κ → ι) (hf : Function.Injective f) (e : ι → Fin N → ℝ)
    (H : Matrix ι ι ℂ) :
    (baseOp N (fun z i => (e z i : ℂ)) H).submatrix (fun p => (f p.1, p.2))
        (fun p => (f p.1, p.2)) =
      baseOp N (fun z i => (e (f z) i : ℂ)) (H.submatrix f f) := by
  ext p q
  have h1 := congrFun (congrFun (blockOf_baseOp e H (f p.1) (f q.1)) p.2) q.2
  have h2 := congrFun (congrFun
    (blockOf_baseOp (fun z => e (f z)) (H.submatrix f f) p.1 q.1) p.2) q.2
  simp only [blockOf, Matrix.of_apply] at h1 h2
  simp only [Matrix.submatrix_apply]
  rw [h1, h2]
  simp only [hf.eq_iff]
  rfl

end Generic

section Split

variable {X : Type*} [Fintype X] [DecidableEq X] {N : ℕ}

omit [DecidableEq X] in
/-- If the scalar matrix of a componentwise Hessian vanishes between the supports of two
configurations, then the form pairs them to zero. -/
theorem cinner_hessian_eq_zero_of_disjoint (hs : X → X → ℝ)
    (Hs : Config X N →ₗ[ℝ] Config X N)
    (hHs : ∀ u x i, (Hs u x i : ℝ) = ∑ y, hs x y * (u y i : ℝ)) (a b : Config X N)
    (hab : ∀ x y, a x ≠ 0 → b y ≠ 0 → hs x y = 0) :
    cinner a (Hs b) = 0 := by
  unfold cinner
  refine Finset.sum_eq_zero fun x _ => ?_
  by_cases hx : a x = 0
  · simp [hx]
  · have : Hs b x = 0 := by
      ext i
      rw [hHs]
      refine Finset.sum_eq_zero fun y _ => ?_
      by_cases hy : b y = 0
      · simp [hy]
      · rw [hab x y hx hy, zero_mul]
    simp [this]

omit [DecidableEq X] in
/-- The quadratic form of a block diagonal componentwise Hessian splits over configurations
supported on the two blocks. -/
theorem cinner_hessian_add_of_cross_zero (P : X → Prop) (hs : X → X → ℝ)
    (hcross : ∀ x y, (P x ↔ ¬ P y) → hs x y = 0)
    (Hs : Config X N →ₗ[ℝ] Config X N)
    (hHs : ∀ u x i, (Hs u x i : ℝ) = ∑ y, hs x y * (u y i : ℝ)) (a b : Config X N)
    (ha : ∀ x, ¬ P x → a x = 0) (hb : ∀ x, P x → b x = 0) :
    cinner (a + b) (Hs (a + b)) = cinner a (Hs a) + cinner b (Hs b) := by
  have h1 : cinner a (Hs b) = 0 := by
    refine cinner_hessian_eq_zero_of_disjoint hs Hs hHs a b fun x y hx hy => ?_
    refine hcross x y ?_
    constructor
    · intro hPx hPy
      exact hy (hb y hPy)
    · intro hPy
      by_contra hPx
      exact hx (ha x hPx)
  have h2 : cinner b (Hs a) = 0 := by
    refine cinner_hessian_eq_zero_of_disjoint hs Hs hHs b a fun x y hx hy => ?_
    refine hcross x y ?_
    constructor
    · intro hPx
      exact absurd hPx (fun hPx => hx (hb x hPx))
    · intro hPy
      by_contra hPx
      exact hy (ha y (by tauto))
  rw [map_add, cinner_add_left, cinner_add_right, cinner_add_right, h1, h2]
  ring

omit [DecidableEq X] in
/-- The form of a componentwise Hessian on a configuration supported on a set of sites is the
form of the restricted Hessian. -/
theorem cinner_hessian_ext_zero (P : X → Prop) (hs : X → X → ℝ)
    (Hs : Config X N →ₗ[ℝ] Config X N)
    (hHs : ∀ u x i, (Hs u x i : ℝ) = ∑ y, hs x y * (u y i : ℝ))
    [DecidablePred P]
    (HsT : Config {x // P x} N →ₗ[ℝ] Config {x // P x} N)
    (hHsT : ∀ u x i, (HsT u x i : ℝ) = ∑ y : {x // P x}, hs x y * (u y i : ℝ))
    (u : Config {x // P x} N) :
    cinner (fun x => if hx : P x then u ⟨x, hx⟩ else 0)
        (Hs (fun x => if hx : P x then u ⟨x, hx⟩ else 0)) = cinner u (HsT u) := by
  set w : Config X N := fun x => if hx : P x then u ⟨x, hx⟩ else 0 with hw
  unfold cinner
  rw [← Fintype.sum_subtype_add_sum_subtype P]
  have h0 : ∑ x : {x // ¬ P x}, inner ℝ (w x) (Hs w x) = 0 := by
    refine Finset.sum_eq_zero fun x _ => ?_
    simp [hw, x.2]
  rw [h0, add_zero]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hwx : w x = u x := by simp [hw, x.2]
  have : Hs w x = HsT u x := by
    ext i
    rw [hHs, hHsT, ← Fintype.sum_subtype_add_sum_subtype P]
    have hz : ∑ y : {x // ¬ P x}, hs x y * (w y i : ℝ) = 0 := by
      refine Finset.sum_eq_zero fun y _ => ?_
      simp [hw, y.2]
    rw [hz, add_zero]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp [hw, y.2]
  rw [hwx, this]

end Split

section Bound

variable {d N L n : ℕ} [NeZero L] [NeZero n] [NeZero N]

/-- The spin integrand `χ K exp(-βH + ⟨g, ·⟩)` of the a priori measure is measurable and bounded
for a measurable cutoff `χ` with values in `[-1, 1]`. -/
theorem baseGood_integrand_bound {β a : ℝ} (hβ : 0 < β) (ha : 0 < a) (ν : ℝ)
    (h : EuclideanSpace ℝ (Fin N)) (g : Torus d (L * n) → Fin N → ℂ)
    (θ : Torus d n → EuclideanSpace ℝ (Fin N)) (χ : CfgT d N L n → ℝ)
    (hχ : Measurable χ) (hχ1 : ∀ φ, |χ φ| ≤ 1) :
    Measurable (fun φ : CfgT d N L n => (χ φ : ℂ) * ((baseKernel d N L n β a θ φ : ℝ) : ℂ) *
      Complex.exp (-((β * energy d N (L * n) ν h φ : ℝ) : ℂ)
        + ∑ x : Torus d (L * n), ∑ i : Fin N,
          g x i * (((φ x : EuclideanSpace ℝ (Fin N)) i : ℝ) : ℂ))) ∧
    ∃ C : ℝ, ∀ φ : CfgT d N L n, ‖(χ φ : ℂ) * ((baseKernel d N L n β a θ φ : ℝ) : ℂ) *
      Complex.exp (-((β * energy d N (L * n) ν h φ : ℝ) : ℂ)
        + ∑ x : Torus d (L * n), ∑ i : Fin N,
          g x i * (((φ x : EuclideanSpace ℝ (Fin N)) i : ℝ) : ℂ))‖ ≤ C := by
  obtain ⟨hm, C, hC⟩ := spin_integrand_bound (L := L) (n := n) β ν h g
  have hk : Measurable fun φ : CfgT d N L n => baseKernel d N L n β a θ φ := by
    have := (measurable_baseKernel (n := n) (L := L) (N := N) β a 1).comp
      (measurable_const (a := θ).prodMk measurable_id)
    simpa [Function.comp_def] using this
  have hkle : ∀ φ : CfgT d N L n, baseKernel d N L n β a θ φ ≤
      ∏ _y : Torus d n, ((β * a * (L : ℝ) ^ d / (L : ℝ) ^ 2) / (2 * Real.pi)) ^
        ((N : ℝ) / 2) := by
    intro φ
    unfold baseKernel
    refine Finset.prod_le_prod₀ (fun y _ => gaussT_nonneg N _ (baseKernel_pos hβ ha).le _ _)
      (fun y _ => ?_)
    unfold gaussT
    have : 0 ≤ ((β * a * (L : ℝ) ^ d / (L : ℝ) ^ 2) / (2 * Real.pi)) ^ ((N : ℝ) / 2) :=
      Real.rpow_nonneg (div_nonneg (baseKernel_pos hβ ha).le (by positivity)) _
    have hexp : Real.exp (-((β * a * (L : ℝ) ^ d / (L : ℝ) ^ 2) / 2) *
        ‖θ y - baseQ d N L n φ y‖ ^ 2) ≤ 1 := by
      apply Real.exp_le_one_iff.2
      have := sq_nonneg ‖θ y - baseQ d N L n φ y‖
      have h2 := (baseKernel_pos (d := d) (L := L) hβ ha).le
      nlinarith
    exact mul_le_of_le_one_right this hexp
  refine ⟨((Complex.measurable_ofReal.comp hχ).mul
    (Complex.measurable_ofReal.comp hk)).mul hm, ?_⟩
  refine ⟨(∏ _y : Torus d n, ((β * a * (L : ℝ) ^ d / (L : ℝ) ^ 2) / (2 * Real.pi)) ^
      ((N : ℝ) / 2)) * C, fun φ => ?_⟩
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_of_nonneg (baseKernel_nonneg hβ ha _ _)]
  have h0 : 0 ≤ ∏ _y : Torus d n, ((β * a * (L : ℝ) ^ d / (L : ℝ) ^ 2) / (2 * Real.pi)) ^
      ((N : ℝ) / 2) :=
    Finset.prod_nonneg fun _ _ => Real.rpow_nonneg
      (div_nonneg (baseKernel_pos hβ ha).le (by positivity)) _
  calc |χ φ| * baseKernel d N L n β a θ φ *
        ‖Complex.exp (-((β * energy d N (L * n) ν h φ : ℝ) : ℂ)
          + ∑ x : Torus d (L * n), ∑ i : Fin N,
            g x i * (((φ x : EuclideanSpace ℝ (Fin N)) i : ℝ) : ℂ))‖
      ≤ 1 * (∏ _y : Torus d n, ((β * a * (L : ℝ) ^ d / (L : ℝ) ^ 2) / (2 * Real.pi)) ^
          ((N : ℝ) / 2)) * C := by
        refine mul_le_mul (mul_le_mul (hχ1 φ) (hkle φ) (baseKernel_nonneg hβ ha _ _)
          zero_le_one) (hC φ) (norm_nonneg _) (by positivity)
    _ = _ := by ring

end Bound

section Physical

variable {d N L n : ℕ} [NeZero L] [NeZero n] [NeZero N]

attribute [local fun_prop] measurable_chartMapPi

omit [NeZero N] in
/-- Cut chart integral over a first-block component. -/
theorem baseChartIntegral_retained
    {β : ℝ} (a₀ ν δ₀ : ℝ)
    (ϱ : ℝ) (aw : ℕ → ℝ)
    (regimeB : Prop) (hδ : 0 < δ₀)
    (h : EuclideanSpace ℝ (Fin N)) (hh : ‖h‖ = 1)
    (H : BgHyp d L 1 ϱ aw (if regimeB then ν else 0))
    (hΛ1 : 4 * d * L * δ₀ ≤ bgC1 d L N)
    (g : Torus d (L * n) → Fin N → ℂ)
    (θ : Torus d n → EuclideanSpace ℝ (Fin N))
    (φ₀ : CfgT d N L n)
    (hp : baseSectorCubeProduct regimeB ν δ₀ h θ φ₀ ≠ 0)
    (U : Set (Torus d (1 * n * L ^ 1)))
    (hU : IsFirstBlockUnion (GeneratingSet.single (d := d) (L := L)
      (N₀ := 1 * n) (k := 1) ϱ) U)
    {η : ℝ} (hη0 : 0 ≤ η)
    (hη : η ≤ baseCoercivity L / (8 * d))
    (s : FineBond d L (1 * n) → ℂ)
    (hs : s ∈ baseParamNbhd (GeneratingSet.single (d := d) (L := L)
      (N₀ := 1 * n) (k := 1) ϱ) η)
    (hz : CrossZero (GeneratingSet.single (d := d) (L := L)
      (N₀ := 1 * n) (k := 1) ϱ) U s)
    (hsr : ∀ b ∈ baseCutBonds (GeneratingSet.single (d := d) (L := L)
      (N₀ := 1 * n) (k := 1) ϱ), (s b).im = 0) :
    let G : GeneratingSet d L (1 * n) 1 ϱ := GeneratingSet.single ϱ
    let α := bgMult G aw (if regimeB then ν else 0) (baseSectorDatum ϱ θ h)
    let e : Config (Torus d (L * n)) N := baseSectorCenter ϱ aw regimeB ν h θ
    let he := baseSectorCenter_unit ϱ aw regimeB ν h hh H θ
    let ec : CfgT d N L n := fun x => ⟨e x, mem_sphere_zero_iff_norm.mpr (he x)⟩
    let Hα : Config (Torus d (L * n)) N →ₗ[ℝ] Config (Torus d (L * n)) N :=
      baseSectorHessian ϱ aw (if regimeB then ν else 0) (fun p => (α p).re)
    let χ := baseSectorCubeProduct regimeB ν δ₀ h θ
    let eG : G.Ω 1 → Fin N → ℝ := fun z i =>
      (baseSectorCenter ϱ aw regimeB ν h θ
        (baseSector_side L n ▸ (z : Torus d (1 * n * L ^ 1))) i : ℝ)
    let A := baseOp N (fun z i => (eG z i : ℂ))
      (baseHamiltonian G aw (if regimeB then ν else 0) α s)
    let P : G.Ω 1 × Fin N → Prop := fun p =>
      (p.1 : Torus d (1 * n * L ^ 1)) ∈ U
    let I := {p : G.Ω 1 × Fin N // P p}
    let A_U : Matrix I I ℂ := A.submatrix Subtype.val Subtype.val
    let K_U := A_U.map Complex.re
    let F : ((x : Torus d (L * n)) → perp (e x)) → ℂ := fun v =>
      let φ := chartMapPi e he ((Real.sqrt β)⁻¹ • v)
      let w : Config (Torus d (L * n)) N := fun x => (v x : EuclideanSpace ℝ (Fin N))
      let z := chartShift β e w
      let W : G.Ω 1 × Fin N → ℂ := fun p =>
        (((w (baseSector_side L n ▸ (p.1 : Torus d (1 * n * L ^ 1)))) p.2 : ℝ) : ℂ)
      let q : (FineBond d L (1 * n) → ℂ) → ℂ := fun t =>
        (1 / 2) * pair G W (liftOp N (baseHamiltonian G aw
          (if regimeB then ν else 0) α t) *ᵥ W)
      let M := β * (ν - (if regimeB then ν else 0)) / 2 *
        ∑ x : Torus d (L * n), ‖(φ x : EuclideanSpace ℝ (Fin N)) - h‖ ^ 2
      ((chartJac β w : ℝ) : ℂ) *
        ((χ φ : ℂ) *
          ((∏ _y : Torus d n,
            ((β * a₀ * (L : ℝ) ^ d / (L : ℝ) ^ 2) / (2 * Real.pi)) ^
              ((N : ℝ) / 2) : ℝ) : ℂ) *
          Complex.exp (
            -((β * (energy d N (L * n) (if regimeB then ν else 0) h ec +
              (a₀ * (L : ℝ) ^ d / (2 * (L : ℝ) ^ 2)) *
                ∑ y : Torus d n, ‖θ y - baseQ d N L n ec y‖ ^ 2) : ℝ) : ℂ) +
            (∑ x : Torus d (L * n), ∑ i : Fin N,
              g x i * (((e x) i : ℝ) : ℂ)) +
            (((Real.sqrt β)⁻¹ : ℝ) : ℂ) *
              (∑ x : Torus d (L * n), ∑ i : Fin N,
                g x i * (((w x + z x) i : ℝ) : ℂ)) -
            (((cinner w (Hα z) + (1 / 2) * cinner z (Hα z) + M : ℝ) : ℂ) +
              (q (fun _ => 1) - q s))))
    let site : Torus d (L * n) → G.Ω 1 := fun x =>
      ⟨(baseSector_side L n).symm ▸ x,
        baseSector_mem_single ϱ ((baseSector_side L n).symm ▸ x)⟩
    let Pt : Torus d (L * n) → Prop := fun x =>
      ((site x : G.Ω 1) : Torus d (1 * n * L ^ 1)) ∈ U
    let qS : ((x : Torus d (L * n)) → perp (e x)) → ℂ := fun v =>
      (1 / 2) * pair G (fun p : G.Ω 1 × Fin N =>
          (((fun x => (v x : EuclideanSpace ℝ (Fin N))) (baseSector_side L n ▸
            (p.1 : Torus d (1 * n * L ^ 1))) p.2 : ℝ) : ℂ))
        (liftOp N (baseHamiltonian G aw (if regimeB then ν else 0) α s) *ᵥ
          fun p : G.Ω 1 × Fin N =>
            (((fun x => (v x : EuclideanSpace ℝ (Fin N))) (baseSector_side L n ▸
              (p.1 : Torus d (1 * n * L ^ 1))) p.2 : ℝ) : ℂ))
    ∃ (HsT : Config {x // Pt x} N →ₗ[ℝ] Config {x // Pt x} N)
      (R : Config {x // Pt x} N ≃ₗ[ℝ] Config {x // Pt x} N),
      (∀ u x i, (HsT u x i : ℝ) = ∑ y : {x // Pt x},
        (baseHamiltonian G aw (if regimeB then ν else 0) α s
          (site x) (site y)).re * (u y i : ℝ)) ∧
      (∀ w, gaussForm (fun x : {x // Pt x} => e x) HsT (R (R w)) = w) ∧
      (∀ u v, cinner (R u) v = cinner u (R v)) ∧
      LinearMap.det (R : Config {x // Pt x} N →ₗ[ℝ] Config {x // Pt x} N) =
        (pdSqrtInv K_U).det ∧
      ∀ vJ : (x : {x : Torus d (L * n) // ¬ Pt x}) → perp (e x),
        ∫ vI : (x : {x // Pt x}) → perp (e x),
            Complex.exp (-qS (fun x => if hx : Pt x then vI ⟨x, hx⟩ else vJ ⟨x, hx⟩)) *
              F (fun x => if hx : Pt x then vI ⟨x, hx⟩ else vJ ⟨x, hx⟩)
          ∂(Measure.pi fun x : {x // Pt x} => (volume : Measure (perp (e x)))) =
          (((2 * Real.pi) ^ (((N : ℝ) - 1) * Fintype.card {x // Pt x} / 2) *
            (pdSqrtInv K_U).det : ℝ) : ℂ) *
            (Complex.exp (-qS (fun x => if hx : Pt x then 0 else vJ ⟨x, hx⟩)) *
              ∫ ψ, F (fun x => if hx : Pt x then
                  tangentProj (fun x : {x // Pt x} => e x) (fun x => he x) (R ψ) ⟨x, hx⟩
                else vJ ⟨x, hx⟩)
                ∂(stdGaussian {x // Pt x} N)) := by
  intro G α e he ec Hα χ eG A P I A_U K_U F site Pt qS
  have hα : ∀ z, (α z).im = 0 :=
    baseSector_bgMult_real_of_product_ne_zero ϱ aw regimeB ν δ₀ hδ h hh H hΛ1 θ φ₀ hp
  have hHim := baseHamiltonian_im_eq_zero G aw (if regimeB then ν else 0) α s hα hsr
  have hpd := baseSector_selected_cut_component_posDef ϱ aw regimeB ν δ₀ hδ h hh H hΛ1 θ φ₀ hp
    U hη0 hη s hs hsr
  have hKU : K_U.PosDef := hpd.2.1
  have hmU : K_U.map (algebraMap ℝ ℂ) = A_U := hpd.2.2.2.1
  have castF {a b : ℕ} (h : a = b) (x : Torus d b) :
      h ▸ (h.symm ▸ x) = x := by
    cases h
    rfl
  have castR {a b : ℕ} (h : a = b) (x : Torus d a) :
      h.symm ▸ (h ▸ x) = x := by
    cases h
    rfl
  let t : G.Ω 1 ≃ Torus d (L * n) :=
    { toFun := fun z => baseSector_side L n ▸ (z : Torus d (1 * n * L ^ 1))
      invFun := site
      left_inv := by intro z; apply Subtype.ext; exact castR (baseSector_side L n) z.1
      right_inv := fun x => castF (baseSector_side L n) x }
  have hts : ∀ x, t (site x) = x := fun x => castF (baseSector_side L n) x
  have hst : ∀ z, site (t z) = z := fun z => t.symm_apply_apply z
  have hcross : ∀ x y : Torus d (L * n), (Pt x ↔ ¬ Pt y) →
      (baseHamiltonian G aw (if regimeB then ν else 0) α s (site x) (site y)).re = 0 := by
    intro x y hxy
    have := baseHamiltonian_cross_zero G hU aw (if regimeB then ν else 0) α hz
      (site x) (site y) hxy
    rw [this]
    rfl
  obtain ⟨Hs, hHs, -⟩ := exists_hessian_chart_of_real_baseOp t e
    (baseHamiltonian G aw (if regimeB then ν else 0) α s) hHim
  have hHs' : ∀ u x i, (Hs u x i : ℝ) = ∑ y,
      (baseHamiltonian G aw (if regimeB then ν else 0) α s (site x) (site y)).re *
        (u y i : ℝ) := hHs
  have hqS : ∀ v, qS v = (1 / 2 : ℂ) * ((cinner (fun x => (v x : EuclideanSpace ℝ (Fin N)))
      (Hs (fun x => (v x : EuclideanSpace ℝ (Fin N)))) : ℝ) : ℂ) := by
    intro v
    change (1 / 2 : ℂ) * pair G _ _ = _
    congr 1
    exact pair_liftOp_eq_cinner t (baseHamiltonian G aw (if regimeB then ν else 0) α s)
      hHim Hs hHs (fun x => (v x : EuclideanSpace ℝ (Fin N)))
  let T := {x : Torus d (L * n) // Pt x}
  let eT : Config T N := fun x => e x
  have heT : ∀ x : T, ‖eT x‖ = 1 := fun x => he x
  let H' : Matrix T T ℂ := fun x y =>
    baseHamiltonian G aw (if regimeB then ν else 0) α s (site x.1) (site y.1)
  obtain ⟨HsT, hHsT, hmat⟩ := exists_hessian_chart_of_real_baseOp (Equiv.refl T) eT H'
    (fun x y => hHim _ _)
  have hHsT' : ∀ u x i, (HsT u x i : ℝ) = ∑ y : T,
      (baseHamiltonian G aw (if regimeB then ν else 0) α s (site x) (site y)).re *
        (u y i : ℝ) := hHsT
  let f : T → G.Ω 1 := fun x => site x.1
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    have := congrArg t hxy
    simpa only [f, hts] using this
  let ρ : I ≃ T × Fin N :=
    { toFun := fun p => (⟨t p.1.1, by
        change ((site (t p.1.1) : G.Ω 1) : Torus d (1 * n * L ^ 1)) ∈ U
        rw [hst]
        exact p.2⟩, p.1.2)
      invFun := fun q => ⟨(f q.1, q.2), q.1.2⟩
      left_inv := by
        intro p
        apply Subtype.ext
        apply Prod.ext
        · exact hst p.1.1
        · rfl
      right_inv := by
        intro q
        apply Prod.ext
        · exact Subtype.ext (hts q.1.1)
        · rfl }
  let B := Pi.basis (fun _ : T => (EuclideanSpace.basisFun (Fin N) ℝ).toBasis)
  let σ := Equiv.sigmaEquivProd T (Fin N)
  have hKmat : Matrix.reindex σ σ (LinearMap.toMatrix B B (gaussForm eT HsT)) =
      Matrix.reindex ρ ρ K_U := by
    apply Matrix.map_injective (algebraMap ℝ ℂ).injective
    refine hmat.trans ?_
    have hsub := baseOp_submatrix_comp f hf eG
      (baseHamiltonian G aw (if regimeB then ν else 0) α s)
    have h2 : (Matrix.reindex ρ ρ K_U).map (algebraMap ℝ ℂ) = Matrix.reindex ρ ρ A_U := by
      rw [← hmU]
      ext a b
      rfl
    show _ = (Matrix.reindex ρ ρ K_U).map (algebraMap ℝ ℂ)
    rw [h2]
    ext a b
    have h1 := congrFun (congrFun hsub a) b
    have he' : (fun (x : T) (i : Fin N) => ((eT x i : ℝ) : ℂ)) =
        fun (z : T) (i : Fin N) => ((eG (f z) i : ℝ) : ℂ) := by
      funext z i
      change ((e z i : ℝ) : ℂ) = ((e (t (site z.1)) i : ℝ) : ℂ)
      rw [hts]
    change baseOp N (fun x i => ((eT x i : ℝ) : ℂ)) H' a b = A (f a.1, a.2) (f b.1, b.2)
    rw [he']
    exact h1.symm
  have hKphys : (LinearMap.toMatrix B B (gaussForm eT HsT)).PosDef := by
    have h1 : (Matrix.reindex ρ ρ K_U).PosDef := hKU.submatrix ρ.symm.injective
    have h2 : LinearMap.toMatrix B B (gaussForm eT HsT) =
        (Matrix.reindex σ σ (LinearMap.toMatrix B B (gaussForm eT HsT))).submatrix σ σ := by
      ext p q
      simp [Matrix.reindex_apply]
    rw [h2, hKmat]
    exact h1.submatrix σ.injective
  have hdet : LinearMap.det (gaussForm eT HsT) = K_U.det := by
    rw [← LinearMap.det_toMatrix B, ← Matrix.det_reindex_self σ, hKmat,
      Matrix.det_reindex_self]
  have hsq : Real.sqrt (LinearMap.det (gaussForm eT HsT))⁻¹ = (pdSqrtInv K_U).det := by
    rw [hdet, ← pdSqrtInv_det_sq hKU, Real.sqrt_sq (pdSqrtInv_det_pos hKU).le]
  obtain ⟨R, hRR, hRs, hdetR⟩ := gaussForm_sqrt_equiv_of_posDef eT HsT hKphys
  have hR (ψ : Config T N) :
      cinner (R ψ) (gaussForm eT HsT (R ψ)) = cinner ψ ψ := by
    have h1 : gaussForm eT HsT (R ψ) = R.symm ψ := by
      have h2 := hRR (R.symm ψ)
      rwa [LinearEquiv.apply_symm_apply] at h2
    rw [h1, hRs, LinearEquiv.apply_symm_apply]
  have hcoord (x : Torus d (L * n)) (i : Fin N) :
      Measurable (fun v : (x : Torus d (L * n)) → perp (e x) =>
        (((v x : EuclideanSpace ℝ (Fin N)) i : ℝ) : ℂ)) := by
    fun_prop
  have hq (Hm : Matrix (G.Ω 1) (G.Ω 1) ℂ) :
      Measurable (fun v : (x : Torus d (L * n)) → perp (e x) =>
        (1 / 2 : ℂ) * pair G (fun p : G.Ω 1 × Fin N =>
          (((fun x => (v x : EuclideanSpace ℝ (Fin N))) (baseSector_side L n ▸
            (p.1 : Torus d (1 * n * L ^ 1))) p.2 : ℝ) : ℂ))
          (liftOp N Hm *ᵥ fun p : G.Ω 1 × Fin N =>
            (((fun x => (v x : EuclideanSpace ℝ (Fin N))) (baseSector_side L n ▸
              (p.1 : Torus d (1 * n * L ^ 1))) p.2 : ℝ) : ℂ))) := by
    refine Measurable.const_mul ?_ _
    unfold pair
    refine Finset.measurable_sum _ fun p _ => (hcoord _ _).mul ?_
    simp only [Matrix.mulVec, dotProduct]
    exact Finset.measurable_sum _ fun p' _ => measurable_const.mul (hcoord _ _)
  have hF : Measurable F := by
    let V := (x : Torus d (L * n)) → perp (e x)
    let W : V → Config (Torus d (L * n)) N := fun v x => (v x : EuclideanSpace ℝ (Fin N))
    let Φ : V → CfgT d N L n := fun v => chartMapPi e he ((Real.sqrt β)⁻¹ • v)
    let Z : V → Config (Torus d (L * n)) N := fun v => chartShift β e (W v)
    let Mass : V → ℝ := fun v => β * (ν - (if regimeB then ν else 0)) / 2 *
      ∑ x : Torus d (L * n), ‖(Φ v x : EuclideanSpace ℝ (Fin N)) - h‖ ^ 2
    let Source : V → ℂ := fun v => ∑ x : Torus d (L * n), ∑ i : Fin N,
      g x i * (((W v x + Z v x) i : ℝ) : ℂ)
    let Cross : V → ℝ := fun v => cinner (W v) (Hα (Z v))
    let Zquad : V → ℝ := fun v => cinner (Z v) (Hα (Z v))
    have hχ : Measurable χ := measurable_baseSectorCubeProduct regimeB ν δ₀ h θ
    have hHα : Measurable Hα :=
      (LinearMap.continuous_of_finiteDimensional Hα).measurable
    have hW : Measurable W := by
      refine measurable_pi_iff.mpr fun x => ?_
      fun_prop
    have hΦ : Measurable Φ := by
      dsimp only [Φ]
      fun_prop
    have hZ : Measurable Z := (measurable_chartShift β e).comp hW
    have hMass : Measurable Mass := by
      dsimp only [Mass]
      fun_prop
    have hSource : Measurable Source := by
      dsimp only [Source]
      fun_prop
    have hCross : Measurable Cross := by
      dsimp only [Cross, cinner]
      fun_prop
    have hZquad : Measurable Zquad := by
      dsimp only [Zquad, cinner]
      fun_prop
    let Qt : (FineBond d L (1 * n) → ℂ) → V → ℂ := fun t v =>
      (1 / 2 : ℂ) * pair G (fun p : G.Ω 1 × Fin N =>
        (((W v) (baseSector_side L n ▸ (p.1 : Torus d (1 * n * L ^ 1))) p.2 : ℝ) : ℂ))
        (liftOp N (baseHamiltonian G aw (if regimeB then ν else 0) α t) *ᵥ
          fun p : G.Ω 1 × Fin N =>
            (((W v) (baseSector_side L n ▸ (p.1 : Torus d (1 * n * L ^ 1))) p.2 : ℝ) : ℂ))
    have hQt (t : FineBond d L (1 * n) → ℂ) : Measurable (Qt t) := hq _
    change Measurable (fun v : V =>
      ((chartJac β (W v) : ℝ) : ℂ) *
        ((χ (Φ v) : ℂ) * ((∏ _y : Torus d n,
            ((β * a₀ * (L : ℝ) ^ d / (L : ℝ) ^ 2) / (2 * Real.pi)) ^
              ((N : ℝ) / 2) : ℝ) : ℂ) * Complex.exp (
          -((β * (energy d N (L * n) (if regimeB then ν else 0) h ec +
            (a₀ * (L : ℝ) ^ d / (2 * (L : ℝ) ^ 2)) *
              ∑ y : Torus d n, ‖θ y - baseQ d N L n ec y‖ ^ 2) : ℝ) : ℂ) +
          (∑ x : Torus d (L * n), ∑ i : Fin N,
            g x i * (((e x) i : ℝ) : ℂ)) +
          (((Real.sqrt β)⁻¹ : ℝ) : ℂ) * Source v -
          (((Cross v + (1 / 2) * Zquad v + Mass v : ℝ) : ℂ) +
            (Qt (fun _ => 1) v - Qt s v)))))
    refine (Complex.measurable_ofReal.comp ((measurable_chartJac β).comp hW)).mul ?_
    refine ((Complex.measurable_ofReal.comp (hχ.comp hΦ)).mul measurable_const).mul ?_
    apply Complex.measurable_exp.comp
    refine Measurable.sub ((measurable_const.add measurable_const).add
      (measurable_const.mul hSource)) ?_
    exact (Complex.measurable_ofReal.comp ((hCross.add (hZquad.const_mul _)).add hMass)).add
      ((hQt _).sub (hQt _))
  refine ⟨HsT, R, hHsT', hRR, hRs, hdetR.trans hsq, fun vJ => ?_⟩
  set mrg : ((x : T) → perp (e x)) → ((x : Torus d (L * n)) → perp (e x)) :=
    fun vI x => if hx : Pt x then vI ⟨x, hx⟩ else vJ ⟨x, hx⟩ with hmrg
  set m0 : (x : Torus d (L * n)) → perp (e x) :=
    fun x => if hx : Pt x then 0 else vJ ⟨x, hx⟩ with hm0
  have hmmrg : Measurable mrg := by
    refine measurable_pi_iff.mpr fun x => ?_
    by_cases hx : Pt x
    · simp only [hmrg, hx, ↓reduceDIte]
      exact measurable_pi_apply (⟨x, hx⟩ : T)
    · simp only [hmrg, hx, ↓reduceDIte]
      exact measurable_const
  have key : ∀ vI : (x : T) → perp (e x),
      Complex.exp (-qS (mrg vI)) * F (mrg vI) =
        ((Real.exp (-(1 / 2) * cinner (fun x : T => (vI x : EuclideanSpace ℝ (Fin N)))
          (HsT (fun x : T => (vI x : EuclideanSpace ℝ (Fin N))))) : ℝ) : ℂ) *
          (Complex.exp (-qS m0) * F (mrg vI)) := by
    intro vI
    set a : Config (Torus d (L * n)) N := fun x =>
      if hx : Pt x then (vI ⟨x, hx⟩ : EuclideanSpace ℝ (Fin N)) else 0 with ha_def
    set b : Config (Torus d (L * n)) N := fun x => (m0 x : EuclideanSpace ℝ (Fin N)) with hb_def
    have hw : (fun x => (mrg vI x : EuclideanSpace ℝ (Fin N))) = a + b := by
      funext x
      by_cases hx : Pt x
      · simp [hmrg, ha_def, hb_def, hm0, hx]
      · simp [hmrg, ha_def, hb_def, hm0, hx]
    have hsplit := cinner_hessian_add_of_cross_zero Pt
      (fun x y => (baseHamiltonian G aw (if regimeB then ν else 0) α s
        (site x) (site y)).re) hcross Hs hHs' a b
      (fun x hx => by simp [ha_def, hx]) (fun x hx => by simp [hb_def, hm0, hx])
    have hext := cinner_hessian_ext_zero Pt
      (fun x y => (baseHamiltonian G aw (if regimeB then ν else 0) α s
        (site x) (site y)).re) Hs hHs' HsT hHsT'
      (fun x : T => (vI x : EuclideanSpace ℝ (Fin N)))
    have e1 : qS (mrg vI) =
        (((1 / 2) * cinner (fun x : T => (vI x : EuclideanSpace ℝ (Fin N)))
          (HsT (fun x : T => (vI x : EuclideanSpace ℝ (Fin N)))) : ℝ) : ℂ) + qS m0 := by
      rw [hqS, hqS m0, hw, hsplit]
      have hb' : cinner b (Hs b) = cinner (fun x => (m0 x : EuclideanSpace ℝ (Fin N)))
          (Hs (fun x => (m0 x : EuclideanSpace ℝ (Fin N)))) := rfl
      rw [hb']
      change (1 / 2 : ℂ) * (((cinner a (Hs a) + _ : ℝ)) : ℂ) = _ + (1 / 2 : ℂ) * _
      rw [← hext]
      push_cast
      ring
    rw [e1, Complex.ofReal_exp]
    have : -((((1 / 2) * cinner (fun x : T => (vI x : EuclideanSpace ℝ (Fin N)))
          (HsT (fun x : T => (vI x : EuclideanSpace ℝ (Fin N)))) : ℝ) : ℂ) + qS m0) =
        (((-(1 / 2) * cinner (fun x : T => (vI x : EuclideanSpace ℝ (Fin N)))
          (HsT (fun x : T => (vI x : EuclideanSpace ℝ (Fin N)))) : ℝ)) : ℂ) + -qS m0 := by
      push_cast
      ring
    rw [this, Complex.exp_add]
    ring
  have hmeasf : Measurable (fun vI : (x : T) → perp (e x) =>
      Complex.exp (-qS m0) * F (mrg vI)) :=
    measurable_const.mul (hF.comp hmmrg)
  have hint := integral_tangent_gaussian_complex eT heT HsT R hR
    (fun vI => Complex.exp (-qS m0) * F (mrg vI)) hmeasf
  calc _ = ∫ vI : (x : T) → perp (e x),
        ((Real.exp (-(1 / 2) * cinner (fun x : T => (vI x : EuclideanSpace ℝ (Fin N)))
          (HsT (fun x : T => (vI x : EuclideanSpace ℝ (Fin N))))) : ℝ) : ℂ) *
          (Complex.exp (-qS m0) * F (mrg vI))
        ∂(Measure.pi fun x : T => (volume : Measure (perp (e x)))) :=
        integral_congr_ae (Filter.Eventually.of_forall key)
    _ = _ := by
      rw [hint, integral_const_mul, hdetR, abs_of_nonneg (Real.sqrt_nonneg _), hsq]

/-- **The retained cut chart integral.** The spin integral over the sites of a union `U` of first
blocks, with the spins on the other sites held fixed, in the hemisphere chart around the
background `e`, rescaled by `√β`: times the chart Jacobian of the fixed spins it is the
rescaled cut integrand `exp (-q_s) F` integrated over the tangent coordinates of the sites of `U`,
with the tangent coordinates of the fixed spins inserted. -/
theorem baseRetainedChartIntegral_eq
    {β : ℝ} (hβ : 0 < β) (a₀ ν δ₀ : ℝ) (ha₀ : 0 < a₀)
    (ϱ : ℝ) (aw : ℕ → ℝ) (ha : aw 1 = a₀)
    (regimeB : Prop) (hδ : 0 < δ₀)
    (h : EuclideanSpace ℝ (Fin N)) (hh : ‖h‖ = 1)
    (H : BgHyp d L 1 ϱ aw (if regimeB then ν else 0))
    (hΛ1 : 4 * d * L * δ₀ ≤ bgC1 d L N)
    (hΛ2 : (d + 2 + 4 * d * bgK1 d L N) * L * δ₀ ≤ 1 / 4)
    (g : Torus d (L * n) → Fin N → ℂ)
    (θ : Torus d n → EuclideanSpace ℝ (Fin N))
    (U : Set (Torus d (1 * n * L ^ 1)))
    (s : FineBond d L (1 * n) → ℂ) :
    let G : GeneratingSet d L (1 * n) 1 ϱ := GeneratingSet.single ϱ
    let α := bgMult G aw (if regimeB then ν else 0) (baseSectorDatum ϱ θ h)
    let e : Config (Torus d (L * n)) N := baseSectorCenter ϱ aw regimeB ν h θ
    let he := baseSectorCenter_unit ϱ aw regimeB ν h hh H θ
    let ec : CfgT d N L n := fun x => ⟨e x, mem_sphere_zero_iff_norm.mpr (he x)⟩
    let Hα : Config (Torus d (L * n)) N →ₗ[ℝ] Config (Torus d (L * n)) N :=
      baseSectorHessian ϱ aw (if regimeB then ν else 0) (fun p => (α p).re)
    let χ := baseSectorCubeProduct regimeB ν δ₀ h θ
    let F : ((x : Torus d (L * n)) → perp (e x)) → ℂ := fun v =>
      let φ := chartMapPi e he ((Real.sqrt β)⁻¹ • v)
      let w : Config (Torus d (L * n)) N := fun x => (v x : EuclideanSpace ℝ (Fin N))
      let z := chartShift β e w
      let W : G.Ω 1 × Fin N → ℂ := fun p =>
        (((w (baseSector_side L n ▸ (p.1 : Torus d (1 * n * L ^ 1)))) p.2 : ℝ) : ℂ)
      let q : (FineBond d L (1 * n) → ℂ) → ℂ := fun t =>
        (1 / 2) * pair G W (liftOp N (baseHamiltonian G aw
          (if regimeB then ν else 0) α t) *ᵥ W)
      let M := β * (ν - (if regimeB then ν else 0)) / 2 *
        ∑ x : Torus d (L * n), ‖(φ x : EuclideanSpace ℝ (Fin N)) - h‖ ^ 2
      ((chartJac β w : ℝ) : ℂ) *
        ((χ φ : ℂ) *
          ((∏ _y : Torus d n,
            ((β * a₀ * (L : ℝ) ^ d / (L : ℝ) ^ 2) / (2 * Real.pi)) ^
              ((N : ℝ) / 2) : ℝ) : ℂ) *
          Complex.exp (
            -((β * (energy d N (L * n) (if regimeB then ν else 0) h ec +
              (a₀ * (L : ℝ) ^ d / (2 * (L : ℝ) ^ 2)) *
                ∑ y : Torus d n, ‖θ y - baseQ d N L n ec y‖ ^ 2) : ℝ) : ℂ) +
            (∑ x : Torus d (L * n), ∑ i : Fin N,
              g x i * (((e x) i : ℝ) : ℂ)) +
            (((Real.sqrt β)⁻¹ : ℝ) : ℂ) *
              (∑ x : Torus d (L * n), ∑ i : Fin N,
                g x i * (((w x + z x) i : ℝ) : ℂ)) -
            (((cinner w (Hα z) + (1 / 2) * cinner z (Hα z) + M : ℝ) : ℂ) +
              (q (fun _ => 1) - q s))))
    let site : Torus d (L * n) → G.Ω 1 := fun x =>
      ⟨(baseSector_side L n).symm ▸ x,
        baseSector_mem_single ϱ ((baseSector_side L n).symm ▸ x)⟩
    let Pt : Torus d (L * n) → Prop := fun x =>
      ((site x : G.Ω 1) : Torus d (1 * n * L ^ 1)) ∈ U
    let qS : ((x : Torus d (L * n)) → perp (e x)) → ℂ := fun v =>
      (1 / 2) * pair G (fun p : G.Ω 1 × Fin N =>
          (((fun x => (v x : EuclideanSpace ℝ (Fin N))) (baseSector_side L n ▸
            (p.1 : Torus d (1 * n * L ^ 1))) p.2 : ℝ) : ℂ))
        (liftOp N (baseHamiltonian G aw (if regimeB then ν else 0) α s) *ᵥ
          fun p : G.Ω 1 × Fin N =>
            (((fun x => (v x : EuclideanSpace ℝ (Fin N))) (baseSector_side L n ▸
              (p.1 : Torus d (1 * n * L ^ 1))) p.2 : ℝ) : ℂ))
    ∀ φ_ret : {x : Torus d (L * n) // ¬ Pt x} →
        Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1,
      (∀ x : {x : Torus d (L * n) // ¬ Pt x},
        0 < inner ℝ (e x) (φ_ret x : EuclideanSpace ℝ (Fin N))) →
      let vJ : (x : {x : Torus d (L * n) // ¬ Pt x}) → perp (e x) := fun x =>
        Real.sqrt β • perpK (e x) (he x) (φ_ret x : EuclideanSpace ℝ (Fin N))
      (((chartJac β (fun x : {x : Torus d (L * n) // ¬ Pt x} =>
          (vJ x : EuclideanSpace ℝ (Fin N))) : ℝ) : ℂ)) *
        ∫ φ_T : {x : Torus d (L * n) // Pt x} →
            Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1,
          (χ (fun x => if hx : Pt x then φ_T ⟨x, hx⟩ else φ_ret ⟨x, hx⟩) : ℂ) *
            ((baseKernel d N L n β a₀ θ
              (fun x => if hx : Pt x then φ_T ⟨x, hx⟩ else φ_ret ⟨x, hx⟩) : ℝ) : ℂ) *
            Complex.exp (-((β * energy d N (L * n) ν h
              (fun x => if hx : Pt x then φ_T ⟨x, hx⟩ else φ_ret ⟨x, hx⟩) : ℝ) : ℂ)
              + ∑ x : Torus d (L * n), ∑ i : Fin N,
                g x i * ((((fun x => if hx : Pt x then φ_T ⟨x, hx⟩ else φ_ret ⟨x, hx⟩ :
                  CfgT d N L n) x : EuclideanSpace ℝ (Fin N)) i : ℝ) : ℂ))
          ∂(Measure.pi fun _ : {x : Torus d (L * n) // Pt x} =>
            (volume : Measure (EuclideanSpace ℝ (Fin N))).toSphere) =
      ((Real.sqrt β)⁻¹ ^ (Fintype.card {x : Torus d (L * n) // Pt x} * (N - 1))) •
        ∫ vI : (x : {x : Torus d (L * n) // Pt x}) → perp (e x),
          Complex.exp (-qS (fun x => if hx : Pt x then vI ⟨x, hx⟩ else vJ ⟨x, hx⟩)) *
            F (fun x => if hx : Pt x then vI ⟨x, hx⟩ else vJ ⟨x, hx⟩)
          ∂(Measure.pi fun x : {x : Torus d (L * n) // Pt x} =>
            (volume : Measure (perp (e x)))) := by
  intro G α e he ec Hα χ F site Pt qS φ_ret hret vJ
  have hχm : Measurable χ := measurable_baseSectorCubeProduct regimeB ν δ₀ h θ
  have hχ1 : ∀ φ, |χ φ| ≤ 1 := by
    intro φ
    change |baseSectorCubeProduct regimeB ν δ₀ h θ φ| ≤ 1
    rw [← baseSectorCutoff_eq_cubeProduct ϱ aw regimeB ν δ₀ hδ h hh H hΛ1 θ φ]
    exact baseSectorCutoff_abs_le_one ϱ regimeB ν δ₀ h θ φ
  have hχs : ∀ φ : CfgT d N L n,
      (∃ x, ¬ 0 < inner ℝ (e x) (φ x : EuclideanSpace ℝ (Fin N))) → χ φ = 0 := by
    intro φ hbad
    change baseSectorCubeProduct regimeB ν δ₀ h θ φ = 0
    rw [← baseSectorCutoff_eq_cubeProduct ϱ aw regimeB ν δ₀ hδ h hh H hΛ1 θ φ]
    exact baseSectorCutoff_hemisphere_support ϱ aw regimeB ν δ₀ hδ h hh H
      hΛ1 hΛ2 θ φ hbad
  let T := {x : Torus d (L * n) // Pt x}
  let eT : Config T N := fun x => e x
  have heT : ∀ x : T, ‖eT x‖ = 1 := fun x => he x
  let mS : (T → Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1) → CfgT d N L n :=
    fun φ_T x => if hx : Pt x then φ_T ⟨x, hx⟩ else φ_ret ⟨x, hx⟩
  have hmS : Measurable mS := by
    refine measurable_pi_iff.mpr fun x => ?_
    by_cases hx : Pt x
    · simp only [mS, hx, ↓reduceDIte]
      exact measurable_pi_apply (⟨x, hx⟩ : T)
    · simp only [mS, hx, ↓reduceDIte]
      exact measurable_const
  let Φ : CfgT d N L n → ℂ := fun φ =>
    (χ φ : ℂ) * ((baseKernel d N L n β a₀ θ φ : ℝ) : ℂ) *
      Complex.exp (-((β * energy d N (L * n) ν h φ : ℝ) : ℂ)
        + ∑ x : Torus d (L * n), ∑ i : Fin N,
          g x i * (((φ x : EuclideanSpace ℝ (Fin N)) i : ℝ) : ℂ))
  obtain ⟨hΦm, C, hΦC⟩ := baseGood_integrand_bound (L := L) (n := n) hβ ha₀ ν h g θ χ hχm hχ1
  have hΦTm : Measurable (fun φ_T => Φ (mS φ_T)) := hΦm.comp hmS
  have hΦTi : Integrable (fun φ_T => Φ (mS φ_T))
      (Measure.pi fun _ : T => (volume : Measure (EuclideanSpace ℝ (Fin N))).toSphere) :=
    Integrable.of_bound (C := C) hΦTm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun φ_T => hΦC (mS φ_T))
  have hΦTs : ∀ φ_T : T → Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1,
      (∃ x : T, ¬ 0 < inner ℝ (eT x) (φ_T x : EuclideanSpace ℝ (Fin N))) → Φ (mS φ_T) = 0 := by
    intro φ_T ⟨x, hx⟩
    have : χ (mS φ_T) = 0 := by
      refine hχs _ ⟨x.1, ?_⟩
      simpa [mS, x.2] using hx
    simp [Φ, this]
  have hchart := integral_sphere_pi_hemisphere_complex eT heT (fun φ_T => Φ (mS φ_T)) hΦTm
    hΦTi hΦTs
  have hexpq : ∀ (q J C E1 E2 : ℂ), E1 = Complex.exp (-q) * E2 →
      Complex.exp (-q) * (J * (C * E2)) = J * (C * E1) := by
    intro q J C E1 E2 hE
    rw [hE]
    ring
  have P : ∀ v : (x : Torus d (L * n)) → perp (e x),
      ((chartJac β (fun x => (v x : EuclideanSpace ℝ (Fin N))) : ℝ) : ℂ) *
        Φ (chartMapPi e he ((Real.sqrt β)⁻¹ • v)) = Complex.exp (-qS v) * F v := by
    intro v
    by_cases hv : ∀ x, ‖v x‖ < Real.sqrt β
    · by_cases hp0 : χ (chartMapPi e he ((Real.sqrt β)⁻¹ • v)) = 0
      · simp only [Φ, F, hp0]
        simp
      · have hint := baseSector_gaussian_integrand_eq hβ a₀ ν δ₀ ϱ aw ha regimeB hδ h hh H
          hΛ1 g θ ((∏ _y : Torus d n,
            ((β * a₀ * (L : ℝ) ^ d / (L : ℝ) ^ 2) / (2 * Real.pi)) ^ ((N : ℝ) / 2) : ℝ) : ℂ) v
        dsimp only at hint
        have hcut := baseSectorHessian_cut_core_one_of_product_ne_zero
          ϱ aw regimeB ν δ₀ hδ h hh H hΛ1 θ (chartMapPi e he ((Real.sqrt β)⁻¹ • v)) hp0
          (fun x => (v x : EuclideanSpace ℝ (Fin N))) (fun x => (v x : EuclideanSpace ℝ (Fin N)))
        dsimp only at hcut
        have hE := basePhysicalExponent_chart e he hβ ν (if regimeB then ν else 0) h g v hv
        simp only [Φ]
        rw [mul_assoc, hE, baseKernel_mul_exp,
          ← mul_assoc (χ (chartMapPi e he ((Real.sqrt β)⁻¹ • v)) : ℂ)]
        refine Eq.trans hint ?_
        dsimp only [F]
        refine (hexpq _ _ _ _ _ ?_).symm
        rw [← Complex.exp_add]
        congr 1
        have hq1 : (1 / 2 : ℂ) * pair G (fun p : G.Ω 1 × Fin N =>
            (((fun x => (v x : EuclideanSpace ℝ (Fin N))) (baseSector_side L n ▸
              (p.1 : Torus d (1 * n * L ^ 1))) p.2 : ℝ) : ℂ))
            (liftOp N (baseHamiltonian G aw (if regimeB then ν else 0) α (fun _ => 1)) *ᵥ
              fun p : G.Ω 1 × Fin N =>
                (((fun x => (v x : EuclideanSpace ℝ (Fin N))) (baseSector_side L n ▸
                  (p.1 : Torus d (1 * n * L ^ 1))) p.2 : ℝ) : ℂ)) =
            (1 / 2 : ℂ) * ((cinner (fun x => (v x : EuclideanSpace ℝ (Fin N)))
              (Hα (fun x => (v x : EuclideanSpace ℝ (Fin N)))) : ℝ) : ℂ) := by
          rw [hcut]
        simp only [G, α, e, ec, Hα, qS] at hq1 ⊢
        push_cast at hq1 ⊢
        linear_combination hq1
    · obtain ⟨x, hx⟩ := not_forall.mp hv
      have hj : chartJac β (fun x => (v x : EuclideanSpace ℝ (Fin N))) = 0 :=
        chartJac_eq_zero (x₀ := x) hx
      simp [F, hj]
  let mrg : ((x : T) → perp (e x)) → ((x : Torus d (L * n)) → perp (e x)) :=
    fun vI x => if hx : Pt x then vI ⟨x, hx⟩ else vJ ⟨x, hx⟩
  have hscale := integral_pi_perp_inv_sqrt_smul eT heT hβ
    (fun ξ => (∏ x, ((chartWeight (eT x) (ξ x) : ℝ) : ℂ)) *
      Φ (mS (chartMapPi eT heT ξ)))
  change ((chartJac β (fun x : {x : Torus d (L * n) // ¬ Pt x} =>
      (vJ x : EuclideanSpace ℝ (Fin N))) : ℝ) : ℂ) *
    (∫ φ_T, Φ (mS φ_T) ∂(Measure.pi fun _ : T =>
      (volume : Measure (EuclideanSpace ℝ (Fin N))).toSphere)) =
      ((Real.sqrt β)⁻¹ ^ (Fintype.card T * (N - 1))) •
        ∫ vI : (x : T) → perp (e x), Complex.exp (-qS (mrg vI)) * F (mrg vI)
          ∂(Measure.pi fun x : T => (volume : Measure (perp (e x))))
  rw [hchart, hscale, mul_smul_comm, ← integral_const_mul]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun vI => ?_)
  have hw1 : ∏ x : T, ((chartWeight (eT x) (((Real.sqrt β)⁻¹ • vI) x) : ℝ) : ℂ) =
      ((chartJac β (fun x : T => (vI x : EuclideanSpace ℝ (Fin N))) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_prod, chartWeight_prod_inv_sqrt_eq_chartJac eT hβ vI]
  have hjac : chartJac β (fun x => ((mrg vI x : perp (e x)) : EuclideanSpace ℝ (Fin N))) =
      chartJac β (fun x : T => (vI x : EuclideanSpace ℝ (Fin N))) *
        chartJac β (fun x : {x : Torus d (L * n) // ¬ Pt x} =>
          (vJ x : EuclideanSpace ℝ (Fin N))) := by
    unfold chartJac
    rw [← Fintype.prod_subtype_mul_prod_subtype Pt]
    congr 1
    · refine Finset.prod_congr rfl fun x _ => ?_
      simp [mrg, x.2]
    · refine Finset.prod_congr rfl fun x _ => ?_
      simp [mrg, x.2]
  have hmap : mS (chartMapPi eT heT ((Real.sqrt β)⁻¹ • vI)) =
      chartMapPi e he ((Real.sqrt β)⁻¹ • mrg vI) := by
    funext x
    by_cases hx : Pt x
    · simp [mS, chartMapPi, mrg, hx]
      rfl
    · have hs : (Real.sqrt β)⁻¹ • vJ ⟨x, hx⟩ =
          perpK (e x) (he x) (φ_ret ⟨x, hx⟩ : EuclideanSpace ℝ (Fin N)) := by
        simp only [vJ]
        rw [smul_smul, inv_mul_cancel₀ (Real.sqrt_pos.2 hβ).ne', one_smul]
      have hn : ‖(φ_ret ⟨x, hx⟩ : EuclideanSpace ℝ (Fin N))‖ = 1 :=
        mem_sphere_zero_iff_norm.mp (φ_ret ⟨x, hx⟩).2
      have hlt := norm_perpK_lt (e x) (he x) hn (hret ⟨x, hx⟩)
      simp only [mS, chartMapPi, mrg, hx, ↓reduceDIte, Pi.smul_apply]
      rw [hs]
      apply Subtype.ext
      rw [coe_hemiPt_of_lt (e x) (he x) hlt]
      exact (hemiE_perpK (e x) (he x) hn (hret ⟨x, hx⟩)).symm
  show _ * ((∏ x : T, ((chartWeight (eT x) (((Real.sqrt β)⁻¹ • vI) x) : ℝ) : ℂ)) *
      Φ (mS (chartMapPi eT heT ((Real.sqrt β)⁻¹ • vI)))) =
    Complex.exp (-qS (mrg vI)) * F (mrg vI)
  rw [hw1, hmap, ← P (mrg vI), hjac]
  push_cast
  ring

/-- **The cut chart integral over a first-block component with the other spins fixed.**
For the spins on the sites of `U` integrated against the a priori measure, with the spins on the
other sites fixed in the open hemispheres around the background `e`, the integral (times the chart
Jacobian of the fixed spins) is the Gaussian prefactor `(2π)^((N-1)|T|/2) det (pdSqrtInv K_U)`
times the standard Gaussian integral of the transported remainder `F`, with the fixed tangent
coordinates inserted and the factor `exp (-q_s)` of the fixed spins. -/
theorem baseRetainedChartIntegral_gaussian
    {β : ℝ} (hβ : 0 < β) (a₀ ν δ₀ : ℝ) (ha₀ : 0 < a₀)
    (ϱ : ℝ) (aw : ℕ → ℝ) (ha : aw 1 = a₀)
    (regimeB : Prop) (hδ : 0 < δ₀)
    (h : EuclideanSpace ℝ (Fin N)) (hh : ‖h‖ = 1)
    (H : BgHyp d L 1 ϱ aw (if regimeB then ν else 0))
    (hΛ1 : 4 * d * L * δ₀ ≤ bgC1 d L N)
    (hΛ2 : (d + 2 + 4 * d * bgK1 d L N) * L * δ₀ ≤ 1 / 4)
    (g : Torus d (L * n) → Fin N → ℂ)
    (θ : Torus d n → EuclideanSpace ℝ (Fin N))
    (φ₀ : CfgT d N L n)
    (hp : baseSectorCubeProduct regimeB ν δ₀ h θ φ₀ ≠ 0)
    (U : Set (Torus d (1 * n * L ^ 1)))
    (hU : IsFirstBlockUnion (GeneratingSet.single (d := d) (L := L)
      (N₀ := 1 * n) (k := 1) ϱ) U)
    {η : ℝ} (hη0 : 0 ≤ η)
    (hη : η ≤ baseCoercivity L / (8 * d))
    (s : FineBond d L (1 * n) → ℂ)
    (hs : s ∈ baseParamNbhd (GeneratingSet.single (d := d) (L := L)
      (N₀ := 1 * n) (k := 1) ϱ) η)
    (hz : CrossZero (GeneratingSet.single (d := d) (L := L)
      (N₀ := 1 * n) (k := 1) ϱ) U s)
    (hsr : ∀ b ∈ baseCutBonds (GeneratingSet.single (d := d) (L := L)
      (N₀ := 1 * n) (k := 1) ϱ), (s b).im = 0) :
    let G : GeneratingSet d L (1 * n) 1 ϱ := GeneratingSet.single ϱ
    let α := bgMult G aw (if regimeB then ν else 0) (baseSectorDatum ϱ θ h)
    let e : Config (Torus d (L * n)) N := baseSectorCenter ϱ aw regimeB ν h θ
    let he := baseSectorCenter_unit ϱ aw regimeB ν h hh H θ
    let ec : CfgT d N L n := fun x => ⟨e x, mem_sphere_zero_iff_norm.mpr (he x)⟩
    let Hα : Config (Torus d (L * n)) N →ₗ[ℝ] Config (Torus d (L * n)) N :=
      baseSectorHessian ϱ aw (if regimeB then ν else 0) (fun p => (α p).re)
    let χ := baseSectorCubeProduct regimeB ν δ₀ h θ
    let eG : G.Ω 1 → Fin N → ℝ := fun z i =>
      (baseSectorCenter ϱ aw regimeB ν h θ
        (baseSector_side L n ▸ (z : Torus d (1 * n * L ^ 1))) i : ℝ)
    let A := baseOp N (fun z i => (eG z i : ℂ))
      (baseHamiltonian G aw (if regimeB then ν else 0) α s)
    let P : G.Ω 1 × Fin N → Prop := fun p =>
      (p.1 : Torus d (1 * n * L ^ 1)) ∈ U
    let I := {p : G.Ω 1 × Fin N // P p}
    let A_U : Matrix I I ℂ := A.submatrix Subtype.val Subtype.val
    let K_U := A_U.map Complex.re
    let F : ((x : Torus d (L * n)) → perp (e x)) → ℂ := fun v =>
      let φ := chartMapPi e he ((Real.sqrt β)⁻¹ • v)
      let w : Config (Torus d (L * n)) N := fun x => (v x : EuclideanSpace ℝ (Fin N))
      let z := chartShift β e w
      let W : G.Ω 1 × Fin N → ℂ := fun p =>
        (((w (baseSector_side L n ▸ (p.1 : Torus d (1 * n * L ^ 1)))) p.2 : ℝ) : ℂ)
      let q : (FineBond d L (1 * n) → ℂ) → ℂ := fun t =>
        (1 / 2) * pair G W (liftOp N (baseHamiltonian G aw
          (if regimeB then ν else 0) α t) *ᵥ W)
      let M := β * (ν - (if regimeB then ν else 0)) / 2 *
        ∑ x : Torus d (L * n), ‖(φ x : EuclideanSpace ℝ (Fin N)) - h‖ ^ 2
      ((chartJac β w : ℝ) : ℂ) *
        ((χ φ : ℂ) *
          ((∏ _y : Torus d n,
            ((β * a₀ * (L : ℝ) ^ d / (L : ℝ) ^ 2) / (2 * Real.pi)) ^
              ((N : ℝ) / 2) : ℝ) : ℂ) *
          Complex.exp (
            -((β * (energy d N (L * n) (if regimeB then ν else 0) h ec +
              (a₀ * (L : ℝ) ^ d / (2 * (L : ℝ) ^ 2)) *
                ∑ y : Torus d n, ‖θ y - baseQ d N L n ec y‖ ^ 2) : ℝ) : ℂ) +
            (∑ x : Torus d (L * n), ∑ i : Fin N,
              g x i * (((e x) i : ℝ) : ℂ)) +
            (((Real.sqrt β)⁻¹ : ℝ) : ℂ) *
              (∑ x : Torus d (L * n), ∑ i : Fin N,
                g x i * (((w x + z x) i : ℝ) : ℂ)) -
            (((cinner w (Hα z) + (1 / 2) * cinner z (Hα z) + M : ℝ) : ℂ) +
              (q (fun _ => 1) - q s))))
    let site : Torus d (L * n) → G.Ω 1 := fun x =>
      ⟨(baseSector_side L n).symm ▸ x,
        baseSector_mem_single ϱ ((baseSector_side L n).symm ▸ x)⟩
    let Pt : Torus d (L * n) → Prop := fun x =>
      ((site x : G.Ω 1) : Torus d (1 * n * L ^ 1)) ∈ U
    let qS : ((x : Torus d (L * n)) → perp (e x)) → ℂ := fun v =>
      (1 / 2) * pair G (fun p : G.Ω 1 × Fin N =>
          (((fun x => (v x : EuclideanSpace ℝ (Fin N))) (baseSector_side L n ▸
            (p.1 : Torus d (1 * n * L ^ 1))) p.2 : ℝ) : ℂ))
        (liftOp N (baseHamiltonian G aw (if regimeB then ν else 0) α s) *ᵥ
          fun p : G.Ω 1 × Fin N =>
            (((fun x => (v x : EuclideanSpace ℝ (Fin N))) (baseSector_side L n ▸
              (p.1 : Torus d (1 * n * L ^ 1))) p.2 : ℝ) : ℂ))
    ∃ (HsT : Config {x // Pt x} N →ₗ[ℝ] Config {x // Pt x} N)
      (R : Config {x // Pt x} N ≃ₗ[ℝ] Config {x // Pt x} N),
      (∀ u x i, (HsT u x i : ℝ) = ∑ y : {x // Pt x},
        (baseHamiltonian G aw (if regimeB then ν else 0) α s
          (site x) (site y)).re * (u y i : ℝ)) ∧
      (∀ w, gaussForm (fun x : {x // Pt x} => e x) HsT (R (R w)) = w) ∧
      (∀ u v, cinner (R u) v = cinner u (R v)) ∧
      LinearMap.det (R : Config {x // Pt x} N →ₗ[ℝ] Config {x // Pt x} N) =
        (pdSqrtInv K_U).det ∧
      ∀ φ_ret : {x : Torus d (L * n) // ¬ Pt x} →
          Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1,
        (∀ x : {x : Torus d (L * n) // ¬ Pt x},
          0 < inner ℝ (e x) (φ_ret x : EuclideanSpace ℝ (Fin N))) →
        let vJ : (x : {x : Torus d (L * n) // ¬ Pt x}) → perp (e x) := fun x =>
          Real.sqrt β • perpK (e x) (he x) (φ_ret x : EuclideanSpace ℝ (Fin N))
        (((chartJac β (fun x : {x : Torus d (L * n) // ¬ Pt x} =>
            (vJ x : EuclideanSpace ℝ (Fin N))) : ℝ) : ℂ)) *
          ∫ φ_T : {x : Torus d (L * n) // Pt x} →
              Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1,
            (χ (fun x => if hx : Pt x then φ_T ⟨x, hx⟩ else φ_ret ⟨x, hx⟩) : ℂ) *
              ((baseKernel d N L n β a₀ θ
                (fun x => if hx : Pt x then φ_T ⟨x, hx⟩ else φ_ret ⟨x, hx⟩) : ℝ) : ℂ) *
              Complex.exp (-((β * energy d N (L * n) ν h
                (fun x => if hx : Pt x then φ_T ⟨x, hx⟩ else φ_ret ⟨x, hx⟩) : ℝ) : ℂ)
                + ∑ x : Torus d (L * n), ∑ i : Fin N,
                  g x i * ((((fun x => if hx : Pt x then φ_T ⟨x, hx⟩ else φ_ret ⟨x, hx⟩ :
                    CfgT d N L n) x : EuclideanSpace ℝ (Fin N)) i : ℝ) : ℂ))
            ∂(Measure.pi fun _ : {x : Torus d (L * n) // Pt x} =>
              (volume : Measure (EuclideanSpace ℝ (Fin N))).toSphere) =
        ((Real.sqrt β)⁻¹ ^ (Fintype.card {x : Torus d (L * n) // Pt x} * (N - 1))) •
          ((((2 * Real.pi) ^ (((N : ℝ) - 1) * Fintype.card {x : Torus d (L * n) // Pt x} / 2) *
            (pdSqrtInv K_U).det : ℝ) : ℂ) *
            (Complex.exp (-qS (fun x => if hx : Pt x then 0 else vJ ⟨x, hx⟩)) *
              ∫ ψ, F (fun x => if hx : Pt x then
                  tangentProj (fun x : {x // Pt x} => e x) (fun x => he x) (R ψ) ⟨x, hx⟩
                else vJ ⟨x, hx⟩)
                ∂(stdGaussian {x // Pt x} N))) := by
  have h1 := baseChartIntegral_retained (β := β) a₀ ν δ₀ ϱ aw regimeB hδ h hh H hΛ1 g θ φ₀ hp U hU
    hη0 hη s hs hz hsr
  have h2 := baseRetainedChartIntegral_eq hβ a₀ ν δ₀ ha₀ ϱ aw ha regimeB hδ h hh H hΛ1 hΛ2 g θ U s
  intro G α e he ec Hα χ eG A P I A_U K_U F site Pt qS
  obtain ⟨HsT, R, hHsT, hRR, hRs, hdet, hint⟩ := h1
  refine ⟨HsT, R, hHsT, hRR, hRs, hdet, fun φ_ret hret => ?_⟩
  intro vJ
  have h3 := h2 φ_ret hret
  dsimp only at h3 ⊢
  rw [h3, hint vJ]

end Physical

end Balaban.LargeField
