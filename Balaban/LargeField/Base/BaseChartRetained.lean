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

end Physical

end Balaban.LargeField
