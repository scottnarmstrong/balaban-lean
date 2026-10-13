module

public import Balaban.LargeField.Base.BaseChartActionBridge
public import Balaban.LargeField.Base.BaseResolvent

/-!
# The physical first-step Hessian

P4 (2.44) identifies the hard-spin chord operator as the real first-step Dirichlet
operator with the real Lagrange multiplier. The lemmas below transport that operator
from the single-scale background carrier to the physical torus.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Background Balaban.Multiscale Matrix Classical
open Balaban.LargeField.Base

variable {d N L n : ℕ} [NeZero L] [NeZero n]

/-- The first-step background multiplier is real on the real data domain. -/
theorem baseSector_bgMult_real_of_domain (ϱ : ℝ) (aw : ℕ → ℝ)
    (regimeB : Prop) (ν : ℝ) (h : EuclideanSpace ℝ (Fin N))
    (H : BgHyp d L 1 ϱ aw (if regimeB then ν else 0))
    (θ : Torus d n → EuclideanSpace ℝ (Fin N))
    (hU : InUnionDomainR (GeneratingSet.single (d := d) (L := L)
      (N₀ := 1 * n) (k := 1) ϱ) (bgC1 d L N) (if regimeB then ν else 0)
      (baseSectorDatum ϱ θ h))
    (x : (GeneratingSet.single (d := d) (L := L)
      (N₀ := 1 * n) (k := 1) ϱ).Ω 1) :
    (bgMult (GeneratingSet.single (d := d) (L := L)
      (N₀ := 1 * n) (k := 1) ϱ) aw (if regimeB then ν else 0)
      (baseSectorDatum ϱ θ h) x).im = 0 := by
  let G : GeneratingSet d L (1 * n) 1 ϱ := GeneratingSet.single ϱ
  let D : BgData G N := baseSectorDatum ϱ θ h
  obtain ⟨δ, hδ0, hδc, hDδ⟩ := hU
  obtain ⟨φ, α, hs, _, hu, _, hmin, huniq⟩ := bg_real (G := G) H hδ0 hδc hDδ
  have hreal : D.IsReal := isReal_of_inDomainR hDδ
  have hc := (hu _ _ (isSmallSolution_conj D hreal hs)).2
  have hf : bgField G aw (if regimeB then ν else 0) D = φ := bgField_eq hmin huniq
  have hm : bgMult G aw (if regimeB then ν else 0) D = α := by
    funext y
    unfold bgMult
    rw [hf]
    exact mult_formula hs.1 y
  rw [hm]
  rw [← Complex.conj_eq_iff_im]
  exact congrFun hc x

/-- On nonzero P5 all-good support the first-step background multiplier is real. -/
theorem baseSector_bgMult_real_of_product_ne_zero (ϱ : ℝ) (aw : ℕ → ℝ)
    (regimeB : Prop) (ν δ₀ : ℝ) (hδ : 0 < δ₀)
    (h : EuclideanSpace ℝ (Fin N)) (hh : ‖h‖ = 1)
    (H : BgHyp d L 1 ϱ aw (if regimeB then ν else 0))
    (hΛ1 : 4 * d * L * δ₀ ≤ bgC1 d L N)
    (θ : Torus d n → EuclideanSpace ℝ (Fin N)) (φ : CfgT d N L n)
    (hp : baseSectorCubeProduct regimeB ν δ₀ h θ φ ≠ 0)
    (x : (GeneratingSet.single (d := d) (L := L)
      (N₀ := 1 * n) (k := 1) ϱ).Ω 1) :
    (bgMult (GeneratingSet.single (d := d) (L := L)
      (N₀ := 1 * n) (k := 1) ϱ) aw (if regimeB then ν else 0)
      (baseSectorDatum ϱ θ h) x).im = 0 := by
  exact baseSector_bgMult_real_of_domain ϱ aw regimeB ν h H θ
    (baseSectorDatum_domain_of_product_ne_zero ϱ aw regimeB ν δ₀ hδ h hh H
      hΛ1 θ φ hp) x

/-- The P5 all-good support bounds the first-step multiplier by the threshold
used in the landed base resolvent. -/
theorem baseSector_bgMult_norm_le_of_product_ne_zero (ϱ : ℝ) (aw : ℕ → ℝ)
    (regimeB : Prop) (ν δ₀ : ℝ) (hδ : 0 < δ₀)
    (h : EuclideanSpace ℝ (Fin N)) (hh : ‖h‖ = 1)
    (H : BgHyp d L 1 ϱ aw (if regimeB then ν else 0))
    (hΛ1 : 4 * d * L * δ₀ ≤ bgC1 d L N)
    (θ : Torus d n → EuclideanSpace ℝ (Fin N)) (φ : CfgT d N L n)
    (hp : baseSectorCubeProduct regimeB ν δ₀ h θ φ ≠ 0)
    (x : (GeneratingSet.single (d := d) (L := L)
      (N₀ := 1 * n) (k := 1) ϱ).Ω 1) :
    ‖bgMult (GeneratingSet.single (d := d) (L := L)
      (N₀ := 1 * n) (k := 1) ϱ) aw (if regimeB then ν else 0)
      (baseSectorDatum ϱ θ h) x‖ ≤ 1 / (8 * (L : ℝ) ^ 2) := by
  let G : GeneratingSet d L (1 * n) 1 ϱ := GeneratingSet.single ϱ
  let D : BgData G N := baseSectorDatum ϱ θ h
  obtain ⟨δ, hδ0, hδc, hDδ⟩ :=
    baseSectorDatum_domain_of_product_ne_zero ϱ aw regimeB ν δ₀ hδ h hh H
      hΛ1 θ φ hp
  have hb := ((theorem71 (G := G) H ⟨δ, hδ0, hδc, hDδ⟩).2.2.2.2)
    δ hδ0 hδc hDδ
  have hd0 : 0 < d := by have := H.hd; omega
  have hc := (bgC1_facts d L N hd0 hδc).2.2.2
  have hsmall : bgK1 d L N * δ ≤ 1 / 32 := by
    have := bgC0_le d L N
    linarith
  have hs : (L : ℝ) ^ 2 * ‖bgMult G aw (if regimeB then ν else 0) D x‖ ≤
      1 / 32 := by
    have hs' := hb.alpha x
    rw [spacing_single (hk := le_rfl), pow_one] at hs'
    exact hs'.trans hsmall
  have hL : 0 < (L : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne L))
  have hsq : 0 < (L : ℝ) ^ 2 := pow_pos hL _
  calc
    ‖bgMult G aw (if regimeB then ν else 0) D x‖ ≤
        (1 / 8 : ℝ) / (L : ℝ) ^ 2 :=
      (le_div_iff₀ hsq).2 (by nlinarith [hs])
    _ = 1 / (8 * (L : ℝ) ^ 2) := by ring

/-- Real multiplier values make every entry of the first-step Dirichlet operator real. -/
theorem baseSector_dirichlet_coeff_real (ϱ : ℝ) (aw : ℕ → ℝ) (μ : ℝ)
    (α : (GeneratingSet.single (d := d) (L := L)
      (N₀ := 1 * n) (k := 1) ϱ).Ω 1 → ℂ)
    (hα : ∀ x, (α x).im = 0)
    (x y : (GeneratingSet.single (d := d) (L := L)
      (N₀ := 1 * n) (k := 1) ϱ).Ω 1) :
    (dirichletOperator (GeneratingSet.single (d := d) (L := L)
      (N₀ := 1 * n) (k := 1) ϱ) aw μ α x y).im = 0 := by
  let G : GeneratingSet d L (1 * n) 1 ϱ := GeneratingSet.single ϱ
  change (dirichletOperator G aw μ α x y).im = 0
  simp only [dirichletOperator, Matrix.add_apply, Green.restrictOp,
    Matrix.submatrix_apply, Matrix.map_apply, Matrix.diagonal_apply]
  split_ifs <;> simp [hα]

/-- Coefficients of the physical-support Hessian are real. -/
theorem baseSector_dirichlet_coeff_real_of_product_ne_zero (ϱ : ℝ)
    (aw : ℕ → ℝ) (regimeB : Prop) (ν δ₀ : ℝ) (hδ : 0 < δ₀)
    (h : EuclideanSpace ℝ (Fin N)) (hh : ‖h‖ = 1)
    (H : BgHyp d L 1 ϱ aw (if regimeB then ν else 0))
    (hΛ1 : 4 * d * L * δ₀ ≤ bgC1 d L N)
    (θ : Torus d n → EuclideanSpace ℝ (Fin N)) (φ : CfgT d N L n)
    (hp : baseSectorCubeProduct regimeB ν δ₀ h θ φ ≠ 0)
    (x y : (GeneratingSet.single (d := d) (L := L)
      (N₀ := 1 * n) (k := 1) ϱ).Ω 1) :
    (dirichletOperator (GeneratingSet.single (d := d) (L := L)
      (N₀ := 1 * n) (k := 1) ϱ) aw (if regimeB then ν else 0)
      (bgMult (GeneratingSet.single (d := d) (L := L)
        (N₀ := 1 * n) (k := 1) ϱ) aw (if regimeB then ν else 0)
        (baseSectorDatum ϱ θ h)) x y).im = 0 := by
  exact baseSector_dirichlet_coeff_real ϱ aw (if regimeB then ν else 0) _
    (baseSector_bgMult_real_of_product_ne_zero ϱ aw regimeB ν δ₀ hδ h hh H
      hΛ1 θ φ hp) x y

/-- The real physical first-step Hessian of P4 (2.44),
`-Δ + aw 1 * L⁻² Q*Q + μ + α`, acting componentwise on the physical torus.
The matrix `fullMatrix` already contains the first-block averaging form. -/
noncomputable def baseSectorHessian (ϱ : ℝ) (aw : ℕ → ℝ) (μ : ℝ)
    (α : (GeneratingSet.single (d := d) (L := L)
      (N₀ := 1 * n) (k := 1) ϱ).Ω 1 → ℝ) :
    Config (Torus d (L * n)) N →ₗ[ℝ] Config (Torus d (L * n)) N := by
  let G : GeneratingSet d L (1 * n) 1 ϱ := GeneratingSet.single ϱ
  let site : Torus d (L * n) → G.Ω 1 := fun x =>
    ⟨(baseSector_side L n).symm ▸ x,
      baseSector_mem_single ϱ ((baseSector_side L n).symm ▸ x)⟩
  let A : Matrix (Torus d (L * n)) (Torus d (L * n)) ℝ := fun x y =>
    fullMatrix G aw μ (site x : Torus d (1 * n * L ^ 1))
      (site y : Torus d (1 * n * L ^ 1)) +
      if x = y then α (site x) else 0
  exact
    { toFun := fun u x => WithLp.toLp 2 (fun i : Fin N =>
        ∑ y : Torus d (L * n), A x y * ((u y) i : ℝ))
      map_add' := by
        intro u v
        funext x
        ext i
        change (∑ y, A x y * (((u + v) y i) : ℝ)) =
          (∑ y, A x y * (u y i : ℝ)) + (∑ y, A x y * (v y i : ℝ))
        simp only [Pi.add_apply, PiLp.add_apply, mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro c u
        funext x
        ext i
        change (∑ y, A x y * (((c • u) y i) : ℝ)) =
          c * ∑ y, A x y * (u y i : ℝ)
        simp only [Pi.smul_apply, PiLp.smul_apply,
          smul_eq_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y hy
        ring }

/-- The coefficients of the physical Hessian are the transported real Dirichlet entries. -/
theorem baseSectorHessian_apply (ϱ : ℝ) (aw : ℕ → ℝ) (μ : ℝ)
    (α : (GeneratingSet.single (d := d) (L := L)
      (N₀ := 1 * n) (k := 1) ϱ).Ω 1 → ℝ)
    (u : Config (Torus d (L * n)) N) (x : Torus d (L * n)) (i : Fin N) :
    (baseSectorHessian ϱ aw μ α u x i : ℝ) =
      ∑ y : Torus d (L * n),
        (fullMatrix (GeneratingSet.single (d := d) (L := L)
          (N₀ := 1 * n) (k := 1) ϱ) aw μ
          ((baseSector_side L n).symm ▸ x) ((baseSector_side L n).symm ▸ y) +
          if x = y then α ⟨(baseSector_side L n).symm ▸ x,
            baseSector_mem_single ϱ ((baseSector_side L n).symm ▸ x)⟩ else 0) *
          (u y i : ℝ) := by
  rfl

private theorem baseSector_cast_cancel {a b : ℕ} (e : a = b)
    (x : Torus d b) : e ▸ (e.symm ▸ x) = x := by
  cases e
  rfl

private theorem baseSector_cast_cancel_rev {a b : ℕ} (e : a = b)
    (x : Torus d a) : e.symm ▸ (e ▸ x) = x := by
  cases e
  rfl

private theorem baseSector_sum_native_sites {R : Type*} [AddCommMonoid R]
    (ϱ : ℝ) (f : Torus d (L * n) → R) :
    (∑ x : (GeneratingSet.single (d := d) (L := L)
      (N₀ := 1 * n) (k := 1) ϱ).Ω 1,
      f (baseSector_side L n ▸ (x : Torus d (1 * n * L ^ 1)))) =
      ∑ x : Torus d (L * n), f x := by
  let G : GeneratingSet d L (1 * n) 1 ϱ := GeneratingSet.single ϱ
  let e : G.Ω 1 ≃ Torus d (L * n) :=
    { toFun := fun p => baseSector_side L n ▸ (p : Torus d (1 * n * L ^ 1))
      invFun := fun x => ⟨(baseSector_side L n).symm ▸ x,
        baseSector_mem_single ϱ ((baseSector_side L n).symm ▸ x)⟩
      left_inv := by
        intro p
        apply Subtype.ext
        exact baseSector_cast_cancel_rev (baseSector_side L n) p.1
      right_inv := baseSector_cast_cancel (baseSector_side L n) }
  exact Fintype.sum_equiv e _ _ (fun _ => rfl)

private theorem baseSector_nativeSite_eq_iff (ϱ : ℝ)
    (x y : Torus d (L * n)) :
    (⟨(baseSector_side L n).symm ▸ x,
      baseSector_mem_single ϱ ((baseSector_side L n).symm ▸ x)⟩ :
        (GeneratingSet.single (d := d) (L := L)
          (N₀ := 1 * n) (k := 1) ϱ).Ω 1) =
      ⟨(baseSector_side L n).symm ▸ y,
      baseSector_mem_single ϱ ((baseSector_side L n).symm ▸ y)⟩ ↔ x = y := by
  constructor
  · intro hsite
    have hv := congrArg Subtype.val hsite
    have hc := congrArg (fun z : Torus d (1 * n * L ^ 1) =>
      baseSector_side L n ▸ z) hv
    simpa only [baseSector_cast_cancel] using hc
  · intro hxy
    subst y
    rfl

/-- The real coefficients of the physical Hessian are exactly the complex Dirichlet
coefficients with a real multiplier, transported from `G.Ω 1`. -/
theorem baseSectorHessian_coeff_eq (ϱ : ℝ) (aw : ℕ → ℝ) (μ : ℝ)
    (α : (GeneratingSet.single (d := d) (L := L)
      (N₀ := 1 * n) (k := 1) ϱ).Ω 1 → ℝ)
    (x y : Torus d (L * n)) :
    let G : GeneratingSet d L (1 * n) 1 ϱ := GeneratingSet.single ϱ
    let site : Torus d (L * n) → G.Ω 1 := fun z =>
      ⟨(baseSector_side L n).symm ▸ z,
        baseSector_mem_single ϱ ((baseSector_side L n).symm ▸ z)⟩
    dirichletOperator G aw μ (fun p => (α p : ℂ)) (site x) (site y) =
      ((fullMatrix G aw μ (site x : Torus d (1 * n * L ^ 1))
        (site y : Torus d (1 * n * L ^ 1)) +
        if x = y then α (site x) else 0 : ℝ) : ℂ) := by
  dsimp only
  simp only [dirichletOperator, Matrix.add_apply, Green.restrictOp,
    Matrix.submatrix_apply, Matrix.map_apply, Matrix.diagonal_apply]
  by_cases hxy : x = y
  · subst y
    simp
  · have hsne : ¬ (⟨(baseSector_side L n).symm ▸ x,
        baseSector_mem_single ϱ ((baseSector_side L n).symm ▸ x)⟩ :
        (GeneratingSet.single (d := d) (L := L)
          (N₀ := 1 * n) (k := 1) ϱ).Ω 1) =
        ⟨(baseSector_side L n).symm ▸ y,
          baseSector_mem_single ϱ ((baseSector_side L n).symm ▸ y)⟩ := by
          intro hs
          exact hxy ((baseSector_nativeSite_eq_iff ϱ x y).mp hs)
    simp [hxy, hsne]

private theorem baseSectorHessian_coeff_symm (ϱ : ℝ) (aw : ℕ → ℝ) (μ : ℝ)
    (α : (GeneratingSet.single (d := d) (L := L)
      (N₀ := 1 * n) (k := 1) ϱ).Ω 1 → ℝ)
    (x y : Torus d (L * n)) :
    let G : GeneratingSet d L (1 * n) 1 ϱ := GeneratingSet.single ϱ
    let site : Torus d (L * n) → G.Ω 1 := fun z =>
      ⟨(baseSector_side L n).symm ▸ z,
        baseSector_mem_single ϱ ((baseSector_side L n).symm ▸ z)⟩
    (fullMatrix G aw μ (site x : Torus d (1 * n * L ^ 1))
      (site y : Torus d (1 * n * L ^ 1)) +
      if x = y then α (site x) else 0) =
    (fullMatrix G aw μ (site y : Torus d (1 * n * L ^ 1))
      (site x : Torus d (1 * n * L ^ 1)) +
      if y = x then α (site y) else 0) := by
  dsimp only
  let G : GeneratingSet d L (1 * n) 1 ϱ := GeneratingSet.single ϱ
  have hfull : (fullMatrix G aw μ)
      ((baseSector_side L n).symm ▸ x) ((baseSector_side L n).symm ▸ y) =
      (fullMatrix G aw μ)
      ((baseSector_side L n).symm ▸ y) ((baseSector_side L n).symm ▸ x) := by
    have ht := congrFun (congrFun (fullMatrix_transpose G aw μ)
      ((baseSector_side L n).symm ▸ y)) ((baseSector_side L n).symm ▸ x)
    simpa only [Matrix.transpose_apply] using ht
  by_cases hxy : x = y
  · subst y
    rfl
  · simpa [hxy, Ne.symm hxy] using hfull

private theorem cinner_components {ι : Type*} [Fintype ι]
    (u v : Config ι N) :
    cinner u v = ∑ x : ι, ∑ i : Fin N, (u x i : ℝ) * (v x i : ℝ) := by
  unfold cinner
  apply Finset.sum_congr rfl
  intro x hx
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [dotProduct, Pi.star_apply, star_trivial]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- The physical first-step Hessian is symmetric on real configurations. -/
theorem baseSectorHessian_symmetric (ϱ : ℝ) (aw : ℕ → ℝ) (μ : ℝ)
    (α : (GeneratingSet.single (d := d) (L := L)
      (N₀ := 1 * n) (k := 1) ϱ).Ω 1 → ℝ)
    (u v : Config (Torus d (L * n)) N) :
    cinner u (baseSectorHessian ϱ aw μ α v) =
      cinner (baseSectorHessian ϱ aw μ α u) v := by
  let G : GeneratingSet d L (1 * n) 1 ϱ := GeneratingSet.single ϱ
  let site : Torus d (L * n) → G.Ω 1 := fun z =>
    ⟨(baseSector_side L n).symm ▸ z,
      baseSector_mem_single ϱ ((baseSector_side L n).symm ▸ z)⟩
  let A : Matrix (Torus d (L * n)) (Torus d (L * n)) ℝ := fun x y =>
    fullMatrix G aw μ (site x : Torus d (1 * n * L ^ 1))
      (site y : Torus d (1 * n * L ^ 1)) +
      if x = y then α (site x) else 0
  have hA (x y : Torus d (L * n)) : A x y = A y x :=
    baseSectorHessian_coeff_symm ϱ aw μ α x y
  rw [cinner_components, cinner_components]
  simp_rw [baseSectorHessian_apply]
  change (∑ x : Torus d (L * n), ∑ i : Fin N,
    (u x i : ℝ) * ∑ y : Torus d (L * n), A x y * (v y i : ℝ)) =
    ∑ x : Torus d (L * n), ∑ i : Fin N,
      (∑ y : Torus d (L * n), A x y * (u y i : ℝ)) * (v x i : ℝ)
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  calc
    _ = ∑ x : Torus d (L * n), ∑ y : Torus d (L * n),
          ∑ i : Fin N, (u x i : ℝ) * (A x y * (v y i : ℝ)) := by
            apply Finset.sum_congr rfl
            intro x hx
            rw [Finset.sum_comm]
    _ = ∑ y : Torus d (L * n), ∑ x : Torus d (L * n),
          ∑ i : Fin N, (u x i : ℝ) * (A x y * (v y i : ℝ)) := by
            rw [Finset.sum_comm]
    _ = ∑ y : Torus d (L * n), ∑ i : Fin N,
          ∑ x : Torus d (L * n),
            (u x i : ℝ) * (A x y * (v y i : ℝ)) := by
              apply Finset.sum_congr rfl
              intro y hy
              rw [Finset.sum_comm]
    _ = ∑ y : Torus d (L * n), ∑ i : Fin N,
          ∑ x : Torus d (L * n),
            (A y x * (u x i : ℝ)) * (v y i : ℝ) := by
              apply Finset.sum_congr rfl
              intro y hy
              apply Finset.sum_congr rfl
              intro i hi
              apply Finset.sum_congr rfl
              intro x hx
              rw [hA]
              ring
    _ = _ := by rfl

/-- Componentwise realification of the transported first-step Dirichlet operator. -/
theorem baseSectorHessian_component_complex (ϱ : ℝ) (aw : ℕ → ℝ) (μ : ℝ)
    (α : (GeneratingSet.single (d := d) (L := L)
      (N₀ := 1 * n) (k := 1) ϱ).Ω 1 → ℝ)
    (v : Config (Torus d (L * n)) N)
    (x : Torus d (L * n)) (i : Fin N) :
    let G : GeneratingSet d L (1 * n) 1 ϱ := GeneratingSet.single ϱ
    let site : Torus d (L * n) → G.Ω 1 := fun z =>
      ⟨(baseSector_side L n).symm ▸ z,
        baseSector_mem_single ϱ ((baseSector_side L n).symm ▸ z)⟩
    (dirichletOperator G aw μ (fun p => (α p : ℂ)) *ᵥ
      (fun y : G.Ω 1 =>
        (((v (baseSector_side L n ▸ (y : Torus d (1 * n * L ^ 1)))) i : ℝ) : ℂ)))
      (site x) = ((baseSectorHessian ϱ aw μ α v x i : ℝ) : ℂ) := by
  dsimp only
  let G : GeneratingSet d L (1 * n) 1 ϱ := GeneratingSet.single ϱ
  let site : Torus d (L * n) → G.Ω 1 := fun z =>
    ⟨(baseSector_side L n).symm ▸ z,
      baseSector_mem_single ϱ ((baseSector_side L n).symm ▸ z)⟩
  let A : Matrix (Torus d (L * n)) (Torus d (L * n)) ℝ := fun z y =>
    fullMatrix G aw μ (site z : Torus d (1 * n * L ^ 1))
      (site y : Torus d (1 * n * L ^ 1)) +
      if z = y then α (site z) else 0
  have hsite (y : G.Ω 1) :
      site (baseSector_side L n ▸ (y : Torus d (1 * n * L ^ 1))) = y := by
    apply Subtype.ext
    exact baseSector_cast_cancel_rev (baseSector_side L n) y.1
  have hterm (y : G.Ω 1) :
      dirichletOperator G aw μ (fun p => (α p : ℂ)) (site x) y *
        (((v (baseSector_side L n ▸ (y : Torus d (1 * n * L ^ 1)))) i : ℝ) : ℂ) =
      ((A x (baseSector_side L n ▸ (y : Torus d (1 * n * L ^ 1))) *
        (v (baseSector_side L n ▸ (y : Torus d (1 * n * L ^ 1))) i : ℝ) : ℝ) : ℂ) := by
    have hc := baseSectorHessian_coeff_eq ϱ aw μ α x
      (baseSector_side L n ▸ (y : Torus d (1 * n * L ^ 1)))
    change dirichletOperator G aw μ (fun p => (α p : ℂ)) (site x)
      (site (baseSector_side L n ▸ (y : Torus d (1 * n * L ^ 1)))) =
      ((A x (baseSector_side L n ▸ (y : Torus d (1 * n * L ^ 1))) : ℝ) : ℂ) at hc
    rw [hsite] at hc
    rw [hc]
    exact (Complex.ofReal_mul _ _).symm
  rw [baseSectorHessian_apply]
  change (∑ y : G.Ω 1,
    dirichletOperator G aw μ (fun p => (α p : ℂ)) (site x) y *
      (((v (baseSector_side L n ▸ (y : Torus d (1 * n * L ^ 1)))) i : ℝ) : ℂ)) = _
  calc
    _ = ∑ y : G.Ω 1, ((A x (baseSector_side L n ▸
        (y : Torus d (1 * n * L ^ 1))) *
        (v (baseSector_side L n ▸ (y : Torus d (1 * n * L ^ 1))) i : ℝ) : ℝ) : ℂ) := by
          apply Finset.sum_congr rfl
          intro y hy
          exact hterm y
    _ = ((∑ y : G.Ω 1, A x (baseSector_side L n ▸
        (y : Torus d (1 * n * L ^ 1))) *
        (v (baseSector_side L n ▸ (y : Torus d (1 * n * L ^ 1))) i : ℝ) : ℝ) : ℂ) := by
          rw [Complex.ofReal_sum]
    _ = ((∑ y : Torus d (L * n), A x y * (v y i : ℝ) : ℝ) : ℂ) := by
          rw [baseSector_sum_native_sites ϱ
            (fun y : Torus d (L * n) => A x y * (v y i : ℝ))]
    _ = _ := by rfl

/-- The complex bilinear Dirichlet form of P4 (2.44) is the complexification of the
real physical Hessian pairing, for arbitrary real configurations. -/
theorem baseSectorHessian_pair_eq_cinner (ϱ : ℝ) (aw : ℕ → ℝ) (μ : ℝ)
    (α : (GeneratingSet.single (d := d) (L := L)
      (N₀ := 1 * n) (k := 1) ϱ).Ω 1 → ℝ)
    (u v : Config (Torus d (L * n)) N) :
    let G : GeneratingSet d L (1 * n) 1 ϱ := GeneratingSet.single ϱ
    let U : G.Ω 1 × Fin N → ℂ := fun p =>
      (((u (baseSector_side L n ▸ (p.1 : Torus d (1 * n * L ^ 1)))) p.2 : ℝ) : ℂ)
    let V : G.Ω 1 × Fin N → ℂ := fun p =>
      (((v (baseSector_side L n ▸ (p.1 : Torus d (1 * n * L ^ 1)))) p.2 : ℝ) : ℂ)
    pair G U (liftOp N (dirichletOperator G aw μ (fun p => (α p : ℂ))) *ᵥ V) =
      ((cinner u (baseSectorHessian ϱ aw μ α v) : ℝ) : ℂ) := by
  dsimp only
  let G : GeneratingSet d L (1 * n) 1 ϱ := GeneratingSet.single ϱ
  let U : G.Ω 1 × Fin N → ℂ := fun p =>
    (((u (baseSector_side L n ▸ (p.1 : Torus d (1 * n * L ^ 1)))) p.2 : ℝ) : ℂ)
  let V : G.Ω 1 × Fin N → ℂ := fun p =>
    (((v (baseSector_side L n ▸ (p.1 : Torus d (1 * n * L ^ 1)))) p.2 : ℝ) : ℂ)
  have hpoint (x : G.Ω 1) (i : Fin N) :
      (liftOp N (dirichletOperator G aw μ (fun p => (α p : ℂ))) *ᵥ V) (x, i) =
      (((baseSectorHessian ϱ aw μ α v
        (baseSector_side L n ▸ (x : Torus d (1 * n * L ^ 1))) i : ℝ) : ℂ)) := by
    have h := baseSectorHessian_component_complex ϱ aw μ α v
      (baseSector_side L n ▸ (x : Torus d (1 * n * L ^ 1))) i
    have hs : (⟨(baseSector_side L n).symm ▸
        (baseSector_side L n ▸ (x : Torus d (1 * n * L ^ 1))),
        baseSector_mem_single ϱ ((baseSector_side L n).symm ▸
          (baseSector_side L n ▸ (x : Torus d (1 * n * L ^ 1))))⟩ : G.Ω 1) = x := by
      apply Subtype.ext
      exact baseSector_cast_cancel_rev (baseSector_side L n) x.1
    dsimp only at h
    rw [hs] at h
    change (dirichletOperator G aw μ (fun p => (α p : ℂ)) *ᵥ
      (fun y : G.Ω 1 => V (y, i))) x = _ at h
    rw [liftOp_mulVec]
    exact h
  unfold pair
  rw [Fintype.sum_prod_type]
  calc
    _ = ∑ x : G.Ω 1, ∑ i : Fin N,
          (((u (baseSector_side L n ▸ (x : Torus d (1 * n * L ^ 1))) i : ℝ) : ℂ) *
            ((baseSectorHessian ϱ aw μ α v
              (baseSector_side L n ▸ (x : Torus d (1 * n * L ^ 1))) i : ℝ) : ℂ)) := by
            apply Finset.sum_congr rfl
            intro x hx
            apply Finset.sum_congr rfl
            intro i hi
            rw [hpoint x i]
    _ = ((∑ x : G.Ω 1, ∑ i : Fin N,
          (u (baseSector_side L n ▸ (x : Torus d (1 * n * L ^ 1))) i : ℝ) *
            (baseSectorHessian ϱ aw μ α v
              (baseSector_side L n ▸ (x : Torus d (1 * n * L ^ 1))) i : ℝ) : ℝ) : ℂ) := by
            simp only [Complex.ofReal_sum, Complex.ofReal_mul]
    _ = ((∑ x : Torus d (L * n), ∑ i : Fin N,
          (u x i : ℝ) * (baseSectorHessian ϱ aw μ α v x i : ℝ) : ℝ) : ℂ) := by
            rw [baseSector_sum_native_sites ϱ (fun x : Torus d (L * n) =>
              ∑ i : Fin N, (u x i : ℝ) * (baseSectorHessian ϱ aw μ α v x i : ℝ))]
    _ = _ := by rw [cinner_components]

/-- The physical-support Dirichlet form is the real Hessian pairing at the
background multiplier. -/
theorem baseSectorHessian_pair_eq_cinner_of_product_ne_zero (ϱ : ℝ)
    (aw : ℕ → ℝ) (regimeB : Prop) (ν δ₀ : ℝ) (hδ : 0 < δ₀)
    (h : EuclideanSpace ℝ (Fin N)) (hh : ‖h‖ = 1)
    (H : BgHyp d L 1 ϱ aw (if regimeB then ν else 0))
    (hΛ1 : 4 * d * L * δ₀ ≤ bgC1 d L N)
    (θ : Torus d n → EuclideanSpace ℝ (Fin N)) (φ : CfgT d N L n)
    (hp : baseSectorCubeProduct regimeB ν δ₀ h θ φ ≠ 0)
    (u v : Config (Torus d (L * n)) N) :
    let G : GeneratingSet d L (1 * n) 1 ϱ := GeneratingSet.single ϱ
    let D := baseSectorDatum ϱ θ h
    let α := bgMult G aw (if regimeB then ν else 0) D
    let U : G.Ω 1 × Fin N → ℂ := fun p =>
      (((u (baseSector_side L n ▸ (p.1 : Torus d (1 * n * L ^ 1)))) p.2 : ℝ) : ℂ)
    let V : G.Ω 1 × Fin N → ℂ := fun p =>
      (((v (baseSector_side L n ▸ (p.1 : Torus d (1 * n * L ^ 1)))) p.2 : ℝ) : ℂ)
    pair G U (liftOp N (dirichletOperator G aw (if regimeB then ν else 0) α) *ᵥ V) =
      ((cinner u (baseSectorHessian ϱ aw (if regimeB then ν else 0)
        (fun p => (α p).re) v) : ℝ) : ℂ) := by
  dsimp only
  let G : GeneratingSet d L (1 * n) 1 ϱ := GeneratingSet.single ϱ
  let D : BgData G N := baseSectorDatum ϱ θ h
  let α := bgMult G aw (if regimeB then ν else 0) D
  have hα (p : G.Ω 1) : ((α p).re : ℂ) = α p := by
    apply Complex.ext
    · simp
    · simpa [α] using (baseSector_bgMult_real_of_product_ne_zero
        ϱ aw regimeB ν δ₀ hδ h hh H hΛ1 θ φ hp p).symm
  have heq : (fun p : G.Ω 1 => (((α p).re : ℝ) : ℂ)) = α := funext hα
  have hp := baseSectorHessian_pair_eq_cinner ϱ aw (if regimeB then ν else 0)
    (fun p : G.Ω 1 => (α p).re) u v
  dsimp only at hp
  rw [heq] at hp
  exact hp

/-- The physical first-step action has the exact real Hessian chord form on the
nonzero all-good support. -/
theorem baseSector_physical_B_hessian_of_product_ne_zero (ϱ : ℝ)
    (aw : ℕ → ℝ) (a₀ : ℝ) (ha : aw 1 = a₀)
    (regimeB : Prop) (ν δ₀ : ℝ) (hδ : 0 < δ₀)
    (h : EuclideanSpace ℝ (Fin N)) (hh : ‖h‖ = 1)
    (H : BgHyp d L 1 ϱ aw (if regimeB then ν else 0))
    (hΛ1 : 4 * d * L * δ₀ ≤ bgC1 d L N)
    (θ : Torus d n → EuclideanSpace ℝ (Fin N)) (φ : CfgT d N L n)
    (hp : baseSectorCubeProduct regimeB ν δ₀ h θ φ ≠ 0) :
    let G : GeneratingSet d L (1 * n) 1 ϱ := GeneratingSet.single ϱ
    let D := baseSectorDatum ϱ θ h
    let α := bgMult G aw (if regimeB then ν else 0) D
    let e : Config (Torus d (L * n)) N := baseSectorCenter ϱ aw regimeB ν h θ
    let ec : CfgT d N L n := fun x => ⟨e x,
      mem_sphere_zero_iff_norm.mpr (baseSectorCenter_unit ϱ aw regimeB ν h hh H θ x)⟩
    let B : CfgT d N L n → ℝ := fun ψ =>
      energy d N (L * n) (if regimeB then ν else 0) h ψ +
        (a₀ * (L : ℝ) ^ d / (2 * (L : ℝ) ^ 2)) *
          ∑ y : Torus d n, ‖θ y - baseQ d N L n ψ y‖ ^ 2
    let u : Config (Torus d (L * n)) N := fun x => (φ x : EuclideanSpace ℝ (Fin N)) - e x
    B φ - B ec = (1 / 2) * cinner u
      (baseSectorHessian ϱ aw (if regimeB then ν else 0) (fun p => (α p).re) u) := by
  dsimp only
  let G : GeneratingSet d L (1 * n) 1 ϱ := GeneratingSet.single ϱ
  let D : BgData G N := baseSectorDatum ϱ θ h
  let α := bgMult G aw (if regimeB then ν else 0) D
  let e : Config (Torus d (L * n)) N := baseSectorCenter ϱ aw regimeB ν h θ
  let ec : CfgT d N L n := fun x => ⟨e x,
    mem_sphere_zero_iff_norm.mpr (baseSectorCenter_unit ϱ aw regimeB ν h hh H θ x)⟩
  let B : CfgT d N L n → ℝ := fun ψ =>
    energy d N (L * n) (if regimeB then ν else 0) h ψ +
      (a₀ * (L : ℝ) ^ d / (2 * (L : ℝ) ^ 2)) *
        ∑ y : Torus d n, ‖θ y - baseQ d N L n ψ y‖ ^ 2
  let u : Config (Torus d (L * n)) N := fun x => (φ x : EuclideanSpace ℝ (Fin N)) - e x
  have hch := baseSector_physical_B_chord_of_product_ne_zero
    ϱ aw a₀ ha regimeB ν δ₀ hδ h hh H hΛ1 θ φ hp
  dsimp only at hch
  have hfield :
      (fun p : G.Ω 1 × Fin N =>
        (((φ (baseSector_side L n ▸ (p.1 : Torus d (1 * n * L ^ 1))) :
          EuclideanSpace ℝ (Fin N)) p.2 : ℝ) : ℂ)) -
      (fun p : G.Ω 1 × Fin N =>
        ((e (baseSector_side L n ▸ (p.1 : Torus d (1 * n * L ^ 1))) p.2 : ℝ) : ℂ)) =
      (fun p : G.Ω 1 × Fin N =>
        ((u (baseSector_side L n ▸ (p.1 : Torus d (1 * n * L ^ 1))) p.2 : ℝ) : ℂ)) := by
    funext p
    simp [u, Pi.sub_apply]
  rw [hfield] at hch
  have hpair := baseSectorHessian_pair_eq_cinner_of_product_ne_zero
    ϱ aw regimeB ν δ₀ hδ h hh H hΛ1 θ φ hp u u
  dsimp only at hpair
  rw [hpair] at hch
  change (((B φ - B ec : ℝ)) : ℂ) =
    (1 / 2 : ℂ) * ((cinner u
      (baseSectorHessian ϱ aw (if regimeB then ν else 0)
        (fun p => (α p).re) u) : ℝ) : ℂ) at hch
  have hre := congrArg Complex.re hch
  simpa using hre

/-- At the uncut parameter `s ≡ 1`, the base cut/core Hamiltonian has exactly
the physical Hessian pairing on nonzero all-good support. -/
theorem baseSectorHessian_cut_core_one_of_product_ne_zero (ϱ : ℝ)
    (aw : ℕ → ℝ) (regimeB : Prop) (ν δ₀ : ℝ) (hδ : 0 < δ₀)
    (h : EuclideanSpace ℝ (Fin N)) (hh : ‖h‖ = 1)
    (H : BgHyp d L 1 ϱ aw (if regimeB then ν else 0))
    (hΛ1 : 4 * d * L * δ₀ ≤ bgC1 d L N)
    (θ : Torus d n → EuclideanSpace ℝ (Fin N)) (φ : CfgT d N L n)
    (hp : baseSectorCubeProduct regimeB ν δ₀ h θ φ ≠ 0)
    (u v : Config (Torus d (L * n)) N) :
    let G : GeneratingSet d L (1 * n) 1 ϱ := GeneratingSet.single ϱ
    let D := baseSectorDatum ϱ θ h
    let α := bgMult G aw (if regimeB then ν else 0) D
    let U : G.Ω 1 × Fin N → ℂ := fun p =>
      (((u (baseSector_side L n ▸ (p.1 : Torus d (1 * n * L ^ 1)))) p.2 : ℝ) : ℂ)
    let V : G.Ω 1 × Fin N → ℂ := fun p =>
      (((v (baseSector_side L n ▸ (p.1 : Torus d (1 * n * L ^ 1)))) p.2 : ℝ) : ℂ)
    pair G U (liftOp N (baseHamiltonian G aw (if regimeB then ν else 0) α
      (fun _ => 1)) *ᵥ V) =
      ((cinner u (baseSectorHessian ϱ aw (if regimeB then ν else 0)
        (fun p => (α p).re) v) : ℝ) : ℂ) := by
  dsimp only
  rw [baseHamiltonian_one]
  exact baseSectorHessian_pair_eq_cinner_of_product_ne_zero ϱ aw regimeB
    ν δ₀ hδ h hh H hΛ1 θ φ hp u v

/-- The landed base cut/core coercivity at its uncut parameter, for the physical
background centre and the multiplier smallness premise of the base resolvent. -/
theorem baseSector_baseOp_coercive_of_mult_bound (ϱ : ℝ) (aw : ℕ → ℝ)
    (regimeB : Prop) (ν : ℝ) (hμ : 0 ≤ (if regimeB then ν else 0))
    (ha : IsAdmissibleWeights 1 aw)
    (h : EuclideanSpace ℝ (Fin N)) (hh : ‖h‖ = 1)
    (H : BgHyp d L 1 ϱ aw (if regimeB then ν else 0))
    (θ : Torus d n → EuclideanSpace ℝ (Fin N))
    (hα : ∀ z : (GeneratingSet.single (d := d) (L := L)
      (N₀ := 1 * n) (k := 1) ϱ).Ω 1,
      ‖bgMult (GeneratingSet.single (d := d) (L := L)
        (N₀ := 1 * n) (k := 1) ϱ) aw (if regimeB then ν else 0)
        (baseSectorDatum ϱ θ h) z‖ ≤ 1 / (8 * (L : ℝ) ^ 2)) :
    let G : GeneratingSet d L (1 * n) 1 ϱ := GeneratingSet.single ϱ
    let D := baseSectorDatum ϱ θ h
    let α := bgMult G aw (if regimeB then ν else 0) D
    let e : G.Ω 1 → Fin N → ℝ := fun z i =>
      (baseSectorCenter ϱ aw regimeB ν h θ
        (baseSector_side L n ▸ (z : Torus d (1 * n * L ^ 1))) i : ℝ)
    Green.IsCoercive (baseOp N (fun z i => (e z i : ℂ))
      (baseHamiltonian G aw (if regimeB then ν else 0) α (fun _ => 1)))
      (baseCoercivity L) := by
  dsimp only
  let G : GeneratingSet d L (1 * n) 1 ϱ := GeneratingSet.single ϱ
  let D : BgData G N := baseSectorDatum ϱ θ h
  let α := bgMult G aw (if regimeB then ν else 0) D
  let e : G.Ω 1 → Fin N → ℝ := fun z i =>
    (baseSectorCenter ϱ aw regimeB ν h θ
      (baseSector_side L n ▸ (z : Torus d (1 * n * L ^ 1))) i : ℝ)
  have he (z : G.Ω 1) : ∑ i, e z i ^ 2 = 1 := by
    have hn := baseSectorCenter_unit ϱ aw regimeB ν h hh H θ
      (baseSector_side L n ▸ (z : Torus d (1 * n * L ^ 1)))
    have hs := EuclideanSpace.norm_sq_eq
      (baseSectorCenter ϱ aw regimeB ν h θ
        (baseSector_side L n ▸ (z : Torus d (1 * n * L ^ 1))))
    simp only [Real.norm_eq_abs, sq_abs] at hs
    change ∑ i, (baseSectorCenter ϱ aw regimeB ν h θ
      (baseSector_side L n ▸ (z : Torus d (1 * n * L ^ 1))) i : ℝ) ^ 2 = 1
    rw [← hs, hn]
    norm_num
  exact baseOp_isCoercive_real G hμ ha hα (fun _ => 1)
    (fun _ _ => ⟨zero_le_one, le_rfl⟩) e he

/-- The uncut component base operator is coercive on the actual P5 all-good
support; the multiplier bound follows from the background estimates. -/
theorem baseSector_baseOp_coercive_of_product_ne_zero (ϱ : ℝ) (aw : ℕ → ℝ)
    (regimeB : Prop) (ν δ₀ : ℝ) (hδ : 0 < δ₀)
    (h : EuclideanSpace ℝ (Fin N)) (hh : ‖h‖ = 1)
    (H : BgHyp d L 1 ϱ aw (if regimeB then ν else 0))
    (hΛ1 : 4 * d * L * δ₀ ≤ bgC1 d L N)
    (θ : Torus d n → EuclideanSpace ℝ (Fin N)) (φ : CfgT d N L n)
    (hp : baseSectorCubeProduct regimeB ν δ₀ h θ φ ≠ 0) :
    let G : GeneratingSet d L (1 * n) 1 ϱ := GeneratingSet.single ϱ
    let D := baseSectorDatum ϱ θ h
    let α := bgMult G aw (if regimeB then ν else 0) D
    let e : G.Ω 1 → Fin N → ℝ := fun z i =>
      (baseSectorCenter ϱ aw regimeB ν h θ
        (baseSector_side L n ▸ (z : Torus d (1 * n * L ^ 1))) i : ℝ)
    Green.IsCoercive (baseOp N (fun z i => (e z i : ℂ))
      (baseHamiltonian G aw (if regimeB then ν else 0) α (fun _ => 1)))
      (baseCoercivity L) := by
  exact baseSector_baseOp_coercive_of_mult_bound ϱ aw regimeB ν H.mass H.weights
    h hh H θ (baseSector_bgMult_norm_le_of_product_ne_zero ϱ aw regimeB ν δ₀
      hδ h hh H hΛ1 θ φ hp)

end Balaban.LargeField
