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

end Balaban.LargeField
