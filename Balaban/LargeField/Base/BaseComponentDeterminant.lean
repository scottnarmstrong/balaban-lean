/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseComponentIdentity
import Balaban.Analysis.MatrixDetExp
import Balaban.Fluctuation.StepComplexCov

/-!
# Trace logarithm and determinant of a cut first-step operator

The logarithm of the operator of P4 (2.51)–(2.54) restricts to either block of a
crossing-bond cut. Its trace splits, giving the determinant factorization.
-/

@[expose] public section

namespace Balaban.LargeField.Base

open Matrix Classical Balaban.Localization

variable {κ : Type*} [Fintype κ] [DecidableEq κ] (P : κ → Prop)

private theorem logMat_fintype_congr {ι : Type*} (F₁ F₂ : Fintype ι)
    [DecidableEq ι] (A : Matrix ι ι ℂ) (p q : ι) :
    @logMat ι F₁ _ A p q = @logMat ι F₂ _ A p q := by
  have h : F₁ = F₂ := Subsingleton.elim _ _
  subst F₂
  rfl

/-- The principal logarithm restricts to a diagonal block of a cut operator. -/
theorem logMat_submatrix_block [Nonempty κ] [Nonempty {p : κ // P p}]
    {M : Matrix κ κ ℂ} (hM : BlockDiag P M) (hR : ResOK M)
    (hRI : ResOK (M.submatrix (Subtype.val : {p : κ // P p} → κ)
      (Subtype.val : {p : κ // P p} → κ))) (p q : {p : κ // P p}) :
    logMat M p.1 q.1 = logMat (M.submatrix Subtype.val Subtype.val) p q := by
  simp only [logMat, intMat, Matrix.neg_apply, Matrix.sub_apply, Matrix.smul_apply]
  congr 1
  refine MeasureTheory.integral_congr_ae ?_
  refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).2
    (Filter.Eventually.of_forall fun y hy => ?_)
  have hy0 : 0 ≤ y := le_of_lt hy
  beta_reduce
  have hsub : ((y : ℂ) • (1 : Matrix κ κ ℂ) + M).submatrix
      (Subtype.val : {p : κ // P p} → κ) Subtype.val =
      (y : ℂ) • (1 : Matrix {p : κ // P p} {p : κ // P p} ℂ) +
        M.submatrix Subtype.val Subtype.val := by
    ext a b
    simp only [Matrix.submatrix_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply]
    congr 1
    simp only [Subtype.ext_iff]
  rw [inv_submatrix_block P (blockDiag_add_smul_one hM y) (hR y hy0)
    (hsub.symm ▸ hRI y hy0) p q, hsub]
  simp only [Matrix.one_apply, Subtype.val_injective.eq_iff]

/-- The trace logarithm of a cut matrix is the sum of the traces of its two blocks. -/
theorem trace_logMat_eq_blocks [Nonempty κ] [Nonempty {p : κ // P p}]
    [Nonempty {p : κ // ¬ P p}] {M : Matrix κ κ ℂ}
    (hM : BlockDiag P M) (hR : ResOK M)
    (hRI : ResOK (M.submatrix (Subtype.val : {p : κ // P p} → κ) Subtype.val))
    (hRJ : ResOK (M.submatrix (Subtype.val : {p : κ // ¬ P p} → κ) Subtype.val)) :
    (logMat M).trace =
      (logMat (M.submatrix (Subtype.val : {p : κ // P p} → κ) Subtype.val)).trace +
      (logMat (M.submatrix (Subtype.val : {p : κ // ¬ P p} → κ) Subtype.val)).trace := by
  have hQ : BlockDiag (fun p => ¬ P p) M := by
    intro p q hpq
    apply hM p q
    simp only [not_not] at hpq
    simpa only [not_not] using not_congr hpq
  simp only [Matrix.trace, Matrix.diag_apply]
  rw [← Fintype.sum_subtype_add_sum_subtype P
    (fun p => logMat M p p)]
  congr 1
  · apply Finset.sum_congr rfl
    intro p _
    exact logMat_submatrix_block P hM hR hRI p p
  · apply Finset.sum_congr rfl
    intro p _
    have hh := logMat_submatrix_block (P := fun p => ¬ P p) hQ hR
      (by convert hRJ using 1) p p
    convert hh using 1
    exact logMat_fintype_congr _ _ _ _ _

/-- Each block determinant and the ambient determinant are exponentials of their
principal trace logarithms. The determinant of the cut operator factors. -/
theorem det_eq_exp_trace_logMat_and_mul_blocks [Nonempty κ]
    [Nonempty {p : κ // P p}] [Nonempty {p : κ // ¬ P p}]
    {M : Matrix κ κ ℂ} (hM : BlockDiag P M) (hR : ResOK M)
    (hRI : ResOK (M.submatrix (Subtype.val : {p : κ // P p} → κ) Subtype.val))
    (hRJ : ResOK (M.submatrix (Subtype.val : {p : κ // ¬ P p} → κ) Subtype.val)) :
    M.det = Complex.exp (logMat M).trace ∧
    (M.submatrix (Subtype.val : {p : κ // P p} → κ) Subtype.val).det =
      Complex.exp (logMat (M.submatrix (Subtype.val : {p : κ // P p} → κ)
        Subtype.val)).trace ∧
    M.det =
      (M.submatrix (Subtype.val : {p : κ // P p} → κ) Subtype.val).det *
      (M.submatrix (Subtype.val : {p : κ // ¬ P p} → κ) Subtype.val).det := by
  have hdet (A : Matrix κ κ ℂ) (hA : ResOK A) :
      A.det = Complex.exp (logMat A).trace := by
    rw [← det_exp_eq_exp_trace, exp_logMat hA]
  have hdetI : (M.submatrix (Subtype.val : {p : κ // P p} → κ) Subtype.val).det =
      Complex.exp (logMat (M.submatrix (Subtype.val : {p : κ // P p} → κ)
        Subtype.val)).trace := by
    rw [← det_exp_eq_exp_trace, exp_logMat hRI]
  have hdetJ : (M.submatrix (Subtype.val : {p : κ // ¬ P p} → κ) Subtype.val).det =
      Complex.exp (logMat (M.submatrix (Subtype.val : {p : κ // ¬ P p} → κ)
        Subtype.val)).trace := by
    rw [← det_exp_eq_exp_trace, exp_logMat hRJ]
  refine ⟨hdet M hR, hdetI, ?_⟩
  rw [hdet M hR, hdetI, hdetJ, trace_logMat_eq_blocks P hM hR hRI hRJ,
    Complex.exp_add]

end Balaban.LargeField.Base

namespace Balaban.LargeField

open Balaban Balaban.Background Balaban.Multiscale Balaban.Green
open Balaban.LargeField.Base Matrix Classical Balaban.Localization

variable {d N L n : ℕ} [NeZero L] [NeZero n] [NeZero N]

/-- On nonzero P5 all-good support, a proper crossing-bond cut splits the trace
logarithm and determinant of the physical first-step operator. The component
and its complement each contain a fine site of the chart domain. -/
theorem baseSector_component_logDet_factorization (ϱ : ℝ) (aw : ℕ → ℝ)
    (regimeB : Prop) (ν δ₀ : ℝ) (hδ : 0 < δ₀)
    (h : EuclideanSpace ℝ (Fin N)) (hh : ‖h‖ = 1)
    (H : BgHyp d L 1 ϱ aw (if regimeB then ν else 0))
    (hΛ1 : 4 * d * L * δ₀ ≤ bgC1 d L N)
    (θ : Torus d n → EuclideanSpace ℝ (Fin N)) (φ : CfgT d N L n)
    (hp : baseSectorCubeProduct regimeB ν δ₀ h θ φ ≠ 0)
    (U : Set (Torus d (1 * n * L ^ 1)))
    (hU : IsFirstBlockUnion (GeneratingSet.single (d := d) (L := L)
      (N₀ := 1 * n) (k := 1) ϱ) U)
    (hU0 : ∃ z : (GeneratingSet.single (d := d) (L := L)
      (N₀ := 1 * n) (k := 1) ϱ).Ω 1,
      (z : Torus d (1 * n * L ^ 1)) ∈ U)
    (hUc : ∃ z : (GeneratingSet.single (d := d) (L := L)
      (N₀ := 1 * n) (k := 1) ϱ).Ω 1,
      (z : Torus d (1 * n * L ^ 1)) ∉ U)
    {η : ℝ} (hη0 : 0 ≤ η)
    (hη : η ≤ baseCoercivity L / (8 * d))
    (s : FineBond d L (1 * n) → ℂ)
    (hs : s ∈ baseParamNbhd (GeneratingSet.single (d := d) (L := L)
      (N₀ := 1 * n) (k := 1) ϱ) η)
    (hz : CrossZero (GeneratingSet.single (d := d) (L := L)
      (N₀ := 1 * n) (k := 1) ϱ) U s) :
    let G : GeneratingSet d L (1 * n) 1 ϱ := GeneratingSet.single ϱ
    let α := bgMult G aw (if regimeB then ν else 0) (baseSectorDatum ϱ θ h)
    let e : G.Ω 1 → Fin N → ℝ := fun z i =>
      (baseSectorCenter ϱ aw regimeB ν h θ
        (baseSector_side L n ▸ (z : Torus d (1 * n * L ^ 1))) i : ℝ)
    let P : G.Ω 1 × Fin N → Prop := fun p =>
      (p.1 : Torus d (1 * n * L ^ 1)) ∈ U
    let I := {p : G.Ω 1 × Fin N // P p}
    let J := {p : G.Ω 1 × Fin N // ¬ P p}
    let A := baseOp N (fun z i => (e z i : ℂ))
      (baseHamiltonian G aw (if regimeB then ν else 0) α s)
    let A_U : Matrix I I ℂ := A.submatrix Subtype.val Subtype.val
    let A_V : Matrix J J ℂ := A.submatrix Subtype.val Subtype.val
    (logMat A).trace = (logMat A_U).trace + (logMat A_V).trace ∧
      A.det = Complex.exp (logMat A).trace ∧
      A_U.det = Complex.exp (logMat A_U).trace ∧
      (sqrtMat A_U).det = Complex.exp (-(1 / 2) * (logMat A_U).trace) ∧
      A.det = A_U.det * A_V.det := by
  dsimp only
  let G : GeneratingSet d L (1 * n) 1 ϱ := GeneratingSet.single ϱ
  let α := bgMult G aw (if regimeB then ν else 0) (baseSectorDatum ϱ θ h)
  let e : G.Ω 1 → Fin N → ℝ := fun z i =>
    (baseSectorCenter ϱ aw regimeB ν h θ
      (baseSector_side L n ▸ (z : Torus d (1 * n * L ^ 1))) i : ℝ)
  let P : G.Ω 1 × Fin N → Prop := fun p =>
    (p.1 : Torus d (1 * n * L ^ 1)) ∈ U
  let I := {p : G.Ω 1 × Fin N // P p}
  let J := {p : G.Ω 1 × Fin N // ¬ P p}
  let A := baseOp N (fun z i => (e z i : ℂ))
    (baseHamiltonian G aw (if regimeB then ν else 0) α s)
  let A_U : Matrix I I ℂ := A.submatrix Subtype.val Subtype.val
  let A_V : Matrix J J ℂ := A.submatrix Subtype.val Subtype.val
  let : Nonempty I := by
    obtain ⟨z, hzU⟩ := hU0
    exact ⟨⟨(z, 0), hzU⟩⟩
  let : Nonempty J := by
    obtain ⟨z, hzU⟩ := hUc
    exact ⟨⟨(z, 0), hzU⟩⟩
  let : Nonempty (G.Ω 1 × Fin N) := ⟨(hU0.choose, 0)⟩
  have hdata := baseSector_component_covariance ϱ aw regimeB ν δ₀ hδ h hh H
    hΛ1 θ φ hp U hU hU0 hη0 hη s hs hz
  dsimp only at hdata
  obtain ⟨hblock, hcoerU, hresU, -, -⟩ := hdata
  have he : ∀ z : G.Ω 1, ∑ i, e z i ^ 2 = 1 :=
    baseSectorCenter_sq_sum ϱ aw regimeB ν h hh H θ
  have hα : ∀ z : G.Ω 1, ‖α z‖ ≤ 1 / (8 * (L : ℝ) ^ 2) :=
    baseSector_bgMult_norm_le_of_product_ne_zero ϱ aw regimeB ν δ₀ hδ h hh H hΛ1 θ φ hp
  have hcoer : Green.IsCoercive A (baseCoercivity L / 2) :=
    baseOp_isCoercive_of_close G H.mass H.weights hα hη0 hη hs e he
  have hcoerV : Green.IsCoercive A_V (baseCoercivity L / 2) :=
    Green.isCoercive_submatrix hcoer Subtype.val Subtype.val_injective
  have hc : 0 < baseCoercivity L / 2 := by
    have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
    exact half_pos (baseCoercivity_pos hL)
  have hres : ResOK A := by
    intro x hx
    have hcx : 0 < baseCoercivity L / 2 + x := by linarith
    rw [add_comm]
    exact Green.isUnit_of_isCoercive hcx (hcoer.add_smul_one x)
  have hresV : ResOK A_V := by
    intro x hx
    have hcx : 0 < baseCoercivity L / 2 + x := by linarith
    rw [add_comm]
    exact Green.isUnit_of_isCoercive hcx (hcoerV.add_smul_one x)
  have ht := trace_logMat_eq_blocks P hblock hres hresU hresV
  have hd := det_eq_exp_trace_logMat_and_mul_blocks P hblock hres hresU hresV
  exact ⟨ht, hd.1, hd.2.1, Balaban.Localization.det_sqrtMat hresU, hd.2.2⟩

end Balaban.LargeField
