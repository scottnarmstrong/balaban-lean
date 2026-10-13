/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseChartHessian
public import Balaban.LargeField.Base.BaseResolventLocal
import Balaban.Green.CauchyInverse

/-!
# First-step covariance on a cut good component

The physical first-step centre and multiplier on nonzero P5 all-good support give the
coercive cut operator of BASE-KERNEL-3 (1.2)–(1.6). A component is a union of complete
first blocks, with crossing cut-bond parameters zero. Its operator is the principal
submatrix of the ambient cut operator. The principal inverse square root and logarithm
are those of the Stieltjes construction used in P4 (2.51)–(2.54).
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Background Balaban.Multiscale Balaban.Green
open Balaban.LargeField.Base Matrix Classical

variable {d N L n : ℕ} [NeZero L] [NeZero n]

/-- Coordinates of the physical unit centre have squared sum one. -/
theorem baseSectorCenter_sq_sum (ϱ : ℝ) (aw : ℕ → ℝ)
    (regimeB : Prop) (ν : ℝ)
    (h : EuclideanSpace ℝ (Fin N)) (hh : ‖h‖ = 1)
    (H : BgHyp d L 1 ϱ aw (if regimeB then ν else 0))
    (θ : Torus d n → EuclideanSpace ℝ (Fin N))
    (z : (GeneratingSet.single (d := d) (L := L)
      (N₀ := 1 * n) (k := 1) ϱ).Ω 1) :
    ∑ i : Fin N, (baseSectorCenter ϱ aw regimeB ν h θ
      (baseSector_side L n ▸ (z : Torus d (1 * n * L ^ 1))) i : ℝ) ^ 2 = 1 := by
  have hn := baseSectorCenter_unit ϱ aw regimeB ν h hh H θ
    (baseSector_side L n ▸ (z : Torus d (1 * n * L ^ 1)))
  have hs := EuclideanSpace.norm_sq_eq
    (baseSectorCenter ϱ aw regimeB ν h θ
      (baseSector_side L n ▸ (z : Torus d (1 * n * L ^ 1))))
  simp only [Real.norm_eq_abs, sq_abs] at hs
  rw [← hs, hn]
  norm_num

/-- The uncut physical first-step operator remains coercive on each component.
The principal submatrix is indexed by sites of the component and spin coordinates. -/
theorem baseSector_component_one_coercive (ϱ : ℝ) (aw : ℕ → ℝ)
    (regimeB : Prop) (ν δ₀ : ℝ) (hδ : 0 < δ₀)
    (h : EuclideanSpace ℝ (Fin N)) (hh : ‖h‖ = 1)
    (H : BgHyp d L 1 ϱ aw (if regimeB then ν else 0))
    (hΛ1 : 4 * d * L * δ₀ ≤ bgC1 d L N)
    (θ : Torus d n → EuclideanSpace ℝ (Fin N)) (φ : CfgT d N L n)
    (hp : baseSectorCubeProduct regimeB ν δ₀ h θ φ ≠ 0)
    (U : Set (Torus d (1 * n * L ^ 1))) :
    let G : GeneratingSet d L (1 * n) 1 ϱ := GeneratingSet.single ϱ
    let α := bgMult G aw (if regimeB then ν else 0) (baseSectorDatum ϱ θ h)
    let e : G.Ω 1 → Fin N → ℝ := fun z i =>
      (baseSectorCenter ϱ aw regimeB ν h θ
        (baseSector_side L n ▸ (z : Torus d (1 * n * L ^ 1))) i : ℝ)
    let I := {p : G.Ω 1 × Fin N // (p.1 : Torus d (1 * n * L ^ 1)) ∈ U}
    Green.IsCoercive ((baseOp N (fun z i => (e z i : ℂ))
      (baseHamiltonian G aw (if regimeB then ν else 0) α (fun _ => 1))).submatrix
        (Subtype.val : I → G.Ω 1 × Fin N) Subtype.val) (baseCoercivity L) := by
  dsimp only
  apply Green.isCoercive_submatrix
    (baseSector_baseOp_coercive_of_product_ne_zero ϱ aw regimeB ν δ₀ hδ h hh H
      hΛ1 θ φ hp) Subtype.val Subtype.val_injective

variable [NeZero N]

/-- On a nonempty cut component, the physical complex cut operator is block diagonal,
its principal submatrix is coercive, and its covariance and principal square root exist.
The cut parameters vanish on bonds crossing the component boundary. -/
theorem baseSector_component_covariance (ϱ : ℝ) (aw : ℕ → ℝ)
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
    let A := baseOp N (fun z i => (e z i : ℂ))
      (baseHamiltonian G aw (if regimeB then ν else 0) α s)
    let A_U : Matrix I I ℂ := A.submatrix Subtype.val Subtype.val
    BlockDiag P A ∧ Green.IsCoercive A_U (baseCoercivity L / 2) ∧
      Balaban.Localization.ResOK A_U ∧
      Balaban.Localization.sqrtMat A_U * Balaban.Localization.sqrtMat A_U = A_U⁻¹ ∧
      NormedSpace.exp (Balaban.Localization.logMat A_U) = A_U := by
  dsimp only
  let G : GeneratingSet d L (1 * n) 1 ϱ := GeneratingSet.single ϱ
  let α := bgMult G aw (if regimeB then ν else 0) (baseSectorDatum ϱ θ h)
  let e : G.Ω 1 → Fin N → ℝ := fun z i =>
    (baseSectorCenter ϱ aw regimeB ν h θ
      (baseSector_side L n ▸ (z : Torus d (1 * n * L ^ 1))) i : ℝ)
  let P : G.Ω 1 × Fin N → Prop := fun p => (p.1 : Torus d (1 * n * L ^ 1)) ∈ U
  let I := {p : G.Ω 1 × Fin N // P p}
  let A := baseOp N (fun z i => (e z i : ℂ))
    (baseHamiltonian G aw (if regimeB then ν else 0) α s)
  let A_U : Matrix I I ℂ := A.submatrix Subtype.val Subtype.val
  have he : ∀ z : G.Ω 1, ∑ i, e z i ^ 2 = 1 :=
    baseSectorCenter_sq_sum ϱ aw regimeB ν h hh H θ
  have hα : ∀ z : G.Ω 1, ‖α z‖ ≤ 1 / (8 * (L : ℝ) ^ 2) :=
    baseSector_bgMult_norm_le_of_product_ne_zero ϱ aw regimeB ν δ₀ hδ h hh H hΛ1 θ φ hp
  have hcoer : Green.IsCoercive A (baseCoercivity L / 2) :=
    baseOp_isCoercive_of_close G H.mass H.weights hα hη0 hη hs e he
  have hcomp : Green.IsCoercive A_U (baseCoercivity L / 2) :=
    Green.isCoercive_submatrix hcoer Subtype.val Subtype.val_injective
  have hc : 0 < baseCoercivity L / 2 := by
    have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
    exact half_pos (baseCoercivity_pos hL)
  have hres : Balaban.Localization.ResOK A_U := by
    intro x hx
    have hcx : 0 < baseCoercivity L / 2 + x := by linarith
    rw [add_comm]
    exact Green.isUnit_of_isCoercive hcx (hcomp.add_smul_one x)
  let : Nonempty I := by
    obtain ⟨z, hzU⟩ := hU0
    exact ⟨⟨(z, 0), hzU⟩⟩
  refine ⟨baseOp_blockDiag G hU aw (if regimeB then ν else 0) α hz e,
    hcomp, hres, Balaban.Localization.sqrtMat_mul_self hres,
    Balaban.Localization.exp_logMat hres⟩

end Balaban.LargeField
