/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseComponentCovariance
import Balaban.Polymer.TwoTorusDecCov

/-!
# Ambient and component first-step covariances

For a cut along a union of complete first blocks, the ambient inverse and the principal
inverse square root restrict to those of the component operator. This is the component
identity used with P4 (2.51)–(2.54) and BASE-KERNEL-3 (1.2)–(1.7).
-/

@[expose] public section

namespace Balaban.LargeField.Base

open Matrix Classical Balaban.Localization
open scoped Matrix.Norms.L2Operator

section Abstract

variable {κ : Type*} [Fintype κ] [DecidableEq κ] (P : κ → Prop)

/-- The inverse of a block diagonal matrix restricts to the inverse of its component block. -/
theorem inv_submatrix_block {M : Matrix κ κ ℂ} (hM : BlockDiag P M)
    (hunit : IsUnit M) (hunitI : IsUnit (M.submatrix
      (Subtype.val : {p : κ // P p} → κ) (Subtype.val : {p : κ // P p} → κ)))
    (p q : {p : κ // P p}) :
    M⁻¹ p.1 q.1 = (M.submatrix
      (Subtype.val : {p : κ // P p} → κ) (Subtype.val : {p : κ // P p} → κ))⁻¹ p q := by
  classical
  let I := {p : κ // P p}
  let M_I : Matrix I I ℂ := M.submatrix Subtype.val Subtype.val
  let f : I → ℂ := Pi.single q 1
  let f' : κ → ℂ := Pi.single q.1 1
  have hf : ∀ z : I, True → f' z.1 = f z := by
    intro z _
    simp only [f, f', Pi.single_apply, Subtype.val_injective.eq_iff]
  have ht := Balaban.Polymer.TwoTorusStep.inv_mulVec_transport_of_triangular
    (fun _ : I => True) P (Subtype.val : I → κ)
    (fun _ _ _ _ h => Subtype.val_injective h)
    (fun z _ => z.2) (fun z hz => ⟨⟨z, hz⟩, trivial, rfl⟩)
    M_I M (fun _ _ _ hz => (hz trivial).elim)
    (fun x z hx hz => hM x z (by simp [hx, hz]))
    (fun _ _ _ _ => rfl) hunitI hunit (f := f) (f' := f') (y := p) hf trivial
  simpa only [f, f', M_I, Matrix.mulVec_single_one, Matrix.col_apply] using ht

/-- The Stieltjes inverse square root respects a block compression. -/
theorem sqrtMat_submatrix_block [Nonempty κ] [Nonempty {p : κ // P p}]
    {M : Matrix κ κ ℂ} (hM : BlockDiag P M)
    (hR : ResOK M) (hRI : ResOK (M.submatrix
      (Subtype.val : {p : κ // P p} → κ) (Subtype.val : {p : κ // P p} → κ)))
    (p q : {p : κ // P p}) :
    sqrtMat M p.1 q.1 = sqrtMat (M.submatrix
      (Subtype.val : {p : κ // P p} → κ) (Subtype.val : {p : κ // P p} → κ)) p q := by
  simp only [sqrtMat, intMat, Matrix.smul_apply]
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

end Abstract

section EntryBound

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}

omit [Fintype ι] [DecidableEq ι] in
/-- An entry of a spin block is bounded by its Euclidean operator norm. -/
theorem norm_entry_le_blockOf (B : Matrix (ι × Fin N) (ι × Fin N) ℂ)
    (z w : ι) (i j : Fin N) : ‖B (z, i) (w, j)‖ ≤ ‖blockOf B z w‖ := by
  have h := Balaban.Localization.norm_entry_le (blockOf B z w)
    (norm_nonneg _) (fun v => sqNorm_mulVec_le_opNorm (blockOf B z w) v) i j
  simpa only [blockOf, Matrix.of_apply] using h

end EntryBound

end Balaban.LargeField.Base

namespace Balaban.LargeField

open Balaban Balaban.Background Balaban.Multiscale Balaban.Green
open Balaban.LargeField.Base Matrix Classical Balaban.Localization
open scoped Matrix.Norms.L2Operator

variable {d N L n : ℕ} [NeZero L] [NeZero n] [NeZero N]

/-- On nonzero P5 all-good support, the ambient cut covariance and its principal inverse
square root have exactly the entries of the operator on a cut component. The component
can be any nonempty union of complete first blocks, including a proper one. -/
theorem baseSector_component_entries (ϱ : ℝ) (aw : ℕ → ℝ)
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
    ∀ p q : I, A⁻¹ p.1 q.1 = A_U⁻¹ p q ∧
      sqrtMat A p.1 q.1 = sqrtMat A_U p q := by
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
  have hi : Nonempty I := by
    obtain ⟨z, hzU⟩ := hU0
    exact ⟨⟨(z, 0), hzU⟩⟩
  let : Nonempty I := hi
  let : Nonempty (G.Ω 1 × Fin N) := ⟨hi.some.1⟩
  obtain ⟨hblock, _, hRI, _, _⟩ :=
    baseSector_component_covariance ϱ aw regimeB ν δ₀ hδ h hh H hΛ1 θ φ hp
      U hU hU0 hη0 hη s hs hz
  have he : ∀ z : G.Ω 1, ∑ i, e z i ^ 2 = 1 :=
    baseSectorCenter_sq_sum ϱ aw regimeB ν h hh H θ
  have hα : ∀ z : G.Ω 1, ‖α z‖ ≤ 1 / (8 * (L : ℝ) ^ 2) :=
    baseSector_bgMult_norm_le_of_product_ne_zero ϱ aw regimeB ν δ₀ hδ h hh H hΛ1 θ φ hp
  have hR : ResOK A := resOK_baseOp G H.mass H.weights hα hη0 hη hs e he
  intro p q
  constructor
  · apply inv_submatrix_block P hblock
    · simpa using hR 0 le_rfl
    · simpa using hRI 0 le_rfl
  · exact sqrtMat_submatrix_block P hblock hR hRI p q

/-- The covariance and principal inverse square root of the physical cut component inherit
the volume-independent exponential decay of the ambient cut operator (BASE-KERNEL-3 (1.7)). -/
theorem baseSector_component_entries_decay (ϱ : ℝ) (aw : ℕ → ℝ)
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
    ∀ p q : I,
      ‖A_U⁻¹ p q‖ ≤ (baseCoercivity L / 4)⁻¹ *
          Real.exp (-baseDecayRate d L (if regimeB then ν else 0) * siteDist G p.1.1 q.1.1) ∧
      ‖sqrtMat A_U p q‖ ≤ Real.sqrt (4 / baseCoercivity L) *
          Real.exp (-baseDecayRate d L (if regimeB then ν else 0) * siteDist G p.1.1 q.1.1) := by
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
  have hi : Nonempty I := by
    obtain ⟨z, hzU⟩ := hU0
    exact ⟨⟨(z, 0), hzU⟩⟩
  let : Nonempty (G.Ω 1 × Fin N) := ⟨hi.some.1⟩
  have he : ∀ z : G.Ω 1, ∑ i, e z i ^ 2 = 1 :=
    baseSectorCenter_sq_sum ϱ aw regimeB ν h hh H θ
  have hα : ∀ z : G.Ω 1, ‖α z‖ ≤ 1 / (8 * (L : ℝ) ^ 2) :=
    baseSector_bgMult_norm_le_of_product_ne_zero ϱ aw regimeB ν δ₀ hδ h hh H hΛ1 θ φ hp
  have hid := baseSector_component_entries ϱ aw regimeB ν δ₀ hδ h hh H hΛ1 θ φ hp
    U hU hU0 hη0 hη s hs hz
  intro p q
  have hd₁ := baseResolvent_decay G H.mass H.weights hα hη0 hη hs e he
    (x := 0) le_rfl p.1.1 q.1.1
  have hd₂ := baseSqrt_decay G H.mass H.weights hα hη0 hη hs e he
    p.1.1 q.1.1
  constructor
  · calc ‖A_U⁻¹ p q‖ = ‖A⁻¹ p.1 q.1‖ := congrArg norm (hid p q).1.symm
      _ ≤ ‖blockOf A⁻¹ p.1.1 q.1.1‖ :=
        norm_entry_le_blockOf A⁻¹ p.1.1 q.1.1 p.1.2 q.1.2
      _ ≤ _ := by simpa [baseResolvent, A] using hd₁
  · calc ‖sqrtMat A_U p q‖ = ‖sqrtMat A p.1 q.1‖ := congrArg norm (hid p q).2.symm
      _ ≤ ‖blockOf (sqrtMat A) p.1.1 q.1.1‖ :=
        norm_entry_le_blockOf (sqrtMat A) p.1.1 q.1.1 p.1.2 q.1.2
      _ ≤ _ := hd₂

end Balaban.LargeField
