/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseChartCutSqrt
public import Balaban.LargeField.Base.BaseComponentDeterminant
public import Balaban.LargeField.Base.BaseComponentCovariance

/-!
# Real coordinate matrix of the selected cut operator

At a real cut parameter the cut operator `A(s)` of BASE-KERNEL-3 (1.3) is the
complexification of a real symmetric matrix, namely its entrywise real part.
This real matrix is positive definite on the whole fine torus and on every
principal block, and the principal square root of a component is the
complexification of the real inverse square root (P4 (2.47)–(2.54)).
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Background Balaban.Multiscale Balaban.Green
open Balaban.LargeField.Base Matrix Classical

/-- The base operator of a symmetric matrix with real entries and a real unit
background is the complexification of a real symmetric matrix. -/
theorem baseOp_exists_real {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}
    (e : ι → Fin N → ℝ) (H : Matrix ι ι ℂ) (hH : ∀ x y, (H x y).im = 0)
    (hs : ∀ x y, H x y = H y x) :
    ∃ K : Matrix (ι × Fin N) (ι × Fin N) ℝ, K.IsSymm ∧
      baseOp N (fun x i => (e x i : ℂ)) H = K.map (algebraMap ℝ ℂ) := by
  let Hr : Matrix ι ι ℝ := H.map Complex.re
  have hHr : H = Hr.map (algebraMap ℝ ℂ) := by
    ext x y
    apply Complex.ext
    · simp [Hr]
    · simp [hH x y]
  let Pr : Matrix (ι × Fin N) (ι × Fin N) ℝ := fun p q =>
    if p.1 = q.1 then e p.1 p.2 * e q.1 q.2 else 0
  let Lr : Matrix (ι × Fin N) (ι × Fin N) ℝ := fun p q =>
    if p.2 = q.2 then Hr p.1 q.1 else 0
  have hP : basePart (fun x i => (e x i : ℂ)) = Pr.map (algebraMap ℝ ℂ) := by
    ext p q
    rw [basePart_real, unitProj_apply]
    change _ = ((if p.1 = q.1 then e p.1 p.2 * e q.1 q.2 else 0 : ℝ) : ℂ)
    split_ifs <;> simp_all
  have hL : liftOp N H = Lr.map (algebraMap ℝ ℂ) := by
    ext p q
    change (if p.2 = q.2 then H p.1 q.1 else 0) =
      ((if p.2 = q.2 then Hr p.1 q.1 else 0 : ℝ) : ℂ)
    split_ifs
    · rw [hHr]; rfl
    · simp
  have hPs : Pr.IsSymm := by
    refine Matrix.IsSymm.ext fun p q => ?_
    simp only [Pr]
    by_cases h : p.1 = q.1
    · simp [h, mul_comm]
    · simp [h, Ne.symm h]
  have hLs : Lr.IsSymm := by
    refine Matrix.IsSymm.ext fun p q => ?_
    simp only [Lr]
    by_cases h : p.2 = q.2
    · have := hs p.1 q.1
      simp [h, Hr, this]
    · simp [h, Ne.symm h]
  refine ⟨(1 - Pr) * Lr * (1 - Pr) + Pr, ?_, ?_⟩
  · have hP' : Prᵀ = Pr := hPs
    have hL' : Lrᵀ = Lr := hLs
    show ((1 - Pr) * Lr * (1 - Pr) + Pr)ᵀ = _
    simp only [Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_sub,
      Matrix.transpose_one, hP', hL', Matrix.mul_assoc]
  · unfold baseOp
    rw [hP, hL]
    let F := (algebraMap ℝ ℂ).mapMatrix (m := ι × Fin N)
    change (1 - F Pr) * F Lr * (1 - F Pr) + F Pr =
      F ((1 - Pr) * Lr * (1 - Pr) + Pr)
    simp only [map_add, map_mul, map_sub, map_one]

section Physical

variable {d N L n : ℕ} [NeZero L] [NeZero n]

/-- At a real cut parameter the cut Hamiltonian of BASE-KERNEL-3 (1.2) has real
entries. -/
theorem baseHamiltonian_im_eq_zero {ϱ : ℝ} {N₀ : ℕ} [NeZero N₀]
    (G : GeneratingSet d L N₀ 1 ϱ) (a : ℕ → ℝ) (ν : ℝ) (α : G.Ω 1 → ℂ)
    (s : FineBond d L N₀ → ℂ) (hα : ∀ z, (α z).im = 0)
    (hs : ∀ b ∈ baseCutBonds G, (s b).im = 0) (x y : G.Ω 1) :
    (baseHamiltonian G a ν α s x y).im = 0 := by
  rw [baseHamiltonian_apply, Complex.add_im, Complex.add_im, Complex.im_sum,
    Complex.ofReal_im]
  have h1 : (if x = y then α x else 0).im = 0 := by
    split_ifs
    · exact hα x
    · simp
  have h2 : ∑ b ∈ baseCutBonds G, (s b * baseBond G b x y).im = 0 := by
    refine Finset.sum_eq_zero fun b hb => ?_
    rw [baseBond_apply, Complex.mul_im, hs b hb]
    simp
  rw [h1, h2]
  simp

/-- At a real selected cut parameter, the physical cut operator `A(s)` of
BASE-KERNEL-3 (1.3) is the complexification of its entrywise real part, which
is a real symmetric matrix. -/
theorem baseSector_selected_cut_real_matrix (ϱ : ℝ) (aw : ℕ → ℝ)
    (regimeB : Prop) (ν δ₀ : ℝ) (hδ : 0 < δ₀)
    (h : EuclideanSpace ℝ (Fin N)) (hh : ‖h‖ = 1)
    (H : BgHyp d L 1 ϱ aw (if regimeB then ν else 0))
    (hΛ1 : 4 * d * L * δ₀ ≤ bgC1 d L N)
    (θ : Torus d n → EuclideanSpace ℝ (Fin N)) (φ : CfgT d N L n)
    (hp : baseSectorCubeProduct regimeB ν δ₀ h θ φ ≠ 0)
    (s : FineBond d L (1 * n) → ℂ)
    (hsr : ∀ b ∈ baseCutBonds (GeneratingSet.single (d := d) (L := L)
      (N₀ := 1 * n) (k := 1) ϱ), (s b).im = 0) :
    let G : GeneratingSet d L (1 * n) 1 ϱ := GeneratingSet.single ϱ
    let α := bgMult G aw (if regimeB then ν else 0) (baseSectorDatum ϱ θ h)
    let e : G.Ω 1 → Fin N → ℝ := fun z i =>
      (baseSectorCenter ϱ aw regimeB ν h θ
        (baseSector_side L n ▸ (z : Torus d (1 * n * L ^ 1))) i : ℝ)
    let A := baseOp N (fun z i => (e z i : ℂ))
      (baseHamiltonian G aw (if regimeB then ν else 0) α s)
    (A.map Complex.re).IsSymm ∧
      (A.map Complex.re).map (algebraMap ℝ ℂ) = A := by
  dsimp only
  have hα : ∀ z, (bgMult (GeneratingSet.single (d := d) (L := L)
      (N₀ := 1 * n) (k := 1) ϱ) aw (if regimeB then ν else 0)
      (baseSectorDatum ϱ θ h) z).im = 0 :=
    baseSector_bgMult_real_of_product_ne_zero ϱ aw regimeB ν δ₀ hδ h hh H hΛ1 θ φ hp
  obtain ⟨K, hKs, hK⟩ := baseOp_exists_real
    (fun z i => (baseSectorCenter ϱ aw regimeB ν h θ
        (baseSector_side L n ▸ (z : Torus d (1 * n * L ^ 1))) i : ℝ))
    (baseHamiltonian (GeneratingSet.single (d := d) (L := L)
      (N₀ := 1 * n) (k := 1) ϱ) aw (if regimeB then ν else 0)
      (bgMult (GeneratingSet.single (d := d) (L := L)
        (N₀ := 1 * n) (k := 1) ϱ) aw (if regimeB then ν else 0)
        (baseSectorDatum ϱ θ h)) s)
    (baseHamiltonian_im_eq_zero _ _ _ _ s hα hsr)
    (baseHamiltonian_symm _ _ _ _ s)
  rw [hK]
  have hmap : (K.map (algebraMap ℝ ℂ)).map Complex.re = K := by
    ext p q
    simp
  rw [hmap]
  exact ⟨hKs, rfl⟩

/-- A coercive complexified real symmetric matrix and both of its principal blocks
(for a predicate on the index) have positive definite real matrices. -/
theorem posDef_blocks_of_real_coercive {κ : Type*} [Fintype κ] [DecidableEq κ]
    (A : Matrix κ κ ℂ) (hsym : (A.map Complex.re).IsSymm)
    (hmap : (A.map Complex.re).map (algebraMap ℝ ℂ) = A) {γ : ℝ} (hγ : 0 < γ)
    (hA : IsCoercive A γ) (P : κ → Prop) :
    let vI : {p // P p} → κ := Subtype.val
    let vJ : {p // ¬ P p} → κ := Subtype.val
    (A.map Complex.re).PosDef ∧
      ((A.submatrix vI vI).map Complex.re).PosDef ∧
      ((A.submatrix vJ vJ).map Complex.re).PosDef ∧
      ((A.submatrix vI vI).map Complex.re).map (algebraMap ℝ ℂ) = A.submatrix vI vI ∧
      ((A.submatrix vJ vJ).map Complex.re).map (algebraMap ℝ ℂ) = A.submatrix vJ vJ := by
  intro vI vJ
  have hA' : IsCoercive ((A.map Complex.re).map (algebraMap ℝ ℂ)) γ := by
    rw [hmap]; exact hA
  have hI : IsCoercive (A.submatrix vI vI) γ :=
    isCoercive_submatrix hA vI Subtype.val_injective
  have hJ : IsCoercive (A.submatrix vJ vJ) γ :=
    isCoercive_submatrix hA vJ Subtype.val_injective
  have hmI : ((A.submatrix vI vI).map Complex.re).map (algebraMap ℝ ℂ) =
      A.submatrix vI vI := by
    ext i j
    exact congrFun (congrFun hmap (vI i)) (vI j)
  have hmJ : ((A.submatrix vJ vJ).map Complex.re).map (algebraMap ℝ ℂ) =
      A.submatrix vJ vJ := by
    ext i j
    exact congrFun (congrFun hmap (vJ i)) (vJ j)
  refine ⟨real_posDef_of_complex_coercive _ hsym _ hγ hA',
    real_posDef_of_complex_coercive _ (hsym.submatrix vI) _ hγ (by rw [hmI]; exact hI),
    real_posDef_of_complex_coercive _ (hsym.submatrix vJ) _ hγ (by rw [hmJ]; exact hJ),
    hmI, hmJ⟩

/-- At a real selected cut parameter in the coercive neighbourhood, the real
coordinate matrix of the cut operator is positive definite, and so are the real
matrices of the principal blocks of a first-block union and its complement. Each
block matrix complexifies to the corresponding principal submatrix. -/
theorem baseSector_selected_cut_component_posDef (ϱ : ℝ) (aw : ℕ → ℝ)
    (regimeB : Prop) (ν δ₀ : ℝ) (hδ : 0 < δ₀)
    (h : EuclideanSpace ℝ (Fin N)) (hh : ‖h‖ = 1)
    (H : BgHyp d L 1 ϱ aw (if regimeB then ν else 0))
    (hΛ1 : 4 * d * L * δ₀ ≤ bgC1 d L N)
    (θ : Torus d n → EuclideanSpace ℝ (Fin N)) (φ : CfgT d N L n)
    (hp : baseSectorCubeProduct regimeB ν δ₀ h θ φ ≠ 0)
    (U : Set (Torus d (1 * n * L ^ 1)))
    {η : ℝ} (hη0 : 0 ≤ η)
    (hη : η ≤ baseCoercivity L / (8 * d))
    (s : FineBond d L (1 * n) → ℂ)
    (hs : s ∈ baseParamNbhd (GeneratingSet.single (d := d) (L := L)
      (N₀ := 1 * n) (k := 1) ϱ) η)
    (hsr : ∀ b ∈ baseCutBonds (GeneratingSet.single (d := d) (L := L)
      (N₀ := 1 * n) (k := 1) ϱ), (s b).im = 0) :
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
    (A.map Complex.re).PosDef ∧ (A_U.map Complex.re).PosDef ∧
      (A_V.map Complex.re).PosDef ∧
      (A_U.map Complex.re).map (algebraMap ℝ ℂ) = A_U ∧
      (A_V.map Complex.re).map (algebraMap ℝ ℂ) = A_V := by
  dsimp only
  have hreal := baseSector_selected_cut_real_matrix ϱ aw regimeB ν δ₀ hδ h hh H
    hΛ1 θ φ hp s hsr
  dsimp only at hreal
  obtain ⟨hsym, hmap⟩ := hreal
  let G : GeneratingSet d L (1 * n) 1 ϱ := GeneratingSet.single ϱ
  let α := bgMult G aw (if regimeB then ν else 0) (baseSectorDatum ϱ θ h)
  let e : G.Ω 1 → Fin N → ℝ := fun z i =>
    (baseSectorCenter ϱ aw regimeB ν h θ
      (baseSector_side L n ▸ (z : Torus d (1 * n * L ^ 1))) i : ℝ)
  let A := baseOp N (fun z i => (e z i : ℂ))
    (baseHamiltonian G aw (if regimeB then ν else 0) α s)
  have he : ∀ z : G.Ω 1, ∑ i, e z i ^ 2 = 1 :=
    baseSectorCenter_sq_sum ϱ aw regimeB ν h hh H θ
  have hα : ∀ z : G.Ω 1, ‖α z‖ ≤ 1 / (8 * (L : ℝ) ^ 2) :=
    baseSector_bgMult_norm_le_of_product_ne_zero ϱ aw regimeB ν δ₀ hδ h hh H hΛ1 θ φ hp
  have hcoer : Green.IsCoercive A (baseCoercivity L / 2) :=
    baseOp_isCoercive_of_close G H.mass H.weights hα hη0 hη hs e he
  have hc : 0 < baseCoercivity L / 2 :=
    half_pos (baseCoercivity_pos (Nat.pos_of_ne_zero (NeZero.ne L)))
  exact posDef_blocks_of_real_coercive A hsym hmap hc hcoer
    (fun p : G.Ω 1 × Fin N => (p.1 : Torus d (1 * n * L ^ 1)) ∈ U)

end Physical

end Balaban.LargeField
