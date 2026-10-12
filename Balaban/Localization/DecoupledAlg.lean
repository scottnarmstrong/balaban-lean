/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.BoxGeometry

/-!
# The parametrix identity (LOCALIZATION.md §1.3)

* `cubeH_isUnit`: the Neumann cube operator `H_z(A)` is invertible (NC1);
* `cubeG_supp`: `G^{(z)}(A) c_z f` is supported in `□_z`;
* `cubeH_cubeG`: `H_z G^{(z)} c_z = c_z`;
* `chiD_dirichlet_cubeG`: `χ_z H_D G^{(z)} c_z = χ_z` (at a point of `supp χ_z` the rows of `H_D` and
  `H_z` agree and the source is untouched by `c_z`);
* `sum_chiD`: `∑_z χ_z = 1` on `Ω₁`;
* `parametrix`: `H_D(A) G*_1(A) = 1 - 𝒦_1(A)`.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Finset Matrix

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ} {α : G.Ω 1 → ℂ}

theorem matrix_ext_mulVec {ι : Type*} [Fintype ι] [DecidableEq ι] {M N : Matrix ι ι ℂ}
    (h : ∀ f : ι → ℂ, M *ᵥ f = N *ᵥ f) : M = N :=
  Matrix.toLin'.injective (LinearMap.ext h)

theorem cD_mulVec (q : ℕ × CTorus d L N₁ m₁ K) (f : G.Ω 1 → ℂ) (x : G.Ω 1) :
    (cD G q *ᵥ f) x = if (x : CTorus d L N₁ m₁ K) ∈ box q then f x else 0 := by
  classical
  unfold cD
  rw [Matrix.mulVec_diagonal]
  split_ifs <;> simp

theorem chiD_mulVec (q : ℕ × CTorus d L N₁ m₁ K) (f : G.Ω 1 → ℂ) (x : G.Ω 1) :
    (chiD G q *ᵥ f) x = ((chi G q x : ℝ) : ℂ) * f x := by
  unfold chiD
  rw [Matrix.mulVec_diagonal]

/-! ### Interior points -/

omit [NeZero N₁] [NeZero L] in
theorem intTorus_zero_aux {m : ℕ} : (intTorus (0 : Fin d → ℤ) : Torus d m) = 0 := by
  funext μ; simp [intTorus_apply]

omit [NeZero N₁] [NeZero L] in
theorem intTorus_single_aux (μ : Fin d) (c : ℤ) {m : ℕ} :
    (intTorus (Pi.single μ c) : Torus d m) = Pi.single μ (c : ZMod m) := by
  funext ν
  by_cases h : ν = μ
  · subst h; simp [intTorus_apply]
  · simp [intTorus_apply, h]

theorem Inner.self {q : ℕ × CTorus d L N₁ m₁ K} {x : CTorus d L N₁ m₁ K} (h : Inner q x) :
    x ∈ box q := by
  simpa [intTorus_zero_aux] using h 0 (fun μ => by simp)

theorem Inner.add_single {q : ℕ × CTorus d L N₁ m₁ K} {x : CTorus d L N₁ m₁ K} (h : Inner q x)
    (μ : Fin d) : x + Pi.single μ 1 ∈ box q := by
  have := h (Pi.single μ 1) (fun ν => by
    by_cases hν : ν = μ <;> simp [hν])
  simpa [intTorus_single_aux] using this

theorem Inner.sub_single {q : ℕ × CTorus d L N₁ m₁ K} {x : CTorus d L N₁ m₁ K} (h : Inner q x)
    (μ : Fin d) : x - Pi.single μ 1 ∈ box q := by
  have := h (Pi.single μ (-1)) (fun ν => by
    by_cases hν : ν = μ <;> simp [hν])
  have e : (intTorus (Pi.single μ (-1 : ℤ)) : CTorus d L N₁ m₁ K) = -Pi.single μ 1 := by
    funext ν
    by_cases hν : ν = μ <;> simp [intTorus_apply, hν]
  rw [e, ← sub_eq_add_neg] at this
  exact this

theorem Inner.sub_add_single {q : ℕ × CTorus d L N₁ m₁ K} {x : CTorus d L N₁ m₁ K}
    (h : Inner q x) (μ ν : Fin d) : x - Pi.single μ 1 + Pi.single ν 1 ∈ box q := by
  have := h (Pi.single ν 1 - Pi.single μ 1) (fun ρ => by
    simp only [Pi.sub_apply, Pi.single_apply]
    split_ifs <;> norm_num)
  have e : x + (intTorus (Pi.single ν (1 : ℤ) - Pi.single μ 1) : CTorus d L N₁ m₁ K) =
      x - Pi.single μ 1 + Pi.single ν 1 := by
    funext ρ
    simp only [Pi.add_apply, Pi.sub_apply, intTorus_apply, Pi.single_apply]
    split_ifs <;> push_cast <;> ring
  rwa [e] at this

theorem Inner.noCut {q : ℕ × CTorus d L N₁ m₁ K} {x : CTorus d L N₁ m₁ K} (h : Inner q x) :
    NoCutAt (cubeCut G (box q)) x :=
  noCutAt_cubeCut (box q) h.self fun μ => ⟨h.add_single μ, h.sub_single μ⟩

/-- The interior points contain the support of `χ_z`. -/
theorem inner_of_chi_ne_zero (S : DGSetting G a ν) {q : ℕ × CTorus d L N₁ m₁ K}
    (hq : q ∈ cubeIdx G) {x : CTorus d L N₁ m₁ K} (hx : x ∈ G.Ω 1) (h : chi G q x ≠ 0) :
    Inner q x := by
  obtain ⟨hn1, hnK, hxl⟩ := G.layerIndex_spec hx
  exact inner_of_near S.cover_sep S.hM (by have := S.hL; omega) hq hn1 hnK hxl (inBox_of_chi_ne_zero h)
    (Or.inr (SameCell.refl _ _))

/-! ### The cube operator -/

theorem cubeH_isUnit (S : DGSetting G a ν) (hα : AdmPot G α) {q : ℕ × CTorus d L N₁ m₁ K}
    (hq : q ∈ cubeIdx G) : IsUnit (cubeH G a ν α q) :=
  cutOperator_isUnit G (cubeCut_aligned G (box_blockAligned S.aligned S.cover_sep (by have := S.hL; omega) hq))
    (by have := S.hd; omega) S.mass S.weights α hα

theorem cubeG_mulVec (q : ℕ × CTorus d L N₁ m₁ K) (f : G.Ω 1 → ℂ) :
    cubeG G a ν α q *ᵥ f = (cubeH G a ν α q)⁻¹ *ᵥ (cD G q *ᵥ f) := by
  unfold cubeG
  rw [Matrix.mulVec_mulVec]

/-- **`G^{(z)}(A) c_z f` is supported in the interaction cube.** -/
theorem cubeG_supp (S : DGSetting G a ν) (hα : AdmPot G α) {q : ℕ × CTorus d L N₁ m₁ K}
    (hq : q ∈ cubeIdx G) (f : G.Ω 1 → ℂ) (z : G.Ω 1) (hz : (z : CTorus d L N₁ m₁ K) ∉ box q) :
    (cubeG G a ν α q *ᵥ f) z = 0 := by
  have hU := cubeH_isUnit S hα hq
  have hdet := (Matrix.isUnit_iff_isUnit_det _).1 hU
  have hH : cubeH G a ν α q *ᵥ (cubeG G a ν α q *ᵥ f) = cD G q *ᵥ f := by
    rw [cubeG_mulVec, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  exact cutOperator_inv_supported G (box_blockAligned S.aligned S.cover_sep (by have := S.hL; omega) hq) α hU
    (f := cD G q *ᵥ f) (fun w hw => by rw [cD_mulVec]; simp [hw]) hH z hz

theorem cubeH_cubeG (S : DGSetting G a ν) (hα : AdmPot G α) {q : ℕ × CTorus d L N₁ m₁ K}
    (hq : q ∈ cubeIdx G) (f : G.Ω 1 → ℂ) :
    cubeH G a ν α q *ᵥ (cubeG G a ν α q *ᵥ f) = cD G q *ᵥ f := by
  have hdet := (Matrix.isUnit_iff_isUnit_det _).1 (cubeH_isUnit S hα hq)
  rw [cubeG_mulVec, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]

/-- **`χ_z H_D G^{(z)} c_z = χ_z`.** -/
theorem chiD_dirichlet_cubeG (S : DGSetting G a ν) (hα : AdmPot G α) {q : ℕ × CTorus d L N₁ m₁ K}
    (hq : q ∈ cubeIdx G) :
    chiD G q * dirichletOperator G a ν α * cubeG G a ν α q = chiD G q := by
  refine matrix_ext_mulVec fun f => ?_
  funext x
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, chiD_mulVec, chiD_mulVec]
  by_cases h0 : chi G q x = 0
  · simp [h0]
  · have hin := inner_of_chi_ne_zero S hq x.2 h0
    have hrow := dirichlet_row_eq_cut_row a ν α (cut := cubeCut G (box q)) hin.noCut
      (cubeG G a ν α q *ᵥ f)
    have h1 := cubeH_cubeG S hα hq f
    have h2 := congrFun h1 x
    simp only [cD_mulVec, hin.self, ite_true] at h2
    change ((chi G q x : ℝ) : ℂ) * (dirichletOperator G a ν α *ᵥ (cubeG G a ν α q *ᵥ f)) x = _
    rw [hrow]
    unfold cubeH at h2
    rw [h2]

theorem sum_chiD (hd : 0 < d) (hL : 2 ≤ L) (hG : CubeAligned G m₁) :
    ∑ q ∈ cubeIdx G, chiD G q = 1 := by
  ext x y
  rw [Matrix.sum_apply]
  unfold chiD
  simp only [Matrix.diagonal_apply]
  by_cases hxy : x = y
  · subst hxy
    obtain ⟨hn1, hnK, hxl⟩ := G.layerIndex_spec x.2
    simp only [ite_true, Matrix.one_apply_eq]
    rw [← Complex.ofReal_sum, sum_chi hG hL hn1 hnK hxl ⟨0, hd⟩, Complex.ofReal_one]
  · simp [hxy]

/-- **The parametrix identity** `H_D(A) G*_1(A) = 1 - 𝒦_1(A)` (LOCALIZATION.md §1.3). -/
theorem parametrix (S : DGSetting G a ν) (hα : AdmPot G α) :
    dirichletOperator G a ν α * Gstar G a ν α (fun _ => 1) = 1 - Kcal G a ν α (fun _ => 1) :=
  parametrix_algebra a ν α (fun q hq => chiD_dirichlet_cubeG S hα hq)
    (sum_chiD (by have := S.hd; omega) (by have := S.hL; omega) S.aligned)

end Balaban.Localization
