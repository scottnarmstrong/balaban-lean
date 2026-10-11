/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.DomainDifference
public import Balaban.Green.InfiniteVolume
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity


/-!
# Cauchy property of inverses on growing tori (G-5, uniqueness of the limit)

Let `A_j` be coercive operators on the tori `(ℤ/s_j ℤ)^d`, `s_j → ∞`, with entries decaying
exponentially uniformly in `j`, whose entries on the images of the cube `{|u_μ| ≤ R} ⊂ ℤ^d`
(`Balaban.Green.castTorus`) form Cauchy families as `j → ∞` for every `R`.  Then the entries of the
inverses `A_j⁻¹` on the same images are Cauchy (`Balaban.Green.cauchy_inv_entries`).

Proof (the route of GREEN.md G-5(b), F-18): on each torus the inverse differs from the Dirichlet
Green function of the image of a cube by an error `e^{-c (R - R₀)}`
(`Balaban.Green.inv_sub_boxGreen_le`, the domain difference
`Balaban.Green.inv_sub_greenFn_le`); the Dirichlet Green functions of the cubes are inverses of
the matrices `(A_j(u, u'))_{u,u' ∈ cube}` indexed by the *same* finite set, which are uniformly
coercive and close, so their inverses are close (`Balaban.Green.entry_diff_le`).
-/

@[expose] public section

open Matrix Finset

namespace Balaban.Green

section Abstract

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem greenFn_univ (A : Matrix ι ι ℂ) (t : ℂ) (x y : ι) :
    greenFn A t Finset.univ x y = (A + t • (1 : Matrix ι ι ℂ))⁻¹ x y := by
  have h : x ∈ (Finset.univ : Finset ι) ∧ y ∈ (Finset.univ : Finset ι) :=
    ⟨mem_univ _, mem_univ _⟩
  simp only [greenFn, h, and_self, ↓reduceDIte]
  let e : (Finset.univ : Finset ι) ≃ ι := Equiv.subtypeUnivEquiv mem_univ
  have : restrictOp A Finset.univ + t • (1 : Matrix (Finset.univ : Finset ι) _ ℂ) =
      (A + t • (1 : Matrix ι ι ℂ)).submatrix e e := by
    ext a b
    simp only [Matrix.add_apply, Matrix.smul_apply, restrictOp, Matrix.submatrix_apply,
      Matrix.one_apply, e, Equiv.subtypeUnivEquiv_apply, Subtype.ext_iff]
  rw [this, Matrix.inv_submatrix_equiv]
  rfl


section Metric

variable [PseudoMetricSpace ι]

/-- The inverse of a coercive matrix differs from its Dirichlet restriction to `Λ'` by an
exponentially small error at points far from the complement of `Λ'`. -/
theorem inv_sub_greenFn_le {A : Matrix ι ι ℂ} {c₀ δ₀ γ₀ κ κ' : ℝ} (hc : 0 ≤ c₀) (hδ : 0 < δ₀)
    (hγ : 0 < γ₀) (hκ : 0 ≤ κ) (hκ' : 0 ≤ κ')
    (hA : ∀ x y, ‖A x y‖ ≤ c₀ * Real.exp (-δ₀ * dist x y))
    (hK : ∀ x : ι, ∑ y, Real.exp (-(δ₀ / 4) * dist x y) ≤ κ)
    (hK' : ∀ x : ι, ∑ y, Real.exp (-(min (ctRate c₀ δ₀ γ₀ κ) δ₀ / 2) * dist x y) ≤ κ')
    (hcoer : IsCoercive A γ₀) (Λ' : Finset ι) {x₁ x₂ : ι} (hx₂ : x₂ ∈ Λ') {r₁ r₂ : ℝ}
    (h₁ : ∀ z, z ∉ Λ' → r₁ ≤ dist x₁ z) (h₂ : ∀ z, z ∉ Λ' → r₂ ≤ dist x₂ z) :
    ‖A⁻¹ x₁ x₂ - greenFn A 0 Λ' x₁ x₂‖ ≤ 4 * c₀ * κ' * κ' / γ₀ ^ 2 *
      Real.exp (-(min (ctRate c₀ δ₀ γ₀ κ) δ₀ / 2) * (r₁ + r₂)) := by
  have hg : A⁻¹ x₁ x₂ = greenFn A 0 Finset.univ x₁ x₂ := by
    rw [greenFn_univ]; simp
  have hμ : 0 ≤ min (ctRate c₀ δ₀ γ₀ κ) δ₀ / 2 :=
    div_nonneg (le_min (ctRate_pos hc hδ hγ hκ).le hδ.le) (by norm_num)
  have hK0 : 0 ≤ 4 * c₀ * κ' * κ' / γ₀ ^ 2 := by positivity
  by_cases hne' : (Finset.univ \ Λ' : Finset ι).Nonempty
  · have hne : ((Finset.univ \ Λ' : Finset ι) : Set ι).Nonempty := Finset.coe_nonempty.2 hne'
    have hdd := domain_difference hc hδ hγ hκ hκ' hA hK hK' hcoer
      (Finset.subset_univ Λ') (le_refl (0 : ℝ)) (x₁ := x₁) hx₂
    simp only [Complex.ofReal_zero, add_zero] at hdd
    rw [hg]
    refine hdd.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hK0)
    have e1 : r₁ ≤ setDist (↑(Finset.univ \ Λ') : Set ι) x₁ := by
      rw [setDist, Metric.le_infDist hne]
      intro z hz
      exact h₁ z (by simpa using hz)
    have e2 : r₂ ≤ setDist (↑(Finset.univ \ Λ') : Set ι) x₂ := by
      rw [setDist, Metric.le_infDist hne]
      intro z hz
      exact h₂ z (by simpa using hz)
    nlinarith [mul_le_mul_of_nonneg_left (add_le_add e1 e2) hμ]
  · have hempty : Finset.univ \ Λ' = ∅ := Finset.not_nonempty_iff_eq_empty.1 hne'
    have hΛ : Λ' = Finset.univ := by
      have := Finset.sdiff_eq_empty_iff_subset.1 hempty
      exact (Finset.eq_univ_of_forall fun x => this (Finset.mem_univ x))
    rw [hg, hΛ, sub_self, norm_zero]
    positivity

end Metric

section Coercive

variable {κ : Type*} [Fintype κ]

/-- Compression of a coercive matrix to the image of an injective map. -/
theorem isCoercive_submatrix {A : Matrix ι ι ℂ} {γ : ℝ} (h : IsCoercive A γ) (f : κ → ι)
    (hf : Function.Injective f) : IsCoercive (A.submatrix f f) γ := by
  intro v
  set W : ι → ℂ := Function.extend f v 0 with hW
  have hWf : ∀ k, W (f k) = v k := fun k => hf.extend_apply v 0 k
  have hW0 : ∀ i, i ∉ Set.range f → W i = 0 := fun i hi => by
    simp [hW, Function.extend_apply' _ _ _ (by simpa using hi)]
  have hsum : ∀ g : ι → ℂ, (∀ i, i ∉ Set.range f → g i = 0) → ∑ i, g i = ∑ k, g (f k) := by
    intro g hg
    rw [← Finset.sum_image (f := g) (g := f) (s := Finset.univ) (fun a _ b _ h => hf h)]
    symm
    refine Finset.sum_subset (Finset.subset_univ _) fun i _ hi => hg i ?_
    intro hr
    obtain ⟨k, rfl⟩ := hr
    exact hi (Finset.mem_image_of_mem _ (Finset.mem_univ k))
  have hN : sqNorm W = sqNorm v := by
    unfold sqNorm
    have := hsum (fun i => ((‖W i‖ ^ 2 : ℝ) : ℂ)) (fun i hi => by simp [hW0 i hi])
    have h2 : ∑ i, ‖W i‖ ^ 2 = ∑ k, ‖W (f k)‖ ^ 2 := by exact_mod_cast this
    rw [h2]
    exact Finset.sum_congr rfl fun k _ => by rw [hWf]
  have hQ : reQuad A W = reQuad (A.submatrix f f) v := by
    unfold reQuad
    congr 1
    rw [hsum (fun i => star (W i) * (A *ᵥ W) i) (fun i hi => by simp [hW0 i hi])]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hWf]
    congr 1
    simp only [Matrix.mulVec, dotProduct]
    rw [hsum (fun j => A (f k) j * W j) (fun j hj => by simp [hW0 j hj])]
    exact Finset.sum_congr rfl fun j _ => by simp [hWf]
  have := h W
  rw [hN, hQ] at this
  exact this

end Coercive

section MatrixDiff

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- Perturbation of right inverses of coercive matrices, entrywise. -/
theorem entry_diff_le {T₁ T₂ G₁ G₂ : Matrix κ κ ℂ} {γ ε : ℝ} (hγ : 0 < γ)
    (h1 : IsCoercive T₁ γ) (h2 : IsCoercive T₂ γ) (e1 : T₁ * G₁ = 1) (e2 : T₂ * G₂ = 1)
    (hε : ∀ a b, ‖T₁ a b - T₂ a b‖ ≤ ε) (x y : κ) :
    ‖G₁ x y - G₂ x y‖ ≤ (Fintype.card κ : ℝ) ^ 2 * ε * (γ⁻¹) ^ 2 := by
  have e1' : G₁ * T₁ = 1 := mul_eq_one_comm.1 e1
  have hid : G₁ - G₂ = G₁ * (T₂ - T₁) * G₂ := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, e2, Matrix.mul_one, e1', Matrix.one_mul]
  have hentry : (G₁ - G₂) x y = ∑ a, ∑ b, G₁ x a * (T₂ - T₁) a b * G₂ b y := by
    rw [hid]
    simp only [Matrix.mul_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
  rw [Matrix.sub_apply] at hentry
  rw [hentry]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ a : κ, ‖∑ b, G₁ x a * (T₂ - T₁) a b * G₂ b y‖ ≤ ∑ _b : κ, γ⁻¹ * ε * γ⁻¹ := by
    intro a
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
    rw [norm_mul, norm_mul]
    have g1 := norm_entry_le_of_mul_eq_one hγ h1 e1 x a
    have g2 := norm_entry_le_of_mul_eq_one hγ h2 e2 b y
    have d1 : ‖(T₂ - T₁) a b‖ ≤ ε := by
      rw [Matrix.sub_apply, norm_sub_rev]; exact hε a b
    have h0 : 0 ≤ ‖(T₂ - T₁) a b‖ := norm_nonneg _
    have hγi : 0 < γ⁻¹ := inv_pos.2 hγ
    have hε0 : 0 ≤ ε := h0.trans d1
    gcongr
  refine (Finset.sum_le_sum fun a _ => hterm a).trans ?_
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have : (Fintype.card κ : ℝ) * ((Fintype.card κ : ℝ) * (γ⁻¹ * ε * γ⁻¹)) =
      (Fintype.card κ : ℝ) ^ 2 * ε * (γ⁻¹) ^ 2 := by ring
  exact this.le

end MatrixDiff

end Abstract

/-! ### Boxes of `ℤ^d` in the tori -/

section Torus

variable {d : ℕ}

/-- The cube `{u ∈ ℤ^d : |u_μ| ≤ R}`. -/
def sqBox (d R : ℕ) : Finset (Fin d → ℤ) := Fintype.piFinset fun _ => Finset.Icc (-(R : ℤ)) R

theorem mem_sqBox {R : ℕ} {u : Fin d → ℤ} : u ∈ sqBox d R ↔ ∀ μ, |u μ| ≤ R := by
  simp [sqBox, Fintype.mem_piFinset, abs_le]

theorem sqBox_mono {R₀ R : ℕ} (h : R₀ ≤ R) : sqBox d R₀ ⊆ sqBox d R := by
  intro u hu
  rw [mem_sqBox] at hu ⊢
  intro μ
  exact (hu μ).trans (by exact_mod_cast h)

/-- The cast `ℤ^d → (ℤ/sℤ)^d` is injective on a cube small compared with `s`. -/
theorem castTorus_injOn_sqBox {R s : ℕ} (hs : 2 * R < s) :
    Set.InjOn (castTorus (d := d) s) (sqBox d R : Set (Fin d → ℤ)) := by
  intro u hu u' hu' h
  funext μ
  have h1 := mem_sqBox.1 (Finset.mem_coe.1 hu) μ
  have h2 := mem_sqBox.1 (Finset.mem_coe.1 hu') μ
  have hc : ((u μ : ℤ) : ZMod s) = ((u' μ : ℤ) : ZMod s) := congrFun h μ
  have hdvd := (ZMod.intCast_eq_intCast_iff_dvd_sub (u μ) (u' μ) s).1 hc
  have hlt : |u' μ - u μ| < s := by
    rw [abs_lt] at *
    rw [abs_le] at h1 h2
    have : (2 * R : ℤ) < s := by exact_mod_cast hs
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have := Int.eq_zero_of_abs_lt_dvd hdvd hlt
  linarith

theorem exists_far_coord {R s : ℕ} [NeZero s] {z : Torus d s}
    (hz : z ∉ (sqBox d R).image (castTorus s)) : ∃ μ, R + 1 ≤ (cycRep (z μ)).natAbs := by
  by_contra hcon
  push Not at hcon
  refine hz (Finset.mem_image.2 ⟨fun μ => cycRep (z μ), ?_, ?_⟩)
  · rw [mem_sqBox]
    intro μ
    have := hcon μ
    rw [Int.abs_eq_natAbs]
    exact_mod_cast Nat.lt_succ_iff.1 this
  · funext μ
    exact cast_cycRep _

/-- Points outside the image of the cube `R` are far from the image of a smaller cube. -/
theorem le_torusDist_of_not_mem {R R₀ s : ℕ} [NeZero s] (hs : 2 * R₀ < s) {u : Fin d → ℤ}
    (hu : u ∈ sqBox d R₀) {z : Torus d s} (hz : z ∉ (sqBox d R).image (castTorus s)) :
    (R : ℝ) + 1 - R₀ ≤ torusDist d s (castTorus s u) z := by
  obtain ⟨μ, hμ⟩ := exists_far_coord hz
  have hu' := mem_sqBox.1 hu μ
  have hsmall : 2 * (u μ).natAbs < s := by
    have : (u μ).natAbs ≤ R₀ := by
      rw [Int.abs_eq_natAbs] at hu'; exact_mod_cast hu'
    omega
  have hc : cycRep ((castTorus s u) μ) = u μ := cycRep_intCast_of_small _ hsmall
  have h1 := natAbs_cycRep_add_le (z μ - castTorus s u μ) (castTorus s u μ)
  rw [sub_add_cancel, hc] at h1
  have h2 : (cycRep (castTorus s u μ - z μ)).natAbs = (cycRep (z μ - castTorus s u μ)).natAbs := by
    rw [← natAbs_cycRep_neg, neg_sub]
  have h3 : (u μ).natAbs ≤ R₀ := by
    rw [Int.abs_eq_natAbs] at hu'; exact_mod_cast hu'
  have h4 : (cycRep (castTorus s u μ - z μ)).natAbs ≥ R + 1 - R₀ := by omega
  have h5 : ((cycRep (castTorus s u μ - z μ)).natAbs : ℝ) ≤ torusDist d s (castTorus s u) z :=
    Finset.single_le_sum (f := fun i => ((cycRep (castTorus s u i - z i)).natAbs : ℝ))
      (fun _ _ => Nat.cast_nonneg _) (Finset.mem_univ μ)
  have h6 : ((R : ℝ) + 1 - R₀) ≤ ((cycRep (castTorus s u μ - z μ)).natAbs : ℝ) := by
    have : ((R + 1 : ℕ) : ℝ) - R₀ ≤ ((cycRep (castTorus s u μ - z μ)).natAbs : ℝ) := by
      have h7 : R + 1 ≤ (cycRep (castTorus s u μ - z μ)).natAbs + R₀ := by omega
      have h8 : ((R + 1 : ℕ) : ℝ) ≤ ((cycRep (castTorus s u μ - z μ)).natAbs : ℝ) + R₀ := by
        exact_mod_cast h7
      linarith
    push_cast at this
    exact this
  exact h6.trans h5

/-- The cast `ℤ^d → (ℤ/sℤ)^d`, as a site of the `ℓ¹` torus. -/
def castL1 (s : ℕ) (u : Fin d → ℤ) : L1Torus d s := castTorus s u

theorem castL1_injOn {R s : ℕ} (hs : 2 * R < s) :
    Set.InjOn (castL1 (d := d) s) (sqBox d R : Set (Fin d → ℤ)) :=
  castTorus_injOn_sqBox hs

/-- The complexification of a real matrix on the torus, as a matrix on the `ℓ¹` torus. -/
noncomputable def cplxOp {s : ℕ} [NeZero s] (A : Matrix (Torus d s) (Torus d s) ℝ) :
    Matrix (L1Torus d s) (L1Torus d s) ℂ := A.map (algebraMap ℝ ℂ)

/-- The image of the cube `R` in the torus of side `s`. -/
noncomputable def boxImage (d s R : ℕ) [NeZero s] : Finset (L1Torus d s) :=
  (sqBox d R).image (castL1 s)

/-- The operator restricted to the cube, indexed by the cube. -/
noncomputable def boxMat {s : ℕ} [NeZero s] (A : Matrix (Torus d s) (Torus d s) ℝ) (R : ℕ) :
    Matrix (sqBox d R) (sqBox d R) ℂ :=
  Matrix.of fun u u' => cplxOp A (castL1 s u) (castL1 s u')

/-- The Dirichlet Green function of the cube, indexed by the cube. -/
noncomputable def boxGreen {s : ℕ} [NeZero s] (A : Matrix (Torus d s) (Torus d s) ℝ) (R : ℕ) :
    Matrix (sqBox d R) (sqBox d R) ℂ :=
  Matrix.of fun u u' => greenFn (cplxOp A) 0 (boxImage d s R) (castL1 s u) (castL1 s u')

theorem cplxOp_coercive {s : ℕ} [NeZero s] {A : Matrix (Torus d s) (Torus d s) ℝ} {γ : ℝ}
    (hcoer : ∀ φ : Torus d s → ℝ, γ * ∑ x, φ x ^ 2 ≤ φ ⬝ᵥ A *ᵥ φ) :
    IsCoercive (cplxOp A) γ :=
  isCoercive_map_of_real A hcoer

theorem boxMat_coercive {s : ℕ} [NeZero s] {A : Matrix (Torus d s) (Torus d s) ℝ} {γ : ℝ}
    (hcoer : ∀ φ : Torus d s → ℝ, γ * ∑ x, φ x ^ 2 ≤ φ ⬝ᵥ A *ᵥ φ) {R : ℕ} (hs : 2 * R < s) :
    IsCoercive (boxMat A R) γ := by
  have h := isCoercive_submatrix (cplxOp_coercive hcoer)
    (fun u : sqBox d R => castL1 s (u : Fin d → ℤ))
    (fun a b h => Subtype.ext (castL1_injOn hs a.2 b.2 h))
  exact h

theorem boxMat_mul_boxGreen {s : ℕ} [NeZero s] {A : Matrix (Torus d s) (Torus d s) ℝ} {γ : ℝ}
    (hγ : 0 < γ) (hcoer : ∀ φ : Torus d s → ℝ, γ * ∑ x, φ x ^ 2 ≤ φ ⬝ᵥ A *ᵥ φ) {R : ℕ}
    (hs : 2 * R < s) : boxMat A R * boxGreen A R = 1 := by
  have hinj := castL1_injOn (d := d) hs
  have hU : IsUnit (restrictOp (cplxOp A) (boxImage d s R) +
      (0 : ℂ) • (1 : Matrix (boxImage d s R) (boxImage d s R) ℂ)) := by
    rw [zero_smul, add_zero]
    exact isUnit_of_isCoercive hγ (isCoercive_restrictOp (cplxOp_coercive hcoer) _)
  ext u u''
  have hmem : ∀ v : sqBox d R, castL1 s (v : Fin d → ℤ) ∈ boxImage d s R :=
    fun v => Finset.mem_image_of_mem _ v.2
  have key := sum_bm_greenFn hU (hmem u) (hmem u'')
  unfold boxImage at key
  rw [Finset.sum_image (fun a ha b hb h => hinj ha hb h)] at key
  have hbm : ∀ v : Fin d → ℤ, bm (cplxOp A) 0 (castL1 s (u : Fin d → ℤ)) (castL1 s v) =
      cplxOp A (castL1 s (u : Fin d → ℤ)) (castL1 s v) := by
    intro v; simp [bm]
  simp only [hbm] at key
  have hiff : (castL1 s (u : Fin d → ℤ) = castL1 s (u'' : Fin d → ℤ)) ↔ u = u'' := by
    constructor
    · intro h; exact Subtype.ext (hinj u.2 u''.2 h)
    · intro h; rw [h]
  rw [Matrix.mul_apply, Matrix.one_apply]
  have e : ∑ v : sqBox d R, boxMat A R u v * boxGreen A R v u'' =
      ∑ v ∈ sqBox d R, cplxOp A (castL1 s (u : Fin d → ℤ)) (castL1 s v) *
        greenFn (cplxOp A) 0 (boxImage d s R) (castL1 s v) (castL1 s (u'' : Fin d → ℤ)) := by
    rw [← Finset.sum_coe_sort (sqBox d R)]
    rfl
  rw [e]
  refine key.trans ?_
  simp only [hiff]

/-- The decay rate of the domain difference. -/
noncomputable def ctDecay (d : ℕ) (c₀ δ₀ γ₀ : ℝ) : ℝ :=
  min (ctRate c₀ δ₀ γ₀ (ballConst d (δ₀ / 4))) δ₀ / 2

/-- The constant of the domain difference. -/
noncomputable def ctDiff (d : ℕ) (c₀ δ₀ γ₀ : ℝ) : ℝ :=
  4 * c₀ * ballConst d (ctDecay d c₀ δ₀ γ₀) * ballConst d (ctDecay d c₀ δ₀ γ₀) / γ₀ ^ 2

theorem ballConst_nonneg' {r : ℝ} (hr : 0 < r) : 0 ≤ ballConst d r := ballConst_nonneg hr

theorem ctDecay_pos {c₀ δ₀ γ₀ : ℝ} (hc : 0 ≤ c₀) (hδ : 0 < δ₀) (hγ : 0 < γ₀) :
    0 < ctDecay d c₀ δ₀ γ₀ := by
  unfold ctDecay
  have hκ : 0 ≤ ballConst d (δ₀ / 4) := ballConst_nonneg (by positivity)
  have := ctRate_pos hc hδ hγ hκ
  have := lt_min this hδ
  positivity

theorem ctDiff_nonneg {c₀ δ₀ γ₀ : ℝ} (hc : 0 ≤ c₀) (hδ : 0 < δ₀) (hγ : 0 < γ₀) :
    0 ≤ ctDiff d c₀ δ₀ γ₀ := by
  unfold ctDiff
  have := ballConst_nonneg (d := d) (ctDecay_pos (d := d) hc hδ hγ)
  positivity

/-- Inverse versus box Dirichlet Green function on one torus. -/
theorem inv_sub_boxGreen_le {s : ℕ} [NeZero s] {c₀ δ₀ γ₀ : ℝ} (hc : 0 ≤ c₀) (hδ : 0 < δ₀)
    (hγ : 0 < γ₀) {A : Matrix (Torus d s) (Torus d s) ℝ}
    (hdec : ∀ x y, |A x y| ≤ c₀ * Real.exp (-δ₀ * torusDist d s x y))
    (hcoer : ∀ φ : Torus d s → ℝ, γ₀ * ∑ x, φ x ^ 2 ≤ φ ⬝ᵥ A *ᵥ φ) {R₀ R : ℕ} (hR : R₀ ≤ R)
    (hs : 2 * R < s) {u u' : Fin d → ℤ} (hu : u ∈ sqBox d R₀) (hu' : u' ∈ sqBox d R₀) :
    ‖((A⁻¹ (castTorus s u) (castTorus s u') : ℝ) : ℂ) -
        greenFn (cplxOp A) 0 (boxImage d s R) (castL1 s u) (castL1 s u')‖ ≤
      ctDiff d c₀ δ₀ γ₀ * Real.exp (-ctDecay d c₀ δ₀ γ₀ * (2 * ((R : ℝ) + 1 - R₀))) := by
  have hcoerc := cplxOp_coercive hcoer
  have hU : IsUnit (cplxOp A) := isUnit_of_isCoercive hγ hcoerc
  have hinv : (cplxOp A)⁻¹ = (A⁻¹).map (algebraMap ℝ ℂ) := map_inv_real A hU
  have hκ : 0 ≤ ballConst d (δ₀ / 4) := ballConst_nonneg (by positivity)
  have hμ := ctDecay_pos (d := d) hc hδ hγ
  have hκ' : 0 ≤ ballConst d (ctDecay d c₀ δ₀ γ₀) := ballConst_nonneg hμ
  have hA : ∀ x y : L1Torus d s, ‖cplxOp A x y‖ ≤ c₀ * Real.exp (-δ₀ * dist x y) := by
    intro x y
    have e : ‖cplxOp A x y‖ = |A x y| := by
      show ‖algebraMap ℝ ℂ (A x y)‖ = |A x y|
      simp
    rw [e, dist_L1Torus]
    exact hdec x y
  have hK : ∀ x : L1Torus d s, ∑ y, Real.exp (-(δ₀ / 4) * dist x y) ≤ ballConst d (δ₀ / 4) :=
    fun x => ballSum_L1Torus d s (by positivity) x
  have hK' : ∀ x : L1Torus d s, ∑ y, Real.exp (-(min (ctRate c₀ δ₀ γ₀ (ballConst d (δ₀ / 4))) δ₀ / 2)
      * dist x y) ≤ ballConst d (ctDecay d c₀ δ₀ γ₀) := fun x =>
    ballSum_L1Torus d s hμ x
  have hmem : ∀ v, v ∈ sqBox d R₀ → castL1 (d := d) s v ∈ boxImage d s R := fun v hv =>
    Finset.mem_image_of_mem _ (sqBox_mono hR hv)
  have hs0 : 2 * R₀ < s := by omega
  have hfar : ∀ v, v ∈ sqBox d R₀ → ∀ z : L1Torus d s, z ∉ boxImage d s R →
      (R : ℝ) + 1 - R₀ ≤ dist (castL1 (d := d) s v) z := fun v hv z hz =>
    le_torusDist_of_not_mem hs0 hv hz
  have key := inv_sub_greenFn_le (A := cplxOp A) hc hδ hγ hκ hκ' hA hK hK' hcoerc
    (boxImage d s R) (x₁ := castL1 s u) (x₂ := castL1 s u') (hmem u' hu')
    (r₁ := (R : ℝ) + 1 - R₀) (r₂ := (R : ℝ) + 1 - R₀) (hfar u hu) (hfar u' hu')
  have e : (cplxOp A)⁻¹ (castL1 s u) (castL1 s u') =
      ((A⁻¹ (castTorus s u) (castTorus s u') : ℝ) : ℂ) := by
    rw [hinv]; rfl
  rw [e] at key
  refine key.trans (le_of_eq ?_)
  unfold ctDiff ctDecay
  congr 2
  ring

theorem exists_nat_exp_small (K μ η : ℝ) (R₀ : ℕ) (hμ : 0 < μ) (hη : 0 < η) :
    ∃ N : ℕ, ∀ R : ℕ, N ≤ R → K * Real.exp (-μ * (2 * ((R : ℝ) + 1 - R₀))) ≤ η := by
  have h1 : Filter.Tendsto (fun R : ℕ => (R : ℝ) * (2 * μ)) Filter.atTop Filter.atTop :=
    Filter.Tendsto.atTop_mul_const (by positivity) tendsto_natCast_atTop_atTop
  have h2 : Filter.Tendsto (fun R : ℕ => (R : ℝ) * (2 * μ) + μ * (2 * (1 - R₀)))
      Filter.atTop Filter.atTop := Filter.tendsto_atTop_add_const_right _ _ h1
  have h3 := (Real.tendsto_exp_neg_atTop_nhds_zero.comp h2).const_mul K
  have h4 : ∀ᶠ R : ℕ in Filter.atTop, K * (Real.exp ∘ Neg.neg ∘ fun R : ℕ => (R : ℝ) * (2 * μ) +
      μ * (2 * (1 - R₀))) R < η := by
    exact Filter.Tendsto.eventually_lt_const (by simpa using hη) h3
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 h4
  refine ⟨N, fun R hR => (hN R hR).le.trans' (le_of_eq ?_)⟩
  simp only [Function.comp]
  congr 2
  ring

/-- **Cauchy property of the inverse.**  Let `A_j` be coercive operators on tori of side
`s j → ∞` with exponentially decaying entries, uniformly in `j`, whose entries on the images of
a cube are Cauchy as `j → ∞`.  Then so are the entries of the inverses. -/
theorem cauchy_inv_entries {c₀ δ₀ γ₀ : ℝ} (hc : 0 ≤ c₀) (hδ : 0 < δ₀) (hγ : 0 < γ₀)
    (s : ℕ → ℕ) [hs0 : ∀ j, NeZero (s j)] (hs : ∀ j, j ≤ s j)
    (A : ∀ j, Matrix (Torus d (s j)) (Torus d (s j)) ℝ)
    (hdec : ∀ j x y, |A j x y| ≤ c₀ * Real.exp (-δ₀ * torusDist d (s j) x y))
    (hcoer : ∀ j (φ : Torus d (s j) → ℝ), γ₀ * ∑ x, φ x ^ 2 ≤ φ ⬝ᵥ A j *ᵥ φ)
    (hagree : ∀ (R : ℕ) (ε : ℝ), 0 < ε → ∃ j₀ : ℕ, ∀ j₁, j₀ ≤ j₁ → ∀ j₂, j₀ ≤ j₂ →
      ∀ u ∈ sqBox d R, ∀ u' ∈ sqBox d R,
        |A j₁ (castTorus (s j₁) u) (castTorus (s j₁) u') -
          A j₂ (castTorus (s j₂) u) (castTorus (s j₂) u')| ≤ ε)
    (R₀ : ℕ) (η : ℝ) (hη : 0 < η) :
    ∃ j₀ : ℕ, ∀ j₁, j₀ ≤ j₁ → ∀ j₂, j₀ ≤ j₂ → ∀ u ∈ sqBox d R₀, ∀ u' ∈ sqBox d R₀,
      |(A j₁)⁻¹ (castTorus (s j₁) u) (castTorus (s j₁) u') -
        (A j₂)⁻¹ (castTorus (s j₂) u) (castTorus (s j₂) u')| ≤ η := by
  have hμ := ctDecay_pos (d := d) hc hδ hγ
  obtain ⟨N, hN⟩ := exists_nat_exp_small (ctDiff d c₀ δ₀ γ₀) (ctDecay d c₀ δ₀ γ₀) (η / 4) R₀ hμ
    (by positivity)
  set R : ℕ := max N R₀ with hRdef
  have hRN : N ≤ R := le_max_left _ _
  have hRR₀ : R₀ ≤ R := le_max_right _ _
  have hexp := hN R hRN
  set nB : ℝ := (Fintype.card (sqBox d R) : ℝ) with hnB
  have hnB0 : 0 ≤ nB := Nat.cast_nonneg _
  set ε : ℝ := η * γ₀ ^ 2 / (4 * (nB ^ 2 + 1)) with hε
  have hε0 : 0 < ε := by positivity
  obtain ⟨j₁', hj₁'⟩ := hagree R ε hε0
  refine ⟨max j₁' (2 * R + 1), fun j₁ hj₁ j₂ hj₂ u hu u' hu' => ?_⟩
  have hj₁a : j₁' ≤ j₁ := (le_max_left _ _).trans hj₁
  have hj₂a : j₁' ≤ j₂ := (le_max_left _ _).trans hj₂
  have hs₁ : 2 * R < s j₁ := by
    have := (le_max_right _ _).trans hj₁
    have := hs j₁
    omega
  have hs₂ : 2 * R < s j₂ := by
    have := (le_max_right _ _).trans hj₂
    have := hs j₂
    omega
  have hmem := sqBox_mono (d := d) hRR₀
  -- the two comparisons with the box Green functions
  have c₁ := inv_sub_boxGreen_le hc hδ hγ (hdec j₁) (hcoer j₁) hRR₀ hs₁ hu hu'
  have c₂ := inv_sub_boxGreen_le hc hδ hγ (hdec j₂) (hcoer j₂) hRR₀ hs₂ hu hu'
  -- the comparison of the box Green functions
  have hent : ∀ a b : sqBox d R, ‖boxMat (A j₁) R a b - boxMat (A j₂) R a b‖ ≤ ε := by
    intro a b
    have := hj₁' j₁ hj₁a j₂ hj₂a a a.2 b b.2
    have e : boxMat (A j₁) R a b - boxMat (A j₂) R a b =
        ((A j₁ (castTorus (s j₁) a) (castTorus (s j₁) b) -
          A j₂ (castTorus (s j₂) a) (castTorus (s j₂) b) : ℝ) : ℂ) := by
      simp [boxMat, cplxOp, castL1]
    rw [e, Complex.norm_real, Real.norm_eq_abs]
    exact this
  have hg := entry_diff_le hγ (boxMat_coercive (hcoer j₁) hs₁) (boxMat_coercive (hcoer j₂) hs₂)
    (boxMat_mul_boxGreen hγ (hcoer j₁) hs₁) (boxMat_mul_boxGreen hγ (hcoer j₂) hs₂) hent
    ⟨u, hmem hu⟩ ⟨u', hmem hu'⟩
  have hg' : ‖greenFn (cplxOp (A j₁)) 0 (boxImage d (s j₁) R) (castL1 (s j₁) u) (castL1 (s j₁) u') -
      greenFn (cplxOp (A j₂)) 0 (boxImage d (s j₂) R) (castL1 (s j₂) u) (castL1 (s j₂) u')‖ ≤
      nB ^ 2 * ε * γ₀⁻¹ ^ 2 := hg
  have hsmall : nB ^ 2 * ε * γ₀⁻¹ ^ 2 ≤ η / 4 := by
    rw [hε]
    have : nB ^ 2 * (η * γ₀ ^ 2 / (4 * (nB ^ 2 + 1))) * γ₀⁻¹ ^ 2 =
        η / 4 * (nB ^ 2 / (nB ^ 2 + 1)) := by
      field_simp
    rw [this]
    have : nB ^ 2 / (nB ^ 2 + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith
    nlinarith
  -- assemble
  set x₁ : ℝ := (A j₁)⁻¹ (castTorus (s j₁) u) (castTorus (s j₁) u') with hx₁
  set x₂ : ℝ := (A j₂)⁻¹ (castTorus (s j₂) u) (castTorus (s j₂) u') with hx₂
  have e1 : |x₁ - x₂| = ‖(x₁ : ℂ) - (x₂ : ℂ)‖ := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  rw [e1]
  set g₁ := greenFn (cplxOp (A j₁)) 0 (boxImage d (s j₁) R) (castL1 (s j₁) u) (castL1 (s j₁) u')
  set g₂ := greenFn (cplxOp (A j₂)) 0 (boxImage d (s j₂) R) (castL1 (s j₂) u) (castL1 (s j₂) u')
  have t1 : ‖(x₁ : ℂ) - g₁‖ ≤ η / 4 := c₁.trans hexp
  have t2 : ‖(x₂ : ℂ) - g₂‖ ≤ η / 4 := c₂.trans hexp
  calc ‖(x₁ : ℂ) - (x₂ : ℂ)‖ = ‖((x₁ : ℂ) - g₁) + (g₁ - g₂) - ((x₂ : ℂ) - g₂)‖ := by
        congr 1; ring
    _ ≤ ‖(x₁ : ℂ) - g₁‖ + ‖g₁ - g₂‖ + ‖(x₂ : ℂ) - g₂‖ := by
        refine (norm_sub_le _ _).trans ?_
        gcongr
        exact norm_add_le _ _
    _ ≤ η := by linarith

end Torus

end Balaban.Green
