/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Background.Def5
import Mathlib.Tactic.Ring

/-!
# O(N) covariance of the background fields (BACKGROUND.md §7)

For a matrix `R` of `ℂ^{N×N}` with `Rᵀ R = 1` the rotation `D ↦ D.rot R` of the data
(`Ψ ↦ R Ψ`, `h̃ ↦ R h̃` pointwise, `rotField` of `Def6Terms`) and `φ ↦ rotFld R φ` of fields on `Ω₁`.

* `bgFieldC_rot`, `bgMultC_rot`: for every such `R` (complex orthogonal) and every `c₀`, the
  complex background field commutes with the rotation and the multiplier is invariant.  No domain
  condition is needed: the set of small solutions of (EL) is carried bijectively onto that of the
  rotated datum, so the `∃!` of the definition transports.
* `bgField_rot`, `bgMult_rot`: the same for the real background field, for real orthogonal `R`
  (`IsRealOrth`), where the action is invariant.
-/

@[expose] public section

namespace Balaban.Background
open Balaban.Multiscale Matrix Finset
variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- The matrix `R` acting on the `Fin N` index of a field on `ι × Fin N`:
`(R φ)(x, i) = ∑ⱼ R i j φ(x, j)` (the pointwise action `rotField` of `Def6Terms`). -/
def rotFld {ι : Type*} (R : Matrix (Fin N) (Fin N) ℂ) (φ : ι × Fin N → ℂ) : ι × Fin N → ℂ :=
  fun p => ∑ j, R p.2 j * φ (p.1, j)

theorem rotFld_mul {ι : Type*} (R S : Matrix (Fin N) (Fin N) ℂ) (φ : ι × Fin N → ℂ) :
    rotFld R (rotFld S φ) = rotFld (R * S) φ := by
  funext p
  simp only [rotFld, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by ring

theorem rotFld_one {ι : Type*} (φ : ι × Fin N → ℂ) : rotFld (1 : Matrix (Fin N) (Fin N) ℂ) φ = φ := by
  funext p
  simp [rotFld, Matrix.one_apply]

theorem rotFld_rotFld_transpose {ι : Type*} {R : Matrix (Fin N) (Fin N) ℂ} (hR : Rᵀ * R = 1)
    (φ : ι × Fin N → ℂ) : rotFld Rᵀ (rotFld R φ) = φ := by
  rw [rotFld_mul, hR, rotFld_one]

theorem rotFld_transpose_rotFld {ι : Type*} {R : Matrix (Fin N) (Fin N) ℂ} (hR : Rᵀ * R = 1)
    (φ : ι × Fin N → ℂ) : rotFld R (rotFld Rᵀ φ) = φ := by
  have : R * Rᵀ = 1 := by
    have := mul_eq_one_comm.1 hR
    simpa using this
  rw [rotFld_mul, this, rotFld_one]

theorem rotFld_liftOp {ι : Type*} [Fintype ι] [DecidableEq ι] (R : Matrix (Fin N) (Fin N) ℂ)
    (A : Matrix ι ι ℂ) (φ : ι × Fin N → ℂ) :
    liftOp N A *ᵥ rotFld R φ = rotFld R (liftOp N A *ᵥ φ) := by
  funext ⟨x, i⟩
  have e1 := liftOp_mulVec A (rotFld R φ) x i
  have e2 : ∀ j, (liftOp N A *ᵥ φ) (x, j) = (A *ᵥ fun b => φ (b, j)) x := fun j => liftOp_mulVec A φ x j
  rw [e1]
  simp only [rotFld]
  simp only [e2]
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun y _ => by ring

theorem rotFld_bilin {ι : Type*} {R : Matrix (Fin N) (Fin N) ℂ} (hR : Rᵀ * R = 1)
    (u w : ι × Fin N → ℂ) (x : ι) :
    ∑ i, rotFld R u (x, i) * rotFld R w (x, i) = ∑ i, u (x, i) * w (x, i) := by
  have h : ∀ j l : Fin N, ∑ i, R i j * R i l = (1 : Matrix (Fin N) (Fin N) ℂ) j l := by
    intro j l
    rw [← hR]; simp [Matrix.mul_apply]
  simp only [rotFld]
  calc _ = ∑ i, ∑ j, ∑ l, R i j * u (x, j) * (R i l * w (x, l)) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_mul_sum]
    _ = ∑ j, ∑ l, (∑ i, R i j * R i l) * (u (x, j) * w (x, l)) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun i _ => by ring
    _ = _ := by
          simp only [h, Matrix.one_apply, ite_mul, one_mul, zero_mul]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.sum_ite_eq]
          simp

variable {G : GeneratingSet d L N₀ k ϱ}

/-- The rotated datum `(R Ψ, R h̃)`. -/
def BgData.rot (R : Matrix (Fin N) (Fin N) ℂ) (D : BgData G N) : BgData G N where
  Ψ x := R *ᵥ D.Ψ x
  h x := R *ᵥ D.h x
  Ψ_layerConst := fun n h1 h2 x hx x' hx' => by
    simp only; rw [D.Ψ_layerConst n h1 h2 x hx x' hx']
  h_layerConst := fun n h1 h2 x hx x' hx' => by
    simp only; rw [D.h_layerConst n h1 h2 x hx x' hx']
  Ψ_zero := fun x hx => by simp [D.Ψ_zero x hx]
  h_zero := fun x hx => by simp [D.h_zero x hx]

theorem BgData.ext' {D D' : BgData G N} (hΨ : D.Ψ = D'.Ψ) (hh : D.h = D'.h) : D = D' := by
  cases D; cases D'; simp_all

theorem BgData.rot_rot (R S : Matrix (Fin N) (Fin N) ℂ) (D : BgData G N) :
    (D.rot R).rot S = D.rot (S * R) := by
  refine BgData.ext' ?_ ?_ <;> funext x <;> simp [BgData.rot, Matrix.mulVec_mulVec]

theorem BgData.rot_one (D : BgData G N) : D.rot 1 = D := by
  refine BgData.ext' ?_ ?_ <;> funext x <;> simp [BgData.rot]

theorem BgData.rot_transpose_rot {R : Matrix (Fin N) (Fin N) ℂ} (hR : Rᵀ * R = 1) (D : BgData G N) :
    (D.rot R).rot Rᵀ = D := by
  rw [BgData.rot_rot, hR, BgData.rot_one]

theorem source_rot (R : Matrix (Fin N) (Fin N) ℂ) (a : ℕ → ℝ) (ν : ℝ) (D : BgData G N) :
    source G a ν (D.rot R) = rotFld R (source G a ν D) := by
  funext p
  simp only [source, qStar, boundaryTerm, rotFld, BgData.rot, Matrix.mulVec, dotProduct,
    Finset.mul_sum, mul_add, Finset.sum_add_distrib]
  refine congrArg₂ _ (congrArg₂ _ (Finset.sum_congr rfl fun i _ => by ring)
    (Finset.sum_congr rfl fun i _ => by ring)) (congrArg₂ _ ?_ ?_) <;>
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun μ _ => ?_
    split_ifs <;> simp

theorem orth_transpose {R : Matrix (Fin N) (Fin N) ℂ} (hR : Rᵀ * R = 1) : Rᵀᵀ * Rᵀ = 1 := by
  rw [Matrix.transpose_transpose]
  exact mul_eq_one_comm.1 hR

theorem existsUnique_equiv_iff {α β : Type*} (e : α ≃ β) {P : α → Prop} {Q : β → Prop}
    (hPQ : ∀ x, P x ↔ Q (e x)) : (∃! x, P x) ↔ ∃! y, Q y := by
  constructor
  · rintro ⟨x, hx, hu⟩
    refine ⟨e x, (hPQ x).1 hx, fun y hy => ?_⟩
    have := hu (e.symm y) ((hPQ _).2 (by simpa using hy))
    rw [← this]; simp
  · rintro ⟨y, hy, hu⟩
    refine ⟨e.symm y, (hPQ _).2 (by simpa using hy), fun x hx => ?_⟩
    have := hu (e x) ((hPQ x).1 hx)
    rw [← this]; simp

open Classical in
theorem dite_existsUnique_equiv {α β γ : Type*} (e : α ≃ β) {P : α → Prop} {Q : β → Prop}
    (hPQ : ∀ x, P x ↔ Q (e x)) (f : α → γ) (g : β → γ) (hfg : ∀ x, f x = g (e x)) (z : γ) :
    (if H : ∃! x, P x then f H.exists.choose else z) =
      (if H : ∃! y, Q y then g H.exists.choose else z) := by
  classical
  by_cases H : ∃! x, P x
  · have H' := (existsUnique_equiv_iff e hPQ).1 H
    simp only [H, H', ↓reduceDIte]
    have : H.exists.choose = e.symm H'.exists.choose :=
      H.unique H.exists.choose_spec ((hPQ _).2 (by simpa using H'.exists.choose_spec))
    rw [this, hfg]; simp
  · have H' : ¬ ∃! y, Q y := fun h => H ((existsUnique_equiv_iff e hPQ).2 h)
    simp only [H, H', ↓reduceDIte]

/-- The rotation of fields as an equivalence. -/
def rotEquiv {ι : Type*} {R : Matrix (Fin N) (Fin N) ℂ} (hR : Rᵀ * R = 1) :
    (ι × Fin N → ℂ) ≃ (ι × Fin N → ℂ) where
  toFun := rotFld R
  invFun := rotFld Rᵀ
  left_inv := rotFld_rotFld_transpose hR
  right_inv := rotFld_transpose_rotFld hR

variable (a : ℕ → ℝ) (ν : ℝ)

theorem isEL_rot {R : Matrix (Fin N) (Fin N) ℂ} (hR : Rᵀ * R = 1) {D : BgData G N}
    {φ : G.Ω 1 × Fin N → ℂ} {α : G.Ω 1 → ℂ} (h : IsEL G a ν D φ α) :
    IsEL G a ν (D.rot R) (rotFld R φ) α := by
  refine ⟨?_, fun x => ?_⟩
  · rw [rotFld_liftOp, h.1, source_rot]
  · rw [rotFld_bilin hR]; exact h.2 x

theorem isEL_rot_iff {R : Matrix (Fin N) (Fin N) ℂ} (hR : Rᵀ * R = 1) {D : BgData G N}
    {φ : G.Ω 1 × Fin N → ℂ} {α : G.Ω 1 → ℂ} :
    IsEL G a ν (D.rot R) (rotFld R φ) α ↔ IsEL G a ν D φ α := by
  refine ⟨fun h => ?_, isEL_rot a ν hR⟩
  have := isEL_rot a ν (orth_transpose hR) h
  rwa [BgData.rot_transpose_rot hR, rotFld_rotFld_transpose hR] at this

theorem isSmallSolution_rot_iff {R : Matrix (Fin N) (Fin N) ℂ} (hR : Rᵀ * R = 1) {c₀ : ℝ}
    {D : BgData G N} {φ : G.Ω 1 × Fin N → ℂ} {α : G.Ω 1 → ℂ} :
    IsSmallSolution G a ν c₀ (D.rot R) (rotFld R φ) α ↔ IsSmallSolution G a ν c₀ D φ α := by
  unfold IsSmallSolution
  rw [isEL_rot_iff a ν hR]

/-- **Covariance of the complex background field**: for `Rᵀ R = 1`,
`bgFieldC (R•D) = R • bgFieldC D` and `bgMultC (R•D) = bgMultC D`. -/
theorem bgFieldC_rot {R : Matrix (Fin N) (Fin N) ℂ} (hR : Rᵀ * R = 1) (c₀ : ℝ)
    (D : BgData G N) :
    bgFieldC G a ν c₀ (D.rot R) = rotFld R (bgFieldC G a ν c₀ D) ∧
      bgMultC G a ν c₀ (D.rot R) = bgMultC G a ν c₀ D := by
  classical
  let e : ((G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ)) ≃ ((G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ)) :=
    (rotEquiv hR).prodCongr (Equiv.refl _)
  have hPQ : ∀ s : (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ),
      IsSmallSolution G a ν c₀ D s.1 s.2 ↔ IsSmallSolution G a ν c₀ (D.rot R) (e s).1 (e s).2 :=
    fun s => (isSmallSolution_rot_iff a ν hR).symm
  constructor
  · have := dite_existsUnique_equiv e (P := fun s => IsSmallSolution G a ν c₀ D s.1 s.2)
      (Q := fun s => IsSmallSolution G a ν c₀ (D.rot R) s.1 s.2) hPQ (fun s => rotFld R s.1) (fun s => s.1)
      (fun s => rfl) (rotFld R 0)
    have h0 : rotFld R (0 : G.Ω 1 × Fin N → ℂ) = 0 := by funext p; simp [rotFld]
    rw [h0] at this
    unfold bgFieldC
    rw [← this]
    split_ifs <;> simp [h0]
  · have := dite_existsUnique_equiv e (P := fun s => IsSmallSolution G a ν c₀ D s.1 s.2)
      (Q := fun s => IsSmallSolution G a ν c₀ (D.rot R) s.1 s.2) hPQ (fun s => s.2) (fun s => s.2) (fun s => rfl) 0
    unfold bgMultC
    rw [← this]

/-- A real orthogonal matrix: `Rᵀ R = 1` with real entries. -/
def IsRealOrth (R : Matrix (Fin N) (Fin N) ℂ) : Prop :=
  Rᵀ * R = 1 ∧ ∀ i j, (R i j).im = 0

theorem IsRealOrth.transpose {R : Matrix (Fin N) (Fin N) ℂ} (h : IsRealOrth R) : IsRealOrth Rᵀ :=
  ⟨orth_transpose h.1, fun i j => h.2 j i⟩

theorem rotFld_sub {ι : Type*} (R : Matrix (Fin N) (Fin N) ℂ) (u w : ι × Fin N → ℂ) :
    rotFld R (u - w) = rotFld R u - rotFld R w := by
  funext p; simp [rotFld, mul_sub, Finset.sum_sub_distrib]

theorem rotFld_conj {ι : Type*} {R : Matrix (Fin N) (Fin N) ℂ} (hr : ∀ i j, (R i j).im = 0)
    (u : ι × Fin N → ℂ) :
    rotFld R (fun p => starRingEnd ℂ (u p)) = fun p => starRingEnd ℂ (rotFld R u p) := by
  funext p
  simp only [rotFld, map_sum, map_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.conj_eq_iff_im.2 (hr _ _)]

theorem normSq_rot {R : Matrix (Fin N) (Fin N) ℂ} (hR : IsRealOrth R) (v : Fin N → ℂ) :
    ∑ i, ‖(R *ᵥ v) i‖ ^ 2 = ∑ i, ‖v i‖ ^ 2 := by
  have key := rotFld_bilin (ι := Unit) hR.1 (fun p => v p.2) (fun p => starRingEnd ℂ (v p.2)) ()
  rw [rotFld_conj hR.2] at key
  apply Complex.ofReal_injective
  push_cast
  have e : ∀ z : ℂ, ((‖z‖ : ℝ) : ℂ) ^ 2 = z * starRingEnd ℂ z := fun z => (Complex.mul_conj' z).symm
  simp only [e]
  simpa [rotFld, Matrix.mulVec, dotProduct] using key

theorem isReal_rot {R : Matrix (Fin N) (Fin N) ℂ} (hR : IsRealOrth R) {D : BgData G N}
    (hD : D.IsReal) : (D.rot R).IsReal := by
  have hv : ∀ v : Fin N → ℂ, (∀ i, (v i).im = 0) → ∀ i, ((R *ᵥ v) i).im = 0 := by
    intro v hv i
    simp [Matrix.mulVec, dotProduct, Complex.im_sum, hR.2, hv]
  intro x i
  exact ⟨hv _ (fun j => (hD x j).1) i, hv _ (fun j => (hD x j).2) i⟩

theorem isRealUnitField_rot {R : Matrix (Fin N) (Fin N) ℂ} (hR : IsRealOrth R)
    {φ : G.Ω 1 × Fin N → ℂ} (h : IsRealUnitField G φ) : IsRealUnitField G (rotFld R φ) := by
  intro x
  refine ⟨fun i => ?_, ?_⟩
  · simp [rotFld, Complex.im_sum, hR.2, (h x).1]
  · rw [← (h x).2]
    exact normSq_rot hR (fun j => φ (x, j))

theorem svec_rot (R : Matrix (Fin N) (Fin N) ℂ) (s : G.Ω 1 × Fin N → ℂ)
    (y : Torus d (N₀ * L ^ k)) : svec G (rotFld R s) y = R *ᵥ svec G s y := by
  funext i
  by_cases hy : y ∈ G.Ω 1
  · simp [svec, zeroExt, hy, rotFld, Matrix.mulVec, dotProduct]
  · simp [svec, zeroExt, hy, Matrix.mulVec, dotProduct]

theorem blockAvg_rot (R : Matrix (Fin N) (Fin N) ℂ) (φ : G.Ω 1 × Fin N → ℂ)
    (x : Torus d (N₀ * L ^ k)) :
    (fun i => blockAvg G (rotFld R φ) x i) = R *ᵥ fun i => blockAvg G φ x i := by
  funext i
  simp only [blockAvg, svec_rot, Matrix.mulVec, dotProduct, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun y _ => by ring

theorem barField_rot (R : Matrix (Fin N) (Fin N) ℂ) (Ψ : Torus d (N₀ * L ^ k) → Fin N → ℂ)
    (φ : G.Ω 1 × Fin N → ℂ) (x : Torus d (N₀ * L ^ k)) :
    (fun i => barField G (fun y => R *ᵥ Ψ y) (rotFld R φ) x i) = R *ᵥ fun i => barField G Ψ φ x i := by
  funext i
  by_cases hx : x ∈ G.Ω 1
  · simp [barField, hx, rotFld, Matrix.mulVec, dotProduct]
  · simp [barField, hx, Matrix.mulVec, dotProduct]

theorem normSq_bar_rot {R : Matrix (Fin N) (Fin N) ℂ} (hR : IsRealOrth R)
    (Ψ : Torus d (N₀ * L ^ k) → Fin N → ℂ) (φ : G.Ω 1 × Fin N → ℂ)
    (x y : Torus d (N₀ * L ^ k)) :
    ∑ i, ‖barField G (fun z => R *ᵥ Ψ z) (rotFld R φ) y i -
      barField G (fun z => R *ᵥ Ψ z) (rotFld R φ) x i‖ ^ 2 =
      ∑ i, ‖barField G Ψ φ y i - barField G Ψ φ x i‖ ^ 2 := by
  have e1 := barField_rot R Ψ φ y
  have e2 := barField_rot R Ψ φ x
  have := normSq_rot hR (fun i => barField G Ψ φ y i - barField G Ψ φ x i)
  rw [← this]
  refine Finset.sum_congr rfl fun i _ => ?_
  have a1 := congrFun e1 i
  have a2 := congrFun e2 i
  rw [a1, a2]
  simp [Matrix.mulVec, dotProduct, mul_sub, Finset.sum_sub_distrib]

theorem action_rot {R : Matrix (Fin N) (Fin N) ℂ} (hR : IsRealOrth R) (a : ℕ → ℝ) (ν : ℝ)
    (D : BgData G N) (φ : G.Ω 1 × Fin N → ℂ) :
    action G a ν (D.rot R) (rotFld R φ) = action G a ν D φ := by
  unfold action
  have h1 : ∀ x : G.Ω 1, ∑ i, ‖(D.rot R).Ψ x i - blockAvg G (rotFld R φ) x i‖ ^ 2 =
      ∑ i, ‖D.Ψ x i - blockAvg G φ x i‖ ^ 2 := by
    intro x
    have e := congrFun (blockAvg_rot R φ x)
    have := normSq_rot hR (fun i => D.Ψ x i - blockAvg G φ x i)
    rw [← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [BgData.rot, e]
    simp [Matrix.mulVec, dotProduct, mul_sub, Finset.sum_sub_distrib]
  have h3 : ∀ x : G.Ω 1, ∑ i, ‖rotFld R φ (x, i) - (D.rot R).h x i‖ ^ 2 =
      ∑ i, ‖φ (x, i) - D.h x i‖ ^ 2 := by
    intro x
    rw [← normSq_rot hR (fun i => φ (x, i) - D.h x i)]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [rotFld, BgData.rot, Matrix.mulVec, dotProduct, mul_sub, Finset.sum_sub_distrib]
  simp only [h1, h3]
  have h2 := fun x μ => normSq_bar_rot (G := G) hR D.Ψ φ x (x + Pi.single μ 1)
  simp only [BgData.rot] at *
  simp only [h2]

theorem isMinimizer_rot {R : Matrix (Fin N) (Fin N) ℂ} (hR : IsRealOrth R) {D : BgData G N}
    {φ : G.Ω 1 × Fin N → ℂ} (h : IsMinimizer G a ν D φ) :
    IsMinimizer G a ν (D.rot R) (rotFld R φ) := by
  refine ⟨isReal_rot hR h.1, isRealUnitField_rot hR h.2.1, fun σ hσ => ?_⟩
  rw [action_rot hR]
  have h1 := h.2.2 (rotFld Rᵀ σ) (isRealUnitField_rot hR.transpose hσ)
  have h2 := action_rot (G := G) hR a ν D (rotFld Rᵀ σ)
  rw [rotFld_transpose_rotFld hR.1] at h2
  rw [← h2] at h1
  exact h1

theorem isMinimizer_rot_iff {R : Matrix (Fin N) (Fin N) ℂ} (hR : IsRealOrth R) {D : BgData G N}
    {φ : G.Ω 1 × Fin N → ℂ} :
    IsMinimizer G a ν (D.rot R) (rotFld R φ) ↔ IsMinimizer G a ν D φ := by
  refine ⟨fun h => ?_, isMinimizer_rot a ν hR⟩
  have := isMinimizer_rot a ν hR.transpose h
  rwa [BgData.rot_transpose_rot hR.1, rotFld_rotFld_transpose hR.1] at this

/-- **Covariance of the real background field** under real orthogonal `R`. -/
theorem bgField_rot {R : Matrix (Fin N) (Fin N) ℂ} (hR : IsRealOrth R) (D : BgData G N) :
    bgField G a ν (D.rot R) = rotFld R (bgField G a ν D) := by
  classical
  have := dite_existsUnique_equiv (rotEquiv hR.1) (P := fun φ => IsMinimizer G a ν D φ)
    (Q := fun φ => IsMinimizer G a ν (D.rot R) φ)
    (fun φ => (isMinimizer_rot_iff a ν hR).symm) (fun φ => rotFld R φ) (fun φ => φ)
    (fun φ => rfl) (rotFld R 0)
  have h0 : rotFld R (0 : G.Ω 1 × Fin N → ℂ) = 0 := by funext p; simp [rotFld]
  rw [h0] at this
  unfold bgField
  rw [← this]
  split_ifs <;> simp [h0]

/-- The real multiplier is invariant under real orthogonal rotations. -/
theorem bgMult_rot {R : Matrix (Fin N) (Fin N) ℂ} (hR : IsRealOrth R) (D : BgData G N) :
    bgMult G a ν (D.rot R) = bgMult G a ν D := by
  funext x
  unfold bgMult
  rw [bgField_rot a ν hR, rotFld_liftOp, source_rot, ← rotFld_sub]
  congr 1
  exact rotFld_bilin hR.1 _ _ x
end Balaban.Background
