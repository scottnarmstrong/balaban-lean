/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.CauchyInverse
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity


/-!
# G-5(b): the kernels of the tori are Cauchy as the side grows

The fine operator `H = N² (-Δ) + ν + a P` on the torus of side `L (j+1) L^k`, and the coarse
operator `A = Δ_tr + (a'/L²) Q*Q` on the torus of side `L (j+1)`, satisfy the hypotheses of
`Balaban.Green.cauchy_inv_entries`: uniform coercivity, uniform exponential decay of the entries,
and entries at the images of sites of `ℤ^d` that agree for large `j` (for `H` exactly, via the
explicit entries `Balaban.Green.latZ`, `Balaban.Green.projZ`; for `A` through the Cauchy property
of `Δ_tr`, itself a finite sum of entries of `H⁻¹` over two blocks).  The consequences
`Balaban.Green.fineGreen_cauchy`, `Balaban.Green.unitOperator_cauchy`,
`Balaban.Green.fineKernel_cauchy` and `Balaban.Green.coarseGreen_cauchy` say that the entries of
`H⁻¹`, `Δ_tr`, `a G Q*` and `C_tr` at sites of `ℤ^d` form Cauchy sequences in `j`, uniformly on
cubes.  No compactness and no subsequence is used.
-/

@[expose] public section

open Matrix Finset

namespace Balaban.Green

section Entries

variable {d : ℕ}

theorem castTorus_eq_iff {s : ℕ} {u u' : Fin d → ℤ} (h : ∀ μ, |u μ - u' μ| < s) :
    castTorus s u = castTorus s u' ↔ u = u' := by
  constructor
  · intro h'
    funext μ
    have hc : ((u μ : ℤ) : ZMod s) = ((u' μ : ℤ) : ZMod s) := congrFun h' μ
    have hdvd := (ZMod.intCast_eq_intCast_iff_dvd_sub (u μ) (u' μ) s).1 hc
    have hlt : |u' μ - u μ| < s := by rw [abs_sub_comm]; exact h μ
    have := Int.eq_zero_of_abs_lt_dvd hdvd hlt
    linarith
  · intro h'; rw [h']

theorem abs_ediv_le {a : ℤ} {N : ℕ} (hN : 0 < N) : |a / (N : ℤ)| ≤ |a| := by
  have hN1 : (1 : ℤ) ≤ N := by exact_mod_cast hN
  have h1 := Int.mul_ediv_self_le (x := a) (k := (N : ℤ)) (by omega)
  have h2 := Int.lt_mul_ediv_self_add (x := a) (k := (N : ℤ)) (by omega)
  set q := a / (N : ℤ) with hq
  rcases le_or_gt 0 q with h | h
  · rw [abs_of_nonneg h]
    have : q ≤ a := by nlinarith
    exact this.trans (le_abs_self _)
  · rw [abs_of_neg h]
    have : a ≤ q := by
      by_contra hc
      push Not at hc
      nlinarith
    have : -q ≤ -a := by linarith
    exact this.trans (neg_le_abs _)

theorem castTorus_add_single (s : ℕ) (u : Fin d → ℤ) (μ : Fin d) :
    castTorus s (u + Pi.single μ 1) = castTorus s u + Pi.single μ 1 := by
  funext i
  by_cases h : i = μ
  · subst h; simp [castTorus]
  · simp [castTorus, h]

/-- The entries of `-Δ + ν` on `ℤ^d`. -/
noncomputable def latZ (d : ℕ) (ν : ℝ) (u u' : Fin d → ℤ) : ℝ :=
  (2 * d + ν) * (if u = u' then 1 else 0) -
    ∑ μ : Fin d, ((if u' = u + Pi.single μ 1 then 1 else 0) +
      (if u = u' + Pi.single μ 1 then 1 else 0))

theorem latticeLaplacian_castTorus {s R : ℕ} [NeZero s] (hs : 2 * R + 1 < s) (ν : ℝ)
    {u u' : Fin d → ℤ} (hu : u ∈ sqBox d R) (hu' : u' ∈ sqBox d R) :
    latticeLaplacian d s ν (castTorus s u) (castTorus s u') = latZ d ν u u' := by
  have hb : ∀ μ, |u μ| ≤ R ∧ |u' μ| ≤ R := fun μ => ⟨mem_sqBox.1 hu μ, mem_sqBox.1 hu' μ⟩
  have key : ∀ (v w : Fin d → ℤ), (∀ μ, |v μ - w μ| ≤ 2 * R + 1) →
      (castTorus s v = castTorus s w ↔ v = w) := by
    intro v w h
    refine castTorus_eq_iff fun μ => ?_
    have := h μ
    have h2 : ((2 * R + 1 : ℕ) : ℤ) < s := by exact_mod_cast hs
    push_cast at h2
    linarith
  have hdiff : ∀ μ ν', |u μ - (u' μ + (Pi.single ν' (1 : ℤ) : Fin d → ℤ) μ)| ≤ 2 * R + 1 := by
    intro μ ν'
    have h1 := abs_le.1 (hb μ).1
    have h2 := abs_le.1 (hb μ).2
    have : |(Pi.single ν' (1 : ℤ) : Fin d → ℤ) μ| ≤ 1 := by
      by_cases h : μ = ν' <;> simp [h]
    have h3 := abs_le.1 this
    rw [abs_le]; constructor <;> linarith
  have hdiff' : ∀ μ ν', |u' μ - (u μ + (Pi.single ν' (1 : ℤ) : Fin d → ℤ) μ)| ≤ 2 * R + 1 := by
    intro μ ν'
    have h1 := abs_le.1 (hb μ).1
    have h2 := abs_le.1 (hb μ).2
    have : |(Pi.single ν' (1 : ℤ) : Fin d → ℤ) μ| ≤ 1 := by
      by_cases h : μ = ν' <;> simp [h]
    have h3 := abs_le.1 this
    rw [abs_le]; constructor <;> linarith
  unfold latticeLaplacian latZ
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.sum_apply,
    Matrix.add_apply, Matrix.transpose_apply, shiftMatrix, smul_eq_mul]
  have e1 : (castTorus s u = castTorus s u') ↔ u = u' := key u u' fun μ => by
    have h1 := abs_le.1 (hb μ).1
    have h2 := abs_le.1 (hb μ).2
    rw [abs_le]; constructor <;> linarith
  have e2 : ∀ μ, (castTorus s u' = castTorus s u + Pi.single μ 1) ↔ u' = u + Pi.single μ 1 := by
    intro μ
    rw [← castTorus_add_single]
    exact key _ _ fun i => by simpa using hdiff' i μ
  have e3 : ∀ μ, (castTorus s u = castTorus s u' + Pi.single μ 1) ↔ u = u' + Pi.single μ 1 := by
    intro μ
    rw [← castTorus_add_single]
    exact key _ _ fun i => by simpa using hdiff i μ
  simp only [e1, e2, e3]

/-- The entries of the block projection on `ℤ^d`. -/
noncomputable def projZ (d N : ℕ) (u u' : Fin d → ℤ) : ℝ :=
  if ∀ μ, u μ / (N : ℤ) = u' μ / (N : ℤ) then ((N : ℝ) ^ d)⁻¹ else 0

theorem mem_intFibre_div {N : ℕ} (hN : 0 < N) (u : Fin d → ℤ) :
    u ∈ intFibre N (fun i => u i / (N : ℤ)) := by
  rw [mem_intFibre]
  intro i
  have hN' : (N : ℤ) ≠ 0 := by exact_mod_cast hN.ne'
  exact ⟨Int.mul_ediv_self_le (x := u i) (k := (N : ℤ)) hN',
    Int.lt_mul_ediv_self_add (x := u i) (k := (N : ℤ)) (by exact_mod_cast hN)⟩

theorem blockMap_castTorus_div {ℓ N m : ℕ} [NeZero ℓ] [NeZero m] (hℓ : ℓ = N * m) (hN : 0 < N)
    (u : Fin d → ℤ) : blockMap N m (castTorus ℓ u) = castTorus m (fun i => u i / (N : ℤ)) :=
  blockMap_castTorus_of_mem hℓ hN (mem_intFibre_div hN u)

/-- Core: if the block indices `w μ / N` of the sites of a set lie in `[lo, hi]` with
`hi - lo < m`, the block projection at these sites is `projZ`. -/
theorem blockProjMatrix_castTorus_of_ediv_bounds {ℓ N m : ℕ} [NeZero ℓ] [NeZero m]
    (hℓ : ℓ = N * m) (hN : 0 < N) {lo hi : ℤ} (hlh : hi - lo < m) {S : Set (Fin d → ℤ)}
    (hb : ∀ w ∈ S, ∀ μ, lo ≤ w μ / (N : ℤ) ∧ w μ / (N : ℤ) ≤ hi) {u u' : Fin d → ℤ}
    (hu : u ∈ S) (hu' : u' ∈ S) :
    blockProjMatrix d ℓ N m (castTorus ℓ u) (castTorus ℓ u') = projZ d N u u' := by
  unfold blockProjMatrix projZ
  rw [blockMap_castTorus_div hℓ hN, blockMap_castTorus_div hℓ hN]
  have hiff : castTorus m (fun i => u i / (N : ℤ)) = castTorus m (fun i => u' i / (N : ℤ)) ↔
      ∀ μ, u μ / (N : ℤ) = u' μ / (N : ℤ) := by
    rw [castTorus_eq_iff, funext_iff]
    intro μ
    have h1 := hb u hu μ
    have h2 := hb u' hu' μ
    rw [abs_lt]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  simp only [hiff]

theorem blockProjMatrix_castTorus {ℓ N m R : ℕ} [NeZero ℓ] [NeZero m] (hℓ : ℓ = N * m)
    (hN : 0 < N) (hm : 2 * R < m) {u u' : Fin d → ℤ} (hu : u ∈ sqBox d R) (hu' : u' ∈ sqBox d R) :
    blockProjMatrix d ℓ N m (castTorus ℓ u) (castTorus ℓ u') = projZ d N u u' := by
  refine blockProjMatrix_castTorus_of_ediv_bounds (lo := -(R : ℤ)) (hi := R) hℓ hN
    (by have : ((2 * R : ℕ) : ℤ) < m := by exact_mod_cast hm
        push_cast at this; linarith) (S := (sqBox d R : Set (Fin d → ℤ))) ?_ hu hu'
  intro w hw μ
  have h1 := abs_ediv_le (a := w μ) hN
  have h3 := mem_sqBox.1 (Finset.mem_coe.1 hw) μ
  exact abs_le.1 (h1.trans h3)

theorem blockProjMatrix_castTorus_fine {ℓ N m R Rm : ℕ} [NeZero ℓ] [NeZero m] (hℓ : ℓ = N * m)
    (hN : 0 < N) (hm : 2 * Rm + 1 < m) (hR : R < N * (Rm + 1)) {u u' : Fin d → ℤ}
    (hu : u ∈ sqBox d R) (hu' : u' ∈ sqBox d R) :
    blockProjMatrix d ℓ N m (castTorus ℓ u) (castTorus ℓ u') = projZ d N u u' := by
  have hN' : (0 : ℤ) < N := by exact_mod_cast hN
  have hRz : (R : ℤ) < N * (Rm + 1) := by exact_mod_cast hR
  refine blockProjMatrix_castTorus_of_ediv_bounds (lo := -((Rm : ℤ) + 1)) (hi := Rm) hℓ hN
    (by have : ((2 * Rm + 1 : ℕ) : ℤ) < m := by exact_mod_cast hm
        push_cast at this; linarith) (S := (sqBox d R : Set (Fin d → ℤ))) ?_ hu hu'
  intro w hw μ
  have h1 := abs_le.1 (mem_sqBox.1 (Finset.mem_coe.1 hw) μ)
  constructor
  · rw [Int.le_ediv_iff_mul_le hN']
    nlinarith [h1.1]
  · have : w μ / (N : ℤ) < (Rm : ℤ) + 1 := by
      rw [Int.ediv_lt_iff_lt_mul hN']
      nlinarith [h1.2]
    omega

theorem fineHamiltonian_castTorus_fine {ℓ N m R Rm : ℕ} [NeZero ℓ] [NeZero m] (hℓ : ℓ = N * m)
    (hN : 0 < N) (hm : 2 * Rm + 1 < m) (hR : R < N * (Rm + 1)) (ν a : ℝ) {u u' : Fin d → ℤ}
    (hu : u ∈ sqBox d R) (hu' : u' ∈ sqBox d R) :
    fineHamiltonian d ℓ N m ν a (castTorus ℓ u) (castTorus ℓ u') =
      (N : ℝ) ^ 2 * latZ d (ν / (N : ℝ) ^ 2) u u' + a * projZ d N u u' := by
  have hs : 2 * R + 1 < ℓ := by
    rw [hℓ]; nlinarith
  unfold fineHamiltonian
  rw [Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul,
    latticeLaplacian_castTorus hs _ hu hu', blockProjMatrix_castTorus_fine hℓ hN hm hR hu hu']

theorem fineHamiltonian_castTorus {ℓ N m R : ℕ} [NeZero ℓ] [NeZero m] (hℓ : ℓ = N * m)
    (hN : 0 < N) (hm : 2 * R + 1 < m) (ν a : ℝ) {u u' : Fin d → ℤ} (hu : u ∈ sqBox d R)
    (hu' : u' ∈ sqBox d R) :
    fineHamiltonian d ℓ N m ν a (castTorus ℓ u) (castTorus ℓ u') =
      (N : ℝ) ^ 2 * latZ d (ν / (N : ℝ) ^ 2) u u' + a * projZ d N u u' :=
  fineHamiltonian_castTorus_fine hℓ hN hm (by nlinarith) ν a hu hu'

end Entries

section Bounds

variable {d N₀ L k : ℕ} [NeZero N₀] [NeZero L]

theorem abs_latticeLaplacian_le {ℓ : ℕ} [NeZero ℓ] {ν : ℝ} (hν : 0 ≤ ν) (x y : Torus d ℓ) :
    |latticeLaplacian d ℓ ν x y| ≤ 4 * d + ν := by
  unfold latticeLaplacian
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.sum_apply,
    Matrix.add_apply, Matrix.transpose_apply, shiftMatrix, smul_eq_mul]
  refine (abs_sub _ _).trans ?_
  have h1 : |(2 * (d : ℝ) + ν) * (if x = y then (1 : ℝ) else 0)| ≤ 2 * d + ν := by
    split_ifs
    · rw [mul_one, abs_of_nonneg (by positivity)]
    · simp; positivity
  have h2 : |∑ μ : Fin d, ((if y = x + Pi.single μ 1 then (1 : ℝ) else 0) +
      (if x = y + Pi.single μ 1 then (1 : ℝ) else 0))| ≤ 2 * d := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc _ ≤ ∑ _μ : Fin d, (2 : ℝ) := Finset.sum_le_sum fun μ _ => by
          split_ifs <;> norm_num
      _ = 2 * d := by simp [mul_comm]
  linarith

theorem torusDist_le_one_of_laplacian_ne_zero {ν : ℝ} {x y : Torus d (N₀ * L ^ k)}
    (h : latticeLaplacian d (N₀ * L ^ k) ν x y ≠ 0) : torusDist d (N₀ * L ^ k) x y ≤ 1 := by
  by_contra hc
  push Not at hc
  apply h
  have hxy : x ≠ y := by
    rintro rfl
    rw [torusDist_self_eq_zero] at hc
    linarith
  have hadj : ∀ μ : Fin d, y ≠ x + Pi.single μ 1 ∧ x ≠ y + Pi.single μ 1 := fun μ =>
    ⟨fun e => absurd (Balaban.Multiscale.Adj.torusDist_le (L := L) (k := k) ⟨μ, Or.inl e⟩)
      (not_le.2 hc), fun e => absurd (Balaban.Multiscale.Adj.torusDist_le (L := L) (k := k)
      ⟨μ, Or.inr e⟩) (not_le.2 hc)⟩
  unfold latticeLaplacian
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.sum_apply,
    Matrix.add_apply, Matrix.transpose_apply, shiftMatrix, smul_eq_mul, hxy, ite_false,
    mul_zero, zero_sub, neg_eq_zero]
  refine Finset.sum_eq_zero fun μ _ => ?_
  simp [(hadj μ).1, (hadj μ).2]

theorem abs_blockProjMatrix_le {ℓ N m : ℕ} [NeZero ℓ] (hN : 0 < N) (x y : Torus d ℓ) :
    |blockProjMatrix d ℓ N m x y| ≤ 1 := by
  unfold blockProjMatrix
  split_ifs
  · rw [abs_of_nonneg (by positivity)]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by exact_mod_cast hN))
  · simp

theorem torusDist_fineHamiltonian_ne_zero (ν a : ℝ) {x y : Torus d (N₀ * L ^ k)}
    (h : fineHamiltonian d (N₀ * L ^ k) (L ^ k) N₀ ν a x y ≠ 0) :
    torusDist d (N₀ * L ^ k) x y ≤ d * ((L ^ k : ℕ) : ℝ) + 1 := by
  have hN : 0 < L ^ k := Nat.pos_of_ne_zero (pow_ne_zero _ (NeZero.ne L))
  have hℓ : N₀ * L ^ k = L ^ k * N₀ := mul_comm _ _
  have hNr : (0 : ℝ) ≤ d * ((L ^ k : ℕ) : ℝ) := by positivity
  unfold fineHamiltonian at h
  rw [Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul] at h
  by_cases h1 : latticeLaplacian d (N₀ * L ^ k) (ν / ((L ^ k : ℕ) : ℝ) ^ 2) x y = 0
  · have h2 : blockProjMatrix d (N₀ * L ^ k) (L ^ k) N₀ x y ≠ 0 := by
      intro h2; apply h; rw [h1, h2]; ring
    have h3 : blockMap (L ^ k) N₀ x = blockMap (L ^ k) N₀ y := by
      by_contra h3
      apply h2
      simp [blockProjMatrix, h3]
    have := torusDist_le_of_blockMap_eq hℓ hN h3
    linarith
  · have := torusDist_le_one_of_laplacian_ne_zero (L := L) (k := k) h1
    linarith

theorem abs_fineHamiltonian_le {ν a : ℝ} (hν : 0 ≤ ν) (ha0 : 0 ≤ a) (ha2 : a ≤ 2)
    (x y : Torus d (N₀ * L ^ k)) :
    |fineHamiltonian d (N₀ * L ^ k) (L ^ k) N₀ ν a x y| ≤
      4 * d * ((L ^ k : ℕ) : ℝ) ^ 2 + ν + 2 := by
  have hN : 0 < L ^ k := Nat.pos_of_ne_zero (pow_ne_zero _ (NeZero.ne L))
  have hNr : (0 : ℝ) < ((L ^ k : ℕ) : ℝ) := by exact_mod_cast hN
  unfold fineHamiltonian
  rw [Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((L ^ k : ℕ) : ℝ) ^ 2),
    abs_of_nonneg ha0]
  have h1 := abs_latticeLaplacian_le (d := d) (ℓ := N₀ * L ^ k)
    (ν := ν / ((L ^ k : ℕ) : ℝ) ^ 2) (by positivity) x y
  have h2 := abs_blockProjMatrix_le (d := d) (ℓ := N₀ * L ^ k) (m := N₀) hN x y
  have h3 : ((L ^ k : ℕ) : ℝ) ^ 2 * |latticeLaplacian d (N₀ * L ^ k)
      (ν / ((L ^ k : ℕ) : ℝ) ^ 2) x y| ≤
      ((L ^ k : ℕ) : ℝ) ^ 2 * (4 * d + ν / ((L ^ k : ℕ) : ℝ) ^ 2) :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  have h4 : ((L ^ k : ℕ) : ℝ) ^ 2 * (4 * d + ν / ((L ^ k : ℕ) : ℝ) ^ 2) =
      4 * d * ((L ^ k : ℕ) : ℝ) ^ 2 + ν := by field_simp
  have h6 := abs_nonneg (blockProjMatrix d (N₀ * L ^ k) (L ^ k) N₀ x y)
  have h5 : a * |blockProjMatrix d (N₀ * L ^ k) (L ^ k) N₀ x y| ≤ 2 := by nlinarith
  linarith

/-- Exponential decay of the entries of the fine operator, with rate `1`. -/
theorem fineHamiltonian_decay {ν a : ℝ} (hν : 0 ≤ ν) (ha0 : 0 ≤ a) (ha2 : a ≤ 2)
    (x y : Torus d (N₀ * L ^ k)) :
    |fineHamiltonian d (N₀ * L ^ k) (L ^ k) N₀ ν a x y| ≤
      (4 * d * ((L ^ k : ℕ) : ℝ) ^ 2 + ν + 2) * Real.exp (d * ((L ^ k : ℕ) : ℝ) + 1) *
        Real.exp (-1 * torusDist d (N₀ * L ^ k) x y) := by
  have hB := abs_fineHamiltonian_le (L := L) (k := k) hν ha0 ha2 x y
  have hBn : 0 ≤ 4 * d * ((L ^ k : ℕ) : ℝ) ^ 2 + ν + 2 := by positivity
  by_cases h : fineHamiltonian d (N₀ * L ^ k) (L ^ k) N₀ ν a x y = 0
  · rw [h, abs_zero]; positivity
  · have hD := torusDist_fineHamiltonian_ne_zero (L := L) (k := k) ν a h
    have h1 : 1 ≤ Real.exp (d * ((L ^ k : ℕ) : ℝ) + 1) * Real.exp (-1 * torusDist d (N₀ * L ^ k) x y) := by
      rw [← Real.exp_add]
      apply Real.one_le_exp
      linarith
    calc _ ≤ 4 * d * ((L ^ k : ℕ) : ℝ) ^ 2 + ν + 2 := hB
      _ ≤ (4 * d * ((L ^ k : ℕ) : ℝ) ^ 2 + ν + 2) * (Real.exp (d * ((L ^ k : ℕ) : ℝ) + 1) *
          Real.exp (-1 * torusDist d (N₀ * L ^ k) x y)) := le_mul_of_one_le_right hBn h1
      _ = _ := by ring

theorem fineHamiltonian_coercive (hd : 0 < d) {ℓ N m : ℕ} [NeZero ℓ] [NeZero m] (hℓ : ℓ = N * m)
    (hN : 0 < N) {ν a : ℝ} (hν : 0 ≤ ν) (ha : 1 / 2 ≤ a) (φ : Torus d ℓ → ℝ) :
    min (2 / (d : ℝ)) (1 / 2) * ∑ x, φ x ^ 2 ≤ φ ⬝ᵥ fineHamiltonian d ℓ N m ν a *ᵥ φ := by
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hdr : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have h := blockHamiltonian_coercive_real hℓ hN hd (ν / (N : ℝ) ^ 2) (a / (N : ℝ) ^ 2) φ
  rw [fineHamiltonian_eq hN, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  have hS : 0 ≤ ∑ x, φ x ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hN2 : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
  have hmin : min (2 / (d : ℝ)) (1 / 2) ≤ (N : ℝ) ^ 2 * (min (2 / ((d : ℝ) * (N : ℝ) ^ 2))
      (a / (N : ℝ) ^ 2) + ν / (N : ℝ) ^ 2) := by
    rw [mul_add, mul_div_cancel₀ _ hN2.ne']
    have : (N : ℝ) ^ 2 * min (2 / ((d : ℝ) * (N : ℝ) ^ 2)) (a / (N : ℝ) ^ 2) =
        min (2 / (d : ℝ)) a := by
      rw [mul_min_of_nonneg _ _ hN2.le]
      congr 1
      · field_simp
      · field_simp
    rw [this]
    have : min (2 / (d : ℝ)) (1 / 2) ≤ min (2 / (d : ℝ)) a := min_le_min le_rfl ha
    linarith
  calc _ ≤ (N : ℝ) ^ 2 * (min (2 / ((d : ℝ) * (N : ℝ) ^ 2)) (a / (N : ℝ) ^ 2) +
        ν / (N : ℝ) ^ 2) * ∑ x, φ x ^ 2 := mul_le_mul_of_nonneg_right hmin hS
    _ = (N : ℝ) ^ 2 * ((min (2 / ((d : ℝ) * (N : ℝ) ^ 2)) (a / (N : ℝ) ^ 2) +
        ν / (N : ℝ) ^ 2) * ∑ x, φ x ^ 2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h hN2.le

end Bounds

section FineFamily

variable {d L k : ℕ} [NeZero L]

theorem le_fineSide (j : ℕ) : j ≤ L * (j + 1) * L ^ k := by
  have hL : 1 ≤ L := Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hN : 1 ≤ L ^ k := Nat.one_le_pow _ _ hL
  calc j ≤ j + 1 := Nat.le_succ j
    _ ≤ L * (j + 1) := Nat.le_mul_of_pos_left _ hL
    _ ≤ L * (j + 1) * L ^ k := Nat.le_mul_of_pos_right _ hN

theorem le_coarseSide (j : ℕ) : j + 1 ≤ L * (j + 1) :=
  Nat.le_mul_of_pos_left _ (Nat.one_le_iff_ne_zero.2 (NeZero.ne L))

/-- **Cauchy property of the fine Green function.**  The entries of `H_j⁻¹`,
`H_j = -N²Δ + ν + a P` on the torus of side `L (j+1) L^k`, at the images of sites of `ℤ^d`, form
Cauchy sequences in `j`, uniformly on cubes. -/
theorem fineGreen_cauchy (hd : 0 < d) {ν a : ℝ} (hν : 0 ≤ ν) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2)
    (R₀ : ℕ) (η : ℝ) (hη : 0 < η) :
    ∃ j₀ : ℕ, ∀ j₁, j₀ ≤ j₁ → ∀ j₂, j₀ ≤ j₂ → ∀ u ∈ sqBox d R₀, ∀ u' ∈ sqBox d R₀,
      |(fineHamiltonian d (L * (j₁ + 1) * L ^ k) (L ^ k) (L * (j₁ + 1)) ν a)⁻¹
          (castTorus (L * (j₁ + 1) * L ^ k) u) (castTorus (L * (j₁ + 1) * L ^ k) u') -
        (fineHamiltonian d (L * (j₂ + 1) * L ^ k) (L ^ k) (L * (j₂ + 1)) ν a)⁻¹
          (castTorus (L * (j₂ + 1) * L ^ k) u) (castTorus (L * (j₂ + 1) * L ^ k) u')| ≤ η := by
  have hN : 0 < L ^ k := Nat.pos_of_ne_zero (pow_ne_zero _ (NeZero.ne L))
  have hL : 1 ≤ L := Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  have hγ : 0 < min (2 / (d : ℝ)) (1 / 2) := lt_min (by positivity) (by norm_num)
  have hc : 0 ≤ (4 * d * ((L ^ k : ℕ) : ℝ) ^ 2 + ν + 2) * Real.exp (d * ((L ^ k : ℕ) : ℝ) + 1) :=
    by positivity
  have : ∀ j : ℕ, NeZero (L * (j + 1) * L ^ k) := fun j => inferInstance
  refine cauchy_inv_entries (d := d) hc one_pos hγ (fun j => L * (j + 1) * L ^ k)
    (fun j => le_fineSide j)
    (fun j => fineHamiltonian d (L * (j + 1) * L ^ k) (L ^ k) (L * (j + 1)) ν a) ?_ ?_ ?_ R₀ η hη
  · intro j x y
    have := fineHamiltonian_decay (N₀ := L * (j + 1)) (L := L) (k := k) hν (by linarith) ha2 x y
    simpa [mul_assoc] using this
  · intro j φ
    exact fineHamiltonian_coercive hd (mul_comm _ _) hN hν ha1 φ
  · intro R ε hε
    refine ⟨2 * R + 1, fun j₁ hj₁ j₂ hj₂ u hu u' hu' => ?_⟩
    have hm₁ : 2 * R + 1 < L * (j₁ + 1) :=
      lt_of_lt_of_le (by omega) (le_coarseSide (L := L) j₁)
    have hm₂ : 2 * R + 1 < L * (j₂ + 1) :=
      lt_of_lt_of_le (by omega) (le_coarseSide (L := L) j₂)
    rw [fineHamiltonian_castTorus (mul_comm _ _) hN hm₁ ν a hu hu',
      fineHamiltonian_castTorus (mul_comm _ _) hN hm₂ ν a hu hu', sub_self, abs_zero]
    exact hε.le

end FineFamily

section Fibres

variable {d : ℕ}

theorem card_intFibre (N : ℕ) (y : Fin d → ℤ) : (intFibre N y).card = N ^ d := by
  unfold intFibre
  rw [Fintype.card_piFinset]
  simp [Int.card_Ico]

theorem intFibre_subset_sqBox {N R : ℕ} {y : Fin d → ℤ} (hy : y ∈ sqBox d R) :
    intFibre N y ⊆ sqBox d (N * (R + 1)) := by
  intro x hx
  rw [mem_sqBox]
  intro μ
  have h1 := mem_intFibre.1 hx μ
  have h2 := abs_le.1 (mem_sqBox.1 hy μ)
  have hN : (0 : ℤ) ≤ N := Nat.cast_nonneg N
  rw [abs_le]
  push_cast
  constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2]

theorem blockFibre_castTorus {ℓ N m : ℕ} [NeZero ℓ] [NeZero m] (hℓ : ℓ = N * m) (hN : 0 < N)
    (y : Fin d → ℤ) :
    blockFibre N m (castTorus m y) = (intFibre N y).image (castTorus ℓ) := by
  have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  symm
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · intro x hx
    obtain ⟨x₀, hx₀, rfl⟩ := Finset.mem_image.1 hx
    exact mem_blockFibre.2 (blockMap_castTorus_of_mem hℓ hN hx₀)
  · rw [card_blockFibre hℓ, Finset.card_image_of_injOn (castTorus_injOn hℓ hm y), card_intFibre]

theorem sum_blockFibre_castTorus {ℓ N m : ℕ} [NeZero ℓ] [NeZero m] (hℓ : ℓ = N * m) (hN : 0 < N)
    (y : Fin d → ℤ) (g : Torus d ℓ → ℝ) :
    ∑ x ∈ blockFibre N m (castTorus m y), g x = ∑ x ∈ intFibre N y, g (castTorus ℓ x) := by
  have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  rw [blockFibre_castTorus hℓ hN, Finset.sum_image (castTorus_injOn hℓ hm y)]

theorem mul_blockPullbackMatrix_castTorus {ℓ N m : ℕ} [NeZero ℓ] [NeZero m] (hℓ : ℓ = N * m)
    (hN : 0 < N) (M : Matrix (Torus d ℓ) (Torus d ℓ) ℝ) (x : Torus d ℓ) (y' : Fin d → ℤ) :
    (M * blockPullbackMatrix d ℓ N m) x (castTorus m y') =
      ∑ x'' ∈ intFibre N y', M x (castTorus ℓ x'') := by
  rw [← sum_blockFibre_castTorus hℓ hN y' (fun x'' => M x x'')]
  simp only [Matrix.mul_apply, blockPullbackMatrix, mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  rfl

theorem unconstrainedUnitOperator_castTorus {ℓ N m : ℕ} [NeZero ℓ] [NeZero m] (hℓ : ℓ = N * m)
    (hN : 0 < N) (ν a : ℝ) (y y' : Fin d → ℤ) :
    unconstrainedUnitOperator d ℓ N m ν a (castTorus m y) (castTorus m y') =
      a * (if castTorus m y = castTorus m y' then 1 else 0) - a ^ 2 * (((N : ℝ) ^ d)⁻¹ *
        ∑ x ∈ intFibre N y, ∑ x'' ∈ intFibre N y',
          (fineHamiltonian d ℓ N m ν a)⁻¹ (castTorus ℓ x) (castTorus ℓ x'')) := by
  have e : unconstrainedUnitOperator d ℓ N m ν a (castTorus m y) (castTorus m y') =
      a * (if castTorus m y = castTorus m y' then 1 else 0) -
        a ^ 2 * blockGreenKernel d ℓ N m ν a (castTorus m y) (castTorus m y') := by
    simp only [unconstrainedUnitOperator, blockGreenKernel, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [e, blockGreenKernel_apply, sum_blockFibre_castTorus hℓ hN y]
  congr 3
  refine Finset.sum_congr rfl fun x _ => ?_
  exact mul_blockPullbackMatrix_castTorus hℓ hN _ _ y'

theorem fineToBlockKernel_castTorus {ℓ N m : ℕ} [NeZero ℓ] [NeZero m] (hℓ : ℓ = N * m)
    (hN : 0 < N) (ν a : ℝ) (x y' : Fin d → ℤ) :
    fineToBlockKernel d ℓ N m ν a (castTorus ℓ x) (castTorus m y') =
      a * ∑ x'' ∈ intFibre N y', (fineHamiltonian d ℓ N m ν a)⁻¹ (castTorus ℓ x)
        (castTorus ℓ x'') := by
  unfold fineToBlockKernel
  rw [Matrix.smul_apply, smul_eq_mul, mul_blockPullbackMatrix_castTorus hℓ hN]

end Fibres

section Kernels

variable {d L k : ℕ} [NeZero L]

/-- Sums over two blocks of an entrywise small difference. -/
theorem abs_sum_sum_sub_le {S S' : Finset (Fin d → ℤ)} {f g : (Fin d → ℤ) → (Fin d → ℤ) → ℝ}
    {η : ℝ} (h : ∀ x ∈ S, ∀ x' ∈ S', |f x x' - g x x'| ≤ η) :
    |∑ x ∈ S, ∑ x' ∈ S', f x x' - ∑ x ∈ S, ∑ x' ∈ S', g x x'| ≤ S.card * S'.card * η := by
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have : ∀ x ∈ S, |∑ x' ∈ S', f x x' - ∑ x' ∈ S', g x x'| ≤ S'.card * η := by
    intro x hx
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc _ ≤ ∑ _x' ∈ S', η := Finset.sum_le_sum fun x' hx' => h x hx x' hx'
      _ = S'.card * η := by simp
  calc _ ≤ ∑ _x ∈ S, (S'.card * η) := Finset.sum_le_sum this
    _ = S.card * S'.card * η := by simp; ring

/-- Cauchy property of `Δ_tr` at sites of `ℤ^d`. -/
theorem unitOperator_cauchy (hd : 0 < d) {ν a : ℝ} (hν : 0 ≤ ν) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2)
    (R₀ : ℕ) (η : ℝ) (hη : 0 < η) :
    ∃ j₀ : ℕ, ∀ j₁, j₀ ≤ j₁ → ∀ j₂, j₀ ≤ j₂ → ∀ y ∈ sqBox d R₀, ∀ y' ∈ sqBox d R₀,
      |unconstrainedUnitOperator d (L * (j₁ + 1) * L ^ k) (L ^ k) (L * (j₁ + 1)) ν a
          (castTorus (L * (j₁ + 1)) y) (castTorus (L * (j₁ + 1)) y') -
        unconstrainedUnitOperator d (L * (j₂ + 1) * L ^ k) (L ^ k) (L * (j₂ + 1)) ν a
          (castTorus (L * (j₂ + 1)) y) (castTorus (L * (j₂ + 1)) y')| ≤ η := by
  have hN : 0 < L ^ k := Nat.pos_of_ne_zero (pow_ne_zero _ (NeZero.ne L))
  have hNr : (0 : ℝ) < ((L ^ k : ℕ) : ℝ) ^ d := by positivity
  set R := L ^ k * (R₀ + 1) with hR
  obtain ⟨j₀', hj₀'⟩ := fineGreen_cauchy (d := d) (L := L) (k := k) hd hν ha1 ha2 R
    (η / (4 * ((L ^ k : ℕ) : ℝ) ^ d)) (by positivity)
  refine ⟨max j₀' (2 * R₀ + 1), fun j₁ hj₁ j₂ hj₂ y hy y' hy' => ?_⟩
  have hj₁a : j₀' ≤ j₁ := (le_max_left _ _).trans hj₁
  have hj₂a : j₀' ≤ j₂ := (le_max_left _ _).trans hj₂
  have hm₁ : 2 * R₀ < L * (j₁ + 1) :=
    lt_of_lt_of_le (by have := (le_max_right _ _).trans hj₁; omega) (le_coarseSide (L := L) j₁)
  have hm₂ : 2 * R₀ < L * (j₂ + 1) :=
    lt_of_lt_of_le (by have := (le_max_right _ _).trans hj₂; omega) (le_coarseSide (L := L) j₂)
  have hℓ₁ : L * (j₁ + 1) * L ^ k = L ^ k * (L * (j₁ + 1)) := mul_comm _ _
  have hℓ₂ : L * (j₂ + 1) * L ^ k = L ^ k * (L * (j₂ + 1)) := mul_comm _ _
  rw [unconstrainedUnitOperator_castTorus hℓ₁ hN, unconstrainedUnitOperator_castTorus hℓ₂ hN]
  have hind : ∀ m : ℕ, 2 * R₀ < m → (castTorus m y = castTorus m y' ↔ y = y') := by
    intro m hm
    refine castTorus_eq_iff fun μ => ?_
    have h1 := abs_le.1 (mem_sqBox.1 hy μ)
    have h2 := abs_le.1 (mem_sqBox.1 hy' μ)
    have h5 : ((2 * R₀ : ℕ) : ℤ) < m := by exact_mod_cast hm
    push_cast at h5
    rw [abs_lt]
    constructor <;> linarith
  simp only [hind _ hm₁, hind _ hm₂]
  have hsum := abs_sum_sum_sub_le (S := intFibre (L ^ k) y) (S' := intFibre (L ^ k) y')
    (f := fun x x'' => (fineHamiltonian d (L * (j₁ + 1) * L ^ k) (L ^ k) (L * (j₁ + 1)) ν a)⁻¹
      (castTorus (L * (j₁ + 1) * L ^ k) x) (castTorus (L * (j₁ + 1) * L ^ k) x''))
    (g := fun x x'' => (fineHamiltonian d (L * (j₂ + 1) * L ^ k) (L ^ k) (L * (j₂ + 1)) ν a)⁻¹
      (castTorus (L * (j₂ + 1) * L ^ k) x) (castTorus (L * (j₂ + 1) * L ^ k) x''))
    (η := η / (4 * ((L ^ k : ℕ) : ℝ) ^ d)) (fun x hx x'' hx'' =>
      hj₀' j₁ hj₁a j₂ hj₂a x (intFibre_subset_sqBox hy hx) x'' (intFibre_subset_sqBox hy' hx''))
  rw [card_intFibre, card_intFibre] at hsum
  set X₁ := ∑ x ∈ intFibre (L ^ k) y, ∑ x'' ∈ intFibre (L ^ k) y',
    (fineHamiltonian d (L * (j₁ + 1) * L ^ k) (L ^ k) (L * (j₁ + 1)) ν a)⁻¹
      (castTorus (L * (j₁ + 1) * L ^ k) x) (castTorus (L * (j₁ + 1) * L ^ k) x'')
  set X₂ := ∑ x ∈ intFibre (L ^ k) y, ∑ x'' ∈ intFibre (L ^ k) y',
    (fineHamiltonian d (L * (j₂ + 1) * L ^ k) (L ^ k) (L * (j₂ + 1)) ν a)⁻¹
      (castTorus (L * (j₂ + 1) * L ^ k) x) (castTorus (L * (j₂ + 1) * L ^ k) x'')
  have e : a * (if y = y' then (1 : ℝ) else 0) - a ^ 2 * ((((L ^ k : ℕ) : ℝ) ^ d)⁻¹ * X₁) -
      (a * (if y = y' then (1 : ℝ) else 0) - a ^ 2 * ((((L ^ k : ℕ) : ℝ) ^ d)⁻¹ * X₂)) =
      -(a ^ 2 * (((L ^ k : ℕ) : ℝ) ^ d)⁻¹) * (X₁ - X₂) := by ring
  rw [e, abs_mul, abs_neg]
  have h1 : |a ^ 2 * (((L ^ k : ℕ) : ℝ) ^ d)⁻¹| ≤ 4 * (((L ^ k : ℕ) : ℝ) ^ d)⁻¹ := by
    rw [abs_of_nonneg (by positivity)]
    have : a ^ 2 ≤ 4 := by nlinarith
    exact mul_le_mul_of_nonneg_right this (by positivity)
  have h2 : |X₁ - X₂| ≤ (((L ^ k : ℕ) : ℝ) ^ d) * (((L ^ k : ℕ) : ℝ) ^ d) *
      (η / (4 * ((L ^ k : ℕ) : ℝ) ^ d)) := by
    have := hsum
    simp only [Nat.cast_pow] at this ⊢
    exact this
  calc _ ≤ 4 * (((L ^ k : ℕ) : ℝ) ^ d)⁻¹ * ((((L ^ k : ℕ) : ℝ) ^ d) * (((L ^ k : ℕ) : ℝ) ^ d) *
        (η / (4 * ((L ^ k : ℕ) : ℝ) ^ d))) := mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
    _ = η := by field_simp

/-- Cauchy property of the fine-to-block kernel `a G Q*` at sites of `ℤ^d`. -/
theorem fineKernel_cauchy (hd : 0 < d) {ν a : ℝ} (hν : 0 ≤ ν) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2)
    (R₀ : ℕ) (η : ℝ) (hη : 0 < η) :
    ∃ j₀ : ℕ, ∀ j₁, j₀ ≤ j₁ → ∀ j₂, j₀ ≤ j₂ → ∀ x ∈ sqBox d R₀, ∀ y' ∈ sqBox d R₀,
      |fineToBlockKernel d (L * (j₁ + 1) * L ^ k) (L ^ k) (L * (j₁ + 1)) ν a
          (castTorus (L * (j₁ + 1) * L ^ k) x) (castTorus (L * (j₁ + 1)) y') -
        fineToBlockKernel d (L * (j₂ + 1) * L ^ k) (L ^ k) (L * (j₂ + 1)) ν a
          (castTorus (L * (j₂ + 1) * L ^ k) x) (castTorus (L * (j₂ + 1)) y')| ≤ η := by
  have hN : 0 < L ^ k := Nat.pos_of_ne_zero (pow_ne_zero _ (NeZero.ne L))
  have hNr : (0 : ℝ) < ((L ^ k : ℕ) : ℝ) ^ d := by positivity
  set R := L ^ k * (R₀ + 1) with hR
  have hR₀ : R₀ ≤ R := by
    rw [hR]; nlinarith [Nat.one_le_iff_ne_zero.2 hN.ne']
  obtain ⟨j₀, hj₀⟩ := fineGreen_cauchy (d := d) (L := L) (k := k) hd hν ha1 ha2 R
    (η / (2 * ((L ^ k : ℕ) : ℝ) ^ d)) (by positivity)
  refine ⟨j₀, fun j₁ hj₁ j₂ hj₂ x hx y' hy' => ?_⟩
  have hℓ₁ : L * (j₁ + 1) * L ^ k = L ^ k * (L * (j₁ + 1)) := mul_comm _ _
  have hℓ₂ : L * (j₂ + 1) * L ^ k = L ^ k * (L * (j₂ + 1)) := mul_comm _ _
  rw [fineToBlockKernel_castTorus hℓ₁ hN, fineToBlockKernel_castTorus hℓ₂ hN, ← mul_sub,
    ← Finset.sum_sub_distrib, abs_mul]
  have h1 : |a| ≤ 2 := by rw [abs_of_nonneg (by linarith)]; exact ha2
  have h2 : |∑ x'' ∈ intFibre (L ^ k) y',
      ((fineHamiltonian d (L * (j₁ + 1) * L ^ k) (L ^ k) (L * (j₁ + 1)) ν a)⁻¹
        (castTorus (L * (j₁ + 1) * L ^ k) x) (castTorus (L * (j₁ + 1) * L ^ k) x'') -
      (fineHamiltonian d (L * (j₂ + 1) * L ^ k) (L ^ k) (L * (j₂ + 1)) ν a)⁻¹
        (castTorus (L * (j₂ + 1) * L ^ k) x) (castTorus (L * (j₂ + 1) * L ^ k) x''))| ≤
      (((L ^ k : ℕ) : ℝ) ^ d) * (η / (2 * ((L ^ k : ℕ) : ℝ) ^ d)) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc _ ≤ ∑ _x'' ∈ intFibre (L ^ k) y', η / (2 * ((L ^ k : ℕ) : ℝ) ^ d) :=
          Finset.sum_le_sum fun x'' hx'' => hj₀ j₁ hj₁ j₂ hj₂ x (sqBox_mono hR₀ hx) x''
            (intFibre_subset_sqBox hy' hx'')
      _ = _ := by rw [Finset.sum_const, card_intFibre, nsmul_eq_mul]; push_cast; ring
  calc _ ≤ 2 * ((((L ^ k : ℕ) : ℝ) ^ d) * (η / (2 * ((L ^ k : ℕ) : ℝ) ^ d))) :=
        mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)
    _ = η := by field_simp

/-- **Cauchy property of `C_tr`** at sites of `ℤ^d`. -/
theorem coarseGreen_cauchy_of_nonneg (hd : 0 < d) (hk : 1 ≤ k) {ν a a' : ℝ} (hν0 : 0 ≤ ν)
    (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (ha'1 : 1 / 2 ≤ a') (ha'2 : a' ≤ 2)
    (R₀ : ℕ) (η : ℝ) (hη : 0 < η) :
    ∃ j₀ : ℕ, ∀ j₁, j₀ ≤ j₁ → ∀ j₂, j₀ ≤ j₂ → ∀ y ∈ sqBox d R₀, ∀ y' ∈ sqBox d R₀,
      |(coarseOperator d (L * (j₁ + 1) * L ^ k) (L ^ k) (L * (j₁ + 1)) L (j₁ + 1) ν a a')⁻¹
          (castTorus (L * (j₁ + 1)) y) (castTorus (L * (j₁ + 1)) y') -
        (coarseOperator d (L * (j₂ + 1) * L ^ k) (L ^ k) (L * (j₂ + 1)) L (j₂ + 1) ν a a')⁻¹
          (castTorus (L * (j₂ + 1)) y) (castTorus (L * (j₂ + 1)) y')| ≤ η := by
  have hN : 0 < L ^ k := Nat.pos_of_ne_zero (pow_ne_zero _ (NeZero.ne L))
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hγ := trGamma_pos (L := L) hd
  have hδ := blockDecayRate_pos hd
  have hc := trC0_nonneg (L := L) hd
  have : ∀ j : ℕ, NeZero (L * (j + 1)) := fun j => inferInstance
  refine cauchy_inv_entries (d := d) hc hδ hγ (fun j => L * (j + 1))
    (fun j => le_trans (Nat.le_succ j) (le_coarseSide (L := L) j))
    (fun j => coarseOperator d (L * (j + 1) * L ^ k) (L ^ k) (L * (j + 1)) L (j + 1) ν a a')
    ?_ ?_ ?_ R₀ η hη
  · intro j x y
    have := coarseOperator_entry (L := L) (N₀ := L * (j + 1)) (k := k) (M := j + 1) hd hk rfl hν0
      ha1 ha2 ha'1 ha'2 x y
    rwa [neg_mul]
  · intro j φ
    exact coarseOperator_form_of_nonneg hd (mul_comm _ _) hN rfl hν0 ha1 ha'1 φ
  · intro R ε hε
    obtain ⟨j₀, hj₀⟩ := unitOperator_cauchy (d := d) (L := L) (k := k) hd hν0 ha1 ha2 R ε hε
    refine ⟨max j₀ (2 * R + 1), fun j₁ hj₁ j₂ hj₂ u hu u' hu' => ?_⟩
    have hm₁ : 2 * R < j₁ + 1 := by have := (le_max_right _ _).trans hj₁; omega
    have hm₂ : 2 * R < j₂ + 1 := by have := (le_max_right _ _).trans hj₂; omega
    have hp₁ := blockProjMatrix_castTorus (d := d) (ℓ := L * (j₁ + 1)) (N := L) (m := j₁ + 1)
      rfl hL hm₁ hu hu'
    have hp₂ := blockProjMatrix_castTorus (d := d) (ℓ := L * (j₂ + 1)) (N := L) (m := j₂ + 1)
      rfl hL hm₂ hu hu'
    have h := hj₀ j₁ ((le_max_left _ _).trans hj₁) j₂ ((le_max_left _ _).trans hj₂) u hu u' hu'
    unfold coarseOperator
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, hp₁, hp₂]
    have e : ∀ A B C : ℝ, A + C - (B + C) = A - B := fun A B C => by ring
    rw [e]
    exact h

/-- **Cauchy property of `C_tr`** at sites of `ℤ^d`, the case `ν ≤ 2` of
`coarseGreen_cauchy_of_nonneg`. -/
theorem coarseGreen_cauchy (hd : 0 < d) (hk : 1 ≤ k) {ν a a' : ℝ} (hν0 : 0 ≤ ν) (_hν2 : ν ≤ 2)
    (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (ha'1 : 1 / 2 ≤ a') (ha'2 : a' ≤ 2)
    (R₀ : ℕ) (η : ℝ) (hη : 0 < η) :
    ∃ j₀ : ℕ, ∀ j₁, j₀ ≤ j₁ → ∀ j₂, j₀ ≤ j₂ → ∀ y ∈ sqBox d R₀, ∀ y' ∈ sqBox d R₀,
      |(coarseOperator d (L * (j₁ + 1) * L ^ k) (L ^ k) (L * (j₁ + 1)) L (j₁ + 1) ν a a')⁻¹
          (castTorus (L * (j₁ + 1)) y) (castTorus (L * (j₁ + 1)) y') -
        (coarseOperator d (L * (j₂ + 1) * L ^ k) (L ^ k) (L * (j₂ + 1)) L (j₂ + 1) ν a a')⁻¹
          (castTorus (L * (j₂ + 1)) y) (castTorus (L * (j₂ + 1)) y')| ≤ η :=
  coarseGreen_cauchy_of_nonneg hd hk hν0 ha1 ha2 ha'1 ha'2 R₀ η hη

end Kernels

end Balaban.Green
