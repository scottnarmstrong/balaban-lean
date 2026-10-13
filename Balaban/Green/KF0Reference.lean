/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.FinalHessian
public import Balaban.Green.FinalMassSqrt
public import Balaban.Green.FinalComplexMatrix
public import Balaban.Green.LimitCauchy
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The reference operator of the branch `k_f = 0` (package K1 `KF0Reference`)

When the mass is already large at the start, `ν > (7/8) L⁻²` (stopping index `k_f = 0`), no
block-spin step is performed and the hard-spin integral on the unit torus is done directly around
the constant configuration `h` (`notes/phase1/BASE.md`, `FINAL.md` §1, §3,
`LF-BASE-KF0.md` Lemma A.4, §B.2).  In the tangent spin directions the Hessian at the saddle is
`K_ν = -Δ + ν` on the torus (`latticeLaplacian d m ν`); its completion to all `N` spin components
is `A₀ = K_ν ⊗ (1 - P_h) + P_h`, `P_h = h hᵀ` (`kf0Full`).

## What is proved (all bounds uniform in the torus size `m`)

* `kf0Op d m ν`: the complexification of `K_ν`, typed over `L1Torus d m` (as `finalOp`).
  `kf0Full d m N ν h`: the real matrix `spinLift K_ν * (1 - projH h) + projH h` on
  `(Torus d m) × Fin N`.  Its quadratic form is `⟨(1-P)u, K (1-P)u⟩ + ‖P u‖²` (`kf0Full_form`),
  i.e. tangent part plus the squared normal component.
* Coercivity: `K_ν ≥ ν`, hence `IsCoercive (kf0Op d m ν) g` for every `g ≤ ν`
  (`kf0Op_isCoercive`) and, when `7/8 L⁻² < ν`, with the gap `kf0Gap L = 7/(8 L²)`; for the full
  operator and `ν ≤ 1`: `⟨u, A₀ u⟩ ≥ ν ‖u‖²` and `⟨u, A₀ u⟩ ≥ (4d+1)⁻¹ ⟨u, spinLift K_ν u⟩`
  (`kf0Full_form_ge`, `kf0Full_form_ge_lift`).
* Combes–Thomas decay (route (B), the landed `combesThomas`): for `0 < g ≤ ν ≤ 1`, every `t ≥ 0`,
  `K_ν + t` is invertible and `|(K_ν + t)⁻¹_{xy}| ≤ 2/(g+t) exp(-r dist x y)` with
  `r = kf0RateAt d g = ctRate (e(4d+1)) 1 g (ballConst d (1/4))` (`kf0_resolvent_decay`); with
  `g = kf0Gap L` this is `kf0Rate d L` (`kf0_resolvent_decay_gap`).  The constants depend only on
  `d` and `g`; not on `m`, `ν ∈ [g,1]`, `t`.  The inverse, and `sqrtMat (kf0Op)` (the principal
  inverse square root, `sqrtMat * sqrtMat = inverse`) satisfy the same bounds with `2/g`, resp.
  `2/√g`.
* The full operator: `A₀⁻¹ = spinLift K⁻¹ * (1 - P) + P` (`kf0Full_inv`), the matrix
  `S = kf0Dress (sqrtMat K) h` satisfies `S * S = (kf0FullC)⁻¹` (`kf0FullC_sqrt_mul_self`), and
  `|A₀⁻¹ (x,i) (y,j)| ≤ [x = y] + (2/g) e^{-r d(x,y)}`, same for `S` with `2/√g`.
* The stopping index: `kStop = 0` gives the gap `e^{-ε}·7/(8L²) ≥ (19/20)·kf0Gap L` for the
  PHYSICAL mass `ν` (`kf0_at_stop`).  The note's threshold is on the running mass `n 0`
  (`ν e^{-ε} ≤ n 0 ≤ ν e^{ε}`), so `n 0 > 7/(8L²)` only gives `ν > e^{-ε}·7/(8L²)`.

## What is NOT proved here

This is the reference operator on the full torus at the constant saddle.  Not proved: the
identification with the Hessian of the hard-spin integral in the sphere chart
`φ = h√(1-|ξ|²) + ξ`; the conditional operator on a good region with holes (the crossing-bond term
(B.1) of `LF-BASE-KF0.md`); the cut-local covariance; the last expansion; Root-F's `k_f = 0`
branch.  `KF0OneScaleInput` can consume from this file the gap, the resolvent / inverse / square
root bounds of `K_ν` and of `A₀` on the full torus, but none of those items.

The explicit rate `θ_L = log(1 + 7/(64 d L²))` and the constants `(3ν_*/4 + t)⁻¹` of the note's
(B.3) (route (A), conjugation by `e^{θ d(x,y)}`) are NOT formalized: the rate obtained is the
Combes–Thomas rate `kf0Rate d L`, and the constant is `2/(ν_* + t)`.  The metric is the `ℓ¹` torus
distance `torusDist` (that of `L1Torus`), a quantity comparable to but different from the
note's `d(x,y)` on the unit lattice.
-/

@[expose] public section

open Matrix Finset Kronecker

namespace Balaban

/-! ### Generic algebra of the dressed operator -/

section Generic

variable {𝕜 : Type*} [CommRing 𝕜] {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}

/-- The spin projection `1 ⊗ (h hᵀ)` onto the direction `h`, over a commutative ring. -/
def kf0Proj (ι : Type*) [DecidableEq ι] (h : Fin N → 𝕜) : Matrix (ι × Fin N) (ι × Fin N) 𝕜 :=
  (1 : Matrix ι ι 𝕜) ⊗ₖ Matrix.vecMulVec h h

/-- The dressed operator: `X` acts on the components orthogonal to `h`, the identity on the
`h`-component: `(X ⊗ 1)(1 - P_h) + P_h`. -/
def kf0Dress (X : Matrix ι ι 𝕜) (h : Fin N → 𝕜) : Matrix (ι × Fin N) (ι × Fin N) 𝕜 :=
  (X ⊗ₖ (1 : Matrix (Fin N) (Fin N) 𝕜)) * (1 - kf0Proj ι h) + kf0Proj ι h

theorem qp_mul {n : Type*} [Fintype n] [DecidableEq n] (P X Y : Matrix n n 𝕜) (hPP : P * P = P)
    (hY : P * Y = Y * P) :
    (X * (1 - P) + P) * (Y * (1 - P) + P) = (X * Y) * (1 - P) + P := by
  have hQP : (1 - P) * P = 0 := by rw [Matrix.sub_mul, hPP]; simp
  have hPQ : P * (1 - P) = 0 := by rw [Matrix.mul_sub, hPP]; simp
  have hQY : (1 - P) * Y = Y * (1 - P) := by
    rw [Matrix.sub_mul, Matrix.mul_sub, hY, Matrix.one_mul, Matrix.mul_one]
  have hQQ : (1 - P) * (1 - P) = 1 - P := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, hPP]; simp
  have t1 : X * (1 - P) * (Y * (1 - P)) = X * Y * (1 - P) := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (1 - P) Y, hQY, Matrix.mul_assoc Y, hQQ,
      ← Matrix.mul_assoc]
  have t2 : X * (1 - P) * P = 0 := by rw [Matrix.mul_assoc, hQP, Matrix.mul_zero]
  have t3 : P * (Y * (1 - P)) = 0 := by
    rw [← Matrix.mul_assoc, hY, Matrix.mul_assoc, hPQ, Matrix.mul_zero]
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, t1, t2, t3, hPP]
  simp

theorem kf0Proj_mul_self {h : Fin N → 𝕜} (hh : h ⬝ᵥ h = 1) :
    kf0Proj ι h * kf0Proj ι h = kf0Proj ι h := by
  unfold kf0Proj
  rw [← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.vecMulVec_mul_vecMulVec, hh, one_smul]

theorem kf0_lift_comm (X : Matrix ι ι 𝕜) (h : Fin N → 𝕜) :
    kf0Proj ι h * (X ⊗ₖ (1 : Matrix (Fin N) (Fin N) 𝕜)) =
      (X ⊗ₖ (1 : Matrix (Fin N) (Fin N) 𝕜)) * kf0Proj ι h := by
  unfold kf0Proj
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul,
    Matrix.one_mul, Matrix.mul_one]

/-- `dress X * dress Y = dress (X * Y)`. -/
theorem kf0Dress_mul {h : Fin N → 𝕜} (hh : h ⬝ᵥ h = 1) (X Y : Matrix ι ι 𝕜) :
    kf0Dress X h * kf0Dress Y h = kf0Dress (X * Y) h := by
  unfold kf0Dress
  rw [qp_mul _ _ _ (kf0Proj_mul_self hh) (kf0_lift_comm Y h),
    ← Matrix.mul_kronecker_mul, Matrix.mul_one]

theorem kf0Dress_one (h : Fin N → 𝕜) : kf0Dress (1 : Matrix ι ι 𝕜) h = 1 := by
  unfold kf0Dress
  rw [Matrix.one_kronecker_one, Matrix.one_mul]
  simp

/-- Entries of the dressed operator. -/
theorem kf0Dress_apply (X : Matrix ι ι 𝕜) (h : Fin N → 𝕜) (x y : ι)
    (i j : Fin N) :
    kf0Dress X h (x, i) (y, j) =
      X x y * ((if i = j then 1 else 0) - h i * h j) + (if x = y then 1 else 0) * (h i * h j) := by
  have e : kf0Dress X h = (X ⊗ₖ ((1 : Matrix (Fin N) (Fin N) 𝕜) - Matrix.vecMulVec h h)) +
      ((1 : Matrix ι ι 𝕜) ⊗ₖ Matrix.vecMulVec h h) := by
    unfold kf0Dress kf0Proj
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]
    ext ⟨a, b⟩ ⟨c, e⟩
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.kroneckerMap_apply, Matrix.one_apply]
    ring
  rw [e]
  simp [Matrix.kroneckerMap_apply, Matrix.vecMulVec_apply, Matrix.one_apply]

end Generic

/-- Norm bound on the entries of the dressed operator: the dressed entry is bounded by the
`X`-entry plus the site-diagonal indicator, provided the spin factors are bounded by `1`. -/
theorem kf0Dress_entry_le {𝕜 : Type*} [NormedField 𝕜] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {N : ℕ} (X : Matrix ι ι 𝕜) (h : Fin N → 𝕜)
    (hM : ∀ i j, ‖h i * h j‖ ≤ 1) (hM' : ∀ i j, ‖(if i = j then (1 : 𝕜) else 0) - h i * h j‖ ≤ 1)
    (x y : ι) (i j : Fin N) :
    ‖kf0Dress X h (x, i) (y, j)‖ ≤ ‖X x y‖ + (if x = y then 1 else 0) := by
  rw [kf0Dress_apply X h]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_mul]
    calc ‖X x y‖ * ‖(if i = j then (1 : 𝕜) else 0) - h i * h j‖ ≤ ‖X x y‖ * 1 :=
          mul_le_mul_of_nonneg_left (hM' i j) (norm_nonneg _)
      _ = _ := mul_one _
  · rw [norm_mul]
    by_cases hxy : x = y
    · simpa [hxy] using hM i j
    · simp [hxy]

/-! ### Real objects: `spinLift`, `projH` and the Kronecker form -/

section Real

variable {d m N : ℕ} [NeZero m]

theorem spinLift_eq_kron {ι κ : Type*} (A : Matrix ι κ ℝ) :
    spinLift N A = A ⊗ₖ (1 : Matrix (Fin N) (Fin N) ℝ) := by
  ext ⟨x, i⟩ ⟨y, j⟩
  by_cases hij : i = j <;> simp [spinLift, Matrix.kroneckerMap_apply, hij]

theorem projH_eq_kf0Proj {ι : Type*} [DecidableEq ι] (h : Fin N → ℝ) :
    projH (ι := ι) h = kf0Proj ι h := by
  ext ⟨x, i⟩ ⟨y, j⟩
  by_cases hxy : x = y <;>
    simp [projH, kf0Proj, Matrix.kroneckerMap_apply, Matrix.vecMulVec_apply, hxy]

/-- The reference operator `A₀ = K_ν (1 - P_h) + P_h` on `(Torus d m) × Fin N`, with real entries
(`K_ν = -Δ + ν` acting on every spin component by `spinLift`, `P_h = projH h`). -/
noncomputable def kf0Full (d m N : ℕ) [NeZero m] (ν : ℝ) (h : Fin N → ℝ) :
    Matrix (Torus d m × Fin N) (Torus d m × Fin N) ℝ :=
  spinLift N (latticeLaplacian d m ν) * (1 - projH h) + projH h

theorem kf0Full_eq_dress (ν : ℝ) (h : Fin N → ℝ) :
    kf0Full d m N ν h = kf0Dress (latticeLaplacian d m ν) h := by
  unfold kf0Full kf0Dress
  rw [spinLift_eq_kron, projH_eq_kf0Proj]

theorem spinLift_dress (X : Matrix (Torus d m) (Torus d m) ℝ) (h : Fin N → ℝ) :
    spinLift N X * (1 - projH (ι := Torus d m) h) + projH h = kf0Dress X h := by
  unfold kf0Dress
  rw [spinLift_eq_kron, projH_eq_kf0Proj]

private theorem vec_dot_self {h : Fin N → ℝ} (hh : ∑ i, h i ^ 2 = 1) : h ⬝ᵥ h = 1 := by
  simpa [dotProduct, sq] using hh

/-- **Quadratic form of `A₀`** (T1): `⟨u, A₀ u⟩ = ⟨(1-P)u, K (1-P)u⟩ + ‖P u‖²`: the tangent
Hessian form plus the squared normal component. -/
theorem kf0Full_form {ν : ℝ} {h : Fin N → ℝ} (hh : ∑ i, h i ^ 2 = 1)
    (u : Torus d m × Fin N → ℝ) :
    u ⬝ᵥ kf0Full d m N ν h *ᵥ u =
      (((1 - projH (ι := Torus d m) h) *ᵥ u) ⬝ᵥ
          spinLift N (latticeLaplacian d m ν) *ᵥ ((1 - projH (ι := Torus d m) h) *ᵥ u)) +
        ((projH (ι := Torus d m) h *ᵥ u) ⬝ᵥ (projH (ι := Torus d m) h *ᵥ u)) := by
  set P := projH (ι := Torus d m) h with hP
  have hPt : Pᵀ = P := projH_transpose h
  have hPP : P * P = P := projH_mul_self hh
  have hcK : P * spinLift N (latticeLaplacian d m ν) = spinLift N (latticeLaplacian d m ν) * P :=
    (spinLift_mul_projH _ h).symm
  have hD : kf0Full d m N ν h = Pᵀ * (1 : Matrix (Torus d m × Fin N) (Torus d m × Fin N) ℝ) * P +
      (1 - P)ᵀ * spinLift N (latticeLaplacian d m ν) * (1 - P) := by
    rw [split_mat P _ _ hPt hPP (by simp) hcK]
    unfold kf0Full
    rw [Matrix.one_mul, add_comm]
  rw [hD, Matrix.add_mulVec, dotProduct_add, ← quad_conj, ← quad_conj, Matrix.one_mulVec]
  ring

private theorem spin_quad_ge {ν : ℝ} (w : Torus d m × Fin N → ℝ) :
    ν * (w ⬝ᵥ w) ≤ w ⬝ᵥ spinLift N (latticeLaplacian d m ν) *ᵥ w := by
  rw [spinLift_quad, sum_sq_spin, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [latticeLaplacian_quadratic]
  have hE := latticeEnergy_nonneg (fun y : Torus d m => w (y, i))
  change _ ≤ latticeEnergy (fun y : Torus d m => w (y, i)) + ν * ∑ y, w (y, i) ^ 2
  linarith

private theorem spin_quad_le {ν : ℝ} (w : Torus d m × Fin N → ℝ) :
    w ⬝ᵥ spinLift N (latticeLaplacian d m ν) *ᵥ w ≤ (4 * d + ν) * (w ⬝ᵥ w) := by
  rw [spinLift_quad, sum_sq_spin, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [latticeLaplacian_quadratic]
  have hE := latticeEnergy_le_four_mul (fun y : Torus d m => w (y, i))
  change latticeEnergy (fun y : Torus d m => w (y, i)) + ν * ∑ y, w (y, i) ^ 2 ≤ _
  linarith

private theorem proj_split {h : Fin N → ℝ} (hh : ∑ i, h i ^ 2 = 1) (u : Torus d m × Fin N → ℝ) :
    u ⬝ᵥ u = ((projH (ι := Torus d m) h *ᵥ u) ⬝ᵥ (projH (ι := Torus d m) h *ᵥ u)) +
      (((1 - projH (ι := Torus d m) h) *ᵥ u) ⬝ᵥ ((1 - projH (ι := Torus d m) h) *ᵥ u)) := by
  set P := projH (ι := Torus d m) h with hP
  have hPt : Pᵀ = P := projH_transpose h
  have hPP : P * P = P := projH_mul_self hh
  have h1 : (1 : Matrix (Torus d m × Fin N) (Torus d m × Fin N) ℝ) =
      Pᵀ * 1 * P + (1 - P)ᵀ * 1 * (1 - P) := by
    rw [split_mat P 1 1 hPt hPP (by simp) (by simp)]
    simp
  have e0 := congrArg (fun M : Matrix (Torus d m × Fin N) (Torus d m × Fin N) ℝ => u ⬝ᵥ (M *ᵥ u)) h1
  simp only [Matrix.one_mulVec] at e0
  refine e0.trans ?_
  rw [Matrix.add_mulVec, dotProduct_add, ← quad_conj, ← quad_conj, Matrix.one_mulVec,
    Matrix.one_mulVec]

private theorem lift_split {ν : ℝ} {h : Fin N → ℝ} (hh : ∑ i, h i ^ 2 = 1)
    (u : Torus d m × Fin N → ℝ) :
    u ⬝ᵥ spinLift N (latticeLaplacian d m ν) *ᵥ u =
      ((projH (ι := Torus d m) h *ᵥ u) ⬝ᵥ
          spinLift N (latticeLaplacian d m ν) *ᵥ (projH (ι := Torus d m) h *ᵥ u)) +
        (((1 - projH (ι := Torus d m) h) *ᵥ u) ⬝ᵥ
          spinLift N (latticeLaplacian d m ν) *ᵥ ((1 - projH (ι := Torus d m) h) *ᵥ u)) := by
  set P := projH (ι := Torus d m) h with hP
  have hPt : Pᵀ = P := projH_transpose h
  have hPP : P * P = P := projH_mul_self hh
  have hcK : P * spinLift N (latticeLaplacian d m ν) = spinLift N (latticeLaplacian d m ν) * P :=
    (spinLift_mul_projH _ h).symm
  have hK : spinLift N (latticeLaplacian d m ν) =
      Pᵀ * spinLift N (latticeLaplacian d m ν) * P +
        (1 - P)ᵀ * spinLift N (latticeLaplacian d m ν) * (1 - P) := by
    rw [split_mat P _ _ hPt hPP hcK hcK, ← Matrix.mul_add, add_sub_cancel, Matrix.mul_one]
  conv_lhs => rw [hK]
  rw [Matrix.add_mulVec, dotProduct_add, ← quad_conj, ← quad_conj]

/-- **Coercivity of the full operator** (T2): for `|h| = 1`, `0 ≤ ν ≤ 1`:
`⟨u, A₀ u⟩ ≥ ν ‖u‖²`. -/
theorem kf0Full_form_ge {ν : ℝ} (hν1 : ν ≤ 1) {h : Fin N → ℝ}
    (hh : ∑ i, h i ^ 2 = 1) (u : Torus d m × Fin N → ℝ) :
    ν * (u ⬝ᵥ u) ≤ u ⬝ᵥ kf0Full d m N ν h *ᵥ u := by
  rw [kf0Full_form hh, proj_split hh u]
  set a := (projH (ι := Torus d m) h *ᵥ u) ⬝ᵥ (projH (ι := Torus d m) h *ᵥ u) with ha
  have ha0 : 0 ≤ a := by
    simp only [ha, dotProduct]; exact Finset.sum_nonneg fun _ _ => mul_self_nonneg _
  have := spin_quad_ge (ν := ν) (N := N) (d := d) (m := m) ((1 - projH (ι := Torus d m) h) *ᵥ u)
  nlinarith

/-- **Comparison with the lifted Laplacian** (T2): for `|h| = 1`, `0 ≤ ν ≤ 1`:
`(4d+1)⁻¹ ⟨u, spinLift K_ν u⟩ ≤ ⟨u, A₀ u⟩`. -/
theorem kf0Full_form_ge_lift {ν : ℝ} (hν : 0 ≤ ν) (hν1 : ν ≤ 1) {h : Fin N → ℝ}
    (hh : ∑ i, h i ^ 2 = 1) (u : Torus d m × Fin N → ℝ) :
    (4 * (d : ℝ) + 1)⁻¹ * (u ⬝ᵥ spinLift N (latticeLaplacian d m ν) *ᵥ u) ≤
      u ⬝ᵥ kf0Full d m N ν h *ᵥ u := by
  rw [kf0Full_form hh, lift_split hh u, mul_add]
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hc : (0 : ℝ) < (4 * (d : ℝ) + 1)⁻¹ := by positivity
  have hc1 : (4 * (d : ℝ) + 1)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
  set P := projH (ι := Torus d m) h with hP
  have hpp : 0 ≤ (P *ᵥ u) ⬝ᵥ (P *ᵥ u) := by
    simp only [dotProduct]; exact Finset.sum_nonneg fun _ _ => mul_self_nonneg _
  have hq := spin_quad_ge (ν := ν) (N := N) (d := d) (m := m) ((1 - P) *ᵥ u)
  have hqq : 0 ≤ ((1 - P) *ᵥ u) ⬝ᵥ ((1 - P) *ᵥ u) := by
    simp only [dotProduct]; exact Finset.sum_nonneg fun _ _ => mul_self_nonneg _
  have h1 := spin_quad_le (ν := ν) (N := N) (d := d) (m := m) (P *ᵥ u)
  have h2 : (4 * (d : ℝ) + 1)⁻¹ * ((P *ᵥ u) ⬝ᵥ spinLift N (latticeLaplacian d m ν) *ᵥ (P *ᵥ u))
      ≤ (P *ᵥ u) ⬝ᵥ (P *ᵥ u) := by
    calc _ ≤ (4 * (d : ℝ) + 1)⁻¹ * ((4 * d + 1) * ((P *ᵥ u) ⬝ᵥ (P *ᵥ u))) := by
          refine mul_le_mul_of_nonneg_left (h1.trans ?_) hc.le
          exact mul_le_mul_of_nonneg_right (by linarith) hpp
      _ = _ := by field_simp
  have h3 : (4 * (d : ℝ) + 1)⁻¹ * (((1 - P) *ᵥ u) ⬝ᵥ
      spinLift N (latticeLaplacian d m ν) *ᵥ ((1 - P) *ᵥ u)) ≤
      ((1 - P) *ᵥ u) ⬝ᵥ spinLift N (latticeLaplacian d m ν) *ᵥ ((1 - P) *ᵥ u) := by
    have hnn : 0 ≤ ((1 - P) *ᵥ u) ⬝ᵥ spinLift N (latticeLaplacian d m ν) *ᵥ ((1 - P) *ᵥ u) :=
      le_trans (mul_nonneg hν hqq) hq
    nlinarith
  linarith

end Real

end Balaban

/-! ### The complexified operator over `L1Torus`: coercivity and Combes–Thomas decay -/

namespace Balaban.Green

open Matrix MeasureTheory Set

variable {d m : ℕ} [NeZero m]

/-- The operator `K_ν = -Δ + ν` on the unit torus `(ℤ/m)^d`, as a complex matrix indexed by the
`ℓ¹` torus (`L1Torus`), exactly as `finalOp`. -/
noncomputable abbrev kf0Op (d m : ℕ) [NeZero m] (ν : ℝ) :
    Matrix (L1Torus d m) (L1Torus d m) ℂ :=
  (latticeLaplacian d m ν).map (algebraMap ℝ ℂ)

/-- The gap `ν_* = 7 / (8 L²)` of the branch `k_f = 0`. -/
noncomputable def kf0Gap (L : ℕ) : ℝ := 7 / (8 * (L : ℝ) ^ 2)

/-- The entry constant `e (4d+1)` of `K_ν`, `0 ≤ ν ≤ 1`, against `exp(-dist)`. -/
noncomputable def kf0DecayC (d : ℕ) : ℝ := Real.exp 1 * (4 * (d : ℝ) + 1)

/-- The Combes–Thomas rate for the gap `g`: `ctRate (e(4d+1)) 1 g (ballConst d (1/4))`. -/
noncomputable def kf0RateAt (d : ℕ) (g : ℝ) : ℝ :=
  ctRate (kf0DecayC d) 1 g (ballConst d (1 / 4))

/-- The rate at the gap `ν_* = 7/(8 L²)`. -/
noncomputable def kf0Rate (d L : ℕ) : ℝ := kf0RateAt d (kf0Gap L)

theorem kf0Gap_pos {L : ℕ} (hL : 0 < L) : 0 < kf0Gap L := by
  unfold kf0Gap
  have : (0 : ℝ) < L := by exact_mod_cast hL
  positivity

theorem kf0DecayC_pos (d : ℕ) : 0 < kf0DecayC d := by
  unfold kf0DecayC
  positivity

theorem kf0RateAt_pos (d : ℕ) {g : ℝ} (hg : 0 < g) : 0 < kf0RateAt d g :=
  ctRate_pos (kf0DecayC_pos d).le one_pos hg (ballConst_decay_nonneg (by norm_num))

theorem kf0Rate_pos (d : ℕ) {L : ℕ} (hL : 0 < L) : 0 < kf0Rate d L :=
  kf0RateAt_pos d (kf0Gap_pos hL)

private theorem reQuad_map_ofReal' {ι : Type*} [Fintype ι] [DecidableEq ι] (U : Matrix ι ι ℝ)
    (v : ι → ℂ) :
    reQuad (U.map (algebraMap ℝ ℂ)) v =
      (fun i => (v i).re) ⬝ᵥ U *ᵥ (fun i => (v i).re) +
        (fun i => (v i).im) ⬝ᵥ U *ᵥ (fun i => (v i).im) := by
  unfold reQuad
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Complex.re_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Matrix.map_apply, Complex.coe_algebraMap, Complex.star_def, Complex.mul_re,
    Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- The real quadratic form of `K_ν` is at least `ν ‖ψ‖²` (for any real `ν`). -/
theorem kf0_real_lower (ν : ℝ) (ψ : Torus d m → ℝ) :
    ν * ∑ x, ψ x ^ 2 ≤ ψ ⬝ᵥ latticeLaplacian d m ν *ᵥ ψ := by
  rw [latticeLaplacian_quadratic]
  have hE := latticeEnergy_nonneg ψ
  change _ ≤ latticeEnergy ψ + ν * ∑ x, ψ x ^ 2
  linarith

/-- **Coercivity** (T2): `Re ⟨u, K_ν u⟩ ≥ g ‖u‖²` for every `g ≤ ν`, for complex fields `u`.
With `7/8 L⁻² < ν` take `g = kf0Gap L`. -/
theorem kf0Op_isCoercive {ν g : ℝ} (hg : g ≤ ν) : IsCoercive (kf0Op d m ν) g := by
  intro u
  have hre : ν * ∑ x : L1Torus d m, (u x).re ^ 2 ≤
      (fun i => (u i).re) ⬝ᵥ latticeLaplacian d m ν *ᵥ (fun i => (u i).re) :=
    kf0_real_lower (d := d) (m := m) ν (fun i => (u i).re)
  have him : ν * ∑ x : L1Torus d m, (u x).im ^ 2 ≤
      (fun i => (u i).im) ⬝ᵥ latticeLaplacian d m ν *ᵥ (fun i => (u i).im) :=
    kf0_real_lower (d := d) (m := m) ν (fun i => (u i).im)
  have e0 : reQuad (kf0Op d m ν) u =
      (fun i => (u i).re) ⬝ᵥ latticeLaplacian d m ν *ᵥ (fun i => (u i).re) +
      (fun i => (u i).im) ⬝ᵥ latticeLaplacian d m ν *ᵥ (fun i => (u i).im) :=
    reQuad_map_ofReal' _ u
  rw [e0]
  have e : sqNorm u = ∑ x, (u x).re ^ 2 + ∑ x, (u x).im ^ 2 := by
    unfold sqNorm
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hs : 0 ≤ ∑ x, (u x).re ^ 2 + ∑ x, (u x).im ^ 2 := by
    rw [← e]; exact sqNorm_nonneg u
  rw [e]
  have h1 : 0 ≤ ∑ x, (u x).re ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h2 : 0 ≤ ∑ x, (u x).im ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  nlinarith [mul_nonneg (sub_nonneg.2 hg) h1, mul_nonneg (sub_nonneg.2 hg) h2]

theorem kf0Op_isCoercive_gap {L : ℕ} {ν : ℝ} (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < ν) :
    IsCoercive (kf0Op d m ν) (kf0Gap L) := by
  refine kf0Op_isCoercive (le_of_lt (lt_of_eq_of_lt ?_ hmass))
  unfold kf0Gap; field_simp

/-- A nonzero entry of `-Δ + ν` has `ℓ¹` distance at most `1`. -/
theorem torusDist_le_one_of_ne_zero {ν : ℝ} {x y : Torus d m}
    (h : latticeLaplacian d m ν x y ≠ 0) : torusDist d m x y ≤ 1 := by
  have key : ∀ (a : Torus d m) (μ : Fin d), torusDist d m a (a + Pi.single μ 1) ≤ 1 := by
    intro a μ
    unfold torusDist
    rw [Finset.sum_eq_single μ]
    · simp only [Pi.add_apply, Pi.single_eq_same, sub_add_cancel_left]
      have := natAbs_cycRep_le_of_cast (m := m) (-1 : ZMod m) (-1) (by simp)
      exact_mod_cast this
    · intro i _ hi
      simp [hi, natAbs_cycRep_zero]
    · simp
  have comm : ∀ a b : Torus d m, torusDist d m a b = torusDist d m b a := fun a b =>
    dist_comm (show L1Torus d m from a) b
  by_contra hc
  push Not at hc
  apply h
  have hxy : x ≠ y := by
    rintro rfl
    have : torusDist d m x x = 0 := dist_self (show L1Torus d m from x)
    linarith
  have hadj : ∀ μ : Fin d, y ≠ x + Pi.single μ 1 ∧ x ≠ y + Pi.single μ 1 := fun μ =>
    ⟨fun e => absurd (e ▸ key x μ) (not_le.2 hc),
      fun e => absurd (by rw [comm]; exact e ▸ key y μ) (not_le.2 hc)⟩
  unfold latticeLaplacian
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.sum_apply,
    Matrix.add_apply, Matrix.transpose_apply, shiftMatrix, smul_eq_mul, hxy, ite_false,
    mul_zero, zero_sub, neg_eq_zero]
  refine Finset.sum_eq_zero fun μ _ => ?_
  simp [(hadj μ).1, (hadj μ).2]

/-- Entry decay of `K_ν` for `0 ≤ ν ≤ 1`: `|K_{xy}| ≤ e(4d+1) exp(-dist x y)`. -/
theorem kf0Op_entry {ν : ℝ} (hν0 : 0 ≤ ν) (hν1 : ν ≤ 1) (x y : L1Torus d m) :
    ‖kf0Op d m ν x y‖ ≤ kf0DecayC d * Real.exp (-1 * dist x y) := by
  have e : kf0Op d m ν x y = ((latticeLaplacian d m ν x y : ℝ) : ℂ) := rfl
  rw [e, Complex.norm_real, Real.norm_eq_abs]
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  by_cases hz : latticeLaplacian d m ν x y = 0
  · rw [hz, abs_zero]; unfold kf0DecayC; positivity
  · have hdist : dist x y ≤ 1 := torusDist_le_one_of_ne_zero hz
    have h1 := abs_latticeLaplacian_le hν0 x y
    have h2 : 1 ≤ Real.exp 1 * Real.exp (-1 * dist x y) := by
      rw [← Real.exp_add]; exact Real.one_le_exp (by linarith)
    unfold kf0DecayC
    calc |latticeLaplacian d m ν x y| ≤ 4 * (d : ℝ) + 1 := by linarith
      _ = 1 * (4 * (d : ℝ) + 1) := by ring
      _ ≤ (Real.exp 1 * Real.exp (-1 * dist x y)) * (4 * (d : ℝ) + 1) :=
          mul_le_mul_of_nonneg_right h2 (by positivity)
      _ = _ := by ring

/-- **Resolvent decay** (T3): for `0 < g ≤ ν ≤ 1` and every `t ≥ 0`, `K_ν + t` is invertible and
`|(K_ν + t)⁻¹_{xy}| ≤ 2/(g + t) exp(-r dist x y)`, `r = kf0RateAt d g`, uniformly in the torus
size `m`, in `ν ∈ [g, 1]` and in `t`. -/
theorem kf0_resolvent_decay {ν g : ℝ} (hg0 : 0 < g) (hgν : g ≤ ν) (hν1 : ν ≤ 1) {t : ℝ}
    (ht : 0 ≤ t) :
    IsUnit (kf0Op d m ν + (t : ℂ) • (1 : Matrix (L1Torus d m) (L1Torus d m) ℂ)) ∧
      ∀ x y : L1Torus d m,
        ‖(kf0Op d m ν + (t : ℂ) • (1 : Matrix (L1Torus d m) (L1Torus d m) ℂ))⁻¹ x y‖ ≤
          2 / (g + t) * Real.exp (-kf0RateAt d g * dist x y) := by
  have hK : ∀ x : L1Torus d m, ∑ y, Real.exp (-((1 : ℝ) / 4) * dist x y) ≤
      ballConst d (1 / 4) := fun x => ballSum_L1Torus (d := d) (m := m) (by norm_num) x
  have hκ : 0 ≤ ballConst d (1 / 4) := ballConst_decay_nonneg (by norm_num)
  have := combesThomas (c₀ := kf0DecayC d) (δ₀ := 1) (γ₀ := g) (κ := ballConst d (1 / 4))
    (kf0DecayC_pos d).le one_pos hg0 hκ (kf0Op_entry (by linarith) hν1) hK
    (kf0Op_isCoercive hgν) ht
  refine ⟨this.1, fun x y => ?_⟩
  have h := this.2 x y
  exact h.trans_eq (by simp only [kf0RateAt, div_eq_mul_inv])

/-- Resolvent decay at the gap `ν_* = 7/(8L²)` (T3): for `7/8 L⁻² < ν ≤ 1`. -/
theorem kf0_resolvent_decay_gap {L : ℕ} [NeZero L] {ν : ℝ}
    (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < ν) (hν1 : ν ≤ 1) {t : ℝ} (ht : 0 ≤ t) :
    IsUnit (kf0Op d m ν + (t : ℂ) • (1 : Matrix (L1Torus d m) (L1Torus d m) ℂ)) ∧
      ∀ x y : L1Torus d m,
        ‖(kf0Op d m ν + (t : ℂ) • (1 : Matrix (L1Torus d m) (L1Torus d m) ℂ))⁻¹ x y‖ ≤
          2 / (kf0Gap L + t) * Real.exp (-kf0Rate d L * dist x y) := by
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hgν : kf0Gap L ≤ ν := by
    refine le_of_lt (lt_of_eq_of_lt ?_ hmass)
    unfold kf0Gap; field_simp
  exact kf0_resolvent_decay (kf0Gap_pos hL) hgν hν1 ht

/-- **Inverse decay** (T3). -/
theorem kf0_inverse_decay {ν g : ℝ} (hg0 : 0 < g) (hgν : g ≤ ν) (hν1 : ν ≤ 1)
    (x y : L1Torus d m) :
    ‖(kf0Op d m ν)⁻¹ x y‖ ≤ 2 / g * Real.exp (-kf0RateAt d g * dist x y) := by
  have h := (kf0_resolvent_decay (d := d) (m := m) hg0 hgν hν1 (le_refl (0 : ℝ))).2 x y
  simpa using h

private instance : Nonempty (L1Torus d m) := ⟨(0 : Torus d m)⟩

theorem kf0_resOK {ν g : ℝ} (hg0 : 0 < g) (hgν : g ≤ ν) (hν1 : ν ≤ 1) :
    Localization.ResOK (kf0Op d m ν) := by
  intro x hx
  have := (kf0_resolvent_decay (d := d) (m := m) hg0 hgν hν1 hx).1
  rwa [add_comm] at this

/-- `sqrtMat K_ν` is the principal inverse square root: `sqrtMat * sqrtMat = K_ν⁻¹` (T3). -/
theorem kf0_sqrt_mul_self {ν g : ℝ} (hg0 : 0 < g) (hgν : g ≤ ν) (hν1 : ν ≤ 1) :
    Localization.sqrtMat (kf0Op d m ν) * Localization.sqrtMat (kf0Op d m ν) =
      (kf0Op d m ν)⁻¹ :=
  Localization.sqrtMat_mul_self (kf0_resOK hg0 hgν hν1)

/-- **Inverse square root decay** (T3): `|(K_ν^{-1/2})_{xy}| ≤ 2 g^{-1/2} exp(-r dist x y)`. -/
theorem kf0_sqrt_decay {ν g : ℝ} (hg0 : 0 < g) (hgν : g ≤ ν) (hν1 : ν ≤ 1)
    (x y : L1Torus d m) :
    ‖Localization.sqrtMat (kf0Op d m ν) x y‖ ≤
      2 / Real.sqrt g * Real.exp (-kf0RateAt d g * dist x y) :=
  sqrtMat_entry_le_of_resolvent _ hg0
    (fun _ ht x y => (kf0_resolvent_decay hg0 hgν hν1 ht).2 x y) x y

/-! ### The full operator `A₀`: inverse, inverse square root, entry bounds -/

theorem kf0_isUnit_det (ν : ℝ) (hν : 0 < ν) : IsUnit (latticeLaplacian d m ν).det := by
  rw [isUnit_iff_ne_zero]
  exact (latticeLaplacian_posDef hν).det_pos.ne'

theorem kf0Op_inv {ν : ℝ} (hν : 0 < ν) :
    (kf0Op d m ν)⁻¹ = ((latticeLaplacian d m ν)⁻¹).map (algebraMap ℝ ℂ) := by
  refine Matrix.inv_eq_right_inv ?_
  show (latticeLaplacian d m ν).map (algebraMap ℝ ℂ) *
    ((latticeLaplacian d m ν)⁻¹).map (algebraMap ℝ ℂ) = 1
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ (kf0_isUnit_det ν hν)]
  ext i j
  by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

section FullOp

variable {N : ℕ}

private theorem dot_self_real {h : Fin N → ℝ} (hh : ∑ i, h i ^ 2 = 1) : h ⬝ᵥ h = 1 := by
  simpa [dotProduct, sq] using hh

private theorem dot_self_complex {h : Fin N → ℝ} (hh : ∑ i, h i ^ 2 = 1) :
    (fun i => (h i : ℂ)) ⬝ᵥ (fun i => (h i : ℂ)) = 1 := by
  have : ((∑ i, h i ^ 2 : ℝ) : ℂ) = 1 := by rw [hh]; simp
  push_cast at this
  simpa [dotProduct, sq] using this

private theorem spin_entry_bounds {h : Fin N → ℝ} (hh : ∑ i, h i ^ 2 = 1) (i j : Fin N) :
    |h i * h j| ≤ 1 ∧ |(if i = j then (1 : ℝ) else 0) - h i * h j| ≤ 1 := by
  have hle : ∀ k, h k ^ 2 ≤ 1 := fun k => by
    rw [← hh]
    exact Finset.single_le_sum (f := fun k => h k ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ k)
  have h1 := hle i
  have h2 := hle j
  have hp : |h i * h j| ≤ 1 := by
    rw [abs_le]; constructor <;> nlinarith [sq_nonneg (h i + h j), sq_nonneg (h i - h j)]
  refine ⟨hp, ?_⟩
  by_cases hij : i = j
  · subst hij
    simp only [ite_true]
    rw [abs_le]; constructor <;> nlinarith [sq_nonneg (h i)]
  · simpa [hij] using hp

/-- The reference operator `A₀` with complex entries over `L1Torus`: `K_ν` dressed with the real
unit vector `h` (cast to `ℂ`). -/
noncomputable def kf0FullC (d m N : ℕ) [NeZero m] (ν : ℝ) (h : Fin N → ℝ) :
    Matrix (L1Torus d m × Fin N) (L1Torus d m × Fin N) ℂ :=
  kf0Dress (kf0Op d m ν) (fun i => (h i : ℂ))

/-- **The inverse of `A₀`** (T4): `A₀⁻¹ = spinLift K_ν⁻¹ * (1 - P_h) + P_h` for `ν > 0`, `|h| = 1`. -/
theorem kf0Full_inv {ν : ℝ} (hν : 0 < ν) {h : Fin N → ℝ} (hh : ∑ i, h i ^ 2 = 1) :
    (kf0Full d m N ν h)⁻¹ =
      spinLift N (latticeLaplacian d m ν)⁻¹ * (1 - projH (ι := Torus d m) h) + projH h := by
  rw [spinLift_dress]
  refine Matrix.inv_eq_right_inv ?_
  rw [kf0Full_eq_dress, kf0Dress_mul (dot_self_real hh),
    Matrix.mul_nonsing_inv _ (kf0_isUnit_det ν hν), kf0Dress_one]

theorem kf0Full_isUnit_det {ν : ℝ} (hν : 0 < ν) {h : Fin N → ℝ} (hh : ∑ i, h i ^ 2 = 1) :
    IsUnit (kf0Full d m N ν h).det := by
  refine Matrix.isUnit_det_of_right_inverse (B := kf0Dress (latticeLaplacian d m ν)⁻¹ h) ?_
  rw [kf0Full_eq_dress, kf0Dress_mul (dot_self_real hh),
    Matrix.mul_nonsing_inv _ (kf0_isUnit_det ν hν), kf0Dress_one]

/-- **Entry bound for `A₀⁻¹`** (T4): for `0 < g ≤ ν ≤ 1`, `|h| = 1`:
`|A₀⁻¹ (x,i) (y,j)| ≤ [x = y] + (2/g) exp(-r d(x,y))`, `r = kf0RateAt d g`, `d` the `ℓ¹` torus
distance. -/
theorem kf0Full_inv_entry {ν g : ℝ} (hg0 : 0 < g) (hgν : g ≤ ν) (hν1 : ν ≤ 1) {h : Fin N → ℝ}
    (hh : ∑ i, h i ^ 2 = 1) (x y : Torus d m) (i j : Fin N) :
    ‖(kf0Full d m N ν h)⁻¹ (x, i) (y, j)‖ ≤
      (if x = y then 1 else 0) + 2 / g * Real.exp (-kf0RateAt d g * torusDist d m x y) := by
  have hν : 0 < ν := lt_of_lt_of_le hg0 hgν
  have e : (kf0Full d m N ν h)⁻¹ = kf0Dress (latticeLaplacian d m ν)⁻¹ h := by
    rw [kf0Full_inv hν hh, spinLift_dress]
  rw [e]
  have h1 := kf0Dress_entry_le (latticeLaplacian d m ν)⁻¹ h
    (fun i j => by simpa [Real.norm_eq_abs] using (spin_entry_bounds hh i j).1)
    (fun i j => by simpa [Real.norm_eq_abs] using (spin_entry_bounds hh i j).2) x y i j
  have h2 := kf0_inverse_decay (d := d) (m := m) hg0 hgν hν1 x y
  rw [kf0Op_inv hν] at h2
  have h3 : ‖((latticeLaplacian d m ν)⁻¹) x y‖ ≤
      2 / g * Real.exp (-kf0RateAt d g * torusDist d m x y) := by
    have : (((latticeLaplacian d m ν)⁻¹).map (algebraMap ℝ ℂ)) x y =
        (((latticeLaplacian d m ν)⁻¹ x y : ℝ) : ℂ) := rfl
    rw [this, Complex.norm_real] at h2
    exact h2
  linarith

/-- `S = kf0Dress (sqrtMat K_ν)` squares to `A₀⁻¹` (T4): `S` is the explicit matrix
`spinLift K_ν^{-1/2} * (1 - P_h) + P_h`; it is not identified here with `sqrtMat A₀`. -/
theorem kf0FullC_sqrt_mul_self {ν g : ℝ} (hg0 : 0 < g) (hgν : g ≤ ν) (hν1 : ν ≤ 1)
    {h : Fin N → ℝ} (hh : ∑ i, h i ^ 2 = 1) :
    kf0Dress (Localization.sqrtMat (kf0Op d m ν)) (fun i => (h i : ℂ)) *
        kf0Dress (Localization.sqrtMat (kf0Op d m ν)) (fun i => (h i : ℂ)) =
      (kf0FullC d m N ν h)⁻¹ := by
  have hu : IsUnit (kf0Op d m ν).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 (by
      have := (kf0_resolvent_decay (d := d) (m := m) hg0 hgν hν1 (le_refl (0 : ℝ))).1
      simpa using this)
  rw [kf0Dress_mul (dot_self_complex hh), kf0_sqrt_mul_self hg0 hgν hν1]
  refine (Matrix.inv_eq_right_inv ?_).symm
  unfold kf0FullC
  rw [kf0Dress_mul (dot_self_complex hh), Matrix.mul_nonsing_inv _ hu, kf0Dress_one]

/-- **Entry bound for the inverse square root of `A₀`** (T4): with
`S = kf0Dress (sqrtMat K_ν) h`, `|S (x,i) (y,j)| ≤ [x = y] + (2/√g) exp(-r dist x y)`. -/
theorem kf0FullC_sqrt_entry {ν g : ℝ} (hg0 : 0 < g) (hgν : g ≤ ν) (hν1 : ν ≤ 1)
    {h : Fin N → ℝ} (hh : ∑ i, h i ^ 2 = 1) (x y : L1Torus d m) (i j : Fin N) :
    ‖kf0Dress (Localization.sqrtMat (kf0Op d m ν)) (fun i => (h i : ℂ)) (x, i) (y, j)‖ ≤
      (if x = y then 1 else 0) +
        2 / Real.sqrt g * Real.exp (-kf0RateAt d g * dist x y) := by
  have cast : ∀ r : ℝ, ‖(r : ℂ)‖ = |r| := fun r => by rw [Complex.norm_real, Real.norm_eq_abs]
  have h1 := kf0Dress_entry_le (Localization.sqrtMat (kf0Op d m ν)) (fun i => (h i : ℂ))
    (fun i j => by
      have := (spin_entry_bounds hh i j).1
      rw [← Complex.ofReal_mul, cast]; exact this)
    (fun i j => by
      have := (spin_entry_bounds hh i j).2
      have e : (if i = j then (1 : ℂ) else 0) - (h i : ℂ) * (h j : ℂ) =
          (((if i = j then (1 : ℝ) else 0) - h i * h j : ℝ) : ℂ) := by
        push_cast; split_ifs <;> simp
      rw [e, cast]; exact this) x y i j
  have h2 := kf0_sqrt_decay (d := d) (m := m) hg0 hgν hν1 x y
  linarith

end FullOp

end Balaban.Green
