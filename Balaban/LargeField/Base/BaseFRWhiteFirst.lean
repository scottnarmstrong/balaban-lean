/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseFRWhite
public import Balaban.LargeField.Base.BaseResolventRange

/-!
# The finite-range whitening of the first-step Hessian (route FR-1, row A3-1 (a)/(b))

`A_e = Q_e (H ⊗ I) Q_e + P_e` (`baseOp`) is `γ`-coercive with `γ = c/2`, `c = 1/(4L²)`, for complex
parameters within `η ≤ c/(8d)` of `[0,1]^𝓔` (`baseOp_isCoercive_of_close`), and its block row and
column sums are at most `J = ν + 12d + 4` with blocks vanishing beyond `R_A = dL + 1`
(`baseOp_rowSum_range`). Hence `‖A_e‖ ≤ J` (`sqNorm_mulVec_le_of_block_sums`, Schur test with block
operator norms), and for the scaling `c_W = J²/γ` the matrix `K_e = 1 - A_e/c_W` is a contraction:
`‖K_e‖ ≤ q = (1 - (γ/J)²)^{1/2} < 1` (`opNorm_one_sub_le`, valid for non-Hermitian `A_e`, i.e. for
complex data), of range `R_A`. The whitening is `W = c_W^{-1/2} S_R(K_e)` (`baseWhiteW`), and
`W A_e W = 1 + D_R` with the finite-range defect `D_R = S_R(K_e)² (1 - K_e) - 1`
(`baseWhite_identity`); `D_R` has range `(2R + 1) R_A` and norm at most
`4 (1 - q)^{-1/2} q^{R+1}/(1 - q)` (the results of `BaseFRWhite.lean`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

open Matrix Balaban.Green Balaban.LargeField.Base Balaban.Multiscale
open scoped Matrix.Norms.L2Operator

namespace Balaban.LargeField.FRWhite

section Abstract

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}


theorem sqNorm_sub_smul (v w : ι → ℂ) (t : ℝ) :
    sqNorm (v - (t : ℂ) • w) =
      sqNorm v - 2 * t * (∑ i, star (v i) * w i).re + t ^ 2 * sqNorm w := by
  unfold sqNorm
  rw [Complex.re_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Complex.sq_norm, Complex.normSq_apply,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

/-- **A coercive matrix of bounded norm is a contraction after the scaling `γ/B²`**:
`‖1 - (γ/B²) A‖ ≤ √(1 - γ²/B²)`. -/
theorem opNorm_one_sub_le {A : Matrix ι ι ℂ} {γ B : ℝ} (hγ : 0 < γ) (hB : 0 < B)
    (hcoer : IsCoercive A γ) (hn : ‖A‖ ≤ B) (hγB : γ ≤ B) :
    ‖(1 : Matrix ι ι ℂ) - ((γ / B ^ 2 : ℝ) : ℂ) • A‖ ≤ Real.sqrt (1 - (γ / B) ^ 2) := by
  have h0 : 0 ≤ 1 - (γ / B) ^ 2 := by
    have : γ / B ≤ 1 := (div_le_one hB).2 hγB
    have h1 : 0 ≤ γ / B := by positivity
    nlinarith
  refine Balaban.LargeField.Base.l2_opNorm_le_of_sqNorm _ (Real.sqrt_nonneg _) fun v => ?_
  rw [Real.sq_sqrt h0]
  set t : ℝ := γ / B ^ 2 with ht
  have e : ((1 : Matrix ι ι ℂ) - ((t : ℝ) : ℂ) • A) *ᵥ v = v - (t : ℂ) • (A *ᵥ v) := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]
  rw [e, sqNorm_sub_smul]
  have h1 := hcoer v
  have h2 := Balaban.LargeField.Base.sqNorm_mulVec_le_opNorm A v
  have h3 : ‖A‖ ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hn 2
  have hq : (∑ i, star (v i) * (A *ᵥ v) i).re = reQuad A v := rfl
  rw [hq]
  have htp : 0 ≤ t := by positivity
  have hsv : 0 ≤ sqNorm v := sqNorm_nonneg v
  have h4 : t ^ 2 * sqNorm (A *ᵥ v) ≤ t ^ 2 * (B ^ 2 * sqNorm v) :=
    mul_le_mul_of_nonneg_left (h2.trans (mul_le_mul_of_nonneg_right h3 hsv)) (sq_nonneg t)
  have e2 : t ^ 2 * (B ^ 2 * sqNorm v) = γ ^ 2 / B ^ 2 * sqNorm v := by
    rw [ht]; field_simp
  have e3 : 2 * t * (γ * sqNorm v) = 2 * γ ^ 2 / B ^ 2 * sqNorm v := by
    rw [ht]; field_simp
  have h5 : 2 * t * (γ * sqNorm v) ≤ 2 * t * reQuad A v :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  have e4 : (1 - (γ / B) ^ 2) * sqNorm v = sqNorm v - γ ^ 2 / B ^ 2 * sqNorm v := by
    rw [div_pow]; ring
  rw [e4]
  have h6 : t ^ 2 * sqNorm (A *ᵥ v) ≤ γ ^ 2 / B ^ 2 * sqNorm v := h4.trans e2.le
  have h7 : 2 * t * reQuad A v ≥ 2 * γ ^ 2 / B ^ 2 * sqNorm v := by rw [← e3]; exact h5
  have h8 : 2 * γ ^ 2 / B ^ 2 * sqNorm v = 2 * (γ ^ 2 / B ^ 2 * sqNorm v) := by ring
  linarith




theorem norm_toLp_eq_sqrt_sqNorm {n : Type*} [Fintype n] (u : n → ℂ) :
    ‖(WithLp.toLp 2 u : EuclideanSpace ℂ n)‖ = Real.sqrt (sqNorm u) := by
  rw [EuclideanSpace.norm_eq]; simp [sqNorm]

/-- **Schur test for the `ℓ²` norm with block operator norms**: if the block row and column sums of
`B` are at most `J` then `‖B v‖² ≤ J² ‖v‖²`. -/
theorem sqNorm_mulVec_le_of_block_sums (B : Matrix (ι × Fin N) (ι × Fin N) ℂ) {J : ℝ} (hJ0 : 0 ≤ J)
    (hrow : ∀ z, ∑ y, ‖blockOf B z y‖ ≤ J) (hcol : ∀ y, ∑ z, ‖blockOf B z y‖ ≤ J)
    (v : ι × Fin N → ℂ) : sqNorm (B *ᵥ v) ≤ J ^ 2 * sqNorm v := by
  set a : ι → ℝ := fun y => Real.sqrt (sqNorm (slice v y)) with ha
  set b : ι → ι → ℝ := fun z y => ‖blockOf B z y‖ with hb
  have hb0 : ∀ z y, 0 ≤ b z y := fun z y => norm_nonneg _
  have ha0 : ∀ y, 0 ≤ a y := fun y => Real.sqrt_nonneg _
  have ha2 : ∀ y, a y ^ 2 = sqNorm (slice v y) := fun y => Real.sq_sqrt (sqNorm_nonneg _)
  -- the slice of `B v`
  have hsl : ∀ z, slice (B *ᵥ v) z = ∑ y, blockOf B z y *ᵥ slice v y := by
    intro z
    funext i
    simp only [slice, Matrix.mulVec, dotProduct, blockOf, Matrix.of_apply, Finset.sum_apply,
      Fintype.sum_prod_type]
  have h1 : ∀ z, Real.sqrt (sqNorm (slice (B *ᵥ v) z)) ≤ ∑ y, b z y * a y := by
    intro z
    rw [← norm_toLp_eq_sqrt_sqNorm, hsl z]
    have : (WithLp.toLp 2 (∑ y, blockOf B z y *ᵥ slice v y) : EuclideanSpace ℂ (Fin N)) =
        ∑ y, (WithLp.toLp 2 (blockOf B z y *ᵥ slice v y) : EuclideanSpace ℂ (Fin N)) := by
      simp
    rw [this]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun y _ => ?_)
    rw [norm_toLp_eq_sqrt_sqNorm]
    have h2 := sqNorm_mulVec_le_opNorm (blockOf B z y) (slice v y)
    calc Real.sqrt (sqNorm (blockOf B z y *ᵥ slice v y))
        ≤ Real.sqrt (‖blockOf B z y‖ ^ 2 * sqNorm (slice v y)) := Real.sqrt_le_sqrt h2
      _ = b z y * a y := by
          rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]
  have h3 : ∀ z, sqNorm (slice (B *ᵥ v) z) ≤ J * ∑ y, b z y * a y ^ 2 := by
    intro z
    have h4 : sqNorm (slice (B *ᵥ v) z) ≤ (∑ y, b z y * a y) ^ 2 := by
      calc sqNorm (slice (B *ᵥ v) z) = (Real.sqrt (sqNorm (slice (B *ᵥ v) z))) ^ 2 :=
            (Real.sq_sqrt (sqNorm_nonneg _)).symm
        _ ≤ _ := pow_le_pow_left₀ (Real.sqrt_nonneg _) (h1 z) 2
    have h5 : (∑ y, b z y * a y) ^ 2 ≤ (∑ y, b z y) * ∑ y, b z y * a y ^ 2 := by
      have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun y => Real.sqrt (b z y))
        (fun y => Real.sqrt (b z y) * a y)
      simp only [← mul_assoc, Real.mul_self_sqrt (hb0 z _), mul_pow, Real.sq_sqrt (hb0 z _)] at this
      convert this using 2
    calc _ ≤ (∑ y, b z y) * ∑ y, b z y * a y ^ 2 := h4.trans h5
      _ ≤ J * ∑ y, b z y * a y ^ 2 := mul_le_mul_of_nonneg_right (hrow z)
          (Finset.sum_nonneg fun y _ => mul_nonneg (hb0 z y) (sq_nonneg _))
  rw [sqNorm_eq_sum_slice]
  calc ∑ z, sqNorm (slice (B *ᵥ v) z) ≤ ∑ z, J * ∑ y, b z y * a y ^ 2 :=
        Finset.sum_le_sum fun z _ => h3 z
    _ = J * ∑ y, a y ^ 2 * ∑ z, b z y := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        congr 1
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun z _ => by ring
    _ ≤ J * ∑ y, a y ^ 2 * J := mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (hcol y) (sq_nonneg _)) hJ0
    _ = J ^ 2 * sqNorm v := by
        rw [← Finset.sum_mul, sqNorm_eq_sum_slice]
        have : ∑ y, a y ^ 2 = ∑ y, sqNorm (slice v y) := Finset.sum_congr rfl fun y _ => ha2 y
        rw [this]; ring

end Abstract

section Whitening

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The contraction `K = 1 - (γ/J²) A` attached to a matrix with coercivity `γ` and norm `≤ J`. -/
noncomputable def whiteK (γ J : ℝ) (A : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  1 - ((γ / J ^ 2 : ℝ) : ℂ) • A

/-- The finite-range whitening `W = c^{-1/2} S_R(K)`, `c = J²/γ`, `K = whiteK γ J A`. -/
noncomputable def whiteW (γ J : ℝ) (A : Matrix ι ι ℂ) (R : ℕ) : Matrix ι ι ℂ :=
  (((J ^ 2 / γ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) • sqrtTrunc (whiteK γ J A) R

theorem sqrtTrunc_commute (K : Matrix ι ι ℂ) (R : ℕ) : Commute (sqrtTrunc K R) K := by
  unfold sqrtTrunc
  refine Commute.sum_left _ _ _ fun n _ => ?_
  exact ((Commute.refl K).pow_left n).smul_left _

/-- **The whitening identity**: `W A W = 1 + D_R`, `D_R = S_R(K)² (1 - K) - 1`, since
`A = c (1 - K)` and `S_R(K)` commutes with `K`. -/
theorem whiteW_mul_mul_whiteW {γ J : ℝ} (hγ : 0 < γ) (hJ : 0 < J) (A : Matrix ι ι ℂ) (R : ℕ) :
    whiteW γ J A R * A * whiteW γ J A R = 1 + whiteDefect (whiteK γ J A) R := by
  set K := whiteK γ J A with hK
  set S := sqrtTrunc K R with hS
  set c : ℝ := J ^ 2 / γ with hc
  have hc0 : 0 < c := by positivity
  have hA : A = (c : ℂ) • (1 - K) := by
    rw [hK, whiteK, sub_sub_cancel, smul_smul]
    have : (c : ℂ) * ((γ / J ^ 2 : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, hc]
      have : J ^ 2 / γ * (γ / J ^ 2) = 1 := by field_simp
      rw [this]; simp
    rw [this, one_smul]
  have hcc : ((c ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * ((c ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * (c : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Real.rpow_add hc0]
    have h1 : c ^ (-(1 / 2 : ℝ) + -(1 / 2)) * c = 1 := by
      rw [show (-(1 / 2 : ℝ)) + -(1 / 2) = -1 by norm_num, Real.rpow_neg_one]
      field_simp
    rw [h1]; simp
  have hcomm : S * (1 - K) = (1 - K) * S :=
    ((Commute.one_left S).symm.sub_right (sqrtTrunc_commute K R)).eq
  have hSS : S * (1 - K) * S = S * S * (1 - K) := by
    calc S * (1 - K) * S = S * ((1 - K) * S) := mul_assoc _ _ _
      _ = S * (S * (1 - K)) := by rw [hcomm]
      _ = S * S * (1 - K) := (mul_assoc _ _ _).symm
  unfold whiteW whiteDefect
  rw [← hK, ← hS]
  set r : ℂ := ((c ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) with hr
  have e1 : (r • S) * A * (r • S) = (r * r * (c : ℂ)) • (S * (1 - K) * S) := by
    rw [hA]
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
    congr 1
    ring
  rw [e1, hcc, one_smul, hSS]
  abel

end Whitening

section First

variable {d L N₀ N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} (G : GeneratingSet d L N₀ 1 ϱ)

/-- The distance on the indices `(z, i)` of `A_e`: the site distance of the chart sites. -/
noncomputable def indexDist (p p' : G.Ω 1 × Fin N) : ℝ := siteDist G p.1 p'.1

theorem indexDist_self : DistSelf (indexDist (N := N) G) := fun p => siteDist_self G p.1

theorem indexDist_tri : DistTri (indexDist (N := N) G) := fun p q r => siteDist_triangle G p.1 q.1 r.1

variable {a : ℕ → ℝ} {ν : ℝ} {α : G.Ω 1 → ℂ} {η : ℝ} {s : FineBond d L N₀ → ℂ}
  (e : G.Ω 1 → Fin N → ℝ)

/-- **`‖A_e(s)‖ ≤ J = ν + 12 d + 4`** (`ℓ²` operator norm): the Schur test with the block row and
column sums of `baseOp_rowSum_range`. -/
theorem baseOp_opNorm_le (hν : 0 ≤ ν) (ha : IsAdmissibleWeights 1 a)
    (hα : ∀ z, ‖α z‖ ≤ 1 / (8 * (L : ℝ) ^ 2)) (hη : η ≤ baseCoercivity L / (8 * d))
    (hs : s ∈ baseParamNbhd G η) (he : ∀ z, ∑ i, e z i ^ 2 = 1) :
    ‖baseOp N (fun z i => (e z i : ℂ)) (baseHamiltonian G a ν α s)‖ ≤ baseJ d ν := by
  obtain ⟨-, hrow, hcol⟩ := baseOp_rowSum_range G hν ha hα hη hs e he
  exact l2_opNorm_le_of_sqNorm _ (baseJ_pos hν).le fun v =>
    sqNorm_mulVec_le_of_block_sums _ (baseJ_pos hν).le hrow hcol v

/-- The contraction `K_e = 1 - (γ/J²) A_e(s)`, `γ = c/2 = 1/(8L²)`, `J = ν + 12 d + 4`. -/
noncomputable def baseWhiteK (a : ℕ → ℝ) (ν : ℝ) (α : G.Ω 1 → ℂ) (s : FineBond d L N₀ → ℂ)
    (e : G.Ω 1 → Fin N → ℝ) : Matrix (G.Ω 1 × Fin N) (G.Ω 1 × Fin N) ℂ :=
  whiteK (baseCoercivity L / 2) (baseJ d ν) (baseOp N (fun z i => (e z i : ℂ))
    (baseHamiltonian G a ν α s))

/-- The finite-range whitening `W = c_W^{-1/2} S_R(K_e)`, `c_W = J²/γ`, of the first step. -/
noncomputable def baseWhiteW (a : ℕ → ℝ) (ν : ℝ) (α : G.Ω 1 → ℂ) (s : FineBond d L N₀ → ℂ)
    (e : G.Ω 1 → Fin N → ℝ) (R : ℕ) : Matrix (G.Ω 1 × Fin N) (G.Ω 1 × Fin N) ℂ :=
  whiteW (baseCoercivity L / 2) (baseJ d ν) (baseOp N (fun z i => (e z i : ℂ))
    (baseHamiltonian G a ν α s)) R

/-- **`K_e` is a contraction**: `‖K_e‖ ≤ q = (1 - (γ/J)²)^{1/2} < 1`, for complex parameters in the
coercive neighbourhood (`baseOp_isCoercive_of_close`). -/
theorem baseWhiteK_norm_le (hν : 0 ≤ ν) (ha : IsAdmissibleWeights 1 a)
    (hα : ∀ z, ‖α z‖ ≤ 1 / (8 * (L : ℝ) ^ 2)) (hη0 : 0 ≤ η)
    (hη : η ≤ baseCoercivity L / (8 * d)) (hs : s ∈ baseParamNbhd G η)
    (he : ∀ z, ∑ i, e z i ^ 2 = 1) :
    ‖baseWhiteK G a ν α s e‖ ≤ Real.sqrt (1 - ((baseCoercivity L / 2) / baseJ d ν) ^ 2) ∧
      Real.sqrt (1 - ((baseCoercivity L / 2) / baseJ d ν) ^ 2) < 1 := by
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hc0 := baseCoercivity_pos hL
  have hc1 := baseCoercivity_le_one hL
  have hJ := baseJ_pos (d := d) hν
  have hJ4 : 4 ≤ baseJ d ν := by
    unfold baseJ
    have : (0 : ℝ) ≤ d := by positivity
    linarith
  have hγ : 0 < baseCoercivity L / 2 := by positivity
  have hγJ : baseCoercivity L / 2 ≤ baseJ d ν := by linarith
  refine ⟨?_, ?_⟩
  · exact opNorm_one_sub_le hγ hJ (baseOp_isCoercive_of_close G hν ha hα hη0 hη hs e he)
      (baseOp_opNorm_le G e hν ha hα hη hs he) hγJ
  · rw [Real.sqrt_lt' one_pos]
    have : 0 < (baseCoercivity L / 2 / baseJ d ν) ^ 2 := by positivity
    linarith

/-- **`K_e` has finite range** `R_A = dL + 1`. -/
theorem baseWhiteK_hasRange (hν : 0 ≤ ν) (ha : IsAdmissibleWeights 1 a)
    (hα : ∀ z, ‖α z‖ ≤ 1 / (8 * (L : ℝ) ^ 2)) (hη : η ≤ baseCoercivity L / (8 * d))
    (hs : s ∈ baseParamNbhd G η) (he : ∀ z, ∑ i, e z i ^ 2 = 1) :
    HasRange (indexDist (N := N) G) (baseWhiteK G a ν α s e) (baseRange d L) := by
  obtain ⟨hr, -, -⟩ := baseOp_rowSum_range G hν ha hα hη hs e he
  have hA : HasRange (indexDist (N := N) G)
      (baseOp N (fun z i => (e z i : ℂ)) (baseHamiltonian G a ν α s)) (baseRange d L) := by
    intro p q hpq
    by_contra hne
    exact absurd (hr p.1 q.1 (fun h0 => hne (by
      show blockOf (baseOp N (fun z i => (e z i : ℂ)) (baseHamiltonian G a ν α s)) p.1 q.1 p.2 q.2 = 0
      rw [h0]; rfl))) (not_le.2 hpq)
  have h1 : HasRange (indexDist (N := N) G) (1 : Matrix (G.Ω 1 × Fin N) (G.Ω 1 × Fin N) ℂ)
      (baseRange d L) := (HasRange.one (indexDist_self G)).mono (baseRange_pos (d := d) (L := L)).le
  exact h1.sub (hA.smul _)

/-- **The finite-range whitening of the first-step Hessian** (route FR-1): for complex parameters in
the coercive neighbourhood, with `K = baseWhiteK`, `q = (1 - (γ/J)²)^{1/2} < 1` and
`D_R = S_R(K)² (1 - K) - 1`,
* `W A_e W = 1 + D_R` (`W = baseWhiteW`, `A_e = baseOp`), i.e. the Gaussian
  `exp(-(β/2)⟨u, A_e u⟩)` in `u = β^{-1/2} W ψ'` is `exp(-½|ψ'|² - ½⟨ψ', D_R ψ'⟩)`;
* `W` has range `R (dL + 1)` and `D_R` has range `(2R + 1)(dL + 1)`;
* `‖D_R‖ ≤ 4 (1 - q)^{-1/2} q^{R+1}/(1 - q)`. -/
theorem baseWhite [Nonempty (G.Ω 1)] [NeZero N] (hν : 0 ≤ ν) (ha : IsAdmissibleWeights 1 a)
    (hα : ∀ z, ‖α z‖ ≤ 1 / (8 * (L : ℝ) ^ 2)) (hη0 : 0 ≤ η)
    (hη : η ≤ baseCoercivity L / (8 * d)) (hs : s ∈ baseParamNbhd G η)
    (he : ∀ z, ∑ i, e z i ^ 2 = 1) (R : ℕ) :
    baseWhiteW G a ν α s e R * baseOp N (fun z i => (e z i : ℂ)) (baseHamiltonian G a ν α s) *
        baseWhiteW G a ν α s e R = 1 + whiteDefect (baseWhiteK G a ν α s e) R ∧
      HasRange (indexDist (N := N) G) (baseWhiteW G a ν α s e R) (R * baseRange d L) ∧
      HasRange (indexDist (N := N) G) (whiteDefect (baseWhiteK G a ν α s e) R)
        ((2 * R + 1) * baseRange d L) ∧
      ‖whiteDefect (baseWhiteK G a ν α s e) R‖ ≤
        4 * Real.sqrt (1 - Real.sqrt (1 - ((baseCoercivity L / 2) / baseJ d ν) ^ 2))⁻¹ *
          (Real.sqrt (1 - ((baseCoercivity L / 2) / baseJ d ν) ^ 2) ^ (R + 1) /
            (1 - Real.sqrt (1 - ((baseCoercivity L / 2) / baseJ d ν) ^ 2))) := by
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hJ := baseJ_pos (d := d) hν
  have hγ : 0 < baseCoercivity L / 2 := half_pos (baseCoercivity_pos hL)
  obtain ⟨hK, hq⟩ := baseWhiteK_norm_le G e hν ha hα hη0 hη hs he
  have hRg := baseWhiteK_hasRange G e hν ha hα hη hs he
  have hr0 := (baseRange_pos (d := d) (L := L)).le
  refine ⟨whiteW_mul_mul_whiteW hγ hJ _ R, ?_, ?_, ?_⟩
  · exact (sqrtTrunc_hasRange (indexDist_self G) (indexDist_tri G) hr0 hRg R).smul _
  · exact whiteDefect_hasRange (indexDist_self G) (indexDist_tri G) hr0 hRg R
  · exact norm_whiteDefect_le hK (Real.sqrt_nonneg _) hq R

end First

end Balaban.LargeField.FRWhite
