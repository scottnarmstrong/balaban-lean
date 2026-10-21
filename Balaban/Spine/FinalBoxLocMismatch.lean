/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.FinalBoxLocWhitenBox
public import Balaban.Green.FinalBoxLocPair

/-!
# The mismatch of the whitening of the box and its pair terms (A6-3, Amendment B-1′, part (U))

With the whitening `A = β_k^{-1/2} L` (`sfWhiten`) and the form `K = β_k D` of the last integral
(`sfFinalK`), the mismatch `Aᵀ K A - 1` is the mismatch `Lᵀ D L - 1` of the localized square root
(`finalWhitenMismatch`), real and small; its quadratic form `-½⟨w, (Aᵀ K A - 1) w⟩` is the undilated
even part of the box integrand, put in polymer form by the pair terms on the paths of the macro
cover (`pairLocal`).

* `finalHessian_submatrix_torusCast`, `sfFinalK_eq`: `sfFinalK` is `β_k` times the final Hessian on
  the torus of the `k`-blocks (`histScale_eq`);
* `sfWhitenMismatch_map`: `(Aᵀ K A - 1)` complexifies to `finalWhitenMismatch`;
* `abs_sfWhitenMismatch_le`: `|(Aᵀ K A - 1)(p, q)| ≤ whitenMismatchBound e^{-r' |p - q|}`;
* `sfMismatchLocal`: the pair terms `U_Y(w)` of `-½⟨w, (Aᵀ K A - 1) w⟩`, with
  `sum_sfMismatchLocal`, locality, support, evenness, continuity and the summed bound
  `sfMismatchLocal_bound` (cell units).
-/

@[expose] public section

namespace Balaban.RootFSpine

open Balaban Balaban.Multiscale Balaban.Background Balaban.LargeField Balaban.LargeField.Def7
  Balaban.Green Matrix

section Transport

/-- **The final Hessian along a cast of the torus size.** -/
theorem finalHessian_submatrix_torusCast {d ℓ ℓ' Nb m m' N : ℕ} [NeZero ℓ] [NeZero ℓ']
    [NeZero m] [NeZero m'] (hℓ : ℓ = ℓ') (hm : m = m') (ν a : ℝ) (h : Fin N → ℝ) :
    (finalHessian d ℓ' Nb m' ν a h).submatrix (fun p : Torus d m × Fin N => (torusCast hm p.1, p.2))
      (fun p : Torus d m × Fin N => (torusCast hm p.1, p.2)) = finalHessian d ℓ Nb m ν a h := by
  subst hℓ
  subst hm
  rfl

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N k m₁ : ℕ} {ϱ : ℝ}

/-- **The form of the last integral on the `k`-blocks**: `sfFinalK = β_k D`, `D` the final Hessian
on the torus of the `k`-blocks (side `M n_K L^{K-k}`). -/
theorem sfFinalK_eq (C : SFCtx S n R M K N k m₁ ϱ) (hv : EuclideanSpace ℝ (Fin N)) :
    sfFinalK C hv = C.sf.β k • finalHessian S.d (M * n K * S.L ^ (K - k) * S.L ^ k) (S.L ^ k)
      (M * n K * S.L ^ (K - k)) (C.cs.muBg k * ((S.L : ℝ) ^ k) ^ 2) (C.weights k)
      (fun i => hv i) := by
  have hm := histScale_eq C.geo.hM C.hnn (le_refl k) C.hkK
  have hℓ : M * n K * S.L ^ (K - k) * S.L ^ k = C.geo.M1 * (C.geo.c * n k) * S.L ^ k := by
    rw [← hm, Nat.sub_self, pow_zero, mul_one]
  unfold sfFinalK sfBlockSite
  rw [← finalHessian_submatrix_torusCast hℓ hm.symm]
  rfl

end Transport

section Mismatch

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N k m₁ : ℕ} {ϱ : ℝ}

theorem smul_transpose_mul_smul_mul_smul {ι : Type*} [Fintype ι] (c b : ℝ) (A B : Matrix ι ι ℝ) :
    (c • A)ᵀ * (b • B) * (c • A) = (c * b * c) • (Aᵀ * B * A) := by
  simp only [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  congr 1
  ring

/-- **The mismatch of the whitening is the mismatch of the localized square root**: for `β_k > 0`,
a unit `h`, `0 ≤ ν` and `a > 0`, `(Aᵀ K A - 1)` complexifies to `finalWhitenMismatch`. -/
theorem sfWhitenMismatch_map (C : SFCtx S n R M K N k m₁ ϱ) (hv : EuclideanSpace ℝ (Fin N))
    (hunit : ‖hv‖ = 1) (hβ : 0 < C.sf.β k) (hd : 0 < S.d)
    (hν : 0 ≤ C.cs.muBg k * ((S.L : ℝ) ^ k) ^ 2) (ha : 0 < C.weights k) (Mc D : ℕ) :
    ((sfWhiten C hv Mc D)ᵀ * sfFinalK C hv * sfWhiten C hv Mc D - 1).map (algebraMap ℝ ℂ) =
      finalWhitenMismatch S.d S.L (M * n K * S.L ^ (K - k)) k Mc
        (C.cs.muBg k * ((S.L : ℝ) ^ k) ^ 2) (C.weights k) (fun i => ((hv i : ℝ) : ℂ)) D := by
  have hh := sum_sq_eq_one_of_norm_eq_one hv hunit
  have hc : Real.sqrt (C.sf.β k)⁻¹ * C.sf.β k * Real.sqrt (C.sf.β k)⁻¹ = 1 := by
    rw [mul_comm, ← mul_assoc, Real.mul_self_sqrt (inv_nonneg.2 hβ.le), inv_mul_cancel₀ hβ.ne']
  set Lr : Matrix (BlockAt S n M K k × Fin N) (BlockAt S n M K k × Fin N) ℝ :=
    finalWhitenR S.d S.L (M * n K * S.L ^ (K - k)) k Mc (C.cs.muBg k * ((S.L : ℝ) ^ k) ^ 2)
      (C.weights k) (fun i => ((hv i : ℝ) : ℂ)) D with hLr
  set Dr := finalHessian S.d (M * n K * S.L ^ (K - k) * S.L ^ k) (S.L ^ k)
    (M * n K * S.L ^ (K - k)) (C.cs.muBg k * ((S.L : ℝ) ^ k) ^ 2) (C.weights k)
    (fun i => hv i) with hDr
  have hLmap : Lr.map (algebraMap ℝ ℂ) = finalWhiten S.d S.L (M * n K * S.L ^ (K - k)) k Mc
      (C.cs.muBg k * ((S.L : ℝ) ^ k) ^ 2) (C.weights k) (fun i => ((hv i : ℝ) : ℂ)) D :=
    finalWhitenR_map (fun i => hv i) D
  have hDmap : Dr.map (algebraMap ℝ ℂ) = finalHessianC S.d S.L (M * n K * S.L ^ (K - k)) k
      (C.cs.muBg k * ((S.L : ℝ) ^ k) ^ 2) (C.weights k) (fun i => ((hv i : ℝ) : ℂ)) :=
    (finalHessianC_ofReal hd hν ha hh).symm
  have key : ((Real.sqrt (C.sf.β k)⁻¹ • Lr)ᵀ * (C.sf.β k • Dr) * (Real.sqrt (C.sf.β k)⁻¹ • Lr) -
      1).map (algebraMap ℝ ℂ) = finalWhitenMismatch S.d S.L (M * n K * S.L ^ (K - k)) k Mc
        (C.cs.muBg k * ((S.L : ℝ) ^ k) ^ 2) (C.weights k) (fun i => ((hv i : ℝ) : ℂ)) D := by
    rw [smul_transpose_mul_smul_mul_smul, hc, one_smul,
      Matrix.map_sub _ (fun a b => map_sub (algebraMap ℝ ℂ) a b), Matrix.map_one _
      (map_zero _) (map_one _), Matrix.map_mul, Matrix.map_mul]
    simp only [Matrix.transpose_map, hLmap, hDmap]
    rfl
  rw [sfFinalK_eq]
  exact key

/-- The weighted row sums of the mismatch bound its entries:
`|(Aᵀ K A - 1)(p, q)| ≤ whitenMismatchBound e^{-r' |p - q|}` (`sum_finalWhitenMismatch_le`). -/
theorem abs_sfWhitenMismatch_le (C : SFCtx S n R M K N k m₁ ϱ) (hv : EuclideanSpace ℝ (Fin N))
    (hunit : ‖hv‖ = 1) (hβ : 0 < C.sf.β k) {Mc : ℕ} {κ α : ℝ}
    (hBC : BoxCutConsts S.d S.L k Mc (C.cs.muBg k * ((S.L : ℝ) ^ k) ^ 2) (C.weights k) κ α)
    (hv0 : 0 < C.cs.muBg k * ((S.L : ℝ) ^ k) ^ 2) [NeZero N] {r r' : ℝ} (hr'0 : 0 ≤ r')
    (hr' : r' < r) (hr : r ≤ pdEps S.d S.L / 8) (D : ℕ) (p q : BlockAt S n M K k × Fin N) :
    |((sfWhiten C hv Mc D)ᵀ * sfFinalK C hv * sfWhiten C hv Mc D - 1) p q| ≤
      whitenMismatchBound S.d S.L N (C.weights k) κ 1 r r' D *
        Real.exp (-r' * bdist p.1 q.1) := by
  have hh := sum_sq_eq_one_of_norm_eq_one hv hunit
  have ha : 0 < C.weights k := by linarith [hBC.ha1]
  have hmap := sfWhitenMismatch_map C hv hunit hβ hBC.hd hv0.le ha Mc D
  have hrow := sum_finalWhitenMismatch_le (N₀ := M * n K * S.L ^ (K - k)) hBC hv0 hh
    (norm_spinProj_ofReal_le_one hh) hr'0 hr' hr D p
  have hentry : |((sfWhiten C hv Mc D)ᵀ * sfFinalK C hv * sfWhiten C hv Mc D - 1) p q| =
      ‖finalWhitenMismatch S.d S.L (M * n K * S.L ^ (K - k)) k Mc
        (C.cs.muBg k * ((S.L : ℝ) ^ k) ^ 2) (C.weights k) (fun i => ((hv i : ℝ) : ℂ)) D p q‖ := by
    rw [← hmap, Matrix.map_apply, Complex.coe_algebraMap, Complex.norm_real, Real.norm_eq_abs]
  rw [hentry]
  have h1 : Real.exp (r' * bdist p.1 q.1) *
      ‖finalWhitenMismatch S.d S.L (M * n K * S.L ^ (K - k)) k Mc
        (C.cs.muBg k * ((S.L : ℝ) ^ k) ^ 2) (C.weights k) (fun i => ((hv i : ℝ) : ℂ)) D p q‖ ≤
      whitenMismatchBound S.d S.L N (C.weights k) κ 1 r r' D :=
    le_trans (Finset.single_le_sum (f := fun q' => Real.exp (r' * bdist p.1 q'.1) *
      ‖finalWhitenMismatch S.d S.L (M * n K * S.L ^ (K - k)) k Mc
        (C.cs.muBg k * ((S.L : ℝ) ^ k) ^ 2) (C.weights k) (fun i => ((hv i : ℝ) : ℂ)) D p q'‖)
      (fun _ _ => mul_nonneg (Real.exp_pos _).le (norm_nonneg _)) (Finset.mem_univ q)) hrow
  have he : Real.exp (-r' * bdist p.1 q.1) * Real.exp (r' * bdist p.1 q.1) = 1 := by
    rw [← Real.exp_add]; simp
  calc ‖finalWhitenMismatch S.d S.L (M * n K * S.L ^ (K - k)) k Mc
        (C.cs.muBg k * ((S.L : ℝ) ^ k) ^ 2) (C.weights k) (fun i => ((hv i : ℝ) : ℂ)) D p q‖
      = Real.exp (-r' * bdist p.1 q.1) * (Real.exp (r' * bdist p.1 q.1) *
          ‖finalWhitenMismatch S.d S.L (M * n K * S.L ^ (K - k)) k Mc
            (C.cs.muBg k * ((S.L : ℝ) ^ k) ^ 2) (C.weights k) (fun i => ((hv i : ℝ) : ℂ)) D
              p q‖) := by rw [← mul_assoc, he, one_mul]
    _ ≤ Real.exp (-r' * bdist p.1 q.1) * whitenMismatchBound S.d S.L N (C.weights k) κ 1 r r' D :=
        mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
    _ = _ := mul_comm _ _

/-- **The pair terms of the mismatch**: `U_Y(w)`, the pair terms of `-½⟨w, (Aᵀ K A - 1) w⟩` on the
paths of the macro cover (`pairLocal`), at the whitening `A = sfWhiten`. -/
noncomputable def sfMismatchLocal (C : SFCtx S n R M K N k m₁ ϱ) (hv : EuclideanSpace ℝ (Fin N))
    (Mc D : ℕ) (Y : Finset (BlockAt S n M K k)) (w : BlockAt S n M K k × Fin N → ℝ) : ℂ :=
  ((pairLocal (fun p q => ((sfWhiten C hv Mc D)ᵀ * sfFinalK C hv * sfWhiten C hv Mc D - 1) p q)
    Y w : ℝ) : ℂ)

/-- **The pair terms sum to the quadratic form of the mismatch.** -/
theorem sum_sfMismatchLocal (C : SFCtx S n R M K N k m₁ ϱ) (hv : EuclideanSpace ℝ (Fin N))
    (Mc D : ℕ) (w : BlockAt S n M K k × Fin N → ℝ) :
    ∑ Y, sfMismatchLocal C hv Mc D Y w = ((-(1 / 2) * ∑ p, ∑ q,
      ((sfWhiten C hv Mc D)ᵀ * sfFinalK C hv * sfWhiten C hv Mc D - 1) p q * w p * w q : ℝ) : ℂ) := by
  unfold sfMismatchLocal
  rw [← Complex.ofReal_sum, sum_pairLocal]

theorem sfMismatchLocal_congr (C : SFCtx S n R M K N k m₁ ϱ) (hv : EuclideanSpace ℝ (Fin N))
    (hd : 0 < S.d) (Mc D : ℕ) (Y : Finset (BlockAt S n M K k))
    {w w' : BlockAt S n M K k × Fin N → ℝ} (hww : ∀ x ∈ Y, ∀ i, w (x, i) = w' (x, i)) :
    sfMismatchLocal C hv Mc D Y w = sfMismatchLocal C hv Mc D Y w' := by
  unfold sfMismatchLocal
  rw [pairLocal_congr hd _ Y hww]

theorem sfMismatchLocal_eq_zero_of_not_isAnimal (C : SFCtx S n R M K N k m₁ ϱ)
    (hv : EuclideanSpace ℝ (Fin N)) (hd : 0 < S.d) (Mc D : ℕ) {Y : Finset (BlockAt S n M K k)}
    (hY : ¬ Polymer.IsAnimal (Polymer.blockGraph S.d (M * n K * S.L ^ (K - k))) Y)
    (w : BlockAt S n M K k × Fin N → ℝ) : sfMismatchLocal C hv Mc D Y w = 0 := by
  unfold sfMismatchLocal
  rw [pairLocal_eq_zero_of_not_isAnimal hd _ hY w, Complex.ofReal_zero]

theorem sfMismatchLocal_neg (C : SFCtx S n R M K N k m₁ ϱ) (hv : EuclideanSpace ℝ (Fin N))
    (Mc D : ℕ) (Y : Finset (BlockAt S n M K k)) (w : BlockAt S n M K k × Fin N → ℝ) :
    sfMismatchLocal C hv Mc D Y (-w) = sfMismatchLocal C hv Mc D Y w := by
  unfold sfMismatchLocal
  rw [pairLocal_neg]

theorem continuous_sfMismatchLocal (C : SFCtx S n R M K N k m₁ ϱ)
    (hv : EuclideanSpace ℝ (Fin N)) (Mc D : ℕ) (Y : Finset (BlockAt S n M K k)) :
    Continuous (sfMismatchLocal C hv Mc D Y) :=
  Complex.continuous_ofReal.comp (continuous_pairLocal _ Y)

/-- **The summed bound of the pair terms of the mismatch** (cell units, macro side `M_c`): for `w`
in the box `|w| ≤ p₁`, the cell rate `α ≥ 0` and `ρ = r' - α 7^d / M_c > 0`,
`∑_{Y ∋ x} ‖U_Y(w)‖ e^{α #cells(Y)} ≤ ½ whitenMismatchBound p₁² e^{α(16^d + 9 d 7^d)}
(N ballConst(ρ))²`; `whitenMismatchBound ≤ whitenQConst 2^{-D}` (`whitenMismatchBound_le_of_ties`). -/
theorem sfMismatchLocal_bound (C : SFCtx S n R M K N k m₁ ϱ) (hv : EuclideanSpace ℝ (Fin N))
    (hunit : ‖hv‖ = 1) (hβ : 0 < C.sf.β k) {Mc : ℕ} {κ α' : ℝ}
    (hBC : BoxCutConsts S.d S.L k Mc (C.cs.muBg k * ((S.L : ℝ) ^ k) ^ 2) (C.weights k) κ α')
    (hv0 : 0 < C.cs.muBg k * ((S.L : ℝ) ^ k) ^ 2) [NeZero N] {r r' : ℝ} (hr'0 : 0 ≤ r')
    (hr' : r' < r) (hr : r ≤ pdEps S.d S.L / 8) (D : ℕ) {α p1 : ℝ} (hα : 0 ≤ α)
    (hρ : 0 < r' - α * 7 ^ S.d / Mc) (hp1 : 0 ≤ p1) {w : BlockAt S n M K k × Fin N → ℝ}
    (hw : w ∈ gaussBox (BlockAt S n M K k × Fin N) p1) (x : BlockAt S n M K k) :
    ∑ Y ∈ Finset.univ.filter (fun Y : Finset (BlockAt S n M K k) => x ∈ Y),
        ‖sfMismatchLocal C hv Mc D Y w‖ *
          Real.exp (α * (macCellCount S.d (M * n K * S.L ^ (K - k)) Mc Y : ℝ)) ≤
      1 / 2 * whitenMismatchBound S.d S.L N (C.weights k) κ 1 r r' D * p1 ^ 2 *
        Real.exp (α * (16 ^ S.d + 9 * S.d * 7 ^ S.d)) *
        (N * ballConst S.d (r' - α * 7 ^ S.d / Mc)) ^ 2 := by
  have hεQ : 0 ≤ whitenMismatchBound S.d S.L N (C.weights k) κ 1 r r' D :=
    (abs_nonneg _).trans ((abs_sfWhitenMismatch_le C hv hunit hβ hBC hv0 hr'0 hr' hr D
      (x, 0) (x, 0)).trans (by
        rw [show bdist x x = 0 from dist_self (α := L1Torus S.d (M * n K * S.L ^ (K - k))) x]
        simp))
  have := pairLocal_bound (d := S.d) (m := M * n K * S.L ^ (K - k)) (N := N) hBC.hM
    (Q := fun p q => ((sfWhiten C hv Mc D)ᵀ * sfFinalK C hv * sfWhiten C hv Mc D - 1) p q) hεQ
    (abs_sfWhitenMismatch_le C hv hunit hβ hBC hv0 hr'0 hr' hr D) hα hρ hp1 hw x
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun Y _ => ?_)) this
  unfold sfMismatchLocal
  rw [Complex.norm_real, Real.norm_eq_abs]

end Mismatch

end Balaban.RootFSpine
