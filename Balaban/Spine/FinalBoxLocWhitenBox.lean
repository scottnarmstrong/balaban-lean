/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.FinalBoxLocChi
public import Balaban.Spine.LastIntegral
public import Balaban.Green.FinalBoxLocWhiten
public import Balaban.Spine.InheritedBound

/-!
# The whitening of the box integral and `χ_k = 1` on the box (A6-3, Amendment B-1′, item (b))

The box integral changes variables by `ψ_k = h + A w`, `w` the standard Gaussian variable of the box
`|w_p| ≤ p₁` (`gaussBox`), with the whitening `A = β_k^{-1/2} L` (`sfWhiten`), `L` the localized
square root of the final Hessian of the class (`finalWhitenR` at the background mass
`μ_k L^{2k}` and the weight `a_k` of `sfFinalK`, macro side `M_c`, localization radius `D`), read on
the `k`-blocks.

* `abs_matAct_le_of_row_bound`, `norm_sub_le_sqrt_mul`: `|(A w)_p| ≤ B p₁` for row sums of `A` at
  most `B`, and `‖ψ_k(y) - h‖ ≤ √N B p₁`;
* `chiY_eq_one_of_row_bound` (core): `χ_k(Y) = 1` at `ψ_k = h + A w` on the box, for every `Y`,
  when `√N B p₁ ≤ m` with the constraints of `chiY_eq_one_of_near`;
* `sfWhiten_row_bound`: the row sums of `sfWhiten` are at most `β_k^{-1/2} boxCutConst`;
  `chiY_sfWhiten_eq_one`: `χ_k(Y) = 1` on the box at the whitening `sfWhiten`;
* `sfWhiten_det_ne_zero_of_lt_one`: `det A ≠ 0` when the mismatch bound is below `1`.
-/

@[expose] public section

namespace Balaban.RootFSpine

open Balaban Balaban.Multiscale Balaban.Background Balaban.LargeField Balaban.LargeField.Def7
  Balaban.Green

section Near

variable {ι : Type*} [Fintype ι] {N : ℕ}

omit [Fintype ι] in
theorem spinField_symm_add_apply (ψ0 : ι → EuclideanSpace ℝ (Fin N)) (u : ι × Fin N → ℝ)
    (y : ι) (i : Fin N) :
    (spinField ι N).symm (spinField ι N ψ0 + u) y i = ψ0 y i + u (y, i) := by
  have h := spinField_apply ι N ((spinField ι N).symm (spinField ι N ψ0 + u)) (y, i)
  rw [MeasurableEquiv.apply_symm_apply, Pi.add_apply, spinField_apply] at h
  exact h.symm

/-- `‖v - w‖ ≤ √N c` when every component of `v - w` is at most `c`. -/
theorem norm_sub_le_sqrt_mul {v w : EuclideanSpace ℝ (Fin N)} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ i, |v i - w i| ≤ c) : ‖v - w‖ ≤ Real.sqrt N * c := by
  rw [EuclideanSpace.norm_eq]
  have hs : ∑ i, ‖(v - w) i‖ ^ 2 ≤ (N : ℝ) * c ^ 2 := by
    calc ∑ i, ‖(v - w) i‖ ^ 2 ≤ ∑ _i : Fin N, c ^ 2 := Finset.sum_le_sum fun i _ => by
          rw [PiLp.sub_apply, Real.norm_eq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (h i) 2
      _ = (N : ℝ) * c ^ 2 := by simp
  calc Real.sqrt (∑ i, ‖(v - w) i‖ ^ 2) ≤ Real.sqrt ((N : ℝ) * c ^ 2) := Real.sqrt_le_sqrt hs
    _ = Real.sqrt N * c := by rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq hc]

/-- `|(A w)_p| ≤ B p₁` for row sums of `|A|` at most `B` and `|w| ≤ p₁`. -/
theorem abs_matAct_le_of_row_bound {A : Matrix ι ι ℝ} {B p1 : ℝ} (hB : ∀ p, ∑ q, |A p q| ≤ B)
    (hp1 : 0 ≤ p1) {w : ι → ℝ} (hw : ∀ q, |w q| ≤ p1) (p : ι) : |matAct A w p| ≤ B * p1 := by
  unfold matAct
  calc |∑ q, A p q • w q| ≤ ∑ q, |A p q| * p1 := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun q _ => ?_)
        rw [smul_eq_mul, abs_mul]
        exact mul_le_mul_of_nonneg_left (hw q) (abs_nonneg _)
    _ = (∑ q, |A p q|) * p1 := by rw [Finset.sum_mul]
    _ ≤ B * p1 := mul_le_mul_of_nonneg_right (hB p) hp1

end Near

section Box

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N k m₁ : ℕ} {ϱ : ℝ}

/-- **`χ_k = 1` on the box at a whitening with bounded rows** (core): for `ψ_k = h + A w` with
`|w| ≤ p₁` and row sums of `|A|` at most `B`, `χ_k(Y) = 1` for every `Y` when `√N B p₁ ≤ m`,
`m ≤ 1/2`, `3 m < δ' ≤ c₁` and `K₁ δ' + m < δ_k`, under the cube `BgHyp` at the cutoff mass. -/
theorem chiY_eq_one_of_row_bound (C : SFCtx S n R M K N k m₁ ϱ) (Y : Set (Torus S.d (n k)))
    (hv : EuclideanSpace ℝ (Fin N)) (hsum : ∑ i, hv i ^ 2 = 1)
    (H : BgHyp S.d S.L k (minSep S.L C.geo.M1) C.weights (C.cs.mu k)) (hk : 1 ≤ k)
    {A : Matrix (BlockAt S n M K k × Fin N) (BlockAt S n M K k × Fin N) ℝ} {B p1 : ℝ}
    (hB : ∀ p, ∑ q, |A p q| ≤ B) (hp1 : 0 ≤ p1)
    {w : BlockAt S n M K k × Fin N → ℝ} (hw : w ∈ gaussBox (BlockAt S n M K k × Fin N) p1)
    {m δ' : ℝ} (hm0 : 0 ≤ m) (hm : Real.sqrt N * (B * p1) ≤ m) (hm1 : m ≤ 1 / 2)
    (hmδ : 3 * m < δ') (hδ'1 : δ' ≤ bgC1 S.d S.L N)
    (hK : bgK1 S.d S.L N * δ' + m < C.cs.delta k) :
    C.chiY Y ((spinField (BlockAt S n M K k) N).symm
      (spinField (BlockAt S n M K k) N (fun _ => hv) + matAct A w)) hv = 1 := by
  refine chiY_eq_one_of_near C Y _ hv hsum H hk hm0 hm1 hmδ hδ'1 hK fun y => ?_
  by_cases hN : N = 0
  · subst hN
    rw [Subsingleton.elim (_ - hv) 0, norm_zero]
    exact hm0
  have hBp : 0 ≤ B * p1 := (abs_nonneg _).trans
    (abs_matAct_le_of_row_bound hB hp1 hw (y, ⟨0, Nat.pos_of_ne_zero hN⟩))
  refine (norm_sub_le_sqrt_mul hBp fun i => ?_).trans hm
  rw [spinField_symm_add_apply, add_sub_cancel_left]
  exact abs_matAct_le_of_row_bound hB hp1 hw (y, i)

/-- **The whitening of the box integral** (Amendment B-1′): `A = β_k^{-1/2} L`, `L` the localized
square root of the final Hessian of `sfFinalK` (background mass `μ_k L^{2k}`, weight `a_k`), with
macro cells of side `M_c` and localization radius `D`, read on the `k`-blocks. -/
noncomputable def sfWhiten (C : SFCtx S n R M K N k m₁ ϱ) (hv : EuclideanSpace ℝ (Fin N))
    (Mc D : ℕ) : Matrix (BlockAt S n M K k × Fin N) (BlockAt S n M K k × Fin N) ℝ :=
  Real.sqrt (C.sf.β k)⁻¹ • finalWhitenR S.d S.L (M * n K * S.L ^ (K - k)) k Mc
    (C.cs.muBg k * ((S.L : ℝ) ^ k) ^ 2) (C.weights k) (fun i => ((hv i : ℝ) : ℂ)) D

/-- **Row sums of the whitening**: at most `β_k^{-1/2} boxCutConst`. -/
theorem sfWhiten_row_bound (C : SFCtx S n R M K N k m₁ ϱ) (hv : EuclideanSpace ℝ (Fin N))
    (hunit : ‖hv‖ = 1) {Mc : ℕ} {κ α : ℝ}
    (hBC : BoxCutConsts S.d S.L k Mc (C.cs.muBg k * ((S.L : ℝ) ^ k) ^ 2) (C.weights k) κ α)
    (D : ℕ) (p : BlockAt S n M K k × Fin N) :
    ∑ q, |sfWhiten C hv Mc D p q| ≤
      Real.sqrt (C.sf.β k)⁻¹ * boxCutConst S.d S.L N (C.weights k) κ 1 := by
  have hκ0 : 0 ≤ κ := by linarith [hBC.ties.1]
  have hrow := finalWhiten_row_bound (N₀ := M * n K * S.L ^ (K - k)) (k := k) (M := Mc)
    hBC.hd hBC.hk hBC.hv0 hBC.hv1 hBC.ha1 hBC.ha2 hBC.hmass hBC.hM hκ0 hBC.ties.2.1
    hBC.ties.2.2.1 (h := fun i => ((hv i : ℝ) : ℂ)) (p := 1)
    (norm_spinProj_ofReal_le_one (sum_sq_eq_one_of_norm_eq_one hv hunit)) D p
  have e : ∀ q, |sfWhiten C hv Mc D p q| = Real.sqrt (C.sf.β k)⁻¹ *
      |(finalWhiten S.d S.L (M * n K * S.L ^ (K - k)) k Mc (C.cs.muBg k * ((S.L : ℝ) ^ k) ^ 2)
        (C.weights k) (fun i => ((hv i : ℝ) : ℂ)) D p q).re| := fun q => by
    show |Real.sqrt (C.sf.β k)⁻¹ * _| = _
    rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    rfl
  rw [Finset.sum_congr rfl fun q _ => e q, ← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left
    ((Finset.sum_le_sum fun q _ => Complex.abs_re_le_norm _).trans hrow) (Real.sqrt_nonneg _)

/-- **`χ_k = 1` on the box at the whitening `sfWhiten`**: for `w` in the box `|w| ≤ p₁`, every `Y`
and `√N β_k^{-1/2} boxCutConst p₁ ≤ m` with the constraints of `chiY_eq_one_of_near`. -/
theorem chiY_sfWhiten_eq_one (C : SFCtx S n R M K N k m₁ ϱ) (Y : Set (Torus S.d (n k)))
    (hv : EuclideanSpace ℝ (Fin N)) (hunit : ‖hv‖ = 1)
    (H : BgHyp S.d S.L k (minSep S.L C.geo.M1) C.weights (C.cs.mu k)) {Mc : ℕ} {κ α : ℝ}
    (hBC : BoxCutConsts S.d S.L k Mc (C.cs.muBg k * ((S.L : ℝ) ^ k) ^ 2) (C.weights k) κ α)
    (D : ℕ) {p1 : ℝ} (hp1 : 0 ≤ p1)
    {w : BlockAt S n M K k × Fin N → ℝ} (hw : w ∈ gaussBox (BlockAt S n M K k × Fin N) p1)
    {m δ' : ℝ} (hm0 : 0 ≤ m)
    (hm : Real.sqrt N * (Real.sqrt (C.sf.β k)⁻¹ * boxCutConst S.d S.L N (C.weights k) κ 1 * p1) ≤ m)
    (hm1 : m ≤ 1 / 2) (hmδ : 3 * m < δ') (hδ'1 : δ' ≤ bgC1 S.d S.L N)
    (hK : bgK1 S.d S.L N * δ' + m < C.cs.delta k) :
    C.chiY Y ((spinField (BlockAt S n M K k) N).symm
      (spinField (BlockAt S n M K k) N (fun _ => hv) + matAct (sfWhiten C hv Mc D) w)) hv = 1 :=
  chiY_eq_one_of_row_bound C Y hv (sum_sq_eq_one_of_norm_eq_one hv hunit) H hBC.hk
    (sfWhiten_row_bound C hv hunit hBC D) hp1 hw hm0 hm hm1 hmδ hδ'1 hK

/-- **The whitening is invertible** when the mismatch bound is below `1` (at some
`0 ≤ r' < r ≤ ε/8`; `exists_whitenRadius` gives such radii `D`). -/
theorem sfWhiten_det_ne_zero_of_lt_one (C : SFCtx S n R M K N k m₁ ϱ)
    (hv : EuclideanSpace ℝ (Fin N)) (hunit : ‖hv‖ = 1) (hβ : 0 < C.sf.β k) {Mc : ℕ} {κ α : ℝ}
    (hBC : BoxCutConsts S.d S.L k Mc (C.cs.muBg k * ((S.L : ℝ) ^ k) ^ 2) (C.weights k) κ α)
    (hv0 : 0 < C.cs.muBg k * ((S.L : ℝ) ^ k) ^ 2) [NeZero N] {r r' : ℝ} (hr'0 : 0 ≤ r')
    (hr' : r' < r) (hr : r ≤ pdEps S.d S.L / 8) (D : ℕ)
    (hsmall : whitenMismatchBound S.d S.L N (C.weights k) κ 1 r r' D < 1) :
    (sfWhiten C hv Mc D).det ≠ 0 := by
  have hh := sum_sq_eq_one_of_norm_eq_one hv hunit
  have hu := isUnit_finalWhiten_of_lt_one (N₀ := M * n K * S.L ^ (K - k)) hBC hv0 hh
    (norm_spinProj_ofReal_le_one hh) hr'0 hr' hr D hsmall
  have hdetC := (Matrix.isUnit_iff_isUnit_det _).1 hu
  rw [← finalWhitenR_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at hdetC
  have hR : (finalWhitenR S.d S.L (M * n K * S.L ^ (K - k)) k Mc
      (C.cs.muBg k * ((S.L : ℝ) ^ k) ^ 2) (C.weights k) (fun i => ((hv i : ℝ) : ℂ)) D).det ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hdetC
    exact not_isUnit_zero hdetC
  have key : (Real.sqrt (C.sf.β k)⁻¹ • finalWhitenR S.d S.L (M * n K * S.L ^ (K - k)) k Mc
      (C.cs.muBg k * ((S.L : ℝ) ^ k) ^ 2) (C.weights k) (fun i => ((hv i : ℝ) : ℂ)) D).det ≠ 0 := by
    rw [Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ (Real.sqrt_pos.2 (inv_pos.2 hβ)).ne') hR
  exact key

end Box

end Balaban.RootFSpine
