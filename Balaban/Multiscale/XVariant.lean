/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Multiscale.AgmonCore
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

/-!
# The x-variant operator `G_{k,x}(α₀)` and its coercivity, G-1(a′) (GREEN.md §1.3 (1.7), §4.1)

On the fine torus `Torus d (N₀ * L ^ (k + 1))` (unit fine spacing, so `ℓ_j = L ^ j`) let
`G : GeneratingSet d L N₀ (k + 1) ϱ`.  Its layers `1, …, k` are those of the generating set
`𝔹_k`; its top region `Ω_{k+1}` (the `(k+1)`-st layer) carries the bracket of (1.7)
`Q_k* S_x Q_k = s₁ P_k + (s₂ - s₁) P_{k+1}` (`P_j = Q_j* Q_j` the block projection), in fine units
multiplied by `L ^ (-2k)`:

* `Balaban.Multiscale.xS1 ak x = ak x/(ak + x)`, `xS2 ak b x = ak (x + b)/(ak + x + b)`, `b = a L⁻²`;
* `Balaban.Multiscale.xAvgMatrix`: `∑_{j ≤ k} a_j L⁻²ʲ 1_{layer j} P_j 1_{layer j}
  + L⁻²ᵏ 1_{Ω_{k+1}} (s₁ P_k + (s₂ - s₁) P_{k+1}) 1_{Ω_{k+1}}`;
* `Balaban.Multiscale.xDirichletOperator`: `H_{k,x}(α₀)` of (1.7) on `Ω₁`.

Main results (uniform in `x ≥ 0`; `ν ≥ 0`; `a_j ∈ [1/2, 2]` for `j ≤ k`; `a ∈ [1/2, 2]`; `L ≥ 3`):

* `Balaban.Multiscale.top_ineq` : the blockwise inequality of G-1(a′), `E_B ≥ c L⁻²⁽ᵏ⁺¹⁾ ‖ψ‖²`
  (the case split `x ≤ a_k/8`, `x > a_k/8` of §4.1);
* `Balaban.Multiscale.xCore_real` : `½ ‖∂φ‖² + c_x ‖ℓ⁻¹ φ‖² ≤ φᵀ (-Δ + ν + Q* a Q|_x) φ`;
* `Balaban.Multiscale.x_multiscale_coercive`, `xDirichletOperator_isCoercive`,
  `xDirichletOperator_isUnit`: G-1(a′) for complex `α₀` with `|α₀| ≤ c_x ℓ⁻² / 4`.

The constants differ from GREEN.md because the landed block Poincaré inequality has the constant
`d/2` (instead of the sharp `1/8` per direction): `c_x = min (1/d) (1/4)`, and the admitted potential
range is `|α₀(y)| ≤ (c_x/4) ℓ(y)⁻²`, i.e. `|α₀| ≤ (c_x/4) L⁻²` in unit-lattice units on `Ω_{k+1}`,
which is smaller than the range `|α₀| ≤ a_{k+1} L⁻²/12 ≤ L⁻²/8` of N-1.  (The N-1 margin needs the
sharp, `d`-free Poincaré constant of GREEN.md Lemma 4.1.)
-/

@[expose] public section

namespace Balaban.Multiscale

open Finset Matrix Balaban

/-! ### The symbols `s₁`, `s₂` -/

/-- `s₁ = a_k x/(a_k + x)`. -/
noncomputable def xS1 (ak x : ℝ) : ℝ := ak * x / (ak + x)

/-- `s₂ = a_k (x + b)/(a_k + x + b)`, `b = a L⁻²`. -/
noncomputable def xS2 (ak b x : ℝ) : ℝ := ak * (x + b) / (ak + x + b)

theorem xS1_nonneg {ak x : ℝ} (hak : 0 < ak) (hx : 0 ≤ x) : 0 ≤ xS1 ak x := by
  unfold xS1; positivity

theorem xS12_sub {ak b x : ℝ} (hak : 0 < ak) (hb : 0 ≤ b) (hx : 0 ≤ x) :
    xS2 ak b x - xS1 ak x = ak ^ 2 * b / ((ak + x) * (ak + x + b)) := by
  unfold xS1 xS2
  have h1 : 0 < ak + x := by linarith
  have h2 : 0 < ak + x + b := by linarith
  field_simp
  ring

theorem xS12_sub_nonneg {ak b x : ℝ} (hak : 0 < ak) (hb : 0 ≤ b) (hx : 0 ≤ x) :
    0 ≤ xS2 ak b x - xS1 ak x := by
  rw [xS12_sub hak hb hx]; positivity

/-- Case `x ≤ a_k/8` of G-1(a′): `s₂ - s₁ ≥ b/2`. -/
theorem xS12_sub_ge {ak b x : ℝ} (hak1 : 1 / 2 ≤ ak) (hb0 : 0 ≤ b)
    (hb1 : b ≤ 2 / 9) (hx0 : 0 ≤ x) (hx : x ≤ ak / 8) : b / 2 ≤ xS2 ak b x - xS1 ak x := by
  have hak : 0 < ak := by linarith
  rw [xS12_sub hak hb0 hx0, le_div_iff₀ (by positivity)]
  have key : (ak + x) * (ak + x + b) ≤ 2 * ak ^ 2 := by
    nlinarith [mul_nonneg hx0 hb0, mul_nonneg (sub_nonneg.2 hx) hb0, mul_nonneg hx0 hx0,
      mul_nonneg (sub_nonneg.2 hx) hx0]
  nlinarith [mul_le_mul_of_nonneg_left key hb0]

/-- Case `x > a_k/8` of G-1(a′): `s₁ ≥ a_k/9`. -/
theorem xS1_ge {ak x : ℝ} (hak : 0 < ak) (hx : ak / 8 < x) : ak / 9 ≤ xS1 ak x := by
  unfold xS1
  rw [le_div_iff₀ (by linarith)]
  nlinarith

/-! ### The matrices -/

section Matrices

variable {d L N₀ K : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- `1_{layer j} P 1_{layer j}` with `P` the projection onto the constants of the blocks of side
`L ^ m` (`m ≤ j` makes this a coarse-grained average inside the layer). -/
noncomputable def layerBlockMatrix (G : GeneratingSet d L N₀ K ϱ) (j m : ℕ) :
    Matrix (Torus d (N₀ * L ^ K)) (Torus d (N₀ * L ^ K)) ℝ :=
  fun x x' => if x ∈ G.layer j ∧ x' ∈ G.layer j then
    blockProjMatrix d (N₀ * L ^ K) (L ^ m) (N₀ * L ^ (K - m)) x x' else 0

theorem layerBlockMatrix_bilinear (G : GeneratingSet d L N₀ K ϱ) (j m : ℕ)
    (g φ : Torus d (N₀ * L ^ K) → ℝ) :
    g ⬝ᵥ layerBlockMatrix G j m *ᵥ φ =
      layerPart G j g ⬝ᵥ blockProjMatrix d (N₀ * L ^ K) (L ^ m) (N₀ * L ^ (K - m)) *ᵥ
        layerPart G j φ := by
  simp only [dotProduct, Matrix.mulVec, layerBlockMatrix, layerPart]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : x ∈ G.layer j
  · simp only [hx, true_and, ite_true]
    congr 1
    refine Finset.sum_congr rfl fun x' _ => ?_
    by_cases hx' : x' ∈ G.layer j <;> simp [hx']
  · simp [hx]

theorem layerBlockMatrix_quadratic (G : GeneratingSet d L N₀ K ϱ) {j m : ℕ} (hmK : m ≤ K)
    (φ : Torus d (N₀ * L ^ K) → ℝ) :
    φ ⬝ᵥ layerBlockMatrix G j m *ᵥ φ =
      ∑ x, (blockProjection (L ^ m) (N₀ * L ^ (K - m)) (layerPart G j φ) x) ^ 2 := by
  have hℓ := side_eq (N₀ := N₀) (L := L) hmK
  have hN : 0 < L ^ m := Nat.pos_of_ne_zero (pow_ne_zero _ (NeZero.ne L))
  rw [layerBlockMatrix_bilinear]
  simp only [dotProduct, blockProjMatrix_mulVec]
  exact sum_mul_blockProjection hℓ hN _

end Matrices

section XOperator

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}
variable (G : GeneratingSet d L N₀ (k + 1) ϱ)

/-- The averaging form of the x-variant (1.7) in fine units:
`∑_{j ≤ k} a_j L⁻²ʲ 1_{layer j} P_j 1_{layer j}
  + L⁻²ᵏ 1_{Ω_{k+1}} (s₁ P_k + (s₂ - s₁) P_{k+1}) 1_{Ω_{k+1}}`. -/
noncomputable def xAvgMatrix (a : ℕ → ℝ) (s₁ s₂ : ℝ) :
    Matrix (Torus d (N₀ * L ^ (k + 1))) (Torus d (N₀ * L ^ (k + 1))) ℝ :=
  ∑ j ∈ Icc 1 k, (a j / ((L : ℝ) ^ j) ^ 2) • layerBlockMatrix G j j +
    (s₁ / ((L : ℝ) ^ k) ^ 2) • layerBlockMatrix G (k + 1) k +
    ((s₂ - s₁) / ((L : ℝ) ^ k) ^ 2) • layerBlockMatrix G (k + 1) (k + 1)

/-- `-Δ + ν + (x-variant averaging form)` on the whole fine torus. -/
noncomputable def xFullMatrix (a : ℕ → ℝ) (s₁ s₂ ν : ℝ) :
    Matrix (Torus d (N₀ * L ^ (k + 1))) (Torus d (N₀ * L ^ (k + 1))) ℝ :=
  latticeLaplacian d (N₀ * L ^ (k + 1)) ν + xAvgMatrix G a s₁ s₂

/-- **The x-variant operator `H_{k,x}(α₀)`** of (1.7) as a complex matrix on `Ω₁`, with
`s₁ = xS1 (a k) x`, `s₂ = xS2 (a k) (aT L⁻²) x`; `aT` is the constant `a` in `a L⁻² Q* Q`. -/
noncomputable def xDirichletOperator (a : ℕ → ℝ) (aT x ν : ℝ) (α : G.Ω 1 → ℂ) :
    Matrix (G.Ω 1) (G.Ω 1) ℂ :=
  Green.restrictOp ((xFullMatrix G a (xS1 (a k) x) (xS2 (a k) (aT / (L : ℝ) ^ 2) x) ν).map
    (algebraMap ℝ ℂ)) (G.Ω 1) + Matrix.diagonal α

theorem xAvgMatrix_quadratic (a : ℕ → ℝ) (s₁ s₂ : ℝ) (φ : Torus d (N₀ * L ^ (k + 1)) → ℝ) :
    φ ⬝ᵥ xAvgMatrix G a s₁ s₂ *ᵥ φ =
      ∑ j ∈ Icc 1 k, (a j / ((L : ℝ) ^ j) ^ 2) *
        ∑ x, (blockProjection (L ^ j) (N₀ * L ^ (k + 1 - j)) (layerPart G j φ) x) ^ 2 +
      (s₁ / ((L : ℝ) ^ k) ^ 2) *
        ∑ x, (blockProjection (L ^ k) (N₀ * L ^ (k + 1 - k)) (layerPart G (k + 1) φ) x) ^ 2 +
      ((s₂ - s₁) / ((L : ℝ) ^ k) ^ 2) *
        ∑ x, (blockProjection (L ^ (k + 1)) (N₀ * L ^ (k + 1 - (k + 1)))
          (layerPart G (k + 1) φ) x) ^ 2 := by
  unfold xAvgMatrix
  rw [Matrix.add_mulVec, Matrix.add_mulVec, dotProduct_add, dotProduct_add, Matrix.sum_mulVec,
    dotProduct_sum]
  congr 1
  · congr 1
    · refine Finset.sum_congr rfl fun j hj => ?_
      rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
        layerBlockMatrix_quadratic G (by have := (Finset.mem_Icc.1 hj).2; omega)]
    · rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
        layerBlockMatrix_quadratic G (by omega)]
  · rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, layerBlockMatrix_quadratic G le_rfl]

end XOperator

/-! ### The blockwise inequality of G-1(a′) -/

/-- The Poincaré constant of the x-variant, `min (1/d) (1/4)`. -/
noncomputable def xPoincareConst (d : ℕ) : ℝ := min (1 / (d : ℝ)) (1 / 4)

theorem xPoincareConst_pos {d : ℕ} (hd : 0 < d) : 0 < xPoincareConst d := by
  have : (0 : ℝ) < d := by exact_mod_cast hd
  unfold xPoincareConst
  exact lt_min (by positivity) (by norm_num)

theorem xPoincareConst_le_quarter (d : ℕ) : xPoincareConst d ≤ 1 / 4 := min_le_right _ _

theorem xPoincareConst_le_inv (d : ℕ) : xPoincareConst d ≤ 1 / (d : ℝ) := min_le_left _ _

theorem xPoincareConst_le_poincareConst (d : ℕ) : xPoincareConst d ≤ poincareConst d :=
  min_le_min le_rfl (by norm_num)

/-- A bond inside an `L ^ k`-block lies inside an `L ^ (k+1)`-block. -/
theorem mod_succ_lt_mul {v N M : ℕ} (hM : 0 < M) (h : v % N + 1 < N) :
    v % (N * M) + 1 < N * M := by
  have hN : 0 < N := by omega
  rw [Nat.mod_mul]
  have h1 : v / N % M < M := Nat.mod_lt _ hM
  have h2 : N * (v / N % M) ≤ N * (M - 1) := Nat.mul_le_mul_left _ (by omega)
  have h3 : N * (M - 1) + N = N * M := by
    obtain ⟨M', rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
    simp [Nat.mul_add]
  omega

section Energy

variable {d ℓ : ℕ} [NeZero ℓ]

theorem innerEnergy_mono_pow {L k : ℕ} [NeZero L] (f : Torus d ℓ → ℝ) :
    innerEnergy (L ^ k) f ≤ innerEnergy (L ^ (k + 1)) f := by
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  unfold innerEnergy
  refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun μ _ => ?_
  by_cases h : (x μ).val % L ^ k + 1 < L ^ k
  · have h' : (x μ).val % L ^ (k + 1) + 1 < L ^ (k + 1) := by
      rw [pow_succ]; exact mod_succ_lt_mul hL h
    simp [h, h']
  · simp only [h, ite_false]
    split_ifs <;> positivity

end Energy

section TopIneq

/-- Scalar form of the case `x ≤ a_k/8` of G-1(a′). -/
theorem top_real_one {c d ℓ0 q V S E t : ℝ} (hc0 : 0 < c) (hcd : c * d ≤ 1) (hc4 : c ≤ 1 / 4)
    (hℓ : 0 < ℓ0) (hq : 0 < q) (hV : V ≤ d / 2 * (ℓ0 * q) * E) (hE : 0 ≤ E) (hS : 0 ≤ S)
    (ht : 1 / (4 * q) ≤ t) :
    c / (ℓ0 * q) * (V + S) ≤ 1 / 2 * E + t / ℓ0 * S := by
  have hℓq : 0 < ℓ0 * q := by positivity
  have hA : c / (ℓ0 * q) * V ≤ 1 / 2 * E := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hℓq]
    have h1 : c * V ≤ c * (d / 2 * (ℓ0 * q) * E) := mul_le_mul_of_nonneg_left hV hc0.le
    have h2 : c * (d / 2 * (ℓ0 * q) * E) = (c * d) / 2 * ((ℓ0 * q) * E) := by ring
    have h3 : (c * d) / 2 * ((ℓ0 * q) * E) ≤ 1 / 2 * ((ℓ0 * q) * E) := by
      gcongr
    nlinarith
  have hB : c / (ℓ0 * q) * S ≤ t / ℓ0 * S := by
    refine mul_le_mul_of_nonneg_right ?_ hS
    rw [div_le_div_iff₀ hℓq hℓ]
    have h2 : 1 / (4 * q) * (ℓ0 * q) ≤ t * (ℓ0 * q) := by gcongr
    have h3 : 1 / (4 * q) * (ℓ0 * q) = 1 / 4 * ℓ0 := by field_simp
    nlinarith
  rw [mul_add]
  linarith

/-- Scalar form of the case `x > a_k/8` of G-1(a′). -/
theorem top_real_two {c d ℓ0 q V S E0 E1 s : ℝ} (hc0 : 0 < c) (hcd : c * d ≤ 1) (hc4 : c ≤ 1 / 4)
    (hℓ : 0 < ℓ0) (hq : 9 ≤ q) (hV0 : 0 ≤ V) (hV : V ≤ d / 2 * ℓ0 * E0) (hE0 : 0 ≤ E0)
    (hE : E0 ≤ E1) (hS : 0 ≤ S) (hs : 1 / 18 ≤ s) :
    c / (ℓ0 * q) * (V + S) ≤ 1 / 2 * E1 + s / ℓ0 * S := by
  have hq0 : 0 < q := by linarith
  have hℓq : 0 < ℓ0 * q := by positivity
  have hA : c / (ℓ0 * q) * V ≤ 1 / 2 * E1 := by
    have h1 : c / (ℓ0 * q) * V ≤ c / ℓ0 * V := by
      refine mul_le_mul_of_nonneg_right ?_ hV0
      exact div_le_div_of_nonneg_left hc0.le hℓ (by nlinarith)
    have h2 : c / ℓ0 * V ≤ 1 / 2 * E0 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hℓ]
      have h1 : c * V ≤ c * (d / 2 * ℓ0 * E0) := mul_le_mul_of_nonneg_left hV hc0.le
      have h2 : c * (d / 2 * ℓ0 * E0) = (c * d) / 2 * (ℓ0 * E0) := by ring
      have h3 : (c * d) / 2 * (ℓ0 * E0) ≤ 1 / 2 * (ℓ0 * E0) := by gcongr
      nlinarith
    linarith
  have hB : c / (ℓ0 * q) * S ≤ s / ℓ0 * S := by
    refine mul_le_mul_of_nonneg_right ?_ hS
    rw [div_le_div_iff₀ hℓq hℓ]
    nlinarith [mul_nonneg hℓ.le (sub_nonneg.2 hs), mul_nonneg hℓ.le (sub_nonneg.2 hq)]
  rw [mul_add]
  linarith

/-- **The blockwise inequality of G-1(a′).**  For `ψ` on the fine torus, with `ℓ₁ = L ^ (k+1)`,
`s₁ ≥ 0`, `s₂ - s₁ ≥ 0` and either `s₂ - s₁ ≥ 1/(4 L²)` (the case `x ≤ a_k/8`) or `s₁ ≥ 1/18` (the
case `x > a_k/8`) (`L ≥ 3`):
`c ℓ₁⁻² ‖ψ‖² ≤ ½ E_{ℓ₁}(ψ) + L⁻²ᵏ (s₁ ‖P_k ψ‖² + (s₂ - s₁) ‖P_{k+1} ψ‖²)`. -/
theorem top_ineq {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] (hd : 0 < d) (hL : 3 ≤ L) {s₁ s₂ : ℝ}
    (hs₁ : 0 ≤ s₁) (hs : 0 ≤ s₂ - s₁)
    (hcase : 1 / (4 * (L : ℝ) ^ 2) ≤ s₂ - s₁ ∨ 1 / 18 ≤ s₁)
    (ψ : Torus d (N₀ * L ^ (k + 1)) → ℝ) :
    xPoincareConst d / ((L : ℝ) ^ (k + 1)) ^ 2 * ∑ x, ψ x ^ 2 ≤
      (1 / 2) * innerEnergy (L ^ (k + 1)) ψ +
        (s₁ / ((L : ℝ) ^ k) ^ 2) *
          ∑ x, (blockProjection (L ^ k) (N₀ * L ^ (k + 1 - k)) ψ x) ^ 2 +
        ((s₂ - s₁) / ((L : ℝ) ^ k) ^ 2) *
          ∑ x, (blockProjection (L ^ (k + 1)) (N₀ * L ^ (k + 1 - (k + 1))) ψ x) ^ 2 := by
  have hdd : (0 : ℝ) < d := by exact_mod_cast hd
  have hLr : (3 : ℝ) ≤ L := by exact_mod_cast hL
  have hc0 := xPoincareConst_pos hd
  have hc4 := xPoincareConst_le_quarter d
  have hcd : xPoincareConst d * d ≤ 1 := by
    have := xPoincareConst_le_inv d
    calc xPoincareConst d * d ≤ 1 / (d : ℝ) * d := by gcongr
      _ = 1 := by field_simp
  have hl0 : (0 : ℝ) < ((L : ℝ) ^ k) ^ 2 := by positivity
  have hl1 : ((L : ℝ) ^ (k + 1)) ^ 2 = ((L : ℝ) ^ k) ^ 2 * (L : ℝ) ^ 2 := by ring
  have hE1 := innerEnergy_nonneg (N := L ^ (k + 1)) ψ
  have hE0n := innerEnergy_nonneg (N := L ^ k) ψ
  have hE0 := innerEnergy_mono_pow (L := L) (k := k) ψ
  have hNk : 0 < L ^ k := Nat.pos_of_ne_zero (pow_ne_zero _ (NeZero.ne L))
  have hNk1 : 0 < L ^ (k + 1) := Nat.pos_of_ne_zero (pow_ne_zero _ (NeZero.ne L))
  have hℓk := side_eq (N₀ := N₀) (L := L) (k := k + 1) (j := k) (by omega)
  have hℓk1 := side_eq (N₀ := N₀) (L := L) (k := k + 1) (j := k + 1) le_rfl
  have hP0 := blockPoincare hℓk hNk ψ
  have hP1 := blockPoincare hℓk1 hNk1 ψ
  have hpy0 := sum_sq_eq_sum_sq_sub_add hℓk hNk ψ
  have hpy1 := sum_sq_eq_sum_sq_sub_add hℓk1 hNk1 ψ
  simp only [Nat.cast_pow] at hP0 hP1
  rw [hl1]
  rcases hcase with hcase | hcase
  · rw [hpy1]
    have hq : (0 : ℝ) < (L : ℝ) ^ 2 := by positivity
    have hP1' : ∑ x, (ψ x - blockProjection (L ^ (k + 1)) (N₀ * L ^ (k + 1 - (k + 1))) ψ x) ^ 2 ≤
        (d : ℝ) / 2 * (((L : ℝ) ^ k) ^ 2 * (L : ℝ) ^ 2) * innerEnergy (L ^ (k + 1)) ψ := by
      rw [← hl1]; exact hP1
    have hS1 : 0 ≤ ∑ x, (blockProjection (L ^ (k + 1)) (N₀ * L ^ (k + 1 - (k + 1))) ψ x) ^ 2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    have := top_real_one hc0 hcd hc4 hl0 hq hP1' hE1 hS1 hcase
    have h0 : 0 ≤ s₁ / ((L : ℝ) ^ k) ^ 2 *
        ∑ x, (blockProjection (L ^ k) (N₀ * L ^ (k + 1 - k)) ψ x) ^ 2 :=
      mul_nonneg (div_nonneg hs₁ hl0.le) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    linarith
  · rw [hpy0]
    have hL2 : (9 : ℝ) ≤ (L : ℝ) ^ 2 := by nlinarith
    have hS0 : 0 ≤ ∑ x, (blockProjection (L ^ k) (N₀ * L ^ (k + 1 - k)) ψ x) ^ 2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    have := top_real_two hc0 hcd hc4 hl0 hL2 (Finset.sum_nonneg fun _ _ => sq_nonneg _) hP0 hE0n
      hE0 hS0 hcase
    have h0 : 0 ≤ (s₂ - s₁) / ((L : ℝ) ^ k) ^ 2 *
        ∑ x, (blockProjection (L ^ (k + 1)) (N₀ * L ^ (k + 1 - (k + 1))) ψ x) ^ 2 :=
      mul_nonneg (div_nonneg hs hl0.le) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    linarith

end TopIneq

/-! ### Real core and coercivity -/

section Core

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}
variable (G : GeneratingSet d L N₀ (k + 1) ϱ)

omit [NeZero L] in
/-- The two cases of G-1(a′) for the symbols: `s₁, s₂ - s₁ ≥ 0` and either `s₂ - s₁ ≥ 1/(4 L²)`
(`x ≤ a_k/8`) or `s₁ ≥ 1/18` (`x > a_k/8`). -/
theorem xSymbols_cases (hL : 3 ≤ L) {ak aT x : ℝ} (hak : 1 / 2 ≤ ak) (haT1 : 1 / 2 ≤ aT)
    (haT2 : aT ≤ 2) (hx : 0 ≤ x) :
    0 ≤ xS1 ak x ∧ 0 ≤ xS2 ak (aT / (L : ℝ) ^ 2) x - xS1 ak x ∧
      (1 / (4 * (L : ℝ) ^ 2) ≤ xS2 ak (aT / (L : ℝ) ^ 2) x - xS1 ak x ∨ 1 / 18 ≤ xS1 ak x) := by
  have hLr : (3 : ℝ) ≤ L := by exact_mod_cast hL
  have hL2 : (9 : ℝ) ≤ (L : ℝ) ^ 2 := by nlinarith
  have hq : (0 : ℝ) < (L : ℝ) ^ 2 := by positivity
  have hak0 : 0 < ak := by linarith
  have hb0 : 0 ≤ aT / (L : ℝ) ^ 2 := by positivity
  refine ⟨xS1_nonneg hak0 hx, xS12_sub_nonneg hak0 hb0 hx, ?_⟩
  by_cases hxa : x ≤ ak / 8
  · left
    have hb1 : aT / (L : ℝ) ^ 2 ≤ 2 / 9 := by
      rw [div_le_iff₀ hq]; nlinarith
    have := xS12_sub_ge hak (by exact hb0) hb1 hx hxa
    have h2 : 1 / (4 * (L : ℝ) ^ 2) ≤ aT / (L : ℝ) ^ 2 / 2 := by
      rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith
  · right
    push Not at hxa
    have := xS1_ge hak0 hxa
    linarith

/-- Core of `xCore_real` with `1 ≤ k` replaced by the lower bound `1/2 ≤ a_k` (the only use of `k ≥ 1`); the weights `a_j`, `1 ≤ j ≤ k`, stay in `[1/2, 2]`. -/
theorem xCore_real_of_ak (hd : 0 < d) (hL : 3 ≤ L) {a : ℕ → ℝ} {ν : ℝ} (hν : 0 ≤ ν)
    (ha : IsAdmissibleWeights k a)
    (hak : 1 / 2 ≤ a k ∧ a k ≤ 2) {aT x : ℝ} (haT1 : 1 / 2 ≤ aT) (haT2 : aT ≤ 2) (hx : 0 ≤ x)
    (φ : Torus d (N₀ * L ^ (k + 1)) → ℝ) :
    (1 / 2) * latticeEnergy φ + xPoincareConst d * ∑ y, invSqSpacing G y * φ y ^ 2 ≤
      φ ⬝ᵥ xFullMatrix G a (xS1 (a k) x) (xS2 (a k) (aT / (L : ℝ) ^ 2) x) ν *ᵥ φ := by
  obtain ⟨hs₁, hs, hcase⟩ := xSymbols_cases (L := L) hL hak.1 haT1 haT2 hx
  have hc0 := xPoincareConst_pos hd
  unfold xFullMatrix
  rw [Matrix.add_mulVec, dotProduct_add, latticeLaplacian_quadratic, xAvgMatrix_quadratic]
  have hE := sum_innerEnergy_le G φ
  rw [Finset.sum_Icc_succ_top (by omega)] at hE
  have hlay : ∑ y, invSqSpacing G y * φ y ^ 2 =
      ∑ j ∈ Icc 1 (k + 1), (((L : ℝ) ^ j) ^ 2)⁻¹ * ∑ y, (layerPart G j φ y) ^ 2 :=
    wsq_eq_sum_layers G φ
  rw [Finset.sum_Icc_succ_top (by omega)] at hlay
  have hper : ∑ j ∈ Icc 1 k, xPoincareConst d / ((L : ℝ) ^ j) ^ 2 * ∑ y, (layerPart G j φ y) ^ 2 ≤
      ∑ j ∈ Icc 1 k, ((1 / 2) * innerEnergy (L ^ j) (layerPart G j φ) +
        (a j / ((L : ℝ) ^ j) ^ 2) *
          ∑ y, (blockProjection (L ^ j) (N₀ * L ^ (k + 1 - j)) (layerPart G j φ) y) ^ 2) := by
    refine Finset.sum_le_sum fun j hj => ?_
    have hjk := (Finset.mem_Icc.1 hj).2
    have h1 := layer_ineq G hd (j := j) (by omega) (ha j (Finset.mem_Icc.1 hj).1 hjk).1 φ
    refine le_trans ?_ h1
    gcongr
    exact xPoincareConst_le_poincareConst d
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hper
  have htop := top_ineq (N₀ := N₀) hd hL hs₁ hs hcase (layerPart G (k + 1) φ)
  have hlay' : xPoincareConst d * ∑ y, invSqSpacing G y * φ y ^ 2 =
      ∑ j ∈ Icc 1 k, xPoincareConst d / ((L : ℝ) ^ j) ^ 2 * ∑ y, (layerPart G j φ y) ^ 2 +
        xPoincareConst d / ((L : ℝ) ^ (k + 1)) ^ 2 * ∑ y, (layerPart G (k + 1) φ y) ^ 2 := by
    rw [hlay, mul_add, Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [← mul_assoc, div_eq_mul_inv]
    · rw [← mul_assoc, div_eq_mul_inv]
  have hν' : 0 ≤ ν * ∑ y, φ y ^ 2 := mul_nonneg hν (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hlat : latticeEnergy φ = ∑ y, ∑ μ : Fin d, (φ (y + Pi.single μ 1) - φ y) ^ 2 := rfl
  rw [hlat] at hE ⊢
  rw [hlay']
  linarith

/-- **G-1(a′), real core.** For `ν ≥ 0`, `a_j ∈ [1/2, 2]` (`j ≤ k`), `a ∈ [1/2, 2]`, `x ≥ 0`,
`½ ‖∂φ‖² + c_x ‖ℓ⁻¹ φ‖² ≤ φᵀ (-Δ + ν + Q* a Q|_x) φ`, `c_x = min (1/d) (1/4)`, uniformly in `x`. -/
theorem xCore_real (hd : 0 < d) (hL : 3 ≤ L) (hk : 1 ≤ k) {a : ℕ → ℝ} {ν : ℝ} (hν : 0 ≤ ν)
    (ha : IsAdmissibleWeights k a) {aT x : ℝ} (haT1 : 1 / 2 ≤ aT) (haT2 : aT ≤ 2) (hx : 0 ≤ x)
    (φ : Torus d (N₀ * L ^ (k + 1)) → ℝ) :
    (1 / 2) * latticeEnergy φ + xPoincareConst d * ∑ y, invSqSpacing G y * φ y ^ 2 ≤
      φ ⬝ᵥ xFullMatrix G a (xS1 (a k) x) (xS2 (a k) (aT / (L : ℝ) ^ 2) x) ν *ᵥ φ :=
  xCore_real_of_ak G hd hL hν ha (ha k hk le_rfl) haT1 haT2 hx φ

end Core

section Complex

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}
variable (G : GeneratingSet d L N₀ (k + 1) ϱ)

/-- The constant `c_x/2` of the complex coercivity. -/
noncomputable def xCoerciveConst (d : ℕ) : ℝ := xPoincareConst d / 2

theorem xCoerciveConst_pos {d : ℕ} (hd : 0 < d) : 0 < xCoerciveConst d := by
  unfold xCoerciveConst
  have := xPoincareConst_pos hd
  positivity

theorem reQuad_xDirichletOperator (a : ℕ → ℝ) (aT x ν : ℝ) (α : G.Ω 1 → ℂ) (u : G.Ω 1 → ℂ) :
    Green.reQuad (xDirichletOperator G a aT x ν α) u =
      Green.reQuad ((xFullMatrix G a (xS1 (a k) x) (xS2 (a k) (aT / (L : ℝ) ^ 2) x) ν).map
        (algebraMap ℝ ℂ)) (zeroExt (G.Ω 1) u) + ∑ i, (α i).re * ‖u i‖ ^ 2 := by
  unfold xDirichletOperator
  rw [Green.reQuad_add, reQuad_restrictOp, reQuad_diagonal]

/-- Core of `x_multiscale_coercive` with `1 ≤ k` replaced by the lower bound `1/2 ≤ a_k` (the only use of `k ≥ 1`); the weights `a_j`, `1 ≤ j ≤ k`, stay in `[1/2, 2]`. -/
theorem x_multiscale_coercive_of_ak (hd : 0 < d) (hL : 3 ≤ L) {a : ℕ → ℝ} {ν : ℝ}
    (hν : 0 ≤ ν) (ha : IsAdmissibleWeights k a)
    (hak : 1 / 2 ≤ a k ∧ a k ≤ 2) {aT x : ℝ} (haT1 : 1 / 2 ≤ aT) (haT2 : aT ≤ 2)
    (hx : 0 ≤ x) (α : G.Ω 1 → ℂ)
    (hα : ∀ y, ‖α y‖ ≤ xCoerciveConst d / (2 * (G.spacing y) ^ 2)) (u : G.Ω 1 → ℂ) :
    xCoerciveConst d * (dirichletEnergy G u + weightedSqNorm G u) ≤
      Green.reQuad (xDirichletOperator G a aT x ν α) u := by
  rw [reQuad_xDirichletOperator, reQuad_map_ofReal]
  have h1 := xCore_real_of_ak G hd hL hν ha hak haT1 haT2 hx (fun y => (zeroExt (G.Ω 1) u y).re)
  have h2 := xCore_real_of_ak G hd hL hν ha hak haT1 haT2 hx (fun y => (zeroExt (G.Ω 1) u y).im)
  have hw := sum_invSqSpacing_eq G u
  have hsplit : ∑ y, invSqSpacing G y * ‖zeroExt (G.Ω 1) u y‖ ^ 2 =
      ∑ y, invSqSpacing G y * (zeroExt (G.Ω 1) u y).re ^ 2 +
        ∑ y, invSqSpacing G y * (zeroExt (G.Ω 1) u y).im ^ 2 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have hαs : -(xCoerciveConst d / 2 * weightedSqNorm G u) ≤ ∑ i, (α i).re * ‖u i‖ ^ 2 := by
    unfold weightedSqNorm
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    have hre : -(xCoerciveConst d / (2 * (G.spacing i) ^ 2)) ≤ (α i).re := by
      have := Complex.abs_re_le_norm (α i)
      have := hα i
      linarith [neg_abs_le (α i).re]
    have : -(xCoerciveConst d / 2 * (‖u i‖ ^ 2 / (G.spacing i) ^ 2)) =
        -(xCoerciveConst d / (2 * (G.spacing i) ^ 2)) * ‖u i‖ ^ 2 := by
      field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_right hre (sq_nonneg _)
  have hE := dirichletEnergy_eq G u
  have hc := xCoerciveConst_pos hd
  have hpc : xPoincareConst d = 2 * xCoerciveConst d := by unfold xCoerciveConst; ring
  have hle : xPoincareConst d ≤ 1 / 2 := (xPoincareConst_le_quarter d).trans (by norm_num)
  have hDE := dirichletEnergy_nonneg G u
  have hW := weightedSqNorm_nonneg G u
  rw [hpc] at h1 h2
  nlinarith

/-- **G-1(a′), the quadratic form** (uniform in `x ≥ 0`): for `|α₀(y)| ≤ c_x/(4 ℓ(y)²)`,
`(c_x/2) (‖∂ũ‖² + ‖ℓ⁻¹u‖²) ≤ Re ⟨u, H_{k,x}(α₀) u⟩`. -/
theorem x_multiscale_coercive (hd : 0 < d) (hL : 3 ≤ L) (hk : 1 ≤ k) {a : ℕ → ℝ} {ν : ℝ}
    (hν : 0 ≤ ν) (ha : IsAdmissibleWeights k a) {aT x : ℝ} (haT1 : 1 / 2 ≤ aT) (haT2 : aT ≤ 2)
    (hx : 0 ≤ x) (α : G.Ω 1 → ℂ)
    (hα : ∀ y, ‖α y‖ ≤ xCoerciveConst d / (2 * (G.spacing y) ^ 2)) (u : G.Ω 1 → ℂ) :
    xCoerciveConst d * (dirichletEnergy G u + weightedSqNorm G u) ≤
      Green.reQuad (xDirichletOperator G a aT x ν α) u :=
  x_multiscale_coercive_of_ak G hd hL hν ha (ha k hk le_rfl) haT1 haT2 hx α hα u

/-- Core of `xDirichletOperator_isCoercive` with `1 ≤ k` replaced by the lower bound `1/2 ≤ a_k` (the only use of `k ≥ 1`); the weights `a_j`, `1 ≤ j ≤ k`, stay in `[1/2, 2]`. -/
theorem xDirichletOperator_isCoercive_of_ak (hd : 0 < d) (hL : 3 ≤ L) {a : ℕ → ℝ}
    {ν : ℝ} (hν : 0 ≤ ν) (ha : IsAdmissibleWeights k a)
    (hak : 1 / 2 ≤ a k ∧ a k ≤ 2) {aT x : ℝ} (haT1 : 1 / 2 ≤ aT)
    (haT2 : aT ≤ 2) (hx : 0 ≤ x) (α : G.Ω 1 → ℂ)
    (hα : ∀ y, ‖α y‖ ≤ xCoerciveConst d / (2 * (G.spacing y) ^ 2)) {γ : ℝ}
    (hγ : ∀ y : G.Ω 1, γ ≤ ((G.spacing y) ^ 2)⁻¹) :
    Green.IsCoercive (xDirichletOperator G a aT x ν α) (xCoerciveConst d * γ) := by
  intro u
  have h := x_multiscale_coercive_of_ak G hd hL hν ha hak haT1 haT2 hx α hα u
  have hc := xCoerciveConst_pos hd
  have hsq : γ * Green.sqNorm u ≤ weightedSqNorm G u := by
    unfold Green.sqNorm weightedSqNorm
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun y _ => ?_
    rw [div_eq_mul_inv, mul_comm (‖u y‖ ^ 2)]
    exact mul_le_mul_of_nonneg_right (hγ y) (sq_nonneg _)
  have hDE := dirichletEnergy_nonneg G u
  nlinarith

/-- **G-1(a′), coercivity**, with `γ ≤ ℓ(y)⁻²` on `Ω₁`. -/
theorem xDirichletOperator_isCoercive (hd : 0 < d) (hL : 3 ≤ L) (hk : 1 ≤ k) {a : ℕ → ℝ}
    {ν : ℝ} (hν : 0 ≤ ν) (ha : IsAdmissibleWeights k a) {aT x : ℝ} (haT1 : 1 / 2 ≤ aT)
    (haT2 : aT ≤ 2) (hx : 0 ≤ x) (α : G.Ω 1 → ℂ)
    (hα : ∀ y, ‖α y‖ ≤ xCoerciveConst d / (2 * (G.spacing y) ^ 2)) {γ : ℝ}
    (hγ : ∀ y : G.Ω 1, γ ≤ ((G.spacing y) ^ 2)⁻¹) :
    Green.IsCoercive (xDirichletOperator G a aT x ν α) (xCoerciveConst d * γ) :=
  xDirichletOperator_isCoercive_of_ak G hd hL hν ha (ha k hk le_rfl) haT1 haT2 hx α hα hγ

/-- Core of `xDirichletOperator_isUnit` with `1 ≤ k` replaced by the lower bound `1/2 ≤ a_k` (the only use of `k ≥ 1`); the weights `a_j`, `1 ≤ j ≤ k`, stay in `[1/2, 2]`. -/
theorem xDirichletOperator_isUnit_of_ak (hd : 0 < d) (hL : 3 ≤ L) {a : ℕ → ℝ} {ν : ℝ}
    (hν : 0 ≤ ν) (ha : IsAdmissibleWeights k a)
    (hak : 1 / 2 ≤ a k ∧ a k ≤ 2) {aT x : ℝ} (haT1 : 1 / 2 ≤ aT) (haT2 : aT ≤ 2)
    (hx : 0 ≤ x) (α : G.Ω 1 → ℂ)
    (hα : ∀ y, ‖α y‖ ≤ xCoerciveConst d / (2 * (G.spacing y) ^ 2)) :
    IsUnit (xDirichletOperator G a aT x ν α) := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  refine Green.isUnit_of_isCoercive
    (mul_pos (xCoerciveConst_pos hd) (inv_pos.2 (by positivity)))
    (xDirichletOperator_isCoercive_of_ak G hd hL hν ha hak haT1 haT2 hx α hα
      (γ := (((L : ℝ) ^ (k + 1)) ^ 2)⁻¹) fun y => ?_)
  have hp : 0 < G.spacing y := spacing_pos G
  exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hp.le (spacing_le G y.2) 2)

/-- **G-1(a′), invertibility** of `H_{k,x}(α₀)`, uniformly in `x ≥ 0`. -/
theorem xDirichletOperator_isUnit (hd : 0 < d) (hL : 3 ≤ L) (hk : 1 ≤ k) {a : ℕ → ℝ} {ν : ℝ}
    (hν : 0 ≤ ν) (ha : IsAdmissibleWeights k a) {aT x : ℝ} (haT1 : 1 / 2 ≤ aT) (haT2 : aT ≤ 2)
    (hx : 0 ≤ x) (α : G.Ω 1 → ℂ)
    (hα : ∀ y, ‖α y‖ ≤ xCoerciveConst d / (2 * (G.spacing y) ^ 2)) :
    IsUnit (xDirichletOperator G a aT x ν α) :=
  xDirichletOperator_isUnit_of_ak G hd hL hν ha (ha k hk le_rfl) haT1 haT2 hx α hα

end Complex

end Balaban.Multiscale
