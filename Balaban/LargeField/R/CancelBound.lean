/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.CancelIdentity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# Lemma III.6.3: the bounds on the remainder `C^♮` (LF-RECONSTRUCTION §III.6.2, (III.6.1))

`C^♮ = C^♮_0 + C^♮_1` (`CnatGen_eq_zero_add_one`, `Cnat_eq_zero_add_one`), where `C^♮_1` (`Cnat1`) keeps
the part of each cross term `X_z = -β_k η_z a_k r_z·Q_zδψ`, `Y_z = β_k a^♮_z Q_zδψ·s_z` that is at most
`⅛`, resp. `¼`, of `β_k a^♮_z |Q_zδψ|²` (the two Cauchy-Schwarz parts of the proof), and `C^♮_0` (`Cnat0`)
is the rest.

* `Cnat1_le`: `|C^♮_1| ≤ ⅜ ∑_z β_k a^♮_z |Q_zδψ|²` (first bound of (III.6.1));
* `Cnat0_le`: `|C^♮_0| ≤ n (36 β_k η_k ρ² + 8 β_k ρ σ + 9 β_k σ² + N η_k)` for `|r_z| ≤ ρ`, `|s_z| ≤ σ`,
  `#Zb ≤ n`, with the BG weights `a_j ∈ [½, 2]` (1.5), `a^♮_z ∈ [½, 2]`, `|a^♮_z/a_z - 1| ≤ η_k ≤ ½`;
* `Cnat0_le_one`: `|C^♮_0| ≤ 1` on the real domain when the four terms are each `≤ ¼` (the consequences
  of (Λ19) used in the proof).  On the complex domain the same lemma gives the bound by the right side.

**Discrepancy with the reconstruction.**  The reconstruction states the bound on `C^♮_0` with the
constants `3, 4, 3, 1` (`∑_z[3β η|r|² + 4β|r||s| + 3β|s|²] + N η #z`) "for `a_k, a_z, a^♮_z ∈ [½, 2]`,
`η_k ≤ ½`".  These constants do not follow from those ranges: already the term
`β η a_k²/(2 a_z)|r|²` is `≤ 4 β η|r|²` there (and equals it for `a_k = 2`, `a_z = ½`), the Cauchy-Schwarz
remainder of `X_z` is `≤ 8 β η² a_k²|r|²/a^♮ ≤ 32 β η|r|²`, that of `Y_z` is `≤ 4 β a^♮|s|² ≤ 8 β|s|²`,
and `|ϱ_z| = (a_k/a_z)|r_z| ≤ 4|r_z|`.  The proved constants are `36, 8, 9, 1`; the numerical
conditions (Λ19) must be strengthened by these factors.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField.ActionConv

open Balaban Balaban.Multiscale Balaban.Background Balaban.LargeField Finset

section Norms

variable {N : ℕ}

theorem vn_const_mul (c : ℂ) (v : Fin N → ℂ) : vn (fun i => c * v i) = ‖c‖ * vn v := by
  rw [vn_eq_sqrt, vn_eq_sqrt]
  have : ∑ i, ‖c * v i‖ ^ 2 = ‖c‖ ^ 2 * ∑ i, ‖v i‖ ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [norm_mul]; ring
  rw [this, Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg c)]

theorem norm_dotC_le (u v : Fin N → ℂ) : ‖dotC u v‖ ≤ vn u * vn v := norm_dot_le u v

theorem dotC_sub_left (u u' v : Fin N → ℂ) :
    dotC (fun i => u i - u' i) v = dotC u v - dotC u' v := by
  unfold dotC
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem abs_log_one_add_le {x : ℝ} (hx : |x| ≤ 1 / 2) : |Real.log (1 + x)| ≤ 2 * |x| := by
  have hx1 := (abs_le.1 hx)
  have hpos : 0 < 1 + x := by linarith
  rcases le_or_gt 0 x with h0 | h0
  · rw [abs_of_nonneg h0]
    have h1 := Real.log_le_sub_one_of_pos hpos
    have h2 : 0 ≤ Real.log (1 + x) := Real.log_nonneg (by linarith)
    rw [abs_of_nonneg h2]; linarith
  · rw [abs_of_neg h0]
    have h1 := Real.log_le_sub_one_of_pos (inv_pos.2 hpos)
    have h2 : Real.log (1 + x) ≤ 0 := Real.log_nonpos hpos.le (by linarith)
    rw [abs_of_nonpos h2, ← Real.log_inv]
    have : (1 + x)⁻¹ - 1 ≤ -(2 * x) := by
      rw [inv_eq_one_div, div_sub_one hpos.ne', div_le_iff₀ hpos]
      nlinarith
    linarith

end Norms

section Split

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L]

/-- The term `X_z = -β_k η_z a_k r_z·Q_zδψ` of `R_{η,z}` linear in `δψ`. -/
noncomputable def Xz (βk ak az aN : ℝ) (r q : Fin N → ℂ) : ℂ :=
  -((βk : ℂ) * ((aN / az - 1 : ℝ) : ℂ) * (ak : ℂ)) * dotC r q

/-- The term `Y_z = β_k a^♮_z Q_zδψ·s_z` of `R_{s,z}` linear in `δψ`. -/
noncomputable def Yz (βk aN : ℝ) (q s : Fin N → ℂ) : ℂ := (βk : ℂ) * (aN : ℂ) * dotC q s

open Classical in
/-- The part of `X_z` kept in `C^♮_1`: all of `X_z` if it is `≤ ⅛ β_k a^♮_z |Q_zδψ|²`, else `0`. -/
noncomputable def keepX (βk ak az aN : ℝ) (r q : Fin N → ℂ) : ℂ :=
  if ‖Xz βk ak az aN r q‖ ≤ 1 / 8 * (βk * aN * vn q ^ 2) then Xz βk ak az aN r q else 0

open Classical in
/-- The part of `Y_z` kept in `C^♮_1`: all of `Y_z` if it is `≤ ¼ β_k a^♮_z |Q_zδψ|²`, else `0`. -/
noncomputable def keepY (βk aN : ℝ) (q s : Fin N → ℂ) : ℂ :=
  if ‖Yz βk aN q s‖ ≤ 1 / 4 * (βk * aN * vn q ^ 2) then Yz βk aN q s else 0

/-- **`C^♮_1`** (LFR (III.6.1)): the parts of the cross terms `∑_z (X_z + Y_z)` bounded by `⅛` and `¼` of
`β_k a^♮_z |Q_zδψ|²` (the two Cauchy-Schwarz parts of the proof of Lemma III.6.3). -/
noncomputable def CnatGen1 (Zb : Finset (Torus d (N₀ * L ^ (k - k)))) (βk ak : ℝ)
    (az aN : Torus d (N₀ * L ^ (k - k)) → ℝ) (r q s : Torus d (N₀ * L ^ (k - k)) → Fin N → ℂ) : ℂ :=
  ∑ z ∈ Zb, (keepX βk ak (az z) (aN z) (r z) (q z) + keepY βk (aN z) (q z) (s z))

/-- **`C^♮_0`** (LFR (III.6.1)): the rest, `C^♮ - C^♮_1`. -/
noncomputable def CnatGen0 (Zb : Finset (Torus d (N₀ * L ^ (k - k)))) (βk ak : ℝ)
    (az aN : Torus d (N₀ * L ^ (k - k)) → ℝ) (r q s ϱ : Torus d (N₀ * L ^ (k - k)) → Fin N → ℂ) : ℂ :=
  CnatGen N Zb βk ak az aN r q s ϱ - CnatGen1 Zb βk ak az aN r q s

theorem CnatGen_eq_zero_add_one (Zb : Finset (Torus d (N₀ * L ^ (k - k)))) (βk ak : ℝ)
    (az aN : Torus d (N₀ * L ^ (k - k)) → ℝ) (r q s ϱ : Torus d (N₀ * L ^ (k - k)) → Fin N → ℂ) :
    CnatGen N Zb βk ak az aN r q s ϱ =
      CnatGen0 Zb βk ak az aN r q s ϱ + CnatGen1 Zb βk ak az aN r q s := by
  unfold CnatGen0; ring

/-- **`‖C^♮_1‖ ≤ ⅜ ∑_z β_k a^♮_z |Q_zδψ|²`** (III.6.1, first bound). -/
theorem norm_CnatGen1_le (Zb : Finset (Torus d (N₀ * L ^ (k - k)))) {βk : ℝ} (hβ : 0 ≤ βk)
    (ak : ℝ) (az aN : Torus d (N₀ * L ^ (k - k)) → ℝ) (haN : ∀ z ∈ Zb, 0 ≤ aN z)
    (r q s : Torus d (N₀ * L ^ (k - k)) → Fin N → ℂ) :
    ‖CnatGen1 Zb βk ak az aN r q s‖ ≤ 3 / 8 * ∑ z ∈ Zb, βk * aN z * vn (q z) ^ 2 := by
  unfold CnatGen1
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun z hz => ?_
  refine (norm_add_le _ _).trans ?_
  have hnn : 0 ≤ βk * aN z * vn (q z) ^ 2 := mul_nonneg (mul_nonneg hβ (haN z hz)) (sq_nonneg _)
  have h1 : ‖keepX βk ak (az z) (aN z) (r z) (q z)‖ ≤ 1 / 8 * (βk * aN z * vn (q z) ^ 2) := by
    unfold keepX
    split_ifs with h
    · exact h
    · simp only [norm_zero]; linarith
  have h2 : ‖keepY βk (aN z) (q z) (s z)‖ ≤ 1 / 4 * (βk * aN z * vn (q z) ^ 2) := by
    unfold keepY
    split_ifs with h
    · exact h
    · simp only [norm_zero]; linarith
  linarith

theorem key_cs {c m t Xn : ℝ} (hc : 0 < c) (hm : 0 ≤ m) (ht : 0 ≤ t) (hX : Xn ≤ m * t)
    (hnot : c * t ^ 2 < Xn) : Xn ≤ m ^ 2 / c := by
  have ht0 : 0 < t := by
    rcases ht.lt_or_eq with h | h
    · exact h
    · rw [← h] at hnot hX; simp at hnot hX; linarith
  have h1 : c * t < m := by
    by_contra hcon
    push Not at hcon
    nlinarith [mul_le_mul_of_nonneg_right hcon ht0.le]
  rw [le_div_iff₀ hc]
  nlinarith [mul_le_mul_of_nonneg_right h1.le ht, mul_nonneg hm ht]


/-- The remaining part `W_z` of `R_{η,z} + R_{s,z}` (no term linear in `Q_zδψ`). -/
noncomputable def Wz (βk ak az aN : ℝ) (r s ϱ : Fin N → ℂ) : ℂ :=
  (βk : ℂ) * ((aN / az - 1 : ℝ) : ℂ) * (((ak ^ 2 / (2 * az) : ℝ) : ℂ) * dotC r r) -
    (βk : ℂ) * (aN : ℂ) * dotC ϱ s + (1 / 2 : ℂ) * (βk : ℂ) * (aN : ℂ) * dotC s s

theorem Reta_add_Rs_eq (βk ak az aN : ℝ) (r q s ϱ : Fin N → ℂ) :
    Reta βk ak az aN r q + Rs βk aN ϱ q s =
      Xz βk ak az aN r q + Yz βk aN q s + Wz βk ak az aN r s ϱ := by
  unfold Reta Rs Xz Yz Wz
  rw [dotC_sub_left]
  ring

theorem norm_Xz_le {βk ak az aN : ℝ} (hβ : 0 ≤ βk) (hak : 0 ≤ ak) (r q : Fin N → ℂ) :
    ‖Xz βk ak az aN r q‖ ≤ (βk * |aN / az - 1| * ak * vn r) * vn q := by
  unfold Xz
  rw [norm_mul, norm_neg, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
    Complex.norm_real, Real.norm_of_nonneg hβ, Real.norm_eq_abs, Real.norm_of_nonneg hak]
  calc βk * |aN / az - 1| * ak * ‖dotC r q‖ ≤ βk * |aN / az - 1| * ak * (vn r * vn q) := by
        gcongr; exact norm_dotC_le r q
    _ = _ := by ring

theorem norm_Yz_le {βk aN : ℝ} (hβ : 0 ≤ βk) (haN : 0 ≤ aN) (q s : Fin N → ℂ) :
    ‖Yz βk aN q s‖ ≤ (βk * aN * vn s) * vn q := by
  unfold Yz
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hβ,
    Real.norm_of_nonneg haN]
  calc βk * aN * ‖dotC q s‖ ≤ βk * aN * (vn q * vn s) := by
        gcongr; exact norm_dotC_le q s
    _ = _ := by ring

theorem norm_sub_keepX_le {βk ak az aN : ℝ} (hβ : 0 ≤ βk) (hak : 0 ≤ ak) (haN : 0 < aN)
    (r q : Fin N → ℂ) :
    ‖Xz βk ak az aN r q - keepX βk ak az aN r q‖ ≤
      8 * βk * (aN / az - 1) ^ 2 * ak ^ 2 * vn r ^ 2 / aN := by
  have hnn : 0 ≤ 8 * βk * (aN / az - 1) ^ 2 * ak ^ 2 * vn r ^ 2 / aN := by positivity
  unfold keepX
  split_ifs with h
  · simpa using hnn
  · rw [sub_zero]
    have hb : βk ≠ 0 := by
      intro hb0
      apply h
      have := norm_Xz_le (az := az) (aN := aN) hβ hak r q
      rw [hb0] at this ⊢
      simp at this ⊢
      exact this
    have hbpos : 0 < βk := lt_of_le_of_ne hβ (Ne.symm hb)
    have hc : 0 < βk * aN / 8 := by positivity
    have hnot : βk * aN / 8 * vn q ^ 2 < ‖Xz βk ak az aN r q‖ := by
      push Not at h; linarith
    have := key_cs hc (m := βk * |aN / az - 1| * ak * vn r) (t := vn q)
      (mul_nonneg (mul_nonneg (mul_nonneg hβ (abs_nonneg _)) hak) (vn_nonneg r))
      (vn_nonneg q) (norm_Xz_le hβ hak r q) hnot
    refine this.trans (le_of_eq ?_)
    rw [mul_pow, mul_pow, mul_pow, sq_abs]
    field_simp

theorem norm_sub_keepY_le {βk aN : ℝ} (hβ : 0 ≤ βk) (haN : 0 < aN) (q s : Fin N → ℂ) :
    ‖Yz βk aN q s - keepY βk aN q s‖ ≤ 4 * βk * aN * vn s ^ 2 := by
  have hnn : 0 ≤ 4 * βk * aN * vn s ^ 2 := by positivity
  unfold keepY
  split_ifs with h
  · simpa using hnn
  · rw [sub_zero]
    have hb : βk ≠ 0 := by
      intro hb0
      apply h
      have := norm_Yz_le (βk := βk) (aN := aN) hβ haN.le q s
      rw [hb0] at this ⊢
      simp at this ⊢
      exact this
    have hbpos : 0 < βk := lt_of_le_of_ne hβ (Ne.symm hb)
    have hc : 0 < βk * aN / 4 := by positivity
    have hnot : βk * aN / 4 * vn q ^ 2 < ‖Yz βk aN q s‖ := by
      push Not at h; linarith
    have := key_cs hc (m := βk * aN * vn s) (t := vn q)
      (mul_nonneg (mul_nonneg hβ haN.le) (vn_nonneg s))
      (vn_nonneg q) (norm_Yz_le hβ haN.le q s) hnot
    refine this.trans (le_of_eq ?_)
    field_simp


theorem norm_Wz_le {βk ak az aN ηk : ℝ} (hβ : 0 ≤ βk) (hak : 0 < ak) (hak2 : ak ≤ 2)
    (haz : 1 / 2 ≤ az) (haN : 1 / 2 ≤ aN) (haN2 : aN ≤ 2) (hη : |aN / az - 1| ≤ ηk)
    (r s ϱ : Fin N → ℂ) (hϱ : ∀ i, ϱ i = ((ak / az : ℝ) : ℂ) * r i) :
    ‖Wz βk ak az aN r s ϱ‖ ≤
      4 * βk * ηk * vn r ^ 2 + 8 * βk * vn r * vn s + βk * vn s ^ 2 := by
  have hazpos : 0 < az := by linarith
  have hϱv : vn ϱ = ak / az * vn r := by
    have : ϱ = fun i => ((ak / az : ℝ) : ℂ) * r i := funext hϱ
    rw [this, vn_const_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hρ := vn_nonneg r
  have hσ := vn_nonneg s
  have hη0 : 0 ≤ ηk := (abs_nonneg _).trans hη
  have hcoef : ak ^ 2 / (2 * az) ≤ 4 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have hratio : ak / az ≤ 4 := by
    rw [div_le_iff₀ hazpos]; nlinarith
  have hA : ‖(βk : ℂ) * ((aN / az - 1 : ℝ) : ℂ) * (((ak ^ 2 / (2 * az) : ℝ) : ℂ) * dotC r r)‖ ≤
      4 * βk * ηk * vn r ^ 2 := by
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg hβ, Real.norm_eq_abs, Real.norm_of_nonneg (by positivity)]
    have h1 : ‖dotC r r‖ ≤ vn r ^ 2 := by
      have := norm_dotC_le r r; nlinarith
    calc βk * |aN / az - 1| * (ak ^ 2 / (2 * az) * ‖dotC r r‖)
        ≤ βk * ηk * (4 * vn r ^ 2) := by
          have h2 : 0 ≤ ‖dotC r r‖ := norm_nonneg _
          gcongr
      _ = _ := by ring
  have hB : ‖(βk : ℂ) * (aN : ℂ) * dotC ϱ s‖ ≤ 8 * βk * vn r * vn s := by
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hβ,
      Real.norm_of_nonneg (by linarith)]
    have h1 := norm_dotC_le ϱ s
    rw [hϱv] at h1
    calc βk * aN * ‖dotC ϱ s‖ ≤ βk * aN * (ak / az * vn r * vn s) := by gcongr
      _ ≤ βk * 2 * (4 * vn r * vn s) := by
          have : 0 ≤ vn r * vn s := mul_nonneg hρ hσ
          have h2 : ak / az * vn r * vn s ≤ 4 * vn r * vn s := by
            nlinarith [mul_le_mul_of_nonneg_right hratio this]
          have h3 : 0 ≤ ak / az * vn r * vn s := by positivity
          gcongr
      _ = _ := by ring
  have hC : ‖(1 / 2 : ℂ) * (βk : ℂ) * (aN : ℂ) * dotC s s‖ ≤ βk * vn s ^ 2 := by
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg hβ, Real.norm_of_nonneg (by linarith)]
    have h1 : ‖dotC s s‖ ≤ vn s ^ 2 := by
      have := norm_dotC_le s s; nlinarith
    have h4 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
    rw [h4]
    calc 1 / 2 * βk * aN * ‖dotC s s‖ ≤ 1 / 2 * βk * 2 * vn s ^ 2 := by gcongr
      _ = _ := by ring
  unfold Wz
  calc _ ≤ ‖(βk : ℂ) * ((aN / az - 1 : ℝ) : ℂ) * (((ak ^ 2 / (2 * az) : ℝ) : ℂ) * dotC r r) -
        (βk : ℂ) * (aN : ℂ) * dotC ϱ s‖ + ‖(1 / 2 : ℂ) * (βk : ℂ) * (aN : ℂ) * dotC s s‖ :=
        norm_add_le _ _
    _ ≤ (‖(βk : ℂ) * ((aN / az - 1 : ℝ) : ℂ) * (((ak ^ 2 / (2 * az) : ℝ) : ℂ) * dotC r r)‖ +
          ‖(βk : ℂ) * (aN : ℂ) * dotC ϱ s‖) + ‖(1 / 2 : ℂ) * (βk : ℂ) * (aN : ℂ) * dotC s s‖ := by
        gcongr; exact norm_sub_le _ _
    _ ≤ _ := by linarith

/-- The per-block bound on the non-linear remainder: `|X - X₁| + |Y - Y₁| + |W| ≤ 36 β η_k |r|² +
8 β |r||s| + 9 β |s|²` for `a_k ≤ 2`, `a_z, a^♮_z ∈ [½, 2]`, `|a^♮/a_z - 1| ≤ η_k ≤ ½`. -/
theorem norm_C0z_le {βk ak az aN ηk : ℝ} (hβ : 0 ≤ βk) (hak : 0 < ak) (hak2 : ak ≤ 2)
    (haz : 1 / 2 ≤ az) (haN : 1 / 2 ≤ aN) (haN2 : aN ≤ 2) (hη : |aN / az - 1| ≤ ηk)
    (hηk : ηk ≤ 1 / 2) (r q s ϱ : Fin N → ℂ) (hϱ : ∀ i, ϱ i = ((ak / az : ℝ) : ℂ) * r i) :
    ‖(Xz βk ak az aN r q - keepX βk ak az aN r q) + (Yz βk aN q s - keepY βk aN q s) +
        Wz βk ak az aN r s ϱ‖ ≤
      36 * βk * ηk * vn r ^ 2 + 8 * βk * vn r * vn s + 9 * βk * vn s ^ 2 := by
  have hρ := vn_nonneg r
  have hσ := vn_nonneg s
  have hη0 : 0 ≤ ηk := (abs_nonneg _).trans hη
  have hX := norm_sub_keepX_le (az := az) hβ hak.le (by linarith : 0 < aN) r q
  have hY := norm_sub_keepY_le hβ (by linarith : 0 < aN) q s
  have hW := norm_Wz_le hβ hak hak2 haz haN haN2 hη r s ϱ hϱ
  have hX' : 8 * βk * (aN / az - 1) ^ 2 * ak ^ 2 * vn r ^ 2 / aN ≤ 32 * βk * ηk * vn r ^ 2 := by
    rw [div_le_iff₀ (by linarith)]
    have h1 : (aN / az - 1) ^ 2 ≤ ηk / 2 := by
      have : (aN / az - 1) ^ 2 = |aN / az - 1| ^ 2 := (sq_abs _).symm
      rw [this]
      nlinarith [abs_nonneg (aN / az - 1)]
    have h2 : ak ^ 2 ≤ 4 := by nlinarith
    have hP : 0 ≤ βk * vn r ^ 2 := by positivity
    have h3 : 8 * βk * (aN / az - 1) ^ 2 * ak ^ 2 * vn r ^ 2 ≤ 8 * (ηk / 2) * 4 * (βk * vn r ^ 2) := by
      have e : 8 * βk * (aN / az - 1) ^ 2 * ak ^ 2 * vn r ^ 2 =
          8 * ((aN / az - 1) ^ 2 * ak ^ 2) * (βk * vn r ^ 2) := by ring
      rw [e, show 8 * (ηk / 2) * 4 * (βk * vn r ^ 2) = 8 * ((ηk / 2) * 4) * (βk * vn r ^ 2) by ring]
      have : (aN / az - 1) ^ 2 * ak ^ 2 ≤ (ηk / 2) * 4 := by
        calc (aN / az - 1) ^ 2 * ak ^ 2 ≤ (ηk / 2) * ak ^ 2 := by gcongr
          _ ≤ (ηk / 2) * 4 := by gcongr
      gcongr
    nlinarith [mul_nonneg hη0 hP]
  have hY' : 4 * βk * aN * vn s ^ 2 ≤ 8 * βk * vn s ^ 2 := by
    have : 0 ≤ βk * vn s ^ 2 := by positivity
    nlinarith
  calc _ ≤ ‖Xz βk ak az aN r q - keepX βk ak az aN r q‖ + ‖Yz βk aN q s - keepY βk aN q s‖ +
        ‖Wz βk ak az aN r s ϱ‖ := by
        refine (norm_add_le _ _).trans ?_
        gcongr; exact norm_add_le _ _
    _ ≤ _ := by linarith


theorem CnatGen0_eq (Zb : Finset (Torus d (N₀ * L ^ (k - k)))) (βk ak : ℝ)
    (az aN : Torus d (N₀ * L ^ (k - k)) → ℝ) (r q s ϱ : Torus d (N₀ * L ^ (k - k)) → Fin N → ℂ) :
    CnatGen0 Zb βk ak az aN r q s ϱ =
      ∑ z ∈ Zb, ((Xz βk ak (az z) (aN z) (r z) (q z) - keepX βk ak (az z) (aN z) (r z) (q z)) +
        (Yz βk (aN z) (q z) (s z) - keepY βk (aN z) (q z) (s z)) +
        Wz βk ak (az z) (aN z) (r z) (s z) (ϱ z)) -
      ((N : ℂ) / 2) * ∑ z ∈ Zb, ((Real.log (aN z / az z) : ℝ) : ℂ) := by
  unfold CnatGen0 CnatGen CnatGen1
  have h1 : ∑ z ∈ Zb, (Reta βk ak (az z) (aN z) (r z) (q z) + Rs βk (aN z) (ϱ z) (q z) (s z)) =
      ∑ z ∈ Zb, (Xz βk ak (az z) (aN z) (r z) (q z) + Yz βk (aN z) (q z) (s z) +
        Wz βk ak (az z) (aN z) (r z) (s z) (ϱ z)) :=
    Finset.sum_congr rfl fun z _ => Reta_add_Rs_eq _ _ _ _ _ _ _ _
  rw [h1]
  have h2 : ∑ z ∈ Zb, ((Xz βk ak (az z) (aN z) (r z) (q z) - keepX βk ak (az z) (aN z) (r z) (q z)) +
        (Yz βk (aN z) (q z) (s z) - keepY βk (aN z) (q z) (s z)) +
        Wz βk ak (az z) (aN z) (r z) (s z) (ϱ z)) =
      ∑ z ∈ Zb, (Xz βk ak (az z) (aN z) (r z) (q z) + Yz βk (aN z) (q z) (s z) +
        Wz βk ak (az z) (aN z) (r z) (s z) (ϱ z)) -
      ∑ z ∈ Zb, (keepX βk ak (az z) (aN z) (r z) (q z) + keepY βk (aN z) (q z) (s z)) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun z _ => by ring
  rw [h2]
  ring

/-- **`‖C^♮_0‖`, general bound** (proof of Lemma III.6.3, "Bounds"): for `a_k ≤ 2`, `a_z, a^♮_z ∈ [½, 2]`,
`|a^♮_z/a_z - 1| ≤ η_k ≤ ½`,
`‖C^♮_0‖ ≤ ∑_z [36 β_k η_k |r_z|² + 8 β_k |r_z||s_z| + 9 β_k |s_z|²] + N η_k #Zb`. -/
theorem norm_CnatGen0_le (Zb : Finset (Torus d (N₀ * L ^ (k - k)))) {βk ak ηk : ℝ} (hβ : 0 ≤ βk)
    (hak : 0 < ak) (hak2 : ak ≤ 2) (az aN : Torus d (N₀ * L ^ (k - k)) → ℝ)
    (r q s ϱ : Torus d (N₀ * L ^ (k - k)) → Fin N → ℂ)
    (haz : ∀ z ∈ Zb, 1 / 2 ≤ az z) (haN : ∀ z ∈ Zb, 1 / 2 ≤ aN z) (haN2 : ∀ z ∈ Zb, aN z ≤ 2)
    (hη : ∀ z ∈ Zb, |aN z / az z - 1| ≤ ηk) (hηk : ηk ≤ 1 / 2)
    (hϱ : ∀ z ∈ Zb, ∀ i, ϱ z i = ((ak / az z : ℝ) : ℂ) * r z i) :
    ‖CnatGen0 Zb βk ak az aN r q s ϱ‖ ≤
      ∑ z ∈ Zb, (36 * βk * ηk * vn (r z) ^ 2 + 8 * βk * vn (r z) * vn (s z) +
        9 * βk * vn (s z) ^ 2) + N * ηk * Zb.card := by
  rw [CnatGen0_eq]
  refine (norm_sub_le _ _).trans ?_
  have h1 : ‖∑ z ∈ Zb, ((Xz βk ak (az z) (aN z) (r z) (q z) -
        keepX βk ak (az z) (aN z) (r z) (q z)) +
        (Yz βk (aN z) (q z) (s z) - keepY βk (aN z) (q z) (s z)) +
        Wz βk ak (az z) (aN z) (r z) (s z) (ϱ z))‖ ≤
      ∑ z ∈ Zb, (36 * βk * ηk * vn (r z) ^ 2 + 8 * βk * vn (r z) * vn (s z) +
        9 * βk * vn (s z) ^ 2) :=
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun z hz =>
      norm_C0z_le hβ hak hak2 (haz z hz) (haN z hz) (haN2 z hz) (hη z hz) hηk _ _ _ _ (hϱ z hz))
  have h2 : ‖((N : ℂ) / 2) * ∑ z ∈ Zb, ((Real.log (aN z / az z) : ℝ) : ℂ)‖ ≤
      N * ηk * Zb.card := by
    rw [norm_mul]
    have hN : ‖((N : ℂ) / 2)‖ = (N : ℝ) / 2 := by
      rw [norm_div]; simp
    rw [hN]
    have h3 : ‖∑ z ∈ Zb, ((Real.log (aN z / az z) : ℝ) : ℂ)‖ ≤ ∑ z ∈ Zb, 2 * ηk := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun z hz => ?_)
      rw [Complex.norm_real, Real.norm_eq_abs]
      have hpos : 0 < az z := by have := haz z hz; linarith
      have e : aN z / az z = 1 + (aN z / az z - 1) := by ring
      rw [e]
      refine (abs_log_one_add_le ((hη z hz).trans hηk)).trans ?_
      have := hη z hz
      linarith
    rw [Finset.sum_const, nsmul_eq_mul] at h3
    calc (N : ℝ) / 2 * ‖∑ z ∈ Zb, ((Real.log (aN z / az z) : ℝ) : ℂ)‖
        ≤ (N : ℝ) / 2 * (Zb.card * (2 * ηk)) := by gcongr
      _ = _ := by ring
  linarith

/-- **`‖C^♮_0‖ ≤ #Zb · (36 β_k η_k ρ² + 8 β_k ρ σ + 9 β_k σ² + N η_k)`** for `|r_z| ≤ ρ`, `|s_z| ≤ σ`,
`#Zb ≤ n`. -/
theorem norm_CnatGen0_le_uniform (Zb : Finset (Torus d (N₀ * L ^ (k - k)))) {βk ak ηk ρ σ n : ℝ}
    (hβ : 0 ≤ βk) (hak : 0 < ak) (hak2 : ak ≤ 2) (az aN : Torus d (N₀ * L ^ (k - k)) → ℝ)
    (r q s ϱ : Torus d (N₀ * L ^ (k - k)) → Fin N → ℂ)
    (haz : ∀ z ∈ Zb, 1 / 2 ≤ az z) (haN : ∀ z ∈ Zb, 1 / 2 ≤ aN z) (haN2 : ∀ z ∈ Zb, aN z ≤ 2)
    (hη : ∀ z ∈ Zb, |aN z / az z - 1| ≤ ηk) (hηk : ηk ≤ 1 / 2)
    (hϱ : ∀ z ∈ Zb, ∀ i, ϱ z i = ((ak / az z : ℝ) : ℂ) * r z i)
    (hr : ∀ z ∈ Zb, vn (r z) ≤ ρ) (hs : ∀ z ∈ Zb, vn (s z) ≤ σ) (hn : (Zb.card : ℝ) ≤ n)
    (hη0 : 0 ≤ ηk) (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) :
    ‖CnatGen0 Zb βk ak az aN r q s ϱ‖ ≤
      n * (36 * βk * ηk * ρ ^ 2 + 8 * βk * ρ * σ + 9 * βk * σ ^ 2 + N * ηk) := by
  refine (norm_CnatGen0_le Zb hβ hak hak2 az aN r q s ϱ haz haN haN2 hη hηk hϱ).trans ?_
  have hterm : ∀ z ∈ Zb, 36 * βk * ηk * vn (r z) ^ 2 + 8 * βk * vn (r z) * vn (s z) +
      9 * βk * vn (s z) ^ 2 ≤ 36 * βk * ηk * ρ ^ 2 + 8 * βk * ρ * σ + 9 * βk * σ ^ 2 := by
    intro z hz
    have h1 := hr z hz
    have h2 := hs z hz
    have h3 := vn_nonneg (r z)
    have h4 := vn_nonneg (s z)
    have : 0 ≤ βk * ηk := mul_nonneg hβ hη0
    have h5 : 0 ≤ ρ := hρ
    gcongr
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_const, nsmul_eq_mul] at hsum
  have hP : 0 ≤ 36 * βk * ηk * ρ ^ 2 + 8 * βk * ρ * σ + 9 * βk * σ ^ 2 + N * ηk := by positivity
  have hcard : (0 : ℝ) ≤ Zb.card := Nat.cast_nonneg _
  nlinarith [mul_le_mul_of_nonneg_right hn hP]


end Split

section Window

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ ϱ' : ℝ}
  {G : GeneratingSet d L N₀ k ϱ} {G' : GeneratingSet d L N₀ k ϱ'}

theorem compWeightZ_mem {a₁ : ℝ} (hadm : IsAdmissibleWeights k (compWeight L a₁))
    {z : Torus d (N₀ * L ^ (k - k))}
    (hn : ∀ x ∈ fib d L N₀ k k z, 1 ≤ G.layerIndex x ∧ G.layerIndex x < k) :
    1 / 2 ≤ compWeightZ G a₁ z ∧ compWeightZ G a₁ z ≤ 2 := by
  have hVcard : ((fib d L N₀ k k z).card : ℝ) = blockVol d L k := by
    rw [card_fib le_rfl, blockVol_eq]; push_cast; rfl
  have hV : 0 < blockVol d L k := blockVol_pos (d := d) (k := k) (NeZero.pos L)
  have hu : ∀ x ∈ fib d L N₀ k k z, 1 / 2 ≤ (compWeight L a₁ (k - G.layerIndex x))⁻¹ ∧
      (compWeight L a₁ (k - G.layerIndex x))⁻¹ ≤ 2 := by
    intro x hx
    obtain ⟨h1, h2⟩ := hn x hx
    obtain ⟨hl, hr⟩ := hadm (k - G.layerIndex x) (by omega) (by omega)
    constructor
    · rw [one_div]; exact inv_anti₀ (by linarith) hr
    · calc (compWeight L a₁ (k - G.layerIndex x))⁻¹ ≤ (1 / 2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hl
        _ = 2 := by norm_num
  have hlo : (fib d L N₀ k k z).card • (1 / 2 : ℝ) ≤
      ∑ x ∈ fib d L N₀ k k z, (compWeight L a₁ (k - G.layerIndex x))⁻¹ :=
    Finset.card_nsmul_le_sum _ _ _ fun x hx => (hu x hx).1
  have hhi : ∑ x ∈ fib d L N₀ k k z, (compWeight L a₁ (k - G.layerIndex x))⁻¹ ≤
      (fib d L N₀ k k z).card • (2 : ℝ) :=
    Finset.sum_le_card_nsmul _ _ _ fun x hx => (hu x hx).2
  rw [nsmul_eq_mul, hVcard] at hlo hhi
  have hz : (compWeightZ G a₁ z)⁻¹ = (blockVol d L k)⁻¹ *
      ∑ s ∈ fib d L N₀ k k z, (compWeight L a₁ (k - G.layerIndex s))⁻¹ := by
    unfold compWeightZ; rw [inv_inv]
  have hlo' : 1 / 2 ≤ (compWeightZ G a₁ z)⁻¹ := by
    rw [hz]
    calc (1 / 2 : ℝ) = (blockVol d L k)⁻¹ * (blockVol d L k * (1 / 2)) := by field_simp
      _ ≤ _ := by gcongr
  have hhi' : (compWeightZ G a₁ z)⁻¹ ≤ 2 := by
    rw [hz]
    calc _ ≤ (blockVol d L k)⁻¹ * (blockVol d L k * 2) := by gcongr
      _ = 2 := by field_simp
  have hpos : 0 < (compWeightZ G a₁ z)⁻¹ := by linarith
  constructor
  · rw [← inv_inv (compWeightZ G a₁ z)]
    calc ((compWeightZ G a₁ z)⁻¹)⁻¹ ≥ (2 : ℝ)⁻¹ := inv_anti₀ hpos hhi'
      _ = 1 / 2 := by norm_num
  · rw [← inv_inv (compWeightZ G a₁ z)]
    calc ((compWeightZ G a₁ z)⁻¹)⁻¹ ≤ (1 / 2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hlo'
      _ = 2 := by norm_num

end Window

section WindowBound

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ ϱ' : ℝ}
  {G : GeneratingSet d L N₀ k ϱ} {G' : GeneratingSet d L N₀ k ϱ'}
  (a₁ : ℝ) (hprec : Precedes G G') (ψ0 : BlockV d L N₀ k → EuclideanSpace ℝ (Fin N))
  (h : Fin N → ℝ)

/-- **`C^♮_1`** of the window (LFR (III.6.1)). -/
noncomputable def Cnat1 (Du : BgData G N) (Zb : Finset (Torus d (N₀ * L ^ (k - k)))) (β0 : ℝ)
    (ϖ : ℕ → ℝ) (aN : Torus d (N₀ * L ^ (k - k)) → ℝ) : ℂ :=
  CnatGen1 Zb (betaK d L k β0) (compWeight L a₁ k) (compWeightZ G a₁) aN
    (rBlk G' (compWeight L a₁) ψ0 h)
    (fun z => kAvg (dataInc (windowData G G' hprec (compWeight L a₁) ψ0 h) Du) z)
    (sBlk G ϖ Du.Ψ)

/-- **`C^♮_0`** of the window (LFR (III.6.1)): `C^♮ - C^♮_1`. -/
noncomputable def Cnat0 (Du : BgData G N) (Zb : Finset (Torus d (N₀ * L ^ (k - k)))) (β0 : ℝ)
    (ϖ : ℕ → ℝ) (aN : Torus d (N₀ * L ^ (k - k)) → ℝ)
    (ψk : Torus d (N₀ * L ^ (k - k)) → Fin N → ℂ) : ℂ :=
  CnatGen0 Zb (betaK d L k β0) (compWeight L a₁ k) (compWeightZ G a₁) aN
    (rBlk G' (compWeight L a₁) ψ0 h)
    (fun z => kAvg (dataInc (windowData G G' hprec (compWeight L a₁) ψ0 h) Du) z)
    (sBlk G ϖ Du.Ψ)
    (fun z i => ψk z i - kAvg (windowData G G' hprec (compWeight L a₁) ψ0 h).Ψ z i)

theorem Cnat_eq_zero_add_one (Du : BgData G N) (Zb : Finset (Torus d (N₀ * L ^ (k - k)))) (β0 : ℝ)
    (ϖ : ℕ → ℝ) (aN : Torus d (N₀ * L ^ (k - k)) → ℝ)
    (ψk : Torus d (N₀ * L ^ (k - k)) → Fin N → ℂ) :
    Cnat a₁ hprec ψ0 h Du Zb β0 ϖ aN ψk =
      Cnat0 a₁ hprec ψ0 h Du Zb β0 ϖ aN ψk + Cnat1 a₁ hprec ψ0 h Du Zb β0 ϖ aN :=
  CnatGen_eq_zero_add_one _ _ _ _ _ _ _ _ _

/-- **Lemma III.6.3, bound on `C^♮_1`** (III.6.1): `|C^♮_1| ≤ ⅜ ∑_z β_k a^♮_z |Q_zδψ|²`. -/
theorem Cnat1_le (Du : BgData G N) (Zb : Finset (Torus d (N₀ * L ^ (k - k)))) {β0 : ℝ}
    (hβ0 : 0 ≤ β0) (ϖ : ℕ → ℝ) (aN : Torus d (N₀ * L ^ (k - k)) → ℝ)
    (haN : ∀ z ∈ Zb, 0 ≤ aN z) :
    ‖Cnat1 a₁ hprec ψ0 h Du Zb β0 ϖ aN‖ ≤ 3 / 8 * ∑ z ∈ Zb, betaK d L k β0 * aN z *
      vn (kAvg (dataInc (windowData G G' hprec (compWeight L a₁) ψ0 h) Du) z) ^ 2 :=
  norm_CnatGen1_le Zb (by unfold betaK; positivity) _ _ _ haN _ _ _

/-- **Lemma III.6.3, general bound on `C^♮_0`** (III.6.1, proof of the Bounds): with the geometry of
`cancellation_identity` (only the facts needed for `ϱ_z = (a_k/a_z) r_z`), the BG weights
`a_j ∈ [½, 2]` (1.5), `a^♮_z ∈ [½, 2]`, `|a^♮_z/a_z - 1| ≤ η_k ≤ ½`, `|r_z| ≤ ρ`, `|s_z| ≤ σ`, `#Zb ≤ n`:
`|C^♮_0| ≤ n (36 β_k η_k ρ² + 8 β_k ρ σ + 9 β_k σ² + N η_k)`.  (The reconstruction writes the
constants `3, 4, 3, 1` here; they do not follow from `a ∈ [½, 2]`, see the handoff.) -/
theorem Cnat0_le (hL : 2 ≤ L) (hk : 1 ≤ k) (hadm : IsAdmissibleWeights k (compWeight L a₁))
    {β0 : ℝ} (hβ0 : 0 ≤ β0) (Du : BgData G N) (D : Region G)
    (Zb : Finset (Torus d (N₀ * L ^ (k - k))))
    (hfib : ∀ z ∈ Zb, fib d L N₀ k k z ⊆ D.sites)
    (hZb : ∀ z ∈ Zb, ∀ x ∈ fib d L N₀ k k z, 1 ≤ G.layerIndex x ∧ G.layerIndex x < k)
    (hlay : ∀ x ∈ D.sites, G'.layerIndex x = k)
    (ψk : Torus d (N₀ * L ^ (k - k)) → Fin N → ℂ)
    (hψk : ∀ z ∈ Zb, ∀ i, ψk z i = ((ψ0 ⟨k, z⟩ i : ℝ) : ℂ))
    (ϖ : ℕ → ℝ) (aN : Torus d (N₀ * L ^ (k - k)) → ℝ)
    (haN : ∀ z ∈ Zb, 1 / 2 ≤ aN z) (haN2 : ∀ z ∈ Zb, aN z ≤ 2) {ηk ρ σ n : ℝ}
    (hη : ∀ z ∈ Zb, |aN z / compWeightZ G a₁ z - 1| ≤ ηk) (hηk : ηk ≤ 1 / 2) (hη0 : 0 ≤ ηk)
    (hr : ∀ z ∈ Zb, vn (rBlk G' (compWeight L a₁) ψ0 h z) ≤ ρ)
    (hs : ∀ z ∈ Zb, vn (sBlk G ϖ Du.Ψ z) ≤ σ) (hn : (Zb.card : ℝ) ≤ n) (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) :
    ‖Cnat0 a₁ hprec ψ0 h Du Zb β0 ϖ aN ψk‖ ≤
      n * (36 * betaK d L k β0 * ηk * ρ ^ 2 + 8 * betaK d L k β0 * ρ * σ +
        9 * betaK d L k β0 * σ ^ 2 + N * ηk) := by
  have hak := hadm k hk le_rfl
  have hakpos : 0 < compWeight L a₁ k := by linarith [hak.1]
  have hakne : compWeight L a₁ k ≠ 0 := hakpos.ne'
  have hmem : ∀ z ∈ Zb, 1 / 2 ≤ compWeightZ G a₁ z ∧ compWeightZ G a₁ z ≤ 2 := fun z hz =>
    compWeightZ_mem hadm (hZb z hz)
  have hϱ : ∀ z ∈ Zb, ∀ i, (fun z i => ψk z i - kAvg
      (windowData G G' hprec (compWeight L a₁) ψ0 h).Ψ z i) z i =
      ((compWeight L a₁ k / compWeightZ G a₁ z : ℝ) : ℂ) * rBlk G' (compWeight L a₁) ψ0 h z i := by
    intro z hz i
    have hazne : compWeightZ G a₁ z ≠ 0 := by have := (hmem z hz).1; positivity
    exact varrho_block D hL ⟨hfib z hz, hZb z hz⟩ hakne hazne
      (windowData G G' hprec (compWeight L a₁) ψ0 h)
      (hprec.restrictφ (phiZero G' (compWeight L a₁) ψ0 h)) (phiZero G' (compWeight L a₁) ψ0 h)
      (rBlk G' (compWeight L a₁) ψ0 h z)
      (fun x hx i => by
        have hx' : x ∈ D.sites := hfib z hz hx
        have := window_res_site hprec (compWeight L a₁) ψ0 h (D.sub_Ω hx') (hlay x hx') i
        have hz' : jBlock d L N₀ k k x = z := mem_fib.1 hx
        rw [this, hz'])
      (fun y hy i => svec_window_eq hprec (compWeight L a₁) ψ0 h (D.sub_Ω (hfib z hz hy)) i)
      (ψk z)
      (fun i => by rw [hψk z hz i]; unfold rBlk; ring) i
  have hβk : 0 ≤ betaK d L k β0 := by unfold betaK; positivity
  exact norm_CnatGen0_le_uniform Zb hβk hakpos hak.2 _ _ _ _ _ _
    (fun z hz => (hmem z hz).1) haN haN2 hη hηk hϱ hr hs hn hη0 hρ hσ

/-- **Lemma III.6.3, (III.6.1) on the real domain**: if the four terms of the general bound are each
`≤ ¼` (the consequences of (Λ19) used in the proof), then `|C^♮_0| ≤ 1`. -/
theorem Cnat0_le_one (hL : 2 ≤ L) (hk : 1 ≤ k) (hadm : IsAdmissibleWeights k (compWeight L a₁))
    {β0 : ℝ} (hβ0 : 0 ≤ β0) (Du : BgData G N) (D : Region G)
    (Zb : Finset (Torus d (N₀ * L ^ (k - k))))
    (hfib : ∀ z ∈ Zb, fib d L N₀ k k z ⊆ D.sites)
    (hZb : ∀ z ∈ Zb, ∀ x ∈ fib d L N₀ k k z, 1 ≤ G.layerIndex x ∧ G.layerIndex x < k)
    (hlay : ∀ x ∈ D.sites, G'.layerIndex x = k)
    (ψk : Torus d (N₀ * L ^ (k - k)) → Fin N → ℂ)
    (hψk : ∀ z ∈ Zb, ∀ i, ψk z i = ((ψ0 ⟨k, z⟩ i : ℝ) : ℂ))
    (ϖ : ℕ → ℝ) (aN : Torus d (N₀ * L ^ (k - k)) → ℝ)
    (haN : ∀ z ∈ Zb, 1 / 2 ≤ aN z) (haN2 : ∀ z ∈ Zb, aN z ≤ 2) {ηk ρ σ n : ℝ}
    (hη : ∀ z ∈ Zb, |aN z / compWeightZ G a₁ z - 1| ≤ ηk) (hηk : ηk ≤ 1 / 2) (hη0 : 0 ≤ ηk)
    (hr : ∀ z ∈ Zb, vn (rBlk G' (compWeight L a₁) ψ0 h z) ≤ ρ)
    (hs : ∀ z ∈ Zb, vn (sBlk G ϖ Du.Ψ z) ≤ σ) (hn : (Zb.card : ℝ) ≤ n) (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ)
    (h1 : n * (36 * betaK d L k β0 * ηk * ρ ^ 2) ≤ 1 / 4)
    (h2 : n * (8 * betaK d L k β0 * ρ * σ) ≤ 1 / 4)
    (h3 : n * (9 * betaK d L k β0 * σ ^ 2) ≤ 1 / 4) (h4 : n * (N * ηk) ≤ 1 / 4) :
    ‖Cnat0 a₁ hprec ψ0 h Du Zb β0 ϖ aN ψk‖ ≤ 1 := by
  have := Cnat0_le a₁ hprec ψ0 h hL hk hadm hβ0 Du D Zb hfib hZb hlay ψk hψk ϖ aN haN haN2 hη hηk
    hη0 hr hs hn hρ hσ
  nlinarith

end WindowBound

end Balaban.LargeField.ActionConv
