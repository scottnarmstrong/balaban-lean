/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Counter.Params
public import Balaban.LargeField.R.RRemovedLres
public import Balaban.Inhabited.LevelPairGeneral
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr

/-!
# Arithmetic of the margin of the removed outcome (W910, blocker 4, input (i))

`notes/phase1/LF4R-PLAN.md`, leaf 6.  The history margin `M ⌊R_{k-1}⌋ / L` of `hmargin_removed` beats the
rate `(2/γ_w) log β_k` of `denominatorRestricted_bounds_of_margin_of_weighted` once `λ_{k-1}` is large:

* `lam_one_le`, `lam_succ_le`: `1 ≤ λ_j` and `λ_{j+1} ≤ λ_j + θ₊` from `Setting.Ok.lam_step`;
* `removed_margin_arith`: `(2/γ) log β_k ≤ M ⌊R_{k-1}⌋ / L` when `log β_k ≤ λ_k` and
  `λ_{k-1} ≥ (L (2/γ)(1 + θ₊) + M)/(M R_base)`;
* `rhoSepG_sub_one_ge`: the generating-set separation `ϱ - 1 ≥ 4 d L^{m₁+3}`, so the cap `ϱ - 1` of
  `hmargin_removed` holds as soon as `L^{m₁}` is large against `log β_k`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

section Margin

variable {S : Setting}

theorem lam_mono (ok : S.Ok) : Monotone S.lam :=
  monotone_nat_of_le_succ fun j => by have := (ok.lam_step j).1; linarith [ok.θm_pos]

theorem lam_one_le (ok : S.Ok) (j : ℕ) : 1 ≤ S.lam j :=
  ok.one_le_lam0.trans (lam_mono ok (Nat.zero_le j))

theorem lam_succ_le (ok : S.Ok) (j : ℕ) : S.lam (j + 1) ≤ S.lam j + S.θp := by
  have := (ok.lam_step j).2; linarith

/-- **The margin arithmetic**: `(2/γ) · lb ≤ M ⌊R_{k'}⌋ / L` for `lb ≤ λ_{k'+1}` (for instance
`lb = log β_k`, `k = k' + 1`, `log b_k ≤ λ_k`) and `λ_{k'} ≥ (L (2/γ)(1 + θ₊) + M) / (M R_base)`, with
`⌊R_{k'}⌋ = ⌊R_base λ_{k'}²⌋`. -/
theorem removed_margin_arith (ok : S.Ok) {R : ℕ → ℝ} {k' : ℕ}
    (hR : ⌊R k'⌋₊ = ⌊S.Rb * S.lam k' ^ 2⌋₊) {γ lb : ℝ} (hγ : 0 < γ) (hlb : lb ≤ S.lam (k' + 1))
    (hx : ((S.L : ℝ) * (2 / γ) * (1 + S.θp) + S.M) / (S.M * S.Rb) ≤ S.lam k') :
    2 / γ * lb ≤ (S.M : ℝ) * ⌊R k'⌋₊ / S.L := by
  have hL : (0 : ℝ) < S.L := by have := ok.two_le_L; positivity
  have hM : (0 : ℝ) < S.M := by have := ok.one_le_M; positivity
  have hRb : 0 < S.Rb := by linarith [ok.two_le_Rb]
  have hθ : 0 ≤ S.θp := by linarith [ok.θm_pos, ok.θm_le_θp]
  set x := S.lam k' with hxdef
  have hx1 : 1 ≤ x := lam_one_le ok k'
  set A := 2 / γ with hA
  have hA0 : 0 ≤ A := by positivity
  have hlbx : lb ≤ x + S.θp := hlb.trans (lam_succ_le ok k')
  have hMR : 0 < (S.M : ℝ) * S.Rb := by positivity
  have hx2 : (S.L : ℝ) * A * (1 + S.θp) + S.M ≤ S.M * S.Rb * x := by
    rw [div_le_iff₀ hMR] at hx; linarith
  have hfl : S.Rb * x ^ 2 - 1 ≤ (⌊R k'⌋₊ : ℝ) := by
    rw [hR]; linarith [Nat.lt_floor_add_one (S.Rb * x ^ 2)]
  have h1 : (S.L : ℝ) * A * (x + S.θp) + S.M ≤ S.M * (S.Rb * x ^ 2) := by
    have e1 : x * ((S.L : ℝ) * A * (1 + S.θp) + S.M) ≤ x * (S.M * S.Rb * x) :=
      mul_le_mul_of_nonneg_left hx2 (by linarith)
    have hLA : 0 ≤ (S.L : ℝ) * A := by positivity
    nlinarith [mul_nonneg hLA hθ, mul_nonneg hLA (sub_nonneg.2 hx1), mul_nonneg hθ (sub_nonneg.2 hx1),
      mul_nonneg hLA (mul_nonneg hθ (sub_nonneg.2 hx1)), hM.le, mul_nonneg hM.le (sub_nonneg.2 hx1)]
  rw [le_div_iff₀ hL]
  have e2 : A * lb ≤ A * (x + S.θp) := mul_le_mul_of_nonneg_left hlbx hA0
  have e3 : (S.M : ℝ) * (S.Rb * x ^ 2 - 1) ≤ S.M * (⌊R k'⌋₊ : ℝ) :=
    mul_le_mul_of_nonneg_left hfl hM.le
  nlinarith [mul_le_mul_of_nonneg_right e2 hL.le]

end Margin

end Balaban.LargeField

namespace Balaban.Inhabited.LevelStep

/-- **The separation of the generating set**: `ϱ - 1 ≥ 4 d L³ L^{m₁}` for `ϱ = rhoSepG d L m₁`. -/
theorem rhoSepG_sub_one_ge {d L : ℕ} (m₁ : ℕ) (hd : 3 ≤ d) (hL : 3 ≤ L) :
    4 * (d : ℝ) * (L : ℝ) ^ 3 * (L : ℝ) ^ m₁ ≤ rhoSepG d L m₁ - 1 := by
  have := rhoSepG_tail_nonneg (d := d) hd hL
  have := rhoSepG_terms_nonneg (d := d) (L := L) m₁ hd hL
  have := bgR0_nonneg_G (d := d) (L := L)
  unfold rhoSepG; linarith

end Balaban.Inhabited.LevelStep
