/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepTowerNewLabelsRadius
public import Balaban.Localization.I5Chain
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The room of the composed step data and the collar `r₀` (`StepTowerDecoupleRoom`)

The inherited labels of the class chain are read at the composed step data, which lie in the
class domain of level `j` when `t + K₂ δ₃ + K₂ δ_fl ≤ ε_j` (`d2raw_d1Triple_mem_xiDom`): `t` the
step radius, `δ₃` the closeness bound of the composed backgrounds (`ChainNum.close`), `δ_fl` the
bound of the composed fluctuation (`FlNum.flb`, proportional to the fluctuation radius `δ₁`).
The new level needs `ε_{k+1} ≤ t`.

`δ₃` is bounded below by `N · composedCloseBound(…, C_{Ξ1} t, r₀)`, which carries the factor
`exp(-γ_w (r₀ - 4 d L³) L^{m₁} / L)` (FLUCTUATION §1.4: the collar `r₀ = 4dL³ + L` of LFR §I.1.3
row 5a gives `e^{-γ_w M₁}`).  At `r₀ = 4 d L³ = 324` (`d = L = 3`) the factor is `1`:

* `composedCloseBound_324_ge`: `composedCloseBound(…, δ, 324) ≥ 855000 B_G δ`;
* `cover_room_r324_bound`, `not_cover_and_room_r324`: with `ChainNum … 324 t δ₃`, for every
  fluctuation radius (any `δ_fl ≥ 0`), the cover `ε_{k+1} ≤ t` and the room
  `t + K₂ δ₃ + K₂ δ_fl ≤ ε_k` force `33060000 B_G < 1`; they exclude each other when `B_G ≥ 1`.

So decoupling the fluctuation radius from the step radius does not give the room at the collar
of the landed chain (`r₀ ≤ 324` in `e0CoeffFamily_class_fromTower_of_irrelBounds_X_onSet`,
`4 d L³ ≤ r₀` in `BgSetting`).  For a larger collar:

* `composedCloseBound_collar`, `composedCloseBound_antitone_collar`: the factor of a larger collar;
* `ChainNum.of_collar`: `ChainNum` at the collar `r₀` gives `ChainNum` at every `r₀' ≥ r₀` with
  `δ₃' = N · composedCloseBound(…, C_{Ξ1} ε', r₀') ≤ δ₃`;
* `exists_pow_close_le`: at `r₀ = 327` the ratio `K₂ N composedCloseBound(…, C_{Ξ1}, 327)` is below
  any `θ > 0` once `3^{m₁}` is large (FLUCTUATION §1.5 row 6; the general-`L` form of the decay is
  `c3_le_of_decay`, the linearity in the radius `Balaban.Fluctuation.composedCloseBound_smul`);
* `eps_succ_le_of_eps_one_le`: the cover `ε_{k+1} ≤ t` at every scale from `ε_1 ≤ t`;
* `room_of_radii`: the room at every `j ≤ k` from `t ≤ ε_{k+1}` (with the cover: `t = ε_{k+1}`),
  `ε_{k+1} ≤ q ε_k`, `δ₃ ≤ Q t`, `δ_fl ≤ F δ₁`, `δ₁ ≤ η ε_k` and `q (1 + K₂ Q) + K₂ F η ≤ 1`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Localization Balaban.SmallField Balaban.SmallField.Def6 Balaban.Background

section Collar

variable {d L N m₁ : ℕ} [NeZero L]

/-- **The factor of a larger collar**: `composedCloseBound` at `r₀'` is the bound at `r₀` times
`exp(-γ_w (r₀' - r₀) L^{m₁} / L)`. -/
theorem composedCloseBound_collar (BG κ δ r₀ r₀' : ℝ) :
    composedCloseBound d L N m₁ BG κ δ r₀' = composedCloseBound d L N m₁ BG κ δ r₀ *
      Real.exp (-(gammaW d * ((r₀' - r₀) * (L : ℝ) ^ m₁ / L))) := by
  unfold composedCloseBound
  rw [mul_assoc (_ * _ * _) (Real.exp _) (Real.exp _), ← Real.exp_add]
  congr 2
  ring

/-- **The closeness bound decreases with the collar.** -/
theorem composedCloseBound_antitone_collar {BG κ δ r₀ r₀' : ℝ} (hBG : 0 ≤ BG) (hδ : 0 ≤ δ)
    (hd : 0 < d) (hr : r₀ ≤ r₀') :
    composedCloseBound d L N m₁ BG κ δ r₀' ≤ composedCloseBound d L N m₁ BG κ δ r₀ := by
  rw [composedCloseBound_collar BG κ δ r₀ r₀']
  have h0 := composedCloseBound_nonneg (d := d) (L := L) (N := N) (m₁ := m₁) (κ := κ) (r₀ := r₀)
    hBG hδ hd
  have hγ := gammaW_nonneg hd
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hx : 0 ≤ (r₀' - r₀) * (L : ℝ) ^ m₁ / L :=
    div_nonneg (mul_nonneg (by linarith) (by positivity)) hL.le
  have he : Real.exp (-(gammaW d * ((r₀' - r₀) * (L : ℝ) ^ m₁ / L))) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    nlinarith [mul_nonneg hγ hx]
  calc _ ≤ composedCloseBound d L N m₁ BG κ δ r₀ * 1 := mul_le_mul_of_nonneg_left he h0
    _ = _ := mul_one _

/-- **`ChainNum` at a larger collar**, with the closeness bound of that collar as `δ₃`. -/
theorem _root_.Balaban.Localization.ChainNum.of_collar {BG κ r₀ r₀' eps δ₃ : ℝ}
    (h : ChainNum d L N m₁ BG κ r₀ eps δ₃) (hr : r₀ ≤ r₀') (hBG : 0 ≤ BG) (hd : 0 < d) :
    ChainNum d L N m₁ BG κ r₀' eps (N * composedCloseBound d L N m₁ BG κ (xiC1 d * eps) r₀') := by
  have hX1 : 0 ≤ xiC1 d := le_trans zero_le_one (one_le_xiC1 d)
  have hX : 0 ≤ xiC1 d * eps := mul_nonneg hX1 h.eps_pos.le
  have h0 : 0 ≤ (N : ℝ) * composedCloseBound d L N m₁ BG κ (xiC1 d * eps) r₀' :=
    mul_nonneg (Nat.cast_nonneg N) (composedCloseBound_nonneg hBG hX hd)
  have hle : (N : ℝ) * composedCloseBound d L N m₁ BG κ (xiC1 d * eps) r₀' ≤ δ₃ :=
    (mul_le_mul_of_nonneg_left (composedCloseBound_antitone_collar hBG hX hd hr)
      (Nat.cast_nonneg N)).trans h.close
  set δ₃' := (N : ℝ) * composedCloseBound d L N m₁ BG κ (xiC1 d * eps) r₀' with hδ₃'
  have hc2 : 0 ≤ cK2 d L N := (cK2_pos d L N).le
  have hx2 : 0 ≤ xiK2 d L N := by
    have := cK2_pos d L N
    unfold xiK2; positivity
  have hp : (0 : ℝ) ≤ (4 * d + 6) * (2 * d + 1) := by positivity
  have h2 : xiK2 d L N * δ₃' ≤ xiK2 d L N * δ₃ := mul_le_mul_of_nonneg_left hle hx2
  have h3 : (4 * d + 6) * (2 * d + 1) * (xiK2 d L N * δ₃') ≤
      (4 * d + 6) * (2 * d + 1) * (xiK2 d L N * δ₃) := mul_le_mul_of_nonneg_left h2 hp
  have h4 : xiC1 d * (xiK2 d L N * δ₃') ≤ xiC1 d * (xiK2 d L N * δ₃) :=
    mul_le_mul_of_nonneg_left h2 hX1
  exact {
    eps_pos := h.eps_pos
    small1 := h.small1
    th1 := h.th1
    c7le := h.c7le
    small₁ := h.small₁
    δ₃_nn := h0
    δ₃_le_one := hle.trans h.δ₃_le_one
    c1 := by linarith [h.c1]
    star := hle.trans h.star
    K1s := h.K1s
    sm := by nlinarith [h.sm, mul_le_mul_of_nonneg_left hle hc2]
    small₂ := by nlinarith [h.small₂]
    th2 := by nlinarith [h.th2]
    close := le_rfl }

end Collar

section Three

variable {N m₁ : ℕ}

/-- **No decay at the collar `r₀ = 4 d L³`** (`d = L = 3`): `composedCloseBound(…, δ, 324)` is at
least `10 · 3 · c_F · lemma53 · B_G δ ≥ 855000 B_G δ`. -/
theorem composedCloseBound_324_ge {BG κ δ : ℝ} (hBG : 0 ≤ BG) (hκ : 0 ≤ κ) (hδ : 0 ≤ δ) :
    855000 * BG * δ ≤ composedCloseBound 3 3 N m₁ BG κ δ 324 := by
  have hγ : 0 ≤ gammaW 3 := gammaW_nonneg (by norm_num)
  have hfam : 0 ≤ famConst 3 3 BG κ := by
    have := famConst_ge_one (d := 3) (L := 3) hBG κ (by norm_num)
    linarith
  have hc' : 0 ≤ cK2' 3 3 N (famConst 3 3 BG κ) := cK2'_nonneg hfam
  have hl : 500 ≤ lemma53Const 3 3 := by
    have := cB7_le_const 3 3
    have := cB7_pos 3 3
    linarith
  have e1 : 1 ≤ Real.exp (gammaW 3 * (2 * ((3 : ℕ) : ℝ))) := Real.one_le_exp (by positivity)
  have e2 : 1 ≤ Real.exp (gammaW 3) := Real.one_le_exp hγ
  have e3 : 1 ≤ Real.exp ((N0 3 3 : ℝ) * κ) := Real.one_le_exp (by positivity)
  have e4 : Real.exp (-(gammaW 3 * ((324 - 4 * ((3 : ℕ) : ℝ) * ((3 : ℕ) : ℝ) ^ 3) *
      ((3 : ℕ) : ℝ) ^ m₁ / ((3 : ℕ) : ℝ)))) = 1 := by
    norm_num
  have hcF : cF 3 3 = 57 := by unfold cF; norm_num
  unfold composedCloseBound closeConst
  rw [e4, hcF]
  have hB : 0 ≤ BG * Real.exp ((N0 3 3 : ℝ) * κ) := by positivity
  have hld : 500 * δ ≤ lemma53Const 3 3 * δ := mul_le_mul_of_nonneg_right hl hδ
  have h1 : 57 * (500 * δ) ≤ (57 + 3 / 2 * cK2' 3 3 N (famConst 3 3 BG κ)) *
      (lemma53Const 3 3 * δ) := by nlinarith
  have h2 : BG * (57 * (500 * δ)) ≤ BG * Real.exp ((N0 3 3 : ℝ) * κ) *
      ((57 + 3 / 2 * cK2' 3 3 N (famConst 3 3 BG κ)) * (lemma53Const 3 3 * δ)) := by
    have h57 : 0 ≤ 57 * (500 * δ) := by positivity
    calc BG * (57 * (500 * δ)) ≤ BG * Real.exp ((N0 3 3 : ℝ) * κ) * (57 * (500 * δ)) := by
          nlinarith [mul_nonneg hBG h57]
      _ ≤ _ := mul_le_mul_of_nonneg_left h1 hB
  have h3 : 0 ≤ BG * (57 * (500 * δ)) := by positivity
  have h4 : 3 * (BG * (57 * (500 * δ))) ≤ ((3 : ℕ) : ℝ) * Real.exp (gammaW 3) *
      (BG * Real.exp ((N0 3 3 : ℝ) * κ) *
        ((57 + 3 / 2 * cK2' 3 3 N (famConst 3 3 BG κ)) * (lemma53Const 3 3 * δ))) := by
    push_cast
    nlinarith
  have h5 : 0 ≤ 3 * (BG * (57 * (500 * δ))) := by positivity
  have h6 := mul_le_mul_of_nonneg_right e1 (h5.trans h4)
  linarith

/-- **`ε_k < 4 ε_{k+1}` and `0 < ε_{k+1}`** for the class sequence at `d = L = 3`, `α₀ > 0`,
`γ ≥ 0`. -/
theorem eps_lt_four_succ {P : Consts} (hα₀ : 0 < P.α₀) (hγ : 0 ≤ P.γ) (k : ℕ) :
    0 < P.eps 3 3 (k + 1) ∧ P.eps 3 3 k < 4 * P.eps 3 3 (k + 1) := by
  have hpos : 0 < P.eps 3 3 (k + 1) := by
    have := epsTail_pos (k + 1)
    unfold Consts.eps epsSeq
    positivity
  have hgap := GsSpec.epsSeq_le_two_rpow_mul_succ 3 (P.alpha 3) P.α₀ hα₀.le k
  have hα : P.alpha 3 ≤ 1 / 2 := by
    unfold Consts.alpha; push_cast; linarith
  have h3 : ((3 : ℕ) : ℝ) ^ P.alpha 3 < 2 := by
    push_cast; exact three_rpow_lt_two hα
  refine ⟨hpos, (show P.eps 3 3 k ≤ 2 * ((3 : ℕ) : ℝ) ^ P.alpha 3 * P.eps 3 3 (k + 1) from
    hgap).trans_lt ?_⟩
  nlinarith

/-- **The cover at a fixed step radius**: `ε_1 ≤ t` gives `ε_{k+1} ≤ t` for every `k` (`α ≥ 0`);
this is the radius premise `P.eps 3 3 (k + 1) ≤ eps` of `newLabels_castInputs` at `eps = t`. -/
theorem eps_succ_le_of_eps_one_le {P : Consts} (hα₀ : 0 ≤ P.α₀) (hα : 0 ≤ P.alpha 3) {t : ℝ}
    (h1 : P.eps 3 3 1 ≤ t) (k : ℕ) : P.eps 3 3 (k + 1) ≤ t := by
  induction k with
  | zero => simpa using h1
  | succ k ih =>
    have hg := epsSeq_gapE 3 (P.alpha 3) P.α₀ hα₀ (k + 1)
    have hq : ((3 : ℕ) : ℝ) ^ (-P.alpha 3) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
    have e : (1 - (1 - ((3 : ℕ) : ℝ) ^ (-P.alpha 3))) = ((3 : ℕ) : ℝ) ^ (-P.alpha 3) := by ring
    rw [e] at hg
    have h0 : 0 ≤ P.eps 3 3 (k + 1) := by
      have := epsTail_pos (k + 1)
      unfold Consts.eps epsSeq
      positivity
    unfold Consts.eps at ih h0 ⊢
    nlinarith

/-- **Cover and room at the collar `324` bound `B_G`** (`d = L = 3`, `N = 2`, any fluctuation
radius): `ε_{k+1} ≤ t` and `t + K₂ δ₃ + K₂ δ_fl ≤ ε_k`, with `ChainNum … 324 t δ₃` and
`δ_fl ≥ 0`, give `33060000 B_G < 1`. -/
theorem cover_room_r324_bound {P : Consts} (hα₀ : 0 < P.α₀) (hγ : 0 ≤ P.γ)
    {BG κ t δ₃ δfl : ℝ} (hC : ChainNum 3 3 2 m₁ BG κ 324 t δ₃) (hBG : 0 ≤ BG) (hκ : 0 ≤ κ)
    (hfl : 0 ≤ δfl) (k : ℕ) (hcov : P.eps 3 3 (k + 1) ≤ t)
    (hroom : t + xiK2 3 3 2 * δ₃ + xiK2 3 3 2 * δfl ≤ P.eps 3 3 k) :
    33060000 * BG < 1 := by
  obtain ⟨hpos, hlt⟩ := eps_lt_four_succ hα₀ hγ k
  have ht : 0 < t := hC.eps_pos
  have hX : 1 ≤ xiC1 3 := one_le_xiC1 3
  have hK : 58 ≤ xiK2 3 3 2 := by
    have := cK2_pos 3 3 2
    unfold xiK2
    push_cast
    nlinarith
  have hcl := hC.close
  have hge := composedCloseBound_324_ge (N := 2) (m₁ := m₁) hBG hκ
    (mul_nonneg (le_trans zero_le_one hX) ht.le)
  have hxt : 855000 * BG * t ≤ 855000 * BG * (xiC1 3 * t) := by
    have : t ≤ xiC1 3 * t := by nlinarith
    exact mul_le_mul_of_nonneg_left this (by positivity)
  have hδ₃ : 1710000 * BG * t ≤ δ₃ := by
    push_cast at hcl
    linarith
  have hfl' : 0 ≤ xiK2 3 3 2 * δfl := mul_nonneg (by linarith) hfl
  have hK3 : 58 * (1710000 * BG * t) ≤ xiK2 3 3 2 * δ₃ :=
    mul_le_mul hK hδ₃ (by positivity) (by linarith)
  nlinarith

/-- **Cover and room exclude each other at the collar `324`** (`d = L = 3`, `N = 2`, `B_G ≥ 1`,
any fluctuation radius). -/
theorem not_cover_and_room_r324 {P : Consts} (hα₀ : 0 < P.α₀) (hγ : 0 ≤ P.γ)
    {BG κ t δ₃ δfl : ℝ} (hC : ChainNum 3 3 2 m₁ BG κ 324 t δ₃) (hBG : 1 ≤ BG) (hκ : 0 ≤ κ)
    (hfl : 0 ≤ δfl) (k : ℕ) :
    ¬ (P.eps 3 3 (k + 1) ≤ t ∧ t + xiK2 3 3 2 * δ₃ + xiK2 3 3 2 * δfl ≤ P.eps 3 3 k) := by
  rintro ⟨hcov, hroom⟩
  have := cover_room_r324_bound hα₀ hγ hC (by linarith) hκ hfl k hcov hroom
  linarith

/-- **The ratio of the closeness bound at the collar `327 = 4dL³ + L` is small for a large
block** (FLUCTUATION §1.5 row 6): for every `θ > 0` there is `M` such that
`K₂ · 2 · composedCloseBound(…, C_{Ξ1}, 327) ≤ θ` whenever `3^{m₁} ≥ M`. -/
theorem exists_pow_close_le {BG κ θ : ℝ} (hBG : 0 ≤ BG) (hθ : 0 < θ) :
    ∃ M : ℝ, ∀ m₁ : ℕ, M ≤ (3 : ℝ) ^ m₁ →
      xiK2 3 3 2 * (2 * composedCloseBound 3 3 2 m₁ BG κ (xiC1 3) 327) ≤ θ := by
  have hγ : 0 < gammaW 3 := gammaW_pos' (by norm_num)
  have hX : 0 ≤ xiC1 3 := le_trans zero_le_one (one_le_xiC1 3)
  have hx2 : 0 ≤ xiK2 3 3 2 := by
    have := cK2_pos 3 3 2
    unfold xiK2; positivity
  set A : ℝ := xiK2 3 3 2 * (2 * composedCloseBound 3 3 2 0 BG κ (xiC1 3) 324) with hA
  have hA0 : 0 ≤ A :=
    mul_nonneg hx2 (mul_nonneg (by norm_num) (composedCloseBound_nonneg hBG hX (by norm_num)))
  have hind : ∀ m₁ : ℕ, composedCloseBound 3 3 2 m₁ BG κ (xiC1 3) 324 =
      composedCloseBound 3 3 2 0 BG κ (xiC1 3) 324 := by
    intro m₁
    unfold composedCloseBound
    norm_num
  refine ⟨(Real.log (A / θ + 1)) / gammaW 3, fun m₁ hM => ?_⟩
  rw [composedCloseBound_collar BG κ (xiC1 3) 324 327, hind m₁]
  have hL : ((3 : ℕ) : ℝ) ^ m₁ = (3 : ℝ) ^ m₁ := by push_cast; ring
  have e : -(gammaW 3 * ((327 - 324) * ((3 : ℕ) : ℝ) ^ m₁ / ((3 : ℕ) : ℝ))) =
      -(gammaW 3 * (3 : ℝ) ^ m₁) := by
    rw [hL]; push_cast; ring
  rw [e]
  have hlog : Real.log (A / θ + 1) ≤ gammaW 3 * (3 : ℝ) ^ m₁ := by
    rw [div_le_iff₀ hγ] at hM
    linarith
  have hpos : 0 < A / θ + 1 := by positivity
  have hexp : A / θ + 1 ≤ Real.exp (gammaW 3 * (3 : ℝ) ^ m₁) := by
    calc A / θ + 1 = Real.exp (Real.log (A / θ + 1)) := (Real.exp_log hpos).symm
      _ ≤ _ := Real.exp_le_exp.2 hlog
  have hE : 0 < Real.exp (gammaW 3 * (3 : ℝ) ^ m₁) := Real.exp_pos _
  rw [Real.exp_neg]
  have hAθ : A ≤ θ * Real.exp (gammaW 3 * (3 : ℝ) ^ m₁) := by
    have h1 : A / θ ≤ Real.exp (gammaW 3 * (3 : ℝ) ^ m₁) := by linarith
    rwa [div_le_iff₀ hθ, mul_comm] at h1
  calc xiK2 3 3 2 * (2 * (composedCloseBound 3 3 2 0 BG κ (xiC1 3) 324 *
        (Real.exp (gammaW 3 * (3 : ℝ) ^ m₁))⁻¹))
        = A * (Real.exp (gammaW 3 * (3 : ℝ) ^ m₁))⁻¹ := by rw [hA]; ring
    _ ≤ θ * Real.exp (gammaW 3 * (3 : ℝ) ^ m₁) * (Real.exp (gammaW 3 * (3 : ℝ) ^ m₁))⁻¹ :=
        mul_le_mul_of_nonneg_right hAθ (inv_nonneg.2 hE.le)
    _ = θ := by field_simp

end Three

/-- **The room at every inherited level from separate radii** (arithmetic).  If `ε` is antitone,
`ε_{k+1} ≤ q ε_k`, `t ≤ ε_{k+1}` (with the cover `ε_{k+1} ≤ t` this is `t = ε_{k+1}`),
`δ₃ ≤ Q t`, `δ_fl ≤ F δ₁`, `δ₁ ≤ η ε_k` and `q (1 + K Q) + K F η ≤ 1`, then
`t + K δ₃ + K δ_fl ≤ ε_j` for every `j ≤ k`. -/
theorem room_of_radii {ε : ℕ → ℝ} (hε : Antitone ε) {k : ℕ} {q Q F η K t δ₃ δ₁ δfl : ℝ}
    (hK : 0 ≤ K) (hQ : 0 ≤ Q) (hF : 0 ≤ F) (hεk : 0 ≤ ε k) (hq : ε (k + 1) ≤ q * ε k)
    (ht : t ≤ ε (k + 1)) (hδ₃ : δ₃ ≤ Q * t) (hfl : δfl ≤ F * δ₁)
    (hδ₁ : δ₁ ≤ η * ε k) (hsum : q * (1 + K * Q) + K * F * η ≤ 1) :
    ∀ j ≤ k, t + K * δ₃ + K * δfl ≤ ε j := by
  intro j hj
  have h1 : t * (1 + K * Q) ≤ q * ε k * (1 + K * Q) :=
    mul_le_mul_of_nonneg_right (ht.trans hq) (by positivity)
  have h2 : K * δ₃ ≤ K * (Q * t) := mul_le_mul_of_nonneg_left hδ₃ hK
  have h3 : K * δfl ≤ K * (F * (η * ε k)) :=
    mul_le_mul_of_nonneg_left (hfl.trans (mul_le_mul_of_nonneg_left hδ₁ hF)) hK
  have h4 : (q * (1 + K * Q) + K * F * η) * ε k ≤ 1 * ε k :=
    mul_le_mul_of_nonneg_right hsum hεk
  have h5 := hε hj
  nlinarith

end Balaban.Inhabited
