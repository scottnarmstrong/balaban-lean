/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepTowerCollarTower
public import Balaban.Inhabited.StepTowerScaleTNum
public import Balaban.Inhabited.StepTowerCollarBase
public import Balaban.Fluctuation.ClassOldBirthDelta
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# Towers at every scale with cover and room at the collar `327` (`StepTowerCollarScales`)

The radii of the source (P4 (H.1), (4.9), (4.19); P5 (1.37), (2.42); FLUCTUATION §1.4, §1.5): at
scale `k` the step radius is `t_k = ε_{k+1}` (the new level is analytic on
`Ξ_{k+1}(1, ε_{k+1})`), the closeness bound of the composed backgrounds at the collar
`r₀ = 4 d L³ + L = 327` is `δ₃ = Q t_k` with `Q = N · composedCloseBound(…, C_{Ξ1}, 327)` (linear in
the radius), the fluctuation radius is `δ₁ = min(t_k, η ε_k)` and the bound of the composed
fluctuation is `δ_fl = F δ₁`, `F = N (5 K₂' + 1)`.  The block `m₁` is chosen once, independently
of `k`, so that `K₂ Q ≤ (1 - q) / (2 q)` (`exists_stepTower_collar`), and `η = (1 - q) / (4 K₂ F)`.

`exists_stepTower_collar_scales`: for every sequence `ε` with `ε_{j+1} ≤ q ε_j` (`0 < q < 1`) and
`ε_1 ≤ T₀.t`, and every scale `k`, the tower `T_k` of step radius `t_k = ε_{k+1}`
(`exists_stepTower_shrink`) carries `ChainNum` at the collar `327` with `δ₃ = Q t_k`
(`ChainNum.scale`, `ChainNum.of_collar`), `FlNum` with `δ₁ = min(t_k, η ε_k)`, `δ_fl = F δ₁`
(`FlNum.scale`, `FlNum.mono_δ₃`, `FlNum.at_fluct`), and the room
`t_k + K₂ δ₃ + K₂ δ_fl ≤ ε_j` for every `j ≤ k` (`room_of_radii`:
`q (1 + K₂ Q) + K₂ F η ≤ q + (1 - q) / 2 + (1 - q) / 4 ≤ 1`); the cover `ε_{k+1} ≤ t_k` holds
with equality.  `classEps_antitone`, `classEps_gap`, `classEps_lower` give the hypotheses on `ε`
for the class sequence `ε_j = P.eps 3 3 j` with `q = 3^{-α}`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.I5Inhabited Balaban.SmallField.Def6

/-- **Towers at every scale with cover and room at the collar `(4 * (d : ℝ) * (L : ℝ) ^ 3 + L)`.**  See the module
doc-string.  `T₀` carries the label rate at `m₀`; for every `ε` with `ε_{j+1} ≤ q ε_j`, `ε > 0`,
`ε` antitone and `ε_1 ≤ T₀.t`, and every `k`, the tower `T_k` has the constants of `T₀` except the
step radius `T_k.t = ε_{k+1}`, `ChainNum` at `(4 * (d : ℝ) * (L : ℝ) ^ 3 + L)` with `δ₃ = Q T_k.t`, `FlNum` with
`δ₁ = min(T_k.t, η ε_k)` and `δ_fl = F δ₁`, and the room at every `j ≤ k`. -/
theorem StepTowerG.exists_collar_scales (d L N : ℕ) [NeZero L] (hd : 3 ≤ d) (hL : 3 ≤ L) (hN : 2 ≤ N)
    (m₀ : ℕ) (κlo : ℝ) {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    ∃ (κmin : ℝ) (_ : κlo ≤ κmin) (T₀ : StepTowerG d L N κmin) (κdec Q F η : ℝ),
      T₀.m₀ = 1 ∧ T₀.κ0 = aEnt d L + 2 ∧
      4 * (d : ℝ) * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ T₀.κ ∧
      (2 * T₀.κdec - 1) * ((L : ℝ) ^ (m₀ - 1) + 2 * (d : ℝ) *
        (L : ℝ) ^ m₀ * ((((L ^ (m₀ - 1)) ^ d : ℕ)) : ℝ) * c1 d L) + 1 ≤ 2 * κdec ∧
      Q = (N : ℝ) * composedCloseBound d L N T₀.m₁ T₀.BG T₀.κ (xiC1 d) (4 * (d : ℝ) * (L : ℝ) ^ 3 + L) ∧
      xiK2 d L N * Q ≤ (1 - q) / (2 * q) ∧
      F = (N : ℝ) * (5 * cK2' d L N (famConst d L T₀.BG₂ T₀.κ) + 1) ∧
      η = (1 - q) / (4 * xiK2 d L N * F) ∧ 0 ≤ Q ∧ 0 < F ∧ 0 < η ∧
      ∀ ε : ℕ → ℝ, Antitone ε → (∀ j, 0 < ε j) → (∀ j, ε (j + 1) ≤ q * ε j) → ε 1 ≤ T₀.t →
      ∀ k : ℕ, ∃ Tk : StepTowerG d L N κmin, Tk.t = ε (k + 1) ∧ Tk.m₁ = T₀.m₁ ∧ Tk.c = T₀.c ∧
        Tk.BG = T₀.BG ∧ Tk.κ = T₀.κ ∧ Tk.c₂ = T₀.c₂ ∧ Tk.BG₂ = T₀.BG₂ ∧ Tk.δc = T₀.δc ∧
        Tk.δ = T₀.δ ∧ Tk.δ' = T₀.δ' ∧ Tk.κ0 = T₀.κ0 ∧ Tk.m₀ = T₀.m₀ ∧
        ChainNum d L N Tk.m₁ Tk.BG Tk.κ (4 * (d : ℝ) * (L : ℝ) ^ 3 + L) Tk.t (Q * Tk.t) ∧
        FlNum d L N Tk.BG Tk.BG₂ Tk.κ Tk.t (Q * Tk.t) (min Tk.t (η * ε k))
          (F * min Tk.t (η * ε k)) ∧
        ∀ j ≤ k, Tk.t + xiK2 d L N * (Q * Tk.t) + xiK2 d L N * (F * min Tk.t (η * ε k)) ≤
          ε j := by
  have hθ : 0 < (1 - q) / (2 * q) := div_pos (by linarith) (by positivity)
  obtain ⟨κmin, hlo, T₀, δ₃, δfl, κdec, hm0, hk0, hC0, hF0, hκ, hr, hQθ⟩ :=
    StepTowerG.exists_collar d L N hd hL hN m₀ κlo hθ
  obtain ⟨hC⟩ := T₀.core
  have hBG : 0 ≤ T₀.BG := hC.hS.fam.2.1
  have hBG₂ : 0 ≤ T₀.BG₂ := hC.hS2.fam.2.1
  have hK : 0 < xiK2 d L N := by
    have := cK2_pos d L N
    unfold xiK2; positivity
  have hX : 0 ≤ xiC1 d := le_trans zero_le_one (one_le_xiC1 d)
  set Q : ℝ := (N : ℝ) * composedCloseBound d L N T₀.m₁ T₀.BG T₀.κ (xiC1 d) (4 * (d : ℝ) * (L : ℝ) ^ 3 + L) with hQdef
  have hQ : 0 ≤ Q := mul_nonneg (Nat.cast_nonneg N) (composedCloseBound_nonneg hBG hX (by omega))
  have hc' : 0 ≤ cK2' d L N (famConst d L T₀.BG₂ T₀.κ) := cK2'_nonneg T₀.fam_nonneg
  set F : ℝ := (N : ℝ) * (5 * cK2' d L N (famConst d L T₀.BG₂ T₀.κ) + 1) with hFdef
  have hF : 0 < F := by positivity
  set η : ℝ := (1 - q) / (4 * xiK2 d L N * F) with hηdef
  have hη : 0 < η := div_pos (by linarith) (by positivity)
  have hKFη : xiK2 d L N * F * η = (1 - q) / 4 := by
    rw [hηdef]; field_simp
  have hqKQ : q * (xiK2 d L N * Q) ≤ (1 - q) / 2 := by
    have h := mul_le_mul_of_nonneg_left hQθ hq0.le
    have e : q * ((1 - q) / (2 * q)) = (1 - q) / 2 := by field_simp
    linarith
  have hsum : q * (1 + xiK2 d L N * Q) + xiK2 d L N * F * η ≤ 1 := by
    rw [hKFη]; nlinarith
  refine ⟨κmin, hlo, T₀, κdec, Q, F, η, hm0, hk0, hκ, hr, rfl, hQθ, rfl, rfl, hQ, hF, hη,
    fun ε hε hpos hgap h1 k => ?_⟩
  have ht0 := T₀.t_pos
  have htk : ε (k + 1) ≤ T₀.t := (hε (by omega : 1 ≤ k + 1)).trans h1
  set l : ℝ := ε (k + 1) / T₀.t with hldef
  have hl0 : 0 < l := div_pos (hpos _) ht0
  have hl1 : l ≤ 1 := (div_le_one ht0).2 htk
  have hlt : l * T₀.t = ε (k + 1) := div_mul_cancel₀ _ ht0.ne'
  obtain ⟨Tk, hTt, hTm, hTc, hTB, hTκ, hTc₂, hTB₂, hTδc, hTδ, hTδ', hTk0, hTm0⟩ :=
    T₀.exists_shrink (hpos (k + 1)) htk
  -- the closeness bound at the collar `(4 * (d : ℝ) * (L : ℝ) ^ 3 + L)`, linear in the radius
  have hCs := hC0.scale hl0 hl1
  rw [hlt] at hCs
  have hCk := hCs.of_collar le_rfl hBG (by have := hd; omega)
  have hδeq : (N : ℝ) * composedCloseBound d L N T₀.m₁ T₀.BG T₀.κ (xiC1 d * ε (k + 1)) (4 * (d : ℝ) * (L : ℝ) ^ 3 + L) =
      Q * ε (k + 1) := by
    rw [hQdef, composedCloseBound_smul d L N T₀.m₁ T₀.BG T₀.κ (xiC1 d * ε (k + 1)),
      composedCloseBound_smul d L N T₀.m₁ T₀.BG T₀.κ (xiC1 d)]
    ring
  have hδ₃le : Q * ε (k + 1) ≤ l * δ₃ := by rw [← hδeq]; exact hCs.close
  -- the fluctuation radius `δ₁ = min(t_k, η ε_k)` and `δ_fl = F δ₁`
  have hFs := hF0.scale hl0 hl1 ht0 hC0.δ₃_nn (by omega) hBG hBG₂
  rw [hlt] at hFs
  have hδ₁0 : 0 < min (ε (k + 1)) (η * ε k) := lt_min (hpos _) (mul_pos hη (hpos k))
  have hFk := (hFs.mono_δ₃ hδ₃le).at_fluct T₀.fam_nonneg hδ₁0 (min_le_left _ _)
  have hfleq : (N : ℝ) * (5 * (cK2' d L N (famConst d L T₀.BG₂ T₀.κ) *
      min (ε (k + 1)) (η * ε k)) + min (ε (k + 1)) (η * ε k)) =
      F * min (ε (k + 1)) (η * ε k) := by
    rw [hFdef]; ring
  rw [hfleq] at hFk
  have hroom := room_of_radii (t := ε (k + 1)) (δ₃ := Q * ε (k + 1))
    (δ₁ := min (ε (k + 1)) (η * ε k)) (δfl := F * min (ε (k + 1)) (η * ε k)) hε hK.le hQ hF.le
    (hpos k).le (hgap k) le_rfl le_rfl le_rfl (min_le_right _ _) hsum
  refine ⟨Tk, hTt, hTm, hTc, hTB, hTκ, hTc₂, hTB₂, hTδc, hTδ, hTδ', hTk0, hTm0, ?_, ?_, ?_⟩
  · rw [hTm, hTB, hTκ, hTt, ← hδeq]; exact hCk
  · rw [hTB, hTB₂, hTκ, hTt]; exact hFk
  · rw [hTt]; exact hroom

/-- **Towers at every scale with cover and room at the collar `327`.**  See the module
doc-string.  `T₀` carries the label rate at `m₀`; for every `ε` with `ε_{j+1} ≤ q ε_j`, `ε > 0`,
`ε` antitone and `ε_1 ≤ T₀.t`, and every `k`, the tower `T_k` has the constants of `T₀` except the
step radius `T_k.t = ε_{k+1}`, `ChainNum` at `327` with `δ₃ = Q T_k.t`, `FlNum` with
`δ₁ = min(T_k.t, η ε_k)` and `δ_fl = F δ₁`, and the room at every `j ≤ k`. -/
theorem exists_stepTower_collar_scales (m₀ : ℕ) (κlo : ℝ) {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    ∃ (κmin : ℝ) (_ : κlo ≤ κmin) (T₀ : StepTower κmin) (κdec Q F η : ℝ),
      4 * 3 * (((2 * 3 + 1) ^ 3 : ℕ) : ℝ) * κdec ≤ T₀.κ ∧
      (2 * T₀.κdec - 1) * (((3 : ℕ) : ℝ) ^ (m₀ - 1) + 2 * ((3 : ℕ) : ℝ) *
        ((3 : ℕ) : ℝ) ^ m₀ * ((((3 ^ (m₀ - 1)) ^ 3 : ℕ)) : ℝ) * c1 3 3) + 1 ≤ 2 * κdec ∧
      Q = 2 * composedCloseBound 3 3 2 T₀.m₁ T₀.BG T₀.κ (xiC1 3) 327 ∧
      xiK2 3 3 2 * Q ≤ (1 - q) / (2 * q) ∧
      F = 2 * (5 * cK2' 3 3 2 (famConst 3 3 T₀.BG₂ T₀.κ) + 1) ∧
      η = (1 - q) / (4 * xiK2 3 3 2 * F) ∧ 0 ≤ Q ∧ 0 < F ∧ 0 < η ∧
      ∀ ε : ℕ → ℝ, Antitone ε → (∀ j, 0 < ε j) → (∀ j, ε (j + 1) ≤ q * ε j) → ε 1 ≤ T₀.t →
      ∀ k : ℕ, ∃ Tk : StepTower κmin, Tk.t = ε (k + 1) ∧ Tk.m₁ = T₀.m₁ ∧ Tk.c = T₀.c ∧
        Tk.BG = T₀.BG ∧ Tk.κ = T₀.κ ∧ Tk.c₂ = T₀.c₂ ∧ Tk.BG₂ = T₀.BG₂ ∧ Tk.δc = T₀.δc ∧
        Tk.δ = T₀.δ ∧ Tk.δ' = T₀.δ' ∧
        ChainNum 3 3 2 Tk.m₁ Tk.BG Tk.κ 327 Tk.t (Q * Tk.t) ∧
        FlNum 3 3 2 Tk.BG Tk.BG₂ Tk.κ Tk.t (Q * Tk.t) (min Tk.t (η * ε k))
          (F * min Tk.t (η * ε k)) ∧
        ∀ j ≤ k, Tk.t + xiK2 3 3 2 * (Q * Tk.t) + xiK2 3 3 2 * (F * min Tk.t (η * ε k)) ≤
          ε j := by
  obtain ⟨κmin, hlo, T₀, κdec, Q, F, η, hm0, hk0, hκ, hr, hQ, hQθ, hF, hη, hQ0, hF0, hη0, H⟩ :=
    StepTowerG.exists_collar_scales 3 3 2 le_rfl le_rfl le_rfl m₀ κlo hq0 hq1
  have e : (4 * ((3 : ℕ) : ℝ) * ((3 : ℕ) : ℝ) ^ 3 + ((3 : ℕ) : ℝ)) = 327 := by norm_num
  rw [e] at hQ
  rw [show ((2 : ℕ) : ℝ) = 2 by norm_num] at hQ hF
  refine ⟨κmin, hlo, T₀.ofThree hk0 hm0, κdec, Q, F, η, by exact_mod_cast hκ, by exact_mod_cast hr, hQ,
    hQθ, hF, hη, hQ0, hF0, hη0, fun ε hε hpos hgap h1 k => ?_⟩
  obtain ⟨Tk, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, hC, hFl, hR⟩ :=
    H ε hε hpos hgap h1 k
  rw [e] at hC
  exact ⟨Tk.ofThree (h11.trans hk0) (h12.trans hm0), h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, hC, hFl, hR⟩

/-! ### The class sequence -/

/-- The class sequence `ε_j = P.eps 3 3 j` is antitone (`α ≥ 0`, `α₀ ≥ 0`). -/
theorem classEps_antitone {P : Consts} (hα₀ : 0 ≤ P.α₀) (hα : 0 ≤ P.alpha 3) :
    Antitone (P.eps 3 3) := by
  refine antitone_nat_of_succ_le fun j => ?_
  have hg := epsSeq_gapE 3 (P.alpha 3) P.α₀ hα₀ j
  have hq : ((3 : ℕ) : ℝ) ^ (-P.alpha 3) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
  have e : (1 - (1 - ((3 : ℕ) : ℝ) ^ (-P.alpha 3))) = ((3 : ℕ) : ℝ) ^ (-P.alpha 3) := by ring
  rw [e] at hg
  have h0 : 0 ≤ P.eps 3 3 j := by
    have := epsTail_pos j
    unfold Consts.eps epsSeq
    positivity
  unfold Consts.eps at h0 ⊢
  nlinarith

/-- The gap of the class sequence: `ε_{j+1} ≤ 3^{-α} ε_j`. -/
theorem classEps_gap {P : Consts} (hα₀ : 0 ≤ P.α₀) (j : ℕ) :
    P.eps 3 3 (j + 1) ≤ (3 : ℝ) ^ (-P.alpha 3) * P.eps 3 3 j := by
  have hg := epsSeq_gapE 3 (P.alpha 3) P.α₀ hα₀ j
  have e : (1 - (1 - ((3 : ℕ) : ℝ) ^ (-P.alpha 3))) = (3 : ℝ) ^ (-P.alpha 3) := by
    push_cast; ring
  rw [e] at hg
  exact hg

/-- The lower bound of the class sequence: `α₀ 3^{-α j} ≤ ε_j`. -/
theorem classEps_lower {P : Consts} (hα₀ : 0 ≤ P.α₀) (j : ℕ) :
    P.α₀ * (3 : ℝ) ^ (-(P.alpha 3 * (j : ℝ))) ≤ P.eps 3 3 j := by
  have ht : 1 ≤ epsTail j := by
    unfold epsTail
    have : 0 ≤ ∑' m : ℕ, if j ≤ m then ((m : ℝ) ^ 2)⁻¹ else 0 :=
      tsum_nonneg fun m => by split_ifs <;> positivity
    linarith
  have e : (((3 : ℕ) : ℝ) ^ (-P.alpha 3)) ^ j = (3 : ℝ) ^ (-(P.alpha 3 * (j : ℝ))) := by
    push_cast
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    ring_nf
  have h0 : 0 ≤ (3 : ℝ) ^ (-(P.alpha 3 * (j : ℝ))) := by positivity
  unfold Consts.eps epsSeq
  rw [e]
  have := mul_le_mul_of_nonneg_left ht hα₀
  nlinarith

end Balaban.Inhabited
