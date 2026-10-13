/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepTowerG
public import Balaban.Inhabited.LevelRayTowerGeneral
public import Balaban.Fluctuation.MarkedRootGeometry
public import Balaban.Fluctuation.MarkedVBlockDec
public import Balaban.Inhabited.DAPhysicalCutoff
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# The mark budget constants at the general tower

The constants and budget theorems of `MarkBudgetAudit` for the general tower `StepTowerG d L N κmin`,
with the scale variable `b = β L^{k(d-2)}` in place of `β 3^k`.  The bodies are those of the fixed
definitions with `3, 3, 2` replaced by `d, L, N`.  The factor `27 = L^d N/2` of the fixed constant
`Ecst` is the factor `L^d · (N/2)` of `energyConstScaled`, the `3` in front of `V²` is `d` and the
`1/9` is `1/L²`.
-/

@[expose] public section

namespace Balaban.Inhabited.MarkBudgetAudit

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep

section Const

variable {d L N : ℕ} [NeZero L] {κmin : ℝ} (T : StepTowerG d L N κmin)

/-- The potential size `V = cK2' · t` of the block energy bound. -/
noncomputable abbrev VstarG : ℝ := cK2' d L N (famConst d L T.BG₂ T.κ) * T.t

/-- `E_*` of the landed bounds, at the scale `k`. -/
noncomputable abbrev EstarG (k : ℕ) : ℝ :=
  ‖energyBdScaled d L N (compWeight L 1) k (VstarG T) T.t (rho4 d L N T.BG T.κ)‖

/-- The scale-free part of `E_*`:
`L^d (N/2) (a (t+V)² + d V² + (1+ρ) V²/L²)`. -/
noncomputable abbrev EcstG (a : ℝ) : ℝ :=
  (L : ℝ) ^ d * ((N : ℝ) / 2 * (a * (T.t + VstarG T) ^ 2 + (d : ℝ) * VstarG T ^ 2 +
    (1 + rho4 d L N T.BG T.κ) * VstarG T ^ 2 / (L : ℝ) ^ 2))

/-- The bridge and fibre factor `c₁ M^d n_F e^{(2κ_dec-1) c_Br}` (`M = L^{1+m₁}`). -/
noncomputable abbrev KmarkG : ℝ :=
  (c1 d L * (((L : ℕ) : ℝ) ^ (1 + T.m₁)) ^ d) *
    ((nFibre d L : ℝ) * Real.exp ((2 * T.κdec - 1) * cBr d L))

/-- The constant `F₀` of the rooted marks `G_{z,Y'} = -β markedOut`. -/
noncomputable def cubicF0G (k : ℕ) (β p₁ : ℝ) : ℝ :=
  |β| * (3 * EstarG T k / ((lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁ / 4) ^ 3 * (1 / 32)) *
    (c1 d L * (((L : ℕ) : ℝ) ^ (1 + T.m₁)) ^ d) *
    ((nFibre d L : ℝ) * Real.exp ((2 * T.κdec - 1) * cBr d L)))

/-- The constant `F_dec(t₀) = (‖E_*‖/t₀) c₁ M^d n_F e^{a c_Br}` of the decoupled marks. -/
noncomputable def decFG (k : ℕ) (t₀ : ℝ) : ℝ :=
  (EstarG T k / t₀) * (c1 d L * (((L : ℕ) : ℝ) ^ (1 + T.m₁)) ^ d) *
    ((nFibre d L : ℝ) * Real.exp ((2 * T.κdec - 1) * cBr d L))

include T in
theorem LposG : (0 : ℝ) < (L : ℝ) := by
  have := T.hL
  exact_mod_cast (by omega : 0 < L)

include T in
theorem NposG : (0 : ℝ) < (N : ℝ) := by
  have := T.hN
  exact_mod_cast (by omega : 0 < N)

theorem VstarG_nonneg : 0 ≤ VstarG T := by
  have h := cK2'_nonneg (d := d) (L := L) (N := N) (B := famConst d L T.BG₂ T.κ) T.fam_nonneg
  exact mul_nonneg h T.t_pos.le

theorem KmarkG_pos : 0 < KmarkG T := by
  have := one_le_c1 d L
  have : (0 : ℝ) < nFibre d L := by unfold nFibre; positivity
  have := LposG T
  unfold KmarkG; positivity

theorem KmarkG_eq : KmarkG T = (c1 d L * (((L : ℕ) : ℝ) ^ (1 + T.m₁)) ^ d) *
    ((nFibre d L : ℝ) * Real.exp ((2 * T.κdec - 1) * cBr d L)) := rfl

include T in
theorem EcstG_nonneg_coeff : 0 ≤ (L : ℝ) ^ d * ((N : ℝ) / 2) := by
  have := LposG T
  have := NposG T
  positivity

theorem EcstG_lo {a : ℝ} (ha : 1 / 2 ≤ a) :
    (L : ℝ) ^ d * ((N : ℝ) / 2 * (1 / 2 * T.t ^ 2)) ≤ EcstG T a := by
  have h1 := VstarG_nonneg T
  have h2 := T.rho_nonneg
  have h3 := T.t_pos
  have hc := EcstG_nonneg_coeff T
  have hL := LposG T
  unfold EcstG
  have hN := NposG T
  refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (by positivity)) (by positivity)
  have e1 : (1 / 2 : ℝ) * T.t ^ 2 ≤ a * (T.t + VstarG T) ^ 2 := by
    have : T.t ^ 2 ≤ (T.t + VstarG T) ^ 2 := by nlinarith
    nlinarith [sq_nonneg (T.t + VstarG T)]
  have e2 : 0 ≤ (d : ℝ) * VstarG T ^ 2 := by positivity
  have e3 : 0 ≤ (1 + rho4 d L N T.BG T.κ) * VstarG T ^ 2 / (L : ℝ) ^ 2 := by positivity
  linarith

theorem EcstG_hi {a : ℝ} (ha : a ≤ 2) :
    EcstG T a ≤ (L : ℝ) ^ d * ((N : ℝ) / 2 * (2 * (T.t + VstarG T) ^ 2 + (d : ℝ) * VstarG T ^ 2 +
      (1 + rho4 d L N T.BG T.κ) * VstarG T ^ 2 / (L : ℝ) ^ 2)) := by
  have hc := EcstG_nonneg_coeff T
  have hL := LposG T
  have hN := NposG T
  unfold EcstG
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  nlinarith [sq_nonneg (T.t + VstarG T)]

theorem EcstG_pos {a : ℝ} (ha : 1 / 2 ≤ a) : 0 < EcstG T a := by
  have := EcstG_lo T ha
  have := T.t_pos
  have := LposG T
  have := NposG T
  have : 0 < (L : ℝ) ^ d * ((N : ℝ) / 2 * (1 / 2 * T.t ^ 2)) := by positivity
  linarith

theorem EstarG_eq {k : ℕ} (hmem : compWeight L (1 : ℝ) k ∈ Set.Icc (1 / 2 : ℝ) 2) :
    EstarG T k = (L : ℝ) ^ (k * (d - 2)) * EcstG T (compWeight L 1 k) := by
  have hpos := EcstG_pos T hmem.1
  have hL := LposG T
  unfold EstarG
  rw [energyBdScaled_eq (by have := T.hd; omega) _ _ _ _ _ hL.ne']
  have e : energyConstScaled d L N (compWeight L 1) k (VstarG T) T.t (rho4 d L N T.BG T.κ) =
      EcstG T (compWeight L 1 k) := by
    unfold energyConstScaled EcstG
    field_simp
    ring
  rw [e, Real.norm_of_nonneg (by positivity)]

include T in
theorem scalePosG (k : ℕ) : (0 : ℝ) < (L : ℝ) ^ (k * (d - 2)) := pow_pos (LposG T) _

include T in
theorem lvKappaG_posT : 0 < lvKappaG d L N T.κ T.t :=
  lvKappaG_pos (by have := T.hd; omega) T.hL (by have := T.hN; omega) T.κ T.t_pos

include T in
theorem compWeightG_mem {k : ℕ} (hk : 1 ≤ k) : compWeight L (1 : ℝ) k ∈ Set.Icc (1 / 2 : ℝ) 2 :=
  compWeight_one_mem T.hL hk

end Const

section Cubic

variable {d L N : ℕ} [NeZero L] {κmin : ℝ} (T : StepTowerG d L N κmin)

/-- The lower constant of the rooted family. -/
noncomputable def cLowG : ℝ :=
  96 * 512 * ((L : ℝ) ^ d * ((N : ℝ) / 2 * (1 / 2 * T.t ^ 2))) * KmarkG T /
    lvKappaG d L N T.κ T.t ^ 3

/-- The upper constant of the rooted family. -/
noncomputable def cHighG : ℝ :=
  96 * 4096 * ((L : ℝ) ^ d * ((N : ℝ) / 2 * (2 * (T.t + VstarG T) ^ 2 + (d : ℝ) * VstarG T ^ 2 +
    (1 + rho4 d L N T.BG T.κ) * VstarG T ^ 2 / (L : ℝ) ^ 2))) * KmarkG T /
    lvKappaG d L N T.κ T.t ^ 3

theorem cLowG_pos : 0 < cLowG T := by
  have := KmarkG_pos T
  have := T.t_pos
  have := lvKappaG_posT T
  have := LposG T
  have := NposG T
  unfold cLowG; positivity

/-- **The constant `F₀` in terms of `b = β L^{k(d-2)}`**:
`F₀ = 96 b Ecst Kmark / r³`, `r = lvR/4`. -/
theorem cubicF0G_eq_b {k : ℕ} (hk : 1 ≤ k) {β p₁ : ℝ} (hβ : 0 < β) :
    cubicF0G T k β p₁ = 96 * (β * (L : ℝ) ^ (k * (d - 2))) * EcstG T (compWeight L 1 k) *
      KmarkG T / (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁ / 4) ^ 3 := by
  unfold cubicF0G
  rw [EstarG_eq T (compWeightG_mem T hk), abs_of_pos hβ]
  unfold KmarkG
  ring

private theorem alg_loG (s κ p E K : ℝ) (hs : s ≠ 0) (hκ : κ ≠ 0) (hp : p ≠ 0) :
    96 * 512 * E * K / κ ^ 3 * p ^ 3 / s = 96 * s ^ 2 * E * K / (κ * s / (8 * p)) ^ 3 := by
  field_simp
  ring

private theorem alg_hiG (s κ p E K : ℝ) (hs : s ≠ 0) (hκ : κ ≠ 0) (hp : p ≠ 0) :
    96 * 4096 * E * K / κ ^ 3 * p ^ 3 / s = 96 * s ^ 2 * E * K / (κ * s / (16 * p)) ^ 3 := by
  field_simp
  ring

theorem lvRG_div_four_le {b p₁ : ℝ} (hp : 0 < p₁) :
    lvRG d L N T.κ T.t b p₁ / 4 ≤ lvKappaG d L N T.κ T.t * Real.sqrt b / (8 * p₁) := by
  unfold lvRG
  rw [lvCpsiG_eq]
  have e : (lvKappaG d L N T.κ T.t * Real.sqrt b / (2 * p₁) - 4) / 4 =
      lvKappaG d L N T.κ T.t * Real.sqrt b / (8 * p₁) - 1 := by field_simp; ring
  rw [e]; linarith

theorem le_lvRG_div_four {b p₁ : ℝ} (hp : 0 < p₁)
    (h16 : 16 * p₁ ≤ lvCpsiG d L N T.κ T.t b) :
    lvKappaG d L N T.κ T.t * Real.sqrt b / (16 * p₁) ≤ lvRG d L N T.κ T.t b p₁ / 4 := by
  unfold lvRG
  rw [← lvCpsiG_eq]
  rw [le_div_iff₀ (by norm_num : (0:ℝ) < 4)]
  rw [lvCpsiG_eq] at h16 ⊢
  have e : lvKappaG d L N T.κ T.t * Real.sqrt b / (16 * p₁) * 4 =
      lvKappaG d L N T.κ T.t * Real.sqrt b / (4 * p₁) := by field_simp; ring
  rw [e]
  have h : 4 ≤ lvKappaG d L N T.κ T.t * Real.sqrt b / (4 * p₁) := by
    rw [le_div_iff₀ (by positivity)]; linarith
  have e2 : lvKappaG d L N T.κ T.t * Real.sqrt b / (2 * p₁) =
      2 * (lvKappaG d L N T.κ T.t * Real.sqrt b / (4 * p₁)) := by field_simp; ring
  rw [e2]; linarith

/-- **Lower bound (the true exponent is `-1/2`)**: for `r > 0`,
`F₀ ≥ cLow · p₁³ / √b`. -/
theorem markedRoot_F0_geG {k : ℕ} (hk : 1 ≤ k) {β p₁ : ℝ} (hβ : 0 < β) (hp : 0 < p₁)
    (hr : 0 < lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁) :
    cLowG T * p₁ ^ 3 / Real.sqrt (β * (L : ℝ) ^ (k * (d - 2))) ≤ cubicF0G T k β p₁ := by
  rw [cubicF0G_eq_b T hk hβ]
  have hLs := scalePosG T k
  set b := β * (L : ℝ) ^ (k * (d - 2)) with hb
  have hb0 : 0 < b := by positivity
  have hs : 0 < Real.sqrt b := Real.sqrt_pos.2 hb0
  have hk1 := lvKappaG_posT T
  have hEc := EcstG_lo T (compWeightG_mem T hk).1
  have hK := KmarkG_pos T
  set r := lvRG d L N T.κ T.t b p₁ / 4 with hrdef
  have hr4 : 0 < r := by rw [hrdef]; positivity
  have hrA := lvRG_div_four_le T (b := b) hp
  have hA : 0 < lvKappaG d L N T.κ T.t * Real.sqrt b / (8 * p₁) := by positivity
  have h3 : r ^ 3 ≤ (lvKappaG d L N T.κ T.t * Real.sqrt b / (8 * p₁)) ^ 3 :=
    pow_le_pow_left₀ hr4.le hrA 3
  have hsq : Real.sqrt b ^ 2 = b := Real.sq_sqrt hb0.le
  have step : 96 * b * ((L : ℝ) ^ d * ((N : ℝ) / 2 * (1 / 2 * T.t ^ 2))) * KmarkG T /
      (lvKappaG d L N T.κ T.t * Real.sqrt b / (8 * p₁)) ^ 3 ≤
      96 * b * EcstG T (compWeight L 1 k) * KmarkG T / r ^ 3 := by
    have hE0 := EcstG_pos T (compWeightG_mem T hk).1
    apply div_le_div₀ (by positivity) _ (by positivity) h3
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hEc (by positivity)) hK.le
  refine le_trans (le_of_eq ?_) step
  unfold cLowG
  have := alg_loG (Real.sqrt b) (lvKappaG d L N T.κ T.t) p₁
    ((L : ℝ) ^ d * ((N : ℝ) / 2 * (1 / 2 * T.t ^ 2))) (KmarkG T) hs.ne' hk1.ne' hp.ne'
  rw [hsq] at this
  exact this

/-- **Upper bound**: for `16 p₁ ≤ c_ψ`, `F₀ ≤ cHigh · p₁³ / √b`. -/
theorem markedRoot_F0_leG {k : ℕ} (hk : 1 ≤ k) {β p₁ : ℝ} (hβ : 0 < β) (hp : 0 < p₁)
    (h16 : 16 * p₁ ≤ lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))) :
    cubicF0G T k β p₁ ≤ cHighG T * p₁ ^ 3 / Real.sqrt (β * (L : ℝ) ^ (k * (d - 2))) := by
  rw [cubicF0G_eq_b T hk hβ]
  have hLs := scalePosG T k
  set b := β * (L : ℝ) ^ (k * (d - 2)) with hb
  have hb0 : 0 < b := by positivity
  have hs : 0 < Real.sqrt b := Real.sqrt_pos.2 hb0
  have hk1 := lvKappaG_posT T
  have hEc := EcstG_hi T (compWeightG_mem T hk).2
  have hK := KmarkG_pos T
  have hE0 := EcstG_pos T (compWeightG_mem T hk).1
  have hrA := le_lvRG_div_four T hp h16
  have hA : 0 < lvKappaG d L N T.κ T.t * Real.sqrt b / (16 * p₁) := by positivity
  set r := lvRG d L N T.κ T.t b p₁ / 4 with hrdef
  have h3 : (lvKappaG d L N T.κ T.t * Real.sqrt b / (16 * p₁)) ^ 3 ≤ r ^ 3 :=
    pow_le_pow_left₀ hA.le hrA 3
  have hsq : Real.sqrt b ^ 2 = b := Real.sq_sqrt hb0.le
  have step : 96 * b * EcstG T (compWeight L 1 k) * KmarkG T / r ^ 3 ≤
      96 * b * ((L : ℝ) ^ d * ((N : ℝ) / 2 * (2 * (T.t + VstarG T) ^ 2 + (d : ℝ) * VstarG T ^ 2 +
        (1 + rho4 d L N T.BG T.κ) * VstarG T ^ 2 / (L : ℝ) ^ 2))) * KmarkG T /
      (lvKappaG d L N T.κ T.t * Real.sqrt b / (16 * p₁)) ^ 3 := by
    apply div_le_div₀ _ _ (by positivity) h3
    · exact mul_nonneg (mul_nonneg (by positivity) (hE0.le.trans hEc)) hK.le
    · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hEc (by positivity)) hK.le
  refine le_trans step (le_of_eq ?_)
  unfold cHighG
  have := alg_hiG (Real.sqrt b) (lvKappaG d L N T.κ T.t) p₁
    ((L : ℝ) ^ d * ((N : ℝ) / 2 * (2 * (T.t + VstarG T) ^ 2 + (d : ℝ) * VstarG T ^ 2 +
      (1 + rho4 d L N T.BG T.κ) * VstarG T ^ 2 / (L : ℝ) ^ 2))) (KmarkG T) hs.ne'
    hk1.ne' hp.ne'
  rw [hsq] at this
  exact this.symm

end Cubic

section Polylog

variable {d L N : ℕ} [NeZero L] {κmin : ℝ} (T : StepTowerG d L N κmin)

/-- **The rooted constant is `O(p₁³ b^{-1/2})`, with `p₁ ≤ A₁ (log b)^p`**: one threshold `b₀`
after which `F₀ ≤ cHigh A₁³ (log b)^{3p} / √b`. -/
theorem markedRoot_F0_le_polylogG {A₁ : ℝ} (hA : 0 ≤ A₁) (p : ℕ) :
    ∃ b₀ : ℝ, 1 ≤ b₀ ∧ ∀ (k : ℕ), 1 ≤ k → ∀ β p₁ : ℝ, 0 < β → 0 < p₁ →
      b₀ ≤ β * (L : ℝ) ^ (k * (d - 2)) →
      p₁ ≤ pLog A₁ p (β * (L : ℝ) ^ (k * (d - 2))) →
      cubicF0G T k β p₁ ≤
        cHighG T * (A₁ ^ 3 * Real.log (β * (L : ℝ) ^ (k * (d - 2))) ^ (3 * p)) /
          Real.sqrt (β * (L : ℝ) ^ (k * (d - 2))) := by
  have hk1 := lvKappaG_posT T
  refine ⟨max 1 (pLogThreshold A₁ p (lvKappaG d L N T.κ T.t / 16)), le_max_left _ _,
    fun k hk β p₁ hβ hp hb hp₁ => ?_⟩
  have hb1 : 1 ≤ β * (L : ℝ) ^ (k * (d - 2)) := (le_max_left _ _).trans hb
  have hbt : pLogThreshold A₁ p (lvKappaG d L N T.κ T.t / 16) ≤ β * (L : ℝ) ^ (k * (d - 2)) :=
    (le_max_right _ _).trans hb
  have hpl := pLog_le_mul_sqrt hA p (by positivity : 0 < lvKappaG d L N T.κ T.t / 16) hb1 hbt
  have h16 : 16 * p₁ ≤ lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) := by
    rw [lvCpsiG_eq]; linarith
  refine (markedRoot_F0_leG T hk hβ hp h16).trans ?_
  have hc : 0 ≤ cHighG T := by
    have := KmarkG_pos T
    have := T.rho_nonneg
    have := VstarG_nonneg T
    have := LposG T
    have := NposG T
    have := lvKappaG_posT T
    have := T.t_pos
    unfold cHighG; positivity
  have h3 : p₁ ^ 3 ≤ A₁ ^ 3 * Real.log (β * (L : ℝ) ^ (k * (d - 2))) ^ (3 * p) := by
    have hpl0 : p₁ ^ 3 ≤ pLog A₁ p (β * (L : ℝ) ^ (k * (d - 2))) ^ 3 := pow_le_pow_left₀ hp.le hp₁ 3
    refine hpl0.trans (le_of_eq ?_)
    unfold pLog
    rw [mul_pow, ← pow_mul, mul_comm p 3]
  gcongr

end Polylog

section Decoupled

variable {d L N : ℕ} [NeZero L] {κmin : ℝ} (T : StepTowerG d L N κmin)

/-- The lower bound of `covSupConstC` on weights in `[1/2, 2]`. -/
noncomputable def covMinG (d L N : ℕ) : ℝ :=
  (N : ℝ) * Green.ballConst d (xAgmonRate d L / L) * (2 / Real.sqrt 2)

omit [NeZero L] in
theorem covMinG_pos (hd : 0 < d) (hL : 3 ≤ L) (hN : 0 < N) : 0 < covMinG d L N := by
  have := ballConst_pos (d := d) (L := L) hd hL
  have : (0 : ℝ) < N := by exact_mod_cast hN
  unfold covMinG; positivity

omit [NeZero L] in
theorem covMinG_le (hd : 0 < d) (hL : 3 ≤ L) (hN : 0 < N) {a : ℝ} (ha : a ∈ Set.Icc (1 / 2 : ℝ) 2) (κ : ℝ) :
    covMinG d L N ≤ covSupConstC d L N a κ := by
  obtain ⟨h1, h2⟩ := ha
  have ha0 : 0 < a := by linarith
  have hB := ballConst_pos (d := d) (L := L) hd hL
  have hN : (0 : ℝ) < N := by exact_mod_cast hN
  have hε : 0 ≤ xAgmonRate d L :=
    (xAgmonRate_pos (L := L) hd hL).le
  have hT := covTConst_nonneg d L a (xAgmonRate d L) κ
  have e1 : (1 : ℝ) ≤ Real.exp (xAgmonRate d L * (2 * d)) := Real.one_le_exp (by positivity)
  have e2 : (1 : ℝ) ≤ Real.exp (xAgmonRate d L * d / L) := Real.one_le_exp (by positivity)
  have hs : Real.sqrt a ≤ Real.sqrt 2 := Real.sqrt_le_sqrt h2
  have hs0 : 0 < Real.sqrt a := Real.sqrt_pos.2 ha0
  unfold covSupConstC covSqrtEntryConstC covC1Const covMinG
  have hC : 2 ≤ 2 * Real.exp (xAgmonRate d L * (2 * d)) + covTConst d L a (xAgmonRate d L) κ / a := by
    have h0 : 0 ≤ covTConst d L a (xAgmonRate d L) κ / a := by positivity
    exact le_add_of_le_of_nonneg (by simpa using mul_le_mul_of_nonneg_left e1 (by norm_num : (0:ℝ) ≤ 2)) h0
  have h4 : 2 / Real.sqrt 2 ≤ (2 * Real.exp (xAgmonRate d L * (2 * d)) +
      covTConst d L a (xAgmonRate d L) κ / a) * Real.exp (xAgmonRate d L * d / L) /
        Real.sqrt a := by
    rw [le_div_iff₀ hs0]
    have hs2 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
    calc 2 / Real.sqrt 2 * Real.sqrt a ≤ 2 / Real.sqrt 2 * Real.sqrt 2 :=
          mul_le_mul_of_nonneg_left hs (by positivity)
      _ = 2 := by field_simp
      _ ≤ _ := by nlinarith
  exact mul_le_mul_of_nonneg_left h4 (by positivity)

/-- The radius `markedRad` at `cc = b^{-1/2}`, `c_ψ = p₁`, as an explicit function. -/
noncomputable def decMRG (k : ℕ) (b p₁ : ℝ) : ℝ :=
  Real.sqrt N * ((Real.sqrt b)⁻¹ * (covSupConstC d L N (compWeight L 1 k) T.κ * p₁))

theorem markedRadG_eq (k : ℕ) {b : ℝ} (hb : 0 ≤ b) (p₁ : ℝ) :
    markedRad d L N k 1 T.κ p₁ (((b ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) = decMRG T k b p₁ := by
  unfold markedRad decMRG
  rw [Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hb _), Real.sqrt_eq_rpow b,
    Real.rpow_neg hb]

theorem decMRG_ge {k : ℕ} (hk : 1 ≤ k) {b p₁ : ℝ} (hb : 0 < b) (hp : 0 ≤ p₁) :
    Real.sqrt N * ((Real.sqrt b)⁻¹ * (covMinG d L N * p₁)) ≤ decMRG T k b p₁ := by
  have := covMinG_le (d := d) (L := L) (N := N) (by have := T.hd; omega) T.hL (by have := T.hN; omega) (compWeightG_mem T hk) T.κ
  unfold decMRG
  have hs : 0 < Real.sqrt b := Real.sqrt_pos.2 hb
  gcongr

theorem decMRG_le {k : ℕ} (hk : 1 ≤ k) {b p₁ : ℝ} (hb : 0 < b) (hp : 0 ≤ p₁) :
    decMRG T k b p₁ ≤ Real.sqrt N * ((Real.sqrt b)⁻¹ * (covSupMaxC d L N T.κ * p₁)) := by
  have := covSupConstC_le_covSupMaxC (N := N) (d := d) (L := L) (by have := T.hd; omega) T.hL T.κ
    (compWeightG_mem T hk)
  unfold decMRG
  have hs : 0 < Real.sqrt b := Real.sqrt_pos.2 hb
  gcongr

theorem decMRG_pos {k : ℕ} (hk : 1 ≤ k) {b p₁ : ℝ} (hb : 0 < b) (hp : 0 < p₁) :
    0 < decMRG T k b p₁ := by
  refine lt_of_lt_of_le ?_ (decMRG_ge T hk hb hp.le)
  have := covMinG_pos (d := d) (L := L) (N := N) (by have := T.hd; omega) T.hL (by have := T.hN; omega)
  have := NposG T
  positivity

theorem decFG_eq (k : ℕ) (t₀ : ℝ) : decFG T k t₀ = EstarG T k / t₀ * KmarkG T := by
  unfold decFG KmarkG; ring

/-- **Lower bound for the constant of the decoupled count at every admissible `t₀`.** -/
theorem decFG_ge {k : ℕ} {t₀ mr : ℝ} (ht0 : 0 < t₀) (hadm : t₀ * mr < T.t) :
    EstarG T k * mr / T.t * KmarkG T ≤ decFG T k t₀ := by
  have hE : 0 ≤ EstarG T k := norm_nonneg _
  have hK := KmarkG_pos T
  have ht := T.t_pos
  rw [decFG_eq]
  refine mul_le_mul_of_nonneg_right ?_ hK.le
  rw [div_le_div_iff₀ ht ht0]
  nlinarith [mul_le_mul_of_nonneg_left hadm.le hE]

/-- The lower constant of the decoupled marks `G = -β markedOutDec`. -/
noncomputable def cDecLowG : ℝ :=
  ((L : ℝ) ^ d * ((N : ℝ) / 2 * (1 / 2 * T.t ^ 2))) * (Real.sqrt N * covMinG d L N) *
    KmarkG T / T.t

/-- The upper constant of the decoupled marks at the best `t₀`. -/
noncomputable def cDecHighG : ℝ :=
  2 * ((L : ℝ) ^ d * ((N : ℝ) / 2 * (2 * (T.t + VstarG T) ^ 2 + (d : ℝ) * VstarG T ^ 2 +
    (1 + rho4 d L N T.BG T.κ) * VstarG T ^ 2 / (L : ℝ) ^ 2))) *
    (Real.sqrt N * covSupMaxC d L N T.κ) * KmarkG T / T.t

theorem cDecLowG_pos : 0 < cDecLowG T := by
  have := KmarkG_pos T
  have := T.t_pos
  have := covMinG_pos (d := d) (L := L) (N := N) (by have := T.hd; omega) T.hL (by have := T.hN; omega)
  have := LposG T
  have := NposG T
  unfold cDecLowG; positivity

/-- **The decoupled constant grows like `√b`.**  For every admissible `t₀`, the constant
`β F_dec(t₀)` of the mark `G = -β markedOutDec` is at least `cDecLow · p₁ · √b`. -/
theorem dec_G_geG {k : ℕ} (hk : 1 ≤ k) {β p₁ t₀ : ℝ} (hβ : 0 < β) (hp : 0 < p₁) (ht0 : 0 < t₀)
    (hadm : t₀ * decMRG T k (β * (L : ℝ) ^ (k * (d - 2))) p₁ < T.t) :
    cDecLowG T * p₁ * Real.sqrt (β * (L : ℝ) ^ (k * (d - 2))) ≤ |β| * decFG T k t₀ := by
  have hLs := scalePosG T k
  have hNr := NposG T
  set b := β * (L : ℝ) ^ (k * (d - 2)) with hb
  have hb0 : 0 < b := by positivity
  have hs : 0 < Real.sqrt b := Real.sqrt_pos.2 hb0
  have hsq : Real.sqrt b ^ 2 = b := Real.sq_sqrt hb0.le
  have h1 := decFG_ge T (k := k) ht0 hadm
  have h2 := decMRG_ge T hk hb0 hp.le
  have hEc := EcstG_lo T (compWeightG_mem T hk).1
  have hK := KmarkG_pos T
  have ht := T.t_pos
  rw [abs_of_pos hβ]
  refine le_trans ?_ (mul_le_mul_of_nonneg_left h1 hβ.le)
  rw [EstarG_eq T (compWeightG_mem T hk)]
  have hmr0 := covMinG_pos (d := d) (L := L) (N := N) (by have := T.hd; omega) T.hL (by have := T.hN; omega)
  have key : cDecLowG T * p₁ * Real.sqrt b =
      β * ((L : ℝ) ^ (k * (d - 2)) * ((L : ℝ) ^ d * ((N : ℝ) / 2 * (1 / 2 * T.t ^ 2))) *
        (Real.sqrt N * ((Real.sqrt b)⁻¹ * (covMinG d L N * p₁))) / T.t * KmarkG T) := by
    unfold cDecLowG
    generalize KmarkG T = K
    generalize covMinG d L N = cm
    field_simp
    rw [hsq, hb]
    ring
  rw [key]
  refine mul_le_mul_of_nonneg_left ?_ hβ.le
  have e0 := EcstG_pos T (compWeightG_mem T hk).1
  gcongr

/-- **Attained: the best admissible `t₀` gives `β F_dec ≤ cDecHigh · p₁ · √b`.** -/
theorem dec_G_le_bestG {k : ℕ} (hk : 1 ≤ k) {β p₁ : ℝ} (hβ : 0 < β) (hp : 0 < p₁)
    (hsmall : decMRG T k (β * (L : ℝ) ^ (k * (d - 2))) p₁ < T.t / 2) :
    (∀ u : ℝ, |u| ≤ 1 →
      (u + T.t / (2 * decMRG T k (β * (L : ℝ) ^ (k * (d - 2))) p₁)) *
        decMRG T k (β * (L : ℝ) ^ (k * (d - 2))) p₁ < T.t) ∧
    |β| * decFG T k (T.t / (2 * decMRG T k (β * (L : ℝ) ^ (k * (d - 2))) p₁)) ≤
      cDecHighG T * p₁ * Real.sqrt (β * (L : ℝ) ^ (k * (d - 2))) := by
  have hLs := scalePosG T k
  have hNr := NposG T
  set b := β * (L : ℝ) ^ (k * (d - 2)) with hb
  have hb0 : 0 < b := by positivity
  have hs : 0 < Real.sqrt b := Real.sqrt_pos.2 hb0
  have hsq : Real.sqrt b ^ 2 = b := Real.sq_sqrt hb0.le
  have hmr := decMRG_pos T hk hb0 hp
  set mr := decMRG T k b p₁ with hmrdef
  have ht := T.t_pos
  have hK := KmarkG_pos T
  refine ⟨fun u hu => ?_, ?_⟩
  · have : (u + T.t / (2 * mr)) * mr = u * mr + T.t / 2 := by field_simp
    rw [this]
    have : u * mr ≤ mr := by
      calc u * mr ≤ |u| * mr := mul_le_mul_of_nonneg_right (le_abs_self u) hmr.le
        _ ≤ 1 * mr := mul_le_mul_of_nonneg_right hu hmr.le
        _ = mr := one_mul _
    linarith
  · have hE0 := EcstG_pos T (compWeightG_mem T hk).1
    have hEh := EcstG_hi T (compWeightG_mem T hk).2
    have hmrle := decMRG_le T hk hb0 hp.le
    have e : decFG T k (T.t / (2 * mr)) =
        2 * ((L : ℝ) ^ (k * (d - 2)) * EcstG T (compWeight L 1 k)) * mr / T.t * KmarkG T := by
      rw [decFG_eq, EstarG_eq T (compWeightG_mem T hk)]
      generalize KmarkG T = K
      field_simp
    rw [abs_of_pos hβ, e]
    have hCmax : 0 ≤ covSupMaxC d L N T.κ :=
      covSupMaxC_nonneg_general (by have := T.hd; omega) T.hL T.κ
    have step : β * (2 * ((L : ℝ) ^ (k * (d - 2)) * EcstG T (compWeight L 1 k)) * mr / T.t *
        KmarkG T) ≤
        β * (2 * ((L : ℝ) ^ (k * (d - 2)) * ((L : ℝ) ^ d * ((N : ℝ) / 2 *
          (2 * (T.t + VstarG T) ^ 2 + (d : ℝ) * VstarG T ^ 2 +
          (1 + rho4 d L N T.BG T.κ) * VstarG T ^ 2 / (L : ℝ) ^ 2)))) *
          (Real.sqrt N * ((Real.sqrt b)⁻¹ * (covSupMaxC d L N T.κ * p₁))) / T.t * KmarkG T) := by
      apply mul_le_mul_of_nonneg_left _ hβ.le
      have := T.rho_nonneg
      have := VstarG_nonneg T
      gcongr
    refine step.trans (le_of_eq ?_)
    unfold cDecHighG
    generalize KmarkG T = K
    field_simp
    rw [hsq, hb]
    ring

end Decoupled

section Verdict

variable {d L N : ℕ} [NeZero L] {κmin : ℝ} (T : StepTowerG d L N κmin)

/-- **The rooted constant exceeds the budget `b⁻¹` of (c).**  For every positive constant `C`,
`p₁ ≥ 1` and `b = β L^{k(d-2)} > 1/(C cLow)²`: `b⁻¹ < C · F₀`. -/
theorem cubic_exceeds_budgetG {k : ℕ} (hk : 1 ≤ k) {β p₁ C : ℝ} (hβ : 0 < β) (hp1 : 1 ≤ p₁)
    (hr : 0 < lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁) (hC : 0 < C)
    (hbig : 1 / (C * cLowG T) ^ 2 < β * (L : ℝ) ^ (k * (d - 2))) :
    (β * (L : ℝ) ^ (k * (d - 2)))⁻¹ < C * cubicF0G T k β p₁ := by
  have hLs := scalePosG T k
  set b := β * (L : ℝ) ^ (k * (d - 2)) with hb
  have hb0 : 0 < b := by positivity
  have hs : 0 < Real.sqrt b := Real.sqrt_pos.2 hb0
  have hsq : Real.sqrt b ^ 2 = b := Real.sq_sqrt hb0.le
  have hcl := cLowG_pos T
  have hCc : 0 < C * cLowG T := by positivity
  have hF := markedRoot_F0_geG T hk hβ (by linarith) hr
  have hp3 : 1 ≤ p₁ ^ 3 := one_le_pow₀ hp1
  have h1 : 1 / (C * cLowG T) < Real.sqrt b := by
    rw [Real.lt_sqrt (by positivity)]
    rw [div_pow, one_pow]
    exact hbig
  have h2 : C * cLowG T / Real.sqrt b ≤ C * cubicF0G T k β p₁ := by
    have : cLowG T / Real.sqrt b ≤ cLowG T * p₁ ^ 3 / Real.sqrt b :=
      div_le_div_of_nonneg_right (le_mul_of_one_le_right hcl.le hp3) hs.le
    calc C * cLowG T / Real.sqrt b = C * (cLowG T / Real.sqrt b) := by ring
      _ ≤ C * (cLowG T * p₁ ^ 3 / Real.sqrt b) := mul_le_mul_of_nonneg_left this hC.le
      _ ≤ _ := mul_le_mul_of_nonneg_left (by simpa [hb] using hF) hC.le
  refine lt_of_lt_of_le ?_ h2
  rw [lt_div_iff₀ hs]
  have h3 : 1 < C * cLowG T * Real.sqrt b := by
    rw [div_lt_iff₀ hCc] at h1; linarith
  have : b⁻¹ * Real.sqrt b = (Real.sqrt b)⁻¹ := by
    rw [inv_mul_eq_iff_eq_mul₀ hb0.ne']
    field_simp
    nlinarith [hsq]
  rw [this]
  rw [inv_lt_iff_one_lt_mul₀ hs]
  linarith

/-- **Necessary condition for the rooted budget:** if `C · F₀ ≤ b⁻¹` then
`C cLow p₁³ ≤ b^{-1/2}`. -/
theorem cubic_budget_needs_small_p1G {k : ℕ} (hk : 1 ≤ k) {β p₁ C : ℝ} (hβ : 0 < β)
    (hp : 0 < p₁) (hr : 0 < lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁) (hC : 0 < C)
    (h : C * cubicF0G T k β p₁ ≤ (β * (L : ℝ) ^ (k * (d - 2)))⁻¹) :
    C * cLowG T * p₁ ^ 3 ≤ (Real.sqrt (β * (L : ℝ) ^ (k * (d - 2))))⁻¹ := by
  have hLs := scalePosG T k
  set b := β * (L : ℝ) ^ (k * (d - 2)) with hb
  have hb0 : 0 < b := by positivity
  have hs : 0 < Real.sqrt b := Real.sqrt_pos.2 hb0
  have hsq : Real.sqrt b ^ 2 = b := Real.sq_sqrt hb0.le
  have hF := markedRoot_F0_geG T hk hβ hp hr
  have h1 : C * (cLowG T * p₁ ^ 3 / Real.sqrt b) ≤ b⁻¹ :=
    (mul_le_mul_of_nonneg_left (by simpa [hb] using hF) hC.le).trans h
  have h2 : C * cLowG T * p₁ ^ 3 / Real.sqrt b ≤ b⁻¹ := by
    calc _ = C * (cLowG T * p₁ ^ 3 / Real.sqrt b) := by ring
      _ ≤ _ := h1
  rw [div_le_iff₀ hs] at h2
  have : b⁻¹ * Real.sqrt b = (Real.sqrt b)⁻¹ := by
    rw [inv_mul_eq_iff_eq_mul₀ hb0.ne']
    field_simp
    nlinarith [hsq]
  rwa [this] at h2

/-- **The decoupled constant exceeds the budget `b⁻¹` of (c)**, at every admissible `t₀`. -/
theorem dec_exceeds_budgetG {k : ℕ} (hk : 1 ≤ k) {β p₁ t₀ C : ℝ} (hβ : 0 < β) (hp1 : 1 ≤ p₁)
    (ht0 : 0 < t₀) (hadm : t₀ * decMRG T k (β * (L : ℝ) ^ (k * (d - 2))) p₁ < T.t) (hC : 0 < C)
    (hb1 : 1 ≤ β * (L : ℝ) ^ (k * (d - 2)))
    (hbig : 1 / (C * cDecLowG T) ^ 2 < β * (L : ℝ) ^ (k * (d - 2))) :
    (β * (L : ℝ) ^ (k * (d - 2)))⁻¹ < C * (|β| * decFG T k t₀) := by
  have hLs := scalePosG T k
  set b := β * (L : ℝ) ^ (k * (d - 2)) with hb
  have hb0 : 0 < b := by positivity
  have hs : 0 < Real.sqrt b := Real.sqrt_pos.2 hb0
  have hcl := cDecLowG_pos T
  have hCc : 0 < C * cDecLowG T := by positivity
  have hF := dec_G_geG T hk hβ (by linarith) ht0 hadm
  have h1 : 1 / (C * cDecLowG T) < Real.sqrt b := by
    rw [Real.lt_sqrt (by positivity)]
    rw [div_pow, one_pow]
    exact hbig
  have h3 : 1 < C * cDecLowG T * Real.sqrt b := by
    rw [div_lt_iff₀ hCc] at h1; linarith
  have h4 : C * cDecLowG T * Real.sqrt b ≤ C * (|β| * decFG T k t₀) := by
    have : cDecLowG T * Real.sqrt b ≤ cDecLowG T * p₁ * Real.sqrt b := by
      have := mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hcl.le hp1) hs.le
      simpa using this
    calc C * cDecLowG T * Real.sqrt b = C * (cDecLowG T * Real.sqrt b) := by ring
      _ ≤ C * (cDecLowG T * p₁ * Real.sqrt b) := mul_le_mul_of_nonneg_left this hC.le
      _ ≤ _ := mul_le_mul_of_nonneg_left (by simpa [hb] using hF) hC.le
  have h5 : b⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hb1
  linarith

end Verdict

end Balaban.Inhabited.MarkBudgetAudit
