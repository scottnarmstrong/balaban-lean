/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Background.LocalSolution
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# Normalization of an interpolated vector (LEMMA53-astra.md, (5), (7), (8)-(9))

For `v ∈ ℂ^N` with `v ⬝ v` near `1` put `s = √(v ⬝ v)` (principal root, `sqrtDot`) and
`F(v) = s⁻¹ v`.  The first and centred second differences of `F` along three vectors
`v₀, v₊, v₋` are bounded by the first and second differences of `v`, without derivatives:
the identity `2 s₀ (s₊ + s₋ - 2 s₀) + (s₊ - s₀)² + (s₋ - s₀)² = z₊ + z₋ - 2 z₀` replaces the
Taylor remainder of the note.
-/

@[expose] public section

namespace Balaban.Background

open Matrix

section Scalar

/-- A principal square root of a number near `1`. -/
theorem sqrt_near_one {z s : ℂ} (hz : ‖z - 1‖ ≤ 1 / 20) (hs2 : s ^ 2 = z) (hsre : 0 ≤ s.re) :
    ‖s - 1‖ ≤ ‖z - 1‖ ∧ 19 / 20 ≤ s.re := by
  have hprod : (s - 1) * (s + 1) = z - 1 := by rw [← hs2]; ring
  have h1 : 1 ≤ ‖s + 1‖ := by
    refine le_trans ?_ (Complex.abs_re_le_norm _)
    have : (s + 1).re = s.re + 1 := by simp
    rw [this, abs_of_nonneg (by linarith)]; linarith
  have h2 : ‖s - 1‖ ≤ ‖z - 1‖ := by
    calc ‖s - 1‖ = ‖s - 1‖ * 1 := by ring
      _ ≤ ‖s - 1‖ * ‖s + 1‖ := mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ = ‖z - 1‖ := by rw [← norm_mul, hprod]
  refine ⟨h2, ?_⟩
  have h3 : |(s - 1).re| ≤ 1 / 20 := (Complex.abs_re_le_norm _).trans (h2.trans hz)
  have : (s - 1).re = s.re - 1 := by simp
  rw [this] at h3
  linarith [(abs_le.1 h3).1]

theorem norm_ge_of_re {s : ℂ} (h : 19 / 20 ≤ s.re) : 19 / 20 ≤ ‖s‖ :=
  h.trans ((le_abs_self _).trans (Complex.abs_re_le_norm _))

theorem sqrt_sub_le {z₀ z₁ s₀ s₁ : ℂ} (h0 : 19 / 20 ≤ s₀.re) (h1 : 19 / 20 ≤ s₁.re)
    (hs0 : s₀ ^ 2 = z₀) (hs1 : s₁ ^ 2 = z₁) : ‖s₁ - s₀‖ ≤ ‖z₁ - z₀‖ := by
  have hprod : (s₁ - s₀) * (s₁ + s₀) = z₁ - z₀ := by rw [← hs0, ← hs1]; ring
  have hge : 1 ≤ ‖s₁ + s₀‖ := by
    refine le_trans ?_ (Complex.abs_re_le_norm _)
    have : (s₁ + s₀).re = s₁.re + s₀.re := by simp
    rw [this, abs_of_nonneg (by linarith)]; linarith
  calc ‖s₁ - s₀‖ = ‖s₁ - s₀‖ * 1 := by ring
    _ ≤ ‖s₁ - s₀‖ * ‖s₁ + s₀‖ := mul_le_mul_of_nonneg_left hge (norm_nonneg _)
    _ = ‖z₁ - z₀‖ := by rw [← norm_mul, hprod]

theorem sqrt_second_le {z₀ zp zm s₀ sp sm : ℂ} (h0 : 19 / 20 ≤ s₀.re)
    (hs0 : s₀ ^ 2 = z₀) (hsp : sp ^ 2 = zp) (hsm : sm ^ 2 = zm) :
    ‖sp + sm - 2 * s₀‖ ≤ ‖zp + zm - 2 * z₀‖ + ‖sp - s₀‖ ^ 2 + ‖sm - s₀‖ ^ 2 := by
  have hid : 2 * s₀ * (sp + sm - 2 * s₀) = (zp + zm - 2 * z₀) - (sp - s₀) ^ 2 - (sm - s₀) ^ 2 := by
    rw [← hs0, ← hsp, ← hsm]; ring
  have hn : 1 ≤ ‖2 * s₀‖ := by
    have := norm_ge_of_re h0
    rw [norm_mul]; simp; linarith
  have : ‖2 * s₀‖ * ‖sp + sm - 2 * s₀‖ ≤ ‖zp + zm - 2 * z₀‖ + ‖sp - s₀‖ ^ 2 + ‖sm - s₀‖ ^ 2 := by
    rw [← norm_mul, hid]
    calc _ ≤ ‖(zp + zm - 2 * z₀) - (sp - s₀) ^ 2‖ + ‖(sm - s₀) ^ 2‖ := norm_sub_le _ _
      _ ≤ ‖zp + zm - 2 * z₀‖ + ‖(sp - s₀) ^ 2‖ + ‖(sm - s₀) ^ 2‖ := by
          linarith [norm_sub_le (zp + zm - 2 * z₀) ((sp - s₀) ^ 2)]
      _ = _ := by rw [norm_pow, norm_pow]
  nlinarith [norm_nonneg (sp + sm - 2 * s₀)]

theorem inv_sub_le {s₀ s₁ : ℂ} (h0 : 19 / 20 ≤ s₀.re) (h1 : 19 / 20 ≤ s₁.re) :
    ‖s₁⁻¹ - s₀⁻¹‖ ≤ 2 * ‖s₁ - s₀‖ := by
  have n0 := norm_ge_of_re h0
  have n1 := norm_ge_of_re h1
  have hne0 : s₀ ≠ 0 := by intro h; rw [h] at n0; simp at n0; linarith
  have hne1 : s₁ ≠ 0 := by intro h; rw [h] at n1; simp at n1; linarith
  have : s₁⁻¹ - s₀⁻¹ = (s₀ - s₁) / (s₁ * s₀) := by field_simp
  rw [this, norm_div, norm_mul, div_le_iff₀ (by positivity), norm_sub_rev]
  have : (1 : ℝ) / 2 ≤ ‖s₁‖ * ‖s₀‖ := by nlinarith
  nlinarith [norm_nonneg (s₁ - s₀)]

theorem inv_second_le {sp sm s₀ : ℂ} (h0 : 19 / 20 ≤ s₀.re) (hp : 19 / 20 ≤ sp.re)
    (hm : 19 / 20 ≤ sm.re) :
    ‖sp⁻¹ + sm⁻¹ - 2 * s₀⁻¹‖ ≤
      2 * ‖sp + sm - 2 * s₀‖ + 2 * (‖sp - s₀‖ ^ 2 + ‖sm - s₀‖ ^ 2) := by
  have n0 := norm_ge_of_re h0
  have np := norm_ge_of_re hp
  have nm := norm_ge_of_re hm
  have hne0 : s₀ ≠ 0 := by intro h; rw [h] at n0; simp at n0; linarith
  have hnep : sp ≠ 0 := by intro h; rw [h] at np; simp at np; linarith
  have hnem : sm ≠ 0 := by intro h; rw [h] at nm; simp at nm; linarith
  have hid : sp⁻¹ + sm⁻¹ - 2 * s₀⁻¹ = -(sp + sm - 2 * s₀) / s₀ ^ 2 +
      (sp - s₀) ^ 2 / (s₀ ^ 2 * sp) + (sm - s₀) ^ 2 / (s₀ ^ 2 * sm) := by
    field_simp; ring
  rw [hid]
  have b1 : ‖-(sp + sm - 2 * s₀) / s₀ ^ 2‖ ≤ 2 * ‖sp + sm - 2 * s₀‖ := by
    rw [norm_div, norm_neg, norm_pow, div_le_iff₀ (by positivity)]
    have : (1 : ℝ) / 2 ≤ ‖s₀‖ ^ 2 := by nlinarith
    nlinarith [norm_nonneg (sp + sm - 2 * s₀)]
  have b2 : ‖(sp - s₀) ^ 2 / (s₀ ^ 2 * sp)‖ ≤ 2 * ‖sp - s₀‖ ^ 2 := by
    rw [norm_div, norm_pow, norm_mul, norm_pow, div_le_iff₀ (by positivity)]
    have : (1 : ℝ) / 2 ≤ ‖s₀‖ ^ 2 * ‖sp‖ := by nlinarith [mul_nonneg (norm_nonneg s₀) (norm_nonneg sp)]
    nlinarith [sq_nonneg ‖sp - s₀‖]
  have b3 : ‖(sm - s₀) ^ 2 / (s₀ ^ 2 * sm)‖ ≤ 2 * ‖sm - s₀‖ ^ 2 := by
    rw [norm_div, norm_pow, norm_mul, norm_pow, div_le_iff₀ (by positivity)]
    have : (1 : ℝ) / 2 ≤ ‖s₀‖ ^ 2 * ‖sm‖ := by nlinarith [mul_nonneg (norm_nonneg s₀) (norm_nonneg sm)]
    nlinarith [sq_nonneg ‖sm - s₀‖]
  calc _ ≤ ‖-(sp + sm - 2 * s₀) / s₀ ^ 2 + (sp - s₀) ^ 2 / (s₀ ^ 2 * sp)‖ +
        ‖(sm - s₀) ^ 2 / (s₀ ^ 2 * sm)‖ := norm_add_le _ _
    _ ≤ ‖-(sp + sm - 2 * s₀) / s₀ ^ 2‖ + ‖(sp - s₀) ^ 2 / (s₀ ^ 2 * sp)‖ +
        ‖(sm - s₀) ^ 2 / (s₀ ^ 2 * sm)‖ := by
        linarith [norm_add_le (-(sp + sm - 2 * s₀) / s₀ ^ 2) ((sp - s₀) ^ 2 / (s₀ ^ 2 * sp))]
    _ ≤ _ := by linarith

theorem inv_second_final {z₀ zp zm s₀ sp sm : ℂ} {Zb t : ℝ} (h0 : 19 / 20 ≤ s₀.re)
    (hp : 19 / 20 ≤ sp.re) (hm : 19 / 20 ≤ sm.re) (hs0 : s₀ ^ 2 = z₀) (hsp : sp ^ 2 = zp)
    (hsm : sm ^ 2 = zm) (hZ : ‖zp + zm - 2 * z₀‖ ≤ Zb) (hap : ‖sp - s₀‖ ≤ t)
    (ham : ‖sm - s₀‖ ≤ t) :
    ‖sp⁻¹ + sm⁻¹ - 2 * s₀⁻¹‖ ≤ 2 * Zb + 8 * t ^ 2 := by
  have h1 := sqrt_second_le (sm := sm) h0 hs0 hsp hsm
  have h2 := inv_second_le h0 hp hm
  have q1 : ‖sp - s₀‖ ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hap 2
  have q2 : ‖sm - s₀‖ ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ (norm_nonneg _) ham 2
  linarith

end Scalar


section Vector

variable {N : ℕ}

/-- `F(v) = v / √(v ⬝ v)`. -/
noncomputable def normalize (v : Fin N → ℂ) : Fin N → ℂ := (sqrtDot v)⁻¹ • v

theorem dot_sub_add (a b : Fin N → ℂ) : (a - b) ⬝ᵥ (a + b) = a ⬝ᵥ a - b ⬝ᵥ b := by
  rw [sub_dotProduct, dotProduct_add, dotProduct_add, dotProduct_comm b a]; ring

theorem dot_second (v0 vp vm : Fin N → ℂ) :
    vp ⬝ᵥ vp + vm ⬝ᵥ vm - 2 * (v0 ⬝ᵥ v0) =
      2 * (v0 ⬝ᵥ (vp + vm - (2 : ℂ) • v0)) + (vp - v0) ⬝ᵥ (vp - v0) + (vm - v0) ⬝ᵥ (vm - v0) := by
  simp only [dotProduct, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem cNorm_dot_le (a b : Fin N → ℂ) : ‖a ⬝ᵥ b‖ ≤ cNorm a * cNorm b := norm_dotProduct_le a b

theorem sqrt_facts {ref v : Fin N → ℂ} {a : ℝ} (href : ref ⬝ᵥ ref = 1) (hrefn : cNorm ref ≤ 2)
    (ha0 : 0 ≤ a) (ha : a ≤ 1 / 100) (hv : cNorm (v - ref) ≤ a) :
    cNorm v ≤ 2 + a ∧ ‖v ⬝ᵥ v - 1‖ ≤ 5 * a ∧ ‖sqrtDot v - 1‖ ≤ 5 * a ∧
      19 / 20 ≤ (sqrtDot v).re := by
  have nv : cNorm v ≤ 2 + a := by
    have := cNorm_add_le (v - ref) ref; simp at this; linarith
  have hz : ‖v ⬝ᵥ v - 1‖ ≤ 5 * a := by
    have : v ⬝ᵥ v - 1 = (v - ref) ⬝ᵥ (v + ref) := by rw [dot_sub_add, href]
    rw [this]
    refine (cNorm_dot_le _ _).trans ?_
    have h2 : cNorm (v + ref) ≤ 4 + a := by
      have := cNorm_add_le v ref; linarith
    calc cNorm (v - ref) * cNorm (v + ref) ≤ a * (4 + a) :=
          mul_le_mul hv h2 (cNorm_nonneg _) ha0
      _ ≤ 5 * a := by nlinarith
  obtain ⟨h1, h2⟩ := sqrt_near_one (by linarith) (sqrtDot_sq v) (re_sqrtDot_nonneg v)
  exact ⟨nv, hz, h1.trans hz, h2⟩

/-- Bounds for the normalization of three nearby vectors. -/
theorem normalize_bounds {ref v0 vp vm : Fin N → ℂ} {a T1 T2 : ℝ} (href : ref ⬝ᵥ ref = 1)
    (hrefn : cNorm ref ≤ 2) (ha0 : 0 ≤ a) (ha : a ≤ 1 / 100)
    (h0 : cNorm (v0 - ref) ≤ a) (hp : cNorm (vp - ref) ≤ a) (hm : cNorm (vm - ref) ≤ a)
    (hT1p : cNorm (vp - v0) ≤ T1) (hT1m : cNorm (vm - v0) ≤ T1)
    (hT2 : cNorm (vp + vm - (2 : ℂ) • v0) ≤ T2) :
    normalize v0 ⬝ᵥ normalize v0 = 1 ∧ cNorm (normalize v0 - ref) ≤ 12 * a ∧
    cNorm (normalize vp - normalize v0) ≤ 22 * T1 ∧
    cNorm (normalize vm - normalize v0) ≤ 22 * T1 ∧
    cNorm (normalize vp + normalize vm - (2 : ℂ) • normalize v0) ≤ 22 * T2 + 440 * T1 ^ 2 := by
  have hT1 : 0 ≤ T1 := le_trans (cNorm_nonneg _) hT1p
  have hT2' : 0 ≤ T2 := le_trans (cNorm_nonneg _) hT2
  obtain ⟨nv0, z0, s0d, s0r⟩ := sqrt_facts href hrefn ha0 ha h0
  obtain ⟨nvp, zp, spd, spr⟩ := sqrt_facts href hrefn ha0 ha hp
  obtain ⟨nvm, zm, smd, smr⟩ := sqrt_facts href hrefn ha0 ha hm
  have ha5 : 5 * a ≤ 1 / 20 := by linarith
  set s0 := sqrtDot v0 with hs0
  set sp := sqrtDot vp with hsp
  set sm := sqrtDot vm with hsm
  have e0 : s0 ^ 2 = v0 ⬝ᵥ v0 := sqrtDot_sq v0
  have ep : sp ^ 2 = vp ⬝ᵥ vp := sqrtDot_sq vp
  have em : sm ^ 2 = vm ⬝ᵥ vm := sqrtDot_sq vm
  have ns0 := norm_ge_of_re s0r
  have hne0 : s0 ≠ 0 := by intro h; rw [h] at ns0; simp at ns0; linarith
  have hu0 : ‖s0⁻¹‖ ≤ 20 / 19 := by
    rw [norm_inv]; rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  have hunit : ∀ (sj : ℂ), 19 / 20 ≤ sj.re → ‖sj⁻¹‖ ≤ 20 / 19 := by
    intro sj hj
    have := norm_ge_of_re hj
    rw [norm_inv]; rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  -- first differences of the pieces
  have zdiff : ∀ v : Fin N → ℂ, cNorm v ≤ 2 + a → cNorm (v - v0) ≤ T1 →
      ‖v ⬝ᵥ v - v0 ⬝ᵥ v0‖ ≤ 5 * T1 := by
    intro v hv hT
    rw [← dot_sub_add]
    refine (cNorm_dot_le _ _).trans ?_
    have : cNorm (v + v0) ≤ 4 + 2 * a := by
      have := cNorm_add_le v v0; linarith
    calc cNorm (v - v0) * cNorm (v + v0) ≤ T1 * (4 + 2 * a) :=
          mul_le_mul hT this (cNorm_nonneg _) hT1
      _ ≤ 5 * T1 := by nlinarith
  have sdiff : ∀ v : Fin N → ℂ, cNorm v ≤ 2 + a → cNorm (v - v0) ≤ T1 →
      19 / 20 ≤ (sqrtDot v).re → ‖sqrtDot v - s0‖ ≤ 5 * T1 := by
    intro v hv hT hr
    exact (sqrt_sub_le s0r hr (sqrtDot_sq v0) (sqrtDot_sq v)).trans
      (zdiff v hv hT)
  have wdiff : ∀ v : Fin N → ℂ, cNorm v ≤ 2 + a → cNorm (v - v0) ≤ T1 →
      19 / 20 ≤ (sqrtDot v).re → cNorm (normalize v - normalize v0) ≤ 22 * T1 := by
    intro v hv hT hr
    have hud : ‖(sqrtDot v)⁻¹ - s0⁻¹‖ ≤ 10 * T1 := by
      have := inv_sub_le s0r hr
      linarith [sdiff v hv hT hr]
    have e : normalize v - normalize v0 =
        (sqrtDot v)⁻¹ • (v - v0) + ((sqrtDot v)⁻¹ - s0⁻¹) • v0 := by
      unfold normalize; funext i; simp [Pi.sub_apply, Pi.smul_apply]; ring
    rw [e]
    have b1 : cNorm ((sqrtDot v)⁻¹ • (v - v0)) ≤ 20 / 19 * T1 := by
      rw [cNorm_smul]; exact mul_le_mul (hunit _ hr) hT (cNorm_nonneg _) (by norm_num)
    have b2 : cNorm (((sqrtDot v)⁻¹ - s0⁻¹) • v0) ≤ 10 * T1 * (2 + a) := by
      rw [cNorm_smul]; exact mul_le_mul hud nv0 (cNorm_nonneg _) (by positivity)
    refine (cNorm_add_le _ _).trans ?_
    nlinarith
  refine ⟨?_, ?_, wdiff vp nvp hT1p spr, wdiff vm nvm hT1m smr, ?_⟩
  · have hdot0 : v0 ⬝ᵥ v0 ≠ 0 := by
      intro h; rw [h] at e0
      have : s0 = 0 := by simpa using e0
      exact hne0 this
    unfold normalize
    rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← hs0]
    have : s0 ^ 2 = v0 ⬝ᵥ v0 := e0
    field_simp
    rw [this]
  · have e : normalize v0 - ref = s0⁻¹ • (v0 - ref) + (s0⁻¹ - 1) • ref := by
      unfold normalize; funext i; simp [Pi.sub_apply, Pi.smul_apply]; ring
    rw [e]
    have b1 : cNorm (s0⁻¹ • (v0 - ref)) ≤ 20 / 19 * a := by
      rw [cNorm_smul]; exact mul_le_mul hu0 h0 (cNorm_nonneg _) (by norm_num)
    have b2 : ‖s0⁻¹ - 1‖ ≤ 20 / 19 * (5 * a) := by
      have : s0⁻¹ - 1 = (1 - s0) / s0 := by field_simp
      rw [this, norm_div, div_le_iff₀ (by linarith), norm_sub_rev]
      nlinarith
    have b3 : cNorm ((s0⁻¹ - 1) • ref) ≤ 20 / 19 * (5 * a) * 2 := by
      rw [cNorm_smul]; exact mul_le_mul b2 hrefn (cNorm_nonneg _) (by positivity)
    refine (cNorm_add_le _ _).trans ?_
    linarith
  · -- second difference
    have ap := sdiff vp nvp hT1p spr
    have am := sdiff vm nvm hT1m smr
    have hΔz : ‖vp ⬝ᵥ vp + vm ⬝ᵥ vm - 2 * (v0 ⬝ᵥ v0)‖ ≤ 5 * T2 + 2 * T1 ^ 2 := by
      rw [dot_second]
      have n2 : ‖(2 : ℂ)‖ = 2 := by simp
      have t1 : ‖2 * (v0 ⬝ᵥ (vp + vm - (2 : ℂ) • v0))‖ ≤ 2 * ((2 + a) * T2) := by
        rw [norm_mul, n2]
        exact mul_le_mul_of_nonneg_left ((cNorm_dot_le _ _).trans
          (mul_le_mul nv0 hT2 (cNorm_nonneg _) (by positivity))) (by norm_num)
      have t2 : ‖(vp - v0) ⬝ᵥ (vp - v0)‖ ≤ T1 ^ 2 :=
        (cNorm_dot_le _ _).trans (by
          have := mul_le_mul hT1p hT1p (cNorm_nonneg _) hT1; linarith [sq T1])
      have t3 : ‖(vm - v0) ⬝ᵥ (vm - v0)‖ ≤ T1 ^ 2 :=
        (cNorm_dot_le _ _).trans (by
          have := mul_le_mul hT1m hT1m (cNorm_nonneg _) hT1; linarith [sq T1])
      have t4 := norm_add_le (2 * (v0 ⬝ᵥ (vp + vm - (2 : ℂ) • v0))) ((vp - v0) ⬝ᵥ (vp - v0))
      have t5 := norm_add_le (2 * (v0 ⬝ᵥ (vp + vm - (2 : ℂ) • v0)) + (vp - v0) ⬝ᵥ (vp - v0))
        ((vm - v0) ⬝ᵥ (vm - v0))
      have t6 : (2 + a) * T2 ≤ 2.01 * T2 := by nlinarith
      linarith
    have hΔu := inv_second_final s0r spr smr e0 ep em hΔz ap am
    have hudp : ‖sp⁻¹ - s0⁻¹‖ ≤ 10 * T1 := by
      have := inv_sub_le s0r spr; linarith
    have hudm : ‖sm⁻¹ - s0⁻¹‖ ≤ 10 * T1 := by
      have := inv_sub_le s0r smr; linarith
    have e : normalize vp + normalize vm - (2 : ℂ) • normalize v0 =
        (sp⁻¹ + sm⁻¹ - 2 * s0⁻¹) • v0 + s0⁻¹ • (vp + vm - (2 : ℂ) • v0) +
        (sp⁻¹ - s0⁻¹) • (vp - v0) + (sm⁻¹ - s0⁻¹) • (vm - v0) := by
      unfold normalize; funext i; simp [Pi.sub_apply, Pi.smul_apply]; ring
    rw [e]
    have hUb : 2 * (5 * T2 + 2 * T1 ^ 2) + 8 * (5 * T1) ^ 2 = 10 * T2 + 204 * T1 ^ 2 := by ring
    rw [hUb] at hΔu
    have c1 : cNorm ((sp⁻¹ + sm⁻¹ - 2 * s0⁻¹) • v0) ≤ (10 * T2 + 204 * T1 ^ 2) * (2 + a) := by
      rw [cNorm_smul]; exact mul_le_mul hΔu nv0 (cNorm_nonneg _) (by positivity)
    have c2 : cNorm (s0⁻¹ • (vp + vm - (2 : ℂ) • v0)) ≤ 20 / 19 * T2 := by
      rw [cNorm_smul]; exact mul_le_mul hu0 hT2 (cNorm_nonneg _) (by norm_num)
    have c3 : cNorm ((sp⁻¹ - s0⁻¹) • (vp - v0)) ≤ 10 * T1 * T1 := by
      rw [cNorm_smul]; exact mul_le_mul hudp hT1p (cNorm_nonneg _) (by positivity)
    have c4 : cNorm ((sm⁻¹ - s0⁻¹) • (vm - v0)) ≤ 10 * T1 * T1 := by
      rw [cNorm_smul]; exact mul_le_mul hudm hT1m (cNorm_nonneg _) (by positivity)
    have d1 := cNorm_add_le ((sp⁻¹ + sm⁻¹ - 2 * s0⁻¹) • v0 + s0⁻¹ • (vp + vm - (2 : ℂ) • v0)
      + (sp⁻¹ - s0⁻¹) • (vp - v0)) ((sm⁻¹ - s0⁻¹) • (vm - v0))
    have d2 := cNorm_add_le ((sp⁻¹ + sm⁻¹ - 2 * s0⁻¹) • v0 + s0⁻¹ • (vp + vm - (2 : ℂ) • v0))
      ((sp⁻¹ - s0⁻¹) • (vp - v0))
    have d3 := cNorm_add_le ((sp⁻¹ + sm⁻¹ - 2 * s0⁻¹) • v0) (s0⁻¹ • (vp + vm - (2 : ℂ) • v0))
    have f1 : (10 * T2 + 204 * T1 ^ 2) * (2 + a) ≤ (10 * T2 + 204 * T1 ^ 2) * 2.01 :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have f2 : T1 * T1 = T1 ^ 2 := by ring
    have hT1sq : 0 ≤ T1 ^ 2 := by positivity
    linarith

end Vector

end Balaban.Background
