module

public import Balaban.LargeField.Counter.LamBounds
public import Balaban.LargeField.Counter.Conditions
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr

/-!
# Existence of `λ_*` (Part I, §I.5.3)

`exists_lamStar`: for typing data satisfying `(K)` there is `x₀ ≥ 1` with (Λ0)–(Λ11) for all
`x ≥ x₀`.  Each condition compares a function with a faster-growing one (a power of `x` of larger
degree, or `L^x`), so it holds eventually; the finitely many thresholds are combined.
-/

@[expose] public section

open Filter

namespace Balaban.LargeField

open Asymp

theorem ev_l0_a (T : Typing) : ∀ᶠ x in atTop, 4 * T.cStar * T.θp ≤ x :=
  eventually_ge_atTop _

section

variable {T : Typing} (hT : T.Ok)

include hT

theorem polyB_CE_pow (m : ℕ) (hm : 2 * T.d + 1 ≤ m) :
    PolyB (fun x => T.CE * x ^ (2 * T.d + 1) + 1) m := by
  have hCE := hT.dummy_ok.CE_nonneg
  refine ⟨T.CE + 1, by positivity, fun x hx => ?_⟩
  have h1 : x ^ (2 * T.d + 1) ≤ x ^ m := pow_le_pow_right₀ hx hm
  have h2 : (1 : ℝ) ≤ x ^ m := one_le_pow₀ hx
  show T.CE * x ^ (2 * T.d + 1) + 1 ≤ (T.CE + 1) * x ^ m
  nlinarith

theorem ev_l0_d : ∀ᶠ x in atTop, T.CE * x ^ (2 * T.d + 1) + 1 ≤ 2 * T.A2 * x ^ T.p2 :=
  ev_polyB_le (polyB_CE_pow hT _ le_rfl) (by have := hT.p2_ge; omega)
    (by have := hT.A2_pos; positivity)

theorem ev_l0_e : ∀ᶠ x in atTop,
    T.CE * x ^ (2 * T.d + 1) + 1 ≤ 1 / 2 * T.A3 * (x / 2) ^ (2 * T.p0) := by
  have hA3 := hT.A3_pos
  have h := ev_polyB_le (polyB_CE_pow hT _ le_rfl) (p := 2 * T.p0)
    (by have := hT.p2_ge; have := hT.p0_gt; omega) (c := 1 / 2 * T.A3 / 2 ^ (2 * T.p0))
    (by positivity)
  filter_upwards [h] with x hx
  calc _ ≤ _ := hx
    _ = _ := by rw [div_pow]; ring

theorem ev_l0_b : ∀ᶠ x in atTop, T.θp * (T.hBar x + 2) ≤ x / (4 * T.cStar) := by
  have hcs := hT.dummy_ok.cStar_ge_one
  have hθ := hT.dummy_ok.θp_pos
  have h := ev_logB_le (((lb_hBar hT).add_const 2).const_mul (c := T.θp) hθ.le)
    (c := 1 / (4 * T.cStar)) (by positivity)
  filter_upwards [h] with x hx
  calc _ ≤ _ := hx
    _ = _ := by ring

theorem ev_l0_c : ∀ᶠ x in atTop, T.n2Bar x ≤ x / (T.α * T.logL) := by
  have h := ev_logB_le (lb_n2Bar hT) (c := 1 / (T.α * T.logL))
    (by have := hT.dummy_ok.αlogL_pos; positivity)
  filter_upwards [h] with x hx
  calc _ ≤ _ := hx
    _ = _ := by ring

theorem ev_l1_a : ∀ᶠ x in atTop,
    T.θp * (2 + Real.logb T.L (T.nuBar x * T.Dbar x)) ≤ x := by
  have hθ := hT.dummy_ok.θp_pos
  have h := ev_logB_le (((logB_const 2).add (lb_logb_nuD hT)).const_mul (c := T.θp) hθ.le)
    (c := 1) one_pos
  filter_upwards [h] with x hx
  calc _ ≤ _ := hx
    _ = _ := by ring

theorem ev_l1_b : ∀ᶠ x in atTop,
    1 + Real.logb T.L (T.nuBar x * T.Dbar x) + T.n2Bar (2 * x) ≤ x / (T.α * T.logL) := by
  have h := ev_logB_le (((logB_const 1).add (lb_logb_nuD hT)).add (lb_n2Bar_two hT))
    (c := 1 / (T.α * T.logL)) (by have := hT.dummy_ok.αlogL_pos; positivity)
  filter_upwards [h] with x hx
  calc _ ≤ _ := hx
    _ = _ := by ring

theorem Abar_nonneg {y : ℝ} (hy : 0 ≤ y) : 0 ≤ T.Abar y := by
  have := hT.A2_pos
  have := hT.dummy_ok.θp_pos
  have := hT.dummy_ok.Cw_nonneg
  unfold Typing.Abar; positivity

theorem one_le_cPrime : 1 ≤ T.cPrime := by
  have h1 := hT.dummy_ok.cStar_ge_one
  have h2 := hT.dummy_ok.θp_pos
  unfold Typing.cPrime
  nlinarith

theorem pb_Phi_one : PolyB (fun x => T.Phi x + 1) T.p2 :=
  (pb_Phi hT).add (polyB_const zero_le_one _)

theorem Phi_nonneg' {x : ℝ} (hx : 0 ≤ x) : 0 ≤ T.Phi x := by
  have hc := cPrime_nonneg hT
  have hCt := Ct_nonneg hT
  have hCw := hT.dummy_ok.Cw_nonneg
  have := hT.A2_pos
  unfold Typing.Phi; positivity

theorem ev_l2 : ∀ᶠ x in atTop,
    T.CE * x ^ (2 * T.d + 1) + T.Phi x + 1 ≤ 1 / 2 * T.A3 * (x / 2) ^ (2 * T.p0) := by
  have hA3 := hT.A3_pos
  have hCE := hT.dummy_ok.CE_nonneg
  have hp2 := hT.p2_ge
  have hf : PolyB (fun x => T.CE * x ^ (2 * T.d + 1) + T.Phi x + 1) T.p2 := by
    have h1 : PolyB (fun x => T.CE * x ^ (2 * T.d + 1)) T.p2 :=
      (polyB_pow_const T.CE hCE _).mono (by omega)
    exact (h1.add (pb_Phi hT)).add (polyB_const zero_le_one _)
  have h := ev_polyB_le hf (p := 2 * T.p0) (by have := hT.p0_gt; omega)
    (c := 1 / 2 * T.A3 / 2 ^ (2 * T.p0)) (by positivity)
  filter_upwards [h] with x hx
  calc _ ≤ _ := hx
    _ = _ := by rw [div_pow]; ring

theorem rpow_L (x : ℝ) : (T.L : ℝ) ^ x = Real.exp (T.logL * x) :=
  Real.rpow_def_of_pos (by have := hT.dummy_ok.cast_L_ge; linarith) x

theorem ev_l3 : ∀ᶠ x in atTop, T.Phi x + 1 ≤ 1 / 2 * (T.L : ℝ) ^ x := by
  have h := ev_polyB_le_exp (pb_Phi_one hT) (a := T.logL) (c := 1 / 2)
    (hT.dummy_ok.logL_pos) (by norm_num)
  filter_upwards [h] with x hx
  rw [rpow_L hT]; exact hx

theorem pb_two_mul_Dbar : PolyB (fun x => 2 * T.Dbar x) 2 := (pb_Dbar hT).const_mul (by norm_num)

theorem ev_l4 : ∀ᶠ x in atTop, T.Phi x + 1 ≤ (T.L : ℝ) ^ x / (2 * T.Dbar x) := by
  have hg0 : ∀ x : ℝ, 1 ≤ x → 0 ≤ 2 * T.Dbar x := fun x hx => by
    have := nonneg_Dbar hT x hx; linarith
  have hf := (pb_Phi_one hT).mul (pb_two_mul_Dbar hT) hg0
  have h := ev_polyB_le_exp hf (a := T.logL) (c := 1) (hT.dummy_ok.logL_pos) one_pos
  filter_upwards [h, eventually_ge_atTop (1 : ℝ)] with x hx hx1
  have hD := hT.dummy_ok.one_le_Dbar x
  rw [le_div_iff₀ (by linarith)]
  rw [rpow_L hT]
  simpa using hx

theorem ev_l5_a : ∀ᶠ x in atTop,
    T.DeltaBar x * T.Abar (3 * T.cStar * x) ≤ 1 / 2 * T.A2 * x ^ T.p2 := by
  have hcs := hT.dummy_ok.cStar_ge_one
  have hf := pb_Abar hT (a := 3 * T.cStar) (by linarith)
  have h := ev_polyB_mul_logB_le hf (lb_DeltaBar hT) (nonneg_DeltaBar hT)
    (fun x hx => Abar_nonneg hT (by positivity)) (p := T.p2)
    (by have := hT.p2_ge; omega) (c := 1 / 2 * T.A2) (by have := hT.A2_pos; positivity)
  filter_upwards [h] with x hx
  calc _ = T.Abar (3 * T.cStar * x) * T.DeltaBar x := mul_comm _ _
    _ ≤ _ := hx

theorem ev_l5_b : ∀ᶠ x in atTop, T.CE * x ^ (2 * T.d + 1) ≤ 1 / 2 * T.A2 * x ^ T.p2 := by
  have hCE := hT.dummy_ok.CE_nonneg
  exact ev_polyB_le (polyB_pow_const T.CE hCE _) (by have := hT.p2_ge; omega)
    (by have := hT.A2_pos; positivity)

theorem ev_l6 : ∀ᶠ x in atTop,
    (T.cStar * (T.hBar x + 1) + 1) * T.Abar (3 * T.cStar * x) ≤ T.A2 * (x / (4 * T.cStar)) ^ T.p2 := by
  have hcs := hT.dummy_ok.cStar_ge_one
  have hf := pb_Abar hT (a := 3 * T.cStar) (by linarith)
  have hg : LogB (fun x => T.cStar * (T.hBar x + 1) + 1) :=
    (((lb_hBar hT).add_const 1).const_mul (c := T.cStar) (by linarith)).add_const 1
  have hg0 : ∀ x : ℝ, 1 ≤ x → 0 ≤ T.cStar * (T.hBar x + 1) + 1 := fun x hx => by
    have := nonneg_hBar hT x hx; positivity
  have h := ev_polyB_mul_logB_le hf hg hg0 (fun x hx => Abar_nonneg hT (by positivity))
    (p := T.p2) (by have := hT.p2_ge; omega) (c := T.A2 / (4 * T.cStar) ^ T.p2)
    (by have := hT.A2_pos; positivity)
  filter_upwards [h] with x hx
  calc _ = T.Abar (3 * T.cStar * x) * (T.cStar * (T.hBar x + 1) + 1) := mul_comm _ _
    _ ≤ _ := hx
    _ = _ := by rw [div_pow]; ring

theorem ev_l7 : ∀ᶠ x in atTop,
    (T.Gbar x + 2 * T.cStar) * T.Abar (T.cPrime * x) + T.CE * x ^ (2 * T.d + 1) ≤
      2 * T.A2 * x ^ T.p2 := by
  have hcs := hT.dummy_ok.cStar_ge_one
  have hf := pb_Abar hT (a := T.cPrime) (one_le_cPrime hT)
  have hg : LogB (fun x => T.Gbar x + 2 * T.cStar) := (lb_Gbar hT).add_const _
  have hg0 : ∀ x : ℝ, 1 ≤ x → 0 ≤ T.Gbar x + 2 * T.cStar := fun x hx => by
    have := nonneg_Gbar hT x hx; linarith
  have hA2 := hT.A2_pos
  have h1 := ev_polyB_mul_logB_le hf hg hg0
    (fun x hx => Abar_nonneg hT (by have := one_le_cPrime hT; positivity))
    (p := T.p2) (by have := hT.p2_ge; omega) (c := T.A2) hA2
  have h2 : ∀ᶠ x in atTop, T.CE * x ^ (2 * T.d + 1) ≤ T.A2 * x ^ T.p2 :=
    ev_polyB_le (polyB_pow_const T.CE hT.dummy_ok.CE_nonneg _)
      (by have := hT.p2_ge; omega) hA2
  filter_upwards [h1, h2] with x hx1 hx2
  calc _ = T.Abar (T.cPrime * x) * (T.Gbar x + 2 * T.cStar) + T.CE * x ^ (2 * T.d + 1) := by ring
    _ ≤ T.A2 * x ^ T.p2 + T.A2 * x ^ T.p2 := add_le_add hx1 hx2
    _ = _ := by ring

theorem ev_l8_a : ∀ᶠ x in atTop, T.Phi x ≤ (T.L : ℝ) ^ (x / 2 - 1) := by
  have hL := hT.dummy_ok.cast_L_ge
  have hlogL := hT.dummy_ok.logL_pos
  have h := ev_polyB_le_exp (pb_Phi hT) (a := T.logL / 2) (c := (T.L : ℝ)⁻¹)
    (by positivity) (by positivity)
  filter_upwards [h] with x hx
  rw [rpow_L hT]
  have e : T.logL * (x / 2 - 1) = T.logL / 2 * x + (-T.logL) := by ring
  rw [e, Real.exp_add, Real.exp_neg]
  have : Real.exp T.logL = T.L := Real.exp_log (by linarith)
  rw [this]
  calc _ ≤ _ := hx
    _ = _ := by ring

theorem ev_l8_b : ∀ᶠ x in atTop,
    T.Phi x ≤ (T.L : ℝ) ^ (x / 2) / (2 * (1 + T.Dbar x)) := by
  have hg0 : ∀ x : ℝ, 1 ≤ x → 0 ≤ 2 * (1 + T.Dbar x) := fun x hx => by
    have := nonneg_Dbar hT x hx; linarith
  have hg : PolyB (fun x => 2 * (1 + T.Dbar x)) 2 :=
    (((polyB_const zero_le_one 2).add (pb_Dbar hT)).const_mul (c := 2) (by norm_num)).congr'
      (fun x => by simp)
  have hf := (pb_Phi hT).mul hg hg0
  have h := ev_polyB_le_exp hf (a := T.logL / 2) (c := 1) (by have := hT.dummy_ok.logL_pos; positivity)
    one_pos
  filter_upwards [h, eventually_ge_atTop (1 : ℝ)] with x hx hx1
  have hD := hT.dummy_ok.one_le_Dbar x
  rw [le_div_iff₀ (by linarith)]
  rw [rpow_L hT]
  have e : T.logL * (x / 2) = T.logL / 2 * x := by ring
  rw [e]
  simpa using hx

theorem ev_l9 : ∀ᶠ x in atTop, T.Phi x ≤ T.Cν * x ^ T.p2 := by
  have hc := cPrime_nonneg hT
  have hCt := Ct_nonneg hT
  have hCw := hT.dummy_ok.Cw_nonneg
  have hA2 := hT.A2_pos
  have hp2 := hT.p2_ge
  have h := ev_polyB_le (polyB_pow_const (T.Ct * T.Cw * T.cPrime ^ (2 * T.d + 1))
    (by positivity) (2 * T.d + 2)) (p := T.p2) (by omega) (c := 1) one_pos
  filter_upwards [h, eventually_ge_atTop (1 : ℝ)] with x hx hx1
  have hxp : 0 ≤ x ^ T.p2 := by positivity
  unfold Typing.Phi
  have e : (T.cPrime * x) ^ T.p2 = T.cPrime ^ T.p2 * x ^ T.p2 := mul_pow _ _ _
  rw [e]
  have hCr := hT.Cr_le
  unfold Typing.Cr at hCr
  nlinarith

theorem ev_l10 : ∀ᶠ x in atTop,
    T.CR * x ^ (2 * T.d + 1) + 2 * T.A2 * (T.cDPrime * x) ^ T.p2 +
      (x / (T.α * T.logL) + 1) * T.Cw * (T.cDPrime * x) ^ (2 * T.d + 1) + 1 ≤
      T.A3' * x ^ T.pR := by
  have hS := hT.dummy_ok
  have hA2 := hT.A2_pos
  have hCR := hT.CR_nonneg
  have hCw := hS.Cw_nonneg
  have hαL := hS.αlogL_pos
  have hp2 := hT.p2_ge
  have hcc : 0 ≤ T.cDPrime := by
    have := hS.cStar_ge_one; have := hS.θp_pos
    unfold Typing.cDPrime; linarith
  have hf : PolyB (fun x => T.CR * x ^ (2 * T.d + 1) + 2 * T.A2 * (T.cDPrime * x) ^ T.p2 +
      (x / (T.α * T.logL) + 1) * T.Cw * (T.cDPrime * x) ^ (2 * T.d + 1) + 1) T.p2 := by
    refine ⟨T.CR + 2 * T.A2 * T.cDPrime ^ T.p2 +
      (1 / (T.α * T.logL) + 1) * T.Cw * T.cDPrime ^ (2 * T.d + 1) + 1, by positivity,
      fun x hx => ?_⟩
    have h1 : x ^ (2 * T.d + 1) ≤ x ^ T.p2 := pow_le_pow_right₀ hx (by omega)
    have h2 : x ^ (2 * T.d + 2) ≤ x ^ T.p2 := pow_le_pow_right₀ hx (by omega)
    have h3 : (1 : ℝ) ≤ x ^ T.p2 := one_le_pow₀ hx
    have e1 : (T.cDPrime * x) ^ T.p2 = T.cDPrime ^ T.p2 * x ^ T.p2 := mul_pow _ _ _
    have e2 : (T.cDPrime * x) ^ (2 * T.d + 1) = T.cDPrime ^ (2 * T.d + 1) * x ^ (2 * T.d + 1) :=
      mul_pow _ _ _
    have e3 : (x / (T.α * T.logL) + 1) * x ^ (2 * T.d + 1) ≤
        (1 / (T.α * T.logL) + 1) * x ^ T.p2 := by
      have : x * x ^ (2 * T.d + 1) = x ^ (2 * T.d + 2) := by ring
      calc (x / (T.α * T.logL) + 1) * x ^ (2 * T.d + 1)
          = (1 / (T.α * T.logL)) * (x * x ^ (2 * T.d + 1)) + x ^ (2 * T.d + 1) := by ring
        _ = (1 / (T.α * T.logL)) * x ^ (2 * T.d + 2) + x ^ (2 * T.d + 1) := by rw [this]
        _ ≤ (1 / (T.α * T.logL)) * x ^ T.p2 + x ^ T.p2 := by
            have : 0 ≤ 1 / (T.α * T.logL) := by positivity
            gcongr
        _ = _ := by ring
    show T.CR * x ^ (2 * T.d + 1) + 2 * T.A2 * (T.cDPrime * x) ^ T.p2 +
      (x / (T.α * T.logL) + 1) * T.Cw * (T.cDPrime * x) ^ (2 * T.d + 1) + 1 ≤ _
    rw [e1, e2]
    have h4 : (x / (T.α * T.logL) + 1) * T.Cw * (T.cDPrime ^ (2 * T.d + 1) * x ^ (2 * T.d + 1)) =
        T.Cw * T.cDPrime ^ (2 * T.d + 1) * ((x / (T.α * T.logL) + 1) * x ^ (2 * T.d + 1)) := by
      ring
    rw [h4]
    have h5 : T.Cw * T.cDPrime ^ (2 * T.d + 1) * ((x / (T.α * T.logL) + 1) * x ^ (2 * T.d + 1)) ≤
        T.Cw * T.cDPrime ^ (2 * T.d + 1) * ((1 / (T.α * T.logL) + 1) * x ^ T.p2) := by
      apply mul_le_mul_of_nonneg_left e3; positivity
    have h6 : T.CR * x ^ (2 * T.d + 1) ≤ T.CR * x ^ T.p2 := by gcongr
    nlinarith
  exact ev_polyB_le hf (p := T.pR) (by have := hT.pR_gt; omega) (c := T.A3')
    hT.A3'_pos

theorem ev_l11_a : ∀ᶠ x in atTop, T.cH ≤ T.d / 2 * x := by
  have hd : (3 : ℝ) ≤ T.d := by exact_mod_cast hT.three_le_d
  filter_upwards [eventually_ge_atTop (2 * T.cH / T.d)] with x hx
  have hd0 : (0 : ℝ) < T.d := by linarith
  rw [div_le_iff₀ hd0] at hx
  nlinarith

theorem ev_l11_b : ∀ᶠ x in atTop,
    x * T.Cw * (T.d * x) ^ (2 * T.d + 1) ≤ T.A2 * x ^ T.p2 := by
  have hCw := hT.dummy_ok.Cw_nonneg
  have hA2 := hT.A2_pos
  have hf : PolyB (fun x => x * T.Cw * (T.d * x) ^ (2 * T.d + 1)) (2 * T.d + 2) :=
    (polyB_pow_const (T.Cw * (T.d : ℝ) ^ (2 * T.d + 1)) (by positivity) (2 * T.d + 2)).congr'
      (fun x => by rw [mul_pow]; ring)
  exact ev_polyB_le hf (by have := hT.p2_ge; omega) hA2

theorem ev_l11_c : ∀ᶠ x in atTop, T.CE * (T.d * x) ^ (2 * T.d + 1) ≤ T.A2 * x ^ T.p2 := by
  have hCE := hT.dummy_ok.CE_nonneg
  have hA2 := hT.A2_pos
  have hf : PolyB (fun x => T.CE * (T.d * x) ^ (2 * T.d + 1)) (2 * T.d + 1) :=
    (polyB_pow_const (T.CE * (T.d : ℝ) ^ (2 * T.d + 1)) (by positivity) (2 * T.d + 1)).congr'
      (fun x => by rw [mul_pow]; ring)
  exact ev_polyB_le hf (by have := hT.p2_ge; omega) hA2

theorem ev_l11_d : ∀ᶠ x in atTop,
    T.A2 * x ^ T.p2 + x * T.Cw * (T.d * x) ^ (2 * T.d + 1) + T.CE * (T.d * x) ^ (2 * T.d + 1) ≤
      1 / 2 * T.A3 * x ^ (2 * T.p0) := by
  have hCw := hT.dummy_ok.Cw_nonneg
  have hCE := hT.dummy_ok.CE_nonneg
  have hA2 := hT.A2_pos
  have hp2 := hT.p2_ge
  have h1 : PolyB (fun x => x * T.Cw * (T.d * x) ^ (2 * T.d + 1)) T.p2 :=
    ((polyB_pow_const (T.Cw * (T.d : ℝ) ^ (2 * T.d + 1)) (by positivity) (2 * T.d + 2)).congr'
      (fun x => by rw [mul_pow]; ring)).mono (by omega)
  have h2 : PolyB (fun x => T.CE * (T.d * x) ^ (2 * T.d + 1)) T.p2 :=
    ((polyB_pow_const (T.CE * (T.d : ℝ) ^ (2 * T.d + 1)) (by positivity) (2 * T.d + 1)).congr'
      (fun x => by rw [mul_pow]; ring)).mono (by omega)
  have hf := ((polyB_pow_const T.A2 hA2.le T.p2).add h1).add h2
  exact ev_polyB_le hf (by have := hT.p0_gt; omega) (by have := hT.A3_pos; positivity)

end


/-- **Existence of `λ_*`** (Part I, §I.5.3): (Λ0)–(Λ11) hold for all `x ≥ x₀`, for some `x₀ ≥ 1`. -/
theorem exists_lamStar (T : Typing) (hT : T.Ok) : ∃ x₀ : ℝ, LamStarConditions T x₀ := by
  have hall := ((ev_l0_a T).and ((ev_l0_b hT).and ((ev_l0_c hT).and ((ev_l0_d hT).and ((ev_l0_e hT).and ((ev_l1_a hT).and ((ev_l1_b hT).and ((ev_l2 hT).and ((ev_l3 hT).and ((ev_l4 hT).and ((ev_l5_a hT).and ((ev_l5_b hT).and ((ev_l6 hT).and ((ev_l7 hT).and ((ev_l8_a hT).and ((ev_l8_b hT).and ((ev_l9 hT).and ((ev_l10 hT).and ((ev_l11_a hT).and ((ev_l11_b hT).and ((ev_l11_c hT).and (ev_l11_d hT))))))))))))))))))))))
  obtain ⟨x1, hx1⟩ := Filter.eventually_atTop.mp hall
  refine ⟨max x1 1, le_max_right _ _, (fun x hx => (hx1 x (le_trans (le_max_left _ _) hx)).1), (fun x hx => (hx1 x (le_trans (le_max_left _ _) hx)).2.1), (fun x hx => (hx1 x (le_trans (le_max_left _ _) hx)).2.2.1), (fun x hx => (hx1 x (le_trans (le_max_left _ _) hx)).2.2.2.1), (fun x hx => (hx1 x (le_trans (le_max_left _ _) hx)).2.2.2.2.1), (fun x hx => (hx1 x (le_trans (le_max_left _ _) hx)).2.2.2.2.2.1), (fun x hx => (hx1 x (le_trans (le_max_left _ _) hx)).2.2.2.2.2.2.1), (fun x hx => (hx1 x (le_trans (le_max_left _ _) hx)).2.2.2.2.2.2.2.1), (fun x hx => (hx1 x (le_trans (le_max_left _ _) hx)).2.2.2.2.2.2.2.2.1), (fun x hx => (hx1 x (le_trans (le_max_left _ _) hx)).2.2.2.2.2.2.2.2.2.1), (fun x hx => (hx1 x (le_trans (le_max_left _ _) hx)).2.2.2.2.2.2.2.2.2.2.1), (fun x hx => (hx1 x (le_trans (le_max_left _ _) hx)).2.2.2.2.2.2.2.2.2.2.2.1), (fun x hx => (hx1 x (le_trans (le_max_left _ _) hx)).2.2.2.2.2.2.2.2.2.2.2.2.1), (fun x hx => (hx1 x (le_trans (le_max_left _ _) hx)).2.2.2.2.2.2.2.2.2.2.2.2.2.1), (fun x hx => (hx1 x (le_trans (le_max_left _ _) hx)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), (fun x hx => (hx1 x (le_trans (le_max_left _ _) hx)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), (fun x hx => (hx1 x (le_trans (le_max_left _ _) hx)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), (fun x hx => (hx1 x (le_trans (le_max_left _ _) hx)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), (fun x hx => (hx1 x (le_trans (le_max_left _ _) hx)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), (fun x hx => (hx1 x (le_trans (le_max_left _ _) hx)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), (fun x hx => (hx1 x (le_trans (le_max_left _ _) hx)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), (fun x hx => (hx1 x (le_trans (le_max_left _ _) hx)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2)⟩

end Balaban.LargeField
