module

public import Balaban.LargeField.Counter.Asymp
public import Balaban.LargeField.Counter.Bars
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr

/-!
# Growth bounds for the auxiliary functions of §I.5.2
-/

@[expose] public section

open Filter

namespace Balaban.LargeField

open Asymp

/-- A setting with the given typing data and `λ_j = max {1, θ₊} + j θ₋` (used only to reuse the
lemmas about the auxiliary functions, which depend on the typing data alone). -/
abbrev Typing.dummy (T : Typing) : Setting :=
  { toTyping := T, lam := fun j => max 1 T.θp + j * T.θm }

theorem Typing.Ok.dummy_ok {T : Typing} (hT : T.Ok) : T.dummy.Ok where
  toOk := hT
  lam_step := fun j => by
    simp only [Nat.cast_add, Nat.cast_one]
    constructor <;> nlinarith [hT.θm_le_θp]
  one_le_lam0 := by simp
  θp_le_lam0 := by simp

namespace Asymp

theorem PolyB.mul {f g : ℝ → ℝ} {m m' : ℕ} (hf : PolyB f m) (hg : PolyB g m')
    (hg0 : ∀ x : ℝ, 1 ≤ x → 0 ≤ g x) :
    PolyB (fun x => f x * g x) (m + m') := by
  obtain ⟨K, hK, hf⟩ := hf
  obtain ⟨K', hK', hg⟩ := hg
  refine ⟨K * K', by positivity, fun x hx => ?_⟩
  have h1 := hf x hx
  have h2 := hg x hx
  calc f x * g x ≤ (K * x ^ m) * (K' * x ^ m') := mul_le_mul h1 h2 (hg0 x hx) (by
        have : 0 ≤ x := by linarith
        positivity)
    _ = K * K' * x ^ (m + m') := by ring

end Asymp

section

variable {T : Typing} (hT : T.Ok)

include hT

theorem pb_critBar : PolyB T.critBar 2 := by
  have hc0 : (0 : ℝ) ≤ T.c0 := Nat.cast_nonneg _
  have hRb := hT.dummy_ok.Rb_pos
  refine ⟨2 * T.c0 * T.Rb + 2 * T.c0 + 10, by positivity, fun x hx => ?_⟩
  unfold Typing.critBar
  have : (1 : ℝ) ≤ x ^ 2 := one_le_pow₀ hx
  nlinarith

theorem pb_omegaBar : PolyB T.omegaBar 2 := by
  have hRb := hT.dummy_ok.Rb_pos
  have hL := hT.dummy_ok.cast_L_ge
  refine ⟨2 * T.Rb + T.L + 11, by positivity, fun x hx => ?_⟩
  unfold Typing.omegaBar
  have : (1 : ℝ) ≤ x ^ 2 := one_le_pow₀ hx
  nlinarith

theorem pb_Dbar : PolyB T.Dbar 2 := by
  obtain ⟨K1, hK1, h1⟩ := pb_critBar hT
  obtain ⟨K2, hK2, h2⟩ := pb_omegaBar hT
  refine ⟨Real.sqrt T.d * (K1 + K2), by positivity, fun x hx => ?_⟩
  unfold Typing.Dbar
  have := h1 x hx; have := h2 x hx
  have hs := Real.sqrt_nonneg (T.d : ℝ)
  nlinarith

theorem pb_nuBar : PolyB T.nuBar T.p2 := by
  have hC := hT.Cν_pos
  refine ⟨T.Cν + 1, by positivity, fun x hx => ?_⟩
  unfold Typing.nuBar
  have : (1 : ℝ) ≤ x ^ T.p2 := one_le_pow₀ hx
  nlinarith

theorem nonneg_Dbar : ∀ x : ℝ, 1 ≤ x → 0 ≤ T.Dbar x := fun x _ =>
  le_trans zero_le_one (hT.dummy_ok.one_le_Dbar x)

theorem nonneg_nuBar : ∀ x : ℝ, 1 ≤ x → 0 ≤ T.nuBar x := fun x hx =>
  hT.dummy_ok.nuBar_nonneg (by linarith)

theorem pb_nuD : PolyB (fun x => T.nuBar x * T.Dbar x) (T.p2 + 2) :=
  (pb_nuBar hT).mul (pb_Dbar hT) (nonneg_Dbar hT)

end

section

variable {T : Typing} (hT : T.Ok)

include hT

theorem pb_Abar {a : ℝ} (ha : 1 ≤ a) : PolyB (fun x => T.Abar (a * x)) (T.p2 - 1) := by
  have hS := hT.dummy_ok
  have hA2 := hT.A2_pos
  have hθ : 0 < T.θp := lt_of_lt_of_le hT.θm_pos hT.θm_le_θp
  have hCw := hS.Cw_nonneg
  have hp2 := hT.p2_ge
  refine ⟨2 * T.A2 * T.p2 * T.θp * a ^ (T.p2 - 1) + T.Cw * a ^ (2 * T.d + 1), by positivity,
    fun x hx => ?_⟩
  show T.Abar (a * x) ≤ _
  unfold Typing.Abar
  have h1 : x ^ (2 * T.d + 1) ≤ x ^ (T.p2 - 1) := pow_le_pow_right₀ hx (by omega)
  have h2 : (a * x) ^ (T.p2 - 1) = a ^ (T.p2 - 1) * x ^ (T.p2 - 1) := mul_pow _ _ _
  have h3 : (a * x) ^ (2 * T.d + 1) = a ^ (2 * T.d + 1) * x ^ (2 * T.d + 1) := mul_pow _ _ _
  rw [h2, h3]
  have h4 : 0 ≤ T.Cw * a ^ (2 * T.d + 1) := by positivity
  nlinarith

theorem cPrime_nonneg : 0 ≤ T.cPrime := by
  have := hT.dummy_ok.cStar_ge_one
  have := hT.dummy_ok.θp_pos
  unfold Typing.cPrime; positivity

theorem Ct_nonneg : 0 ≤ T.Ct := by
  have := hT.dummy_ok.αlogL_pos
  have := hT.dummy_ok.θp_pos
  unfold Typing.Ct; positivity

theorem pb_Phi : PolyB T.Phi T.p2 := by
  have hS := hT.dummy_ok
  have hA2 := hT.A2_pos
  have hc := cPrime_nonneg hT
  have hCt := Ct_nonneg hT
  have hCw := hS.Cw_nonneg
  have hp2 := hT.p2_ge
  refine ⟨2 * T.A2 * T.cPrime ^ T.p2 + T.Ct * T.Cw * T.cPrime ^ (2 * T.d + 1), by positivity,
    fun x hx => ?_⟩
  unfold Typing.Phi
  have h1 : x ^ (2 * T.d + 2) ≤ x ^ T.p2 := pow_le_pow_right₀ hx (by omega)
  have h2 : (T.cPrime * x) ^ T.p2 = T.cPrime ^ T.p2 * x ^ T.p2 := mul_pow _ _ _
  rw [h2]
  have h4 : 0 ≤ T.Ct * T.Cw * T.cPrime ^ (2 * T.d + 1) := by positivity
  nlinarith

theorem one_le_nuD : ∀ x : ℝ, 1 ≤ x → 1 ≤ T.nuBar x * T.Dbar x := fun x hx => by
  have h1 := hT.dummy_ok.one_le_nuBar (by linarith : (0 : ℝ) ≤ x)
  have h2 := hT.dummy_ok.one_le_Dbar x
  nlinarith

theorem lb_logb_nuD : LogB (fun x => Real.logb T.L (T.nuBar x * T.Dbar x)) :=
  logB_logb (by have := hT.dummy_ok.cast_L_ge; linarith) (pb_nuD hT) (one_le_nuD hT)

theorem lb_logb_nu : LogB (fun x => Real.logb T.L (T.nuBar x)) :=
  logB_logb (by have := hT.dummy_ok.cast_L_ge; linarith) (pb_nuBar hT)
    (fun x hx => hT.dummy_ok.one_le_nuBar (by linarith))

theorem lb_logb_1D : LogB (fun x => Real.logb T.L (1 + T.Dbar x)) := by
  have hD : PolyB (fun x => 1 + T.Dbar x) 2 :=
    ((polyB_const (zero_le_one) 2).add (pb_Dbar hT)).congr' (fun x => by simp)
  exact logB_logb (by have := hT.dummy_ok.cast_L_ge; linarith) hD
    (fun x hx => by have := hT.dummy_ok.one_le_Dbar x; linarith)

theorem lb_hBar : LogB T.hBar := by
  have hS := hT.dummy_ok
  have hy : PolyB (fun x => 2 * Real.sqrt T.d * T.nuBar x * T.M *
      (T.critBar x + T.omegaBar x)) (T.p2 + 2) := by
    have h1 : PolyB (fun x => T.critBar x + T.omegaBar x) 2 :=
      (pb_critBar hT).add (pb_omegaBar hT)
    have hnn : ∀ x : ℝ, 1 ≤ x → 0 ≤ T.critBar x + T.omegaBar x := fun x hx => by
      have := hS.critBar_ge x; have := hS.omegaBar_ge x; linarith
    have h2 := (pb_nuBar hT).mul h1 hnn
    have h3 := h2.const_mul (c := 2 * Real.sqrt T.d * T.M)
      (by have : (0 : ℝ) ≤ T.M := Nat.cast_nonneg _; positivity)
    exact h3.congr' (fun x => by ring)
  have hlb := logB_logb (by have := hS.cast_L_ge; linarith) hy (fun x hx => by
    have h1 := hS.sqrt_d_ge
    have h2 := hS.one_le_nuBar (by linarith : (0 : ℝ) ≤ x)
    have h3 : (1 : ℝ) ≤ T.M := by exact_mod_cast hT.one_le_M
    have h4 := hS.critBar_ge x
    have h5 := hS.omegaBar_ge x
    have : (1 : ℝ) ≤ 2 * Real.sqrt T.d * T.nuBar x * T.M * (T.critBar x + T.omegaBar x) := by
      have e1 : (1 : ℝ) ≤ 2 * Real.sqrt T.d := by linarith
      have e2 : (1 : ℝ) ≤ 2 * Real.sqrt T.d * T.nuBar x := by nlinarith
      have e3 : (1 : ℝ) ≤ 2 * Real.sqrt T.d * T.nuBar x * T.M := by nlinarith
      nlinarith
    exact this)
  exact (hlb.add_const 3).congr' (fun x => by unfold Typing.hBar; rfl)

theorem lb_n2Bar : LogB T.n2Bar := by
  have hS := hT.dummy_ok
  have hy : PolyB (fun x => (T.L : ℝ) * T.M * T.critBar x) 2 := by
    have := (pb_critBar hT).const_mul (c := (T.L : ℝ) * T.M)
      (by have : (0 : ℝ) ≤ T.M := Nat.cast_nonneg _; have := hS.cast_L_ge; positivity)
    exact this
  have hlb := logB_logb (by have := hS.cast_L_ge; linarith) hy (fun x hx => by
    have h3 : (1 : ℝ) ≤ T.M := by exact_mod_cast hT.one_le_M
    have h4 := hS.critBar_ge x
    have h5 := hS.cast_L_ge
    have e1 : (1 : ℝ) ≤ (T.L : ℝ) * T.M := by nlinarith
    nlinarith)
  exact (hlb.add_const 1).congr' (fun x => by unfold Typing.n2Bar; rfl)

theorem lb_n2Bar_two : LogB (fun x => T.n2Bar (2 * x)) := by
  have hS := hT.dummy_ok
  have hy : PolyB (fun x => (T.L : ℝ) * T.M * T.critBar (2 * x)) 2 := by
    obtain ⟨K, hK, h⟩ := pb_critBar hT
    refine ⟨(T.L : ℝ) * T.M * (K * 4), by
      have : (0 : ℝ) ≤ T.M := Nat.cast_nonneg _; have := hS.cast_L_ge; positivity, fun x hx => ?_⟩
    have h1 := h (2 * x) (by linarith)
    have : (T.L : ℝ) * T.M * T.critBar (2 * x) ≤ (T.L : ℝ) * T.M * (K * (2 * x) ^ 2) := by
      apply mul_le_mul_of_nonneg_left h1
      have : (0 : ℝ) ≤ T.M := Nat.cast_nonneg _; have := hS.cast_L_ge; positivity
    calc _ ≤ _ := this
      _ = (T.L : ℝ) * T.M * (K * 4) * x ^ 2 := by ring
  have hlb := logB_logb (by have := hS.cast_L_ge; linarith) hy (fun x hx => by
    have h3 : (1 : ℝ) ≤ T.M := by exact_mod_cast hT.one_le_M
    have h4 := hS.critBar_ge (2 * x)
    have h5 := hS.cast_L_ge
    have e1 : (1 : ℝ) ≤ (T.L : ℝ) * T.M := by nlinarith
    nlinarith)
  exact (hlb.add_const 1).congr' (fun x => by unfold Typing.n2Bar; rfl)

theorem lb_DeltaBar : LogB T.DeltaBar := by
  have h := (((logB_const 2).add (lb_logb_nu hT)).add (lb_logb_1D hT)).add (lb_n2Bar_two hT)
  exact h.congr' (fun x => by unfold Typing.DeltaBar; ring)

theorem lb_Gbar : LogB T.Gbar := by
  have hcs := hT.dummy_ok.cStar_ge_one
  have h := ((((logB_const 2).add (lb_logb_nuD hT)).add (lb_logb_1D hT)).const_mul
    (c := T.cStar) (by linarith)).add_const 1
  exact h.congr' (fun x => by unfold Typing.Gbar; ring)

theorem nonneg_hBar : ∀ x : ℝ, 1 ≤ x → 0 ≤ T.hBar x := fun x hx => by
  have hS := hT.dummy_ok
  have hL := hS.cast_L_ge
  have h1 := hS.sqrt_d_ge
  have h2 := hS.one_le_nuBar (by linarith : (0 : ℝ) ≤ x)
  have h3 : (1 : ℝ) ≤ T.M := by exact_mod_cast hT.one_le_M
  have h4 := hS.critBar_ge x
  have h5 := hS.omegaBar_ge x
  have e2 : (1 : ℝ) ≤ 2 * Real.sqrt T.d * T.nuBar x := by nlinarith
  have e3 : (1 : ℝ) ≤ 2 * Real.sqrt T.d * T.nuBar x * T.M := by nlinarith
  have e4 : (1 : ℝ) ≤ 2 * Real.sqrt T.d * T.nuBar x * T.M * (T.critBar x + T.omegaBar x) := by
    nlinarith
  unfold Typing.hBar
  have := Real.logb_nonneg (b := (T.L : ℝ)) (by linarith) e4
  linarith

theorem nonneg_DeltaBar : ∀ x : ℝ, 1 ≤ x → 0 ≤ T.DeltaBar x := fun x hx => by
  have hS := hT.dummy_ok
  have hL := hS.cast_L_ge
  have h1 := hS.one_le_nuBar (by linarith : (0 : ℝ) ≤ x)
  have h2 := hS.one_le_Dbar x
  have h3 : 0 ≤ Real.logb T.L (T.nuBar x) := Real.logb_nonneg (by linarith) h1
  have h4 : 0 ≤ Real.logb T.L (1 + T.Dbar x) := Real.logb_nonneg (by linarith) (by linarith)
  have h5 : 0 ≤ T.n2Bar (2 * x) := by
    unfold Typing.n2Bar
    have hM : (1 : ℝ) ≤ T.M := by exact_mod_cast hT.one_le_M
    have hc := hS.critBar_ge (2 * x)
    have : 0 ≤ Real.logb T.L ((T.L : ℝ) * T.M * T.critBar (2 * x)) :=
      Real.logb_nonneg (by linarith)
        (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (by linarith) hM)
          (by linarith))
    linarith
  unfold Typing.DeltaBar
  linarith

theorem nonneg_Gbar : ∀ x : ℝ, 1 ≤ x → 0 ≤ T.Gbar x := fun x hx => by
  have hS := hT.dummy_ok
  have hL := hS.cast_L_ge
  have h1 := hS.cStar_ge_one
  have h2 := hS.one_le_nuBar (by linarith : (0 : ℝ) ≤ x)
  have h3 := hS.one_le_Dbar x
  have h4 : 0 ≤ Real.logb T.L (T.nuBar x * T.Dbar x) :=
    Real.logb_nonneg (by linarith) (by nlinarith)
  have h5 : 0 ≤ Real.logb T.L (1 + T.Dbar x) :=
    Real.logb_nonneg (by linarith) (by linarith)
  unfold Typing.Gbar
  positivity

theorem nonneg_n2Bar : ∀ x : ℝ, 1 ≤ x → 0 ≤ T.n2Bar x := fun x hx => by
  have hS := hT.dummy_ok
  have hL := hS.cast_L_ge
  unfold Typing.n2Bar
  have hM : (1 : ℝ) ≤ T.M := by exact_mod_cast hT.one_le_M
  have hc := hS.critBar_ge x
  have : 0 ≤ Real.logb T.L ((T.L : ℝ) * T.M * T.critBar x) :=
    Real.logb_nonneg (by linarith)
      (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (by linarith) hM)
        (by linarith))
  linarith

end

end Balaban.LargeField
