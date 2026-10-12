module

public import Balaban.Flow.RunningCoefficients
public import Balaban.LargeField.Counter.Bars
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr

/-!
# The horizon of the flow (Part I, Lemma I.5.6)

`FlowSeq` is the data of (I.1)-(I.2): `β_k = β L^{k(d-2)} γ_k`, `ν_k = ν L^{2k} δ_k` with
`γ_k, δ_k ∈ [19/20, 20/19]` (this contains `e^{±ε}`, `ε ≤ 1/20`; the moduli of the
products of `RunningCoefficients` satisfy it, `FlowSeq.ofRunning`).  `kfhat` is `k̂_f`, `kf` the
first `k` with `ν_k > (7/8) L^{-2}`, `k0` the last `k` with `β_k ν_k ≤ 1` (`0` if none).

* `kfhat_bounds` and `k0_lt_kf` (Lemma I.5.6 (a));
* `hLambda_of_flow` ((b): the horizon conditions (H-λ) for `λ̂`);
* `hT_of_flow` ((c): (H-T) for the tori of the flow).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

/-- The data (I.1), (I.2) of the flow. -/
structure FlowSeq where
  d : ℕ
  L : ℕ
  β : ℝ
  ν : ℝ
  a : ℝ
  γ : ℕ → ℝ
  δ : ℕ → ℝ
  hd : 3 ≤ d
  hL : 2 ≤ L
  hβ : 0 < β
  hν0 : 0 < ν
  hν1 : ν ≤ 1
  ha1 : 1 < a
  ha2 : a < 3 / 2
  hγ : ∀ k, 19 / 20 ≤ γ k ∧ γ k ≤ 20 / 19
  hδ : ∀ k, 19 / 20 ≤ δ k ∧ δ k ≤ 20 / 19
  hγ0 : γ 0 = 1
  hδ0 : δ 0 = 1

namespace FlowSeq

variable (F : FlowSeq)

/-- `d - 2`. -/
def e : ℕ := F.d - 2

/-- `β_k = β L^{k(d-2)} γ_k`. -/
noncomputable def beta (k : ℕ) : ℝ := F.β * (F.L : ℝ) ^ (k * F.e) * F.γ k

/-- `ν_k = ν L^{2k} δ_k`. -/
noncomputable def nu (k : ℕ) : ℝ := F.ν * (F.L : ℝ) ^ (2 * k) * F.δ k

/-- `λ̂_j = log (β a) + 1 + j (d-2) log L`. -/
noncomputable def lamHat (j : ℕ) : ℝ := Real.log (F.β * F.a) + 1 + j * ((F.e : ℝ) * Real.log F.L)

/-- `λ_k = log (β_k a)`. -/
noncomputable def lam (k : ℕ) : ℝ := Real.log (F.beta k * F.a)

theorem L_ge : (2 : ℝ) ≤ F.L := by exact_mod_cast F.hL

theorem L_pos : (0 : ℝ) < F.L := by linarith [F.L_ge]

theorem gamma_pos (k : ℕ) : 0 < F.γ k := by linarith [(F.hγ k).1]

theorem delta_pos (k : ℕ) : 0 < F.δ k := by linarith [(F.hδ k).1]

theorem beta_pos (k : ℕ) : 0 < F.beta k := by
  unfold beta; have := F.L_pos; have := F.gamma_pos k; have := F.hβ; positivity

theorem nu_pos (k : ℕ) : 0 < F.nu k := by
  unfold nu; have := F.L_pos; have := F.delta_pos k; have := F.hν0; positivity

theorem d_eq : (F.d : ℝ) = F.e + 2 := by
  have := F.hd; unfold e; push_cast [Nat.cast_sub (by omega : 2 ≤ F.d)]; ring

theorem nu_succ (k : ℕ) : F.nu (k + 1) = F.nu k * (F.L : ℝ) ^ 2 * (F.δ (k + 1) / F.δ k) := by
  have := F.delta_pos k
  unfold nu
  rw [show 2 * (k + 1) = 2 * k + 2 by ring, pow_add]
  field_simp

theorem beta_succ (k : ℕ) :
    F.beta (k + 1) = F.beta k * (F.L : ℝ) ^ F.e * (F.γ (k + 1) / F.γ k) := by
  have := F.gamma_pos k
  unfold beta
  rw [show (k + 1) * F.e = k * F.e + F.e by ring, pow_add]
  field_simp

theorem delta_ratio_ge (k : ℕ) : 361 / 400 ≤ F.δ (k + 1) / F.δ k := by
  have h0 := F.delta_pos k
  rw [le_div_iff₀ h0]
  nlinarith [(F.hδ k).2, (F.hδ (k + 1)).1]

theorem delta_ratio_le (k : ℕ) : F.δ (k + 1) / F.δ k ≤ 400 / 361 := by
  have h0 := F.delta_pos k
  rw [div_le_iff₀ h0]
  nlinarith [(F.hδ k).1, (F.hδ (k + 1)).2]

theorem gamma_ratio_ge (k : ℕ) : 361 / 400 ≤ F.γ (k + 1) / F.γ k := by
  have h0 := F.gamma_pos k
  rw [le_div_iff₀ h0]
  nlinarith [(F.hγ k).2, (F.hγ (k + 1)).1]

theorem gamma_ratio_le (k : ℕ) : F.γ (k + 1) / F.γ k ≤ 400 / 361 := by
  have h0 := F.gamma_pos k
  rw [div_le_iff₀ h0]
  nlinarith [(F.hγ k).1, (F.hγ (k + 1)).2]

/-- `ν_k` is strictly increasing. -/
theorem nu_strictMono : StrictMono F.nu := by
  refine strictMono_nat_of_lt_succ fun k => ?_
  rw [F.nu_succ k]
  have h1 := F.nu_pos k
  have h2 := F.delta_ratio_ge k
  have h3 : (4 : ℝ) ≤ (F.L : ℝ) ^ 2 := by nlinarith [F.L_ge]
  have : 1 < (F.L : ℝ) ^ 2 * (F.δ (k + 1) / F.δ k) := by nlinarith
  nlinarith

/-- `β_k ν_k` is strictly increasing. -/
theorem betanu_succ_gt (k : ℕ) : F.beta k * F.nu k < F.beta (k + 1) * F.nu (k + 1) := by
  rw [F.nu_succ k, F.beta_succ k]
  have h1 := F.nu_pos k
  have h2 := F.beta_pos k
  have h3 := F.delta_ratio_ge k
  have h4 := F.gamma_ratio_ge k
  have h5 : (8 : ℝ) ≤ (F.L : ℝ) ^ F.e * (F.L : ℝ) ^ 2 := by
    have : (F.L : ℝ) ^ F.e * (F.L : ℝ) ^ 2 = (F.L : ℝ) ^ (F.e + 2) := by rw [pow_add]
    rw [this]
    have he : 1 ≤ F.e := by have := F.hd; unfold e; omega
    calc (8 : ℝ) = 2 ^ 3 := by norm_num
      _ ≤ (F.L : ℝ) ^ 3 := pow_le_pow_left₀ (by norm_num) F.L_ge 3
      _ ≤ (F.L : ℝ) ^ (F.e + 2) := pow_le_pow_right₀ (by linarith [F.L_ge]) (by omega)
  have h6 : 1 < (F.L : ℝ) ^ F.e * (F.γ (k + 1) / F.γ k) * ((F.L : ℝ) ^ 2 * (F.δ (k + 1) / F.δ k)) := by
    have : (F.L : ℝ) ^ F.e * (F.γ (k + 1) / F.γ k) * ((F.L : ℝ) ^ 2 * (F.δ (k + 1) / F.δ k)) =
        ((F.L : ℝ) ^ F.e * (F.L : ℝ) ^ 2) * ((F.γ (k + 1) / F.γ k) * (F.δ (k + 1) / F.δ k)) := by ring
    rw [this]
    have : (361 / 400 : ℝ) * (361 / 400) ≤ (F.γ (k + 1) / F.γ k) * (F.δ (k + 1) / F.δ k) :=
      mul_le_mul h4 h3 (by norm_num) (by linarith)
    nlinarith
  have : F.beta k * F.nu k * 1 < F.beta k * F.nu k *
      ((F.L : ℝ) ^ F.e * (F.γ (k + 1) / F.γ k) * ((F.L : ℝ) ^ 2 * (F.δ (k + 1) / F.δ k))) :=
    mul_lt_mul_of_pos_left h6 (mul_pos h2 h1)
  nlinarith

/-! ### `λ_k` versus `λ̂_k` (I.3) -/

theorem log_gamma_bounds (k : ℕ) : -1 ≤ Real.log (F.γ k) ∧ Real.log (F.γ k) ≤ 1 := by
  have h0 := F.gamma_pos k
  have h1 := (F.hγ k).1
  have h2 := (F.hγ k).2
  constructor
  · have := Real.log_le_sub_one_of_pos (inv_pos.mpr h0)
    rw [Real.log_inv] at this
    have h3 : (F.γ k)⁻¹ ≤ 20 / 19 := by
      rw [inv_le_comm₀ h0 (by norm_num)]; linarith
    linarith
  · have := Real.log_le_sub_one_of_pos h0
    linarith

theorem lam_eq (k : ℕ) :
    F.lam k = Real.log F.β + k * ((F.e : ℝ) * Real.log F.L) + Real.log (F.γ k) + Real.log F.a := by
  have h1 := F.L_pos
  have h2 := F.hβ
  have h3 := F.gamma_pos k
  have h4 : 0 < F.a := by linarith [F.ha1]
  unfold lam beta
  rw [Real.log_mul (by positivity) h4.ne', Real.log_mul (by positivity) h3.ne',
    Real.log_mul h2.ne' (by positivity), Real.log_pow]
  push_cast
  ring

theorem lamHat_eq (k : ℕ) :
    F.lamHat k = Real.log F.β + Real.log F.a + 1 + k * ((F.e : ℝ) * Real.log F.L) := by
  have h4 : 0 < F.a := by linarith [F.ha1]
  unfold lamHat
  rw [Real.log_mul F.hβ.ne' h4.ne']

/-- (I.3): `λ_k ≤ λ̂_k ≤ λ_k + 2`. -/
theorem lam_le_lamHat (k : ℕ) : F.lam k ≤ F.lamHat k := by
  rw [F.lam_eq, F.lamHat_eq]; linarith [(F.log_gamma_bounds k).2]

theorem lamHat_le_lam_add (k : ℕ) : F.lamHat k ≤ F.lam k + 2 := by
  rw [F.lam_eq, F.lamHat_eq]; linarith [(F.log_gamma_bounds k).1]

theorem exp_lam (k : ℕ) : Real.exp (F.lam k) = F.beta k * F.a := by
  have h4 : 0 < F.a := by linarith [F.ha1]
  exact Real.exp_log (mul_pos (F.beta_pos k) h4)

/-- `β_k ≥ (2/3) e^{λ̂_k - 2}`. -/
theorem beta_ge (k : ℕ) : 2 / 3 * Real.exp (F.lamHat k - 2) ≤ F.beta k := by
  have h4 : 0 < F.a := by linarith [F.ha1]
  have h1 : Real.exp (F.lamHat k - 2) ≤ Real.exp (F.lam k) :=
    Real.exp_le_exp.mpr (by linarith [F.lamHat_le_lam_add k])
  rw [F.exp_lam] at h1
  have h2 : F.beta k * F.a ≤ F.beta k * (3 / 2) :=
    mul_le_mul_of_nonneg_left F.ha2.le (F.beta_pos k).le
  nlinarith

theorem lamHat_sub (j k : ℕ) :
    F.lamHat j - F.lamHat k = ((j : ℝ) - k) * ((F.e : ℝ) * Real.log F.L) := by
  unfold lamHat; ring

/-! ### `k̂_f`, `k_f`, `k_0` -/

theorem exists_pow_big (c : ℝ) : ∃ n : ℕ, c < (F.L : ℝ) ^ n :=
  pow_unbounded_of_one_lt c (by linarith [F.L_ge])

theorem exists_kfhat : ∃ k : ℕ, 1 ≤ F.ν * (F.L : ℝ) ^ (2 * k + 2) := by
  obtain ⟨n, hn⟩ := F.exists_pow_big (1 / F.ν)
  refine ⟨n, ?_⟩
  have h1 : (F.L : ℝ) ^ n ≤ (F.L : ℝ) ^ (2 * n + 2) :=
    pow_le_pow_right₀ (by linarith [F.L_ge]) (by omega)
  rw [div_lt_iff₀ F.hν0] at hn
  have h2 := mul_le_mul_of_nonneg_left h1 F.hν0.le
  nlinarith

theorem nu_gt_of {k : ℕ} (h : 1 ≤ F.ν * (F.L : ℝ) ^ (2 * k + 2)) : 7 / 8 / (F.L : ℝ) ^ 2 < F.nu k := by
  have hL2 : (4 : ℝ) ≤ (F.L : ℝ) ^ 2 := by nlinarith [F.L_ge]
  have hL2' : (0 : ℝ) < (F.L : ℝ) ^ 2 := by linarith
  have h2 : (F.L : ℝ) ^ (2 * k + 2) = (F.L : ℝ) ^ (2 * k) * (F.L : ℝ) ^ 2 := by rw [pow_add]
  rw [h2, ← mul_assoc] at h
  have h3 : 1 / (F.L : ℝ) ^ 2 ≤ F.ν * (F.L : ℝ) ^ (2 * k) := by
    rw [div_le_iff₀ hL2']; linarith
  have h4 := (F.hδ k).1
  unfold nu
  have h5 : 7 / 8 / (F.L : ℝ) ^ 2 < 19 / 20 * (1 / (F.L : ℝ) ^ 2) := by
    rw [div_eq_mul_one_div (7 / 8 : ℝ)]
    have : 0 < 1 / (F.L : ℝ) ^ 2 := by positivity
    nlinarith
  have h6 : 19 / 20 * (1 / (F.L : ℝ) ^ 2) ≤ F.δ k * (F.ν * (F.L : ℝ) ^ (2 * k)) := by
    have : 0 ≤ F.ν * (F.L : ℝ) ^ (2 * k) := by have := F.hν0; positivity
    nlinarith
  linarith

theorem exists_kf : ∃ k : ℕ, 7 / 8 / (F.L : ℝ) ^ 2 < F.nu k := by
  obtain ⟨k, hk⟩ := F.exists_kfhat
  exact ⟨k, F.nu_gt_of hk⟩

open Classical in
/-- `k̂_f = min {k : ν L^{2k+2} ≥ 1}`. -/
noncomputable def kfhat : ℕ := Nat.find F.exists_kfhat

open Classical in
/-- `k_f`: the first `k` with `ν_k > (7/8) L^{-2}`. -/
noncomputable def kf : ℕ := Nat.find F.exists_kf

theorem kfhat_spec : 1 ≤ F.ν * (F.L : ℝ) ^ (2 * F.kfhat + 2) := by
  classical
  exact Nat.find_spec F.exists_kfhat

theorem kfhat_min {j : ℕ} (hj : j < F.kfhat) : F.ν * (F.L : ℝ) ^ (2 * j + 2) < 1 := by
  classical
  exact not_le.mp (Nat.find_min F.exists_kfhat hj)

theorem kf_spec : 7 / 8 / (F.L : ℝ) ^ 2 < F.nu F.kf := by
  classical
  exact Nat.find_spec F.exists_kf

theorem kf_min {j : ℕ} (hj : j < F.kf) : F.nu j ≤ 7 / 8 / (F.L : ℝ) ^ 2 := by
  classical
  exact not_lt.mp (Nat.find_min F.exists_kf hj)

/-- **Lemma I.5.6 (a)**: `k_f ≤ k̂_f ≤ k_f + 1`. -/
theorem kfhat_bounds : F.kf ≤ F.kfhat ∧ F.kfhat ≤ F.kf + 1 := by
  classical
  have hL2 : (4 : ℝ) ≤ (F.L : ℝ) ^ 2 := by nlinarith [F.L_ge]
  have hL2' : (0 : ℝ) < (F.L : ℝ) ^ 2 := by linarith
  constructor
  · exact Nat.find_min' F.exists_kf (F.nu_gt_of F.kfhat_spec)
  · apply Nat.find_min'
    have h := F.kf_spec
    unfold nu at h
    have h1 := (F.hδ F.kf).2
    have h2 : (F.L : ℝ) ^ (2 * (F.kf + 1) + 2) = (F.L : ℝ) ^ (2 * F.kf) * (F.L : ℝ) ^ 2 *
        (F.L : ℝ) ^ 2 := by
      rw [show 2 * (F.kf + 1) + 2 = 2 * F.kf + 2 + 2 by ring, pow_add, pow_add]
    rw [h2]
    have h3 : 7 / 8 / (F.L : ℝ) ^ 2 < F.ν * (F.L : ℝ) ^ (2 * F.kf) * (20 / 19) := by
      have : 0 ≤ F.ν * (F.L : ℝ) ^ (2 * F.kf) := by have := F.hν0; positivity
      nlinarith
    rw [div_lt_iff₀ hL2'] at h3
    have h4 : 0 < F.ν * (F.L : ℝ) ^ (2 * F.kf) := by have := F.hν0; have := F.L_pos; positivity
    nlinarith

/-- The set of `k` with `β_k ν_k ≤ 1` is bounded. -/
theorem bddAbove_betanu : BddAbove {k : ℕ | F.beta k * F.nu k ≤ 1} := by
  obtain ⟨n, hn⟩ := F.exists_pow_big (2 / (F.β * F.ν))
  refine ⟨n, fun k hk => ?_⟩
  by_contra hlt
  push Not at hlt
  simp only [Set.mem_ofPred_eq] at hk
  have hbn : 0 < F.β * F.ν := mul_pos F.hβ F.hν0
  rw [div_lt_iff₀ hbn] at hn
  have h1 : (F.L : ℝ) ^ n ≤ (F.L : ℝ) ^ (k * F.e + 2 * k) :=
    pow_le_pow_right₀ (by linarith [F.L_ge]) (by
      have : 1 ≤ F.e := by have := F.hd; unfold e; omega
      nlinarith)
  have h2 := (F.hγ k).1
  have h3 := (F.hδ k).1
  have h4 : F.beta k * F.nu k = F.β * F.ν * (F.L : ℝ) ^ (k * F.e + 2 * k) * (F.γ k * F.δ k) := by
    unfold beta nu; rw [pow_add]; ring
  rw [h4] at hk
  have h5 : (361 / 400 : ℝ) ≤ F.γ k * F.δ k := by nlinarith
  have h6 : 2 < F.β * F.ν * (F.L : ℝ) ^ (k * F.e + 2 * k) := by nlinarith
  nlinarith

theorem betanu_mono {j k : ℕ} (h : j ≤ k) : F.beta j * F.nu j ≤ F.beta k * F.nu k := by
  induction k, h using Nat.le_induction with
  | base => exact le_rfl
  | succ k _ ih => exact ih.trans (F.betanu_succ_gt k).le

/-- `k_0`: the last `k` with `β_k ν_k ≤ 1`, and `0` if there is none. -/
noncomputable def k0 : ℕ := sSup {k : ℕ | F.beta k * F.nu k ≤ 1}

/-- Either `k_0` is genuine (`β_{k_0} ν_{k_0} ≤ 1 < β_{k_0+1} ν_{k_0+1}`) or `β ν > 1` and `k_0 = 0`. -/
theorem k0_cases : (F.beta F.k0 * F.nu F.k0 ≤ 1 ∧ 1 < F.beta (F.k0 + 1) * F.nu (F.k0 + 1)) ∨
    (1 < F.β * F.ν ∧ F.k0 = 0) := by
  by_cases h : F.beta 0 * F.nu 0 ≤ 1
  · left
    have hne : ({k : ℕ | F.beta k * F.nu k ≤ 1}).Nonempty := ⟨0, h⟩
    have hmem := Nat.sSup_mem hne F.bddAbove_betanu
    refine ⟨hmem, ?_⟩
    by_contra hcon
    push Not at hcon
    have : F.k0 + 1 ≤ F.k0 := le_csSup F.bddAbove_betanu hcon
    omega
  · right
    have h0 : F.beta 0 * F.nu 0 = F.β * F.ν := by
      unfold beta nu; rw [F.hγ0, F.hδ0]; simp
    have hempty : {k : ℕ | F.beta k * F.nu k ≤ 1} = ∅ := by
      ext k
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le]
      exact lt_of_not_ge h |>.trans_le (F.betanu_mono (Nat.zero_le k))
    refine ⟨?_, ?_⟩
    · rw [← h0]; exact lt_of_not_ge h
    · unfold k0; rw [hempty]; simp

theorem betanu_succ_le (k : ℕ) :
    F.beta (k + 1) * F.nu (k + 1) ≤
      F.beta k * F.nu k * ((F.L : ℝ) ^ F.e * (F.L : ℝ) ^ 2 * (400 / 361) ^ 2) := by
  rw [F.nu_succ k, F.beta_succ k]
  have h1 := F.nu_pos k
  have h2 := F.beta_pos k
  have h3 := F.delta_ratio_le k
  have h4 := F.gamma_ratio_le k
  have h5 : 0 < F.δ (k + 1) / F.δ k := div_pos (F.delta_pos _) (F.delta_pos _)
  have h6 : 0 < F.γ (k + 1) / F.γ k := div_pos (F.gamma_pos _) (F.gamma_pos _)
  have h7 : (F.γ (k + 1) / F.γ k) * (F.δ (k + 1) / F.δ k) ≤ (400 / 361) ^ 2 := by
    have := mul_le_mul h4 h3 h5.le (by norm_num)
    nlinarith
  have hLe : 0 < (F.L : ℝ) ^ F.e * (F.L : ℝ) ^ 2 := by have := F.L_pos; positivity
  have : F.beta k * (F.L : ℝ) ^ F.e * (F.γ (k + 1) / F.γ k) * (F.nu k * (F.L : ℝ) ^ 2 *
      (F.δ (k + 1) / F.δ k)) = F.beta k * F.nu k * ((F.L : ℝ) ^ F.e * (F.L : ℝ) ^ 2 *
      ((F.γ (k + 1) / F.γ k) * (F.δ (k + 1) / F.δ k))) := by ring
  rw [this]
  exact mul_le_mul_of_nonneg_left (by nlinarith) (mul_pos h2 h1).le

/-- **Lemma I.5.6 (a)**: `k_0 < k_f` (for `k_f ≥ 1`; if `k_0` is genuine, `β_{k_0} ≥ 2L²`). -/
theorem k0_lt_kf (hkf : 1 ≤ F.kf)
    (hgen : F.beta F.k0 * F.nu F.k0 ≤ 1 → 2 * (F.L : ℝ) ^ 2 ≤ F.beta F.k0) : F.k0 < F.kf := by
  rcases F.k0_cases with ⟨h, -⟩ | ⟨-, h0⟩
  · by_contra hcon
    push Not at hcon
    have h1 := F.nu_strictMono.monotone hcon
    have h2 := hgen h
    have hB := F.beta_pos F.k0
    have hN := F.nu_pos F.k0
    have hL2 : (0 : ℝ) < (F.L : ℝ) ^ 2 := by have := F.L_pos; positivity
    have h3 : F.nu F.k0 ≤ 1 / (2 * (F.L : ℝ) ^ 2) := by
      rw [le_div_iff₀ (by positivity)]; nlinarith
    have h4 := F.kf_spec
    have : 1 / (2 * (F.L : ℝ) ^ 2) < 7 / 8 / (F.L : ℝ) ^ 2 := by
      rw [div_lt_div_iff₀ (by positivity) hL2]; nlinarith
    linarith
  · omega

theorem log_L_gt : 1 / 2 < Real.log F.L := by
  have h1 : Real.log 2 ≤ Real.log F.L := Real.log_le_log (by norm_num) F.L_ge
  have := Real.log_two_gt_d9
  linarith

theorem log_beta_lt (k : ℕ) : Real.log (F.beta k) < F.lamHat k := by
  have h4 : 0 < F.a := by linarith [F.ha1]
  have h1 : Real.log (F.beta k) < Real.log (F.beta k * F.a) :=
    Real.log_lt_log (F.beta_pos k) (by nlinarith [F.beta_pos k, F.ha1])
  exact h1.trans_le (F.lam_le_lamHat k)

/-- The core estimate of Lemma I.5.6 (b), genuine case. -/
theorem kf_sub_k0_genuine (hkf : 1 ≤ F.kf)
    (h1 : 1 < F.beta (F.k0 + 1) * F.nu (F.k0 + 1)) (hlt : F.k0 < F.kf) :
    (F.kf : ℝ) - F.k0 < ((F.e : ℝ) + 3) / 2 + F.lamHat F.k0 / (2 * Real.log F.L) := by
  have hLpos := F.L_pos
  obtain ⟨v, hv⟩ : ∃ v, F.kf = v + 1 := ⟨F.kf - 1, by omega⟩
  have huv : F.k0 ≤ v := by omega
  obtain ⟨w, hw⟩ : ∃ w, v = F.k0 + w := ⟨v - F.k0, by omega⟩
  have hvk : v < F.kf := by omega
  have hnuv := F.kf_min hvk
  -- `ν_v = ν_{k0} L^{2w} δ_v/δ_{k0}`
  have hX : F.nu v = F.nu F.k0 * (F.L : ℝ) ^ (2 * w) * (F.δ v / F.δ F.k0) := by
    have := F.delta_pos F.k0
    unfold nu
    rw [hw, show 2 * (F.k0 + w) = 2 * F.k0 + 2 * w by ring, pow_add]
    field_simp
  have hδ : 361 / 400 ≤ F.δ v / F.δ F.k0 := by
    have h0 := F.delta_pos F.k0
    rw [le_div_iff₀ h0]
    nlinarith [(F.hδ F.k0).2, (F.hδ v).1]
  set N := F.nu F.k0 with hN
  set B := F.beta F.k0 with hB
  set X := (F.L : ℝ) ^ (2 * w) with hXdef
  set P := (F.L : ℝ) ^ F.e with hP
  set Q := (F.L : ℝ) ^ 2 with hQ
  have hNpos : 0 < N := F.nu_pos _
  have hBpos : 0 < B := F.beta_pos _
  have hXpos : 0 < X := by positivity
  have hPpos : 0 < P := by positivity
  have hQpos : 0 < Q := by positivity
  have hi : N * X * (361 / 400) ≤ 7 / 8 / Q := by
    rw [hX] at hnuv
    have : N * X * (361 / 400) ≤ N * X * (F.δ v / F.δ F.k0) :=
      mul_le_mul_of_nonneg_left hδ (by positivity)
    linarith
  have hii : 1 < B * N * (P * Q * (400 / 361) ^ 2) := by
    have := F.betanu_succ_le F.k0
    have hh : 0 < F.beta F.k0 * F.nu F.k0 := mul_pos hBpos hNpos
    nlinarith
  have hT : X * (N * Q) ≤ 7 / 8 * (400 / 361) := by
    have h2 : N * X * (361 / 400) * Q ≤ 7 / 8 / Q * Q := mul_le_mul_of_nonneg_right hi hQpos.le
    rw [div_mul_cancel₀ _ hQpos.ne'] at h2
    nlinarith
  have hXlt : X < 2 * B * P := by
    have hTpos : 0 < N * Q := mul_pos hNpos hQpos
    have hk2 : 1 < (N * Q) * (B * P * (400 / 361) ^ 2) := by nlinarith
    have hBP : 0 < B * P * (400 / 361) ^ 2 := by positivity
    have h3 : X < X * ((N * Q) * (B * P * (400 / 361) ^ 2)) := by nlinarith
    have h4 : X * ((N * Q) * (B * P * (400 / 361) ^ 2)) ≤ 7 / 8 * (400 / 361) * (B * P * (400 / 361) ^ 2) := by
      calc X * ((N * Q) * (B * P * (400 / 361) ^ 2)) = (X * (N * Q)) * (B * P * (400 / 361) ^ 2) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hT hBP.le
    have hBP' : 0 < B * P := by positivity
    nlinarith
  -- logs
  have hlog := Real.log_lt_log hXpos hXlt
  rw [hXdef, Real.log_pow, Real.log_mul (by positivity) hPpos.ne', Real.log_mul (by norm_num) hBpos.ne',
    hP, Real.log_pow] at hlog
  have hlog2 : Real.log 2 ≤ Real.log F.L := Real.log_le_log (by norm_num) F.L_ge
  have hlb := F.log_beta_lt F.k0
  have hlL := F.log_L_gt
  have hkf' : (F.kf : ℝ) = (F.k0 : ℝ) + w + 1 := by rw [hv, hw]; push_cast; ring
  push_cast at hlog
  rw [hkf']
  have hlpos : 0 < 2 * Real.log F.L := by linarith
  rw [← sub_pos]
  have : ((F.e : ℝ) + 3) / 2 + F.lamHat F.k0 / (2 * Real.log F.L) - ((F.k0 : ℝ) + w + 1 - F.k0) =
      (((F.e : ℝ) + 1) * Real.log F.L + F.lamHat F.k0 - 2 * w * Real.log F.L) / (2 * Real.log F.L) := by
    field_simp; ring
  rw [this]
  apply div_pos _ hlpos
  nlinarith

/-- The flow's `c_H`. -/
noncomputable def cH : ℝ := ((F.d : ℝ) + 3) * ((F.e : ℝ)) / 2 * Real.log F.L

/-- **Lemma I.5.6 (b)**: `k̂_f - k_0 < (d+3)/2 + λ̂_{k_0}/(2 log L)`. -/
theorem kfhat_sub_k0_lt (hkf : 1 ≤ F.kf) (hpos : 0 ≤ F.lamHat F.k0)
    (hgen : F.beta F.k0 * F.nu F.k0 ≤ 1 → 2 * (F.L : ℝ) ^ 2 ≤ F.beta F.k0) :
    (F.kfhat : ℝ) - F.k0 < ((F.d : ℝ) + 3) / 2 + F.lamHat F.k0 / (2 * Real.log F.L) := by
  have hlL := F.log_L_gt
  have hlpos : 0 < 2 * Real.log F.L := by linarith
  have hd := F.d_eq
  have hb := F.kfhat_bounds.2
  have hdiv : 0 ≤ F.lamHat F.k0 / (2 * Real.log F.L) := div_nonneg hpos hlpos.le
  rcases F.k0_cases with ⟨h, h1⟩ | ⟨hbn, h0⟩
  · have := F.kf_sub_k0_genuine hkf h1 (F.k0_lt_kf hkf hgen)
    have hb' : (F.kfhat : ℝ) ≤ F.kf + 1 := by exact_mod_cast hb
    rw [hd]
    linarith
  · rw [h0] at hpos hdiv ⊢
    simp only [Nat.cast_zero, sub_zero]
    rcases Nat.eq_zero_or_pos F.kfhat with hk | hk
    · have he : (0 : ℝ) ≤ F.e := Nat.cast_nonneg _
      rw [hk]; push_cast; rw [hd]; linarith
    · have hmin := F.kfhat_min (j := F.kfhat - 1) (by omega)
      rw [show 2 * (F.kfhat - 1) + 2 = 2 * F.kfhat by omega] at hmin
      have hν := F.hν0
      have hLk : (F.L : ℝ) ^ (2 * F.kfhat) < F.β := by
        by_contra hcon
        push Not at hcon
        have := mul_le_mul_of_nonneg_left hcon hν.le
        nlinarith
      have hlog := Real.log_lt_log (by have := F.L_pos; positivity) hLk
      rw [Real.log_pow] at hlog
      have hlb : Real.log F.β < F.lamHat 0 := by
        have h4 : 0 < F.a := by linarith [F.ha1]
        have h1 : Real.log F.β < Real.log (F.β * F.a) :=
          Real.log_lt_log F.hβ (by nlinarith [F.hβ, F.ha1])
        unfold lamHat
        simp only [Nat.cast_zero, zero_mul, add_zero]
        linarith
      push_cast at hlog
      have : (F.kfhat : ℝ) < F.lamHat 0 / (2 * Real.log F.L) := by
        rw [lt_div_iff₀ hlpos]; nlinarith
      rw [hd]
      have h3 : (0 : ℝ) ≤ ((F.e : ℝ) + 2 + 3) / 2 := by positivity
      linarith

/-- **Lemma I.5.6 (b)**: the horizon conditions (H-λ) for `λ̂`, with `c_H = ((d+3)(d-2)/2) log L`:
under (Λ12), `k̂_f - k_0 < λ̂_{k_0}` and `λ̂_{k̂_f} ≤ (d/2) λ̂_{k_0} + c_H`. -/
theorem hLambda_of_flow (hkf : 1 ≤ F.kf)
    (hΛ12 : ((F.d : ℝ) + 3) / 2 ≤ F.lamHat F.k0 * (1 - 1 / (2 * Real.log F.L)))
    (hgen : F.beta F.k0 * F.nu F.k0 ≤ 1 → 2 * (F.L : ℝ) ^ 2 ≤ F.beta F.k0) :
    ((F.kfhat : ℝ) - F.k0 < F.lamHat F.k0) ∧
      F.lamHat F.kfhat ≤ (F.d : ℝ) / 2 * F.lamHat F.k0 + F.cH := by
  have hlL := F.log_L_gt
  have hlpos : 0 < 2 * Real.log F.L := by linarith
  have hd := F.d_eq
  have hlpos' : 0 < F.lamHat F.k0 := by
    have h1 : 0 < 1 - 1 / (2 * Real.log F.L) := by
      rw [sub_pos, div_lt_one hlpos]; linarith
    by_contra hcon
    push Not at hcon
    have : F.lamHat F.k0 * (1 - 1 / (2 * Real.log F.L)) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hcon h1.le
    have : (0 : ℝ) < ((F.d : ℝ) + 3) / 2 := by rw [hd]; positivity
    linarith
  have hb := F.kfhat_sub_k0_lt hkf hlpos'.le hgen
  have e1 : ((F.d : ℝ) + 3) / 2 + F.lamHat F.k0 / (2 * Real.log F.L) ≤ F.lamHat F.k0 := by
    have : F.lamHat F.k0 * (1 - 1 / (2 * Real.log F.L)) =
        F.lamHat F.k0 - F.lamHat F.k0 / (2 * Real.log F.L) := by ring
    linarith
  refine ⟨hb.trans_le e1, ?_⟩
  have hθ : 0 < (F.e : ℝ) * Real.log F.L := by
    have : 1 ≤ F.e := by have := F.hd; unfold e; omega
    have : (1 : ℝ) ≤ F.e := by exact_mod_cast this
    nlinarith
  have hsub := F.lamHat_sub F.kfhat F.k0
  have h2 : ((F.kfhat : ℝ) - F.k0) * ((F.e : ℝ) * Real.log F.L) ≤
      (((F.d : ℝ) + 3) / 2 + F.lamHat F.k0 / (2 * Real.log F.L)) * ((F.e : ℝ) * Real.log F.L) :=
    mul_le_mul_of_nonneg_right hb.le hθ.le
  have h3 : (((F.d : ℝ) + 3) / 2 + F.lamHat F.k0 / (2 * Real.log F.L)) * ((F.e : ℝ) * Real.log F.L) =
      ((F.d : ℝ) + 3) / 2 * ((F.e : ℝ) * Real.log F.L) + F.lamHat F.k0 * ((F.e : ℝ) / 2) := by
    field_simp
  unfold cH
  rw [hd] at *
  nlinarith

/-- The counter `S` is the one of the flow: `λ = λ̂`, `θ_± = θ`, `c_H`, `d`, `L`. -/
structure Matches (S : Setting) : Prop where
  d_eq : S.d = F.d
  L_eq : S.L = F.L
  lam_eq : ∀ j, S.lam j = F.lamHat j
  cH_eq : S.cH = F.cH

/-- **Lemma I.5.6 (b)** in the form of the hypotheses of `LF2`. -/
theorem hLambda_of_flow' {S : Setting} (hS : F.Matches S) (hkf : 1 ≤ F.kf)
    (hΛ12 : ((F.d : ℝ) + 3) / 2 ≤ S.lam F.k0 * (1 - 1 / (2 * Real.log F.L)))
    (hgen : F.beta F.k0 * F.nu F.k0 ≤ 1 → 2 * (F.L : ℝ) ^ 2 ≤ F.beta F.k0) :
    ((F.kfhat : ℝ) - F.k0 < S.lam F.k0) ∧
      S.lam F.kfhat ≤ (S.d : ℝ) / 2 * S.lam F.k0 + S.cH := by
  rw [hS.lam_eq] at hΛ12
  obtain ⟨h1, h2⟩ := F.hLambda_of_flow hkf hΛ12 hgen
  rw [hS.lam_eq, hS.lam_eq, hS.d_eq, hS.cH_eq]
  exact ⟨h1, h2⟩

/-- **Lemma I.5.6 (c)**, the lower bound on the tori: for a genuine `k_0 < k_f`,
`L^{k_f+1-k_0} ≥ e^{λ̂_{k_0}/2 - 1}/√2`. -/
theorem pow_kf_ge (hlt : F.k0 < F.kf) (hgenuine : F.beta F.k0 * F.nu F.k0 ≤ 1) :
    Real.exp (F.lamHat F.k0 / 2 - 1) / Real.sqrt 2 ≤ (F.L : ℝ) ^ (F.kf + 1 - F.k0) := by
  have hLpos := F.L_pos
  obtain ⟨w, hw⟩ : ∃ w, F.kf = F.k0 + w := ⟨F.kf - F.k0, by omega⟩
  have hBpos := F.beta_pos F.k0
  have hNpos := F.nu_pos F.k0
  have hX : F.nu F.kf = F.nu F.k0 * (F.L : ℝ) ^ (2 * w) * (F.δ F.kf / F.δ F.k0) := by
    have := F.delta_pos F.k0
    unfold nu
    rw [hw, show 2 * (F.k0 + w) = 2 * F.k0 + 2 * w by ring, pow_add]
    field_simp
  have hδ : F.δ F.kf / F.δ F.k0 ≤ 400 / 361 := by
    have h0 := F.delta_pos F.k0
    rw [div_le_iff₀ h0]
    nlinarith [(F.hδ F.k0).1, (F.hδ F.kf).2]
  set N := F.nu F.k0
  set B := F.beta F.k0
  set X := (F.L : ℝ) ^ (2 * w)
  have hXpos : 0 < X := by positivity
  have hQ : (0 : ℝ) < (F.L : ℝ) ^ 2 := by positivity
  have hkf := F.kf_spec
  rw [hX] at hkf
  have h1 : N * X * (F.δ F.kf / F.δ F.k0) ≤ N * X * (400 / 361) :=
    mul_le_mul_of_nonneg_left hδ (by positivity)
  have h2 : 7 / 8 / (F.L : ℝ) ^ 2 < N * X * (400 / 361) := lt_of_lt_of_le hkf h1
  rw [div_lt_iff₀ hQ] at h2
  have h3 : B * N ≤ 1 := hgenuine
  -- `X L² (7/8)(361/400) > B`
  have h4 : 7 / 8 * (361 / 400) * B < X * (F.L : ℝ) ^ 2 := by
    have h5 : 7 / 8 * B < B * (N * X * (400 / 361) * (F.L : ℝ) ^ 2) := by nlinarith
    have h6 : B * (N * X * (400 / 361) * (F.L : ℝ) ^ 2) ≤ X * (400 / 361) * (F.L : ℝ) ^ 2 := by
      have : B * N * (X * (400 / 361) * (F.L : ℝ) ^ 2) ≤ 1 * (X * (400 / 361) * (F.L : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_right h3 (by positivity)
      nlinarith
    nlinarith
  have h7 : 3 / 4 * B ≤ X * (F.L : ℝ) ^ 2 := by nlinarith
  have hbeta := F.beta_ge F.k0
  have h8 : 1 / 2 * Real.exp (F.lamHat F.k0 - 2) ≤ (F.L : ℝ) ^ (2 * (F.kf + 1 - F.k0)) := by
    have : (F.L : ℝ) ^ (2 * (F.kf + 1 - F.k0)) = X * (F.L : ℝ) ^ 2 := by
      rw [← pow_add]; congr 1; omega
    rw [this]; nlinarith
  have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have h9 : (Real.exp (F.lamHat F.k0 / 2 - 1) / Real.sqrt 2) ^ 2 ≤ ((F.L : ℝ) ^ (F.kf + 1 - F.k0)) ^ 2 := by
    rw [div_pow, Real.sq_sqrt (by norm_num), ← pow_mul, mul_comm (F.kf + 1 - F.k0) 2]
    have : Real.exp (F.lamHat F.k0 / 2 - 1) ^ 2 = Real.exp (F.lamHat F.k0 - 2) := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [this]
    linarith
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num)).mp h9

/-- **Lemma I.5.6 (c)**: (H-T) for the tori of the flow, `n_k ≥ 4ν_max(k)(crit_k+ω_k)+4` for
`1 ≤ k ≤ k_0` when `k_0 < k_f` is genuine, `n_k ≥ L^{k_f+1-k}` and (Λ13) holds at `λ̂_{k_0}`. -/
theorem hT_of_flow {S : Setting} (hS : F.Matches S) (ok : S.Ok) (n : ℕ → ℕ)
    (hlt : F.k0 < F.kf) (hgenuine : F.beta F.k0 * F.nu F.k0 ≤ 1)
    (hn : ∀ k, k ≤ F.kf + 1 → F.L ^ (F.kf + 1 - k) ≤ n k)
    (hΛ13 : 4 * S.nuBar (F.lamHat F.k0) * (S.critBar (F.lamHat F.k0) + S.omegaBar (F.lamHat F.k0)) + 4 ≤
      Real.exp (F.lamHat F.k0 / 2 - 1) / Real.sqrt 2) :
    ∀ k, 1 ≤ k → k ≤ F.k0 → 4 * S.numax k * (S.crit k + S.omega k) + 4 ≤ n k := by
  intro k hk1 hk0
  have hpow := F.pow_kf_ge hlt hgenuine
  have hnk : (F.L : ℝ) ^ (F.kf + 1 - F.k0) ≤ (n k : ℝ) := by
    have h1 : F.L ^ (F.kf + 1 - F.k0) ≤ F.L ^ (F.kf + 1 - k) :=
      Nat.pow_le_pow_right (by have := F.hL; omega) (by omega)
    have h2 := hn k (by omega)
    exact_mod_cast h1.trans h2
  have hx : S.lam k ≤ F.lamHat F.k0 := by
    rw [← hS.lam_eq]; exact ok.lam_mono hk0
  have hl0 : 0 ≤ S.lam k := (ok.lam_pos k).le
  have h1 := ok.numax_le_bar k
  have h2 := ok.crit_le_bar k
  have h3 := ok.omega_le_bar k
  have h1' := h1.trans (ok.nuBar_mono hl0 hx)
  have h2' := h2.trans (ok.critBar_mono hl0 hx)
  have h3' := h3.trans (ok.omegaBar_mono hl0 hx)
  have hnn : (0 : ℝ) ≤ S.numax k := Nat.cast_nonneg _
  have hcn : (0 : ℝ) ≤ S.crit k := Nat.cast_nonneg _
  have hon : (0 : ℝ) ≤ S.omega k := Nat.cast_nonneg _
  have hmain : (4 * (S.numax k : ℝ) * ((S.crit k : ℝ) + S.omega k) + 4) ≤ n k := by
    have : (S.numax k : ℝ) * ((S.crit k : ℝ) + S.omega k) ≤
        S.nuBar (F.lamHat F.k0) * (S.critBar (F.lamHat F.k0) + S.omegaBar (F.lamHat F.k0)) :=
      mul_le_mul h1' (add_le_add h2' h3') (by positivity) ((ok.nuBar_nonneg (by
        have := ok.lam_pos k; linarith)))
    linarith
  exact_mod_cast hmain

/-- The moduli of the running coefficients of `Balaban.Flow` (P4 (5.28), (H.6)) satisfy (I.2):
`‖γ_k‖, ‖δ_k‖ ∈ [19/20, 20/19]` when `ε = c₈ q/(1-q) ≤ 1/20`. -/
theorem running_bounds {q c₈ : ℝ} {ξ : ℕ → Fin 3 → ℂ} (hq0 : 0 ≤ q) (hq1 : q < 1) (hc : 0 ≤ c₈)
    (hs : c₈ * q ≤ 1 - q) (hξ : ∀ k, ‖ξ k‖ ≤ c₈ / 4 * q ^ (k + 1))
    (hε : c₈ * q / (1 - q) ≤ 1 / 20) (k : ℕ) :
    (19 / 20 ≤ ‖Balaban.Flow.gammaSeq ξ k‖ ∧ ‖Balaban.Flow.gammaSeq ξ k‖ ≤ 20 / 19) ∧
    (19 / 20 ≤ ‖Balaban.Flow.deltaSeq ξ k‖ ∧ ‖Balaban.Flow.deltaSeq ξ k‖ ≤ 20 / 19) := by
  obtain ⟨h1, h2, h3, h4⟩ := Balaban.Flow.norm_gammaSeq_le hq0 hq1 hc hs hξ k
  have hsum : c₈ * Balaban.Flow.ratePartialSum q k ≤ 1 / 20 := by
    have := Balaban.Flow.ratePartialSum_le hq0 hq1 k
    have h5 : c₈ * Balaban.Flow.ratePartialSum q k ≤ c₈ * (q / (1 - q)) :=
      mul_le_mul_of_nonneg_left this hc
    have h6 : c₈ * (q / (1 - q)) = c₈ * q / (1 - q) := by ring
    linarith
  set E := Real.exp (c₈ * Balaban.Flow.ratePartialSum q k) with hE
  have hE1 : E ≤ 20 / 19 := by
    have h7 : Real.exp (-(c₈ * Balaban.Flow.ratePartialSum q k)) ≥ 19 / 20 := by
      have := Real.add_one_le_exp (-(c₈ * Balaban.Flow.ratePartialSum q k))
      have h8 : 0 ≤ c₈ * Balaban.Flow.ratePartialSum q k := mul_nonneg hc (Finset.sum_nonneg
        fun j _ => by positivity)
      linarith
    rw [hE, Real.exp_neg] at *
    have hpos := Real.exp_pos (c₈ * Balaban.Flow.ratePartialSum q k)
    rw [ge_iff_le, le_inv_comm₀ (by norm_num) hpos] at h7
    linarith
  have hEpos : 0 < E := Real.exp_pos _
  have hE0 : 1 ≤ E := Real.one_le_exp (mul_nonneg hc (Finset.sum_nonneg fun j _ => by positivity))
  have lower : ∀ z : ℂ, z ≠ 0 → ‖z‖ ≤ E → ‖z⁻¹‖ ≤ E → 19 / 20 ≤ ‖z‖ ∧ ‖z‖ ≤ 20 / 19 := by
    intro z hz0 hz hzi
    refine ⟨?_, hz.trans hE1⟩
    rw [norm_inv] at hzi
    have hp : 0 < ‖z‖ := norm_pos_iff.mpr hz0
    rw [inv_le_comm₀ hp hEpos] at hzi
    have : (19 / 20 : ℝ) ≤ E⁻¹ := by
      rw [le_inv_comm₀ (by norm_num) hEpos]; linarith
    linarith
  have hq4 := Balaban.Flow.norm_le_quarter hq0 hq1 hc hs hξ
  have hne : ∀ j, (1 + ξ j 2 ≠ 0) ∧ (1 + ξ j 1 ≠ 0) := by
    intro j
    have c2 : ‖ξ j 2‖ ≤ 1 / 4 := (norm_le_pi_norm _ 2).trans (hq4 j)
    have c1 : ‖ξ j 1‖ ≤ 1 / 4 := (norm_le_pi_norm _ 1).trans (hq4 j)
    have key : ∀ z : ℂ, ‖z‖ ≤ 1 / 4 → 1 + z ≠ 0 := by
      intro z hz h
      have : z = -1 := by linear_combination h
      rw [this] at hz; simp at hz; linarith
    exact ⟨key _ c2, key _ c1⟩
  have hg0 : Balaban.Flow.gammaSeq ξ k ≠ 0 := by
    unfold Balaban.Flow.gammaSeq
    exact Finset.prod_ne_zero_iff.mpr fun j _ => inv_ne_zero (hne j).1
  have hd0 : Balaban.Flow.deltaSeq ξ k ≠ 0 := by
    unfold Balaban.Flow.deltaSeq
    exact Finset.prod_ne_zero_iff.mpr fun j _ => div_ne_zero (hne j).1 (hne j).2
  exact ⟨lower _ hg0 h1 h2, lower _ hd0 h3 h4⟩

end FlowSeq

/-- The flow data built from the running coefficients of `Balaban.Flow`: `γ_k = ‖gammaSeq ξ k‖`,
`δ_k = ‖deltaSeq ξ k‖`. -/
noncomputable def FlowSeq.ofRunning (d L : ℕ) (β ν a : ℝ) (hd : 3 ≤ d) (hL : 2 ≤ L) (hβ : 0 < β)
    (hν0 : 0 < ν) (hν1 : ν ≤ 1) (ha1 : 1 < a) (ha2 : a < 3 / 2) {q c₈ : ℝ} {ξ : ℕ → Fin 3 → ℂ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hc : 0 ≤ c₈) (hs : c₈ * q ≤ 1 - q)
    (hξ : ∀ k, ‖ξ k‖ ≤ c₈ / 4 * q ^ (k + 1)) (hε : c₈ * q / (1 - q) ≤ 1 / 20) : FlowSeq where
  d := d
  L := L
  β := β
  ν := ν
  a := a
  γ k := ‖Balaban.Flow.gammaSeq ξ k‖
  δ k := ‖Balaban.Flow.deltaSeq ξ k‖
  hd := hd
  hL := hL
  hβ := hβ
  hν0 := hν0
  hν1 := hν1
  ha1 := ha1
  ha2 := ha2
  hγ k := (FlowSeq.running_bounds hq0 hq1 hc hs hξ hε k).1
  hδ k := (FlowSeq.running_bounds hq0 hq1 hc hs hξ hε k).2
  hγ0 := by simp [Balaban.Flow.gammaSeq]
  hδ0 := by simp [Balaban.Flow.deltaSeq]

/-- `β_k` of the flow data is the modulus of `Flow.betaSeq` (`betaSeq_eq`). -/
theorem FlowSeq.ofRunning_beta (d L : ℕ) (β ν a : ℝ) (hd : 3 ≤ d) (hL : 2 ≤ L) (hβ : 0 < β)
    (hν0 : 0 < ν) (hν1 : ν ≤ 1) (ha1 : 1 < a) (ha2 : a < 3 / 2) {q c₈ : ℝ} {ξ : ℕ → Fin 3 → ℂ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hc : 0 ≤ c₈) (hs : c₈ * q ≤ 1 - q)
    (hξ : ∀ k, ‖ξ k‖ ≤ c₈ / 4 * q ^ (k + 1)) (hε : c₈ * q / (1 - q) ≤ 1 / 20) (k : ℕ) :
    (FlowSeq.ofRunning d L β ν a hd hL hβ hν0 hν1 ha1 ha2 hq0 hq1 hc hs hξ hε).beta k =
      ‖Balaban.Flow.betaSeq (L : ℝ) d ξ (β : ℂ) k‖ := by
  rw [Balaban.Flow.betaSeq_eq, norm_mul, norm_mul, norm_pow]
  simp [FlowSeq.beta, FlowSeq.ofRunning, FlowSeq.e, abs_of_pos hβ]

/-- `ν_k` of the flow data is the modulus of `Flow.nuSeq` (`nuSeq_eq`). -/
theorem FlowSeq.ofRunning_nu (d L : ℕ) (β ν a : ℝ) (hd : 3 ≤ d) (hL : 2 ≤ L) (hβ : 0 < β)
    (hν0 : 0 < ν) (hν1 : ν ≤ 1) (ha1 : 1 < a) (ha2 : a < 3 / 2) {q c₈ : ℝ} {ξ : ℕ → Fin 3 → ℂ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hc : 0 ≤ c₈) (hs : c₈ * q ≤ 1 - q)
    (hξ : ∀ k, ‖ξ k‖ ≤ c₈ / 4 * q ^ (k + 1)) (hε : c₈ * q / (1 - q) ≤ 1 / 20) (k : ℕ) :
    (FlowSeq.ofRunning d L β ν a hd hL hβ hν0 hν1 ha1 ha2 hq0 hq1 hc hs hξ hε).nu k =
      ‖Balaban.Flow.nuSeq (L : ℝ) ξ (ν : ℂ) k‖ := by
  rw [Balaban.Flow.nuSeq_eq, norm_mul, norm_mul, norm_pow]
  simp [FlowSeq.nu, FlowSeq.ofRunning, abs_of_pos hν0]

end Balaban.LargeField
