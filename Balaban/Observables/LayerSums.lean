/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Observables.LayerDef
public import Balaban.Correlations.Series

/-!
# Lemma 2.3: the sums of the observable layer (OBSERVABLES.md §2.3)

First the real-variable core (no structure involved):

* `inner_geom`: `∑_{j=i}^k L^{-jρ₀} ≤ L^{-iρ₀}/(1 - L^{-ρ₀})`;
* `core_series`: `∑_{i ≤ j ≤ k} L^{-(i-1)(d-2)} L^{-jρ₀} e^{-δ₀ L^{-i} z} ≤ C (1+z)^{-(d-2+ρ₀)}
  e^{-(δ₀/2) s z/L²}` whenever `L^k s ≤ L²` (the mass factor, with `s = √ν`).
-/

@[expose] public section

open Finset

namespace Balaban.Observables

theorem inner_geom {Lr ρ₀ : ℝ} (hL : 1 < Lr) (hρ₀ : 0 < ρ₀) (i k : ℕ) :
    ∑ j ∈ Finset.Icc i k, Lr ^ (-((j : ℝ) * ρ₀)) ≤ Lr ^ (-((i : ℝ) * ρ₀)) / (1 - Lr ^ (-ρ₀)) := by
  have hρ : Lr ^ (-ρ₀) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hL (by linarith)
  have hρ0 : 0 ≤ Lr ^ (-ρ₀) := Real.rpow_nonneg (by linarith) _
  have e : ∀ j : ℕ, Lr ^ (-((j : ℝ) * ρ₀)) = (Lr ^ (-ρ₀)) ^ j := by
    intro j
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
    ring_nf
  simp_rw [e]
  have h := geom_sum_Ico_le_of_lt_one (m := i) (n := k + 1) hρ0 hρ
  have hIcc : Finset.Icc i k = Finset.Ico i (k + 1) := by
    ext x; simp
  rw [hIcc]
  exact h

/-- **The real-variable core of Lemma 2.3 (b)**. -/
theorem core_series {d L : ℕ} (hd : 2 ≤ d) (hL : 2 ≤ L) {ρ₀ δ₀ : ℝ} (hρ₀ : 0 < ρ₀)
    (hδ₀ : 0 < δ₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ) (z s : ℝ), 0 ≤ z → 0 ≤ s → (L : ℝ) ^ k * s ≤ (L : ℝ) ^ 2 →
      ∑ i ∈ Icc 1 k, ∑ j ∈ Icc i k, ((L : ℝ) ^ ((i - 1) * (d - 2)))⁻¹ *
          (L : ℝ) ^ (-((j : ℝ) * ρ₀)) * Real.exp (-(δ₀ * ((L : ℝ) ^ i)⁻¹ * z)) ≤
        C * (1 + z) ^ (-(((d : ℝ) - 2) + ρ₀)) * Real.exp (-(δ₀ / 2 * s * z / (L : ℝ) ^ 2)) := by
  set Lr : ℝ := (L : ℝ) with hLr
  have hL1 : 1 < Lr := by
    have : (2 : ℝ) ≤ L := by exact_mod_cast hL
    linarith
  have hL0 : 0 < Lr := by linarith
  have hd2 : (0 : ℝ) ≤ (d : ℝ) - 2 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  set σ : ℝ := ((d : ℝ) - 2) + ρ₀ with hσ
  have hσ0 : 0 < σ := by rw [hσ]; linarith
  have ha : 0 < δ₀ / 2 / Lr := by positivity
  obtain ⟨C1, hC1, hC1'⟩ := Balaban.Correlations.sum_pow_exp_le hσ0 ha hL1
  have hρ1 : Lr ^ (-ρ₀) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hL1 (by linarith)
  have hρ0 : 0 < 1 - Lr ^ (-ρ₀) := by linarith
  refine ⟨Lr ^ (d - 2) / (1 - Lr ^ (-ρ₀)) * Lr ^ (-σ) * C1, by positivity, ?_⟩
  intro k z s hz hs hks
  -- the exponent identity
  have hpow : ∀ i : ℕ, 1 ≤ i →
      (Lr ^ ((i - 1) * (d - 2)))⁻¹ * Lr ^ (-((i : ℝ) * ρ₀)) =
        Lr ^ (d - 2) * Lr ^ (-((i : ℝ) * σ)) := by
    intro i hi
    obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
    have e1 : (Lr ^ ((m + 1 - 1) * (d - 2)))⁻¹ = Lr ^ (-((m : ℝ) * ((d : ℝ) - 2))) := by
      rw [Nat.add_sub_cancel, Real.rpow_neg hL0.le, ← Real.rpow_natCast]
      congr 2
      push_cast [Nat.cast_sub hd]
      ring
    have e2 : Lr ^ (d - 2) = Lr ^ (((d : ℝ) - 2)) := by
      rw [← Real.rpow_natCast]; congr 1; push_cast [Nat.cast_sub hd]; ring
    rw [e1, e2, ← Real.rpow_add hL0, ← Real.rpow_add hL0]
    congr 1
    rw [hσ]
    push_cast
    ring
  -- the mass factor
  have hmass : ∀ i ∈ Icc 1 k, s / Lr ^ 2 ≤ (Lr ^ i)⁻¹ := by
    intro i hi
    have hik : i ≤ k := (Finset.mem_Icc.1 hi).2
    have h1 : Lr ^ i ≤ Lr ^ k := pow_le_pow_right₀ hL1.le hik
    have h2 : s / Lr ^ 2 ≤ (Lr ^ k)⁻¹ := by
      rw [div_le_iff₀ (by positivity), inv_mul_eq_div, le_div_iff₀ (by positivity)]
      linarith
    exact h2.trans (inv_anti₀ (by positivity) h1)
  have hstep : ∀ i ∈ Icc 1 k, ∑ j ∈ Icc i k, (Lr ^ ((i - 1) * (d - 2)))⁻¹ *
      Lr ^ (-((j : ℝ) * ρ₀)) * Real.exp (-(δ₀ * (Lr ^ i)⁻¹ * z)) ≤
      Lr ^ (d - 2) / (1 - Lr ^ (-ρ₀)) *
        (Lr ^ (-((i : ℝ) * σ)) * Real.exp (-(δ₀ / 2 / Lr * z / Lr ^ (i - 1)))) *
        Real.exp (-(δ₀ / 2 * s * z / Lr ^ 2)) := by
    intro i hi
    have hi1 : 1 ≤ i := (Finset.mem_Icc.1 hi).1
    have hgeo := inner_geom hL1 hρ₀ i k
    have hsum : ∑ j ∈ Icc i k, (Lr ^ ((i - 1) * (d - 2)))⁻¹ * Lr ^ (-((j : ℝ) * ρ₀)) *
        Real.exp (-(δ₀ * (Lr ^ i)⁻¹ * z)) =
        (Lr ^ ((i - 1) * (d - 2)))⁻¹ * Real.exp (-(δ₀ * (Lr ^ i)⁻¹ * z)) *
          ∑ j ∈ Icc i k, Lr ^ (-((j : ℝ) * ρ₀)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    have hexp : Real.exp (-(δ₀ * (Lr ^ i)⁻¹ * z)) ≤
        Real.exp (-(δ₀ / 2 / Lr * z / Lr ^ (i - 1))) * Real.exp (-(δ₀ / 2 * s * z / Lr ^ 2)) := by
      rw [← Real.exp_add, Real.exp_le_exp]
      have h1 : δ₀ / 2 * s * z / Lr ^ 2 = δ₀ / 2 * z * (s / Lr ^ 2) := by ring
      have h2 : δ₀ / 2 / Lr * z / Lr ^ (i - 1) = δ₀ / 2 * z * (Lr ^ i)⁻¹ := by
        obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
        rw [Nat.add_sub_cancel, pow_succ]
        field_simp
      have h3 : δ₀ / 2 * z * (s / Lr ^ 2) ≤ δ₀ / 2 * z * (Lr ^ i)⁻¹ :=
        mul_le_mul_of_nonneg_left (hmass i hi) (by positivity)
      rw [h1, h2]
      nlinarith
    rw [hsum]
    calc (Lr ^ ((i - 1) * (d - 2)))⁻¹ * Real.exp (-(δ₀ * (Lr ^ i)⁻¹ * z)) *
          ∑ j ∈ Icc i k, Lr ^ (-((j : ℝ) * ρ₀))
        ≤ (Lr ^ ((i - 1) * (d - 2)))⁻¹ * (Real.exp (-(δ₀ / 2 / Lr * z / Lr ^ (i - 1))) *
            Real.exp (-(δ₀ / 2 * s * z / Lr ^ 2))) *
          (Lr ^ (-((i : ℝ) * ρ₀)) / (1 - Lr ^ (-ρ₀))) := by
          gcongr
      _ = (Lr ^ ((i - 1) * (d - 2)))⁻¹ * Lr ^ (-((i : ℝ) * ρ₀)) / (1 - Lr ^ (-ρ₀)) *
          Real.exp (-(δ₀ / 2 / Lr * z / Lr ^ (i - 1))) *
          Real.exp (-(δ₀ / 2 * s * z / Lr ^ 2)) := by ring
      _ = _ := by rw [hpow i hi1]; ring
  refine (Finset.sum_le_sum hstep).trans ?_
  -- the shifted sum
  have hshift : ∑ i ∈ Icc 1 k, Lr ^ (-((i : ℝ) * σ)) *
      Real.exp (-(δ₀ / 2 / Lr * z / Lr ^ (i - 1))) =
      Lr ^ (-σ) * ∑ j ∈ range k, Lr ^ (-((j : ℝ) * σ)) *
        Real.exp (-(δ₀ / 2 / Lr * z / Lr ^ j)) := by
    have hIcc : Finset.Icc 1 k = Finset.Ico 1 (k + 1) := by ext x; simp
    rw [hIcc, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have : Lr ^ (-(((1 + j : ℕ) : ℝ) * σ)) = Lr ^ (-σ) * Lr ^ (-((j : ℝ) * σ)) := by
      rw [← Real.rpow_add hL0]; congr 1; push_cast; ring
    rw [this]
    have : 1 + j - 1 = j := by omega
    rw [this]; ring
  have hmain := hC1' k z hz
  rw [← Finset.sum_mul, ← Finset.mul_sum, hshift]
  have h2 : ∑ j ∈ range k, Lr ^ (-((j : ℝ) * σ)) * Real.exp (-(δ₀ / 2 / Lr * z / Lr ^ j)) ≤
      C1 * (1 + z) ^ (-σ) := by
    exact hmain
  calc _ ≤ Lr ^ (d - 2) / (1 - Lr ^ (-ρ₀)) * (Lr ^ (-σ) * (C1 * (1 + z) ^ (-σ))) *
        Real.exp (-(δ₀ / 2 * s * z / Lr ^ 2)) := by gcongr
    _ = _ := by ring

/-! ### The running coupling is positive and grows like `L^{n(d-2)}` -/

open Balaban.SmallField.Def6 in
/-- From the coefficient bounds (H.6): for `n ≤ k`, `β_n > 0` and `β_n ≥ β L^{n(d-2)}/e`
(`β = β_0 > 0`; `γ_n` is real with `‖γ_n - 1‖ < 1` and `‖γ_n⁻¹‖ ≤ e`). -/
theorem beta_pos_lower {d L k : ℕ} (hL : 2 ≤ L) {P : Consts} (hP : P.Admissible d L)
    {β ν a : ℕ → ℝ} (hc : CoeffBounds d L k P β ν a) (hβ0 : 0 < β 0) {n : ℕ} (hn : n ≤ k) :
    0 < β n ∧ β 0 * (L : ℝ) ^ (n * (d - 2)) / Real.exp 1 ≤ β n := by
  obtain ⟨ξ, β₀, ν₀, hξ, hs, hflow⟩ := hc.flow
  have hLr : (1 : ℝ) < L := by
    have : (2 : ℝ) ≤ L := by exact_mod_cast hL
    linarith
  set q : ℝ := Flow.rate (L : ℝ) P.γ with hq
  have hq0 : 0 ≤ q := (Flow.rate_pos (by linarith) _).le
  have hq1 : q < 1 := Flow.rate_lt_one hLr hP.γ_pos
  have hc8 : 0 ≤ P.c₈ := hP.c₈_pos.le
  have hβ0' : β₀ = β 0 := by
    have := (hflow 0 (Nat.zero_le _)).1
    simpa [Flow.betaSeq] using this.symm
  have hβn : ((β n : ℝ) : ℂ) = (β₀ : ℂ) * (L : ℂ) ^ (n * (d - 2)) * Flow.gammaSeq ξ n := by
    rw [(hflow n hn).1, Flow.betaSeq_eq]
    push_cast
    rfl
  have hu : P.c₈ * q / (1 - q) ≤ 1 := by
    rw [div_le_iff₀ (by linarith)]; linarith
  obtain ⟨γ, δ, -, -, hγ1, hγj, -, -, -, -, -⟩ := Flow.exists_gamma_infty hq0 hq1 hc8 hs hξ
  have hq' : 0 < 1 - q := by linarith
  -- `γ_n` has positive real part
  have hre : 0 < (Flow.gammaSeq ξ n).re := by
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp [Flow.gammaSeq]
    · have h1 : ‖Flow.gammaSeq ξ n - 1‖ < 1 := by
        have h2 := hγj n
        calc ‖Flow.gammaSeq ξ n - 1‖ = ‖(Flow.gammaSeq ξ n - γ) + (γ - 1)‖ := by ring_nf
          _ ≤ ‖Flow.gammaSeq ξ n - γ‖ + ‖γ - 1‖ := norm_add_le _ _
          _ ≤ P.c₈ * q ^ (n + 1) / (2 * (1 - q)) + P.c₈ * q / (2 * (1 - q)) := add_le_add h2 hγ1
          _ < 1 := by
            have hqn : q ^ (n + 1) ≤ q * q := by
              rw [pow_succ']
              exact mul_le_mul_of_nonneg_left (by
                calc q ^ n ≤ q ^ 1 := pow_le_pow_of_le_one hq0 hq1.le hpos
                  _ = q := pow_one q) hq0
            have hcq : P.c₈ * q ≤ 1 - q := hs
            have : P.c₈ * q ^ (n + 1) + P.c₈ * q < 2 * (1 - q) := by
              nlinarith [mul_le_mul_of_nonneg_left hqn hc8]
            rw [← add_div, div_lt_one (by linarith)]
            linarith
      have := Complex.abs_re_le_norm (Flow.gammaSeq ξ n - 1)
      have h3 : |(Flow.gammaSeq ξ n - 1).re| < 1 := lt_of_le_of_lt this h1
      have h4 := (abs_lt.1 h3).1
      simp at h4
      linarith
  -- `γ_n` is real
  have hβ0pos : 0 < β₀ := hβ0' ▸ hβ0
  have hpowne : ((L : ℂ) ^ (n * (d - 2))) ≠ 0 := pow_ne_zero _ (by
    have : (L : ℂ) ≠ 0 := by exact_mod_cast (by omega : L ≠ 0)
    exact this)
  have hγreal : Flow.gammaSeq ξ n = ((Flow.gammaSeq ξ n).re : ℂ) := by
    have h1 : Flow.gammaSeq ξ n = ((β n : ℝ) : ℂ) / ((β₀ : ℂ) * (L : ℂ) ^ (n * (d - 2))) := by
      rw [hβn]
      have : (β₀ : ℂ) ≠ 0 := by exact_mod_cast hβ0pos.ne'
      field_simp
    have hreal : (((β n : ℝ) : ℂ) / ((β₀ : ℂ) * (L : ℂ) ^ (n * (d - 2)))).im = 0 := by
      have : ((β₀ : ℂ) * (L : ℂ) ^ (n * (d - 2))) = (((β₀ * (L : ℝ) ^ (n * (d - 2)) : ℝ)) : ℂ) := by
        push_cast; ring
      rw [this, ← Complex.ofReal_div]
      exact Complex.ofReal_im _
    apply Complex.ext
    · simp
    · rw [h1]; simp [hreal]
  -- the lower bound
  have hnorm : Real.exp (-1) ≤ (Flow.gammaSeq ξ n).re := by
    have hb := (Flow.norm_gammaSeq_le hq0 hq1 hc8 hs hξ n).2.1
    have hps : P.c₈ * Flow.ratePartialSum q n ≤ 1 := by
      calc P.c₈ * Flow.ratePartialSum q n ≤ P.c₈ * (q / (1 - q)) :=
            mul_le_mul_of_nonneg_left (Flow.ratePartialSum_le hq0 hq1 n) hc8
        _ = P.c₈ * q / (1 - q) := by ring
        _ ≤ 1 := hu
    have hinv : ‖(Flow.gammaSeq ξ n)⁻¹‖ ≤ Real.exp 1 := hb.trans (Real.exp_le_exp.mpr hps)
    have hgne : Flow.gammaSeq ξ n ≠ 0 := Flow.gammaSeq_ne_zero hq0 hq1 hc8 hs hξ n
    have hgpos : 0 < ‖Flow.gammaSeq ξ n‖ := norm_pos_iff.2 hgne
    have hone : ‖Flow.gammaSeq ξ n‖ * ‖(Flow.gammaSeq ξ n)⁻¹‖ = 1 := by
      rw [← norm_mul, mul_inv_cancel₀ hgne, norm_one]
    have h1 : 1 ≤ ‖Flow.gammaSeq ξ n‖ * Real.exp 1 := by
      calc (1 : ℝ) = ‖Flow.gammaSeq ξ n‖ * ‖(Flow.gammaSeq ξ n)⁻¹‖ := hone.symm
        _ ≤ ‖Flow.gammaSeq ξ n‖ * Real.exp 1 := mul_le_mul_of_nonneg_left hinv hgpos.le
    have h2 : ‖Flow.gammaSeq ξ n‖ = (Flow.gammaSeq ξ n).re := by
      conv_lhs => rw [hγreal]
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hre]
    rw [← h2, Real.exp_neg]
    rw [inv_le_iff_one_le_mul₀ (Real.exp_pos 1)]
    linarith
  have hβn_eq : β n = β 0 * (L : ℝ) ^ (n * (d - 2)) * (Flow.gammaSeq ξ n).re := by
    have hcast : ((β n : ℝ) : ℂ) =
        ((β₀ * (L : ℝ) ^ (n * (d - 2)) * (Flow.gammaSeq ξ n).re : ℝ) : ℂ) := by
      rw [hβn]
      conv_lhs => rw [hγreal]
      push_cast
      ring
    rw [← hβ0']
    exact_mod_cast hcast
  have hLpos : 0 < (L : ℝ) ^ (n * (d - 2)) := by positivity
  refine ⟨?_, ?_⟩
  · rw [hβn_eq]; positivity
  · rw [hβn_eq, div_le_iff₀ (Real.exp_pos 1)]
    have h1 : 0 < β 0 * (L : ℝ) ^ (n * (d - 2)) := by positivity
    have h2 : 1 ≤ (Flow.gammaSeq ξ n).re * Real.exp 1 := by
      have := mul_le_mul_of_nonneg_right hnorm (Real.exp_pos 1).le
      rw [← Real.exp_add] at this
      simpa using this
    nlinarith

/-! ### Lemma 2.3 -/

section Lemma23

open Balaban Balaban.SmallField Balaban.SmallField.Def6 Balaban.Localization Balaban.Multiscale

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- The constant of Lemma 2.3 (a): `√e · L^{-ρ₀}/(1 - L^{-ρ₀})`. -/
noncomputable def obsC1 (L : ℕ) (ρ₀ : ℝ) : ℝ :=
  Real.sqrt (Real.exp 1) * ((L : ℝ) ^ (-ρ₀) / (1 - (L : ℝ) ^ (-ρ₀)))

theorem obsC1_nonneg {L : ℕ} (hL : 2 ≤ L) {ρ₀ : ℝ} (hρ₀ : 0 < ρ₀) : 0 ≤ obsC1 L ρ₀ := by
  have hLr : (1 : ℝ) < L := by
    have : (2 : ℝ) ≤ L := by exact_mod_cast hL
    linarith
  have h1 : (L : ℝ) ^ (-ρ₀) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hLr (by linarith)
  have h0 : 0 ≤ (L : ℝ) ^ (-ρ₀) := Real.rpow_nonneg (by linarith) _
  unfold obsC1
  have : 0 < 1 - (L : ℝ) ^ (-ρ₀) := by linarith
  positivity

/-- **Lemma 2.3 (a)**: `|m_k(x) - 1| ≤ C β^{-1+ρ₁}`, `C = obsC1 L ρ₀`, from (O1) and the growth
of the running coupling. -/
theorem mFactor_sub_one_le (hL : 2 ≤ L) {P : Consts} (hP : P.Admissible d L) {Q : ObsConsts}
    (hQ : Q.ρ₀ > 0) {β ν a : ℕ → ℝ} {Tm : Terms d L N₁ m₁ k N ϱ} {Ot : ObsTerms d L N₁ m₁ k N}
    {Gker : ℕ → CTorus d L N₁ m₁ k → CTorus d L N₁ m₁ k → Fld d L N₁ m₁ k N →
      Fld d L N₁ m₁ k N → Matrix (Fin N) (Fin N) ℂ}
    (hc : CoeffBounds d L k P β ν a) (hO : IsObs P Q β ν a Tm Ot Gker) (hβ0 : 0 < β 0)
    (x : CTorus d L N₁ m₁ k) :
    |mFactor β Ot x - 1| ≤ obsC1 L Q.ρ₀ * (β 0) ^ (-1 + Q.ρ₁) := by
  have hLr : (1 : ℝ) < L := by
    have : (2 : ℝ) ≤ L := by exact_mod_cast hL
    linarith
  have hterm : ∀ j ∈ Icc 1 k, |(Real.sqrt (β (j - 1)))⁻¹ * Ot.μ j x| ≤
      Real.sqrt (Real.exp 1) * (β 0) ^ (-1 + Q.ρ₁) * (L : ℝ) ^ (-((j : ℝ) * Q.ρ₀)) := by
    intro j hj
    have hj1 : 1 ≤ j := (Finset.mem_Icc.1 hj).1
    have hjk : j ≤ k := (Finset.mem_Icc.1 hj).2
    obtain ⟨hpos, hlow⟩ := beta_pos_lower hL hP hc hβ0 (n := j - 1) (by omega)
    have hLp : (1 : ℝ) ≤ (L : ℝ) ^ ((j - 1) * (d - 2)) := one_le_pow₀ hLr.le
    have hlow' : β 0 / Real.exp 1 ≤ β (j - 1) := by
      refine le_trans ?_ hlow
      rw [div_le_div_iff_of_pos_right (Real.exp_pos 1)]
      nlinarith
    have hsq : Real.sqrt (β 0) / Real.sqrt (Real.exp 1) ≤ Real.sqrt (β (j - 1)) := by
      rw [← Real.sqrt_div hβ0.le]
      exact Real.sqrt_le_sqrt hlow'
    have hsq0 : 0 < Real.sqrt (β 0) / Real.sqrt (Real.exp 1) := by
      have := Real.sqrt_pos.2 hβ0
      have := Real.sqrt_pos.2 (Real.exp_pos 1)
      positivity
    have hinv : (Real.sqrt (β (j - 1)))⁻¹ ≤ Real.sqrt (Real.exp 1) / Real.sqrt (β 0) := by
      calc (Real.sqrt (β (j - 1)))⁻¹ ≤ (Real.sqrt (β 0) / Real.sqrt (Real.exp 1))⁻¹ :=
            inv_anti₀ hsq0 hsq
        _ = _ := by rw [inv_div]
    have hμ := hO.μ_bound j hj1 hjk x
    rw [abs_mul, abs_of_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _))]
    calc (Real.sqrt (β (j - 1)))⁻¹ * |Ot.μ j x|
        ≤ (Real.sqrt (Real.exp 1) / Real.sqrt (β 0)) *
          ((β 0) ^ (-(1 / 2 : ℝ) + Q.ρ₁) * (L : ℝ) ^ (-((j : ℝ) * Q.ρ₀))) := by
          gcongr
      _ = Real.sqrt (Real.exp 1) * (β 0) ^ (-1 + Q.ρ₁) * (L : ℝ) ^ (-((j : ℝ) * Q.ρ₀)) := by
          have h1 : (β 0) ^ (-1 + Q.ρ₁) = (β 0) ^ (-(1 / 2 : ℝ)) * (β 0) ^ (-(1 / 2 : ℝ) + Q.ρ₁) := by
            rw [← Real.rpow_add hβ0]; congr 1; ring
          have h2 : (β 0) ^ (-(1 / 2 : ℝ)) = (Real.sqrt (β 0))⁻¹ := by
            rw [Real.sqrt_eq_rpow, Real.rpow_neg hβ0.le]
          rw [h1, h2]
          field_simp
  unfold mFactor
  rw [show 1 - ∑ j ∈ Finset.Icc 1 k, (Real.sqrt (β (j - 1)))⁻¹ * Ot.μ j x - 1 =
      -∑ j ∈ Finset.Icc 1 k, (Real.sqrt (β (j - 1)))⁻¹ * Ot.μ j x by ring, abs_neg]
  calc |∑ j ∈ Finset.Icc 1 k, (Real.sqrt (β (j - 1)))⁻¹ * Ot.μ j x|
      ≤ ∑ j ∈ Finset.Icc 1 k, |(Real.sqrt (β (j - 1)))⁻¹ * Ot.μ j x| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.Icc 1 k, Real.sqrt (Real.exp 1) * (β 0) ^ (-1 + Q.ρ₁) *
          (L : ℝ) ^ (-((j : ℝ) * Q.ρ₀)) := Finset.sum_le_sum hterm
    _ = Real.sqrt (Real.exp 1) * (β 0) ^ (-1 + Q.ρ₁) *
          ∑ j ∈ Finset.Icc 1 k, (L : ℝ) ^ (-((j : ℝ) * Q.ρ₀)) := by rw [Finset.mul_sum]
    _ ≤ Real.sqrt (Real.exp 1) * (β 0) ^ (-1 + Q.ρ₁) *
          ((L : ℝ) ^ (-((1 : ℕ) * Q.ρ₀)) / (1 - (L : ℝ) ^ (-Q.ρ₀))) := by
        gcongr
        exact inner_geom hLr hQ 1 k
    _ = obsC1 L Q.ρ₀ * (β 0) ^ (-1 + Q.ρ₁) := by
        unfold obsC1
        norm_num
        ring

/-- **Lemma 2.3 (a), the bound `|m_k| ≤ 2`**: if `C β^{-1+ρ₁} ≤ 1` (`β ≥ β₁`, see
`exists_beta_threshold`) then `|m_k(x) - 1| ≤ 1`, so `|m_k(x)| ≤ 2` and `m_k ≥ 0`. -/
theorem abs_mFactor_le_two (hL : 2 ≤ L) {P : Consts} (hP : P.Admissible d L) {Q : ObsConsts}
    (hQ : Q.ρ₀ > 0) {β ν a : ℕ → ℝ} {Tm : Terms d L N₁ m₁ k N ϱ} {Ot : ObsTerms d L N₁ m₁ k N}
    {Gker : ℕ → CTorus d L N₁ m₁ k → CTorus d L N₁ m₁ k → Fld d L N₁ m₁ k N →
      Fld d L N₁ m₁ k N → Matrix (Fin N) (Fin N) ℂ}
    (hc : CoeffBounds d L k P β ν a) (hO : IsObs P Q β ν a Tm Ot Gker) (hβ0 : 0 < β 0)
    (hsmall : obsC1 L Q.ρ₀ * (β 0) ^ (-1 + Q.ρ₁) ≤ 1) (x : CTorus d L N₁ m₁ k) :
    |mFactor β Ot x| ≤ 2 := by
  have h := mFactor_sub_one_le hL hP hQ hc hO hβ0 x
  have h1 : |mFactor β Ot x - 1| ≤ 1 := h.trans hsmall
  have := abs_le.1 h1
  rw [abs_le]
  constructor <;> linarith [this.1, this.2]

/-- The threshold `β₁` of Lemma 2.3: `C b^{-1+ρ₁} ≤ 1` for `b ≥ β₁` (`ρ₁ < 1`, `C ≥ 0`). -/
theorem exists_beta_threshold {C ρ₁ : ℝ} (hC : 0 ≤ C) (hρ₁ : ρ₁ < 1) :
    ∃ β₁ : ℝ, 0 < β₁ ∧ ∀ b : ℝ, β₁ ≤ b → C * b ^ (-1 + ρ₁) ≤ 1 := by
  refine ⟨max 1 (C ^ (1 / (1 - ρ₁))), lt_of_lt_of_le one_pos (le_max_left _ _), fun b hb => ?_⟩
  have hb1 : 1 ≤ b := (le_max_left _ _).trans hb
  have hb0 : 0 < b := by linarith
  have h1ρ : 0 < 1 - ρ₁ := by linarith
  have hb2 : C ^ (1 / (1 - ρ₁)) ≤ b := (le_max_right _ _).trans hb
  have h3 : C ≤ b ^ (1 - ρ₁) := by
    calc C = (C ^ (1 / (1 - ρ₁))) ^ (1 - ρ₁) := by
          rw [← Real.rpow_mul hC]; field_simp; simp
      _ ≤ b ^ (1 - ρ₁) := Real.rpow_le_rpow (Real.rpow_nonneg hC _) hb2 h1ρ.le
  have h4 : b ^ (-1 + ρ₁) = (b ^ (1 - ρ₁))⁻¹ := by
    rw [← Real.rpow_neg hb0.le]; congr 1; ring
  rw [h4]
  have hpos : 0 < b ^ (1 - ρ₁) := Real.rpow_pos_of_pos hb0 _
  rw [← div_eq_mul_inv, div_le_one hpos]
  exact h3

/-- The sup-norm distance of two sites of the torus (representatives of minimal absolute
value). -/
noncomputable def torusDist (x x' : CTorus d L N₁ m₁ k) : ℝ :=
  ((Finset.univ.sup fun μ : Fin d => (ZMod.valMinAbs (x μ - x' μ)).natAbs : ℕ) : ℝ)

omit [NeZero L] [NeZero N₁] in
theorem torusDist_nonneg (x x' : CTorus d L N₁ m₁ k) : 0 ≤ torusDist x x' := Nat.cast_nonneg _

omit [NeZero L] [NeZero N₁] in
theorem torusL1_nonneg (x x' : CTorus d L N₁ m₁ k) : 0 ≤ torusL1 x x' :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

omit [NeZero L] [NeZero N₁] in
theorem torusDist_le_torusL1 (x x' : CTorus d L N₁ m₁ k) : torusDist x x' ≤ torusL1 x x' := by
  have h : (Finset.univ.sup fun μ : Fin d => (ZMod.valMinAbs (x μ - x' μ)).natAbs) ≤
      ∑ μ : Fin d, (ZMod.valMinAbs (x μ - x' μ)).natAbs :=
    Finset.sup_le fun μ hμ => Finset.single_le_sum (f := fun μ : Fin d =>
      (ZMod.valMinAbs (x μ - x' μ)).natAbs) (fun _ _ => Nat.zero_le _) hμ
  have h2 : ((Finset.univ.sup fun μ : Fin d => (ZMod.valMinAbs (x μ - x' μ)).natAbs : ℕ) : ℝ) ≤
      ((∑ μ : Fin d, (ZMod.valMinAbs (x μ - x' μ)).natAbs : ℕ) : ℝ) := by exact_mod_cast h
  refine h2.trans (le_of_eq ?_)
  unfold torusL1
  push_cast
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Nat.cast_natAbs, Int.cast_abs]

theorem finsum_mem_le_mul {α : Type*} [Finite α] {S : Set α} {f g : α → ℝ} {c : ℝ}
    (h : ∀ X ∈ S, f X ≤ c * g X) :
    ∑ᶠ X ∈ S, f X ≤ c * ∑ᶠ X ∈ S, g X := by
  have hS : S.Finite := Set.toFinite S
  rw [finsum_mem_eq_finite_toFinset_sum f hS, finsum_mem_eq_finite_toFinset_sum g hS,
    Finset.mul_sum]
  exact Finset.sum_le_sum fun X hX => h X (hS.mem_toFinset.1 hX)

/-- **Lemma 2.3 (b)**: `∑_{1 ≤ i ≤ j ≤ k} β_{i-1}^{-1} ∑_{X ∋ x, x'} |R^{ij}(x, x'; X; ψ_j, h_j)|
≤ C β^{-3/2+ρ₁} (1 + |x - x'|)^{-(d-2+ρ₀)} e^{-(δ₀/2) √ν |x - x'|/L²}`, when `L^k √ν ≤ L²`
(i.e. `k ≤ J`), with `|x - x'|` the sup-norm distance and `C` depending only on `d, L, ρ₀, δ₀` and
the polymer-sum constant `K₀` (P5 (1.35): `∑_{X ∋ x, x'} e^{-κ d_j(X)} ≤ K₀`, the hypothesis
`hK`).  **The mass factor carries `δ₀/2`, not `δ₀`**: with the full `δ₀` the statement is false
for `R^{kk}` saturating its bound (the algebraic prefactor `(1+|z|)^{-σ}` would have to come from
no part of the exponent); the proof splits the exponent into two halves, as the document says. -/
theorem sum_R_le (hd : 3 ≤ d) (hL : 2 ≤ L) {Q : ObsConsts} (hQ : Q.Admissible d) {K0 : ℝ}
    (hK0 : 0 ≤ K0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {N₁ m₁ k N : ℕ} [NeZero N₁] {ϱ : ℝ} {P : Consts}
      (_hP : P.Admissible d L) {β ν a : ℕ → ℝ} {Tm : Terms d L N₁ m₁ k N ϱ}
      {Ot : ObsTerms d L N₁ m₁ k N}
      {Gker : ℕ → CTorus d L N₁ m₁ k → CTorus d L N₁ m₁ k → Fld d L N₁ m₁ k N →
        Fld d L N₁ m₁ k N → Matrix (Fin N) (Fin N) ℂ},
      CoeffBounds d L k P β ν a → IsObs P Q β ν a Tm Ot Gker → 0 < β 0 →
      (∀ j, 1 ≤ j → j ≤ k → ∀ x x' : CTorus d L N₁ m₁ k,
        ∑ᶠ X ∈ polysAt2 P.m₀ j x x', Real.exp (-P.κ * sizeJ P.m₀ j X) ≤ K0) →
      (L : ℝ) ^ k * Real.sqrt (ν 0) ≤ (L : ℝ) ^ 2 →
      ∀ (Ψ Φ : ℕ → Fld d L N₁ m₁ k N),
      (∀ j, 1 ≤ j → j ≤ k → ∀ X, IsPolyDom P.m₀ j X →
        XiDom (Tm.gs j X) (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) j (P.eps d L j)
          (Ψ j) (Φ j)) →
      ∀ x x' : CTorus d L N₁ m₁ k,
      ∑ i ∈ Icc 1 k, ∑ j ∈ Icc i k, (β (i - 1))⁻¹ *
          ∑ᶠ X ∈ polysAt2 P.m₀ j x x', matNorm (Ot.R i j x x' X (Ψ j) (Φ j)) ≤
        C * (β 0) ^ (-(3 / 2 : ℝ) + Q.ρ₁) *
          (1 + torusDist x x') ^ (-(((d : ℝ) - 2) + Q.ρ₀)) *
          Real.exp (-(Q.δ₀ / 2 * Real.sqrt (ν 0) * torusDist x x' / (L : ℝ) ^ 2)) := by
  have hLr : (1 : ℝ) < L := by
    have : (2 : ℝ) ≤ L := by exact_mod_cast hL
    linarith
  obtain ⟨Cc, hCc, hcore⟩ := core_series (d := d) (L := L) (by omega) hL hQ.ρ₀_pos hQ.δ₀_pos
  refine ⟨Real.exp 1 * K0 * Cc, by positivity, ?_⟩
  intro N₁ m₁ k N _ ϱ P hP β ν a Tm Ot Gker hc hO hβ0 hK hk Ψ Φ hdom x x'
  set z1 := torusL1 x x' with hz1
  set zd := torusDist x x' with hzd
  have hz1nn : 0 ≤ z1 := torusL1_nonneg x x'
  have hzdnn : 0 ≤ zd := torusDist_nonneg x x'
  have hzle : zd ≤ z1 := torusDist_le_torusL1 x x'
  set s := Real.sqrt (ν 0) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hterm : ∀ i ∈ Icc 1 k, ∀ j ∈ Icc i k, (β (i - 1))⁻¹ *
      ∑ᶠ X ∈ polysAt2 P.m₀ j x x', matNorm (Ot.R i j x x' X (Ψ j) (Φ j)) ≤
      (Real.exp 1 * K0 * (β 0) ^ (-(3 / 2 : ℝ) + Q.ρ₁)) *
        (((L : ℝ) ^ ((i - 1) * (d - 2)))⁻¹ * (L : ℝ) ^ (-((j : ℝ) * Q.ρ₀)) *
          Real.exp (-(Q.δ₀ * ((L : ℝ) ^ i)⁻¹ * z1))) := by
    intro i hi j hj
    have hi1 : 1 ≤ i := (Finset.mem_Icc.1 hi).1
    have hij : i ≤ j := (Finset.mem_Icc.1 hj).1
    have hjk : j ≤ k := (Finset.mem_Icc.1 hj).2
    have hj1 : 1 ≤ j := hi1.trans hij
    -- the bound on the sum over polymers
    set RB : ℝ := (β 0) ^ (-(1 / 2 : ℝ) + Q.ρ₁) * (L : ℝ) ^ (-((j : ℝ) * Q.ρ₀)) *
      Real.exp (-(Q.δ₀ * ((L : ℝ) ^ i)⁻¹ * z1)) with hRB
    have hRB0 : 0 ≤ RB := by
      rw [hRB]
      have : 0 ≤ (β 0) ^ (-(1 / 2 : ℝ) + Q.ρ₁) := Real.rpow_nonneg hβ0.le _
      have : 0 ≤ (L : ℝ) ^ (-((j : ℝ) * Q.ρ₀)) := Real.rpow_nonneg (by linarith) _
      positivity
    have hX : ∑ᶠ X ∈ polysAt2 P.m₀ j x x', matNorm (Ot.R i j x x' X (Ψ j) (Φ j)) ≤ RB * K0 := by
      refine (finsum_mem_le_mul (c := RB)
        (g := fun X => Real.exp (-P.κ * sizeJ P.m₀ j X)) ?_).trans
        (mul_le_mul_of_nonneg_left (hK j hj1 hjk x x') hRB0)
      intro X hXmem
      obtain ⟨hXp, hxX, hx'X⟩ := hXmem
      have := hO.boundR i j hi1 hij hjk x x' X hXp hxX hx'X (Ψ j) (Φ j) (hdom j hj1 hjk X hXp)
      rw [hRB]
      calc matNorm (Ot.R i j x x' X (Ψ j) (Φ j)) ≤ _ := this
        _ = _ := by ring
    -- the bound on the coupling
    obtain ⟨hpos, hlow⟩ := beta_pos_lower hL hP hc hβ0 (n := i - 1) (by omega)
    have hLp : 0 < (L : ℝ) ^ ((i - 1) * (d - 2)) := by positivity
    have hβinv : (β (i - 1))⁻¹ ≤ Real.exp 1 / β 0 * ((L : ℝ) ^ ((i - 1) * (d - 2)))⁻¹ := by
      calc (β (i - 1))⁻¹ ≤ (β 0 * (L : ℝ) ^ ((i - 1) * (d - 2)) / Real.exp 1)⁻¹ :=
            inv_anti₀ (by positivity) hlow
        _ = _ := by field_simp
    have hsum0 : 0 ≤ ∑ᶠ X ∈ polysAt2 P.m₀ j x x', matNorm (Ot.R i j x x' X (Ψ j) (Φ j)) := by
      rw [finsum_mem_eq_finite_toFinset_sum _ (Set.toFinite _)]
      exact Finset.sum_nonneg fun X _ => norm_nonneg _
    have hpow : (β 0) ^ (-(3 / 2 : ℝ) + Q.ρ₁) = (β 0)⁻¹ * (β 0) ^ (-(1 / 2 : ℝ) + Q.ρ₁) := by
      rw [← Real.rpow_neg_one, ← Real.rpow_add hβ0]; congr 1; ring
    calc (β (i - 1))⁻¹ * ∑ᶠ X ∈ polysAt2 P.m₀ j x x', matNorm (Ot.R i j x x' X (Ψ j) (Φ j))
        ≤ (Real.exp 1 / β 0 * ((L : ℝ) ^ ((i - 1) * (d - 2)))⁻¹) * (RB * K0) :=
          mul_le_mul hβinv hX hsum0 (by positivity)
      _ = _ := by
          rw [hRB, hpow]
          field_simp
  have hcore' := hcore k z1 s hz1nn hs0 hk
  calc _ ≤ ∑ i ∈ Icc 1 k, ∑ j ∈ Icc i k, (Real.exp 1 * K0 * (β 0) ^ (-(3 / 2 : ℝ) + Q.ρ₁)) *
          (((L : ℝ) ^ ((i - 1) * (d - 2)))⁻¹ * (L : ℝ) ^ (-((j : ℝ) * Q.ρ₀)) *
            Real.exp (-(Q.δ₀ * ((L : ℝ) ^ i)⁻¹ * z1))) :=
        Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => hterm i hi j hj
    _ = (Real.exp 1 * K0 * (β 0) ^ (-(3 / 2 : ℝ) + Q.ρ₁)) *
          ∑ i ∈ Icc 1 k, ∑ j ∈ Icc i k, ((L : ℝ) ^ ((i - 1) * (d - 2)))⁻¹ *
            (L : ℝ) ^ (-((j : ℝ) * Q.ρ₀)) * Real.exp (-(Q.δ₀ * ((L : ℝ) ^ i)⁻¹ * z1)) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [Finset.mul_sum]
    _ ≤ (Real.exp 1 * K0 * (β 0) ^ (-(3 / 2 : ℝ) + Q.ρ₁)) *
          (Cc * (1 + z1) ^ (-(((d : ℝ) - 2) + Q.ρ₀)) *
            Real.exp (-(Q.δ₀ / 2 * s * z1 / (L : ℝ) ^ 2))) := by
        gcongr
    _ ≤ (Real.exp 1 * K0 * (β 0) ^ (-(3 / 2 : ℝ) + Q.ρ₁)) *
          (Cc * (1 + zd) ^ (-(((d : ℝ) - 2) + Q.ρ₀)) *
            Real.exp (-(Q.δ₀ / 2 * s * zd / (L : ℝ) ^ 2))) := by
        have hσ : 0 ≤ ((d : ℝ) - 2) + Q.ρ₀ := by
          have : (3 : ℝ) ≤ d := by exact_mod_cast hd
          linarith [hQ.ρ₀_pos]
        have h1 : (1 + z1) ^ (-(((d : ℝ) - 2) + Q.ρ₀)) ≤ (1 + zd) ^ (-(((d : ℝ) - 2) + Q.ρ₀)) :=
          Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by linarith)
        have h2 : Real.exp (-(Q.δ₀ / 2 * s * z1 / (L : ℝ) ^ 2)) ≤
            Real.exp (-(Q.δ₀ / 2 * s * zd / (L : ℝ) ^ 2)) := by
          rw [Real.exp_le_exp, neg_le_neg_iff]
          have : 0 ≤ Q.δ₀ / 2 * s / (L : ℝ) ^ 2 := by have := hQ.δ₀_pos; positivity
          have h3 := mul_le_mul_of_nonneg_left hzle this
          calc Q.δ₀ / 2 * s * zd / (L : ℝ) ^ 2 = Q.δ₀ / 2 * s / (L : ℝ) ^ 2 * zd := by ring
            _ ≤ Q.δ₀ / 2 * s / (L : ℝ) ^ 2 * z1 := h3
            _ = _ := by ring
        have hb : 0 ≤ Real.exp 1 * K0 * (β 0) ^ (-(3 / 2 : ℝ) + Q.ρ₁) := by
          have := Real.rpow_nonneg hβ0.le (-(3 / 2 : ℝ) + Q.ρ₁); positivity
        gcongr
    _ = _ := by ring

end Lemma23

end Balaban.Observables
