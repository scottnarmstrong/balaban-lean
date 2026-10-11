/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Correlations.LemmaThree

/-!
# Step C: the limits `ν ↓ 0` (CORRELATIONS.md §3.3)

Tannery's theorem (`tendsto_tsum_of_dominated_convergence`) applied to the magnetization series
`m_{J(ν)}(ν; 0) = 1 - ∑_j 1_{j < J(ν)} β_j(ν)^{-1/2} μ_{j+1}(ν; 0)` and to the Gaussian main sum
`∑_{j<J(ν)} (β γ_j(ν))⁻¹ t_j^{ν δ_j(ν)}(z, y)`.
-/

@[expose] public section

open Filter Topology Finset

namespace Balaban.Correlations

open Balaban Balaban.Flow

variable {d L : ℕ}

theorem tendsto_inv_pow_J (hd : 3 ≤ d) (hL : 2 ≤ L) {J : ℝ → ℕ} (hJ : Tendsto J (𝓝[>] 0) atTop)
    (C : ℝ) :
    Tendsto (fun ν => C * ((L : ℝ) ^ (2 * J ν * (d - 2)))⁻¹) (𝓝[>] 0) (𝓝 0) := by
  have hL1 : (1 : ℝ) < L := by exact_mod_cast hL
  have he : Tendsto (fun n : ℕ => 2 * n * (d - 2)) atTop atTop :=
    tendsto_atTop_mono (fun n => by
      have : 1 ≤ d - 2 := by omega
      show n ≤ 2 * n * (d - 2)
      nlinarith) tendsto_id
  have h1 : Tendsto (fun n : ℕ => (L : ℝ) ^ (2 * n * (d - 2))) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt hL1).comp he
  have h2 := (h1.inv_tendsto_atTop).comp hJ
  simpa using h2.const_mul C

theorem tendsto_mag {γ₀ c₈ ρ₀ ρ₁ cS β : ℝ} {ξ : ℝ → ℕ → Fin 3 → ℝ}
    {μ : ℕ → ℝ → (Fin d → ℤ) → ℝ} {J : ℝ → ℕ} (hd : 3 ≤ d) (hL : 2 ≤ L)
    (HS : ∀ ν ∈ Set.Icc (0 : ℝ) 1, SeqHyp L γ₀ c₈ (ξ ν))
    (hc : ∀ k, Tendsto (fun ν => ξ ν k) (𝓝[>] 0) (𝓝 (ξ 0 k))) (hρ₀ : 0 < ρ₀) (hcS : 0 ≤ cS)
    (hβ : 0 < β)
    (hμb : ∀ j, 1 ≤ j → ∀ ν ∈ Set.Icc (0 : ℝ) 1, ∀ x,
      |μ j ν x| ≤ cS * β ^ (-(1 / 2 : ℝ) + ρ₁) * (L : ℝ) ^ (-((j : ℝ) * ρ₀)))
    (hμc : ∀ j x, Tendsto (fun ν => μ j ν x) (𝓝[>] 0) (𝓝 (μ j 0 x)))
    (hJ : Tendsto J (𝓝[>] 0) atTop) {m : ℝ → ℝ}
    (hm : ∀ ν ∈ Set.Ioc (0 : ℝ) 1, ∀ x,
      |m ν - magJ L d (ξ ν) (fun j => μ j ν) β (J ν) x| ≤
        cS * (β ^ 2)⁻¹ * ((L : ℝ) ^ (2 * J ν * (d - 2)))⁻¹) :
    ∃ m₀ : ℝ, Tendsto m (𝓝[>] 0) (𝓝 m₀) ∧
      (∀ x, Tendsto (fun ν => magJ L d (ξ ν) (fun j => μ j ν) β (J ν) x) (𝓝[>] 0) (𝓝 m₀)) ∧
      |m₀ - 1| ≤ Real.sqrt 2 * cS * ((L : ℝ) ^ (-ρ₀) / (1 - (L : ℝ) ^ (-ρ₀))) *
        β ^ (-1 + ρ₁) := by
  have hL1 : (1 : ℝ) < L := by exact_mod_cast hL
  have hL0 : (0 : ℝ) < L := by linarith
  set r : ℝ := (L : ℝ) ^ (-ρ₀) with hr
  have hr0 : 0 ≤ r := (Real.rpow_pos_of_pos hL0 _).le
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg hL1 (by linarith)
  have hIcc : ∀ ν ∈ Set.Ioc (0 : ℝ) 1, ν ∈ Set.Icc (0 : ℝ) 1 := fun ν hν => ⟨hν.1.le, hν.2⟩
  have hI : ∀ᶠ ν in 𝓝[>] (0 : ℝ), ν ∈ Set.Ioc (0 : ℝ) 1 := Ioc_mem_nhdsGT one_pos
  set f : ℝ → ℕ → ℝ := fun ν j => if j < J ν then
    (Real.sqrt (betaR L d (ξ ν) β j))⁻¹ * μ (j + 1) ν 0 else 0 with hf
  set g : ℕ → ℝ := fun j => (Real.sqrt (betaR L d (ξ 0) β j))⁻¹ * μ (j + 1) 0 0 with hg
  set bd : ℕ → ℝ := fun j => Real.sqrt 2 * cS * β ^ (-1 + ρ₁) * r ^ (j + 1) with hbd
  have hbdS : Summable bd := by
    refine ((summable_geometric_of_lt_one hr0 hr1).mul_left
      (Real.sqrt 2 * cS * β ^ (-1 + ρ₁) * r)).congr fun j => ?_
    simp only [hbd]; ring
  have hab : ∀ j, Tendsto (fun ν => f ν j) (𝓝[>] 0) (𝓝 (g j)) := by
    intro j
    have h0 : Tendsto (fun ν => (Real.sqrt (betaR L d (ξ ν) β j))⁻¹ * μ (j + 1) ν 0)
        (𝓝[>] 0) (𝓝 (g j)) := by
      have hb := tendsto_betaR (d := d) hc (HS 0 ⟨le_rfl, zero_le_one⟩) β j
      have hs := (Real.continuous_sqrt.tendsto _).comp hb
      have hpos : Real.sqrt (betaR L d (ξ 0) β j) ≠ 0 :=
        (Real.sqrt_pos.2 ((HS 0 ⟨le_rfl, zero_le_one⟩).betaR_pos hβ j)).ne'
      exact (hs.inv₀ hpos).mul (hμc (j + 1) 0)
    refine h0.congr' ?_
    filter_upwards [hJ.eventually_gt_atTop j] with ν hν
    simp [hf, hν]
  have hbound : ∀ᶠ ν in 𝓝[>] (0 : ℝ), ∀ j, ‖f ν j‖ ≤ bd j := by
    filter_upwards [hI] with ν hν j
    by_cases hj : j < J ν
    · simp only [hf, hj, ↓reduceIte, Real.norm_eq_abs]
      exact abs_term_le (HS ν (hIcc ν hν)) hβ (fun j hj1 => hμb j hj1 ν (hIcc ν hν) 0) j
    · simp only [hf, hj, ↓reduceIte, norm_zero]
      exact mul_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hcS)
        (Real.rpow_nonneg hβ.le _)) (pow_nonneg hr0 _)
  have htsum := tendsto_tsum_of_dominated_convergence hbdS hab hbound
  have hsum_eq : ∀ ν, ∑' j, f ν j = ∑ j ∈ range (J ν),
      (Real.sqrt (betaR L d (ξ ν) β j))⁻¹ * μ (j + 1) ν 0 := by
    intro ν
    rw [tsum_eq_sum (s := range (J ν)) (fun j hj => by
      have : ¬ j < J ν := by simpa using hj
      simp [hf, this])]
    exact Finset.sum_congr rfl fun j hj => by simp [hf, mem_range.1 hj]
  have hmag0 : Tendsto (fun ν => magJ L d (ξ ν) (fun j => μ j ν) β (J ν) 0) (𝓝[>] 0)
      (𝓝 (1 - ∑' j, g j)) := by
    have := (tendsto_const_nhds (x := (1 : ℝ))).sub htsum
    refine this.congr fun ν => ?_
    rw [hsum_eq]; rfl
  have hE := tendsto_inv_pow_J hd hL hJ (cS * (β ^ 2)⁻¹)
  have hdiff : ∀ x, Tendsto (fun ν => m ν - magJ L d (ξ ν) (fun j => μ j ν) β (J ν) x)
      (𝓝[>] 0) (𝓝 0) := fun x => by
    refine squeeze_zero_norm' ?_ hE
    filter_upwards [hI] with ν hν
    rw [Real.norm_eq_abs]; exact hm ν hν x
  have hm0 : Tendsto m (𝓝[>] 0) (𝓝 (1 - ∑' j, g j)) := by
    have := (hdiff 0).add hmag0
    simp only [zero_add] at this
    exact this.congr fun ν => by ring
  refine ⟨1 - ∑' j, g j, hm0, fun x => ?_, ?_⟩
  · have := hm0.sub (hdiff x)
    simp only [sub_zero] at this
    exact this.congr fun ν => by ring
  · have h1 := (hmag0.sub_const 1).abs
    refine le_of_tendsto h1 ?_
    filter_upwards [hI] with ν hν
    exact abs_magJ_sub_one_le (HS ν (hIcc ν hν)) hρ₀ hcS hβ (J ν)
      (fun j hj1 => hμb j hj1 ν (hIcc ν hν) 0)

theorem mass_mem {γ₀ c₈ : ℝ} {ξ : ℕ → Fin 3 → ℝ} (HS : SeqHyp L γ₀ c₈ ξ) {ν : ℝ}
    (hν : ν ∈ Set.Ioc (0 : ℝ) 1) (j : ℕ) : 0 < ν * deltaR ξ j ∧ ν * deltaR ξ j ≤ 2 := by
  have h1 := HS.deltaR_pos j
  have h2 := (HS.deltaR_bounds j).2
  exact ⟨mul_pos hν.1 h1, by nlinarith [hν.1, hν.2]⟩

theorem mass_mem' {γ₀ c₈ : ℝ} {ξ : ℕ → Fin 3 → ℝ} (HS : SeqHyp L γ₀ c₈ ξ) {ν : ℝ}
    (hν : ν ∈ Set.Ioc (0 : ℝ) 1) {j J : ℕ} (hj : j < J)
    (hJ : (L : ℝ) ^ J * Real.sqrt ν ≤ (L : ℝ) ^ 2) :
    0 < ν * deltaR ξ j ∧ ν * deltaR ξ j * (L : ℝ) ^ (2 * (j + 1)) ≤ 2 * (L : ℝ) ^ 4 := by
  refine ⟨(mass_mem HS hν j).1, ?_⟩
  have hL1 : (1 : ℝ) < L := by exact_mod_cast HS.hL
  have hδ := (HS.deltaR_bounds j).2
  have hP : 0 ≤ (L : ℝ) ^ (2 * (j + 1)) := by positivity
  have e1 : (L : ℝ) ^ (2 * (j + 1)) ≤ ((L : ℝ) ^ J) ^ 2 := by
    rw [← pow_mul']
    exact pow_le_pow_right₀ hL1.le (by omega)
  have hsq : ν = Real.sqrt ν ^ 2 := (Real.sq_sqrt hν.1.le).symm
  have h0 : 0 ≤ (L : ℝ) ^ J * Real.sqrt ν := by positivity
  calc ν * deltaR ξ j * (L : ℝ) ^ (2 * (j + 1))
      ≤ ν * 2 * (L : ℝ) ^ (2 * (j + 1)) :=
        mul_le_mul_of_nonneg_right (by nlinarith [hν.1]) hP
    _ ≤ ν * 2 * ((L : ℝ) ^ J) ^ 2 :=
        mul_le_mul_of_nonneg_left e1 (by nlinarith [hν.1])
    _ = 2 * ((L : ℝ) ^ J * Real.sqrt ν) ^ 2 := by
        conv_lhs => rw [hsq]
        ring
    _ ≤ 2 * ((L : ℝ) ^ 2) ^ 2 := by gcongr
    _ = 2 * (L : ℝ) ^ 4 := by ring

theorem tendsto_mainSum [NeZero L] {γ₀ c₈ β a C_G δ_G C_P : ℝ} {ξ : ℝ → ℕ → Fin 3 → ℝ}
    {J : ℝ → ℕ} (hL : 2 ≤ L) (hd : 3 ≤ d)
    (HS : ∀ ν ∈ Set.Icc (0 : ℝ) 1, SeqHyp L γ₀ c₈ (ξ ν))
    (hc : ∀ k, Tendsto (fun ν => ξ ν k) (𝓝[>] 0) (𝓝 (ξ 0 k))) (hβ : 0 < β)
    (hJ : Tendsto J (𝓝[>] 0) atTop)
    (hJb : ∀ ν ∈ Set.Ioc (0 : ℝ) 1, (L : ℝ) ^ J ν * Real.sqrt ν ≤ (L : ℝ) ^ 2)
    {t : ℕ → ℝ → (Fin d → ℤ) → (Fin d → ℤ) → ℝ}
    {t0 : ℕ → (Fin d → ℤ) → (Fin d → ℤ) → ℝ}
    (H : KernelHyp d L a t t0 C_G δ_G C_P) (HL : KernelHypLarge d L a t C_G δ_G)
    (z y : Fin d → ℤ) :
    Tendsto (fun ν => ∑ j ∈ range (J ν), (β * gammaR (ξ ν) j)⁻¹ * t j (ν * deltaR (ξ ν) j) z y)
      (𝓝[>] 0) (𝓝 (∑' j, (β * gammaR (ξ 0) j)⁻¹ * t0 j z y)) := by
  have hL1 : (1 : ℝ) < L := by exact_mod_cast hL
  have hL0 : (0 : ℝ) < L := by linarith
  have hIcc : ∀ ν ∈ Set.Ioc (0 : ℝ) 1, ν ∈ Set.Icc (0 : ℝ) 1 := fun ν hν => ⟨hν.1.le, hν.2⟩
  have hI : ∀ᶠ ν in 𝓝[>] (0 : ℝ), ν ∈ Set.Ioc (0 : ℝ) 1 := Ioc_mem_nhdsGT one_pos
  have H0 := HS 0 ⟨le_rfl, zero_le_one⟩
  set ρ : ℝ := ((L : ℝ) ^ (d - 2))⁻¹ with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  have hρ1 : ρ < 1 := inv_lt_one_of_one_lt₀ (one_lt_pow₀ hL1 (by omega))
  set f : ℝ → ℕ → ℝ := fun ν j => if j < J ν then
    (β * gammaR (ξ ν) j)⁻¹ * t j (ν * deltaR (ξ ν) j) z y else 0 with hf
  set g : ℕ → ℝ := fun j => (β * gammaR (ξ 0) j)⁻¹ * t0 j z y with hg
  set bd : ℕ → ℝ := fun j => 2 / β * C_G * ρ ^ j with hbd
  have hbdS : Summable bd := (summable_geometric_of_lt_one hρ0 hρ1).mul_left _
  have hab : ∀ j, Tendsto (fun ν => f ν j) (𝓝[>] 0) (𝓝 (g j)) := by
    intro j
    have hγ := tendsto_gammaR hc H0 j
    have hγne : β * gammaR (ξ 0) j ≠ 0 := (mul_pos hβ (H0.gammaR_pos j)).ne'
    have hφ : Tendsto (fun ν => ν * deltaR (ξ ν) j) (𝓝[>] 0) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have := ((tendsto_id (α := ℝ)).mono_left nhdsWithin_le_nhds).mul
          (tendsto_deltaR hc H0 j)
        simpa using this
      · filter_upwards [hI] with ν hν
        exact (mass_mem (HS ν (hIcc ν hν)) hν j).1
    have h0 : Tendsto (fun ν => (β * gammaR (ξ ν) j)⁻¹ * t j (ν * deltaR (ξ ν) j) z y)
        (𝓝[>] 0) (𝓝 (g j)) :=
      ((tendsto_const_nhds.mul hγ).inv₀ hγne).mul ((H.g3 j z y).comp hφ)
    refine h0.congr' ?_
    filter_upwards [hJ.eventually_gt_atTop j] with ν hν
    simp [hf, hν]
  have hbound : ∀ᶠ ν in 𝓝[>] (0 : ℝ), ∀ j, ‖f ν j‖ ≤ bd j := by
    filter_upwards [hI] with ν hν j
    by_cases hj : j < J ν
    · simp only [hf, hj, ↓reduceIte, Real.norm_eq_abs]
      have HSν := HS ν (hIcc ν hν)
      obtain ⟨hm1, hm2⟩ := mass_mem' HSν hν hj (hJb ν hν)
      have h2 := HL.g2 j _ hm1 hm2 z y
      have hgp := HSν.gammaR_pos j
      have hgb := (HSν.gammaR_bounds j).1
      have h1 : |(β * gammaR (ξ ν) j)⁻¹| ≤ 2 / β := by
        rw [abs_of_pos (inv_pos.2 (by positivity))]
        calc (β * gammaR (ξ ν) j)⁻¹ ≤ (β / 2)⁻¹ :=
              inv_anti₀ (by positivity) (by nlinarith)
          _ = 2 / β := by field_simp
      have hx : ((L : ℝ) ^ (j * (d - 2)))⁻¹ = ρ ^ j := by
        rw [hρ, inv_pow, ← pow_mul, mul_comm]
      have hex : Real.exp (-(δ_G * ‖z - y‖ / (L : ℝ) ^ j)) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        have := H.pos_δ
        have : 0 ≤ δ_G * ‖z - y‖ / (L : ℝ) ^ j := by positivity
        linarith
      have hC := H.nonneg_G
      rw [abs_mul]
      calc |(β * gammaR (ξ ν) j)⁻¹| * |t j (ν * deltaR (ξ ν) j) z y|
          ≤ (2 / β) * (C_G * ((L : ℝ) ^ (j * (d - 2)))⁻¹ *
            Real.exp (-(δ_G * ‖z - y‖ / (L : ℝ) ^ j))) :=
            mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
        _ ≤ (2 / β) * (C_G * ρ ^ j * 1) := by
            rw [hx]; gcongr
        _ = bd j := by simp only [hbd]; ring
    · simp only [hf, hj, ↓reduceIte, norm_zero]
      have := H.nonneg_G
      positivity
  have htsum := tendsto_tsum_of_dominated_convergence hbdS hab hbound
  refine htsum.congr fun ν => ?_
  rw [tsum_eq_sum (s := range (J ν)) (fun j hj => by
    have : ¬ j < J ν := by simpa using hj
    simp [hf, this])]
  exact Finset.sum_congr rfl fun j hj => by simp [hf, mem_range.1 hj]

end Balaban.Correlations
