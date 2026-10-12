/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Observables.FirstOrderScale
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The first-order terms of the step (OBSERVABLES.md §3.5): exponent bookkeeping

`T1_bound`: the term `m_k⟨δφ_k⟩`.  The Cauchy estimate (3.5) gives
`|Φ_k| ≤ (4/r₁)(1/r₀) C` with the radii of the background case; with (B1), (B3) and the exponent
constraints (E1), (E2) this is `≤ ½ β^{-1/2+ρ₁} ξ_{k+1}^{ρ₀}` for `β ≥ β₀`, the threshold being the
explicit inequality `hβ0`.
-/

@[expose] public section

namespace Balaban.Observables

open Real

namespace StepScale

variable {D ρ₂ : ℝ} (S : StepScale D ρ₂)

theorem η_rpow_eq {e : ℝ} : S.η ^ e = S.L ^ e * S.ξ ^ e := by
  have : S.η = S.L * S.ξ := by
    unfold ξ; field_simp [S.L_pos.ne']
  conv_lhs => rw [this]
  exact Real.mul_rpow S.L_pos.le S.ξ_pos.le

end StepScale

/-- **T1** (P9 (3.16)-(3.17); OBSERVABLES (3.5)).  `x` is the size of one `(x, Y)` term of
`m_k ⟨δφ_k⟩` divided by `e^{-2κ d_{k+1}(Y)}`; it satisfies the Cauchy estimate `(4/r₁)(1/r₀) C_m`
with the radii of the case `RadiusCase.background`.  Under (E1), (E2) and `β ≥ β₀` (the inequality
`hβ0`), `x ≤ ½ β^{-1/2+ρ₁} ξ_{k+1}^{ρ₀}`. -/
theorem T1_bound {d : ℕ} {γ α₁ ρ₀ ρ₁ ρ₂ : ℝ} (hE : ExponentConstraints d γ α₁ ρ₀ ρ₁ ρ₂)
    (S : StepScale ((d : ℝ) - 2) ρ₂) {c c₁ α εo εn Cm x : ℝ} (hc : 0 < c) (hc₁ : 0 < c₁)
    (hCm : 0 ≤ Cm)
    (hx : x ≤ 4 / couplingRadius c c₁ S.βk S.p1 *
      (1 / fieldRadius c c₁ α εo εn S.p1 RadiusCase.background) * Cm)
    (hβ0 : 2 * √2 * (4 * Cm / (c * c₁) ^ 2) * (2 * S.Cp) ^ 2 * S.L ^ ρ₀ ≤ S.β ^ (2 * ρ₂)) :
    x ≤ 1 / 2 * S.β ^ (-(1 / 2 : ℝ) + ρ₁) * S.ξ ^ ρ₀ := by
  have hD : (1 : ℝ) ≤ (d : ℝ) - 2 := S.hD
  have hβp := S.β_pos
  have hβk := S.βk_pos
  have hp1 : 0 < S.p1 := by linarith [S.hp1]
  have hρ2 := hE.ρ₂_pos
  have hρ2' : ρ₂ ≤ 1 := by
    have := hE.E1; have := hE.ρ₁_lt_one; linarith
  -- step 1: the radii
  have hsq : 0 < √S.βk := Real.sqrt_pos.2 hβk
  have h1 : 4 / couplingRadius c c₁ S.βk S.p1 *
      (1 / fieldRadius c c₁ α εo εn S.p1 RadiusCase.background) * Cm =
      (4 * Cm / (c * c₁) ^ 2) * S.p1 ^ 2 * S.βk ^ (-(1 / 2 : ℝ)) := by
    unfold couplingRadius fieldRadius
    rw [Real.rpow_neg hβk.le, ← Real.sqrt_eq_rpow]
    field_simp
  have hK : 0 ≤ 4 * Cm / (c * c₁) ^ 2 := by positivity
  -- step 2: (B3) with s = 2 and (B1)
  have hp2 : S.p1 ^ 2 ≤ (2 * S.Cp) ^ 2 * S.β ^ (2 * ρ₂) * S.η ^ (-(2 * ((d - 2 : ℝ) * ρ₂))) := by
    have := S.p1_pow_le hρ2.le hρ2' (s := 2) (by norm_num)
    simpa [Real.rpow_two, Real.rpow_natCast] using this
  have hb1 := S.betak_inv_sqrt_le
  -- step 3: assemble
  set K := 4 * Cm / (c * c₁) ^ 2 with hKdef
  have hη0 := S.hη0
  have hηe : S.η ^ (-(2 * ((d - 2 : ℝ) * ρ₂))) * S.η ^ ((d - 2 : ℝ) / 2) ≤ S.η ^ ρ₀ := by
    rw [← Real.rpow_add hη0]
    refine Real.rpow_le_rpow_of_exponent_ge hη0 S.hη1 ?_
    have := hE.E2
    nlinarith [hE.ρ₂_pos, hD]
  have hmain : x ≤ K * ((2 * S.Cp) ^ 2 * S.β ^ (2 * ρ₂) * S.η ^ (-(2 * ((d - 2 : ℝ) * ρ₂)))) *
      (√2 * S.β ^ (-(1 / 2 : ℝ)) * S.η ^ ((d - 2 : ℝ) / 2)) := by
    rw [h1] at hx
    refine hx.trans ?_
    have := mul_le_mul (mul_le_mul_of_nonneg_left hp2 hK) hb1
      (Real.rpow_nonneg hβk.le _) (by positivity)
    exact this
  have hβe : S.β ^ (2 * ρ₂) * S.β ^ (-(1 / 2 : ℝ)) ≤
      S.β ^ (-(2 * ρ₂)) * S.β ^ (-(1 / 2 : ℝ) + ρ₁) := by
    rw [← Real.rpow_add hβp, ← Real.rpow_add hβp]
    refine Real.rpow_le_rpow_of_exponent_le S.hβ ?_
    have := hE.E1; linarith
  have hβ0' : 0 ≤ S.β ^ (-(2 * ρ₂)) := Real.rpow_nonneg hβp.le _
  have hη1 : 0 ≤ S.η ^ (-(2 * ((d - 2 : ℝ) * ρ₂))) := Real.rpow_nonneg hη0.le _
  have hη2 : 0 ≤ S.η ^ ((d - 2 : ℝ) / 2) := Real.rpow_nonneg hη0.le _
  have hCp2 : 0 ≤ (2 * S.Cp) ^ 2 := by positivity
  have hs2 : 0 ≤ √2 := Real.sqrt_nonneg 2
  have hLpos : 0 < S.L ^ ρ₀ := Real.rpow_pos_of_pos S.L_pos _
  have hξpos := S.ξ_pos
  calc x ≤ _ := hmain
    _ = K * (2 * S.Cp) ^ 2 * √2 * (S.β ^ (2 * ρ₂) * S.β ^ (-(1 / 2 : ℝ))) *
          (S.η ^ (-(2 * ((d - 2 : ℝ) * ρ₂))) * S.η ^ ((d - 2 : ℝ) / 2)) := by ring
    _ ≤ K * (2 * S.Cp) ^ 2 * √2 * (S.β ^ (-(2 * ρ₂)) * S.β ^ (-(1 / 2 : ℝ) + ρ₁)) *
          S.η ^ ρ₀ := by
        gcongr
    _ = K * (2 * S.Cp) ^ 2 * √2 * S.L ^ ρ₀ * S.β ^ (-(2 * ρ₂)) *
          (S.β ^ (-(1 / 2 : ℝ) + ρ₁) * S.ξ ^ ρ₀) := by
        rw [S.η_rpow_eq (e := ρ₀)]; ring
    _ ≤ 1 / 2 * (S.β ^ (-(1 / 2 : ℝ) + ρ₁) * S.ξ ^ ρ₀) := by
        have hprod : 0 ≤ S.β ^ (-(1 / 2 : ℝ) + ρ₁) * S.ξ ^ ρ₀ := by positivity
        have hneg : S.β ^ (2 * ρ₂) * S.β ^ (-(2 * ρ₂)) = 1 := by
          rw [← Real.rpow_add hβp]; simp
        have hle : K * (2 * S.Cp) ^ 2 * √2 * S.L ^ ρ₀ * S.β ^ (-(2 * ρ₂)) ≤ 1 / 2 := by
          have h2 := mul_le_mul_of_nonneg_right hβ0 hβ0'
          have : S.β ^ (2 * ρ₂) * S.β ^ (-(2 * ρ₂)) = 1 := hneg
          nlinarith [h2, this]
        exact mul_le_mul_of_nonneg_right hle hprod
    _ = _ := by ring

/-- **(3.23)** `ξ_j^{ρ₀+γ-1} η^{1-Dρ₂} ≤ ξ_j^{γ-Dρ₂} η^{ρ₀}` for `η ≤ ξ_j` and `ρ₀ + Dρ₂ ≤ 1`:
the irrelevant factor `η^{ρ₀}` is split off. -/
theorem xi_eta_split {ξj η D γ ρ₀ ρ₂ : ℝ} (hξj : 0 < ξj) (hη : 0 < η) (hηξ : η ≤ ξj)
    (hρ : ρ₀ + D * ρ₂ ≤ 1) :
    ξj ^ (ρ₀ + γ - 1) * η ^ (1 - D * ρ₂) ≤ ξj ^ (γ - D * ρ₂) * η ^ ρ₀ := by
  have e1 : η ^ (1 - D * ρ₂) = η ^ (1 - ρ₀ - D * ρ₂) * η ^ ρ₀ := by
    rw [← Real.rpow_add hη]; congr 1; ring
  have h2 : η ^ (1 - ρ₀ - D * ρ₂) ≤ ξj ^ (1 - ρ₀ - D * ρ₂) :=
    Real.rpow_le_rpow hη.le hηξ (by linarith)
  have e3 : ξj ^ (ρ₀ + γ - 1) * ξj ^ (1 - ρ₀ - D * ρ₂) = ξj ^ (γ - D * ρ₂) := by
    rw [← Real.rpow_add hξj]; congr 1; ring
  rw [e1, ← e3]
  have h4 : 0 ≤ η ^ ρ₀ := Real.rpow_nonneg hη.le _
  have h5 : 0 ≤ ξj ^ (ρ₀ + γ - 1) := Real.rpow_nonneg hξj.le _
  calc ξj ^ (ρ₀ + γ - 1) * (η ^ (1 - ρ₀ - D * ρ₂) * η ^ ρ₀)
      = ξj ^ (ρ₀ + γ - 1) * η ^ (1 - ρ₀ - D * ρ₂) * η ^ ρ₀ := by ring
    _ ≤ ξj ^ (ρ₀ + γ - 1) * ξj ^ (1 - ρ₀ - D * ρ₂) * η ^ ρ₀ := by gcongr

/-- The geometric sum `∑_{j=1}^k (L^{-j})^θ ≤ 1/(L^θ - 1)` for `L ≥ 2`, `θ > 0`. -/
theorem sum_xi_pow_le {L θ : ℝ} (hL : 2 ≤ L) (hθ : 0 < θ) (k : ℕ) :
    ∑ j ∈ Finset.Icc 1 k, (((L ^ j)⁻¹ : ℝ)) ^ θ ≤ 1 / (L ^ θ - 1) := by
  have hLp : 0 < L := by linarith
  have hLθ : 1 < L ^ θ := Real.one_lt_rpow (by linarith) hθ
  set q : ℝ := (L ^ θ)⁻¹ with hq
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := inv_lt_one_of_one_lt₀ hLθ
  have hterm : ∀ j : ℕ, (((L ^ j)⁻¹ : ℝ)) ^ θ = q ^ j := by
    intro j
    rw [Real.inv_rpow (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hLp.le,
      mul_comm, Real.rpow_mul hLp.le, Real.rpow_natCast, hq, inv_pow]
  simp_rw [hterm]
  have := geom_sum_Ico_le_of_lt_one hq0 hq1 (m := 1) (n := k + 1)
  rw [show Finset.Icc 1 k = Finset.Ico 1 (k + 1) from by ext; simp]
  refine this.trans (le_of_eq ?_)
  have hd : L ^ θ - 1 ≠ 0 := by linarith
  have hd' : L ^ θ ≠ 0 := by linarith
  rw [hq]; field_simp

/-- **T2, summed over the scales `j ≤ k`** (P9 (3.23)).  If every scale contributes
`x_j ≤ K β^{-1+ρ₁+ρ₂} ξ_j^{γ-Dρ₂} η^{ρ₀}` (`xi_eta_split` applied to `T2_bound_ge`), then, since
`γ - Dρ₂ > 0` by (E4), the sum is `≤ ½ β^{-1/2+ρ₁} ξ_{k+1}^{ρ₀}` for `β ≥ β₀` (`hβ0`). -/
theorem T2_total {d : ℕ} {γ α₁ ρ₀ ρ₁ ρ₂ : ℝ} (hE : ExponentConstraints d γ α₁ ρ₀ ρ₁ ρ₂)
    (S : StepScale ((d : ℝ) - 2) ρ₂) (k : ℕ) (xs : ℕ → ℝ) {Kc : ℝ} (hK : 0 ≤ Kc)
    (hj : ∀ j ∈ Finset.Icc 1 k, xs j ≤ Kc * S.β ^ (-1 + ρ₁ + ρ₂) *
      (((S.L ^ j)⁻¹ : ℝ)) ^ (γ - ((d : ℝ) - 2) * ρ₂) * S.η ^ ρ₀)
    (hβ0 : 2 * Kc * S.L ^ ρ₀ / (S.L ^ (γ - ((d : ℝ) - 2) * ρ₂) - 1) ≤ S.β ^ (1 / 2 - ρ₂)) :
    ∑ j ∈ Finset.Icc 1 k, xs j ≤ 1 / 2 * S.β ^ (-(1 / 2 : ℝ) + ρ₁) * S.ξ ^ ρ₀ := by
  have hD : (1 : ℝ) ≤ (d : ℝ) - 2 := S.hD
  have hβp := S.β_pos
  have hθ : 0 < γ - ((d : ℝ) - 2) * ρ₂ := by
    have := hE.E4; have := hE.ρ₂_pos; nlinarith
  have hLθ : 1 < S.L ^ (γ - ((d : ℝ) - 2) * ρ₂) := Real.one_lt_rpow (by linarith [S.hL]) hθ
  have hgeo := sum_xi_pow_le S.hL hθ k
  have hsum : ∑ j ∈ Finset.Icc 1 k, xs j ≤ Kc * S.β ^ (-1 + ρ₁ + ρ₂) * S.η ^ ρ₀ *
      (1 / (S.L ^ (γ - ((d : ℝ) - 2) * ρ₂) - 1)) := by
    calc ∑ j ∈ Finset.Icc 1 k, xs j
        ≤ ∑ j ∈ Finset.Icc 1 k, Kc * S.β ^ (-1 + ρ₁ + ρ₂) * S.η ^ ρ₀ *
            (((S.L ^ j)⁻¹ : ℝ)) ^ (γ - ((d : ℝ) - 2) * ρ₂) :=
          Finset.sum_le_sum (fun j hjm => (hj j hjm).trans (le_of_eq (by ring)))
      _ = Kc * S.β ^ (-1 + ρ₁ + ρ₂) * S.η ^ ρ₀ *
            ∑ j ∈ Finset.Icc 1 k, (((S.L ^ j)⁻¹ : ℝ)) ^ (γ - ((d : ℝ) - 2) * ρ₂) :=
          (Finset.mul_sum _ _ _).symm
      _ ≤ _ := by
          have h0 : 0 ≤ Kc * S.β ^ (-1 + ρ₁ + ρ₂) * S.η ^ ρ₀ :=
            mul_nonneg (mul_nonneg hK (Real.rpow_nonneg hβp.le _)) (Real.rpow_nonneg S.hη0.le _)
          exact mul_le_mul_of_nonneg_left hgeo h0
  refine hsum.trans ?_
  have hu : S.β ^ (-1 + ρ₁ + ρ₂) = S.β ^ (-(1 / 2 : ℝ) + ρ₁) * S.β ^ (-(1 / 2 : ℝ) + ρ₂) := by
    rw [← Real.rpow_add hβp]; congr 1; ring
  have hone : S.β ^ (1 / 2 - ρ₂) * S.β ^ (-(1 / 2 : ℝ) + ρ₂) = 1 := by
    rw [← Real.rpow_add hβp]; simp
  have hden : 0 < S.L ^ (γ - ((d : ℝ) - 2) * ρ₂) - 1 := by linarith
  have hb2 : 0 ≤ S.β ^ (-(1 / 2 : ℝ) + ρ₂) := Real.rpow_nonneg hβp.le _
  have hle : Kc * S.L ^ ρ₀ / (S.L ^ (γ - ((d : ℝ) - 2) * ρ₂) - 1) * S.β ^ (-(1 / 2 : ℝ) + ρ₂)
      ≤ 1 / 2 := by
    have h2 := mul_le_mul_of_nonneg_right hβ0 hb2
    rw [hone] at h2
    have : 2 * Kc * S.L ^ ρ₀ / (S.L ^ (γ - ((d : ℝ) - 2) * ρ₂) - 1) *
        S.β ^ (-(1 / 2 : ℝ) + ρ₂) = 2 * (Kc * S.L ^ ρ₀ /
        (S.L ^ (γ - ((d : ℝ) - 2) * ρ₂) - 1) * S.β ^ (-(1 / 2 : ℝ) + ρ₂)) := by ring
    linarith
  have hprod : 0 ≤ S.β ^ (-(1 / 2 : ℝ) + ρ₁) * S.ξ ^ ρ₀ := by
    have := S.ξ_pos; positivity
  calc Kc * S.β ^ (-1 + ρ₁ + ρ₂) * S.η ^ ρ₀ * (1 / (S.L ^ (γ - ((d : ℝ) - 2) * ρ₂) - 1))
      = (Kc * S.L ^ ρ₀ / (S.L ^ (γ - ((d : ℝ) - 2) * ρ₂) - 1) * S.β ^ (-(1 / 2 : ℝ) + ρ₂)) *
          (S.β ^ (-(1 / 2 : ℝ) + ρ₁) * S.ξ ^ ρ₀) := by
        rw [hu, S.η_rpow_eq (e := ρ₀)]; ring
    _ ≤ 1 / 2 * (S.β ^ (-(1 / 2 : ℝ) + ρ₁) * S.ξ ^ ρ₀) := mul_le_mul_of_nonneg_right hle hprod
    _ = _ := by ring

/-- **The scalar `μ_{k+1}` (OBSERVABLES §3.7).**  Each of the five contributions (T1, T2, the two
shifts, `M_ℛ`) is bounded as listed in §3.7; for `β ≥ β₀` (`hβ0`, with the entropy constant
`K_0^O`) their sum times `K_0^O` is `≤ ½ β^{-1/2+ρ₁} ξ_{k+1}^{ρ₀}`.  Uses (E1), (E2), (E4)-(E6). -/
theorem mu_bound {d : ℕ} {γ α₁ ρ₀ ρ₁ ρ₂ : ℝ} (hE : ExponentConstraints d γ α₁ ρ₀ ρ₁ ρ₂)
    (S : StepScale ((d : ℝ) - 2) ρ₂) {K0O C₁ C₂ C₃ C₄ C₅ t₁ t₂ t₃ t₄ t₅ : ℝ} (hK : 0 ≤ K0O)
    (ht₁ : t₁ ≤ C₁ * (S.β ^ (-(1 / 2 : ℝ) + 2 * ρ₂) * S.ξ ^ (((d : ℝ) - 2) / 2 - 2 * ((d : ℝ) - 2) * ρ₂)))
    (ht₂ : t₂ ≤ C₂ * (S.β ^ (-1 + ρ₁ + ρ₂) * S.ξ ^ ρ₀))
    (ht₃ : t₃ ≤ C₃ * (S.β ^ (-(1 / 2 : ℝ)) * S.ξ ^ γ))
    (ht₄ : t₄ ≤ C₄ * (S.β ^ (-(3 / 2 : ℝ) + ρ₁) * S.ξ ^ (2 * γ)))
    (ht₅ : t₅ ≤ C₅ * (S.β ^ (-1 : ℝ) * S.ξ ^ ((d : ℝ) - 2)))
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hC₃ : 0 ≤ C₃) (hC₄ : 0 ≤ C₄) (hC₅ : 0 ≤ C₅)
    (hβ0 : 2 * K0O * (C₁ + C₂ + C₃ + C₄ + C₅) ≤ S.β ^ (2 * ρ₂)) :
    K0O * (t₁ + t₂ + t₃ + t₄ + t₅) ≤ 1 / 2 * S.β ^ (-(1 / 2 : ℝ) + ρ₁) * S.ξ ^ ρ₀ := by
  have hD : (1 : ℝ) ≤ (d : ℝ) - 2 := S.hD
  have hβp := S.β_pos
  have hρ2 := hE.ρ₂_pos
  have hρ0 := hE.ρ₀_pos
  have E1 := hE.E1
  have E2 := hE.E2
  have E4 := hE.E4
  have E5 := hE.E5
  have E6 := hE.E6
  have hξ0 := S.ξ_pos
  have hξ1 := S.ξ_le_one
  have hρ6 : ρ₂ < 1 / 6 := by nlinarith
  have hγ : 0 < γ := by nlinarith
  set T : ℝ := S.β ^ (-(1 / 2 : ℝ) + ρ₁ - 2 * ρ₂) * S.ξ ^ ρ₀ with hT
  have g₁ : S.β ^ (-(1 / 2 : ℝ) + 2 * ρ₂) * S.ξ ^ (((d : ℝ) - 2) / 2 - 2 * ((d : ℝ) - 2) * ρ₂) ≤ T :=
    rpow_mul_rpow_le S.hβ hξ0 hξ1 (by linarith) (by nlinarith)
  have g₂ : S.β ^ (-1 + ρ₁ + ρ₂) * S.ξ ^ ρ₀ ≤ T :=
    rpow_mul_rpow_le S.hβ hξ0 hξ1 (by linarith) le_rfl
  have g₃ : S.β ^ (-(1 / 2 : ℝ)) * S.ξ ^ γ ≤ T :=
    rpow_mul_rpow_le S.hβ hξ0 hξ1 (by linarith) (by linarith)
  have g₄ : S.β ^ (-(3 / 2 : ℝ) + ρ₁) * S.ξ ^ (2 * γ) ≤ T :=
    rpow_mul_rpow_le S.hβ hξ0 hξ1 (by linarith) (by linarith)
  have g₅ : S.β ^ (-1 : ℝ) * S.ξ ^ ((d : ℝ) - 2) ≤ T :=
    rpow_mul_rpow_le S.hβ hξ0 hξ1 (by linarith) (by linarith)
  have hsum : t₁ + t₂ + t₃ + t₄ + t₅ ≤ (C₁ + C₂ + C₃ + C₄ + C₅) * T := by
    have i₁ := ht₁.trans (mul_le_mul_of_nonneg_left g₁ hC₁)
    have i₂ := ht₂.trans (mul_le_mul_of_nonneg_left g₂ hC₂)
    have i₃ := ht₃.trans (mul_le_mul_of_nonneg_left g₃ hC₃)
    have i₄ := ht₄.trans (mul_le_mul_of_nonneg_left g₄ hC₄)
    have i₅ := ht₅.trans (mul_le_mul_of_nonneg_left g₅ hC₅)
    linarith
  have hTe : T = S.β ^ (-(2 * ρ₂)) * (S.β ^ (-(1 / 2 : ℝ) + ρ₁) * S.ξ ^ ρ₀) := by
    rw [hT, ← mul_assoc, ← Real.rpow_add hβp]; congr 3; ring
  have hneg : S.β ^ (2 * ρ₂) * S.β ^ (-(2 * ρ₂)) = 1 := by
    rw [← Real.rpow_add hβp]; simp
  have hb0 : 0 ≤ S.β ^ (-(2 * ρ₂)) := Real.rpow_nonneg hβp.le _
  have hprod : 0 ≤ S.β ^ (-(1 / 2 : ℝ) + ρ₁) * S.ξ ^ ρ₀ := by positivity
  have hle : K0O * (C₁ + C₂ + C₃ + C₄ + C₅) * S.β ^ (-(2 * ρ₂)) ≤ 1 / 2 := by
    have h2 := mul_le_mul_of_nonneg_right hβ0 hb0
    rw [hneg] at h2
    linarith
  calc K0O * (t₁ + t₂ + t₃ + t₄ + t₅) ≤ K0O * ((C₁ + C₂ + C₃ + C₄ + C₅) * T) :=
        mul_le_mul_of_nonneg_left hsum hK
    _ = (K0O * (C₁ + C₂ + C₃ + C₄ + C₅) * S.β ^ (-(2 * ρ₂))) *
          (S.β ^ (-(1 / 2 : ℝ) + ρ₁) * S.ξ ^ ρ₀) := by rw [hTe]; ring
    _ ≤ 1 / 2 * (S.β ^ (-(1 / 2 : ℝ) + ρ₁) * S.ξ ^ ρ₀) := mul_le_mul_of_nonneg_right hle hprod
    _ = _ := by ring

/-- **The terms (3.3)** (OBSERVABLES §3.7, P9 p. 514): from `|μ_{k+1}| ≤ ½ β^{-1/2+ρ₁}
ξ_{k+1}^{ρ₀}` one gets `β_k^{-1/2} |μ_{k+1}| ≤ (√2/2) L^{D/2} β^{-1+ρ₁} ξ_{k+1}^{D/2+ρ₀}`
(`D = d - 2`). -/
theorem mu_shift_bound {D ρ₀ ρ₁ ρ₂ μ : ℝ} (S : StepScale D ρ₂)
    (hμ : |μ| ≤ 1 / 2 * S.β ^ (-(1 / 2 : ℝ) + ρ₁) * S.ξ ^ ρ₀) :
    S.βk ^ (-(1 / 2 : ℝ)) * |μ| ≤
      √2 / 2 * S.L ^ (D / 2) * S.β ^ (-1 + ρ₁) * S.ξ ^ (D / 2 + ρ₀) := by
  have hβp := S.β_pos
  have hb := S.betak_inv_sqrt_le
  have hξ0 := S.ξ_pos
  have hη0 := S.hη0
  have h1 := mul_le_mul hb hμ (abs_nonneg _) (by positivity)
  refine h1.trans (le_of_eq ?_)
  have e1 : S.η ^ (D / 2) = S.L ^ (D / 2) * S.ξ ^ (D / 2) := S.η_rpow_eq
  have e2 : S.β ^ (-(1 / 2 : ℝ)) * S.β ^ (-(1 / 2 : ℝ) + ρ₁) = S.β ^ (-1 + ρ₁) := by
    rw [← Real.rpow_add hβp]; congr 1; ring
  have e3 : S.ξ ^ (D / 2) * S.ξ ^ ρ₀ = S.ξ ^ (D / 2 + ρ₀) := by
    rw [← Real.rpow_add hξ0]
  rw [e1, ← e2, ← e3]; ring

/-- The terms (3.3) are `R^{j,k+1}`-terms: with the kernel bound `G₀` and `β ≥ β₀` (`hβ0`),
`(√2/2) L^{D/2} β^{-1+ρ₁} ξ^{D/2+ρ₀} G₀ ≤ β^{-1/2+ρ₁} ξ^{ρ₀}`. -/
theorem mu_kernel_bound {D ρ₀ ρ₁ ρ₂ G₀ : ℝ} (S : StepScale D ρ₂) (hG : 0 ≤ G₀) (hD0 : 0 ≤ D)
    (hβ0 : √2 / 2 * S.L ^ (D / 2) * G₀ ≤ S.β ^ (1 / 2 : ℝ)) :
    √2 / 2 * S.L ^ (D / 2) * S.β ^ (-1 + ρ₁) * S.ξ ^ (D / 2 + ρ₀) * G₀ ≤
      S.β ^ (-(1 / 2 : ℝ) + ρ₁) * S.ξ ^ ρ₀ := by
  have hβp := S.β_pos
  have hξ0 := S.ξ_pos
  have h1 : S.ξ ^ (D / 2 + ρ₀) ≤ S.ξ ^ ρ₀ :=
    Real.rpow_le_rpow_of_exponent_ge hξ0 S.ξ_le_one (by linarith)
  have e : S.β ^ (-1 + ρ₁) * S.β ^ (1 / 2 : ℝ) = S.β ^ (-(1 / 2 : ℝ) + ρ₁) := by
    rw [← Real.rpow_add hβp]; congr 1; ring
  have hb : 0 ≤ S.β ^ (-1 + ρ₁) := Real.rpow_nonneg hβp.le _
  have hL : 0 ≤ S.L ^ (D / 2) := Real.rpow_nonneg S.L_pos.le _
  calc √2 / 2 * S.L ^ (D / 2) * S.β ^ (-1 + ρ₁) * S.ξ ^ (D / 2 + ρ₀) * G₀
      ≤ √2 / 2 * S.L ^ (D / 2) * S.β ^ (-1 + ρ₁) * S.ξ ^ ρ₀ * G₀ := by gcongr
    _ = (S.β ^ (-1 + ρ₁) * (√2 / 2 * S.L ^ (D / 2) * G₀)) * S.ξ ^ ρ₀ := by ring
    _ ≤ (S.β ^ (-1 + ρ₁) * S.β ^ (1 / 2 : ℝ)) * S.ξ ^ ρ₀ := by gcongr
    _ = _ := by rw [e]

/-- **The shift term** (OBSERVABLES §3.7): with `β_{k+1} ≥ β ξ_{k+1}^{-D}/2` and
`ε_{k+1} = α₀ ξ_{k+1}^{D/2-γ}`, `β_k^{1/2} β_{k+1}^{-1} ε_{k+1}^{-1} ≤ (2√2/α₀) L^{-D/2}
β^{-1/2} ξ_{k+1}^{γ}`, i.e. `β_k^{1/2} |m_k δφ_{k+1}| ≤ C β^{-1/2} ξ_{k+1}^{γ}`. -/
theorem shift_bound {D ρ₂ γ α₀ βk1 : ℝ} (S : StepScale D ρ₂) (hα₀ : 0 < α₀)
    (hβk1 : S.β ≤ 2 * βk1 * S.ξ ^ D) (hβk1p : 0 < βk1) :
    S.βk ^ (1 / 2 : ℝ) * βk1⁻¹ * (α₀ * S.ξ ^ (D / 2 - γ))⁻¹ ≤
      2 * √2 / α₀ * S.L ^ (-(D / 2)) * S.β ^ (-(1 / 2 : ℝ)) * S.ξ ^ γ := by
  have hβp := S.β_pos
  have hη0 := S.hη0
  have hξ0 := S.ξ_pos
  have hLp := S.L_pos
  have h1 : S.βk ^ (1 / 2 : ℝ) ≤ (2 * S.β * S.η ^ (-D)) ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow S.βk_pos.le S.hβk_hi (by norm_num)
  have hxD : 0 < S.ξ ^ D := Real.rpow_pos_of_pos hξ0 D
  have h2 : βk1⁻¹ ≤ 2 * S.β⁻¹ * S.ξ ^ D := by
    rw [inv_eq_one_div, div_le_iff₀ hβk1p]
    have : 1 ≤ 2 * S.β⁻¹ * S.ξ ^ D * βk1 := by
      have e : 2 * S.β⁻¹ * S.ξ ^ D * βk1 = S.β⁻¹ * (2 * βk1 * S.ξ ^ D) := by ring
      rw [e]
      calc 1 = S.β⁻¹ * S.β := by field_simp
        _ ≤ S.β⁻¹ * (2 * βk1 * S.ξ ^ D) := mul_le_mul_of_nonneg_left hβk1 (by positivity)
    linarith
  have e1 : (2 * S.β * S.η ^ (-D)) ^ (1 / 2 : ℝ) = √2 * S.β ^ (1 / 2 : ℝ) * S.η ^ (-(D / 2)) := by
    have hη' : 0 < S.η ^ (-D) := Real.rpow_pos_of_pos hη0 _
    rw [Real.mul_rpow (by positivity) hη'.le, Real.mul_rpow (by norm_num) hβp.le,
      ← Real.rpow_mul hη0.le, Real.sqrt_eq_rpow]
    congr 3; ring
  have e2 : (α₀ * S.ξ ^ (D / 2 - γ))⁻¹ = α₀⁻¹ * (S.ξ ^ (D / 2 - γ))⁻¹ := mul_inv _ _
  have e3 : (S.ξ ^ (D / 2 - γ))⁻¹ = S.ξ ^ (-(D / 2 - γ)) := (Real.rpow_neg hξ0.le _).symm
  have e4 : S.η ^ (-(D / 2)) = S.L ^ (-(D / 2)) * S.ξ ^ (-(D / 2)) := S.η_rpow_eq
  have hβh : S.β ^ (1 / 2 : ℝ) * S.β⁻¹ = S.β ^ (-(1 / 2 : ℝ)) := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hβp]; congr 1; ring
  have hξe : S.ξ ^ (-(D / 2)) * S.ξ ^ D * S.ξ ^ (-(D / 2 - γ)) = S.ξ ^ γ := by
    rw [← Real.rpow_add hξ0, ← Real.rpow_add hξ0]; congr 1; ring
  have hpos1 : 0 ≤ βk1⁻¹ := by positivity
  have hpos2 : 0 ≤ (α₀ * S.ξ ^ (D / 2 - γ))⁻¹ := by positivity
  calc S.βk ^ (1 / 2 : ℝ) * βk1⁻¹ * (α₀ * S.ξ ^ (D / 2 - γ))⁻¹
      ≤ (2 * S.β * S.η ^ (-D)) ^ (1 / 2 : ℝ) * (2 * S.β⁻¹ * S.ξ ^ D) *
          (α₀ * S.ξ ^ (D / 2 - γ))⁻¹ := by gcongr
    _ = 2 * √2 / α₀ * S.L ^ (-(D / 2)) * (S.β ^ (1 / 2 : ℝ) * S.β⁻¹) *
          (S.ξ ^ (-(D / 2)) * S.ξ ^ D * S.ξ ^ (-(D / 2 - γ))) := by
        rw [e1, e2, e3, e4]; field_simp
    _ = _ := by rw [hβh, hξe]

/-- **The normalization (3.2)** (OBSERVABLES §3.7): if `∑_Y M_u(x, Y; h, h) = μ_{k+1}(x) h` and
the localization of the background sums to `∑_Y φ_{k+1}(x, Y; h, h) = h`, then
`M^{(k+1)} := M_u - μ_{k+1} φ_{k+1}` satisfies `∑_Y M^{(k+1)}(x, Y; h, h) = 0`: (2.1) at level
`k + 1`. -/
theorem normalization_sum_eq_zero {ι V R : Type*} [Fintype ι] [Ring R] [AddCommGroup V]
    [Module R V] (Mu φ : ι → V) (μ : R) (h : V) (hMu : ∑ Y, Mu Y = μ • h)
    (hφ : ∑ Y, φ Y = h) : ∑ Y, (Mu Y - μ • φ Y) = 0 := by
  rw [Finset.sum_sub_distrib, ← Finset.smul_sum, hMu, hφ, sub_self]

end Balaban.Observables
