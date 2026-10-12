/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.RenormTermwiseBound

/-!
# Lemma 3.2 (iii): the termwise irrelevance bound

`termwise_irrelevant`: for a polymer `X ∈ T.polys` and data satisfying (Σ1), (Σ2),
`‖I(y,X)‖ ≤ C E₀ e^{-(κ-1) d_j(X)} σ^{3-α₁} (ε/ρ)²`, under the premises `PremisesTerm`
(no renormalization conditions are needed).  `termwise_irrelevant_scaled` is the form (3.1):
with `σ = C₀ s` and `ε/ρ ≤ K_R s^{(d-2)/2 - γ}` the bound is `C_I E₀ s^{d+α₃} e^{-(κ-1)d_j(X)}`,
`α₃ = 1 - 2γ - α₁`.

The polynomial weight `|X|² (1 + d_j(X))⁶` of the landed per-term estimate is absorbed into
`e^{-d_j(X)}` using the path bound `diam`, which gives `|X| ≤ (2A(1 + d_j(X)) + 1)^d`.
-/

@[expose] public section

open Metric Set Matrix

namespace Balaban.SmallField

variable {d N : ℕ}

theorem card_le_of_diam {T : TermFamily d N} {i₀ i₁ : Fin N} {ν ρ E₀ κ A K₀ : ℝ}
    {Dom : Set ((Site d → Spin N) × Spin N)} (hP : PremisesTerm T i₀ i₁ ν ρ E₀ κ A K₀ Dom)
    {X : Finset (Site d)} (hX : X ∈ T.polys) :
    (X.card : ℝ) ≤ (2 * (A * (1 + T.dist X)) + 1) ^ d := by
  classical
  set Rr : ℝ := A * (1 + T.dist X) with hRr
  have hR0 : 0 ≤ Rr := by
    have h0 := hP.diam X hX 0 (hP.zero_mem X hX)
    refine le_trans ?_ h0
    simp
  set m : ℤ := ⌊Rr⌋ with hm
  have hm0 : 0 ≤ m := Int.floor_nonneg.mpr hR0
  have hsub : X ⊆ Fintype.piFinset (fun _ : Fin d => Finset.Icc (-m) m) := by
    intro x hx
    rw [Fintype.mem_piFinset]
    intro μ
    have h1 := hP.diam X hX x hx
    have h2 : |x μ| ≤ ∑ ν, |x ν| := Finset.single_le_sum (f := fun ν => |x ν|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ μ)
    have h3 : ((|x μ| : ℤ) : ℝ) ≤ Rr := by
      refine le_trans ?_ h1
      exact_mod_cast h2
    have h4 : |x μ| ≤ m := Int.le_floor.mpr h3
    exact Finset.mem_Icc.mpr (abs_le.mp h4)
  have hc := Finset.card_le_card hsub
  rw [Fintype.card_piFinset] at hc
  simp only [Int.card_Icc, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hc
  have hc' : (X.card : ℝ) ≤ (((m + 1 - -m).toNat : ℕ) : ℝ) ^ d := by exact_mod_cast hc
  refine hc'.trans ?_
  have hm1 : (((m + 1 - -m).toNat : ℕ) : ℝ) = 2 * (m : ℝ) + 1 := by
    have : ((m + 1 - -m).toNat : ℤ) = m + 1 - -m := Int.toNat_of_nonneg (by omega)
    have h2 : (((m + 1 - -m).toNat : ℕ) : ℝ) = (((m + 1 - -m).toNat : ℤ) : ℝ) := by
      norm_cast
    rw [h2, this]; push_cast; ring
  rw [hm1]
  have hmR : (m : ℝ) ≤ Rr := Int.floor_le Rr
  have h5 : 2 * (m : ℝ) + 1 ≤ 2 * Rr + 1 := by linarith
  have h6 : 0 ≤ 2 * (m : ℝ) + 1 := by have : (0 : ℝ) ≤ m := by exact_mod_cast hm0
                                      linarith
  exact pow_le_pow_left₀ h6 h5 d

/-- The polynomial weight is absorbed into `e^{-t}`. -/
theorem weight_absorb (A : ℝ) (hA : 0 ≤ A) (d : ℕ) :
    ∃ Cw : ℝ, 0 ≤ Cw ∧ ∀ (κ t P : ℝ), 0 ≤ t → 0 ≤ P → P ≤ (2 * (A * (1 + t)) + 1) ^ d →
      Real.exp (-κ * t) * (P ^ 2 * (1 + t) ^ 6) ≤ Cw * Real.exp (-(κ - 1) * t) := by
  refine ⟨(2 * A + 1) ^ (2 * d) * ((2 * d + 6).factorial : ℝ) * Real.exp 1, by positivity, ?_⟩
  intro κ t P ht hP0 hP
  have ht1 : (1 : ℝ) ≤ 1 + t := by linarith
  have h1 : 2 * (A * (1 + t)) + 1 ≤ (2 * A + 1) * (1 + t) := by nlinarith
  have h2 : P ≤ ((2 * A + 1) * (1 + t)) ^ d :=
    hP.trans (pow_le_pow_left₀ (by positivity) h1 d)
  have h3 : P ^ 2 ≤ ((2 * A + 1) ^ (2 * d)) * (1 + t) ^ (2 * d) := by
    calc P ^ 2 ≤ (((2 * A + 1) * (1 + t)) ^ d) ^ 2 := pow_le_pow_left₀ hP0 h2 2
      _ = _ := by rw [← pow_mul, mul_pow, mul_comm d 2]
  have h4 : (1 + t) ^ (2 * d + 6) ≤ ((2 * d + 6).factorial : ℝ) * Real.exp (1 + t) := by
    have := Real.pow_div_factorial_le_exp (1 + t) (by linarith) (2 * d + 6)
    rw [div_le_iff₀ (by positivity)] at this
    linarith
  have hexp : Real.exp (-κ * t) = Real.exp (-(κ - 1) * t) * Real.exp (-t) := by
    rw [← Real.exp_add]; congr 1; ring
  calc Real.exp (-κ * t) * (P ^ 2 * (1 + t) ^ 6)
      ≤ Real.exp (-κ * t) * (((2 * A + 1) ^ (2 * d)) * (1 + t) ^ (2 * d) * (1 + t) ^ 6) := by
        gcongr
    _ = Real.exp (-(κ - 1) * t) * ((2 * A + 1) ^ (2 * d)) *
          ((1 + t) ^ (2 * d + 6) * Real.exp (-t)) := by
        rw [hexp]; ring
    _ ≤ Real.exp (-(κ - 1) * t) * ((2 * A + 1) ^ (2 * d)) *
          (((2 * d + 6).factorial : ℝ) * Real.exp (1 + t) * Real.exp (-t)) := by
        gcongr
    _ = _ := by
        rw [mul_assoc ((2 * d + 6).factorial : ℝ), ← Real.exp_add]
        have : (1 + t + -t) = 1 := by ring
        rw [this]; ring

theorem termwise_irrelevant (d N : ℕ) (A Λ Ksig α₁ : ℝ) (hA : 0 ≤ A) (hΛ : 1 ≤ Λ)
    (hKsig : 0 ≤ Ksig) (hα0 : 0 < α₁) (hα1 : α₁ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : TermFamily d N) (i₀ i₁ : Fin N)
      (ν ρ E₀ κ K₀ : ℝ) (Dom : Set ((Site d → Spin N) × Spin N))
      (_ : PremisesTerm T i₀ i₁ ν ρ E₀ κ A K₀ Dom) (ψ : Site d → Spin N) (b : Spin N)
      (σ ε K₂ : ℝ) (_ : DataHyp Dom ν σ ε K₂ ψ b) (X : Finset (Site d)) (_ : X ∈ T.polys),
      0 < ρ → ρ ≤ 1 → 0 < ε → ε ≤ Λ * ρ → 0 < σ → σ ≤ 1 → σ ^ 2 * ε ≤ 1 / 4 → 0 ≤ ν → ν ≤ σ ^ 2 →
      0 ≤ E₀ → K₂ ≤ Ksig * σ ^ (2 - α₁) * ε →
      ‖Itw T i₀ i₁ ν X ψ b‖ ≤
        C * E₀ * Real.exp (-(κ - 1) * T.dist X) * (σ ^ (3 - α₁) * (ε / ρ) ^ 2) := by
  obtain ⟨Cs, hCs0, hCs⟩ := smallBnd_le N A Λ Ksig hA hΛ hKsig
  obtain ⟨Ct, hCt0, hCt⟩ := tailBnd_le N A Λ hA hΛ
  obtain ⟨Cw, hCw0, hCw⟩ := weight_absorb A hA d
  have hC1 : 0 ≤ cC1 N := by unfold cC1; positivity
  refine ⟨(Cs + Ct + 12 * cC1 N ^ 2) * Cw, by positivity, ?_⟩
  intro T i₀ i₁ ν ρ E₀ κ K₀ Dom hP ψ b σ ε K₂ dat X hX hρ hρ1 hε hεΛ hσ hσ1 hτ hν hνσ hE0 hK
  obtain ⟨u, R, hF⟩ := exists_frame i₀ dat hτ
  have c : CtxTw T i₀ i₁ ν ρ E₀ κ A K₀ Dom ψ b σ ε K₂ u R :=
    ⟨hP, dat, hF, hσ, hσ1, hε, hρ, hρ1, hν, hνσ, hE0, hA, hτ⟩
  have h := c.itw_bound_raw hCs0 hCt0 hα0 hα1 hCs hCt hεΛ hK hX
  refine h.trans ?_
  have hd0 := hP.dist_nonneg X hX
  have hcard := card_le_of_diam hP hX
  have hab := hCw κ (T.dist X) (X.card : ℝ) hd0 (Nat.cast_nonneg _) hcard
  have hT0 : 0 ≤ σ ^ (3 - α₁) * (ε / ρ) ^ 2 :=
    mul_nonneg (Real.rpow_pos_of_pos hσ _).le (sq_nonneg _)
  have hCsum : 0 ≤ Cs + Ct + 12 * cC1 N ^ 2 := by positivity
  calc (Cs + Ct + 12 * cC1 N ^ 2) *
        (E₀ * Real.exp (-κ * T.dist X) * ((X.card : ℝ) ^ 2 * (1 + T.dist X) ^ 6)) *
        (σ ^ (3 - α₁) * (ε / ρ) ^ 2)
      = (Cs + Ct + 12 * cC1 N ^ 2) * E₀ *
        (Real.exp (-κ * T.dist X) * ((X.card : ℝ) ^ 2 * (1 + T.dist X) ^ 6)) *
        (σ ^ (3 - α₁) * (ε / ρ) ^ 2) := by ring
    _ ≤ (Cs + Ct + 12 * cC1 N ^ 2) * E₀ * (Cw * Real.exp (-(κ - 1) * T.dist X)) *
        (σ ^ (3 - α₁) * (ε / ρ) ^ 2) := by
        have : 0 ≤ (Cs + Ct + 12 * cC1 N ^ 2) * E₀ := mul_nonneg hCsum hE0
        gcongr
    _ = _ := by ring

/-- **Lemma 3.2 (iii), the form (3.1)**: with `σ = C₀ s` and `ε/ρ = ε_k/ε_j ≤ K_R s^{(d-2)/2 - γ}`
(the scale ratio of FLUCTUATION.md §3.2 / SF (2.2)), `α₃ = 1 - 2γ - α₁`:
`|I(y,X)| ≤ C_I E₀ s^{d+α₃} e^{-(κ-1) d_j(X)}`. -/
theorem termwise_irrelevant_scaled (d N : ℕ) (A Λ Ksig α₁ γ C₀ KR : ℝ) (hA : 0 ≤ A) (hΛ : 1 ≤ Λ)
    (hKsig : 0 ≤ Ksig) (hα0 : 0 < α₁) (hα1 : α₁ < 1) (hC₀ : 0 < C₀) :
    ∃ CI : ℝ, 0 ≤ CI ∧ ∀ (T : TermFamily d N) (i₀ i₁ : Fin N)
      (ν ρ E₀ κ K₀ : ℝ) (Dom : Set ((Site d → Spin N) × Spin N))
      (_ : PremisesTerm T i₀ i₁ ν ρ E₀ κ A K₀ Dom) (ψ : Site d → Spin N) (b : Spin N)
      (s σ ε K₂ : ℝ) (_ : DataHyp Dom ν σ ε K₂ ψ b) (X : Finset (Site d)) (_ : X ∈ T.polys),
      0 < s → σ = C₀ * s → ε / ρ ≤ KR * s ^ (((d : ℝ) - 2) / 2 - γ) →
      0 < ρ → ρ ≤ 1 → 0 < ε → ε ≤ Λ * ρ → σ ≤ 1 → σ ^ 2 * ε ≤ 1 / 4 → 0 ≤ ν → ν ≤ σ ^ 2 →
      0 ≤ E₀ → K₂ ≤ Ksig * σ ^ (2 - α₁) * ε →
      ‖Itw T i₀ i₁ ν X ψ b‖ ≤
        CI * E₀ * s ^ ((d : ℝ) + (1 - 2 * γ - α₁)) * Real.exp (-(κ - 1) * T.dist X) := by
  obtain ⟨C, hC0, hC⟩ := termwise_irrelevant d N A Λ Ksig α₁ hA hΛ hKsig hα0 hα1
  refine ⟨C * (C₀ ^ (3 - α₁) * KR ^ 2), by positivity, ?_⟩
  intro T i₀ i₁ ν ρ E₀ κ K₀ Dom hP ψ b s σ ε K₂ dat X hX hs hσs hR hρ hρ1 hε hεΛ hσ1 hτ hν hνσ hE0 hK
  have hσ : 0 < σ := by rw [hσs]; positivity
  have h := hC T i₀ i₁ ν ρ E₀ κ K₀ Dom hP ψ b σ ε K₂ dat X hX hρ hρ1 hε hεΛ hσ hσ1 hτ hν hνσ hE0 hK
  refine h.trans ?_
  have hr0 : 0 ≤ ε / ρ := by positivity
  have h1 : (ε / ρ) ^ 2 ≤ KR ^ 2 * s ^ (2 * (((d : ℝ) - 2) / 2 - γ)) := by
    have := pow_le_pow_left₀ hr0 hR 2
    refine this.trans (le_of_eq ?_)
    rw [mul_pow]
    congr 1
    rw [← Real.rpow_natCast, ← Real.rpow_mul hs.le]
    norm_num
    ring_nf
  have h2 : σ ^ (3 - α₁) = C₀ ^ (3 - α₁) * s ^ (3 - α₁) := by
    rw [hσs, Real.mul_rpow hC₀.le hs.le]
  have h3 : s ^ (3 - α₁) * s ^ (2 * (((d : ℝ) - 2) / 2 - γ)) =
      s ^ ((d : ℝ) + (1 - 2 * γ - α₁)) := by
    rw [← Real.rpow_add hs]; congr 1; ring
  have hs0 : 0 ≤ s ^ (3 - α₁) := (Real.rpow_pos_of_pos hs _).le
  calc C * E₀ * Real.exp (-(κ - 1) * T.dist X) * (σ ^ (3 - α₁) * (ε / ρ) ^ 2)
      ≤ C * E₀ * Real.exp (-(κ - 1) * T.dist X) *
        (C₀ ^ (3 - α₁) * s ^ (3 - α₁) * (KR ^ 2 * s ^ (2 * (((d : ℝ) - 2) / 2 - γ)))) := by
        rw [h2]
        have : 0 ≤ C * E₀ * Real.exp (-(κ - 1) * T.dist X) := by positivity
        gcongr
    _ = C * (C₀ ^ (3 - α₁) * KR ^ 2) * E₀ * (s ^ (3 - α₁) * s ^ (2 * (((d : ℝ) - 2) / 2 - γ))) *
        Real.exp (-(κ - 1) * T.dist X) := by ring
    _ = _ := by rw [h3]

end Balaban.SmallField
