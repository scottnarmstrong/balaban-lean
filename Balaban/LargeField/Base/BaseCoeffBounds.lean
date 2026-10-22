module

public import Balaban.SmallField.Def6
public import Balaban.Flow.RGInfty

/-!
# The coefficient bounds (H.6) at scale `1` from the solution of the first step

The counterterm system of the first step (`BaseRgStep`) gives a real solution `ξ⁰ = (ξ₁, ξ₂, ξ₃)` with
`‖ξ⁰‖ ≤ (c₈/4) q`, `q = L^{-2γ}`.  The running coefficients at scale `1` are
`β₁ = β L^{d-2}/(1 + ξ₃)` and `ν₁ = ν L² (1 + ξ₃)/(1 + ξ₂)` (P4 (5.28)), with the kernel constant of the
free flow for `a₁`.  `baseCoeffBounds` is `CoeffBounds d L 1 P` for these sequences.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.SmallField Balaban.SmallField.Def6

/-- The coefficient `β₁ = β L^{d-2}/(1 + ξ₃)`; `β₀ = β`. -/
noncomputable def baseBetaSeq (d L : ℕ) (β : ℝ) (ξ : Fin 3 → ℂ) : ℕ → ℝ
  | 0 => β
  | _ + 1 => β * (L : ℝ) ^ (d - 2) / (1 + (ξ 2).re)

/-- The coefficient `ν₁ = ν L² (1 + ξ₃)/(1 + ξ₂)`; `ν₀ = ν`. -/
noncomputable def baseNuSeq (L : ℕ) (ν : ℝ) (ξ : Fin 3 → ℂ) : ℕ → ℝ
  | 0 => ν
  | _ + 1 => ν * (L : ℝ) ^ 2 * (1 + (ξ 2).re) / (1 + (ξ 1).re)

/-- **(H.6) at scale `1`.**  For a real solution `ξ` of the first step with `‖ξ‖ ≤ (c₈/4) q`, the
coefficients `β₁, ν₁` above and the kernel constant `aKer` in the window of `a₁`: `CoeffBounds d L 1 P`.
The inequalities `5/4 B < β` and `5/3 · ν L² ≤ ν̄` are the sizes that the factors
`(1+ξ₃)^{-1} ≥ 4/5` and `(1+ξ₃)/(1+ξ₂) ≤ 5/3` need (`‖ξ‖ ≤ 1/4`). -/
theorem baseCoeffBounds (d L : ℕ) (P : Consts) {β ν aKer : ℝ} {ξ : Fin 3 → ℂ}
    (hreal : ∀ i, (ξ i).im = 0)
    (hξ : ‖ξ‖ ≤ P.c₈ / 4 * Flow.rate (L : ℝ) P.γ)
    (hs : P.c₈ * Flow.rate (L : ℝ) P.γ ≤ 1 - Flow.rate (L : ℝ) P.γ)
    (hq : P.c₈ / 4 * Flow.rate (L : ℝ) P.γ ≤ 1 / 4) (hL : 0 < L)
    (hβ : 5 / 4 * P.B < β) (hB : 0 ≤ P.B) (hν0 : 0 < ν) (hν : 5 / 3 * (ν * (L : ℝ) ^ 2) ≤ P.νbar)
    (haL : 9 / 10 * (1 - ((L : ℝ) ^ 2)⁻¹)⁻¹ ≤ aKer) (haH : aKer < 3 / 2) :
    CoeffBounds d L 1 P (baseBetaSeq d L β ξ) (baseNuSeq L ν ξ) (fun _ => aKer) := by
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have hc8 : ∀ i, |(ξ i).re| ≤ 1 / 4 := fun i => by
    have h1 : ‖ξ i‖ ≤ ‖ξ‖ := norm_le_pi_norm ξ i
    have h2 : |(ξ i).re| ≤ ‖ξ i‖ := Complex.abs_re_le_norm _
    linarith
  have h2 := abs_le.mp (hc8 1)
  have h3 := abs_le.mp (hc8 2)
  have hξi : ∀ i, ξ i = (((ξ i).re : ℝ) : ℂ) := fun i => Complex.ext (by simp) (by simpa using hreal i)
  have hp3 : 0 < 1 + (ξ 2).re := by linarith
  have hp2 : 0 < 1 + (ξ 1).re := by linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨fun n => if n = 0 then ξ else 0, β, ν, ?_, hs, ?_⟩
    · intro n
      by_cases hn : n = 0
      · subst hn; simpa using hξ
      · simp only [hn, ↓reduceIte, norm_zero]
        have : 0 ≤ P.c₈ / 4 * Flow.rate (L : ℝ) P.γ ^ (n + 1) := by
          have hr : 0 ≤ Flow.rate (L : ℝ) P.γ := (Flow.rate_pos hLr _).le
          have hc : 0 ≤ P.c₈ := by
            by_contra hneg
            push Not at hneg
            have : P.c₈ / 4 * Flow.rate (L : ℝ) P.γ < 0 :=
              mul_neg_of_neg_of_pos (by linarith) (Flow.rate_pos hLr _)
            have := norm_nonneg ξ
            linarith
          positivity
        exact this
    · intro n hn
      interval_cases n
      · simp [baseBetaSeq, baseNuSeq, Flow.betaSeq, Flow.nuSeq]
      · constructor
        · simp only [Flow.betaSeq, baseBetaSeq, ↓reduceIte]
          rw [hξi 2]
          push_cast
          simp
        · simp only [Flow.nuSeq, baseNuSeq, ↓reduceIte]
          rw [hξi 2, hξi 1]
          push_cast
          simp
  · show P.B * (L : ℝ) ^ (1 * (d - 2)) < β * (L : ℝ) ^ (d - 2) / (1 + (ξ 2).re)
    rw [one_mul, lt_div_iff₀ hp3]
    have hpos : 0 < (L : ℝ) ^ (d - 2) := pow_pos hLr _
    have hb : P.B * (1 + (ξ 2).re) < β := by nlinarith
    calc P.B * (L : ℝ) ^ (d - 2) * (1 + (ξ 2).re) = P.B * (1 + (ξ 2).re) * (L : ℝ) ^ (d - 2) := by ring
      _ < β * (L : ℝ) ^ (d - 2) := mul_lt_mul_of_pos_right hb hpos
  · show 0 < ν * (L : ℝ) ^ 2 * (1 + (ξ 2).re) / (1 + (ξ 1).re)
    positivity
  · show ν * (L : ℝ) ^ 2 * (1 + (ξ 2).re) / (1 + (ξ 1).re) ≤ P.νbar
    rw [div_le_iff₀ hp2]
    have : 0 < ν * (L : ℝ) ^ 2 := by positivity
    nlinarith
  · exact haL
  · exact haH

/-- The bound of the solution of the first step, `‖ξ⁰‖ ≤ C_ξ β⁻¹ q` (`baseRg_step`), is the bound
`(c₈/4) q` of (H.6) when `C_ξ β⁻¹ ≤ c₈/4`, i.e. `c₈ = 4 C_ξ/β` or larger. -/
theorem norm_le_c8_of_step {C β q c₈ : ℝ} {ξ : Fin 3 → ℂ} (hq : 0 ≤ q) (hξ : ‖ξ‖ ≤ C * (β⁻¹ * q))
    (hC : C * β⁻¹ ≤ c₈ / 4) : ‖ξ‖ ≤ c₈ / 4 * q :=
  hξ.trans (by
    calc C * (β⁻¹ * q) = (C * β⁻¹) * q := by ring
      _ ≤ c₈ / 4 * q := mul_le_mul_of_nonneg_right hC hq)

end Balaban.LargeField
