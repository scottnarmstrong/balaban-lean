/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Correlations.C1Star

/-!
# Extending a stopped physical flow for C-1*

At positive field the physical construction stops at `J ν`. The clauses of `C1Star` quantify
over all indices. Values beyond the stop can be set to zero. At zero field the physical
sequence is retained, and `J ν → ∞` makes each fixed index eventually physical as `ν ↓ 0`.
-/

@[expose] public section

namespace Balaban.Correlations

open Filter Topology Balaban.Flow

/-- The coefficient bound and continuity in `C1StarF1` follow from the physical steps
before the stop and from the massless flow. The values after the stop are zero. -/
theorem c1StarF1_of_stopped_steps (L : ℕ) (γ₀ cXi β : ℝ) (hL : (0 : ℝ) < L)
    (hcXi : 0 ≤ cXi) (hβ : 0 < β) (J : ℝ → ℕ)
    (ξraw : ℝ → ℕ → Fin 3 → ℝ)
    (hJ : Tendsto J (𝓝[>] (0 : ℝ)) atTop)
    (hzero : ∀ k, ‖ξraw 0 k‖ ≤ cXi / (4 * β) * rate (L : ℝ) γ₀ ^ (k + 1))
    (hstep : ∀ ν ∈ Set.Ioc (0 : ℝ) 1, ∀ k, k < J ν →
      ‖ξraw ν k‖ ≤ cXi / (4 * β) * rate (L : ℝ) γ₀ ^ (k + 1))
    (hcont : ∀ k, Tendsto (fun ν => ξraw ν k) (𝓝[>] (0 : ℝ)) (𝓝 (ξraw 0 k))) :
    C1StarF1 L γ₀ cXi β
      (fun ν k => if k < J ν then ξraw ν k else if ν = 0 then ξraw 0 k else 0) := by
  have hnonneg : ∀ k : ℕ, 0 ≤ cXi / (4 * β) * rate (L : ℝ) γ₀ ^ (k + 1) := by
    intro k
    exact mul_nonneg (div_nonneg hcXi (by positivity)) (pow_nonneg (rate_pos hL γ₀).le _)
  constructor
  · intro ν hν k
    by_cases hz : ν = 0
    · subst ν
      by_cases hk : k < J 0
      · simpa [hk] using hzero k
      · simpa [hk] using hzero k
    · by_cases hk : k < J ν
      · simpa [hk] using hstep ν ⟨lt_of_le_of_ne hν.1 (Ne.symm hz), hν.2⟩ k hk
      · simpa [hk, hz] using hnonneg k
  · intro k
    have hevent : ∀ᶠ ν in 𝓝[>] (0 : ℝ), k < J ν := by
      filter_upwards [(tendsto_atTop.1 hJ (k + 1))] with ν hν
      omega
    have heq : (fun ν => if k < J ν then ξraw ν k else if ν = 0 then ξraw 0 k else 0) =ᶠ[𝓝[>] (0 : ℝ)]
        (fun ν => ξraw ν k) := by
      filter_upwards [hevent] with ν hk
      simp [hk]
    have hvalue : (if k < J 0 then ξraw 0 k else if (0 : ℝ) = 0 then ξraw 0 k else 0) =
        ξraw 0 k := by
      split_ifs <;> simp_all
    change Tendsto
      (fun ν => if k < J ν then ξraw ν k else if ν = 0 then ξraw 0 k else 0)
      (𝓝[>] (0 : ℝ))
      (𝓝 (if k < J 0 then ξraw 0 k else if (0 : ℝ) = 0 then ξraw 0 k else 0))
    rw [hvalue]
    exact (hcont k).congr' heq.symm

/-- The scalar observable bound and continuity extend past the physical stop by zero.
The scale-zero value is retained from the massless flow. -/
theorem stopped_mu_bound_cont {d : ℕ} (L : ℕ) (cStar ρ₀ ρ₁ β : ℝ) (hL : (0 : ℝ) < L)
    (hcStar : 0 ≤ cStar) (hβ : 0 < β) (J : ℝ → ℕ)
    (μraw : ℕ → ℝ → (Fin d → ℤ) → ℝ)
    (hJ : Tendsto J (𝓝[>] (0 : ℝ)) atTop)
    (hzero : ∀ j, 1 ≤ j → ∀ x,
      |μraw j 0 x| ≤ cStar * β ^ (-(1 / 2 : ℝ) + ρ₁) * (L : ℝ) ^ (-((j : ℝ) * ρ₀)))
    (hstep : ∀ j, 1 ≤ j → ∀ ν ∈ Set.Ioc (0 : ℝ) 1, j ≤ J ν → ∀ x,
      |μraw j ν x| ≤ cStar * β ^ (-(1 / 2 : ℝ) + ρ₁) * (L : ℝ) ^ (-((j : ℝ) * ρ₀)))
    (hcont : ∀ j x, Tendsto (fun ν => μraw j ν x) (𝓝[>] (0 : ℝ)) (𝓝 (μraw j 0 x))) :
    (∀ j, 1 ≤ j → ∀ ν ∈ Set.Icc (0 : ℝ) 1, ∀ x,
      |(if j ≤ J ν then μraw j ν x else if ν = 0 then μraw j 0 x else 0)| ≤
        cStar * β ^ (-(1 / 2 : ℝ) + ρ₁) * (L : ℝ) ^ (-((j : ℝ) * ρ₀))) ∧
    (∀ j x, Tendsto
      (fun ν => if j ≤ J ν then μraw j ν x else if ν = 0 then μraw j 0 x else 0)
      (𝓝[>] (0 : ℝ)) (𝓝 (μraw j 0 x))) := by
  have hnonneg : ∀ j : ℕ,
      0 ≤ cStar * β ^ (-(1 / 2 : ℝ) + ρ₁) * (L : ℝ) ^ (-((j : ℝ) * ρ₀)) := by
    intro j
    exact mul_nonneg (mul_nonneg hcStar (Real.rpow_nonneg hβ.le _))
      (Real.rpow_nonneg hL.le _)
  constructor
  · intro j hj ν hν x
    by_cases hz : ν = 0
    · subst ν
      by_cases hjJ : j ≤ J 0
      · simpa [hjJ] using hzero j hj x
      · simpa [hjJ] using hzero j hj x
    · by_cases hjJ : j ≤ J ν
      · simpa [hjJ] using hstep j hj ν ⟨lt_of_le_of_ne hν.1 (Ne.symm hz), hν.2⟩ hjJ x
      · simpa [hjJ, hz] using hnonneg j
  · intro j x
    have hevent : ∀ᶠ ν in 𝓝[>] (0 : ℝ), j ≤ J ν := tendsto_atTop.1 hJ j
    have heq : (fun ν => if j ≤ J ν then μraw j ν x else if ν = 0 then μraw j 0 x else 0) =ᶠ[𝓝[>] (0 : ℝ)]
        (fun ν => μraw j ν x) := by
      filter_upwards [hevent] with ν hν
      simp [hν]
    exact (hcont j x).congr' heq.symm

/-- A running product at level `j` uses only coefficient steps below `j`. -/
theorem gammaR_eq_of_prefix (ξ ζ : ℕ → Fin 3 → ℝ) (j : ℕ)
    (hprefix : ∀ i, i < j → ξ i = ζ i) : gammaR ξ j = gammaR ζ j := by
  unfold gammaR Flow.gammaSeq
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  simp only [xiC]
  rw [hprefix i (Finset.mem_range.mp hi)]

/-- The mass product has the same prefix property. -/
theorem deltaR_eq_of_prefix (ξ ζ : ℕ → Fin 3 → ℝ) (j : ℕ)
    (hprefix : ∀ i, i < j → ξ i = ζ i) : deltaR ξ j = deltaR ζ j := by
  unfold deltaR Flow.deltaSeq
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  simp only [xiC]
  rw [hprefix i (Finset.mem_range.mp hi)]

/-- The running inverse temperature at level `j` depends only on earlier steps. -/
theorem betaR_eq_of_prefix (L d : ℕ) (β : ℝ) (ξ ζ : ℕ → Fin 3 → ℝ) (j : ℕ)
    (hprefix : ∀ i, i < j → ξ i = ζ i) :
    betaR L d ξ β j = betaR L d ζ β j := by
  unfold betaR
  have hγ : Flow.gammaSeq (xiC ξ) j = Flow.gammaSeq (xiC ζ) j := by
    unfold Flow.gammaSeq
    apply Finset.prod_congr rfl
    intro i hi
    simp only [xiC]
    rw [hprefix i (Finset.mem_range.mp hi)]
  rw [Flow.betaSeq_eq, Flow.betaSeq_eq, hγ]

/-- The finite observable magnetization is unchanged by extending the coefficients and
observables past its last scale. -/
theorem magJ_eq_of_prefix (L d : ℕ) (β : ℝ) (J : ℕ)
    (ξ ζ : ℕ → Fin 3 → ℝ) (μ η : ℕ → (Fin d → ℤ) → ℝ)
    (hξ : ∀ i, i < J → ξ i = ζ i)
    (hμ : ∀ j, 1 ≤ j → j ≤ J → ∀ x, μ j x = η j x) (x : Fin d → ℤ) :
    magJ L d ξ μ β J x = magJ L d ζ η β J x := by
  unfold magJ
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hjJ : j < J := Finset.mem_range.mp hj
  rw [betaR_eq_of_prefix L d β ξ ζ j (fun i hi => hξ i (hi.trans hjJ))]
  rw [hμ (j + 1) (by omega) (by omega) x]

/-- The finite transverse Gaussian sum depends only on coefficients below `J`. -/
theorem mainTr_eq_of_prefix (d L : ℕ) [NeZero L] (a β ν : ℝ) (J ℓ : ℕ)
    (ξ ζ : ℕ → Fin 3 → ℝ) (hξ : ∀ i, i < J → ξ i = ζ i)
    (x y : Fin d → ℤ) :
    mainTr d L a ξ β ν J ℓ x y = mainTr d L a ζ β ν J ℓ x y := by
  unfold mainTr
  apply Finset.sum_congr rfl
  intro j hj
  have hjJ : j < J := Finset.mem_range.mp hj
  rw [gammaR_eq_of_prefix ξ ζ j (fun i hi => hξ i (hi.trans hjJ))]
  rw [deltaR_eq_of_prefix ξ ζ j (fun i hi => hξ i (hi.trans hjJ))]

end Balaban.Correlations
