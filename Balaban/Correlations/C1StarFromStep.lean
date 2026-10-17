/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Correlations.C1StarFromStepCore

/-!
# C-1* from named physical step outputs

The coefficient equations, the scalar observable at each RG step, the final source
derivatives, and the two parameter limits are separate premises. The theorem assembles
them into `C1Star`. The coefficient and observable families are extended by zero after
the positive-field stop; finite sums are unchanged by that extension.
-/

@[expose] public section

namespace Balaban.Correlations

open Filter Topology

/-- Assemble `C1Star` from scale-resolved physical step outputs. The two equations in
`hcoeffZero` and `hcoeffStep` are the physical P4 coefficient equations with their
one-step estimates. The equations in `hobsZero` and `hobsStep` identify the scalar
observable produced at a step, including its one-step estimate. `hfinalM` and `hfinalG`
are the first and second final source derivatives; `hfamilyLimit` and `hfamilyZero`
are the separately named family continuity inputs. -/
theorem c1Star_of_physical_step_targets (d N L M : ℕ) [NeZero L] (hN : 2 ≤ N)
    (hL : 3 ≤ L) (a γ₀ cStar cXi cPrime ρ₀ ρ₁ βStar : ℝ)
    (ha : 1 / (2 * (1 - ((L : ℝ) ^ 2)⁻¹)) < a ∧ a < 3 / 2)
    (hγ : 0 < γ₀ ∧ γ₀ ≤ 1 / 2)
    (hcStar : 0 < cStar) (hcXi : 0 < cXi) (hcPrime : 0 < cPrime)
    (hρ₀ : 0 < ρ₀ ∧ ρ₀ ≤ (d : ℝ) - 2) (hρ₁ : 0 < ρ₁ ∧ ρ₁ < 1)
    (J : ℝ → ℝ → ℕ)
    (ξraw : ℝ → ℝ → ℕ → Fin 3 → ℝ)
    (μraw : ℝ → ℕ → ℝ → (Fin d → ℤ) → ℝ)
    (A : ℝ → ℝ → ℕ → Matrix (Fin 3) (Fin 3) ℝ)
    (c f : ℝ → ℝ → ℕ → (Fin 3 → ℝ) → Fin 3 → ℝ)
    (Mstep : ℝ → ℝ → ℕ → (Fin d → ℤ) → ℝ)
    (em : ℝ → ℕ → ℝ → (Fin d → ℤ) → ℝ)
    (rtr rlg : ℝ → ℕ → ℝ → (Fin d → ℤ) → (Fin d → ℤ) → ℝ)
    (rtrLim rlgLim : ℝ → ℝ → (Fin d → ℤ) → (Fin d → ℤ) → ℝ)
    (rtrZero rlgZero : ℝ → (Fin d → ℤ) → (Fin d → ℤ) → ℝ)
    (hJpos : ∀ β, βStar ≤ β → ∀ ν ∈ Set.Ioc (0 : ℝ) 1, 1 ≤ J β ν)
    (hJtend : ∀ β, βStar ≤ β → Tendsto (J β) (𝓝[>] (0 : ℝ)) atTop)
    (hJbounds : ∀ β, βStar ≤ β → ∀ ν ∈ Set.Ioc (0 : ℝ) 1,
      1 / 2 ≤ (L : ℝ) ^ J β ν * Real.sqrt ν ∧
        (L : ℝ) ^ J β ν * Real.sqrt ν ≤ (L : ℝ) ^ 2)
    (hβpos : ∀ β, βStar ≤ β → 0 < β)
    (hcoeffZero : ∀ β, βStar ≤ β → ∀ k,
      (A β 0 k).mulVec (ξraw β 0 k) + c β 0 k (ξraw β 0 k) = f β 0 k (ξraw β 0 k) ∧
      ‖ξraw β 0 k‖ ≤ cXi / (4 * β) * Balaban.Flow.rate (L : ℝ) γ₀ ^ (k + 1))
    (hcoeffStep : ∀ β, βStar ≤ β → ∀ ν ∈ Set.Ioc (0 : ℝ) 1, ∀ k, k < J β ν →
      (A β ν k).mulVec (ξraw β ν k) + c β ν k (ξraw β ν k) =
        f β ν k (ξraw β ν k) ∧
      ‖ξraw β ν k‖ ≤ cXi / (4 * β) * Balaban.Flow.rate (L : ℝ) γ₀ ^ (k + 1))
    (hcoeffCont : ∀ β, βStar ≤ β → ∀ k,
      Tendsto (fun ν => ξraw β ν k) (𝓝[>] (0 : ℝ)) (𝓝 (ξraw β 0 k)))
    (hobsZero : ∀ β, βStar ≤ β → ∀ j, 1 ≤ j → ∀ x,
      Mstep β 0 j x = magJ L d (ξraw β 0) (fun i => μraw β i 0) β j x ∧
      |μraw β j 0 x| ≤
        cStar * β ^ (-(1 / 2 : ℝ) + ρ₁) * (L : ℝ) ^ (-((j : ℝ) * ρ₀)))
    (hobsStep : ∀ β, βStar ≤ β → ∀ j, 1 ≤ j → ∀ ν ∈ Set.Ioc (0 : ℝ) 1,
      j ≤ J β ν → ∀ x,
      Mstep β ν j x = magJ L d (ξraw β ν) (fun i => μraw β i ν) β j x ∧
      |μraw β j ν x| ≤
        cStar * β ^ (-(1 / 2 : ℝ) + ρ₁) * (L : ℝ) ^ (-((j : ℝ) * ρ₀)))
    (hobsCont : ∀ β, βStar ≤ β → ∀ j x,
      Tendsto (fun ν => μraw β j ν x) (𝓝[>] (0 : ℝ)) (𝓝 (μraw β j 0 x)))
    (hfinalM : ∀ β, βStar ≤ β → ∀ ν ∈ Set.Ioc (0 : ℝ) 1, ∀ x,
      ∃ ℓ₀ : ℕ, ∀ (ℓ : ℕ) [NeZero ℓ], ℓ₀ ≤ ℓ → M * L ^ (J β ν + 1) ∣ ℓ →
        blockM d N ℓ hN β ν =
          magJ L d (ξraw β ν) (fun j => μraw β j ν) β (J β ν) x + em β ℓ ν x ∧
        |em β ℓ ν x| ≤ cStar * (β ^ 2)⁻¹ *
          ((L : ℝ) ^ (2 * J β ν * (d - 2)))⁻¹)
    (hfinalG : ∀ β, βStar ≤ β → ∀ ν ∈ Set.Ioc (0 : ℝ) 1,
      ∀ x y : Fin d → ℤ, ∀ (ℓ : ℕ) [NeZero ℓ],
      M * L ^ (J β ν + 1) ∣ ℓ → (∀ i, 2 * |(x - y) i| < (ℓ : ℤ)) →
      blockGtr d N ℓ hN β ν (embedZ ℓ (x - y)) =
        magJ L d (ξraw β ν) (fun j => μraw β j ν) β (J β ν) x *
          magJ L d (ξraw β ν) (fun j => μraw β j ν) β (J β ν) y *
          mainTr d L a (ξraw β ν) β ν (J β ν) ℓ x y + rtr β ℓ ν x y ∧
      blockGlg d N ℓ hN β ν (embedZ ℓ (x - y)) = rlg β ℓ ν x y ∧
      |rtr β ℓ ν x y| ≤ cStar *
        ((1 + ‖x - y‖) ^ (-((d : ℝ) - 2 + ρ₀)) + ν ^ (((d : ℝ) - 2) / 2)) *
        Real.exp (-(cPrime * Real.sqrt ν * ‖x - y‖)) ∧
      |rlg β ℓ ν x y| ≤ cStar *
        ((1 + ‖x - y‖) ^ (-((d : ℝ) - 2 + ρ₀)) + ν ^ (((d : ℝ) - 2) / 2)) *
        Real.exp (-(cPrime * Real.sqrt ν * ‖x - y‖)))
    (hfamilyLimit : ∀ β, βStar ≤ β → ∀ ν ∈ Set.Ioc (0 : ℝ) 1, ∀ x y,
      LimAlong (M * L) (fun ℓ _ => rtr β ℓ ν x y) (rtrLim β ν x y) ∧
      LimAlong (M * L) (fun ℓ _ => rlg β ℓ ν x y) (rlgLim β ν x y))
    (hfamilyZero : ∀ β, βStar ≤ β → ∀ x y,
      Tendsto (fun ν => rtrLim β ν x y) (𝓝[>] (0 : ℝ)) (𝓝 (rtrZero β x y)) ∧
      Tendsto (fun ν => rlgLim β ν x y) (𝓝[>] (0 : ℝ)) (𝓝 (rlgZero β x y))) :
    Nonempty (C1Star d N L M hN) := by
  have hLreal : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  refine ⟨{
    a := a, γ₀ := γ₀, cStar := cStar, cXi := cXi, cPrime := cPrime,
    ρ₀ := ρ₀, ρ₁ := ρ₁, βStar := βStar,
    a_range := ha, γ₀_range := hγ, cStar_pos := hcStar,
    cXi_pos := hcXi, cPrime_pos := hcPrime,
    ρ₀_range := hρ₀, ρ₁_range := hρ₁, data := ?_ }⟩
  intro β hβ
  let ξ : ℝ → ℕ → Fin 3 → ℝ :=
    fun ν k => if k < J β ν then ξraw β ν k else if ν = 0 then ξraw β 0 k else 0
  let μ : ℕ → ℝ → (Fin d → ℤ) → ℝ :=
    fun j ν x => if j ≤ J β ν then μraw β j ν x else if ν = 0 then μraw β j 0 x else 0
  have hξprefix : ∀ ν, ∀ k, k < J β ν → ξ ν k = ξraw β ν k := by
    intro ν k hk
    simp only [ξ, hk, ↓reduceIte]
  have hμprefix : ∀ ν, ∀ j, j ≤ J β ν → ∀ x, μ j ν x = μraw β j ν x := by
    intro ν j hj x
    simp only [μ, hj, ↓reduceIte]
  have hμzero : ∀ j x, μ j 0 x = μraw β j 0 x := by
    intro j x
    simp only [μ]
    split_ifs <;> simp_all
  have hF1 : C1StarF1 L γ₀ cXi β ξ :=
    c1StarF1_of_stopped_steps L γ₀ cXi β hLreal hcXi.le (hβpos β hβ)
      (J β) (ξraw β) (hJtend β hβ)
      (fun k => (hcoeffZero β hβ k).2)
      (fun ν hν k hk => (hcoeffStep β hβ ν hν k hk).2)
      (hcoeffCont β hβ)
  have hμbc := stopped_mu_bound_cont L cStar ρ₀ ρ₁ β hLreal hcStar.le
    (hβpos β hβ) (J β) (μraw β) (hJtend β hβ)
    (fun j hj x => (hobsZero β hβ j hj x).2)
    (fun j hj ν hν hjJ x => (hobsStep β hβ j hj ν hν hjJ x).2)
    (hobsCont β hβ)
  have hμcont : ∀ j x, Tendsto (fun ν => μ j ν x) (𝓝[>] (0 : ℝ)) (𝓝 (μ j 0 x)) := by
    intro j x
    rw [hμzero j x]
    exact hμbc.2 j x
  refine ⟨J β, ξ, μ, rtr β, rlg β, em β, rtrLim β, rlgLim β,
    rtrZero β, rlgZero β, hJpos β hβ, hJtend β hβ, hJbounds β hβ,
    hF1, ?_, ?_⟩
  · refine ⟨hμbc.1, hμcont, ?_⟩
    intro ν hν x
    obtain ⟨ℓ₀, hlast⟩ := hfinalM β hβ ν hν x
    refine ⟨ℓ₀, ?_⟩
    intro ℓ _ hℓ hdvd
    obtain ⟨heq, hbd⟩ := hlast ℓ hℓ hdvd
    have hmag := magJ_eq_of_prefix L d β (J β ν) (ξ ν) (ξraw β ν)
      (fun j => μ j ν) (fun j => μraw β j ν)
      (hξprefix ν) (fun j _ hj x => hμprefix ν j hj x) x
    rw [hmag]
    exact ⟨heq, hbd⟩
  · refine ⟨?_, hfamilyLimit β hβ, hfamilyZero β hβ⟩
    intro ν hν x y ℓ _ hdvd hwrap
    obtain ⟨htr, hlg, hrtr, hrlg⟩ := hfinalG β hβ ν hν x y ℓ hdvd hwrap
    have hmagx := magJ_eq_of_prefix L d β (J β ν) (ξ ν) (ξraw β ν)
      (fun j => μ j ν) (fun j => μraw β j ν)
      (hξprefix ν) (fun j _ hj z => hμprefix ν j hj z) x
    have hmagy := magJ_eq_of_prefix L d β (J β ν) (ξ ν) (ξraw β ν)
      (fun j => μ j ν) (fun j => μraw β j ν)
      (hξprefix ν) (fun j _ hj z => hμprefix ν j hj z) y
    have hmain := mainTr_eq_of_prefix d L a β ν (J β ν) ℓ
      (ξ ν) (ξraw β ν) (hξprefix ν) x y
    rw [hmagx, hmagy, hmain]
    exact ⟨htr, hlg, hrtr, hrlg⟩

end Balaban.Correlations
