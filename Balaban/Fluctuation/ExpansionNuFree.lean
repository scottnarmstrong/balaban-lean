module

public import Balaban.Fluctuation.ExpansionQuad
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Lemma 2.3 (c): the `ν`-free convention

The backgrounds `φ^0_{k+1}`, `φ^0_k(ψ)` are those of mass `0` while the action keeps the mass
term `νk` (P5 (1.9)): `J_k = J⁰_k + (νk/2) ‖φ^0_k(ψ) - h‖²` (`actionC_mass_split`).  The expansion
(2.4) holds for the `ν`-free objects, plus the variation `massVar` of the mass term:
`V_ν(ψ') = νk ⟨φ', φ^0_{k+1} - h⟩ + (νk/2) ‖φ'‖²` (design choice D-FL.1 of FLUCTUATION §2.3: the
covariance is that of mass `0`, the whole `ν`-variation sits in `V_ν`).
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban.Multiscale Balaban.Background Finset Matrix

section NuFree

variable {d L N₀ K : ℕ} [NeZero N₀] [NeZero L] {ϱ ϱ' : ℝ} {N : ℕ}
variable {G : GeneratingSet d L N₀ K ϱ} {G' : GeneratingSet d L N₀ K ϱ'} {a₁ : ℝ} {n : ℕ}

theorem IsLevel.sum_ΩC (hG : IsLevel G n) (F : Torus d (N₀ * L ^ K) → ℂ) :
    ∑ x : G.Ω 1, F x = ∑ x, F x := by
  rw [Finset.sum_coe_sort (G.Ω 1) F, hG.Ω_one]

/-- The mass term of `actionC`: `A_ν = A_0 + (ν/2) ∑ (φ - h̃)·(φ - h̃)`. -/
theorem actionC_mass_split (a : ℕ → ℝ) (ν : ℝ) (D : BgData G N) (φ : G.Ω 1 × Fin N → ℂ) :
    actionC G a ν D φ = actionC G a 0 D φ +
      (ν : ℂ) / 2 * ∑ x : G.Ω 1, ∑ i, (φ (x, i) - D.h x i) * (φ (x, i) - D.h x i) := by
  unfold actionC
  push_cast
  ring

theorem sum_sq_sub_torus (hG : IsLevel G n) (φ : G.Ω 1 × Fin N → ℂ)
    (hh : Torus d (N₀ * L ^ K) → Fin N → ℂ) :
    ∑ x : G.Ω 1, ∑ i, (φ (x, i) - hh x i) * (φ (x, i) - hh x i) =
      ∑ x, ∑ i, (svec G φ x i - hh x i) * (svec G φ x i - hh x i) := by
  rw [← hG.sum_ΩC (fun x => ∑ i, (svec G φ x i - hh x i) * (svec G φ x i - hh x i))]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ => ?_
  rw [svec_of_mem]

/-- The mass variation `V_ν(ψ') = ν⟨φ', φ^0_{k+1} - h⟩ + (ν/2)‖φ'‖²` of Lemma 2.3 (c). -/
noncomputable def massVar (νk : ℝ) (h : Precedes G G') (φ₁ : G'.Ω 1 × Fin N → ℂ)
    (hh : Torus d (N₀ * L ^ K) → Fin N → ℂ) (φ' : G.Ω 1 × Fin N → ℂ) : ℂ :=
  (νk : ℂ) * ∑ x : G.Ω 1, ∑ i, φ' (x, i) * (h.restrictφ φ₁ (x, i) - hh x i) +
    (νk : ℂ) / 2 * ∑ x : G.Ω 1, ∑ i, φ' (x, i) * φ' (x, i)

/-- **Lemma 2.3 (c): the `ν`-free convention.**  The backgrounds `φ^0_{k+1}`, `φ^0_k(ψ)` are those
of mass `0` (the `bgFieldC` at `ν = 0`), while the action keeps the mass term `νk`.  With
`A*_{k+1}(θ, φ) = A^η_{k+1}(θ, φ)` (the mass term evaluated at the `ν`-free background):
`J_k(θ, ψ) = A*_{k+1}(θ, φ^0_{k+1}) + ½ a₁ L^{-2(n+1)} ‖Qψ'‖² + ½⟨ψ', Δ^{(k)} ψ'⟩ + V^{(k)}(ψ')
 + V_ν(ψ')`, with `Δ^{(k)}`, `V^{(k)}` those of mass `0`. -/
theorem expansion_nuFree (νk : ℝ) (ha₁ : 0 < a₁) (hG : IsLevel G n) (hG' : IsLevel G' (n + 1))
    (hp : n + 1 ≤ K) (H : BgHyp d L K ϱ (compWeight L a₁) 0)
    (H' : BgHyp d L K ϱ' (compWeight L a₁) 0) (D' : BgData G' N)
    (hD' : InUnionDomainC G' (bgC0 d L N) (thm73C2 d L N) 0 D') (D : BgData G N)
    (hh : ∀ x i, D.h x i = D'.h x i)
    (hD : InUnionDomainC G (bgC0 d L N) (bgC1 d L N) 0 D) :
    couplingC G' a₁ (n + 1) D'.Ψ D.Ψ +
        actionC G (compWeight L a₁) νk D (bgFieldC G (compWeight L a₁) 0 (bgC0 d L N) D) =
      actionC G' (compWeight L a₁) νk D' (bgFieldC G' (compWeight L a₁) 0 (bgC0 d L N) D') +
        couplingC G' a₁ (n + 1) (fun _ _ => 0) (compTangent hG hG' hp (compWeight L a₁)
          (bgFieldC G' (compWeight L a₁) 0 (bgC0 d L N) D') D' D) +
        (1 / 2) * deltaForm (hG.precedes hG' hp) (compWeight L a₁) 0
          (bgMultC G' (compWeight L a₁) 0 (bgC0 d L N) D')
          (bgFieldC G' (compWeight L a₁) 0 (bgC0 d L N) D')
          (compTangent hG hG' hp (compWeight L a₁)
            (bgFieldC G' (compWeight L a₁) 0 (bgC0 d L N) D') D' D) +
        interactionV (hG.precedes hG' hp) (compWeight L a₁) 0
          (bgMultC G' (compWeight L a₁) 0 (bgC0 d L N) D')
          (bgFieldC G' (compWeight L a₁) 0 (bgC0 d L N) D')
          (compTangent hG hG' hp (compWeight L a₁)
            (bgFieldC G' (compWeight L a₁) 0 (bgC0 d L N) D') D' D)
          (bgFieldC G (compWeight L a₁) 0 (bgC0 d L N) D -
            (hG.precedes hG' hp).restrictφ (bgFieldC G' (compWeight L a₁) 0 (bgC0 d L N) D')) +
        massVar νk (hG.precedes hG' hp) (bgFieldC G' (compWeight L a₁) 0 (bgC0 d L N) D') D.h
          (bgFieldC G (compWeight L a₁) 0 (bgC0 d L N) D -
            (hG.precedes hG' hp).restrictφ (bgFieldC G' (compWeight L a₁) 0 (bgC0 d L N) D')) := by
  have hb := expansion_quadratic (ν := 0) ha₁ hG hG' hp H H' D' hD' D hh hD
  rw [actionC_mass_split _ νk D, actionC_mass_split _ νk D']
  set φD := bgFieldC G (compWeight L a₁) 0 (bgC0 d L N) D with hφD
  set φ₁ := bgFieldC G' (compWeight L a₁) 0 (bgC0 d L N) D' with hφ₁
  set h := hG.precedes hG' hp with hh'
  have hsplit : ∑ x : G.Ω 1, ∑ i, (φD (x, i) - D.h x i) * (φD (x, i) - D.h x i) =
      ∑ x : G'.Ω 1, ∑ i, (φ₁ (x, i) - D'.h x i) * (φ₁ (x, i) - D'.h x i) +
        2 * ∑ x : G.Ω 1, ∑ i, (φD (x, i) - h.restrictφ φ₁ (x, i)) *
          (h.restrictφ φ₁ (x, i) - D.h x i) +
        ∑ x : G.Ω 1, ∑ i, (φD (x, i) - h.restrictφ φ₁ (x, i)) *
          (φD (x, i) - h.restrictφ φ₁ (x, i)) := by
    have e : ∑ x : G'.Ω 1, ∑ i, (φ₁ (x, i) - D'.h x i) * (φ₁ (x, i) - D'.h x i) =
        ∑ x : G.Ω 1, ∑ i, (h.restrictφ φ₁ (x, i) - D.h x i) * (h.restrictφ φ₁ (x, i) - D.h x i) := by
      rw [sum_sq_sub_torus hG', sum_sq_sub_torus hG]
      have ef : svec G (h.restrictφ φ₁) = svec G' φ₁ :=
        funext fun y => funext fun i => svec_restrict hG hG' hp φ₁ y i
      rw [ef]
      simp only [hh]
    rw [e, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  unfold massVar
  simp only [Pi.sub_apply]
  linear_combination hb + ((νk : ℂ) / 2) * hsplit

end NuFree

end Balaban.Fluctuation
