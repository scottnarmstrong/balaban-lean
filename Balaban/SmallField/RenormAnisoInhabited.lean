/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.RenormAnisoCtx

/-!
# Inhabitation of the anisotropic I-6 hypotheses (hard rule 10)

* `nonempty_premisesTermAniso`: the family `constTerms a` of one polymer `{0}` at distance `0`
  with a constant term `a`, `‖a‖ ≤ E₀`, satisfies `PremisesTermAniso` for every `i₀ ≠ i₁`,
  `ν, r, κ`, every data domain, `A ≥ 0` and `K₀ ≥ 1`;
* `nonempty_dataHypAniso`: the constant configuration `ψ ≡ e_{i₀}`, `b = ν e_{i₀}` satisfies
  `DataHypAniso` on the data domain `univ` for all `σ, ε, K₂ ≥ 0`;
* `nonempty_ctxAniso`: the two together with the trivial frame satisfy `CtxAniso`, hence the whole
  hypothesis set of `termwise_irrelevant_aniso`, for all admissible numerical parameters.
-/

@[expose] public section

open Metric Set

namespace Balaban.SmallField

variable {d N : ℕ}

/-- The family of one polymer `{0}` at distance `0` with the constant term `a`. -/
def constTerms (d N : ℕ) (a : ℂ) : TermFamily d N where
  polys := {{0}}
  dist := fun _ => 0
  term := fun _ _ => a

theorem nonempty_premisesTermAniso (i₀ i₁ : Fin N) (h : i₀ ≠ i₁) (ν r E₀ κ A K₀ : ℝ) (a : ℂ)
    (ha : ‖a‖ ≤ E₀) (hA : 0 ≤ A) (hK₀ : 1 ≤ K₀) (Dom : Set ((Site d → Spin N) × Spin N)) :
    Nonempty (PremisesTermAniso (constTerms d N a) i₀ i₁ ν r E₀ κ A K₀ Dom) := by
  have hpol : ∀ X ∈ (constTerms d N a).polys, X = {0} := fun X hX => hX
  have hbd : ‖a‖ ≤ E₀ * Real.exp (-κ * 0) := by simpa using ha
  have hfin : Finite ↥(constTerms d N a).polys := Set.finite_singleton _ |>.to_subtype
  refine ⟨⟨h, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro X hX; rw [hpol X hX]; simp
  · intro X _; exact le_rfl
  · intro X hX x hx
    rw [hpol X hX, Finset.mem_singleton] at hx
    subst hx
    simp only [Pi.zero_apply, abs_zero, Finset.sum_const_zero, Int.cast_zero]
    show (0 : ℝ) ≤ A * (1 + 0)
    linarith
  · exact Summable.of_finite
  · have e : (∑' X : ↥(constTerms d N a).polys, wt κ X.1 ((constTerms d N a).dist X.1)) =
        wt κ ({0} : Finset (Site d)) 0 :=
      tsum_singleton (({0} : Finset (Site d))) (fun X => wt κ X 0)
    rw [e]
    simp [wt, hK₀]
  · intro X _; exact analyticOnNhd_const
  · intro X _ c _; exact hbd
  · intro X _ p _; exact hbd
  · intro X _ c _ R _ _ _; rfl

theorem dot_single_self (i₀ : Fin N) : dot (Pi.single i₀ (1 : ℂ) : Spin N) (Pi.single i₀ 1) = 1 := by
  rw [dot_single_left]; simp

theorem uInv_const_single (i₀ : Fin N) :
    uInv (fun _ : Site d => (Pi.single i₀ (1 : ℂ) : Spin N)) = 1 := by
  unfold uInv
  rw [dot_single_self]
  exact sqrtC_eq (by ring) (by simp)

theorem vInv_const_single (i₀ : Fin N) (ν : ℝ) :
    vInv (fun _ : Site d => (Pi.single i₀ (1 : ℂ) : Spin N)) ((ν : ℂ) • Pi.single i₀ 1) = ν := by
  unfold vInv
  rw [uInv_const_single, dot_smul_right, dot_single_self]
  simp

theorem nonempty_dataHypAniso (i₀ : Fin N) (ν σ ε K₂ : ℝ) (hσ : 0 ≤ σ) (hε : 0 ≤ ε)
    (hK₂ : 0 ≤ K₂) :
    Nonempty (DataHypAniso (univ : Set ((Site d → Spin N) × Spin N)) ν σ ε K₂
      (fun _ => Pi.single i₀ 1) ((ν : ℂ) • Pi.single i₀ 1)) := by
  refine ⟨⟨⟨hK₂, ?_, ?_, ?_, ?_, ?_, mem_univ _, mem_univ _⟩, ?_⟩⟩
  · intro x; rw [dot_single_self]; simp; positivity
  · rw [Pi.norm_single, norm_one]; norm_num
  · intro x μ; simp; positivity
  · simp; positivity
  · intro x μ μ'; simpa using hK₂
  · rw [vInv_const_single]; simp; positivity

theorem frame_const_single (i₀ : Fin N) (σ ε : ℝ) (hσε : 0 ≤ σ ^ 2 * ε) :
    Frame i₀ σ ε (fun _ : Site d => (Pi.single i₀ (1 : ℂ) : Spin N)) 1 1 :=
  ⟨isOrth_one, entryBd_one, by rw [dot_single_self]; ring, by simpa using hσε,
    by rw [Matrix.one_mulVec, one_smul]⟩

/-- The whole hypothesis set of the anisotropic termwise theorem is satisfiable for every
admissible choice of the numerical parameters. -/
theorem nonempty_ctxAniso (i₀ i₁ : Fin N) (h : i₀ ≠ i₁) (ν r E₀ κ A K₀ Λ σ ε K₂ : ℝ) (a : ℂ)
    (ha : ‖a‖ ≤ E₀) (hA : 0 ≤ A) (hK₀ : 1 ≤ K₀) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hε : 0 < ε)
    (hεΛ : ε ≤ Λ * r) (hr : 0 < r) (hr1 : r ≤ 1) (hν : 0 ≤ ν) (hνσ : ν ≤ σ ^ 2)
    (hτ : σ ^ 2 * ε ≤ 1 / 4) (hK₂ : 0 ≤ K₂) :
    Nonempty (CtxAniso (constTerms d N a) i₀ i₁ ν r E₀ κ A K₀ Λ univ
      (fun _ => Pi.single i₀ 1) ((ν : ℂ) • Pi.single i₀ 1) σ ε K₂ 1 1) := by
  obtain ⟨hP⟩ := nonempty_premisesTermAniso (d := d) i₀ i₁ h ν r E₀ κ A K₀ a ha hA hK₀ univ
  obtain ⟨hD⟩ := nonempty_dataHypAniso (d := d) (N := N) i₀ ν σ ε K₂ hσ.le hε.le hK₂
  have hE₀ : 0 ≤ E₀ := le_trans (norm_nonneg _) ha
  exact ⟨⟨hP, hD, frame_const_single i₀ σ ε (by positivity), hσ, hσ1, hε, hεΛ, hr, hr1, hν, hνσ,
    hE₀, hA, hτ⟩⟩

end Balaban.SmallField
