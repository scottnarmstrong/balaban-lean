/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Regrouping Mayer weights by a key

Let terms `t ∈ U` carry weights `f_t` and keys `key t`, and group them into
`F_x = ∏_{t ∈ U, key t = x} (1 + f_t) - 1`. If every product of weights is integrable and
`|∫ ∏_{t ∈ C} f_t| ≤ ∏_{t ∈ C} b_t` for every `C ⊆ U`, then every product of grouped weights is
integrable and `|∫ ∏_{x ∈ 𝒞} F_x| ≤ ∏_{x ∈ 𝒞} (∏_{t, key t = x} (1 + b_t) - 1)`
(`regroup_prod_bound`). Expanding `F_x = ∑_{∅ ≠ A ⊆ T_x} ∏_{t∈A} f_t`, a product over `𝒞` is a sum
of products of weights over disjoint unions.
-/

@[expose] public section

open MeasureTheory Finset

namespace Balaban.Polymer

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {T X : Type*} [DecidableEq T]
  [DecidableEq X] (key : T → X) (U : Finset T)

/-- The terms of the key `x`. -/
def keyTerms (x : X) : Finset T := U.filter fun t => key t = x

/-- The grouped weight of the key `x`. -/
def keyWeight (f : T → Ω → ℂ) (x : X) (ω : Ω) : ℂ :=
  ∏ t ∈ keyTerms key U x, (1 + f t ω) - 1

omit [MeasurableSpace Ω] in
theorem keyWeight_eq_sum (f : T → Ω → ℂ) (x : X) (ω : Ω) :
    keyWeight key U f x ω = ∑ A ∈ (keyTerms key U x).powerset.erase ∅, ∏ t ∈ A, f t ω := by
  unfold keyWeight
  rw [Finset.prod_one_add, Finset.sum_erase_eq_sub (Finset.empty_mem_powerset _),
    Finset.prod_empty]

omit [MeasurableSpace Ω] in
theorem prod_one_add_sub_eq_sum (b : T → ℝ) (x : X) :
    ∏ t ∈ keyTerms key U x, (1 + b t) - 1 =
      ∑ A ∈ (keyTerms key U x).powerset.erase ∅, ∏ t ∈ A, b t := by
  rw [Finset.prod_one_add, Finset.sum_erase_eq_sub (Finset.empty_mem_powerset _),
    Finset.prod_empty]

variable {key U}

/-- **The product bound of the grouped weights** (strengthened form, with an extra product of
weights whose keys lie outside the family). -/
theorem regroup_prod_bound_aux (f : T → Ω → ℂ) (b : T → ℝ)
    (hint : ∀ C ⊆ U, Integrable (fun ω => ∏ t ∈ C, f t ω) μ)
    (hprod : ∀ C ⊆ U, ‖∫ ω, ∏ t ∈ C, f t ω ∂μ‖ ≤ ∏ t ∈ C, b t) (𝒞 : Finset X) :
    ∀ C₀ ⊆ U, (∀ t ∈ C₀, key t ∉ 𝒞) →
      Integrable (fun ω => (∏ t ∈ C₀, f t ω) * ∏ x ∈ 𝒞, keyWeight key U f x ω) μ ∧
      ‖∫ ω, (∏ t ∈ C₀, f t ω) * ∏ x ∈ 𝒞, keyWeight key U f x ω ∂μ‖ ≤
        (∏ t ∈ C₀, b t) * ∏ x ∈ 𝒞, (∏ t ∈ keyTerms key U x, (1 + b t) - 1) := by
  induction 𝒞 using Finset.induction_on with
  | empty =>
    intro C₀ hC₀ _
    simp only [Finset.prod_empty, mul_one]
    exact ⟨hint C₀ hC₀, hprod C₀ hC₀⟩
  | insert x 𝒞' hx ih =>
    intro C₀ hC₀ hkey
    have hsplit : ∀ ω, (∏ t ∈ C₀, f t ω) * ∏ y ∈ insert x 𝒞', keyWeight key U f y ω =
        ∑ A ∈ (keyTerms key U x).powerset.erase ∅,
          (∏ t ∈ C₀ ∪ A, f t ω) * ∏ y ∈ 𝒞', keyWeight key U f y ω := by
      intro ω
      rw [Finset.prod_insert hx, keyWeight_eq_sum, Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun A hA => ?_
      have hdisj : Disjoint C₀ A := by
        rw [Finset.disjoint_left]
        intro t ht htA
        have hA' := Finset.mem_powerset.1 (Finset.mem_of_mem_erase hA) htA
        have : key t = x := (Finset.mem_filter.1 hA').2
        exact hkey t ht (this ▸ Finset.mem_insert_self _ _)
      rw [Finset.prod_union hdisj]
      ring
    have hsub : ∀ A ∈ (keyTerms key U x).powerset.erase ∅, C₀ ∪ A ⊆ U ∧
        ∀ t ∈ C₀ ∪ A, key t ∉ 𝒞' := by
      intro A hA
      have hAT := Finset.mem_powerset.1 (Finset.mem_of_mem_erase hA)
      refine ⟨Finset.union_subset hC₀ (hAT.trans (Finset.filter_subset _ _)), fun t ht => ?_⟩
      rcases Finset.mem_union.1 ht with ht | ht
      · exact fun h => hkey t ht (Finset.mem_insert_of_mem h)
      · have : key t = x := (Finset.mem_filter.1 (hAT ht)).2
        rw [this]; exact hx
    refine ⟨?_, ?_⟩
    · simp_rw [hsplit]
      exact integrable_finsetSum _ fun A hA => (ih (C₀ ∪ A) (hsub A hA).1 (hsub A hA).2).1
    · simp_rw [hsplit]
      rw [integral_finsetSum _ fun A hA => (ih (C₀ ∪ A) (hsub A hA).1 (hsub A hA).2).1]
      refine (norm_sum_le _ _).trans ?_
      calc ∑ A ∈ (keyTerms key U x).powerset.erase ∅,
            ‖∫ ω, (∏ t ∈ C₀ ∪ A, f t ω) * ∏ y ∈ 𝒞', keyWeight key U f y ω ∂μ‖
          ≤ ∑ A ∈ (keyTerms key U x).powerset.erase ∅,
            (∏ t ∈ C₀ ∪ A, b t) * ∏ y ∈ 𝒞', (∏ t ∈ keyTerms key U y, (1 + b t) - 1) :=
            Finset.sum_le_sum fun A hA => (ih (C₀ ∪ A) (hsub A hA).1 (hsub A hA).2).2
        _ = (∏ t ∈ C₀, b t) * ∏ y ∈ insert x 𝒞', (∏ t ∈ keyTerms key U y, (1 + b t) - 1) := by
            rw [Finset.prod_insert hx, prod_one_add_sub_eq_sum key U b x, Finset.sum_mul,
              Finset.mul_sum]
            refine Finset.sum_congr rfl fun A hA => ?_
            have hdisj : Disjoint C₀ A := by
              rw [Finset.disjoint_left]
              intro t ht htA
              have hA' := Finset.mem_powerset.1 (Finset.mem_of_mem_erase hA) htA
              have : key t = x := (Finset.mem_filter.1 hA').2
              exact hkey t ht (this ▸ Finset.mem_insert_self _ _)
            rw [Finset.prod_union hdisj]
            ring

/-- **The product bound of the grouped weights.** -/
theorem regroup_prod_bound (f : T → Ω → ℂ) (b : T → ℝ)
    (hint : ∀ C ⊆ U, Integrable (fun ω => ∏ t ∈ C, f t ω) μ)
    (hprod : ∀ C ⊆ U, ‖∫ ω, ∏ t ∈ C, f t ω ∂μ‖ ≤ ∏ t ∈ C, b t) (𝒞 : Finset X) :
    Integrable (fun ω => ∏ x ∈ 𝒞, keyWeight key U f x ω) μ ∧
    ‖∫ ω, ∏ x ∈ 𝒞, keyWeight key U f x ω ∂μ‖ ≤
      ∏ x ∈ 𝒞, (∏ t ∈ keyTerms key U x, (1 + b t) - 1) := by
  have h := regroup_prod_bound_aux μ (key := key) (U := U) f b hint hprod 𝒞 ∅
    (Finset.empty_subset _)
    (fun t ht => absurd ht (Finset.notMem_empty t))
  simpa using h

end

end Balaban.Polymer
