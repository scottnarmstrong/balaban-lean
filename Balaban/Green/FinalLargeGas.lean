/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.FinalTailGas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The normalized singleton gas of the last integral

The two physical identifications are explicit premises: integration of the large variables
factorizes into fixed singleton weights, and the new boundary difference localizes into fixed
coefficients. The Gaussian and variational estimates do not imply either identification.
-/

@[expose] public section

noncomputable section

open scoped Classical
open Finset

namespace Balaban.Green

open Balaban.Polymer

variable {d m : ℕ} [NeZero m] {Yt : Type*} [Fintype Yt]

omit [NeZero m] in
/-- Every family of singleton heavy supports is admissible in `gasXi`. -/
theorem singleton_family_admissible (Γ : Finset (Torus d m)) :
    ∀ z ∈ Γ, ∀ z' ∈ Γ, z ≠ z' →
      Disjoint ({z} : Finset (Torus d m)) {z'} := by
  intro z _ z' _ hne
  exact Finset.disjoint_left.mpr (fun b hb hb' => by
    simp only [Finset.mem_singleton] at hb hb'
    exact hne (hb.symm.trans hb'))

omit [NeZero m] in
/-- The charged union of singleton cores is the selected bad set. -/
theorem biUnion_singleton (Γ : Finset (Torus d m)) :
    Γ.biUnion (fun z => ({z} : Finset (Torus d m))) = Γ := by
  ext z
  simp

/-- With singleton heavy labels, the gas partition function is a sum over all bad sets. -/
theorem singleton_gasXi_eq_sum (cy : Yt → Finset (Torus d m))
    (g : Yt → ℂ) (τ : Torus d m → ℂ) :
    gasXi cy (fun z => {z}) (fun z => {z}) g τ =
      ∑ Z : Finset (Torus d m),
        (∏ z ∈ Z, τ z) * Complex.exp
          (∑ y ∈ Finset.univ.filter (fun y => ¬ Disjoint (cy y) Z), g y) := by
  classical
  simp [gasXi]

/-- Integrating the large variables first and localizing every boundary difference as a fixed
coefficient identifies the last integral with the normalized singleton gas. `hOperator` is the
heavy-operator factorization; `hBoundary` is the fixed-coefficient identity for the new `B″`.
Neither is inferred from an absolute tail bound. -/
theorem final_large_integral_eq_gasXi_of_factorization
    (cy : Yt → Finset (Torus d m)) (g : Yt → ℂ) (τ : Torus d m → ℂ)
    (cell : Finset (Torus d m) → ℂ) (Q : ℂ)
    (boundary : Finset (Torus d m) → ℂ)
    (hOperator : ∀ Z, cell Z = Q * (∏ z ∈ Z, τ z) * Complex.exp (boundary Z))
    (hBoundary : ∀ Z, boundary Z =
      ∑ y ∈ Finset.univ.filter (fun y => ¬ Disjoint (cy y) Z), g y) :
    (∑ Z : Finset (Torus d m), cell Z) =
      Q * gasXi cy (fun z => {z}) (fun z => {z}) g τ := by
  calc
    (∑ Z : Finset (Torus d m), cell Z) =
        ∑ Z : Finset (Torus d m),
          Q * ((∏ z ∈ Z, τ z) * Complex.exp
            (∑ y ∈ Finset.univ.filter (fun y => ¬ Disjoint (cy y) Z), g y)) := by
      apply Finset.sum_congr rfl
      intro Z _
      rw [hOperator Z, hBoundary Z]
      ring
    _ = Q * ∑ Z : Finset (Torus d m),
          (∏ z ∈ Z, τ z) * Complex.exp
            (∑ y ∈ Finset.univ.filter (fun y => ¬ Disjoint (cy y) Z), g y) := by
      rw [Finset.mul_sum]
    _ = Q * gasXi cy (fun z => {z}) (fun z => {z}) g τ := by
      rw [singleton_gasXi_eq_sum]

/-- The actual last integral has the polymer partition-function representation once the two
physical identification premises are supplied. -/
theorem final_large_integral_eq_polymerXi_of_factorization
    (cy : Yt → Finset (Torus d m)) (g : Yt → ℂ) (τ : Torus d m → ℂ)
    (cell : Finset (Torus d m) → ℂ) (Q : ℂ)
    (boundary : Finset (Torus d m) → ℂ)
    (hOperator : ∀ Z, cell Z = Q * (∏ z ∈ Z, τ z) * Complex.exp (boundary Z))
    (hBoundary : ∀ Z, boundary Z =
      ∑ y ∈ Finset.univ.filter (fun y => ¬ Disjoint (cy y) Z), g y) :
    (∑ Z : Finset (Torus d m), cell Z) =
      Q * Xi (shareBlock (Subtype.val : NePoly (Torus d m) → Finset (Torus d m)))
        (gasK cy (fun z => {z}) (fun z => {z}) g τ) := by
  rw [final_large_integral_eq_gasXi_of_factorization cy g τ cell Q boundary hOperator hBoundary]
  congr 1
  exact gas_eq (cy := cy) (zs := fun z => {z}) (cr := fun z => {z})
    (β := g) (τ := τ) (fun z => by simp) (fun z => by simp)

/-- The singleton heavy labels have counting constant one. -/
private theorem singleton_heavy_count (b : Torus d m) (v : ℕ) :
    ((Finset.univ.filter (fun z : Torus d m => b ∈ ({z} : Finset (Torus d m)) ∧
      ({z} : Finset (Torus d m)).card = v)).card : ℝ) ≤ (1 : ℝ) ^ v := by
  have hc : (Finset.univ.filter (fun z : Torus d m =>
      b ∈ ({z} : Finset (Torus d m)) ∧ ({z} : Finset (Torus d m)).card = v)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro z hz z' hz'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton] at hz hz'
    exact hz.1.symm.trans hz'.1
  have hcr : ((Finset.univ.filter (fun z : Torus d m =>
      b ∈ ({z} : Finset (Torus d m)) ∧ ({z} : Finset (Torus d m)).card = v)).card : ℝ) ≤ 1 := by
    exact_mod_cast hc
  simpa using hcr

/-- The general landed gas bound with one heavy label per bad block. The coupling bound `hB`
is the output required from a fixed localization theorem for `B″`; `hτ` is the output of a
normalized heavy-operator bound. -/
theorem final_large_gas_activity_bound_of_fixed_boundary
    (cy : Yt → Finset (Torus d m))
    (g : Yt → ℂ) (τ : Torus d m → ℂ)
    {B0 κ' κ'' P H : ℝ}
    (hB0 : 0 ≤ B0) (hκ' : 0 ≤ κ') (hκκ : κ' ≤ κ'') (hP : 0 ≤ P)
    (hent : ∀ b : Torus d m,
      ∑ y ∈ Finset.univ.filter (fun y => b ∈ cy y),
        Real.exp (-(κ'' - κ') * ((cy y).card : ℝ)) ≤ 1)
    (hB : ∀ y, ‖g y‖ ≤ B0 * Real.exp (-κ'' * ((cy y).card : ℝ)))
    (hτ : ∀ z, ‖τ z‖ ≤ Real.exp (-P - H))
    (hH : B0 * Real.exp B0 + κ' + 4 ≤ H)
    (X : NePoly (Torus d m)) :
    ‖gasK cy (fun z => {z}) (fun z => {z}) g τ X‖ ≤
      3 * Real.exp (-P) * Real.exp (-(κ' - 2) * (X.1.card : ℝ)) := by
  have hmain : ‖gasK cy (fun z => {z}) (fun z => {z}) g τ X‖ ≤
      3 * 1 * Real.exp (-P) * Real.exp (-(κ' - 2) * (X.1.card : ℝ)) := by
    refine Polymer.gas_activity_bound (d := fun S : Finset (Torus d m) => (S.card : ℝ))
      (zs := fun z : Torus d m => {z}) (cr := fun z : Torus d m => {z})
      (cy := cy) (β := g) (τ := τ) (c := 0) (c1 := 1) (c2 := 1)
      (B0 := B0) (κ' := κ') (κ'' := κ'') (p := P) (h := H)
      hB0 hκ' hκκ le_rfl zero_le_one hP (fun _ => Nat.cast_nonneg _)
      (fun z => by simp) (fun z => by simp) hB ?_ ?_ ?_
      (K0' := 1) (K0'' := 1) zero_le_one ?_ le_rfl ?_ ?_ X ?_
    · intro z
      simpa using hτ z
    · intro z
      simp
    · intro C _ _
      simpa [Polymer.gasCs] using
        card_unionCs_le (V := Torus d m) (Polymer.gasCs cy (fun z : Torus d m => {z})) C
    · intro b
      exact le_of_eq_of_le (Finset.sum_congr (by ext; simp) (fun _ _ => rfl)) (hent b)
    · intro b v
      convert singleton_heavy_count (d := d) (m := m) b v using 1
      congr 1
      congr 1
      ext z
      simp
    · have := hH
      norm_num at this ⊢
      linarith
    · simp
  simpa only [one_mul, mul_one] using hmain

end Balaban.Green
