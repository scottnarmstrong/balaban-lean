/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.FinalLargeBounds
public import Balaban.Green.FinalLargeEntropy

/-!
# The conditional last-integral singleton gas theorem

The heavy-operator factorization and fixed `B″` identity are named physical inputs. A
modular-size bound on the localized coefficients supplies `hB`; a normalized heavy bound
supplies `hτ`. The conclusion is an exact polymer representation and its activity estimate.
-/

@[expose] public section

noncomputable section

open scoped Classical
open Finset Balaban.Polymer

namespace Balaban.Green

/-- Conditional closure of the corrected finite-volume last-integral gas. The first two
premises are the physical identifications still needed from P7 (4.11); the size and coefficient
bounds supply the landed gas theorem's `hB`. `hHeavy` is its `hτ`, for instance furnished by
`normalized_one_block_integral_bound_of_log_budget` after the operator is identified with a
one-block Gaussian integral. -/
theorem final_large_integral_polymer_bound_of_fixed_localization
    {d m : ℕ} [NeZero m] {Yt : Type*} [Fintype Yt]
    (cy : Yt → Finset (Torus d m)) (g : Yt → ℂ) (τ : Torus d m → ℂ)
    (cell : Finset (Torus d m) → ℂ) (Q : ℂ)
    (boundary : Finset (Torus d m) → ℂ)
    (hOperator : ∀ Z, cell Z = Q * (∏ z ∈ Z, τ z) * Complex.exp (boundary Z))
    (hBoundary : ∀ Z, boundary Z =
      ∑ y ∈ Finset.univ.filter (fun y => ¬ Disjoint (cy y) Z), g y)
    (D : Finset (Torus d m) → ℝ) {C fac rate κ' P H : ℝ}
    (hC : 0 < C) (hfac : 0 ≤ fac) (hrate : 0 ≤ rate)
    (hSize : ∀ y, ((cy y).card : ℝ) ≤ C * (1 + D (cy y)))
    (hMod : ∀ y, ‖g y‖ ≤ fac * Real.exp (-rate * D (cy y)))
    (hκ' : 0 ≤ κ') (hκκ : κ' ≤ rate / C) (hP : 0 ≤ P)
    (hEntropy : ∀ b : Torus d m,
      ∑ y ∈ Finset.univ.filter (fun y => b ∈ cy y),
        Real.exp (-(rate / C - κ') * ((cy y).card : ℝ)) ≤ 1)
    (hHeavy : ∀ z, ‖τ z‖ ≤ Real.exp (-P - H))
    (hH : (fac * Real.exp rate) * Real.exp (fac * Real.exp rate) + κ' + 4 ≤ H) :
    (∑ Z : Finset (Torus d m), cell Z) =
      Q * Xi (shareBlock (Subtype.val : NePoly (Torus d m) → Finset (Torus d m)))
        (gasK cy (fun z => {z}) (fun z => {z}) g τ) ∧
    ∀ X : NePoly (Torus d m),
      ‖gasK cy (fun z => {z}) (fun z => {z}) g τ X‖ ≤
        3 * Real.exp (-P) * Real.exp (-(κ' - 2) * (X.1.card : ℝ)) := by
  refine ⟨final_large_integral_eq_polymerXi_of_factorization cy g τ cell Q boundary
    hOperator hBoundary, ?_⟩
  intro X
  apply final_large_gas_activity_bound_of_fixed_boundary cy g τ
    (B0 := fac * Real.exp rate) (κ' := κ') (κ'' := rate / C)
    (P := P) (H := H)
    (mul_nonneg hfac (Real.exp_pos rate).le) hκ' hκκ hP
  · intro b
    exact hEntropy b
  · intro y
    exact boundary_card_bound_of_size_comparison cy g D hC hfac hrate hSize hMod y
  · exact hHeavy
  · exact hH

/-- The connected-support and multiplicity premises supply the entropy condition via the
landed `coupling_entropy_le_one`. This is the final conditional theorem with only the physical
factorization, fixed localization, heavy tail, and modular boundary bound as analytic inputs. -/
theorem final_large_integral_polymer_bound_of_connected_localization
    {d m : ℕ} [NeZero m] (hd : 1 ≤ d) {Yt : Type*} [Fintype Yt]
    (cy : Yt → Finset (Torus d m)) (g : Yt → ℂ) (τ : Torus d m → ℂ)
    (cell : Finset (Torus d m) → ℂ) (Q : ℂ)
    (boundary : Finset (Torus d m) → ℂ)
    (hOperator : ∀ Z, cell Z = Q * (∏ z ∈ Z, τ z) * Complex.exp (boundary Z))
    (hBoundary : ∀ Z, boundary Z =
      ∑ y ∈ Finset.univ.filter (fun y => ¬ Disjoint (cy y) Z), g y)
    (D : Finset (Torus d m) → ℝ) {C fac rate κ' P H mY : ℝ}
    (hC : 0 < C) (hfac : 0 ≤ fac) (hrate : 0 ≤ rate)
    (hSize : ∀ y, ((cy y).card : ℝ) ≤ C * (1 + D (cy y)))
    (hMod : ∀ y, ‖g y‖ ≤ fac * Real.exp (-rate * D (cy y)))
    (hκ' : 0 ≤ κ') (hP : 0 ≤ P)
    (hcyne : ∀ y, (cy y).Nonempty)
    (hcyconn : ∀ y, ((blockGraph d m).induce (cy y : Set (Torus d m))).Connected)
    (hfib : ∀ T, ((Finset.univ.filter fun y => cy y = T).card : ℝ) ≤ mY)
    (hmY : 1 ≤ mY)
    (hκ : Real.log (mY * (((2 * d : ℕ) : ℝ)) ^ 2) + 3 ≤ rate / C - κ')
    (hHeavy : ∀ z, ‖τ z‖ ≤ Real.exp (-P - H))
    (hH : (fac * Real.exp rate) * Real.exp (fac * Real.exp rate) + κ' + 4 ≤ H) :
    (∑ Z : Finset (Torus d m), cell Z) =
      Q * Xi (shareBlock (Subtype.val : NePoly (Torus d m) → Finset (Torus d m)))
        (gasK cy (fun z => {z}) (fun z => {z}) g τ) ∧
    ∀ X : NePoly (Torus d m),
      ‖gasK cy (fun z => {z}) (fun z => {z}) g τ X‖ ≤
        3 * Real.exp (-P) * Real.exp (-(κ' - 2) * (X.1.card : ℝ)) := by
  have hd' : (1 : ℝ) ≤ ((2 * d : ℕ) : ℝ) := by
    have : 1 ≤ 2 * d := by omega
    exact_mod_cast this
  have hκκ : κ' ≤ rate / C := by
    have hlog : 0 ≤ Real.log (mY * (((2 * d : ℕ) : ℝ)) ^ 2) :=
      Real.log_nonneg (by nlinarith)
    linarith
  have hent : ∀ b : Torus d m,
      ∑ y ∈ Finset.univ.filter (fun y => b ∈ cy y),
        Real.exp (-(rate / C - κ') * ((cy y).card : ℝ)) ≤ 1 := by
    intro b
    exact final_large_entropy_of_connected hd cy hcyne hcyconn hfib hmY hκ b
  exact final_large_integral_polymer_bound_of_fixed_localization cy g τ cell Q boundary
    hOperator hBoundary D hC hfac hrate hSize hMod hκ' hκκ hP hent hHeavy hH


end Balaban.Green
