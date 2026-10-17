/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.ActionConvDef
public import Balaban.Fluctuation.CubeActionRealStar

/-!
# The star cube action is the restricted action of a region (W937)

`notes/phase1/LF4R-PLAN.md` §8.5 item (3).  `cubeActionStar_eq_actionRegionC`: for a `Region D` of a
generating set, the star cube action of `D.sites` (`Fluctuation/CubeActionRealStar.lean`) is the restricted
action `actionRegionC D` (`ActionConvDef.lean`) of the data.  Block, bond (half-bond weights) and mass terms
agree termwise, because `D.sites ⊆ Ω₁` and the bond weight vanishes unless an end point lies in `D.sites`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField.ActionConv

open Balaban.Multiscale Balaban.Background Balaban.Fluctuation Finset

variable {d L N₀ K N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ K ϱ}

open Classical in
/-- A sum over `Ω₁` of a function supported on `S ⊆ Ω₁` is the sum over `S`. -/
theorem sum_Omega_ite_eq (S : Finset (Torus d (N₀ * L ^ K))) (hS : S ⊆ G.Ω 1)
    (g : G.Ω 1 → ℂ) (F : Torus d (N₀ * L ^ K) → ℂ)
    (hgF : ∀ (x : Torus d (N₀ * L ^ K)) (hx : x ∈ S), g ⟨x, hS hx⟩ = F x) :
    ∑ x : G.Ω 1, (if (x : Torus d (N₀ * L ^ K)) ∈ S then g x else 0) = ∑ x ∈ S, F x := by
  have h1 : ∀ x : G.Ω 1, (if (x : Torus d (N₀ * L ^ K)) ∈ S then g x else 0) =
      if (x : Torus d (N₀ * L ^ K)) ∈ S then F x else 0 := by
    intro x
    by_cases hx : (x : Torus d (N₀ * L ^ K)) ∈ S
    · simp only [hx, ↓reduceIte]; exact hgF x hx
    · simp only [hx, ↓reduceIte]
  rw [Finset.sum_congr rfl fun x _ => h1 x]
  rw [Finset.sum_coe_sort (G.Ω 1) (fun x => if x ∈ S then F x else 0), Finset.sum_ite_mem,
    Finset.inter_eq_right.2 hS]

open Classical in
theorem cubeActionStar_eq_actionRegionC (D : Region G) (a : ℕ → ℝ) (ν : ℝ) (Dat : BgData G N)
    (φ : G.Ω 1 × Fin N → ℂ) :
    cubeActionStar G a ν D.sites Dat.Ψ Dat.h φ = actionRegionC D a ν Dat φ := by
  unfold cubeActionStar actionRegionC
  refine congrArg₂ _ (congrArg₂ _ ?_ ?_) ?_
  · refine congrArg (fun t => (1 / 2 : ℂ) * t) ?_
    unfold Region.blockPair
    exact sum_Omega_ite_eq D.sites D.sub_Ω _ _ fun x hx => rfl
  · refine congrArg (fun t => (1 / 2 : ℂ) * t) ?_
    unfold Region.bondPair
    refine Finset.sum_congr rfl fun x _ => ?_
    unfold cubeBondStar
    refine Finset.sum_congr rfl fun μ _ => ?_
    by_cases hc : x ∈ G.Ω 1 ∨ x + Pi.single μ 1 ∈ G.Ω 1
    · simp only [hc, ↓reduceIte]
      refine congrArg (· * _) ?_
      unfold Region.starWeight Balaban.Fluctuation.starWeight
      split_ifs <;> push_cast <;> ring
    · have h1 : x ∉ D.sites := fun h => hc (Or.inl (D.sub_Ω h))
      have h2 : x + Pi.single μ 1 ∉ D.sites := fun h => hc (Or.inr (D.sub_Ω h))
      simp only [hc, ↓reduceIte]
      unfold Region.starWeight
      simp [h1, h2]
  · refine congrArg (fun t => (ν : ℂ) / 2 * t) ?_
    unfold Region.massPair
    refine sum_Omega_ite_eq D.sites D.sub_Ω _ _ fun x hx => ?_
    unfold cubeMassTerm
    refine Finset.sum_congr rfl fun i _ => ?_
    have := svec_of_mem (G := G) φ ⟨x, D.sub_Ω hx⟩ i
    simp only [] at this ⊢
    rw [this]

end Balaban.LargeField.ActionConv
