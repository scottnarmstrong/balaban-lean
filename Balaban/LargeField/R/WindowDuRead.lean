/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.WindowDuSwitch
public import Balaban.LargeField.R.CancelRemaining
public import Balaban.LargeField.R.WindowConvPhysReadTransport

/-!
# What the restricted action reads (blocker 4)

The restricted action `A_X(a, ν, D, φ)` reads the field `φ` only at the sites of `Ω₁` that lie in
`X` or next to `X`, and the datum `Ψ` only at the sites of `X` or next to `X` (`barField` reads
`Ψ` off `Ω₁`); `A_X(a, 0, D, φ)` does not read the external field.
* `actionRegionC_congr_field`, `actionRegionC_congr_Ψ_zero`: the corresponding congruences;
* `actionRegionC_mass_sub`: `A_X(a, ν, D, φ) - A_X(a, 0, D, φ) = (ν/2) ⟨φ - h, φ - h⟩_X`.
-/

@[expose] public section

namespace Balaban.LargeField.ActionConv

open Balaban.Multiscale Balaban.Background Finset

variable {d L N₀ K N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ K ϱ}

theorem Region.mem_or_of_starWeight_ne {X : Region G} {x : Torus d (N₀ * L ^ K)} {μ : Fin d}
    (hw : X.starWeight x μ ≠ 0) :
    (x ∈ X.sites ∨ x + Pi.single μ 1 ∈ X.sites) := by
  by_contra hcon
  push Not at hcon
  apply hw
  unfold Region.starWeight
  simp [hcon.1, hcon.2]

theorem actionRegionC_mass_sub (X : Region G) (a : ℕ → ℝ) (ν : ℝ) (Dat : BgData G N)
    (φ : G.Ω 1 × Fin N → ℂ) :
    actionRegionC X a ν Dat φ - actionRegionC X a 0 Dat φ =
      (ν : ℂ) / 2 * X.massPair (fun x i => svec G φ x i - Dat.h x i)
        (fun x i => svec G φ x i - Dat.h x i) := by
  unfold actionRegionC
  simp

/-- The action does not see the field off the sites of `Ω₁` in or next to `X`. -/
theorem actionRegionC_congr_field (X : Region G) (a : ℕ → ℝ) (ν : ℝ) (Dat : BgData G N)
    {φ φ' : G.Ω 1 × Fin N → ℂ}
    (h : ∀ y : G.Ω 1, ((y : Torus d (N₀ * L ^ K)) ∈ X.sites ∨ ∃ μ : Fin d,
      (y : Torus d (N₀ * L ^ K)) + Pi.single μ 1 ∈ X.sites ∨
        (y : Torus d (N₀ * L ^ K)) - Pi.single μ 1 ∈ X.sites) → ∀ i, φ (y, i) = φ' (y, i)) :
    actionRegionC X a ν Dat φ = actionRegionC X a ν Dat φ' := by
  have hs : ∀ x ∈ X.sites, ∀ i, svec G φ x i = svec G φ' x i := fun x hx i => by
    have h1 := X.sub_Ω hx
    rw [svec_of_mem G φ ⟨x, h1⟩ i, svec_of_mem G φ' ⟨x, h1⟩ i]
    exact h ⟨x, h1⟩ (Or.inl hx) i
  have hb : ∀ x ∈ X.sites, ∀ i, blockAvg G φ x i = blockAvg G φ' x i := fun x hx i => by
    unfold blockAvg
    congr 1
    exact Finset.sum_congr rfl fun y hy => hs y (X.blockClosed x hx y hy) i
  have hbar : ∀ (x : Torus d (N₀ * L ^ K)) (μ : Fin d), (x ∈ X.sites ∨ x + Pi.single μ 1 ∈ X.sites) →
      ∀ i, barField G Dat.Ψ φ x i = barField G Dat.Ψ φ' x i ∧
        barField G Dat.Ψ φ (x + Pi.single μ 1) i = barField G Dat.Ψ φ' (x + Pi.single μ 1) i :=
    fun x μ hx i => by
      constructor
      · by_cases h1 : x ∈ G.Ω 1
        · simp only [barField, h1, ↓reduceDIte]
          exact h ⟨x, h1⟩ (by rcases hx with hx | hx; exacts [Or.inl hx, Or.inr ⟨μ, Or.inl hx⟩]) i
        · simp [barField, h1]
      · by_cases h1 : x + Pi.single μ 1 ∈ G.Ω 1
        · simp only [barField, h1, ↓reduceDIte]
          exact h ⟨_, h1⟩ (by
            rcases hx with hx | hx
            · exact Or.inr ⟨μ, Or.inr (by simpa using hx)⟩
            · exact Or.inl hx) i
        · simp [barField, h1]
  unfold actionRegionC
  have e1 : X.blockPair a (fun x i => Dat.Ψ x i - blockAvg G φ x i)
      (fun x i => Dat.Ψ x i - blockAvg G φ x i) =
      X.blockPair a (fun x i => Dat.Ψ x i - blockAvg G φ' x i)
      (fun x i => Dat.Ψ x i - blockAvg G φ' x i) := by
    unfold Region.blockPair
    refine Finset.sum_congr rfl fun x hx => ?_
    simp only [hb x hx]
  have e2 : X.bondPair (barField G Dat.Ψ φ) (barField G Dat.Ψ φ) =
      X.bondPair (barField G Dat.Ψ φ') (barField G Dat.Ψ φ') := by
    unfold Region.bondPair
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun μ _ => ?_
    by_cases hw : X.starWeight x μ = 0
    · simp [hw]
    · have hx := Region.mem_or_of_starWeight_ne hw
      simp only [fun i => (hbar x μ hx i).1, fun i => (hbar x μ hx i).2]
  have e3 : X.massPair (fun x i => svec G φ x i - Dat.h x i) (fun x i => svec G φ x i - Dat.h x i) =
      X.massPair (fun x i => svec G φ' x i - Dat.h x i) (fun x i => svec G φ' x i - Dat.h x i) := by
    unfold Region.massPair
    refine Finset.sum_congr rfl fun x hx => ?_
    simp only [hs x hx]
  rw [e1, e2, e3]

/-- At mass `0` the action reads the datum `Ψ` only at the sites in or next to `X`, and does not
read the external field. -/
theorem actionRegionC_congr_Ψ_zero (X : Region G) (a : ℕ → ℝ) {D D' : BgData G N}
    (hΨ : ∀ y : Torus d (N₀ * L ^ K), (y ∈ X.sites ∨ ∃ μ : Fin d,
      y + Pi.single μ 1 ∈ X.sites ∨ y - Pi.single μ 1 ∈ X.sites) → D.Ψ y = D'.Ψ y)
    (φ : G.Ω 1 × Fin N → ℂ) :
    actionRegionC X a 0 D φ = actionRegionC X a 0 D' φ := by
  have hbar : ∀ (x : Torus d (N₀ * L ^ K)) (μ : Fin d), (x ∈ X.sites ∨ x + Pi.single μ 1 ∈ X.sites) →
      ∀ i, barField G D.Ψ φ x i = barField G D'.Ψ φ x i ∧
        barField G D.Ψ φ (x + Pi.single μ 1) i = barField G D'.Ψ φ (x + Pi.single μ 1) i :=
    fun x μ hx i => by
      constructor
      · by_cases h1 : x ∈ G.Ω 1
        · simp [barField, h1]
        · simp only [barField, h1, ↓reduceDIte]
          rw [hΨ x (by rcases hx with hx | hx; exacts [Or.inl hx, Or.inr ⟨μ, Or.inl hx⟩])]
      · by_cases h1 : x + Pi.single μ 1 ∈ G.Ω 1
        · simp [barField, h1]
        · simp only [barField, h1, ↓reduceDIte]
          rw [hΨ _ (by
            rcases hx with hx | hx
            · exact Or.inr ⟨μ, Or.inr (by simpa using hx)⟩
            · exact Or.inl hx)]
  unfold actionRegionC
  have e1 : X.blockPair a (fun x i => D.Ψ x i - blockAvg G φ x i)
      (fun x i => D.Ψ x i - blockAvg G φ x i) =
      X.blockPair a (fun x i => D'.Ψ x i - blockAvg G φ x i)
      (fun x i => D'.Ψ x i - blockAvg G φ x i) := by
    unfold Region.blockPair
    refine Finset.sum_congr rfl fun x hx => ?_
    simp only [hΨ x (Or.inl hx)]
  have e2 : X.bondPair (barField G D.Ψ φ) (barField G D.Ψ φ) =
      X.bondPair (barField G D'.Ψ φ) (barField G D'.Ψ φ) := by
    unfold Region.bondPair
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun μ _ => ?_
    by_cases hw : X.starWeight x μ = 0
    · simp [hw]
    · have hx := Region.mem_or_of_starWeight_ne hw
      simp only [fun i => (hbar x μ hx i).1, fun i => (hbar x μ hx i).2]
  rw [e1, e2]
  simp

section Transport

variable {N₀l kl N₀w kw : ℕ} [NeZero N₀l] [NeZero N₀w] {ϱl ϱw : ℝ}
  {Gl : GeneratingSet d L N₀l kl ϱl} {Gw : GeneratingSet d L N₀w kw ϱw}

/-- The field transported from `Gw` does not depend on the extension datum at the sites of `Ω₁(Gl)`
that correspond to sites of `Ω₁(Gw)`. -/
theorem transportField_congr_of_mem (e : Torus d (N₀w * L ^ kw) ≃ Torus d (N₀l * L ^ kl))
    (Ψ₁ Ψ₂ : Torus d (N₀w * L ^ kw) → Fin N → ℂ) (φw : Gw.Ω 1 × Fin N → ℂ)
    (y : Gl.Ω 1) (hy : e.symm (y : Torus d (N₀l * L ^ kl)) ∈ Gw.Ω 1) (i : Fin N) :
    transportField (Gl := Gl) e Ψ₁ φw (y, i) = transportField (Gl := Gl) e Ψ₂ φw (y, i) := by
  simp [transportField, barField, hy]

end Transport

/-- A site and its neighbours are within distance `1`. -/
theorem torusDist_le_one_of_near {N₀ k : ℕ} [NeZero N₀] (x y : Torus d (N₀ * L ^ k))
    (h : y = x ∨ ∃ μ : Fin d, y = x + Pi.single μ 1 ∨ y = x - Pi.single μ 1) :
    Green.torusDist d (N₀ * L ^ k) x y ≤ 1 := by
  rcases h with rfl | ⟨μ, rfl | rfl⟩
  · rw [torusDist_self']; norm_num
  · exact Adj.torusDist_le (adj_add_single _ μ)
  · exact Adj.torusDist_le (adj_sub_single _ μ)

/-- A site in or next to a region is within distance `r ≥ 1` of a site of the region. -/
theorem Region.exists_dist_le_of_near (X : Region G) {y : Torus d (N₀ * L ^ K)}
    (hy : y ∈ X.sites ∨ ∃ μ : Fin d, y + Pi.single μ 1 ∈ X.sites ∨ y - Pi.single μ 1 ∈ X.sites)
    {r : ℝ} (hr : 1 ≤ r) : ∃ z ∈ X.sites, Green.torusDist d (N₀ * L ^ K) z y ≤ r := by
  rcases hy with hy | ⟨μ, hy | hy⟩
  · exact ⟨y, hy, by rw [torusDist_self']; linarith only [hr]⟩
  · exact ⟨_, hy, (torusDist_le_one_of_near _ y (Or.inr ⟨μ, Or.inr (by simp)⟩)).trans hr⟩
  · exact ⟨_, hy, (torusDist_le_one_of_near _ y (Or.inr ⟨μ, Or.inl (by simp)⟩)).trans hr⟩

end Balaban.LargeField.ActionConv
