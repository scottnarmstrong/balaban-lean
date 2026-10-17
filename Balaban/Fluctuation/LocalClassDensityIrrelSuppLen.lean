/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalClassDensityIrrelSupport
public import Balaban.Fluctuation.HatLabelsGeom
public import Balaban.SmallField.Def6BridgeGeom

/-!
# The size of the support polymer of a label (`LocalClassDensityIrrelSuppLen`)

For a polymer `X` of `𝒟_j` and `y ∈ X`, the support `X^⋆ = X ∪ □(y)` of the label `(j, y, X)`
has covering size at most `d^cov_j(X) + c_G`, `c_G = 2 d L` (connected-structure surgery:
`thick_union` for the single cube `□(y)`, which shares the `π_j`-cell of `y` with `X`).

* `cell_subset_cubeAt`: the `π_j`-cell of `y` lies in `□(y)`;
* `treeLenCovOne_support_le`: `d^cov_j(X ∪ □(y)) ≤ d^cov_j(X) + 2 d L`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Localization Balaban.SmallField Balaban.SmallField.Def6
  Balaban.SmallField.Def6v2

section SuppLen

variable {d L N₁ m₁ k : ℕ} [NeZero L] [NeZero N₁] {m₀ j : ℕ}

/-- **The `π_j`-cell of `y` lies in `□(y)`.** -/
theorem cell_subset_cubeAt (hN : L ^ m₀ ∣ N₁) (hjk : j ≤ k) (y : CTorus d L N₁ m₁ k) :
    box (cbase (cellSide L m₀ m₁ j) y) (cellSide L m₀ m₁ j) ⊆
      box (cbase (cellSide L m₀ m₁ j) y - natT fun _ => L / 2 * cellSide L m₀ m₁ j)
        (L * cellSide L m₀ m₁ j) := by
  have hdvd := cellSide_dvd (K := k) (m₁ := m₁) (L := L) (N₁ := N₁) hN hjk
  have hpos := cellSide_pos (L := L) m₀ m₁ j
  set s := cellSide L m₀ m₁ j with hs
  set c : CTorus d L N₁ m₁ k := cbase s y - natT fun _ => L / 2 * s with hc
  have hcal : Aligned s c := aligned_cubeAt_base hN hjk y
  obtain ⟨w, hw⟩ := exists_cell_of_mem_cube hpos (mem_cubeAt (m₀ := m₀) (j := j) y)
  have hal : Aligned s (c + natT fun μ => s * (w μ : ℕ)) :=
    aligned_add_natT hdvd hcal fun μ => by simp
  have hb : cbase s y = c + natT fun μ => s * (w μ : ℕ) := cbase_eq_of_mem_box hdvd hal hw
  rintro x ⟨u, hu, rfl⟩
  refine ⟨(fun μ => s * (w μ : ℕ)) + u, fun μ => ?_, ?_⟩
  · have h1 : (w μ : ℕ) + 1 ≤ L := (w μ).2
    have h2 : s * (w μ : ℕ) + s ≤ L * s := by nlinarith [Nat.mul_le_mul_left s h1]
    simp only [Pi.add_apply]
    have := hu μ
    omega
  · rw [hb, natT_add, add_assoc]

/-- **The size of the support polymer.**  For a polymer `X` of `𝒟_j` and `y ∈ X`,
`d^cov_j(X ∪ □(y)) ≤ d^cov_j(X) + 2 d L`. -/
theorem treeLenCovOne_support_le (hN : L ^ m₀ ∣ N₁) (hjk : j ≤ k)
    {X : Set (CTorus d L N₁ m₁ k)} (hX : IsPolyDom m₀ j X) {y : CTorus d L N₁ m₁ k} (hy : y ∈ X) :
    treeLenCovOne m₀ j (X ∪ box (cbase (cellSide L m₀ m₁ j) y -
        natT fun _ => L / 2 * cellSide L m₀ m₁ j) (L * cellSide L m₀ m₁ j)) ≤
      treeLenCovOne m₀ j X + cG d L := by
  classical
  have hdvd := cellSide_dvd (K := k) (m₁ := m₁) (L := L) (N₁ := N₁) hN hjk
  have hpos := cellSide_pos (L := L) m₀ m₁ j
  have hP : ∀ p ∈ ({cbase (cellSide L m₀ m₁ j) y - natT fun _ => L / 2 * cellSide L m₀ m₁ j} :
      Finset (CTorus d L N₁ m₁ k)), Aligned (cellSide L m₀ m₁ j) p ∧
      ∃ t, Aligned (cellSide L m₀ m₁ j) t ∧
        box t (cellSide L m₀ m₁ j) ⊆ X ∩ box p (L * cellSide L m₀ m₁ j) := by
    intro p hp
    rw [Finset.mem_singleton] at hp
    subst hp
    exact ⟨aligned_cubeAt_base hN hjk y, cbase (cellSide L m₀ m₁ j) y, aligned_cbase y,
      fun x hx => ⟨cell_subset_of_isPolyDom hN hjk hX y hy hx, cell_subset_cubeAt hN hjk y hx⟩⟩
  have h := (thick_union (m₀ := m₀) (j := j) (isDj_of_isPolyDom hX) _ hP).2
  simpa using h

end SuppLen

end Balaban.Fluctuation
