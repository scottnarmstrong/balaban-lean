/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.IrrelTorusXidomPatch
import Mathlib.Tactic.Linarith

/-!
# Path estimate for the small-polymer spin field

The source centre estimate and the first-difference bound place every spin on a sufficiently
small polymer within the anisotropic spin radius after real frame alignment.
-/

@[expose] public section

namespace Balaban.SmallField.Def6v2

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
  Balaban.SmallField.Def6

variable {d L N₁ m₁ k N m₀ : ℕ} [NeZero L] [NeZero N₁]
  {j : ℕ} {y : CTorus d L N₁ m₁ k} {X : Set (CTorus d L N₁ m₁ k)}
  {S : Finset (Site d)} {i₀ : Fin N} {ν σ ε K₂ r q : ℝ}
  {ψ : Site d → Spin N} {b : Spin N}
  {Dom : Set ((Site d → Spin N) × Spin N)}

/-- The placed field of a `DataHypAniso` datum stays in the spin polydisc on a small
polymer, provided its real-frame centre and the path length fit in the radius. -/
theorem local_spin_bound_of_dataHyp
    (hjk : j ≤ k) (hy : Aligned (L ^ j) y)
    (hX : IsPolyDom m₀ j X) (hyX : y ∈ X)
    (hS' : ∀ s ∈ S, ∃ x ∈ X, Aligned (L ^ j) x ∧
      unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x - y) = s)
    (dat : DataHypAniso Dom ν σ ε K₂ ψ b)
    (hσε : 0 ≤ σ * ε)
    (hcentre : ∀ i, ‖ψ 0 i - (Pi.single i₀ 1 : Spin N) i‖ ≤ q)
    (hsmall : q + diamA d L m₀ m₁ * (1 + sizeJ m₀ j X) * (σ * ε) ≤ r) :
    ∀ z, unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (z - y) ∈ S →
      ∀ i, ‖fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ S
        (pack S ψ b) (z - y) i - (Pi.single i₀ 1 : Spin N) i‖ ≤ r := by
  intro z hz i
  let s := unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (z - y)
  obtain ⟨x, hx, hxa, hxs⟩ := hS' s hz
  have hgeom : (l1 s : ℝ) ≤ diamA d L m₀ m₁ * (1 + sizeJ m₀ j X) := by
    rw [l1_cast, ← hxs]
    exact unlift_sub_diam hjk hX hx hyX hxa hy
  have hpath : ‖ψ s - ψ 0‖ ≤
      diamA d L m₀ m₁ * (1 + sizeJ m₀ j X) * (σ * ε) := by
    have hp := norm_sub_le_l1 dat.adj 0 s
    simp only [zero_add] at hp
    exact hp.trans (mul_le_mul_of_nonneg_right hgeom hσε)
  have heq : fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ S
      (pack S ψ b) (z - y) i = ψ s i := by
    simp only [fieldOf, s, hz, ↓reduceDIte, pack, Sum.elim_inl]
  rw [heq]
  calc
    ‖ψ s i - (Pi.single i₀ 1 : Spin N) i‖ ≤
        ‖ψ s i - ψ 0 i‖ + ‖ψ 0 i - (Pi.single i₀ 1 : Spin N) i‖ := by
          have he : ψ s i - (Pi.single i₀ 1 : Spin N) i =
              (ψ s i - ψ 0 i) + (ψ 0 i - (Pi.single i₀ 1 : Spin N) i) := by ring
          rw [he]
          exact norm_add_le _ _
    _ ≤ ‖ψ s - ψ 0‖ + q := by
      have hi : ‖ψ s i - ψ 0 i‖ ≤ ‖ψ s - ψ 0‖ := by
        simpa only [Pi.sub_apply] using (norm_le_pi_norm (ψ s - ψ 0) i)
      exact add_le_add hi (hcentre i)
    _ ≤ r := by linarith

end Balaban.SmallField.Def6v2
