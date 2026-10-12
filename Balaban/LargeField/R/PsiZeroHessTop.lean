/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.PsiZeroBlocks
public import Balaban.LargeField.R.PsiZeroInput
public import Balaban.Background.Def5Response
public import Balaban.Multiscale.Locality

/-!
# Tangent data of the top layer (PSIZERO-HESS §5, row 1)

For a box `Z` of `k`-blocks lying over the top layer `Ω_k(G)` the tangent datum `Jv` of a perturbation
`v ∈ SuppSpace Z` is the lift of its zero extension (`topTangent`).  It is the derivative of the data line
`t ↦ dataR (ψ + t v)` (`dataR_merge_line`), it vanishes off `Ω_k(G)` and in particular on the collar
(`topLift_zero_collar`), and each block of `Z` carries `L^{kd}` fine sites, all of layer `k`
(`topLift_block_count`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background

section Top

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} (G : GeneratingSet d L N₀ k ϱ)
  {Z : Finset (Torus d (N₀ * L ^ (k - k)))}

/-- The tangent datum `J v` of a perturbation supported in `Z`: the lift of its zero extension. -/
noncomputable def topTangent (v : SuppSpace Z N) : BgData G N :=
  dataC G (fun z i => (extSupp Z v z i : ℂ))

variable {G}

theorem topTangent_Ψ (v : SuppSpace Z N) {x : Torus d (N₀ * L ^ k)} (hx : x ∈ dataSites G) (i : Fin N) :
    (topTangent G v).Ψ x i = (extSupp Z v (jBlock d L N₀ k k x) i : ℂ) := by
  simp [topTangent, dataC, liftSingle_Ψ G _ _ hx]

theorem topTangent_h (v : SuppSpace Z N) (x : Torus d (N₀ * L ^ k)) (i : Fin N) :
    (topTangent G v).h x i = 0 := by
  by_cases hx : x ∈ G.Ω 1
  · simp [topTangent, dataC, liftSingle_h G _ _ hx]
  · simp [(topTangent G v).h_zero x hx]

/-- On the top blocks over `Z` the lift of `Z`-supported perturbations is the zero extension. -/
theorem topLift_extSupp (hΩ : OverTop G (Z : Set (Torus d (N₀ * L ^ (k - k))))) (hk : 1 ≤ k)
    (v : SuppSpace Z N) {x : Torus d (N₀ * L ^ k)} (hx : jBlock d L N₀ k k x ∈ Z) (i : Fin N) :
    x ∈ G.Ω k ∧ x ∈ dataSites G ∧ G.layerIndex x = k ∧
      (topTangent G v).Ψ x i = (v (⟨jBlock d L N₀ k k x, hx⟩, i) : ℂ) := by
  have hxk : x ∈ G.Ω k := hΩ x hx
  have h1 : x ∈ G.Ω 1 := G.Ω_antitone le_rfl hk (by omega) hxk
  have hds : x ∈ dataSites G := (mem_dataSites G).2 (Or.inl h1)
  refine ⟨hxk, hds, G.layerIndex_eq hk le_rfl (G.mem_layer.2 ⟨hxk, by rw [G.top]; simp⟩), ?_⟩
  rw [topTangent_Ψ v hds]
  simp [extSupp, hx]

/-- The tangent datum vanishes off `Ω_k(G)`, in particular on the collar. -/
theorem topLift_zero_collar (hΩ : OverTop G (Z : Set (Torus d (N₀ * L ^ (k - k)))))
    (v : SuppSpace Z N) {x : Torus d (N₀ * L ^ k)} (hx : x ∉ G.Ω k) (i : Fin N) :
    (topTangent G v).Ψ x i = 0 := by
  by_cases hds : x ∈ dataSites G
  · rw [topTangent_Ψ v hds]
    have : jBlock d L N₀ k k x ∉ Z := fun h => hx (hΩ x h)
    simp [extSupp, this]
  · simp [(topTangent G v).Ψ_zero x hds]

theorem topLift_collar_zero (hΩ : OverTop G (Z : Set (Torus d (N₀ * L ^ (k - k))))) (hk : 1 ≤ k)
    (v : SuppSpace Z N) {x : Torus d (N₀ * L ^ k)} (hx : x ∈ collar G) (i : Fin N) :
    (topTangent G v).Ψ x i = 0 := by
  refine topLift_zero_collar hΩ v (fun h => ((mem_collar G).1 hx).1 ?_) i
  exact G.Ω_antitone le_rfl hk (by omega) h

/-- Each top block `z ∈ Z` consists of `L^{kd}` fine sites of `Ω_k`, all of layer `k`, with the same block. -/
theorem topLift_block_count (hΩ : OverTop G (Z : Set (Torus d (N₀ * L ^ (k - k))))) (hk : 1 ≤ k)
    {z : Torus d (N₀ * L ^ (k - k))} (hz : z ∈ Z) :
    (Finset.univ.filter fun x : Torus d (N₀ * L ^ k) => jBlock d L N₀ k k x = z).card = (L ^ k) ^ d ∧
      ∀ x : Torus d (N₀ * L ^ k), jBlock d L N₀ k k x = z →
        x ∈ G.Ω k ∧ G.layerIndex x = k ∧ G.blk k x = Finset.univ.filter
          fun y : Torus d (N₀ * L ^ k) => jBlock d L N₀ k k y = z := by
  classical
  have hsame : ∀ x, jBlock d L N₀ k k x = z → G.blk k x = Finset.univ.filter
      fun y : Torus d (N₀ * L ^ k) => jBlock d L N₀ k k y = z := by
    intro x hx
    ext y
    simp [GeneratingSet.mem_blk, hx]
  refine ⟨?_, fun x hx => ⟨?_, ?_, hsame x hx⟩⟩
  · obtain ⟨x0, hx0⟩ : ∃ x0 : Torus d (N₀ * L ^ k), jBlock d L N₀ k k x0 = z := by
      have hN : 0 < L ^ k := pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) k
      exact Balaban.exists_blockMap_eq (fine_eq_block L N₀ k) hN z
    rw [← hsame x0 hx0]
    exact Balaban.Multiscale.card_blk (G := G) k le_rfl x0
  · exact hΩ x (hx ▸ hz)
  · have hxk : x ∈ G.Ω k := hΩ x (hx ▸ hz)
    exact G.layerIndex_eq hk le_rfl (G.mem_layer.2 ⟨hxk, by rw [G.top]; simp⟩)

end Top

end Balaban.LargeField
