/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.P6PairOp
public import Balaban.LargeField.Region.StepMisses
public import Balaban.Fluctuation.HoleStep
import Mathlib.Tactic.Linarith

/-!
# The generating sets of the step on a region (P5 (2.17))

At the step `k → k + 1` of the region calculus (`RegionStep`, `𝕋_k = Torus d n0`,
`𝕋_{k+1} = Torus d n1`, `n0 = L n1`) the fluctuation integral of P5 (2.16) is expanded around the
composed datum (2.17) of the old operator set `𝔹_k(W_k)` (`p6Hold`, `W_k = (Z_k^c)^{≈2}`) over the
set `(𝔹_k(W_k) ∩ Ω^c_{k+1}) ∪ Λ_{k+1}`: the same layers below `k + 1` and the top layer `Ω_{k+1}`.

* `fineK1_Omega_subset_p6Halo`: the new region lies in the halo `A` of `F♯` (its cubes meet
  `Z_k^c`; P5 (2.3), `RegionStep.blockMap_notMem_Omega`), hence in `W_k` at distance
  `> 5 L M₁ L^k` from `W_k^c` (`p6_halo_subset_W`, `p6_halo_far`);
* `p6Top`: the set of P5 (2.17), `p6Hold.addTop (fine Ω_{k+1})`; `p6Top_Ω_top`, `p6Top_Ω_of_le`,
  `p6Hold_precedes_p6Top`;
* `p6TopC`: the same on the cover torus (`castN`), next to `p6OldC`;
* `holeStepOf`: **the step on a region of a region step** (`Fluctuation.HoleStep`), with the old set
  `p6OldC`, the set `p6TopC`, and the mixed datum `liftMixed` of the old field `ψ_k`, the block
  variable `θ` and the field `h`.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Localization Balaban.Multiscale.GeneratingSet

set_option linter.unusedSectionVars false

variable {d M1 c n1 L k n0 m₁ : ℕ} [NeZero L] [NeZero M1] [NeZero c] [NeZero n0] [NeZero n1]
  {Rprev Rk : ℝ} (st : RegionStep d L n0 n1 Rprev Rk)

/-- **The new region lies in the halo of `F♯`**: a fine site of `Ω_{k+1}` has its cube of `𝕋_k`
outside `Z_k` (P5 (2.3), `RegionStep.blockMap_notMem_Omega`), so its cube of `𝕋_{k+1}` meets
`(Z_k^c)^≈`. -/
theorem fineK1_Omega_subset_p6Halo (hn : n0 = L * n1) (ρ' : ℕ) :
    fineK1 M1 c n1 L k st.Omega ⊆ p6Halo M1 c n1 L k ρ' st.Z := by
  intro x hx
  rw [mem_fineK1] at hx
  rw [mem_p6Halo]
  have hu : blockMap (L ^ k * (c * M1)) n0 x ∉ st.Z := fun hZ =>
    st.blockMap_notMem_Omega hZ (by rw [blockMap_k_succ hn x]; exact hx)
  refine subset_nbhd 1 _ ⟨blockMap (L ^ k * (c * M1)) n0 x, subset_nbhd _ _ hu, ?_⟩
  exact blockMap_k_succ hn x

/-- The new region lies in `W_k`. -/
theorem fineK1_Omega_subset_stepW (hn : n0 = L * n1) {ρ' : ℕ} (hρ : 2 * L ≤ ρ' + 2) :
    fineK1 M1 c n1 L k st.Omega ⊆ stepW M1 c n1 L k ρ' st.Z :=
  (fineK1_Omega_subset_p6Halo st hn ρ').trans (p6_halo_subset_W hn hρ st.Z)

/-- **The set of P5 (2.17)**: `(𝔹_k(W_k) ∩ Ω^c_{k+1}) ∪ Λ_{k+1}`, the old operator set `𝔹_k(W_k)`
with the top layer `Ω_{k+1}` (`ρ' = ⌊R_{k-1}⌋ ≥ 3 L`, `c ≥ 5`). -/
noncomputable def p6Top (hn : n0 = L * n1) {ρ' : ℕ} (hρ : 3 * L ≤ ρ') (hc : 5 ≤ c) :
    GeneratingSet d L (M1 * (c * n1)) (k + 1) (minSep L M1) :=
  (p6Hold M1 c n1 L k ρ' st.Z).addTop (fineK1 M1 c n1 L k st.Omega)
    ((isCubeUnion_fineK1 _).isBlockUnion le_rfl)
    (fun _ => by
      rw [p6Hold_Ω_k hn]
      exact fineK1_Omega_subset_stepW st hn (by omega))
    (fun _ x hx y hy => by
      rw [p6Hold_Ω_k hn] at hx
      exact p6_halo_far hn hρ hc st.Z hx (fineK1_Omega_subset_p6Halo st hn ρ' hy))

variable {st}

theorem p6Top_Ω_top (hn : n0 = L * n1) {ρ' : ℕ} (hρ : 3 * L ≤ ρ') (hc : 5 ≤ c) :
    (p6Top st hn hρ hc).Ω (k + 1) = fineK1 M1 c n1 L k st.Omega := by
  unfold p6Top
  rw [GeneratingSet.addTop_Ω]; simp

theorem p6Top_Ω_of_le (hn : n0 = L * n1) {ρ' : ℕ} (hρ : 3 * L ≤ ρ') (hc : 5 ≤ c) {j : ℕ}
    (hj : j ≤ k) : (p6Top st hn hρ hc).Ω j = (p6Hold M1 c n1 L k ρ' st.Z).Ω j := by
  have h : j ≠ k + 1 := by omega
  unfold p6Top
  rw [GeneratingSet.addTop_Ω]; simp [h]

/-- `𝔹_k(W_k) ≺ (𝔹_k(W_k) ∩ Ω^c_{k+1}) ∪ Λ_{k+1}`. -/
theorem p6Hold_precedes_p6Top (hn : n0 = L * n1) {ρ' : ℕ} (hρ : 3 * L ≤ ρ') (hc : 5 ≤ c) :
    Background.Precedes (p6Hold M1 c n1 L k ρ' st.Z) (p6Top st hn hρ hc) := by
  intro i _ hi
  by_cases h : i = k + 1
  · subst h
    rw [p6Hold_Ω_top]
    exact Finset.empty_subset _
  · rw [p6Top_Ω_of_le hn hρ hc (by omega)]

variable (st)

/-- The set of P5 (2.17) on the cover torus. -/
noncomputable def p6TopC (hM1 : M1 = L ^ m₁) (hn : n0 = L * n1) {ρ' : ℕ} (hρ : 3 * L ≤ ρ')
    (hc : 5 ≤ c) : GeneratingSet d L ((c * n1) * L ^ m₁) (k + 1) (minSep L M1) :=
  castN (p6_side hM1) (p6Top st hn hρ hc)

theorem castN_Ω_subset {N₀ N₀' K' : ℕ} [NeZero N₀] [NeZero N₀'] {ϱ ϱ' : ℝ} (h : N₀ = N₀')
    {G : GeneratingSet d L N₀ K' ϱ} {G' : GeneratingSet d L N₀ K' ϱ'} {i j : ℕ}
    (hs : G.Ω i ⊆ G'.Ω j) : (castN h G).Ω i ⊆ (castN h G').Ω j := by
  subst h; exact hs

theorem castN_Ω_eq_empty {N₀ N₀' K' : ℕ} [NeZero N₀] [NeZero N₀'] {ϱ : ℝ} (h : N₀ = N₀')
    {G : GeneratingSet d L N₀ K' ϱ} {i : ℕ} (he : G.Ω i = ∅) : (castN h G).Ω i = ∅ := by
  subst h; exact he

/-- **The step on a region of a region step** (P5 (2.16)–(2.20)): the old operator set
`𝔹_k(W_k)` (`p6OldC`), the set of (2.17) (`p6TopC`), and the mixed datum `θ̃ = lift_{k,k+1}(ψ_k, θ)`
of the old field `ψ_k` (on the blocks of side `L^k`), the block variable `θ` (on the blocks of side
`L^{k+1}`) and the field `h₀`, on the cover torus; weights `compWeight L a₁`, mass `ν`, coupling
`β`, radius `p₁`, threshold `δ`. -/
noncomputable def holeStepOf (hM1 : M1 = L ^ m₁) (hn : n0 = L * n1) {ρ' : ℕ} (hρ : 3 * L ≤ ρ')
    (hc : 5 ≤ c) (hk1 : 1 ≤ k) {N : ℕ}
    (ψ : Torus d (((c * n1) * L ^ m₁) * L ^ (k + 1 - k)) → Fin N → ℂ)
    (θ : Torus d (((c * n1) * L ^ m₁) * L ^ (k + 1 - (k + 1))) → Fin N → ℂ) (h₀ : Fin N → ℝ)
    (a₁ ν β p₁ δ : ℝ) :
    Fluctuation.HoleStep d L (c * n1) m₁ k N (minSep L M1) (minSep L M1) where
  G := p6OldC hM1 ρ' st.Z
  G' := p6TopC st hM1 hn hρ hc
  hpre := castN_precedes (p6_side hM1) (p6Hold_precedes_p6Top hn hρ hc)
  topG := castN_Ω_eq_empty (p6_side hM1) (p6Hold_Ω_top st.Z)
  topIn := castN_Ω_subset (p6_side hM1) (by
    rw [p6Top_Ω_top hn hρ hc, p6Hold_Ω_k hn]
    exact fineK1_Omega_subset_stepW st hn (by omega))
  hk1 := hk1
  D' := liftMixed (p6TopC st hM1 hn hρ hc)
    ((p6TopC st hM1 hn hρ hc).blockUnion (k + 1) (by omega) le_rfl) subset_rfl ψ θ
    (fun i => (h₀ i : ℂ))
  h₀ := h₀
  hh₀ := fun _ hx _ => by rw [liftMixed_h _ _ _ _ _ _ hx]
  a₁ := a₁
  ν := ν
  β := β
  p₁ := p₁
  δ := δ

end Balaban.LargeField
