/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RRemovedHidLeafMean
public import Balaban.LargeField.R.RRemovedHidLeafAssemble
public import Balaban.LargeField.R.RRemovedHidGaussEq

/-!
# The exact node integral of the window is `const^♮ e^{-𝒢^♮}` (W942)

`notes/phase1/LF4R-PLAN.md` §8.5.  `window_node_integral_eq`: the exact integral over the node coordinates of the
regrouping of `exists_window_hid` (`lintegral_gauss_coords_eq`) equals `ofReal (constNat N β_k aN Zb · e^{-Re 𝒢^♮})`
(`CancelIdentity.lean`) for the window generating set `G = W.windowGenSet` of the history, the composed weights
`aN z = (precision of the root of z)/β_k` and the multiscale data `Ψ` of the window, given the data relations `hΨ`
(`Ψ` is the field `fld` on the layers of the sites of the fixed top blocks) and `hψk` (`ψ_k` is the output `ft`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale RegionHistory

section Aux

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ ϱ' : ℝ}

theorem layerIndex_congr (G : GeneratingSet d L N₀ k ϱ) (G' : GeneratingSet d L N₀ k ϱ')
    (h : ∀ j, G.Ω j = G'.Ω j) (x : Torus d (N₀ * L ^ k)) : G.layerIndex x = G'.layerIndex x := by
  classical
  have hlay : ∀ j, x ∈ G.layer j ↔ x ∈ G'.layer j := fun j => by
    rw [GeneratingSet.mem_layer, GeneratingSet.mem_layer, h j, h (j + 1)]
  by_cases hex : ∃ j, 1 ≤ j ∧ j ≤ k ∧ x ∈ G.layer j
  · obtain ⟨j, hj1, hjk, hjl⟩ := hex
    rw [G.layerIndex_eq hj1 hjk hjl, G'.layerIndex_eq hj1 hjk ((hlay j).mp hjl)]
  · have hex' : ¬ ∃ j, 1 ≤ j ∧ j ≤ k ∧ x ∈ G'.layer j := by
      rintro ⟨j, hj1, hjk, hjl⟩
      exact hex ⟨j, hj1, hjk, (hlay j).mpr hjl⟩
    unfold GeneratingSet.layerIndex
    rw [dite_eq_right_of_eq_false (eq_false hex), dite_eq_right_of_eq_false (eq_false hex')]

theorem compMeanT_im_eq_zero (G : GeneratingSet d L N₀ k ϱ) {N : ℕ} (ϖ : ℕ → ℝ)
    (Ψ : Torus d (N₀ * L ^ k) → Fin N → ℂ) (z : Torus d (N₀ * L ^ (k - k))) (i : Fin N)
    (h : ∀ s ∈ fib d L N₀ k k z, (Ψ s i).im = 0) :
    (ActionConv.compMeanT G ϖ Ψ z i).im = 0 := by
  unfold ActionConv.compMeanT
  rw [← Complex.ofReal_inv, Complex.im_ofReal_mul, Complex.im_sum]
  rw [Finset.sum_eq_zero, mul_zero]
  intro s hs
  rw [Complex.im_ofReal_mul, h s hs, mul_zero]

end Aux

section Top

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {H : RegionHistory S n R k0 K} {m' : ℕ}

/-- The sites of a top Gaussian block are in `Z` and not in `Ω_{m'+1}` of the localization. -/
theorem gauss_top_site (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) (hmK : m' + 1 ≤ K) (hL : 2 ≤ S.L)
    (hR : ∀ j, 1 ≤ j → j < m' + 1 → S.Rb ≤ R j) {Z : H.Comp (m' + 1)}
    {y : BlockAt S n M K (m' + 1)} (hy : y ∈ gaussBlocks (H.localHistory M K (m' + 1) Z) m')
    {s : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1))}
    (hs : jBlock S.d S.L (M * n K) K (m' + 1) (torusCast (fine_eq_top hnn hmK).symm s) = y) :
    s ∈ H.locFine Z M (m' + 1) ∧ s ∉ (H.locGen Z M hmK hL hR).Ω (m' + 1) := by
  have hc : Z ∈ H.ancFin (m' + 1) (m' + 1) Z := by rw [ancFin_self]; exact Finset.mem_singleton_self _
  have hxy := blockCube_castSite hnn hmK (j := m' + 1) hmK s
  rw [hs] at hxy
  have := (gaussBlocks_iff_locGen (by omega) hmK (by omega) hL hR hc y s hxy.symm).mp hy
  refine ⟨?_, this.2⟩
  rw [mem_locFine_k hmK, ← hxy]
  exact this.1

theorem ut_eq (nd : (Σ s, BlockAt S n M K s) → Prop) {m' : ℕ} {V : Type*} [Zero V]
    (b : {b : Σ s, BlockAt S n M K s // nd b}) (y : BlockAt S n M K (m' + 1))
    (hb : b.1 = ⟨m' + 1, y⟩) (ft' : BlockAt S n M K (m' + 1) → V) :
    (fun b : {b : Σ s, BlockAt S n M K s // nd b} =>
      if h : b.1.1 = m' + 1 then ft' (h ▸ b.1.2) else (0 : V)) b = ft' y := by
  obtain ⟨⟨s0, y0⟩, hn⟩ := b
  obtain ⟨hs0, hy0⟩ := Sigma.mk.inj_iff.mp hb
  subst hs0
  have := eq_of_heq hy0
  subst this
  simp

end Top

end Balaban.LargeField
