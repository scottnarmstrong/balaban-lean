/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Background.TwoTorusAction
public import Balaban.LargeField.Background.TwoTorusLocBridge
public import Balaban.LargeField.Background.TwoTorusChiNew

/-!
# The main action of the new large-field region on two tori

`mainActionLoc_corr`: at corresponding configurations the main action `𝒜_{k+1}(Z'; ψ)`
(Definition II.5.4) of the quiet kernel agrees on two tori.
-/

@[expose] public section

namespace Balaban.RootFSpine

open Balaban Balaban.Multiscale Balaban.Background Balaban.LargeField RegionHistory

section LayersLevel

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {k : ℕ}

/-- **The layers of the level generating set of the history near `Zc`**, in terms of cubes. -/
theorem castHistGen_mem_near {N₀ : ℕ} [NeZero N₀] (Hl : RegionHistory S n R k0 K)
    (hrem : ∀ j, Hl.rem j = ∅) (hk : k + 1 ≤ K) (hL : 2 ≤ S.L)
    (hR : ∀ j, 1 ≤ j → j < k + 1 → S.Rb ≤ R j) (e : M * n (k + 1) = N₀)
    (Zc : Finset (Torus S.d (n (k + 1)))) (hZc : Zc ∈ comps (S.omega (k + 1)) (Hl.F.Zp (k + 1)))
    (hω : 2 * ⌊R k⌋₊ + S.L + 11 ≤ S.omega (k + 1)) {r : ℕ} (hr : r ≤ ⌊R k⌋₊ + 2)
    (x : Torus S.d (N₀ * S.L ^ (k + 1)))
    (hx : blockMap (S.L ^ (k + 1) * M) (n (k + 1)) x ∈ nbhd r (Zc : Set (Torus S.d (n (k + 1)))))
    (i : ℕ) :
    x ∈ (castGen e (Hl.histGen (M := M) (K' := k + 1) hk hrem hL hR)).Ω (i + 1) ↔
      i + 1 ≤ k + 1 ∧ (blockMap (S.L ^ (k + 1) * M) (n (k + 1)) x ∉ (Zc : Set (Torus S.d (n (k + 1)))) ∨
        blockMap (S.L ^ (i + 1) * M) (n (i + 1)) x ∈ (Hl.step i).Omega) := by
  rw [mem_castGen]
  have hc : ∀ j, cubeMap n S.L M (k + 1) j
      (torusCast (congrArg (· * S.L ^ (k + 1)) e.symm) x) = blockMap (S.L ^ j * M) (n j) x := by
    intro j
    show blockMap (S.L ^ j * M) (n j) (torusCast _ x) = _
    exact blockMap_torusCast _ _ _ _
  rw [histGen_mem_near Hl hrem (K' := k + 1) le_rfl hk hL hR Zc hZc hω hr _ (by
    obtain ⟨z, hz, hd⟩ := mem_nbhd.1 (show cubeMap n S.L M (k + 1) (k + 1)
      (torusCast (congrArg (· * S.L ^ (k + 1)) e.symm) x) ∈ _ by rw [hc]; exact hx)
    exact ⟨z, Finset.mem_coe.1 hz, hd⟩) i, hc, hc]
  exact Iff.rfl

omit [∀ (k : ℕ), NeZero (n k)] [NeZero M] [NeZero S.L] in
theorem level_size_eq (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) (hk : k + 1 ≤ K) {j : ℕ}
    (hj : j ≤ k + 1) {N₀ : ℕ} (e : M * n (k + 1) = N₀) :
    N₀ * S.L ^ (k + 1) = (S.L ^ j * M) * n j := by
  subst e
  have h1 := nn_eq_pow hnn j (k + 1 - j) (by omega)
  rw [show j + (k + 1 - j) = k + 1 by omega] at h1
  rw [h1, show S.L ^ (k + 1) = S.L ^ j * S.L ^ (k + 1 - j) by rw [← pow_add]; congr 1; omega]
  ring

theorem fine_level_eq (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) (hk : k + 1 ≤ K) :
    M * n (k + 1) * S.L ^ (k + 1) = M * n K * S.L ^ K := by
  have h := level_size_eq (S := S) (M := M) hnn hk (j := k + 1) le_rfl (N₀ := M * n (k + 1)) rfl
  rw [h]
  exact (Balaban.LargeField.fine_eq hnn hk).symm

end LayersLevel

end Balaban.RootFSpine
