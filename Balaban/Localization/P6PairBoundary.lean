/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.P6PairHalo
public import Balaban.Fluctuation.Theorem42RealFlow
import Mathlib.Tactic.Linarith

/-!
# The P6 mixed pair: the domains of the boundary set and the layer comparison (VMOD-11 (1.5)-(1.7))

`H⁻ = p6Hold` (`𝔹_k(W_k)` at depth `K = k + 1`), `H^∂ = genBoundary` (P6's boundary generating set
`G^∂_{k+1}`, Definition II.2.4 (iv)), `F♯ = p6Fsharp`.

* `p6_boundary_domains` : (1.6): the layers of `H^∂`;
* `p6_omega_subset_halo`: Lemma I.3.5 (f) in the form `Ω_{k+1} ⊆ A` (as fine sets);
* `p6_boundary_embedded`: `H^∂ ≺ F♯` layer by layer, hence `Ω₁(H^∂) ⊆ Ω₁(F♯)` (1.7);
* `p6_layer_le`: `n_{H^∂}(x) ≤ n_{F♯}(x)` (1.7);
* `p6_old_embedded`, `p6_old_layer`: (1.5): `Ω₁(H⁻) = Ω₁(F♯)` and `n_{H⁻} = min(n_{F♯}, k)`.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Localization

set_option linter.unusedSectionVars false

variable {d M1 c n1 L k n0 : ℕ} [NeZero L] [NeZero M1] [NeZero c] [NeZero n0] [NeZero n1]
  {Rprev Rk : ℝ} {Zp : Set (Torus d n1)} (st : RegionStep d L n0 n1 Rprev Rk)

/-- **Lemma I.3.5 (f)** for the halo: the fine set of `Ω_{k+1}` lies in `A`
(`Ω_{k+1} ⊆ Z_kᶜ ⊆ Z^≈ ⊆ A`). -/
theorem p6_omega_subset_halo (hn : n0 = L * n1) (hL : 0 < L) :
    fineK1 M1 c n1 L k st.Omega ⊆ p6Halo M1 c n1 L k ⌊Rprev⌋₊ st.Z := by
  intro x hx
  rw [mem_fineK1] at hx
  rw [mem_p6Halo]
  have h1 := blockMap_k_succ (M1 := M1) (c := c) (L := L) (k := k) hn x
  have hmem : blockMap (L ^ k * (c * M1)) n0 x ∈ (st.Z)ᶜ :=
    st.not_mem_Z_of_mem_Omega hL hn (by rw [h1]; exact hx)
  refine subset_nbhd 1 _ ⟨blockMap (L ^ k * (c * M1)) n0 x,
    subset_nbhd _ _ hmem, h1⟩

variable (M1 c n1 L k) in
/-- `H^∂` is the boundary family `G^∂_{k+1}`; `U_{k+1} = (Z^pre_{k+1})^≈` and `Ω_{k+1}` as fine
sets. -/
theorem p6_boundary_domains (hc : 14 ≤ c) (hn : n0 = L * n1) (hL : 2 ≤ L)
    (hρ : 3 * L ≤ ⌊Rprev⌋₊) (hZ : st.Omegaᶜ ⊆ Zp) :
    (∀ n, n ≤ k → (genBoundary M1 c n1 L k st hc hn hL hρ hZ).Ω n =
      ((p6Hold M1 c n1 L k ⌊Rprev⌋₊ st.Z).Ω n \ fineK1 M1 c n1 L k st.Omega) ∪
        (minLayer M1 (c * n1) L (k + 1) (k + 1) (stepU M1 c n1 L k ⌊Rk⌋₊ Zp) n ∩
          fineK1 M1 c n1 L k st.Omega)) ∧
    (genBoundary M1 c n1 L k st hc hn hL hρ hZ).Ω (k + 1) =
      stepU M1 c n1 L k ⌊Rk⌋₊ Zp ∩ fineK1 M1 c n1 L k st.Omega := by
  refine ⟨fun n _ => rfl, ?_⟩
  unfold genBoundary
  rw [boundaryGenSet_Ω]
  unfold boundaryLayer
  have hU : cubeInterior M1 (c * n1) L (k + 1) (k + 1) (stepU M1 c n1 L k ⌊Rk⌋₊ Zp) =
      stepU M1 c n1 L k ⌊Rk⌋₊ Zp :=
    (isCubeUnion_fineK1 (M1 := M1) (c := c) (n1 := n1) (L := L) (k := k) _).cubeInterior_eq
  rw [minLayer_of_gt _ (Nat.lt_succ_self k), minLayer_self, hU]
  simp

/-- **`p6_boundary_embedded`** (VMOD-11 (1.7)): `H^∂ ≺ F♯`, layer by layer. -/
theorem p6_boundary_embedded (hc : 14 ≤ c) (hn : n0 = L * n1) (hL : 2 ≤ L)
    (hρ : 3 * L ≤ ⌊Rprev⌋₊) (hZ : st.Omegaᶜ ⊆ Zp) :
    Background.Precedes (genBoundary M1 c n1 L k st hc hn hL hρ hZ)
      (p6Fsharp (M1 := M1) (c := c) (L := L) (k := k) hn hρ (by omega) st.Z) := by
  intro i hi1 hik x hx
  have hOm : x ∈ fineK1 M1 c n1 L k st.Omega →
      x ∈ (p6Fsharp (M1 := M1) (c := c) (L := L) (k := k) hn hρ (by omega) st.Z).Ω i := by
    intro h
    have hA : x ∈ (p6Fsharp (M1 := M1) (c := c) (L := L) (k := k) hn hρ (by omega) st.Z).Ω
        (k + 1) := by
      rw [p6Fsharp_Ω_top]; exact p6_omega_subset_halo st hn (by omega) h
    exact (p6Fsharp (M1 := M1) (c := c) (L := L) (k := k) hn hρ (by omega) st.Z).Ω_antitone
      hi1 hik (by omega) hA
  by_cases hik' : i ≤ k
  · obtain ⟨hd, -⟩ := p6_boundary_domains M1 c n1 L k st hc hn hL hρ hZ
    rw [hd i hik'] at hx
    rcases Finset.mem_union.1 hx with h | h
    · rw [p6Fsharp_Ω_of_le hn hρ _ st.Z hik']
      exact (Finset.mem_sdiff.1 h).1
    · exact hOm (Finset.mem_inter.1 h).2
  · have hi : i = k + 1 := by omega
    subst hi
    obtain ⟨-, hd⟩ := p6_boundary_domains M1 c n1 L k st hc hn hL hρ hZ
    rw [hd] at hx
    exact hOm (Finset.mem_inter.1 hx).2

/-- `Ω₁(H^∂) ⊆ Ω₁(F♯)` (VMOD-11 (1.7)). -/
theorem p6_boundary_Ω1_subset (hc : 14 ≤ c) (hn : n0 = L * n1) (hL : 2 ≤ L)
    (hρ : 3 * L ≤ ⌊Rprev⌋₊) (hZ : st.Omegaᶜ ⊆ Zp) :
    (genBoundary M1 c n1 L k st hc hn hL hρ hZ).Ω 1 ⊆
      (p6Fsharp (M1 := M1) (c := c) (L := L) (k := k) hn hρ (by omega) st.Z).Ω 1 :=
  fun _ hx => (p6_boundary_embedded st hc hn hL hρ hZ).mem_Ω1 hx

/-- **`p6_layer_le`** (VMOD-11 (1.7)): `n_{H^∂}(x) ≤ n_{F♯}(x)` on `Ω₁(H^∂)`. -/
theorem p6_layer_le (hc : 14 ≤ c) (hn : n0 = L * n1) (hL : 2 ≤ L)
    (hρ : 3 * L ≤ ⌊Rprev⌋₊) (hZ : st.Omegaᶜ ⊆ Zp)
    {x : Torus d (M1 * (c * n1) * L ^ (k + 1))}
    (hx : x ∈ (genBoundary M1 c n1 L k st hc hn hL hρ hZ).Ω 1) :
    (genBoundary M1 c n1 L k st hc hn hL hρ hZ).layerIndex x ≤
      (p6Fsharp (M1 := M1) (c := c) (L := L) (k := k) hn hρ (by omega) st.Z).layerIndex x :=
  (p6_boundary_embedded st hc hn hL hρ hZ).layerIndex_le hx

/-! ### The old operator -/

/-- `H⁻ ≺ F♯`. -/
theorem p6_old_precedes (hn : n0 = L * n1) {ρ' : ℕ} (hρ : 3 * L ≤ ρ') (hc : 5 ≤ c)
    (Z : Set (Torus d n0)) :
    Background.Precedes (p6Hold M1 c n1 L k ρ' Z)
      (p6Fsharp (M1 := M1) (c := c) (L := L) (k := k) hn hρ hc Z) := by
  intro i hi1 hik x hx
  by_cases hik' : i ≤ k
  · rwa [p6Fsharp_Ω_of_le hn hρ hc Z hik']
  · have hi : i = k + 1 := by omega
    subst hi
    rw [p6Hold_Ω_top] at hx
    exact absurd hx (Finset.notMem_empty _)

/-- **(1.5)**, domain: for `k ≥ 1`, `Ω₁(H⁻) = Ω₁(F♯)`. -/
theorem p6_old_Ω1 (hn : n0 = L * n1) {ρ' : ℕ} (hρ : 3 * L ≤ ρ') (hc : 5 ≤ c)
    (Z : Set (Torus d n0)) (hk : 1 ≤ k) :
    (p6Hold M1 c n1 L k ρ' Z).Ω 1 =
      (p6Fsharp (M1 := M1) (c := c) (L := L) (k := k) hn hρ hc Z).Ω 1 :=
  (p6Fsharp_Ω_of_le hn hρ hc Z hk).symm

/-- **(1.5)**, layers: for `k ≥ 1` and `x ∈ Ω₁(F♯)`, `n_{H⁻}(x) = min(n_{F♯}(x), k)`. -/
theorem p6_old_layer (hn : n0 = L * n1) {ρ' : ℕ} (hρ : 3 * L ≤ ρ') (hc : 5 ≤ c)
    (Z : Set (Torus d n0)) (hk : 1 ≤ k)
    {x : Torus d (M1 * (c * n1) * L ^ (k + 1))}
    (hx : x ∈ (p6Fsharp (M1 := M1) (c := c) (L := L) (k := k) hn hρ hc Z).Ω 1) :
    (p6Hold M1 c n1 L k ρ' Z).layerIndex x =
      min ((p6Fsharp (M1 := M1) (c := c) (L := L) (k := k) hn hρ hc Z).layerIndex x) k := by
  set F := p6Fsharp (M1 := M1) (c := c) (L := L) (k := k) hn hρ hc Z with hF
  obtain ⟨hn1, hnK, hxl⟩ := F.layerIndex_spec hx
  rw [GeneratingSet.mem_layer] at hxl
  by_cases hnk : F.layerIndex x ≤ k
  · rw [min_eq_left hnk]
    refine (p6Hold M1 c n1 L k ρ' Z).layerIndex_eq hn1 (by omega) ?_
    rw [GeneratingSet.mem_layer]
    refine ⟨?_, ?_⟩
    · rw [← p6Fsharp_Ω_of_le hn hρ hc Z hnk]; exact hxl.1
    · by_cases hs : F.layerIndex x + 1 ≤ k
      · rw [← p6Fsharp_Ω_of_le hn hρ hc Z hs]; exact hxl.2
      · have : F.layerIndex x + 1 = k + 1 := by omega
        rw [this, p6Hold_Ω_top]; exact Finset.notMem_empty _
  · have hkn : F.layerIndex x = k + 1 := by omega
    rw [hkn, min_eq_right (by omega)]
    refine (p6Hold M1 c n1 L k ρ' Z).layerIndex_eq hk (Nat.le_succ k) ?_
    rw [GeneratingSet.mem_layer]
    refine ⟨?_, ?_⟩
    · rw [p6Hold_Ω_k hn]
      have := hxl.1
      rw [hkn, p6Fsharp_Ω_top] at this
      exact p6_halo_subset_W hn (by omega) Z this
    · rw [p6Hold_Ω_top]; exact Finset.notMem_empty _

end Balaban.LargeField
