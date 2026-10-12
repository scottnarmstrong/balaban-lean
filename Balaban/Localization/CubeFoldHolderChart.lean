/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.CubeFoldGeometry
public import Balaban.Localization.DecoupledCubeHolder

/-!
# The four-point chart identity of the mixed-wall Hölder estimate (VMOD-10 (3.2))

`cubeFoldPt_eq_of_chart`: the local fold `P` of a cube is the identity in the chart of the centre.
`cubeFold_chart_pair`: `P(0) = x`, `P(e_μ) = x + e_μ`, `P(z) = x'`, `P(z + e_μ) = x' + e_μ` when
`x, x', x + e_μ, x' + e_μ` lie in the cube and `z` is the displacement of `x'` from `x` with
`‖z‖ < B`, `S + B ≤ T` (`chart_z`).
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.Reflection Balaban.LatticeGreen Finset

/-- One coordinate of the chart identity. -/
theorem fold1_chart {ℓ S c : ℕ} [NeZero ℓ] [NeZero S] (hSℓ : S < ℓ) (p : ZMod (2 * S))
    (hp : p.val < S) {y : ZMod ℓ} (hy : InCube1 ℓ S c y) {w : ℤ}
    (hw : w = (((y - (c : ZMod ℓ)).val : ℕ) : ℤ) -
      (((fold1 ℓ S c (2 * S) p - (c : ZMod ℓ)).val : ℕ) : ℤ)) :
    fold1 ℓ S c (2 * S) (p + (w : ZMod (2 * S))) = y := by
  obtain ⟨t, ht, hyt⟩ := hy
  have h1 : fold1 ℓ S c (2 * S) p - (c : ZMod ℓ) = ((p.val : ℕ) : ZMod ℓ) := by
    rw [fold1_eq]
    simp only [foldNat, hp, ↓reduceIte]
    push_cast
    ring
  have h2 : y - (c : ZMod ℓ) = ((t : ℕ) : ZMod ℓ) := by
    rw [hyt]; push_cast; ring
  rw [h1, h2, ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega)] at hw
  have h3 : p + (w : ZMod (2 * S)) = ((t : ℕ) : ZMod (2 * S)) := by
    rw [hw]
    push_cast
    rw [ZMod.natCast_zmod_val]
    ring
  rw [h3, fold1_eq, ZMod.val_natCast_of_lt (by omega)]
  simp only [foldNat, ht, ↓reduceIte]
  exact hyt.symm

variable {d N₀ L k : ℕ} [NeZero N₀] [NeZero L]

/-- **The local fold is the identity on the cube in the chart of the centre**: if `p₀` is a
lower-half preimage of `x` and `w` is the chart difference of `y` and `x`, then `P(w) = y`. -/
theorem cubeFoldPt_eq_of_chart (S : ℕ) [NeZero S] (c : Fin d → ℕ) (p0 : Torus d (2 * S))
    (hSℓ : S < N₀ * L ^ k) (hlow : ∀ i, (p0 i).val < S) {x y : Torus d (N₀ * L ^ k)}
    (hp0 : foldMap (N₀ * L ^ k) S (2 * S) c p0 = x) (hy : y ∈ cubeSet (N₀ * L ^ k) S c)
    {w : Fin d → ℤ}
    (hw : ∀ i, w i = (((y i - (c i : ZMod (N₀ * L ^ k))).val : ℕ) : ℤ) -
      (((x i - (c i : ZMod (N₀ * L ^ k))).val : ℕ) : ℤ)) :
    cubeFoldPt N₀ L k S c p0 w = y := by
  funext i
  have h := fold1_chart (c := c i) hSℓ (p0 i) (hlow i) ((mem_cubeSet.1 hy) i)
    (w := w i) (by rw [hw i, ← hp0]; rfl)
  exact h

/-- **VMOD-10 (3.2).** The four values of (1.4) are the folded values at `0`, `e_μ`, `z`, `z + e_μ`. -/
theorem cubeFold_chart_pair (S : ℕ) [NeZero S] (c : Fin d → ℕ) (p0 : Torus d (2 * S))
    {B : ℕ} (hB : 2 ≤ B) (hSB : S + B ≤ N₀ * L ^ k) (hlow : ∀ i, (p0 i).val < S)
    {x x' : Torus d (N₀ * L ^ k)} (hp0 : foldMap (N₀ * L ^ k) S (2 * S) c p0 = x)
    (hx : x ∈ cubeSet (N₀ * L ^ k) S c) (hx' : x' ∈ cubeSet (N₀ * L ^ k) S c) {μ : Fin d}
    (hxe : x + Pi.single μ 1 ∈ cubeSet (N₀ * L ^ k) S c)
    (hx'e : x' + Pi.single μ 1 ∈ cubeSet (N₀ * L ^ k) S c) {z : Fin d → ℤ}
    (hxz : x' = x + intTorus z) (hz : ‖z‖ < B) :
    cubeFoldPt N₀ L k S c p0 0 = x ∧ cubeFoldPt N₀ L k S c p0 (Pi.single μ 1) = x + Pi.single μ 1 ∧
      cubeFoldPt N₀ L k S c p0 z = x' ∧
      cubeFoldPt N₀ L k S c p0 (z + Pi.single μ 1) = x' + Pi.single μ 1 := by
  have hSℓ : S < N₀ * L ^ k := by omega
  have hmem : ∀ y, y ∈ cubeSet (N₀ * L ^ k) S c → ∀ i, InCube1 (N₀ * L ^ k) S (c i) (y i) :=
    fun y hy => mem_cubeSet.1 hy
  have hnorm1 : ‖(Pi.single μ 1 : Fin d → ℤ)‖ < B := by
    have : ‖(Pi.single μ 1 : Fin d → ℤ)‖ ≤ 1 := by
      rw [pi_norm_le_iff_of_nonneg zero_le_one]
      intro i
      by_cases hi : i = μ
      · subst hi; simp
      · simp [hi]
    have hB' : (2 : ℝ) ≤ B := by exact_mod_cast hB
    linarith
  have hxe' : x + Pi.single μ 1 = x + intTorus (Pi.single μ 1 : Fin d → ℤ) := by
    funext i
    by_cases hi : i = μ
    · subst hi; simp [intTorus_apply]
    · simp [intTorus_apply, hi]
  have hx'e' : x' + Pi.single μ 1 = (x + Pi.single μ 1) + intTorus z := by
    rw [hxz]; abel
  have c1 := chart_z c (hmem x hx) (hmem x' hx') hxz hz hSB
  have c2 := chart_z c (hmem x hx) (hmem _ hxe) hxe' hnorm1 hSB
  have c3 := chart_z c (hmem _ hxe) (hmem _ hx'e) hx'e' hz hSB
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [cubeFoldPt_zero, hp0]
  · refine cubeFoldPt_eq_of_chart S c p0 hSℓ hlow hp0 hxe fun i => ?_
    exact c2 i
  · exact cubeFoldPt_eq_of_chart S c p0 hSℓ hlow hp0 hx' c1
  · refine cubeFoldPt_eq_of_chart S c p0 hSℓ hlow hp0 hx'e fun i => ?_
    have := c2 i
    have := c3 i
    have e : (z + (Pi.single μ 1 : Fin d → ℤ)) i = z i + (Pi.single μ 1 : Fin d → ℤ) i := rfl
    rw [e]
    omega

end Balaban.Localization
