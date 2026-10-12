/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.PsiZeroWindowBox
public import Balaban.LargeField.R.ZeroDomainD
public import Balaban.LargeField.R.PsiZeroTube
public import Balaban.LargeField.R.ChainSetting
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The geometry of `Z₀` inside the ripe window (Lemma III.3.2 (c), (d))

For the localization `𝔹_k` (`locGen`) of a ripe component `Z`, with `Z₀ = box b₀ w` the box of `k`-blocks
(`Zzero_eq_box`), in the type `Torus d (N₀ L^{k-k})` of the `k`-blocks used by `psiZero`:

* `exists_window_box`: `Z₀` as a box `box b₀ w` of `psiZero`'s block torus, `1 ≤ w_i ≤ D₀`, and `jBlock x ∈ Z₀ ↔ the
  k-block of x lies in Zzero`;
* `locFine_of_mem_box_shell`: every fine site in a block of `Z₀ ∪ shellOut Z₀` lies in `Z` (the fine set `Z_k`)
  (Lemma III.3.2 (d) and III.5.0 (b));
* `not_mem_box_of_top`: the blocks of `Ω_k ∩ Z` (terminal blocks) lie off `Z₀`;
* `not_mem_box_of_not_locFine`: a fine site off `Z` lies in a `k`-block off `Z₀`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale

theorem torusCast_blockMap_right {d ℓ m m' : ℕ} (h : m = m') (A : ℕ) (x : Torus d ℓ) :
    torusCast h (blockMap A m x) = blockMap A m' x := by
  subst h; rfl

theorem supDist_torusCast_eq {d m m' : ℕ} [NeZero m] [NeZero m'] (h : m = m') (x y : Torus d m) :
    supDist (torusCast h x) (torusCast h y) = supDist x y := by
  subst h; rfl

theorem mem_box_torusCast_iff {d m m' : ℕ} (h : m = m') (y a : Torus d m) (w : Fin d → ℕ) :
    torusCast h y ∈ box (torusCast h a) w ↔ y ∈ box a w := by
  subst h; exact Iff.rfl

namespace RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}
  (H : RegionHistory S n R k0 K) [NeZero S.L] [NeZero S.M] {k : ℕ}

include H in
theorem blockMap_blockMap_eq_cubeMap (x : Torus S.d (S.M * n k * S.L ^ k)) :
    blockMap S.M (n k) (blockMap (S.L ^ k) (S.M * n k) x) = cubeMap n S.L S.M k k x := by
  have := (blockMap_comp (d := S.d) (ℓ := S.M * n k * S.L ^ k) (N := S.L ^ k) (m₁ := S.M * n k)
    (m₂ := n k) (M := S.M) (by ring) rfl x)
  rw [this]
  rfl

/-- A fine site whose `k`-block is within sup-distance `1` of `Z₀` lies in the fine set `Z_k` of `Z`. -/
theorem mem_locFine_of_near_Zzero (hS : S.Ok) (h3 : 8 ≤ S.L * S.lateR k)
    (hR : ∀ j, R j = S.Rb * S.lam j ^ 2) (hkK : k ≤ K) (hk : 1 ≤ k) (Z : H.Comp k)
    {x : Torus S.d (S.M * n k * S.L ^ k)} {y0 : Torus S.d (S.M * n k)} (hy0 : y0 ∈ H.Zzero k Z)
    (hd : supDist (blockMap (S.L ^ k) (S.M * n k) x) y0 ≤ 1) :
    x ∈ H.locFine Z S.M k := by
  have hdd : cubeMap n S.L S.M k k x ∈ nbhd 3 (H.ZzeroDD k Z) := by
    rw [← H.blockMap_blockMap_eq_cubeMap]
    refine mem_nbhd.mpr ⟨blockMap S.M (n k) y0, H.Zzero_cube_mem hS hkK h3 Z hy0, ?_⟩
    have h1 := supDist_blockMap_le (d := S.d) (L := S.M) (m := n k) rfl
      (blockMap (S.L ^ k) (S.M * n k) x) y0
    have h2 : (supDist (blockMap (S.L ^ k) (S.M * n k) x) y0 + S.M - 1) / S.M ≤ 1 := by
      have hM : 0 < S.M := Nat.pos_of_ne_zero (NeZero.ne _)
      rw [Nat.div_le_iff_le_mul_add_pred hM]
      omega
    omega
  have := H.ZzeroDD_nbhd_margin hR hkK hk Z hdd
  exact (mem_locFine_k hkK).2 this.2.2

/-- A fine site in a `k`-block of `Z₀` lies in the fine set `Z_k`. -/
theorem mem_locFine_of_mem_Zzero (hS : S.Ok) (h3 : 8 ≤ S.L * S.lateR k)
    (hR : ∀ j, R j = S.Rb * S.lam j ^ 2) (hkK : k ≤ K) (hk : 1 ≤ k) (Z : H.Comp k)
    {x : Torus S.d (S.M * n k * S.L ^ k)} (hx : blockMap (S.L ^ k) (S.M * n k) x ∈ H.Zzero k Z) :
    x ∈ H.locFine Z S.M k :=
  H.mem_locFine_of_near_Zzero hS h3 hR hkK hk Z hx (by rw [supDist_self]; omega)

/-- A fine site of `Ω_k` (of the localization) has its `k`-block off `Z₀`. -/
theorem blockMap_not_mem_Zzero_of_top (hR : ∀ j, R j = S.Rb * S.lam j ^ 2) (hkK : k ≤ K) (hk : 1 ≤ k)
    (hL : 2 ≤ S.L) (hR' : ∀ j, 1 ≤ j → j < k → S.Rb ≤ R j) (Z : H.Comp k)
    {x : Torus S.d (S.M * n k * S.L ^ k)} (hx : x ∈ (H.locGen Z S.M hkK hL hR').Ω k) :
    blockMap (S.L ^ k) (S.M * n k) x ∉ H.Zzero k Z := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  intro hz
  have h1 := H.Zzero_not_mem_Omega_top hR hkK Z hz
  exact h1 ((mem_locGen_succ (hL := hL) (hR := hR') (Nat.lt_succ_self k')).1 hx)

include H in
/-- **`Z₀` as a box of `psiZero`'s block torus**: `Z₀ = box b₀ w` with `1 ≤ w_i ≤ D₀ = 3 c₀ + 4`, where a fine site
`x` has `jBlock x ∈ Z₀` iff its `k`-block lies in `Zzero`. -/
theorem exists_window_box (G : S.Good)
    (h18 : ∀ j, S.Rb * (S.lam j + S.θp + 1) ^ 2 + 1 ≤ 9 / 8 * (S.Rb * S.lam j ^ 2 - 1))
    (hR0 : 2 * S.c0 + 10 ≤ S.lateR 0) (hkK : k ≤ K) {Z : H.Comp k} (W : H.RipeWindow k Z)
    (hk0 : k ≤ k0) (hT : ∀ j, 1 ≤ j → j ≤ k0 → 4 * S.rho j + 21 ≤ n j) :
    ∃ (b0 : Torus S.d (S.M * n k * S.L ^ (k - k))) (w : Fin S.d → ℕ),
      (∀ i, 1 ≤ w i ∧ w i ≤ 3 * S.c0 + 4) ∧
      ∀ x : Torus S.d (S.M * n k * S.L ^ k),
        (jBlock S.d S.L (S.M * n k) k k x ∈ box b0 w ↔
          blockMap (S.L ^ k) (S.M * n k) x ∈ H.Zzero k Z) := by
  obtain ⟨b0, w, hw, hZ⟩ := H.Zzero_eq_box G h18 hR0 hkK W hk0 hT
  have hc : S.M * n k = S.M * n k * S.L ^ (k - k) := by simp
  refine ⟨torusCast hc b0, w, hw, fun x => ?_⟩
  have : jBlock S.d S.L (S.M * n k) k k x = torusCast hc (blockMap (S.L ^ k) (S.M * n k) x) := by
    unfold jBlock
    rw [torusCast_blockMap_right]
  rw [this, mem_box_torusCast_iff, hZ]

/-- Every fine site in a `k`-block of `Z₀ ∪ shellOut Z₀` lies in the fine set `Z_k` of `Z`
(Lemma III.3.2 (d), III.5.0 (b)). -/
theorem mem_locFine_of_mem_box_shell (hS : S.Ok) (h3 : 8 ≤ S.L * S.lateR k)
    (hR : ∀ j, R j = S.Rb * S.lam j ^ 2) (hkK : k ≤ K) (hk : 1 ≤ k) (Z : H.Comp k)
    {b0 : Torus S.d (S.M * n k * S.L ^ (k - k))} {w : Fin S.d → ℕ}
    (hbx : ∀ x : Torus S.d (S.M * n k * S.L ^ k),
      (jBlock S.d S.L (S.M * n k) k k x ∈ box b0 w ↔
        blockMap (S.L ^ k) (S.M * n k) x ∈ H.Zzero k Z))
    {x : Torus S.d (S.M * n k * S.L ^ k)}
    (hx : jBlock S.d S.L (S.M * n k) k k x ∈ box b0 w ∪ shellOut (box b0 w)) :
    x ∈ H.locFine Z S.M k := by
  have hc : S.M * n k = S.M * n k * S.L ^ (k - k) := by simp
  have hj : ∀ y : Torus S.d (S.M * n k * S.L ^ k),
      jBlock S.d S.L (S.M * n k) k k y = torusCast hc (blockMap (S.L ^ k) (S.M * n k) y) := by
    intro y; unfold jBlock; rw [torusCast_blockMap_right]
  rcases hx with hx | ⟨-, y0, hy0, hd⟩
  · exact H.mem_locFine_of_mem_Zzero hS h3 hR hkK hk Z ((hbx x).1 hx)
  · obtain ⟨x0, hx0⟩ := Balaban.exists_blockMap_eq (fine_eq_block S.L (S.M * n k) k)
      (pow_pos (Nat.pos_of_ne_zero (NeZero.ne S.L)) k) y0
    have hx0' : jBlock S.d S.L (S.M * n k) k k x0 = y0 := hx0
    rw [← hx0'] at hd
    have hz0 : blockMap (S.L ^ k) (S.M * n k) x0 ∈ H.Zzero k Z := (hbx x0).1 (hx0' ▸ hy0)
    refine H.mem_locFine_of_near_Zzero hS h3 hR hkK hk Z hz0 ?_
    rw [hj x, hj x0, supDist_torusCast_eq] at hd
    exact hd

end RegionHistory

end Balaban.LargeField
