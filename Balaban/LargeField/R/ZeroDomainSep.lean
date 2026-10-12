/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.PsiZeroWindowGeom
public import Balaban.LargeField.R.PsiZeroWindowRipe
public import Balaban.LargeField.R.WindowOfHistory
public import Balaban.LargeField.R.ZeroDomainB
public import Balaban.LargeField.History.Core
import Mathlib.Tactic.Linarith

/-!
# Separation of the zero-domains from the windows of other components (Lemma III.5.0 (a), III.3.2 (c))

For a history `H` and components `Z ≠ Z'` of `Z_k` (`k ≥ 1`):

* `ripeX H Z` is the region `X` read by the reference density of `Z`: the `k`-blocks meeting the fine set of
  `U_k^∼ = bdryUnb H Z` (the `Unb` of `windowOfHistory`, the set `blocksMeeting Unb` of `psiZeroSpec_ripe_of_input`);
* `Zzero_cube_mem_nbhd_comp`: the `π_k`-cube of a block of `Z₀(Z')` lies in `nbhd 3 Z'` (`Z₀ ⊆ Z''₀ ⊆ Z'^{∼3}`);
* `ripeX_cube_mem_nbhd`: the `π_k`-cube of a block of `X(Z)` lies in `nbhd (⌊R_{k-1}⌋ + 2) Z`;
* `core_sep` gives `ω_k ≤ dist(Z, Z')`, and `⌊R_{k-1}⌋ + 2 + 3 < ω_k = 2⌊R_base λ_{k-1}²⌋ + L + 11` (from the
  radius hypothesis `R_{k-1} ≤ R_base λ_{k-1}²`), so `X(Z)` is disjoint from `Z₀(Z')`: `zeroDomain_hsep`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale

namespace RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}
  (H : RegionHistory S n R k0 K) [NeZero S.L] [NeZero S.M] {k : ℕ}

/-- The region `X = U_k^∼(Z)` read by the reference density of `Z`, as `k`-blocks: the `k`-blocks of the fine
set of `bdryUnb H Z`. -/
def ripeX (Z : H.Comp k) : Set (Torus S.d (S.M * n k * S.L ^ (k - k))) :=
  blocksMeeting (k := k) (N₀ := S.M * n k)
    ((fineFin (k := k) (M := S.M) k (bdryUnb H Z) : Finset _) : Set (Torus S.d (S.M * n k * S.L ^ k)))

include H in
theorem cube_jBlock (x : Torus S.d (S.M * n k * S.L ^ k)) :
    blockMap S.M (n k) (jBlock S.d S.L (S.M * n k) k k x) = cubeMap n S.L S.M k k x := by
  have hc : S.M * n k = S.M * n k * S.L ^ (k - k) := by simp
  have : jBlock S.d S.L (S.M * n k) k k x = torusCast hc (blockMap (S.L ^ k) (S.M * n k) x) := by
    unfold jBlock
    rw [torusCast_blockMap_right]
  rw [this, blockMap_torusCast hc rfl, H.blockMap_blockMap_eq_cubeMap]

/-- **T1 (i)**: `cubesMeetingZ3 ⊆ Z'` (the `π_k`-cubes meeting `Z'_{k₃}` lie in `Z'_k`). -/
theorem cubesMeetingZ3_subset (hS : S.Ok) (hkK : k ≤ K) (h3 : 8 ≤ S.L * S.lateR k) (Z : H.Comp k) :
    H.cubesMeetingZ3 k Z ⊆ Z.1 := by
  rintro c ⟨s, rfl, hs⟩
  have h3k := (hS.kThree_mem h3).1
  have := H.blockMap_pow_mem_lin hkK Z hs k h3k le_rfl
  rw [H.cubeOf_comp h3k le_rfl hkK s] at this
  simpa [H.lin_self] using this

/-- **T1 (i)**: `Z₀(Z') ⊆ Z''₀(Z') ⊆ nbhd 3 Z'`: the `π_k`-cube of a block of `Z₀` is within distance `3` of `Z'`
(Lemma III.3.2 (c), Definition III.3.1). -/
theorem Zzero_cube_mem_nbhd_comp (hS : S.Ok) (hkK : k ≤ K) (h3 : 8 ≤ S.L * S.lateR k) (Z : H.Comp k)
    {b : Torus S.d (S.M * n k)} (hb : b ∈ H.Zzero k Z) :
    blockMap S.M (n k) b ∈ nbhd 3 (Z.1 : Set (Torus S.d (n k))) :=
  nbhd_mono le_rfl (H.cubesMeetingZ3_subset hS hkK h3 Z) (H.Zzero_cube_mem hS hkK h3 Z hb)

/-- **T1 (ii)**: the `π_k`-cube of a block of `X(Z)` lies within `⌊R_{k-1}⌋ + 2` of `Z`
(`bdryUnb = nbhd 1 (nbhd (⌊R_{k-1}⌋+1) Z)`). -/
theorem ripeX_cube_mem_nbhd (Z : H.Comp k) {y : Torus S.d (S.M * n k * S.L ^ (k - k))}
    (hy : y ∈ H.ripeX Z) :
    blockMap S.M (n k) y ∈ nbhd (⌊R (k - 1)⌋₊ + 2) (Z.1 : Set (Torus S.d (n k))) := by
  obtain ⟨x, hx, rfl⟩ := hy
  have hx' : cubeMap n S.L S.M k k x ∈ bdryUnb H Z := (mem_fineFin).1 (by exact_mod_cast hx)
  rw [H.cube_jBlock]
  have : bdryUnb H Z = nbhd (⌊R (k - 1)⌋₊ + 2) (Z.1 : Set (Torus S.d (n k))) := by
    unfold bdryUnb bdryU thick
    rw [nbhd_nbhd]
  rwa [this] at hx'

/-- **T2**: a cube within `r` of `Z` and within `3` of a different component `Z'` forces `ω_k ≤ r + 3`. -/
theorem omega_le_of_near {Z Z' : H.Comp k} (hne : (Z : H.Comp k) ≠ Z') {c : Torus S.d (n k)} {r : ℕ}
    (h1 : c ∈ nbhd r (Z.1 : Set (Torus S.d (n k)))) (h2 : c ∈ nbhd 3 (Z'.1 : Set (Torus S.d (n k)))) :
    S.omega k ≤ r + 3 := by
  obtain ⟨z, hz, hd1⟩ := mem_nbhd.1 h1
  obtain ⟨z', hz', hd2⟩ := mem_nbhd.1 h2
  have := H.core_sep hne hz hz'
  have h := supDist_triangle z c z'
  rw [supDist_comm z c] at h
  omega

include H in
/-- The numerical condition: `⌊R_{k-1}⌋ + 2 + 3 < ω_k` (radius hypothesis `R_{k-1} ≤ R_base λ_{k-1}²`). -/
theorem radius_lt_omega (hk : 1 ≤ k) : ⌊R (k - 1)⌋₊ + 2 + 3 < S.omega k := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have h := Setting.omega_eq_omegaW S (j + 1)
  rw [h, omegaW_succ]
  have : ⌊R (j + 1 - 1)⌋₊ ≤ ⌊S.Rb * S.lam j ^ 2⌋₊ := by
    simpa using Nat.floor_le_floor (H.F.RH.le j)
  omega

/-- **T3** (`hsep` of `RopConcrete`): for a family of components of `Z_k`, indexed injectively by `Zc`, with
`Z₀(Zc c) = box (b0 c) (w c)`, the region `X(Zc c)` is disjoint from the zero-domain box of every other
component. -/
theorem zeroDomain_hsep (hkK : k ≤ K) (hk : 1 ≤ k) {ι : Type} (Zc : ι → H.Comp k)
    (hZc : Function.Injective Zc) (b0 : ι → Torus S.d (S.M * n k * S.L ^ (k - k))) (w : ι → Fin S.d → ℕ)
    (hbx : ∀ c, ∀ x : Torus S.d (S.M * n k * S.L ^ k),
      (jBlock S.d S.L (S.M * n k) k k x ∈ box (b0 c) (w c) ↔
        blockMap (S.L ^ k) (S.M * n k) x ∈ H.Zzero k (Zc c))) :
    ∀ c c', c ≠ c' → Disjoint (H.ripeX (Zc c)) (box (b0 c') (w c')) := by
  intro c c' hcc
  rw [Set.disjoint_left]
  intro y hyX hyB
  have hS := H.F.ok
  have h3 := H.eight_le_L_mul_lateR k
  obtain ⟨x0, hx0⟩ := Balaban.exists_blockMap_eq (fine_eq_block S.L (S.M * n k) k)
    (pow_pos (Nat.pos_of_ne_zero (NeZero.ne S.L)) k) y
  have hx0' : jBlock S.d S.L (S.M * n k) k k x0 = y := hx0
  have hz : blockMap (S.L ^ k) (S.M * n k) x0 ∈ H.Zzero k (Zc c') :=
    (hbx c' x0).1 (hx0' ▸ hyB)
  have h2 := H.Zzero_cube_mem_nbhd_comp hS hkK h3 (Zc c') hz
  rw [H.blockMap_blockMap_eq_cubeMap, ← H.cube_jBlock, hx0'] at h2
  have h1 := H.ripeX_cube_mem_nbhd (Zc c) hyX
  have := H.omega_le_of_near (fun h => hcc (hZc h)) h1 h2
  have := H.radius_lt_omega hk
  omega

end RegionHistory

end Balaban.LargeField
