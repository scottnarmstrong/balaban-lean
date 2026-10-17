/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.ZeroDomainSep
public import Balaban.LargeField.R.RopRestricted
public import Balaban.LargeField.R.RTransport
import Mathlib

/-!
# The geometric premises of the factorization of `R`, from the history (blocker 4)

For components `Zc c` of `Z_k` of a region history `H`, with the localized histories
`a c = H.localHistory S.M K k (Zc c)`, the region `X c = H.ripeX (Zc c)` and the box description
`hbx` of `Z₀`, the premises of `Rop_famDecompRestricted_factor` are consequences of the history:

* `Vblk_localHistory_iff`: the `k`-blocks of `V_c` are those whose cube lies in `U_k^∼ = bdryUnb H Z`;
* `hXV_ripeX`: `X c` lies over `V_c` (premise `hXV`);
* `zzero_cube_mem_comp`: the `π_k`-cube of a block of `Z₀(Z)` lies in `Z`;
* `hsepV_removed`: `V_c ∩ Z₀(c') = ∅` for `c ≠ c'` (premise `hsepV`);
* `hZ0_removed`: the blocks of `Z₀(c)` lie in `V_c` (premise `hZ0`, with `Z₀(c)` the set of blocks
  whose cast lies in `zb b0 w c`).

The only numerical input is the history's own radius bound `R_{k-1} ≤ R_base λ_{k-1}²` (`H.F.RH.le`),
used through `radius_lt_omega` (`⌊R_{k-1}⌋ + 5 < ω_k`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale

namespace RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}
  (H : RegionHistory S n R k0 K) [NeZero S.L] [NeZero S.M] {k : ℕ}

/-- The cubes of `𝕋_k` all of whose sites lie in the `k`-th record of the localized history of `Z` are the
cubes of `Z`. -/
theorem Zcubes_localHistory (hkK : k ≤ K) (Z : H.Comp k) (c : Torus S.d (n k)) :
    c ∈ Zcubes (H.localHistory S.M K k Z) k ↔ c ∈ (Z.1 : Set (Torus S.d (n k))) := by
  constructor
  · intro h
    obtain ⟨x, hx⟩ := cubeMap_surjective (M := S.M) H.F.hnn hkK c
    have h1 := (h x hx).2
    rw [← hx]; exact h1
  · intro h x hx
    refine ⟨?_, ?_⟩
    · show cubeMap n S.L S.M K k x ∈ ((H.locRH k Z).step k).Z
      rw [locRH_Z Z le_rfl hkK, lin_self]
      rw [hx]; exact h
    · show cubeMap n S.L S.M K k x ∈ (Z.1 : Set _)
      rw [hx]; exact h

/-- The cubes of `V_c = (Z^≈)^∼` of the localized history of `Z` are those of `U_k^∼ = bdryUnb H Z`. -/
theorem Vcubes_localHistory (hkK : k ≤ K) (Z : H.Comp k) :
    Vcubes R (H.localHistory S.M K k Z) k = bdryUnb H Z := by
  have h : Zcubes (H.localHistory S.M K k Z) k = (Z.1 : Set (Torus S.d (n k))) :=
    Set.ext fun c => H.Zcubes_localHistory hkK Z c
  unfold Vcubes bdryUnb bdryU
  rw [h]

/-- The `k`-blocks of `V_c` are those whose `π_k`-cube lies in `U_k^∼ = bdryUnb H Z`. -/
theorem mem_Vblk_localHistory (hkK : k ≤ K) (Z : H.Comp k) (y : BlockAt S n S.M K k) :
    y ∈ Vblk R (H.localHistory S.M K k Z) k ↔ blockMap S.M (n k) y ∈ bdryUnb H Z := by
  show blockCube S n S.M K k y ∈ Vcubes R (H.localHistory S.M K k Z) k ↔ _
  rw [H.Vcubes_localHistory hkK Z]
  rfl

/-- `bdryUnb H Z` is the `(⌊R_{k-1}⌋ + 2)`-neighbourhood of `Z`. -/
theorem bdryUnb_eq (Z : H.Comp k) :
    bdryUnb H Z = nbhd (⌊R (k - 1)⌋₊ + 2) (Z.1 : Set (Torus S.d (n k))) := by
  unfold bdryUnb bdryU thick
  rw [nbhd_nbhd]

/-- **Premise `hXV`**: the region `X = U_k^∼(Z)` (`ripeX`) lies over the volume `V` of the localized history:
for every `z ∈ X`, the block `torusCast hN z` lies in `Vblk R (H.localHistory S.M K k Z) k`. -/
theorem hXV_ripeX (hkK : k ≤ K) (Z : H.Comp k)
    (hN : S.M * n k * S.L ^ (k - k) = S.M * n K * S.L ^ (K - k)) :
    ∀ z ∈ H.ripeX Z, torusCast hN z ∈ Vblk R (H.localHistory S.M K k Z) k := by
  intro z hz
  rw [H.mem_Vblk_localHistory hkK Z, Balaban.LargeField.blockMap_torusCast hN S.M (n k) z, H.bdryUnb_eq]
  exact H.ripeX_cube_mem_nbhd Z hz

/-- The `π_k`-cube of a block of `Z₀(Z)` lies in `Z` itself. -/
theorem zzero_cube_mem_comp (hkK : k ≤ K) (Z : H.Comp k) {b : Torus S.d (S.M * n k)}
    (hb : b ∈ H.Zzero k Z) : blockMap S.M (n k) b ∈ (Z.1 : Set (Torus S.d (n k))) := by
  have hS := H.F.ok
  have h3 := H.eight_le_L_mul_lateR k
  refine H.cubesMeetingZ3_subset hS hkK h3 Z ?_
  obtain ⟨s, rfl, hs⟩ := hb
  refine ⟨s, (H.block_cube s).symm, ?_⟩
  have h23 := hS.kTwo_le_kThree h3
  have h3k := (hS.kThree_mem h3).1
  have := H.blockMap_pow_mem_lin hkK Z hs (S.kThree k) h23 h3k
  rw [H.cubeOf_comp h23 h3k hkK s] at this
  exact this

/-- A `k`-block of the box `Z₀ = box b0 w` (`hbx`: the box description of `Z₀(Z)` on the fine torus) has its
`π_k`-cube in `Z`. -/
theorem blockMap_mem_comp_of_box (hkK : k ≤ K) (Z : H.Comp k) (b0 : Torus S.d (S.M * n k * S.L ^ (k - k)))
    (w : Fin S.d → ℕ)
    (hbx : ∀ x : Torus S.d (S.M * n k * S.L ^ k),
      (jBlock S.d S.L (S.M * n k) k k x ∈ box b0 w ↔
        blockMap (S.L ^ k) (S.M * n k) x ∈ H.Zzero k Z))
    {y : Torus S.d (S.M * n k * S.L ^ (k - k))} (hy : y ∈ box b0 w) :
    blockMap S.M (n k) y ∈ (Z.1 : Set (Torus S.d (n k))) := by
  obtain ⟨x0, hx0⟩ := Balaban.exists_blockMap_eq (fine_eq_block S.L (S.M * n k) k)
    (pow_pos (Nat.pos_of_ne_zero (NeZero.ne S.L)) k) y
  have hx0' : jBlock S.d S.L (S.M * n k) k k x0 = y := hx0
  have hz := (hbx x0).1 (hx0' ▸ hy)
  have h2 := H.zzero_cube_mem_comp hkK Z hz
  rw [H.blockMap_blockMap_eq_cubeMap, ← H.cube_jBlock, hx0'] at h2
  exact h2

/-- **Premise `hsepV`**: for distinct components `c ≠ c'` of `Z_k`, `V_c ∩ Z₀(c') = ∅`: no block of `V_c`
lies in the box `zb c'`.  Needs only `1 ≤ k` and the history's radius bound `R_{k-1} ≤ R_base λ_{k-1}²`
(through `radius_lt_omega`: `⌊R_{k-1}⌋ + 5 < ω_k`). -/
theorem hsepV_removed (hkK : k ≤ K) (hk : 1 ≤ k) {ι : Type} (Zc : ι → H.Comp k)
    (hZc : Function.Injective Zc) (b0 : ι → Torus S.d (S.M * n k * S.L ^ (k - k))) (w : ι → Fin S.d → ℕ)
    (hbx : ∀ c, ∀ x : Torus S.d (S.M * n k * S.L ^ k),
      (jBlock S.d S.L (S.M * n k) k k x ∈ box (b0 c) (w c) ↔
        blockMap (S.L ^ k) (S.M * n k) x ∈ H.Zzero k (Zc c)))
    (hN : S.M * n k * S.L ^ (k - k) = S.M * n K * S.L ^ (K - k)) :
    ∀ c c' : ι, c ≠ c' → ∀ y ∈ Vblk R (H.localHistory S.M K k (Zc c)) k,
      torusCast hN.symm y ∉ zb (L := S.L) (N₀ := S.M * n k) (k := k) b0 w c' := by
  intro c c' hcc y hy hyz
  have hbox := mem_boxFinset.1 hyz
  have h2 := H.blockMap_mem_comp_of_box hkK (Zc c') (b0 c') (w c') (hbx c') hbox
  rw [Balaban.LargeField.blockMap_torusCast hN.symm S.M (n k) y] at h2
  have h1 := (H.mem_Vblk_localHistory hkK (Zc c) y).1 hy
  rw [H.bdryUnb_eq] at h1
  have h2' : blockMap S.M (n k) y ∈ nbhd 3 ((Zc c').1 : Set (Torus S.d (n k))) := subset_nbhd 3 _ h2
  have := H.omega_le_of_near (fun h => hcc (hZc h)) h1 h2'
  have := H.radius_lt_omega hk
  omega

/-- **Premise `hZ0`**: with `Z₀(c)` the set of `k`-blocks whose cast lies in the box `zb c`, the blocks of
`Z₀(c)` lie in `V_c`, so `(y ∈ V_c ∧ y ∈ Z₀(c)) ↔ torusCast hN.symm y ∈ zb c`.  No radius condition. -/
theorem hZ0_removed (hkK : k ≤ K) (Z : H.Comp k) (b0 : Torus S.d (S.M * n k * S.L ^ (k - k)))
    (w : Fin S.d → ℕ)
    (hbx : ∀ x : Torus S.d (S.M * n k * S.L ^ k),
      (jBlock S.d S.L (S.M * n k) k k x ∈ box b0 w ↔
        blockMap (S.L ^ k) (S.M * n k) x ∈ H.Zzero k Z))
    (hN : S.M * n k * S.L ^ (k - k) = S.M * n K * S.L ^ (K - k)) (y : BlockAt S n S.M K k) :
    (y ∈ Vblk R (H.localHistory S.M K k Z) k ∧
        y ∈ {y : BlockAt S n S.M K k | torusCast hN.symm y ∈
          boxFinset (L := S.L) (N₀ := S.M * n k) (k := k) b0 w}) ↔
      torusCast hN.symm y ∈ boxFinset (L := S.L) (N₀ := S.M * n k) (k := k) b0 w := by
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  have h2 := H.blockMap_mem_comp_of_box hkK Z b0 w hbx (mem_boxFinset.1 h)
  rw [Balaban.LargeField.blockMap_torusCast hN.symm S.M (n k) y] at h2
  rw [H.mem_Vblk_localHistory hkK Z, H.bdryUnb_eq]
  exact subset_nbhd _ _ h2

end RegionHistory

end Balaban.LargeField
