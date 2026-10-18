/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Background.TwoTorusPb

/-!
# Locality of the region `Z_k` and of `Ω_{k+1}` near a component

For a component `Z'` of `Z^pre_{k+1}` (width `ω`) and a site whose `π_{k+1}`-cube lies within
`D < ω` of `Z'`:
* a site of `Z_k` lies in `Z'` (`mem_of_mem_Zk_near`): its `π_{k+1}`-cube is not in `Ω_{k+1}`
  (Lemma I.3.5 (f)), so lies in `Z^pre_{k+1}` and is `ω`-close to `Z'`;
* a site outside `Z'` lies in `Ω_{k+1}` (`mem_Omega_of_not_mem_near`).

So, near `Z'`, the global sets `Z_k`, `Ω_{k+1}` are determined by `Z'`, `Z_k ∩ Z'`, `Ω_{k+1} ∩ Z'`.
-/

@[expose] public section

namespace Balaban.RootFSpine

open Balaban Balaban.Multiscale Balaban.LargeField

set_option linter.unusedSectionVars false

section Local

variable {d M1 c n1 L k n0 : ℕ} [NeZero L] [NeZero M1] [NeZero c] [NeZero n0] [NeZero n1]
  {Rprev Rk : ℝ} {ω : ℕ} {Zp : Set (Torus d n1)} {Z' : Finset (Torus d n1)}

/-- A site `z` whose `π_{k+1}`-cube is within `D` of a cube of `Z'` (integer lift form). -/
theorem exists_close_of_dil {D : ℕ} {z : Fin d → ℤ}
    (hz : z ∈ dilZ (L ^ (k + 1) * (c * M1)) D
      (pbZ (M1 * (c * n1) * L ^ (k + 1))
        ((fineK1 M1 c n1 L k (Z' : Set (Torus d n1)) : Finset _) :
          Set (Torus d (M1 * (c * n1) * L ^ (k + 1)))))) :
    ∃ z' ∈ Z', supDist (blockMap (L ^ (k + 1) * (c * M1)) n1
        (zcast (M1 * (c * n1) * L ^ (k + 1)) z)) z' ≤ D := by
  obtain ⟨s, hs, hmem⟩ := hz
  have hmem' : zcast (M1 * (c * n1) * L ^ (k + 1)) (z + shiftZ (L ^ (k + 1) * (c * M1)) s) ∈
      (fineK1 M1 c n1 L k (Z' : Set (Torus d n1)) : Set _) := hmem
  rw [Finset.mem_coe, mem_fineK1, blockMap_zcast fine_eq_P1 P1_pos] at hmem'
  have hP' : ((L ^ (k + 1) * (c * M1) : ℕ) : ℤ) ≠ 0 := by exact_mod_cast P1_pos.ne'
  have e1 : (fun μ => (z + shiftZ (L ^ (k + 1) * (c * M1)) s) μ / ((L ^ (k + 1) * (c * M1) : ℕ) : ℤ)) =
      (fun μ => z μ / ((L ^ (k + 1) * (c * M1) : ℕ) : ℤ)) + s := by
    funext μ
    simp only [Pi.add_apply, shiftZ]
    rw [Int.add_mul_ediv_left _ _ hP']
  rw [e1] at hmem'
  refine ⟨_, Finset.mem_coe.1 hmem', ?_⟩
  rw [blockMap_zcast fine_eq_P1 P1_pos, supDist_le_iff]
  intro μ
  rw [cycNorm_le_iff]
  refine ⟨-s μ, by simpa using hs μ, ?_⟩
  simp [zcast]

/-- Near `Z'`, a site of `Z_k` lies in `Z'`. -/
theorem mem_of_mem_Zk_near (st : RegionStep d L n0 n1 Rprev Rk) (hL : 0 < L) (hn : n0 = L * n1)
    (hZ : st.Omegaᶜ ⊆ Zp) (hZ' : Z' ∈ comps ω (finOf Zp)) {D : ℕ} (hD : D < ω) {z : Fin d → ℤ}
    (hz : z ∈ dilZ (L ^ (k + 1) * (c * M1)) D
      (pbZ (M1 * (c * n1) * L ^ (k + 1))
        ((fineK1 M1 c n1 L k (Z' : Set (Torus d n1)) : Finset _) :
          Set (Torus d (M1 * (c * n1) * L ^ (k + 1))))))
    (hk : z ∈ pbZ (M1 * (c * n1) * L ^ (k + 1))
      ((fineK M1 c n1 L k n0 st.Z : Finset _) : Set (Torus d (M1 * (c * n1) * L ^ (k + 1))))) :
    z ∈ pbZ (M1 * (c * n1) * L ^ (k + 1))
      ((fineK1 M1 c n1 L k (Z' : Set (Torus d n1)) : Finset _) :
        Set (Torus d (M1 * (c * n1) * L ^ (k + 1)))) := by
  obtain ⟨z', hz'Z, hz'd⟩ := exists_close_of_dil hz
  rw [mem_pbZ, Finset.mem_coe, mem_fineK] at hk
  set x := zcast (M1 * (c * n1) * L ^ (k + 1)) z with hx
  have hp : blockMap (L ^ (k + 1) * (c * M1)) n1 x ∈ Zp := by
    by_contra hp
    have hpO : blockMap (L ^ (k + 1) * (c * M1)) n1 x ∈ st.Omega := by
      by_contra hpO
      exact hp (hZ hpO)
    rw [← blockMap_k_succ hn] at hpO
    exact st.not_mem_Z_of_mem_Omega hL hn hpO hk
  have := mem_comp_of_close hZ' (Finset.mem_coe.1 (Finset.mem_coe.2 hz'Z)) (mem_finOf.2 hp)
    (by rw [supDist_comm]; omega)
  rw [mem_pbZ, Finset.mem_coe, mem_fineK1]
  exact this

/-- Near `Z'`, a site outside `Z'` lies in `Ω_{k+1}`. -/
theorem mem_Omega_of_not_mem_near (st : RegionStep d L n0 n1 Rprev Rk) (hZ : st.Omegaᶜ ⊆ Zp)
    (hZ' : Z' ∈ comps ω (finOf Zp)) {D : ℕ} (hD : D < ω) {z : Fin d → ℤ}
    (hz : z ∈ dilZ (L ^ (k + 1) * (c * M1)) D
      (pbZ (M1 * (c * n1) * L ^ (k + 1))
        ((fineK1 M1 c n1 L k (Z' : Set (Torus d n1)) : Finset _) :
          Set (Torus d (M1 * (c * n1) * L ^ (k + 1))))))
    (hnot : z ∉ pbZ (M1 * (c * n1) * L ^ (k + 1))
      ((fineK1 M1 c n1 L k (Z' : Set (Torus d n1)) : Finset _) :
        Set (Torus d (M1 * (c * n1) * L ^ (k + 1))))) :
    z ∈ pbZ (M1 * (c * n1) * L ^ (k + 1))
      ((fineK1 M1 c n1 L k st.Omega : Finset _) : Set (Torus d (M1 * (c * n1) * L ^ (k + 1)))) := by
  obtain ⟨z', hz'Z, hz'd⟩ := exists_close_of_dil hz
  rw [mem_pbZ, Finset.mem_coe, mem_fineK1]
  by_contra hpO
  apply hnot
  rw [mem_pbZ, Finset.mem_coe, mem_fineK1]
  have hp : blockMap (L ^ (k + 1) * (c * M1)) n1 (zcast (M1 * (c * n1) * L ^ (k + 1)) z) ∈ Zp :=
    hZ hpO
  exact mem_comp_of_close hZ' (Finset.mem_coe.1 (Finset.mem_coe.2 hz'Z)) (mem_finOf.2 hp)
    (by rw [supDist_comm]; omega)

end Local

end Balaban.RootFSpine
