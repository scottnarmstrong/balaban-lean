/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Def7Inhabited
public import Balaban.LargeField.R.HaloDistance
public import Balaban.LargeField.R.RegionShrink
import Balaban.SmallField.Def6v2Inhabited
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# A small-field context on a torus with many cubes

The landed inhabitant `nonempty_sfCtx` of `SFCtx` lives on the torus with `n 1 = 1` cube per
side, where every regional statement is vacuous: the thickening of a nonempty region is the whole
torus.  This file gives an inhabitant on a torus with `2 ⌊R_0⌋ + 4` cubes per side and
instantiates the halo-distance lemma and the region-shrink identity on it without vacuity.

## Survey: what forced one cube

The side sequence of the landed family is `sides L K nK j = nK · L^(K - j)` (Def7.lean), and
`RepFam.ctx` takes the top side `nK` as an argument.  `nonempty_sfCtx` only chose `nK = 1`.  The
horizon `K = 1`, the scale `k = 1`, the small-field data (`wSF`), the geometric typing (`wGeo`,
`M₁ = 1`, `c = 27`) and the setting `wS` do not depend on `nK`; `wFam` is a single family over all
tori.  So the cheapest change is `nK = 2 ⌊R_0⌋ + 4`: nothing is re-proved, `wFam` and `ctx` are
instantiated at a new `nK`.  Here `n 1 = sides 3 1 nK 1 = nK` and the radius used by `thickY` at
`k = 1` is `R_0 = 32 λ_0²`, where `λ_0 = log(5β/4) + 1` is large.

## Parametric lemmas

`siteOf` puts the corner site of a cube of `𝕋_k` on the Def-6 torus; it lies in the fine set of a
region exactly when its cube does, and it is `L^j`-aligned for `j ≤ k`.  A cube at index distance
`r + 2` from the origin on a torus with `2 r + 4` cubes per side is not in the thickening
`thick r {0}`.
-/

@[expose] public section

namespace Balaban.LargeField.Def7

open Balaban Balaban.Multiscale Balaban.Localization Balaban.SmallField Balaban.LargeField
  Balaban.Background Balaban.LargeField.Def7.Wit

section Generic

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N k m₁ : ℕ} {ϱ : ℝ} (C : SFCtx S n R M K N k m₁ ϱ)

private theorem sigma_pos : 0 < S.L ^ k * M :=
  Nat.mul_pos (pow_pos (Nat.pos_of_ne_zero (NeZero.ne S.L)) _) (Nat.pos_of_ne_zero (NeZero.ne M))

/-- The corner site, on the Def-6 torus, of a cube `c` of `𝕋_k`: coordinates `c_i · L^k M`. -/
def siteOf (c : Torus S.d (n k)) : Localization.CTorus S.d S.L C.N₁ m₁ k :=
  fun i => (((c i).val * (S.L ^ k * M) : ℕ) : ZMod _)

theorem val_siteOf (c : Torus S.d (n k)) (i : Fin S.d) :
    (siteOf C c i).val = (c i).val * (S.L ^ k * M) := by
  unfold siteOf
  apply ZMod.val_natCast_of_lt
  rw [side_eq_sigma C, mul_comm (S.L ^ k * M)]
  exact Nat.mul_lt_mul_of_pos_right (ZMod.val_lt (c i)) (sigma_pos (S := S) (k := k) (M := M))

/-- The cube of the corner site is the cube. -/
theorem cubeMap_siteOf (c : Torus S.d (n k)) :
    cubeMap n S.L M K k (bgToFine C.geo C.hnn C.hkK (sfToBg C.geo C.hT (siteOf C c))) = c := by
  funext i
  rw [cubeMap_sfToBg]
  unfold blockCoord
  rw [val_siteOf, Nat.mul_div_cancel _ (sigma_pos (S := S) (k := k) (M := M))]
  exact ZMod.natCast_zmod_val (c i)

/-- The corner site of `c` is in the fine set of `A` iff `c ∈ A`. -/
theorem siteOf_mem_sset (A : Set (Torus S.d (n k))) (c : Torus S.d (n k)) :
    siteOf C c ∈ C.sset A ↔ c ∈ A := by
  show cubeMap n S.L M K k (bgToFine C.geo C.hnn C.hkK (sfToBg C.geo C.hT (siteOf C c))) ∈ A ↔ _
  rw [cubeMap_siteOf]

theorem aligned_siteOf {j : ℕ} (hj : j ≤ k) (c : Torus S.d (n k)) :
    Aligned (S.L ^ j) (siteOf C c) := by
  intro μ
  rw [val_siteOf]
  apply Nat.mod_eq_zero_of_dvd
  exact Dvd.dvd.mul_left (dvd_mul_of_dvd_left (pow_dvd_pow _ hj) M) _

/-- The corner site of `c` is an aligned site of `A` iff `c ∈ A`. -/
theorem siteOf_mem_alignedIn {j : ℕ} (hj : j ≤ k) (A : Set (Torus S.d (n k)))
    (c : Torus S.d (n k)) : siteOf C c ∈ C.alignedIn j A ↔ c ∈ A := by
  classical
  simp only [SFCtx.alignedIn, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [siteOf_mem_sset]
  exact ⟨fun h => h.2, fun h => ⟨aligned_siteOf C hj c, h⟩⟩

end Generic

section Far

/-- A cube at index distance `r + 2` from the origin on a torus with `2 r + 4` cubes per side is
not in `thick r {0}` (which is the `(r+1)`-neighbourhood). -/
theorem far_not_mem_thick {d N r : ℕ} [NeZero N] (hN : N = 2 * r + 4) (i₀ : Fin d) :
    (Function.update (0 : Torus d N) i₀ ((r + 2 : ℕ) : ZMod N)) ∉
      thick r ({0} : Set (Torus d N)) := by
  unfold thick
  rw [mem_nbhd]
  rintro ⟨x, hx, h⟩
  rw [Set.mem_singleton_iff] at hx
  subst hx
  have hval : (((r + 2 : ℕ) : ZMod N)).val = r + 2 := ZMod.val_natCast_of_lt (by omega)
  have h1 : cycNorm N ((Function.update (0 : Torus d N) i₀ ((r + 2 : ℕ) : ZMod N)) i₀ -
      (0 : Torus d N) i₀) ≤ supDist (Function.update (0 : Torus d N) i₀ ((r + 2 : ℕ) : ZMod N))
        (0 : Torus d N) :=
    Finset.le_sup (f := fun i => cycNorm N ((Function.update (0 : Torus d N) i₀
      ((r + 2 : ℕ) : ZMod N)) i - (0 : Torus d N) i)) (Finset.mem_univ i₀)
  simp only [Function.update_self, Pi.zero_apply, sub_zero, cycNorm, hval] at h1
  omega

/-- Two distinct cubes on a torus with at least two cubes per side. -/
theorem one_ne_zero_zmod {N : ℕ} (hN : 2 ≤ N) : ((1 : ℕ) : ZMod N) ≠ 0 := by
  intro h
  rw [ZMod.natCast_eq_zero_iff] at h
  have := Nat.le_of_dvd one_pos h
  omega

end Far

section Instance

/-- The number `⌊R_0⌋` of cubes of the halo at scale `k = 1` of the witness radii. -/
noncomputable def rMulti : ℕ := ⌊wR 0⌋₊

/-- The number of cubes per side of the scale-`1` torus of the multi-cube context. -/
noncomputable def nMulti : ℕ := 2 * rMulti + 4

instance : NeZero nMulti := ⟨by unfold nMulti; omega⟩

theorem sides_nMulti : sides wS.L 1 nMulti 1 = 2 * ⌊wR (1 - 1)⌋₊ + 4 := by
  simp [sides, nMulti, rMulti]

/-- **The multi-cube small-field context**: the landed family `wFam` at the top side
`nK = 2 ⌊R_0⌋ + 4`. -/
noncomputable def ctxMulti :
    SFCtx wS (sides wS.L 1 nMulti) wR 27 1 2 1 wC7.m₁ (bgR0 3 3) :=
  (wFam wν₀ (kZero wS.d wS.L wβ wν₀) 2).ctx wM6 le_rfl nMulti

/-- **`SFCtx` has an inhabitant whose scale-`k` torus has many cubes**: with `d = L = 3`, `N = 2`,
`M = 27`, horizon `K = 1`, scale `k = 1`, `m₁ = 3`, the radii `R_j = 32 λ_j²` and the side sequence
`sides 3 1 nK`, there is a top side `nK` with `n 1 = nK ≥ 2 ⌊R_0⌋ + 4` cubes per side. -/
theorem nonempty_sfCtx_multi :
    ∃ nK : ℕ, ∃ _ : NeZero nK, 2 * ⌊wR (1 - 1)⌋₊ + 4 ≤ sides wS.L 1 nK 1 ∧
      Nonempty (SFCtx wS (sides wS.L 1 nK) wR 27 1 2 1 wC7.m₁ (bgR0 3 3)) :=
  ⟨nMulti, inferInstance, sides_nMulti.ge, ⟨ctxMulti⟩⟩

end Instance

end Balaban.LargeField.Def7
