/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.ZeroDomainD
public import Balaban.LargeField.R.RRemovedGeometry
public import Balaban.LargeField.R.CoreResponseOsc
import Balaban.Localization.CubeRegimes
import Mathlib

/-!
# The margin between `Z₀` and the edge of the action region (blocker 4, `hZr` and `hmargin`)

For a component `Z` of `Z_{k}`, `k = k' + 1`, of a region history, with `Z₀ = Zzero k Z` and the action region
`Zr` whose sites are the fine sites of `Z`:

* `torusDist_ge_of_not_mem_comp`: a site `y` whose `π_k`-cube is not in `Z` is at `ℓ¹` distance at least
  `L^{k'} M (L(⌊R_{k'}⌋ + 3) + ⌊R_{k'-1}⌋ + 1) + 1` from every site of a block of `Z₀`
  (`far_Zzero_Omega_top`, `Ω_kᶜ ⊆ Z`, `torusDist_lower`);
* `hZr_removed`: the fine sites of `Z₀` lie in `Zr`;
* `hmargin_removed`: the margin hypothesis of `hosc_of_margin_of_weighted`, with every
  `R ≤ M ⌊R_{k-1}⌋ / L` and `R ≤ ϱ - 1`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background Balaban.Fluctuation Balaban.Localization

namespace RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}
  (H : RegionHistory S n R k0 K) [NeZero S.L] [NeZero S.M]

/-- **The distance from `Z₀` to the outside of `Z`**: a site `y` of the fine torus of horizon `k' + 1` whose
`π_{k'+1}`-cube is not in `Z` is at `ℓ¹` distance at least
`L^{k'} M (L(⌊R_{k'}⌋ + 3) + ⌊R_{k'-1}⌋ + 1) + 1` from every site `x` of a block of `Z₀(Z)`. -/
theorem torusDist_ge_of_not_mem_comp {k' : ℕ} (hkK : k' + 1 ≤ K) (Z : H.Comp (k' + 1))
    {x y : Torus S.d (S.M * n (k' + 1) * S.L ^ (k' + 1))}
    (hx : blockMap (S.L ^ (k' + 1)) (S.M * n (k' + 1)) x ∈ H.Zzero (k' + 1) Z)
    (hy : cubeMap n S.L S.M (k' + 1) (k' + 1) y ∉ (Z.1 : Set (Torus S.d (n (k' + 1))))) :
    ((S.L ^ k' * S.M : ℕ) : ℝ) * ((S.L * (⌊R k'⌋₊ + 3) + ⌊R (k' - 1)⌋₊ + 1 : ℕ) : ℝ) + 1 ≤
      Green.torusDist S.d (S.M * n (k' + 1) * S.L ^ (k' + 1)) y x := by
  have hOm : cubeMap n S.L S.M (k' + 1) (k' + 1) y ∈ ((H.locRH (k' + 1) Z).step k').Omega := by
    by_contra h
    apply hy
    have := H.nbhd_Omega_compl_subset_lin hkK Z (j := k') le_rfl (c := cubeMap n S.L S.M (k' + 1) (k' + 1) y)
      h (by rw [supDist_self]; exact Nat.zero_le _)
    rwa [lin_self] at this
  have hfar := H.far_Zzero_Omega_top hkK Z hx hOm
  have hℓ : S.M * n (k' + 1) * S.L ^ (k' + 1) = (S.L ^ k' * S.M) * n k' :=
    fine_eq (hnn_k H hkK) (Nat.le_succ k')
  have hP : 0 < S.L ^ k' * S.M :=
    Nat.mul_pos (pow_pos (NeZero.pos S.L) _) (NeZero.pos S.M)
  have h1 := torusDist_lower (d := S.d) hℓ hP y x
  have h2 : (S.L * (⌊R k'⌋₊ + 3) + ⌊R (k' - 1)⌋₊ + 2 : ℕ) ≤
      supDist (blockMap (S.L ^ k' * S.M) (n k') y) (blockMap (S.L ^ k' * S.M) (n k') x) := hfar
  have h3 : (((S.L * (⌊R k'⌋₊ + 3) + ⌊R (k' - 1)⌋₊ + 1 : ℕ) : ℝ) + 1) ≤
      (supDist (blockMap (S.L ^ k' * S.M) (n k') y) (blockMap (S.L ^ k' * S.M) (n k') x) : ℝ) := by
    exact_mod_cast h2
  have h4 : ((S.L ^ k' * S.M : ℕ) : ℝ) * (((S.L * (⌊R k'⌋₊ + 3) + ⌊R (k' - 1)⌋₊ + 1 : ℕ) : ℝ) + 1) ≤
      ((S.L ^ k' * S.M : ℕ) : ℝ) *
        (supDist (blockMap (S.L ^ k' * S.M) (n k') y) (blockMap (S.L ^ k' * S.M) (n k') x) : ℝ) :=
    mul_le_mul_of_nonneg_left h3 (Nat.cast_nonneg _)
  nlinarith

/-- The `π_k`-cube of a fine site of a block of `Z₀(Z)` lies in `Z`. -/
theorem cubeMap_mem_comp_of_Zzero {k : ℕ} (hkK : k ≤ K) (Z : H.Comp k)
    {x : Torus S.d (S.M * n k * S.L ^ k)}
    (hx : blockMap (S.L ^ k) (S.M * n k) x ∈ H.Zzero k Z) :
    cubeMap n S.L S.M k k x ∈ (Z.1 : Set (Torus S.d (n k))) := by
  have h2 := H.zzero_cube_mem_comp hkK Z hx
  rwa [H.blockMap_blockMap_eq_cubeMap] at h2

end RegionHistory

section Margin

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}
  (H : RegionHistory S n R k0 K) [NeZero S.L] [NeZero S.M]
  {k' : ℕ} (hkK : k' + 1 ≤ K) (Z : H.Comp (k' + 1)) {N₁ m₁ : ℕ} [NeZero N₁]
  (hq : N₁ * S.L ^ m₁ = S.M * n (k' + 1)) {ϱ : ℝ}
  (G : GeneratingSet S.d S.L (N₁ * S.L ^ m₁) (k' + 1) ϱ) (Zr : ActionConv.Region G)
  (b0 : Torus S.d (N₁ * S.L ^ m₁ * S.L ^ (k' + 1 - (k' + 1)))) (w : Fin S.d → ℕ)
  (hbx : ∀ x : Torus S.d (N₁ * S.L ^ m₁ * S.L ^ (k' + 1)),
    jBlock S.d S.L (N₁ * S.L ^ m₁) (k' + 1) (k' + 1) x ∈ box b0 w ↔
      blockMap (S.L ^ (k' + 1)) (S.M * n (k' + 1))
        (torusCast (congrArg (· * S.L ^ (k' + 1)) hq) x) ∈ H.Zzero (k' + 1) Z)
  (hZrsites : ∀ x : Torus S.d (N₁ * S.L ^ m₁ * S.L ^ (k' + 1)),
    x ∈ Zr.sites ↔ cubeMap n S.L S.M (k' + 1) (k' + 1)
      (torusCast (congrArg (· * S.L ^ (k' + 1)) hq) x) ∈ (Z.1 : Set (Torus S.d (n (k' + 1)))))

include hkK hbx hZrsites in
/-- **Premise `hZr`**: the fine sites of the blocks of `Z₀ = box b0 w` lie in the action region `Zr`, whose sites
are the fine sites of `Z` (`hZrsites`), and `Z₀` is described by `hbx` (typing data, as in
`psiZeroSpec_ripe_of_input`).  `hq` identifies the torus `N₁ L^{m₁}` of the generating set with `M n_k`; no radius
condition. -/
theorem hZr_removed : ∀ x, jBlock S.d S.L (N₁ * S.L ^ m₁) (k' + 1) (k' + 1) x ∈ box b0 w → x ∈ Zr.sites := by
  intro x hx
  exact (hZrsites x).2 (H.cubeMap_mem_comp_of_Zzero hkK Z ((hbx x).1 hx))

theorem torusDist_torusCast {d ℓ ℓ' : ℕ} (h : ℓ = ℓ') (y x : Torus d ℓ) :
    Green.torusDist d ℓ' (torusCast h y) (torusCast h x) = Green.torusDist d ℓ y x := by
  subst h; rfl

theorem torusCast_add_single {d ℓ ℓ' : ℕ} (h : ℓ = ℓ') (y : Torus d ℓ) (μ : Fin d) :
    torusCast h (y + Pi.single μ 1) = torusCast h y + Pi.single μ 1 := by
  subst h; rfl

theorem torusCast_sub_single {d ℓ ℓ' : ℕ} (h : ℓ = ℓ') (y : Torus d ℓ) (μ : Fin d) :
    torusCast h (y - Pi.single μ 1) = torusCast h y - Pi.single μ 1 := by
  subst h; rfl

include hkK hbx hZrsites in
/-- The distance bound of `hfar` in `margin_of_torusDist` for the removed component: every site `y` of the
generating set that is outside `Zr` or next to a site outside `Zr` is at `ℓ¹` distance at least
`T = L^{k'} M (L(⌊R_{k'}⌋ + 3) + ⌊R_{k'-1}⌋ + 1)` from every fine site of a block of `Z₀ = box b0 w`. -/
theorem hfar_removed :
    ∀ y : Torus S.d (N₁ * S.L ^ m₁ * S.L ^ (k' + 1)),
      (y ∉ Zr.sites ∨ ∃ μ : Fin S.d, y + Pi.single μ 1 ∉ Zr.sites ∨ y - Pi.single μ 1 ∉ Zr.sites) →
      ∀ w' ∈ (boxFinset (L := S.L) (N₀ := N₁ * S.L ^ m₁) (k := k' + 1) b0 w).biUnion
          (fib S.d S.L (N₁ * S.L ^ m₁) (k' + 1) (k' + 1)),
        ((S.L ^ k' * S.M : ℕ) : ℝ) * ((S.L * (⌊R k'⌋₊ + 3) + ⌊R (k' - 1)⌋₊ + 1 : ℕ) : ℝ) ≤
          Green.torusDist S.d (N₁ * S.L ^ m₁ * S.L ^ (k' + 1)) y w' := by
  intro y hy w' hw'
  obtain ⟨bk, hbk, hw'fib⟩ := Finset.mem_biUnion.1 hw'
  have hbl : jBlock S.d S.L (N₁ * S.L ^ m₁) (k' + 1) (k' + 1) w' ∈ box b0 w := by
    have : blkMap S.d S.L (N₁ * S.L ^ m₁) (k' + 1) (k' + 1) w' = bk := (Finset.mem_filter.1 hw'fib).2
    have e : jBlock S.d S.L (N₁ * S.L ^ m₁) (k' + 1) (k' + 1) w' = bk := this
    rw [e]; exact mem_boxFinset.1 hbk
  have hZ0 := (hbx w').1 hbl
  have key : ∀ y' : Torus S.d (N₁ * S.L ^ m₁ * S.L ^ (k' + 1)), y' ∉ Zr.sites →
      ((S.L ^ k' * S.M : ℕ) : ℝ) * ((S.L * (⌊R k'⌋₊ + 3) + ⌊R (k' - 1)⌋₊ + 1 : ℕ) : ℝ) + 1 ≤
        Green.torusDist S.d (N₁ * S.L ^ m₁ * S.L ^ (k' + 1)) y' w' := by
    intro y' hy'
    have h1 := H.torusDist_ge_of_not_mem_comp hkK Z hZ0 (fun hc => hy' ((hZrsites y').2 hc))
    rwa [torusDist_torusCast] at h1
  rcases hy with hy | ⟨μ, hy | hy⟩
  · exact (le_add_of_nonneg_right zero_le_one).trans (key y hy)
  · have h1 := key _ hy
    have h2 := Balaban.Reflection.torusDist_add_single_le (d := S.d) y w' μ
    linarith
  · have h1 := key _ hy
    have h2 := Balaban.Reflection.torusDist_sub_single_le (d := S.d) y w' μ
    linarith

include hkK hbx hZrsites in
/-- **Premise `hmargin`**: every site `y` of `Ω₁` outside `Zr` or next to a site outside `Zr` is at path distance at
least `Rm` from the shadow of the fine sites of `Z₀`, for every `Rm ≤ M ⌊R_{k-1}⌋ / L` (`k = k' + 1`) with
`Rm ≤ ϱ - 1`.  So the history gives a margin of `M ⌊R_{k-1}⌋ / L` blocks of side `L^k` (in the units
`(T - 1)/L^{k+1}` of `margin_of_torusDist`), i.e. `≈ (M R_base / L) λ_{k-1}²` when `R_{k-1} = R_base λ_{k-1}²`;
the other cap is the separation `ϱ - 1` of the generating set. -/
theorem hmargin_removed (hϱ : 1 ≤ ϱ) {Rm : ℝ} (hR1 : Rm ≤ (S.M : ℝ) * ⌊R k'⌋₊ / S.L) (hR2 : Rm ≤ ϱ - 1) :
    ∀ y ∈ G.Ω 1, (y ∉ Zr.sites ∨ ∃ μ : Fin S.d, y + Pi.single μ 1 ∉ Zr.sites ∨
        y - Pi.single μ 1 ∉ Zr.sites) →
      ENNReal.ofReal Rm ≤ siteSetDist G (shadow G
        ((boxFinset (L := S.L) (N₀ := N₁ * S.L ^ m₁) (k := k' + 1) b0 w).biUnion
          (fib S.d S.L (N₁ * S.L ^ m₁) (k' + 1) (k' + 1)))) y := by
  intro y hy hOy
  have hL : (0 : ℝ) < S.L := by exact_mod_cast NeZero.pos S.L
  have hM : (0 : ℝ) < S.M := by exact_mod_cast NeZero.pos S.M
  have hfar := hfar_removed H hkK Z hq G Zr b0 w hbx hZrsites
  have hm := margin_of_torusDist hϱ Zr
    (boxFinset (L := S.L) (N₀ := N₁ * S.L ^ m₁) (k := k' + 1) b0 w)
    (T := ((S.L ^ k' * S.M : ℕ) : ℝ) * ((S.L * (⌊R k'⌋₊ + 3) + ⌊R (k' - 1)⌋₊ + 1 : ℕ) : ℝ))
    (fun y' _ h w' hw' => hfar y' h w' hw') y hy hOy
  refine le_trans (ENNReal.ofReal_le_ofReal (le_min ?_ hR2)) hm
  have hp : (0 : ℝ) < (S.L : ℝ) ^ (k' + 1 + 1) := pow_pos hL _
  rw [le_div_iff₀ hp]
  have h1 : (1 : ℝ) ≤ ((S.L ^ k' * S.M : ℕ) : ℝ) * ((3 * S.L + ⌊R (k' - 1)⌋₊ + 1 : ℕ) : ℝ) := by
    have a : (1 : ℝ) ≤ ((S.L ^ k' * S.M : ℕ) : ℝ) := by
      exact_mod_cast Nat.mul_pos (pow_pos (NeZero.pos S.L) _) (NeZero.pos S.M)
    have b : (1 : ℝ) ≤ ((3 * S.L + ⌊R (k' - 1)⌋₊ + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
    nlinarith
  have h2 : ((S.L * (⌊R k'⌋₊ + 3) + ⌊R (k' - 1)⌋₊ + 1 : ℕ) : ℝ) =
      S.L * ⌊R k'⌋₊ + ((3 * S.L + ⌊R (k' - 1)⌋₊ + 1 : ℕ) : ℝ) := by push_cast; ring
  rw [h2]
  have h3 : Rm * (S.L : ℝ) ^ (k' + 1 + 1) ≤ (S.M : ℝ) * ⌊R k'⌋₊ / S.L * (S.L : ℝ) ^ (k' + 1 + 1) :=
    mul_le_mul_of_nonneg_right hR1 hp.le
  have h4 : (S.M : ℝ) * ⌊R k'⌋₊ / S.L * (S.L : ℝ) ^ (k' + 1 + 1) =
      ((S.L ^ k' * S.M : ℕ) : ℝ) * (S.L * ⌊R k'⌋₊) := by
    field_simp
    push_cast; ring
  have h5 : (0 : ℝ) ≤ ((S.L ^ k' * S.M : ℕ) : ℝ) := Nat.cast_nonneg _
  nlinarith [Nat.cast_nonneg (α := ℝ) ⌊R k'⌋₊]

end Margin

end Balaban.LargeField
