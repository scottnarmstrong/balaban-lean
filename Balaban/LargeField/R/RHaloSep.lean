/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.ZeroDomainSep
import Mathlib.Tactic.Linarith

/-!
# Halos of components of `Z^pre_k` (blocker 4, `notes/phase1/VMOD-43.md` §2(b))

Distinct components of `Z^pre_k` are at sup-distance `≥ ω_k = 2⌊R_base λ_{k-1}²⌋ + L + 11`
(`core_sep`).  With `r = ⌊R_{k-1}⌋` the P5 enlargements are `X^∼ = nbhd 1 X`,
`X^≈ = nbhd (r+1) X` and the halo of P7 pp. 527-528 is `(Z^{≈2})^{∼2} = nbhd (2r+4) Z`
(`halo_eq_nbhd`).  Results:

* a halo of radius `a` of one component and a halo of radius `b` of a different component are
  disjoint as soon as `a + b < ω_k` (`halo_disjoint_of_comp_sep`);
* the `≈`-thickening (`radius `r+1`) of distinct components are disjoint, and the P7 halo of a
  component misses every *other* component, retained or removed (`halo_disjoint_comp`);
* two P7 halos of distinct components are disjoint when `2(2r+4) < ω_k` (`halo_disjoint_halo_of_lt`),
  but this inequality is *not* a consequence of the radius hypothesis: for `r = ⌊R_base λ_{k-1}²⌋`
  one has `ω_k ≤ 2(2r+4)` (`omega_le_halo_sum`), so `comp_sep` alone does not separate the P7 halos
  of two removed components.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale

/-- Neighbourhoods of radii `a`, `b` of two sets at distance `> a + b` are disjoint. -/
theorem nbhd_disjoint_of_sep {d n a b : ℕ} [NeZero n] {X Y : Set (Torus d n)}
    (h : ∀ x ∈ X, ∀ y ∈ Y, a + b < supDist x y) : Disjoint (nbhd a X) (nbhd b Y) := by
  rw [Set.disjoint_left]
  intro z hzX hzY
  obtain ⟨x, hx, hxz⟩ := mem_nbhd.1 hzX
  obtain ⟨y, hy, hyz⟩ := mem_nbhd.1 hzY
  have h1 := supDist_triangle x z y
  have h2 := h x hx y hy
  have h3 := supDist_comm x z
  have h4 := supDist_comm y z
  omega

namespace RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}
  (H : RegionHistory S n R k0 K) [NeZero S.L] [NeZero S.M] {k : ℕ}

/-- The P7 halo `(Z^{≈2})^{∼2}` of a set is the neighbourhood of radius `2⌊R_{k-1}⌋ + 4`. -/
theorem halo_eq_nbhd (r : ℕ) (X : Set (Torus S.d (n k))) :
    nbhd 2 (thick2 r X) = nbhd (2 * r + 4) X := by
  rw [thick2_eq, nbhd_nbhd]; congr 1

/-- **Halo separation from `comp_sep`**: neighbourhoods of radii `a`, `b` of two distinct
components of `Z^pre_k` are disjoint when `a + b < ω_k`. -/
theorem halo_disjoint_of_comp_sep {c c' : H.Comp k} (hne : c ≠ c') {a b : ℕ}
    (hab : a + b < S.omega k) :
    Disjoint (nbhd a (c.1 : Set (Torus S.d (n k)))) (nbhd b (c'.1 : Set (Torus S.d (n k)))) :=
  nbhd_disjoint_of_sep fun _ hx _ hy => lt_of_lt_of_le hab (H.core_sep hne hx hy)

include H in
/-- The halo radius is below `ω_k`: `2⌊R_{k-1}⌋ + 4 < ω_k` (`k ≥ 1`). -/
theorem halo_radius_lt_omega (hk : 1 ≤ k) : 2 * ⌊R (k - 1)⌋₊ + 4 < S.omega k := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have h1 : ⌊R j⌋₊ ≤ ⌊S.Rb * S.lam j ^ 2⌋₊ := Nat.floor_le_floor (H.F.RH.le j)
  rw [Setting.omega_eq_omegaW, omegaW_succ]
  simp only [Nat.add_sub_cancel]
  omega

include H in
/-- The `≈`-thickenings `X^≈ = nbhd (⌊R_{k-1}⌋+1)` of distinct components of `Z^pre_k` are
disjoint (`k ≥ 1`). -/
theorem thick_disjoint (hk : 1 ≤ k) {c c' : H.Comp k} (hne : c ≠ c') :
    Disjoint (thick ⌊R (k - 1)⌋₊ (c.1 : Set (Torus S.d (n k))))
      (thick ⌊R (k - 1)⌋₊ (c'.1 : Set (Torus S.d (n k)))) := by
  have := H.halo_radius_lt_omega hk
  exact H.halo_disjoint_of_comp_sep hne (a := ⌊R (k - 1)⌋₊ + 1) (b := ⌊R (k - 1)⌋₊ + 1) (by omega)

include H in
/-- **The P7 halo of a component misses every other component** (removed or retained), `k ≥ 1`:
`(c^{≈2})^{∼2}` is disjoint from `c'`. -/
theorem halo_disjoint_comp (hk : 1 ≤ k) {c c' : H.Comp k} (hne : c ≠ c') :
    Disjoint (nbhd 2 (thick2 ⌊R (k - 1)⌋₊ (c.1 : Set (Torus S.d (n k)))))
      (c'.1 : Set (Torus S.d (n k))) := by
  have hd := H.halo_disjoint_of_comp_sep hne (a := 2 * ⌊R (k - 1)⌋₊ + 4) (b := 0)
    (by have := H.halo_radius_lt_omega hk; omega)
  rw [halo_eq_nbhd]
  have h0 : nbhd 0 (c'.1 : Set (Torus S.d (n k))) = c'.1 := by
    ext y; rw [mem_nbhd]
    constructor
    · rintro ⟨x, hx, hxy⟩
      rwa [supDist_eq_zero.1 (Nat.le_zero.1 hxy)]
    · intro hy; exact ⟨y, hy, by rw [supDist_self]⟩
  rwa [h0] at hd

include H in
/-- **Two P7 halos of distinct components are disjoint when `2(2⌊R_{k-1}⌋+4) < ω_k`.** -/
theorem halo_disjoint_halo_of_lt {c c' : H.Comp k} (hne : c ≠ c')
    (hlt : 2 * (2 * ⌊R (k - 1)⌋₊ + 4) < S.omega k) :
    Disjoint (nbhd 2 (thick2 ⌊R (k - 1)⌋₊ (c.1 : Set (Torus S.d (n k)))))
      (nbhd 2 (thick2 ⌊R (k - 1)⌋₊ (c'.1 : Set (Torus S.d (n k))))) := by
  rw [halo_eq_nbhd, halo_eq_nbhd]
  exact H.halo_disjoint_of_comp_sep hne (by omega)

include H in
/-- **The numerical separation of P7 halos fails at the maximal radius** (`k ≥ 1`): for
`r = ⌊R_base λ_{k-1}²⌋` (allowed by `R_{k-1} ≤ R_base λ_{k-1}²`), `ω_k ≤ 2(2r+4)`, so the bound
`comp_sep` does not separate two halos of radius `2r+4`.  (Radius hypothesis `R_base ≥ 4L+20`.) -/
theorem omega_le_halo_sum (hk : 1 ≤ k) :
    S.omega k ≤ 2 * (2 * ⌊S.Rb * S.lam (k - 1) ^ 2⌋₊ + 4) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [Setting.omega_eq_omegaW, omegaW_succ]
  have hb := H.F.RH.base
  have h1 := H.F.RH.one_le j
  have h2 : S.Rb ≤ S.Rb * S.lam j ^ 2 := by
    have : 1 ≤ S.lam j ^ 2 := one_le_pow₀ h1
    nlinarith
  have h3 : ((4 * S.L + 20 : ℕ) : ℝ) ≤ S.Rb * S.lam j ^ 2 := by push_cast; linarith
  have h4 : 4 * S.L + 20 ≤ ⌊S.Rb * S.lam j ^ 2⌋₊ := Nat.le_floor h3
  simp only [Nat.add_sub_cancel]
  omega

end RegionHistory

end Balaban.LargeField
