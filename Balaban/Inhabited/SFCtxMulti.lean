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

## Findings on the landed data

* The small-field data `wSF` has nonzero running couplings `β`, `ν`, `a` and `z = 1`, but the
  terms `E`, `ℰ`, `ℳ` (the family `zeroFam`), `ℛ` and `corr` are all zero.  The regional
  statements are tested for the shape of their index sets only.
* `hT : N₁ L^{m₁} L^k = M₁ (c n_k) L^k` holds for every `n_k` because `N₁ = L^{m₀} n_k` and
  `M = c M₁` (`sfIdx_hT`); `hnn` holds for `sides` for every `nK`.  Neither relates `n_k` to the
  radii, so a torus with many cubes is admissible.
* The halo `⌊R_{k-1}⌋ + 1` is `⌊R_0⌋ + 1 ≥ 33` cubes at `k = 1`, since `R_0 = 32 λ_0² ≥ 32`
  (`Geo.hRlow`); the torus with `2⌊R_0⌋ + 4` cubes per side is the smallest one used here, in
  which a single cube does not have a thickening equal to the torus.

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

section Regional

open Balaban.LargeField.RegionShrink

theorem wR_ge (j : ℕ) : 32 ≤ wR j := by
  have h1 := wS_lam_one_le j
  have h3 : (1 : ℝ) ≤ wS.lam j ^ 2 := one_le_pow₀ h1
  show (32 : ℝ) ≤ wS.Rb * wS.lam j ^ 2
  have : wS.Rb = 32 := rfl
  rw [this]
  linarith

theorem wS_L_cast : ((wS.L : ℕ) : ℝ) = 3 := by norm_num [wS, setting, typing, typing0]

/-- The torus of the multi-cube context has at least two cubes per side. -/
theorem two_le_nMulti : 2 ≤ sides wS.L 1 nMulti 1 := by
  have := sides_nMulti
  omega

/-- **Non-vacuous halo distance** (`regionalHaloDistance`, `exp_sizeJ_le_of_halo`) on the
multi-cube context, `k = j = 1`: a region `Y` of one cube whose thickening is not the whole torus,
an aligned centre `y` over `Y`, and the whole torus as a polymer `X ∈ 𝒟_1` through `y` that is not
contained in the fine set of `Y^≈`.  The lower bound `(M / L^(m₀+m₁)) R_0 L^0 - 2L` on its size
is strictly positive (it equals `R_0 - 6 ≥ 26`), and the bound and the decay form hold. -/
theorem multi_halo_instance :
    ∃ (Y : Set (Torus wS.d (sides wS.L 1 nMulti 1)))
      (y : Localization.CTorus wS.d wS.L ctxMulti.N₁ wC7.m₁ 1)
      (X : Set (Localization.CTorus wS.d wS.L ctxMulti.N₁ wC7.m₁ 1)),
      Y.Nonempty ∧ thickY wR Y ≠ Set.univ ∧ y ∈ ctxMulti.alignedIn 1 Y ∧
      Def6.IsPolyDom ctxMulti.m₀ 1 X ∧ y ∈ X ∧ ¬ X ⊆ ctxMulti.sset (thickY wR Y) ∧
      0 < (((27 : ℕ) : ℝ) / ((wS.L : ℕ) : ℝ) ^ (ctxMulti.m₀ + wC7.m₁)) * wR (1 - 1) *
          ((wS.L : ℕ) : ℝ) ^ (1 - 1) - 2 * ((wS.L : ℕ) : ℝ) ∧
      (((27 : ℕ) : ℝ) / ((wS.L : ℕ) : ℝ) ^ (ctxMulti.m₀ + wC7.m₁)) * wR (1 - 1) *
          ((wS.L : ℕ) : ℝ) ^ (1 - 1) - 2 * ((wS.L : ℕ) : ℝ) ≤ Def6.sizeJ ctxMulti.m₀ 1 X ∧
      ∀ ρ : ℝ, 0 ≤ ρ → Real.exp (-ρ * Def6.sizeJ ctxMulti.m₀ 1 X) ≤
        Real.exp (2 * ((wS.L : ℕ) : ℝ) * ρ) * Real.exp (-ρ * ((((27 : ℕ) : ℝ) /
          ((wS.L : ℕ) : ℝ) ^ (ctxMulti.m₀ + wC7.m₁)) * (⌊wR (1 - 1)⌋₊ : ℝ) *
          ((wS.L : ℕ) : ℝ) ^ (1 - 1))) := by
  classical
  set C := ctxMulti with hC
  let i₀ : Fin wS.d := ⟨0, by norm_num [wS, setting, typing, typing0]⟩
  have hN : sides wS.L 1 nMulti 1 = 2 * ⌊wR (1 - 1)⌋₊ + 4 := sides_nMulti
  let c₂ : Torus wS.d (sides wS.L 1 nMulti 1) :=
    Function.update 0 i₀ ((⌊wR (1 - 1)⌋₊ + 2 : ℕ) : ZMod _)
  have hfar : c₂ ∉ thick ⌊wR (1 - 1)⌋₊ ({0} : Set (Torus wS.d (sides wS.L 1 nMulti 1))) :=
    far_not_mem_thick hN i₀
  have hthick : thickY wR ({0} : Set (Torus wS.d (sides wS.L 1 nMulti 1))) ≠ Set.univ := by
    intro h
    apply hfar
    have : c₂ ∈ thickY wR ({0} : Set (Torus wS.d (sides wS.L 1 nMulti 1))) := by
      rw [h]; trivial
    exact this
  have hy : siteOf C 0 ∈ C.alignedIn 1 ({0} : Set (Torus wS.d (sides wS.L 1 nMulti 1))) :=
    (siteOf_mem_alignedIn C le_rfl _ _).2 (Set.mem_singleton _)
  have hyS : siteOf C 0 ∈ C.sset ({0} : Set (Torus wS.d (sides wS.L 1 nMulti 1))) :=
    (siteOf_mem_sset C _ _).2 (Set.mem_singleton _)
  have hX : Def6.IsPolyDom C.m₀ 1
      (Set.univ : Set (Localization.CTorus wS.d wS.L C.N₁ wC7.m₁ 1)) :=
    Balaban.SmallField.Def6v2.isPolyDom_univ _ _
  have hnot : ¬ (Set.univ : Set (Localization.CTorus wS.d wS.L C.N₁ wC7.m₁ 1)) ⊆
      C.sset (thickY wR ({0} : Set (Torus wS.d (sides wS.L 1 nMulti 1)))) := by
    intro h
    have := (siteOf_mem_sset C _ c₂).1 (h (Set.mem_univ (siteOf C c₂)))
    exact hfar this
  have hm : C.m₀ = 0 := rfl
  have h3 : wC7.m₁ = 3 := rfl
  refine ⟨{0}, siteOf C 0, Set.univ, Set.singleton_nonempty _, hthick, hy, hX, trivial, hnot,
    ?_, ?_, ?_⟩
  · rw [hm, h3, wS_L_cast]
    have := wR_ge (1 - 1)
    norm_num
    linarith
  · exact regionalHaloDistance C le_rfl hX trivial hyS hnot
  · intro ρ hρ
    exact exp_sizeJ_le_of_halo C le_rfl hX hy trivial hnot hρ

open Classical in
/-- **Non-vacuous region shrink** (`EresJ2_shrink`) on the multi-cube context: nested regions
`Y' = {0} ⊂ Y = {0, e}` (two cubes) with `alignedIn 1 Y' ⊂ alignedIn 1 Y` strictly, so the
deleted-centre set `alignedIn 1 Y \ alignedIn 1 Y'` is nonempty, and the identity of
`EresJ2_shrink` for every correction coefficient `vc`, field `hv` and composed field `ψ`.  In the
witness `𝔰` all terms `E`, `ℳ`, `ℛ`, `corr` are zero, so both sides are `0`; only the shapes of
the index sets are tested. -/
theorem multi_shrink_instance :
    ∃ Y Y' : Set (Torus wS.d (sides wS.L 1 nMulti 1)), Y' ⊆ Y ∧
      ctxMulti.alignedIn 1 Y' ⊂ ctxMulti.alignedIn 1 Y ∧
      (ctxMulti.alignedIn 1 Y \ ctxMulti.alignedIn 1 Y').Nonempty ∧
      ∀ (vc : Def7v2.CorrCoef wS.d) (hv : EuclideanSpace ℝ (Fin 2))
        (ψ : Def6.Fld wS.d wS.L ctxMulti.N₁ wC7.m₁ 1 2),
      EresAt ctxMulti vc hv 1 (ctxMulti.alignedIn 1 Y) (ctxMulti.alignedIn 1 (thickY wR Y))
          (ctxMulti.sset (thickY wR Y)) ψ -
        EresAt ctxMulti vc hv 1 (ctxMulti.alignedIn 1 Y') (ctxMulti.alignedIn 1 (thickY wR Y'))
          (ctxMulti.sset (thickY wR Y')) ψ =
        shrinkDeleted (polyUniv ctxMulti 1) (polyTerm ctxMulti hv 1 ψ) (ctxMulti.alignedIn 1 Y)
            (ctxMulti.alignedIn 1 Y') (ctxMulti.sset (thickY wR Y)) +
          shrinkCrossing (polyUniv ctxMulti 1) (polyTerm ctxMulti hv 1 ψ)
            (ctxMulti.alignedIn 1 Y') (ctxMulti.sset (thickY wR Y))
            (ctxMulti.sset (thickY wR Y')) -
          shrinkFlux (corrFn ctxMulti vc hv 1 ψ) (ctxMulti.alignedIn 1 Y)
            (ctxMulti.alignedIn 1 Y') (ctxMulti.alignedIn 1 (thickY wR Y))
            (ctxMulti.alignedIn 1 (thickY wR Y')) := by
  set C := ctxMulti with hC
  let i₀ : Fin wS.d := ⟨0, by norm_num [wS, setting, typing, typing0]⟩
  let c₁ : Torus wS.d (sides wS.L 1 nMulti 1) := Function.update 0 i₀ ((1 : ℕ) : ZMod _)
  have hc1 : c₁ ≠ 0 := by
    intro h
    have := congrFun h i₀
    simp only [c₁, Function.update_self, Pi.zero_apply] at this
    exact one_ne_zero_zmod two_le_nMulti this
  have hsub : ({0} : Set (Torus wS.d (sides wS.L 1 nMulti 1))) ⊆ {0, c₁} := by
    intro x hx; exact Or.inl hx
  have hc1Y : c₁ ∈ ({0, c₁} : Set (Torus wS.d (sides wS.L 1 nMulti 1))) := Or.inr rfl
  have hc1Y' : c₁ ∉ ({0} : Set (Torus wS.d (sides wS.L 1 nMulti 1))) := hc1
  have hdel : siteOf C c₁ ∈ C.alignedIn 1 ({0, c₁} : Set (Torus wS.d (sides wS.L 1 nMulti 1))) \
      C.alignedIn 1 ({0} : Set (Torus wS.d (sides wS.L 1 nMulti 1))) :=
    Finset.mem_sdiff.2 ⟨(siteOf_mem_alignedIn C le_rfl _ _).2 hc1Y,
      fun h => hc1Y' ((siteOf_mem_alignedIn C le_rfl _ _).1 h)⟩
  refine ⟨{0, c₁}, {0}, hsub, ?_, ⟨_, hdel⟩, fun vc hv ψ => ?_⟩
  · refine ⟨alignedIn_mono C 1 hsub, fun h => ?_⟩
    exact (Finset.mem_sdiff.1 hdel).2 (h (Finset.mem_sdiff.1 hdel).1)
  · exact EresJ2_shrink C vc hv 1 hsub ψ

end Regional

end Balaban.LargeField.Def7
