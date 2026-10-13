module

public import Balaban.Inhabited.ChiYWitness
public import Balaban.LargeField.GlobalGenRegional
import Mathlib.Tactic.Linarith

/-!
# A context in which the local generating set is a proper subset

`Balaban.LargeField.GlobalGenRegional` proves that the regional composed field `C.psiJ Y ψk hv j`
is outside the analyticity domain of the whole-level generating set `levelGS j` as soon as some
site is outside the data sites of the local generating set `genSF j (W2 R Y)`.  No landed context
has such a site: on the tori of `nonempty_sfCtx`, `ctxMulti` and `ctxY` the halo `W2 R Y` covers the
whole torus.  This file gives a context and a region for which the site hypothesis holds, and
instantiates the theorem.

This shows that the regional argument is outside the whole-level term domain in a concrete context.
It does not show that no scheme with whole-level generating sets can work, and it makes no choice
between the options; that choice is with the author.

## The context `ctxPlg`

It is the context `ctxY` (scale `k = 1`, horizon `K = 1`, `d = L = 3`, `N = 2`, `M₁ = 3^{a₁}`,
`c = 27`, constants `csY`, small-field data `wSF`) with the number of scale-`1` cubes per side
`nPlg = 4 ⌊R_0⌋ + 8` in place of `2 ⌊R_0⌋ + 4`.  Of the constructions of `ChiYWitness.lean` and
`SFCtxMulti.lean` only the choice of the top side `nK` is changed: `geoY` used the radii conditions
`(wGeo _).hRlow`, `(wGeo _).hRmono` at the side `nMulti`, here taken at the side `nPlg`; `sides_hnn`,
`sfIdx_hT`, `siteOf` and `cubeMap_siteOf` are stated for every side.

## The region and the site

`Y = {0}` is one cube.  A datum site of `genSF 1 (W2 R Y)` lies over a cube within `2 ⌊R_0⌋ + 3`
of `Y` (`dataSite_cube_mem_nbhd`, as `genSF 1 = genW` at `j = k = 1`).  The corner site over the
cube `(2 ⌊R_0⌋ + 4) e_0` lies over a cube at distance `2 ⌊R_0⌋ + 4` from `Y` (the torus has
`4 ⌊R_0⌋ + 8` cubes per side), hence is not a datum site.

## Contrast and the terms

`xiDom_levelGS_nonempty_plg`: the whole-level domain is not empty in the landed witness setting.
`psiJ_xIn`, `psiJ_xIn_ne_zero`: at a site over the cube of `Y0` the regional field for the constant
block field `whv` is the unit vector `whv`.  The small-field terms of `ctxPlg` are those of the
witness family `zeroFam` (`E`, `ℰ`, `ℳ`, `ℛ`, `corr` all zero), so the sums `EresJ`, `MresJ` on this
context are sums of zero terms: the result concerns the argument at which the terms are evaluated,
not a non-zero term.
-/

@[expose] public section

namespace Balaban.Inhabited.ProperLocalGen

open Balaban Balaban.Multiscale Balaban.Localization Balaban.SmallField Balaban.LargeField
  Balaban.Background Balaban.LargeField.Def7 Balaban.LargeField.Def7.Wit

/-- The number of scale-`1` cubes per side: `4 ⌊R_0⌋ + 8`. -/
noncomputable def nPlg : ℕ := 4 * rMulti + 8

instance : NeZero nPlg := ⟨by unfold nPlg; omega⟩

/-- The geometric typing of `ctxY` on the torus with `nPlg` cubes per side. -/
noncomputable def geoPlg : Geo wS (sides wS.L 1 nPlg) wR (27 * M1y) where
  M1 := M1y
  c := 27
  neM1 := inferInstance
  nec := ⟨by norm_num⟩
  hM := rfl
  hc := by norm_num
  hRlow := (wGeo (sides wS.L 1 nPlg)).hRlow
  hRmono := (wGeo (sides wS.L 1 nPlg)).hRmono

/-- **The small-field context on the wide torus**: `ctxY` with `nPlg = 4 ⌊R_0⌋ + 8` scale-`1`
cubes per side. -/
noncomputable def ctxPlg :
    SFCtx wS (sides wS.L 1 nPlg) wR (27 * M1y) 1 2 1 wC7.m₁ (bgR0 3 3) where
  geo := geoPlg
  hnn := sides_hnn wS.L 1 nPlg
  hkK := le_rfl
  cs := csY
  m₀ := a1
  sf := wSF wν₀ 3
  N₁ := sfIdx wS.L a1 (sides wS.L 1 nPlg) 1
  hT := sfIdx_hT geoPlg M_eq_pow_y

theorem sides_nPlg : sides wS.L 1 nPlg 1 = 4 * ⌊wR 0⌋₊ + 8 := by
  simp [sides, nPlg, rMulti]

/-- The region: one cube. -/
def Y0 : Set (Torus wS.d (sides wS.L 1 nPlg 1)) := {0}

/-- The cube at index distance `2 ⌊R_0⌋ + 4` from the origin along the first axis. -/
noncomputable def cFar : Torus wS.d (sides wS.L 1 nPlg 1) :=
  Function.update 0 ⟨0, by norm_num [wS, setting, typing, typing0]⟩
    ((2 * rMulti + 4 : ℕ) : ZMod _)

/-- **Distance bound.**  The cube `cFar` is not within `2 ⌊R_0⌋ + 3` of `Y0`. -/
theorem cFar_not_mem_nbhd : cFar ∉ nbhd (2 * ⌊wR 0⌋₊ + 3) Y0 := by
  unfold cFar Y0
  rw [mem_nbhd]
  rintro ⟨x, hx, h⟩
  rw [Set.mem_singleton_iff] at hx
  subst hx
  have hN := sides_nPlg
  have hval : (((2 * rMulti + 4 : ℕ) : ZMod (sides wS.L 1 nPlg 1))).val = 2 * rMulti + 4 :=
    ZMod.val_natCast_of_lt (by unfold rMulti; omega)
  have h1 := Finset.le_sup (f := fun i => cycNorm (sides wS.L 1 nPlg 1)
    ((Function.update (0 : Torus wS.d (sides wS.L 1 nPlg 1))
      ⟨0, by norm_num [wS, setting, typing, typing0]⟩ ((2 * rMulti + 4 : ℕ) : ZMod _)) i -
      (0 : Torus wS.d (sides wS.L 1 nPlg 1)) i))
    (Finset.mem_univ (⟨0, by norm_num [wS, setting, typing, typing0]⟩ : Fin wS.d))
  have h2 := h.trans' h1
  simp only [Function.update_self, Pi.zero_apply, sub_zero, cycNorm, hval] at h2
  unfold rMulti at h2 hval
  omega

/-- The site over the far cube. -/
noncomputable def xFar : Localization.CTorus wS.d wS.L ctxPlg.N₁ wC7.m₁ 1 := siteOf ctxPlg cFar

/-- **The local generating set is proper**: the site `xFar` is not a data site of
`genSF 1 (W2 R Y0)`; the data sites lie over cubes within `2 ⌊R_0⌋ + 3` of `Y0`, and `xFar` lies
over a cube at distance `2 ⌊R_0⌋ + 4`. -/
theorem xFar_not_mem : sfToBg ctxPlg.geo ctxPlg.hT xFar ∉ dataSites
    (genSF (M1 := ctxPlg.geo.M1) (N₁ := ctxPlg.geo.c * sides wS.L 1 nPlg 1) (L := wS.L)
      (c := ctxPlg.geo.c) (n := sides wS.L 1 nPlg 1) (le_refl 1) (W2 wR Y0)) := by
  intro hs
  have h := dataSite_cube_mem_nbhd (j := 0) ctxPlg (by norm_num [wS, setting, typing, typing0])
    Y0 hs
  rw [xFar, cubeMap_siteOf] at h
  exact cFar_not_mem_nbhd h


theorem ctxPlg_weights_one : ctxPlg.weights 1 = 5 / 4 := by
  show Def6.aIdeal 3 1 (5 / 4) 1 = 5 / 4
  unfold Def6.aIdeal
  have : (1 - (((3 : ℕ) : ℝ) ^ 1)⁻¹ ^ 2 : ℝ) ≠ 0 := by norm_num
  field_simp

/-- **The regional field vanishes at the far site.** -/
theorem psiJ_xFar (ψk : BlockAt wS (sides wS.L 1 nPlg) (27 * M1y) 1 1 → EuclideanSpace ℝ (Fin 2))
    (hv : EuclideanSpace ℝ (Fin 2)) (i : Fin 2) :
    ctxPlg.psiJ Y0 ψk hv 1 xFar i = 0 :=
  GlobalGenRegional.psiJ_eq_zero_of_not_mem ctxPlg Y0 ψk hv (le_refl 1) xFar_not_mem i

/-- **The instance.**  In the context `ctxPlg`, for the region `Y0` of one cube, `xFar` is a site
outside the data sites of the local generating set `genSF 1 (W2 R Y0)`; the regional composed field
vanishes there; and for every block field `ψk`, vector `hv`, kernel sequence `a`, mass `ν` and
radius `ε`, the pair `(C.psiJ Y0 ψk hv 1, constFld (hC hv))` is outside `XiDom (levelGS 1)`. -/
theorem properLocalGen_instance :
    ∃ x : Localization.CTorus wS.d wS.L ctxPlg.N₁ wC7.m₁ 1,
      sfToBg ctxPlg.geo ctxPlg.hT x ∉ dataSites
        (genSF (M1 := ctxPlg.geo.M1) (N₁ := ctxPlg.geo.c * sides wS.L 1 nPlg 1) (L := wS.L)
          (c := ctxPlg.geo.c) (n := sides wS.L 1 nPlg 1) (le_refl 1) (W2 wR Y0)) ∧
      (∀ ψk hv, ∀ i, ctxPlg.psiJ Y0 ψk hv 1 x i = 0) ∧
      ∀ (ψk : BlockAt wS (sides wS.L 1 nPlg) (27 * M1y) 1 1 → EuclideanSpace ℝ (Fin 2))
        (hv : EuclideanSpace ℝ (Fin 2)) (a : ℕ → ℝ) (ν ε : ℝ),
        ¬ Def6.XiDom (Def6.levelGS (d := wS.d) (L := wS.L) (N₁ := ctxPlg.N₁) (m₁ := wC7.m₁) (k := 1)
          (ϱ := bgR0 3 3) 1 (le_refl 1)) a ν 1 ε (ctxPlg.psiJ Y0 ψk hv 1)
          (Def6.constFld (hC hv)) :=
  ⟨xFar, xFar_not_mem, fun ψk hv i => psiJ_xFar ψk hv i, fun ψk hv a ν ε =>
    GlobalGenRegional.regional_psiJ_not_globalXiDom ctxPlg Y0 ψk hv (by norm_num [wS, setting, typing, typing0])
      le_rfl le_rfl xFar_not_mem a ν ε⟩


/-! ### Contrast -/

/-- **The whole-level domain is not empty in this setting** (the landed witness kernel sequence and
mass): the constant unit field lies in `XiDom (levelGS 1)` for the Def-6 torus of `ctxPlg`. -/
theorem xiDom_levelGS_nonempty_plg (ε : ℝ) (hε : 0 < ε) :
    Def6.XiDom (Def6.levelGS 1 (le_refl 1) :
        GeneratingSet 3 3 (ctxPlg.N₁ * 3 ^ wC7.m₁) 1 (bgR0 3 3))
      (Def6.aIdeal 3 1 (Def6.witnessa 1))
      (Def6.bgMass 3 1 (Def6.witnessβ 1) (Def6.witnessν 1 1)) 1 ε
      (fun _ => (Pi.single (0 : Fin 2) 1 : Fin 2 → ℂ))
      (fun _ => (Pi.single (0 : Fin 2) 1 : Fin 2 → ℂ)) :=
  GlobalGenRegional.xiDom_levelGS_nonempty (m₁ := wC7.m₁) (N₁ := ctxPlg.N₁) (α₀ := 1)
    one_pos le_rfl (le_refl 1) ε hε

/-- The site over the cube `0 ∈ Y0`. -/
noncomputable def xIn : Localization.CTorus wS.d wS.L ctxPlg.N₁ wC7.m₁ 1 := siteOf ctxPlg 0

theorem xIn_mem : sfToBg ctxPlg.geo ctxPlg.hT xIn ∈ (ctxPlg.genW Y0).Ω 1 := by
  have hs1 : sfToBg ctxPlg.geo ctxPlg.hT xIn ∈ (ctxPlg.genW Y0).Ω (0 + 1) := by
    rw [genW_mem_top_iff]
    have e := cubeMap_bgToFine (j := 0) ctxPlg (sfToBg ctxPlg.geo ctxPlg.hT xIn)
    rw [xIn, cubeMap_siteOf] at e
    have h0 : (0 : Torus wS.d (sides wS.L 1 nPlg 1)) ∈ W2 wR Y0 :=
      nbhd_two_subset_W2 (j := 0) Y0 (Set.mem_singleton _)
        (mem_nbhd.mpr ⟨0, rfl, by simp [supDist, cycNorm]⟩)
    exact Eq.mpr (congrArg (· ∈ W2 wR Y0) e.symm) h0
  exact mem_Ω_one_of_top _ (Nat.succ_pos 0) hs1


/-- **Inside the local data sites the regional field is the unit vector.**  For the constant block
field `whv` (a unit vector), at the site `xIn` over the cube of `Y0` the regional field
`C.psiJ Y0 (fun _ => whv) whv 1` equals `whv`; in particular it is nonzero. -/
theorem psiJ_xIn (i : Fin 2) :
    ctxPlg.psiJ Y0 (fun _ => whv) whv 1 xIn i = ((whv i : ℝ) : ℂ) := by
  have hmem := xIn_mem
  unfold SFCtx.psiJ
  simp only [le_refl, ↓reduceDIte]
  unfold sfPull psiSF
  rw [composeField_of_mem _ _ _ hmem i]
  have hl : (ctxPlg.genW Y0).layerIndex (sfToBg ctxPlg.geo ctxPlg.hT xIn) = 1 :=
    layerIndex_top _ (le_refl 1) hmem
  have hd : sfToBg ctxPlg.geo ctxPlg.hT xIn ∈ dataSites (ctxPlg.genW Y0) :=
    (mem_dataSites _).2 (Or.inl hmem)
  have hΨ := liftSingle_Ψ (ctxPlg.genW Y0) (ctxPlg.liftData fun _ => whv) (hC whv) hd
  simp only [hl, ctxPlg_weights_one]
  rw [hΨ]
  have h3 : ((wS.L : ℕ) : ℝ) ≠ 0 := by rw [wS_L_cast]; norm_num
  have hne : ((5 / 4 : ℝ) / (5 / 4) * (((wS.L : ℝ) ^ 1) ^ 2 / ((wS.L : ℝ) ^ 1) ^ 2) : ℝ) = 1 := by
    field_simp
  rw [hne]
  simp
  rfl


/-- The regional field at `xIn` is not zero. -/
theorem psiJ_xIn_ne_zero : ¬ ∀ i, ctxPlg.psiJ Y0 (fun _ => whv) whv 1 xIn i = 0 := by
  intro h
  have h0 := psiJ_xIn 0
  rw [h 0] at h0
  have : (whv 0 : ℝ) = 1 := by simp [whv]
  rw [this] at h0
  norm_num at h0

end Balaban.Inhabited.ProperLocalGen
