/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.History.RetainedShell
public import Balaban.LargeField.Operators.StepData
public import Balaban.LargeField.Characteristic.Stencil
public import Balaban.LargeField.Characteristic.Reg
public import Balaban.LargeField.Def7SmallField

/-!
# Top-scale blocks of the retained shell (Q13-COVER, `TopBlockTransport`)

Geometric half of the package `TopBlockTransport` of `notes/phase1/Q13-COVER.md` §2.  Setting: a
region history `H`, a scale `k = j + 1 ≤ K`, `Y = Z_kᶜ`, the small-field context `Cx : SFCtx`
at scale `k` with generating set `G_k = Cx.genW Y = 𝔹_k(W₂(Y))`, and a component `C` of
`Z^pre_k` not removed at scale `k` (a retained component).  `B = chiDomGen H Cx.geo k C` is
literally the generating set of `ChiDomAt` (the `histGen` of the lineage localization `locRH k C`).

## What is proved

* **Cube level** (no small-field context).  `mem_layer_chiDomGen`: a fine site whose scale-`k`
  cube is within one cube of `C` (and in `Ω_k` of the history if it belongs to `C`) lies in the
  layer `k` of `B`, that is in `Ω_k` but not `Ω_{k+1}` of the localization (the steps of the
  localization at scales `≥ k` have no new cubes, so `Ω_{k+1}(loc)` misses the cubes of
  `U'_k ⊇ C`).  `cube_conditions_of_mem_Omega`: a cube `q` of `C` in `Ω_k` satisfies the two
  conditions of the first family of `ChiDomProp` (`CubeSub … (a.Z k)` and
  `q ∈ lhOmegaSim a k k`), through `locRH_derived` and `locRH_Z`.  `topBlock_mem_genBlocksIn`:
  the top-scale block of such a site lies in `genBlocksIn B k (nbhd 1 {q})`.
  `subMultiscaleField_top_eq_out`: at that block the gate of `subMultiscaleField` is open, the
  block lies in the output set `Vblk`, and the multiscale field is the output variable.
* **T1** (`dataSite_cube_near_W2`, `dataSite_cube_mem_nbhd`, `datum_site_topBlock`,
  `liftSingle_genW_Ψ_top`, `datum_value_eq_tested`).  A datum site `s` of `G_k` lies over a cube
  within `2⌊R_{k-1}⌋ + 3` of `Y` (`dataSites_cube_near` with `12 M₁ ≤ c M₁`, from `Geo.hc`,
  and `W₂(Y) ⊆ nbhd_{2a+2}(Y)`); if that cube `q` lies in a retained component `C`, then
  `q ∈ Ω''_k` (`retained_shell_subset_OmegaDD`), `q` satisfies the two conditions of the first
  family of `ChiDomProp`, and the top-scale block `(k, blkToBlock (jBlock s))` is in
  `genBlocksIn B k (nbhd 1 {q})`.  The datum `liftSingle (Cx.genW Y) (Cx.liftData ψ_k) …` takes
  at `s` the value `ψ_k` at this block (`blkToBlock` is `blockCfgOf`'s cast), and for
  `ψ_k = outField o` this is the value of `subMultiscaleField` that `PsiTildeMulti` tests.
* **T2** (`interface_pair_topBlocks`).  For an `IsInterfacePair` pair `(s, s')` of `G_k` such that
  one of the two sites (`t`) is over a cube `q` of a retained component `C`: the two cubes are
  within one cube; `q` is a valid cube for the first family of `ChiDomProp`; both top-scale
  blocks lie in `genBlocksIn B k (nbhd 1 {q})`; they have the same layer `k` and are adjacent
  (`BlockAdj`).  The other site is arbitrary: collar sites and sites over `Y` are covered, and so
  are collar–collar pairs with one site over `C`.  The pair's layer-`n` blocks are only used to
  produce adjacent sites; the datum is constant on them with value `ψ_k` at the `k`-block.
* **T3** (`psiTildeMulti_of_chiDomProp`, `chiDomAt_site_sphere`, `chiDomAt_pair_bounds`).  Under
  `ChiDomAt` for `C`: `‖ψ_k(b) - ψ_k(b')‖ < 3 d L δ_{k-1}` and
  `|‖ψ_k(b)‖² - 1| < 3 d L δ_{k-1}`, `|‖ψ_k(b')‖² - 1| < 3 d L δ_{k-1}` for the top blocks of an
  interface pair as in T2.  These are the interface condition (R1) and the sphere condition (R2)
  for the data `Ψ` (closeness of neighbouring block values, and of the block value to the sphere).
  They are neither `BlockClose` (`|Ψ - Qφ|`, data against the block average of the solution)
  nor `GradClose` (derivatives of the background).
* **T4** (`chiKProp_of_chiY_ne_zero`, `chiY_ne_zero_blockClose_gradClose`,
  `blockDev_lt_of_chiY_ne_zero`, `cubeData_Ψ_eq_liftSingle_Ψ`).  From `chiY ≠ 0`, for every cube
  `y₀` of `Y`, `RegIneq` of the cube `y₀` gives `BlockClose` (on the sites over `y₀^∼`) and
  `GradClose` (at the sites of `Ω₁(G_k(y₀))` over `y₀^∼`) with tolerance `δ_k`, for the data
  `cubeData` of the cube and the background of the generating set `G_k(y₀) = 𝔹_k(y₀^{∼2})`.  The
  data of the cube and of `G_k` agree at common data sites.  The `InUnionDomainR` conjunct is not
  used.

## What is not proved

* Pairs `(s, s')` with both sites over cubes of `Y`, or over no retained component: T4 gives
  only the site bounds `BlockClose`, `GradClose` for the background of one cube `G_k(y₀)`, which
  is not the background of `G_k`; a bound on `|Ψ(s) - Ψ(s')|` for such pairs needs the difference
  of the block averages `Qφ` of two blocks (not a consequence of `RegIneq`), `GradClose` does not
  cover collar sites (it ranges over `Ω₁`), and the radius in `InUnionDomainR` is only
  existential.  This is the separate bond lift.
* The transfer to the composed inherited fields `ψ^{(j)}_k` of older scales (`psiJ`), which are
  not the multiscale field `ψ_k` of the layer-`k` blocks tested here.
* The strict-margin statements (comparison of the background of `G_k` with the cube backgrounds,
  the eight `StrictData` tests); the numbers `3 d L δ_{k-1}` (here) and `δ_k` (in `chiY`) are
  different tolerances.
* `ActiveFactor`.  Statement (not proved): for every configuration `(o, x)` of the output and of
  the internal variables at which a nonzero integrand of (D1) is evaluated, with the retained
  component `C` of `Z^pre_k` the corresponding localized component operator
  `locOp … k hk C` satisfies `ChiDomAt geo cs H k C o x` (this is what `locOp_vanish_chiDom`
  gives for a nonvanishing kernel value), with `o` the output configuration (the block field
  `ψ_k` read by `SFCtx.liftData` and `chiY` in the same integrand is `outField o`), and the
  background datum of the small-field factor in that integrand is `Cx.liftData (outField o)` on
  `Cx.genW Y`.  With this, `datum_value_eq_tested` identifies the datum values with the values
  tested by `ChiDomProp`.
* Nothing here depends on the mass convention of the backgrounds: only the generating set
  `G_k`, the block fields and the history enter; the mass `Cx.cs.mu` occurs only inside the
  background in T4.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background RegionHistory Balaban.LargeField.Def7

section Core

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ} {M : ℕ} [NeZero M]
  [NeZero S.L] (H : RegionHistory S n R k0 K) (g : Geo S n R M)

/-- The generating set `B = 𝔹_K` of the lineage localization of a component `Z` of `Z^pre_k`, as
it occurs in `ChiDomAt`. -/
noncomputable abbrev chiDomGen (k : ℕ) (Z : H.Comp k) :=
  (H.locRH k Z).histGen (M := M) (K' := K) le_rfl (locRH_rem k Z) H.F.ok.two_le_L
    (fun j _ _ => g.hRlow j)

/-- A fine site whose scale-`(j+1)` cube is within one cube of the component `C` lies in the layer
`j + 1` of `B` (in `Ω_{j+1}` of the lineage localization but not in `Ω_{j+2}`: the top layer) as
soon as, when the cube belongs to `C`, it belongs to `Ω_{j+1}` of the global history.  A cube
outside `C` is in `Ω_{j+1}` of the localization automatically (`Ωᶜ(loc) = Ωᶜ ∩ Lin`). -/
theorem mem_layer_chiDomGen {j : ℕ} (hjK : j + 1 ≤ K) (C : H.Comp (j + 1))
    {x : Torus S.d (M * n K * S.L ^ K)} (hx : cubeMap n S.L M K (j + 1) x ∈ nbhd 1 C.1)
    (hΩ : cubeMap n S.L M K (j + 1) x ∈ C.1 → cubeMap n S.L M K (j + 1) x ∈ (H.step j).Omega) :
    x ∈ (chiDomGen H g (j + 1) C).layer (j + 1) := by
  rw [GeneratingSet.mem_layer]
  unfold chiDomGen
  rw [mem_histGen, mem_histGen]
  refine ⟨⟨hjK, ?_⟩, ?_⟩
  · show _ ∈ ((H.locRH (j + 1) C).step j).Omega
    by_contra h
    have h1 := ((H.locRH_derived C (Nat.lt_succ_self j) (by omega)).2.1).symm
    have h2 : cubeMap n S.L M K (j + 1) x ∈ ((H.locRH (j + 1) C).step j).Omegaᶜ := h
    rw [h1] at h2
    have h3 := h2.2
    rw [Finset.mem_coe, lin_self] at h3
    exact h2.1 (hΩ h3)
  · rintro ⟨hle, h⟩
    have hst : (H.locRH (j + 1) C).step (j + 1) =
        emptyStep S n R (j + 1) (H.tailZ (j + 1) C (j + 1)) := by
      show H.locStep (j + 1) C (j + 1) = _
      unfold locStep
      exact ite_eq_right_of_eq_false _ _ (eq_false fun hh => absurd hh.1 (lt_irrefl _))
    have hZ : H.tailZ (j + 1) C (j + 1) = C.1 := by
      rw [tailZ_eq_lin C le_rfl hjK, lin_self]
    have h2 : cubeMap n S.L M K (j + 1 + 1) x ∈
        (emptyStep S n R (j + 1) (H.tailZ (j + 1) C (j + 1))).Omega := by
      have := h
      simp only [RegionSeq.OmegaAt_succ] at this
      rw [← hst]; exact this
    have h3 : blockMap S.L (n (j + 1 + 1)) (cubeMap n S.L M K (j + 1) x) ∈
        (emptyStep S n R (j + 1) (H.tailZ (j + 1) C (j + 1))).Uprime := by
      refine ⟨cubeMap n S.L M K (j + 1) x, ?_, rfl⟩
      rw [hZ]
      exact nbhd_mono (by omega) subset_rfl hx
    rw [cubeMap_succ H.F.hnn hle x] at h3
    exact ((emptyStep S n R (j + 1) (H.tailZ (j + 1) C (j + 1))).OmegaPrime_compl_subset_Omega_compl
      ((emptyStep S n R (j + 1) (H.tailZ (j + 1) C (j + 1))).Uprime_subset_compl h3)) h2

/-- **`TopBlockTransport` at the level of a cube (the two conditions of the first family of
`ChiDomProp`).**  Let `C` be a component of `Z^pre_{j+1}` and `q` a cube of `C` lying in
`Ω_{j+1}` of the global history (for instance in `Ω''_{j+1}`).  Then `q` is a cube of the
region `Z_{j+1}` of the localized history of `C`, and `q` belongs to `Ω^∼_{j+1}` of the localized
history (it is even a cube of `Ω_{j+1}` of the localized history).  No admissibility and no
retained-ness is used here. -/
theorem cube_conditions_of_mem_Omega {j : ℕ} (hjK : j + 1 ≤ K) (C : H.Comp (j + 1))
    {q : Torus S.d (n (j + 1))} (hq : q ∈ C.1) (hΩ : q ∈ (H.step j).Omega) :
    CubeSub (S := S) (n := n) M K (j + 1) q ((H.localHistory M K (j + 1) C).Z (j + 1)) ∧
      q ∈ lhOmegaSim (H.localHistory M K (j + 1) C) (j + 1) (j + 1) := by
  refine ⟨fun x hx => ⟨?_, ?_⟩, ?_⟩
  · show cubeMap n S.L M K (j + 1) x ∈ ((H.locRH (j + 1) C).step (j + 1)).Z
    rw [locRH_Z C le_rfl hjK, hx]
    simp [lin_self, hq]
  · show cubeMap n S.L M K (j + 1) x ∈ C.1
    rw [hx]; exact hq
  · have hmem : CubeSub (S := S) (n := n) M K (j + 1) q
        (lhOmega (H.localHistory M K (j + 1) C) (j + 1) (j + 1)) := by
      intro x hx
      left
      refine ⟨?_, ?_⟩
      · show cubeMap n S.L M K (j + 1) x ∈ ((H.locRH (j + 1) C).step j).Omega
        by_contra h
        have h1 := ((H.locRH_derived C (Nat.lt_succ_self j) (by omega)).2.1).symm
        have h2 : cubeMap n S.L M K (j + 1) x ∈ ((H.locRH (j + 1) C).step j).Omegaᶜ := h
        rw [h1, hx] at h2
        exact h2.1 hΩ
      · show cubeMap n S.L M K (j + 1) x ∈ C.1
        rw [hx]; exact hq
    unfold lhOmegaSim lhOmegaNb
    rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
    exact mem_nbhd.mpr ⟨q, hmem, by simp [supDist_self]⟩

/-- The tested block: the top-scale block `(j+1, jBlock x)` of a fine site `x` whose scale-`(j+1)`
cube is within one cube of `C` (and in `Ω_{j+1}` if it belongs to `C`) and within one cube of
`q` belongs to `genBlocksIn B (j+1) (nbhd 1 {q})`, where `B` is the generating set of
`ChiDomAt`. -/
theorem topBlock_mem_genBlocksIn {j : ℕ} (hjK : j + 1 ≤ K) (C : H.Comp (j + 1))
    {x : Torus S.d (M * n K * S.L ^ K)} (hx : cubeMap n S.L M K (j + 1) x ∈ nbhd 1 C.1)
    (hΩ : cubeMap n S.L M K (j + 1) x ∈ C.1 → cubeMap n S.L M K (j + 1) x ∈ (H.step j).Omega)
    {q : Torus S.d (n (j + 1))}
    (hxq : supDist (cubeMap n S.L M K (j + 1) x) q ≤ 1) :
    (⟨j + 1, jBlock S.d S.L (M * n K) K (j + 1) x⟩ : BlockPt S n M K) ∈
      genBlocksIn (chiDomGen H g (j + 1) C) (j + 1) (nbhd 1 {q}) :=
  ⟨Nat.succ_pos j, hjK, x, mem_layer_chiDomGen H g hjK C hx hΩ, rfl,
    mem_nbhd.mpr ⟨q, rfl, hxq⟩⟩

/-- **The field tested at a top-scale block is the output field `ψ_{j+1}`.**  For a fine site `x`
whose scale-`(j+1)` cube is within one cube of `C` (and in `Ω_{j+1}` if it belongs to `C`), the
top-scale block `b = jBlock x` lies in the output set `V = Vblk` (so `ψ_{j+1}(b)` is an actual
output variable) and the multiscale field of `ChiDomAt` at `b` is that variable: the gate
`b ⊂ lhOmega` of `subMultiscaleField` is open on `b`. -/
theorem subMultiscaleField_top_eq_out {N j : ℕ} (hjK : j + 1 ≤ K) (C : H.Comp (j + 1))
    {x : Torus S.d (M * n K * S.L ^ K)} (hx : cubeMap n S.L M K (j + 1) x ∈ nbhd 1 C.1)
    (hΩ : cubeMap n S.L M K (j + 1) x ∈ C.1 → cubeMap n S.L M K (j + 1) x ∈ (H.step j).Omega)
    {A : Set (InternalVars (H.localHistory M K (j + 1) C) (j + 1))}
    (o : OutT N R (H.localHistory M K (j + 1) C) (j + 1))
    (xs : SubCfg N (H.localHistory M K (j + 1) C) (j + 1) A) :
    ∃ hV : jBlock S.d S.L (M * n K) K (j + 1) x ∈ Vblk R (H.localHistory M K (j + 1) C) (j + 1),
      subMultiscaleField N (H.localHistory M K (j + 1) C) (j + 1)
          (Vblk R (H.localHistory M K (j + 1) C) (j + 1)) xs o (j + 1)
          (jBlock S.d S.L (M * n K) K (j + 1) x) =
        o ⟨jBlock S.d S.L (M * n K) K (j + 1) x, hV⟩ := by
  have hcube : ∀ x' : Torus S.d (M * n K * S.L ^ K),
      jBlock S.d S.L (M * n K) K (j + 1) x' = jBlock S.d S.L (M * n K) K (j + 1) x →
      cubeMap n S.L M K (j + 1) x' = cubeMap n S.L M K (j + 1) x := by
    intro x' h
    rw [← cubeMap_eq_comp H.F.hnn hjK x', ← cubeMap_eq_comp H.F.hnn hjK x, h]
  have hV : jBlock S.d S.L (M * n K) K (j + 1) x ∈
      Vblk R (H.localHistory M K (j + 1) C) (j + 1) := by
    show blockCube S n M K (j + 1) _ ∈ Vcubes R (H.localHistory M K (j + 1) C) (j + 1)
    unfold blockCube Vcubes
    rw [cubeMap_eq_comp H.F.hnn hjK x]
    refine nbhd_mono le_rfl ?_ hx
    intro q hq
    refine mem_nbhd.mpr ⟨q, ?_, by simp [supDist_self]⟩
    intro x' hx'
    refine ⟨?_, ?_⟩
    · show cubeMap n S.L M K (j + 1) x' ∈ ((H.locRH (j + 1) C).step (j + 1)).Z
      rw [locRH_Z C le_rfl hjK, hx']
      simp [lin_self, hq]
    · show cubeMap n S.L M K (j + 1) x' ∈ C.1
      rw [hx']; exact hq
  refine ⟨hV, ?_⟩
  have hgate : BlockSub (S := S) (n := n) (M := M) (K := K) (j + 1)
      (jBlock S.d S.L (M * n K) K (j + 1) x) (lhOmega (H.localHistory M K (j + 1) C) (j + 1) (j + 1)) := by
    intro x' hx'
    have hc := hcube x' hx'
    by_cases hqC : cubeMap n S.L M K (j + 1) x ∈ C.1
    · left
      refine ⟨?_, ?_⟩
      · show cubeMap n S.L M K (j + 1) x' ∈ ((H.locRH (j + 1) C).step j).Omega
        by_contra h
        have h1 := ((H.locRH_derived C (Nat.lt_succ_self j) (by omega)).2.1).symm
        have h2 : cubeMap n S.L M K (j + 1) x' ∈ ((H.locRH (j + 1) C).step j).Omegaᶜ := h
        rw [h1, hc] at h2
        exact h2.1 (hΩ hqC)
      · show cubeMap n S.L M K (j + 1) x' ∈ C.1
        rw [hc]; exact hqC
    · right
      intro hz
      exact hqC (by have := hz.2; simpa [fineSet, hc] using this)
  unfold subMultiscaleField
  simp only [lt_irrefl, ite_false, dite_true, hgate, or_true, ite_true]
  simp only [outField, hV, dite_true]

end Core

section Casts

theorem blockMap_torusCast {d a b : ℕ} (h : a = b) (N m : ℕ) (x : Torus d a) :
    blockMap N m (torusCast h x) = blockMap N m x := by
  subst h; rfl

theorem torusCast_add_single {d a b : ℕ} (h : a = b) (x : Torus d a) (μ : Fin d) :
    torusCast h (x + Pi.single μ 1) = torusCast h x + Pi.single μ 1 := by
  subst h; rfl

end Casts

section Datum

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ} {M : ℕ} [NeZero M]
  [NeZero S.L] {N m₁ j : ℕ} {ϱ : ℝ} (H : RegionHistory S n R k0 K)
  (Cx : SFCtx S n R M K N (j + 1) m₁ ϱ) {C : H.Comp (j + 1)}

/-- The scale-`(j+1)` cube of a site of the level-`(j+1)` torus of the backgrounds, read on the
fine torus of the history (`bgToFine`). -/
theorem cubeMap_bgToFine (s : BgT Cx.geo (j + 1)) :
    cubeMap n S.L M K (j + 1) (bgToFine Cx.geo Cx.hnn Cx.hkK s) =
      blockMap (S.L ^ (j + 1) * (Cx.geo.c * Cx.geo.M1)) (n (j + 1)) s := by
  have e : S.L ^ (j + 1) * M = S.L ^ (j + 1) * (Cx.geo.c * Cx.geo.M1) :=
    congrArg (fun m => S.L ^ (j + 1) * m) Cx.geo.hM
  unfold cubeMap bgToFine
  rw [e, blockMap_torusCast]

/-- The `(j+1)`-block of a site of the fine torus corresponding to `s` is the block
`blkToBlock` of the `(j+1)`-block of `s` on the level-`(j+1)` torus. -/
theorem jBlock_bgToFine (s : BgT Cx.geo (j + 1)) :
    jBlock S.d S.L (M * n K) K (j + 1) (bgToFine Cx.geo Cx.hnn Cx.hkK s) =
      blkToBlock Cx.geo Cx.hnn Cx.hkK
        (jBlock S.d S.L (Cx.geo.M1 * (Cx.geo.c * n (j + 1))) (j + 1) (j + 1) s) := by
  funext i
  apply ZMod.val_injective
  have hjK : j + 1 ≤ K := Cx.hkK
  have h1 : (jBlock S.d S.L (M * n K) K (j + 1) (bgToFine Cx.geo Cx.hnn Cx.hkK s) i).val =
      ((bgToFine Cx.geo Cx.hnn Cx.hkK s) i).val / S.L ^ (j + 1) := by
    unfold jBlock
    exact blockCoord_val (side_eq hjK) _
  have h2 : (jBlock S.d S.L (Cx.geo.M1 * (Cx.geo.c * n (j + 1))) (j + 1) (j + 1) s i).val =
      (s i).val / S.L ^ (j + 1) := by
    unfold jBlock
    exact blockCoord_val (side_eq le_rfl) _
  have h3 : ∀ {a b : ℕ} (h : a = b) (y : Torus S.d a) (i : Fin S.d), ((torusCast h y) i).val =
      (y i).val := by
    intro a b h y i; subst h; rfl
  rw [h1]
  unfold blkToBlock bgToFine
  rw [h3, h3, h2]

/-- **T1 (a), geometry.**  A datum site `s` of `G_{j+1} = 𝔹_{j+1}(W₂(Y))` lies over a cube of
`𝕋_{j+1}` that is within one cube of a cube of `W₂(Y)`.  The numeric premise is the landed one:
`12 M₁ ≤ c M₁`, from `Geo.hc : 14 ≤ c`, through `dataSites_cube_near`. -/
theorem dataSite_cube_near_W2 (hL : 2 ≤ S.L) (Y : Set (Torus S.d (n (j + 1))))
    {s : BgT Cx.geo (j + 1)} (hs : s ∈ dataSites (Cx.genW Y)) :
    ∃ w ∈ W2 R Y, supDist (blockMap (S.L ^ (j + 1) * (Cx.geo.c * Cx.geo.M1)) (n (j + 1)) s) w ≤ 1 := by
  have hM1 : NeZero Cx.geo.M1 := Cx.geo.neM1
  have hc : 12 * Cx.geo.M1 ≤ Cx.geo.c * Cx.geo.M1 :=
    Nat.mul_le_mul_right _ (by have := Cx.geo.hc; omega)
  have hP : Cx.geo.M1 * (Cx.geo.c * n (j + 1)) * S.L ^ (j + 1) =
      (S.L ^ (j + 1) * (Cx.geo.c * Cx.geo.M1)) * n (j + 1) := by ring
  obtain ⟨y, hy, hd⟩ := dataSites_cube_near (j := j + 1) (q := j + 1) hL (le_refl _)
    (cubePre Cx.geo.M1 (Cx.geo.c * n (j + 1)) S.L (j + 1)
      (S.L ^ (j + 1) * (Cx.geo.c * Cx.geo.M1)) (n (j + 1)) (W2 R Y))
    (G' := Cx.genW Y) (fun z hz => hz) (M := Cx.geo.c * Cx.geo.M1) hc hP hs
  exact ⟨_, mem_cubePre.1 hy, hd⟩

/-- The scale-`(j+1)` cube of a datum site of `G_{j+1}` lies within `2⌊R_j⌋ + 3` of `Y`. -/
theorem dataSite_cube_mem_nbhd (hL : 2 ≤ S.L) (Y : Set (Torus S.d (n (j + 1))))
    {s : BgT Cx.geo (j + 1)} (hs : s ∈ dataSites (Cx.genW Y)) :
    cubeMap n S.L M K (j + 1) (bgToFine Cx.geo Cx.hnn Cx.hkK s) ∈ nbhd (2 * ⌊R j⌋₊ + 3) Y := by
  obtain ⟨w, hw, hd⟩ := dataSite_cube_near_W2 Cx hL Y hs
  obtain ⟨y, hy, hwy⟩ := mem_nbhd.mp (W2_subset_nbhd j Y hw)
  rw [cubeMap_bgToFine]
  exact mem_nbhd.mpr ⟨y, hy, (supDist_triangle _ w y).trans (by omega)⟩

/-- **T1.**  Let `s` be a datum site of `G_{j+1} = C.genW Y`, `Y = Z_{j+1}ᶜ`, whose scale-`(j+1)`
cube `q` lies in a retained component `C` of `Z^pre_{j+1}`.  Then

* (a) `q` is within `2⌊R_j⌋ + 3` of `Y` and lies in `Ω''_{j+1}`;
* (b) `q` is a cube of `Z_{j+1}` of the localized history of `C` and lies in its `Ω^∼_{j+1}`
  (`lhOmegaSim`): the two conditions of the first family of `ChiDomProp` for `y := q`;
* (c) the top-scale block `(j+1, blkToBlock (jBlock s))` of the datum belongs to
  `genBlocksIn B (j+1) (nbhd 1 {q})`, `B` the generating set of `ChiDomAt`
  (`chiDomGen`).  The block is the one at which the datum reads the field
  (`liftSingle_genW_Ψ_top`). -/
theorem datum_site_topBlock (hC : C.1 ∉ H.rem (j + 1))
    {s : BgT Cx.geo (j + 1)} (hs : s ∈ dataSites (Cx.genW ((H.step (j + 1)).Z)ᶜ))
    (hq : cubeMap n S.L M K (j + 1) (bgToFine Cx.geo Cx.hnn Cx.hkK s) ∈ C.1) :
    cubeMap n S.L M K (j + 1) (bgToFine Cx.geo Cx.hnn Cx.hkK s) ∈
        nbhd (2 * ⌊R j⌋₊ + 3) ((H.step (j + 1)).Z)ᶜ ∧
      cubeMap n S.L M K (j + 1) (bgToFine Cx.geo Cx.hnn Cx.hkK s) ∈ (H.step j).OmegaDD ∧
      CubeSub (S := S) (n := n) M K (j + 1)
        (cubeMap n S.L M K (j + 1) (bgToFine Cx.geo Cx.hnn Cx.hkK s))
        ((H.localHistory M K (j + 1) C).Z (j + 1)) ∧
      cubeMap n S.L M K (j + 1) (bgToFine Cx.geo Cx.hnn Cx.hkK s) ∈
        lhOmegaSim (H.localHistory M K (j + 1) C) (j + 1) (j + 1) ∧
      (⟨j + 1, blkToBlock Cx.geo Cx.hnn Cx.hkK
          (jBlock S.d S.L (Cx.geo.M1 * (Cx.geo.c * n (j + 1))) (j + 1) (j + 1) s)⟩ :
          BlockPt S n M K) ∈
        genBlocksIn (chiDomGen H Cx.geo (j + 1) C) (j + 1)
          (nbhd 1 {cubeMap n S.L M K (j + 1) (bgToFine Cx.geo Cx.hnn Cx.hkK s)}) := by
  have hnb := dataSite_cube_mem_nbhd Cx H.F.ok.two_le_L _ hs
  have hDD := H.retained_shell_subset_OmegaDD j hC hq hnb
  have hΩ := (H.step j).OmegaDD_subset_Omega hDD
  obtain ⟨hZ, hsim⟩ := cube_conditions_of_mem_Omega (M := M) H Cx.hkK C hq hΩ
  refine ⟨hnb, hDD, hZ, hsim, ?_⟩
  rw [← jBlock_bgToFine]
  exact topBlock_mem_genBlocksIn H Cx.geo Cx.hkK C (mem_nbhd.mpr ⟨_, hq, by simp [supDist_self]⟩)
    (fun _ => hΩ) (by simp [supDist_self])

/-- The value of the single-scale datum at a data site is the field `ψ_{j+1}` at the top-scale
block `blkToBlock (jBlock s)`: the value tested by `PsiTildeMulti` at that block. -/
theorem liftSingle_genW_Ψ_top (Y : Set (Torus S.d (n (j + 1))))
    (ψk : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N)) (hv : EuclideanSpace ℝ (Fin N))
    {s : BgT Cx.geo (j + 1)} (hs : s ∈ dataSites (Cx.genW Y)) :
    (liftSingle (Cx.genW Y) (Cx.liftData ψk) (hC hv)).Ψ s =
      fun i => ((ψk (blkToBlock Cx.geo Cx.hnn Cx.hkK
        (jBlock S.d S.L (Cx.geo.M1 * (Cx.geo.c * n (j + 1))) (j + 1) (j + 1) s)) i : ℝ) : ℂ) :=
  liftSingle_Ψ (Cx.genW Y) _ _ hs

omit [NeZero M] in
/-- A site of the block `blockSet G s` of a site `s` lies in the same top-scale (`k`-)block
as `s`: the block of layer `n ≤ k` is contained in the `k`-block. -/
theorem jBlock_top_eq_of_mem_blockSet {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}
    (G : GeneratingSet d L N₀ k ϱ) {s y : Torus d (N₀ * L ^ k)} (hy : y ∈ blockSet G s) :
    jBlock d L N₀ k k y = jBlock d L N₀ k k s := by
  unfold blockSet at hy
  by_cases hs : s ∈ G.Ω 1
  · simp only [hs, ↓reduceIte] at hy
    obtain ⟨-, hnk, -⟩ := G.layerIndex_spec hs
    exact jBlock_eq_of_le hnk le_rfl (GeneratingSet.mem_blk.1 hy)
  · simp only [hs, ↓reduceIte, Finset.mem_singleton] at hy
    rw [hy]

/-- **T1 for a neighbouring site.**  Let `t` be a site whose cube `q` lies in the component `C`,
and `u` a datum site of `G_{j+1} = C.genW Y`, `Y = Z_{j+1}ᶜ`, whose cube is within one cube of `q`
(the cube of `u` need not lie in `C`).  Then the top-scale block of `u` lies in
`genBlocksIn B (j+1) (nbhd 1 {q})`. -/
theorem datum_site_block_mem_of_near (hC : C.1 ∉ H.rem (j + 1))
    {t u : BgT Cx.geo (j + 1)} (hu : u ∈ dataSites (Cx.genW ((H.step (j + 1)).Z)ᶜ))
    (hq : cubeMap n S.L M K (j + 1) (bgToFine Cx.geo Cx.hnn Cx.hkK t) ∈ C.1)
    (hd : supDist (cubeMap n S.L M K (j + 1) (bgToFine Cx.geo Cx.hnn Cx.hkK u))
      (cubeMap n S.L M K (j + 1) (bgToFine Cx.geo Cx.hnn Cx.hkK t)) ≤ 1) :
    (⟨j + 1, blkToBlock Cx.geo Cx.hnn Cx.hkK
        (jBlock S.d S.L (Cx.geo.M1 * (Cx.geo.c * n (j + 1))) (j + 1) (j + 1) u)⟩ :
        BlockPt S n M K) ∈
      genBlocksIn (chiDomGen H Cx.geo (j + 1) C) (j + 1)
        (nbhd 1 {cubeMap n S.L M K (j + 1) (bgToFine Cx.geo Cx.hnn Cx.hkK t)}) := by
  rw [← jBlock_bgToFine]
  refine topBlock_mem_genBlocksIn H Cx.geo Cx.hkK C (mem_nbhd.mpr ⟨_, hq, hd⟩) ?_ hd
  intro hqu
  exact (H.step j).OmegaDD_subset_Omega (datum_site_topBlock H Cx hC hu hqu).2.1

/-- **T2.**  Let `(s, s')` be an interface pair of `G_{j+1} = C.genW Y`, `Y = Z_{j+1}ᶜ`, and let
`t ∈ {s, s'}` be a site whose scale-`(j+1)` cube `q` lies in a retained component `C` of
`Z^pre_{j+1}`.  The other site is arbitrary (it may lie over `Y`, or in the collar of `C`).  Then
the two cubes are within one cube of each other, the cube `q` satisfies the two conditions of the
first family of `ChiDomProp` (T1 (b)), both top-scale blocks lie in
`genBlocksIn B (j+1) (nbhd 1 {q})`, have the same layer `j + 1`, and are adjacent (`BlockAdj`).
(Pairs with neither site over a retained component are not covered: see T4.) -/
theorem interface_pair_topBlocks (hC : C.1 ∉ H.rem (j + 1))
    {s s' t : BgT Cx.geo (j + 1)}
    (hp : IsInterfacePair (Cx.genW ((H.step (j + 1)).Z)ᶜ) s s') (hts : t = s ∨ t = s')
    (hq : cubeMap n S.L M K (j + 1) (bgToFine Cx.geo Cx.hnn Cx.hkK t) ∈ C.1) :
    supDist (cubeMap n S.L M K (j + 1) (bgToFine Cx.geo Cx.hnn Cx.hkK s'))
        (cubeMap n S.L M K (j + 1) (bgToFine Cx.geo Cx.hnn Cx.hkK s)) ≤ 1 ∧
      CubeSub (S := S) (n := n) M K (j + 1)
        (cubeMap n S.L M K (j + 1) (bgToFine Cx.geo Cx.hnn Cx.hkK t))
        ((H.localHistory M K (j + 1) C).Z (j + 1)) ∧
      cubeMap n S.L M K (j + 1) (bgToFine Cx.geo Cx.hnn Cx.hkK t) ∈
        lhOmegaSim (H.localHistory M K (j + 1) C) (j + 1) (j + 1) ∧
      (⟨j + 1, blkToBlock Cx.geo Cx.hnn Cx.hkK
          (jBlock S.d S.L (Cx.geo.M1 * (Cx.geo.c * n (j + 1))) (j + 1) (j + 1) s)⟩ :
          BlockPt S n M K) ∈
        genBlocksIn (chiDomGen H Cx.geo (j + 1) C) (j + 1)
          (nbhd 1 {cubeMap n S.L M K (j + 1) (bgToFine Cx.geo Cx.hnn Cx.hkK t)}) ∧
      (⟨j + 1, blkToBlock Cx.geo Cx.hnn Cx.hkK
          (jBlock S.d S.L (Cx.geo.M1 * (Cx.geo.c * n (j + 1))) (j + 1) (j + 1) s')⟩ :
          BlockPt S n M K) ∈
        genBlocksIn (chiDomGen H Cx.geo (j + 1) C) (j + 1)
          (nbhd 1 {cubeMap n S.L M K (j + 1) (bgToFine Cx.geo Cx.hnn Cx.hkK t)}) ∧
      BlockAdj
        (⟨j + 1, blkToBlock Cx.geo Cx.hnn Cx.hkK
          (jBlock S.d S.L (Cx.geo.M1 * (Cx.geo.c * n (j + 1))) (j + 1) (j + 1) s)⟩ :
          BlockPt S n M K)
        (⟨j + 1, blkToBlock Cx.geo Cx.hnn Cx.hkK
          (jBlock S.d S.L (Cx.geo.M1 * (Cx.geo.c * n (j + 1))) (j + 1) (j + 1) s')⟩ :
          BlockPt S n M K) := by
  have hp0 := hp
  obtain ⟨hs, hs', -, y, hy, y', hy', hadj⟩ := hp
  have hy1 := jBlock_top_eq_of_mem_blockSet _ hy
  have hy1' := jBlock_top_eq_of_mem_blockSet _ hy'
  have hm : Cx.geo.c * n (j + 1) * S.L ^ (j + 1 - (j + 1)) = Cx.geo.c * n (j + 1) := by simp
  have e1 := cube_eq_of_jBlock_eq (c := Cx.geo.c) (n := n (j + 1)) hm hy1
  have e2 := cube_eq_of_jBlock_eq (c := Cx.geo.c) (n := n (j + 1)) hm hy1'
  have hP : Cx.geo.M1 * (Cx.geo.c * n (j + 1)) * S.L ^ (j + 1) =
      (S.L ^ (j + 1) * (Cx.geo.c * Cx.geo.M1)) * n (j + 1) := by ring
  have hpos : 1 ≤ S.L ^ (j + 1) * (Cx.geo.c * Cx.geo.M1) := by
    have := NeZero.ne S.L; have := Cx.geo.neM1.out; have := Cx.geo.nec.out
    exact Nat.one_le_iff_ne_zero.2 (by positivity)
  have hd : supDist (blockMap (S.L ^ (j + 1) * (Cx.geo.c * Cx.geo.M1)) (n (j + 1)) y')
      (blockMap (S.L ^ (j + 1) * (Cx.geo.c * Cx.geo.M1)) (n (j + 1)) y) ≤ 1 :=
    supDist_blockMap_le_one hP (D := 1) hpos y' y (Adj.supDist_le_one hadj.symm)
  have hcube : supDist (cubeMap n S.L M K (j + 1) (bgToFine Cx.geo Cx.hnn Cx.hkK s'))
      (cubeMap n S.L M K (j + 1) (bgToFine Cx.geo Cx.hnn Cx.hkK s)) ≤ 1 := by
    rw [cubeMap_bgToFine, cubeMap_bgToFine, ← e1, ← e2]; exact hd
  have hcube' : supDist (cubeMap n S.L M K (j + 1) (bgToFine Cx.geo Cx.hnn Cx.hkK s))
      (cubeMap n S.L M K (j + 1) (bgToFine Cx.geo Cx.hnn Cx.hkK s')) ≤ 1 := by
    rw [supDist_comm]; exact hcube
  have ht : t ∈ dataSites (Cx.genW ((H.step (j + 1)).Z)ᶜ) := by
    rcases hts with rfl | rfl <;> assumption
  obtain ⟨-, -, hZ, hsim, -⟩ := datum_site_topBlock H Cx hC ht hq
  have hself : supDist (cubeMap n S.L M K (j + 1) (bgToFine Cx.geo Cx.hnn Cx.hkK t))
      (cubeMap n S.L M K (j + 1) (bgToFine Cx.geo Cx.hnn Cx.hkK t)) ≤ 1 := by
    simp [supDist_self]
  refine ⟨hcube, hZ, hsim, ?_, ?_, ?_⟩
  · rcases hts with rfl | rfl
    · exact datum_site_block_mem_of_near H Cx hC hs hq hself
    · exact datum_site_block_mem_of_near H Cx hC hs hq hcube'
  · rcases hts with rfl | rfl
    · exact datum_site_block_mem_of_near H Cx hC hs' hq hcube
    · exact datum_site_block_mem_of_near H Cx hC hs' hq hself
  · refine ⟨bgToFine Cx.geo Cx.hnn Cx.hkK y, bgToFine Cx.geo Cx.hnn Cx.hkK y', ?_, ?_, ?_⟩
    · show jBlock S.d S.L (M * n K) K (j + 1) _ = _
      rw [jBlock_bgToFine, hy1]
    · show jBlock S.d S.L (M * n K) K (j + 1) _ = _
      rw [jBlock_bgToFine, hy1']
    · obtain ⟨μ, h | h⟩ := hadj
      · exact ⟨μ, Or.inl (by unfold bgToFine; rw [h, torusCast_add_single])⟩
      · exact ⟨μ, Or.inr (by unfold bgToFine; rw [h, torusCast_add_single])⟩

/-- **T1 (c), the values agree.**  For a datum site `s` as in `datum_site_topBlock` and an output
configuration `o`, the single-scale datum of `G_{j+1}` built from the output field
`ψ_{j+1} = outField o` takes at `s` the value of the multiscale field of `ChiDomAt` at the
top-scale block of `s`, i.e. the value tested by `PsiTildeMulti` in `genBlocksIn`. -/
theorem datum_value_eq_tested {C : H.Comp (j + 1)} (hret : C.1 ∉ H.rem (j + 1))
    {A : Set (InternalVars (H.localHistory M K (j + 1) C) (j + 1))}
    (o : OutT N R (H.localHistory M K (j + 1) C) (j + 1))
    (xs : SubCfg N (H.localHistory M K (j + 1) C) (j + 1) A) (hv : EuclideanSpace ℝ (Fin N))
    {s : BgT Cx.geo (j + 1)} (hs : s ∈ dataSites (Cx.genW ((H.step (j + 1)).Z)ᶜ))
    (hq : cubeMap n S.L M K (j + 1) (bgToFine Cx.geo Cx.hnn Cx.hkK s) ∈ C.1) :
    (liftSingle (Cx.genW ((H.step (j + 1)).Z)ᶜ)
        (Cx.liftData (outField N o)) (hC hv)).Ψ s =
      fun i => ((subMultiscaleField N (H.localHistory M K (j + 1) C) (j + 1)
          (Vblk R (H.localHistory M K (j + 1) C) (j + 1)) xs o (j + 1)
          (blkToBlock Cx.geo Cx.hnn Cx.hkK
            (jBlock S.d S.L (Cx.geo.M1 * (Cx.geo.c * n (j + 1))) (j + 1) (j + 1) s)) i : ℝ) : ℂ) := by
  have hnb := dataSite_cube_mem_nbhd Cx H.F.ok.two_le_L _ hs
  have hΩ := (H.step j).OmegaDD_subset_Omega (H.retained_shell_subset_OmegaDD j hret hq hnb)
  obtain ⟨hV, hfield⟩ := subMultiscaleField_top_eq_out (R := R) H Cx.hkK C
    (x := bgToFine Cx.geo Cx.hnn Cx.hkK s) (mem_nbhd.mpr ⟨_, hq, by simp [supDist_self]⟩)
    (fun _ => hΩ) o xs
  have e := jBlock_bgToFine Cx s
  have hV' : blkToBlock Cx.geo Cx.hnn Cx.hkK
      (jBlock S.d S.L (Cx.geo.M1 * (Cx.geo.c * n (j + 1))) (j + 1) (j + 1) s) ∈
      Vblk R (H.localHistory M K (j + 1) C) (j + 1) := e ▸ hV
  have hgen : ∀ (b : BlockAt S n M K (j + 1))
      (hb : b ∈ Vblk R (H.localHistory M K (j + 1) C) (j + 1)),
      jBlock S.d S.L (M * n K) K (j + 1) (bgToFine Cx.geo Cx.hnn Cx.hkK s) = b →
      subMultiscaleField N (H.localHistory M K (j + 1) C) (j + 1)
        (Vblk R (H.localHistory M K (j + 1) C) (j + 1)) xs o (j + 1) b = o ⟨b, hb⟩ := by
    intro b hb e'
    subst e'
    exact hfield
  have hfield' := hgen _ hV' e
  rw [liftSingle_genW_Ψ_top Cx _ (outField N o) hv hs, hfield']
  funext i
  simp [outField, hV']

end Datum

section Factor

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ} {M : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {ϱ : ℝ}

/-- **T3, the factor.**  The first family of `ChiDomProp` at `j + 1 = k` applied at a cube `q`
satisfying the two conditions of T1 (b) / T2 gives `Ψ̃(𝔹_k ∩ q^∼; 3 d L δ_j)` for the multiscale
field. -/
theorem psiTildeMulti_of_chiDomProp {a : LocalHistory S n M K} {j : ℕ}
    {B : GeneratingSet S.d S.L (M * n K) K ϱ} {Zc : Set (Torus S.d (M * n K * S.L ^ K))}
    {δ p0 : ℕ → ℝ} {Cpsi : ℝ} {ψ ψ' : MultiField S n M K N}
    (h : ChiDomProp a (j + 1) B Zc δ p0 Cpsi ψ ψ') {q : Torus S.d (n (j + 1))}
    (hZ : CubeSub (S := S) (n := n) M K (j + 1) q (a.Z (j + 1)))
    (hsim : q ∈ lhOmegaSim a (j + 1) (j + 1)) :
    PsiTildeMulti ψ (genBlocksIn B (j + 1) (nbhd 1 {q})) (3 * S.d * S.L * δ j) :=
  h.1 j (Nat.lt_succ_self j) q hZ hsim

/-- **T3, the inequalities on the blocks of a datum site.**  If `ChiDomAt` holds for the
component `C` and `s` is a datum site over a cube of `C` as in T1, the multiscale field satisfies
the sphere condition (R2 for the data) `|‖ψ_{j+1}(b)‖² - 1| < 3 d L δ_j` at the top-scale block
`b = blkToBlock (jBlock s)` of the datum; by `liftSingle_genW_Ψ_top` this is the value of the
datum `Ψ(s)`.  (The first conjunct of `PsiTildeMulti` is about pairs of blocks, T3 for pairs
below.) -/
theorem chiDomAt_site_sphere {m₁ j : ℕ}
    {H : RegionHistory S n R k0 K} (Cx : SFCtx S n R M K N (j + 1) m₁ ϱ) {C : H.Comp (j + 1)}
    (cs : OpConsts) {A : Set (InternalVars (H.localHistory M K (j + 1) C) (j + 1))}
    {o : OutT N R (H.localHistory M K (j + 1) C) (j + 1)}
    {x : SubCfg N (H.localHistory M K (j + 1) C) (j + 1) A}
    (hχ : ChiDomAt Cx.geo cs H (j + 1) C o x) (hC : C.1 ∉ H.rem (j + 1))
    {s : BgT Cx.geo (j + 1)} (hs : s ∈ dataSites (Cx.genW ((H.step (j + 1)).Z)ᶜ))
    (hq : cubeMap n S.L M K (j + 1) (bgToFine Cx.geo Cx.hnn Cx.hkK s) ∈ C.1) :
    |‖subMultiscaleField N (H.localHistory M K (j + 1) C) (j + 1)
          (Vblk R (H.localHistory M K (j + 1) C) (j + 1)) x o (j + 1)
        (blkToBlock Cx.geo Cx.hnn Cx.hkK
          (jBlock S.d S.L (Cx.geo.M1 * (Cx.geo.c * n (j + 1))) (j + 1) (j + 1) s))‖ ^ 2 - 1| <
      3 * S.d * S.L * cs.delta j := by
  obtain ⟨-, -, hZ, hsim, hb⟩ := datum_site_topBlock H Cx hC hs hq
  have h : ChiDomProp (H.localHistory M K (j + 1) C) (j + 1) (chiDomGen H Cx.geo (j + 1) C)
      (fineSet (S := S) (n := n) M K (j + 1) (C.1 : Set (Torus S.d (n (j + 1))))) cs.delta cs.p0
      cs.Cpsi (subMultiscaleField N (H.localHistory M K (j + 1) C) (j + 1)
        (Vblk R (H.localHistory M K (j + 1) C) (j + 1)) x o)
      (subFluctField N (H.localHistory M K (j + 1) C) (j + 1) x) := hχ
  have key := (psiTildeMulti_of_chiDomProp h hZ hsim).2 _ hb
  dsimp only at key
  exact key

/-- **T3, the inequalities on the blocks of an interface pair.**  Under `ChiDomAt` for the
component `C`, for an interface pair `(s, s')` of `G_{j+1}` with `t ∈ {s, s'}` over a cube of `C`
(T2), the multiscale field at the two top-scale blocks `b, b'` of the pair satisfies

* `‖ψ_{j+1}(b) - ψ_{j+1}(b')‖ < 3 d L δ_j` (the interface condition (R1) for the data, between
  the values of the datum at the two sites by `liftSingle_genW_Ψ_top`),
* `|‖ψ_{j+1}(b)‖² - 1| < 3 d L δ_j` and the same for `b'` (the sphere condition (R2)).

These are conditions on the data `Ψ` (closeness of neighbouring block values and of the block
value to the sphere), not `BlockClose` (`|Ψ - Qφ|`, a comparison of the data with the block
average of the background solution) and not `GradClose` (derivatives of the background). -/
theorem chiDomAt_pair_bounds {m₁ j : ℕ}
    {H : RegionHistory S n R k0 K} (Cx : SFCtx S n R M K N (j + 1) m₁ ϱ) {C : H.Comp (j + 1)}
    (cs : OpConsts) {A : Set (InternalVars (H.localHistory M K (j + 1) C) (j + 1))}
    {o : OutT N R (H.localHistory M K (j + 1) C) (j + 1)}
    {x : SubCfg N (H.localHistory M K (j + 1) C) (j + 1) A}
    (hχ : ChiDomAt Cx.geo cs H (j + 1) C o x) (hC : C.1 ∉ H.rem (j + 1))
    {s s' t : BgT Cx.geo (j + 1)}
    (hp : IsInterfacePair (Cx.genW ((H.step (j + 1)).Z)ᶜ) s s') (hts : t = s ∨ t = s')
    (hq : cubeMap n S.L M K (j + 1) (bgToFine Cx.geo Cx.hnn Cx.hkK t) ∈ C.1) :
    let ψ := subMultiscaleField N (H.localHistory M K (j + 1) C) (j + 1)
      (Vblk R (H.localHistory M K (j + 1) C) (j + 1)) x o
    let b := blkToBlock Cx.geo Cx.hnn Cx.hkK
      (jBlock S.d S.L (Cx.geo.M1 * (Cx.geo.c * n (j + 1))) (j + 1) (j + 1) s)
    let b' := blkToBlock Cx.geo Cx.hnn Cx.hkK
      (jBlock S.d S.L (Cx.geo.M1 * (Cx.geo.c * n (j + 1))) (j + 1) (j + 1) s')
    ‖ψ (j + 1) b - ψ (j + 1) b'‖ < 3 * S.d * S.L * cs.delta j ∧
      |‖ψ (j + 1) b‖ ^ 2 - 1| < 3 * S.d * S.L * cs.delta j ∧
      |‖ψ (j + 1) b'‖ ^ 2 - 1| < 3 * S.d * S.L * cs.delta j := by
  intro ψ b b'
  obtain ⟨-, hZ, hsim, hb, hb', hadj⟩ := interface_pair_topBlocks H Cx hC hp hts hq
  have hχ' : ChiDomProp (H.localHistory M K (j + 1) C) (j + 1) (chiDomGen H Cx.geo (j + 1) C)
      (fineSet (S := S) (n := n) M K (j + 1) (C.1 : Set (Torus S.d (n (j + 1))))) cs.delta cs.p0
      cs.Cpsi (subMultiscaleField N (H.localHistory M K (j + 1) C) (j + 1)
        (Vblk R (H.localHistory M K (j + 1) C) (j + 1)) x o)
      (subFluctField N (H.localHistory M K (j + 1) C) (j + 1) x) := hχ
  have h := psiTildeMulti_of_chiDomProp hχ' hZ hsim
  have key := (⟨h.1 _ hb _ hb' (Or.inl rfl) hadj, h.2 _ hb, h.2 _ hb'⟩ : _ ∧ _ ∧ _)
  dsimp only at key ⊢
  exact key

end Factor

section Small

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N m₁ j : ℕ} {ϱ : ℝ} (Cx : SFCtx S n R M K N (j + 1) m₁ ϱ)

/-- **T4, the cube conditions.**  If `χ_{j+1}(Y) ≠ 0` (it is a product of indicator functions
over the cubes of `Y`, `SFCtx.chiY`), then for every cube `y₀` of `Y` the condition `χ_{j+1}(y₀)`
holds: `Reg_{j+1}(G_{j+1}(y₀), lift ψ_{j+1}, δ_{j+1}; T(y₀^∼), S(y₀^∼))` for the data
`cubeData` of the cube, with the block field `blockCfgOf ψ_{j+1}` of the history. -/
theorem chiKProp_of_chiY_ne_zero (Y : Set (Torus S.d (n (j + 1))))
    (ψk : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N)) (hv : EuclideanSpace ℝ (Fin N))
    (h : Cx.chiY Y ψk hv ≠ 0) {y₀ : Torus S.d (n (j + 1))} (hy₀ : y₀ ∈ cubeFin Y) :
    ChiKProp (M1 := Cx.geo.M1) (N₁ := Cx.geo.c * n (j + 1)) (L := S.L) (q := j + 1) (N := N)
      Cx.weights (Cx.cs.mu (j + 1)) (Cx.cs.delta (j + 1)) (fun i => hv i) Cx.geo.c (n (j + 1)) y₀
      (blockCfgOf Cx.geo Cx.hnn le_rfl Cx.hkK ψk) := by
  by_contra hP
  apply (Finset.prod_ne_zero_iff.1 h) y₀ hy₀
  exact charFn_eq_zero hP

/-- **T4, `BlockClose` and `GradClose`.**  Under `χ_{j+1}(Y) ≠ 0`, for a cube `y₀` of `Y`, the
data `Ψ = lift ψ_{j+1}` of the single cube `y₀` and the background `φ` of the generating set
`G_{j+1}(y₀) = 𝔹_{j+1}(y₀^{∼2})` satisfy `|Ψ(x) - (Qφ)(x)| < δ_{j+1}` (`BlockClose`) on the sites
`x` over the cubes of `y₀^∼`, and `ℓ|∂φ̄|, ℓ²|Δφ̄|, ℓ²|α| < δ_{j+1}` (`GradClose`) at the sites of
`Ω₁(G_{j+1}(y₀))` over those cubes.  Both statements concern the background of the cube
`G_{j+1}(y₀)`, not the background of `G_{j+1}`; the `InUnionDomainR` conjunct of `Reg` is not used. -/
theorem chiY_ne_zero_blockClose_gradClose (Y : Set (Torus S.d (n (j + 1))))
    (ψk : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N)) (hv : EuclideanSpace ℝ (Fin N))
    (h : Cx.chiY Y ψk hv ≠ 0) {y₀ : Torus S.d (n (j + 1))} (hy₀ : y₀ ∈ cubeFin Y) :
    BlockClose
        (genCube (M1 := Cx.geo.M1) (N₁ := Cx.geo.c * n (j + 1)) (L := S.L) (q := j + 1)
          Cx.geo.c (n (j + 1)) y₀)
        (cubeData (M1 := Cx.geo.M1) (N₁ := Cx.geo.c * n (j + 1)) (L := S.L) (q := j + 1)
          (fun i => hv i) Cx.geo.c (n (j + 1)) y₀ (blockCfgOf Cx.geo Cx.hnn le_rfl Cx.hkK ψk))
        (bgFieldC
          (genCube (M1 := Cx.geo.M1) (N₁ := Cx.geo.c * n (j + 1)) (L := S.L) (q := j + 1)
            Cx.geo.c (n (j + 1)) y₀)
          Cx.weights (Cx.cs.mu (j + 1)) (bgC0 S.d S.L N)
          (cubeData (M1 := Cx.geo.M1) (N₁ := Cx.geo.c * n (j + 1)) (L := S.L) (q := j + 1)
            (fun i => hv i) Cx.geo.c (n (j + 1)) y₀
            (blockCfgOf Cx.geo Cx.hnn le_rfl Cx.hkK ψk)))
        (cubeNbhd Cx.geo.M1 (Cx.geo.c * n (j + 1)) S.L (j + 1) Cx.geo.c (n (j + 1)) 1 y₀)
        (Cx.cs.delta (j + 1)) ∧
      GradClose
        (genCube (M1 := Cx.geo.M1) (N₁ := Cx.geo.c * n (j + 1)) (L := S.L) (q := j + 1)
          Cx.geo.c (n (j + 1)) y₀)
        (cubeData (M1 := Cx.geo.M1) (N₁ := Cx.geo.c * n (j + 1)) (L := S.L) (q := j + 1)
          (fun i => hv i) Cx.geo.c (n (j + 1)) y₀ (blockCfgOf Cx.geo Cx.hnn le_rfl Cx.hkK ψk))
        (bgFieldC
          (genCube (M1 := Cx.geo.M1) (N₁ := Cx.geo.c * n (j + 1)) (L := S.L) (q := j + 1)
            Cx.geo.c (n (j + 1)) y₀)
          Cx.weights (Cx.cs.mu (j + 1)) (bgC0 S.d S.L N)
          (cubeData (M1 := Cx.geo.M1) (N₁ := Cx.geo.c * n (j + 1)) (L := S.L) (q := j + 1)
            (fun i => hv i) Cx.geo.c (n (j + 1)) y₀
            (blockCfgOf Cx.geo Cx.hnn le_rfl Cx.hkK ψk)))
        (bgMultC
          (genCube (M1 := Cx.geo.M1) (N₁ := Cx.geo.c * n (j + 1)) (L := S.L) (q := j + 1)
            Cx.geo.c (n (j + 1)) y₀)
          Cx.weights (Cx.cs.mu (j + 1)) (bgC0 S.d S.L N)
          (cubeData (M1 := Cx.geo.M1) (N₁ := Cx.geo.c * n (j + 1)) (L := S.L) (q := j + 1)
            (fun i => hv i) Cx.geo.c (n (j + 1)) y₀
            (blockCfgOf Cx.geo Cx.hnn le_rfl Cx.hkK ψk)))
        ((S.L : ℝ) ^ (j + 1))
        (cubeNbhd Cx.geo.M1 (Cx.geo.c * n (j + 1)) S.L (j + 1) Cx.geo.c (n (j + 1)) 1 y₀)
        (Cx.cs.delta (j + 1)) :=
  let hK := chiKProp_of_chiY_ne_zero Cx Y ψk hv h hy₀
  ⟨hK.2.1, hK.2.2.1⟩

/-- **T4, the datum sites over the stencil.**  Under `χ_{j+1}(Y) ≠ 0`, for a cube `y₀` of `Y` and
a site `s` of the level-`(j+1)` torus (in particular any datum site of `G_{j+1}`) over a cube
within one cube of `y₀`, `|Ψ(s) - (Qφ)(s)| < δ_{j+1}` for the data and background of the
cube `y₀`. -/
theorem blockDev_lt_of_chiY_ne_zero (Y : Set (Torus S.d (n (j + 1))))
    (ψk : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N)) (hv : EuclideanSpace ℝ (Fin N))
    (h : Cx.chiY Y ψk hv ≠ 0) {y₀ : Torus S.d (n (j + 1))} (hy₀ : y₀ ∈ cubeFin Y)
    {s : BgT Cx.geo (j + 1)}
    (hs : blockMap (S.L ^ (j + 1) * (Cx.geo.c * Cx.geo.M1)) (n (j + 1)) s ∈ nbhd 1 {y₀}) :
    blockDev
        (genCube (M1 := Cx.geo.M1) (N₁ := Cx.geo.c * n (j + 1)) (L := S.L) (q := j + 1)
          Cx.geo.c (n (j + 1)) y₀)
        (cubeData (M1 := Cx.geo.M1) (N₁ := Cx.geo.c * n (j + 1)) (L := S.L) (q := j + 1)
          (fun i => hv i) Cx.geo.c (n (j + 1)) y₀ (blockCfgOf Cx.geo Cx.hnn le_rfl Cx.hkK ψk))
        (bgFieldC
          (genCube (M1 := Cx.geo.M1) (N₁ := Cx.geo.c * n (j + 1)) (L := S.L) (q := j + 1)
            Cx.geo.c (n (j + 1)) y₀)
          Cx.weights (Cx.cs.mu (j + 1)) (bgC0 S.d S.L N)
          (cubeData (M1 := Cx.geo.M1) (N₁ := Cx.geo.c * n (j + 1)) (L := S.L) (q := j + 1)
            (fun i => hv i) Cx.geo.c (n (j + 1)) y₀
            (blockCfgOf Cx.geo Cx.hnn le_rfl Cx.hkK ψk))) s < Cx.cs.delta (j + 1) :=
  (chiY_ne_zero_blockClose_gradClose Cx Y ψk hv h hy₀).1 s (mem_cubePre.2 hs)

/-- The data of the cube `y₀` and the data of `G_{j+1}` coincide at a site which is a data site of
both: both read `ψ_{j+1}` at the top-scale block of the site. -/
theorem cubeData_Ψ_eq_liftSingle_Ψ (Y : Set (Torus S.d (n (j + 1))))
    (ψk : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N)) (hv : EuclideanSpace ℝ (Fin N))
    (y₀ : Torus S.d (n (j + 1))) {s : BgT Cx.geo (j + 1)}
    (hs₁ : s ∈ dataSites (genCube (M1 := Cx.geo.M1) (N₁ := Cx.geo.c * n (j + 1)) (L := S.L)
      (q := j + 1) Cx.geo.c (n (j + 1)) y₀))
    (hs₂ : s ∈ dataSites (Cx.genW Y)) :
    (cubeData (M1 := Cx.geo.M1) (N₁ := Cx.geo.c * n (j + 1)) (L := S.L) (q := j + 1)
        (fun i => hv i) Cx.geo.c (n (j + 1)) y₀ (blockCfgOf Cx.geo Cx.hnn le_rfl Cx.hkK ψk)).Ψ s =
      (liftSingle (Cx.genW Y) (Cx.liftData ψk) (hC hv)).Ψ s := by
  unfold cubeData
  rw [liftSingle_Ψ _ _ _ hs₁, liftSingle_Ψ _ _ _ hs₂]
  rfl

end Small

end Balaban.LargeField
