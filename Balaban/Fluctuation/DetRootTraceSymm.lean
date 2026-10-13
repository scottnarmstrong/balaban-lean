/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.DetDecCovSymm
public import Balaban.Fluctuation.DetActivitySymm

/-!
# Covariance of the root trace and of the determinant activities under lattice symmetries

Let `S : LatSymm G G σ`, `hU : UnitBlockPres σ`, `CS : CoverSymm (coverOf G) σ` and
`u = unitAct G S hU` the induced permutation of the unit points.  From the covariance of the
decoupled logarithm (`DetDecCov.decLog_rm`) the diagonal trace over the transported unit root
satisfies exactly the hypothesis `hRT` of `detActivityBg_sym_of_rootTrace`:

`rootTrace {u y} (CS.par s) (symSite σ φ) (S.mul α) = rootTrace {y} s φ α`

(`rootTrace_unitAct`, `hRT_unitAct`).  Together with the identity `rootIdxOf (u y) = rootAct σ
(rootIdxOf y)` for a paving symmetry (`rootIdxOf_unitAct`) this gives the covariance of the
determinant activities (`detActivityBg_sym`) with the remaining premises of
`detActivityBg_sym_of_rootTrace` (paving membership and patch covariance).

Covariance of the CLASS terms (after the collar regrouping, on the class domain) is NOT proved
here.  The statements are not chart-sensitive and independent of the choice of generator.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.Analysis
  Balaban.SmallField Balaban.SmallField.Def6 Balaban.Localization.DecEquiv
  Balaban.Localization.DetUnitIncidence Balaban.Localization.DetDecCov Finset Matrix

section Trace

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} {σ : Equiv.Perm (CTorus d L N₁ m₁ (k + 1))}
variable (S : LatSymm G G σ) (hU : UnitBlockPres σ) (CS : CoverSymm (coverOf G) σ)

include S hU CS in
/-- **T3. The root trace over the transported unit root is unchanged**: for the induced
permutation `u = unitAct G S hU` of the unit points,
`rootTrace {u y} (CS.par s) (σ-transported φ) (S.mul α) = rootTrace {y} s φ α`. -/
theorem rootTrace_unitAct (a : ℕ → ℝ) (aT ν : ℝ) (y : unitPts G) (s : DecParams G)
    (φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) (α : G.Ω 1 → ℂ) :
    rootTrace G a aT ν (unitQ G) (unitP G) {unitAct G S hU y} (CS.par s) (symSite σ φ)
        (S.mul α) =
      rootTrace G a aT ν (unitQ G) (unitP G) {y} s φ α := by
  unfold rootTrace
  simp only [Finset.sum_singleton]
  refine congrArg (fun t => -(1 / 2 : ℂ) * t) (Finset.sum_congr rfl fun i _ => ?_)
  have h : decLog G a aT ν (S.mul α) (extS G (CS.par s)) (symSite σ φ) (unitQ G) (unitP G) =
      rm ((unitAct G S hU).prodCongr (Equiv.refl (Fin N)))
        (decLog G a aT ν α (extS G s) φ (unitQ G) (unitP G)) := decLog_rm S hU CS a aT ν α s φ
  rw [h]
  exact rm_apply ((unitAct G S hU).prodCongr (Equiv.refl (Fin N)))
    (decLog G a aT ν α (extS G s) φ (unitQ G) (unitP G)) (y, i) (y, i)

end Trace

/-! ### The root of the transported unit point -/

section Root

variable {d L N₁ m₁ k : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ} {m₀ : ℕ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} {σ : Equiv.Perm (CTorus d L N₁ m₁ (k + 1))}

/-- Two sites with the same block base have the same root index. -/
theorem blockIndex_eq_of_blockBase_eq {K : ℕ} {w w' : CTorus d L N₁ m₁ K}
    (h : blockBase (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L K w =
      blockBase (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L K w') :
    blockIndex w = blockIndex w' :=
  rootSite_injective (by rw [rootSite_blockIndex, rootSite_blockIndex, h])

/-- A paving symmetry sends the root of the block of `x` into the block of `σ x`. -/
theorem blockIndex_image_root {K : ℕ} {r : Equiv.Perm (CTorus d L N₁ m₁ K)}
    (hr : r ∈ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L m₀ K)
    (x : CTorus d L N₁ m₁ K) :
    blockIndex (r (rootSite (blockIndex x))) = blockIndex (r x) := by
  have hL : 0 < L ^ K := Nat.pos_of_ne_zero (NeZero.ne _)
  have h1 := image_box_blockBase (m₀ := m₀) hr (rootSite (blockIndex x))
  rw [blockBase_rootSite] at h1
  have hx : x ∈ box (rootSite (blockIndex x)) (L ^ K) := by
    rw [rootSite_blockIndex]; exact mem_box_cbase hL x
  have hrx : r x ∈ box (blockBase (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L K
      (r (rootSite (blockIndex x)))) (L ^ K) := h1 ▸ ⟨x, hx, rfl⟩
  have := cbase_eq_of_mem_box pow_dvd_torus (aligned_cbase _) hrx
  exact (blockIndex_eq_of_blockBase_eq this).symm

/-- **The root of the transported unit point**: for a lattice symmetry which is a paving
symmetry, `rootIdxOf (u y) = rootAct σ (rootIdxOf y)` with `u = unitAct G S hU`. -/
theorem rootIdxOf_unitAct (S : LatSymm G G σ) (hU : UnitBlockPres σ)
    (hσ : σ ∈ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L m₀ (k + 1))
    (y : unitPts G) :
    rootIdxOf (unitAct G S hU y) = rootAct σ (rootIdxOf y) := by
  obtain ⟨x, -, hx⟩ := (mem_unitPts G).1 y.2
  rw [rootIdxOf_eq hx, rootIdxOf_eq ((unitBlock_unitAct_iff G S hU y x).2 hx)]
  unfold rootAct
  exact (blockIndex_image_root (m₀ := m₀) hσ x).symm

end Root

/-! ### The hypothesis `hRT` and the covariance of the activities -/

section Activity

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ} {m₀ : ℕ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} {a : ℕ → ℝ} {aT ν : ℝ}
  {σ : Equiv.Perm (CTorus d L N₁ m₁ (k + 1))}
  (S : LatSymm G G σ) (hU : UnitBlockPres σ) (CS : CoverSymm (coverOf G) σ)

include S hU CS in
/-- **The hypothesis `hRT` of `detActivityBg_sym_of_rootTrace`, proved** for the transported unit
root `u y`, `u = unitAct G S hU`. -/
theorem hRT_unitAct (y : unitPts G) :
    ∀ (I : Finset (cubeIdx G)) (φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) (α : G.Ω 1 → ℂ),
      rootTrace G a aT ν (unitQ G) (unitP G) {unitAct G S hU y} (CS.par (cutPt I))
          (symSite σ φ) (S.mul α) =
        rootTrace G a aT ν (unitQ G) (unitP G) {y} (cutPt I) φ α :=
  fun _ φ α => rootTrace_unitAct S hU CS a aT ν y _ φ α

variable (B : BlockSymm G σ)

include B in
open Classical in
/-- **T4. Covariance of the determinant activities.**  `detActivityBg (σ D) (u y) (σ • Y) =
detActivityBg D y Y` for a lattice symmetry `σ` of the generating set which preserves the unit
blocks (`hU`), is compatible with the cover and the blocks (`CS`, `B`), and is a symmetry of the
paving `π_{k+1}` mapping the cube of each parameter `q` onto the cube of `CS.τ q`
(`hpset`).  Here `u = unitAct G S hU`. -/
theorem detActivityBg_sym (hN : L ^ m₀ ∣ N₁)
    (hσ : σ ∈ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L m₀ (k + 1))
    (hpset : ∀ q ∈ cubeIdx G, Pset m₁ (CS.τ q) = σ '' Pset m₁ q)
    (y : unitPts G) (ρ : ℝ) (D : BgData G N)
    (Y : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ)) :
    detActivityBg m₀ a aT ν ρ (S.sym D) (unitAct G S hU y) (cubeAct σ Y) =
      detActivityBg m₀ a aT ν ρ D y Y :=
  detActivityBg_sym_of_rootTrace S CS B hN hσ hpset (rootIdxOf_unitAct S hU hσ y)
    (hRT_unitAct S hU CS y) ρ D Y

end Activity

section Block

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ} {m₀ : ℕ}
  {σ : Equiv.Perm (CTorus d L N₁ m₁ (k + 1))} (St : StepSetting d L N₁ m₁ k N ϱ)
  (S : LatSymm St.G' St.G' σ) (hU : UnitBlockPres σ) (CS : CoverSymm (coverOf St.G') σ)
  (B : BlockSymm St.G' σ)

include S hU CS B in
open Classical in
/-- **T4. Covariance of the terms of a block**, in the form `e' (σ z) (σ • T) = e z T` used for
the terms of `DetExpansionLocC`: the sums of the determinant activities over the unit blocks of
`B(σ z)` and of `B(z)` agree, with the data `σ D` on the left. -/
theorem sum_detActivityBg_sym (hN : L ^ m₀ ∣ N₁)
    (hσ : σ ∈ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L m₀ (k + 1))
    (hpset : ∀ q ∈ cubeIdx St.G', Pset m₁ (CS.τ q) = σ '' Pset m₁ q)
    {ρ : ℝ} (D : BgData St.G' N) (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))))
    (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ)) :
    ∑ y' ∈ St.blockU (rootAct σ z), detActivityBg m₀ St.a St.a₁ St.ν ρ (S.sym D) y'
        (cubeAct σ T) =
      ∑ y ∈ St.blockU z, detActivityBg m₀ St.a St.a₁ St.ν ρ D y T := by
  refine sum_detActivityBg_relabel_of_rootTraceBg St hN hσ
    (CS.τ.subtypeEquiv fun q => (CS.idx q).symm) (fun P => hpset P.1 P.2)
    (unitAct St.G' S hU) (fun y => ?_) (fun y I => ?_) z T
  · rw [← rootIdxOf_eq_unitBlock1, ← rootIdxOf_eq_unitBlock1]
    exact rootIdxOf_unitAct S hU hσ y
  · exact rootTraceBg_sym_of_rootTrace S CS B (cutPt I) (hRT_unitAct S hU CS y I) ρ D

end Block

/-! ### Non-vacuity: the translation and the coordinate swap of the top level set -/

section Inhabited

open Balaban.Inhabited Balaban.Inhabited.LevelStep

variable (m₁ k : ℕ) (ϱ : ℝ) {N : ℕ} (a : ℕ → ℝ) (aT ν : ℝ)

/-- **T5. The root trace is covariant at the translation `stepVec`** of the top level set
`lvTop 3 m₁ k ϱ`, a symmetry different from the identity (`unitAct_translate_ne_one`). -/
theorem rootTrace_translate (y : unitPts (lvTop 3 m₁ k ϱ)) (s : DecParams (lvTop 3 m₁ k ϱ))
    (φ : CTorus 3 3 3 m₁ (k + 1) → Fin N → ℂ) (α : (lvTop 3 m₁ k ϱ).Ω 1 → ℂ) :
    rootTrace (lvTop 3 m₁ k ϱ) a aT ν (unitQ (lvTop 3 m₁ k ϱ)) (unitP (lvTop 3 m₁ k ϱ))
        {unitAct (lvTop 3 m₁ k ϱ) (stepTranslateSymm m₁ k ϱ) (unitBlockPres_stepVec m₁ k) y}
        ((CoverSymm.ofTranslate (G := lvTop 3 m₁ k ϱ) isLevel_lvTop (stepVec m₁ k)
          (stepVec_dvd m₁ k)).par s)
        (symSite (Equiv.addRight (stepVec m₁ k)) φ) ((stepTranslateSymm m₁ k ϱ).mul α) =
      rootTrace (lvTop 3 m₁ k ϱ) a aT ν (unitQ (lvTop 3 m₁ k ϱ)) (unitP (lvTop 3 m₁ k ϱ))
        {y} s φ α :=
  rootTrace_unitAct (stepTranslateSymm m₁ k ϱ) (unitBlockPres_stepVec m₁ k) _ a aT ν y s φ α

/-- **T5. The root trace is covariant at the coordinate swap** of the top level set. -/
theorem rootTrace_swap (y : unitPts (lvTop 3 m₁ k ϱ)) (s : DecParams (lvTop 3 m₁ k ϱ))
    (φ : CTorus 3 3 3 m₁ (k + 1) → Fin N → ℂ) (α : (lvTop 3 m₁ k ϱ).Ω 1 → ℂ) :
    rootTrace (lvTop 3 m₁ k ϱ) a aT ν (unitQ (lvTop 3 m₁ k ϱ)) (unitP (lvTop 3 m₁ k ϱ))
        {unitAct (lvTop 3 m₁ k ϱ) (stepSwapSymm m₁ k ϱ) (unitBlockPres_swap01 m₁ k) y}
        ((CoverSymm.ofCoordPerm (G := lvTop 3 m₁ k ϱ) (m₁ := m₁) isLevel_lvTop swap01).par s)
        (symSite (coordPerm swap01) φ) ((stepSwapSymm m₁ k ϱ).mul α) =
      rootTrace (lvTop 3 m₁ k ϱ) a aT ν (unitQ (lvTop 3 m₁ k ϱ)) (unitP (lvTop 3 m₁ k ϱ))
        {y} s φ α :=
  rootTrace_unitAct (stepSwapSymm m₁ k ϱ) (unitBlockPres_swap01 m₁ k) _ a aT ν y s φ α

/-- Both instances move the unit points. -/
theorem rootTrace_symm_instances_nontrivial :
    unitAct (lvTop 3 m₁ k ϱ) (stepTranslateSymm m₁ k ϱ) (unitBlockPres_stepVec m₁ k) ≠ 1 ∧
      unitAct (lvTop 3 m₁ k ϱ) (stepSwapSymm m₁ k ϱ) (unitBlockPres_swap01 m₁ k) ≠ 1 :=
  ⟨unitAct_translate_ne_one m₁ k ϱ, unitAct_swap_ne_one m₁ k ϱ⟩

end Inhabited

end Balaban.Fluctuation
