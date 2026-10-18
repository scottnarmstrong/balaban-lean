/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.XiLatSymm
public import Balaban.Localization.DecEquivTranslate
public import Balaban.Localization.DetUnitIncidenceSymm
public import Balaban.Fluctuation.DetOutputTerms
public import Balaban.Fluctuation.StepObjects

/-!
# The full level group acts on a level set, on its unit points and on the blocks (`StepTowerNewLevelSymGeom`)

Geometry for the covariance of the new-level density `densE0` under `fullJSymGroup L (k + 1)`
(blocker 6, `hDzfull`).  For a whole-lattice generating set `G` of level `n` and `σ` in the full
group `fullJSymGroup L j`, `n ≤ j ≤ K`:

* `nonempty_latSymm_of_isLevel`: `σ` is a lattice symmetry of `G` (all `Ω_i` are the whole torus);
* `unitBlockPres_of_fullJ`: `σ` preserves the unit blocks of the step torus (`K = k + 1`);
* `unitAct_unitPt`, `unitAct_symm_unitPt`: the induced permutation of the unit points sends the unit
  point of a site `x` to that of `σ x`;
* `mem_blockU_unitAct`: it carries the unit points over the block of `x` onto those over the block
  of `σ x`.

Nothing here uses the cover or the paving, which `fullJSymGroup` does not preserve.
-/

@[expose] public section

namespace Balaban.Inhabited.StepSym

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.Fluctuation
  Balaban.SmallField Balaban.SmallField.Def6 Balaban.Localization.DecEquiv
  Balaban.Localization.DetUnitIncidence

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}

/-- **Every element of the full level group `fullJSymGroup L j` is a lattice symmetry of a
whole-lattice generating set of level `n ≤ j`** (all of whose sites lie in the layer `n`). -/
theorem nonempty_latSymm_of_isLevel {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {n j : ℕ}
    (hG : IsLevel G n) (hnj : n ≤ j) (hjK : j ≤ K)
    {σ : Equiv.Perm (CTorus d L N₁ m₁ K)}
    (hσ : σ ∈ fullJSymGroup (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L j) :
    Nonempty (LatSymm G G σ) := by
  obtain ⟨T⟩ := nonempty_torusSymm_of_mem_fullJSymGroup hjK hσ
  refine ⟨LatSymm.ofTorusSymm T (fun i h1 hk x => ?_) (fun n' h1 hk hne => ?_)⟩
  · rw [level_mem_Ω hG h1 hk, level_mem_Ω hG h1 hk]
  · obtain ⟨x, hx⟩ := hne
    have := G.layerIndex_eq h1 hk hx
    rw [(hG x).2] at this
    exact this.ge.trans hnj

/-- **Every element of `fullJSymGroup L (k + 1)` of the torus of index `k + 1` preserves the unit
blocks.** -/
theorem unitBlockPres_of_fullJ {k : ℕ} {σ : Equiv.Perm (CTorus d L N₁ m₁ (k + 1))}
    (hσ : σ ∈ fullJSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L (k + 1)) :
    UnitBlockPres σ := by
  obtain ⟨T⟩ := nonempty_torusSymm_of_mem_fullJSymGroup (le_refl (k + 1)) hσ
  exact unitBlockPres_of_torusSymm (Nat.le_succ k) T

section Unit

variable {k : ℕ} {σ : Equiv.Perm (CTorus d L N₁ m₁ (k + 1))}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}

/-- The permutation of the unit points induced by `σ` sends the unit point of `x` to the unit
point of `σ x`. -/
theorem unitAct_unitPt (hG : IsLevel G (k + 1)) (S : LatSymm G G σ) (hU : UnitBlockPres σ)
    (x : CTorus d L N₁ m₁ (k + 1)) :
    unitAct G S hU (unitPt hG x) = unitPt hG (σ x) :=
  Subtype.ext (unitAct_unitBlock G S hU (hG.mem_layer x))

theorem unitAct_symm_unitPt (hG : IsLevel G (k + 1)) (S : LatSymm G G σ) (hU : UnitBlockPres σ)
    (x : CTorus d L N₁ m₁ (k + 1)) :
    (unitAct G S hU).symm (unitPt hG x) = unitPt hG (σ.symm x) :=
  (Equiv.symm_apply_eq _).2 (by rw [unitAct_unitPt hG S hU, Equiv.apply_symm_apply])

/-- **The block `B(z)` of the unit lattice is transported by the induced permutation**: the unit
points over the block of `σ x` are the images of those over the block of `x`. -/
theorem mem_blockU_unitAct {N : ℕ} {S : StepSetting d L N₁ m₁ k N ϱ}
    (Sy : LatSymm S.G' S.G' σ) (hU : UnitBlockPres σ) (x : CTorus d L N₁ m₁ (k + 1)) :
    S.blockU (blockIndex (σ x)) = (S.blockU (blockIndex x)).map
      (unitAct S.G' Sy hU).toEmbedding := by
  classical
  ext b'
  rw [Finset.mem_map_equiv]
  set u := unitAct S.G' Sy hU with hu
  have hmem : ∀ (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))) (b : S.U),
      b ∈ S.blockU z ↔ unitBlock1 (b : UnitTorus d L N₁ m₁ k) = z := fun z b => by
    simp [StepSetting.blockU]
  rw [hmem, hmem]
  have e1 : blockIndex (σ x) = unitBlock1 (u (unitPt S.hG' x) : UnitTorus d L N₁ m₁ k) := by
    rw [hu, unitAct_unitPt S.hG' Sy hU x]
    exact (rootIdxOf_eq (y := unitPt S.hG' (σ x)) rfl).symm.trans (rootIdxOf_eq_unitBlock1 _)
  have e2 : blockIndex x = unitBlock1 (unitPt S.hG' x : UnitTorus d L N₁ m₁ k) :=
    (rootIdxOf_eq (y := unitPt S.hG' x) rfl).symm.trans (rootIdxOf_eq_unitBlock1 _)
  rw [e1, e2]
  have := unitBlock1_unitAct_iff S.G' Sy hU (u.symm b') (unitPt S.hG' x)
  rw [Equiv.apply_symm_apply] at this
  exact this

end Unit

end Balaban.Inhabited.StepSym
