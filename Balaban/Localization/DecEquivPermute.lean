/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.DecEquivTranslate

/-!
# Coordinate permutations as symmetries of the cover and of the interpolation blocks

For a level set `G` (`IsLevel G n`) and a permutation `π` of the coordinates, the map
`coordPerm π : x ↦ x ∘ π⁻¹` of the fine torus `CTorus d L N₁ m₁ K` (so that the coordinate `π μ`
of the image is the coordinate `μ` of the point) is realized as an inhabitant of `LatSymm`,
`CoverSymm (coverOf G)` and `BlockSymm G`, with the action `(j, y₀) ↦ (j, y₀ ∘ π⁻¹)` on the
centres.  No divisibility is needed: the bump is a product over the coordinates, and the notions
`InBox`, `SameCell`, `CubeBase`, `IsBase` are coordinate-wise.

Also: composition of symmetries, `CoverSymm.trans` and `BlockSymm.trans` (the latter needs the
block clause of the first lattice symmetry).

Covariance of the output terms of a step is not proved here; only that the symmetry data exist.
-/

@[expose] public section

namespace Balaban.Localization.DecEquiv

open Balaban Balaban.Multiscale Balaban.Background Balaban.Fluctuation Finset

section Perm

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}

omit [NeZero N₁] [NeZero L] in
theorem coordPerm_apply' (π : Equiv.Perm (Fin d)) (x : CTorus d L N₁ m₁ K) (μ : Fin d) :
    coordPerm π x μ = x (π.symm μ) := rfl

omit [NeZero N₁] [NeZero L] in
theorem castT_comp {n n' : ℕ} (h : n = n') (x : Torus d n) (f : Fin d → Fin d) :
    castT h (x ∘ f) = castT h x ∘ f := by
  subst h; rfl

omit [NeZero L] in
/-- The periodized bump is invariant under permutations of the coordinates. -/
theorem bump_coordPerm {N₀ k : ℕ} [NeZero N₀] (m : ℕ) (π : Equiv.Perm (Fin d))
    (y0 x : Torus d (N₀ * L ^ k)) :
    bump m (coordPerm π y0) (coordPerm π x) = bump m y0 x := by
  unfold bump
  refine Fintype.prod_equiv π.symm _ _ fun μ => ?_
  unfold perFac bumpCentre
  rfl

omit [NeZero L] in
theorem cubeBump_coordPerm (π : Equiv.Perm (Fin d)) (j : ℕ) (y0 x : CTorus d L N₁ m₁ K) :
    cubeBump m₁ j (coordPerm π y0) (coordPerm π x) = cubeBump m₁ j y0 x := by
  unfold cubeBump tor coordPerm
  simp only [Equiv.coe_fn_mk]
  rw [castT_comp, castT_comp]
  exact bump_coordPerm _ _ _ _

omit [NeZero N₁] [NeZero L] in
theorem inBox_coordPerm_iff (π : Equiv.Perm (Fin d)) (j : ℕ) (y0 x : CTorus d L N₁ m₁ K)
    (R : ℝ) : InBox m₁ j (coordPerm π y0) R (coordPerm π x) ↔ InBox m₁ j y0 R x :=
  (π.forall_congr_left (p := fun μ => ∃ p : ℤ, |((x μ).val : ℝ) + p *
    (((N₁ * L ^ m₁) * L ^ K : ℕ) : ℝ) - (((y0 μ).val : ℝ) + ((L : ℝ) ^ (j + m₁) - 1) / 2)| < R)).symm

omit [NeZero N₁] [NeZero L] in
theorem cubeBase_coordPerm_iff (π : Equiv.Perm (Fin d)) (j : ℕ) (y : CTorus d L N₁ m₁ K) :
    CubeBase m₁ j (coordPerm π y) ↔ CubeBase m₁ j y :=
  (π.forall_congr_left (p := fun μ => (y μ).val % L ^ (j + m₁) = 0)).symm

omit [NeZero N₁] [NeZero L] in
theorem isBase_coordPerm_iff (π : Equiv.Perm (Fin d)) (j : ℕ) (y : CTorus d L N₁ m₁ K) :
    IsBase j (coordPerm π y) ↔ IsBase j y :=
  (π.forall_congr_left (p := fun μ => (y μ).val % L ^ j = 0)).symm

omit [NeZero N₁] [NeZero L] in
theorem sameCell_coordPerm_iff (π : Equiv.Perm (Fin d)) (a : ℕ) (x y : CTorus d L N₁ m₁ K) :
    SameCell a (coordPerm π x) (coordPerm π y) ↔ SameCell a x y :=
  (π.forall_congr_left (p := fun μ => (x μ).val / a = (y μ).val / a)).symm

end Perm

section Level

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {n : ℕ}

/-- **(T1) A coordinate permutation is a lattice symmetry of a level set.** -/
def LatSymm.ofCoordPermLevel (hG : IsLevel G n) (π : Equiv.Perm (Fin d)) :
    LatSymm G G (coordPerm π : Equiv.Perm (CTorus d L N₁ m₁ K)) :=
  LatSymm.ofCoordPerm π
    (fun i h1 hk x => by rw [level_mem_Ω hG h1 hk (coordPerm π x), level_mem_Ω hG h1 hk x])

/-- The action `(j, y₀) ↦ (j, y₀ ∘ π⁻¹)` on the centres. -/
def permuteCentres (π : Equiv.Perm (Fin d)) : Equiv.Perm (ℕ × CTorus d L N₁ m₁ K) :=
  Equiv.prodCongr (Equiv.refl ℕ) (coordPerm π)

omit [NeZero N₁] [NeZero L] in
@[simp] theorem permuteCentres_apply (π : Equiv.Perm (Fin d)) (q : ℕ × CTorus d L N₁ m₁ K) :
    permuteCentres π q = (q.1, coordPerm π q.2) := rfl

theorem permute_mem_cubeIdx_iff (hG : IsLevel G n) (π : Equiv.Perm (Fin d))
    (q : ℕ × CTorus d L N₁ m₁ K) : permuteCentres π q ∈ cubeIdx G ↔ q ∈ cubeIdx G := by
  have S := LatSymm.ofCoordPermLevel (m₁ := m₁) hG π
  simp only [mem_cubeIdx, permuteCentres_apply]
  constructor
  · rintro ⟨hr, hl, hb⟩
    exact ⟨hr, (S.mem_layer hr.1 hr.2 q.2).1 hl, (cubeBase_coordPerm_iff π q.1 q.2).1 hb⟩
  · rintro ⟨hr, hl, hb⟩
    exact ⟨hr, (S.mem_layer hr.1 hr.2 q.2).2 hl, (cubeBase_coordPerm_iff π q.1 q.2).2 hb⟩

theorem permute_mem_blockIdx_iff (hG : IsLevel G n) (π : Equiv.Perm (Fin d))
    (q : ℕ × CTorus d L N₁ m₁ K) : permuteCentres π q ∈ blockIdx G ↔ q ∈ blockIdx G := by
  have S := LatSymm.ofCoordPermLevel (m₁ := m₁) hG π
  simp only [mem_blockIdx, permuteCentres_apply]
  constructor
  · rintro ⟨hr, hl, hb⟩
    exact ⟨hr, (S.mem_layer hr.1 hr.2 q.2).1 hl, (isBase_coordPerm_iff π q.1 q.2).1 hb⟩
  · rintro ⟨hr, hl, hb⟩
    exact ⟨hr, (S.mem_layer hr.1 hr.2 q.2).2 hl, (isBase_coordPerm_iff π q.1 q.2).2 hb⟩

/-- **(T3) A coordinate permutation is compatible with the blocks of the interpolation of a level
set.** -/
def BlockSymm.ofCoordPerm (hG : IsLevel G n) (π : Equiv.Perm (Fin d)) :
    BlockSymm G (coordPerm π : Equiv.Perm (CTorus d L N₁ m₁ K)) where
  τ := permuteCentres π
  idx := permute_mem_blockIdx_iff hG π
  layer := fun _ => rfl
  bump := fun q x => bump_coordPerm q.1 π q.2 x
  base := fun q _ => by
    show jBlock d L (N₁ * L ^ m₁) K q.1 ((coordPerm π).symm ((coordPerm π) q.2)) = _
    rw [Equiv.symm_apply_apply]

theorem coverDenom_coordPerm (hG : IsLevel G n) (π : Equiv.Perm (Fin d))
    (x : CTorus d L N₁ m₁ K) : coverDenom G (coordPerm π x) = coverDenom G x := by
  unfold coverDenom
  refine (Finset.sum_equiv (permuteCentres π)
    (fun q => (permute_mem_cubeIdx_iff hG π q).symm) fun q _ => ?_).symm
  exact (cubeBump_coordPerm π q.1 q.2 x).symm

/-- **(T2) A coordinate permutation is compatible with the cover of a level set.** -/
def CoverSymm.ofCoordPerm (hG : IsLevel G n) (π : Equiv.Perm (Fin d)) :
    CoverSymm (coverOf G) (coordPerm π : Equiv.Perm (CTorus d L N₁ m₁ K)) where
  τ := permuteCentres π
  idx := permute_mem_cubeIdx_iff hG π
  chi := fun q x => by
    show Balaban.Localization.chi G (q.1, coordPerm π q.2) (coordPerm π x) =
      Balaban.Localization.chi G q x
    unfold Balaban.Localization.chi
    rw [coverDenom_coordPerm hG π]
    exact congrArg (· / coverDenom G x) (cubeBump_coordPerm π q.1 q.2 x)
  box := fun q x => by
    show coordPerm π x ∈ intBox (q.1, coordPerm π q.2) ↔ x ∈ intBox q
    rw [mem_intBox, mem_intBox]
    exact inBox_coordPerm_iff π q.1 q.2 x _
  qset := fun q q' => by
    have hidx := permute_mem_cubeIdx_iff hG π q'
    show (q'.1, coordPerm π q'.2) ∈ (coverOf G).Qset (q.1, coordPerm π q.2) ↔
      q' ∈ (coverOf G).Qset q
    rw [DecCover.mem_Qset, DecCover.mem_Qset]
    have hid : (coverOf G).cubeIdx = cubeIdx G := rfl
    rw [hid]
    constructor
    · rintro ⟨h1, y, hy1, hy2⟩
      refine ⟨hidx.1 h1, (coordPerm π).symm y, ?_, ?_⟩
      · refine (sameCell_coordPerm_iff π _ _ _).1 ?_
        simpa only [Equiv.apply_symm_apply] using hy1
      · refine (inBox_coordPerm_iff π _ _ _ _).1 ?_
        simpa only [Equiv.apply_symm_apply] using hy2
    · rintro ⟨h1, y, hy1, hy2⟩
      exact ⟨hidx.2 h1, coordPerm π y, (sameCell_coordPerm_iff π _ _ _).2 hy1,
        (inBox_coordPerm_iff π _ _ _ _).2 hy2⟩

end Level

section Trans

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}

/-- **Composition of cover symmetries** (first `σ`, then `σ'`). -/
def CoverSymm.trans {C : DecCover d L N₁ m₁ K} {σ σ' : Equiv.Perm (CTorus d L N₁ m₁ K)}
    (S : CoverSymm C σ) (S' : CoverSymm C σ') : CoverSymm C (σ.trans σ') where
  τ := S.τ.trans S'.τ
  idx := fun q => (S'.idx (S.τ q)).trans (S.idx q)
  chi := fun q x => (S'.chi (S.τ q) (σ x)).trans (S.chi q x)
  box := fun q x => (S'.box (S.τ q) (σ x)).trans (S.box q x)
  qset := fun q q' => (S'.qset (S.τ q) (S.τ q')).trans (S.qset q q')

/-- **Composition of block symmetries** (first `σ`, then `σ'`); the block clause of the lattice
symmetry `σ` carries the base-point identity of `σ'` back through `σ`. -/
def BlockSymm.trans {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ}
    {σ σ' : Equiv.Perm (CTorus d L N₁ m₁ K)}
    (S : BlockSymm G σ) (S' : BlockSymm G σ') (T : LatSymm G G σ) :
    BlockSymm G (σ.trans σ') where
  τ := S.τ.trans S'.τ
  idx := fun q => (S'.idx (S.τ q)).trans (S.idx q)
  layer := fun q => (S'.layer (S.τ q)).trans (S.layer q)
  bump := fun q x => by
    show Background.bump (S'.τ (S.τ q)).1 (S'.τ (S.τ q)).2 (σ' (σ x)) = _
    rw [S'.bump (S.τ q) (σ x)]
    have h := S.bump q x
    rw [S.layer q] at h ⊢
    exact h
  base := fun q hq => by
    obtain ⟨⟨h1, hk⟩, hl, -⟩ := (mem_blockIdx G).1 hq
    have hq' : S.τ q ∈ blockIdx G := (S.idx q).2 hq
    have hb := S'.base (S.τ q) hq'
    have hb2 := S.base q hq
    have hlay := S.layer q
    show jBlock d L (N₁ * L ^ m₁) K q.1 (σ.symm (σ'.symm (S'.τ (S.τ q)).2)) = _
    rw [← hb2]
    have key := (T.block q.1 h1 hk ⟨q.2, hl⟩ (σ.symm (σ'.symm (S'.τ (S.τ q)).2))
      (σ.symm (S.τ q).2))
    simp only [Equiv.apply_symm_apply] at key
    refine key.1 ?_
    rw [hlay] at hb
    exact hb

end Trans

end Balaban.Localization.DecEquiv
