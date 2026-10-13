/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.DecEquivPermuteStep
public import Balaban.Localization.DecEquivTranslatePolymer

/-!
# Coordinate permutations are compatible with the polymers of a level set

For a level set `G` (`IsLevel G n`) and a permutation `π` of the coordinates, the two fields of
`PolymerSymm` hold at the centres of the cover with the action `(j, y₀) ↦ (j, y₀ ∘ π⁻¹)`
(`permuteCentres π`), for every `m₀` and without any divisibility: the cells, the grid of bases
and the boxes are defined coordinate-wise.  This gives `PolymerSymm.ofCoordPerm` and the
covariance of the expansion terms at the coordinate swap of the level step
(`evTerm_permute_lvTop`).

Also: composition of polymer symmetries, `PolymerSymm.trans` (it needs the index clause of the
cover symmetry of the first factor).

Covariance of the output terms of a step as class terms is not proved here; only the term
covariance of `evTerm` for a function transported on the unit polydisc.
-/

@[expose] public section

namespace Balaban.Localization.DecEquiv

open Balaban Balaban.Multiscale Balaban.Background Balaban.Fluctuation Finset

section Boxes

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}

omit [NeZero N₁] [NeZero L] in
theorem mem_box_coordPerm_iff (π : Equiv.Perm (Fin d)) (b x : CTorus d L N₁ m₁ K) (s : ℕ) :
    coordPerm π x ∈ box (coordPerm π b) s ↔ x ∈ box b s := by
  unfold box
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨w, hw, hx⟩
    refine ⟨w ∘ π, fun μ => hw _, ?_⟩
    funext μ
    have := congrFun hx (π μ)
    simpa [coordPerm_apply', natT] using this
  · rintro ⟨w, hw, hx⟩
    refine ⟨w ∘ π.symm, fun μ => hw _, ?_⟩
    funext μ
    have := congrFun hx (π.symm μ)
    simpa [coordPerm_apply', natT] using this

omit [NeZero N₁] [NeZero L] in
theorem aligned_coordPerm_iff (π : Equiv.Perm (Fin d)) (a : ℕ) (b : CTorus d L N₁ m₁ K) :
    Aligned a (coordPerm π b) ↔ Aligned a b :=
  (π.forall_congr_left (p := fun μ => (b μ).val % a = 0)).symm

omit [NeZero N₁] [NeZero L] in
theorem cbase_coordPerm (π : Equiv.Perm (Fin d)) (a : ℕ) (z : CTorus d L N₁ m₁ K) :
    cbase a (coordPerm π z) = coordPerm π (cbase a z) := rfl

omit [NeZero N₁] [NeZero L] in
theorem cellOf_coordPerm (π : Equiv.Perm (Fin d)) (m₀ j : ℕ) (y x : CTorus d L N₁ m₁ K) :
    coordPerm π x ∈ cellOf L m₀ m₁ (j, coordPerm π y) ↔ x ∈ cellOf L m₀ m₁ (j, y) := by
  unfold cellOf
  simp only
  rw [cbase_coordPerm]
  exact mem_box_coordPerm_iff π _ x _

end Boxes

section Level

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {n m₀ : ℕ}

theorem dcubes_coordPerm (hG : IsLevel G n) (π : Equiv.Perm (Fin d))
    (y b : CTorus d L N₁ m₁ K) :
    coordPerm π b ∈ Dcubes G m₀ (n, coordPerm π y) ↔ b ∈ Dcubes G m₀ (n, y) := by
  unfold Dcubes
  simp only [Set.mem_ofPred_eq]
  refine and_congr (aligned_coordPerm_iff π _ b) (and_congr ?_ ?_)
  · constructor
    · intro h x hx
      exact (mem_box_coordPerm_iff π b x _).1 (h ((cellOf_coordPerm π m₀ n y x).2 hx))
    · intro h z hz
      obtain ⟨x, rfl⟩ : ∃ x, z = coordPerm π x := ⟨(coordPerm π).symm z, by simp⟩
      exact (mem_box_coordPerm_iff π b x _).2 (h ((cellOf_coordPerm π m₀ n y x).1 hz))
  · exact ⟨fun _ x hx => (hG.mem_layer x), fun _ x hx => (hG.mem_layer x)⟩

/-- **The sets `D(P)` are permuted** by a coordinate permutation of a level set. -/
theorem Dsites_coordPerm (hG : IsLevel G n) (π : Equiv.Perm (Fin d))
    (y : CTorus d L N₁ m₁ K) :
    Dsites G m₀ (n, coordPerm π y) = (coordPerm π) '' Dsites G m₀ (n, y) := by
  ext z
  obtain ⟨x, rfl⟩ : ∃ x, z = coordPerm π x := ⟨(coordPerm π).symm z, by simp⟩
  rw [(coordPerm π).injective.mem_set_image]
  unfold Dsites
  simp only [Set.mem_iUnion, exists_prop]
  constructor
  · rintro ⟨b, hb, hx⟩
    obtain ⟨b', rfl⟩ : ∃ b', b = coordPerm π b' := ⟨(coordPerm π).symm b, by simp⟩
    exact ⟨b', (dcubes_coordPerm hG π y b').1 hb, (mem_box_coordPerm_iff π b' x _).1 hx⟩
  · rintro ⟨b, hb, hx⟩
    exact ⟨coordPerm π b, (dcubes_coordPerm hG π y b).2 hb,
      (mem_box_coordPerm_iff π b x _).2 hx⟩

/-- **(P1) Coordinate permutations are compatible with the polymers of a level set**, for every
`m₀` and without divisibility. -/
theorem PolymerSymm.ofCoordPerm (hG : IsLevel G n) (π : Equiv.Perm (Fin d)) :
    PolymerSymm G m₀ (coordPerm π : Equiv.Perm (CTorus d L N₁ m₁ K)) (permuteCentres π) where
  pset := fun q _ x => sameCell_coordPerm_iff π _ x q.2
  dsites := fun q hq => by
    have hqn : q.1 = n := fst_eq_of_mem_cubeIdx hG hq
    obtain ⟨j, y⟩ := q
    simp only at hqn
    subst hqn
    exact Dsites_coordPerm hG π y

end Level

section Trans

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {m₀ : ℕ}
variable {σ σ' : Equiv.Perm (CTorus d L N₁ m₁ K)}
  {τ τ' : Equiv.Perm (ℕ × CTorus d L N₁ m₁ K)}

/-- **Composition of polymer symmetries** (first `σ`, then `σ'`); `τ` must carry the centres of
the cover to centres of the cover (as the action of a `CoverSymm` does). -/
theorem _root_.Balaban.Localization.PolymerSymm.trans (P : PolymerSymm G m₀ σ τ) (P' : PolymerSymm G m₀ σ' τ')
    (hτ : ∀ q ∈ (coverOf G).cubeIdx, τ q ∈ (coverOf G).cubeIdx) :
    PolymerSymm G m₀ (σ.trans σ') (τ.trans τ') where
  pset := fun q hq x =>
    (P'.pset (τ q) (hτ q hq) (σ x)).trans (P.pset q hq x)
  dsites := fun q hq => by
    show Dsites G m₀ (τ' (τ q)) = (σ.trans σ') '' Dsites G m₀ q
    rw [P'.dsites _ (hτ q hq), P.dsites _ hq, Set.image_image]
    rfl

/-- `PolymerSymm.trans` for the action of a cover symmetry. -/
theorem _root_.Balaban.Localization.PolymerSymm.trans_coverSymm (S : CoverSymm (coverOf G) σ)
    (P : PolymerSymm G m₀ σ S.τ) (P' : PolymerSymm G m₀ σ' τ') :
    PolymerSymm G m₀ (σ.trans σ') (S.τ.trans τ') :=
  P.trans P' fun q hq => (S.idx q).2 hq

end Trans

/-! ### The landed step -/

section Step

open Balaban.Inhabited Balaban.Inhabited.LevelStep Balaban.Analysis

variable (m₁ k m₀ : ℕ) (ϱ : ℝ) [NeZero (3 : ℕ)]

/-- **`PolymerSymm` is inhabited at the coordinate swap** of the top level set of the step, for
every `m₀`, and the swap is not the identity. -/
theorem polymerSymm_swap_lvTop :
    (coordPerm swap01 : Equiv.Perm (CTorus 3 3 3 m₁ (k + 1))) ≠ 1 ∧
      Nonempty (PolymerSymm (lvTop 3 m₁ k ϱ) m₀ (coordPerm swap01) (permuteCentres swap01)) :=
  ⟨swap_ne_one m₁ k, ⟨PolymerSymm.ofCoordPerm isLevel_lvTop swap01⟩⟩

/-- **Covariance of the expansion terms `𝓔(X, Y)` at the coordinate swap of the step**
(every `m₀` with `L ^ m₀ ∣ N₁` is not needed: permutations need no divisibility): the term of the
transported function at the swapped sets equals the original term. -/
theorem evTerm_permute_lvTop (S : LatSymm (lvTop 3 m₁ k ϱ) (lvTop 3 m₁ k ϱ)
      (coordPerm swap01)) {R : ℝ} (hR : 1 < R) (X₁ Y : Set (CTorus 3 3 3 m₁ (k + 1)))
    {U U' : Type*} {F : U → ((coverOf (lvTop 3 m₁ k ϱ)).cubeIdx → ℂ) → ℂ}
    {F' : U' → ((coverOf (lvTop 3 m₁ k ϱ)).cubeIdx → ℂ) → ℂ} {u : U} {u' : U'} :
    let G := lvTop 3 m₁ k ϱ
    let CS := CoverSymm.ofCoordPerm (G := G) (m₁ := m₁) isLevel_lvTop swap01
    let κ : (coverOf G).cubeIdx ≃ (coverOf G).cubeIdx :=
      Equiv.subtypeEquiv CS.τ fun q => (CS.idx q).symm
    AnalyticOnNhd ℂ (F u) (polydisc (0 : (coverOf G).cubeIdx → ℂ) (fun _ => R)) →
    AnalyticOnNhd ℂ (F' u') (polydisc (0 : (coverOf G).cubeIdx → ℂ) (fun _ => R)) →
    (∀ s ∈ unitCube (coverOf G).cubeIdx, F' u' s = F u (s ∘ κ)) →
    evTerm (fun i : (coverOf G).cubeIdx => i.1) G m₀ ((coordPerm swap01) '' X₁) F'
        ((coordPerm swap01) '' Y) u' =
      evTerm (fun i : (coverOf G).cubeIdx => i.1) G m₀ X₁ F Y u := by
  intro G CS κ hF hF' hff
  classical
  exact evTerm_relabel (fun i : (coverOf G).cubeIdx => i.1) (fun i : (coverOf G).cubeIdx => i.1)
    κ hR (PolymerSymm.ofCoordPerm isLevel_lvTop swap01) S
    (fun _ => rfl) (fun i => i.2) X₁ Y hF hF' hff

end Step

end Balaban.Localization.DecEquiv
