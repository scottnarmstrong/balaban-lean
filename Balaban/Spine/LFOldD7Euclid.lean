/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.HoleStepAnalytic
public import Balaban.Localization.DecEquivAff
public import Balaban.Localization.LatPairDecBg
public import Balaban.Localization.LatPairCov
public import Balaban.Fluctuation.LocalClassLatCore
public import Balaban.LargeField.Region.SymmLevel

/-!
# Lattice covariance of the composed field of a step (the clause `euclid` of (D7))

Two steps `S`, `S'` related by an aligned affine lattice isometry `A` of the cover torus that
carries the layers of `G` and of `G'` onto those of `S'` and the datum `D'` onto that of `S'`
(`StepAff`).  Then (all the objects being transported by `A` and the unit points by the bijection
`StepAff.u`):

* `StepAff.latSymm`, `StepAff.latSymm'`: `A` is a lattice symmetry `G → G'`, `G' → G'` of the sets
  of the steps;
* the decoupled covariance root and the composed field of `S'` are those of `S`.
-/

@[expose] public section

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.LargeField
  Balaban.Localization.DecEquiv Balaban.Localization.DetUnitIncidence

namespace Balaban.Fluctuation

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱ' : ℝ}

/-- **Two steps related by an aligned affine lattice isometry of the cover torus.** -/
structure StepAff (S S' : HoleStep d L N₁ m₁ k N ϱ ϱ')
    (A : AffIso d ((N₁ * L ^ m₁) * L ^ (k + 1))) : Prop where
  hAl : A.Aligned (L ^ (k + 1 + m₁))
  hΩ : ∀ j x, A.toFun x ∈ S'.G.Ω j ↔ x ∈ S.G.Ω j
  hΩ' : ∀ j x, A.toFun x ∈ S'.G'.Ω j ↔ x ∈ S.G'.Ω j
  hca : CubeAligned S.G' m₁
  hca' : CubeAligned S'.G' m₁
  hΨ : ∀ x i, S'.D'.Ψ (A.toFun x) i = S.D'.Ψ x i
  hh : ∀ x i, S'.D'.h (A.toFun x) i = S.D'.h x i
  ha₁ : S'.a₁ = S.a₁
  hν : S'.ν = S.ν
  hβ : S'.β = S.β

namespace StepAff

variable {S S' : HoleStep d L N₁ m₁ k N ϱ ϱ'} {A : AffIso d ((N₁ * L ^ m₁) * L ^ (k + 1))}

theorem aligned_pow (H : StepAff S S' A) {j : ℕ} (hj : j ≤ k + 1 + m₁) : A.Aligned (L ^ j) :=
  fun i => dvd_trans (pow_dvd_pow L hj) (H.hAl i)

/-- `A` is a lattice symmetry between the old sets of the two steps. -/
def latSymm (H : StepAff S S' A) : LatSymm S.G S'.G A.toEquiv :=
  A.latSymm (H.aligned_pow (by omega)) (fun m => by
    ext x
    rw [Finset.mem_map_equiv]
    have := H.hΩ m (A.toEquiv.symm x)
    have e : A.toFun (A.toEquiv.symm x) = x := A.toFun_invFun x
    rwa [e] at this)

/-- `A` is a lattice symmetry between the sets `G'` of the two steps. -/
def latSymm' (H : StepAff S S' A) : LatSymm S.G' S'.G' A.toEquiv :=
  A.latSymm (H.aligned_pow (by omega)) (fun m => by
    ext x
    rw [Finset.mem_map_equiv]
    have := H.hΩ' m (A.toEquiv.symm x)
    have e : A.toFun (A.toEquiv.symm x) = x := A.toFun_invFun x
    rwa [e] at this)

/-- The unit blocks are preserved by `A`. -/
theorem unitBlockPres (H : StepAff S S' A) : UnitBlockPres A.toEquiv := by
  intro x y
  have hpos : 0 < L ^ k := by have := NeZero.pos L; positivity
  have hdv : L ^ k ∣ (N₁ * L ^ m₁) * L ^ (k + 1) := by
    exact ⟨N₁ * L ^ m₁ * L, by ring⟩
  rw [unitBlock_eq_iff, unitBlock_eq_iff]
  exact sameCell_aff_iff A hpos hdv (H.aligned_pow (by omega)) x y

/-- The centres of the covers of `G'` of the two steps. -/
noncomputable def tau (A : AffIso d ((N₁ * L ^ m₁) * L ^ (k + 1))) :
    Equiv.Perm (ℕ × CTorus d L N₁ m₁ (k + 1)) := affCentres (m₁ := m₁) A m₁

theorem sym_D (H : StepAff S S' A) : H.latSymm'.sym S.D' = S'.D' := by
  refine Background.BgData.ext' ?_ ?_
  · funext y i
    have := H.hΨ (A.toEquiv.symm y) i
    have e : A.toFun (A.toEquiv.symm y) = y := A.toFun_invFun y
    rw [e] at this
    exact this.symm
  · funext y i
    have := H.hh (A.toEquiv.symm y) i
    have e : A.toFun (A.toEquiv.symm y) = y := A.toFun_invFun y
    rw [e] at this
    exact this.symm

theorem a_eq (H : StepAff S S' A) : S'.a = S.a := by
  simp [HoleStep.a, H.ha₁]

/-- **The decoupled background of the step is transported.** -/
theorem decBg (H : StepAff S S' A) (ρ : ℝ) {s : Dec2.DecParams (coverOf S.G')}
    {s' : Dec2.DecParams (coverOf S'.G')}
    (hs : ∀ P, Dec2.extS (coverOf S'.G') s' (tau A P) = Dec2.extS (coverOf S.G') s P) :
    Dec2.decBgField (coverOf S'.G') S'.G' S'.a S'.ν ρ s' S'.D' =
        H.latSymm'.fld (Dec2.decBgField (coverOf S.G') S.G' S.a S.ν ρ s S.D') ∧
      Dec2.decBgMult (coverOf S'.G') S'.G' S'.a S'.ν ρ s' S'.D' =
        H.latSymm'.mul (Dec2.decBgMult (coverOf S.G') S.G' S.a S.ν ρ s S.D') := by
  have hB := decBg2_sym_pair (a := S.a) (ν := S.ν) H.latSymm'
    (τ := tau A) (τb := affBlocks A)
    (cover_idx_aff A H.hAl H.hca H.hca' H.hΩ') (cover_chi_aff A H.hAl H.hca H.hca' H.hΩ')
    (cover_box_aff A) (cover_qset_aff A H.hAl H.hca H.hca' H.hΩ')
    (block_idx_aff A H.hAl H.hca H.hca' H.hΩ') (fun _ => rfl) (block_bump_aff A)
    (fun q hq => by
      obtain ⟨hr, -, hb⟩ := (Background.mem_blockIdx S.G').1 hq
      exact block_base_aff A H.hAl q hr hb) hs ρ S.D'
  rw [sym_D H] at hB
  rw [H.a_eq, H.hν]
  exact hB

end StepAff

end Balaban.Fluctuation
