/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.LFOldMarks
public import Balaban.Fluctuation.LocalClassRot
public import Balaban.Localization.DecEquivRelabel
public import Balaban.Polymer.TwoTorusEv

/-!
# The coefficient of the re-expanded old term is `O(N)`-covariant (the clause `rot` of (D7))

For a step on a region (`Fluctuation.HoleStep`) the datum `D'` and the field `h₀` may be rotated
(`HoleStep.rotBy`).  Then, under the standing conditions of the decoupled covariance:

* `psiKdAt_rotBy`: the decoupled approximate minimum rotates (`composeData_rot`, `decBg2_rot`);
* `covSqrtAt_rotBy`: the decoupled covariance square root is conjugated by the rotation
  (`decCovSqrt_rot`; the multiplier is a scalar and does not rotate);
* `composed_rotBy`: the composed field of P5 (2.39) rotates with the fluctuation field;
* `oldInterp_rotBy`: the interpolated old term of the rotated step, with the old term composed with
  the rotation and the fluctuation variables and fixed values rotated, is the interpolated old term;
* `coef_congr_of_agree_unit`: a coefficient of Lemma AE is determined by the values at the vertices
  `1_A` of the unit cube;
* `oldCoef_rotBy`: the coefficient `T(X, J)` of the re-expansion is the same.
-/

@[expose] public section

open MeasureTheory Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Localization Balaban.Localization.DecEquiv Matrix

set_option linter.unusedSectionVars false

namespace Balaban.Fluctuation

section RotStep

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱ' : ℝ}
  (S : HoleStep d L N₁ m₁ k N ϱ ϱ')

/-- **The step with the datum rotated**: `D'` replaced by `R D'`, `h₀` by `h₀'` with `R h₀ = h₀'`. -/
noncomputable abbrev HoleStep.rotBy (R : Matrix (Fin N) (Fin N) ℂ) (h₀' : Fin N → ℝ)
    (hh : R *ᵥ (fun i => ((S.h₀ i : ℝ) : ℂ)) = fun i => ((h₀' i : ℝ) : ℂ)) :
    HoleStep d L N₁ m₁ k N ϱ ϱ' :=
  { S with
    D' := S.D'.rot R
    h₀ := h₀'
    hh₀ := fun x hx i => by
      have hD : S.D'.h x = fun i => ((S.h₀ i : ℝ) : ℂ) := funext fun j => S.hh₀ x hx j
      show (R *ᵥ S.D'.h x) i = _
      rw [hD, hh] }

theorem HoleStep.rotBy_U (R : Matrix (Fin N) (Fin N) ℂ) (h₀' : Fin N → ℝ) (hh) :
    (S.rotBy R h₀' hh).U = S.U := rfl

theorem HoleStep.psiKdAt_rotBy {R : Matrix (Fin N) (Fin N) ℂ} (hR : Rᵀ * R = 1) (h₀' : Fin N → ℝ)
    (hh) (C : DecCover d L N₁ m₁ (k + 1)) (ρ : ℝ) (s : Dec2.DecParams C) :
    (S.rotBy R h₀' hh).psiKdAt C ρ s = (S.psiKdAt C ρ s).rot R := by
  unfold HoleStep.psiKdAt
  show composeData S.hpre S.a (Dec2.decBgField C S.G' S.a S.ν ρ s (S.D'.rot R)) (S.D'.rot R) = _
  rw [(decBg2_rot (C := C) (H := S.G') (a := S.a) (ν := S.ν) hR ρ s S.D').1, composeData_rot]


theorem svec_rot_eq {R : Matrix (Fin N) (Fin N) ℂ} {G' : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ'}
    (φ : G'.Ω 1 × Fin N → ℂ) : svec G' (rotFld R φ) = rotSite R (svec G' φ) := by
  funext y i
  rw [svec_rotFld]
  simp [rotSite, Matrix.mulVec, dotProduct]

theorem HoleStep.covSqrtAt_rotBy {R : Matrix (Fin N) (Fin N) ℂ} (hR : Rᵀ * R = 1) (h₀' : Fin N → ℝ)
    (hh) (ρ : ℝ) (s : Dec2.DecParams (coverOf S.G')) {κ δ : ℝ}
    (hstand : CovStanding S.G' S.a S.a₁ S.ν (Dec2.decBgMult (coverOf S.G') S.G' S.a S.ν ρ s S.D')
      κ (Dec2.extS (coverOf S.G') s) δ (svec S.G' (Dec2.decBgField (coverOf S.G') S.G' S.a S.ν ρ s S.D'))
      (unitQ S.G') (unitP S.G')) :
    (S.rotBy R h₀' hh).covSqrtAt (coverOf S.G') ρ s =
      (rotLift R : Matrix (S.U × Fin N) (S.U × Fin N) ℂ) * S.covSqrtAt (coverOf S.G') ρ s * rotLift Rᵀ := by
  unfold HoleStep.covSqrtAt
  have h := decBg2_rot (C := coverOf S.G') (H := S.G') (a := S.a) (ν := S.ν) hR ρ s S.D'
  show Dec2.decCovSqrt (coverOf S.G') S.G' S.a S.a₁ S.ν
      (Dec2.decBgMult (coverOf S.G') S.G' S.a S.ν ρ s (S.D'.rot R)) (Dec2.extS (coverOf S.G') s)
      (svec S.G' (Dec2.decBgField (coverOf S.G') S.G' S.a S.ν ρ s (S.D'.rot R))) (unitQ S.G') (unitP S.G') = _
  rw [h.1, h.2, svec_rot_eq]
  exact decCovSqrt_rot hR hstand


theorem HoleStep.shiftLoc_eq_mulVec (C : DecCover d L N₁ m₁ (k + 1)) (ρ : ℝ)
    (sloc : S.U → Dec2.DecParams C) (ψhat : S.U → Fin N → ℂ) (b : S.U) (i : Fin N) :
    S.shiftLoc C ρ sloc ψhat b i = ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
      (S.covSqrtAt C ρ (sloc b) *ᵥ (fun q : S.U × Fin N => ψhat q.1 q.2)) (b, i) := rfl

theorem HoleStep.shiftLoc_rotBy {R : Matrix (Fin N) (Fin N) ℂ} (hR : Rᵀ * R = 1) (h₀' : Fin N → ℝ)
    (hh) (ρ : ℝ) (sloc : S.U → Dec2.DecParams (coverOf S.G')) {κ δ : ℝ}
    (hstand : ∀ b, CovStanding S.G' S.a S.a₁ S.ν
      (Dec2.decBgMult (coverOf S.G') S.G' S.a S.ν ρ (sloc b) S.D') κ
      (Dec2.extS (coverOf S.G') (sloc b)) δ
      (svec S.G' (Dec2.decBgField (coverOf S.G') S.G' S.a S.ν ρ (sloc b) S.D'))
      (unitQ S.G') (unitP S.G'))
    (ψhat : S.U → Fin N → ℂ) (b : S.U) (i : Fin N) :
    (S.rotBy R h₀' hh).shiftLoc (coverOf S.G') ρ sloc (rotSite R ψhat) b i =
      ∑ j, R i j * S.shiftLoc (coverOf S.G') ρ sloc ψhat b j := by
  rw [HoleStep.shiftLoc_eq_mulVec, HoleStep.covSqrtAt_rotBy S hR h₀' hh ρ (sloc b) (hstand b)]
  have hv : (fun q : S.U × Fin N => rotSite R ψhat q.1 q.2) =
      rotFld R (fun q : S.U × Fin N => ψhat q.1 q.2) := rfl
  have hb : (S.rotBy R h₀' hh).betaU = S.betaU := rfl
  rw [hb, hv, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, rotLift_mulVec Rᵀ, rotFld_mul, hR,
    rotFld_one, rotLift_mulVec]
  simp only [rotFld, HoleStep.shiftLoc_eq_mulVec, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring


theorem HoleStep.composed_rotBy {R : Matrix (Fin N) (Fin N) ℂ} (hR : Rᵀ * R = 1) (h₀' : Fin N → ℝ)
    (hh) (ρ : ℝ) (sloc : S.U → Dec2.DecParams (coverOf S.G')) {κ δ : ℝ}
    (hstand : ∀ b, CovStanding S.G' S.a S.a₁ S.ν
      (Dec2.decBgMult (coverOf S.G') S.G' S.a S.ν ρ (sloc b) S.D') κ
      (Dec2.extS (coverOf S.G') (sloc b)) δ
      (svec S.G' (Dec2.decBgField (coverOf S.G') S.G' S.a S.ν ρ (sloc b) S.D'))
      (unitQ S.G') (unitP S.G'))
    (ψhat : S.U → Fin N → ℂ) (b : S.U) (i : Fin N) :
    (S.rotBy R h₀' hh).composed (coverOf S.G') ρ sloc (rotSite R ψhat) b i =
      ∑ j, R i j * S.composed (coverOf S.G') ρ sloc ψhat b j := by
  unfold HoleStep.composed
  rw [HoleStep.shiftLoc_rotBy S hR h₀' hh ρ sloc hstand]
  have hp : (S.rotBy R h₀' hh).psiLoc (coverOf S.G') ρ sloc b i =
      ∑ j, R i j * S.psiLoc (coverOf S.G') ρ sloc b j := by
    unfold HoleStep.psiLoc
    rw [HoleStep.psiKdAt_rotBy S hR h₀' hh]
    rfl
  rw [hp]
  simp only [mul_add, Finset.sum_add_distrib]


theorem HoleStep.fill_rot {R : Matrix (Fin N) (Fin N) ℂ} (Q : Matrix (Fin N) (Fin N) ℝ)
    (hRQ : ∀ i j, R i j = ((Q i j : ℝ) : ℂ)) (inner : Finset S.U) (ψin : inner → Rn N)
    (ψout : S.U → Fin N → ℂ) :
    S.fill inner (fun u => (EuclideanSpace.equiv (Fin N) ℝ).symm (Q *ᵥ (ψin u))) (rotSite R ψout) =
      rotSite R (S.fill inner ψin ψout) := by
  funext b i
  unfold HoleStep.fill rotSite
  by_cases h : b ∈ inner
  · simp only [h, ↓reduceDIte, Matrix.mulVec, dotProduct, EuclideanSpace.equiv]
    simp [hRQ, Matrix.mulVec, dotProduct, Complex.ofReal_sum]
  · simp [h]


theorem HoleStep.oldInterp_rotBy {R : Matrix (Fin N) (Fin N) ℂ} (hR : Rᵀ * R = 1)
    (Q : Matrix (Fin N) (Fin N) ℝ) (hRQ : ∀ i j, R i j = ((Q i j : ℝ) : ℂ)) (h₀' : Fin N → ℝ) (hh)
    (ρ : ℝ) (X₁loc : S.U → Finset (CTorus d L N₁ m₁ (k + 1)))
    (X₁ : Finset (CTorus d L N₁ m₁ (k + 1))) (inner : Finset S.U) (ψout : S.U → Fin N → ℂ)
    (B B' : (S.U → Fin N → ℂ) → ℂ) (hB : ∀ c, B' (rotSite R c) = B c) (ψin : inner → Rn N)
    (s : Dec2.DecParams (coverOf S.G')) {κ δ : ℝ}
    (hst : ∀ b, CovStanding S.G' S.a S.a₁ S.ν
      (Dec2.decBgMult (coverOf S.G') S.G' S.a S.ν ρ (S.slocOf (coverOf S.G') X₁loc (coreExt (coverOf S.G') X₁ s) b) S.D') κ
      (Dec2.extS (coverOf S.G') (S.slocOf (coverOf S.G') X₁loc (coreExt (coverOf S.G') X₁ s) b)) δ
      (svec S.G' (Dec2.decBgField (coverOf S.G') S.G' S.a S.ν ρ
        (S.slocOf (coverOf S.G') X₁loc (coreExt (coverOf S.G') X₁ s) b) S.D'))
      (unitQ S.G') (unitP S.G')) :
    (S.rotBy R h₀' hh).oldInterp (coverOf S.G') ρ X₁loc X₁ inner (rotSite R ψout) B'
        (fun u => (EuclideanSpace.equiv (Fin N) ℝ).symm (Q *ᵥ (ψin u))) s =
      S.oldInterp (coverOf S.G') ρ X₁loc X₁ inner ψout B ψin s := by
  unfold HoleStep.oldInterp
  rw [← hB]
  congr 1
  funext b i
  have h1 := HoleStep.composed_rotBy S hR h₀' hh ρ
    (S.slocOf (coverOf S.G') X₁loc (coreExt (coverOf S.G') X₁ s)) hst
    (S.fill inner ψin ψout) b i
  rw [← HoleStep.fill_rot S Q hRQ] at h1
  exact h1

end RotStep

section CoefAgree

open Balaban.Analysis Balaban.Localization

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The coefficient is determined by the values at the vertices of the unit cube**: two functions
analytic on the polydisc of radius `R > 1` that agree at every `1_A` have the same coefficients. -/
theorem coef_congr_of_agree_unit {R : ℝ} (hR : 1 < R) {f g : (ι → ℂ) → ℂ}
    (hf : AnalyticOnNhd ℂ f (polydisc (0 : ι → ℂ) (fun _ => R)))
    (hg : AnalyticOnNhd ℂ g (polydisc (0 : ι → ℂ) (fun _ => R)))
    (h : ∀ A : Finset ι, f (indic A) = g (indic A)) (C : Finset ι) : coef f C = coef g C := by
  refine Balaban.Polymer.TwoTorusStep.eq_of_sum_powerset_eq_of_subset
    (g := coef f) (h := coef g) (C := C) ?_ C Finset.Subset.rfl
  intro A _
  rw [← sum_coef_unit hR hf A, ← sum_coef_unit hR hg A, h A]


end CoefAgree

section OldCoefRot

open Balaban.Analysis Balaban.Localization

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱ' : ℝ}
  (S : HoleStep d L N₁ m₁ k N ϱ ϱ')

/-- **The coefficient `T(X, J)` is `O(N)`-covariant**: for the step with the datum rotated, the
old term composed with the rotation, the fluctuation variables and the fixed values rotated, the
coefficient of Lemma AE is the same.  The standing conditions of the decoupled covariance are asked
at the vertices of the unit cube (the points where the coefficient is read, `sum_coef_unit`). -/
theorem HoleStep.oldCoef_rotBy {R : Matrix (Fin N) (Fin N) ℂ} (hR : Rᵀ * R = 1)
    (Q : Matrix (Fin N) (Fin N) ℝ) (hRQ : ∀ i j, R i j = ((Q i j : ℝ) : ℂ)) (h₀' : Fin N → ℝ) (hh)
    (ρ : ℝ) (X₁loc : S.U → Finset (CTorus d L N₁ m₁ (k + 1)))
    (X₁ : Finset (CTorus d L N₁ m₁ (k + 1))) (inner : Finset S.U) (ψout : S.U → Fin N → ℂ)
    (B B' : (S.U → Fin N → ℂ) → ℂ) (hB : ∀ c, B' (rotSite R c) = B c) (ψin : inner → Rn N)
    (J : Finset (coverOf S.G').cubeIdx) {Rp : ℝ} (hRp : 1 < Rp)
    (hana : AnalyticOnNhd ℂ (S.oldInterp (coverOf S.G') ρ X₁loc X₁ inner ψout B ψin)
      (polydisc (0 : Dec2.DecParams (coverOf S.G')) fun _ => Rp))
    (hana' : AnalyticOnNhd ℂ ((S.rotBy R h₀' hh).oldInterp (coverOf S.G') ρ X₁loc X₁ inner
        (rotSite R ψout) B' (fun u => (EuclideanSpace.equiv (Fin N) ℝ).symm (Q *ᵥ (ψin u))))
      (polydisc (0 : Dec2.DecParams (coverOf S.G')) fun _ => Rp)) {κ δ : ℝ}
    (hst : ∀ (A : Finset (coverOf S.G').cubeIdx) (b : S.U), CovStanding S.G' S.a S.a₁ S.ν
      (Dec2.decBgMult (coverOf S.G') S.G' S.a S.ν ρ
        (S.slocOf (coverOf S.G') X₁loc (coreExt (coverOf S.G') X₁ (indic A)) b) S.D') κ
      (Dec2.extS (coverOf S.G') (S.slocOf (coverOf S.G') X₁loc (coreExt (coverOf S.G') X₁ (indic A)) b)) δ
      (svec S.G' (Dec2.decBgField (coverOf S.G') S.G' S.a S.ν ρ
        (S.slocOf (coverOf S.G') X₁loc (coreExt (coverOf S.G') X₁ (indic A)) b) S.D'))
      (unitQ S.G') (unitP S.G')) :
    (S.rotBy R h₀' hh).oldCoef (coverOf S.G') ρ X₁loc X₁ inner (rotSite R ψout) B' J
        (fun u => (EuclideanSpace.equiv (Fin N) ℝ).symm (Q *ᵥ (ψin u))) =
      S.oldCoef (coverOf S.G') ρ X₁loc X₁ inner ψout B J ψin := by
  unfold HoleStep.oldCoef
  exact coef_congr_of_agree_unit hRp hana' hana
    (fun A => HoleStep.oldInterp_rotBy S hR Q hRQ h₀' hh ρ X₁loc X₁ inner ψout B B' hB ψin _ (hst A)) J

end OldCoefRot

end Balaban.Fluctuation
