/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.LFOldD7Rot
public import Balaban.Spine.LFHoleStepLoc
public import Balaban.LargeField.Operators.QuietSymm
public import Balaban.Spine.LFOldCoef

/-!
# The coefficient of the re-expanded old term on the local pair is `O(N)`-covariant

`oldCoefLoc_rot`: rotating the multiscale field `ψ`, the field `h₀`, the second field `ψ'`, the
physical field, the external source and the fluctuation field `ψ̂` by `ρ ∈ O(N)` leaves the
coefficient `T(X, J)` of the re-expansion (reading HS-1′) unchanged.  It is the clause `rot` of
(D7) for the re-expanded old term at the level of one coefficient; `Spine/LFOldD7Support.lean`
lifts clauses by summation over the fibre of an output label.

Inputs (`OldCoefRotHyp`): the clause `rot` of the record at the old label `X`, the analyticity of
the interpolated old terms of the step and of the rotated step on a polydisc of radius `> 1`
(`analyticOnNhd_oldInterp`), and the standing conditions of the decoupled covariance at the vertices
of the unit cube.  The covariance of the step with the datum rotated is `holeStepLoc_rot`
(the mixed lift rotates, `liftMixed_rot`), that of the composed field is `HoleStep.composed_rotBy`,
`oldTermLF_rot` that of the old term at the composed multiscale field (`composedMulti_rot`).
-/

@[expose] public section

open MeasureTheory Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Localization Balaban.Localization.DecEquiv Matrix Balaban.LargeField

set_option linter.unusedSectionVars false

namespace Balaban.RootFSpine

section LiftRot

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

theorem mixedLift_rot (R : Matrix (Fin N) (Fin N) ℂ) (Ω : Finset (Torus d (N₀ * L ^ (k + 1))))
    (ψ : Torus d (N₀ * L ^ (k + 1 - k)) → Fin N → ℂ)
    (ϑ : Torus d (N₀ * L ^ (k + 1 - (k + 1))) → Fin N → ℂ) (x : Torus d (N₀ * L ^ (k + 1))) :
    mixedLift (L := L) Ω (fun z => R *ᵥ ψ z) (fun z => R *ᵥ ϑ z) x = R *ᵥ mixedLift Ω ψ ϑ x := by
  classical
  unfold mixedLift blockLift
  split_ifs <;> rfl

theorem liftMixed_rot (R : Matrix (Fin N) (Fin N) ℂ) (G : GeneratingSet d L N₀ (k + 1) ϱ)
    {Ω : Finset (Torus d (N₀ * L ^ (k + 1)))} (hΩ : IsBlockUnion L N₀ (k + 1) (k + 1) Ω)
    (hG : G.Ω (k + 1) ⊆ Ω) (ψ : Torus d (N₀ * L ^ (k + 1 - k)) → Fin N → ℂ)
    (ϑ : Torus d (N₀ * L ^ (k + 1 - (k + 1))) → Fin N → ℂ) (h : Fin N → ℂ) :
    (liftMixed G hΩ hG ψ ϑ h).rot R =
      liftMixed G hΩ hG (fun z => R *ᵥ ψ z) (fun z => R *ᵥ ϑ z) (R *ᵥ h) := by
  classical
  refine Background.BgData.ext' ?_ ?_
  · funext x
    simp only [BgData.rot, liftMixed, BgData.clip]
    split_ifs
    · exact (mixedLift_rot R Ω ψ ϑ x).symm
    · simp
  · funext x
    simp only [BgData.rot, liftMixed, BgData.clip]
    split_ifs <;> simp

end LiftRot


section LocRot

open Balaban.Fluctuation Balaban.LargeField.Def7 Balaban.LargeField.RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {N m₁ : ℕ}
  (g : Geo S n R M) (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) (hM1 : g.M1 = S.L ^ m₁)

/-- The complex matrix of a rotation. -/
noncomputable def rotCMat (ρ : OrthN N) : Matrix (Fin N) (Fin N) ℂ := (rotMat ρ).map (↑)

/-- The rotated field `h₀`. -/
noncomputable def rotH0 (ρ : OrthN N) (h₀ : Fin N → ℝ) : Fin N → ℝ := fun i => ∑ j, rotEntry ρ i j * h₀ j

theorem rotCMat_apply (ρ : OrthN N) (i j : Fin N) : rotCMat ρ i j = ((rotEntry ρ i j : ℝ) : ℂ) := by
  simp [rotCMat, rotMat]

theorem rotCMat_orth (ρ : OrthN N) : (rotCMat ρ)ᵀ * rotCMat ρ = 1 := by
  ext i j
  have h := congrFun (congrFun (rotMat_transpose_mul ρ) i) j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] at h ⊢
  simp only [rotCMat_apply]
  have h' : ∀ k, rotMat ρ k i = rotEntry ρ k i := fun k => by simp [rotMat]
  simp only [h'] at h
  by_cases hij : i = j
  · subst hij; simp only [ite_true] at h ⊢; rw [← Complex.ofReal_one, ← h]; push_cast; rfl
  · simp only [hij, ite_false] at h ⊢; rw [← Complex.ofReal_zero, ← h]; push_cast; rfl

theorem rotC_eq_mulVec (ρ : OrthN N) (v : Fin N → ℂ) : rotC ρ v = rotCMat ρ *ᵥ v := by
  funext i
  simp [rotC, Matrix.mulVec, dotProduct, rotCMat_apply]

theorem rotCMat_h0 (ρ : OrthN N) (h₀ : Fin N → ℝ) :
    rotCMat ρ *ᵥ (fun i => ((h₀ i : ℝ) : ℂ)) = fun i => ((rotH0 ρ h₀ i : ℝ) : ℂ) := by
  funext i
  simp [rotCMat, rotH0, Matrix.mulVec, dotProduct, Complex.ofReal_sum, rotMat]

theorem coverField_rotM (ρ : OrthN N) {k : ℕ} (hk : k + 1 ≤ K) (ψ : MultiFieldC S n M K N) (i : ℕ)
    (hi : i ≤ k + 1) :
    coverField g hnn hM1 hk (rotM ρ ψ) i hi = fun z => rotCMat ρ *ᵥ coverField g hnn hM1 hk ψ i hi z := by
  funext z
  simp only [coverField, rotM]
  exact rotC_eq_mulVec ρ _

theorem scaleMulti_rotM (ρ : OrthN N) (z : ℝ) (ψ : MultiFieldC S n M K N) :
    scaleMulti z (rotM ρ ψ) = rotM ρ (scaleMulti z ψ) := by
  funext j y i
  simp only [scaleMulti, rotM, rotC, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by ring

theorem holeStepLoc_rot (ρo : OrthN N) (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K)
    (hk1 : 1 ≤ k) (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (ψ : MultiFieldC S n M K N) (z : ℝ)
    (h₀ : Fin N → ℝ) (a₁ ν β p₁ δ : ℝ) (V : Set (CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1))) :
    holeStepLoc g hnn hM1 H hk hk1 hρ (rotM ρo ψ) z (rotH0 ρo h₀) a₁ ν β p₁ δ V =
      (holeStepLoc g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).rotBy (rotCMat ρo) (rotH0 ρo h₀)
        (rotCMat_h0 ρo h₀) := by
  unfold holeStepLoc HoleStep.restrict HoleStep.rotBy
  congr 1
  dsimp only
  rw [liftMixed_rot]
  congr 1
  · rw [scaleMulti_rotM, coverField_rotM g hnn hM1 ρo hk _ (k + 1)]
  · exact (rotCMat_h0 ρo h₀).symm

theorem composedMulti_rot (ρo : OrthN N) {k : ℕ} (hk : k + 1 ≤ K) {ϱ' : ℝ}
    (G' : GeneratingSet S.d S.L ((g.c * n (k + 1)) * S.L ^ m₁) (k + 1) ϱ')
    (ψ : MultiFieldC S n M K N) (comp : unitPts G' → Fin N → ℂ) :
    composedMulti g hnn hM1 hk G' (rotM ρo ψ) (rotSite (rotCMat ρo) comp) =
      rotM ρo (composedMulti g hnn hM1 hk G' ψ comp) := by
  funext j y
  unfold composedMulti rotM
  by_cases h1 : j < k
  · simp [h1]
  · by_cases h2 : j = k
    · subst h2
      simp only [h1, ↓reduceIte, dite_true]
      split_ifs
      · rw [rotC_eq_mulVec]; rfl
      · rfl
    · have : ¬ j = k := h2
      simp only [h1, this, ↓reduceIte, dite_false]
      funext i
      simp [rotC]

theorem hC_rot (ρo : OrthN N) (hv : EuclideanSpace ℝ (Fin N)) :
    rotC ρo (hC hv) = hC (ρo hv) := by
  funext i
  simp only [rotC, hC]
  rw [rot_apply_coord]
  push_cast
  rfl

theorem oldTermLF_rot {geo : Geo S n R M} {cs : OpConsts} {P : BudgetConsts} {k : ℕ}
    (rep : Rep S n R k0 K M N geo cs P k) (A : LabHist S n R k0 K) (X : Finset (Torus S.d (n k)))
    (hk : k + 1 ≤ K) {ϱ' : ℝ} (G' : GeneratingSet S.d S.L ((g.c * n (k + 1)) * S.L ^ m₁) (k + 1) ϱ')
    (ρo : OrthN N) (ψ ψ' : MultiFieldC S n M K N) (hv : EuclideanSpace ℝ (Fin N))
    (gx : GIdx S n M K N → ℂ) (comp : unitPts G' → Fin N → ℂ)
    (hrot : ∀ (ψ₂ ψ₃ : MultiFieldC S n M K N) (h : Fin N → ℂ) (g₂ : GIdx S n M K N → ℂ),
      rep.B A X (rotM ρo ψ₂) (rotM ρo ψ₃) (rotC ρo h) (rotG ρo g₂) = rep.B A X ψ₂ ψ₃ h g₂) :
    oldTermLF g hnn hM1 rep A X hk G' (rotM ρo ψ) (rotM ρo ψ') (ρo hv) (rotG ρo gx)
        (rotSite (rotCMat ρo) comp) = oldTermLF g hnn hM1 rep A X hk G' ψ ψ' hv gx comp := by
  unfold oldTermLF
  rw [composedMulti_rot g hnn hM1 ρo hk G' ψ comp, ← hC_rot]
  exact hrot _ _ _ _

variable {k : ℕ}

/-- **The coefficient of an old term on a step** (`oldCoefLoc` for an arbitrary step): the
coefficient `oldCoefLF` with no integration variable. -/
noncomputable def oldCoefAt (H : RegionHistory S n R k0 K) (hk : k + 1 ≤ K)
    (St : HoleStep S.d S.L (g.c * n (k + 1)) m₁ k N (minSep S.L g.M1) (minSep S.L g.M1))
    (ρc : ℝ) (ρ r : ℕ) {geo : Geo S n R M} {cs : OpConsts} {P : BudgetConsts}
    (rep : Rep S n R k0 K M N geo cs P k) (A : LabHist S n R k0 K) (X : Finset (Torus S.d (n k)))
    (ψ ψ' : MultiFieldC S n M K N) (hv : EuclideanSpace ℝ (Fin N)) (gx : GIdx S n M K N → ℂ)
    (J : Finset (ℕ × CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)))
    (ψout : St.U → Fin N → ℂ) : ℂ :=
  oldCoefLF g hnn hM1 St H hk (coverOf St.G') ρc ρ r ∅ ψout rep A X ψ ψ' hv gx
    (locCubes g (coverOf St.G') J) (fun b => absurd b.2 (Finset.notMem_empty _))

theorem oldCoefAt_congr_step (H : RegionHistory S n R k0 K) (hk : k + 1 ≤ K)
    {St₁ St₂ : HoleStep S.d S.L (g.c * n (k + 1)) m₁ k N (minSep S.L g.M1) (minSep S.L g.M1)}
    (e : St₁ = St₂) (ρc : ℝ) (ρ r : ℕ) {geo : Geo S n R M} {cs : OpConsts} {P : BudgetConsts}
    (rep : Rep S n R k0 K M N geo cs P k) (A : LabHist S n R k0 K) (X : Finset (Torus S.d (n k)))
    (ψ ψ' : MultiFieldC S n M K N) (hv : EuclideanSpace ℝ (Fin N)) (gx : GIdx S n M K N → ℂ)
    (J : Finset (ℕ × CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)))
    (ψ₁ : St₁.U → Fin N → ℂ) (ψ₂ : St₂.U → Fin N → ℂ) (h : ∀ b, ψ₁ b = ψ₂ (e ▸ b)) :
    oldCoefAt g hnn hM1 H hk St₁ ρc ρ r rep A X ψ ψ' hv gx J ψ₁ =
      oldCoefAt g hnn hM1 H hk St₂ ρc ρ r rep A X ψ ψ' hv gx J ψ₂ := by
  subst e
  congr 1
  funext b
  exact h b

/-- **The hypotheses of the covariance of the coefficient on a step**: the clause `rot` of (D7) of
the record at `X`, the analyticity of the interpolated old term of the step and of the rotated step on
a polydisc of radius `Rp > 1`, and the standing conditions of the decoupled covariance at the
vertices of the unit cube. -/
structure OldCoefRotHyp (H : RegionHistory S n R k0 K) (hk : k + 1 ≤ K)
    (St : HoleStep S.d S.L (g.c * n (k + 1)) m₁ k N (minSep S.L g.M1) (minSep S.L g.M1))
    (ρo : OrthN N) (h₀' : Fin N → ℝ) (hh : rotCMat ρo *ᵥ (fun i => ((St.h₀ i : ℝ) : ℂ)) =
      fun i => ((h₀' i : ℝ) : ℂ))
    (ρc : ℝ) (ρ r : ℕ) {geo : Geo S n R M} {cs : OpConsts} {P : BudgetConsts}
    (rep : Rep S n R k0 K M N geo cs P k) (A : LabHist S n R k0 K) (X : Finset (Torus S.d (n k)))
    (ψ ψ' : MultiFieldC S n M K N) (hv : EuclideanSpace ℝ (Fin N)) (gx : GIdx S n M K N → ℂ)
    (ψout : St.U → Fin N → ℂ) (Rp : ℝ) (κ δ : ℝ) : Prop where
  hrot : ∀ (ψ₂ ψ₃ : MultiFieldC S n M K N) (h : Fin N → ℂ) (g₂ : GIdx S n M K N → ℂ),
    rep.B A X (rotM ρo ψ₂) (rotM ρo ψ₃) (rotC ρo h) (rotG ρo g₂) = rep.B A X ψ₂ ψ₃ h g₂
  hRp : 1 < Rp
  hana : AnalyticOnNhd ℂ (St.oldInterp (coverOf St.G') ρc (locDomsLF g hM1 St ρ)
    (collarCoreC (c := g.c) (H.step k) hM1 r X) ∅ ψout
    (oldTermLF g hnn hM1 rep A X hk St.G' ψ ψ' hv gx)
    (fun b => absurd b.2 (Finset.notMem_empty _)))
    (Analysis.polydisc (0 : Dec2.DecParams (coverOf St.G')) fun _ => Rp)
  hana' : AnalyticOnNhd ℂ ((St.rotBy (rotCMat ρo) h₀' hh).oldInterp (coverOf St.G') ρc
    (locDomsLF g hM1 St ρ) (collarCoreC (c := g.c) (H.step k) hM1 r X) ∅
    (rotSite (rotCMat ρo) ψout)
    (oldTermLF g hnn hM1 rep A X hk St.G' (rotM ρo ψ) (rotM ρo ψ') (ρo hv) (rotG ρo gx))
    (fun b => absurd b.2 (Finset.notMem_empty _)))
    (Analysis.polydisc (0 : Dec2.DecParams (coverOf St.G')) fun _ => Rp)
  hst : ∀ (Ac : Finset (coverOf St.G').cubeIdx) (b : St.U), CovStanding St.G' St.a St.a₁ St.ν
    (Dec2.decBgMult (coverOf St.G') St.G' St.a St.ν ρc
      (St.slocOf (coverOf St.G') (locDomsLF g hM1 St ρ)
        (Fluctuation.HoleStep.coreExt (coverOf St.G') (collarCoreC (c := g.c) (H.step k) hM1 r X)
          (indic Ac)) b) St.D') κ
    (Dec2.extS (coverOf St.G') (St.slocOf (coverOf St.G') (locDomsLF g hM1 St ρ)
      (Fluctuation.HoleStep.coreExt (coverOf St.G') (collarCoreC (c := g.c) (H.step k) hM1 r X)
        (indic Ac)) b)) δ
    (svec St.G' (Dec2.decBgField (coverOf St.G') St.G' St.a St.ν ρc
      (St.slocOf (coverOf St.G') (locDomsLF g hM1 St ρ)
        (Fluctuation.HoleStep.coreExt (coverOf St.G') (collarCoreC (c := g.c) (H.step k) hM1 r X)
          (indic Ac)) b) St.D'))
    (unitQ St.G') (unitP St.G')

/-- **`O(N)`-covariance of the coefficient `T(X, J)` on a step.** -/
theorem oldCoefAt_rotBy (H : RegionHistory S n R k0 K) (hk : k + 1 ≤ K)
    (St : HoleStep S.d S.L (g.c * n (k + 1)) m₁ k N (minSep S.L g.M1) (minSep S.L g.M1))
    (ρo : OrthN N) (h₀' : Fin N → ℝ) (hh : rotCMat ρo *ᵥ (fun i => ((St.h₀ i : ℝ) : ℂ)) =
      fun i => ((h₀' i : ℝ) : ℂ))
    (ρc : ℝ) (ρ r : ℕ) {geo : Geo S n R M} {cs : OpConsts} {P : BudgetConsts}
    (rep : Rep S n R k0 K M N geo cs P k) (A : LabHist S n R k0 K) (X : Finset (Torus S.d (n k)))
    (ψ ψ' : MultiFieldC S n M K N) (hv : EuclideanSpace ℝ (Fin N)) (gx : GIdx S n M K N → ℂ)
    (J : Finset (ℕ × CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)))
    (ψout : St.U → Fin N → ℂ) {Rp κ δ : ℝ}
    (hyp : OldCoefRotHyp g hnn hM1 H hk St ρo h₀' hh ρc ρ r rep A X ψ ψ' hv gx ψout Rp κ δ) :
    oldCoefAt g hnn hM1 H hk (St.rotBy (rotCMat ρo) h₀' hh) ρc ρ r rep A X (rotM ρo ψ) (rotM ρo ψ')
        (ρo hv) (rotG ρo gx) J (rotSite (rotCMat ρo) ψout) =
      oldCoefAt g hnn hM1 H hk St ρc ρ r rep A X ψ ψ' hv gx J ψout := by
  unfold oldCoefAt oldCoefLF
  have hRQ : ∀ i j, rotCMat ρo i j = ((rotMat ρo i j : ℝ) : ℂ) := fun i j => by
    rw [rotCMat_apply]; simp [rotMat]
  have key := HoleStep.oldCoef_rotBy St (rotCMat_orth ρo) (rotMat ρo) hRQ h₀' hh ρc
    (locDomsLF g hM1 St ρ) (collarCoreC (c := g.c) (H.step k) hM1 r X) ∅ ψout
    (oldTermLF g hnn hM1 rep A X hk St.G' ψ ψ' hv gx)
    (oldTermLF g hnn hM1 rep A X hk St.G' (rotM ρo ψ) (rotM ρo ψ') (ρo hv) (rotG ρo gx))
    (fun c => oldTermLF_rot g hnn hM1 rep A X hk St.G' ρo ψ ψ' hv gx c hyp.hrot)
    (fun b => absurd b.2 (Finset.notMem_empty _)) (locCubes g (coverOf St.G') J) hyp.hRp hyp.hana
    hyp.hana' hyp.hst
  have e : (fun u : (∅ : Finset St.U) =>
      (EuclideanSpace.equiv (Fin N) ℝ).symm (rotMat ρo *ᵥ ((fun b : (∅ : Finset St.U) =>
        (absurd b.2 (Finset.notMem_empty _) : Rn N)) u))) =
      (fun b => absurd b.2 (Finset.notMem_empty _)) :=
    funext fun b => absurd b.2 (Finset.notMem_empty _)
  rw [e] at key
  exact key

theorem HoleStep.val_cast_eq {St₁ St₂ : HoleStep S.d S.L (g.c * n (k + 1)) m₁ k N (minSep S.L g.M1)
    (minSep S.L g.M1)} (e : St₁ = St₂) (b : St₁.U) : (e ▸ b : St₂.U).1 = b.1 := by
  subst e; rfl

/-- **The coefficient `T(X, J)` on the local pair is `O(N)`-covariant** (the clause `rot` of (D7) for
the re-expanded old term, at the level of one coefficient): rotating the multiscale field `ψ`, the
field `h₀`, the second field `ψ'`, the physical field `hv`, the external source `gx` and the
fluctuation field `ψ̂` by `ρ ∈ O(N)` leaves the coefficient unchanged.  Hypotheses: the clause `rot` of
the record at `X`, analyticity of the interpolated old terms, the standing conditions
(`OldCoefRotHyp`). -/
theorem oldCoefLoc_rot (ρo : OrthN N) (H : RegionHistory S n R k0 K) (hk : k + 1 ≤ K) (hk1 : 1 ≤ k)
    (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (ψ : MultiFieldC S n M K N) (z : ℝ) (h₀ : Fin N → ℝ)
    (a₁ ν β p₁ δ : ℝ) (ρc : ℝ) (ρ r r' : ℕ) {geo : Geo S n R M} {cs : OpConsts}
    {P : BudgetConsts} (rep : Rep S n R k0 K M N geo cs P k) (A : LabHist S n R k0 K)
    (X : Finset (Torus S.d (n k))) (ψ' : MultiFieldC S n M K N) (hv : EuclideanSpace ℝ (Fin N))
    (gx : GIdx S n M K N → ℂ) (J : Finset (ℕ × CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)))
    (ψhat : (holeStepLF g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).U → Fin N → ℂ) {Rp κ δs : ℝ}
    (hyp : OldCoefRotHyp g hnn hM1 H hk
      (holeStepLoc g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ (locSetXJ g hM1 H r r' X J)) ρo
      (rotH0 ρo h₀) (rotCMat_h0 ρo h₀) ρc ρ r rep A X ψ ψ' hv gx
      (restrictU _ _ _ _ _ _ _ ψhat) Rp κ δs) :
    oldCoefLoc g hnn hM1 H hk hk1 hρ (rotM ρo ψ) z (rotH0 ρo h₀) a₁ ν β p₁ δ ρc ρ r r' rep A X
        (rotM ρo ψ') (ρo hv) (rotG ρo gx) J (rotSite (rotCMat ρo) ψhat) =
      oldCoefLoc g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ ρc ρ r r' rep A X ψ' hv gx J ψhat := by
  have e := holeStepLoc_rot g hnn hM1 ρo H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ (locSetXJ g hM1 H r r' X J)
  have h1 : oldCoefLoc g hnn hM1 H hk hk1 hρ (rotM ρo ψ) z (rotH0 ρo h₀) a₁ ν β p₁ δ ρc ρ r r' rep A X
        (rotM ρo ψ') (ρo hv) (rotG ρo gx) J (rotSite (rotCMat ρo) ψhat) =
      oldCoefAt g hnn hM1 H hk
        (holeStepLoc g hnn hM1 H hk hk1 hρ (rotM ρo ψ) z (rotH0 ρo h₀) a₁ ν β p₁ δ
          (locSetXJ g hM1 H r r' X J)) ρc ρ r rep A X (rotM ρo ψ) (rotM ρo ψ') (ρo hv) (rotG ρo gx) J
        (restrictU _ _ _ _ _ _ _ (rotSite (rotCMat ρo) ψhat)) := rfl
  have h2 : oldCoefLoc g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ ρc ρ r r' rep A X ψ' hv gx J ψhat =
      oldCoefAt g hnn hM1 H hk
        (holeStepLoc g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ (locSetXJ g hM1 H r r' X J)) ρc ρ r
        rep A X ψ ψ' hv gx J (restrictU _ _ _ _ _ _ _ ψhat) := rfl
  rw [h1, h2, ← oldCoefAt_rotBy g hnn hM1 H hk _ ρo _ (rotCMat_h0 ρo h₀) ρc ρ r rep A X ψ ψ' hv gx J _
    hyp]
  refine oldCoefAt_congr_step g hnn hM1 H hk e ρc ρ r rep A X (rotM ρo ψ) (rotM ρo ψ') (ρo hv)
    (rotG ρo gx) J _ _ ?_
  intro b
  simp only [restrictU, rotSite]
  congr 2
  exact Subtype.ext (HoleStep.val_cast_eq g e b).symm

end LocRot

end Balaban.RootFSpine
