/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.LFOldD7Real
public import Balaban.Spine.LFOldD7RotLoc

/-!
# The coefficient of the re-expanded old term on the local pair is real (the clause `real` of (D7))

`oldCoefLoc_im`: for a real multiscale field `ψ`, real `ψ'`, real physical field and external source
and real fluctuation field `ψ̂`, the coefficient `T(X, J)` of the re-expansion has imaginary part
`0`, provided the clause `real` of the record at the old label `X` (the old term is real at real
arguments) and the analyticity of the interpolated old term on a polydisc of radius `> 1`.  The
datum of the local step is real (`liftMixed_isReal`, `holeStepLoc_D'_isReal`), the composed field is
real (`HoleStep.composed_conj`, from `Dec2.decCovSqrt_isRealMat`), and the coefficient is determined
by the values at the vertices of the unit cube (`coef_conj_of_real_unit`).
`Spine/LFOldD7Support.lean` lifts clauses by summation over the fibre of an output label.
-/

@[expose] public section

open MeasureTheory Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField
  Balaban.Localization Matrix Balaban.LargeField

namespace Balaban.RootFSpine

open Balaban.Fluctuation Balaban.LargeField.Def7 Balaban.LargeField.RegionHistory

section LiftReal

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

theorem liftMixed_isReal (G : GeneratingSet d L N₀ (k + 1) ϱ)
    {Ω : Finset (Torus d (N₀ * L ^ (k + 1)))} (hΩ : IsBlockUnion L N₀ (k + 1) (k + 1) Ω)
    (hG : G.Ω (k + 1) ⊆ Ω) (ψ : Torus d (N₀ * L ^ (k + 1 - k)) → Fin N → ℂ)
    (ϑ : Torus d (N₀ * L ^ (k + 1 - (k + 1))) → Fin N → ℂ) (h : Fin N → ℂ)
    (hψ : ∀ z i, (ψ z i).im = 0) (hϑ : ∀ z i, (ϑ z i).im = 0) (hh : ∀ i, (h i).im = 0) :
    (liftMixed G hΩ hG ψ ϑ h).IsReal := by
  classical
  intro x i
  refine ⟨?_, ?_⟩
  · simp only [liftMixed, BgData.clip]
    split_ifs
    · unfold mixedLift blockLift
      split_ifs
      · exact hϑ _ _
      · exact hψ _ _
    · simp
  · simp only [liftMixed, BgData.clip]
    split_ifs
    · exact hh i
    · simp

end LiftReal

section LocReal

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {N m₁ : ℕ}
  (g : Geo S n R M) (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) (hM1 : g.M1 = S.L ^ m₁)

omit [NeZero M] in
theorem holeStepLoc_D'_isReal (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K)
    (hk1 : 1 ≤ k) (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (ψ : MultiFieldC S n M K N) (z : ℝ)
    (h₀ : Fin N → ℝ) (a₁ ν β p₁ δ : ℝ) (V : Set (CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)))
    (hψ : ∀ j y i, (ψ j y i).im = 0) :
    (holeStepLoc g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).D'.IsReal := by
  unfold holeStepLoc HoleStep.restrict
  dsimp only
  refine liftMixed_isReal _ _ _ _ _ _ (fun w i => ?_) (fun w i => ?_) (fun i => ?_)
  · exact hψ _ _ _
  · simp [scaleMulti, coverField, hψ]
  · simp

omit [NeZero M] in
theorem composedMulti_im {k : ℕ} (hk : k + 1 ≤ K) {ϱ' : ℝ}
    (G' : GeneratingSet S.d S.L ((g.c * n (k + 1)) * S.L ^ m₁) (k + 1) ϱ')
    (ψ : MultiFieldC S n M K N) (comp : unitPts G' → Fin N → ℂ)
    (hψ : ∀ j y i, (ψ j y i).im = 0) (hc : ∀ u i, (comp u i).im = 0) (j : ℕ) (y) (i : Fin N) :
    (composedMulti g hnn hM1 hk G' ψ comp j y i).im = 0 := by
  unfold composedMulti
  split_ifs
  · exact hψ _ _ _
  · exact hc _ _
  · exact hψ _ _ _
  · simp

/-- **The old term at real arguments is real**, from the clause `real` of the record at `X`. -/
theorem oldTermLF_conj {geo : Geo S n R M} {cs : OpConsts} {P : BudgetConsts} {k : ℕ}
    (rep : Rep S n R k0 K M N geo cs P k) (A : LabHist S n R k0 K) (X : Finset (Torus S.d (n k)))
    (hk : k + 1 ≤ K) {ϱ' : ℝ} (G' : GeneratingSet S.d S.L ((g.c * n (k + 1)) * S.L ^ m₁) (k + 1) ϱ')
    (ψ ψ' : MultiFieldC S n M K N) (hv : EuclideanSpace ℝ (Fin N)) (gx : GIdx S n M K N → ℂ)
    (hreal : ∀ (ψ₂ ψ₃ : MultiFieldC S n M K N) (h : Fin N → ℂ) (g₂ : GIdx S n M K N → ℂ),
      (∀ j y i, (ψ₂ j y i).im = 0 ∧ (ψ₃ j y i).im = 0) → (∀ i, (h i).im = 0) →
      (∀ p, (g₂ p).im = 0) → (rep.B A X ψ₂ ψ₃ h g₂).im = 0)
    (hψ : ∀ j y i, (ψ j y i).im = 0) (hψ' : ∀ j y i, (ψ' j y i).im = 0)
    (hgx : ∀ p, (gx p).im = 0) (comp : unitPts G' → Fin N → ℂ) (hc : ∀ u i, (comp u i).im = 0) :
    (oldTermLF g hnn hM1 rep A X hk G' ψ ψ' hv gx comp).im = 0 :=
  hreal _ _ _ _ (fun j y i => ⟨composedMulti_im g hnn hM1 hk G' ψ comp hψ hc j y i, hψ' j y i⟩)
    (fun i => by simp [hC]) hgx

variable {k : ℕ}

/-- **The coefficient `T(X, J)` on the local pair is real** (the clause `real` of (D7) for the
re-expanded old term, at the level of one coefficient).  Hypotheses: the clause `real` of the record
at `X` (`hreal`), analyticity of the interpolated old term on a polydisc of radius `Rp > 1`
(`hana`), and reality of the multiscale field, of `ψ'`, of the external source and of the fluctuation
field. -/
theorem oldCoefLoc_im (H : RegionHistory S n R k0 K) (hk : k + 1 ≤ K) (hk1 : 1 ≤ k)
    (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (ψ : MultiFieldC S n M K N) (z : ℝ) (h₀ : Fin N → ℝ)
    (a₁ ν β p₁ δ : ℝ) (ρc : ℝ) (ρ r r' : ℕ) {geo : Geo S n R M} {cs : OpConsts}
    {P : BudgetConsts} (rep : Rep S n R k0 K M N geo cs P k) (A : LabHist S n R k0 K)
    (X : Finset (Torus S.d (n k))) (ψ' : MultiFieldC S n M K N) (hv : EuclideanSpace ℝ (Fin N))
    (gx : GIdx S n M K N → ℂ) (J : Finset (ℕ × CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)))
    (ψhat : (holeStepLF g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).U → Fin N → ℂ)
    (hreal : ∀ (ψ₂ ψ₃ : MultiFieldC S n M K N) (h : Fin N → ℂ) (g₂ : GIdx S n M K N → ℂ),
      (∀ j y i, (ψ₂ j y i).im = 0 ∧ (ψ₃ j y i).im = 0) → (∀ i, (h i).im = 0) →
      (∀ p, (g₂ p).im = 0) → (rep.B A X ψ₂ ψ₃ h g₂).im = 0)
    (hψ : ∀ j y i, (ψ j y i).im = 0) (hψ' : ∀ j y i, (ψ' j y i).im = 0)
    (hgx : ∀ p, (gx p).im = 0) (hψhat : ∀ b i, (ψhat b i).im = 0) {Rp : ℝ} (hRp : 1 < Rp)
    (hana : AnalyticOnNhd ℂ
      ((holeStepLoc g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ (locSetXJ g hM1 H r r' X J)).oldInterp
        (coverOf (holeStepLoc g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ
          (locSetXJ g hM1 H r r' X J)).G') ρc
        (locDomsLF g hM1 (holeStepLoc g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ
          (locSetXJ g hM1 H r r' X J)) ρ)
        (collarCoreC (c := g.c) (H.step k) hM1 r X) ∅
        (restrictU _ _ _ _ _ _ _ ψhat)
        (oldTermLF g hnn hM1 rep A X hk (holeStepLoc g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ
          (locSetXJ g hM1 H r r' X J)).G' ψ ψ' hv gx)
        (fun b => absurd b.2 (Finset.notMem_empty _)))
      (Analysis.polydisc
        (0 : Dec2.DecParams (coverOf (holeStepLoc g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ
          (locSetXJ g hM1 H r r' X J)).G')) fun _ => Rp)) :
    (oldCoefLoc g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ ρc ρ r r' rep A X ψ' hv gx J ψhat).im
      = 0 := by
  unfold oldCoefLoc oldCoefLF
  rw [← Complex.conj_eq_iff_im]
  refine HoleStep.oldCoef_conj _
    (holeStepLoc_D'_isReal g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ _ hψ) _ _ _ _ _ _
    (fun q i => Complex.conj_eq_iff_im.2 (hψhat _ i)) _ (fun c hc => ?_) _ _ hRp hana
  exact Complex.conj_eq_iff_im.2 (oldTermLF_conj g hnn hM1 rep A X hk _ ψ ψ' hv gx hreal hψ hψ'
    hgx c fun u i => Complex.conj_eq_iff_im.1 (hc u i))

end LocReal

end Balaban.RootFSpine
