/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.LFOldStepClauses

/-!
# The clauses `real` and `rot` of (D7) for the old part in the form of the step

* `reExt_rotC`, `reExtE_rotC`: the real part of a rotated complex field is the rotated real part;
* `oldStepB_real` (clause `real`): from `oldBAtAt_im` and `oldCoefLoc2_im` (the record's clause
  `real`), given the reality of the interaction family and of the fixed values at real arguments and
  the analyticity of the interpolated old terms on a polydisc of radius `Rp > 1` at real arguments
  (`hana`);
* `oldStepB_rot` (clause `rot`): from `oldBAtAt_rot` and `oldCoefLoc2_rot`, given the covariance of
  the interaction family and of the fixed values and the hypotheses `OldCoefRotHyp` of the coefficients
  (`hcoef`: the record's clause `rot`, the analyticity of the interpolated old terms and the standing
  conditions of the decoupled covariance at the vertices of the unit cube).

The clauses `real` and `rot` of (D7) are asked at every argument, not only on the H7 domain; `hana` and
`hcoef` are asked at every (real) argument accordingly.
-/

@[expose] public section

open MeasureTheory Balaban Balaban.LargeField Balaban.LargeField.Def7 Balaban.Multiscale
  Balaban.Localization Balaban.Fluctuation Balaban.LargeField.RegionHistory Balaban.Background
  Balaban.Polymer Balaban.Localization.DecEquiv

namespace Balaban.RootFSpine

/-- The real part of a rotated complex field is the rotated real part. -/
theorem reExt_rotC {N : ℕ} (ρo : OrthN N) (h : Fin N → ℂ) :
    reExt (rotC ρo h) = rotH0 ρo (reExt h) := by
  funext i
  simp [reExt, rotC, rotH0, Complex.re_sum]

/-- The real part of a rotated complex field is the rotated real part (as a vector of `ℝ^N`). -/
theorem reExtE_rotC {N : ℕ} (ρo : OrthN N) (h : Fin N → ℂ) :
    reExtE (rotC ρo h) = ρo (reExtE h) := by
  ext i
  rw [rot_apply_coord]
  simp [reExtE, reExt, rotC, Complex.re_sum]

section StepRot

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {N m₁ : ℕ}
  (g : Geo S n R M) (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) (hM1 : g.M1 = S.L ^ m₁)

/-- **The clause `real` of (D7) for the old part in the form of the step** (`oldBAtAt_im`,
`oldCoefLoc2_im`): for a record of scale `k + 1` whose boundary terms are `oldStepB …` re-expanding the
terms of `rep` (its histories histories of `rep`), if `rep` satisfies (D7) of the post-`R` class at the
regions `Z_k`, the activities of the interaction family at real arguments and real interpolation
parameters are real (`hIF`), the fixed values at real fields are real (`hout`), and at every real
argument the interpolated old terms of the local pairs are analytic on the polydisc of radius
`Rp > 1` (`hana`), then the old part is real at real arguments. -/
theorem oldStepB_real {m₀ : ℕ} (F : FineSizeFrame S n M K m₀ m₁) {k : ℕ} (hk : k + 1 ≤ K)
    (hk1 : 1 ≤ k) (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (z a₁ ν β p₁ δ : ℝ)
    (inner : ∀ A : LabHist S n R k0 K, Finset (unitPts (stepG' g hnn hM1 A.H hk hρ)))
    (cb : ∀ A : LabHist S n R k0 K, inner A →
      CubeB (d := S.d) (L := S.L) (N₁ := F.N₁) (m₁ := m₁) (K := K) m₀ (k + 1)
        (d7Pull F (k + 1) (OmegaCube A.H (k + 1))))
    (hp : 0 < p₁)
    (IF : ∀ A : LabHist S n R k0 K,
      LocIntFam (fun b => {u : inner A // cb A u = b} → Rn N) (OldPrm S n M K N))
    (ψout : ∀ A : LabHist S n R k0 K, MultiFieldC S n M K N → (Fin N → ℂ) →
      unitPts (stepG' g hnn hM1 A.H hk hρ) → Fin N → ℂ)
    (rψ ρc : ℝ) (ρ r r' : ℕ) {cs : OpConsts} {P : BudgetConsts}
    (rep : Rep S n R k0 K M N g cs P k) {aw μs ε ε1 νs : ℕ → ℝ} {fac rate : ℝ}
    {hv : EuclideanSpace ℝ (Fin N)}
    (hrec : D7BdryPost F hnn (Nat.le_of_succ_le hk) rep (fun A => (A.H.step k).Z) aw μs ε ε1 νs fac
      rate hv)
    {cs' : OpConsts} {P' : BudgetConsts} (rep' : Rep S n R k0 K M N g cs' P' (k + 1))
    (hhist : ∀ A ∈ rep'.hist, A ∈ rep.hist)
    (hB : rep'.B = oldStepB g hnn hM1 F hk hk1 hρ z a₁ ν β p₁ δ inner cb hp IF ψout rψ ρc ρ r r' rep)
    (hIF : ∀ (A : LabHist S n R k0 K) (q : OldPrm S n M K N),
      (∀ j y i, (q.1 j y i).im = 0 ∧ (q.2.1 j y i).im = 0) → (∀ i, (q.2.2.1 i).im = 0) →
      (∀ p, (q.2.2.2 p).im = 0) → ∀ (u : ℝ) y Φ, ((((IF A).A q (u : ℂ)).H y Φ).im = 0))
    (hout : ∀ (A : LabHist S n R k0 K) (ψ : MultiFieldC S n M K N) (h : Fin N → ℂ),
      (∀ j y i, (ψ j y i).im = 0) → (∀ i, (h i).im = 0) → ∀ b i, (ψout A ψ h b i).im = 0)
    {Rp : ℝ} (hRp : 1 < Rp)
    (hana : ∀ A ∈ rep'.hist, ∀ (ψ ψ' : MultiFieldC S n M K N) (h : Fin N → ℂ)
      (gx : GIdx S n M K N → ℂ), (∀ j y i, (ψ j y i).im = 0 ∧ (ψ' j y i).im = 0) →
      (∀ i, (h i).im = 0) → (∀ p, (gx p).im = 0) → ∀ X ∈ oldDoms F A.H k,
      ∀ J : Finset (ℕ × CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)),
      GoodJAt g hnn hM1 F A.H hk hρ r r' (d7Pull F (k + 1) (OmegaCube A.H (k + 1))) (stencilX X) X J →
      ∀ ψhat : (holeStepLF g hnn hM1 A.H hk hk1 hρ ψ z (reExt h) a₁ ν β p₁ δ).U → Fin N → ℂ,
      (∀ b i, (ψhat b i).im = 0) →
      (∀ b ∈ locUnits g hnn hM1 A.H hk hk1 hρ ψ z (reExt h) a₁ ν β p₁ δ
        (locSetXJ g hM1 A.H r r' (stencilX X) J), vn (ψhat b) < rψ) →
      AnalyticOnNhd ℂ
        ((holeStepLoc2 g hnn hM1 A.H hk hk1 hρ ψ z (reExt h) a₁ ν β p₁ δ
          (locSetXJ2 g hM1 A.H r r' X J)).oldInterp
          (coverOf (holeStepLoc2 g hnn hM1 A.H hk hk1 hρ ψ z (reExt h) a₁ ν β p₁ δ
            (locSetXJ2 g hM1 A.H r r' X J)).G') ρc
          (locDomsLF g hM1 (holeStepLoc2 g hnn hM1 A.H hk hk1 hρ ψ z (reExt h) a₁ ν β p₁ δ
            (locSetXJ2 g hM1 A.H r r' X J)) ρ)
          (collarCoreC (c := g.c) (A.H.step k) hM1 r X) ∅
          (restrictU _ _ _ _ _ _ _ ψhat)
          (oldTermLF g hnn hM1 rep A X hk (holeStepLoc2 g hnn hM1 A.H hk hk1 hρ ψ z (reExt h) a₁ ν β
            p₁ δ (locSetXJ2 g hM1 A.H r r' X J)).G' ψ ψ' (reExtE h) gx)
          (fun b => absurd b.2 (Finset.notMem_empty _)))
        (Analysis.polydisc
          (0 : Dec2.DecParams (coverOf (holeStepLoc2 g hnn hM1 A.H hk hk1 hρ ψ z (reExt h) a₁ ν β p₁ δ
            (locSetXJ2 g hM1 A.H r r' X J)).G')) fun _ => Rp))
    (Zof : LabHist S n R k0 K → Set (Torus S.d (n (k + 1)))) (aw' μs' ε' ε1' νs' : ℕ → ℝ)
    (fac' rate' : ℝ) (hv' : EuclideanSpace ℝ (Fin N)) :
    D7Clause.real.Holds F hnn hk rep' Zof aw' μs' ε' ε1' νs' fac' rate' hv' := by
  intro A hA Y _ ψ ψ' h gx hψ hh hg
  rw [hB]
  have hA' := hhist A hA
  exact oldBAtAt_im g hnn hM1 true F A.H stencilX hk hk1 hρ ψ z (reExt h) a₁ ν β p₁ δ (inner A) (cb A)
    hp ((IF A).at (ψ, ψ', h, gx)) (ψout A ψ h) rψ ρc ρ r r' rep A (oldDoms F A.H k) ψ' (reExtE h) gx Y
    (hIF A (ψ, ψ', h, gx) hψ hh hg) (hout A ψ h (fun j y i => (hψ j y i).1) hh)
    (fun X hX J hJ ψhat hre hball => oldCoefLoc2_im g hnn hM1 A.H hk hk1 hρ ψ z (reExt h) a₁ ν β p₁ δ
      ρc ρ r r' rep A X ψ' (reExtE h) gx J ψhat
      (hrec.real A hA' X (mem_bdryDomsPost_of_mem_oldDoms hX)) (fun j y i => (hψ j y i).1)
      (fun j y i => (hψ j y i).2) hg hre hRp (hana A hA ψ ψ' h gx hψ hh hg X hX J hJ ψhat hre hball))

/-- **The clause `rot` of (D7) for the old part in the form of the step** (`oldBAtAt_rot`,
`oldCoefLoc2_rot`): for a record of scale `k + 1` whose boundary terms are `oldStepB …` re-expanding the
terms of `rep`, if the interaction family is covariant (`hIF`: the activities at the rotated arguments,
on the rotated cube variables, are those at the arguments), the fixed values are covariant (`hout`) and
the coefficients satisfy the hypotheses `OldCoefRotHyp` at every argument (`hcoef`), then the old part
is `O(N)`-invariant. -/
theorem oldStepB_rot {m₀ : ℕ} (F : FineSizeFrame S n M K m₀ m₁) {k : ℕ} (hk : k + 1 ≤ K)
    (hk1 : 1 ≤ k) (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (z a₁ ν β p₁ δ : ℝ)
    (inner : ∀ A : LabHist S n R k0 K, Finset (unitPts (stepG' g hnn hM1 A.H hk hρ)))
    (cb : ∀ A : LabHist S n R k0 K, inner A →
      CubeB (d := S.d) (L := S.L) (N₁ := F.N₁) (m₁ := m₁) (K := K) m₀ (k + 1)
        (d7Pull F (k + 1) (OmegaCube A.H (k + 1))))
    (hp : 0 < p₁)
    (IF : ∀ A : LabHist S n R k0 K,
      LocIntFam (fun b => {u : inner A // cb A u = b} → Rn N) (OldPrm S n M K N))
    (ψout : ∀ A : LabHist S n R k0 K, MultiFieldC S n M K N → (Fin N → ℂ) →
      unitPts (stepG' g hnn hM1 A.H hk hρ) → Fin N → ℂ)
    (rψ ρc : ℝ) (ρ r r' : ℕ) {cs : OpConsts} {P : BudgetConsts}
    (rep : Rep S n R k0 K M N g cs P k)
    {cs' : OpConsts} {P' : BudgetConsts} (rep' : Rep S n R k0 K M N g cs' P' (k + 1))
    (hB : rep'.B = oldStepB g hnn hM1 F hk hk1 hρ z a₁ ν β p₁ δ inner cb hp IF ψout rψ ρc ρ r r' rep)
    (hIF : ∀ (A : LabHist S n R k0 K) (ρo : OrthN N) (q : OldPrm S n M K N) (u : ℝ) y Φ,
      ((IF A).A (rotM ρo q.1, rotM ρo q.2.1, rotC ρo q.2.2.1, rotG ρo q.2.2.2) (u : ℂ)).H y
          (fun b v => ρo (Φ b v)) = ((IF A).A q (u : ℂ)).H y Φ)
    (hout : ∀ (A : LabHist S n R k0 K) (ρo : OrthN N) (ψ : MultiFieldC S n M K N) (h : Fin N → ℂ),
      ψout A (rotM ρo ψ) (rotC ρo h) = rotSite (rotCMat ρo) (ψout A ψ h))
    (hcoef : ∀ A ∈ rep'.hist, ∀ (ρo : OrthN N) (ψ ψ' : MultiFieldC S n M K N) (h : Fin N → ℂ)
      (gx : GIdx S n M K N → ℂ), ∀ X ∈ oldDoms F A.H k,
      ∀ J : Finset (ℕ × CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)),
      GoodJAt g hnn hM1 F A.H hk hρ r r' (d7Pull F (k + 1) (OmegaCube A.H (k + 1))) (stencilX X) X J →
      ∀ ψhat : (holeStepLF g hnn hM1 A.H hk hk1 hρ ψ z (reExt h) a₁ ν β p₁ δ).U → Fin N → ℂ,
      (∀ b ∈ locUnits g hnn hM1 A.H hk hk1 hρ ψ z (reExt h) a₁ ν β p₁ δ
        (locSetXJ g hM1 A.H r r' (stencilX X) J), vn (ψhat b) < rψ) →
      ∃ Rp κ δs : ℝ, OldCoefRotHyp g hnn hM1 A.H hk
        (holeStepLoc2 g hnn hM1 A.H hk hk1 hρ ψ z (reExt h) a₁ ν β p₁ δ (locSetXJ2 g hM1 A.H r r' X J))
        ρo (rotH0 ρo (reExt h)) (rotCMat_h0 ρo (reExt h)) ρc ρ r rep A X ψ ψ' (reExtE h) gx
        (restrictU _ _ _ _ _ _ _ ψhat) Rp κ δs)
    (Zof : LabHist S n R k0 K → Set (Torus S.d (n (k + 1)))) (aw μs ε ε1 νs : ℕ → ℝ)
    (fac rate : ℝ) (hv : EuclideanSpace ℝ (Fin N)) :
    D7Clause.rot.Holds F hnn hk rep' Zof aw μs ε ε1 νs fac rate hv := by
  intro A hA Y _ ρo ψ ψ' h gx
  rw [hB]
  show oldBAtAt (glob := true) (σ := stencilX) g hnn hM1 F A.H hk hk1 hρ (rotM ρo ψ) z
      (reExt (rotC ρo h)) a₁ ν β p₁ δ (inner A) (cb A) hp
      ((IF A).at (rotM ρo ψ, rotM ρo ψ', rotC ρo h, rotG ρo gx)) (ψout A (rotM ρo ψ) (rotC ρo h)) rψ
      ρc ρ r r' rep A (oldDoms F A.H k) (rotM ρo ψ') (reExtE (rotC ρo h)) (rotG ρo gx) Y =
    oldBAtAt (glob := true) (σ := stencilX) g hnn hM1 F A.H hk hk1 hρ ψ z (reExt h) a₁ ν β p₁ δ
      (inner A) (cb A) hp ((IF A).at (ψ, ψ', h, gx)) (ψout A ψ h) rψ ρc ρ r r' rep A (oldDoms F A.H k)
      ψ' (reExtE h) gx Y
  rw [reExt_rotC, reExtE_rotC, hout]
  exact oldBAtAt_rot g hnn hM1 true F A.H stencilX hk hk1 hρ ψ z (reExt h) a₁ ν β p₁ δ ρo (inner A)
    (cb A) hp (IF A) (ψ, ψ', h, gx) (rotM ρo ψ, rotM ρo ψ', rotC ρo h, rotG ρo gx) (ψout A ψ h) rψ ρc
    ρ r r' rep A (oldDoms F A.H k) ψ' (reExtE h) gx Y (fun u y Φ => hIF A ρo (ψ, ψ', h, gx) u y Φ)
    (fun X hX J hJ ψhat hball => by
      obtain ⟨Rp, κ, δs, hyp⟩ := hcoef A hA ρo ψ ψ' h gx X hX J hJ ψhat hball
      exact oldCoefLoc2_rot g hnn hM1 ρo A.H hk hk1 hρ ψ z (reExt h) a₁ ν β p₁ δ ρc ρ r r' rep A X ψ'
        (reExtE h) gx J ψhat hyp)

end StepRot

end Balaban.RootFSpine
