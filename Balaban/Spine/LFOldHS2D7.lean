/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.LFOldHS2Chain
public import Balaban.Spine.LFOldD7EuclidLoc
public import Balaban.Spine.LFOldD7AnalyticLoc

/-!
# The (D7) clauses of the coefficient of reading HS-2

The clauses `rot`, `real`, `loc_field`, `loc_hist`, `analytic` and `euclid` of (D7) at the level of
one coefficient (W1158, `Spine/LFOldD7*Loc.lean`) are cores over the readings of the local pair;
their instances for reading HS-2 (the restricted global datum `holeStepLoc2`, the local sets
`V₂(X, J)`):

* `stencilX_map_ec`: the stencil commutes with the isometries of the cube torus (the input `hσX` of
  `oldCoefLocAt_euclid`);
* `stepReadsIn_outLabel2` (`hsiteY` at the fine set of the output label);
* `holeStepLoc2_congr_hist_Z` (`loc_hist`: the local step reads `Ω_{k+1}` also at the data sites of
  the local pair);
* `oldCoefLoc2_rot`, `oldCoefLoc2_im`, `oldCoefLoc2_congr_fields`, `oldCoefLoc2_analytic_family`,
  `oldCoefLoc2_analytic_family_LF`, `oldCoefLoc2_euclid`.
-/

@[expose] public section

open MeasureTheory Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField
  Balaban.Localization Balaban.Localization.DecEquiv Matrix Balaban.LargeField
  Balaban.Fluctuation Balaban.LargeField.Def7 Balaban.LargeField.RegionHistory

namespace Balaban.RootFSpine

set_option linter.unusedSectionVars false

section Stencil

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)]

/-- **The stencil commutes with the isometries of the cube torus**: for a permutation `e` of the cubes
of `𝕋_k` preserving the index distance, `(e X)^{∼3} = e (X^{∼3})`. -/
theorem stencilX_map_ec {k : ℕ} (e : Equiv.Perm (Torus S.d (n k)))
    (he : ∀ x y, supDist (e x) (e y) = supDist x y) (X : Finset (Torus S.d (n k))) :
    stencilX (X.map e.toEmbedding) = (stencilX X).map e.toEmbedding := by
  ext u
  obtain ⟨u', rfl⟩ := e.surjective u
  have hmap : e u' ∈ (stencilX X).map e.toEmbedding ↔ u' ∈ stencilX X := by
    constructor
    · intro h
      obtain ⟨w, hw, hwu⟩ := Finset.mem_map.1 h
      rwa [show w = u' from e.injective hwu] at hw
    · intro h
      exact Finset.mem_map_of_mem _ h
  rw [hmap, mem_stencilX, mem_stencilX]
  constructor
  · rintro hu
    obtain ⟨v, hv, huv⟩ := mem_nbhd.1 hu
    obtain ⟨w, hw, rfl⟩ := Finset.mem_map.1 (Finset.mem_coe.1 hv)
    exact mem_nbhd.2 ⟨w, hw, by rw [← he]; exact huv⟩
  · rintro hu
    obtain ⟨w, hw, huw⟩ := mem_nbhd.1 hu
    exact mem_nbhd.2 ⟨e w, Finset.mem_coe.2 (Finset.mem_map_of_mem _ hw), by
      show supDist (e u') (e w) ≤ 3
      rw [he]; exact huw⟩

end Stencil

section Basic

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {N m₁ : ℕ}
  (g : Geo S n R M) (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) (hM1 : g.M1 = S.L ^ m₁)

/-- **`hsiteY` of `oldCoefLoc2_congr_fields` at the fine set of the output label** (reading HS-2;
`stepReadsIn_outLabelAt`). -/
theorem stepReadsIn_outLabel2 {m₀ : ℕ} (F : FineSizeFrame S n M K m₀ m₁)
    (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K) (hk1 : 1 ≤ k)
    (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (ψ : MultiFieldC S n M K N) (z : ℝ) (h₀ : Fin N → ℝ)
    (a₁ ν β p₁ δ : ℝ) (r r' : ℕ) (X : Finset (Torus S.d (n k)))
    (J : Finset (ℕ × CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)))
    (hJ : GoodJAt g hnn hM1 F H hk hρ r r' (d7Pull F (k + 1) (OmegaCube H (k + 1))) (stencilX X) X J)
    (T : Finset (CubeB (d := S.d) (L := S.L) (N₁ := F.N₁) (m₁ := m₁) (K := K) m₀ (k + 1)
      (d7Pull F (k + 1) (OmegaCube H (k + 1)))))
    (hT : blocksOf m₀ (k + 1) (d7Pull F (k + 1) (OmegaCube H (k + 1)))
      (markSiteAt g hnn hM1 F H hk hρ r r' (stencilX X) X J) ⊆ T)
    (hfin : dOmega m₀ (k + 1) (d7Pull F (k + 1) (OmegaCube H (k + 1))) (sitesOf T) ≠ ⊤) :
    StepReadsIn g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ (locSetXJ2 g hM1 H r r' X J)
      (fineSet (S := S) (n := n) M K (k + 1)
        (outLabel F k (OmegaCube H (k + 1)) T : Set (Torus S.d (n (k + 1))))) :=
  stepReadsIn_outLabelAt (σ := stencilX) g hnn hM1 F H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ r r' X J hJ T
    hT hfin

/-- **The local steps of reading HS-2 of two histories agree when `Z_k` agrees near `V`** and `Ω_{k+1}`
agrees on the cubes of the top layer of `𝔹_{k+1}(V)` and of the data sites of the local pair (the
datum reads `Ω_{k+1}` there; `holeStepLocAt_congr_hist_Z`). -/
theorem holeStepLoc2_congr_hist_Z (H H' : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K)
    (hk1 : 1 ≤ k) (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (ψ : MultiFieldC S n M K N) (z : ℝ)
    (h₀ : Fin N → ℝ) (a₁ ν β p₁ δ : ℝ) (V : Set (CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)))
    (hL : 2 ≤ S.L)
    (hZag : ∀ j, j ≤ k → ∀ x ∈ (locB g hM1 V).Ω j,
      ∀ y : Torus S.d (g.M1 * (g.c * n (k + 1)) * S.L ^ (k + 1)),
      supDist ((congrArg (· * S.L ^ (k + 1)) (p6_side (c := g.c) (n1 := n (k + 1)) hM1)).symm ▸ x :
        Torus S.d (g.M1 * (g.c * n (k + 1)) * S.L ^ (k + 1))) y ≤ 12 * g.M1 * S.L ^ k →
      ∀ w : Torus S.d (n k), supDist (blockMap (S.L ^ k * (g.c * g.M1)) (n k) y) w ≤
        2 * (⌊R (k - 1)⌋₊ + 1) → (w ∈ (H.step k).Z ↔ w ∈ (H'.step k).Z))
    (hOm : ∀ x ∈ (locB g hM1 V).Ω (k + 1),
      (cubeOfC hM1 x ∈ (H.step k).Omega ↔ cubeOfC hM1 x ∈ (H'.step k).Omega))
    (hOmD : ∀ x ∈ dataSites
        ((holeStepLF g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).G'.inter (locB g hM1 V)),
      (cubeOfC hM1 x ∈ (H.step k).Omega ↔ cubeOfC hM1 x ∈ (H'.step k).Omega)) :
    holeStepLoc2 g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V =
      holeStepLoc2 g hnn hM1 H' hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V :=
  holeStepLocAt_congr_hist_Z g hnn hM1 true H H' hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V hL hZag hOm
    (fun _ => hOmD)

variable {k : ℕ}

/-- **The coefficient `T(X, J)` on the local pair of reading HS-2 is `O(N)`-covariant** (the clause
`rot` of (D7) at the level of one coefficient; `oldCoefLocAt_rot`). -/
theorem oldCoefLoc2_rot (ρo : OrthN N) (H : RegionHistory S n R k0 K) (hk : k + 1 ≤ K) (hk1 : 1 ≤ k)
    (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (ψ : MultiFieldC S n M K N) (z : ℝ) (h₀ : Fin N → ℝ)
    (a₁ ν β p₁ δ : ℝ) (ρc : ℝ) (ρ r r' : ℕ) {geo : Geo S n R M} {cs : OpConsts}
    {P : BudgetConsts} (rep : Rep S n R k0 K M N geo cs P k) (A : LabHist S n R k0 K)
    (X : Finset (Torus S.d (n k))) (ψ' : MultiFieldC S n M K N) (hv : EuclideanSpace ℝ (Fin N))
    (gx : GIdx S n M K N → ℂ) (J : Finset (ℕ × CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)))
    (ψhat : (holeStepLF g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).U → Fin N → ℂ) {Rp κ δs : ℝ}
    (hyp : OldCoefRotHyp g hnn hM1 H hk
      (holeStepLoc2 g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ (locSetXJ2 g hM1 H r r' X J)) ρo
      (rotH0 ρo h₀) (rotCMat_h0 ρo h₀) ρc ρ r rep A X ψ ψ' hv gx
      (restrictU _ _ _ _ _ _ _ ψhat) Rp κ δs) :
    oldCoefLoc2 g hnn hM1 H hk hk1 hρ (rotM ρo ψ) z (rotH0 ρo h₀) a₁ ν β p₁ δ ρc ρ r r' rep A X
        (rotM ρo ψ') (ρo hv) (rotG ρo gx) J (rotSite (rotCMat ρo) ψhat) =
      oldCoefLoc2 g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ ρc ρ r r' rep A X ψ' hv gx J ψhat :=
  oldCoefLocAt_rot (glob := true) (σ := stencilX) g hnn hM1 ρo H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ ρc ρ
    r r' rep A X ψ' hv gx J ψhat hyp

/-- **The coefficient `T(X, J)` on the local pair of reading HS-2 is real** (the clause `real` of
(D7) at the level of one coefficient; `oldCoefLocAt_im`). -/
theorem oldCoefLoc2_im (H : RegionHistory S n R k0 K) (hk : k + 1 ≤ K) (hk1 : 1 ≤ k)
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
      ((holeStepLoc2 g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ (locSetXJ2 g hM1 H r r' X J)).oldInterp
        (coverOf (holeStepLoc2 g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ
          (locSetXJ2 g hM1 H r r' X J)).G') ρc
        (locDomsLF g hM1 (holeStepLoc2 g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ
          (locSetXJ2 g hM1 H r r' X J)) ρ)
        (collarCoreC (c := g.c) (H.step k) hM1 r X) ∅
        (restrictU _ _ _ _ _ _ _ ψhat)
        (oldTermLF g hnn hM1 rep A X hk (holeStepLoc2 g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ
          (locSetXJ2 g hM1 H r r' X J)).G' ψ ψ' hv gx)
        (fun b => absurd b.2 (Finset.notMem_empty _)))
      (Analysis.polydisc
        (0 : Dec2.DecParams (coverOf (holeStepLoc2 g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ
          (locSetXJ2 g hM1 H r r' X J)).G')) fun _ => Rp)) :
    (oldCoefLoc2 g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ ρc ρ r r' rep A X ψ' hv gx J ψhat).im
      = 0 :=
  oldCoefLocAt_im (glob := true) (σ := stencilX) g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ ρc ρ r r'
    rep A X ψ' hv gx J ψhat hreal hψ hψ' hgx hψhat hRp hana

/-- **The clause `loc_field` of (D7) for the coefficient of reading HS-2**
(`oldCoefLocAt_congr_fields`; for `Y` the fine set of an output label, `hsiteY` is
`stepReadsIn_outLabel2`). -/
theorem oldCoefLoc2_congr_fields (H : RegionHistory S n R k0 K) (hk : k + 1 ≤ K) (hk1 : 1 ≤ k)
    (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (z : ℝ) (h₀ : Fin N → ℝ)
    (a₁ ν β p₁ δ : ℝ) (ρc : ℝ) (ρ r r' : ℕ) {geo : Geo S n R M} {cs : OpConsts}
    {P : BudgetConsts} (rep : Rep S n R k0 K M N geo cs P k) (A : LabHist S n R k0 K)
    (X : Finset (Torus S.d (n k))) (hv : EuclideanSpace ℝ (Fin N))
    (J : Finset (ℕ × CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)))
    (hloc : ∀ (ψ₁ ψ₂ ψ'₁ ψ'₂ : MultiFieldC S n M K N) (h : Fin N → ℂ)
      (g₁ g₂ : GIdx S n M K N → ℂ),
      (∀ j, j ≤ K → ∀ y : BlockAt S n M K j,
        BlockSub (S := S) (n := n) (M := M) (K := K) j y
          (fineSet (S := S) (n := n) M K k (X : Set (Torus S.d (n k)))) →
          ψ₁ j y = ψ₂ j y ∧ ψ'₁ j y = ψ'₂ j y) →
      (∀ x i, x ∈ fineSet (S := S) (n := n) M K k (X : Set (Torus S.d (n k))) →
        g₁ (x, i) = g₂ (x, i)) →
      rep.B A X ψ₁ ψ'₁ h g₁ = rep.B A X ψ₂ ψ'₂ h g₂)
    (Y : Set (Torus S.d (M * n K * S.L ^ K)))
    (hXY : fineSet (S := S) (n := n) M K k (X : Set (Torus S.d (n k))) ⊆ Y)
    (ψ₁ ψ₂ ψ'₁ ψ'₂ : MultiFieldC S n M K N) (gx₁ gx₂ : GIdx S n M K N → ℂ)
    (hsiteY : StepReadsIn g hnn hM1 H hk hk1 hρ ψ₁ z h₀ a₁ ν β p₁ δ
      (locSetXJ2 g hM1 H r r' X J) Y)
    (hψ : ∀ j, j ≤ K → ∀ y : BlockAt S n M K j, BlockSub (S := S) (n := n) (M := M) (K := K) j y Y →
      ψ₁ j y = ψ₂ j y)
    (hψ' : ∀ j, j ≤ K → ∀ y : BlockAt S n M K j,
      BlockSub (S := S) (n := n) (M := M) (K := K) j y Y → ψ'₁ j y = ψ'₂ j y)
    (hgx : ∀ x i, x ∈ Y → gx₁ (x, i) = gx₂ (x, i))
    (ψhat : (holeStepLF g hnn hM1 H hk hk1 hρ ψ₁ z h₀ a₁ ν β p₁ δ).U → Fin N → ℂ) :
    oldCoefLoc2 g hnn hM1 H hk hk1 hρ ψ₁ z h₀ a₁ ν β p₁ δ ρc ρ r r' rep A X ψ'₁ hv gx₁ J ψhat =
      oldCoefLoc2 g hnn hM1 H hk hk1 hρ ψ₂ z h₀ a₁ ν β p₁ δ ρc ρ r r' rep A X ψ'₂ hv gx₂ J ψhat :=
  oldCoefLocAt_congr_fields (glob := true) (σ := stencilX) g hnn hM1 H hk hk1 hρ z h₀ a₁ ν β p₁ δ
    ρc ρ r r' rep A X hv J hloc Y hXY ψ₁ ψ₂ ψ'₁ ψ'₂ gx₁ gx₂ hsiteY hψ hψ' hgx ψhat

end Basic

section Fam2

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {N m₁ : ℕ}
  (g : Geo S n R M) (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) (hM1 : g.M1 = S.L ^ m₁)
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {ψE : E → MultiFieldC S n M K N}

/-- **The coefficient on the local pair of reading HS-2 is analytic in the fields** (the clause
`analytic` of (D7) at the level of one coefficient; `oldCoefLocAt_analytic_family`). -/
theorem oldCoefLoc2_analytic_family (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K)
    (hk1 : 1 ≤ k) (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (ψ₀ : MultiFieldC S n M K N) (z : ℝ)
    (h₀ : Fin N → ℝ) (a₁ ν β p₁ δ : ℝ) (ρ r r' : ℕ) {geo : Geo S n R M}
    {cs : OpConsts} {P : BudgetConsts} (rep : Rep S n R k0 K M N geo cs P k)
    (A : LabHist S n R k0 K) (X : Finset (Torus S.d (n k))) (hv : EuclideanSpace ℝ (Fin N))
    (J : Finset (ℕ × CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)))
    (ψout : (locStepXJAt (glob := true) (σ := stencilX) g hnn hM1 H hk hk1 hρ ψ₀ z h₀ a₁ ν β p₁ δ r r' X J).U → Fin N → ℂ)
    {Kc Cx Cx₂ c BG δ' δc : ℝ} {κ κ₁ : ℝ}
    (hS : Dec2.DecSpecs S.d S.L Kc Cx c BG)
    (Sb : Dec2.CoverBase (coverOf (locStepXJAt (glob := true) (σ := stencilX) g hnn hM1 H hk hk1 hρ ψ₀ z h₀ a₁ ν β p₁ δ r r' X J).G')
      (locStepXJAt (glob := true) (σ := stencilX) g hnn hM1 H hk hk1 hρ ψ₀ z h₀ a₁ ν β p₁ δ r r' X J).G' (compWeight S.L a₁) ν Kc Cx)
    (SX : Dec2.XCover (coverOf (locStepXJAt (glob := true) (σ := stencilX) g hnn hM1 H hk hk1 hρ ψ₀ z h₀ a₁ ν β p₁ δ r r' X J).G')
      (locStepXJAt (glob := true) (σ := stencilX) g hnn hM1 H hk hk1 hρ ψ₀ z h₀ a₁ ν β p₁ δ r r' X J).G' (compWeight S.L a₁) a₁ ν Cx₂)
    (hCx₂ : 0 ≤ Cx₂)
    (HB : BgHyp S.d S.L (k + 1) (minSep S.L g.M1) (compWeight S.L a₁) ν) (hκ : 0 < κ)
    (hM : c * Real.exp (N0 S.d S.L * κ) ≤ (S.L : ℝ) ^ m₁)
    (hMX : Dec2.cstarX S.d S.L Cx₂ * Real.exp (N0 S.d S.L * κ) ≤ (S.L : ℝ) ^ m₁)
    (hδ0 : 0 < δ') (hε : δ' ≤ bgC0 S.d S.L N) (hδ : δ' ≤ c7 S.d S.L N BG κ)
    (hνε : ν * ((S.L : ℝ) ^ (k + 1)) ^ 2 * δ' ^ 2 ≤ δ' ^ 2)
    (hphi : 3 * δ' + K4 S.d S.L N BG κ * δ' < 1 / 2)
    (hmarD : K4 S.d S.L N BG κ * δ' + 2 * δ' + K4 S.d S.L N BG κ * δ' *
      (K4 S.d S.L N BG κ * δ' + 2 * (1 + 3 * δ')) < δc)
    (hαD : K4 S.d S.L N BG κ * δ' < coerciveConst S.d / 2)
    (hsm : δc ^ 2 * smallConstX S.d S.L κ ≤ 1 / 4) (hκ₁0 : 0 < κ₁) (hκ₁ : κ₁ ≤ κ)
    {Pset : Set E} (hP : IsOpen Pset)
    (hψ : ∀ j y i, AnalyticOnNhd ℂ (fun e => ψE e j y i) Pset)
    (ψ'E : E → MultiFieldC S n M K N) (gxE : E → GIdx S n M K N → ℂ)
    (hD : ∀ e ∈ Pset, InDomainC (locStepXJAt (glob := true) (σ := stencilX) g hnn hM1 H hk hk1 hρ ψ₀ z h₀ a₁ ν β p₁ δ r r' X J).G'
      ν δ' δ' (locStepXJAt (glob := true) (σ := stencilX) g hnn hM1 H hk hk1 hρ (ψE e) z h₀ a₁ ν β p₁ δ r r' X J).D')
    (hB : ∀ e ∈ Pset, ∀ s ∈ Analysis.polydisc
      (0 : Dec2.DecParams (coverOf (locStepXJAt (glob := true) (σ := stencilX) g hnn hM1 H hk hk1 hρ ψ₀ z h₀ a₁ ν β p₁ δ r r' X J).G'))
      (fun _ => Real.exp κ₁),
      AnalyticAt ℂ (fun q : E × ((locStepXJAt (glob := true) (σ := stencilX) g hnn hM1 H hk hk1 hρ ψ₀ z h₀ a₁ ν β p₁ δ r r' X J).U →
          Fin N → ℂ) =>
        oldTermLF g hnn hM1 rep A X hk
          (locStepXJAt (glob := true) (σ := stencilX) g hnn hM1 H hk hk1 hρ ψ₀ z h₀ a₁ ν β p₁ δ r r' X J).G'
          (ψE q.1) (ψ'E q.1) hv (gxE q.1) q.2)
        (e, ((locStepXJAt (glob := true) (σ := stencilX) g hnn hM1 H hk hk1 hρ ψ₀ z h₀ a₁ ν β p₁ δ r r' X J).withD
            (locStepXJAt (glob := true) (σ := stencilX) g hnn hM1 H hk hk1 hρ (ψE e) z h₀ a₁ ν β p₁ δ r r' X J).D'
            (locStepXJAt (glob := true) (σ := stencilX) g hnn hM1 H hk hk1 hρ (ψE e) z h₀ a₁ ν β p₁ δ r r' X J).hh₀).composed
          (coverOf (locStepXJAt (glob := true) (σ := stencilX) g hnn hM1 H hk hk1 hρ ψ₀ z h₀ a₁ ν β p₁ δ r r' X J).G')
          (rho4 S.d S.L N BG κ)
          ((locStepXJAt (glob := true) (σ := stencilX) g hnn hM1 H hk hk1 hρ ψ₀ z h₀ a₁ ν β p₁ δ r r' X J).slocOf
            (coverOf (locStepXJAt (glob := true) (σ := stencilX) g hnn hM1 H hk hk1 hρ ψ₀ z h₀ a₁ ν β p₁ δ r r' X J).G')
            (locDomsLF g hM1 (locStepXJAt (glob := true) (σ := stencilX) g hnn hM1 H hk hk1 hρ ψ₀ z h₀ a₁ ν β p₁ δ r r' X J) ρ)
            (HoleStep.coreExt (coverOf (locStepXJAt (glob := true) (σ := stencilX) g hnn hM1 H hk hk1 hρ ψ₀ z h₀ a₁ ν β p₁ δ r r' X J).G')
              (collarCoreC (c := g.c) (H.step k) hM1 r X) s))
          ((locStepXJAt (glob := true) (σ := stencilX) g hnn hM1 H hk hk1 hρ ψ₀ z h₀ a₁ ν β p₁ δ r r' X J).fill ∅
            (fun b => absurd b.2 (Finset.notMem_empty _)) ψout))) :
    AnalyticOnNhd ℂ (fun e =>
      ((locStepXJAt (glob := true) (σ := stencilX) g hnn hM1 H hk hk1 hρ ψ₀ z h₀ a₁ ν β p₁ δ r r' X J).withD
        (locStepXJAt (glob := true) (σ := stencilX) g hnn hM1 H hk hk1 hρ (ψE e) z h₀ a₁ ν β p₁ δ r r' X J).D'
        (locStepXJAt (glob := true) (σ := stencilX) g hnn hM1 H hk hk1 hρ (ψE e) z h₀ a₁ ν β p₁ δ r r' X J).hh₀).oldCoef
        (coverOf (locStepXJAt (glob := true) (σ := stencilX) g hnn hM1 H hk hk1 hρ ψ₀ z h₀ a₁ ν β p₁ δ r r' X J).G') (rho4 S.d S.L N BG κ)
        (locDomsLF g hM1 (locStepXJAt (glob := true) (σ := stencilX) g hnn hM1 H hk hk1 hρ ψ₀ z h₀ a₁ ν β p₁ δ r r' X J) ρ)
        (collarCoreC (c := g.c) (H.step k) hM1 r X) ∅ ψout
        (oldTermLF g hnn hM1 rep A X hk
          (locStepXJAt (glob := true) (σ := stencilX) g hnn hM1 H hk hk1 hρ ψ₀ z h₀ a₁ ν β p₁ δ r r' X J).G' (ψE e) (ψ'E e) hv
          (gxE e))
        (locCubes g (coverOf (locStepXJAt (glob := true) (σ := stencilX) g hnn hM1 H hk hk1 hρ ψ₀ z h₀ a₁ ν β p₁ δ r r' X J).G') J)
        (fun b => absurd b.2 (Finset.notMem_empty _))) Pset :=
  oldCoefLocAt_analytic_family (glob := true) (σ := stencilX) g hnn hM1 H hk hk1 hρ ψ₀ z h₀ a₁ ν β
    p₁ δ ρ r r' rep A X hv J ψout hS Sb SX hCx₂ HB hκ hM hMX hδ0 hε hδ hνε hphi hmarD hαD hsm hκ₁0
    hκ₁ hP hψ ψ'E gxE hD hB

/-- **The coefficient of reading HS-2, as `oldCoefLF` of the local step of each field, is analytic**
(`oldCoefLocAt_analytic_family_LF`). -/
theorem oldCoefLoc2_analytic_family_LF (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K)
    (hk1 : 1 ≤ k) (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (ψ₀ : MultiFieldC S n M K N) (z : ℝ)
    (h₀ : Fin N → ℝ) (a₁ ν β p₁ δ : ℝ) (ρ r r' : ℕ) {geo : Geo S n R M}
    {cs : OpConsts} {P : BudgetConsts} (rep : Rep S n R k0 K M N geo cs P k)
    (A : LabHist S n R k0 K) (X : Finset (Torus S.d (n k))) (hv : EuclideanSpace ℝ (Fin N))
    (J : Finset (ℕ × CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)))
    (ψout : (locStepXJAt (glob := true) (σ := stencilX) g hnn hM1 H hk hk1 hρ ψ₀ z h₀ a₁ ν β p₁ δ r r' X J).U → Fin N → ℂ)
    {ρc₀ : ℝ} {Pset : Set E} (hP : IsOpen Pset) (ψ'E : E → MultiFieldC S n M K N)
    (gxE : E → GIdx S n M K N → ℂ)
    (key : AnalyticOnNhd ℂ (fun e =>
      ((locStepXJAt (glob := true) (σ := stencilX) g hnn hM1 H hk hk1 hρ ψ₀ z h₀ a₁ ν β p₁ δ r r' X J).withD
        (locStepXJAt (glob := true) (σ := stencilX) g hnn hM1 H hk hk1 hρ (ψE e) z h₀ a₁ ν β p₁ δ r r' X J).D'
        (locStepXJAt (glob := true) (σ := stencilX) g hnn hM1 H hk hk1 hρ (ψE e) z h₀ a₁ ν β p₁ δ r r' X J).hh₀).oldCoef
        (coverOf (locStepXJAt (glob := true) (σ := stencilX) g hnn hM1 H hk hk1 hρ ψ₀ z h₀ a₁ ν β p₁ δ r r' X J).G') ρc₀
        (locDomsLF g hM1 (locStepXJAt (glob := true) (σ := stencilX) g hnn hM1 H hk hk1 hρ ψ₀ z h₀ a₁ ν β p₁ δ r r' X J) ρ)
        (collarCoreC (c := g.c) (H.step k) hM1 r X) ∅ ψout
        (oldTermLF g hnn hM1 rep A X hk
          (locStepXJAt (glob := true) (σ := stencilX) g hnn hM1 H hk hk1 hρ ψ₀ z h₀ a₁ ν β p₁ δ r r' X J).G' (ψE e) (ψ'E e) hv
          (gxE e))
        (locCubes g (coverOf (locStepXJAt (glob := true) (σ := stencilX) g hnn hM1 H hk hk1 hρ ψ₀ z h₀ a₁ ν β p₁ δ r r' X J).G') J)
        (fun b => absurd b.2 (Finset.notMem_empty _))) Pset) :
    AnalyticOnNhd ℂ (fun e => oldCoefLF g hnn hM1
      (locStepXJAt (glob := true) (σ := stencilX) g hnn hM1 H hk hk1 hρ (ψE e) z h₀ a₁ ν β p₁ δ r r' X J) H hk
      (coverOf (locStepXJAt (glob := true) (σ := stencilX) g hnn hM1 H hk hk1 hρ (ψE e) z h₀ a₁ ν β p₁ δ r r' X J).G') ρc₀ ρ r ∅
      ψout rep A X (ψE e) (ψ'E e) hv (gxE e)
      (locCubes g (coverOf (locStepXJAt (glob := true) (σ := stencilX) g hnn hM1 H hk hk1 hρ (ψE e) z h₀ a₁ ν β p₁ δ r r' X J).G') J)
      (fun b => absurd b.2 (Finset.notMem_empty _))) Pset :=
  oldCoefLocAt_analytic_family_LF (glob := true) (σ := stencilX) g hnn hM1 H hk hk1 hρ ψ₀ z h₀ a₁ ν
    β p₁ δ ρ r r' rep A X hv J ψout hP ψ'E gxE key

end Fam2

section Euclid

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {N m₁ : ℕ}
  (g : Geo S n R M) (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) (hM1 : g.M1 = S.L ^ m₁)
variable (H H' : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K) (hk1 : 1 ≤ k)
  (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (ψ : MultiFieldC S n M K N) (z : ℝ) (h₀ : Fin N → ℝ)
  (a₁ ν β p₁ δ : ℝ)

/-- **The clause `euclid` of (D7) for the coefficient of reading HS-2** (`oldCoefLocAt_euclid`; the
stencil commutes with the lattice symmetry, `stencilX_map_ec`). -/
theorem oldCoefLoc2_euclid (σ : LatTorusSym S n M K) (hI : RegionIso σ H H') (hm₁ : 2 ≤ m₁)
    {geo : Geo S n R M} {cs : OpConsts} {P : BudgetConsts}
    (rep : Rep S n R k0 K M N geo cs P k) (A A' : LabHist S n R k0 K)
    (X : Finset (Torus S.d (n k))) (ρc : ℝ) (ρ r r' : ℕ)
    (ψ' : MultiFieldC S n M K N) (hv : EuclideanSpace ℝ (Fin N)) (gx : GIdx S n M K N → ℂ)
    (J : Finset (ℕ × CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)))
    (hJc : ∀ P ∈ J, P ∈ cubeIdx (holeStepLoc2 g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ
      (locSetXJ2 g hM1 H r r' X J)).G')
    (heuc : ∀ (ψ₂ ψ₃ : MultiFieldC S n M K N) (h : Fin N → ℂ) (g₂ : GIdx S n M K N → ℂ),
      rep.B A' (X.map (σ.ec k).toEmbedding) (symM σ ψ₂) (symM σ ψ₃) h (symG σ g₂) =
        rep.B A X ψ₂ ψ₃ h g₂)
    (ψhat : (holeStepLF g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).U → Fin N → ℂ)
    (ψhat' : (holeStepLF g hnn hM1 H' hk hk1 hρ (symM σ ψ) z h₀ a₁ ν β p₁ δ).U → Fin N → ℂ)
    (hψhat : ∀ (b : (holeStepLF g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).U)
      (b' : (holeStepLF g hnn hM1 H' hk hk1 hρ (symM σ ψ) z h₀ a₁ ν β p₁ δ).U),
      (b' : UnitTorus S.d S.L (g.c * n (k + 1)) m₁ k) =
        ((coverAff g hnn hM1 σ hk).coarse (S.L ^ k)
          ((g.c * n (k + 1)) * S.L ^ m₁ * S.L ^ (k + 1 - k))).toFun
          (b : UnitTorus S.d S.L (g.c * n (k + 1)) m₁ k) → ∀ i, ψhat' b' i = ψhat b i)
    {R₀ : ℝ} (hR : 1 < R₀)
    (hana : AnalyticOnNhd ℂ ((holeStepLoc2 g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ
        (locSetXJ2 g hM1 H r r' X J)).oldInterp
      (coverOf (holeStepLoc2 g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ
        (locSetXJ2 g hM1 H r r' X J)).G') ρc
      (locDomsLF g hM1 (holeStepLoc2 g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ
        (locSetXJ2 g hM1 H r r' X J)) ρ)
      (collarCoreC (c := g.c) (H.step k) hM1 r X) ∅
      (restrictU _ _ _ _ _ _ _ ψhat)
      (oldTermLF g hnn hM1 rep A X hk
        (holeStepLoc2 g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ (locSetXJ2 g hM1 H r r' X J)).G'
        ψ ψ' hv gx)
      (fun b => absurd b.2 (Finset.notMem_empty _)))
      (Analysis.polydisc (0 : Dec2.DecParams (coverOf (holeStepLoc2 g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ
        (locSetXJ2 g hM1 H r r' X J)).G')) fun _ => R₀))
    (hana' : AnalyticOnNhd ℂ ((holeStepLoc2 g hnn hM1 H' hk hk1 hρ (symM σ ψ) z h₀ a₁ ν β p₁ δ
        (locSetXJ2 g hM1 H' r r' (X.map (σ.ec k).toEmbedding)
          (J.map (affCentres (m₁ := m₁) (coverAff g hnn hM1 σ hk) m₁).toEmbedding))).oldInterp
      (coverOf (holeStepLoc2 g hnn hM1 H' hk hk1 hρ (symM σ ψ) z h₀ a₁ ν β p₁ δ
        (locSetXJ2 g hM1 H' r r' (X.map (σ.ec k).toEmbedding)
          (J.map (affCentres (m₁ := m₁) (coverAff g hnn hM1 σ hk) m₁).toEmbedding))).G') ρc
      (locDomsLF g hM1 (holeStepLoc2 g hnn hM1 H' hk hk1 hρ (symM σ ψ) z h₀ a₁ ν β p₁ δ
        (locSetXJ2 g hM1 H' r r' (X.map (σ.ec k).toEmbedding)
          (J.map (affCentres (m₁ := m₁) (coverAff g hnn hM1 σ hk) m₁).toEmbedding))) ρ)
      (collarCoreC (c := g.c) (H'.step k) hM1 r (X.map (σ.ec k).toEmbedding)) ∅
      (restrictU _ _ _ _ _ _ _ ψhat')
      (oldTermLF g hnn hM1 rep A' (X.map (σ.ec k).toEmbedding) hk
        (holeStepLoc2 g hnn hM1 H' hk hk1 hρ (symM σ ψ) z h₀ a₁ ν β p₁ δ
          (locSetXJ2 g hM1 H' r r' (X.map (σ.ec k).toEmbedding)
            (J.map (affCentres (m₁ := m₁) (coverAff g hnn hM1 σ hk) m₁).toEmbedding))).G'
        (symM σ ψ) (symM σ ψ') hv (symG σ gx))
      (fun b => absurd b.2 (Finset.notMem_empty _)))
      (Analysis.polydisc (0 : Dec2.DecParams (coverOf (holeStepLoc2 g hnn hM1 H' hk hk1 hρ (symM σ ψ) z h₀ a₁ ν β p₁ δ
        (locSetXJ2 g hM1 H' r r' (X.map (σ.ec k).toEmbedding)
          (J.map (affCentres (m₁ := m₁) (coverAff g hnn hM1 σ hk) m₁).toEmbedding))).G')) fun _ => R₀)) :
    oldCoefLoc2 g hnn hM1 H' hk hk1 hρ (symM σ ψ) z h₀ a₁ ν β p₁ δ ρc ρ r r' rep A'
        (X.map (σ.ec k).toEmbedding) (symM σ ψ') hv (symG σ gx)
        (J.map (affCentres (m₁ := m₁) (coverAff g hnn hM1 σ hk) m₁).toEmbedding) ψhat' =
      oldCoefLoc2 g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ ρc ρ r r' rep A X ψ' hv gx J ψhat :=
  oldCoefLocAt_euclid (glob := true) (σX := stencilX) g hnn hM1 H H' hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ σ
    hI hm₁ rep A A' X ρc ρ r r' ψ' hv gx J hJc heuc ψhat ψhat' hψhat hR hana hana' (hσX :=
    stencilX_map_ec (σ.ec k) (σ.dist k) X)

end Euclid

end Balaban.RootFSpine
