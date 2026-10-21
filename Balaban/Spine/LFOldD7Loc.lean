/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.LFOldD7RealLoc
public import Balaban.Spine.LFOldLocCoef

@[expose] public section

open MeasureTheory Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField
  Balaban.Localization Matrix Balaban.LargeField

namespace Balaban.RootFSpine

open Balaban.Fluctuation Balaban.LargeField.Def7 Balaban.LargeField.RegionHistory

section Loc

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {N m₁ : ℕ}
  (g : Geo S n R M) (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) (hM1 : g.M1 = S.L ^ m₁)

omit [NeZero M] in
/-- Any datum `glob`. -/
theorem holeStepLocAt_congr_D' (glob : Bool) (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K)
    (hk1 : 1 ≤ k) (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (ψ₁ ψ₂ : MultiFieldC S n M K N) (z : ℝ)
    (h₀ : Fin N → ℝ) (a₁ ν β p₁ δ : ℝ) (V : Set (CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)))
    (h : (holeStepLocAt g hnn hM1 glob H hk hk1 hρ ψ₁ z h₀ a₁ ν β p₁ δ V).D' =
      (holeStepLocAt g hnn hM1 glob H hk hk1 hρ ψ₂ z h₀ a₁ ν β p₁ δ V).D') :
    holeStepLocAt g hnn hM1 glob H hk hk1 hρ ψ₁ z h₀ a₁ ν β p₁ δ V =
      holeStepLocAt g hnn hM1 glob H hk hk1 hρ ψ₂ z h₀ a₁ ν β p₁ δ V := by
  unfold holeStepLocAt at h ⊢
  unfold HoleStep.restrict at h ⊢
  dsimp only at h ⊢
  congr 1
theorem liftMixed_congr_data {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}
    (G : GeneratingSet d L N₀ (k + 1) ϱ)
    {Ω : Finset (Torus d (N₀ * L ^ (k + 1)))} (hΩ : IsBlockUnion L N₀ (k + 1) (k + 1) Ω)
    (hG : G.Ω (k + 1) ⊆ Ω) (ψ₁ ψ₂ : Torus d (N₀ * L ^ (k + 1 - k)) → Fin N → ℂ)
    (ϑ₁ ϑ₂ : Torus d (N₀ * L ^ (k + 1 - (k + 1))) → Fin N → ℂ) (h : Fin N → ℂ)
    (hag : ∀ x ∈ dataSites G, mixedLift Ω ψ₁ ϑ₁ x = mixedLift Ω ψ₂ ϑ₂ x) :
    liftMixed G hΩ hG ψ₁ ϑ₁ h = liftMixed G hΩ hG ψ₂ ϑ₂ h := by
  classical
  refine Background.BgData.ext' ?_ rfl
  funext x
  simp only [liftMixed, BgData.clip]
  by_cases hx : x ∈ dataSites G
  · simp only [hx, ↓reduceIte]; exact hag x hx
  · simp [hx]

omit [NeZero M] in
theorem holeStepLoc_congr_D' (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K)
    (hk1 : 1 ≤ k) (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (ψ₁ ψ₂ : MultiFieldC S n M K N) (z : ℝ)
    (h₀ : Fin N → ℝ) (a₁ ν β p₁ δ : ℝ) (V : Set (CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)))
    (h : (holeStepLoc g hnn hM1 H hk hk1 hρ ψ₁ z h₀ a₁ ν β p₁ δ V).D' =
      (holeStepLoc g hnn hM1 H hk hk1 hρ ψ₂ z h₀ a₁ ν β p₁ δ V).D') :
    holeStepLoc g hnn hM1 H hk hk1 hρ ψ₁ z h₀ a₁ ν β p₁ δ V =
      holeStepLoc g hnn hM1 H hk hk1 hρ ψ₂ z h₀ a₁ ν β p₁ δ V :=
  holeStepLocAt_congr_D' (glob := false) g hnn hM1 H hk hk1 hρ ψ₁ ψ₂ z h₀ a₁ ν β p₁ δ V h

/-- The block of scale `i ≤ k+1` of the history torus containing a site of the cover torus. -/
noncomputable def coverBlk {k : ℕ} (hk : k + 1 ≤ K) (i : ℕ) (hi : i ≤ k + 1)
    (x : CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)) : BlockAt S n M K i :=
  LargeField.torusCast (coverScale_eq g hnn hM1 hi hk)
    (jBlock S.d S.L ((g.c * n (k + 1)) * S.L ^ m₁) (k + 1) i x)

/-- **The sites read by the datum of the local step lie in `Y`**: every site of the data sites of the
local pair has its blocks of scales `k` and `k + 1` (those read by the mixed lift) inside `Y`.  This is
the geometric input `hsiteY` (for `Y` a fine set of the output label). -/
def StepReadsIn (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K) (hk1 : 1 ≤ k)
    (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (ψ : MultiFieldC S n M K N) (z : ℝ) (h₀ : Fin N → ℝ)
    (a₁ ν β p₁ δ : ℝ) (V : Set (CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)))
    (Y : Set (Torus S.d (M * n K * S.L ^ K))) : Prop :=
  ∀ x ∈ dataSites (holeStepLoc g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).G',
    BlockSub k (coverBlk g hnn hM1 hk k (Nat.le_succ k) x) Y ∧
      BlockSub (k + 1) (coverBlk g hnn hM1 hk (k + 1) le_rfl x) Y

omit [NeZero M] in
/-- Any datum `glob`. -/
theorem holeStepLocAt_D'_congr (glob : Bool) (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K)
    (hk1 : 1 ≤ k) (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (ψ₁ ψ₂ : MultiFieldC S n M K N) (z : ℝ)
    (h₀ : Fin N → ℝ) (a₁ ν β p₁ δ : ℝ) (V : Set (CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)))
    (Y : Set (Torus S.d (M * n K * S.L ^ K)))
    (hread : StepReadsIn g hnn hM1 H hk hk1 hρ ψ₁ z h₀ a₁ ν β p₁ δ V Y)
    (hψ : ∀ j, j ≤ K → ∀ y : BlockAt S n M K j, BlockSub j y Y → ψ₁ j y = ψ₂ j y) :
    holeStepLocAt g hnn hM1 glob H hk hk1 hρ ψ₁ z h₀ a₁ ν β p₁ δ V =
      holeStepLocAt g hnn hM1 glob H hk hk1 hρ ψ₂ z h₀ a₁ ν β p₁ δ V := by
  classical
  refine holeStepLocAt_congr_D' g hnn hM1 glob H hk hk1 hρ ψ₁ ψ₂ z h₀ a₁ ν β p₁ δ V ?_
  unfold holeStepLocAt
  unfold HoleStep.restrict
  dsimp only
  refine liftMixed_congr_data _ _ _ _ _ _ _ _ (fun x hx => ?_)
  obtain ⟨h1, h2⟩ := hread x hx
  unfold mixedLift
  split_ifs
  · unfold blockLift coverField scaleMulti
    funext i
    exact congrArg (fun w => (z : ℂ) * w i) (hψ (k + 1) hk _ h2)
  · unfold blockLift coverField
    exact hψ k (by omega) _ h1

omit [NeZero M] in
theorem holeStepLoc_D'_congr (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K)
    (hk1 : 1 ≤ k) (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (ψ₁ ψ₂ : MultiFieldC S n M K N) (z : ℝ)
    (h₀ : Fin N → ℝ) (a₁ ν β p₁ δ : ℝ) (V : Set (CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)))
    (Y : Set (Torus S.d (M * n K * S.L ^ K)))
    (hread : StepReadsIn g hnn hM1 H hk hk1 hρ ψ₁ z h₀ a₁ ν β p₁ δ V Y)
    (hψ : ∀ j, j ≤ K → ∀ y : BlockAt S n M K j, BlockSub j y Y → ψ₁ j y = ψ₂ j y) :
    holeStepLoc g hnn hM1 H hk hk1 hρ ψ₁ z h₀ a₁ ν β p₁ δ V =
      holeStepLoc g hnn hM1 H hk hk1 hρ ψ₂ z h₀ a₁ ν β p₁ δ V :=
  holeStepLocAt_D'_congr (glob := false) g hnn hM1 H hk hk1 hρ ψ₁ ψ₂ z h₀ a₁ ν β p₁ δ V Y hread hψ

variable {k : ℕ}

theorem oldCoefLF_congr_step_data
    {St₁ St₂ : HoleStep S.d S.L (g.c * n (k + 1)) m₁ k N (minSep S.L g.M1) (minSep S.L g.M1)}
    (e : St₁ = St₂) (H : RegionHistory S n R k0 K) (hk : k + 1 ≤ K) (ρc : ℝ) (ρ r : ℕ)
    {geo : Geo S n R M} {cs : OpConsts} {P : BudgetConsts}
    (rep : Rep S n R k0 K M N geo cs P k) (A : LabHist S n R k0 K) (X : Finset (Torus S.d (n k)))
    (ψ₁ ψ₂ ψ'₁ ψ'₂ : MultiFieldC S n M K N) (hv : EuclideanSpace ℝ (Fin N))
    (gx₁ gx₂ : GIdx S n M K N → ℂ) (J : Finset (ℕ × CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)))
    (ψout₁ : St₁.U → Fin N → ℂ) (ψout₂ : St₂.U → Fin N → ℂ)
    (hout : ∀ b, ψout₁ b = ψout₂ (e ▸ b))
    (hT : ∀ comp, oldTermLF g hnn hM1 rep A X hk St₂.G' ψ₁ ψ'₁ hv gx₁ comp =
      oldTermLF g hnn hM1 rep A X hk St₂.G' ψ₂ ψ'₂ hv gx₂ comp) :
    oldCoefLF g hnn hM1 St₁ H hk (coverOf St₁.G') ρc ρ r ∅ ψout₁ rep A X ψ₁ ψ'₁ hv gx₁
      (locCubes g (coverOf St₁.G') J) (fun b => absurd b.2 (Finset.notMem_empty _)) =
    oldCoefLF g hnn hM1 St₂ H hk (coverOf St₂.G') ρc ρ r ∅ ψout₂ rep A X ψ₂ ψ'₂ hv gx₂
      (locCubes g (coverOf St₂.G') J) (fun b => absurd b.2 (Finset.notMem_empty _)) := by
  subst e
  unfold oldCoefLF
  have h1 : oldTermLF g hnn hM1 rep A X hk St₁.G' ψ₁ ψ'₁ hv gx₁ =
      oldTermLF g hnn hM1 rep A X hk St₁.G' ψ₂ ψ'₂ hv gx₂ := funext hT
  rw [h1]
  congr 2
  funext b
  exact hout b

omit [∀ k, NeZero (n k)] [NeZero M] [NeZero S.L] in
theorem BlockSub.mono {j : ℕ} {y : BlockAt S n M K j} {A B : Set (Torus S.d (M * n K * S.L ^ K))}
    (h : BlockSub (S := S) (n := n) (M := M) (K := K) j y A) (hAB : A ⊆ B) :
    BlockSub (S := S) (n := n) (M := M) (K := K) j y B := fun x hx => hAB (h x hx)

/-- **The old term at the composed multiscale field is local** (clause `loc_field` of the record at
the old label `X`, with `fineSet X ⊆ Y`): if two multiscale fields agree on the blocks inside `Y`,
the old terms at their composed fields (the same fluctuation field `comp`) agree. -/
theorem oldTermLF_congr_fields {geo : Geo S n R M} {cs : OpConsts} {P : BudgetConsts}
    (rep : Rep S n R k0 K M N geo cs P k) (A : LabHist S n R k0 K) (X : Finset (Torus S.d (n k)))
    (hk : k + 1 ≤ K) {ϱ' : ℝ} (G' : GeneratingSet S.d S.L ((g.c * n (k + 1)) * S.L ^ m₁) (k + 1) ϱ')
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
    (ψ₁ ψ₂ ψ'₁ ψ'₂ : MultiFieldC S n M K N) (hv : EuclideanSpace ℝ (Fin N))
    (gx₁ gx₂ : GIdx S n M K N → ℂ)
    (hψ : ∀ j, j ≤ K → ∀ y : BlockAt S n M K j, BlockSub (S := S) (n := n) (M := M) (K := K) j y Y →
      ψ₁ j y = ψ₂ j y)
    (hψ' : ∀ j, j ≤ K → ∀ y : BlockAt S n M K j,
      BlockSub (S := S) (n := n) (M := M) (K := K) j y Y → ψ'₁ j y = ψ'₂ j y)
    (hgx : ∀ x i, x ∈ Y → gx₁ (x, i) = gx₂ (x, i)) (comp : unitPts G' → Fin N → ℂ) :
    oldTermLF g hnn hM1 rep A X hk G' ψ₁ ψ'₁ hv gx₁ comp =
      oldTermLF g hnn hM1 rep A X hk G' ψ₂ ψ'₂ hv gx₂ comp := by
  unfold oldTermLF
  refine hloc _ _ _ _ _ _ _ (fun j hj y hy => ⟨?_, hψ' j hj y (BlockSub.mono hy hXY)⟩)
    (fun x i hx => hgx x i (hXY hx))
  have h1 := hψ j hj y (BlockSub.mono hy hXY)
  unfold composedMulti
  split_ifs
  · exact h1
  · rfl
  · exact h1
  · rfl

/-- **The clause `loc_field` of (D7) for the coefficient of the re-expanded old term**:
the coefficient `T(X, J)` on the local pair does not change when the multiscale fields `ψ`, `ψ'` and
the external source `gx` are changed outside `Y`.  Inputs: the clause `loc_field` of the record at
the old label `X` (`hloc`), `fineSet X ⊆ Y` (`hXY`) and that the datum of the local step reads only
sites whose blocks lie in `Y` (`hsiteY`, `StepReadsIn`; for `Y` a fine set of the output label this
is `markSite_holeClose_subset_outLabel`). Core for the readings of the local pair (the datum `glob`,
the label `σ` of the local set). -/
theorem oldCoefLocAt_congr_fields (glob : Bool) (σ : Finset (Torus S.d (n k)) → Finset (Torus S.d (n k))) (H : RegionHistory S n R k0 K) (hk : k + 1 ≤ K) (hk1 : 1 ≤ k)
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
      (locSetXJ g hM1 H r r' (σ X) J) Y)
    (hψ : ∀ j, j ≤ K → ∀ y : BlockAt S n M K j, BlockSub (S := S) (n := n) (M := M) (K := K) j y Y →
      ψ₁ j y = ψ₂ j y)
    (hψ' : ∀ j, j ≤ K → ∀ y : BlockAt S n M K j,
      BlockSub (S := S) (n := n) (M := M) (K := K) j y Y → ψ'₁ j y = ψ'₂ j y)
    (hgx : ∀ x i, x ∈ Y → gx₁ (x, i) = gx₂ (x, i))
    (ψhat : (holeStepLF g hnn hM1 H hk hk1 hρ ψ₁ z h₀ a₁ ν β p₁ δ).U → Fin N → ℂ) :
    oldCoefLocAt (glob := glob) (σ := σ) g hnn hM1 H hk hk1 hρ ψ₁ z h₀ a₁ ν β p₁ δ ρc ρ r r' rep A X ψ'₁ hv gx₁ J ψhat =
      oldCoefLocAt (glob := glob) (σ := σ) g hnn hM1 H hk hk1 hρ ψ₂ z h₀ a₁ ν β p₁ δ ρc ρ r r' rep A X ψ'₂ hv gx₂ J ψhat := by
  have e := holeStepLocAt_D'_congr g hnn hM1 glob H hk hk1 hρ ψ₁ ψ₂ z h₀ a₁ ν β p₁ δ
    (locSetXJ g hM1 H r r' (σ X) J) Y hsiteY hψ
  unfold oldCoefLocAt
  refine oldCoefLF_congr_step_data g hnn hM1 e H hk ρc ρ r rep A X ψ₁ ψ₂ ψ'₁ ψ'₂ hv gx₁ gx₂ J _ _ ?_ ?_
  · intro b
    unfold restrictU
    congr 1
    exact Subtype.ext (HoleStep.val_cast_eq (g := g) e b).symm
  · intro comp
    exact oldTermLF_congr_fields g hnn hM1 rep A X hk _ hloc Y hXY ψ₁ ψ₂ ψ'₁ ψ'₂ hv gx₁ gx₂
      hψ hψ' hgx comp

/-- **The clause `loc_field` of (D7) for the coefficient of the re-expanded old term**: the
coefficient `T(X, J)` on the local pair does not change when the multiscale fields `ψ`, `ψ'` and the
external source `gx` are changed outside `Y`.  Inputs: the clause `loc_field` of the record at the old
label `X` (`hloc`), `fineSet X ⊆ Y` (`hXY`) and that the datum of the local step reads only sites whose
blocks lie in `Y` (`hsiteY`, `StepReadsIn`; for `Y` a fine set of the output label this is
`markSite_holeClose_subset_outLabel`). -/
theorem oldCoefLoc_congr_fields (H : RegionHistory S n R k0 K) (hk : k + 1 ≤ K) (hk1 : 1 ≤ k)
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
      (locSetXJ g hM1 H r r' X J) Y)
    (hψ : ∀ j, j ≤ K → ∀ y : BlockAt S n M K j, BlockSub (S := S) (n := n) (M := M) (K := K) j y Y →
      ψ₁ j y = ψ₂ j y)
    (hψ' : ∀ j, j ≤ K → ∀ y : BlockAt S n M K j,
      BlockSub (S := S) (n := n) (M := M) (K := K) j y Y → ψ'₁ j y = ψ'₂ j y)
    (hgx : ∀ x i, x ∈ Y → gx₁ (x, i) = gx₂ (x, i))
    (ψhat : (holeStepLF g hnn hM1 H hk hk1 hρ ψ₁ z h₀ a₁ ν β p₁ δ).U → Fin N → ℂ) :
    oldCoefLoc g hnn hM1 H hk hk1 hρ ψ₁ z h₀ a₁ ν β p₁ δ ρc ρ r r' rep A X ψ'₁ hv gx₁ J ψhat =
      oldCoefLoc g hnn hM1 H hk hk1 hρ ψ₂ z h₀ a₁ ν β p₁ δ ρc ρ r r' rep A X ψ'₂ hv gx₂ J ψhat :=
  oldCoefLocAt_congr_fields (glob := false) (σ := fun X => X) g hnn hM1 H hk hk1 hρ z h₀ a₁ ν β p₁
    δ ρc ρ r r' rep A X hv J hloc Y hXY ψ₁ ψ₂ ψ'₁ ψ'₂ gx₁ gx₂ hsiteY hψ hψ' hgx ψhat

/-- **The clause `loc_hist` of (D7) for the coefficient of the re-expanded old term**: two histories
`(H, A)`, `(H', A')` whose records at the old label `X` agree (`hB`, the conclusion of the clause
`loc_hist` of the record), whose local steps agree (`e`, with the fixed values `ψout` related by it)
and whose collar cores agree (`hcore`) give the same coefficient.  The inputs `e`, `hcore` are the
geometric consequences of the agreement of the histories in `Y` (as `hsiteY`); the coefficient on the
local pair `oldCoefLoc` is this with `St = holeStepLoc …`, `ψout = restrictU … ψhat`. -/
theorem oldCoefLF_congr_hist
    {St₁ St₂ : HoleStep S.d S.L (g.c * n (k + 1)) m₁ k N (minSep S.L g.M1) (minSep S.L g.M1)}
    (e : St₁ = St₂) (H H' : RegionHistory S n R k0 K) (hk : k + 1 ≤ K) (ρc : ℝ) (ρ r : ℕ)
    {geo : Geo S n R M} {cs : OpConsts} {P : BudgetConsts}
    (rep : Rep S n R k0 K M N geo cs P k) (A A' : LabHist S n R k0 K) (X : Finset (Torus S.d (n k)))
    (ψ ψ' : MultiFieldC S n M K N) (hv : EuclideanSpace ℝ (Fin N)) (gx : GIdx S n M K N → ℂ)
    (J : Finset (ℕ × CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)))
    (ψout₁ : St₁.U → Fin N → ℂ) (ψout₂ : St₂.U → Fin N → ℂ)
    (hout : ∀ b, ψout₁ b = ψout₂ (e ▸ b))
    (hcore : (collarCoreC (c := g.c) (H.step k) hM1 r X :
        Finset (CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1))) =
      collarCoreC (c := g.c) (H'.step k) hM1 r X)
    (hB : ∀ (ψ₂ ψ₃ : MultiFieldC S n M K N) (h : Fin N → ℂ) (g₂ : GIdx S n M K N → ℂ),
      rep.B A X ψ₂ ψ₃ h g₂ = rep.B A' X ψ₂ ψ₃ h g₂) :
    oldCoefLF g hnn hM1 St₁ H hk (coverOf St₁.G') ρc ρ r ∅ ψout₁ rep A X ψ ψ' hv gx
      (locCubes g (coverOf St₁.G') J) (fun b => absurd b.2 (Finset.notMem_empty _)) =
    oldCoefLF g hnn hM1 St₂ H' hk (coverOf St₂.G') ρc ρ r ∅ ψout₂ rep A' X ψ ψ' hv gx
      (locCubes g (coverOf St₂.G') J) (fun b => absurd b.2 (Finset.notMem_empty _)) := by
  subst e
  unfold oldCoefLF
  have h1 : oldTermLF g hnn hM1 rep A X hk St₁.G' ψ ψ' hv gx =
      oldTermLF g hnn hM1 rep A' X hk St₁.G' ψ ψ' hv gx := by
    funext comp
    unfold oldTermLF
    exact hB _ _ _ _
  rw [h1, hcore]
  congr 2
  funext b
  exact hout b

end Loc



end Balaban.RootFSpine
