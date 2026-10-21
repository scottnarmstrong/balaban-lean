/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.LFOldD7Loc
public import Balaban.Spine.LFOldOut
public import Balaban.Spine.LFOldH7Loc

/-!
# The datum of the local step reads only sites in the output label (`hsiteY`)

`stepReadsIn_of_toFrame`: if the data sites of the local pair `G′_V` lie, on the frame torus, in the
pull-back `d7Pull F (k+1) Out` of a set `Out` of cubes of `𝕋_{k+1}`, then the blocks of scales `k` and
`k + 1` read by the mixed lift lie in the fine set `fineSet (k+1) Out` of the history torus
(`StepReadsIn`).  With `Out` the output label of a set `T` of cubes containing those of the site of the
mark, the hypothesis is `markSite_subset_outLabel` (`stepReadsIn_outLabel`), which discharges `hsiteY`
of `oldCoefLoc_congr_fields`.
-/

@[expose] public section

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Localization
  Balaban.LargeField Balaban.Fluctuation Balaban.LargeField.Def7 Balaban.LargeField.RegionHistory

namespace Balaban.RootFSpine

set_option linter.unusedSectionVars false

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {N m₁ : ℕ}
  (g : Geo S n R M) (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) (hM1 : g.M1 = S.L ^ m₁)

theorem jBlock_fineOfC {k : ℕ} (hk : k + 1 ≤ K) (i : ℕ) (hi : i ≤ k + 1)
    (x : CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)) :
    jBlock S.d S.L (M * n K) K i (fineOfC g hnn hM1 hk x) = coverBlk g hnn hM1 hk i hi x := by
  funext μ
  have h1 := coverScale_eq g hnn hM1 hi hk
  have hv : ∀ ν : Fin S.d, ((fineOfC g hnn hM1 hk x) ν).val = (x ν).val := fun ν =>
    LargeField.torusCast_val _ _ _
  apply ZMod.val_injective
  unfold coverBlk
  rw [LargeField.torusCast_val h1]
  simp only [jBlock, blockMap_apply, blockCoord, hv, ZMod.val_natCast]
  rw [h1]

/-- **The blocks read by the mixed lift lie in `Y`** when the data sites of the local pair lie in the
pull-back of the cubes `Out` (`hsite`): `StepReadsIn` for `Y = fineSet (k+1) Out`. -/
theorem stepReadsIn_of_toFrame {m₀ : ℕ} (F : FineSizeFrame S n M K m₀ m₁)
    (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K) (hk1 : 1 ≤ k)
    (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (ψ : MultiFieldC S n M K N) (z : ℝ) (h₀ : Fin N → ℝ)
    (a₁ ν β p₁ δ : ℝ) (V : Set (CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)))
    (Out : Set (Torus S.d (n (k + 1))))
    (hsite : ∀ x ∈ dataSites (holeStepLoc g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).G',
      toFrame g hnn hM1 F hk x ∈ d7Pull F (k + 1) Out) :
    StepReadsIn g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V
      (fineSet (S := S) (n := n) M K (k + 1) Out) := by
  intro x hx
  have hxO : cubeMap n S.L M K (k + 1) (fineOfC g hnn hM1 hk x) ∈ Out := by
    have h := hsite x hx
    rw [mem_d7Pull] at h
    unfold toFrame at h
    rw [castT_castT_symm] at h
    exact h
  have key : ∀ (j : ℕ) (hj : j ≤ k + 1),
      BlockSub (S := S) (n := n) (M := M) (K := K) j (coverBlk g hnn hM1 hk j hj x)
        (fineSet (S := S) (n := n) M K (k + 1) Out) := by
    intro j hj x' hx'
    have hb : jBlock S.d S.L (M * n K) K j (fineOfC g hnn hM1 hk x) =
        jBlock S.d S.L (M * n K) K j x' := by
      rw [jBlock_fineOfC g hnn hM1 hk j hj x]; exact hx'.symm
    have := cubeMap_eq_of_jBlock_eq hj hk hnn hb
    show cubeMap n S.L M K (k + 1) x' ∈ Out
    rw [← this]; exact hxO
  exact ⟨key k (Nat.le_succ k), key (k + 1) le_rfl⟩

/-- **`hsiteY` of `oldCoefLoc_congr_fields`, for the fine set of the output label**: for a family `J`
with a good site (`GoodJ`) and a set `T` of cubes of `Ω_{k+1}` with `d_Ω(T) < ∞` containing the cubes
of `Ω_{k+1}` inside the site of the mark, the datum of the local step of `V(X, J)` reads only blocks
inside the fine set of the output label of `T`. -/
theorem stepReadsIn_outLabel {m₀ : ℕ} (F : FineSizeFrame S n M K m₀ m₁)
    (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K) (hk1 : 1 ≤ k)
    (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (ψ : MultiFieldC S n M K N) (z : ℝ) (h₀ : Fin N → ℝ)
    (a₁ ν β p₁ δ : ℝ) (r r' : ℕ) (X : Finset (Torus S.d (n k)))
    (J : Finset (ℕ × CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)))
    (hJ : GoodJ g hnn hM1 F H hk hρ r r' (d7Pull F (k + 1) (OmegaCube H (k + 1))) X J)
    (T : Finset (CubeB (d := S.d) (L := S.L) (N₁ := F.N₁) (m₁ := m₁) (K := K) m₀ (k + 1)
      (d7Pull F (k + 1) (OmegaCube H (k + 1)))))
    (hT : blocksOf m₀ (k + 1) (d7Pull F (k + 1) (OmegaCube H (k + 1)))
      (markSite g hnn hM1 F H hk hρ r r' X J) ⊆ T)
    (hfin : dOmega m₀ (k + 1) (d7Pull F (k + 1) (OmegaCube H (k + 1))) (sitesOf T) ≠ ⊤) :
    StepReadsIn g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ (locSetXJ g hM1 H r r' X J)
      (fineSet (S := S) (n := n) M K (k + 1)
        (outLabel F k (OmegaCube H (k + 1)) T : Set (Torus S.d (n (k + 1))))) := by
  refine stepReadsIn_of_toFrame g hnn hM1 F H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ _ _ (fun x hx => ?_)
  refine markSite_subset_outLabel F hnn hM1 H hk hρ r r' X J hJ T hT hfin ?_
  exact markBase_subset_markSite g hnn hM1 F H hk hρ r r' X J (Or.inr ⟨x, hx, rfl⟩)

/-- **`hXY` of `oldCoefLoc_congr_fields`, for the fine set of the output label**: the fine set of the old
label `X` lies in the fine set of the output label (`d7Pull_subset_outLabel`). -/
theorem fineSet_subset_outLabel {m₀ : ℕ} (F : FineSizeFrame S n M K m₀ m₁)
    (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K)
    (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) {Om : Set (Torus S.d (n k))} {X : Finset (Torus S.d (n k))}
    (hX : FineValidAt F k Om X)
    (hXm : (d7Pull F k (X : Set (Torus S.d (n k))) ∩
      d7Pull F (k + 1) (OmegaCube H (k + 1))).Nonempty) (r r' : ℕ)
    (J : Finset (ℕ × CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)))
    (T : Finset (CubeB (d := S.d) (L := S.L) (N₁ := F.N₁) (m₁ := m₁) (K := K) m₀ (k + 1)
      (d7Pull F (k + 1) (OmegaCube H (k + 1)))))
    (hT : blocksOf m₀ (k + 1) (d7Pull F (k + 1) (OmegaCube H (k + 1)))
      (markSite g hnn hM1 F H hk hρ r r' X J) ⊆ T)
    (hfin : dOmega m₀ (k + 1) (d7Pull F (k + 1) (OmegaCube H (k + 1))) (sitesOf T) ≠ ⊤) :
    fineSet (S := S) (n := n) M K k (X : Set (Torus S.d (n k))) ⊆
      fineSet (S := S) (n := n) M K (k + 1)
        (outLabel F k (OmegaCube H (k + 1)) T : Set (Torus S.d (n (k + 1)))) := by
  intro x hx
  have h := d7Pull_subset_outLabel F hnn hM1 H hk hρ hX hXm r r' J T hT hfin
    (show castT F.side.symm x ∈ d7Pull F k (X : Set (Torus S.d (n k))) from by
      rw [mem_d7Pull, castT_castT_symm]; exact hx)
  rw [mem_d7Pull, castT_castT_symm] at h
  exact h

end Balaban.RootFSpine
