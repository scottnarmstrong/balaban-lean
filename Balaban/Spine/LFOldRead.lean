/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.LFOldLocal
public import Balaban.LargeField.R.PsiZeroWindowGeom
public import Balaban.LargeField.Background.TwoTorusCubeLift

/-!
# The read points of an old boundary term of a history (the field locality of (D7))

The field-locality clause of (D7) (`D7BdryPost.loc_field`: the term `ℬ^{(k)}(X, 𝔸)` depends on the
fields only through the blocks inside the fine set of `X`) gives the hypothesis `hB` of
`oldCoefLF_eq_zero_of_not_reached`: the old term at the composed multiscale field reads the field on
the unit points of `Ω_{k+1}` only at the read points `readPts` (the unit points of `A_X`).

* `exists_fine_of_unitOfBlock`: the representative of the unit point of a block, transported to the
  history torus, lies in the block, with its cubes of `𝕋_k` and `𝕋_{k+1}` (the cover torus and the
  fine torus of the history are the same torus, `coverScale_eq`);
* `cubeKOfC_mem_of_blockSub`: the representative of the unit point of a block inside the fine set of
  `X` has its cube of `𝕋_k` in `X`;
* `cubeOfC_mem_of_unitPts`: the representative of a unit point of the set of (2.17) lies in
  `Ω_{k+1}`;
* `oldTermLF_congr_of_locField`: **the old term reads the composed field only at the read points**,
  from the field-locality clause of the record at `X`.
-/

@[expose] public section

open MeasureTheory Balaban Balaban.LargeField Balaban.LargeField.Def7 Balaban.Multiscale
  Balaban.Localization Balaban.Fluctuation Balaban.LargeField.RegionHistory

namespace Balaban.RootFSpine

section History

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {N m₁ : ℕ}
  (g : Geo S n R M) (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) (hM1 : g.M1 = S.L ^ m₁)

omit [NeZero M] in
/-- **The site of the history torus of the representative of a unit point**: for the unit point `b`
of a `k`-block `y` (`b = unitOfBlock y`), the representative of `b` transported to the history torus
lies in the block `y`, and its cubes of `𝕋_k` and `𝕋_{k+1}` are the cubes `cubeKOfC` and `cubeOfC`
of the representative (the cover torus and the fine torus of the history are the same torus,
`coverScale_eq`). -/
theorem exists_fine_of_unitOfBlock {k : ℕ} (hk : k + 1 ≤ K) {ϱ' : ℝ}
    {G' : GeneratingSet S.d S.L ((g.c * n (k + 1)) * S.L ^ m₁) (k + 1) ϱ'}
    (b : unitPts G') {y : Torus S.d (M * n K * S.L ^ (K - k))}
    (hb : (b : UnitTorus S.d S.L (g.c * n (k + 1)) m₁ k) = unitOfBlock g hnn hM1 hk y) :
    ∃ x : Torus S.d (M * n K * S.L ^ K), jBlock S.d S.L (M * n K) K k x = y ∧
      LargeField.cubeMap n S.L M K k x =
        cubeKOfC (c := g.c) (n1 := n (k + 1)) (n0 := n k) hM1 (unitRep b) ∧
      LargeField.cubeMap n S.L M K (k + 1) x =
        cubeOfC (c := g.c) (n1 := n (k + 1)) hM1 (unitRep b) := by
  have hside : (g.c * n (k + 1)) * S.L ^ m₁ * S.L ^ (k + 1) = M * n K * S.L ^ K := by
    simpa using coverScale_eq g hnn hM1 (Nat.zero_le (k + 1)) hk
  refine ⟨LargeField.torusCast hside (unitRep b), ?_, ?_, ?_⟩
  · have h1 : unitBlock (unitRep b) = unitOfBlock g hnn hM1 hk y := by
      rw [unitBlock_unitRep, hb]
    unfold unitBlock unitOfBlock at h1
    unfold jBlock
    rw [blockMap_torusCast,
      ← torusCast_blockMap_right (coverScale_eq g hnn hM1 (Nat.le_succ k) hk), h1]
    exact torusCast_symm_cast _ y
  · have e : S.L ^ k * M = S.L ^ k * (g.c * g.M1) := congrArg _ g.hM
    unfold LargeField.cubeMap cubeKOfC
    show _ = blockMap _ _ (LargeField.torusCast
      (congrArg (· * S.L ^ (k + 1)) (p6_side (c := g.c) (n1 := n (k + 1)) hM1)).symm (unitRep b))
    rw [blockMap_torusCast, blockMap_torusCast, e]
  · have e : S.L ^ (k + 1) * M = S.L ^ (k + 1) * (g.c * g.M1) := congrArg _ g.hM
    unfold LargeField.cubeMap cubeOfC
    show _ = blockMap _ _ (LargeField.torusCast
      (congrArg (· * S.L ^ (k + 1)) (p6_side (c := g.c) (n1 := n (k + 1)) hM1)).symm (unitRep b))
    rw [blockMap_torusCast, blockMap_torusCast, e]

omit [NeZero M] in
/-- **The cube of `𝕋_k` of the representative of the unit point of a block inside the fine set of
`X` lies in `X`.** -/
theorem cubeKOfC_mem_of_blockSub {k : ℕ} (hk : k + 1 ≤ K) {ϱ' : ℝ}
    {G' : GeneratingSet S.d S.L ((g.c * n (k + 1)) * S.L ^ m₁) (k + 1) ϱ'}
    (b : unitPts G') {y : Torus S.d (M * n K * S.L ^ (K - k))}
    (hb : (b : UnitTorus S.d S.L (g.c * n (k + 1)) m₁ k) = unitOfBlock g hnn hM1 hk y)
    {X : Finset (Torus S.d (n k))}
    (hy : BlockSub (S := S) (n := n) (M := M) (K := K) k y
      (fineSet (S := S) (n := n) M K k (X : Set (Torus S.d (n k))))) :
    cubeKOfC (c := g.c) (n1 := n (k + 1)) (n0 := n k) hM1 (unitRep b) ∈ X := by
  obtain ⟨x, hx, hxk, -⟩ := exists_fine_of_unitOfBlock g hnn hM1 hk b hb
  have hmem : LargeField.cubeMap n S.L M K k x ∈ (X : Set (Torus S.d (n k))) := hy x hx
  rwa [hxk] at hmem

omit [NeZero M] in
/-- **The representative of a unit point of the set of (2.17) lies in `Ω_{k+1}`.** -/
theorem cubeOfC_mem_of_unitPts (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K)
    (hk1 : 1 ≤ k) (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (ψ : MultiFieldC S n M K N) (z₀ : ℝ)
    (h₀ : Fin N → ℝ) (a₁ ν β p₁ δ : ℝ) (b : (holeStepLF g hnn hM1 H hk hk1 hρ ψ z₀ h₀ a₁ ν β p₁ δ).U) :
    cubeOfC (c := g.c) (n1 := n (k + 1)) hM1 (unitRep b) ∈ (H.step k).Omega := by
  have htop := (holeStepLF g hnn hM1 H hk hk1 hρ ψ z₀ h₀ a₁ ν β p₁ δ).unitRep_mem_top b
  have hΩ := ((holeStepLF g hnn hM1 H hk hk1 hρ ψ z₀ h₀ a₁ ν β p₁ δ).G'.mem_layer.1 htop).1
  have hc := g.hc
  change (unitRep b : CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)) ∈
    (p6TopC (k := k) (H.step k) hM1 (hnn k (by omega)) hρ (by omega)).Ω (k + 1) at hΩ
  rw [p6TopC, mem_castN_Ω, p6Top_Ω_top, mem_fineK1] at hΩ
  exact hΩ

/-- **The old term reads the composed field only at the read points** (from the field-locality
clause of (D7) for the term at `X`): two fields on the unit points of `Ω_{k+1}` agreeing at the read
points of `X` give the same value of `ℬ^{(k)}(X, 𝔸)` at the composed multiscale field. -/
theorem oldTermLF_congr_of_locField (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K)
    (hk1 : 1 ≤ k) (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (ψ : MultiFieldC S n M K N) (z₀ : ℝ)
    (h₀ : Fin N → ℝ) (a₁ ν β p₁ δ : ℝ) {geo : Geo S n R M} {cs : OpConsts} {P : BudgetConsts}
    (rep : Rep S n R k0 K M N geo cs P k) (A : LabHist S n R k0 K) (X : Finset (Torus S.d (n k)))
    (ψ' : MultiFieldC S n M K N) (hv : EuclideanSpace ℝ (Fin N)) (gx : GIdx S n M K N → ℂ)
    (hloc : ∀ (ψ₁ ψ₂ ψ'₁ ψ'₂ : MultiFieldC S n M K N) (h : Fin N → ℂ) (g₁ g₂ : GIdx S n M K N → ℂ),
      (∀ j, j ≤ K → ∀ y : BlockAt S n M K j,
        BlockSub (S := S) (n := n) (M := M) (K := K) j y
          (fineSet (S := S) (n := n) M K k (X : Set (Torus S.d (n k)))) →
          ψ₁ j y = ψ₂ j y ∧ ψ'₁ j y = ψ'₂ j y) →
      (∀ x i, x ∈ fineSet (S := S) (n := n) M K k (X : Set (Torus S.d (n k))) →
        g₁ (x, i) = g₂ (x, i)) →
      rep.B A X ψ₁ ψ'₁ h g₁ = rep.B A X ψ₂ ψ'₂ h g₂)
    (c c' : (holeStepLF g hnn hM1 H hk hk1 hρ ψ z₀ h₀ a₁ ν β p₁ δ).U → Fin N → ℂ)
    (hcc : ∀ b ∈ readPts g hM1 H (holeStepLF g hnn hM1 H hk hk1 hρ ψ z₀ h₀ a₁ ν β p₁ δ) X,
      c b = c' b) :
    oldTermLF g hnn hM1 rep A X hk (holeStepLF g hnn hM1 H hk hk1 hρ ψ z₀ h₀ a₁ ν β p₁ δ).G' ψ ψ'
        hv gx c =
      oldTermLF g hnn hM1 rep A X hk (holeStepLF g hnn hM1 H hk hk1 hρ ψ z₀ h₀ a₁ ν β p₁ δ).G' ψ ψ'
        hv gx c' := by
  classical
  unfold oldTermLF
  refine hloc _ _ _ _ _ _ _ (fun j _ y hy => ⟨?_, rfl⟩) (fun _ _ _ => rfl)
  rcases lt_trichotomy j k with hjk | hjk | hjk
  · rw [composedMulti_of_lt hk _ ψ c hjk, composedMulti_of_lt hk _ ψ c' hjk]
  · subst hjk
    by_cases hu : unitOfBlock g hnn hM1 hk y ∈
        unitPts (holeStepLF g hnn hM1 H hk hk1 hρ ψ z₀ h₀ a₁ ν β p₁ δ).G'
    · rw [composedMulti_in hk _ ψ c y hu, composedMulti_in hk _ ψ c' y hu]
      refine hcc _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, (mem_activeCoreC (H.step j)).2
        ⟨cubeKOfC_mem_of_blockSub g hnn hM1 hk _ rfl hy, ?_⟩⟩)
      exact cubeOfC_mem_of_unitPts g hnn hM1 H hk hk1 hρ ψ z₀ h₀ a₁ ν β p₁ δ _
    · rw [composedMulti_out hk _ ψ c y hu, composedMulti_out hk _ ψ c' y hu]
  · rw [composedMulti_of_gt hk _ ψ c hjk, composedMulti_of_gt hk _ ψ c' hjk]

end History

end Balaban.RootFSpine
