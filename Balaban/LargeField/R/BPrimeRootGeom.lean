/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.BPrimeRootForm
public import Balaban.LargeField.R.BPrimeCast
public import Balaban.Fluctuation.LocalClassDensityIrrelSuppSpec

/-!
# The P3 geometry of the roots of the residual of `R`

The roots of the residual of `R` (`sfExp2At_sub_eq_roots`) are localized (P3 §4) in the whole-lattice
generating set of the top level `K` (`IsLevel G K`): every root region `X` is a union of cubes of the
top layer, and its region `X₁ = X1 G m₀ j 𝒦X` is a union of cells of side `a_K = L^{K+m₀+m₁}`.

* `topLab`: the label of a centre of any generating set, the cell of side `L^{K+m₁}` containing its
  base; `mem_Pset_topLab`, `topLab_mem_cubeIdx`;
* `mem_X1_of_sameCell`: `X₁` is a union of cells of side `a_K`;
* `rootLabs`: the labels of the cut parameters of a root, the top cells off `X₁`, with the facts asked
  by `bPrime_pairs_aggregate_adm` (`rootLabs_mem`, `rootLabs_disj`, `rootLabs_par`,
  `mem_Pset_topLab`) for every pair of generating sets;
* `SFCtx.tCubeOfC_eq_iff`, `SFCtx.cubeCorner`, `SFCtx.sset_singleton_eq`: a cube of `𝕋_k` is a cell
  of side `a_k` of the Def-6 torus, the local cube `LocalCover.cube m₀ (k - 1)` of its corner.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Localization Balaban.Fluctuation

section TopLab

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L]

/-- **The top label of a centre**: the cell of side `L^{K+m₁}` (a cube of the top level `K`)
containing its base. -/
def topLab (P : ℕ × Localization.CTorus d L N₁ m₁ K) : ℕ × Localization.CTorus d L N₁ m₁ K :=
  (K, cbase (L ^ (K + m₁)) P.2)

omit [NeZero N₁] [NeZero L] in
theorem pow_top_dvd : L ^ (K + m₁) ∣ (N₁ * L ^ m₁) * L ^ K :=
  ⟨N₁, by rw [pow_add]; ring⟩

/-- The cube of a centre of level `≤ K` lies in the parameter cube of its top label. -/
theorem mem_Pset_topLab {P : ℕ × Localization.CTorus d L N₁ m₁ K} (hP : P.1 ≤ K) {x : Localization.CTorus d L N₁ m₁ K}
    (hx : x ∈ cubeP P) : x ∈ Pset m₁ (topLab P) := by
  have hpos : 0 < L ^ (K + m₁) := pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) _
  have h1 : SameCell (L ^ (P.1 + m₁)) x P.2 := mem_cubeP.1 hx
  have h2 : SameCell (L ^ (K + m₁)) x P.2 := h1.mono (pow_dvd_pow L (by omega))
  have h3 : SameCell (L ^ (K + m₁)) P.2 (cbase (L ^ (K + m₁)) P.2) := by
    rw [sameCell_iff_cbase_eq hpos]
    exact (cbase_eq_of_mem_box pow_top_dvd (aligned_cbase P.2) (mem_box_self _ hpos)).symm
  exact h2.trans h3

/-- The top label is a centre of a whole-lattice set of the top level. -/
theorem topLab_mem_cubeIdx {ϱ : ℝ} {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} (hG : IsLevel G K)
    (P : ℕ × Localization.CTorus d L N₁ m₁ K) : topLab P ∈ cubeIdx G :=
  (mem_cubeIdx G).2 ⟨hG.bounds, hG.mem_layer _, aligned_cbase P.2⟩

/-- **`X₁` is a union of cells of side `a_K`.** -/
theorem mem_X1_of_sameCell {ϱ : ℝ} {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {m₀ j : ℕ}
    (hN : L ^ m₀ ∣ N₁) {𝒦X : Set (Localization.CTorus d L N₁ m₁ K)} {x y : Localization.CTorus d L N₁ m₁ K}
    (hx : x ∈ X1 G m₀ j 𝒦X) (hxy : SameCell (cellSide L m₀ m₁ K) y x) :
    y ∈ X1 G m₀ j 𝒦X := by
  obtain ⟨b, hb, hxb, hsub⟩ := X1_cubes x hx
  have ha := cellSide_dvd (L := L) (m₁ := m₁) (K := K) hN (le_refl K)
  have ha0 := cellSide_pos (L := L) (m₁ := m₁) m₀ K
  have hcell := cell_subset_cube ha ha0 hb hxb
  have hy : y ∈ Localization.box (cbase (cellSide L m₀ m₁ K) x) (cellSide L m₀ m₁ K) := by
    rw [← (sameCell_iff_cbase_eq ha0).1 hxy]
    exact mem_box_cbase ha0 y
  exact hsub (hcell hy)

/-- **The parameter cube of a top label meets `X₁` only if it lies in `X₁`**: so the top label of a
centre whose cube is not in `X₁` is disjoint from `X₁`. -/
theorem disjoint_Pset_topLab {ϱ : ℝ} {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {m₀ j : ℕ}
    (hN : L ^ m₀ ∣ N₁) {𝒦X : Set (Localization.CTorus d L N₁ m₁ K)} {P : ℕ × Localization.CTorus d L N₁ m₁ K}
    (hP : P.1 ≤ K) (hPX : ¬ (↑(cubeP P) : Set (Localization.CTorus d L N₁ m₁ K)) ⊆ X1 G m₀ j 𝒦X) :
    Disjoint (Pset m₁ (topLab P)) (X1 G m₀ j 𝒦X) := by
  rw [Set.disjoint_left]
  intro y hyP hyX
  apply hPX
  intro x hx
  have hxP := mem_Pset_topLab hP (Finset.mem_coe.1 hx)
  have hxy : SameCell (L ^ (K + m₁)) x y := hxP.trans (SameCell.symm hyP)
  have hxy' : SameCell (cellSide L m₀ m₁ K) x y :=
    hxy.mono (by unfold cellSide; exact pow_dvd_pow L (by omega))
  exact mem_X1_of_sameCell hN hyX hxy'

open Classical in
/-- **The labels of the cut parameters of a root** with region `X₁`: the centres of `G` whose
parameter cubes are disjoint from `X₁`. -/
noncomputable def rootLabs {ϱ : ℝ} (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ)
    (X₁ : Set (Localization.CTorus d L N₁ m₁ K)) : Finset (ℕ × Localization.CTorus d L N₁ m₁ K) :=
  (cubeIdx G).filter fun q => Disjoint (Pset m₁ q) X₁

theorem rootLabs_mem {ϱ : ℝ} {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ}
    {X₁ : Set (Localization.CTorus d L N₁ m₁ K)} (i : rootLabs G X₁) : i.1 ∈ cubeIdx G := by
  classical
  exact (Finset.mem_filter.1 i.2).1

theorem rootLabs_disj {ϱ : ℝ} {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ}
    {X₁ : Set (Localization.CTorus d L N₁ m₁ K)} (i : rootLabs G X₁) : Disjoint (Pset m₁ i.1) X₁ := by
  classical
  exact (Finset.mem_filter.1 i.2).2

/-- **Every centre of any generating set off `X₁` has its top label among the labels of the root**
(the hypothesis `hπpar` of `bPrime_pairs_aggregate_adm` for the map `topLab`). -/
theorem rootLabs_par {ϱ ϱ' : ℝ} {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} (hG : IsLevel G K)
    {m₀ j : ℕ} (hN : L ^ m₀ ∣ N₁) {𝒦X : Set (Localization.CTorus d L N₁ m₁ K)}
    {X₁f : Finset (Localization.CTorus d L N₁ m₁ K)}
    (hX₁ : (↑X₁f : Set (Localization.CTorus d L N₁ m₁ K)) = X1 G m₀ j 𝒦X)
    (H : GeneratingSet d L (N₁ * L ^ m₁) K ϱ') :
    ∀ P ∈ cubeIdx H, ¬ cubeP P ⊆ X₁f →
      ∃ i : rootLabs G (X1 G m₀ j 𝒦X), i.1 = topLab P := by
  classical
  intro P hP hPX
  have hPK : P.1 ≤ K := ((mem_cubeIdx H).1 hP).1.2
  have hdis : Disjoint (Pset m₁ (topLab P)) (X1 G m₀ j 𝒦X) := by
    refine disjoint_Pset_topLab hN hPK fun hsub => hPX fun x hx => ?_
    have := hsub (Finset.mem_coe.2 hx)
    rw [← hX₁] at this
    exact Finset.mem_coe.1 this
  exact ⟨⟨topLab P, Finset.mem_filter.2 ⟨topLab_mem_cubeIdx hG P, hdis⟩⟩, rfl⟩

end TopLab

namespace Def7.SFCtx

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N k m₁ : ℕ} {ϱ : ℝ} (C : SFCtx S n R M K N k m₁ ϱ)

/-- **The coordinates of the cube of `𝕋_k` of a site of the Def-6 torus**: `⌊x_μ / (L^k M)⌋`. -/
theorem tCubeOfC_val (x : Localization.CTorus S.d S.L C.N₁ m₁ k) (μ : Fin S.d) :
    (C.tCubeOfC x μ).val = (x μ).val / (S.L ^ k * M) := by
  have : NeZero (M * n K * S.L ^ K) :=
    ⟨Nat.mul_ne_zero (Nat.mul_ne_zero (NeZero.ne M) (NeZero.ne (n K)))
      (pow_ne_zero _ (NeZero.ne S.L))⟩
  unfold tCubeOfC tCubeOfBg cubeMap
  rw [blockMap_apply, blockCoord_val (fine_eq (L := S.L) (M := M) (nn := n) C.hnn C.hkK), bgToFine, LargeField.torusCast_val, sfToBg,
    LargeField.torusCast_val]

/-- **Two sites lie in the same cube of `𝕋_k` iff they lie in the same cell of side `L^k M`.** -/
theorem tCubeOfC_eq_iff (x y : Localization.CTorus S.d S.L C.N₁ m₁ k) :
    C.tCubeOfC x = C.tCubeOfC y ↔ SameCell (S.L ^ k * M) x y := by
  constructor
  · intro h μ
    have := congrArg (fun z : Torus S.d (n k) => (z μ).val) h
    simp only [tCubeOfC_val] at this
    exact this
  · intro h
    funext μ
    apply ZMod.val_injective
    rw [tCubeOfC_val, tCubeOfC_val, h μ]

/-- The block of side `L^k M` of `𝕋_k` is the cell of side `a_k` (`M = c M₁ = L^{m₀+m₁}`). -/
theorem cellSide_eq_blk (hMm : C.geo.c * C.geo.M1 = S.L ^ (C.m₀ + m₁)) :
    cellSide S.L C.m₀ m₁ k = S.L ^ k * M := by
  calc cellSide S.L C.m₀ m₁ k = S.L ^ k * (C.geo.c * C.geo.M1) := by
        rw [hMm, cellSide, ← pow_add]
        congr 1
        ring
    _ = S.L ^ k * M := congrArg (S.L ^ k * ·) C.geo.hM.symm

/-- The side of the Def-6 torus is `L^k M n_k`. -/
theorem cSide_eq : (C.N₁ * S.L ^ m₁) * S.L ^ k = S.L ^ k * M * n k := by
  rw [C.hT]
  calc C.geo.M1 * (C.geo.c * n k) * S.L ^ k = S.L ^ k * (C.geo.c * C.geo.M1) * n k := by ring
    _ = S.L ^ k * M * n k := congrArg (fun t => S.L ^ k * t * n k) C.geo.hM.symm

theorem mem_box_cbase_iff {d ℓ a : ℕ} [NeZero ℓ] (ha : a ∣ ℓ) (ha0 : 0 < a) (x y : Torus d ℓ) :
    y ∈ Localization.box (cbase a x) a ↔ SameCell a y x := by
  constructor
  · intro hy
    exact (sameCell_iff_cbase_eq ha0).2 (cbase_eq_of_mem_box ha (aligned_cbase x) hy)
  · intro h
    rw [← (sameCell_iff_cbase_eq ha0).1 h]
    exact mem_box_cbase ha0 y

/-- **The fine set of a cube of `𝕋_k` is the local cube of level `k - 1`** (the cell of side `a_k`)
of any of its sites. -/
theorem sset_singleton_eq (hMm : C.geo.c * C.geo.M1 = S.L ^ (C.m₀ + m₁)) (hk : 1 ≤ k)
    (hN : S.L ^ C.m₀ ∣ C.N₁) (x : Localization.CTorus S.d S.L C.N₁ m₁ k) :
    C.sset {C.tCubeOfC x} = LocalCover.cube C.m₀ (k - 1) x := by
  ext y
  have hL : S.L * cellSide S.L C.m₀ m₁ (k - 1) = cellSide S.L C.m₀ m₁ k := by
    unfold cellSide
    rw [← pow_succ']
    congr 1
    omega
  have ha := cellSide_dvd (L := S.L) (m₁ := m₁) (K := k) hN (le_refl k)
  have ha0 := cellSide_pos (L := S.L) (m₁ := m₁) C.m₀ k
  unfold LocalCover.cube LocalCover.corner
  rw [hL, mem_box_cbase_iff ha ha0, C.cellSide_eq_blk hMm, ← tCubeOfC_eq_iff, mem_sset_iff_cube,
    Set.mem_singleton_iff]

/-- **The corner of a cube of `𝕋_k`** on the Def-6 torus. -/
def cubeCorner (c : Torus S.d (n k)) : Localization.CTorus S.d S.L C.N₁ m₁ k :=
  fun μ => (((c μ).val * (S.L ^ k * M) : ℕ) : ZMod _)

theorem tCubeOfC_cubeCorner (c : Torus S.d (n k)) : C.tCubeOfC (C.cubeCorner c) = c := by
  funext μ
  apply ZMod.val_injective
  have hpos : 0 < S.L ^ k * M :=
    Nat.mul_pos (pow_pos (Nat.pos_of_ne_zero (NeZero.ne S.L)) _) (Nat.pos_of_ne_zero (NeZero.ne M))
  have hlt : (c μ).val * (S.L ^ k * M) < (C.N₁ * S.L ^ m₁) * S.L ^ k := by
    rw [C.cSide_eq, mul_comm (S.L ^ k * M) (n k)]
    exact Nat.mul_lt_mul_of_pos_right (ZMod.val_lt (c μ)) hpos
  rw [tCubeOfC_val]
  unfold cubeCorner
  rw [ZMod.val_natCast_of_lt hlt, Nat.mul_div_cancel _ hpos]

end Def7.SFCtx

end Balaban.LargeField
