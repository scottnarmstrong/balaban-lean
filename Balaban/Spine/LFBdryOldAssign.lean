/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.LFBdryOldEntropy
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The assignments of the old boundary terms of a step (part (a) of `LFBdryOldInput`; leaves O3, O5)

LFR Lemma IV.1.5 (iii); P6 p. 34, (4.32)–(4.34); P3 (4.41)–(4.49); P5 p. 512 (the part `ℬ''^{(k)}`).

At the step `k → k + 1` the old boundary terms `ℬ^{(k)}(X, 𝔸)` of a history whose domains `X` meet
the new region `Ω_{k+1}` are re-expanded in the fluctuation integral; to each term of the
re-expansion P6 p. 34 assigns "the corresponding domain `Y ∈ 𝒟_{k+1}(mod Ω^c_{k+1})` determined as
in (4.44) [3]": the domain `X` with the `π'_{k+1}`-cubes over its chosen cover and over the
decoupling patches, completed by the new holes it meets.  This file defines the assignments and
their output labels and proves their geometry and counting, on the landed class (ruling R11).

* `transferLabel_union_patches`, `transferCubes`, `transferCubes_spec`: the output label of an old
  label `X` with a cover `𝒦` and patches `J`, as a set of cubes of `𝕋_{k+1}`: it contains `X`, is a
  valid label at `Ω_{k+1}` (`FineValidAt`), has size at most `L⁻¹ d_k(X) + c_G |J|`, and `J`
  consists of its patches (`transfer_patches`).
* `optCovers`: the optimal covers of a label (the chosen covers attaining the size); the average
  over them is the covariant choice of the transfer.
* `oldAssign`, `assignOut`, `assignWt`: the assignments `(X, 𝒦, J)` of a history at the step
  `k → k + 1`, their output labels and their weights `1 / #optCovers`.
* `oldAssign_spec`: the geometry of one assignment (validity of `X` and of the output label, the
  inclusion, the patches, the size transfer, and the lower bound `d_k(X) ≥ L (⌊R_k⌋ + 2)` of leaf
  O4).
* `sum_assignWt_le`: the weights sharing an old label and a set of patches add up to at most `1`.
* `norm_sum_oldAssign_fiber_le`: **the bound of the old part at one output label** from the
  re-expansion bound of each assignment, with every other hypothesis of
  `Balaban.Fluctuation.norm_sum_oldAssign_le` discharged; the remaining hypotheses are the
  coefficient bound and the constant conditions `κ/2 - κ_o/L ≥ a_ent + 1` and (Λ28).
* `RegionHistory.cubeIdx_succ_mem_Zpre`, `assignOut_meets_Zpre`, `assignOut_mem_bdryDomsAt_iff`
  (leaf O3): every output label meets `Z^pre_{k+1}`, and it is a boundary domain of the pre-`R`
  class at `k + 1` exactly when it meets the complement of `Z^pre_{k+1}`; the others lie in the
  large-field region of scale `k + 1`.

**What is not here.**  The coefficient `T(X, 𝒦, J)` of an assignment, i.e. the old term re-expanded
in the fluctuation integral of the step (P5 (2.48), (3.2); FLUCTUATION Theorem 3.1 (c): the
interpolation average `∫₀¹ ⟨ℬ''^{(k)}⟩''_u du` in the measure of the step on `Ω''_{k+1}`, with the
localization (4.33) of each old term), and its bound P6 (4.34).  The fluctuation integral of a step
with large-field regions is not defined in the repository (`Fluctuation/Thm31cde.lean`: the objects
of the subdomain case are not defined; `Fluctuation.StepSetting` is the whole-lattice step), and the
modular localization of the old terms (Vmod) is conditional on open assertions
(`notes/phase1/VMOD.md` §1.4, `notes/phase1/VMOD-39.md`).  See `notes/phase1/SPINE.md`, row (g2).
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ j : ℕ}

omit [NeZero N₁] [NeZero L] in
/-- The hole closure is monotone. -/
theorem holeClose_mono (Ω : Set (CTorus d L N₁ m₁ K)) {A B : Set (CTorus d L N₁ m₁ K)}
    (h : A ⊆ B) : holeClose Ω A ⊆ holeClose Ω B := by
  rintro y (hy | hy)
  · exact Or.inl (h hy)
  · obtain ⟨z, hz, hyz⟩ := Set.mem_iUnion₂.1 hy
    exact Or.inr (Set.mem_iUnion₂.2 ⟨z, ⟨h hz.1, hz.2⟩, hyz⟩)

omit [NeZero N₁] [NeZero L] in
/-- **Closing twice**: `holeClose Ω (holeClose Ω A ∪ B) = holeClose Ω (A ∪ B)`. -/
theorem holeClose_holeClose_union (Ω A B : Set (CTorus d L N₁ m₁ K)) :
    holeClose Ω (holeClose Ω A ∪ B) = holeClose Ω (A ∪ B) := by
  refine Set.Subset.antisymm ?_ (holeClose_mono Ω (Set.union_subset_union_left B
    (subset_holeClose Ω A)))
  have hA : holeClose Ω A ⊆ holeClose Ω (A ∪ B) := holeClose_mono Ω Set.subset_union_left
  have hB : B ⊆ holeClose Ω (A ∪ B) :=
    Set.subset_union_right.trans (subset_holeClose Ω (A ∪ B))
  rintro y (hy | hy)
  · exact hy.elim (fun h => hA h) (fun h => hB h)
  · obtain ⟨z, ⟨hzS, hzΩ⟩, hyz⟩ := Set.mem_iUnion₂.1 hy
    rcases hzS with hzA | hzB
    · rcases hzA with hzA | hzA
      · exact Or.inr (Set.mem_iUnion₂.2 ⟨z, ⟨Or.inl hzA, hzΩ⟩, hyz⟩)
      · obtain ⟨w, hw, hzw⟩ := Set.mem_iUnion₂.1 hzA
        have e : OmegaComp Ω z = OmegaComp Ω w := (comp_eq_of_rtg hzw.2).symm
        rw [e] at hyz
        exact Or.inr (Set.mem_iUnion₂.2 ⟨w, ⟨Or.inl hw.1, hw.2⟩, hyz⟩)
    · exact Or.inr (Set.mem_iUnion₂.2 ⟨z, ⟨Or.inr hzB, hzΩ⟩, hyz⟩)

/-- **The transfer label with the patches as cover cubes** (P3 (4.42), modular form): for patches
`J` with bases aligned to the cells of scale `j + 1`, the transfer label of the family `𝒦 ∪ J` is
the hole closure of the transfer label of `𝒦` and of the patches (the `π'_{j+1}`-cube based at the
coarse base of an aligned patch is the patch). -/
theorem transferLabel_union_patches (hN : L ^ m₀ ∣ N₁) (hj : j + 1 ≤ K)
    (Ω' X 𝒦 : Set (CTorus d L N₁ m₁ K)) {J : Finset (CTorus d L N₁ m₁ K)}
    (hJ : ∀ p ∈ J, Aligned (cellSide L m₀ m₁ (j + 1)) p) :
    transferLabel m₀ j Ω' X (𝒦 ∪ (J : Set (CTorus d L N₁ m₁ K))) =
      holeClose Ω' (transferLabel m₀ j Ω' X 𝒦 ∪
        ⋃ p ∈ J, box p (L * cellSide L m₀ m₁ (j + 1))) := by
  have hdvd := cellSide_dvd (K := K) (m₁ := m₁) hN hj
  have ha0 := cellSide_pos (L := L) m₀ m₁ (j + 1)
  unfold transferLabel
  rw [holeClose_holeClose_union]
  congr 1
  rw [Set.biUnion_union, Set.union_assoc]
  congr 2
  ext x
  simp only [Set.mem_iUnion, Finset.mem_coe]
  refine exists_congr fun p => exists_congr fun hp => ?_
  rw [cbase_eq_of_mem_box hdvd (hJ p hp) (mem_box_self p ha0)]

end Balaban.Fluctuation

namespace Balaban.LargeField

open Balaban

section Region

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M m₀ m₁ : ℕ}
  [NeZero S.L] [NeZero M]

/-- **The cubes of `𝕋_{k+1}` over `Z_k` lie in `Z^pre_{k+1}`**: they lie outside `Ω_{k+1}`
(`RegionHistory.cubeMap_succ_notMem_Omega`; P5 (2.3)), and `Ω_{k+1}^c ⊆ Z^pre_{k+1}`. -/
theorem RegionHistory.cubeIdx_succ_mem_Zpre (F : Def7.FineSizeFrame S n M K m₀ m₁)
    (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) (H : RegionHistory S n R k0 K) {k : ℕ}
    (hk : k + 1 ≤ K) {x : Localization.CTorus S.d S.L F.N₁ m₁ K}
    (hx : cubeIdx F k x ∈ (H.step k).Z) : cubeIdx F (k + 1) x ∈ H.F.Zpre (k + 1) :=
  H.compl_OmegaCube_subset_Zpre (k + 1) (H.cubeMap_succ_notMem_Omega F hnn hk hx)

end Region

end Balaban.LargeField

namespace Balaban.LargeField.Def7

open Balaban Balaban.Localization Balaban.Fluctuation

section Assign

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {M K m₀ m₁ : ℕ} [NeZero S.L]
  (F : FineSizeFrame S n M K m₀ m₁) (hnn : ∀ i, i < K → n i = S.L * n (i + 1))

open Classical in
/-- **The transfer of an old label with mark patches** (P6 p. 34, "to each `Y₁` we assign the
corresponding domain `Y ∈ 𝒟_{k+1}(mod Ω^c_{k+1})` determined as in (4.44) [3]"; P3 (4.42)–(4.44)):
the cubes of `𝕋_{k+1}` of the transfer label (`Fluctuation.transferLabel`) of the fine set of `X`
with the family `𝒦 ∪ J`, that is the hole closure at the new region `Ω'` of the fine set of `X`, of
the `π'_{k+1}`-cubes containing the cubes of the cover `𝒦` and of the patches `J`. -/
noncomputable def transferCubes (k : ℕ) (Om' : Set (Torus S.d (n (k + 1))))
    (X : Finset (Torus S.d (n k))) (𝒦 : Set (Localization.CTorus S.d S.L F.N₁ m₁ K))
    (J : Finset (Localization.CTorus S.d S.L F.N₁ m₁ K)) : Finset (Torus S.d (n (k + 1))) :=
  Finset.univ.filter (· ∈ cubeIdx F (k + 1) '' transferLabel m₀ k (d7Pull F (k + 1) Om')
    (d7Pull F k (X : Set (Torus S.d (n k))))
    (𝒦 ∪ (J : Set (Localization.CTorus S.d S.L F.N₁ m₁ K))))

include hnn in
/-- **The transfer with patches of a class label** (blocker 3 under ruling R11; P6 p. 34; P3
(4.42)–(4.48)).  Let `X` be a valid label at the scale-`k` region `Om`, `(𝒦, W, E)` an admissible
pair of its fine set of cost `d7SizeAt F k Om X` (an optimal cover), and `J` a chain of
`π'_{k+1}`-cubes rooted at the transfer label of `𝒦` in the new region `Om'` (`PatchChain`: each
cube meets the label or an earlier cube there).  Then `Y = transferCubes F k Om' X 𝒦 J` has the
transfer label
of `𝒦 ∪ J` as fine set, contains `X`, is a valid label at `Om'`, has size at most
`L⁻¹ d7SizeAt F k Om X + c_G |J|`, and `J` consists of patches of `Y`. -/
theorem transferCubes_spec {k : ℕ} (hkK : k + 1 ≤ K) {Om : Set (Torus S.d (n k))}
    {Om' : Set (Torus S.d (n (k + 1)))} (hΩ : d7Pull F (k + 1) Om' ⊆ d7Pull F k Om)
    {X : Finset (Torus S.d (n k))} (hX : FineValidAt F k Om X)
    {𝒦 : Set (Localization.CTorus S.d S.L F.N₁ m₁ K)} {W : Finset (Localization.CTorus S.d S.L F.N₁ m₁ K)}
    {E : Finset (Localization.CTorus S.d S.L F.N₁ m₁ K × Localization.CTorus S.d S.L F.N₁ m₁ K)}
    (hA : ModAdmissible m₀ k (d7Pull F k Om) (d7Pull F k (X : Set (Torus S.d (n k)))) 𝒦 W E)
    (hc : bondCost (scaleW S.L m₀ m₁ k) E = d7SizeAt F k Om X)
    {J : Finset (Localization.CTorus S.d S.L F.N₁ m₁ K)}
    (hJ : PatchChain m₀ (k + 1) (transferLabel m₀ k (d7Pull F (k + 1) Om')
      (d7Pull F k (X : Set (Torus S.d (n k)))) 𝒦) (d7Pull F (k + 1) Om') J) :
    d7Pull F (k + 1) (transferCubes F k Om' X 𝒦 J : Set (Torus S.d (n (k + 1)))) =
        transferLabel m₀ k (d7Pull F (k + 1) Om') (d7Pull F k (X : Set (Torus S.d (n k))))
          (𝒦 ∪ (J : Set (Localization.CTorus S.d S.L F.N₁ m₁ K))) ∧
      d7Pull F k (X : Set (Torus S.d (n k))) ⊆
        d7Pull F (k + 1) (transferCubes F k Om' X 𝒦 J : Set (Torus S.d (n (k + 1)))) ∧
      FineValidAt F (k + 1) Om' (transferCubes F k Om' X 𝒦 J) ∧
      d7SizeAt F (k + 1) Om' (transferCubes F k Om' X 𝒦 J) ≤
        (S.L : ℝ)⁻¹ * d7SizeAt F k Om X + cG S.d S.L * J.card ∧
      J ⊆ patchesIn m₀ (k + 1) (d7Pull F (k + 1) Om')
        (d7Pull F (k + 1) (transferCubes F k Om' X 𝒦 J : Set (Torus S.d (n (k + 1))))) := by
  classical
  have hJal : ∀ p ∈ J, Aligned (cellSide S.L m₀ m₁ (k + 1)) p := fun p hp => hJ.aligned hp
  have hcl := cellClosed_transferLabel F hnn hkK Om' hΩ
    (𝒦 := 𝒦 ∪ (J : Set (Localization.CTorus S.d S.L F.N₁ m₁ K)))
    (hA.2.1.trans (Set.biUnion_subset_biUnion_left Set.subset_union_left))
    (fun b hb => hb.elim (fun hb => (hA.1 b hb).1) (fun hb => Localization.aligned_of_dvd
      (by rw [Localization.cellSide_succ]; exact dvd_mul_left _ _) (hJal b hb)))
  have hYT : d7Pull F (k + 1) (transferCubes F k Om' X 𝒦 J : Set (Torus S.d (n (k + 1)))) =
      transferLabel m₀ k (d7Pull F (k + 1) Om') (d7Pull F k (X : Set (Torus S.d (n k))))
        (𝒦 ∪ (J : Set (Localization.CTorus S.d S.L F.N₁ m₁ K))) := by
    unfold transferCubes
    rw [Finset.coe_filter]
    simp only [Finset.mem_univ, true_and, Set.ofPred_mem_eq]
    exact d7Pull_cubeIdx_image F hnn hkK hcl
  have hTU := transferLabel_union_patches F.divN₁ hkK (d7Pull F (k + 1) Om')
    (d7Pull F k (X : Set (Torus S.d (n k)))) 𝒦 hJal
  obtain ⟨hD, hsz⟩ := transfer_patches_chain hΩ hA hX.1 hX.2.1 hJ
  rw [← hTU] at hD hsz
  refine ⟨hYT, hYT ▸ subset_transferLabel _ _ _, ?_, ?_, fun p hp => ?_⟩
  · unfold FineValidAt; rw [hYT]; exact hD
  · have e : d7SizeAt F (k + 1) Om' (transferCubes F k Om' X 𝒦 J) =
        dcovMod m₀ (k + 1) (d7Pull F (k + 1) Om') (transferLabel m₀ k (d7Pull F (k + 1) Om')
          (d7Pull F k (X : Set (Torus S.d (n k))))
          (𝒦 ∪ (J : Set (Localization.CTorus S.d S.L F.N₁ m₁ K)))) := by
      unfold d7SizeAt d7SizeAtE; rw [hYT]; rfl
    rw [e, ← hc]
    exact hsz
  · obtain ⟨z, hzb, hzΩ⟩ := hJ.meets hp
    refine mem_patchesIn.2 ⟨hJ.aligned hp, z, hzb, ?_, hzΩ⟩
    rw [hYT, hTU]
    exact subset_holeClose _ _ (Or.inr (Set.mem_iUnion₂.2 ⟨p, hp, hzb⟩))

open Classical in
/-- **The optimal covers of a label**: the families `𝒦` of the admissible pairs `(𝒦, W, E)` of its
fine set modulo the fine set of `Om` whose cost is the size `d7SizeAt F k Om X` (the chosen covers
attaining `d^cov_k(X mod Ω^c)`, P5 (1.34), FLUCTUATION Definition 1.1).  The average over this
finite set is the covariant choice of the transfer (P6 p. 34; P3 (4.44)). -/
noncomputable def optCovers (k : ℕ) (Om : Set (Torus S.d (n k))) (X : Finset (Torus S.d (n k))) :
    Finset (Set (Localization.CTorus S.d S.L F.N₁ m₁ K)) :=
  Finset.univ.filter fun 𝒦 => ∃ (W : Finset (Localization.CTorus S.d S.L F.N₁ m₁ K))
    (E : Finset (Localization.CTorus S.d S.L F.N₁ m₁ K × Localization.CTorus S.d S.L F.N₁ m₁ K)),
    ModAdmissible m₀ k (d7Pull F k Om) (d7Pull F k (X : Set (Torus S.d (n k)))) 𝒦 W E ∧
      bondCost (scaleW S.L m₀ m₁ k) E = d7SizeAt F k Om X

omit [∀ k, NeZero (n k)] in
theorem mem_optCovers {k : ℕ} {Om : Set (Torus S.d (n k))} {X : Finset (Torus S.d (n k))}
    {𝒦 : Set (Localization.CTorus S.d S.L F.N₁ m₁ K)} :
    𝒦 ∈ optCovers F k Om X ↔ ∃ (W : Finset (Localization.CTorus S.d S.L F.N₁ m₁ K))
      (E : Finset (Localization.CTorus S.d S.L F.N₁ m₁ K × Localization.CTorus S.d S.L F.N₁ m₁ K)),
      ModAdmissible m₀ k (d7Pull F k Om) (d7Pull F k (X : Set (Torus S.d (n k)))) 𝒦 W E ∧
        bondCost (scaleW S.L m₀ m₁ k) E = d7SizeAt F k Om X := by
  classical
  simp [optCovers]

omit [∀ k, NeZero (n k)] in
/-- A valid label has an optimal cover (the infimum of the size is attained). -/
theorem optCovers_nonempty {k : ℕ} {Om : Set (Torus S.d (n k))} {X : Finset (Torus S.d (n k))}
    (hX : FineValidAt F k Om X) : (optCovers F k Om X).Nonempty := by
  obtain ⟨𝒦, W, E, hA, hc⟩ :=
    exists_admissible_eq_dcovMod (exists_admissible_of_ne_top hX.2.2.2)
  exact ⟨𝒦, (mem_optCovers F).2 ⟨W, E, hA, hc⟩⟩

variable {R : ℕ → ℝ} {k0 : ℕ}

/-- The assignments of the old boundary terms: an old label, an optimal cover and a set of patches. -/
abbrev OldAssignIdx (S : Setting) (n : ℕ → ℕ) (k : ℕ) (F : FineSizeFrame S n M K m₀ m₁) : Type :=
  Finset (Torus S.d (n k)) × Set (Localization.CTorus S.d S.L F.N₁ m₁ K) ×
    Finset (Localization.CTorus S.d S.L F.N₁ m₁ K)

open Classical in
/-- **The assignments of the old boundary terms of a history at the step `k → k + 1`** (P6 p. 34,
LFR Lemma IV.1.5 (iii)): the triples `(X, 𝒦, J)` of a boundary domain `X` of the post-`R` class at
scale `k` (`bdryDomsAt` at the region `Ω_k^post`, for `Z_k`) whose fine set meets the fine set of
the new region `Ω_{k+1}`, an optimal cover `𝒦` of `X`, and a chain `J` of patches
(`π'_{k+1}`-cubes with aligned bases, `PatchChain`) rooted at the transfer label of `𝒦` inside
`Ω_{k+1}`. -/
noncomputable def oldAssign (H : RegionHistory S n R k0 K) (k : ℕ) : Finset (OldAssignIdx S n k F) :=
  Finset.univ.filter fun a =>
    a.1 ∈ bdryDomsAt F k (H.omegaPost k) (H.step k).Z ∧
    (d7Pull F k (a.1 : Set (Torus S.d (n k))) ∩ d7Pull F (k + 1) (OmegaCube H (k + 1))).Nonempty ∧
    a.2.1 ∈ optCovers F k (H.omegaPost k) a.1 ∧
    PatchChain m₀ (k + 1) (transferLabel m₀ k (d7Pull F (k + 1) (OmegaCube H (k + 1)))
      (d7Pull F k (a.1 : Set (Torus S.d (n k)))) a.2.1) (d7Pull F (k + 1) (OmegaCube H (k + 1))) a.2.2

/-- **The output label of an assignment**: the transfer of its old label with its optimal cover and
its patches at the new region `Ω_{k+1}` (`transferCubes`). -/
noncomputable def assignOut (H : RegionHistory S n R k0 K) (k : ℕ) (a : OldAssignIdx S n k F) :
    Finset (Torus S.d (n (k + 1))) :=
  transferCubes F k (OmegaCube H (k + 1)) a.1 a.2.1 a.2.2

/-- **The weight of an assignment**: `1 / #(optimal covers of its old label)`, the average over the
optimal covers. -/
noncomputable def assignWt (H : RegionHistory S n R k0 K) (k : ℕ) (a : OldAssignIdx S n k F) : ℝ :=
  ((optCovers F k (H.omegaPost k) a.1).card : ℝ)⁻¹

theorem mem_oldAssign {H : RegionHistory S n R k0 K} {k : ℕ} {a : OldAssignIdx S n k F} :
    a ∈ oldAssign F H k ↔
      a.1 ∈ bdryDomsAt F k (H.omegaPost k) (H.step k).Z ∧
      (d7Pull F k (a.1 : Set (Torus S.d (n k))) ∩ d7Pull F (k + 1) (OmegaCube H (k + 1))).Nonempty ∧
      a.2.1 ∈ optCovers F k (H.omegaPost k) a.1 ∧
      PatchChain m₀ (k + 1) (transferLabel m₀ k (d7Pull F (k + 1) (OmegaCube H (k + 1)))
        (d7Pull F k (a.1 : Set (Torus S.d (n k)))) a.2.1) (d7Pull F (k + 1) (OmegaCube H (k + 1)))
        a.2.2 := by
  classical
  simp [oldAssign]

include hnn in
/-- **The geometry of one assignment** (leaves O2–O4 and the transfer of blocker 3, at one
assignment): for `(X, 𝒦, J) ∈ oldAssign F H k` with output `Y = assignOut F H k (X, 𝒦, J)`:
`X` is valid at `Ω_k^post`, its fine set lies in that of `Y` and meets `Ω_{k+1}`, `J` consists of
patches of `Y`, `Y` is valid at `Ω_{k+1}`, `d_{k+1}(Y) ≤ d_k(X)/L + c_G |J|`, and
`d_k(X) ≥ L (⌊R_k⌋ + 2)`. -/
theorem oldAssign_spec [NeZero M] (H : RegionHistory S n R k0 K) {k : ℕ} (hkK : k + 1 ≤ K)
    {a : OldAssignIdx S n k F} (ha : a ∈ oldAssign F H k) :
    FineValidAt F k (H.omegaPost k) a.1 ∧
      d7Pull F k (a.1 : Set (Torus S.d (n k))) ⊆
        d7Pull F (k + 1) (assignOut F H k a : Set (Torus S.d (n (k + 1)))) ∧
      (d7Pull F k (a.1 : Set (Torus S.d (n k))) ∩ d7Pull F (k + 1) (OmegaCube H (k + 1))).Nonempty ∧
      a.2.2 ⊆ patchesIn m₀ (k + 1) (d7Pull F (k + 1) (OmegaCube H (k + 1)))
        (d7Pull F (k + 1) (assignOut F H k a : Set (Torus S.d (n (k + 1))))) ∧
      FineValidAt F (k + 1) (OmegaCube H (k + 1)) (assignOut F H k a) ∧
      d7SizeAt F (k + 1) (OmegaCube H (k + 1)) (assignOut F H k a) ≤
        d7SizeAt F k (H.omegaPost k) a.1 / S.L + cG S.d S.L * a.2.2.card ∧
      (S.L : ℝ) * (⌊R k⌋₊ + 2) ≤ d7SizeAt F k (H.omegaPost k) a.1 := by
  obtain ⟨hbd, hmeet, hopt, hJ⟩ := (mem_oldAssign F).1 ha
  have hX : FineValidAt F k (H.omegaPost k) a.1 := ((mem_bdryDomsAt).1 hbd).2
  obtain ⟨W, E, hA, hc⟩ := (mem_optCovers F).1 hopt
  obtain ⟨_, hsub, hval, hsize, hpat⟩ := transferCubes_spec F hnn hkK
    (H.d7Pull_OmegaCube_succ_subset F hnn hkK) hX hA hc hJ
  refine ⟨hX, hsub, hmeet, hpat, hval, hsize.trans_eq (by ring), ?_⟩
  exact H.le_d7SizeAt_of_reach F hnn hkK hbd hmeet

/-- **The weights of the assignments sharing an old label and a set of patches add up to at most
`1`** (they differ only by the optimal cover). -/
theorem sum_assignWt_le (H : RegionHistory S n R k0 K) (k : ℕ) (s : Finset (OldAssignIdx S n k F))
    (hs : s ⊆ oldAssign F H k)
    (p : Finset (Torus S.d (n k)) × Finset (Localization.CTorus S.d S.L F.N₁ m₁ K)) :
    ∑ a ∈ s.filter (fun a => (a.1, a.2.2) = p), assignWt F H k a ≤ 1 := by
  classical
  set t := s.filter (fun a => (a.1, a.2.2) = p) with ht
  have hw : ∀ a ∈ t, assignWt F H k a = ((optCovers F k (H.omegaPost k) p.1).card : ℝ)⁻¹ := by
    intro a ha
    have := (Finset.mem_filter.1 ha).2
    unfold assignWt
    rw [show a.1 = p.1 from congrArg Prod.fst this]
  rw [Finset.sum_congr rfl hw, Finset.sum_const, nsmul_eq_mul]
  have hcard : t.card ≤ (optCovers F k (H.omegaPost k) p.1).card := by
    refine Finset.card_le_card_of_injOn (fun a => a.2.1) (fun a ha => ?_) (fun a ha b hb hab => ?_)
    · obtain ⟨has, hap⟩ := Finset.mem_filter.1 ha
      have := ((mem_oldAssign F).1 (hs has)).2.2.1
      rwa [show a.1 = p.1 from congrArg Prod.fst hap] at this
    · obtain ⟨-, hap⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 ha)
      obtain ⟨-, hbp⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hb)
      have h1 : a.1 = b.1 := (congrArg Prod.fst hap).trans (congrArg Prod.fst hbp).symm
      have h2 : a.2.2 = b.2.2 := (congrArg Prod.snd hap).trans (congrArg Prod.snd hbp).symm
      exact Prod.ext h1 (Prod.ext hab h2)
  rcases Nat.eq_zero_or_pos (optCovers F k (H.omegaPost k) p.1).card with h0 | hpos
  · have : t.card = 0 := by omega
    rw [this]; simp
  · rw [← div_eq_mul_inv, div_le_one (by exact_mod_cast hpos)]
    exact_mod_cast hcard

include hnn in
/-- **The bound of the re-expanded old terms of a history at one output label** (LFR Lemma IV.1.5
(iii); P6 (4.32)–(4.34); P3 (4.48)–(4.49)): for every family `T` of coefficients on the assignments
of the history `H` with output `Y` satisfying the re-expansion bound
`‖T a‖ ≤ assignWt · C_re B₀ e^{-κ d_k(X_a)} e^{-κ_m |J_a|}` (the record's bound `B₀ e^{-κ d_k}` of
(D7) times the mark factor, averaged over the optimal covers),
`‖∑_a T a‖ ≤ C_re · assignEnt d L (κ/2 - κ_o/L) (κ_m - κ_o c_G) (d_{k+1}(Y)) · e^{-κ_o d_{k+1}(Y)}`
under the constant conditions `κ/2 - κ_o/L ≥ a_ent + 1` and (Λ28)
`B₀ e^{-(κ/2) L (⌊R_k⌋ + 2)} ≤ 1`.  Everything except the coefficient bound is proved here: the
size transfer and the validity of `Y` (`oldAssign_spec`, ruling R11), the lower bound of the old
sizes (O4), the entropy of the old labels and of the patches (O5) and the weights. -/
theorem norm_sum_oldAssign_fiber_le [NeZero M] (H : RegionHistory S n R k0 K) {k : ℕ}
    (hkK : k + 1 ≤ K) (Y : Finset (Torus S.d (n (k + 1)))) (T : OldAssignIdx S n k F → ℂ)
    {B₀ Cre κ κm κo : ℝ} (hCre : 0 ≤ Cre) (hB₀ : 0 ≤ B₀) (hκo : 0 ≤ κo)
    (hκ : aEnt S.d S.L + 1 ≤ κ / 2 - κo / S.L)
    (hΛ28 : B₀ * Real.exp (-(κ / 2) * ((S.L : ℝ) * (⌊R k⌋₊ + 2))) ≤ 1)
    (hT : ∀ a ∈ (oldAssign F H k).filter (fun a => assignOut F H k a = Y),
      ‖T a‖ ≤ assignWt F H k a * (Cre * B₀ * Real.exp (-κ * d7SizeAt F k (H.omegaPost k) a.1) *
        Real.exp (-κm * a.2.2.card))) :
    ‖∑ a ∈ (oldAssign F H k).filter (fun a => assignOut F H k a = Y), T a‖ ≤
      Cre * assignEnt S.d S.L (κ / 2 - κo / S.L) (κm - κo * cG S.d S.L)
          (d7SizeAt F (k + 1) (OmegaCube H (k + 1)) Y) *
        Real.exp (-κo * d7SizeAt F (k + 1) (OmegaCube H (k + 1)) Y) := by
  classical
  set I := (oldAssign F H k).filter (fun a => assignOut F H k a = Y) with hI
  have hIsub : I ⊆ oldAssign F H k := Finset.filter_subset _ _
  rcases I.eq_empty_or_nonempty with hemp | ⟨a₀, ha₀⟩
  · rw [hemp, Finset.sum_empty, norm_zero]
    have hD := d7SizeAt_nonneg F (k + 1) (OmegaCube H (k + 1)) Y
    have := one_le_c1 S.d S.L
    have := (K0_pos S.d S.L (κ / 2 - κo / S.L)).le
    unfold assignEnt
    have : 0 ≤ 1 + d7SizeAt F (k + 1) (OmegaCube H (k + 1)) Y := by linarith
    positivity
  have hY0 := (Finset.mem_filter.1 ha₀).2
  have hYv : FineValidAt F (k + 1) (OmegaCube H (k + 1)) Y :=
    hY0 ▸ (oldAssign_spec F hnn H hkK (hIsub ha₀)).2.2.2.2.1
  have hkK' : k ≤ K := Nat.le_of_succ_le hkK
  have hinj : Function.Injective fun X : Finset (Torus S.d (n k)) =>
      d7Pull F k (X : Set (Torus S.d (n k))) :=
    (Balaban.LargeField.d7Pull_injective F hnn hkK').comp Finset.coe_injective
  refine norm_sum_oldAssign_le F.divN₁ hkK (d7Pull_isPiUnion F hnn hkK' (H.omegaPost k))
    (d7Pull_isPiUnion F hnn hkK (OmegaCube H (k + 1))) (H.d7Pull_OmegaCube_succ_subset F hnn hkK)
    hYv I T (fun a => d7Pull F k (a.1 : Set (Torus S.d (n k)))) (fun a => a.2.2) (assignWt F H k)
    (fun p hp => ?_) (fun a ha => ?_) (fun a ha => ?_) hCre hB₀ hκo hκ hT
    (fun a ha => (oldAssign_spec F hnn H hkK (hIsub ha)).2.2.2.2.2.2) hΛ28 (fun a ha => ?_)
  · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hp
    have e : I.filter (fun a => (d7Pull F k (a.1 : Set (Torus S.d (n k))), a.2.2) =
        (d7Pull F k (b.1 : Set (Torus S.d (n k))), b.2.2)) =
        I.filter (fun a => (a.1, a.2.2) = (b.1, b.2.2)) := by
      refine Finset.filter_congr fun a _ => ?_
      simp only [Prod.mk.injEq]
      exact and_congr_left fun _ => hinj.eq_iff
    rw [e]
    exact sum_assignWt_le F H k I hIsub (b.1, b.2.2)
  · obtain ⟨h1, h2, h3, -⟩ := oldAssign_spec F hnn H hkK (hIsub ha)
    rw [← (Finset.mem_filter.1 ha).2]
    exact ⟨h1, h2, h3⟩
  · have h := (oldAssign_spec F hnn H hkK (hIsub ha)).2.2.2.1
    rwa [(Finset.mem_filter.1 ha).2] at h
  · have h := (oldAssign_spec F hnn H hkK (hIsub ha)).2.2.2.2.2.1
    rwa [(Finset.mem_filter.1 ha).2] at h

include hnn in
/-- **(O3) The output labels meet `Z^pre_{k+1}`**: the old label meets `Z_k` (it is a boundary
domain of scale `k`), and the cubes of `𝕋_{k+1}` over `Z_k` lie in `Z^pre_{k+1}`
(`RegionHistory.cubeIdx_succ_mem_Zpre`). -/
theorem assignOut_meets_Zpre [NeZero M] (H : RegionHistory S n R k0 K) {k : ℕ}
    (hkK : k + 1 ≤ K) {a : OldAssignIdx S n k F} (ha : a ∈ oldAssign F H k) :
    ((assignOut F H k a : Set (Torus S.d (n (k + 1)))) ∩ H.F.Zpre (k + 1)).Nonempty := by
  obtain ⟨hbd, -⟩ := (mem_oldAssign F).1 ha
  obtain ⟨-, ⟨q, hqX, hqZ⟩, -⟩ := mem_bdryDoms.1 (mem_bdryDomsAt.1 hbd).1
  have hxq : cubeIdx F k (cubeBase F k q) = q := cubeIdx_cubeBase F hnn (Nat.le_of_succ_le hkK) q
  have hxX : cubeBase F k q ∈ d7Pull F k (a.1 : Set (Torus S.d (n k))) := by
    rw [d7Pull_iff, hxq]; exact hqX
  have hxY := (oldAssign_spec F hnn H hkK ha).2.1 hxX
  exact ⟨cubeIdx F (k + 1) (cubeBase F k q), hxY,
    H.cubeIdx_succ_mem_Zpre F hnn hkK (by rw [hxq]; exact hqZ)⟩

include hnn in
/-- **(O3) Which output labels are boundary domains at `k + 1`** (LFR Lemma IV.1.5 (iii)): an output
label is a boundary domain of the pre-`R` class at scale `k + 1` (`bdryDomsAt` at `Ω_{k+1}`, for
`Z^pre_{k+1}`) exactly when it meets the complement of `Z^pre_{k+1}`; it always meets `Z^pre_{k+1}`
(`assignOut_meets_Zpre`) and is valid with a cube-level domain (`oldAssign_spec`,
`FineValidAt.dmodOmega`).  The output labels inside `Z^pre_{k+1}` are not boundary domains: their
terms belong to the large-field region of scale `k + 1` (LFR Lemma IV.1.3, `b_k`). -/
theorem assignOut_mem_bdryDomsAt_iff [NeZero M] (H : RegionHistory S n R k0 K) {k : ℕ}
    (hkK : k + 1 ≤ K) {a : OldAssignIdx S n k F} (ha : a ∈ oldAssign F H k) :
    assignOut F H k a ∈ bdryDomsAt F (k + 1) (OmegaCube H (k + 1)) (H.F.Zpre (k + 1)) ↔
      ((assignOut F H k a : Set (Torus S.d (n (k + 1)))) \ H.F.Zpre (k + 1)).Nonempty := by
  have hv := (oldAssign_spec F hnn H hkK ha).2.2.2.2.1
  constructor
  · intro h
    exact (mem_bdryDoms.1 (mem_bdryDomsAt.1 h).1).2.2
  · intro h
    exact mem_bdryDomsAt.2 ⟨mem_bdryDoms.2 ⟨hv.dmodOmega F hnn hkK,
      assignOut_meets_Zpre F hnn H hkK ha, h⟩, hv⟩

end Assign

end Balaban.LargeField.Def7
