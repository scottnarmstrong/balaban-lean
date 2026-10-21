/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.SizeModEntropy
public import Balaban.Fluctuation.SizeModUnion
public import Balaban.Fluctuation.DjModFin
public import Balaban.Fluctuation.GeneralOldCoeffFamily
public import Balaban.Fluctuation.HatLabelsGeom
public import Balaban.Fluctuation.Thm31Inhab
public import Balaban.Localization.TreeLengthDiam
public import Balaban.LargeField.R.CoarseFineComponents
public import Balaban.LargeField.R.RRawHoleComponent
public import Balaban.LargeField.R.RGasCoreConn
public import Balaban.LargeField.Region.StepMisses
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Old boundary labels across a new hole (blocker 3, row (g2))

LFR Lemma IV.1.5 (iii); P5 (1.33)–(1.34), p. 493, p. 512; P6 p. 34, (4.32)–(4.34); P3 (4.41)–(4.48);
`notes/phase1/astra/ALIGNED.md` rounds 2–3; `notes/phase1/LFROOT3.md`; `notes/phase1/VMOD-44.md`.

**The obstruction.**  An old boundary term `ℬ^{(k)}(X')` whose domain meets `Ω_{k+1}` is re-expanded
by the step and assigned an output label `Y` of scale `k + 1`.  The term depends on the history of
every component of the large-field region that it meets (P5 p. 493; `D7Bdry.loc_hist`), so `Y`
contains `X'` and every component of the new holes `Ω_{k+1}^c` that meets it.  The former labels
(`Fluctuation.DjMod`) are in addition unions of `π'_{k+1}`-cubes at **every**
site, the sites of the holes included.  A new hole need not be such a union: at a seam where two
thick inherited pieces meet diagonally (ALIGNED (23)–(26)) every `π'_{k+1}`-cube through a site of
the hole contains active sites (`spill_of_defect`), so every former label containing the hole
contains active sites along the whole seam, and its size grows linearly with the seam
(`Fluctuation.G1_cellCount`, `R.completion_cellCount_le`).  A coefficient of the class that is
constant in the fields and depends only on the history (ALIGNED (33), LFROOT3 Q2) has no decay to
pay that size.  The same holds for the terms of the fluctuation integral and of the change of
background: their labels are the sets `Ŷ(S)` of finite modular size (FLUCTUATION Theorem 4.2,
`Fluctuation.dOmega`), which are labels of `DjModFin` (`djModFin_Yhat`) and need not be unions of
`π'`-cubes in the holes.

**The change of ruling request R11** (`notes/phase1/PLAN-B.md`): require the `π'`-cube structure
through the active sites only.  `DjModFin` (fine sites) and `Def7.FineValidAt` (class labels):
nonempty, nearest-neighbour connected, containing or missing every component of the holes, of finite
modular size; the finite size already places every active site in a `π'`-cube inside the label
(`DjModFin.exists_box`).  `djMod_iff_djModFin` and `fineValidAt_of_djMod`: the former
class is R11 plus the `π'`-cubes through the sites of the holes, so every former label is an R11
label (`DjMod.djModFin`).  The size `d7SizeAt` is unchanged.

**What is proved.**
* The transfer label (`transferLabel`): the hole closure (`holeClose`) at the new region of the old
  label and of the `π'_{k+1}`-cubes containing the cubes of an admissible cover.  The cover and the
  structure of the old size are admissible for it (`modAdmissible_transferLabel`), so its size is at
  most `L⁻¹` times the old one (`dcovModE_transferLabel_le`, `dcovMod_transferLabel_le`), and it is
  a label of `DjModFin` with no condition on the new holes (`djModFin_transferLabel`).  In the
  landed class it is a label when the new holes it meets are unions of `π'_{k+1}`-cubes
  (`djMod_transferLabel_of_open`).
* `exists_transfer_djModFin` (fine sites) and `Def7.exists_transfer_fineValidAt` (class labels):
  **under R11 the old labels cross the new holes** with `d_{k+1}(Y) ≤ L⁻¹ d_k(X')`; the landed-class
  versions `exists_transfer_djMod_of_open`, `Def7.exists_transfer_djMod_of_open` hold when the
  new holes are unions of `π'_{k+1}`-cubes (the old terms that cross no defect of a new hole).
* Mark patches rooted at active sites (P3 (4.44)–(4.48), modular form): the hole closure is free
  (`modAdmissible_holeClose`) and each patch costs `c_G = 2 d L` (`exists_admissible_union_boxes`,
  `transfer_patches`).
* Two active sites at distance `D` force the size `D / a_j - 2L` (`dcovMod_ge_supDist`): the lower
  bound of LFR Lemma IV.1.5 (iii) that frees the constant of the step from `B₀`.
* The labels of R11 keep the counting and union properties of the landed labels: (G1)
  (`DjModFin.cellCount_le`) and (G3) (`djModFin_union`) with the same constants.
* The fine new region lies in the fine post-`R` region of the same history
  (`RegionHistory.d7Pull_OmegaCube_succ_subset`), the inclusion the transfer needs.
* An old label of the post-`R` class whose fine set meets the new region has size at least
  `L (⌊R_k⌋ + 2)` (`RegionHistory.le_d7SizeAt_of_reach`, through the exit of a hole
  `DmodOmega.exists_active_near`): the lower bound `hmin` of `norm_sum_le_of_transfer`.
* A valid label of R11 is a cube-level domain of `𝒟_k(mod Ω^c)` (`Def7.FineValidAt.dmodOmega`).

**What is not proved here.**  The analytic re-expansion of the old terms (the coefficients of the
assignments and their bounds, P6 (4.32)–(4.34)), and which transferred labels meet `Z^pre_{k+1}` and
its complement (the others go to `b_k`); these are leaves of `Spine/LFBdry.lean`
(`notes/phase1/SPINE.md`, section "LFBdryInput sub-inputs").
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ j : ℕ}

/-- `DjModFin` is inhabited (rule 10): the whole torus. -/
theorem djModFin_univ (Ω : Set (CTorus d L N₁ m₁ K)) : DjModFin m₀ j Ω Set.univ :=
  DjMod.djModFin ⟨isDj_univ d L N₁ m₁ K m₀ j, fun _ _ => Or.inl (Set.subset_univ _)⟩

/-! ### Connectivity -/

omit [NeZero N₁] [NeZero L] in
/-- A set is connected when every site reaches one fixed site inside it. -/
theorem siteConnected_of_reach {X : Set (CTorus d L N₁ m₁ K)} {t : CTorus d L N₁ m₁ K}
    (h : ∀ x ∈ X, Relation.ReflTransGen (fun u v => u ∈ X ∧ v ∈ X ∧ Nbr u v) x t) :
    SiteConnected X := fun x hx y hy =>
  (h x hx).trans (rtg_symm (fun _ _ h => ⟨h.2.1, h.1, h.2.2.symm⟩) (h y hy))

omit [NeZero N₁] [NeZero L] in
/-- **A connected set with connected pieces attached.**  If `A` is connected and every set of the
family `B i` (`i ∈ I`) is connected and meets `A`, the union is connected. -/
theorem siteConnected_union_iUnion {ι : Type*} {A : Set (CTorus d L N₁ m₁ K)}
    {I : Set ι} {B : ι → Set (CTorus d L N₁ m₁ K)} (hA : SiteConnected A)
    (hB : ∀ i ∈ I, SiteConnected (B i)) (hmeet : ∀ i ∈ I, (B i ∩ A).Nonempty)
    {t : CTorus d L N₁ m₁ K} (ht : t ∈ A) :
    SiteConnected (A ∪ ⋃ i ∈ I, B i) := by
  set U := A ∪ ⋃ i ∈ I, B i with hU
  have hAU : A ⊆ U := Set.subset_union_left
  have hBU : ∀ i ∈ I, B i ⊆ U := fun i hi =>
    (Set.subset_biUnion_of_mem (u := B) hi).trans Set.subset_union_right
  have liftA : ∀ x y, Relation.ReflTransGen (fun u v => u ∈ A ∧ v ∈ A ∧ Nbr u v) x y →
      Relation.ReflTransGen (fun u v => u ∈ U ∧ v ∈ U ∧ Nbr u v) x y := fun x y h =>
    Relation.ReflTransGen.mono (fun u v h => ⟨hAU h.1, hAU h.2.1, h.2.2⟩) x y h
  refine siteConnected_of_reach (t := t) fun x hx => ?_
  rcases hx with hx | hx
  · exact liftA x t (hA x hx t ht)
  · obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.1 hx
    obtain ⟨a, haB, haA⟩ := hmeet i hi
    refine Relation.ReflTransGen.trans ?_ (liftA a t (hA a haA t ht))
    exact Relation.ReflTransGen.mono (fun u v h => ⟨hBU i hi h.1, hBU i hi h.2.1, h.2.2⟩) x a
      (hB i hi x hxi a haB)

omit [NeZero N₁] [NeZero L] in
/-- A component of `Ω^c` is connected. -/
theorem siteConnected_omegaComp (Ω : Set (CTorus d L N₁ m₁ K)) (z : CTorus d L N₁ m₁ K) :
    SiteConnected (OmegaComp Ω z) := by
  refine siteConnected_of_reach (t := z) fun x hx => ?_
  have key : ∀ y, Relation.ReflTransGen (fun u v => u ∈ Ωᶜ ∧ v ∈ Ωᶜ ∧ Nbr u v) z y →
      Relation.ReflTransGen (fun u v => u ∈ OmegaComp Ω z ∧ v ∈ OmegaComp Ω z ∧ Nbr u v) z y := by
    intro y hzy
    induction hzy with
    | refl => exact Relation.ReflTransGen.refl
    | tail hab hbc ih => exact ih.tail ⟨⟨hbc.1, hab⟩, ⟨hbc.2.1, hab.tail hbc⟩, hbc.2.2⟩
  exact rtg_symm (fun _ _ h => ⟨h.2.1, h.1, h.2.2.symm⟩) (key x hx.2)

omit [NeZero N₁] [NeZero L] in
/-- A box is connected. -/
theorem siteConnected_box (b : CTorus d L N₁ m₁ K) (s : ℕ) : SiteConnected (box b s) :=
  siteConnected_box_aux b s

/-! ### The hole closure and the transfer label -/

/-- **The hole closure** of a set `S`: `S` together with the components of `Ω^c` that meet it. -/
def holeClose (Ω S : Set (CTorus d L N₁ m₁ K)) : Set (CTorus d L N₁ m₁ K) :=
  S ∪ ⋃ z ∈ S ∩ Ωᶜ, OmegaComp Ω z

omit [NeZero N₁] [NeZero L] in
theorem subset_holeClose (Ω S : Set (CTorus d L N₁ m₁ K)) : S ⊆ holeClose Ω S :=
  Set.subset_union_left

omit [NeZero N₁] [NeZero L] in
/-- The hole closure adds no site of `Ω`. -/
theorem holeClose_inter (Ω S : Set (CTorus d L N₁ m₁ K)) : holeClose Ω S ∩ Ω ⊆ S := by
  rintro y ⟨hy | hy, hyΩ⟩
  · exact hy
  · obtain ⟨z, -, hyz⟩ := Set.mem_iUnion₂.1 hy
    exact absurd hyΩ hyz.1

omit [NeZero N₁] [NeZero L] in
/-- The hole closure contains or misses every component of `Ω^c`. -/
theorem holeClose_comp (Ω S : Set (CTorus d L N₁ m₁ K)) (z : CTorus d L N₁ m₁ K) :
    OmegaComp Ω z ⊆ holeClose Ω S ∨ Disjoint (OmegaComp Ω z) (holeClose Ω S) := by
  by_cases h : (OmegaComp Ω z ∩ holeClose Ω S).Nonempty
  · left
    obtain ⟨y, hyz, hyS⟩ := h
    have e1 : OmegaComp Ω z = OmegaComp Ω y := comp_eq_of_rtg hyz.2
    rcases hyS with hyS | hyS
    · rw [e1]
      exact (Set.subset_biUnion_of_mem (u := OmegaComp Ω) (show y ∈ S ∩ Ωᶜ from ⟨hyS, hyz.1⟩)).trans
        Set.subset_union_right
    · obtain ⟨w, hw, hyw⟩ := Set.mem_iUnion₂.1 hyS
      have e2 : OmegaComp Ω w = OmegaComp Ω y := comp_eq_of_rtg hyw.2
      rw [e1, ← e2]
      exact (Set.subset_biUnion_of_mem (u := OmegaComp Ω) hw).trans Set.subset_union_right
  · right
    exact Set.disjoint_iff_inter_eq_empty.2 (Set.not_nonempty_iff_eq_empty.1 h)

omit [NeZero N₁] [NeZero L] in
/-- The hole closure of a connected set is connected. -/
theorem siteConnected_holeClose {Ω S : Set (CTorus d L N₁ m₁ K)} (hS : SiteConnected S)
    {t : CTorus d L N₁ m₁ K} (ht : t ∈ S) : SiteConnected (holeClose Ω S) :=
  siteConnected_union_iUnion hS (fun z _ => siteConnected_omegaComp Ω z)
    (fun z hz => ⟨z, mem_comp_self hz.2, hz.1⟩) ht

/-- **The transfer label** of a label `X` of scale `j` with a family `𝒦` of `π'_j`-cubes, at the
region `Ω'` of scale `j + 1`: the hole closure at `Ω'` of `X` and of the `π'_{j+1}`-cubes containing
the cubes of `𝒦` (the cube of the coarser grid based at `cbase a_{j+1} b`). -/
def transferLabel (m₀ j : ℕ) (Ω' X 𝒦 : Set (CTorus d L N₁ m₁ K)) : Set (CTorus d L N₁ m₁ K) :=
  holeClose Ω' (X ∪ ⋃ b ∈ 𝒦,
    box (cbase (cellSide L m₀ m₁ (j + 1)) b) (L * cellSide L m₀ m₁ (j + 1)))

/-- A `π'_j`-cube lies in the `π'_{j+1}`-cube based at the coarser base. -/
theorem box_subset_box_cbase_succ {b : CTorus d L N₁ m₁ K} (hb : Aligned (cellSide L m₀ m₁ j) b) :
    box b (L * cellSide L m₀ m₁ j) ⊆
      box (cbase (cellSide L m₀ m₁ (j + 1)) b) (L * cellSide L m₀ m₁ (j + 1)) :=
  box_subset_box_cbase_of_dvd (cellSide_pos m₀ m₁ (j + 1))
    (pow_dvd_pow L (by omega)) (Nat.one_le_iff_ne_zero.2 (NeZero.ne L)) hb

omit [NeZero N₁] [NeZero L] in
theorem subset_transferLabel (Ω' X 𝒦 : Set (CTorus d L N₁ m₁ K)) :
    X ⊆ transferLabel m₀ j Ω' X 𝒦 :=
  Set.subset_union_left.trans (subset_holeClose _ _)

/-- **The scale transfer of an admissible pair.**  Let `(𝒦, W, E)` be admissible for `X` modulo the
scale-`j` region `Ω`, and let `Ω' ⊆ Ω` be the region of scale `j + 1`.  The coarser cubes of `𝒦`
and the same structure `(W, E)` are admissible for the transfer label modulo `Ω'`: the transfer
label adds no site of `Ω'` outside `X` and these cubes, and the hole closure adds sites of `Ω'^c`
only. -/
theorem modAdmissible_transferLabel {Ω Ω' X 𝒦 : Set (CTorus d L N₁ m₁ K)}
    {W : Finset (CTorus d L N₁ m₁ K)} {E : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K)}
    (hΩ : Ω' ⊆ Ω) (h : ModAdmissible m₀ j Ω X 𝒦 W E) :
    ModAdmissible m₀ (j + 1) Ω' (transferLabel m₀ j Ω' X 𝒦)
      (cbase (cellSide L m₀ m₁ (j + 1)) '' 𝒦) W E := by
  obtain ⟨hK, hcov, hconn, hWX, hmeet⟩ := h
  have hbig : ∀ b ∈ 𝒦, box (cbase (cellSide L m₀ m₁ (j + 1)) b) (L * cellSide L m₀ m₁ (j + 1)) ⊆
      transferLabel m₀ j Ω' X 𝒦 := fun b hb =>
    ((Set.subset_biUnion_of_mem (u := fun b =>
      box (cbase (cellSide L m₀ m₁ (j + 1)) b) (L * cellSide L m₀ m₁ (j + 1))) hb).trans
      Set.subset_union_right).trans (subset_holeClose _ _)
  refine ⟨?_, ?_, hconn, hWX.trans (subset_transferLabel Ω' X 𝒦), ?_⟩
  · rintro _ ⟨b, hb, rfl⟩
    exact ⟨aligned_cbase b, hbig b hb⟩
  · intro z hz
    have hzS := holeClose_inter Ω' _ hz
    rcases hzS with hzX | hzB
    · obtain ⟨b, hb, hzb⟩ := Set.mem_iUnion₂.1 (hcov ⟨hzX, hΩ hz.2⟩)
      exact Set.mem_iUnion₂.2 ⟨_, ⟨b, hb, rfl⟩, box_subset_box_cbase_succ (hK b hb).1 hzb⟩
    · obtain ⟨b, hb, hzb⟩ := Set.mem_iUnion₂.1 hzB
      exact Set.mem_iUnion₂.2 ⟨_, ⟨b, hb, rfl⟩, hzb⟩
  · rintro _ ⟨b, hb, rfl⟩
    obtain ⟨x, hx, hxb⟩ := hmeet b hb
    exact ⟨x, hx, box_subset_box_cbase_succ (hK b hb).1 hxb⟩

omit [NeZero N₁] [NeZero L] in
/-- The bond weight of the next scale is `L⁻¹` times the bond weight of the scale. -/
theorem bondCost_scaleW_succ (E : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K)) :
    bondCost (scaleW L m₀ m₁ (j + 1)) E = (L : ℝ)⁻¹ * bondCost (scaleW L m₀ m₁ j) E := by
  unfold bondCost scaleW
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => ?_
  rw [show m₀ + m₁ + (j + 1) = (m₀ + m₁ + j) + 1 by omega, pow_succ, mul_inv, mul_comm]

/-- **The size of the transfer label**: `d^cov_{j+1}(Y mod Ω'^c) ≤ L⁻¹ · cost(E)` for the transfer
label `Y` of an admissible pair `(𝒦, W, E)` of `X` modulo `Ω ⊇ Ω'`. -/
theorem dcovModE_transferLabel_le {Ω Ω' X 𝒦 : Set (CTorus d L N₁ m₁ K)}
    {W : Finset (CTorus d L N₁ m₁ K)} {E : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K)}
    (hΩ : Ω' ⊆ Ω) (h : ModAdmissible m₀ j Ω X 𝒦 W E) :
    dcovModE m₀ (j + 1) Ω' (transferLabel m₀ j Ω' X 𝒦) ≤
      ENNReal.ofReal ((L : ℝ)⁻¹ * bondCost (scaleW L m₀ m₁ j) E) := by
  rw [← bondCost_scaleW_succ]
  exact dcovModE_le_of_admissible (modAdmissible_transferLabel hΩ h)

/-- The real form of `dcovModE_transferLabel_le`. -/
theorem dcovMod_transferLabel_le {Ω Ω' X 𝒦 : Set (CTorus d L N₁ m₁ K)}
    {W : Finset (CTorus d L N₁ m₁ K)} {E : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K)}
    (hΩ : Ω' ⊆ Ω) (h : ModAdmissible m₀ j Ω X 𝒦 W E) :
    dcovMod m₀ (j + 1) Ω' (transferLabel m₀ j Ω' X 𝒦) ≤
      (L : ℝ)⁻¹ * bondCost (scaleW L m₀ m₁ j) E := by
  have hle := ENNReal.toReal_mono ENNReal.ofReal_ne_top (dcovModE_transferLabel_le hΩ h)
  rwa [ENNReal.toReal_ofReal (mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg L))
    (bondCost_scaleW_nonneg E))] at hle

/-- **The transfer label is a label of `DjModFin` at scale `j + 1`** (no condition on the holes):
it is nonempty and connected when `X` is, it contains or misses every component of `Ω'^c` (hole
closure), and its size is finite (`modAdmissible_transferLabel`). -/
theorem djModFin_transferLabel {Ω Ω' X 𝒦 : Set (CTorus d L N₁ m₁ K)}
    {W : Finset (CTorus d L N₁ m₁ K)} {E : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K)}
    (hΩ : Ω' ⊆ Ω) (h : ModAdmissible m₀ j Ω X 𝒦 W E) (hXne : X.Nonempty)
    (hXc : SiteConnected X) :
    DjModFin m₀ (j + 1) Ω' (transferLabel m₀ j Ω' X 𝒦) := by
  obtain ⟨t, ht⟩ := hXne
  refine ⟨⟨t, subset_transferLabel Ω' X 𝒦 ht⟩, ?_, fun z _ => holeClose_comp Ω' _ z,
    dcovModE_ne_top ⟨_, W, E, modAdmissible_transferLabel hΩ h⟩⟩
  refine siteConnected_holeClose (siteConnected_union_iUnion hXc
    (fun b _ => siteConnected_box _ _) (fun b hb => ?_) ht) (Or.inl ht)
  have hb' := h.1 b hb
  refine ⟨b, box_subset_box_cbase_succ hb'.1 (mem_box_self b ?_), hb'.2 (mem_box_self b ?_)⟩ <;>
    exact Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne L)) (cellSide_pos m₀ m₁ j)

/-- **The transfer label in the landed class, when the holes it meets are `π'_{j+1}`-unions.**
If every component of `Ω'^c` meeting `X` or one of the coarser cubes of `𝒦` is a union of
`π'_{j+1}`-cubes (no spill), the transfer label belongs to the landed `𝒟_{j+1}(mod Ω'^c)`. -/
theorem djMod_transferLabel_of_open {Ω Ω' X 𝒦 : Set (CTorus d L N₁ m₁ K)}
    {W : Finset (CTorus d L N₁ m₁ K)} {E : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K)}
    (hΩ : Ω' ⊆ Ω) (h : ModAdmissible m₀ j Ω X 𝒦 W E) (hXne : X.Nonempty)
    (hXc : SiteConnected X)
    (hopen : ∀ z ∈ (X ∪ ⋃ b ∈ 𝒦,
        box (cbase (cellSide L m₀ m₁ (j + 1)) b) (L * cellSide L m₀ m₁ (j + 1))) ∩ Ω'ᶜ,
      IsPiPrimeUnion m₀ (j + 1) (OmegaComp Ω' z)) :
    DjMod m₀ (j + 1) Ω' (transferLabel m₀ j Ω' X 𝒦) := by
  have hF := djModFin_transferLabel hΩ h hXne hXc
  refine djMod_iff_djModFin.2 ⟨hF, fun z hz => ?_⟩
  have hzS := hz.1
  rcases hzS with hzS | hzS
  · exact (hopen z ⟨hzS, hz.2⟩) z (mem_comp_self hz.2) |>.imp fun b hb =>
      ⟨hb.1, hb.2.1, hb.2.2.trans ((Set.subset_biUnion_of_mem (u := OmegaComp Ω')
        (show z ∈ _ ∩ Ω'ᶜ from ⟨hzS, hz.2⟩)).trans Set.subset_union_right)⟩
  · obtain ⟨w, hw, hzw⟩ := Set.mem_iUnion₂.1 hzS
    obtain ⟨b, hb1, hb2, hb3⟩ := hopen w hw z hzw
    exact ⟨b, hb1, hb2, hb3.trans ((Set.subset_biUnion_of_mem (u := OmegaComp Ω') hw).trans
      Set.subset_union_right)⟩

/-- **The transfer of a label across a new hole, with the class of R11** (blocker 3, zero marks).
Let `X` be a label of `DjModFin` at the scale-`j` region `Ω` and `Ω' ⊆ Ω` the region of the next
scale.  There is a label `Y ⊇ X` of `DjModFin` at `Ω'` (it contains every component of `Ω'^c` that
meets `X`) whose size is at most `L⁻¹` times the size of `X`:
`d^cov_{j+1}(Y mod Ω'^c) ≤ L⁻¹ d^cov_j(X mod Ω^c)`.  No condition on the shape of the new holes. -/
theorem exists_transfer_djModFin {Ω Ω' X : Set (CTorus d L N₁ m₁ K)} (hΩ : Ω' ⊆ Ω)
    (hX : DjModFin m₀ j Ω X) :
    ∃ Y, X ⊆ Y ∧ DjModFin m₀ (j + 1) Ω' Y ∧
      dcovMod m₀ (j + 1) Ω' Y ≤ (L : ℝ)⁻¹ * dcovMod m₀ j Ω X := by
  obtain ⟨𝒦, W, E, hA, hc⟩ := exists_admissible_eq_dcovMod (exists_admissible_of_ne_top hX.2.2.2)
  rw [← hc]
  exact ⟨transferLabel m₀ j Ω' X 𝒦, subset_transferLabel Ω' X 𝒦,
    djModFin_transferLabel hΩ hA hX.1 hX.2.1, dcovMod_transferLabel_le hΩ hA⟩

/-- **The same transfer in the landed class, when the new holes are `π'_{j+1}`-unions.**  If every
component of `Ω'^c` is a union of `π'_{j+1}`-cubes, a label of the landed `𝒟_j(mod Ω^c)` has a
transfer label `Y ⊇ X` in the landed `𝒟_{j+1}(mod Ω'^c)` with
`d^cov_{j+1}(Y mod Ω'^c) ≤ L⁻¹ d^cov_j(X mod Ω^c)`.  When a component of `Ω'^c` meeting `Y` is not a
union of `π'_{j+1}`-cubes the landed class forces active sites into `Y` (`spill_of_defect`). -/
theorem exists_transfer_djMod_of_open {Ω Ω' X : Set (CTorus d L N₁ m₁ K)} (hΩ : Ω' ⊆ Ω)
    (hX : DjMod m₀ j Ω X) (hopen : ∀ z ∈ Ω'ᶜ, IsPiPrimeUnion m₀ (j + 1) (OmegaComp Ω' z)) :
    ∃ Y, X ⊆ Y ∧ DjMod m₀ (j + 1) Ω' Y ∧
      dcovMod m₀ (j + 1) Ω' Y ≤ (L : ℝ)⁻¹ * dcovMod m₀ j Ω X := by
  obtain ⟨𝒦, W, E, hA, hc⟩ := exists_admissible_eq_dcovMod (exists_admissible_of_IsDj (Ω := Ω) hX.1)
  rw [← hc]
  exact ⟨transferLabel m₀ j Ω' X 𝒦, subset_transferLabel Ω' X 𝒦,
    djMod_transferLabel_of_open hΩ hA hX.1.1 hX.1.2.2 (fun z hz => hopen z hz.2),
    dcovMod_transferLabel_le hΩ hA⟩

omit [NeZero N₁] [NeZero L] in
/-- **The spill of the landed class at a defect of a hole.**  If every `π'_j`-cube through a site
`p` meets `Ω` (a defect of the hole containing `p`, as on the seam of
`notes/phase1/astra/ALIGNED.md` (23)–(26)), then every union `Y ∋ p` of `π'_j`-cubes contains a
site of `Ω` in a `π'_j`-cube through `p`. -/
theorem spill_of_defect {Ω Y : Set (CTorus d L N₁ m₁ K)} {p : CTorus d L N₁ m₁ K}
    (hdef : ∀ b, Aligned (cellSide L m₀ m₁ j) b → p ∈ box b (L * cellSide L m₀ m₁ j) →
      (box b (L * cellSide L m₀ m₁ j) ∩ Ω).Nonempty)
    (hY : IsPiPrimeUnion m₀ j Y) (hp : p ∈ Y) :
    ∃ b, Aligned (cellSide L m₀ m₁ j) b ∧ p ∈ box b (L * cellSide L m₀ m₁ j) ∧
      (box b (L * cellSide L m₀ m₁ j) ∩ (Y ∩ Ω)).Nonempty := by
  obtain ⟨b, hb, hpb, hbY⟩ := hY p hp
  obtain ⟨q, hqb, hqΩ⟩ := hdef b hb hpb
  exact ⟨b, hb, hpb, q, hqb, hbY hqb, hqΩ⟩

omit [NeZero N₁] [NeZero L] in
/-- **The labels `Ŷ(S)` of the fluctuation step are labels of `DjModFin`.**  For a nonempty set `S`
of sites of `Ω` with `d_Ω(S) < ∞` (the polymers of FLUCTUATION Theorem 4.2 and of the marked
expansion, `dOmega`), `Ŷ(S)` is a label of `DjModFin`.  It need not belong to the landed
`𝒟_j(mod Ω^c)`: the components of `Ω^c` next to `S` need not be unions of `π'_j`-cubes. -/
theorem djModFin_Yhat {Ω S : Set (CTorus d L N₁ m₁ K)} (hS : S ⊆ Ω) (hne : S.Nonempty)
    (h : dOmega m₀ j Ω S ≠ ⊤) : DjModFin m₀ j Ω (Yhat Ω S) := by
  classical
  have hcon : SiteConnected (Yhat Ω S) := by
    by_contra hc
    exact h (by simp [dOmega, hc])
  have hfin : dcovModE m₀ j Ω (Yhat Ω S) ≠ ⊤ := by
    simpa [dOmega, hcon] using h
  refine ⟨hne.mono (subset_Yhat Ω S), hcon, fun z _ => ?_, hfin⟩
  by_cases hm : (OmegaComp Ω z ∩ Yhat Ω S).Nonempty
  · left
    obtain ⟨y, hyz, hyS | ⟨w, hw, hws, hyw⟩⟩ := hm
    · exact absurd (hS hyS) hyz.1
    · have e1 : OmegaComp Ω z = OmegaComp Ω y := comp_eq_of_rtg hyz.2
      have e2 : OmegaComp Ω w = OmegaComp Ω y := comp_eq_of_rtg hyw.2
      rw [e1, ← e2]
      intro u hu
      exact Or.inr ⟨w, hw, hws, hu⟩
  · right
    exact Set.disjoint_iff_inter_eq_empty.2 (Set.not_nonempty_iff_eq_empty.1 hm)

/-! ### Mark patches rooted at active sites -/

omit [NeZero N₁] [NeZero L] in
/-- **The hole closure is free**: an admissible pair of `Z` modulo `Ω` is admissible for the hole
closure of `Z` (the closure adds sites of `Ω^c` only). -/
theorem modAdmissible_holeClose {Ω Z 𝒦 : Set (CTorus d L N₁ m₁ K)}
    {W : Finset (CTorus d L N₁ m₁ K)} {E : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K)}
    (h : ModAdmissible m₀ j Ω Z 𝒦 W E) : ModAdmissible m₀ j Ω (holeClose Ω Z) 𝒦 W E := by
  obtain ⟨hK, hcov, hconn, hWZ, hmeet⟩ := h
  refine ⟨fun b hb => ⟨(hK b hb).1, (hK b hb).2.trans (subset_holeClose Ω Z)⟩, fun z hz => ?_,
    hconn, hWZ.trans (subset_holeClose Ω Z), hmeet⟩
  exact hcov ⟨holeClose_inter Ω Z hz, hz.2⟩

omit [NeZero N₁] in
/-- A `π'_j`-cube alone, with its base point, is admissible modulo any region (cost `0`). -/
theorem modAdmissible_box (Ω : Set (CTorus d L N₁ m₁ K)) {p : CTorus d L N₁ m₁ K}
    (hp : Aligned (cellSide L m₀ m₁ j) p) :
    ModAdmissible m₀ j Ω (box p (L * cellSide L m₀ m₁ j)) {p} {p} ∅ := by
  have hLa : 0 < L * cellSide L m₀ m₁ j :=
    Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne L)) (cellSide_pos m₀ m₁ j)
  refine ⟨fun b hb => ?_, fun z hz => ?_, connStruct_singleton p, ?_, fun b hb => ?_⟩
  · rw [Set.mem_singleton_iff.1 hb]
    exact ⟨hp, subset_rfl⟩
  · exact Set.mem_iUnion₂.2 ⟨p, rfl, hz.1⟩
  · intro x hx
    rw [Finset.coe_singleton, Set.mem_singleton_iff] at hx
    rw [hx]
    exact mem_box_self p hLa
  · rw [Set.mem_singleton_iff.1 hb]
    exact ⟨p, Finset.mem_singleton_self p, mem_box_self p hLa⟩

omit [NeZero N₁] in
/-- **Adding mark patches rooted at active sites** (P3 (4.44)–(4.48), modular form): if every cube
of a finite family `P` of `π'_j`-cubes contains a site of `Y ∩ Ω`, an admissible pair of `Y` modulo
`Ω` extends to the union with these cubes at the extra cost `c_G = 2 d L` per cube. -/
theorem exists_admissible_union_boxes {Ω Y 𝒦 : Set (CTorus d L N₁ m₁ K)}
    {W : Finset (CTorus d L N₁ m₁ K)} {E : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K)}
    (h : ModAdmissible m₀ j Ω Y 𝒦 W E) (P : Finset (CTorus d L N₁ m₁ K))
    (hP : ∀ p ∈ P, Aligned (cellSide L m₀ m₁ j) p ∧
      (box p (L * cellSide L m₀ m₁ j) ∩ (Y ∩ Ω)).Nonempty) :
    ∃ 𝒦' W' E', ModAdmissible m₀ j Ω (Y ∪ ⋃ p ∈ P, box p (L * cellSide L m₀ m₁ j)) 𝒦' W' E' ∧
      bondCost (scaleW L m₀ m₁ j) E' ≤ bondCost (scaleW L m₀ m₁ j) E + cG d L * P.card := by
  classical
  induction P using Finset.induction_on with
  | empty =>
    refine ⟨𝒦, W, E, ?_, by simp⟩
    simpa using h
  | insert p P hpP ih =>
    obtain ⟨𝒦₁, W₁, E₁, h₁, hc₁⟩ := ih fun q hq => hP q (Finset.mem_insert_of_mem hq)
    obtain ⟨hp, t, htp, htY, htΩ⟩ := hP p (Finset.mem_insert_self p P)
    obtain ⟨𝒦₂, W₂, E₂, h₂, hc₂⟩ := exists_union_admissible h₁ (modAdmissible_box Ω hp)
      (Or.inl htY) htp htΩ
    have hset : (Y ∪ ⋃ q ∈ P, box q (L * cellSide L m₀ m₁ j)) ∪ box p (L * cellSide L m₀ m₁ j) =
        Y ∪ ⋃ q ∈ insert p P, box q (L * cellSide L m₀ m₁ j) := by
      rw [Finset.set_biUnion_insert]
      ext x; simp only [Set.mem_union]; tauto
    refine ⟨𝒦₂, W₂, E₂, hset ▸ h₂, ?_⟩
    have h0 : bondCost (scaleW L m₀ m₁ j) (∅ : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K))
        = 0 := by simp [bondCost]
    rw [h0, add_zero] at hc₂
    rw [Finset.card_insert_of_notMem hpP]
    push_cast
    linarith

/-- **The transfer with mark patches, with the class of R11.**  For an admissible pair `(𝒦, W, E)`
of `X` modulo `Ω ⊇ Ω'` and a finite family `P` of `π'_{j+1}`-cubes each containing a site of the
transfer label in `Ω'` (patches rooted at active sites), the hole closure at `Ω'` of the transfer
label and the patches is a label of `DjModFin` at scale `j + 1` (when `X` is nonempty and
connected) of size at most `L⁻¹ cost(E) + c_G |P|`: the bound of P3 (4.48) with modular sizes,
with no term for the holes. -/
theorem transfer_patches {Ω Ω' X 𝒦 : Set (CTorus d L N₁ m₁ K)}
    {W : Finset (CTorus d L N₁ m₁ K)} {E : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K)}
    (hΩ : Ω' ⊆ Ω) (h : ModAdmissible m₀ j Ω X 𝒦 W E) (hXne : X.Nonempty) (hXc : SiteConnected X)
    (P : Finset (CTorus d L N₁ m₁ K))
    (hP : ∀ p ∈ P, Aligned (cellSide L m₀ m₁ (j + 1)) p ∧
      (box p (L * cellSide L m₀ m₁ (j + 1)) ∩ (transferLabel m₀ j Ω' X 𝒦 ∩ Ω')).Nonempty) :
    DjModFin m₀ (j + 1) Ω' (holeClose Ω' (transferLabel m₀ j Ω' X 𝒦 ∪
        ⋃ p ∈ P, box p (L * cellSide L m₀ m₁ (j + 1)))) ∧
      dcovMod m₀ (j + 1) Ω' (holeClose Ω' (transferLabel m₀ j Ω' X 𝒦 ∪
        ⋃ p ∈ P, box p (L * cellSide L m₀ m₁ (j + 1)))) ≤
        (L : ℝ)⁻¹ * bondCost (scaleW L m₀ m₁ j) E + cG d L * P.card := by
  have hT := djModFin_transferLabel hΩ h hXne hXc
  obtain ⟨𝒦', W', E', h', hc'⟩ := exists_admissible_union_boxes (modAdmissible_transferLabel hΩ h)
    P hP
  have hA := modAdmissible_holeClose h'
  obtain ⟨t, ht⟩ := hT.1
  refine ⟨⟨⟨t, subset_holeClose _ _ (Or.inl ht)⟩, siteConnected_holeClose
    (siteConnected_union_iUnion hT.2.1 (fun p _ => siteConnected_box _ _) (fun p hp => ?_) ht)
    (Or.inl ht), fun z _ => holeClose_comp Ω' _ z, dcovModE_ne_top ⟨_, _, _, hA⟩⟩, ?_⟩
  · obtain ⟨u, hu, huT, -⟩ := (hP p hp).2
    exact ⟨u, hu, huT⟩
  · have hle := ENNReal.toReal_mono ENNReal.ofReal_ne_top (dcovModE_le_of_admissible hA)
    rw [ENNReal.toReal_ofReal (bondCost_scaleW_nonneg E')] at hle
    rw [bondCost_scaleW_succ (m₀ := m₀) (j := j) E] at hc'
    exact hle.trans hc'

/-! ### Two active sites far apart force the size -/

section Dist

open Balaban.LargeField (supDist)

/-- **Distance bound for an admissible pair modulo a hole.**  For two sites `y, x` of `X ∩ Ω` and
an admissible pair `(𝒦, W, E)` of `X` modulo `Ω`: `supDist y x ≤ |E| + 2 (L a_j - 1)`. -/
theorem supDist_le_card_add_of_admissible {Ω X 𝒦 : Set (CTorus d L N₁ m₁ K)}
    {W : Finset (CTorus d L N₁ m₁ K)} {E : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K)}
    (h : ModAdmissible m₀ j Ω X 𝒦 W E) {y x : CTorus d L N₁ m₁ K} (hy : y ∈ X ∩ Ω)
    (hx : x ∈ X ∩ Ω) :
    supDist y x ≤ E.card + 2 * (L * cellSide L m₀ m₁ j - 1) := by
  refine supDist_le_card_add m₀ j (X := ⋃ b ∈ 𝒦, box b (L * cellSide L m₀ m₁ j)) (𝒦 := 𝒦)
    ⟨fun b hb => ⟨(h.1 b hb).1, Set.subset_biUnion_of_mem (u := fun b =>
      box b (L * cellSide L m₀ m₁ j)) hb⟩, fun z hz => ?_⟩ h.2.2.1 h.2.2.2.2 (h.2.1 hy) (h.2.1 hx)
  obtain ⟨b, hb, hzb⟩ := Set.mem_iUnion₂.1 hz
  exact ⟨b, hb, hzb⟩

/-- **Size at least the distance between two active sites** (LFR Lemma IV.1.5 (iii)): for a set
`X` of finite size modulo `Ω` and two sites `y, x ∈ X ∩ Ω`,
`supDist y x / a_j - 2 L ≤ d^cov_j(X mod Ω^c)`, `a_j = L^{j + m₀ + m₁}`. -/
theorem dcovMod_ge_supDist {Ω X : Set (CTorus d L N₁ m₁ K)} (hfin : dcovModE m₀ j Ω X ≠ ⊤)
    {y x : CTorus d L N₁ m₁ K} (hy : y ∈ X ∩ Ω) (hx : x ∈ X ∩ Ω) :
    (supDist y x : ℝ) / (L : ℝ) ^ (j + m₀ + m₁) - 2 * L ≤ dcovMod m₀ j Ω X := by
  obtain ⟨𝒦, W, E, hA, hc⟩ := exists_admissible_eq_dcovMod (exists_admissible_of_ne_top hfin)
  rw [← hc]
  have hd := supDist_le_card_add_of_admissible hA hy hx
  have hL : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hpos : (0 : ℝ) < (L : ℝ) ^ (j + m₀ + m₁) := by positivity
  have hcs : ((cellSide L m₀ m₁ j : ℕ) : ℝ) = (L : ℝ) ^ (j + m₀ + m₁) := by
    unfold cellSide; push_cast; rfl
  have hs : 1 ≤ L * cellSide L m₀ m₁ j :=
    Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne L)) (cellSide_pos m₀ m₁ j)
  have hd' : (supDist y x : ℝ) ≤ E.card + 2 * (L * (L : ℝ) ^ (j + m₀ + m₁)) := by
    have : ((supDist y x : ℕ) : ℝ) ≤ ((E.card + 2 * (L * cellSide L m₀ m₁ j - 1) : ℕ) : ℝ) := by
      exact_mod_cast hd
    have e : ((L * cellSide L m₀ m₁ j - 1 : ℕ) : ℝ) ≤ L * (L : ℝ) ^ (j + m₀ + m₁) := by
      rw [Nat.cast_sub hs]; push_cast; rw [hcs]; linarith
    push_cast at this
    linarith
  have hcost : bondCost (scaleW L m₀ m₁ j) E = E.card / (L : ℝ) ^ (j + m₀ + m₁) := by
    unfold bondCost scaleW
    rw [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv,
      show m₀ + m₁ + j = j + m₀ + m₁ by omega]
  rw [hcost, div_sub' (ne_of_gt hpos), div_le_div_iff_of_pos_right hpos]
  nlinarith

end Dist

end Balaban.Fluctuation


/-!
### The class labels of scale `k` and `k + 1`
-/

namespace Balaban.LargeField.Def7

open Balaban Balaban.Localization Balaban.Fluctuation

section Cube

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {M K m₀ m₁ : ℕ} [NeZero S.L]

variable (F : FineSizeFrame S n M K m₀ m₁) (hnn : ∀ i, i < K → n i = S.L * n (i + 1))

include hnn in
/-- **A union of cells is a fine lift.**  A set `Y` of fine sites that contains the cell of each of
its sites is the fine lift of the cubes of `𝕋_k` of its sites. -/
theorem d7Pull_cubeIdx_image {k : ℕ} (hkK : k ≤ K)
    {Y : Set (Localization.CTorus S.d S.L F.N₁ m₁ K)}
    (hY : ∀ y ∈ Y, Localization.box (cbase (cellSide S.L m₀ m₁ k) y) (cellSide S.L m₀ m₁ k) ⊆ Y) :
    d7Pull F k (cubeIdx F k '' Y) = Y := by
  ext x
  rw [d7Pull_iff]
  constructor
  · rintro ⟨y, hy, hxy⟩
    have hb : cbase (cellSide S.L m₀ m₁ k) x = cbase (cellSide S.L m₀ m₁ k) y :=
      cubeIdx_injOn F hnn hkK (aligned_cbase x) (aligned_cbase y) (by
        rw [cubeIdx_cbase F hnn hkK, cubeIdx_cbase F hnn hkK, hxy])
    exact hY y hy (hb ▸ mem_box_cbase (cellSide_pos m₀ m₁ k) x)
  · intro hx
    exact ⟨x, hx, rfl⟩

include hnn in
/-- **The transfer label is a union of cells of scale `j + 1`** when the region `Ω'` is the fine
lift of a set of cubes of `𝕋_{j+1}`. -/
theorem cellClosed_transferLabel {j : ℕ} (hjK : j + 1 ≤ K) (Om' : Set (Torus S.d (n (j + 1))))
    {X 𝒦 Ω : Set (Localization.CTorus S.d S.L F.N₁ m₁ K)} (hΩ : d7Pull F (j + 1) Om' ⊆ Ω)
    (hcov : X ∩ Ω ⊆ ⋃ b ∈ 𝒦, Localization.box b (S.L * cellSide S.L m₀ m₁ j))
    (hK : ∀ b ∈ 𝒦, Aligned (cellSide S.L m₀ m₁ j) b) :
    ∀ y ∈ transferLabel m₀ j (d7Pull F (j + 1) Om') X 𝒦,
      Localization.box (cbase (cellSide S.L m₀ m₁ (j + 1)) y) (cellSide S.L m₀ m₁ (j + 1)) ⊆
        transferLabel m₀ j (d7Pull F (j + 1) Om') X 𝒦 := by
  set Ω' := d7Pull F (j + 1) Om' with hΩ'
  set a := cellSide S.L m₀ m₁ (j + 1) with ha
  have hN := F.divN₁
  have hdvd : a ∣ (F.N₁ * S.L ^ m₁) * S.L ^ K := cellSide_dvd (K := K) (m₁ := m₁) hN hjK
  have ha0 : 0 < a := cellSide_pos m₀ m₁ (j + 1)
  have hΩu : IsPiUnion m₀ (j + 1) Ω' := d7Pull_isPiUnion F hnn hjK Om'
  set T := transferLabel m₀ j Ω' X 𝒦 with hT
  -- the cell of a site of a coarser cube of `𝒦`
  have hbig : ∀ b ∈ 𝒦, ∀ y ∈ Localization.box (cbase a b) (S.L * a),
      Localization.box (cbase a y) a ⊆ T := by
    intro b hb y hy
    refine (cell_subset_cube hdvd ha0 (aligned_cbase b) hy).trans ?_
    exact ((Set.subset_biUnion_of_mem
      (u := fun b => Localization.box (cbase a b) (S.L * a)) hb).trans
      Set.subset_union_right).trans (subset_holeClose _ _)
  -- the cell of a site of a component of `Ω'^c` contained in `T`
  have hhole : ∀ y, y ∈ Ω'ᶜ → OmegaComp Ω' y ⊆ T → Localization.box (cbase a y) a ⊆ T := by
    intro y hy hcomp
    have hcell : Localization.box (cbase a y) a ⊆ Ω'ᶜ := by
      rcases cell_dichotomy hN hjK hΩu (aligned_cbase y) with h | h
      · exact absurd (h (mem_box_cbase ha0 y)) hy
      · exact h
    intro u hu
    exact hcomp ⟨hcell hu, rtg_box_compl hcell (mem_box_cbase ha0 y) hu⟩
  have hcompT : ∀ y ∈ (X ∪ ⋃ b ∈ 𝒦, Localization.box (cbase a b) (S.L * a)) ∩ Ω'ᶜ,
      OmegaComp Ω' y ⊆ T :=
    fun y hy => (Set.subset_biUnion_of_mem (u := OmegaComp Ω') hy).trans Set.subset_union_right
  intro y hy
  rcases hy with hyS | hyC
  · by_cases hyΩ : y ∈ Ω'
    · rcases hyS with hyX | hyB
      · obtain ⟨b, hb, hyb⟩ := Set.mem_iUnion₂.1 (hcov ⟨hyX, hΩ hyΩ⟩)
        exact hbig b hb y (box_subset_box_cbase_succ (hK b hb) hyb)
      · obtain ⟨b, hb, hyb⟩ := Set.mem_iUnion₂.1 hyB
        exact hbig b hb y hyb
    · exact hhole y hyΩ (hcompT y ⟨hyS, hyΩ⟩)
  · obtain ⟨w, hw, hyw⟩ := Set.mem_iUnion₂.1 hyC
    have e : OmegaComp Ω' y = OmegaComp Ω' w := (comp_eq_of_rtg hyw.2).symm
    exact hhole y hyw.1 (e ▸ hcompT w hw)

include hnn in
/-- **The transfer label of a class label is the fine set of a set of cubes of `𝕋_{k+1}`**, of size
at most `L⁻¹` times the cost of the admissible pair it is built from. -/
theorem exists_cube_transferLabel {k : ℕ} (hkK : k + 1 ≤ K) {Om : Set (Torus S.d (n k))}
    {Om' : Set (Torus S.d (n (k + 1)))} (hΩ : d7Pull F (k + 1) Om' ⊆ d7Pull F k Om)
    {X : Finset (Torus S.d (n k))} {𝒦 : Set (Localization.CTorus S.d S.L F.N₁ m₁ K)}
    {W : Finset (Localization.CTorus S.d S.L F.N₁ m₁ K)}
    {E : Finset (Localization.CTorus S.d S.L F.N₁ m₁ K × Localization.CTorus S.d S.L F.N₁ m₁ K)}
    (hA : ModAdmissible m₀ k (d7Pull F k Om) (d7Pull F k (X : Set (Torus S.d (n k)))) 𝒦 W E) :
    ∃ Y : Finset (Torus S.d (n (k + 1))),
      d7Pull F (k + 1) (Y : Set (Torus S.d (n (k + 1)))) =
        transferLabel m₀ k (d7Pull F (k + 1) Om') (d7Pull F k (X : Set (Torus S.d (n k)))) 𝒦 ∧
      d7SizeAt F (k + 1) Om' Y ≤ (S.L : ℝ)⁻¹ * bondCost (scaleW S.L m₀ m₁ k) E := by
  classical
  have hcl := cellClosed_transferLabel F hnn hkK Om' hΩ hA.2.1 fun b hb => (hA.1 b hb).1
  have hYT : d7Pull F (k + 1) ((Finset.univ.filter (· ∈ cubeIdx F (k + 1) ''
      transferLabel m₀ k (d7Pull F (k + 1) Om') (d7Pull F k (X : Set (Torus S.d (n k)))) 𝒦) :
        Finset (Torus S.d (n (k + 1)))) : Set (Torus S.d (n (k + 1)))) =
      transferLabel m₀ k (d7Pull F (k + 1) Om') (d7Pull F k (X : Set (Torus S.d (n k)))) 𝒦 := by
    rw [Finset.coe_filter]
    simp only [Finset.mem_univ, true_and, Set.ofPred_mem_eq]
    exact d7Pull_cubeIdx_image F hnn hkK hcl
  refine ⟨_, hYT, ?_⟩
  unfold d7SizeAt d7SizeAtE
  rw [hYT]
  exact dcovMod_transferLabel_le hΩ hA

include hnn in
/-- **The transfer of a class label across a new hole, with the labels of R11** (blocker 3, zero
marks; LFR Lemma IV.1.5 (iii), P6 p. 34).  Let `X` be a valid label of R11 at the scale-`k` region
`Om` (in particular a label of the former class, `fineValidAt_of_djMod`), and let `Om'`
be the region of scale `k + 1` with fine set inside that of `Om`.  There is a set `Y` of cubes of
`𝕋_{k+1}` whose fine set contains the fine set of `X` (and every component of the new holes that
meets it), that is a valid label of R11 at `Om'`, with
`d7SizeAt F (k + 1) Om' Y ≤ L⁻¹ d7SizeAt F k Om X`.  No condition on the shape of the new holes:
the seam of `notes/phase1/astra/ALIGNED.md` (23)–(26), which forces active sites into every label
of the landed class (`Balaban.Fluctuation.spill_of_defect`), costs nothing here. -/
theorem exists_transfer_fineValidAt {k : ℕ} (hkK : k + 1 ≤ K) {Om : Set (Torus S.d (n k))}
    {Om' : Set (Torus S.d (n (k + 1)))} (hΩ : d7Pull F (k + 1) Om' ⊆ d7Pull F k Om)
    {X : Finset (Torus S.d (n k))} (hX : FineValidAt F k Om X) :
    ∃ Y : Finset (Torus S.d (n (k + 1))),
      d7Pull F k (X : Set (Torus S.d (n k))) ⊆ d7Pull F (k + 1) (Y : Set (Torus S.d (n (k + 1)))) ∧
      FineValidAt F (k + 1) Om' Y ∧
      d7SizeAt F (k + 1) Om' Y ≤ (S.L : ℝ)⁻¹ * d7SizeAt F k Om X := by
  obtain ⟨𝒦, W, E, hA, hc⟩ := exists_admissible_eq_dcovMod (exists_admissible_of_ne_top hX.2.2.2)
  obtain ⟨Y, hYT, hsize⟩ := exists_cube_transferLabel F hnn hkK hΩ hA
  refine ⟨Y, hYT ▸ subset_transferLabel _ _ _, ?_, hsize.trans_eq (by rw [hc]; rfl)⟩
  unfold FineValidAt
  rw [hYT]
  exact djModFin_transferLabel hΩ hA hX.1 hX.2.1

include hnn in
/-- **The same transfer in the former class, for new holes that are unions of `π'_{k+1}`-cubes.**
If every component of the complement of the fine set of `Om'` is a union of `π'_{k+1}`-cubes, a
label `X` of the former class `Fluctuation.DjMod` at `Om` has a transfer `Y` in the former class at
`Om'`, with `d7SizeAt F (k + 1) Om' Y ≤ L⁻¹ d7SizeAt F k Om X`.  This is the transfer of the old
terms that cross no defect of a new hole; for the other holes the labels of R11 are needed. -/
theorem exists_transfer_djMod_of_open {k : ℕ} (hkK : k + 1 ≤ K) {Om : Set (Torus S.d (n k))}
    {Om' : Set (Torus S.d (n (k + 1)))} (hΩ : d7Pull F (k + 1) Om' ⊆ d7Pull F k Om)
    (hopen : ∀ z ∈ (d7Pull F (k + 1) Om')ᶜ,
      IsPiPrimeUnion m₀ (k + 1) (OmegaComp (d7Pull F (k + 1) Om') z))
    {X : Finset (Torus S.d (n k))}
    (hXd : DjMod m₀ k (d7Pull F k Om) (d7Pull F k (X : Set (Torus S.d (n k))))) :
    ∃ Y : Finset (Torus S.d (n (k + 1))),
      d7Pull F k (X : Set (Torus S.d (n k))) ⊆ d7Pull F (k + 1) (Y : Set (Torus S.d (n (k + 1)))) ∧
      DjMod m₀ (k + 1) (d7Pull F (k + 1) Om') (d7Pull F (k + 1) (Y : Set (Torus S.d (n (k + 1))))) ∧
      d7SizeAt F (k + 1) Om' Y ≤ (S.L : ℝ)⁻¹ * d7SizeAt F k Om X := by
  obtain ⟨𝒦, W, E, hA, hc⟩ := exists_admissible_eq_dcovMod (exists_admissible_of_IsDj
    (Ω := d7Pull F k Om) hXd.1)
  obtain ⟨Y, hYT, hsize⟩ := exists_cube_transferLabel F hnn hkK hΩ hA
  refine ⟨Y, hYT ▸ subset_transferLabel _ _ _, ?_, hsize.trans_eq (by rw [hc]; rfl)⟩
  rw [hYT]
  exact djMod_transferLabel_of_open hΩ hA hXd.1.1 hXd.1.2.2 fun z hz => hopen z hz.2

include hnn in
/-- **A valid label of R11 is a domain of `𝒟_k(mod Ω^c)` at cube level** (`DmodOmega`, the
condition of `bdryDoms`): its cubes are nearest-neighbour connected (`isDomain_iff_siteConnected`)
and it contains or misses every nearest-neighbour component of the cube complement
(`omegaComp_preimage`).  For the transfer label this is the cube-level part of leaf O3. -/
theorem FineValidAt.dmodOmega {k : ℕ} (hkK : k ≤ K) {Om : Set (Torus S.d (n k))}
    {Y : Finset (Torus S.d (n k))} (h : FineValidAt F k Om Y) : DmodOmega Om Y := by
  have : NeZero (cellSide S.L m₀ m₁ k) := ⟨(cellSide_pos m₀ m₁ k).ne'⟩
  have hN := fine_side_eq F hnn hkK
  unfold FineValidAt at h
  rw [d7Pull_eq_preimage_siteCube, d7Pull_eq_preimage_siteCube] at h
  refine ⟨(isDomain_iff_siteConnected hN Y).2 ⟨h.1, h.2.1⟩, fun c hc => ?_⟩
  obtain ⟨z, rfl⟩ := siteCube_surj' (N := (F.N₁ * S.L ^ m₁) * S.L ^ K) hN c
  have := h.2.2.1 z hc
  rwa [omegaComp_preimage hN Om z hc, preimage_subset_iff hN, preimage_disjoint_iff hN] at this

end Cube

end Balaban.LargeField.Def7

/-!
### The new region lies in the old post-`R` region
-/

namespace Balaban.LargeField

open Balaban

section Region

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}

/-- The complement of the raw region `Ω_k` lies in `Z^pre_k` (LFR Lemma I.3.5 (e)). -/
theorem RegionHistory.compl_OmegaCube_subset_Zpre (H : RegionHistory S n R k0 K) (k : ℕ) :
    (Def7.OmegaCube H k)ᶜ ⊆ H.F.Zpre k := by
  cases k with
  | zero => intro x hx; exact absurd (Set.mem_univ x) hx
  | succ j => exact (H.step j).Omega_compl_subset_Z0.trans ((H.step j).Z0_subset_Zpre _ _)

/-- The complement of the post-`R` region `Ω_k^post` lies in `Z_k = Z^pre_k ∖ ⋃ Rem_k`. -/
theorem RegionHistory.compl_omegaPost_subset_Z (H : RegionHistory S n R k0 K) (k : ℕ) :
    (H.omegaPost k)ᶜ ⊆ (H.step k).Z := by
  intro x hx
  rw [H.Z_eq]
  exact ⟨H.compl_OmegaCube_subset_Zpre k fun h => hx (Or.inl h), fun h => hx (Or.inr h)⟩

variable {M m₀ m₁ : ℕ} [NeZero S.L] [NeZero M]

/-- **The new region misses the large-field region of the previous scale** (P5 (2.3): the opening
of scale `k + 1` misses the coarsening `U'_k` of `Z_k`; LFR Lemma I.3.5 (e)): a fine site whose cube
of `𝕋_k` lies in `Z_k` has its cube of `𝕋_{k+1}` outside `Ω_{k+1}`. -/
theorem RegionHistory.cubeMap_succ_notMem_Omega (F : Def7.FineSizeFrame S n M K m₀ m₁)
    (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) (H : RegionHistory S n R k0 K) {k : ℕ}
    (hk : k + 1 ≤ K) {x : Localization.CTorus S.d S.L F.N₁ m₁ K}
    (hx : cubeMap n S.L M K k (Localization.castT F.side x) ∈ (H.step k).Z) :
    cubeMap n S.L M K (k + 1) (Localization.castT F.side x) ∉ (H.step k).Omega := by
  rw [← cubeMap_succ hnn hk]
  exact (H.step k).blockMap_notMem_Omega hx

/-- **The fine new region lies in the fine post-`R` region** (the inclusion `Ω' ⊆ Ω` of the
transfer of `Def7.exists_transfer_fineValidAt`; P5 (2.3): the opening of scale `k + 1` misses
the coarsening `U'_k` of `Z_k`, and `(Ω_k^post)^c ⊆ Z_k`). -/
theorem RegionHistory.d7Pull_OmegaCube_succ_subset (F : Def7.FineSizeFrame S n M K m₀ m₁)
    (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) (H : RegionHistory S n R k0 K) {k : ℕ}
    (hk : k + 1 ≤ K) :
    Def7.d7Pull F (k + 1) (Def7.OmegaCube H (k + 1)) ⊆ Def7.d7Pull F k (H.omegaPost k) := by
  intro x hx
  rw [Def7.mem_d7Pull] at hx ⊢
  by_contra hy
  exact H.cubeMap_succ_notMem_Omega F hnn hk (H.compl_omegaPost_subset_Z k hy) hx

end Region

/-!
### An old label that reaches the new region is long (LFR Lemma IV.1.5 (iii))
-/

section Exit

variable {d n : ℕ} [NeZero n]

/-- **The exit of a hole.**  If a domain `X` of `𝒟(mod Ω^c)` meets a set `Z ⊇ Ω^c` and its
complement, it has a cube of `Ω` within distance `1` of `Z`. -/
theorem DmodOmega.exists_active_near {Ω Z : Set (Torus d n)} {X : Finset (Torus d n)}
    (hX : DmodOmega Ω X) (hΩZ : Ωᶜ ⊆ Z) (hXZ : ((X : Set (Torus d n)) ∩ Z).Nonempty)
    (hXZc : ((X : Set (Torus d n)) \ Z).Nonempty) :
    ∃ u ∈ X, u ∈ Ω ∧ u ∈ nbhd 1 Z := by
  obtain ⟨c, hcX, hcZ⟩ := hXZ
  by_cases hcΩ : c ∈ Ω
  · exact ⟨c, hcX, hcΩ, subset_nbhd 1 Z hcZ⟩
  obtain ⟨e, heX, heZ⟩ := hXZc
  have hpath := hX.1.2 c hcX e heX
  -- the first cube of the path outside the component of `c` in `Ω^c`
  suffices key : ∀ y, Relation.ReflTransGen
      (fun a b => a ∈ (X : Set (Torus d n)) ∧ b ∈ (X : Set (Torus d n)) ∧ NNAdj a b) c y →
      y ∉ nnComp Ωᶜ c → ∃ u ∈ X, u ∈ Ω ∧ u ∈ nbhd 1 Z by
    refine key e hpath fun he => heZ (hΩZ (nnComp_subset _ he))
  intro y hy
  induction hy with
  | refl => exact fun h => (h (mem_nnComp_self hcΩ)).elim
  | @tail a b hca hab ih =>
    intro hb
    by_cases ha : a ∈ nnComp Ωᶜ c
    · have hbΩ : b ∈ Ω := by
        by_contra hbΩ
        exact hb ⟨hbΩ, ha.2.tail ⟨ha.1, hbΩ, hab.2.2⟩⟩
      refine ⟨b, hab.2.1, hbΩ, mem_nbhd.2 ⟨a, hΩZ ha.1, ?_⟩⟩
      rw [supDist_comm]
      exact NNAdj.supDist_le_one hab.2.2
    · exact ih ha

end Exit

section Size

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M m₀ m₁ : ℕ}
  [NeZero S.L] [NeZero M]

omit [∀ k, NeZero (n k)] [NeZero S.L] [NeZero M] in
/-- The cast between two tori of equal side preserves the distance. -/
theorem supDist_castT {d N N' : ℕ} (h : N = N') (x y : Torus d N) :
    supDist (Localization.castT h x) (Localization.castT h y) = supDist x y := by
  subst h; rfl

/-- **An old label that reaches the new region is long** (LFR Lemma IV.1.5 (iii)).  A boundary
domain `X` of the post-`R` class at scale `k` (it meets `Z_k` and its complement) whose fine set
meets the fine set of the new region `Ω_{k+1}` has size at least `L (⌊R_k⌋ + 2)`: it has a cube of
`Ω_k^post` next to `Z_k` (`DmodOmega.exists_active_near`), the new region lies at distance
`⌊R_k⌋ + 5` from the coarsening of `Z_k` (P5 (2.3)), and two active sites at that distance force
the size (`Fluctuation.dcovMod_ge_supDist`).  With `B₀ e^{-(κ/2) L (⌊R_k⌋+2)} ≤ 1` this frees the
constant of the re-expanded old terms from `B₀`. -/
theorem RegionHistory.le_d7SizeAt_of_reach (F : Def7.FineSizeFrame S n M K m₀ m₁)
    (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) (H : RegionHistory S n R k0 K) {k : ℕ}
    (hk : k + 1 ≤ K) {X : Finset (Torus S.d (n k))}
    (hX : X ∈ Def7.bdryDomsAt F k (H.omegaPost k) (H.step k).Z)
    (hmeet : (Def7.d7Pull F k (X : Set (Torus S.d (n k))) ∩
      Def7.d7Pull F (k + 1) (Def7.OmegaCube H (k + 1))).Nonempty) :
    (S.L : ℝ) * (⌊R k⌋₊ + 2) ≤ Def7.d7SizeAt F k (H.omegaPost k) X := by
  have hkK : k ≤ K := by omega
  rw [Def7.mem_bdryDomsAt, Def7.mem_bdryDoms] at hX
  obtain ⟨⟨hD, hXZ, hXZc⟩, hv⟩ := hX
  obtain ⟨u, huX, huΩ, huZ⟩ := hD.exists_active_near (H.compl_omegaPost_subset_Z k) hXZ hXZc
  obtain ⟨x, hxX, hxΩ'⟩ := hmeet
  set y := cubeBase F k u with hy
  have hyu : cubeIdx F k y = u := cubeIdx_cubeBase F hnn hkK u
  have hyX : y ∈ Def7.d7Pull F k (X : Set (Torus S.d (n k))) := by
    rw [d7Pull_iff, hyu]; exact huX
  have hyΩ : y ∈ Def7.d7Pull F k (H.omegaPost k) := by rw [d7Pull_iff, hyu]; exact huΩ
  have hxΩ : x ∈ Def7.d7Pull F k (H.omegaPost k) := H.d7Pull_OmegaCube_succ_subset F hnn hk hxΩ'
  have hge := Fluctuation.dcovMod_ge_supDist hv.2.2.2 ⟨hyX, hyΩ⟩ ⟨hxX, hxΩ⟩
  -- the distance of the two sites
  set ρ := ⌊R k⌋₊ with hρ
  set a := S.L ^ (k + 1) * M with ha
  have hapos : 0 < a := Nat.mul_pos (pow_pos (Nat.pos_of_ne_zero (NeZero.ne S.L)) _)
    (Nat.pos_of_ne_zero (NeZero.ne M))
  have hU : blockMap S.L (n (k + 1)) u ∈ (H.step k).Uprime :=
    ⟨u, nbhd_mono (by omega) le_rfl huZ, rfl⟩
  have hcx : cubeMap n S.L M K (k + 1) (Localization.castT F.side x) ∈ (H.step k).Omega := hxΩ'
  have hcy : cubeMap n S.L M K (k + 1) (Localization.castT F.side y) =
      blockMap S.L (n (k + 1)) u := by
    rw [← cubeMap_succ hnn hk]
    exact congrArg _ hyu
  have hfar : ρ + 5 ≤ supDist (cubeMap n S.L M K (k + 1) (Localization.castT F.side x))
      (cubeMap n S.L M K (k + 1) (Localization.castT F.side y)) := by
    by_contra hlt
    have hin : cubeMap n S.L M K (k + 1) (Localization.castT F.side x) ∈
        nbhd (ρ + 4) (H.step k).Uprime := by
      rw [mem_nbhd]
      exact ⟨_, hU, by rw [← hcy]; omega⟩
    exact Region.nbhd_subset_compl_OmegaPrime S.L ρ _ hin
      ((H.step k).Omega_subset_OmegaPrime hcx)
  have hbl := supDist_blockMap_le (L := a) (m := n (k + 1)) (fine_eq hnn hk)
    (Localization.castT F.side x) (Localization.castT F.side y)
  have hd : a * (ρ + 4) + 1 ≤ supDist x y := by
    rw [supDist_castT] at hbl
    have h1 : ρ + 5 ≤ (supDist x y + a - 1) / a := hfar.trans hbl
    have h2 := (Nat.le_div_iff_mul_le hapos).1 h1
    have : a * (ρ + 4) + a = (ρ + 5) * a := by ring
    omega
  -- the arithmetic
  have hLpos : (0 : ℝ) < (S.L : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne S.L)
  have hp : (0 : ℝ) < (S.L : ℝ) ^ (k + m₀ + m₁) := by positivity
  have hae : ((a : ℕ) : ℝ) = (S.L : ℝ) * (S.L : ℝ) ^ (k + m₀ + m₁) := by
    rw [ha, F.hM]; push_cast; ring
  have hd' : ((a : ℝ)) * (ρ + 4) ≤ (supDist x y : ℝ) := by
    have : ((a * (ρ + 4) : ℕ) : ℝ) ≤ (supDist x y : ℝ) := by exact_mod_cast (Nat.le_succ _).trans hd
    push_cast at this
    exact this
  rw [hae] at hd'
  have hq : (S.L : ℝ) * (ρ + 4) ≤ (supDist x y : ℝ) / (S.L : ℝ) ^ (k + m₀ + m₁) := by
    rw [le_div_iff₀ hp]; nlinarith
  rw [supDist_comm] at hge
  have : Def7.d7SizeAt F k (H.omegaPost k) X =
      Fluctuation.dcovMod m₀ k (Def7.d7Pull F k (H.omegaPost k))
        (Def7.d7Pull F k (X : Set (Torus S.d (n k)))) := rfl
  rw [this]
  nlinarith

end Size

end Balaban.LargeField
