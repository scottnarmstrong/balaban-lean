/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Operators.QuietLocalIso
public import Balaban.LargeField.Operators.QuietLocalInput
public import Balaban.LargeField.Region.SymmLoc


/-!
# Image of a region history under a lattice symmetry (`k₀ = 0`)

For a lattice symmetry `σ : LatTorusSym` and a region history `H` without removed components (this
is forced for `k₀ = 0`: `RegionHistory.rem_empty`) on tori that are points above the horizon
(`n j = 1` for `j ≥ K`), the image history `imgHist σ H` has the steps `σ.ec j` / `σ.ec (j+1)`
transported (`RegionStep.img`), the components `imgComp`, the lineages `lin_img`, and its localized
histories are the `σ`-images of those of `H` (`histImage_loc`).  Consequently the quiet realizable
localized histories are closed under `HistImage` (`quietRealized_iff_of_histImage`): this is the
field `real_euclid` of `QuietStepInput'`.

The affine property of `σ.ec j` and its compatibility with the coarsening above the horizon hold
because the tori there are single points (`isAff_ec_all`, `ec_blockMap_all`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban RegionHistory

section Step

variable {d L n0 n1 : ℕ} [NeZero n0] [NeZero n1] {Rp Rk : ℝ}
  {e0 : Equiv.Perm (Torus d n0)} {e1 : Equiv.Perm (Torus d n1)} (h0 : IsAff e0) (h1 : IsAff e1)
  (hb : ∀ x, blockMap L n1 (e0 x) = e1 (blockMap L n1 x)) (hL : 0 < L)
  (st : RegionStep d L n0 n1 Rp Rk)

include h0 h1 hb hL in
theorem img_OmegaPrime : Region.OmegaPrime L ⌊Rk⌋₊ (Region.Uprime L n1 ⌊Rp⌋₊ (e0 '' st.Z)) =
    e1 '' st.OmegaPrime := by
  let s0 : RegionStep d L n0 n1 Rp Rk :=
    ⟨e0 '' st.Z, ∅, ∅, ∅, ∅, Set.empty_subset _, Set.empty_subset _, Set.empty_subset _,
      Set.empty_subset _⟩
  exact RegionStep.image_OmegaPrime h0 h1 hb hL (st := st) (st' := s0) rfl

/-- First stage of the image step: the region and the cubes `P`. -/
def RegionStep.stage1 : RegionStep d L n0 n1 Rp Rk where
  Z := e0 '' st.Z
  P := e1 '' st.P
  Q := ∅
  R := ∅
  S := ∅
  P_sub := by
    rw [img_OmegaPrime h0 h1 hb hL st]
    exact Set.image_mono st.P_sub
  Q_sub := Set.empty_subset _
  R_sub := Set.empty_subset _
  S_sub := Set.empty_subset _

include h0 h1 hb hL in
theorem RegionStep.stage1_Omega : (st.stage1 h0 h1 hb hL).Omega = e1 '' st.Omega :=
  RegionStep.image_Omega h0 h1 hb hL (st := st) (st' := st.stage1 h0 h1 hb hL) rfl rfl

/-- Second stage: `Q` and `R` added. -/
def RegionStep.stage2 : RegionStep d L n0 n1 Rp Rk where
  Z := e0 '' st.Z
  P := e1 '' st.P
  Q := e1 '' st.Q
  R := e1 '' st.R
  S := ∅
  P_sub := (st.stage1 h0 h1 hb hL).P_sub
  Q_sub := by
    show _ ⊆ nbhd 3 (st.stage1 h0 h1 hb hL).Omega
    rw [RegionStep.stage1_Omega h0 h1 hb hL, ← image_nbhd h1.supDist_eq]
    exact Set.image_mono st.Q_sub
  R_sub := by
    show _ ⊆ (st.stage1 h0 h1 hb hL).Omega
    rw [RegionStep.stage1_Omega h0 h1 hb hL]
    exact Set.image_mono st.R_sub
  S_sub := Set.empty_subset _

include h0 h1 hb hL in
theorem RegionStep.stage2_OmegaDD : (st.stage2 h0 h1 hb hL).OmegaDD = e1 '' st.OmegaDD :=
  RegionStep.image_OmegaDD h0 h1 hb hL (st := st) (st' := st.stage2 h0 h1 hb hL) rfl rfl rfl rfl

/-- The image of a region step under affine isometries commuting with the coarsening. -/
def RegionStep.img : RegionStep d L n0 n1 Rp Rk where
  Z := e0 '' st.Z
  P := e1 '' st.P
  Q := e1 '' st.Q
  R := e1 '' st.R
  S := e1 '' st.S
  P_sub := (st.stage2 h0 h1 hb hL).P_sub
  Q_sub := (st.stage2 h0 h1 hb hL).Q_sub
  R_sub := (st.stage2 h0 h1 hb hL).R_sub
  S_sub := by
    show _ ⊆ nbhdNeg 3 (st.stage2 h0 h1 hb hL).OmegaDD
    rw [RegionStep.stage2_OmegaDD h0 h1 hb hL, ← image_nbhdNeg h1.supDist_eq]
    exact Set.image_mono st.S_sub

include h0 h1 hb hL in
theorem RegionStep.img_Zpre (ω : ℕ) (crit : Option ℕ) :
    (st.img h0 h1 hb hL).Zpre ω crit = e1 '' st.Zpre ω crit :=
  RegionStep.image_Zpre h0 h1 hb hL (st := st) (st' := st.img h0 h1 hb hL) rfl rfl rfl rfl rfl ω crit

end Step


section Hist

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 M K : ℕ} [NeZero M]
  [NeZero S.L] (σ : LatTorusSym S n M K) (H : RegionHistory S n R k0 K)
  (hsub : ∀ j, K ≤ j → n j = 1)

include hsub in
theorem torus_subsingleton {j : ℕ} (hj : K ≤ j) : Subsingleton (Torus S.d (n j)) := by
  have h := hsub j hj
  have : Subsingleton (ZMod (n j)) := by rw [h]; infer_instance
  infer_instance

include hsub in
theorem isAff_ec_all (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) (j : ℕ) : IsAff (σ.ec j) := by
  rcases le_or_gt j K with h | h
  · exact σ.isAff_ec hnn h
  · have := torus_subsingleton (S := S) hsub h.le
    exact ⟨⟨1, fun _ => false, 0⟩, fun x => Subsingleton.elim _ _⟩

include hsub in
theorem ec_blockMap_all (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) (j : ℕ) (x : Torus S.d (n j)) :
    blockMap S.L (n (j + 1)) (σ.ec j x) = σ.ec (j + 1) (blockMap S.L (n (j + 1)) x) := by
  rcases le_or_gt (j + 1) K with h | h
  · exact (σ.ec_blockMap hnn h x).symm
  · have := torus_subsingleton (S := S) hsub h.le
    exact Subsingleton.elim _ _

/-- The image of the steps of `H` under `σ`. -/
noncomputable def imgF : FlowSteps S n R k0 K :=
  { H.F with
    step := fun j => (H.step j).img (isAff_ec_all σ hsub H.F.hnn j) (isAff_ec_all σ hsub H.F.hnn (j + 1))
      (ec_blockMap_all σ hsub H.F.hnn j) (NeZero.pos S.L) }

theorem imgF_Zpre : ∀ j, (imgF σ H hsub).Zpre j = σ.ec j '' H.F.Zpre j
  | 0 => by simp [FlowSteps.Zpre]
  | j + 1 => (H.step j).img_Zpre (isAff_ec_all σ hsub H.F.hnn j) (isAff_ec_all σ hsub H.F.hnn (j + 1))
      (ec_blockMap_all σ hsub H.F.hnn j) (NeZero.pos S.L) _ _

variable (hrem : ∀ k, H.rem k = ∅)

/-- The image of a region history without removals under a lattice symmetry. -/
noncomputable def imgHist : RegionHistory S n R k0 K where
  F := imgF σ H hsub
  rem := fun _ => ∅
  rem_sub := fun _ => Finset.empty_subset _
  rem_empty := fun _ _ => rfl
  Z_eq := fun j => by
    have h1 : (H.step j).Z = H.F.Zpre j := by
      rw [H.Z_eq j, hrem j]; simp
    show σ.ec j '' (H.step j).Z = _
    rw [h1, imgF_Zpre]
    simp


omit hrem in
theorem finOf_ec (k : ℕ) (X : Set (Torus S.d (n k))) :
    finOf (σ.ec k '' X) = (finOf X).map (σ.ec k).toEmbedding := by
  ext y
  obtain ⟨y0, rfl⟩ := (σ.ec k).surjective y
  rw [Finset.mem_map_equiv, Equiv.symm_apply_apply, mem_finOf, mem_finOf]
  exact (σ.ec k).injective.mem_set_image

/-- The component of the image history corresponding to a component of `H`. -/
noncomputable def imgComp {k : ℕ} (c : H.Comp k) : (imgHist σ H hsub hrem).Comp k :=
  ⟨c.1.map (σ.ec k).toEmbedding, by
    show _ ∈ comps (S.omega k) (finOf ((imgF σ H hsub).Zpre k))
    rw [imgF_Zpre, finOf_ec, comps_map (σ.ec k) (σ.dist k)]
    exact Finset.mem_image_of_mem _ c.2⟩

theorem imgComp_coe {k : ℕ} (c : H.Comp k) :
    (((imgComp σ H hsub hrem c).1 : Finset (Torus S.d (n k))) : Set (Torus S.d (n k))) =
      σ.ec k '' (c.1 : Set (Torus S.d (n k))) := by
  simp [imgComp, Finset.coe_map]

theorem imgComp_injective {k : ℕ} : Function.Injective (imgComp σ H hsub hrem (k := k)) := by
  intro c c' h
  apply Subtype.ext
  have := congrArg Subtype.val h
  exact Finset.map_injective _ this

theorem imgComp_surjective {k : ℕ} (c' : (imgHist σ H hsub hrem).Comp k) :
    ∃ c : H.Comp k, imgComp σ H hsub hrem c = c' := by
  have h := c'.2
  change c'.1 ∈ comps (S.omega k) (finOf ((imgF σ H hsub).Zpre k)) at h
  rw [imgF_Zpre, finOf_ec, comps_map (σ.ec k) (σ.dist k)] at h
  obtain ⟨Y0, hY0, hY⟩ := Finset.mem_image.mp h
  exact ⟨⟨Y0, hY0⟩, Subtype.ext hY⟩

theorem isSucc_img {k : ℕ} (c : H.Comp k) (Z : H.Comp (k + 1)) :
    (imgHist σ H hsub hrem).IsSucc k (imgComp σ H hsub hrem c) (imgComp σ H hsub hrem Z) ↔
      H.IsSucc k c Z := by
  unfold RegionHistory.IsSucc
  rw [imgComp_coe, imgComp_coe, Set.image_image]
  have : (fun x => blockMap S.L (n (k + 1)) (σ.ec k x)) =
      fun x => σ.ec (k + 1) (blockMap S.L (n (k + 1)) x) :=
    funext (ec_blockMap_all σ hsub H.F.hnn k)
  rw [this, ← Set.image_image (σ.ec (k + 1)) (blockMap S.L (n (k + 1)))]
  exact Set.image_subset_image_iff (σ.ec (k + 1)).injective


omit σ hsub in
theorem mem_lin_succ {a b : ℕ} (hab : a ≤ b) {Z : H.Comp (b + 1)} {x : Torus S.d (n a)} :
    x ∈ H.lin a (b + 1) Z ↔ ∃ c ∈ H.parts b Z, x ∈ H.lin a b c := by
  rw [mem_lin]
  constructor
  · rintro ⟨Y, hd, hx⟩
    obtain ⟨c, hc, hd'⟩ := (desc_succ_iff hab).mp hd
    exact ⟨c, hc, mem_lin.mpr ⟨Y, hd', hx⟩⟩
  · rintro ⟨c, hc, hx⟩
    obtain ⟨Y, hd', hx'⟩ := mem_lin.mp hx
    exact ⟨Y, (desc_succ_iff hab).mpr ⟨c, hc, hd'⟩, hx'⟩

theorem mem_parts_img {b : ℕ} (c : H.Comp b) (Z : H.Comp (b + 1)) :
    imgComp σ H hsub hrem c ∈ (imgHist σ H hsub hrem).parts b (imgComp σ H hsub hrem Z) ↔
      c ∈ H.parts b Z := by
  rw [RegionHistory.mem_parts, RegionHistory.mem_parts, isSucc_img]
  have h1 : c.1 ∉ H.rem b := by rw [hrem b]; simp
  have h2 : (imgComp σ H hsub hrem c).1 ∉ (imgHist σ H hsub hrem).rem b := by
    show _ ∉ (∅ : Finset _); simp
  simp [h1, h2]

theorem lin_img : ∀ {b : ℕ} (a : ℕ), a ≤ b → ∀ Z : H.Comp b,
    (((imgHist σ H hsub hrem).lin a b (imgComp σ H hsub hrem Z) :
      Finset (Torus S.d (n a))) : Set (Torus S.d (n a))) =
      σ.ec a '' ((H.lin a b Z : Finset (Torus S.d (n a))) : Set (Torus S.d (n a))) := by
  intro b a hab
  induction b, hab using Nat.le_induction with
  | base =>
    intro Z
    rw [RegionHistory.lin_self, RegionHistory.lin_self, imgComp_coe]
  | succ b hab ih =>
    intro Z
    ext x'
    rw [Finset.mem_coe, mem_lin_succ _ hab]
    constructor
    · rintro ⟨c', hc', hx'⟩
      obtain ⟨c, rfl⟩ := imgComp_surjective σ H hsub hrem c'
      rw [mem_parts_img] at hc'
      have h3 : x' ∈ σ.ec a '' ((H.lin a b c : Finset (Torus S.d (n a))) :
          Set (Torus S.d (n a))) := by
        rw [← ih c]; exact Finset.mem_coe.mpr hx'
      obtain ⟨x, hx, rfl⟩ := h3
      exact ⟨x, Finset.mem_coe.mpr ((mem_lin_succ _ hab).mpr ⟨c, hc', hx⟩), rfl⟩
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨c, hc, hx2⟩ := (mem_lin_succ _ hab).mp (Finset.mem_coe.mp hx)
      refine ⟨imgComp σ H hsub hrem c, (mem_parts_img σ H hsub hrem c Z).mpr hc, ?_⟩
      have : σ.ec a x ∈ ((((imgHist σ H hsub hrem).lin a b (imgComp σ H hsub hrem c) :
          Finset (Torus S.d (n a))) : Set (Torus S.d (n a)))) := by
        rw [ih c]; exact ⟨x, Finset.mem_coe.mpr hx2, rfl⟩
      exact this


theorem tailZ_img {k : ℕ} (Z : H.Comp k) : ∀ j : ℕ,
    (imgHist σ H hsub hrem).tailZ k (imgComp σ H hsub hrem Z) j =
      σ.ec j '' H.tailZ k Z j := by
  intro j
  induction j with
  | zero => simp [tailZ]
  | succ j ih =>
    by_cases hc : j + 1 ≤ k ∧ j + 1 ≤ K
    · simp only [tailZ, hc, and_self, ↓reduceIte]
      exact lin_img σ H hsub hrem (j + 1) hc.1 Z
    · simp only [tailZ, hc, ↓reduceIte]
      refine RegionStep.image_Zpre (isAff_ec_all σ hsub H.F.hnn j)
        (isAff_ec_all σ hsub H.F.hnn (j + 1)) (ec_blockMap_all σ hsub H.F.hnn j)
        (NeZero.pos S.L) ih ?_ ?_ ?_ ?_ _ _ <;> simp [emptyStep]

local notation "Hi" => imgHist σ H hsub hrem
local notation "ci" => imgComp σ H hsub hrem

theorem locStep_corr {k : ℕ} (Z : H.Comp k) (j : ℕ) :
    (((Hi).locRH k (ci Z)).step j).Z = σ.ec j '' ((H.locRH k Z).step j).Z ∧
    (((Hi).locRH k (ci Z)).step j).P = σ.ec (j + 1) '' ((H.locRH k Z).step j).P ∧
    (((Hi).locRH k (ci Z)).step j).Q = σ.ec (j + 1) '' ((H.locRH k Z).step j).Q ∧
    (((Hi).locRH k (ci Z)).step j).R = σ.ec (j + 1) '' ((H.locRH k Z).step j).R ∧
    (((Hi).locRH k (ci Z)).step j).S = σ.ec (j + 1) '' ((H.locRH k Z).step j).S := by
  refine ⟨?_, ?_⟩
  · show ((Hi).locStep k (ci Z) j).Z = σ.ec j '' (H.locStep k Z j).Z
    rw [locStep_Z, locStep_Z]
    exact tailZ_img σ H hsub hrem Z j
  · by_cases hc : j < k ∧ j < K
    · obtain ⟨hP, hQ, hR, hS⟩ := locRH_new Z hc.1 hc.2
      obtain ⟨hP', hQ', hR', hS'⟩ := locRH_new (ci Z) hc.1 hc.2
      have hl := lin_img σ H hsub hrem (j + 1) (by omega) Z
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hP', hP, hl, Set.image_inter (σ.ec (j + 1)).injective]; rfl
      · rw [hQ', hQ, hl, Set.image_inter (σ.ec (j + 1)).injective]; rfl
      · rw [hR', hR, hl, Set.image_inter (σ.ec (j + 1)).injective]; rfl
      · rw [hS', hS, hl, Set.image_inter (σ.ec (j + 1)).injective]; rfl
    · rw [locRH_step_empty Z hc, locRH_step_empty (ci Z) hc]
      simp [emptyStep]


omit hrem in
include hsub in
theorem fineSet_img_all (i : ℕ) (A : Set (Torus S.d (n i))) :
    σ.ef '' fineSet (S := S) (n := n) M K i A = fineSet (S := S) (n := n) M K i (σ.ec i '' A) := by
  rcases le_or_gt i K with h | h
  · exact σ.toTorusSym.fineSet_image h A
  · have := torus_subsingleton (S := S) hsub h.le
    rcases Set.eq_empty_or_nonempty A with rfl | ⟨a, ha⟩
    · simp [fineSet]
    · have hA : A = Set.univ := Set.eq_univ_of_forall fun x => by
        rwa [Subsingleton.elim x a]
      subst hA
      have e1 : fineSet (S := S) (n := n) M K i Set.univ = Set.univ := by
        ext x; simp [fineSet]
      rw [e1, Set.image_univ_of_surjective (σ.ec i).surjective, e1,
        Set.image_univ_of_surjective σ.ef.surjective]

theorem rec_img {k i : ℕ} (Z : H.Comp k) (A A' : Set (Torus S.d (n i))) (h : A' = σ.ec i '' A) :
    fineSet (S := S) (n := n) M K i A' ∩ fineSet M K k (((ci Z).1 : Finset (Torus S.d (n k))) :
      Set (Torus S.d (n k))) =
      σ.ef '' (fineSet (S := S) (n := n) M K i A ∩ fineSet M K k ((Z.1 : Finset (Torus S.d (n k))) :
      Set (Torus S.d (n k)))) := by
  rw [Set.image_inter σ.ef.injective, fineSet_img_all σ hsub i A, fineSet_img_all σ hsub k,
    imgComp_coe, h]

theorem histImage_loc {k : ℕ} (Z : H.Comp k) :
    HistImage σ.toTorusSym (H.localHistory M K k Z) ((Hi).localHistory M K k (ci Z)) := by
  have hL := NeZero.pos S.L
  have key : ∀ j, (((Hi).locRH k (ci Z)).step j).OmegaPrime = σ.ec (j + 1) '' ((H.locRH k Z).step j).OmegaPrime ∧
      (((Hi).locRH k (ci Z)).step j).Omega = σ.ec (j + 1) '' ((H.locRH k Z).step j).Omega ∧
      (((Hi).locRH k (ci Z)).step j).OmegaDD = σ.ec (j + 1) '' ((H.locRH k Z).step j).OmegaDD := by
    intro j
    obtain ⟨hZ, hP, hQ, hR, -⟩ := locStep_corr σ H hsub hrem Z j
    have h0 := isAff_ec_all σ hsub H.F.hnn j
    have h1 := isAff_ec_all σ hsub H.F.hnn (j + 1)
    have hb := ec_blockMap_all σ hsub H.F.hnn j
    exact ⟨RegionStep.image_OmegaPrime h0 h1 hb hL hZ, RegionStep.image_Omega h0 h1 hb hL hZ hP,
      RegionStep.image_OmegaDD h0 h1 hb hL hZ hP hQ hR⟩
  refine ⟨fun j => ?_, fun j => ?_, fun j => ?_, fun j => ?_, fun j => ?_, fun j => ?_, fun j => ?_,
    fun j => ?_⟩
  · exact rec_img σ H hsub hrem Z _ _ (locStep_corr σ H hsub hrem Z j).1
  · exact rec_img σ H hsub hrem Z _ _ (locStep_corr σ H hsub hrem Z j).2.1
  · exact rec_img σ H hsub hrem Z _ _ (locStep_corr σ H hsub hrem Z j).2.2.1
  · exact rec_img σ H hsub hrem Z _ _ (locStep_corr σ H hsub hrem Z j).2.2.2.1
  · exact rec_img σ H hsub hrem Z _ _ (locStep_corr σ H hsub hrem Z j).2.2.2.2
  · exact rec_img σ H hsub hrem Z _ _ (key j).1
  · exact rec_img σ H hsub hrem Z _ _ (key j).2.1
  · exact rec_img σ H hsub hrem Z _ _ (key j).2.2


theorem isQuiet_img {k : ℕ} (hk : k + 1 ≤ K) (Z : H.Comp (k + 1))
    (hq : IsQuiet (H.locRH (k + 1) Z) k Z.1) :
    IsQuiet ((Hi).locRH (k + 1) (ci Z)) k (ci Z).1 := by
  have hiso : RegionIso σ (H.locRH (k + 1) Z) ((Hi).locRH (k + 1) (ci Z)) :=
    ⟨fun j _ => (locStep_corr σ H hsub hrem Z j).1,
      fun j _ => (locStep_corr σ H hsub hrem Z j).2.1,
      fun j _ => (locStep_corr σ H hsub hrem Z j).2.2.1,
      fun j _ => (locStep_corr σ H hsub hrem Z j).2.2.2.1,
      fun j _ => (locStep_corr σ H hsub hrem Z j).2.2.2.2⟩
  exact isQuiet_of_regionIso σ hiso hk (imgComp_coe σ H hsub hrem Z) hq

theorem admissible_imgHist : (Hi).Admissible := fun _ _ hc => absurd hc (Finset.notMem_empty _)

end Hist

section Realized

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 M K : ℕ} [NeZero M]
  [NeZero S.L] (σ : LatTorusSym S n M K) (hsub : ∀ j, K ≤ j → n j = 1) (hk0 : k0 = 0)

include hsub hk0 in
/-- Quiet realizability is stable under lattice symmetries (when `k₀ = 0`, so every region history
is admissible, and the tori above the horizon are points). -/
theorem QuietRealized.image {k : ℕ} {a : LocalHistory S n M K} (h : QuietRealized R k0 k a) :
    ∃ a', QuietRealized R k0 k a' ∧ HistImage σ.toTorusSym a a' := by
  obtain ⟨H, -, Z', hk1, hkK, hq, rfl⟩ := h
  have hrem : ∀ k', H.rem k' = ∅ := fun k' => H.rem_empty k' (by omega)
  exact ⟨_, ⟨imgHist σ H hsub hrem, admissible_imgHist σ H hsub hrem, imgComp σ H hsub hrem Z',
    hk1, hkK, isQuiet_img σ H hsub hrem hkK Z' hq, rfl⟩, histImage_loc σ H hsub hrem Z'⟩


/-- `b` is the image of the localized history `a` under the permutation `g` of the fine torus. -/
def LocalHistory.ImgBy (g : Equiv.Perm (Torus S.d (M * n K * S.L ^ K)))
    (a b : LocalHistory S n M K) : Prop :=
  (∀ j, b.Z j = g '' a.Z j) ∧ (∀ j, b.P j = g '' a.P j) ∧ (∀ j, b.Q j = g '' a.Q j) ∧
  (∀ j, b.R j = g '' a.R j) ∧ (∀ j, b.Sset j = g '' a.Sset j) ∧
  (∀ j, b.OmegaPrime j = g '' a.OmegaPrime j) ∧ (∀ j, b.Omega j = g '' a.Omega j) ∧
  (∀ j, b.OmegaDD j = g '' a.OmegaDD j)

variable {σ} {a b c : LocalHistory S n M K}

theorem LocalHistory.ImgBy.of_histImage (h : HistImage σ.toTorusSym a b) :
    LocalHistory.ImgBy σ.ef a b :=
  ⟨h.Z, h.P, h.Q, h.R, h.Sset, h.OmegaPrime, h.Omega, h.OmegaDD⟩

theorem LocalHistory.ImgBy.toHistImage (h : LocalHistory.ImgBy σ.ef a b) :
    HistImage σ.toTorusSym a b :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2⟩

theorem LocalHistory.ImgBy.comp {g g' : Equiv.Perm (Torus S.d (M * n K * S.L ^ K))}
    (h : LocalHistory.ImgBy g a b) (h' : LocalHistory.ImgBy g' b c) :
    LocalHistory.ImgBy (g' * g) a c := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8⟩ := h'
  refine ⟨fun j => ?_, fun j => ?_, fun j => ?_, fun j => ?_, fun j => ?_, fun j => ?_,
    fun j => ?_, fun j => ?_⟩
  · rw [k1, h1, Set.image_image]; rfl
  · rw [k2, h2, Set.image_image]; rfl
  · rw [k3, h3, Set.image_image]; rfl
  · rw [k4, h4, Set.image_image]; rfl
  · rw [k5, h5, Set.image_image]; rfl
  · rw [k6, h6, Set.image_image]; rfl
  · rw [k7, h7, Set.image_image]; rfl
  · rw [k8, h8, Set.image_image]; rfl

theorem LocalHistory.ext' {b c : LocalHistory S n M K} (h1 : b.Z = c.Z) (h2 : b.P = c.P)
    (h3 : b.Q = c.Q) (h4 : b.R = c.R) (h5 : b.Sset = c.Sset) (h6 : b.OmegaPrime = c.OmegaPrime)
    (h7 : b.Omega = c.Omega) (h8 : b.OmegaDD = c.OmegaDD) : b = c := by
  cases b; cases c
  simp only [LocalHistory.mk.injEq]
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

theorem LocalHistory.ImgBy.unique {g : Equiv.Perm (Torus S.d (M * n K * S.L ^ K))}
    (h : LocalHistory.ImgBy g a b) (h' : LocalHistory.ImgBy g a c) : b = c := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8⟩ := h'
  exact LocalHistory.ext' (funext fun j => by rw [h1 j, k1 j]) (funext fun j => by rw [h2 j, k2 j])
    (funext fun j => by rw [h3 j, k3 j]) (funext fun j => by rw [h4 j, k4 j])
    (funext fun j => by rw [h5 j, k5 j]) (funext fun j => by rw [h6 j, k6 j])
    (funext fun j => by rw [h7 j, k7 j]) (funext fun j => by rw [h8 j, k8 j])

theorem LocalHistory.ImgBy.one (h : LocalHistory.ImgBy (1 : Equiv.Perm (Torus S.d (M * n K * S.L ^ K))) a b) : b = a := by
  have h' : LocalHistory.ImgBy (1 : Equiv.Perm (Torus S.d (M * n K * S.L ^ K))) a a := by
    refine ⟨fun j => ?_, fun j => ?_, fun j => ?_, fun j => ?_, fun j => ?_, fun j => ?_,
      fun j => ?_, fun j => ?_⟩ <;> simp
  exact h.unique h'

include hsub hk0 in
/-- **Closure of quiet realizability under lattice symmetries** (`real_euclid`). -/
theorem quietRealized_iff_of_histImage {k : ℕ} (hI : HistImage σ.toTorusSym a b) :
    QuietRealized R k0 k a ↔ QuietRealized R k0 k b := by
  constructor
  · intro h
    obtain ⟨a'', hr, hI''⟩ := QuietRealized.image σ hsub hk0 h
    rwa [(LocalHistory.ImgBy.of_histImage hI).unique (LocalHistory.ImgBy.of_histImage hI'')]
  · intro h
    have hfin : Finite (Torus S.d (M * n K * S.L ^ K)) := inferInstance
    obtain ⟨m, hm, hfm⟩ := (isOfFinOrder_of_finite σ.ef).exists_pow_eq_one
    have key : ∀ i : ℕ, ∃ b', QuietRealized R k0 k b' ∧ LocalHistory.ImgBy (σ.ef ^ i) b b' := by
      intro i
      induction i with
      | zero =>
        refine ⟨b, h, ?_⟩
        refine ⟨fun j => ?_, fun j => ?_, fun j => ?_, fun j => ?_, fun j => ?_, fun j => ?_,
          fun j => ?_, fun j => ?_⟩ <;> simp
      | succ i ih =>
        obtain ⟨b', hr, hb'⟩ := ih
        obtain ⟨b'', hr'', hI''⟩ := QuietRealized.image σ hsub hk0 hr
        refine ⟨b'', hr'', ?_⟩
        rw [pow_succ']
        exact hb'.comp (LocalHistory.ImgBy.of_histImage hI'')
    obtain ⟨b', hr, hb'⟩ := key (m - 1)
    have hcomp := (LocalHistory.ImgBy.of_histImage hI).comp hb'
    rw [← pow_succ, Nat.sub_add_cancel hm, hfm] at hcomp
    rwa [← LocalHistory.ImgBy.one (S := S) (n := n) (M := M) (K := K) hcomp]

end Realized

end Balaban.LargeField
