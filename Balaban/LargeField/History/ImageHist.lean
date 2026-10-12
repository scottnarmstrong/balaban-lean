module

public import Balaban.LargeField.Region.SymmLoc
public import Balaban.LargeField.Operators.QuietLocalIso
public import Balaban.LargeField.History.FlowBook

/-!
# Image of a region history under a lattice symmetry (Part I, Definition I.4.1)

For a lattice symmetry `σ : LatTorusSym` and any region history `H` (with removed components) on
tori that are points above the horizon (`n j = 1` for `j ≥ K`), the image history `imgHist σ H hsub`
has the steps `σ.ec j` / `σ.ec (j+1)` transported (`RegionStep.img`), the removed components
transported, the components `imgComp`, the lineages `lin_img`, and its localized histories are the
`σ`-images of those of `H` (`histImage_loc`).

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

theorem finOf_ec (k : ℕ) (X : Set (Torus S.d (n k))) :
    finOf (σ.ec k '' X) = (finOf X).map (σ.ec k).toEmbedding := by
  ext y
  obtain ⟨y0, rfl⟩ := (σ.ec k).surjective y
  rw [Finset.mem_map_equiv, Equiv.symm_apply_apply, mem_finOf, mem_finOf]
  exact (σ.ec k).injective.mem_set_image

/-- The image of a region history under a lattice symmetry: the steps and the removed components
are transported by `σ`. -/
noncomputable def imgHist : RegionHistory S n R k0 K where
  F := imgF σ H hsub
  rem := fun k => (H.rem k).image (Finset.map (σ.ec k).toEmbedding)
  rem_sub := fun k => by
    intro Y hY
    obtain ⟨Y0, hY0, rfl⟩ := Finset.mem_image.mp hY
    have h := H.rem_sub k hY0
    show _ ∈ comps (S.omega k) (finOf ((imgF σ H hsub).Zpre k))
    rw [imgF_Zpre, finOf_ec, comps_map (σ.ec k) (σ.dist k)]
    exact Finset.mem_image_of_mem _ h
  rem_empty := fun k hk => by rw [H.rem_empty k hk]; simp
  Z_eq := fun j => by
    show σ.ec j '' (H.step j).Z = _
    rw [H.Z_eq j, Set.image_sdiff (σ.ec j).injective, imgF_Zpre]
    congr 1
    ext x
    simp only [Set.mem_image, Set.mem_iUnion, Finset.mem_image, exists_prop, Finset.mem_coe]
    constructor
    · rintro ⟨y, ⟨c, hc, hy⟩, rfl⟩
      exact ⟨c.map (σ.ec j).toEmbedding, ⟨c, hc, rfl⟩, Finset.mem_map_of_mem _ hy⟩
    · rintro ⟨_, ⟨c, hc, rfl⟩, hx⟩
      obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
      exact ⟨y, ⟨c, hc, hy⟩, rfl⟩

/-- The component of the image history corresponding to a component of `H`. -/
noncomputable def imgComp {k : ℕ} (c : H.Comp k) : (imgHist σ H hsub).Comp k :=
  ⟨c.1.map (σ.ec k).toEmbedding, by
    show _ ∈ comps (S.omega k) (finOf ((imgF σ H hsub).Zpre k))
    rw [imgF_Zpre, finOf_ec, comps_map (σ.ec k) (σ.dist k)]
    exact Finset.mem_image_of_mem _ c.2⟩

theorem imgComp_coe {k : ℕ} (c : H.Comp k) :
    (((imgComp σ H hsub c).1 : Finset (Torus S.d (n k))) : Set (Torus S.d (n k))) =
      σ.ec k '' (c.1 : Set (Torus S.d (n k))) := by
  simp [imgComp, Finset.coe_map]

theorem imgComp_injective {k : ℕ} : Function.Injective (imgComp σ H hsub (k := k)) := by
  intro c c' h
  apply Subtype.ext
  have := congrArg Subtype.val h
  exact Finset.map_injective _ this

theorem imgComp_surjective {k : ℕ} (c' : (imgHist σ H hsub).Comp k) :
    ∃ c : H.Comp k, imgComp σ H hsub c = c' := by
  have h := c'.2
  change c'.1 ∈ comps (S.omega k) (finOf ((imgF σ H hsub).Zpre k)) at h
  rw [imgF_Zpre, finOf_ec, comps_map (σ.ec k) (σ.dist k)] at h
  obtain ⟨Y0, hY0, hY⟩ := Finset.mem_image.mp h
  exact ⟨⟨Y0, hY0⟩, Subtype.ext hY⟩

theorem isSucc_img {k : ℕ} (c : H.Comp k) (Z : H.Comp (k + 1)) :
    (imgHist σ H hsub).IsSucc k (imgComp σ H hsub c) (imgComp σ H hsub Z) ↔
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

theorem mem_rem_img {b : ℕ} (c : H.Comp b) :
    (imgComp σ H hsub c).1 ∈ (imgHist σ H hsub).rem b ↔ c.1 ∈ H.rem b := by
  show c.1.map (σ.ec b).toEmbedding ∈ (H.rem b).image (Finset.map (σ.ec b).toEmbedding) ↔ _
  constructor
  · intro h
    obtain ⟨a, ha, h⟩ := Finset.mem_image.mp h
    rwa [← Finset.map_injective _ h]
  · intro h
    exact Finset.mem_image_of_mem _ h

theorem mem_parts_img {b : ℕ} (c : H.Comp b) (Z : H.Comp (b + 1)) :
    imgComp σ H hsub c ∈ (imgHist σ H hsub).parts b (imgComp σ H hsub Z) ↔
      c ∈ H.parts b Z := by
  rw [RegionHistory.mem_parts, RegionHistory.mem_parts, isSucc_img, mem_rem_img]

theorem lin_img : ∀ {b : ℕ} (a : ℕ), a ≤ b → ∀ Z : H.Comp b,
    (((imgHist σ H hsub).lin a b (imgComp σ H hsub Z) :
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
      obtain ⟨c, rfl⟩ := imgComp_surjective σ H hsub c'
      rw [mem_parts_img] at hc'
      have h3 : x' ∈ σ.ec a '' ((H.lin a b c : Finset (Torus S.d (n a))) :
          Set (Torus S.d (n a))) := by
        rw [← ih c]; exact Finset.mem_coe.mpr hx'
      obtain ⟨x, hx, rfl⟩ := h3
      exact ⟨x, Finset.mem_coe.mpr ((mem_lin_succ _ hab).mpr ⟨c, hc', hx⟩), rfl⟩
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨c, hc, hx2⟩ := (mem_lin_succ _ hab).mp (Finset.mem_coe.mp hx)
      refine ⟨imgComp σ H hsub c, (mem_parts_img σ H hsub c Z).mpr hc, ?_⟩
      have : σ.ec a x ∈ ((((imgHist σ H hsub).lin a b (imgComp σ H hsub c) :
          Finset (Torus S.d (n a))) : Set (Torus S.d (n a)))) := by
        rw [ih c]; exact ⟨x, Finset.mem_coe.mpr hx2, rfl⟩
      exact this


theorem tailZ_img {k : ℕ} (Z : H.Comp k) : ∀ j : ℕ,
    (imgHist σ H hsub).tailZ k (imgComp σ H hsub Z) j =
      σ.ec j '' H.tailZ k Z j := by
  intro j
  induction j with
  | zero => simp [tailZ]
  | succ j ih =>
    by_cases hc : j + 1 ≤ k ∧ j + 1 ≤ K
    · simp only [tailZ, hc, and_self, ↓reduceIte]
      exact lin_img σ H hsub (j + 1) hc.1 Z
    · simp only [tailZ, hc, ↓reduceIte]
      refine RegionStep.image_Zpre (isAff_ec_all σ hsub H.F.hnn j)
        (isAff_ec_all σ hsub H.F.hnn (j + 1)) (ec_blockMap_all σ hsub H.F.hnn j)
        (NeZero.pos S.L) ih ?_ ?_ ?_ ?_ _ _ <;> simp [emptyStep]


theorem locStep_corr {k : ℕ} (Z : H.Comp k) (j : ℕ) :
    (((imgHist σ H hsub).locRH k (imgComp σ H hsub Z)).step j).Z = σ.ec j '' ((H.locRH k Z).step j).Z ∧
    (((imgHist σ H hsub).locRH k (imgComp σ H hsub Z)).step j).P = σ.ec (j + 1) '' ((H.locRH k Z).step j).P ∧
    (((imgHist σ H hsub).locRH k (imgComp σ H hsub Z)).step j).Q = σ.ec (j + 1) '' ((H.locRH k Z).step j).Q ∧
    (((imgHist σ H hsub).locRH k (imgComp σ H hsub Z)).step j).R = σ.ec (j + 1) '' ((H.locRH k Z).step j).R ∧
    (((imgHist σ H hsub).locRH k (imgComp σ H hsub Z)).step j).S = σ.ec (j + 1) '' ((H.locRH k Z).step j).S := by
  refine ⟨?_, ?_⟩
  · show ((imgHist σ H hsub).locStep k (imgComp σ H hsub Z) j).Z = σ.ec j '' (H.locStep k Z j).Z
    rw [locStep_Z, locStep_Z]
    exact tailZ_img σ H hsub Z j
  · by_cases hc : j < k ∧ j < K
    · obtain ⟨hP, hQ, hR, hS⟩ := locRH_new Z hc.1 hc.2
      obtain ⟨hP', hQ', hR', hS'⟩ := locRH_new (imgComp σ H hsub Z) hc.1 hc.2
      have hl := lin_img σ H hsub (j + 1) (by omega) Z
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hP', hP, hl, Set.image_inter (σ.ec (j + 1)).injective]; rfl
      · rw [hQ', hQ, hl, Set.image_inter (σ.ec (j + 1)).injective]; rfl
      · rw [hR', hR, hl, Set.image_inter (σ.ec (j + 1)).injective]; rfl
      · rw [hS', hS, hl, Set.image_inter (σ.ec (j + 1)).injective]; rfl
    · rw [locRH_step_empty Z hc, locRH_step_empty (imgComp σ H hsub Z) hc]
      simp [emptyStep]


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
    fineSet (S := S) (n := n) M K i A' ∩ fineSet M K k (((imgComp σ H hsub Z).1 : Finset (Torus S.d (n k))) :
      Set (Torus S.d (n k))) =
      σ.ef '' (fineSet (S := S) (n := n) M K i A ∩ fineSet M K k ((Z.1 : Finset (Torus S.d (n k))) :
      Set (Torus S.d (n k)))) := by
  rw [Set.image_inter σ.ef.injective, fineSet_img_all σ hsub i A, fineSet_img_all σ hsub k,
    imgComp_coe, h]

theorem histImage_loc {k : ℕ} (Z : H.Comp k) :
    HistImage σ.toTorusSym (H.localHistory M K k Z) ((imgHist σ H hsub).localHistory M K k (imgComp σ H hsub Z)) := by
  have hL := NeZero.pos S.L
  have key : ∀ j, (((imgHist σ H hsub).locRH k (imgComp σ H hsub Z)).step j).OmegaPrime = σ.ec (j + 1) '' ((H.locRH k Z).step j).OmegaPrime ∧
      (((imgHist σ H hsub).locRH k (imgComp σ H hsub Z)).step j).Omega = σ.ec (j + 1) '' ((H.locRH k Z).step j).Omega ∧
      (((imgHist σ H hsub).locRH k (imgComp σ H hsub Z)).step j).OmegaDD = σ.ec (j + 1) '' ((H.locRH k Z).step j).OmegaDD := by
    intro j
    obtain ⟨hZ, hP, hQ, hR, -⟩ := locStep_corr σ H hsub Z j
    have h0 := isAff_ec_all σ hsub H.F.hnn j
    have h1 := isAff_ec_all σ hsub H.F.hnn (j + 1)
    have hb := ec_blockMap_all σ hsub H.F.hnn j
    exact ⟨RegionStep.image_OmegaPrime h0 h1 hb hL hZ, RegionStep.image_Omega h0 h1 hb hL hZ hP,
      RegionStep.image_OmegaDD h0 h1 hb hL hZ hP hQ hR⟩
  refine ⟨fun j => ?_, fun j => ?_, fun j => ?_, fun j => ?_, fun j => ?_, fun j => ?_, fun j => ?_,
    fun j => ?_⟩
  · exact rec_img σ H hsub Z _ _ (locStep_corr σ H hsub Z j).1
  · exact rec_img σ H hsub Z _ _ (locStep_corr σ H hsub Z j).2.1
  · exact rec_img σ H hsub Z _ _ (locStep_corr σ H hsub Z j).2.2.1
  · exact rec_img σ H hsub Z _ _ (locStep_corr σ H hsub Z j).2.2.2.1
  · exact rec_img σ H hsub Z _ _ (locStep_corr σ H hsub Z j).2.2.2.2
  · exact rec_img σ H hsub Z _ _ (key j).1
  · exact rec_img σ H hsub Z _ _ (key j).2.1
  · exact rec_img σ H hsub Z _ _ (key j).2.2

end Hist

end Balaban.LargeField
