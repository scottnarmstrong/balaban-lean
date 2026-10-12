module

public import Balaban.LargeField.History.ImageHist
public import Balaban.LargeField.Budget.CanonicalBook

/-!
# The bookkeeping of the image history (Part I, Definitions I.4.6-I.4.7)

Because the spine of a component is chosen of the canonical length `RegionHistory.spineTarget`
(which depends only on the lengths of the spines of the old parts, the new cubes and the shape of
the component), the lengths of the spines and the books are invariant under lattice symmetries:
`(imgHist σ H hsub).bk k (imgComp c) = H.bk k c` (`bk_img`), hence ripeness of the removed
components is preserved (`admissible_imgHist_iff`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban RegionHistory

section Book

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 M K : ℕ} [NeZero M]
  [NeZero S.L] (σ : LatTorusSym S n M K) (H : RegionHistory S n R k0 K)
  (hsub : ∀ j, K ≤ j → n j = 1)

theorem newCubes_img (k : ℕ) :
    (imgHist σ H hsub).newCubes (k + 1) = (H.newCubes (k + 1)).map (σ.ec (k + 1)).toEmbedding := by
  show finOf (((imgHist σ H hsub).step k).newCubes) = _
  have e : ((imgHist σ H hsub).step k).newCubes = σ.ec (k + 1) '' (H.step k).newCubes := by
    show Region.newCubes _ _ _ _ = _
    simp only [imgHist, imgF, RegionStep.img, Region.newCubes, Set.image_union]
  rw [e, finOf_ec]
  rfl

theorem inter_newCubes_card_img {k : ℕ} (Z : H.Comp (k + 1)) :
    ((imgComp σ H hsub Z).1 ∩ (imgHist σ H hsub).newCubes (k + 1)).card =
      (Z.1 ∩ H.newCubes (k + 1)).card := by
  rw [newCubes_img]
  show (Z.1.map (σ.ec (k + 1)).toEmbedding ∩ (H.newCubes (k + 1)).map (σ.ec (k + 1)).toEmbedding).card = _
  rw [← Finset.map_inter, Finset.card_map]

theorem parts_img {k : ℕ} (Z : H.Comp (k + 1)) :
    (imgHist σ H hsub).parts k (imgComp σ H hsub Z) = (H.parts k Z).image (imgComp σ H hsub) := by
  classical
  ext c'
  obtain ⟨c, rfl⟩ := imgComp_surjective σ H hsub c'
  rw [mem_parts_img, Finset.mem_image]
  constructor
  · intro h; exact ⟨c, h, rfl⟩
  · rintro ⟨d, hd, hdc⟩
    rwa [← imgComp_injective σ H hsub hdc]

theorem isSmall_img {k : ℕ} (Z : H.Comp k) :
    IsSmall (((imgComp σ H hsub Z).1 : Finset (Torus S.d (n k))) : Set (Torus S.d (n k))) ↔
      IsSmall ((Z.1 : Finset (Torus S.d (n k))) : Set (Torus S.d (n k))) := by
  obtain ⟨A, hA⟩ := isAff_ec_all σ hsub H.F.hnn k
  have : (σ.ec k '' ((Z.1 : Finset (Torus S.d (n k))) : Set (Torus S.d (n k)))) =
      A.toFun '' ((Z.1 : Finset (Torus S.d (n k))) : Set (Torus S.d (n k))) :=
    Set.image_congr (fun x _ => hA x)
  rw [imgComp_coe, this]
  exact A.isSmall_image _

theorem side_img {k : ℕ} (Z : H.Comp k) :
    side (((imgComp σ H hsub Z).1 : Finset (Torus S.d (n k))) : Set (Torus S.d (n k))) =
      side ((Z.1 : Finset (Torus S.d (n k))) : Set (Torus S.d (n k))) := by
  obtain ⟨A, hA⟩ := isAff_ec_all σ hsub H.F.hnn k
  have : (σ.ec k '' ((Z.1 : Finset (Torus S.d (n k))) : Set (Torus S.d (n k)))) =
      A.toFun '' ((Z.1 : Finset (Torus S.d (n k))) : Set (Torus S.d (n k))) :=
    Set.image_congr (fun x _ => hA x)
  rw [imgComp_coe, this]
  exact A.side_image _

theorem nextBook_len_congr (μ : ℕ) {ι : Type*} (parts : Finset ι) (f : ι → Book) (r : ℕ)
    (Γ Γ' : Spine S.d) (h : Γ.length = Γ'.length) :
    S.nextBook μ parts f r Γ = S.nextBook μ parts f r Γ' := by
  unfold Setting.nextBook
  rw [h]

/-- The lengths of the canonical spines and the books are invariant under lattice symmetries. -/
theorem spine_len_bk_img : ∀ k, k ≤ K → ∀ c : H.Comp k,
    ((imgHist σ H hsub).spine k (imgComp σ H hsub c)).length = (H.spine k c).length ∧
    (imgHist σ H hsub).bk k (imgComp σ H hsub c) = H.bk k c := by
  classical
  intro k
  induction k with
  | zero => intro _ c; exact (H.F.isEmpty_comp_zero.false c).elim
  | succ k ih =>
    intro hkK Z
    have hk : k < K := by omega
    have ih' := fun c => ih hk.le c
    have hparts := parts_img σ H hsub Z
    have hsum : ∑ c' ∈ (imgHist σ H hsub).parts k (imgComp σ H hsub Z),
        ((imgHist σ H hsub).spine k c').length / S.L = ∑ c ∈ H.parts k Z, (H.spine k c).length / S.L := by
      rw [hparts, Finset.sum_image (fun _ _ _ _ h => imgComp_injective σ H hsub h)]
      exact Finset.sum_congr rfl fun c _ => by rw [(ih' c).1]
    have hcard : ((imgHist σ H hsub).parts k (imgComp σ H hsub Z)).card = (H.parts k Z).card := by
      rw [hparts, Finset.card_image_of_injective _ (imgComp_injective σ H hsub)]
    have hex : (∃ c', (imgHist σ H hsub).parts k (imgComp σ H hsub Z) = {c'} ∧
        ((imgHist σ H hsub).spine k c').length ≤ S.L) ↔
        ∃ c, H.parts k Z = {c} ∧ (H.spine k c).length ≤ S.L := by
      constructor
      · rintro ⟨c', hc', hL⟩
        have hmem : c' ∈ (imgHist σ H hsub).parts k (imgComp σ H hsub Z) := by
          rw [hc']; exact Finset.mem_singleton_self _
        obtain ⟨c, rfl⟩ := imgComp_surjective σ H hsub c'
        rw [mem_parts_img] at hmem
        refine ⟨c, ?_, by rw [← (ih' c).1]; exact hL⟩
        rw [hparts] at hc'
        have := congrArg (Finset.image (fun d => d)) hc'
        ext d
        rw [Finset.mem_singleton]
        constructor
        · intro hd
          have : imgComp σ H hsub d ∈ (H.parts k Z).image (imgComp σ H hsub) :=
            Finset.mem_image_of_mem _ hd
          rw [hc', Finset.mem_singleton] at this
          exact imgComp_injective σ H hsub this
        · rintro rfl; exact hmem
      · rintro ⟨c, hc, hL⟩
        refine ⟨imgComp σ H hsub c, ?_, by rw [(ih' c).1]; exact hL⟩
        rw [hparts, hc]; simp
    have htarget : (imgHist σ H hsub).spineTarget k ((imgHist σ H hsub).spine k) (imgComp σ H hsub Z) =
        H.spineTarget k (H.spine k) Z := by
      unfold spineTarget
      simp only [inter_newCubes_card_img, hsum, hcard, hex, isSmall_img, side_img]
    have hlen : ((imgHist σ H hsub).spine (k + 1) (imgComp σ H hsub Z)).length =
        (H.spine (k + 1) Z).length := by
      rw [((imgHist σ H hsub).spineCan_spine hk _).2, (H.spineCan_spine hk Z).2, htarget]
    refine ⟨hlen, ?_⟩
    show S.nextBook (k + 1) _ _ _ _ = S.nextBook (k + 1) _ _ _ _
    rw [nextBook_len_congr _ _ _ _ _ _ hlen, parts_img, inter_newCubes_card_img]
    have hfg : ∀ c ∈ H.parts k Z, S.postBook k0 k (H.bk k c) =
        (fun c' => S.postBook k0 k ((imgHist σ H hsub).bk k c')) (imgComp σ H hsub c) := by
      intro c _
      simp only [(ih' c).2]
    have h := S.nextBook_image (k + 1) (imgComp σ H hsub) (imgComp_injective σ H hsub) (H.parts k Z)
      (fun c => S.postBook k0 k (H.bk k c)) (fun c' => S.postBook k0 k ((imgHist σ H hsub).bk k c'))
      hfg (Z.1 ∩ H.newCubes (k + 1)).card (H.spine (k + 1) Z)
    rw [h]
    congr
    exact Subsingleton.elim _ _

theorem bk_img {k : ℕ} (hk : k ≤ K) (c : H.Comp k) :
    (imgHist σ H hsub).bk k (imgComp σ H hsub c) = H.bk k c :=
  (spine_len_bk_img σ H hsub k hk c).2

/-- Admissibility (ripeness of the removed components) is invariant under lattice symmetries. -/
theorem admissible_imgHist_iff (hk0K : k0 ≤ K) :
    (imgHist σ H hsub).Admissible ↔ H.Admissible := by
  constructor
  · intro h k c hc
    by_cases hk : k ≤ K
    · have h1 := h k (imgComp σ H hsub c) ((mem_rem_img σ H hsub c).mpr hc)
      rwa [bk_img σ H hsub hk] at h1
    · exact absurd hc (by rw [H.rem_empty k (Or.inr (by omega))]; simp)
  · intro h k c' hc'
    obtain ⟨c, rfl⟩ := imgComp_surjective σ H hsub c'
    have hc := (mem_rem_img σ H hsub c).mp hc'
    by_cases hk : k ≤ K
    · rw [bk_img σ H hsub hk]; exact h k c hc
    · exact absurd hc (by rw [H.rem_empty k (Or.inr (by omega))]; simp)

end Book

end Balaban.LargeField
