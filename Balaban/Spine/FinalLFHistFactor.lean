/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.FinalLFSplit
public import Balaban.Spine.AgreeTransportRep
public import Balaban.LargeField.Budget.KeptPositions
public import Balaban.LargeField.R.LocalLemmas

/-!
# The records of the components of a history (A6-4, the history factorization)

The large-field half of the last integral is a sum over the histories `𝔸 ∈ lfHist` (no removal up to
the scale `k`, nonempty region `Z_k`). The factorization of P7 (4.2)–(4.4) rewrites it as a sum over
families of components: a history is determined, up to the scale `k`, by the records of the
components of `Z_k` (`notes/phase1/A64-DESIGN.md` §2).

* `exists_desc_of_rem`: without removals every component has a descendant at the scale `k`;
* `exists_of_mem_keptPos`, `mem_keptPos_of_desc`: the kept positions of the lineage of `Z` are the
  kept ripe events of the ancestors of `Z`;
* `keptLab_eq_of_rem`: without removals the kept labels of a history are its labels at the kept
  positions of the components of scale `k`;
* `new_eq_iUnion_locRH`: the new cubes `P, Q, R, S` of a step are the unions of those of the
  localization steps of the components of scale `k`;
* the record of a component, `compRec` (its cubes, its localized history, its labelled kept
  positions `labSet`, the records of Lemma II.5.15), and the records of a history, `lfRecs`;
* **`agree_of_lfRecs_eq`**: two histories without removals up to `k` with the same records agree up
  to `k`; **`lfRecs_eq_of_agree`**: conversely agreeing histories have the same records;
* **`lfRecs_injOn`**: on the histories `lfHist` of a complete set the records are injective.
-/

@[expose] public section

open Balaban Balaban.LargeField Balaban.LargeField.Def7 RegionHistory

namespace Balaban.RootFSpine

/-- **The record of a component of scale `k`**: its set of cubes, its localized history, and its
labelled kept positions (the form of the records of Lemma II.5.15, `sum_inv_logC_labelled`). -/
abbrev CRec (S : Setting) (n : ℕ → ℕ) [∀ k, NeZero (n k)] (M K k : ℕ) : Type :=
  Finset (Torus S.d (n k)) × LocalHistory S n M K × Finset (KeptPos S n × Fin 5)

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}

section Lineage

variable (H : RegionHistory S n R k0 K)

/-- **Without removals between the scales `a` and `k`, every component of scale `a` has a
descendant of scale `k`** (the successors of `RegionHistory.exists_succ`). -/
theorem exists_desc_of_rem {a k : ℕ} (hak : a ≤ k) (hkK : k ≤ K)
    (hrem : ∀ i, a ≤ i → i < k → H.rem i = ∅) (Y : H.Comp a) :
    ∃ Z : H.Comp k, H.Desc a k Y Z := by
  induction k, hak using Nat.le_induction with
  | base => exact ⟨Y, Desc.refl Y⟩
  | succ k hak ih =>
    obtain ⟨Z, hZ⟩ := ih (by omega) (fun i hi1 hi2 => hrem i hi1 (by omega))
    have hZr : Z.1 ∉ H.rem k := by rw [hrem k hak (by omega)]; exact Finset.notMem_empty _
    exact ⟨H.succ (by omega) Z hZr, Desc.step k Y Z _ hZ hZr (H.succ_spec (by omega) hZr)⟩

/-- A kept position of the lineage of `Z` is a kept ripe event of an ancestor of `Z`. -/
theorem exists_of_mem_keptPos : ∀ (k : ℕ) (Z : H.Comp k) (p : KeptPos S n),
    p ∈ H.keptPos k Z → ∃ Y : H.Comp p.1, H.Desc p.1 k Y Z ∧ Y.1 = p.2 ∧ H.IsKeptEvent p.1 Y
  | 0, Z, _, _ => (H.F.isEmpty_comp_zero.false Z).elim
  | k + 1, Z', p, hp => by
    classical
    rw [keptPos_succ, Finset.mem_union, Finset.mem_biUnion] at hp
    rcases hp with ⟨c, hc, hpc⟩ | hp
    · obtain ⟨Y, hY, hY1, hY2⟩ := exists_of_mem_keptPos k c p hpc
      exact ⟨Y, (desc_succ_iff hY.le).2 ⟨c, hc, hY⟩, hY1, hY2⟩
    · by_cases hk : H.IsKeptEvent (k + 1) Z'
      · rw [ite_eq_left hk, Finset.mem_singleton] at hp
        subst hp
        exact ⟨Z', Desc.refl Z', rfl, hk⟩
      · rw [ite_eq_right hk] at hp
        exact absurd hp (Finset.notMem_empty _)

/-- A kept ripe event of an ancestor of `Z` is a kept position of the lineage of `Z`. -/
theorem mem_keptPos_of_desc {j k : ℕ} {Y : H.Comp j} {Z : H.Comp k} (hd : H.Desc j k Y Z)
    (hY : H.IsKeptEvent j Y) : (⟨j, Y.1⟩ : KeptPos S n) ∈ H.keptPos k Z := by
  classical
  induction hd with
  | refl =>
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by have := hY.1; omega⟩
    rw [keptPos_succ, Finset.mem_union, ite_eq_left hY]
    exact Or.inr (Finset.mem_singleton_self _)
  | step b Y Y' Y'' hd hrem hs ih =>
    rw [keptPos_succ, Finset.mem_union, Finset.mem_biUnion]
    exact Or.inl ⟨Y', (H.mem_parts b Y' Y'').2 ⟨hrem, hs⟩, ih hY⟩

/-- **The new cubes of a step are the unions of those of the localization steps** of the
components of scale `k`, when no component is removed between the scales `j + 1` and `k`: every new
cube lies in `Z^pre_{j+1}` (Lemma I.3.5 (e)), hence in a component of scale `j + 1`, hence in the
lineage of its descendant of scale `k`. -/
theorem new_eq_iUnion_locRH {j k : ℕ} (hjk : j < k) (hkK : k ≤ K)
    (hrem : ∀ i, j + 1 ≤ i → i < k → H.rem i = ∅) :
    (H.step j).P = ⋃ c : H.Comp k, ((H.locRH k c).step j).P ∧
    (H.step j).Q = ⋃ c : H.Comp k, ((H.locRH k c).step j).Q ∧
    (H.step j).R = ⋃ c : H.Comp k, ((H.locRH k c).step j).R ∧
    (H.step j).S = ⋃ c : H.Comp k, ((H.locRH k c).step j).S := by
  have hlin : ∀ y ∈ (H.step j).newCubes, ∃ c : H.Comp k,
      y ∈ ((H.lin (j + 1) k c : Finset (Torus S.d (n (j + 1)))) : Set (Torus S.d (n (j + 1)))) := by
    intro y hy
    have hy' : y ∈ H.F.Zpre (j + 1) :=
      (H.step j).Z0_subset_Zpre _ _ ((H.step j).newCubes_subset_Z0 hy)
    obtain ⟨Y, hY, hyY⟩ := mem_comp_self (ω := S.omega (j + 1)) (mem_finOf.mpr hy')
    obtain ⟨Z, hZ⟩ := exists_desc_of_rem H hjk hkK hrem ⟨Y, hY⟩
    exact ⟨Z, Finset.mem_coe.2 (mem_lin.2 ⟨⟨Y, hY⟩, hZ, hyY⟩)⟩
  have key : ∀ T : Set (Torus S.d (n (j + 1))), T ⊆ (H.step j).newCubes →
      T = ⋃ c : H.Comp k, T ∩ ((H.lin (j + 1) k c : Finset _) : Set _) := by
    intro T hT
    ext y
    simp only [Set.mem_iUnion, Set.mem_inter_iff]
    exact ⟨fun hy => (hlin y (hT hy)).imp fun c hc => ⟨hy, hc⟩, fun ⟨_, hy, _⟩ => hy⟩
  refine ⟨(key _ fun x hx => Or.inl (Or.inl (Or.inl hx))).trans
      (Set.iUnion_congr fun c => (locRH_new c hjk (by omega)).1.symm),
    (key _ fun x hx => Or.inl (Or.inl (Or.inr hx))).trans
      (Set.iUnion_congr fun c => (locRH_new c hjk (by omega)).2.1.symm),
    (key _ fun x hx => Or.inl (Or.inr hx)).trans
      (Set.iUnion_congr fun c => (locRH_new c hjk (by omega)).2.2.1.symm),
    (key _ fun x hx => Or.inr hx).trans
      (Set.iUnion_congr fun c => (locRH_new c hjk (by omega)).2.2.2.symm)⟩

end Lineage

open Classical in
/-- **The kept labels of a history without removals up to `k`** are its labels at the kept positions
of the components of scale `k`, and `none` elsewhere. -/
theorem keptLab_eq_of_rem (A : LabHist S n R k0 K) {j k : ℕ} (hjk : j ≤ k) (hkK : k ≤ K)
    (hrem : ∀ i, i ≤ k → A.H.rem i = ∅) (c : Finset (Torus S.d (n j))) :
    A.keptLab j c = if ∃ Z : A.H.Comp k, (⟨j, c⟩ : KeptPos S n) ∈ A.H.keptPos k Z then
      some (A.lab j c) else none := by
  unfold LabHist.keptLab
  by_cases hc : c ∈ comps (S.omega j) (A.H.Zp j)
  · rw [dite_eq_left hc]
    have hr : c ∉ A.H.rem j := by rw [hrem j hjk]; exact Finset.notMem_empty _
    have e : (IsKept A.H j ⟨c, hc⟩ ∧ c ∉ A.H.rem j) ↔
        ∃ Z : A.H.Comp k, (⟨j, c⟩ : KeptPos S n) ∈ A.H.keptPos k Z := by
      constructor
      · rintro ⟨hk, -⟩
        obtain ⟨Z, hZ⟩ := exists_desc_of_rem A.H hjk hkK (fun i _ hi => hrem i (by omega)) ⟨c, hc⟩
        exact ⟨Z, mem_keptPos_of_desc A.H hZ hk⟩
      · rintro ⟨Z, hZ⟩
        obtain ⟨Y, -, hY1, hY2⟩ := exists_of_mem_keptPos A.H k Z _ hZ
        have hY : Y = ⟨c, hc⟩ := Subtype.ext hY1
        subst hY
        exact ⟨hY2, hr⟩
    by_cases h : ∃ Z : A.H.Comp k, (⟨j, c⟩ : KeptPos S n) ∈ A.H.keptPos k Z
    · rw [ite_eq_left h, ite_eq_left (e.2 h)]
    · rw [ite_eq_right h, ite_eq_right fun h' => h (e.1 h')]
  · rw [dite_eq_right hc]
    have : ¬ ∃ Z : A.H.Comp k, (⟨j, c⟩ : KeptPos S n) ∈ A.H.keptPos k Z := by
      rintro ⟨Z, hZ⟩
      obtain ⟨Y, -, hY1, -⟩ := exists_of_mem_keptPos A.H k Z _ hZ
      have hY1' : Y.1 = c := hY1
      exact hc (hY1' ▸ Y.2)
    rw [ite_eq_right this]

/-- Two families indexed by matched elements have the same union. -/
theorem iUnion_eq_of_forall_exists {α β γ : Type*} (f : α → Set γ) (g : β → Set γ)
    (h₁ : ∀ a, ∃ b, f a = g b) (h₂ : ∀ b, ∃ a, g b = f a) : ⋃ a, f a = ⋃ b, g b := by
  ext y
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨a, hy⟩
    obtain ⟨b, e⟩ := h₁ a
    exact ⟨b, e ▸ hy⟩
  · rintro ⟨b, hy⟩
    obtain ⟨a, e⟩ := h₂ b
    exact ⟨a, e ▸ hy⟩

section Records

variable (M : ℕ) [NeZero M]

open Classical in
/-- The kept positions of the lineage of a component with the labels of the history there. -/
noncomputable def labSet (A : LabHist S n R k0 K) {k : ℕ} (c : A.H.Comp k) :
    Finset (KeptPos S n × Fin 5) :=
  (A.H.keptPos k c).image fun p => (p, A.lab p.1 p.2)

theorem mem_labSet {A : LabHist S n R k0 K} {k : ℕ} {c : A.H.Comp k} {p : KeptPos S n}
    {ϰ : Fin 5} : (p, ϰ) ∈ labSet A c ↔ p ∈ A.H.keptPos k c ∧ A.lab p.1 p.2 = ϰ := by
  classical
  unfold labSet
  rw [Finset.mem_image]
  constructor
  · rintro ⟨q, hq, e⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
    exact ⟨hq, rfl⟩
  · rintro ⟨hp, rfl⟩
    exact ⟨p, hp, rfl⟩

/-- **The record of the component `c` of scale `k` of `𝔸`**: its cubes, its localized history and
its labels at its kept positions. -/
noncomputable def compRec (A : LabHist S n R k0 K) {k : ℕ} (c : A.H.Comp k) : CRec S n M K k :=
  (c.1, A.H.localHistory M K k c, labSet A c)

open Classical in
/-- **The records of the components of scale `k` of `𝔸`.** -/
noncomputable def lfRecs (k : ℕ) (A : LabHist S n R k0 K) : Finset (CRec S n M K k) :=
  Finset.univ.image fun c : A.H.Comp k => compRec M A c

omit [NeZero M] in
theorem mem_lfRecs {k : ℕ} {A : LabHist S n R k0 K} {r : CRec S n M K k} :
    r ∈ lfRecs M k A ↔ ∃ c : A.H.Comp k, compRec M A c = r := by
  classical
  simp [lfRecs]

/-- **Equal records give agreeing histories**: two histories without removals up to the scale `k`
whose components of scale `k` have the same records agree up to `k` (steps `j < k`, removals and
kept labels `j ≤ k`). The new cubes of a step are the unions of those of the localization steps
(`new_eq_iUnion_locRH`), which are functions of the localized histories; the kept labels are the
labels at the kept positions (`keptLab_eq_of_rem`), which are functions of the localized histories
(`keptPos_eq_of_localHistory_eq`). -/
theorem agree_of_lfRecs_eq {k : ℕ} (hkK : k ≤ K) {A B : LabHist S n R k0 K}
    (hA : ∀ i, i ≤ k → A.H.rem i = ∅) (hB : ∀ i, i ≤ k → B.H.rem i = ∅)
    (h : lfRecs M k A = lfRecs M k B) : A.Agree k (k + 1) B := by
  classical
  have mAB : ∀ cA : A.H.Comp k, ∃ cB : B.H.Comp k, compRec M A cA = compRec M B cB := by
    intro cA
    have hm : compRec M A cA ∈ lfRecs M k B := by rw [← h]; exact (mem_lfRecs M).2 ⟨cA, rfl⟩
    obtain ⟨cB, hcB⟩ := (mem_lfRecs M).1 hm
    exact ⟨cB, hcB.symm⟩
  have mBA : ∀ cB : B.H.Comp k, ∃ cA : A.H.Comp k, compRec M B cB = compRec M A cA := by
    intro cB
    have hm : compRec M B cB ∈ lfRecs M k A := by rw [h]; exact (mem_lfRecs M).2 ⟨cB, rfl⟩
    obtain ⟨cA, hcA⟩ := (mem_lfRecs M).1 hm
    exact ⟨cA, hcA.symm⟩
  have hst : ∀ {cA : A.H.Comp k} {cB : B.H.Comp k}, compRec M A cA = compRec M B cB → ∀ j,
      (A.H.locRH k cA).step j = (B.H.locRH k cB).step j := by
    intro cA cB e j
    exact locRH_step_eq_of_localHistory_eq hkK cA cB (congrArg Prod.fst e)
      (congrArg (fun r : CRec S n M K k => r.2.1) e) j
  have hkp : ∀ {cA : A.H.Comp k} {cB : B.H.Comp k}, compRec M A cA = compRec M B cB →
      A.H.keptPos k cA = B.H.keptPos k cB := fun {cA cB} e =>
    keptPos_eq_of_localHistory_eq k hkK A.H B.H cA cB (congrArg (fun r : CRec S n M K k => r.2.1) e)
  refine ⟨fun j hj => ?_, fun j hj => ⟨(hA j (by omega)).trans (hB j (by omega)).symm, ?_⟩⟩
  · obtain ⟨a1, a2, a3, a4⟩ := new_eq_iUnion_locRH A.H hj hkK (fun i _ hi => hA i (by omega))
    obtain ⟨b1, b2, b3, b4⟩ := new_eq_iUnion_locRH B.H hj hkK (fun i _ hi => hB i (by omega))
    have u : ∀ (f : RegionStep S.d S.L (n j) (n (j + 1)) (R (j - 1)) (R j) →
        Set (Torus S.d (n (j + 1)))),
        ⋃ cA : A.H.Comp k, f ((A.H.locRH k cA).step j) =
          ⋃ cB : B.H.Comp k, f ((B.H.locRH k cB).step j) := fun f =>
      iUnion_eq_of_forall_exists _ _
        (fun cA => (mAB cA).imp fun cB e => by rw [hst e j])
        (fun cB => (mBA cB).imp fun cA e => by rw [hst e.symm j])
    exact ⟨a1.trans ((u fun st => st.P).trans b1.symm), a2.trans ((u fun st => st.Q).trans b2.symm),
      a3.trans ((u fun st => st.R).trans b3.symm), a4.trans ((u fun st => st.S).trans b4.symm)⟩
  · funext c
    rw [keptLab_eq_of_rem A (by omega) hkK hA c, keptLab_eq_of_rem B (by omega) hkK hB c]
    have hiff : (∃ Z : A.H.Comp k, (⟨j, c⟩ : KeptPos S n) ∈ A.H.keptPos k Z) ↔
        ∃ Z : B.H.Comp k, (⟨j, c⟩ : KeptPos S n) ∈ B.H.keptPos k Z := by
      constructor
      · rintro ⟨cA, hcA⟩
        obtain ⟨cB, e⟩ := mAB cA
        exact ⟨cB, hkp e ▸ hcA⟩
      · rintro ⟨cB, hcB⟩
        obtain ⟨cA, e⟩ := mBA cB
        exact ⟨cA, hkp e.symm ▸ hcB⟩
    by_cases hex : ∃ Z : A.H.Comp k, (⟨j, c⟩ : KeptPos S n) ∈ A.H.keptPos k Z
    · rw [ite_eq_left hex, ite_eq_left (hiff.1 hex)]
      obtain ⟨cA, hcA⟩ := hex
      obtain ⟨cB, e⟩ := mAB cA
      have hl : ((⟨j, c⟩ : KeptPos S n), A.lab j c) ∈ labSet B cB := by
        have e2 : labSet A cA = labSet B cB := congrArg (fun r : CRec S n M K k => r.2.2) e
        rw [← e2]
        exact mem_labSet.2 ⟨hcA, rfl⟩
      rw [(mem_labSet.1 hl).2]
    · rw [ite_eq_right hex, ite_eq_right fun h' => hex (hiff.2 h')]

/-- **Agreeing histories have the same records**: the components of scale `k` are identified
(`HAgr.cmap`), with the same localized histories (`HAgr.localHistory_eq`), the same kept positions
and the same labels there (`lab_eq_of_agree`). -/
theorem lfRecs_eq_of_agree {k : ℕ} (hkK : k ≤ K) {A B : LabHist S n R k0 K}
    (hA : ∀ i, i ≤ k → A.H.rem i = ∅) (h : A.Agree k (k + 1) B) :
    lfRecs M k A = lfRecs M k B := by
  classical
  have hH := HAgr.of_agree h
  have key : ∀ cA : A.H.Comp k, compRec M B (hH.cmap le_rfl cA) = compRec M A cA := by
    intro cA
    have hlh := hH.localHistory_eq le_rfl M K cA
    have hkp : B.H.keptPos k (hH.cmap le_rfl cA) = A.H.keptPos k cA :=
      keptPos_eq_of_localHistory_eq k hkK B.H A.H _ cA hlh
    refine Prod.ext (hH.cmap_val le_rfl cA) (Prod.ext hlh ?_)
    show labSet B _ = labSet A cA
    unfold labSet
    rw [hkp]
    refine Finset.image_congr fun p hp => ?_
    obtain ⟨Y, hd, hY1, hY2⟩ := exists_of_mem_keptPos A.H k cA p hp
    have hr : Y.1 ∉ A.H.rem p.1 := by rw [hA p.1 hd.le]; exact Finset.notMem_empty _
    have hl := lab_eq_of_agree h hd.le Y hY2 hr
    rw [hY1] at hl
    simp only [hl]
  ext r
  rw [mem_lfRecs, mem_lfRecs]
  constructor
  · rintro ⟨cA, rfl⟩
    exact ⟨hH.cmap le_rfl cA, key cA⟩
  · rintro ⟨cB, rfl⟩
    refine ⟨(hH.cequiv le_rfl).symm cB, ?_⟩
    have e : hH.cmap le_rfl ((hH.cequiv le_rfl).symm cB) = cB :=
      (hH.cequiv le_rfl).apply_symm_apply cB
    rw [← key, e]

/-- **The records are injective on the histories of the large-field half** of a complete set:
equal records give agreeing histories (`agree_of_lfRecs_eq`), and a complete set has one history in
each class. -/
theorem lfRecs_injOn {k : ℕ} (hkK : k ≤ K) {hist : Finset (LabHist S n R k0 K)}
    (hc : IsComplete k (k + 1) hist) :
    Set.InjOn (lfRecs M k) (lfHist hist k : Set (LabHist S n R k0 K)) := by
  intro A hA B hB h
  obtain ⟨hA1, -, hA3⟩ := mem_lfHist.1 (Finset.mem_coe.1 hA)
  obtain ⟨hB1, -, hB3⟩ := mem_lfHist.1 (Finset.mem_coe.1 hB)
  have hAB := agree_of_lfRecs_eq M hkK hA3 hB3 h
  obtain ⟨C, -, hCu⟩ := hc A
  exact (hCu A ⟨hA1, LabHist.agree_refl _ _ A⟩).trans (hCu B ⟨hB1, hAB⟩).symm

end Records

end Balaban.RootFSpine
