/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.FinalLFHistFactor
public import Balaban.Spine.FinalLFHistGlue

/-!
# The histories of the large-field half as separated families of component records (A6-4)

The second half of the history factorization (`notes/phase1/A64-DESIGN.md` §2): the records of the
histories `lfHist` of a complete set (`lfRecs`, `Spine/FinalLFHistFactor.lean`) are exactly the
nonempty families of realized component records that are pairwise `ω_k`-separated.

* `Realized`: a record is the record of a component of scale `k` of some labelled history;
  `RecSep`: the records of a family are pairwise at index distance `≥ ω_k`;
* `exists_labHist_of_sep`: a nonempty separated family of realized records is the family of
  records of a labelled history without removals (the assembly without a common witness,
  `exists_assembled_of_sepZ`, with the labels glued at the kept positions);
* **`mem_image_lfRecs_iff`**: `Γ` is the family of records of a history of `lfHist` iff `Γ` is a
  nonempty separated family of realized records (the representative in the complete set);
* `lfAllRecs`, `mem_lfAllRecs_iff`: the realized records, as a finite set;
* **`sum_lfHist_eq_sum_sep`**: `∑_{𝔸 ∈ lfHist} f(lfRecs 𝔸) = ∑_Γ f(Γ)` over the nonempty pairwise
  `ω_k`-separated families `Γ` of realized records.
-/

@[expose] public section

open Balaban Balaban.LargeField Balaban.LargeField.Def7 RegionHistory

namespace Balaban.RootFSpine

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {M K : ℕ} [NeZero M]

/-- A record is **realized** if it is the record of a component of scale `k` of some labelled
history. -/
def Realized (R : ℕ → ℝ) (k0 : ℕ) {k : ℕ} (r : CRec S n M K k) : Prop :=
  ∃ s : (Σ A : LabHist S n R k0 K, A.H.Comp k), compRec M s.1 s.2 = r

/-- The records of a family are **pairwise `ω_k`-separated**: the cubes of two distinct records are
at index distance `≥ ω_k`. -/
def RecSep (k : ℕ) (Γ : Finset (CRec S n M K k)) : Prop :=
  ∀ r ∈ Γ, ∀ r' ∈ Γ, r ≠ r' → ∀ x ∈ r.1, ∀ y ∈ r'.1, S.omega k ≤ supDist x y

variable {R : ℕ → ℝ} {k0 : ℕ}

omit [NeZero M] in
/-- A family of at most one record is separated. -/
theorem recSep_singleton {k : ℕ} (r : CRec S n M K k) : RecSep k {r} := by
  intro a ha b hb hab
  rw [Finset.mem_singleton] at ha hb
  exact absurd (ha.trans hb.symm) hab

/-- **A nonempty separated family of records with given sources is the family of records of a
history without removals**: the components of the sources occur in one history without removals
with the same localized histories (`exists_assembled_of_sepZ`), and its labels are glued at the kept
positions (which are distinct for distinct records, since their lineages are separated). -/
theorem exists_labHist_of_src {k : ℕ} (hkK : k ≤ K) {Γ : Finset (CRec S n M K k)}
    (src : CRec S n M K k → Σ A : LabHist S n R k0 K, A.H.Comp k)
    (hsrc : ∀ r ∈ Γ, compRec M (src r).1 (src r).2 = r) (hsep : RecSep k Γ)
    (F0 : FlowSteps S n R k0 K) :
    ∃ A : LabHist S n R k0 K, (∀ j, A.H.rem j = ∅) ∧ lfRecs M k A = Γ := by
  classical
  have hω : 0 < S.omega k := by
    have h := le_omegaW S.L S.Rb S.lam k
    rw [← Setting.omega_eq_omegaW] at h
    omega
  have hfst : ∀ r ∈ Γ, ((src r).2).1 = r.1 := fun r hr => congrArg Prod.fst (hsrc r hr)
  have hsepZ : ∀ i ∈ Γ, ∀ i' ∈ Γ, i ≠ i' → ∀ x ∈ ((src i).2).1, ∀ y ∈ ((src i').2).1,
      S.omega k ≤ supDist x y := by
    intro i hi i' hi' hne x hx y hy
    exact hsep i hi i' hi' hne x (hfst i hi ▸ hx) y (hfst i' hi' ▸ hy)
  have hcomps : ∀ i ∈ Γ, comps (S.omega k) ((src i).2).1 = {((src i).2).1} := by
    intro i _
    have h := locRH_comps hkK (src i).2
    rwa [locRH_Zp hkK] at h
  obtain ⟨H, hrem, hcov, hloc⟩ := exists_assembled_of_sepZ (M := M) (F := Γ)
    (Hm := fun r => (src r).1.H) (cm := fun r => (src r).2) F0 hkK hsepZ hcomps
  -- the kept positions of the sources are distinct for distinct records
  have huniq : ∀ r ∈ Γ, ∀ r' ∈ Γ, ∀ p : KeptPos S n, p ∈ (src r).1.H.keptPos k (src r).2 →
      p ∈ (src r').1.H.keptPos k (src r').2 → r = r' := by
    intro r hr r' hr' p hp hp'
    obtain ⟨Y, hd, hY1, -⟩ := exists_of_mem_keptPos (src r).1.H k (src r).2 p hp
    obtain ⟨Y', hd', hY1', -⟩ := exists_of_mem_keptPos (src r').1.H k (src r').2 p hp'
    obtain ⟨y, hy⟩ := comp_nonempty Y.2
    have hy' : y ∈ Y'.1 := hY1' ▸ hY1 ▸ hy
    have h1 : y ∈ (((src r).1.H.lin p.1 k (src r).2 : Finset _) : Set (Torus S.d (n p.1))) :=
      Finset.mem_coe.2 (mem_lin.2 ⟨Y, hd, hy⟩)
    have h2 : y ∈ (((src r').1.H.lin p.1 k (src r').2 : Finset _) : Set (Torus S.d (n p.1))) :=
      Finset.mem_coe.2 (mem_lin.2 ⟨Y', hd', hy'⟩)
    obtain ⟨z1, hz1, z2, hz2, hz⟩ := exists_over_of_mem_lin hd.le hkK h1 h2
    by_contra hne
    have := hsepZ r hr r' hr' hne z1 hz1 z2 hz2
    rw [supDist_self] at hz
    omega
  -- the glued labels: at a kept position of a source, the label of that source
  let lab : ∀ j, Finset (Torus S.d (n j)) → Fin 5 := fun j c =>
    if h : ∃ r ∈ Γ, (⟨j, c⟩ : KeptPos S n) ∈ (src r).1.H.keptPos k (src r).2 then
      (src h.choose).1.lab j c else 0
  let A : LabHist S n R k0 K :=
    { H := H
      adm := fun j c hc => absurd hc (by rw [hrem j]; exact Finset.notMem_empty _)
      lab := lab }
  -- the record of a component of `A` matched with `r`
  have hrec : ∀ r ∈ Γ, ∀ c : H.Comp k, c.1 = ((src r).2).1 →
      H.localHistory M K k c = (src r).1.H.localHistory M K k (src r).2 → compRec M A c = r := by
    intro r hr c hc1 hc2
    refine Eq.trans ?_ (hsrc r hr)
    have hkp : H.keptPos k c = (src r).1.H.keptPos k (src r).2 :=
      keptPos_eq_of_localHistory_eq k hkK H (src r).1.H c (src r).2 hc2
    refine Prod.ext hc1 (Prod.ext hc2 ?_)
    show labSet A c = labSet (src r).1 (src r).2
    unfold labSet
    change (H.keptPos k c).image (fun p => (p, lab p.1 p.2)) = _
    rw [hkp]
    refine Finset.image_congr fun p hp => ?_
    have hex : ∃ r' ∈ Γ, (⟨p.1, p.2⟩ : KeptPos S n) ∈ (src r').1.H.keptPos k (src r').2 :=
      ⟨r, hr, hp⟩
    have e : hex.choose = r := huniq _ hex.choose_spec.1 r hr _ hex.choose_spec.2 hp
    show (p, (if h : ∃ r' ∈ Γ, (⟨p.1, p.2⟩ : KeptPos S n) ∈ (src r').1.H.keptPos k (src r').2 then
      (src h.choose).1.lab p.1 p.2 else 0)) = _
    rw [dite_eq_left hex, e]
  refine ⟨A, hrem, ?_⟩
  ext r
  rw [mem_lfRecs]
  constructor
  · rintro ⟨c, rfl⟩
    obtain ⟨r', hr', hc'⟩ := hcov c
    obtain ⟨c'', hc''1, hc''2⟩ := hloc r' hr'
    have e : c'' = c := Subtype.ext (hc''1.trans hc')
    subst e
    rw [hrec r' hr' c'' hc''1 hc''2]
    exact hr'
  · intro hr
    obtain ⟨c, hc1, hc2⟩ := hloc r hr
    exact ⟨c, hrec r hr c hc1 hc2⟩

/-- **A nonempty separated family of realized records is the family of records of a history without
removals.** -/
theorem exists_labHist_of_sep {k : ℕ} (hkK : k ≤ K) {Γ : Finset (CRec S n M K k)}
    (hne : Γ.Nonempty) (hreal : ∀ r ∈ Γ, Realized R k0 r) (hsep : RecSep k Γ) :
    ∃ A : LabHist S n R k0 K, (∀ j, A.H.rem j = ∅) ∧ lfRecs M k A = Γ := by
  classical
  obtain ⟨r0, hr0⟩ := hne
  obtain ⟨s0, -⟩ := hreal r0 hr0
  have hs : ∀ r : CRec S n M K k, ∃ s : (Σ A : LabHist S n R k0 K, A.H.Comp k),
      r ∈ Γ → compRec M s.1 s.2 = r := by
    intro r
    by_cases hr : r ∈ Γ
    · obtain ⟨s, h⟩ := hreal r hr
      exact ⟨s, fun _ => h⟩
    · exact ⟨s0, fun h => absurd h hr⟩
  choose src hsrc using hs
  exact exists_labHist_of_src hkK src hsrc hsep s0.1.H.F

open Classical in
/-- **The families of records of the histories of the large-field half** of a complete set are
exactly the nonempty pairwise `ω_k`-separated families of realized records. Forward: the components
of `Z_k` are separated (`comps_sep`); backward: the history without removals with these records
(`exists_labHist_of_sep`) has a representative in the complete set, which lies in `lfHist` and has
the same records (`lfRecs_eq_of_agree`). -/
theorem mem_image_lfRecs_iff {k : ℕ} (hkK : k ≤ K) {hist : Finset (LabHist S n R k0 K)}
    (hc : IsComplete k (k + 1) hist) (Γ : Finset (CRec S n M K k)) :
    Γ ∈ (lfHist hist k).image (lfRecs M k) ↔
      Γ.Nonempty ∧ (∀ r ∈ Γ, Realized R k0 r) ∧ RecSep k Γ := by
  classical
  constructor
  · rintro hΓ
    obtain ⟨A, hA, rfl⟩ := Finset.mem_image.1 hΓ
    obtain ⟨-, hA2, -⟩ := mem_lfHist.1 hA
    refine ⟨?_, ?_, ?_⟩
    · rw [lastRegion_eq_empty_iff] at hA2
      obtain ⟨y, hy⟩ := Set.nonempty_iff_ne_empty.2 hA2
      obtain ⟨Y, hY, -⟩ := mem_comp_self (ω := S.omega k) (mem_finOf.mpr (A.H.Z_subset_Zpre k hy))
      exact ⟨_, (mem_lfRecs M).2 ⟨⟨Y, hY⟩, rfl⟩⟩
    · intro r hr
      obtain ⟨c, rfl⟩ := (mem_lfRecs M).1 hr
      exact ⟨⟨A, c⟩, rfl⟩
    · intro r hr r' hr' hne x hx y hy
      obtain ⟨c, rfl⟩ := (mem_lfRecs M).1 hr
      obtain ⟨c', rfl⟩ := (mem_lfRecs M).1 hr'
      have hcc : c.1 ≠ c'.1 := fun e => hne (by rw [Subtype.ext e])
      exact comps_sep c.2 c'.2 hcc hx hy
  · rintro ⟨hne, hreal, hsep⟩
    obtain ⟨A, hrem, hrec⟩ := exists_labHist_of_sep hkK hne hreal hsep
    obtain ⟨B, ⟨hB, hAB⟩, -⟩ := hc A
    refine Finset.mem_image.2 ⟨B, mem_lfHist.2 ⟨hB, ?_, fun j (hj : j ≤ k) =>
      ((hAB.2 j (by omega)).1).symm.trans (hrem j)⟩, ?_⟩
    · rw [lastRegion_eq_empty_iff, ← LabHist.Agree.region_eq (Nat.lt_succ_self k) hAB k le_rfl]
      obtain ⟨r, hr⟩ := hne
      rw [← hrec] at hr
      obtain ⟨c, -⟩ := (mem_lfRecs M).1 hr
      obtain ⟨y, hy⟩ := comp_nonempty c.2
      have hZ : y ∈ (A.H.step k).Z := (A.H.mem_Z_iff (Y := c) hy).2 (by
        rw [hrem k]; exact Finset.notMem_empty _)
      exact Set.nonempty_iff_ne_empty.1 ⟨y, hZ⟩
    · rw [← lfRecs_eq_of_agree M hkK (fun i _ => hrem i) hAB, hrec]

open Classical in
/-- **The realized records**, as a finite set: the records of the components of the histories of the
large-field half of a complete set. -/
noncomputable def lfAllRecs (hist : Finset (LabHist S n R k0 K)) (k : ℕ) :
    Finset (CRec S n M K k) :=
  ((lfHist hist k).image (lfRecs M k)).biUnion id

/-- The finite set `lfAllRecs` is the set of realized records. -/
theorem mem_lfAllRecs_iff {k : ℕ} (hkK : k ≤ K) {hist : Finset (LabHist S n R k0 K)}
    (hc : IsComplete k (k + 1) hist) (r : CRec S n M K k) :
    r ∈ lfAllRecs (M := M) hist k ↔ Realized R k0 r := by
  classical
  unfold lfAllRecs
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨Γ, hΓ, hr⟩
    exact ((mem_image_lfRecs_iff hkK hc Γ).1 hΓ).2.1 r hr
  · intro hr
    refine ⟨{r}, (mem_image_lfRecs_iff hkK hc {r}).2 ⟨Finset.singleton_nonempty r, ?_,
      recSep_singleton r⟩, Finset.mem_singleton_self r⟩
    intro r' hr'
    rw [Finset.mem_singleton] at hr'
    exact hr' ▸ hr

open Classical in
/-- **The history factorization as a sum**: for a complete set, a sum over the histories of the
large-field half of a function of their records is the sum over the nonempty pairwise
`ω_k`-separated families of realized records. -/
theorem sum_lfHist_eq_sum_sep {β : Type*} [AddCommMonoid β] {k : ℕ} (hkK : k ≤ K)
    {hist : Finset (LabHist S n R k0 K)} (hc : IsComplete k (k + 1) hist)
    (f : Finset (CRec S n M K k) → β) :
    ∑ A ∈ lfHist hist k, f (lfRecs M k A) =
      ∑ Γ ∈ (lfAllRecs (M := M) hist k).powerset.filter (fun Γ => Γ.Nonempty ∧ RecSep k Γ),
        f Γ := by
  classical
  rw [← Finset.sum_image (lfRecs_injOn M hkK hc)]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext Γ
  rw [mem_image_lfRecs_iff hkK hc, Finset.mem_filter, Finset.mem_powerset]
  constructor
  · rintro ⟨hne, hreal, hsep⟩
    exact ⟨fun r hr => (mem_lfAllRecs_iff hkK hc r).2 (hreal r hr), hne, hsep⟩
  · rintro ⟨hsub, hne, hsep⟩
    exact ⟨hne, fun r hr => (mem_lfAllRecs_iff hkK hc r).1 (hsub hr), hsep⟩

end Balaban.RootFSpine
