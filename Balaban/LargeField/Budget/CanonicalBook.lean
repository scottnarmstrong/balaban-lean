module

public import Balaban.LargeField.Budget.RecordForward
public import Balaban.LargeField.Budget.Exponents

/-!
# The bookkeeping is a function of the localized history (Definition I.4.7, R3-12, O-9)

The spine of a component is chosen (`RegionHistory.nextSpine`) by `Classical.choose` among the
spines satisfying `SpineOK`, a property of `Z'`, of the spines of its old parts and of the number
of new cubes in `Z'` only.  We show that the choice, hence the whole book, is a function of the
localized history:

* `Setting.nextBook_congr`: the book after a step only depends on the *set* of old parts (given as
  an image in a common type) and their books;
* `RegionHistory.SpineOK_iff`: `SpineOK` is a property of `Z'`, of the old parts as a set of
  cubes, and of their spines;
* `RegionHistory.bk_eq_of_localHistory_eq`: if `localHistory H₁ M K k Z₁ = localHistory H₂ M K k Z₂`
  then `Z₁ = Z₂` (as sets of cubes) and `H₁.spine k Z₁ = H₂.spine k Z₂`, `H₁.bk k Z₁ = H₂.bk k Z₂`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban

section NextBook

variable (S : Setting) {ι α : Type*} (μ : ℕ)

/-- A default book (used only off the support of the old parts). -/
def Book.dflt : Book := { st := .pre, s := 0, len := 0, pt := False }

open Classical in
theorem Setting.nextBook_image (e : ι → α) (he : Function.Injective e) (parts : Finset ι)
    (f : ι → Book) (g : α → Book) (hfg : ∀ i ∈ parts, f i = g (e i)) (r : ℕ) (Γ : Spine S.d) :
    S.nextBook μ parts f r Γ = S.nextBook μ (parts.image e) g r Γ := by
  have hcard : (parts.image e).card = parts.card := Finset.card_image_of_injective _ he
  have hsup : parts.sup (fun i => (f i).s) = (parts.image e).sup (fun a => (g a).s) := by
    rw [Finset.sup_image]
    exact Finset.sup_congr rfl fun i hi => by simp [Function.comp, hfg i hi]
  have hall : (∀ i ∈ parts, (f i).pt) ↔ ∀ a ∈ parts.image e, (g a).pt := by
    rw [Finset.forall_mem_image]
    exact forall₂_congr fun i hi => by rw [hfg i hi]
  have hex : (∃ i ∈ parts, (f i).st = .pre) ↔ ∃ a ∈ parts.image e, (g a).st = .pre := by
    constructor
    · rintro ⟨i, hi, h⟩
      exact ⟨e i, Finset.mem_image_of_mem _ hi, by rw [← hfg i hi]; exact h⟩
    · rintro ⟨a, ha, h⟩
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
      exact ⟨i, hi, by rw [hfg i hi]; exact h⟩
  have hnu : ∑ i ∈ parts, (f i).nu = ∑ a ∈ parts.image e, (g a).nu := by
    rw [Finset.sum_image (fun i _ j _ h => he h)]
    exact Finset.sum_congr rfl fun i hi => by rw [hfg i hi]
  have hq : parts.sup (fun i => (f i).q) = (parts.image e).sup (fun a => (g a).q) := by
    rw [Finset.sup_image]
    exact Finset.sup_congr rfl fun i hi => by simp [Function.comp, hfg i hi]
  have hM : parts.biUnion (fun i => (f i).M) = (parts.image e).biUnion (fun a => (g a).M) := by
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_image]
    constructor
    · rintro ⟨i, hi, hx⟩
      exact ⟨e i, ⟨i, hi, rfl⟩, by rw [← hfg i hi]; exact hx⟩
    · rintro ⟨a, ⟨i, hi, rfl⟩, hx⟩
      exact ⟨i, hi, by rw [hfg i hi]; exact hx⟩
  have hclock : S.nextClock μ parts f r Γ.length = S.nextClock μ (parts.image e) g r Γ.length := by
    unfold Setting.nextClock
    simp only [hcard, hsup, hall]
  have ht4 : ∀ s', S.t4State μ parts f s' = S.t4State μ (parts.image e) g s' := by
    intro s'
    have hQ : t4Q parts f = t4Q (parts.image e) g := hq
    have hE : t4E μ parts f = t4E μ (parts.image e) g := by
      unfold t4E; rw [hM]
    have hT : S.t4T μ parts f s' = S.t4T μ (parts.image e) g s' := by
      unfold Setting.t4T Setting.t4t0
      rw [hE, hQ]
    have hq' : S.t4q μ parts f s' = S.t4q μ (parts.image e) g s' := by
      unfold Setting.t4q; rw [hT]
    unfold Setting.t4State
    rw [hq', hE, hnu]
  have hstate : ∀ s' pt', S.nextState μ parts f r pt' s' =
      S.nextState μ (parts.image e) g r pt' s' := by
    intro s' pt'
    unfold Setting.nextState
    by_cases h : parts.card = 1
    · obtain ⟨i, hi⟩ := Finset.card_eq_one.mp h
      have hi' : parts.image e = {e i} := by rw [hi]; simp
      have hmem : i ∈ parts := by rw [hi]; simp
      have h' : (parts.image e).card = 1 := by rw [hcard]; exact h
      have hc : (Finset.card_eq_one.mp h).choose = i :=
        Finset.singleton_injective ((Finset.card_eq_one.mp h).choose_spec.symm.trans hi)
      have hc' : (Finset.card_eq_one.mp h').choose = e i :=
        Finset.singleton_injective ((Finset.card_eq_one.mp h').choose_spec.symm.trans hi')
      simp only [h, h', ↓reduceDIte, hc, hc', hfg i hmem]
    · have h' : ¬ (parts.image e).card = 1 := by rw [hcard]; exact h
      simp only [h, h', hex, hnu, ht4, ↓reduceDIte]
  unfold Setting.nextBook
  rw [hclock, hstate]

open Classical in
/-- The book after a step depends on the old parts only through their images in a common type and
the books on these images. -/
theorem Setting.nextBook_congr {ι' : Type*} (e : ι → α) (he : Function.Injective e)
    (e' : ι' → α) (he' : Function.Injective e') (parts : Finset ι) (parts' : Finset ι')
    (f : ι → Book) (f' : ι' → Book) (hparts : parts.image e = parts'.image e')
    (hf : ∀ i ∈ parts, ∀ i' ∈ parts', e i = e' i' → f i = f' i') (r : ℕ) (Γ : Spine S.d) :
    S.nextBook μ parts f r Γ = S.nextBook μ parts' f' r Γ := by
  let g : α → Book := fun a => if h : ∃ i ∈ parts, e i = a then f h.choose else Book.dflt
  have hg : ∀ i ∈ parts, f i = g (e i) := by
    intro i hi
    have h : ∃ j ∈ parts, e j = e i := ⟨i, hi, rfl⟩
    simp only [g, h, ↓reduceDIte]
    have := h.choose_spec
    rw [he this.2]
  have hg' : ∀ i' ∈ parts', f' i' = g (e' i') := by
    intro i' hi'
    have hmem : e' i' ∈ parts.image e := by rw [hparts]; exact Finset.mem_image_of_mem _ hi'
    obtain ⟨j, hj, hje⟩ := Finset.mem_image.mp hmem
    have h : ∃ j ∈ parts, e j = e' i' := ⟨j, hj, hje⟩
    simp only [g, h, ↓reduceDIte]
    exact (hf _ h.choose_spec.1 i' hi' h.choose_spec.2).symm
  rw [S.nextBook_image μ e he parts f g hg, S.nextBook_image μ e' he' parts' f' g hg', hparts]

end NextBook

namespace RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}

/-- `SpineOK` with the old parts given as a set `Ys` of cubes-sets and their spines as a function
`G` on cubes-sets. -/
def SpineOKO (S : Setting) (n : ℕ → ℕ) [∀ k, NeZero (n k)] (k0 k : ℕ)
    (Zf : Finset (Torus S.d (n (k + 1)))) (Ys : Finset (Finset (Torus S.d (n k))))
    (G : Finset (Torus S.d (n k)) → Spine S.d) (nn : ℕ) (Γ' : Spine S.d) : Prop :=
  (Zf : Set (Torus S.d (n (k + 1)))) ⊆ NR ((S.rho (k + 1) : ℝ) + 4) (Γ'.proj (n (k + 1))) ∧
  Γ'.length ≤ ∑ Y ∈ Ys, (G Y).length / S.L +
      ((((Ys.card + nn : ℕ) : ℝ) - 1) * S.D (k + 1)) ∧
  (nn = 0 → ∀ Y, Ys = {Y} → (G Y).length ≤ S.L → Γ'.length = 0) ∧
  (k + 1 ≤ k0 → IsSmall (Zf : Set (Torus S.d (n (k + 1)))) →
    side (Zf : Set (Torus S.d (n (k + 1)))) ≤ S.crit (k + 1) →
    ∃ (a : Torus S.d (n (k + 1))) (s : Fin S.d → ℕ),
      (Zf : Set (Torus S.d (n (k + 1)))) = box a s ∧
      Γ'.length = 0 ∧ Γ'.proj (n (k + 1)) = {boxCentre a s})

theorem SpineOKO_congr (k0 k : ℕ) (Zf : Finset (Torus S.d (n (k + 1))))
    (Ys : Finset (Finset (Torus S.d (n k)))) {G G' : Finset (Torus S.d (n k)) → Spine S.d}
    (hG : ∀ Y ∈ Ys, G Y = G' Y) (nn : ℕ) (Γ' : Spine S.d) :
    SpineOKO S n k0 k Zf Ys G nn Γ' ↔ SpineOKO S n k0 k Zf Ys G' nn Γ' := by
  unfold SpineOKO
  have hs : ∑ Y ∈ Ys, (G Y).length / S.L = ∑ Y ∈ Ys, (G' Y).length / S.L :=
    Finset.sum_congr rfl fun Y hY => by rw [hG Y hY]
  rw [hs]
  refine and_congr Iff.rfl (and_congr Iff.rfl (and_congr ?_ Iff.rfl))
  refine forall_congr' fun _ => forall_congr' fun Y => forall_congr' fun hY => ?_
  have : Y ∈ Ys := by rw [hY]; exact Finset.mem_singleton_self Y
  rw [hG Y this]

/-- The spine of a component of `Z^pre_k` as a function of the cube set (a default off the
components). -/
noncomputable def spineO (H : RegionHistory S n R k0 K) (k : ℕ) (Y : Finset (Torus S.d (n k))) :
    Spine S.d :=
  open Classical in
  if h : Y ∈ comps (S.omega k) (H.Zp k) then H.spine k ⟨Y, h⟩ else Spine.point 0

theorem spineO_comp (H : RegionHistory S n R k0 K) (k : ℕ) (c : H.Comp k) :
    H.spineO k c.1 = H.spine k c := by
  classical
  simp [spineO, c.2]

theorem SpineOK_iff (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k < K) (Z' : H.Comp (k + 1))
    (Γ' : Spine S.d) :
    H.SpineOK k (H.spine k) Z' Γ' ↔
      SpineOKO S n k0 k Z'.1 (comps (S.omega k) (H.oldCubes k Z')) (H.spineO k)
        (Z'.1 ∩ H.newCubes (k + 1)).card Γ' := by
  classical
  have hI := H.parts_image_eq_comps hk Z'
  have hsum : ∑ Y ∈ comps (S.omega k) (H.oldCubes k Z'), (H.spineO k Y).length / S.L =
      ∑ c ∈ H.parts k Z', (H.spine k c).length / S.L := by
    rw [← hI, Finset.sum_image (fun _ _ _ _ h => Subtype.val_injective h)]
    exact Finset.sum_congr rfl fun c _ => by rw [H.spineO_comp]
  have hcard : (comps (S.omega k) (H.oldCubes k Z')).card = (H.parts k Z').card := by
    rw [← hI, Finset.card_image_of_injective _ Subtype.val_injective]
  unfold SpineOK SpineOKO
  rw [hsum, hcard]
  refine and_congr Iff.rfl (and_congr Iff.rfl (and_congr ?_ Iff.rfl))
  refine imp_congr_right fun _ => ?_
  constructor
  · intro h3 Y hY hL
    have hc : (H.parts k Z').card = 1 := by rw [← hcard, hY]; simp
    obtain ⟨c, hc'⟩ := Finset.card_eq_one.mp hc
    have hYc : Y = c.1 := by
      rw [← hI, hc'] at hY
      simpa using hY.symm
    subst hYc
    refine h3 c hc' ?_
    rw [← H.spineO_comp]; exact hL
  · intro h3 c hc hL
    refine h3 c.1 ?_ ?_
    · rw [← hI, hc]; simp
    · rw [H.spineO_comp]; exact hL

theorem dite_choose_congr {P Q : Spine S.d → Prop} (h : P = Q) (x : Spine S.d) :
    (open Classical in if hp : ∃ Γ, P Γ then hp.choose else x) =
      (open Classical in if hq : ∃ Γ, Q Γ then hq.choose else x) := by
  subst h; rfl

open Classical in
theorem spine_succ_eq (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k < K) (Z' : H.Comp (k + 1)) :
    H.spine (k + 1) Z' =
      if h : ∃ Γ', SpineOKO S n k0 k Z'.1 (comps (S.omega k) (H.oldCubes k Z')) (H.spineO k)
          (Z'.1 ∩ H.newCubes (k + 1)).card Γ' then h.choose else Spine.point 0 := by
  have hp : (fun Γ' => H.SpineOK k (H.spine k) Z' Γ') =
      (fun Γ' => SpineOKO S n k0 k Z'.1 (comps (S.omega k) (H.oldCubes k Z')) (H.spineO k)
        (Z'.1 ∩ H.newCubes (k + 1)).card Γ') :=
    funext fun Γ' => propext (H.SpineOK_iff hk Z' Γ')
  show H.nextSpine k (H.spine k) Z' = _
  unfold nextSpine
  exact dite_choose_congr hp _

theorem mem_Zp_of_old (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k < K) (Z' : H.Comp (k + 1))
    {Y : Finset (Torus S.d (n k))} (hY : Y ∈ comps (S.omega k) (H.oldCubes k Z')) :
    Y ∈ comps (S.omega k) (H.Zp k) := by
  classical
  rw [← H.parts_image_eq_comps hk Z'] at hY
  obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp hY
  exact c.2

variable {M K : ℕ} [NeZero M]

/-- **The spine and the book of a component are functions of its localized history.** -/
theorem spine_bk_eq_of_localHistory_eq :
    ∀ (k : ℕ), k ≤ K → ∀ (H1 H2 : RegionHistory S n R k0 K) (Z1 : H1.Comp k) (Z2 : H2.Comp k),
      localHistory H1 M K k Z1 = localHistory H2 M K k Z2 →
      Z1.1 = Z2.1 ∧ H1.spine k Z1 = H2.spine k Z2 ∧ H1.bk k Z1 = H2.bk k Z2 := by
  classical
  intro k
  induction k with
  | zero => intro _ H1 _ Z1; exact (H1.F.isEmpty_comp_zero.false Z1).elim
  | succ k ih =>
    intro hkK H1 H2 Z1 Z2 h
    obtain ⟨hZ, hold, hnew, hfam⟩ := record_forward hkK Z1 Z2 h
    have hnn : (Z1.1 ∩ H1.newCubes (k + 1)).card = (Z2.1 ∩ H2.newCubes (k + 1)).card := by
      rw [hnew]
    have hmem1 := fun Y (hY : Y ∈ comps (S.omega k) (H1.oldCubes k Z1)) =>
      mem_Zp_of_old H1 (by omega) Z1 hY
    have hmem2 := fun Y (hY : Y ∈ comps (S.omega k) (H1.oldCubes k Z1)) =>
      mem_Zp_of_old H2 (by omega) Z2 (hold ▸ hY)
    have hih : ∀ Y (hY : Y ∈ comps (S.omega k) (H1.oldCubes k Z1)),
        H1.spine k ⟨Y, hmem1 Y hY⟩ = H2.spine k ⟨Y, hmem2 Y hY⟩ ∧
        H1.bk k ⟨Y, hmem1 Y hY⟩ = H2.bk k ⟨Y, hmem2 Y hY⟩ := fun Y hY =>
      (ih (by omega) H1 H2 ⟨Y, hmem1 Y hY⟩ ⟨Y, hmem2 Y hY⟩
        (hfam Y (hmem1 Y hY) (hmem2 Y hY) hY)).2
    have hspO : ∀ Y ∈ comps (S.omega k) (H1.oldCubes k Z1), H1.spineO k Y = H2.spineO k Y := by
      intro Y hY
      have e1 := H1.spineO_comp k ⟨Y, hmem1 Y hY⟩
      have e2 := H2.spineO_comp k ⟨Y, hmem2 Y hY⟩
      simp only at e1 e2
      rw [e1, e2]
      exact (hih Y hY).1
    have hsp : H1.spine (k + 1) Z1 = H2.spine (k + 1) Z2 := by
      rw [spine_succ_eq (hk := by omega), spine_succ_eq (hk := by omega)]
      refine dite_choose_congr (funext fun Γ' => propext ?_) _
      rw [hnn, hZ, hold]
      exact SpineOKO_congr k0 k _ _ (hold ▸ hspO) _ _
    refine ⟨hZ, hsp, ?_⟩
    show S.nextBook (k + 1) (H1.parts k Z1) (fun c => S.postBook k0 k (H1.bk k c))
        (Z1.1 ∩ H1.newCubes (k + 1)).card (H1.spine (k + 1) Z1) =
      S.nextBook (k + 1) (H2.parts k Z2) (fun c => S.postBook k0 k (H2.bk k c))
        (Z2.1 ∩ H2.newCubes (k + 1)).card (H2.spine (k + 1) Z2)
    rw [hnn, hsp]
    refine S.nextBook_congr (k + 1) Subtype.val Subtype.val_injective Subtype.val
      Subtype.val_injective _ _ _ _ ?_ ?_ _ _
    · have e1 := H1.parts_image_eq_comps (k := k) (by omega) Z1
      have e2 := H2.parts_image_eq_comps (k := k) (by omega) Z2
      rw [hold] at e1
      convert e1.trans e2.symm
    · intro c hc c' hc' hcc
      have hY : c.1 ∈ comps (S.omega k) (H1.oldCubes k Z1) := by
        rw [← H1.parts_image_eq_comps (k := k) (by omega)]; exact Finset.mem_image_of_mem _ hc
      have hb := (hih c.1 hY).2
      have e1 : (⟨c.1, hmem1 c.1 hY⟩ : H1.Comp k) = c := Subtype.ext rfl
      have e2 : (⟨c.1, hmem2 c.1 hY⟩ : H2.Comp k) = c' := Subtype.ext hcc
      rw [e1, e2] at hb
      simp only [hb]

end RegionHistory

end Balaban.LargeField
