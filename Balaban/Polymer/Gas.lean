module

public import Balaban.Polymer.Decomposition

/-!
# The boundary-term lemma GAS

Heavy objects `Z` (blocks `zs Z`, core `cr Z ⊆ zs Z`, weight `τ Z`) and couplings `Y` (charged
support `cy Y`, value `β Y`).  The partition function
`Ξ = ∑_{Γ ⊆ 𝒵 pairwise disjoint} ∏_{Z ∈ Γ} τ Z · exp ∑_{Y meeting the core of Γ} β Y`
equals the partition function of the polymer gas whose polymers are the connected clusters
`(D, Γ₀)` of couplings and heavy objects (POLYMER.md §2.6, §3.9, `gas_eq`).  The coupling/heavy
contact relation is "the charged supports meet"; two heavy objects in one polymer never touch.

`gas_eq` is the instance of a gas with a general activation rule: a coupling is present when the
selected heavy objects `Γ` activate it, `act y Γ`, and
`Ξ = ∑_{Γ compatible} ∏_{z ∈ Γ} τ z · exp ∑_{y : act y Γ} β y` (`actGasXi`), where

* (L) `act y Γ` is decided by the members of `Γ` whose supports meet `cy y`;
* (M) an active coupling meets the support of a selected heavy object.

The rule above is `coreAct cy cr` (activation by sites: an activation set meets the cores);
`reqAct` activates a coupling by a required set of heavy objects (a determinant cycle through
several components); a coupling decorated by the data of the heavy objects it meets has the
decoration as part of `y`, and `act` checks that it is the one induced by `Γ`.  `actGasXi_eq` is the
identity for every rule satisfying (L) and (M).
-/

@[expose] public section

noncomputable section

open scoped Classical

open Finset

namespace Balaban.Polymer

section Gas

variable {B Yt Zt : Type*} [Fintype B] [Fintype Yt] [Fintype Zt]
  (cy : Yt → Finset B) (zs cr : Zt → Finset B) (β : Yt → ℂ) (τ : Zt → ℂ)

/-- The charged supports of the elementary objects: couplings on the left, heavy objects on the
right. -/
def gasCs : Yt ⊕ Zt → Finset B := Sum.elim cy zs

omit [Fintype B] [Fintype Yt] [Fintype Zt] in
variable {cy zs} in
@[simp] theorem gasCs_inl (y : Yt) : gasCs cy zs (Sum.inl y) = cy y := rfl

omit [Fintype B] [Fintype Yt] [Fintype Zt] in
variable {cy zs} in
@[simp] theorem gasCs_inr (z : Zt) : gasCs cy zs (Sum.inr z) = zs z := rfl

/-- The weights `e^{β Y} - 1` and `τ Z`. -/
def gasW : Yt ⊕ Zt → ℂ := Sum.elim (fun y => Complex.exp (β y) - 1) τ

/-- Admissible families: the heavy objects are pairwise disjoint and every coupling meets the core
of a heavy object of the family. -/
def gasA (D : Finset (Yt ⊕ Zt)) : Prop :=
  (∀ z ∈ D.toRight, ∀ z' ∈ D.toRight, z ≠ z' → Disjoint (zs z) (zs z')) ∧
    ∀ y ∈ D.toLeft, ∃ z ∈ D.toRight, ¬ Disjoint (cy y) (cr z)

/-- The partition function of GAS. -/
def gasXi : ℂ :=
  ∑ Γ ∈ Finset.univ.filter (fun Γ : Finset Zt => ∀ z ∈ Γ, ∀ z' ∈ Γ, z ≠ z' → Disjoint (zs z) (zs z')),
    (∏ z ∈ Γ, τ z) * Complex.exp (∑ y ∈ Finset.univ.filter
      (fun y => ¬ Disjoint (cy y) (Γ.biUnion cr)), β y)

/-- The activity of the polymer `X`: the sum over connected admissible clusters with union `X`. -/
def gasK (X : NePoly B) : ℂ := polyAct (gasCs cy zs) (gasA cy zs cr) (gasW β τ) X

end Gas

section Defs

variable {B Yt Zt : Type*} [Fintype B] [Fintype Yt] [Fintype Zt]
  (act : Yt → Finset Zt → Prop) (cy : Yt → Finset B) (zs : Zt → Finset B)
  (β : Yt → ℂ) (τ : Zt → ℂ)

/-- Admissible families for the activation rule `act`: pairwise disjoint heavy supports, and every
coupling of the family is active for the heavy objects of the family. -/
def actGasA (D : Finset (Yt ⊕ Zt)) : Prop :=
  (∀ z ∈ D.toRight, ∀ z' ∈ D.toRight, z ≠ z' → Disjoint (zs z) (zs z')) ∧
    ∀ y ∈ D.toLeft, act y D.toRight

/-- The partition function of the gas with activation rule `act`. -/
def actGasXi : ℂ :=
  ∑ Γ ∈ Finset.univ.filter
      (fun Γ : Finset Zt => ∀ z ∈ Γ, ∀ z' ∈ Γ, z ≠ z' → Disjoint (zs z) (zs z')),
    (∏ z ∈ Γ, τ z) * Complex.exp (∑ y ∈ Finset.univ.filter (fun y => act y Γ), β y)

/-- The activity of the polymer `X`: the sum over the connected admissible families whose union of
supports is `X`. -/
def actGasK (X : NePoly B) : ℂ := polyAct (gasCs cy zs) (actGasA act zs) (gasW β τ) X

/-- Activation by sites: the activation set `asite y` of the coupling meets the core of a selected
heavy object (the rule of `Gas.lean` is `asite = cy`). -/
def coreAct (asite : Yt → Finset B) (cr : Zt → Finset B) (y : Yt) (Γ : Finset Zt) : Prop :=
  ∃ z ∈ Γ, ¬ Disjoint (asite y) (cr z)

/-- Activation by heavy objects: the coupling requires the nonempty set `req y` of heavy objects,
all of which must be selected. -/
def reqAct (req : Yt → Finset Zt) (y : Yt) (Γ : Finset Zt) : Prop :=
  (req y).Nonempty ∧ req y ⊆ Γ

omit [Fintype B] [Fintype Yt] [Fintype Zt] in
theorem gasA_eq_actGasA (cr : Zt → Finset B) : gasA cy zs cr = actGasA (coreAct cy cr) zs := rfl

omit [Fintype B] in
theorem gasK_eq_actGasK (cr : Zt → Finset B) :
    gasK cy zs cr β τ = actGasK (coreAct cy cr) cy zs β τ := rfl

omit [Fintype B] in
theorem gasXi_eq_actGasXi (cr : Zt → Finset B) :
    gasXi cy zs cr β τ = actGasXi (coreAct cy cr) zs β τ := by
  unfold gasXi actGasXi
  refine Finset.sum_congr rfl (fun Γ _ => ?_)
  rw [Finset.filter_congr (fun y _ => (show ¬ Disjoint (cy y) (Γ.biUnion cr) ↔ coreAct cy cr y Γ by
    simp [coreAct, Finset.disjoint_biUnion_right]))]

end Defs

section Local

variable {B Yt Zt : Type*} [Fintype B] [Fintype Yt] [Fintype Zt]
  {act : Yt → Finset Zt → Prop} {cy : Yt → Finset B} {zs : Zt → Finset B}

omit [Fintype B] [Fintype Yt] [Fintype Zt] in
theorem not_disjoint_of_coreAct {asite : Yt → Finset B} {cr : Zt → Finset B}
    (hsub : ∀ y, asite y ⊆ cy y) (hcr : ∀ z, cr z ⊆ zs z) {y : Yt} {z : Zt}
    (h : ¬ Disjoint (asite y) (cr z)) : ¬ Disjoint (cy y) (zs z) := fun hd =>
  h (Finset.disjoint_of_subset_left (hsub y) (Finset.disjoint_of_subset_right (hcr z) hd))

omit [Fintype B] [Fintype Yt] [Fintype Zt] in
/-- (L) for activation by sites, when the activation sets lie in the charged supports and the
cores in the supports. -/
theorem coreAct_local {asite : Yt → Finset B} {cr : Zt → Finset B} (hsub : ∀ y, asite y ⊆ cy y)
    (hcr : ∀ z, cr z ⊆ zs z) (y : Yt) (Γ : Finset Zt) :
    coreAct asite cr y Γ ↔
      coreAct asite cr y (Γ.filter (fun z => ¬ Disjoint (cy y) (zs z))) := by
  constructor
  · rintro ⟨z, hz, hd⟩
    exact ⟨z, Finset.mem_filter.mpr ⟨hz, not_disjoint_of_coreAct hsub hcr hd⟩, hd⟩
  · rintro ⟨z, hz, hd⟩
    exact ⟨z, (Finset.mem_filter.mp hz).1, hd⟩

omit [Fintype B] [Fintype Yt] [Fintype Zt] in
/-- (M) for activation by sites. -/
theorem coreAct_meets {asite : Yt → Finset B} {cr : Zt → Finset B} (hsub : ∀ y, asite y ⊆ cy y)
    (hcr : ∀ z, cr z ⊆ zs z) (y : Yt) (Γ : Finset Zt) (h : coreAct asite cr y Γ) :
    ∃ z ∈ Γ, ¬ Disjoint (cy y) (zs z) := by
  obtain ⟨z, hz, hd⟩ := h
  exact ⟨z, hz, not_disjoint_of_coreAct hsub hcr hd⟩

omit [Fintype B] [Fintype Yt] [Fintype Zt] in
/-- (L) for activation by heavy objects, when every required heavy object meets the charged
support. -/
theorem reqAct_local {req : Yt → Finset Zt} (hreq : ∀ y, ∀ z ∈ req y, ¬ Disjoint (cy y) (zs z))
    (y : Yt) (Γ : Finset Zt) :
    reqAct req y Γ ↔ reqAct req y (Γ.filter (fun z => ¬ Disjoint (cy y) (zs z))) := by
  constructor
  · rintro ⟨hne, hsub⟩
    exact ⟨hne, fun z hz => Finset.mem_filter.mpr ⟨hsub hz, hreq y z hz⟩⟩
  · rintro ⟨hne, hsub⟩
    exact ⟨hne, hsub.trans (Finset.filter_subset _ _)⟩

omit [Fintype B] [Fintype Yt] [Fintype Zt] in
/-- (M) for activation by heavy objects. -/
theorem reqAct_meets {req : Yt → Finset Zt} (hreq : ∀ y, ∀ z ∈ req y, ¬ Disjoint (cy y) (zs z))
    (y : Yt) (Γ : Finset Zt) (h : reqAct req y Γ) : ∃ z ∈ Γ, ¬ Disjoint (cy y) (zs z) := by
  obtain ⟨⟨z, hz⟩, hsub⟩ := h
  exact ⟨z, hsub hz, hreq y z hz⟩

omit [Fintype B] [Fintype Yt] [Fintype Zt] in
/-- The heavy objects of a family in contact with a coupling of one of its components are those
of the component. -/
theorem filter_toRight_comp {D : Finset (Yt ⊕ Zt)} {t : Yt ⊕ Zt} {y : Yt}
    (hy : Sum.inl y ∈ comp (gasCs cy zs) D t) :
    (comp (gasCs cy zs) D t).toRight.filter (fun z => ¬ Disjoint (cy y) (zs z)) =
      D.toRight.filter (fun z => ¬ Disjoint (cy y) (zs z)) := by
  ext z
  simp only [Finset.mem_filter, Finset.mem_toRight]
  constructor
  · rintro ⟨hz, hd⟩
    exact ⟨comp_subset D t hz, hd⟩
  · rintro ⟨hz, hd⟩
    exact ⟨comp_closed hy hz hd, hd⟩

omit [Fintype B] [Fintype Yt] [Fintype Zt] in
theorem act_iff_of_filter_eq
    (hloc : ∀ y Γ, act y Γ ↔ act y (Γ.filter (fun z => ¬ Disjoint (cy y) (zs z))))
    {y : Yt} {Γ Γ' : Finset Zt}
    (h : Γ.filter (fun z => ¬ Disjoint (cy y) (zs z)) =
      Γ'.filter (fun z => ¬ Disjoint (cy y) (zs z))) :
    act y Γ ↔ act y Γ' := by
  rw [hloc y Γ, hloc y Γ', h]

omit [Fintype B] [Fintype Yt] [Fintype Zt] in
/-- Admissibility is local to the components (the input of `decomposition`). -/
theorem actGasA_loc
    (hloc : ∀ y Γ, act y Γ ↔ act y (Γ.filter (fun z => ¬ Disjoint (cy y) (zs z))))
    (D : Finset (Yt ⊕ Zt)) :
    actGasA act zs D ↔ ∀ t ∈ D, actGasA act zs (comp (gasCs cy zs) D t) := by
  constructor
  · rintro ⟨h1, h2⟩ t _
    refine ⟨fun z hz z' hz' hne => h1 z (toRight_subset_toRight (comp_subset D t) hz) z'
      (toRight_subset_toRight (comp_subset D t) hz') hne, fun y hy => ?_⟩
    have hy' := Finset.mem_toLeft.mp hy
    exact (act_iff_of_filter_eq hloc (filter_toRight_comp hy')).mpr
      (h2 y (Finset.mem_toLeft.mpr (comp_subset D t hy')))
  · intro h
    refine ⟨fun z hz z' hz' hne => ?_, fun y hy => ?_⟩
    · by_contra hnd
      have hzD := Finset.mem_toRight.mp hz
      have hmem : (Sum.inr z' : Yt ⊕ Zt) ∈ comp (gasCs cy zs) D (Sum.inr z) :=
        comp_closed (self_mem_comp hzD) (Finset.mem_toRight.mp hz') hnd
      exact hnd ((h _ hzD).1 z (Finset.mem_toRight.mpr (self_mem_comp hzD)) z'
        (Finset.mem_toRight.mpr hmem) hne)
    · have hyD := Finset.mem_toLeft.mp hy
      exact (act_iff_of_filter_eq hloc (filter_toRight_comp (self_mem_comp hyD))).mp
        ((h _ hyD).2 y (Finset.mem_toLeft.mpr (self_mem_comp hyD)))

omit [Fintype B] [Fintype Yt] [Fintype Zt] in
theorem actGasA_nonempty (hz : ∀ z, (zs z).Nonempty)
    (hmeet : ∀ y Γ, act y Γ → ∃ z ∈ Γ, ¬ Disjoint (cy y) (zs z))
    (D : Finset (Yt ⊕ Zt)) (hD : actGasA act zs D) : ∀ t ∈ D, (gasCs cy zs t).Nonempty := by
  intro t ht
  rcases t with y | z
  · obtain ⟨z, _, hnd⟩ := hmeet y _ (hD.2 y (Finset.mem_toLeft.mpr ht))
    exact (Finset.not_disjoint_iff.mp hnd).elim (fun b hb => ⟨b, hb.1⟩)
  · exact hz z

end Local

section Gas

variable {B Yt Zt : Type*} [Fintype B] [Fintype Yt] [Fintype Zt]
  {cy : Yt → Finset B} {zs cr : Zt → Finset B} (β : Yt → ℂ) (τ : Zt → ℂ)

omit [Fintype B] [Fintype Yt] [Fintype Zt] in
theorem gasA_loc (hcr : ∀ z, cr z ⊆ zs z) (D : Finset (Yt ⊕ Zt)) :
    gasA cy zs cr D ↔ ∀ t ∈ D, gasA cy zs cr (comp (gasCs cy zs) D t) :=
  actGasA_loc (coreAct_local (fun _ => Finset.Subset.rfl) hcr) D

omit [Fintype B] [Fintype Yt] [Fintype Zt] in
theorem gasA_nonempty (hz : ∀ z, (zs z).Nonempty)
    (D : Finset (Yt ⊕ Zt)) (hD : gasA cy zs cr D) : ∀ t ∈ D, (gasCs cy zs t).Nonempty := by
  intro t ht
  rcases t with y | z
  · obtain ⟨z, _, hnd⟩ := hD.2 y (Finset.mem_toLeft.mpr ht)
    exact (Finset.not_disjoint_iff.mp hnd).elim (fun b hb => ⟨b, hb.1⟩)
  · exact hz z

omit [Fintype Yt] [Fintype Zt] in
theorem prod_gasW (D : Finset (Yt ⊕ Zt)) :
    ∏ t ∈ D, gasW β τ t =
      (∏ y ∈ D.toLeft, (Complex.exp (β y) - 1)) * ∏ z ∈ D.toRight, τ z := by
  conv_lhs => rw [← Finset.toLeft_disjSum_toRight (u := D)]
  rw [Finset.prod_disjSum]
  rfl

end Gas

section Identity

variable {B Yt Zt : Type*} [Fintype B] [Fintype Yt] [Fintype Zt]
  {act : Yt → Finset Zt → Prop} {cy : Yt → Finset B} {zs : Zt → Finset B}
  (β : Yt → ℂ) (τ : Zt → ℂ)

/-- **GAS with a general activation rule (identity)**: the partition function is the partition
function of the polymer gas of the connected admissible clusters. -/
theorem actGasXi_eq (hz : ∀ z, (zs z).Nonempty)
    (hloc : ∀ y Γ, act y Γ ↔ act y (Γ.filter (fun z => ¬ Disjoint (cy y) (zs z))))
    (hmeet : ∀ y Γ, act y Γ → ∃ z ∈ Γ, ¬ Disjoint (cy y) (zs z)) :
    actGasXi act zs β τ =
      Xi (shareBlock (Subtype.val : NePoly B → Finset B)) (actGasK act cy zs β τ) := by
  have hdec := decomposition (cs := gasCs cy zs) (A := actGasA act zs)
    (fun D hD => actGasA_nonempty hz hmeet D hD) (actGasA_loc hloc) (gasW β τ)
  unfold actGasK
  rw [← hdec]
  unfold actGasXi
  set S : Finset (Finset Zt) := Finset.univ.filter
    (fun Γ : Finset Zt => ∀ z ∈ Γ, ∀ z' ∈ Γ, z ≠ z' → Disjoint (zs z) (zs z')) with hS
  set Ym : Finset Zt → Finset Yt := fun Γ => Finset.univ.filter (fun y => act y Γ) with hYm
  have h1 : ∀ Γ : Finset Zt, (∏ z ∈ Γ, τ z) * Complex.exp (∑ y ∈ Ym Γ, β y) =
      ∑ Dy ∈ (Ym Γ).powerset, (∏ y ∈ Dy, (Complex.exp (β y) - 1)) * ∏ z ∈ Γ, τ z := by
    intro Γ
    rw [Complex.exp_sum, ← Finset.sum_mul]
    have : ∏ y ∈ Ym Γ, Complex.exp (β y) = ∏ y ∈ Ym Γ, (1 + (Complex.exp (β y) - 1)) :=
      Finset.prod_congr rfl (fun y _ => by ring)
    rw [this, Finset.prod_one_add, mul_comm]
  refine (Finset.sum_congr rfl (fun Γ _ => h1 Γ)).trans ?_
  rw [Finset.sum_sigma' S (fun Γ => (Ym Γ).powerset)
    (fun Γ Dy => (∏ y ∈ Dy, (Complex.exp (β y) - 1)) * ∏ z ∈ Γ, τ z)]
  symm
  refine Finset.sum_nbij' (fun D => (⟨D.toRight, D.toLeft⟩ : Σ _ : Finset Zt, Finset Yt))
    (fun x => x.2.disjSum x.1) ?_ ?_ ?_ ?_ ?_
  · intro D hD
    have hA : actGasA act zs D := (Finset.mem_filter.mp hD).2
    rw [Finset.mem_sigma]
    refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hA.1⟩, ?_⟩
    rw [Finset.mem_powerset]
    intro y hy
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hA.2 y hy⟩
  · rintro ⟨Γ, Dy⟩ hx
    rw [Finset.mem_sigma] at hx
    obtain ⟨hΓ, hDy⟩ := hx
    rw [Finset.mem_powerset] at hDy
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · simpa using (Finset.mem_filter.mp hΓ).2
    · intro y hy
      simp only [Finset.toLeft_disjSum] at hy
      simpa only [Finset.toRight_disjSum] using (Finset.mem_filter.mp (hDy hy)).2
  · intro D _
    simp [Finset.toLeft_disjSum_toRight]
  · rintro ⟨Γ, Dy⟩ _
    simp
  · intro D _
    rw [prod_gasW]

end Identity

section GasEq

variable {B Yt Zt : Type*} [Fintype B] [Fintype Yt] [Fintype Zt]
  {cy : Yt → Finset B} {zs cr : Zt → Finset B} (β : Yt → ℂ) (τ : Zt → ℂ)

/-- **GAS (identity)**: the partition function with non-small boundary terms is the partition
function of the polymer gas of connected clusters `(D, Γ₀)`. -/
theorem gas_eq (hz : ∀ z, (zs z).Nonempty) (hcr : ∀ z, cr z ⊆ zs z) :
    gasXi cy zs cr β τ =
      Xi (shareBlock (Subtype.val : NePoly B → Finset B)) (gasK cy zs cr β τ) := by
  rw [gasXi_eq_actGasXi]
  exact actGasXi_eq β τ hz (coreAct_local (fun _ => Finset.Subset.rfl) hcr)
    (coreAct_meets (fun _ => Finset.Subset.rfl) hcr)

end GasEq

end Balaban.Polymer
