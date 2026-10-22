/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.GasBound

/-!
# GAS with a general activation rule

Heavy objects `z` (supports `zs z`, weights `τ z`) and couplings `y` (charged supports `cy y`,
values `β y`).  A coupling is present when the selected heavy objects `Γ` activate it,
`act y Γ`, and the partition function is
`Ξ = ∑_{Γ compatible} ∏_{z ∈ Γ} τ z · exp ∑_{y : act y Γ} β y` (`actGasXi`).  The rule `act` is
arbitrary subject to two conditions:

* (L) `act y Γ` is decided by the members of `Γ` whose supports meet `cy y`;
* (M) an active coupling meets the support of a selected heavy object.

The rule of `Gas.lean` (the charged support meets the core of a selected heavy object, `coreAct`)
and the two rules of `GasLinked.lean` satisfy (L) and (M); so do a coupling that requires every
heavy object it passes through (a determinant cycle through several components), and a coupling
decorated by the data of the heavy objects it meets (the decoration is part of `y`, and `act`
checks that it is the one induced by `Γ`).

* `actGasXi_eq`: `Ξ` is the partition function of the polymer gas of connected admissible
  clusters (`gas_eq`, `gasLinked_eq` for the rules above).
* `cfam_actGas_majorant_le`: the combinatorial part of the activity bound for nonnegative
  majorants `g` of the couplings and `a` of the heavy objects: the sum over the connected
  admissible families with union `X` of `∏ g ∏ a` is at most `exp(|X| η) - 1`, when the couplings
  active for each compatible family have entropy `Cc` through every block and the heavy objects
  through every block have weighted entropy `∑ a e^{Cc |Z|} ≤ η`.
* `heavy_entropy_weighted`: that heavy entropy from weighted counts
  `∑_{Z ∋ b, |Z| = v} ω Z ≤ K₀^v` (`heavy_entropy` is the case `ω = 1`).
* `exp_le_prod_of_mem_cfam`: the size of a connected admissible family distributed over its
  members.
* `sum_cfam_actGas_le_of_counts`: the activity bound `3 c₁ e^{-p} e^{-(κ' - 2) d(X)}` of
  `gas_activity_bound` for the sum over the connected admissible families of
  `∏ B₀ e^{B₀} e^{-κ'' d(Y)} ∏ a(Z)`, with the summed counts
  `∑_{Z ∋ b, |Z| = v} a(Z) ≤ K₀''^v e^{-p - h v}` of the heavy majorants and the entropy of the
  couplings active for each compatible family; `actGasK_activity_bound` for scalar weights.
-/

@[expose] public section

noncomputable section

open scoped Classical

open Finset

namespace Balaban.Polymer

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

section Majorant

variable {B Yt Zt : Type*} [Fintype B] [Fintype Yt] [Fintype Zt]
  {act : Yt → Finset Zt → Prop} {cy : Yt → Finset B} {zs : Zt → Finset B}

omit [Fintype B] in
/-- The sum over the connected admissible families with union `X` of products of nonnegative
majorants is at most the sum over the nonempty compatible families `Γ` of heavy objects inside `X`
of `∏_Γ a` times the product of `1 + g` over the couplings active for `Γ`. -/
theorem sum_cfam_actGas_le (hmeet : ∀ y Γ, act y Γ → ∃ z ∈ Γ, ¬ Disjoint (cy y) (zs z))
    (g : Yt → ℝ) (a : Zt → ℝ) (hg : ∀ y, 0 ≤ g y) (ha : ∀ z, 0 ≤ a z) (X : Finset B) :
    ∑ C ∈ Cfam (gasCs cy zs) (actGasA act zs) X, (∏ y ∈ C.toLeft, g y) * ∏ z ∈ C.toRight, a z ≤
      ∑ Γ ∈ (((gasZsub zs X).powerset).erase ∅).filter
          (fun Γ => ∀ z ∈ Γ, ∀ z' ∈ Γ, z ≠ z' → Disjoint (zs z) (zs z')),
        (∏ z ∈ Γ, a z) * ∏ y ∈ Finset.univ.filter (fun y => act y Γ), (1 + g y) := by
  set 𝒮 : Finset (Σ _ : Finset Zt, Finset Yt) :=
    ((((gasZsub zs X).powerset).erase ∅).filter
      (fun Γ => ∀ z ∈ Γ, ∀ z' ∈ Γ, z ≠ z' → Disjoint (zs z) (zs z'))).sigma
      (fun Γ => (Finset.univ.filter (fun y => act y Γ)).powerset) with h𝒮
  set ψ : (Σ _ : Finset Zt, Finset Yt) → Finset (Yt ⊕ Zt) := fun x => x.2.disjSum x.1 with hψ
  have hsub : Cfam (gasCs cy zs) (actGasA act zs) X ⊆ 𝒮.image ψ := by
    intro C hC
    obtain ⟨hconn, hA, hU⟩ := mem_Cfam.mp hC
    rw [Finset.mem_image]
    refine ⟨⟨C.toRight, C.toLeft⟩, ?_, ?_⟩
    · rw [h𝒮, Finset.mem_sigma, Finset.mem_filter, Finset.mem_erase, Finset.mem_powerset,
        Finset.mem_powerset]
      refine ⟨⟨⟨?_, ?_⟩, hA.1⟩, ?_⟩
      · intro hR0
        have hR : C.toRight = ∅ := hR0
        have hL : C.toLeft = ∅ := by
          refine Finset.eq_empty_of_forall_notMem (fun y hy => ?_)
          obtain ⟨z, hz, _⟩ := hmeet y _ (hA.2 y hy)
          rw [hR] at hz
          simp at hz
        have : C = ∅ := by
          rw [← Finset.toLeft_disjSum_toRight (u := C), hL, hR]
          rfl
        exact Finset.not_nonempty_empty (this ▸ hconn.1)
      · intro z hz
        simp only [gasZsub, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [← hU]
        have := Finset.subset_biUnion_of_mem (gasCs cy zs) (Finset.mem_toRight.mp hz)
        simpa [unionCs] using this
      · intro y hy
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hA.2 y hy⟩
    · simp [hψ, Finset.toLeft_disjSum_toRight]
  have hinj : Set.InjOn ψ (𝒮 : Set _) := by
    rintro ⟨Γ, Dy⟩ _ ⟨Γ', Dy'⟩ _ hxy
    have h1 := congrArg Finset.toLeft hxy
    have h2 := congrArg Finset.toRight hxy
    simp only [hψ, Finset.toLeft_disjSum, Finset.toRight_disjSum] at h1 h2
    subst h1
    subst h2
    rfl
  calc ∑ C ∈ Cfam (gasCs cy zs) (actGasA act zs) X, (∏ y ∈ C.toLeft, g y) * ∏ z ∈ C.toRight, a z
      ≤ ∑ C ∈ 𝒮.image ψ, (∏ y ∈ C.toLeft, g y) * ∏ z ∈ C.toRight, a z :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun C _ _ =>
          mul_nonneg (Finset.prod_nonneg (fun y _ => hg y)) (Finset.prod_nonneg (fun z _ => ha z)))
    _ = ∑ x ∈ 𝒮, (∏ y ∈ x.2, g y) * ∏ z ∈ x.1, a z := by
        rw [Finset.sum_image hinj]
        refine Finset.sum_congr rfl (fun x _ => ?_)
        simp [hψ]
    _ = ∑ Γ ∈ (((gasZsub zs X).powerset).erase ∅).filter
          (fun Γ => ∀ z ∈ Γ, ∀ z' ∈ Γ, z ≠ z' → Disjoint (zs z) (zs z')),
          ∑ Dy ∈ (Finset.univ.filter (fun y => act y Γ)).powerset,
            (∏ y ∈ Dy, g y) * ∏ z ∈ Γ, a z := by
        rw [h𝒮, Finset.sum_sigma']
    _ = _ := by
        refine Finset.sum_congr rfl (fun Γ _ => ?_)
        rw [← Finset.sum_mul, ← Finset.prod_one_add, mul_comm]

omit [Fintype B] [Fintype Zt] in
/-- The product of `1 + g` over the couplings active for `Γ` is at most `e^{Cc ∑_Γ |Z|}` when the
active couplings through every block have entropy `Cc`. -/
theorem prod_actGas_le (hmeet : ∀ y Γ, act y Γ → ∃ z ∈ Γ, ¬ Disjoint (cy y) (zs z))
    (g : Yt → ℝ) (hg : ∀ y, 0 ≤ g y) {Cc : ℝ} (hCc : 0 ≤ Cc) (Γ : Finset Zt)
    (hent : ∀ b : B, ∑ y ∈ Finset.univ.filter (fun y => act y Γ ∧ b ∈ cy y), g y ≤ Cc) :
    ∏ y ∈ Finset.univ.filter (fun y => act y Γ), (1 + g y) ≤
      Real.exp (Cc * ∑ z ∈ Γ, ((zs z).card : ℝ)) := by
  refine (Real.prod_one_add_le_exp_sum _ hg).trans (Real.exp_le_exp.mpr ?_)
  set f : Yt → ℝ := fun y => if act y Γ then g y else 0 with hf
  have hf0 : ∀ y, 0 ≤ f y := fun y => by
    simp only [hf]
    split_ifs
    · exact hg y
    · exact le_rfl
  have hcov := sum_le_sum_cover (Finset.univ.filter (fun y => act y Γ)) cy (Γ.biUnion zs) f hf0
    (fun y hy => by
      obtain ⟨z, hz, hnd⟩ := hmeet y Γ (Finset.mem_filter.mp hy).2
      obtain ⟨b, hb1, hb2⟩ := Finset.not_disjoint_iff.mp hnd
      exact ⟨b, Finset.mem_biUnion.mpr ⟨z, hz, hb2⟩, hb1⟩)
  have hfs : ∑ y ∈ Finset.univ.filter (fun y => act y Γ), g y =
      ∑ y ∈ Finset.univ.filter (fun y => act y Γ), f y :=
    Finset.sum_congr rfl (fun y hy => by
      simp [hf, (Finset.mem_filter.mp hy).2])
  have hin : ∀ b : B, ∑ y ∈ Finset.univ.filter (fun y => b ∈ cy y), f y ≤ Cc := by
    intro b
    refine le_of_eq_of_le ?_ (hent b)
    rw [Finset.sum_filter, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    by_cases h1 : act y Γ <;> by_cases h2 : b ∈ cy y <;> simp [hf, h1, h2]
  calc ∑ y ∈ Finset.univ.filter (fun y => act y Γ), g y
      ≤ ∑ b ∈ Γ.biUnion zs, ∑ y ∈ Finset.univ.filter (fun y => b ∈ cy y), f y := hfs ▸ hcov
    _ ≤ ∑ _b ∈ Γ.biUnion zs, Cc := Finset.sum_le_sum (fun b _ => hin b)
    _ = ((Γ.biUnion zs).card : ℝ) * Cc := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (∑ z ∈ Γ, ((zs z).card : ℝ)) * Cc := by
        refine mul_le_mul_of_nonneg_right ?_ hCc
        exact_mod_cast Finset.card_biUnion_le
    _ = Cc * ∑ z ∈ Γ, ((zs z).card : ℝ) := mul_comm _ _

omit [Fintype B] in
/-- **The combinatorial part of the activity bound.**  For nonnegative majorants `g` of the
couplings and `a` of the heavy objects, if the couplings active for every compatible family have
entropy `Cc` through every block and the heavy objects through every block satisfy
`∑ a e^{Cc |Z|} ≤ η`, the sum over the connected admissible families with union `X` of `∏ g ∏ a`
is at most `exp(|X| η) - 1`. -/
theorem cfam_actGas_majorant_le (hz : ∀ z, (zs z).Nonempty)
    (hmeet : ∀ y Γ, act y Γ → ∃ z ∈ Γ, ¬ Disjoint (cy y) (zs z))
    (g : Yt → ℝ) (a : Zt → ℝ) (hg : ∀ y, 0 ≤ g y) (ha : ∀ z, 0 ≤ a z) {Cc η : ℝ}
    (hCc : 0 ≤ Cc)
    (hent : ∀ Γ : Finset Zt, (∀ z ∈ Γ, ∀ z' ∈ Γ, z ≠ z' → Disjoint (zs z) (zs z')) →
      ∀ b : B, ∑ y ∈ Finset.univ.filter (fun y => act y Γ ∧ b ∈ cy y), g y ≤ Cc)
    (hheavy : ∀ b : B, ∑ z ∈ Finset.univ.filter (fun z => b ∈ zs z),
      a z * Real.exp (Cc * (zs z).card) ≤ η)
    (X : Finset B) :
    ∑ C ∈ Cfam (gasCs cy zs) (actGasA act zs) X, (∏ y ∈ C.toLeft, g y) * ∏ z ∈ C.toRight, a z ≤
      Real.exp (X.card * η) - 1 := by
  set ζ : Zt → ℝ := fun z => a z * Real.exp (Cc * (zs z).card) with hζ
  have hζ0 : ∀ z, 0 ≤ ζ z := fun z => mul_nonneg (ha z) (Real.exp_pos _).le
  have h1 := sum_cfam_actGas_le hmeet g a hg ha X
  have h2 : ∀ Γ ∈ (((gasZsub zs X).powerset).erase ∅).filter
      (fun Γ => ∀ z ∈ Γ, ∀ z' ∈ Γ, z ≠ z' → Disjoint (zs z) (zs z')),
      (∏ z ∈ Γ, a z) * ∏ y ∈ Finset.univ.filter (fun y => act y Γ), (1 + g y) ≤
        ∏ z ∈ Γ, ζ z := by
    intro Γ hΓ
    calc (∏ z ∈ Γ, a z) * ∏ y ∈ Finset.univ.filter (fun y => act y Γ), (1 + g y)
        ≤ (∏ z ∈ Γ, a z) * Real.exp (Cc * ∑ z ∈ Γ, ((zs z).card : ℝ)) :=
          mul_le_mul_of_nonneg_left
            (prod_actGas_le hmeet g hg hCc Γ (hent Γ (Finset.mem_filter.mp hΓ).2))
            (Finset.prod_nonneg (fun z _ => ha z))
      _ = ∏ z ∈ Γ, ζ z := by
          rw [Finset.mul_sum, Real.exp_sum, ← Finset.prod_mul_distrib]
  have h3 : ∑ Γ ∈ (((gasZsub zs X).powerset).erase ∅).filter
      (fun Γ => ∀ z ∈ Γ, ∀ z' ∈ Γ, z ≠ z' → Disjoint (zs z) (zs z')), ∏ z ∈ Γ, ζ z ≤
        ∑ Γ ∈ ((gasZsub zs X).powerset).erase ∅, ∏ z ∈ Γ, ζ z :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun Γ _ _ => Finset.prod_nonneg (fun z _ => hζ0 z))
  have h4 := sum_powerset_erase_le ζ hζ0 (gasZsub zs X)
  have h5 : ∑ z ∈ gasZsub zs X, ζ z ≤ X.card * η := by
    refine (sum_le_sum_cover (gasZsub zs X) zs X ζ hζ0 (fun z hz' => ?_)).trans ?_
    · obtain ⟨b, hb⟩ := hz z
      simp only [gasZsub, Finset.mem_filter, Finset.mem_univ, true_and] at hz'
      exact ⟨b, hz' hb, hb⟩
    · calc ∑ b ∈ X, ∑ z ∈ Finset.univ.filter (fun z => b ∈ zs z), ζ z
          ≤ ∑ _b ∈ X, η := Finset.sum_le_sum (fun b _ => hheavy b)
        _ = X.card * η := by rw [Finset.sum_const, nsmul_eq_mul]
  have h6 := Real.exp_le_exp.mpr h5
  linarith [(Finset.sum_le_sum h2).trans h3]

/-- **Heavy entropy from weighted counts.**  If the weights `ω Z` of the heavy objects through
a block with `v` blocks sum to at most `K₀^v`, then `∑_{Z ∋ b} ω Z e^{-λ |Z|} ≤ e^{-(c₁+2)}` for
`λ ≥ c₁ + 3 + ln K₀` (`heavy_entropy` is the case `ω = 1`). -/
theorem heavy_entropy_weighted {K0 c1 lam : ℝ} (hc1 : 0 ≤ c1) (hK0 : 1 ≤ K0)
    (hz : ∀ z, (zs z).Nonempty) (ω : Zt → ℝ)
    (hcount : ∀ (b : B) (v : ℕ),
      ∑ z ∈ Finset.univ.filter (fun z => b ∈ zs z ∧ (zs z).card = v), ω z ≤ K0 ^ v)
    (hlam : c1 + 3 + Real.log K0 ≤ lam) (b : B) :
    ∑ z ∈ Finset.univ.filter (fun z => b ∈ zs z), ω z * Real.exp (-lam * (zs z).card) ≤
      Real.exp (-(c1 + 2)) := by
  set x : ℝ := K0 * Real.exp (-lam) with hx
  have hK0pos : 0 < K0 := by linarith
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x ≤ Real.exp (-(c1 + 3)) := by
    rw [hx]
    calc K0 * Real.exp (-lam) = Real.exp (Real.log K0) * Real.exp (-lam) := by
          rw [Real.exp_log hK0pos]
      _ = Real.exp (Real.log K0 - lam) := by rw [← Real.exp_add]; ring_nf
      _ ≤ Real.exp (-(c1 + 3)) := Real.exp_le_exp.mpr (by linarith)
  have he3 : Real.exp (-3) ≤ 1 / 2 := by
    have h3 : (2 : ℝ) ≤ Real.exp 3 := by
      have := Real.add_one_le_exp (3 : ℝ)
      linarith
    rw [Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le (by norm_num) h3
  have hx12 : x ≤ 1 / 2 :=
    hx1.trans ((Real.exp_le_exp.mpr (by linarith : -(c1 + 3) ≤ -3)).trans he3)
  have hg : ∀ z ∈ Finset.univ.filter (fun z => b ∈ zs z),
      (zs z).card - 1 ∈ Finset.range (Fintype.card B) := by
    intro z hzF
    rw [Finset.mem_filter] at hzF
    rw [Finset.mem_range]
    have h1 := Finset.card_le_univ (zs z)
    have h2 : 0 < Fintype.card B := Fintype.card_pos_iff.mpr ⟨b⟩
    have h3 := (hz z).card_pos
    omega
  rw [← Finset.sum_fiberwise_of_maps_to hg]
  have hinner : ∀ j ∈ Finset.range (Fintype.card B),
      ∑ z ∈ (Finset.univ.filter (fun z => b ∈ zs z)).filter (fun z => (zs z).card - 1 = j),
        ω z * Real.exp (-lam * (zs z).card) ≤ x ^ (j + 1) := by
    intro j _
    have hset : (Finset.univ.filter (fun z => b ∈ zs z)).filter (fun z => (zs z).card - 1 = j) =
        Finset.univ.filter (fun z => b ∈ zs z ∧ (zs z).card = j + 1) := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have := (hz z).card_pos
      constructor
      · rintro ⟨hb, hj⟩
        exact ⟨hb, by omega⟩
      · rintro ⟨hb, hj⟩
        exact ⟨hb, by omega⟩
    rw [hset]
    have : ∀ z ∈ Finset.univ.filter (fun z => b ∈ zs z ∧ (zs z).card = j + 1),
        ω z * Real.exp (-lam * (zs z).card) = ω z * Real.exp (-lam) ^ (j + 1) := by
      intro z hzz
      rw [Finset.mem_filter] at hzz
      rw [hzz.2.2, ← Real.exp_nat_mul]
      congr 2
      push_cast
      ring
    rw [Finset.sum_congr rfl this, ← Finset.sum_mul, hx, mul_pow]
    exact mul_le_mul_of_nonneg_right (hcount b (j + 1)) (by positivity)
  refine (Finset.sum_le_sum hinner).trans ?_
  have hgeo : ∑ j ∈ Finset.range (Fintype.card B), x ^ j ≤ (1 - x)⁻¹ :=
    sum_le_hasSum _ (fun i _ => by positivity) (hasSum_geometric_of_lt_one hx0 (by linarith))
  calc ∑ j ∈ Finset.range (Fintype.card B), x ^ (j + 1)
      = x * ∑ j ∈ Finset.range (Fintype.card B), x ^ j := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun j _ => by ring)
    _ ≤ x * (1 - x)⁻¹ := mul_le_mul_of_nonneg_left hgeo hx0
    _ ≤ x * 2 := by
        refine mul_le_mul_of_nonneg_left ?_ hx0
        rw [inv_le_comm₀ (by linarith) (by norm_num)]
        linarith
    _ ≤ 2 * Real.exp (-(c1 + 3)) := by linarith
    _ ≤ Real.exp (-(c1 + 2)) := by
        have h1 : Real.exp (-(c1 + 2)) = Real.exp 1 * Real.exp (-(c1 + 3)) := by
          rw [← Real.exp_add]
          congr 1
          ring
        rw [h1]
        have := Real.exp_one_gt_d9
        have hp := Real.exp_pos (-(c1 + 3))
        nlinarith

omit [Fintype B] in
/-- **The size of a connected admissible family distributed over its members.**  If the size `d`
is subadditive over connected admissible families up to `c` per member and `d(Z) ≤ c₂ |Z|`, then
`e^{κ' d(X)} ≤ ∏_Y e^{κ' (d(Y) + c)} ∏_Z e^{κ' (c₂ + c) |Z|}` for a family with union `X`. -/
theorem exp_le_prod_of_mem_cfam {A : Finset (Yt ⊕ Zt) → Prop} {d : Finset B → ℝ}
    {κ' c c2 : ℝ} (hκ' : 0 ≤ κ') (hc : 0 ≤ c) (hz : ∀ z, (zs z).Nonempty)
    (hzd : ∀ z, d (zs z) ≤ c2 * (zs z).card)
    (hG3 : ∀ C : Finset (Yt ⊕ Zt), ConnSet (gasCs cy zs) C → A C →
      d (unionCs (gasCs cy zs) C) ≤ ∑ t ∈ C, d (gasCs cy zs t) + c * ((C.card : ℝ) - 1))
    {X : Finset B} {C : Finset (Yt ⊕ Zt)} (hC : C ∈ Cfam (gasCs cy zs) A X) :
    Real.exp (κ' * d X) ≤
      (∏ y ∈ C.toLeft, Real.exp (κ' * (d (cy y) + c))) *
        ∏ z ∈ C.toRight, Real.exp (κ' * ((c2 + c) * (zs z).card)) := by
  obtain ⟨hconn, hA, hU⟩ := mem_Cfam.mp hC
  have h3 := hG3 C hconn hA
  rw [hU, sum_gasCs] at h3
  have hcard : (C.card : ℝ) = C.toLeft.card + C.toRight.card := by
    rw [← Finset.card_toLeft_add_card_toRight (u := C)]
    push_cast
    ring
  rw [hcard] at h3
  have hc2 : ∀ z, d (zs z) + c ≤ (c2 + c) * (zs z).card := by
    intro z
    have h1 : (1 : ℝ) ≤ (zs z).card := by exact_mod_cast (hz z).card_pos
    have := hzd z
    nlinarith
  have hdX : d X ≤ ∑ y ∈ C.toLeft, (d (cy y) + c) +
      ∑ z ∈ C.toRight, (c2 + c) * (zs z).card := by
    have e1 : ∑ y ∈ C.toLeft, (d (cy y) + c) = ∑ y ∈ C.toLeft, d (cy y) + C.toLeft.card * c := by
      rw [Finset.sum_add_distrib]
      simp
    have e2 : ∑ z ∈ C.toRight, d (zs z) ≤ ∑ z ∈ C.toRight, ((c2 + c) * (zs z).card - c) :=
      Finset.sum_le_sum (fun z _ => by linarith [hc2 z])
    have e3 : ∑ z ∈ C.toRight, ((c2 + c) * (zs z).card - c) =
        ∑ z ∈ C.toRight, (c2 + c) * (zs z).card - C.toRight.card * c := by
      rw [Finset.sum_sub_distrib]
      simp
    simp only [gasCs_inl, gasCs_inr] at h3
    nlinarith
  rw [← Real.exp_sum, ← Real.exp_sum, ← Real.exp_add, ← Finset.mul_sum, ← Finset.mul_sum,
    ← mul_add]
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hdX hκ')

omit [Fintype B] [Fintype Zt] in
/-- The entropy of all the couplings through a block bounds that of the active ones. -/
theorem sum_filter_act_le {f : Yt → ℝ} {K : ℝ} (hf : ∀ y, 0 ≤ f y)
    (hent : ∀ b : B, ∑ y ∈ Finset.univ.filter (fun y => b ∈ cy y), f y ≤ K)
    (Γ : Finset Zt) (b : B) :
    ∑ y ∈ Finset.univ.filter (fun y => act y Γ ∧ b ∈ cy y), f y ≤ K :=
  le_trans (Finset.sum_le_sum_of_subset_of_nonneg
    (fun _ hy => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hy).2.2⟩)
    (fun y _ _ => hf y)) (hent b)

omit [Fintype B] [Fintype Yt] in
/-- Unweighted counts with a uniform bound give the summed counts. -/
theorem sum_filter_le_of_count {a : Zt → ℝ} {p h K0 : ℝ}
    (ha : ∀ z, a z ≤ Real.exp (-p - h * (zs z).card))
    (hcount : ∀ (b : B) (v : ℕ),
      ((Finset.univ.filter (fun z => b ∈ zs z ∧ (zs z).card = v)).card : ℝ) ≤ K0 ^ v)
    (b : B) (v : ℕ) :
    ∑ z ∈ Finset.univ.filter (fun z => b ∈ zs z ∧ (zs z).card = v), a z ≤
      K0 ^ v * Real.exp (-p - h * v) := by
  calc ∑ z ∈ Finset.univ.filter (fun z => b ∈ zs z ∧ (zs z).card = v), a z
      ≤ ∑ _z ∈ Finset.univ.filter (fun z => b ∈ zs z ∧ (zs z).card = v),
          Real.exp (-p - h * v) := by
        refine Finset.sum_le_sum (fun z hz => ?_)
        have := (Finset.mem_filter.mp hz).2.2
        exact (ha z).trans_eq (by rw [this])
    _ = ((Finset.univ.filter (fun z => b ∈ zs z ∧ (zs z).card = v)).card : ℝ) *
          Real.exp (-p - h * v) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ K0 ^ v * Real.exp (-p - h * v) :=
        mul_le_mul_of_nonneg_right (hcount b v) (Real.exp_pos _).le

/-- **The activity bound with weighted counts (scalar core).**  For heavy majorants `a ≥ 0` whose
sums over the heavy objects through a block with `v` blocks are at most `K₀''^v e^{-p - h v}`, if the
couplings active for every compatible family satisfy `∑_{Y ∋ b} e^{-(κ'' - κ') d(Y)} ≤ K₀'`, then
`∑_{C ∈ Cfam X} ∏_Y B₀ e^{B₀} e^{-κ'' d(Y)} ∏_Z a(Z) ≤ 3 c₁ e^{-p} e^{-(κ' - 2) d(X)}` for
`|X| ≤ c₁ (1 + d(X))`, provided `h ≥ B₀ e^{B₀} e^{κ' c} K₀' + κ' (c₂ + c) + c₁ + 3 + ln K₀''`. -/
theorem sum_cfam_actGas_le_of_counts {d : Finset B → ℝ} {B0 κ' κ'' c c1 c2 p h K0' K0'' : ℝ}
    (hB0 : 0 ≤ B0) (hκ' : 0 ≤ κ') (hc : 0 ≤ c) (hc1 : 0 ≤ c1) (hp : 0 ≤ p)
    (hd : ∀ Y, 0 ≤ d Y) (hz : ∀ z, (zs z).Nonempty)
    (hmeet : ∀ y Γ, act y Γ → ∃ z ∈ Γ, ¬ Disjoint (cy y) (zs z))
    (a : Zt → ℝ) (ha : ∀ z, 0 ≤ a z)
    (hzd : ∀ z, d (zs z) ≤ c2 * (zs z).card)
    (hG3 : ∀ C : Finset (Yt ⊕ Zt), ConnSet (gasCs cy zs) C → actGasA act zs C →
      d (unionCs (gasCs cy zs) C) ≤ ∑ t ∈ C, d (gasCs cy zs t) + c * ((C.card : ℝ) - 1))
    (hK0' : 0 ≤ K0')
    (hent : ∀ Γ : Finset Zt, (∀ z ∈ Γ, ∀ z' ∈ Γ, z ≠ z' → Disjoint (zs z) (zs z')) →
      ∀ b : B, ∑ y ∈ Finset.univ.filter (fun y => act y Γ ∧ b ∈ cy y),
        Real.exp (-(κ'' - κ') * d (cy y)) ≤ K0')
    (hK1 : 1 ≤ K0'')
    (hcount : ∀ (b : B) (v : ℕ),
      ∑ z ∈ Finset.univ.filter (fun z => b ∈ zs z ∧ (zs z).card = v), a z ≤
        K0'' ^ v * Real.exp (-p - h * v))
    (hh : B0 * Real.exp B0 * Real.exp (κ' * c) * K0' + κ' * (c2 + c) + c1 + 3 +
      Real.log K0'' ≤ h)
    (X : Finset B) (hG1 : (X.card : ℝ) ≤ c1 * (1 + d X)) :
    ∑ C ∈ Cfam (gasCs cy zs) (actGasA act zs) X,
        (∏ y ∈ C.toLeft, B0 * Real.exp B0 * Real.exp (-κ'' * d (cy y))) * ∏ z ∈ C.toRight, a z ≤
      3 * c1 * Real.exp (-p) * Real.exp (-(κ' - 2) * d X) := by
  set Cc : ℝ := B0 * Real.exp B0 * Real.exp (κ' * c) * K0' with hCc
  set lam : ℝ := h - κ' * (c2 + c) - Cc with hlam
  have hlam' : c1 + 3 + Real.log K0'' ≤ lam := by
    rw [hlam]
    linarith
  have hCc0 : 0 ≤ Cc := by positivity
  set a' : Zt → ℝ := fun z => Real.exp (κ' * ((c2 + c) * (zs z).card)) * a z with ha'
  have hgas : ∀ y, B0 * Real.exp B0 * Real.exp (-κ'' * d (cy y)) *
      Real.exp (κ' * (d (cy y) + c)) = gasG cy d B0 κ' κ'' c y := by
    intro y
    simp only [gasG]
    have : Real.exp (-κ'' * d (cy y)) * Real.exp (κ' * (d (cy y) + c)) =
        Real.exp (κ' * c) * Real.exp (-(κ'' - κ') * d (cy y)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    calc B0 * Real.exp B0 * Real.exp (-κ'' * d (cy y)) * Real.exp (κ' * (d (cy y) + c))
        = B0 * Real.exp B0 * (Real.exp (-κ'' * d (cy y)) * Real.exp (κ' * (d (cy y) + c))) := by
          ring
      _ = _ := by rw [this]; ring
  -- the size distributed over the members of each family
  have hterm : ∀ C ∈ Cfam (gasCs cy zs) (actGasA act zs) X,
      Real.exp (κ' * d X) *
          ((∏ y ∈ C.toLeft, B0 * Real.exp B0 * Real.exp (-κ'' * d (cy y))) *
            ∏ z ∈ C.toRight, a z) ≤
        (∏ y ∈ C.toLeft, gasG cy d B0 κ' κ'' c y) * ∏ z ∈ C.toRight, a' z := by
    intro C hC
    have h1 := exp_le_prod_of_mem_cfam hκ' hc hz hzd hG3 hC
    calc Real.exp (κ' * d X) *
          ((∏ y ∈ C.toLeft, B0 * Real.exp B0 * Real.exp (-κ'' * d (cy y))) *
            ∏ z ∈ C.toRight, a z)
        ≤ ((∏ y ∈ C.toLeft, Real.exp (κ' * (d (cy y) + c))) *
            ∏ z ∈ C.toRight, Real.exp (κ' * ((c2 + c) * (zs z).card))) *
          ((∏ y ∈ C.toLeft, B0 * Real.exp B0 * Real.exp (-κ'' * d (cy y))) *
            ∏ z ∈ C.toRight, a z) :=
          mul_le_mul_of_nonneg_right h1
            (mul_nonneg (Finset.prod_nonneg (fun y _ => by positivity))
              (Finset.prod_nonneg (fun z _ => ha z)))
      _ = (∏ y ∈ C.toLeft, (B0 * Real.exp B0 * Real.exp (-κ'' * d (cy y)) *
            Real.exp (κ' * (d (cy y) + c)))) * ∏ z ∈ C.toRight, a' z := by
          simp only [ha', Finset.prod_mul_distrib]
          ring
      _ = _ := by simp only [hgas]
  -- the entropy of the couplings
  have hent' : ∀ Γ : Finset Zt, (∀ z ∈ Γ, ∀ z' ∈ Γ, z ≠ z' → Disjoint (zs z) (zs z')) →
      ∀ b : B, ∑ y ∈ Finset.univ.filter (fun y => act y Γ ∧ b ∈ cy y),
        gasG cy d B0 κ' κ'' c y ≤ Cc := by
    intro Γ hΓ b
    simp only [gasG]
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hent Γ hΓ b) (by positivity)
  -- the entropy of the heavy objects
  have hcountω : ∀ (b : B) (v : ℕ), ∑ z ∈ Finset.univ.filter
      (fun z => b ∈ zs z ∧ (zs z).card = v), Real.exp (p + h * (zs z).card) * a z ≤ K0'' ^ v := by
    intro b v
    calc ∑ z ∈ Finset.univ.filter (fun z => b ∈ zs z ∧ (zs z).card = v),
          Real.exp (p + h * (zs z).card) * a z
        = Real.exp (p + h * v) *
            ∑ z ∈ Finset.univ.filter (fun z => b ∈ zs z ∧ (zs z).card = v), a z := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun z hz => ?_)
          rw [(Finset.mem_filter.mp hz).2.2]
      _ ≤ Real.exp (p + h * v) * (K0'' ^ v * Real.exp (-p - h * v)) :=
          mul_le_mul_of_nonneg_left (hcount b v) (Real.exp_pos _).le
      _ = K0'' ^ v := by
          rw [mul_comm, mul_assoc, ← Real.exp_add]
          simp
  have hheavy : ∀ b : B, ∑ z ∈ Finset.univ.filter (fun z => b ∈ zs z),
      a' z * Real.exp (Cc * (zs z).card) ≤ Real.exp (-p) * Real.exp (-(c1 + 2)) := by
    intro b
    calc ∑ z ∈ Finset.univ.filter (fun z => b ∈ zs z), a' z * Real.exp (Cc * (zs z).card)
        = Real.exp (-p) * ∑ z ∈ Finset.univ.filter (fun z => b ∈ zs z),
            Real.exp (p + h * (zs z).card) * a z * Real.exp (-lam * (zs z).card) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun z _ => ?_)
          simp only [ha']
          have : Real.exp (κ' * ((c2 + c) * (zs z).card)) * Real.exp (Cc * (zs z).card) =
              Real.exp (-p) * Real.exp (p + h * (zs z).card) * Real.exp (-lam * (zs z).card) := by
            rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
            congr 1
            rw [hlam]
            ring
          calc Real.exp (κ' * ((c2 + c) * (zs z).card)) * a z * Real.exp (Cc * (zs z).card)
              = (Real.exp (κ' * ((c2 + c) * (zs z).card)) * Real.exp (Cc * (zs z).card)) * a z := by
                ring
            _ = _ := by rw [this]; ring
      _ ≤ Real.exp (-p) * Real.exp (-(c1 + 2)) :=
          mul_le_mul_of_nonneg_left (heavy_entropy_weighted hc1 hK1 hz _ hcountω hlam' b)
            (Real.exp_pos _).le
  have h2 := cfam_actGas_majorant_le hz hmeet (gasG cy d B0 κ' κ'' c) a' (gasG_nonneg hB0)
    (fun z => mul_nonneg (Real.exp_pos _).le (ha z)) hCc0 hent' hheavy X
  have h3 := gas_real_bound (p := p) (c1 := c1) (D := d X) (n := (X.card : ℝ)) hp hc1 (hd _)
    (Nat.cast_nonneg _) hG1
  set S := ∑ C ∈ Cfam (gasCs cy zs) (actGasA act zs) X,
    (∏ y ∈ C.toLeft, B0 * Real.exp B0 * Real.exp (-κ'' * d (cy y))) * ∏ z ∈ C.toRight, a z
    with hS
  have h4 : Real.exp (κ' * d X) * S ≤ 3 * c1 * Real.exp (-p) * Real.exp (2 * d X) := by
    rw [hS, Finset.mul_sum]
    exact ((Finset.sum_le_sum hterm).trans h2).trans (by linarith)
  have e : Real.exp (-κ' * d X) * Real.exp (κ' * d X) = 1 := by
    rw [← Real.exp_add]
    simp
  calc S = Real.exp (-κ' * d X) * (Real.exp (κ' * d X) * S) := by rw [← mul_assoc, e, one_mul]
    _ ≤ Real.exp (-κ' * d X) * (3 * c1 * Real.exp (-p) * Real.exp (2 * d X)) :=
        mul_le_mul_of_nonneg_left h4 (Real.exp_pos _).le
    _ = 3 * c1 * Real.exp (-p) * Real.exp (-(κ' - 2) * d X) := by
        have : Real.exp (-κ' * d X) * Real.exp (2 * d X) = Real.exp (-(κ' - 2) * d X) := by
          rw [← Real.exp_add]
          congr 1
          ring
        rw [← this]
        ring

/-- **GAS with a general activation rule (activity bound)**: with couplings bounded by
`B₀ e^{-κ'' d(Y)}` and heavy weights with the summed counts
`∑_{Z ∋ b, |Z| = v} |τ Z| ≤ K₀''^v e^{-p - h v}`, the activities satisfy
`|K(X)| ≤ 3 c₁ e^{-p} e^{-(κ' - 2) d(X)}` for `|X| ≤ c₁ (1 + d(X))`. -/
theorem actGasK_activity_bound {β : Yt → ℂ} {τ : Zt → ℂ} {d : Finset B → ℝ}
    {B0 κ' κ'' c c1 c2 p h K0' K0'' : ℝ}
    (hB0 : 0 ≤ B0) (hκ' : 0 ≤ κ') (hκ'' : κ' ≤ κ'') (hc : 0 ≤ c) (hc1 : 0 ≤ c1) (hp : 0 ≤ p)
    (hd : ∀ Y, 0 ≤ d Y) (hz : ∀ z, (zs z).Nonempty)
    (hmeet : ∀ y Γ, act y Γ → ∃ z ∈ Γ, ¬ Disjoint (cy y) (zs z))
    (hB : ∀ y, ‖β y‖ ≤ B0 * Real.exp (-κ'' * d (cy y)))
    (hzd : ∀ z, d (zs z) ≤ c2 * (zs z).card)
    (hG3 : ∀ C : Finset (Yt ⊕ Zt), ConnSet (gasCs cy zs) C → actGasA act zs C →
      d (unionCs (gasCs cy zs) C) ≤ ∑ t ∈ C, d (gasCs cy zs t) + c * ((C.card : ℝ) - 1))
    (hK0' : 0 ≤ K0')
    (hent : ∀ Γ : Finset Zt, (∀ z ∈ Γ, ∀ z' ∈ Γ, z ≠ z' → Disjoint (zs z) (zs z')) →
      ∀ b : B, ∑ y ∈ Finset.univ.filter (fun y => act y Γ ∧ b ∈ cy y),
        Real.exp (-(κ'' - κ') * d (cy y)) ≤ K0')
    (hK1 : 1 ≤ K0'')
    (hcount : ∀ (b : B) (v : ℕ),
      ∑ z ∈ Finset.univ.filter (fun z => b ∈ zs z ∧ (zs z).card = v), ‖τ z‖ ≤
        K0'' ^ v * Real.exp (-p - h * v))
    (hh : B0 * Real.exp B0 * Real.exp (κ' * c) * K0' + κ' * (c2 + c) + c1 + 3 +
      Real.log K0'' ≤ h)
    (X : NePoly B) (hG1 : (X.1.card : ℝ) ≤ c1 * (1 + d X.1)) :
    ‖actGasK act cy zs β τ X‖ ≤ 3 * c1 * Real.exp (-p) * Real.exp (-(κ' - 2) * d X.1) := by
  refine le_trans ?_ (sum_cfam_actGas_le_of_counts hB0 hκ' hc hc1 hp hd hz hmeet (fun z => ‖τ z‖)
    (fun z => norm_nonneg _) hzd hG3 hK0' hent hK1 hcount hh X.1 hG1)
  unfold actGasK polyAct
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun C _ => ?_))
  rw [prod_gasW, norm_mul, norm_prod, norm_prod]
  exact mul_le_mul_of_nonneg_right (Finset.prod_le_prod₀ (fun y _ => norm_nonneg _)
    (fun y _ => norm_expm1_le hB0 (hκ'.trans hκ'') hd y (hB y)))
    (Finset.prod_nonneg (fun z _ => norm_nonneg _))

end Majorant

end Balaban.Polymer
