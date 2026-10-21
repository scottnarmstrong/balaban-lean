/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.CorrHull
public import Balaban.LargeField.Budget.CanonicalBook

/-!
# The books of corresponding components of two tori

Let `Z₁`, `Z₂` be components of `Z^pre_k` of two region histories on two tori `n_K = nK₁, nK₂`
whose lineages and new cubes correspond (`LinCorr`: the fine sets of `Lin_j(Z)` and of
`Lin_{j+1}(Z) ∩ 𝒩_{j+1}` correspond in the box) and whose sites lie in the box with the margin of
one cube (`Marg`).  Then their books agree (`bk_corr`).  The proof runs by induction on the scale
along the lifted cube indices (`CorrLift`): the old parts are the components of the lifted set of
cubes of `Z_{k-1}` over `Z`, the spine length is `spineTarget` (a function of the lifted data, the
hull of `Z` and the spine lengths of the parts, `spineTarget_corr`), and the book depends on the
spine only through its length.
-/

@[expose] public section

open Balaban Balaban.LargeField

set_option linter.unusedSectionVars false

namespace Balaban.RootFSpine

section Index

variable {ι₁ ι₂ α : Type*} [DecidableEq α] {e₁ : ι₁ → α} {e₂ : ι₂ → α} {p₁ : Finset ι₁}
  {p₂ : Finset ι₂}

theorem exists_corr_left (hp : p₁.image e₁ = p₂.image e₂) {i₁ : ι₁}
    (h : i₁ ∈ p₁) : ∃ i₂ ∈ p₂, e₂ i₂ = e₁ i₁ := by
  have : e₁ i₁ ∈ p₂.image e₂ := by rw [← hp]; exact Finset.mem_image_of_mem _ h
  obtain ⟨i₂, hi₂, h2⟩ := Finset.mem_image.1 this
  exact ⟨i₂, hi₂, h2⟩

theorem exists_corr_right (hp : p₁.image e₁ = p₂.image e₂) {i₂ : ι₂} (h : i₂ ∈ p₂) :
    ∃ i₁ ∈ p₁, e₁ i₁ = e₂ i₂ := by
  have : e₂ i₂ ∈ p₁.image e₁ := by rw [hp]; exact Finset.mem_image_of_mem _ h
  obtain ⟨i₁, hi₁, h1⟩ := Finset.mem_image.1 this
  exact ⟨i₁, hi₁, h1⟩

theorem card_eq_of_image (he₁ : Function.Injective e₁) (he₂ : Function.Injective e₂)
    (hp : p₁.image e₁ = p₂.image e₂) : p₁.card = p₂.card := by
  rw [← Finset.card_image_of_injective _ he₁, hp, Finset.card_image_of_injective _ he₂]

theorem sum_eq_of_image {β : Type*} [AddCommMonoid β] (he₁ : Function.Injective e₁)
    (he₂ : Function.Injective e₂) (hp : p₁.image e₁ = p₂.image e₂) (f₁ : ι₁ → β) (f₂ : ι₂ → β)
    (hf : ∀ i₁ ∈ p₁, ∀ i₂ ∈ p₂, e₁ i₁ = e₂ i₂ → f₁ i₁ = f₂ i₂) :
    ∑ i ∈ p₁, f₁ i = ∑ i ∈ p₂, f₂ i := by
  refine Finset.sum_bij (fun i hi => (exists_corr_left hp hi).choose)
    (fun i hi => (exists_corr_left hp hi).choose_spec.1) (fun i hi i' hi' h => ?_)
    (fun i₂ hi₂ => ?_) (fun i hi => ?_)
  · have h1 := (exists_corr_left hp hi).choose_spec.2
    have h2 := (exists_corr_left hp hi').choose_spec.2
    rw [h] at h1
    exact he₁ (h1.symm.trans h2)
  · obtain ⟨i₁, hi₁, h1⟩ := exists_corr_right hp hi₂
    refine ⟨i₁, hi₁, he₂ ?_⟩
    rw [(exists_corr_left hp hi₁).choose_spec.2, h1]
  · exact hf i hi _ (exists_corr_left hp hi).choose_spec.1
      ((exists_corr_left hp hi).choose_spec.2.symm)

theorem singleton_image {ι ι' : Type*} {e : ι → α} {e' : ι' → α} {p : Finset ι} {p' : Finset ι'}
    (he' : Function.Injective e') (hp : p.image e = p'.image e')
    (c : ι) (hc : p = {c}) : ∃ c', p' = {c'} ∧ e c = e' c' := by
  have h1 : p'.image e' = {e c} := by rw [← hp, hc]; simp
  have h2 : p'.card = 1 := by
    rw [← Finset.card_image_of_injective _ he', h1]; simp
  obtain ⟨c', hc'⟩ := Finset.card_eq_one.1 h2
  refine ⟨c', hc', ?_⟩
  rw [hc'] at h1
  simpa using h1.symm

theorem exists_singleton_iff (he₁ : Function.Injective e₁) (he₂ : Function.Injective e₂)
    (hp : p₁.image e₁ = p₂.image e₂) (φ₁ : ι₁ → Prop) (φ₂ : ι₂ → Prop)
    (hφ : ∀ i₁ ∈ p₁, ∀ i₂ ∈ p₂, e₁ i₁ = e₂ i₂ → (φ₁ i₁ ↔ φ₂ i₂)) :
    (∃ c, p₁ = {c} ∧ φ₁ c) ↔ ∃ c, p₂ = {c} ∧ φ₂ c := by
  constructor
  · rintro ⟨c, hc, hφ'⟩
    obtain ⟨c', hc', hee⟩ := singleton_image he₂ hp c hc
    refine ⟨c', hc', ?_⟩
    exact (hφ c (by rw [hc]; simp) c' (by rw [hc']; simp) hee).1 hφ'
  · rintro ⟨c, hc, hφ'⟩
    obtain ⟨c', hc', hee⟩ := singleton_image he₁ hp.symm c hc
    refine ⟨c', hc', ?_⟩
    exact (hφ c' (by rw [hc']; simp) c (by rw [hc]; simp) hee.symm).2 hφ'

end Index

section Hist

variable {S : Setting} {n₁ n₂ : ℕ → ℕ} [∀ k, NeZero (n₁ k)] [∀ k, NeZero (n₂ k)] {R : ℕ → ℝ}
  {k0 K : ℕ} (M : ℕ) [NeZero M] [NeZero S.L]

/-- Two sets of cubes of scale `j` of two tori correspond: their fine sets do (`SetCorr`). -/
def FCorr (cc : Fin S.d → ℤ) (j : ℕ) (A₁ : Finset (Torus S.d (n₁ j)))
    (A₂ : Finset (Torus S.d (n₂ j))) : Prop :=
  SetCorr cc (RegionHistory.fineSet (S := S) (n := n₁) M K j (A₁ : Set (Torus S.d (n₁ j))))
    (RegionHistory.fineSet (S := S) (n := n₂) M K j (A₂ : Set (Torus S.d (n₂ j))))

theorem fcorr_iff_clift (hnn₁ : ∀ i, i < K → n₁ i = S.L * n₁ (i + 1))
    (hnn₂ : ∀ i, i < K → n₂ i = S.L * n₂ (i + 1)) {j : ℕ} (hj : j ≤ K) (hP : 2 ≤ S.L ^ j * M)
    (hq₁ : 4 ≤ n₁ j) (hq₂ : 4 ≤ n₂ j) {cc : Fin S.d → ℤ} {A₁ : Finset (Torus S.d (n₁ j))}
    {A₂ : Finset (Torus S.d (n₂ j))} :
    FCorr M cc j A₁ A₂ (K := K) ↔
      GBox (S.L ^ j * M) (n₁ j) (M * n₁ K * S.L ^ K) (M * n₂ K * S.L ^ K) cc A₁ ∧
      GBox (S.L ^ j * M) (n₂ j) (M * n₂ K * S.L ^ K) (M * n₁ K * S.L ^ K) cc A₂ ∧
      cliftSet (S.L ^ j * M) cc A₁ = cliftSet (S.L ^ j * M) cc A₂ :=
  setCorr_iff_clift hP (Balaban.LargeField.fine_eq hnn₁ hj) (Balaban.LargeField.fine_eq hnn₂ hj)
    hq₁ hq₂


open RegionHistory

variable (H₁ : RegionHistory S n₁ R k0 K) (H₂ : RegionHistory S n₂ R k0 K)

/-- **The lineages and their new cubes of two components correspond.**  For components `Z₁`, `Z₂` of
`Z^pre_k` of two region histories on two tori: the lineages `Lin_j(Z)`, `j ≤ k`, and the new cubes
`Lin_{j+1}(Z) ∩ 𝒩_{j+1}`, `j < k`, correspond (their fine sets do). -/
def LinCorr (cc : Fin S.d → ℤ) (k : ℕ) (Z₁ : H₁.Comp k) (Z₂ : H₂.Comp k) : Prop :=
  (∀ j, j ≤ k → FCorr M cc j (H₁.lin j k Z₁) (H₂.lin j k Z₂) (K := K)) ∧
  (∀ j, j < k → FCorr M cc (j + 1) (H₁.lin (j + 1) k Z₁ ∩ H₁.newCubes (j + 1))
    (H₂.lin (j + 1) k Z₂ ∩ H₂.newCubes (j + 1)) (K := K))

variable {H₁ H₂}

/-- The sites of a component `Z` lie in the box with the margin of one cube. -/
def Marg {n : ℕ → ℕ} [∀ k, NeZero (n k)] (M K : ℕ) (cc : Fin S.d → ℤ)
    (m₁ m₂ k : ℕ) (Z : Finset (Torus S.d (n k))) : Prop :=
  ∀ x ∈ fineSet (S := S) (n := n) M K k (Z : Set (Torus S.d (n k))),
    InBoxK (S.L ^ k * M) m₁ m₂ cc (liftNear cc x)

theorem LinCorr.top {cc : Fin S.d → ℤ} {k : ℕ} {Z₁ : H₁.Comp k} {Z₂ : H₂.Comp k}
    (h : LinCorr M H₁ H₂ cc k Z₁ Z₂) : FCorr M cc k Z₁.1 Z₂.1 (K := K) := by
  have := h.1 k le_rfl
  rwa [lin_self, lin_self] at this

theorem LinCorr.old {cc : Fin S.d → ℤ} {j : ℕ} (hjK : j < K) {Z₁ : H₁.Comp (j + 1)}
    {Z₂ : H₂.Comp (j + 1)} (h : LinCorr M H₁ H₂ cc (j + 1) Z₁ Z₂) :
    FCorr M cc j (H₁.oldCubes j Z₁) (H₂.oldCubes j Z₂) (K := K) := by
  have := h.1 j (Nat.le_succ j)
  rwa [lin_succ_self H₁ hjK, lin_succ_self H₂ hjK] at this

theorem LinCorr.new {cc : Fin S.d → ℤ} {j : ℕ} {Z₁ : H₁.Comp (j + 1)}
    {Z₂ : H₂.Comp (j + 1)} (h : LinCorr M H₁ H₂ cc (j + 1) Z₁ Z₂) :
    FCorr M cc (j + 1) (Z₁.1 ∩ H₁.newCubes (j + 1)) (Z₂.1 ∩ H₂.newCubes (j + 1)) (K := K) := by
  have := h.2 j (Nat.lt_succ_self j)
  rwa [lin_self, lin_self] at this


variable {M}

/-- The hypotheses on the two tori: the scales up to `kmax` have at least `4` cubes per side. -/
structure CorrEnv (S : Setting) (n₁ n₂ : ℕ → ℕ) (M K kmax : ℕ) : Prop where
  hnn₁ : ∀ i, i < K → n₁ i = S.L * n₁ (i + 1)
  hnn₂ : ∀ i, i < K → n₂ i = S.L * n₂ (i + 1)
  hM : 2 ≤ M
  hL : 2 ≤ S.L
  hω : ∀ i, 0 < S.omega i
  hroom : ∀ i, i ≤ kmax → 4 ≤ n₁ i ∧ 4 ≤ n₂ i
  hkK : kmax ≤ K

theorem CorrEnv.P2 {kmax : ℕ} (E : CorrEnv S n₁ n₂ M K kmax) (j : ℕ) : 2 ≤ S.L ^ j * M :=
  le_trans E.hM (Nat.le_mul_of_pos_left _ (pow_pos (by have := E.hL; omega) _))

theorem CorrEnv.mono {kmax kmax' : ℕ} (E : CorrEnv S n₁ n₂ M K kmax) (h : kmax' ≤ kmax) :
    CorrEnv S n₁ n₂ M K kmax' :=
  ⟨E.hnn₁, E.hnn₂, E.hM, E.hL, E.hω, fun i hi => E.hroom i (hi.trans h), h.trans E.hkK⟩

/-- The lifted cube indices of a component. -/
noncomputable def partLift {n : ℕ → ℕ} [∀ k, NeZero (n k)] (M : ℕ) (cc : Fin S.d → ℤ) (j : ℕ)
    (A : Finset (Torus S.d (n j))) : Finset (Fin S.d → ℤ) :=
  cliftSet (S.L ^ j * M) cc A

theorem partLift_injective {n : ℕ → ℕ} [∀ k, NeZero (n k)] (M : ℕ) (cc : Fin S.d → ℤ) (j : ℕ) :
    Function.Injective (partLift (S := S) (n := n) M cc j) := by
  intro A B h
  ext y
  have := Finset.ext_iff.1 h (clift (S.L ^ j * M) cc y)
  simp only [partLift, mem_cliftSet] at this
  constructor
  · intro hy
    obtain ⟨y', hy', e⟩ := this.1 ⟨y, hy, rfl⟩
    rw [← clift_inj _ cc e]; exact hy'
  · intro hy
    obtain ⟨y', hy', e⟩ := this.2 ⟨y, hy, rfl⟩
    rw [← clift_inj _ cc e]; exact hy'

theorem fcorr_lifts {cc : Fin S.d → ℤ} {kmax : ℕ} (E : CorrEnv S n₁ n₂ M K kmax) {j : ℕ}
    (hj : j ≤ kmax) {A₁ : Finset (Torus S.d (n₁ j))} {A₂ : Finset (Torus S.d (n₂ j))}
    (h : FCorr M cc j A₁ A₂ (K := K)) :
    GBox (S.L ^ j * M) (n₁ j) (M * n₁ K * S.L ^ K) (M * n₂ K * S.L ^ K) cc A₁ ∧
    GBox (S.L ^ j * M) (n₂ j) (M * n₂ K * S.L ^ K) (M * n₁ K * S.L ^ K) cc A₂ ∧
    partLift M cc j A₁ = partLift M cc j A₂ :=
  (fcorr_iff_clift M E.hnn₁ E.hnn₂ (hj.trans E.hkK) (E.P2 j) (E.hroom j hj).1 (E.hroom j hj).2).1 h

theorem fcorr_of_lifts {cc : Fin S.d → ℤ} {kmax : ℕ} (E : CorrEnv S n₁ n₂ M K kmax) {j : ℕ}
    (hj : j ≤ kmax) {A₁ : Finset (Torus S.d (n₁ j))} {A₂ : Finset (Torus S.d (n₂ j))}
    (g₁ : GBox (S.L ^ j * M) (n₁ j) (M * n₁ K * S.L ^ K) (M * n₂ K * S.L ^ K) cc A₁)
    (g₂ : GBox (S.L ^ j * M) (n₂ j) (M * n₂ K * S.L ^ K) (M * n₁ K * S.L ^ K) cc A₂)
    (h : partLift M cc j A₁ = partLift M cc j A₂) : FCorr M cc j A₁ A₂ (K := K) :=
  (fcorr_iff_clift M E.hnn₁ E.hnn₂ (hj.trans E.hkK) (E.P2 j) (E.hroom j hj).1 (E.hroom j hj).2).2
    ⟨g₁, g₂, h⟩

theorem GBox.mono_subset {P q ℓ m' : ℕ} [NeZero ℓ] [NeZero q] {cc : Fin S.d → ℤ}
    {A B : Finset (Torus S.d q)} (hAB : B ⊆ A) (h : GBox P q ℓ m' cc A) : GBox P q ℓ m' cc B :=
  fun y hy => h y (hAB hy)


/-- The old parts of `Z'` have, under the lift, the components of the lifted set of cubes of `Z_j`
over `Z'`. -/
theorem parts_image_lift {n : ℕ → ℕ} [∀ k, NeZero (n k)] {cc : Fin S.d → ℤ}
    {m' : ℕ} (H : RegionHistory S n R k0 K) (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) {j : ℕ} (hjK : j < K) (Z' : H.Comp (j + 1))
    (hP2 : 2 ≤ S.L ^ j * M) (hq : 4 ≤ n j)
    (hA : GBox (S.L ^ j * M) (n j) (M * n K * S.L ^ K) m' cc (H.oldCubes j Z'))
    (hω : 0 < S.omega j) :
    (H.parts j Z').image (fun c => partLift M cc j c.1) = zcomps (S.omega j) (partLift M cc j (H.oldCubes j Z')) := by
  classical
  have h1 := parts_image_eq_comps H hjK Z'
  have h2 := image_comps hP2 (Balaban.LargeField.fine_eq hnn hjK.le) hq hA hω
  have : (H.parts j Z').image (fun c => partLift M cc j c.1) =
      ((H.parts j Z').image Subtype.val).image (Finset.image (clift (S.L ^ j * M) cc)) := by
    rw [Finset.image_image]; rfl
  rw [this, h1, h2]; rfl


theorem LinCorr.part {cc : Fin S.d → ℤ} {j : ℕ} (hjK : j + 1 ≤ K) {Z₁ : H₁.Comp (j + 1)}
    {Z₂ : H₂.Comp (j + 1)} {c₁ : H₁.Comp j} {c₂ : H₂.Comp j}
    (h : LinCorr M H₁ H₂ cc (j + 1) Z₁ Z₂) (hc₁ : c₁ ∈ H₁.parts j Z₁) (hc₂ : c₂ ∈ H₂.parts j Z₂)
    (hfc : FCorr M cc j c₁.1 c₂.1 (K := K)) : LinCorr M H₁ H₂ cc j c₁ c₂ := by
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · have e₁ : fineSet (S := S) (n := n₁) M K i ((H₁.lin i j c₁ : Finset _) : Set _) =
        fineSet (S := S) (n := n₁) M K i ((H₁.lin i (j + 1) Z₁ : Finset _) : Set _) ∩
          fineSet (S := S) (n := n₁) M K j (c₁.1 : Set _) :=
      Set.ext fun x => mem_fine_lin_part hjK hc₁ hi x
    have e₂ : fineSet (S := S) (n := n₂) M K i ((H₂.lin i j c₂ : Finset _) : Set _) =
        fineSet (S := S) (n := n₂) M K i ((H₂.lin i (j + 1) Z₂ : Finset _) : Set _) ∩
          fineSet (S := S) (n := n₂) M K j (c₂.1 : Set _) :=
      Set.ext fun x => mem_fine_lin_part hjK hc₂ hi x
    unfold FCorr
    rw [e₁, e₂]
    exact SetCorr.inter_iff (h.1 i (by omega)) hfc.setIff
  · have hi' : i + 1 ≤ j := hi
    have e₁ : fineSet (S := S) (n := n₁) M K (i + 1)
          ((H₁.lin (i + 1) j c₁ ∩ H₁.newCubes (i + 1) : Finset _) : Set _) =
        fineSet (S := S) (n := n₁) M K (i + 1)
          ((H₁.lin (i + 1) (j + 1) Z₁ ∩ H₁.newCubes (i + 1) : Finset _) : Set _) ∩
          fineSet (S := S) (n := n₁) M K j (c₁.1 : Set _) := by
      ext x
      have := mem_fine_lin_part hjK hc₁ hi' x
      simp only [fineSet, Finset.coe_inter, Set.mem_inter_iff, Set.mem_ofPred_eq, Finset.mem_coe] at this ⊢
      tauto
    have e₂ : fineSet (S := S) (n := n₂) M K (i + 1)
          ((H₂.lin (i + 1) j c₂ ∩ H₂.newCubes (i + 1) : Finset _) : Set _) =
        fineSet (S := S) (n := n₂) M K (i + 1)
          ((H₂.lin (i + 1) (j + 1) Z₂ ∩ H₂.newCubes (i + 1) : Finset _) : Set _) ∩
          fineSet (S := S) (n := n₂) M K j (c₂.1 : Set _) := by
      ext x
      have := mem_fine_lin_part hjK hc₂ hi' x
      simp only [fineSet, Finset.coe_inter, Set.mem_inter_iff, Set.mem_ofPred_eq, Finset.mem_coe] at this ⊢
      tauto
    unfold FCorr
    rw [e₁, e₂]
    exact SetCorr.inter_iff (h.2 i (by omega)) hfc.setIff

theorem Marg.part {n : ℕ → ℕ} [∀ k, NeZero (n k)] {cc : Fin S.d → ℤ} {m₁ m₂ j : ℕ}
    (H : RegionHistory S n R k0 K) (hjK : j + 1 ≤ K) {Z' : H.Comp (j + 1)} {c : H.Comp j}
    (hc : c ∈ H.parts j Z') (h : Marg (S := S) (n := n) M K cc m₁ m₂ (j + 1) Z'.1) :
    Marg (S := S) (n := n) M K cc m₁ m₂ j c.1 := by
  intro x hx
  have hx' : x ∈ fineSet (S := S) (n := n) M K (j + 1) (Z'.1 : Set _) := by
    have hs := ((H.mem_parts j c Z').1 hc).2
    have : blockMap S.L (n (j + 1)) (cubeMap n S.L M K j x) ∈ Z'.1 :=
      hs ⟨_, hx, rfl⟩
    show cubeMap n S.L M K (j + 1) x ∈ (Z'.1 : Set _)
    rw [← cubeMap_succ H.F.hnn hjK x]
    exact this
  refine (h x hx').mono ?_
  have : S.L ^ j * M ≤ S.L ^ (j + 1) * M :=
    Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (Nat.pos_of_ne_zero (NeZero.ne S.L)) (Nat.le_succ j))
  exact this


theorem spineTarget_corr {cc : Fin S.d → ℤ} {j : ℕ} {Z₁ : H₁.Comp (j + 1)}
    {Z₂ : H₂.Comp (j + 1)} (Γs₁ : H₁.Comp j → Spine S.d) (Γs₂ : H₂.Comp j → Spine S.d)
    (hsmall : (j + 1 ≤ k0 ∧ IsSmall (Z₁.1 : Set (Torus S.d (n₁ (j + 1)))) ∧
        side (Z₁.1 : Set (Torus S.d (n₁ (j + 1)))) ≤ S.crit (j + 1)) ↔
      (j + 1 ≤ k0 ∧ IsSmall (Z₂.1 : Set (Torus S.d (n₂ (j + 1)))) ∧
        side (Z₂.1 : Set (Torus S.d (n₂ (j + 1)))) ≤ S.crit (j + 1)))
    (hnew : (Z₁.1 ∩ H₁.newCubes (j + 1)).card = (Z₂.1 ∩ H₂.newCubes (j + 1)).card)
    (hp : (H₁.parts j Z₁).image (fun c => partLift M cc j c.1) =
      (H₂.parts j Z₂).image (fun c => partLift M cc j c.1))
    (hΓ : ∀ c₁ ∈ H₁.parts j Z₁, ∀ c₂ ∈ H₂.parts j Z₂, partLift M cc j c₁.1 = partLift M cc j c₂.1 →
      (Γs₁ c₁).length = (Γs₂ c₂).length) :
    H₁.spineTarget j Γs₁ Z₁ = H₂.spineTarget j Γs₂ Z₂ := by
  classical
  have he₁ : Function.Injective (fun c : H₁.Comp j => partLift M cc j c.1) :=
    (partLift_injective M cc j).comp Subtype.val_injective
  have he₂ : Function.Injective (fun c : H₂.Comp j => partLift M cc j c.1) :=
    (partLift_injective M cc j).comp Subtype.val_injective
  have hcard := card_eq_of_image he₁ he₂ hp
  have hsum := sum_eq_of_image he₁ he₂ hp (fun c => (Γs₁ c).length / S.L)
    (fun c => (Γs₂ c).length / S.L) (fun c₁ hc₁ c₂ hc₂ h => by rw [hΓ c₁ hc₁ c₂ hc₂ h])
  have hex := exists_singleton_iff he₁ he₂ hp (fun c => (Γs₁ c).length ≤ S.L)
    (fun c => (Γs₂ c).length ≤ S.L) (fun c₁ hc₁ c₂ hc₂ h => by rw [hΓ c₁ hc₁ c₂ hc₂ h])
  unfold RegionHistory.spineTarget
  refine if_congr hsmall rfl (if_congr (and_congr (by rw [hnew]) hex) rfl ?_)
  rw [hsum, hcard, hnew]

theorem nextBook_len_congr {ι : Type*} (μ : ℕ) (parts : Finset ι) (f : ι → Book) (r : ℕ)
    (Γ Γ' : Spine S.d) (h : Γ.length = Γ'.length) :
    S.nextBook μ parts f r Γ = S.nextBook μ parts f r Γ' := by
  simp only [Setting.nextBook, h]


theorem Marg.gboxK₁ {n : ℕ → ℕ} [∀ k, NeZero (n k)] {cc : Fin S.d → ℤ} {j : ℕ} {m' : ℕ}
    {A : Finset (Torus S.d (n j))}
    (h : Marg (S := S) (n := n) M K cc (M * n K * S.L ^ K) m' j A) :
    GBoxK (S.L ^ j * M) (S.L ^ j * M) (n j) (M * n K * S.L ^ K) m' cc A :=
  fun y hy x hx => h x (by
    show cubeMap n S.L M K j x ∈ (A : Set _)
    simp only [cubeMap, hx]; exact hy)

theorem Marg.gboxK₂ {n : ℕ → ℕ} [∀ k, NeZero (n k)] {cc : Fin S.d → ℤ} {j : ℕ} {m' : ℕ}
    {A : Finset (Torus S.d (n j))}
    (h : Marg (S := S) (n := n) M K cc m' (M * n K * S.L ^ K) j A) :
    GBoxK (S.L ^ j * M) (S.L ^ j * M) (n j) (M * n K * S.L ^ K) m' cc A :=
  fun y hy x hx => (h x (by
    show cubeMap n S.L M K j x ∈ (A : Set _)
    simp only [cubeMap, hx]; exact hy)).symm

theorem small_corr {kmax : ℕ} (E : CorrEnv S n₁ n₂ M K kmax) {cc : Fin S.d → ℤ} {j : ℕ}
    (hj : j ≤ kmax) {Z₁ : H₁.Comp j} {Z₂ : H₂.Comp j} (h : FCorr M cc j Z₁.1 Z₂.1 (K := K))
    (m₁ : Marg (S := S) (n := n₁) M K cc (M * n₁ K * S.L ^ K) (M * n₂ K * S.L ^ K) j Z₁.1)
    (m₂ : Marg (S := S) (n := n₂) M K cc (M * n₁ K * S.L ^ K) (M * n₂ K * S.L ^ K) j Z₂.1) :
    (IsSmall (Z₁.1 : Set (Torus S.d (n₁ j))) ∧ IsSmall (Z₂.1 : Set (Torus S.d (n₂ j))) ∧
      side (Z₁.1 : Set (Torus S.d (n₁ j))) = side (Z₂.1 : Set (Torus S.d (n₂ j)))) := by
  obtain ⟨-, -, hl⟩ := fcorr_lifts E hj h
  have a₁ := isSmall_side (E.P2 j) (Balaban.LargeField.fine_eq E.hnn₁ (hj.trans E.hkK))
    (E.hroom j hj).1 (Marg.gboxK₁ m₁) (comp_nonempty Z₁.2)
  have a₂ := isSmall_side (E.P2 j) (Balaban.LargeField.fine_eq E.hnn₂ (hj.trans E.hkK))
    (E.hroom j hj).2 (Marg.gboxK₂ m₂) (comp_nonempty Z₂.2)
  refine ⟨a₁.1, a₂.1, ?_⟩
  rw [a₁.2, a₂.2]
  exact congrArg zside hl


/-- Common facts at a step of the induction: the old parts of corresponding components. -/
theorem parts_corr {kmax : ℕ} (E : CorrEnv S n₁ n₂ M K kmax) {cc : Fin S.d → ℤ} {j : ℕ}
    (hj : j + 1 ≤ kmax) {Z₁ : H₁.Comp (j + 1)} {Z₂ : H₂.Comp (j + 1)}
    (h : LinCorr M H₁ H₂ cc (j + 1) Z₁ Z₂) :
    (H₁.parts j Z₁).image (fun c => partLift M cc j c.1) =
      (H₂.parts j Z₂).image (fun c => partLift M cc j c.1) := by
  have hjK : j < K := by have := E.hkK; omega
  obtain ⟨g₁, g₂, hl⟩ := fcorr_lifts E (by omega : j ≤ kmax) (h.old (M := M) hjK)
  rw [parts_image_lift H₁ E.hnn₁ hjK Z₁ (E.P2 j) (E.hroom j (by omega)).1 g₁ (E.hω j),
    parts_image_lift H₂ E.hnn₂ hjK Z₂ (E.P2 j) (E.hroom j (by omega)).2 g₂ (E.hω j), hl]

theorem part_fcorr {kmax : ℕ} (E : CorrEnv S n₁ n₂ M K kmax) {cc : Fin S.d → ℤ} {j : ℕ}
    (hj : j + 1 ≤ kmax) {Z₁ : H₁.Comp (j + 1)} {Z₂ : H₂.Comp (j + 1)}
    (h : LinCorr M H₁ H₂ cc (j + 1) Z₁ Z₂) {c₁ : H₁.Comp j} {c₂ : H₂.Comp j}
    (hc₁ : c₁ ∈ H₁.parts j Z₁) (hc₂ : c₂ ∈ H₂.parts j Z₂)
    (hl : partLift M cc j c₁.1 = partLift M cc j c₂.1) : FCorr M cc j c₁.1 c₂.1 (K := K) := by
  have hjK : j < K := by have := E.hkK; omega
  obtain ⟨g₁, g₂, -⟩ := fcorr_lifts E (by omega : j ≤ kmax) (h.old (M := M) hjK)
  have s₁ : c₁.1 ⊆ H₁.oldCubes j Z₁ := by
    rw [H₁.oldCubes_eq hjK]; exact Finset.subset_biUnion_of_mem (fun c : H₁.Comp j => c.1) hc₁
  have s₂ : c₂.1 ⊆ H₂.oldCubes j Z₂ := by
    rw [H₂.oldCubes_eq hjK]; exact Finset.subset_biUnion_of_mem (fun c : H₂.Comp j => c.1) hc₂
  exact fcorr_of_lifts E (by omega) (g₁.mono_subset s₁) (g₂.mono_subset s₂) hl

/-- A statement about corresponding components that holds for the pairs of corresponding
components with the margin holds for corresponding old parts. -/
theorem parts_ih {kmax : ℕ} (E : CorrEnv S n₁ n₂ M K kmax) {cc : Fin S.d → ℤ} {j : ℕ}
    (hj : j + 1 ≤ kmax) {Z₁ : H₁.Comp (j + 1)} {Z₂ : H₂.Comp (j + 1)}
    (h : LinCorr M H₁ H₂ cc (j + 1) Z₁ Z₂)
    (m₁ : Marg (S := S) (n := n₁) M K cc (M * n₁ K * S.L ^ K) (M * n₂ K * S.L ^ K) (j + 1) Z₁.1)
    (m₂ : Marg (S := S) (n := n₂) M K cc (M * n₁ K * S.L ^ K) (M * n₂ K * S.L ^ K) (j + 1) Z₂.1)
    (Q : H₁.Comp j → H₂.Comp j → Prop)
    (hQ : ∀ (c₁ : H₁.Comp j) (c₂ : H₂.Comp j), LinCorr M H₁ H₂ cc j c₁ c₂ →
      Marg (S := S) (n := n₁) M K cc (M * n₁ K * S.L ^ K) (M * n₂ K * S.L ^ K) j c₁.1 →
      Marg (S := S) (n := n₂) M K cc (M * n₁ K * S.L ^ K) (M * n₂ K * S.L ^ K) j c₂.1 → Q c₁ c₂) :
    ∀ c₁ ∈ H₁.parts j Z₁, ∀ c₂ ∈ H₂.parts j Z₂,
      partLift M cc j c₁.1 = partLift M cc j c₂.1 → Q c₁ c₂ := by
  intro c₁ hc₁ c₂ hc₂ hl
  have hfc := part_fcorr E hj h hc₁ hc₂ hl
  exact hQ c₁ c₂ (h.part (M := M) (by have := E.hkK; omega) hc₁ hc₂ hfc)
    (Marg.part H₁ (by have := E.hkK; omega) hc₁ m₁) (Marg.part H₂ (by have := E.hkK; omega) hc₂ m₂)

/-- **The book of a component is determined by the lineage and its new cubes, across tori.** -/
theorem bk_corr {kmax : ℕ} (E : CorrEnv S n₁ n₂ M K kmax) {cc : Fin S.d → ℤ} :
    ∀ (k : ℕ), k ≤ kmax → ∀ (Z₁ : H₁.Comp k) (Z₂ : H₂.Comp k),
      LinCorr M H₁ H₂ cc k Z₁ Z₂ →
      Marg (S := S) (n := n₁) M K cc (M * n₁ K * S.L ^ K) (M * n₂ K * S.L ^ K) k Z₁.1 →
      Marg (S := S) (n := n₂) M K cc (M * n₁ K * S.L ^ K) (M * n₂ K * S.L ^ K) k Z₂.1 →
      H₁.bk k Z₁ = H₂.bk k Z₂
  | 0, _, Z₁, _, _, _, _ => (H₁.F.isEmpty_comp_zero.false Z₁).elim
  | j + 1, hj, Z₁, Z₂, h, m₁, m₂ => by
    classical
    have hjK : j < K := by have := E.hkK; omega
    have hP := parts_corr E hj h
    have hIH := parts_ih E hj h m₁ m₂ (fun c₁ c₂ => H₁.bk j c₁ = H₂.bk j c₂)
      (fun c₁ c₂ hl m1 m2 => bk_corr E j (by omega) c₁ c₂ hl m1 m2)
    have hsm := small_corr E hj h.top m₁ m₂
    have hnew : (Z₁.1 ∩ H₁.newCubes (j + 1)).card = (Z₂.1 ∩ H₂.newCubes (j + 1)).card := by
      obtain ⟨-, -, hl⟩ := fcorr_lifts E hj h.new
      rw [← card_cliftSet (P := S.L ^ (j + 1) * M) (cc := cc) (Z₁.1 ∩ H₁.newCubes (j + 1)),
        ← card_cliftSet (P := S.L ^ (j + 1) * M) (cc := cc) (Z₂.1 ∩ H₂.newCubes (j + 1))]
      exact congrArg Finset.card hl
    have hlen : (H₁.spine (j + 1) Z₁).length = (H₂.spine (j + 1) Z₂).length := by
      rw [(H₁.spineCan_spine hjK Z₁).2, (H₂.spineCan_spine hjK Z₂).2]
      refine spineTarget_corr (M := M) (cc := cc) (H₁.spine j) (H₂.spine j) ?_ hnew hP ?_
      · obtain ⟨s1, s2, s3⟩ := hsm
        rw [s3]
        exact ⟨fun ⟨a, _, c⟩ => ⟨a, s2, c⟩, fun ⟨a, _, c⟩ => ⟨a, s1, c⟩⟩
      · intro c₁ hc₁ c₂ hc₂ hl
        rw [← H₁.bk_len, ← H₂.bk_len, hIH c₁ hc₁ c₂ hc₂ hl]
    show S.nextBook (j + 1) (H₁.parts j Z₁) (fun c => S.postBook k0 j (H₁.bk j c))
        (Z₁.1 ∩ H₁.newCubes (j + 1)).card (H₁.spine (j + 1) Z₁) =
      S.nextBook (j + 1) (H₂.parts j Z₂) (fun c => S.postBook k0 j (H₂.bk j c))
        (Z₂.1 ∩ H₂.newCubes (j + 1)).card (H₂.spine (j + 1) Z₂)
    rw [hnew, nextBook_len_congr (S := S) (j + 1) _ _ _ _ _ hlen.symm.symm]
    refine S.nextBook_congr (j + 1) (fun c : H₁.Comp j => partLift M cc j c.1)
      ((partLift_injective M cc j).comp Subtype.val_injective)
      (fun c : H₂.Comp j => partLift M cc j c.1)
      ((partLift_injective M cc j).comp Subtype.val_injective) _ _ _ _ (by convert hP) ?_ _ _
    intro c₁ hc₁ c₂ hc₂ hl
    simp only [hIH c₁ hc₁ c₂ hc₂ hl]

end Hist

end Balaban.RootFSpine
