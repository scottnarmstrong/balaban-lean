/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalClassAssembly
public import Balaban.Fluctuation.ClassOldTermInputE
public import Balaban.Fluctuation.LocalClassRot

/-!
# The old labels under the paving group of the new level; the rotation input from the old class

Inputs of the assembly of the local successor class (`LocalClassAssembleE.lean`) that come from
the old class at level `k`:

* `transBy_mul_eq_pow`, `transBy_mem_symGroupBy`, `symGroupBy_le_of_dvd`,
  `pavingSymGroup_le_of_le`: the paving group of the level `K` lies in the paving group of every
  level `j ≤ K` (translations by multiples, the reflection by `s'` is the reflection by `s` followed
  by a translation by `s' - s`), so the clauses `pavingGS`, `eucE` of the old class at the level `j`
  apply to the paving symmetries of the new level;
* `image_box_blockBase_of_le`, `blockBase_mem_image_of_le`, `blockBase_inv_blockBase_of_le`,
  `blockUnion_of_isPolyDom_of_le`: the `L^j`-blocks under the paving symmetries of the level `K`,
  `j ≤ K` (the landed statements are at `j = K`);
* `classLabels_bijOn_paving`: a paving symmetry `r` of the level `K` permutes the labels
  `(j, y, X)` of the old energy terms by `(j, y, X) ↦ (j, blockBase L j (r y), r X)` (the relabelling
  `π` of `localClass_avg_eq_sum_of_cov`);
* `classOldEnergy_rot_input`: the rotation input `hEr` of `localB_eTermHat_evTerm_rot` for the label
  functional `β⁻¹ ℰ^{(j)}(y, X; ·)`, from the clause `rotE` of the old class.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.SmallField Balaban.SmallField.Def6
  Balaban.SmallField.Def6v2 Balaban.Background Finset

section GroupLe

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L]

omit [NeZero N₁] [NeZero L] in
/-- A translation by `c s` is the `c`-th power of the translation by `s`. -/
theorem transBy_mul_eq_pow (s c : ℕ) (μ : Fin d) :
    transBy (N₁ := N₁) (m₁ := m₁) (k := K) (L := L) (s * c) μ =
      (transBy (N₁ := N₁) (m₁ := m₁) (k := K) (L := L) s μ) ^ c := by
  induction c with
  | zero => ext x i; simp [transBy]
  | succ c ih =>
    rw [pow_succ, ← ih]
    ext x i
    simp only [transBy, Equiv.coe_addRight, Equiv.Perm.mul_apply, Pi.add_apply, Pi.smul_apply]
    ring

omit [NeZero N₁] [NeZero L] in
/-- The translations by multiples of `s` lie in `symGroupBy s`. -/
theorem transBy_mem_symGroupBy {s t : ℕ} (h : s ∣ t) (μ : Fin d) :
    transBy (N₁ := N₁) (m₁ := m₁) (k := K) (L := L) t μ ∈
      symGroupBy (N₁ := N₁) (m₁ := m₁) (k := K) (L := L) s := by
  obtain ⟨c, rfl⟩ := h
  rw [transBy_mul_eq_pow]
  have hg : transBy (N₁ := N₁) (m₁ := m₁) (k := K) (L := L) s μ ∈
      symGroupBy (N₁ := N₁) (m₁ := m₁) (k := K) (L := L) s :=
    Subgroup.subset_closure (Or.inl (Or.inl ⟨μ, rfl⟩))
  exact Subgroup.pow_mem _ hg c

omit [NeZero N₁] [NeZero L] in
/-- **The symmetry groups decrease when the side grows by a factor**: for `s ∣ s'`, `0 < s'`,
`symGroupBy s' ≤ symGroupBy s` (the reflection by `s'` is the reflection by `s` followed by the
translation by `s' - s`). -/
theorem symGroupBy_le_of_dvd {s s' : ℕ} (hss : s ∣ s') (hs' : 0 < s') :
    symGroupBy (N₁ := N₁) (m₁ := m₁) (k := K) (L := L) (d := d) s' ≤
      symGroupBy (N₁ := N₁) (m₁ := m₁) (k := K) (L := L) s := by
  have hle : s ≤ s' := Nat.le_of_dvd hs' hss
  refine (Subgroup.closure_le _).2 ?_
  rintro g ((⟨μ, rfl⟩ | ⟨μ, rfl⟩) | ⟨μ, ν, rfl⟩)
  · exact transBy_mem_symGroupBy hss μ
  · have e : flipBy (N₁ := N₁) (m₁ := m₁) (k := K) (L := L) s' μ =
        transBy (N₁ := N₁) (m₁ := m₁) (k := K) (L := L) (s' - s) μ *
          flipBy (N₁ := N₁) (m₁ := m₁) (k := K) (L := L) s μ := by
      ext x i
      by_cases hi : i = μ
      · subst hi
        simp only [flipBy, transBy, Equiv.coe_fn_mk, Equiv.Perm.mul_apply, Equiv.coe_addRight,
          Pi.add_apply, Function.update_self, Pi.smul_apply, Pi.single_eq_same]
        rw [nsmul_eq_mul, mul_one, Nat.cast_sub hle]
        ring
      · simp [flipBy, transBy, Function.update_of_ne hi, Pi.single_eq_of_ne hi]
    rw [e]
    exact Subgroup.mul_mem _ (transBy_mem_symGroupBy (Nat.dvd_sub hss dvd_rfl) μ)
      (Subgroup.subset_closure (Or.inl (Or.inr ⟨μ, rfl⟩)))
  · exact Subgroup.subset_closure (Or.inr ⟨μ, ν, rfl⟩)

omit [NeZero N₁] in
/-- **The paving group of a level lies in the paving groups of the lower levels.** -/
theorem pavingSymGroup_le_of_le {m₀ j j' : ℕ} (hjj : j ≤ j') :
    pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L m₀ j' ≤
      pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L m₀ j :=
  symGroupBy_le_of_dvd (pow_dvd_pow L (by omega)) (cellSide_pos m₀ m₁ j')

end GroupLe


section LevelBlocks

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ j : ℕ}

omit [NeZero N₁] [NeZero L] in
theorem pow_dvd_torus_of_le (hj : j ≤ K) : L ^ j ∣ (N₁ * L ^ m₁) * L ^ K :=
  Dvd.dvd.mul_left (pow_dvd_pow L hj) _

/-- A paving symmetry of the level `K` maps the `L^j`-block of a site onto the `L^j`-block of its
image, `j ≤ K`. -/
theorem image_box_blockBase_of_le (hj : j ≤ K) {r : Equiv.Perm (CTorus d L N₁ m₁ K)}
    (hr : r ∈ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L m₀ K)
    (y : CTorus d L N₁ m₁ K) :
    r '' box (blockBase (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L j y) (L ^ j) =
      box (blockBase (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L j (r y)) (L ^ j) := by
  have hL : 0 < L ^ j := Nat.pos_of_ne_zero (NeZero.ne _)
  obtain ⟨b', hb', himg⟩ :=
    (goodMap_of_mem_pavingSymGroup (L ^ j) (L ^ j) (pow_dvd_pow L (by omega))
      (pow_dvd_torus_of_le hj) dvd_rfl hr).1.boxes
      (blockBase (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L j y) (aligned_cbase _)
  have hmem : r y ∈ box b' (L ^ j) :=
    himg ▸ ⟨y, mem_box_cbase hL y, rfl⟩
  have : blockBase (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L j (r y) = b' :=
    cbase_eq_of_mem_box (pow_dvd_torus_of_le hj) hb' hmem
  rw [this, himg]

/-- If `y ∈ X` and `X` is a union of `L^j`-blocks, the root of the transformed block of `y` lies in
`r '' X`. -/
theorem blockBase_mem_image_of_le (hj : j ≤ K) {r : Equiv.Perm (CTorus d L N₁ m₁ K)}
    (hr : r ∈ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L m₀ K)
    {X : Set (CTorus d L N₁ m₁ K)}
    (hX : ∀ x ∈ X, ∀ w, blockBase (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L j w =
      blockBase (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L j x → w ∈ X)
    {y : CTorus d L N₁ m₁ K} (hy : y ∈ X) :
    blockBase (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L j (r y) ∈ r '' X := by
  have hL : 0 < L ^ j := Nat.pos_of_ne_zero (NeZero.ne _)
  have h0 : blockBase (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L j (r y) ∈
      box (blockBase (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L j (r y)) (L ^ j) :=
    mem_box_self _ hL
  rw [← image_box_blockBase_of_le (m₀ := m₀) hj hr y] at h0
  obtain ⟨w, hw, hwe⟩ := h0
  refine ⟨w, hX y hy w ?_, hwe⟩
  exact cbase_eq_of_mem_box (pow_dvd_torus_of_le hj) (aligned_cbase _) hw

/-- The `L^j`-block of the preimage of the root of the image block is the block of `y`. -/
theorem blockBase_inv_blockBase_of_le (hj : j ≤ K) {r : Equiv.Perm (CTorus d L N₁ m₁ K)}
    (hr : r ∈ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L m₀ K)
    (y : CTorus d L N₁ m₁ K) :
    blockBase (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L j
        (r⁻¹ (blockBase (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L j (r y))) =
      blockBase (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L j y := by
  have hL : 0 < L ^ j := Nat.pos_of_ne_zero (NeZero.ne _)
  have h0 : blockBase (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L j (r y) ∈
      box (blockBase (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L j (r y)) (L ^ j) :=
    mem_box_self _ hL
  rw [← image_box_blockBase_of_le (m₀ := m₀) hj hr y] at h0
  obtain ⟨w, hw, hwe⟩ := h0
  have : r⁻¹ (blockBase (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L j (r y)) = w := by
    rw [← hwe]; simp [Equiv.Perm.inv_def]
  rw [this]
  exact cbase_eq_of_mem_box (pow_dvd_torus_of_le hj) (aligned_cbase _) hw

/-- A polymer of `𝒟_j` is a union of `L^j`-blocks, `j ≤ K`. -/
theorem blockUnion_of_isPolyDom_of_le (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K)
    {X : Set (CTorus d L N₁ m₁ K)}
    (hX : IsPolyDom (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) m₀ j X) :
    ∀ x ∈ X, ∀ w, blockBase (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L j w =
      blockBase (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L j x → w ∈ X := by
  intro x hx w hw
  have hdvd := cellSide_dvd (K := K) (m₁ := m₁) hN hj
  have ha0 := cellSide_pos (L := L) m₀ m₁ j
  have hL : 0 < L ^ j := Nat.pos_of_ne_zero (NeZero.ne _)
  obtain ⟨-, ⟨𝒦, h1, h2⟩, -⟩ := hX
  obtain ⟨b, hb, hxb⟩ := h2 x hx
  obtain ⟨c, hc⟩ := (pow_dvd_cellSide (L := L) (K := j) (m₀ := m₀) (m₁ := m₁))
  have hsame : cbase (cellSide L m₀ m₁ j) w = cbase (cellSide L m₀ m₁ j) x := by
    funext μ
    have hμ := congrArg (fun t : CTorus d L N₁ m₁ K => (t μ).val) hw
    simp only [blockBase, cbase_val] at hμ
    have hq : (w μ).val / L ^ j = (x μ).val / L ^ j := Nat.eq_of_mul_eq_mul_left hL hμ
    simp only [cbase]
    rw [hc, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, hq]
  have hwx : w ∈ box (cbase (cellSide L m₀ m₁ j) x) (cellSide L m₀ m₁ j) := by
    rw [← hsame]; exact mem_box_cbase ha0 w
  exact (h1 b hb).2 (cell_subset_cube hdvd ha0 (h1 b hb).1 hxb hwx)

end LevelBlocks

section Labels

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L]

open Classical in
/-- **The paving symmetries of the level `K` permute the labels of the old energy terms.**  The
labels are the triples `(j, y, X)`, `1 ≤ j ≤ k ≤ K`, `y` an `L^j`-aligned site, `X ∈ 𝒟_j`,
`y ∈ X` (`mem_classLabels_E_iff` on the step torus); for `r ∈ pavingSymGroup L m₀ K`, the map
`(j, y, X) ↦ (j, blockBase L j (r y), r X)` is a bijection of the label set onto itself
(`r` lies in the paving group of every level `j ≤ K`, `pavingSymGroup_le_of_le`).  This is the
relabelling `π` of `localClass_avg_eq_sum_of_cov`. -/
theorem classLabels_bijOn_paving {m₀ k : ℕ} (hN : L ^ m₀ ∣ N₁) (hkK : k ≤ K)
    {r : Equiv.Perm (CTorus d L N₁ m₁ K)}
    (hr : r ∈ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L m₀ K) :
    Set.BijOn (fun τ : ℕ × CTorus d L N₁ m₁ K × Set (CTorus d L N₁ m₁ K) =>
        (τ.1, blockBase (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L τ.1 (r τ.2.1), r '' τ.2.2))
      ↑(((Finset.Icc 1 k) ×ˢ (Finset.univ : Finset (CTorus d L N₁ m₁ K ×
          Set (CTorus d L N₁ m₁ K)))).filter
        (fun τ => Aligned (L ^ τ.1) τ.2.1 ∧ IsPolyDom m₀ τ.1 τ.2.2 ∧ τ.2.1 ∈ τ.2.2))
      ↑(((Finset.Icc 1 k) ×ˢ (Finset.univ : Finset (CTorus d L N₁ m₁ K ×
          Set (CTorus d L N₁ m₁ K)))).filter
        (fun τ => Aligned (L ^ τ.1) τ.2.1 ∧ IsPolyDom m₀ τ.1 τ.2.2 ∧ τ.2.1 ∈ τ.2.2)) := by
  have hri : r⁻¹ ∈ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L m₀ K := inv_mem hr
  have mem : ∀ τ : ℕ × CTorus d L N₁ m₁ K × Set (CTorus d L N₁ m₁ K),
      τ ∈ (((Finset.Icc 1 k) ×ˢ (Finset.univ : Finset (CTorus d L N₁ m₁ K ×
          Set (CTorus d L N₁ m₁ K)))).filter
        (fun τ => Aligned (L ^ τ.1) τ.2.1 ∧ IsPolyDom m₀ τ.1 τ.2.2 ∧ τ.2.1 ∈ τ.2.2) :
          Set (ℕ × CTorus d L N₁ m₁ K × Set (CTorus d L N₁ m₁ K))) ↔
      (1 ≤ τ.1 ∧ τ.1 ≤ k) ∧ Aligned (L ^ τ.1) τ.2.1 ∧ IsPolyDom m₀ τ.1 τ.2.2 ∧ τ.2.1 ∈ τ.2.2 :=
    fun τ => by simp [Finset.mem_product, Finset.mem_Icc]
  -- the image of a label is a label
  have hmap : ∀ {r' : Equiv.Perm (CTorus d L N₁ m₁ K)},
      r' ∈ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L m₀ K →
      ∀ τ : ℕ × CTorus d L N₁ m₁ K × Set (CTorus d L N₁ m₁ K),
      (1 ≤ τ.1 ∧ τ.1 ≤ k) ∧ Aligned (L ^ τ.1) τ.2.1 ∧ IsPolyDom m₀ τ.1 τ.2.2 ∧ τ.2.1 ∈ τ.2.2 →
      (1 ≤ τ.1 ∧ τ.1 ≤ k) ∧
        Aligned (L ^ τ.1) (blockBase (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L τ.1 (r' τ.2.1)) ∧
        IsPolyDom m₀ τ.1 (r' '' τ.2.2) ∧
        blockBase (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L τ.1 (r' τ.2.1) ∈ r' '' τ.2.2 := by
    intro r' hr' τ ⟨hjk, _, hX, hy⟩
    have hj : τ.1 ≤ K := hjk.2.trans hkK
    exact ⟨hjk, aligned_cbase _,
      isPolyDom_image_of_mem_pavingSymGroup hN hj hX (pavingSymGroup_le_of_le hj hr'),
      blockBase_mem_image_of_le hj hr' (blockUnion_of_isPolyDom_of_le hN hj hX) hy⟩
  refine ⟨fun τ hτ => (mem _).2 (hmap hr τ ((mem τ).1 hτ)), fun τ hτ τ' hτ' he => ?_,
    fun τ' hτ' => ?_⟩
  · obtain ⟨j, y, X⟩ := τ
    obtain ⟨j', y', X'⟩ := τ'
    obtain ⟨hjk, hal, -, -⟩ := (mem _).1 hτ
    obtain ⟨-, hal', -, -⟩ := (mem _).1 hτ'
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, h2, h3⟩ := he
    have hj : j ≤ K := hjk.2.trans hkK
    have hX : X = X' := Set.image_injective.2 r.injective h3
    have hb : blockBase (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L j y = y :=
      cbase_eq_self_of_aligned hal
    have hb' : blockBase (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L j y' = y' :=
      cbase_eq_self_of_aligned hal'
    have e1 := blockBase_inv_blockBase_of_le (m₀ := m₀) hj hr y
    have e2 := blockBase_inv_blockBase_of_le (m₀ := m₀) hj hr y'
    rw [h2, e2, hb, hb'] at e1
    rw [hX, e1]
  · obtain ⟨j, y', X'⟩ := τ'
    obtain ⟨hjk, hal, hX, hy⟩ := (mem _).1 hτ'
    have hj : j ≤ K := hjk.2.trans hkK
    have hb' : blockBase (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L j y' = y' :=
      cbase_eq_self_of_aligned hal
    refine ⟨(j, blockBase (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L j (r⁻¹ y'),
      (⇑(r⁻¹)) '' X'), (mem _).2 (hmap hri (j, y', X') ⟨hjk, hal, hX, hy⟩), ?_⟩
    have e := blockBase_inv_blockBase_of_le (m₀ := m₀) hj hri y'
    rw [inv_inv] at e
    refine Prod.ext rfl (Prod.ext (e.trans hb') ?_)
    show r '' ((⇑(r⁻¹)) '' X') = X'
    rw [Set.image_image]
    simp [Equiv.Perm.inv_def]

end Labels

section RotInput

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}

open Matrix in
/-- **The rotation input of the per-label theorems from the old class** (the hypothesis `hEr` of
`localB_eTermHat_evTerm_rot`): for a label `τ = (j, y, X)` of the old energy terms of a class
member `C` whose chart `Ξ^c(𝔹_j(X); σ, ε)` lies in the field domain of the class (`hchart`, as in
`classOldEnergy_analytic_bound`), the label functional `EE τ = β⁻¹ ℰ^{(j)}(y, X; ·)` is invariant
under every real orthogonal `Q` on the chart (the clause `rotE` of the class; the chart is invariant,
`xiCData_rot`). -/
theorem classOldEnergy_rot_input {P : Consts} {Dom : FieldDom d L N₁ m₁ (k + 1) N ϱ}
    (C : StepClass d L N₁ m₁ k N ϱ) (hm : P.m₀ = C.m₀) (hcl : SFTermClauses P Dom C.Tm)
    (β : ℝ) (a : ℕ → ℝ) (ν σ ε : ℝ)
    {τ : ℕ × CTorus d L N₁ m₁ (k + 1) × Set (CTorus d L N₁ m₁ (k + 1))}
    (hτ : (1 ≤ τ.1 ∧ τ.1 ≤ k) ∧ IsPolyDom C.m₀ τ.1 τ.2.2 ∧ τ.2.1 ∈ τ.2.2)
    (hchart : ∀ r ∈ XiCRaw (C.Tm.gs τ.1 τ.2.2) a ν τ.1 σ ε,
      Dom.dom τ.1 (C.Tm.gs τ.1 τ.2.2) r.1 r.2)
    {Q : Matrix (Fin N) (Fin N) ℝ} (hQ : Qᵀ * Q = 1) :
    ∀ r ∈ XiCRaw (C.Tm.gs τ.1 τ.2.2) a ν τ.1 σ ε,
      (β : ℂ)⁻¹ * C.Tm.E τ.1 τ.2.1 τ.2.2 (rotRaw (cmat Q) r).1 (rotRaw (cmat Q) r).2 =
        (β : ℂ)⁻¹ * C.Tm.E τ.1 τ.2.1 τ.2.2 r.1 r.2 := by
  intro r hr
  obtain ⟨⟨h1, h2⟩, hX, hy⟩ := hτ
  obtain ⟨D, hD, rfl⟩ := hr
  have hrot : rotRaw (cmat Q) (rawOf D) ∈ XiCRaw (C.Tm.gs τ.1 τ.2.2) a ν τ.1 σ ε :=
    ⟨D.rot (cmat Q), xiCData_rot hQ hD, rfl⟩
  have hR : IsRot (cmat Q) := ⟨(isRealOrth_ofReal hQ).1, Or.inl (isRealOrth_ofReal hQ).2⟩
  congr 1
  exact hcl.rotE τ.1 h1 (h2.trans (Nat.le_succ k)) τ.2.1 τ.2.2 (hm ▸ hX) hy (cmat Q) hR _ _
    (hchart _ ⟨D, hD, rfl⟩) (hchart _ hrot)

end RotInput

end Balaban.Fluctuation
