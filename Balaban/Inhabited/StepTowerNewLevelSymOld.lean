/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepTowerNewLevelSymGeom
public import Balaban.Fluctuation.LocalClassLatCore
public import Balaban.Fluctuation.StepComplex
public import Balaban.SmallField.Def6v2
public import Balaban.Fluctuation.RootPavingMap
public import Balaban.Fluctuation.LocalClassLabels
public import Balaban.Fluctuation.LocalClassAssembly

/-!
# The old composite energy under the full level group (`StepTowerNewLevelSymOld`)

The old energy `ℰ_k(ψ, h) = ∑_{j ≤ k} ℰ^{(j)}(ψ_k^{(j)}, h)` of an inductive class is covariant
under the full level group on the domain of the level sets, by the clause `eucEloc` (the densities
`Eloc` at each centre, `P1 (H.4)`, `P4 (H.3)`).  The full group `fullJSymGroup L j` does not
preserve the paving, so the statements here use blocks only:

* `goodMap_of_mem_symGroupBy`: elements of `symGroupBy s'` map aligned boxes to aligned boxes;
* `image_box_blockBase_fullJ`, `blockBase_map_fullJ`: they permute the `L^j`-blocks;
* `sum_aligned_blockBase_fullJ`: `y ↦ blockBase (r y)` permutes the aligned sites;
* `Edens_fullJ`: `ℰ^{(j)}(rΨ, rh) = ℰ^{(j)}(Ψ, h)` from `eucEloc`;
* `composedPairAtC_sym`, `EcompAtC_sym`: the composed old pairs of a transported datum are the
  transported pairs, and `ℰ_k` is invariant.
-/

@[expose] public section

namespace Balaban.Inhabited.StepSym

open Balaban Balaban.Localization Balaban.SmallField Balaban.SmallField.Def6 Balaban.Fluctuation
  Balaban.Multiscale Balaban.Background Balaban.SmallField.Def6v2

section Align

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L]

/-- **A symmetry of the group `symGroupBy s'` maps aligned boxes onto aligned boxes** (`s ∣ s'`,
`s ∣ a`, `s ∣` the torus size), together with its inverse. -/
theorem goodMap_of_mem_symGroupBy (s' s a : ℕ) (hs : s ∣ s')
    (hsn : s ∣ (N₁ * L ^ m₁) * L ^ K) (ha : s ∣ a)
    {r : Equiv.Perm (CTorus d L N₁ m₁ K)}
    (hr : r ∈ symGroupBy (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) (L := L) s') :
    GoodMap s a r ∧ GoodMap s a r⁻¹ := by
  have hcs : ZMod.castHom hsn (ZMod s) ((s' : ℕ) : ZMod ((N₁ * L ^ m₁) * L ^ K)) = 0 := by
    rw [map_natCast]; exact (ZMod.natCast_eq_zero_iff _ _).2 hs
  refine Subgroup.closure_induction (p := fun r _ => GoodMap s a r ∧ GoodMap s a r⁻¹)
    ?_ ?_ ?_ ?_ hr
  · rintro g ((⟨μ, rfl⟩ | ⟨μ, rfl⟩) | ⟨μ, ν, rfl⟩)
    · have ht : ∀ i, ZMod.castHom hsn (ZMod s)
          ((s' • (Pi.single μ 1 : CTorus d L N₁ m₁ K)) i) = 0 := by
        intro i
        by_cases h : i = μ
        · subst h
          have : (s' • (Pi.single i 1 : CTorus d L N₁ m₁ K)) i =
              ((s' : ℕ) : ZMod ((N₁ * L ^ m₁) * L ^ K)) := by simp
          rw [this, hcs]
        · simp [Pi.single_eq_of_ne h]
      refine ⟨good_addRight hsn _ _ ht, ?_⟩
      have : (transBy (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) s' μ)⁻¹ =
          Equiv.addRight (-(s' • (Pi.single μ 1 : CTorus d L N₁ m₁ K))) := by
        ext x; simp [transBy, Equiv.Perm.inv_def]
      rw [this]
      refine good_addRight hsn _ _ fun i => ?_
      rw [Pi.neg_apply, map_neg, ht i, neg_zero]
    · have hf : GoodMap s a (flipBy (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) s' μ) := by
        refine good_flip μ _ _ (fun x => rfl) hsn hcs ha fun x => ?_
        ext i
        by_cases h : i = μ
        · subst h; simp [flipBy]
        · simp [flipBy, Function.update_of_ne h]
      exact ⟨hf, hf⟩
    · have hf : GoodMap s a (swapJ (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) μ ν) :=
        good_swap μ ν _ hsn (fun x => rfl)
      exact ⟨hf, hf⟩
  · exact ⟨GoodMap.one _ _, by rw [inv_one]; exact GoodMap.one _ _⟩
  · intro x y _ _ hx hy
    exact ⟨hx.1.mul hy.1, by rw [mul_inv_rev]; exact hy.2.mul hx.2⟩
  · intro x _ hx
    exact ⟨hx.2, by rw [inv_inv]; exact hx.1⟩

variable {j : ℕ}

/-- A symmetry of the full level group `fullJSymGroup L j` maps the `L^j`-block of a site onto the
`L^j`-block of its image, `j ≤ K`. -/
theorem image_box_blockBase_fullJ (hj : j ≤ K) {r : Equiv.Perm (CTorus d L N₁ m₁ K)}
    (hr : r ∈ fullJSymGroup (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L j)
    (y : CTorus d L N₁ m₁ K) :
    r '' box (blockBase (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L j y) (L ^ j) =
      box (blockBase (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L j (r y)) (L ^ j) := by
  have hL : 0 < L ^ j := Nat.pos_of_ne_zero (NeZero.ne _)
  obtain ⟨b', hb', himg⟩ :=
    (goodMap_of_mem_symGroupBy (L ^ j) (L ^ j) (L ^ j) dvd_rfl (pow_dvd_torus_of_le hj) dvd_rfl hr).1.boxes
      (blockBase (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L j y) (aligned_cbase _)
  have hmem : r y ∈ box b' (L ^ j) :=
    himg ▸ ⟨y, mem_box_cbase hL y, rfl⟩
  have : blockBase (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L j (r y) = b' :=
    cbase_eq_of_mem_box (pow_dvd_torus_of_le hj) hb' hmem
  rw [this, himg]

/-- A symmetry of the full level group sends two sites of the same `L^j`-block to two sites of the
same `L^j`-block. -/
theorem blockBase_map_fullJ (hj : j ≤ K) {r : Equiv.Perm (CTorus d L N₁ m₁ K)}
    (hr : r ∈ fullJSymGroup (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L j)
    {x x' : CTorus d L N₁ m₁ K}
    (h : blockBase (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L j x =
      blockBase (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L j x') :
    blockBase (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L j (r x) =
      blockBase (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L j (r x') := by
  have hL : 0 < L ^ j := Nat.pos_of_ne_zero (NeZero.ne _)
  have h1 := image_box_blockBase_fullJ hj hr x'
  have hx : x ∈ box (blockBase (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L j x') (L ^ j) := by
    rw [← h]; exact mem_box_cbase hL x
  have : r x ∈ box (blockBase (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L j (r x')) (L ^ j) := by
    rw [← h1]; exact ⟨x, hx, rfl⟩
  exact cbase_eq_of_mem_box (pow_dvd_torus_of_le hj) (aligned_cbase _) this

open Classical in
/-- **The block-base map of a full-group symmetry permutes the aligned sites**: for every function
`F` of the sites, `∑_{y aligned} F (blockBase (r y)) = ∑_{y aligned} F y`. -/
theorem sum_aligned_blockBase_fullJ {M : Type*} [AddCommMonoid M] (hj : j ≤ K)
    {r : Equiv.Perm (CTorus d L N₁ m₁ K)}
    (hr : r ∈ fullJSymGroup (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L j)
    (F : CTorus d L N₁ m₁ K → M) :
    ∑ y ∈ (Finset.univ : Finset (CTorus d L N₁ m₁ K)).filter (Aligned (L ^ j)),
        F (blockBase (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L j (r y)) =
      ∑ y ∈ (Finset.univ : Finset (CTorus d L N₁ m₁ K)).filter (Aligned (L ^ j)), F y := by
  have hrinv : r⁻¹ ∈ fullJSymGroup (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L j :=
    Subgroup.inv_mem _ hr
  refine Finset.sum_nbij'
    (fun y => blockBase (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L j (r y))
    (fun y => blockBase (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L j (r⁻¹ y))
    (fun y _ => by simp [blockBase, aligned_cbase])
    (fun y _ => by simp [blockBase, aligned_cbase])
    (fun y hy => ?_) (fun y hy => ?_) (fun y _ => rfl)
  · have hy' : Aligned (L ^ j) y := (Finset.mem_filter.1 hy).2
    have h1 : blockBase (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L j
        (r⁻¹ (blockBase L j (r y))) = blockBase L j y := by
      have := blockBase_map_fullJ hj hrinv
        (x := blockBase (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L j (r y)) (x' := r y)
        (by simp only [blockBase]; rw [cbase_eq_self_of_aligned (aligned_cbase _)])
      rw [this]; simp
    rw [h1]
    exact cbase_eq_self_of_aligned hy'
  · have hy' : Aligned (L ^ j) y := (Finset.mem_filter.1 hy).2
    have h1 : blockBase (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L j
        (r (blockBase L j (r⁻¹ y))) = blockBase L j y := by
      have := blockBase_map_fullJ hj hr
        (x := blockBase (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L j (r⁻¹ y)) (x' := r⁻¹ y)
        (by simp only [blockBase]; rw [cbase_eq_self_of_aligned (aligned_cbase _)])
      rw [this]; simp
    rw [h1]
    exact cbase_eq_self_of_aligned hy'

end Align

section Old

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ} {P : Consts}
  {Dom : FieldDom d L N₁ m₁ (k + 1) N ϱ} {Tm : Terms d L N₁ m₁ (k + 1) N ϱ}

open Classical in
/-- **The level density `ℰ^{(j)}` of an old class is covariant under the full group**, on pairs
`(Ψ, h)` and `(rΨ, rh)` of the domain of the level set `𝔹_j` (the clause `eucEloc` summed over
the aligned sites). -/
theorem Edens_fullJ (hcl : SFTermClauses P Dom Tm) {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k + 1)
    {r : Equiv.Perm (CTorus d L N₁ m₁ (k + 1))}
    (hr : r ∈ fullJSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L j)
    (Ψ h : Fld d L N₁ m₁ (k + 1) N)
    (h1 : Dom.dom j (levelGS (ϱ := ϱ) (N₁ := N₁) (m₁ := m₁) j hjk) Ψ h)
    (h2 : Dom.dom j (levelGS (ϱ := ϱ) (N₁ := N₁) (m₁ := m₁) j hjk) (actField r Ψ) (actField r h)) :
    Edens P.m₀ Tm j (actField r Ψ) (actField r h) = Edens P.m₀ Tm j Ψ h := by
  unfold Edens
  rw [← sum_aligned_blockBase_fullJ hjk hr (fun y => Eloc P.m₀ Tm j y (actField r Ψ) (actField r h))]
  exact Finset.sum_congr rfl fun y _ => hcl.eucEloc j hj1 hjk y r hr Ψ h h1 h2

variable {a : ℕ → ℝ} {ν : ℝ} {σ : Equiv.Perm (CTorus d L N₁ m₁ (k + 1))}

omit [NeZero N₁] [NeZero L] in
theorem actField_eq (g : Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) (Ψ : Fld d L N₁ m₁ (k + 1) N) :
    actField g Ψ = fun x => Ψ (g.symm x) := rfl

/-- **The composed old pair of a transported datum is the transported composed pair.** -/
theorem composedPairAtC_sym (hσ : σ ∈ fullJSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L (k + 1))
    (Sk : LatSymm (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) k
      (Nat.le_succ k)) (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) k
      (Nat.le_succ k)) σ)
    {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k)
    (E : BgData (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) k
      (Nat.le_succ k)) N) :
    composedPairAtC a ν (Nat.le_succ k) j (Sk.sym E) =
      (actField σ (composedPairAtC a ν (Nat.le_succ k) j E).1,
        actField σ (composedPairAtC a ν (Nat.le_succ k) j E).2) := by
  obtain ⟨Sj⟩ := nonempty_latSymm_of_isLevel (G := levelGS (d := d) (L := L) (N₁ := N₁)
    (m₁ := m₁) (k := k + 1) (ϱ := ϱ) j (hjk.trans (Nat.le_succ k)))
    (isLevel_levelGS hj1 (hjk.trans (Nat.le_succ k))) (n := j) (j := k + 1) (by omega) le_rfl hσ
  simp only [composedPairAtC, composedDataAtC, hjk, ↓reduceDIte]
  rw [(Sk.bgFieldC_sym a ν (bgC0 d L N) E).1,
    composeData_sym_pair Sj Sk (levelGS_precedes_at hjk (Nat.le_succ k))
      (levelGS_precedes_at hjk (Nat.le_succ k))]
  rfl

/-- **`ℰ_k` at the transported datum equals `ℰ_k`** (from `eucEloc` of the old class, on data whose
composed pairs lie in the domain of the level sets). -/
theorem EcompAtC_sym (hcl : SFTermClauses P Dom Tm)
    (hσ : σ ∈ fullJSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L (k + 1))
    (Sk : LatSymm (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) k
      (Nat.le_succ k)) (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) k
      (Nat.le_succ k)) σ)
    (E : BgData (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) k
      (Nat.le_succ k)) N)
    (hdom : ∀ j ∈ Finset.Icc 1 k, ∀ hjk : j ≤ k + 1,
      Dom.dom j (levelGS (ϱ := ϱ) (N₁ := N₁) (m₁ := m₁) j hjk)
        (composedPairAtC a ν (Nat.le_succ k) j E).1 (composedPairAtC a ν (Nat.le_succ k) j E).2)
    (hdom' : ∀ j ∈ Finset.Icc 1 k, ∀ hjk : j ≤ k + 1,
      Dom.dom j (levelGS (ϱ := ϱ) (N₁ := N₁) (m₁ := m₁) j hjk)
        (composedPairAtC a ν (Nat.le_succ k) j (Sk.sym E)).1
        (composedPairAtC a ν (Nat.le_succ k) j (Sk.sym E)).2) :
    EcompAtC P.m₀ Tm a ν (Nat.le_succ k) (Sk.sym E) = EcompAtC P.m₀ Tm a ν (Nat.le_succ k) E := by
  unfold EcompAtC
  refine Finset.sum_congr rfl fun j hj => ?_
  obtain ⟨hj1, hjk⟩ := Finset.mem_Icc.1 hj
  have hjk' : j ≤ k + 1 := hjk.trans (Nat.le_succ k)
  have hσj : σ ∈ fullJSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L j :=
    symGroupBy_le_of_dvd (pow_dvd_pow L hjk') (Nat.pos_of_ne_zero (pow_ne_zero _ (NeZero.ne L))) hσ
  have hc := composedPairAtC_sym (a := a) (ν := ν) hσ Sk hj1 hjk E
  have h2 := hdom' j hj hjk'
  rw [hc] at h2 ⊢
  exact Edens_fullJ hcl hj1 hjk' hσj _ _ (hdom j hj hjk') h2

end Old

end Balaban.Inhabited.StepSym
