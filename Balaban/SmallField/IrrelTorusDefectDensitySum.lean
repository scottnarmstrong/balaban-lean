/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.IrrelTorusDefectDensity

/-!
# The filed sum at an aligned centre is the filed sum at the origin

For the lifted context of a torus (`LiftCtx`), the complete sum over the polymers through an
aligned centre `y` of the filed term `T_Z + Φ_{y,Z}` is the affine expression
`V + (u - 1) A + (w - 1) H - ¼ ∑ g S` of four jets of the density
(`LiftCtx.sum_filed_eq_density`): the value `V`, the sum `A` of the first derivatives over the
aligned blocks, the derivative `H` in `h`, and the weighted sum `S` of the second derivatives.
These jets do not depend on the aligned centre, by the covariance of the density under the
translations of the level-`j` lattice, so the sum at `y` is the sum at the origin with the same
coefficients (`LiftCtx.sum_filed_translate`).
-/

@[expose] public section

namespace Balaban.SmallField.Def6

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.Fluctuation
  Balaban.SmallField Filter Metric Set

section Torus

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ} {P : Consts} {β ν a : ℕ → ℝ}
  {Tm : Terms d L N₁ m₁ k N ϱ}
  {ρd : (CTorus d L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) → (CTorus d L N₁ m₁ k → Fin N → ℝ) → ℝ}
  {Ek : ℝ} {j : ℕ} {ρ : ℝ}

open Classical in
/-- The first order sum of the terms is the derivative of the density, summed over the aligned
blocks. -/
theorem LiftCtx.sum_blk_fderiv_E (ctx : LiftCtx P β ν a Tm ρd Ek j ρ) (hN : L ^ P.m₀ ∣ N₁)
    (i₀ : Fin N) (y : CTorus d L N₁ m₁ k) :
    ∑ Z ∈ (Set.toFinite (polysAt (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k)
        P.m₀ j y)).toFinset,
      ∑ x ∈ Finset.univ.filter (fun x => Aligned (L ^ j) x ∧ x ∈ Z),
        fderiv ℂ (fun Ψ' : Fld d L N₁ m₁ k N => Tm.E j y Z Ψ' (eFld d L N₁ m₁ k N i₀))
          (eFld d L N₁ m₁ k N i₀) (blockDir L j x i₀) =
      ∑ x ∈ Finset.univ.filter (Aligned (L ^ j)),
        fderiv ℂ (fun ψ : Fld d L N₁ m₁ k N => Eloc P.m₀ Tm j y ψ (eFld d L N₁ m₁ k N i₀))
          (eFld d L N₁ m₁ k N i₀) (blockDir L j x i₀) := by
  have hfin := Set.toFinite (polysAt (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P.m₀ j y)
  have hEloc : (fun ψ : Fld d L N₁ m₁ k N => Eloc P.m₀ Tm j y ψ (eFld d L N₁ m₁ k N i₀)) =
      fun ψ => ∑ X ∈ hfin.toFinset, Tm.E j y X ψ (eFld d L N₁ m₁ k N i₀) := by
    funext ψ
    unfold Eloc
    exact finsum_mem_eq_finite_toFinset_sum _ hfin
  have hsub : ∀ X ∈ hfin.toFinset,
      ∑ x ∈ Finset.univ.filter (fun x => Aligned (L ^ j) x ∧ x ∈ X),
        fderiv ℂ (fun Ψ' : Fld d L N₁ m₁ k N => Tm.E j y X Ψ' (eFld d L N₁ m₁ k N i₀))
          (eFld d L N₁ m₁ k N i₀) (blockDir L j x i₀) =
      ∑ x ∈ Finset.univ.filter (Aligned (L ^ j)),
        fderiv ℂ (fun Ψ' : Fld d L N₁ m₁ k N => Tm.E j y X Ψ' (eFld d L N₁ m₁ k N i₀))
          (eFld d L N₁ m₁ k N i₀) (blockDir L j x i₀) := by
    intro X hX
    have hX' := hfin.mem_toFinset.1 hX
    refine Finset.sum_subset (fun x hx => ?_) (fun x hx hxn => ?_)
    · exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 hx).2.1⟩
    · have hxX : x ∉ X := fun h => hxn (Finset.mem_filter.2
        ⟨Finset.mem_univ _, (Finset.mem_filter.1 hx).2, h⟩)
      exact ctx.fderiv_E_zero_of_not_mem hN i₀ y hX'.1 hxX _ _
  rw [Finset.sum_congr rfl hsub, Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [hEloc, fderiv_fun_sum fun X hX =>
    (ctx.analyticAt_E i₀ y ((hfin.mem_toFinset.1 hX).1) ((hfin.mem_toFinset.1 hX).2)).differentiableAt,
    _root_.sum_apply]

open Classical in
/-- The derivative in `h` of the density is the sum of the derivatives of the terms. -/
theorem LiftCtx.sum_fderiv_E_h (ctx : LiftCtx P β ν a Tm ρd Ek j ρ) (i₀ : Fin N)
    (y : CTorus d L N₁ m₁ k) :
    ∑ Z ∈ (Set.toFinite (polysAt (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k)
        P.m₀ j y)).toFinset,
      fderiv ℂ (fun h' : Fld d L N₁ m₁ k N => Tm.E j y Z (eFld d L N₁ m₁ k N i₀) h')
        (eFld d L N₁ m₁ k N i₀) (eFld d L N₁ m₁ k N i₀) =
      fderiv ℂ (fun h' : Fld d L N₁ m₁ k N => Eloc P.m₀ Tm j y (eFld d L N₁ m₁ k N i₀) h')
        (eFld d L N₁ m₁ k N i₀) (eFld d L N₁ m₁ k N i₀) := by
  have hfin := Set.toFinite (polysAt (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P.m₀ j y)
  have hEloc : (fun h' : Fld d L N₁ m₁ k N => Eloc P.m₀ Tm j y (eFld d L N₁ m₁ k N i₀) h') =
      fun h' => ∑ X ∈ hfin.toFinset, Tm.E j y X (eFld d L N₁ m₁ k N i₀) h' := by
    funext h'
    unfold Eloc
    exact finsum_mem_eq_finite_toFinset_sum _ hfin
  rw [hEloc, fderiv_fun_sum fun X hX => by
    have hXm := hfin.mem_toFinset.1 hX
    exact (AnalyticAt.comp (f := fun h' : Fld d L N₁ m₁ k N => (eFld d L N₁ m₁ k N i₀, h'))
      (ctx.analyticAt_E_pair i₀ y hXm.1 hXm.2) (analyticAt_const.prod analyticAt_id)).differentiableAt,
    _root_.sum_apply]

open Classical in
/-- The second order sum of the terms is the second derivative of the density, summed over the
pairs of aligned blocks. -/
theorem LiftCtx.sum_blk_D2_E (ctx : LiftCtx P β ν a Tm ρd Ek j ρ) (hN : L ^ P.m₀ ∣ N₁)
    (i₀ i₁ : Fin N) (y : CTorus d L N₁ m₁ k)
    (W : CTorus d L N₁ m₁ k → CTorus d L N₁ m₁ k → ℂ) :
    ∑ Z ∈ (Set.toFinite (polysAt (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k)
        P.m₀ j y)).toFinset,
      ∑ x ∈ Finset.univ.filter (fun x => Aligned (L ^ j) x ∧ x ∈ Z),
        ∑ x' ∈ Finset.univ.filter (fun x => Aligned (L ^ j) x ∧ x ∈ Z),
          D2 (fun Ψ' : Fld d L N₁ m₁ k N => Tm.E j y Z Ψ' (eFld d L N₁ m₁ k N i₀))
            (eFld d L N₁ m₁ k N i₀) (blockDir L j x i₁) (blockDir L j x' i₁) * W x x' =
      ∑ x ∈ Finset.univ.filter (Aligned (L ^ j)),
        ∑ x' ∈ Finset.univ.filter (Aligned (L ^ j)),
          D2 (fun ψ : Fld d L N₁ m₁ k N => Eloc P.m₀ Tm j y ψ (eFld d L N₁ m₁ k N i₀))
            (eFld d L N₁ m₁ k N i₀) (blockDir L j x i₁) (blockDir L j x' i₁) * W x x' := by
  have hfin := Set.toFinite (polysAt (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P.m₀ j y)
  have hEloc : (fun ψ : Fld d L N₁ m₁ k N => Eloc P.m₀ Tm j y ψ (eFld d L N₁ m₁ k N i₀)) =
      fun ψ => ∑ X ∈ hfin.toFinset, Tm.E j y X ψ (eFld d L N₁ m₁ k N i₀) := by
    funext ψ
    unfold Eloc
    exact finsum_mem_eq_finite_toFinset_sum _ hfin
  have hsub : ∀ X ∈ hfin.toFinset,
      ∑ x ∈ Finset.univ.filter (fun x => Aligned (L ^ j) x ∧ x ∈ X),
        ∑ x' ∈ Finset.univ.filter (fun x => Aligned (L ^ j) x ∧ x ∈ X),
          D2 (fun Ψ' : Fld d L N₁ m₁ k N => Tm.E j y X Ψ' (eFld d L N₁ m₁ k N i₀))
            (eFld d L N₁ m₁ k N i₀) (blockDir L j x i₁) (blockDir L j x' i₁) * W x x' =
      ∑ x ∈ Finset.univ.filter (Aligned (L ^ j)),
        ∑ x' ∈ Finset.univ.filter (Aligned (L ^ j)),
          D2 (fun Ψ' : Fld d L N₁ m₁ k N => Tm.E j y X Ψ' (eFld d L N₁ m₁ k N i₀))
            (eFld d L N₁ m₁ k N i₀) (blockDir L j x i₁) (blockDir L j x' i₁) * W x x' := by
    intro X hX
    have hX' := hfin.mem_toFinset.1 hX
    have hsubset : Finset.univ.filter (fun x => Aligned (L ^ j) x ∧ x ∈ X) ⊆
        Finset.univ.filter (Aligned (L ^ j)) := fun x hx =>
      Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 hx).2.1⟩
    have hout : ∀ x ∈ Finset.univ.filter (Aligned (L ^ j)),
        x ∉ Finset.univ.filter (fun x => Aligned (L ^ j) x ∧ x ∈ X) → x ∉ X := by
      intro x hx hxn hxX
      exact hxn (Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 hx).2, hxX⟩)
    rw [Finset.sum_subset hsubset (fun x hx hxn => by
      refine Finset.sum_eq_zero fun x' _ => ?_
      rw [ctx.D2_E_zero_of_not_mem hN i₀ i₁ y hX'.1 hX'.2 (Or.inl (hout x hx hxn)), zero_mul])]
    refine Finset.sum_congr rfl fun x hx => ?_
    refine Finset.sum_subset hsubset (fun x' hx' hxn' => ?_)
    rw [ctx.D2_E_zero_of_not_mem hN i₀ i₁ y hX'.1 hX'.2 (Or.inr (hout x' hx' hxn')), zero_mul]
  rw [Finset.sum_congr rfl hsub, Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x' _ => ?_
  rw [← Finset.sum_mul, hEloc, D2_sum hfin.toFinset (fun X hX =>
    ctx.analyticAt_E i₀ y ((hfin.mem_toFinset.1 hX).1) ((hfin.mem_toFinset.1 hX).2))]


open Classical in
/-- The sum over the aligned blocks of the first derivatives of the density does not depend on the
aligned centre. -/
theorem LiftCtx.sum_fderiv_Eloc_translate (ctx : LiftCtx P β ν a Tm ρd Ek j ρ) (i₀ : Fin N)
    {y : CTorus d L N₁ m₁ k} (hy : Aligned (L ^ j) y) :
    ∑ x ∈ Finset.univ.filter (Aligned (L ^ j)),
        fderiv ℂ (fun ψ : Fld d L N₁ m₁ k N => Eloc P.m₀ Tm j y ψ (eFld d L N₁ m₁ k N i₀))
          (eFld d L N₁ m₁ k N i₀) (blockDir L j x i₀) =
      ∑ x ∈ Finset.univ.filter (Aligned (L ^ j)),
        fderiv ℂ (fun ψ : Fld d L N₁ m₁ k N => Eloc P.m₀ Tm j 0 ψ (eFld d L N₁ m₁ k N i₀))
          (eFld d L N₁ m₁ k N i₀) (blockDir L j x i₀) := by
  set Λ : Finset (CTorus d L N₁ m₁ k) :=
    (Finset.univ : Finset (CTorus d L N₁ m₁ k)).filter (Aligned (L ^ j)) with hΛ
  have hjk := ctx.jk
  have hdvd : L ^ j ∣ N₁ * L ^ m₁ * L ^ k := by rw [side_eq hjk]; exact dvd_mul_right _ _
  have hmemΛ : ∀ z, z ∈ Λ ↔ Aligned (L ^ j) z := fun z => by simp [hΛ]
  rw [Finset.sum_congr rfl fun x _ => ctx.fderiv_Eloc_translate i₀ hy x]
  refine Finset.sum_nbij' (fun x => x - y) (fun z => z + y) (fun x hx => ?_) (fun z hz => ?_)
    (fun x _ => by simp) (fun z _ => by simp) (fun x _ => rfl)
  · rw [hmemΛ] at hx ⊢
    rw [sub_eq_add_neg]; exact aligned_add hdvd hx (aligned_neg hdvd hy)
  · rw [hmemΛ] at hz ⊢
    exact aligned_add hdvd hz hy

open Classical in
/-- The weighted sum over the pairs of aligned blocks of the second derivatives of the density
does not depend on the aligned centre, the weight being a function of the centred positions
relative to the centre. -/
theorem LiftCtx.sum_D2_Eloc_translate (ctx : LiftCtx P β ν a Tm ρd Ek j ρ) (i₀ i₁ : Fin N)
    {y : CTorus d L N₁ m₁ k} (hy : Aligned (L ^ j) y) (ω : Site d → Site d → ℂ) :
    ∑ x ∈ Finset.univ.filter (Aligned (L ^ j)),
      ∑ x' ∈ Finset.univ.filter (Aligned (L ^ j)),
        D2 (fun ψ : Fld d L N₁ m₁ k N => Eloc P.m₀ Tm j y ψ (eFld d L N₁ m₁ k N i₀))
          (eFld d L N₁ m₁ k N i₀) (blockDir L j x i₁) (blockDir L j x' i₁) *
          ω (unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x - y))
            (unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x' - y)) =
      ∑ x ∈ Finset.univ.filter (Aligned (L ^ j)),
        ∑ x' ∈ Finset.univ.filter (Aligned (L ^ j)),
          D2 (fun ψ : Fld d L N₁ m₁ k N => Eloc P.m₀ Tm j 0 ψ (eFld d L N₁ m₁ k N i₀))
            (eFld d L N₁ m₁ k N i₀) (blockDir L j x i₁) (blockDir L j x' i₁) *
            ω (unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x - 0))
              (unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x' - 0)) := by
  set Λ : Finset (CTorus d L N₁ m₁ k) :=
    (Finset.univ : Finset (CTorus d L N₁ m₁ k)).filter (Aligned (L ^ j)) with hΛ
  have hjk := ctx.jk
  have hdvd : L ^ j ∣ N₁ * L ^ m₁ * L ^ k := by rw [side_eq hjk]; exact dvd_mul_right _ _
  have hmemΛ : ∀ z, z ∈ Λ ↔ Aligned (L ^ j) z := fun z => by simp [hΛ]
  simp only [ctx.D2_Eloc_translate' i₀ i₁ hy]
  rw [← Finset.sum_product', ← Finset.sum_product']
  refine Finset.sum_nbij' (fun p => (p.1 - y, p.2 - y)) (fun p => (p.1 + y, p.2 + y)) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    rw [Finset.mem_product] at hp ⊢
    have h1 := (hmemΛ _).1 hp.1
    have h2 := (hmemΛ _).1 hp.2
    refine ⟨(hmemΛ _).2 ?_, (hmemΛ _).2 ?_⟩
    · show Aligned (L ^ j) (p.1 - y)
      rw [sub_eq_add_neg]; exact aligned_add hdvd h1 (aligned_neg hdvd hy)
    · show Aligned (L ^ j) (p.2 - y)
      rw [sub_eq_add_neg]; exact aligned_add hdvd h2 (aligned_neg hdvd hy)
  · intro p hp
    rw [Finset.mem_product] at hp ⊢
    have h1 := (hmemΛ _).1 hp.1
    have h2 := (hmemΛ _).1 hp.2
    exact ⟨(hmemΛ _).2 (aligned_add hdvd h1 hy), (hmemΛ _).2 (aligned_add hdvd h2 hy)⟩
  · intro p hp
    ext <;> simp
  · intro p hp
    ext <;> simp
  · intro p hp
    simp


open Classical in
/-- **The filed sum is the density expression**: the sum over the polymers through the centre of
the filed term is the same affine expression in `u`, `w`, `g` of the jets of the density. -/
theorem LiftCtx.sum_filed_eq_density (ctx : LiftCtx P β ν a Tm ρd Ek j ρ) (hN : L ^ P.m₀ ∣ N₁)
    (i₀ i₁ : Fin N) (y : CTorus d L N₁ m₁ k) (u w : ℂ) (g : Fin d → Fin d → ℂ)
    (ω : Fin d → Fin d → Site d → Site d → ℂ) :
    ∑ᶠ Z ∈ polysAt P.m₀ j y,
      (Tm.E j y Z (eFld d L N₁ m₁ k N i₀) (eFld d L N₁ m₁ k N i₀) +
        (u - 1) * ∑ x ∈ Finset.univ.filter (fun x => Aligned (L ^ j) x ∧ x ∈ Z),
          fderiv ℂ (fun Ψ' : Fld d L N₁ m₁ k N => Tm.E j y Z Ψ' (eFld d L N₁ m₁ k N i₀))
            (eFld d L N₁ m₁ k N i₀) (blockDir L j x i₀) +
        (w - 1) * fderiv ℂ (fun h' : Fld d L N₁ m₁ k N => Tm.E j y Z (eFld d L N₁ m₁ k N i₀) h')
          (eFld d L N₁ m₁ k N i₀) (eFld d L N₁ m₁ k N i₀) -
        (1 / 4 : ℂ) * ∑ μ, ∑ μ', g μ μ' *
          ∑ x ∈ Finset.univ.filter (fun x => Aligned (L ^ j) x ∧ x ∈ Z),
            ∑ x' ∈ Finset.univ.filter (fun x => Aligned (L ^ j) x ∧ x ∈ Z),
              D2 (fun Ψ' : Fld d L N₁ m₁ k N => Tm.E j y Z Ψ' (eFld d L N₁ m₁ k N i₀))
                (eFld d L N₁ m₁ k N i₀) (blockDir L j x i₁) (blockDir L j x' i₁) *
                ω μ μ' (unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x - y))
                  (unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x' - y))) =
    (Eloc P.m₀ Tm j y (eFld d L N₁ m₁ k N i₀) (eFld d L N₁ m₁ k N i₀) +
      (u - 1) * ∑ x ∈ Finset.univ.filter (Aligned (L ^ j)),
        fderiv ℂ (fun ψ : Fld d L N₁ m₁ k N => Eloc P.m₀ Tm j y ψ (eFld d L N₁ m₁ k N i₀))
          (eFld d L N₁ m₁ k N i₀) (blockDir L j x i₀) +
      (w - 1) * fderiv ℂ (fun h' : Fld d L N₁ m₁ k N =>
        Eloc P.m₀ Tm j y (eFld d L N₁ m₁ k N i₀) h') (eFld d L N₁ m₁ k N i₀)
        (eFld d L N₁ m₁ k N i₀) -
      (1 / 4 : ℂ) * ∑ μ, ∑ μ', g μ μ' *
        ∑ x ∈ Finset.univ.filter (Aligned (L ^ j)),
          ∑ x' ∈ Finset.univ.filter (Aligned (L ^ j)),
            D2 (fun ψ : Fld d L N₁ m₁ k N => Eloc P.m₀ Tm j y ψ (eFld d L N₁ m₁ k N i₀))
              (eFld d L N₁ m₁ k N i₀) (blockDir L j x i₁) (blockDir L j x' i₁) *
              ω μ μ' (unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x - y))
                (unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x' - y))) := by
  have hfin := Set.toFinite (polysAt (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P.m₀ j y)
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
  set F := hfin.toFinset with hF
  have h0 : ∑ Z ∈ F, Tm.E j y Z (eFld d L N₁ m₁ k N i₀) (eFld d L N₁ m₁ k N i₀) =
      Eloc P.m₀ Tm j y (eFld d L N₁ m₁ k N i₀) (eFld d L N₁ m₁ k N i₀) := by
    unfold Eloc
    exact (finsum_mem_eq_finite_toFinset_sum _ hfin).symm
  have hA := ctx.sum_blk_fderiv_E hN i₀ y
  have hH := ctx.sum_fderiv_E_h i₀ y
  have hS := fun μ μ' : Fin d => ctx.sum_blk_D2_E hN i₀ i₁ y
    (fun x x' => ω μ μ' (unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x - y))
      (unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x' - y)))
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [h0, hA, hH]
  congr 1
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun μ' _ => ?_
  rw [← Finset.mul_sum, hS μ μ']


open Classical in
/-- **The filed sum at an aligned centre is the filed sum at the origin**, with the same
coefficients `u`, `w`, `g` and the weights taken at the centred positions relative to the centre:
the four jets of the density (the value, the sum of the first derivatives over the aligned blocks,
the derivative in `h` and the weighted sum of the second derivatives) do not depend on the
aligned centre, by the covariance of the density under the translations of the level-`j`
lattice. -/
theorem LiftCtx.sum_filed_translate (ctx : LiftCtx P β ν a Tm ρd Ek j ρ) (hN : L ^ P.m₀ ∣ N₁)
    (i₀ i₁ : Fin N) {y : CTorus d L N₁ m₁ k} (hy : Aligned (L ^ j) y) (u w : ℂ)
    (g : Fin d → Fin d → ℂ) (ω : Fin d → Fin d → Site d → Site d → ℂ) :
    ∑ᶠ Z ∈ polysAt P.m₀ j y,
      (Tm.E j y Z (eFld d L N₁ m₁ k N i₀) (eFld d L N₁ m₁ k N i₀) +
        (u - 1) * ∑ x ∈ Finset.univ.filter (fun x => Aligned (L ^ j) x ∧ x ∈ Z),
          fderiv ℂ (fun Ψ' : Fld d L N₁ m₁ k N => Tm.E j y Z Ψ' (eFld d L N₁ m₁ k N i₀))
            (eFld d L N₁ m₁ k N i₀) (blockDir L j x i₀) +
        (w - 1) * fderiv ℂ (fun h' : Fld d L N₁ m₁ k N => Tm.E j y Z (eFld d L N₁ m₁ k N i₀) h')
          (eFld d L N₁ m₁ k N i₀) (eFld d L N₁ m₁ k N i₀) -
        (1 / 4 : ℂ) * ∑ μ, ∑ μ', g μ μ' *
          ∑ x ∈ Finset.univ.filter (fun x => Aligned (L ^ j) x ∧ x ∈ Z),
            ∑ x' ∈ Finset.univ.filter (fun x => Aligned (L ^ j) x ∧ x ∈ Z),
              D2 (fun Ψ' : Fld d L N₁ m₁ k N => Tm.E j y Z Ψ' (eFld d L N₁ m₁ k N i₀))
                (eFld d L N₁ m₁ k N i₀) (blockDir L j x i₁) (blockDir L j x' i₁) *
                ω μ μ' (unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x - y))
                  (unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x' - y))) =
    ∑ᶠ Z ∈ polysAt P.m₀ j (0 : CTorus d L N₁ m₁ k),
      (Tm.E j 0 Z (eFld d L N₁ m₁ k N i₀) (eFld d L N₁ m₁ k N i₀) +
        (u - 1) * ∑ x ∈ Finset.univ.filter (fun x => Aligned (L ^ j) x ∧ x ∈ Z),
          fderiv ℂ (fun Ψ' : Fld d L N₁ m₁ k N => Tm.E j 0 Z Ψ' (eFld d L N₁ m₁ k N i₀))
            (eFld d L N₁ m₁ k N i₀) (blockDir L j x i₀) +
        (w - 1) * fderiv ℂ (fun h' : Fld d L N₁ m₁ k N => Tm.E j 0 Z (eFld d L N₁ m₁ k N i₀) h')
          (eFld d L N₁ m₁ k N i₀) (eFld d L N₁ m₁ k N i₀) -
        (1 / 4 : ℂ) * ∑ μ, ∑ μ', g μ μ' *
          ∑ x ∈ Finset.univ.filter (fun x => Aligned (L ^ j) x ∧ x ∈ Z),
            ∑ x' ∈ Finset.univ.filter (fun x => Aligned (L ^ j) x ∧ x ∈ Z),
              D2 (fun Ψ' : Fld d L N₁ m₁ k N => Tm.E j 0 Z Ψ' (eFld d L N₁ m₁ k N i₀))
                (eFld d L N₁ m₁ k N i₀) (blockDir L j x i₁) (blockDir L j x' i₁) *
                ω μ μ' (unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x - 0))
                  (unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x' - 0))) := by
  rw [ctx.sum_filed_eq_density hN i₀ i₁ y u w g ω, ctx.sum_filed_eq_density hN i₀ i₁ 0 u w g ω,
    ctx.Eloc_const_translate i₀ hy, ctx.sum_fderiv_Eloc_translate i₀ hy,
    ctx.fderiv_Eloc_h_translate i₀ hy]
  congr 2
  refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun μ' _ => ?_
  rw [ctx.sum_D2_Eloc_translate i₀ i₁ hy (ω μ μ')]

end Torus

end Balaban.SmallField.Def6
