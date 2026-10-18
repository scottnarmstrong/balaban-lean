/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.IrrelTorusDefectMatrix
public import Balaban.SmallField.IrrelTorusSum

/-!
# Translation covariance of the jets of the density

The value, the first derivative along a block direction and the derivative in `h` of the density
`Eloc` at the constant fields are translated from an aligned centre to the origin by the
covariance `eucEloc` (`LiftCtx.Eloc_const_translate`, `LiftCtx.fderiv_Eloc_translate`,
`LiftCtx.fderiv_Eloc_h_translate`). A term has no derivative in the direction of a block outside
its polymer.
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

/-- The term of a polymer is jointly analytic at the reference fields. -/
theorem LiftCtx.analyticAt_E_pair (ctx : LiftCtx P β ν a Tm ρd Ek j ρ) (i₀ : Fin N)
    (y : CTorus d L N₁ m₁ k) {X : Set (CTorus d L N₁ m₁ k)} (hX : IsPolyDom P.m₀ j X)
    (hy : y ∈ X) :
    AnalyticAt ℂ (fun p : Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N => Tm.E j y X p.1 p.2)
      (eFld d L N₁ m₁ k N i₀, eFld d L N₁ m₁ k N i₀) := by
  have hp0 : XiDom (Tm.gs j X) (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) j (P.eps d L j)
      (eFld d L N₁ m₁ k N i₀) (eFld d L N₁ m₁ k N i₀) :=
    ctx.xiDom_const (Tm.gs j X) (ctx.sf.gs_spec j ctx.j1 ctx.jk X hX).2 i₀ _
      (fun x i => by simp [eFld, constFld, ctx.rho_pos.le]) (fun _ _ _ => rfl)
  exact ctx.sf.analyticE j ctx.j1 ctx.jk y X hX hy (eFld d L N₁ m₁ k N i₀, eFld d L N₁ m₁ k N i₀)
    hp0

/-- The density at the constant fields is the same at every aligned centre. -/
theorem LiftCtx.Eloc_const_translate (ctx : LiftCtx P β ν a Tm ρd Ek j ρ) (i₀ : Fin N)
    {y : CTorus d L N₁ m₁ k} (hy : Aligned (L ^ j) y) :
    Eloc P.m₀ Tm j y (eFld d L N₁ m₁ k N i₀) (eFld d L N₁ m₁ k N i₀) =
      Eloc P.m₀ Tm j 0 (eFld d L N₁ m₁ k N i₀) (eFld d L N₁ m₁ k N i₀) := by
  have hjk := ctx.jk
  have hr := mem_fullJSymGroup_addRight_neg (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) hy
  have hlev : ∀ i, j < i →
      (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (ϱ := ϱ) j hjk).Ω i = ∅ := by
    intro i hi
    simp [levelGS, not_le.2 hi]
  have X1 := ctx.xiDom_const (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (ϱ := ϱ) j hjk) hlev
    i₀ (eFld d L N₁ m₁ k N i₀) (fun x i => by simp [eFld, constFld, ctx.rho_pos.le])
    (fun _ _ _ => rfl)
  have key := ctx.sf.eucEloc j ctx.j1 hjk y (Equiv.addRight (-y)) hr (eFld d L N₁ m₁ k N i₀)
    (eFld d L N₁ m₁ k N i₀) X1 X1
  have hry : (Equiv.addRight (-y) : Equiv.Perm (CTorus d L N₁ m₁ k)) y = 0 := by
    simp
  have h1 : actField (N := N) (Equiv.addRight (-y)) (eFld d L N₁ m₁ k N i₀) =
      eFld d L N₁ m₁ k N i₀ := rfl
  rw [h1, hry, blockBase_zero] at key
  exact key.symm


/-- Translation covariance of the first derivative of the density along a block direction. -/
theorem LiftCtx.fderiv_Eloc_translate (ctx : LiftCtx P β ν a Tm ρd Ek j ρ) (i₀ : Fin N)
    {y : CTorus d L N₁ m₁ k} (hy : Aligned (L ^ j) y) (x : CTorus d L N₁ m₁ k) :
    fderiv ℂ (fun ψ : Fld d L N₁ m₁ k N => Eloc P.m₀ Tm j y ψ (eFld d L N₁ m₁ k N i₀))
        (eFld d L N₁ m₁ k N i₀) (blockDir L j x i₀) =
      fderiv ℂ (fun ψ : Fld d L N₁ m₁ k N => Eloc P.m₀ Tm j 0 ψ (eFld d L N₁ m₁ k N i₀))
        (eFld d L N₁ m₁ k N i₀) (blockDir L j (x - y) i₀) := by
  have hjk := ctx.jk
  have hr := mem_fullJSymGroup_addRight_neg (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) hy
  have hlev : ∀ i, j < i →
      (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (ϱ := ϱ) j hjk).Ω i = ∅ := by
    intro i hi
    simp [levelGS, not_le.2 hi]
  refine Def6v2.fderiv_eq_of_eventually_line (ctx.analyticAt_Eloc i₀ y).differentiableAt
    (ctx.analyticAt_Eloc i₀ 0).differentiableAt ?_
  filter_upwards [Metric.closedBall_mem_nhds (0 : ℂ) ctx.rho_pos] with t ht
  have ht' : ‖t‖ ≤ ρ := by simpa using ht
  have hline : ∀ x' : CTorus d L N₁ m₁ k,
      XiDom (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (ϱ := ϱ) j hjk)
        (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) j (P.eps d L j)
        (eFld d L N₁ m₁ k N i₀ + t • blockDir L j x' i₀) (eFld d L N₁ m₁ k N i₀) := by
    intro x'
    refine ctx.xiDom_const _ hlev i₀ _ (fun z i => ?_) (fun z z' hzz => ?_)
    · have h1 := norm_blockDir_le (N := N) L j x' i₀ z i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, eFld, constFld, add_sub_cancel_left,
        norm_mul]
      nlinarith [norm_nonneg t, norm_nonneg (blockDir (N := N) L j x' i₀ z i)]
    · simp only [Pi.add_apply, Pi.smul_apply, eFld, constFld, blockDir_jBlock hjk x' i₀ hzz]
  have e1 := actField_addRight_neg_blockDir (N := N) hjk hy x i₀
  have hact : actField (N := N) (Equiv.addRight (-y))
      (eFld d L N₁ m₁ k N i₀ + t • blockDir L j x i₀) =
      eFld d L N₁ m₁ k N i₀ + t • blockDir L j (x - y) i₀ := by
    rw [← e1]; funext z; rfl
  have hacte : actField (N := N) (Equiv.addRight (-y)) (eFld d L N₁ m₁ k N i₀) =
      eFld d L N₁ m₁ k N i₀ := rfl
  have key := ctx.sf.eucEloc j ctx.j1 hjk y (Equiv.addRight (-y)) hr
    (eFld d L N₁ m₁ k N i₀ + t • blockDir L j x i₀) (eFld d L N₁ m₁ k N i₀) (hline x)
    (by rw [hact, hacte]; exact hline (x - y))
  rw [hact, hacte] at key
  have hry : blockBase L j ((Equiv.addRight (-y) : Equiv.Perm (CTorus d L N₁ m₁ k)) y) = 0 := by
    simp only [Equiv.coe_addRight, add_neg_cancel]
    exact blockBase_zero L j
  rw [hry] at key
  exact key.symm


open Classical in
/-- The density at the reference field is analytic in the field `h` at the reference field. -/
theorem LiftCtx.analyticAt_Eloc_h (ctx : LiftCtx P β ν a Tm ρd Ek j ρ) (i₀ : Fin N)
    (y : CTorus d L N₁ m₁ k) :
    AnalyticAt ℂ (fun h' : Fld d L N₁ m₁ k N => Eloc P.m₀ Tm j y (eFld d L N₁ m₁ k N i₀) h')
      (eFld d L N₁ m₁ k N i₀) := by
  have hfin : (polysAt (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P.m₀ j y).Finite :=
    Set.toFinite _
  have : (fun h' : Fld d L N₁ m₁ k N => Eloc P.m₀ Tm j y (eFld d L N₁ m₁ k N i₀) h') =
      fun h' => ∑ X ∈ hfin.toFinset, Tm.E j y X (eFld d L N₁ m₁ k N i₀) h' := by
    funext h'
    unfold Eloc
    exact finsum_mem_eq_finite_toFinset_sum _ hfin
  rw [this]
  refine Finset.analyticAt_fun_sum _ fun X hX => ?_
  have hXm := (Set.Finite.mem_toFinset hfin).1 hX
  exact AnalyticAt.comp (f := fun h' : Fld d L N₁ m₁ k N => (eFld d L N₁ m₁ k N i₀, h'))
    (ctx.analyticAt_E_pair i₀ y hXm.1 hXm.2) (analyticAt_const.prod analyticAt_id)

/-- Translation covariance of the derivative of the density in the field `h`. -/
theorem LiftCtx.fderiv_Eloc_h_translate (ctx : LiftCtx P β ν a Tm ρd Ek j ρ) (i₀ : Fin N)
    {y : CTorus d L N₁ m₁ k} (hy : Aligned (L ^ j) y) :
    fderiv ℂ (fun h' : Fld d L N₁ m₁ k N => Eloc P.m₀ Tm j y (eFld d L N₁ m₁ k N i₀) h')
        (eFld d L N₁ m₁ k N i₀) (eFld d L N₁ m₁ k N i₀) =
      fderiv ℂ (fun h' : Fld d L N₁ m₁ k N => Eloc P.m₀ Tm j 0 (eFld d L N₁ m₁ k N i₀) h')
        (eFld d L N₁ m₁ k N i₀) (eFld d L N₁ m₁ k N i₀) := by
  have hjk := ctx.jk
  have hr := mem_fullJSymGroup_addRight_neg (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) hy
  have hlev : ∀ i, j < i →
      (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (ϱ := ϱ) j hjk).Ω i = ∅ := by
    intro i hi
    simp [levelGS, not_le.2 hi]
  have hνj : 0 < nuIdeal L k (ν k) j := nuIdeal_pos' (L := L) ctx.nu_pos j
  refine Def6v2.fderiv_eq_of_eventually_line (ctx.analyticAt_Eloc_h i₀ y).differentiableAt
    (ctx.analyticAt_Eloc_h i₀ 0).differentiableAt ?_
  filter_upwards [Metric.closedBall_mem_nhds (0 : ℂ) (div_pos ctx.rho_pos hνj)] with t ht
  have ht' : ‖t‖ ≤ ρ / nuIdeal L k (ν k) j := by simpa using ht
  have hline : XiDom (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (ϱ := ϱ) j hjk)
      (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) j (P.eps d L j)
      (eFld d L N₁ m₁ k N i₀) (eFld d L N₁ m₁ k N i₀ + t • eFld d L N₁ m₁ k N i₀) := by
    have h := ctx.xiDom_constw (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (ϱ := ϱ) j hjk)
      hlev i₀ (Pi.single i₀ 1) ((1 + t) • (Pi.single i₀ 1 : Fin N → ℂ))
      (fun i => by simp [ctx.rho_pos.le])
      (fun i => by
        have e : ((1 + t) • (Pi.single i₀ 1 : Fin N → ℂ)) i - (Pi.single i₀ 1 : Fin N → ℂ) i =
            t * (Pi.single i₀ 1 : Fin N → ℂ) i := by
          simp only [Pi.smul_apply, smul_eq_mul]; ring
        rw [e, norm_mul]
        have h1 : ‖(Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ 1 := by
          by_cases hi : i = i₀
          · subst hi; simp
          · simp [hi]
        calc nuIdeal L k (ν k) j * (‖t‖ * ‖(Pi.single i₀ 1 : Fin N → ℂ) i‖)
            ≤ nuIdeal L k (ν k) j * (‖t‖ * 1) := by gcongr
          _ = nuIdeal L k (ν k) j * ‖t‖ := by ring
          _ ≤ ρ := by
            have := mul_le_mul_of_nonneg_left ht' hνj.le
            rwa [mul_div_cancel₀ _ hνj.ne'] at this)
    have e : eFld d L N₁ m₁ k N i₀ + t • eFld d L N₁ m₁ k N i₀ =
        constFld ((1 + t) • (Pi.single i₀ 1 : Fin N → ℂ)) := by
      funext z i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, eFld, constFld]
      ring
    rw [e]
    exact h
  have hacte : actField (N := N) (Equiv.addRight (-y)) (eFld d L N₁ m₁ k N i₀) =
      eFld d L N₁ m₁ k N i₀ := rfl
  have hacth : actField (N := N) (Equiv.addRight (-y))
      (eFld d L N₁ m₁ k N i₀ + t • eFld d L N₁ m₁ k N i₀) =
      eFld d L N₁ m₁ k N i₀ + t • eFld d L N₁ m₁ k N i₀ := rfl
  have key := ctx.sf.eucEloc j ctx.j1 hjk y (Equiv.addRight (-y)) hr (eFld d L N₁ m₁ k N i₀)
    (eFld d L N₁ m₁ k N i₀ + t • eFld d L N₁ m₁ k N i₀) hline
    (by rw [hacte, hacth]; exact hline)
  rw [hacte, hacth] at key
  have hry : blockBase L j ((Equiv.addRight (-y) : Equiv.Perm (CTorus d L N₁ m₁ k)) y) = 0 := by
    simp only [Equiv.coe_addRight, add_neg_cancel]
    exact blockBase_zero L j
  rw [hry] at key
  exact key.symm


open Classical in
/-- A term has no dependence on the block of a site outside its polymer: the derivative of the
term in that block direction vanishes at every field. -/
theorem LiftCtx.fderiv_E_zero_of_not_mem (ctx : LiftCtx P β ν a Tm ρd Ek j ρ)
    (hN : L ^ P.m₀ ∣ N₁) (i₀ : Fin N) (y : CTorus d L N₁ m₁ k)
    {X : Set (CTorus d L N₁ m₁ k)} (hX : IsPolyDom P.m₀ j X) {x : CTorus d L N₁ m₁ k}
    (hx : x ∉ X) (Ψ h : Fld d L N₁ m₁ k N) :
    fderiv ℂ (fun Ψ' : Fld d L N₁ m₁ k N => Tm.E j y X Ψ' h) Ψ (blockDir L j x i₀) = 0 := by
  by_cases hd : DifferentiableAt ℂ (fun Ψ' : Fld d L N₁ m₁ k N => Tm.E j y X Ψ' h) Ψ
  · rw [Def6v2.fderiv_apply_eq_deriv_line hd]
    have hc : (fun t : ℂ => Tm.E j y X (Ψ + t • blockDir L j x i₀) h) =
        fun _ => Tm.E j y X Ψ h := by
      funext t
      refine ctx.sf.localE j y X _ _ _ _ fun z hz => ⟨?_, rfl⟩
      have hzx : ¬ cbase (L ^ j) z = x := by
        intro hzx
        apply hx
        rw [← hzx]
        exact hX.block_closed ctx.jk hN hz (jBlock_cbase z).symm
      have hb : blockDir (N := N) L j x i₀ z = 0 := by
        funext i'
        simp [blockDir, hzx]
      simp [hb]
    rw [hc, deriv_const]
  · have : fderiv ℂ (fun Ψ' : Fld d L N₁ m₁ k N => Tm.E j y X Ψ' h) Ψ = 0 :=
      fderiv_zero_of_not_differentiableAt hd
    rw [this]; rfl

open Classical in
/-- The second derivative of a term vanishes in the direction of a block outside its polymer
(second slot). -/
theorem LiftCtx.D2_E_zero_of_not_mem (ctx : LiftCtx P β ν a Tm ρd Ek j ρ)
    (hN : L ^ P.m₀ ∣ N₁) (i₀ i₁ : Fin N) (y : CTorus d L N₁ m₁ k)
    {X : Set (CTorus d L N₁ m₁ k)} (hX : IsPolyDom P.m₀ j X) (hyX : y ∈ X)
    {x x' : CTorus d L N₁ m₁ k} (hx : x ∉ X ∨ x' ∉ X) :
    D2 (fun Ψ' : Fld d L N₁ m₁ k N => Tm.E j y X Ψ' (eFld d L N₁ m₁ k N i₀))
      (eFld d L N₁ m₁ k N i₀) (blockDir L j x i₁) (blockDir L j x' i₁) = 0 := by
  have han := ctx.analyticAt_E i₀ y hX hyX
  have key : ∀ {u v : CTorus d L N₁ m₁ k}, v ∉ X →
      D2 (fun Ψ' : Fld d L N₁ m₁ k N => Tm.E j y X Ψ' (eFld d L N₁ m₁ k N i₀))
        (eFld d L N₁ m₁ k N i₀) (blockDir L j u i₁) (blockDir L j v i₁) = 0 := by
    intro u v hv
    have h1 := hasDerivAt_fderiv_line han (blockDir (N := N) L j u i₁) (blockDir L j v i₁)
    have h2 : (fun s : ℂ => fderiv ℂ (fun Ψ' : Fld d L N₁ m₁ k N =>
        Tm.E j y X Ψ' (eFld d L N₁ m₁ k N i₀)) (eFld d L N₁ m₁ k N i₀ + s • blockDir L j u i₁)
          (blockDir L j v i₁)) = fun _ => 0 := by
      funext s
      exact ctx.fderiv_E_zero_of_not_mem hN i₁ y hX hv _ _
    rw [h2] at h1
    exact h1.unique (hasDerivAt_const 0 0)
  rcases hx with hx | hx
  · rw [D2_symm han]
    exact key hx
  · exact key hx



end Torus

end Balaban.SmallField.Def6
