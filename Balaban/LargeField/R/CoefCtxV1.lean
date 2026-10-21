/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.CoefCtx

/-!
# The radial coefficient `v₁` from the coefficient context

The statements of `RadialCoefficient`, `RadialCoefficientLimit` and `RadialCoefficientAvg` about
the local coefficient `v1Loc`, for a `CoefCtx` instead of a `LiftCtx`:

* `CoefCtx.norm_tensA_EauxC_le`: the Cauchy bound of one coefficient on a torus;
* `CoefCtx.v1Loc_eq_zero_of_not_mem`: locality of the coefficient;
* `CoefCtx.tensA_EauxC_eq_v1Loc`: the tensor `tensA` of the centred term is `v1Loc`;
* `CoefCtx.v1Loc_axis_eq`: the coefficient does not depend on the axis.
-/

@[expose] public section

namespace Balaban.LargeField.Def7v2

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.SmallField.Def6v2 Filter Matrix Metric

section V1

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  {P : Consts} {νk : ℝ} {Dom : FieldDom d L N₁ m₁ k N ϱ} {Tm : Terms d L N₁ m₁ k N ϱ}
  {j : ℕ} {ρ : ℝ}

/-- **Cauchy bound of one coefficient on a torus**: for a shape `X' ∋ y` that does not wind and
whose lift is a polymer of `𝒟_j`, `‖∂_{ψ_{i₀}(x)} ℰ(y, Y)‖ ≤ E₀ e^{-κ d_j(Y)} / ρ`. -/
theorem CoefCtx.norm_tensA_EauxC_le (ctx : CoefCtx P νk Dom Tm j ρ) (i₀ : Fin N)
    {y : SmallField.Site d} {X' : Finset (SmallField.Site d)} (hnw : NonWind L N₁ m₁ k j X')
    (hpd : IsPolyDom P.m₀ j (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X')) (hy : y ∈ X')
    (x : ↥X') :
    ‖tensA i₀ (nuIdeal L k νk j) X' (EauxC Tm j i₀ (nuIdeal L k νk j) y X') x‖ ≤
      P.E₀ * Real.exp (-P.κ * sizeJ (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P.m₀ j
        (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X')) / ρ := by
  have hb : ∀ c ∈ ball (refPt i₀ (nuIdeal L k νk j) X') ρ,
      ‖EauxC Tm j i₀ (nuIdeal L k νk j) y X' c‖ ≤ P.E₀ * Real.exp (-P.κ *
        sizeJ (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P.m₀ j
          (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X')) := fun c hc =>
    ctx.norm_EauxC_le i₀ hpd y hnw hy hc
  have hM0 := (norm_nonneg _).trans (hb _ (mem_ball_self ctx.rho_pos))
  have h := norm_fderiv_apply_le ctx.rho_pos
    (fun c hc => ctx.analyticAt_EauxC i₀ hpd y hnw hy hc) hb
    (Pi.single (Sum.inl (x, i₀)) (1 : ℂ) : Cfg d N X')
  have h2 := norm_single_one_le (Sum.inl (x, i₀) : Idx d N X')
  unfold tensA
  refine h.trans ?_
  exact div_le_div_of_nonneg_right (mul_le_of_le_one_right hM0 h2) ctx.rho_pos.le

/-- **Locality of the radial coefficient**: for a centre `w ∈ Y` and a block corner `u` whose centred
position is not in the shape `X'` of `Y = Ypoly X'`, the local coefficient `v1Loc` vanishes. -/
theorem CoefCtx.v1Loc_eq_zero_of_not_mem (ctx : CoefCtx P νk Dom Tm j ρ) {i₀ : Fin N}
    {X' : Finset (SmallField.Site d)}
    (hpd : IsPolyDom P.m₀ j (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X'))
    {w : Localization.CTorus d L N₁ m₁ k}
    (hw : w ∈ Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X')
    {u : Localization.CTorus d L N₁ m₁ k} (hu : Aligned (L ^ j) u)
    (hux : unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j u ∉ X')
    (Et : Fld d L N₁ m₁ k N → Fld d L N₁ m₁ k N → ℂ)
    (hEt : ∀ (Ψ : Fld d L N₁ m₁ k N) (b : Fin N → ℂ),
      Et Ψ (constFld b) = Tm.E j w (Ypoly j X') Ψ
        (constFld (((nuIdeal L k νk j : ℝ) : ℂ)⁻¹ • b))) :
    v1Loc Et j (nuIdeal L k νk j) (Pi.single i₀ 1) u = 0 := by
  have hjk := ctx.jk
  have hjh := ctx.analyticAt_E i₀ w hpd hw
  have hcu : ∀ z : Localization.CTorus d L N₁ m₁ k,
      (cbase (L ^ j) z = u ↔ unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j z =
        unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j u) :=
    fun z => by rw [cbase_eq_iff_jBlock hjk hu z, unlift_eq_iff]
  have hνj := ctx.nuj_pos
  have hνc : ((nuIdeal L k νk j : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hνj.ne'
  have hEt' : (fun ψ : Fld d L N₁ m₁ k N =>
      Et ψ (constFld (((nuIdeal L k νk j : ℝ) : ℂ) • (Pi.single i₀ 1 : Fin N → ℂ)))) =
      fun ψ => Tm.E j w (Ypoly j X') ψ (eFld d L N₁ m₁ k N i₀) := by
    funext ψ
    rw [hEt, smul_smul, inv_mul_cancel₀ hνc, one_smul]
  unfold v1Loc
  rw [hEt']
  have hloc := fderiv_eq_of_line (f := fun _ : ℂ => Tm.E j w (Ypoly j X')
      (eFld d L N₁ m₁ k N i₀) (eFld d L N₁ m₁ k N i₀)) (p := (0 : ℂ))
    (g := fun ψ : Fld d L N₁ m₁ k N => Tm.E j w (Ypoly j X') ψ
      (eFld d L N₁ m₁ k N i₀)) (q := eFld d L N₁ m₁ k N i₀) (v := (0 : ℂ))
    (w := blockDirV L j u (Pi.single i₀ 1)) (differentiableAt_const _)
    hjh.differentiableAt (fun s => ?_)
  · rw [← hloc]; simp
  · refine ctx.tc.localE j _ _ _ _ _ _ (fun z hz => ⟨?_, rfl⟩)
    have hne' : ¬ cbase (L ^ j) z = u := fun h => hux (by
      have := (hcu z).1 h
      rw [← this]; exact hz)
    simp [blockDirV, hne']

/-- **The tensor `tensA` of the centre-`y` class term is the local coefficient `v1Loc`.**
For a polymer `X'` of the lift, a block corner `u` whose centred position lies in `X'`, and a source
form `Et` of the term in the variable `b = ν_j h` (the shape of `D1Corr.src_pos`), the derivative of
`EauxC` at the reference point `(e_{i₀}, ν_j e_{i₀})` in the coordinate `ψ_{i₀}(unlift u)` is
`v1Loc` at the block `u`. -/
theorem CoefCtx.tensA_EauxC_eq_v1Loc (ctx : CoefCtx P νk Dom Tm j ρ) {i₀ : Fin N}
    {y : SmallField.Site d} {X' : Finset (SmallField.Site d)} (hnw : NonWind L N₁ m₁ k j X')
    (hpd : IsPolyDom P.m₀ j (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X')) (hy : y ∈ X')
    {u : Localization.CTorus d L N₁ m₁ k} (hu : Aligned (L ^ j) u)
    (huX : unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j u ∈ X')
    (Et : Fld d L N₁ m₁ k N → Fld d L N₁ m₁ k N → ℂ)
    (hEt : ∀ (Ψ : Fld d L N₁ m₁ k N) (b : Fin N → ℂ),
      Et Ψ (constFld b) = Tm.E j (blockPt j y) (Ypoly j X') Ψ
        (constFld (((nuIdeal L k νk j : ℝ) : ℂ)⁻¹ • b))) :
    tensA i₀ (nuIdeal L k νk j) X' (EauxC Tm j i₀ (nuIdeal L k νk j) y X')
        ⟨unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j u, huX⟩ =
      v1Loc Et j (nuIdeal L k νk j) (Pi.single i₀ 1) u := by
  have hjk := ctx.jk
  have hνj := ctx.nuj_pos
  have hνc : ((nuIdeal L k νk j : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hνj.ne'
  have h2 : AnalyticAt ℂ (EauxC Tm j i₀ (nuIdeal L k νk j) y X')
      (refPt i₀ (nuIdeal L k νk j) X') :=
    ctx.analyticAt_EauxC i₀ hpd y hnw hy (Metric.mem_ball_self ctx.rho_pos)
  have h1 := ctx.analyticAt_E i₀ (blockPt j y) hpd (blockPt_mem_Ypoly hjk hnw hy)
  have hEt' : (fun ψ : Fld d L N₁ m₁ k N =>
      Et ψ (constFld (((nuIdeal L k νk j : ℝ) : ℂ) • (Pi.single i₀ 1 : Fin N → ℂ)))) =
      fun ψ => Tm.E j (blockPt j y) (Ypoly j X') ψ (eFld d L N₁ m₁ k N i₀) := by
    funext ψ
    rw [hEt, smul_smul, inv_mul_cancel₀ hνc, one_smul]
  unfold tensA v1Loc
  rw [hEt']
  refine fderiv_eq_of_line h2.differentiableAt h1.differentiableAt (fun s => ?_)
  have hcu : ∀ z : Localization.CTorus d L N₁ m₁ k,
      (cbase (L ^ j) z = u ↔ unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j z =
        unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j u) := fun z => by
    rw [cbase_eq_iff_jBlock hjk hu z, unlift_eq_iff]
  set c : Cfg d N X' := refPt i₀ (nuIdeal L k νk j) X' +
    s • (Pi.single (Sum.inl (⟨unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j u, huX⟩, i₀)) 1 :
      Cfg d N X') with hc
  have hf : fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ X' c =
      eFld d L N₁ m₁ k N i₀ + s • blockDirV L j u (Pi.single i₀ 1) := by
    funext z i
    by_cases hz : unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j z ∈ X'
    · simp only [fieldOf, hz, dite_true, hc, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        Pi.single_apply, refPt_inl, blockDirV, eFld, constFld, hcu z,
        Sum.inl.injEq, Prod.mk.injEq, Subtype.mk.injEq]
      by_cases h : unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j z =
          unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j u <;>
        by_cases hi : i = i₀ <;> simp [h, hi]
    · have hu0 : blockDirV L j u (Pi.single i₀ 1 : Fin N → ℂ) z i = 0 := by
        have hne : ¬ cbase (L ^ j) z = u := fun h => hz ((hcu z).1 h ▸ huX)
        simp [blockDirV, hne]
      simp only [fieldOf, hz, dite_false, Pi.add_apply, Pi.smul_apply, smul_eq_mul, eFld,
        constFld, hu0]
      ring
  have hh : hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) (nuIdeal L k νk j) X' c =
      eFld d L N₁ m₁ k N i₀ := by
    funext z i
    simp only [hOf, hc, Pi.add_apply, Pi.smul_apply, eFld, constFld]
    rw [refPt_inr]
    simp only [Pi.single_apply, smul_eq_mul]
    simp only [reduceCtorEq, ite_false, mul_zero, add_zero]
    field_simp
  show Tm.E j (blockPt j y) (Ypoly j X') (fieldOf j i₀ X' c) (hOf (nuIdeal L k νk j) X' c) = _
  rw [hf, hh]

/-- **One polymer: the radial coefficient does not depend on the axis.**  Let `Et` be a source form
of the class term `Tm.E j y X`, and `Q` a real orthogonal matrix with `Q e_{i₀} = w`.  Then
`v1Loc Et j ν_j w u = v1Loc Et j ν_j e_{i₀} u`. -/
theorem CoefCtx.v1Loc_axis_eq (ctx : CoefCtx P νk Dom Tm j ρ) {i₀ : Fin N}
    {Q : Matrix (Fin N) (Fin N) ℝ} (hQ : Qᵀ * Q = 1)
    {y : Localization.CTorus d L N₁ m₁ k} {X : Set (Localization.CTorus d L N₁ m₁ k)}
    (hX : IsPolyDom P.m₀ j X) (hy : y ∈ X)
    (Et : Fld d L N₁ m₁ k N → Fld d L N₁ m₁ k N → ℂ)
    (hEt : ∀ (Ψ : Fld d L N₁ m₁ k N) (b : Fin N → ℂ),
      Et Ψ (constFld b) = Tm.E j y X Ψ (constFld (((nuIdeal L k νk j : ℝ) : ℂ)⁻¹ • b)))
    {w : Fin N → ℂ} (hw : w = cmat Q *ᵥ (Pi.single i₀ 1 : Fin N → ℂ))
    (u : Localization.CTorus d L N₁ m₁ k) :
    v1Loc Et j (nuIdeal L k νk j) w u =
      v1Loc Et j (nuIdeal L k νk j) (Pi.single i₀ 1) u := by
  have hνc : ((nuIdeal L k νk j : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ctx.nuj_pos.ne'
  have hEs : ∀ v : Fin N → ℂ, (fun ψ : Fld d L N₁ m₁ k N =>
      Et ψ (constFld (((nuIdeal L k νk j : ℝ) : ℂ) • v))) =
      fun ψ => Tm.E j y X ψ (constFld v) := by
    intro v; funext ψ
    rw [hEt, smul_smul, inv_mul_cancel₀ hνc, one_smul]
  unfold v1Loc
  rw [hEs, hEs]
  have hre : rotField (cmat Q) (eFld d L N₁ m₁ k N i₀) = constFld w := by
    rw [eFld, rotField_constFld, hw]
  have hdomw : Dom.dom j (Tm.gs j X) (constFld w) (constFld w) := by
    have h0 := ctx.const_dom i₀ hX
    have h1 := ctx.rotDom Q hQ X _ _ h0
    rwa [hre] at h1
  have hg : DifferentiableAt ℂ (fun ψ : Fld d L N₁ m₁ k N => Tm.E j y X ψ (eFld d L N₁ m₁ k N i₀))
      (eFld d L N₁ m₁ k N i₀) := (ctx.analyticAt_E i₀ y hX hy).differentiableAt
  have hf : DifferentiableAt ℂ (fun ψ : Fld d L N₁ m₁ k N => Tm.E j y X ψ (constFld w))
      (constFld w) := by
    have h1 := ctx.tc.analyticE j ctx.j1 ctx.jk y X hX hy (constFld w, constFld w) hdomw
    have h2 : AnalyticAt ℂ (fun ψ : Fld d L N₁ m₁ k N => (ψ, (constFld w : Fld d L N₁ m₁ k N)))
        (constFld w : Fld d L N₁ m₁ k N) :=
      AnalyticAt.prod analyticAt_id analyticAt_const
    exact (AnalyticAt.comp (f := fun ψ : Fld d L N₁ m₁ k N => (ψ, (constFld w : Fld d L N₁ m₁ k N)))
      h1 h2).differentiableAt
  have hdir : blockDirV L j u w = rotField (cmat Q) (blockDirV L j u (Pi.single i₀ 1)) := by
    rw [rotField_blockDirV, hw]
  rw [hdir]
  refine fderiv_eq_of_line_eventually hf hg ?_
  have hev : ∀ᶠ s : ℂ in nhds 0, ‖s‖ ≤ ρ := by
    have : Metric.closedBall (0 : ℂ) ρ ∈ nhds (0 : ℂ) :=
      Metric.closedBall_mem_nhds _ ctx.rho_pos
    filter_upwards [this] with s hs using by simpa using hs
  filter_upwards [hev] with s hs
  have hd1 := ctx.line_dom i₀ hX u hs
  have hd2 := ctx.rotDom Q hQ X _ _ hd1
  have key := ctx.tc.rotE j ctx.j1 ctx.jk y X hX hy (cmat Q) (isRot_cmat hQ) _ _ hd1 hd2
  rw [rotField_add_smul, hre] at key
  exact key

end V1

end Balaban.LargeField.Def7v2
