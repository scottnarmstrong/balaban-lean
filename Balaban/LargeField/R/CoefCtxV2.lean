/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.CoefCtxV1

/-!
# The transverse coefficient `v₂` from the coefficient context

The local coefficient `v2Loc` of P1 p. 146 (3.106) is the derivative in the transverse source
coordinate of the transverse spin derivative of the term at the reference field.  This file shows
that it is a mixed second derivative of an analytic function and gives its three properties
used by the limit:

* `fderiv_fderiv_eq_deriv_deriv`: for a function analytic at `p`, the derivative of
  `c ↦ f'(c) v` at `p` in the direction `w` is the iterated line derivative
  `∂_t ∂_s f(p + t w + s v)`;
* `v2Loc_eq_iter`: `v2Loc` is the iterated line derivative of the source form of the term;
* `CoefCtx.v2Loc_eq_zero_of_not_mem`: locality;
* `CoefCtx.v2Loc_axis_eq`: the coefficient does not depend on the pair of axes (`Q e₀`, `Q e₁`).
-/

@[expose] public section

namespace Balaban.LargeField.Def7v2

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.SmallField.Def6v2 Filter Matrix Metric

section Generic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- **The mixed second derivative as an iterated line derivative.**  For `f` analytic at `p`, the
derivative at `p` in the direction `w` of `c ↦ f'(c) v` is `∂_t ∂_s f(p + t w + s v)` at `0`. -/
theorem fderiv_fderiv_eq_deriv_deriv {f : E → ℂ} {p v w : E} (hf : AnalyticAt ℂ f p) :
    fderiv ℂ (fun c => fderiv ℂ f c v) p w =
      deriv (fun t : ℂ => deriv (fun s : ℂ => f (p + t • w + s • v)) 0) 0 := by
  have hg : DifferentiableAt ℂ (fun c => fderiv ℂ f c v) p :=
    hf.fderiv.differentiableAt.clm_apply (differentiableAt_const _)
  have h1 := hasDerivAt_line hg w
  have hcont : Tendsto (fun t : ℂ => p + t • w) (nhds 0) (nhds p) := by
    have : Continuous (fun t : ℂ => p + t • w) := by fun_prop
    simpa using this.tendsto 0
  have hev : ∀ᶠ t : ℂ in nhds 0, deriv (fun s : ℂ => f (p + t • w + s • v)) 0 =
      fderiv ℂ f (p + t • w) v := by
    filter_upwards [hcont.eventually hf.eventually_analyticAt] with t ht
    exact (hasDerivAt_line ht.differentiableAt v).deriv
  have h2 : HasDerivAt (fun t : ℂ => deriv (fun s : ℂ => f (p + t • w + s • v)) 0)
      (fderiv ℂ (fun c => fderiv ℂ f c v) p w) 0 := by
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards [hev] with t ht using ht
  exact h2.deriv.symm

end Generic

section V2

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  {P : Consts} {νk : ℝ} {Dom : FieldDom d L N₁ m₁ k N ϱ} {Tm : Terms d L N₁ m₁ k N ϱ}
  {j : ℕ} {ρ : ℝ}

/-- **The source form of a term as a function of `(ψ, b)`**: `K(ψ, b) = ℰ(ψ, b / ν_j)` for the
constant source field `b`. -/
noncomputable def srcK (Tm : Terms d L N₁ m₁ k N ϱ) (j : ℕ) (y : Localization.CTorus d L N₁ m₁ k)
    (X : Set (Localization.CTorus d L N₁ m₁ k)) (νj : ℝ) :
    Fld d L N₁ m₁ k N × (Fin N → ℂ) → ℂ :=
  fun p => Tm.E j y X p.1 (constFld ((νj : ℂ)⁻¹ • p.2))

/-- The source form is analytic at the reference pair `(w, ν_j w)` when `(w, w)` lies in the domain
of the term. -/
theorem CoefCtx.analyticAt_srcK (ctx : CoefCtx P νk Dom Tm j ρ)
    {y : Localization.CTorus d L N₁ m₁ k} {X : Set (Localization.CTorus d L N₁ m₁ k)}
    (hX : IsPolyDom P.m₀ j X) (hy : y ∈ X) {w : Fin N → ℂ}
    (hw : Dom.dom j (Tm.gs j X) (constFld w) (constFld w)) :
    AnalyticAt ℂ (srcK Tm j y X (nuIdeal L k νk j))
      (constFld w, ((nuIdeal L k νk j : ℝ) : ℂ) • w) := by
  have hνc : ((nuIdeal L k νk j : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ctx.nuj_pos.ne'
  have h1 := ctx.tc.analyticE j ctx.j1 ctx.jk y X hX hy (constFld w, constFld w) hw
  have hcl : AnalyticAt ℂ (fun p : Fld d L N₁ m₁ k N × (Fin N → ℂ) =>
      ((p.1, constFld (((nuIdeal L k νk j : ℝ) : ℂ)⁻¹ • p.2)) :
        Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N)) (constFld w, ((nuIdeal L k νk j : ℝ) : ℂ) • w) := by
    refine AnalyticAt.prod analyticAt_fst ?_
    refine analyticAt_pi_iff.2 fun x => analyticAt_pi_iff.2 fun i => ?_
    simp only [constFld, Pi.smul_apply, smul_eq_mul]
    exact (analyticAt_const.mul ((ContinuousLinearMap.proj (R := ℂ)
      (φ := fun _ : Fin N => ℂ) i).analyticAt _ |>.comp analyticAt_snd))
  have h2 : (constFld (((nuIdeal L k νk j : ℝ) : ℂ)⁻¹ • (((nuIdeal L k νk j : ℝ) : ℂ) • w)) :
      Fld d L N₁ m₁ k N) = constFld w := by
    funext x i
    simp [constFld, hνc]
  have h1' : AnalyticAt ℂ (fun p : Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N => Tm.E j y X p.1 p.2)
      (constFld w, constFld (((nuIdeal L k νk j : ℝ) : ℂ)⁻¹ • (((nuIdeal L k νk j : ℝ) : ℂ) • w))) := by
    rw [h2]; exact h1
  exact AnalyticAt.comp (g := fun p : Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N => Tm.E j y X p.1 p.2)
    (f := fun p : Fld d L N₁ m₁ k N × (Fin N → ℂ) =>
      ((p.1, constFld (((nuIdeal L k νk j : ℝ) : ℂ)⁻¹ • p.2)) :
        Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N)) (x := (constFld w, ((nuIdeal L k νk j : ℝ) : ℂ) • w))
    h1' hcl

/-- **The iterated line derivative of the source form**: the value `∂_t ∂_s K(p + t w + s v)` at
`0`, `p = (w₀, ν_j w₀)`, `v = (δ_u w₁, 0)`, `w = (0, w₁)`.  It is `v2Loc` (`v2Loc_eq_iter`). -/
noncomputable def iter2 (Tm : Terms d L N₁ m₁ k N ϱ) (j : ℕ)
    (y : Localization.CTorus d L N₁ m₁ k) (X : Set (Localization.CTorus d L N₁ m₁ k)) (νj : ℝ)
    (w0 w1 : Fin N → ℂ) (u : Localization.CTorus d L N₁ m₁ k) : ℂ :=
  deriv (fun t : ℂ => deriv (fun s : ℂ => srcK Tm j y X νj
    ((constFld w0, (νj : ℂ) • w0) + t • ((0 : Fld d L N₁ m₁ k N), w1) +
      s • (blockDirV L j u w1, (0 : Fin N → ℂ)))) 0) 0

/-- **`v2Loc` is the iterated line derivative of the source form.** -/
theorem CoefCtx.v2Loc_eq_iter (ctx : CoefCtx P νk Dom Tm j ρ)
    {y : Localization.CTorus d L N₁ m₁ k} {X : Set (Localization.CTorus d L N₁ m₁ k)}
    (hX : IsPolyDom P.m₀ j X) (hy : y ∈ X) {w0 : Fin N → ℂ}
    (hw : Dom.dom j (Tm.gs j X) (constFld w0) (constFld w0)) (w1 : Fin N → ℂ)
    (Et : Fld d L N₁ m₁ k N → Fld d L N₁ m₁ k N → ℂ)
    (hEt : ∀ (Ψ : Fld d L N₁ m₁ k N) (b : Fin N → ℂ),
      Et Ψ (constFld b) = Tm.E j y X Ψ (constFld (((nuIdeal L k νk j : ℝ) : ℂ)⁻¹ • b)))
    (u : Localization.CTorus d L N₁ m₁ k) :
    v2Loc Et j (nuIdeal L k νk j) w0 w1 u =
      iter2 Tm j y X (nuIdeal L k νk j) w0 w1 u := by
  set νj := nuIdeal L k νk j with hνj
  set K := srcK Tm j y X νj with hKdef
  set p0 : Fld d L N₁ m₁ k N × (Fin N → ℂ) := (constFld w0, (νj : ℂ) • w0) with hp0
  have hK : AnalyticAt ℂ K p0 := ctx.analyticAt_srcK hX hy hw
  set Bu := blockDirV L j u w1 with hBu
  have hEtK : ∀ (ψ : Fld d L N₁ m₁ k N) (b : Fin N → ℂ), Et ψ (constFld b) = K (ψ, b) :=
    fun ψ b => hEt ψ b
  have hgd : DifferentiableAt ℂ (fun c => fderiv ℂ K c (Bu, 0)) p0 :=
    hK.fderiv.differentiableAt.clm_apply (differentiableAt_const _)
  set ι : (Fin N → ℂ) → Fld d L N₁ m₁ k N × (Fin N → ℂ) := fun b => (constFld w0, b) with hι
  have hιc : Continuous ι := by fun_prop
  have hι0 : ι ((νj : ℂ) • w0) = p0 := rfl
  -- the inner derivative is the total derivative, for `b` near `ν w₀`
  have hev : ∀ᶠ b in nhds ((νj : ℂ) • w0),
      fderiv ℂ (fun ψ : Fld d L N₁ m₁ k N => Et ψ (constFld b)) (constFld w0) Bu =
        fderiv ℂ K (ι b) (Bu, 0) := by
    have h1 : ∀ᶠ c in nhds p0, AnalyticAt ℂ K c := hK.eventually_analyticAt
    have h2 : ∀ᶠ b in nhds ((νj : ℂ) • w0), AnalyticAt ℂ K (ι b) :=
      (hιc.tendsto ((νj : ℂ) • w0)).eventually (by rw [hι0]; exact h1)
    filter_upwards [h2] with b hb
    have hdiff : HasFDerivAt (fun ψ : Fld d L N₁ m₁ k N => ((ψ, b) : Fld d L N₁ m₁ k N × (Fin N → ℂ)))
        ((ContinuousLinearMap.id ℂ _).prod (0 : Fld d L N₁ m₁ k N →L[ℂ] (Fin N → ℂ)))
        (constFld w0) :=
      (hasFDerivAt_id _).prodMk (hasFDerivAt_const b _)
    have hcomp := hb.differentiableAt.hasFDerivAt.comp (constFld w0) hdiff
    have e : (fun ψ : Fld d L N₁ m₁ k N => Et ψ (constFld b)) = fun ψ => K (ψ, b) := by
      funext ψ; exact hEtK ψ b
    rw [e]
    have := hcomp.fderiv
    simp only [Function.comp_def] at this
    rw [this]
    simp
  have hfb : DifferentiableAt ℂ (fun b => fderiv ℂ K (ι b) (Bu, 0)) ((νj : ℂ) • w0) := by
    have hg' : DifferentiableAt ℂ (fun c => fderiv ℂ K c (Bu, 0)) (ι ((νj : ℂ) • w0)) := by
      rw [hι0]; exact hgd
    exact hg'.comp ((νj : ℂ) • w0) ((differentiableAt_const _).prodMk differentiableAt_id)
  unfold v2Loc
  have e1 : (fun b => fderiv ℂ (fun ψ : Fld d L N₁ m₁ k N => Et ψ (constFld b)) (constFld w0) Bu)
      =ᶠ[nhds ((νj : ℂ) • w0)] fun b => fderiv ℂ K (ι b) (Bu, 0) := hev
  rw [e1.fderiv_eq]
  have h3 : fderiv ℂ (fun b => fderiv ℂ K (ι b) (Bu, 0)) ((νj : ℂ) • w0) w1 =
      fderiv ℂ (fun c => fderiv ℂ K c (Bu, 0)) p0 ((0 : Fld d L N₁ m₁ k N), w1) := by
    refine fderiv_eq_of_line hfb hgd (fun s => ?_)
    have : ι ((νj : ℂ) • w0 + s • w1) = p0 + s • ((0 : Fld d L N₁ m₁ k N), w1) := by
      simp [hι, hp0]
    simp only [this]
  rw [h3]
  unfold iter2
  exact fderiv_fderiv_eq_deriv_deriv hK

/-- The source form along the two lines. -/
theorem srcK_line (Tm : Terms d L N₁ m₁ k N ϱ) (j : ℕ) (y : Localization.CTorus d L N₁ m₁ k)
    (X : Set (Localization.CTorus d L N₁ m₁ k)) (νj : ℝ) (w0 w1 : Fin N → ℂ)
    (u : Localization.CTorus d L N₁ m₁ k) (s t : ℂ) :
    srcK Tm j y X νj ((constFld w0, (νj : ℂ) • w0) + t • ((0 : Fld d L N₁ m₁ k N), w1) +
      s • (blockDirV L j u w1, (0 : Fin N → ℂ))) =
      Tm.E j y X (constFld w0 + s • blockDirV L j u w1)
        (constFld ((νj : ℂ)⁻¹ • ((νj : ℂ) • w0 + t • w1))) := by
  simp [srcK]

/-- **Locality of the transverse coefficient**: for a centre `y ∈ Y` and a block corner `u` whose
centred position is not in the shape `X'` of `Y = Ypoly X'`, the local coefficient `v2Loc`
vanishes. -/
theorem CoefCtx.v2Loc_eq_zero_of_not_mem (ctx : CoefCtx P νk Dom Tm j ρ) {w0 w1 : Fin N → ℂ}
    {X' : Finset (SmallField.Site d)} {w : Localization.CTorus d L N₁ m₁ k}
    {u : Localization.CTorus d L N₁ m₁ k} (hu : Aligned (L ^ j) u)
    (hux : unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j u ∉ X')
    (Et : Fld d L N₁ m₁ k N → Fld d L N₁ m₁ k N → ℂ)
    (hEt : ∀ (Ψ : Fld d L N₁ m₁ k N) (b : Fin N → ℂ),
      Et Ψ (constFld b) = Tm.E j w (Ypoly j X') Ψ
        (constFld (((nuIdeal L k νk j : ℝ) : ℂ)⁻¹ • b))) :
    v2Loc Et j (nuIdeal L k νk j) w0 w1 u = 0 := by
  have hjk := ctx.jk
  have hcu : ∀ z : Localization.CTorus d L N₁ m₁ k,
      (cbase (L ^ j) z = u ↔ unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j z =
        unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j u) :=
    fun z => by rw [cbase_eq_iff_jBlock hjk hu z, unlift_eq_iff]
  have hinner : ∀ b : Fin N → ℂ,
      fderiv ℂ (fun ψ : Fld d L N₁ m₁ k N => Et ψ (constFld b)) (constFld w0)
        (blockDirV L j u w1) = 0 := by
    intro b
    by_cases hd : DifferentiableAt ℂ (fun ψ : Fld d L N₁ m₁ k N => Et ψ (constFld b)) (constFld w0)
    · have h1 := hasDerivAt_line hd (blockDirV L j u w1)
      have h2 : (fun s : ℂ => Et (constFld w0 + s • blockDirV L j u w1) (constFld b)) =
          fun _ => Et (constFld w0) (constFld b) := by
        funext s
        rw [hEt, hEt]
        refine ctx.tc.localE j _ _ _ _ _ _ (fun z hz => ⟨?_, rfl⟩)
        have hne' : ¬ cbase (L ^ j) z = u := fun h => hux (by
          have := (hcu z).1 h
          rw [← this]; exact hz)
        simp [blockDirV, hne']
      rw [h2] at h1
      exact h1.unique (hasDerivAt_const _ _)
    · rw [fderiv_zero_of_not_differentiableAt hd]; rfl
  unfold v2Loc
  simp only [hinner]
  simp

/-- **The transverse coefficient does not depend on the pair of axes.**  For a real orthogonal `Q`,
`v2Loc` at the pair `(Q e_{i₀}, Q e_{i₁})` is `v2Loc` at `(e_{i₀}, e_{i₁})`. -/
theorem CoefCtx.v2Loc_axis_eq (ctx : CoefCtx P νk Dom Tm j ρ) {i₀ i₁ : Fin N}
    {Q : Matrix (Fin N) (Fin N) ℝ} (hQ : Qᵀ * Q = 1)
    {y : Localization.CTorus d L N₁ m₁ k} {X : Set (Localization.CTorus d L N₁ m₁ k)}
    (hX : IsPolyDom P.m₀ j X) (hy : y ∈ X)
    (Et : Fld d L N₁ m₁ k N → Fld d L N₁ m₁ k N → ℂ)
    (hEt : ∀ (Ψ : Fld d L N₁ m₁ k N) (b : Fin N → ℂ),
      Et Ψ (constFld b) = Tm.E j y X Ψ (constFld (((nuIdeal L k νk j : ℝ) : ℂ)⁻¹ • b)))
    {w0 w1 : Fin N → ℂ} (hw0 : w0 = cmat Q *ᵥ (Pi.single i₀ 1 : Fin N → ℂ))
    (hw1 : w1 = cmat Q *ᵥ (Pi.single i₁ 1 : Fin N → ℂ))
    (u : Localization.CTorus d L N₁ m₁ k) :
    v2Loc Et j (nuIdeal L k νk j) w0 w1 u =
      v2Loc Et j (nuIdeal L k νk j) (Pi.single i₀ 1) (Pi.single i₁ 1) u := by
  set νj := nuIdeal L k νk j with hνj
  have hνpos : 0 < νj := ctx.nuj_pos
  have hνc : (νj : ℂ) ≠ 0 := by exact_mod_cast hνpos.ne'
  have hre0 : rotField (cmat Q) (eFld d L N₁ m₁ k N i₀) = constFld w0 := by
    rw [eFld, rotField_constFld, hw0]
  have hdom0 : Dom.dom j (Tm.gs j X) (constFld w0) (constFld w0) := by
    have h1 := ctx.rotDom Q hQ X _ _ (ctx.const_dom i₀ hX)
    rwa [hre0] at h1
  rw [ctx.v2Loc_eq_iter hX hy hdom0 w1 Et hEt u,
    ctx.v2Loc_eq_iter hX hy (ctx.const_dom i₀ hX) (Pi.single i₁ 1) Et hEt u]
  unfold iter2
  -- the two functions of `(s, t)` agree for `‖s‖ ≤ ρ`, `‖t‖ < ρ`
  have hagree : ∀ s t : ℂ, ‖s‖ ≤ ρ → ‖t‖ < ρ →
      srcK Tm j y X νj ((constFld w0, (νj : ℂ) • w0) + t • ((0 : Fld d L N₁ m₁ k N), w1) +
        s • (blockDirV L j u w1, (0 : Fin N → ℂ))) =
      srcK Tm j y X νj ((constFld (Pi.single i₀ 1 : Fin N → ℂ),
        (νj : ℂ) • (Pi.single i₀ 1 : Fin N → ℂ)) +
        t • ((0 : Fld d L N₁ m₁ k N), (Pi.single i₁ 1 : Fin N → ℂ)) +
        s • (blockDirV L j u (Pi.single i₁ 1), (0 : Fin N → ℂ))) := by
    intro s t hs ht
    rw [srcK_line, srcK_line]
    set Ψ : Fld d L N₁ m₁ k N := constFld (Pi.single i₀ 1 : Fin N → ℂ) +
      s • blockDirV L j u (Pi.single i₁ 1) with hΨ
    set h : Fld d L N₁ m₁ k N := constFld ((νj : ℂ)⁻¹ • ((νj : ℂ) • (Pi.single i₀ 1 : Fin N → ℂ) +
      t • (Pi.single i₁ 1 : Fin N → ℂ))) with hh
    have hdomΨh : Dom.dom j (Tm.gs j X) Ψ h := by
      have h1 : ∀ z i, ‖Ψ z i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ ρ := by
        intro z i
        simp only [hΨ, Pi.add_apply, Pi.smul_apply, smul_eq_mul, constFld, add_sub_cancel_left]
        rw [norm_mul]
        calc ‖s‖ * ‖(blockDirV L j u (Pi.single i₁ 1 : Fin N → ℂ)) z i‖ ≤ ρ * 1 :=
              mul_le_mul hs (norm_blockDirV_single_le u i₁ z i) (norm_nonneg _) ctx.rho_pos.le
          _ = ρ := mul_one _
      have h2 : ∀ z z', jBlock d L (N₁ * L ^ m₁) k j z = jBlock d L (N₁ * L ^ m₁) k j z' →
          Ψ z = Ψ z' := by
        intro z z' hz
        simp only [hΨ, Pi.add_apply, Pi.smul_apply, constFld]
        unfold blockDirV
        rw [cbase_pow_eq_of_jBlock ctx.jk hz]
      have h3 : ∀ i, ‖((νj : ℂ) • (Pi.single i₀ 1 : Fin N → ℂ) + t • (Pi.single i₁ 1 : Fin N → ℂ)) i -
          (nuIdeal L k νk j : ℂ) * (Pi.single i₀ 1 : Fin N → ℂ) i‖ < ρ := by
        intro i
        rw [← hνj]
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_sub_cancel_left]
        rw [norm_mul]
        have h1 : ‖(Pi.single i₁ (1 : ℂ) : Fin N → ℂ) i‖ ≤ 1 := by
          by_cases hi : i = i₁ <;> simp [hi]
        calc ‖t‖ * ‖(Pi.single i₁ (1 : ℂ) : Fin N → ℂ) i‖ ≤ ‖t‖ * 1 :=
              mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
          _ < ρ := by linarith
      have this := ctx.dom i₀ X hX Ψ ((νj : ℂ) • (Pi.single i₀ 1 : Fin N → ℂ) +
        t • (Pi.single i₁ 1 : Fin N → ℂ)) h1 h2 h3
      rw [← hνj] at this
      have e : h = fun _ i => ((νj : ℂ) • (Pi.single i₀ 1 : Fin N → ℂ) +
          t • (Pi.single i₁ 1 : Fin N → ℂ)) i / (νj : ℂ) := by
        funext x i
        simp only [hh, constFld, Pi.smul_apply, Pi.add_apply, smul_eq_mul, div_eq_inv_mul]
      rw [e]; exact this
    have hrot := ctx.tc.rotE j ctx.j1 ctx.jk y X hX hy (cmat Q) (isRot_cmat hQ) Ψ h hdomΨh
      (ctx.rotDom Q hQ X _ _ hdomΨh)
    have e1 : rotField (cmat Q) Ψ = constFld w0 + s • blockDirV L j u w1 := by
      rw [hΨ, rotField_add_smul, rotField_constFld, rotField_blockDirV, ← hw0, ← hw1]
    have e2 : rotField (cmat Q) h =
        constFld ((νj : ℂ)⁻¹ • ((νj : ℂ) • w0 + t • w1)) := by
      rw [hh, rotField_constFld, hw0, hw1]
      funext x
      simp [Matrix.mulVec_smul, Matrix.mulVec_add]
    rw [e1, e2] at hrot
    exact hrot
  refine Filter.EventuallyEq.deriv_eq ?_
  have hball : Metric.ball (0 : ℂ) ρ ∈ nhds (0 : ℂ) := Metric.ball_mem_nhds _ ctx.rho_pos
  filter_upwards [hball] with t ht
  have ht' : ‖t‖ < ρ := by simpa using ht
  refine Filter.EventuallyEq.deriv_eq ?_
  have hcb : Metric.closedBall (0 : ℂ) ρ ∈ nhds (0 : ℂ) :=
    Metric.closedBall_mem_nhds _ ctx.rho_pos
  filter_upwards [hcb] with s hs
  exact hagree s t (by simpa using hs) ht'

end V2

end Balaban.LargeField.Def7v2
