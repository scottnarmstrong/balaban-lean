/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RadialCoefficientAvg
public import Balaban.SmallField.Def6AvgLimit
public import Balaban.SmallField.Def6AvgMomTorus
public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

/-!
# The thermodynamic limit of the radial coefficient (links M1 of `RadialCoefficientAvg`)

`RadialCoefficientAvg.lean` shows that the kernel `aCoef (avgFamilyA …)` of the renormalization step
is the coefficient `vc.v1` of the correction term (1.8), under two premises: the summability `hsum`
of the coefficients `GEder` over the polymers of `T∞`, and the limit link `hM1`.  This file proves
both from the class `IsSFFamily` (and the numeric premises `MomNum` of the landed bridge).

## Summability and tail (T1)

For a centre `y` and a site `z`, the coefficient `∂_{ψ_{i₀}(z)} ℰ_∞(y, X')` of one polymer is a
Cauchy derivative of the cut-off term of `T∞` on a ball of the radius `liftRadius` around the
reference point; the class bound gives `‖GEder y X' z‖ ≤ (E₀/ρ) e^{-κ d_∞(X')}`
(`norm_GEder_le`).  The landed counting of the polymers of `T∞` through `y`
(`Def6AvgLimit.summable_shapes`, from `sum_wt_dInf_le_at`) then gives `summable_GEder` with
`∑ ‖GEder‖ ≤ (E₀/ρ) K₀` and the tail bound `tail_GEder`.

## The limit (T2)

On the `n`-th torus of the sequence the whole-torus coefficient `v1T` at the block corner of `y` is
a sum over the shapes `X' ∋ y` that are good on that torus (non-winding lattice polymers whose lift
is a polymer of `𝒟_j`); every polymer of the torus is such a lift (`polysAt_eq_image`), so no
surjectivity premise (`hsurj`) is needed.  The shapes whose covering size is below a threshold that
grows with the torus are polymers of `T∞`, and on them the torus coefficient is `GEder`
(`GE_eq_EauxC`, the torus-independence clause of the class).  All the other shapes are controlled by
the same Cauchy bound on the torus and the torus counting (`exp_sum_le_at`, constants independent
of the torus), which gives the dominated convergence of `Def6AvgLimit.tendsto_shapeSum`.

The class fields used: the torus family (`hF.ctxSeq`: analyticity on the data domain, the bound
`E₀ e^{-κ d_j}`, locality), the torus independence of the class terms (`hF.torusIndep`, through
`GE_eq_EauxC`), the translation covariance of the sum over polymers through a centre (`eucEloc`, in
`v1T_translate`, used only in the translation statement), the source relation `D1Corr.src_pos`
(in `hsrc`), and the numeric premises `MomNum`.  Nothing about the winding polymers of a small
torus is needed: they are in the part of the sum that tends to `0`.
-/

@[expose] public section

namespace Balaban.LargeField.Def7v2

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.Fluctuation Filter Matrix Metric

section Torus

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ} {P : Consts} {β ν a : ℕ → ℝ}
  {Tm : Terms d L N₁ m₁ k N ϱ}
  {ρd : (Localization.CTorus d L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) →
    (Localization.CTorus d L N₁ m₁ k → Fin N → ℝ) → ℝ}
  {Ek : ℝ} {j : ℕ} {ρ : ℝ}

/-- **Cauchy bound of one coefficient on a torus**: for a shape `X' ∋ y` that does not wind and
whose lift is a polymer of `𝒟_j`, `‖∂_{ψ_{i₀}(x)} ℰ(y, Y)‖ ≤ E₀ e^{-κ d_j(Y)} / ρ`, `Y` the lift of
`X'`, `ρ` the radius of the lifting context. -/
theorem norm_tensA_EauxC_le (ctx : LiftCtx P β ν a Tm ρd Ek j ρ) (i₀ : Fin N) {y : SmallField.Site d}
    {X' : Finset (SmallField.Site d)} (hnw : NonWind L N₁ m₁ k j X')
    (hpd : IsPolyDom P.m₀ j (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X')) (hy : y ∈ X')
    (x : ↥X') :
    ‖tensA i₀ (nuIdeal L k (ν k) j) X' (EauxC Tm j i₀ (nuIdeal L k (ν k) j) y X') x‖ ≤
      P.E₀ * Real.exp (-P.κ * sizeJ (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P.m₀ j
        (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X')) / ρ := by
  have hb : ∀ c ∈ ball (refPt i₀ (nuIdeal L k (ν k) j) X') ρ,
      ‖EauxC Tm j i₀ (nuIdeal L k (ν k) j) y X' c‖ ≤ P.E₀ * Real.exp (-P.κ *
        sizeJ (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P.m₀ j
          (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X')) := fun c hc =>
    ctx.norm_EauxC_le i₀ hpd y hnw hy (ctx.mem_xiDom i₀ hpd hc)
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
theorem v1Loc_eq_zero_of_not_mem (ctx : LiftCtx P β ν a Tm ρd Ek j ρ) {i₀ : Fin N}
    {X' : Finset (SmallField.Site d)}
    (hpd : IsPolyDom P.m₀ j (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X'))
    {w : Localization.CTorus d L N₁ m₁ k}
    (hw : w ∈ Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X')
    {u : Localization.CTorus d L N₁ m₁ k} (hu : Aligned (L ^ j) u)
    (hux : unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j u ∉ X')
    (Et : Fld d L N₁ m₁ k N → Fld d L N₁ m₁ k N → ℂ)
    (hEt : ∀ (Ψ : Fld d L N₁ m₁ k N) (b : Fin N → ℂ),
      Et Ψ (constFld b) = Tm.E j w (Ypoly j X') Ψ
        (constFld (((nuIdeal L k (ν k) j : ℝ) : ℂ)⁻¹ • b))) :
    v1Loc Et j (nuIdeal L k (ν k) j) (Pi.single i₀ 1) u = 0 := by
  have hjk := ctx.jk
  have hjh := ctx.analyticAt_E i₀ w hpd hw
  have hcu : ∀ z : Localization.CTorus d L N₁ m₁ k,
      (cbase (L ^ j) z = u ↔ unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j z =
        unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j u) :=
    fun z => by rw [cbase_eq_iff_jBlock hjk hu z, unlift_eq_iff]
  have hνj : 0 < nuIdeal L k (ν k) j := by
    have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    have := ctx.nu_pos
    unfold nuIdeal; positivity
  have hνc : ((nuIdeal L k (ν k) j : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hνj.ne'
  have hEt' : (fun ψ : Fld d L N₁ m₁ k N =>
      Et ψ (constFld (((nuIdeal L k (ν k) j : ℝ) : ℂ) • (Pi.single i₀ 1 : Fin N → ℂ)))) =
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
  · refine ctx.sf.localE j _ _ _ _ _ _ (fun z hz => ⟨?_, rfl⟩)
    have hne' : ¬ cbase (L ^ j) z = u := fun h => hux (by
      have := (hcu z).1 h
      rw [← this]; exact hz)
    simp [blockDirV, hne']

end Torus

section Lim

variable {d L m₁ k N : ℕ} [NeZero L] {ϱ : ℝ} {P : Consts} {β ν a : ℕ → ℝ} {Ek : ℕ → ℝ}
  {Tm : ∀ (N₁ : ℕ) [NeZero N₁], Terms d L N₁ m₁ k N ϱ}
  {ρd : ∀ (N₁ : ℕ) [NeZero N₁], (Localization.CTorus d L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) →
    (Localization.CTorus d L N₁ m₁ k → Fin N → ℝ) → ℝ}
  {j : ℕ}

variable (P ν Tm j) in
/-- The coefficient of the shape `X'` on the `n`-th torus of the sequence:
`∂_{ψ_{i₀}(z)} ℰ(y, Y)` for the lift `Y` of `X'`, read at the reference point through the centred
class term `EauxC` (`0` for `z ∉ X'`).  It is the torus counterpart of `GEder`; on a polymer of `T∞`
that is good on the torus the two agree (`GEder_eq_GEderN`).  Auxiliary to the limit argument. -/
noncomputable def GEderN (i₀ : Fin N) (y z : SmallField.Site d) (n : ℕ) (X' : Finset (SmallField.Site d)) : ℂ :=
  haveI : NeZero (torusSeq L P.m₀ n) := ⟨torusSeq_ne_zero P.m₀ n⟩
  if hz : z ∈ X' then
    tensA i₀ (nuIdeal L k (ν k) j) X'
      (EauxC (Tm (torusSeq L P.m₀ n)) j i₀ (nuIdeal L k (ν k) j) y X') ⟨z, hz⟩
  else 0

section LimF

variable (hF : IsSFFamily P β ν a Tm ρd Ek) (hn : MomNum d L N k j ϱ P) {i₀ : Fin N}
include hF hn

/-- On a shape that is a polymer of `T∞` and good on the `n`-th torus, the coefficient of the cut-off
term `GE` of `T∞` is the coefficient of the torus term (torus independence of the class). -/
theorem GEder_eq_GEderN {y z : SmallField.Site d} {X' : Finset (SmallField.Site d)} (hy : y ∈ X')
    (hX : InfPoly (L := L) (m₁ := m₁) (k := k) P.m₀ j X') {n : ℕ}
    (hgood : GoodAt L m₁ k P.m₀ j X' n) :
    GEder P β ν a Tm j i₀ (nuIdeal L k (ν k) j) y X' z = GEderN P ν Tm j i₀ y z n X' := by
  have : NeZero (torusSeq L P.m₀ n) := ⟨torusSeq_ne_zero P.m₀ n⟩
  have hρ0 := liftRadius_pos (d := d) (L := L) (eps_pos hF.admissible.α₀_pos j) i₀
  unfold GEder GEderN
  by_cases hz : z ∈ X'
  · simp only [hz, dite_true]
    unfold tensA
    have hev : GE P β ν a Tm j i₀ (nuIdeal L k (ν k) j) y X' =ᶠ[nhds (refPt i₀ (nuIdeal L k (ν k) j) X')]
        EauxC (Tm (torusSeq L P.m₀ n)) j i₀ (nuIdeal L k (ν k) j) y X' := by
      filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hρ0)] with c hc
      exact GE_eq_EauxC hF hn hX hy hc hgood
    rw [hev.fderiv_eq (𝕜 := ℂ)]
  · simp [hz]

/-- The Cauchy bound of the coefficient on a good torus. -/
theorem norm_GEderN_le {y z : SmallField.Site d} {n : ℕ} {X' : Finset (SmallField.Site d)} (hy : y ∈ X')
    (hgood : GoodAt L m₁ k P.m₀ j X' n) :
    ‖GEderN P ν Tm j i₀ y z n X'‖ ≤
      P.E₀ / liftRadius d L N P j * Real.exp (-P.κ * sizeSeq L m₁ k P.m₀ j X' n) := by
  have : NeZero (torusSeq L P.m₀ n) := ⟨torusSeq_ne_zero P.m₀ n⟩
  have ctx := hF.ctxSeq hn i₀ n
  unfold GEderN
  by_cases hz : z ∈ X'
  · simp only [hz, dite_true]
    refine (norm_tensA_EauxC_le ctx i₀ hgood.1 hgood.2 hy ⟨z, hz⟩).trans (le_of_eq ?_)
    unfold sizeSeq
    ring
  · simp only [hz, dite_false, norm_zero]
    have := hF.admissible.E₀_nonneg
    have := liftRadius_pos (d := d) (L := L) (eps_pos hF.admissible.α₀_pos j) i₀
    positivity

/-- **The Cauchy bound of the coefficient of a polymer of `T∞`**: `‖∂_{ψ_{i₀}(z)} ℰ_∞(y, X')‖ ≤
(E₀/ρ) e^{-κ d_∞(X')}`, `ρ` the radius `liftRadius` of the class. -/
theorem norm_GEder_le {y z : SmallField.Site d} {X' : Finset (SmallField.Site d)} (hy : y ∈ X')
    (hX : InfPoly (L := L) (m₁ := m₁) (k := k) P.m₀ j X') :
    ‖GEder P β ν a Tm j i₀ (nuIdeal L k (ν k) j) y X' z‖ ≤
      P.E₀ / liftRadius d L N P j * Real.exp (-P.κ * dInf L m₁ k P.m₀ j X') := by
  obtain ⟨n₀, hn₀⟩ := exists_goodAt (L := L) (m₁ := m₁) (k := k) hX
  have hκ0 : 0 ≤ P.κ := by linarith [hn.hκ, aEnt_nonneg d L]
  refine bound_dInf hn₀ (norm_nonneg _) hκ0 fun n hgood => ?_
  rw [GEder_eq_GEderN hF hn hy hX hgood]
  exact norm_GEderN_le hF hn hy hgood

omit hn in
theorem rad_const_nonneg (i₀ : Fin N) : 0 ≤ P.E₀ / liftRadius d L N P j := by
  have := hF.admissible.E₀_nonneg
  have := liftRadius_pos (d := d) (L := L) (eps_pos hF.admissible.α₀_pos j) i₀
  positivity

/-- **T1, summability of the coefficients of `T∞` through a centre `y`** (`hsum` of
`aCoef_avgFamilyA_eq_sum`): the series `∑_{X'} ∂_{ψ_{i₀}(z)} ℰ_∞(y, X')` converges absolutely, and
`∑ ‖GEder y X' z‖ ≤ (E₀/ρ) K₀`. -/
theorem summable_GEder (y z : SmallField.Site d) :
    Summable (fun X' : Finset (SmallField.Site d) =>
      ‖GEder P β ν a Tm j i₀ (nuIdeal L k (ν k) j) y X' z‖) ∧
    ∑' X' : Finset (SmallField.Site d), ‖GEder P β ν a Tm j i₀ (nuIdeal L k (ν k) j) y X' z‖ ≤
      P.E₀ / liftRadius d L N P j * K0 d L P.κ :=
  summable_shapes (m₀ := P.m₀) (j := j) hn.hjk (by linarith [hn.hκ]) y _
    (rad_const_nonneg (j := j) hF i₀)
    (fun X' hy hX => norm_GEder_le hF hn hy hX)
    (fun X' h => GEder_eq_zero_of_inactive fun h' => h ⟨h'.2, h'.1⟩)

/-- Summability of the coefficients (not of their norms). -/
theorem summable_GEder' (y z : SmallField.Site d) :
    Summable (fun X' : Finset (SmallField.Site d) =>
      GEder P β ν a Tm j i₀ (nuIdeal L k (ν k) j) y X' z) :=
  Summable.of_norm (summable_GEder hF hn y z).1

/-- **T1, tail bound**: the polymers through `y` of size `d_∞ ≥ s` contribute at most
`(E₀/ρ) e^{-(κ - a_ent - 1) s} K₀(a_ent + 1)`. -/
theorem tail_GEder (y z : SmallField.Site d) (s : ℝ) :
    ∑' X' : Finset (SmallField.Site d), (if s ≤ dInf L m₁ k P.m₀ j X' then
        ‖GEder P β ν a Tm j i₀ (nuIdeal L k (ν k) j) y X' z‖ else 0) ≤
      P.E₀ / liftRadius d L N P j * Real.exp (-(P.κ - (aEnt d L + 1)) * s) *
        K0 d L (aEnt d L + 1) := by
  classical
  set κ₁ : ℝ := aEnt d L + 1 with hκ₁
  have hκle : κ₁ ≤ P.κ := by rw [hκ₁]; linarith [hn.hκ]
  set C : ℝ := P.E₀ / liftRadius d L N P j * Real.exp (-(P.κ - κ₁) * s) with hC
  have hC0 : 0 ≤ C := by
    have := rad_const_nonneg (j := j) hF i₀
    rw [hC]; positivity
  have h := summable_shapes (m₀ := P.m₀) (m₁ := m₁) (j := j) hn.hjk (κ := κ₁) le_rfl y
    (fun X' => if s ≤ dInf L m₁ k P.m₀ j X' then
      GEder P β ν a Tm j i₀ (nuIdeal L k (ν k) j) y X' z else 0) hC0
    (fun X' hy hX => ?_) (fun X' h => ?_)
  · have e : ∀ X', ‖(if s ≤ dInf L m₁ k P.m₀ j X' then
        GEder P β ν a Tm j i₀ (nuIdeal L k (ν k) j) y X' z else 0)‖ =
        (if s ≤ dInf L m₁ k P.m₀ j X' then
          ‖GEder P β ν a Tm j i₀ (nuIdeal L k (ν k) j) y X' z‖ else 0) := by
      intro X'; split_ifs <;> simp
    simp only [e] at h
    exact h.2
  · by_cases hs : s ≤ dInf L m₁ k P.m₀ j X'
    · simp only [hs, ite_true]
      refine (norm_GEder_le hF hn hy hX).trans ?_
      have : Real.exp (-P.κ * dInf L m₁ k P.m₀ j X') ≤
          Real.exp (-(P.κ - κ₁) * s) * Real.exp (-κ₁ * dInf L m₁ k P.m₀ j X') := by
        rw [← Real.exp_add]
        refine Real.exp_le_exp.2 ?_
        nlinarith [sub_nonneg.2 hκle, sub_nonneg.2 hs]
      calc _ ≤ P.E₀ / liftRadius d L N P j * (Real.exp (-(P.κ - κ₁) * s) *
            Real.exp (-κ₁ * dInf L m₁ k P.m₀ j X')) :=
            mul_le_mul_of_nonneg_left this (rad_const_nonneg (j := j) hF i₀)
        _ = _ := by rw [hC]; ring
    · simp only [hs, ite_false, norm_zero]
      positivity
  · by_cases hs : s ≤ dInf L m₁ k P.m₀ j X'
    · simp only [hs, ite_true]
      exact GEder_eq_zero_of_inactive fun h' => h ⟨h'.2, h'.1⟩
    · simp [hs]

end LimF

end Lim

section Axis

open Balaban.LargeField.Def7 in
/-- **The rotation carrying the coordinate axis to the physical field**: for a unit vector
`hv ∈ ℝ^N` and an index `i₀` there is a real orthogonal matrix `Q` (`Qᵀ Q = 1`) with
`Q e_{i₀} = hv` (as complex vectors); it is the matrix of a reflection. -/
theorem exists_rot_axis {N : ℕ} (i₀ : Fin N) (hv : EuclideanSpace ℝ (Fin N)) (hh : ‖hv‖ = 1) :
    ∃ Q : Matrix (Fin N) (Fin N) ℝ, Qᵀ * Q = 1 ∧
      hC hv = cmat Q *ᵥ (Pi.single i₀ 1 : Fin N → ℂ) := by
  set e : EuclideanSpace ℝ (Fin N) := EuclideanSpace.single i₀ 1 with he
  have hne : ‖e‖ = ‖hv‖ := by rw [hh, he]; simp
  set R : EuclideanSpace ℝ (Fin N) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N) :=
    Submodule.reflection (ℝ ∙ (e - hv))ᗮ with hR
  have hRe : R e = hv := Submodule.reflection_sub hne
  refine ⟨Matrix.of fun i k => R (EuclideanSpace.single k 1) i, ?_, ?_⟩
  · ext a b
    have h1 : inner ℝ (R (EuclideanSpace.single a (1 : ℝ))) (R (EuclideanSpace.single b (1 : ℝ))) =
        inner ℝ (EuclideanSpace.single a (1 : ℝ)) (EuclideanSpace.single b (1 : ℝ)) :=
      R.inner_map_map _ _
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Matrix.one_apply]
    rw [EuclideanSpace.inner_single_left] at h1
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial] at h1
    simp only [PiLp.single_apply] at h1
    by_cases hab : a = b
    · subst hab
      simp at h1
      simpa [mul_comm] using h1
    · simp [hab] at h1 ⊢
      simpa [mul_comm] using h1
  · funext i
    simp only [cmat, Matrix.mulVec, dotProduct, Matrix.map_apply, Matrix.of_apply, hC]
    rw [Finset.sum_eq_single i₀]
    · simp only [Pi.single_eq_same, mul_one]
      rw [← hRe]
    · intro b _ hb; simp [hb]
    · simp

end Axis

section LimitThm

variable {d L m₁ k N : ℕ} [NeZero L] {ϱ : ℝ} {P : Consts} {β ν a : ℕ → ℝ} {Ek : ℕ → ℝ}
  {Tm : ∀ (N₁ : ℕ) [NeZero N₁], Terms d L N₁ m₁ k N ϱ}
  {ρd : ∀ (N₁ : ℕ) [NeZero N₁], (Localization.CTorus d L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) →
    (Localization.CTorus d L N₁ m₁ k → Fin N → ℝ) → ℝ}
  {j : ℕ}

open Classical Balaban.SmallField.Def6v2 in
/-- **The whole-torus coefficient as a sum over the shapes** through `y`: on the `n`-th torus of the
sequence (for `n` so large that `y` and `z` are centred), `v1T` at the block corners of `y` and `z`
is the sum, over the shapes `X' ∋ y` that are good on the torus, of the coefficients `GEderN`.  Every
polymer of the torus through `blockPt y` is the lift of such a shape (`polysAt_eq_image`). -/
theorem v1T_eq_sum_GEderN (hF : IsSFFamily P β ν a Tm ρd Ek) (hn : MomNum d L N k j ϱ P)
    (i₀ : Fin N) (St : ∀ (N₁ : ℕ) [NeZero N₁], SourceTerms d L N₁ m₁ k N)
    (hsrc : ∀ (N₁ : ℕ) [NeZero N₁] (y : Localization.CTorus d L N₁ m₁ k)
      (Y : Set (Localization.CTorus d L N₁ m₁ k)) (Ψ : Fld d L N₁ m₁ k N) (b : Fin N → ℂ),
      (St N₁).E j y Y Ψ (constFld b) =
        (Tm N₁).E j y Y Ψ (constFld (((nuIdeal L k (ν k) j : ℝ) : ℂ)⁻¹ • b)))
    (y z : SmallField.Site d) (n : ℕ)
    (hyu : unlift (L := L) (N₁ := torusSeq L P.m₀ n) (m₁ := m₁) (k := k) j (blockPt j y) = y)
    (hzu : unlift (L := L) (N₁ := torusSeq L P.m₀ n) (m₁ := m₁) (k := k) j (blockPt j z) = z) :
    (haveI : NeZero (torusSeq L P.m₀ n) := ⟨torusSeq_ne_zero P.m₀ n⟩; v1T P.m₀ (St (torusSeq L P.m₀ n)) j (nuIdeal L k (ν k) j) (Pi.single i₀ 1)
        (blockPt j y) (blockPt j z)) =
      ∑ᶠ X' ∈ ShAt (d := d) L m₁ k P.m₀ j y n, GEderN P ν Tm j i₀ y z n X' := by
  have : NeZero (torusSeq L P.m₀ n) := ⟨torusSeq_ne_zero P.m₀ n⟩
  have ctx := hF.ctxSeq hn i₀ n
  have hjk := hn.hjk
  unfold v1T
  rw [polysAt_eq_image hjk (torusSeq_dvd P.m₀ n) (blockPt j y)]
  rw [finsum_mem_image (g := fun X' => Ypoly (L := L) (N₁ := torusSeq L P.m₀ n) (m₁ := m₁)
    (k := k) j X') (f := fun Y => v1Loc ((St (torusSeq L P.m₀ n)).E j (blockPt j y) Y) j
      (nuIdeal L k (ν k) j) (Pi.single i₀ 1) (blockPt j z))
    (fun A hA B hB h => ypoly_injOn_nonWind hjk hA.2.1 hB.2.1 h)]
  rw [hyu]
  have hset : {X' : Finset (SmallField.Site d) | y ∈ X' ∧
      NonWind L (torusSeq L P.m₀ n) m₁ k j X' ∧
      IsPolyDom (L := L) (N₁ := torusSeq L P.m₀ n) (m₁ := m₁) (k := k) P.m₀ j
        (Ypoly (L := L) (N₁ := torusSeq L P.m₀ n) (m₁ := m₁) (k := k) j X')} =
      ShAt (d := d) L m₁ k P.m₀ j y n := by
    ext X'
    simp only [Set.mem_ofPred_eq, ShAt, GoodAt]
  rw [hset]
  refine finsum_mem_congr rfl fun X' hX' => ?_
  obtain ⟨hy, hnw, hpd⟩ : y ∈ X' ∧ NonWind L (torusSeq L P.m₀ n) m₁ k j X' ∧
      IsPolyDom (L := L) (N₁ := torusSeq L P.m₀ n) (m₁ := m₁) (k := k) P.m₀ j
        (Ypoly (L := L) (N₁ := torusSeq L P.m₀ n) (m₁ := m₁) (k := k) j X') := by
    rw [← hset] at hX'; exact hX'
  have hEt : ∀ (Ψ : Fld d L (torusSeq L P.m₀ n) m₁ k N) (b : Fin N → ℂ),
      (St (torusSeq L P.m₀ n)).E j (blockPt j y) (Ypoly j X') Ψ (constFld b) =
        (Tm (torusSeq L P.m₀ n)).E j (blockPt j y) (Ypoly j X') Ψ
          (constFld (((nuIdeal L k (ν k) j : ℝ) : ℂ)⁻¹ • b)) :=
    fun Ψ b => hsrc (torusSeq L P.m₀ n) (blockPt j y) (Ypoly j X') Ψ b
  have hbp : blockPt (L := L) (N₁ := torusSeq L P.m₀ n) (m₁ := m₁) (k := k) j z = ibase j z := by
    funext μ; simp only [blockPt, ibase]; congr 1; ring
  have hal : Aligned (L ^ j) (blockPt (L := L) (N₁ := torusSeq L P.m₀ n) (m₁ := m₁) (k := k) j z) := by
    rw [hbp]; exact ibase_aligned hjk z
  unfold GEderN
  by_cases hz : z ∈ X'
  · simp only [hz, dite_true]
    have hzX : unlift (L := L) (N₁ := torusSeq L P.m₀ n) (m₁ := m₁) (k := k) j (blockPt j z) ∈ X' := by
      rw [hzu]; exact hz
    have key := tensA_EauxC_eq_v1Loc ctx (i₀ := i₀) hnw hpd hy hal hzX _ hEt
    rw [← key]
    have : (⟨unlift (L := L) (N₁ := torusSeq L P.m₀ n) (m₁ := m₁) (k := k) j (blockPt j z), hzX⟩ :
        ↥X') = ⟨z, hz⟩ := Subtype.ext hzu
    rw [this]
  · simp only [hz, dite_false]
    exact v1Loc_eq_zero_of_not_mem ctx hpd (blockPt_mem_Ypoly hjk hnw hy) hal
      (by rw [hzu]; exact hz) _ hEt

open Balaban.SmallField.Def6v2 in
/-- **T2, the thermodynamic limit of the radial coefficient (link M1)**: for all sites `y z` of the
lattice, the whole-torus coefficient `v1T` at the block corners of `y` and `z` tends, along the tori
of the sequence, to the kernel `aInfC y z = ∑_{X' ∋ y} ∂_{ψ_{i₀}(z)} ℰ_∞(y, X')` of `T∞`.  The class
fields used are those of `IsSFFamily` through `hF.ctxSeq` (bound, analyticity, locality) and
`hF.torusIndep` (through `GE_eq_EauxC`); the source relation `hsrc` is `D1Corr.src_pos`. -/
theorem tendsto_v1T_aInfC (hF : IsSFFamily P β ν a Tm ρd Ek) (hn : MomNum d L N k j ϱ P)
    (i₀ : Fin N) (St : ∀ (N₁ : ℕ) [NeZero N₁], SourceTerms d L N₁ m₁ k N)
    (hsrc : ∀ (N₁ : ℕ) [NeZero N₁] (y : Localization.CTorus d L N₁ m₁ k)
      (Y : Set (Localization.CTorus d L N₁ m₁ k)) (Ψ : Fld d L N₁ m₁ k N) (b : Fin N → ℂ),
      (St N₁).E j y Y Ψ (constFld b) =
        (Tm N₁).E j y Y Ψ (constFld (((nuIdeal L k (ν k) j : ℝ) : ℂ)⁻¹ • b)))
    (y z : SmallField.Site d) :
    Tendsto (fun n : ℕ =>
      haveI : NeZero (torusSeq L P.m₀ n) := ⟨torusSeq_ne_zero P.m₀ n⟩
      v1T P.m₀ (St (torusSeq L P.m₀ n)) j (nuIdeal L k (ν k) j) (Pi.single i₀ 1)
        (blockPt j y) (blockPt j z)) atTop
      (nhds (aInfC P β ν a Tm j i₀ (nuIdeal L k (ν k) j) y z)) := by
  have hlim := tendsto_shapeSum (m₀ := P.m₀) (m₁ := m₁) (j := j) hn.hjk (κ := P.κ)
    (by linarith [hn.hκ]) y (GEderN P ν Tm j i₀ y z)
    (fun X' => GEder P β ν a Tm j i₀ (nuIdeal L k (ν k) j) y X' z)
    (rad_const_nonneg (j := j) hF i₀)
    (fun n X' hy hgood hsz =>
      (GEder_eq_GEderN hF hn hy (infPoly_of_small hn.hjk hy hgood hsz) hgood).symm)
    (fun n X' hy hgood => norm_GEderN_le hF hn hy hgood)
    (fun X' hy hX => norm_GEder_le hF hn hy hX)
    (fun X' h => GEder_eq_zero_of_inactive fun h' => h ⟨h'.2, h'.1⟩)
  have hev : ∀ᶠ n in atTop,
      (haveI : NeZero (torusSeq L P.m₀ n) := ⟨torusSeq_ne_zero P.m₀ n⟩; v1T P.m₀ (St (torusSeq L P.m₀ n)) j (nuIdeal L k (ν k) j) (Pi.single i₀ 1)
        (blockPt j y) (blockPt j z)) =
      ∑ᶠ X' ∈ ShAt (d := d) L m₁ k P.m₀ j y n, GEderN P ν Tm j i₀ y z n X' := by
    filter_upwards [eventually_unlift_blockPt (L := L) (m₁ := m₁) (k := k) hn.hjk P.m₀ y,
      eventually_unlift_blockPt (L := L) (m₁ := m₁) (k := k) hn.hjk P.m₀ z] with n h1 h2
    exact v1T_eq_sum_GEderN hF hn i₀ St hsrc y z n h1 h2
  exact hlim.congr' (hev.mono fun n h => h.symm)

end LimitThm

section Final3

variable {d L m₁ k N : ℕ} [NeZero L] {ϱ : ℝ} {P : Consts} {β ν a : ℕ → ℝ} {Ek : ℕ → ℝ}
  {Tm : ∀ (N₁ : ℕ) [NeZero N₁], Terms d L N₁ m₁ k N ϱ}
  {ρd : ∀ (N₁ : ℕ) [NeZero N₁], (Localization.CTorus d L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) →
    (Localization.CTorus d L N₁ m₁ k → Fin N → ℝ) → ℝ}
  {j : ℕ}

open Balaban.SmallField.Def6v2 in
/-- **T3: the kernel of `T∞` is translation covariant, `a_y(z) = a_0(z - y)`** (unconditional form of
`aInfC_translate_of_M1`: the limit link is `tendsto_v1T_aInfC`). -/
theorem aInfC_translate (hF : IsSFFamily P β ν a Tm ρd Ek) (hn : MomNum d L N k j ϱ P)
    (i₀ : Fin N) (St : ∀ (N₁ : ℕ) [NeZero N₁], SourceTerms d L N₁ m₁ k N)
    (hsrc : ∀ (N₁ : ℕ) [NeZero N₁] (y : Localization.CTorus d L N₁ m₁ k)
      (Y : Set (Localization.CTorus d L N₁ m₁ k)) (Ψ : Fld d L N₁ m₁ k N) (b : Fin N → ℂ),
      (St N₁).E j y Y Ψ (constFld b) =
        (Tm N₁).E j y Y Ψ (constFld (((nuIdeal L k (ν k) j : ℝ) : ℂ)⁻¹ • b)))
    (y z : SmallField.Site d) :
    aInfC P β ν a Tm j i₀ (nuIdeal L k (ν k) j) y z =
      aInfC P β ν a Tm j i₀ (nuIdeal L k (ν k) j) 0 (z - y) :=
  aInfC_translate_of_M1 hF hn i₀ St hsrc (tendsto_v1T_aInfC hF hn i₀ St hsrc) y z

open Balaban.SmallField.Def6v2 in
/-- **T3: the averaged and the unaveraged kernels agree**, with the limit link and the summability
proved from the class (unconditional form of `aCoef_avgFamilyA_eq_liftInfA_of_M1`). -/
theorem aCoef_avgFamilyA_eq_liftInfA (hF : IsSFFamily P β ν a Tm ρd Ek)
    (hn : MomNum d L N k j ϱ P) {i₀ i₁ : Fin N} (hne : i₁ ≠ i₀)
    (St : ∀ (N₁ : ℕ) [NeZero N₁], SourceTerms d L N₁ m₁ k N)
    (hsrc : ∀ (N₁ : ℕ) [NeZero N₁] (y : Localization.CTorus d L N₁ m₁ k)
      (Y : Set (Localization.CTorus d L N₁ m₁ k)) (Ψ : Fld d L N₁ m₁ k N) (b : Fin N → ℂ),
      (St N₁).E j y Y Ψ (constFld b) =
        (Tm N₁).E j y Y Ψ (constFld (((nuIdeal L k (ν k) j : ℝ) : ℂ)⁻¹ • b)))
    (x : SmallField.Site d) :
    aCoef (avgFamilyA P β ν a Tm j i₀ (nuIdeal L k (ν k) j) (anisoRadius d L N P j)) i₀
        (nuIdeal L k (ν k) j) x =
      aCoef (liftInfA (L := L) (m₁ := m₁) (k := k) P Tm j i₀ (nuIdeal L k (ν k) j)
        (anisoRadius d L N P j)) i₀ (nuIdeal L k (ν k) j) x :=
  aCoef_avgFamilyA_eq_liftInfA_of_M1 hF hn hne St hsrc (tendsto_v1T_aInfC hF hn i₀ St hsrc) x
    (fun t => summable_GEder' hF hn (offs t) (x + offs t))

open Balaban.SmallField.Def6v2 Balaban.LargeField.Def7 in
/-- **T3, the final theorem: the marginal kernel of the renormalization step is the coefficient of
the correction (1.8).**  For a `D1Corr` datum `(St, hv, vc)` of a class family (`‖hv‖ = 1`: the
physical field is a unit vector), at the scale `j` with the numeric premises `MomNum` of the landed
bridge, the kernel `aCoef (avgFamilyA …)` of the averaged family consumed by the renormalization
theorem is the coefficient `vc.v1 j` of `D1Corr`:
`a_j(x) = v₁^{(j)}(0, x)`.  The class fields used are listed in the module doc; no premise on the
limit or on the summability is left. -/
theorem aCoef_avgFamilyA_eq_v1 {sf : SFData d L m₁ k N ϱ}
    {St : ∀ (N₁ : ℕ) [NeZero N₁], SourceTerms d L N₁ m₁ k N} {hv : EuclideanSpace ℝ (Fin N)}
    {vc : CorrCoef d} (hD : D1Corr P.m₀ sf St hv vc)
    (hF : IsSFFamily P sf.β sf.ν sf.a sf.Tm ρd Ek) (hn : MomNum d L N k j ϱ P) {i₀ i₁ : Fin N}
    (hne : i₁ ≠ i₀) (hhv : ‖hv‖ = 1) (x : SmallField.Site d) :
    aCoef (avgFamilyA P sf.β sf.ν sf.a sf.Tm j i₀ (nuIdeal L k (sf.ν k) j)
        (anisoRadius d L N P j)) i₀ (nuIdeal L k (sf.ν k) j) x = vc.v1 j x := by
  obtain ⟨Q, hQ, hw⟩ := exists_rot_axis i₀ hv hhv
  have hpos := nuIdeal_pos' (L := L) hF.coeff.nu_pos j
  have hsrc : ∀ (N₁ : ℕ) [NeZero N₁] (y : Localization.CTorus d L N₁ m₁ k)
      (Y : Set (Localization.CTorus d L N₁ m₁ k)) (Ψ : Fld d L N₁ m₁ k N) (b : Fin N → ℂ),
      (St N₁).E j y Y Ψ (constFld b) =
        (sf.Tm N₁).E j y Y Ψ (constFld (((nuIdeal L k (sf.ν k) j : ℝ) : ℂ)⁻¹ • b)) :=
    fun N₁ _ y Y Ψ b => hD.src_pos N₁ j hn.hj1 hn.hjk hpos y Y Ψ b
  exact aCoef_avgFamilyA_eq_v1_of_M1 hD hF hn hne hQ hw (tendsto_v1T_aInfC hF hn i₀ St hsrc) x
    (fun t => summable_GEder' hF hn (offs t) (x + offs t))

end Final3

end Balaban.LargeField.Def7v2
