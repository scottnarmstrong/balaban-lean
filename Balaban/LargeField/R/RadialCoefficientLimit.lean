/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RadialCoefficientAvg
public import Balaban.SmallField.Def6AvgLimit
public import Balaban.SmallField.Def6AvgMomTorus

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

end Balaban.LargeField.Def7v2
