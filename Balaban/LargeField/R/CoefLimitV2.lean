/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.CoefLimitV1
public import Balaban.LargeField.R.CoefCtxV2
public import Balaban.Analysis.Cauchy

/-!
# The thermodynamic limit of the transverse coefficient `v₂`

As `CoefLimitV1` for `v₁`: on the `n`-th torus the transverse coefficient `v2T` is a sum over the
good shapes of the mixed second derivative `∂_{b_{i₁}} ∂_{ψ_{i₁}(z)} ℰ(y, Y)` of the centred term
at the reference point.  The values agree on good tori, and the Cauchy estimate on the polydisc of
radius `ρ` bounds them by `E₀ ρ⁻² e^{-κ d_j}`.
-/

@[expose] public section

namespace Balaban.LargeField.Def7v2

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.SmallField.Def6v2 Balaban.Fluctuation Filter Matrix Metric

section Fam

variable {d L m₁ k N : ℕ} [NeZero L] {ϱ : ℝ}

variable (P : Consts) (νk : ℝ) (Tm : ∀ (N₁ : ℕ) [NeZero N₁], Terms d L N₁ m₁ k N ϱ) (j : ℕ) in
/-- The transverse coefficient of the shape `X'` on the `n`-th torus of the sequence:
`∂_{b_{i₁}} ∂_{ψ_{i₁}(z)} ℰ(y, Y)` at the reference point, for the lift `Y` of `X'` (`0` for
`z ∉ X'`). -/
noncomputable def G2derN (i₀ i₁ : Fin N) (y z : SmallField.Site d) (n : ℕ)
    (X' : Finset (SmallField.Site d)) : ℂ :=
  haveI : NeZero (torusSeq L P.m₀ n) := ⟨torusSeq_ne_zero P.m₀ n⟩
  if hz : z ∈ X' then
    fderiv ℂ (fun c : Cfg d N X' =>
        fderiv ℂ (EauxC (Tm (torusSeq L P.m₀ n)) j i₀ (nuIdeal L k νk j) y X') c
          (Pi.single (Sum.inl (⟨z, hz⟩, i₁)) 1))
      (refPt i₀ (nuIdeal L k νk j) X') (Pi.single (Sum.inr i₁) 1)
  else 0

end Fam

section Torus

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  {P : Consts} {νk : ℝ} {Dom : FieldDom d L N₁ m₁ k N ϱ} {Tm : Terms d L N₁ m₁ k N ϱ}
  {j : ℕ} {ρ : ℝ}

/-- The ball of radius `ρ` in the sup norm is the polydisc of radius `ρ`. -/
theorem mem_polydisc_of_mem_ball {ι : Type*} [Fintype ι] {c z : ι → ℂ} {r : ℝ}
    (h : z ∈ ball c r) : z ∈ Balaban.Analysis.polydisc c (fun _ => r) := by
  intro i
  have := (dist_le_pi_dist z c i).trans_lt (mem_ball.1 h)
  rwa [dist_eq_norm] at this

/-- **Cauchy bound of the transverse coefficient on a torus**. -/
theorem CoefCtx.norm_mixed_EauxC_le (ctx : CoefCtx P νk Dom Tm j ρ) (i₀ i₁ : Fin N)
    {y : SmallField.Site d} {X' : Finset (SmallField.Site d)} (hnw : NonWind L N₁ m₁ k j X')
    (hpd : IsPolyDom P.m₀ j (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X')) (hy : y ∈ X')
    (x : ↥X') :
    ‖fderiv ℂ (fun c : Cfg d N X' =>
        fderiv ℂ (EauxC Tm j i₀ (nuIdeal L k νk j) y X') c (Pi.single (Sum.inl (x, i₁)) 1))
      (refPt i₀ (nuIdeal L k νk j) X') (Pi.single (Sum.inr i₁) 1)‖ ≤
      P.E₀ * Real.exp (-P.κ * sizeJ (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P.m₀ j
        (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X')) / ρ / ρ := by
  have hρ := ctx.rho_pos
  exact Balaban.Analysis.norm_mixed_fderiv_le (r := fun _ => ρ) (fun _ => hρ)
    (fun c hc => ctx.analyticAt_EauxC i₀ hpd y hnw hy (by
      rw [mem_ball, dist_eq_norm, pi_norm_lt_iff hρ]; exact hc))
    (fun c hc => ctx.norm_EauxC_le i₀ hpd y hnw hy (by
      rw [mem_ball, dist_eq_norm, pi_norm_lt_iff hρ]; exact hc))
    (by simp)

/-- **The mixed derivative of the centred term is the iterated line derivative of the source form.**
For a polymer `X'` of the lift, a block corner `u` aligned and centred at `z ∈ X'`, the nested
derivative of `EauxC` at the reference point in the coordinates `(ψ_{i₁}(z), b_{i₁})` is
`iter2` (hence `v2Loc`, `CoefCtx.v2Loc_eq_iter`) at the axes `(e_{i₀}, e_{i₁})`. -/
theorem CoefCtx.G2der_eq_iter2 (ctx : CoefCtx P νk Dom Tm j ρ) (i₀ i₁ : Fin N)
    {y z : SmallField.Site d} {X' : Finset (SmallField.Site d)} (hnw : NonWind L N₁ m₁ k j X')
    (hpd : IsPolyDom P.m₀ j (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X')) (hy : y ∈ X')
    {u : Localization.CTorus d L N₁ m₁ k} (hu : Aligned (L ^ j) u)
    (hzu : unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j u = z) (hz : z ∈ X') :
    fderiv ℂ (fun c : Cfg d N X' =>
        fderiv ℂ (EauxC Tm j i₀ (nuIdeal L k νk j) (y) X') c
          (Pi.single (Sum.inl (⟨z, hz⟩, i₁)) 1))
      (refPt i₀ (nuIdeal L k νk j) X') (Pi.single (Sum.inr i₁) 1) =
      iter2 Tm j (blockPt j y) (Ypoly j X') (nuIdeal L k νk j) (Pi.single i₀ 1) (Pi.single i₁ 1)
        u := by
  have hjk := ctx.jk
  have hνj := ctx.nuj_pos
  have hνc : ((nuIdeal L k νk j : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hνj.ne'
  have hF := ctx.analyticAt_EauxC i₀ hpd y hnw hy (Metric.mem_ball_self ctx.rho_pos)
  rw [fderiv_fderiv_eq_deriv_deriv hF]
  unfold iter2
  have hcu : ∀ z' : Localization.CTorus d L N₁ m₁ k,
      (cbase (L ^ j) z' = u ↔ unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j z' = z) :=
    fun z' => by rw [cbase_eq_iff_jBlock hjk hu z', ← hzu, unlift_eq_iff]
  have hpt : ∀ s t : ℂ,
      EauxC Tm j i₀ (nuIdeal L k νk j) y X' (refPt i₀ (nuIdeal L k νk j) X' +
        t • (Pi.single (Sum.inr i₁) 1 : Cfg d N X') +
        s • (Pi.single (Sum.inl (⟨z, hz⟩, i₁)) 1 : Cfg d N X')) =
      srcK Tm j (blockPt j y) (Ypoly j X') (nuIdeal L k νk j)
        ((constFld (Pi.single i₀ 1 : Fin N → ℂ),
          ((nuIdeal L k νk j : ℝ) : ℂ) • (Pi.single i₀ 1 : Fin N → ℂ)) +
          t • ((0 : Fld d L N₁ m₁ k N), (Pi.single i₁ 1 : Fin N → ℂ)) +
          s • (blockDirV L j u (Pi.single i₁ 1), (0 : Fin N → ℂ))) := by
    intro s t
    rw [srcK_line]
    set c : Cfg d N X' := refPt i₀ (nuIdeal L k νk j) X' +
      t • (Pi.single (Sum.inr i₁) 1 : Cfg d N X') +
      s • (Pi.single (Sum.inl (⟨z, hz⟩, i₁)) 1 : Cfg d N X') with hc
    have hf : fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ X' c =
        constFld (Pi.single i₀ 1 : Fin N → ℂ) + s • blockDirV L j u (Pi.single i₁ 1) := by
      funext z' i
      by_cases hz' : unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j z' ∈ X'
      · simp only [fieldOf, hz', dite_true, hc, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
          Pi.single_apply, refPt_inl, blockDirV, constFld, hcu z',
          Sum.inl.injEq, Prod.mk.injEq, Subtype.mk.injEq, reduceCtorEq, ite_false, mul_zero,
          add_zero]
        by_cases h : unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j z' = z <;>
          by_cases hi : i = i₁ <;> simp [h, hi]
      · have hu0 : blockDirV L j u (Pi.single i₁ 1 : Fin N → ℂ) z' i = 0 := by
          have hne : ¬ cbase (L ^ j) z' = u := fun h => hz' (by rw [(hcu z').1 h]; exact hz)
          simp [blockDirV, hne]
        simp only [fieldOf, hz', dite_false, Pi.add_apply, Pi.smul_apply, smul_eq_mul, constFld,
          hu0]
        ring
    have hh : hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) (nuIdeal L k νk j) X' c =
        constFld (((nuIdeal L k νk j : ℝ) : ℂ)⁻¹ • (((nuIdeal L k νk j : ℝ) : ℂ) •
          (Pi.single i₀ 1 : Fin N → ℂ) + t • (Pi.single i₁ 1 : Fin N → ℂ))) := by
      funext z' i
      simp only [hOf, hc, Pi.add_apply, Pi.smul_apply, constFld]
      rw [refPt_inr]
      simp only [Pi.single_apply, smul_eq_mul, reduceCtorEq, ite_false, mul_zero, add_zero,
        Sum.inr.injEq]
      rw [div_eq_inv_mul]
    show Tm.E j (blockPt j y) (Ypoly j X') (fieldOf j i₀ X' c)
      (hOf (nuIdeal L k νk j) X' c) = _
    rw [hf, hh]
  congr 1
  funext t
  congr 1
  funext s
  exact hpt s t

end Torus

section Family

variable {d L m₁ k N : ℕ} [NeZero L] {ϱ : ℝ}
  {P : Consts} {νk : ℝ} {Dom : ∀ (N₁ : ℕ) [NeZero N₁], FieldDom d L N₁ m₁ k N ϱ}
  {Tm : ∀ (N₁ : ℕ) [NeZero N₁], Terms d L N₁ m₁ k N ϱ} {j : ℕ} {ρ : ℝ}
  (fam : CoefFam P νk Dom Tm j ρ) (i₀ i₁ : Fin N)
include fam

/-- The transverse coefficient of the shape on the `n`-th torus does not depend on the good
torus. -/
theorem CoefFam.G2derN_eq {y z : SmallField.Site d} {X' : Finset (SmallField.Site d)}
    (hy : y ∈ X') {n n' : ℕ} (hg : GoodAt L m₁ k P.m₀ j X' n) (hg' : GoodAt L m₁ k P.m₀ j X' n') :
    G2derN P νk Tm j i₀ i₁ y z n X' = G2derN P νk Tm j i₀ i₁ y z n' X' := by
  have hj1 := (fam.ctx 0).j1
  have hjk := (fam.ctx 0).jk
  have e := EauxC_eq_of_good fam.indep hj1 hjk i₀ (nuIdeal L k νk j) hy hg hg'
  unfold G2derN
  have : NeZero (torusSeq L P.m₀ n) := ⟨torusSeq_ne_zero P.m₀ n⟩
  have : NeZero (torusSeq L P.m₀ n') := ⟨torusSeq_ne_zero P.m₀ n'⟩
  by_cases hz : z ∈ X'
  · simp only [hz, dite_true]
    rw [e]
  · simp [hz]

/-- The Cauchy bound of the transverse coefficient on a good torus. -/
theorem CoefFam.norm_G2derN_le {y z : SmallField.Site d} {n : ℕ}
    {X' : Finset (SmallField.Site d)} (hy : y ∈ X') (hgood : GoodAt L m₁ k P.m₀ j X' n) :
    ‖G2derN P νk Tm j i₀ i₁ y z n X'‖ ≤
      P.E₀ / ρ / ρ * Real.exp (-P.κ * sizeSeq L m₁ k P.m₀ j X' n) := by
  have : NeZero (torusSeq L P.m₀ n) := ⟨torusSeq_ne_zero P.m₀ n⟩
  have ctx := fam.ctx n
  unfold G2derN
  by_cases hz : z ∈ X'
  · simp only [hz, dite_true]
    refine (ctx.norm_mixed_EauxC_le i₀ i₁ hgood.1 hgood.2 hy ⟨z, hz⟩).trans (le_of_eq ?_)
    unfold sizeSeq
    ring
  · simp only [hz, dite_false, norm_zero]
    have := fam.E0_nonneg
    have := (fam.ctx 0).rho_pos
    positivity

/-- **On one torus the transverse whole-torus coefficient is a sum over the shapes** through `y`. -/
theorem CoefFam.v2T_eq_sum
    (St : ∀ (N₁ : ℕ) [NeZero N₁], SourceTerms d L N₁ m₁ k N)
    (hsrc : ∀ (N₁ : ℕ) [NeZero N₁] (y : Localization.CTorus d L N₁ m₁ k)
      (Y : Set (Localization.CTorus d L N₁ m₁ k)) (Ψ : Fld d L N₁ m₁ k N) (b : Fin N → ℂ),
      (St N₁).E j y Y Ψ (constFld b) =
        (Tm N₁).E j y Y Ψ (constFld (((nuIdeal L k νk j : ℝ) : ℂ)⁻¹ • b)))
    (y z : SmallField.Site d) (n : ℕ)
    (hyu : unlift (L := L) (N₁ := torusSeq L P.m₀ n) (m₁ := m₁) (k := k) j (blockPt j y) = y)
    (hzu : unlift (L := L) (N₁ := torusSeq L P.m₀ n) (m₁ := m₁) (k := k) j (blockPt j z) = z) :
    (haveI : NeZero (torusSeq L P.m₀ n) := ⟨torusSeq_ne_zero P.m₀ n⟩;
      v2T P.m₀ (St (torusSeq L P.m₀ n)) j (nuIdeal L k νk j) (Pi.single i₀ 1) (Pi.single i₁ 1)
        (blockPt j y) (blockPt j z)) =
      ∑ᶠ X' ∈ ShAt (d := d) L m₁ k P.m₀ j y n, G2derN P νk Tm j i₀ i₁ y z n X' := by
  classical
  have : NeZero (torusSeq L P.m₀ n) := ⟨torusSeq_ne_zero P.m₀ n⟩
  have ctx := fam.ctx n
  have hjk := ctx.jk
  unfold v2T
  rw [finsum_polysAt_eq_shAt (m₁ := m₁) hjk y n hyu
    (fun Y => v2Loc ((St (torusSeq L P.m₀ n)).E j (blockPt j y) Y) j (nuIdeal L k νk j)
      (Pi.single i₀ 1) (Pi.single i₁ 1) (blockPt j z))]
  refine finsum_mem_congr rfl fun X' hX' => ?_
  obtain ⟨hy, hnw, hpd⟩ := hX'
  have hEt : ∀ (Ψ : Fld d L (torusSeq L P.m₀ n) m₁ k N) (b : Fin N → ℂ),
      (St (torusSeq L P.m₀ n)).E j (blockPt j y) (Ypoly j X') Ψ (constFld b) =
        (Tm (torusSeq L P.m₀ n)).E j (blockPt j y) (Ypoly j X') Ψ
          (constFld (((nuIdeal L k νk j : ℝ) : ℂ)⁻¹ • b)) :=
    fun Ψ b => hsrc (torusSeq L P.m₀ n) (blockPt j y) (Ypoly j X') Ψ b
  have hbp : blockPt (L := L) (N₁ := torusSeq L P.m₀ n) (m₁ := m₁) (k := k) j z = ibase j z := by
    funext μ; simp only [blockPt, ibase]; congr 1; ring
  have hal : Aligned (L ^ j) (blockPt (L := L) (N₁ := torusSeq L P.m₀ n) (m₁ := m₁) (k := k) j z) := by
    rw [hbp]; exact ibase_aligned hjk z
  unfold G2derN
  by_cases hz : z ∈ X'
  · simp only [hz, dite_true]
    rw [ctx.G2der_eq_iter2 i₀ i₁ hnw hpd hy hal hzu hz,
      ctx.v2Loc_eq_iter hpd (blockPt_mem_Ypoly hjk hnw hy) (ctx.const_dom i₀ hpd) (Pi.single i₁ 1) _
        hEt (blockPt j z)]
  · simp only [hz, dite_false]
    exact ctx.v2Loc_eq_zero_of_not_mem hal (by rw [hzu]; exact hz) _ hEt

/-- **The thermodynamic limit of the transverse coefficient exists**. -/
theorem CoefFam.exists_tendsto_v2T
    (St : ∀ (N₁ : ℕ) [NeZero N₁], SourceTerms d L N₁ m₁ k N)
    (hsrc : ∀ (N₁ : ℕ) [NeZero N₁] (y : Localization.CTorus d L N₁ m₁ k)
      (Y : Set (Localization.CTorus d L N₁ m₁ k)) (Ψ : Fld d L N₁ m₁ k N) (b : Fin N → ℂ),
      (St N₁).E j y Y Ψ (constFld b) =
        (Tm N₁).E j y Y Ψ (constFld (((nuIdeal L k νk j : ℝ) : ℂ)⁻¹ • b)))
    (y z : SmallField.Site d) :
    ∃ ℓ : ℂ, Tendsto (fun n : ℕ =>
      haveI : NeZero (torusSeq L P.m₀ n) := ⟨torusSeq_ne_zero P.m₀ n⟩;
      v2T P.m₀ (St (torusSeq L P.m₀ n)) j (nuIdeal L k νk j) (Pi.single i₀ 1) (Pi.single i₁ 1)
        (blockPt j y) (blockPt j z)) atTop (nhds ℓ) := by
  have hjk := (fam.ctx 0).jk
  have hC : 0 ≤ P.E₀ / ρ / ρ := by
    have := fam.E0_nonneg
    have := (fam.ctx 0).rho_pos
    positivity
  obtain ⟨ℓ, hℓ⟩ := exists_tendsto_shapeSum (m₀ := P.m₀) (m₁ := m₁) (j := j) hjk fam.kappa y
    (fun n X' => G2derN P νk Tm j i₀ i₁ y z n X') hC
    (fun n n' X' hy hg hg' => fam.G2derN_eq i₀ i₁ hy hg hg')
    (fun n X' hy hg => fam.norm_G2derN_le i₀ i₁ hy hg)
  refine ⟨ℓ, hℓ.congr' ?_⟩
  filter_upwards [eventually_unlift_blockPt (L := L) (m₁ := m₁) (k := k) hjk P.m₀ y,
    eventually_unlift_blockPt (L := L) (m₁ := m₁) (k := k) hjk P.m₀ z] with n h1 h2
  exact (fam.v2T_eq_sum i₀ i₁ St hsrc y z n h1 h2).symm

end Family

end Balaban.LargeField.Def7v2
