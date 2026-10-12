/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.Def6AvgSumConst

/-!
# Reynolds averaging: the first three renormalization conditions for the averaged family

(H.5)(1)-(3) of I-6 for `avgFamily`, from the infinite-volume conditions `val`, `dh`, `dpsi` of
`RenormCond` at the origin: by `avg_tsum_pack` the sum of the averaged family at constant data is
the density `ℰ_∞(0; const, const)`, so the argument of `IsSFFamily.liftInf_ren_b` and
`IsSFFamily.liftInf_ren_psi` (differentiation under the sum) applies verbatim.
-/

@[expose] public section

namespace Balaban.SmallField.Def6

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.Fluctuation
  Balaban.SmallField Filter Metric Set

variable {d L m₁ k N : ℕ} [NeZero L] {ϱ : ℝ}

section Conds

variable {P : Consts} {β ν a : ℕ → ℝ} {Ek : ℕ → ℝ}
  {Tm : ∀ (N₁ : ℕ) [NeZero N₁], Terms d L N₁ m₁ k N ϱ}
  {ρd : ∀ (N₁ : ℕ) [NeZero N₁], (CTorus d L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) →
    (CTorus d L N₁ m₁ k → Fin N → ℝ) → ℝ}
  {j : ℕ}

variable (hF : IsSFFamily P β ν a Tm ρd Ek) (hn : MomNum d L N k j ϱ P) {i₀ i₁ : Fin N}
  (hne : i₁ ≠ i₀)
include hF hn hne

/-- **(H.5)(1) for the averaged family.** -/
theorem avgFamily_ren_val :
    ∑' X : (avgFamily P β ν a Tm j i₀ (nuIdeal L k (ν k) j) (liftRadius d L N P j)).polys,
      (avgFamily P β ν a Tm j i₀ (nuIdeal L k (ν k) j) (liftRadius d L N P j)).term X.1
        (refPt i₀ (nuIdeal L k (ν k) j) X.1) = 0 := by
  have hρ0 := liftRadius_pos (d := d) (L := L) (eps_pos hF.admissible.α₀_pos j) i₀
  have h := avg_tsum_pack hF hn hne (Pi.single i₀ 1) (Pi.single i₀ 1)
    (fun i => by simp [hρ0]) (fun i => by simp [hρ0])
  simp_rw [refPt_eq_pack]
  rw [h]
  exact (hF.renorm j hn.hj1 hn.hjk).val i₀

/-- **(H.5)(2) for the averaged family**, from the `h`-derivative condition `dh` of `RenormCond`. -/
theorem avgFamily_ren_b :
    ∑' X : (avgFamily P β ν a Tm j i₀ (nuIdeal L k (ν k) j) (liftRadius d L N P j)).polys,
      fderiv ℂ ((avgFamily P β ν a Tm j i₀ (nuIdeal L k (ν k) j) (liftRadius d L N P j)).term X.1)
        (refPt i₀ (nuIdeal L k (ν k) j) X.1) (Pi.single (Sum.inr i₀) 1) = 0 := by
  have hνj := nuIdeal_pos' (L := L) hF.coeff.nu_pos j
  have hρ0 := liftRadius_pos (d := d) (L := L) (eps_pos hF.admissible.α₀_pos j) i₀
  have hE0 := hF.admissible.E₀_nonneg
  have hP := avgFamily_core hF hn hne
  set T := avgFamily P β ν a Tm j i₀ (nuIdeal L k (ν k) j) (liftRadius d L N P j) with hT
  set νj := nuIdeal L k (ν k) j with hνjdef
  set e : Fin N → ℂ := Pi.single i₀ 1 with he
  let Aop : ∀ X : T.polys, (Fin N → ℂ) →L[ℂ] Cfg d N X.1 := fun X => bLin X.1 νj
  have hD := hasFDerivAt_tsum_term hP hρ0 hE0 Aop hνj (fun X => norm_bLin_le X.1 hνj.le) e
  have hS := summable_fderiv_comp hP hρ0 hE0 Aop (fun X => norm_bLin_le X.1 hνj.le)
  have hcfg : ∀ (X : T.polys) (h : Fin N → ℂ),
      refPt i₀ νj X.1 + Aop X (h - e) = pack X.1 (fun _ => e) ((νj : ℂ) • h) := by
    intro X h
    funext idx
    cases idx with
    | inl p => simp [Aop, bLin_apply_inl, pack, refPt, he]
    | inr i =>
      simp only [Pi.add_apply, Aop, bLin_apply_inr, refPt, pack, Sum.elim_inr, Pi.smul_apply,
        Pi.sub_apply, smul_eq_mul]
      ring
  have hev : (fun h : Fin N → ℂ => ElocInf P.m₀ Tm j 0 (constInf e) (constInf h)) =ᶠ[nhds e]
      fun z : Fin N → ℂ => ∑' X : T.polys, T.term X.1 (refPt i₀ νj X.1 + Aop X (z - e)) := by
    have hball : ball e (liftRadius d L N P j / νj) ∈ nhds e := ball_mem_nhds _ (by positivity)
    filter_upwards [hball] with h hh
    simp_rw [hcfg]
    rw [avg_tsum_pack hF hn hne e h (fun i => by simp [he, hρ0]) (fun i => ?_)]
    rw [mem_ball, dist_eq_norm] at hh
    have h1 : ‖h i - e i‖ ≤ ‖h - e‖ := by
      simpa using norm_le_pi_norm (h - e) i
    calc νj * ‖h i - e i‖ ≤ νj * ‖h - e‖ := mul_le_mul_of_nonneg_left h1 hνj.le
      _ < νj * (liftRadius d L N P j / νj) := mul_lt_mul_of_pos_left hh hνj
      _ = liftRadius d L N P j := by field_simp
  have hg := hD.congr_of_eventuallyEq hev
  have hdh := (hF.renorm j hn.hj1 hn.hjk).dh i₀ hνj
  have hap := (ContinuousLinearMap.apply ℂ ℂ e).map_tsum hS
  simp only [ContinuousLinearMap.apply_apply] at hap
  rw [hg.fderiv, hap] at hdh
  have hL_e : ∀ X : T.polys, ((fderiv ℂ (T.term X.1) (refPt i₀ νj X.1)).comp (Aop X)) e =
      (νj : ℂ) * fderiv ℂ (T.term X.1) (refPt i₀ νj X.1) (Pi.single (Sum.inr i₀) 1) := by
    intro X
    simp only [ContinuousLinearMap.comp_apply]
    have : Aop X e = (νj : ℂ) • (Pi.single (Sum.inr i₀) 1 : Cfg d N X.1) := by
      funext idx
      cases idx with
      | inl p => simp [Aop, bLin_apply_inl]
      | inr i =>
        simp only [Aop, bLin_apply_inr, Pi.smul_apply, smul_eq_mul, he]
        by_cases h : i = i₀
        · subst h; simp
        · simp [h]
    rw [this, map_smul, smul_eq_mul]
  rw [tsum_congr hL_e, tsum_mul_left] at hdh
  have : ((νj : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hνj.ne'
  exact (mul_eq_zero.1 hdh).resolve_left this

/-- **(H.5)(3) for the averaged family**, from the `ψ`-derivative condition `dpsi` of
`RenormCond`. -/
theorem avgFamily_ren_psi :
    ∑' X : (avgFamily P β ν a Tm j i₀ (nuIdeal L k (ν k) j) (liftRadius d L N P j)).polys,
      ∑ x : ↥X.1, tensA i₀ (nuIdeal L k (ν k) j) X.1
        ((avgFamily P β ν a Tm j i₀ (nuIdeal L k (ν k) j) (liftRadius d L N P j)).term X.1) x
        = 0 := by
  have hνj := nuIdeal_pos' (L := L) hF.coeff.nu_pos j
  have hρ0 := liftRadius_pos (d := d) (L := L) (eps_pos hF.admissible.α₀_pos j) i₀
  have hE0 := hF.admissible.E₀_nonneg
  have hP := avgFamily_core hF hn hne
  set T := avgFamily P β ν a Tm j i₀ (nuIdeal L k (ν k) j) (liftRadius d L N P j) with hT
  set νj := nuIdeal L k (ν k) j with hνjdef
  set e : Fin N → ℂ := Pi.single i₀ 1 with he
  let Aop : ∀ X : T.polys, ℂ →L[ℂ] Cfg d N X.1 := fun X => tLin X.1 i₀
  have hD := hasFDerivAt_tsum_term hP hρ0 hE0 Aop one_pos (fun X => norm_tLin_le X.1 i₀) 0
  have hS := summable_fderiv_comp hP hρ0 hE0 Aop (fun X => norm_tLin_le X.1 i₀)
  have hcfg : ∀ (X : T.polys) (t : ℂ),
      refPt i₀ νj X.1 + Aop X (t - 0) = pack X.1 (fun _ => (1 + t) • e) ((νj : ℂ) • e) := by
    intro X t
    funext idx
    cases idx with
    | inl p =>
      obtain ⟨x, i⟩ := p
      simp only [Pi.add_apply, Aop, tLin_apply, psiDir_inl, refPt, pack, Sum.elim_inl, sub_zero,
        Pi.smul_apply, smul_eq_mul, he]
      by_cases h : i = i₀
      · subst h; simp
      · simp [h]
    | inr i =>
      simp [Aop, tLin_apply, psiDir_inr, refPt, pack, he]
  have hev : (fun t : ℂ => ElocInf P.m₀ Tm j 0 (constInf ((1 + t) • e)) (constInf e)) =ᶠ[nhds 0]
      fun z : ℂ => ∑' X : T.polys, T.term X.1 (refPt i₀ νj X.1 + Aop X (z - 0)) := by
    have hball : ball (0 : ℂ) (liftRadius d L N P j) ∈ nhds (0 : ℂ) := ball_mem_nhds _ hρ0
    filter_upwards [hball] with t ht
    simp_rw [hcfg]
    rw [mem_ball, dist_zero_right] at ht
    rw [avg_tsum_pack hF hn hne ((1 + t) • e) e (fun i => ?_) (fun i => by simp [he, hρ0])]
    have h1 : ‖((1 + t) • e) i - e i‖ ≤ ‖t‖ := by
      have : ((1 + t) • e) i - e i = t * e i := by simp only [Pi.smul_apply, smul_eq_mul]; ring
      rw [this, norm_mul]
      have : ‖e i‖ ≤ 1 := by
        by_cases h : i = i₀
        · subst h; simp [he]
        · simp [he, h]
      nlinarith [norm_nonneg t, norm_nonneg (e i)]
    exact lt_of_le_of_lt h1 ht
  have hg := hD.congr_of_eventuallyEq hev
  have hdp := (hF.renorm j hn.hj1 hn.hjk).dpsi i₀
  rw [hg.hasDerivAt.deriv] at hdp
  have hap := (ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)).map_tsum hS
  simp only [ContinuousLinearMap.apply_apply] at hap
  rw [hap] at hdp
  rw [← hdp]
  refine tsum_congr fun X => ?_
  simp only [ContinuousLinearMap.comp_apply, Aop, tLin_apply, one_smul, psiDir, map_sum]
  rfl

end Conds

end Balaban.SmallField.Def6
