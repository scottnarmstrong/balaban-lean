/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.IrrelTorusDefectCoeff
public import Balaban.SmallField.Def6BridgeInfMoment
public import Balaban.SmallField.RenormAnisoBridgeInf
public import Balaban.SmallField.IrrelTorusDefectRawMatrix

/-!
# The sum of the filed term over the infinite shapes vanishes

At the origin, for every datum, the sum over the polymers of `T∞` of `T_X + Φ_X` vanishes
(`IsSFFamily.tsum_filed_inf`). The four coefficient sums are the renormalization conditions
(`sumCondsInf`) and the vanishing of the raw second moment matrix. The jets at the reference
point of the anisotropic term, of the isotropic term and of the cut-off term agree, because the
three functions are equal near the reference point.
-/

@[expose] public section

namespace Balaban.SmallField.Def6

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.Fluctuation
  Balaban.SmallField Filter Metric Set

variable {d L m₁ k N : ℕ} [NeZero L] {ϱ : ℝ} {P : Consts} {β ν a : ℕ → ℝ} {Ek : ℕ → ℝ}
  {Tm : ∀ (N₁ : ℕ) [NeZero N₁], Terms d L N₁ m₁ k N ϱ}
  {ρd : ∀ (N₁ : ℕ) [NeZero N₁], (CTorus d L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) →
    (CTorus d L N₁ m₁ k → Fin N → ℝ) → ℝ}
  {j : ℕ}

/-- On the anisotropic polydisc the term of `T∞` on the tube is the centred term itself. -/
theorem IsSFFamily.termLInfA_eq_EauxInf (hF : IsSFFamily P β ν a Tm ρd Ek) (hd : 3 ≤ d)
    (hL : 3 ≤ L) (hϱ : bgR0 d L ≤ ϱ) (hj1 : 1 ≤ j) (hjk : j ≤ k)
    (hsmall : P.eps d L j ≤ (2 * bgK1 d L N + 2) * min (bgC0 d L N) (bgC1 d L N))
    {i₀ i₁ : Fin N} (hne : i₁ ≠ i₀) {X' : Finset (Site d)} (h0 : (0 : Site d) ∈ X')
    (hX : InfPoly (L := L) (m₁ := m₁) (k := k) P.m₀ j X') {c : Cfg d N X'}
    (hc : c ∈ polyAniso i₀ (nuIdeal L k (ν k) j) (anisoRadius d L N P j) X') :
    termLInfA Tm P.m₀ j i₀ (nuIdeal L k (ν k) j) (anisoRadius d L N P j) X' c =
      EauxInf Tm P.m₀ j i₀ (nuIdeal L k (ν k) j) X' c := by
  obtain ⟨n, hn⟩ := exists_goodAt (L := L) (m₁ := m₁) (k := k) hX
  have : NeZero (torusSeq L P.m₀ n) := ⟨torusSeq_ne_zero P.m₀ n⟩
  rw [termLInfA_eq hF.torusIndep hj1 hjk i₀ _ _ h0 hX (torusSeq L P.m₀ n) hn.1 hn.2 c,
    EauxInf_eq hF.torusIndep hj1 hjk i₀ _ h0 hX (torusSeq L P.m₀ n) hn.1 hn.2 c]
  have hrot : rotCfgL (1 : Matrix (Fin N) (Fin N) ℂ) X' c ∈
      polyAniso i₀ (nuIdeal L k (ν k) j) (anisoRadius d L N P j) X' := by
    rwa [rotCfgL_one]
  rw [termLA_eq (hF.torus _) (bgHyp_of_class hF.admissible hF.coeff hd hL hϱ) hF.coeff.nu_pos
    hj1 hjk (hF.anisoRadiusOK hsmall i₀) hn.2 h0 hne isOrth_one entryBd_one hrot, rotCfgL_one]



section Eventually

variable {X : Finset (Site d)} {i₀ i₁ : Fin N} {ν' : ℝ} {f g : Cfg d N X → ℂ}

theorem value_congr_eventually (h : f =ᶠ[nhds (refPt i₀ ν' X)] g) : f (refPt i₀ ν' X) = g (refPt i₀ ν' X) :=
  h.self_of_nhds

theorem tensA_congr_eventually (h : f =ᶠ[nhds (refPt i₀ ν' X)] g) (x : ↥X) :
    tensA i₀ ν' X f x = tensA i₀ ν' X g x := by
  unfold tensA
  rw [h.fderiv_eq]

theorem fderiv_inr_congr_eventually (h : f =ᶠ[nhds (refPt i₀ ν' X)] g) :
    fderiv ℂ f (refPt i₀ ν' X) (Pi.single (Sum.inr i₀) 1) =
      fderiv ℂ g (refPt i₀ ν' X) (Pi.single (Sum.inr i₀) 1) := by
  rw [h.fderiv_eq]

theorem tensB_congr_eventually (h : f =ᶠ[nhds (refPt i₀ ν' X)] g) (x x' : ↥X) :
    tensB i₀ i₁ ν' X f x x' = tensB i₀ i₁ ν' X g x x' := by
  unfold tensB D2
  rw [h.fderiv.fderiv_eq]

end Eventually

section Inf

variable (hF : IsSFFamily P β ν a Tm ρd Ek) (hn : MomNum d L N k j ϱ P) {i₀ i₁ : Fin N}
  (hne : i₁ ≠ i₀)
include hF hn hne

theorem IsSFFamily.termLInfA_eventually {X' : Finset (Site d)} (h0 : (0 : Site d) ∈ X')
    (hX : InfPoly (L := L) (m₁ := m₁) (k := k) P.m₀ j X') :
    termLInfA Tm P.m₀ j i₀ (nuIdeal L k (ν k) j) (anisoRadius d L N P j) X' =ᶠ[nhds
        (refPt i₀ (nuIdeal L k (ν k) j) X')]
      EauxInf Tm P.m₀ j i₀ (nuIdeal L k (ν k) j) X' := by
  have hr := (hF.anisoRadiusOK hn.hsmall i₀).1
  filter_upwards [isOpen_polyAniso.mem_nhds (refPt_mem_polyAniso (X := X') hr)] with c hc
  exact hF.termLInfA_eq_EauxInf hn.hd hn.hL hn.hϱ hn.hj1 hn.hjk hn.hsmall hne h0 hX hc

theorem IsSFFamily.termLInf_eventually {X' : Finset (Site d)} (h0 : (0 : Site d) ∈ X')
    (hX : InfPoly (L := L) (m₁ := m₁) (k := k) P.m₀ j X') :
    termLInf Tm P.m₀ j i₀ (nuIdeal L k (ν k) j) (liftRadius d L N P j) X' =ᶠ[nhds
        (refPt i₀ (nuIdeal L k (ν k) j) X')]
      EauxInf Tm P.m₀ j i₀ (nuIdeal L k (ν k) j) X' := by
  have hρ0 := liftRadius_pos (d := d) (L := L) (eps_pos hF.admissible.α₀_pos j) i₀
  filter_upwards [ball_mem_nhds (refPt i₀ (nuIdeal L k (ν k) j) X') hρ0] with c hc
  exact hF.termLInf_of_ball hn.hd hn.hL hn.hϱ hn.hj1 hn.hjk hn.hsmall hne h0 hX hc

omit hne in
theorem IsSFFamily.GE_zero_eventually {X' : Finset (Site d)} (h0 : (0 : Site d) ∈ X')
    (hX : InfPoly (L := L) (m₁ := m₁) (k := k) P.m₀ j X') :
    GE P β ν a Tm j i₀ (nuIdeal L k (ν k) j) 0 X' =ᶠ[nhds (refPt i₀ (nuIdeal L k (ν k) j) X')]
      EauxInf Tm P.m₀ j i₀ (nuIdeal L k (ν k) j) X' := by
  have hρ0 := liftRadius_pos (d := d) (L := L) (eps_pos hF.admissible.α₀_pos j) i₀
  filter_upwards [ball_mem_nhds (refPt i₀ (nuIdeal L k (ν k) j) X') hρ0] with c hc
  rw [GE_of_ball hF hn hX h0 hc]
  rfl


open Classical in
/-- **The sum over the infinite shapes of the filed term vanishes** for every datum: the four
coefficient sums are the renormalization conditions and the vanishing raw second moment matrix. -/
theorem IsSFFamily.tsum_filed_inf (ψ : Site d → Spin N) (b : Spin N) :
    Summable (fun X : (liftInfA (L := L) (m₁ := m₁) (k := k) P Tm j i₀ (nuIdeal L k (ν k) j)
        (anisoRadius d L N P j)).polys =>
      Ttw (liftInfA (L := L) (m₁ := m₁) (k := k) P Tm j i₀ (nuIdeal L k (ν k) j)
        (anisoRadius d L N P j)) i₀ (nuIdeal L k (ν k) j) X.1 ψ b +
      Phitw (liftInfA (L := L) (m₁ := m₁) (k := k) P Tm j i₀ (nuIdeal L k (ν k) j)
        (anisoRadius d L N P j)) i₀ i₁ (nuIdeal L k (ν k) j) X.1 ψ) ∧
    ∑' X : (liftInfA (L := L) (m₁ := m₁) (k := k) P Tm j i₀ (nuIdeal L k (ν k) j)
        (anisoRadius d L N P j)).polys,
      (Ttw (liftInfA (L := L) (m₁ := m₁) (k := k) P Tm j i₀ (nuIdeal L k (ν k) j)
        (anisoRadius d L N P j)) i₀ (nuIdeal L k (ν k) j) X.1 ψ b +
      Phitw (liftInfA (L := L) (m₁ := m₁) (k := k) P Tm j i₀ (nuIdeal L k (ν k) j)
        (anisoRadius d L N P j)) i₀ i₁ (nuIdeal L k (ν k) j) X.1 ψ) = 0 := by
  have hP := hF.premisesTermAnisoInf hn.hd hn.hL hn.hϱ hn.hj1 hn.hjk hn.hsmall hn.hκ hne
  have hr := (hF.anisoRadiusOK hn.hsmall i₀).1
  have hE0 := hF.admissible.E₀_nonneg
  have hA := diamA_nonneg d L P.m₀ m₁
  have SC := hF.sumCondsInf hn hne
  refine hP.tsum_ttw_add_phitw hr hE0 hA ?_ ?_ ?_ ?_ ψ b
  · refine (tsum_congr fun X => ?_).trans SC.ren_val
    exact (value_congr_eventually (hF.termLInfA_eventually hn hne X.2.1 X.2.2)).trans
      (value_congr_eventually (hF.termLInf_eventually hn hne X.2.1 X.2.2)).symm
  · refine (tsum_congr fun X => ?_).trans SC.ren_b
    exact (fderiv_inr_congr_eventually (hF.termLInfA_eventually hn hne X.2.1 X.2.2)).trans
      (fderiv_inr_congr_eventually (hF.termLInf_eventually hn hne X.2.1 X.2.2)).symm
  · refine (tsum_congr fun X => ?_).trans SC.ren_psi
    refine Finset.sum_congr rfl fun x _ => ?_
    exact (tensA_congr_eventually (hF.termLInfA_eventually hn hne X.2.1 X.2.2) x).trans
      (tensA_congr_eventually (hF.termLInf_eventually hn hne X.2.1 X.2.2) x).symm
  · intro μ η
    have hraw := raw_second_matrix_zero hF hn hne 0 μ η
    set g : Finset (Site d) → ℂ := fun X' =>
      ∑ z : ↥X', ∑ z' : ↥X',
        tensB i₀ i₁ (nuIdeal L k (ν k) j) X'
          (GE P β ν a Tm j i₀ (nuIdeal L k (ν k) j) 0 X') z z' *
        (((z.1 μ - z'.1 μ : ℤ) : ℂ) * (((z.1 η - z'.1 η : ℤ) : ℂ))) with hg
    have hsupp : Function.support g ⊆
        (liftInfA (L := L) (m₁ := m₁) (k := k) P Tm j i₀ (nuIdeal L k (ν k) j)
          (anisoRadius d L N P j)).polys := by
      intro X' hX'
      by_contra hnot
      apply hX'
      have hGE : GE P β ν a Tm j i₀ (nuIdeal L k (ν k) j) 0 X' = fun _ => 0 :=
        funext fun c => GE_eq_zero (fun h => hnot ⟨h.2, h.1⟩) _ c
      simp only [hg, hGE]
      refine Finset.sum_eq_zero fun z _ => Finset.sum_eq_zero fun z' _ => ?_
      simp [tensB, D2]
    rw [← tsum_subtype_eq_of_support_subset hsupp] at hraw
    refine Eq.trans (tsum_congr fun X => ?_) hraw
    unfold Sx
    refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun z' _ => ?_
    have h1 := tensB_congr_eventually (i₁ := i₁) (hF.termLInfA_eventually hn hne X.2.1 X.2.2) z z'
    have h2 := tensB_congr_eventually (i₁ := i₁) (hF.GE_zero_eventually (i₀ := i₀) hn X.2.1 X.2.2) z z'
    show tensB i₀ i₁ _ X.1 (termLInfA _ _ _ _ _ _ _) z z' * _ = _
    rw [h1, ← h2]
    simp only [Pi.sub_apply]

end Inf

end Balaban.SmallField.Def6
