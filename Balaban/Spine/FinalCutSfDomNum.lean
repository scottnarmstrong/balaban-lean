/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.FinalCutSfDomPsi
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The small-field factor of a cut is Borel and bounded, from the smallness of the tolerance

A6-4 (`CutSfDomInput`, "A4-1i for cuts"). At a late scale `k` (positive cube mass `ν L^{-2k}`,
`0 < ν ≤ 1`), for **every** cut `Y` the small-field factor `sfFactor2(Y)` is Borel and bounded in
the block field, once the scaled tolerance `δ_k / √ν` is small against the radii of the term domains
(`cutGamma δ_k / √ν ≤ min (c, ε_j)`, `measBound_sfFactor2_cut_of_numerics`). The replacement fields
of the cores `measurable_sfFactor2_of_dom`, `exists_bound_sfFactor2_of_dom` are the extensions by
`h` of the inherited fields (`psiJExt`) and of the lift (`liftExt`); no condition on the history
of the cut enters.
-/

@[expose] public section

open MeasureTheory Balaban Balaban.Multiscale Balaban.Background Balaban.LargeField
  Balaban.LargeField.Def7 Balaban.LargeField.Def7v2 Balaban.SmallField Balaban.SmallField.Def6
  Balaban.SmallField.Def6v2 Balaban.Localization

namespace Balaban.RootFSpine

section Consts

variable (d L N : ℕ) [NeZero L]

/-- The constant of the smallness condition of the cut domains: `8 (2 K₁ + 2) (6 K₁ + 3)`. -/
noncomputable def cutGamma : ℝ := 8 * (2 * bgK1 d L N + 2) * (6 * bgK1 d L N + 3)

theorem cutGamma_pos : 0 < cutGamma d L N := by
  have := bgK1_ge_one d L N
  unfold cutGamma
  positivity

end Consts

section Vec

variable {N : ℕ}

/-- A vector within `t ≤ 1/2` of a unit vector has length in `(0, 2]`. -/
theorem rn_pos_le_two_of_near (a h : Fin N → ℝ) (hh : ∑ i, h i ^ 2 = 1) {t : ℝ}
    (ht : rn (fun i => a i - h i) ≤ t) (ht2 : 2 * t ≤ 1) : 0 < rn a ∧ rn a ≤ 2 := by
  have hrnh : rn h = 1 := by unfold rn; rw [hh, Real.sqrt_one]
  have h1 := rn_triangle a h (fun _ => 0)
  have h2 := rn_triangle h a (fun _ => 0)
  simp only [sub_zero] at h1 h2
  rw [rn_sub_comm] at h2
  constructor <;> linarith

end Vec

section Ctx

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N m₁ j : ℕ} {ϱ : ℝ} (C : SFCtx S n R M K N (j + 1) m₁ ϱ)
  (hv : EuclideanSpace ℝ (Fin N)) (vc : CorrCoef S.d) {P6 : Def6.Consts} {k0 : ℕ}

/-- **The small-field factor of a cut is Borel and bounded, from the smallness of the tolerance**
(A6-4, `CutSfDomInput`). The hypotheses are: the class clauses (the term clauses `hTm`, the
remainder clauses `hRt`), the standing hypotheses `BgHyp` of the background theory at the cube level
and at the birth masses of the inherited levels, the cube mass equal to the physical mass
`ν L^{-2k}` at the scale `k` with `0 < ν ≤ 1`, a positive tolerance `δ_k`, and the smallness
`cutGamma δ_k / √ν ≤ min (c, ε_j)`. The cut `Y` is arbitrary. -/
theorem measBound_sfFactor2_cut_of_numerics
    (hm0 : P6.m₀ = C.m₀) (hTm : SFTermClauses P6 (sfDom P6 k0 C.sf C.N₁) (C.sf.Tm C.N₁))
    {fac : ℕ → ℝ} (hRt : RTermsH4 (ϱ := ϱ) P6 C.sf.β C.sf.ν C.sf.a C.N₁ (C.sf.Rt C.N₁) fac)
    (g : GIdx S n M K N → ℂ) (hgl : g ∈ LargeField.l1Ball (GIdx S n M K N))
    (HB : BgHyp S.d S.L (j + 1) (minSep S.L C.geo.M1) C.weights (C.cs.muBg (j + 1)))
    (hL : 2 ≤ S.L) {ν : ℝ} (hν : 0 < ν) (hν1 : ν ≤ 1) (hunit : ‖hv‖ = 1)
    (hμ : C.cs.mu (j + 1) = sfBgMassAt S.L (j + 1) ν)
    (hμBg : C.cs.muBg (j + 1) = sfBgMassAt S.L (j + 1) ν)
    (hact : 0 ≤ C.cs.muAct (j + 1)) (hβ : 0 ≤ C.sf.β (j + 1))
    (hBgJ : ∀ jj, 1 ≤ jj → jj ≤ j + 1 → BgHyp S.d S.L (j + 1) ϱ
      (Def6.aIdeal S.L (j + 1) (C.sf.a (j + 1))) (physMass S.L jj (C.sf.ν jj)))
    (hratioJ : ∀ jj, 1 ≤ jj → jj ≤ j + 1 → physMass S.L jj (C.sf.ν jj) * ((S.L : ℝ) ^ jj) ^ 2 ≤
      4 * (sfBgMassAt S.L (j + 1) ν * ((S.L : ℝ) ^ jj) ^ 2))
    (hBgR : BgHyp S.d S.L (j + 1) ϱ (Def6.aIdeal S.L (j + 1) (C.sf.a (j + 1)))
      (Def6.bgMass S.L (j + 1) (C.sf.β (j + 1)) (C.sf.ν (j + 1))))
    (hratioR : Def6.bgMass S.L (j + 1) (C.sf.β (j + 1)) (C.sf.ν (j + 1)) *
        ((S.L : ℝ) ^ (j + 1)) ^ 2 ≤
      4 * (sfBgMassAt S.L (j + 1) ν * ((S.L : ℝ) ^ (j + 1)) ^ 2))
    (hδ : 0 < C.cs.delta (j + 1))
    (hnum : cutGamma S.d S.L N * (C.cs.delta (j + 1) / Real.sqrt ν) ≤ deltaCap S.d S.L N)
    (hnumε : ∀ jj, 1 ≤ jj → jj ≤ j + 1 →
      cutGamma S.d S.L N * (C.cs.delta (j + 1) / Real.sqrt ν) ≤ P6.eps S.d S.L jj)
    (Y : Set (Torus S.d (n (j + 1)))) :
    Measurable (fun ψk : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N) =>
      sfFactor2 C vc Y ψk hv g) ∧
    ∃ B : ℝ, ∀ ψk : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N),
      ‖sfFactor2 C vc Y ψk hv g‖ ≤ B := by
  classical
  set e : ℝ := C.cs.delta (j + 1) / Real.sqrt ν with he
  set t : ℝ := (6 * bgK1 S.d S.L N + 3) * e with ht
  have hsq : 0 < Real.sqrt ν := Real.sqrt_pos.2 hν
  have he0 : 0 < e := div_pos hδ hsq
  have hK1 := bgK1_ge_one S.d S.L N
  have hC4 := compC4_ge S.d
  have hd0 : 0 < S.d := by have := HB.hd; omega
  have ht0 : 0 < t := by positivity
  have hcg : cutGamma S.d S.L N * e = 8 * (2 * bgK1 S.d S.L N + 2) * t := by
    unfold cutGamma; rw [ht]; ring
  have hcap1 : cutGamma S.d S.L N * e ≤ 1 :=
    hnum.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hcapT : cutGamma S.d S.L N * e ≤ thm73C1 S.d S.L N :=
    hnum.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hcap0 : cutGamma S.d S.L N * e ≤ bgC0 S.d S.L N := hnum.trans (min_le_right _ _)
  have h32 : 32 * t ≤ cutGamma S.d S.L N * e := by rw [hcg]; nlinarith
  have ht1 : t ≤ 1 := by linarith
  have ht2 : 2 * t ≤ 1 := by linarith
  have h9e : 9 * e ≤ t := by rw [ht]; nlinarith
  have he1 : e ≤ 1 := by linarith
  have htT : t ≤ thm73C1 S.d S.L N := by linarith
  have h3eT : 3 * e ≤ thm73C1 S.d S.L N := by linarith
  have h16 : 16 * t ≤ bgC1 S.d S.L N := by
    obtain ⟨-, h2, -, -, -⟩ := thm73_small (L := S.L) (N := N) hd0 ht0 htT
    have : 16 * t ≤ 2 * (compC4 S.d * (bgK1 S.d S.L N * t)) := by nlinarith
    linarith
  have h3e1 : 3 * e ≤ bgC1 S.d S.L N :=
    (thm73_small (L := S.L) (N := N) hd0 (by positivity) h3eT).1
  have hsum : ∑ i, hv i ^ 2 = 1 := by rw [parent_sum_sq_eq_norm_sq, hunit]; norm_num
  -- the datum of the cut lies in the real domain
  have hAD : AsuppY C hv Y ⊆ DomSetY C hv Y (C.cs.muBg (j + 1)) := by
    intro ψ hψ
    rw [hμBg]
    exact mem_DomSetY_of_inPsiTilde C hv ψ Y (by positivity) h3e1
      (inPsiTilde_genW_late C hv Y ψ hL hν hν1 hunit hδ he1 hμ hψ)
  -- the extended inherited fields lie in the domains of the terms `ℰ^{(j)}`, `ℳ^{(j)}`
  have hdomJ : ∀ ψ ∈ AsuppY C hv Y, ∀ jj, 1 ≤ jj → jj ≤ j + 1 → ∀ X,
      Def6.IsPolyDom C.m₀ jj X →
      (sfDom P6 k0 C.sf C.N₁).dom jj ((C.sf.Tm C.N₁).gs jj X) (psiJExt C hv Y ψ jj)
        (Def6.constFld (hC hv)) := by
    intro ψ hψ jj hj1 hj X hX
    have hX' : Def6.IsPolyDom P6.m₀ jj X := by rw [hm0]; exact hX
    obtain ⟨hEq, hA⟩ := psiJExt_allSites C hv Y ψ hL hν hν1 hunit hδ ht1 h3eT hμ hμBg HB hψ hj1 hj
    rw [hEq]
    have hε := hnumε jj hj1 hj
    rw [hcg] at hε
    exact xiDom_pull_of_allSites C hv hj hunit (by positivity : 0 < 4 * t) hA (hBgJ jj hj1 hj)
      ((C.sf.Tm C.N₁).gs jj X) (hTm.gs_spec jj hj1 hj X hX').2 (hratioJ jj hj1 hj)
      (by linarith) (by linarith) (by linarith)
  -- the extended lift lies in the domain of the terms `ℛ^{(k)}_n`
  have hdomR : ∀ ψ ∈ AsuppY C hv Y, Def6.XiDom (Def6.topGS S.d S.L C.N₁ m₁ (j + 1) ϱ)
      (Def6.aIdeal S.L (j + 1) (C.sf.a (j + 1)))
      (Def6.bgMass S.L (j + 1) (C.sf.β (j + 1)) (C.sf.ν (j + 1))) (j + 1)
      (P6.eps S.d S.L (j + 1)) (liftExt C hv Y ψ) (Def6.constFld (hC hv)) := by
    intro ψ hψ
    obtain ⟨hEq, hA⟩ := liftExt_allSites C hv Y ψ hL hν hν1 hunit hδ he1 hμ hψ
    rw [hEq]
    have hε := hnumε (j + 1) (by omega) le_rfl
    rw [hcg] at hε
    have hle : (2 * bgK1 S.d S.L N + 2) * (2 * (4 * e)) ≤
        (2 * bgK1 S.d S.L N + 2) * (2 * (4 * t)) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    refine xiDom_pull_of_allSites C hv le_rfl hunit (by positivity : 0 < 4 * e) hA hBgR
      (Def6.topGS S.d S.L C.N₁ m₁ (j + 1) ϱ) (fun i hi => ?_) hratioR (by linarith)
      (by linarith) (by linarith)
    simp [Def6.topGS, levelGS, show ¬ i ≤ j + 1 by omega]
  -- the inherited fields on `Y^≈` are real, of length in `(0, 2]`
  have hpsiR : ∀ ψ ∈ AsuppY C hv Y, ∀ jj, 1 ≤ jj → jj ≤ j + 1 → ∀ x ∈ C.sset (thickY R Y),
      ∃ v : Fin N → ℝ, (∀ i, C.psiJ Y ψ hv jj x i = (v i : ℂ)) ∧ 0 < rn v ∧ rn v ≤ 2 := by
    intro ψ hψ jj hj1 hj x hx
    obtain ⟨hreal, hnear⟩ :=
      psiSF_real_near C hv Y ψ hL hν hν1 hunit hδ he1 h3eT hμ hμBg HB hψ hj
    refine ⟨psiJReY C ψ hv Y hj (torusCast C.hT x),
      fun i => psiJ_eq_ofRealY C hv Y ψ hj hreal x i, ?_⟩
    have hx' : torusCast C.hT x ∈ cubeSet C (W2 R Y) :=
      (mem_sset_iff C _ x).1 (sset_mono C (thickY_subset_W2 Y) hx)
    exact rn_pos_le_two_of_near _ (fun i => hv i) hsum
      (hnear _ (mem_genSF_Ω_of_cubeSet C hj hj1 (W2 R Y) hx')) ht2
  have hslit : ∀ ψ ∈ AsuppY C hv Y, ∀ jj, 1 ≤ jj → jj ≤ j + 1 → ∀ x ∈ C.sset (thickY R Y),
      dot (C.psiJ Y ψ hv jj x) (C.psiJ Y ψ hv jj x) ∈ Complex.slitPlane := by
    intro ψ hψ jj hj1 hj x hx
    obtain ⟨v, hv1, hv0, -⟩ := hpsiR ψ hψ jj hj1 hj x hx
    have : C.psiJ Y ψ hv jj x = fun i => (v i : ℂ) := funext hv1
    rw [this]
    exact dot_real_mem_slitPlane v hv0
  -- the real background of the cut is a unit field on the fine set of `Y`
  have hphi : ∀ ψ ∈ AsuppY C hv Y, ∀ z ∈ C.bgSet Y, ∀ i, |(C.phiBar Y ψ hv z) i| ≤ 1 := by
    intro ψ hψ z hz i
    have hz' : z ∈ cubeSet C Y := by
      rw [mem_cubeSet, ← cubeMap_bgToFine C z]
      unfold SFCtx.bgSet at hz
      exact (Finset.mem_filter.1 hz).2
    exact abs_phiBarY_le_one C hv ψ Y HB (hAD hψ)
      (mem_genSF_Ω_of_cubeSet C le_rfl (by omega) (W2 R Y) (cubeSet_subset_W2 C Y hz')) i
  refine ⟨measurable_sfFactor2_of_dom C hv vc hm0 HB hTm Y hAD
    (fun jj hj1 hj => ⟨fun ψ => psiJExt C hv Y ψ jj, (continuousOn_psiJExt C hv Y HB hj).mono hAD,
      fun ψ hψ => ⟨fun x hx => psiJExt_eq_of_mem C hv Y ψ hx,
        fun X hX _ => hdomJ ψ hψ jj hj1 hj X hX⟩⟩)
    hslit g (l1_sfG_lt_one C g hgl) hRt
    ⟨fun ψ => liftExt C hv Y ψ, (continuous_liftExt C hv Y).continuousOn,
      fun ψ hψ => ⟨fun x hx => liftExt_eq_of_mem C hv Y ψ hx, hdomR ψ hψ⟩⟩
    (hμ.trans hμBg.symm), ?_⟩
  exact exists_bound_sfFactor2_of_dom C hv vc hm0 hTm Y
    (fun jj hj1 hj ψ hψ => ⟨psiJExt C hv Y ψ jj, fun x hx => psiJExt_eq_of_mem C hv Y ψ hx,
      fun X hX _ => hdomJ ψ hψ jj hj1 hj X hX⟩)
    hpsiR g hgl HB hL hact hβ hphi hRt
    (fun ψ hψ => ⟨liftExt C hv Y ψ, fun x hx => liftExt_eq_of_mem C hv Y ψ hx, hdomR ψ hψ⟩)

end Ctx

end Balaban.RootFSpine
