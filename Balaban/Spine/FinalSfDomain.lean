/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.FinalSfBound
public import Balaban.LargeField.R.PsiZeroBlocks
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The domain facts on the `χ`-support

A6-3 (a), item 1: from the level-`k` real domain of the datum on the support of `χ_k(univ)`
(`inPsiTilde_genW_univ_late`) the facts used by the measurability and the boundedness of
`sfFactor2`: the datum is in the real domain `𝒟_ℝ` (`DomSet`), the real background `φ̄_k` is a unit
field, and the block field is bounded.
-/

@[expose] public section

open MeasureTheory Balaban Balaban.Multiscale Balaban.Background Balaban.LargeField
  Balaban.LargeField.Def7 Balaban.LargeField.Def7v2 Balaban.SmallField Balaban.SmallField.Def6
  Balaban.SmallField.Def6v2 Balaban.Localization

namespace Balaban.RootFSpine

section Consts

variable (d L N : ℕ) [NeZero L]

/-- The constant `Γ = (2 K₁ + 2) · 2 C₄ K₁ · 4 (d + 1)`: the radii of the domain transport are
`Γ δ_k` times fixed numbers. -/
noncomputable def gammaConst : ℝ :=
  (2 * bgK1 d L N + 2) * 2 * compC4 d * bgK1 d L N * 4 * ((d : ℝ) + 1)

/-- The cap `min (1, thm73C1, c₀)` on the radii. -/
noncomputable def deltaCap : ℝ := min (min 1 (thm73C1 d L N)) (bgC0 d L N)

theorem gammaConst_pos : 0 < gammaConst d L N := by
  unfold gammaConst
  have := bgK1_ge_one d L N
  have := compC4_ge d
  positivity

theorem deltaCap_pos (hd : 0 < d) : 0 < deltaCap d L N := by
  unfold deltaCap thm73C1
  have h1 := bgC1_pos_of (L := L) (N := N) hd
  have h2 := bgC0_pos (L := L) (N := N) d hd
  have h3 := bgK1_ge_one d L N
  have h4 := compC4_ge d
  exact lt_min (lt_min one_pos (by positivity)) h2

end Consts

section Ctx

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N m₁ j : ℕ} {ϱ : ℝ} (C : SFCtx S n R M K N (j + 1) m₁ ϱ)
  (hv : EuclideanSpace ℝ (Fin N))
  (ψk : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N))

/-- The datum is in the real domain `𝒟_ℝ` when the field is in the data domain `Ψ̃`. -/
theorem mem_DomSet_of_inPsiTilde {m η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ bgC1 S.d S.L N)
    (hP : InPsiTilde (C.genW (Set.univ : Set (Torus S.d (n (j + 1))))) m η (parentPsi C ψk)
      (fun i => hv i)) : ψk ∈ DomSet C hv m :=
  ⟨η, hη0, hη1, parentPsi C ψk, fun i => hv i, hP,
    fun x hx i => liftSingle_Ψ_eq_parentPsi C _ ψk hv hx i,
    fun x hx i => by unfold Dfam; rw [liftSingle_h _ _ _ hx]; rfl⟩

/-- **The real background `φ̄_k` is a unit field** on the domain (coordinates of modulus `≤ 1`). -/
theorem abs_phiBar_le_one
    (HB : BgHyp S.d S.L (j + 1) (minSep S.L C.geo.M1) C.weights (C.cs.muBg (j + 1)))
    (hψ : ψk ∈ DomSet C hv (C.cs.muBg (j + 1))) (z : BgT C.geo (j + 1)) (i : Fin N) :
    |(C.phiBar (Set.univ : Set (Torus S.d (n (j + 1)))) ψk hv z) i| ≤ 1 := by
  obtain ⟨δ, hδ0, hδc, hD⟩ := hψ
  obtain ⟨φ, α, hs, hb, hu, hunit, -, -⟩ := bg_real HB hδ0 hδc hD
  obtain ⟨hfC, -⟩ := bgFieldC_eq hs hu
  have hz : z ∈ (C.genW (Set.univ : Set (Torus S.d (n (j + 1))))).Ω 1 := by
    rw [genW_Ω_univ C (by omega)]; exact Finset.mem_univ _
  have hphiK : C.phiK (Set.univ : Set (Torus S.d (n (j + 1)))) ψk hv = φ := hfC
  have key : (C.phiBar (Set.univ : Set (Torus S.d (n (j + 1)))) ψk hv z) i =
      (φ (⟨z, hz⟩, i)).re := by
    show (barField (C.genW (Set.univ : Set (Torus S.d (n (j + 1))))) (Dfam C hv ψk).Ψ
      (C.phiK (Set.univ : Set (Torus S.d (n (j + 1)))) ψk hv) z i).re = _
    rw [hphiK]
    simp [barField, hz]
  rw [key]
  have h1 := hunit ⟨z, hz⟩
  have h2 : ‖φ (⟨z, hz⟩, i)‖ ^ 2 ≤ 1 := by
    rw [← h1.2]
    exact Finset.single_le_sum (f := fun i => ‖φ (⟨z, hz⟩, i)‖ ^ 2) (fun _ _ => sq_nonneg _)
      (Finset.mem_univ i)
  have h3 : ‖φ (⟨z, hz⟩, i)‖ ≤ 1 := by nlinarith [norm_nonneg (φ (⟨z, hz⟩, i))]
  exact (Complex.abs_re_le_norm _).trans h3

/-- **A block field in the data domain is bounded**: `‖ψ_k(b)‖ ≤ 2` for `η ≤ 1`. -/
theorem norm_le_two_of_inPsiTilde {m η : ℝ} (hη1 : η ≤ 1)
    (hP : InPsiTilde (C.genW (Set.univ : Set (Torus S.d (n (j + 1))))) m η (parentPsi C ψk)
      (fun i => hv i)) (b : BlockAt S n M K (j + 1)) : ‖ψk b‖ ≤ 2 := by
  obtain ⟨y0, hy0⟩ : ∃ y0, blkToBlock C.geo C.hnn C.hkK y0 = b :=
    (torusCast_surjective' _) b
  obtain ⟨x, hx⟩ := Balaban.exists_blockMap_eq (fine_eq_block S.L (C.geo.M1 * (C.geo.c * n (j + 1)))
    (j + 1)) (pow_pos (Nat.pos_of_ne_zero (NeZero.ne S.L)) (j + 1)) y0
  have hx' : jBlock S.d S.L (C.geo.M1 * (C.geo.c * n (j + 1))) (j + 1) (j + 1) x = y0 := hx
  have hxd : x ∈ dataSites (C.genW (Set.univ : Set (Torus S.d (n (j + 1))))) := by
    refine (mem_dataSites _).2 (Or.inl ?_)
    rw [genW_Ω_univ C (by omega)]; exact Finset.mem_univ _
  have h2 := hP.r2 x hxd
  have e : parentPsi C ψk x = fun i => ψk b i := by
    funext i
    unfold parentPsi
    rw [hx', hy0]
  rw [e] at h2
  have h3 : ∑ i, ψk b i ^ 2 = ‖ψk b‖ ^ 2 := parent_sum_sq_eq_norm_sq (ψk b)
  rw [h3] at h2
  have h4 := (abs_lt.1 h2).2
  nlinarith [norm_nonneg (ψk b)]

/-- The numerical hypotheses of the domain transport (radii against the tolerance):
`t = 4 (d+1) δ_k`, the child radius `η_c = C₄ K₁ t`. -/
theorem parent_of_mem_Asupp (hL : 2 ≤ S.L) {ν : ℝ} (hν : 0 < ν) (hunit : ‖hv‖ = 1)
    (hδ : 0 < C.cs.delta (j + 1)) (hδ1 : (S.d + 1) * C.cs.delta (j + 1) ≤ 1)
    (hμ : C.cs.mu (j + 1) = sfBgMassAt S.L (j + 1) ν)
    (hμBg : C.cs.muBg (j + 1) = sfBgMassAt S.L (j + 1) ν)
    (HB : BgHyp S.d S.L (j + 1) (minSep S.L C.geo.M1) C.weights (C.cs.muBg (j + 1)))
    (hψ : ψk ∈ Asupp C hv) :
    InPsiTilde (C.genW (Set.univ : Set (Torus S.d (n (j + 1)))))
      (sfBgMassAt S.L (j + 1) ν) (4 * (S.d + 1) * C.cs.delta (j + 1)) (parentPsi C ψk)
      (fun i => hv i) := by
  have HBmu : BgHyp S.d S.L (j + 1) (minSep S.L C.geo.M1) C.weights (C.cs.mu (j + 1)) := by
    rw [hμ, ← hμBg]; exact HB
  exact inPsiTilde_genW_univ_late C ψk hv hL hν hunit hδ hδ1 hμ hψ HBmu

/-- On the support of `χ_k(univ)` the tolerance is positive. -/
theorem delta_pos_of_mem_Asupp (hL : 2 ≤ S.L) {ν : ℝ} (hν : 0 < ν)
    (hμ : C.cs.mu (j + 1) = sfBgMassAt S.L (j + 1) ν) (hψ : ψk ∈ Asupp C hv) :
    0 < C.cs.delta (j + 1) := by
  obtain ⟨s, hs⟩ := exists_tested_site C (Set.univ : Set (Torus S.d (n (j + 1)))) (Set.mem_univ _)
  have hdir := parentPsi_dir_of_chiY_ne_zero C hL (Set.univ : Set (Torus S.d (n (j + 1)))) ψk hv
    hψ hν hμ (testedSites_subset_dataSites C _ hs)
  have h0 : 0 < C.cs.delta (j + 1) / Real.sqrt ν := lt_of_le_of_lt (rn_nonneg _) hdir
  exact (div_pos_iff_of_pos_right (Real.sqrt_pos.2 hν)).1 h0

/-- If the tolerance is not positive, the small-field factor of the whole torus vanishes. -/
theorem sfFactor2_univ_eq_zero_of_not_pos (vc : CorrCoef S.d) (g : GIdx S n M K N → ℂ)
    (hL2 : 2 ≤ S.L) {ν : ℝ} (hν : 0 < ν)
    (hμ : C.cs.mu (j + 1) = sfBgMassAt S.L (j + 1) ν) (hpos : ¬ 0 < C.cs.delta (j + 1)) :
    (fun ψk : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N) =>
      sfFactor2 C vc (Set.univ : Set (Torus S.d (n (j + 1)))) ψk hv g) = fun _ => 0 := by
  funext ψk
  have h0 : C.chiY (Set.univ : Set (Torus S.d (n (j + 1)))) ψk hv = 0 := by
    by_contra hne
    exact hpos (delta_pos_of_mem_Asupp C hv ψk hL2 hν hμ hne)
  unfold sfFactor2
  rw [h0]; simp

variable {P6 : Def6.Consts} {k0 : ℕ}

/-- **`sfFactor2` of the whole torus is integrable, from the numerical smallness of the tolerance**
(A6-3 (a), item 1). The hypotheses are: the class clauses (the term clauses `hTm`, the remainder
clauses `hRt`), the standing hypotheses `BgHyp` of the background theory at the cube level and at the
birth masses of the inherited levels, the cube mass equal to the physical mass at the scale `k`,
and the smallness of the tolerance `δ_k` against the radii (`hη`, `hc0`, `h1`, `hε`). -/
theorem measInt_sfFactor2_univ_of_numerics (vc : CorrCoef S.d)
    (hm0 : P6.m₀ = C.m₀) (hTm : SFTermClauses P6 (sfDom P6 k0 C.sf C.N₁) (C.sf.Tm C.N₁))
    {fac : ℕ → ℝ} (hRt : RTermsH4 (ϱ := ϱ) P6 C.sf.β C.sf.ν C.sf.a C.N₁ (C.sf.Rt C.N₁) fac)
    (g : GIdx S n M K N → ℂ) (hgl : g ∈ LargeField.l1Ball (GIdx S n M K N))
    (HB : BgHyp S.d S.L (j + 1) (minSep S.L C.geo.M1) C.weights (C.cs.muBg (j + 1)))
    (hL : 3 ≤ S.L) {ν : ℝ} (hν : 0 < ν) (hunit : ‖hv‖ = 1)
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
    (hδ1 : (S.d + 1) * C.cs.delta (j + 1) ≤ 1)
    (hη : 4 * (S.d + 1) * C.cs.delta (j + 1) ≤ thm73C1 S.d S.L N)
    (hc0 : 2 * (compC4 S.d * (bgK1 S.d S.L N * (4 * (S.d + 1) * C.cs.delta (j + 1)))) ≤
      bgC0 S.d S.L N)
    (h1 : 2 * (compC4 S.d * (bgK1 S.d S.L N * (4 * (S.d + 1) * C.cs.delta (j + 1)))) ≤ 1)
    (hε : ∀ jj, 1 ≤ jj → jj ≤ j + 1 → (2 * bgK1 S.d S.L N + 2) *
      (2 * (compC4 S.d * (bgK1 S.d S.L N * (4 * (S.d + 1) * C.cs.delta (j + 1))))) ≤
        P6.eps S.d S.L jj) :
    Measurable (fun ψk : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N) =>
      sfFactor2 C vc (Set.univ : Set (Torus S.d (n (j + 1)))) ψk hv g) ∧
    Integrable fun ψk : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N) =>
      sfFactor2 C vc (Set.univ : Set (Torus S.d (n (j + 1)))) ψk hv g := by
  classical
  have hL2 : 2 ≤ S.L := by omega
  by_cases hpos : 0 < C.cs.delta (j + 1)
  swap
  · rw [sfFactor2_univ_eq_zero_of_not_pos C hv vc g hL2 hν hμ hpos]
    exact ⟨measurable_const, integrable_zero _ _ _⟩
  have hd0 : 0 < S.d := by have := HB.hd; omega
  have hK1 := bgK1_ge_one S.d S.L N
  have hC4 := compC4_ge S.d
  have hd0r : (0 : ℝ) < S.d := by exact_mod_cast hd0
  set t : ℝ := 4 * ((S.d : ℝ) + 1) * C.cs.delta (j + 1) with ht
  have ht0 : 0 < t := by rw [ht]; positivity
  set ηc : ℝ := compC4 S.d * (bgK1 S.d S.L N * t) with hηc
  have hηc0 : 0 < ηc := by rw [hηc]; positivity
  have htη : t ≤ ηc := by
    rw [hηc]
    have : 1 ≤ compC4 S.d * bgK1 S.d S.L N := by nlinarith
    nlinarith
  obtain ⟨hsm1, hsm2, -, -, -⟩ := thm73_small (L := S.L) (N := N) hd0 ht0 hη
  have hAD : Asupp C hv ⊆ DomSet C hv (C.cs.muBg (j + 1)) := by
    intro ψ hψ
    have hP := parent_of_mem_Asupp C hv ψ hL2 hν hunit hpos hδ1 hμ hμBg HB hψ
    rw [hμBg]
    exact mem_DomSet_of_inPsiTilde C hv ψ ht0 hsm1 hP
  have hparent : ∀ ψ ∈ Asupp C hv, InPsiTilde (C.genW (Set.univ : Set (Torus S.d (n (j + 1)))))
      (sfBgMassAt S.L (j + 1) ν) t (parentPsi C ψ) (fun i => hv i) :=
    fun ψ hψ => parent_of_mem_Asupp C hv ψ hL2 hν hunit hpos hδ1 hμ hμBg HB hψ
  have hpsiR : ∀ ψk ∈ Asupp C hv, ∀ jj, 1 ≤ jj → jj ≤ j + 1 →
      ∀ x : Localization.CTorus S.d S.L C.N₁ m₁ (j + 1), ∃ v : Fin N → ℝ,
        (∀ i, C.psiJ (Set.univ : Set (Torus S.d (n (j + 1)))) ψk hv jj x i = (v i : ℂ)) ∧
          0 < rn v ∧ rn v ≤ 2 := by
    intro ψ hψ jj hj1 hj x
    obtain ⟨hreal, hA⟩ := psiJ_allSites C ψ hv hj1 hj hL hν hunit hpos hδ1 hμ hμBg hψ HB hη
    refine ⟨fun i => psiJRe C ψ hv hj (torusCast C.hT x) i, fun i => ?_, ?_⟩
    · exact psiJ_eq_ofReal C hv ψ hj hreal x i
    · have hs := hA.sphere (torusCast C.hT x)
      have hsq : rn (fun i => psiJRe C ψ hv hj (torusCast C.hT x) i) ^ 2 =
          ∑ i, psiJRe C ψ hv hj (torusCast C.hT x) i ^ 2 := rn_sq _
      have hb := abs_lt.1 hs
      have hrn := rn_nonneg (fun i => psiJRe C ψ hv hj (torusCast C.hT x) i)
      refine ⟨?_, ?_⟩
      · by_contra hle
        have : rn (fun i => psiJRe C ψ hv hj (torusCast C.hT x) i) = 0 := le_antisymm (not_lt.1 hle) hrn
        rw [this] at hsq
        nlinarith [hb.1]
      · nlinarith [hb.2]
  have hdomJ : ∀ ψk ∈ Asupp C hv, ∀ jj, 1 ≤ jj → jj ≤ j + 1 → ∀ X, Def6.IsPolyDom C.m₀ jj X →
      (sfDom P6 k0 C.sf C.N₁).dom jj ((C.sf.Tm C.N₁).gs jj X)
        (C.psiJ (Set.univ : Set (Torus S.d (n (j + 1)))) ψk hv jj) (Def6.constFld (hC hv)) := by
    intro ψ hψ jj hj1 hj X hX
    have hX' : Def6.IsPolyDom P6.m₀ jj X := by rw [hm0]; exact hX
    exact psiJ_xiDom C ψ hv hj1 hj hL hν hunit hpos hδ1 hμ hμBg hψ HB hη (hBgJ jj hj1 hj)
      ((C.sf.Tm C.N₁).gs jj X) (hTm.gs_spec jj hj1 hj X hX').2 (hratioJ jj hj1 hj) hc0 hsm2
      (hε jj hj1 hj)
  have hdomR : ∀ ψk ∈ Asupp C hv, Def6.XiDom (Def6.topGS S.d S.L C.N₁ m₁ (j + 1) ϱ)
      (Def6.aIdeal S.L (j + 1) (C.sf.a (j + 1)))
      (Def6.bgMass S.L (j + 1) (C.sf.β (j + 1)) (C.sf.ν (j + 1))) (j + 1)
      (P6.eps S.d S.L (j + 1)) (sfLiftK C.geo C.hnn C.hkK C.hT ψk) (Def6.constFld (hC hv)) := by
    intro ψ hψ
    refine sfLiftK_xiDom C ψ hv hL hν hunit hpos hδ1 hμ hμBg hψ HB hBgR
      (Def6.topGS S.d S.L C.N₁ m₁ (j + 1) ϱ) (fun i hi => ?_) hratioR (by linarith) (by linarith)
      ((mul_le_mul_of_nonneg_left (by linarith) (by positivity)).trans (hε (j + 1) (by omega) le_rfl))
    simp [Def6.topGS, levelGS, show ¬ i ≤ j + 1 by omega]
  exact measInt_sfFactor2_univ_of_dom C hv vc hm0 hTm hdomJ hpsiR g hgl HB hL2 hact hβ hAD
    (fun ψ hψ z i => abs_phiBar_le_one C hv ψ HB (hAD hψ) z i)
    (fun ψ hψ b => norm_le_two_of_inPsiTilde C hv ψ (htη.trans (by linarith)) (hparent ψ hψ) b)
    hRt hdomR (hμ.trans hμBg.symm)

/-- **`sfFactor2` of the whole torus is integrable, from `Γ δ_k ≤ min (c, ε_j)`** (A6-3 (a), item 1;
`gammaConst`, `deltaCap`): the single smallness condition on the tolerance against the radii
`ε_j`, `1 ≤ j ≤ k`. -/
theorem measInt_sfFactor2_univ_of_delta_le (vc : CorrCoef S.d)
    (hm0 : P6.m₀ = C.m₀) (hTm : SFTermClauses P6 (sfDom P6 k0 C.sf C.N₁) (C.sf.Tm C.N₁))
    {fac : ℕ → ℝ} (hRt : RTermsH4 (ϱ := ϱ) P6 C.sf.β C.sf.ν C.sf.a C.N₁ (C.sf.Rt C.N₁) fac)
    (g : GIdx S n M K N → ℂ) (hgl : g ∈ LargeField.l1Ball (GIdx S n M K N))
    (HB : BgHyp S.d S.L (j + 1) (minSep S.L C.geo.M1) C.weights (C.cs.muBg (j + 1)))
    (hL : 3 ≤ S.L) {ν : ℝ} (hν : 0 < ν) (hunit : ‖hv‖ = 1)
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
    (hnum : gammaConst S.d S.L N * C.cs.delta (j + 1) ≤ deltaCap S.d S.L N)
    (hnumε : ∀ jj, 1 ≤ jj → jj ≤ j + 1 →
      gammaConst S.d S.L N * C.cs.delta (j + 1) ≤ P6.eps S.d S.L jj) :
    Measurable (fun ψk : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N) =>
      sfFactor2 C vc (Set.univ : Set (Torus S.d (n (j + 1)))) ψk hv g) ∧
    Integrable fun ψk : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N) =>
      sfFactor2 C vc (Set.univ : Set (Torus S.d (n (j + 1)))) ψk hv g := by
  have hd0 : 0 < S.d := by have := HB.hd; omega
  have hK1 := bgK1_ge_one S.d S.L N
  have hC4 := compC4_ge S.d
  have hd0r : (0 : ℝ) < S.d := by exact_mod_cast hd0
  have hΓ : gammaConst S.d S.L N * C.cs.delta (j + 1) =
      (2 * bgK1 S.d S.L N + 2) *
        (2 * (compC4 S.d * (bgK1 S.d S.L N * (4 * (S.d + 1) * C.cs.delta (j + 1))))) := by
    unfold gammaConst; ring
  have hcap1 : deltaCap S.d S.L N ≤ 1 :=
    (min_le_left _ _).trans (min_le_left _ _)
  have hcapη : deltaCap S.d S.L N ≤ thm73C1 S.d S.L N :=
    (min_le_left _ _).trans (min_le_right _ _)
  have hcap0 : deltaCap S.d S.L N ≤ bgC0 S.d S.L N := min_le_right _ _
  by_cases hpos : 0 < C.cs.delta (j + 1)
  · have hΓpos := gammaConst_pos S.d S.L N
    have hone : 4 * ((S.d : ℝ) + 1) * C.cs.delta (j + 1) ≤
        gammaConst S.d S.L N * C.cs.delta (j + 1) := by
      refine mul_le_mul_of_nonneg_right ?_ hpos.le
      unfold gammaConst
      have : 1 ≤ (2 * bgK1 S.d S.L N + 2) * 2 * compC4 S.d * bgK1 S.d S.L N := by
        have h1 : 1 ≤ 2 * bgK1 S.d S.L N + 2 := by linarith
        have h2 : 1 ≤ compC4 S.d := by linarith
        have : 1 ≤ (2 * bgK1 S.d S.L N + 2) * 2 := by linarith
        have := mul_le_mul this h2 zero_le_one (by linarith)
        have := mul_le_mul this hK1 zero_le_one (by positivity)
        nlinarith
      nlinarith [mul_pos hd0r hd0r]
    have h2η : 2 * (compC4 S.d * (bgK1 S.d S.L N * (4 * (S.d + 1) * C.cs.delta (j + 1)))) ≤
        gammaConst S.d S.L N * C.cs.delta (j + 1) := by
      rw [hΓ]
      have h0 : 0 ≤ 2 * (compC4 S.d * (bgK1 S.d S.L N * (4 * (S.d + 1) * C.cs.delta (j + 1)))) := by
        positivity
      nlinarith
    refine measInt_sfFactor2_univ_of_numerics C hv vc hm0 hTm hRt g hgl HB hL hν hunit hμ hμBg
      hact hβ hBgJ hratioJ hBgR hratioR ?_ ?_ ?_ ?_ ?_
    · have : (S.d + 1) * C.cs.delta (j + 1) ≤ 4 * ((S.d : ℝ) + 1) * C.cs.delta (j + 1) := by
        nlinarith [mul_pos hd0r hpos]
      linarith
    · linarith
    · linarith
    · linarith
    · intro jj hj1 hj
      rw [← hΓ]; exact hnumε jj hj1 hj
  · rw [sfFactor2_univ_eq_zero_of_not_pos C hv vc g (by omega) hν hμ hpos]
    exact ⟨measurable_const, integrable_zero _ _ _⟩

end Ctx

end Balaban.RootFSpine
