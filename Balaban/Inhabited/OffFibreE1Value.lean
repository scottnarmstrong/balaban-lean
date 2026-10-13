/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.OffFibreE1Compare

/-!
# First-energy parameter marks at a free datum

The parameter marks agree with the localized derivative of the raw first exponent.
-/

@[expose] public section
namespace Balaban.Inhabited

open Balaban Balaban.Fluctuation Balaban.Multiscale Balaban.Background Balaban.Localization
  Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited Balaban.Polymer
  Balaban.SmallField Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep Matrix Metric Set
  Filter Topology

open Classical in
/-- At every chart datum, the E1 parameter marks equal the localized derivative of the
raw first exponent. The incoming field may vary across the block. -/
theorem e1_param_marks_eq_raw_deriv {κmin : ℝ} (T : StepTower κmin)
    {k : ℕ} {hk : 1 ≤ k} {N₁ : ℕ} [NeZero N₁] {ν β p₁ pp : ℝ}
    (Dt : StepScaleData T k hk N₁ ν β p₁)
    (S : StepSetting 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁))
    (hS : S = T.step k hk N₁ ν β p₁) (Jr : S.JointRep T.t pp)
    (hp : 0 < S.p₁) (hlt : S.p₁ < pp)
    {BG κdec : ℝ}
    (F₁ : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) →
      DecParams S.G' × RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 →
        (S.G'.Ω 1 × Fin 2 → ℂ) × (S.G'.Ω 1 → ℂ))
    (Sol : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf S.G') × Edat (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) 2 →
        ((stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)).Ω 1 × Fin 2 → ℂ) ×
          ((stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)).Ω 1 → ℂ))
    (z : RootIdx 3 3 N₁ T.m₁ (k + 1))
    (hP : ∀ b, MarkedBlockExpansionDecPair 2
      (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) S.hG'
      ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) S.a₁ S.ν BG T.BG₂ T.κ T.t T.t κdec p₁
      (S.blockU z) (LocalCover.nbhdF 1 (LocalCover.blockSite k b)) 1 k
      (LocalCover.fam 1 (LocalCover.blockSite k b)) b (F₁ b) (Sol b))
    (D : BgData S.G' 2) (hX : XiCData S.G' S.a S.ν (k + 1) 1 T.t D)
    (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) (x : S.E) (hx : ‖x‖ ≤ p₁) :
    ∑ i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1Dom S) z},
      e1MarkGParam S F₁ Sol p₁ hp z T.t
        ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub 2 S.G'),
          (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) i (s : ℂ)
        ((S.blockSplit 1 hp).restr x) =
      (fderiv ℂ (fun w : S.EC =>
        Jr.W1 (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) (rawOf D, w))
        ((s : ℂ) • yhat x))
        ((Jr.Mx (rawOf D))⁻¹ *ᵥ S.maskUC z (Jr.Mx (rawOf D) *ᵥ yhat x)) := by
  subst hS
  let S := T.step k hk N₁ ν β p₁
  let a : S.EC := yhat x
  let b : S.EC := (hatCovSqrt S.G' S.a₁ S.ν D)⁻¹ *ᵥ
    S.maskUC z (hatCovSqrt S.G' S.a₁ S.ν D *ᵥ a)
  let y : S.EC := S.hatField (hatCovSqrt S.G' S.a₁ S.ν D) a
  let e : ℂ × ℂ → ℂ := fun w =>
    ∑ b' : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))),
      blockEnergyOne S.G' (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) S.a₁ S.ν
        T.BG₂ T.κ T.t k b'
        (rawOf D, liftC S.hG' (w.1 • y + w.2 • S.maskUC z y))
  let f : ℂ → ℂ := fun u => deriv (fun t : ℂ => e (u, t)) 0
  have hRpos := Dt.r_pos
  have hdisc : ∀ u : ℂ, ‖u‖ < 17 / 16 → ∀ t : ℂ, ‖t‖ < 1 / 16 →
      liftC S.hG' (S.hatField (hatCovSqrt S.G' S.a₁ S.ν D) (u • a + t • b)) ∈
        FlBall (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) T.t := by
    intro u hu t ht
    have hd := markReal_disc_slice_raw T Dt hp D hX x hx z hu t ht 1 (by
      rw [norm_one]
      linarith)
    have hm := Jr.hatField_marked_raw Dt.core T.large_block T.dom_margin
      T.coer_margin T.δc_small D hX z x u t
    dsimp only at hm
    rw [Jr.Mx_eq D hX] at hm
    have hm' : S.hatField (hatCovSqrt S.G' S.a₁ S.ν D) (u • a + t • b) =
        u • y + t • S.maskUC z y := hm
    have htransport : liftC S.hG' (u • y + t • S.maskUC z y) =
        liftC S.hG' (u • y) + t • liftC S.hG' (S.maskUC z y) := by
      calc
        _ = liftC S.hG' (u • y) + liftC S.hG' (t • S.maskUC z y) := by rw [map_add]
        _ = _ := congrArg (fun w => liftC S.hG' (u • y) + w) (by rw [map_smul])
    rw [hm', htransport]
    simpa only [one_smul] using hd
  have hD2 : InUnionDomainC S.G' (bgC0 3 3 2) (thm73C2 3 3 2) S.ν D :=
    (isDecBg_one_of_xiCData Dt.core hX).2.mono
      (T.c7_cap.trans (thm73C3_le_thm73C2 3 3 2))
  have hspp : ‖(s : ℂ) • a‖ < pp := by
    have hs1 : |s| ≤ 1 := by rw [abs_of_nonneg hs.1]; exact hs.2
    calc
      ‖(s : ℂ) • a‖ ≤ |s| * ‖x‖ :=
        StepSetting.JointRep.norm_smul_yhat_le (S := S) s x
      _ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right hs1 (norm_nonneg _)
      _ ≤ p₁ := by simpa using hx
      _ < pp := hlt
  have hsm : ‖(s : ℂ)‖ < 17 / 16 := by
    rw [Complex.norm_real, Real.norm_of_nonneg hs.1]
    linarith [hs.2]
  have hcore := Jr.blockEnergy_mark_taylor_eq_fderiv_W1_raw Dt.core one_pos
    T.c7_cap (R := 2) (by norm_num) T.bg1_cap T.t_cap T.bg0_cap
    T.cK2_cap T.cK2'_cap D hX hD2 (hp.trans hlt) a b
    (U := 17 / 16) (V := 1 / 16) (by norm_num) (by norm_num) hdisc
    (s : ℂ) hsm hspp
  let ec : ℂ × ℂ → ℂ := fun w =>
    ∑ b' : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))),
      blockEnergyOne S.G' (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) S.a₁ S.ν
        T.BG₂ T.κ T.t k b'
        (rawOf D, liftC S.hG' (S.hatField (hatCovSqrt S.G' S.a₁ S.ν D)
          (w.1 • a + w.2 • b)))
  let fc : ℂ → ℂ := fun u => deriv (fun t : ℂ => ec (u, t)) 0
  have hef : f = fc := by
    funext u
    apply congrArg (fun g : ℂ → ℂ => deriv g 0)
    funext t
    have hm := Jr.hatField_marked_raw Dt.core T.large_block T.dom_margin
      T.coer_margin T.δc_small D hX z x u t
    dsimp only at hm
    rw [Jr.Mx_eq D hX] at hm
    have hm' : S.hatField (hatCovSqrt S.G' S.a₁ S.ν D) (u • a + t • b) =
        u • y + t • S.maskUC z y := hm
    dsimp only [e, ec]
    rw [hm']
  dsimp only at hcore
  change -(S.β : ℂ) * (fc (s : ℂ) - fc 0 - (s : ℂ) * deriv fc 0) = _ at hcore
  rw [← hef] at hcore
  have hxcoord : ∀ q, ‖x q‖ ≤ p₁ :=
    fun q => (norm_le_pi_norm x q).trans hx
  let G : ℂ → ℂ := fun u => ∑ b', ∑ Y ∈ e1Dom S b',
    decMarkG S (LocalCover.nbhdF 1 (LocalCover.blockSite k b')) 1 k
      (LocalCover.fam 1 (LocalCover.blockSite k b')) S.a₁ S.ν
      ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁ b') (Sol b')
      (blockEnergyFun S.G' (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) S.a S.ν k b')
      (S.blockU z) Y p₁ hp (rawOf D) u ((S.blockSplit 1 hp).restr x)
  have hGf (u : ℂ) (hu : ‖u‖ < 17 / 16) : G u = f u := by
    have hrad := markedRad_slice_lt_fromTower T Dt hp hu.le
    have hraw := S.sum_decMarkG_eq_deriv_blockEnergyOne_raw
      (X₁V := fun b' => LocalCover.nbhdF 1 (LocalCover.blockSite k b'))
      (jV := fun _ => k) (𝒦XV := fun b' => LocalCover.fam 1 (LocalCover.blockSite k b'))
      (m₀ := 1) z F₁ Sol hP hp le_rfl hp D hX x hxcoord hrad
    unfold G f e e1Dom
    exact hraw
  have hGfn : G =ᶠ[𝓝 0] f := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 17 / 16)]
      with u hu
    exact hGf u (by simpa using hu)
  have hT := e1_param_marks_taylor_raw T Dt rfl hp F₁ Sol z hP D hX s hs x
  have htf := taylor1_remainder_congr hGfn (hGf (s : ℂ) hsm)
  dsimp only at hT hcore
  rw [hT, htf]
  rw [Jr.Mx_eq D hX]
  exact hcore

end Balaban.Inhabited
