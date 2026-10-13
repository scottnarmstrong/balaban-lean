/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.ObsCoeffLocal
public import Balaban.Fluctuation.RawAgreeSites

/-!
# Exact locality of the observable coefficient on the sites of the cluster

`obsCoeffParam_local_of_Ev_rawY`: the coefficient `obsCoeffParam … θ T'` depends on the parameter
`θ` only through the raw datum and the source on the set `sitesOf T'` itself.  The kernel and the
remainder marks are controlled by the sharp locality clause of `Ev` (raw data agreeing on `Y`
itself, hat variables agreeing at the unit points of `Y`); the activity of the labels is an
explicit hypothesis in the exact form (raw datum and source agreeing on the set of the labels).

`obsCoeffParam_local_of_Ev_physRestrict`: the same conclusion from equality of the restrictions
`physRestrict (sitesOf T') (physIncl 2 S ·)`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep MeasureTheory Metric

section TowerG

variable {d L N : ℕ} [NeZero L] {κmin : ℝ} (T : StepTowerG d L N κmin) (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁]
  (ν β p₁ : ℝ) (Dsc : StepScaleDataG T k hk N₁ ν β p₁)
  {ϱ : ℝ} (S : StepSetting d L N₁ T.m₁ k N ϱ) (hS : S = hatStepKG T.hN k T.m₁ ϱ hk ν β p₁ T.δ)
  (hp : 0 < S.p₁) (y : CTorus d L N₁ T.m₁ (k + 1)) (h3N : L ^ T.m₀ ∣ N₁)
  {Lb : Type} [Fintype Lb]
  (Lab : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) T.m₀ (k + 1)
    Set.univ Lb) {εH : ℝ} (hεH : 0 < εH) {Kc : ℝ}
  (Aact : physParam N S → ℂ → LabelAct Lab (S.blockSplit T.m₀ hp).Ωb εH (2 * T.κdec - 1) T.κ0 Kc)
  (hdj : ∀ Y ∈ obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y), IsDj T.m₀ (k + 1) Y)
  {Kobs : ℝ} (hK : Kc + Kc + K0 d L T.κ0 + K0 d L T.κ0 ≤ Kobs) (Rg : ℝ) (hR : 0 ≤ Rg)
  (Ev : Set (CTorus d L N₁ T.m₁ (k + 1)) →
    RawData d L (N₁ * L ^ T.m₁) (k + 1) N × (unitPts S.G' × Fin N → ℂ) → ℂ)

include Dsc hS in
/-- General tower `T : StepTowerG d L N κmin` (block scale `T.m₀`, `b = β L^{k (d-2)}`); the fixed theorem `obsCoeffParam_local_of_Ev_rawY` is its corollary.  **Exact locality of the observable coefficient at the tower.**  Let `Ev` be local in the sharp
form (clause `hd` of `obsEv_fromTower_rawY`) and let the activity `Aact` of the family of labels be
local in the exact form: for `e, e'` of `physVq` whose raw data agree on `Z` itself and whose
sources agree on `Z`, the activities of the labels with sites in `Z` agree, at the parameters
`(e.1, 0), (e'.1, 0)` and at `e, e'`.  Then for `θ, θ'` of `physVq` whose raw data agree on
`sitesOf T'` and whose sources agree on `sitesOf T'`, the coefficients agree.  The kernel entries
and remainder marks read the raw datum on `sitesOf T'` through `hd`; the datum enters the proof of
the analyticity and the value of the remainder marks only through the thick clause, which is not
a hypothesis here. -/
theorem obsCoeffParam_local_of_Ev_rawYG {q : ℝ}
    (hAloc : ∀ e ∈ physVq S S.a₁ S.ν T.t q, ∀ e' ∈ physVq S S.a₁ S.ν T.t q,
      ∀ Z : Set (CTorus d L N₁ T.m₁ (k + 1)),
      agreeOn Z (e.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N)
        (e'.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N) → (∀ x ∈ Z, e.2 x = e'.2 x) →
      ∀ (u : ℂ) (w : Lb), Lab.ysite w ⊆ Z →
        (Aact ((e.1, 0) : physParam N S) u).H w = (Aact ((e'.1, 0) : physParam N S) u).H w ∧
        (Aact e u).H w = (Aact e' u).H w)
    (hd : ∀ Y, ∀ u ∈ XiCRaw S.G' (compWeight L 1) ν (k + 1) 1 T.t ×ˢ
          {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))},
        ∀ u' ∈ XiCRaw S.G' (compWeight L 1) ν (k + 1) 1 T.t ×ˢ
          {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))},
        agreeOn Y u.1 u'.1 → (∀ y ∈ Y, ∀ i, u.2 (unitPt S.hG' y, i) = u'.2 (unitPt S.hG' y, i)) →
        Ev Y u = Ev Y u')
    {θ θ' : physParam N S} (hθ : θ ∈ physVq S S.a₁ S.ν T.t q) (hθ' : θ' ∈ physVq S S.a₁ S.ν T.t q)
    (T' : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) T.m₀ (k + 1)
      Set.univ))
    (hr : agreeOn (sitesOf T') (θ.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N)
      (θ'.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N))
    (hg : ∀ x ∈ sitesOf T', θ.2 x = θ'.2 x) :
    obsCoeffParam (S.blockSplit T.m₀ hp).μ
      (fun θ t σ => tiltActObs Aact (show L ^ T.m₀ ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le hdj hK
        Rg hR (ball (0 : ℂ) (3 / 2)) θ t σ)
      (fun m => obsY1 T.m₀ S (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k
        (LocalCover.fam T.m₀ y)) m) (fun m => blockMarkC S T.m₀ hp m.1 m.2)
      (fun θ m T'' => obsHker (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y))
        (fun Y => hatCoeff (Ev Y) (θ.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N)
          (obsUnitVec S m)) T.m₀ T'')
      (obsRemLab (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y))
        (fun Y => Sum.inl (Sum.inr Y))
        (obsY0 T.m₀ (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y))
          (rootCube (m₀ := T.m₀) (blockIndex y))))
      (fun θ => obsGrFam S T.m₀ hp Ev (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k
        (LocalCover.fam T.m₀ y)) (XiCRaw S.G' (compWeight L 1) ν (k + 1) 1 T.t) θ) θ T' =
    obsCoeffParam (S.blockSplit T.m₀ hp).μ
      (fun θ t σ => tiltActObs Aact (show L ^ T.m₀ ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le hdj hK
        Rg hR (ball (0 : ℂ) (3 / 2)) θ t σ)
      (fun m => obsY1 T.m₀ S (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k
        (LocalCover.fam T.m₀ y)) m) (fun m => blockMarkC S T.m₀ hp m.1 m.2)
      (fun θ m T'' => obsHker (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y))
        (fun Y => hatCoeff (Ev Y) (θ.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N)
          (obsUnitVec S m)) T.m₀ T'')
      (obsRemLab (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y))
        (fun Y => Sum.inl (Sum.inr Y))
        (obsY0 T.m₀ (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y))
          (rootCube (m₀ := T.m₀) (blockIndex y))))
      (fun θ => obsGrFam S T.m₀ hp Ev (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k
        (LocalCover.fam T.m₀ y)) (XiCRaw S.G' (compWeight L 1) ν (k + 1) 1 T.t) θ) θ' T' := by
  have hN3 : L ^ T.m₀ ∣ N₁ := by simpa using h3N
  have hcψ := Dsc.cψ_pos
  have hp₁ : S.p₁ = p₁ := by subst hS; rfl
  have hq : S.p₁ / lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) ≤ 1 / 4 := by
    rw [hp₁, div_le_iff₀ hcψ]
    have : 0 < lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁ * p₁ := mul_pos Dsc.r_pos (hp₁ ▸ hp)
    nlinarith [Dsc.ray_margin]
  have hcell : ∀ m : ObsMarkIdx S,
      obsMarkCube S T.m₀ m ∈ blocksOf (d := d) (L := L) (N₁ := N₁)
        (m₁ := T.m₁) (K := k + 1) T.m₀ (k + 1) Set.univ ((obsLab (Lab.sum Lab) hdj).ysite
          (obsY1 T.m₀ S (Lb ⊕ Lb) (obsDomains S
            (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y)) m)) :=
    fun m => obsCubeLab_mem T.m₀ (obsMarkCube S T.m₀ m)
  have ha1 : S.a₁ = 1 := by subst hS; rfl
  have hν1 : S.ν = ν := by subst hS; rfl
  have hr0 : (θ.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N) ∈
      XiCRaw S.G' (compWeight L 1) ν (k + 1) 1 T.t := by
    have := physV_fst_mem_xiCRaw (S := S) hθ.1
    rwa [ha1, hν1] at this
  have hr0' : (θ'.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N) ∈
      XiCRaw S.G' (compWeight L 1) ν (k + 1) 1 T.t := by
    have := physV_fst_mem_xiCRaw (S := S) hθ'.1
    rwa [ha1, hν1] at this
  refine obsCoeffParam_congr_of_local (S.blockSplit T.m₀ hp).μ hN3 (le_refl (k + 1))
    isPiUnion_univ_K (Lab := obsLab (Lab.sum Lab) hdj)
    (fun θ t σ => tiltActObs Aact (show L ^ T.m₀ ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le hdj hK
        Rg hR (ball (0 : ℂ) (3 / 2)) θ t σ)
    (fun m => obsY1 T.m₀ S (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k
        (LocalCover.fam T.m₀ y)) m) (fun m => blockMarkC S T.m₀ hp m.1 m.2)
    (fun θ m T'' => obsHker (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y))
        (fun Y => hatCoeff (Ev Y) (θ.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N)
          (obsUnitVec S m)) T.m₀ T'')
    (obsRemLab (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y))
        (fun Y => Sum.inl (Sum.inr Y))
        (obsY0 T.m₀ (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y))
          (rootCube (m₀ := T.m₀) (blockIndex y))))
    (fun θ => obsGrFam S T.m₀ hp Ev (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k
        (LocalCover.fam T.m₀ y)) (XiCRaw S.G' (compWeight L 1) ν (k + 1) 1 T.t) θ)
    (fun m => depOn_blockMarkC m.1 m.2 (hcell m))
    (fun θ i u => depOn_obsGrFam_all (hp := hp) hN3 hcψ hq hdj
      (fun Y _ u hu u' hu' h =>
        hd Y u hu u' hu' (agreeOn_mono (fun x hx => Or.inl hx) h.1) h.2) _
      (fun Y => Sum.inl (Sum.inr Y)) _ (fun Y => rfl) θ i u)
    T' (θ := θ) (θ' := θ') ?_ ?_ ?_
  · intro m T₁ hT₁
    exact obsHker_hatCoeff_local_rawY hN3 hcψ hdj hd hr0 hr0' hr m (sitesOf_mono hT₁)
  · intro s _ y' hy'
    rw [Yhat_univ_eq] at hy'
    exact tiltActObs_H_local_of_labels Aact Rg hR (ball (0 : ℂ) (3 / 2)) (sitesOf T')
      (fun u w hw => (hAloc θ hθ θ' hθ' _ hr hg u w hw).1)
      (fun u w hw => (hAloc θ hθ θ' hθ' _ hr hg u w hw).2) _ _ y' hy'
  · intro s _ i hi
    rw [Yhat_univ_eq] at hi
    refine obsGrFam_local_rawY hd hcψ hq hr0 hr0' hr _ ?_ _
    intro Y hY
    subst hY
    exact hi

include Dsc hS in
/-- General tower `T : StepTowerG d L N κmin` (block scale `T.m₀`, `b = β L^{k (d-2)}`); the fixed theorem `obsCoeffParam_local_of_Ev_physRestrict` is its corollary.  **Exact locality of the observable coefficient, `physRestrict` form.**  The hypotheses of
`obsCoeffParam_local_of_Ev_rawY`, with the agreement on `sitesOf T'` of the raw data and the
sources replaced by the equality of the restrictions of `physIncl N S θ` and `physIncl N S θ'`
to `sitesOf T'`. -/
theorem obsCoeffParam_local_of_Ev_physRestrictG {q : ℝ}
    (hAloc : ∀ e ∈ physVq S S.a₁ S.ν T.t q, ∀ e' ∈ physVq S S.a₁ S.ν T.t q,
      ∀ Z : Set (CTorus d L N₁ T.m₁ (k + 1)),
      agreeOn Z (e.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N)
        (e'.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N) → (∀ x ∈ Z, e.2 x = e'.2 x) →
      ∀ (u : ℂ) (w : Lb), Lab.ysite w ⊆ Z →
        (Aact ((e.1, 0) : physParam N S) u).H w = (Aact ((e'.1, 0) : physParam N S) u).H w ∧
        (Aact e u).H w = (Aact e' u).H w)
    (hd : ∀ Y, ∀ u ∈ XiCRaw S.G' (compWeight L 1) ν (k + 1) 1 T.t ×ˢ
          {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))},
        ∀ u' ∈ XiCRaw S.G' (compWeight L 1) ν (k + 1) 1 T.t ×ˢ
          {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))},
        agreeOn Y u.1 u'.1 → (∀ y ∈ Y, ∀ i, u.2 (unitPt S.hG' y, i) = u'.2 (unitPt S.hG' y, i)) →
        Ev Y u = Ev Y u')
    {θ θ' : physParam N S} (hθ : θ ∈ physVq S S.a₁ S.ν T.t q) (hθ' : θ' ∈ physVq S S.a₁ S.ν T.t q)
    (T' : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) T.m₀ (k + 1)
      Set.univ))
    (h : physRestrict (N := N) (sitesOf T') (physIncl N S θ) =
      physRestrict (sitesOf T') (physIncl N S θ')) :
    obsCoeffParam (S.blockSplit T.m₀ hp).μ
      (fun θ t σ => tiltActObs Aact (show L ^ T.m₀ ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le hdj hK
        Rg hR (ball (0 : ℂ) (3 / 2)) θ t σ)
      (fun m => obsY1 T.m₀ S (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k
        (LocalCover.fam T.m₀ y)) m) (fun m => blockMarkC S T.m₀ hp m.1 m.2)
      (fun θ m T'' => obsHker (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y))
        (fun Y => hatCoeff (Ev Y) (θ.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N)
          (obsUnitVec S m)) T.m₀ T'')
      (obsRemLab (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y))
        (fun Y => Sum.inl (Sum.inr Y))
        (obsY0 T.m₀ (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y))
          (rootCube (m₀ := T.m₀) (blockIndex y))))
      (fun θ => obsGrFam S T.m₀ hp Ev (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k
        (LocalCover.fam T.m₀ y)) (XiCRaw S.G' (compWeight L 1) ν (k + 1) 1 T.t) θ) θ T' =
    obsCoeffParam (S.blockSplit T.m₀ hp).μ
      (fun θ t σ => tiltActObs Aact (show L ^ T.m₀ ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le hdj hK
        Rg hR (ball (0 : ℂ) (3 / 2)) θ t σ)
      (fun m => obsY1 T.m₀ S (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k
        (LocalCover.fam T.m₀ y)) m) (fun m => blockMarkC S T.m₀ hp m.1 m.2)
      (fun θ m T'' => obsHker (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y))
        (fun Y => hatCoeff (Ev Y) (θ.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N)
          (obsUnitVec S m)) T.m₀ T'')
      (obsRemLab (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y))
        (fun Y => Sum.inl (Sum.inr Y))
        (obsY0 T.m₀ (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y))
          (rootCube (m₀ := T.m₀) (blockIndex y))))
      (fun θ => obsGrFam S T.m₀ hp Ev (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k
        (LocalCover.fam T.m₀ y)) (XiCRaw S.G' (compWeight L 1) ν (k + 1) 1 T.t) θ) θ' T' := by
  obtain ⟨hr, hg⟩ := (physRestrict_physIncl_eq_iff S (sitesOf T') θ θ').1 h
  exact obsCoeffParam_local_of_Ev_rawYG T k hk N₁ ν β p₁ Dsc S hS hp y h3N Lab hεH Aact hdj hK Rg hR
    Ev hAloc hd hθ hθ' T' hr hg

end TowerG

section Tower

variable {κmin : ℝ} (T : StepTower κmin) (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁]
  (ν β p₁ : ℝ) (Dsc : StepScaleData T k hk N₁ ν β p₁)
  (S : StepSetting 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) (hS : S = T.step k hk N₁ ν β p₁)
  (hp : 0 < S.p₁) (y : CTorus 3 3 N₁ T.m₁ (k + 1)) (h3N : 3 ∣ N₁)
  {Lb : Type} [Fintype Lb]
  (Lab : CubeLabels (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
    Set.univ Lb) {εH : ℝ} (hεH : 0 < εH) {Kc : ℝ}
  (Aact : physParam 2 S → ℂ → LabelAct Lab (S.blockSplit 1 hp).Ωb εH (2 * T.κdec - 1) T.κ0 Kc)
  (hdj : ∀ Y ∈ obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y), IsDj 1 (k + 1) Y)
  {Kobs : ℝ} (hK : Kc + Kc + K0 3 3 T.κ0 + K0 3 3 T.κ0 ≤ Kobs) (Rg : ℝ) (hR : 0 ≤ Rg)
  (Ev : Set (CTorus 3 3 N₁ T.m₁ (k + 1)) →
    RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 × (unitPts S.G' × Fin 2 → ℂ) → ℂ)

include Dsc hS in
/-- **Exact locality of the observable coefficient at the tower.**  Let `Ev` be local in the sharp
form (clause `hd` of `obsEv_fromTower_rawY`) and let the activity `Aact` of the family of labels be
local in the exact form: for `e, e'` of `physVq` whose raw data agree on `Z` itself and whose
sources agree on `Z`, the activities of the labels with sites in `Z` agree, at the parameters
`(e.1, 0), (e'.1, 0)` and at `e, e'`.  Then for `θ, θ'` of `physVq` whose raw data agree on
`sitesOf T'` and whose sources agree on `sitesOf T'`, the coefficients agree.  The kernel entries
and remainder marks read the raw datum on `sitesOf T'` through `hd`; the datum enters the proof of
the analyticity and the value of the remainder marks only through the thick clause, which is not
a hypothesis here. -/
theorem obsCoeffParam_local_of_Ev_rawY {q : ℝ}
    (hAloc : ∀ e ∈ physVq S S.a₁ S.ν T.t q, ∀ e' ∈ physVq S S.a₁ S.ν T.t q,
      ∀ Z : Set (CTorus 3 3 N₁ T.m₁ (k + 1)),
      agreeOn Z (e.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2)
        (e'.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2) → (∀ x ∈ Z, e.2 x = e'.2 x) →
      ∀ (u : ℂ) (w : Lb), Lab.ysite w ⊆ Z →
        (Aact ((e.1, 0) : physParam 2 S) u).H w = (Aact ((e'.1, 0) : physParam 2 S) u).H w ∧
        (Aact e u).H w = (Aact e' u).H w)
    (hd : ∀ Y, ∀ u ∈ XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t ×ˢ
          {ψh : unitPts S.G' × Fin 2 → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsi T.κ T.t (β * 3 ^ k)},
        ∀ u' ∈ XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t ×ˢ
          {ψh : unitPts S.G' × Fin 2 → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsi T.κ T.t (β * 3 ^ k)},
        agreeOn Y u.1 u'.1 → (∀ y ∈ Y, ∀ i, u.2 (unitPt S.hG' y, i) = u'.2 (unitPt S.hG' y, i)) →
        Ev Y u = Ev Y u')
    {θ θ' : physParam 2 S} (hθ : θ ∈ physVq S S.a₁ S.ν T.t q) (hθ' : θ' ∈ physVq S S.a₁ S.ν T.t q)
    (T' : Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
      Set.univ))
    (hr : agreeOn (sitesOf T') (θ.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2)
      (θ'.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2))
    (hg : ∀ x ∈ sitesOf T', θ.2 x = θ'.2 x) :
    obsCoeffParam (S.blockSplit 1 hp).μ
      (fun θ t σ => tiltActObs Aact (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le hdj hK
        Rg hR (ball (0 : ℂ) (3 / 2)) θ t σ)
      (fun m => obsY1 1 S (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k
        (LocalCover.fam 1 y)) m) (fun m => blockMarkC S 1 hp m.1 m.2)
      (fun θ m T'' => obsHker (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
        (fun Y => hatCoeff (Ev Y) (θ.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2)
          (obsUnitVec S m)) 1 T'')
      (obsRemLab (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
        (fun Y => Sum.inl (Sum.inr Y))
        (obsY0 1 (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
          (rootCube (m₀ := 1) (blockIndex y))))
      (fun θ => obsGrFam S 1 hp Ev (obsDomains S (LocalCover.nbhdF 1 y) 1 k
        (LocalCover.fam 1 y)) (XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t) θ) θ T' =
    obsCoeffParam (S.blockSplit 1 hp).μ
      (fun θ t σ => tiltActObs Aact (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le hdj hK
        Rg hR (ball (0 : ℂ) (3 / 2)) θ t σ)
      (fun m => obsY1 1 S (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k
        (LocalCover.fam 1 y)) m) (fun m => blockMarkC S 1 hp m.1 m.2)
      (fun θ m T'' => obsHker (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
        (fun Y => hatCoeff (Ev Y) (θ.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2)
          (obsUnitVec S m)) 1 T'')
      (obsRemLab (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
        (fun Y => Sum.inl (Sum.inr Y))
        (obsY0 1 (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
          (rootCube (m₀ := 1) (blockIndex y))))
      (fun θ => obsGrFam S 1 hp Ev (obsDomains S (LocalCover.nbhdF 1 y) 1 k
        (LocalCover.fam 1 y)) (XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t) θ) θ' T' := by
  have hb : β * ((3 : ℕ) : ℝ) ^ (k * (3 - 2)) = β * 3 ^ k := by norm_num
  exact obsCoeffParam_local_of_Ev_rawYG T.toG k hk N₁ ν β p₁ (T.scaleDataG_of_fixed Dsc)
    S hS hp y h3N Lab hεH Aact hdj hK Rg hR Ev hAloc (by rw [hb]; exact hd) hθ hθ' T' hr hg

include Dsc hS in
/-- **Exact locality of the observable coefficient, `physRestrict` form.**  The hypotheses of
`obsCoeffParam_local_of_Ev_rawY`, with the agreement on `sitesOf T'` of the raw data and the
sources replaced by the equality of the restrictions of `physIncl 2 S θ` and `physIncl 2 S θ'`
to `sitesOf T'`. -/
theorem obsCoeffParam_local_of_Ev_physRestrict {q : ℝ}
    (hAloc : ∀ e ∈ physVq S S.a₁ S.ν T.t q, ∀ e' ∈ physVq S S.a₁ S.ν T.t q,
      ∀ Z : Set (CTorus 3 3 N₁ T.m₁ (k + 1)),
      agreeOn Z (e.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2)
        (e'.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2) → (∀ x ∈ Z, e.2 x = e'.2 x) →
      ∀ (u : ℂ) (w : Lb), Lab.ysite w ⊆ Z →
        (Aact ((e.1, 0) : physParam 2 S) u).H w = (Aact ((e'.1, 0) : physParam 2 S) u).H w ∧
        (Aact e u).H w = (Aact e' u).H w)
    (hd : ∀ Y, ∀ u ∈ XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t ×ˢ
          {ψh : unitPts S.G' × Fin 2 → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsi T.κ T.t (β * 3 ^ k)},
        ∀ u' ∈ XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t ×ˢ
          {ψh : unitPts S.G' × Fin 2 → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsi T.κ T.t (β * 3 ^ k)},
        agreeOn Y u.1 u'.1 → (∀ y ∈ Y, ∀ i, u.2 (unitPt S.hG' y, i) = u'.2 (unitPt S.hG' y, i)) →
        Ev Y u = Ev Y u')
    {θ θ' : physParam 2 S} (hθ : θ ∈ physVq S S.a₁ S.ν T.t q) (hθ' : θ' ∈ physVq S S.a₁ S.ν T.t q)
    (T' : Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
      Set.univ))
    (h : physRestrict (N := 2) (sitesOf T') (physIncl 2 S θ) =
      physRestrict (sitesOf T') (physIncl 2 S θ')) :
    obsCoeffParam (S.blockSplit 1 hp).μ
      (fun θ t σ => tiltActObs Aact (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le hdj hK
        Rg hR (ball (0 : ℂ) (3 / 2)) θ t σ)
      (fun m => obsY1 1 S (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k
        (LocalCover.fam 1 y)) m) (fun m => blockMarkC S 1 hp m.1 m.2)
      (fun θ m T'' => obsHker (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
        (fun Y => hatCoeff (Ev Y) (θ.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2)
          (obsUnitVec S m)) 1 T'')
      (obsRemLab (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
        (fun Y => Sum.inl (Sum.inr Y))
        (obsY0 1 (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
          (rootCube (m₀ := 1) (blockIndex y))))
      (fun θ => obsGrFam S 1 hp Ev (obsDomains S (LocalCover.nbhdF 1 y) 1 k
        (LocalCover.fam 1 y)) (XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t) θ) θ T' =
    obsCoeffParam (S.blockSplit 1 hp).μ
      (fun θ t σ => tiltActObs Aact (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le hdj hK
        Rg hR (ball (0 : ℂ) (3 / 2)) θ t σ)
      (fun m => obsY1 1 S (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k
        (LocalCover.fam 1 y)) m) (fun m => blockMarkC S 1 hp m.1 m.2)
      (fun θ m T'' => obsHker (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
        (fun Y => hatCoeff (Ev Y) (θ.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2)
          (obsUnitVec S m)) 1 T'')
      (obsRemLab (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
        (fun Y => Sum.inl (Sum.inr Y))
        (obsY0 1 (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
          (rootCube (m₀ := 1) (blockIndex y))))
      (fun θ => obsGrFam S 1 hp Ev (obsDomains S (LocalCover.nbhdF 1 y) 1 k
        (LocalCover.fam 1 y)) (XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t) θ) θ' T' := by
  obtain ⟨hr, hg⟩ := (physRestrict_physIncl_eq_iff S (sitesOf T') θ θ').1 h
  exact obsCoeffParam_local_of_Ev_rawY T k hk N₁ ν β p₁ Dsc S hS hp y h3N Lab hεH Aact hdj hK Rg hR
    Ev hAloc hd hθ hθ' T' hr hg

end Tower

end Balaban.Inhabited
