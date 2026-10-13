/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepScaleDataGBridge
public import Balaban.Fluctuation.ObsKernelParam
public import Balaban.Fluctuation.ObsMarksAssembly
public import Balaban.Inhabited.ObsMarksFromTower

/-!
# The observable kernel as a function of the datum, for the family of the sharp hat expansion

For the one family `Ev` of `obsMarkHalves_of_sharpHat_param`: the mark half and the identity of
`ObsMarks` for every datum of `Ξ`, and, for every mark and label set, the kernel
`r ↦ obsHker 𝒴 (fun Y => hatCoeff (Ev Y) r e_m) m₀ T` is analytic on the raw data `XiCRaw`, equals
the kernel of `ObsMarkHalf` at `rawOf D`, is local, and obeys the decay bound.

* `obsHker_param_fromSharpHat`: the statement, under the premises of the sharp hat expansion.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Polymer Balaban.SmallField.Def6 Balaban.Multiscale
  Balaban.Background Balaban.Analysis Balaban.SmallField

section SharpHat

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ)
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ} {X₁f : Finset (CTorus d L N₁ m₁ (k + 1))} {j : ℕ}
variable {m₀ : ℕ} {X 𝒦X : Set (CTorus d L N₁ m₁ (k + 1))}

/-- **The observable kernel as an analytic, local, bounded function of the datum.**

Premises: those of `obsMarkHalves_of_sharpHat`.  Conclusion: one family `Ev` such that

* for every datum `D` of `Ξ`, `ObsMarkHalf` and `ObsRayIdentity` hold for `Ev` (the conclusion of
  `obsMarkHalves_of_sharpHat`);
* for every mark `m` and label set `T`, with `kerr r := obsHker 𝒴 (fun Y => hatCoeff (Ev Y) r
  (obsUnitVec S m)) m₀ T` and `𝒴` the polymer domains of the expansion: `kerr` is analytic at every
  point of `XiCRaw`; `kerr (rawOf D)` is the kernel `obsHker 𝒴 (obsRowCoeff S Ev D m) m₀ T` for
  every raw datum of `Ξ`; `kerr` is local (two raw data of `XiCRaw` that agree on the thickening
  of a set containing every domain with label `T` have the same `kerr`); and
  `‖kerr r‖ ≤ (Q δ₁ / cψ) · exp (-2 κdec · dExt T)` on `XiCRaw`. -/
theorem obsHker_param_fromSharpHat (hC : FlCore N S.G' Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hk : 1 ≤ k) (hG : IsLevel Hm k) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 < cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    (hcov : CovSetup S.G' m₀ j X 𝒦X)
    (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) = X1 S.G' m₀ j 𝒦X)
    (hconn : HatConn S.G') (hrow : RowInHat (coverOf S.G') Hm (compWeight L a₁) ν)
    (hopt : ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X) ∧ MeetsOne m₀ j 𝒦X W₀ ∧
        bondCost (scaleW L m₀ m₁ j) E₀ = treeLenCovOne m₀ j X)
    (hΔ : treeLenCovOne m₀ j X = 0)
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (y : CTorus d L N₁ m₁ (k + 1)) (hy : y ∈ X₁f) (iy : Fin N)
    (hp : 0 < S.p₁) (hq : S.p₁ / cψ ≤ 1 / 4)
    {Lb₀ : Type} (Lab₀ : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀
      (k + 1) Set.univ Lb₀)
    {κG κ0 : ℝ} (hκG : κG ≤ 2 * κdec) (hκ0 : aEnt d L + 1 ≤ κ0) :
    ∃ Ev : Set (CTorus d L N₁ m₁ (k + 1)) →
        RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts S.G' × Fin N → ℂ) → ℂ,
      (∀ D : BgData S.G' N, XiCData S.G' (compWeight L a₁) ν (k + 1) 1 eps D →
        ObsMarkHalf S m₀ hp Ev D (obsDomains S X₁f m₀ j 𝒦X)
          (obsLab Lab₀ (obsDomains_isDj (X₁f := X₁f) S hC.HBp.hd hcov hopt)) cψ
          (cK2' d L N (famConst d L BG₂ κ) * δ₁) κG κ0
          (cK2' d L N (famConst d L BG₂ κ) * δ₁ / cψ) (2 * κdec)
          (rootCube (m₀ := m₀) (blockIndex y)) ∧
        ObsRayIdentity S m₀ hp
          (fun ψh => svec Hm (flFieldOne S.G' Hm BG₂ κ a₁ ν D
            (hatLift S.G' a₁ ν S.hG' cc D ψh)) y iy) Ev D (obsDomains S X₁f m₀ j 𝒦X)) ∧
      ∀ (m : ObsMarkIdx S) (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
        (K := k + 1) m₀ (k + 1) Set.univ)),
      AnalyticOnNhd ℂ (fun r => obsHker (obsDomains S X₁f m₀ j 𝒦X) (fun Y => hatCoeff (Ev Y) r (obsUnitVec S m)) m₀ T)
        (XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps) ∧
      (∀ D : BgData S.G' N, rawOf D ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps →
        obsHker (obsDomains S X₁f m₀ j 𝒦X) (obsRowCoeff S Ev D m) m₀ T =
          obsHker (obsDomains S X₁f m₀ j 𝒦X) (fun Y => hatCoeff (Ev Y) (rawOf D) (obsUnitVec S m)) m₀ T) ∧
      (∀ Z : Set (CTorus d L N₁ m₁ (k + 1)),
        (∀ Y ∈ (obsDomains S X₁f m₀ j 𝒦X), obsRowLabel m₀ (k + 1) Y = T → Y ⊆ Z) →
        ∀ r ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps, ∀ r' ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps, agreeOn (thickSet S.G' Z) r r' →
          obsHker (obsDomains S X₁f m₀ j 𝒦X) (fun Y => hatCoeff (Ev Y) r (obsUnitVec S m)) m₀ T =
            obsHker (obsDomains S X₁f m₀ j 𝒦X) (fun Y => hatCoeff (Ev Y) r' (obsUnitVec S m)) m₀ T) ∧
      (∀ r ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps, ‖obsHker (obsDomains S X₁f m₀ j 𝒦X) (fun Y => hatCoeff (Ev Y) r (obsUnitVec S m)) m₀ T‖ ≤
        (cK2' d L N (famConst d L BG₂ κ) * δ₁ / cψ) * Real.exp (-(2 * κdec) * dExt T)) := by
  classical
  obtain ⟨Ev, ha, hd, hb, hEv⟩ := obsMarkHalves_of_sharpHat_param S hC hk hG cc hcψ hMX hdm hα hsm
    hδ₁ hcov hX₁ hconn hrow hopt hΔ hκ₀ hκdec hκ h1 hlog y hy iy hp hq Lab₀ hκG hκ0
  have hd0 : 0 < d := by have := hC.HBp.hd; omega
  have hB0 : 0 ≤ cK2' d L N (famConst d L BG₂ κ) * δ₁ := by
    have hf := famConst_ge_one (L := L) hC.hS2.fam.2.1 κ hd0
    exact mul_nonneg (cK2'_nonneg (by linarith)) hC.δ₁_pos.le
  refine ⟨Ev, hEv, fun m T => ?_⟩
  exact obsHker_param_of_Ev S hcψ hB0 (by linarith) Ev hd hb ha _ hcov.hN
    (obsDomains_isDj (X₁f := X₁f) S hC.HBp.hd hcov hopt) m T

end SharpHat

end Balaban.Fluctuation

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep

/-- The label domains of the observable site `(y, i)` of a step equal to the step of the tower are
domains of the level `k + 1`. -/
theorem StepScaleDataG.isDj_obsDomains {d L N : ℕ} [NeZero L] {κmin : ℝ} {T : StepTowerG d L N κmin}
    {k : ℕ} {hk : 1 ≤ k} {N₁ : ℕ} [NeZero N₁] {ν β p₁ : ℝ}
    (D : StepScaleDataG T k hk N₁ ν β p₁) {ϱ : ℝ} (hϱ : ϱ = rhoSepG d L T.m₁)
    {S : StepSetting d L N₁ T.m₁ k N ϱ} (hS : S = hatStepKG T.hN k T.m₁ ϱ hk ν β p₁ T.δ)
    (y : CTorus d L N₁ T.m₁ (k + 1)) (i : Fin N) :
    ∀ Y ∈ obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y), IsDj T.m₀ (k + 1) Y := by
  subst hϱ
  subst hS
  exact obsDomains_isDj (X₁f := LocalCover.nbhdF T.m₀ y) _ T.hd (D.covers.2 (y, i)).1
    (D.covers.2 (y, i)).2.2.1

/-- General tower `T : StepTowerG d L N κmin` (block scale `T.m₀`, `b = β L^{k (d-2)}`); the fixed theorem `obsHker_param_fromTower` is its corollary.  **The observable kernel as an analytic, local, bounded function of the datum, at the shared
tower.**  The instance of `obsHker_param_fromSharpHat` used by `obsMarks_zeroClass_family_of_ray`
(same covers `Dsc.covers`, same constants `κ0 = T.κ0`, `κG = 2 κdec - 1`, `cψ = lvCpsi`, same root
`rootCube (blockIndex y)`, same `cc = β_k^{-1/2}`), at one admissible scale with `StepScaleData`,
for every site `y`, spin `i` and every label system `Lab₀`. -/
theorem obsHker_param_fromTowerG {d L N : ℕ} [NeZero L] {κmin : ℝ} (T : StepTowerG d L N κmin)
    (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (ν β p₁ : ℝ) (hN : 5 < N₁)
    (hνpos : 0 < ν) (hν : ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1)
    (Dsc : StepScaleDataG T k hk N₁ ν β p₁)
    {ϱ : ℝ} (hϱ : ϱ = rhoSepG d L T.m₁) {S : StepSetting d L N₁ T.m₁ k N ϱ}
    (hS : S = hatStepKG T.hN k T.m₁ ϱ hk ν β p₁ T.δ)
    (hp : 0 < S.p₁) (y : CTorus d L N₁ T.m₁ (k + 1)) (i : Fin N)
    {Lb₀ : Type} (Lab₀ : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) T.m₀
      (k + 1) Set.univ Lb₀) :
    ∃ Ev : Set (CTorus d L N₁ T.m₁ (k + 1)) →
        RawData d L (N₁ * L ^ T.m₁) (k + 1) N × (unitPts S.G' × Fin N → ℂ) → ℂ,
      (∀ D : BgData S.G' N, XiCData S.G' (compWeight L 1) ν (k + 1) 1 T.t D →
        ObsMarkHalf S T.m₀ hp Ev D (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y))
          (obsLab Lab₀ (Dsc.isDj_obsDomains hϱ hS y i)) (lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))))
          (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) (2 * T.κdec - 1) T.κ0
          (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t / (lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))))) (2 * T.κdec)
          (rootCube (m₀ := T.m₀) (blockIndex y)) ∧
        ObsRayIdentity S T.m₀ hp
          (fun ψh => svec (lvLowG d L N₁ T.m₁ k ϱ) (flFieldOne S.G' (lvLowG d L N₁ T.m₁ k ϱ) T.BG₂ T.κ 1 ν D
            (hatLift S.G' 1 ν S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) D ψh)) y i) Ev D (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y))) ∧
      ∀ (m : ObsMarkIdx S) (Tl : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁)
        (K := k + 1) T.m₀ (k + 1) Set.univ)),
      AnalyticOnNhd ℂ (fun r => obsHker (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y)) (fun Y => hatCoeff (Ev Y) r (obsUnitVec S m)) T.m₀ Tl)
        (XiCRaw S.G' (compWeight L 1) ν (k + 1) 1 T.t) ∧
      (∀ D : BgData S.G' N, rawOf D ∈ XiCRaw S.G' (compWeight L 1) ν (k + 1) 1 T.t →
        obsHker (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y)) (obsRowCoeff S Ev D m) T.m₀ Tl =
          obsHker (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y)) (fun Y => hatCoeff (Ev Y) (rawOf D) (obsUnitVec S m)) T.m₀ Tl) ∧
      (∀ Z : Set (CTorus d L N₁ T.m₁ (k + 1)),
        (∀ Y ∈ (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y)), obsRowLabel T.m₀ (k + 1) Y = Tl → Y ⊆ Z) →
        ∀ r ∈ XiCRaw S.G' (compWeight L 1) ν (k + 1) 1 T.t, ∀ r' ∈ XiCRaw S.G' (compWeight L 1) ν (k + 1) 1 T.t, agreeOn (thickSet S.G' Z) r r' →
          obsHker (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y)) (fun Y => hatCoeff (Ev Y) r (obsUnitVec S m)) T.m₀ Tl =
            obsHker (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y)) (fun Y => hatCoeff (Ev Y) r' (obsUnitVec S m)) T.m₀ Tl) ∧
      (∀ r ∈ XiCRaw S.G' (compWeight L 1) ν (k + 1) 1 T.t, ‖obsHker (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y)) (fun Y => hatCoeff (Ev Y) r (obsUnitVec S m)) T.m₀ Tl‖ ≤
        (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t / (lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))))) * Real.exp (-(2 * T.κdec) * dExt Tl)) := by
  subst hϱ
  have hS' : S = T.step k hk N₁ ν β p₁ := hS
  subst hS'
  have hν0 : 0 ≤ ν := hνpos.le
  have hr0 := Dsc.r_pos
  have hcψ0 := Dsc.cψ_pos
  have hq : p₁ / lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) ≤ 1 / 4 := by
    rw [div_le_iff₀ hcψ0]
    have : 0 < lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁ * p₁ := mul_pos hr0 hp
    nlinarith [Dsc.ray_margin]
  obtain ⟨hcov, hX₁, hopt, hΔ, hy⟩ := Dsc.covers.2 (y, i)
  exact obsHker_param_fromSharpHat (T.step k hk N₁ ν β p₁) Dsc.core hk (isLevel_lvLowG hk)
    ((_ ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) hcψ0 T.large_block T.dom_margin T.coer_margin T.δc_small
    Dsc.fl_radius hcov hX₁ (hatConn_lvTopG T.hL) (rowInHat_lvG hk (dgSetting_lvG T.hd T.hL T.m₁_four hN hν0 hν)) hopt hΔ
    T.κ0_nonneg T.κdec_lower (by exact_mod_cast T.κ_lower) T.κ_one T.κ_log y hy i hp hq Lab₀
    T.marks_κG_le T.κ0_ent


/-- **The observable kernel as an analytic, local, bounded function of the datum, at the shared
tower.**  The instance of `obsHker_param_fromSharpHat` used by `obsMarks_zeroClass_family_of_ray`
(same covers `Dsc.covers`, same constants `κ0 = T.κ0`, `κG = 2 κdec - 1`, `cψ = lvCpsi`, same root
`rootCube (blockIndex y)`, same `cc = β_k^{-1/2}`), at one admissible scale with `StepScaleData`,
for every site `y`, spin `i` and every label system `Lab₀`. -/
theorem obsHker_param_fromTower {κmin : ℝ} (T : StepTower κmin)
    (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (ν β p₁ : ℝ) (hN : 5 < N₁)
    (hνpos : 0 < ν) (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1)
    (Dsc : StepScaleData T k hk N₁ ν β p₁)
    (hp : 0 < (T.step k hk N₁ ν β p₁).p₁) (y : CTorus 3 3 N₁ T.m₁ (k + 1)) (i : Fin 2)
    {Lb₀ : Type} (Lab₀ : CubeLabels (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1
      (k + 1) Set.univ Lb₀) :
    let S := T.step k hk N₁ ν β p₁;
    ∃ Ev : Set (CTorus 3 3 N₁ T.m₁ (k + 1)) →
        RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 × (unitPts S.G' × Fin 2 → ℂ) → ℂ,
      (∀ D : BgData S.G' 2, XiCData S.G' (compWeight 3 1) ν (k + 1) 1 T.t D →
        ObsMarkHalf S 1 hp Ev D (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
          (obsLab Lab₀ (obsDomains_isDj (X₁f := LocalCover.nbhdF 1 y) S le_rfl (Dsc.covers.2 (y, i)).1 (Dsc.covers.2 (y, i)).2.2.1)) (lvCpsi T.κ T.t (β * 3 ^ k))
          (cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) * T.t) (2 * T.κdec - 1) T.κ0
          (cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) * T.t / (lvCpsi T.κ T.t (β * 3 ^ k))) (2 * T.κdec)
          (rootCube (m₀ := 1) (blockIndex y)) ∧
        ObsRayIdentity S 1 hp
          (fun ψh => svec (lvLow N₁ T.m₁ k (rhoSep T.m₁)) (flFieldOne S.G' (lvLow N₁ T.m₁ k (rhoSep T.m₁)) T.BG₂ T.κ 1 ν D
            (hatLift S.G' 1 ν S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) D ψh)) y i) Ev D (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))) ∧
      ∀ (m : ObsMarkIdx S) (Tl : Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁)
        (K := k + 1) 1 (k + 1) Set.univ)),
      AnalyticOnNhd ℂ (fun r => obsHker (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) (fun Y => hatCoeff (Ev Y) r (obsUnitVec S m)) 1 Tl)
        (XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t) ∧
      (∀ D : BgData S.G' 2, rawOf D ∈ XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t →
        obsHker (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) (obsRowCoeff S Ev D m) 1 Tl =
          obsHker (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) (fun Y => hatCoeff (Ev Y) (rawOf D) (obsUnitVec S m)) 1 Tl) ∧
      (∀ Z : Set (CTorus 3 3 N₁ T.m₁ (k + 1)),
        (∀ Y ∈ (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)), obsRowLabel 1 (k + 1) Y = Tl → Y ⊆ Z) →
        ∀ r ∈ XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t, ∀ r' ∈ XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t, agreeOn (thickSet S.G' Z) r r' →
          obsHker (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) (fun Y => hatCoeff (Ev Y) r (obsUnitVec S m)) 1 Tl =
            obsHker (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) (fun Y => hatCoeff (Ev Y) r' (obsUnitVec S m)) 1 Tl) ∧
      (∀ r ∈ XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t, ‖obsHker (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) (fun Y => hatCoeff (Ev Y) r (obsUnitVec S m)) 1 Tl‖ ≤
        (cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) * T.t / (lvCpsi T.κ T.t (β * 3 ^ k))) * Real.exp (-(2 * T.κdec) * dExt Tl)) := by
  intro S
  have e : β * ((3 : ℕ) : ℝ) ^ (k * (3 - 2)) = β * 3 ^ k := by norm_num
  have G := obsHker_param_fromTowerG T.toG k hk N₁ ν β p₁ hN hνpos (by simpa using hν)
    (T.scaleDataG_of_fixed Dsc) (ϱ := rhoSep T.m₁) (rhoSepG_three _).symm
    (S := T.step k hk N₁ ν β p₁) rfl hp y i Lab₀
  rw [e] at G
  exact G

end Balaban.Inhabited
