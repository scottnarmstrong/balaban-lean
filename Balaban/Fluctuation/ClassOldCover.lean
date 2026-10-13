/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.ClassOldDecInputM
public import Balaban.Fluctuation.GeneralOldCoeffFamily
public import Balaban.Fluctuation.LevelLocalCover
import Mathlib.Tactic.Linarith

/-!
# The cover data of an inherited label of a class member

For an inherited label `X ∈ 𝒟_j` (`1 ≤ j ≤ k`) of a class member and the level generating set `Gp`
of level `K = k + 1` (`IsLevel Gp K`), the cover data that `classOldDec_expansion` and
`classOldDecObs_expansion` assumed (`hcov`, `hX₁`, `hopt`) exist.

* `exists_covSetup_of_isPolyDom`: there is a chosen family `𝒦_X` of `X` with `CovSetup Gp m₀ j X 𝒦_X`
  (the nesting of each chosen cube in an aligned level-`K` cube inside `Λ_K`, which is the whole
  torus for a level set) and a connected structure in `X` meeting `𝒦_X` whose cost is `d^cov_j(X)`
  (attainment of the infimum `treeLenCovOne`, for the same family).
* `classOldDec_expansion_cover`, `classOldDecObs_expansion_cover`: the per-label decoupled expansions
  without `hcov`, `hX₁`, `hopt`: there is a chosen family `𝒦_X` such that for every finset `X₁f` with
  underlying set `X1 Gp m₀ j 𝒦_X` the expansion holds.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Multiscale Balaban.Background Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.SmallField.Def6v2 Finset

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- **The cover data of a polymer of `𝒟_j` at the level `K = k + 1`.**  For `X ∈ 𝒟_j`, `j ≤ k`, and a
level generating set `Gp` (`Λ_K` is the whole torus), there is a chosen family `𝒦_X` with
`CovSetup Gp m₀ j X 𝒦_X` together with a connected structure in `X` meeting `𝒦_X` whose cost is
`d^cov_j(X)`.  The nest of a cube `b ∈ 𝒦_X` is the level-`K` cube `cbase (cellSide K) b`
(`box_subset_box_cbase_of_dvd`). -/
theorem exists_covSetup_of_isPolyDom {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
    (hG' : IsLevel Gp (k + 1)) {m₀ j : ℕ} (hN : L ^ m₀ ∣ N₁) (hjk : j + 1 ≤ k + 1)
    {X : Set (CTorus d L N₁ m₁ (k + 1))} (hX : IsPolyDom m₀ j X) :
    ∃ 𝒦X : Set (CTorus d L N₁ m₁ (k + 1)), CovSetup Gp m₀ j X 𝒦X ∧
      ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
        (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
        ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X) ∧ MeetsOne m₀ j 𝒦X W₀ ∧
          bondCost (scaleW L m₀ m₁ j) E₀ = treeLenCovOne m₀ j X := by
  obtain ⟨𝒦, W, E, hch, hconn, hWX, hmeet, hcost⟩ :=
    treeLenCovOne_attained m₀ j X (SmallField.exists_cover_struct hX)
  refine ⟨𝒦, ⟨layerUnion_of_isLevel hG' m₀, hN, hjk, hch, fun b hb => ?_⟩,
    W, E, hconn, hWX, hmeet, hcost⟩
  have hac : cellSide L m₀ m₁ j ∣ cellSide L m₀ m₁ (k + 1) :=
    pow_dvd_pow L (by omega)
  have hc0 := cellSide_pos (L := L) m₀ m₁ (k + 1)
  have hL1 : 1 ≤ L := Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  exact ⟨cbase (cellSide L m₀ m₁ (k + 1)) b, aligned_cbase b,
    box_subset_box_cbase_of_dvd hc0 hac hL1 (hch.1 b hb).1,
    fun x _ => Finset.mem_coe.2 (hG'.mem_layer x)⟩

variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
  {Gk : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
  {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
  {a₁ ν c BG κ r₀ eps δ₃ : ℝ} {X₀ : Finset (CTorus d L N₁ m₁ (k + 1))}
  {Kc Cx c₂ BG₂ δ₁ δfl : ℝ} {X : Set (CTorus d L N₁ m₁ (k + 1))}

open Classical in
/-- **`classOldDec_expansion` without `hcov`, `hX₁`, `hopt`.**  The cover data come from
`exists_covSetup_of_isPolyDom`: some chosen family `𝒦_X` works for every finset `X₁f` of sites with
underlying set `X1 Gp m₀ j 𝒦_X`; the hypotheses `hB`, `hF` are about this `X₁f`, hence stated
inside.  Needs `L ^ m₀ ∣ N₁`. -/
theorem classOldDec_expansion_cover {P : Consts} {Dom : FieldDom d L N₁ m₁ (k + 1) N ϱ}
    (C : StepClass d L N₁ m₁ k N ϱ) (hm : P.m₀ = C.m₀) (hcl : SFTermClauses P Dom C.Tm)
    {β : ℝ} (hβ : 0 < β) (hE₀ : 0 ≤ P.E₀) {j : ℕ} (hN : L ^ C.m₀ ∣ N₁) (hj1 : 1 ≤ j) (hjk : j ≤ k)
    {y : CTorus d L N₁ m₁ (k + 1)} (hXp : IsPolyDom C.m₀ j X) (hy : y ∈ X)
    (hk : 1 ≤ k) (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    (hconn : HatConn Gp) (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ C.m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hκP : κdec - 1 ≤ P.κ)
    (hchart : ∀ r ∈ XiCRaw (C.Tm.gs j X) (compWeight L a₁) ν j (scaledC0 d)
      (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      Dom.dom j (C.Tm.gs j X) r.1 r.2) :
    ∃ 𝒦X : Set (CTorus d L N₁ m₁ (k + 1)),
      ∀ X₁f : Finset (CTorus d L N₁ m₁ (k + 1)),
        (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp C.m₀ j 𝒦X →
        ∀ (hB : BgSetting N Gp Gk (C.Tm.gs j X) a₁ ν c BG κ r₀ eps δ₃ X₀ X₁f j) (hF : FlSetting N Gp Gk Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl X₁f),
    ∃ Ev : Set (CTorus d L N₁ m₁ (k + 1)) →
          RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gp × Fin N → ℂ) → ℂ,
        (∀ D : BgData Gp N, XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D →
          ∀ ψh : unitPts Gp × Fin N → ℂ, (∀ p, ‖ψh p‖ ≤ cψ) →
          flComp hB hF (fun r => (β : ℂ)⁻¹ * C.Tm.E j y X r.1 r.2)
            (rawOf D, hatLift Gp a₁ ν hG' cc D ψh) =
          ∑ Y ∈ polymerDomains (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1)
            Gp C.m₀ (X1 Gp C.m₀ j 𝒦X), Ev Y (rawOf D, ψh)) ∧
        (∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
            {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
          ∀ u' ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
            {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
          agreeOn Y u.1 u'.1 → (∀ y ∈ Y, ∀ i, u.2 (unitPt hG' y, i) = u'.2 (unitPt hG' y, i)) →
          Ev Y u = Ev Y u') ∧
        (∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
            {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
          ‖Ev Y u‖ ≤ (β⁻¹ * P.E₀) *
            Real.exp (-κ₀ * treeLenCovOne C.m₀ j X - 2 * κdec * treeLenCov Gp C.m₀ Y)) ∧
        (∀ Y, AnalyticOnNhd ℂ (Ev Y) (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
            {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ})) := by
  obtain ⟨𝒦X, hcov, hopt⟩ := exists_covSetup_of_isPolyDom hG' hN (by omega) hXp
  exact ⟨𝒦X, fun X₁f hX₁ hB hF =>
    classOldDec_expansion C hm hcl hβ hE₀ hj1 hjk hXp hy hB hF hk hG hG' cc hcψ hMX hdm hα hsm hδ₁
      hcov hX₁ hconn hrow hopt hκ₀ hκdec hκ h1 hlog hκP hchart⟩


open Classical in
/-- **`classOldDecObs_expansion` without `hcov`, `hX₁`, `hopt`**, as `classOldDec_expansion_cover`. -/
theorem classOldDecObs_expansion_cover {P : Consts} {Dom : FieldDom d L N₁ m₁ (k + 1) N ϱ}
    (C : StepClass d L N₁ m₁ k N ϱ) (hm : P.m₀ = C.m₀) (hcl : SFTermClauses P Dom C.Tm)
    (hc₉ : 0 ≤ P.c₉) (g : Fld d L N₁ m₁ (k + 1) N) (hg : Def6.l1 g < 1) {j : ℕ}
    (hN : L ^ C.m₀ ∣ N₁) (hj1 : 1 ≤ j) (hjk : j ≤ k)
    {y : CTorus d L N₁ m₁ (k + 1)} (i : Fin N) (hXp : IsPolyDom C.m₀ j X) (hy : y ∈ X)
    (hk : 1 ≤ k) (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    (hconn : HatConn Gp) (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ C.m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hκP : κdec - 1 ≤ P.κ)
    (hchart : ∀ r ∈ XiCRaw (C.Tm.gs j X) (compWeight L a₁) ν j (scaledC0 d)
      (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      Dom.dom j (C.Tm.gs j X) r.1 r.2) :
    ∃ 𝒦X : Set (CTorus d L N₁ m₁ (k + 1)),
      ∀ X₁f : Finset (CTorus d L N₁ m₁ (k + 1)),
        (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp C.m₀ j 𝒦X →
        ∀ (hB : BgSetting N Gp Gk (C.Tm.gs j X) a₁ ν c BG κ r₀ eps δ₃ X₀ X₁f j) (hF : FlSetting N Gp Gk Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl X₁f),
    ∃ Ev : Set (CTorus d L N₁ m₁ (k + 1)) →
          RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gp × Fin N → ℂ) → ℂ,
        (∀ D : BgData Gp N, XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D →
          ∀ ψh : unitPts Gp × Fin N → ℂ, (∀ p, ‖ψh p‖ ≤ cψ) →
          flComp hB hF (fun r => C.Tm.M j y X r.1 r.2 g i)
            (rawOf D, hatLift Gp a₁ ν hG' cc D ψh) =
          ∑ Y ∈ polymerDomains (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1)
            Gp C.m₀ (X1 Gp C.m₀ j 𝒦X), Ev Y (rawOf D, ψh)) ∧
        (∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
            {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
          ∀ u' ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
            {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
          agreeOn Y u.1 u'.1 → (∀ y ∈ Y, ∀ i, u.2 (unitPt hG' y, i) = u'.2 (unitPt hG' y, i)) →
          Ev Y u = Ev Y u') ∧
        (∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
            {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
          ‖Ev Y u‖ ≤ (P.c₉ * ((L : ℝ) ^ j)⁻¹ ^ (((d : ℝ) - 2) / 2 + P.γ - P.α₁)) *
            Real.exp (-κ₀ * treeLenCovOne C.m₀ j X - 2 * κdec * treeLenCov Gp C.m₀ Y)) ∧
        (∀ Y, AnalyticOnNhd ℂ (Ev Y) (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
            {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ})) := by
  obtain ⟨𝒦X, hcov, hopt⟩ := exists_covSetup_of_isPolyDom hG' hN (by omega) hXp
  exact ⟨𝒦X, fun X₁f hX₁ hB hF =>
    classOldDecObs_expansion C hm hcl hc₉ g hg hj1 hjk i hXp hy hB hF hk hG hG' cc hcψ hMX hdm hα hsm
      hδ₁ hcov hX₁ hconn hrow hopt hκ₀ hκdec hκ h1 hlog hκP hchart⟩

end Balaban.Fluctuation
