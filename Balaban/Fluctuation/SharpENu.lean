/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.InteractionHatE
public import Balaban.Fluctuation.InteractionHatNu
public import Balaban.Fluctuation.SharpEngine
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Sharp locality of the old-energy term and of the mass block

The old-energy summand `E` and the mass-variation block summand `ν` of the localized interaction
expand over the polymer domains `Y` with terms that depend on the hat variable only at the unit
points of the sites of `Y` (the relation `AgHatDir`), the raw data still agreeing on the thick set
of `Y`.  These are the sharp versions of `eterm_expansion_hat` and `nublock_expansion_hat`.

* `eTermFun_local_dir`: `eTermFun_local` with the fluctuation variable assumed equal only on the
  sites of `X₁` (the proof reads it only at data sites, which lie in `X₁`).
* `eterm_expansion_hat_dir`, `nublock_expansion_hat_dir`: one `Ev` with the value identity, both
  locality clauses (landed `AgHat` and sharp `AgHatDir`), the bound and analyticity.

The V and F summands, the assembly (`PhysicalSharpLoc`) and `physical_directTerms` are separate and
not treated here.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Analysis
  Balaban.Fluctuation Finset Matrix Set Metric

section SharpE

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱ₁ ϱ₂ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Gk : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁}
variable {Gj : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₂}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ r₀ eps δ₃ : ℝ} {X₀ X₁f : Finset (CTorus d L N₁ m₁ (k + 1))} {j : ℕ}
variable {Kc Cx c₂ BG₂ δ₁ δfl : ℝ} {m₀ : ℕ} {X 𝒦X : Set (CTorus d L N₁ m₁ (k + 1))}

/-- **Locality of the old-term functional, sharp form**: as `eTermFun_local`, with the fluctuation
variable assumed equal only on the sites of `X₁`. -/
theorem eTermFun_local_dir (hB : BgSetting N Gp Gk Gj a₁ ν c BG κ r₀ eps δ₃ X₀ X₁f j)
    (hF : FlSetting N Gp Gk Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl X₁f)
    (hcov : CovSetup Gp m₀ j X 𝒦X) (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp m₀ j 𝒦X)
    (Fk : RawData d L (N₁ * L ^ m₁) (k + 1) N → (Gk.Ω 1 × Fin N → ℂ) × (Gk.Ω 1 → ℂ))
    (E : RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ)
    {t t' : ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) × (Hm.Ω 1 × Fin N → ℂ) ×
      (RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ))}
    (hφ : ∀ y : Gp.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) →
      ∀ i, t.1.1 (y, i) = t'.1.1 (y, i))
    (hδ : ∀ y : Hm.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) →
      ∀ i, t.2.1 (y, i) = t'.2.1 (y, i))
    (hag : agreeOn (thickSet Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1)))) t.2.2.1 t'.2.2.1)
    (hψ : ∀ y ∈ (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))), t.2.2.2 y = t'.2.2.2 y) :
    eTermFun Gp Gk Gj Hm (compWeight L a₁) Fk E t.1 t.2.1 t.2.2 =
      eTermFun Gp Gk Gj Hm (compWeight L a₁) Fk E t'.1 t'.2.1 t'.2.2 := by
  classical
  have hX₁Ω : (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) ⊆ ↑(Gp.Ω 1) := fun x hx =>
    X1_subset_Omega1 hcov (hX₁ ▸ hx)
  have hXthick : ∀ y ∈ X₁f, t.2.2.1.1 y = t'.2.2.1.1 y ∧ t.2.2.1.2 y = t'.2.2.1.2 y := fun y hy =>
    hag y (Or.inl (Finset.mem_coe.2 hy))
  refine congrArg E (congrArg (D2raw Gk Gj (compWeight L a₁) Fk) ?_)
  refine Prod.ext (funext fun x => funext fun i => ?_) (funext fun x => funext fun i => ?_)
  · show composeField Gk Gp (compWeight L a₁) t.1.1 t.2.2.1.1 x i +
        composeField Gk Hm (compWeight L a₁) t.2.1 t.2.2.2 x i =
      composeField Gk Gp (compWeight L a₁) t'.1.1 t'.2.2.1.1 x i +
        composeField Gk Hm (compWeight L a₁) t'.2.1 t'.2.2.2 x i
    by_cases hx : x ∈ dataSites Gk
    · congr 1
      · refine composeField_congr (G := Gk) (G' := Gp) (compWeight L a₁) (fun y hy jj => ?_)
          (fun jj => congrFun (hXthick x (hB.dep x hx x (self_mem_composeDep x))).1 jj) i
        have hyX := hB.dep x hx y hy
        have hyΩ : y ∈ Gp.Ω 1 := hX₁Ω (Finset.mem_coe.2 hyX)
        rw [svec_of_mem' t.1.1 hyΩ jj, svec_of_mem' t'.1.1 hyΩ jj]
        exact hφ ⟨y, hyΩ⟩ (Finset.mem_coe.2 hyX) jj
      · refine composeField_congr (G := Gk) (G' := Hm) (compWeight L a₁) (fun y hy jj => ?_)
          (fun jj => congrFun (hψ x (Finset.mem_coe.2 (hF.depm x hx x
            (self_mem_composeDep x)))) jj) i
        have hyX := hF.depm x hx y hy
        by_cases hyΩ : y ∈ Hm.Ω 1
        · rw [svec_of_mem' t.2.1 hyΩ jj, svec_of_mem' t'.2.1 hyΩ jj]
          exact hδ ⟨y, hyΩ⟩ (Finset.mem_coe.2 hyX) jj
        · rw [svec_of_not_mem Hm t.2.1 hyΩ jj, svec_of_not_mem Hm t'.2.1 hyΩ jj]
    · rw [composeField_of_not_mem _ _ _ hx, composeField_of_not_mem _ _ _ hx,
        composeField_of_not_mem _ _ _ hx, composeField_of_not_mem _ _ _ hx]
  · show (if x ∈ Gk.Ω 1 then t.2.2.1.2 x i else 0) = (if x ∈ Gk.Ω 1 then t'.2.2.1.2 x i else 0)
    by_cases hx : x ∈ Gk.Ω 1
    · simp only [hx, ↓reduceIte]
      have hxd : x ∈ dataSites Gk := (mem_dataSites Gk).2 (Or.inl hx)
      exact congrFun (hXthick x (hB.dep x hxd x (self_mem_composeDep x))).2 i
    · simp [hx]

/-- **An old term expands over the domains `Y ⊃ X₁`, with terms local in `ψ̂` at the unit points
of `Y` only** (sharp form of `eterm_expansion_hat`; the landed `AgHat` clause is also returned). -/
theorem eterm_expansion_hat_dir (hB : BgSetting N Gp Gk Gj a₁ ν c BG κ r₀ eps δ₃ X₀ X₁f j)
    (hF : FlSetting N Gp Gk Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl X₁f)
    (hk : 1 ≤ k) (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    (hcov : CovSetup Gp m₀ j X 𝒦X) (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp m₀ j 𝒦X)
    (hconn : HatConn Gp) (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
    (hopt : ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X) ∧ MeetsOne m₀ j 𝒦X W₀ ∧
        bondCost (scaleW L m₀ m₁ j) E₀ = treeLenCovOne m₀ j X)
    {κdec κ₀ Eb : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hEb : 0 ≤ Eb) {E : RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ}
    (hEan : AnalyticOnNhd ℂ E (XiCRaw Gj (compWeight L a₁) ν j (scaledC0 d)
      (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)))
    (hEbd : ∀ r ∈ XiCRaw Gj (compWeight L a₁) ν j (scaledC0 d)
      (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      ‖E r‖ ≤ Eb * Real.exp (-(κdec - 1) * treeLenCovOne m₀ j X)) :
    ∃ Ev : Set (CTorus d L N₁ m₁ (k + 1)) →
        RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gp × Fin N → ℂ) → ℂ,
      (∀ D : BgData Gp N, XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D →
        ∀ ψh : unitPts Gp × Fin N → ℂ, (∀ p, ‖ψh p‖ ≤ cψ) →
        flComp hB hF E (rawOf D, hatLift Gp a₁ ν hG' cc D ψh) =
        ∑ Y ∈ polymerDomains (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1)
          Gp m₀ (X1 Gp m₀ j 𝒦X), Ev Y (rawOf D, ψh)) ∧
      (∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        ∀ u' ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        AgHat hG' Y u u' → Ev Y u = Ev Y u') ∧
      (∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        ∀ u' ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        AgHatDir hG' Y u u' → Ev Y u = Ev Y u') ∧
      (∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        ‖Ev Y u‖ ≤ Eb * Real.exp (-κ₀ * treeLenCovOne m₀ j X - 2 * κdec * treeLenCov Gp m₀ Y)) ∧
      (∀ Y, AnalyticOnNhd ℂ (Ev Y) (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ})) := by
  classical
  obtain ⟨Fk, hFkan, hFk⟩ := theorem72_analytic (G := Gk) (a := compWeight L a₁) (ν := ν) hB.HBk
  have hC := flCore_of hB hF
  obtain ⟨Ev, h1', h2', h3', h4'⟩ := i5_functional_hatLC_dir hC hk hG hG' cc hcψ hMX hdm hα hsm hδ₁
    hcov hX₁ hconn hrow hopt hκ₀ hκdec hκ h1 hlog hEb
    (Φ := eTermFun Gp Gk Gj Hm (compWeight L a₁) Fk E)
    (eTermFun_analytic hB hF hFkan hFk hEan)
    (fun t ht => eTermFun_bound hB hF hFk hEbd ht)
    (Z := ↑X₁f) (Zα := ∅) subset_rfl (fun x hx => absurd hx (Set.notMem_empty x))
    (fun t _ t' _ hφ _ hδ hag hψ => eTermFun_local_dir hB hF hcov hX₁ Fk E hφ hδ hag hψ)
  refine ⟨Ev, fun D hD ψh hψh => ?_, fun Y u hu u' hu' h => h2' Y u hu u' hu' (agHatDir_of_agHat hG' h), h2', h3', h4'⟩
  rw [← h1' D hD ψh hψh]
  exact (eTermFun_value hB hF hFk E hD
    (hatLift_mem_flBallLC hC hk hG hG' cc hcψ hMX hdm hα hsm hδ₁ hD hψh)).symm


end SharpE

section SharpNu

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ} {X₁f : Finset (CTorus d L N₁ m₁ (k + 1))} {j : ℕ}
variable {m₀ : ℕ} {X 𝒦X : Set (CTorus d L N₁ m₁ (k + 1))}

/-- **The mass block expands over the domains `Y ⊃ X₁`, with terms local in `ψ̂` at the unit
points of `Y` only** (sharp form of `nublock_expansion_hat`). -/
theorem nublock_expansion_hat_dir (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hk : 1 ≤ k) (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    {Bh : ℝ} (hBh0 : 0 ≤ Bh)
    (hBh : ∀ D : BgData Gp N, XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D →
      ∀ x i, ‖D.h x i‖ ≤ Bh)
    (hcov : CovSetup Gp m₀ j X 𝒦X)
    (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp m₀ j 𝒦X)
    (hconn : HatConn Gp) (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
    (hopt : ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X) ∧ MeetsOne m₀ j 𝒦X W₀ ∧
        bondCost (scaleW L m₀ m₁ j) E₀ = treeLenCovOne m₀ j X)
    (hΔ : treeLenCovOne m₀ j X = 0)
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))))
    (hZ : (↑(blockSites d L N₁ m₁ (k + 1) k z) : Set (CTorus d L N₁ m₁ (k + 1))) ⊆ ↑X₁f) :
    ∃ Ev : Set (CTorus d L N₁ m₁ (k + 1)) →
        RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gp × Fin N → ℂ) → ℂ,
      (∀ D : BgData Gp N, XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D →
        ∀ ψh : unitPts Gp × Fin N → ℂ, (∀ p, ‖ψh p‖ ≤ cψ) →
        nuBlockFun Gp Hm k z (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D,
            bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D)
          (flFieldOne Gp Hm BG₂ κ a₁ ν D (hatLift Gp a₁ ν hG' cc D ψh))
          (rawOf D, hatLift Gp a₁ ν hG' cc D ψh) =
          ∑ Y ∈ polyDom Gp X₁f m₀ j 𝒦X, Ev Y (rawOf D, ψh)) ∧
      (∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        ∀ u' ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        AgHat hG' Y u u' → Ev Y u = Ev Y u') ∧
      (∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        ∀ u' ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        AgHatDir hG' Y u u' → Ev Y u = Ev Y u') ∧
      (∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        ‖Ev Y u‖ ≤ nuBd d L N k (cK2' d L N (famConst d L BG₂ κ) * δ₁)
          (K4 d L N BG κ * (xiC1 d * eps) + (1 + 3 * (xiC1 d * eps)) + Bh) *
          Real.exp (-2 * κdec * treeLenCov Gp m₀ Y)) ∧
      (∀ Y, AnalyticOnNhd ℂ (Ev Y) (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ})) := by
  have hd0 : 0 < d := by have := hC.HBp.hd; omega
  have hB0 : 0 ≤ famConst d L BG₂ κ := by
    have := famConst_ge_one (L := L) hC.hS2.fam.2.1 κ hd0; linarith
  have hV : 0 ≤ cK2' d L N (famConst d L BG₂ κ) * δ₁ :=
    mul_nonneg (cK2'_nonneg hB0) hC.δ₁_pos.le
  have hB1 : 0 ≤ K4 d L N BG κ * (xiC1 d * eps) + (1 + 3 * (xiC1 d * eps)) + Bh := by
    have hK4 : 0 < K4 d L N BG κ := K4_pos (L := L) (N := N) (κ := κ) hC.hS.fam.2.1 hd0
    have hx1 := one_le_xiC1 d
    have hx2 := hC.eps_pos
    have hx3 : 0 ≤ xiC1 d * eps := by positivity
    have hx4 := mul_nonneg hK4.le hx3
    linarith
  have hEb : 0 ≤ nuBd d L N k (cK2' d L N (famConst d L BG₂ κ) * δ₁)
      (K4 d L N BG κ * (xiC1 d * eps) + (1 + 3 * (xiC1 d * eps)) + Bh) := by
    unfold nuBd; positivity
  obtain ⟨Ev, h1', h2', h3', h4'⟩ := i5_functional_hat_dir hC hk hG hG' cc hcψ hMX hdm hα hsm hδ₁ hcov
    hX₁ hconn hrow hopt hκ₀ hκdec hκ h1 hlog hEb (Φ := nuBlockFun Gp Hm k z)
    ((nuBlockFun_analytic (Gp := Gp) (Hm := Hm) k z).mono (Set.subset_univ _))
    (fun t ht => by
      rw [hΔ]; simpa using nuBlockFun_bound hC le_rfl hG' hBh0 hBh z ht)
    (Z := ↑(blockSites d L N₁ m₁ (k + 1) k z)) (Zα := ∅) hZ
    (fun x hx => absurd hx (Set.notMem_empty x))
    (fun t _ t' _ hφ _ hδ hag _ => nuBlockFun_local k z hφ hδ hag)
  refine ⟨Ev, h1', fun Y u hu u' hu' h => h2' Y u hu u' hu' (agHatDir_of_agHat hG' h), h2', fun Y u hu => ?_, h4'⟩
  have := h3' Y u hu
  rw [hΔ] at this
  simpa using this

end SharpNu

end Balaban.Localization
