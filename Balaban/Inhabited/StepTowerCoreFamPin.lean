/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.E0CoeffFamilyRotHat
public import Balaban.Inhabited.E0CoeffFamilyRotAct
public import Balaban.Fluctuation.InteractionSymmSolRot
public import Balaban.Fluctuation.MarkedDecBall
public import Balaban.Fluctuation.MarkedVBlockDec
import Mathlib.Tactic.Linarith

/-!
# Uniqueness of the pinned decoupled maps and of the functionals expanded from them

Two maps `F₁`, `F₁'` pinned by the uniqueness clause of Theorem I-4b agree at every
`(s, rawOf D)` with `‖s‖ < e^κ` and `D` in the chart `Ξ^c`; two maps `Sol`, `Sol'` with `SolSpec`
agree at every strict datum.  Hence the hat field, the masked tangent, the expanded function
`fnOfDec` at the realizable points, and the terms `evTerm`, `evDec` built from `(F₁, Sol)` and
`(F₁', Sol')` coincide (the analogue of the spin covariance `evTermHat_rot`, `evDec_rot_real` for
the identity rotation and two pinned pairs).
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Analysis
  Balaban.Fluctuation Finset Matrix

section Pin

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ} {X₁f : Finset (CTorus d L N₁ m₁ (k + 1))}

/-- **Two pinned background maps agree on the chart.** -/
theorem F₁_unique (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    {F₁ F₁' : DecParams Gp × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    (hF₁ : ∀ (s : DecParams Gp) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
        (α : Gp.Ω 1 → ℂ), IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    (hF₁' : ∀ (s : DecParams Gp) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
        (α : Gp.Ω 1 → ℂ), IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁' (s, rawOf D) = (φ, α))
    {s : DecParams Gp} (hs : ∀ P, ‖s P‖ < Real.exp κ) {D : BgData Gp N}
    (hD : XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D) :
    F₁ (s, rawOf D) = F₁' (s, rawOf D) := by
  obtain ⟨hU, φ, α, hI, hF⟩ := bg_point hC hF₁ hs hD
  rw [hF, hF₁' s D hs hU φ α hI]

/-- **Two fluctuation solution maps with `SolSpec` agree at every strict datum.** -/
theorem Sol_unique
    {Sol Sol' : Dec2.DecParams (coverOf Gp) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    (hSol : SolSpec Gp Hm a₁ ν BG BG₂ κ eps δ₁ Sol)
    (hSol' : SolSpec Gp Hm a₁ ν BG BG₂ κ eps δ₁ Sol')
    {p : Dec2.DecParams (coverOf Gp) × Edat Hm N} (hs : ∀ P, ‖p.1 P‖ < Real.exp κ)
    (he : StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2) :
    Sol p = Sol' p := by
  obtain ⟨hfld, -, -, -, -, huniq⟩ := hSol p hs he
  obtain ⟨hfld', hfix', hs6', -, -, -⟩ := hSol' p hs he
  have hδ : (Sol' p).2 = (Sol p).2 := huniq _ hs6' hfix'
  refine Prod.ext ?_ hδ.symm
  show (Sol p).1 = (Sol' p).1
  rw [hfld, hfld', hδ]

/-- `hatSqrtF` depends on `F₁` only through its value at the datum. -/
theorem hatSqrtF_unique {F₁ F₁' : DecParams Gp × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    {s : DecParams Gp} {Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N}
    (h : F₁ (s, Θ) = F₁' (s, Θ)) :
    hatSqrtF Gp a₁ ν F₁ s Θ = hatSqrtF Gp a₁ ν F₁' s Θ := by
  unfold hatSqrtF
  rw [h]

theorem hatPsiF_unique (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    {F₁ F₁' : DecParams Gp × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    {s : DecParams Gp} {Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N}
    (h : F₁ (s, Θ) = F₁' (s, Θ)) (ψh : unitPts Gp × Fin N → ℂ) :
    hatPsiF Gp a₁ ν hG' cc F₁ s Θ ψh = hatPsiF Gp a₁ ν hG' cc F₁' s Θ ψh := by
  unfold hatPsiF
  rw [hatSqrtF_unique h]

theorem markedHatPsiF_unique (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    {F₁ F₁' : DecParams Gp × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    {s : DecParams Gp} {Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N}
    (h : F₁ (s, Θ) = F₁' (s, Θ)) (Z : Finset (unitPts Gp)) (u t : ℂ)
    (ψh : unitPts Gp × Fin N → ℂ) :
    markedHatPsiF a₁ ν hG' cc F₁ Z u t s Θ ψh = markedHatPsiF a₁ ν hG' cc F₁' Z u t s Θ ψh := by
  simp only [markedHatPsiF_eq_hatPsiF_add]
  rw [hatPsiF_unique hG' cc h, hatSqrtF_unique h]

variable (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
include hC

/-- **The expanded function of a functional of the decoupled objects is the same for two pinned
pairs, at every realizable point.** -/
theorem fnOfDec_unique
    {F₁ F₁' : DecParams Gp × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    (hF₁ : ∀ (s : DecParams Gp) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
        (α : Gp.Ω 1 → ℂ), IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    (hF₁' : ∀ (s : DecParams Gp) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
        (α : Gp.Ω 1 → ℂ), IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁' (s, rawOf D) = (φ, α))
    {Sol Sol' : Dec2.DecParams (coverOf Gp) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    (hSol : SolSpec Gp Hm a₁ ν BG BG₂ κ eps δ₁ Sol)
    (hSol' : SolSpec Gp Hm a₁ ν BG BG₂ κ eps δ₁ Sol')
    {Φ : ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) → (Hm.Ω 1 × Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ}
    {Φ' : ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) → (Hm.Ω 1 × Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ}
    (hΦ : ∀ t ∈ FlRealLC Gp Hm a₁ ν BG κ eps X₁f BG₂ δ₁, Φ t.1 t.2.1 t.2.2 = Φ' t.1 t.2.1 t.2.2)
    {u : RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)}
    (hu : u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ FlBall Hm δ₁)
    (hlc : IsLayerConstant Hm u.2)
    {s : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) → ℂ}
    (hs : s ∈ polydisc (0 : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) → ℂ)
      (fun _ => Real.exp κ)) :
    fnOfDec Gp Hm X₁f F₁ Sol Φ u s = fnOfDec Gp Hm X₁f F₁' Sol' Φ' u s := by
  obtain ⟨⟨D, hD, hDu⟩, hψ⟩ := hu
  obtain ⟨u1, ψ'⟩ := u
  have hs' : ∀ i, ‖s i‖ < Real.exp κ := fun i => by simpa using hs i
  have hE1 : 1 < Real.exp κ := Real.one_lt_exp_iff.2 hC.hκ
  have hsx : ∀ P, ‖extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s P‖ < Real.exp κ :=
    norm_extParams_lt hE1 hs'
  have hs1 := extParams_hs1 (X₁f := X₁f) (Gp := Gp) s
  have hDu' : u1 = rawOf D := hDu
  subst hDu'
  obtain ⟨φ, α, δφ, δα, hI, hF, hstr, hS, hmem⟩ := point_facts_core hC hF₁ hSol hsx hs1 hD hψ
  have hFF := F₁_unique hC hF₁ hF₁' hsx hD
  unfold fnOfDec
  show Φ (F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s, rawOf D))
      (Sol (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s,
        flEdat Gp Hm (F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s, rawOf D))
          (rawOf D).1 ψ')).1 (rawOf D, ψ') =
    Φ' (F₁' (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s, rawOf D))
      (Sol' (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s,
        flEdat Gp Hm (F₁' (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s, rawOf D))
          (rawOf D).1 ψ')).1 (rawOf D, ψ')
  rw [← hFF, hF]
  have hSS : Sol (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s,
      flEdat Gp Hm (φ, α) (rawOf D).1 ψ') =
      Sol' (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s,
      flEdat Gp Hm (φ, α) (rawOf D).1 ψ') := by
    refine Sol_unique hSol hSol' ?_ ?_
    · exact hsx
    · exact hstr
  have hS1 : Sol (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s,
      flEdat Gp Hm (φ, α) (rawOf D).1 ψ') = (δφ, δα) := hS
  rw [hS1, ← hSS, hS1]
  exact hΦ _ ⟨hmem, hlc⟩

/-- **The expansion terms of a hat-variable functional agree for two pinned pairs.** -/
theorem evTermHat_unique (hk : 1 ≤ k)
    (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1)) (cc : ℂ) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    {F₁ F₁' : DecParams Gp × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    (hF₁ : ∀ (s : DecParams Gp) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
        (α : Gp.Ω 1 → ℂ), IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    (hF₁' : ∀ (s : DecParams Gp) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
        (α : Gp.Ω 1 → ℂ), IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁' (s, rawOf D) = (φ, α))
    {Sol Sol' : Dec2.DecParams (coverOf Gp) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    (hSol : SolSpec Gp Hm a₁ ν BG BG₂ κ eps δ₁ Sol)
    (hSol' : SolSpec Gp Hm a₁ ν BG BG₂ κ eps δ₁ Sol')
    {Φ : ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) → (Hm.Ω 1 × Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ}
    {m₀ : ℕ} {X₁ : Set (CTorus d L N₁ m₁ (k + 1))} (Y : Set (CTorus d L N₁ m₁ (k + 1)))
    {D : BgData Gp N} (hD : XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D)
    {ψh : unitPts Gp × Fin N → ℂ} (hψh : ∀ p, ‖ψh p‖ ≤ cψ) :
    evTerm (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) Gp m₀ X₁
      (fun u s => fnOfDec Gp Hm X₁f F₁ Sol Φ
        (u.1, hatPsiF Gp a₁ ν hG' cc F₁
          (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s) u.1 u.2) s) Y
      (rawOf D, ψh) =
    evTerm (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) Gp m₀ X₁
      (fun u s => fnOfDec Gp Hm X₁f F₁' Sol' Φ
        (u.1, hatPsiF Gp a₁ ν hG' cc F₁'
          (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s) u.1 u.2) s) Y
      (rawOf D, ψh) := by
  refine evTerm_congr_polydisc _ (Real.one_lt_exp_iff.2 hC.hκ) X₁ Y fun s hs => ?_
  have hs' : ∀ i, ‖s i‖ < Real.exp κ := fun i => by simpa using hs i
  have hE1 : 1 < Real.exp κ := Real.one_lt_exp_iff.2 hC.hκ
  have hsx : ∀ P, ‖extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s P‖ < Real.exp κ :=
    norm_extParams_lt hE1 hs'
  have hmem := hatPsiF_mem_flBallLC hC hk hG hG' cc hcψ hMX hmar hα hsm hδ₁ hF₁ hsx hD hψh
  have hFF := F₁_unique hC hF₁ hF₁' hsx hD
  show fnOfDec Gp Hm X₁f F₁ Sol Φ (rawOf D, hatPsiF Gp a₁ ν hG' cc F₁
      (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s) (rawOf D) ψh) s =
    fnOfDec Gp Hm X₁f F₁' Sol' Φ (rawOf D, hatPsiF Gp a₁ ν hG' cc F₁'
      (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s) (rawOf D) ψh) s
  rw [← hatPsiF_unique hG' cc hFF]
  refine fnOfDec_unique hC hF₁ hF₁' hSol hSol' (Φ := Φ) (Φ' := Φ) (fun _ _ => rfl)
    (u := (rawOf D, hatPsiF Gp a₁ ν hG' cc F₁
      (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s) (rawOf D) ψh)) ?_ hmem.2 hs
  exact ⟨⟨D, hD, rfl⟩, hmem.1⟩

end Pin

end Balaban.Localization
