/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.HoleStepOldLocal
public import Balaban.Fluctuation.LocalPairHatLift

/-!
# The standing conditions of the step on a region from the chart of its datum

The locality of the re-expansion of an old boundary term (`HoleStep.oldInterp_localityAEOn`) uses,
at every localization vector `v` of the polydisc, the standing conditions of the decoupled objects
of the pair `(coverOf G′, G′)`: the datum in the domain of Theorem I-4b, `AdmPot` of the decoupled
multiplier, and the invertibility of `1 - 𝒦_x` and of `M_x` for `x > 0`.  All of them follow from the
datum of the step lying in the chart `Ξ^c(G′; 1, ε)` (`XiCData`), with the numerical conditions of
Theorems I-4b and I-4c (`coverBg_exists`, `decDom_of_coverBg`, `xData_cover_of_mem`,
`decM_isUnit_cover`), as in `localHatLift_eq_hatPsiF`.

* `decM_svec_eq_barField`: `M_x` sees the field only on `Ω₁`;
* `HoleStep.standing_of_xiCData`: **the standing conditions at a vector of the open polydisc of
  radius `e^κ`**;
* `HoleStep.oldInterp_localityAEOn_of_xiCData`: (AE2) for the interpolated old term with the analytic
  hypotheses reduced to the datum in the chart (the remaining analytic input is the image of the
  target H7 domain in the chart, OPEN-H7-MIXED);
* `HoleStep.standing_of_inDomainC`, `HoleStep.oldInterp_localityAEOn_of_inDomainC`: the same from the
  weaker hypothesis that the datum lies in the domain `Ψ̃^c(δ, δ)` of Theorem I-4b
  (`decDom_of_bgBounds`).
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.LargeField
  Balaban.SmallField

section Field

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}

/-- The constraint matrix `M_x` sees the field only on `Ω₁`: the zero extension and the extension by
the data give the same matrix. -/
theorem decM_svec_eq_barField (a : ℕ → ℝ) (aT x ν : ℝ) (α : G.Ω 1 → ℂ)
    (s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ) (Ψ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)
    (φ : G.Ω 1 × Fin N → ℂ) :
    Balaban.Localization.decM G a aT x ν α s (svec G φ) =
      Balaban.Localization.decM G a aT x ν α s (barField G Ψ φ) := by
  have h : restrictField G (svec G φ) = restrictField G (barField G Ψ φ) := by
    funext y i
    simp only [restrictField]
    rw [svec_of_mem G φ y i]
    simp [barField, y.2]
  unfold Balaban.Localization.decM
  rw [h]

end Field

namespace HoleStep

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱ' : ℝ}
  (S : HoleStep d L N₁ m₁ k N ϱ ϱ')

/-- **The standing conditions of the decoupled objects at a localization vector**, from the datum of
the step in the chart `Ξ^c(G′; 1, ε)` (Theorems I-4b, I-4c for the pair `(coverOf G′, G′)`). -/
theorem standing_of_xiCData {Kc Cx Cx₂ c BG eps δc : ℝ} (hS : Dec2.DecSpecs d L Kc Cx c BG)
    (Sb : Dec2.CoverBase (coverOf S.G') S.G' (compWeight L S.a₁) S.ν Kc Cx)
    (SX : Dec2.XCover (coverOf S.G') S.G' (compWeight L S.a₁) S.a₁ S.ν Cx₂) (hCx₂ : 0 ≤ Cx₂)
    (HB : BgHyp d L (k + 1) ϱ' (compWeight L S.a₁) S.ν) {κ : ℝ} (hκ : 0 ≤ κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hMX : Dec2.cstarX d L Cx₂ * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (heps : 0 < eps) (hsmall : (4 * d + 6) * ((2 * d + 1) * eps) ≤ 1)
    (hc7 : xiC1 d * eps ≤ c7 d L N BG κ) (hphi : (3 + K4 d L N BG κ) * (xiC1 d * eps) < 1 / 2)
    (hmarD : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hαD : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hD : XiCData S.G' (compWeight L S.a₁) S.ν (k + 1) 1 eps S.D')
    {v : Dec2.DecParams (coverOf S.G')} (hv : ∀ P, ‖v P‖ < Real.exp κ) :
    AdmPot S.G' (Dec2.decBgMult (coverOf S.G') S.G' S.a S.ν (rho4 d L N BG κ) v S.D') ∧
      (∀ x : ℝ, 0 < x → IsUnit (1 - Dec2.Kcalx (coverOf S.G') S.G' S.a S.a₁ x S.ν
        (Dec2.decBgMult (coverOf S.G') S.G' S.a S.ν (rho4 d L N BG κ) v S.D') (Dec2.extS _ v))) ∧
      (∀ x : ℝ, 0 < x → IsUnit (Dec2.decM (coverOf S.G') S.G' S.a S.a₁ x S.ν
        (Dec2.decBgMult (coverOf S.G') S.G' S.a S.ν (rho4 d L N BG κ) v S.D') (Dec2.extS _ v)
        (svec S.G' (Dec2.decBgField (coverOf S.G') S.G' S.a S.ν (rho4 d L N BG κ) v S.D')))) := by
  obtain ⟨φ, α, hI, hu, -⟩ := coverBg_exists hS Sb HB hκ hM heps hsmall hc7 hv hD
  have hI2 : Dec2.IsDecBg (coverOf S.G') S.G' S.a S.ν (rho4 d L N BG κ) v S.D' φ α :=
    ⟨hI.small, hI.fixed, hI.field⟩
  have hu2 : ∀ φ' α', Dec2.IsDecBg (coverOf S.G') S.G' S.a S.ν (rho4 d L N BG κ) v S.D' φ' α' →
      φ' = φ ∧ α' = α := fun φ' α' h => hu φ' α' ⟨h.small, h.fixed, h.field⟩
  obtain ⟨hφe, hαe⟩ := Dec2.decBg_eq hI2 hu2
  rw [hφe, hαe]
  have hdom := decDom_of_coverBg hS Sb HB hκ hM heps hsmall hc7 hphi hv hD hI hmarD hαD
  have hδc : 0 ≤ δc := by
    have hd0 : 0 < d := by have := HB.hd; omega
    have : 0 ≤ decDomMargin d L N BG κ (xiC1 d * eps) := by
      have : 0 < K4 d L N BG κ := K4_pos hS.fam.2.1 hd0
      have h1 := one_le_xiC1 d
      unfold decDomMargin; positivity
    linarith
  have hXD : ∀ x : ℝ, 0 < x → Dec2.XData (coverOf S.G') S.G' (compWeight L S.a₁) S.a₁ S.ν x α κ
      (extS S.G' v) Cx₂ := fun x hx => xData_cover_of_mem SX hCx₂ hx.le hκ hMX hdom
  refine ⟨fun w => (hdom.2.2 w).le, fun x hx => (hXD x hx).isUnit_one_sub, fun x hx => ?_⟩
  have h1 := decM_isUnit_cover (hXD x hx) hdom.2.1.toIsConstraintField hδc hsm
  rw [Dec2.decM_self]
  have h2 := decM_svec_eq_barField (G := S.G') S.a S.a₁ x S.ν α (Dec2.extS (coverOf S.G') v)
    S.D'.Ψ φ
  rw [h2]
  exact h1

/-- **The standing conditions of the decoupled objects at a localization vector, from the background
domain of the datum** (`S.D' ∈ Ψ̃^c(δ, δ)`, the domain of Theorem I-4b, with the numerical conditions of
`decDom_of_bgBounds`; weaker than the chart `Ξ^c`, `xiCData_inDomainC`). -/
theorem standing_of_inDomainC {Kc Cx Cx₂ c BG δ δc : ℝ} (hS : Dec2.DecSpecs d L Kc Cx c BG)
    (Sb : Dec2.CoverBase (coverOf S.G') S.G' (compWeight L S.a₁) S.ν Kc Cx)
    (SX : Dec2.XCover (coverOf S.G') S.G' (compWeight L S.a₁) S.a₁ S.ν Cx₂) (hCx₂ : 0 ≤ Cx₂)
    (HB : BgHyp d L (k + 1) ϱ' (compWeight L S.a₁) S.ν) {κ : ℝ} (hκ : 0 ≤ κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hMX : Dec2.cstarX d L Cx₂ * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hδ0 : 0 < δ) (hε : δ ≤ bgC0 d L N) (hδ : δ ≤ c7 d L N BG κ)
    (hνε : S.ν * ((L : ℝ) ^ (k + 1)) ^ 2 * δ ^ 2 ≤ δ ^ 2)
    (hphi : 3 * δ + K4 d L N BG κ * δ < 1 / 2)
    (hmarD : K4 d L N BG κ * δ + 2 * δ + K4 d L N BG κ * δ * (K4 d L N BG κ * δ + 2 * (1 + 3 * δ))
      < δc)
    (hαD : K4 d L N BG κ * δ < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hD : InDomainC S.G' S.ν δ δ S.D')
    {v : Dec2.DecParams (coverOf S.G')} (hv : ∀ P, ‖v P‖ < Real.exp κ) :
    AdmPot S.G' (Dec2.decBgMult (coverOf S.G') S.G' S.a S.ν (rho4 d L N BG κ) v S.D') ∧
      (∀ x : ℝ, 0 < x → IsUnit (1 - Dec2.Kcalx (coverOf S.G') S.G' S.a S.a₁ x S.ν
        (Dec2.decBgMult (coverOf S.G') S.G' S.a S.ν (rho4 d L N BG κ) v S.D') (Dec2.extS _ v))) ∧
      (∀ x : ℝ, 0 < x → IsUnit (Dec2.decM (coverOf S.G') S.G' S.a S.a₁ x S.ν
        (Dec2.decBgMult (coverOf S.G') S.G' S.a S.ν (rho4 d L N BG κ) v S.D') (Dec2.extS _ v)
        (svec S.G' (Dec2.decBgField (coverOf S.G') S.G' S.a S.ν (rho4 d L N BG κ) v S.D')))) := by
  obtain ⟨φ, α, hI, hu, -, -, hbb⟩ := Dec2.i4b_exists_unique hS Sb HB hκ hM (fun P => (hv P).le)
    hδ0 le_rfl hε hδ hνε hD
  obtain ⟨hφe, hαe⟩ := Dec2.decBg_eq hI hu
  rw [hφe, hαe]
  have hd0 : 0 < d := by have := HB.hd; omega
  have hK4 : 0 < K4 d L N BG κ := K4_pos hS.fam.2.1 hd0
  have hB4 : 0 < K4 d L N BG κ * δ := mul_pos hK4 hδ0
  have hdom : (v, (barField S.G' S.D'.Ψ φ, α)) ∈ DecDom S.G' N κ δc :=
    decDom_of_bgBounds (c := K4 d L N BG κ * δ) hδ0.le hB4.le hD hbb (by linarith) hmarD hαD hv
  have hδc : 0 ≤ δc := by nlinarith
  have hXD : ∀ x : ℝ, 0 < x → Dec2.XData (coverOf S.G') S.G' (compWeight L S.a₁) S.a₁ S.ν x α κ
      (extS S.G' v) Cx₂ := fun x hx => xData_cover_of_mem SX hCx₂ hx.le hκ hMX hdom
  refine ⟨fun w => (hdom.2.2 w).le, fun x hx => (hXD x hx).isUnit_one_sub, fun x hx => ?_⟩
  have h1 := decM_isUnit_cover (hXD x hx) hdom.2.1.toIsConstraintField hδc hsm
  rw [Dec2.decM_self]
  have h2 := decM_svec_eq_barField (G := S.G') S.a S.a₁ x S.ν α (Dec2.extS (coverOf S.G') v)
    S.D'.Ψ φ
  rw [h2]
  exact h1

/-- **(AE2) for the interpolated old term, from the chart of the datum** (OPEN-P6-ACTIVE-COMPOSITE-LOC
under R12, with the analytic hypotheses reduced to `S.D' ∈ Ξ^c(G′; 1, ε)` and the numerical conditions
of Theorems I-4b, I-4c; parameters in the polydisc of radius `R`, `1 ≤ R < e^κ`). -/
theorem oldInterp_localityAEOn_of_xiCData {Kc Cx Cx₂ c BG eps δc : ℝ}
    (hS : Dec2.DecSpecs d L Kc Cx c BG)
    (Sb : Dec2.CoverBase (coverOf S.G') S.G' (compWeight L S.a₁) S.ν Kc Cx)
    (SX : Dec2.XCover (coverOf S.G') S.G' (compWeight L S.a₁) S.a₁ S.ν Cx₂) (hCx₂ : 0 ≤ Cx₂)
    (HB : BgHyp d L (k + 1) ϱ' (compWeight L S.a₁) S.ν) {κ : ℝ} (hκ : 0 ≤ κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hMX : Dec2.cstarX d L Cx₂ * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (heps : 0 < eps) (hsmall : (4 * d + 6) * ((2 * d + 1) * eps) ≤ 1)
    (hc7 : xiC1 d * eps ≤ c7 d L N BG κ) (hphi : (3 + K4 d L N BG κ) * (xiC1 d * eps) < 1 / 2)
    (hmarD : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hαD : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4) (hνL : S.ν * ((L : ℝ) ^ (k + 1)) ^ 2 ≤ 1)
    (hD : XiCData S.G' (compWeight L S.a₁) S.ν (k + 1) 1 eps S.D')
    {D : ℕ} (hDD : L ^ (k + 1) + 2 * L ^ (k + 1) ≤ D)
    (X₁loc : S.U → Finset (CTorus d L N₁ m₁ (k + 1))) (X₁ : Finset (CTorus d L N₁ m₁ (k + 1)))
    (inner : Finset S.U) (ψout : S.U → Fin N → ℂ) {B : (S.U → Fin N → ℂ) → ℂ} {Rd : Finset S.U}
    (hB : ∀ c c' : S.U → Fin N → ℂ, (∀ b ∈ Rd, c b = c' b) → B c = B c')
    {R : ℝ} (hR1 : 1 ≤ R) (hRk : R < Real.exp κ)
    (hcov : ∀ b ∈ Rd, ∃ q ∈ (coverOf S.G').cubeIdx,
      (unitRep b : CTorus d L N₁ m₁ (k + 1)) ∈ intBox q ∧
        ∀ P ∈ (coverOf S.G').Qset q, cubeP P ⊆ X₁ ∧ cubeP P ⊆ X₁loc b)
    (hlocdeep : ∀ b ∈ Rd, ∀ q ∈ (coverOf S.G').cubeIdx,
      (∀ P ∈ (coverOf S.G').Qset q, cubeP P ⊆ X₁loc b) → ∀ x ∈ intBox q,
        ∀ z : CTorus d L N₁ m₁ (k + 1), supDist x z ≤ 4 * L ^ (k + 1) → z ∈ S.G'.Ω 1) :
    LocalityAEOn R Set.univ
      (fun P : (coverOf S.G').cubeIdx =>
        (cubeP (P : ℕ × CTorus d L N₁ m₁ (k + 1)) : Set (CTorus d L N₁ m₁ (k + 1))))
      (S.reachSet (coverOf S.G') X₁loc X₁ D Rd) (S.AgreeReach (coverOf S.G') X₁loc X₁ D Rd inner)
      (fun ψin w => S.oldInterp (coverOf S.G') (rho4 d L N BG κ) X₁loc X₁ inner ψout B ψin w) := by
  have hd0 : 0 < d := by have := HB.hd; omega
  have hδ0 : 0 < xiC1 d * eps := mul_pos (lt_of_lt_of_le one_pos (one_le_xiC1 d)) heps
  have hε : xiC1 d * eps ≤ bgC0 d L N :=
    hc7.trans ((c7_le_bgC1 d L N BG κ).trans (bgC1_le_bgC0 d L N hd0))
  have hνε : S.ν * ((L : ℝ) ^ (k + 1)) ^ 2 * (xiC1 d * eps) ^ 2 ≤ (xiC1 d * eps) ^ 2 :=
    mul_le_of_le_one_left (sq_nonneg _) hνL
  exact oldInterp_localityAEOn hS Sb SX HB hκ hM hδ0 le_rfl hε hc7 hνε
    (xiCData_inDomainC HB hsmall hD) hDD X₁loc X₁ inner ψout hB hR1 hRk.le
    (fun v hv => S.standing_of_xiCData hS Sb SX hCx₂ HB hκ hM hMX heps hsmall hc7 hphi hmarD hαD
      hsm hD fun P => (hv P).trans_lt hRk) hcov hlocdeep

/-- **(AE2) for the interpolated old term, from the background domain of the datum**
(OPEN-P6-ACTIVE-COMPOSITE-LOC under R12, with the analytic hypotheses reduced to
`S.D' ∈ Ψ̃^c(δ, δ)` and the numerical conditions of Theorems I-4b, I-4c). -/
theorem oldInterp_localityAEOn_of_inDomainC {Kc Cx Cx₂ c BG δ δc : ℝ}
    (hS : Dec2.DecSpecs d L Kc Cx c BG)
    (Sb : Dec2.CoverBase (coverOf S.G') S.G' (compWeight L S.a₁) S.ν Kc Cx)
    (SX : Dec2.XCover (coverOf S.G') S.G' (compWeight L S.a₁) S.a₁ S.ν Cx₂) (hCx₂ : 0 ≤ Cx₂)
    (HB : BgHyp d L (k + 1) ϱ' (compWeight L S.a₁) S.ν) {κ : ℝ} (hκ : 0 ≤ κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hMX : Dec2.cstarX d L Cx₂ * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hδ0 : 0 < δ) (hε : δ ≤ bgC0 d L N) (hδ : δ ≤ c7 d L N BG κ)
    (hphi : 3 * δ + K4 d L N BG κ * δ < 1 / 2)
    (hmarD : K4 d L N BG κ * δ + 2 * δ + K4 d L N BG κ * δ * (K4 d L N BG κ * δ + 2 * (1 + 3 * δ))
      < δc)
    (hαD : K4 d L N BG κ * δ < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4) (hνL : S.ν * ((L : ℝ) ^ (k + 1)) ^ 2 ≤ 1)
    (hD : InDomainC S.G' S.ν δ δ S.D')
    {D : ℕ} (hDD : L ^ (k + 1) + 2 * L ^ (k + 1) ≤ D)
    (X₁loc : S.U → Finset (CTorus d L N₁ m₁ (k + 1))) (X₁ : Finset (CTorus d L N₁ m₁ (k + 1)))
    (inner : Finset S.U) (ψout : S.U → Fin N → ℂ) {B : (S.U → Fin N → ℂ) → ℂ} {Rd : Finset S.U}
    (hB : ∀ c c' : S.U → Fin N → ℂ, (∀ b ∈ Rd, c b = c' b) → B c = B c')
    {R : ℝ} (hR1 : 1 ≤ R) (hRk : R < Real.exp κ)
    (hcov : ∀ b ∈ Rd, ∃ q ∈ (coverOf S.G').cubeIdx,
      (unitRep b : CTorus d L N₁ m₁ (k + 1)) ∈ intBox q ∧
        ∀ P ∈ (coverOf S.G').Qset q, cubeP P ⊆ X₁ ∧ cubeP P ⊆ X₁loc b)
    (hlocdeep : ∀ b ∈ Rd, ∀ q ∈ (coverOf S.G').cubeIdx,
      (∀ P ∈ (coverOf S.G').Qset q, cubeP P ⊆ X₁loc b) → ∀ x ∈ intBox q,
        ∀ z : CTorus d L N₁ m₁ (k + 1), supDist x z ≤ 4 * L ^ (k + 1) → z ∈ S.G'.Ω 1) :
    LocalityAEOn R Set.univ
      (fun P : (coverOf S.G').cubeIdx =>
        (cubeP (P : ℕ × CTorus d L N₁ m₁ (k + 1)) : Set (CTorus d L N₁ m₁ (k + 1))))
      (S.reachSet (coverOf S.G') X₁loc X₁ D Rd) (S.AgreeReach (coverOf S.G') X₁loc X₁ D Rd inner)
      (fun ψin w => S.oldInterp (coverOf S.G') (rho4 d L N BG κ) X₁loc X₁ inner ψout B ψin w) := by
  have hνε : S.ν * ((L : ℝ) ^ (k + 1)) ^ 2 * δ ^ 2 ≤ δ ^ 2 :=
    mul_le_of_le_one_left (sq_nonneg _) hνL
  exact oldInterp_localityAEOn hS Sb SX HB hκ hM hδ0 le_rfl hε hδ hνε hD hDD X₁loc X₁ inner ψout hB
    hR1 hRk.le
    (fun v hv => S.standing_of_inDomainC hS Sb SX hCx₂ HB hκ hM hMX hδ0 hε hδ hνε hphi hmarD hαD hsm
      hD fun P => (hv P).trans_lt hRk) hcov hlocdeep

end HoleStep

end Balaban.Fluctuation
