/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.LocalHatCov
public import Balaban.Fluctuation.FlCoreCover
public import Balaban.Fluctuation.HatEngineDom
public import Balaban.Localization.I5FluctFan
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The local decoupled background lies in the decoupled domain; the local hat lift is analytic

For the pair `(coverOf G, G)` (no `DGSetting`), with `G` the literal local generator
`𝔹(Y) = localB j hj Y hsep` in the main application:

* `decDom_of_coverBg`: the cover form of `decDom_of_isDecBg`.  The decoupled background `(φ, α)`
  of a datum of the chart at a realizable `s` gives `(s, (φ̄, α)) ∈ DecDom G N κ δc`.
* `analyticAt_localLift`: the extension by zero of a field on the unit lattice of `G`, lifted to
  the fine lattice, is linear, hence analytic in analytic arguments.
* `analyticAt_localHatLift_of_decDom`: the cover form of `analyticAt_hatPsi_of_decDom`: the local
  hat lift `ψ' = cc C^{1/2}(s) ψ̂` is analytic in the datum at every point of `DecDom`.
* `localB_analyticAt_localHatLift_of_decDom`: the instance at `localB j hj Y hsep`.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.LargeField Finset Matrix

section LocalDom

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {a₁ ν Kc Cx c BG κ eps δc : ℝ}

/-- **The decoupled background of the cover pair lies in `DecDom`** (cover form of
`decDom_of_isDecBg`, from `Dec2.CoverBase (coverOf G) G`, no `DGSetting`): for a datum
`D ∈ Ξ^c(G; 1, ε)`, parameters `s` with `|s_P| < e^κ` and `(φ, α)` the decoupled background of `D`
at `s`, the point `(s, (φ̄, α))` lies in `DecDom G N κ δc` once `δc` exceeds the margin
`decDomMargin` and `K₄ δ < γ/2`. -/
theorem decDom_of_coverBg {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
    (hS : Dec2.DecSpecs d L Kc Cx c BG) (S : Dec2.CoverBase (coverOf G) G (compWeight L a₁) ν Kc Cx)
    (HBp : BgHyp d L (k + 1) ϱ (compWeight L a₁) ν) (hκ : 0 ≤ κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) (heps : 0 < eps)
    (hsmall : (4 * d + 6) * ((2 * d + 1) * eps) ≤ 1) (hc7 : xiC1 d * eps ≤ c7 d L N BG κ)
    (hphi : (3 + K4 d L N BG κ) * (xiC1 d * eps) < 1 / 2) {s : DecParams G}
    (hs : ∀ P, ‖s P‖ < Real.exp κ) {D : BgData G N}
    (hD : XiCData G (compWeight L a₁) ν (k + 1) 1 eps D) {φ : G.Ω 1 × Fin N → ℂ}
    {α : G.Ω 1 → ℂ} (hI : IsDecBg G (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α)
    (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2) :
    (s, (barField G D.Ψ φ, α)) ∈ DecDom G N κ δc := by
  have hd0 : 0 < d := by have := HBp.hd; omega
  have hc1 := one_le_xiC1 d
  have hδ0 : 0 < xiC1 d * eps := by positivity
  have hDom := xiCData_inDomainC HBp hsmall hD
  obtain ⟨φ', α', hI', hu', hbb⟩ := coverBg_exists hS S HBp hκ hM heps hsmall hc7 hs hD
  obtain ⟨rfl, rfl⟩ := hu' φ α hI
  have hK4 : 0 < K4 d L N BG κ := K4_pos hS.fam.2.1 hd0
  have hB4 : 0 < K4 d L N BG κ * (xiC1 d * eps) := mul_pos hK4 hδ0
  refine decDom_of_bgBounds (c := K4 d L N BG κ * (xiC1 d * eps)) hδ0.le hB4.le hDom hbb ?_
    ?_ hα hs
  · nlinarith
  · unfold decDomMargin at hmar; nlinarith

end LocalDom

section LocalLift

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Q : Type*} [NormedAddCommGroup Q] [NormedSpace ℂ Q]

/-- **Analyticity of the local lift**: the extension by zero of a field on the unit lattice of `G`,
lifted to the fine lattice, is analytic in `q` when the field is. -/
theorem analyticAt_localLift {q : Q} {V : Q → unitPts G × Fin N → ℂ}
    (hV : ∀ r, AnalyticAt ℂ (fun q => V q r) q) :
    AnalyticAt ℂ (fun q => fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
      if h : unitBlock x ∈ unitPts G then V q (⟨unitBlock x, h⟩, i) else 0) q := by
  refine analyticAt_pi_iff.2 fun x => analyticAt_pi_iff.2 fun i => ?_
  by_cases h : unitBlock x ∈ unitPts G
  · simp only [h, dite_true]
    exact hV _
  · simp only [h, dite_false]
    exact analyticAt_const

end LocalLift

section LocalAnalytic

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {a : ℕ → ℝ} {aT ν Cx κ δc : ℝ}
variable {Q : Type*} [NormedAddCommGroup Q] [NormedSpace ℂ Q]

/-- **Analyticity of the local hat lift in the datum** (cover form of
`analyticAt_hatPsi_of_decDom`, from `Dec2.XCover (coverOf G) G`): if `(s, (φ̄, α))` lies in
`DecDom` at `q` and `s, Ψ, φ, α, ψ̂` are analytic in `q`, then
`q ↦ (cc C^{1/2}(s) ψ̂)` extended by zero off the unit blocks of `G` and lifted to the fine
lattice is analytic at `q`. -/
theorem analyticAt_localHatLift_of_decDom (S : Dec2.XCover (coverOf G) G a aT ν Cx)
    (hCx : 0 ≤ Cx) (hκ : 0 ≤ κ)
    (hM : Dec2.cstarX d L Cx * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) (hδ : 0 ≤ δc)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4) (cc : ℂ) {q : Q}
    {sF : Q → DecParams G} {ΨF : Q → CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ}
    {φF : Q → G.Ω 1 × Fin N → ℂ} {αF : Q → G.Ω 1 → ℂ} {ψh : Q → unitPts G × Fin N → ℂ}
    (hs : ∀ P, AnalyticAt ℂ (fun q => sF q P) q)
    (hΨ : ∀ y j, AnalyticAt ℂ (fun q => ΨF q y j) q)
    (hφ : ∀ r, AnalyticAt ℂ (fun q => φF q r) q) (hα : ∀ y, AnalyticAt ℂ (fun q => αF q y) q)
    (hψ : ∀ r, AnalyticAt ℂ (fun q => ψh q r) q)
    (hmem : (sF q, (barField G (ΨF q) (φF q), αF q)) ∈ DecDom G N κ δc) :
    AnalyticAt ℂ (fun q => fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
      if h : unitBlock x ∈ unitPts G then
        (cc • (decCovSqrt G a aT ν (αF q) (extS G (sF q)) (barField G (ΨF q) (φF q))
          (unitQ G) (unitP G) *ᵥ ψh q)) (⟨unitBlock x, h⟩, i)
      else 0) q := by
  classical
  have hbar := analyticAt_barField (Gp := G) φF ΨF hφ hΨ
  have he : AnalyticAt ℂ (fun q => (sF q, (barField G (ΨF q) (φF q), αF q))) q :=
    AnalyticAt.prod (analyticAt_pi_iff.2 hs) (hbar.prod (analyticAt_pi_iff.2 hα))
  have hU := (isUnitLatticeB_unit (G := G)).toIsUnitLattice
  have hent : ∀ p r, AnalyticAt ℂ (fun q => decCovSqrt G a aT ν (αF q)
      (extS G (sF q)) (barField G (ΨF q) (φF q)) (unitQ G) (unitP G) p r) q := by
    intro p r
    have hg : AnalyticAt ℂ (fun e : DecData G N =>
        decCovSqrt G a aT ν e.2.2 (extS G e.1) e.2.1 (unitQ G) (unitP G) p r)
        (sF q, (barField G (ΨF q) (φF q), αF q)) :=
      analyticOnNhd_decCovSqrt_entry_cover (N := N) S hCx hκ hM hδ hsm hU p r _ hmem
    exact AnalyticAt.comp (f := fun q => (sF q, (barField G (ΨF q) (φF q), αF q))) hg he
  refine analyticAt_localLift (V := fun q => cc • (decCovSqrt G a aT ν (αF q)
      (extS G (sF q)) (barField G (ΨF q) (φF q)) (unitQ G) (unitP G) *ᵥ ψh q)) fun r => ?_
  simp only [Pi.smul_apply, Matrix.mulVec, dotProduct, smul_eq_mul]
  exact analyticAt_const.mul (Finset.analyticAt_fun_sum _ fun t _ => (hent r t).mul (hψ t))

end LocalAnalytic

section LocalB

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {a₁ ν Kc c BG κ eps δc : ℝ}

/-- **The local decoupled background lies in `DecDom`** (instance of `decDom_of_coverBg` at the
literal local generator `𝔹(Y) = localB j hj Y hsep`, with the cover base `localB_coverBase`, from
the constants `mixedKc d L`, `Cchi d L`): the point `(s, (φ̄, α))` built from the decoupled
background of a datum of `Ξ^c(𝔹(Y); 1, ε)` is in `DecDom 𝔹(Y) N κ δc`.  The datum `e` of
`localB_localHatLift_mem_flBallLC` can be taken to be this point. -/
theorem localB_decDom_of_coverBg {j : ℕ} (hj : j ≤ k + 1) (Y : Set (CTorus d L N₁ m₁ (k + 1)))
    (hsep : ϱ ≤ minSep L (L ^ m₁)) (hN₁ : 5 < N₁) (hMM : 4 * L ^ 2 ≤ L ^ m₁)
    (hS : Dec2.DecSpecs d L (Dec2.mixedKc d L) (Cchi d L) c BG)
    (HBp : BgHyp d L (k + 1) ϱ (compWeight L a₁) ν)
    (hag : 2 * d * Real.log L ≤ agmonRate d / 16 * (ϱ - 1)) (hκ : 0 ≤ κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) (heps : 0 < eps)
    (hsmall : (4 * d + 6) * ((2 * d + 1) * eps) ≤ 1) (hc7 : xiC1 d * eps ≤ c7 d L N BG κ)
    (hphi : (3 + K4 d L N BG κ) * (xiC1 d * eps) < 1 / 2)
    {s : DecParams (SmallField.GsSpec.localB j hj Y hsep)} (hs : ∀ P, ‖s P‖ < Real.exp κ)
    {D : BgData (SmallField.GsSpec.localB j hj Y hsep) N}
    (hD : XiCData (SmallField.GsSpec.localB j hj Y hsep) (compWeight L a₁) ν (k + 1) 1 eps D)
    {φ : (SmallField.GsSpec.localB j hj Y hsep).Ω 1 × Fin N → ℂ}
    {α : (SmallField.GsSpec.localB j hj Y hsep).Ω 1 → ℂ}
    (hI : IsDecBg (SmallField.GsSpec.localB j hj Y hsep) (compWeight L a₁) ν
      (rho4 d L N BG κ) s D φ α)
    (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2) :
    (s, (barField (SmallField.GsSpec.localB j hj Y hsep) D.Ψ φ, α)) ∈
      DecDom (SmallField.GsSpec.localB j hj Y hsep) N κ δc := by
  have hL : 3 ≤ L := HBp.hL
  have hm₁ : 2 ≤ m₁ := by
    by_contra h
    push Not at h
    have hL2 : L ^ m₁ ≤ L ^ 1 := Nat.pow_le_pow_right (by omega) (by omega)
    nlinarith
  exact decDom_of_coverBg hS
    (localB_coverBase hj Y hsep hN₁ hm₁ hMM HBp.hd hL HBp.mass HBp.massLe HBp.weights hag)
    HBp hκ hM heps hsmall hc7 hphi hs hD hI hmar hα

end LocalB

end Balaban.Localization
