/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.ClassOldEndpointLocal
public import Balaban.Fluctuation.StepComplexJointH
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-!
# The endpoint identity of an inherited label at a free block datum

The marks of the inherited energy are needed at every datum of the chart `Ξ^c(𝔹_{k+1}; 1, ε)`,
with an arbitrary (complex, non-constant) external field: the input (M2) of
`e0CoeffFamily_class_fromTower` is quantified over all chart data.  The landed endpoint identities
of `ClassOldEndpointLocal.lean` hold at the block datum of a `StepSetting`, whose field is the real
constant `h₀`.  Here they are proved at the block datum `H.D'` of a free-datum wrapper
`H : StepSettingH S` (any field), with the old-level datum `H.dataUCH` carrying the incoming field.
The proofs use only identities valid for every datum of the chart: the fluctuation identity
`fluct_of_tangent`, the composition formulas `flDatum_eq_composeData_of_fluct`,
`bgFieldC_compose`, `composeData_composeData`, and the agreement on `X` of the compositions from
`𝔹_j(X)` and from the whole level `j` (`composeData_agree_on_X`).

* `flCompLocalH_agree_on_X`: on `X` the composed datum of `flComp` at `(rawOf H.D', liftC v)` is the
  composed pair `composedPairAtC … j (H.dataUCH (ψ^{(k)} + v))` of the free datum;
* `classOldEndpointLocalH_liftC`: the endpoint identity
  `flComp Eτ (rawOf H.D', liftC v) = β⁻¹ ℰ^{(j)}(y, X; composedPairAtC … j (H.dataUCH (ψ^{(k)} + v)))`;
* `classOldEndpointLocalH_PJ`: the same with the composed pair written as the joint representative
  `Jr.PJ j (rawOf H.D', ψ̂)` of the old spin `ψ^{(k)} + β_k^{-1/2} C^{(k)1/2} ψ̂`
  (`JointRep.PJ_dataUCH`), i.e. the label term of `ℰ_k = Jr.EJ C` at every chart datum.
-/

@[expose] public section

namespace Balaban.Fluctuation

open MeasureTheory Balaban Balaban.Localization Balaban.Multiscale
  Balaban.Background Balaban.SmallField Balaban.SmallField.Def6 Balaban.SmallField.Def6v2
  Balaban.SmallField.GsSpec Balaban.Analysis Finset Matrix

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱ₁ : ℝ}

namespace StepSettingH

variable {S : StepSetting d L N₁ m₁ k N ϱ} (H : StepSettingH S)

/-- **On `X` the composed datum of `flComp` is the composed pair of the free datum** (P3 (4.16), any
external field).  For a term generator `Gj` with the strong specification for `X`, a localized
ambient set `Gk` (any separation index) with the settings `hB`, `hF` (fluctuation set
`𝔹_k = stepG`), a datum `H.D'` of the chart and a complex field `v` of the unit lattice with
`liftC v` in the ball of fluctuations: at every site of `X` the datum
`ψ(Gj, Gk; ψ(Gk, 𝔹_{k+1}; θ) + δψ(Gk, 𝔹_k; liftC v))` evaluated by `flComp` has the spin and field
of `composedPairAtC … j (H.dataUCH (ψ^{(k)}(θ) + v))`. -/
theorem flCompLocalH_agree_on_X {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k)
    {X : Set (CTorus d L N₁ m₁ (k + 1))} {Gj : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
    (hS : GsSpecStrong j (hjk.trans (Nat.le_succ k)) X Gj)
    {Gk : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁}
    {c BG κ eps Kc Cx c₂ BG₂ δ₁ r₀ δ₃ δfl : ℝ}
    {X₀ X₁f : Finset (CTorus d L N₁ m₁ (k + 1))} {j₁ : ℕ}
    (hB : BgSetting N S.G' Gk Gj S.a₁ S.ν c BG κ r₀ eps δ₃ X₀ X₁f j₁)
    (hF : FlSetting N S.G' Gk (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl
      X₁f)
    (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps H.D')
    (hc7 : c7 d L N BG κ ≤ thm73C3 d L N) {R : ℝ} (hR : 2 ≤ R)
    (hsmR : 2 * (compC4 d * (bgK1 d L N * (xiC1 d * eps))) + 5 * (R * δ₁) ≤ bgC1 d L N)
    (hRs : R * δ₁ ≤ deltaStar d L N) (hsmall : cK2 d L N * (R * δ₁) < bgC0 d L N / 2)
    (hnum : cK2 d L N * δ₁ ≤ c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hnum' : cK2' d L N (famConst d L BG₂ κ) * δ₁ ≤
      c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (v : S.EC) (hv : liftC S.hG' v ∈ FlBall (stepG d L N₁ m₁ k ϱ) δ₁)
    (hz : IsLayerConstant (stepG d L N₁ m₁ k ϱ) (liftC S.hG' v))
    {x : CTorus d L N₁ m₁ (k + 1)} (hx : x ∈ X) :
    (composeData hB.hq S.a
        (bgFieldC Gk S.a S.ν (bgC0 d L N)
          (flDatumOne (stepG d L N₁ m₁ k ϱ) BG₂ κ hB.hP hF.hPm S.a₁ S.ν H.D' (liftC S.hG' v) hz))
        (flDatumOne (stepG d L N₁ m₁ k ϱ) BG₂ κ hB.hP hF.hPm S.a₁ S.ν H.D' (liftC S.hG' v)
          hz)).Ψ x =
        (composedPairAtC S.a S.ν (Nat.le_succ k) j (H.dataUCH ((fun q =>
          (composeData (S.hG.precedes S.hG' (le_refl (k + 1))) S.a
            (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D') H.D').Ψ
              (unitRep (G' := S.G') q.1) q.2) + v))).1 x ∧
      (composeData hB.hq S.a
        (bgFieldC Gk S.a S.ν (bgC0 d L N)
          (flDatumOne (stepG d L N₁ m₁ k ϱ) BG₂ κ hB.hP hF.hPm S.a₁ S.ν H.D' (liftC S.hG' v) hz))
        (flDatumOne (stepG d L N₁ m₁ k ϱ) BG₂ κ hB.hP hF.hPm S.a₁ S.ν H.D' (liftC S.hG' v)
          hz)).h x =
        (composedPairAtC S.a S.ν (Nat.le_succ k) j (H.dataUCH ((fun q =>
          (composeData (S.hG.precedes S.hG' (le_refl (k + 1))) S.a
            (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D') H.D').Ψ
              (unitRep (G' := S.G') q.1) q.2) + v))).2 x := by
  classical
  have hC := flCore_of hB hF
  have hL2 : 2 ≤ L := by have := hB.HBp.hL; omega
  have ha : ∀ i, 1 ≤ i → i ≤ k + 1 → S.a i ≠ 0 := fun i hi _ =>
    (compWeight_pos hL2 hB.ha₁ hi).ne'
  have hψ : liftC S.hG' v ∈ FlBallLC (stepG d L N₁ m₁ k ϱ) δ₁ := ⟨hv, hz⟩
  set ψ0 : S.EC := fun q =>
    (composeData (S.hG.precedes S.hG' (le_refl (k + 1))) S.a
      (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D') H.D').Ψ (unitRep (G' := S.G') q.1) q.2 with hψ0
  set Dk := H.dataUCH (ψ0 + v) with hDk
  set φ := bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D' with hφ
  set Φ := bgFieldC (stepG d L N₁ m₁ k ϱ) S.a S.ν (bgC0 d L N) Dk with hΦ
  have hhD : ∀ z i, Dk.h z i = H.D'.h z i := fun z i => H.dataUCH_h _ z i
  have ht : compTangent S.hG S.hG' (le_refl (k + 1)) S.a φ H.D' Dk = liftC S.hG' v := by
    rw [hDk, hφ, H.compTangent_dataUCH, add_sub_cancel_left]
  -- the fluctuation identity at the free datum
  obtain ⟨hDkdom, hfl⟩ := fluct_of_tangent hC S.hG S.hG' hB.ha₁ hB.HBp hc7 hR hsmR hRs hsmall
    hnum hnum' hD hhD hψ ht
  have hΦeq : Φ = (S.hG.precedes S.hG' (le_refl (k + 1))).restrictφ φ +
      flFieldOne S.G' (stepG d L N₁ m₁ k ϱ) BG₂ κ S.a₁ S.ν H.D' (liftC S.hG' v) := by
    rw [← hfl]; abel
  -- the datum of `Gk` is the composition from the free old datum
  have hFd : flDatumOne (stepG d L N₁ m₁ k ϱ) BG₂ κ hB.hP hF.hPm S.a₁ S.ν H.D' (liftC S.hG' v)
      hz = composeData hF.hPm S.a Φ Dk := by
    rw [hΦeq]
    refine flDatum_eq_composeData_of_fluct hB.hP hF.hPm (S.hG.precedes S.hG' (le_refl (k + 1)))
      ha φ _ H.D' (liftC S.hG' v) hz Dk (fun z i => ?_) (fun z _ i => hhD z i)
    have h1 := congrFun (congrFun ht z) i
    simp only [compTangent] at h1
    have e : (composeData (S.hG.precedes S.hG' (le_refl (k + 1))) S.a φ H.D').Ψ z i =
        composeField (stepG d L N₁ m₁ k ϱ) S.G' S.a φ H.D'.Ψ z i := rfl
    rw [e] at h1
    linear_combination h1
  -- the chart of `Gk` at the datum
  obtain ⟨Fk, -, hFk⟩ := theorem72_analytic (G := Gk) (a := compWeight L S.a₁) (ν := S.ν)
    hB.HBk
  have hmem := triple_one_mem (X₁f := X₁f) hC hD hψ
  obtain ⟨D₁, ψ₁, hlc, ht22, hX3, -, -, -⟩ := eTerm_chain hB hF hFk hmem
  obtain ⟨hr, hψe⟩ := Prod.mk.inj ht22
  have hDD : H.D' = D₁ := BgData.eq_of_raw hr
  rw [← hDD] at hX3
  have hDj0 : InUnionDomainC Gk (bgC0 d L N) (bgC1 d L N) S.ν
      (flDatumOne (stepG d L N₁ m₁ k ϱ) BG₂ κ hB.hP hF.hPm S.a₁ S.ν H.D' (liftC S.hG' v) hz) := by
    have := xiCData_unionC hX3
    subst hψe
    exact this
  have hDj : InUnionDomainC Gk (bgC0 d L N) (bgC1 d L N) S.ν (composeData hF.hPm S.a Φ Dk) := by
    rw [← hFd]; exact hDj0
  -- Theorem 7.3: the background of `Gk` at the composed datum is the restriction
  have hbg : bgFieldC Gk S.a S.ν (bgC0 d L N) (composeData hF.hPm S.a Φ Dk) =
      hF.hPm.restrictφ Φ :=
    (bgFieldC_compose hF.hPm ha Dk (theorem72 hB.HBp hDkdom).2.1
      (theorem72 hB.HBk hDj).1).1
  rw [hFd, hbg, composeData_composeData hB.hq hF.hPm
    (precedes_levelGS hS hjk (Nat.le_succ k)) ha Φ Dk]
  unfold composedPairAtC
  simp only [hjk, ↓reduceDIte]
  exact composeData_agree_on_X (N := N) (a := S.a) hj1 hjk hS Φ Dk hx

/-- **The endpoint identity of an inherited energy label at a free block datum** (any external
field), with a localized ambient set: at the lifted tangent `liftC v` of a complex field `v` of the
unit lattice in the ball of fluctuations,
`flComp Eτ (rawOf H.D', liftC v) = β⁻¹ ℰ^{(j)}(y, X; composedPairAtC … j (H.dataUCH (ψ^{(k)} + v)))`
(P3 (4.16); `StepSetting.classOldEndpointLocal_liftC` is the case of a constant real field). -/
theorem classOldEndpointLocalH_liftC_gen
    (Eτ : RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ) {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k)
    {X : Set (CTorus d L N₁ m₁ (k + 1))}
    (hlocE : ∀ Ψ Ψ' h h', (∀ x ∈ X, Ψ x = Ψ' x ∧ h x = h' x) → Eτ (Ψ, h) = Eτ (Ψ', h'))
    {Gj : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
    (hS : GsSpecStrong j (hjk.trans (Nat.le_succ k)) X Gj)
    {Gk : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁}
    {c BG κ eps Kc Cx c₂ BG₂ δ₁ r₀ δ₃ δfl : ℝ}
    {X₀ X₁f : Finset (CTorus d L N₁ m₁ (k + 1))} {j₁ : ℕ}
    (hB : BgSetting N S.G' Gk Gj S.a₁ S.ν c BG κ r₀ eps δ₃ X₀ X₁f j₁)
    (hF : FlSetting N S.G' Gk (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl
      X₁f)
    (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps H.D')
    (hc7 : c7 d L N BG κ ≤ thm73C3 d L N) {R : ℝ} (hR : 2 ≤ R)
    (hsmR : 2 * (compC4 d * (bgK1 d L N * (xiC1 d * eps))) + 5 * (R * δ₁) ≤ bgC1 d L N)
    (hRs : R * δ₁ ≤ deltaStar d L N) (hsmall : cK2 d L N * (R * δ₁) < bgC0 d L N / 2)
    (hnum : cK2 d L N * δ₁ ≤ c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hnum' : cK2' d L N (famConst d L BG₂ κ) * δ₁ ≤
      c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (v : S.EC) (hv : liftC S.hG' v ∈ FlBall (stepG d L N₁ m₁ k ϱ) δ₁) :
    flComp hB hF (fun raw => (S.β : ℂ)⁻¹ * Eτ raw) (rawOf H.D', liftC S.hG' v) =
      (S.β : ℂ)⁻¹ * Eτ
        (composedPairAtC S.a S.ν (Nat.le_succ k) j (H.dataUCH ((fun q =>
          (composeData (S.hG.precedes S.hG' (le_refl (k + 1))) S.a
            (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D') H.D').Ψ
              (unitRep (G' := S.G') q.1) q.2) + v))) := by
  have hz : IsLayerConstant (stepG d L N₁ m₁ k ϱ) (liftC S.hG' v) :=
    isLayerConstant_liftC S.hG S.hG' v
  rw [flComp_rawOf hB hF _ hD hz]
  congr 1
  exact hlocE _ _ _ _ fun x hx =>
    H.flCompLocalH_agree_on_X hj1 hjk hS hB hF hD hc7 hR hsmR hRs hsmall hnum hnum' v hv hz hx

/-- **The endpoint identity of an inherited energy label at a free block datum** (any external
field), with a localized ambient set: at the lifted tangent `liftC v` of a complex field `v` of the
unit lattice in the ball of fluctuations,
`flComp Eτ (rawOf H.D', liftC v) = β⁻¹ ℰ^{(j)}(y, X; composedPairAtC … j (H.dataUCH (ψ^{(k)} + v)))`
(P3 (4.16); `StepSetting.classOldEndpointLocal_liftC` is the case of a constant real field). -/
theorem classOldEndpointLocalH_liftC
    {P : Consts} {Dom : FieldDom d L N₁ m₁ (k + 1) N ϱ} {Tm : Terms d L N₁ m₁ (k + 1) N ϱ}
    (hcl : SFTermClauses P Dom Tm) {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k)
    {y : CTorus d L N₁ m₁ (k + 1)} {X : Set (CTorus d L N₁ m₁ (k + 1))}
    {Gj : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
    (hS : GsSpecStrong j (hjk.trans (Nat.le_succ k)) X Gj)
    {Gk : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁}
    {c BG κ eps Kc Cx c₂ BG₂ δ₁ r₀ δ₃ δfl : ℝ}
    {X₀ X₁f : Finset (CTorus d L N₁ m₁ (k + 1))} {j₁ : ℕ}
    (hB : BgSetting N S.G' Gk Gj S.a₁ S.ν c BG κ r₀ eps δ₃ X₀ X₁f j₁)
    (hF : FlSetting N S.G' Gk (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl
      X₁f)
    (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps H.D')
    (hc7 : c7 d L N BG κ ≤ thm73C3 d L N) {R : ℝ} (hR : 2 ≤ R)
    (hsmR : 2 * (compC4 d * (bgK1 d L N * (xiC1 d * eps))) + 5 * (R * δ₁) ≤ bgC1 d L N)
    (hRs : R * δ₁ ≤ deltaStar d L N) (hsmall : cK2 d L N * (R * δ₁) < bgC0 d L N / 2)
    (hnum : cK2 d L N * δ₁ ≤ c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hnum' : cK2' d L N (famConst d L BG₂ κ) * δ₁ ≤
      c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (v : S.EC) (hv : liftC S.hG' v ∈ FlBall (stepG d L N₁ m₁ k ϱ) δ₁) :
    flComp hB hF (fun raw => (S.β : ℂ)⁻¹ * Tm.E j y X raw.1 raw.2) (rawOf H.D', liftC S.hG' v) =
      (S.β : ℂ)⁻¹ * Tm.E j y X
        (composedPairAtC S.a S.ν (Nat.le_succ k) j (H.dataUCH ((fun q =>
          (composeData (S.hG.precedes S.hG' (le_refl (k + 1))) S.a
            (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D') H.D').Ψ
              (unitRep (G' := S.G') q.1) q.2) + v))).1
        (composedPairAtC S.a S.ν (Nat.le_succ k) j (H.dataUCH ((fun q =>
          (composeData (S.hG.precedes S.hG' (le_refl (k + 1))) S.a
            (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D') H.D').Ψ
              (unitRep (G' := S.G') q.1) q.2) + v))).2 := by
  exact classOldEndpointLocalH_liftC_gen H (fun r => Tm.E j y X r.1 r.2) hj1 hjk
    (fun Ψ Ψ' h h' hag => hcl.localE j y X Ψ Ψ' h h' hag) hS hB hF hD hc7 hR hsmR hRs hsmall hnum
    hnum' v hv

end StepSettingH

end Balaban.Fluctuation
