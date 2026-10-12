/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.HatEngineLocal
public import Balaban.Localization.RowsCov

/-!
# Narrow agreement for the hat variable: `hatSqrtF` and `hatPsiF` on the rows of the interaction boxes

Parallel versions of `hatSqrtF_local` and `hatPsiF_local` (FOOTPRINT, package 3b, item 5), built
on `I4c_local_sqrt_rows`.  The hat variables are compared only at the unit points whose
`(k+1)`-block lies in `Y` (`UnitOut`), and `hatPsiF` only on `Y` (the landed `hatPsiF_local`
concludes on `psiThick Y`; this version does not).

The row-local background theorem (FOOTPRINT item 3, `i4b_local_rows`) is not available here: its
conclusion, equality of the multipliers on `B = S_Y` and of the decoupled field on `R(B)`
(`rowsCov_R`), is taken as the explicit hypothesis `hbg`, whence the suffix `_of_bgAgree`; the raw
data condition on `A` is the premise of that theorem and does not occur here.  The block hypothesis
`hcomp : CompleteBlocks Gp Y` says `Y` is a union of complete `(k+1)`-blocks.  The agreement of the
hat variable is stated at the unit points of `UnitOut` blocks, i.e. the unit blocks inside `Y`; the
identification with `blocksOf` is not made here.  The fluctuation and fan versions (FOOTPRINT
items 6 and 7) and the physical-reads lemma are not proved here.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Analysis
  Balaban.Fluctuation Finset Matrix

section Rows

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ}

/-- **Rows version of `hatSqrtF_local`, given the background agreement.**  As `hatSqrtF_local`,
with the raw-data condition on `resDep` replaced by the conclusion of the row-local background
theorem (`hbg`: the multipliers agree on `S_Y`, the decoupled field on `R(B)`), the output block
inside `Y`, and the hat variables agreeing on the unit points of the blocks inside `Y`. -/
theorem hatSqrtF_rows_of_bgAgree (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (hk : 1 ≤ k)
    (hconn : HatConn Gp)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    {F₁ : DecParams Gp × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    (hF₁ : ∀ (s : DecParams Gp) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
        (α : Gp.Ω 1 → ℂ), IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    {s s' : DecParams Gp} (hs : ∀ P, ‖s P‖ < Real.exp κ) (hs' : ∀ P, ‖s' P‖ < Real.exp κ)
    {D D' : BgData Gp N} (hD : XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D)
    (hD' : XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D')
    {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ (k + 1))} {X₁ Y : Finset (CTorus d L N₁ m₁ (k + 1))}
    (hY : IsNnComp ((Vset X₁ 𝒞).filter fun x => x ∈ Gp.Ω 1) Y)
    (hs1 : ∀ P ∈ cubeIdx Gp, P ∉ parCubes Gp X₁ → extS Gp s P = 1 ∧ extS Gp s' P = 1)
    (hs0 : ∀ P ∈ parCubes Gp X₁, P ∉ 𝒞 → extS Gp s P = 0 ∧ extS Gp s' P = 0)
    (hag : ∀ P ∈ 𝒞, SubI Gp (cubeP P) Y → extS Gp s P = extS Gp s' P)
    (hcomp : CompleteBlocks Gp Y)
    (hbg : ∀ (φ : Gp.Ω 1 × Fin N → ℂ) (α : Gp.Ω 1 → ℂ) (φ₂ : Gp.Ω 1 × Fin N → ℂ)
      (α₂ : Gp.Ω 1 → ℂ), IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
      IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s' D' φ₂ α₂ →
      (∀ x : Gp.Ω 1, (x : CTorus d L N₁ m₁ (k + 1)) ∈ SY Gp X₁ 𝒞 Y → α x = α₂ x) ∧
      (∀ y : Gp.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ rowsCov_R Gp (compWeight L a₁) a₁ ν α X₁ 𝒞 Y →
        ∀ i, φ (y, i) = φ₂ (y, i)))
    (ψh ψh' : unitPts Gp × Fin N → ℂ)
    {b : unitPts Gp} (hb : UnitOut Gp Y b)
    (hh : ∀ b' : unitPts Gp, UnitOut Gp Y b' → ∀ i, ψh (b', i) = ψh' (b', i)) (i : Fin N) :
    (hatSqrtF Gp a₁ ν F₁ s (rawOf D) *ᵥ ψh) (b, i) =
      (hatSqrtF Gp a₁ ν F₁ s' (rawOf D') *ᵥ ψh') (b, i) := by
  classical
  have hd0 : 0 < d := by have := hC.HBp.hd; omega
  have hc1 := one_le_xiC1 d
  have hε := hC.eps_pos
  have hδ0 : 0 < xiC1 d * eps := by positivity
  have hδ1 : xiC1 d * eps ≤ c7 d L N BG κ := hC.c7le
  have hδ0' : xiC1 d * eps ≤ bgC0 d L N := hδ1.trans ((c7_le_bgC1 d L N BG κ).trans
    (bgC1_le_bgC0 d L N hd0))
  have hνε : ν * ((L : ℝ) ^ (k + 1)) ^ 2 * (xiC1 d * eps) ^ 2 ≤ (xiC1 d * eps) ^ 2 := by
    have := hC.HBp.massLe; nlinarith [sq_nonneg (xiC1 d * eps)]
  have hDom := xiCData_inDomainC hC.HBp hC.small1 hD
  have hDom' := xiCData_inDomainC hC.HBp hC.small1 hD'
  obtain ⟨φ, α, hI, -⟩ := i4b_exists_unique hC.hS hC.Sp hC.HBp hC.hκ.le hC.hM
    (fun P => (hs P).le) hδ0 le_rfl hδ0' hδ1 hνε hDom
  obtain ⟨φ₂, α₂, hI₂, -⟩ := i4b_exists_unique hC.hS hC.Sp hC.HBp hC.hκ.le hC.hM
    (fun P => (hs' P).le) hδ0 le_rfl hδ0' hδ1 hνε hDom'
  have hU : InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D :=
    inUnionDomainC_of_inDomainC hC.HBp hδ0 hδ0' hδ1 hDom
  have hU' : InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D' :=
    inUnionDomainC_of_inDomainC hC.HBp hδ0 hδ0' hδ1 hDom'
  have hFeq := hF₁ s D hs hU φ α hI
  have hFeq' := hF₁ s' D' hs' hU' φ₂ α₂ hI₂
  obtain ⟨hαSY, hφY⟩ := hbg φ α φ₂ α₂ hI hI₂
  have hdec := decDom_of_isDecBg hC hs hD hI hmar hα
  have hdec' := decDom_of_isDecBg hC hs' hD' hI₂ hmar hα
  have hδc : 0 ≤ δc := by
    have : 0 ≤ decDomMargin d L N BG κ (xiC1 d * eps) := by
      have : 0 < K4 d L N BG κ := K4_pos hC.hS.fam.2.1 hd0
      unfold decDomMargin; positivity
    linarith
  have hX : XSetting Gp (compWeight L a₁) a₁ ν := xSetting_of_flCore hC hk
  have hU1 := (isUnitLatticeB_unit (G := Gp)).toIsUnitLattice
  have St := covStanding_of_mem (N := N) (Q := unitQ Gp) (P := unitP Gp) hX hC.hκ.le hMX hδc hsm
    hU1 hdec
  have St' := covStanding_of_mem (N := N) (Q := unitQ Gp) (P := unitP Gp) hX hC.hκ.le hMX hδc hsm
    hU1 hdec'
  have hpot : AdmPot Gp α := fun w => (hdec.2.2 w).le
  have H : LocHyp Gp X₁ 𝒞 Y α (extS Gp s) (extS Gp s') :=
    ⟨hconn, hY, hpot, hs1, hs0, hag⟩
  have hφbar : ∀ y : Gp.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈
      rowsCov_R Gp (compWeight L a₁) a₁ ν α X₁ 𝒞 Y →
      barField Gp D.Ψ φ y = barField Gp D'.Ψ φ₂ y := by
    intro y hy
    funext i
    simp only [barField, y.2, ↓reduceDIte]
    exact hφY y hy i
  unfold hatSqrtF
  rw [hFeq, hFeq']
  exact I4c_local_sqrt_rows St.fam St'.fam H (fun x hx => hαSY x hx) hφbar St.field St'.field
    St.nonneg St.small hcomp ψh ψh' hh hb i

/-- **Rows version of `hatPsiF_local`, given the background agreement.**  The fluctuation field
`hatPsiF` agrees on `Y` itself (the landed theorem concludes on `psiThick Y`), under `hbg` (the
conclusion of the row-local background theorem) and hat agreement on the unit blocks inside `Y`. -/
theorem hatPsiF_rows_of_bgAgree (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (hk : 1 ≤ k)
    (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    (hconn : HatConn Gp)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    {F₁ : DecParams Gp × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    (hF₁ : ∀ (s : DecParams Gp) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
        (α : Gp.Ω 1 → ℂ), IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    {s s' : DecParams Gp} (hs : ∀ P, ‖s P‖ < Real.exp κ) (hs' : ∀ P, ‖s' P‖ < Real.exp κ)
    {D D' : BgData Gp N} (hD : XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D)
    (hD' : XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D')
    {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ (k + 1))} {X₁ Y : Finset (CTorus d L N₁ m₁ (k + 1))}
    (hY : IsNnComp ((Vset X₁ 𝒞).filter fun x => x ∈ Gp.Ω 1) Y)
    (hs1 : ∀ P ∈ cubeIdx Gp, P ∉ parCubes Gp X₁ → extS Gp s P = 1 ∧ extS Gp s' P = 1)
    (hs0 : ∀ P ∈ parCubes Gp X₁, P ∉ 𝒞 → extS Gp s P = 0 ∧ extS Gp s' P = 0)
    (hag : ∀ P ∈ 𝒞, SubI Gp (cubeP P) Y → extS Gp s P = extS Gp s' P)
    (hcomp : CompleteBlocks Gp Y)
    (hbg : ∀ (φ : Gp.Ω 1 × Fin N → ℂ) (α : Gp.Ω 1 → ℂ) (φ₂ : Gp.Ω 1 × Fin N → ℂ)
      (α₂ : Gp.Ω 1 → ℂ), IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
      IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s' D' φ₂ α₂ →
      (∀ x : Gp.Ω 1, (x : CTorus d L N₁ m₁ (k + 1)) ∈ SY Gp X₁ 𝒞 Y → α x = α₂ x) ∧
      (∀ y : Gp.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ rowsCov_R Gp (compWeight L a₁) a₁ ν α X₁ 𝒞 Y →
        ∀ i, φ (y, i) = φ₂ (y, i)))
    (ψh ψh' : unitPts Gp × Fin N → ℂ)
    (hh : ∀ b' : unitPts Gp, UnitOut Gp Y b' → ∀ i, ψh (b', i) = ψh' (b', i)) :
    ∀ y ∈ Y,
      hatPsiF Gp a₁ ν hG' cc F₁ s (rawOf D) ψh y = hatPsiF Gp a₁ ν hG' cc F₁ s' (rawOf D') ψh' y := by
  classical
  intro y hy
  funext i
  unfold hatPsiF
  simp only [liftC_apply, Pi.smul_apply, smul_eq_mul]
  refine congrArg (cc * ·) ?_
  have hout : UnitOut Gp Y (unitPt hG' y) := by
    intro y' hy'
    exact hcomp ⟨y, (hG' y).1⟩ y' (Finset.mem_coe.1 hy |> fun h => h) hy'
  exact hatSqrtF_rows_of_bgAgree hC hk hconn hMX hmar hα hsm hF₁ hs hs' hD hD' hY hs1 hs0 hag hcomp hbg
    ψh ψh' hout hh i

/-- **T5.**  The `UnitOut` case of `hatSqrtF_local` from `hatSqrtF_rows_of_bgAgree`, the landed
background theorem `i4b_local` supplying the background agreement, when `R(B) ⊆ Y` (`hRY`) and `Y`
is a union of complete blocks (`hcomp`, not a hypothesis of the landed theorem). -/
theorem hatSqrtF_local_unitOut_of_rows_subset (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (hk : 1 ≤ k)
    (hconn : HatConn Gp)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    {F₁ : DecParams Gp × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    (hF₁ : ∀ (s : DecParams Gp) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
        (α : Gp.Ω 1 → ℂ), IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    {s s' : DecParams Gp} (hs : ∀ P, ‖s P‖ < Real.exp κ) (hs' : ∀ P, ‖s' P‖ < Real.exp κ)
    {D D' : BgData Gp N} (hD : XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D)
    (hD' : XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D')
    {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ (k + 1))} {X₁ Y : Finset (CTorus d L N₁ m₁ (k + 1))}
    (hY : IsNnComp ((Vset X₁ 𝒞).filter fun x => x ∈ Gp.Ω 1) Y)
    (hs1 : ∀ P ∈ cubeIdx Gp, P ∉ parCubes Gp X₁ → extS Gp s P = 1 ∧ extS Gp s' P = 1)
    (hs0 : ∀ P ∈ parCubes Gp X₁, P ∉ 𝒞 → extS Gp s P = 0 ∧ extS Gp s' P = 0)
    (hag : ∀ P ∈ 𝒞, SubI Gp (cubeP P) Y → extS Gp s P = extS Gp s' P)
    (hdata : ∀ x : Gp.Ω 1, (x : CTorus d L N₁ m₁ (k + 1)) ∈ Y →
      ∀ y ∈ resDep Gp (x : CTorus d L N₁ m₁ (k + 1)), D.Ψ y = D'.Ψ y ∧ (y ∈ Gp.Ω 1 → D.h y = D'.h y))
    (hcomp : CompleteBlocks Gp Y)
    (hRY : ∀ α : Gp.Ω 1 → ℂ, ∀ u ∈ rowsCov_R Gp (compWeight L a₁) a₁ ν α X₁ 𝒞 Y, u ∈ Y)
    (ψh ψh' : unitPts Gp × Fin N → ℂ)
    {b : unitPts Gp} (hb : UnitOut Gp Y b)
    (hh : ∀ b' : unitPts Gp, (UnitOut Gp Y b' ∨ UnitIn Gp X₁ 𝒞 Y b' ∨
      unitBlock1 b.1 = unitBlock1 b'.1) → ∀ i, ψh (b', i) = ψh' (b', i)) (i : Fin N) :
    (hatSqrtF Gp a₁ ν F₁ s (rawOf D) *ᵥ ψh) (b, i) =
      (hatSqrtF Gp a₁ ν F₁ s' (rawOf D') *ᵥ ψh') (b, i) := by
  classical
  have hd0 : 0 < d := by have := hC.HBp.hd; omega
  have hc1 := one_le_xiC1 d
  have hε := hC.eps_pos
  have hδ0 : 0 < xiC1 d * eps := by positivity
  have hδ1 : xiC1 d * eps ≤ c7 d L N BG κ := hC.c7le
  have hδ0' : xiC1 d * eps ≤ bgC0 d L N := hδ1.trans ((c7_le_bgC1 d L N BG κ).trans
    (bgC1_le_bgC0 d L N hd0))
  have hνε : ν * ((L : ℝ) ^ (k + 1)) ^ 2 * (xiC1 d * eps) ^ 2 ≤ (xiC1 d * eps) ^ 2 := by
    have := hC.HBp.massLe; nlinarith [sq_nonneg (xiC1 d * eps)]
  have hDom := xiCData_inDomainC hC.HBp hC.small1 hD
  have hDom' := xiCData_inDomainC hC.HBp hC.small1 hD'
  exact hatSqrtF_rows_of_bgAgree hC hk hconn hMX hmar hα hsm hF₁ hs hs' hD hD' hY hs1 hs0 hag hcomp
    (fun φ α φ₂ α₂ hI hI₂ => by
      obtain ⟨hαSY, hφY⟩ := i4b_local hC.hS hC.Sp hconn hC.HBp hC.hκ.le hC.hM
        (fun P => (hs P).le) (fun P => (hs' P).le) hδ0 le_rfl hδ0' hδ1 hνε hDom hDom' hY
        hs1 hs0 hag hdata hI hI₂
      exact ⟨hαSY, fun y hy i => hφY y (hRY α _ hy) i⟩)
    ψh ψh' hb (fun b' hb' i' => hh b' (Or.inl hb') i') i

end Rows

end Balaban.Localization
