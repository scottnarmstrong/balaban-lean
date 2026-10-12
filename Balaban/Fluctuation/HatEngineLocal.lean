/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.HatEngineFan
public import Balaban.Localization.DecoupledCovLocal2
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Locality of the decoupled square root at the decoupled backgrounds of two data

Two data `D, D'` of `Ξ^c(𝔹_{k+1}; 1, ε)` and parameters `s, s'` as in Theorem I-4b (iv) have
decoupled backgrounds `(φ, α) = F₁(s, Θ)`, `(φ', α') = F₁(s', Θ')`.  `i4b_local` gives
`α = α'` on `S_Y` and `φ = φ'` on `Y ∩ Ω₁`; this is exactly the agreement of the backgrounds that
the two-background covariance locality `I4c_local_sqrt2` needs (the extension `φ̄ = barField Ψ φ`
of the field agrees at the sites of `Ω₁` in `Y` because `φ` does, so no thicker region for `φ`
is required).  Hence `hatSqrtF` is local on the unit lattice: `hatSqrtF_local`.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Analysis
  Balaban.Fluctuation Finset Matrix

section Local

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ}

/-- **Locality of the decoupled square root `C^{1/2}(s)` at the decoupled backgrounds.**  Let
`D, D'` be data of `Ξ^c(𝔹_{k+1}; 1, ε)`, `s, s'` decoupling parameters in the open polydisc,
`Y` a union of nearest-neighbour components of `V(𝒞) ∩ Ω₁` with `s, s'` as in `i4b_local`
(equal to `1` off `𝔓`, `0` on `𝔓 ∖ 𝒞`, agreeing on the cubes of `𝒞` inside `Y`), and the raw data
agreeing on the dependency sets `resDep` of the sites of `Y ∩ Ω₁`.  If `ψ̂, ψ̂'` agree at the unit
points of the output blocks and of the blocks meeting `S_Y`, then `C^{1/2}(s) ψ̂` and
`C^{1/2}(s') ψ̂'` agree at the unit points whose `(k+1)`-block lies in `Y`. -/
theorem hatSqrtF_local (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (hk : 1 ≤ k)
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
    (ψh ψh' : unitPts Gp × Fin N → ℂ)
    (hh : ∀ b' : unitPts Gp, (UnitOut Gp Y b' ∨ UnitIn Gp X₁ 𝒞 Y b') → ∀ i,
      ψh (b', i) = ψh' (b', i))
    {b : unitPts Gp} (hb : UnitOut Gp Y b) (i : Fin N) :
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
  obtain ⟨hαSY, hφY⟩ := i4b_local hC.hS hC.Sp hconn hC.HBp hC.hκ.le hC.hM
    (fun P => (hs P).le) (fun P => (hs' P).le) hδ0 le_rfl hδ0' hδ1 hνε hDom hDom' hY
    hs1 hs0 hag hdata hI hI₂
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
  have hφbar : ∀ y : Gp.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y →
      barField Gp D.Ψ φ y = barField Gp D'.Ψ φ₂ y := by
    intro y hy
    funext i
    simp only [barField, y.2, ↓reduceDIte]
    exact hφY y hy i
  unfold hatSqrtF
  rw [hFeq, hFeq']
  exact I4c_local_sqrt2 St.fam St'.fam H (fun x hx => hαSY x hx) hφbar St.field St'.field
    St.nonneg St.small ψh ψh' hh hb i

end Local

end Balaban.Localization
