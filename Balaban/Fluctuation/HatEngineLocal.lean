/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.HatEngineFan
public import Balaban.Localization.DecoupledCovLocal2
public import Balaban.Localization.DecoupledCovLocal2Free
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
`C^{1/2}(s') ψ̂'` agree at the unit points whose `(k+1)`-block lies in `Y`, and (with the inputs
agreeing on the unit points of the block) at the unit points whose block avoids the cores of
both parameter vectors. -/
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
    {b : unitPts Gp} (hb : UnitOut Gp Y b ∨ FreeBlk Gp (extS Gp s) (extS Gp s') b)
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
  exact I4c_local_sqrt3 St.fam St'.fam H (fun x hx => hαSY x hx) hφbar St.field St'.field
    St.nonneg St.small ψh ψh' hb hh i

end Local

section PsiAux

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} {a₁ ν : ℝ}

omit [NeZero N₁] [NeZero L] in
theorem exists_near_of_psiThick {Y : Finset (CTorus d L N₁ m₁ (k + 1))}
    {y : CTorus d L N₁ m₁ (k + 1)} (hy : y ∈ psiThick (↑Y : Set (CTorus d L N₁ m₁ (k + 1)))) :
    ∃ x₀ ∈ Y, ∃ v : Fin d → ℤ, (∀ μ, |(v μ : ℝ)| ≤ 1) ∧
      x₀ = y + (intTorus v : CTorus d L N₁ m₁ (k + 1)) := by
  rcases hy with hy | ⟨x, hx, μ, hxy | hxy⟩
  · exact ⟨y, Finset.mem_coe.1 hy, 0, fun μ => by simp, by
      funext μ; simp [intTorus_apply]⟩
  · refine ⟨x, Finset.mem_coe.1 hx, Pi.single μ (-1), fun ν' => ?_, ?_⟩
    · by_cases h' : ν' = μ <;> simp [h']
    · rw [hxy]; funext ν'
      by_cases h' : ν' = μ <;> simp [intTorus_apply, h']
  · refine ⟨x, Finset.mem_coe.1 hx, Pi.single μ 1, fun ν' => ?_, ?_⟩
    · by_cases h' : ν' = μ <;> simp [h']
    · rw [hxy]; funext ν'
      by_cases h' : ν' = μ <;> simp [intTorus_apply, h']

/-- A unit point next to `Y` whose block is not inside `Y` is free. -/
theorem freeBlk_of_psiThick (S : DGSetting Gp (compWeight L a₁) ν) (hconn : HatConn Gp)
    {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ (k + 1))} {X₁ Y : Finset (CTorus d L N₁ m₁ (k + 1))}
    (hY : IsNnComp ((Vset X₁ 𝒞).filter fun x => x ∈ Gp.Ω 1) Y)
    {s s' : DecParams Gp}
    (hs0 : ∀ P ∈ parCubes Gp X₁, P ∉ 𝒞 → extS Gp s P = 0 ∧ extS Gp s' P = 0)
    (hG' : IsLevel Gp (k + 1)) {y : CTorus d L N₁ m₁ (k + 1)}
    (hy : y ∈ psiThick (↑Y : Set (CTorus d L N₁ m₁ (k + 1))))
    (hout : ¬ UnitOut Gp Y (unitPt hG' y)) :
    FreeBlk Gp (extS Gp s) (extS Gp s') (unitPt hG' y) := by
  have hb1 : unitBlock1 (unitPt hG' y).1 = jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) y :=
    unitBlock1_unitBlock y
  have hy₀ : y ∈ Gp.layer (k + 1) := hG'.mem_layer y
  have hnot : ¬ ∀ y' : Gp.Ω 1, jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1)
      (y' : CTorus d L N₁ m₁ (k + 1)) = jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) y →
      (y' : CTorus d L N₁ m₁ (k + 1)) ∈ Y := by
    intro hall
    apply hout
    intro y' hy'
    apply hall y'
    rw [← hb1, ← hy', unitBlock1_unitBlock]
  obtain ⟨x₀, hx₀, v, hv, hx₀v⟩ := exists_near_of_psiThick hy
  intro y' hy'
  have hy'b : jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) (y' : CTorus d L N₁ m₁ (k + 1)) =
      jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) y := by
    rw [← unitBlock1_unitBlock, hy', hb1]
  exact ⟨free_of_block S hconn hY (fun P hP hPC => (hs0 P hP hPC).1)
      (y₀ := ⟨y, (hG' y).1⟩) hy₀ hx₀ hv hx₀v hnot y' hy'b,
    free_of_block S hconn hY (fun P hP hPC => (hs0 P hP hPC).2)
      (y₀ := ⟨y, (hG' y).1⟩) hy₀ hx₀ hv hx₀v hnot y' hy'b⟩

end PsiAux

section PsiLocal

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ}

/-- The sites whose `(k+1)`-block meets `Y` or a neighbour of `Y`: the set on which the hat
variable must agree for `ψ'(s)` to agree on `Y` and its neighbours. -/
def blockThick (Y : Set (CTorus d L N₁ m₁ (k + 1))) : Set (CTorus d L N₁ m₁ (k + 1)) :=
  {y | ∃ y₂ ∈ psiThick Y, jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) y =
    jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) y₂}

omit [NeZero N₁] [NeZero L] in
theorem psiThick_subset_blockThick (Y : Set (CTorus d L N₁ m₁ (k + 1))) :
    psiThick Y ⊆ blockThick Y := fun y hy => ⟨y, hy, rfl⟩

/-- **Locality of the fluctuation field `ψ'(s) = liftC (cc • C^{1/2}(s) ψ̂)`** on `Y` and its
neighbours: for `Y` as in `hatSqrtF_local`, if the hat variables agree at the unit points whose
`(k+1)`-block meets `Y` or a neighbour of `Y`, then `ψ'(s)` and `ψ'(s')` agree on `Y` and its
neighbours. -/
theorem hatPsiF_local (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (hk : 1 ≤ k)
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
    (hdata : ∀ x : Gp.Ω 1, (x : CTorus d L N₁ m₁ (k + 1)) ∈ Y →
      ∀ y ∈ resDep Gp (x : CTorus d L N₁ m₁ (k + 1)), D.Ψ y = D'.Ψ y ∧ (y ∈ Gp.Ω 1 → D.h y = D'.h y))
    (ψh ψh' : unitPts Gp × Fin N → ℂ)
    (hh : ∀ y ∈ blockThick (↑Y : Set (CTorus d L N₁ m₁ (k + 1))), ∀ i,
      ψh (unitPt hG' y, i) = ψh' (unitPt hG' y, i)) :
    ∀ y ∈ psiThick (↑Y : Set (CTorus d L N₁ m₁ (k + 1))),
      hatPsiF Gp a₁ ν hG' cc F₁ s (rawOf D) ψh y = hatPsiF Gp a₁ ν hG' cc F₁ s' (rawOf D') ψh' y := by
  classical
  intro y hy
  funext i
  unfold hatPsiF
  simp only [liftC_apply, Pi.smul_apply, smul_eq_mul]
  refine congrArg (cc * ·) ?_
  set b : unitPts Gp := unitPt hG' y with hbdef
  have hb1 : unitBlock1 b.1 = jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) y := by
    rw [hbdef]; exact unitBlock1_unitBlock y
  -- agreement of the hat variables on the unit points of the blocks meeting `psiThick Y`
  have hagr : ∀ b' : unitPts Gp, (∃ y2 ∈ psiThick (↑Y : Set (CTorus d L N₁ m₁ (k + 1))),
      jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) y2 = unitBlock1 b'.1) →
      ∀ j, ψh (b', j) = ψh' (b', j) := by
    intro b' ⟨y2, hy2, hy2b⟩ j
    obtain ⟨x, hxl, hxb⟩ := (mem_unitPts Gp).1 b'.2
    have hxb' : unitPt hG' x = b' := Subtype.ext hxb
    have := hh x ⟨y2, hy2, by
      rw [← unitBlock1_unitBlock, hxb, hy2b]⟩ j
    rwa [hxb'] at this
  have hblk : ∀ b' : unitPts Gp, unitBlock1 b.1 = unitBlock1 b'.1 → ∀ j,
      ψh (b', j) = ψh' (b', j) := fun b' hb' j =>
    hagr b' ⟨y, hy, by rw [← hb', hb1]⟩ j
  have hOI : ∀ b' : unitPts Gp, (UnitOut Gp Y b' ∨ UnitIn Gp X₁ 𝒞 Y b') → ∀ j,
      ψh (b', j) = ψh' (b', j) := by
    intro b' hb' j
    refine hagr b' ?_ j
    rcases hb' with h1 | ⟨y1, hy1, hy1b⟩
    · obtain ⟨x, hxl, hxb⟩ := (mem_unitPts Gp).1 b'.2
      refine ⟨x, Or.inl (Finset.mem_coe.2 (h1 ⟨x, (hG' x).1⟩ (by simp [hxb]))), ?_⟩
      rw [← unitBlock1_unitBlock, hxb]
    · exact ⟨y1, Or.inl (Finset.mem_coe.2 (SY_subset hy1)), by
        rw [← unitBlock1_unitBlock, hy1b]⟩
  have key := hatSqrtF_local hC hk hconn hMX hmar hα hsm hF₁ hs hs' hD hD' hY hs1 hs0 hag hdata
    ψh ψh' (b := b)
  by_cases hout : UnitOut Gp Y b
  · exact key (Or.inl hout) (fun b' hb' j => by
      rcases hb' with h1 | h1 | h1
      · exact hOI b' (Or.inl h1) j
      · exact hOI b' (Or.inr h1) j
      · exact hblk b' h1 j) i
  · have hfree : FreeBlk Gp (extS Gp s) (extS Gp s') b :=
      freeBlk_of_psiThick hC.Sp hconn hY hs0 hG' hy hout
    exact key (Or.inr hfree) (fun b' hb' j => by
      rcases hb' with h1 | h1 | h1
      · exact hOI b' (Or.inl h1) j
      · exact hOI b' (Or.inr h1) j
      · exact hblk b' h1 j) i

end PsiLocal

end Balaban.Localization
