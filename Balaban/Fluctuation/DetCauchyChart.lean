/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.HatEngineDom
public import Balaban.Fluctuation.RootDetChart
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The rooted trace on the cut chart, with the background cut by the same parameters

For a block `B` of the unit lattice, a datum `D` of the chart `Ξ^c(𝔹_{k+1}; 1, ε)` and cut
parameters `s` (one complex number for each cube of the generating set `G`), let
`(φ_s, α_s)` be the decoupled background field of `D` at `s` (`decBgField`, `decBgMult`) and
`φ̄_s = barField G D.Ψ φ_s` its extension by the datum.  This file studies

`rootTraceBg B D s = rootTrace s φ̄_s α_s`

(`rootTrace` of `Balaban/Fluctuation/RootDetChart`), the only new definition.

* `dec2_decParams_eq`, `dec2_extS_eq`: the cut parameters of the pair-cover version of Theorem I-4b
  (`Dec2`, the cover `coverOf G`) and those of `rootTrace` are the same functions on the same index
  set, extended by `1` in the same way.  The theorem `i4b_analytic` used here is the one for the
  self-cover (`Balaban/Localization/DecoupledBackground`), stated directly for `DecParams G`.
* `exists_isDecBg_of_flCore`, `mem_decDom_rootTraceBg`: for `s` in the polydisc of radius `e^κ`
  the point `(s, (φ̄_s, α_s))` lies in the domain `DecDom` of the decoupled logarithm.
* `analyticOnNhd_rootTraceBg_raw`: one function of `(s, raw datum)`, analytic at every chart point
  `(s, rawOf D)`, which is `rootTraceBg` there (joint analyticity in the cuts and in the datum).
* `analyticOnNhd_rootTraceBg`, `norm_rootTraceBg_le`: analyticity in `s` on the open polydisc and
  the bound `(1/2) N |B| covBLog`.
* `rootTraceBg_cut_expansion`: `rootTraceBg … 1 = ∑_J Δ_J` and
  `‖Δ_J‖ ≤ M (2 / e^κ)^{|J|}`, `M = (1/2) N |B| covBLog d L a_k (a₁/L²) κ`, where `M` involves
  neither the torus nor `J`.
* `rootTraceBg_one_eq`, `rootTraceBg_one_eq_logAC`: at `s = 1` the background is the uncut one
  and `rootTraceBg` is `-(1/2)` times the block trace of `StepSetting.logAC`.

## What this file does not do

No support statement, no hull and no `DetExpansionC` is constructed here.  The dependence of
`rootTraceBg` on the datum is not shown to be local.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.Analysis
  Balaban.SmallField Finset Matrix

/-! ### One parameter space -/

section Params

variable {d L N₁ m₁ k : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}

/-- The cut parameters of the pair-cover version over the self-cover `coverOf G` are the functions
on the cubes of `G`, as for `rootTrace`. -/
theorem dec2_decParams_eq (G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ) :
    Dec2.DecParams (coverOf G) = DecParams G := rfl

/-- The extension by `1` outside the cubes of `G` is the same for both conventions. -/
theorem dec2_extS_eq (G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ) (s : DecParams G) :
    Dec2.extS (coverOf G) s = extS G s := rfl

end Params

/-! ### The definition -/

section Def

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {κι : Type*} [Fintype κι] [DecidableEq κι]

/-- **The rooted trace with the background cut by the same parameters**:
`rootTrace s φ̄_s α_s`, with `(φ_s, α_s)` the decoupled background field of the datum `D` at
`s` (`ρ` the radius of its ball of uniqueness) and `φ̄_s = barField G D.Ψ φ_s` the extension of
`φ_s` by the datum. -/
noncomputable def rootTraceBg (G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ) (a : ℕ → ℝ)
    (aT ν ρ : ℝ) (Q : Matrix κι (G.Ω 1) ℂ) (P : Matrix κι κι ℂ) (B : Finset κι)
    (D : BgData G N) (s : DecParams G) : ℂ :=
  rootTrace G a aT ν Q P B s (barField G D.Ψ (decBgField G a ν ρ s D)) (decBgMult G a ν ρ s D)

end Def

/-! ### Membership in the domain -/

section Chart

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
  {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ}
variable {κι : Type*} [Fintype κι] [DecidableEq κι]

/-- A datum of the chart is in the union domain of Theorem I-4b. -/
theorem inUnionDomainC_of_xiCData
    (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) {D : BgData Gp N}
    (hD : XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D) :
    InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D := by
  have hd0 : 0 < d := by have := hC.HBp.hd; omega
  have hε := hC.eps_pos
  have hδ0 : 0 < xiC1 d * eps := by have := one_le_xiC1 d; positivity
  have hDom := xiCData_inDomainC hC.HBp hC.small1 hD
  have hδ1 : xiC1 d * eps ≤ c7 d L N BG κ := hC.c7le
  have hδ0' : xiC1 d * eps ≤ bgC0 d L N := hδ1.trans ((c7_le_bgC1 d L N BG κ).trans
    (bgC1_le_bgC0 d L N hd0))
  have hνε : ν * ((L : ℝ) ^ (k + 1)) ^ 2 * (xiC1 d * eps) ^ 2 ≤ (xiC1 d * eps) ^ 2 := by
    have := hC.HBp.massLe; nlinarith [sq_nonneg (xiC1 d * eps)]
  exact ⟨xiC1 d * eps, xiC1 d * eps, hδ0, le_rfl, hδ0', hδ1, hνε, hDom⟩

/-- For a datum of the chart and `|s_P| < e^κ` the decoupled background exists, is unique, and
`decBgField`, `decBgMult` return it. -/
theorem exists_isDecBg_of_flCore
    (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) {s : DecParams Gp}
    (hs : ∀ P, ‖s P‖ < Real.exp κ) {D : BgData Gp N}
    (hD : XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D) :
    ∃ (φ : Gp.Ω 1 × Fin N → ℂ) (α : Gp.Ω 1 → ℂ),
      IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α ∧
      decBgField Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D = φ ∧
      decBgMult Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D = α := by
  have hε := hC.eps_pos
  have hδ0 : 0 < xiC1 d * eps := by have := one_le_xiC1 d; positivity
  have hDom := xiCData_inDomainC hC.HBp hC.small1 hD
  have hδ1 : xiC1 d * eps ≤ c7 d L N BG κ := hC.c7le
  have hd0 : 0 < d := by have := hC.HBp.hd; omega
  have hδ0' : xiC1 d * eps ≤ bgC0 d L N := hδ1.trans ((c7_le_bgC1 d L N BG κ).trans
    (bgC1_le_bgC0 d L N hd0))
  have hνε : ν * ((L : ℝ) ^ (k + 1)) ^ 2 * (xiC1 d * eps) ^ 2 ≤ (xiC1 d * eps) ^ 2 := by
    have := hC.HBp.massLe; nlinarith [sq_nonneg (xiC1 d * eps)]
  obtain ⟨φ', α', hI', hu', -⟩ := i4b_exists_unique hC.hS hC.Sp hC.HBp hC.hκ.le hC.hM
    (fun P => (hs P).le) hδ0 le_rfl hδ0' hδ1 hνε hDom
  exact ⟨φ', α', hI', (decBg_eq hI' hu').1, (decBg_eq hI' hu').2⟩

/-- **T2 (a)**: for every `|s_P| < e^κ` the point `(s, (φ̄_s, α_s))` lies in `DecDom`. -/
theorem mem_decDom_rootTraceBg
    (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) {s : DecParams Gp}
    (hs : ∀ P, ‖s P‖ < Real.exp κ) {D : BgData Gp N}
    (hD : XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D) {δc : ℝ}
    (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2) :
    (s, (barField Gp D.Ψ (decBgField Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D),
      decBgMult Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D)) ∈ DecDom Gp N κ δc := by
  obtain ⟨φ, α, hI, h1, h2⟩ := exists_isDecBg_of_flCore hC hs hD
  rw [h1, h2]
  exact decDom_of_isDecBg hC hs hD hI hmar hα

end Chart

end Balaban.Fluctuation
