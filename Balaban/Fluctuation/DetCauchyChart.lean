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

/-- The open polydisc of radius `R` in the cut parameters. -/
theorem isOpen_cutPolydisc (R : ℝ) : IsOpen (cutPolydisc (cubeIdx Gp) R) := by
  have : cutPolydisc (cubeIdx Gp) R = ⋂ P, {p : DecParams Gp | ‖p P‖ < R} := by
    ext p; simp [cutPolydisc]
  rw [this]
  exact isOpen_iInter_of_finite fun P =>
    isOpen_lt (continuous_norm.comp (continuous_apply P)) continuous_const

/-- The extension `φ̄` by the datum is analytic in the pair (raw datum, field). -/
theorem analyticAt_barField_coord {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    {Ψ : X → Torus d (N₁ * L ^ m₁ * L ^ (k + 1)) → Fin N → ℂ} {φ : X → Gp.Ω 1 × Fin N → ℂ}
    {x₀ : X} (hΨ : AnalyticAt ℂ Ψ x₀) (hφ : AnalyticAt ℂ φ x₀) :
    AnalyticAt ℂ (fun x => barField Gp (Ψ x) (φ x)) x₀ := by
  refine analyticAt_pi_iff.2 fun x => analyticAt_pi_iff.2 fun i => ?_
  by_cases h : x ∈ Gp.Ω 1
  · have h1 : AnalyticAt ℂ (fun y => φ y (⟨x, h⟩, i)) x₀ := analyticAt_pi_iff.1 hφ _
    exact h1.congr (Filter.Eventually.of_forall fun y => by simp [barField, h])
  · have h1 : AnalyticAt ℂ (fun y => Ψ y x i) x₀ :=
      analyticAt_pi_iff.1 (analyticAt_pi_iff.1 hΨ x) i
    exact h1.congr (Filter.Eventually.of_forall fun y => by simp [barField, h])

variable {Q : Matrix κι (Gp.Ω 1) ℂ} {P : Matrix κι κι ℂ}

/-- **T5 (a), joint analyticity in the cuts and the datum**: there is one function `F` of
`(s, raw datum)` on all raw data, analytic at every chart point `(s, rawOf D)` with
`|s_P| < e^κ` and `D` in the chart `Ξ^c`, and equal to `rootTraceBg` there.  (The chart has empty
interior in the space of raw data: nothing is said about openness of the chart.) -/
theorem analyticOnNhd_rootTraceBg_raw
    (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (hk : 1 ≤ k) {δc : ℝ}
    (hδc : 0 ≤ δc) (hcap : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hU : IsUnitLattice Gp Q P) (B : Finset κι) :
    ∃ F : DecParams Gp × RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ,
      AnalyticOnNhd ℂ F {q | (∀ P, ‖q.1 P‖ < Real.exp κ) ∧ ∃ D : BgData Gp N,
        XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D ∧ q.2 = rawOf D} ∧
      ∀ (s : DecParams Gp) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
        XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D →
        F (s, rawOf D) = rootTraceBg Gp (compWeight L a₁) a₁ ν (rho4 d L N BG κ) Q P B D s := by
  obtain ⟨F0, hanal, hval⟩ := i4b_analytic (N := N) hC.hS hC.Sp hC.HBp hC.hκ.le hC.hM
  refine ⟨fun q => rootTrace Gp (compWeight L a₁) a₁ ν Q P B q.1
    (barField Gp q.2.1 (F0 q).1) (F0 q).2, ?_, ?_⟩
  · rintro ⟨s, p⟩ ⟨hs, D, hD, rfl⟩
    have hq : AnalyticAt ℂ F0 (s, rawOf D) := hanal _ ⟨hs, D, inUnionDomainC_of_xiCData hC hD, rfl⟩
    have h1 : AnalyticAt ℂ (fun q : DecParams Gp × RawData d L (N₁ * L ^ m₁) (k + 1) N =>
        (F0 q).1) (s, rawOf D) := analyticAt_fst.comp hq
    have h2 : AnalyticAt ℂ (fun q : DecParams Gp × RawData d L (N₁ * L ^ m₁) (k + 1) N =>
        (F0 q).2) (s, rawOf D) := analyticAt_snd.comp hq
    have h3 : AnalyticAt ℂ (fun q : DecParams Gp × RawData d L (N₁ * L ^ m₁) (k + 1) N =>
        q.2.1) (s, rawOf D) := analyticAt_fst.comp analyticAt_snd
    have hg : AnalyticAt ℂ (fun q : DecParams Gp × RawData d L (N₁ * L ^ m₁) (k + 1) N =>
        ((q.1, (barField Gp q.2.1 (F0 q).1, (F0 q).2)) : DecData Gp N)) (s, rawOf D) :=
      analyticAt_fst.prod ((analyticAt_barField_coord h3 h1).prod h2)
    obtain ⟨φ, α, hI, h1', h2'⟩ := exists_isDecBg_of_flCore hC hs hD
    have hv : F0 (s, rawOf D) = (φ, α) :=
      hval s D hs (inUnionDomainC_of_xiCData hC hD) φ α hI
    have hmem : ((s, (barField Gp (rawOf D).1 (F0 (s, rawOf D)).1, (F0 (s, rawOf D)).2)) :
        DecData Gp N) ∈ DecDom Gp N κ δc := by
      have e : ((s, (barField Gp (rawOf D).1 (F0 (s, rawOf D)).1, (F0 (s, rawOf D)).2)) :
          DecData Gp N) = (s, (barField Gp D.Ψ φ, α)) := by rw [hv]; rfl
      rw [e]; exact decDom_of_isDecBg hC hs hD hI hmar hα
    have hS := xSetting_of_flCore hC hk
    have hrt := analyticOnNhd_rootTrace (a := compWeight L a₁) (aT := a₁) (N := N) hS hC.hκ.le
      hcap hδc hsm hU B
      ((s, (barField Gp (rawOf D).1 (F0 (s, rawOf D)).1, (F0 (s, rawOf D)).2)) : DecData Gp N)
      hmem
    have key := AnalyticAt.comp_of_eq (g := fun e : DecData Gp N =>
      rootTrace Gp (compWeight L a₁) a₁ ν Q P B e.1 e.2.1 e.2.2)
      (f := fun q : DecParams Gp × RawData d L (N₁ * L ^ m₁) (k + 1) N =>
        ((q.1, (barField Gp q.2.1 (F0 q).1, (F0 q).2)) : DecData Gp N)) hrt hg rfl
    exact key
  · intro s D hs hD
    obtain ⟨φ, α, hI, h1, h2⟩ := exists_isDecBg_of_flCore hC hs hD
    have hv : F0 (s, rawOf D) = (φ, α) :=
      hval s D hs (inUnionDomainC_of_xiCData hC hD) φ α hI
    show rootTrace Gp (compWeight L a₁) a₁ ν Q P B s (barField Gp (rawOf D).1 (F0 (s, rawOf D)).1)
      (F0 (s, rawOf D)).2 = _
    rw [hv]
    unfold rootTraceBg
    rw [h1, h2]
    rfl

/-- **T2 (b)**: `s ↦ rootTraceBg B D s` is analytic on the open polydisc of radius `e^κ`. -/
theorem analyticOnNhd_rootTraceBg
    (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (hk : 1 ≤ k) {δc : ℝ}
    (hδc : 0 ≤ δc) (hcap : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hU : IsUnitLattice Gp Q P) (B : Finset κι) {D : BgData Gp N}
    (hD : XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D) :
    AnalyticOnNhd ℂ (rootTraceBg Gp (compWeight L a₁) a₁ ν (rho4 d L N BG κ) Q P B D)
      (cutPolydisc (cubeIdx Gp) (Real.exp κ)) := by
  obtain ⟨F, hF, hFv⟩ := analyticOnNhd_rootTraceBg_raw hC hk hδc hcap hsm hmar hα hU B
  intro s hs
  have hs' : ∀ P, ‖s P‖ < Real.exp κ := hs
  have h1 : AnalyticAt ℂ (fun s : DecParams Gp => F (s, rawOf D)) s :=
    AnalyticAt.comp_of_eq (hF _ ⟨hs', D, hD, rfl⟩) (analyticAt_id.prod analyticAt_const) rfl
  refine h1.congr ?_
  filter_upwards [(isOpen_cutPolydisc (Gp := Gp) (Real.exp κ)).mem_nhds hs] with t ht
  exact hFv t D ht hD

/-- **T2 (c)**: the bound `‖rootTraceBg‖ ≤ (1/2) N |B| covBLog` on the polydisc. -/
theorem norm_rootTraceBg_le
    (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (hk : 1 ≤ k) {δc : ℝ}
    (hδc : 0 ≤ δc) (hcap : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hU : IsUnitLattice Gp Q P) (B : Finset κι) {D : BgData Gp N}
    (hD : XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D) {s : DecParams Gp}
    (hs : ∀ P, ‖s P‖ < Real.exp κ) :
    ‖rootTraceBg Gp (compWeight L a₁) a₁ ν (rho4 d L N BG κ) Q P B D s‖ ≤
      (1 / 2 : ℝ) * N * B.card * covBLog d L (compWeight L a₁ k) (a₁ / (L : ℝ) ^ 2) κ :=
  norm_rootTrace_le (a := compWeight L a₁) (aT := a₁) (N := N) (xSetting_of_flCore hC hk) hC.hκ.le
    hcap hδc hsm hU B (e := ((s, (barField Gp D.Ψ (decBgField Gp (compWeight L a₁) ν
      (rho4 d L N BG κ) s D), decBgMult Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D)) :
      DecData Gp N)) (mem_decDom_rootTraceBg hC hs hD hmar hα)

/-- **T3 (mixed differences)**: with `R = e^κ > 1` and `M = (1/2) N |B| covBLog d L a_k (a₁/L²) κ`,
`rootTraceBg … 1 = ∑_J Δ_J` and `‖Δ_J‖ ≤ M (2/R)^{|J|}`.  The constant `M` depends on `d, L, N`,
the weight `a_k`, `a₁`, `κ` and the block size `|B|` only: neither on the torus (`N₁`, `m₁`) nor
on `J`.  The factor `2/R < 1` exactly when `e^κ > 2`. -/
theorem rootTraceBg_cut_expansion
    (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (hk : 1 ≤ k) {δc : ℝ}
    (hδc : 0 ≤ δc) (hcap : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hU : IsUnitLattice Gp Q P) (B : Finset κι) {D : BgData Gp N}
    (hD : XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D) :
    rootTraceBg Gp (compWeight L a₁) a₁ ν (rho4 d L N BG κ) Q P B D (fun _ => 1) =
        ∑ J ∈ (Finset.univ : Finset (cubeIdx Gp)).powerset,
          mixDiff J (rootTraceBg Gp (compWeight L a₁) a₁ ν (rho4 d L N BG κ) Q P B D) ∧
      ∀ J : Finset (cubeIdx Gp),
        ‖mixDiff J (rootTraceBg Gp (compWeight L a₁) a₁ ν (rho4 d L N BG κ) Q P B D)‖ ≤
          (1 / 2 : ℝ) * N * B.card *
            covBLog d L (compWeight L a₁ k) (a₁ / (L : ℝ) ^ 2) κ * (2 / Real.exp κ) ^ J.card := by
  have hR : 1 < Real.exp κ := Real.one_lt_exp_iff.2 hC.hκ
  refine ⟨sum_mixDiff _, fun J => norm_mixDiff_le hR J ?_ ?_⟩
  · exact (analyticOnNhd_rootTraceBg hC hk hδc hcap hsm hmar hα hU B hD).differentiableOn
  · intro s hs
    exact norm_rootTraceBg_le hC hk hδc hcap hsm hmar hα hU B hD hs

end Chart

end Balaban.Fluctuation
