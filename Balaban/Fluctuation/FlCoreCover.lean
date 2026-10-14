/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.InteractionHatE
public import Balaban.Fluctuation.SharpChartTestFlSup
public import Balaban.Fluctuation.LocalFluctGen
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The fluctuation core in cover form, and its instance at the local generator pair

The fluctuation core of the decoupled expansion (`FlCore`, `point_facts_core`, `fanF_analytic`, the
bound in `i5_functional`, `triple_one_mem`, `eTerm_chain_of_one_le`, `eTermFun_analytic_of_one_le`,
`eTermFun_bound_of_one_le`, `eTermFun_value`) is stated for a parent `𝔹_{k+1}` with `DGSetting`
(through `FlCore.Sp` or `BgSetting.Sp`) and the separation `r₀ M₁ ≤ ϱ - 1`.  Neither holds for the
literal local generator `𝔹_{k+1}(Y) = localB …` of P3 (4.4)-(4.6) (`not_bgSetting_localB`).  The
landed theorems are now applications of common steps with the background stage as hypothesis
(`point_facts_core_of_bg`, `fanF_analytic_of_bg`, `fanF_bound_of_bg`, `triple_one_mem_of_bg`,
`eTerm_chain_of_bg`, `eTermFun_analytic_of_bg`, `eTermFun_bound_of_bg`,
`eTermFun_value_of_bg`); here the same common steps are applied with Theorem I-4b for the cover
`coverOf 𝔹_{k+1}` (`Dec2.i4b_exists_unique`, `Dec2.i4b_one`) and the sup-separated stage 1
(`i5_stage1_sup_of_one_le`).  The set `FlReal` of realizable triples needs no rerun: its
decoupled background `IsDecBg 𝔹_{k+1}` is the pair notion `Dec2.IsDecBg (coverOf 𝔹_{k+1}) 𝔹_{k+1}`
(the same three fields).  `flComp` is defined only under `BgSetting`; the cover form of its value is
the explicit composite `E(ψ(𝔹_j(X), 𝔹_k(X); ψ(𝔹_k(X), 𝔹_{k+1}; Θ) + δψ(𝔹_k(X), 𝔹_k; ψ')))`.

* `coverBg_exists`, `coverBg_one`, `bgStage_cover_of_one_le`: the background stage for the cover;
* `point_facts_core_cover`, `fanF_analytic_cover`, `fanF_bound_cover`, `triple_one_mem_cover`:
  the fluctuation core (`FlCore` with `Sp : DGSetting` replaced by `Dec2.CoverBase`);
* `eTerm_chain_cover_of_one_le`, `eTermFun_analytic_cover_of_one_le`,
  `eTermFun_bound_cover_of_one_le`, `eTermFun_value_cover`: the old-term functional, with the
  hypotheses of `point_facts_fl_sup_of_one_le`;
* `localB_coverData`: the cover data of `localB` at `ϱ = 5 L M₁`, `r₀ = 4 d L³ + L`;
* `localB_fanF_analytic`, `localB_fanF_bound`, `localB_eTermFun_analytic`, `localB_eTermFun_bound`,
  `localB_eTermFun_value`: the instances at `𝔹_{k+1}(Y) = localB …`;
* `localB_pair_flSetting`: `FlSetting` at the local pair `(𝔹_{k+1}(Y), 𝔹_k(Y))`, `𝔹_k(Y)` the local
  generator with the top layer dropped (`Fluctuation/LocalFluctGen.lean`).

The fan locality `eterm_fan_local_rawY` is not rerun here: it is typed by `IsLevel 𝔹_{k+1} (k + 1)`
(`unitPt`, `hatPsiF`), `HatConn 𝔹_{k+1}` and `CovSetup 𝔹_{k+1}`, which fail for `localB`; in the
two-generator design (WIDEGEN, NEXT (W776)) the expansion and the fan stay on the ambient level
pair.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Analysis Finset Matrix
  Balaban.Fluctuation Balaban.SmallField.Def6 Balaban.LargeField

section BgCover

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱ₁ ϱ₂ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {Gk : GeneratingSet d L (N₁ * L ^ m₁) K ϱ₁}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) K ϱm}
variable {a₁ ν Kc Cx : ℝ}

/-- **Theorem I-4b at a realizable point, for the cover of `𝔹_{k+1}`** (cover form of
`flCore_bgBounds`): from `Dec2.CoverBase (coverOf 𝔹_{k+1}) 𝔹_{k+1}` (no `DGSetting`), for
`|s_P| < e^κ` and a datum of `Ξ^c_K(𝔹_{k+1}; 1, ε')` the decoupled background field exists, is
unique in its ball and has the bounds `BgBounds` with the constant `K₄ C₁ ε'`.  The pair notion
`Dec2.IsDecBg (coverOf 𝔹_{k+1}) 𝔹_{k+1}` is the self-cover notion `IsDecBg 𝔹_{k+1}`
(the same three fields), which is the one in `FlReal`. -/
theorem coverBg_exists {c BG : ℝ} (hS : Dec2.DecSpecs d L Kc Cx c BG)
    (S : Dec2.CoverBase (coverOf Gp) Gp (compWeight L a₁) ν Kc Cx)
    (HBp : BgHyp d L K ϱ (compWeight L a₁) ν) {κ eps : ℝ} (hκ : 0 ≤ κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) (heps : 0 < eps)
    (hsmall : (4 * d + 6) * ((2 * d + 1) * eps) ≤ 1) (hc7 : xiC1 d * eps ≤ c7 d L N BG κ)
    {s : DecParams Gp} (hs : ∀ P, ‖s P‖ < Real.exp κ) {D : BgData Gp N}
    (hD : XiCData Gp (compWeight L a₁) ν K 1 eps D) :
    ∃ (φ : Gp.Ω 1 × Fin N → ℂ) (α : Gp.Ω 1 → ℂ),
      IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α ∧
      (∀ φ' α', IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ' α' →
        φ' = φ ∧ α' = α) ∧
      BgBounds Gp D φ α (K4 d L N BG κ * (xiC1 d * eps)) := by
  have hd0 : 0 < d := by have := HBp.hd; omega
  have hc1 := one_le_xiC1 d
  have hδ0 : 0 < xiC1 d * eps := by positivity
  have hDom := xiCData_inDomainC HBp hsmall hD
  have hδ0' : xiC1 d * eps ≤ bgC0 d L N := hc7.trans ((c7_le_bgC1 d L N BG κ).trans
    (bgC1_le_bgC0 d L N hd0))
  have hνε : ν * ((L : ℝ) ^ K) ^ 2 * (xiC1 d * eps) ^ 2 ≤ (xiC1 d * eps) ^ 2 := by
    have := HBp.massLe; nlinarith [sq_nonneg (xiC1 d * eps)]
  obtain ⟨φ, α, hI, hu, -, -, hbb⟩ := Dec2.i4b_exists_unique hS S HBp hκ hM
    (s := s) (fun P => (hs P).le) hδ0 le_rfl hδ0' hc7 hνε hDom
  exact ⟨φ, α, ⟨hI.small, hI.fixed, hI.field⟩,
    fun φ' α' h => hu φ' α' ⟨h.small, h.fixed, h.field⟩, hbb⟩

/-- **The decoupled background field at `s ≡ 1` for the cover of `𝔹_{k+1}` is the background
field of Theorem 5.2** (cover form of `i4b_one` at a datum of the chart): `(bgFieldC D, bgMultC D)`
is the decoupled background field of `D` at `s ≡ 1`. -/
theorem coverBg_one {c BG : ℝ} (hS : Dec2.DecSpecs d L Kc Cx c BG)
    (S : Dec2.CoverBase (coverOf Gp) Gp (compWeight L a₁) ν Kc Cx)
    (HBp : BgHyp d L K ϱ (compWeight L a₁) ν) {κ eps : ℝ} (hκ : 0 ≤ κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) (heps : 0 < eps)
    (hsmall : (4 * d + 6) * ((2 * d + 1) * eps) ≤ 1) (hc7 : xiC1 d * eps ≤ c7 d L N BG κ)
    {D : BgData Gp N} (hD : XiCData Gp (compWeight L a₁) ν K 1 eps D) :
    IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) (fun _ => 1) D
      (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D)
      (bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D) := by
  have hd0 : 0 < d := by have := HBp.hd; omega
  have hc1 := one_le_xiC1 d
  have hδ0 : 0 < xiC1 d * eps := by positivity
  have hDom := xiCData_inDomainC HBp hsmall hD
  have hδ0' : xiC1 d * eps ≤ bgC0 d L N := hc7.trans ((c7_le_bgC1 d L N BG κ).trans
    (bgC1_le_bgC0 d L N hd0))
  have hνε : ν * ((L : ℝ) ^ K) ^ 2 * (xiC1 d * eps) ^ 2 ≤ (xiC1 d * eps) ^ 2 := by
    have := HBp.massLe; nlinarith [sq_nonneg (xiC1 d * eps)]
  have hone : ∀ P : ↥(coverOf Gp).cubeIdx,
      ‖(fun _ : ↥(coverOf Gp).cubeIdx => (1 : ℂ)) P‖ ≤ Real.exp κ :=
    fun P => by simpa using Real.one_le_exp hκ
  obtain ⟨φ, α, hI, -⟩ := Dec2.i4b_exists_unique hS S HBp hκ hM hone hδ0 le_rfl hδ0' hc7 hνε hDom
  obtain ⟨-, hφ1, hα1⟩ := Dec2.i4b_one hS S HBp hκ hM hδ0 le_rfl hδ0' hc7 hνε hDom hI
  rw [hφ1, hα1]
  exact ⟨hI.small, hI.fixed, hI.field⟩

/-- **The background stage of the point facts of Lemma DL for a sup-separated parent** (cover
form of `bgStage_of_one_le`): for the decoupled background field `(φ, α)` of a datum of the chart
at a realizable `s`, the bounds `BgBounds` hold and the composed datum lies in
`Ξ^c_K(𝔹_k(X); 1, b² ε' + K₂' δ₃)` (Theorem I-4b and `i5_stage1_sup_of_one_le`). -/
theorem bgStage_cover_of_one_le {b : ℝ} (hb₁ : 1 ≤ b) (hbC : b ≤ scaledC0 d) {c BG : ℝ}
    (hS : Dec2.DecSpecs d L Kc Cx c BG)
    (S : Dec2.CoverBase (coverOf Gp) Gp (compWeight L a₁) ν Kc Cx) (hG : CubeAligned Gp m₁)
    (hSS : SupSep Gp m₁) (hMM : 4 * L ^ 2 ≤ L ^ m₁) (ha₁ : 0 < a₁)
    (HBp : BgHyp d L K ϱ (compWeight L a₁) ν) (HBk : BgHyp d L K ϱ₁ (compWeight L a₁) ν)
    (hP : Precedes Gk Gp) (colk : ∀ z ∈ collar Gk, z ∈ Gp.Ω 1)
    {κ r₀ eps δ₃ : ℝ} (hκ : 0 < κ) (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hnum : ChainNum d L N m₁ BG κ r₀ eps δ₃) {X₀ X₁f : Finset (CTorus d L N₁ m₁ K)}
    (dsX₀ : ∀ x ∈ dataSites Gk, x ∈ X₀)
    (hN : ∀ x ∈ X₀, x ∈ Gp.Ω 1 → ∀ y : CTorus d L N₁ m₁ K,
      Green.torusDist d ((N₁ * L ^ m₁) * L ^ K) x y < r₀ * (L : ℝ) ^ m₁ * Gp.spacing x →
        y ∈ X₁f)
    (hT : (r₀ - 4 * d * (L : ℝ) ^ 3) * (L : ℝ) ^ m₁ / L ≤ ϱ - 1)
    (hr₀ : 4 * d * (L : ℝ) ^ 3 ≤ r₀)
    {s : DecParams Gp} (hs : ∀ P, ‖s P‖ < Real.exp κ)
    (hs1 : ∀ (P : ℕ × CTorus d L N₁ m₁ K) (hP : P ∈ cubeIdx Gp), P ∉ parCubes Gp X₁f →
      s ⟨P, hP⟩ = 1)
    {D : BgData Gp N} (hD : XiCData Gp (compWeight L a₁) ν K 1 eps D)
    {φ : Gp.Ω 1 × Fin N → ℂ} {α : Gp.Ω 1 → ℂ}
    (hI : IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α) :
    BgBounds Gp D φ α (K4 d L N BG κ * (xiC1 d * eps)) ∧
      XiCData Gk (compWeight L a₁) ν K 1 (b ^ 2 * eps + xiK2 d L N * δ₃)
        (composeData hP (compWeight L a₁) φ D) := by
  obtain ⟨hδ0, hδ0', hδ1, hνε, hDom, -⟩ := hnum.domain HBp hD
  have hsle : ∀ P, ‖s P‖ ≤ Real.exp κ := fun P => (hs P).le
  have hone : ∀ P : ↥(coverOf Gp).cubeIdx,
      ‖(fun _ : ↥(coverOf Gp).cubeIdx => (1 : ℂ)) P‖ ≤ Real.exp κ :=
    fun P => by simpa using Real.one_le_exp hκ.le
  obtain ⟨φ', α', -, hu', -, -, hbb⟩ := Dec2.i4b_exists_unique hS S HBp hκ.le hM (s := s) hsle
    hδ0 le_rfl hδ0' hδ1 hνε hDom
  obtain ⟨rfl, rfl⟩ := hu' φ α ⟨hI.small, hI.fixed, hI.field⟩
  obtain ⟨φ1, α1, hI1, -⟩ := Dec2.i4b_exists_unique hS S HBp hκ.le hM hone hδ0 le_rfl hδ0' hδ1
    hνε hDom
  exact ⟨hbb, i5_stage1_sup_of_one_le hb₁ hbC hS S hG hSS hMM ha₁ HBp HBk hP colk hκ.le hM hnum
    dsX₀ hN hT hr₀ hsle hs1 hD ⟨hI.small, hI.fixed, hI.field⟩ hI1⟩

/-- **The point facts for a functional of the decoupled objects, for the cover of `𝔹_{k+1}`**
(cover form of `point_facts_core`, the field `Sp : DGSetting` of `FlCore` replaced by
`Dec2.CoverBase (coverOf 𝔹_{k+1}) 𝔹_{k+1}`). -/
theorem point_facts_core_cover {c BG : ℝ} (hS : Dec2.DecSpecs d L Kc Cx c BG)
    (S : Dec2.CoverBase (coverOf Gp) Gp (compWeight L a₁) ν Kc Cx)
    (HBp : BgHyp d L K ϱ (compWeight L a₁) ν) {κ eps : ℝ} (hκ : 0 < κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) (heps : 0 < eps)
    (hsmall : (4 * d + 6) * ((2 * d + 1) * eps) ≤ 1) (hc7 : xiC1 d * eps ≤ c7 d L N BG κ)
    (hphi : (3 + K4 d L N BG κ) * (xiC1 d * eps) < 1 / 2) {δ₁ BG₂ : ℝ} (hδ₁ : 0 < δ₁)
    (hPmp : Precedes Hm Gp)
    {F₁ : Dec2.DecParams (coverOf Gp) × RawData d L (N₁ * L ^ m₁) K N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    (hF₁ : ∀ (s : Dec2.DecParams (coverOf Gp)) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
        (α : Gp.Ω 1 → ℂ),
        Dec2.IsDecBg (coverOf Gp) Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    {Sol : Dec2.DecParams (coverOf Gp) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    (hSol : ∀ p : Dec2.DecParams (coverOf Gp) × Edat Hm N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol p).1 = dphi Hm (Dec2.decG (coverOf Gp) Hm (compWeight L a₁) ν p.1) p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Dec2.DecFixed (coverOf Gp) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Small Hm (Sol p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm (Sol p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm (Sol p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gp) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol p).2))
    {X₁f : Finset (CTorus d L N₁ m₁ K)}
    {s : Dec2.DecParams (coverOf Gp)} (hs : ∀ P, ‖s P‖ < Real.exp κ)
    (hs1 : ∀ (P : ℕ × CTorus d L N₁ m₁ K) (hP : P ∈ (coverOf Gp).cubeIdx),
      P ∉ (coverOf Gp).parCubes X₁f → s ⟨P, hP⟩ = 1)
    {D : BgData Gp N} (hD : XiCData Gp (compWeight L a₁) ν K 1 eps D)
    {ψ' : CTorus d L N₁ m₁ K → Fin N → ℂ} (hψ : ψ' ∈ FlBall Hm δ₁) :
    ∃ (φ : Gp.Ω 1 × Fin N → ℂ) (α : Gp.Ω 1 → ℂ) (δφ : Hm.Ω 1 × Fin N → ℂ) (δα : Hm.Ω 1 → ℂ),
      Dec2.IsDecBg (coverOf Gp) Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α ∧
      F₁ (s, rawOf D) = (φ, α) ∧
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁
        (flEdat Gp Hm (φ, α) D.Ψ ψ') ∧
      Sol (s, flEdat Gp Hm (φ, α) D.Ψ ψ') = (δφ, δα) ∧
      ((φ, α), δφ, (rawOf D, ψ')) ∈ FlReal Gp Hm a₁ ν BG κ eps X₁f BG₂ δ₁ := by
  have hd0 : 0 < d := by have := HBp.hd; omega
  have hc1 := one_le_xiC1 d
  have hδ0 : 0 < xiC1 d * eps := by positivity
  have hU : InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D :=
    inUnionDomainC_of_inDomainC HBp hδ0
      (hc7.trans ((c7_le_bgC1 d L N BG κ).trans (bgC1_le_bgC0 d L N hd0))) hc7
      (xiCData_inDomainC HBp hsmall hD)
  obtain ⟨φ, α, hI, -, hbb⟩ := coverBg_exists hS S HBp hκ.le hM heps hsmall hc7 hs hD
  obtain ⟨hstrict, hmem⟩ := point_facts_core_of_bg hS.fam.2.1 HBp heps hsmall hphi hδ₁ hPmp hSol
    hs hs1 hD hI hbb hψ
  exact ⟨φ, α, _, _, ⟨hI.small, hI.fixed, hI.field⟩,
    hF₁ s D hs hU φ α ⟨hI.small, hI.fixed, hI.field⟩, hstrict, rfl, hmem⟩

/-- **(AE1), analyticity, for a functional of the decoupled objects of the cover of `𝔹_{k+1}`**
(cover form of `fanF_analytic`): the composite `Φ(F₁(s, Θ), Sol(s, …), (Θ, ψ'))` is analytic on the
chart `Ξ^c_K(𝔹_{k+1}; 1, ε')`, the ball of fluctuations and the polydisc of the parameters of the
cubes of `coverOf 𝔹_{k+1}` outside `X₁`. -/
theorem fanF_analytic_cover {c BG : ℝ} (hS : Dec2.DecSpecs d L Kc Cx c BG)
    (S : Dec2.CoverBase (coverOf Gp) Gp (compWeight L a₁) ν Kc Cx)
    (HBp : BgHyp d L K ϱ (compWeight L a₁) ν) {κ eps : ℝ} (hκ : 0 < κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) (heps : 0 < eps)
    (hsmall : (4 * d + 6) * ((2 * d + 1) * eps) ≤ 1) (hc7 : xiC1 d * eps ≤ c7 d L N BG κ)
    (hphi : (3 + K4 d L N BG κ) * (xiC1 d * eps) < 1 / 2) {δ₁ BG₂ : ℝ} (hδ₁ : 0 < δ₁)
    (hPmp : Precedes Hm Gp)
    {F₁ : Dec2.DecParams (coverOf Gp) × RawData d L (N₁ * L ^ m₁) K N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    (hF₁an : AnalyticOnNhd ℂ F₁ {q | (∀ P, ‖q.1 P‖ < Real.exp κ) ∧ ∃ D : BgData Gp N,
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D ∧ q.2 = (D.Ψ, D.h)})
    (hF₁ : ∀ (s : Dec2.DecParams (coverOf Gp)) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
        (α : Gp.Ω 1 → ℂ),
        Dec2.IsDecBg (coverOf Gp) Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    {Sol : Dec2.DecParams (coverOf Gp) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    (hSolan : AnalyticOnNhd ℂ Sol {p | (∀ P, ‖p.1 P‖ < Real.exp κ) ∧
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2})
    (hSol : ∀ p : Dec2.DecParams (coverOf Gp) × Edat Hm N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol p).1 = dphi Hm (Dec2.decG (coverOf Gp) Hm (compWeight L a₁) ν p.1) p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Dec2.DecFixed (coverOf Gp) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Small Hm (Sol p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm (Sol p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm (Sol p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gp) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol p).2))
    {X₁f : Finset (CTorus d L N₁ m₁ K)}
    {Φ : ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) → (Hm.Ω 1 × Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ) → ℂ}
    (hΦ : AnalyticOnNhd ℂ (fun t => Φ t.1 t.2.1 t.2.2)
      (FlReal Gp Hm a₁ ν BG κ eps X₁f BG₂ δ₁)) :
    AnalyticOnNhd ℂ (fun p : (RawData d L (N₁ * L ^ m₁) K N ×
        (CTorus d L N₁ m₁ K → Fin N → ℂ)) ×
        (ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) → ℂ) =>
      Φ (F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) p.2, p.1.1))
        (Sol (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) p.2,
          flEdat Gp Hm (F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) p.2, p.1.1))
            p.1.1.1 p.1.2)).1 p.1)
      ((XiCRaw Gp (compWeight L a₁) ν K 1 eps ×ˢ FlBall Hm δ₁) ×ˢ
        polydisc (0 : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) → ℂ) (fun _ => Real.exp κ)) :=
  fanF_analytic_of_bg hκ hS.fam.2.1 HBp heps hsmall hc7 hphi hδ₁ hPmp
    (fun _ hs _ hD => coverBg_exists hS S HBp hκ.le hM heps hsmall hc7 hs hD) hF₁an
    (fun s D hs hU φ α hI => hF₁ s D hs hU φ α ⟨hI.small, hI.fixed, hI.field⟩) hSolan hSol hΦ

/-- **The bound of a functional of the decoupled objects of the cover of `𝔹_{k+1}` on the
polydisc** (cover form of the bound in `i5_functional`). -/
theorem fanF_bound_cover {c BG : ℝ} (hS : Dec2.DecSpecs d L Kc Cx c BG)
    (S : Dec2.CoverBase (coverOf Gp) Gp (compWeight L a₁) ν Kc Cx)
    (HBp : BgHyp d L K ϱ (compWeight L a₁) ν) {κ eps : ℝ} (hκ : 0 < κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) (heps : 0 < eps)
    (hsmall : (4 * d + 6) * ((2 * d + 1) * eps) ≤ 1) (hc7 : xiC1 d * eps ≤ c7 d L N BG κ)
    (hphi : (3 + K4 d L N BG κ) * (xiC1 d * eps) < 1 / 2) {δ₁ BG₂ : ℝ} (hδ₁ : 0 < δ₁)
    (hPmp : Precedes Hm Gp)
    {F₁ : Dec2.DecParams (coverOf Gp) × RawData d L (N₁ * L ^ m₁) K N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    (hF₁ : ∀ (s : Dec2.DecParams (coverOf Gp)) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
        (α : Gp.Ω 1 → ℂ),
        Dec2.IsDecBg (coverOf Gp) Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    {Sol : Dec2.DecParams (coverOf Gp) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    (hSol : ∀ p : Dec2.DecParams (coverOf Gp) × Edat Hm N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol p).1 = dphi Hm (Dec2.decG (coverOf Gp) Hm (compWeight L a₁) ν p.1) p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Dec2.DecFixed (coverOf Gp) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Small Hm (Sol p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm (Sol p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm (Sol p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gp) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol p).2))
    {X₁f : Finset (CTorus d L N₁ m₁ K)}
    {Φ : ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) → (Hm.Ω 1 × Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ) → ℂ} {B : ℝ}
    (hΦbd : ∀ t ∈ FlReal Gp Hm a₁ ν BG κ eps X₁f BG₂ δ₁, ‖Φ t.1 t.2.1 t.2.2‖ ≤ B) :
    ∀ u ∈ XiCRaw (N := N) Gp (compWeight L a₁) ν K 1 eps ×ˢ FlBall Hm δ₁,
      ∀ s ∈ polydisc (0 : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) → ℂ)
        (fun _ => Real.exp κ),
      ‖Φ (F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s, u.1))
        (Sol (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s,
          flEdat Gp Hm (F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s, u.1))
            u.1.1 u.2)).1 u‖ ≤ B :=
  fanF_bound_of_bg hκ hS.fam.2.1 HBp heps hsmall hc7 hphi hδ₁ hPmp
    (fun _ hs _ hD => coverBg_exists hS S HBp hκ.le hM heps hsmall hc7 hs hD)
    (fun s D hs hU φ α hI => hF₁ s D hs hU φ α ⟨hI.small, hI.fixed, hI.field⟩) hSol hΦbd

end BgCover


section ChainCover

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱ₁ ϱ₂ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Gk : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁}
variable {Gj : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₂}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν Kc Cx : ℝ}

/-- **The triple of a datum at `s ≡ 1` is realizable, for the cover of `𝔹_{k+1}`** (cover form of
`triple_one_mem`). -/
theorem triple_one_mem_cover {c BG : ℝ} (hS : Dec2.DecSpecs d L Kc Cx c BG)
    (S : Dec2.CoverBase (coverOf Gp) Gp (compWeight L a₁) ν Kc Cx)
    (HBp : BgHyp d L (k + 1) ϱ (compWeight L a₁) ν) {κ eps : ℝ} (hκ : 0 < κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) (heps : 0 < eps)
    (hsmall : (4 * d + 6) * ((2 * d + 1) * eps) ≤ 1) (hc7 : xiC1 d * eps ≤ c7 d L N BG κ)
    (hphi : (3 + K4 d L N BG κ) * (xiC1 d * eps) < 1 / 2) {Kf Cf c₂ BG₂ δ₁ : ℝ} (hδ₁ : 0 < δ₁)
    (hδ₁le : δ₁ ≤ deltaStar' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hBle : 2 * (K4 d L N BG κ * (xiC1 d * eps)) ≤
      deltaStar' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hS2 : Dec2.DecSpecs d L Kf Cf c₂ BG₂)
    (SM : Dec2.FootLocal (coverOf Gp) Hm (compWeight L a₁) ν Kf Cf)
    (hM2 : c₂ * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) (hPmp : Precedes Hm Gp)
    {X₁f : Finset (CTorus d L N₁ m₁ (k + 1))}
    {D : BgData Gp N} (hD : XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D)
    {ψ' : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ} (hψ : ψ' ∈ FlBallLC Hm δ₁) :
    ((bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D,
        bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D),
      flFieldOne Gp Hm BG₂ κ a₁ ν D ψ', (rawOf D, ψ')) ∈
      FlRealLC Gp Hm a₁ ν BG κ eps X₁f BG₂ δ₁ := by
  have hE1 : 1 < Real.exp κ := Real.one_lt_exp_iff.2 hκ
  have hsx : ∀ P : ↥(cubeIdx Gp), ‖(fun _ : ↥(cubeIdx Gp) => (1 : ℂ)) P‖ < Real.exp κ :=
    fun P => by simpa using hE1
  have hI1 := coverBg_one hS S HBp hκ.le hM heps hsmall hc7 hD
  obtain ⟨φ, α, hI, hu, hbb⟩ := coverBg_exists hS S HBp hκ.le hM heps hsmall hc7 hsx hD
  obtain ⟨rfl, rfl⟩ := hu _ _ hI1
  exact triple_one_mem_of_bg hκ hS.fam.2.1 HBp heps hsmall hphi hδ₁ hδ₁le hBle hS2 SM hM2 hPmp hD
    hI hbb hψ

/-- **The facts at a realizable triple, for a sup-separated parent** (cover form of
`eTerm_chain_of_one_le`; the hypotheses are those of `point_facts_fl_sup_of_one_le`). -/
theorem eTerm_chain_cover_of_one_le {b : ℝ} (hb₁ : 1 ≤ b) (hbC : b ≤ scaledC0 d) {c BG : ℝ}
    (hS : Dec2.DecSpecs d L Kc Cx c BG)
    (S : Dec2.CoverBase (coverOf Gp) Gp (compWeight L a₁) ν Kc Cx) (hG : CubeAligned Gp m₁)
    (hSS : SupSep Gp m₁) (hMM : 4 * L ^ 2 ≤ L ^ m₁) (ha₁ : 0 < a₁)
    (HBp : BgHyp d L (k + 1) ϱ (compWeight L a₁) ν)
    (HBk : BgHyp d L (k + 1) ϱ₁ (compWeight L a₁) ν)
    (HBj : BgHyp d L (k + 1) ϱ₂ (compWeight L a₁) ν) (hP : Precedes Gk Gp) (hq : Precedes Gj Gk)
    (colk : ∀ z ∈ collar Gk, z ∈ Gp.Ω 1) (colj : ∀ z ∈ collar Gj, z ∈ Gk.Ω 1)
    {κ r₀ eps δ₃ : ℝ} (hκ : 0 < κ) (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hnum : ChainNum d L N m₁ BG κ r₀ eps δ₃) {X₀ X₁f : Finset (CTorus d L N₁ m₁ (k + 1))}
    (dsX₀ : ∀ x ∈ dataSites Gk, x ∈ X₀)
    (hN : ∀ x ∈ X₀, x ∈ Gp.Ω 1 → ∀ y : CTorus d L N₁ m₁ (k + 1),
      Green.torusDist d ((N₁ * L ^ m₁) * L ^ (k + 1)) x y < r₀ * (L : ℝ) ^ m₁ * Gp.spacing x →
        y ∈ X₁f)
    (hT : (r₀ - 4 * d * (L : ℝ) ^ 3) * (L : ℝ) ^ m₁ / L ≤ ϱ - 1)
    (hr₀ : 4 * d * (L : ℝ) ^ 3 ≤ r₀) {j : ℕ} (hj : j ≤ k + 1)
    {Kf Cf c₂ BG₂ δ₁ δfl : ℝ}
    (hF : FlSetting N Gp Gk Hm a₁ ν κ BG eps δ₃ Kf Cf c₂ BG₂ δ₁ δfl X₁f)
    {Fk : RawData d L (N₁ * L ^ m₁) (k + 1) N → (Gk.Ω 1 × Fin N → ℂ) × (Gk.Ω 1 → ℂ)}
    (hFk : ∀ D : BgData Gk N, InUnionDomainC Gk (bgC0 d L N) (bgC1 d L N) ν D →
      Fk (rawOf D) = (bgFieldC Gk (compWeight L a₁) ν (bgC0 d L N) D,
        bgMultC Gk (compWeight L a₁) ν (bgC0 d L N) D))
    {t : ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) × (Hm.Ω 1 × Fin N → ℂ) ×
      (RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ))}
    (ht : t ∈ FlRealLC Gp Hm a₁ ν BG κ eps X₁f BG₂ δ₁) :
    ∃ (D : BgData Gp N) (ψ' : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)
      (hlc : IsLayerConstant Hm ψ'), t.2.2 = (rawOf D, ψ') ∧
      XiCData Gk (compWeight L a₁) ν (k + 1) 1
        (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)
        (flDatum Gk hP hF.hPm (compWeight L a₁) t.1.1 t.2.1 D ψ' hlc) ∧
      d1Triple Gp Gk Hm (compWeight L a₁) t.1.1 t.2.1 t.2.2 =
        rawOf (flDatum Gk hP hF.hPm (compWeight L a₁) t.1.1 t.2.1 D ψ' hlc) ∧
      D2raw Gk Gj (compWeight L a₁) Fk
          (rawOf (flDatum Gk hP hF.hPm (compWeight L a₁) t.1.1 t.2.1 D ψ' hlc)) =
        rawOf (composeData hq (compWeight L a₁)
          (bgFieldC Gk (compWeight L a₁) ν (bgC0 d L N)
            (flDatum Gk hP hF.hPm (compWeight L a₁) t.1.1 t.2.1 D ψ' hlc))
          (flDatum Gk hP hF.hPm (compWeight L a₁) t.1.1 t.2.1 D ψ' hlc)) ∧
      XiCData Gj (compWeight L a₁) ν j b
        (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)
        (composeData hq (compWeight L a₁)
          (bgFieldC Gk (compWeight L a₁) ν (bgC0 d L N)
            (flDatum Gk hP hF.hPm (compWeight L a₁) t.1.1 t.2.1 D ψ' hlc))
          (flDatum Gk hP hF.hPm (compWeight L a₁) t.1.1 t.2.1 D ψ' hlc)) :=
  eTerm_chain_of_bg hb₁ hbC hS.fam.2.1 ha₁ HBp HBk HBj hP hq colj hnum hj hκ hF hFk
    (fun _ hs hs1 _ hD _ _ hI => bgStage_cover_of_one_le hb₁ hbC hS S hG hSS hMM ha₁ HBp HBk hP
      colk hκ hM hnum dsX₀ hN hT hr₀ hs hs1 hD hI) ht

/-- **Analyticity of the old-term functional on the realizable triples, for a sup-separated
parent** (cover form of `eTermFun_analytic_of_one_le`). -/
theorem eTermFun_analytic_cover_of_one_le {b : ℝ} (hb₁ : 1 ≤ b) (hbC : b ≤ scaledC0 d)
    {c BG : ℝ} (hS : Dec2.DecSpecs d L Kc Cx c BG)
    (S : Dec2.CoverBase (coverOf Gp) Gp (compWeight L a₁) ν Kc Cx) (hG : CubeAligned Gp m₁)
    (hSS : SupSep Gp m₁) (hMM : 4 * L ^ 2 ≤ L ^ m₁) (ha₁ : 0 < a₁)
    (HBp : BgHyp d L (k + 1) ϱ (compWeight L a₁) ν)
    (HBk : BgHyp d L (k + 1) ϱ₁ (compWeight L a₁) ν)
    (HBj : BgHyp d L (k + 1) ϱ₂ (compWeight L a₁) ν) (hP : Precedes Gk Gp) (hq : Precedes Gj Gk)
    (colk : ∀ z ∈ collar Gk, z ∈ Gp.Ω 1) (colj : ∀ z ∈ collar Gj, z ∈ Gk.Ω 1)
    {κ r₀ eps δ₃ : ℝ} (hκ : 0 < κ) (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hnum : ChainNum d L N m₁ BG κ r₀ eps δ₃) {X₀ X₁f : Finset (CTorus d L N₁ m₁ (k + 1))}
    (dsX₀ : ∀ x ∈ dataSites Gk, x ∈ X₀)
    (hN : ∀ x ∈ X₀, x ∈ Gp.Ω 1 → ∀ y : CTorus d L N₁ m₁ (k + 1),
      Green.torusDist d ((N₁ * L ^ m₁) * L ^ (k + 1)) x y < r₀ * (L : ℝ) ^ m₁ * Gp.spacing x →
        y ∈ X₁f)
    (hT : (r₀ - 4 * d * (L : ℝ) ^ 3) * (L : ℝ) ^ m₁ / L ≤ ϱ - 1)
    (hr₀ : 4 * d * (L : ℝ) ^ 3 ≤ r₀) {j : ℕ} (hj : j ≤ k + 1)
    {Kf Cf c₂ BG₂ δ₁ δfl : ℝ}
    (hF : FlSetting N Gp Gk Hm a₁ ν κ BG eps δ₃ Kf Cf c₂ BG₂ δ₁ δfl X₁f)
    {Fk : RawData d L (N₁ * L ^ m₁) (k + 1) N → (Gk.Ω 1 × Fin N → ℂ) × (Gk.Ω 1 → ℂ)}
    (hFkan : AnalyticOnNhd ℂ Fk {p | ∃ D : BgData Gk N,
      InUnionDomainC Gk (bgC0 d L N) (bgC1 d L N) ν D ∧ p = (D.Ψ, D.h)})
    (hFk : ∀ D : BgData Gk N, InUnionDomainC Gk (bgC0 d L N) (bgC1 d L N) ν D →
      Fk (rawOf D) = (bgFieldC Gk (compWeight L a₁) ν (bgC0 d L N) D,
        bgMultC Gk (compWeight L a₁) ν (bgC0 d L N) D))
    {E : RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ}
    (hE : AnalyticOnNhd ℂ E (XiCRaw Gj (compWeight L a₁) ν j b
      (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl))) :
    AnalyticOnNhd ℂ (fun t : ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) × (Hm.Ω 1 × Fin N → ℂ) ×
        (RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)) =>
      eTermFun Gp Gk Gj Hm (compWeight L a₁) Fk E t.1 t.2.1 t.2.2)
      (FlRealLC Gp Hm a₁ ν BG κ eps X₁f BG₂ δ₁) :=
  eTermFun_analytic_of_bg hb₁ hbC hS.fam.2.1 ha₁ HBp HBk HBj hP hq colj hnum hj hκ hF hFkan hFk
    (fun _ hs hs1 _ hD _ _ hI => bgStage_cover_of_one_le hb₁ hbC hS S hG hSS hMM ha₁ HBp HBk hP
      colk hκ hM hnum dsX₀ hN hT hr₀ hs hs1 hD hI) hE

/-- **The bound of the old-term functional on the realizable triples, for a sup-separated
parent** (cover form of `eTermFun_bound_of_one_le`). -/
theorem eTermFun_bound_cover_of_one_le {b : ℝ} (hb₁ : 1 ≤ b) (hbC : b ≤ scaledC0 d)
    {c BG : ℝ} (hS : Dec2.DecSpecs d L Kc Cx c BG)
    (S : Dec2.CoverBase (coverOf Gp) Gp (compWeight L a₁) ν Kc Cx) (hG : CubeAligned Gp m₁)
    (hSS : SupSep Gp m₁) (hMM : 4 * L ^ 2 ≤ L ^ m₁) (ha₁ : 0 < a₁)
    (HBp : BgHyp d L (k + 1) ϱ (compWeight L a₁) ν)
    (HBk : BgHyp d L (k + 1) ϱ₁ (compWeight L a₁) ν)
    (HBj : BgHyp d L (k + 1) ϱ₂ (compWeight L a₁) ν) (hP : Precedes Gk Gp) (hq : Precedes Gj Gk)
    (colk : ∀ z ∈ collar Gk, z ∈ Gp.Ω 1) (colj : ∀ z ∈ collar Gj, z ∈ Gk.Ω 1)
    {κ r₀ eps δ₃ : ℝ} (hκ : 0 < κ) (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hnum : ChainNum d L N m₁ BG κ r₀ eps δ₃) {X₀ X₁f : Finset (CTorus d L N₁ m₁ (k + 1))}
    (dsX₀ : ∀ x ∈ dataSites Gk, x ∈ X₀)
    (hN : ∀ x ∈ X₀, x ∈ Gp.Ω 1 → ∀ y : CTorus d L N₁ m₁ (k + 1),
      Green.torusDist d ((N₁ * L ^ m₁) * L ^ (k + 1)) x y < r₀ * (L : ℝ) ^ m₁ * Gp.spacing x →
        y ∈ X₁f)
    (hT : (r₀ - 4 * d * (L : ℝ) ^ 3) * (L : ℝ) ^ m₁ / L ≤ ϱ - 1)
    (hr₀ : 4 * d * (L : ℝ) ^ 3 ≤ r₀) {j : ℕ} (hj : j ≤ k + 1)
    {Kf Cf c₂ BG₂ δ₁ δfl : ℝ}
    (hF : FlSetting N Gp Gk Hm a₁ ν κ BG eps δ₃ Kf Cf c₂ BG₂ δ₁ δfl X₁f)
    {Fk : RawData d L (N₁ * L ^ m₁) (k + 1) N → (Gk.Ω 1 × Fin N → ℂ) × (Gk.Ω 1 → ℂ)}
    (hFk : ∀ D : BgData Gk N, InUnionDomainC Gk (bgC0 d L N) (bgC1 d L N) ν D →
      Fk (rawOf D) = (bgFieldC Gk (compWeight L a₁) ν (bgC0 d L N) D,
        bgMultC Gk (compWeight L a₁) ν (bgC0 d L N) D))
    {E : RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ} {B : ℝ}
    (hEb : ∀ r ∈ XiCRaw Gj (compWeight L a₁) ν j b
      (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl), ‖E r‖ ≤ B)
    {t : ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) × (Hm.Ω 1 × Fin N → ℂ) ×
      (RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ))}
    (ht : t ∈ FlRealLC Gp Hm a₁ ν BG κ eps X₁f BG₂ δ₁) :
    ‖eTermFun Gp Gk Gj Hm (compWeight L a₁) Fk E t.1 t.2.1 t.2.2‖ ≤ B :=
  eTermFun_bound_of_bg hb₁ hbC hS.fam.2.1 ha₁ HBp HBk HBj hP hq colj hnum hj hκ hF hFk
    (fun _ hs hs1 _ hD _ _ hI => bgStage_cover_of_one_le hb₁ hbC hS S hG hSS hMM ha₁ HBp HBk hP
      colk hκ hM hnum dsX₀ hN hT hr₀ hs hs1 hD hI) hEb ht

/-- **The old-term functional at the triple of a datum, for a sup-separated parent** (cover form
of `eTermFun_value`; the right side is the value of `flComp`, which is defined only under
`BgSetting`): `E(ψ(𝔹_j(X), 𝔹_k(X); ψ(𝔹_k(X), 𝔹_{k+1}; Θ) + δψ(𝔹_k(X), 𝔹_k; ψ')))`. -/
theorem eTermFun_value_cover {c BG : ℝ} (hS : Dec2.DecSpecs d L Kc Cx c BG)
    (S : Dec2.CoverBase (coverOf Gp) Gp (compWeight L a₁) ν Kc Cx) (hG : CubeAligned Gp m₁)
    (hSS : SupSep Gp m₁) (hMM : 4 * L ^ 2 ≤ L ^ m₁) (ha₁ : 0 < a₁)
    (HBp : BgHyp d L (k + 1) ϱ (compWeight L a₁) ν)
    (HBk : BgHyp d L (k + 1) ϱ₁ (compWeight L a₁) ν)
    (HBj : BgHyp d L (k + 1) ϱ₂ (compWeight L a₁) ν) (hP : Precedes Gk Gp) (hq : Precedes Gj Gk)
    (colk : ∀ z ∈ collar Gk, z ∈ Gp.Ω 1) (colj : ∀ z ∈ collar Gj, z ∈ Gk.Ω 1)
    {κ r₀ eps δ₃ : ℝ} (hκ : 0 < κ) (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hnum : ChainNum d L N m₁ BG κ r₀ eps δ₃) {X₀ X₁f : Finset (CTorus d L N₁ m₁ (k + 1))}
    (dsX₀ : ∀ x ∈ dataSites Gk, x ∈ X₀)
    (hN : ∀ x ∈ X₀, x ∈ Gp.Ω 1 → ∀ y : CTorus d L N₁ m₁ (k + 1),
      Green.torusDist d ((N₁ * L ^ m₁) * L ^ (k + 1)) x y < r₀ * (L : ℝ) ^ m₁ * Gp.spacing x →
        y ∈ X₁f)
    (hT : (r₀ - 4 * d * (L : ℝ) ^ 3) * (L : ℝ) ^ m₁ / L ≤ ϱ - 1)
    (hr₀ : 4 * d * (L : ℝ) ^ 3 ≤ r₀) {j : ℕ} (hj : j ≤ k + 1)
    {Kf Cf c₂ BG₂ δ₁ δfl : ℝ}
    (hF : FlSetting N Gp Gk Hm a₁ ν κ BG eps δ₃ Kf Cf c₂ BG₂ δ₁ δfl X₁f)
    {Fk : RawData d L (N₁ * L ^ m₁) (k + 1) N → (Gk.Ω 1 × Fin N → ℂ) × (Gk.Ω 1 → ℂ)}
    (hFk : ∀ D : BgData Gk N, InUnionDomainC Gk (bgC0 d L N) (bgC1 d L N) ν D →
      Fk (rawOf D) = (bgFieldC Gk (compWeight L a₁) ν (bgC0 d L N) D,
        bgMultC Gk (compWeight L a₁) ν (bgC0 d L N) D))
    (E : RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ)
    {D : BgData Gp N} (hD : XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D)
    {ψ' : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ} (hψ : ψ' ∈ FlBallLC Hm δ₁) :
    eTermFun Gp Gk Gj Hm (compWeight L a₁) Fk E
        (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D,
          bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D)
        (flFieldOne Gp Hm BG₂ κ a₁ ν D ψ') (rawOf D, ψ') =
      E (rawOf (composeData hq (compWeight L a₁)
        (bgFieldC Gk (compWeight L a₁) ν (bgC0 d L N)
          (flDatumOne Hm BG₂ κ hP hF.hPm a₁ ν D ψ' hψ.2))
        (flDatumOne Hm BG₂ κ hP hF.hPm a₁ ν D ψ' hψ.2))) :=
  eTermFun_value_of_bg (one_le_scaledC0 d) le_rfl hS.fam.2.1 ha₁ HBp HBk HBj hP hq colj hnum hj hκ
    hF hFk (fun _ hs hs1 _ hD _ _ hI => bgStage_cover_of_one_le (one_le_scaledC0 d) le_rfl hS S hG
      hSS hMM ha₁ HBp HBk hP colk hκ hM hnum dsX₀ hN hT hr₀ hs hs1 hD hI) E hD
    (coverBg_one hS S HBp hκ.le hM hnum.eps_pos hnum.small1 hnum.c7le hD) hψ

end ChainCover


section LocalB

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ₁ ϱm : ℝ}
variable {Gk : GeneratingSet d L (N₁ * L ^ m₁) K ϱ₁} {Hm : GeneratingSet d L (N₁ * L ^ m₁) K ϱm}

/-- **The cover data of the literal local generator** `𝔹 = localB t ht Y …` at the separation
`ϱ = 5 L M₁` and the collar `r₀ = 4 d L³ + L`: `Dec2.CoverBase (coverOf 𝔹) 𝔹` with the constants
`mixedKc d L`, `Cchi d L`, cube alignment, sup-separation, and the target bound
`((r₀ - 4 d L³)/L) M₁ ≤ ϱ - 1` with `r₀ ≥ 4 d L³` (`localB_coverBase`, `localB_cubeAligned`,
`localB_supSep`, `target_le_minSep`).  These are the inputs of the cover forms of the point facts
and of the fluctuation core in place of `DGSetting` and `r₀ M₁ ≤ ϱ - 1`. -/
theorem localB_coverData {t : ℕ} (ht : t ≤ K) (Y : Set (CTorus d L N₁ m₁ K)) (hN₁ : 5 < N₁)
    (hMM : 4 * L ^ 2 ≤ L ^ m₁)
    (hag : 2 * d * Real.log L ≤ agmonRate d / 16 * (minSep L (L ^ m₁) - 1)) {a : ℕ → ℝ} {ν : ℝ}
    (HBp : BgHyp d L K (minSep L (L ^ m₁)) a ν) :
    Dec2.CoverBase (coverOf (GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁)))))
        (GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁)))) a ν (Dec2.mixedKc d L) (Cchi d L) ∧
      CubeAligned (GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁)))) m₁ ∧
      SupSep (GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁)))) m₁ ∧
      ((4 * d * (L : ℝ) ^ 3 + L) - 4 * d * (L : ℝ) ^ 3) * (L : ℝ) ^ m₁ / L ≤
        minSep L (L ^ m₁) - 1 ∧
      4 * d * (L : ℝ) ^ 3 ≤ 4 * d * (L : ℝ) ^ 3 + L := by
  have hL : 3 ≤ L := HBp.hL
  have hm₁ : 2 ≤ m₁ := by
    by_contra h
    push Not at h
    have hL2 : L ^ m₁ ≤ L ^ 1 := Nat.pow_le_pow_right (by omega) (by omega)
    nlinarith
  obtain ⟨hT1, hT2⟩ := target_le_minSep (d := d) (m₁ := m₁) (by omega : 1 ≤ L)
  exact ⟨localB_coverBase ht Y le_rfl hN₁ hm₁ hMM HBp.hd hL HBp.mass HBp.massLe HBp.weights hag,
    localB_cubeAligned ht Y le_rfl hm₁, localB_supSep ht Y le_rfl, by rw [hT1]; exact hT2,
    by linarith [show (0 : ℝ) ≤ L from by positivity]⟩


/-- **(AE1) for the literal local generator** `𝔹_{k+1}(Y) = localB t ht Y …` at `ϱ = 5 L M₁`:
`fanF_analytic_cover` with the cover base `localB_coverBase`.  The composite
`Φ(F₁(s, Θ), Sol(s, …), (Θ, ψ'))` built from the decoupled background field of
`(coverOf 𝔹_{k+1}(Y), 𝔹_{k+1}(Y))` and the fluctuation field of `(coverOf 𝔹_{k+1}(Y), H⁻)` is
analytic on the local chart `Ξ^c_K(𝔹_{k+1}(Y); 1, ε')`, the ball of fluctuations of `H⁻` and the
polydisc of the parameters of the cubes of `coverOf 𝔹_{k+1}(Y)` outside `X₁`. -/
theorem localB_fanF_analytic {t : ℕ} (ht : t ≤ K) (Y : Set (CTorus d L N₁ m₁ K)) (hN₁ : 5 < N₁)
    (hMM : 4 * L ^ 2 ≤ L ^ m₁)
    (hag : 2 * d * Real.log L ≤ agmonRate d / 16 * (minSep L (L ^ m₁) - 1)) {a₁ ν : ℝ}
    {c BG : ℝ} (hS : Dec2.DecSpecs d L (Dec2.mixedKc d L) (Cchi d L) c BG)
    (HBp : BgHyp d L K (minSep L (L ^ m₁)) (compWeight L a₁) ν) {κ eps : ℝ} (hκ : 0 < κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) (heps : 0 < eps)
    (hsmall : (4 * d + 6) * ((2 * d + 1) * eps) ≤ 1) (hc7 : xiC1 d * eps ≤ c7 d L N BG κ)
    (hphi : (3 + K4 d L N BG κ) * (xiC1 d * eps) < 1 / 2) {δ₁ BG₂ : ℝ} (hδ₁ : 0 < δ₁)
    (hPmp : Precedes Hm (GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁)))))
    {F₁ : Dec2.DecParams (coverOf (GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁))))) ×
        RawData d L (N₁ * L ^ m₁) K N →
      ((GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁)))).Ω 1 × Fin N → ℂ) ×
        ((GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁)))).Ω 1 → ℂ)}
    (hF₁an : AnalyticOnNhd ℂ F₁ {q | (∀ P, ‖q.1 P‖ < Real.exp κ) ∧
      ∃ D : BgData (GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁)))) N,
        InUnionDomainC (GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁)))) (bgC0 d L N)
          (c7 d L N BG κ) ν D ∧ q.2 = (D.Ψ, D.h)})
    (hF₁ : ∀ (s : Dec2.DecParams (coverOf (GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁))))))
      (D : BgData (GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁)))) N),
      (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC (GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁)))) (bgC0 d L N)
        (c7 d L N BG κ) ν D →
      ∀ (φ : (GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁)))).Ω 1 × Fin N → ℂ)
        (α : (GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁)))).Ω 1 → ℂ),
        Dec2.IsDecBg (coverOf (GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁)))))
          (GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁) ν
          (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    {Sol : Dec2.DecParams (coverOf (GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁))))) ×
      Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    (hSolan : AnalyticOnNhd ℂ Sol {p | (∀ P, ‖p.1 P‖ < Real.exp κ) ∧
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2})
    (hSol : ∀ p : Dec2.DecParams (coverOf (GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁))))) ×
        Edat Hm N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol p).1 = dphi Hm (Dec2.decG (coverOf (GsSpec.localB t ht Y
            (le_refl (minSep L (L ^ m₁))))) Hm (compWeight L a₁) ν p.1) p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Dec2.DecFixed (coverOf (GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁))))) Hm
          (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Small Hm (Sol p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm (Sol p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm (Sol p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁))))) Hm
            (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol p).2))
    {X₁f : Finset (CTorus d L N₁ m₁ K)}
    {Φ : (((GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁)))).Ω 1 × Fin N → ℂ) ×
        ((GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁)))).Ω 1 → ℂ)) →
      (Hm.Ω 1 × Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ) → ℂ}
    (hΦ : AnalyticOnNhd ℂ (fun q => Φ q.1 q.2.1 q.2.2)
      (FlReal (GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁)))) Hm a₁ ν BG κ eps X₁f BG₂
        δ₁)) :
    AnalyticOnNhd ℂ (fun p : (RawData d L (N₁ * L ^ m₁) K N ×
        (CTorus d L N₁ m₁ K → Fin N → ℂ)) ×
        (ParIdx (GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁))))
          (↑X₁f : Set (CTorus d L N₁ m₁ K)) → ℂ) =>
      Φ (F₁ (extParams (GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁))))
          (↑X₁f : Set (CTorus d L N₁ m₁ K)) p.2, p.1.1))
        (Sol (extParams (GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁))))
            (↑X₁f : Set (CTorus d L N₁ m₁ K)) p.2,
          flEdat (GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁)))) Hm
            (F₁ (extParams (GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁))))
              (↑X₁f : Set (CTorus d L N₁ m₁ K)) p.2, p.1.1))
            p.1.1.1 p.1.2)).1 p.1)
      ((XiCRaw (GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁) ν K 1 eps ×ˢ
          FlBall Hm δ₁) ×ˢ
        polydisc (0 : ParIdx (GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁))))
          (↑X₁f : Set (CTorus d L N₁ m₁ K)) → ℂ) (fun _ => Real.exp κ)) :=
  fanF_analytic_cover hS (localB_coverData ht Y hN₁ hMM hag HBp).1 HBp hκ hM heps hsmall hc7 hphi
    hδ₁ hPmp hF₁an hF₁ hSolan hSol hΦ

/-- **The bound of the composite for the literal local generator** (`fanF_bound_cover` at
`𝔹_{k+1}(Y) = localB t ht Y …`, `ϱ = 5 L M₁`). -/
theorem localB_fanF_bound {t : ℕ} (ht : t ≤ K) (Y : Set (CTorus d L N₁ m₁ K)) (hN₁ : 5 < N₁)
    (hMM : 4 * L ^ 2 ≤ L ^ m₁)
    (hag : 2 * d * Real.log L ≤ agmonRate d / 16 * (minSep L (L ^ m₁) - 1)) {a₁ ν : ℝ}
    {c BG : ℝ} (hS : Dec2.DecSpecs d L (Dec2.mixedKc d L) (Cchi d L) c BG)
    (HBp : BgHyp d L K (minSep L (L ^ m₁)) (compWeight L a₁) ν) {κ eps : ℝ} (hκ : 0 < κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) (heps : 0 < eps)
    (hsmall : (4 * d + 6) * ((2 * d + 1) * eps) ≤ 1) (hc7 : xiC1 d * eps ≤ c7 d L N BG κ)
    (hphi : (3 + K4 d L N BG κ) * (xiC1 d * eps) < 1 / 2) {δ₁ BG₂ : ℝ} (hδ₁ : 0 < δ₁)
    (hPmp : Precedes Hm (GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁)))))
    {F₁ : Dec2.DecParams (coverOf (GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁))))) ×
        RawData d L (N₁ * L ^ m₁) K N →
      ((GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁)))).Ω 1 × Fin N → ℂ) ×
        ((GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁)))).Ω 1 → ℂ)}
    (hF₁ : ∀ (s : Dec2.DecParams (coverOf (GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁))))))
      (D : BgData (GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁)))) N),
      (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC (GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁)))) (bgC0 d L N)
        (c7 d L N BG κ) ν D →
      ∀ (φ : (GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁)))).Ω 1 × Fin N → ℂ)
        (α : (GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁)))).Ω 1 → ℂ),
        Dec2.IsDecBg (coverOf (GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁)))))
          (GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁) ν
          (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    {Sol : Dec2.DecParams (coverOf (GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁))))) ×
      Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    (hSol : ∀ p : Dec2.DecParams (coverOf (GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁))))) ×
        Edat Hm N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol p).1 = dphi Hm (Dec2.decG (coverOf (GsSpec.localB t ht Y
            (le_refl (minSep L (L ^ m₁))))) Hm (compWeight L a₁) ν p.1) p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Dec2.DecFixed (coverOf (GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁))))) Hm
          (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Small Hm (Sol p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm (Sol p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm (Sol p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁))))) Hm
            (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol p).2))
    {X₁f : Finset (CTorus d L N₁ m₁ K)}
    {Φ : (((GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁)))).Ω 1 × Fin N → ℂ) ×
        ((GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁)))).Ω 1 → ℂ)) →
      (Hm.Ω 1 × Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ) → ℂ} {Bd : ℝ}
    (hΦbd : ∀ q ∈ FlReal (GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁)))) Hm a₁ ν BG κ eps
      X₁f BG₂ δ₁, ‖Φ q.1 q.2.1 q.2.2‖ ≤ Bd) :
    ∀ u ∈ XiCRaw (N := N) (GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁)
        ν K 1 eps ×ˢ FlBall Hm δ₁,
      ∀ s ∈ polydisc (0 : ParIdx (GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁))))
          (↑X₁f : Set (CTorus d L N₁ m₁ K)) → ℂ) (fun _ => Real.exp κ),
      ‖Φ (F₁ (extParams (GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁))))
          (↑X₁f : Set (CTorus d L N₁ m₁ K)) s, u.1))
        (Sol (extParams (GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁))))
            (↑X₁f : Set (CTorus d L N₁ m₁ K)) s,
          flEdat (GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁)))) Hm
            (F₁ (extParams (GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁))))
              (↑X₁f : Set (CTorus d L N₁ m₁ K)) s, u.1))
            u.1.1 u.2)).1 u‖ ≤ Bd :=
  fanF_bound_cover hS (localB_coverData ht Y hN₁ hMM hag HBp).1 HBp hκ hM heps hsmall hc7 hphi hδ₁
    hPmp hF₁ hSol hΦbd

end LocalB

section LocalPairE

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ₁ ϱ₂ ϱm : ℝ}
variable {Gk : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁}
variable {Gj : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₂}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm} {a₁ ν : ℝ}

/-- **Analyticity of the old-term functional on the realizable triples of the literal local
generator** `𝔹_{k+1}(Y) = localB t ht Y …` at `ϱ = 5 L M₁` and `r₀ = 4 d L³ + L`
(`eTermFun_analytic_cover_of_one_le` with `localB_coverData`), for every fluctuation generating set
`H⁻` with `FlSetting` (for the local pair `H⁻ = 𝔹_k(Y)` see `localB_pair_flSetting`). -/
theorem localB_eTermFun_analytic {b : ℝ} (hb₁ : 1 ≤ b) (hbC : b ≤ scaledC0 d) {t : ℕ}
    (ht : t ≤ k + 1)
    (Y : Set (CTorus d L N₁ m₁ (k + 1))) (hN₁ : 5 < N₁) (hMM : 4 * L ^ 2 ≤ L ^ m₁)
    (hag : 2 * d * Real.log L ≤ agmonRate d / 16 * (minSep L (L ^ m₁) - 1)) {c BG : ℝ}
    (hS : Dec2.DecSpecs d L (Dec2.mixedKc d L) (Cchi d L) c BG) (ha₁ : 0 < a₁)
    (HBp : BgHyp d L (k + 1) (minSep L (L ^ m₁)) (compWeight L a₁) ν)
    (HBk : BgHyp d L (k + 1) ϱ₁ (compWeight L a₁) ν)
    (HBj : BgHyp d L (k + 1) ϱ₂ (compWeight L a₁) ν)
    (hP : Precedes Gk (GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁))))) (hq : Precedes Gj Gk)
    (colk : ∀ z ∈ collar Gk, z ∈ (GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁)))).Ω 1)
    (colj : ∀ z ∈ collar Gj, z ∈ Gk.Ω 1)
    {κ eps δ₃ : ℝ} (hκ : 0 < κ) (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hnum : ChainNum d L N m₁ BG κ (4 * d * (L : ℝ) ^ 3 + L) eps δ₃)
    {X₀ X₁f : Finset (CTorus d L N₁ m₁ (k + 1))} (dsX₀ : ∀ x ∈ dataSites Gk, x ∈ X₀)
    (hN : ∀ x ∈ X₀, x ∈ (GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁)))).Ω 1 →
      ∀ y : CTorus d L N₁ m₁ (k + 1), Green.torusDist d ((N₁ * L ^ m₁) * L ^ (k + 1)) x y <
        (4 * d * (L : ℝ) ^ 3 + L) * (L : ℝ) ^ m₁ *
          (GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁)))).spacing x → y ∈ X₁f)
    {j : ℕ} (hj : j ≤ k + 1) {Kf Cf c₂ BG₂ δ₁ δfl : ℝ}
    (hF : FlSetting N (GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁)))) Gk Hm a₁ ν κ BG eps δ₃
      Kf Cf c₂ BG₂ δ₁ δfl X₁f)
    {Fk : RawData d L (N₁ * L ^ m₁) (k + 1) N → (Gk.Ω 1 × Fin N → ℂ) × (Gk.Ω 1 → ℂ)}
    (hFkan : AnalyticOnNhd ℂ Fk {p | ∃ D : BgData Gk N,
      InUnionDomainC Gk (bgC0 d L N) (bgC1 d L N) ν D ∧ p = (D.Ψ, D.h)})
    (hFk : ∀ D : BgData Gk N, InUnionDomainC Gk (bgC0 d L N) (bgC1 d L N) ν D →
      Fk (rawOf D) = (bgFieldC Gk (compWeight L a₁) ν (bgC0 d L N) D,
        bgMultC Gk (compWeight L a₁) ν (bgC0 d L N) D))
    {E : RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ}
    (hE : AnalyticOnNhd ℂ E (XiCRaw Gj (compWeight L a₁) ν j b
      (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl))) :
    AnalyticOnNhd ℂ (fun q :
        (((GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁)))).Ω 1 × Fin N → ℂ) ×
          ((GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁)))).Ω 1 → ℂ)) ×
        (Hm.Ω 1 × Fin N → ℂ) ×
        (RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)) =>
      eTermFun (GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁)))) Gk Gj Hm (compWeight L a₁) Fk E
        q.1 q.2.1 q.2.2)
      (FlRealLC (GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁)))) Hm a₁ ν BG κ eps X₁f BG₂
        δ₁) := by
  have hcd := localB_coverData ht Y hN₁ hMM hag HBp
  exact eTermFun_analytic_cover_of_one_le hb₁ hbC hS hcd.1 hcd.2.1 hcd.2.2.1 hMM ha₁ HBp HBk HBj
    hP hq colk colj hκ hM hnum dsX₀ hN hcd.2.2.2.1 hcd.2.2.2.2 hj hF hFkan hFk hE

/-- **The bound of the old-term functional on the realizable triples of the literal local
generator** (`eTermFun_bound_cover_of_one_le` with `localB_coverData`). -/
theorem localB_eTermFun_bound {b : ℝ} (hb₁ : 1 ≤ b) (hbC : b ≤ scaledC0 d) {t : ℕ}
    (ht : t ≤ k + 1)
    (Y : Set (CTorus d L N₁ m₁ (k + 1))) (hN₁ : 5 < N₁) (hMM : 4 * L ^ 2 ≤ L ^ m₁)
    (hag : 2 * d * Real.log L ≤ agmonRate d / 16 * (minSep L (L ^ m₁) - 1)) {c BG : ℝ}
    (hS : Dec2.DecSpecs d L (Dec2.mixedKc d L) (Cchi d L) c BG) (ha₁ : 0 < a₁)
    (HBp : BgHyp d L (k + 1) (minSep L (L ^ m₁)) (compWeight L a₁) ν)
    (HBk : BgHyp d L (k + 1) ϱ₁ (compWeight L a₁) ν)
    (HBj : BgHyp d L (k + 1) ϱ₂ (compWeight L a₁) ν)
    (hP : Precedes Gk (GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁))))) (hq : Precedes Gj Gk)
    (colk : ∀ z ∈ collar Gk, z ∈ (GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁)))).Ω 1)
    (colj : ∀ z ∈ collar Gj, z ∈ Gk.Ω 1)
    {κ eps δ₃ : ℝ} (hκ : 0 < κ) (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hnum : ChainNum d L N m₁ BG κ (4 * d * (L : ℝ) ^ 3 + L) eps δ₃)
    {X₀ X₁f : Finset (CTorus d L N₁ m₁ (k + 1))} (dsX₀ : ∀ x ∈ dataSites Gk, x ∈ X₀)
    (hN : ∀ x ∈ X₀, x ∈ (GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁)))).Ω 1 →
      ∀ y : CTorus d L N₁ m₁ (k + 1), Green.torusDist d ((N₁ * L ^ m₁) * L ^ (k + 1)) x y <
        (4 * d * (L : ℝ) ^ 3 + L) * (L : ℝ) ^ m₁ *
          (GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁)))).spacing x → y ∈ X₁f)
    {j : ℕ} (hj : j ≤ k + 1) {Kf Cf c₂ BG₂ δ₁ δfl : ℝ}
    (hF : FlSetting N (GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁)))) Gk Hm a₁ ν κ BG eps δ₃
      Kf Cf c₂ BG₂ δ₁ δfl X₁f)
    {Fk : RawData d L (N₁ * L ^ m₁) (k + 1) N → (Gk.Ω 1 × Fin N → ℂ) × (Gk.Ω 1 → ℂ)}
    (hFk : ∀ D : BgData Gk N, InUnionDomainC Gk (bgC0 d L N) (bgC1 d L N) ν D →
      Fk (rawOf D) = (bgFieldC Gk (compWeight L a₁) ν (bgC0 d L N) D,
        bgMultC Gk (compWeight L a₁) ν (bgC0 d L N) D))
    {E : RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ} {Bd : ℝ}
    (hEb : ∀ r ∈ XiCRaw Gj (compWeight L a₁) ν j b
      (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl), ‖E r‖ ≤ Bd)
    {q : (((GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁)))).Ω 1 × Fin N → ℂ) ×
        ((GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁)))).Ω 1 → ℂ)) × (Hm.Ω 1 × Fin N → ℂ) ×
      (RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ))}
    (hq' : q ∈ FlRealLC (GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁)))) Hm a₁ ν BG κ eps X₁f
      BG₂ δ₁) :
    ‖eTermFun (GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁)))) Gk Gj Hm (compWeight L a₁) Fk E
      q.1 q.2.1 q.2.2‖ ≤ Bd := by
  have hcd := localB_coverData ht Y hN₁ hMM hag HBp
  exact eTermFun_bound_cover_of_one_le hb₁ hbC hS hcd.1 hcd.2.1 hcd.2.2.1 hMM ha₁ HBp HBk HBj
    hP hq colk colj hκ hM hnum dsX₀ hN hcd.2.2.2.1 hcd.2.2.2.2 hj hF hFk hEb hq'

/-- **The old-term functional at the triple of a datum of the literal local generator** (the value
identity `eTermFun_value_cover` with `localB_coverData`): at `s ≡ 1` the functional is the old term
at the composed datum `ψ(𝔹_j(X), 𝔹_k(X); ψ(𝔹_k(X), 𝔹_{k+1}(Y); Θ) + δψ(𝔹_k(X), H⁻; ψ'))`. -/
theorem localB_eTermFun_value {t : ℕ} (ht : t ≤ k + 1)
    (Y : Set (CTorus d L N₁ m₁ (k + 1))) (hN₁ : 5 < N₁) (hMM : 4 * L ^ 2 ≤ L ^ m₁)
    (hag : 2 * d * Real.log L ≤ agmonRate d / 16 * (minSep L (L ^ m₁) - 1)) {c BG : ℝ}
    (hS : Dec2.DecSpecs d L (Dec2.mixedKc d L) (Cchi d L) c BG) (ha₁ : 0 < a₁)
    (HBp : BgHyp d L (k + 1) (minSep L (L ^ m₁)) (compWeight L a₁) ν)
    (HBk : BgHyp d L (k + 1) ϱ₁ (compWeight L a₁) ν)
    (HBj : BgHyp d L (k + 1) ϱ₂ (compWeight L a₁) ν)
    (hP : Precedes Gk (GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁))))) (hq : Precedes Gj Gk)
    (colk : ∀ z ∈ collar Gk, z ∈ (GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁)))).Ω 1)
    (colj : ∀ z ∈ collar Gj, z ∈ Gk.Ω 1)
    {κ eps δ₃ : ℝ} (hκ : 0 < κ) (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hnum : ChainNum d L N m₁ BG κ (4 * d * (L : ℝ) ^ 3 + L) eps δ₃)
    {X₀ X₁f : Finset (CTorus d L N₁ m₁ (k + 1))} (dsX₀ : ∀ x ∈ dataSites Gk, x ∈ X₀)
    (hN : ∀ x ∈ X₀, x ∈ (GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁)))).Ω 1 →
      ∀ y : CTorus d L N₁ m₁ (k + 1), Green.torusDist d ((N₁ * L ^ m₁) * L ^ (k + 1)) x y <
        (4 * d * (L : ℝ) ^ 3 + L) * (L : ℝ) ^ m₁ *
          (GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁)))).spacing x → y ∈ X₁f)
    {j : ℕ} (hj : j ≤ k + 1) {Kf Cf c₂ BG₂ δ₁ δfl : ℝ}
    (hF : FlSetting N (GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁)))) Gk Hm a₁ ν κ BG eps δ₃
      Kf Cf c₂ BG₂ δ₁ δfl X₁f)
    {Fk : RawData d L (N₁ * L ^ m₁) (k + 1) N → (Gk.Ω 1 × Fin N → ℂ) × (Gk.Ω 1 → ℂ)}
    (hFk : ∀ D : BgData Gk N, InUnionDomainC Gk (bgC0 d L N) (bgC1 d L N) ν D →
      Fk (rawOf D) = (bgFieldC Gk (compWeight L a₁) ν (bgC0 d L N) D,
        bgMultC Gk (compWeight L a₁) ν (bgC0 d L N) D))
    (E : RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ)
    {D : BgData (GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁)))) N}
    (hD : XiCData (GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁) ν (k + 1) 1
      eps D)
    {ψ' : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ} (hψ : ψ' ∈ FlBallLC Hm δ₁) :
    eTermFun (GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁)))) Gk Gj Hm (compWeight L a₁) Fk E
        (bgFieldC (GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁) ν
            (bgC0 d L N) D,
          bgMultC (GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁) ν
            (bgC0 d L N) D)
        (flFieldOne (GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁)))) Hm BG₂ κ a₁ ν D ψ')
        (rawOf D, ψ') =
      E (rawOf (composeData hq (compWeight L a₁)
        (bgFieldC Gk (compWeight L a₁) ν (bgC0 d L N)
          (flDatumOne Hm BG₂ κ hP hF.hPm a₁ ν D ψ' hψ.2))
        (flDatumOne Hm BG₂ κ hP hF.hPm a₁ ν D ψ' hψ.2))) := by
  have hcd := localB_coverData ht Y hN₁ hMM hag HBp
  exact eTermFun_value_cover hS hcd.1 hcd.2.1 hcd.2.2.1 hMM ha₁ HBp HBk HBj
    hP hq colk colj hκ hM hnum dsX₀ hN hcd.2.2.2.1 hcd.2.2.2.2 hj hF hFk E hD hψ

end LocalPairE

section LocalPairSetting

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ₁ : ℝ} {a₁' ν' : ℝ}

/-- **The core of `localB_pair_flSetting`**: the same conclusion from the typing and numerical data
(`3 ≤ d`, `3 ≤ L`, `2 ≤ m₁`, `0 ≤ ν`, `ν (L^K)² ≤ 1`, admissible weights) that the proof uses of
`BgHyp`; the radius condition `bgR0 ≤ minSep` of `BgHyp` is not needed. -/
theorem localB_pair_flSetting_core {k : ℕ} (hk : k + 1 ≤ K) (Y : Set (CTorus d L N₁ m₁ K))
    (hN₁ : 5 < N₁) (hm₁ : 2 ≤ m₁) (hMM : 4 * L ^ 2 ≤ L ^ m₁) (hd : 3 ≤ d) (hL : 3 ≤ L)
    (hν : 0 ≤ ν') (hνL : ν' * ((L : ℝ) ^ K) ^ 2 ≤ 1)
    (ha : IsAdmissibleWeights K (compWeight L a₁'))
    (hag : 2 * d * Real.log L ≤ agmonRate d / 16 * (minSep L (L ^ m₁) - 1))
    {Gk : GeneratingSet d L (N₁ * L ^ m₁) K ϱ₁}
    (hP : Precedes Gk (GsSpec.localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))))
    (htop : Gk.Ω (k + 1) = ∅) {κ BG eps δ₃ c₂ BG₂ δ₁ δfl : ℝ}
    {X₁f : Finset (CTorus d L N₁ m₁ K)}
    (hS2 : Dec2.DecSpecs d L (Dec2.mixedKc d L) (Cchi d L) c₂ BG₂)
    (hM2 : c₂ * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (depm : ∀ x ∈ dataSites Gk, ∀ y ∈ composeDep Gk (GsSpec.localB k (by omega)
        (↑((GsSpec.localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω k) :
          Set (CTorus d L N₁ m₁ K)) (le_refl (minSep L (L ^ m₁)))) x, y ∈ X₁f)
    (num : FlNum d L N BG BG₂ κ eps δ₃ δ₁ δfl) :
    FlSetting N (GsSpec.localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))) Gk
      (GsSpec.localB k (by omega)
        (↑((GsSpec.localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω k) :
          Set (CTorus d L N₁ m₁ K)) (le_refl (minSep L (L ^ m₁))))
      a₁' ν' κ BG eps δ₃ (Dec2.mixedKc d L) (Cchi d L) c₂ BG₂ δ₁ δfl X₁f := by
  obtain ⟨hPmp, -, SM, -⟩ := localB_drop_pair hk Y hN₁ hm₁ hMM hd hL hν hνL ha hag
  exact ⟨hS2, SM, hM2, GsSpec.precedes_localB_drop hk (by omega) Y le_rfl le_rfl hP htop, hPmp,
    depm, num⟩

/-- **The fluctuation setting at the local pair** `(𝔹_{k+1}(Y), 𝔹_k(Y))`,
`𝔹_{k+1}(Y) = localB (k + 1) … Y`, `𝔹_k(Y) = localB k … Ω_k(𝔹_{k+1}(Y))` (the top layer dropped):
for a generating set `𝔹_k(X) ≺ 𝔹_{k+1}(Y)` without layer `k + 1`, `FlSetting` holds with the
constants `mixedKc d L`, `Cchi d L` of the cover of `𝔹_{k+1}(Y)` as soon as the Green's function
constants of the pair (`hS2`, `hM2`), the dependency of the composition on `X₁` (`depm`) and the
numerical conditions `FlNum` hold (`localB_drop_pair`, `GsSpec.precedes_localB_drop`). -/
theorem localB_pair_flSetting {k : ℕ} (hk : k + 1 ≤ K) (Y : Set (CTorus d L N₁ m₁ K))
    (hN₁ : 5 < N₁) (hMM : 4 * L ^ 2 ≤ L ^ m₁)
    (hag : 2 * d * Real.log L ≤ agmonRate d / 16 * (minSep L (L ^ m₁) - 1)) {a₁ ν : ℝ}
    (HBp : BgHyp d L K (minSep L (L ^ m₁)) (compWeight L a₁) ν)
    {Gk : GeneratingSet d L (N₁ * L ^ m₁) K ϱ₁}
    (hP : Precedes Gk (GsSpec.localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))))
    (htop : Gk.Ω (k + 1) = ∅) {κ BG eps δ₃ c₂ BG₂ δ₁ δfl : ℝ}
    {X₁f : Finset (CTorus d L N₁ m₁ K)}
    (hS2 : Dec2.DecSpecs d L (Dec2.mixedKc d L) (Cchi d L) c₂ BG₂)
    (hM2 : c₂ * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (depm : ∀ x ∈ dataSites Gk, ∀ y ∈ composeDep Gk (GsSpec.localB k (by omega)
        (↑((GsSpec.localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω k) :
          Set (CTorus d L N₁ m₁ K)) (le_refl (minSep L (L ^ m₁)))) x, y ∈ X₁f)
    (num : FlNum d L N BG BG₂ κ eps δ₃ δ₁ δfl) :
    FlSetting N (GsSpec.localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))) Gk
      (GsSpec.localB k (by omega)
        (↑((GsSpec.localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω k) :
          Set (CTorus d L N₁ m₁ K)) (le_refl (minSep L (L ^ m₁))))
      a₁ ν κ BG eps δ₃ (Dec2.mixedKc d L) (Cchi d L) c₂ BG₂ δ₁ δfl X₁f := by
  have hL : 3 ≤ L := HBp.hL
  have hm₁ : 2 ≤ m₁ := by
    by_contra h
    push Not at h
    have hL2 : L ^ m₁ ≤ L ^ 1 := Nat.pow_le_pow_right (by omega) (by omega)
    nlinarith
  have hm₁ : 2 ≤ m₁ := by
    by_contra h
    push Not at h
    have hL2 : L ^ m₁ ≤ L ^ 1 := Nat.pow_le_pow_right (by omega) (by omega)
    nlinarith
  exact localB_pair_flSetting_core hk Y hN₁ hm₁ hMM HBp.hd hL HBp.mass HBp.massLe HBp.weights hag
    hP htop hS2 hM2 depm num

end LocalPairSetting

end Balaban.Localization
