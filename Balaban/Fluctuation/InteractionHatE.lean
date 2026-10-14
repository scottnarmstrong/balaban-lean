/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.InteractionHatLC
public import Balaban.Fluctuation.InteractionHatF
public import Balaban.Fluctuation.InteractionETerm
public import Balaban.Fluctuation.Prop33Parts
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The `δ𝓔'`-part of the localized interaction in the variable `ψ̂`

An old term `E` of the effective action, composed with the fluctuation datum, is a functional of
the decoupled objects: with `(φ, α) = F₁(s, Θ)` and `δφ = Sol(s, …)`,

`E(D2raw (D1rawFl F₁ Sol s (Θ, ψ')))`, `D1rawFl = (composeField φ Ψ + composeField δφ ψ', h)`,

so it is `Φ_E(φ, δφ, (Θ, ψ'))` with `Φ_E` analytic on the realizable triples with layer-constant
fluctuation (`eTermFun_analytic`).  `i5_functional_hatLC` expands it with terms local in `ψ̂`
(`eterm_locInt_hat`).
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Analysis
  Balaban.Fluctuation Finset Matrix Set Metric

section EHat

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱ₁ ϱ₂ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Gk : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁}
variable {Gj : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₂}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ r₀ eps δ₃ : ℝ} {X₀ X₁f : Finset (CTorus d L N₁ m₁ (k + 1))} {j : ℕ}
variable {Kc Cx c₂ BG₂ δ₁ δfl : ℝ} {m₀ : ℕ} {X 𝒦X : Set (CTorus d L N₁ m₁ (k + 1))}

variable (Gp Gk Hm) in
/-- The raw datum of `𝔹_k(X)` composed from the triple `(φ, δφ, (Θ, ψ'))`:
`ψ(𝔹_k(X), 𝔹_{k+1}; Θ) + δψ(𝔹_k(X), 𝔹_k; ψ')` (`D1rawFl` with the objects of the triple). -/
noncomputable def d1Triple (a : ℕ → ℝ) (φ : Gp.Ω 1 × Fin N → ℂ) (δφ : Hm.Ω 1 × Fin N → ℂ)
    (u : RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)) :
    RawData d L (N₁ * L ^ m₁) (k + 1) N :=
  (fun x i => composeField Gk Gp a φ u.1.1 x i + composeField Gk Hm a δφ u.2 x i,
    fun x i => by classical exact if x ∈ Gk.Ω 1 then u.1.2 x i else 0)

variable (Gp Gk Gj Hm) in
/-- **An old term as a functional of the decoupled objects**:
`Φ_E(φ, δφ, (Θ, ψ')) = E(D2raw Fk (d1Triple φ δφ (Θ, ψ')))`. -/
noncomputable def eTermFun (a : ℕ → ℝ)
    (Fk : RawData d L (N₁ * L ^ m₁) (k + 1) N → (Gk.Ω 1 × Fin N → ℂ) × (Gk.Ω 1 → ℂ))
    (E : RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ) :
    ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) → (Hm.Ω 1 × Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ :=
  fun pa δφ u => E (D2raw Gk Gj a Fk (d1Triple Gp Gk Hm a pa.1 δφ u))

theorem d1Triple_D1rawFl (a : ℕ → ℝ)
    (F₁ : DecParams Gp × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ))
    (Sol : Dec2.DecParams (coverOf Gp) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ))
    (s : Dec2.DecParams (coverOf Gp))
    (u : RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)) :
    D1rawFl Gp Gk Hm a F₁ Sol s u =
      d1Triple Gp Gk Hm a (F₁ (s, u.1)).1 (Sol (s, flEdat Gp Hm (F₁ (s, u.1)) u.1.1 u.2)).1 u :=
  rfl

end EHat

section Chain

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱ₁ ϱ₂ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Gk : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁}
variable {Gj : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₂}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ r₀ eps δ₃ : ℝ} {X₀ X₁f : Finset (CTorus d L N₁ m₁ (k + 1))} {j : ℕ}
variable {Kc Cx c₂ BG₂ δ₁ δfl : ℝ} {m₀ : ℕ} {X 𝒦X : Set (CTorus d L N₁ m₁ (k + 1))}

/-- **The triple of a datum at `s ≡ 1` is realizable, at a given background field** (the common
step of `triple_one_mem`, one generating set with `DGSetting`, and of its cover form
`triple_one_mem_cover`): if `(φ_{k+1}, α_{k+1}) = (bgFieldC D, bgMultC D)` is the decoupled
background field at `s ≡ 1` with the bounds of Theorem I-4b, then for a layer-constant fluctuation
`ψ'` in the ball `((φ_{k+1}, α_{k+1}), flFieldOne D ψ', (Θ, ψ')) ∈ FlRealLC`.  The hypotheses on the
pair `(coverOf 𝔹_{k+1}, H⁻)` are those of Theorem I-4a (mode P). -/
theorem triple_one_mem_of_bg (hκ : 0 < κ) (hBG : 0 ≤ BG)
    (HBp : BgHyp d L (k + 1) ϱ (compWeight L a₁) ν) (heps : 0 < eps)
    (hsmall : (4 * d + 6) * ((2 * d + 1) * eps) ≤ 1)
    (hphi : (3 + K4 d L N BG κ) * (xiC1 d * eps) < 1 / 2) (hδ₁ : 0 < δ₁)
    (hδ₁le : δ₁ ≤ deltaStar' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hBle : 2 * (K4 d L N BG κ * (xiC1 d * eps)) ≤
      deltaStar' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hS2 : Dec2.DecSpecs d L Kc Cx c₂ BG₂)
    (SM : Dec2.FootLocal (coverOf Gp) Hm (compWeight L a₁) ν Kc Cx)
    (hM2 : c₂ * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) (hPmp : Precedes Hm Gp)
    {D : BgData Gp N} (hD : XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D)
    (hI1 : IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) (fun _ => 1) D
      (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D)
      (bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D))
    (hbb1 : BgBounds Gp D (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D)
      (bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D) (K4 d L N BG κ * (xiC1 d * eps)))
    {ψ' : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ} (hψ : ψ' ∈ FlBallLC Hm δ₁) :
    ((bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D,
        bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D),
      flFieldOne Gp Hm BG₂ κ a₁ ν D ψ', (rawOf D, ψ')) ∈
      FlRealLC Gp Hm a₁ ν BG κ eps X₁f BG₂ δ₁ := by
  classical
  have hd0 : 0 < d := by have := HBp.hd; omega
  have hc1 := one_le_xiC1 d
  have hδ0 : 0 < xiC1 d * eps := by positivity
  have hB0 : 0 ≤ 2 * (K4 d L N BG κ * (xiC1 d * eps)) :=
    mul_nonneg (by norm_num) (mul_nonneg (K4_pos hBG hd0).le hδ0.le)
  obtain ⟨Sol, -, hSolprop⟩ := Dec2.i4a_analytic (N := N) hS2.fam hS2.an SM.toCoverBase hκ.le hM2
    false hB0 hδ₁.le hBle hδ₁le
  have hE1 : 1 < Real.exp κ := Real.one_lt_exp_iff.2 hκ
  have hsx : ∀ P : ↥(cubeIdx Gp), ‖(fun _ : ↥(cubeIdx Gp) => (1 : ℂ)) P‖ < Real.exp κ :=
    fun P => by simpa using hE1
  have hs1 : ∀ (P : ℕ × CTorus d L N₁ m₁ (k + 1)) (hP : P ∈ cubeIdx Gp), P ∉ parCubes Gp X₁f →
      (fun _ : ↥(cubeIdx Gp) => (1 : ℂ)) ⟨P, hP⟩ = 1 := fun P hP hPn => rfl
  obtain ⟨hstrict, hmem⟩ := point_facts_core_of_bg (X₁f := X₁f) hBG HBp heps hsmall hphi hδ₁ hPmp
    hSolprop hsx hs1 hD hI1 hbb1 hψ.1
  obtain ⟨hfld, hfix, hs6, -, -, huniq⟩ := hSolprop ((fun _ : ↥(cubeIdx Gp) => (1 : ℂ)),
    flEdat Gp Hm (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D,
      bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D) D.Ψ ψ') hsx hstrict
  have hmult := flMult_spec (C := coverOf Gp) (Hm := Hm) (a := compWeight L a₁) (ν := ν)
    (ρ := c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) (s := fun _ : ↥(cubeIdx Gp) => (1 : ℂ))
    (e := flEdat Gp Hm (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D,
      bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D) D.Ψ ψ') ⟨hs6, hfix⟩
    (fun δα' h => huniq δα' h.1 h.2)
  have hfl : flFieldOne Gp Hm BG₂ κ a₁ ν D ψ' = (Sol ((fun _ : ↥(cubeIdx Gp) => (1 : ℂ)),
      flEdat Gp Hm (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D,
        bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D) D.Ψ ψ')).1 := by
    unfold flFieldOne flField
    exact (congrArg (dphi Hm (Dec2.decG (coverOf Gp) Hm (compWeight L a₁) ν
      (fun _ : ↥(cubeIdx Gp) => (1 : ℂ))) _ _ _) hmult).trans hfld.symm
  rw [hfl]
  exact ⟨hmem, hψ.2⟩

/-- **The triple of a datum at `s ≡ 1` is realizable**: for `D ∈ Ξ^c` and a layer-constant
fluctuation `ψ'` in the ball, `((bgFieldC D, bgMultC D), flFieldOne D ψ', (Θ, ψ')) ∈ FlRealLC`. -/
theorem triple_one_mem (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    {D : BgData Gp N} (hD : XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D)
    {ψ' : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ} (hψ : ψ' ∈ FlBallLC Hm δ₁) :
    ((bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D,
        bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D),
      flFieldOne Gp Hm BG₂ κ a₁ ν D ψ', (rawOf D, ψ')) ∈
      FlRealLC Gp Hm a₁ ν BG κ eps X₁f BG₂ δ₁ := by
  have hd0 : 0 < d := by have := hC.HBp.hd; omega
  have hc1 := one_le_xiC1 d
  have hε := hC.eps_pos
  have hδ0 : 0 < xiC1 d * eps := by positivity
  have hE1 : 1 < Real.exp κ := Real.one_lt_exp_iff.2 hC.hκ
  have hsx : ∀ P : ↥(cubeIdx Gp), ‖(fun _ : ↥(cubeIdx Gp) => (1 : ℂ)) P‖ < Real.exp κ :=
    fun P => by simpa using hE1
  have hδ1 : xiC1 d * eps ≤ c7 d L N BG κ := hC.c7le
  have hδ0' : xiC1 d * eps ≤ bgC0 d L N := hδ1.trans ((c7_le_bgC1 d L N BG κ).trans
    (bgC1_le_bgC0 d L N hd0))
  have hνε : ν * ((L : ℝ) ^ (k + 1)) ^ 2 * (xiC1 d * eps) ^ 2 ≤ (xiC1 d * eps) ^ 2 := by
    have := hC.HBp.massLe; nlinarith [sq_nonneg (xiC1 d * eps)]
  have hDom := xiCData_inDomainC hC.HBp hC.small1 hD
  obtain ⟨φ, α, hI, -, hbb⟩ := flCore_bgBounds hC hsx hD
  obtain ⟨-, hφ1, hα1⟩ := i4b_one hC.hS hC.Sp hC.HBp hC.hκ.le hC.hM hδ0 le_rfl hδ0' hδ1
    hνε hDom hI
  subst hφ1 hα1
  exact triple_one_mem_of_bg hC.hκ hC.hS.fam.2.1 hC.HBp hC.eps_pos hC.small1 hC.phi_lt hC.δ₁_pos
    hC.δ₁_le hC.B_le hC.hS2 hC.SM hC.hM2 hC.hPmp hD hI hbb hψ

end Chain

section ChainE

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱ₁ ϱ₂ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Gk : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁}
variable {Gj : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₂}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ r₀ eps δ₃ : ℝ} {X₀ X₁f : Finset (CTorus d L N₁ m₁ (k + 1))} {j : ℕ}
variable {Kc Cx c₂ BG₂ δ₁ δfl : ℝ} {m₀ : ℕ} {X 𝒦X : Set (CTorus d L N₁ m₁ (k + 1))}

/-- **The background stage of the point facts of Lemma DL, from `BgSetting`** (Theorem I-4b and
stage 1 at a realizable background field): the bounds `BgBounds` and the composed datum
`ψ(𝔹_k(X), 𝔹_{k+1}; Θ, s) ∈ Ξ^c_K(𝔹_k(X); 1, b² ε' + K₂' δ₃)`.  The cover form is
`bgStage_cover_of_one_le`. -/
theorem bgStage_of_one_le {b : ℝ} (hb₁ : 1 ≤ b) (hbC : b ≤ scaledC0 d)
    (hB : BgSetting N Gp Gk Gj a₁ ν c BG κ r₀ eps δ₃ X₀ X₁f j)
    {s : DecParams Gp} (hs : ∀ P, ‖s P‖ < Real.exp κ)
    (hs1 : ∀ (P : ℕ × CTorus d L N₁ m₁ (k + 1)) (hP : P ∈ cubeIdx Gp), P ∉ parCubes Gp X₁f →
      s ⟨P, hP⟩ = 1)
    {D : BgData Gp N} (hD : XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D)
    {φ : Gp.Ω 1 × Fin N → ℂ} {α : Gp.Ω 1 → ℂ}
    (hI : IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α) :
    BgBounds Gp D φ α (K4 d L N BG κ * (xiC1 d * eps)) ∧
      XiCData Gk (compWeight L a₁) ν (k + 1) 1 (b ^ 2 * eps + xiK2 d L N * δ₃)
        (composeData hB.hP (compWeight L a₁) φ D) := by
  obtain ⟨hδ0, hδ0', hδ1, hνε, hDom, -⟩ := hB.num.domain hB.HBp hD
  have hsle : ∀ P, ‖s P‖ ≤ Real.exp κ := fun P => (hs P).le
  have hone : ∀ P : ↥(cubeIdx Gp), ‖(fun _ : ↥(cubeIdx Gp) => (1 : ℂ)) P‖ ≤ Real.exp κ :=
    fun P => by simpa using Real.one_le_exp hB.hκ.le
  obtain ⟨φ', α', -, hu', -, -, hbb⟩ := i4b_exists_unique hB.hS hB.Sp hB.HBp hB.hκ.le hB.hM
    hsle hδ0 le_rfl hδ0' hδ1 hνε hDom
  obtain ⟨rfl, rfl⟩ := hu' φ α hI
  obtain ⟨φ1, α1, hI1, -⟩ := i4b_exists_unique hB.hS hB.Sp hB.HBp hB.hκ.le hB.hM hone hδ0
    le_rfl hδ0' hδ1 hνε hDom
  exact ⟨hbb, i5_stage1_of_one_le hb₁ hbC hB.hS hB.Sp hB.ha₁ hB.HBp hB.HBk hB.hP hB.colk
    hB.hκ.le hB.hM hB.num hB.dsX₀ hB.hN hB.hr hB.hr₀ hsle hs1 hD hI hI1⟩

/-- **The facts at a realizable triple, at given background stages** (the common step of
`eTerm_chain_of_one_le`, one generating set with `BgSetting`, and of its cover form
`eTerm_chain_cover_of_one_le`): `hbg` is the background stage of the point facts (Theorem I-4b
bounds and stage 1) at every realizable background field. -/
theorem eTerm_chain_of_bg {b : ℝ} (hb₁ : 1 ≤ b) (hbC : b ≤ scaledC0 d) (hBG : 0 ≤ BG)
    (ha₁ : 0 < a₁) (HBp : BgHyp d L (k + 1) ϱ (compWeight L a₁) ν)
    (HBk : BgHyp d L (k + 1) ϱ₁ (compWeight L a₁) ν) (HBj : BgHyp d L (k + 1) ϱ₂ (compWeight L a₁) ν)
    (hP : Precedes Gk Gp) (hq : Precedes Gj Gk) (colj : ∀ z ∈ collar Gj, z ∈ Gk.Ω 1)
    (hnum : ChainNum d L N m₁ BG κ r₀ eps δ₃) (hj : j ≤ k + 1) (hκ : 0 < κ)
    (hF : FlSetting N Gp Gk Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl X₁f)
    {Fk : RawData d L (N₁ * L ^ m₁) (k + 1) N → (Gk.Ω 1 × Fin N → ℂ) × (Gk.Ω 1 → ℂ)}
    (hFk : ∀ D : BgData Gk N, InUnionDomainC Gk (bgC0 d L N) (bgC1 d L N) ν D →
      Fk (rawOf D) = (bgFieldC Gk (compWeight L a₁) ν (bgC0 d L N) D,
        bgMultC Gk (compWeight L a₁) ν (bgC0 d L N) D))
    (hbg : ∀ s : DecParams Gp, (∀ P, ‖s P‖ < Real.exp κ) →
      (∀ (P : ℕ × CTorus d L N₁ m₁ (k + 1)) (hP : P ∈ cubeIdx Gp), P ∉ parCubes Gp X₁f →
        s ⟨P, hP⟩ = 1) →
      ∀ D : BgData Gp N, XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D →
      ∀ (φ : Gp.Ω 1 × Fin N → ℂ) (α : Gp.Ω 1 → ℂ),
        IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        BgBounds Gp D φ α (K4 d L N BG κ * (xiC1 d * eps)) ∧
        XiCData Gk (compWeight L a₁) ν (k + 1) 1 (b ^ 2 * eps + xiK2 d L N * δ₃)
          (composeData hP (compWeight L a₁) φ D))
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
          (flDatum Gk hP hF.hPm (compWeight L a₁) t.1.1 t.2.1 D ψ' hlc)) := by
  classical
  obtain ⟨⟨φ, α⟩, δφt, ut⟩ := t
  obtain ⟨⟨s, D, ψ', δα, hs, hs1, hD, hψ, hI, ht22, hδ, hfix, hsm1, hsm2, hsup⟩, hlc⟩ := ht
  dsimp only at hI ht22 hδ hfix hlc ⊢
  have hlc' : IsLayerConstant Hm ψ' := by rw [ht22] at hlc; exact hlc
  have hd0 : 0 < d := by have := HBp.hd; omega
  have hc1 := one_le_xiC1 d
  have hε := hnum.eps_pos
  have hδ0 : 0 < xiC1 d * eps := by positivity
  have hB0 : 0 ≤ 2 * (K4 d L N BG κ * (xiC1 d * eps)) :=
    mul_nonneg (by norm_num) (mul_nonneg (K4_pos hBG hd0).le hδ0.le)
  obtain ⟨Sol, -, hSolprop⟩ := Dec2.i4a_analytic (N := N) hF.hS2.fam hF.hS2.an
    hF.SM.toCoverBase hκ.le hF.hM2 false hB0 hF.num.δ₁_pos.le hF.num.B_le hF.num.δ₁_le
  obtain ⟨hbb, hst⟩ := hbg s hs hs1 D hD φ α hI
  obtain ⟨δφ, hstrict, hδφ, hX3, hrawD, hD2, hX2⟩ :=
    point_facts_fl_of_bg (F₁ := fun _ => (φ, α)) hb₁ hbC hBG ha₁ HBp HBk HBj hP hq colj hnum hj
      hF hFk hSolprop hs hD rfl hbb hst hψ hlc'
  have hδt : δφt = δφ := by
    obtain ⟨hfld, -, -, -, -, huniq⟩ := hSolprop (s, flEdat Gp Hm (φ, α) D.Ψ ψ') hs hstrict
    have hδα : δα = (Sol (s, flEdat Gp Hm (φ, α) D.Ψ ψ')).2 := huniq δα hsm1 hfix
    rw [hδ, hδα, ← hfld]
    exact hδφ
  subst hδt
  refine ⟨D, ψ', hlc', ht22, hX3, ?_, hD2, hX2⟩
  rw [ht22, ← hrawD]
  change _ = d1Triple Gp Gk Hm (compWeight L a₁) φ
    (Sol (s, flEdat Gp Hm (φ, α) D.Ψ ψ')).1 (rawOf D, ψ')
  rw [hδφ]

/-- **The facts at a realizable triple with layer-constant fluctuation**: the composed datum of
`𝔹_k(X)` is the datum `flDatum`, in `Ξ^c`, its background composition lies in `Ξ^c(𝔹_j(X))`,
with a composition constant `1 ≤ b ≤ C₀` (at `b = 1` the radius is `ε + K₂ δ₃ + K₂ δ_fl`; the landed
`eTerm_chain` is the instance `b = C₀`). -/
theorem eTerm_chain_of_one_le {b : ℝ} (hb₁ : 1 ≤ b) (hbC : b ≤ scaledC0 d)
    (hB : BgSetting N Gp Gk Gj a₁ ν c BG κ r₀ eps δ₃ X₀ X₁f j)
    (hF : FlSetting N Gp Gk Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl X₁f)
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
        (flDatum Gk hB.hP hF.hPm (compWeight L a₁) t.1.1 t.2.1 D ψ' hlc) ∧
      d1Triple Gp Gk Hm (compWeight L a₁) t.1.1 t.2.1 t.2.2 =
        rawOf (flDatum Gk hB.hP hF.hPm (compWeight L a₁) t.1.1 t.2.1 D ψ' hlc) ∧
      D2raw Gk Gj (compWeight L a₁) Fk
          (rawOf (flDatum Gk hB.hP hF.hPm (compWeight L a₁) t.1.1 t.2.1 D ψ' hlc)) =
        rawOf (composeData hB.hq (compWeight L a₁)
          (bgFieldC Gk (compWeight L a₁) ν (bgC0 d L N)
            (flDatum Gk hB.hP hF.hPm (compWeight L a₁) t.1.1 t.2.1 D ψ' hlc))
          (flDatum Gk hB.hP hF.hPm (compWeight L a₁) t.1.1 t.2.1 D ψ' hlc)) ∧
      XiCData Gj (compWeight L a₁) ν j b
        (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)
        (composeData hB.hq (compWeight L a₁)
          (bgFieldC Gk (compWeight L a₁) ν (bgC0 d L N)
            (flDatum Gk hB.hP hF.hPm (compWeight L a₁) t.1.1 t.2.1 D ψ' hlc))
          (flDatum Gk hB.hP hF.hPm (compWeight L a₁) t.1.1 t.2.1 D ψ' hlc)) :=
  eTerm_chain_of_bg hb₁ hbC hB.hS.fam.2.1 hB.ha₁ hB.HBp hB.HBk hB.HBj hB.hP hB.hq hB.colj hB.num
    hB.hj hB.hκ hF hFk (fun _ hs hs1 _ hD _ _ hI => bgStage_of_one_le hb₁ hbC hB hs hs1 hD hI) ht

/-- **The facts at a realizable triple with layer-constant fluctuation**: the composed datum of
`𝔹_k(X)` is the datum `flDatum`, in `Ξ^c`, its background composition lies in `Ξ^c(𝔹_j(X))`. -/
theorem eTerm_chain (hB : BgSetting N Gp Gk Gj a₁ ν c BG κ r₀ eps δ₃ X₀ X₁f j)
    (hF : FlSetting N Gp Gk Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl X₁f)
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
        (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)
        (flDatum Gk hB.hP hF.hPm (compWeight L a₁) t.1.1 t.2.1 D ψ' hlc) ∧
      d1Triple Gp Gk Hm (compWeight L a₁) t.1.1 t.2.1 t.2.2 =
        rawOf (flDatum Gk hB.hP hF.hPm (compWeight L a₁) t.1.1 t.2.1 D ψ' hlc) ∧
      D2raw Gk Gj (compWeight L a₁) Fk
          (rawOf (flDatum Gk hB.hP hF.hPm (compWeight L a₁) t.1.1 t.2.1 D ψ' hlc)) =
        rawOf (composeData hB.hq (compWeight L a₁)
          (bgFieldC Gk (compWeight L a₁) ν (bgC0 d L N)
            (flDatum Gk hB.hP hF.hPm (compWeight L a₁) t.1.1 t.2.1 D ψ' hlc))
          (flDatum Gk hB.hP hF.hPm (compWeight L a₁) t.1.1 t.2.1 D ψ' hlc)) ∧
      XiCData Gj (compWeight L a₁) ν j (scaledC0 d)
        (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)
        (composeData hB.hq (compWeight L a₁)
          (bgFieldC Gk (compWeight L a₁) ν (bgC0 d L N)
            (flDatum Gk hB.hP hF.hPm (compWeight L a₁) t.1.1 t.2.1 D ψ' hlc))
          (flDatum Gk hB.hP hF.hPm (compWeight L a₁) t.1.1 t.2.1 D ψ' hlc)) :=
  eTerm_chain_of_one_le (one_le_scaledC0 d) le_rfl hB hF hFk ht

end ChainE

section Props

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱ₁ ϱ₂ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Gk : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁}
variable {Gj : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₂}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ r₀ eps δ₃ : ℝ} {X₀ X₁f : Finset (CTorus d L N₁ m₁ (k + 1))} {j : ℕ}
variable {Kc Cx c₂ BG₂ δ₁ δfl : ℝ} {m₀ : ℕ} {X 𝒦X : Set (CTorus d L N₁ m₁ (k + 1))}

/-- **Analyticity of the old-term functional on the realizable triples, at given background
stages** (the common step of `eTermFun_analytic_of_one_le` and of its cover form
`eTermFun_analytic_cover_of_one_le`). -/
theorem eTermFun_analytic_of_bg {b : ℝ} (hb₁ : 1 ≤ b) (hbC : b ≤ scaledC0 d) (hBG : 0 ≤ BG)
    (ha₁ : 0 < a₁) (HBp : BgHyp d L (k + 1) ϱ (compWeight L a₁) ν)
    (HBk : BgHyp d L (k + 1) ϱ₁ (compWeight L a₁) ν) (HBj : BgHyp d L (k + 1) ϱ₂ (compWeight L a₁) ν)
    (hP : Precedes Gk Gp) (hq : Precedes Gj Gk) (colj : ∀ z ∈ collar Gj, z ∈ Gk.Ω 1)
    (hnum : ChainNum d L N m₁ BG κ r₀ eps δ₃) (hj : j ≤ k + 1) (hκ : 0 < κ)
    (hF : FlSetting N Gp Gk Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl X₁f)
    {Fk : RawData d L (N₁ * L ^ m₁) (k + 1) N → (Gk.Ω 1 × Fin N → ℂ) × (Gk.Ω 1 → ℂ)}
    (hFkan : AnalyticOnNhd ℂ Fk {p | ∃ D : BgData Gk N,
      InUnionDomainC Gk (bgC0 d L N) (bgC1 d L N) ν D ∧ p = (D.Ψ, D.h)})
    (hFk : ∀ D : BgData Gk N, InUnionDomainC Gk (bgC0 d L N) (bgC1 d L N) ν D →
      Fk (rawOf D) = (bgFieldC Gk (compWeight L a₁) ν (bgC0 d L N) D,
        bgMultC Gk (compWeight L a₁) ν (bgC0 d L N) D))
    (hbg : ∀ s : DecParams Gp, (∀ P, ‖s P‖ < Real.exp κ) →
      (∀ (P : ℕ × CTorus d L N₁ m₁ (k + 1)) (hP : P ∈ cubeIdx Gp), P ∉ parCubes Gp X₁f →
        s ⟨P, hP⟩ = 1) →
      ∀ D : BgData Gp N, XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D →
      ∀ (φ : Gp.Ω 1 × Fin N → ℂ) (α : Gp.Ω 1 → ℂ),
        IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        BgBounds Gp D φ α (K4 d L N BG κ * (xiC1 d * eps)) ∧
        XiCData Gk (compWeight L a₁) ν (k + 1) 1 (b ^ 2 * eps + xiK2 d L N * δ₃)
          (composeData hP (compWeight L a₁) φ D))
    {E : RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ}
    (hE : AnalyticOnNhd ℂ E (XiCRaw Gj (compWeight L a₁) ν j b
      (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl))) :
    AnalyticOnNhd ℂ (fun t : ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) × (Hm.Ω 1 × Fin N → ℂ) ×
        (RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)) =>
      eTermFun Gp Gk Gj Hm (compWeight L a₁) Fk E t.1 t.2.1 t.2.2)
      (FlRealLC Gp Hm a₁ ν BG κ eps X₁f BG₂ δ₁) := by
  classical
  intro t ht
  obtain ⟨D, ψ', hlc, ht22, hX3, hD1, hD2, hX2⟩ := eTerm_chain_of_bg hb₁ hbC hBG ha₁ HBp HBk HBj
    hP hq colj hnum hj hκ hF hFk hbg ht
  set g : (((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) × (Hm.Ω 1 × Fin N → ℂ) ×
      (RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ))) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N :=
    fun t' => d1Triple Gp Gk Hm (compWeight L a₁) t'.1.1 t'.2.1 t'.2.2 with hg
  have hφ : ∀ r, AnalyticAt ℂ (fun q : ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) ×
      (Hm.Ω 1 × Fin N → ℂ) × (RawData d L (N₁ * L ^ m₁) (k + 1) N ×
        (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)) => q.1.1 r) t := fun r =>
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Gp.Ω 1 × Fin N => ℂ) r).analyticAt _).comp
      (analyticAt_fst.comp analyticAt_fst)
  have hδ : ∀ r, AnalyticAt ℂ (fun q : ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) ×
      (Hm.Ω 1 × Fin N → ℂ) × (RawData d L (N₁ * L ^ m₁) (k + 1) N ×
        (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)) => q.2.1 r) t := fun r =>
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Hm.Ω 1 × Fin N => ℂ) r).analyticAt _).comp
      (analyticAt_fst.comp analyticAt_snd)
  have hΨ : ∀ y jj, AnalyticAt ℂ (fun q : ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) ×
      (Hm.Ω 1 × Fin N → ℂ) × (RawData d L (N₁ * L ^ m₁) (k + 1) N ×
        (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)) => q.2.2.1.1 y jj) t := fun y jj =>
    (analyticAt_rawΨ y jj t.2.2.1).comp_of_eq
      (analyticAt_fst.comp (analyticAt_snd.comp analyticAt_snd)) rfl
  have hψ : ∀ y jj, AnalyticAt ℂ (fun q : ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) ×
      (Hm.Ω 1 × Fin N → ℂ) × (RawData d L (N₁ * L ^ m₁) (k + 1) N ×
        (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)) => q.2.2.2 y jj) t := fun y jj =>
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N => ℂ) jj).analyticAt _).comp
      (((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : CTorus d L N₁ m₁ (k + 1) =>
        Fin N → ℂ) y).analyticAt _).comp (analyticAt_snd.comp (analyticAt_snd.comp analyticAt_snd)))
  have ha2 : AnalyticAt ℂ g t := by
    refine AnalyticAt.prod (analyticAt_pi_iff.2 fun x => analyticAt_pi_iff.2 fun i => ?_)
      (analyticAt_pi_iff.2 fun x => analyticAt_pi_iff.2 fun i => ?_)
    · exact (analyticAt_composeField (G := Gk) (G' := Gp) (q := t) (compWeight L a₁)
        (fun q => q.1.1) (fun q => q.2.2.1.1) hφ hΨ x i).add
        (analyticAt_composeField (G := Gk) (G' := Hm) (q := t) (compWeight L a₁)
        (fun q => q.2.1) (fun q => q.2.2.2) hδ hψ x i)
    · by_cases hx : x ∈ Gk.Ω 1
      · simp only [hx, ↓reduceIte]
        exact (analyticAt_rawh x i t.2.2.1).comp_of_eq
          (analyticAt_fst.comp (analyticAt_snd.comp analyticAt_snd)) rfl
      · simp only [hx, ↓reduceIte]
        exact analyticAt_const
  have hmem : g t ∈ {p | ∃ D : BgData Gk N,
      InUnionDomainC Gk (bgC0 d L N) (bgC1 d L N) ν D ∧ p = (D.Ψ, D.h)} :=
    ⟨_, xiCData_unionC hX3, hD1⟩
  have ha3 : AnalyticAt ℂ (fun q => Fk (g q)) t := (hFkan _ hmem).comp ha2
  have ha4 : AnalyticAt ℂ (fun q => D2raw Gk Gj (compWeight L a₁) Fk (g q)) t :=
    analyticAt_D2raw (Gj := Gj) (compWeight L a₁) Fk g ha2 ha3
  refine (hE _ ?_).comp ha4
  show D2raw Gk Gj (compWeight L a₁) Fk (d1Triple Gp Gk Hm (compWeight L a₁) t.1.1 t.2.1 t.2.2) ∈ _
  rw [hD1, hD2]
  exact ⟨_, hX2, rfl⟩

/-- **The bound of the old-term functional on the realizable triples, at given background
stages** (the common step of `eTermFun_bound_of_one_le` and of its cover form
`eTermFun_bound_cover_of_one_le`). -/
theorem eTermFun_bound_of_bg {b : ℝ} (hb₁ : 1 ≤ b) (hbC : b ≤ scaledC0 d) (hBG : 0 ≤ BG)
    (ha₁ : 0 < a₁) (HBp : BgHyp d L (k + 1) ϱ (compWeight L a₁) ν)
    (HBk : BgHyp d L (k + 1) ϱ₁ (compWeight L a₁) ν) (HBj : BgHyp d L (k + 1) ϱ₂ (compWeight L a₁) ν)
    (hP : Precedes Gk Gp) (hq : Precedes Gj Gk) (colj : ∀ z ∈ collar Gj, z ∈ Gk.Ω 1)
    (hnum : ChainNum d L N m₁ BG κ r₀ eps δ₃) (hj : j ≤ k + 1) (hκ : 0 < κ)
    (hF : FlSetting N Gp Gk Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl X₁f)
    {Fk : RawData d L (N₁ * L ^ m₁) (k + 1) N → (Gk.Ω 1 × Fin N → ℂ) × (Gk.Ω 1 → ℂ)}
    (hFk : ∀ D : BgData Gk N, InUnionDomainC Gk (bgC0 d L N) (bgC1 d L N) ν D →
      Fk (rawOf D) = (bgFieldC Gk (compWeight L a₁) ν (bgC0 d L N) D,
        bgMultC Gk (compWeight L a₁) ν (bgC0 d L N) D))
    (hbg : ∀ s : DecParams Gp, (∀ P, ‖s P‖ < Real.exp κ) →
      (∀ (P : ℕ × CTorus d L N₁ m₁ (k + 1)) (hP : P ∈ cubeIdx Gp), P ∉ parCubes Gp X₁f →
        s ⟨P, hP⟩ = 1) →
      ∀ D : BgData Gp N, XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D →
      ∀ (φ : Gp.Ω 1 × Fin N → ℂ) (α : Gp.Ω 1 → ℂ),
        IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        BgBounds Gp D φ α (K4 d L N BG κ * (xiC1 d * eps)) ∧
        XiCData Gk (compWeight L a₁) ν (k + 1) 1 (b ^ 2 * eps + xiK2 d L N * δ₃)
          (composeData hP (compWeight L a₁) φ D))
    {E : RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ} {B : ℝ}
    (hEb : ∀ r ∈ XiCRaw Gj (compWeight L a₁) ν j b
      (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl), ‖E r‖ ≤ B)
    {t : ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) × (Hm.Ω 1 × Fin N → ℂ) ×
      (RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ))}
    (ht : t ∈ FlRealLC Gp Hm a₁ ν BG κ eps X₁f BG₂ δ₁) :
    ‖eTermFun Gp Gk Gj Hm (compWeight L a₁) Fk E t.1 t.2.1 t.2.2‖ ≤ B := by
  obtain ⟨D, ψ', hlc, ht22, hX3, hD1, hD2, hX2⟩ := eTerm_chain_of_bg hb₁ hbC hBG ha₁ HBp HBk HBj
    hP hq colj hnum hj hκ hF hFk hbg ht
  show ‖E (D2raw Gk Gj (compWeight L a₁) Fk
    (d1Triple Gp Gk Hm (compWeight L a₁) t.1.1 t.2.1 t.2.2))‖ ≤ B
  rw [hD1, hD2]
  exact hEb _ ⟨_, hX2, rfl⟩

/-- **Analyticity of the old-term functional on the realizable triples.** -/
theorem eTermFun_analytic_of_one_le {b : ℝ} (hb₁ : 1 ≤ b) (hbC : b ≤ scaledC0 d)
    (hB : BgSetting N Gp Gk Gj a₁ ν c BG κ r₀ eps δ₃ X₀ X₁f j)
    (hF : FlSetting N Gp Gk Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl X₁f)
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
  eTermFun_analytic_of_bg hb₁ hbC hB.hS.fam.2.1 hB.ha₁ hB.HBp hB.HBk hB.HBj hB.hP hB.hq hB.colj
    hB.num hB.hj hB.hκ hF hFkan hFk
    (fun _ hs hs1 _ hD _ _ hI => bgStage_of_one_le hb₁ hbC hB hs hs1 hD hI) hE

/-- **Analyticity of the old-term functional on the realizable triples.** -/
theorem eTermFun_analytic (hB : BgSetting N Gp Gk Gj a₁ ν c BG κ r₀ eps δ₃ X₀ X₁f j)
    (hF : FlSetting N Gp Gk Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl X₁f)
    {Fk : RawData d L (N₁ * L ^ m₁) (k + 1) N → (Gk.Ω 1 × Fin N → ℂ) × (Gk.Ω 1 → ℂ)}
    (hFkan : AnalyticOnNhd ℂ Fk {p | ∃ D : BgData Gk N,
      InUnionDomainC Gk (bgC0 d L N) (bgC1 d L N) ν D ∧ p = (D.Ψ, D.h)})
    (hFk : ∀ D : BgData Gk N, InUnionDomainC Gk (bgC0 d L N) (bgC1 d L N) ν D →
      Fk (rawOf D) = (bgFieldC Gk (compWeight L a₁) ν (bgC0 d L N) D,
        bgMultC Gk (compWeight L a₁) ν (bgC0 d L N) D))
    {E : RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ}
    (hE : AnalyticOnNhd ℂ E (XiCRaw Gj (compWeight L a₁) ν j (scaledC0 d)
      (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl))) :
    AnalyticOnNhd ℂ (fun t : ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) × (Hm.Ω 1 × Fin N → ℂ) ×
        (RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)) =>
      eTermFun Gp Gk Gj Hm (compWeight L a₁) Fk E t.1 t.2.1 t.2.2)
      (FlRealLC Gp Hm a₁ ν BG κ eps X₁f BG₂ δ₁) :=
  eTermFun_analytic_of_one_le (one_le_scaledC0 d) le_rfl hB hF hFkan hFk hE

/-- **The bound of the old-term functional on the realizable triples.** -/
theorem eTermFun_bound_of_one_le {b : ℝ} (hb₁ : 1 ≤ b) (hbC : b ≤ scaledC0 d)
    (hB : BgSetting N Gp Gk Gj a₁ ν c BG κ r₀ eps δ₃ X₀ X₁f j)
    (hF : FlSetting N Gp Gk Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl X₁f)
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
  eTermFun_bound_of_bg hb₁ hbC hB.hS.fam.2.1 hB.ha₁ hB.HBp hB.HBk hB.HBj hB.hP hB.hq hB.colj
    hB.num hB.hj hB.hκ hF hFk
    (fun _ hs hs1 _ hD _ _ hI => bgStage_of_one_le hb₁ hbC hB hs hs1 hD hI) hEb ht

/-- **The bound of the old-term functional on the realizable triples.** -/
theorem eTermFun_bound (hB : BgSetting N Gp Gk Gj a₁ ν c BG κ r₀ eps δ₃ X₀ X₁f j)
    (hF : FlSetting N Gp Gk Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl X₁f)
    {Fk : RawData d L (N₁ * L ^ m₁) (k + 1) N → (Gk.Ω 1 × Fin N → ℂ) × (Gk.Ω 1 → ℂ)}
    (hFk : ∀ D : BgData Gk N, InUnionDomainC Gk (bgC0 d L N) (bgC1 d L N) ν D →
      Fk (rawOf D) = (bgFieldC Gk (compWeight L a₁) ν (bgC0 d L N) D,
        bgMultC Gk (compWeight L a₁) ν (bgC0 d L N) D))
    {E : RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ} {B : ℝ}
    (hEb : ∀ r ∈ XiCRaw Gj (compWeight L a₁) ν j (scaledC0 d)
      (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl), ‖E r‖ ≤ B)
    {t : ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) × (Hm.Ω 1 × Fin N → ℂ) ×
      (RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ))}
    (ht : t ∈ FlRealLC Gp Hm a₁ ν BG κ eps X₁f BG₂ δ₁) :
    ‖eTermFun Gp Gk Gj Hm (compWeight L a₁) Fk E t.1 t.2.1 t.2.2‖ ≤ B :=
  eTermFun_bound_of_one_le (one_le_scaledC0 d) le_rfl hB hF hFk hEb ht

/-- **Locality of the old-term functional**: it reads `φ`, `δφ`, `Ψ`, `h` and `ψ'` only at the
dependency sets of the data sites of `𝔹_k(X)`, which lie in `X₁`. -/
theorem eTermFun_local (hB : BgSetting N Gp Gk Gj a₁ ν c BG κ r₀ eps δ₃ X₀ X₁f j)
    (hF : FlSetting N Gp Gk Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl X₁f)
    (hcov : CovSetup Gp m₀ j X 𝒦X) (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp m₀ j 𝒦X)
    (Fk : RawData d L (N₁ * L ^ m₁) (k + 1) N → (Gk.Ω 1 × Fin N → ℂ) × (Gk.Ω 1 → ℂ))
    (E : RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ)
    {t t' : ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) × (Hm.Ω 1 × Fin N → ℂ) ×
      (RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ))}
    (hφ : ∀ y : Gp.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) →
      ∀ i, t.1.1 (y, i) = t'.1.1 (y, i))
    (hδ : ∀ y : Hm.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) →
      ∀ i, t.2.1 (y, i) = t'.2.1 (y, i))
    (hag : agreeOn (thickSet Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1)))) t.2.2.1 t'.2.2.1)
    (hψ : ∀ y ∈ psiThick (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))), t.2.2.2 y = t'.2.2.2 y) :
    eTermFun Gp Gk Gj Hm (compWeight L a₁) Fk E t.1 t.2.1 t.2.2 =
      eTermFun Gp Gk Gj Hm (compWeight L a₁) Fk E t'.1 t'.2.1 t'.2.2 := by
  classical
  have hX₁Ω : (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) ⊆ ↑(Gp.Ω 1) := fun x hx =>
    X1_subset_Omega1 hcov (hX₁ ▸ hx)
  have hXthick : ∀ y ∈ X₁f, t.2.2.1.1 y = t'.2.2.1.1 y ∧ t.2.2.1.2 y = t'.2.2.1.2 y := fun y hy =>
    hag y (Or.inl (Finset.mem_coe.2 hy))
  refine congrArg E (congrArg (D2raw Gk Gj (compWeight L a₁) Fk) ?_)
  refine Prod.ext (funext fun x => funext fun i => ?_) (funext fun x => funext fun i => ?_)
  · show composeField Gk Gp (compWeight L a₁) t.1.1 t.2.2.1.1 x i +
        composeField Gk Hm (compWeight L a₁) t.2.1 t.2.2.2 x i =
      composeField Gk Gp (compWeight L a₁) t'.1.1 t'.2.2.1.1 x i +
        composeField Gk Hm (compWeight L a₁) t'.2.1 t'.2.2.2 x i
    by_cases hx : x ∈ dataSites Gk
    · congr 1
      · refine composeField_congr (G := Gk) (G' := Gp) (compWeight L a₁) (fun y hy jj => ?_)
          (fun jj => congrFun (hXthick x (hB.dep x hx x (self_mem_composeDep x))).1 jj) i
        have hyX := hB.dep x hx y hy
        have hyΩ : y ∈ Gp.Ω 1 := hX₁Ω (Finset.mem_coe.2 hyX)
        rw [svec_of_mem' t.1.1 hyΩ jj, svec_of_mem' t'.1.1 hyΩ jj]
        exact hφ ⟨y, hyΩ⟩ (Finset.mem_coe.2 hyX) jj
      · refine composeField_congr (G := Gk) (G' := Hm) (compWeight L a₁) (fun y hy jj => ?_)
          (fun jj => congrFun (hψ x (Or.inl (Finset.mem_coe.2 (hF.depm x hx x
            (self_mem_composeDep x))))) jj) i
        have hyX := hF.depm x hx y hy
        by_cases hyΩ : y ∈ Hm.Ω 1
        · rw [svec_of_mem' t.2.1 hyΩ jj, svec_of_mem' t'.2.1 hyΩ jj]
          exact hδ ⟨y, hyΩ⟩ (Finset.mem_coe.2 hyX) jj
        · rw [svec_of_not_mem Hm t.2.1 hyΩ jj, svec_of_not_mem Hm t'.2.1 hyΩ jj]
    · rw [composeField_of_not_mem _ _ _ hx, composeField_of_not_mem _ _ _ hx,
        composeField_of_not_mem _ _ _ hx, composeField_of_not_mem _ _ _ hx]
  · show (if x ∈ Gk.Ω 1 then t.2.2.1.2 x i else 0) = (if x ∈ Gk.Ω 1 then t'.2.2.1.2 x i else 0)
    by_cases hx : x ∈ Gk.Ω 1
    · simp only [hx, ↓reduceIte]
      have hxd : x ∈ dataSites Gk := (mem_dataSites Gk).2 (Or.inl hx)
      exact congrFun (hXthick x (hB.dep x hxd x (self_mem_composeDep x))).2 i
    · simp [hx]

end Props

section Value

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱ₁ ϱ₂ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Gk : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁}
variable {Gj : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₂}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ r₀ eps δ₃ : ℝ} {X₀ X₁f : Finset (CTorus d L N₁ m₁ (k + 1))} {j : ℕ}
variable {Kc Cx c₂ BG₂ δ₁ δfl : ℝ} {m₀ : ℕ} {X 𝒦X : Set (CTorus d L N₁ m₁ (k + 1))}

/-- **The old-term functional at the triple of a datum, at given background stages** (the common
step of `eTermFun_value` and of its cover form `eTermFun_value_cover`): at the triple of `D` at
`s ≡ 1` the functional is the old term at the composed datum of P3 (4.16), (4.17),
`E(ψ(𝔹_j(X), 𝔹_k(X); ψ(𝔹_k(X), 𝔹_{k+1}; Θ) + δψ(𝔹_k(X), 𝔹_k; ψ')))` (the value of `flComp`). -/
theorem eTermFun_value_of_bg {b : ℝ} (hb₁ : 1 ≤ b) (hbC : b ≤ scaledC0 d) (hBG : 0 ≤ BG)
    (ha₁ : 0 < a₁) (HBp : BgHyp d L (k + 1) ϱ (compWeight L a₁) ν)
    (HBk : BgHyp d L (k + 1) ϱ₁ (compWeight L a₁) ν) (HBj : BgHyp d L (k + 1) ϱ₂ (compWeight L a₁) ν)
    (hP : Precedes Gk Gp) (hq : Precedes Gj Gk) (colj : ∀ z ∈ collar Gj, z ∈ Gk.Ω 1)
    (hnum : ChainNum d L N m₁ BG κ r₀ eps δ₃) (hj : j ≤ k + 1) (hκ : 0 < κ)
    (hF : FlSetting N Gp Gk Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl X₁f)
    {Fk : RawData d L (N₁ * L ^ m₁) (k + 1) N → (Gk.Ω 1 × Fin N → ℂ) × (Gk.Ω 1 → ℂ)}
    (hFk : ∀ D : BgData Gk N, InUnionDomainC Gk (bgC0 d L N) (bgC1 d L N) ν D →
      Fk (rawOf D) = (bgFieldC Gk (compWeight L a₁) ν (bgC0 d L N) D,
        bgMultC Gk (compWeight L a₁) ν (bgC0 d L N) D))
    (hbg : ∀ s : DecParams Gp, (∀ P, ‖s P‖ < Real.exp κ) →
      (∀ (P : ℕ × CTorus d L N₁ m₁ (k + 1)) (hP : P ∈ cubeIdx Gp), P ∉ parCubes Gp X₁f →
        s ⟨P, hP⟩ = 1) →
      ∀ D : BgData Gp N, XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D →
      ∀ (φ : Gp.Ω 1 × Fin N → ℂ) (α : Gp.Ω 1 → ℂ),
        IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        BgBounds Gp D φ α (K4 d L N BG κ * (xiC1 d * eps)) ∧
        XiCData Gk (compWeight L a₁) ν (k + 1) 1 (b ^ 2 * eps + xiK2 d L N * δ₃)
          (composeData hP (compWeight L a₁) φ D))
    (E : RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ)
    {D : BgData Gp N} (hD : XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D)
    (hI1 : IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) (fun _ => 1) D
      (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D)
      (bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D))
    {ψ' : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ} (hψ : ψ' ∈ FlBallLC Hm δ₁) :
    eTermFun Gp Gk Gj Hm (compWeight L a₁) Fk E
        (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D,
          bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D)
        (flFieldOne Gp Hm BG₂ κ a₁ ν D ψ') (rawOf D, ψ') =
      E (rawOf (composeData hq (compWeight L a₁)
        (bgFieldC Gk (compWeight L a₁) ν (bgC0 d L N)
          (flDatumOne Hm BG₂ κ hP hF.hPm a₁ ν D ψ' hψ.2))
        (flDatumOne Hm BG₂ κ hP hF.hPm a₁ ν D ψ' hψ.2))) := by
  classical
  have hE1 : 1 < Real.exp κ := Real.one_lt_exp_iff.2 hκ
  have hsx : ∀ P : ↥(cubeIdx Gp), ‖(fun _ : ↥(cubeIdx Gp) => (1 : ℂ)) P‖ < Real.exp κ :=
    fun P => by simpa using hE1
  have hbb1 := (hbg _ hsx (fun _ _ _ => rfl) D hD _ _ hI1).1
  have hmem := triple_one_mem_of_bg (X₁f := X₁f) hκ hBG HBp hnum.eps_pos hnum.small1
    hF.num.phi_lt hF.num.δ₁_pos hF.num.δ₁_le hF.num.B_le hF.hS2 hF.SM hF.hM2 hF.hPmp hD hI1 hbb1 hψ
  obtain ⟨D', ψ'', hlc, ht22, -, hD1, hD2, -⟩ := eTerm_chain_of_bg hb₁ hbC hBG ha₁ HBp HBk HBj
    hP hq colj hnum hj hκ hF hFk hbg hmem
  obtain ⟨hr, hψe⟩ := Prod.mk.inj ht22
  have hDD : D = D' := BgData.eq_of_raw hr
  subst hDD
  subst hψe
  show E (D2raw Gk Gj (compWeight L a₁) Fk (d1Triple Gp Gk Hm (compWeight L a₁) _ _ _)) = _
  rw [hD1, hD2]
  rfl

/-- **The old-term functional at the triple of a datum is the composite `flComp`.** -/
theorem eTermFun_value (hB : BgSetting N Gp Gk Gj a₁ ν c BG κ r₀ eps δ₃ X₀ X₁f j)
    (hF : FlSetting N Gp Gk Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl X₁f)
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
      flComp hB hF E (rawOf D, ψ') := by
  have hC := flCore_of hB hF
  have hd0 : 0 < d := by have := hC.HBp.hd; omega
  have hc1 := one_le_xiC1 d
  have hε := hC.eps_pos
  have hδ0 : 0 < xiC1 d * eps := by positivity
  have hE1 : 1 < Real.exp κ := Real.one_lt_exp_iff.2 hC.hκ
  have hsx : ∀ P : ↥(cubeIdx Gp), ‖(fun _ : ↥(cubeIdx Gp) => (1 : ℂ)) P‖ < Real.exp κ :=
    fun P => by simpa using hE1
  have hδ1 : xiC1 d * eps ≤ c7 d L N BG κ := hC.c7le
  have hδ0' : xiC1 d * eps ≤ bgC0 d L N := hδ1.trans ((c7_le_bgC1 d L N BG κ).trans
    (bgC1_le_bgC0 d L N hd0))
  have hνε : ν * ((L : ℝ) ^ (k + 1)) ^ 2 * (xiC1 d * eps) ^ 2 ≤ (xiC1 d * eps) ^ 2 := by
    have := hC.HBp.massLe; nlinarith [sq_nonneg (xiC1 d * eps)]
  have hDom := xiCData_inDomainC hC.HBp hC.small1 hD
  obtain ⟨φ, α, hI, -, -⟩ := flCore_bgBounds hC hsx hD
  obtain ⟨-, hφ1, hα1⟩ := i4b_one hC.hS hC.Sp hC.HBp hC.hκ.le hC.hM hδ0 le_rfl hδ0' hδ1
    hνε hDom hI
  subst hφ1 hα1
  rw [flComp_rawOf hB hF E hD hψ.2]
  exact eTermFun_value_of_bg (one_le_scaledC0 d) le_rfl hB.hS.fam.2.1 hB.ha₁ hB.HBp hB.HBk hB.HBj
    hB.hP hB.hq hB.colj hB.num hB.hj hB.hκ hF hFk
    (fun _ hs hs1 _ hD _ _ hI => bgStage_of_one_le (one_le_scaledC0 d) le_rfl hB hs hs1 hD hI)
    E hD hI hψ

end Value

section EngineE

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱ₁ ϱ₂ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Gk : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁}
variable {Gj : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₂}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ r₀ eps δ₃ : ℝ} {X₀ X₁f : Finset (CTorus d L N₁ m₁ (k + 1))} {j : ℕ}
variable {Kc Cx c₂ BG₂ δ₁ δfl : ℝ} {m₀ : ℕ} {X 𝒦X : Set (CTorus d L N₁ m₁ (k + 1))}

/-- **An old term along the fluctuation expands over the domains `Y ⊃ X₁`, with terms local in
`ψ̂`** (the hat version of `i5_fluct`). -/
theorem eterm_expansion_hat_of_one_le {b : ℝ} (hb₁ : 1 ≤ b) (hbC : b ≤ scaledC0 d) (hB : BgSetting N Gp Gk Gj a₁ ν c BG κ r₀ eps δ₃ X₀ X₁f j)
    (hF : FlSetting N Gp Gk Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl X₁f)
    (hk : 1 ≤ k) (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    (hcov : CovSetup Gp m₀ j X 𝒦X) (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp m₀ j 𝒦X)
    (hconn : HatConn Gp) (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
    (hopt : ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X) ∧ MeetsOne m₀ j 𝒦X W₀ ∧
        bondCost (scaleW L m₀ m₁ j) E₀ = treeLenCovOne m₀ j X)
    {κdec κ₀ Eb : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hEb : 0 ≤ Eb) {E : RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ}
    (hEan : AnalyticOnNhd ℂ E (XiCRaw Gj (compWeight L a₁) ν j b
      (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)))
    (hEbd : ∀ r ∈ XiCRaw Gj (compWeight L a₁) ν j b
      (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      ‖E r‖ ≤ Eb * Real.exp (-(κdec - 1) * treeLenCovOne m₀ j X)) :
    ∃ Ev : Set (CTorus d L N₁ m₁ (k + 1)) →
        RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gp × Fin N → ℂ) → ℂ,
      (∀ D : BgData Gp N, XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D →
        ∀ ψh : unitPts Gp × Fin N → ℂ, (∀ p, ‖ψh p‖ ≤ cψ) →
        flComp hB hF E (rawOf D, hatLift Gp a₁ ν hG' cc D ψh) =
        ∑ Y ∈ polymerDomains (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1)
          Gp m₀ (X1 Gp m₀ j 𝒦X), Ev Y (rawOf D, ψh)) ∧
      (∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        ∀ u' ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        AgHat hG' Y u u' → Ev Y u = Ev Y u') ∧
      (∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        ‖Ev Y u‖ ≤ Eb * Real.exp (-κ₀ * treeLenCovOne m₀ j X - 2 * κdec * treeLenCov Gp m₀ Y)) ∧
      (∀ Y, AnalyticOnNhd ℂ (Ev Y) (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ})) := by
  classical
  obtain ⟨Fk, hFkan, hFk⟩ := theorem72_analytic (G := Gk) (a := compWeight L a₁) (ν := ν) hB.HBk
  have hC := flCore_of hB hF
  obtain ⟨Ev, h1', h2', h3', h4'⟩ := i5_functional_hatLC hC hk hG hG' cc hcψ hMX hdm hα hsm hδ₁
    hcov hX₁ hconn hrow hopt hκ₀ hκdec hκ h1 hlog hEb
    (Φ := eTermFun Gp Gk Gj Hm (compWeight L a₁) Fk E)
    (eTermFun_analytic_of_one_le hb₁ hbC hB hF hFkan hFk hEan)
    (fun t ht => eTermFun_bound_of_one_le hb₁ hbC hB hF hFk hEbd ht)
    (Z := ↑X₁f) (Zα := ∅) subset_rfl (fun x hx => absurd hx (Set.notMem_empty x))
    (fun t _ t' _ hφ _ hδ hag hψ => eTermFun_local hB hF hcov hX₁ Fk E hφ hδ hag hψ)
  refine ⟨Ev, fun D hD ψh hψh => ?_, h2', h3', h4'⟩
  rw [← h1' D hD ψh hψh]
  exact (eTermFun_value hB hF hFk E hD
    (hatLift_mem_flBallLC hC hk hG hG' cc hcψ hMX hdm hα hsm hδ₁ hD hψh)).symm

/-- **An old term along the fluctuation expands over the domains `Y ⊃ X₁`, with terms local in
`ψ̂`** (the hat version of `i5_fluct`). -/
theorem eterm_expansion_hat (hB : BgSetting N Gp Gk Gj a₁ ν c BG κ r₀ eps δ₃ X₀ X₁f j)
    (hF : FlSetting N Gp Gk Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl X₁f)
    (hk : 1 ≤ k) (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    (hcov : CovSetup Gp m₀ j X 𝒦X) (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp m₀ j 𝒦X)
    (hconn : HatConn Gp) (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
    (hopt : ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X) ∧ MeetsOne m₀ j 𝒦X W₀ ∧
        bondCost (scaleW L m₀ m₁ j) E₀ = treeLenCovOne m₀ j X)
    {κdec κ₀ Eb : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hEb : 0 ≤ Eb) {E : RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ}
    (hEan : AnalyticOnNhd ℂ E (XiCRaw Gj (compWeight L a₁) ν j (scaledC0 d)
      (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)))
    (hEbd : ∀ r ∈ XiCRaw Gj (compWeight L a₁) ν j (scaledC0 d)
      (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      ‖E r‖ ≤ Eb * Real.exp (-(κdec - 1) * treeLenCovOne m₀ j X)) :
    ∃ Ev : Set (CTorus d L N₁ m₁ (k + 1)) →
        RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gp × Fin N → ℂ) → ℂ,
      (∀ D : BgData Gp N, XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D →
        ∀ ψh : unitPts Gp × Fin N → ℂ, (∀ p, ‖ψh p‖ ≤ cψ) →
        flComp hB hF E (rawOf D, hatLift Gp a₁ ν hG' cc D ψh) =
        ∑ Y ∈ polymerDomains (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1)
          Gp m₀ (X1 Gp m₀ j 𝒦X), Ev Y (rawOf D, ψh)) ∧
      (∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        ∀ u' ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        AgHat hG' Y u u' → Ev Y u = Ev Y u') ∧
      (∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        ‖Ev Y u‖ ≤ Eb * Real.exp (-κ₀ * treeLenCovOne m₀ j X - 2 * κdec * treeLenCov Gp m₀ Y)) ∧
      (∀ Y, AnalyticOnNhd ℂ (Ev Y) (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ})) :=
  eterm_expansion_hat_of_one_le (one_le_scaledC0 d) le_rfl hB hF hk hG hG' cc hcψ hMX hdm hα hsm hδ₁ hcov hX₁ hconn hrow hopt hκ₀ hκdec hκ h1 hlog hEb hEan hEbd

end EngineE

section ELoc

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱ₁ ϱ₂ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Gk : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁}
variable {Gj : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₂}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ r₀ eps δ₃ : ℝ} {X₀ X₁f : Finset (CTorus d L N₁ m₁ (k + 1))} {j : ℕ}
variable {Kc Cx c₂ BG₂ δ₁ δfl : ℝ} {m₀ : ℕ} {X 𝒦X : Set (CTorus d L N₁ m₁ (k + 1))}

/-- **The `δ𝓔'`-term of one old term in the variable `ψ̂`** (hat version of `eterm_locInt`). -/
theorem eterm_locInt_hat_dm_of_one_le {b : ℝ} (hb₁ : 1 ≤ b) (hbC : b ≤ scaledC0 d) (hB : BgSetting N Gp Gk Gj a₁ ν c BG κ r₀ eps δ₃ X₀ X₁f j)
    (hF : FlSetting N Gp Gk Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl X₁f)
    (hk : 1 ≤ k) (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    (hcov : CovSetup Gp m₀ j X 𝒦X) (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp m₀ j 𝒦X)
    (hconn : HatConn Gp) (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
    (hopt : ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X) ∧ MeetsOne m₀ j 𝒦X W₀ ∧
        bondCost (scaleW L m₀ m₁ j) E₀ = treeLenCovOne m₀ j X)
    {κdec κ₀ Eb : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hEb : 0 ≤ Eb) {E : RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ}
    (hEan : AnalyticOnNhd ℂ E (XiCRaw Gj (compWeight L a₁) ν j b
      (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)))
    (hEbd : ∀ r ∈ XiCRaw Gj (compWeight L a₁) ν j b
      (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      ‖E r‖ ≤ Eb * Real.exp (-(κdec - 1) * treeLenCovOne m₀ j X))
    {ω : ℂ → ℂ} (hωc : Continuous ω) {R₁ : ℝ} (hR₁ : 1 < R₁)
    (hω : AnalyticOnNhd ℂ ω (ball (0 : ℂ) R₁)) {Mω : ℝ} (hMω : 0 ≤ Mω)
    (hωb : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → ‖ω (t : ℂ)‖ ≤ Mω) {r Rσ : ℝ} (hr : 0 < r) :
    ∃ Ev : Set (CTorus d L N₁ m₁ (k + 1)) →
        RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gp × Fin N → ℂ) → ℂ,
      LocIntDm (IsDj m₀ (k + 1)) (id : (unitPts Gp × Fin N → ℂ) → _)
        (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps) (HatRaysO Gp cψ R₁ Rσ r) Rσ
        (polymerDomains (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) Gp m₀
          (X1 Gp m₀ j 𝒦X))
        (fun Y x₀ w σ Θ => dirTerm (Ev Y) ω x₀ w σ Θ)
        (fun x₀ w σ Θ => dirTermSrc (hatFun Gp a₁ ν eps hG' cc (flComp hB hF E)) ω x₀ w σ Θ)
        (fun Y => Mω * ((Eb * Real.exp (-κ₀ * treeLenCovOne m₀ j X
          - 2 * κdec * treeLenCov Gp m₀ Y)) / r))
        (fun Y Θ Θ' => agreeOn (thickSet Gp Y) Θ Θ') (AgHatF Gp hG') := by
  classical
  obtain ⟨Ev, hsum, hloc, hbd, hanY⟩ := eterm_expansion_hat_of_one_le hb₁ hbC hB hF hk hG hG' cc hcψ hMX hdm hα hsm
    hδ₁ hcov hX₁ hconn hrow hopt hκ₀ hκdec hκ h1 hlog hEb hEan hEbd
  have hd : 3 ≤ d := (flCore_of hB hF).HBp.hd
  refine ⟨Ev, ?_⟩
  have hbase := locInt_dir1 (S := XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps)
    (B := hatBall (N := N) Gp cψ)
    (f := hatFun Gp a₁ ν eps hG' cc (flComp hB hF E))
    (polymerDomains (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) Gp m₀
      (X1 Gp m₀ j 𝒦X)) (Evs := Ev)
    (b := fun Y => Eb * Real.exp (-κ₀ * treeLenCovOne m₀ j X - 2 * κdec * treeLenCov Gp m₀ Y))
    (AgΘ := fun Y Θ Θ' => agreeOn (thickSet Gp Y) Θ Θ')
    (AgF := AgHatF Gp hG') (Rσ := Rσ) hR₁ hω hωc hMω hωb hr
    (isOpen_hatBall cψ) (fun Y => (hanY Y).mono (Set.prod_mono le_rfl (hatBall_subset cψ)))
    (fun Y u hu => hbd Y u ⟨hu.1, hatBall_subset cψ hu.2⟩)
    (fun Y a a' c' c'' p q ha hb y hy i => by simp [ha y hy i, hb y hy i])
    (fun Y Θ hΘ Θ' hΘ' z hz z' hz' h1' h2' =>
      hloc Y (Θ, z) ⟨hΘ, hatBall_subset cψ hz⟩ (Θ', z') ⟨hΘ', hatBall_subset cψ hz'⟩ ⟨h1', h2'⟩)
    (fun Θ hΘ ψh hψ => by
      obtain ⟨D, hD, rfl⟩ := hΘ
      rw [hatFun_rawOf hG' cc _ hD]
      exact hsum D hD ψh (hatBall_subset cψ hψ))
  exact LocIntDm.mk hbase (fun Y hY => isDj_of_polyDom hG' hcov hd hopt hY)
    (diagCont_dirTerm _ hR₁ hωc hr
      (fun Y => (hanY Y).mono (Set.prod_mono le_rfl (hatBall_subset cψ))))

/-- **The `δ𝓔'`-term of one old term in the variable `ψ̂`** (hat version of `eterm_locInt`). -/
theorem eterm_locInt_hat_dm (hB : BgSetting N Gp Gk Gj a₁ ν c BG κ r₀ eps δ₃ X₀ X₁f j)
    (hF : FlSetting N Gp Gk Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl X₁f)
    (hk : 1 ≤ k) (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    (hcov : CovSetup Gp m₀ j X 𝒦X) (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp m₀ j 𝒦X)
    (hconn : HatConn Gp) (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
    (hopt : ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X) ∧ MeetsOne m₀ j 𝒦X W₀ ∧
        bondCost (scaleW L m₀ m₁ j) E₀ = treeLenCovOne m₀ j X)
    {κdec κ₀ Eb : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hEb : 0 ≤ Eb) {E : RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ}
    (hEan : AnalyticOnNhd ℂ E (XiCRaw Gj (compWeight L a₁) ν j (scaledC0 d)
      (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)))
    (hEbd : ∀ r ∈ XiCRaw Gj (compWeight L a₁) ν j (scaledC0 d)
      (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      ‖E r‖ ≤ Eb * Real.exp (-(κdec - 1) * treeLenCovOne m₀ j X))
    {ω : ℂ → ℂ} (hωc : Continuous ω) {R₁ : ℝ} (hR₁ : 1 < R₁)
    (hω : AnalyticOnNhd ℂ ω (ball (0 : ℂ) R₁)) {Mω : ℝ} (hMω : 0 ≤ Mω)
    (hωb : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → ‖ω (t : ℂ)‖ ≤ Mω) {r Rσ : ℝ} (hr : 0 < r) :
    ∃ Ev : Set (CTorus d L N₁ m₁ (k + 1)) →
        RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gp × Fin N → ℂ) → ℂ,
      LocIntDm (IsDj m₀ (k + 1)) (id : (unitPts Gp × Fin N → ℂ) → _)
        (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps) (HatRaysO Gp cψ R₁ Rσ r) Rσ
        (polymerDomains (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) Gp m₀
          (X1 Gp m₀ j 𝒦X))
        (fun Y x₀ w σ Θ => dirTerm (Ev Y) ω x₀ w σ Θ)
        (fun x₀ w σ Θ => dirTermSrc (hatFun Gp a₁ ν eps hG' cc (flComp hB hF E)) ω x₀ w σ Θ)
        (fun Y => Mω * ((Eb * Real.exp (-κ₀ * treeLenCovOne m₀ j X
          - 2 * κdec * treeLenCov Gp m₀ Y)) / r))
        (fun Y Θ Θ' => agreeOn (thickSet Gp Y) Θ Θ') (AgHatF Gp hG') :=
  eterm_locInt_hat_dm_of_one_le (one_le_scaledC0 d) le_rfl hB hF hk hG hG' cc hcψ hMX hdm hα hsm hδ₁ hcov hX₁ hconn hrow hopt hκ₀ hκdec hκ h1 hlog hEb hEan hEbd hωc hR₁ hω hMω hωb hr

/-- **The `δ𝓔'`-term of one old term in the variable `ψ̂`** (hat version of `eterm_locInt`). -/
theorem eterm_locInt_hat_of_one_le {b : ℝ} (hb₁ : 1 ≤ b) (hbC : b ≤ scaledC0 d) (hB : BgSetting N Gp Gk Gj a₁ ν c BG κ r₀ eps δ₃ X₀ X₁f j)
    (hF : FlSetting N Gp Gk Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl X₁f)
    (hk : 1 ≤ k) (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    (hcov : CovSetup Gp m₀ j X 𝒦X) (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp m₀ j 𝒦X)
    (hconn : HatConn Gp) (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
    (hopt : ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X) ∧ MeetsOne m₀ j 𝒦X W₀ ∧
        bondCost (scaleW L m₀ m₁ j) E₀ = treeLenCovOne m₀ j X)
    {κdec κ₀ Eb : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hEb : 0 ≤ Eb) {E : RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ}
    (hEan : AnalyticOnNhd ℂ E (XiCRaw Gj (compWeight L a₁) ν j b
      (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)))
    (hEbd : ∀ r ∈ XiCRaw Gj (compWeight L a₁) ν j b
      (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      ‖E r‖ ≤ Eb * Real.exp (-(κdec - 1) * treeLenCovOne m₀ j X))
    {ω : ℂ → ℂ} (hωc : Continuous ω) {R₁ : ℝ} (hR₁ : 1 < R₁)
    (hω : AnalyticOnNhd ℂ ω (ball (0 : ℂ) R₁)) {Mω : ℝ} (hMω : 0 ≤ Mω)
    (hωb : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → ‖ω (t : ℂ)‖ ≤ Mω) {r Rσ : ℝ} (hr : 0 < r) :
    ∃ Ev : Set (CTorus d L N₁ m₁ (k + 1)) →
        RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gp × Fin N → ℂ) → ℂ,
      LocInt (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps) (HatRaysO Gp cψ R₁ Rσ r) Rσ
        (polymerDomains (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) Gp m₀
          (X1 Gp m₀ j 𝒦X))
        (fun Y x₀ w σ Θ => dirTerm (Ev Y) ω x₀ w σ Θ)
        (fun x₀ w σ Θ => dirTermSrc (hatFun Gp a₁ ν eps hG' cc (flComp hB hF E)) ω x₀ w σ Θ)
        (fun Y => Mω * ((Eb * Real.exp (-κ₀ * treeLenCovOne m₀ j X
          - 2 * κdec * treeLenCov Gp m₀ Y)) / r))
        (fun Y Θ Θ' => agreeOn (thickSet Gp Y) Θ Θ') (AgHatF Gp hG') := by
  obtain ⟨T, h⟩ := eterm_locInt_hat_dm_of_one_le hb₁ hbC hB hF hk hG hG' cc (cψ := cψ) hcψ hMX (δc := δc) hdm hα hsm hδ₁ hcov hX₁ hconn hrow hopt (κdec := κdec) (κ₀ := κ₀) (Eb := Eb) hκ₀ hκdec hκ h1 hlog hEb (E := E) hEan hEbd (ω := ω) hωc (R₁ := R₁) hR₁ hω (Mω := Mω) hMω hωb (r := r) (Rσ := Rσ) hr
  exact ⟨T, h.loc⟩

/-- **The `δ𝓔'`-term of one old term in the variable `ψ̂`** (hat version of `eterm_locInt`). -/
theorem eterm_locInt_hat (hB : BgSetting N Gp Gk Gj a₁ ν c BG κ r₀ eps δ₃ X₀ X₁f j)
    (hF : FlSetting N Gp Gk Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl X₁f)
    (hk : 1 ≤ k) (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    (hcov : CovSetup Gp m₀ j X 𝒦X) (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp m₀ j 𝒦X)
    (hconn : HatConn Gp) (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
    (hopt : ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X) ∧ MeetsOne m₀ j 𝒦X W₀ ∧
        bondCost (scaleW L m₀ m₁ j) E₀ = treeLenCovOne m₀ j X)
    {κdec κ₀ Eb : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hEb : 0 ≤ Eb) {E : RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ}
    (hEan : AnalyticOnNhd ℂ E (XiCRaw Gj (compWeight L a₁) ν j (scaledC0 d)
      (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)))
    (hEbd : ∀ r ∈ XiCRaw Gj (compWeight L a₁) ν j (scaledC0 d)
      (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      ‖E r‖ ≤ Eb * Real.exp (-(κdec - 1) * treeLenCovOne m₀ j X))
    {ω : ℂ → ℂ} (hωc : Continuous ω) {R₁ : ℝ} (hR₁ : 1 < R₁)
    (hω : AnalyticOnNhd ℂ ω (ball (0 : ℂ) R₁)) {Mω : ℝ} (hMω : 0 ≤ Mω)
    (hωb : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → ‖ω (t : ℂ)‖ ≤ Mω) {r Rσ : ℝ} (hr : 0 < r) :
    ∃ Ev : Set (CTorus d L N₁ m₁ (k + 1)) →
        RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gp × Fin N → ℂ) → ℂ,
      LocInt (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps) (HatRaysO Gp cψ R₁ Rσ r) Rσ
        (polymerDomains (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) Gp m₀
          (X1 Gp m₀ j 𝒦X))
        (fun Y x₀ w σ Θ => dirTerm (Ev Y) ω x₀ w σ Θ)
        (fun x₀ w σ Θ => dirTermSrc (hatFun Gp a₁ ν eps hG' cc (flComp hB hF E)) ω x₀ w σ Θ)
        (fun Y => Mω * ((Eb * Real.exp (-κ₀ * treeLenCovOne m₀ j X
          - 2 * κdec * treeLenCov Gp m₀ Y)) / r))
        (fun Y Θ Θ' => agreeOn (thickSet Gp Y) Θ Θ') (AgHatF Gp hG') :=
  eterm_locInt_hat_of_one_le (one_le_scaledC0 d) le_rfl hB hF hk hG hG' cc hcψ hMX hdm hα hsm hδ₁ hcov hX₁ hconn hrow hopt hκ₀ hκdec hκ h1 hlog hEb hEan hEbd hωc hR₁ hω hMω hωb hr

end ELoc

section EFamily

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ eps : ℝ}

/-- **The `δ𝓔'`-part for a finite family of old terms, in the variable `ψ̂`** (hat version of
`eterms_locInt`). -/
theorem eterms_locInt_hat_dm_of_one_le {b : ℝ} (hb₁ : 1 ≤ b) (hbC : b ≤ scaledC0 d) {τι : Type*} [DecidableEq τι] (𝒯 : Finset τι) {ϱ₁ ϱ₂ : τι → ℝ}
    {Gk : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₁ τ)}
    {Gj : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₂ τ)}
    {r₀ δ₃ : ℝ} {X₀ X₁f : τι → Finset (CTorus d L N₁ m₁ (k + 1))} {j m₀ : τι → ℕ}
    {X 𝒦X : τι → Set (CTorus d L N₁ m₁ (k + 1))} {Kc Cx c₂ BG₂ δ₁ δfl : ℝ}
    (hB : ∀ τ ∈ 𝒯, BgSetting N Gp (Gk τ) (Gj τ) a₁ ν c BG κ r₀ eps δ₃ (X₀ τ) (X₁f τ) (j τ))
    (hF : ∀ τ ∈ 𝒯, FlSetting N Gp (Gk τ) Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl (X₁f τ))
    (hk : 1 ≤ k) (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    (hcov : ∀ τ ∈ 𝒯, CovSetup Gp (m₀ τ) (j τ) (X τ) (𝒦X τ))
    (hX₁ : ∀ τ ∈ 𝒯, (↑(X₁f τ) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp (m₀ τ) (j τ) (𝒦X τ))
    (hconn : HatConn Gp) (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
    (hopt : ∀ τ ∈ 𝒯, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X τ) ∧ MeetsOne (m₀ τ) (j τ) (𝒦X τ) W₀ ∧
        bondCost (scaleW L (m₀ τ) m₁ (j τ)) E₀ = treeLenCovOne (m₀ τ) (j τ) (X τ))
    {κdec κ₀ : ℝ} {Eb : τι → ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : ∀ τ ∈ 𝒯, Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀ τ) ^ d : ℕ) : ℝ)) ≤
      (κ / 2 - 1) / 2)
    (hEb : ∀ τ ∈ 𝒯, 0 ≤ Eb τ) {E : τι → RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ}
    (hEan : ∀ τ ∈ 𝒯, AnalyticOnNhd ℂ (E τ) (XiCRaw (Gj τ) (compWeight L a₁) ν (j τ) b
      (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)))
    (hEbd : ∀ τ ∈ 𝒯, ∀ r ∈ XiCRaw (Gj τ) (compWeight L a₁) ν (j τ) b
      (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      ‖E τ r‖ ≤ Eb τ * Real.exp (-(κdec - 1) * treeLenCovOne (m₀ τ) (j τ) (X τ)))
    {ω : ℂ → ℂ} (hωc : Continuous ω) {R₁ : ℝ} (hR₁ : 1 < R₁)
    (hω : AnalyticOnNhd ℂ ω (ball (0 : ℂ) R₁)) {Mω : ℝ} (hMω : 0 ≤ Mω)
    (hωb : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → ‖ω (t : ℂ)‖ ≤ Mω) {r Rσ : ℝ} (hr : 0 < r) :
    ∃ (T : τι → Set (CTorus d L N₁ m₁ (k + 1)) → (unitPts Gp × Fin N → ℂ) →
        (unitPts Gp × Fin N → ℂ) → ℂ → RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ),
      LocIntDm (fun Y => ∃ τ ∈ 𝒯, IsDj (m₀ τ) (k + 1) Y) (id : (unitPts Gp × Fin N → ℂ) → _)
        (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps) (HatRaysO Gp cψ R₁ Rσ r) Rσ
        (𝒯.biUnion fun τ => polyDom Gp (X₁f τ) (m₀ τ) (j τ) (𝒦X τ))
        (fun Y x₀ w σ Θ => ∑ τ ∈ 𝒯, if Y ∈ polyDom Gp (X₁f τ) (m₀ τ) (j τ) (𝒦X τ) then
          T τ Y x₀ w σ Θ else 0)
        (fun x₀ w σ Θ => ∑ τ ∈ 𝒯, if h : τ ∈ 𝒯 then
          dirTermSrc (hatFun Gp a₁ ν eps hG' cc (flComp (hB τ h) (hF τ h) (E τ))) ω x₀ w σ Θ
          else 0)
        (fun Y => ∑ τ ∈ 𝒯, if Y ∈ polyDom Gp (X₁f τ) (m₀ τ) (j τ) (𝒦X τ) then
          Mω * ((Eb τ * Real.exp (-κ₀ * treeLenCovOne (m₀ τ) (j τ)
          (X τ) - 2 * κdec * treeLenCov Gp (m₀ τ) Y)) / r) else 0)
        (fun Y Θ Θ' => agreeOn (thickSet Gp Y) Θ Θ') (AgHatF Gp hG') := by
  classical
  have hex : ∀ τ, ∃ (Ev : Set (CTorus d L N₁ m₁ (k + 1)) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gp × Fin N → ℂ) → ℂ), τ ∈ 𝒯 →
      LocIntDm (fun Y => ∃ τ' ∈ 𝒯, IsDj (m₀ τ') (k + 1) Y) (id : (unitPts Gp × Fin N → ℂ) → _)
        (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps) (HatRaysO Gp cψ R₁ Rσ r) Rσ
        (polymerDomains (fun i : ParIdx Gp (↑(X₁f τ) : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1)
          Gp (m₀ τ) (X1 Gp (m₀ τ) (j τ) (𝒦X τ)))
        (fun Y x₀ w σ Θ => dirTerm (Ev Y) ω x₀ w σ Θ)
        (fun x₀ w σ Θ => if h : τ ∈ 𝒯 then
          dirTermSrc (hatFun Gp a₁ ν eps hG' cc (flComp (hB τ h) (hF τ h) (E τ))) ω x₀ w σ Θ
          else 0)
        (fun Y => Mω * ((Eb τ * Real.exp (-κ₀ * treeLenCovOne (m₀ τ) (j τ)
          (X τ) - 2 * κdec * treeLenCov Gp (m₀ τ) Y)) / r))
        (fun Y Θ Θ' => agreeOn (thickSet Gp Y) Θ Θ') (AgHatF Gp hG') := by
    intro τ
    by_cases hτ : τ ∈ 𝒯
    · obtain ⟨Ev, hEv⟩ := eterm_locInt_hat_dm_of_one_le hb₁ hbC (hB τ hτ) (hF τ hτ) hk hG hG' cc hcψ hMX hdm hα hsm hδ₁
        (hcov τ hτ) (hX₁ τ hτ) hconn hrow (hopt τ hτ) hκ₀ hκdec hκ h1 (hlog τ hτ) (hEb τ hτ)
        (hEan τ hτ) (hEbd τ hτ) hωc hR₁ hω hMω hωb hr (Rσ := Rσ)
      exact ⟨Ev, fun _ => by simpa [hτ] using hEv.mono_P fun Y hY => ⟨τ, hτ, hY⟩⟩
    · exact ⟨fun _ _ => 0, fun h => absurd h hτ⟩
  choose Ev hEv using hex
  exact ⟨fun τ Y x₀ w σ Θ => dirTerm (Ev τ Y) ω x₀ w σ Θ,
    LocIntDm.finsum 𝒯 (fun τ hτ => hEv τ hτ)⟩

/-- **The `δ𝓔'`-part for a finite family of old terms, in the variable `ψ̂`** (hat version of
`eterms_locInt`). -/
theorem eterms_locInt_hat_dm {τι : Type*} [DecidableEq τι] (𝒯 : Finset τι) {ϱ₁ ϱ₂ : τι → ℝ}
    {Gk : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₁ τ)}
    {Gj : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₂ τ)}
    {r₀ δ₃ : ℝ} {X₀ X₁f : τι → Finset (CTorus d L N₁ m₁ (k + 1))} {j m₀ : τι → ℕ}
    {X 𝒦X : τι → Set (CTorus d L N₁ m₁ (k + 1))} {Kc Cx c₂ BG₂ δ₁ δfl : ℝ}
    (hB : ∀ τ ∈ 𝒯, BgSetting N Gp (Gk τ) (Gj τ) a₁ ν c BG κ r₀ eps δ₃ (X₀ τ) (X₁f τ) (j τ))
    (hF : ∀ τ ∈ 𝒯, FlSetting N Gp (Gk τ) Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl (X₁f τ))
    (hk : 1 ≤ k) (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    (hcov : ∀ τ ∈ 𝒯, CovSetup Gp (m₀ τ) (j τ) (X τ) (𝒦X τ))
    (hX₁ : ∀ τ ∈ 𝒯, (↑(X₁f τ) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp (m₀ τ) (j τ) (𝒦X τ))
    (hconn : HatConn Gp) (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
    (hopt : ∀ τ ∈ 𝒯, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X τ) ∧ MeetsOne (m₀ τ) (j τ) (𝒦X τ) W₀ ∧
        bondCost (scaleW L (m₀ τ) m₁ (j τ)) E₀ = treeLenCovOne (m₀ τ) (j τ) (X τ))
    {κdec κ₀ : ℝ} {Eb : τι → ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : ∀ τ ∈ 𝒯, Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀ τ) ^ d : ℕ) : ℝ)) ≤
      (κ / 2 - 1) / 2)
    (hEb : ∀ τ ∈ 𝒯, 0 ≤ Eb τ) {E : τι → RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ}
    (hEan : ∀ τ ∈ 𝒯, AnalyticOnNhd ℂ (E τ) (XiCRaw (Gj τ) (compWeight L a₁) ν (j τ) (scaledC0 d)
      (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)))
    (hEbd : ∀ τ ∈ 𝒯, ∀ r ∈ XiCRaw (Gj τ) (compWeight L a₁) ν (j τ) (scaledC0 d)
      (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      ‖E τ r‖ ≤ Eb τ * Real.exp (-(κdec - 1) * treeLenCovOne (m₀ τ) (j τ) (X τ)))
    {ω : ℂ → ℂ} (hωc : Continuous ω) {R₁ : ℝ} (hR₁ : 1 < R₁)
    (hω : AnalyticOnNhd ℂ ω (ball (0 : ℂ) R₁)) {Mω : ℝ} (hMω : 0 ≤ Mω)
    (hωb : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → ‖ω (t : ℂ)‖ ≤ Mω) {r Rσ : ℝ} (hr : 0 < r) :
    ∃ (T : τι → Set (CTorus d L N₁ m₁ (k + 1)) → (unitPts Gp × Fin N → ℂ) →
        (unitPts Gp × Fin N → ℂ) → ℂ → RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ),
      LocIntDm (fun Y => ∃ τ ∈ 𝒯, IsDj (m₀ τ) (k + 1) Y) (id : (unitPts Gp × Fin N → ℂ) → _)
        (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps) (HatRaysO Gp cψ R₁ Rσ r) Rσ
        (𝒯.biUnion fun τ => polyDom Gp (X₁f τ) (m₀ τ) (j τ) (𝒦X τ))
        (fun Y x₀ w σ Θ => ∑ τ ∈ 𝒯, if Y ∈ polyDom Gp (X₁f τ) (m₀ τ) (j τ) (𝒦X τ) then
          T τ Y x₀ w σ Θ else 0)
        (fun x₀ w σ Θ => ∑ τ ∈ 𝒯, if h : τ ∈ 𝒯 then
          dirTermSrc (hatFun Gp a₁ ν eps hG' cc (flComp (hB τ h) (hF τ h) (E τ))) ω x₀ w σ Θ
          else 0)
        (fun Y => ∑ τ ∈ 𝒯, if Y ∈ polyDom Gp (X₁f τ) (m₀ τ) (j τ) (𝒦X τ) then
          Mω * ((Eb τ * Real.exp (-κ₀ * treeLenCovOne (m₀ τ) (j τ)
          (X τ) - 2 * κdec * treeLenCov Gp (m₀ τ) Y)) / r) else 0)
        (fun Y Θ Θ' => agreeOn (thickSet Gp Y) Θ Θ') (AgHatF Gp hG') :=
  eterms_locInt_hat_dm_of_one_le (one_le_scaledC0 d) le_rfl 𝒯 hB hF hk hG hG' cc hcψ hMX hdm hα hsm hδ₁ hcov hX₁ hconn hrow hopt hκ₀ hκdec hκ h1 hlog hEb hEan hEbd hωc hR₁ hω hMω hωb hr

/-- **The `δ𝓔'`-part for a finite family of old terms, in the variable `ψ̂`** (hat version of
`eterms_locInt`). -/
theorem eterms_locInt_hat_of_one_le {b : ℝ} (hb₁ : 1 ≤ b) (hbC : b ≤ scaledC0 d) {τι : Type*} [DecidableEq τι] (𝒯 : Finset τι) {ϱ₁ ϱ₂ : τι → ℝ}
    {Gk : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₁ τ)}
    {Gj : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₂ τ)}
    {r₀ δ₃ : ℝ} {X₀ X₁f : τι → Finset (CTorus d L N₁ m₁ (k + 1))} {j m₀ : τι → ℕ}
    {X 𝒦X : τι → Set (CTorus d L N₁ m₁ (k + 1))} {Kc Cx c₂ BG₂ δ₁ δfl : ℝ}
    (hB : ∀ τ ∈ 𝒯, BgSetting N Gp (Gk τ) (Gj τ) a₁ ν c BG κ r₀ eps δ₃ (X₀ τ) (X₁f τ) (j τ))
    (hF : ∀ τ ∈ 𝒯, FlSetting N Gp (Gk τ) Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl (X₁f τ))
    (hk : 1 ≤ k) (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    (hcov : ∀ τ ∈ 𝒯, CovSetup Gp (m₀ τ) (j τ) (X τ) (𝒦X τ))
    (hX₁ : ∀ τ ∈ 𝒯, (↑(X₁f τ) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp (m₀ τ) (j τ) (𝒦X τ))
    (hconn : HatConn Gp) (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
    (hopt : ∀ τ ∈ 𝒯, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X τ) ∧ MeetsOne (m₀ τ) (j τ) (𝒦X τ) W₀ ∧
        bondCost (scaleW L (m₀ τ) m₁ (j τ)) E₀ = treeLenCovOne (m₀ τ) (j τ) (X τ))
    {κdec κ₀ : ℝ} {Eb : τι → ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : ∀ τ ∈ 𝒯, Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀ τ) ^ d : ℕ) : ℝ)) ≤
      (κ / 2 - 1) / 2)
    (hEb : ∀ τ ∈ 𝒯, 0 ≤ Eb τ) {E : τι → RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ}
    (hEan : ∀ τ ∈ 𝒯, AnalyticOnNhd ℂ (E τ) (XiCRaw (Gj τ) (compWeight L a₁) ν (j τ) b
      (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)))
    (hEbd : ∀ τ ∈ 𝒯, ∀ r ∈ XiCRaw (Gj τ) (compWeight L a₁) ν (j τ) b
      (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      ‖E τ r‖ ≤ Eb τ * Real.exp (-(κdec - 1) * treeLenCovOne (m₀ τ) (j τ) (X τ)))
    {ω : ℂ → ℂ} (hωc : Continuous ω) {R₁ : ℝ} (hR₁ : 1 < R₁)
    (hω : AnalyticOnNhd ℂ ω (ball (0 : ℂ) R₁)) {Mω : ℝ} (hMω : 0 ≤ Mω)
    (hωb : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → ‖ω (t : ℂ)‖ ≤ Mω) {r Rσ : ℝ} (hr : 0 < r) :
    ∃ (T : τι → Set (CTorus d L N₁ m₁ (k + 1)) → (unitPts Gp × Fin N → ℂ) →
        (unitPts Gp × Fin N → ℂ) → ℂ → RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ),
      LocInt (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps) (HatRaysO Gp cψ R₁ Rσ r) Rσ
        (𝒯.biUnion fun τ => polyDom Gp (X₁f τ) (m₀ τ) (j τ) (𝒦X τ))
        (fun Y x₀ w σ Θ => ∑ τ ∈ 𝒯, if Y ∈ polyDom Gp (X₁f τ) (m₀ τ) (j τ) (𝒦X τ) then
          T τ Y x₀ w σ Θ else 0)
        (fun x₀ w σ Θ => ∑ τ ∈ 𝒯, if h : τ ∈ 𝒯 then
          dirTermSrc (hatFun Gp a₁ ν eps hG' cc (flComp (hB τ h) (hF τ h) (E τ))) ω x₀ w σ Θ
          else 0)
        (fun Y => ∑ τ ∈ 𝒯, if Y ∈ polyDom Gp (X₁f τ) (m₀ τ) (j τ) (𝒦X τ) then
          Mω * ((Eb τ * Real.exp (-κ₀ * treeLenCovOne (m₀ τ) (j τ)
          (X τ) - 2 * κdec * treeLenCov Gp (m₀ τ) Y)) / r) else 0)
        (fun Y Θ Θ' => agreeOn (thickSet Gp Y) Θ Θ') (AgHatF Gp hG') := by
  obtain ⟨T, h⟩ := eterms_locInt_hat_dm_of_one_le hb₁ hbC (τι := τι) 𝒯 (ϱ₁ := ϱ₁) (ϱ₂ := ϱ₂) (Gk := Gk) (Gj := Gj) (r₀ := r₀) (δ₃ := δ₃) (X₀ := X₀) (X₁f := X₁f) (j := j) (m₀ := m₀) (X := X) (𝒦X := 𝒦X) (Kc := Kc) (Cx := Cx) (c₂ := c₂) (BG₂ := BG₂) (δ₁ := δ₁) (δfl := δfl) hB hF hk hG hG' cc (cψ := cψ) hcψ hMX (δc := δc) hdm hα hsm hδ₁ hcov hX₁ hconn hrow hopt (κdec := κdec) (κ₀ := κ₀) (Eb := Eb) hκ₀ hκdec hκ h1 hlog hEb (E := E) hEan hEbd (ω := ω) hωc (R₁ := R₁) hR₁ hω (Mω := Mω) hMω hωb (r := r) (Rσ := Rσ) hr
  exact ⟨T, h.loc⟩

/-- **The `δ𝓔'`-part for a finite family of old terms, in the variable `ψ̂`** (hat version of
`eterms_locInt`). -/
theorem eterms_locInt_hat {τι : Type*} [DecidableEq τι] (𝒯 : Finset τι) {ϱ₁ ϱ₂ : τι → ℝ}
    {Gk : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₁ τ)}
    {Gj : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₂ τ)}
    {r₀ δ₃ : ℝ} {X₀ X₁f : τι → Finset (CTorus d L N₁ m₁ (k + 1))} {j m₀ : τι → ℕ}
    {X 𝒦X : τι → Set (CTorus d L N₁ m₁ (k + 1))} {Kc Cx c₂ BG₂ δ₁ δfl : ℝ}
    (hB : ∀ τ ∈ 𝒯, BgSetting N Gp (Gk τ) (Gj τ) a₁ ν c BG κ r₀ eps δ₃ (X₀ τ) (X₁f τ) (j τ))
    (hF : ∀ τ ∈ 𝒯, FlSetting N Gp (Gk τ) Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl (X₁f τ))
    (hk : 1 ≤ k) (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    (hcov : ∀ τ ∈ 𝒯, CovSetup Gp (m₀ τ) (j τ) (X τ) (𝒦X τ))
    (hX₁ : ∀ τ ∈ 𝒯, (↑(X₁f τ) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp (m₀ τ) (j τ) (𝒦X τ))
    (hconn : HatConn Gp) (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
    (hopt : ∀ τ ∈ 𝒯, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X τ) ∧ MeetsOne (m₀ τ) (j τ) (𝒦X τ) W₀ ∧
        bondCost (scaleW L (m₀ τ) m₁ (j τ)) E₀ = treeLenCovOne (m₀ τ) (j τ) (X τ))
    {κdec κ₀ : ℝ} {Eb : τι → ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : ∀ τ ∈ 𝒯, Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀ τ) ^ d : ℕ) : ℝ)) ≤
      (κ / 2 - 1) / 2)
    (hEb : ∀ τ ∈ 𝒯, 0 ≤ Eb τ) {E : τι → RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ}
    (hEan : ∀ τ ∈ 𝒯, AnalyticOnNhd ℂ (E τ) (XiCRaw (Gj τ) (compWeight L a₁) ν (j τ) (scaledC0 d)
      (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)))
    (hEbd : ∀ τ ∈ 𝒯, ∀ r ∈ XiCRaw (Gj τ) (compWeight L a₁) ν (j τ) (scaledC0 d)
      (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      ‖E τ r‖ ≤ Eb τ * Real.exp (-(κdec - 1) * treeLenCovOne (m₀ τ) (j τ) (X τ)))
    {ω : ℂ → ℂ} (hωc : Continuous ω) {R₁ : ℝ} (hR₁ : 1 < R₁)
    (hω : AnalyticOnNhd ℂ ω (ball (0 : ℂ) R₁)) {Mω : ℝ} (hMω : 0 ≤ Mω)
    (hωb : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → ‖ω (t : ℂ)‖ ≤ Mω) {r Rσ : ℝ} (hr : 0 < r) :
    ∃ (T : τι → Set (CTorus d L N₁ m₁ (k + 1)) → (unitPts Gp × Fin N → ℂ) →
        (unitPts Gp × Fin N → ℂ) → ℂ → RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ),
      LocInt (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps) (HatRaysO Gp cψ R₁ Rσ r) Rσ
        (𝒯.biUnion fun τ => polyDom Gp (X₁f τ) (m₀ τ) (j τ) (𝒦X τ))
        (fun Y x₀ w σ Θ => ∑ τ ∈ 𝒯, if Y ∈ polyDom Gp (X₁f τ) (m₀ τ) (j τ) (𝒦X τ) then
          T τ Y x₀ w σ Θ else 0)
        (fun x₀ w σ Θ => ∑ τ ∈ 𝒯, if h : τ ∈ 𝒯 then
          dirTermSrc (hatFun Gp a₁ ν eps hG' cc (flComp (hB τ h) (hF τ h) (E τ))) ω x₀ w σ Θ
          else 0)
        (fun Y => ∑ τ ∈ 𝒯, if Y ∈ polyDom Gp (X₁f τ) (m₀ τ) (j τ) (𝒦X τ) then
          Mω * ((Eb τ * Real.exp (-κ₀ * treeLenCovOne (m₀ τ) (j τ)
          (X τ) - 2 * κdec * treeLenCov Gp (m₀ τ) Y)) / r) else 0)
        (fun Y Θ Θ' => agreeOn (thickSet Gp Y) Θ Θ') (AgHatF Gp hG') :=
  eterms_locInt_hat_of_one_le (one_le_scaledC0 d) le_rfl 𝒯 hB hF hk hG hG' cc hcψ hMX hdm hα hsm hδ₁ hcov hX₁ hconn hrow hopt hκ₀ hκdec hκ h1 hlog hEb hEan hEbd hωc hR₁ hω hMω hωb hr

/-- **The `𝓜`-terms of the source along the fluctuation, in the variable `ψ̂`** (hat version of
`mterms_locInt`). -/
theorem mterms_locInt_hat_dm_of_one_le {b : ℝ} (hb₁ : 1 ≤ b) (hbC : b ≤ scaledC0 d) {τι : Type*} [DecidableEq τι] (𝒯 : Finset τι) {ϱ₁ ϱ₂ : τι → ℝ}
    {Gk : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₁ τ)}
    {Gj : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₂ τ)}
    {r₀ δ₃ : ℝ} {X₀ X₁f : τι → Finset (CTorus d L N₁ m₁ (k + 1))} {j m₀ : τι → ℕ}
    {X 𝒦X : τι → Set (CTorus d L N₁ m₁ (k + 1))} {Kc Cx c₂ BG₂ δ₁ δfl : ℝ}
    (ys : τι → CTorus d L N₁ m₁ (k + 1)) (is : τι → Fin N) (hys : ∀ τ ∈ 𝒯, ys τ ∈ X₁f τ)
    (hB : ∀ τ ∈ 𝒯, BgSetting N Gp (Gk τ) (Gj τ) a₁ ν c BG κ r₀ eps δ₃ (X₀ τ) (X₁f τ) (j τ))
    (hF : ∀ τ ∈ 𝒯, FlSetting N Gp (Gk τ) Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl (X₁f τ))
    (hk : 1 ≤ k) (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    (hcov : ∀ τ ∈ 𝒯, CovSetup Gp (m₀ τ) (j τ) (X τ) (𝒦X τ))
    (hX₁ : ∀ τ ∈ 𝒯, (↑(X₁f τ) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp (m₀ τ) (j τ) (𝒦X τ))
    (hconn : HatConn Gp) (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
    (hopt : ∀ τ ∈ 𝒯, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X τ) ∧ MeetsOne (m₀ τ) (j τ) (𝒦X τ) W₀ ∧
        bondCost (scaleW L (m₀ τ) m₁ (j τ)) E₀ = treeLenCovOne (m₀ τ) (j τ) (X τ))
    {κdec κ₀ : ℝ} {Eb : τι → ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : ∀ τ ∈ 𝒯, Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀ τ) ^ d : ℕ) : ℝ)) ≤
      (κ / 2 - 1) / 2)
    (hEb : ∀ τ ∈ 𝒯, 0 ≤ Eb τ) {E : τι → RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ}
    (hEan : ∀ τ ∈ 𝒯, AnalyticOnNhd ℂ (E τ) (XiCRaw (Gj τ) (compWeight L a₁) ν (j τ) b
      (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)))
    (hEbd : ∀ τ ∈ 𝒯, ∀ r ∈ XiCRaw (Gj τ) (compWeight L a₁) ν (j τ) b
      (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      ‖E τ r‖ ≤ Eb τ * Real.exp (-(κdec - 1) * treeLenCovOne (m₀ τ) (j τ) (X τ)))
    {ω : ℂ → ℂ} (hωc : Continuous ω) {R₁ : ℝ} (hR₁ : 1 < R₁)
    (hω : AnalyticOnNhd ℂ ω (ball (0 : ℂ) R₁)) {Mω : ℝ} (hMω : 0 ≤ Mω)
    (hωb : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → ‖ω (t : ℂ)‖ ≤ Mω) {r Rσ : ℝ} (hr : 0 < r) :
    ∃ (𝒴 : τι → Finset (Set (CTorus d L N₁ m₁ (k + 1))))
      (T : τι → Set (CTorus d L N₁ m₁ (k + 1)) → (unitPts Gp × Fin N → ℂ) →
        (unitPts Gp × Fin N → ℂ) → ℂ → RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ),
      LocIntDm (fun Y => ∃ τ ∈ 𝒯, IsDj (m₀ τ) (k + 1) Y) (id : (unitPts Gp × Fin N → ℂ) → _)
        (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ l1Ball d L N₁ m₁ (k + 1) N)
        (HatRaysO Gp cψ R₁ Rσ r) Rσ
        (𝒯.biUnion 𝒴)
        (fun Y x₀ w σ p => ∑ τ ∈ 𝒯, if Y ∈ 𝒴 τ then p.2 (ys τ) (is τ) * T τ Y x₀ w σ p.1 else 0)
        (fun x₀ w σ p => ∑ τ ∈ 𝒯, if h : τ ∈ 𝒯 then
          p.2 (ys τ) (is τ) * dirTermSrc (hatFun Gp a₁ ν eps hG' cc
            (flComp (hB τ h) (hF τ h) (E τ))) ω x₀ w σ p.1 else 0)
        (fun Y => ∑ τ ∈ 𝒯, if Y ∈ 𝒴 τ then 1 * (Mω * ((Eb τ * Real.exp (-κ₀ * treeLenCovOne
          (m₀ τ) (j τ) (X τ) - 2 * κdec * treeLenCov Gp (m₀ τ) Y)) / r)) else 0)
        (fun Y p p' => agreeOn (thickSet Gp Y) p.1 p'.1 ∧ ∀ x ∈ Y, p.2 x = p'.2 x)
        (AgHatF Gp hG') := by
  classical
  have hex : ∀ τ, ∃ (Ev : Set (CTorus d L N₁ m₁ (k + 1)) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gp × Fin N → ℂ) → ℂ), τ ∈ 𝒯 →
      LocIntDm (fun Y => ∃ τ' ∈ 𝒯, IsDj (m₀ τ') (k + 1) Y) (id : (unitPts Gp × Fin N → ℂ) → _)
        (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ l1Ball d L N₁ m₁ (k + 1) N)
        (HatRaysO Gp cψ R₁ Rσ r) Rσ
        (polymerDomains (fun i : ParIdx Gp (↑(X₁f τ) : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1)
          Gp (m₀ τ) (X1 Gp (m₀ τ) (j τ) (𝒦X τ)))
        (fun Y x₀ w σ p => p.2 (ys τ) (is τ) * dirTerm (Ev Y) ω x₀ w σ p.1)
        (fun x₀ w σ p => if h : τ ∈ 𝒯 then
          p.2 (ys τ) (is τ) * dirTermSrc (hatFun Gp a₁ ν eps hG' cc
            (flComp (hB τ h) (hF τ h) (E τ))) ω x₀ w σ p.1 else 0)
        (fun Y => 1 * (Mω * ((Eb τ * Real.exp (-κ₀ * treeLenCovOne (m₀ τ) (j τ)
          (X τ) - 2 * κdec * treeLenCov Gp (m₀ τ) Y)) / r)))
        (fun Y p p' => agreeOn (thickSet Gp Y) p.1 p'.1 ∧ ∀ x ∈ Y, p.2 x = p'.2 x)
        (AgHatF Gp hG') := by
    intro τ
    by_cases hτ : τ ∈ 𝒯
    · obtain ⟨Ev, hEv⟩ := eterm_locInt_hat_dm_of_one_le hb₁ hbC (hB τ hτ) (hF τ hτ) hk hG hG' cc hcψ hMX hdm hα hsm hδ₁
        (hcov τ hτ) (hX₁ τ hτ) hconn hrow (hopt τ hτ) hκ₀ hκdec hκ h1 (hlog τ hτ) (hEb τ hτ)
        (hEan τ hτ) (hEbd τ hτ) hωc hR₁ hω hMω hωb hr (Rσ := Rσ)
      refine ⟨Ev, fun _ => ?_⟩
      have := (hEv.mono_P (P' := fun Y => ∃ τ' ∈ 𝒯, IsDj (m₀ τ') (k + 1) Y)
        fun Y hY => ⟨τ, hτ, hY⟩).mulAmp (SG := l1Ball d L N₁ m₁ (k + 1) N) (amp := fun g => g (ys τ) (is τ))
        (Ma := 1)
        ((analyticOnNhd_coord (ys τ) (is τ)).mono (Set.subset_univ _))
        (fun g hg => norm_le_of_mem_l1Ball hg (ys τ) (is τ))
        (AgG := fun Y g g' => ∀ x ∈ Y, g x = g' x) (by
          intro Y hY g _ g' _ hag
          have hyY : ys τ ∈ Y := subset_of_mem_polymerDomains hY (by
            rw [← hX₁ τ hτ]; exact hys τ hτ)
          exact congrFun (hag _ hyY) _)
      simpa [hτ] using this
    · exact ⟨fun _ _ => 0, fun h => absurd h hτ⟩
  choose Ev hEv using hex
  exact ⟨fun τ => polymerDomains (fun i : ParIdx Gp (↑(X₁f τ) : Set (CTorus d L N₁ m₁ (k + 1))) =>
      i.1.1) Gp (m₀ τ) (X1 Gp (m₀ τ) (j τ) (𝒦X τ)),
    fun τ Y x₀ w σ Θ => dirTerm (Ev τ Y) ω x₀ w σ Θ, LocIntDm.finsum 𝒯 (fun τ hτ => hEv τ hτ)⟩

/-- **The `𝓜`-terms of the source along the fluctuation, in the variable `ψ̂`** (hat version of
`mterms_locInt`). -/
theorem mterms_locInt_hat_dm {τι : Type*} [DecidableEq τι] (𝒯 : Finset τι) {ϱ₁ ϱ₂ : τι → ℝ}
    {Gk : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₁ τ)}
    {Gj : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₂ τ)}
    {r₀ δ₃ : ℝ} {X₀ X₁f : τι → Finset (CTorus d L N₁ m₁ (k + 1))} {j m₀ : τι → ℕ}
    {X 𝒦X : τι → Set (CTorus d L N₁ m₁ (k + 1))} {Kc Cx c₂ BG₂ δ₁ δfl : ℝ}
    (ys : τι → CTorus d L N₁ m₁ (k + 1)) (is : τι → Fin N) (hys : ∀ τ ∈ 𝒯, ys τ ∈ X₁f τ)
    (hB : ∀ τ ∈ 𝒯, BgSetting N Gp (Gk τ) (Gj τ) a₁ ν c BG κ r₀ eps δ₃ (X₀ τ) (X₁f τ) (j τ))
    (hF : ∀ τ ∈ 𝒯, FlSetting N Gp (Gk τ) Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl (X₁f τ))
    (hk : 1 ≤ k) (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    (hcov : ∀ τ ∈ 𝒯, CovSetup Gp (m₀ τ) (j τ) (X τ) (𝒦X τ))
    (hX₁ : ∀ τ ∈ 𝒯, (↑(X₁f τ) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp (m₀ τ) (j τ) (𝒦X τ))
    (hconn : HatConn Gp) (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
    (hopt : ∀ τ ∈ 𝒯, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X τ) ∧ MeetsOne (m₀ τ) (j τ) (𝒦X τ) W₀ ∧
        bondCost (scaleW L (m₀ τ) m₁ (j τ)) E₀ = treeLenCovOne (m₀ τ) (j τ) (X τ))
    {κdec κ₀ : ℝ} {Eb : τι → ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : ∀ τ ∈ 𝒯, Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀ τ) ^ d : ℕ) : ℝ)) ≤
      (κ / 2 - 1) / 2)
    (hEb : ∀ τ ∈ 𝒯, 0 ≤ Eb τ) {E : τι → RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ}
    (hEan : ∀ τ ∈ 𝒯, AnalyticOnNhd ℂ (E τ) (XiCRaw (Gj τ) (compWeight L a₁) ν (j τ) (scaledC0 d)
      (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)))
    (hEbd : ∀ τ ∈ 𝒯, ∀ r ∈ XiCRaw (Gj τ) (compWeight L a₁) ν (j τ) (scaledC0 d)
      (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      ‖E τ r‖ ≤ Eb τ * Real.exp (-(κdec - 1) * treeLenCovOne (m₀ τ) (j τ) (X τ)))
    {ω : ℂ → ℂ} (hωc : Continuous ω) {R₁ : ℝ} (hR₁ : 1 < R₁)
    (hω : AnalyticOnNhd ℂ ω (ball (0 : ℂ) R₁)) {Mω : ℝ} (hMω : 0 ≤ Mω)
    (hωb : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → ‖ω (t : ℂ)‖ ≤ Mω) {r Rσ : ℝ} (hr : 0 < r) :
    ∃ (𝒴 : τι → Finset (Set (CTorus d L N₁ m₁ (k + 1))))
      (T : τι → Set (CTorus d L N₁ m₁ (k + 1)) → (unitPts Gp × Fin N → ℂ) →
        (unitPts Gp × Fin N → ℂ) → ℂ → RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ),
      LocIntDm (fun Y => ∃ τ ∈ 𝒯, IsDj (m₀ τ) (k + 1) Y) (id : (unitPts Gp × Fin N → ℂ) → _)
        (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ l1Ball d L N₁ m₁ (k + 1) N)
        (HatRaysO Gp cψ R₁ Rσ r) Rσ
        (𝒯.biUnion 𝒴)
        (fun Y x₀ w σ p => ∑ τ ∈ 𝒯, if Y ∈ 𝒴 τ then p.2 (ys τ) (is τ) * T τ Y x₀ w σ p.1 else 0)
        (fun x₀ w σ p => ∑ τ ∈ 𝒯, if h : τ ∈ 𝒯 then
          p.2 (ys τ) (is τ) * dirTermSrc (hatFun Gp a₁ ν eps hG' cc
            (flComp (hB τ h) (hF τ h) (E τ))) ω x₀ w σ p.1 else 0)
        (fun Y => ∑ τ ∈ 𝒯, if Y ∈ 𝒴 τ then 1 * (Mω * ((Eb τ * Real.exp (-κ₀ * treeLenCovOne
          (m₀ τ) (j τ) (X τ) - 2 * κdec * treeLenCov Gp (m₀ τ) Y)) / r)) else 0)
        (fun Y p p' => agreeOn (thickSet Gp Y) p.1 p'.1 ∧ ∀ x ∈ Y, p.2 x = p'.2 x)
        (AgHatF Gp hG') :=
  mterms_locInt_hat_dm_of_one_le (one_le_scaledC0 d) le_rfl 𝒯 ys is hys hB hF hk hG hG' cc hcψ hMX hdm hα hsm hδ₁ hcov hX₁ hconn hrow hopt hκ₀ hκdec hκ h1 hlog hEb hEan hEbd hωc hR₁ hω hMω hωb hr

/-- **The `𝓜`-terms of the source along the fluctuation, in the variable `ψ̂`** (hat version of
`mterms_locInt`). -/
theorem mterms_locInt_hat_of_one_le {b : ℝ} (hb₁ : 1 ≤ b) (hbC : b ≤ scaledC0 d) {τι : Type*} [DecidableEq τι] (𝒯 : Finset τι) {ϱ₁ ϱ₂ : τι → ℝ}
    {Gk : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₁ τ)}
    {Gj : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₂ τ)}
    {r₀ δ₃ : ℝ} {X₀ X₁f : τι → Finset (CTorus d L N₁ m₁ (k + 1))} {j m₀ : τι → ℕ}
    {X 𝒦X : τι → Set (CTorus d L N₁ m₁ (k + 1))} {Kc Cx c₂ BG₂ δ₁ δfl : ℝ}
    (ys : τι → CTorus d L N₁ m₁ (k + 1)) (is : τι → Fin N) (hys : ∀ τ ∈ 𝒯, ys τ ∈ X₁f τ)
    (hB : ∀ τ ∈ 𝒯, BgSetting N Gp (Gk τ) (Gj τ) a₁ ν c BG κ r₀ eps δ₃ (X₀ τ) (X₁f τ) (j τ))
    (hF : ∀ τ ∈ 𝒯, FlSetting N Gp (Gk τ) Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl (X₁f τ))
    (hk : 1 ≤ k) (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    (hcov : ∀ τ ∈ 𝒯, CovSetup Gp (m₀ τ) (j τ) (X τ) (𝒦X τ))
    (hX₁ : ∀ τ ∈ 𝒯, (↑(X₁f τ) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp (m₀ τ) (j τ) (𝒦X τ))
    (hconn : HatConn Gp) (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
    (hopt : ∀ τ ∈ 𝒯, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X τ) ∧ MeetsOne (m₀ τ) (j τ) (𝒦X τ) W₀ ∧
        bondCost (scaleW L (m₀ τ) m₁ (j τ)) E₀ = treeLenCovOne (m₀ τ) (j τ) (X τ))
    {κdec κ₀ : ℝ} {Eb : τι → ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : ∀ τ ∈ 𝒯, Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀ τ) ^ d : ℕ) : ℝ)) ≤
      (κ / 2 - 1) / 2)
    (hEb : ∀ τ ∈ 𝒯, 0 ≤ Eb τ) {E : τι → RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ}
    (hEan : ∀ τ ∈ 𝒯, AnalyticOnNhd ℂ (E τ) (XiCRaw (Gj τ) (compWeight L a₁) ν (j τ) b
      (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)))
    (hEbd : ∀ τ ∈ 𝒯, ∀ r ∈ XiCRaw (Gj τ) (compWeight L a₁) ν (j τ) b
      (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      ‖E τ r‖ ≤ Eb τ * Real.exp (-(κdec - 1) * treeLenCovOne (m₀ τ) (j τ) (X τ)))
    {ω : ℂ → ℂ} (hωc : Continuous ω) {R₁ : ℝ} (hR₁ : 1 < R₁)
    (hω : AnalyticOnNhd ℂ ω (ball (0 : ℂ) R₁)) {Mω : ℝ} (hMω : 0 ≤ Mω)
    (hωb : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → ‖ω (t : ℂ)‖ ≤ Mω) {r Rσ : ℝ} (hr : 0 < r) :
    ∃ (𝒴 : τι → Finset (Set (CTorus d L N₁ m₁ (k + 1))))
      (T : τι → Set (CTorus d L N₁ m₁ (k + 1)) → (unitPts Gp × Fin N → ℂ) →
        (unitPts Gp × Fin N → ℂ) → ℂ → RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ),
      LocInt (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ l1Ball d L N₁ m₁ (k + 1) N)
        (HatRaysO Gp cψ R₁ Rσ r) Rσ
        (𝒯.biUnion 𝒴)
        (fun Y x₀ w σ p => ∑ τ ∈ 𝒯, if Y ∈ 𝒴 τ then p.2 (ys τ) (is τ) * T τ Y x₀ w σ p.1 else 0)
        (fun x₀ w σ p => ∑ τ ∈ 𝒯, if h : τ ∈ 𝒯 then
          p.2 (ys τ) (is τ) * dirTermSrc (hatFun Gp a₁ ν eps hG' cc
            (flComp (hB τ h) (hF τ h) (E τ))) ω x₀ w σ p.1 else 0)
        (fun Y => ∑ τ ∈ 𝒯, if Y ∈ 𝒴 τ then 1 * (Mω * ((Eb τ * Real.exp (-κ₀ * treeLenCovOne
          (m₀ τ) (j τ) (X τ) - 2 * κdec * treeLenCov Gp (m₀ τ) Y)) / r)) else 0)
        (fun Y p p' => agreeOn (thickSet Gp Y) p.1 p'.1 ∧ ∀ x ∈ Y, p.2 x = p'.2 x)
        (AgHatF Gp hG') := by
  obtain ⟨a, T, h⟩ := mterms_locInt_hat_dm_of_one_le hb₁ hbC (τι := τι) 𝒯 (ϱ₁ := ϱ₁) (ϱ₂ := ϱ₂) (Gk := Gk) (Gj := Gj) (r₀ := r₀) (δ₃ := δ₃) (X₀ := X₀) (X₁f := X₁f) (j := j) (m₀ := m₀) (X := X) (𝒦X := 𝒦X) (Kc := Kc) (Cx := Cx) (c₂ := c₂) (BG₂ := BG₂) (δ₁ := δ₁) (δfl := δfl) ys is hys hB hF hk hG hG' cc (cψ := cψ) hcψ hMX (δc := δc) hdm hα hsm hδ₁ hcov hX₁ hconn hrow hopt (κdec := κdec) (κ₀ := κ₀) (Eb := Eb) hκ₀ hκdec hκ h1 hlog hEb (E := E) hEan hEbd (ω := ω) hωc (R₁ := R₁) hR₁ hω (Mω := Mω) hMω hωb (r := r) (Rσ := Rσ) hr
  exact ⟨a, T, h.loc⟩

/-- **The `𝓜`-terms of the source along the fluctuation, in the variable `ψ̂`** (hat version of
`mterms_locInt`). -/
theorem mterms_locInt_hat {τι : Type*} [DecidableEq τι] (𝒯 : Finset τι) {ϱ₁ ϱ₂ : τι → ℝ}
    {Gk : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₁ τ)}
    {Gj : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₂ τ)}
    {r₀ δ₃ : ℝ} {X₀ X₁f : τι → Finset (CTorus d L N₁ m₁ (k + 1))} {j m₀ : τι → ℕ}
    {X 𝒦X : τι → Set (CTorus d L N₁ m₁ (k + 1))} {Kc Cx c₂ BG₂ δ₁ δfl : ℝ}
    (ys : τι → CTorus d L N₁ m₁ (k + 1)) (is : τι → Fin N) (hys : ∀ τ ∈ 𝒯, ys τ ∈ X₁f τ)
    (hB : ∀ τ ∈ 𝒯, BgSetting N Gp (Gk τ) (Gj τ) a₁ ν c BG κ r₀ eps δ₃ (X₀ τ) (X₁f τ) (j τ))
    (hF : ∀ τ ∈ 𝒯, FlSetting N Gp (Gk τ) Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl (X₁f τ))
    (hk : 1 ≤ k) (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    (hcov : ∀ τ ∈ 𝒯, CovSetup Gp (m₀ τ) (j τ) (X τ) (𝒦X τ))
    (hX₁ : ∀ τ ∈ 𝒯, (↑(X₁f τ) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp (m₀ τ) (j τ) (𝒦X τ))
    (hconn : HatConn Gp) (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
    (hopt : ∀ τ ∈ 𝒯, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X τ) ∧ MeetsOne (m₀ τ) (j τ) (𝒦X τ) W₀ ∧
        bondCost (scaleW L (m₀ τ) m₁ (j τ)) E₀ = treeLenCovOne (m₀ τ) (j τ) (X τ))
    {κdec κ₀ : ℝ} {Eb : τι → ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : ∀ τ ∈ 𝒯, Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀ τ) ^ d : ℕ) : ℝ)) ≤
      (κ / 2 - 1) / 2)
    (hEb : ∀ τ ∈ 𝒯, 0 ≤ Eb τ) {E : τι → RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ}
    (hEan : ∀ τ ∈ 𝒯, AnalyticOnNhd ℂ (E τ) (XiCRaw (Gj τ) (compWeight L a₁) ν (j τ) (scaledC0 d)
      (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)))
    (hEbd : ∀ τ ∈ 𝒯, ∀ r ∈ XiCRaw (Gj τ) (compWeight L a₁) ν (j τ) (scaledC0 d)
      (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      ‖E τ r‖ ≤ Eb τ * Real.exp (-(κdec - 1) * treeLenCovOne (m₀ τ) (j τ) (X τ)))
    {ω : ℂ → ℂ} (hωc : Continuous ω) {R₁ : ℝ} (hR₁ : 1 < R₁)
    (hω : AnalyticOnNhd ℂ ω (ball (0 : ℂ) R₁)) {Mω : ℝ} (hMω : 0 ≤ Mω)
    (hωb : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → ‖ω (t : ℂ)‖ ≤ Mω) {r Rσ : ℝ} (hr : 0 < r) :
    ∃ (𝒴 : τι → Finset (Set (CTorus d L N₁ m₁ (k + 1))))
      (T : τι → Set (CTorus d L N₁ m₁ (k + 1)) → (unitPts Gp × Fin N → ℂ) →
        (unitPts Gp × Fin N → ℂ) → ℂ → RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ),
      LocInt (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ l1Ball d L N₁ m₁ (k + 1) N)
        (HatRaysO Gp cψ R₁ Rσ r) Rσ
        (𝒯.biUnion 𝒴)
        (fun Y x₀ w σ p => ∑ τ ∈ 𝒯, if Y ∈ 𝒴 τ then p.2 (ys τ) (is τ) * T τ Y x₀ w σ p.1 else 0)
        (fun x₀ w σ p => ∑ τ ∈ 𝒯, if h : τ ∈ 𝒯 then
          p.2 (ys τ) (is τ) * dirTermSrc (hatFun Gp a₁ ν eps hG' cc
            (flComp (hB τ h) (hF τ h) (E τ))) ω x₀ w σ p.1 else 0)
        (fun Y => ∑ τ ∈ 𝒯, if Y ∈ 𝒴 τ then 1 * (Mω * ((Eb τ * Real.exp (-κ₀ * treeLenCovOne
          (m₀ τ) (j τ) (X τ) - 2 * κdec * treeLenCov Gp (m₀ τ) Y)) / r)) else 0)
        (fun Y p p' => agreeOn (thickSet Gp Y) p.1 p'.1 ∧ ∀ x ∈ Y, p.2 x = p'.2 x)
        (AgHatF Gp hG') :=
  mterms_locInt_hat_of_one_le (one_le_scaledC0 d) le_rfl 𝒯 ys is hys hB hF hk hG hG' cc hcψ hMX hdm hα hsm hδ₁ hcov hX₁ hconn hrow hopt hκ₀ hκdec hκ h1 hlog hEb hEan hEbd hωc hR₁ hω hMω hωb hr

end EFamily

end Balaban.Localization
