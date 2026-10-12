/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.I5Fluct
public import Balaban.Fluctuation.InteractionETerm
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Lemma AE for functionals of the decoupled fluctuation objects (LOCALIZATION.md (V3))

Theorem I-5 with `ψ'` (`i5_fluct`) expands the composite `E(ψ(𝔹_j, 𝔹_k; Θ, ψ'))`, a function of the
raw data of a *local* generating set.  The interaction potential `V^{(k)}` and the source
`⟨g, δφ_k⟩` are functions of the decoupled objects themselves: the background field `φ_{k+1}(s)`
(Theorem I-4b), the fluctuation field `δφ(s)` (Theorem I-4a, mode P) and the data.  By LOC (V3)
Lemma AE applies to every `F(s; u) = Φ(extended objects)` with (AE1) and (AE2).  This file proves
that: `i5_functional` expands `Φ(φ_{k+1}(s), δφ(s), Θ, ψ')` at `s = 1` over the domains `Y ⊃ X₁`,
for every `Φ` that is analytic, bounded and local on the set `FlReal` of realizable triples.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Analysis Finset Matrix
  Balaban.Fluctuation

section Core

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱ₁ ϱ₂ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {Gk : GeneratingSet d L (N₁ * L ^ m₁) K ϱ₁}
variable {Gj : GeneratingSet d L (N₁ * L ^ m₁) K ϱ₂} {Hm : GeneratingSet d L (N₁ * L ^ m₁) K ϱm}
variable {a₁ ν c BG κ r₀ eps δ₃ : ℝ} {X₀ X₁f : Finset (CTorus d L N₁ m₁ K)} {j : ℕ}
variable {Kc Cx c₂ BG₂ δ₁ δfl : ℝ}

variable (N Gp Hm) in
/-- **The part of the hypotheses of `i5_fluct` that concerns the pair `(Gp, Hm)` only**: the
decoupled background (I-4b) for `Gp`, the decoupled fluctuation problem (I-4a, mode P) for the
pair `(coverOf Gp, Hm)`, and the numerical conditions of the strict data.  The generating sets
`𝔹_k(X)`, `𝔹_j(X)` of a local term do not enter. -/
structure FlCore (a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ) : Prop where
  hS : DecSpecs d L c BG
  Sp : DGSetting Gp (compWeight L a₁) ν
  HBp : BgHyp d L K ϱ (compWeight L a₁) ν
  hκ : 0 < κ
  hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁
  eps_pos : 0 < eps
  small1 : (4 * d + 6) * ((2 * d + 1) * eps) ≤ 1
  c7le : xiC1 d * eps ≤ c7 d L N BG κ
  hS2 : Dec2.DecSpecs d L Kc Cx c₂ BG₂
  SM : Dec2.FootLocal (coverOf Gp) Hm (compWeight L a₁) ν Kc Cx
  hM2 : c₂ * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁
  hPmp : Precedes Hm Gp
  δ₁_pos : 0 < δ₁
  δ₁_le : δ₁ ≤ deltaStar' d L N (famConst d L BG₂ κ) (gamma1 d / 8)
  B_le : 2 * (K4 d L N BG κ * (xiC1 d * eps)) ≤
    deltaStar' d L N (famConst d L BG₂ κ) (gamma1 d / 8)
  B_one : 2 * (K4 d L N BG κ * (xiC1 d * eps)) ≤ 1
  phi_lt : (3 + K4 d L N BG κ) * (xiC1 d * eps) < 1 / 2

/-- The pair-only hypotheses follow from those of `i5_fluct`. -/
theorem flCore_of (hB : BgSetting N Gp Gk Gj a₁ ν c BG κ r₀ eps δ₃ X₀ X₁f j)
    (hF : FlSetting N Gp Gk Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl X₁f) :
    FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ :=
  { hS := hB.hS, Sp := hB.Sp, HBp := hB.HBp, hκ := hB.hκ, hM := hB.hM,
    eps_pos := hB.num.eps_pos, small1 := hB.num.small1, c7le := hB.num.c7le,
    hS2 := hF.hS2, SM := hF.SM, hM2 := hF.hM2, hPmp := hF.hPmp, δ₁_pos := hF.num.δ₁_pos,
    δ₁_le := hF.num.δ₁_le, B_le := hF.num.B_le, B_one := hF.num.B_one,
    phi_lt := hF.num.phi_lt }

variable (Gp X₁f) in
/-- **The margin of a set of sites against the cover** (LOCALIZATION.md, proof of Lemma DL: "every
centre `z` with `C_z ∩ X₀ ≠ ∅` has `□̂_z` inside `X₁`, hence `𝒬(z) ∩ 𝔓 = ∅` and `z ∈ Z_Y`"): each
site `x` of `Z_α ∩ Ω₁` lies in the interaction box of a centre `z` whose thickened box lies in `X₁`
and which interacts with no parameter cube.  It makes the multiplier `α_{k+1}(s)` at `x` depend
on the decoupling parameters only through the cubes of the polymer (Theorem I-4b (iv)). -/
def BlockMargin (Zα : Set (CTorus d L N₁ m₁ K)) : Prop :=
  ∀ x ∈ Zα, x ∈ Gp.Ω 1 → ∃ z ∈ (coverOf Gp).cubeIdx, x ∈ intBox z ∧
    (∀ P ∈ (coverOf Gp).Qset z, P ∉ (coverOf Gp).parCubes X₁f) ∧ SubI Gp (hatBox z) X₁f

variable (Gp Hm a₁ ν BG BG₂ κ eps δ₁ X₁f) in
/-- **The realizable triples** `(φ_{k+1}(s), δφ(s), (Θ, ψ'))`: `Θ = rawOf D` for a datum
`D ∈ Ξ^c_K(𝔹_{k+1}; 1, ε')`, `ψ'` in the ball of fluctuations, `s` in the polydisc with `s = 1` off
the parameter cubes, `(φ_{k+1}(s), α_{k+1}(s))` the decoupled background of `D`, and `δφ(s)` the
fluctuation field (a fixed point `δα(s)` of the mode-P equation in the ball `c₆`). -/
def FlReal : Set (((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) × (Hm.Ω 1 × Fin N → ℂ) ×
    (RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ))) :=
  {t | ∃ (s : DecParams Gp) (D : BgData Gp N) (ψ' : CTorus d L N₁ m₁ K → Fin N → ℂ)
      (δα : Hm.Ω 1 → ℂ),
    (∀ P, ‖s P‖ < Real.exp κ) ∧
    (∀ (P : ℕ × CTorus d L N₁ m₁ K) (hP : P ∈ cubeIdx Gp), P ∉ parCubes Gp X₁f → s ⟨P, hP⟩ = 1) ∧
    XiCData Gp (compWeight L a₁) ν K 1 eps D ∧ ψ' ∈ FlBall Hm δ₁ ∧
    IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D t.1.1 t.1.2 ∧
    t.2.2 = (rawOf D, ψ') ∧
    t.2.1 = dphi Hm (Dec2.decG (coverOf Gp) Hm (compWeight L a₁) ν s)
      (flEdat Gp Hm t.1 D.Ψ ψ').2.1 (flEdat Gp Hm t.1 D.Ψ ψ').1
      (pertSource Hm (compWeight L a₁) (flEdat Gp Hm t.1 D.Ψ ψ').2.2.1
        (flEdat Gp Hm t.1 D.Ψ ψ').2.2.2) δα ∧
    Dec2.DecFixed (coverOf Gp) Hm (compWeight L a₁) ν s false
      (flEdat Gp Hm t.1 D.Ψ ψ').2.1 (flEdat Gp Hm t.1 D.Ψ ψ').1
      (pertSource Hm (compWeight L a₁) (flEdat Gp Hm t.1 D.Ψ ψ').2.2.1
        (flEdat Gp Hm t.1 D.Ψ ψ').2.2.2) δα ∧
    Small Hm δα (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
    Small Hm δα (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
    SupBounds Hm t.2.1 (cK2' d L N (famConst d L BG₂ κ) * δ₁)}

section Facts

/-- **The point facts for a functional of the decoupled objects**: the decoupled background and
fluctuation at a realizable point exist, are given by `F₁` and `Sol`, satisfy the strict
inequalities, and the triple lies in `FlReal`. -/
theorem point_facts_core (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    {F₁ : DecParams Gp × RawData d L (N₁ * L ^ m₁) K N → (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    (hF₁ : ∀ (s : DecParams Gp) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
        (α : Gp.Ω 1 → ℂ), IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
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
    {s : DecParams Gp} (hs : ∀ P, ‖s P‖ < Real.exp κ)
    (hs1 : ∀ (P : ℕ × CTorus d L N₁ m₁ K) (hP : P ∈ cubeIdx Gp), P ∉ parCubes Gp X₁f →
      s ⟨P, hP⟩ = 1)
    {D : BgData Gp N} (hD : XiCData Gp (compWeight L a₁) ν K 1 eps D)
    {ψ' : CTorus d L N₁ m₁ K → Fin N → ℂ} (hψ : ψ' ∈ FlBall Hm δ₁) :
    ∃ (φ : Gp.Ω 1 × Fin N → ℂ) (α : Gp.Ω 1 → ℂ) (δφ : Hm.Ω 1 × Fin N → ℂ) (δα : Hm.Ω 1 → ℂ),
      IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α ∧ F₁ (s, rawOf D) = (φ, α) ∧
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁
        (flEdat Gp Hm (φ, α) D.Ψ ψ') ∧
      Sol (s, flEdat Gp Hm (φ, α) D.Ψ ψ') = (δφ, δα) ∧
      ((φ, α), δφ, (rawOf D, ψ')) ∈ FlReal Gp Hm a₁ ν BG κ eps X₁f BG₂ δ₁ := by
  classical
  have hd0 : 0 < d := by have := hC.HBp.hd; omega
  have hc1 := one_le_xiC1 d
  have hε := hC.eps_pos
  have hδ0 : 0 < xiC1 d * eps := by positivity
  have hDom := xiCData_inDomainC hC.HBp hC.small1 hD
  have hδ1 : xiC1 d * eps ≤ c7 d L N BG κ := hC.c7le
  have hδ0' : xiC1 d * eps ≤ bgC0 d L N := hδ1.trans ((c7_le_bgC1 d L N BG κ).trans
    (bgC1_le_bgC0 d L N hd0))
  have hνε : ν * ((L : ℝ) ^ K) ^ 2 * (xiC1 d * eps) ^ 2 ≤ (xiC1 d * eps) ^ 2 := by
    have := hC.HBp.massLe; nlinarith [sq_nonneg (xiC1 d * eps)]
  have hU : InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D :=
    inUnionDomainC_of_inDomainC hC.HBp hδ0 hδ0' hδ1 hDom
  have hsle : ∀ P, ‖s P‖ ≤ Real.exp κ := fun P => (hs P).le
  obtain ⟨φ, α, hI, hu', -, -, hbb⟩ := i4b_exists_unique hC.hS hC.Sp hC.HBp hC.hκ.le hC.hM
    hsle hδ0 le_rfl hδ0' hδ1 hνε hDom
  have hFeq : F₁ (s, rawOf D) = (φ, α) := hF₁ s D hs hU φ α hI
  have hK4 : 0 < K4 d L N BG κ := K4_pos hC.hS.fam.2.1 hd0
  have hB4 : 0 < K4 d L N BG κ * (xiC1 d * eps) := mul_pos hK4 hδ0
  have hphi : ∀ x : Gp.Ω 1, vn (fun i => φ (x, i)) < 3 / 2 := by
    intro x
    have hxd : (x : CTorus d L N₁ m₁ K) ∈ dataSites Gp := (mem_dataSites Gp).2 (Or.inl x.2)
    have h1 := vn_Psi_lt hδ0.le hDom hxd
    have h2 := vn_le_sub_add (fun i => φ (x, i)) (D.Ψ x)
    have h3 := hbb.val x
    have h4 := hC.phi_lt
    nlinarith
  have hstrict : StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁
      (flEdat Gp Hm (φ, α) D.Ψ ψ') :=
    flEdat_strict hC.hPmp hbb hB4 hphi hC.δ₁_pos hψ
  obtain ⟨hfld, hfix, hs6, hsK, hdp, -⟩ := hSol (s, flEdat Gp Hm (φ, α) D.Ψ ψ') hs hstrict
  refine ⟨φ, α, (Sol (s, flEdat Gp Hm (φ, α) D.Ψ ψ')).1, (Sol (s, flEdat Gp Hm (φ, α) D.Ψ ψ')).2,
    hI, hFeq, hstrict, rfl, ?_⟩
  exact ⟨s, D, ψ', (Sol (s, flEdat Gp Hm (φ, α) D.Ψ ψ')).2, hs, hs1, hD, hψ, hI, rfl,
    hfld, hfix, hs6, hsK, hdp⟩

end Facts

section Tail

variable {m₀ : ℕ} {X 𝒦X : Set (CTorus d L N₁ m₁ K)}

/-- **Lemma AE and the resummation, for an arbitrary set of fluctuations** (the common tail of
`i5_functional` and `i5_functional_taylor`): a function `Fn(u, s)` of the data `u = (Θ, z)`,
`z ∈ B'`, and the decoupling parameters, analytic and bounded on the polydisc and local, expands
at `s = 1` over the domains `Y ⊃ X₁` with the bound `Eb e^{-κ₀ Δ - 2 κ d̃^{cov}_{k+1}(Y)}`. -/
theorem expansion_of_AE (hd : 3 ≤ d) (hL : 3 ≤ L) (hκpos : 0 < κ)
    (hcov : CovSetup Gp m₀ j X 𝒦X)
    (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ K)) = X1 Gp m₀ j 𝒦X)
    (hopt : ∃ (W₀ : Finset (CTorus d L N₁ m₁ K))
      (E₀ : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K)),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X) ∧ MeetsOne m₀ j 𝒦X W₀ ∧
        bondCost (scaleW L m₀ m₁ j) E₀ = treeLenCovOne m₀ j X)
    {κdec κ₀ Eb : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hEb : 0 ≤ Eb) {B' : Set (CTorus d L N₁ m₁ K → Fin N → ℂ)}
    {FF : RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ) →
      (ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) → ℂ) → ℂ}
    (hana : AnalyticOnNhd ℂ (fun p : (RawData d L (N₁ * L ^ m₁) K N ×
        (CTorus d L N₁ m₁ K → Fin N → ℂ)) ×
        (ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) → ℂ) => FF p.1 p.2)
      ((XiCRaw Gp (compWeight L a₁) ν K 1 eps ×ˢ B') ×ˢ
        polydisc (0 : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) → ℂ) (fun _ => Real.exp κ)))
    (hbd : ∀ u ∈ XiCRaw (N := N) Gp (compWeight L a₁) ν K 1 eps ×ˢ B',
      ∀ s ∈ polydisc (0 : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) → ℂ)
        (fun _ => Real.exp κ),
      ‖FF u s‖ ≤ Eb * Real.exp (-(κdec - 1) * treeLenCovOne m₀ j X))
    (hloc : LocalityAEOn (Real.exp κ) (XiCRaw Gp (compWeight L a₁) ν K 1 eps ×ˢ B')
      (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) => Pset m₁ i.1.1)
      (compY (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) => i.1.1)
        (↑X₁f : Set (CTorus d L N₁ m₁ K)))
      (fun C u u' => agreeOn (thickSet Gp (compY
        (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) => i.1.1)
        (↑X₁f : Set (CTorus d L N₁ m₁ K)) C)) u.1 u'.1 ∧
        ∀ y ∈ psiThick (compY
          (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) => i.1.1)
          (↑X₁f : Set (CTorus d L N₁ m₁ K)) C), u.2 y = u'.2 y) FF) :
    ∃ Ev : Set (CTorus d L N₁ m₁ K) →
        RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ) → ℂ,
      (∀ u ∈ XiCRaw Gp (compWeight L a₁) ν K 1 eps ×ˢ B',
        FF u 1 = ∑ Y ∈ polymerDomains
          (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) => i.1.1) Gp m₀
          (X1 Gp m₀ j 𝒦X), Ev Y u) ∧
      (∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν K 1 eps ×ˢ B',
        ∀ u' ∈ XiCRaw Gp (compWeight L a₁) ν K 1 eps ×ˢ B',
        agreeOn (thickSet Gp Y) u.1 u'.1 → (∀ y ∈ psiThick Y, u.2 y = u'.2 y) →
        Ev Y u = Ev Y u') ∧
      (∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν K 1 eps ×ˢ B',
        ‖Ev Y u‖ ≤ Eb * Real.exp (-κ₀ * treeLenCovOne m₀ j X - 2 * κdec * treeLenCov Gp m₀ Y)) ∧
      (∀ Y, AnalyticOnNhd ℂ (Ev Y) (XiCRaw Gp (compWeight L a₁) ν K 1 eps ×ˢ B')) := by
  classical
  have hc : ∀ i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)), (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) => i.1.1) i ∈ cubeIdx Gp := fun i => i.1.2
  have hcinj : Function.Injective (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) => i.1.1) := fun i i' h => Subtype.ext (Subtype.ext h)
  have hdisj : ∀ i, Disjoint (Pset m₁ ((fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) => i.1.1) i)) (X1 Gp m₀ j 𝒦X) := fun i => hX₁ ▸ i.2
  have hrefl : ∀ (C : Finset (ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)))) (u : RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ)), u ∈ XiCRaw (N := N) Gp (compWeight L a₁) ν K 1 eps ×ˢ B' →
      (fun C u u' => agreeOn (N := N) (thickSet Gp (compY (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) => i.1.1) (↑X₁f : Set (CTorus d L N₁ m₁ K)) C))
        u.1 u'.1 ∧ ∀ y ∈ psiThick (compY (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) => i.1.1) (↑X₁f : Set (CTorus d L N₁ m₁ K)) C), u.2 y = u'.2 y)
        C u u := fun C u _ => ⟨agreeOn_refl _ u.1, fun _ _ => rfl⟩
  have hlink : ∀ (C : Finset (ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)))) (u u' : RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ)), (agreeOn (N := N) (thickSet Gp (Ysites Gp m₀ (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) => i.1.1) (X1 Gp m₀ j 𝒦X) C)) u.1 u'.1 ∧
        ∀ y ∈ psiThick (Ysites Gp m₀ (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) => i.1.1) (X1 Gp m₀ j 𝒦X) C), u.2 y = u'.2 y) →
      (agreeOn (N := N) (thickSet Gp (compY (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) => i.1.1) (↑X₁f : Set (CTorus d L N₁ m₁ K)) C)) u.1 u'.1 ∧
        ∀ y ∈ psiThick (compY (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) => i.1.1) (↑X₁f : Set (CTorus d L N₁ m₁ K)) C), u.2 y = u'.2 y) := by
    intro C u u' h
    have hsub : compY (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) => i.1.1) (↑X₁f : Set (CTorus d L N₁ m₁ K)) C ⊆
        Ysites Gp m₀ (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) => i.1.1) (X1 Gp m₀ j 𝒦X) C := by
      have e1 : compY (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) => i.1.1) (↑X₁f : Set (CTorus d L N₁ m₁ K)) C =
          compY (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) => i.1.1) (X1 Gp m₀ j 𝒦X) C :=
        congrArg (fun S => compY (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) => i.1.1) S C) hX₁
      rw [e1]; exact compY_subset_Ysites hcov.hU hcov.hN hc _ C
    exact ⟨agreeOn_mono (thickSet_mono hsub) h.1, fun y hy => h.2 y (psiThick_mono hsub hy)⟩
  have hloc' : LocalityAEOn (Real.exp κ)
      (XiCRaw (N := N) Gp (compWeight L a₁) ν K 1 eps ×ˢ B')
      (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) => Pset m₁ ((fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) => i.1.1) i)) (compY (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) => i.1.1) (X1 Gp m₀ j 𝒦X))
      (fun C u u' => agreeOn (N := N) (thickSet Gp (compY (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) => i.1.1) (↑X₁f : Set (CTorus d L N₁ m₁ K)) C))
        u.1 u'.1 ∧ ∀ y ∈ psiThick (compY (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) => i.1.1) (↑X₁f : Set (CTorus d L N₁ m₁ K)) C), u.2 y = u'.2 y)
      FF := by
    have e2 : compY (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) => i.1.1) (X1 Gp m₀ j 𝒦X) =
        compY (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) => i.1.1) (↑X₁f : Set (CTorus d L N₁ m₁ K)) :=
      congrArg (fun S => compY (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) => i.1.1) S) hX₁.symm
    rw [e2]; exact hloc
  obtain ⟨hsum, hlocY, hbound, hanY⟩ := localization_expansion (c := (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) => i.1.1)) hcov hd hL hc hcinj hdisj
    hopt hκ₀ hκdec hκ h1 hlog hEb
    (Ag := fun C u u' => agreeOn (N := N) (thickSet Gp (compY (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) => i.1.1) (↑X₁f : Set (CTorus d L N₁ m₁ K)) C))
        u.1 u'.1 ∧ ∀ y ∈ psiThick (compY (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) => i.1.1) (↑X₁f : Set (CTorus d L N₁ m₁ K)) C), u.2 y = u'.2 y)
    (AgY := fun Y u u' => agreeOn (N := N) (thickSet Gp Y) u.1 u'.1 ∧
      ∀ y ∈ psiThick Y, u.2 y = u'.2 y) hrefl hlink hana hbd hloc'
  exact ⟨evTerm (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) => i.1.1) Gp m₀ (X1 Gp m₀ j 𝒦X) FF, hsum,
    fun Y u hu u' hu' h1 h2 => hlocY Y u hu u' hu' ⟨h1, h2⟩, hbound, hanY⟩


end Tail

section Fan

variable (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
include hC

/-- **(AE1), analyticity, for a functional of the decoupled objects.** -/
theorem fanF_analytic
    {F₁ : DecParams Gp × RawData d L (N₁ * L ^ m₁) K N → (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    (hF₁an : AnalyticOnNhd ℂ F₁ {q | (∀ P, ‖q.1 P‖ < Real.exp κ) ∧ ∃ D : BgData Gp N,
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D ∧ q.2 = (D.Ψ, D.h)})
    (hF₁ : ∀ (s : DecParams Gp) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
        (α : Gp.Ω 1 → ℂ), IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
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
        polydisc (0 : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) → ℂ) (fun _ => Real.exp κ)) := by
  classical
  rintro ⟨⟨u, ψ'⟩, s⟩ ⟨⟨⟨D, hD, rfl⟩, hψ⟩, hs⟩
  have hs' : ∀ i, ‖s i‖ < Real.exp κ := fun i => by simpa using hs i
  have hE1 : 1 < Real.exp κ := Real.one_lt_exp_iff.2 hC.hκ
  have hsx : ∀ P, ‖extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s P‖ < Real.exp κ :=
    norm_extParams_lt hE1 hs'
  have hs1 := extParams_hs1 (X₁f := X₁f) (Gp := Gp) s
  obtain ⟨φ, α, δφ, δα, hI, hFeq, hstrict, hSeq, hmem⟩ :=
    point_facts_core hC hF₁ hSol hsx hs1 hD hψ
  set pt : (RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ)) ×
      (ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) → ℂ) := ((rawOf D, ψ'), s) with hpt
  set g0 : (RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ)) ×
      (ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) → ℂ) →
      DecParams Gp × RawData d L (N₁ * L ^ m₁) K N :=
    fun p => (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) p.2, p.1.1) with hg0
  have hext : AnalyticAt ℂ (fun p : (RawData d L (N₁ * L ^ m₁) K N ×
      (CTorus d L N₁ m₁ K → Fin N → ℂ)) × (ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) → ℂ) =>
      extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) p.2) pt :=
    (analyticAt_extParams s).comp_of_eq analyticAt_snd rfl
  have ha0 : AnalyticAt ℂ g0 pt := hext.prod (analyticAt_fst.comp analyticAt_fst)
  have hU : InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D := by
    have hd0 : 0 < d := by have := hC.HBp.hd; omega
    have hc1 := one_le_xiC1 d
    have hε := hC.eps_pos
    have hδ0 : 0 < xiC1 d * eps := by positivity
    exact inUnionDomainC_of_inDomainC hC.HBp hδ0
      (hC.c7le.trans ((c7_le_bgC1 d L N BG κ).trans (bgC1_le_bgC0 d L N hd0))) hC.c7le
      (xiCData_inDomainC hC.HBp hC.small1 hD)
  have ha1 : AnalyticAt ℂ (fun p => F₁ (g0 p)) pt :=
    (hF₁an (g0 pt) ⟨hsx, D, hU, rfl⟩).comp_of_eq ha0 rfl
  have hφ1 : AnalyticAt ℂ (fun p => (F₁ (g0 p)).1) pt := analyticAt_fst.comp ha1
  have hΨ1 : ∀ y jj, AnalyticAt ℂ (fun p : (RawData d L (N₁ * L ^ m₁) K N ×
      (CTorus d L N₁ m₁ K → Fin N → ℂ)) × (ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) → ℂ) =>
      p.1.1.1 y jj) pt := fun y jj =>
    (analyticAt_rawΨ y jj (rawOf D)).comp_of_eq (analyticAt_fst.comp analyticAt_fst) rfl
  set ed : (RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ)) ×
      (ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) → ℂ) → Edat Hm N :=
    fun p => flEdat Gp Hm (F₁ (g0 p)) p.1.1.1 p.1.2 with hed
  have haed : AnalyticAt ℂ ed pt := by
    refine AnalyticAt.prod (analyticAt_barField (fun p => (F₁ (g0 p)).1) (fun p => p.1.1.1)
      (fun r => analyticAt_pi_iff.1 hφ1 r) hΨ1) (AnalyticAt.prod
      (analyticAt_flAlpha (fun p => (F₁ (g0 p)).2) (fun y => analyticAt_pi_iff.1
        (analyticAt_snd.comp ha1) y))
      (AnalyticAt.prod (analyticAt_snd.comp analyticAt_fst) analyticAt_const))
  have hSolpt : AnalyticAt ℂ (fun p => Sol (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) p.2,
      ed p)) pt := by
    refine (hSolan (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s, ed pt)
      ⟨hsx, ?_⟩).comp_of_eq (hext.prod haed) rfl
    have : ed pt = flEdat Gp Hm (φ, α) D.Ψ ψ' := by
      show flEdat Gp Hm (F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s, rawOf D)) D.Ψ ψ' = _
      rw [hFeq]
    rw [this]; exact hstrict
  have hg : AnalyticAt ℂ (fun p : (RawData d L (N₁ * L ^ m₁) K N ×
      (CTorus d L N₁ m₁ K → Fin N → ℂ)) × (ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) → ℂ) =>
      (F₁ (g0 p), (Sol (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) p.2, ed p)).1,
        p.1)) pt :=
    ha1.prod ((analyticAt_fst.comp hSolpt).prod analyticAt_fst)
  have hval : (F₁ (g0 pt), (Sol (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) pt.2,
      ed pt)).1, pt.1) = ((φ, α), δφ, (rawOf D, ψ')) := by
    have e1 : F₁ (g0 pt) = (φ, α) := hFeq
    have e2 : ed pt = flEdat Gp Hm (φ, α) D.Ψ ψ' := by
      show flEdat Gp Hm (F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s, rawOf D)) D.Ψ ψ' = _
      rw [hFeq]
    show (F₁ (g0 pt), (Sol (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s, ed pt)).1,
      (rawOf D, ψ')) = _
    rw [e1, e2, hSeq]
  have hΦpt := hΦ ((φ, α), δφ, (rawOf D, ψ')) hmem
  rw [← hval] at hΦpt
  exact hΦpt.comp_of_eq hg rfl

variable {m₀ : ℕ} {X 𝒦X : Set (CTorus d L N₁ m₁ K)}

/-- **(AE2), locality, for a functional of the decoupled objects.**  If `Φ` depends on the
triple only through its values on a set `Z ⊆ X₁`, the composite is local. -/
theorem fanF_local
    (hcov : CovSetup Gp m₀ j X 𝒦X) (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ K)) = X1 Gp m₀ j 𝒦X)
    (hconn : HatConn Gp) (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
    {F₁ : DecParams Gp × RawData d L (N₁ * L ^ m₁) K N → (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    (hF₁ : ∀ (s : DecParams Gp) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
        (α : Gp.Ω 1 → ℂ), IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
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
    {Φ : ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) → (Hm.Ω 1 × Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ) → ℂ}
    {Z Zα : Set (CTorus d L N₁ m₁ K)} (hZ : Z ⊆ ↑X₁f) (hmar : BlockMargin Gp X₁f Zα)
    (hΦloc : ∀ t ∈ FlReal Gp Hm a₁ ν BG κ eps X₁f BG₂ δ₁,
      ∀ t' ∈ FlReal Gp Hm a₁ ν BG κ eps X₁f BG₂ δ₁,
      (∀ y : Gp.Ω 1, (y : CTorus d L N₁ m₁ K) ∈ Z → ∀ i, t.1.1 (y, i) = t'.1.1 (y, i)) →
      (∀ y : Gp.Ω 1, (y : CTorus d L N₁ m₁ K) ∈ Zα → t.1.2 y = t'.1.2 y) →
      (∀ y : Hm.Ω 1, (y : CTorus d L N₁ m₁ K) ∈ Z → ∀ i, t.2.1 (y, i) = t'.2.1 (y, i)) →
      agreeOn (thickSet Gp Z) t.2.2.1 t'.2.2.1 → (∀ y ∈ psiThick Z, t.2.2.2 y = t'.2.2.2 y) →
      Φ t.1 t.2.1 t.2.2 = Φ t'.1 t'.2.1 t'.2.2) :
    LocalityAEOn (Real.exp κ) (XiCRaw Gp (compWeight L a₁) ν K 1 eps ×ˢ FlBall Hm δ₁)
      (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) => Pset m₁ i.1.1)
      (compY (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) => i.1.1)
        (↑X₁f : Set (CTorus d L N₁ m₁ K)))
      (fun C u u' => agreeOn (thickSet Gp (compY
        (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) => i.1.1)
        (↑X₁f : Set (CTorus d L N₁ m₁ K)) C)) u.1 u'.1 ∧
        ∀ y ∈ psiThick (compY
          (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) => i.1.1)
          (↑X₁f : Set (CTorus d L N₁ m₁ K)) C), u.2 y = u'.2 y)
      (fun u s => Φ (F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s, u.1))
        (Sol (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s,
          flEdat Gp Hm (F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s, u.1))
            u.1.1 u.2)).1 u) := by
  classical
  rintro C ⟨u, ψ⟩ ⟨u', ψ'⟩ ⟨⟨D, hD, rfl⟩, hψ⟩ ⟨⟨D', hD', rfl⟩, hψ'⟩ s s' hs hs' hag hAg
  obtain ⟨hAgΘ, hAgψ⟩ := hAg
  set cc : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) → ℕ × CTorus d L N₁ m₁ K :=
    fun i => i.1.1 with hcc
  have hd0 : 0 < d := by have := hC.HBp.hd; omega
  have hE1 : 1 < Real.exp κ := Real.one_lt_exp_iff.2 hC.hκ
  have hsx : ∀ P, ‖extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s P‖ < Real.exp κ :=
    norm_extParams_lt hE1 (fun i => hs.2 i)
  have hsx' : ∀ P, ‖extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s' P‖ < Real.exp κ :=
    norm_extParams_lt hE1 (fun i => hs'.2 i)
  have hs1 := extParams_hs1 (X₁f := X₁f) (Gp := Gp) s
  have hs1' := extParams_hs1 (X₁f := X₁f) (Gp := Gp) s'
  obtain ⟨φ, α, δφ, δα, hI, hFeq, hstrict, hSeq, hmem⟩ :=
    point_facts_core hC hF₁ hSol hsx hs1 hD hψ
  obtain ⟨φ', α', δφ', δα', hI', hFeq', hstrict', hSeq', hmem'⟩ :=
    point_facts_core hC hF₁ hSol hsx' hs1' hD' hψ'
  show Φ (F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s, rawOf D))
      (Sol (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s,
        flEdat Gp Hm (F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s, rawOf D))
          D.Ψ ψ)).1 (rawOf D, ψ) =
    Φ (F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s', rawOf D'))
      (Sol (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s',
        flEdat Gp Hm (F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s', rawOf D'))
          D'.Ψ ψ')).1 (rawOf D', ψ')
  rw [hFeq, hFeq', hSeq, hSeq']
  -- notation
  set Yc : Set (CTorus d L N₁ m₁ K) := compY cc (↑X₁f : Set (CTorus d L N₁ m₁ K)) C with hYc
  set Y : Finset (CTorus d L N₁ m₁ K) := Finset.univ.filter (· ∈ Yc) with hY
  set 𝒞 : Finset (ℕ × CTorus d L N₁ m₁ K) := C.image cc with h𝒞
  have hmemY : ∀ x, x ∈ Y ↔ x ∈ Yc := fun x => by simp [hY]
  have hcc_mem : ∀ i, cc i ∈ cubeIdx Gp := fun i => i.1.2
  have hX₁Ω : (↑X₁f : Set (CTorus d L N₁ m₁ K)) ⊆ ↑(Gp.Ω 1) := fun x hx =>
    X1_subset_Omega1 hcov (hX₁ ▸ hx)
  have hPatchΩ : patchUnion (↑X₁f : Set (CTorus d L N₁ m₁ K)) (fun i => Pset m₁ (cc i)) C ⊆
      ↑(Gp.Ω 1) := by
    intro x hx
    rcases hx with hx | hx
    · exact hX₁Ω hx
    · obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.1 hx
      exact Pset_subset_Omega1 hcov (hcc_mem i) hxi
  have hYsub : Yc ⊆ patchUnion (↑X₁f : Set (CTorus d L N₁ m₁ K)) (fun i => Pset m₁ (cc i)) C :=
    componentOf_subset _ (fun _ h => Or.inl h)
  have hYnn : IsNnComp ((Vset X₁f 𝒞).filter fun x => x ∈ Gp.Ω 1) Y := by
    refine ⟨fun x hx => ?_, fun x hx y hy hadj => ?_⟩
    · have hxY : x ∈ Yc := (hmemY x).1 hx
      rw [Finset.mem_filter]
      exact ⟨(mem_Vset_iff cc C).2 (hYsub hxY), hPatchΩ (hYsub hxY)⟩
    · have hxY : x ∈ Yc := (hmemY x).1 hx
      rw [Finset.mem_filter] at hy
      exact (hmemY y).2 (compY_closed hxY ((mem_Vset_iff cc C).1 hy.1) hadj)
  have hdisj_of : ∀ P : ↥(cubeIdx Gp), P.1 ∈ parCubes Gp X₁f →
      Disjoint (Pset m₁ P.1) (↑X₁f : Set (CTorus d L N₁ m₁ K)) := by
    intro P hP
    by_contra hnd
    have hsub := Pset_subset_of_not_disjoint (hX₁ ▸ hcov.polySetup) P.2 hnd
    unfold parCubes at hP
    rw [Finset.mem_filter] at hP
    apply hP.2
    intro y hy
    have := hsub (mem_cubeP.1 hy)
    exact Finset.mem_coe.1 this
  have hs1E : ∀ P ∈ cubeIdx Gp, P ∉ parCubes Gp X₁f →
      extS Gp (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s) P = 1 ∧
        extS Gp (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s') P = 1 := by
    intro P hP hPn
    unfold extS
    simp only [hP, ↓reduceDIte]
    exact ⟨hs1 P hP hPn, hs1' P hP hPn⟩
  have hs0E : ∀ P ∈ parCubes Gp X₁f, P ∉ 𝒞 →
      extS Gp (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s) P = 0 ∧
        extS Gp (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s') P = 0 := by
    intro P hP hP𝒞
    have hPc : P ∈ cubeIdx Gp := (Finset.mem_filter.1 hP).1
    have hd := hdisj_of ⟨P, hPc⟩ hP
    unfold extS
    simp only [hPc, ↓reduceDIte]
    have hi : (⟨⟨P, hPc⟩, hd⟩ : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K))) ∉ C := fun hi =>
      hP𝒞 (Finset.mem_image.2 ⟨_, hi, rfl⟩)
    rw [show extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s ⟨P, hPc⟩ =
        s ⟨⟨P, hPc⟩, hd⟩ from extParams_par s ⟨⟨P, hPc⟩, hd⟩,
      show extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s' ⟨P, hPc⟩ =
        s' ⟨⟨P, hPc⟩, hd⟩ from extParams_par s' ⟨⟨P, hPc⟩, hd⟩]
    exact ⟨hs.1 _ hi, hs'.1 _ hi⟩
  have hsub : ∀ P ∈ 𝒞, (∀ x ∈ cubeP P, x ∈ Y) →
      extS Gp (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s) P =
        extS Gp (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s') P := by
    intro P hP𝒞 hSub
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hP𝒞
    have hsub : Pset m₁ (cc i) ⊆ Yc := by
      intro x hx
      have hxΩ : x ∈ Gp.Ω 1 := Pset_subset_Omega1 hcov (hcc_mem i) hx
      exact (hmemY x).1 (hSub x (mem_cubeP.2 hx))
    have := hag i hi hsub
    unfold extS
    simp only [hcc_mem i, ↓reduceDIte]
    rw [show extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s ⟨cc i, hcc_mem i⟩ = s i from
        extParams_par s i,
      show extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s' ⟨cc i, hcc_mem i⟩ = s' i from
        extParams_par s' i]
    exact this
  -- the data domain
  have hc1 := one_le_xiC1 d
  have hε := hC.eps_pos
  have hδ0 : 0 < xiC1 d * eps := by positivity
  have hδ1 : xiC1 d * eps ≤ c7 d L N BG κ := hC.c7le
  have hδ0' : xiC1 d * eps ≤ bgC0 d L N := hδ1.trans ((c7_le_bgC1 d L N BG κ).trans
    (bgC1_le_bgC0 d L N hd0))
  have hνε : ν * ((L : ℝ) ^ K) ^ 2 * (xiC1 d * eps) ^ 2 ≤ (xiC1 d * eps) ^ 2 := by
    have := hC.HBp.massLe; nlinarith [sq_nonneg (xiC1 d * eps)]
  have hDom := xiCData_inDomainC hC.HBp hC.small1 hD
  have hDom' := xiCData_inDomainC hC.HBp hC.small1 hD'
  have hdata : ∀ x : Gp.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ Y → ∀ y ∈ resDep Gp (x : CTorus d L N₁ m₁ K),
      D.Ψ y = D'.Ψ y ∧ (y ∈ Gp.Ω 1 → D.h y = D'.h y) := by
    intro x hx y hy
    have := hAgΘ y (Or.inr ⟨x, (hmemY x).1 hx, x.2, hy⟩)
    exact ⟨this.1, fun _ => this.2⟩
  have hagE : ∀ P ∈ 𝒞, SubI Gp (cubeP P) Y →
      extS Gp (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s) P =
        extS Gp (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s') P := by
    intro P hP𝒞 hSub
    refine hsub P hP𝒞 (fun x hx => ?_)
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hP𝒞
    exact hSub ⟨x, Pset_subset_Omega1 hcov (hcc_mem i) (mem_cubeP.1 hx)⟩ hx
  -- the background fields agree
  obtain ⟨hαSY, hφY⟩ := i4b_local hC.hS hC.Sp hconn hC.HBp hC.hκ.le hC.hM
    (fun P => (hsx P).le) (fun P => (hsx' P).le) hδ0 le_rfl hδ0' hδ1 hνε hDom hDom' hYnn
    hs1E hs0E hagE hdata hI hI'
  -- the geometry of the pair
  have SL : Dec2.CoverLocal (coverOf Gp) Gp (compWeight L a₁) ν (Dec2.selfKc d L) (Cchi d L) :=
    Dec2.coverLocal_self hC.Sp
  have hconn' : Dec2.HatConn (coverOf Gp) Gp := hconn
  have h𝒞c : ∀ P ∈ 𝒞, P ∈ (coverOf Gp).cubeIdx := by
    intro P hP
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hP
    exact hcc_mem i
  have hsubΩ : ∀ x, x ∈ Hm.Ω 1 → x ∈ Gp.Ω 1 := fun x hx => hC.hPmp.mem_Ω1 hx
  obtain ⟨A, hIU, hAcube⟩ := incUnion_of_nnComp SL hconn' hsubΩ hrow h𝒞c hYnn
  -- the fluctuation fields agree
  set e := flEdat Gp Hm (φ, α) D.Ψ ψ with he
  set e' := flEdat Gp Hm (φ', α') D'.Ψ ψ' with he'
  obtain ⟨hfld, hfix, hs6, hsK, hdp, huniq⟩ := hSol (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s, e) hsx hstrict
  obtain ⟨hfld', hfix', hs6', hsK', hdp', huniq'⟩ :=
    hSol (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s', e') hsx' hstrict'
  have hOp := hC.SM.toCoverBase.toOpSetting.toGreen
  have hB0 : 0 ≤ 2 * (K4 d L N BG κ * (xiC1 d * eps)) :=
    mul_nonneg (by norm_num) (mul_nonneg (K4_pos hC.hS.fam.2.1 hd0).le hδ0.le)
  have Hh : DecHyp Hm (compWeight L a₁) ν false e.2.1 e.1 e.2.2.1 e.2.2.2
      (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ :=
    StrictDataM.hyp hOp hB0 hC.δ₁_pos.le hC.B_one hstrict
  have Hh' : DecHyp Hm (compWeight L a₁) ν false e'.2.1 e'.1 e'.2.2.1 e'.2.2.2
      (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ :=
    StrictDataM.hyp hOp hB0 hC.δ₁_pos.le hC.B_one hstrict'
  have hDA : Dec2.DataAgreeS Hm N Y (Dec2.SYF (coverOf Gp) Hm (compWeight L a₁) ν X₁f 𝒞 Y)
      e.2.1 e'.2.1 e.1 e'.1 e.2.2.1 e'.2.2.1 e.2.2.2 e'.2.2.2 := by
    refine ⟨fun x hx => ?_, fun x hx => ?_, fun x hx => ?_, fun y hy hxy => ?_, fun x hx i => rfl⟩
    · have := hαSY ⟨x, hsubΩ x x.2⟩ (SYF_subset_SY SL hconn' hsubΩ hYnn hx)
      show flAlpha Gp Hm α x = flAlpha Gp Hm α' x
      rw [flAlpha_of_prec hC.hPmp, flAlpha_of_prec hC.hPmp]
      exact this
    · have hxΩ := hsubΩ x x.2
      funext i
      show barField Gp D.Ψ φ x i = barField Gp D'.Ψ φ' x i
      simp only [barField, hxΩ, ↓reduceDIte]
      exact hφY ⟨x, hxΩ⟩ hx i
    · exact hAgψ x (Or.inl ((hmemY x).1 hx))
    · obtain ⟨x, hx, hadj⟩ := hxy
      exact hAgψ y (Or.inr ⟨x, (hmemY x).1 hx, hadj⟩)
  have hflloc := Dec2.i4a_local_fpS hC.hS2.fam hC.SM hC.hκ.le hC.hM2 (fun P => (hsx P).le)
    (fun P => (hsx' P).le) Hh Hh' hC.B_le hC.δ₁_le hIU hs1E hs0E
    (fun P hP hPA => hsub P hP (hAcube P hPA).2) hDA
    hfix hs6 hfix' hs6'
  have hδeq : ∀ y : Hm.Ω 1, (y : CTorus d L N₁ m₁ K) ∈ Y → ∀ i, δφ (y, i) = δφ' (y, i) := by
    intro y hy i
    have h1 : (Sol (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s, e)).1 = δφ :=
      congrArg Prod.fst hSeq
    have h2 : (Sol (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s', e')).1 = δφ' :=
      congrArg Prod.fst hSeq'
    rw [← h1, ← h2, hfld, hfld']
    exact hflloc.2 y hy i
  have hZY : ∀ y ∈ Z, y ∈ Yc := fun y hy =>
    subset_compY (↑X₁f : Set (CTorus d L N₁ m₁ K)) C (hZ hy)
  have hXY' : ∀ x ∈ X₁f, x ∈ Y := fun x hx => (hmemY x).2 (subset_compY
    (↑X₁f : Set (CTorus d L N₁ m₁ K)) C (Finset.mem_coe.2 hx))
  have hαeq : ∀ y : Gp.Ω 1, (y : CTorus d L N₁ m₁ K) ∈ Zα → α y = α' y := by
    intro y hy
    obtain ⟨z, hz, hyz, hQ, hhat⟩ := hmar y hy y.2
    refine hαSY y (Finset.mem_biUnion.2 ⟨z, Finset.mem_filter.2 ⟨hz, ?_, ?_⟩, hyz⟩)
    · intro P hP hPpar
      exact absurd hPpar (hQ P hP)
    · intro x hx
      exact hXY' _ (hhat x hx)
  refine hΦloc _ hmem _ hmem' (fun y hy i => ?_) (fun y hy => hαeq y hy) (fun y hy i => ?_) ?_ ?_
  · exact hφY y ((hmemY _).2 (hZY _ hy)) i
  · exact hδeq y ((hmemY _).2 (hZY _ hy)) i
  · exact agreeOn_mono (thickSet_mono (fun y hy => hZY y hy)) hAgΘ
  · exact fun y hy => hAgψ y (psiThick_mono (fun y hy => hZY y hy) hy)


variable (Gp Hm) in
/-- **The fluctuation field at `s ≡ 1`** for the datum `D` and the fluctuation `ψ'`: the field
`δφ(ψ')` of Theorem I-4a (mode P) with the background `φ_{k+1} = bgFieldC D` (the same
`flField` as in `flDatumOne`). -/
noncomputable def flFieldOne (BG₂ κ a₁ ν : ℝ) (D : BgData Gp N)
    (ψ' : CTorus d L N₁ m₁ K → Fin N → ℂ) : Hm.Ω 1 × Fin N → ℂ :=
  flField (coverOf Gp) Hm (compWeight L a₁) ν
    (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) (fun _ => 1)
    (flEdat Gp Hm (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D,
      bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D) D.Ψ ψ')

/-- **Theorem I-5 for a functional of the decoupled objects** (LOCALIZATION.md (V3)).  Let `Φ` be
analytic and bounded by `Eb` on the realizable triples `(φ_{k+1}(s), δφ(s), (Θ, ψ'))` and depend only
on the values on `Z ⊆ X₁`.  Then
`Φ(φ_{k+1}, δφ, Θ, ψ') = ∑_{Y ⊃ X₁} Ev_Y(Θ, ψ')` with terms analytic in `(Θ, ψ')`, depending on `Θ`
through its restriction to the thickening of `Y` and on `ψ'` through its restriction to `Y` and its
neighbours, and bounded by `Eb e^{-κ₀ Δ - 2 κ d̃^{cov}_{k+1}(Y)}` (`Δ = 0` for `Φ` that is bounded
without decay in `X`; `Δ` the size of `X` otherwise). -/
theorem i5_functional (hcov : CovSetup Gp m₀ j X 𝒦X)
    (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ K)) = X1 Gp m₀ j 𝒦X)
    (hconn : HatConn Gp) (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
    (hopt : ∃ (W₀ : Finset (CTorus d L N₁ m₁ K))
      (E₀ : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K)),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X) ∧ MeetsOne m₀ j 𝒦X W₀ ∧
        bondCost (scaleW L m₀ m₁ j) E₀ = treeLenCovOne m₀ j X)
    {κdec κ₀ Eb : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hEb : 0 ≤ Eb)
    {Φ : ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) → (Hm.Ω 1 × Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ) → ℂ}
    (hΦan : AnalyticOnNhd ℂ (fun t => Φ t.1 t.2.1 t.2.2)
      (FlReal Gp Hm a₁ ν BG κ eps X₁f BG₂ δ₁))
    (hΦbd : ∀ t ∈ FlReal Gp Hm a₁ ν BG κ eps X₁f BG₂ δ₁,
      ‖Φ t.1 t.2.1 t.2.2‖ ≤ Eb * Real.exp (-(κdec - 1) * treeLenCovOne m₀ j X))
    {Z Zα : Set (CTorus d L N₁ m₁ K)} (hZ : Z ⊆ ↑X₁f) (hmar : BlockMargin Gp X₁f Zα)
    (hΦloc : ∀ t ∈ FlReal Gp Hm a₁ ν BG κ eps X₁f BG₂ δ₁,
      ∀ t' ∈ FlReal Gp Hm a₁ ν BG κ eps X₁f BG₂ δ₁,
      (∀ y : Gp.Ω 1, (y : CTorus d L N₁ m₁ K) ∈ Z → ∀ i, t.1.1 (y, i) = t'.1.1 (y, i)) →
      (∀ y : Gp.Ω 1, (y : CTorus d L N₁ m₁ K) ∈ Zα → t.1.2 y = t'.1.2 y) →
      (∀ y : Hm.Ω 1, (y : CTorus d L N₁ m₁ K) ∈ Z → ∀ i, t.2.1 (y, i) = t'.2.1 (y, i)) →
      agreeOn (thickSet Gp Z) t.2.2.1 t'.2.2.1 → (∀ y ∈ psiThick Z, t.2.2.2 y = t'.2.2.2 y) →
      Φ t.1 t.2.1 t.2.2 = Φ t'.1 t'.2.1 t'.2.2) :
    ∃ Ev : Set (CTorus d L N₁ m₁ K) →
        RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ) → ℂ,
      (∀ D : BgData Gp N, XiCData Gp (compWeight L a₁) ν K 1 eps D →
        ∀ ψ' ∈ FlBall Hm δ₁,
        Φ (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D,
            bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D) (flFieldOne Gp Hm BG₂ κ a₁ ν D ψ')
          (rawOf D, ψ') =
        ∑ Y ∈ polymerDomains (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) => i.1.1) Gp m₀
          (X1 Gp m₀ j 𝒦X), Ev Y (rawOf D, ψ')) ∧
      (∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν K 1 eps ×ˢ FlBall Hm δ₁,
        ∀ u' ∈ XiCRaw Gp (compWeight L a₁) ν K 1 eps ×ˢ FlBall Hm δ₁,
        agreeOn (thickSet Gp Y) u.1 u'.1 → (∀ y ∈ psiThick Y, u.2 y = u'.2 y) →
        Ev Y u = Ev Y u') ∧
      (∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν K 1 eps ×ˢ FlBall Hm δ₁,
        ‖Ev Y u‖ ≤ Eb * Real.exp (-κ₀ * treeLenCovOne m₀ j X - 2 * κdec * treeLenCov Gp m₀ Y)) ∧
      (∀ Y, AnalyticOnNhd ℂ (Ev Y) (XiCRaw Gp (compWeight L a₁) ν K 1 eps ×ˢ FlBall Hm δ₁)) := by
  classical
  have hd0 : 0 < d := by have := hC.HBp.hd; omega
  have hc1 := one_le_xiC1 d
  have hε := hC.eps_pos
  have hδ0 : 0 < xiC1 d * eps := by positivity
  have hB0 : 0 ≤ 2 * (K4 d L N BG κ * (xiC1 d * eps)) :=
    mul_nonneg (by norm_num) (mul_nonneg (K4_pos hC.hS.fam.2.1 hd0).le hδ0.le)
  obtain ⟨F₁, hF₁an, hF₁⟩ := i4b_analytic hC.hS hC.Sp hC.HBp hC.hκ.le hC.hM
  obtain ⟨Sol, hSolan, hSolprop⟩ := Dec2.i4a_analytic (N := N) hC.hS2.fam hC.hS2.an
    hC.SM.toCoverBase hC.hκ.le hC.hM2 false hB0 hC.δ₁_pos.le hC.B_le hC.δ₁_le
  set F : RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ) →
      (ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) → ℂ) → ℂ :=
    fun u s => Φ (F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s, u.1))
      (Sol (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s,
        flEdat Gp Hm (F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s, u.1))
          u.1.1 u.2)).1 u with hF'
  have hana := fanF_analytic hC hF₁an hF₁ hSolan hSolprop hΦan
  have hbd : ∀ u ∈ XiCRaw (N := N) Gp (compWeight L a₁) ν K 1 eps ×ˢ FlBall Hm δ₁,
      ∀ s ∈ polydisc (0 : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) → ℂ)
        (fun _ => Real.exp κ),
      ‖F u s‖ ≤ Eb * Real.exp (-(κdec - 1) * treeLenCovOne m₀ j X) := by
    rintro ⟨u1, ψ'⟩ ⟨⟨D, hD, rfl⟩, hψ⟩ s hs
    have hs' : ∀ i, ‖s i‖ < Real.exp κ := fun i => by simpa using hs i
    have hE1 : 1 < Real.exp κ := Real.one_lt_exp_iff.2 hC.hκ
    have hsx : ∀ P, ‖extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s P‖ < Real.exp κ :=
      norm_extParams_lt hE1 hs'
    obtain ⟨φ, α, δφ, δα, hI, hFeq, hstrict, hSeq, hmem⟩ := point_facts_core hC hF₁ hSolprop hsx
      (extParams_hs1 (X₁f := X₁f) (Gp := Gp) s) hD hψ
    show ‖Φ (F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s, rawOf D))
      (Sol (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s,
        flEdat Gp Hm (F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s, rawOf D))
          D.Ψ ψ')).1 (rawOf D, ψ')‖ ≤ _
    rw [hFeq, hSeq]
    exact hΦbd _ hmem
  have hloc := fanF_local hC hcov hX₁ hconn hrow hF₁ hSolprop hZ hmar hΦloc
  obtain ⟨Ev, hsum, hlocY, hbound, hanY⟩ := expansion_of_AE (a₁ := a₁) hC.HBp.hd hC.HBp.hL hC.hκ
    hcov hX₁ hopt hκ₀ hκdec hκ h1 hlog hEb hana hbd hloc
  refine ⟨Ev, fun D hD ψ' hψ => ?_, hlocY, hbound, hanY⟩
  have hsum' := hsum (rawOf D, ψ') ⟨⟨D, hD, rfl⟩, hψ⟩
  rw [← hsum']
  symm
  have hE1 : 1 < Real.exp κ := Real.one_lt_exp_iff.2 hC.hκ
  have hsx : ∀ P : ↥(cubeIdx Gp), ‖(fun _ : ↥(cubeIdx Gp) => (1 : ℂ)) P‖ < Real.exp κ :=
    fun P => by simpa using hE1
  have hs1 : ∀ (P : ℕ × CTorus d L N₁ m₁ K) (hP : P ∈ cubeIdx Gp), P ∉ parCubes Gp X₁f →
      (fun _ : ↥(cubeIdx Gp) => (1 : ℂ)) ⟨P, hP⟩ = 1 := fun P hP hPn => rfl
  show Φ (F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) 1, rawOf D))
      (Sol (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) 1,
        flEdat Gp Hm (F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) 1, rawOf D))
          D.Ψ ψ')).1 (rawOf D, ψ') = _
  rw [extParams_one]
  obtain ⟨φ, α, δφ, δα, hI, hFeq, hstrict, hSeq, hmem⟩ :=
    point_facts_core hC hF₁ hSolprop hsx hs1 hD hψ
  rw [hFeq, hSeq]
  have hδ1 : xiC1 d * eps ≤ c7 d L N BG κ := hC.c7le
  have hδ0' : xiC1 d * eps ≤ bgC0 d L N := hδ1.trans ((c7_le_bgC1 d L N BG κ).trans
    (bgC1_le_bgC0 d L N hd0))
  have hνε : ν * ((L : ℝ) ^ K) ^ 2 * (xiC1 d * eps) ^ 2 ≤ (xiC1 d * eps) ^ 2 := by
    have := hC.HBp.massLe; nlinarith [sq_nonneg (xiC1 d * eps)]
  have hDom := xiCData_inDomainC hC.HBp hC.small1 hD
  obtain ⟨-, hφ1, hα1⟩ := i4b_one hC.hS hC.Sp hC.HBp hC.hκ.le hC.hM hδ0 le_rfl hδ0' hδ1
    hνε hDom hI
  obtain ⟨hfld, hfix, hs6, -, -, huniq⟩ := hSolprop ((fun _ : ↥(cubeIdx Gp) => (1 : ℂ)),
    flEdat Gp Hm (φ, α) D.Ψ ψ') hsx hstrict
  have hmult := flMult_spec (C := coverOf Gp) (Hm := Hm) (a := compWeight L a₁) (ν := ν)
    (ρ := c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) (s := fun _ : ↥(cubeIdx Gp) => (1 : ℂ))
    (e := flEdat Gp Hm (φ, α) D.Ψ ψ') ⟨hs6, hfix⟩ (fun δα' h => huniq δα' h.1 h.2)
  have hfl : flFieldOne Gp Hm BG₂ κ a₁ ν D ψ' = δφ := by
    have hSol1 : (Sol ((fun _ : ↥(cubeIdx Gp) => (1 : ℂ)),
        flEdat Gp Hm (φ, α) D.Ψ ψ')).1 = δφ := congrArg Prod.fst hSeq
    unfold flFieldOne flField
    rw [hφ1, hα1]
    exact (congrArg (dphi Hm (Dec2.decG (coverOf Gp) Hm (compWeight L a₁) ν
      (fun _ : ↥(cubeIdx Gp) => (1 : ℂ))) (flEdat Gp Hm (φ, α) D.Ψ ψ').2.1
      (flEdat Gp Hm (φ, α) D.Ψ ψ').1 (pertSource Hm (compWeight L a₁)
      (flEdat Gp Hm (φ, α) D.Ψ ψ').2.2.1 (flEdat Gp Hm (φ, α) D.Ψ ψ').2.2.2)) hmult).trans
      (hfld.symm.trans hSol1)
  rw [hφ1, hα1, hfl]

end Fan

end Core

end Balaban.Localization
