/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.InteractionVBlock
public import Balaban.Fluctuation.ExpansionBounds
public import Balaban.Fluctuation.RenormIdentity
public import Balaban.Localization.Decoupled2One
public import Balaban.Localization.I5FluctSol
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The decoupled fluctuation at `s = 1` is the exact fluctuation (FLUCTUATION §3.3, V-part)

At `s = 1` mode P coincides with mode U when the base field satisfies the constraint
(`φ₀ · φ₀ = 1`), and the decoupled system is the perturbed system of Proposition 5.1.  Hence the
exact fluctuation `φ' = φ_k(ψ) - φ_{k+1}|` (a small solution of the perturbed system, Lemma 2.3 (d))
is the fluctuation field `flField` of Theorem I-4a (mode P) at `s = 1` (`exact_eq_flField`), and the
block energies of the decoupled objects sum to the exact chord energy.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation Finset
  Matrix Set Metric

section Bridge

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {Hm : GeneratingSet d L (N₁ * L ^ m₁) K ϱm}
variable {a : ℕ → ℝ} {ν Kc Cx : ℝ}

/-- In mode P the map `𝒩` of a base field with `φ₀ · φ₀ = 1` is the map of mode U. -/
theorem Nmap_true_eq_false {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱm}
    (H₀ : Matrix (G.Ω 1) (G.Ω 1) ℂ) (φ₀ : CTorus d L N₁ m₁ K → Fin N → ℂ)
    (hg : ∀ x : G.Ω 1, gdef G φ₀ x = 0) (Fs δφ : G.Ω 1 × Fin N → ℂ) :
    Nmap G H₀ true φ₀ Fs δφ = Nmap G H₀ false φ₀ Fs δφ := by
  have : gdef G φ₀ = 0 := funext hg
  funext x
  simp [Nmap, this]

variable {C : DecCover d L N₁ m₁ K}

theorem decHyp_true_of_false {H : GeneratingSet d L (N₁ * L ^ m₁) K ϱm} {α₀ : H.Ω 1 → ℂ}
    {φ₀ δΨ : CTorus d L N₁ m₁ K → Fin N → ℂ} {f₁ : H.Ω 1 × Fin N → ℂ} {δ₀ δ₁ : ℝ}
    (Hh : DecHyp H a ν false α₀ φ₀ δΨ f₁ δ₀ δ₁) (hg : ∀ x : H.Ω 1, gdef H φ₀ x = 0) :
    DecHyp H a ν true α₀ φ₀ δΨ f₁ δ₀ δ₁ where
  green := Hh.green
  δ₀_nn := Hh.δ₀_nn
  δ₁_nn := Hh.δ₁_nn
  δ₀_le := Hh.δ₀_le
  smooth := Hh.smooth
  phiBd := Hh.phiBd
  alpha0 := Hh.alpha0
  f₁_bd := Hh.f₁_bd
  dPsi := Hh.dPsi
  g0 := fun _ x => by rw [hg x, norm_zero]; exact Hh.δ₁_nn
  gl := fun _ x => by
    have : gdef H φ₀ = 0 := funext hg
    rw [this]
    simp [negLap, zeroExt]
    exact Hh.δ₁_nn

theorem decFixed_false_of_true {s : Dec2.DecParams C} {H : GeneratingSet d L (N₁ * L ^ m₁) K ϱm}
    {α₀ : H.Ω 1 → ℂ} {φ₀ : CTorus d L N₁ m₁ K → Fin N → ℂ} {Fs : H.Ω 1 × Fin N → ℂ}
    {δα : H.Ω 1 → ℂ} (hg : ∀ x : H.Ω 1, gdef H φ₀ x = 0)
    (h : Dec2.DecFixed C H a ν s true α₀ φ₀ Fs δα) : Dec2.DecFixed C H a ν s false α₀ φ₀ Fs δα := by
  unfold Dec2.DecFixed at h ⊢
  rw [← Nmap_true_eq_false _ _ hg]
  exact h

/-- **The exact fluctuation is the fluctuation field of Theorem I-4a at `s = 1`.** -/
theorem exact_eq_flField {cstar BG c1 : ℝ} (hF : Dec2.FamSpec d L Kc Cx cstar BG)
    (h1 : Dec2.OneSpec d L Kc Cx c1) (hc1 : c1 ≤ cstar) {κ : ℝ} (hκ : 0 ≤ κ)
    (S : Dec2.CoverBase (coverOf Gp) Hm a ν Kc Cx)
    (hM : cstar * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {e : Edat Hm N} {δ₀ δ₁ : ℝ}
    (Hh : DecHyp Hm a ν false e.2.1 e.1 e.2.2.1 e.2.2.2 δ₀ δ₁)
    (hg : ∀ x : Hm.Ω 1, gdef Hm e.1 x = 0)
    (hδ₀ : δ₀ ≤ deltaStar' d L N (famConst d L BG κ) (gamma1 d / 8))
    (hδ₁ : δ₁ ≤ deltaStar' d L N (famConst d L BG κ) (gamma1 d / 8))
    (hnum : cK2' d L N (famConst d L BG κ) * δ₁ ≤ c6' d L N (famConst d L BG κ) (gamma1 d / 8))
    {δφ' : Hm.Ω 1 × Fin N → ℂ} {δα' : Hm.Ω 1 → ℂ}
    (hP : IsPerturbed Hm a ν e.2.1 e.1 (pertSource Hm a e.2.2.1 e.2.2.2) δφ' δα')
    (hs : Small Hm δα' (c6' d L N (famConst d L BG κ) (gamma1 d / 8))) :
    δφ' = flField (coverOf Gp) Hm a ν (c6' d L N (famConst d L BG κ) (gamma1 d / 8))
      (fun _ => 1) e := by
  have hs1 : ∀ P : (coverOf Gp).cubeIdx, ‖(fun _ : (coverOf Gp).cubeIdx => (1 : ℂ)) P‖ ≤
      Real.exp κ := fun P => by simpa using Real.one_le_exp hκ
  have hHU := decHyp_true_of_false Hh hg
  obtain ⟨δα, hfixU, -, hsmU, huniqU⟩ := Dec2.i4a_one hF h1 hc1 hκ S hM hHU hδ₀ hδ₁
  obtain ⟨hφ, hα⟩ := huniqU δφ' δα' hP hs
  obtain ⟨δαP, hfixP, -, -, -, huniqP, -⟩ := Dec2.i4a_exists_unique hF (coverOf Gp) Hm S hκ hM hs1
    Hh hδ₀ hδ₁
  have hfixF := decFixed_false_of_true hg hfixU
  have hsmall : Small Hm δα (c6' d L N (famConst d L BG κ) (gamma1 d / 8)) := fun x =>
    (hsmU x).trans hnum
  have heq : δα = δαP := huniqP δα hsmall hfixF
  have hmult : flMult (coverOf Gp) Hm a ν (c6' d L N (famConst d L BG κ) (gamma1 d / 8))
      (fun _ => 1) e = δα :=
    flMult_spec (e := e) ⟨hsmall, hfixF⟩ (fun δα'' h => by
      rw [heq]; exact huniqP δα'' h.1 h.2)
  unfold flField
  rw [hmult, hφ]

section Exact

variable {a₁ c BG κ eps Kc' Cx' c₂ BG₂ δ₁ : ℝ} {n : ℕ}

/-- **The exact fluctuation is `flFieldOne`** (Lemma 2.3 and Theorem I-4a at `s = 1`).  For a
whole-lattice pair of levels `n`, `n+1`, a datum `D'` of level `n+1` in the realizable set, and
the datum `D` of level `n` with the tangent `ψ' = D.Ψ - ψ^{(k)}` in the ball of fluctuations (the
disc `{ψ^{(k)} + t ψ'}` stays in the domain: the domain premises of Lemma 2.3 (d)):
`φ_k(ψ) - φ_{k+1}| = δφ(ψ')`. -/
theorem exact_fluct_eq_flFieldOne (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc' Cx' c₂ BG₂ δ₁)
    (hG : IsLevel Hm n) (hG' : IsLevel Gp (n + 1)) (hp : n + 1 ≤ K) (ha₁ : 0 < a₁)
    (H : BgHyp d L K ϱm (compWeight L a₁) ν)
    (D' : BgData Gp N) (hD : XiCData Gp (compWeight L a₁) ν K 1 eps D')
    (hc7 : c7 d L N BG κ ≤ thm73C3 d L N)
    (D : BgData Hm N) (hh : ∀ x i, D.h x i = D'.h x i)
    (hψ : compTangent hG hG' hp (compWeight L a₁)
      (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D') D' D ∈ FlBall Hm δ₁)
    {R : ℝ} (hR : 2 ≤ R)
    (hdisc : ∀ t : ℂ, ‖t‖ < R → InUnionDomainC Hm (bgC0 d L N) (bgC1 d L N) ν
      ((composeData (hG.precedes hG' hp) (compWeight L a₁)
        (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D') D').lineAt
        (tangentData D (composeData (hG.precedes hG' hp) (compWeight L a₁)
          (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D') D')) t))
    (hRs : R * δ₁ ≤ deltaStar d L N) (hsmall : cK2 d L N * (R * δ₁) < bgC0 d L N / 2)
    (hnum : cK2 d L N * δ₁ ≤ c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hnum' : cK2' d L N (famConst d L BG₂ κ) * δ₁ ≤
      c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) :
    bgFieldC Hm (compWeight L a₁) ν (bgC0 d L N) D -
        (hG.precedes hG' hp).restrictφ (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D') =
      flFieldOne Gp Hm BG₂ κ a₁ ν D' (compTangent hG hG' hp (compWeight L a₁)
        (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D') D' D) := by
  classical
  have hd0 : 0 < d := by have := hC.HBp.hd; omega
  have hL2 : 2 ≤ L := by have := hC.HBp.hL; omega
  set a := compWeight L a₁ with ha
  set φ₁ := bgFieldC Gp a ν (bgC0 d L N) D' with hφ₁
  set α₁ := bgMultC Gp a ν (bgC0 d L N) D' with hα₁
  set h := hG.precedes hG' hp with hhP
  set ψt := compTangent hG hG' hp a φ₁ D' D with hψt
  have hc1 := one_le_xiC1 d
  have hε := hC.eps_pos
  have hδ0 : 0 < xiC1 d * eps := by positivity
  have hDom := xiCData_inDomainC hC.HBp hC.small1 hD
  have hδ1 : xiC1 d * eps ≤ c7 d L N BG κ := hC.c7le
  have hδ0' : xiC1 d * eps ≤ bgC0 d L N := hδ1.trans ((c7_le_bgC1 d L N BG κ).trans
    (bgC1_le_bgC0 d L N hd0))
  have hU : InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D' :=
    inUnionDomainC_of_inDomainC hC.HBp hδ0 hδ0' hδ1 hDom
  have hU3 : InUnionDomainC Gp (bgC0 d L N) (thm73C3 d L N) ν D' := InUnionDomainC.mono hc7 hU
  have hU2 := InUnionDomainC.mono (thm73C3_le_thm73C2 d L N) hU3
  have hU1 := InUnionDomainC.mono (thm73C2_le_thm73C1 d L N) hU2
  have hUC1 : InUnionDomainC Gp (bgC0 d L N) (bgC1 d L N) ν D' := by
    obtain ⟨δ, ε, hδ0, hδε, hε, hδc, hνε, hDC⟩ := hU1
    exact ⟨δ, ε, hδ0, hδε, hε, (thm73_small (L := L) (N := N) hd0 hδ0 hδc).1, hνε, hDC⟩
  have hELp : IsEL Gp a ν D' φ₁ α₁ := (theorem72 hC.HBp hUC1).2.1.1
  have hapos : ∀ j, 1 ≤ j → j ≤ K → a j ≠ 0 := fun j hj _ =>
    (compWeight_pos hL2 ha₁ hj).ne'
  have hELc := isEL_compose h a hapos ν D' hELp
  have hhB : D.h = (composeData h a φ₁ D').h := funext fun x => funext fun i => by
    rw [hh x i, composeData_h hG hG' hp]
  have hDdom : InUnionDomainC Hm (bgC0 d L N) (bgC1 d L N) ν D := by
    have := hdisc 1 (by rw [norm_one]; linarith)
    rwa [lineAt_tangent D (composeData h a φ₁ D') hhB] at this
  have hELu : IsEL Hm a ν D (bgFieldC Hm a ν (bgC0 d L N) D) (bgMultC Hm a ν (bgC0 d L N) D) :=
    (theorem72 H hDdom).2.1.1
  have hELc' : IsEL Hm a ν (composeData h a φ₁ D') (h.restrictφ φ₁) (h.restrictα α₁) := hELc
  have hP := isPerturbed_of_EL (G := Hm) a (μ := ν) (μu := ν) (D := composeData h a φ₁ D')
    (Du := D) (δΨ := ψt) (φ₀ := barField Gp D'.Ψ φ₁)
    (fun x i => by simp [hψt, compTangent]) (fun x i => by rw [hhB])
    (fun x i => by
      have hx : (x : CTorus d L N₁ m₁ K) ∈ Gp.Ω 1 := hC.hPmp.mem_Ω1 x.2
      simp [barField, hx, Precedes.restrictφ]; rfl)
    hELc' hELu
  -- the exact perturbation is small
  have hψs : ∀ x, vn (compTangent hG hG' hp a φ₁ D' D x) ≤ δ₁ := by
    intro x
    by_cases hx : x ∈ dataSites Hm
    · exact (hψ x hx).le
    · have h1 : D.Ψ x = 0 := D.Ψ_zero x hx
      have h2 : (composeData h a φ₁ D').Ψ x = 0 := (composeData h a φ₁ D').Ψ_zero x hx
      have : compTangent hG hG' hp a φ₁ D' D x = 0 := by
        funext i; simp [compTangent, h1, h2]
      rw [this]
      have : vn (0 : Fin N → ℂ) = 0 := by simp [vn]
      rw [this]; exact hC.δ₁_pos.le
  obtain ⟨-, hsmall', -⟩ := expansion_bounds ha₁ hG hG' hp H hC.HBp D' hU3 D hh hC.δ₁_pos.le hR
    hψs hdisc hRs hsmall
  -- the data of the fluctuation problem at `s = 1`
  have hνε : ν * ((L : ℝ) ^ K) ^ 2 * (xiC1 d * eps) ^ 2 ≤ (xiC1 d * eps) ^ 2 := by
    have := hC.HBp.massLe; nlinarith [sq_nonneg (xiC1 d * eps)]
  have hB0 : 0 ≤ 2 * (K4 d L N BG κ * (xiC1 d * eps)) :=
    mul_nonneg (by norm_num) (mul_nonneg (K4_pos hC.hS.fam.2.1 hd0).le hδ0.le)
  obtain ⟨F₁, hF₁an, hF₁⟩ := i4b_analytic hC.hS hC.Sp hC.HBp hC.hκ.le hC.hM
  obtain ⟨Sol, hSolan, hSolprop⟩ := Dec2.i4a_analytic (N := N) hC.hS2.fam hC.hS2.an
    hC.SM.toCoverBase hC.hκ.le hC.hM2 false hB0 hC.δ₁_pos.le hC.B_le hC.δ₁_le
  have hE1 : 1 < Real.exp κ := Real.one_lt_exp_iff.2 hC.hκ
  have hsx : ∀ P : ↥(cubeIdx Gp), ‖(fun _ : ↥(cubeIdx Gp) => (1 : ℂ)) P‖ < Real.exp κ :=
    fun P => by simpa using hE1
  obtain ⟨φ, α, δφ, δα, hI, hFeq, hstrict, hSeq, hmem⟩ := point_facts_core
    (X₁f := (∅ : Finset (CTorus d L N₁ m₁ K))) hC hF₁ hSolprop hsx (fun P hP _ => rfl) hD hψ
  obtain ⟨-, hφ1, hα1⟩ := i4b_one hC.hS hC.Sp hC.HBp hC.hκ.le hC.hM hδ0 le_rfl hδ0' hδ1
    hνε hDom hI
  rw [← hφ1, ← hα1] at hstrict
  have hOp := hC.SM.toCoverBase.toOpSetting.toGreen
  have Hh := StrictDataM.hyp hOp hB0 hC.δ₁_pos.le hC.B_one hstrict
  have hg : ∀ x : Hm.Ω 1, gdef Hm (flEdat Gp Hm (φ₁, α₁) D'.Ψ ψt).1 x = 0 := by
    intro x
    have hx : (x : CTorus d L N₁ m₁ K) ∈ Gp.Ω 1 := hC.hPmp.mem_Ω1 x.2
    have := hELp.2 ⟨x, hx⟩
    unfold gdef
    simp only [flEdat, barField, hx, ↓reduceDIte]
    rw [this]; ring
  have e1 : flAlpha Gp Hm α₁ = h.restrictα α₁ :=
    funext fun y => flAlpha_of_prec hC.hPmp α₁ y
  have e2 : (fun p : Hm.Ω 1 × Fin N => ((ν - ν : ℝ) : ℂ) *
      ((composeData h a φ₁ D').h p.1 p.2 - h.restrictφ φ₁ p)) = 0 := by
    funext p; simp
  rw [e2] at hP
  have hP' : IsPerturbed Hm a ν (flEdat Gp Hm (φ₁, α₁) D'.Ψ ψt).2.1
      (flEdat Gp Hm (φ₁, α₁) D'.Ψ ψt).1
      (pertSource Hm a (flEdat Gp Hm (φ₁, α₁) D'.Ψ ψt).2.2.1 (flEdat Gp Hm (φ₁, α₁) D'.Ψ ψt).2.2.2)
      (bgFieldC Hm a ν (bgC0 d L N) D - h.restrictφ φ₁)
      (bgMultC Hm a ν (bgC0 d L N) D - h.restrictα α₁) := by
    show IsPerturbed Hm a ν (flAlpha Gp Hm α₁) (barField Gp D'.Ψ φ₁)
      (pertSource Hm a ψt 0) _ _
    rw [e1]; exact hP
  have hsm : Small Hm (bgMultC Hm a ν (bgC0 d L N) D - h.restrictα α₁)
      (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) := fun x => (hsmall' x).trans hnum
  exact exact_eq_flField (cstar := c₂) (BG := BG₂) (c1 := c₂) hC.hS2.fam hC.hS2.one le_rfl
    hC.hκ.le hC.SM.toCoverBase hC.hM2 Hh hg hC.B_le hC.δ₁_le hnum' hP' hsm

end Exact

section Sum

variable {n : ℕ}

/-- **The block energies add up to the chord energy** of the exact fluctuation:
`∑_z ℰ_z = (a_n/2)‖ψ' - Q_n δφ‖² + ½ ⟨δφ, (-Δ + ν + α) δφ⟩` for a whole-lattice level `n`. -/
theorem energyBlock_sum (hG : IsLevel Hm n) (ν : ℝ) (α : Gp.Ω 1 → ℂ)
    (δφ : Hm.Ω 1 × Fin N → ℂ) (ψ' : CTorus d L N₁ m₁ K → Fin N → ℂ) :
    ∑ z : Torus d (N₁ * L ^ m₁ * L ^ (K - (n + 1))),
        energyBlock Gp Hm a ν n α δφ ψ' z =
      levelEnergyC Hm a n ψ' (svec Hm δφ) + (1 / 2) * hessForm Gp ν α (svec Hm δφ) := by
  classical
  unfold energyBlock
  rw [Finset.sum_fiberwise (Finset.univ : Finset (CTorus d L N₁ m₁ K))
    (fun x : CTorus d L N₁ m₁ K => jBlock d L (N₁ * L ^ m₁) K (n + 1) x)
    (fun x => energyDensity Gp Hm a ν n α δφ ψ' x)]
  unfold energyDensity levelEnergyC hessForm
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hΩ : ∀ x : CTorus d L N₁ m₁ K, x ∈ Hm.Ω 1 := fun x => (hG x).1
  simp only [hΩ, ite_true]
  simp only [Finset.mul_sum]

end Sum

section Chord

variable {a₁ c BG κ eps Kc' Cx' c₂ BG₂ δ₁ : ℝ} {n : ℕ}

/-- **The potential `V^{(k)}` is the energy of the decoupled fluctuation minus a quadratic form**
(Lemma 2.3 (b), (a) and the identification of the fluctuation): with the notation of
`exact_fluct_eq_flFieldOne`, `V^{(k)}(ψ') = ∑_z ℰ_z - ½ ⟨ψ', Δ^{(k)} ψ'⟩`. -/
theorem interactionV_eq_energy (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc' Cx' c₂ BG₂ δ₁)
    (hG : IsLevel Hm n) (hG' : IsLevel Gp (n + 1)) (hp : n + 1 ≤ K) (ha₁ : 0 < a₁)
    (H : BgHyp d L K ϱm (compWeight L a₁) ν)
    (D' : BgData Gp N) (hD : XiCData Gp (compWeight L a₁) ν K 1 eps D')
    (hc7 : c7 d L N BG κ ≤ thm73C3 d L N)
    (D : BgData Hm N) (hh : ∀ x i, D.h x i = D'.h x i)
    (hψ : compTangent hG hG' hp (compWeight L a₁)
      (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D') D' D ∈ FlBall Hm δ₁)
    {R : ℝ} (hR : 2 ≤ R)
    (hdisc : ∀ t : ℂ, ‖t‖ < R → InUnionDomainC Hm (bgC0 d L N) (bgC1 d L N) ν
      ((composeData (hG.precedes hG' hp) (compWeight L a₁)
        (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D') D').lineAt
        (tangentData D (composeData (hG.precedes hG' hp) (compWeight L a₁)
          (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D') D')) t))
    (hRs : R * δ₁ ≤ deltaStar d L N) (hsmall : cK2 d L N * (R * δ₁) < bgC0 d L N / 2)
    (hnum : cK2 d L N * δ₁ ≤ c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hnum' : cK2' d L N (famConst d L BG₂ κ) * δ₁ ≤
      c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) :
    interactionV (hG.precedes hG' hp) (compWeight L a₁) ν
        (bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D')
        (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D')
        (compTangent hG hG' hp (compWeight L a₁)
          (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D') D' D)
        (bgFieldC Hm (compWeight L a₁) ν (bgC0 d L N) D -
          (hG.precedes hG' hp).restrictφ (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D')) =
      (∑ z : Torus d (N₁ * L ^ m₁ * L ^ (K - (n + 1))),
        energyBlock Gp Hm (compWeight L a₁) ν n (bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D')
          (flFieldOne Gp Hm BG₂ κ a₁ ν D' (compTangent hG hG' hp (compWeight L a₁)
            (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D') D' D))
          (compTangent hG hG' hp (compWeight L a₁)
            (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D') D' D) z) -
        (1 / 2) * deltaForm (hG.precedes hG' hp) (compWeight L a₁) ν
          (bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D')
          (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D')
          (compTangent hG hG' hp (compWeight L a₁)
            (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D') D' D) := by
  classical
  have hd0 : 0 < d := by have := hC.HBp.hd; omega
  have hc1 := one_le_xiC1 d
  have hε := hC.eps_pos
  have hδ0 : 0 < xiC1 d * eps := by positivity
  have hDom := xiCData_inDomainC hC.HBp hC.small1 hD
  have hδ1 : xiC1 d * eps ≤ c7 d L N BG κ := hC.c7le
  have hδ0' : xiC1 d * eps ≤ bgC0 d L N := hδ1.trans ((c7_le_bgC1 d L N BG κ).trans
    (bgC1_le_bgC0 d L N hd0))
  have hU : InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D' :=
    inUnionDomainC_of_inDomainC hC.HBp hδ0 hδ0' hδ1 hDom
  have hU3 : InUnionDomainC Gp (bgC0 d L N) (thm73C3 d L N) ν D' := InUnionDomainC.mono hc7 hU
  have hU2 := InUnionDomainC.mono (thm73C3_le_thm73C2 d L N) hU3
  have hU1 := InUnionDomainC.mono (thm73C2_le_thm73C1 d L N) hU2
  have hhB : D.h = (composeData (hG.precedes hG' hp) (compWeight L a₁)
      (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D') D').h := funext fun x => funext fun i => by
    rw [hh x i, composeData_h hG hG' hp]
  have hDdom : InUnionDomainC Hm (bgC0 d L N) (bgC1 d L N) ν D := by
    have := hdisc 1 (by rw [norm_one]; linarith)
    rwa [lineAt_tangent D (composeData (hG.precedes hG' hp) (compWeight L a₁)
      (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D') D') hhB] at this
  have hq := expansion_quadratic ha₁ hG hG' hp H hC.HBp D' hU2 D hh hDdom
  have hch := expansion_chord ha₁ hG hG' hp H hC.HBp D' hU1 D hh hDdom
  have hexact := exact_fluct_eq_flFieldOne hC hG hG' hp ha₁ H D' hD hc7 D hh hψ hR hdisc hRs
    hsmall hnum hnum'
  rw [energyBlock_sum hG ν _ _ _, ← hexact]
  linear_combination hch - hq

end Chord

end Bridge

end Balaban.Localization
