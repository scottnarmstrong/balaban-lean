/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.RenormC1Analytic
public import Balaban.Fluctuation.RenormStrictData
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The analytic family and the sharp bound of the shifted perturbation problem

Mode P (`ιU = false`) of the decoupled solver of Theorem I-4a, for the renormalization cut
family.  The data of the shifted problem at a raw datum `(Ψ, h)`, a vector `ξ` and a vector `s`
of cut parameters (indexed by the labels of the cover) are

`renDecData F₁ ((Ψ, h), ξ) s = (s', (φ̄, α + Δν, ε ξ₀ Ψ, Δν (h - φ)))`,
`s' = extParams (s ∘ renLabelEquiv.symm)`, `(φ, α) = F₁ (s', (Ψ, h))`, `Δν = ν_u - ν`,

where `F₁` is the analytic family of `i4b_analytic`.

* `renDecData_analytic`: this map is analytic at every point of `expDom × polydisc` (T1), and on
  the data of `XiCOneReal` it equals `renEdat` at the decoupled background.
* `renDec_analytic`: the composition of `i4a_analytic … false D₀ D₁` with this map is analytic at
  every point of `expDom × polydisc`, and on the data it is the `DecFixed` solution, with the
  bounds at `cK2' · D₁` and uniqueness in the `c6'` ball (T2).
* `renDec_sharp`: the same family satisfies the sharp bound `cK2' · b_* ε ‖ξ‖`, obtained by
  applying `i4a_exists_unique` at the radii `(D₀, b_* ε ‖ξ‖)` and uniqueness; at `ξ = 0` the
  solution vanishes (T3).

Not here: class membership, the endpoint `s = 1`, locality, `locC2` and `locDφ`.  The statements
are about mode P only; for `s ≠ 1` nothing is said about the Euler–Lagrange equation of the
continued field.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Analysis Finset

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}

section Data

variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) K ϱ}

/-- Analyticity of the data tuple `(φ̄, α + Δν, ζ Ψ, Δν (h - φ))` in the raw datum, `ξ`, `φ`, `α`
(the denominator `1 + ξ₃` of `ν_u` being nonzero). -/
theorem an_renData {Q : Type*} [NormedAddCommGroup Q] [NormedSpace ℂ Q] {q : Q} (ν eps : ℝ)
    (Ψ h : Q → Torus d (N₁ * L ^ m₁ * L ^ K) → Fin N → ℂ) (ξ : Q → Fin 3 → ℂ)
    (φ : Q → Gp.Ω 1 × Fin N → ℂ) (α : Q → Gp.Ω 1 → ℂ)
    (hΨ : ∀ x i, AnalyticAt ℂ (fun q => Ψ q x i) q)
    (hh : ∀ x i, AnalyticAt ℂ (fun q => h q x i) q)
    (hξ : ∀ j, AnalyticAt ℂ (fun q => ξ q j) q)
    (hφ : ∀ (y : Gp.Ω 1) i, AnalyticAt ℂ (fun q => φ q (y, i)) q)
    (hα : ∀ y : Gp.Ω 1, AnalyticAt ℂ (fun q => α q y) q) (hq : 1 + ξ q 2 ≠ 0) :
    AnalyticAt ℂ (fun q => ((barField Gp (Ψ q) (φ q), α q + fun _ => renMassU ν (ξ q) - ν,
      fun x i => renZeta eps (ξ q) * Ψ q x i, renF1 ν (ξ q) (h q) (φ q)) : Edat Gp N)) q := by
  have hm : AnalyticAt ℂ (fun q => renMassU ν (ξ q)) q := by
    unfold renMassU
    exact (analyticAt_const.mul (analyticAt_const.add (hξ 1))).div
      (analyticAt_const.add (hξ 2)) hq
  have hz : AnalyticAt ℂ (fun q => renZeta eps (ξ q)) q := by
    unfold renZeta
    exact analyticAt_const.mul (hξ 0)
  refine AnalyticAt.prod ?_ (AnalyticAt.prod ?_ (AnalyticAt.prod ?_ ?_))
  · refine analyticAt_pi_iff.2 fun x => analyticAt_pi_iff.2 fun i => ?_
    by_cases hx : x ∈ Gp.Ω 1
    · have e : (fun q => barField Gp (Ψ q) (φ q) x i) = fun q => φ q (⟨x, hx⟩, i) := by
        funext q; simp [barField, hx]
      rw [e]; exact hφ _ i
    · have e : (fun q => barField Gp (Ψ q) (φ q) x i) = fun q => Ψ q x i := by
        funext q; simp [barField, hx]
      rw [e]; exact hΨ x i
  · exact analyticAt_pi_iff.2 fun y => (hα y).add (hm.sub analyticAt_const)
  · exact analyticAt_pi_iff.2 fun x => analyticAt_pi_iff.2 fun i => hz.mul (hΨ x i)
  · refine analyticAt_pi_iff.2 fun p => ?_
    unfold renF1
    exact (hm.sub analyticAt_const).mul ((hh _ _).sub (hφ p.1 p.2))

variable (Gp) in
/-- **The ambient data map** of the shifted problem: from `((Ψ, h), ξ)` and the cut vector `s`
(indexed by the labels of the cover) to the parameters `s' = extParams (s ∘ renLabelEquiv.symm)`
and the data tuple `(φ̄, α + Δν, ε ξ₀ Ψ, Δν (h - φ))`, where `(φ, α) = F₁ (s', (Ψ, h))`. -/
noncomputable def renDecData (ν eps : ℝ) (X₁ : Set (CTorus d L N₁ m₁ K))
    (F₁ : DecParams Gp × RawData d L (N₁ * L ^ m₁) K N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ))
    (u : RawData d L (N₁ * L ^ m₁) K N × (Fin 3 → ℂ)) (s : RenLabel Gp X₁ → ℂ) :
    DecParams Gp × Edat Gp N :=
  (extParams Gp X₁ (s ∘ (renLabelEquiv Gp X₁).symm),
    (barField Gp u.1.1 (F₁ (extParams Gp X₁ (s ∘ (renLabelEquiv Gp X₁).symm), u.1)).1,
      (F₁ (extParams Gp X₁ (s ∘ (renLabelEquiv Gp X₁).symm), u.1)).2 +
        fun _ => renMassU ν u.2 - ν,
      fun x i => renZeta eps u.2 * u.1.1 x i,
      renF1 ν u.2 u.1.2 (F₁ (extParams Gp X₁ (s ∘ (renLabelEquiv Gp X₁).symm), u.1)).1))

end Data

section Facts

variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {Hm : GeneratingSet d L (N₁ * L ^ m₁) K ϱm}
variable {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ}

/-- For `s` in the open polydisc and a datum of the union domain, the decoupled background exists
and `decBgField`, `decBgMult` are its field and multiplier. -/
theorem exists_decBg'
    (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) {D : BgData Gp N}
    (hU : InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D) {s : DecParams Gp}
    (hs : ∀ P, ‖s P‖ < Real.exp κ) :
    ∃ (φ : Gp.Ω 1 × Fin N → ℂ) (α : Gp.Ω 1 → ℂ),
      IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α ∧
      decBgField Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D = φ ∧
      decBgMult Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D = α := by
  obtain ⟨δ, ε, hδ0, hδε, hε, hδc, hνε, hDC⟩ := hU
  obtain ⟨φ, α, hI, hu, -⟩ := i4b_exists_unique hC.hS hC.Sp hC.HBp hC.hκ.le hC.hM
    (fun P => (hs P).le) hδ0 hδε hε hδc hνε hDC
  exact ⟨φ, α, hI, decBg_eq hI hu⟩

/-- **T1.**  The ambient data map is analytic at every point of `expDom × polydisc` (for
`r₀ ≤ 1/16`), and on the data of `XiCOneReal` it is `(s', renEdat …)` at the decoupled
background of the parameters `s'`. -/
theorem renDecData_analytic
    (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) {r₀ : ℝ} (hr₀ : r₀ ≤ 1 / 16)
    (X₁ : Set (CTorus d L N₁ m₁ K)) :
    ∃ F₁ : DecParams Gp × RawData d L (N₁ * L ^ m₁) K N →
        (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ),
      AnalyticOnNhd ℂ (fun p : (RawData d L (N₁ * L ^ m₁) K N × (Fin 3 → ℂ)) ×
          (RenLabel Gp X₁ → ℂ) => renDecData Gp ν eps X₁ F₁ p.1 p.2)
        (expDom Gp (XiCOneReal Gp (compWeight L a₁) ν eps) r₀ ×ˢ
          polydisc (0 : RenLabel Gp X₁ → ℂ) (fun _ => Real.exp κ)) ∧
      ∀ D : BgData Gp N, XiCOneReal Gp (compWeight L a₁) ν eps D → ∀ ξ : Fin 3 → ℂ,
        ∀ s ∈ polydisc (0 : RenLabel Gp X₁ → ℂ) (fun _ => Real.exp κ),
          renDecData Gp ν eps X₁ F₁ (rawOf D, ξ) s =
            (extParams Gp X₁ (s ∘ (renLabelEquiv Gp X₁).symm),
              renEdat ν eps D
                (decBgField Gp (compWeight L a₁) ν (rho4 d L N BG κ)
                  (extParams Gp X₁ (s ∘ (renLabelEquiv Gp X₁).symm)) D)
                (decBgMult Gp (compWeight L a₁) ν (rho4 d L N BG κ)
                  (extParams Gp X₁ (s ∘ (renLabelEquiv Gp X₁).symm)) D) ξ) := by
  classical
  obtain ⟨F₁, hF₁an, hF₁⟩ := i4b_analytic (N := N) hC.hS hC.Sp hC.HBp hC.hκ.le hC.hM
  have hE1 : 1 < Real.exp κ := Real.one_lt_exp_iff.2 hC.hκ
  refine ⟨F₁, ?_, ?_⟩
  · rintro ⟨u, s⟩ ⟨⟨D, hD, hu1, hu2⟩, hs⟩
    have hs' : ∀ i, ‖s i‖ < Real.exp κ := fun i => by simpa using hs i
    have hU := renXiCOneReal_inUnionC7 hC hD
    have hsx : ∀ P, ‖extParams Gp X₁ (s ∘ (renLabelEquiv Gp X₁).symm) P‖ < Real.exp κ :=
      norm_extParams_lt hE1 (fun i => hs' _)
    set g : ((RawData d L (N₁ * L ^ m₁) K N × (Fin 3 → ℂ)) × (RenLabel Gp X₁ → ℂ)) →
        DecParams Gp × RawData d L (N₁ * L ^ m₁) K N :=
      fun p => (extParams Gp X₁ (p.2 ∘ (renLabelEquiv Gp X₁).symm), p.1.1) with hg
    have hs2 : AnalyticAt ℂ (fun p : (RawData d L (N₁ * L ^ m₁) K N × (Fin 3 → ℂ)) ×
        (RenLabel Gp X₁ → ℂ) => p.2 ∘ (renLabelEquiv Gp X₁).symm) (u, s) :=
      analyticAt_reindex (Gp := Gp) X₁
        (fun p : (RawData d L (N₁ * L ^ m₁) K N × (Fin 3 → ℂ)) × (RenLabel Gp X₁ → ℂ) => p.2)
        fun i =>
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : RenLabel Gp X₁ => ℂ) i).analyticAt _
          |>.comp_of_eq analyticAt_snd rfl
    have hext : AnalyticAt ℂ (fun p : (RawData d L (N₁ * L ^ m₁) K N × (Fin 3 → ℂ)) ×
        (RenLabel Gp X₁ → ℂ) => extParams Gp X₁ (p.2 ∘ (renLabelEquiv Gp X₁).symm)) (u, s) :=
      (analyticAt_extParams _).comp_of_eq hs2 rfl
    have hg0 : AnalyticAt ℂ g (u, s) := hext.prod (analyticAt_fst.comp analyticAt_fst)
    have hF1 : AnalyticAt ℂ (fun p => F₁ (g p)) (u, s) :=
      (hF₁an (g (u, s)) ⟨hsx, D, hU, by rw [hg]; exact hu1⟩).comp_of_eq hg0 rfl
    have hF1' : ∀ (y : Gp.Ω 1) i, AnalyticAt ℂ (fun p => (F₁ (g p)).1 (y, i)) (u, s) :=
      fun y i => (analyticAt_pi_iff.1 (analyticAt_fst.comp hF1) (y, i))
    have hF2' : ∀ y : Gp.Ω 1, AnalyticAt ℂ (fun p => (F₁ (g p)).2 y) (u, s) :=
      fun y => (analyticAt_pi_iff.1 (analyticAt_snd.comp hF1) y)
    have aP : AnalyticAt ℂ (fun p : (RawData d L (N₁ * L ^ m₁) K N × (Fin 3 → ℂ)) ×
        (RenLabel Gp X₁ → ℂ) => p.1.1) (u, s) := analyticAt_fst.comp analyticAt_fst
    have aΨ : AnalyticAt ℂ (fun p : (RawData d L (N₁ * L ^ m₁) K N × (Fin 3 → ℂ)) ×
        (RenLabel Gp X₁ → ℂ) => p.1.1.1) (u, s) := analyticAt_fst.comp aP
    have ah : AnalyticAt ℂ (fun p : (RawData d L (N₁ * L ^ m₁) K N × (Fin 3 → ℂ)) ×
        (RenLabel Gp X₁ → ℂ) => p.1.1.2) (u, s) := analyticAt_snd.comp aP
    have aξ : AnalyticAt ℂ (fun p : (RawData d L (N₁ * L ^ m₁) K N × (Fin 3 → ℂ)) ×
        (RenLabel Gp X₁ → ℂ) => p.1.2) (u, s) := analyticAt_snd.comp analyticAt_fst
    have hΨ : ∀ x i, AnalyticAt ℂ (fun p : (RawData d L (N₁ * L ^ m₁) K N × (Fin 3 → ℂ)) ×
        (RenLabel Gp X₁ → ℂ) => p.1.1.1 x i) (u, s) := fun x i =>
      analyticAt_pi_iff.1 (analyticAt_pi_iff.1 aΨ x) i
    have hh : ∀ x i, AnalyticAt ℂ (fun p : (RawData d L (N₁ * L ^ m₁) K N × (Fin 3 → ℂ)) ×
        (RenLabel Gp X₁ → ℂ) => p.1.1.2 x i) (u, s) := fun x i =>
      analyticAt_pi_iff.1 (analyticAt_pi_iff.1 ah x) i
    have hξ : ∀ j, AnalyticAt ℂ (fun p : (RawData d L (N₁ * L ^ m₁) K N × (Fin 3 → ℂ)) ×
        (RenLabel Gp X₁ → ℂ) => p.1.2 j) (u, s) := fun j => analyticAt_pi_iff.1 aξ j
    have hq : 1 + u.2 2 ≠ 0 := one_add_ne_zero_of_norm (by linarith [hu2]) 2
    exact hext.prod (an_renData (Gp := Gp) ν eps (fun p => p.1.1.1) (fun p => p.1.1.2)
      (fun p => p.1.2) (fun p => (F₁ (g p)).1) (fun p => (F₁ (g p)).2) hΨ hh hξ hF1' hF2' hq)
  · intro D hD ξ s hs
    have hs' : ∀ i, ‖s i‖ < Real.exp κ := fun i => by simpa using hs i
    have hU := renXiCOneReal_inUnionC7 hC hD
    have hsx : ∀ P, ‖extParams Gp X₁ (s ∘ (renLabelEquiv Gp X₁).symm) P‖ < Real.exp κ :=
      norm_extParams_lt hE1 (fun i => hs' _)
    obtain ⟨φ, α, hI, hF, hM⟩ := exists_decBg' hC hU hsx
    have h1 := hF₁ _ D hsx hU φ α hI
    simp only [renDecData, rawOf, h1, hF, hM, renEdat]

/-- **T2.**  The family `F = (δφ, δα) = sol ∘ renDecData` with `sol` from
`i4a_analytic … false D₀ D₁`, `D₀ = 2 K₄ δ + 3 r₀`, `D₁ = b_* ε r₀`: analytic at every point of
`expDom × polydisc`; on the data of `XiCOneReal` with `‖ξ‖ < r₀` it is the `DecFixed` solution
of mode P for `renEdat` at the decoupled background of `s'`, with `Small`/`SupBounds` at
`cK2' · D₁` and uniqueness in the `c6'` ball.  The margins `hδ₀`, `hδ₁` are explicit. -/
theorem renDec_analytic
    (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) {r₀ : ℝ} (hr₀0 : 0 < r₀)
    (hr₀ : r₀ ≤ 1 / 16) (X₁ : Set (CTorus d L N₁ m₁ K))
    (hδ₀ : 2 * (K4 d L N BG κ * (xiC1 d * eps)) + 3 * r₀ ≤
      deltaStar' d L N (famConst d L BG κ) (gamma1 d / 8))
    (hδ₁ : (3 / 2 + 32 / 15 * (3 + (K4 d L N BG κ + bgK1 d L N) * xiC1 d)) * eps * r₀ ≤
      deltaStar' d L N (famConst d L BG κ) (gamma1 d / 8)) :
    ∃ F : RawData d L (N₁ * L ^ m₁) K N × (Fin 3 → ℂ) → (RenLabel Gp X₁ → ℂ) →
        (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ),
      AnalyticOnNhd ℂ (fun p : (RawData d L (N₁ * L ^ m₁) K N × (Fin 3 → ℂ)) ×
          (RenLabel Gp X₁ → ℂ) => F p.1 p.2)
        (expDom Gp (XiCOneReal Gp (compWeight L a₁) ν eps) r₀ ×ˢ
          polydisc (0 : RenLabel Gp X₁ → ℂ) (fun _ => Real.exp κ)) ∧
      ∀ D : BgData Gp N, XiCOneReal Gp (compWeight L a₁) ν eps D → ∀ ξ : Fin 3 → ℂ, ‖ξ‖ < r₀ →
        ∀ s ∈ polydisc (0 : RenLabel Gp X₁ → ℂ) (fun _ => Real.exp κ),
        ∀ (s' : DecParams Gp) (E : Edat Gp N),
          s' = extParams Gp X₁ (s ∘ (renLabelEquiv Gp X₁).symm) →
          E = renEdat ν eps D (decBgField Gp (compWeight L a₁) ν (rho4 d L N BG κ) s' D)
            (decBgMult Gp (compWeight L a₁) ν (rho4 d L N BG κ) s' D) ξ →
          (F (rawOf D, ξ) s).1 = dphi Gp (decG Gp (compWeight L a₁) ν s') E.2.1 E.1
              (pertSource Gp (compWeight L a₁) E.2.2.1 E.2.2.2) (F (rawOf D, ξ) s).2 ∧
          DecFixed Gp (compWeight L a₁) ν s' false E.2.1 E.1
              (pertSource Gp (compWeight L a₁) E.2.2.1 E.2.2.2) (F (rawOf D, ξ) s).2 ∧
          Small Gp (F (rawOf D, ξ) s).2 (c6' d L N (famConst d L BG κ) (gamma1 d / 8)) ∧
          Small Gp (F (rawOf D, ξ) s).2 (cK2' d L N (famConst d L BG κ) *
            ((3 / 2 + 32 / 15 * (3 + (K4 d L N BG κ + bgK1 d L N) * xiC1 d)) * eps * r₀)) ∧
          SupBounds Gp (F (rawOf D, ξ) s).1 (cK2' d L N (famConst d L BG κ) *
            ((3 / 2 + 32 / 15 * (3 + (K4 d L N BG κ + bgK1 d L N) * xiC1 d)) * eps * r₀)) ∧
          (∀ δα' : Gp.Ω 1 → ℂ, Small Gp δα' (c6' d L N (famConst d L BG κ) (gamma1 d / 8)) →
            DecFixed Gp (compWeight L a₁) ν s' false E.2.1 E.1
              (pertSource Gp (compWeight L a₁) E.2.2.1 E.2.2.2) δα' →
            δα' = (F (rawOf D, ξ) s).2) := by
  classical
  obtain ⟨F₁, han, heq⟩ := renDecData_analytic (ν := ν) (eps := eps) hC hr₀ X₁
  have hE1 : 1 < Real.exp κ := Real.one_lt_exp_iff.2 hC.hκ
  have hd0 : 0 < d := by have := hC.HBp.hd; omega
  have hK4 := (K4_pos (L := L) (N := N) (κ := κ) hC.hS.fam.2.1 hd0).le
  have hC1pos : 0 < xiC1 d := by unfold xiC1; positivity
  have hm0 := renMassStar_nonneg hC
  have hε := hC.eps_pos
  have hb0 : 0 ≤ (3 / 2 + 32 / 15 * (3 + (K4 d L N BG κ + bgK1 d L N) * xiC1 d)) * eps * r₀ := by
    positivity
  have hD00 : 0 ≤ 2 * (K4 d L N BG κ * (xiC1 d * eps)) + 3 * r₀ := by positivity
  obtain ⟨sol, hsolan, hsol⟩ := i4a_analytic (N := N) hC.hS.fam hC.hS.an hC.Sp hC.hκ.le hC.hM
    false (δ₀ := 2 * (K4 d L N BG κ * (xiC1 d * eps)) + 3 * r₀)
    (δ₁ := (3 / 2 + 32 / 15 * (3 + (K4 d L N BG κ + bgK1 d L N) * xiC1 d)) * eps * r₀)
    hD00 hb0 hδ₀ hδ₁
  have hmem : ∀ D : BgData Gp N, XiCOneReal Gp (compWeight L a₁) ν eps D → ∀ ξ : Fin 3 → ℂ,
      ‖ξ‖ < r₀ → ∀ s ∈ polydisc (0 : RenLabel Gp X₁ → ℂ) (fun _ => Real.exp κ),
      (∀ P, ‖(renDecData Gp ν eps X₁ F₁ (rawOf D, ξ) s).1 P‖ < Real.exp κ) ∧
      StrictDataM Gp N false (2 * (K4 d L N BG κ * (xiC1 d * eps)) + 3 * r₀)
        ((3 / 2 + 32 / 15 * (3 + (K4 d L N BG κ + bgK1 d L N) * xiC1 d)) * eps * r₀)
        (renDecData Gp ν eps X₁ F₁ (rawOf D, ξ) s).2 := by
    intro D hD ξ hξ s hs
    have hs' : ∀ i, ‖s i‖ < Real.exp κ := fun i => by simpa using hs i
    have hsx : ∀ P, ‖extParams Gp X₁ (s ∘ (renLabelEquiv Gp X₁).symm) P‖ < Real.exp κ :=
      norm_extParams_lt hE1 (fun i => hs' _)
    rw [heq D hD ξ s hs]
    exact ⟨hsx, renEdat_strictDataM_of_flCore hC hD (fun P => (hsx P).le) hr₀ hξ⟩
  refine ⟨fun u s => sol (renDecData Gp ν eps X₁ F₁ u s), ?_, ?_⟩
  · intro p hp
    obtain ⟨⟨D, hD, hu1, hu2⟩, hs⟩ := hp
    have hu : p.1 = (rawOf D, p.1.2) := Prod.ext hu1 rfl
    have := hmem D hD p.1.2 hu2 p.2 hs
    rw [← hu] at this
    exact (hsolan _ this).comp_of_eq (han p ⟨⟨D, hD, hu1, hu2⟩, hs⟩) (by rw [hu])
  · intro D hD ξ hξ s hs s' E hs' hE
    subst hs' hE
    have hm := hmem D hD ξ hξ s hs
    rw [heq D hD ξ s hs] at hm
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hsol _ hm.1 hm.2
    simp only [heq D hD ξ s hs]
    exact ⟨h1, h2, h3, h4, h5, h6⟩

/-- **T3 (the two-radius argument).**  The family `F` of `renDec_analytic` satisfies the sharp
bounds `cK2' · b_* ε ‖ξ‖` on `Small`/`SupBounds` for each admitted `(D, ξ, s)`, `‖ξ‖ < r₀`:
`i4a_exists_unique` at the radii `(D₀, b_* ε ‖ξ‖)` produces a solution with the sharp bound, and
the uniqueness clause in the `c6'` ball identifies it with `F`.  For `ξ = 0` both `δα` and `δφ`
vanish.  The extra margin is `D₀ ≤ 1` (supplied by `renMargins_exists_r₀_of_flCore`). -/
theorem renDec_sharp
    (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) {r₀ : ℝ} (hr₀0 : 0 < r₀)
    (hr₀ : r₀ ≤ 1 / 16) (X₁ : Set (CTorus d L N₁ m₁ K))
    (hD₀ : 2 * (K4 d L N BG κ * (xiC1 d * eps)) + 3 * r₀ ≤ 1)
    (hδ₀ : 2 * (K4 d L N BG κ * (xiC1 d * eps)) + 3 * r₀ ≤
      deltaStar' d L N (famConst d L BG κ) (gamma1 d / 8))
    (hδ₁ : (3 / 2 + 32 / 15 * (3 + (K4 d L N BG κ + bgK1 d L N) * xiC1 d)) * eps * r₀ ≤
      deltaStar' d L N (famConst d L BG κ) (gamma1 d / 8)) :
    ∃ F : RawData d L (N₁ * L ^ m₁) K N × (Fin 3 → ℂ) → (RenLabel Gp X₁ → ℂ) →
        (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ),
      AnalyticOnNhd ℂ (fun p : (RawData d L (N₁ * L ^ m₁) K N × (Fin 3 → ℂ)) ×
          (RenLabel Gp X₁ → ℂ) => F p.1 p.2)
        (expDom Gp (XiCOneReal Gp (compWeight L a₁) ν eps) r₀ ×ˢ
          polydisc (0 : RenLabel Gp X₁ → ℂ) (fun _ => Real.exp κ)) ∧
      ∀ D : BgData Gp N, XiCOneReal Gp (compWeight L a₁) ν eps D → ∀ ξ : Fin 3 → ℂ, ‖ξ‖ < r₀ →
        ∀ s ∈ polydisc (0 : RenLabel Gp X₁ → ℂ) (fun _ => Real.exp κ),
        ∀ (s' : DecParams Gp) (E : Edat Gp N),
          s' = extParams Gp X₁ (s ∘ (renLabelEquiv Gp X₁).symm) →
          E = renEdat ν eps D (decBgField Gp (compWeight L a₁) ν (rho4 d L N BG κ) s' D)
            (decBgMult Gp (compWeight L a₁) ν (rho4 d L N BG κ) s' D) ξ →
          (F (rawOf D, ξ) s).1 = dphi Gp (decG Gp (compWeight L a₁) ν s') E.2.1 E.1
              (pertSource Gp (compWeight L a₁) E.2.2.1 E.2.2.2) (F (rawOf D, ξ) s).2 ∧
          DecFixed Gp (compWeight L a₁) ν s' false E.2.1 E.1
              (pertSource Gp (compWeight L a₁) E.2.2.1 E.2.2.2) (F (rawOf D, ξ) s).2 ∧
          Small Gp (F (rawOf D, ξ) s).2 (c6' d L N (famConst d L BG κ) (gamma1 d / 8)) ∧
          Small Gp (F (rawOf D, ξ) s).2 (cK2' d L N (famConst d L BG κ) *
            ((3 / 2 + 32 / 15 * (3 + (K4 d L N BG κ + bgK1 d L N) * xiC1 d)) * eps * ‖ξ‖)) ∧
          SupBounds Gp (F (rawOf D, ξ) s).1 (cK2' d L N (famConst d L BG κ) *
            ((3 / 2 + 32 / 15 * (3 + (K4 d L N BG κ + bgK1 d L N) * xiC1 d)) * eps * ‖ξ‖)) ∧
          (ξ = 0 → (F (rawOf D, ξ) s).2 = 0 ∧ (F (rawOf D, ξ) s).1 = 0) := by
  classical
  obtain ⟨F, han, hpt⟩ := renDec_analytic hC hr₀0 hr₀ X₁ hδ₀ hδ₁
  have hE1 : 1 < Real.exp κ := Real.one_lt_exp_iff.2 hC.hκ
  have hm0 := renMassStar_nonneg hC
  have hε := hC.eps_pos
  refine ⟨F, han, ?_⟩
  intro D hD ξ hξ s hs s' E hs' hE
  obtain ⟨h1, h2, h3, -, -, h6⟩ := hpt D hD ξ hξ s hs s' E hs' hE
  have hs'' : ∀ i, ‖s i‖ < Real.exp κ := fun i => by simpa using hs i
  have hsx : ∀ P, ‖s' P‖ ≤ Real.exp κ := by
    subst hs'
    exact fun P => (norm_extParams_lt hE1 (fun i => hs'' _) P).le
  have hH := renEdat_decHyp_of_flCore hC hD hsx hr₀ hξ hD₀
  have hδr : (3 / 2 + 32 / 15 * (3 + (K4 d L N BG κ + bgK1 d L N) * xiC1 d)) * eps * ‖ξ‖ ≤
      deltaStar' d L N (famConst d L BG κ) (gamma1 d / 8) := by
    refine le_trans ?_ hδ₁
    have : 0 ≤ (3 / 2 + 32 / 15 * (3 + (K4 d L N BG κ + bgK1 d L N) * xiC1 d)) * eps := by
      positivity
    exact mul_le_mul_of_nonneg_left hξ.le this
  obtain ⟨δα, hfix, hs6, hsK, hdp, huniq, hzero⟩ := i4a_exists_unique hC.hS.fam Gp hC.Sp
    hC.hκ.le hC.hM hsx hH hδ₀ hδr
  subst hE
  have hFeq : (F (rawOf D, ξ) s).2 = δα := (h6 δα hs6 hfix).symm
  have hFeq1 := h1
  rw [hFeq] at hFeq1
  refine ⟨h1, h2, h3, ?_, ?_, ?_⟩
  · rw [hFeq]; exact hsK
  · rw [hFeq1]; exact hdp
  · intro hξ0
    have hz0 : (renEdat ν eps D (decBgField Gp (compWeight L a₁) ν (rho4 d L N BG κ) s' D)
        (decBgMult Gp (compWeight L a₁) ν (rho4 d L N BG κ) s' D) ξ).2.2.1 = 0 ∧
        (renEdat ν eps D (decBgField Gp (compWeight L a₁) ν (rho4 d L N BG κ) s' D)
        (decBgMult Gp (compWeight L a₁) ν (rho4 d L N BG κ) s' D) ξ).2.2.2 = 0 := by
      subst hξ0
      refine ⟨?_, ?_⟩
      · funext x i; simp [renEdat, renZeta]
      · funext p; simp [renEdat, renF1, renMassU]
    obtain ⟨hδα0, hdp0⟩ := hzero rfl hz0.1 hz0.2
    exact ⟨hFeq.trans hδα0, hFeq1.trans hdp0⟩

end Facts

end Balaban.Localization
