/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.RenormDecAnalytic
public import Balaban.Fluctuation.RenormStrictData
public import Balaban.Fluctuation.RenormExpLemma35
public import Balaban.Background.ExistenceSetup
public import Balaban.Background.Prop51Mass
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The endpoint `s = 1` of the shifted perturbation problem

The cut family of `renDec_sharp` (mode P of Theorem I-4a, data `renEdat`) is identified, at the
all-ones cut, with the renormalized solution `F` of `IsRenSol`.

* `gdef_eq_zero_of_unit`, `DecHyp.toU_of_unit`, `decFixed_true_of_false`: when the base field has
  `φ₀ · φ₀ = 1` on `Ω₁`, the defect `gdef` vanishes, so the term `(1/2) H₀ gdef` of `Nmap` is zero
  and a mode-P fixed point is a mode-U fixed point (the `g0`, `gl` clauses of `DecHyp` in mode U
  hold trivially).
* `gdef_barField_bgFieldC`: the base field `φ̄` of the true background has `gdef = 0`.
* `renDec_one_unique_of_fixed`: a mode-P fixed point at the all-ones cut, small in the `rho4` ball,
  is the `IsRenSol` solution.
* `renDec_one_unique`: the family of `renDec_sharp` at `s = 1` is the `IsRenSol` solution.

Not here: class bounds, locality, and the fields `locC2`, `locDφ`.  Nothing is said about
`s ≠ 1`.  The comparison `rho4 ≤ c6` is not derivable from the landed definitions
(`rho4 = c6' … (γ₁/8)` involves `famConst`, `c6` involves the unrelated constant `greenSupConst`);
it is the named hypothesis `hball`.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Analysis
  Finset Matrix

section Bridge

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ}

/-- If `φ₀ · φ₀ = 1` on `Ω₁` the defect `g = φ₀ · φ₀ - 1` vanishes. -/
theorem gdef_eq_zero_of_unit {φ₀ : CTorus d L N₁ m₁ K → Fin N → ℂ}
    (hg : ∀ x ∈ G.Ω 1, φ₀ x ⬝ᵥ φ₀ x = 1) : gdef G φ₀ = 0 := by
  funext y
  have := hg y y.2
  simp only [gdef, Pi.zero_apply]
  rw [sub_eq_zero]; exact this

/-- **The mode bridge for the hypotheses**: `DecHyp` in mode P and `φ₀ · φ₀ = 1` on `Ω₁` give
`DecHyp` in mode U (the clauses `g0`, `gl` are about `gdef`, which is zero). -/
theorem DecHyp.toU_of_unit {α₀ : G.Ω 1 → ℂ} {φ₀ δΨ : CTorus d L N₁ m₁ K → Fin N → ℂ}
    {f₁ : G.Ω 1 × Fin N → ℂ} {δ₀ δ₁ : ℝ}
    (H : DecHyp G a ν false α₀ φ₀ δΨ f₁ δ₀ δ₁) (hg : ∀ x ∈ G.Ω 1, φ₀ x ⬝ᵥ φ₀ x = 1) :
    DecHyp G a ν true α₀ φ₀ δΨ f₁ δ₀ δ₁ := by
  have h0 := gdef_eq_zero_of_unit (G := G) hg
  refine ⟨H.green, H.δ₀_nn, H.δ₁_nn, H.δ₀_le, H.smooth, H.phiBd, H.alpha0, H.f₁_bd, H.dPsi,
    fun _ x => ?_, fun _ x => ?_⟩
  · rw [h0]; simpa using H.δ₁_nn
  · have := negLap_zeroExt_gdef (G := G) hg (x : CTorus d L N₁ m₁ K)
    rw [this, norm_zero, mul_zero]; exact H.δ₁_nn

/-- **The mode bridge for the fixed point**: with `φ₀ · φ₀ = 1` on `Ω₁` the only difference of the
maps `𝒩` of the two modes, `(1/2) H₀ gdef(φ₀)`, is zero, so a mode-P fixed point is a mode-U
fixed point. -/
theorem decFixed_true_of_false {s : DecParams G} {α₀ : G.Ω 1 → ℂ}
    {φ₀ : CTorus d L N₁ m₁ K → Fin N → ℂ} {Fs : G.Ω 1 × Fin N → ℂ} {δα : G.Ω 1 → ℂ}
    (hg : ∀ x ∈ G.Ω 1, φ₀ x ⬝ᵥ φ₀ x = 1)
    (h : DecFixed G a ν s false α₀ φ₀ Fs δα) : DecFixed G a ν s true α₀ φ₀ Fs δα := by
  have h0 := gdef_eq_zero_of_unit (G := G) hg
  unfold DecFixed at h ⊢
  refine Eq.trans ?_ h
  funext x
  simp [Nmap, h0]

/-- The extension `φ̄` of a field with `φ · φ = 1` on `Ω₁` (the constraint of `IsEL`) has
`φ̄ · φ̄ = 1` on `Ω₁`, hence `gdef = 0`. -/
theorem barField_unit {Ψ : CTorus d L N₁ m₁ K → Fin N → ℂ} {φ : G.Ω 1 × Fin N → ℂ}
    (h : ∀ x : G.Ω 1, ∑ i, φ (x, i) * φ (x, i) = 1) :
    ∀ x ∈ G.Ω 1, barField G Ψ φ x ⬝ᵥ barField G Ψ φ x = 1 := by
  intro x hx
  have := h ⟨x, hx⟩
  simpa [dotProduct, barField, hx] using this

/-- **The defect of the true background vanishes**: for a small solution `(φ, α)` the extension
`φ̄` has `gdef G (barField G Ψ φ) = 0` (the unit-length equation of `IsSmallSolution`). -/
theorem gdef_barField_eq_zero {c₀ : ℝ} {D : BgData G N} {φ : G.Ω 1 × Fin N → ℂ}
    {α : G.Ω 1 → ℂ} (h : IsSmallSolution G a ν c₀ D φ α) :
    gdef G (barField G D.Ψ φ) = 0 :=
  gdef_eq_zero_of_unit (barField_unit h.1.2)

end Bridge

section Endpoint

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {Hm : GeneratingSet d L (N₁ * L ^ m₁) K ϱm}
variable {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ}

/-- **The endpoint, pointwise.**  At the all-ones cut, let `(φ₁, α₁)` be the decoupled background
(`hbg`), and let `δα` be a mode-P fixed point of the shifted problem (`hfix`, data `renEdat`) that
is small in the ball `rho4` (`hsmall`).  Then `(dphi …, δα)` is the `IsRenSol` solution
`F ((D.Ψ, D.h), ξ)`.  The margins are the named hypotheses `hDzero`, `hDstar`, `hDone`, `hrF`,
`hball`. -/
theorem renDec_one_unique_of_fixed
    (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) {r₀ rF B : ℝ}
    {F : RawData d L (N₁ * L ^ m₁) K N × (Fin 3 → ℂ) → (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    (hF : IsRenSol (N := N) Gp (compWeight L a₁) ν eps eps rF B F)
    (hr₀ : r₀ ≤ 1 / 16) (hrF : r₀ ≤ rF)
    (hDzero : 2 * (K4 d L N BG κ * (xiC1 d * eps)) + 3 * r₀ ≤ 1)
    (hDstar : 2 * (K4 d L N BG κ * (xiC1 d * eps)) + 3 * r₀ ≤
      deltaStar' d L N (famConst d L BG κ) (gamma1 d / 8))
    (hDone : (3 / 2 + 32 / 15 * (3 + (K4 d L N BG κ + bgK1 d L N) * xiC1 d)) * eps * r₀ ≤
      deltaStar' d L N (famConst d L BG κ) (gamma1 d / 8))
    (hball : rho4 d L N BG κ ≤ c6 d L N)
    {D : BgData Gp N} (hD : XiCOneReal Gp (compWeight L a₁) ν eps D) {ξ : Fin 3 → ℂ}
    (hξ : ‖ξ‖ < r₀) {φ₁ : Gp.Ω 1 × Fin N → ℂ} {α₁ : Gp.Ω 1 → ℂ}
    (hbg : IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) (fun _ => 1) D φ₁ α₁)
    {δα : Gp.Ω 1 → ℂ}
    (hfix : DecFixed Gp (compWeight L a₁) ν (fun _ => 1) false
      (renEdat ν eps D φ₁ α₁ ξ).2.1 (renEdat ν eps D φ₁ α₁ ξ).1
      (pertSource Gp (compWeight L a₁) (renEdat ν eps D φ₁ α₁ ξ).2.2.1
        (renEdat ν eps D φ₁ α₁ ξ).2.2.2) δα)
    (hsmall : Small Gp δα (rho4 d L N BG κ)) :
    dphi Gp (decG Gp (compWeight L a₁) ν (fun _ => 1)) (renEdat ν eps D φ₁ α₁ ξ).2.1
        (renEdat ν eps D φ₁ α₁ ξ).1
        (pertSource Gp (compWeight L a₁) (renEdat ν eps D φ₁ α₁ ξ).2.2.1
          (renEdat ν eps D φ₁ α₁ ξ).2.2.2) δα = (F ((D.Ψ, D.h), ξ)).1 ∧
      δα = (F ((D.Ψ, D.h), ξ)).2 := by
  have hs1 : ∀ P, ‖(fun _ : ↥(cubeIdx Gp) => (1 : ℂ)) P‖ ≤ Real.exp κ := fun P => by
    simpa using Real.one_le_exp hC.hκ.le
  have hU := renXiCOneReal_inUnionC7 hC hD
  obtain ⟨δ, ε, hδ0, hδε, hε, hδc, hνε, hDC⟩ := hU
  obtain ⟨hsol, hbf, hbm⟩ := i4b_one hC.hS hC.Sp hC.HBp hC.hκ.le hC.hM hδ0 hδε hε hδc hνε hDC hbg
  obtain ⟨φ', α', hI, hu, -⟩ := i4b_exists_unique hC.hS hC.Sp hC.HBp hC.hκ.le hC.hM
    (s := fun _ => 1) hs1 hδ0 hδε hε hδc hνε hDC
  obtain ⟨u1, u2⟩ := hu φ₁ α₁ hbg
  obtain ⟨e1, e2⟩ := decBg_eq hI hu
  have hH := renEdat_decHyp_of_flCore hC hD hs1 hr₀ hξ hDzero
  rw [e1, e2, ← u1, ← u2] at hH
  have hg := barField_unit (Ψ := D.Ψ) hsol.1.2
  have hHU := hH.toU_of_unit hg
  have hδr : (3 / 2 + 32 / 15 * (3 + (K4 d L N BG κ + bgK1 d L N) * xiC1 d)) * eps * ‖ξ‖ ≤
      deltaStar' d L N (famConst d L BG κ) (gamma1 d / 8) := by
    refine le_trans ?_ hDone
    have := renMassStar_nonneg hC
    have := hC.eps_pos
    exact mul_le_mul_of_nonneg_left hξ.le (by positivity)
  have hfixU := decFixed_true_of_false hg hfix
  have hP := isPerturbed_of_decFixed_one hC.hS hC.Sp hC.hκ.le hC.hM hHU hDstar hδr hfixU hsmall
  have hPM : IsPerturbedM Gp (compWeight L a₁) (renMassU ν ξ)
      (bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D)
      (barField Gp D.Ψ (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D))
      (pertSource Gp (compWeight L a₁) (fun x i => renZeta eps ξ * D.Ψ x i)
        (renF1 ν ξ D.h (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D)))
      (dphi Gp (decG Gp (compWeight L a₁) ν (fun _ => 1)) (renEdat ν eps D φ₁ α₁ ξ).2.1
        (renEdat ν eps D φ₁ α₁ ξ).1
        (pertSource Gp (compWeight L a₁) (renEdat ν eps D φ₁ α₁ ξ).2.2.1
          (renEdat ν eps D φ₁ α₁ ξ).2.2.2) δα) δα := by
    rw [isPerturbedM_iff Gp (compWeight L a₁) ν]
    rw [hbf, hbm]
    exact hP
  exact hF.unique D hD.xiCOne ξ (hξ.trans_le hrF) _ _ hPM
    (fun x => (hsmall x).trans hball)

/-- **`renDec_one_unique`.**  The cut family of `renDec_sharp` at the all-ones cut vector
(`s = 1`, with `extParams_one`) is the `IsRenSol` solution `F`: `(δφ₁, δα₁) = F ((D.Ψ, D.h), ξ)`
for every datum of `XiCOneReal` and every `‖ξ‖ < r₀`.  The margins `hDzero`, `hDstar`, `hDone`,
`hrF`, `hball` are as in `renDec_one_unique_of_fixed`. -/
theorem renDec_one_unique
    (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) {r₀ rF B : ℝ} (hr₀0 : 0 < r₀)
    (hr₀ : r₀ ≤ 1 / 16) (X₁ : Set (CTorus d L N₁ m₁ K))
    {F : RawData d L (N₁ * L ^ m₁) K N × (Fin 3 → ℂ) → (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    (hF : IsRenSol (N := N) Gp (compWeight L a₁) ν eps eps rF B F) (hrF : r₀ ≤ rF)
    (hDzero : 2 * (K4 d L N BG κ * (xiC1 d * eps)) + 3 * r₀ ≤ 1)
    (hDstar : 2 * (K4 d L N BG κ * (xiC1 d * eps)) + 3 * r₀ ≤
      deltaStar' d L N (famConst d L BG κ) (gamma1 d / 8))
    (hDone : (3 / 2 + 32 / 15 * (3 + (K4 d L N BG κ + bgK1 d L N) * xiC1 d)) * eps * r₀ ≤
      deltaStar' d L N (famConst d L BG κ) (gamma1 d / 8))
    (hball : rho4 d L N BG κ ≤ c6 d L N) :
    ∃ Fcut : RawData d L (N₁ * L ^ m₁) K N × (Fin 3 → ℂ) → (RenLabel Gp X₁ → ℂ) →
        (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ),
      AnalyticOnNhd ℂ (fun p : (RawData d L (N₁ * L ^ m₁) K N × (Fin 3 → ℂ)) ×
          (RenLabel Gp X₁ → ℂ) => Fcut p.1 p.2)
        (expDom Gp (XiCOneReal Gp (compWeight L a₁) ν eps) r₀ ×ˢ
          polydisc (0 : RenLabel Gp X₁ → ℂ) (fun _ => Real.exp κ)) ∧
      ∀ D : BgData Gp N, XiCOneReal Gp (compWeight L a₁) ν eps D → ∀ ξ : Fin 3 → ℂ,
        ‖ξ‖ < r₀ → Fcut (rawOf D, ξ) 1 = F ((D.Ψ, D.h), ξ) := by
  classical
  obtain ⟨Fcut, han, hpt⟩ := renDec_sharp hC hr₀0 hr₀ X₁ hDzero hDstar hDone
  refine ⟨Fcut, han, ?_⟩
  intro D hD ξ hξ
  have hs1 : ∀ P, ‖(fun _ : ↥(cubeIdx Gp) => (1 : ℂ)) P‖ ≤ Real.exp κ := fun P => by
    simpa using Real.one_le_exp hC.hκ.le
  have hmem : (1 : RenLabel Gp X₁ → ℂ) ∈ polydisc (0 : RenLabel Gp X₁ → ℂ)
      (fun _ => Real.exp κ) := fun i => by
    simpa using Real.one_lt_exp_iff.2 hC.hκ
  have hext : extParams Gp X₁ ((1 : RenLabel Gp X₁ → ℂ) ∘ (renLabelEquiv Gp X₁).symm) =
      fun _ => 1 := by
    have h1 : (1 : RenLabel Gp X₁ → ℂ) ∘ (renLabelEquiv Gp X₁).symm = 1 := rfl
    rw [h1, extParams_one]
  obtain ⟨hU⟩ : Nonempty (InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D) :=
    ⟨renXiCOneReal_inUnionC7 hC hD⟩
  obtain ⟨δ, ε, hδ0, hδε, hε, hδc, hνε, hDC⟩ := hU
  obtain ⟨φ, α, hI, hu, -⟩ := i4b_exists_unique hC.hS hC.Sp hC.HBp hC.hκ.le hC.hM
    (s := fun _ => 1) hs1 hδ0 hδε hε hδc hνε hDC
  obtain ⟨e1, e2⟩ := decBg_eq hI hu
  obtain ⟨h1, h2, h3, -⟩ := hpt D hD ξ hξ 1 hmem (fun _ => 1) _ hext.symm rfl
  rw [e1, e2] at h1 h2
  have key := renDec_one_unique_of_fixed hC hF hr₀ hrF hDzero hDstar hDone hball hD hξ hI h2
    (δα := (Fcut (rawOf D, ξ) 1).2) h3
  exact Prod.ext (h1.trans key.1) key.2

end Endpoint

end Balaban.Localization
