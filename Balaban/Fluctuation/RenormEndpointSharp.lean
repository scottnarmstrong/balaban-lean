/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.RenormEndpoint
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The endpoint `s = 1` without the ball comparison

`renDec_one_unique` carries the hypothesis `rho4 ≤ c6`, which is not derivable from the landed
constants.  It is used only to pass from the ball of radius `rho4` to the ball of radius `c6`
for the cut family.  The cut family satisfies the bound `K₂' b_* ε ‖ξ‖` of `renDec_sharp`, so the
inequality
`K₂' (b_* ε r₀) ≤ c6`
(payable by shrinking `r₀`) replaces it; the smallness in the `rho4` ball is the first clause of
`renDec_sharp` itself (`rho4 = c6'(famConst, γ₁/8)`).

* `Small.mono`: smallness is monotone in the radius.
* `rho4_pos`: positivity of the radius `rho4`.
* `renDec_one_unique_of_fixed'`: the pointwise endpoint with the smallness in both balls given.
* `renDec_one_unique_sharp`: the endpoint theorem with the margin `hM2`.
* `exists_radius_margins`: for positive targets the margins hold for all small radii.

Not here: class bounds, locality, and the fields `locC2`, `locDφ`.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Analysis
  Finset Matrix

section Margins

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}

/-- Smallness is monotone in the radius. -/
theorem _root_.Balaban.Background.Small.mono {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {δα : G.Ω 1 → ℂ} {r s : ℝ}
    (h : Small G δα r) (hrs : r ≤ s) : Small G δα s := fun x => (h x).trans hrs

omit [NeZero L] in
/-- `rho4 > 0` for a nonnegative `BG` and `d > 0`. -/
theorem rho4_pos {BG κ : ℝ} (hd : 0 < d) (hBG : 0 ≤ BG) : 0 < rho4 d L N BG κ := by
  have hB1 := famConst_ge_one (L := L) hBG κ hd
  unfold rho4
  exact c6'_pos (by linarith) (by have := gamma1_pos hd; positivity)

/-- For positive targets `P, Q`, positive `r₀, rF` and `A ≥ 0` there is a radius `r ∈ (0, r₀]`
with `r ≤ rF`, `A r ≤ P` and `A r ≤ Q`. -/
theorem exists_radius_margins {A P Q r₀ rF : ℝ} (hA : 0 ≤ A) (hP : 0 < P) (hQ : 0 < Q)
    (hr₀ : 0 < r₀) (hrF : 0 < rF) :
    ∃ r : ℝ, 0 < r ∧ r ≤ r₀ ∧ r ≤ rF ∧ A * r ≤ P ∧ A * r ≤ Q := by
  have h1 : 0 < P / (A + 1) := div_pos hP (by linarith)
  have h2 : 0 < Q / (A + 1) := div_pos hQ (by linarith)
  refine ⟨min (min r₀ rF) (min (P / (A + 1)) (Q / (A + 1))), ?_, ?_, ?_, ?_, ?_⟩
  · exact lt_min (lt_min hr₀ hrF) (lt_min h1 h2)
  · exact (min_le_left _ _).trans (min_le_left _ _)
  · exact (min_le_left _ _).trans (min_le_right _ _)
  · have h : min (min r₀ rF) (min (P / (A + 1)) (Q / (A + 1))) ≤ P / (A + 1) :=
      (min_le_right _ _).trans (min_le_left _ _)
    calc A * _ ≤ A * (P / (A + 1)) := mul_le_mul_of_nonneg_left h hA
      _ ≤ P := by
          rw [← mul_div_assoc, div_le_iff₀ (by linarith)]
          nlinarith
  · have h : min (min r₀ rF) (min (P / (A + 1)) (Q / (A + 1))) ≤ Q / (A + 1) :=
      (min_le_right _ _).trans (min_le_right _ _)
    calc A * _ ≤ A * (Q / (A + 1)) := mul_le_mul_of_nonneg_left h hA
      _ ≤ Q := by
          rw [← mul_div_assoc, div_le_iff₀ (by linarith)]
          nlinarith

end Margins

section Endpoint

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {Hm : GeneratingSet d L (N₁ * L ^ m₁) K ϱm}
variable {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ}

/-- **The endpoint, pointwise, with the smallness in both balls.**  As
`renDec_one_unique_of_fixed`, with `hball` replaced by the smallness `hsmall6` of the fixed point
in the ball of radius `c6` (the radius that `IsRenSol.unique` needs). -/
theorem renDec_one_unique_of_fixed'
    (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) {r₀ rF B : ℝ}
    {F : RawData d L (N₁ * L ^ m₁) K N × (Fin 3 → ℂ) → (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    (hF : IsRenSol (N := N) Gp (compWeight L a₁) ν eps eps rF B F)
    (hr₀ : r₀ ≤ 1 / 16) (hrF : r₀ ≤ rF)
    (hDzero : 2 * (K4 d L N BG κ * (xiC1 d * eps)) + 3 * r₀ ≤ 1)
    (hDstar : 2 * (K4 d L N BG κ * (xiC1 d * eps)) + 3 * r₀ ≤
      deltaStar' d L N (famConst d L BG κ) (gamma1 d / 8))
    (hDone : (3 / 2 + 32 / 15 * (3 + (K4 d L N BG κ + bgK1 d L N) * xiC1 d)) * eps * r₀ ≤
      deltaStar' d L N (famConst d L BG κ) (gamma1 d / 8))
    {D : BgData Gp N} (hD : XiCOneReal Gp (compWeight L a₁) ν eps D) {ξ : Fin 3 → ℂ}
    (hξ : ‖ξ‖ < r₀) {φ₁ : Gp.Ω 1 × Fin N → ℂ} {α₁ : Gp.Ω 1 → ℂ}
    (hbg : IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) (fun _ => 1) D φ₁ α₁)
    {δα : Gp.Ω 1 → ℂ}
    (hfix : DecFixed Gp (compWeight L a₁) ν (fun _ => 1) false
      (renEdat ν eps D φ₁ α₁ ξ).2.1 (renEdat ν eps D φ₁ α₁ ξ).1
      (pertSource Gp (compWeight L a₁) (renEdat ν eps D φ₁ α₁ ξ).2.2.1
        (renEdat ν eps D φ₁ α₁ ξ).2.2.2) δα)
    (hsmall : Small Gp δα (rho4 d L N BG κ)) (hsmall6 : Small Gp δα (c6 d L N)) :
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
  exact hF.unique D hD.xiCOne ξ (hξ.trans_le hrF) _ _ hPM hsmall6

/-- **`renDec_one_unique_sharp`.**  The cut family of `renDec_sharp` at the all-ones cut is the
`IsRenSol` solution `F`, for every datum of `XiCOneReal` and every `‖ξ‖ < r₀`, under the
margin `hM2` (the sharp bound at radius `r₀` fits in the ball `c6`).  It replaces the hypothesis
`rho4 ≤ c6` of `renDec_one_unique`.  The companion margin into the ball `rho4` is not needed:
`rho4` is by definition the radius `c6'(famConst, γ₁/8)` of the first clause of `renDec_sharp`. -/
theorem renDec_one_unique_sharp
    (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) {r₀ rF B : ℝ} (hr₀0 : 0 < r₀)
    (hr₀ : r₀ ≤ 1 / 16) (X₁ : Set (CTorus d L N₁ m₁ K))
    {F : RawData d L (N₁ * L ^ m₁) K N × (Fin 3 → ℂ) → (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    (hF : IsRenSol (N := N) Gp (compWeight L a₁) ν eps eps rF B F) (hrF : r₀ ≤ rF)
    (hDzero : 2 * (K4 d L N BG κ * (xiC1 d * eps)) + 3 * r₀ ≤ 1)
    (hDstar : 2 * (K4 d L N BG κ * (xiC1 d * eps)) + 3 * r₀ ≤
      deltaStar' d L N (famConst d L BG κ) (gamma1 d / 8))
    (hDone : (3 / 2 + 32 / 15 * (3 + (K4 d L N BG κ + bgK1 d L N) * xiC1 d)) * eps * r₀ ≤
      deltaStar' d L N (famConst d L BG κ) (gamma1 d / 8))
    (hM2 : cK2' d L N (famConst d L BG κ) *
      ((3 / 2 + 32 / 15 * (3 + (K4 d L N BG κ + bgK1 d L N) * xiC1 d)) * eps * r₀) ≤
        c6 d L N) :
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
  obtain ⟨h1, h2, h3, h4, -⟩ := hpt D hD ξ hξ 1 hmem (fun _ => 1) _ hext.symm rfl
  rw [e1, e2] at h1 h2
  have hb : 0 ≤ (3 / 2 + 32 / 15 * (3 + (K4 d L N BG κ + bgK1 d L N) * xiC1 d)) * eps := by
    have := renMassStar_nonneg hC
    have := hC.eps_pos
    positivity
  have hK2 : cK2' d L N (famConst d L BG κ) *
      ((3 / 2 + 32 / 15 * (3 + (K4 d L N BG κ + bgK1 d L N) * xiC1 d)) * eps * ‖ξ‖) ≤
      cK2' d L N (famConst d L BG κ) *
      ((3 / 2 + 32 / 15 * (3 + (K4 d L N BG κ + bgK1 d L N) * xiC1 d)) * eps * r₀) := by
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hξ.le hb) ?_
    have hd0 : 0 < d := by have := hC.HBp.hd; omega
    have := famConst_ge_one (d := d) (L := L) hC.hS.fam.2.1 κ hd0
    exact cK2'_nonneg (d := d) (L := L) (N := N) (B := famConst d L BG κ) (by linarith)
  have key := renDec_one_unique_of_fixed' hC hF hr₀ hrF hDzero hDstar hDone hD hξ hI h2
    (δα := (Fcut (rawOf D, ξ) 1).2) h3 (h4.mono (hK2.trans hM2))
  exact Prod.ext (h1.trans key.1) key.2

end Endpoint

end Balaban.Localization
