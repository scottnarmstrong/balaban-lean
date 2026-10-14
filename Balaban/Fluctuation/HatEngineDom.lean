/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.InteractionEngine
public import Balaban.Localization.DecoupledCovAnalyticFull
import Balaban.SmallField.PsiGeomSlice
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The decoupled background lies in the domain `DecDom` of the decoupled covariance

For a datum `D ∈ Ξ^c(𝔹_{k+1}; 1, ε)` and decoupling parameters `s` with `|s_P| < e^κ`, the
decoupled background `(φ(s), α(s))` of Theorem I-4b (`IsDecBg`) has the extension
`φ̄ = barField Gp D.Ψ φ` as strict constraint field, and its multiplier is admissible:
`(s, (φ̄, α)) ∈ DecDom Gp N κ δc`, as soon as `δc` exceeds the explicit margin
`decDomMargin` and `K₄ δ < γ/2` (`γ` the coercivity constant).  The smallness condition
`δc² smallConstX ≤ 1/4` of the covariance analyticity is a separate hypothesis of its consumers.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Analysis Finset Matrix

section Dom

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}

/-- The margin of the strict constraint field of the decoupled background:
`c + 2δ + c (c + 2 (1 + 3δ))` with `c = K₄ δ`. -/
noncomputable def decDomMargin (d L N : ℕ) [NeZero L] (BG κ δ : ℝ) : ℝ :=
  K4 d L N BG κ * δ + 2 * δ +
    K4 d L N BG κ * δ * (K4 d L N BG κ * δ + 2 * (1 + 3 * δ))

variable {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} {ν : ℝ}

/-- **Membership in `DecDom` from the bounds of Theorem I-4b**: the bounds `BgBounds … c` for the
decoupled background of a datum of `Ψ̃^c(δ, δ)` give a strict constraint field `φ̄` and an
admissible multiplier. -/
theorem decDom_of_bgBounds {D : BgData G N} {φ : G.Ω 1 × Fin N → ℂ} {α : G.Ω 1 → ℂ}
    {c δ δc κ : ℝ} (hδ : 0 ≤ δ) (hc : 0 ≤ c) (hD : InDomainC G ν δ δ D)
    (hb : BgBounds G D φ α c) (hphi : 3 * δ + c < 1 / 2)
    (hmar : c + 2 * δ + c * (c + 2 * (1 + 3 * δ)) < δc) (hα : c < coerciveConst d / 2)
    {s : DecParams G} (hs : ∀ P, ‖s P‖ < Real.exp κ) :
    (s, (barField G D.Ψ φ, α)) ∈ DecDom G N κ δc := by
  have hsp : ∀ x : CTorus d L N₁ m₁ (k + 1), 0 < G.spacing x := fun x => spacing_pos G
  have hcl : c < δc := by nlinarith [mul_nonneg hc (add_nonneg hc (by positivity : (0:ℝ) ≤ 2 * (1 + 3 * δ)))]
  refine ⟨hs, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro x hx μ
    have := hb.grad ⟨x, hx⟩ μ
    exact ⟨lt_of_le_of_lt this.1 (div_lt_div_of_pos_right hcl (hsp x)),
      lt_of_le_of_lt this.2 (div_lt_div_of_pos_right hcl (hsp x))⟩
  · intro x hx
    have := hb.lap ⟨x, hx⟩
    exact lt_of_le_of_lt this (div_lt_div_of_pos_right hcl (by have := hsp x; positivity))
  · intro x hx
    have hxd : x ∈ dataSites G := (mem_dataSites G).2 (Or.inl hx)
    have h1 := vn_Psi_lt hδ hD hxd
    have h2 := vn_le_sub_add (fun i => φ (⟨x, hx⟩, i)) (D.Ψ x)
    have h3 := hb.val ⟨x, hx⟩
    have e : barField G D.Ψ φ x = fun i => φ (⟨x, hx⟩, i) := by
      funext i; simp [barField, hx]
    dsimp only
    rw [e]; linarith
  · intro x hx
    have hxd : x ∈ dataSites G := (mem_dataSites G).2 (Or.inl hx)
    have hvb := vn_Psi_lt hδ hD hxd
    have hva := hb.val ⟨x, hx⟩
    have e : barField G D.Ψ φ x = fun i => φ (⟨x, hx⟩, i) := by
      funext i; simp [barField, hx]
    dsimp only
    rw [e]
    set a : Fin N → ℂ := fun i => φ (⟨x, hx⟩, i) with ha
    set b : Fin N → ℂ := D.Ψ x with hbdef
    have hab : vn (fun i => a i - b i) ≤ c := hva
    have hvA : vn a ≤ vn b + c := by
      have := vn_le_sub_add a b; linarith
    have hbb : ‖∑ i, b i * b i - 1‖ < 2 * δ := by
      obtain ⟨Ψ, h, Ψ', h', hP, hΨ, -⟩ := hD
      have h1 := hP.c2b x hxd
      have h2 := hP.r2 x hxd
      have e1 : ∑ i, b i * b i = ∑ i, ((Ψ x i : ℂ) + Ψ' x i) * ((Ψ x i : ℂ) + Ψ' x i) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hbdef, hΨ x hxd i]
      have e2 : ((∑ i, Ψ x i ^ 2 - 1 : ℝ) : ℂ) = ∑ i, (Ψ x i : ℂ) * (Ψ x i : ℂ) - 1 := by
        push_cast; simp [sq]
      have h3 : ‖∑ i, (Ψ x i : ℂ) * (Ψ x i : ℂ) - 1‖ < δ := by
        rw [← e2, Complex.norm_real, Real.norm_eq_abs]; exact h2
      rw [e1]
      calc ‖∑ i, ((Ψ x i : ℂ) + Ψ' x i) * ((Ψ x i : ℂ) + Ψ' x i) - 1‖
          = ‖(∑ i, ((Ψ x i : ℂ) + Ψ' x i) * ((Ψ x i : ℂ) + Ψ' x i) -
              ∑ i, (Ψ x i : ℂ) * (Ψ x i : ℂ)) + (∑ i, (Ψ x i : ℂ) * (Ψ x i : ℂ) - 1)‖ := by
            congr 1; ring
        _ ≤ _ := norm_add_le _ _
        _ < 2 * δ := by linarith
    have hsum : ∑ i, a i * a i - 1 = (∑ i, b i * b i - 1) + ∑ i, (a i - b i) * (a i + b i) := by
      have : ∑ i, (a i - b i) * (a i + b i) = ∑ i, (a i * a i - b i * b i) :=
        Finset.sum_congr rfl fun i _ => by ring
      rw [this, Finset.sum_sub_distrib]; ring
    have hcs := norm_sum_mul_le_vn (fun i => a i - b i) (fun i => a i + b i)
    have hpl : vn (fun i => a i + b i) ≤ vn a + vn b := by
      have := vn_lin_le 1 1 a b
      simpa using this
    have hv0 := vn_nonneg (fun i => a i - b i)
    rw [hsum]
    calc _ ≤ ‖∑ i, b i * b i - 1‖ + ‖∑ i, (a i - b i) * (a i + b i)‖ := norm_add_le _ _
      _ ≤ 2 * δ + c * (c + 2 * (1 + 3 * δ)) := by
          refine add_le_add hbb.le (hcs.trans ?_)
          have hb0 := vn_nonneg b
          have hbl : vn b < 1 + 3 * δ := by linarith
          calc _ ≤ c * (vn a + vn b) := mul_le_mul hab (hpl.trans le_rfl) (vn_nonneg _) hc
            _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) hc
      _ < _ := by linarith
  · intro w
    have h := hb.alpha w
    have hp := hsp (w : CTorus d L N₁ m₁ (k + 1))
    have hp2 : 0 < G.spacing (w : CTorus d L N₁ m₁ (k + 1)) ^ 2 := by positivity
    rw [lt_div_iff₀ (by positivity)]
    nlinarith

variable {ϱm : ℝ} {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
  {a₁ c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ}

/-- **The decoupled background lies in `DecDom`** (target 1 of the hat-variable engine).  For a
datum `D ∈ Ξ^c(𝔹_{k+1}; 1, ε)`, parameters `s` with `|s_P| < e^κ`, and `(φ, α)` the decoupled
background of `D` at `s` (`IsDecBg`), the point `(s, (φ̄, α))`, `φ̄ = barField Gp D.Ψ φ` the
extension of `φ` by the datum, lies in `DecDom Gp N κ δc` whenever `δc` exceeds the margin
`decDomMargin` of `δ = C₁ ε` and `K₄ δ < γ/2`.  The two extra conditions are the smallness
requirements of the strict constraint field and of the multiplier; the bounds `BgBounds` come from
the uniqueness part of Theorem I-4b. -/
theorem decDom_of_isDecBg {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
    (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) {s : DecParams Gp}
    (hs : ∀ P, ‖s P‖ < Real.exp κ) {D : BgData Gp N}
    (hD : XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D) {φ : Gp.Ω 1 × Fin N → ℂ}
    {α : Gp.Ω 1 → ℂ} (hI : IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α)
    {δc : ℝ} (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2) :
    (s, (barField Gp D.Ψ φ, α)) ∈ DecDom Gp N κ δc := by
  have hd0 : 0 < d := by have := hC.HBp.hd; omega
  have hc1 := one_le_xiC1 d
  have hε := hC.eps_pos
  have hδ0 : 0 < xiC1 d * eps := by positivity
  have hDom := xiCData_inDomainC hC.HBp hC.small1 hD
  have hδ1 : xiC1 d * eps ≤ c7 d L N BG κ := hC.c7le
  have hδ0' : xiC1 d * eps ≤ bgC0 d L N := hδ1.trans ((c7_le_bgC1 d L N BG κ).trans
    (bgC1_le_bgC0 d L N hd0))
  have hνε : ν * ((L : ℝ) ^ (k + 1)) ^ 2 * (xiC1 d * eps) ^ 2 ≤ (xiC1 d * eps) ^ 2 := by
    have := hC.HBp.massLe; nlinarith [sq_nonneg (xiC1 d * eps)]
  have hsle : ∀ P, ‖s P‖ ≤ Real.exp κ := fun P => (hs P).le
  obtain ⟨φ', α', hI', hu', -, -, hbb⟩ := i4b_exists_unique hC.hS hC.Sp hC.HBp hC.hκ.le hC.hM
    hsle hδ0 le_rfl hδ0' hδ1 hνε hDom
  obtain ⟨rfl, rfl⟩ := hu' φ α hI
  have hK4 : 0 < K4 d L N BG κ := K4_pos hC.hS.fam.2.1 hd0
  have hB4 : 0 < K4 d L N BG κ * (xiC1 d * eps) := mul_pos hK4 hδ0
  refine decDom_of_bgBounds (c := K4 d L N BG κ * (xiC1 d * eps)) hδ0.le hB4.le hDom hbb ?_
    ?_ hα hs
  · have := hC.phi_lt; nlinarith
  · unfold decDomMargin at hmar; nlinarith

/-- **The `XSetting` bridge** (target 2): the standing hypotheses of the decoupled covariance
`XSetting Gp (compWeight L a₁) aT ν` follow from `FlCore` and `1 ≤ k`, with the top-layer
coefficient `aT = a₁` (the weight `a_1` of the new layer, as in `StepSetting.covSqrt`); the bounds
`aT ∈ [1/2, 2]` are the admissibility `a_1 ∈ [1/2, 2]` of the weights `compWeight L a₁`. -/
theorem xSetting_of_flCore {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
    (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (hk : 1 ≤ k) :
    XSetting Gp (compWeight L a₁) a₁ ν := by
  have hL : 2 ≤ L := by have := hC.Sp.hL; omega
  have h := hC.Sp.weights 1 le_rfl (by omega)
  rw [compWeight_one hL] at h
  have hw := hC.Sp.weights k hk (by omega)
  exact ⟨hC.Sp, hw.1, hw.2, h.1, h.2⟩

end Dom

end Balaban.Localization
