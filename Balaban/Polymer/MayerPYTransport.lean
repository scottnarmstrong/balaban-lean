/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.MayerPYClose
public import Balaban.Polymer.MayerTransport

/-!
# Closeness of the local terms of two Mayer gases related by a map of blocks

`PY_mayer_close_transport`: two product spaces related by a map of blocks `σ`, injective on `Y`,
carrying integrals as in `PY_mayer_transport`; if the terms of the second system read on the first
(`H₂`) are close to those of the first with the margin factor `e^{-λ m}`, then `|P'(σ Y) - P(Y)|` is
bounded by `e^{-κ'(d(Y) + c_P) - λ m(Y)}` times the constant of `pe_size_sub_bound`
(`PY_mayer_transport` and `mayer_PY_sub_bound_single`).
-/

@[expose] public section

noncomputable section

open scoped Classical

open Finset MeasureTheory

namespace Balaban.Polymer

section Transport

variable {B : Type*} [Fintype B] {Ω : B → Type*} [∀ b, MeasurableSpace (Ω b)]
  (μ : ∀ b, Measure (Ω b)) [∀ b, IsProbabilityMeasure (μ b)]
  {H H₂ : NePoly B → (∀ b, Ω b) → ℂ} {d : Finset B → ℝ}
  {H0 κ0 κ1 c K0 c1 κ' κ0P K0P cP : ℝ}

/-- **Closeness of the local terms of two Mayer gases related by a map of blocks** (P7 (4.9); the
two-torus closeness of the last-scale gas). Let `σ` map the blocks of a first product space to those
of a second, injectively on `Y`, carrying integrals of functions of the blocks of `Z ⊆ Y` along the
relation `Rel` (as in `PY_mayer_transport`); let `H₂` be the terms `H'` of the second system read on
the first (`H'_{σ t}(Φ') = H₂ t (Φ)` for related configurations, `t ⊆ Y`), with the bound of MY, and
close to the terms `H` of the first system inside `Y` with the margin factor `e^{-λ m(t)}`. Then
`|P'(σ Y) - P(Y)| ≤ 2 ε K₀ᴾ e^{c₁ + κ' c_P} e^{-κ'(d(Y) + c_P) - λ m(Y)}`, `ε = 4 q₂ c₁`. -/
theorem PY_mayer_close_transport {B' : Type*} [Fintype B'] [DecidableEq B']
    {Ω' : B' → Type*} [∀ b, MeasurableSpace (Ω' b)] (μ' : ∀ b, Measure (Ω' b))
    (σ : B → B') (Y : Finset B) (hY : Y.Nonempty) (hσ : Set.InjOn σ (Y : Set B))
    (H' : NePoly B' → (∀ b, Ω' b) → ℂ) (Rel : (∀ b, Ω b) → (∀ b, Ω' b) → Prop)
    (hint : ∀ Z ⊆ Y, ∀ (F : (∀ b, Ω b) → ℂ) (F' : (∀ b, Ω' b) → ℂ), DepOn Z F →
      (∀ Φ Φ', Rel Φ Φ' → F' Φ' = F Φ) →
        ∫ Φ', F' Φ' ∂(Measure.pi μ') = ∫ Φ, F Φ ∂(Measure.pi μ))
    (hdep₂ : ∀ t : NePoly B, DepOn t.1 (H₂ t))
    (hlink : ∀ t : NePoly B, t.1 ⊆ Y → ∀ Φ Φ', Rel Φ Φ' →
      H' ⟨t.1.image σ, t.2.image σ⟩ Φ' = H₂ t Φ)
    (hmeas : ∀ t, Measurable (H t)) (hmeas₂ : ∀ t, Measurable (H₂ t))
    (hH0 : 0 ≤ H0) (hH0' : H0 ≤ Real.log 2) (hκ0 : 0 ≤ κ0) (hκ1 : 0 ≤ κ1) (hc : 0 ≤ c)
    (hd : ∀ Y, 0 ≤ d Y)
    (hH : ∀ t Φ, ‖H t Φ‖ ≤ H0 * Real.exp (-(κ0 + κ1) * d t.1))
    (hH₂ : ∀ t Φ, ‖H₂ t Φ‖ ≤ H0 * Real.exp (-(κ0 + κ1) * d t.1))
    (hG2T : ∀ b : B, ∑ t ∈ Finset.univ.filter (fun t : NePoly B => b ∈ t.1),
      Real.exp (-κ0 * d t.1) ≤ K0)
    (hG3T : ∀ C : Finset (NePoly B), ConnSet (fun t : NePoly B => t.1) C →
      d (unionCs (fun t : NePoly B => t.1) C) ≤ ∑ t ∈ C, d t.1 + c * ((C.card : ℝ) - 1))
    (hc1 : 0 ≤ c1) (hq : 2 * (2 * H0) * K0 * Real.exp (κ1 * c) * c1 ≤ 1 / 2)
    (hG1 : ∀ Y : NePoly B, (Y.1.card : ℝ) ≤ c1 * (1 + d Y.1))
    (hκ' : 0 ≤ κ') (hcP : 0 ≤ cP)
    (hG2P : ∀ b : B, ∑ Y : NePoly B, (if b ∈ Y.1 then Real.exp (-κ0P * d Y.1) else 0) ≤ K0P)
    (hG3P : ∀ (n : ℕ) (X : Fin (n + 1) → NePoly B),
      (clusterGraph (shareBlock (Subtype.val : NePoly B → Finset B)) X).Connected →
        d (unionOf (Subtype.val : NePoly B → Finset B) X) ≤ ∑ i, d (X i).1 + cP * n)
    (hκ : κ' + κ0P + c1 ≤ κ1 - 3 / 2)
    (hα : 2 * (4 * (2 * (2 * H0) * K0 * Real.exp (κ1 * c)) * c1) * K0P *
      Real.exp (c1 + κ' * cP) ≤ 1)
    (m : Finset B → ℝ) (hm : ∀ Y, 0 ≤ m Y) (hmono : ∀ X Y, X ⊆ Y → m Y ≤ m X) {lam : ℝ}
    (hlam : 0 ≤ lam)
    (hHH : ∀ t : NePoly B, t.1 ⊆ Y → ∀ Φ, ‖H t Φ - H₂ t Φ‖ ≤
      H0 * Real.exp (-(κ0 + κ1) * d t.1) * Real.exp (-lam * m t.1)) :
    ‖PY (shareBlock (Subtype.val : NePoly B' → Finset B')) Subtype.val
          (mayerK μ' (fun X : NePoly B' => X.1) H') (Y.image σ) -
        PY (shareBlock (Subtype.val : NePoly B → Finset B)) Subtype.val
          (mayerK μ (fun X : NePoly B => X.1) H) Y‖ ≤
      2 * (4 * (2 * (2 * H0) * K0 * Real.exp (κ1 * c)) * c1) * K0P * Real.exp (c1 + κ' * cP) *
        Real.exp (-(κ' * (d Y + cP) + lam * m Y)) := by
  rw [PY_mayer_transport μ μ' σ Y hσ H₂ H' Rel hint hdep₂ hlink, norm_sub_rev]
  exact mayer_PY_sub_bound_single μ hmeas hmeas₂ hH0 hH0' hκ0 hκ1 hc hd hH hH₂ hG2T hG3T hc1 hq
    hG1 hκ' hcP hG2P hG3P hκ hα m hm hmono hlam Y hY hHH

end Transport

end Balaban.Polymer
