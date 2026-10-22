/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.LocalGas
public import Balaban.Polymer.MayerPYTransport
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Closeness of the local terms of two local gases (A6-3 (d), blocker 7)

The local terms `P_g(Y) = localGasP μ W g Y` of the gas of a family `W` with the local form
(`LocalGasForm`, `Polymer/LocalGas.lean`) on two systems of sites related by a map of blocks `σ`,
injective on `Y`, carrying integrals along a relation `Rel` (as in `PY_mayer_transport`). Let `W₂` be
the terms of the second system read on the first (`W'_{σX}(Φ', g') = W₂ X(Φ, g)` for related
configurations, `X ⊆ Y`), with the local form, and close to `W` inside `Y` with a margin factor:
`|W_X(Φ, g) - W₂ X(Φ, g)| ≤ ε e^{-a |X|_St} e^{-λ m(X)}` (`m ≥ 0` decreasing under inclusion). Under the
numerical conditions of `integral_exp_eq_gasP` with the doubled amplitude (`16 ε e^{-κ₀} ≤ 1/2`,
`512 e ε e^{-2κ₀} ≤ 1`):

`|P'_{g'}(σ Y) - P_g(Y)| ≤ 512 e ε e^{-2κ₀} e^{-κ'|Y|_St - λ m(Y)}` (`localGasP_close_transport`),

the instance of `PY_mayer_close_transport` with the Steiner size of `steinerGen_gas`. The Mayer
activities on one system: `localGasK_close` (instance of `mayerK_sub_bound_margin`).
-/

@[expose] public section

noncomputable section

open scoped Classical

open Finset MeasureTheory

namespace Balaban.Polymer

variable {B : Type*} [Fintype B] [DecidableEq B] {H : SimpleGraph B}
  {Ω : B → Type*} [∀ b, TopologicalSpace (Ω b)] [∀ b, MeasurableSpace (Ω b)]
  [∀ b, BorelSpace (Ω b)] [∀ b, SecondCountableTopology (Ω b)]
  {μ : ∀ b, Measure (Ω b)} [∀ b, IsProbabilityMeasure (μ b)]
  {I : Type*} [Fintype I] {σI : I → B} {U : Set (I → ℂ)} {a ε : ℝ}
  {W W₂ : Finset B → (∀ b, Ω b) → (I → ℂ) → ℂ}

omit [∀ b, MeasurableSpace (Ω b)] [∀ b, BorelSpace (Ω b)] [∀ b, SecondCountableTopology (Ω b)]
  [∀ b, IsProbabilityMeasure (μ b)] in
/-- The per-term bound of the local form with the rate split `κ₀ + κ₁ ≤ a`. -/
theorem norm_gasTerm_le_split (hconn : H.Connected) (hW : LocalGasForm H σI U a ε W)
    {κ0 κ1 : ℝ} (ha : κ0 + κ1 ≤ a) {g : I → ℂ} (hg : g ∈ U) (X : NePoly B) (Φ : ∀ b, Ω b) :
    ‖localGasTerm W g X Φ‖ ≤ ε * Real.exp (-(κ0 + κ1) * stSizeG H X.1) := by
  have hε : 0 ≤ ε := by
    obtain ⟨b⟩ := hconn.nonempty
    exact le_trans (Finset.sum_nonneg fun Y _ => by positivity) (hW.bound Φ g hg b)
  refine (norm_gasTerm_le hconn hW.toLocalGasFormE hg X Φ).trans (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.2 ?_) hε)
  have := stSizeG_nonneg (H := H) X.1
  nlinarith

/-- **Closeness of the local terms of two local gases related by a map of blocks.** -/
theorem localGasP_close_transport (hconn : H.Connected) {Δ : ℕ} (hdeg : ∀ v, H.degree v ≤ Δ)
    {κ0 κ1 κ' : ℝ} (hq : (Δ : ℝ) ^ 2 * 2 * Real.exp (-κ0) ≤ 1 / 2)
    (hκ0 : Real.log 4 + 1 ≤ κ0) (hκ' : 0 ≤ κ') (hκ : κ' + κ0 + 1 ≤ κ1 - 3 / 2)
    (ha : κ0 + κ1 ≤ a) (hεlog : ε ≤ Real.log 2)
    (hε2 : 16 * ε * Real.exp (-κ0) ≤ 1 / 2)
    (hεα : 512 * Real.exp 1 * ε * Real.exp (-(2 * κ0)) ≤ 1)
    (hW : LocalGasForm H σI U a ε W) (hW₂ : LocalGasForm H σI U a ε W₂) {g : I → ℂ}
    (hg : g ∈ U) {B' : Type*} [Fintype B'] [DecidableEq B'] {Ω' : B' → Type*}
    [∀ b, MeasurableSpace (Ω' b)] (μ' : ∀ b, Measure (Ω' b)) {I' : Type*}
    (σ : B → B') (Y : Finset B) (hY : Y.Nonempty) (hσ : Set.InjOn σ (Y : Set B))
    (W' : Finset B' → (∀ b, Ω' b) → (I' → ℂ) → ℂ) (g' : I' → ℂ)
    (Rel : (∀ b, Ω b) → (∀ b, Ω' b) → Prop)
    (hint : ∀ Z ⊆ Y, ∀ (F : (∀ b, Ω b) → ℂ) (F' : (∀ b, Ω' b) → ℂ), DepOn Z F →
      (∀ Φ Φ', Rel Φ Φ' → F' Φ' = F Φ) →
        ∫ Φ', F' Φ' ∂(Measure.pi μ') = ∫ Φ, F Φ ∂(Measure.pi μ))
    (hlink : ∀ X : Finset B, X.Nonempty → X ⊆ Y → ∀ Φ Φ', Rel Φ Φ' →
      W' (X.image σ) Φ' g' = W₂ X Φ g)
    (m : Finset B → ℝ) (hm : ∀ Y, 0 ≤ m Y) (hmono : ∀ X Y, X ⊆ Y → m Y ≤ m X) {lam : ℝ}
    (hlam : 0 ≤ lam)
    (hclose : ∀ X : Finset B, X.Nonempty → X ⊆ Y → ∀ Φ,
      ‖W X Φ g - W₂ X Φ g‖ ≤ ε * Real.exp (-a * stSizeG H X) * Real.exp (-lam * m X)) :
    ‖localGasP μ' W' g' (Y.image σ) - localGasP μ W g Y‖ ≤
      512 * Real.exp 1 * ε * Real.exp (-(2 * κ0)) *
        Real.exp (-(κ' * stSizeG H Y + lam * m Y)) := by
  have hκ0nn : 0 ≤ κ0 := by
    have : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    linarith
  have hκ1nn : 0 ≤ κ1 := by linarith
  have hε : 0 ≤ ε := by
    obtain ⟨b⟩ := hconn.nonempty
    have hΦ : Nonempty (∀ b, Ω b) := ⟨fun b => (nonempty_of_isProbabilityMeasure (μ b)).some⟩
    exact le_trans (Finset.sum_nonneg fun Y _ => by positivity) (hW.bound hΦ.some g hg b)
  have hG2 : ∀ b : B, ∑ Y : NePoly B,
      (if b ∈ Y.1 then Real.exp (-κ0 * stSizeG H Y.1) else 0) ≤ 4 * Real.exp (-κ0) :=
    fun b => sum_exp_stSizeG_le hconn hdeg hq b
  have hexp2 : Real.exp (-(2 * κ0)) = Real.exp (-κ0) ^ 2 := by
    rw [sq, ← Real.exp_add]; congr 1; ring
  have hmain := PY_mayer_close_transport μ (H := localGasTerm W g) (H₂ := localGasTerm W₂ g)
    (d := stSizeG H) (H0 := ε) (κ0 := κ0) (κ1 := κ1) (c := 0) (K0 := 4 * Real.exp (-κ0))
    (c1 := 1) (κ' := κ') (κ0P := κ0) (K0P := 4 * Real.exp (-κ0)) (cP := 0)
    μ' σ Y hY hσ (localGasTerm W' g') Rel hint (fun t => hW₂.local_w t.1 g)
    (fun t ht Φ Φ' hR => hlink t.1 t.2 ht Φ Φ' hR) (measurable_gasTerm hW.toLocalGasFormE hg)
    (measurable_gasTerm hW₂.toLocalGasFormE hg) hε hεlog hκ0nn hκ1nn le_rfl (fun Y => stSizeG_nonneg Y)
    (norm_gasTerm_le_split hconn hW ha hg) (norm_gasTerm_le_split hconn hW₂ ha hg)
    (fun b => by rw [Finset.sum_filter]; convert hG2 b)
    (fun C hC => by simpa using stSizeG_unionCs_le hconn C hC) zero_le_one
    (by simp only [mul_zero, Real.exp_zero, mul_one]; linarith)
    (fun Y => card_le_stSizeG hconn Y.1) hκ' le_rfl (fun b => by convert hG2 b)
    (fun n X hX => by simpa using stSizeG_union_cluster hconn X hX) hκ
    (by
      have e : 2 * (4 * (2 * (2 * ε) * (4 * Real.exp (-κ0)) * Real.exp (κ1 * 0)) * 1) *
          (4 * Real.exp (-κ0)) * Real.exp (1 + κ' * 0) =
          512 * Real.exp 1 * ε * Real.exp (-(2 * κ0)) := by
        rw [hexp2]
        simp only [mul_zero, Real.exp_zero, add_zero]
        ring
      rw [e]; exact hεα)
    m hm hmono hlam (fun t ht Φ => by
      refine (hclose t.1 t.2 ht Φ).trans ?_
      refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hε)
        (Real.exp_pos _).le
      have := stSizeG_nonneg (H := H) t.1
      nlinarith)
  refine hmain.trans (le_of_eq ?_)
  rw [hexp2]
  simp only [mul_zero, Real.exp_zero, add_zero]
  ring

/-- **Closeness of the Mayer activities of two local gases on one system** (instance of
`mayerK_sub_bound_margin` with the Steiner size): if `|W_X - W₂ X| ≤ ε e^{-a|X|_St} e^{-λ m(X)}` inside
`Y`, then `|K_W(Y) - K_{W₂}(Y)| ≤ 64 ε e^{-κ₀} e^{-λ m(Y)} e^{-(κ₁ - 3/2)|Y|_St}`. -/
theorem localGasK_close (hconn : H.Connected) {Δ : ℕ} (hdeg : ∀ v, H.degree v ≤ Δ)
    {κ0 κ1 : ℝ} (hq : (Δ : ℝ) ^ 2 * 2 * Real.exp (-κ0) ≤ 1 / 2) (hκ0 : 0 ≤ κ0) (hκ1 : 0 ≤ κ1)
    (ha : κ0 + κ1 ≤ a) (hεlog : ε ≤ Real.log 2) (hε2 : 16 * ε * Real.exp (-κ0) ≤ 1 / 2)
    (hW : LocalGasForm H σI U a ε W) (hW₂ : LocalGasForm H σI U a ε W₂) {g : I → ℂ}
    (hg : g ∈ U) (m : Finset B → ℝ) (hm : ∀ Y, 0 ≤ m Y) (hmono : ∀ X Y, X ⊆ Y → m Y ≤ m X)
    {lam : ℝ} (hlam : 0 ≤ lam) (Y : NePoly B)
    (hclose : ∀ X : Finset B, X.Nonempty → X ⊆ Y.1 → ∀ Φ,
      ‖W X Φ g - W₂ X Φ g‖ ≤ ε * Real.exp (-a * stSizeG H X) * Real.exp (-lam * m X)) :
    ‖localGasK μ W g Y - localGasK μ W₂ g Y‖ ≤
      64 * ε * Real.exp (-κ0) * Real.exp (-lam * m Y.1) *
        Real.exp (-(κ1 - 3 / 2) * stSizeG H Y.1) := by
  have hε : 0 ≤ ε := by
    obtain ⟨b⟩ := hconn.nonempty
    have hΦ : Nonempty (∀ b, Ω b) := ⟨fun b => (nonempty_of_isProbabilityMeasure (μ b)).some⟩
    exact le_trans (Finset.sum_nonneg fun Y _ => by positivity) (hW.bound hΦ.some g hg b)
  have hG2 : ∀ b : B, ∑ Y : NePoly B,
      (if b ∈ Y.1 then Real.exp (-κ0 * stSizeG H Y.1) else 0) ≤ 4 * Real.exp (-κ0) :=
    fun b => sum_exp_stSizeG_le hconn hdeg hq b
  have h := mayerK_sub_bound_margin μ (sup := fun X : NePoly B => X.1) (H := localGasTerm W g)
    (H₂ := localGasTerm W₂ g) (d := stSizeG H) (κ0 := κ0) (κ1 := κ1) (c := 0)
    (K0 := 4 * Real.exp (-κ0)) (c1 := 1) (measurable_gasTerm hW.toLocalGasFormE hg) (measurable_gasTerm hW₂.toLocalGasFormE hg)
    hε hεlog hκ0 hκ1 le_rfl (fun Y => stSizeG_nonneg Y) (fun t => t.2)
    (norm_gasTerm_le_split hconn hW ha hg) (norm_gasTerm_le_split hconn hW₂ ha hg) m hm hmono hlam
    (fun b => by rw [Finset.sum_filter]; convert hG2 b)
    (fun C hC => by simpa using stSizeG_unionCs_le hconn C hC) zero_le_one
    (by simp only [mul_zero, Real.exp_zero, mul_one]; linarith) Y (card_le_stSizeG hconn Y.1)
    (fun t ht Φ => by
      refine (hclose t.1 t.2 ht Φ).trans ?_
      refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hε)
        (Real.exp_pos _).le
      have := stSizeG_nonneg (H := H) t.1
      nlinarith)
  refine h.trans (le_of_eq ?_)
  simp only [mul_zero, Real.exp_zero]
  ring

end Balaban.Polymer
