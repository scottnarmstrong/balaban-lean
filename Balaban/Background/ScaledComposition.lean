/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Background.CompositionDomain
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The scaled composition (R-S) (SMALLFIELD.md §1.7, requirement of review S-02)

For `𝔹_j ≺ 𝔹'_k` with the scale gap `ℓ(x) ≤ s ℓ'(x)`, `s = L^{-(k-j)}`, the composed data
(formula (6.2)) lie in the domain `Ψ̃^c(𝔹_j; σε, ε)` with `σ = C₀ s` and satisfy the second-order
condition (R2') `|Ψ·Ψ - 1| < σ² ε`; the discrepancy `Ψ - Q_n φ'` of (6.2) carries the factor
`(a_p/a_n) L^{2(n-p)} ≤ s²`.

* `Balaban.Background.ScaledPsiC`: the domain of the conclusion, (R1')–(R4'), (C1')–(C3');
* `Balaban.Background.HypS`: the hypotheses on the input field (the bounds of Theorem 5.2 (3) in
  the form `|φ' - Q*Ψ'|₀, |∂φ̄'|, |Δφ̄'| ≤ η` for the real and the complex field,
  `|φ^c - φ^r|₀ ≤ ε`, `η ≤ ε`);
* `Balaban.Background.scaledComposition`: the theorem (R-S).
-/

@[expose] public section

namespace Balaban.Background

open Balaban.Multiscale Matrix Finset

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ ϱ' : ℝ}

/-- The constant `C₀ = C₀(d)` of (R-S): `σ = C₀ s`. -/
noncomputable def scaledC0 (d : ℕ) : ℝ := 8 * d + 12

section Numeric

theorem b2_le {d η θ : ℝ} (hd : 0 ≤ d) (hη : 0 < η) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (hs : (4 * d + 6) * η ≤ 1) {M : ℝ} :
    (2 * d * (θ * η)) ^ 2 + 2 * θ ^ 2 * M * η + (θ ^ 2) ^ 2 * η ^ 2 ≤ θ ^ 2 * η * (d + 2 * M + 1) := by
  have h1 : 4 * d * η ≤ 1 := by nlinarith
  have h2 : η ≤ 1 := by nlinarith
  have hθ2 : θ ^ 2 ≤ 1 := by nlinarith
  have h3 : (2 * d * (θ * η)) ^ 2 ≤ θ ^ 2 * η * d := by
    have : (2 * d * (θ * η)) ^ 2 = θ ^ 2 * η * (4 * d * η * d) := by ring
    rw [this]
    have h4 : 4 * d * η * d ≤ d := by nlinarith
    exact mul_le_mul_of_nonneg_left h4 (by positivity)
  have h5 : (θ ^ 2) ^ 2 * η ^ 2 ≤ θ ^ 2 * η := by
    have : (θ ^ 2) ^ 2 * η ^ 2 = θ ^ 2 * η * (θ ^ 2 * η) := by ring
    rw [this]
    have h6 : θ ^ 2 * η ≤ 1 := by nlinarith
    exact mul_le_of_le_one_right (by positivity) h6
  nlinarith

theorem r3_final {θ η δ ε d b E : ℝ} (hd0 : 0 ≤ d) (hθ0 : 0 < θ) (hδη : δ ≤ η) (hηε : η ≤ ε)
    (hη : 0 < η) (hb0 : 0 ≤ b) (hE0 : 0 ≤ E) (hbE : b + E ≤ θ * η * (d + 5)) (hδ : 0 < δ) :
    (1 / 2) * (b + E) ^ 2 + (1 / 2) * (θ * δ) ^ 2 ≤ ((8 * d + 12) * θ * ε) ^ 2 := by
  have h1 : (b + E) ^ 2 ≤ (θ * η * (d + 5)) ^ 2 := pow_le_pow_left₀ (by linarith) hbE 2
  have h2 : (θ * δ) ^ 2 ≤ (θ * ε) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left (hδη.trans hηε) hθ0.le) 2
  have h3 : (θ * η * (d + 5)) ^ 2 ≤ (θ * ε * (d + 5)) ^ 2 :=
    pow_le_pow_left₀ (by positivity)
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hηε hθ0.le) (by linarith)) 2
  have hX : 0 ≤ (θ * ε) ^ 2 := sq_nonneg _
  have e1 : (θ * ε * (d + 5)) ^ 2 = (θ * ε) ^ 2 * (d + 5) ^ 2 := by ring
  have e2 : ((8 * d + 12) * θ * ε) ^ 2 = (θ * ε) ^ 2 * (8 * d + 12) ^ 2 := by ring
  rw [e2]
  nlinarith [mul_nonneg hX (sq_nonneg d), mul_nonneg hX hd0]

theorem c3b_numeric2 {d η δ ε : ℝ} (hd0 : 0 ≤ d) (hδ : 0 < δ) (hδη : δ ≤ η) (hηε : η ≤ ε) :
    δ ^ 2 + 3 * ((2 * d + 2) * η) * (δ ^ 2 / ε) ≤ ((8 * d + 12) * ε) ^ 2 := by
  have hε : 0 < ε := hδ.trans_le (hδη.trans hηε)
  have hη : 0 < η := hδ.trans_le hδη
  have h1 : δ ^ 2 / ε ≤ η := by
    rw [div_le_iff₀ hε]; nlinarith
  have h2 : δ ^ 2 ≤ η ^ 2 := pow_le_pow_left₀ hδ.le hδη 2
  have h3 : 3 * ((2 * d + 2) * η) * (δ ^ 2 / ε) ≤ 3 * ((2 * d + 2) * η) * η :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  have h4 : η ^ 2 ≤ ε ^ 2 := pow_le_pow_left₀ hη.le hηε 2
  nlinarith [sq_nonneg ε, mul_nonneg hd0 (sq_nonneg ε), mul_nonneg hd0 hd0,
    mul_nonneg (mul_nonneg hd0 hd0) (sq_nonneg ε), mul_nonneg hd0 (sub_nonneg.2 h4)]

end Numeric

section ScaledDomain

variable {G : GeneratingSet d L N₀ k ϱ} {G' : GeneratingSet d L N₀ k ϱ'}

/-- **The domain of the scaled composition** (R-S): `Ψ̃^c(𝔹_j; σε, ε)` with the second-order
condition (R2') `|Ψ·Ψ - 1| < σ² ε`.  In fine units the masses are `ν L^{2n}` on layer `n`, and
(R4') reads `ν L^{2j} |h·h - 1| < (σε)²` (`ν_j = ν L^{2j}`). -/
structure ScaledPsiC (G : GeneratingSet d L N₀ k ϱ) (ν σ ε : ℝ) (j : ℕ)
    (Ψ : Torus d (N₀ * L ^ k) → Fin N → ℝ) (h : Fin N → ℝ)
    (Ψ' h' : Torus d (N₀ * L ^ k) → Fin N → ℂ) : Prop where
  layerConst : IsLayerConstant G Ψ
  r1 : ∀ x x', IsInterfacePair G x x' → rn (fun i => Ψ x i - Ψ x' i) < σ * ε
  r2 : ∀ x ∈ dataSites G, |∑ i, Ψ x i ^ 2 - 1| < σ ^ 2 * ε
  r3 : ∀ x ∈ dataSites G, ν * ((L : ℝ) ^ G.layerIndex x) ^ 2 *
    |1 - (∑ i, Ψ x i * h i) / rn (Ψ x)| < (σ * ε) ^ 2
  r4 : ν * ((L : ℝ) ^ j) ^ 2 * |∑ i, h i ^ 2 - 1| < (σ * ε) ^ 2
  layerConst' : IsLayerConstant G Ψ'
  hLayerConst' : IsLayerConstant G h'
  c1 : ∀ x x', IsInterfacePair G x x' → vn (Ψ' x - Ψ' x') < σ * ε
  c2a : ∀ x ∈ dataSites G, vn (Ψ' x) < ε + σ * ε
  c2b : ∀ x ∈ dataSites G,
    ‖∑ i, ((Ψ x i : ℂ) + Ψ' x i) * ((Ψ x i : ℂ) + Ψ' x i) - ∑ i, (Ψ x i : ℂ) * (Ψ x i : ℂ)‖ <
      σ * ε
  c3a : ∀ x ∈ G.Ω 1, ν * ((L : ℝ) ^ G.layerIndex x) ^ 2 * vn (h' x) < (σ * ε) ^ 2 / ε
  c3b : ∀ x ∈ G.Ω 1, ν * ((L : ℝ) ^ G.layerIndex x) ^ 2 *
    ‖∑ i, ((Ψ x i / rn (Ψ x) : ℝ) : ℂ) * h' x i‖ < (σ * ε) ^ 2

/-- **The hypotheses of (R-S)**: `𝔹_j ≺ 𝔹'_k`; the scale gap `ℓ ≤ θ ℓ'` on `Ω₁` and on the collar
(with `Ω₁ ∪ C(Ω₁) ⊆ Ω'₁`), `θ = L^{j-k}` (`(L^j) = θ L^k`), all layers of `𝔹_j` at most `j`; the data
`(Ψ0 + Ψ'', h0 + h'') ∈ Ψ̃^c(𝔹'_k; δ, ε)` with `δ ≤ η ≤ ε ≤ 1`; the real field `φr` and the complex
field `φc` with the bounds of Theorem 5.2 (3) of size `η` and `|φc - φr|₀ ≤ ε`. -/
structure HypS (G : GeneratingSet d L N₀ k ϱ) (G' : GeneratingSet d L N₀ k ϱ') (a₁ ν δ ε η θ : ℝ)
    (j : ℕ) (Ψ0 : Torus d (N₀ * L ^ k) → Fin N → ℝ) (h0 : Fin N → ℝ)
    (Ψ'' h'' : Torus d (N₀ * L ^ k) → Fin N → ℂ) (φr φc : G'.Ω 1 × Fin N → ℂ) : Prop where
  prec : Precedes G G'
  hL : 2 ≤ L
  ha₁ : 0 < a₁
  hθ0 : 0 < θ
  hθ1 : θ ≤ 1
  hjθ : (L : ℝ) ^ j = θ * (L : ℝ) ^ k
  hnj : ∀ x ∈ G.Ω 1, G.layerIndex x ≤ j
  gap : ScaleGap G G' θ
  hcol : ∀ z ∈ collar G, z ∈ G'.Ω 1 ∧ 1 ≤ θ * G'.spacing z
  hδ : 0 < δ
  hδη : δ ≤ η
  hηε : η ≤ ε
  hε1 : ε ≤ 1
  hsmall : (4 * d + 6) * η ≤ 1
  hν : 0 ≤ ν
  hνk : ν * ((L : ℝ) ^ k) ^ 2 ≤ 1
  hPC : InPsiTildeC G' ν δ ε Ψ0 h0 Ψ'' h''
  hφr : ∀ z i, (φr (z, i)).im = 0
  hbr : FieldBounds G' η (psiR Ψ0) φr
  hmass : ∀ z : G'.Ω 1, Real.sqrt ν * G'.spacing z * vn (fun i => φr (z, i) - (h0 i : ℂ)) ≤ η
  hbc : FieldBounds G' η (psiC Ψ0 Ψ'') φc
  hdiff : ∀ z : G'.Ω 1, vn (fun i => φc (z, i) - φr (z, i)) ≤ ε

namespace HypS

variable {a₁ ν δ ε η θ : ℝ} {j : ℕ} {Ψ0 : Torus d (N₀ * L ^ k) → Fin N → ℝ} {h0 : Fin N → ℝ}
  {Ψ'' h'' : Torus d (N₀ * L ^ k) → Fin N → ℂ} {φr φc : G'.Ω 1 × Fin N → ℂ}
  (H : HypS G G' a₁ ν δ ε η θ j Ψ0 h0 Ψ'' h'' φr φc)

include H

theorem ηpos : 0 < η := H.hδ.trans_le H.hδη

theorem εpos : 0 < ε := H.ηpos.trans_le H.hηε

theorem psiR_const : IsLayerConstant G' (psiR Ψ0) := by
  intro n hn1 hnk x hx x' hx'
  funext i
  have := congrFun (H.hPC.layerConst n hn1 hnk x hx x' hx') i
  simp only [psiR, this]

theorem psiC_const : IsLayerConstant G' (psiC Ψ0 Ψ'') := by
  intro n hn1 hnk x hx x' hx'
  funext i
  have h1 := congrFun (H.hPC.layerConst n hn1 hnk x hx x' hx') i
  have h2 := congrFun (H.hPC.layerConst' n hn1 hnk x hx x' hx') i
  simp only [psiC, h1, h2]

theorem hr : CompHyp G G' (compWeight L a₁) θ η (psiR Ψ0) φr :=
  { prec := H.prec, θ_pos := H.hθ0, η_nn := H.ηpos.le, gap := H.gap
    ratio := fun _ hx => compWeight_ratio H.hL H.ha₁ (G.layerIndex_spec hx).1
      (H.prec.layerIndex_le hx)
    layerConst := H.psiR_const, bounds := H.hbr }

theorem hc : CompHyp G G' (compWeight L a₁) θ η (psiC Ψ0 Ψ'') φc :=
  { prec := H.prec, θ_pos := H.hθ0, η_nn := H.ηpos.le, gap := H.gap
    ratio := fun _ hx => compWeight_ratio H.hL H.ha₁ (G.layerIndex_spec hx).1
      (H.prec.layerIndex_le hx)
    layerConst := H.psiC_const, bounds := H.hbc }

theorem real_crv (x : Torus d (N₀ * L ^ k)) : IsRealVec (crv G G' a₁ φr Ψ0 x) :=
  compVec_isReal H.prec _ φr (psiR Ψ0) H.hφr psiR_im_zero x

/-- All sites of `Ω₁ ∪ C(Ω₁)` are in `Ω'₁` with `1 ≤ θ ℓ'`. -/
theorem data_gap {z : Torus d (N₀ * L ^ k)} (hz : z ∈ dataSites G) :
    z ∈ G'.Ω 1 ∧ 1 ≤ θ * G'.spacing z := by
  rcases (mem_dataSites G).1 hz with hz | hz
  · refine ⟨H.prec.mem_Ω1 hz, ?_⟩
    exact (G.spacing_ge_one z).trans (H.gap z hz)
  · exact H.hcol z hz

/-- The bonds of `φ̄'` at sites of `Ω₁ ∪ C(Ω₁)`: `|∂φ̄'| ≤ θ η`. -/
theorem bond_data {Ψx : Torus d (N₀ * L ^ k) → Fin N → ℂ} {φx : G'.Ω 1 × Fin N → ℂ}
    (Hx : FieldBounds G' η Ψx φx) {z z' : Torus d (N₀ * L ^ k)} (hz : z ∈ dataSites G)
    (hadj : Adj z z') : vn (barVec G' Ψx φx z' - barVec G' Ψx φx z) ≤ θ * η := by
  obtain ⟨hz1, hz2⟩ := H.data_gap hz
  have h1 := Hx.smooth.adj_grad hz1 hadj
  have hsp : 0 < G'.spacing z := (G'.spacing_ge_one z).trans_lt' one_pos
  refine h1.trans ?_
  rw [div_le_iff₀ hsp]
  nlinarith [H.ηpos]

theorem layerConst : IsLayerConstant G (reR G G' a₁ φr Ψ0) := by
  intro n hn1 hnk x hx x' hx'
  funext i
  have := congrFun (composeField_layerConst H.prec (compWeight L a₁) φr H.psiR_const n hn1 hnk
    x hx x' hx') i
  exact congrArg Complex.re this

theorem hB {Ψx : Torus d (N₀ * L ^ k) → Fin N → ℂ} {φx : G'.Ω 1 × Fin N → ℂ}
    (Hx : FieldBounds G' η Ψx φx) : ∀ z z', z ∈ dataSites G → z' ∈ dataSites G → Adj z z' →
      vn (barVec G' Ψx φx z - barVec G' Ψx φx z') ≤ θ * η := by
  intro z z' hz hz' hadj
  rw [vn_sub_comm]
  exact H.bond_data Hx hz hadj

theorem r1 : ∀ x x', IsInterfacePair G x x' →
    rn (fun i => reR G G' a₁ φr Ψ0 x i - reR G G' a₁ φr Ψ0 x' i) < scaledC0 d * θ * ε := by
  intro x x' hxx'
  have hη := H.ηpos
  have hθ := H.hθ0
  have hθ1 := H.hθ1
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have e : rn (fun i => reR G G' a₁ φr Ψ0 x i - reR G G' a₁ φr Ψ0 x' i) =
      vn (crv G G' a₁ φr Ψ0 x - crv G G' a₁ φr Ψ0 x') :=
    rn_re_sub_eq_vn (H.real_crv x) (H.real_crv x')
  rw [e]
  have h1 : vn (crv G G' a₁ φr Ψ0 x - crv G G' a₁ φr Ψ0 x') ≤ _ :=
    H.hr.interface hxx' (H.hB H.hbr)
  refine h1.trans_lt ?_
  unfold scaledC0
  have ht := mul_pos hθ hη
  have hT : θ * η ≤ θ * ε := mul_le_mul_of_nonneg_left H.hηε hθ.le
  have hdt : d * (θ * η) ≤ d * (θ * ε) := mul_le_mul_of_nonneg_left hT hd0
  have hθt : θ * (θ * η) ≤ θ * η := mul_le_of_le_one_left ht.le hθ1
  have hdT : 0 ≤ d * (θ * ε) := by have := H.εpos; positivity
  nlinarith

theorem unit_collar {x : Torus d (N₀ * L ^ k)} (hx : x ∈ collar G) :
    rn (reR G G' a₁ φr Ψ0 x) = 1 := by
  have hx' := (H.hcol x hx).1
  have h1 : vn (crv G G' a₁ φr Ψ0 x) = 1 := by
    unfold crv
    rw [compVec_collar _ φr _ hx]
    exact barVec_vn_eq_one H.hφr H.hbr.unit _ hx'
  rw [(H.real_crv x).vn_eq] at h1
  exact h1

theorem r2 : ∀ x ∈ dataSites G, |∑ i, reR G G' a₁ φr Ψ0 x i ^ 2 - 1| <
    (scaledC0 d * θ) ^ 2 * ε := by
  intro x hx
  have hη := H.ηpos
  have hθ := H.hθ0
  have hθ1 := H.hθ1
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hε := H.εpos
  have hpos : 0 < (scaledC0 d * θ) ^ 2 * ε := by unfold scaledC0; positivity
  rcases (mem_dataSites G).1 hx with hx | hx
  · have h1 := H.hr.re_r2 H.hφr psiR_im_zero hx
    have h2 := b2_le hd0 hη hθ hθ1 H.hsmall (M := 1)
    rw [← rn_sq]
    refine (h1.trans h2).trans_lt ?_
    unfold scaledC0
    have h3 : θ ^ 2 * η * (d + 2 * 1 + 1) ≤ θ ^ 2 * ε * (d + 3) := by
      have : θ ^ 2 * η ≤ θ ^ 2 * ε := mul_le_mul_of_nonneg_left H.hηε (by positivity)
      nlinarith
    have h4 : 0 < θ ^ 2 * ε := by positivity
    nlinarith [mul_nonneg h4.le hd0, mul_nonneg (mul_nonneg h4.le hd0) hd0]
  · rw [← rn_sq, H.unit_collar hx]
    simpa using hpos

theorem hh_of {n : ℕ} (hn : n ≤ j) :
    ν * ((L : ℝ) ^ n) ^ 2 * |∑ i, h0 i ^ 2 - 1| < (θ * δ) ^ 2 := by
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have h1 : ν * ((L : ℝ) ^ n) ^ 2 ≤ ν * ((L : ℝ) ^ j) ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity)
      (pow_le_pow_right₀ hL1 hn) 2) H.hν
  have h2 := H.hPC.toInPsiTilde.r4
  have e : ν * ((L : ℝ) ^ j) ^ 2 * |∑ i, h0 i ^ 2 - 1| =
      θ ^ 2 * (ν * ((L : ℝ) ^ k) ^ 2 * |∑ i, h0 i ^ 2 - 1|) := by
    rw [H.hjθ]; ring
  calc ν * ((L : ℝ) ^ n) ^ 2 * |∑ i, h0 i ^ 2 - 1|
      ≤ ν * ((L : ℝ) ^ j) ^ 2 * |∑ i, h0 i ^ 2 - 1| :=
        mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
    _ = θ ^ 2 * (ν * ((L : ℝ) ^ k) ^ 2 * |∑ i, h0 i ^ 2 - 1|) := e
    _ < θ ^ 2 * δ ^ 2 := mul_lt_mul_of_pos_left h2 (by have := H.hθ0; positivity)
    _ = (θ * δ) ^ 2 := by ring

theorem r4 : ν * ((L : ℝ) ^ j) ^ 2 * |∑ i, h0 i ^ 2 - 1| < (scaledC0 d * θ * ε) ^ 2 := by
  have hη := H.ηpos
  have hθ := H.hθ0
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have h1 := H.hh_of (le_refl j)
  refine h1.trans_le ?_
  have h2 : θ * δ ≤ scaledC0 d * θ * ε := by
    unfold scaledC0
    have : δ ≤ ε := H.hδη.trans H.hηε
    nlinarith [mul_pos hθ H.hδ, mul_nonneg hd0 (mul_pos hθ H.εpos).le, mul_le_mul_of_nonneg_left this hθ.le]
  exact pow_le_pow_left₀ (by have := H.hδ; positivity) h2 2

theorem r3 : ∀ x ∈ dataSites G, ν * ((L : ℝ) ^ G.layerIndex x) ^ 2 *
    |1 - (∑ i, reR G G' a₁ φr Ψ0 x i * h0 i) / rn (reR G G' a₁ φr Ψ0 x)| <
      (scaledC0 d * θ * ε) ^ 2 := by
  intro x hx
  have hη := H.ηpos
  have hθ := H.hθ0
  have hθ1 := H.hθ1
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hδ := H.hδ
  rcases (mem_dataSites G).1 hx with hx | hx
  · have h2 := b2_le hd0 hη hθ hθ1 H.hsmall (M := 1)
    have hb2 : (2 * d * (θ * η)) ^ 2 + 2 * θ ^ 2 * 1 * η + (θ ^ 2) ^ 2 * η ^ 2 ≤ 1 / 2 := by
      refine h2.trans ?_
      have : θ ^ 2 ≤ 1 := by nlinarith
      nlinarith [H.hsmall, mul_pos hθ hη]
    have hh := H.hh_of (H.hnj x hx)
    have := H.hr.re_r3 H.hφr psiR_im_zero H.hν H.hνk h0 H.hmass hx hb2 hh
    refine this.trans_le ?_
    refine r3_final hd0 hθ H.hδη H.hηε hη (by positivity) (by positivity) ?_ hδ
    have hθ2 : θ ^ 2 ≤ θ := by nlinarith
    have h5 : θ ^ 2 * η * (d + 2 * 1 + 1) ≤ θ * η * (d + 3) := by
      have : θ ^ 2 * η ≤ θ * η := mul_le_mul_of_nonneg_right hθ2 hη.le
      nlinarith
    have h6 : θ * η + θ ^ 2 * η ≤ 2 * (θ * η) := by nlinarith
    nlinarith
  · have hn : x ∉ G.Ω 1 := ((mem_collar G).1 hx).1
    have hl : G.layerIndex x = 0 := layerIndex_of_not_mem G hn
    have hh := H.hh_of (n := G.layerIndex x) (by rw [hl]; exact Nat.zero_le _)
    have hgs : G.spacing x ≤ θ * G'.spacing x := by
      have : G.spacing x = 1 := by
        unfold GeneratingSet.spacing; rw [hl]; simp
      rw [this]; exact (H.hcol x hx).2
    have := H.hr.re_r3_collar H.hφr psiR_im_zero H.hν H.hνk h0 H.hmass hx (H.hcol x hx).1 hgs hh
    refine this.trans_le ?_
    refine r3_final hd0 hθ H.hδη H.hηε hη le_rfl (by positivity) ?_ hδ
    have ht := mul_pos hθ hη
    nlinarith [mul_nonneg ht.le hd0]

theorem layerConst' : IsLayerConstant G (dPsi G G' a₁ φr φc Ψ0 Ψ'') := by
  intro n hn1 hnk x hx x' hx'
  funext i
  have h1 := congrFun (composeField_layerConst H.prec (compWeight L a₁) φc H.psiC_const n hn1 hnk
    x hx x' hx') i
  have h2 := congrFun (composeField_layerConst H.prec (compWeight L a₁) φr H.psiR_const n hn1 hnk
    x hx x' hx') i
  simp only at h1 h2
  simp only [dPsi, ccv, crv, compVec, h1, h2]

theorem hLayerConst' : IsLayerConstant G (hRes G h'') := by
  intro n hn1 hnk x hx x' hx'
  have hxΩ := G.layer_subset hn1 hnk hx
  have hn : G.layerIndex x = n := G.layerIndex_eq hn1 hnk hx
  have hx'b : x' ∈ G.blk (G.layerIndex x) x := by rw [hn]; exact hx'
  obtain ⟨hx'1, -, -, -, -⟩ := H.prec.block_compat hxΩ hx'b
  obtain ⟨hp1, hpk, hxp⟩ := G'.layerIndex_spec (H.prec.mem_Ω1 hxΩ)
  have hx'p : x' ∈ G'.blk (G'.layerIndex x) x := blk_subset_blk' H.prec hxΩ hx'b
  rw [hRes_of_mem h'' hxΩ, hRes_of_mem h'' hx'1]
  funext i
  exact congrFun (H.hPC.hLayerConst' _ hp1 hpk x hxp x' hx'p) i

theorem c1 : ∀ x x', IsInterfacePair G x x' →
    vn (dPsi G G' a₁ φr φc Ψ0 Ψ'' x - dPsi G G' a₁ φr φc Ψ0 Ψ'' x') <
      scaledC0 d * θ * ε := by
  intro x x' hxx'
  have hη := H.ηpos
  have hθ := H.hθ0
  have hθ1 := H.hθ1
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have h1 : vn (ccv G G' a₁ φc Ψ0 Ψ'' x - ccv G G' a₁ φc Ψ0 Ψ'' x') ≤ _ :=
    H.hc.interface hxx' (H.hB H.hbc)
  have h2 : vn (crv G G' a₁ φr Ψ0 x - crv G G' a₁ φr Ψ0 x') ≤ _ :=
    H.hr.interface hxx' (H.hB H.hbr)
  have e : dPsi G G' a₁ φr φc Ψ0 Ψ'' x - dPsi G G' a₁ φr φc Ψ0 Ψ'' x' =
      fun i => (ccv G G' a₁ φc Ψ0 Ψ'' x - ccv G G' a₁ φc Ψ0 Ψ'' x') i -
        (crv G G' a₁ φr Ψ0 x - crv G G' a₁ φr Ψ0 x') i := by
    funext i; simp only [dPsi, Pi.sub_apply]; ring
  rw [e]
  refine (vn_sub_le' _ _).trans_lt ?_
  unfold scaledC0
  have ht := mul_pos hθ hη
  have hT : θ * η ≤ θ * ε := mul_le_mul_of_nonneg_left H.hηε hθ.le
  have hdt : d * (θ * η) ≤ d * (θ * ε) := mul_le_mul_of_nonneg_left hT hd0
  have hθt : θ * (θ * η) ≤ θ * η := mul_le_of_le_one_left ht.le hθ1
  have hdT : 0 ≤ d * (θ * ε) := by have := H.εpos; positivity
  nlinarith

theorem c2a : ∀ x ∈ dataSites G, vn (dPsi G G' a₁ φr φc Ψ0 Ψ'' x) <
    ε + scaledC0 d * θ * ε := by
  intro x hx
  have hη := H.ηpos
  have hθ := H.hθ0
  have hθ1 := H.hθ1
  have hε := H.εpos
  have hδ := H.hδ
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hpos : 0 < scaledC0 d * θ * ε := by unfold scaledC0; positivity
  have hD : ∀ y ∈ dataSites G', vn (fun i => psiC Ψ0 Ψ'' y i - psiR Ψ0 y i) ≤ ε + δ := by
    intro y hy
    have e : (fun i => psiC Ψ0 Ψ'' y i - psiR Ψ0 y i) = Ψ'' y := by
      funext i; simp [psiC, psiR]
    rw [e]
    have := H.hPC.c2a y hy
    linarith
  show vn (fun i => ccv G G' a₁ φc Ψ0 Ψ'' x i - crv G G' a₁ φr Ψ0 x i) < _
  rcases (mem_dataSites G).1 hx with hx | hx
  · have hD' := hD x ((mem_dataSites G').2 (Or.inl (H.prec.mem_Ω1 hx)))
    have := compVec_sub_bound H.hc H.hr H.hθ1 (AΔ := ε) (e := δ) H.hdiff H.hδ.le hx hD'
    refine lt_of_le_of_lt this ?_
    unfold scaledC0
    have ht := mul_pos hθ hη
    have hT : θ * η ≤ θ * ε := mul_le_mul_of_nonneg_left H.hηε hθ.le
    have hθ2 : θ ^ 2 ≤ θ := by nlinarith
    have h1 : θ ^ 2 * (δ + 4 * d * η) ≤ θ * (δ + 4 * d * η) :=
      mul_le_mul_of_nonneg_right hθ2 (by positivity)
    have h2 : δ + 4 * d * η ≤ (4 * d + 1) * ε := by
      nlinarith [H.hδη, H.hηε, mul_le_mul_of_nonneg_left H.hηε hd0]
    have h3 : θ * (δ + 4 * d * η) ≤ θ * ((4 * d + 1) * ε) :=
      mul_le_mul_of_nonneg_left h2 hθ.le
    nlinarith [mul_nonneg (mul_pos hθ hε).le hd0]
  · have hn : x ∉ G.Ω 1 := ((mem_collar G).1 hx).1
    have hx' := (H.hcol x hx).1
    have e : (fun i => ccv G G' a₁ φc Ψ0 Ψ'' x i - crv G G' a₁ φr Ψ0 x i) =
        fun i => φc (⟨x, hx'⟩, i) - φr (⟨x, hx'⟩, i) := by
      funext i
      simp only [ccv, crv]
      rw [compVec_collar _ φc _ hx, compVec_collar _ φr _ hx, barVec_of_mem _ φc hx',
        barVec_of_mem _ φr hx']
    rw [e]
    exact lt_of_le_of_lt (H.hdiff ⟨x, hx'⟩) (by linarith)

theorem c2b : ∀ x ∈ dataSites G,
    ‖∑ i, (((reR G G' a₁ φr Ψ0 x i : ℝ) : ℂ) + dPsi G G' a₁ φr φc Ψ0 Ψ'' x i) *
        (((reR G G' a₁ φr Ψ0 x i : ℝ) : ℂ) + dPsi G G' a₁ φr φc Ψ0 Ψ'' x i) -
      ∑ i, ((reR G G' a₁ φr Ψ0 x i : ℝ) : ℂ) * ((reR G G' a₁ φr Ψ0 x i : ℝ) : ℂ)‖ <
      scaledC0 d * θ * ε := by
  intro x hx
  have hP := H.hPC.toInPsiTilde
  have hη := H.ηpos
  have hθ := H.hθ0
  have hθ1 := H.hθ1
  have hε := H.εpos
  have hδ := H.hδ
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hη6 : η ≤ 1 / 6 := by nlinarith [H.hsmall]
  have hpos : 0 < scaledC0 d * θ * ε := by unfold scaledC0; positivity
  have hcastr : ∀ x i, crv G G' a₁ φr Ψ0 x i = ((reR G G' a₁ φr Ψ0 x i : ℝ) : ℂ) := fun x i =>
    congrFun (H.real_crv x).eq_ofReal i
  have e0 : ∀ i, crv G G' a₁ φr Ψ0 x i + dPsi G G' a₁ φr φc Ψ0 Ψ'' x i =
      ccv G G' a₁ φc Ψ0 Ψ'' x i := fun i => by
    simp [dPsi]
  simp only [← hcastr x _]
  simp only [e0]
  rcases (mem_dataSites G).1 hx with hx | hx
  · have hMr : ∀ y ∈ G.blk (G.layerIndex x) x,
        vn (barVec G' (psiR Ψ0) φr y) ≤ 1 := fun y hy =>
      (barVec_vn_eq_one H.hφr H.hbr.unit _ (blk_mem_Ω1' H.prec hx hy).2).le
    have hMc : ∀ y ∈ G.blk (G.layerIndex x) x, vn (barVec G' (psiC Ψ0 Ψ'') φc y) ≤ 3 := by
      intro y hy
      have hy2 := (blk_mem_Ω1' H.prec hx hy).2
      have hyd : y ∈ dataSites G' := (mem_dataSites G').2 (Or.inl hy2)
      have e : barVec G' (psiC Ψ0 Ψ'') φc y =
          fun i => (φc (⟨y, hy2⟩, i) - psiC Ψ0 Ψ'' y i) + psiC Ψ0 Ψ'' y i := by
        funext i; rw [barVec_of_mem _ φc hy2]; ring
      rw [e]
      refine (vn_add' _ _).trans ?_
      have h1 := H.hbc.close ⟨y, hy2⟩
      have e2 : psiC Ψ0 Ψ'' y = fun i => (psiR Ψ0 y i) + Ψ'' y i := by
        funext i; simp [psiC, psiR]
      have h2 : vn (psiC Ψ0 Ψ'' y) ≤ vn (psiR Ψ0 y) + vn (Ψ'' y) := by
        rw [e2]; exact vn_add' _ _
      have h3 : vn (psiR Ψ0 y) ≤ 1 + δ := by
        have e3 : psiR Ψ0 y = fun i => (Ψ0 y i : ℂ) := rfl
        rw [e3, vn_ofReal]
        have := hP.r2 y hyd
        rw [← rn_sq] at this
        have h4 := rn_nonneg (Ψ0 y)
        have h5 := (abs_lt.1 this).2
        by_contra hcon
        push Not at hcon
        nlinarith
      have h6 := H.hPC.c2a y hyd
      have : vn (fun i => φc (⟨y, hy2⟩, i) - psiC Ψ0 Ψ'' y i) ≤ η := h1
      have hε1 := H.hε1
      linarith [H.hδη]
    have hc := H.hc.dot_sub_one hx hMc
    have hr := H.hr.dot_sub_one hx hMr
    have e : ∑ i, ccv G G' a₁ φc Ψ0 Ψ'' x i * ccv G G' a₁ φc Ψ0 Ψ'' x i -
        ∑ i, crv G G' a₁ φr Ψ0 x i * crv G G' a₁ φr Ψ0 x i =
        (∑ i, ccv G G' a₁ φc Ψ0 Ψ'' x i * ccv G G' a₁ φc Ψ0 Ψ'' x i - 1) -
        (∑ i, crv G G' a₁ φr Ψ0 x i * crv G G' a₁ φr Ψ0 x i - 1) := by ring
    rw [e]
    refine (norm_sub_le _ _).trans_lt ?_
    have hc' : ‖∑ i, ccv G G' a₁ φc Ψ0 Ψ'' x i * ccv G G' a₁ φc Ψ0 Ψ'' x i - 1‖ ≤ _ := hc
    have hr' : ‖∑ i, crv G G' a₁ φr Ψ0 x i * crv G G' a₁ φr Ψ0 x i - 1‖ ≤ _ := hr
    have b3 := b2_le hd0 hη hθ hθ1 H.hsmall (M := 3)
    have b1 := b2_le hd0 hη hθ hθ1 H.hsmall (M := 1)
    have hθ2 : θ ^ 2 ≤ θ := by nlinarith
    have hT : θ ^ 2 * η ≤ θ * ε := by
      calc θ ^ 2 * η ≤ θ * η := mul_le_mul_of_nonneg_right hθ2 hη.le
        _ ≤ θ * ε := mul_le_mul_of_nonneg_left H.hηε hθ.le
    unfold scaledC0
    nlinarith [mul_nonneg (mul_pos hθ hε).le hd0, mul_nonneg hd0 (sq_nonneg θ),
      mul_le_mul_of_nonneg_left H.hηε (mul_nonneg hd0 (sq_nonneg θ))]
  · have hn : x ∉ G.Ω 1 := ((mem_collar G).1 hx).1
    have hx' := (H.hcol x hx).1
    have e1 : ∀ i, ccv G G' a₁ φc Ψ0 Ψ'' x i = φc (⟨x, hx'⟩, i) := fun i => by
      simp only [ccv]; rw [compVec_collar _ φc _ hx]; exact barVec_of_mem _ φc hx' i
    have e2 : ∀ i, crv G G' a₁ φr Ψ0 x i = φr (⟨x, hx'⟩, i) := fun i => by
      simp only [crv]; rw [compVec_collar _ φr _ hx]; exact barVec_of_mem _ φr hx' i
    simp only [e1, e2, H.hbc.unit ⟨x, hx'⟩, H.hbr.unit ⟨x, hx'⟩, sub_self, norm_zero]
    exact hpos

theorem c3a : ∀ x ∈ G.Ω 1, ν * ((L : ℝ) ^ G.layerIndex x) ^ 2 * vn (hRes G h'' x) <
    (scaledC0 d * θ * ε) ^ 2 / ε := by
  intro x hx
  rw [hRes_of_mem h'' hx]
  have hθ := H.hθ0
  have hε := H.εpos
  have h1 := H.hPC.c3a x (H.prec.mem_Ω1 hx)
  have hsp : ((L : ℝ) ^ G.layerIndex x) ^ 2 ≤ θ ^ 2 * ((L : ℝ) ^ G'.layerIndex x) ^ 2 := by
    have := H.gap x hx
    unfold GeneratingSet.spacing at this
    calc ((L : ℝ) ^ G.layerIndex x) ^ 2 ≤ (θ * (L : ℝ) ^ G'.layerIndex x) ^ 2 :=
          pow_le_pow_left₀ (by positivity) this 2
      _ = _ := by ring
  have hν := H.hν
  have h2 : ν * ((L : ℝ) ^ G.layerIndex x) ^ 2 * vn (h'' x) ≤
      θ ^ 2 * (ν * ((L : ℝ) ^ G'.layerIndex x) ^ 2 * vn (h'' x)) := by
    have := mul_le_mul_of_nonneg_left hsp hν
    have := mul_le_mul_of_nonneg_right this (vn_nonneg (h'' x))
    nlinarith
  have h3 : θ ^ 2 * (ν * ((L : ℝ) ^ G'.layerIndex x) ^ 2 * vn (h'' x)) <
      θ ^ 2 * (δ ^ 2 / ε) := mul_lt_mul_of_pos_left h1 (by positivity)
  have h4 : δ ^ 2 / ε ≤ ε := by
    rw [div_le_iff₀ hε]
    have : δ ≤ ε := H.hδη.trans H.hηε
    nlinarith [H.hδ]
  have h5 : θ ^ 2 * (δ ^ 2 / ε) ≤ θ ^ 2 * ε := mul_le_mul_of_nonneg_left h4 (by positivity)
  have h6 : (scaledC0 d * θ * ε) ^ 2 / ε = (scaledC0 d * θ) ^ 2 * ε := by
    field_simp
  rw [h6]
  have h7 : θ ^ 2 * ε ≤ (scaledC0 d * θ) ^ 2 * ε := by
    unfold scaledC0
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    have : 1 ≤ (8 * (d : ℝ) + 12) ^ 2 := by nlinarith
    have h8 : θ ^ 2 * ε * 1 ≤ θ ^ 2 * ε * (8 * (d : ℝ) + 12) ^ 2 :=
      mul_le_mul_of_nonneg_left this (by positivity)
    nlinarith
  linarith

theorem rn_lower {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.Ω 1) :
    2 / 3 ≤ rn (reR G G' a₁ φr Ψ0 x) := by
  have hη := H.ηpos
  have hθ := H.hθ0
  have hθ1 := H.hθ1
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have h2 := b2_le hd0 hη hθ hθ1 H.hsmall (M := 1)
  have hbr2 : |rn (reR G G' a₁ φr Ψ0 x) ^ 2 - 1| ≤ (d + 3) * η := by
    refine (H.hr.re_r2 H.hφr psiR_im_zero hx).trans (h2.trans ?_)
    have : θ ^ 2 ≤ 1 := by nlinarith
    have h3 : θ ^ 2 * η ≤ η := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left h3 (by linarith : (0 : ℝ) ≤ d + 2 * 1 + 1)]
  have hr2 : 1 / 2 ≤ rn (reR G G' a₁ φr Ψ0 x) ^ 2 := by
    have := (abs_le.1 hbr2).1
    nlinarith [H.hsmall]
  have hrn0 := rn_nonneg (reR G G' a₁ φr Ψ0 x)
  by_contra hcon
  push Not at hcon
  nlinarith

theorem dist_bound {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.Ω 1) :
    rn (fun i => reR G G' a₁ φr Ψ0 x i - Ψ0 x i) ≤ (2 * d + 2) * η := by
  have hx' := H.prec.mem_Ω1 hx
  have hη := H.ηpos
  have hθ := H.hθ0
  have hθ1 := H.hθ1
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hreal := H.real_crv x
  have h0 : (fun i => reR G G' a₁ φr Ψ0 x i - Ψ0 x i) =
      fun i => (crv G G' a₁ φr Ψ0 x i).re - Ψ0 x i := rfl
  rw [h0, rn_re_sub_cast_eq_vn hreal (Ψ0 x)]
  have t1 := H.hr.compVec_sub_mean hx
  have t2 := H.hr.mean_sub_bar hx (x_mem_blk (G := G) _ x)
  have t3 : vn ((fun i => φr (⟨x, hx'⟩, i)) - psiR Ψ0 x) ≤ η := H.hbr.close ⟨x, hx'⟩
  have e : barVec G' (psiR Ψ0) φr x = fun i => φr (⟨x, hx'⟩, i) := by
    funext i; exact barVec_of_mem _ φr hx' i
  rw [e] at t2
  have u1 := vn_triangle (compVec G G' (compWeight L a₁) φr (psiR Ψ0) x)
    (meanVec G (barVec G' (psiR Ψ0) φr) x) (fun i => φr (⟨x, hx'⟩, i))
  have u2 := vn_triangle (compVec G G' (compWeight L a₁) φr (psiR Ψ0) x)
    (fun i => φr (⟨x, hx'⟩, i)) (psiR Ψ0 x)
  show vn (compVec G G' (compWeight L a₁) φr (psiR Ψ0) x - psiR Ψ0 x) ≤ _
  have hθ2 : θ ^ 2 ≤ 1 := by nlinarith
  have hθη : θ * η ≤ η := by nlinarith
  have h4 : θ ^ 2 * η ≤ η := by nlinarith
  have h5 : 2 * d * (θ * η) ≤ 2 * d * η := by nlinarith
  linarith

theorem c3b : ∀ x ∈ G.Ω 1, ν * ((L : ℝ) ^ G.layerIndex x) ^ 2 *
    ‖∑ i, ((reR G G' a₁ φr Ψ0 x i / rn (reR G G' a₁ φr Ψ0 x) : ℝ) : ℂ) * hRes G h'' x i‖ <
      (scaledC0 d * θ * ε) ^ 2 := by
  intro x hx
  have hx' := H.prec.mem_Ω1 hx
  have hxd : x ∈ dataSites G' := (mem_dataSites G').2 (Or.inl hx')
  have hη := H.ηpos
  have hθ := H.hθ0
  have hε := H.εpos
  have hδ := H.hδ
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hrlow := H.rn_lower hx
  have hrpos : 0 < rn (reR G G' a₁ φr Ψ0 x) := by linarith
  have hr0pos : 0 < rn (Ψ0 x) := by
    have h1 := (abs_lt.1 (H.hPC.toInPsiTilde.r2 x hxd)).1
    rw [← rn_sq] at h1
    have := rn_nonneg (Ψ0 x)
    by_contra hcon
    push Not at hcon
    have h2 : rn (Ψ0 x) = 0 := le_antisymm hcon this
    rw [h2] at h1
    nlinarith [H.hδη, H.hηε, H.hε1]
  have hτ := H.dist_bound hx
  have hτ0 : 0 ≤ (2 * d + 2) * η := by positivity
  have hnorm := rn_normalize_sub (reR G G' a₁ φr Ψ0 x) (Ψ0 x) hrpos hr0pos
  have hru : rn (fun i => reR G G' a₁ φr Ψ0 x i / rn (reR G G' a₁ φr Ψ0 x) -
      Ψ0 x i / rn (Ψ0 x)) ≤ 3 * ((2 * d + 2) * η) := by
    refine hnorm.trans ?_
    rw [div_le_iff₀ hrpos]
    nlinarith
  rw [hRes_of_mem h'' hx]
  have hsum : ∑ i, ((reR G G' a₁ φr Ψ0 x i / rn (reR G G' a₁ φr Ψ0 x) : ℝ) : ℂ) * h'' x i =
      ∑ i, ((Ψ0 x i / rn (Ψ0 x) : ℝ) : ℂ) * h'' x i +
      ∑ i, ((reR G G' a₁ φr Ψ0 x i / rn (reR G G' a₁ φr Ψ0 x) - Ψ0 x i / rn (Ψ0 x) : ℝ) : ℂ) *
        h'' x i := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    push_cast; ring
  rw [hsum]
  have hB : ‖∑ i, ((reR G G' a₁ φr Ψ0 x i / rn (reR G G' a₁ φr Ψ0 x) - Ψ0 x i / rn (Ψ0 x) : ℝ) :
      ℂ) * h'' x i‖ ≤ 3 * ((2 * d + 2) * η) * vn (h'' x) := by
    refine (norm_dot_le _ _).trans ?_
    rw [vn_ofReal]
    exact mul_le_mul_of_nonneg_right hru (vn_nonneg _)
  have hT := H.hPC.c3b x hx'
  have hV := H.hPC.c3a x hx'
  have hsp : ((L : ℝ) ^ G.layerIndex x) ^ 2 ≤ θ ^ 2 * ((L : ℝ) ^ G'.layerIndex x) ^ 2 := by
    have := H.gap x hx
    unfold GeneratingSet.spacing at this
    calc ((L : ℝ) ^ G.layerIndex x) ^ 2 ≤ (θ * (L : ℝ) ^ G'.layerIndex x) ^ 2 :=
          pow_le_pow_left₀ (by positivity) this 2
      _ = _ := by ring
  have hmono : ν * ((L : ℝ) ^ G.layerIndex x) ^ 2 ≤
      θ ^ 2 * (ν * ((L : ℝ) ^ G'.layerIndex x) ^ 2) := by
    have := mul_le_mul_of_nonneg_left hsp H.hν
    nlinarith
  have hνn0 : 0 ≤ ν * ((L : ℝ) ^ G.layerIndex x) ^ 2 := by have := H.hν; positivity
  have hnum := c3b_numeric2 hd0 hδ H.hδη H.hηε
  set S1 := ‖∑ i, ((Ψ0 x i / rn (Ψ0 x) : ℝ) : ℂ) * h'' x i‖ with hS1
  set S2 := ‖∑ i, ((reR G G' a₁ φr Ψ0 x i / rn (reR G G' a₁ φr Ψ0 x) - Ψ0 x i / rn (Ψ0 x) : ℝ) :
    ℂ) * h'' x i‖ with hS2
  have hS : ‖∑ i, ((Ψ0 x i / rn (Ψ0 x) : ℝ) : ℂ) * h'' x i +
      ∑ i, ((reR G G' a₁ φr Ψ0 x i / rn (reR G G' a₁ φr Ψ0 x) - Ψ0 x i / rn (Ψ0 x) : ℝ) : ℂ) *
        h'' x i‖ ≤ S1 + S2 := norm_add_le _ _
  have hθ2 : 0 ≤ θ ^ 2 := by positivity
  have h1 : ν * ((L : ℝ) ^ G.layerIndex x) ^ 2 * S1 ≤
      θ ^ 2 * (ν * ((L : ℝ) ^ G'.layerIndex x) ^ 2 * S1) := by
    have := mul_le_mul_of_nonneg_right hmono (norm_nonneg
      (∑ i, ((Ψ0 x i / rn (Ψ0 x) : ℝ) : ℂ) * h'' x i))
    nlinarith
  have h2 : ν * ((L : ℝ) ^ G.layerIndex x) ^ 2 * S2 ≤
      θ ^ 2 * (3 * ((2 * d + 2) * η) * (ν * ((L : ℝ) ^ G'.layerIndex x) ^ 2 * vn (h'' x))) := by
    calc ν * ((L : ℝ) ^ G.layerIndex x) ^ 2 * S2
        ≤ ν * ((L : ℝ) ^ G.layerIndex x) ^ 2 * (3 * ((2 * d + 2) * η) * vn (h'' x)) :=
          mul_le_mul_of_nonneg_left hB hνn0
      _ = 3 * ((2 * d + 2) * η) * ((ν * ((L : ℝ) ^ G.layerIndex x) ^ 2) * vn (h'' x)) := by ring
      _ ≤ 3 * ((2 * d + 2) * η) * ((θ ^ 2 * (ν * ((L : ℝ) ^ G'.layerIndex x) ^ 2)) *
            vn (h'' x)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hmono (vn_nonneg _))
            (by positivity)
      _ = _ := by ring
  have h3 := mul_lt_mul_of_pos_left hV (by positivity : 0 < 3 * ((2 * d + 2) * η))
  have hT' : θ ^ 2 * (ν * ((L : ℝ) ^ G'.layerIndex x) ^ 2 * S1) ≤ θ ^ 2 * δ ^ 2 :=
    mul_le_mul_of_nonneg_left hT.le hθ2
  have hV' : θ ^ 2 * (3 * ((2 * d + 2) * η) * (ν * ((L : ℝ) ^ G'.layerIndex x) ^ 2 *
      vn (h'' x))) < θ ^ 2 * (3 * ((2 * d + 2) * η) * (δ ^ 2 / ε)) :=
    mul_lt_mul_of_pos_left h3 (by positivity)
  calc ν * ((L : ℝ) ^ G.layerIndex x) ^ 2 * ‖_‖
      ≤ ν * ((L : ℝ) ^ G.layerIndex x) ^ 2 * (S1 + S2) :=
        mul_le_mul_of_nonneg_left hS hνn0
    _ = ν * ((L : ℝ) ^ G.layerIndex x) ^ 2 * S1 + ν * ((L : ℝ) ^ G.layerIndex x) ^ 2 * S2 := by
        ring
    _ < θ ^ 2 * (δ ^ 2 + 3 * ((2 * d + 2) * η) * (δ ^ 2 / ε)) := by nlinarith
    _ ≤ θ ^ 2 * ((8 * d + 12) * ε) ^ 2 := mul_le_mul_of_nonneg_left hnum hθ2
    _ = (scaledC0 d * θ * ε) ^ 2 := by unfold scaledC0; ring

/-- **(R-S), the scaled composition**: see `scaledComposition`. -/
theorem scaledPsiC : ScaledPsiC G ν (scaledC0 d * θ) ε j (reR G G' a₁ φr Ψ0) h0
    (dPsi G G' a₁ φr φc Ψ0 Ψ'') (hRes G h'') :=
  { layerConst := H.layerConst
    r1 := fun x x' hxx' => H.r1 x x' hxx'
    r2 := H.r2
    r3 := H.r3
    r4 := H.r4
    layerConst' := H.layerConst'
    hLayerConst' := H.hLayerConst'
    c1 := H.c1
    c2a := H.c2a
    c2b := H.c2b
    c3a := H.c3a
    c3b := H.c3b }

end HypS

/-- **(R-S) the scaled composition** (SMALLFIELD.md §1.7; review S-02).  Under `HypS` -- `𝔹_j ≺ 𝔹'_k`
with the scale gap `ℓ ≤ θ ℓ'`, `θ = L^{j-k}`, the data `(Ψ0 + Ψ'', h0 + h'') ∈ Ψ̃^c(𝔹'_k; δ, ε)` and
the fields `φr`, `φc` with the bounds of Theorem 5.2 (3) of size `η ≤ ε` -- the composed data
(formula (6.2)) satisfy, with `σ = C₀ θ` (`C₀ = 8 d + 12`):
(i) `|Ψ(y) - Ψ(y')| < σ ε` and `|Ψ'(y) - Ψ'(y')| < σ ε` for adjacent blocks;
(ii) the second-order condition `| |Ψ|² - 1 | < σ² ε` (R2'), `|Ψ'| < ε + σ ε`,
`|(Ψ + Ψ')·(Ψ + Ψ') - Ψ·Ψ| < σ ε`;
(iii) `ν L^{2n} |1 - Ψ₀·h| < (σ ε)²`, `ν L^{2j} |h·h - 1| < (σ ε)²` (`ν_j = ν L^{2j}`), `ν L^{2n} |h'| <
σ² ε`, `ν L^{2n} |Ψ₀·h'| < (σ ε)²`. -/
theorem scaledComposition {G : GeneratingSet d L N₀ k ϱ} {G' : GeneratingSet d L N₀ k ϱ'}
    {a₁ ν δ ε η θ : ℝ} {j : ℕ} {Ψ0 : Torus d (N₀ * L ^ k) → Fin N → ℝ} {h0 : Fin N → ℝ}
    {Ψ'' h'' : Torus d (N₀ * L ^ k) → Fin N → ℂ} {φr φc : G'.Ω 1 × Fin N → ℂ}
    (H : HypS G G' a₁ ν δ ε η θ j Ψ0 h0 Ψ'' h'' φr φc) :
    ScaledPsiC G ν (scaledC0 d * θ) ε j (reR G G' a₁ φr Ψ0) h0
      (dPsi G G' a₁ φr φc Ψ0 Ψ'') (hRes G h'') :=
  H.scaledPsiC

end ScaledDomain

end Balaban.Background
