/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.DecoupledBackground
public import Balaban.Background.Composition
public import Balaban.Localization.NC3
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Theorem I-4b (v): the decoupled composition `ψ(𝔹_j, 𝔹'_k; s)`

The composed field `ψ(𝔹_j, 𝔹'_k; s)` is `composeField` of BG (6.2) evaluated at the decoupled
background field `φ'_k(s)` of `𝔹'_k`.  Since (6.2) is affine in `(φ', Ψ')`:

* `composeField_sub`: `ψ(s) - ψ(1) = composeField (φ'(s) - φ'(1)) 0` (P3 (2.59));
* `analyticAt_composeField`: coordinatewise analyticity in the parameters;
* `composeField_congr`: locality in comparison form, with the explicit dependency set
  `composeDep`;
* `composeField_close`: closeness (P3 (2.60)) from closeness of the fine fields;
* `i4b_compose_*`: the statements for the decoupled background field.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Finset Matrix

section Algebra

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ ϱ' : ℝ}
variable {G : GeneratingSet d L N₀ k ϱ} {G' : GeneratingSet d L N₀ k ϱ'}

theorem blockMean_sub (n : ℕ) (w w' : Torus d (N₀ * L ^ k) → ℂ) (x : Torus d (N₀ * L ^ k)) :
    blockMean G n (fun y => w y - w' y) x = blockMean G n w x - blockMean G n w' x := by
  unfold blockMean
  rw [Finset.sum_sub_distrib]; ring

theorem svec_sub_apply (u w : G'.Ω 1 × Fin N → ℂ) (y : Torus d (N₀ * L ^ k)) (i : Fin N) :
    svec G' (u - w) y i = svec G' u y i - svec G' w y i := by
  unfold svec zeroExt
  split_ifs <;> simp

/-- **Affine structure of (6.2)** (P3 (2.59)): the difference of two composed fields with the same
`Ψ'` is the composed field of the difference with `Ψ' = 0`. -/
theorem composeField_sub (a : ℕ → ℝ) (φ φ₁ : G'.Ω 1 × Fin N → ℂ)
    (Ψ : Torus d (N₀ * L ^ k) → Fin N → ℂ) (x : Torus d (N₀ * L ^ k)) (i : Fin N) :
    composeField G G' a φ Ψ x i - composeField G G' a φ₁ Ψ x i =
      composeField G G' a (φ - φ₁) (0 : Torus d (N₀ * L ^ k) → Fin N → ℂ) x i := by
  by_cases hx : x ∈ G.Ω 1
  · rw [composeField_of_mem a φ Ψ hx, composeField_of_mem a φ₁ Ψ hx,
      composeField_of_mem a (φ - φ₁) _ hx]
    have e : (fun y => svec G' (φ - φ₁) y i) =
        fun y => svec G' φ y i - svec G' φ₁ y i := funext fun y => svec_sub_apply _ _ y i
    rw [e, blockMean_sub, blockMean_sub]
    simp only [Pi.zero_apply]
    ring
  · by_cases hc : x ∈ collar G
    · rw [composeField_of_collar a φ Ψ hc, composeField_of_collar a φ₁ Ψ hc,
        composeField_of_collar a (φ - φ₁) _ hc]
      unfold barField
      split_ifs <;> simp
    · have hd : x ∉ dataSites G := fun h => by
        rcases (mem_dataSites G).1 h with h | h
        · exact hx h
        · exact hc h
      rw [composeField_of_not_mem a φ Ψ hd, composeField_of_not_mem a φ₁ Ψ hd,
        composeField_of_not_mem a (φ - φ₁) _ hd]
      simp

/-- The sites on which `composeField G G' a φ Ψ x` reads `φ`: the `n`-block and the `p`-block of
`x`, and `x` itself. -/
noncomputable def composeDep (G : GeneratingSet d L N₀ k ϱ) (G' : GeneratingSet d L N₀ k ϱ')
    (x : Torus d (N₀ * L ^ k)) : Finset (Torus d (N₀ * L ^ k)) := by
  classical
  exact if x ∈ G.Ω 1 then insert x (G.blk (G.layerIndex x) x ∪ G'.blk (G'.layerIndex x) x)
    else {x}

theorem self_mem_composeDep (x : Torus d (N₀ * L ^ k)) : x ∈ composeDep G G' x := by
  classical
  unfold composeDep
  split_ifs
  · exact Finset.mem_insert_self _ _
  · exact Finset.mem_singleton_self _

/-- **Locality of (6.2)**: `composeField G G' a φ Ψ x i` depends only on the values of `svec φ` on
`composeDep x` and on `Ψ x`. -/
theorem composeField_congr (a : ℕ → ℝ) {φ φ₂ : G'.Ω 1 × Fin N → ℂ}
    {Ψ Ψ₂ : Torus d (N₀ * L ^ k) → Fin N → ℂ} {x : Torus d (N₀ * L ^ k)}
    (hφ : ∀ y ∈ composeDep G G' x, ∀ j, svec G' φ y j = svec G' φ₂ y j)
    (hΨ : ∀ j, Ψ x j = Ψ₂ x j) (i : Fin N) :
    composeField G G' a φ Ψ x i = composeField G G' a φ₂ Ψ₂ x i := by
  classical
  by_cases hx : x ∈ G.Ω 1
  · have hdep : composeDep G G' x = insert x (G.blk (G.layerIndex x) x ∪
        G'.blk (G'.layerIndex x) x) := by
      unfold composeDep; simp [hx]
    rw [composeField_of_mem a φ Ψ hx, composeField_of_mem a φ₂ Ψ₂ hx, hΨ i]
    have h1 : blockMean G (G.layerIndex x) (fun y => svec G' φ y i) x =
        blockMean G (G.layerIndex x) (fun y => svec G' φ₂ y i) x := by
      unfold blockMean
      congr 1
      refine Finset.sum_congr rfl fun y hy => hφ y ?_ i
      rw [hdep]
      exact Finset.mem_insert_of_mem (Finset.mem_union_left _ hy)
    have h2 : blockMean G' (G'.layerIndex x) (fun y => svec G' φ y i) x =
        blockMean G' (G'.layerIndex x) (fun y => svec G' φ₂ y i) x := by
      unfold blockMean
      congr 1
      refine Finset.sum_congr rfl fun y hy => hφ y ?_ i
      rw [hdep]
      exact Finset.mem_insert_of_mem (Finset.mem_union_right _ hy)
    rw [h1, h2]
  · by_cases hc : x ∈ collar G
    · rw [composeField_of_collar a φ Ψ hc, composeField_of_collar a φ₂ Ψ₂ hc]
      unfold barField
      split_ifs with h
      · have := hφ x (self_mem_composeDep x) i
        rwa [svec_of_mem G' φ ⟨x, h⟩ i, svec_of_mem G' φ₂ ⟨x, h⟩ i] at this
      · exact hΨ i
    · have hd : x ∉ dataSites G := fun h => by
        rcases (mem_dataSites G).1 h with h | h
        · exact hx h
        · exact hc h
      rw [composeField_of_not_mem a φ Ψ hd, composeField_of_not_mem a φ₂ Ψ₂ hd]

end Algebra

section Analytic

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ ϱ' : ℝ}
variable {G : GeneratingSet d L N₀ k ϱ} {G' : GeneratingSet d L N₀ k ϱ'}

theorem analyticAt_svec {Q : Type*} [NormedAddCommGroup Q] [NormedSpace ℂ Q] {q : Q}
    (φ : Q → G'.Ω 1 × Fin N → ℂ) (hφ : ∀ r, AnalyticAt ℂ (fun q => φ q r) q)
    (y : Torus d (N₀ * L ^ k)) (i : Fin N) :
    AnalyticAt ℂ (fun q => svec G' (φ q) y i) q := by
  unfold svec zeroExt
  by_cases hy : y ∈ G'.Ω 1
  · simp only [hy, ↓reduceDIte]
    exact hφ _
  · simp only [hy, ↓reduceDIte]
    exact analyticAt_const

theorem analyticAt_blockMean {Q : Type*} [NormedAddCommGroup Q] [NormedSpace ℂ Q] {q : Q}
    (n : ℕ) (w : Q → Torus d (N₀ * L ^ k) → ℂ) (hw : ∀ y, AnalyticAt ℂ (fun q => w q y) q)
    (x : Torus d (N₀ * L ^ k)) :
    AnalyticAt ℂ (fun q => blockMean G n (w q) x) q := by
  unfold blockMean
  exact analyticAt_const.mul (Finset.analyticAt_fun_sum _ fun y _ => hw y)

/-- **Analyticity of (6.2)** in the parameters: if the coordinates of `φ'` and `Ψ'` are analytic,
so are the coordinates of the composed field. -/
theorem analyticAt_composeField {Q : Type*} [NormedAddCommGroup Q] [NormedSpace ℂ Q] {q : Q}
    (a : ℕ → ℝ) (φ : Q → G'.Ω 1 × Fin N → ℂ) (Ψ : Q → Torus d (N₀ * L ^ k) → Fin N → ℂ)
    (hφ : ∀ r, AnalyticAt ℂ (fun q => φ q r) q)
    (hΨ : ∀ y j, AnalyticAt ℂ (fun q => Ψ q y j) q) (x : Torus d (N₀ * L ^ k)) (i : Fin N) :
    AnalyticAt ℂ (fun q => composeField G G' a (φ q) (Ψ q) x i) q := by
  by_cases hx : x ∈ G.Ω 1
  · have e : (fun q => composeField G G' a (φ q) (Ψ q) x i) = fun q =>
        blockMean G (G.layerIndex x) (fun y => svec G' (φ q) y i) x +
          ((a (G'.layerIndex x) / a (G.layerIndex x) *
            (((L : ℝ) ^ G.layerIndex x) ^ 2 / ((L : ℝ) ^ G'.layerIndex x) ^ 2) : ℝ) : ℂ) *
            (Ψ q x i - blockMean G' (G'.layerIndex x) (fun y => svec G' (φ q) y i) x) :=
      funext fun q => composeField_of_mem a (φ q) (Ψ q) hx i
    rw [e]
    exact (analyticAt_blockMean _ _ (fun y => analyticAt_svec φ hφ y i) x).add
      (analyticAt_const.mul ((hΨ x i).sub
        (analyticAt_blockMean _ _ (fun y => analyticAt_svec φ hφ y i) x)))
  · by_cases hc : x ∈ collar G
    · have e : (fun q => composeField G G' a (φ q) (Ψ q) x i) =
          fun q => barField G' (Ψ q) (φ q) x i :=
        funext fun q => composeField_of_collar a (φ q) (Ψ q) hc i
      rw [e]
      unfold barField
      by_cases h : x ∈ G'.Ω 1
      · simp only [h, ↓reduceDIte]; exact hφ _
      · simp only [h, ↓reduceDIte]; exact hΨ x i
    · have hd : x ∉ dataSites G := fun h => by
        rcases (mem_dataSites G).1 h with h | h
        · exact hx h
        · exact hc h
      have e : (fun q => composeField G G' a (φ q) (Ψ q) x i) = fun _ => 0 :=
        funext fun q => composeField_of_not_mem a (φ q) (Ψ q) hd i
      rw [e]; exact analyticAt_const

end Analytic


section Close

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱ' : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {G' : GeneratingSet d L (N₁ * L ^ m₁) K ϱ'}

/-- A block mean is bounded by the maximum over the block. -/
theorem norm_blockMean_le (n : ℕ) (hn : n ≤ K) (w : CTorus d L N₁ m₁ K → ℂ)
    (x : CTorus d L N₁ m₁ K) {B : ℝ} (hw : ∀ y ∈ G.blk n x, ‖w y‖ ≤ B) :
    ‖blockMean G n w x‖ ≤ B := by
  unfold blockMean
  have hc := card_blk_cast G n hn x
  have hp : (0 : ℝ) < ((L : ℝ) ^ n) ^ d := by
    have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hp)]
  have hsum : ‖∑ y ∈ G.blk n x, w y‖ ≤ ((G.blk n x).card : ℝ) * B := by
    refine (norm_sum_le _ _).trans ?_
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum hw
  rw [hc] at hsum
  calc (((L : ℝ) ^ n) ^ d)⁻¹ * ‖∑ y ∈ G.blk n x, w y‖ ≤ (((L : ℝ) ^ n) ^ d)⁻¹ * (((L : ℝ) ^ n) ^ d * B) :=
        mul_le_mul_of_nonneg_left hsum (inv_nonneg.2 hp.le)
    _ = B := by field_simp

/-- **Closeness of the composed field (P3 (2.60))**: if the fine field `δ` is bounded by
`C e^{-γ d(·, W)}` then the composed field `composeField δ 0` (the difference of two decoupled
composed fields) is bounded by `5 e^{2dγ} C e^{-γ d(x, W)}`. -/
theorem composeField_close (h : Precedes G G') {a : ℕ → ℝ} (ha : IsAdmissibleWeights K a)
    {γ C : ℝ} (hγ : 0 ≤ γ) (hC : 0 ≤ C) {W : Finset (CTorus d L N₁ m₁ K)}
    {δ : G'.Ω 1 × Fin N → ℂ}
    (hδ : ∀ (y : CTorus d L N₁ m₁ K) (i : Fin N), ‖svec G' δ y i‖ ≤
      C * decay γ (siteSetDist G' W y)) (x : CTorus d L N₁ m₁ K) (i : Fin N) :
    ‖composeField G G' a δ (0 : CTorus d L N₁ m₁ K → Fin N → ℂ) x i‖ ≤
      5 * Real.exp (γ * (2 * d)) * C * decay γ (siteSetDist G' W x) := by
  have hd2 : (0 : ℝ) ≤ 2 * d := by positivity
  have hE : 1 ≤ Real.exp (γ * (2 * d)) := Real.one_le_exp (by positivity)
  have hdec := decay_nonneg γ (siteSetDist G' W x)
  have hR : 0 ≤ 5 * Real.exp (γ * (2 * d)) * C * decay γ (siteSetDist G' W x) := by positivity
  -- from a point `y` at path distance `≤ 2d` from `x`
  have key : ∀ y : CTorus d L N₁ m₁ K, G'.pathDist x y ≤ ENNReal.ofReal (2 * d) →
      ‖svec G' δ y i‖ ≤ Real.exp (γ * (2 * d)) * C * decay γ (siteSetDist G' W x) := by
    intro y hxy
    have h1 : siteSetDist G' W x ≤ ENNReal.ofReal (2 * d) + siteSetDist G' W y :=
      (setDist_triangle W x y).trans (add_le_add_left hxy _)
    have h2 := Balaban.Reflection.decay_le_exp_mul hγ hd2 h1
    calc ‖svec G' δ y i‖ ≤ C * decay γ (siteSetDist G' W y) := hδ y i
      _ ≤ C * (Real.exp (γ * (2 * d)) * decay γ (siteSetDist G' W x)) :=
          mul_le_mul_of_nonneg_left h2 hC
      _ = _ := by ring
  by_cases hx : x ∈ G.Ω 1
  · rw [composeField_of_mem a δ _ hx]
    obtain ⟨hn1, hnk, hxn⟩ := G.layerIndex_spec hx
    obtain ⟨hp1, hpk, hxp⟩ := G'.layerIndex_spec (h.mem_Ω1 hx)
    have hnp := h.layerIndex_le hx
    set B : ℝ := Real.exp (γ * (2 * d)) * C * decay γ (siteSetDist G' W x) with hBdef
    have hB0 : 0 ≤ B := by positivity
    have b1 : ‖blockMean G (G.layerIndex x) (fun y => svec G' δ y i) x‖ ≤ B := by
      refine norm_blockMean_le _ hnk _ x fun y hy => key y ?_
      have hb := GeneratingSet.mem_blk.1 hy
      exact G'.pathDist_block_le hp1 hpk hxp (jBlock_eq_of_le hnp hpk hb)
    have b2 : ‖blockMean G' (G'.layerIndex x) (fun y => svec G' δ y i) x‖ ≤ B := by
      refine norm_blockMean_le _ hpk _ x fun y hy => key y ?_
      exact G'.pathDist_block_le hp1 hpk hxp (GeneratingSet.mem_blk.1 hy)
    have hcoef : ‖(((a (G'.layerIndex x) / a (G.layerIndex x) *
        (((L : ℝ) ^ G.layerIndex x) ^ 2 / ((L : ℝ) ^ G'.layerIndex x) ^ 2) : ℝ)) : ℂ)‖ ≤ 4 := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      have han := ha _ hn1 hnk
      have hap := ha _ hp1 hpk
      have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by have := NeZero.ne L; omega : 1 ≤ L)
      have hr : ((L : ℝ) ^ G.layerIndex x) ^ 2 / ((L : ℝ) ^ G'.layerIndex x) ^ 2 ≤ 1 := by
        rw [div_le_one (by positivity)]
        have := pow_le_pow_right₀ hL1 hnp
        nlinarith [pow_nonneg (by linarith : (0 : ℝ) ≤ L) (G.layerIndex x)]
      have hr0 : 0 ≤ ((L : ℝ) ^ G.layerIndex x) ^ 2 / ((L : ℝ) ^ G'.layerIndex x) ^ 2 := by
        positivity
      have hq0 : 0 ≤ a (G'.layerIndex x) / a (G.layerIndex x) :=
        div_nonneg (by linarith [hap.1]) (by linarith [han.1])
      have hq : a (G'.layerIndex x) / a (G.layerIndex x) ≤ 4 := by
        rw [div_le_iff₀ (by linarith [han.1])]
        nlinarith [hap.2, han.1]
      rw [abs_of_nonneg (mul_nonneg hq0 hr0)]
      nlinarith
    simp only [Pi.zero_apply, zero_sub]
    calc ‖blockMean G (G.layerIndex x) (fun y => svec G' δ y i) x +
          (((a (G'.layerIndex x) / a (G.layerIndex x) *
            (((L : ℝ) ^ G.layerIndex x) ^ 2 / ((L : ℝ) ^ G'.layerIndex x) ^ 2) : ℝ)) : ℂ) *
            (-blockMean G' (G'.layerIndex x) (fun y => svec G' δ y i) x)‖
        ≤ ‖blockMean G (G.layerIndex x) (fun y => svec G' δ y i) x‖ +
          ‖(((a (G'.layerIndex x) / a (G.layerIndex x) *
            (((L : ℝ) ^ G.layerIndex x) ^ 2 / ((L : ℝ) ^ G'.layerIndex x) ^ 2) : ℝ)) : ℂ)‖ *
            ‖blockMean G' (G'.layerIndex x) (fun y => svec G' δ y i) x‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, norm_neg]
      _ ≤ B + 4 * B := by
          refine add_le_add b1 (mul_le_mul hcoef b2 (norm_nonneg _) (by norm_num))
      _ = 5 * Real.exp (γ * (2 * d)) * C * decay γ (siteSetDist G' W x) := by
          rw [hBdef]; ring
  · by_cases hc : x ∈ collar G
    · rw [composeField_of_collar a δ _ hc]
      unfold barField
      by_cases hx' : x ∈ G'.Ω 1
      · simp only [hx', ↓reduceDIte]
        have := hδ x i
        rw [svec_of_mem G' δ ⟨x, hx'⟩ i] at this
        refine this.trans ?_
        have : C * decay γ (siteSetDist G' W x) * 1 ≤
            C * decay γ (siteSetDist G' W x) * (5 * Real.exp (γ * (2 * d))) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          linarith
        nlinarith
      · simp only [hx', ↓reduceDIte, Pi.zero_apply, norm_zero]; exact hR
    · have hd : x ∉ dataSites G := fun h => by
        rcases (mem_dataSites G).1 h with h | h
        · exact hx h
        · exact hc h
      rw [composeField_of_not_mem a δ _ hd, norm_zero]; exact hR

end Close


/-! ### The decoupled composition -/

section Decoupled

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱ' : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {G' : GeneratingSet d L (N₁ * L ^ m₁) K ϱ'}
variable {a : ℕ → ℝ} {ν : ℝ}

/-- **Theorem I-4b (v), `s = 1`**: the decoupled composition at `s ≡ 1` is the composed field
`ψ(𝔹_j, 𝔹'_k)` of BG (6.2) evaluated at the background field `bgFieldC` of `𝔹'_k`. -/
theorem i4b_compose_one {c BG : ℝ} (hS : DecSpecs d L c BG) (S : DGSetting G' a ν)
    (HB : BgHyp d L K ϱ' a ν) {κ : ℝ} (hκ : 0 ≤ κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δ ε : ℝ} (hδ0 : 0 < δ) (hδε : δ ≤ ε)
    (hε : ε ≤ bgC0 d L N) (hδ : δ ≤ c7 d L N BG κ)
    (hνε : ν * ((L : ℝ) ^ K) ^ 2 * ε ^ 2 ≤ δ ^ 2) {D' : BgData G' N}
    (hD : InDomainC G' ν δ ε D') {φ : G'.Ω 1 × Fin N → ℂ} {α : G'.Ω 1 → ℂ}
    (h : IsDecBg G' a ν (rho4 d L N BG κ) (fun _ => 1) D' φ α) :
    composeField G G' a φ D'.Ψ =
      composeField G G' a (bgFieldC G' a ν (bgC0 d L N) D') D'.Ψ := by
  obtain ⟨-, e1, -⟩ := i4b_one hS S HB hκ hM hδ0 hδε hε hδ hνε hD h
  rw [e1]

/-- **Theorem I-4b (v): closeness of the decoupled composition (P3 (2.60)).**  The composed fields
at `s` and at `s ≡ 1` differ at `x` by at most
`10 e^{2dγ_w} closeConst · e^{-γ_w d(x, W)}`, where `W` contains the thickened interaction cubes of
the centres with `s_z ≠ 1` and `d` is the scaled distance of `𝔹'_k`. -/
theorem i4b_compose_close {c BG : ℝ} (hS : DecSpecs d L c BG) (S : DGSetting G' a ν)
    (HB : BgHyp d L K ϱ' a ν) (hP : Precedes G G') {κ : ℝ} (hκ : 0 ≤ κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {s : DecParams G'}
    (hs : ∀ P, ‖s P‖ ≤ Real.exp κ) {W : Finset (CTorus d L N₁ m₁ K)}
    (hW : ∀ z ∈ cubeIdx G', sProd G' (extS G' s) z ≠ 1 → intBox z ⊆ W)
    {δ ε : ℝ} (hδ0 : 0 < δ) (hδε : δ ≤ ε) (hε : ε ≤ bgC0 d L N) (hδ : δ ≤ c7 d L N BG κ)
    (hνε : ν * ((L : ℝ) ^ K) ^ 2 * ε ^ 2 ≤ δ ^ 2) {D' : BgData G' N}
    (hD : InDomainC G' ν δ ε D') {φ φ1 : G'.Ω 1 × Fin N → ℂ} {α α1 : G'.Ω 1 → ℂ}
    (h : IsDecBg G' a ν (rho4 d L N BG κ) s D' φ α)
    (h1 : IsDecBg G' a ν (rho4 d L N BG κ) (fun _ => 1) D' φ1 α1)
    (x : CTorus d L N₁ m₁ K) (i : Fin N) :
    ‖composeField G G' a φ D'.Ψ x i - composeField G G' a φ1 D'.Ψ x i‖ ≤
      10 * Real.exp (gammaW d * (2 * d)) *
        closeConst d L N BG κ (lemma53Const d L * δ) * decay (gammaW d) (siteSetDist G' W x) := by
  have hd0 : 0 < d := by have := HB.hd; omega
  have hγ := gammaW_nonneg hd0
  obtain ⟨-, hval, -, -⟩ := i4b_close hS S HB hκ hM hs hW hδ0 hδε hε hδ hνε hD h h1
  have hcc : 0 ≤ closeConst d L N BG κ (lemma53Const d L * δ) := by
    have hB0 : 0 ≤ famConst d L BG κ := by
      have := famConst_ge_one (L := L) hS.fam.2.1 κ hd0; linarith
    have hk := cK2'_nonneg (d := d) (L := L) (N := N) hB0
    have hC := lemma53Const_pos d L
    have hF := Balaban.Background.cF_pos d L
    have := hS.fam.2.1
    unfold closeConst
    positivity
  rw [composeField_sub]
  have := composeField_close hP (a := a) HB.weights hγ (by positivity : 0 ≤ 2 * closeConst d L N BG κ
    (lemma53Const d L * δ)) hval x i
  refine this.trans (le_of_eq ?_)
  ring

/-- **Theorem I-4b (v): locality of the decoupled composition.**  If the decoupled background
fields of `𝔹'_k` at `(s, D')` and `(s', D'₂)` agree on the dependency set `composeDep x` of
(6.2) and the data `Ψ'` agree at `x`, then the composed fields agree at `x`. -/
theorem i4b_compose_local (a : ℕ → ℝ) {φ φ₂ : G'.Ω 1 × Fin N → ℂ}
    {Ψ Ψ₂ : CTorus d L N₁ m₁ K → Fin N → ℂ} {x : CTorus d L N₁ m₁ K}
    (hφ : ∀ y ∈ composeDep G G' x, ∀ j, svec G' φ y j = svec G' φ₂ y j)
    (hΨ : ∀ j, Ψ x j = Ψ₂ x j) (i : Fin N) :
    composeField G G' a φ Ψ x i = composeField G G' a φ₂ Ψ₂ x i :=
  composeField_congr a hφ hΨ i

/-- **Theorem I-4b (v): analyticity of the decoupled composition in `(s, data)`.** -/
theorem i4b_compose_analytic {c BG : ℝ} (hS : DecSpecs d L c BG) (S : DGSetting G' a ν)
    (HB : BgHyp d L K ϱ' a ν) {κ : ℝ} (hκ : 0 ≤ κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) :
    ∃ Ψs : DecParams G' × RawData d L (N₁ * L ^ m₁) K N →
        CTorus d L N₁ m₁ K → Fin N → ℂ,
      (∀ (x : CTorus d L N₁ m₁ K) (i : Fin N), AnalyticOnNhd ℂ (fun q => Ψs q x i)
        {q | (∀ P, ‖q.1 P‖ < Real.exp κ) ∧ ∃ D' : BgData G' N,
          InUnionDomainC G' (bgC0 d L N) (c7 d L N BG κ) ν D' ∧ q.2 = (D'.Ψ, D'.h)}) ∧
      ∀ (s : DecParams G') (D' : BgData G' N), (∀ P, ‖s P‖ < Real.exp κ) →
        InUnionDomainC G' (bgC0 d L N) (c7 d L N BG κ) ν D' →
        ∀ (φ : G'.Ω 1 × Fin N → ℂ) (α : G'.Ω 1 → ℂ),
          IsDecBg G' a ν (rho4 d L N BG κ) s D' φ α →
          Ψs (s, (D'.Ψ, D'.h)) = composeField G G' a φ D'.Ψ := by
  obtain ⟨F, hF, hFp⟩ := i4b_analytic hS S HB hκ hM
  refine ⟨fun q => composeField G G' a (F q).1 q.2.1, fun x i q hq => ?_, ?_⟩
  · have hFq := hF q hq
    refine analyticAt_composeField (G := G) (G' := G') (Q := DecParams G' × RawData d L (N₁ * L ^ m₁) K N)
      a (fun q => (F q).1) (fun q => q.2.1) (fun r => ?_) (fun y j => ?_) x i
    · exact analyticAt_pi_iff.1 (analyticAt_fst.comp hFq) r
    · exact (analyticAt_rawΨ y j q.2).comp_of_eq (f := fun q : DecParams G' × RawData d L (N₁ * L ^ m₁) K N => q.2) analyticAt_snd rfl
  · intro s D' hs hDU φ α hI
    have := hFp s D' hs hDU φ α hI
    funext x i
    show composeField G G' a (F (s, (D'.Ψ, D'.h))).1 D'.Ψ x i = _
    rw [this]

end Decoupled

end Balaban.Localization
