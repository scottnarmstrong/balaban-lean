/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Multiscale.XVariant
public import Balaban.Multiscale.ScaleMismatch
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# G-2(vii)(i): the `L²` Agmon block decay for `G_{k,x}`, uniformly in `x ≥ 0` (GREEN.md §4.2, F-04)

The Agmon argument of `Balaban/Multiscale/Agmon.lean`, `AgmonDecay.lean`, `ScaleMismatch.lean` for the
x-variant operator `H_{k,x}(α₀)` of `Balaban/Multiscale/XVariant.lean`.

* `Balaban.Multiscale.agmon_energy_gen`: the energy inequality of Proposition 4.5 for *any* real
  symmetric `M` satisfying the conjugated lower bound (`hcore`), with a free Poincaré-type constant `c`.
* `Balaban.Multiscale.x_weighted_core`: **the modified commutator estimate.**  For `w = exp (ε r)`,
  `v = w φ`, the conjugation errors of the layer terms `j ≤ k` are those of `weighted_core`; the
  bracket on `Ω_{k+1}` contributes the block errors of `s₁ P_k` and `(s₂ - s₁) P_{k+1}`,
  `-½ B (s₁ ‖v‖²_{Ω_{k+1}} + (s₂ - s₁) ‖v‖²_{Ω_{k+1}}) L⁻²ᵏ = -½ B s₂ L⁻²ᵏ ‖v‖²_{Ω_{k+1}}`,
  `B = (e^{2εd} - 1)²`; since `s₂ ≤ a_k ≤ 2` and `L⁻²ᵏ = L² ℓ_{k+1}⁻²` the total error is
  `(4 d ε² + L² B) ‖ℓ⁻¹ v‖²`, uniform in `x` (the only `x`-dependence is through `0 ≤ s₁ ≤ s₂ ≤ a_k`).
  The price of this coarse (symmetrization) estimate is a rate `ε ≤ c_x/(16 d L)` depending on `L`;
  the interface of GREEN.md F-04 allows `ε₀'(d, L)`.
* `Balaban.Multiscale.green_G2i_x`: for `u = G_{k,x}(α₀) f`, `f` supported in `Δ_{j'}(y')`,
  `ℓ_j ‖χ_{Δ_j(y)} ∂ũ‖ + ‖χ_{Δ_j(y)} ũ‖ ≤ (13 L / c_x) e^{-(ε/2) t} ℓ_{j'}² ‖f‖`
  for `0 ≤ t ≤ d(y, y')`, `1 ≤ j, j' ≤ k + 1`.
-/

@[expose] public section

namespace Balaban.Multiscale

open Finset Matrix Balaban

variable {d L N₀ K : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-! ### The energy inequality for a general real operator -/

theorem agmon_energy_gen (G : GeneratingSet d L N₀ K ϱ)
    {M : Matrix (Torus d (N₀ * L ^ K)) (Torus d (N₀ * L ^ K)) ℝ} {c κ : ℝ} (hc0 : 0 < c)
    (hκ : κ ≤ c / 4) (α : G.Ω 1 → ℂ) (hα : ∀ x, ‖α x‖ ≤ c / (4 * (G.spacing x) ^ 2))
    {r : Torus d (N₀ * L ^ K) → ℝ} {ε : ℝ}
    (hcore : ∀ φ : Torus d (N₀ * L ^ K) → ℝ, (∀ x, x ∉ G.Ω 1 → φ x = 0) →
      (1 / 2) * latticeEnergy (fun x => Real.exp (ε * r x) * φ x) +
          (c - κ) * wsq G (fun x => Real.exp (ε * r x) * φ x) ≤
        (fun x => Real.exp (ε * r x) ^ 2 * φ x) ⬝ᵥ M *ᵥ φ)
    {u f : G.Ω 1 → ℂ}
    (hu : (Green.restrictOp (M.map (algebraMap ℝ ℂ)) (G.Ω 1) + Matrix.diagonal α) *ᵥ u = f) :
    (1 / 2) * cEnergy (agmonField G ε r u) + (c / 4) * cwsq G (agmonField G ε r u) ≤
      (1 / c) * agmonSource G ε r f := by
  set w : Torus d (N₀ * L ^ K) → ℝ := fun x => Real.exp (ε * r x) with hw
  set ut := zeroExt (G.Ω 1) u with hut
  set ft := zeroExt (G.Ω 1) f with hft
  set αt := zeroExt (G.Ω 1) α with hαt
  set p : Torus d (N₀ * L ^ K) → ℝ := fun x => (ut x).re with hp
  set q : Torus d (N₀ * L ^ K) → ℝ := fun x => (ut x).im with hq
  have hpz : ∀ x, x ∉ G.Ω 1 → p x = 0 := fun x hx => by simp [hp, hut, zeroExt_not_mem _ _ hx]
  have hqz : ∀ x, x ∉ G.Ω 1 → q x = 0 := fun x hx => by simp [hq, hut, zeroExt_not_mem _ _ hx]
  have core_p := hcore p hpz
  have core_q := hcore q hqz
  set v := agmonField G ε r u with hv
  have hvre : (fun x => (v x).re) = fun x => w x * p x := by
    funext x; exact Complex.re_ofReal_mul _ _
  have hvim : (fun x => (v x).im) = fun x => w x * q x := by
    funext x; exact Complex.im_ofReal_mul _ _
  have hE : cEnergy v = latticeEnergy (fun x => w x * p x) + latticeEnergy (fun x => w x * q x) := by
    rw [cEnergy_eq, hvre, hvim]
  have hS : cwsq G v = wsq G (fun x => w x * p x) + wsq G (fun x => w x * q x) := by
    rw [cwsq_eq, hvre, hvim]
  set Ap := M *ᵥ p with hAp
  set Aq := M *ᵥ q with hAq
  have hpt : ∀ x : Torus d (N₀ * L ^ K), w x ^ 2 * (star (ut x) * ft x).re =
      w x ^ 2 * p x * Ap x + w x ^ 2 * q x * Aq x + w x ^ 2 * (αt x).re * ‖ut x‖ ^ 2 := by
    intro x
    by_cases hx : x ∈ G.Ω 1
    · have heq := congrFun hu ⟨x, hx⟩
      rw [Matrix.add_mulVec, Pi.add_apply, Matrix.mulVec_diagonal, restrictOp_mulVec] at heq
      have h1 : ft x = (M.map (algebraMap ℝ ℂ) *ᵥ ut) x + αt x * ut x := by
        have e1 : ft x = f ⟨x, hx⟩ := zeroExt_mem (G.Ω 1) f ⟨x, hx⟩
        have e2 : αt x = α ⟨x, hx⟩ := zeroExt_mem (G.Ω 1) α ⟨x, hx⟩
        have e3 : ut x = u ⟨x, hx⟩ := zeroExt_mem (G.Ω 1) u ⟨x, hx⟩
        rw [e1, e2, e3]
        exact heq.symm
      rw [h1, mul_add, Complex.add_re, re_star_mul, re_star_mul_mul, re_mulVec_map, im_mulVec_map]
      simp only [hp, hq, hAp, hAq]
      ring
    · have : ut x = 0 := zeroExt_not_mem _ _ hx
      simp [this, hp, hq]
  set T : ℝ := ∑ x, w x ^ 2 * (star (ut x) * ft x).re with hT
  have hTsum : T = (∑ x, w x ^ 2 * p x * Ap x) + (∑ x, w x ^ 2 * q x * Aq x) +
      ∑ x, w x ^ 2 * (αt x).re * ‖ut x‖ ^ 2 := by
    rw [hT, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ => hpt x
  have hRp : (∑ x, w x ^ 2 * p x * Ap x) =
      (fun x => Real.exp (ε * r x) ^ 2 * p x) ⬝ᵥ M *ᵥ p := rfl
  have hRq : (∑ x, w x ^ 2 * q x * Aq x) =
      (fun x => Real.exp (ε * r x) ^ 2 * q x) ⬝ᵥ M *ᵥ q := rfl
  have hpot : -(c / 4 * cwsq G v) ≤ ∑ x, w x ^ 2 * (αt x).re * ‖ut x‖ ^ 2 := by
    unfold cwsq
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun x _ => ?_
    by_cases hx : x ∈ G.Ω 1
    · have hαx : ‖αt x‖ ≤ c / (4 * (G.spacing x) ^ 2) := by
        have e : αt x = α ⟨x, hx⟩ := zeroExt_mem (G.Ω 1) α ⟨x, hx⟩
        rw [e]
        exact hα ⟨x, hx⟩
      have hre : -(c / (4 * (G.spacing x) ^ 2)) ≤ (αt x).re := by
        have := Complex.abs_re_le_norm (αt x)
        linarith [neg_abs_le (αt x).re]
      have hnv : ‖v x‖ ^ 2 = w x ^ 2 * ‖ut x‖ ^ 2 := by
        rw [hv, norm_agmonField]; ring
      rw [invSqSpacing_eq G hx, hnv]
      have hsp : 0 < (G.spacing x) ^ 2 := by have := spacing_pos G (x := x); positivity
      have e2 : -(c / 4 * ((G.spacing x ^ 2)⁻¹ * (w x ^ 2 * ‖ut x‖ ^ 2))) =
          -(c / (4 * (G.spacing x) ^ 2)) * (w x ^ 2 * ‖ut x‖ ^ 2) := by
        field_simp
      rw [e2]
      calc -(c / (4 * (G.spacing x) ^ 2)) * (w x ^ 2 * ‖ut x‖ ^ 2)
          ≤ (αt x).re * (w x ^ 2 * ‖ut x‖ ^ 2) :=
            mul_le_mul_of_nonneg_right hre (by positivity)
        _ = _ := by ring
    · have h0 : ut x = 0 := zeroExt_not_mem _ _ hx
      have h1 : 0 ≤ c / 4 * (invSqSpacing G x * ‖v x‖ ^ 2) := by
        have := invSqSpacing_nonneg G x
        positivity
      have h2 : w x ^ 2 * (αt x).re * ‖ut x‖ ^ 2 = 0 := by rw [h0]; simp
      linarith
  have hsrc : T ≤ c / 4 * cwsq G v + (1 / c) * agmonSource G ε r f := by
    unfold cwsq agmonSource
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun x _ => ?_
    by_cases hx : x ∈ G.Ω 1
    · have hsp : 0 < G.spacing x := spacing_pos G
      have hnv : ‖v x‖ = w x * ‖ut x‖ := by rw [hv, norm_agmonField]
      have hnh : ‖((Real.exp (ε * r x) : ℝ) : ℂ) * ft x‖ = w x * ‖ft x‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
      have hre : (star (ut x) * ft x).re ≤ ‖ut x‖ * ‖ft x‖ := by
        calc _ ≤ ‖star (ut x) * ft x‖ := Complex.re_le_norm _
          _ = _ := by rw [norm_mul, norm_star]
      have h1 : w x ^ 2 * (star (ut x) * ft x).re ≤ ‖v x‖ * (w x * ‖ft x‖) := by
        rw [hnv]
        have := mul_le_mul_of_nonneg_left hre (sq_nonneg (w x))
        nlinarith [this]
      rw [invSqSpacing_eq G hx, hnh]
      set A := ‖v x‖
      set B := w x * ‖ft x‖
      set s := G.spacing x
      have hs2 : 0 < s ^ 2 := by positivity
      have key : A * B ≤ c / 4 * ((s ^ 2)⁻¹ * A ^ 2) + 1 / c * (s ^ 2 * B ^ 2) := by
        have h0 : 0 ≤ 1 / c * (s * B - c / 2 * (A / s)) ^ 2 := by positivity
        have e : c / 4 * ((s ^ 2)⁻¹ * A ^ 2) + 1 / c * (s ^ 2 * B ^ 2) - A * B =
            1 / c * (s * B - c / 2 * (A / s)) ^ 2 := by
          field_simp; ring
        linarith
      linarith
    · have : ut x = 0 := zeroExt_not_mem _ _ hx
      have h0 : 0 ≤ c / 4 * (invSqSpacing G x * ‖v x‖ ^ 2) := by
        have := invSqSpacing_nonneg G x
        positivity
      have h1 : 0 ≤ 1 / c * (G.spacing x ^ 2 * ‖((Real.exp (ε * r x) : ℝ) : ℂ) *
          zeroExt (G.Ω 1) f x‖ ^ 2) := by positivity
      simp only [this, star_zero, zero_mul, Complex.zero_re, mul_zero]
      linarith
  have hcomb : (1 / 2) * cEnergy v + (c - κ) * cwsq G v ≤
      (∑ x, w x ^ 2 * p x * Ap x) + (∑ x, w x ^ 2 * q x * Aq x) := by
    rw [hE, hS, hRp, hRq]
    nlinarith [core_p, core_q]
  have hS0 := cwsq_nonneg G v
  have hE0 := cEnergy_nonneg v
  nlinarith [hcomb, hTsum, hpot, hsrc, hκ, mul_nonneg hS0 (sub_nonneg.2 hκ)]

/-! ### The conjugation error of one block term -/

theorem layer_conj_ge (G : GeneratingSet d L N₀ K ϱ) {j m : ℕ} (hmK : m ≤ K)
    {r : Torus d (N₀ * L ^ K) → ℝ} {ε B : ℝ} (hB0 : 0 ≤ B)
    (hosc : ∀ x x', x ∈ G.layer j →
      blockMap (L ^ m) (N₀ * L ^ (K - m)) x' = blockMap (L ^ m) (N₀ * L ^ (K - m)) x →
      (Real.exp (ε * r x) - Real.exp (ε * r x')) ^ 2 ≤ B * Real.exp (ε * r x) ^ 2)
    (φ : Torus d (N₀ * L ^ K) → ℝ) :
    -(1 / 2 * B * ∑ x, (Real.exp (ε * r x) * layerPart G j φ x) ^ 2) ≤
      layerPart G j (fun x => Real.exp (ε * r x) ^ 2 * φ x) ⬝ᵥ
          blockProjMatrix d (N₀ * L ^ K) (L ^ m) (N₀ * L ^ (K - m)) *ᵥ layerPart G j φ -
        layerPart G j (fun x => Real.exp (ε * r x) * φ x) ⬝ᵥ
          blockProjMatrix d (N₀ * L ^ K) (L ^ m) (N₀ * L ^ (K - m)) *ᵥ
            layerPart G j (fun x => Real.exp (ε * r x) * φ x) := by
  set w : Torus d (N₀ * L ^ K) → ℝ := fun x => Real.exp (ε * r x) with hw
  have hlg : layerPart G j (fun x => w x ^ 2 * φ x) = fun x => w x ^ 2 * layerPart G j φ x := by
    funext x; by_cases h : x ∈ G.layer j <;> simp [layerPart, h]
  have hlv : layerPart G j (fun x => w x * φ x) = fun x => w x * layerPart G j φ x := by
    funext x; by_cases h : x ∈ G.layer j <;> simp [layerPart, h]
  rw [hlg, hlv]
  exact block_diff_ge (blockProjMatrix d (N₀ * L ^ K) (L ^ m) (N₀ * L ^ (K - m)))
    (blockProjMatrix_symm m) (blockProjMatrix_nonneg m) (blockProjMatrix_row hmK) w
    (layerPart G j φ) hB0 (by
      intro x x' hM hψ _
      have hbm : blockMap (L ^ m) (N₀ * L ^ (K - m)) x = blockMap (L ^ m) (N₀ * L ^ (K - m)) x' := by
        by_contra hne
        exact hM (by simp [blockProjMatrix, hne])
      have hx : x ∈ G.layer j := by
        by_contra hne; exact hψ (by simp [layerPart, hne])
      exact hosc x x' hx hbm.symm)

theorem combine_aux {DL Lw R1 D1 D2 T1 T2 R2 : ℝ} (hsum : -Lw ≤ DL) (hb1 : Lw ≤ R1)
    (e1 : -T1 ≤ D1) (e2 : -T2 ≤ D2) (hb2 : T1 + T2 ≤ R2) : -(R1 + R2) ≤ DL + D1 + D2 := by
  linarith

/-! ### The x-variant: bilinear form and conjugation error -/

section XErr

variable {k : ℕ}
variable (G : GeneratingSet d L N₀ (k + 1) ϱ)

theorem xAvgMatrix_bilinear (a : ℕ → ℝ) (s₁ s₂ : ℝ) (g φ : Torus d (N₀ * L ^ (k + 1)) → ℝ) :
    g ⬝ᵥ xAvgMatrix G a s₁ s₂ *ᵥ φ =
      ∑ j ∈ Icc 1 k, (a j / ((L : ℝ) ^ j) ^ 2) *
        (layerPart G j g ⬝ᵥ blockProjMatrix d (N₀ * L ^ (k + 1)) (L ^ j) (N₀ * L ^ (k + 1 - j)) *ᵥ
          layerPart G j φ) +
      (s₁ / ((L : ℝ) ^ k) ^ 2) *
        (layerPart G (k + 1) g ⬝ᵥ
          blockProjMatrix d (N₀ * L ^ (k + 1)) (L ^ k) (N₀ * L ^ (k + 1 - k)) *ᵥ
            layerPart G (k + 1) φ) +
      ((s₂ - s₁) / ((L : ℝ) ^ k) ^ 2) *
        (layerPart G (k + 1) g ⬝ᵥ
          blockProjMatrix d (N₀ * L ^ (k + 1)) (L ^ (k + 1)) (N₀ * L ^ (k + 1 - (k + 1))) *ᵥ
            layerPart G (k + 1) φ) := by
  unfold xAvgMatrix
  rw [Matrix.add_mulVec, Matrix.add_mulVec, dotProduct_add, dotProduct_add, Matrix.sum_mulVec,
    dotProduct_sum]
  congr 1
  · congr 1
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, layerBlockMatrix_bilinear]
    · rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, layerBlockMatrix_bilinear]
  · rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, layerBlockMatrix_bilinear]

theorem xS2_le {ak b x : ℝ} (hak : 0 < ak) (hb : 0 ≤ b) (hx : 0 ≤ x) : xS2 ak b x ≤ ak := by
  unfold xS2
  rw [div_le_iff₀ (by linarith)]
  nlinarith

theorem xS2_nonneg {ak b x : ℝ} (hak : 0 < ak) (hb : 0 ≤ b) (hx : 0 ≤ x) : 0 ≤ xS2 ak b x := by
  unfold xS2; positivity

/-- Core of `xAvg_diff_ge` with `1 ≤ k` replaced by the lower bound `1/2 ≤ a_k` (the only use of `k ≥ 1`); the weights `a_j`, `1 ≤ j ≤ k`, stay in `[1/2, 2]`. -/
theorem xAvg_diff_ge_of_ak {a : ℕ → ℝ} (ha : IsAdmissibleWeights k a)
    (hak : 1 / 2 ≤ a k ∧ a k ≤ 2) {aT x : ℝ}
    (haT1 : 1 / 2 ≤ aT) (hx : 0 ≤ x) (hL : 3 ≤ L)
    {r : Torus d (N₀ * L ^ (k + 1)) → ℝ} (hr : IsAgmonWeight G r) {ε : ℝ} (hε0 : 0 ≤ ε)
    (φ : Torus d (N₀ * L ^ (k + 1)) → ℝ) :
    -((L : ℝ) ^ 2 * (Real.exp (ε * (2 * d)) - 1) ^ 2 *
        wsq G (fun y => Real.exp (ε * r y) * φ y)) ≤
      (fun y => Real.exp (ε * r y) ^ 2 * φ y) ⬝ᵥ
          xAvgMatrix G a (xS1 (a k) x) (xS2 (a k) (aT / (L : ℝ) ^ 2) x) *ᵥ φ -
        (fun y => Real.exp (ε * r y) * φ y) ⬝ᵥ
          xAvgMatrix G a (xS1 (a k) x) (xS2 (a k) (aT / (L : ℝ) ^ 2) x) *ᵥ
            (fun y => Real.exp (ε * r y) * φ y) := by
  have hLr : (3 : ℝ) ≤ L := by exact_mod_cast hL
  have hL0 : (0 : ℝ) < L := by linarith
  have hL1 : (1 : ℝ) ≤ (L : ℝ) ^ 2 := by nlinarith
  have hak0 : 0 < a k := by linarith [hak.1]
  have hb0 : 0 ≤ aT / (L : ℝ) ^ 2 := by positivity
  set s₁ := xS1 (a k) x with hs₁d
  set s₂ := xS2 (a k) (aT / (L : ℝ) ^ 2) x with hs₂d
  have hs₁ : 0 ≤ s₁ := xS1_nonneg hak0 hx
  have hs : 0 ≤ s₂ - s₁ := xS12_sub_nonneg hak0 hb0 hx
  have hs₂ : s₂ ≤ 2 := (xS2_le hak0 hb0 hx).trans hak.2
  set B := (Real.exp (ε * (2 * d)) - 1) ^ 2 with hB
  have hB0 : 0 ≤ B := sq_nonneg _
  set w : Torus d (N₀ * L ^ (k + 1)) → ℝ := fun y => Real.exp (ε * r y) with hw
  rw [xAvgMatrix_bilinear, xAvgMatrix_bilinear, ← sub_add_sub_comm, ← sub_add_sub_comm,
    ← Finset.sum_sub_distrib]
  -- the layers `j ≤ k`
  have hlow : ∀ j ∈ Icc 1 k, -((1 / 2 * B) * (a j / ((L : ℝ) ^ j) ^ 2) *
      ∑ y, (w y * layerPart G j φ y) ^ 2) ≤
      (a j / ((L : ℝ) ^ j) ^ 2) *
        (layerPart G j (fun y => w y ^ 2 * φ y) ⬝ᵥ
            blockProjMatrix d (N₀ * L ^ (k + 1)) (L ^ j) (N₀ * L ^ (k + 1 - j)) *ᵥ
              layerPart G j φ) -
        (a j / ((L : ℝ) ^ j) ^ 2) *
          (layerPart G j (fun y => w y * φ y) ⬝ᵥ
            blockProjMatrix d (N₀ * L ^ (k + 1)) (L ^ j) (N₀ * L ^ (k + 1 - j)) *ᵥ
              layerPart G j (fun y => w y * φ y)) := by
    intro j hj
    have hj1 := (Finset.mem_Icc.1 hj).1
    have hjk := (Finset.mem_Icc.1 hj).2
    have hLj : (0 : ℝ) < ((L : ℝ) ^ j) ^ 2 := by positivity
    have hcoef : 0 ≤ a j / ((L : ℝ) ^ j) ^ 2 := div_nonneg (by linarith [(ha j hj1 hjk).1]) hLj.le
    have h := layer_conj_ge G (j := j) (m := j) (by omega) hB0 (r := r) (ε := ε) (φ := φ)
      (fun x x' hx hbm => exp_sq_sub_le hε0 (hr.block j hj1 (by omega) x x' hx hbm))
    rw [← mul_sub]
    calc _ = (a j / ((L : ℝ) ^ j) ^ 2) * (-(1 / 2 * B * ∑ y, (w y * layerPart G j φ y) ^ 2)) := by
          ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h hcoef
  -- the top layer
  have hLk : (0 : ℝ) < ((L : ℝ) ^ k) ^ 2 := by positivity
  have htop1 := layer_conj_ge G (j := k + 1) (m := k) (by omega) hB0 (r := r) (ε := ε) (φ := φ)
    (fun x x' hx hbm => exp_sq_sub_le hε0 (hr.block (k + 1) (by omega) le_rfl x x' hx
      (by
        have := GeneratingSet.jBlock_succ_eq (d := d) (L := L) (N₀ := N₀) (k := k + 1) (j := k)
          (by omega) hbm.symm
        exact this.symm)))
  have htop2 := layer_conj_ge G (j := k + 1) (m := k + 1) (by omega) hB0 (r := r) (ε := ε)
    (φ := φ) (fun x x' hx hbm => exp_sq_sub_le hε0 (hr.block (k + 1) (by omega) le_rfl x x' hx hbm))
  set St := ∑ y, (w y * layerPart G (k + 1) φ y) ^ 2 with hSt
  have hSt0 : 0 ≤ St := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have e1 : (s₁ / ((L : ℝ) ^ k) ^ 2) * (layerPart G (k + 1) (fun y => w y ^ 2 * φ y) ⬝ᵥ
        blockProjMatrix d (N₀ * L ^ (k + 1)) (L ^ k) (N₀ * L ^ (k + 1 - k)) *ᵥ
          layerPart G (k + 1) φ) -
      (s₁ / ((L : ℝ) ^ k) ^ 2) * (layerPart G (k + 1) (fun y => w y * φ y) ⬝ᵥ
        blockProjMatrix d (N₀ * L ^ (k + 1)) (L ^ k) (N₀ * L ^ (k + 1 - k)) *ᵥ
          layerPart G (k + 1) (fun y => w y * φ y)) ≥
      -((1 / 2 * B) * (s₁ / ((L : ℝ) ^ k) ^ 2) * St) := by
    rw [← mul_sub]
    calc _ = (s₁ / ((L : ℝ) ^ k) ^ 2) * (-(1 / 2 * B * St)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left htop1 (div_nonneg hs₁ hLk.le)
  have e2 : ((s₂ - s₁) / ((L : ℝ) ^ k) ^ 2) * (layerPart G (k + 1) (fun y => w y ^ 2 * φ y) ⬝ᵥ
        blockProjMatrix d (N₀ * L ^ (k + 1)) (L ^ (k + 1)) (N₀ * L ^ (k + 1 - (k + 1))) *ᵥ
          layerPart G (k + 1) φ) -
      ((s₂ - s₁) / ((L : ℝ) ^ k) ^ 2) * (layerPart G (k + 1) (fun y => w y * φ y) ⬝ᵥ
        blockProjMatrix d (N₀ * L ^ (k + 1)) (L ^ (k + 1)) (N₀ * L ^ (k + 1 - (k + 1))) *ᵥ
          layerPart G (k + 1) (fun y => w y * φ y)) ≥
      -((1 / 2 * B) * ((s₂ - s₁) / ((L : ℝ) ^ k) ^ 2) * St) := by
    rw [← mul_sub]
    calc _ = ((s₂ - s₁) / ((L : ℝ) ^ k) ^ 2) * (-(1 / 2 * B * St)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left htop2 (div_nonneg hs hLk.le)
  -- assemble
  have hsum := Finset.sum_le_sum hlow
  rw [Finset.sum_neg_distrib] at hsum
  have hwsq : wsq G (fun y => w y * φ y) =
      ∑ j ∈ Icc 1 k, (((L : ℝ) ^ j) ^ 2)⁻¹ * ∑ y, (w y * layerPart G j φ y) ^ 2 +
        (((L : ℝ) ^ (k + 1)) ^ 2)⁻¹ * St := by
    rw [wsq_eq_sum_layers, Finset.sum_Icc_succ_top (by omega)]
    congr 1
    · refine Finset.sum_congr rfl fun j _ => ?_
      congr 1
      refine Finset.sum_congr rfl fun y _ => ?_
      by_cases h : y ∈ G.layer j <;> simp [layerPart, h, hw]
    · congr 1
      refine Finset.sum_congr rfl fun y _ => ?_
      by_cases h : y ∈ G.layer (k + 1) <;> simp [layerPart, h, hw]
  have hbnd1 : ∑ j ∈ Icc 1 k, (1 / 2 * B) * (a j / ((L : ℝ) ^ j) ^ 2) *
        ∑ y, (w y * layerPart G j φ y) ^ 2 ≤
      (L : ℝ) ^ 2 * B * ∑ j ∈ Icc 1 k, (((L : ℝ) ^ j) ^ 2)⁻¹ *
        ∑ y, (w y * layerPart G j φ y) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j hj => ?_
    have hj1 := (Finset.mem_Icc.1 hj).1
    have hjk := (Finset.mem_Icc.1 hj).2
    have haj := ha j hj1 hjk
    have hLj : (0 : ℝ) < ((L : ℝ) ^ j) ^ 2 := by positivity
    have hS : 0 ≤ ∑ y, (w y * layerPart G j φ y) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hcoef : (1 / 2 * B) * (a j / ((L : ℝ) ^ j) ^ 2) ≤
        (L : ℝ) ^ 2 * B * (((L : ℝ) ^ j) ^ 2)⁻¹ := by
      have hdiv : a j / ((L : ℝ) ^ j) ^ 2 = a j * (((L : ℝ) ^ j) ^ 2)⁻¹ := div_eq_mul_inv _ _
      rw [hdiv]
      have hi : 0 ≤ (((L : ℝ) ^ j) ^ 2)⁻¹ := by positivity
      have h2 : 1 / 2 * B * (a j * (((L : ℝ) ^ j) ^ 2)⁻¹) ≤ B * (((L : ℝ) ^ j) ^ 2)⁻¹ := by
        nlinarith [mul_nonneg hB0 hi, haj.2]
      have h3 : B * (((L : ℝ) ^ j) ^ 2)⁻¹ ≤ (L : ℝ) ^ 2 * B * (((L : ℝ) ^ j) ^ 2)⁻¹ := by
        nlinarith [mul_nonneg hB0 hi]
      linarith
    calc _ ≤ ((L : ℝ) ^ 2 * B * (((L : ℝ) ^ j) ^ 2)⁻¹) * ∑ y, (w y * layerPart G j φ y) ^ 2 :=
          mul_le_mul_of_nonneg_right hcoef hS
      _ = _ := by ring
  have hbnd2 : (1 / 2 * B) * (s₁ / ((L : ℝ) ^ k) ^ 2) * St +
      (1 / 2 * B) * ((s₂ - s₁) / ((L : ℝ) ^ k) ^ 2) * St ≤
      (L : ℝ) ^ 2 * B * ((((L : ℝ) ^ (k + 1)) ^ 2)⁻¹ * St) := by
    have e : (1 / 2 * B) * (s₁ / ((L : ℝ) ^ k) ^ 2) * St +
        (1 / 2 * B) * ((s₂ - s₁) / ((L : ℝ) ^ k) ^ 2) * St =
        (1 / 2 * B) * (s₂ / ((L : ℝ) ^ k) ^ 2) * St := by ring
    rw [e]
    have e3 : (L : ℝ) ^ 2 * B * ((((L : ℝ) ^ (k + 1)) ^ 2)⁻¹ * St) =
        B * ((((L : ℝ) ^ k) ^ 2)⁻¹ * St) := by
      rw [show ((L : ℝ) ^ (k + 1)) ^ 2 = ((L : ℝ) ^ k) ^ 2 * (L : ℝ) ^ 2 by ring]
      field_simp
    rw [e3]
    have : (1 / 2 * B) * (s₂ / ((L : ℝ) ^ k) ^ 2) * St =
        (1 / 2 * B * s₂) * ((((L : ℝ) ^ k) ^ 2)⁻¹ * St) := by
      rw [div_eq_mul_inv]; ring
    rw [this]
    have hi : 0 ≤ (((L : ℝ) ^ k) ^ 2)⁻¹ * St := by positivity
    refine mul_le_mul_of_nonneg_right ?_ hi
    have h2 : 0 ≤ B * (2 - s₂) := mul_nonneg hB0 (by linarith)
    linarith
  rw [hwsq, mul_add]
  exact combine_aux hsum hbnd1 e1 e2 hbnd2

/-- **The conjugation error of the x-variant averaging form.**  With `B = (e^{2εd} - 1)²`,
`(w²φ)ᵀ A φ - (wφ)ᵀ A (wφ) ≥ - L² B ‖ℓ⁻¹ (wφ)‖²`, uniformly in `x ≥ 0`. -/
theorem xAvg_diff_ge (hk : 1 ≤ k) {a : ℕ → ℝ} (ha : IsAdmissibleWeights k a) {aT x : ℝ}
    (haT1 : 1 / 2 ≤ aT) (hx : 0 ≤ x) (hL : 3 ≤ L)
    {r : Torus d (N₀ * L ^ (k + 1)) → ℝ} (hr : IsAgmonWeight G r) {ε : ℝ} (hε0 : 0 ≤ ε)
    (φ : Torus d (N₀ * L ^ (k + 1)) → ℝ) :
    -((L : ℝ) ^ 2 * (Real.exp (ε * (2 * d)) - 1) ^ 2 *
        wsq G (fun y => Real.exp (ε * r y) * φ y)) ≤
      (fun y => Real.exp (ε * r y) ^ 2 * φ y) ⬝ᵥ
          xAvgMatrix G a (xS1 (a k) x) (xS2 (a k) (aT / (L : ℝ) ^ 2) x) *ᵥ φ -
        (fun y => Real.exp (ε * r y) * φ y) ⬝ᵥ
          xAvgMatrix G a (xS1 (a k) x) (xS2 (a k) (aT / (L : ℝ) ^ 2) x) *ᵥ
            (fun y => Real.exp (ε * r y) * φ y) :=
  xAvg_diff_ge_of_ak G ha (ha k hk le_rfl) haT1 hx hL hr hε0 φ

end XErr

section XEnergy

variable {k : ℕ}
variable (G : GeneratingSet d L N₀ (k + 1) ϱ)

/-- The Agmon rate of the x-variant, `ε₀' = c_x/(16 d L)`. -/
noncomputable def xAgmonRate (d L : ℕ) : ℝ := xPoincareConst d / (16 * d * L)

omit [NeZero L] in
theorem xAgmonRate_pos (hd : 0 < d) (hL : 3 ≤ L) : 0 < xAgmonRate d L := by
  have : (0 : ℝ) < d := by exact_mod_cast hd
  have : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have := xPoincareConst_pos hd
  unfold xAgmonRate; positivity

omit [NeZero L] in
/-- The total conjugation error of the x-variant is at most a quarter of `c_x`. -/
theorem kappa_x_le (hd : 0 < d) (hL : 3 ≤ L) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ xAgmonRate d L) :
    4 * d * ε ^ 2 + (L : ℝ) ^ 2 * (Real.exp (ε * (2 * d)) - 1) ^ 2 ≤ xPoincareConst d / 4 := by
  have hdd : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hLr : (3 : ℝ) ≤ L := by exact_mod_cast hL
  have hc0 := xPoincareConst_pos hd
  have hc4 := xPoincareConst_le_quarter d
  set c := xPoincareConst d with hcdef
  have hεdL : ε * d * L ≤ c / 16 := by
    have : ε * (d * L) ≤ xAgmonRate d L * (d * L) := by gcongr
    have e : xAgmonRate d L * (d * L) = c / 16 := by
      unfold xAgmonRate; field_simp; rfl
    nlinarith
  have hεd : ε * d ≤ c / 16 := by nlinarith [mul_nonneg hε0 (by linarith : (0 : ℝ) ≤ d)]
  have hε : ε ≤ c / 16 := by nlinarith [mul_nonneg hε0 (by linarith : (0 : ℝ) ≤ d)]
  have hs : ε * (2 * d) ≤ 1 / 2 := by nlinarith
  have h1 : Real.exp (ε * (2 * d)) - 1 ≤ 2 * (ε * (2 * d)) :=
    exp_sub_one_le_two_mul (by positivity) hs
  have h0 : 0 ≤ Real.exp (ε * (2 * d)) - 1 := by
    have := Real.add_one_le_exp (ε * (2 * d)); have : 0 ≤ ε * (2 * d) := by positivity
    linarith
  have h2 : (Real.exp (ε * (2 * d)) - 1) ^ 2 ≤ (4 * (ε * d)) ^ 2 := by
    have : Real.exp (ε * (2 * d)) - 1 ≤ 4 * (ε * d) := by linarith
    exact pow_le_pow_left₀ h0 this 2
  have hεdL0 : 0 ≤ ε * d * L := by positivity
  have h3 : (L : ℝ) ^ 2 * (Real.exp (ε * (2 * d)) - 1) ^ 2 ≤ 16 * (ε * d * L) ^ 2 := by
    calc (L : ℝ) ^ 2 * (Real.exp (ε * (2 * d)) - 1) ^ 2 ≤ (L : ℝ) ^ 2 * (4 * (ε * d)) ^ 2 :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = 16 * (ε * d * L) ^ 2 := by ring
  have h4 : (ε * d * L) ^ 2 ≤ (c / 16) ^ 2 := pow_le_pow_left₀ hεdL0 hεdL 2
  have h5 : 4 * (d : ℝ) * ε ^ 2 ≤ 4 * (ε * d) * ε := by nlinarith [mul_nonneg hε0 hε0]
  have h6 : 4 * (ε * d) * ε ≤ 4 * (c / 16) * (c / 16) := by
    have := mul_le_mul hεd hε hε0 (by positivity)
    nlinarith
  nlinarith

/-- Core of `x_weighted_core` with `1 ≤ k` replaced by the lower bound `1/2 ≤ a_k` (the only use of `k ≥ 1`); the weights `a_j`, `1 ≤ j ≤ k`, stay in `[1/2, 2]`. -/
theorem x_weighted_core_of_ak (hd : 0 < d) (hL : 3 ≤ L) {a : ℕ → ℝ} {ν : ℝ} (hν : 0 ≤ ν)
    (ha : IsAdmissibleWeights k a)
    (hak : 1 / 2 ≤ a k ∧ a k ≤ 2) {aT x : ℝ} (haT1 : 1 / 2 ≤ aT) (haT2 : aT ≤ 2) (hx : 0 ≤ x)
    {r : Torus d (N₀ * L ^ (k + 1)) → ℝ} (hr : IsAgmonWeight G r) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ 1 / 2) {φ : Torus d (N₀ * L ^ (k + 1)) → ℝ} (hφ : ∀ y, y ∉ G.Ω 1 → φ y = 0) :
    (1 / 2) * latticeEnergy (fun y => Real.exp (ε * r y) * φ y) +
        (xPoincareConst d - (4 * d * ε ^ 2 + (L : ℝ) ^ 2 * (Real.exp (ε * (2 * d)) - 1) ^ 2)) *
          wsq G (fun y => Real.exp (ε * r y) * φ y) ≤
      (fun y => Real.exp (ε * r y) ^ 2 * φ y) ⬝ᵥ
        xFullMatrix G a (xS1 (a k) x) (xS2 (a k) (aT / (L : ℝ) ^ 2) x) ν *ᵥ φ := by
  set v : Torus d (N₀ * L ^ (k + 1)) → ℝ := fun y => Real.exp (ε * r y) * φ y with hv
  have hcore := xCore_real_of_ak G hd hL hν ha hak haT1 haT2 hx v
  have hlap := lap_diff r ε ν φ
  have hlapE := lap_error_le G hr hε0 hε1 hφ
  have havg := xAvg_diff_ge_of_ak G ha hak haT1 hx hL hr hε0 φ
  have hwsq : ∑ y, invSqSpacing G y * v y ^ 2 = wsq G v := rfl
  rw [hwsq] at hcore
  have hsplit : ∀ ψ : Torus d (N₀ * L ^ (k + 1)) → ℝ, ∀ g : Torus d (N₀ * L ^ (k + 1)) → ℝ,
      g ⬝ᵥ xFullMatrix G a (xS1 (a k) x) (xS2 (a k) (aT / (L : ℝ) ^ 2) x) ν *ᵥ ψ =
        g ⬝ᵥ latticeLaplacian d (N₀ * L ^ (k + 1)) ν *ᵥ ψ +
          g ⬝ᵥ xAvgMatrix G a (xS1 (a k) x) (xS2 (a k) (aT / (L : ℝ) ^ 2) x) *ᵥ ψ := by
    intro ψ g
    unfold xFullMatrix
    rw [Matrix.add_mulVec, dotProduct_add]
  rw [hsplit] at hcore ⊢
  rw [hlap]
  nlinarith [hcore, hlapE, havg]

/-- **The modified commutator estimate for `G_{k,x}`** (GREEN.md §4.2, F-04): for `w = exp (ε r)`,
`v = w φ`, uniformly in `x ≥ 0`,
`½ ‖∂v‖² + (c_x - 4 d ε² - L² (e^{2εd} - 1)²) ‖ℓ⁻¹ v‖² ≤ ∑ w² φ (A_x φ)`,
`A_x = -Δ + ν + Q* a Q|_x`. -/
theorem x_weighted_core (hd : 0 < d) (hL : 3 ≤ L) (hk : 1 ≤ k) {a : ℕ → ℝ} {ν : ℝ} (hν : 0 ≤ ν)
    (ha : IsAdmissibleWeights k a) {aT x : ℝ} (haT1 : 1 / 2 ≤ aT) (haT2 : aT ≤ 2) (hx : 0 ≤ x)
    {r : Torus d (N₀ * L ^ (k + 1)) → ℝ} (hr : IsAgmonWeight G r) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ 1 / 2) {φ : Torus d (N₀ * L ^ (k + 1)) → ℝ} (hφ : ∀ y, y ∉ G.Ω 1 → φ y = 0) :
    (1 / 2) * latticeEnergy (fun y => Real.exp (ε * r y) * φ y) +
        (xPoincareConst d - (4 * d * ε ^ 2 + (L : ℝ) ^ 2 * (Real.exp (ε * (2 * d)) - 1) ^ 2)) *
          wsq G (fun y => Real.exp (ε * r y) * φ y) ≤
      (fun y => Real.exp (ε * r y) ^ 2 * φ y) ⬝ᵥ
        xFullMatrix G a (xS1 (a k) x) (xS2 (a k) (aT / (L : ℝ) ^ 2) x) ν *ᵥ φ :=
  x_weighted_core_of_ak G hd hL hν ha (ha k hk le_rfl) haT1 haT2 hx hr hε0 hε1 hφ

/-- Core of `x_agmon_energy` with `1 ≤ k` replaced by the lower bound `1/2 ≤ a_k` (the only use of `k ≥ 1`); the weights `a_j`, `1 ≤ j ≤ k`, stay in `[1/2, 2]`. -/
theorem x_agmon_energy_of_ak (hd : 0 < d) (hL : 3 ≤ L) {a : ℕ → ℝ} {ν : ℝ} (hν : 0 ≤ ν)
    (ha : IsAdmissibleWeights k a)
    (hak : 1 / 2 ≤ a k ∧ a k ≤ 2) {aT x : ℝ} (haT1 : 1 / 2 ≤ aT) (haT2 : aT ≤ 2) (hx : 0 ≤ x)
    (α : G.Ω 1 → ℂ) (hα : ∀ y, ‖α y‖ ≤ xCoerciveConst d / (2 * (G.spacing y) ^ 2))
    {r : Torus d (N₀ * L ^ (k + 1)) → ℝ} (hr : IsAgmonWeight G r) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ xAgmonRate d L) {u f : G.Ω 1 → ℂ}
    (hu : xDirichletOperator G a aT x ν α *ᵥ u = f) :
    (1 / 2) * cEnergy (agmonField G ε r u) +
        (xPoincareConst d / 4) * cwsq G (agmonField G ε r u) ≤
      (1 / xPoincareConst d) * agmonSource G ε r f := by
  have hc0 := xPoincareConst_pos hd
  have hεhalf : ε ≤ 1 / 2 := by
    have hLr : (3 : ℝ) ≤ L := by exact_mod_cast hL
    have hdd : (1 : ℝ) ≤ d := by exact_mod_cast hd
    have h1 : xAgmonRate d L ≤ xPoincareConst d / 16 := by
      unfold xAgmonRate
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [mul_le_mul hdd hLr (by norm_num) (by linarith)]
    linarith [xPoincareConst_le_quarter d]
  refine agmon_energy_gen G hc0 (kappa_x_le hd hL hε0 hε1) α ?_ ?_ hu
  · intro y
    have := hα y
    have e : xCoerciveConst d / (2 * (G.spacing y) ^ 2) = xPoincareConst d / (4 * (G.spacing y) ^ 2) := by
      unfold xCoerciveConst; ring
    rwa [e] at this
  · intro φ hφ
    exact x_weighted_core_of_ak G hd hL hν ha hak haT1 haT2 hx hr hε0 hεhalf hφ

/-- **The Agmon energy inequality for `G_{k,x}`**, uniformly in `x ≥ 0`:
for `0 ≤ ε ≤ ε₀' = c_x/(16 d L)`, `H_{k,x}(α₀) u = f`, `v = w ũ`,
`½ ‖∂v‖² + (c_x/4) ‖ℓ⁻¹ v‖² ≤ c_x⁻¹ ‖ℓ w f‖²`. -/
theorem x_agmon_energy (hd : 0 < d) (hL : 3 ≤ L) (hk : 1 ≤ k) {a : ℕ → ℝ} {ν : ℝ} (hν : 0 ≤ ν)
    (ha : IsAdmissibleWeights k a) {aT x : ℝ} (haT1 : 1 / 2 ≤ aT) (haT2 : aT ≤ 2) (hx : 0 ≤ x)
    (α : G.Ω 1 → ℂ) (hα : ∀ y, ‖α y‖ ≤ xCoerciveConst d / (2 * (G.spacing y) ^ 2))
    {r : Torus d (N₀ * L ^ (k + 1)) → ℝ} (hr : IsAgmonWeight G r) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ xAgmonRate d L) {u f : G.Ω 1 → ℂ}
    (hu : xDirichletOperator G a aT x ν α *ᵥ u = f) :
    (1 / 2) * cEnergy (agmonField G ε r u) +
        (xPoincareConst d / 4) * cwsq G (agmonField G ε r u) ≤
      (1 / xPoincareConst d) * agmonSource G ε r f :=
  x_agmon_energy_of_ak G hd hL hν ha (ha k hk le_rfl) haT1 haT2 hx α hα hr hε0 hε1 hu

end XEnergy

/-! ### Block decay for a general constant `c` -/

section Decay

variable {K : ℕ}

theorem eps_sq_mul_le_gen (hd : 0 < d) {c ε : ℝ} (hc0 : 0 < c) (hε0 : 0 ≤ ε)
    (hεd : ε * d ≤ c / 16) : ε ^ 2 * d ≤ c ^ 2 / 256 := by
  have hdd : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hε : ε ≤ c / 16 := by nlinarith [mul_nonneg hε0 (by linarith : (0 : ℝ) ≤ d)]
  nlinarith [mul_le_mul hεd hε hε0 (by positivity)]

theorem numeric_grad_gen (hd : 0 < d) {c ε : ℝ} (hc0 : 0 < c) (hc2 : c ≤ 1 / 2) (hε0 : 0 ≤ ε)
    (hεd : ε * d ≤ c / 16) {E S Hh : ℝ} (hHh0 : 0 ≤ Hh) (hS : S ≤ 4 / c ^ 2 * Hh)
    (hE : E ≤ 2 / c * Hh) : 2 * E + 8 * ε ^ 2 * (d * S) ≤ 5 / c * Hh := by
  have hε2 := eps_sq_mul_le_gen hd hc0 hε0 hεd
  have h3 : 8 * ε ^ 2 * (d * S) ≤ 1 / 8 * Hh := by
    have hcc : 0 ≤ 8 * ε ^ 2 * d :=
      mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg ε)) (Nat.cast_nonneg d)
    calc 8 * ε ^ 2 * (d * S) = (8 * ε ^ 2 * d) * S := by ring
      _ ≤ (8 * ε ^ 2 * d) * (4 / c ^ 2 * Hh) := mul_le_mul_of_nonneg_left hS hcc
      _ = (32 * (ε ^ 2 * d) / c ^ 2) * Hh := by ring
      _ ≤ (32 * (c ^ 2 / 256) / c ^ 2) * Hh := by gcongr
      _ = 1 / 8 * Hh := by field_simp; ring
  have h4 : 1 / 8 * Hh ≤ 1 / c * Hh := by
    have : 1 / 8 ≤ 1 / c := by
      rw [div_le_div_iff₀ (by norm_num) hc0]; linarith
    exact mul_le_mul_of_nonneg_right this hHh0
  have e : 5 / c * Hh = 4 / c * Hh + 1 / c * Hh := by ring
  have e2 : 2 * (2 / c * Hh) = 4 / c * Hh := by ring
  linarith

/-- **Agmon block decay**, for any operator satisfying the energy inequality `hen` for all admissible
weights (the proof of `Balaban.Multiscale.agmon_block` with a free constant `c`). -/
theorem agmon_block_gen (G : GeneratingSet d L N₀ K ϱ) (hd : 0 < d) {c : ℝ} (hc0 : 0 < c)
    (hc2 : c ≤ 1 / 2) {j j' : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ K) (hj'1 : 1 ≤ j') (hj'k : j' ≤ K)
    {y y' : Torus d (N₀ * L ^ K)} (hy : y ∈ G.layer j) (hy' : y' ∈ G.layer j')
    {u f : G.Ω 1 → ℂ} {ε : ℝ} (hε0 : 0 ≤ ε) (hεd : ε * d ≤ c / 16)
    (hen : ∀ r : Torus d (N₀ * L ^ K) → ℝ, IsAgmonWeight G r →
      (1 / 2) * cEnergy (agmonField G ε r u) + (c / 4) * cwsq G (agmonField G ε r u) ≤
        (1 / c) * agmonSource G ε r f)
    (hsupp : ∀ x : G.Ω 1, f x ≠ 0 → jBlock d L N₀ K j' x = jBlock d L N₀ K j' y')
    {t : ℝ} (ht0 : 0 ≤ t) (ht : ENNReal.ofReal t ≤ G.pathDist y y') :
    (∑ x ∈ G.blk j y, ‖zeroExt (G.Ω 1) u x‖ ^ 2 ≤
        8 / c ^ 2 * ((L : ℝ) ^ j) ^ 2 * ((L : ℝ) ^ j') ^ 2 * Real.exp (-(2 * ε * t)) *
          Green.sqNorm f) ∧
    (∑ x ∈ G.blk j y, ∑ μ : Fin d,
        ‖zeroExt (G.Ω 1) u (x + Pi.single μ 1) - zeroExt (G.Ω 1) u x‖ ^ 2 ≤
        10 / c * ((L : ℝ) ^ j') ^ 2 * Real.exp (-(2 * ε * t)) * Green.sqNorm f) := by
  have hε12 : ε ≤ 1 / 2 := by
    have hdd : (1 : ℝ) ≤ d := by exact_mod_cast hd
    nlinarith [mul_nonneg hε0 (by linarith : (0 : ℝ) ≤ d)]
  have h8 : Real.exp (8 * (ε * d)) ≤ 2 := exp_eight_mul_le_two (by positivity) (by linarith)
  have hr : IsAgmonWeight G (G.truncDist y' t) := G.isAgmonWeight_truncDist y' t
  have hry : G.truncDist y' t y = t := G.truncDist_eq_of_le ht0 ht
  have hry' : G.truncDist y' t y' = 0 := G.truncDist_self (G.layer_subset hj'1 hj'k hy') t
  have h := hen _ hr
  have hEnn := cEnergy_nonneg (agmonField G ε (G.truncDist y' t) u)
  have hSnn := cwsq_nonneg G (agmonField G ε (G.truncDist y' t) u)
  have hS : cwsq G (agmonField G ε (G.truncDist y' t) u) ≤
      4 / c ^ 2 * agmonSource G ε (G.truncDist y' t) f := by
    have h2 : c / 4 * cwsq G (agmonField G ε (G.truncDist y' t) u) ≤
        1 / c * agmonSource G ε (G.truncDist y' t) f := by linarith
    have e : 4 / c ^ 2 * agmonSource G ε (G.truncDist y' t) f =
        4 / c * (1 / c * agmonSource G ε (G.truncDist y' t) f) := by field_simp
    rw [e, show cwsq G (agmonField G ε (G.truncDist y' t) u) = 4 / c *
      (c / 4 * cwsq G (agmonField G ε (G.truncDist y' t) u)) by field_simp]
    exact mul_le_mul_of_nonneg_left h2 (by positivity)
  have hE : cEnergy (agmonField G ε (G.truncDist y' t) u) ≤
      2 / c * agmonSource G ε (G.truncDist y' t) f := by
    have : (1 / 2) * cEnergy (agmonField G ε (G.truncDist y' t) u) ≤
        1 / c * agmonSource G ε (G.truncDist y' t) f := by nlinarith [mul_nonneg hc0.le hSnn]
    have e : 2 / c * agmonSource G ε (G.truncDist y' t) f =
        2 * (1 / c * agmonSource G ε (G.truncDist y' t) f) := by ring
    linarith
  have hsrc := agmonSource_le G hr hε0 hj'1 hj'k hy' hry' hsupp
  have hlow := blk_lower G hr hε0 hj1 hjk hy u
  have hgrad := blk_grad_le G hr hε0 hε12 hj1 hjk hy u
  rw [hry] at hlow hgrad
  have hHh0 := agmonSource_nonneg G ε (G.truncDist y' t) f
  have hZZ : Real.exp (4 * ε * d) * Real.exp (4 * ε * d) ≤ 2 := by
    rw [← Real.exp_add]
    have : 4 * ε * d + 4 * ε * d = 8 * (ε * d) := by ring
    rw [this]; exact h8
  have hE20 : 0 < Real.exp (2 * ε * (t - 2 * d)) := Real.exp_pos _
  have hA0 : 0 < ((L : ℝ) ^ j) ^ 2 := by
    have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  have hLj : ((L : ℝ) ^ j) ≠ 0 := by
    have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  have hE2inv : (Real.exp (2 * ε * (t - 2 * d)))⁻¹ =
      Real.exp (-(2 * ε * t)) * Real.exp (4 * ε * d) := by
    rw [← Real.exp_neg, ← Real.exp_add]; congr 1; ring
  have hsf := Green.sqNorm_nonneg f
  refine ⟨?_, ?_⟩
  · have hX2 : ∑ x ∈ G.blk j y, ‖zeroExt (G.Ω 1) u x‖ ^ 2 ≤ ((L : ℝ) ^ j) ^ 2 *
        (Real.exp (-(2 * ε * t)) * Real.exp (4 * ε * d)) *
          cwsq G (agmonField G ε (G.truncDist y' t) u) := by
      rw [← hE2inv]
      have := mul_le_mul_of_nonneg_left hlow
        (mul_nonneg hA0.le (inv_nonneg.2 hE20.le))
      calc _ = (((L : ℝ) ^ j) ^ 2 * (Real.exp (2 * ε * (t - 2 * d)))⁻¹) *
            ((((L : ℝ) ^ j) ^ 2)⁻¹ * Real.exp (2 * ε * (t - 2 * d)) *
              ∑ x ∈ G.blk j y, ‖zeroExt (G.Ω 1) u x‖ ^ 2) := by field_simp
        _ ≤ _ := this
        _ = _ := by ring
    exact numeric_a hc0 hA0.le (by positivity) (Real.exp_pos _).le (Real.exp_pos _).le hsf
      hX2 hS hsrc hZZ
  · have hY2 : ∑ x ∈ G.blk j y, ∑ μ : Fin d,
        ‖zeroExt (G.Ω 1) u (x + Pi.single μ 1) - zeroExt (G.Ω 1) u x‖ ^ 2 ≤
        (Real.exp (-(2 * ε * t)) * Real.exp (4 * ε * d)) *
          (5 / c * agmonSource G ε (G.truncDist y' t) f) := by
      have h1 := hgrad.trans (numeric_grad_gen hd hc0 hc2 hε0 hεd hHh0 hS hE)
      rw [← hE2inv, ← div_eq_inv_mul, le_div_iff₀ hE20]
      linarith
    exact numeric_b hc0 (by positivity) (Real.exp_pos _).le (Real.exp_pos _).le hsf hY2 hsrc hZZ

/-- **G-2(i) for a general constant `c`**: from the block decay `agmon_block_gen` and the scale
mismatch (the proof of `Balaban.Multiscale.green_G2i`). -/
theorem green_G2i_gen (G : GeneratingSet d L N₀ K ϱ) (hd : 0 < d) {c : ℝ} (hc0 : 0 < c)
    (hc2 : c ≤ 1 / 2) {j j' : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ K) (hj'1 : 1 ≤ j') (hj'k : j' ≤ K)
    {y y' : Torus d (N₀ * L ^ K)} (hy : y ∈ G.layer j) (hy' : y' ∈ G.layer j')
    {u f : G.Ω 1 → ℂ} {ε : ℝ} (hε0 : 0 ≤ ε) (hεd : ε * d ≤ c / 16)
    (hen : ∀ r : Torus d (N₀ * L ^ K) → ℝ, IsAgmonWeight G r →
      (1 / 2) * cEnergy (agmonField G ε r u) + (c / 4) * cwsq G (agmonField G ε r u) ≤
        (1 / c) * agmonSource G ε r f)
    (hsupp : ∀ x : G.Ω 1, f x ≠ 0 → jBlock d L N₀ K j' x = jBlock d L N₀ K j' y')
    {t : ℝ} (ht0 : 0 ≤ t) (ht : ENNReal.ofReal t ≤ G.pathDist y y')
    (hϱ : 1 ≤ ϱ) (hsep : (L : ℝ) ≤ Real.exp (ε / 2 * (ϱ - 1))) :
    (L : ℝ) ^ j * Real.sqrt (∑ x ∈ G.blk j y, ∑ μ : Fin d,
        ‖zeroExt (G.Ω 1) u (x + Pi.single μ 1) - zeroExt (G.Ω 1) u x‖ ^ 2) +
      Real.sqrt (∑ x ∈ G.blk j y, ‖zeroExt (G.Ω 1) u x‖ ^ 2) ≤
    13 * L / c * Real.exp (-(ε / 2 * t)) * ((L : ℝ) ^ j') ^ 2 * Real.sqrt (Green.sqNorm f) := by
  have hL : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hL0 : (0 : ℝ) < L := by linarith
  have hyΩ : y ∈ G.Ω j := (G.mem_layer.1 hy).1
  have hsep0 := G.pathDist_separation_le hϱ hj'1 hjk hy' hyΩ
  rw [GeneratingSet.pathDist_comm] at hsep0
  set s₀ : ℝ := (ϱ - 1) * ((j - j' - 1 : ℕ) : ℝ) with hs₀
  have hs₀0 : 0 ≤ s₀ := mul_nonneg (by linarith) (Nat.cast_nonneg _)
  set t₂ := max t s₀ with ht₂
  have ht₂0 : 0 ≤ t₂ := ht0.trans (le_max_left _ _)
  have ht₂d : ENNReal.ofReal t₂ ≤ G.pathDist y y' := by
    rcases le_total t s₀ with h | h
    · rw [ht₂, max_eq_right h]; exact hsep0
    · rw [ht₂, max_eq_left h]; exact ht
  obtain ⟨hA, hB⟩ := agmon_block_gen G hd hc0 hc2 hj1 hjk hj'1 hj'k hy hy' hε0 hεd hen hsupp
    ht₂0 ht₂d
  have hmis := scale_mismatch (L := L) (ε := ε) (t := t) (t₂ := t₂) hε0 j j' hsep
    (le_max_left _ _) (le_max_right _ _)
  set F := Green.sqNorm f with hF
  have hF0 : 0 ≤ F := Green.sqNorm_nonneg f
  set P : ℝ := (L : ℝ) ^ j * (L : ℝ) ^ j' * Real.exp (-(ε * t₂)) * Real.sqrt F with hP
  have hP0 : 0 ≤ P := by positivity
  have hP2 : P ^ 2 = ((L : ℝ) ^ j) ^ 2 * ((L : ℝ) ^ j') ^ 2 * Real.exp (-(2 * ε * t₂)) * F := by
    rw [hP, mul_pow, mul_pow, mul_pow, Real.sq_sqrt hF0, ← Real.exp_nat_mul]
    congr 2
    · push_cast; ring_nf
  have hPle : P ≤ L * ((L : ℝ) ^ j') ^ 2 * Real.exp (-(ε / 2 * t)) * Real.sqrt F := by
    rw [hP]
    exact mul_le_mul_of_nonneg_right hmis (Real.sqrt_nonneg _)
  clear_value P
  set Nn := ∑ x ∈ G.blk j y, ‖zeroExt (G.Ω 1) u x‖ ^ 2 with hNn
  set Yy := ∑ x ∈ G.blk j y, ∑ μ : Fin d,
    ‖zeroExt (G.Ω 1) u (x + Pi.single μ 1) - zeroExt (G.Ω 1) u x‖ ^ 2 with hYy
  have hY0 : 0 ≤ Yy := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hN0 : 0 ≤ Nn := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h1 : Real.sqrt Nn ≤ 3 / c * P := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    calc Nn ≤ 8 / c ^ 2 * P ^ 2 := by rw [hP2]; convert hA using 1; ring
      _ ≤ (3 / c * P) ^ 2 := by
        rw [mul_pow, div_pow]
        have : 8 / c ^ 2 ≤ 3 ^ 2 / c ^ 2 :=
          div_le_div_of_nonneg_right (by norm_num) (by positivity)
        exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
  have h2 : (L : ℝ) ^ j * Real.sqrt Yy ≤ 10 / c * P := by
    have hsq : ((L : ℝ) ^ j * Real.sqrt Yy) ^ 2 ≤ (10 / c * P) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hY0, mul_pow]
      have hB' : ((L : ℝ) ^ j) ^ 2 * Yy ≤ 10 / c * P ^ 2 := by
        rw [hP2]
        calc ((L : ℝ) ^ j) ^ 2 * Yy ≤ ((L : ℝ) ^ j) ^ 2 *
              (10 / c * ((L : ℝ) ^ j') ^ 2 * Real.exp (-(2 * ε * t₂)) * F) :=
            mul_le_mul_of_nonneg_left hB (by positivity)
          _ = _ := by ring
      have h10 : 10 / c ≤ (10 / c) ^ 2 := by
        have : 1 ≤ 10 / c := by
          rw [le_div_iff₀ hc0]; linarith
        nlinarith
      calc _ ≤ 10 / c * P ^ 2 := hB'
        _ ≤ (10 / c) ^ 2 * P ^ 2 := mul_le_mul_of_nonneg_right h10 (sq_nonneg _)
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 hsq
  calc (L : ℝ) ^ j * Real.sqrt Yy + Real.sqrt Nn ≤ 10 / c * P + 3 / c * P := add_le_add h2 h1
    _ = 13 / c * P := by ring
    _ ≤ 13 / c * (L * ((L : ℝ) ^ j') ^ 2 * Real.exp (-(ε / 2 * t)) * Real.sqrt F) :=
        mul_le_mul_of_nonneg_left hPle (by positivity)
    _ = _ := by ring

end Decay

/-! ### The x-variant -/

section XBlock

variable {k : ℕ}
variable (G : GeneratingSet d L N₀ (k + 1) ϱ)

/-- Core of `xDirichletOperator_mulVec_inv` with `1 ≤ k` replaced by the lower bound `1/2 ≤ a_k` (the only use of `k ≥ 1`); the weights `a_j`, `1 ≤ j ≤ k`, stay in `[1/2, 2]`. -/
theorem xDirichletOperator_mulVec_inv_of_ak (hd : 0 < d) (hL : 3 ≤ L) {a : ℕ → ℝ}
    {ν : ℝ} (hν : 0 ≤ ν) (ha : IsAdmissibleWeights k a)
    (hak : 1 / 2 ≤ a k ∧ a k ≤ 2) {aT x : ℝ} (haT1 : 1 / 2 ≤ aT)
    (haT2 : aT ≤ 2) (hx : 0 ≤ x) (α : G.Ω 1 → ℂ)
    (hα : ∀ y, ‖α y‖ ≤ xCoerciveConst d / (2 * (G.spacing y) ^ 2)) (f : G.Ω 1 → ℂ) :
    xDirichletOperator G a aT x ν α *ᵥ ((xDirichletOperator G a aT x ν α)⁻¹ *ᵥ f) = f := by
  have hU := xDirichletOperator_isUnit_of_ak G hd hL hν ha hak haT1 haT2 hx α hα
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hU),
    Matrix.one_mulVec]

/-- `H_{k,x}(α₀) G_{k,x}(α₀) f = f`. -/
theorem xDirichletOperator_mulVec_inv (hd : 0 < d) (hL : 3 ≤ L) (hk : 1 ≤ k) {a : ℕ → ℝ}
    {ν : ℝ} (hν : 0 ≤ ν) (ha : IsAdmissibleWeights k a) {aT x : ℝ} (haT1 : 1 / 2 ≤ aT)
    (haT2 : aT ≤ 2) (hx : 0 ≤ x) (α : G.Ω 1 → ℂ)
    (hα : ∀ y, ‖α y‖ ≤ xCoerciveConst d / (2 * (G.spacing y) ^ 2)) (f : G.Ω 1 → ℂ) :
    xDirichletOperator G a aT x ν α *ᵥ ((xDirichletOperator G a aT x ν α)⁻¹ *ᵥ f) = f :=
  xDirichletOperator_mulVec_inv_of_ak G hd hL hν ha (ha k hk le_rfl) haT1 haT2 hx α hα f

/-- Core of `green_G2i_x` with `1 ≤ k` replaced by the lower bound `1/2 ≤ a_k` (the only use of `k ≥ 1`); the weights `a_j`, `1 ≤ j ≤ k`, stay in `[1/2, 2]`. -/
theorem green_G2i_x_of_ak (hd : 0 < d) (hL : 3 ≤ L) {a : ℕ → ℝ} {ν : ℝ} (hν : 0 ≤ ν)
    (ha : IsAdmissibleWeights k a)
    (hak : 1 / 2 ≤ a k ∧ a k ≤ 2) {aT x : ℝ} (haT1 : 1 / 2 ≤ aT) (haT2 : aT ≤ 2) (hx : 0 ≤ x)
    (α : G.Ω 1 → ℂ) (hα : ∀ y, ‖α y‖ ≤ xCoerciveConst d / (2 * (G.spacing y) ^ 2))
    {j j' : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k + 1) (hj'1 : 1 ≤ j') (hj'k : j' ≤ k + 1)
    {y y' : Torus d (N₀ * L ^ (k + 1))} (hy : y ∈ G.layer j) (hy' : y' ∈ G.layer j')
    {u f : G.Ω 1 → ℂ} (hu : xDirichletOperator G a aT x ν α *ᵥ u = f)
    (hsupp : ∀ z : G.Ω 1, f z ≠ 0 → jBlock d L N₀ (k + 1) j' z = jBlock d L N₀ (k + 1) j' y')
    {t : ℝ} (ht0 : 0 ≤ t) (ht : ENNReal.ofReal t ≤ G.pathDist y y') {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ xAgmonRate d L) (hϱ : 1 ≤ ϱ) (hsep : (L : ℝ) ≤ Real.exp (ε / 2 * (ϱ - 1))) :
    (L : ℝ) ^ j * Real.sqrt (∑ z ∈ G.blk j y, ∑ μ : Fin d,
        ‖zeroExt (G.Ω 1) u (z + Pi.single μ 1) - zeroExt (G.Ω 1) u z‖ ^ 2) +
      Real.sqrt (∑ z ∈ G.blk j y, ‖zeroExt (G.Ω 1) u z‖ ^ 2) ≤
    13 * L / xPoincareConst d * Real.exp (-(ε / 2 * t)) * ((L : ℝ) ^ j') ^ 2 *
      Real.sqrt (Green.sqNorm f) := by
  have hc0 := xPoincareConst_pos hd
  have hc2 : xPoincareConst d ≤ 1 / 2 := (xPoincareConst_le_quarter d).trans (by norm_num)
  have hLr : (3 : ℝ) ≤ L := by exact_mod_cast hL
  have hdd : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hεd : ε * d ≤ xPoincareConst d / 16 := by
    have : ε * (d * L) ≤ xAgmonRate d L * (d * L) := by gcongr
    have e : xAgmonRate d L * (d * L) = xPoincareConst d / 16 := by
      unfold xAgmonRate; field_simp
    have h2 : ε * d * 1 ≤ ε * d * L := by
      have : (1 : ℝ) ≤ L := by linarith
      exact mul_le_mul_of_nonneg_left this (by positivity)
    nlinarith
  exact green_G2i_gen G hd hc0 hc2 hj1 hjk hj'1 hj'k hy hy' hε0 hεd
    (fun r hr => x_agmon_energy_of_ak G hd hL hν ha hak haT1 haT2 hx α hα hr hε0 hε1 hu) hsupp ht0 ht
    hϱ hsep

/-- **G-2(vii)(i): the `L²` Agmon block decay for `G_{k,x}(α₀)`, uniformly in `x ≥ 0`.**
Let `G` be a generating set of level `k + 1` (so `Ω_{k+1}` is its top layer), `u` solve
`H_{k,x}(α₀) u = f` with `f` supported in the block `Δ_{j'}(y')`, `y ∈` layer `j`,
`1 ≤ j, j' ≤ k + 1`, `0 ≤ ε ≤ ε₀' = c_x/(16 d L)`, `L ≤ exp ((ε/2)(ϱ - 1))`. Then for
`0 ≤ t ≤ d(y, y')`
`ℓ_j ‖χ_{Δ_j(y)} ∂ũ‖ + ‖χ_{Δ_j(y)} ũ‖ ≤ (13 L / c_x) e^{-(ε/2) t} ℓ_{j'}² ‖f‖`. -/
theorem green_G2i_x (hd : 0 < d) (hL : 3 ≤ L) (hk : 1 ≤ k) {a : ℕ → ℝ} {ν : ℝ} (hν : 0 ≤ ν)
    (ha : IsAdmissibleWeights k a) {aT x : ℝ} (haT1 : 1 / 2 ≤ aT) (haT2 : aT ≤ 2) (hx : 0 ≤ x)
    (α : G.Ω 1 → ℂ) (hα : ∀ y, ‖α y‖ ≤ xCoerciveConst d / (2 * (G.spacing y) ^ 2))
    {j j' : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k + 1) (hj'1 : 1 ≤ j') (hj'k : j' ≤ k + 1)
    {y y' : Torus d (N₀ * L ^ (k + 1))} (hy : y ∈ G.layer j) (hy' : y' ∈ G.layer j')
    {u f : G.Ω 1 → ℂ} (hu : xDirichletOperator G a aT x ν α *ᵥ u = f)
    (hsupp : ∀ z : G.Ω 1, f z ≠ 0 → jBlock d L N₀ (k + 1) j' z = jBlock d L N₀ (k + 1) j' y')
    {t : ℝ} (ht0 : 0 ≤ t) (ht : ENNReal.ofReal t ≤ G.pathDist y y') {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ xAgmonRate d L) (hϱ : 1 ≤ ϱ) (hsep : (L : ℝ) ≤ Real.exp (ε / 2 * (ϱ - 1))) :
    (L : ℝ) ^ j * Real.sqrt (∑ z ∈ G.blk j y, ∑ μ : Fin d,
        ‖zeroExt (G.Ω 1) u (z + Pi.single μ 1) - zeroExt (G.Ω 1) u z‖ ^ 2) +
      Real.sqrt (∑ z ∈ G.blk j y, ‖zeroExt (G.Ω 1) u z‖ ^ 2) ≤
    13 * L / xPoincareConst d * Real.exp (-(ε / 2 * t)) * ((L : ℝ) ^ j') ^ 2 *
      Real.sqrt (Green.sqNorm f) :=
  green_G2i_x_of_ak G hd hL hν ha (ha k hk le_rfl) haT1 haT2 hx α hα hj1 hjk hj'1 hj'k hy hy' hu hsupp ht0 ht hε0 hε1 hϱ hsep

/-- Core of `green_G2i_x_green` with `1 ≤ k` replaced by the lower bound `1/2 ≤ a_k` (the only use of `k ≥ 1`); the weights `a_j`, `1 ≤ j ≤ k`, stay in `[1/2, 2]`. -/
theorem green_G2i_x_green_of_ak (hd : 0 < d) (hL : 3 ≤ L) {a : ℕ → ℝ} {ν : ℝ}
    (hν : 0 ≤ ν) (ha : IsAdmissibleWeights k a)
    (hak : 1 / 2 ≤ a k ∧ a k ≤ 2) {aT x : ℝ} (haT1 : 1 / 2 ≤ aT) (haT2 : aT ≤ 2)
    (hx : 0 ≤ x) (α : G.Ω 1 → ℂ)
    (hα : ∀ y, ‖α y‖ ≤ xCoerciveConst d / (2 * (G.spacing y) ^ 2))
    {j j' : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k + 1) (hj'1 : 1 ≤ j') (hj'k : j' ≤ k + 1)
    {y y' : Torus d (N₀ * L ^ (k + 1))} (hy : y ∈ G.layer j) (hy' : y' ∈ G.layer j')
    {f : G.Ω 1 → ℂ}
    (hsupp : ∀ z : G.Ω 1, f z ≠ 0 → jBlock d L N₀ (k + 1) j' z = jBlock d L N₀ (k + 1) j' y')
    {t : ℝ} (ht0 : 0 ≤ t) (ht : ENNReal.ofReal t ≤ G.pathDist y y') {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ xAgmonRate d L) (hϱ : 1 ≤ ϱ) (hsep : (L : ℝ) ≤ Real.exp (ε / 2 * (ϱ - 1))) :
    (L : ℝ) ^ j * Real.sqrt (∑ z ∈ G.blk j y, ∑ μ : Fin d,
        ‖zeroExt (G.Ω 1) ((xDirichletOperator G a aT x ν α)⁻¹ *ᵥ f) (z + Pi.single μ 1) -
          zeroExt (G.Ω 1) ((xDirichletOperator G a aT x ν α)⁻¹ *ᵥ f) z‖ ^ 2) +
      Real.sqrt (∑ z ∈ G.blk j y,
        ‖zeroExt (G.Ω 1) ((xDirichletOperator G a aT x ν α)⁻¹ *ᵥ f) z‖ ^ 2) ≤
    13 * L / xPoincareConst d * Real.exp (-(ε / 2 * t)) * ((L : ℝ) ^ j') ^ 2 *
      Real.sqrt (Green.sqNorm f) :=
  green_G2i_x_of_ak G hd hL hν ha hak haT1 haT2 hx α hα hj1 hjk hj'1 hj'k hy hy'
    (xDirichletOperator_mulVec_inv_of_ak G hd hL hν ha hak haT1 haT2 hx α hα f) hsupp ht0 ht hε0 hε1 hϱ
    hsep

/-- **G-2(vii)(i) for the Green's function** `G_{k,x}(α₀) = H_{k,x}(α₀)⁻¹`. -/
theorem green_G2i_x_green (hd : 0 < d) (hL : 3 ≤ L) (hk : 1 ≤ k) {a : ℕ → ℝ} {ν : ℝ}
    (hν : 0 ≤ ν) (ha : IsAdmissibleWeights k a) {aT x : ℝ} (haT1 : 1 / 2 ≤ aT) (haT2 : aT ≤ 2)
    (hx : 0 ≤ x) (α : G.Ω 1 → ℂ)
    (hα : ∀ y, ‖α y‖ ≤ xCoerciveConst d / (2 * (G.spacing y) ^ 2))
    {j j' : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k + 1) (hj'1 : 1 ≤ j') (hj'k : j' ≤ k + 1)
    {y y' : Torus d (N₀ * L ^ (k + 1))} (hy : y ∈ G.layer j) (hy' : y' ∈ G.layer j')
    {f : G.Ω 1 → ℂ}
    (hsupp : ∀ z : G.Ω 1, f z ≠ 0 → jBlock d L N₀ (k + 1) j' z = jBlock d L N₀ (k + 1) j' y')
    {t : ℝ} (ht0 : 0 ≤ t) (ht : ENNReal.ofReal t ≤ G.pathDist y y') {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ xAgmonRate d L) (hϱ : 1 ≤ ϱ) (hsep : (L : ℝ) ≤ Real.exp (ε / 2 * (ϱ - 1))) :
    (L : ℝ) ^ j * Real.sqrt (∑ z ∈ G.blk j y, ∑ μ : Fin d,
        ‖zeroExt (G.Ω 1) ((xDirichletOperator G a aT x ν α)⁻¹ *ᵥ f) (z + Pi.single μ 1) -
          zeroExt (G.Ω 1) ((xDirichletOperator G a aT x ν α)⁻¹ *ᵥ f) z‖ ^ 2) +
      Real.sqrt (∑ z ∈ G.blk j y,
        ‖zeroExt (G.Ω 1) ((xDirichletOperator G a aT x ν α)⁻¹ *ᵥ f) z‖ ^ 2) ≤
    13 * L / xPoincareConst d * Real.exp (-(ε / 2 * t)) * ((L : ℝ) ^ j') ^ 2 *
      Real.sqrt (Green.sqNorm f) :=
  green_G2i_x_green_of_ak G hd hL hν ha (ha k hk le_rfl) haT1 haT2 hx α hα hj1 hjk hj'1 hj'k hy hy' hsupp ht0 ht hε0 hε1 hϱ hsep

end XBlock

end Balaban.Multiscale
