/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Multiscale.GlobalBound
public import Balaban.Multiscale.Counting
public import Balaban.Multiscale.CutCube
public import Balaban.Multiscale.KernelAlgebra

/-!
# Weighted sums of block pieces (LOCALIZATION.md §3.1, "Weighted form of (NC3)")

A weight of rate `γ` is a function `w ≥ 1` with `w(x) ≤ w(x') e^{γ d(x,x')}` (`IsWeight`; `d` the
path metric).  `weighted_sum_bound` is the summation behind the weighted form of (NC3):
if a solution operator `u = M f` (a matrix `M` on `Ω₁`, zero-extended) and a linear observable
`o` satisfy the *block bound* — for a source `f` supported in one block of a point `y'` of the
support set `Λ`, `s ‖o ũ‖ ≤ K e^{-γ₀ d(p, y')} ℓ_{j'}² ‖f‖_∞` — then, for every `f` supported in `Λ`
with `w ℓ² |f| ≤ C`, `w(p) s ‖o ũ‖ ≤ B C` with `B = K e^{2 γ d} C(d, L, γ₀ - γ)`.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Finset Matrix

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- A weight of rate `γ` for the path metric of `G`: `w ≥ 1` and `w(x) e^{-γ d(x,y)} ≤ w(y)`. -/
def IsWeight (G : GeneratingSet d L N₀ k ϱ) (γ : ℝ) (w : Torus d (N₀ * L ^ k) → ℝ) : Prop :=
  (∀ x, 1 ≤ w x) ∧ ∀ x y, w x * decay γ (G.pathDist x y) ≤ w y

theorem IsWeight.one (G : GeneratingSet d L N₀ k ϱ) {γ : ℝ} (hγ : 0 ≤ γ) :
    IsWeight G γ (fun _ => 1) :=
  ⟨fun _ => le_rfl, fun x y => by simpa using decay_le_one hγ _⟩

theorem IsWeight.pos {G : GeneratingSet d L N₀ k ϱ} {γ : ℝ} {w : Torus d (N₀ * L ^ k) → ℝ}
    (h : IsWeight G γ w) (x : Torus d (N₀ * L ^ k)) : 0 < w x :=
  lt_of_lt_of_le one_pos (h.1 x)

/-- Weights vary by the factor `e^{γ ρ}` over points at path distance `≤ ρ`. -/
theorem IsWeight.le_mul {G : GeneratingSet d L N₀ k ϱ} {γ : ℝ} (hγ : 0 ≤ γ)
    {w : Torus d (N₀ * L ^ k) → ℝ} (h : IsWeight G γ w) {x y : Torus d (N₀ * L ^ k)} {ρ : ℝ}
    (hρ : 0 ≤ ρ) (hxy : G.pathDist x y ≤ ENNReal.ofReal ρ) : w x ≤ w y * Real.exp (γ * ρ) := by
  have h1 := h.2 x y
  have h2 := decay_ofReal_ge hγ hρ hxy
  have h3 : w x * Real.exp (-(γ * ρ)) ≤ w y :=
    (mul_le_mul_of_nonneg_left h2 (h.pos x).le).trans h1
  have hE := Real.exp_pos (γ * ρ)
  calc w x = w x * Real.exp (-(γ * ρ)) * Real.exp (γ * ρ) := by
        rw [mul_assoc, ← Real.exp_add]; simp
    _ ≤ w y * Real.exp (γ * ρ) := mul_le_mul_of_nonneg_right h3 hE.le

theorem decay_split {c c' : ℝ} (D : ENNReal) :
    decay (c + c') D = decay c D * decay c' D := by
  unfold decay
  by_cases h : D = ⊤
  · simp [h]
  · simp only [h, ↓reduceIte, ← Real.exp_add]
    congr 1; ring

/-- The weight comparison with a decay factor. -/
theorem IsWeight.mul_decay_le {G : GeneratingSet d L N₀ k ϱ} {γ γ' : ℝ}
    {w : Torus d (N₀ * L ^ k) → ℝ} (h : IsWeight G γ w) (x y : Torus d (N₀ * L ^ k)) :
    w x * decay (γ + γ') (G.pathDist x y) ≤ w y * decay γ' (G.pathDist x y) := by
  rw [decay_split, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (h.2 x y) (decay_nonneg _ _)

section Sum

variable (G : GeneratingSet d L N₀ k ϱ)

/-- The matrix solution map, zero extended to the torus. -/
noncomputable def solExt (M : Matrix (G.Ω 1) (G.Ω 1) ℂ) (f : G.Ω 1 → ℂ) :
    Torus d (N₀ * L ^ k) → ℂ :=
  zeroExt (G.Ω 1) (M *ᵥ f)

theorem solExt_sum {ι : Type*} (M : Matrix (G.Ω 1) (G.Ω 1) ℂ) (s : Finset ι)
    (c : ι → ℂ) (f : ι → G.Ω 1 → ℂ) (p : Torus d (N₀ * L ^ k)) :
    solExt G M (∑ i ∈ s, c i • f i) p = ∑ i ∈ s, c i * solExt G M (f i) p := by
  classical
  unfold solExt zeroExt
  split_ifs with h
  · rw [Matrix.mulVec_sum]
    simp only [Matrix.mulVec_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  · simp

theorem blockPiece_ne_zero {f : G.Ω 1 → ℂ} {y z : G.Ω 1} (h : blockPiece G f y z ≠ 0) :
    jBlock d L N₀ k (G.layerIndex (y : Torus d (N₀ * L ^ k))) z =
      jBlock d L N₀ k (G.layerIndex (y : Torus d (N₀ * L ^ k))) y ∧ f z ≠ 0 := by
  unfold blockPiece at h
  split_ifs at h with hb
  · exact ⟨hb, h⟩
  · exact absurd rfl h

end Sum

variable {G : GeneratingSet d L N₀ k ϱ}

/-- **Weighted summation of block pieces.** -/
theorem weighted_sum_bound {γ γ0 Kc s : ℝ} (hγ : 0 ≤ γ) (hγγ : γ < γ0) (hKc : 0 ≤ Kc)
    (hs : 0 ≤ s) {w : Torus d (N₀ * L ^ k) → ℝ} (hw : IsWeight G γ w)
    (M : Matrix (G.Ω 1) (G.Ω 1) ℂ) (o : (Torus d (N₀ * L ^ k) → ℂ) →ₗ[ℂ] ℂ)
    {p : Torus d (N₀ * L ^ k)} (hp : p ∈ G.Ω 1) {Λ : Finset (Torus d (N₀ * L ^ k))}
    (hΛ : BlockAligned G Λ) (hϱ1 : 1 < ϱ)
    (hcond : 2 * d * Real.log L ≤ (γ0 - γ) / 2 * (ϱ - 1))
    (hpiece : ∀ {j' : ℕ} {y' : Torus d (N₀ * L ^ k)}, 1 ≤ j' → j' ≤ k → y' ∈ G.layer j' →
      y' ∈ Λ → ∀ (f : G.Ω 1 → ℂ),
      (∀ z : G.Ω 1, f z ≠ 0 → jBlock d L N₀ k j' z = jBlock d L N₀ k j' y') →
      ∀ {Mf : ℝ}, 0 ≤ Mf → (∀ z, ‖f z‖ ≤ Mf) →
      s * ‖o (solExt G M f)‖ ≤ Kc * decay γ0 (G.pathDist p y') * ((L : ℝ) ^ (2 * j') * Mf))
    (f : G.Ω 1 → ℂ) (hf : ∀ z : G.Ω 1, f z ≠ 0 → (z : Torus d (N₀ * L ^ k)) ∈ Λ) {C : ℝ}
    (hC : 0 ≤ C) (hfC : ∀ x : G.Ω 1, w x * (G.spacing (x : Torus d (N₀ * L ^ k))) ^ 2 * ‖f x‖ ≤ C) :
    w p * (s * ‖o (solExt G M f)‖) ≤
      Kc * Real.exp (2 * γ * d) * countConst d L (γ0 - γ) * C := by
  classical
  have hγ' : 0 < γ0 - γ := by linarith
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hd0 : (0 : ℝ) ≤ d := by positivity
  -- decomposition of the source
  have hfeq : f = ∑ y : G.Ω 1, (siteWeight G y : ℂ) • blockPiece G f y := by
    funext z
    rw [Finset.sum_apply]
    simpa using (sum_siteWeight_blockPiece G f z).symm
  have hosum : o (solExt G M f) = ∑ y : G.Ω 1, (siteWeight G y : ℂ) * o (solExt G M (blockPiece G f y)) := by
    have : solExt G M f = fun p => ∑ y : G.Ω 1, (siteWeight G y : ℂ) * solExt G M (blockPiece G f y) p := by
      funext p
      conv_lhs => rw [hfeq]
      exact solExt_sum G M _ _ _ p
    rw [this]
    have h2 : (fun p => ∑ y : G.Ω 1, (siteWeight G y : ℂ) * solExt G M (blockPiece G f y) p) =
        ∑ y : G.Ω 1, (siteWeight G y : ℂ) • solExt G M (blockPiece G f y) := by
      funext p; simp [Finset.sum_apply]
    rw [h2, map_sum]
    simp
  -- the bound for each piece
  have hterm : ∀ y : G.Ω 1, w p * (s * ‖o (solExt G M (blockPiece G f y))‖) ≤
      Kc * Real.exp (2 * γ * d) * C * decay (γ0 - γ) (G.pathDist p y) := by
    intro y
    by_cases hz : blockPiece G f y = 0
    · have : solExt G M (blockPiece G f y) = 0 := by
        funext q; unfold solExt; rw [hz]; simp [zeroExt]
      rw [this]; simp only [map_zero, norm_zero, mul_zero]
      have := decay_nonneg (γ0 - γ) (G.pathDist p y)
      positivity
    · obtain ⟨hj1, hjk, hyl⟩ := G.layerIndex_spec y.2
      set j := G.layerIndex (y : Torus d (N₀ * L ^ k)) with hj
      -- the block of y meets the support of f, hence y ∈ Λ
      have hyΛ : (y : Torus d (N₀ * L ^ k)) ∈ Λ := by
        obtain ⟨z, hz'⟩ := Function.ne_iff.1 hz
        obtain ⟨hzb, hzf⟩ := blockPiece_ne_zero G (by simpa using hz')
        exact (hΛ j hj1 hjk _ _ hyl hzb).2 (hf z hzf)
      have hsp : G.spacing (y : Torus d (N₀ * L ^ k)) = (L : ℝ) ^ j := G.spacing_eq hj1 hjk hyl
      have hLp : (0 : ℝ) < (L : ℝ) ^ j := by positivity
      have hwy := hw.pos y
      set Mf : ℝ := C * Real.exp (2 * γ * d) / (w y * ((L : ℝ) ^ j) ^ 2) with hMf
      have hMf0 : 0 ≤ Mf := by positivity
      have hMfb : ∀ z, ‖blockPiece G f y z‖ ≤ Mf := by
        intro z
        unfold blockPiece
        split_ifs with h
        · have h1 := hfC z
          rw [mem_layer_of_blockPiece G y z h, hsp] at h1
          have hzl : (z : Torus d (N₀ * L ^ k)) ∈ G.layer j := (G.mem_layer_iff hj1 hjk h).2 hyl
          have hdist := G.pathDist_block_le hj1 hjk hyl h
          have hwz := hw.le_mul hγ (by positivity : (0 : ℝ) ≤ 2 * d) hdist
          have hwzpos := hw.pos z
          rw [hMf, le_div_iff₀ (by positivity)]
          have h2 : w y ≤ w z * Real.exp (γ * (2 * d)) := hwz
          have h3 : ‖f z‖ * (w y * ((L : ℝ) ^ j) ^ 2) ≤ ‖f z‖ * (w z * Real.exp (γ * (2 * d)) *
              ((L : ℝ) ^ j) ^ 2) := by
            apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
            exact mul_le_mul_of_nonneg_right h2 (by positivity)
          calc ‖f z‖ * (w y * ((L : ℝ) ^ j) ^ 2) ≤ ‖f z‖ * (w z * Real.exp (γ * (2 * d)) *
              ((L : ℝ) ^ j) ^ 2) := h3
            _ = (w z * ((L : ℝ) ^ j) ^ 2 * ‖f z‖) * Real.exp (2 * γ * d) := by
                rw [show 2 * γ * d = γ * (2 * d) by ring]; ring
            _ ≤ C * Real.exp (2 * γ * d) :=
                mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
        · simpa using hMf0
      have hsupp : ∀ z : G.Ω 1, blockPiece G f y z ≠ 0 →
          jBlock d L N₀ k j z = jBlock d L N₀ k j y := fun z hzz => (blockPiece_ne_zero G hzz).1
      have hP := hpiece hj1 hjk hyl hyΛ (blockPiece G f y) hsupp hMf0 hMfb
      have hF : (L : ℝ) ^ (2 * j) * Mf = C * Real.exp (2 * γ * d) / w y := by
        rw [hMf, pow_mul']
        field_simp
      rw [hF] at hP
      have hwc : w p * decay γ0 (G.pathDist p y) ≤ w y * decay (γ0 - γ) (G.pathDist p y) := by
        have := hw.mul_decay_le (γ' := γ0 - γ) p y
        rwa [show γ + (γ0 - γ) = γ0 by ring] at this
      calc w p * (s * ‖o (solExt G M (blockPiece G f y))‖)
          ≤ w p * (Kc * decay γ0 (G.pathDist p y) * (C * Real.exp (2 * γ * d) / w y)) :=
            mul_le_mul_of_nonneg_left hP (hw.pos p).le
        _ = (w p * decay γ0 (G.pathDist p y)) * (Kc * (C * Real.exp (2 * γ * d)) / w y) := by
            field_simp
        _ ≤ (w y * decay (γ0 - γ) (G.pathDist p y)) * (Kc * (C * Real.exp (2 * γ * d)) / w y) :=
            mul_le_mul_of_nonneg_right hwc (by positivity)
        _ = _ := by field_simp
  -- summation
  have hsum := sum_siteWeight_decay_le G hϱ1 hγ' hcond hp
  rw [hosum]
  calc w p * (s * ‖∑ y : G.Ω 1, (siteWeight G y : ℂ) * o (solExt G M (blockPiece G f y))‖)
      ≤ w p * (s * ∑ y : G.Ω 1, siteWeight G y * ‖o (solExt G M (blockPiece G f y))‖) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hs) (hw.pos p).le
        refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun y _ => ?_))
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (siteWeight_nonneg G _)]
    _ = ∑ y : G.Ω 1, siteWeight G y * (w p * (s * ‖o (solExt G M (blockPiece G f y))‖)) := by
        rw [Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun y _ => by ring
    _ ≤ ∑ y : G.Ω 1, siteWeight G y *
          (Kc * Real.exp (2 * γ * d) * C * decay (γ0 - γ) (G.pathDist p y)) :=
        Finset.sum_le_sum fun y _ =>
          mul_le_mul_of_nonneg_left (hterm y) (siteWeight_nonneg G _)
    _ = Kc * Real.exp (2 * γ * d) * C *
          ∑ y : G.Ω 1, siteWeight G y * decay (γ0 - γ) (G.pathDist p y) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun y _ => by ring
    _ ≤ Kc * Real.exp (2 * γ * d) * C * countConst d L (γ0 - γ) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by ring

end Balaban.Localization
