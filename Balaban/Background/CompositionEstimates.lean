/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Background.CompositionSystem
public import Balaban.Multiscale.PathMetricBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# Estimates for the composed field (BACKGROUND.md §6.6; the common core of Lemmas 6.2, 6.3, (R-S))

Everything here is stated for complex vector fields with the Euclidean norm `vn`; the real cases
are specializations.  Notation: `φ'` is a field on `Ω'₁` with data `Ψ'`, `F = φ̄'` its extension
by `Ψ'`, `θ` the scale gap (`ℓ(x) ≤ θ ℓ'(x)` on `Ω₁`; `θ = 1` for `𝔹_j ≺ 𝔹'_k`), `η` the size of
the bounds of Theorem 5.2 (3) (`K₁ δ` in Lemma 6.2).

* `Balaban.Background.FieldBounds`: the hypotheses `|φ' - Q*Ψ'|₀ ≤ η`, `|∂φ̄'|₁, |Δφ̄'|₂ ≤ η`,
  `φ' · φ' = 1`;
* `vn_block_osc`: the oscillation of a field with Lipschitz bond bounds inside one block
  (`≤ 2 d A`, through the corner of the block);
* `compVec_sub_mean`, `compVec_sub_bar`: (E1) and the comparison `|Ψ - φ̄'(y)| ≤ (2d + θ) θ η`;
* `compVec_dot_sub_one`: the bilinear estimate `|Ψ · Ψ - 1| ≲ (2dθη)² + 2θ²η M + θ⁴η²`;
* `compVec_interface`: the interface estimate (R1).
-/

@[expose] public section

namespace Balaban.Background

open Balaban.Multiscale Matrix Finset

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ ϱ' : ℝ}

/-! ### Vector norm lemmas -/

theorem vn_smul_complex (c : ℂ) (v : Fin N → ℂ) : vn (fun i => c * v i) = ‖c‖ * vn v := by
  unfold vn
  have : (WithLp.toLp 2 (fun i => c * v i) : EuclideanSpace ℂ (Fin N)) =
      c • (WithLp.toLp 2 v : EuclideanSpace ℂ (Fin N)) := by
    ext i; simp
  rw [this, norm_smul]

theorem vn_smul_real (r : ℝ) (v : Fin N → ℂ) : vn (fun i => (r : ℂ) * v i) = |r| * vn v := by
  rw [vn_smul_complex, Complex.norm_real, Real.norm_eq_abs]

theorem vn_sum_le {ι : Type*} (S : Finset ι) (g : ι → Fin N → ℂ) :
    vn (fun i => ∑ y ∈ S, g y i) ≤ ∑ y ∈ S, vn (g y) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact (vn_zero (N := N)).le
  | insert a S ha ih =>
    simp only [Finset.sum_insert ha]
    have h := vn_add (g a) (fun i => ∑ y ∈ S, g y i)
    exact h.trans (by linarith)

theorem vn_neg (v : Fin N → ℂ) : vn (fun i => -v i) = vn v := by
  have := vn_smul_complex (-1) v
  simpa using this

theorem vn_sub_le' (u w : Fin N → ℂ) : vn (fun i => u i - w i) ≤ vn u + vn w := by
  have h := vn_add u (fun i => -w i)
  rw [vn_neg] at h
  have e : (fun i => u i - w i) = u + fun i => -w i := by
    funext i; simp [sub_eq_add_neg]
  rw [e]; exact h

/-- The Euclidean norm of a real vector. -/
theorem vn_ofReal (v : Fin N → ℝ) : vn (fun i => (v i : ℂ)) = rn v := by
  rw [vn_eq_sqrt]
  unfold rn
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- A vector with vanishing imaginary part. -/
def IsRealVec (v : Fin N → ℂ) : Prop := ∀ i, (v i).im = 0

theorem IsRealVec.eq_ofReal {v : Fin N → ℂ} (h : IsRealVec v) :
    v = fun i => ((v i).re : ℂ) := by
  funext i
  exact Complex.ext (by simp) (by simpa using h i)

theorem IsRealVec.vn_eq {v : Fin N → ℂ} (h : IsRealVec v) : vn v = rn (fun i => (v i).re) := by
  rw [← vn_ofReal, ← h.eq_ofReal]

theorem IsRealVec.dot_self {v : Fin N → ℂ} (h : IsRealVec v) :
    ∑ i, v i * v i = ((∑ i, (v i).re ^ 2 : ℝ) : ℂ) := by
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  have := h i
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, this, sq]

theorem rn_sq (v : Fin N → ℝ) : rn v ^ 2 = ∑ i, v i ^ 2 := by
  unfold rn
  exact Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)

theorem rn_nonneg (v : Fin N → ℝ) : 0 ≤ rn v := Real.sqrt_nonneg _

/-! ### Block means -/

section Means

variable {G : GeneratingSet d L N₀ k ϱ}

theorem blockMean_sub (n : ℕ) (u w : Torus d (N₀ * L ^ k) → ℂ) (x : Torus d (N₀ * L ^ k)) :
    blockMean G n (fun y => u y - w y) x = blockMean G n u x - blockMean G n w x := by
  unfold blockMean
  rw [Finset.sum_sub_distrib, mul_sub]

theorem blockMean_add (n : ℕ) (u w : Torus d (N₀ * L ^ k) → ℂ) (x : Torus d (N₀ * L ^ k)) :
    blockMean G n (fun y => u y + w y) x = blockMean G n u x + blockMean G n w x := by
  unfold blockMean
  rw [Finset.sum_add_distrib, mul_add]

theorem blockMean_smul (n : ℕ) (c : ℂ) (u : Torus d (N₀ * L ^ k) → ℂ) (x : Torus d (N₀ * L ^ k)) :
    blockMean G n (fun y => c * u y) x = c * blockMean G n u x := by
  unfold blockMean
  rw [← Finset.mul_sum]; ring

theorem x_mem_blk (n : ℕ) (x : Torus d (N₀ * L ^ k)) : x ∈ G.blk n x :=
  GeneratingSet.mem_blk.2 rfl

/-- The block mean of a vector field is bounded by the bound on the field in the block. -/
theorem vn_blockMean_le {n : ℕ} (hn : n ≤ k) (g : Torus d (N₀ * L ^ k) → Fin N → ℂ)
    (x : Torus d (N₀ * L ^ k)) {c : ℝ} (hc : ∀ y ∈ G.blk n x, vn (g y) ≤ c) :
    vn (fun i => blockMean G n (fun y => g y i) x) ≤ c := by
  have hcard := card_blk_cast G n hn x
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hK : (0 : ℝ) ≤ ((((L : ℝ) ^ n) ^ d)⁻¹) := by positivity
  have h1 : vn (fun i => blockMean G n (fun y => g y i) x) =
      ((((L : ℝ) ^ n) ^ d)⁻¹) * vn (fun i => ∑ y ∈ G.blk n x, g y i) := by
    unfold blockMean
    rw [vn_smul_real, abs_of_nonneg hK]
  rw [h1]
  have h2 : vn (fun i => ∑ y ∈ G.blk n x, g y i) ≤ ((L : ℝ) ^ n) ^ d * c := by
    refine (vn_sum_le _ _).trans ?_
    calc ∑ y ∈ G.blk n x, vn (g y) ≤ ∑ _y ∈ G.blk n x, c := Finset.sum_le_sum hc
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, hcard]
  have hpos : (0 : ℝ) < ((L : ℝ) ^ n) ^ d := by positivity
  calc _ ≤ ((((L : ℝ) ^ n) ^ d)⁻¹) * (((L : ℝ) ^ n) ^ d * c) := mul_le_mul_of_nonneg_left h2 hK
    _ = c := by field_simp

/-- A block mean is within `c` of `z` if the field is. -/
theorem vn_blockMean_sub_le {n : ℕ} (hn : n ≤ k) (g : Torus d (N₀ * L ^ k) → Fin N → ℂ)
    (x : Torus d (N₀ * L ^ k)) (z : Fin N → ℂ) {c : ℝ}
    (hc : ∀ y ∈ G.blk n x, vn (fun i => g y i - z i) ≤ c) :
    vn (fun i => blockMean G n (fun y => g y i) x - z i) ≤ c := by
  have h := vn_blockMean_le (G := G) hn (fun y i => g y i - z i) x hc
  have e : ∀ i, blockMean G n (fun y => g y i - z i) x =
      blockMean G n (fun y => g y i) x - z i := fun i => by
    rw [blockMean_sub, blockMean_const G hn]
  simpa only [e] using h

/-- The scaled version: `s * |mean - z| ≤ c` if `s * |g - z| ≤ c` on the block. -/
theorem vn_blockMean_sub_le_scaled {n : ℕ} (hn : n ≤ k) (g : Torus d (N₀ * L ^ k) → Fin N → ℂ)
    (x : Torus d (N₀ * L ^ k)) (z : Fin N → ℂ) {s c : ℝ} (hs : 0 ≤ s)
    (hc : ∀ y ∈ G.blk n x, s * vn (fun i => g y i - z i) ≤ c) :
    s * vn (fun i => blockMean G n (fun y => g y i) x - z i) ≤ c := by
  have h := vn_blockMean_le (G := G) hn (fun y i => (s : ℂ) * (g y i - z i)) x (c := c) (by
    intro y hy
    rw [vn_smul_real, abs_of_nonneg hs]
    exact hc y hy)
  have e : ∀ i, blockMean G n (fun y => (s : ℂ) * (g y i - z i)) x =
      (s : ℂ) * (blockMean G n (fun y => g y i) x - z i) := fun i => by
    rw [blockMean_smul, blockMean_sub, blockMean_const G hn]
  simp only [e] at h
  rwa [vn_smul_real, abs_of_nonneg hs] at h

end Means

/-! ### Paths inside a block -/

section Paths

variable {G : GeneratingSet d L N₀ k ϱ}

theorem vn_sub_le_of_pathCost (f : Torus d (N₀ * L ^ k) → Fin N → ℂ) {A : ℝ}
    (hf : ∀ x x', x ∈ G.Ω 1 → x' ∈ G.Ω 1 → Adj x x' → vn (f x' - f x) ≤ A * G.bondCost x x')
    {x y : Torus d (N₀ * L ^ k)} {c : ℝ} (h : G.PathCost x y c) : vn (f y - f x) ≤ A * c := by
  induction h with
  | refl x hx => simp [vn_zero]
  | step x y z c hx hadj hp ih =>
    have h1 := hf x y hx hp.left_mem hadj
    have h2 := vn_triangle (f z) (f y) (f x)
    calc vn (f z - f x) ≤ vn (f z - f y) + vn (f y - f x) := h2
      _ ≤ A * c + A * G.bondCost x y := add_le_add ih h1
      _ = A * (G.bondCost x y + c) := by ring

/-- **Oscillation inside a block**: a field with Lipschitz bond bounds `A / ℓ(b)` changes by at
most `2 d A` inside a block of its layer (through the corner of the block). -/
theorem vn_block_osc (f : Torus d (N₀ * L ^ k) → Fin N → ℂ) {A : ℝ} (hA : 0 ≤ A)
    (hf : ∀ x x', x ∈ G.Ω 1 → x' ∈ G.Ω 1 → Adj x x' → vn (f x' - f x) ≤ A * G.bondCost x x')
    {j : ℕ} (hj : 1 ≤ j) (hjk : j ≤ k) {x y : Torus d (N₀ * L ^ k)} (hx : x ∈ G.layer j)
    (h : jBlock d L N₀ k j y = jBlock d L N₀ k j x) : vn (f y - f x) ≤ 2 * d * A := by
  have hy : y ∈ G.layer j := (G.mem_layer_iff hj hjk h).2 hx
  obtain ⟨c, hc, hcb, t, ht, hp⟩ := G.pathCost_corner_le hj hjk hx
  obtain ⟨c', hc', hcb', t', ht', hp'⟩ := G.pathCost_corner_le hj hjk hy
  have hcc : c = c' := GeneratingSet.corner_eq hjk hc hc' (hcb.trans (h.symm.trans hcb'.symm))
  subst hcc
  have h1 := vn_sub_le_of_pathCost f hf hp
  have h2 := vn_sub_le_of_pathCost f hf hp'
  have h3 := vn_triangle (f y) (f c) (f x)
  rw [vn_sub_comm (f y) (f c)] at h3
  have h4 : A * t ≤ A * d := mul_le_mul_of_nonneg_left ht hA
  have h5 : A * t' ≤ A * d := mul_le_mul_of_nonneg_left ht' hA
  nlinarith

end Paths

/-! ### The hypotheses on the field `φ'` -/

section Bounds

variable {G : GeneratingSet d L N₀ k ϱ} {G' : GeneratingSet d L N₀ k ϱ'} {θ : ℝ}

/-- The extension `φ̄'` of `φ'` by `Ψ'`, as a vector field on the torus. -/
noncomputable def barVec (G' : GeneratingSet d L N₀ k ϱ') (Ψ' : Torus d (N₀ * L ^ k) → Fin N → ℂ)
    (φ' : G'.Ω 1 × Fin N → ℂ) : Torus d (N₀ * L ^ k) → Fin N → ℂ :=
  fun y i => barField G' Ψ' φ' y i

/-- The composed field `Ψ` of (6.2) as a vector field. -/
noncomputable def compVec (G : GeneratingSet d L N₀ k ϱ) (G' : GeneratingSet d L N₀ k ϱ')
    (a : ℕ → ℝ) (φ' : G'.Ω 1 × Fin N → ℂ) (Ψ' : Torus d (N₀ * L ^ k) → Fin N → ℂ) :
    Torus d (N₀ * L ^ k) → Fin N → ℂ :=
  fun x i => composeField G G' a φ' Ψ' x i

/-- The block mean of a vector field over the block of its layer. -/
noncomputable def meanVec (G : GeneratingSet d L N₀ k ϱ) (F : Torus d (N₀ * L ^ k) → Fin N → ℂ)
    (x : Torus d (N₀ * L ^ k)) : Fin N → ℂ :=
  fun i => blockMean G (G.layerIndex x) (fun y => F y i) x

/-- **The hypotheses on `φ'`** (the bounds of Theorem 5.2 (3), for the solution of (EL) of
`𝔹'_k`, taken as hypotheses: this is a statement about any such field): `|φ' - Q*Ψ'|₀ ≤ η`,
`|∂φ̄'|₁, |Δφ̄'|₂ ≤ η` (`IsSmoothField`, with `ℓ'` the spacing of `𝔹'_k`) and `φ' · φ' = 1`. -/
structure FieldBounds (G' : GeneratingSet d L N₀ k ϱ') (η : ℝ)
    (Ψ' : Torus d (N₀ * L ^ k) → Fin N → ℂ) (φ' : G'.Ω 1 × Fin N → ℂ) : Prop where
  close : ∀ z : G'.Ω 1, vn (fun i => φ' (z, i) - Ψ' z i) ≤ η
  smooth : IsSmoothField G' η (barVec G' Ψ' φ')
  unit : ∀ z : G'.Ω 1, ∑ i, φ' (z, i) * φ' (z, i) = 1

/-- The scale gap `ℓ(x) ≤ θ ℓ'(x)` on `Ω₁` (`θ = 1` for `𝔹_j ≺ 𝔹'_k`). -/
def ScaleGap (G : GeneratingSet d L N₀ k ϱ) (G' : GeneratingSet d L N₀ k ϱ') (θ : ℝ) : Prop :=
  ∀ x ∈ G.Ω 1, G.spacing x ≤ θ * G'.spacing x

theorem scaleGap_one (h : Precedes G G') : ScaleGap G G' 1 := by
  intro x hx
  have hL : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  unfold GeneratingSet.spacing
  rw [one_mul]
  exact pow_le_pow_right₀ hL (h.layerIndex_le hx)

theorem barVec_of_mem (Ψ' : Torus d (N₀ * L ^ k) → Fin N → ℂ) (φ' : G'.Ω 1 × Fin N → ℂ)
    {z : Torus d (N₀ * L ^ k)} (hz : z ∈ G'.Ω 1) (i : Fin N) :
    barVec G' Ψ' φ' z i = φ' (⟨z, hz⟩, i) := by
  simp [barVec, barField, hz]

theorem svec_of_mem' (φ' : G'.Ω 1 × Fin N → ℂ) {z : Torus d (N₀ * L ^ k)} (hz : z ∈ G'.Ω 1)
    (i : Fin N) : svec G' φ' z i = φ' (⟨z, hz⟩, i) := by
  simp [svec, zeroExt, hz]

theorem barVec_of_not_mem (Ψ' : Torus d (N₀ * L ^ k) → Fin N → ℂ) (φ' : G'.Ω 1 × Fin N → ℂ)
    {z : Torus d (N₀ * L ^ k)} (hz : z ∉ G'.Ω 1) (i : Fin N) :
    barVec G' Ψ' φ' z i = Ψ' z i := by
  simp [barVec, barField, hz]

theorem bondCost_le_of_gap (hg : ScaleGap G G' θ) (hθ : 0 < θ) {x x' : Torus d (N₀ * L ^ k)}
    (hx : x ∈ G.Ω 1) (hx' : x' ∈ G.Ω 1) :
    G'.bondCost x x' ≤ θ * G.bondCost x x' := by
  unfold GeneratingSet.bondCost
  have hs1 : (1 : ℝ) ≤ G.spacing x := G.spacing_ge_one x
  have hM : 0 < max (G.spacing x) (G.spacing x') := lt_of_lt_of_le one_pos
    (hs1.trans (le_max_left _ _))
  have hM' : 0 < max (G'.spacing x) (G'.spacing x') := lt_of_lt_of_le one_pos
    ((G'.spacing_ge_one x).trans (le_max_left _ _))
  have hle : max (G.spacing x) (G.spacing x') ≤ θ * max (G'.spacing x) (G'.spacing x') := by
    refine max_le ?_ ?_
    · exact (hg x hx).trans (mul_le_mul_of_nonneg_left (le_max_left _ _) hθ.le)
    · exact (hg x' hx').trans (mul_le_mul_of_nonneg_left (le_max_right _ _) hθ.le)
  rw [mul_one_div, div_le_div_iff₀ hM' hM]
  linarith

/-- The bond bound `|∂φ̄'| ≤ θ η / ℓ(b)` on bonds inside `Ω₁`. -/
theorem FieldBounds.bond {η θ : ℝ} {Ψ' : Torus d (N₀ * L ^ k) → Fin N → ℂ}
    {φ' : G'.Ω 1 × Fin N → ℂ} (hb : FieldBounds G' η Ψ' φ') (h : Precedes G G')
    (hθ : 0 < θ) (hg : ScaleGap G G' θ) (hη : 0 ≤ η) {x x' : Torus d (N₀ * L ^ k)}
    (hx : x ∈ G.Ω 1) (hx' : x' ∈ G.Ω 1) (hadj : Adj x x') :
    vn (barVec G' Ψ' φ' x' - barVec G' Ψ' φ' x) ≤ (θ * η) * G.bondCost x x' := by
  have h1 := hb.smooth.adj_bound (h.mem_Ω1 hx) (h.mem_Ω1 hx') hadj
  have h2 := bondCost_le_of_gap hg hθ hx hx'
  calc _ ≤ η * G'.bondCost x x' := h1
    _ ≤ η * (θ * G.bondCost x x') := mul_le_mul_of_nonneg_left h2 hη
    _ = _ := by ring

end Bounds

/-! ### The composed field against the extension `φ̄'` -/

section Compose

variable {G : GeneratingSet d L N₀ k ϱ} {G' : GeneratingSet d L N₀ k ϱ'} {θ η : ℝ}
  {a : ℕ → ℝ} {Ψ' : Torus d (N₀ * L ^ k) → Fin N → ℂ} {φ' : G'.Ω 1 × Fin N → ℂ}

/-- The common hypotheses of the estimates: `𝔹_j ≺ 𝔹'_k`, the scale gap `θ`, the weights
`a_p / a_n ∈ [0, 1]` (for `n ≤ p`, `n ≥ 1`), `Ψ'` constant on the blocks of `𝔹'_k`, and the
bounds of Theorem 5.2 (3) of size `η`. -/
structure CompHyp (G : GeneratingSet d L N₀ k ϱ) (G' : GeneratingSet d L N₀ k ϱ') (a : ℕ → ℝ)
    (θ η : ℝ) (Ψ' : Torus d (N₀ * L ^ k) → Fin N → ℂ) (φ' : G'.Ω 1 × Fin N → ℂ) : Prop where
  prec : Precedes G G'
  θ_pos : 0 < θ
  η_nn : 0 ≤ η
  gap : ScaleGap G G' θ
  ratio : ∀ x ∈ G.Ω 1, 0 ≤ a (G'.layerIndex x) / a (G.layerIndex x) ∧
    a (G'.layerIndex x) / a (G.layerIndex x) ≤ 1
  layerConst : IsLayerConstant G' Ψ'
  bounds : FieldBounds G' η Ψ' φ'

theorem blockSet_of_mem (G : GeneratingSet d L N₀ k ϱ) {x : Torus d (N₀ * L ^ k)}
    (hx : x ∈ G.Ω 1) : blockSet G x = G.blk (G.layerIndex x) x := by
  classical
  simp [blockSet, hx]

theorem blockSet_of_not_mem (G : GeneratingSet d L N₀ k ϱ) {x : Torus d (N₀ * L ^ k)}
    (hx : x ∉ G.Ω 1) : blockSet G x = {x} := by
  classical
  simp [blockSet, hx]

theorem blk_mem_layer {x y : Torus d (N₀ * L ^ k)} (hx : x ∈ G.Ω 1)
    (hy : y ∈ G.blk (G.layerIndex x) x) : y ∈ G.layer (G.layerIndex x) := by
  obtain ⟨hn1, hnk, hxn⟩ := G.layerIndex_spec hx
  exact (G.mem_layer_iff hn1 hnk (GeneratingSet.mem_blk.1 hy)).2 hxn

theorem blockSet_subset_dataSites {x z : Torus d (N₀ * L ^ k)} (hx : x ∈ dataSites G)
    (hz : z ∈ blockSet G x) : z ∈ dataSites G := by
  rcases (mem_dataSites G).1 hx with hx | hx
  · rw [blockSet_of_mem G hx] at hz
    have h1 := (G.layer_subset (G.layerIndex_spec hx).1 (G.layerIndex_spec hx).2.1)
      (blk_mem_layer hx hz)
    exact (mem_dataSites G).2 (Or.inl h1)
  · have hn : x ∉ G.Ω 1 := ((mem_collar G).1 hx).1
    rw [blockSet_of_not_mem G hn, Finset.mem_singleton] at hz
    rw [hz]; exact (mem_dataSites G).2 (Or.inr hx)

/-- `y ∈ B_n(x)` is in `Ω₁` and in `Ω'₁`. -/
theorem blk_mem_Ω1' (h : Precedes G G') {x y : Torus d (N₀ * L ^ k)} (hx : x ∈ G.Ω 1)
    (hy : y ∈ G.blk (G.layerIndex x) x) : y ∈ G.Ω 1 ∧ y ∈ G'.Ω 1 := by
  have h1 := (G.layer_subset (G.layerIndex_spec hx).1 (G.layerIndex_spec hx).2.1)
    (blk_mem_layer hx hy)
  exact ⟨h1, h.mem_Ω1 h1⟩

/-- Within a block of `𝔹_j`, the extension `φ̄'` oscillates by at most `2 d θ η`. -/
theorem CompHyp.osc (H : CompHyp G G' a θ η Ψ' φ') {x y y' : Torus d (N₀ * L ^ k)}
    (hx : x ∈ G.Ω 1) (hy : y ∈ G.blk (G.layerIndex x) x) (hy' : y' ∈ G.blk (G.layerIndex x) x) :
    vn (barVec G' Ψ' φ' y - barVec G' Ψ' φ' y') ≤ 2 * d * (θ * η) := by
  obtain ⟨hn1, hnk, -⟩ := G.layerIndex_spec hx
  have hy'l := blk_mem_layer hx hy'
  refine vn_block_osc (barVec G' Ψ' φ') (mul_nonneg H.θ_pos.le H.η_nn)
    (fun u u' hu hu' hadj => H.bounds.bond H.prec H.θ_pos H.gap H.η_nn hu hu' hadj) hn1 hnk
    hy'l ?_
  rw [GeneratingSet.mem_blk.1 hy, GeneratingSet.mem_blk.1 hy']

/-- The block mean is within `2 d θ η` of the values of `φ̄'` in the block. -/
theorem CompHyp.mean_sub_bar (H : CompHyp G G' a θ η Ψ' φ') {x y : Torus d (N₀ * L ^ k)}
    (hx : x ∈ G.Ω 1) (hy : y ∈ G.blk (G.layerIndex x) x) :
    vn (meanVec G (barVec G' Ψ' φ') x - barVec G' Ψ' φ' y) ≤ 2 * d * (θ * η) := by
  obtain ⟨-, hnk, -⟩ := G.layerIndex_spec hx
  exact vn_blockMean_sub_le (G := G) hnk (barVec G' Ψ' φ') x (barVec G' Ψ' φ' y)
    (fun y' hy' => H.osc hx hy' hy)

/-- The residual `Ψ'(x) - (Q_p φ')(x)` of (6.2) is at most `η`. -/
theorem CompHyp.resid_le (H : CompHyp G G' a θ η Ψ' φ') {x : Torus d (N₀ * L ^ k)}
    (hx : x ∈ G'.Ω 1) :
    vn (fun i => Ψ' x i - blockMean G' (G'.layerIndex x) (fun y => svec G' φ' y i) x) ≤ η := by
  obtain ⟨hp1, hpk, hxp⟩ := G'.layerIndex_spec hx
  have hc : ∀ y ∈ G'.blk (G'.layerIndex x) x,
      vn (fun i => svec G' φ' y i - Ψ' x i) ≤ η := by
    intro y hy
    have hyl : y ∈ G'.layer (G'.layerIndex x) :=
      (G'.mem_layer_iff hp1 hpk (GeneratingSet.mem_blk.1 hy)).2 hxp
    have hy1 : y ∈ G'.Ω 1 := G'.layer_subset hp1 hpk hyl
    have e : ∀ i, svec G' φ' y i - Ψ' x i = φ' (⟨y, hy1⟩, i) - Ψ' y i := fun i => by
      rw [svec_of_mem' φ' hy1, H.layerConst _ hp1 hpk x hxp y hy]
    simp only [e]
    exact H.bounds.close ⟨y, hy1⟩
  have h := vn_blockMean_sub_le (G := G') hpk (svec G' φ') x (Ψ' x) hc
  exact (vn_sub_comm (fun i => Ψ' x i) (fun i => blockMean G' (G'.layerIndex x)
    (fun y => svec G' φ' y i) x)).trans_le h

/-- The coefficient `κ = (a_p / a_n) L^{2(n-p)}` of (6.2) at a site. -/
noncomputable def kap (G : GeneratingSet d L N₀ k ϱ) (G' : GeneratingSet d L N₀ k ϱ')
    (a : ℕ → ℝ) (x : Torus d (N₀ * L ^ k)) : ℝ :=
  a (G'.layerIndex x) / a (G.layerIndex x) *
    (((L : ℝ) ^ G.layerIndex x) ^ 2 / ((L : ℝ) ^ G'.layerIndex x) ^ 2)

theorem CompHyp.kap_bounds (H : CompHyp G G' a θ η Ψ' φ') {x : Torus d (N₀ * L ^ k)}
    (hx : x ∈ G.Ω 1) : 0 ≤ kap G G' a x ∧ kap G G' a x ≤ θ ^ 2 := by
  obtain ⟨r0, r1⟩ := H.ratio x hx
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hq0 : 0 ≤ ((L : ℝ) ^ G.layerIndex x) ^ 2 / ((L : ℝ) ^ G'.layerIndex x) ^ 2 := by positivity
  have hq1 : ((L : ℝ) ^ G.layerIndex x) ^ 2 / ((L : ℝ) ^ G'.layerIndex x) ^ 2 ≤ θ ^ 2 := by
    rw [div_le_iff₀ (by positivity)]
    have hg := H.gap x hx
    unfold GeneratingSet.spacing at hg
    have h0 : (0 : ℝ) ≤ (L : ℝ) ^ G.layerIndex x := by positivity
    calc ((L : ℝ) ^ G.layerIndex x) ^ 2 ≤ (θ * (L : ℝ) ^ G'.layerIndex x) ^ 2 :=
          pow_le_pow_left₀ h0 hg 2
      _ = _ := by ring
  unfold kap
  exact ⟨mul_nonneg r0 hq0, (mul_le_of_le_one_left hq0 r1).trans hq1⟩

theorem blockMean_svec_eq_bar (Ψ' : Torus d (N₀ * L ^ k) → Fin N → ℂ) (φ' : G'.Ω 1 × Fin N → ℂ)
    (n : ℕ) (x : Torus d (N₀ * L ^ k)) (hsub : ∀ y ∈ G.blk n x, y ∈ G'.Ω 1) (i : Fin N) :
    blockMean G n (fun y => svec G' φ' y i) x = blockMean G n (fun y => barVec G' Ψ' φ' y i) x := by
  unfold blockMean
  congr 1
  refine Finset.sum_congr rfl fun y hy => ?_
  show svec G' φ' y i = barVec G' Ψ' φ' y i
  rw [svec_of_mem' φ' (hsub y hy), barVec_of_mem Ψ' φ' (hsub y hy)]

theorem CompHyp.compVec_eq (H : CompHyp G G' a θ η Ψ' φ') {x : Torus d (N₀ * L ^ k)}
    (hx : x ∈ G.Ω 1) (i : Fin N) :
    compVec G G' a φ' Ψ' x i = meanVec G (barVec G' Ψ' φ') x i + (kap G G' a x : ℂ) *
      (Ψ' x i - blockMean G' (G'.layerIndex x) (fun y => svec G' φ' y i) x) := by
  unfold compVec meanVec
  rw [composeField_of_mem a φ' Ψ' hx i,
    blockMean_svec_eq_bar Ψ' φ' _ x (fun y hy => (blk_mem_Ω1' H.prec hx hy).2) i]
  rfl

/-- **(E1)**: `|Ψ - Q_n φ'| ≤ κ η ≤ θ² η`. -/
theorem CompHyp.compVec_sub_mean (H : CompHyp G G' a θ η Ψ' φ') {x : Torus d (N₀ * L ^ k)}
    (hx : x ∈ G.Ω 1) :
    vn (compVec G G' a φ' Ψ' x - meanVec G (barVec G' Ψ' φ') x) ≤ θ ^ 2 * η := by
  obtain ⟨k0, k1⟩ := H.kap_bounds hx
  have hres := H.resid_le (H.prec.mem_Ω1 hx)
  have e : compVec G G' a φ' Ψ' x - meanVec G (barVec G' Ψ' φ') x = fun i => (kap G G' a x : ℂ) *
      (Ψ' x i - blockMean G' (G'.layerIndex x) (fun y => svec G' φ' y i) x) := by
    funext i
    simp only [Pi.sub_apply, H.compVec_eq hx i]
    ring
  rw [e, vn_smul_real, abs_of_nonneg k0]
  calc _ ≤ kap G G' a x * η := mul_le_mul_of_nonneg_left hres k0
    _ ≤ θ ^ 2 * η := mul_le_mul_of_nonneg_right k1 H.η_nn

/-- The composed field against the extension `φ̄'` at the sites of the block of `x`
(P2 (4.24), (4.26)): `|Ψ(x) - φ̄'(y)| ≤ (2 d + θ) θ η`. -/
theorem CompHyp.compVec_sub_bar (H : CompHyp G G' a θ η Ψ' φ') {x y : Torus d (N₀ * L ^ k)}
    (hx : x ∈ dataSites G) (hy : y ∈ blockSet G x) :
    vn (compVec G G' a φ' Ψ' x - barVec G' Ψ' φ' y) ≤ (2 * d + θ) * (θ * η) := by
  rcases (mem_dataSites G).1 hx with hx | hx
  · rw [blockSet_of_mem G hx] at hy
    have h1 := H.compVec_sub_mean hx
    have h2 := H.mean_sub_bar hx hy
    have h3 := vn_triangle (compVec G G' a φ' Ψ' x) (meanVec G (barVec G' Ψ' φ') x)
      (barVec G' Ψ' φ' y)
    nlinarith [mul_nonneg H.θ_pos.le H.η_nn]
  · have hn : x ∉ G.Ω 1 := ((mem_collar G).1 hx).1
    rw [blockSet_of_not_mem G hn, Finset.mem_singleton] at hy
    subst hy
    have : compVec G G' a φ' Ψ' y - barVec G' Ψ' φ' y = 0 := by
      funext i
      simp [compVec, barVec, composeField_of_collar a φ' Ψ' hx i]
    rw [this, vn_zero]
    have := mul_nonneg H.θ_pos.le H.η_nn
    have h2 : (0 : ℝ) ≤ 2 * d + θ := by have := H.θ_pos; positivity
    positivity

/-- The interface estimate (R1): for blocks `y ∋ x`, `y' ∋ x'` of `𝔹_j` with adjacent sites
`z ∈ y`, `z' ∈ y'`, `|Ψ(x) - Ψ(x')| ≤ 2 (2d + θ) θ η + |φ̄'(z) - φ̄'(z')|`. -/
theorem CompHyp.interface (H : CompHyp G G' a θ η Ψ' φ') {x x' : Torus d (N₀ * L ^ k)}
    (hxx' : IsInterfacePair G x x') {B : ℝ}
    (hB : ∀ z z', z ∈ dataSites G → z' ∈ dataSites G → Adj z z' →
      vn (barVec G' Ψ' φ' z - barVec G' Ψ' φ' z') ≤ B) :
    vn (compVec G G' a φ' Ψ' x - compVec G G' a φ' Ψ' x') ≤ 2 * ((2 * d + θ) * (θ * η)) + B := by
  obtain ⟨hx, hx', -, z, hz, z', hz', hadj⟩ := hxx'
  have h1 := H.compVec_sub_bar hx hz
  have h2 := H.compVec_sub_bar hx' hz'
  have h3 := hB z z' (blockSet_subset_dataSites hx hz) (blockSet_subset_dataSites hx' hz') hadj
  have t1 := vn_triangle (compVec G G' a φ' Ψ' x) (barVec G' Ψ' φ' z) (compVec G G' a φ' Ψ' x')
  have t2 := vn_triangle (barVec G' Ψ' φ' z) (barVec G' Ψ' φ' z') (compVec G G' a φ' Ψ' x')
  rw [vn_sub_comm (barVec G' Ψ' φ' z') (compVec G G' a φ' Ψ' x')] at t2
  linarith

/-- **The bilinear estimate for a block mean**: if `F · F = 1` on a block and `F` is within `osc` of
its mean there, then `m · m - 1` is of second order, `|m · m - 1| ≤ osc²`
(`m · m - 1 = -avg (F - m) · (F - m)`). -/
theorem mean_dot_sub_one {n : ℕ} (hn : n ≤ k) (F : Torus d (N₀ * L ^ k) → Fin N → ℂ)
    (x : Torus d (N₀ * L ^ k)) {osc : ℝ}
    (hunit : ∀ y ∈ G.blk n x, ∑ i, F y i * F y i = 1)
    (hosc : ∀ y ∈ G.blk n x,
      vn (fun i => F y i - blockMean G n (fun y => F y i) x) ≤ osc) :
    ‖∑ i, blockMean G n (fun y => F y i) x * blockMean G n (fun y => F y i) x - 1‖ ≤ osc ^ 2 := by
  classical
  set S := G.blk n x with hS
  set m : Fin N → ℂ := fun i => blockMean G n (fun y => F y i) x with hm
  have hcard := card_blk_cast G n hn x
  have hLpos : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hcpos : (0 : ℝ) < S.card := by rw [hS, hcard]; positivity
  have hKc : (S.card : ℂ) * ((((((L : ℝ) ^ n) ^ d)⁻¹ : ℝ)) : ℂ) = 1 := by
    have : (S.card : ℝ) * ((((L : ℝ) ^ n) ^ d)⁻¹) = 1 := by
      rw [hS, hcard]; field_simp
    exact_mod_cast this
  have hsum0 : ∀ i, ∑ y ∈ S, (F y i - m i) = 0 := by
    intro i
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    have : m i = ((((((L : ℝ) ^ n) ^ d)⁻¹ : ℝ)) : ℂ) * ∑ y ∈ S, F y i := rfl
    rw [this]
    linear_combination (-(∑ y ∈ S, F y i)) * hKc
  have hexp : ∀ y ∈ S, ∑ i, F y i * F y i = ∑ i, m i * m i +
      2 * ∑ i, m i * (F y i - m i) + ∑ i, (F y i - m i) * (F y i - m i) := by
    intro y _
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => by ring
  have htot : (S.card : ℂ) = (S.card : ℂ) * ∑ i, m i * m i +
      ∑ y ∈ S, ∑ i, (F y i - m i) * (F y i - m i) := by
    have h1 : ∑ y ∈ S, ∑ i, F y i * F y i = (S.card : ℂ) := by
      rw [Finset.sum_congr rfl hunit, Finset.sum_const, nsmul_eq_mul, mul_one]
    have h2 : ∑ y ∈ S, ∑ i, F y i * F y i = ∑ y ∈ S, (∑ i, m i * m i +
        2 * ∑ i, m i * (F y i - m i) + ∑ i, (F y i - m i) * (F y i - m i)) :=
      Finset.sum_congr rfl hexp
    rw [h2, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
      ← Finset.mul_sum] at h1
    have h3 : ∑ y ∈ S, ∑ i, m i * (F y i - m i) = 0 := by
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [← Finset.mul_sum, hsum0 i, mul_zero]
    rw [h3] at h1
    linear_combination (-1 : ℂ) * h1
  set U := ∑ y ∈ S, ∑ i, (F y i - m i) * (F y i - m i) with hU
  have hUb : ‖U‖ ≤ S.card * osc ^ 2 := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ y ∈ S, ‖∑ i, (F y i - m i) * (F y i - m i)‖ ≤ ∑ _y ∈ S, osc ^ 2 := by
          refine Finset.sum_le_sum fun y hy => ?_
          have h1 := norm_dot_le (fun i => F y i - m i) (fun i => F y i - m i)
          have h2 := hosc y hy
          have h3 := vn_nonneg (fun i => F y i - m i)
          calc _ ≤ vn (fun i => F y i - m i) * vn (fun i => F y i - m i) := h1
            _ ≤ osc * osc := mul_le_mul h2 h2 h3 (h3.trans h2)
            _ = osc ^ 2 := by ring
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  have hkey : (S.card : ℂ) * (∑ i, m i * m i - 1) = -U := by
    linear_combination (-1 : ℂ) * htot
  have hnorm : (S.card : ℝ) * ‖∑ i, m i * m i - 1‖ = ‖U‖ := by
    have := congrArg norm hkey
    rw [norm_mul, norm_neg, Complex.norm_natCast] at this
    exact this
  have : (S.card : ℝ) * ‖∑ i, m i * m i - 1‖ ≤ (S.card : ℝ) * osc ^ 2 := by
    rw [hnorm]; exact hUb
  exact le_of_mul_le_mul_left this hcpos

/-- **The bilinear estimate for the composed field**:
`|Ψ · Ψ - 1| ≤ (2dθη)² + 2θ² M η + θ⁴ η²`, `M` a bound for `|φ̄'|` on the block. -/
theorem CompHyp.dot_sub_one (H : CompHyp G G' a θ η Ψ' φ') {x : Torus d (N₀ * L ^ k)}
    (hx : x ∈ G.Ω 1) {M : ℝ}
    (hM : ∀ y ∈ G.blk (G.layerIndex x) x, vn (barVec G' Ψ' φ' y) ≤ M) :
    ‖∑ i, compVec G G' a φ' Ψ' x i * compVec G G' a φ' Ψ' x i - 1‖ ≤
      (2 * d * (θ * η)) ^ 2 + 2 * θ ^ 2 * M * η + (θ ^ 2) ^ 2 * η ^ 2 := by
  obtain ⟨-, hnk, -⟩ := G.layerIndex_spec hx
  obtain ⟨k0, k1⟩ := H.kap_bounds hx
  have hres := H.resid_le (H.prec.mem_Ω1 hx)
  have hM0 : 0 ≤ M := (vn_nonneg _).trans (hM x (x_mem_blk _ x))
  have hmM : vn (meanVec G (barVec G' Ψ' φ') x) ≤ M := vn_blockMean_le hnk _ x hM
  have h1 := mean_dot_sub_one (G := G) hnk (barVec G' Ψ' φ') x (osc := 2 * d * (θ * η))
    (fun y hy => by
      have hy' := (blk_mem_Ω1' H.prec hx hy).2
      simp only [barVec_of_mem Ψ' φ' hy']
      exact H.bounds.unit ⟨y, hy'⟩)
    (fun y hy => by
      have := H.mean_sub_bar hx hy
      rw [vn_sub_comm] at this
      exact this)
  set m := meanVec G (barVec G' Ψ' φ') x with hm
  set ρ : Fin N → ℂ := fun i => Ψ' x i - blockMean G' (G'.layerIndex x) (fun y => svec G' φ' y i) x
    with hρ
  set κ := kap G G' a x with hκ
  have hc : ∀ i, compVec G G' a φ' Ψ' x i = m i + (κ : ℂ) * ρ i := fun i => H.compVec_eq hx i
  have e : ∑ i, compVec G G' a φ' Ψ' x i * compVec G G' a φ' Ψ' x i - 1 =
      (∑ i, m i * m i - 1) + 2 * (κ : ℂ) * ∑ i, m i * ρ i + (κ : ℂ) ^ 2 * ∑ i, ρ i * ρ i := by
    have e1 : ∀ i, compVec G G' a φ' Ψ' x i * compVec G G' a φ' Ψ' x i =
        m i * m i + 2 * (κ : ℂ) * (m i * ρ i) + (κ : ℂ) ^ 2 * (ρ i * ρ i) := by
      intro i; rw [hc i]; ring
    simp only [e1]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    ring
  have hρn : vn ρ ≤ η := hres
  have hmρ : ‖∑ i, m i * ρ i‖ ≤ M * η := by
    refine (norm_dot_le m ρ).trans ?_
    exact mul_le_mul hmM hρn (vn_nonneg _) hM0
  have hρρ : ‖∑ i, ρ i * ρ i‖ ≤ η ^ 2 := by
    refine (norm_dot_le ρ ρ).trans ?_
    calc vn ρ * vn ρ ≤ η * η := mul_le_mul hρn hρn (vn_nonneg _) H.η_nn
      _ = η ^ 2 := by ring
  rw [e]
  have hκn : ‖(κ : ℂ)‖ = κ := by rw [Complex.norm_real, Real.norm_of_nonneg k0]
  have h1' : ‖∑ i, m i * m i - 1‖ ≤ (2 * d * (θ * η)) ^ 2 := h1
  refine norm_add₃_le.trans ?_
  have b2 : ‖2 * (κ : ℂ) * ∑ i, m i * ρ i‖ ≤ 2 * θ ^ 2 * M * η := by
    rw [norm_mul, norm_mul, hκn]
    have : ‖(2 : ℂ)‖ = 2 := by simp
    rw [this]
    calc 2 * κ * ‖∑ i, m i * ρ i‖ ≤ 2 * θ ^ 2 * (M * η) := by
          refine mul_le_mul (by linarith) hmρ (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have b3 : ‖(κ : ℂ) ^ 2 * ∑ i, ρ i * ρ i‖ ≤ (θ ^ 2) ^ 2 * η ^ 2 := by
    rw [norm_mul, norm_pow, hκn]
    exact mul_le_mul (pow_le_pow_left₀ k0 k1 2) hρρ (norm_nonneg _) (by positivity)
  linarith

/-- A bond at a site of `Ω'₁` (to any neighbour, also to the collar): `|∂φ̄'| ≤ η`. -/
theorem _root_.Balaban.Multiscale.IsSmoothField.adj_grad {G : GeneratingSet d L N₀ k ϱ} {δ : ℝ}
    {φ : Torus d (N₀ * L ^ k) → Fin N → ℂ} (hφ : IsSmoothField G δ φ)
    {x x' : Torus d (N₀ * L ^ k)} (hx : x ∈ G.Ω 1) (hadj : Adj x x') :
    vn (φ x' - φ x) ≤ δ / G.spacing x := by
  obtain ⟨μ, h | h⟩ := hadj
  · rw [h]; exact (hφ.grad x hx μ).1
  · have := (hφ.grad x hx μ).2
    have e : x - Pi.single μ 1 = x' := by rw [h]; simp
    rwa [e] at this

theorem CompHyp.bond_out (H : CompHyp G G' a θ η Ψ' φ') {z z' : Torus d (N₀ * L ^ k)}
    (hz : z ∈ G'.Ω 1) (hadj : Adj z z') :
    vn (barVec G' Ψ' φ' z' - barVec G' Ψ' φ' z) ≤ η := by
  have h := H.bounds.smooth.adj_grad hz hadj
  have h1 : (1 : ℝ) ≤ G'.spacing z := G'.spacing_ge_one z
  have : η / G'.spacing z ≤ η := div_le_self H.η_nn h1
  exact h.trans this

/-! ### Differences of two composed fields (Lemma 6.3, (R-S) complex part) -/

theorem vn_add' (u w : Fin N → ℂ) : vn (fun i => u i + w i) ≤ vn u + vn w := vn_add u w

theorem blk_subset_blk' (h : Precedes G G') {x y : Torus d (N₀ * L ^ k)} (hx : x ∈ G.Ω 1)
    (hy : y ∈ G.blk (G.layerIndex x) x) : y ∈ G'.blk (G'.layerIndex x) x := by
  obtain ⟨-, hpk, -⟩ := G'.layerIndex_spec (h.mem_Ω1 hx)
  exact GeneratingSet.mem_blk.2 (jBlock_eq_of_le (h.layerIndex_le hx) hpk
    (GeneratingSet.mem_blk.1 hy))

/-- **Linear structure of the difference**: for two fields `(Ψc, φc)`, `(Ψr, φr)`,
`Ψ_c - Ψ_r = Q_n Δφ + κ (ΔΨ' - Q_p Δφ)`. -/
theorem compVec_sub_eq {Ψc Ψr : Torus d (N₀ * L ^ k) → Fin N → ℂ} {φc φr : G'.Ω 1 × Fin N → ℂ}
    (a : ℕ → ℝ) (h : Precedes G G') {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.Ω 1) (i : Fin N) :
    compVec G G' a φc Ψc x i - compVec G G' a φr Ψr x i =
      blockMean G (G.layerIndex x) (fun y => barVec G' Ψc φc y i - barVec G' Ψr φr y i) x +
        (kap G G' a x : ℂ) * ((Ψc x i - Ψr x i) -
          blockMean G' (G'.layerIndex x) (fun y => barVec G' Ψc φc y i - barVec G' Ψr φr y i) x) := by
  obtain ⟨hp1, hpk, hxp⟩ := G'.layerIndex_spec (h.mem_Ω1 hx)
  have hsub : ∀ y ∈ G'.blk (G'.layerIndex x) x, y ∈ G'.Ω 1 := fun y hy =>
    G'.layer_subset hp1 hpk ((G'.mem_layer_iff hp1 hpk (GeneratingSet.mem_blk.1 hy)).2 hxp)
  have hsubG : ∀ y ∈ G.blk (G.layerIndex x) x, y ∈ G'.Ω 1 := fun y hy =>
    (blk_mem_Ω1' h hx hy).2
  unfold compVec
  rw [composeField_of_mem a φc Ψc hx i, composeField_of_mem a φr Ψr hx i,
    blockMean_svec_eq_bar (G := G) Ψc φc _ x hsubG i, blockMean_svec_eq_bar (G := G) Ψr φr _ x hsubG i,
    blockMean_svec_eq_bar (G := G') Ψc φc _ x hsub i, blockMean_svec_eq_bar (G := G') Ψr φr _ x hsub i,
    blockMean_sub, blockMean_sub]
  unfold kap
  push_cast
  ring

/-- The bonds of `φ̄'_c - φ̄'_r` inside `Ω'₁`. -/
theorem FieldBounds.bond_sub {Ψc Ψr : Torus d (N₀ * L ^ k) → Fin N → ℂ}
    {φc φr : G'.Ω 1 × Fin N → ℂ} {η : ℝ} (hc : FieldBounds G' η Ψc φc)
    (hr : FieldBounds G' η Ψr φr) {x x' : Torus d (N₀ * L ^ k)} (hx : x ∈ G'.Ω 1)
    (hx' : x' ∈ G'.Ω 1) (hadj : Adj x x') :
    vn (barVec G' Ψc φc x' - barVec G' Ψr φr x' -
        (barVec G' Ψc φc x - barVec G' Ψr φr x)) ≤ (η + η) * G'.bondCost x x' := by
  have h1 := hc.smooth.adj_bound hx hx' hadj
  have h2 := hr.smooth.adj_bound hx hx' hadj
  have e : barVec G' Ψc φc x' - barVec G' Ψr φr x' - (barVec G' Ψc φc x - barVec G' Ψr φr x) =
      (fun i => (barVec G' Ψc φc x' - barVec G' Ψc φc x) i -
        (barVec G' Ψr φr x' - barVec G' Ψr φr x) i) := by
    funext i; simp only [Pi.sub_apply]; ring
  rw [e]
  refine (vn_sub_le' _ _).trans ?_
  nlinarith

/-- The difference `φ̄'_c - φ̄'_r` of two extensions. -/
noncomputable def diffBar (G' : GeneratingSet d L N₀ k ϱ') (Ψc Ψr : Torus d (N₀ * L ^ k) → Fin N → ℂ)
    (φc φr : G'.Ω 1 × Fin N → ℂ) : Torus d (N₀ * L ^ k) → Fin N → ℂ :=
  fun y i => barVec G' Ψc φc y i - barVec G' Ψr φr y i

/-- **The size of the difference** (the core of Lemma 6.3 (C2) and of (R-S) (C2')):
if `|φc - φr| ≤ AΔ` on `Ω'₁` and `|Ψc - Ψr|(x) ≤ AΔ + e`, then
`|Ψ_c - Ψ_r|(x) ≤ AΔ + θ² (e + 4 d η)`. -/
theorem compVec_sub_bound {Ψc Ψr : Torus d (N₀ * L ^ k) → Fin N → ℂ}
    {φc φr : G'.Ω 1 × Fin N → ℂ} {a : ℕ → ℝ} {θ η : ℝ}
    (Hc : CompHyp G G' a θ η Ψc φc) (Hr : CompHyp G G' a θ η Ψr φr) (hθ1 : θ ≤ 1)
    {AΔ e : ℝ} (hΔ : ∀ z : G'.Ω 1, vn (fun i => φc (z, i) - φr (z, i)) ≤ AΔ) (he : 0 ≤ e)
    {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.Ω 1) (hD : vn (fun i => Ψc x i - Ψr x i) ≤ AΔ + e) :
    vn (compVec G G' a φc Ψc x - compVec G G' a φr Ψr x) ≤ AΔ + θ ^ 2 * (e + 4 * d * η) := by
  have h := Hc.prec
  obtain ⟨hn1, hnk, -⟩ := G.layerIndex_spec hx
  obtain ⟨hp1, hpk, hxp⟩ := G'.layerIndex_spec (h.mem_Ω1 hx)
  obtain ⟨k0, k1⟩ := Hc.kap_bounds hx
  have hκ1 : kap G G' a x ≤ 1 := k1.trans (by nlinarith [Hc.θ_pos])
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ = kap G G' a x := ⟨_, rfl⟩
  rw [← hκ] at k0 k1 hκ1
  obtain ⟨mQ, hmQ⟩ : ∃ m : Fin N → ℂ, m = fun i =>
      blockMean G (G.layerIndex x) (fun y => diffBar G' Ψc Ψr φc φr y i) x := ⟨_, rfl⟩
  obtain ⟨pQ, hpQ⟩ : ∃ m : Fin N → ℂ, m = fun i =>
      blockMean G' (G'.layerIndex x) (fun y => diffBar G' Ψc Ψr φc φr y i) x := ⟨_, rfl⟩
  have hAΔ : 0 ≤ AΔ := (vn_nonneg _).trans (hΔ ⟨x, h.mem_Ω1 hx⟩)
  have hDFb : ∀ y ∈ G'.Ω 1, vn (diffBar G' Ψc Ψr φc φr y) ≤ AΔ := fun y hy => by
    have : diffBar G' Ψc Ψr φc φr y = fun i => φc (⟨y, hy⟩, i) - φr (⟨y, hy⟩, i) := by
      funext i; simp only [diffBar, barVec_of_mem Ψc φc hy, barVec_of_mem Ψr φr hy]
    rw [this]; exact hΔ _
  have hm : vn mQ ≤ AΔ := by
    rw [hmQ]
    exact vn_blockMean_le (G := G) hnk (diffBar G' Ψc Ψr φc φr) x
      (fun y hy => hDFb y (blk_mem_Ω1' h hx hy).2)
  -- oscillation of `diffBar` in the `p`-block of `x`
  have hosc : ∀ y ∈ G'.blk (G'.layerIndex x) x, ∀ y' ∈ G'.blk (G'.layerIndex x) x,
      vn (diffBar G' Ψc Ψr φc φr y' - diffBar G' Ψc Ψr φc φr y) ≤ 2 * d * (η + η) := by
    intro y hy y' hy'
    have hyl : y ∈ G'.layer (G'.layerIndex x) :=
      (G'.mem_layer_iff hp1 hpk (GeneratingSet.mem_blk.1 hy)).2 hxp
    refine vn_block_osc (diffBar G' Ψc Ψr φc φr) (by have := Hc.η_nn; positivity) ?_ hp1 hpk hyl ?_
    · intro u u' hu hu' hadj
      exact Hc.bounds.bond_sub Hr.bounds hu hu' hadj
    · rw [GeneratingSet.mem_blk.1 hy', GeneratingSet.mem_blk.1 hy]
  have hpm : ∀ y ∈ G.blk (G.layerIndex x) x,
      vn (fun i => diffBar G' Ψc Ψr φc φr y i - pQ i) ≤ 2 * d * (η + η) := by
    intro y hy
    have hy' := blk_subset_blk' h hx hy
    have := vn_blockMean_sub_le (G := G') hpk (diffBar G' Ψc Ψr φc φr) x
      (diffBar G' Ψc Ψr φc φr y) (fun y' hy'' => hosc y hy' y' hy'')
    have hpQi : ∀ i, pQ i = blockMean G' (G'.layerIndex x)
        (fun y => diffBar G' Ψc Ψr φc φr y i) x := fun i => by rw [hpQ]
    simp only [← hpQi] at this
    exact (vn_sub_comm (diffBar G' Ψc Ψr φc φr y) pQ).trans_le this
  have hdiff : vn (fun i => mQ i - pQ i) ≤ 2 * d * (η + η) := by
    rw [hmQ]
    have := vn_blockMean_sub_le (G := G) hnk (diffBar G' Ψc Ψr φc φr) x pQ hpm
    exact this
  -- assemble
  have hw : compVec G G' a φc Ψc x - compVec G G' a φr Ψr x = fun i =>
      ((1 - κ : ℝ) : ℂ) * mQ i + (κ : ℂ) * (Ψc x i - Ψr x i) + (κ : ℂ) * (mQ i - pQ i) := by
    funext i
    simp only [Pi.sub_apply]
    have := compVec_sub_eq (φc := φc) (φr := φr) (Ψc := Ψc) (Ψr := Ψr) a h hx i
    simp only [compVec] at this ⊢
    rw [hmQ, hpQ, hκ]
    simp only [diffBar]
    rw [this]
    push_cast
    ring
  rw [hw]
  have t1 : vn (fun i => ((1 - κ : ℝ) : ℂ) * mQ i) ≤ (1 - κ) * AΔ := by
    rw [vn_smul_real, abs_of_nonneg (by linarith)]
    exact mul_le_mul_of_nonneg_left hm (by linarith)
  have t2 : vn (fun i => (κ : ℂ) * (Ψc x i - Ψr x i)) ≤ κ * (AΔ + e) := by
    rw [vn_smul_real, abs_of_nonneg k0]
    exact mul_le_mul_of_nonneg_left hD k0
  have t3 : vn (fun i => (κ : ℂ) * (mQ i - pQ i)) ≤ κ * (2 * d * (η + η)) := by
    rw [vn_smul_real, abs_of_nonneg k0]
    exact mul_le_mul_of_nonneg_left hdiff k0
  have t12 := vn_add' (fun i => ((1 - κ : ℝ) : ℂ) * mQ i) (fun i => (κ : ℂ) * (Ψc x i - Ψr x i))
  have t123 := vn_add' (fun i => ((1 - κ : ℝ) : ℂ) * mQ i + (κ : ℂ) * (Ψc x i - Ψr x i))
    (fun i => (κ : ℂ) * (mQ i - pQ i))
  have hθ2 : κ ≤ θ ^ 2 := k1
  have hη0 := Hc.η_nn
  nlinarith [mul_nonneg hη0 (Nat.cast_nonneg (α := ℝ) d), mul_nonneg he (sub_nonneg.2 hθ2),
    mul_nonneg (mul_nonneg hη0 (Nat.cast_nonneg (α := ℝ) d)) (sub_nonneg.2 hθ2)]

end Compose

end Balaban.Background
