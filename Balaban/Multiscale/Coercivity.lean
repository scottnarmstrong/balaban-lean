/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Multiscale.Operator
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# Multiscale coercivity G-1(a) (GREEN.md §3, §4.1)

For the operator `H_D(α)` of `Balaban/Multiscale/Operator.lean` (fine torus, unit spacing):

`Re ⟨u, H_D(α) u⟩ ≥ c₁ (‖∂ũ‖² + ‖ℓ⁻¹u‖²)` whenever `|α(x)| ≤ c₁ ℓ(x)⁻² / 2`,

with `c₁ = min (1/d) (1/2) / 2` (`Balaban.Multiscale.coerciveConst`), where `‖∂ũ‖²` is the sum over
all bonds of the torus of `|ũ(x + e_μ) - ũ(x)|²` for the zero extension `ũ` (so bonds joining
`Ω₁` to its complement are included) and `‖ℓ⁻¹u‖² = ∑_{x ∈ Ω₁} ℓ(x)⁻² |u(x)|²`.

The constant differs from the `(1/2, 1/4)` of GREEN.md §3: the block Poincaré inequality landed in
`Balaban.blockPoincare` has the constant `d/2` (instead of the sharp `1/8` per direction of
GREEN.md Lemma 4.1), so the Poincaré gap per layer block is `2/(d L²ʲ)` and the constant depends on `d`.
Everything else is the proof of §4.1: the bonds inside the layer blocks are a subset of all bonds
(`sum_innerEnergy_le`), half of the energy is spent on the block Poincaré inequality on each layer
(`layer_ineq`), and `a_j ≥ 1/2` controls the block averages.

Main results:
* `Balaban.Multiscale.multiscale_coercive` : the inequality for `reQuad (dirichletOperator ..)`;
* `Balaban.Multiscale.dirichletOperator_isCoercive` : `IsCoercive` with constant `c₁ γ` whenever
  `γ ≤ ℓ(x)⁻²` on `Ω₁` (e.g. `γ = L⁻²ᵏ`, `dirichletOperator_isCoercive_min`);
* `Balaban.Multiscale.dirichletOperator_isUnit` : invertibility.
-/

@[expose] public section

namespace Balaban.Multiscale

open Finset Matrix

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-! ### Bonds inside blocks -/

section Bonds

variable {ℓ N m : ℕ} [NeZero ℓ] [NeZero m]

theorem blockCoord_add_one (hℓ : ℓ = N * m) (a : ZMod ℓ) (h : a.val % N + 1 < N) :
    blockCoord N m (a + 1) = blockCoord N m a := by
  subst hℓ
  have hN2 : 2 ≤ N := by omega
  have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.2 (NeZero.ne m)
  have hℓ2 : 2 ≤ N * m := by nlinarith
  have hN : 0 < N := by omega
  have h1 : (a + 1).val = (a.val + 1) % (N * m) := by
    rw [ZMod.val_add, ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (by omega : 1 < N * m)]
  have hq : a.val / N < m := by
    have := ZMod.val_lt a
    exact (Nat.div_lt_iff_lt_mul hN).2 (by linarith [mul_comm N m])
  have hdm := Nat.div_add_mod a.val N
  have hdm' : a.val / N * N + a.val % N = a.val := by rw [mul_comm]; exact hdm
  have hq1 : (a.val / N + 1) * N ≤ m * N := Nat.mul_le_mul_right N hq
  have hlt : a.val + 1 < N * m := by
    rw [add_mul, one_mul] at hq1
    nlinarith
  have h2 : (a.val + 1) / N = a.val / N := by
    refine Nat.div_eq_of_lt_le ((Nat.div_mul_le_self _ _).trans (Nat.le_succ _)) ?_
    rw [add_mul, one_mul]
    nlinarith
  unfold blockCoord
  rw [h1, Nat.mod_eq_of_lt hlt, h2]

theorem blockMap_add_single_of_inner (hℓ : ℓ = N * m) {x : Torus d ℓ} {μ : Fin d}
    (h : (x μ).val % N + 1 < N) :
    blockMap N m (x + Pi.single μ 1) = blockMap N m x := by
  funext i
  by_cases hi : i = μ
  · subst hi
    simp only [blockMap_apply, Pi.add_apply, Pi.single_eq_same]
    exact blockCoord_add_one hℓ _ h
  · simp [blockMap_apply, hi]

end Bonds

/-! ### Layers are unions of `j`-blocks -/

namespace GeneratingSet

variable (G : GeneratingSet d L N₀ k ϱ)

theorem jBlock_succ_eq {j : ℕ} (hj : j + 1 ≤ k) {x x' : Torus d (N₀ * L ^ k)}
    (h : jBlock d L N₀ k j x = jBlock d L N₀ k j x') :
    jBlock d L N₀ k (j + 1) x = jBlock d L N₀ k (j + 1) x' := by
  have hℓ := side_eq (N₀ := N₀) (L := L) (k := k) (j := j) (by omega)
  have hm : N₀ * L ^ (k - j) = L ^ 1 * (N₀ * L ^ (k - (j + 1))) := by
    obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hj
    have e1 : j + 1 + t - j = t + 1 := by omega
    have e2 : j + 1 + t - (j + 1) = t := by omega
    rw [e1, e2]
    ring
  have key := fun y : Torus d (N₀ * L ^ k) =>
    blockMap_pow_add (d := d) (L := L) (j := j) (k := 1) (m₂ := N₀ * L ^ (k - (j + 1))) hℓ hm y
  unfold jBlock at h ⊢
  rw [← key x, ← key x', h]

theorem mem_layer_iff {j : ℕ} (hj : 1 ≤ j) (hjk : j ≤ k) {x x' : Torus d (N₀ * L ^ k)}
    (h : jBlock d L N₀ k j x = jBlock d L N₀ k j x') : x ∈ G.layer j ↔ x' ∈ G.layer j := by
  rw [mem_layer, mem_layer, G.blockUnion j hj hjk x x' h]
  rcases Nat.lt_or_ge j k with hlt | hge
  · rw [G.blockUnion (j + 1) (by omega) (by omega) x x' (jBlock_succ_eq (by omega) h)]
  · have : j = k := le_antisymm hjk hge
    subst this
    simp [G.top]

end GeneratingSet

/-! ### Comparison of the layer energies with the full energy -/

section Energy

variable (G : GeneratingSet d L N₀ k ϱ)

theorem layerPart_sq_diff_le {j : ℕ} (hj : 1 ≤ j) (hjk : j ≤ k)
    (φ : Torus d (N₀ * L ^ k) → ℝ) (x : Torus d (N₀ * L ^ k)) (μ : Fin d)
    (h : (x μ).val % L ^ j + 1 < L ^ j) :
    (layerPart G j φ (x + Pi.single μ 1) - layerPart G j φ x) ^ 2 ≤
      if x ∈ G.layer j then (φ (x + Pi.single μ 1) - φ x) ^ 2 else 0 := by
  have hb : jBlock d L N₀ k j (x + Pi.single μ 1) = jBlock d L N₀ k j x :=
    blockMap_add_single_of_inner (side_eq hjk) h
  have hiff := G.mem_layer_iff hj hjk hb
  by_cases hx : x ∈ G.layer j
  · have hx' := hiff.2 hx
    simp [layerPart, hx, hx']
  · have hx' : x + Pi.single μ 1 ∉ G.layer j := fun h' => hx (hiff.1 h')
    simp [layerPart, hx, hx']

theorem sum_layer_ite_le (x : Torus d (N₀ * L ^ k)) {D : ℝ} (hD : 0 ≤ D) :
    ∑ j ∈ Icc 1 k, (if x ∈ G.layer j then D else 0) ≤ D := by
  by_cases h : ∃ j ∈ Icc 1 k, x ∈ G.layer j
  · obtain ⟨j0, hj0, hx0⟩ := h
    rw [Finset.sum_eq_single j0]
    · simp [hx0]
    · intro j hj hne
      have := G.layer_disjoint (mem_Icc.1 hj0).1 (mem_Icc.1 hj0).2 (mem_Icc.1 hj).1
        (mem_Icc.1 hj).2 (Ne.symm hne) hx0
      simp [this]
    · intro h
      exact absurd hj0 h
  · push Not at h
    have : ∀ j ∈ Icc 1 k, (if x ∈ G.layer j then D else 0) = 0 := fun j hj => by simp [h j hj]
    rw [Finset.sum_eq_zero this]
    exact hD

/-- The bonds inside the layer blocks are a subset of all bonds: the layer energies add up to at most
the full energy. -/
theorem sum_innerEnergy_le (φ : Torus d (N₀ * L ^ k) → ℝ) :
    ∑ j ∈ Icc 1 k, innerEnergy (L ^ j) (layerPart G j φ) ≤ latticeEnergy φ := by
  unfold innerEnergy latticeEnergy
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun x _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun μ _ => ?_
  simp only [update_eq_add_single]
  calc _ ≤ ∑ j ∈ Icc 1 k, (if x ∈ G.layer j then (φ (x + Pi.single μ 1) - φ x) ^ 2 else 0) := by
        refine Finset.sum_le_sum fun j hj => ?_
        by_cases hc : (x μ).val % L ^ j + 1 < L ^ j
        · simp only [hc, ↓reduceIte]
          exact layerPart_sq_diff_le G (mem_Icc.1 hj).1 (mem_Icc.1 hj).2 φ x μ hc
        · simp only [hc, ↓reduceIte]
          split_ifs <;> positivity
    _ ≤ _ := sum_layer_ite_le G x (sq_nonneg _)

end Energy

/-! ### Coercivity -/

section Coercivity

variable (G : GeneratingSet d L N₀ k ϱ)

/-- The Poincaré constant of the landed block Poincaré inequality: `min (1 / d) (1 / 2)`. -/
noncomputable def poincareConst (d : ℕ) : ℝ := min (1 / (d : ℝ)) (1 / 2)

/-- The constant `c₁ = min (1 / d) (1 / 2) / 2` of the multiscale coercivity. -/
noncomputable def coerciveConst (d : ℕ) : ℝ := poincareConst d / 2

theorem poincareConst_pos (hd : 0 < d) : 0 < poincareConst d := by
  have : (0 : ℝ) < d := by exact_mod_cast hd
  unfold poincareConst
  exact lt_min (by positivity) (by norm_num)

theorem coerciveConst_pos (hd : 0 < d) : 0 < coerciveConst d := by
  unfold coerciveConst
  have := poincareConst_pos hd
  positivity

/-- **Block Poincaré on one layer**: with `ψ = 1_{layer j} φ` and `a_j ≥ 1/2`,
`c L⁻²ʲ ‖ψ‖² ≤ ½ E_j(ψ) + a_j L⁻²ʲ ‖P_j ψ‖²`, `c = min (1/d) (1/2)`. -/
theorem layer_ineq (hd : 0 < d) {j : ℕ} (hjk : j ≤ k) {aj : ℝ} (ha : 1 / 2 ≤ aj)
    (φ : Torus d (N₀ * L ^ k) → ℝ) :
    poincareConst d / ((L : ℝ) ^ j) ^ 2 * ∑ x, (layerPart G j φ x) ^ 2 ≤
      (1 / 2) * innerEnergy (L ^ j) (layerPart G j φ) +
        (aj / ((L : ℝ) ^ j) ^ 2) *
          ∑ x, (blockProjection (L ^ j) (N₀ * L ^ (k - j)) (layerPart G j φ) x) ^ 2 := by
  have hℓ := side_eq (N₀ := N₀) (L := L) hjk
  have hN : 0 < L ^ j := Nat.pos_of_ne_zero (pow_ne_zero _ (NeZero.ne L))
  set ψ := layerPart G j φ with hψ
  set E := innerEnergy (L ^ j) ψ with hE
  set V := ∑ x, (ψ x - blockProjection (L ^ j) (N₀ * L ^ (k - j)) ψ x) ^ 2 with hV
  set S := ∑ x, (blockProjection (L ^ j) (N₀ * L ^ (k - j)) ψ x) ^ 2 with hS
  have hP := blockPoincare hℓ hN ψ
  have hpy := sum_sq_eq_sum_sq_sub_add hℓ hN ψ
  push_cast at hP
  have hV0 : 0 ≤ V := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hn : (0 : ℝ) < ((L : ℝ) ^ j) ^ 2 := by
    have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  have hc1 : poincareConst d ≤ 1 / (d : ℝ) := min_le_left _ _
  have hc2 : poincareConst d ≤ 1 / 2 := min_le_right _ _
  have h1 : poincareConst d * V ≤ ((L : ℝ) ^ j) ^ 2 * (1 / 2 * E) :=
    calc poincareConst d * V ≤ (1 / (d : ℝ)) * V := mul_le_mul_of_nonneg_right hc1 hV0
      _ ≤ (1 / (d : ℝ)) * (((d : ℝ) / 2) * ((L : ℝ) ^ j) ^ 2 * E) :=
          mul_le_mul_of_nonneg_left hP (by positivity)
      _ = ((L : ℝ) ^ j) ^ 2 * (1 / 2 * E) := by field_simp
  have h2 : poincareConst d * S ≤ aj * S := mul_le_mul_of_nonneg_right (hc2.trans ha) hS0
  have hn0 : ((L : ℝ) ^ j) ^ 2 ≠ 0 := hn.ne'
  have key : poincareConst d * (V + S) ≤ ((L : ℝ) ^ j) ^ 2 * (1 / 2 * E) + aj * S := by
    nlinarith
  rw [hpy]
  have e : 1 / 2 * E + aj / ((L : ℝ) ^ j) ^ 2 * S =
      (((L : ℝ) ^ j) ^ 2 * (1 / 2 * E) + aj * S) / ((L : ℝ) ^ j) ^ 2 := by
    generalize ((L : ℝ) ^ j) ^ 2 = n at hn0 ⊢
    field_simp
  rw [e, div_mul_eq_mul_div]
  gcongr

/-- The inverse squared spacing `ℓ(x)⁻²`, as a sum over the layers. -/
noncomputable def invSqSpacing (x : Torus d (N₀ * L ^ k)) : ℝ :=
  ∑ j ∈ Icc 1 k, if x ∈ G.layer j then (((L : ℝ) ^ j) ^ 2)⁻¹ else 0

theorem invSqSpacing_eq {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.Ω 1) :
    invSqSpacing G x = ((G.spacing x) ^ 2)⁻¹ := by
  obtain ⟨h1, h2, h3⟩ := G.layerIndex_spec hx
  unfold invSqSpacing
  rw [Finset.sum_eq_single (G.layerIndex x)]
  · simp only [h3, ↓reduceIte]; rfl
  · intro j hj hne
    have := G.layer_disjoint h1 h2 (mem_Icc.1 hj).1 (mem_Icc.1 hj).2 (Ne.symm hne) h3
    simp [this]
  · intro h
    exact absurd (mem_Icc.2 ⟨h1, h2⟩) h

/-- Real core of G-1(a): `½ E(φ) + c ∑ ℓ⁻² φ² ≤ φᵀ (-Δ + ν + Q* a Q) φ`. -/
theorem core_real (hd : 0 < d) {a : ℕ → ℝ} {ν : ℝ} (hν : 0 ≤ ν) (ha : IsAdmissibleWeights k a)
    (φ : Torus d (N₀ * L ^ k) → ℝ) :
    (1 / 2) * latticeEnergy φ + poincareConst d * ∑ x, invSqSpacing G x * φ x ^ 2 ≤
      φ ⬝ᵥ fullMatrix G a ν *ᵥ φ := by
  unfold fullMatrix
  rw [Matrix.add_mulVec, dotProduct_add, latticeLaplacian_quadratic, avgMatrix_quadratic]
  have hE := sum_innerEnergy_le G φ
  have hlay : ∑ x, invSqSpacing G x * φ x ^ 2 =
      ∑ j ∈ Icc 1 k, (((L : ℝ) ^ j) ^ 2)⁻¹ * ∑ x, (layerPart G j φ x) ^ 2 := by
    unfold invSqSpacing
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun x _ => ?_
    by_cases h : x ∈ G.layer j <;> simp [layerPart, h]
  have hper : ∑ j ∈ Icc 1 k, poincareConst d / ((L : ℝ) ^ j) ^ 2 * ∑ x, (layerPart G j φ x) ^ 2 ≤
      ∑ j ∈ Icc 1 k, ((1 / 2) * innerEnergy (L ^ j) (layerPart G j φ) +
        (a j / ((L : ℝ) ^ j) ^ 2) *
          ∑ x, (blockProjection (L ^ j) (N₀ * L ^ (k - j)) (layerPart G j φ) x) ^ 2) := by
    refine Finset.sum_le_sum fun j hj => ?_
    exact layer_ineq G hd (mem_Icc.1 hj).2 (ha j (mem_Icc.1 hj).1 (mem_Icc.1 hj).2).1 φ
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hper
  have hlay' : poincareConst d * ∑ x, invSqSpacing G x * φ x ^ 2 =
      ∑ j ∈ Icc 1 k, poincareConst d / ((L : ℝ) ^ j) ^ 2 * ∑ x, (layerPart G j φ x) ^ 2 := by
    rw [hlay, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← mul_assoc, div_eq_mul_inv]
  have hν' : 0 ≤ ν * ∑ x, φ x ^ 2 := mul_nonneg hν (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hlat : latticeEnergy φ = ∑ x, ∑ μ : Fin d, (φ (x + Pi.single μ 1) - φ x) ^ 2 := rfl
  rw [hlat] at hE ⊢
  rw [hlay']
  linarith

end Coercivity

section Complex

variable (G : GeneratingSet d L N₀ k ϱ)

/-- `‖∂ũ‖²`: the sum of `|ũ(x + e_μ) - ũ(x)|²` over all bonds of the torus, `ũ` the zero extension
of `u` (so bonds joining `Ω₁` to its complement are included). -/
noncomputable def dirichletEnergy (u : G.Ω 1 → ℂ) : ℝ :=
  ∑ x, ∑ μ : Fin d, ‖zeroExt (G.Ω 1) u (x + Pi.single μ 1) - zeroExt (G.Ω 1) u x‖ ^ 2

/-- `‖ℓ⁻¹ u‖² = ∑_{x ∈ Ω₁} ℓ(x)⁻² |u(x)|²`. -/
noncomputable def weightedSqNorm (u : G.Ω 1 → ℂ) : ℝ :=
  ∑ x : G.Ω 1, ‖u x‖ ^ 2 / (G.spacing x) ^ 2

theorem dirichletEnergy_nonneg (u : G.Ω 1 → ℂ) : 0 ≤ dirichletEnergy G u :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem weightedSqNorm_nonneg (u : G.Ω 1 → ℂ) : 0 ≤ weightedSqNorm G u :=
  Finset.sum_nonneg fun _ _ => by positivity

theorem dirichletEnergy_eq (u : G.Ω 1 → ℂ) :
    dirichletEnergy G u =
      latticeEnergy (fun x => (zeroExt (G.Ω 1) u x).re) +
        latticeEnergy (fun x => (zeroExt (G.Ω 1) u x).im) := by
  unfold dirichletEnergy latticeEnergy
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im]
  ring

theorem sum_invSqSpacing_eq (u : G.Ω 1 → ℂ) :
    ∑ x, invSqSpacing G x * ‖zeroExt (G.Ω 1) u x‖ ^ 2 = weightedSqNorm G u := by
  rw [Green.sum_eq_sum_subtype (G.Ω 1) _ (fun i hi => by simp [zeroExt, hi])]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hx : (x : Torus d (N₀ * L ^ k)) ∈ G.Ω 1 := x.2
  rw [invSqSpacing_eq G hx]
  have : zeroExt (G.Ω 1) u x = u x := by simp [zeroExt]
  rw [this, div_eq_mul_inv, mul_comm]

/-- **G-1(a), the quadratic form.** For `ν ≥ 0`, `a_j ∈ [1/2, 2]` and `|α(x)| ≤ c₁ ℓ(x)⁻² / 2`,
`c₁ (‖∂ũ‖² + ‖ℓ⁻¹u‖²) ≤ Re ⟨u, H_D(α) u⟩`. -/
theorem multiscale_coercive (hd : 0 < d) {a : ℕ → ℝ} {ν : ℝ} (hν : 0 ≤ ν)
    (ha : IsAdmissibleWeights k a) (α : G.Ω 1 → ℂ)
    (hα : ∀ x, ‖α x‖ ≤ coerciveConst d / (2 * (G.spacing x) ^ 2)) (u : G.Ω 1 → ℂ) :
    coerciveConst d * (dirichletEnergy G u + weightedSqNorm G u) ≤
      Green.reQuad (dirichletOperator G a ν α) u := by
  rw [reQuad_dirichletOperator, reQuad_map_ofReal]
  have h1 := core_real G hd hν ha (fun x => (zeroExt (G.Ω 1) u x).re)
  have h2 := core_real G hd hν ha (fun x => (zeroExt (G.Ω 1) u x).im)
  have hw := sum_invSqSpacing_eq G u
  have hsplit : ∑ x, invSqSpacing G x * ‖zeroExt (G.Ω 1) u x‖ ^ 2 =
      ∑ x, invSqSpacing G x * (zeroExt (G.Ω 1) u x).re ^ 2 +
        ∑ x, invSqSpacing G x * (zeroExt (G.Ω 1) u x).im ^ 2 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have hαs : -(coerciveConst d / 2 * weightedSqNorm G u) ≤ ∑ i, (α i).re * ‖u i‖ ^ 2 := by
    unfold weightedSqNorm
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    have hre : -(coerciveConst d / (2 * (G.spacing i) ^ 2)) ≤ (α i).re := by
      have := Complex.abs_re_le_norm (α i)
      have := hα i
      linarith [neg_abs_le (α i).re]
    have : -(coerciveConst d / 2 * (‖u i‖ ^ 2 / (G.spacing i) ^ 2)) =
        -(coerciveConst d / (2 * (G.spacing i) ^ 2)) * ‖u i‖ ^ 2 := by
      field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_right hre (sq_nonneg _)
  have hE := dirichletEnergy_eq G u
  have hc := coerciveConst_pos hd
  have hpc : poincareConst d = 2 * coerciveConst d := by unfold coerciveConst; ring
  have hle : poincareConst d ≤ 1 / 2 := min_le_right _ _
  have hDE := dirichletEnergy_nonneg G u
  have hW := weightedSqNorm_nonneg G u
  rw [hpc] at h1 h2
  nlinarith

/-- **G-1(a), coercivity.** If `γ ≤ ℓ(x)⁻²` on `Ω₁` and `|α(x)| ≤ c₁ ℓ(x)⁻² / 2`, then `H_D(α)` is
`c₁ γ`-coercive. -/
theorem dirichletOperator_isCoercive (hd : 0 < d) {a : ℕ → ℝ} {ν : ℝ} (hν : 0 ≤ ν)
    (ha : IsAdmissibleWeights k a) (α : G.Ω 1 → ℂ)
    (hα : ∀ x, ‖α x‖ ≤ coerciveConst d / (2 * (G.spacing x) ^ 2)) {γ : ℝ}
    (hγ : ∀ x : G.Ω 1, γ ≤ ((G.spacing x) ^ 2)⁻¹) :
    Green.IsCoercive (dirichletOperator G a ν α) (coerciveConst d * γ) := by
  intro u
  have h := multiscale_coercive G hd hν ha α hα u
  have hc := coerciveConst_pos hd
  have hsq : γ * Green.sqNorm u ≤ weightedSqNorm G u := by
    unfold Green.sqNorm weightedSqNorm
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun x _ => ?_
    rw [div_eq_mul_inv, mul_comm (‖u x‖ ^ 2)]
    exact mul_le_mul_of_nonneg_right (hγ x) (sq_nonneg _)
  have hDE := dirichletEnergy_nonneg G u
  nlinarith

theorem spacing_le {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.Ω 1) : G.spacing x ≤ (L : ℝ) ^ k := by
  obtain ⟨h1, h2, _⟩ := G.layerIndex_spec hx
  have hL : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  exact pow_le_pow_right₀ hL h2

theorem spacing_pos {x : Torus d (N₀ * L ^ k)} : 0 < G.spacing x := by
  have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  unfold GeneratingSet.spacing
  positivity

/-- **G-1(a), global constant.** With `γ = L⁻²ᵏ ≤ ℓ(x)⁻²`: `H_D(α)` is `c₁ L⁻²ᵏ`-coercive. -/
theorem dirichletOperator_isCoercive_min (hd : 0 < d) {a : ℕ → ℝ} {ν : ℝ} (hν : 0 ≤ ν)
    (ha : IsAdmissibleWeights k a) (α : G.Ω 1 → ℂ)
    (hα : ∀ x, ‖α x‖ ≤ coerciveConst d / (2 * (G.spacing x) ^ 2)) :
    Green.IsCoercive (dirichletOperator G a ν α) (coerciveConst d * (((L : ℝ) ^ k) ^ 2)⁻¹) := by
  refine dirichletOperator_isCoercive G hd hν ha α hα fun x => ?_
  have hp : 0 < G.spacing x := spacing_pos G
  exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hp.le (spacing_le G x.2) 2)

/-- **G-1(a), invertibility.** -/
theorem dirichletOperator_isUnit (hd : 0 < d) {a : ℕ → ℝ} {ν : ℝ} (hν : 0 ≤ ν)
    (ha : IsAdmissibleWeights k a) (α : G.Ω 1 → ℂ)
    (hα : ∀ x, ‖α x‖ ≤ coerciveConst d / (2 * (G.spacing x) ^ 2)) :
    IsUnit (dirichletOperator G a ν α) := by
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  exact Green.isUnit_of_isCoercive
    (mul_pos (coerciveConst_pos hd) (inv_pos.2 (by positivity)))
    (dirichletOperator_isCoercive_min G hd hν ha α hα)

end Complex

end Balaban.Multiscale
