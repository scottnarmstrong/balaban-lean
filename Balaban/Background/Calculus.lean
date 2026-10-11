/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Multiscale.ConstraintSup
public import Balaban.Multiscale.Analyticity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Calculus on the multiscale lattice (BACKGROUND.md §3)
-/

@[expose] public section

namespace Balaban.Background

open Balaban.Multiscale Matrix Finset

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

section Formula

/-- `(-Δ w)(x) = ∑_μ (2 w(x) - w(x + e_μ) - w(x - e_μ))`, the nearest-neighbour lattice Laplacian
(with the sign making it nonnegative) of a function on the torus. -/
def negLap {d ℓ : ℕ} (w : Torus d ℓ → ℂ) (x : Torus d ℓ) : ℂ :=
  ∑ μ : Fin d, (2 * w x - w (x + Pi.single μ 1) - w (x - Pi.single μ 1))

variable (G : GeneratingSet d L N₀ k ϱ)

/-- The block-average term `(Q* a Q w)(x) = a_n L^{-2n} (P_{B_n(x)} w)(x)` of `H_D`, where `n` is
the layer index of `x` and `P_B` is the average over the `n`-block `B_n(x)`. -/
noncomputable def blockTerm (a : ℕ → ℝ) (w : Torus d (N₀ * L ^ k) → ℂ)
    (x : Torus d (N₀ * L ^ k)) : ℂ :=
  ((a (G.layerIndex x) / ((L : ℝ) ^ G.layerIndex x) ^ 2 : ℝ) : ℂ) *
    ((((((L : ℝ) ^ G.layerIndex x) ^ d)⁻¹ : ℝ) : ℂ) * ∑ y ∈ G.blk (G.layerIndex x) x, w y)

/-- **Pointwise form of `H_D(α)`**: for `x ∈ Ω₁`,
`(H_D(α) u)(x) = (-Δ ũ)(x) + (Q* a Q ũ)(x) + ν u(x) + α(x) u(x)` with `ũ` the zero extension. -/
theorem dirichlet_apply (a : ℕ → ℝ) (ν : ℝ) (α : G.Ω 1 → ℂ) (u : G.Ω 1 → ℂ) (x : G.Ω 1) :
    (dirichletOperator G a ν α *ᵥ u) x =
      negLap (zeroExt (G.Ω 1) u) x + blockTerm G a (zeroExt (G.Ω 1) u) x + ν * u x + α x * u x := by
  have h := dirichlet_eq G (a := a) (ν := ν) (α := α) (u := u) (f := dirichletOperator G a ν α *ᵥ u)
    rfl x
  rw [← h]
  have hx : zeroExt (G.Ω 1) u (x : Torus d (N₀ * L ^ k)) = u x := zeroExt_mem _ _ _
  have hfull : (fullMatrix G a ν).map (algebraMap ℝ ℂ) =
      (latticeLaplacian d (N₀ * L ^ k) ν).map (algebraMap ℝ ℂ) +
        (avgMatrix G a).map (algebraMap ℝ ℂ) := by
    ext y z; simp [fullMatrix]
  rw [hfull, Matrix.add_mulVec, Pi.add_apply, lap_mulVec_complex, hx]
  obtain ⟨hj1, hjk, hxl⟩ := G.layerIndex_spec x.2
  have hblock : ((avgMatrix G a).map (algebraMap ℝ ℂ) *ᵥ zeroExt (G.Ω 1) u)
      (x : Torus d (N₀ * L ^ k)) = blockTerm G a (zeroExt (G.Ω 1) u) x := by
    have hterm : ∀ y : Torus d (N₀ * L ^ k),
        (algebraMap ℝ ℂ) (avgMatrix G a x y) * zeroExt (G.Ω 1) u y =
          if y ∈ G.blk (G.layerIndex (x : Torus d (N₀ * L ^ k))) x then
            ((a (G.layerIndex x) / ((L : ℝ) ^ G.layerIndex x) ^ 2 : ℝ) : ℂ) *
              ((((((L : ℝ) ^ G.layerIndex x) ^ d)⁻¹ : ℝ) : ℂ) * zeroExt (G.Ω 1) u y) else 0 := by
      intro y
      rw [avgMatrix_apply_of_layer G a hj1 hjk hxl, layerProjMatrix_apply_of_layer G hj1 hjk hxl]
      by_cases hy : y ∈ G.blk (G.layerIndex (x : Torus d (N₀ * L ^ k))) x
      · simp only [hy, ↓reduceIte, map_mul, Complex.coe_algebraMap]
        ring
      · simp [hy]
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
    rw [Finset.sum_congr rfl fun y _ => hterm y, ← Finset.sum_filter]
    unfold blockTerm
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    have hf : (Finset.univ.filter fun y : Torus d (N₀ * L ^ k) =>
        y ∈ G.blk (G.layerIndex (x : Torus d (N₀ * L ^ k))) x) =
        G.blk (G.layerIndex (x : Torus d (N₀ * L ^ k))) x := by ext y; simp
    rw [hf]
  rw [hblock]
  unfold negLap
  simp only [hx]
  ring


end Formula

omit [NeZero N₀] [NeZero L] in
/-- The exact discrete Leibniz rule (3.1) for `-Δ`:
`-Δ(vw) = v(-Δw) + w(-Δv) - ∑_e Δ_e v Δ_e w` (sum over the `2d` unit vectors). -/
theorem negLap_mul {ℓ : ℕ} (v w : Torus d ℓ → ℂ) (x : Torus d ℓ) :
    negLap (fun y => v y * w y) x = v x * negLap w x + w x * negLap v x -
      ∑ μ : Fin d, ((v (x + Pi.single μ 1) - v x) * (w (x + Pi.single μ 1) - w x) +
        (v (x - Pi.single μ 1) - v x) * (w (x - Pi.single μ 1) - w x)) := by
  unfold negLap
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun μ _ => by ring

/-- Zero extension of a product. -/
theorem zeroExt_mul (G : GeneratingSet d L N₀ k ϱ) (u w : G.Ω 1 → ℂ) :
    zeroExt (G.Ω 1) (u * w) = fun y => zeroExt (G.Ω 1) u y * zeroExt (G.Ω 1) w y := by
  funext y
  by_cases hy : y ∈ G.Ω 1
  · simp [zeroExt, hy]
  · simp [zeroExt, hy]

section Rform

variable {G : GeneratingSet d L N₀ k ϱ}

/-- The scalar quadratic remainder `R(u, w) = H(uw) - u Hw - w Hu` (BACKGROUND.md Lemma 3.2,
polarised). -/
noncomputable def Rsc (H : Matrix (G.Ω 1) (G.Ω 1) ℂ) (u w : G.Ω 1 → ℂ) : G.Ω 1 → ℂ :=
  H *ᵥ (u * w) - u * (H *ᵥ w) - w * (H *ᵥ u)

/-- Explicit form of `R` for `H = H_D(α)`:
`R(u,w)(x) = -∑_e Δ_e ũ Δ_e w̃ + [Q*aQ, ·]-term - (ν + α) u w`. -/
theorem Rsc_apply (a : ℕ → ℝ) (ν : ℝ) (α : G.Ω 1 → ℂ) (u w : G.Ω 1 → ℂ) (x : G.Ω 1) :
    Rsc (dirichletOperator G a ν α) u w x =
      -(∑ μ : Fin d, ((zeroExt (G.Ω 1) u ((x : Torus d (N₀ * L ^ k)) + Pi.single μ 1) - u x) *
          (zeroExt (G.Ω 1) w ((x : Torus d (N₀ * L ^ k)) + Pi.single μ 1) - w x) +
        (zeroExt (G.Ω 1) u ((x : Torus d (N₀ * L ^ k)) - Pi.single μ 1) - u x) *
          (zeroExt (G.Ω 1) w ((x : Torus d (N₀ * L ^ k)) - Pi.single μ 1) - w x))) +
      (blockTerm G a (fun y => zeroExt (G.Ω 1) u y * zeroExt (G.Ω 1) w y) x -
        u x * blockTerm G a (zeroExt (G.Ω 1) w) x - w x * blockTerm G a (zeroExt (G.Ω 1) u) x) -
      (ν + α x) * (u x * w x) := by
  have hx : ∀ f : G.Ω 1 → ℂ, zeroExt (G.Ω 1) f (x : Torus d (N₀ * L ^ k)) = f x :=
    fun f => zeroExt_mem _ _ _
  simp only [Rsc, Pi.sub_apply, Pi.mul_apply]
  rw [dirichlet_apply, dirichlet_apply, dirichlet_apply, zeroExt_mul G, negLap_mul]
  have hp : (u * w) x = u x * w x := rfl
  rw [hp]
  simp only [hx]
  ring


theorem blockTerm_norm_le {a : ℕ → ℝ} (ha : IsAdmissibleWeights k a) {x : Torus d (N₀ * L ^ k)}
    (hx : x ∈ G.Ω 1) {f : Torus d (N₀ * L ^ k) → ℂ} {F : ℝ}
    (hf : ∀ y, ‖f y‖ ≤ F) :
    ‖blockTerm G a f x‖ ≤ a (G.layerIndex x) / ((L : ℝ) ^ G.layerIndex x) ^ 2 * F := by
  obtain ⟨hj1, hjk, hxl⟩ := G.layerIndex_spec hx
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have haj : 0 ≤ a (G.layerIndex x) := by linarith [(ha _ hj1 hjk).1]
  have hLj : (0 : ℝ) < ((L : ℝ) ^ G.layerIndex x) ^ d := by positivity
  have hc : ((G.blk (G.layerIndex x) x).card : ℝ) = ((L : ℝ) ^ G.layerIndex x) ^ d :=
    card_blk_cast G _ hjk x
  unfold blockTerm
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg (by positivity),
    Real.norm_of_nonneg (by positivity)]
  have hsum : ‖∑ y ∈ G.blk (G.layerIndex x) x, f y‖ ≤ ((L : ℝ) ^ G.layerIndex x) ^ d * F := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ y ∈ G.blk (G.layerIndex x) x, ‖f y‖ ≤ ∑ _y ∈ G.blk (G.layerIndex x) x, F :=
          Finset.sum_le_sum fun y _ => hf y
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, hc]
  have h1 : (((L : ℝ) ^ G.layerIndex x) ^ d)⁻¹ *
      ‖∑ y ∈ G.blk (G.layerIndex x) x, f y‖ ≤ F := by
    calc _ ≤ (((L : ℝ) ^ G.layerIndex x) ^ d)⁻¹ * (((L : ℝ) ^ G.layerIndex x) ^ d * F) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = F := by field_simp
  have hc0 : 0 ≤ a (G.layerIndex x) / ((L : ℝ) ^ G.layerIndex x) ^ 2 := by positivity
  calc _ ≤ a (G.layerIndex x) / ((L : ℝ) ^ G.layerIndex x) ^ 2 * F :=
        mul_le_mul_of_nonneg_left h1 hc0
    _ = _ := rfl

theorem Rsc_bound {a : ℕ → ℝ} (ha : IsAdmissibleWeights k a) {ν : ℝ} (hν0 : 0 ≤ ν)
    {α : G.Ω 1 → ℂ} {x : G.Ω 1} (hν : ν * G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 ≤ 1)
    (hα : G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 * ‖α x‖ ≤ 1)
    {u w : G.Ω 1 → ℂ} {U W : ℝ} (hU : 0 ≤ U) (hW : 0 ≤ W)
    (hu0 : ∀ y, ‖zeroExt (G.Ω 1) u y‖ ≤ U) (hw0 : ∀ y, ‖zeroExt (G.Ω 1) w y‖ ≤ W)
    (hu1 : ∀ μ : Fin d, G.spacing (x : Torus d (N₀ * L ^ k)) *
      ‖zeroExt (G.Ω 1) u ((x : Torus d (N₀ * L ^ k)) + Pi.single μ 1) - u x‖ ≤ U)
    (hu2 : ∀ μ : Fin d, G.spacing (x : Torus d (N₀ * L ^ k)) *
      ‖zeroExt (G.Ω 1) u ((x : Torus d (N₀ * L ^ k)) - Pi.single μ 1) - u x‖ ≤ U)
    (hw1 : ∀ μ : Fin d, G.spacing (x : Torus d (N₀ * L ^ k)) *
      ‖zeroExt (G.Ω 1) w ((x : Torus d (N₀ * L ^ k)) + Pi.single μ 1) - w x‖ ≤ W)
    (hw2 : ∀ μ : Fin d, G.spacing (x : Torus d (N₀ * L ^ k)) *
      ‖zeroExt (G.Ω 1) w ((x : Torus d (N₀ * L ^ k)) - Pi.single μ 1) - w x‖ ≤ W) :
    G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 * ‖Rsc (dirichletOperator G a ν α) u w x‖ ≤
      (2 * d + 8) * (U * W) := by
  obtain ⟨hj1, hjk, hxl⟩ := G.layerIndex_spec x.2
  set p : Torus d (N₀ * L ^ k) := (x : Torus d (N₀ * L ^ k)) with hp
  set ℓ : ℝ := G.spacing p with hℓdef
  have hsp : ℓ = (L : ℝ) ^ G.layerIndex p := G.spacing_eq hj1 hjk hxl
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hℓ : 0 < ℓ := by rw [hsp]; positivity
  have hUW : 0 ≤ U * W := mul_nonneg hU hW
  have hxe : ∀ f : G.Ω 1 → ℂ, zeroExt (G.Ω 1) f p = f x := fun f => zeroExt_mem _ _ _
  have key : ∀ b c : ℂ, ℓ * ‖b‖ ≤ U → ℓ * ‖c‖ ≤ W → ℓ ^ 2 * ‖b * c‖ ≤ U * W := by
    intro b c hb hc
    rw [norm_mul]
    calc ℓ ^ 2 * (‖b‖ * ‖c‖) = (ℓ * ‖b‖) * (ℓ * ‖c‖) := by ring
      _ ≤ U * W := mul_le_mul hb hc (by positivity) hU
  rw [Rsc_apply]
  set T1 := ∑ μ : Fin d, ((zeroExt (G.Ω 1) u (p + Pi.single μ 1) - u x) *
          (zeroExt (G.Ω 1) w (p + Pi.single μ 1) - w x) +
        (zeroExt (G.Ω 1) u (p - Pi.single μ 1) - u x) *
          (zeroExt (G.Ω 1) w (p - Pi.single μ 1) - w x)) with hT1
  set T2 := blockTerm G a (fun y => zeroExt (G.Ω 1) u y * zeroExt (G.Ω 1) w y) p -
        u x * blockTerm G a (zeroExt (G.Ω 1) w) p - w x * blockTerm G a (zeroExt (G.Ω 1) u) p
    with hT2
  set T3 := ((ν : ℂ) + α x) * (u x * w x) with hT3
  have h1 : ℓ ^ 2 * ‖T1‖ ≤ 2 * d * (U * W) := by
    calc ℓ ^ 2 * ‖T1‖ ≤ ℓ ^ 2 * ∑ μ : Fin d, (‖(zeroExt (G.Ω 1) u (p + Pi.single μ 1) - u x) *
          (zeroExt (G.Ω 1) w (p + Pi.single μ 1) - w x)‖ +
        ‖(zeroExt (G.Ω 1) u (p - Pi.single μ 1) - u x) *
          (zeroExt (G.Ω 1) w (p - Pi.single μ 1) - w x)‖) := by
          refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans ?_) (by positivity)
          exact Finset.sum_le_sum fun μ _ => norm_add_le _ _
      _ = ∑ μ : Fin d, (ℓ ^ 2 * ‖(zeroExt (G.Ω 1) u (p + Pi.single μ 1) - u x) *
          (zeroExt (G.Ω 1) w (p + Pi.single μ 1) - w x)‖ +
        ℓ ^ 2 * ‖(zeroExt (G.Ω 1) u (p - Pi.single μ 1) - u x) *
          (zeroExt (G.Ω 1) w (p - Pi.single μ 1) - w x)‖) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun μ _ => by ring
      _ ≤ ∑ _μ : Fin d, (U * W + U * W) := by
          refine Finset.sum_le_sum fun μ _ => add_le_add ?_ ?_
          · exact key _ _ (hu1 μ) (hw1 μ)
          · exact key _ _ (hu2 μ) (hw2 μ)
      _ = 2 * d * (U * W) := by simp; ring
  have hc : ℓ ^ 2 * (a (G.layerIndex p) / ((L : ℝ) ^ G.layerIndex p) ^ 2) ≤ 2 := by
    have h2 := (ha _ hj1 hjk).2
    rw [hsp]
    have : (0 : ℝ) < ((L : ℝ) ^ G.layerIndex p) ^ 2 := by positivity
    calc ((L : ℝ) ^ G.layerIndex p) ^ 2 * (a (G.layerIndex p) / ((L : ℝ) ^ G.layerIndex p) ^ 2)
        = a (G.layerIndex p) := by field_simp
      _ ≤ 2 := h2
  have hc0 : 0 ≤ a (G.layerIndex p) / ((L : ℝ) ^ G.layerIndex p) ^ 2 := by
    have := (ha _ hj1 hjk).1
    positivity
  have hux : ‖u x‖ ≤ U := by simpa [hxe] using hu0 p
  have hwx : ‖w x‖ ≤ W := by simpa [hxe] using hw0 p
  have hb1 := blockTerm_norm_le (G := G) ha x.2
    (f := fun y => zeroExt (G.Ω 1) u y * zeroExt (G.Ω 1) w y) (fun y => by
      rw [norm_mul]; exact mul_le_mul (hu0 y) (hw0 y) (norm_nonneg _) hU)
  have hb2 := blockTerm_norm_le (G := G) ha x.2 (f := zeroExt (G.Ω 1) w) hw0
  have hb3 := blockTerm_norm_le (G := G) ha x.2 (f := zeroExt (G.Ω 1) u) hu0
  set c := a (G.layerIndex p) / ((L : ℝ) ^ G.layerIndex p) ^ 2 with hcdef
  have h2 : ‖T2‖ ≤ c * (U * W) + U * (c * W) + W * (c * U) := by
    refine (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add hb1 ?_)) ?_)
    · rw [norm_mul]; exact mul_le_mul hux hb2 (norm_nonneg _) hU
    · rw [norm_mul]; exact mul_le_mul hwx hb3 (norm_nonneg _) hW
  have h2' : ℓ ^ 2 * ‖T2‖ ≤ 6 * (U * W) := by
    calc ℓ ^ 2 * ‖T2‖ ≤ ℓ ^ 2 * (3 * c * (U * W)) := by
          refine mul_le_mul_of_nonneg_left (h2.trans (le_of_eq (by ring))) (by positivity)
      _ = 3 * (ℓ ^ 2 * c) * (U * W) := by ring
      _ ≤ 3 * 2 * (U * W) := by gcongr
      _ = _ := by ring
  have h3 : ℓ ^ 2 * ‖T3‖ ≤ 2 * (U * W) := by
    have hn : ‖((ν : ℂ) + α x)‖ ≤ ν + ‖α x‖ := by
      refine (norm_add_le _ _).trans ?_
      rw [Complex.norm_real, Real.norm_of_nonneg hν0]
    calc ℓ ^ 2 * ‖T3‖ = ℓ ^ 2 * (‖((ν : ℂ) + α x)‖ * (‖u x‖ * ‖w x‖)) := by
          rw [hT3, norm_mul, norm_mul]
      _ ≤ ℓ ^ 2 * ((ν + ‖α x‖) * (U * W)) := by
          gcongr
      _ = (ν * ℓ ^ 2 + ℓ ^ 2 * ‖α x‖) * (U * W) := by ring
      _ ≤ (1 + 1) * (U * W) := by gcongr
      _ = _ := by ring
  have hsum : ‖-T1 + T2 - T3‖ ≤ ‖T1‖ + ‖T2‖ + ‖T3‖ := by
    refine (norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans ?_) le_rfl)
    rw [norm_neg]
  calc ℓ ^ 2 * ‖-T1 + T2 - T3‖ ≤ ℓ ^ 2 * (‖T1‖ + ‖T2‖ + ‖T3‖) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = ℓ ^ 2 * ‖T1‖ + ℓ ^ 2 * ‖T2‖ + ℓ ^ 2 * ‖T3‖ := by ring
    _ ≤ 2 * d * (U * W) + 6 * (U * W) + 2 * (U * W) := by linarith
    _ = _ := by ring

end Rform

/-! ### The norm bundle `|u|₀, |∂u|₁` for vector fields on `Ω₁` -/

section Star

variable (G : GeneratingSet d L N₀ k ϱ)

/-- `|u|₀ ≤ V` and `|∂u|₁ ≤ V` for a vector field `u` on `Ω₁` (zero extended), componentwise:
the part of `Balaban.Multiscale.SupBounds` without the Laplacian.  Here `|∂u|₁` is the supremum
over all bonds `(x, x ± e_μ)` at points `x ∈ Ω₁` (wall bonds included, the outside value being
`0`) of `ℓ(x) |∂ũ|`, which is `sup_b ℓ̄(b) |∂ũ(b)|` of BACKGROUND.md §1.1. -/
structure StarBound (u : G.Ω 1 × Fin N → ℂ) (V : ℝ) : Prop where
  val : ∀ (y : Torus d (N₀ * L ^ k)) (i : Fin N), ‖svec G u y i‖ ≤ V
  fwd : ∀ x ∈ G.Ω 1, ∀ (μ : Fin d) (i : Fin N),
    G.spacing x * ‖svec G u (x + Pi.single μ 1) i - svec G u x i‖ ≤ V
  bwd : ∀ x ∈ G.Ω 1, ∀ (μ : Fin d) (i : Fin N),
    G.spacing x * ‖svec G u (x - Pi.single μ 1) i - svec G u x i‖ ≤ V

variable {G}

theorem SupBounds.star {u : G.Ω 1 × Fin N → ℂ} {V : ℝ} (h : SupBounds G u V) : StarBound G u V :=
  ⟨h.val, h.fwd, h.bwd⟩

theorem StarBound.mono {u : G.Ω 1 × Fin N → ℂ} {V V' : ℝ} (h : StarBound G u V) (hV : V ≤ V') :
    StarBound G u V' :=
  ⟨fun y i => (h.val y i).trans hV, fun x hx μ i => (h.fwd x hx μ i).trans hV,
    fun x hx μ i => (h.bwd x hx μ i).trans hV⟩

theorem svec_add (u w : G.Ω 1 × Fin N → ℂ) (y : Torus d (N₀ * L ^ k)) (i : Fin N) :
    svec G (u + w) y i = svec G u y i + svec G w y i := by
  unfold svec zeroExt
  split_ifs <;> simp

theorem StarBound.sub {u w : G.Ω 1 × Fin N → ℂ} {V W : ℝ} (hu : StarBound G u V)
    (hw : StarBound G w W) : StarBound G (u - w) (V + W) := by
  have key : ∀ (y z : Torus d (N₀ * L ^ k)) (i : Fin N),
      svec G (u - w) y i - svec G (u - w) z i =
        (svec G u y i - svec G u z i) - (svec G w y i - svec G w z i) := by
    intro y z i; simp only [svec_sub]; ring
  refine ⟨fun y i => ?_, fun x hx μ i => ?_, fun x hx μ i => ?_⟩
  · rw [svec_sub]; exact (norm_sub_le _ _).trans (add_le_add (hu.val y i) (hw.val y i))
  · rw [key]
    calc _ ≤ G.spacing x * (‖svec G u (x + Pi.single μ 1) i - svec G u x i‖ +
          ‖svec G w (x + Pi.single μ 1) i - svec G w x i‖) :=
          mul_le_mul_of_nonneg_left (norm_sub_le _ _) (spacing_pos G).le
      _ ≤ _ := by rw [mul_add]; exact add_le_add (hu.fwd x hx μ i) (hw.fwd x hx μ i)
  · rw [key]
    calc _ ≤ G.spacing x * (‖svec G u (x - Pi.single μ 1) i - svec G u x i‖ +
          ‖svec G w (x - Pi.single μ 1) i - svec G w x i‖) :=
          mul_le_mul_of_nonneg_left (norm_sub_le _ _) (spacing_pos G).le
      _ ≤ _ := by rw [mul_add]; exact add_le_add (hu.bwd x hx μ i) (hw.bwd x hx μ i)

theorem StarBound.add {u w : G.Ω 1 × Fin N → ℂ} {V W : ℝ} (hu : StarBound G u V)
    (hw : StarBound G w W) : StarBound G (u + w) (V + W) := by
  have key : ∀ (y z : Torus d (N₀ * L ^ k)) (i : Fin N),
      svec G (u + w) y i - svec G (u + w) z i =
        (svec G u y i - svec G u z i) + (svec G w y i - svec G w z i) := by
    intro y z i; simp only [svec_add]; ring
  refine ⟨fun y i => ?_, fun x hx μ i => ?_, fun x hx μ i => ?_⟩
  · rw [svec_add]; exact (norm_add_le _ _).trans (add_le_add (hu.val y i) (hw.val y i))
  · rw [key]
    calc _ ≤ G.spacing x * (‖svec G u (x + Pi.single μ 1) i - svec G u x i‖ +
          ‖svec G w (x + Pi.single μ 1) i - svec G w x i‖) :=
          mul_le_mul_of_nonneg_left (norm_add_le _ _) (spacing_pos G).le
      _ ≤ _ := by rw [mul_add]; exact add_le_add (hu.fwd x hx μ i) (hw.fwd x hx μ i)
  · rw [key]
    calc _ ≤ G.spacing x * (‖svec G u (x - Pi.single μ 1) i - svec G u x i‖ +
          ‖svec G w (x - Pi.single μ 1) i - svec G w x i‖) :=
          mul_le_mul_of_nonneg_left (norm_add_le _ _) (spacing_pos G).le
      _ ≤ _ := by rw [mul_add]; exact add_le_add (hu.bwd x hx μ i) (hw.bwd x hx μ i)

theorem StarBound.zero (V : ℝ) (hV : 0 ≤ V) : StarBound G (0 : G.Ω 1 × Fin N → ℂ) V := by
  have h0 : ∀ (y : Torus d (N₀ * L ^ k)) (i : Fin N), svec G (0 : G.Ω 1 × Fin N → ℂ) y i = 0 := by
    intro y i; simp [svec, zeroExt]
  refine ⟨fun y i => ?_, fun x _ μ i => ?_, fun x _ μ i => ?_⟩ <;> simp [h0, hV]

end Star

section Vector

variable {G : GeneratingSet d L N₀ k ϱ}

/-- The vector quadratic remainder `R(v, w) = H(v · w) - v · Hw - w · Hv`, summed over the
components (BACKGROUND.md Lemma 3.2, polarised; `R(v) = R(v, v)`). -/
noncomputable def Rvec (H : Matrix (G.Ω 1) (G.Ω 1) ℂ) (v w : G.Ω 1 × Fin N → ℂ) : G.Ω 1 → ℂ :=
  fun x => ∑ i, Rsc H (comp G v i) (comp G w i) x

theorem Rvec_eq (H : Matrix (G.Ω 1) (G.Ω 1) ℂ) (v w : G.Ω 1 × Fin N → ℂ) (x : G.Ω 1) :
    Rvec H v w x = (H *ᵥ fun y => ∑ i, v (y, i) * w (y, i)) x -
      ∑ i, v (x, i) * (liftOp N H *ᵥ w) (x, i) - ∑ i, w (x, i) * (liftOp N H *ᵥ v) (x, i) := by
  unfold Rvec Rsc
  simp only [Pi.sub_apply, Pi.mul_apply, Finset.sum_sub_distrib, Balaban.Multiscale.liftOp_mulVec]
  congr 2
  simp only [Matrix.mulVec, dotProduct, Balaban.Multiscale.comp, Pi.mul_apply, Finset.mul_sum]
  exact Finset.sum_comm

theorem Rvec_bound {a : ℕ → ℝ} (ha : IsAdmissibleWeights k a) {ν : ℝ} (hν0 : 0 ≤ ν)
    (hν : ν * ((L : ℝ) ^ k) ^ 2 ≤ 1) {α : G.Ω 1 → ℂ}
    (hα : ∀ x : G.Ω 1, G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 * ‖α x‖ ≤ 1)
    {v w : G.Ω 1 × Fin N → ℂ} {V W : ℝ} (hV : 0 ≤ V) (hW : 0 ≤ W)
    (hv : StarBound G v V) (hw : StarBound G w W) (x : G.Ω 1) :
    G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 * ‖Rvec (dirichletOperator G a ν α) v w x‖ ≤
      N * ((2 * d + 8) * (V * W)) := by
  have hνx : ν * G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 ≤ 1 := by
    refine le_trans (mul_le_mul_of_nonneg_left ?_ hν0) hν
    exact pow_le_pow_left₀ (spacing_pos G).le (spacing_le G x.2) 2
  have hxe : ∀ (s : G.Ω 1 × Fin N → ℂ) (i : Fin N),
      zeroExt (G.Ω 1) (comp G s i) (x : Torus d (N₀ * L ^ k)) = s (x, i) :=
    fun s i => zeroExt_mem _ _ _
  have hterm : ∀ i : Fin N, G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 *
      ‖Rsc (dirichletOperator G a ν α) (comp G v i) (comp G w i) x‖ ≤
      (2 * d + 8) * (V * W) := by
    intro i
    refine Rsc_bound ha hν0 hνx (hα x) hV hW (fun y => hv.val y i) (fun y => hw.val y i)
      (fun μ => ?_) (fun μ => ?_) (fun μ => ?_) (fun μ => ?_)
    · have := hv.fwd x x.2 μ i
      rwa [svec_of_mem] at this
    · have := hv.bwd x x.2 μ i
      rwa [svec_of_mem] at this
    · have := hw.fwd x x.2 μ i
      rwa [svec_of_mem] at this
    · have := hw.bwd x x.2 μ i
      rwa [svec_of_mem] at this
  unfold Rvec
  calc _ ≤ G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 *
        ∑ i, ‖Rsc (dirichletOperator G a ν α) (comp G v i) (comp G w i) x‖ :=
        mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ = ∑ i, G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 *
        ‖Rsc (dirichletOperator G a ν α) (comp G v i) (comp G w i) x‖ := by rw [Finset.mul_sum]
    _ ≤ ∑ _i : Fin N, (2 * d + 8) * (V * W) := Finset.sum_le_sum fun i _ => hterm i
    _ = _ := by simp

/-- **Lemma 3.1 (commutator).**  For `φ₀` with `IsSmoothField G δ₀ φ₀` and `s` with
`|s|₀, |∂s|₁ ≤ V`: `|K s|₂ ≤ C δ₀ V` where `K s = φ₀ · H s - H (φ₀ · s)` is `commK`
(`C = commKConst d L N = N(2dL + 1 + 4d)`; BACKGROUND.md has `(1 + 2d) δ₀ ‖v‖_*` for the Euclidean
norm). -/
theorem commK_bound (hd : 0 < d) (hL : 1 ≤ L) {a : ℕ → ℝ} (ha : IsAdmissibleWeights k a)
    (ν : ℝ) (α : G.Ω 1 → ℂ) {δ : ℝ} {φ : Torus d (N₀ * L ^ k) → Fin N → ℂ}
    (hφ : IsSmoothField G δ φ) (hδ : 0 ≤ δ) {s : G.Ω 1 × Fin N → ℂ} {V : ℝ} (hV : 0 ≤ V)
    (hs : StarBound G s V) (x : G.Ω 1) :
    G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 *
        ‖(commK (dirichletOperator G a ν α) (restrictField G φ) *ᵥ s) x‖ ≤
      commKConst d L N * δ * V := by
  have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
  exact commK_sup_bound G hd hL ha ν α hφ hδ s hV hs.val hs.fwd
    (fun x hx μ i => (hs.bwd x hx μ i).trans (le_mul_of_one_le_left hV hL')) x

end Vector

/-! ### The bridge to the landed Green's function bounds (BACKGROUND.md V-01) -/

section Bridge

/-- The coefficient `γ₁ = coerciveConst d / 2` of the polydisc of `α` on which `H_D(α)` is
invertible and the Green's function bounds hold: `|α|₂ ≤ γ₁` means `ℓ(x)² |α(x)| ≤ γ₁`. -/
noncomputable def gamma1 (d : ℕ) : ℝ := coerciveConst d / 2

/-- The standing hypotheses of the Green's function bound (G): `d ≥ 3`, `L ≥ 3`, mass
`0 ≤ ν ≤ L^{-2k}`, admissible weights, and the separation `2 d log L ≤ (agmonRate d / 4)(ϱ - 1)`
(the large-separation condition `ϱ ≥ R₀(d, L)`). -/
structure GreenSetting (G : GeneratingSet d L N₀ k ϱ) (a : ℕ → ℝ) (ν : ℝ) : Prop where
  hd : 3 ≤ d
  hL : 3 ≤ L
  mass : 0 ≤ ν
  massLe : ν * ((L : ℝ) ^ k) ^ 2 ≤ 1
  weights : IsAdmissibleWeights k a
  sep : 2 * d * Real.log L ≤ agmonRate d / 2 / 2 * (ϱ - 1)

variable {G : GeneratingSet d L N₀ k ϱ} {a : ℕ → ℝ} {ν : ℝ}

theorem GreenSetting.sep_gt_one (S : GreenSetting G a ν) : 1 < ϱ := by
  have hε := agmonRate_pos (d := d) (by have := S.hd; omega)
  have hL3 : (1 : ℝ) < L := by exact_mod_cast (by have := S.hL; omega : 1 < L)
  have hlog : 0 < Real.log L := Real.log_pos hL3
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by have := S.hd; omega : 0 < d)
  by_contra hcon
  push Not at hcon
  have : agmonRate d / 2 / 2 * (ϱ - 1) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
  have : 0 < 2 * d * Real.log L := by positivity
  linarith [S.sep]

/-- `α` lies in the polydisc `|α|₂ ≤ γ₁`. -/
theorem alpha_mem_polydisc {α : G.Ω 1 → ℂ} (h : ∀ x : G.Ω 1,
    G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 * ‖α x‖ ≤ gamma1 d) :
    ∀ x : G.Ω 1, ‖α x‖ ≤ coerciveConst d / (2 * G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2) := by
  intro x
  have hp : 0 < G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 := by
    have := spacing_pos G (x := (x : Torus d (N₀ * L ^ k)))
    positivity
  have := h x
  unfold gamma1 at this
  rw [le_div_iff₀ (by positivity)]
  nlinarith

theorem GreenSetting.isUnit (S : GreenSetting G a ν) {α : G.Ω 1 → ℂ}
    (hα : ∀ x : G.Ω 1, G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 * ‖α x‖ ≤ gamma1 d) :
    IsUnit (dirichletOperator G a ν α) :=
  dirichletOperator_isUnit G (by have := S.hd; omega) S.mass S.weights α (alpha_mem_polydisc hα)

/-- **The bridge lemma (V-01).**  For `|α|₂ ≤ γ₁` and a source `g` with `|g|₂ ≤ C_g`
(componentwise), `|Ĝ(α) g|₀, |∂ Ĝ(α) g|₁, |Δ^D Ĝ(α) g|₂ ≤ B C_g` with `B = greenSupConst d L`:
this is the landed `global_bound` applied to each component, with the wall bonds (factor `L`)
absorbed in `B = L B₁` and the vector norm taken componentwise (BACKGROUND.md (G)). -/
theorem GreenSetting.green_bound (S : GreenSetting G a ν) {α : G.Ω 1 → ℂ}
    (hα : ∀ x : G.Ω 1, G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 * ‖α x‖ ≤ gamma1 d)
    (g : G.Ω 1 × Fin N → ℂ) {Cg : ℝ} (hCg : 0 ≤ Cg)
    (hg : ∀ (x : G.Ω 1) (i : Fin N), G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 * ‖g (x, i)‖ ≤ Cg) :
    SupBounds G (liftOp N (dirichletOperator G a ν α)⁻¹ *ᵥ g) (greenSupConst d L * Cg) :=
  greenSupConst_spec S.hd S.hL G S.mass S.massLe S.weights (alpha_mem_polydisc hα) S.sep g hCg hg

/-- **Lemma 3.3 (resolvent differences).**  For `α, α'` in the polydisc `|α|₂ ≤ γ₁` with
`|α - α'|₂ ≤ Δ` and a source `g`, `|g|₂ ≤ C_g`:
`Ĝ(α) g - Ĝ(α') g = Ĝ(α) (-(α - α') Ĝ(α') g)` has `‖·‖_*, |Δ^D ·|₂ ≤ B² Δ C_g`. -/
theorem GreenSetting.green_sub_bound (S : GreenSetting G a ν) {α α' : G.Ω 1 → ℂ}
    (hα : ∀ x : G.Ω 1, G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 * ‖α x‖ ≤ gamma1 d)
    (hα' : ∀ x : G.Ω 1, G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 * ‖α' x‖ ≤ gamma1 d)
    (g : G.Ω 1 × Fin N → ℂ) {Cg Δ : ℝ} (hCg : 0 ≤ Cg)
    (hg : ∀ (x : G.Ω 1) (i : Fin N), G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 * ‖g (x, i)‖ ≤ Cg)
    (hΔ0 : 0 ≤ Δ)
    (hΔ : ∀ x : G.Ω 1, G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 * ‖α x - α' x‖ ≤ Δ) :
    SupBounds G ((liftOp N (dirichletOperator G a ν α)⁻¹ - liftOp N (dirichletOperator G a ν α')⁻¹) *ᵥ g)
      (greenSupConst d L * (Δ * (greenSupConst d L * Cg))) := by
  have hB := greenSupConst_nonneg d L
  have hd0 : 0 < d := by have := S.hd; omega
  set h : G.Ω 1 × Fin N → ℂ := fun p => -(α p.1 - α' p.1) *
    (liftOp N (dirichletOperator G a ν α')⁻¹ *ᵥ g) p with hh
  have hGg := S.green_bound hα' g hCg hg
  have hident : (liftOp N (dirichletOperator G a ν α)⁻¹ - liftOp N (dirichletOperator G a ν α')⁻¹) *ᵥ g =
      liftOp N (dirichletOperator G a ν α)⁻¹ *ᵥ h := by
    ext ⟨x, i⟩
    rw [Matrix.sub_mulVec, Pi.sub_apply, Balaban.Multiscale.liftOp_mulVec, Balaban.Multiscale.liftOp_mulVec,
      Balaban.Multiscale.liftOp_mulVec]
    have := congrFun (green_sub_eq_mulVec G hd0 S.mass S.weights α α' (alpha_mem_polydisc hα)
      (alpha_mem_polydisc hα') (fun z => g (z, i))) x
    rw [Pi.sub_apply] at this
    rw [this]
    congr 1
    ext y
    simp only [hh, Balaban.Multiscale.liftOp_mulVec]
  rw [hident]
  refine S.green_bound hα h (mul_nonneg hΔ0 (mul_nonneg hB hCg)) (fun x i => ?_)
  · have hv := hGg.val x i
    rw [svec_of_mem] at hv
    simp only [hh, norm_mul, norm_neg]
    calc G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 * (‖α x - α' x‖ *
          ‖(liftOp N (dirichletOperator G a ν α')⁻¹ *ᵥ g) (x, i)‖)
        = (G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 * ‖α x - α' x‖) *
          ‖(liftOp N (dirichletOperator G a ν α')⁻¹ *ᵥ g) (x, i)‖ := by ring
      _ ≤ Δ * (greenSupConst d L * Cg) := mul_le_mul (hΔ x) hv (norm_nonneg _) hΔ0

end Bridge

/-! ### Wall sites lie in layer 1, and the named norms -/

section Walls

variable {G : GeneratingSet d L N₀ k ϱ}

/-- **Wall sites are in layer 1** (BACKGROUND.md §1.1): a site of `Ω₁` with a neighbour outside
`Ω₁` (that is, in the collar) has layer index `1`, hence spacing `L`.  Needs the separation
`ϱ > 1` and `L ≥ 2`. -/
theorem layerIndex_eq_one_of_adj_not_mem (hϱ : 1 < ϱ) (hL : 2 ≤ L)
    {x x' : Torus d (N₀ * L ^ k)} (hx : x ∈ G.Ω 1) (hx' : x' ∉ G.Ω 1) (h : Adj x x') :
    G.layerIndex x = 1 := by
  obtain ⟨hj1, hjk, hxl⟩ := G.layerIndex_spec hx
  have hs := spacing_le_of_adj_not_mem G hϱ (by omega) hx hx' h
  rw [G.spacing_eq hj1 hjk hxl] at hs
  by_contra hne
  have hj2 : 2 ≤ G.layerIndex x := by omega
  have hL2 : (2 : ℝ) ≤ L := by exact_mod_cast hL
  have : (L : ℝ) ^ 2 ≤ (L : ℝ) ^ G.layerIndex x := pow_le_pow_right₀ (by linarith) hj2
  nlinarith

variable (G)

/-- The weighted sup norm `|f|_σ = sup_{x ∈ Ω₁, i} ℓ(x)^σ |f_i(x)|` of a vector field on `Ω₁`
(componentwise sup over the `N` components). -/
noncomputable def wnorm (σ : ℕ) (f : G.Ω 1 × Fin N → ℂ) : ℝ :=
  ⨆ p : G.Ω 1 × Fin N, G.spacing (p.1 : Torus d (N₀ * L ^ k)) ^ σ * ‖f p‖

/-- The bond norm `|∂u|₁ = sup ℓ(x) |ũ(x ± e_μ) - ũ(x)|` over bonds at points `x ∈ Ω₁`
(componentwise), with `ũ` the zero extension. -/
noncomputable def gradNorm1 (u : G.Ω 1 × Fin N → ℂ) : ℝ :=
  (⨆ q : G.Ω 1 × Fin d × Fin N, G.spacing (q.1 : Torus d (N₀ * L ^ k)) *
      ‖svec G u ((q.1 : Torus d (N₀ * L ^ k)) + Pi.single q.2.1 1) q.2.2 -
        svec G u (q.1 : Torus d (N₀ * L ^ k)) q.2.2‖) ⊔
    (⨆ q : G.Ω 1 × Fin d × Fin N, G.spacing (q.1 : Torus d (N₀ * L ^ k)) *
      ‖svec G u ((q.1 : Torus d (N₀ * L ^ k)) - Pi.single q.2.1 1) q.2.2 -
        svec G u (q.1 : Torus d (N₀ * L ^ k)) q.2.2‖)

variable {G}

theorem wnorm_le_iff {σ : ℕ} {f : G.Ω 1 × Fin N → ℂ} {V : ℝ} (hV : 0 ≤ V) :
    wnorm G σ f ≤ V ↔ ∀ (x : G.Ω 1) (i : Fin N),
      G.spacing (x : Torus d (N₀ * L ^ k)) ^ σ * ‖f (x, i)‖ ≤ V := by
  unfold wnorm
  constructor
  · intro h x i
    exact (le_ciSup (Set.finite_range _).bddAbove (x, i)).trans h
  · intro h
    exact Real.iSup_le (fun p => h p.1 p.2) hV

theorem gradNorm1_le_iff {u : G.Ω 1 × Fin N → ℂ} {V : ℝ} (hV : 0 ≤ V) :
    gradNorm1 G u ≤ V ↔ (∀ (x : G.Ω 1) (μ : Fin d) (i : Fin N),
      G.spacing (x : Torus d (N₀ * L ^ k)) *
        ‖svec G u ((x : Torus d (N₀ * L ^ k)) + Pi.single μ 1) i -
          svec G u (x : Torus d (N₀ * L ^ k)) i‖ ≤ V) ∧
    (∀ (x : G.Ω 1) (μ : Fin d) (i : Fin N), G.spacing (x : Torus d (N₀ * L ^ k)) *
        ‖svec G u ((x : Torus d (N₀ * L ^ k)) - Pi.single μ 1) i -
          svec G u (x : Torus d (N₀ * L ^ k)) i‖ ≤ V) := by
  unfold gradNorm1
  rw [sup_le_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun x μ i => (le_ciSup (Set.finite_range _).bddAbove (x, μ, i)).trans h1,
      fun x μ i => (le_ciSup (Set.finite_range _).bddAbove (x, μ, i)).trans h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨Real.iSup_le (fun q => h1 q.1 q.2.1 q.2.2) hV, Real.iSup_le (fun q => h2 q.1 q.2.1 q.2.2) hV⟩

/-- `StarBound` is `|u|₀ ≤ V` and `|∂u|₁ ≤ V` in terms of the named norms. -/
theorem starBound_iff {u : G.Ω 1 × Fin N → ℂ} {V : ℝ} (hV : 0 ≤ V) :
    StarBound G u V ↔ wnorm G 0 u ≤ V ∧ gradNorm1 G u ≤ V := by
  rw [wnorm_le_iff hV, gradNorm1_le_iff hV]
  constructor
  · intro h
    refine ⟨fun x i => ?_, fun x μ i => h.fwd x x.2 μ i, fun x μ i => h.bwd x x.2 μ i⟩
    have := h.val x i
    rw [svec_of_mem] at this
    simpa using this
  · rintro ⟨h0, h1, h2⟩
    refine ⟨fun y i => ?_, fun x hx μ i => h1 ⟨x, hx⟩ μ i, fun x hx μ i => h2 ⟨x, hx⟩ μ i⟩
    by_cases hy : y ∈ G.Ω 1
    · have := h0 ⟨y, hy⟩ i
      simpa [svec_of_mem G u ⟨y, hy⟩ i] using this
    · rw [svec_of_not_mem G u hy]
      simpa using hV
end Walls

end Balaban.Background
