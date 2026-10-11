/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Background.MinimizerAlg
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The quadratic expansion of the action (BACKGROUND.md (5.3))

`actionC` is the action with the norms `‖z‖²` replaced by the bilinear products `z * z`; it
equals `action` on real data and real fields (`action_cast`, in `Minimizer.lean`).  The expansion
`actionC_add`: for all complex fields `φ, τ` on `Ω₁`,
`A(φ + τ) - A(φ) = ½ ⟨τ, H_D(0) τ⟩ + ⟨τ, H_D(0) φ - S⟩`
with the bilinear pairing `⟨u, v⟩ = ∑_{x, i} u(x, i) v(x, i)`.  The proof treats the three terms of
the action separately: the block term by `blk_sum_comm`, the bond term by `bond_sum_by_parts`.
-/

@[expose] public section

namespace Balaban.Background

open Balaban.Multiscale Matrix Finset

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

variable (G : GeneratingSet d L N₀ k ϱ) (a : ℕ → ℝ) (ν : ℝ)

/-- The bilinear pairing `⟨u, v⟩ = ∑_{x, i} u(x, i) v(x, i)` of fields on `Ω₁`. -/
def pair (u v : G.Ω 1 × Fin N → ℂ) : ℂ := ∑ p, u p * v p

/-- **The action with products in place of norms squared** (complex-valued; see `action`). -/
noncomputable def actionC (D : BgData G N) (φ : G.Ω 1 × Fin N → ℂ) : ℂ :=
  (1 / 2) * ∑ x : G.Ω 1, ((a (G.layerIndex (x : Torus d (N₀ * L ^ k))) /
      ((L : ℝ) ^ G.layerIndex (x : Torus d (N₀ * L ^ k))) ^ 2 : ℝ) : ℂ) *
      ∑ i, (D.Ψ x i - blockAvg G φ x i) * (D.Ψ x i - blockAvg G φ x i) +
  (1 / 2) * ∑ x : Torus d (N₀ * L ^ k), ∑ μ : Fin d,
      (if x ∈ G.Ω 1 ∨ x + Pi.single μ 1 ∈ G.Ω 1 then
        ∑ i, (barField G D.Ψ φ (x + Pi.single μ 1) i - barField G D.Ψ φ x i) *
          (barField G D.Ψ φ (x + Pi.single μ 1) i - barField G D.Ψ φ x i) else 0) +
  (ν : ℂ) / 2 * ∑ x : G.Ω 1, ∑ i, (φ (x, i) - D.h x i) * (φ (x, i) - D.h x i)

variable {G a ν}

theorem blockAvg_add (u v : G.Ω 1 × Fin N → ℂ) (x : Torus d (N₀ * L ^ k)) (i : Fin N) :
    blockAvg G (u + v) x i = blockAvg G u x i + blockAvg G v x i := by
  unfold blockAvg
  simp only [svec_add, Finset.sum_add_distrib, mul_add]

theorem barField_add (Ψ : Torus d (N₀ * L ^ k) → Fin N → ℂ) (u v : G.Ω 1 × Fin N → ℂ)
    (y : Torus d (N₀ * L ^ k)) (i : Fin N) :
    barField G Ψ (u + v) y i = barField G Ψ u y i + svec G v y i := by
  classical
  by_cases hy : y ∈ G.Ω 1
  · have h2 := svec_of_mem G v ⟨y, hy⟩ i
    simp only [barField, hy, dite_true, Pi.add_apply]
    simp only at h2
    rw [h2]
  · simp only [barField, hy, dite_false]
    rw [svec_of_not_mem G _ hy, add_zero]

/-- `Q φ` is constant on blocks. -/
theorem blockAvg_blockConst (φ : G.Ω 1 × Fin N → ℂ) (i : Fin N) :
    ∀ x ∈ G.Ω 1, ∀ y ∈ G.blk (G.layerIndex x) x,
      blockAvg G φ y i = blockAvg G φ x i := by
  intro x hx y hy
  have h := (mem_blk_iff G hx).1 hy
  have hb : G.blk (G.layerIndex x) y = G.blk (G.layerIndex x) x := by
    ext z
    rw [GeneratingSet.mem_blk, GeneratingSet.mem_blk, GeneratingSet.mem_blk.1 hy]
  unfold blockAvg
  rw [h.2.1, hb]

section Block

variable (G a)

/-- The block term `Q* a Q` applied to each component of a field on `Ω₁` (zero extended). -/
noncomputable def blockVec (u : G.Ω 1 × Fin N → ℂ) : G.Ω 1 × Fin N → ℂ := fun p =>
  blockTerm G a (zeroExt (G.Ω 1) (fun z => u (z, p.2))) p.1

/-- The lattice Laplacian `-Δ` applied to each component of a field on `Ω₁` (zero extended). -/
noncomputable def lapVec (u : G.Ω 1 × Fin N → ℂ) : G.Ω 1 × Fin N → ℂ := fun p =>
  negLap (zeroExt (G.Ω 1) (fun z => u (z, p.2))) p.1

variable {G a}

theorem sum_blockAvg {g : Fin N → Torus d (N₀ * L ^ k) → ℂ}
    (hg : ∀ i, ∀ x ∈ G.Ω 1, ∀ y ∈ G.blk (G.layerIndex x) x, g i y = g i x)
    (u : G.Ω 1 × Fin N → ℂ) :
    ∑ x : G.Ω 1, ((a (G.layerIndex (x : Torus d (N₀ * L ^ k))) /
        ((L : ℝ) ^ G.layerIndex (x : Torus d (N₀ * L ^ k))) ^ 2 : ℝ) : ℂ) *
      ∑ i, g i x * blockAvg G u x i =
    ∑ p : G.Ω 1 × Fin N, ((a (G.layerIndex (p.1 : Torus d (N₀ * L ^ k))) /
        ((L : ℝ) ^ G.layerIndex (p.1 : Torus d (N₀ * L ^ k))) ^ 2 : ℝ) : ℂ) * g p.2 p.1 * u p := by
  rw [Fintype.sum_prod_type_right]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h := blk_sum_comm G a (g i) (fun y => svec G u y i) (hg i)
  simp only [svec_of_mem G u _ i] at h
  unfold blockAvg
  rw [← h]
  refine Finset.sum_congr rfl fun x _ => ?_
  ring

/-- **The block term of the action**: expansion in `τ`. -/
theorem blockPart (D : BgData G N) (φ τ : G.Ω 1 × Fin N → ℂ) :
    (1 / 2) * ∑ x : G.Ω 1, ((a (G.layerIndex (x : Torus d (N₀ * L ^ k))) /
      ((L : ℝ) ^ G.layerIndex (x : Torus d (N₀ * L ^ k))) ^ 2 : ℝ) : ℂ) *
      ∑ i, (D.Ψ x i - blockAvg G (φ + τ) x i) * (D.Ψ x i - blockAvg G (φ + τ) x i) -
    (1 / 2) * ∑ x : G.Ω 1, ((a (G.layerIndex (x : Torus d (N₀ * L ^ k))) /
      ((L : ℝ) ^ G.layerIndex (x : Torus d (N₀ * L ^ k))) ^ 2 : ℝ) : ℂ) *
      ∑ i, (D.Ψ x i - blockAvg G φ x i) * (D.Ψ x i - blockAvg G φ x i) =
    -pair G τ (qStar G a D.Ψ) + pair G τ (blockVec G a φ) + (1 / 2) * pair G τ (blockVec G a τ) := by
  have hΨ : ∀ i, ∀ x ∈ G.Ω 1, ∀ y ∈ G.blk (G.layerIndex x) x, D.Ψ y i = D.Ψ x i := by
    intro i x hx y hy
    obtain ⟨hn1, hnk, hxl⟩ := G.layerIndex_spec hx
    have := D.Ψ_layerConst (G.layerIndex x) hn1 hnk x hxl y hy
    rw [this]
  have eA := sum_blockAvg (a := a) (g := fun i y => D.Ψ y i) hΨ τ
  have eB := sum_blockAvg (a := a) (g := fun i y => blockAvg G φ y i)
    (fun i => blockAvg_blockConst φ i) τ
  have eC := sum_blockAvg (a := a) (g := fun i y => blockAvg G τ y i)
    (fun i => blockAvg_blockConst τ i) τ
  have hpair : ∀ v : G.Ω 1 × Fin N → ℂ, pair G τ v = ∑ p, v p * τ p := fun v => by
    unfold pair; exact Finset.sum_congr rfl fun p _ => mul_comm _ _
  rw [hpair, hpair, hpair]
  have eq1 : ∑ p : G.Ω 1 × Fin N, qStar G a D.Ψ p * τ p =
      ∑ p : G.Ω 1 × Fin N, ((a (G.layerIndex (p.1 : Torus d (N₀ * L ^ k))) /
        ((L : ℝ) ^ G.layerIndex (p.1 : Torus d (N₀ * L ^ k))) ^ 2 : ℝ) : ℂ) * D.Ψ p.1 p.2 * τ p :=
    rfl
  have eq2 : ∑ p : G.Ω 1 × Fin N, blockVec G a φ p * τ p =
      ∑ p : G.Ω 1 × Fin N, ((a (G.layerIndex (p.1 : Torus d (N₀ * L ^ k))) /
        ((L : ℝ) ^ G.layerIndex (p.1 : Torus d (N₀ * L ^ k))) ^ 2 : ℝ) : ℂ) *
          blockAvg G φ p.1 p.2 * τ p := rfl
  have eq3 : ∑ p : G.Ω 1 × Fin N, blockVec G a τ p * τ p =
      ∑ p : G.Ω 1 × Fin N, ((a (G.layerIndex (p.1 : Torus d (N₀ * L ^ k))) /
        ((L : ℝ) ^ G.layerIndex (p.1 : Torus d (N₀ * L ^ k))) ^ 2 : ℝ) : ℂ) *
          blockAvg G τ p.1 p.2 * τ p := rfl
  rw [eq1, eq2, eq3, ← eA, ← eB, ← eC]
  simp only [blockAvg_add, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib,
    neg_add_eq_sub]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ => ?_
  ring

end Block

section Bond

theorem bar_nbr (D : BgData G N) (φ : G.Ω 1 × Fin N → ℂ) {y : Torus d (N₀ * L ^ k)}
    (hy : y ∈ dataSites G) (i : Fin N) :
    barField G D.Ψ φ y i = svec G φ y i + (if y ∈ collar G then D.Ψ y i else 0) := by
  classical
  by_cases h1 : y ∈ G.Ω 1
  · have hc : y ∉ collar G := fun h => ((mem_collar G).1 h).1 h1
    have := svec_of_mem G φ ⟨y, h1⟩ i
    simp only [barField, h1, dite_true, hc, ite_false, add_zero]
    rw [this]
  · have hc : y ∈ collar G := ((mem_dataSites G).1 hy).resolve_left h1
    simp only [barField, h1, dite_false, hc, ite_true]
    rw [svec_of_not_mem G _ h1, zero_add]

theorem lap_bar (D : BgData G N) (φ : G.Ω 1 × Fin N → ℂ) (x : G.Ω 1) (i : Fin N) :
    ∑ μ : Fin d, (2 * barField G D.Ψ φ (x : Torus d (N₀ * L ^ k)) i -
        barField G D.Ψ φ ((x : Torus d (N₀ * L ^ k)) + Pi.single μ 1) i -
        barField G D.Ψ φ ((x : Torus d (N₀ * L ^ k)) - Pi.single μ 1) i) =
      lapVec G φ (x, i) - boundaryTerm G D.Ψ (x, i) := by
  have hnb : ∀ y, Adj (x : Torus d (N₀ * L ^ k)) y → y ∈ dataSites G := fun y hy => by
    by_cases h : y ∈ G.Ω 1
    · exact (mem_dataSites G).2 (Or.inl h)
    · exact (mem_dataSites G).2 (Or.inr (mem_collar_of_adj G x.2 h hy))
  have hxd : (x : Torus d (N₀ * L ^ k)) ∈ dataSites G := (mem_dataSites G).2 (Or.inl x.2)
  unfold lapVec boundaryTerm negLap
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [bar_nbr D φ hxd i, bar_nbr D φ (hnb _ (adj_add _ μ)) i, bar_nbr D φ (hnb _ (adj_sub _ μ)) i]
  have hxc : (x : Torus d (N₀ * L ^ k)) ∉ collar G := fun h => ((mem_collar G).1 h).1 x.2
  simp only [hxc, ite_false, add_zero]
  show _ = _ - _
  simp only [svec]
  ring

/-- **The bond term of the action**: expansion in `τ`. -/
theorem bondPart (D : BgData G N) (φ τ : G.Ω 1 × Fin N → ℂ) :
    (1 / 2) * ∑ x : Torus d (N₀ * L ^ k), ∑ μ : Fin d,
      (if x ∈ G.Ω 1 ∨ x + Pi.single μ 1 ∈ G.Ω 1 then
        ∑ i, (barField G D.Ψ (φ + τ) (x + Pi.single μ 1) i - barField G D.Ψ (φ + τ) x i) *
          (barField G D.Ψ (φ + τ) (x + Pi.single μ 1) i - barField G D.Ψ (φ + τ) x i) else 0) -
    (1 / 2) * ∑ x : Torus d (N₀ * L ^ k), ∑ μ : Fin d,
      (if x ∈ G.Ω 1 ∨ x + Pi.single μ 1 ∈ G.Ω 1 then
        ∑ i, (barField G D.Ψ φ (x + Pi.single μ 1) i - barField G D.Ψ φ x i) *
          (barField G D.Ψ φ (x + Pi.single μ 1) i - barField G D.Ψ φ x i) else 0) =
    pair G τ (lapVec G φ) - pair G τ (boundaryTerm G D.Ψ) + (1 / 2) * pair G τ (lapVec G τ) := by
  classical
  -- Step 1: the difference of the integrands.
  have step1 : ∀ (x : Torus d (N₀ * L ^ k)) (μ : Fin d),
      (if x ∈ G.Ω 1 ∨ x + Pi.single μ 1 ∈ G.Ω 1 then
        ∑ i, (barField G D.Ψ (φ + τ) (x + Pi.single μ 1) i - barField G D.Ψ (φ + τ) x i) *
          (barField G D.Ψ (φ + τ) (x + Pi.single μ 1) i - barField G D.Ψ (φ + τ) x i) else 0) -
      (if x ∈ G.Ω 1 ∨ x + Pi.single μ 1 ∈ G.Ω 1 then
        ∑ i, (barField G D.Ψ φ (x + Pi.single μ 1) i - barField G D.Ψ φ x i) *
          (barField G D.Ψ φ (x + Pi.single μ 1) i - barField G D.Ψ φ x i) else 0) =
      ∑ i, (2 * ((barField G D.Ψ φ (x + Pi.single μ 1) i - barField G D.Ψ φ x i) *
          (svec G τ (x + Pi.single μ 1) i - svec G τ x i)) +
        (svec G τ (x + Pi.single μ 1) i - svec G τ x i) *
          (svec G τ (x + Pi.single μ 1) i - svec G τ x i)) := by
    intro x μ
    by_cases hF : x ∈ G.Ω 1 ∨ x + Pi.single μ 1 ∈ G.Ω 1
    · simp only [hF, ite_true, barField_add, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    · have h1 : x ∉ G.Ω 1 := fun h => hF (Or.inl h)
      have h2 : x + Pi.single μ 1 ∉ G.Ω 1 := fun h => hF (Or.inr h)
      simp [hF, svec_of_not_mem G _ h1, svec_of_not_mem G _ h2]
  have hL : ∀ (A' A : Torus d (N₀ * L ^ k) → Fin d → ℂ) (B : Torus d (N₀ * L ^ k) → Fin d → ℂ),
      (∀ x μ, A' x μ - A x μ = B x μ) →
      (1 / 2 : ℂ) * ∑ x, ∑ μ, A' x μ - (1 / 2 : ℂ) * ∑ x, ∑ μ, A x μ =
        (1 / 2 : ℂ) * ∑ x, ∑ μ, B x μ := by
    intro A' A B h
    rw [← mul_sub, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun μ _ => h x μ
  rw [hL _ _ (fun x μ => ∑ i, (2 * ((barField G D.Ψ φ (x + Pi.single μ 1) i - barField G D.Ψ φ x i) *
          (svec G τ (x + Pi.single μ 1) i - svec G τ x i)) +
        (svec G τ (x + Pi.single μ 1) i - svec G τ x i) *
          (svec G τ (x + Pi.single μ 1) i - svec G τ x i))) step1]
  have hsw : ∀ f : Torus d (N₀ * L ^ k) → Fin d → Fin N → ℂ,
      ∑ x, ∑ μ, ∑ i, f x μ i = ∑ i, ∑ x, ∑ μ, f x μ i := by
    intro f
    calc _ = ∑ x, ∑ i, ∑ μ, f x μ i := Finset.sum_congr rfl fun x _ => Finset.sum_comm
      _ = _ := Finset.sum_comm
  rw [hsw]
  -- per component
  have hB : ∀ i : Fin N, ∑ x : Torus d (N₀ * L ^ k), ∑ μ : Fin d,
      (barField G D.Ψ φ (x + Pi.single μ 1) i - barField G D.Ψ φ x i) *
        (svec G τ (x + Pi.single μ 1) i - svec G τ x i) =
      ∑ x : G.Ω 1, τ (x, i) * (lapVec G φ (x, i) - boundaryTerm G D.Ψ (x, i)) := by
    intro i
    rw [bond_sum_by_parts (fun y => barField G D.Ψ φ y i) (fun y => svec G τ y i)]
    rw [Green.sum_eq_sum_subtype (G.Ω 1) _ (fun x hx => by simp [svec_of_not_mem G _ hx])]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [svec_of_mem G τ x i, lap_bar D φ x i]
  have hT : ∀ i : Fin N, ∑ x : Torus d (N₀ * L ^ k), ∑ μ : Fin d,
      (svec G τ (x + Pi.single μ 1) i - svec G τ x i) *
        (svec G τ (x + Pi.single μ 1) i - svec G τ x i) =
      ∑ x : G.Ω 1, τ (x, i) * lapVec G τ (x, i) := by
    intro i
    rw [bond_sum_by_parts (fun y => svec G τ y i) (fun y => svec G τ y i)]
    rw [Green.sum_eq_sum_subtype (G.Ω 1) _ (fun x hx => by simp [svec_of_not_mem G _ hx])]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← svec_of_mem G τ x i]
    rfl
  have hpair : ∀ v : G.Ω 1 × Fin N → ℂ, pair G τ v = ∑ i : Fin N, ∑ x : G.Ω 1, τ (x, i) * v (x, i) :=
    fun v => by
      unfold pair
      rw [Fintype.sum_prod_type_right]
  rw [hpair, hpair, hpair]
  have hI : ∀ i : Fin N, ∑ x : Torus d (N₀ * L ^ k), ∑ μ : Fin d,
      (2 * ((barField G D.Ψ φ (x + Pi.single μ 1) i - barField G D.Ψ φ x i) *
          (svec G τ (x + Pi.single μ 1) i - svec G τ x i)) +
        (svec G τ (x + Pi.single μ 1) i - svec G τ x i) *
          (svec G τ (x + Pi.single μ 1) i - svec G τ x i)) =
      2 * ∑ x : G.Ω 1, τ (x, i) * (lapVec G φ (x, i) - boundaryTerm G D.Ψ (x, i)) +
        ∑ x : G.Ω 1, τ (x, i) * lapVec G τ (x, i) := by
    intro i
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hB i, hT i]
  rw [Finset.sum_congr rfl fun i _ => hI i]
  simp only [mul_sub, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

end Bond

section Total

theorem H0_apply (u : G.Ω 1 × Fin N → ℂ) (p : G.Ω 1 × Fin N) :
    (liftOp N (dirichletOperator G a ν 0) *ᵥ u) p =
      lapVec G u p + blockVec G a u p + (ν : ℂ) * u p := by
  obtain ⟨x, i⟩ := p
  rw [liftOp_mulVec, dirichlet_apply]
  simp [lapVec, blockVec]

theorem pair_add_right (u v w : G.Ω 1 × Fin N → ℂ) :
    pair G u (v + w) = pair G u v + pair G u w := by
  unfold pair
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem pair_sub_right (u v w : G.Ω 1 × Fin N → ℂ) :
    pair G u (v - w) = pair G u v - pair G u w := by
  unfold pair
  simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem pair_smul_right (u v : G.Ω 1 × Fin N → ℂ) (c : ℂ) :
    pair G u (fun p => c * v p) = c * pair G u v := by
  unfold pair
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun p _ => by ring

/-- **The quadratic expansion of the action** (for all complex fields):
`A(φ + τ) - A(φ) = ½ ⟨τ, H_D(0) τ⟩ + ⟨τ, H_D(0) φ - S⟩`. -/
theorem actionC_add (D : BgData G N) (φ τ : G.Ω 1 × Fin N → ℂ) :
    actionC G a ν D (φ + τ) - actionC G a ν D φ =
      (1 / 2) * pair G τ (liftOp N (dirichletOperator G a ν 0) *ᵥ τ) +
        pair G τ (liftOp N (dirichletOperator G a ν 0) *ᵥ φ - source G a ν D) := by
  have e1 := blockPart (a := a) D φ τ
  have e2 := bondPart D φ τ
  have e3 : (ν : ℂ) / 2 * ∑ x : G.Ω 1, ∑ i, ((φ + τ) (x, i) - D.h x i) * ((φ + τ) (x, i) - D.h x i) -
      (ν : ℂ) / 2 * ∑ x : G.Ω 1, ∑ i, (φ (x, i) - D.h x i) * (φ (x, i) - D.h x i) =
      (ν : ℂ) * (pair G τ φ - pair G τ (fun p => D.h p.1 p.2)) + (ν : ℂ) / 2 * pair G τ τ := by
    unfold pair
    simp only [Fintype.sum_prod_type, Pi.add_apply, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ => ?_
    ring
  have hH : ∀ v, pair G τ (liftOp N (dirichletOperator G a ν 0) *ᵥ v) =
      pair G τ (lapVec G v) + pair G τ (blockVec G a v) + (ν : ℂ) * pair G τ v := by
    intro v
    have : liftOp N (dirichletOperator G a ν 0) *ᵥ v =
        lapVec G v + blockVec G a v + fun p => (ν : ℂ) * v p := funext fun p => by
      rw [H0_apply]; rfl
    rw [this, pair_add_right, pair_add_right, pair_smul_right]
  have hS : pair G τ (source G a ν D) = pair G τ (qStar G a D.Ψ) +
      (ν : ℂ) * pair G τ (fun p => D.h p.1 p.2) + pair G τ (boundaryTerm G D.Ψ) := by
    have : source G a ν D = qStar G a D.Ψ + (fun p => (ν : ℂ) * D.h p.1 p.2) +
        boundaryTerm G D.Ψ := rfl
    rw [this, pair_add_right, pair_add_right, pair_smul_right]
  rw [pair_sub_right, hH, hH, hS]
  unfold actionC
  linear_combination e1 + e2 + e3

end Total

end Balaban.Background
