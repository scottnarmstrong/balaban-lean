/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Background.ExistenceSetup
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Theorem 5.2 (3): the bounds P2 (1.15) for a field `φ₀ + δφ`

`BgBounds G D φ α c` collects the bounds of P2 (1.15) (BACKGROUND.md Theorem 5.2 (3)):
`|φ - Ψ|₀`, `|∂ φ̄|₁`, `|Δ φ̄|₂`, `|α|₂ ≤ c`, where `φ̄` is the extension of `φ` by the data `Ψ`
outside `Ω₁` (`barField`).  `bgBounds_of_parts` derives them for `φ = φ₀ + δφ` from the
smoothness and closeness of the approximate field `φ₀` (Lemma 5.3) and the sup bounds on the
increment `δφ` (Proposition 5.1).  The collar bonds enter through the fact that a site of `Ω₁`
adjacent to the collar has spacing `L`.
-/

@[expose] public section

namespace Balaban.Background

open Balaban.Multiscale Matrix Finset

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- **The bounds P2 (1.15)** (BACKGROUND.md Theorem 5.2 (3)) for a solution `(φ, α)`, with the
common constant `c`: `|φ - Ψ|₀ ≤ c`, `|∂φ̄|₁ ≤ c`, `|Δφ̄|₂ ≤ c` and `|α|₂ ≤ c`, with `φ̄ = barField`
the extension of `φ` by `Ψ` and `|g|_p = sup ℓ^p |g|`. -/
structure BgBounds (G : GeneratingSet d L N₀ k ϱ) (D : BgData G N) (φ : G.Ω 1 × Fin N → ℂ)
    (α : G.Ω 1 → ℂ) (c : ℝ) : Prop where
  val : ∀ x : G.Ω 1, vn (fun i => φ (x, i) - D.Ψ x i) ≤ c
  grad : ∀ (x : G.Ω 1) (μ : Fin d),
    vn (fun i => barField G D.Ψ φ ((x : Torus d (N₀ * L ^ k)) + Pi.single μ 1) i -
        barField G D.Ψ φ x i) ≤ c / G.spacing (x : Torus d (N₀ * L ^ k)) ∧
    vn (fun i => barField G D.Ψ φ ((x : Torus d (N₀ * L ^ k)) - Pi.single μ 1) i -
        barField G D.Ψ φ x i) ≤ c / G.spacing (x : Torus d (N₀ * L ^ k))
  lap : ∀ x : G.Ω 1, vn (fun i => ∑ μ : Fin d,
    (barField G D.Ψ φ ((x : Torus d (N₀ * L ^ k)) + Pi.single μ 1) i +
      barField G D.Ψ φ ((x : Torus d (N₀ * L ^ k)) - Pi.single μ 1) i -
      2 * barField G D.Ψ φ x i)) ≤ c / G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2
  alpha : Small G α c

section Parts

variable {G : GeneratingSet d L N₀ k ϱ} {D : BgData G N}
  {φ₀ : Torus d (N₀ * L ^ k) → Fin N → ℂ} {δφ : G.Ω 1 × Fin N → ℂ}

theorem bar_eq {y : Torus d (N₀ * L ^ k)} (hy : y ∈ dataSites G) (i : Fin N) :
    barField G D.Ψ (fun p => φ₀ p.1 p.2 + δφ p) y i =
      φ₀ y i + svec G δφ y i + (if y ∈ collar G then D.Ψ y i - φ₀ y i else 0) := by
  classical
  by_cases h1 : y ∈ G.Ω 1
  · have hc : y ∉ collar G := fun h => ((mem_collar G).1 h).1 h1
    have := svec_of_mem G δφ ⟨y, h1⟩ i
    simp only [barField, h1, hc, ite_false, dite_true, add_zero]
    rw [this]
  · have hc : y ∈ collar G := ((mem_dataSites G).1 hy).resolve_left h1
    simp only [barField, h1, hc, ite_true, dite_false]
    rw [svec_of_not_mem G δφ h1 i]; ring

theorem cterm_le {y : Torus d (N₀ * L ^ k)} {X ℓ : ℝ} (hX : 0 ≤ X) (hℓ : 0 < ℓ) (p : ℕ)
    (hΨ : y ∈ collar G → vn (φ₀ y - D.Ψ y) ≤ X) (hw : y ∈ collar G → ℓ = L) :
    vn (fun i => if y ∈ collar G then D.Ψ y i - φ₀ y i else 0) ≤ (L : ℝ) ^ p * X / ℓ ^ p := by
  classical
  by_cases hc : y ∈ collar G
  · simp only [hc, ite_true]
    have : vn (fun i => D.Ψ y i - φ₀ y i) = vn (φ₀ y - D.Ψ y) := vn_sub_comm _ _
    rw [this, hw hc]
    have hL : (0 : ℝ) < L := by rw [← hw hc]; exact hℓ
    rw [mul_div_cancel_left₀ _ (by positivity)]
    exact hΨ hc
  · simp only [hc, ite_false]
    have : (fun _ : Fin N => (0 : ℂ)) = (0 : Fin N → ℂ) := rfl
    rw [this, vn_zero]
    have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity

theorem grad_bound {x : G.Ω 1} {y : Torus d (N₀ * L ^ k)} (hy : y ∈ dataSites G) {X V : ℝ}
    (hX : 0 ≤ X) (hV : 0 ≤ V)
    (h0 : vn (φ₀ y - φ₀ x.1) ≤ X / G.spacing x.1)
    (hΨ : y ∈ collar G → vn (φ₀ y - D.Ψ y) ≤ X)
    (hfw : ∀ i, G.spacing x.1 * ‖svec G δφ y i - svec G δφ x.1 i‖ ≤ V)
    (hw : y ∈ collar G → G.spacing x.1 = L) :
    vn (fun i => barField G D.Ψ (fun p => φ₀ p.1 p.2 + δφ p) y i -
        barField G D.Ψ (fun p => φ₀ p.1 p.2 + δφ p) x.1 i) ≤
      ((1 + L) * X + N * V) / G.spacing x.1 := by
  have hℓ : 0 < G.spacing x.1 := spacing_pos G
  have hxd : x.1 ∈ dataSites G := (mem_dataSites G).2 (Or.inl x.2)
  have hxc : x.1 ∉ collar G := fun h => ((mem_collar G).1 h).1 x.2
  have e : (fun i => barField G D.Ψ (fun p => φ₀ p.1 p.2 + δφ p) y i -
        barField G D.Ψ (fun p => φ₀ p.1 p.2 + δφ p) x.1 i) =
      ((fun i => φ₀ y i - φ₀ x.1 i) + (fun i => svec G δφ y i - svec G δφ x.1 i)) +
        (fun i => if y ∈ collar G then D.Ψ y i - φ₀ y i else 0) := by
    funext i
    rw [bar_eq hy i, bar_eq hxd i]
    simp only [hxc, ite_false, Pi.add_apply]
    ring
  rw [e]
  have hA := vn_add (fun i => φ₀ y i - φ₀ x.1 i) (fun i => svec G δφ y i - svec G δφ x.1 i)
  have hA' : vn ((fun i => φ₀ y i - φ₀ x.1 i)) ≤ X / G.spacing x.1 := h0
  have hB : vn (fun i => svec G δφ y i - svec G δφ x.1 i) ≤ N * (V / G.spacing x.1) := by
    refine vn_le_card_mul (div_nonneg hV hℓ.le) fun i => ?_
    rw [le_div_iff₀ hℓ]; linarith [hfw i]
  have hC := cterm_le (G := G) (D := D) (φ₀ := φ₀) (y := y) hX hℓ 1 hΨ hw
  have hC' : vn (fun i => if y ∈ collar G then D.Ψ y i - φ₀ y i else 0) ≤ L * X / G.spacing x.1 := by
    simpa using hC
  have := vn_add ((fun i => φ₀ y i - φ₀ x.1 i) + (fun i => svec G δφ y i - svec G δφ x.1 i))
    (fun i => if y ∈ collar G then D.Ψ y i - φ₀ y i else 0)
  have e2 : ((1 + L) * X + N * V) / G.spacing x.1 =
      X / G.spacing x.1 + N * (V / G.spacing x.1) + L * X / G.spacing x.1 := by ring
  rw [e2]
  linarith

theorem lap_bound {x : G.Ω 1} {X V : ℝ} (hX : 0 ≤ X) (hV : 0 ≤ V)
    (hnb : ∀ μ : Fin d, (x : Torus d (N₀ * L ^ k)) + Pi.single μ 1 ∈ dataSites G ∧
      (x : Torus d (N₀ * L ^ k)) - Pi.single μ 1 ∈ dataSites G)
    (hs : vn (fun i => ∑ μ : Fin d, (φ₀ ((x : Torus d (N₀ * L ^ k)) + Pi.single μ 1) i +
      φ₀ ((x : Torus d (N₀ * L ^ k)) - Pi.single μ 1) i - 2 * φ₀ x i)) ≤
        X / G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2)
    (hΨ : ∀ y ∈ collar G, vn (φ₀ y - D.Ψ y) ≤ X)
    (hlap : ∀ i, G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 * ‖∑ μ : Fin d,
      (2 * svec G δφ x i - svec G δφ ((x : Torus d (N₀ * L ^ k)) + Pi.single μ 1) i -
        svec G δφ ((x : Torus d (N₀ * L ^ k)) - Pi.single μ 1) i)‖ ≤ V)
    (hw : ∀ y ∈ collar G, Adj (x : Torus d (N₀ * L ^ k)) y → G.spacing (x : Torus d (N₀ * L ^ k)) = L) :
    vn (fun i => ∑ μ : Fin d,
      (barField G D.Ψ (fun p => φ₀ p.1 p.2 + δφ p) ((x : Torus d (N₀ * L ^ k)) + Pi.single μ 1) i +
      barField G D.Ψ (fun p => φ₀ p.1 p.2 + δφ p) ((x : Torus d (N₀ * L ^ k)) - Pi.single μ 1) i -
      2 * barField G D.Ψ (fun p => φ₀ p.1 p.2 + δφ p) x i)) ≤
      ((1 + 2 * d * (L : ℝ) ^ 2) * X + N * V) / G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 := by
  classical
  set ℓ := G.spacing (x : Torus d (N₀ * L ^ k)) with hℓdef
  have hℓ : 0 < ℓ := spacing_pos G
  have hxd : (x : Torus d (N₀ * L ^ k)) ∈ dataSites G := (mem_dataSites G).2 (Or.inl x.2)
  have hxc : (x : Torus d (N₀ * L ^ k)) ∉ collar G := fun h => ((mem_collar G).1 h).1 x.2
  set cT : Torus d (N₀ * L ^ k) → Fin N → ℂ := fun y i =>
    if y ∈ collar G then D.Ψ y i - φ₀ y i else 0 with hcT
  have key : ∀ μ : Fin d, ∀ i,
      (barField G D.Ψ (fun p => φ₀ p.1 p.2 + δφ p) ((x : Torus d (N₀ * L ^ k)) + Pi.single μ 1) i +
      barField G D.Ψ (fun p => φ₀ p.1 p.2 + δφ p) ((x : Torus d (N₀ * L ^ k)) - Pi.single μ 1) i -
      2 * barField G D.Ψ (fun p => φ₀ p.1 p.2 + δφ p) x i) =
      (φ₀ ((x : Torus d (N₀ * L ^ k)) + Pi.single μ 1) i +
        φ₀ ((x : Torus d (N₀ * L ^ k)) - Pi.single μ 1) i - 2 * φ₀ x i) +
      (-(2 * svec G δφ x i - svec G δφ ((x : Torus d (N₀ * L ^ k)) + Pi.single μ 1) i -
        svec G δφ ((x : Torus d (N₀ * L ^ k)) - Pi.single μ 1) i)) +
      (cT ((x : Torus d (N₀ * L ^ k)) + Pi.single μ 1) i +
        cT ((x : Torus d (N₀ * L ^ k)) - Pi.single μ 1) i) := by
    intro μ i
    rw [bar_eq (hnb μ).1 i, bar_eq (hnb μ).2 i, bar_eq hxd i]
    simp only [hxc, ite_false, hcT]
    ring
  have e : (fun i => ∑ μ : Fin d,
      (barField G D.Ψ (fun p => φ₀ p.1 p.2 + δφ p) ((x : Torus d (N₀ * L ^ k)) + Pi.single μ 1) i +
      barField G D.Ψ (fun p => φ₀ p.1 p.2 + δφ p) ((x : Torus d (N₀ * L ^ k)) - Pi.single μ 1) i -
      2 * barField G D.Ψ (fun p => φ₀ p.1 p.2 + δφ p) x i)) =
      (fun i => ∑ μ : Fin d, (φ₀ ((x : Torus d (N₀ * L ^ k)) + Pi.single μ 1) i +
        φ₀ ((x : Torus d (N₀ * L ^ k)) - Pi.single μ 1) i - 2 * φ₀ x i)) +
      (fun i => -∑ μ : Fin d, (2 * svec G δφ x i -
        svec G δφ ((x : Torus d (N₀ * L ^ k)) + Pi.single μ 1) i -
        svec G δφ ((x : Torus d (N₀ * L ^ k)) - Pi.single μ 1) i)) +
      ∑ μ : Fin d, ((fun i => cT ((x : Torus d (N₀ * L ^ k)) + Pi.single μ 1) i) +
        (fun i => cT ((x : Torus d (N₀ * L ^ k)) - Pi.single μ 1) i)) := by
    funext i
    simp only [Pi.add_apply, Finset.sum_apply]
    rw [Finset.sum_congr rfl fun μ _ => key μ i, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_neg_distrib]
  rw [e]
  have hB : vn (fun i => -∑ μ : Fin d, (2 * svec G δφ x i -
        svec G δφ ((x : Torus d (N₀ * L ^ k)) + Pi.single μ 1) i -
        svec G δφ ((x : Torus d (N₀ * L ^ k)) - Pi.single μ 1) i)) ≤ N * (V / ℓ ^ 2) := by
    refine vn_le_card_mul (div_nonneg hV (by positivity)) fun i => ?_
    rw [norm_neg, le_div_iff₀ (by positivity)]
    linarith [hlap i]
  have hterm : ∀ y, Adj (x : Torus d (N₀ * L ^ k)) y →
      cNorm (fun i => cT y i) ≤ (L : ℝ) ^ 2 * X / ℓ ^ 2 := by
    intro y hy
    exact cterm_le (G := G) (D := D) (φ₀ := φ₀) (y := y) hX hℓ 2 (hΨ y) (fun hc => hw y hc hy)
  have hC : vn (∑ μ : Fin d, ((fun i => cT ((x : Torus d (N₀ * L ^ k)) + Pi.single μ 1) i) +
        (fun i => cT ((x : Torus d (N₀ * L ^ k)) - Pi.single μ 1) i))) ≤
      d * (2 * ((L : ℝ) ^ 2 * X / ℓ ^ 2)) := by
    refine (cNorm_sum_le _ _).trans ?_
    calc ∑ μ : Fin d, cNorm ((fun i => cT ((x : Torus d (N₀ * L ^ k)) + Pi.single μ 1) i) +
          (fun i => cT ((x : Torus d (N₀ * L ^ k)) - Pi.single μ 1) i))
        ≤ ∑ _μ : Fin d, (2 * ((L : ℝ) ^ 2 * X / ℓ ^ 2)) := by
          refine Finset.sum_le_sum fun μ _ => ?_
          refine (cNorm_add_le _ _).trans ?_
          have h1 := hterm _ (adj_add (x : Torus d (N₀ * L ^ k)) μ)
          have h2 := hterm _ (adj_sub (x : Torus d (N₀ * L ^ k)) μ)
          linarith
      _ = d * (2 * ((L : ℝ) ^ 2 * X / ℓ ^ 2)) := by simp
  have h1 := vn_add ((fun i => ∑ μ : Fin d, (φ₀ ((x : Torus d (N₀ * L ^ k)) + Pi.single μ 1) i +
        φ₀ ((x : Torus d (N₀ * L ^ k)) - Pi.single μ 1) i - 2 * φ₀ x i)) +
      (fun i => -∑ μ : Fin d, (2 * svec G δφ x i -
        svec G δφ ((x : Torus d (N₀ * L ^ k)) + Pi.single μ 1) i -
        svec G δφ ((x : Torus d (N₀ * L ^ k)) - Pi.single μ 1) i)))
    (∑ μ : Fin d, ((fun i => cT ((x : Torus d (N₀ * L ^ k)) + Pi.single μ 1) i) +
        (fun i => cT ((x : Torus d (N₀ * L ^ k)) - Pi.single μ 1) i)))
  have h2 := vn_add (fun i => ∑ μ : Fin d, (φ₀ ((x : Torus d (N₀ * L ^ k)) + Pi.single μ 1) i +
        φ₀ ((x : Torus d (N₀ * L ^ k)) - Pi.single μ 1) i - 2 * φ₀ x i))
      (fun i => -∑ μ : Fin d, (2 * svec G δφ x i -
        svec G δφ ((x : Torus d (N₀ * L ^ k)) + Pi.single μ 1) i -
        svec G δφ ((x : Torus d (N₀ * L ^ k)) - Pi.single μ 1) i))
  have e2 : ((1 + 2 * d * (L : ℝ) ^ 2) * X + N * V) / ℓ ^ 2 =
      X / ℓ ^ 2 + N * (V / ℓ ^ 2) + d * (2 * ((L : ℝ) ^ 2 * X / ℓ ^ 2)) := by ring
  rw [e2]
  linarith

theorem spacing_eq_L_of_collar (hϱ : 1 < ϱ) (hL : 2 ≤ L) {x : G.Ω 1}
    {y : Torus d (N₀ * L ^ k)} (hy : y ∈ collar G) (hxy : Adj x.1 y) : G.spacing x.1 = L := by
  have h := layerIndex_eq_one_of_adj_not_mem (G := G) hϱ hL x.2 ((mem_collar G).1 hy).1 hxy
  unfold GeneratingSet.spacing
  rw [h]; simp

/-- **Theorem 5.2 (3), bounds P2 (1.15)** for `φ = φ₀ + δφ`, from the properties of the
approximate field and the sup bounds on the increment (the constant is explicit). -/
theorem bgBounds_of_parts (hϱ : 1 < ϱ) (hL : 2 ≤ L) {X V c : ℝ} {α : G.Ω 1 → ℂ}
    (hX : 0 ≤ X) (hV : 0 ≤ V) (hs : IsSmoothField G X φ₀)
    (hdata : ∀ y ∈ dataSites G, vn (φ₀ y - D.Ψ y) ≤ X) (hsup : SupBounds G δφ V)
    (hα : Small G α c) (hc : (1 + L + 2 * d * (L : ℝ) ^ 2) * X + N * V ≤ c) :
    BgBounds G D (fun p => φ₀ p.1 p.2 + δφ p) α c := by
  have hnb : ∀ (x : G.Ω 1) (μ : Fin d), (x : Torus d (N₀ * L ^ k)) + Pi.single μ 1 ∈ dataSites G ∧
      (x : Torus d (N₀ * L ^ k)) - Pi.single μ 1 ∈ dataSites G := by
    intro x μ
    refine ⟨(mem_dataSites G).2 ?_, (mem_dataSites G).2 ?_⟩
    · by_cases h : (x : Torus d (N₀ * L ^ k)) + Pi.single μ 1 ∈ G.Ω 1
      · exact Or.inl h
      · exact Or.inr (mem_collar_of_adj G x.2 h (adj_add _ μ))
    · by_cases h : (x : Torus d (N₀ * L ^ k)) - Pi.single μ 1 ∈ G.Ω 1
      · exact Or.inl h
      · exact Or.inr (mem_collar_of_adj G x.2 h (adj_sub _ μ))
  have hcol : ∀ y ∈ collar G, y ∈ dataSites G := fun y hy => (mem_dataSites G).2 (Or.inr hy)
  have hℓ : ∀ x : G.Ω 1, 0 < G.spacing (x : Torus d (N₀ * L ^ k)) := fun x => spacing_pos G
  have hcpos : 0 ≤ (1 + L + 2 * d * (L : ℝ) ^ 2) * X + N * V := by positivity
  have hLpos : (0 : ℝ) ≤ L := by positivity
  refine ⟨fun x => ?_, fun x μ => ⟨?_, ?_⟩, fun x => ?_, hα⟩
  · have hxd : (x : Torus d (N₀ * L ^ k)) ∈ dataSites G := (mem_dataSites G).2 (Or.inl x.2)
    have e : (fun i => (φ₀ x i + δφ (x, i)) - D.Ψ x i) =
        (φ₀ x - D.Ψ x) + (fun i => svec G δφ x i) := by
      funext i
      simp only [Pi.add_apply, Pi.sub_apply, svec_of_mem G δφ x i]
      ring
    show vn (fun i => (φ₀ x i + δφ (x, i)) - D.Ψ x i) ≤ c
    rw [e]
    have h1 := vn_add (φ₀ x - D.Ψ x) (fun i => svec G δφ x i)
    have h2 : vn (fun i => svec G δφ x i) ≤ N * V :=
      vn_le_card_mul hV fun i => hsup.val x i
    have h3 := hdata x hxd
    have : (1 + L + 2 * d * (L : ℝ) ^ 2) * X ≥ X := by
      have : (0 : ℝ) ≤ L + 2 * d * (L : ℝ) ^ 2 := by positivity
      nlinarith
    linarith
  · have := grad_bound (G := G) (D := D) (φ₀ := φ₀) (δφ := δφ) (hnb x μ).1 hX hV
      (hs.grad x x.2 μ).1 (fun hc => hdata _ (hcol _ hc)) (fun i => hsup.fwd x x.2 μ i)
      (fun hc => spacing_eq_L_of_collar hϱ hL hc (adj_add _ μ))
    refine this.trans (div_le_div_of_nonneg_right ?_ (hℓ x).le)
    nlinarith [mul_nonneg hLpos hX, mul_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ d)
      (sq_nonneg (L : ℝ))) hX]
  · have := grad_bound (G := G) (D := D) (φ₀ := φ₀) (δφ := δφ) (hnb x μ).2 hX hV
      (hs.grad x x.2 μ).2 (fun hc => hdata _ (hcol _ hc)) (fun i => hsup.bwd x x.2 μ i)
      (fun hc => spacing_eq_L_of_collar hϱ hL hc (adj_sub _ μ))
    refine this.trans (div_le_div_of_nonneg_right ?_ (hℓ x).le)
    nlinarith [mul_nonneg hLpos hX, mul_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ d)
      (sq_nonneg (L : ℝ))) hX]
  · have := lap_bound (G := G) (D := D) (φ₀ := φ₀) (δφ := δφ) hX hV (hnb x) (hs.lap x x.2)
      (fun y hy => hdata _ (hcol _ hy)) (fun i => hsup.lap x x.2 i)
      (fun y hy hxy => spacing_eq_L_of_collar hϱ hL hy hxy)
    refine this.trans (div_le_div_of_nonneg_right ?_ (by have := hℓ x; positivity))
    nlinarith [mul_nonneg hLpos hX]

end Parts

end Balaban.Background
