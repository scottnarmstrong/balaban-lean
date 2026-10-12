/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.ExpansionLocal
public import Balaban.Fluctuation.ExpansionBounds
public import Balaban.SmallField.Xi
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.LinearCombination

/-!
# Lemma 2.5, the tests of `χ_k` (FLUCTUATION.md §2.5)

The tests of `χ_{k+1,u}` for `θ` (`ChiUBounds`: `|θ - Qφ| < 3/2 δ`, `ℓ|∂φ|, ℓ²|Δφ|, ℓ²|α| < δ/2`,
`√ν ℓ |φ - h| < δ/2`) imply the inequalities of `Ξ_k(𝔹; 1, δ)` (`XiBounds`) for `ψ = ψ^{(k)} + ψ'`
once `‖φ_k(ψ) - φ_{k+1}‖_*, |α_k(ψ) - α_{k+1}|₂ ≤ V` (Lemma 2.3 (d)), `√N V ≤ δ/3` and
`|ψ'| ≤ t ≤ δ/3` (`xiBounds_of_perturb`), each test checked against its own threshold, in the fine
units of the level-`n` and level-`(n+1)` generating sets (`ℓ_{n+1} = L ℓ_n`).
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban.Multiscale Balaban.Background Balaban.SmallField Finset Matrix

variable {d L N₀ K N : ℕ} [NeZero N₀] [NeZero L] {ϱ ϱ' : ℝ}
  {G : GeneratingSet d L N₀ K ϱ} {G' : GeneratingSet d L N₀ K ϱ'} {n : ℕ}

theorem IsLevel.layerIndex_eq (hG : IsLevel G n) (x : Torus d (N₀ * L ^ K)) :
    G.layerIndex x = n := (hG x).2

theorem IsLevel.spacing_eq (hG : IsLevel G n) (x : Torus d (N₀ * L ^ K)) :
    G.spacing x = (L : ℝ) ^ n := by
  obtain ⟨hj1, hjk, hxl⟩ := G.layerIndex_spec (hG x).1
  rw [G.spacing_eq hj1 hjk hxl, (hG x).2]

theorem IsLevel.collar_eq (hG : IsLevel G n) : collar G = ∅ := by
  ext x
  rw [mem_collar]
  simp [(hG x).1]

theorem vn_le_sqrt_mul {v : Fin N → ℂ} {V : ℝ} (hV : 0 ≤ V) (h : ∀ i, ‖v i‖ ≤ V) :
    vn v ≤ Real.sqrt N * V := by
  rw [vn_eq_sqrt]
  calc Real.sqrt (∑ i, ‖v i‖ ^ 2) ≤ Real.sqrt (∑ _i : Fin N, V ^ 2) := by
        apply Real.sqrt_le_sqrt
        exact Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (h i) 2
    _ = Real.sqrt N * V := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          Real.sqrt_mul (Nat.cast_nonneg N), Real.sqrt_sq hV]


/-- The five tests of `χ_{k+1,u}` (FLUCTUATION Lemma 2.5), in fine units of the level-`(n+1)`
generating set `G'`: `|θ - Q φ| < 3/2 δ`, `ℓ |∂φ|, ℓ² |Δφ|, ℓ² |α| < δ/2`, and (mass) `√ν ℓ |φ - h| < δ/2`
(void in the `ν`-free convention, `ν = 0`). -/
structure ChiUBounds (G' : GeneratingSet d L N₀ K ϱ') (ν δ : ℝ) {N : ℕ} (D' : BgData G' N)
    (φ₁ : G'.Ω 1 × Fin N → ℂ) (α₁ : G'.Ω 1 → ℂ) : Prop where
  close : ∀ x ∈ G'.Ω 1, vn (fun i => D'.Ψ x i - blockAvg G' φ₁ x i) < 3 / 2 * δ
  grad : ∀ x ∈ G'.Ω 1, ∀ μ : Fin d,
    vn (fun i => barField G' D'.Ψ φ₁ (x + Pi.single μ 1) i - barField G' D'.Ψ φ₁ x i) <
      δ / 2 / G'.spacing x ∧
    vn (fun i => barField G' D'.Ψ φ₁ (x - Pi.single μ 1) i - barField G' D'.Ψ φ₁ x i) <
      δ / 2 / G'.spacing x
  lap : ∀ x ∈ G'.Ω 1, vn (fun i => ∑ μ : Fin d,
    (barField G' D'.Ψ φ₁ (x + Pi.single μ 1) i + barField G' D'.Ψ φ₁ (x - Pi.single μ 1) i -
      2 * barField G' D'.Ψ φ₁ x i)) < δ / 2 / G'.spacing x ^ 2
  mult : ∀ x : G'.Ω 1, G'.spacing (x : Torus d (N₀ * L ^ K)) ^ 2 * ‖α₁ x‖ < δ / 2
  mass : ∀ z : G'.Ω 1, Real.sqrt ν * G'.spacing (z : Torus d (N₀ * L ^ K)) *
    vn (fun i => φ₁ (z, i) - D'.h z i) < δ / 2

omit [NeZero N₀] [NeZero L] in
theorem vn_sum_le_two {F U : Torus d (N₀ * L ^ K) → Fin N → ℂ} (y z : Torus d (N₀ * L ^ K)) :
    vn (fun i => (F y i + U y i) - (F z i + U z i)) ≤
      vn (fun i => F y i - F z i) + vn (fun i => U y i - U z i) := by
  have e : (fun i => (F y i + U y i) - (F z i + U z i)) =
      fun i => (F y i - F z i) + (U y i - U z i) := by funext i; ring
  rw [e]
  exact vn_add' _ _


section Perturb

variable {a₁ ν δ t V : ℝ} {D' : BgData G' N} {φ₁ : G'.Ω 1 × Fin N → ℂ} {α₁ : G'.Ω 1 → ℂ}
  {D : BgData G N} {φ : G.Ω 1 × Fin N → ℂ} {α : G.Ω 1 → ℂ}

theorem svec_perturb (hG : IsLevel G n) (hG' : IsLevel G' (n + 1)) (hp : n + 1 ≤ K)
    (y : Torus d (N₀ * L ^ K)) (i : Fin N) :
    svec G φ y i = svec G' φ₁ y i + svec G (φ - (hG.precedes hG' hp).restrictφ φ₁) y i := by
  rw [svec_sub, svec_restrict hG hG' hp]
  ring

theorem spacing_pos' (hG : IsLevel G n) (x : Torus d (N₀ * L ^ K)) : 0 < G.spacing x := by
  rw [hG.spacing_eq]
  have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  positivity

/-- The `ℓ`-weighted component bound as a bound on the difference. -/
theorem norm_le_div_of_mul_le {ℓ r V : ℝ} (hℓ : 0 < ℓ) (h : ℓ * r ≤ V) : r ≤ V / ℓ := by
  rw [le_div_iff₀ hℓ]; linarith

theorem xi_grad_of_perturb (hL3 : 3 ≤ L) (hG : IsLevel G n) (hG' : IsLevel G' (n + 1))
    (hp : n + 1 ≤ K) (hχ : ChiUBounds G' ν δ D' φ₁ α₁) (hδ : 0 < δ) (hV0 : 0 ≤ V)
    (hu : SupBounds G (φ - (hG.precedes hG' hp).restrictφ φ₁) V)
    (hsm : Real.sqrt N * V ≤ δ / 3) :
    ∀ x ∈ G.Ω 1, ∀ μ : Fin d,
      vn (fun i => barField G D.Ψ φ (x + Pi.single μ 1) i - barField G D.Ψ φ x i) <
        1 * δ / G.spacing x ∧
      vn (fun i => barField G D.Ψ φ (x - Pi.single μ 1) i - barField G D.Ψ φ x i) <
        1 * δ / G.spacing x := by
  intro x hx μ
  have hℓ := spacing_pos' hG x
  have hLℓ : G'.spacing x = L * G.spacing x := by
    rw [hG'.spacing_eq, hG.spacing_eq, pow_succ]; ring
  have hL0 : (3 : ℝ) ≤ L := by exact_mod_cast hL3
  have hx' : x ∈ G'.Ω 1 := (hG' x).1
  obtain ⟨g1, g2⟩ := hχ.grad x hx' μ
  simp only [barField_eq_svec hG'] at g1 g2
  have key : ∀ (y : Torus d (N₀ * L ^ K)),
      vn (fun i => svec G' φ₁ y i - svec G' φ₁ x i) < δ / 2 / G'.spacing x →
      (∀ i, G.spacing x * ‖svec G (φ - (hG.precedes hG' hp).restrictφ φ₁) y i -
        svec G (φ - (hG.precedes hG' hp).restrictφ φ₁) x i‖ ≤ V) →
      vn (fun i => barField G D.Ψ φ y i - barField G D.Ψ φ x i) < 1 * δ / G.spacing x := by
    intro y h1 h2
    have e : (fun i => barField G D.Ψ φ y i - barField G D.Ψ φ x i) =
        fun i => (svec G' φ₁ y i + svec G (φ - (hG.precedes hG' hp).restrictφ φ₁) y i) -
          (svec G' φ₁ x i + svec G (φ - (hG.precedes hG' hp).restrictφ φ₁) x i) := by
      funext i
      rw [barField_eq_svec hG, barField_eq_svec hG, svec_perturb hG hG' hp y i,
        svec_perturb hG hG' hp x i]
    rw [e]
    refine lt_of_le_of_lt (vn_sum_le_two y x) ?_
    have h3 : vn (fun i => svec G (φ - (hG.precedes hG' hp).restrictφ φ₁) y i -
        svec G (φ - (hG.precedes hG' hp).restrictφ φ₁) x i) ≤ Real.sqrt N * (V / G.spacing x) :=
      vn_le_sqrt_mul (by positivity) fun i => norm_le_div_of_mul_le hℓ (h2 i)
    have h4 : δ / 2 / G'.spacing x = δ / 2 / L / G.spacing x := by
      rw [hLℓ]; field_simp
    rw [h4] at h1
    have h5 : Real.sqrt N * (V / G.spacing x) = Real.sqrt N * V / G.spacing x := by ring
    rw [h5] at h3
    have h6 : δ / 2 / L ≤ δ / 6 := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    calc _ < δ / 2 / L / G.spacing x + Real.sqrt N * V / G.spacing x := by linarith
      _ ≤ δ / 6 / G.spacing x + δ / 3 / G.spacing x := by
          gcongr
      _ < 1 * δ / G.spacing x := by
          rw [← add_div, div_lt_div_iff_of_pos_right hℓ]; linarith
  refine ⟨key _ g1 fun i => hu.fwd x hx μ i, key _ g2 fun i => hu.bwd x hx μ i⟩


theorem blockAvg_eq_blockMean (hG : IsLevel G n) (φ : G.Ω 1 × Fin N → ℂ) (x : Torus d (N₀ * L ^ K))
    (i : Fin N) : blockAvg G φ x i = blockMean G n (fun y => svec G φ y i) x := by
  unfold blockAvg blockMean
  rw [(hG x).2]

/-- `ψ^{(k)} - Q_k φ₁ = κ (θ - Q_{k+1} φ₁)`, `κ = (a_{k+1}/a_k) L^{-2}` (Lemma 2.2 (a), (2.1)). -/
theorem compose_sub_blockAvg (hG : IsLevel G n) (hG' : IsLevel G' (n + 1)) (hp : n + 1 ≤ K)
    (a : ℕ → ℝ) (φ₁ : G'.Ω 1 × Fin N → ℂ) (D' : BgData G' N) (x : Torus d (N₀ * L ^ K))
    (i : Fin N) :
    (composeData (hG.precedes hG' hp) a φ₁ D').Ψ x i -
        blockAvg G ((hG.precedes hG' hp).restrictφ φ₁) x i =
      ((a (n + 1) / a n * (((L : ℝ) ^ n) ^ 2 / ((L : ℝ) ^ (n + 1)) ^ 2) : ℝ) : ℂ) *
        (D'.Ψ x i - blockAvg G' φ₁ x i) := by
  rw [composeData_Ψ_eq_psiStar hG hG' hp a φ₁ D' x i, blockAvg_eq_blockMean hG,
    blockAvg_eq_blockMean hG']
  unfold psiStar
  have e : (fun y => svec G ((hG.precedes hG' hp).restrictφ φ₁) y i) =
      fun y => svec G' φ₁ y i := funext fun y => svec_restrict hG hG' hp φ₁ y i
  rw [e]
  ring

omit [NeZero L] in
theorem kappa_bounds (hL3 : 3 ≤ L) (hn1 : 1 ≤ n) {a₁ : ℝ} (ha₁ : 0 < a₁) :
    0 ≤ compWeight L a₁ (n + 1) / compWeight L a₁ n *
        (((L : ℝ) ^ n) ^ 2 / ((L : ℝ) ^ (n + 1)) ^ 2) ∧
      compWeight L a₁ (n + 1) / compWeight L a₁ n *
        (((L : ℝ) ^ n) ^ 2 / ((L : ℝ) ^ (n + 1)) ^ 2) ≤ 1 / (L : ℝ) ^ 2 := by
  obtain ⟨r0, r1⟩ := compWeight_ratio (by omega : 2 ≤ L) ha₁ hn1 (Nat.le_succ n)
  have hL0 : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have hq : ((L : ℝ) ^ n) ^ 2 / ((L : ℝ) ^ (n + 1)) ^ 2 = 1 / (L : ℝ) ^ 2 := by
    rw [pow_succ]; field_simp; ring
  rw [hq]
  refine ⟨by positivity, ?_⟩
  calc _ ≤ 1 * (1 / (L : ℝ) ^ 2) := mul_le_mul_of_nonneg_right r1 (by positivity)
    _ = _ := one_mul _


theorem xi_lap_of_perturb (hL3 : 3 ≤ L) (hG : IsLevel G n) (hG' : IsLevel G' (n + 1))
    (hp : n + 1 ≤ K) (hχ : ChiUBounds G' ν δ D' φ₁ α₁) (hδ : 0 < δ) (hV0 : 0 ≤ V)
    (hu : SupBounds G (φ - (hG.precedes hG' hp).restrictφ φ₁) V)
    (hsm : Real.sqrt N * V ≤ δ / 3) :
    ∀ x ∈ G.Ω 1, vn (fun i => ∑ μ : Fin d,
      (barField G D.Ψ φ (x + Pi.single μ 1) i + barField G D.Ψ φ (x - Pi.single μ 1) i -
        2 * barField G D.Ψ φ x i)) < 1 ^ 2 * δ / G.spacing x ^ 2 := by
  intro x hx
  have hℓ := spacing_pos' hG x
  have hLℓ : G'.spacing x = L * G.spacing x := by
    rw [hG'.spacing_eq, hG.spacing_eq, pow_succ]; ring
  have hL0 : (3 : ℝ) ≤ L := by exact_mod_cast hL3
  have hx' : x ∈ G'.Ω 1 := (hG' x).1
  have g := hχ.lap x hx'
  simp only [barField_eq_svec hG'] at g
  set U := svec G (φ - (hG.precedes hG' hp).restrictφ φ₁) with hU
  have e : (fun i => ∑ μ : Fin d,
      (barField G D.Ψ φ (x + Pi.single μ 1) i + barField G D.Ψ φ (x - Pi.single μ 1) i -
        2 * barField G D.Ψ φ x i)) =
      (fun i => ∑ μ : Fin d, (svec G' φ₁ (x + Pi.single μ 1) i + svec G' φ₁ (x - Pi.single μ 1) i -
        2 * svec G' φ₁ x i)) +
      fun i => -(∑ μ : Fin d, (2 * U x i - U (x + Pi.single μ 1) i - U (x - Pi.single μ 1) i)) := by
    funext i
    simp only [Pi.add_apply, barField_eq_svec hG, ← Finset.sum_neg_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [svec_perturb hG hG' hp (x + Pi.single μ 1) i, svec_perturb hG hG' hp (x - Pi.single μ 1) i,
      svec_perturb hG hG' hp x i, ← hU]
    ring
  rw [e]
  refine lt_of_le_of_lt (vn_add _ _) ?_
  have h3 : vn (fun i => -(∑ μ : Fin d, (2 * U x i - U (x + Pi.single μ 1) i -
      U (x - Pi.single μ 1) i))) ≤ Real.sqrt N * (V / G.spacing x ^ 2) := by
    refine vn_le_sqrt_mul (by positivity) fun i => ?_
    rw [norm_neg]
    exact norm_le_div_of_mul_le (by positivity) (hu.lap x hx i)
  have h4 : δ / 2 / G'.spacing x ^ 2 = δ / 2 / L ^ 2 / G.spacing x ^ 2 := by
    rw [hLℓ]; field_simp
  rw [h4] at g
  have h5 : Real.sqrt N * (V / G.spacing x ^ 2) = Real.sqrt N * V / G.spacing x ^ 2 := by ring
  rw [h5] at h3
  have h6 : δ / 2 / (L : ℝ) ^ 2 ≤ δ / 6 := by
    have hL2 : (9 : ℝ) ≤ (L : ℝ) ^ 2 := by nlinarith
    rw [div_le_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hL2 hδ.le]
  have hp2 : 0 < G.spacing x ^ 2 := by positivity
  calc _ < δ / 2 / (L : ℝ) ^ 2 / G.spacing x ^ 2 + Real.sqrt N * V / G.spacing x ^ 2 := by
        linarith
    _ ≤ δ / 6 / G.spacing x ^ 2 + δ / 3 / G.spacing x ^ 2 := by gcongr
    _ < 1 ^ 2 * δ / G.spacing x ^ 2 := by
        rw [← add_div, div_lt_div_iff_of_pos_right hp2]; linarith


theorem xi_mult_of_perturb (hL3 : 3 ≤ L) (hG : IsLevel G n) (hG' : IsLevel G' (n + 1))
    (hp : n + 1 ≤ K) (hχ : ChiUBounds G' ν δ D' φ₁ α₁) (hδ : 0 < δ)
    (hua : Small G (α - (hG.precedes hG' hp).restrictα α₁) V) (hV : V ≤ δ / 3) :
    ∀ x : G.Ω 1, G.spacing (x : Torus d (N₀ * L ^ K)) ^ 2 * ‖α x‖ < 1 ^ 2 * δ := by
  intro x
  have hℓ := spacing_pos' hG (x : Torus d (N₀ * L ^ K))
  have hLℓ : G'.spacing (x : Torus d (N₀ * L ^ K)) = L * G.spacing (x : Torus d (N₀ * L ^ K)) := by
    rw [hG'.spacing_eq, hG.spacing_eq, pow_succ]; ring
  have hL0 : (3 : ℝ) ≤ L := by exact_mod_cast hL3
  have g := hχ.mult ((hG.precedes hG' hp).incl x)
  have e : α x = (hG.precedes hG' hp).restrictα α₁ x + (α - (hG.precedes hG' hp).restrictα α₁) x := by
    simp
  have h1 : G.spacing (x : Torus d (N₀ * L ^ K)) ^ 2 * ‖α x‖ ≤
      G.spacing (x : Torus d (N₀ * L ^ K)) ^ 2 * ‖(hG.precedes hG' hp).restrictα α₁ x‖ +
        G.spacing (x : Torus d (N₀ * L ^ K)) ^ 2 *
          ‖(α - (hG.precedes hG' hp).restrictα α₁) x‖ := by
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left (e ▸ norm_add_le _ _) (by positivity)
  have h2 := hua x
  have h3 : G.spacing (x : Torus d (N₀ * L ^ K)) ^ 2 *
      ‖(hG.precedes hG' hp).restrictα α₁ x‖ < δ / 2 / L ^ 2 := by
    have : G'.spacing (((hG.precedes hG' hp).incl x : G'.Ω 1) : Torus d (N₀ * L ^ K)) =
        L * G.spacing (x : Torus d (N₀ * L ^ K)) := hLℓ
    rw [this] at g
    have hL2 : (0 : ℝ) < (L : ℝ) ^ 2 := by positivity
    rw [lt_div_iff₀ hL2]
    unfold Precedes.restrictα
    nlinarith
  have h6 : δ / 2 / (L : ℝ) ^ 2 ≤ δ / 6 := by
    have hL2 : (9 : ℝ) ≤ (L : ℝ) ^ 2 := by nlinarith
    rw [div_le_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hL2 hδ.le]
  nlinarith

theorem xi_mass_of_perturb (hL3 : 3 ≤ L) (hG : IsLevel G n) (hG' : IsLevel G' (n + 1))
    (hp : n + 1 ≤ K) (hχ : ChiUBounds G' ν δ D' φ₁ α₁) (hδ : 0 < δ) (hV0 : 0 ≤ V)
    (hν0 : 0 ≤ ν) (hν1 : ν * ((L : ℝ) ^ (n + 1)) ^ 2 ≤ 1) {h₀ : Fin N → ℝ}
    (hh' : ∀ x i, D'.h x i = (h₀ i : ℂ))
    (hu : SupBounds G (φ - (hG.precedes hG' hp).restrictφ φ₁) V)
    (hsm : Real.sqrt N * V ≤ δ / 3) :
    ∀ z : G.Ω 1, Real.sqrt ν * G.spacing (z : Torus d (N₀ * L ^ K)) *
      vn (fun i => φ (z, i) - (h₀ i : ℂ)) < 1 * δ := by
  intro z
  have hℓ := spacing_pos' hG (z : Torus d (N₀ * L ^ K))
  have hLℓ : G'.spacing (z : Torus d (N₀ * L ^ K)) = L * G.spacing (z : Torus d (N₀ * L ^ K)) := by
    rw [hG'.spacing_eq, hG.spacing_eq, pow_succ]; ring
  have hL0 : (3 : ℝ) ≤ L := by exact_mod_cast hL3
  have g : Real.sqrt ν * G'.spacing (z : Torus d (N₀ * L ^ K)) *
      vn (fun i => φ₁ ((hG.precedes hG' hp).incl z, i) - D'.h z i) < δ / 2 :=
    hχ.mass ((hG.precedes hG' hp).incl z)
  have hn1 : Real.sqrt ν * G'.spacing (z : Torus d (N₀ * L ^ K)) ≤ 1 := by
    rw [hG'.spacing_eq]
    have h2 : (Real.sqrt ν * (L : ℝ) ^ (n + 1)) ^ 2 ≤ 1 := by
      rw [mul_pow, Real.sq_sqrt hν0]; exact hν1
    have h3 : 0 ≤ Real.sqrt ν * (L : ℝ) ^ (n + 1) := by positivity
    nlinarith
  have hsp : 0 ≤ Real.sqrt ν * G.spacing (z : Torus d (N₀ * L ^ K)) := by positivity
  have hq : Real.sqrt ν * G.spacing (z : Torus d (N₀ * L ^ K)) * L ≤ 1 := by
    rw [hLℓ] at hn1; linarith
  have hq3 : Real.sqrt ν * G.spacing (z : Torus d (N₀ * L ^ K)) ≤ 1 / 3 := by
    nlinarith
  have e : (fun i => φ (z, i) - (h₀ i : ℂ)) =
      (fun i => φ₁ ((hG.precedes hG' hp).incl z, i) - D'.h z i) +
        fun i => (φ - (hG.precedes hG' hp).restrictφ φ₁) (z, i) := by
    funext i
    simp only [Pi.add_apply, Pi.sub_apply, hh']
    unfold Precedes.restrictφ
    ring
  rw [e]
  refine lt_of_le_of_lt (mul_le_mul_of_nonneg_left (vn_add _ _) hsp) ?_
  have h4 : vn (fun i => (φ - (hG.precedes hG' hp).restrictφ φ₁) (z, i)) ≤ Real.sqrt N * V := by
    refine vn_le_sqrt_mul hV0 fun i => ?_
    have := hu.val z i
    rwa [svec_of_mem] at this
  have h5 : Real.sqrt ν * G.spacing (z : Torus d (N₀ * L ^ K)) *
      vn (fun i => φ₁ ((hG.precedes hG' hp).incl z, i) - D'.h z i) < δ / 2 / L := by
    rw [hLℓ] at g
    rw [lt_div_iff₀ (by linarith)]
    nlinarith
  have h6 : δ / 2 / (L : ℝ) ≤ δ / 6 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  rw [mul_add]
  have h7 : Real.sqrt ν * G.spacing (z : Torus d (N₀ * L ^ K)) *
      vn (fun i => (φ - (hG.precedes hG' hp).restrictφ φ₁) (z, i)) ≤ 1 / 3 * (δ / 3) := by
    calc _ ≤ 1 / 3 * vn (fun i => (φ - (hG.precedes hG' hp).restrictφ φ₁) (z, i)) :=
          mul_le_mul_of_nonneg_right hq3 (vn_nonneg _)
      _ ≤ 1 / 3 * (δ / 3) := by
          gcongr; exact h4.trans hsm
  linarith


theorem xi_close_of_perturb (hL3 : 3 ≤ L) (hn1 : 1 ≤ n) {a₁ : ℝ} (ha₁ : 0 < a₁)
    (hG : IsLevel G n) (hG' : IsLevel G' (n + 1))
    (hp : n + 1 ≤ K) (hχ : ChiUBounds G' ν δ D' φ₁ α₁) (hδ : 0 < δ) (hV0 : 0 ≤ V)
    (hu : SupBounds G (φ - (hG.precedes hG' hp).restrictφ φ₁) V)
    (hsm : Real.sqrt N * V ≤ δ / 3)
    (htang : ∀ x, vn (fun i => D.Ψ x i -
      (composeData (hG.precedes hG' hp) (compWeight L a₁) φ₁ D').Ψ x i) ≤ t) (ht : t ≤ δ / 3) :
    ∀ x ∈ G.Ω 1, vn (fun i => D.Ψ x i - blockAvg G φ x i) < 1 ^ 2 * δ := by
  intro x hx
  obtain ⟨hk0, hk1⟩ := kappa_bounds hL3 hn1 ha₁
  set κ : ℝ := compWeight L a₁ (n + 1) / compWeight L a₁ n *
    (((L : ℝ) ^ n) ^ 2 / ((L : ℝ) ^ (n + 1)) ^ 2) with hκ
  have hL0 : (3 : ℝ) ≤ L := by exact_mod_cast hL3
  have hL2 : (9 : ℝ) ≤ (L : ℝ) ^ 2 := by nlinarith
  have hκ9 : κ ≤ 1 / 9 := by
    refine hk1.trans ?_
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  set U := svec G (φ - (hG.precedes hG' hp).restrictφ φ₁) with hU
  have hbU : ∀ i, blockAvg G (φ - (hG.precedes hG' hp).restrictφ φ₁) x i =
      blockMean G n (fun y => U y i) x := fun i => blockAvg_eq_blockMean hG _ x i
  have hφsplit : φ = (hG.precedes hG' hp).restrictφ φ₁ + (φ - (hG.precedes hG' hp).restrictφ φ₁) := by
    abel
  have e : (fun i => D.Ψ x i - blockAvg G φ x i) =
      ((fun i => D.Ψ x i - (composeData (hG.precedes hG' hp) (compWeight L a₁) φ₁ D').Ψ x i) +
        fun i => (κ : ℂ) * (D'.Ψ x i - blockAvg G' φ₁ x i)) +
        fun i => -(blockAvg G (φ - (hG.precedes hG' hp).restrictφ φ₁) x i) := by
    funext i
    simp only [Pi.add_apply]
    have h1 := compose_sub_blockAvg hG hG' hp (compWeight L a₁) φ₁ D' x i
    have h2 : blockAvg G φ x i = blockAvg G ((hG.precedes hG' hp).restrictφ φ₁) x i +
        blockAvg G (φ - (hG.precedes hG' hp).restrictφ φ₁) x i := by
      conv_lhs => rw [hφsplit]
      exact blockAvg_add _ _ x i
    rw [h2]
    rw [← hκ] at h1
    linear_combination h1
  rw [e]
  refine lt_of_le_of_lt (vn_add _ _) ?_
  have hw : vn (fun i => D'.Ψ x i - blockAvg G' φ₁ x i) < 3 / 2 * δ := hχ.close x (hG' x).1
  have h3 : vn (fun i => (κ : ℂ) * (D'.Ψ x i - blockAvg G' φ₁ x i)) ≤ 1 / 9 * (3 / 2 * δ) := by
    rw [vn_smul_real, abs_of_nonneg hk0]
    have := vn_nonneg (fun i => D'.Ψ x i - blockAvg G' φ₁ x i)
    nlinarith
  have h4 : vn (fun i => -(blockAvg G (φ - (hG.precedes hG' hp).restrictφ φ₁) x i)) ≤ δ / 3 := by
    rw [vn_neg]
    refine (vn_le_sqrt_mul hV0 fun i => ?_).trans hsm
    rw [hbU]
    refine norm_blockMean_le' (by omega) _ x fun y _ => ?_
    exact hu.val y i
  have h5 := vn_add (fun i => D.Ψ x i - (composeData (hG.precedes hG' hp) (compWeight L a₁) φ₁ D').Ψ x i)
    (fun i => (κ : ℂ) * (D'.Ψ x i - blockAvg G' φ₁ x i))
  have h6 := htang x
  have h7 : vn (fun i => (κ : ℂ) * (D'.Ψ x i - blockAvg G' φ₁ x i)) <  1 / 9 * (3 / 2 * δ) ∨ True := Or.inr trivial
  nlinarith


/-- **The inequalities of `Ξ_n(𝔹; 1, δ)` for `ψ = ψ^{(k)} + ψ'`** (the tests of `χ_k`), from the
tests of `χ_{k+1,u}` for `θ` and the bounds of Lemma 2.3 (d):
`‖φ_k(ψ) - φ_{k+1}‖_*, |α_k(ψ) - α_{k+1}|₂ ≤ V` with `√N V ≤ δ/3`, and `|ψ'| ≤ t ≤ δ/3`. -/
theorem xiBounds_of_perturb (hL3 : 3 ≤ L) (hn1 : 1 ≤ n) {a₁ : ℝ} (ha₁ : 0 < a₁)
    (hG : IsLevel G n) (hG' : IsLevel G' (n + 1)) (hp : n + 1 ≤ K)
    (hχ : ChiUBounds G' ν δ D' φ₁ α₁) (hδ : 0 < δ) (hV0 : 0 ≤ V)
    (hν0 : 0 ≤ ν) (hν1 : ν * ((L : ℝ) ^ (n + 1)) ^ 2 ≤ 1) {h₀ : Fin N → ℝ}
    (hh' : ∀ x i, D'.h x i = (h₀ i : ℂ))
    (hu : SupBounds G (φ - (hG.precedes hG' hp).restrictφ φ₁) V)
    (hua : Small G (α - (hG.precedes hG' hp).restrictα α₁) V)
    (hsm : Real.sqrt N * V ≤ δ / 3) (hVδ : V ≤ δ / 3)
    (htang : ∀ x, vn (fun i => D.Ψ x i -
      (composeData (hG.precedes hG' hp) (compWeight L a₁) φ₁ D').Ψ x i) ≤ t) (ht : t ≤ δ / 3)
    (hnorm : ν * ((L : ℝ) ^ n) ^ 2 * |∑ i, h₀ i ^ 2 - 1| < (1 * δ) ^ 2) :
    XiBounds G ν n 1 δ D h₀ φ α where
  grad := xi_grad_of_perturb hL3 hG hG' hp hχ hδ hV0 hu hsm
  lap := xi_lap_of_perturb hL3 hG hG' hp hχ hδ hV0 hu hsm
  mult := xi_mult_of_perturb hL3 hG hG' hp hχ hδ hua hVδ
  close := xi_close_of_perturb hL3 hn1 ha₁ hG hG' hp hχ hδ hV0 hu hsm htang ht
  collarBond := fun z hz => by rw [hG.collar_eq] at hz; exact absurd hz (by simp)
  mass := xi_mass_of_perturb hL3 hG hG' hp hχ hδ hV0 hν0 hν1 hh' hu hsm
  hnorm := hnorm

end Perturb

end Balaban.Fluctuation
