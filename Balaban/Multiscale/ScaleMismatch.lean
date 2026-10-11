/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Multiscale.AgmonDecay
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# G-2(i): block-to-block decay with the scale mismatch (GREEN.md §4.3, Corollary 4.6)

`Balaban.Multiscale.agmon_block` bounds the block norms of `u = G_D(α) f` by
`ℓ_j ℓ_{j'} e^{-εt}‖f‖` for every `t ≤ d(y, y')`.  The factor `ℓ_j / ℓ_{j'} ≤ L^{(j - j')₊}` is
absorbed by the layer separation `d(y, y') ≥ (ϱ - 1) (j - j' - 1)₊`
(`Balaban.Multiscale.GeneratingSet.pathDist_separation_le`) provided
`L ≤ exp ((ε/2) (ϱ - 1))`, i.e. `log L ≤ (ε/2) (ϱ - 1)` (GREEN.md (4.1)); with `ε = ε₀` this
reads `ϱ - 1 ≥ 2 ε₀⁻¹ log L = 32 d c⁻¹ log L`.

Main result `Balaban.Multiscale.green_G2i`:
`ℓ_j ‖χ_{Δ_j(y)} ∂ũ‖ + ‖χ_{Δ_j(y)} ũ‖ ≤ (13 L / c) e^{-(ε/2) t} ℓ_{j'}² ‖f‖`
for all `t ≥ 0` with `t ≤ d(y, y')` (`ℓ_j = L ^ j`, unit fine lattice spacing).
-/

@[expose] public section

namespace Balaban.Multiscale

open Finset Matrix Balaban

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- The absorption inequality: `L ^ m e^{-c (m - 1)} ≤ L` when `L ≤ e^c`. -/
theorem pow_mul_exp_le {c : ℝ} (hc : (L : ℝ) ≤ Real.exp c) (m : ℕ) :
    (L : ℝ) ^ m * Real.exp (-(c * ((m - 1 : ℕ) : ℝ))) ≤ L := by
  have hL : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hL0 : (0 : ℝ) < L := by linarith
  have key : ∀ n : ℕ, (L : ℝ) ^ n * Real.exp (-(c * n)) ≤ 1 := by
    intro n
    have h1 : (L : ℝ) ^ n ≤ Real.exp c ^ n := pow_le_pow_left₀ hL0.le hc n
    have h2 : Real.exp c ^ n = Real.exp (n * c) := by rw [Real.exp_nat_mul]
    have h3 : Real.exp (n * c) * Real.exp (-(c * n)) = 1 := by
      rw [← Real.exp_add]; simp [mul_comm]
    calc (L : ℝ) ^ n * Real.exp (-(c * n)) ≤ Real.exp (n * c) * Real.exp (-(c * n)) :=
          mul_le_mul_of_nonneg_right (h1.trans h2.le) (Real.exp_pos _).le
      _ = 1 := h3
  rcases Nat.eq_zero_or_pos m with h | h
  · subst h; simp [hL]
  · obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
    have : n + 1 - 1 = n := by omega
    rw [this, pow_succ]
    calc (L : ℝ) ^ n * L * Real.exp (-(c * n)) = L * ((L : ℝ) ^ n * Real.exp (-(c * n))) := by ring
      _ ≤ L * 1 := mul_le_mul_of_nonneg_left (key n) hL0.le
      _ = L := mul_one _

/-- The scale mismatch (GREEN.md §4.3): for `t₂ ≥ t, s₀` with `s₀ = (ϱ - 1)(j - j' - 1)₊`,
`ℓ_j ℓ_{j'} e^{-ε t₂} ≤ L ℓ_{j'}² e^{-(ε/2) t}`. -/
theorem scale_mismatch {ε ϱ t t₂ : ℝ} (hε : 0 ≤ ε) (j j' : ℕ)
    (hsep : (L : ℝ) ≤ Real.exp (ε / 2 * (ϱ - 1))) (ht : t ≤ t₂)
    (hs : (ϱ - 1) * ((j - j' - 1 : ℕ) : ℝ) ≤ t₂) :
    (L : ℝ) ^ j * (L : ℝ) ^ j' * Real.exp (-(ε * t₂)) ≤
      L * ((L : ℝ) ^ j') ^ 2 * Real.exp (-(ε / 2 * t)) := by
  have hL : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hL0 : (0 : ℝ) < L := by linarith
  set m := j - j' with hm
  have hjm : (L : ℝ) ^ j ≤ (L : ℝ) ^ j' * (L : ℝ) ^ m := by
    rw [← pow_add]; exact pow_le_pow_right₀ hL (by omega)
  have habs := pow_mul_exp_le (L := L) hsep m
  have hm1 : (j - j' - 1 : ℕ) = m - 1 := rfl
  -- split the exponential
  have hs' : ε / 2 * ((ϱ - 1) * ((m - 1 : ℕ) : ℝ)) ≤ ε / 2 * t₂ := by
    have : (ϱ - 1) * ((m - 1 : ℕ) : ℝ) ≤ t₂ := by rw [hm1] at hs; exact hs
    exact mul_le_mul_of_nonneg_left this (by positivity)
  have hexp : Real.exp (-(ε * t₂)) ≤
      Real.exp (-(ε / 2 * t)) * Real.exp (-(ε / 2 * ((ϱ - 1) * ((m - 1 : ℕ) : ℝ)))) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    have h1 : ε / 2 * t ≤ ε / 2 * t₂ := mul_le_mul_of_nonneg_left ht (by positivity)
    linarith
  have e : ε / 2 * ((ϱ - 1) * ((m - 1 : ℕ) : ℝ)) = (ε / 2 * (ϱ - 1)) * ((m - 1 : ℕ) : ℝ) := by ring
  rw [e] at hexp
  have hmain : (L : ℝ) ^ m * Real.exp (-(ε / 2 * (ϱ - 1) * ((m - 1 : ℕ) : ℝ))) ≤ L :=
    pow_mul_exp_le (L := L) hsep m
  have hE0 : 0 ≤ Real.exp (-(ε / 2 * t)) := (Real.exp_pos _).le
  calc (L : ℝ) ^ j * (L : ℝ) ^ j' * Real.exp (-(ε * t₂))
      ≤ ((L : ℝ) ^ j' * (L : ℝ) ^ m) * (L : ℝ) ^ j' *
          (Real.exp (-(ε / 2 * t)) * Real.exp (-(ε / 2 * (ϱ - 1) * ((m - 1 : ℕ) : ℝ)))) := by
        gcongr
    _ = ((L : ℝ) ^ j') ^ 2 * Real.exp (-(ε / 2 * t)) *
          ((L : ℝ) ^ m * Real.exp (-(ε / 2 * (ϱ - 1) * ((m - 1 : ℕ) : ℝ)))) := by ring
    _ ≤ ((L : ℝ) ^ j') ^ 2 * Real.exp (-(ε / 2 * t)) * L := by gcongr
    _ = _ := by ring


/-- **G-2(i).**  For `f` supported in the block `Δ_{j'}(y')` (`y'` in layer `j'`), `u` with
`H_D(α) u = f`, `y` in layer `j`, `0 ≤ ε ≤ ε₀`, `ϱ ≥ 1` with `L ≤ exp ((ε/2)(ϱ - 1))`, and every
`t ≥ 0` with `t ≤ d(y, y')`:
`ℓ_j ‖χ_{Δ_j(y)} ∂ũ‖ + ‖χ_{Δ_j(y)} ũ‖ ≤ (13 L / c) e^{-(ε/2) t} ℓ_{j'}² ‖f‖`. -/
theorem green_G2i (G : GeneratingSet d L N₀ k ϱ) (hd : 0 < d) {a : ℕ → ℝ} {ν : ℝ} (hν : 0 ≤ ν)
    (ha : IsAdmissibleWeights k a) (α : G.Ω 1 → ℂ)
    (hα : ∀ x, ‖α x‖ ≤ coerciveConst d / (2 * (G.spacing x) ^ 2))
    {j j' : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k) (hj'1 : 1 ≤ j') (hj'k : j' ≤ k)
    {y y' : Torus d (N₀ * L ^ k)} (hy : y ∈ G.layer j) (hy' : y' ∈ G.layer j')
    {u f : G.Ω 1 → ℂ} (hu : dirichletOperator G a ν α *ᵥ u = f)
    (hsupp : ∀ x : G.Ω 1, f x ≠ 0 → jBlock d L N₀ k j' x = jBlock d L N₀ k j' y')
    {t : ℝ} (ht0 : 0 ≤ t) (ht : ENNReal.ofReal t ≤ G.pathDist y y') {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ agmonRate d) (hϱ : 1 ≤ ϱ) (hsep : (L : ℝ) ≤ Real.exp (ε / 2 * (ϱ - 1))) :
    (L : ℝ) ^ j * Real.sqrt (∑ x ∈ G.blk j y, ∑ μ : Fin d,
        ‖zeroExt (G.Ω 1) u (x + Pi.single μ 1) - zeroExt (G.Ω 1) u x‖ ^ 2) +
      Real.sqrt (∑ x ∈ G.blk j y, ‖zeroExt (G.Ω 1) u x‖ ^ 2) ≤
    13 * L / poincareConst d * Real.exp (-(ε / 2 * t)) * ((L : ℝ) ^ j') ^ 2 *
      Real.sqrt (Green.sqNorm f) := by
  have hp0 := poincareConst_pos hd
  have hph := poincareConst_le_half d
  have hL : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hL0 : (0 : ℝ) < L := by linarith
  -- the separation lower bound for the distance
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
  obtain ⟨hA, hB⟩ := agmon_block G hd hν ha α hα hj1 hjk hj'1 hj'k hy hy' hu hsupp ht₂0 ht₂d hε0 hε1
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
  -- the two square-root bounds
  have h1 : Real.sqrt Nn ≤ 3 / poincareConst d * P := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    calc Nn ≤ 8 / poincareConst d ^ 2 * P ^ 2 := by rw [hP2]; convert hA using 1; ring
      _ ≤ (3 / poincareConst d * P) ^ 2 := by
        rw [mul_pow, div_pow]
        have : 8 / poincareConst d ^ 2 ≤ 3 ^ 2 / poincareConst d ^ 2 :=
          div_le_div_of_nonneg_right (by norm_num) (by positivity)
        exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
  have h2 : (L : ℝ) ^ j * Real.sqrt Yy ≤ 10 / poincareConst d * P := by
    have hsq : ((L : ℝ) ^ j * Real.sqrt Yy) ^ 2 ≤ (10 / poincareConst d * P) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hY0, mul_pow]
      have hB' : ((L : ℝ) ^ j) ^ 2 * Yy ≤ 10 / poincareConst d * P ^ 2 := by
        rw [hP2]
        calc ((L : ℝ) ^ j) ^ 2 * Yy ≤ ((L : ℝ) ^ j) ^ 2 *
              (10 / poincareConst d * ((L : ℝ) ^ j') ^ 2 * Real.exp (-(2 * ε * t₂)) * F) :=
            mul_le_mul_of_nonneg_left hB (by positivity)
          _ = _ := by ring
      have h10 : 10 / poincareConst d ≤ (10 / poincareConst d) ^ 2 := by
        have : 1 ≤ 10 / poincareConst d := by
          rw [le_div_iff₀ hp0]; linarith
        nlinarith
      calc _ ≤ 10 / poincareConst d * P ^ 2 := hB'
        _ ≤ (10 / poincareConst d) ^ 2 * P ^ 2 := mul_le_mul_of_nonneg_right h10 (sq_nonneg _)
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 hsq
  calc (L : ℝ) ^ j * Real.sqrt Yy + Real.sqrt Nn ≤ 10 / poincareConst d * P + 3 / poincareConst d * P :=
        add_le_add h2 h1
    _ = 13 / poincareConst d * P := by ring
    _ ≤ 13 / poincareConst d * (L * ((L : ℝ) ^ j') ^ 2 * Real.exp (-(ε / 2 * t)) * Real.sqrt F) :=
        mul_le_mul_of_nonneg_left hPle (by positivity)
    _ = _ := by ring


/-- GREEN.md (4.1): `log L ≤ (ε/2)(ϱ - 1)` gives the absorption hypothesis. -/
theorem sep_of_log_le {ε ϱ : ℝ} (h : Real.log L ≤ ε / 2 * (ϱ - 1)) :
    (L : ℝ) ≤ Real.exp (ε / 2 * (ϱ - 1)) := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  exact (Real.log_le_iff_le_exp hL0).1 h

/-- G-2(i) with the distance of the path metric itself: if `d(y, y') < ⊤`, the bound holds with
`t = d(y, y')`; if `d(y, y') = ⊤` (no path in `Ω₁`), `u` vanishes on `Δ_j(y)` (it has zero gradient
energy and zero norm there). -/
theorem green_G2i_of_pathDist (G : GeneratingSet d L N₀ k ϱ) (hd : 0 < d) {a : ℕ → ℝ} {ν : ℝ}
    (hν : 0 ≤ ν) (ha : IsAdmissibleWeights k a) (α : G.Ω 1 → ℂ)
    (hα : ∀ x, ‖α x‖ ≤ coerciveConst d / (2 * (G.spacing x) ^ 2))
    {j j' : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k) (hj'1 : 1 ≤ j') (hj'k : j' ≤ k)
    {y y' : Torus d (N₀ * L ^ k)} (hy : y ∈ G.layer j) (hy' : y' ∈ G.layer j')
    {u f : G.Ω 1 → ℂ} (hu : dirichletOperator G a ν α *ᵥ u = f)
    (hsupp : ∀ x : G.Ω 1, f x ≠ 0 → jBlock d L N₀ k j' x = jBlock d L N₀ k j' y')
    (hϱ : 1 ≤ ϱ) (hsep : (L : ℝ) ≤ Real.exp (agmonRate d / 2 * (ϱ - 1))) :
    (G.pathDist y y' ≠ ⊤ →
      (L : ℝ) ^ j * Real.sqrt (∑ x ∈ G.blk j y, ∑ μ : Fin d,
          ‖zeroExt (G.Ω 1) u (x + Pi.single μ 1) - zeroExt (G.Ω 1) u x‖ ^ 2) +
        Real.sqrt (∑ x ∈ G.blk j y, ‖zeroExt (G.Ω 1) u x‖ ^ 2) ≤
      13 * L / poincareConst d * Real.exp (-(agmonRate d / 2 * (G.pathDist y y').toReal)) *
        ((L : ℝ) ^ j') ^ 2 * Real.sqrt (Green.sqNorm f)) ∧
    (G.pathDist y y' = ⊤ →
      (L : ℝ) ^ j * Real.sqrt (∑ x ∈ G.blk j y, ∑ μ : Fin d,
          ‖zeroExt (G.Ω 1) u (x + Pi.single μ 1) - zeroExt (G.Ω 1) u x‖ ^ 2) +
        Real.sqrt (∑ x ∈ G.blk j y, ‖zeroExt (G.Ω 1) u x‖ ^ 2) ≤ 0) := by
  have hε0 : 0 < agmonRate d := agmonRate_pos hd
  have hp0 := poincareConst_pos hd
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  refine ⟨fun hne => ?_, fun htop => ?_⟩
  · exact green_G2i G hd hν ha α hα hj1 hjk hj'1 hj'k hy hy' hu hsupp ENNReal.toReal_nonneg
      (by rw [ENNReal.ofReal_toReal hne]) hε0.le le_rfl hϱ hsep
  · set LHS := (L : ℝ) ^ j * Real.sqrt (∑ x ∈ G.blk j y, ∑ μ : Fin d,
          ‖zeroExt (G.Ω 1) u (x + Pi.single μ 1) - zeroExt (G.Ω 1) u x‖ ^ 2) +
        Real.sqrt (∑ x ∈ G.blk j y, ‖zeroExt (G.Ω 1) u x‖ ^ 2) with hLHS
    set K : ℝ := 13 * L / poincareConst d * ((L : ℝ) ^ j') ^ 2 * Real.sqrt (Green.sqNorm f) with hK
    have hK0 : 0 ≤ K := by positivity
    have hbound : ∀ t : ℝ, 0 ≤ t → LHS ≤ K * Real.exp (-(agmonRate d / 2 * t)) := by
      intro t ht0
      have := green_G2i G hd hν ha α hα hj1 hjk hj'1 hj'k hy hy' hu hsupp ht0
        (by rw [htop]; exact le_top) hε0.le le_rfl hϱ hsep
      calc LHS ≤ _ := this
        _ = _ := by rw [hK]; ring
    have hLHS0 : 0 ≤ LHS := by positivity
    by_contra hpos
    push Not at hpos
    set c := agmonRate d / 2 with hc
    have hc0 : 0 < c := by positivity
    set t := K / (c * LHS) with ht
    have ht0 : 0 ≤ t := by positivity
    have h1 := hbound t ht0
    have h2 : Real.exp (c * t) ≥ 1 + c * t := by linarith [Real.add_one_le_exp (c * t)]
    have h3 : K * Real.exp (-(c * t)) * (1 + c * t) ≤ K := by
      have : Real.exp (-(c * t)) * Real.exp (c * t) = 1 := by rw [← Real.exp_add]; simp
      calc K * Real.exp (-(c * t)) * (1 + c * t) ≤ K * Real.exp (-(c * t)) * Real.exp (c * t) :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = K := by rw [mul_assoc, this, mul_one]
    have h4 : c * t = K / LHS := by rw [ht]; field_simp
    rw [h4] at h3 h1
    have h5 : LHS * (1 + K / LHS) = LHS + K := by field_simp
    have h6 : LHS * (1 + K / LHS) ≤ K * Real.exp (-(K / LHS)) * (1 + K / LHS) :=
      mul_le_mul_of_nonneg_right (by simpa [h4] using h1) (by positivity)
    nlinarith


/-- `H_D(α) G_D(α) f = f` for the Green's function `G_D(α) = H_D(α)⁻¹`. -/
theorem dirichletOperator_mulVec_inv (G : GeneratingSet d L N₀ k ϱ) (hd : 0 < d) {a : ℕ → ℝ}
    {ν : ℝ} (hν : 0 ≤ ν) (ha : IsAdmissibleWeights k a) (α : G.Ω 1 → ℂ)
    (hα : ∀ x, ‖α x‖ ≤ coerciveConst d / (2 * (G.spacing x) ^ 2)) (f : G.Ω 1 → ℂ) :
    dirichletOperator G a ν α *ᵥ ((dirichletOperator G a ν α)⁻¹ *ᵥ f) = f := by
  have hU := dirichletOperator_isUnit G hd hν ha α hα
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hU),
    Matrix.one_mulVec]

/-- **G-2(i) for the Green's function** `G_D(α) = H_D(α)⁻¹`: the block-to-block bound
`ℓ_j ‖χ_{Δ_j(y)} ∂ G_D f‖ + ‖χ_{Δ_j(y)} G_D f‖ ≤ (13 L / c) e^{-(ε/2) t} ℓ_{j'}² ‖f‖` for `f`
supported in `Δ_{j'}(y')` and `0 ≤ t ≤ d(y, y')`, uniformly over `α` with `|α| ≤ c₁ ℓ⁻²/2`. -/
theorem green_G2i_green (G : GeneratingSet d L N₀ k ϱ) (hd : 0 < d) {a : ℕ → ℝ} {ν : ℝ}
    (hν : 0 ≤ ν) (ha : IsAdmissibleWeights k a) (α : G.Ω 1 → ℂ)
    (hα : ∀ x, ‖α x‖ ≤ coerciveConst d / (2 * (G.spacing x) ^ 2))
    {j j' : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k) (hj'1 : 1 ≤ j') (hj'k : j' ≤ k)
    {y y' : Torus d (N₀ * L ^ k)} (hy : y ∈ G.layer j) (hy' : y' ∈ G.layer j')
    {f : G.Ω 1 → ℂ}
    (hsupp : ∀ x : G.Ω 1, f x ≠ 0 → jBlock d L N₀ k j' x = jBlock d L N₀ k j' y')
    {t : ℝ} (ht0 : 0 ≤ t) (ht : ENNReal.ofReal t ≤ G.pathDist y y') {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ agmonRate d) (hϱ : 1 ≤ ϱ) (hsep : (L : ℝ) ≤ Real.exp (ε / 2 * (ϱ - 1))) :
    (L : ℝ) ^ j * Real.sqrt (∑ x ∈ G.blk j y, ∑ μ : Fin d,
        ‖zeroExt (G.Ω 1) ((dirichletOperator G a ν α)⁻¹ *ᵥ f) (x + Pi.single μ 1) -
          zeroExt (G.Ω 1) ((dirichletOperator G a ν α)⁻¹ *ᵥ f) x‖ ^ 2) +
      Real.sqrt (∑ x ∈ G.blk j y, ‖zeroExt (G.Ω 1) ((dirichletOperator G a ν α)⁻¹ *ᵥ f) x‖ ^ 2) ≤
    13 * L / poincareConst d * Real.exp (-(ε / 2 * t)) * ((L : ℝ) ^ j') ^ 2 *
      Real.sqrt (Green.sqNorm f) :=
  green_G2i G hd hν ha α hα hj1 hjk hj'1 hj'k hy hy'
    (dirichletOperator_mulVec_inv G hd hν ha α hα f) hsupp ht0 ht hε0 hε1 hϱ hsep

end Balaban.Multiscale
