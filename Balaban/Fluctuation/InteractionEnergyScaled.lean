/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.InteractionEnergy
public import Balaban.Fluctuation.StepObjects
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The block energy in physical units: a scale-uniform bound (PHYSCUBIC §2, formula (E*))

The landed bound `energyBlock_bound` of the block energy (`Balaban.Localization.energyBd`) bounds
every bond difference of the fluctuation field by `2V` and uses the mass `ν` and the multiplier
bound `ρ` without their scale factors.  On a full level (`IsLevel Hm n`, `IsLevel Gp (n+1)`) the
weighted sup bounds give much more: a bond difference is at most `V / L^n`, the multiplier is at most
`ρ / L^{2(n+1)}` and the mass is at most `L^{-2(n+1)}`.  Hence every term of the density except the
level term (which already carries `a_n / L^{2n}`) gains a factor `L^{-2n}`, and the block bound
`energyBdScaled` equals `L^{n(d-2)}` times a constant independent of the scale `n`
(`energyBdScaled_eq`, `energyBdScaled_le`), instead of `L^{nd}` times a constant.

The gain over the landed bound is a factor of order `L^{2n}` in the gradient, mass and multiplier
terms.  The landed `energyBd` is kept as the (weaker) bound; propagation to the activity bound and
the physical corollary belong to later packages.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation Finset Matrix

section Scaled

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {Hm : GeneratingSet d L (N₁ * L ^ m₁) K ϱm}

/-- **The density bound in physical units** on a full level.  With `c_n = a_n / L^{2n}` the level
term is `½ c_n N (δ+V)²`; a bond difference is at most `V / L^n`, the mass term is at most
`L^{-2(n+1)} N V²`, the multiplier term at most `ρ L^{-2(n+1)} N V²`. -/
theorem energyDensity_bound_scaled {a : ℕ → ℝ} {ν : ℝ} {n : ℕ} (hnK : n ≤ K) (ha : 0 ≤ a n)
    (hν : 0 ≤ ν) (hmass : ν * ((L : ℝ) ^ (n + 1)) ^ 2 ≤ 1)
    (hHm : IsLevel Hm n) (hGp : IsLevel Gp (n + 1))
    {α : Gp.Ω 1 → ℂ} {δφ : Hm.Ω 1 × Fin N → ℂ} {ψ' : CTorus d L N₁ m₁ K → Fin N → ℂ}
    {V δ ρ : ℝ} (hV : 0 ≤ V) (hρ : 0 ≤ ρ)
    (hsup : SupBounds Hm δφ V)
    (hα : ∀ x : Gp.Ω 1, Gp.spacing (x : CTorus d L N₁ m₁ K) ^ 2 * ‖α x‖ ≤ ρ)
    (hψ : ∀ x ∈ Hm.Ω 1, ∀ i, ‖ψ' x i‖ ≤ δ) (x : CTorus d L N₁ m₁ K) :
    ‖energyDensity Gp Hm a ν n α δφ ψ' x‖ ≤
      (1 / 2) * (a n / ((L : ℝ) ^ n) ^ 2) * (N * (δ + V) * (δ + V)) +
        (1 / 2) * (d * (N * (V / (L : ℝ) ^ n) * (V / (L : ℝ) ^ n)) +
          ((1 + ρ) / ((L : ℝ) ^ (n + 1)) ^ 2) * (N * V * V)) := by
  classical
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hLn : 0 < (L : ℝ) ^ n := by positivity
  have hLn1 : 0 < ((L : ℝ) ^ (n + 1)) ^ 2 := by positivity
  set cn : ℝ := (1 / 2) * (a n / ((L : ℝ) ^ n) ^ 2) with hcn
  have hcn0 : 0 ≤ cn := by positivity
  have hxΩ : x ∈ Hm.Ω 1 := (hHm x).1
  have hspH : Hm.spacing x = (L : ℝ) ^ n := by unfold GeneratingSet.spacing; rw [(hHm x).2]
  have hspG : Gp.spacing x = (L : ℝ) ^ (n + 1) := by unfold GeneratingSet.spacing; rw [(hGp x).2]
  unfold energyDensity
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · simp only [hxΩ, ↓reduceIte]
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hcn0]
    refine mul_le_mul_of_nonneg_left ?_ hcn0
    refine norm_sum_mul_le (P := δ + V) (Q := δ + V) (fun i => ?_) (fun i => ?_) <;>
    · refine (norm_sub_le _ _).trans (add_le_add (hψ x hxΩ i) ?_)
      exact norm_blockMean_le' hnK _ x (fun y _ => hsup.val y i)
  · rw [norm_mul]
    have h12 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
    rw [h12]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    have hgrad : ∀ μ : Fin d, ∀ i, ‖svec Hm δφ (x + Pi.single μ 1) i - svec Hm δφ x i‖ ≤
        V / (L : ℝ) ^ n := fun μ i => by
      rw [le_div_iff₀ hLn, mul_comm, ← hspH]; exact hsup.fwd x hxΩ μ i
    have hz : ‖zeroExt (Gp.Ω 1) α x‖ ≤ ρ / ((L : ℝ) ^ (n + 1)) ^ 2 := by
      have hxG : x ∈ Gp.Ω 1 := (hGp x).1
      simp only [zeroExt, hxG, dite_true]
      have h1 := hα ⟨x, hxG⟩
      rw [le_div_iff₀ hLn1]
      simp only at h1
      rw [hspG] at h1
      linarith
    have hν' : ν ≤ 1 / ((L : ℝ) ^ (n + 1)) ^ 2 := by
      rw [le_div_iff₀ hLn1]; exact hmass
    have hNVV : 0 ≤ (N : ℝ) * V * V := by positivity
    have hsq : ‖∑ i, svec Hm δφ x i * svec Hm δφ x i‖ ≤ N * V * V :=
      norm_sum_mul_le (fun i => hsup.val x i) (fun i => hsup.val x i)
    have b1 : ‖∑ μ : Fin d, ∑ i, (svec Hm δφ (x + Pi.single μ 1) i - svec Hm δφ x i) *
        (svec Hm δφ (x + Pi.single μ 1) i - svec Hm δφ x i)‖ ≤
        d * (N * (V / (L : ℝ) ^ n) * (V / (L : ℝ) ^ n)) := by
      refine (norm_sum_le _ _).trans ?_
      calc ∑ μ : Fin d, ‖∑ i, (svec Hm δφ (x + Pi.single μ 1) i - svec Hm δφ x i) *
            (svec Hm δφ (x + Pi.single μ 1) i - svec Hm δφ x i)‖
          ≤ ∑ _μ : Fin d, (N * (V / (L : ℝ) ^ n) * (V / (L : ℝ) ^ n)) :=
            Finset.sum_le_sum fun μ _ => norm_sum_mul_le (hgrad μ) (hgrad μ)
        _ = d * (N * (V / (L : ℝ) ^ n) * (V / (L : ℝ) ^ n)) := by simp
    have b2 : ‖(ν : ℂ) * ∑ i, svec Hm δφ x i * svec Hm δφ x i‖ ≤
        (1 / ((L : ℝ) ^ (n + 1)) ^ 2) * (N * V * V) := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hν]
      exact mul_le_mul hν' hsq (norm_nonneg _) (by positivity)
    have b3 : ‖zeroExt (Gp.Ω 1) α x * ∑ i, svec Hm δφ x i * svec Hm δφ x i‖ ≤
        (ρ / ((L : ℝ) ^ (n + 1)) ^ 2) * (N * V * V) := by
      rw [norm_mul]
      exact mul_le_mul hz hsq (norm_nonneg _) (by positivity)
    have e : ((1 + ρ) / ((L : ℝ) ^ (n + 1)) ^ 2) * (N * V * V) =
        (1 / ((L : ℝ) ^ (n + 1)) ^ 2) * (N * V * V) +
          (ρ / ((L : ℝ) ^ (n + 1)) ^ 2) * (N * V * V) := by ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    have := (norm_add_le (∑ μ : Fin d, ∑ i, (svec Hm δφ (x + Pi.single μ 1) i - svec Hm δφ x i) *
        (svec Hm δφ (x + Pi.single μ 1) i - svec Hm δφ x i))
        ((ν : ℂ) * ∑ i, svec Hm δφ x i * svec Hm δφ x i))
    linarith

variable (d L N) in
/-- **The scale-uniform bound of the block energy**: the number of sites `(L^{n+1})^d` of the
block times the bound of the density of `energyDensity_bound_scaled`. -/
noncomputable def energyBdScaled (a : ℕ → ℝ) (n : ℕ) (V δ ρ : ℝ) : ℝ :=
  ((L : ℝ) ^ (n + 1)) ^ d * ((1 / 2) * (a n / ((L : ℝ) ^ n) ^ 2) * (N * (δ + V) * (δ + V)) +
    (1 / 2) * (d * (N * (V / (L : ℝ) ^ n) * (V / (L : ℝ) ^ n)) +
      ((1 + ρ) / ((L : ℝ) ^ (n + 1)) ^ 2) * (N * V * V)))

variable (d L N) in
/-- **The scale-free constant** of `energyBdScaled`:
`L^d · ½ N (a_n (δ+V)² + (d + (1+ρ)/L²) V²)`. -/
noncomputable def energyConstScaled (a : ℕ → ℝ) (n : ℕ) (V δ ρ : ℝ) : ℝ :=
  (L : ℝ) ^ d * ((1 / 2) * (N * (a n * (δ + V) ^ 2 + (d + (1 + ρ) / (L : ℝ) ^ 2) * V ^ 2)))

omit [NeZero L] in
theorem energyBdScaled_nonneg {a : ℕ → ℝ} {n : ℕ} (ha : 0 ≤ a n) {V δ ρ : ℝ} (hV : 0 ≤ V)
    (hδ : 0 ≤ δ) (hρ : 0 ≤ ρ) : 0 ≤ energyBdScaled d L N a n V δ ρ := by
  unfold energyBdScaled
  have hL : (0 : ℝ) ≤ L := Nat.cast_nonneg _
  positivity

/-- **The block energy is bounded in physical units** on a full level. -/
theorem energyBlock_bound_scaled {a : ℕ → ℝ} {ν : ℝ} {n : ℕ} (hn : n + 1 ≤ K) (ha : 0 ≤ a n)
    (hν : 0 ≤ ν) (hmass : ν * ((L : ℝ) ^ (n + 1)) ^ 2 ≤ 1)
    (hHm : IsLevel Hm n) (hGp : IsLevel Gp (n + 1))
    {α : Gp.Ω 1 → ℂ} {δφ : Hm.Ω 1 × Fin N → ℂ} {ψ' : CTorus d L N₁ m₁ K → Fin N → ℂ}
    {V δ ρ : ℝ} (hV : 0 ≤ V) (hρ : 0 ≤ ρ) (hsup : SupBounds Hm δφ V)
    (hα : ∀ x : Gp.Ω 1, Gp.spacing (x : CTorus d L N₁ m₁ K) ^ 2 * ‖α x‖ ≤ ρ)
    (hψ : ∀ x ∈ Hm.Ω 1, ∀ i, ‖ψ' x i‖ ≤ δ)
    (z : Torus d (N₁ * L ^ m₁ * L ^ (K - (n + 1)))) :
    ‖energyBlock Gp Hm a ν n α δφ ψ' z‖ ≤ energyBdScaled d L N a n V δ ρ := by
  classical
  have hd := fun x => energyDensity_bound_scaled (Gp := Gp) (Hm := Hm) (by omega : n ≤ K) ha hν
    hmass hHm hGp hV hρ hsup hα hψ x
  have hB0 := (norm_nonneg _).trans (hd 0)
  unfold energyBlock energyBdScaled
  calc _ ≤ ∑ x ∈ Finset.univ.filter (fun x : CTorus d L N₁ m₁ K =>
          jBlock d L (N₁ * L ^ m₁) K (n + 1) x = z),
        ‖energyDensity Gp Hm a ν n α δφ ψ' x‖ := norm_sum_le _ _
    _ ≤ ∑ _x ∈ Finset.univ.filter (fun x : CTorus d L N₁ m₁ K =>
          jBlock d L (N₁ * L ^ m₁) K (n + 1) x = z),
        ((1 / 2) * (a n / ((L : ℝ) ^ n) ^ 2) * (N * (δ + V) * (δ + V)) +
          (1 / 2) * (d * (N * (V / (L : ℝ) ^ n) * (V / (L : ℝ) ^ n)) +
            ((1 + ρ) / ((L : ℝ) ^ (n + 1)) ^ 2) * (N * V * V))) :=
        Finset.sum_le_sum fun x _ => hd x
    _ = (blockSites d L N₁ m₁ K n z).card * _ := by
        rw [Finset.sum_const, nsmul_eq_mul]; rfl
    _ ≤ _ := mul_le_mul_of_nonneg_right (card_blockSites_le Hm n hn z) hB0

omit [NeZero L] in
/-- **The factorization**: for `d ≥ 2`, `energyBdScaled = L^{n(d-2)} ·` (a constant that depends on
the scale only through `a_n`). -/
theorem energyBdScaled_eq (hd : 2 ≤ d) (a : ℕ → ℝ) (n : ℕ) (V δ ρ : ℝ) (hL : (L : ℝ) ≠ 0) :
    energyBdScaled d L N a n V δ ρ = (L : ℝ) ^ (n * (d - 2)) * energyConstScaled d L N a n V δ ρ := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 2 := ⟨d - 2, by omega⟩
  unfold energyBdScaled energyConstScaled
  simp only [Nat.add_sub_cancel]
  field_simp
  ring

omit [NeZero L] in
/-- **The constant (E\*)**: with `V = Q δ`, `a_n ≤ 2`, `L ≥ 3`,
`energyBdScaled ≤ L^{n(d-2)} · L^d · C_E` with `C_E = (N/2)[2(1+Q)² + (d+1+ρ)Q²]δ²`. -/
theorem energyBdScaled_le (hd : 2 ≤ d) (hL3 : 3 ≤ L) {a : ℕ → ℝ} {n : ℕ}
    (ha2 : a n ≤ 2) {Q δ ρ : ℝ} (hρ : 0 ≤ ρ) :
    energyBdScaled d L N a n (Q * δ) δ ρ ≤
      (L : ℝ) ^ (n * (d - 2)) * ((L : ℝ) ^ d *
        ((N / 2) * (2 * (1 + Q) ^ 2 + (d + 1 + ρ) * Q ^ 2) * δ ^ 2)) := by
  have hL3' : (3 : ℝ) ≤ L := by exact_mod_cast hL3
  have hL0 : (L : ℝ) ≠ 0 := by positivity
  rw [energyBdScaled_eq hd _ _ _ _ _ hL0]
  unfold energyConstScaled
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hL2 : (1 : ℝ) ≤ (L : ℝ) ^ 2 := by nlinarith
  have h1 : a n * (δ + Q * δ) ^ 2 ≤ 2 * (1 + Q) ^ 2 * δ ^ 2 := by
    have : (δ + Q * δ) ^ 2 = (1 + Q) ^ 2 * δ ^ 2 := by ring
    rw [this]
    nlinarith [sq_nonneg ((1 + Q) * δ)]
  have h2 : (1 + ρ) / (L : ℝ) ^ 2 ≤ 1 + ρ := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have h3 : ((d : ℝ) + (1 + ρ) / (L : ℝ) ^ 2) * (Q * δ) ^ 2 ≤ (d + 1 + ρ) * Q ^ 2 * δ ^ 2 := by
    have : (Q * δ) ^ 2 = Q ^ 2 * δ ^ 2 := by ring
    rw [this]
    have h4 : (d : ℝ) + (1 + ρ) / (L : ℝ) ^ 2 ≤ d + 1 + ρ := by linarith
    nlinarith [mul_nonneg (sq_nonneg Q) (sq_nonneg δ)]
  nlinarith

omit [NeZero L] in
/-- **The identity that makes the amplitude scale-uniform**: `β · energyBdScaled = β_k · (constant)`
with `β_k = β L^{k(d-2)}` (`StepSetting.betaU`); the constant `energyConstScaled` depends on the scale
only through `a_k`. -/
theorem beta_mul_energyBdScaled {k N₁ m₁ : ℕ} [NeZero N₁] {ϱ : ℝ} [NeZero L]
    (S : StepSetting d L N₁ m₁ k N ϱ) (a : ℕ → ℝ) (V δ ρ : ℝ) :
    S.β * energyBdScaled d L N a k V δ ρ = S.betaU * energyConstScaled d L N a k V δ ρ := by
  have hL : (L : ℝ) ≠ 0 := by
    have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    exact this.ne'
  unfold energyBdScaled energyConstScaled StepSetting.betaU
  field_simp
  ring

end Scaled

end Balaban.Localization
