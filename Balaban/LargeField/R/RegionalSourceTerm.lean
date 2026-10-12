/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RegionalTails
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# The near source term of the grouped regional correction (Q13-GROUPED §2, (4) second part, (5), (7))

The near source term is `v2Part`, `Σ_{y∈R} Σ_{x∈Bc} v₂(y, x) ν_j (⟨h, u_x⟩ - ⟨h, u_y⟩)`.

* **(M) Moments.**  If `v₂(y, ·)` is a sum of per-polymer coefficients `c_X(y, ·)` over the
  polymers through `y`, with `Σ_x ‖c_X(y, x)‖ ≤ A₂ e^{-κ sz X}`, and a distance weight `D` satisfies
  `D(y, x) ≤ sz X + c₀` for `x, y ∈ X`, then for `κ₀ < κ`
  `Σ_x ‖v₂(y, x)‖ (D² + D) ≤ A₂ · Cmom c₀ (κ - κ₀) · K₀`,
  with the explicit constant `Cmom c₀ ρ = ((c₀+1)² + (c₀+1)) (1 + 2/ρ)²` (`cmom_bound`).
* **(N) Near source term.**  With the pointwise bound `‖ν_j(⟨h,u_x⟩ - ⟨h,u_y⟩)‖ ≤ C_s (D² + D) σ³ ε²`
  (derived from the data in `pair_bound_of_data` via `dotC_source_term_le`, `C_s = sourceConstC B`)
  the near source term is at most `|R| · C_s σ³ ε² · A₂ Cmom K₀` (`v2Part_le`), and with the scale
  relations of `v2_scale_le_rate`, at most `|R| · C₂' E₀ s^(d+α₃)` (`v2Part_le_power`).
* The instance for `polyUniv`, `sizeJ`, `D = supDist / a_j`, `c₀ = 2 L`: `v2_moment_polyUniv`.

## What is and is not proved

The per-polymer coefficient bounds for the actual `v₂` (PinJet / anisotropic tube), the data bounds
of the small-field class (`‖ψ_x - ψ_y‖ ≤ D σ ε`, `‖ψ‖₂ ≤ B`, `σ² ε ≤ 1/2`, ...), and the scale
relations are inputs (hypotheses).  Nothing here bounds the actual renormalization-group terms.
-/

@[expose] public section

open Finset Real

namespace Balaban.LargeField.RegionalSourceTerm

/-! ### (T1) The elementary bound -/

/-- The moment constant `((c₀+1)² + (c₀+1)) (1 + 2/ρ)²`. -/
noncomputable def Cmom (c₀ ρ : ℝ) : ℝ := ((c₀ + 1) ^ 2 + (c₀ + 1)) * (1 + 2 / ρ) ^ 2

theorem cmom_nonneg {c₀ ρ : ℝ} (hc : 0 ≤ c₀) (hρ : 0 < ρ) : 0 ≤ Cmom c₀ ρ := by
  unfold Cmom; positivity

/-- `(1 + t)² e^{-ρ t} ≤ (1 + 2/ρ)²` for `t ≥ 0`, `ρ > 0`. -/
theorem one_add_sq_exp_le {t ρ : ℝ} (ht : 0 ≤ t) (hρ : 0 < ρ) :
    (1 + t) ^ 2 * exp (-ρ * t) ≤ (1 + 2 / ρ) ^ 2 := by
  have h1 : t * exp (-(ρ * t / 2)) ≤ 2 / ρ := by
    have hp : 0 < exp (ρ * t / 2) := Real.exp_pos _
    have h2 : ρ * t / 2 ≤ exp (ρ * t / 2) := by
      have := Real.add_one_le_exp (ρ * t / 2); linarith
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_div_iff₀ hp hρ]
    nlinarith
  have h3 : exp (-(ρ * t / 2)) ≤ 1 := Real.exp_le_one_iff.2 (by
    have : 0 ≤ ρ * t / 2 := by positivity
    linarith)
  have h4 : (1 + t) * exp (-(ρ * t / 2)) ≤ 1 + 2 / ρ := by
    nlinarith [Real.exp_pos (-(ρ * t / 2))]
  have h5 : exp (-ρ * t) = exp (-(ρ * t / 2)) ^ 2 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [h5, ← mul_pow]
  exact pow_le_pow_left₀ (by positivity) h4 2

/-- **(T1)** For `t ≥ 0`, `c₀ ≥ 0`, `ρ > 0`:
`((t + c₀)² + (t + c₀)) e^{-ρ t} ≤ Cmom c₀ ρ`. -/
theorem cmom_bound {t c₀ ρ : ℝ} (ht : 0 ≤ t) (hc : 0 ≤ c₀) (hρ : 0 < ρ) :
    ((t + c₀) ^ 2 + (t + c₀)) * exp (-ρ * t) ≤ Cmom c₀ ρ := by
  have h1 : (t + c₀) ^ 2 + (t + c₀) ≤ ((c₀ + 1) ^ 2 + (c₀ + 1)) * (1 + t) ^ 2 := by
    nlinarith [mul_nonneg ht hc, mul_nonneg ht ht, mul_nonneg (mul_nonneg ht ht) hc,
      mul_nonneg (mul_nonneg ht hc) hc, mul_nonneg hc hc]
  calc _ ≤ ((c₀ + 1) ^ 2 + (c₀ + 1)) * (1 + t) ^ 2 * exp (-ρ * t) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = ((c₀ + 1) ^ 2 + (c₀ + 1)) * ((1 + t) ^ 2 * exp (-ρ * t)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (one_add_sq_exp_le ht hρ) (by positivity)

/-! ### (T2) The moment bound, abstract -/

section Moment

variable {ι : Type*} [Fintype ι]

open Classical in
/-- **(M) Moment bound for `v₂`.**  For a centre `y`: `v₂(x) = Σ_{X∈U, y,x∈X} c X y x`
(`hv`), `Σ_{x∈X} ‖c X y x‖ ≤ A₂ e^{-κ sz X}` for `X ∈ U` through `y` (`hc`), `sz ≥ 0` on them,
`0 ≤ D x ≤ sz X + c₀` whenever `x, y ∈ X` (`hD`), entropy `Σ_{X∈U, y∈X} e^{-κ₀ sz X} ≤ K₀`, and
`κ₀ < κ`.  Then `Σ_x ‖v₂ x‖ (D x² + D x) ≤ A₂ · Cmom c₀ (κ - κ₀) · K₀`. -/
theorem v2_moment_le (U : Finset (Set ι)) (c : Set ι → ι → ι → ℂ) (v₂ : ι → ℂ) (y : ι)
    (sz : Set ι → ℝ) (D : ι → ℝ) {A₂ K₀ κ κ₀ c₀ : ℝ} (hA₂ : 0 ≤ A₂) (hc₀ : 0 ≤ c₀)
    (hκ : κ₀ < κ)
    (hv : ∀ x, v₂ x = ∑ X ∈ U.filter (fun X => y ∈ X ∧ x ∈ X), c X y x)
    (hc : ∀ X ∈ U, y ∈ X → ∑ x ∈ Finset.univ.filter (fun x => x ∈ X), ‖c X y x‖ ≤
      A₂ * exp (-κ * sz X))
    (hsz : ∀ X ∈ U, y ∈ X → 0 ≤ sz X)
    (hD0 : ∀ x, 0 ≤ D x)
    (hD : ∀ X ∈ U, y ∈ X → ∀ x ∈ X, D x ≤ sz X + c₀)
    (hent : ∑ X ∈ U.filter (fun X => y ∈ X), exp (-κ₀ * sz X) ≤ K₀) :
    ∑ x, ‖v₂ x‖ * (D x ^ 2 + D x) ≤ A₂ * Cmom c₀ (κ - κ₀) * K₀ := by
  set W : ℝ → ℝ := fun t => (t + c₀) ^ 2 + (t + c₀) with hW
  have hρ : 0 < κ - κ₀ := sub_pos.2 hκ
  -- pointwise in x
  have h1 : ∀ x, ‖v₂ x‖ * (D x ^ 2 + D x) ≤
      ∑ X ∈ U.filter (fun X => y ∈ X), (if x ∈ X then ‖c X y x‖ * W (sz X) else 0) := by
    intro x
    have hw : 0 ≤ D x ^ 2 + D x := by have := hD0 x; positivity
    calc ‖v₂ x‖ * (D x ^ 2 + D x)
        ≤ (∑ X ∈ U.filter (fun X => y ∈ X ∧ x ∈ X), ‖c X y x‖) * (D x ^ 2 + D x) := by
          rw [hv x]; exact mul_le_mul_of_nonneg_right (norm_sum_le _ _) hw
      _ = ∑ X ∈ U.filter (fun X => y ∈ X ∧ x ∈ X), ‖c X y x‖ * (D x ^ 2 + D x) :=
          Finset.sum_mul _ _ _
      _ ≤ ∑ X ∈ U.filter (fun X => y ∈ X ∧ x ∈ X), ‖c X y x‖ * W (sz X) := by
          refine Finset.sum_le_sum fun X hX => ?_
          obtain ⟨hXU, hyX, hxX⟩ := by simpa [Finset.mem_filter, and_assoc] using hX
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          have h0 := hD0 x
          have h2 := hD X hXU hyX x hxX
          simp only [hW]
          nlinarith
      _ = _ := by rw [← Finset.sum_filter, Finset.filter_filter]
  have h2 : ∀ X ∈ U.filter (fun X => y ∈ X),
      ∑ x, (if x ∈ X then ‖c X y x‖ * W (sz X) else 0) ≤
        A₂ * Cmom c₀ (κ - κ₀) * exp (-κ₀ * sz X) := by
    intro X hX
    obtain ⟨hXU, hyX⟩ := Finset.mem_filter.1 hX
    have e : ∑ x, (if x ∈ X then ‖c X y x‖ * W (sz X) else 0) =
        (∑ x ∈ Finset.univ.filter (fun x => x ∈ X), ‖c X y x‖) * W (sz X) := by
      rw [Finset.sum_mul, Finset.sum_filter]
    rw [e]
    have hs := hsz X hXU hyX
    have hb := cmom_bound hs hc₀ hρ
    have hW0 : 0 ≤ W (sz X) := by simp only [hW]; positivity
    have hexp : exp (-κ * sz X) = exp (-(κ - κ₀) * sz X) * exp (-κ₀ * sz X) := by
      rw [← Real.exp_add]; congr 1; ring
    calc (∑ x ∈ Finset.univ.filter (fun x => x ∈ X), ‖c X y x‖) * W (sz X)
        ≤ A₂ * exp (-κ * sz X) * W (sz X) := mul_le_mul_of_nonneg_right (hc X hXU hyX) hW0
      _ = A₂ * (W (sz X) * exp (-(κ - κ₀) * sz X)) * exp (-κ₀ * sz X) := by rw [hexp]; ring
      _ ≤ A₂ * Cmom c₀ (κ - κ₀) * exp (-κ₀ * sz X) := by
          have : W (sz X) * exp (-(κ - κ₀) * sz X) ≤ Cmom c₀ (κ - κ₀) := hb
          have := mul_le_mul_of_nonneg_left this hA₂
          exact mul_le_mul_of_nonneg_right this (Real.exp_pos _).le
  calc ∑ x, ‖v₂ x‖ * (D x ^ 2 + D x)
      ≤ ∑ x, ∑ X ∈ U.filter (fun X => y ∈ X), (if x ∈ X then ‖c X y x‖ * W (sz X) else 0) :=
        Finset.sum_le_sum fun x _ => h1 x
    _ = ∑ X ∈ U.filter (fun X => y ∈ X), ∑ x, (if x ∈ X then ‖c X y x‖ * W (sz X) else 0) :=
        Finset.sum_comm
    _ ≤ ∑ X ∈ U.filter (fun X => y ∈ X), A₂ * Cmom c₀ (κ - κ₀) * exp (-κ₀ * sz X) :=
        Finset.sum_le_sum h2
    _ = A₂ * Cmom c₀ (κ - κ₀) * ∑ X ∈ U.filter (fun X => y ∈ X), exp (-κ₀ * sz X) :=
        (Finset.mul_sum _ _ _).symm
    _ ≤ A₂ * Cmom c₀ (κ - κ₀) * K₀ :=
        mul_le_mul_of_nonneg_left hent (mul_nonneg hA₂ (cmom_nonneg hc₀ hρ))

end Moment

/-! ### (T3) The near source term -/

section Source

open Balaban.SmallField Balaban.SmallField.Def6 Balaban.LargeField.Def7v2
  Balaban.LargeField.RegionalArith Balaban.LargeField.RegionEnergyAlgebra

/-- **(5) for the pair `(y, x)`, from the data.**  With `b = ν_j h` and the data hypotheses of
`dotC_source_term_le` (`ψ_x`, `ψ_y` in the `ℓ²` ball of radius `B`, `‖ψ_x - ψ_y‖₂ ≤ D σ ε`,
`‖ν_j h - ν' ψ_y‖₂ ≤ σ² ε`, `|ψ·ψ - 1|` small, `σ² ε ≤ 1/2`, ...):
`‖ν_j (⟨h, u_x⟩ - ⟨h, u_y⟩)‖ ≤ C_s (D² + D) σ³ ε²`, `C_s = sourceConstC B`. -/
theorem pair_bound_of_data {N : ℕ} {ψx ψy h : Fin N → ℂ} {νj ν' B σ ε D : ℝ}
    (hax : ‖dot ψx ψx - 1‖ ≤ 1 / 2) (hBx : nrm2 ψx ≤ B) (hBy : nrm2 ψy ≤ B)
    (hD : nrm2 (ψx - ψy) ≤ D * σ * ε) (hb : nrm2 ((νj : ℂ) • h - (ν' : ℂ) • ψy) ≤ σ ^ 2 * ε)
    (hn : ‖dot ψy ψy - 1‖ ≤ σ ^ 2 * ε) (hη : σ ^ 2 * ε ≤ 1 / 2) (hν0 : 0 ≤ ν')
    (hνσ : ν' ≤ σ ^ 2) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (hε0 : 0 ≤ ε) (hD0 : 0 ≤ D) :
    ‖(νj : ℂ) * (dot h (unitDirC ψx) - dot h (unitDirC ψy))‖ ≤
      sourceConstC B * (D ^ 2 + D) * σ ^ 3 * ε ^ 2 := by
  have := dotC_source_term_le (b := (νj : ℂ) • h) hax hBx hBy hD hb hn hη hν0 hνσ hσ0 hσ1 hε0 hD0
  rwa [dot_smul_left, dot_sub_right] at this

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁]

open Classical in
/-- **(7) for the near source term.**  For every centre `y ∈ R`: the decomposition of `v₂ y ·`
over the polymers `U` through `y`, the per-polymer mass bound, sizes `sz ≥ 0`, the weight bound
`0 ≤ D y x ≤ sz X + c₀` for `x, y ∈ X`, and the entropy bound; and the pointwise source bound
`‖ν_j(⟨h,u_x⟩ - ⟨h,u_y⟩)‖ ≤ C_s (D² + D) σ³ ε²` for `x ∈ Bc` (from `pair_bound_of_data`).  Then
`‖v2Part‖ ≤ |R| · C_s σ³ ε² · A₂ Cmom K₀`. -/
theorem v2Part_le (U : Finset (Set (Localization.CTorus d L N₁ m₁ k)))
    (c : Set (Localization.CTorus d L N₁ m₁ k) → Localization.CTorus d L N₁ m₁ k →
      Localization.CTorus d L N₁ m₁ k → ℂ)
    (v₂ : Localization.CTorus d L N₁ m₁ k → Localization.CTorus d L N₁ m₁ k → ℂ) (νj : ℝ)
    (R Bc : Finset (Localization.CTorus d L N₁ m₁ k)) (ψ : Fld d L N₁ m₁ k N) (h : Fin N → ℂ)
    (sz : Set (Localization.CTorus d L N₁ m₁ k) → ℝ)
    (D : Localization.CTorus d L N₁ m₁ k → Localization.CTorus d L N₁ m₁ k → ℝ)
    {A₂ K₀ κ κ₀ c₀ Cs σ ε : ℝ} (hA₂ : 0 ≤ A₂) (hc₀ : 0 ≤ c₀) (hκ : κ₀ < κ) (hCs : 0 ≤ Cs)
    (hσ : 0 ≤ σ)
    (hv : ∀ y ∈ R, ∀ x, v₂ y x = ∑ X ∈ U.filter (fun X => y ∈ X ∧ x ∈ X), c X y x)
    (hc : ∀ y ∈ R, ∀ X ∈ U, y ∈ X → ∑ x ∈ Finset.univ.filter (fun x => x ∈ X), ‖c X y x‖ ≤
      A₂ * exp (-κ * sz X))
    (hsz : ∀ y ∈ R, ∀ X ∈ U, y ∈ X → 0 ≤ sz X)
    (hD0 : ∀ y ∈ R, ∀ x, 0 ≤ D y x)
    (hD : ∀ y ∈ R, ∀ X ∈ U, y ∈ X → ∀ x ∈ X, D y x ≤ sz X + c₀)
    (hent : ∀ y ∈ R, ∑ X ∈ U.filter (fun X => y ∈ X), exp (-κ₀ * sz X) ≤ K₀)
    (hpt : ∀ y ∈ R, ∀ x ∈ Bc,
      ‖(νj : ℂ) * (dot h (unitDirC (ψ x)) - dot h (unitDirC (ψ y)))‖ ≤
        Cs * (D y x ^ 2 + D y x) * σ ^ 3 * ε ^ 2) :
    ‖v2Part v₂ νj R Bc ψ h‖ ≤
      R.card * (Cs * σ ^ 3 * ε ^ 2 * (A₂ * Cmom c₀ (κ - κ₀) * K₀)) := by
  unfold v2Part
  refine (norm_sum_le _ _).trans ?_
  calc ∑ y ∈ R, ‖∑ x ∈ Bc, v₂ y x * ((νj : ℂ) * (dot h (unitDirC (ψ x)) -
        dot h (unitDirC (ψ y))))‖
      ≤ ∑ _y ∈ R, Cs * σ ^ 3 * ε ^ 2 * (A₂ * Cmom c₀ (κ - κ₀) * K₀) := by
        refine Finset.sum_le_sum fun y hy => ?_
        refine (norm_sum_le _ _).trans ?_
        have hm := v2_moment_le U c (v₂ y) y sz (D y) hA₂ hc₀ hκ (hv y hy) (hc y hy) (hsz y hy)
          (hD0 y hy) (hD y hy) (hent y hy)
        calc ∑ x ∈ Bc, ‖v₂ y x * ((νj : ℂ) * (dot h (unitDirC (ψ x)) -
              dot h (unitDirC (ψ y))))‖
            ≤ ∑ x ∈ Bc, ‖v₂ y x‖ * (Cs * (D y x ^ 2 + D y x) * σ ^ 3 * ε ^ 2) := by
              refine Finset.sum_le_sum fun x hx => ?_
              rw [norm_mul]
              exact mul_le_mul_of_nonneg_left (hpt y hy x hx) (norm_nonneg _)
          _ = Cs * σ ^ 3 * ε ^ 2 * ∑ x ∈ Bc, ‖v₂ y x‖ * (D y x ^ 2 + D y x) := by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun x _ => by ring
          _ ≤ Cs * σ ^ 3 * ε ^ 2 * ∑ x, ‖v₂ y x‖ * (D y x ^ 2 + D y x) := by
              refine mul_le_mul_of_nonneg_left ?_ (by positivity)
              refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun x _ _ => ?_
              have := hD0 y hy x
              positivity
          _ ≤ _ := mul_le_mul_of_nonneg_left hm (by positivity)
    _ = R.card * (Cs * σ ^ 3 * ε ^ 2 * (A₂ * Cmom c₀ (κ - κ₀) * K₀)) := by simp

open Classical in
/-- **(7), scaled.**  Under the hypotheses of `v2Part_le` with `σ = C₀ s`, `ε = ε_q`,
`A₂ = 4 E₀ / r²`, `r = ε_j / K_r`, `ε_q / ε_j ≤ K_R s^α`, `3 + 2α = d + α₃ + α₁` (`α₁ ≥ 0`),
`0 < s ≤ 1`:
`‖v2Part‖ ≤ |R| · C₂' E₀ s^(d+α₃)` with `C₂' = 4 C_s Cmom K₀ C₀³ K_r² K_R²`. -/
theorem v2Part_le_power (U : Finset (Set (Localization.CTorus d L N₁ m₁ k)))
    (c : Set (Localization.CTorus d L N₁ m₁ k) → Localization.CTorus d L N₁ m₁ k →
      Localization.CTorus d L N₁ m₁ k → ℂ)
    (v₂ : Localization.CTorus d L N₁ m₁ k → Localization.CTorus d L N₁ m₁ k → ℂ) (νj : ℝ)
    (R Bc : Finset (Localization.CTorus d L N₁ m₁ k)) (ψ : Fld d L N₁ m₁ k N) (h : Fin N → ℂ)
    (sz : Set (Localization.CTorus d L N₁ m₁ k) → ℝ)
    (D : Localization.CTorus d L N₁ m₁ k → Localization.CTorus d L N₁ m₁ k → ℝ)
    {E₀ K₀ κ κ₀ c₀ Cs C₀ K_r K_R s α εj εq r dd α₁ α₃ : ℝ} (hE : 0 ≤ E₀) (hK₀ : 0 ≤ K₀)
    (hc₀ : 0 ≤ c₀) (hκ : κ₀ < κ) (hCs : 0 ≤ Cs) (hC₀ : 0 ≤ C₀) (hKr : 0 < K_r) (hs : 0 < s)
    (hs1 : s ≤ 1) (hεj : 0 < εj) (hεq : 0 ≤ εq) (hr : r = εj / K_r)
    (hR : εq / εj ≤ K_R * s ^ α) (hrel : 3 + 2 * α = dd + α₃ + α₁) (hα₁ : 0 ≤ α₁)
    (hv : ∀ y ∈ R, ∀ x, v₂ y x = ∑ X ∈ U.filter (fun X => y ∈ X ∧ x ∈ X), c X y x)
    (hc : ∀ y ∈ R, ∀ X ∈ U, y ∈ X → ∑ x ∈ Finset.univ.filter (fun x => x ∈ X), ‖c X y x‖ ≤
      (4 * E₀ / r ^ 2) * exp (-κ * sz X))
    (hsz : ∀ y ∈ R, ∀ X ∈ U, y ∈ X → 0 ≤ sz X)
    (hD0 : ∀ y ∈ R, ∀ x, 0 ≤ D y x)
    (hD : ∀ y ∈ R, ∀ X ∈ U, y ∈ X → ∀ x ∈ X, D y x ≤ sz X + c₀)
    (hent : ∀ y ∈ R, ∑ X ∈ U.filter (fun X => y ∈ X), exp (-κ₀ * sz X) ≤ K₀)
    (hpt : ∀ y ∈ R, ∀ x ∈ Bc,
      ‖(νj : ℂ) * (dot h (unitDirC (ψ x)) - dot h (unitDirC (ψ y)))‖ ≤
        Cs * (D y x ^ 2 + D y x) * (C₀ * s) ^ 3 * εq ^ 2) :
    ‖v2Part v₂ νj R Bc ψ h‖ ≤
      R.card * ((4 * Cs * Cmom c₀ (κ - κ₀) * K₀ * C₀ ^ 3 * K_r ^ 2 * K_R ^ 2) * E₀ *
        s ^ (dd + α₃)) := by
  have hr0 : 0 < r := by rw [hr]; positivity
  have hA : 0 ≤ 4 * E₀ / r ^ 2 := by positivity
  have h1 := v2Part_le U c v₂ νj R Bc ψ h sz D (σ := C₀ * s) (ε := εq) hA hc₀ hκ hCs
    (by positivity) hv hc hsz hD0 hD hent hpt
  have hCm := cmom_nonneg hc₀ (sub_pos.2 hκ)
  have h2 := v2_scale_le_rate (M₂ := Cs * Cmom c₀ (κ - κ₀) * K₀ / 2) (E₀ := E₀) (C₀ := C₀)
    (K_r := K_r) (K_R := K_R) (s := s) (α := α) (εj := εj) (εq := εq) (r := r) (d := dd)
    (α₁ := α₁) (α₃ := α₃) (by positivity) hE hC₀ hKr hs hs1 hεj hεq hr hR hrel hα₁
  refine h1.trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  have e1 : Cs * (C₀ * s) ^ 3 * εq ^ 2 * (4 * E₀ / r ^ 2 * Cmom c₀ (κ - κ₀) * K₀) =
      8 * (Cs * Cmom c₀ (κ - κ₀) * K₀ / 2) * E₀ * (1 / r ^ 2) * (C₀ * s) ^ 3 * εq ^ 2 := by
    ring
  have e2 : 8 * (Cs * Cmom c₀ (κ - κ₀) * K₀ / 2) * C₀ ^ 3 * K_r ^ 2 * K_R ^ 2 =
      4 * Cs * Cmom c₀ (κ - κ₀) * K₀ * C₀ ^ 3 * K_r ^ 2 * K_R ^ 2 := by ring
  rw [e1]
  refine h2.trans (le_of_eq ?_)
  rw [e2]

end Source

/-! ### (T4) The instance for `polyUniv`, `sizeJ`, `supDist / a_j` -/

section Instance

open Balaban Balaban.Localization Balaban.Fluctuation Balaban.SmallField Balaban.LargeField
  Balaban.LargeField.Def7 Balaban.LargeField.RegionShrink Balaban.LargeField.RegionEnergyAlgebra
  Balaban.LargeField.RegionalTails

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N k m₁ : ℕ} {ϱ : ℝ} (C : SFCtx S n R M K N k m₁ ϱ)

open Classical in
/-- **The moment bound for the landed objects.**  Distance weight
`D(y, x) = supDist y x / L^(j+m₀+m₁)` (distance in units of `a_j`), sizes `sizeJ`, `c₀ = 2 L`, the
entropy from `entropy_polyUniv` (`κ₀ ≥ aEnt d L + 1`).  The decomposition `hv` of `v₂(y, ·)` over
the polymers of `polyUniv C j` and the per-polymer coefficient bound `hc` are inputs.
`Σ_x ‖v₂ x‖ (D² + D) ≤ A₂ · Cmom (2L) (κ - κ₀) · K0 d L κ₀`. -/
theorem v2_moment_polyUniv {j : ℕ} (hN : S.L ^ C.m₀ ∣ C.N₁) (hj : j ≤ k)
    (c : Set (Localization.CTorus S.d S.L C.N₁ m₁ k) → Localization.CTorus S.d S.L C.N₁ m₁ k →
      Localization.CTorus S.d S.L C.N₁ m₁ k → ℂ)
    (v₂ : Localization.CTorus S.d S.L C.N₁ m₁ k → ℂ) (y : Localization.CTorus S.d S.L C.N₁ m₁ k)
    {A₂ κ κ₀ : ℝ} (hA₂ : 0 ≤ A₂) (hκ₀ : aEnt S.d S.L + 1 ≤ κ₀) (hκ : κ₀ < κ)
    (hv : ∀ x, v₂ x = ∑ X ∈ (polyUniv C j).filter (fun X => y ∈ X ∧ x ∈ X), c X y x)
    (hc : ∀ X, Def6.IsPolyDom C.m₀ j X → y ∈ X →
      ∑ x ∈ Finset.univ.filter (fun x => x ∈ X), ‖c X y x‖ ≤
        A₂ * exp (-κ * Def6.sizeJ C.m₀ j X)) :
    ∑ x, ‖v₂ x‖ * (((supDist y x : ℝ) / (S.L : ℝ) ^ (j + C.m₀ + m₁)) ^ 2 +
        (supDist y x : ℝ) / (S.L : ℝ) ^ (j + C.m₀ + m₁)) ≤
      A₂ * Cmom (2 * S.L) (κ - κ₀) * K0 S.d S.L κ₀ := by
  have hL : (0 : ℝ) < S.L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne S.L)
  refine v2_moment_le (polyUniv C j) c v₂ y (Def6.sizeJ C.m₀ j)
    (fun x => (supDist y x : ℝ) / (S.L : ℝ) ^ (j + C.m₀ + m₁)) hA₂ (by positivity) hκ hv
    (fun X hX hyX => hc X ((mem_polyUniv C).1 hX) hyX) ?_ (fun x => by positivity) ?_
    (entropy_polyUniv C hN hj y hκ₀)
  · intro X _ _
    unfold Def6.sizeJ
    exact treeLenCovOne_nonneg _ _ _
  · intro X hX hyX x hxX
    have := treeLenCovOne_ge_dist (L := S.L) (N₁ := C.N₁) (m₁ := m₁) (K := k) C.m₀ j
      (exists_cover_struct (m₀ := C.m₀) (j := j) ((mem_polyUniv C).1 hX)) hyX hxX
    unfold Def6.sizeJ
    linarith

end Instance

/-! ### (T5) Non-vacuity: polymers `{0}` and `{0, 1}` on `ZMod 5` -/

section Example

open Balaban.LargeField.RegionalTails

/-- The per-polymer coefficient of the example: mass `e^{-3 |X|}` spread evenly over `X`. -/
noncomputable def exC (X : Set (ZMod 5)) (_y x : ZMod 5) : ℂ :=
  open Classical in if x ∈ X then ((Real.exp (-3 * exSz X) / exSz X : ℝ) : ℂ) else 0

/-- The source coefficient of the example at the centre `0`. -/
noncomputable def exV (x : ZMod 5) : ℂ :=
  open Classical in ∑ X ∈ exU.filter (fun X => (0 : ZMod 5) ∈ X ∧ x ∈ X), exC X 0 x

/-- The distance weight of the example. -/
noncomputable def exD (x : ZMod 5) : ℝ := ((x.val : ℕ) : ℝ)

theorem exC_of_mem {X : Set (ZMod 5)} {y x : ZMod 5} (h : x ∈ X) :
    exC X y x = ((Real.exp (-3 * exSz X) / exSz X : ℝ) : ℂ) := by
  classical
  simp [exC, h]

theorem exD_one : exD 1 = 1 := by
  have hv1 : (1 : ZMod 5).val = 1 := rfl
  unfold exD; rw [hv1]; simp

theorem mem_exU {X : Set (ZMod 5)} : X ∈ exU ↔ X = polyA ∨ X = polyB := by
  classical
  simp [exU]

theorem exV_one : exV 1 = ((Real.exp (-3 * 2) / 2 : ℝ) : ℂ) := by
  classical
  have hf : exU.filter (fun X => (0 : ZMod 5) ∈ X ∧ (1 : ZMod 5) ∈ X) = {polyB} := by
    ext X
    simp only [Finset.mem_filter, Finset.mem_singleton, mem_exU]
    constructor
    · rintro ⟨hX | hX, h0, h1⟩
      · subst hX; simp [polyA] at h1; exact absurd h1 (by decide)
      · exact hX
    · rintro rfl; exact ⟨Or.inr rfl, by simp [polyB], by simp [polyB]⟩
  unfold exV
  rw [hf, Finset.sum_singleton]
  rw [exC_of_mem (by simp [polyB]), ncard_polyB]

/-- The hypotheses of `v2_moment_le` hold in the example (`A₂ = 1`, `κ = 3`, `κ₀ = 1`, `c₀ = 0`,
`K₀ = 2`), the left side is nonzero, and the bound holds. -/
theorem example_moment :
    0 < ∑ x : ZMod 5, ‖exV x‖ * (exD x ^ 2 + exD x) ∧
    ∑ x : ZMod 5, ‖exV x‖ * (exD x ^ 2 + exD x) ≤ 1 * Cmom 0 (3 - 1) * 2 := by
  classical
  refine ⟨?_, ?_⟩
  · have h1 : ‖exV 1‖ * (exD 1 ^ 2 + exD 1) ≤ ∑ x : ZMod 5, ‖exV x‖ * (exD x ^ 2 + exD x) :=
      Finset.single_le_sum (f := fun x : ZMod 5 => ‖exV x‖ * (exD x ^ 2 + exD x))
        (fun x _ => by unfold exD; positivity) (Finset.mem_univ 1)
    have h2 : 0 < ‖exV 1‖ * (exD 1 ^ 2 + exD 1) := by
      rw [exV_one, Complex.norm_real, Real.norm_eq_abs]
      rw [exD_one]
      have := Real.exp_pos (-3 * 2)
      positivity
    exact h2.trans_le h1
  · refine v2_moment_le exU exC exV 0 exSz exD (A₂ := 1) (K₀ := 2) (κ := 3) (κ₀ := 1) (c₀ := 0)
      (by norm_num) le_rfl (by norm_num) (fun x => rfl) ?_ ?_ (fun x => by unfold exD; positivity)
      ?_ ?_
    · intro X hX _
      have fA : (Finset.univ.filter fun x : ZMod 5 => x ∈ polyA) = {0} := by
        ext x; simp [polyA]
      have fB : (Finset.univ.filter fun x : ZMod 5 => x ∈ polyB) = {0, 1} := by
        ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and, polyB, Set.mem_insert_iff,
          Set.mem_singleton_iff, Finset.mem_insert, Finset.mem_singleton]
      rcases mem_exU.1 hX with rfl | rfl
      · rw [fA, Finset.sum_singleton]
        rw [exC_of_mem (by simp [polyA]), ncard_polyA]
        simp only [Complex.norm_real, Real.norm_eq_abs]
        rw [abs_of_nonneg (by positivity)]
        norm_num
      · rw [fB, Finset.sum_pair (by decide)]
        rw [exC_of_mem (by simp [polyB]), exC_of_mem (by simp [polyB]), ncard_polyB]
        simp only [Complex.norm_real, Real.norm_eq_abs]
        have : (0 : ℝ) ≤ Real.exp (-3 * 2) / 2 := by positivity
        rw [abs_of_nonneg this]
        linarith
    · intro X _ _; unfold exSz; positivity
    · intro X hX _ x hx
      rcases mem_exU.1 hX with rfl | rfl
      · simp only [polyA, Set.mem_singleton_iff] at hx
        subst hx
        rw [ncard_polyA]; unfold exD; simp
      · simp only [polyB, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rw [ncard_polyB]
        rcases hx with rfl | rfl
        · unfold exD; simp
        · rw [exD_one]; norm_num
    · have hf : exU.filter (fun X => (0 : ZMod 5) ∈ X) = {polyA, polyB} := by
        ext X
        simp only [Finset.mem_filter, mem_exU, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · exact fun h => h.1
        · rintro (rfl | rfl)
          · exact ⟨Or.inl rfl, by simp [polyA]⟩
          · exact ⟨Or.inr rfl, by simp [polyB]⟩
      rw [hf, Finset.sum_pair polyA_ne_polyB, ncard_polyA, ncard_polyB]
      have a1 : Real.exp (-1 * 1) ≤ 1 := Real.exp_le_one_iff.2 (by norm_num)
      have a2 : Real.exp (-1 * 2) ≤ 1 := Real.exp_le_one_iff.2 (by norm_num)
      linarith

end Example

end Balaban.LargeField.RegionalSourceTerm
