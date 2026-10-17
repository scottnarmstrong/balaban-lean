/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.VacuumEnergy
public import Balaban.Fluctuation.VacuumFlow
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# The increment of the vacuum constant in one step (package `VacuumFlow`, step form)

`vacuumEnergy_succ_of_absorb` gives `E_{k+1} = L^d (E_k + (E'''_k - E_k)) - e₀ / |T^{(k+1)}_1|`
(P4 (4.21)), `e₀` the vacuum value of the new localized terms.  This file writes it as
`E_{k+1} = L^d E_k + g_k` with the increment `g_k` computed exactly, and bounds `g_k`.

* `cKernel_eq_betaU_mul`: `c = β_k a₁ L^{d-2}` in the units of `betaU`.
* `step_increment_eq`: `L^d (E'''_k - E_k) = ½ N (L^d - 1) log β_k - ½ N log (a₁ L^{d-2} / 2π)
  - L^d log Z₁(p₁)`: the dependence on `β_k` is exactly `½ N (L^d - 1) log β_k` (the Jacobian
  `L^d · ½ N log β_k` of (2.7) per block, less `½ N log β_k` of the normalization of `t_k`).
* `vacuumEnergy_succ_eq_increment`: `E_{k+1} = L^d E_k + g_k` under the absorption relation.
* `abs_step_increment_le`: `|g_k| ≤ ½ N (L^d - 1) |log β_k| + ½ N |log (a₁ L^{d-2}/2π)|
  + L^d |log Z₁(p₁)| + |e₀| / |T^{(k+1)}_1|`.
* `abs_vacuum_le_of_final_eq_zero_step`: for a sequence obeying `E_{j+1} = L^d E_j + g_j` with
  `|g_j| ≤ ½ N (L^d - 1) λ_j + B` (the form of `abs_step_increment_le` with `λ_j = log β_j`),
  `λ_j ≤ λ_k + (j - k) θ`, and `E_K = 0`: `|E_k| ≤ C' λ_k + C'`,
  `C' = N/2 + B/(L^d - 1) + N θ/(2 (L^d - 1))`.  The leading coefficient `N/2` is that of the
  Gaussian free energy `-½ N log β_k` per site.
-/

@[expose] public section

namespace Balaban.Fluctuation

namespace StepSetting

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) (C : StepClass d L N₁ m₁ k N ϱ)

/-- **The Gaussian coefficient of `t_k` in the units of `β_k`**: `c = β_k · a₁ L^d / L²`. -/
theorem cKernel_eq_betaU_mul :
    S.cKernel = S.betaU * (S.a₁ * (L : ℝ) ^ d / (L : ℝ) ^ 2) := by
  have hL : (L : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne L
  unfold cKernel betaU
  field_simp
  ring

include C in
/-- **The per-block step constant, exactly**: `L^d (E'''_k - E_k) = ½ N (L^d - 1) log β_k
- ½ N log (a₁ L^{d-2} / 2π) - L^d log Z₁(p₁)`, `Z₁(p) = ∫ 1[|ψ| < p] e^{-|ψ|²/2} dψ`. -/
theorem step_increment_eq (ha₁ : 0 < S.a₁) (hβ : 0 < S.β) (hp₁ : 0 < S.p₁) :
    (L : ℝ) ^ d * (S.Eppp C - C.Ek) =
      (N : ℝ) / 2 * ((L : ℝ) ^ d - 1) * Real.log S.betaU -
        (N : ℝ) / 2 * Real.log (S.a₁ * (L : ℝ) ^ d / (L : ℝ) ^ 2 / (2 * Real.pi)) -
        (L : ℝ) ^ d * Real.log (fluctNorm N S.p₁) := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hLd : (0 : ℝ) < (L : ℝ) ^ d := by positivity
  have hB : 0 < S.betaU := by
    unfold betaU
    have : (0 : ℝ) < (L : ℝ) ^ k := by positivity
    positivity
  have hA : 0 < S.a₁ * (L : ℝ) ^ d / (L : ℝ) ^ 2 / (2 * Real.pi) := by positivity
  have hZ := fluctNorm_pos N hp₁
  have he : fluctE N S.p₁ =
      -((N : ℝ) / 2) * Real.log (2 * Real.pi) + Real.log (fluctNorm N S.p₁) := by
    unfold fluctE
    rw [Real.log_mul (by positivity) hZ.ne', Real.log_rpow (by positivity)]
    ring
  have hc : Real.log (S.cKernel / (2 * Real.pi)) =
      Real.log S.betaU + Real.log (S.a₁ * (L : ℝ) ^ d / (L : ℝ) ^ 2 / (2 * Real.pi)) := by
    rw [S.cKernel_eq_betaU_mul, ← Real.log_mul hB.ne' hA.ne']
    congr 1
    ring
  rw [S.eppp_sub_Ek C, hc, he]
  field_simp
  ring

include C in
/-- **The recursion with its increment**: under the absorption relation of
`vacuumEnergy_succ_of_absorb`, `E_{k+1} = L^d E_k + g_k` with
`g_k = ½ N (L^d - 1) log β_k - ½ N log (a₁ L^{d-2}/2π) - L^d log Z₁(p₁) - e₀ / |T^{(k+1)}_1|`;
`g_k` does not depend on `E_k`. -/
theorem vacuumEnergy_succ_eq_increment (hnB : 0 < S.nBlocks) (ha₁ : 0 < S.a₁) (hβ : 0 < S.β)
    (hp₁ : 0 < S.p₁) {Ek' e₀ : ℝ} (hE' : Ek' * S.nBlocks = S.Eppp C * S.nU - e₀) :
    Ek' = (L : ℝ) ^ d * C.Ek +
      ((N : ℝ) / 2 * ((L : ℝ) ^ d - 1) * Real.log S.betaU -
        (N : ℝ) / 2 * Real.log (S.a₁ * (L : ℝ) ^ d / (L : ℝ) ^ 2 / (2 * Real.pi)) -
        (L : ℝ) ^ d * Real.log (fluctNorm N S.p₁) - e₀ / S.nBlocks) := by
  have h := S.vacuumEnergy_succ_of_absorb C hnB hE'
  rw [← S.eppp_sub_Ek C] at h
  rw [h, ← S.step_increment_eq C ha₁ hβ hp₁]
  ring

/-- **The bound of the increment**: `|g_k| ≤ ½ N (L^d - 1) |log β_k| + ½ N |log (a₁ L^{d-2}/2π)|
+ L^d |log Z₁(p₁)| + |e₀| / |T^{(k+1)}_1|`. -/
theorem abs_step_increment_le (hnB : 0 < S.nBlocks) (e₀ : ℝ) :
    |(N : ℝ) / 2 * ((L : ℝ) ^ d - 1) * Real.log S.betaU -
        (N : ℝ) / 2 * Real.log (S.a₁ * (L : ℝ) ^ d / (L : ℝ) ^ 2 / (2 * Real.pi)) -
        (L : ℝ) ^ d * Real.log (fluctNorm N S.p₁) - e₀ / S.nBlocks| ≤
      (N : ℝ) / 2 * ((L : ℝ) ^ d - 1) * |Real.log S.betaU| +
        (N : ℝ) / 2 * |Real.log (S.a₁ * (L : ℝ) ^ d / (L : ℝ) ^ 2 / (2 * Real.pi))| +
        (L : ℝ) ^ d * |Real.log (fluctNorm N S.p₁)| + |e₀| / S.nBlocks := by
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hLd1 : (1 : ℝ) ≤ (L : ℝ) ^ d := one_le_pow₀ hL1
  have hA : 0 ≤ (N : ℝ) / 2 * ((L : ℝ) ^ d - 1) := by
    have : (0 : ℝ) ≤ (L : ℝ) ^ d - 1 := by linarith
    positivity
  have hN : (0 : ℝ) ≤ (N : ℝ) / 2 := by positivity
  have hLd : (0 : ℝ) ≤ (L : ℝ) ^ d := by linarith
  have h1 : |(N : ℝ) / 2 * ((L : ℝ) ^ d - 1) * Real.log S.betaU| =
      (N : ℝ) / 2 * ((L : ℝ) ^ d - 1) * |Real.log S.betaU| := by
    rw [abs_mul, abs_of_nonneg hA]
  have h2 : |(N : ℝ) / 2 * Real.log (S.a₁ * (L : ℝ) ^ d / (L : ℝ) ^ 2 / (2 * Real.pi))| =
      (N : ℝ) / 2 * |Real.log (S.a₁ * (L : ℝ) ^ d / (L : ℝ) ^ 2 / (2 * Real.pi))| := by
    rw [abs_mul, abs_of_nonneg hN]
  have h3 : |(L : ℝ) ^ d * Real.log (fluctNorm N S.p₁)| =
      (L : ℝ) ^ d * |Real.log (fluctNorm N S.p₁)| := by
    rw [abs_mul, abs_of_nonneg hLd]
  have h4 : |e₀ / S.nBlocks| = |e₀| / S.nBlocks := by rw [abs_div, abs_of_pos hnB]
  rw [← h1, ← h2, ← h3, ← h4]
  refine (abs_sub _ _).trans (add_le_add ((abs_sub _ _).trans
    (add_le_add ((abs_sub _ _).trans le_rfl) le_rfl)) le_rfl)

end StepSetting

namespace VacuumFlow

open Finset

/-- **The vacuum bound for the step increments, in the normalization `E_K = 0`**: if
`E_{j+1} = L^d E_j + g_j` on `[0, K)`, `|g_j| ≤ ½ N (L^d - 1) λ_j + B` (`abs_step_increment_le`
with `λ_j = |log β_j|`), `λ_j ≤ λ_k + (j - k) θ` and `E_K = 0`, then for `k ≤ K`
`|E_k| ≤ C' λ_k + C'`, `C' = N/2 + B/(L^d - 1) + N θ/(2 (L^d - 1))`. -/
theorem abs_vacuum_le_of_final_eq_zero_step {d L N K : ℕ} (hLd : 2 ≤ L ^ d)
    {E g lam : ℕ → ℝ} (hE : ∀ j, j < K → E (j + 1) = (L : ℝ) ^ d * E j + g j) (hEK : E K = 0)
    {k : ℕ} (hk : k ≤ K) {B θ : ℝ} (hB : 0 ≤ B) (hθ : 0 ≤ θ) (hl0 : 0 ≤ lam k)
    (hg : ∀ j, k ≤ j → j < K → |g j| ≤ (N : ℝ) / 2 * ((L : ℝ) ^ d - 1) * lam j + B)
    (hl : ∀ j, k ≤ j → j < K → lam j ≤ lam k + ((j - k : ℕ) : ℝ) * θ) :
    |E k| ≤ ((N : ℝ) / 2 + B / ((L : ℝ) ^ d - 1) + (N : ℝ) * θ / (2 * ((L : ℝ) ^ d - 1))) *
        lam k + ((N : ℝ) / 2 + B / ((L : ℝ) ^ d - 1) +
          (N : ℝ) * θ / (2 * ((L : ℝ) ^ d - 1))) := by
  have hq : (1 : ℝ) < (L : ℝ) ^ d := by
    have : (2 : ℝ) ≤ ((L ^ d : ℕ) : ℝ) := by exact_mod_cast hLd
    push_cast at this
    linarith
  have hq1 : (0 : ℝ) < (L : ℝ) ^ d - 1 := by linarith
  have hA : (0 : ℝ) ≤ (N : ℝ) / 2 * ((L : ℝ) ^ d - 1) := by positivity
  have h := abs_vacuum_le_of_final_eq_zero hq hE hEK hk hA hB hθ hl0 hg hl
  have hC : ((N : ℝ) / 2 * ((L : ℝ) ^ d - 1) + B) / ((L : ℝ) ^ d - 1) +
      (N : ℝ) / 2 * ((L : ℝ) ^ d - 1) * θ / ((L : ℝ) ^ d - 1) ^ 2 =
      (N : ℝ) / 2 + B / ((L : ℝ) ^ d - 1) + (N : ℝ) * θ / (2 * ((L : ℝ) ^ d - 1)) := by
    field_simp
  rwa [hC] at h

end VacuumFlow

end Balaban.Fluctuation
