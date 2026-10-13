/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.SourceDirectTermsScale
public import Balaban.Fluctuation.SourceSliceScaled
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The physical amplitude of the step on the slice `η = ρ/β`

One computation, used at every scale and for every tower: the amplitude
`ε_U = β · prop33EpsEtaScaled … (ρ/β)` equals the potential part plus the source part
(`sourceEta_scaled_identity`), the potential part is bounded by `β_k P / r³`
(`beta_mul_potentialAmp_le`), is nonnegative, and `ε_U` is positive and bounded by any bound of
`β_k P / r³ + ρ Q t / r`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Localization Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation

/-- **The physical amplitude facts.**  For a step `S` with weight `a₁ = 1` and scaled coupling
`b = S.betaU`, the amplitude `ε_U = β · prop33EpsEtaScaled d L N m₁ k m₀ 1 BG BG₂ κ t r 0 0 (ρ/β)`
satisfies the identity, the potential bound, the nonnegativity of the potential term, the bound
by every upper bound of `b P / r³ + ρ Q t / r`, and positivity. -/
theorem physAmp_facts {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
    (S : StepSetting d L N₁ m₁ k N ϱ) (hd : 2 ≤ d) (hL3 : 3 ≤ L) (m₀ : ℕ)
    (hmem : compWeight L (1 : ℝ) k ∈ Set.Icc (1 / 2 : ℝ) 2) (ha : S.a₁ = 1)
    {BG BG₂ κ t β b r ρ Q P εU : ℝ} (hβ0 : 0 < β) (hβS : S.β = β) (hbU : S.betaU = b)
    (hQ0 : 0 < Q) (ht0 : 0 < t) (hρ4 : 0 ≤ rho4 d L N BG κ) (hr0 : 0 < r)
    (hρ : 0 < ρ) (hQdef : Q = cK2' d L N (famConst d L BG₂ κ))
    (hPdef : P = 3 * c1 d L * (((L : ℕ) : ℝ) ^ (m₀ + m₁)) ^ d *
      ((L : ℝ) ^ d * (((N : ℝ) / 2) * (2 * (1 + Q) ^ 2 +
        ((d : ℝ) + 1 + rho4 d L N BG κ) * Q ^ 2) * t ^ 2)))
    (hεU : εU = β * prop33EpsEtaScaled d L N m₁ k m₀ 1 BG BG₂ κ t r 0 0 (ρ / β)) :
    εU = β * (3 * c1 d L * (((L : ℕ) : ℝ) ^ (m₀ + m₁)) ^ d *
        ‖energyBdScaled d L N (compWeight L 1) k (Q * t) t (rho4 d L N BG κ)‖ / r ^ 3) +
      ρ * (Q * t) / r ∧
    β * (3 * c1 d L * (((L : ℕ) : ℝ) ^ (m₀ + m₁)) ^ d *
        ‖energyBdScaled d L N (compWeight L 1) k (Q * t) t (rho4 d L N BG κ)‖ / r ^ 3) ≤
      b * (P / r ^ 3) ∧
    0 ≤ β * (3 * c1 d L * (((L : ℕ) : ℝ) ^ (m₀ + m₁)) ^ d *
        ‖energyBdScaled d L N (compWeight L 1) k (Q * t) t (rho4 d L N BG κ)‖ / r ^ 3) ∧
    (∀ R : ℝ, b * (P / r ^ 3) + ρ * (Q * t) / r ≤ R → εU ≤ R) ∧ 0 < εU := by
  have hK0 : 0 < Q * t := mul_pos hQ0 ht0
  have hid := sourceEta_scaled_identity d L N m₁ k m₀ 1 BG BG₂ κ t r ρ β hβ0.ne'
  rw [← hεU, ← hQdef] at hid
  have hpot : β * (3 * c1 d L * (((L : ℕ) : ℝ) ^ (m₀ + m₁)) ^ d *
      ‖energyBdScaled d L N (compWeight L 1) k (Q * t) t (rho4 d L N BG κ)‖ / r ^ 3) ≤
      b * (P / r ^ 3) := by
    have hm : compWeight L S.a₁ k ∈ Set.Icc (1 / 2 : ℝ) 2 := by rw [ha]; exact hmem
    have h := beta_mul_potentialAmp_le (N := N) S hd hL3 hm.2
      (le_trans (by norm_num) hm.1) (by rw [hβS]; exact hβ0.le) hQ0.le ht0.le hρ4 hr0 (m₀ + m₁)
    rw [hbU, ← hPdef, ha, hβS] at h
    exact h
  have hterm0 : 0 ≤ β * (3 * c1 d L * (((L : ℕ) : ℝ) ^ (m₀ + m₁)) ^ d *
      ‖energyBdScaled d L N (compWeight L 1) k (Q * t) t (rho4 d L N BG κ)‖ / r ^ 3) := by
    have h3 : (0 : ℝ) ≤ 3 * c1 d L := by have := one_le_c1 d L; linarith
    positivity
  refine ⟨hid, hpot, hterm0, fun R hR => ?_, ?_⟩
  · rw [hid]; linarith
  · rw [hid]
    have : 0 < ρ * (Q * t) / r := div_pos (mul_pos hρ hK0) hr0
    linarith

end Balaban.Inhabited
