/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.IrrelTorusXidomThreshold
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# A threshold fixed by the scale ratio
-/

@[expose] public section

namespace Balaban.SmallField

/-- The scale ratio fixes a threshold that fits the small-polymer path and whose cubic
large-polymer payment has the anisotropic irrelevance power. -/
theorem threshold_of_scale_ratio {d : ℕ} {A C₀ s σ ε r q KR γ α : ℝ}
    (hA : 0 ≤ A) (hC₀ : 0 < C₀) (hs : 0 < s) (hσs : σ = C₀ * s)
    (hσ1 : σ ≤ 1) (hε : 0 < ε) (hr : 0 < r) (hεr : ε ≤ r)
    (hR : ε / r ≤ KR * s ^ (((d : ℝ) - 2) / 2 - γ))
    (hq : q ≤ r / 2) (hα : 0 ≤ α) (hα1 : α < 1) :
    ∃ ρ Cρ : ℝ, 0 < ρ ∧ 0 ≤ Cρ ∧
      q + A * (σ * ε) / ρ ≤ r ∧
      ρ ^ 3 ≤ Cρ * s ^ ((d : ℝ) + (1 - 2 * γ - α)) := by
  let C : ℝ := 1 + 2 * A
  let u : ℝ := ε / r
  let ρ : ℝ := C * σ * u
  let Cρ : ℝ := C ^ 3 * C₀ ^ (3 - α) * KR ^ 2
  have hC : 0 < C := by dsimp [C]; linarith
  have hσ : 0 < σ := by rw [hσs]; positivity
  have hu : 0 < u := by dsimp [u]; positivity
  have hu1 : u ≤ 1 := by dsimp [u]; exact (div_le_iff₀ hr).2 (by simpa using hεr)
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hσε : 0 ≤ σ * ε := by positivity
  have hpath : A * (σ * ε) / ρ ≤ r / 2 := by
    apply (div_le_iff₀ hρ).2
    have heq : r / 2 * ρ = C / 2 * (σ * ε) := by
      dsimp [ρ, u]
      field_simp
    rw [heq]
    have hCA : 0 ≤ C - 2 * A := by dsimp [C]; norm_num
    nlinarith [mul_nonneg hσε hCA]
  have hbase : q + A * (σ * ε) / ρ ≤ r := by linarith
  have hαlow := cubic_threshold_le_aniso hC.le hσ.le hσ1 hu.le hu1 hα hα1
  have hR2 : u ^ 2 ≤ KR ^ 2 * s ^ (2 * (((d : ℝ) - 2) / 2 - γ)) := by
    have hh := pow_le_pow_left₀ hu.le hR 2
    refine hh.trans (le_of_eq ?_)
    rw [mul_pow]
    congr 1
    rw [← Real.rpow_natCast, ← Real.rpow_mul hs.le]
    norm_num
    ring_nf
  have hσpow : σ ^ (3 - α) = C₀ ^ (3 - α) * s ^ (3 - α) := by
    rw [hσs, Real.mul_rpow hC₀.le hs.le]
  have hexp : s ^ (3 - α) * s ^ (2 * (((d : ℝ) - 2) / 2 - γ)) =
      s ^ ((d : ℝ) + (1 - 2 * γ - α)) := by
    rw [← Real.rpow_add hs]
    congr 1
    ring
  have hpow : ρ ^ 3 ≤ Cρ * s ^ ((d : ℝ) + (1 - 2 * γ - α)) := by
    calc
      ρ ^ 3 ≤ C ^ 3 * σ ^ (3 - α) * u ^ 2 := hαlow
      _ ≤ C ^ 3 * σ ^ (3 - α) *
          (KR ^ 2 * s ^ (2 * (((d : ℝ) - 2) / 2 - γ))) := by gcongr
      _ = Cρ * s ^ ((d : ℝ) + (1 - 2 * γ - α)) := by
        rw [hσpow]
        dsimp [Cρ]
        rw [← hexp]
        ring
  exact ⟨ρ, Cρ, hρ, by dsimp [Cρ]; positivity, hbase, hpow⟩

end Balaban.SmallField
