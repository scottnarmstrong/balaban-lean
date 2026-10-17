/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.StepIdentity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# The recursion of the vacuum constant `E_k` of the small-field class (package `VacuumEnergy`)

The class exponent carries `- E_k |T^{(k)}_1|` (`StepClass.Ek`, `StepSetting.nU = |T^{(k)}_1|`).
One step multiplies the density by the normalisation constants of `t_k`, the Jacobian and `ν_{p₁}`,
which is `exp (-(E'''_k - E_k) |T^{(k)}_1|)` (`const_identity`).  The output of the step has the
form of the class at scale `k + 1`, with exponent `- E_{k+1} |T^{(k+1)}_1|`,
`|T^{(k+1)}_1| = nBlocks = L^{-d} |T^{(k)}_1|`, after the vacuum value `e₀` of the new localized
terms (the sum over the torus of `ℰ^{(k+1)}` at the zero datum) has been absorbed (P4 (4.21)):
`E_{k+1} |T^{(k+1)}_1| = E'''_k |T^{(k)}_1| - e₀`.

* `eppp_sub_Ek`: the per-site form of `E'''_k - E_k`.
* `vacuumEnergy_succ_of_absorb`: the recursion `E_{k+1} = L^d (E_k + c_k) - e₀ / nBlocks`, with `c_k`
  the explicit step constant.
* `abs_vacuumEnergy_succ_le`: the one-step bound it gives.

The factor is `L^d`, not `L^{-d}`: per block of the coarser lattice the constant grows, so a
bound `|E_k| ≤ C' λ_k + C'` is a statement about the cancellation between `L^d E'''_k` and the vacuum
value of the new localized terms, not a geometric sum (`notes/phase1/LF4R-PLAN.md` §7).
-/

@[expose] public section

namespace Balaban.Fluctuation

namespace StepSetting

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) (C : StepClass d L N₁ m₁ k N ϱ)

include S C in
/-- **The per-site step constant**: `E'''_k - E_k = -½ N L^{-d} log (c/2π) + ½ N log β_k
- e(N, p₁) - ½ N log 2π`. -/
theorem eppp_sub_Ek :
    S.Eppp C - C.Ek =
      -((N : ℝ) / 2 * ((L : ℝ) ^ d)⁻¹ * Real.log (S.cKernel / (2 * Real.pi))) +
        (N : ℝ) / 2 * Real.log S.betaU - fluctE N S.p₁ -
        (N : ℝ) / 2 * Real.log (2 * Real.pi) := by
  unfold Eppp Epp Ep
  ring

include S C in
/-- **The recursion of the vacuum constant.**  If `E_{k+1}` is the constant of the next class,
defined by absorbing the vacuum value `e₀` of the new localized terms,
`E_{k+1} |T^{(k+1)}_1| = E'''_k |T^{(k)}_1| - e₀`, then
`E_{k+1} = L^d (E_k + c_k) - e₀ / |T^{(k+1)}_1|`, `c_k = E'''_k - E_k` of `eppp_sub_Ek`. -/
theorem vacuumEnergy_succ_of_absorb (hnB : 0 < S.nBlocks) {Ek' e₀ : ℝ}
    (hE' : Ek' * S.nBlocks = S.Eppp C * S.nU - e₀) :
    Ek' = (L : ℝ) ^ d * (C.Ek +
      (-((N : ℝ) / 2 * ((L : ℝ) ^ d)⁻¹ * Real.log (S.cKernel / (2 * Real.pi))) +
        (N : ℝ) / 2 * Real.log S.betaU - fluctE N S.p₁ -
        (N : ℝ) / 2 * Real.log (2 * Real.pi))) - e₀ / S.nBlocks := by
  have hL : (0 : ℝ) < (L : ℝ) ^ d := by
    have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  have hU : S.nU = S.nBlocks * (L : ℝ) ^ d := by
    unfold nBlocks; field_simp
  have hc := S.eppp_sub_Ek C
  have hEppp : S.Eppp C = C.Ek + (-((N : ℝ) / 2 * ((L : ℝ) ^ d)⁻¹ *
      Real.log (S.cKernel / (2 * Real.pi))) + (N : ℝ) / 2 * Real.log S.betaU - fluctE N S.p₁ -
      (N : ℝ) / 2 * Real.log (2 * Real.pi)) := by linarith
  rw [← hEppp]
  have hne : S.nBlocks ≠ 0 := hnB.ne'
  rw [hU] at hE'
  field_simp
  linarith [hE']

include S C in
/-- **One-step bound.**  Under the absorption relation of `vacuumEnergy_succ_of_absorb`,
`|E_{k+1}| ≤ L^d (|E_k| + |c_k|) + |e₀| / |T^{(k+1)}_1|`, `|c_k|` bounded by the four logarithms. -/
theorem abs_vacuumEnergy_succ_le (hnB : 0 < S.nBlocks) {Ek' e₀ : ℝ}
    (hE' : Ek' * S.nBlocks = S.Eppp C * S.nU - e₀) :
    |Ek'| ≤ (L : ℝ) ^ d * (|C.Ek| +
      ((N : ℝ) / 2 * ((L : ℝ) ^ d)⁻¹ * |Real.log (S.cKernel / (2 * Real.pi))| +
        (N : ℝ) / 2 * |Real.log S.betaU| + |fluctE N S.p₁| +
        (N : ℝ) / 2 * |Real.log (2 * Real.pi)|)) + |e₀| / S.nBlocks := by
  have hL : (0 : ℝ) < (L : ℝ) ^ d := by
    have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  rw [S.vacuumEnergy_succ_of_absorb C hnB hE']
  have hN : (0 : ℝ) ≤ (N : ℝ) / 2 := by positivity
  have hLi : (0 : ℝ) ≤ ((L : ℝ) ^ d)⁻¹ := by positivity
  have hP : (0 : ℝ) ≤ (N : ℝ) / 2 * ((L : ℝ) ^ d)⁻¹ := mul_nonneg hN hLi
  have ha := mul_le_mul_of_nonneg_left (le_abs_self (Real.log (S.cKernel / (2 * Real.pi)))) hP
  have ha' := mul_le_mul_of_nonneg_left (neg_abs_le (Real.log (S.cKernel / (2 * Real.pi)))) hP
  have hb := mul_le_mul_of_nonneg_left (le_abs_self (Real.log S.betaU)) hN
  have hb' := mul_le_mul_of_nonneg_left (neg_abs_le (Real.log S.betaU)) hN
  have hc := mul_le_mul_of_nonneg_left (le_abs_self (Real.log (2 * Real.pi))) hN
  have hc' := mul_le_mul_of_nonneg_left (neg_abs_le (Real.log (2 * Real.pi))) hN
  have hf := le_abs_self (fluctE N S.p₁)
  have hf' := neg_abs_le (fluctE N S.p₁)
  have hk := le_abs_self C.Ek
  have hk' := neg_abs_le C.Ek
  have he := le_abs_self e₀
  have he' := neg_abs_le e₀
  have hdiv : |e₀ / S.nBlocks| = |e₀| / S.nBlocks := by rw [abs_div, abs_of_pos hnB]
  have hdiv1 : e₀ / S.nBlocks ≤ |e₀| / S.nBlocks := div_le_div_of_nonneg_right he hnB.le
  have hdiv2 : -(|e₀| / S.nBlocks) ≤ e₀ / S.nBlocks := by
    rw [← neg_div]; exact div_le_div_of_nonneg_right he' hnB.le
  rw [abs_le]
  constructor <;> nlinarith [mul_le_mul_of_nonneg_left (show _ ≤ _ from hk) hL.le,
    mul_le_mul_of_nonneg_left (show _ ≤ _ from hk') hL.le]

end StepSetting

end Balaban.Fluctuation
