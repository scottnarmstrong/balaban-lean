/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.Transfer
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The regime bound of the SF/LF interface at the switching scale

`beta_nu_kZero_le`: if the running couplings at the scale `k₀` have the form of (I.2),
`β_{k₀} = β L^{k₀(d-2)} γ`, `ν_{k₀} = ν L^{2k₀} δ` with `|log γ|, |log δ| ≤ 1/20`, then
`β_{k₀} ν_{k₀} ≤ e^{1/10}` (the clause `mass_le` of `SFtoLFInterface` with `C₀ = e^{1/10}`), from the
definition of `k₀`, `β ν L^{k₀ d} ≤ 1`.
-/

@[expose] public section

namespace Balaban.RootFSpine

open Balaban Balaban.LargeField Balaban.Multiscale

theorem beta_nu_kZero_le {d L : ℕ} (hd : 3 ≤ d) (hL : 2 ≤ L) {β ν γ δ : ℝ} (hβ : 4 ≤ β)
    (hν : 0 < ν) (hk : 1 ≤ kZero d L β ν) (hγ0 : 0 < γ) (hγ : |Real.log γ| ≤ 1 / 20)
    (hδ0 : 0 < δ) (hδ : |Real.log δ| ≤ 1 / 20) :
    (β * (L : ℝ) ^ (kZero d L β ν * (d - 2)) * γ) * (ν * (L : ℝ) ^ (2 * kZero d L β ν) * δ) ≤
      Real.exp (1 / 10) := by
  have hg : KZeroGenuine β ν := by
    by_contra hng
    have := kZero_of_not_genuine (d := d) hL hng
    omega
  have hβν : 0 < β * ν := mul_pos (by linarith) hν
  have hspec := kZero_spec (d := d) (L := L) (by omega) hL hβν hg
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have hpow : (L : ℝ) ^ (kZero d L β ν * (d - 2)) * (L : ℝ) ^ (2 * kZero d L β ν) =
      (L : ℝ) ^ (kZero d L β ν * d) := by
    rw [← pow_add]
    congr 1
    have : d - 2 + 2 = d := by omega
    calc kZero d L β ν * (d - 2) + 2 * kZero d L β ν = kZero d L β ν * (d - 2 + 2) := by ring
      _ = kZero d L β ν * d := by rw [this]
  have hγ1 : γ ≤ Real.exp (1 / 20) := by
    calc γ = Real.exp (Real.log γ) := (Real.exp_log hγ0).symm
      _ ≤ Real.exp (1 / 20) := Real.exp_le_exp.2 (abs_le.1 hγ).2
  have hδ1 : δ ≤ Real.exp (1 / 20) := by
    calc δ = Real.exp (Real.log δ) := (Real.exp_log hδ0).symm
      _ ≤ Real.exp (1 / 20) := Real.exp_le_exp.2 (abs_le.1 hδ).2
  have heq : (β * (L : ℝ) ^ (kZero d L β ν * (d - 2)) * γ) *
      (ν * (L : ℝ) ^ (2 * kZero d L β ν) * δ) =
      (β * ν * (L : ℝ) ^ (kZero d L β ν * d)) * (γ * δ) := by
    rw [← hpow]; ring
  rw [heq]
  have hprod : γ * δ ≤ Real.exp (1 / 10) := by
    calc γ * δ ≤ Real.exp (1 / 20) * Real.exp (1 / 20) :=
          mul_le_mul hγ1 hδ1 hδ0.le (Real.exp_pos _).le
      _ = Real.exp (1 / 10) := by rw [← Real.exp_add]; norm_num
  have hpos : 0 ≤ γ * δ := (mul_pos hγ0 hδ0).le
  calc (β * ν * (L : ℝ) ^ (kZero d L β ν * d)) * (γ * δ) ≤ 1 * (γ * δ) :=
        mul_le_mul_of_nonneg_right hspec hpos
    _ ≤ Real.exp (1 / 10) := by linarith

end Balaban.RootFSpine
