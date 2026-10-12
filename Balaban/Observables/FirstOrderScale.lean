/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Observables.MarkedRadius
public import Balaban.Observables.LayerConstants
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The first-order step of OBSERVABLES.md §3.5: the scale conversions (B1)-(B3)

`η = L^{-k}` and `ξ_{k+1} = η / L`.  `StepScale` bundles the typing data of a step at large `β`:
`2 ≤ L`, `1 ≤ β`, `0 < η ≤ 1`, `β_k = β L^{k(d-2)} γ_k` with `|log γ_k| ≤ 1/20` (so that
`β η^{-(d-2)} / 2 ≤ β_k ≤ 2 β η^{-(d-2)}`) and the polynomial `p₁(β_k) ≤ C_p β_k^{ρ₂}`
((B3), from `(log β_k)^{p₁} ≤ C β_k^{ρ₂}`).  `StepScale.nonempty` is the inhabitation witness.

* `StepScale.betak_inv_sqrt_le` (B1): `β_k^{-1/2} ≤ √2 β^{-1/2} η^{(d-2)/2}`;
* `StepScale.p1_pow_le` (B3): `p₁^s ≤ (2 C_p)^s β^{sρ₂} η^{-s(d-2)ρ₂}`.
-/

@[expose] public section

namespace Balaban.Observables

open Real

theorem inv_rpow_le {a b c s : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hs : 0 ≤ s)
    (h : a ≤ c * b) : b ^ (-s) ≤ c ^ s * a ^ (-s) := by
  have h1 : (c * b) ^ (-s) ≤ a ^ (-s) :=
    Real.rpow_le_rpow_of_nonpos ha h (by linarith)
  rw [Real.mul_rpow hc.le hb.le, Real.rpow_neg hc.le] at h1
  have hcs : 0 < c ^ s := Real.rpow_pos_of_pos hc s
  calc b ^ (-s) = c ^ s * ((c ^ s)⁻¹ * b ^ (-s)) := by field_simp
    _ ≤ c ^ s * a ^ (-s) := mul_le_mul_of_nonneg_left h1 hcs.le

/-- `β^x ξ^b ≤ β^y ξ^c` for `β ≥ 1`, `0 < ξ ≤ 1`, `x ≤ y`, `c ≤ b`. -/
theorem rpow_mul_rpow_le {β ξ x y b c : ℝ} (hβ : 1 ≤ β) (hξ0 : 0 < ξ) (hξ1 : ξ ≤ 1)
    (hxy : x ≤ y) (hcb : c ≤ b) : β ^ x * ξ ^ b ≤ β ^ y * ξ ^ c := by
  have h1 : β ^ x ≤ β ^ y := Real.rpow_le_rpow_of_exponent_le hβ hxy
  have h2 : ξ ^ b ≤ ξ ^ c := Real.rpow_le_rpow_of_exponent_ge hξ0 hξ1 hcb
  exact mul_le_mul h1 h2 (Real.rpow_nonneg hξ0.le _) (Real.rpow_nonneg (by linarith) _)

/-- **The typing data of a small-field step at large `β`** (OBSERVABLES §3.5, (B1)-(B3)),
`D = d - 2`. -/
structure StepScale (D ρ₂ : ℝ) where
  /-- the block ratio `L` -/
  L : ℝ
  /-- the coupling `β` -/
  β : ℝ
  /-- `η = L^{-k}` -/
  η : ℝ
  /-- `β_k` -/
  βk : ℝ
  /-- the polynomial `p₁(β_k)` of the characteristic function `χ_fl` -/
  p1 : ℝ
  /-- the constant of `p₁ ≤ C_p β_k^{ρ₂}` -/
  Cp : ℝ
  hD : 1 ≤ D
  hL : 2 ≤ L
  hβ : 1 ≤ β
  hη0 : 0 < η
  hη1 : η ≤ 1
  hβk_lo : β ≤ 2 * βk * η ^ D
  hβk_hi : βk ≤ 2 * β * η ^ (-D)
  hp1 : 1 ≤ p1
  hCp : 1 ≤ Cp
  hp1βk : p1 ≤ Cp * βk ^ ρ₂

/-- **Inhabitation of `StepScale`.** -/
theorem StepScale.nonempty (D ρ₂ : ℝ) (hD : 1 ≤ D) : Nonempty (StepScale D ρ₂) :=
  ⟨{ L := 2, β := 1, η := 1, βk := 1, p1 := 1, Cp := 1, hD := hD, hL := le_rfl, hβ := le_rfl,
     hη0 := one_pos, hη1 := le_rfl, hβk_lo := by simp, hβk_hi := by simp,
     hp1 := le_rfl, hCp := le_rfl, hp1βk := by simp }⟩

namespace StepScale

variable {D ρ₂ : ℝ} (S : StepScale D ρ₂)

theorem L_pos : 0 < S.L := by linarith [S.hL]
theorem β_pos : 0 < S.β := by linarith [S.hβ]
theorem ηD_pos : 0 < S.η ^ D := Real.rpow_pos_of_pos S.hη0 D

theorem βk_pos : 0 < S.βk := by
  by_contra hneg
  push Not at hneg
  have h := mul_nonpos_of_nonpos_of_nonneg hneg S.ηD_pos.le
  nlinarith [S.hβk_lo, S.hβ]

/-- The scale `ξ_{k+1} = η / L`. -/
noncomputable def ξ : ℝ := S.η / S.L

theorem ξ_pos : 0 < S.ξ := div_pos S.hη0 S.L_pos

theorem ξ_le_one : S.ξ ≤ 1 := by
  unfold ξ
  rw [div_le_one S.L_pos]
  linarith [S.hη1, S.hL]

/-- **(B1)** `β_k^{-s} ≤ 2^s β^{-s} η^{sD}` for `s ≥ 0` (`s = 1/2` gives `β_k^{-1/2} ≤ √2 β^{-1/2}
η^{D/2}`). -/
theorem betak_neg_pow_le {s : ℝ} (hs : 0 ≤ s) :
    S.βk ^ (-s) ≤ 2 ^ s * S.β ^ (-s) * S.η ^ (D * s) := by
  have h := inv_rpow_le S.β_pos S.βk_pos (by have := S.ηD_pos; positivity : (0 : ℝ) < 2 * S.η ^ D) hs
    (by linarith [S.hβk_lo] : S.β ≤ 2 * S.η ^ D * S.βk)
  rw [Real.mul_rpow (by norm_num) S.ηD_pos.le, ← Real.rpow_mul S.hη0.le] at h
  calc _ ≤ _ := h
    _ = _ := by ring

theorem betak_inv_sqrt_le : S.βk ^ (-(1 / 2 : ℝ)) ≤
    √2 * S.β ^ (-(1 / 2 : ℝ)) * S.η ^ (D / 2) := by
  have := S.betak_neg_pow_le (s := 1 / 2) (by norm_num)
  rw [Real.sqrt_eq_rpow]
  convert this using 3
  ring

/-- **(B3)** `p₁^s ≤ (2 C_p)^s β^{sρ₂} η^{-sDρ₂}` for `s ≥ 0`, `0 ≤ ρ₂ ≤ 1`. -/
theorem p1_pow_le (hρ : 0 ≤ ρ₂) (hρ1 : ρ₂ ≤ 1) {s : ℝ} (hs : 0 ≤ s) :
    S.p1 ^ s ≤ (2 * S.Cp) ^ s * S.β ^ (s * ρ₂) * S.η ^ (-(s * (D * ρ₂))) := by
  have hβk := S.βk_pos
  have hβp := S.β_pos
  have hηp := S.hη0
  have hCp0 : 0 < S.Cp := by linarith [S.hCp]
  have hη : 0 < S.η ^ (-D) := Real.rpow_pos_of_pos hηp _
  have h2 : S.βk ^ ρ₂ ≤ (2 * S.β * S.η ^ (-D)) ^ ρ₂ := Real.rpow_le_rpow hβk.le S.hβk_hi hρ
  have hβ' : 0 < S.β ^ ρ₂ := Real.rpow_pos_of_pos hβp _
  have hη' : 0 < S.η ^ (-(D * ρ₂)) := Real.rpow_pos_of_pos hηp _
  have h2' : (0 : ℝ) < 2 ^ ρ₂ := by positivity
  have e1 : (2 * S.β * S.η ^ (-D)) ^ ρ₂ = 2 ^ ρ₂ * S.β ^ ρ₂ * S.η ^ (-(D * ρ₂)) := by
    rw [Real.mul_rpow (by positivity) hη.le, Real.mul_rpow (by norm_num) hβp.le,
      ← Real.rpow_mul hηp.le]
    ring_nf
  have hT : S.p1 ≤ S.Cp * 2 ^ ρ₂ * S.β ^ ρ₂ * S.η ^ (-(D * ρ₂)) := by
    calc S.p1 ≤ S.Cp * S.βk ^ ρ₂ := S.hp1βk
      _ ≤ S.Cp * (2 * S.β * S.η ^ (-D)) ^ ρ₂ := mul_le_mul_of_nonneg_left h2 hCp0.le
      _ = _ := by rw [e1]; ring
  have h1 := Real.rpow_le_rpow (by linarith [S.hp1]) hT hs
  have h5 : (2 : ℝ) ^ (ρ₂ * s) ≤ 2 ^ s :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith)
  rw [Real.mul_rpow (by positivity) hη'.le, Real.mul_rpow (by positivity) hβ'.le,
    Real.mul_rpow hCp0.le h2'.le, ← Real.rpow_mul hβp.le, ← Real.rpow_mul hηp.le,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)] at h1
  calc S.p1 ^ s ≤ _ := h1
    _ ≤ S.Cp ^ s * 2 ^ s * S.β ^ (ρ₂ * s) * S.η ^ (-(D * ρ₂) * s) := by gcongr
    _ = _ := by
        rw [Real.mul_rpow (by norm_num) hCp0.le]
        have e2 : -(D * ρ₂) * s = -(s * (D * ρ₂)) := by ring
        rw [e2, mul_comm ρ₂ s]; ring

end StepScale

end Balaban.Observables
