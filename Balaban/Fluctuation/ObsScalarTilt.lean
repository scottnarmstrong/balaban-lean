/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.Thm31b
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The scalar tilt of the observable marks

For the record `ObsMarks` (`Thm31b`) it suffices to take
`A(t, σ) = σ · A_phys(t)` on the disc `|σ| < R_g` (and `t` in the open set `𝒰`), and `0` elsewhere,
where `A_phys(t)` is a label activity, holomorphic in `t` on `𝒰 ⊇ [0,1]` and bounded by `ε_base`.
The bound constant of `A` is `R_g · ε_base`.

* `LabelAct.rscale`: multiplication of a label activity by `c` with `‖c‖ ≤ R`, prefactor `R ε`.
* `obsScalarTilt`: the literal piecewise definition, and the four fields `holt`, `holσ`, `zero`,
  `hW` of `ObsMarks` in their exact form (`obsScalarTilt_holt`, …).
* The arithmetic for `R_g = b^s / (C_R w³)`, `w = (log b)^p`, `b = β 3^k`: `R_g > 1`,
  `R_g ε_base ≤ Θ`, and the amplitude `(1/R_g)(w/√b) = C_R w⁴ b^{-1/2-s}` against the class amplitude.
* `obsTilt_of_physAct`: the conditional assembly from a physical complex-`t` activity family.

NOT constructed here: the physical complex-`t` activity family (`OPEN-OBS-PHYS-ACT`), the kernel
and remainder marks, and the `ObsMarks` inhabitant.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Polymer MeasureTheory Metric Filter Topology

section Tilt

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ j : ℕ} {Ω : Set (CTorus d L N₁ m₁ K)}
variable {Lb : Type*} [Fintype Lb] {Lab : CubeLabels m₀ j Ω Lb} {εH κH κ0 Kc : ℝ}

/-- A label activity multiplied by a complex constant `c` with `‖c‖ ≤ R`: a label activity with
prefactor `R * εH` and the same other bounds. -/
noncomputable def LabelAct.rscale
    {Ωb : CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω → Type*}
    [∀ b, MeasurableSpace (Ωb b)] (A : LabelAct Lab Ωb εH κH κ0 Kc) (R : ℝ) (c : ℂ)
    (hc : ‖c‖ ≤ R) : LabelAct Lab Ωb (R * εH) κH κ0 Kc where
  H y Φ := c * A.H y Φ
  meas y := (A.meas y).const_mul c
  dep y Φ Φ' h := by simp only [A.dep y Φ Φ' h]
  bound y Φ := by
    calc ‖c * A.H y Φ‖ = ‖c‖ * ‖A.H y Φ‖ := norm_mul _ _
      _ ≤ R * (εH * Real.exp (-κH * Lab.dl y)) :=
          mul_le_mul hc (A.bound y Φ) (norm_nonneg _) ((norm_nonneg _).trans hc)
      _ = R * εH * Real.exp (-κH * Lab.dl y) := by ring
  entropy := A.entropy

open Classical in
/-- The scalar multiplier of the tilt: `σ` if `t ∈ 𝒰` and `‖σ‖ < Rg`, and `0` otherwise. -/
noncomputable def obsTiltFactor (Rg : ℝ) (𝒰 : Set ℂ) (t σ : ℂ) : ℂ :=
  if t ∈ 𝒰 ∧ ‖σ‖ < Rg then σ else 0

theorem norm_obsTiltFactor_le {Rg : ℝ} (hR : 0 ≤ Rg) (𝒰 : Set ℂ) (t σ : ℂ) :
    ‖obsTiltFactor Rg 𝒰 t σ‖ ≤ Rg := by
  unfold obsTiltFactor
  split_ifs with h
  · exact h.2.le
  · simpa using hR

/-- **The scalar tilt.**  `A t σ = σ • A_phys t` when `t ∈ 𝒰` and `‖σ‖ < Rg`, and `0` otherwise
(the same labels, entropy and dependence; prefactor `Rg * εH`). -/
noncomputable def obsScalarTilt
    {Ωb : CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω → Type*}
    [∀ b, MeasurableSpace (Ωb b)] (Rg : ℝ) (hR : 0 ≤ Rg) (𝒰 : Set ℂ)
    (Aphys : ℂ → LabelAct Lab Ωb εH κH κ0 Kc) (t σ : ℂ) :
    LabelAct Lab Ωb (Rg * εH) κH κ0 Kc :=
  (Aphys t).rscale Rg (obsTiltFactor Rg 𝒰 t σ) (norm_obsTiltFactor_le hR 𝒰 t σ)

variable {Ωb : CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω → Type*}
  [∀ b, MeasurableSpace (Ωb b)] {Rg : ℝ} {hR : 0 ≤ Rg} {𝒰 : Set ℂ}
  {Aphys : ℂ → LabelAct Lab Ωb εH κH κ0 Kc}

theorem obsScalarTilt_H (t σ : ℂ) (y : Lb) (Φ : ∀ b, Ωb b) :
    (obsScalarTilt Rg hR 𝒰 Aphys t σ).H y Φ = obsTiltFactor Rg 𝒰 t σ * (Aphys t).H y Φ := rfl

theorem obsTiltFactor_of_mem {t σ : ℂ} (ht : t ∈ 𝒰) (hσ : ‖σ‖ < Rg) :
    obsTiltFactor Rg 𝒰 t σ = σ := by
  simp [obsTiltFactor, ht, hσ]

/-- `ObsMarks.holt`: holomorphy in `t` on `𝒰` at `σ = 1` (needs `1 < Rg`). -/
theorem obsScalarTilt_holt (hRg : 1 < Rg)
    (hol : ∀ y Φ, DifferentiableOn ℂ (fun t => (Aphys t).H y Φ) 𝒰) :
    ∀ y Φ, DifferentiableOn ℂ (fun t => (obsScalarTilt Rg hR 𝒰 Aphys t 1).H y Φ) 𝒰 := by
  intro y Φ
  refine (hol y Φ).congr fun t ht => ?_
  rw [obsScalarTilt_H, obsTiltFactor_of_mem ht (by simpa using hRg), one_mul]

/-- `ObsMarks.holσ`: holomorphy in `σ` on the open disc, at every `t ∈ 𝒰`. -/
theorem obsScalarTilt_holσ {t : ℂ} (ht : t ∈ 𝒰) :
    ∀ y Φ, DifferentiableOn ℂ (fun σ => (obsScalarTilt Rg hR 𝒰 Aphys t σ).H y Φ)
      (ball (0 : ℂ) Rg) := by
  intro y Φ
  have : DifferentiableOn ℂ (fun σ : ℂ => σ * (Aphys t).H y Φ) (ball (0 : ℂ) Rg) :=
    (differentiableOn_id.mul_const _)
  refine this.congr fun σ hσ => ?_
  rw [obsScalarTilt_H, obsTiltFactor_of_mem ht (by simpa using hσ)]

/-- `ObsMarks.zero`: the tilt vanishes at `σ = 0`. -/
theorem obsScalarTilt_zero (t : ℂ) (y : Lb) (Φ : ∀ b, Ωb b) :
    (obsScalarTilt Rg hR 𝒰 Aphys t 0).H y Φ = 0 := by
  rw [obsScalarTilt_H]
  unfold obsTiltFactor
  split_ifs <;> simp

/-- `ObsMarks.hW`: at `σ = 1` and `t ∈ 𝒰` the tilt is the physical activity, so the physical
identity `W s = ∑ y, A_phys.H y (restr x)` transfers (needs `1 < Rg`). -/
theorem obsScalarTilt_hW {X : Type*} [MeasurableSpace X] {ν : Measure X}
    (restr : X → ∀ b, Ωb b) (W : ℝ → X → ℂ) (hRg : 1 < Rg)
    (hseg : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → (s : ℂ) ∈ 𝒰)
    (hWphys : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ᵐ x ∂ν,
      W s x = ∑ y, (Aphys (s : ℂ)).H y (restr x)) :
    ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ᵐ x ∂ν,
      W s x = ∑ y, (obsScalarTilt Rg hR 𝒰 Aphys (s : ℂ) 1).H y (restr x) := by
  intro s hs
  filter_upwards [hWphys s hs] with x hx
  rw [hx]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [obsScalarTilt_H, obsTiltFactor_of_mem (hseg s hs) (by simpa using hRg), one_mul]

end Tilt

section Arith

/-- The scale factor `w = (log b)^p`. -/
noncomputable def obsW (p b : ℝ) : ℝ := Real.log b ^ p

/-- The disc radius `R_g = b^s / (C_R w³)`. -/
noncomputable def obsRg (CR s p b : ℝ) : ℝ := b ^ s / (CR * obsW p b ^ 3)

/-- Powers dominate logarithms, as an explicit threshold. -/
theorem exists_log_rpow_le (q c σ : ℝ) (hσ : 0 < σ) (hc : 0 < c) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ b : ℝ, B ≤ b → Real.log b ^ q ≤ c * b ^ σ := by
  have h := ((isLittleO_log_rpow_rpow_atTop q hσ).bound hc)
  obtain ⟨B, hB⟩ := eventually_atTop.1 h
  refine ⟨max B 1, le_max_right _ _, fun b hb => ?_⟩
  have hb1 : 1 ≤ b := le_trans (le_max_right _ _) hb
  have := hB b (le_trans (le_max_left _ _) hb)
  have h0 : 0 ≤ Real.log b := Real.log_nonneg hb1
  have h1 : 0 ≤ b ^ σ := Real.rpow_nonneg (by linarith) _
  rwa [Real.norm_of_nonneg (Real.rpow_nonneg h0 _), Real.norm_of_nonneg h1] at this

theorem obsW_cube (p b : ℝ) (hb : 1 ≤ b) : obsW p b ^ 3 = Real.log b ^ (3 * p) := by
  unfold obsW
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Real.log_nonneg hb)]
  norm_num [mul_comm]

theorem obsW_pos (p b : ℝ) (hb : 1 < b) : 0 < obsW p b :=
  Real.rpow_pos_of_pos (Real.log_pos hb) _

/-- (a) `R_g > 1` beyond an explicit-in-form threshold. -/
theorem exists_one_lt_obsRg {CR s p : ℝ} (hCR : 0 < CR) (hs : 0 < s) :
    ∃ b₁ : ℝ, 1 < b₁ ∧ ∀ b : ℝ, b₁ ≤ b → 1 < obsRg CR s p b := by
  obtain ⟨B, hB1, hB⟩ := exists_log_rpow_le (3 * p) (1 / (2 * CR)) s hs (by positivity)
  refine ⟨B + 1, by linarith, fun b hb => ?_⟩
  have hb1 : 1 < b := by linarith
  have hw := obsW_pos p b hb1
  have hbs : 0 < b ^ s := Real.rpow_pos_of_pos (by linarith) _
  have hle := hB b (by linarith)
  rw [← obsW_cube p b hb1.le] at hle
  unfold obsRg
  rw [lt_div_iff₀ (by positivity)]
  have : CR * obsW p b ^ 3 ≤ b ^ s / 2 := by
    calc CR * obsW p b ^ 3 ≤ CR * (1 / (2 * CR) * b ^ s) := by gcongr
      _ = b ^ s / 2 := by field_simp
  linarith

/-- (b) `R_g ε_base ≤ (C_U / C_R) b^{s-1/2}` when `0 ≤ ε_base ≤ C_U w³/√b`. -/
theorem obsRg_mul_le {CR CU s p b ε : ℝ} (hCR : 0 < CR) (hb : 1 < b)
    (hε : ε ≤ CU * obsW p b ^ 3 / Real.sqrt b) :
    obsRg CR s p b * ε ≤ CU / CR * b ^ (s - 1 / 2) := by
  have hw := obsW_pos p b hb
  have hb0 : 0 < b := by linarith
  have hsq : Real.sqrt b = b ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow b
  have hsqp : 0 < Real.sqrt b := Real.sqrt_pos.2 hb0
  have hR0 : 0 ≤ obsRg CR s p b := by
    unfold obsRg; have := Real.rpow_pos_of_pos hb0 s; positivity
  calc obsRg CR s p b * ε ≤ obsRg CR s p b * (CU * obsW p b ^ 3 / Real.sqrt b) :=
        mul_le_mul_of_nonneg_left hε hR0
    _ = CU / CR * (b ^ s / b ^ (1 / 2 : ℝ)) := by
        unfold obsRg; rw [hsq]; field_simp
    _ = CU / CR * b ^ (s - 1 / 2) := by rw [Real.rpow_sub hb0]

/-- (c) `R_g ε_base ≤ Θ` beyond an explicit-in-form threshold (`s < 1/2`). -/
theorem exists_obsRg_mul_le {CR CU s p Θ : ℝ} (hCR : 0 < CR) (hs : s < 1 / 2)
    (hCU : 0 ≤ CU) (hΘ : 0 < Θ) :
    ∃ b₂ : ℝ, 1 < b₂ ∧ ∀ b ε : ℝ, b₂ ≤ b → ε ≤ CU * obsW p b ^ 3 / Real.sqrt b →
      obsRg CR s p b * ε ≤ Θ := by
  have ht : Tendsto (fun b : ℝ => b ^ (s - 1 / 2)) atTop (nhds 0) :=
    by simpa [neg_sub] using tendsto_rpow_neg_atTop (by linarith : 0 < 1 / 2 - s)
  have hCU1 : 0 < CU + 1 := by linarith
  have hpos : 0 < Θ * CR / (CU + 1) := by positivity
  obtain ⟨B, hB⟩ := eventually_atTop.1 ((ht.eventually (gt_mem_nhds hpos)))
  refine ⟨max B 2, by linarith [le_max_right B 2], fun b ε hb hε => ?_⟩
  have hb1 : 1 < b := by linarith [le_max_right B 2]
  refine (obsRg_mul_le hCR hb1 hε).trans ?_
  have := hB b (le_trans (le_max_left _ _) hb)
  have hbp : 0 ≤ b ^ (s - 1 / 2) := Real.rpow_nonneg (by linarith) _
  calc CU / CR * b ^ (s - 1 / 2) ≤ (CU + 1) / CR * b ^ (s - 1 / 2) := by gcongr; linarith
    _ ≤ (CU + 1) / CR * (Θ * CR / (CU + 1)) := by gcongr
    _ = Θ := by field_simp

/-- (d) the first-order amplitude: `(1/R_g)(w/√b) = C_R w⁴ b^{-1/2-s}`. -/
theorem obsRg_inv_amp {CR s p b : ℝ} (hCR : 0 < CR) (hb : 1 < b) :
    (1 / obsRg CR s p b) * (obsW p b / Real.sqrt b) =
      CR * obsW p b ^ 4 * b ^ (-(1 / 2) - s) := by
  have hw := obsW_pos p b hb
  have hb0 : 0 < b := by linarith
  have h1 : Real.sqrt b = b ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow b
  have h2 : b ^ (-(1 / 2 : ℝ) - s) = (b ^ (1 / 2 : ℝ))⁻¹ / b ^ s := by
    rw [Real.rpow_sub hb0, Real.rpow_neg hb0.le]
  have h3 : 0 < b ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hb0 _
  have h4 : 0 < b ^ s := Real.rpow_pos_of_pos hb0 _
  rw [h2, h1]
  unfold obsRg
  field_simp

/-- (d, comparison) For `0 ≤ δ < s` there is `β₂` with
`C w⁴ b^{-1/2-s} ≤ β^{-1/4} 3^{-(k+1)(1/2+δ)}` for all `β ≥ β₂`, uniformly in `k`, `b = β 3^k`. -/
theorem obsAmp_le_class {C s δ p : ℝ} (hC : 0 ≤ C) (hδ0 : 0 ≤ δ) (hδ : δ < s) :
    ∃ β₂ : ℝ, 1 < β₂ ∧ ∀ (β : ℝ) (k : ℕ), β₂ ≤ β →
      C * obsW p (β * 3 ^ k) ^ 4 * (β * 3 ^ k) ^ (-(1 / 2 : ℝ) - s) ≤
        β ^ (-(1 / 4 : ℝ)) * (3 : ℝ) ^ (-((k + 1 : ℝ) * (1 / 2 + δ))) := by
  set σ : ℝ := (s - δ) / 2 with hσ
  have hσ0 : 0 < σ := by rw [hσ]; linarith
  set e : ℝ := σ - s - 1 / 4 with he
  have he0 : 0 < -e := by rw [he, hσ]; linarith
  obtain ⟨B, hB1, hB⟩ := exists_log_rpow_le (4 * p) 1 σ hσ0 one_pos
  have ht : Tendsto (fun β : ℝ => β ^ e) atTop (nhds 0) := by
    simpa using tendsto_rpow_neg_atTop he0
  have hK : 0 < (C * (3 : ℝ) ^ (1 / 2 + δ) + 1)⁻¹ := by positivity
  obtain ⟨B2, hB2⟩ := eventually_atTop.1 (ht.eventually (gt_mem_nhds hK))
  refine ⟨max (max B B2) 2, by linarith [le_max_right (max B B2) 2], fun β k hβ => ?_⟩
  have hβB : B ≤ β := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hβ
  have hβB2 : B2 ≤ β := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hβ
  have hβ2 : 2 ≤ β := le_trans (le_max_right _ _) hβ
  have hβ0 : 0 < β := by linarith
  have h3k : (1 : ℝ) ≤ 3 ^ k := one_le_pow₀ (by norm_num)
  have h3k0 : (0 : ℝ) < 3 ^ k := by linarith
  have hb1 : 1 < β * 3 ^ k := by nlinarith
  have hb0 : 0 < β * 3 ^ k := by linarith
  have hbB : B ≤ β * 3 ^ k := by nlinarith
  -- the logarithm bound
  have hw4 : obsW p (β * 3 ^ k) ^ 4 ≤ (β * 3 ^ k) ^ σ := by
    have h := hB _ hbB
    have : obsW p (β * 3 ^ k) ^ 4 = Real.log (β * 3 ^ k) ^ (4 * p) := by
      unfold obsW
      rw [← Real.rpow_natCast, ← Real.rpow_mul (Real.log_nonneg hb1.le)]
      norm_num [mul_comm]
    rw [this]; simpa using h
  have hx : (β * 3 ^ k) ^ (-(1 / 2 : ℝ) - s) * (β * 3 ^ k) ^ σ = (β * 3 ^ k) ^ (σ - 1 / 2 - s) := by
    rw [← Real.rpow_add hb0]; congr 1; ring
  have hsplit : (β * 3 ^ k) ^ (σ - 1 / 2 - s) = β ^ (σ - 1 / 2 - s) * (3 : ℝ) ^ ((k : ℝ) * (σ - 1 / 2 - s)) := by
    rw [Real.mul_rpow hβ0.le h3k0.le, ← Real.rpow_natCast (3 : ℝ) k, ← Real.rpow_mul (by norm_num)]
  have h3le : (3 : ℝ) ^ ((k : ℝ) * (σ - 1 / 2 - s)) ≤ (3 : ℝ) ^ (-((k : ℝ) * (1 / 2 + δ))) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have : σ - 1 / 2 - s ≤ -(1 / 2 + δ) := by rw [hσ]; linarith
    nlinarith
  have hβe : β ^ (σ - 1 / 2 - s) = β ^ e * β ^ (-(1 / 4 : ℝ)) := by
    rw [← Real.rpow_add hβ0]; congr 1; rw [he]; ring
  have hrhs : (3 : ℝ) ^ (-((k + 1 : ℝ) * (1 / 2 + δ))) =
      (3 : ℝ) ^ (-((k : ℝ) * (1 / 2 + δ))) * ((3 : ℝ) ^ (1 / 2 + δ))⁻¹ := by
    rw [← Real.rpow_neg (by norm_num), ← Real.rpow_add (by norm_num)]; congr 1; ring
  have hβe1 : β ^ e < (C * (3 : ℝ) ^ (1 / 2 + δ) + 1)⁻¹ := hB2 β hβB2
  have h3p : 0 < (3 : ℝ) ^ (1 / 2 + δ) := by positivity
  have hE : C * (3 : ℝ) ^ (1 / 2 + δ) * β ^ e ≤ 1 := by
    have hpe : 0 ≤ β ^ e := Real.rpow_nonneg hβ0.le _
    have hCK : 0 < C * (3 : ℝ) ^ (1 / 2 + δ) + 1 := by positivity
    have h6 := mul_lt_mul_of_pos_left hβe1 hCK
    rw [mul_inv_cancel₀ hCK.ne'] at h6
    nlinarith
  have h3pos : 0 < (3 : ℝ) ^ (-((k : ℝ) * (1 / 2 + δ))) := by positivity
  have hbp : 0 ≤ (β * 3 ^ k) ^ (-(1 / 2 : ℝ) - s) := Real.rpow_nonneg hb0.le _
  calc C * obsW p (β * 3 ^ k) ^ 4 * (β * 3 ^ k) ^ (-(1 / 2 : ℝ) - s)
      ≤ C * (β * 3 ^ k) ^ σ * (β * 3 ^ k) ^ (-(1 / 2 : ℝ) - s) := by gcongr
    _ = C * (β ^ e * β ^ (-(1 / 4 : ℝ)) * (3 : ℝ) ^ ((k : ℝ) * (σ - 1 / 2 - s))) := by
        rw [mul_assoc, mul_comm ((β * 3 ^ k) ^ σ), hx, hsplit, hβe]
    _ ≤ C * (β ^ e * β ^ (-(1 / 4 : ℝ)) * (3 : ℝ) ^ (-((k : ℝ) * (1 / 2 + δ)))) := by gcongr
    _ = (C * (3 : ℝ) ^ (1 / 2 + δ) * β ^ e) * (β ^ (-(1 / 4 : ℝ)) *
          (3 : ℝ) ^ (-((k : ℝ) * (1 / 2 + δ))) * ((3 : ℝ) ^ (1 / 2 + δ))⁻¹) := by
        field_simp
    _ ≤ 1 * (β ^ (-(1 / 4 : ℝ)) * (3 : ℝ) ^ (-((k : ℝ) * (1 / 2 + δ))) *
          ((3 : ℝ) ^ (1 / 2 + δ))⁻¹) := by
        gcongr
    _ = _ := by rw [one_mul, hrhs]; ring

end Arith

section Assembly

universe u

open Classical in
/-- **Conditional assembly at every scale.**  Beyond an explicit threshold `b₀` (depending only on
`C_R, C_U, s, p, Θ`), for every physical complex-`t` label activity family with base bound
`ε_base ≤ C_U w³/√b` (this family is `OPEN-OBS-PHYS-ACT`, not constructed here), holomorphic in `t`
on `𝒰 ⊇ [0,1]` and representing `W` on `[0,1]`: `R_g > 1`, `R_g ε_base ≤ Θ`, and the tilt
`A : ℂ → ℂ → LabelAct Lab BS.Ωb (R_g ε_base) κH κ0 Kc` satisfies the four fields `holt`, `holσ`,
`zero`, `hW` of `ObsMarks` (with `Rσ = R_g`). -/
theorem obsTilt_of_physAct {CR CU s p Θ : ℝ} (hCR : 0 < CR) (hCU : 0 ≤ CU) (hs : 0 < s)
    (hs2 : s < 1 / 2) (hΘ : 0 < Θ) :
    ∃ b₀ : ℝ, 1 < b₀ ∧ ∀ b : ℝ, b₀ ≤ b →
      ∀ {d L N₁ m₁ K : ℕ} [NeZero L] [NeZero N₁] {X : Type u} [MeasurableSpace X]
        {ν : Measure X} {m₀ : ℕ} (BS : ProdSplit ν d L N₁ m₁ K m₀) {Lb : Type}
        [Fintype Lb]
        (Lab : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ K Set.univ Lb)
        {εb κH κ0 Kc : ℝ} (Aphys : ℂ → LabelAct Lab BS.Ωb εb κH κ0 Kc) (𝒰 : Set ℂ)
        (W : ℝ → X → ℂ),
        εb ≤ CU * obsW p b ^ 3 / Real.sqrt b →
        (∀ r : ℝ, r ∈ Set.Icc (0 : ℝ) 1 → (r : ℂ) ∈ 𝒰) →
        (∀ y Φ, DifferentiableOn ℂ (fun t => (Aphys t).H y Φ) 𝒰) →
        (∀ r : ℝ, r ∈ Set.Icc (0 : ℝ) 1 → ∀ᵐ x ∂ν,
          W r x = ∑ y, (Aphys (r : ℂ)).H y (BS.restr x)) →
        1 < obsRg CR s p b ∧ obsRg CR s p b * εb ≤ Θ ∧
        ∃ hR : 0 ≤ obsRg CR s p b,
          (∀ y Φ, DifferentiableOn ℂ
            (fun t => (obsScalarTilt (obsRg CR s p b) hR 𝒰 Aphys t 1).H y Φ) 𝒰) ∧
          (∀ r : ℝ, r ∈ Set.Icc (0 : ℝ) 1 → ∀ y Φ, DifferentiableOn ℂ
            (fun σ => (obsScalarTilt (obsRg CR s p b) hR 𝒰 Aphys (r : ℂ) σ).H y Φ)
            (ball (0 : ℂ) (obsRg CR s p b))) ∧
          (∀ r : ℝ, r ∈ Set.Icc (0 : ℝ) 1 → ∀ y Φ,
            (obsScalarTilt (obsRg CR s p b) hR 𝒰 Aphys (r : ℂ) 0).H y Φ = 0) ∧
          (∀ r : ℝ, r ∈ Set.Icc (0 : ℝ) 1 → ∀ᵐ x ∂ν,
            W r x = ∑ y, (obsScalarTilt (obsRg CR s p b) hR 𝒰 Aphys (r : ℂ) 1).H y
              (BS.restr x)) := by
  obtain ⟨b₁, hb₁, h1⟩ := exists_one_lt_obsRg (p := p) hCR hs
  obtain ⟨b₂, hb₂, h2⟩ := exists_obsRg_mul_le (CR := CR) (CU := CU) (s := s) (p := p) hCR hs2 hCU hΘ
  refine ⟨max b₁ b₂, lt_max_of_lt_left hb₁, fun b hb d L N₁ m₁ K _ _ X _ ν m₀ BS Lb _ Lab
    εb κH κ0 Kc Aphys 𝒰 W hε hseg hol hWphys => ?_⟩
  have hR1 : 1 < obsRg CR s p b := h1 b (le_trans (le_max_left _ _) hb)
  have hR0 : 0 ≤ obsRg CR s p b := by linarith
  refine ⟨hR1, h2 b εb (le_trans (le_max_right _ _) hb) hε, hR0, ?_, ?_, ?_, ?_⟩
  · exact obsScalarTilt_holt hR1 hol
  · intro r hr y Φ
    exact obsScalarTilt_holσ (hseg r hr) y Φ
  · intro r _ y Φ
    exact obsScalarTilt_zero _ y Φ
  · exact obsScalarTilt_hW BS.restr W hR1 hseg hWphys

end Assembly

section Instance

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ j : ℕ} {Ω : Set (CTorus d L N₁ m₁ K)}
variable {Lb : Type*} [Fintype Lb] {Lab : CubeLabels m₀ j Ω Lb} {εH κH κ0 Kc : ℝ}

/-- **Non-vacuity.**  For a `t`-independent label activity `A0` (holomorphic in `t` trivially),
`𝒰 = ℂ`, `R_g = 2` and `W s x = ∑ y, A0.H y (restr x)`, the four fields hold; and the tilt at
`σ = 1` is `A0` (so it is nonzero as soon as `A0` is). -/
theorem obsScalarTilt_const_fields
    {Ωb : CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω → Type*}
    [∀ b, MeasurableSpace (Ωb b)] (A0 : LabelAct Lab Ωb εH κH κ0 Kc)
    {X : Type*} [MeasurableSpace X] (ν : Measure X) (restr : X → ∀ b, Ωb b) :
    let A := obsScalarTilt (2 : ℝ) (by norm_num) (Set.univ : Set ℂ) (fun _ : ℂ => A0)
    (∀ y Φ, DifferentiableOn ℂ (fun t => (A t 1).H y Φ) Set.univ) ∧
    (∀ s : ℝ, ∀ y Φ, DifferentiableOn ℂ (fun σ => (A (s : ℂ) σ).H y Φ) (ball (0 : ℂ) 2)) ∧
    (∀ s : ℝ, ∀ y Φ, (A (s : ℂ) 0).H y Φ = 0) ∧
    (∀ s : ℝ, ∀ᵐ x ∂ν, (∑ y, A0.H y (restr x)) = ∑ y, (A (s : ℂ) 1).H y (restr x)) ∧
    (∀ t y Φ, (A t 1).H y Φ = A0.H y Φ) := by
  intro A
  have h1 : ∀ t y Φ, (A t 1).H y Φ = A0.H y Φ := by
    intro t y Φ
    show obsTiltFactor 2 Set.univ t 1 * A0.H y Φ = _
    rw [obsTiltFactor_of_mem (Set.mem_univ t) (by norm_num), one_mul]
  refine ⟨?_, ?_, ?_, ?_, h1⟩
  · intro y Φ
    simp only [h1]
    exact differentiableOn_const _
  · intro s y Φ
    exact obsScalarTilt_holσ (Set.mem_univ _) y Φ
  · intro s y Φ
    exact obsScalarTilt_zero _ y Φ
  · intro s
    exact Filter.Eventually.of_forall fun x => Finset.sum_congr rfl fun y _ => (h1 _ y _).symm

end Instance

end Balaban.Fluctuation
