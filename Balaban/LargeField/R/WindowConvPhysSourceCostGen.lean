/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.WindowConvPhysSourceAlg
public import Balaban.LargeField.R.WindowConvPhysSourceBudget
public import Balaban.LargeField.R.CoeffResponseBudget
public import Balaban.LargeField.R.ActionConvWindow
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The cost of a conversion step from the reads, the response and the cube budgets

The assembly of P7CONV (38)–(40) on a region with a cube decomposition, independently of the
chain: the unprimed energies of the background `φ⁰` from its pointwise reads and the cube
budgets, the primed energies of `w = φ¹ - φ⁰` from its sup bounds, then
`actionRegionC_step_le`.
-/

@[expose] public section

namespace Balaban.LargeField.ActionConv

open Balaban.Multiscale Balaban.Background Finset

variable {d L N₀ K N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ K ϱ}

/-- **The unprimed energies of the background `φ⁰`** (P7CONV (38), first row): from the pointwise
reads `4 ε²` (block, bond) and `12 ε² ℓ⁻²` (mass) and the cube budgets. -/
theorem unprimed_budgets (X : Region G) (Dc : StepDecomp X) (a₁ : ℕ → ℝ) (ν₁ β₁ ε κb κg : ℝ)
    (Dat : BgData G N) (φ : G.Ω 1 × Fin N → ℂ) (hβ : 0 ≤ β₁)
    (hcb : ∀ c, β₁ * ∑ x ∈ (Dc.cube c).sites, ‖levelCoeff G a₁ x‖ ≤ κb * Dc.wt c)
    (hcg : ∀ c, β₁ * ∑ x ∈ (Dc.cube c).sites, ((G.spacing x) ^ 2)⁻¹ ≤ κg * Dc.wt c)
    (hrB : ∀ x ∈ X.sites, ∑ j, ‖Dat.Ψ x j - blockAvg G φ x j‖ ^ 2 ≤ 4 * ε ^ 2)
    (hrGf : ∀ x ∈ X.sites, ∀ μ : Fin d, G.spacing x ^ 2 * ∑ j,
      ‖barField G Dat.Ψ φ (x + Pi.single μ 1) j - barField G Dat.Ψ φ x j‖ ^ 2 ≤ 4 * ε ^ 2)
    (hrGb : ∀ x ∈ X.sites, ∀ μ : Fin d, G.spacing x ^ 2 * ∑ j,
      ‖barField G Dat.Ψ φ (x - Pi.single μ 1) j - barField G Dat.Ψ φ x j‖ ^ 2 ≤ 4 * ε ^ 2)
    (hrM : ∀ x ∈ X.sites, |ν₁| * ∑ j, ‖svec G φ x j - Dat.h x j‖ ^ 2 ≤
      12 * ε ^ 2 * ((G.spacing x) ^ 2)⁻¹) :
    β₁ * ∑ x ∈ X.sites, ‖levelCoeff G a₁ x‖ * ∑ j, ‖Dat.Ψ x j - blockAvg G φ x j‖ ^ 2 ≤
        (4 * ε ^ 2) * (κb * Dc.total) ∧
    β₁ * ∑ z : Torus d (N₀ * L ^ K) × Fin d, X.starWeight z.1 z.2 * ∑ j,
        ‖barField G Dat.Ψ φ (z.1 + Pi.single z.2 1) j - barField G Dat.Ψ φ z.1 j‖ ^ 2 ≤
      d * ((4 * ε ^ 2) * (κg * Dc.total)) ∧
    β₁ * ∑ x ∈ X.sites, |ν₁| * ∑ j, ‖svec G φ x j - Dat.h x j‖ ^ 2 ≤
      (12 * ε ^ 2) * (κg * Dc.total) := by
  have h4 : 0 ≤ 4 * ε ^ 2 := by positivity
  refine ⟨?_, ?_, ?_⟩
  · exact Region.siteEnergy_le Dc (fun x => ‖levelCoeff G a₁ x‖)
      (fun x j => Dat.Ψ x j - blockAvg G φ x j) hβ h4 (fun x => norm_nonneg _) hrB hcb
  · exact Region.bondEnergy_le Dc (barField G Dat.Ψ φ) hβ h4 hrGf hrGb hcg
  · exact Region.massRead_energy_le Dc
      (fun x => |ν₁| * ∑ j, ‖svec G φ x j - Dat.h x j‖ ^ 2) hβ (by positivity) hrM hcg

/-- **The primed energies of the response `w`** (P7CONV (38), second row): from the weight-one
sup bounds `V` of `w` and the cube budgets. -/
theorem primed_budgets (X : Region G) (Dc : StepDecomp X) (a₁ : ℕ → ℝ) (ν₁ β₁ A' V Cb Cg Cm : ℝ)
    (w : G.Ω 1 × Fin N → ℂ) (hβ : 0 ≤ β₁)
    (hcb : ∀ c, β₁ * ∑ x ∈ (Dc.cube c).sites, ‖levelCoeff G a₁ x‖ ≤ Cb * (A' * Dc.wt c))
    (hcg : ∀ c, β₁ * ∑ x ∈ (Dc.cube c).sites, ((G.spacing x) ^ 2)⁻¹ ≤ Cg * (A' * Dc.wt c))
    (hcm : ∀ c, β₁ * ∑ _x ∈ (Dc.cube c).sites, |ν₁| ≤ Cm * (A' * Dc.wt c))
    (hval : ∀ (x : G.Ω 1) (j : Fin N), 1 * ‖w (x, j)‖ ≤ V)
    (hfwd : ∀ x ∈ G.Ω 1, ∀ (μ : Fin d) (j : Fin N),
      1 * (G.spacing x * ‖svec G w (x + Pi.single μ 1) j - svec G w x j‖) ≤ V)
    (hbwd : ∀ x ∈ G.Ω 1, ∀ (μ : Fin d) (j : Fin N),
      1 * (G.spacing x * ‖svec G w (x - Pi.single μ 1) j - svec G w x j‖) ≤ V) :
    β₁ * ∑ x ∈ X.sites, ‖levelCoeff G a₁ x‖ * ∑ j, ‖blockAvg G w x j‖ ^ 2 ≤
        (N * Cb) * (A' * Dc.total * V ^ 2) ∧
    β₁ * ∑ z : Torus d (N₀ * L ^ K) × Fin d, X.starWeight z.1 z.2 * ∑ j,
        ‖svec G w (z.1 + Pi.single z.2 1) j - svec G w z.1 j‖ ^ 2 ≤
      (d * (N * Cg)) * (A' * Dc.total * V ^ 2) ∧
    β₁ * ∑ x ∈ X.sites, |ν₁| * ∑ j, ‖svec G w x j‖ ^ 2 ≤
      (N * Cm) * (A' * Dc.total * V ^ 2) :=
  ⟨Region.blockEnergy_response_le Dc a₁ w hβ hval hcb,
    Region.bondEnergy_response_le Dc w hβ hfwd hbwd hcg,
    Region.massEnergy_response_le Dc w hβ hval hcm⟩

/-- The scalar bookkeeping of the final estimate. -/
theorem step_arith {Aa ρ S1 S2 S3 Ksrc : ℝ} (hAa : 0 ≤ Aa) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1 / 2)
    (hS2 : 0 ≤ S2) (hK : S1 + S2 / 2 + S3 ≤ Ksrc) :
    Aa * (ρ * S1 + ρ ^ 2 / 2 * S2) + ρ * (Aa * S3) ≤ Aa * ρ * Ksrc := by
  have hρρ : ρ ^ 2 ≤ ρ := by nlinarith
  have e1 : Aa * (ρ * S1 + ρ ^ 2 / 2 * S2) + ρ * (Aa * S3) =
      Aa * ρ * (S1 + S3) + (Aa * S2 / 2) * ρ ^ 2 := by ring
  have e2 : (Aa * S2 / 2) * ρ ^ 2 ≤ (Aa * S2 / 2) * ρ :=
    mul_le_mul_of_nonneg_left hρρ (by positivity)
  have e4 : Aa * ρ * (S1 + S2 / 2 + S3) ≤ Aa * ρ * Ksrc :=
    mul_le_mul_of_nonneg_left hK (by positivity)
  nlinarith [e1, e2, e4]

/-- The primed budget in the scaled form: `V ≤ ρ ε V₁` turns `C (A' T V²)` into
`(C V₁²)(A' ε² T ρ²)`. -/
theorem primed_scale {C A' T Vb ρ ε V1 : ℝ} (hC : 0 ≤ C) (hP : 0 ≤ A' * T) (hVb0 : 0 ≤ Vb)
    (hVb : Vb ≤ ρ * ε * V1) :
    C * (A' * T * Vb ^ 2) ≤ (C * V1 ^ 2) * ((A' * ε ^ 2 * T) * ρ ^ 2) := by
  have hVsq : Vb ^ 2 ≤ (ρ * ε * V1) ^ 2 := pow_le_pow_left₀ hVb0 hVb 2
  calc C * (A' * T * Vb ^ 2) ≤ C * (A' * T * (ρ * ε * V1) ^ 2) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hVsq hP) hC
    _ = _ := by ring

/-- **The six budgets of a conversion step in the scaled form.** -/
theorem step_budgets (X : Region G) (Dc : StepDecomp X) {a₁ : ℕ → ℝ} {ν₁ β₁ ρ A' ε Ka cν e V1 Vb : ℝ}
    (Dat : BgData G N) (φ0 φ1 : G.Ω 1 × Fin N → ℂ) (hβ : 0 < β₁)
    (hA' : 0 ≤ A') (hKa0 : 0 ≤ Ka) (he0 : 0 ≤ e)
    (hcb : ∀ c, β₁ * ∑ x ∈ (Dc.cube c).sites, ‖levelCoeff G a₁ x‖ ≤ (Ka * A') * Dc.wt c)
    (hcg : ∀ c, β₁ * ∑ x ∈ (Dc.cube c).sites, ((G.spacing x) ^ 2)⁻¹ ≤ (e * A') * Dc.wt c)
    (hcm : ∀ c, β₁ * ∑ _x ∈ (Dc.cube c).sites, |ν₁| ≤ (e * cν ^ 2) * (A' * Dc.wt c))
    (hrB : ∀ x ∈ X.sites, ∑ j, ‖Dat.Ψ x j - blockAvg G φ0 x j‖ ^ 2 ≤ 4 * ε ^ 2)
    (hrGf : ∀ x ∈ X.sites, ∀ μ : Fin d, G.spacing x ^ 2 * ∑ j,
      ‖barField G Dat.Ψ φ0 (x + Pi.single μ 1) j - barField G Dat.Ψ φ0 x j‖ ^ 2 ≤ 4 * ε ^ 2)
    (hrGb : ∀ x ∈ X.sites, ∀ μ : Fin d, G.spacing x ^ 2 * ∑ j,
      ‖barField G Dat.Ψ φ0 (x - Pi.single μ 1) j - barField G Dat.Ψ φ0 x j‖ ^ 2 ≤ 4 * ε ^ 2)
    (hrM : ∀ x ∈ X.sites, |ν₁| * ∑ j, ‖svec G φ0 x j - Dat.h x j‖ ^ 2 ≤
      12 * ε ^ 2 * ((G.spacing x) ^ 2)⁻¹)
    (hVb0 : 0 ≤ Vb) (hVb : Vb ≤ ρ * ε * V1)
    (hval : ∀ (x : G.Ω 1) (j : Fin N), 1 * ‖(φ1 - φ0) (x, j)‖ ≤ Vb)
    (hfwd : ∀ x ∈ G.Ω 1, ∀ (μ : Fin d) (j : Fin N),
      1 * (G.spacing x * ‖svec G (φ1 - φ0) (x + Pi.single μ 1) j - svec G (φ1 - φ0) x j‖) ≤ Vb)
    (hbwd : ∀ x ∈ G.Ω 1, ∀ (μ : Fin d) (j : Fin N),
      1 * (G.spacing x * ‖svec G (φ1 - φ0) (x - Pi.single μ 1) j - svec G (φ1 - φ0) x j‖) ≤ Vb) :
    β₁ * ∑ x ∈ X.sites, ‖levelCoeff G a₁ x‖ * ∑ j, ‖Dat.Ψ x j - blockAvg G φ0 x j‖ ^ 2 ≤
      (4 * Ka) * (A' * ε ^ 2 * Dc.total) ∧
    β₁ * ∑ x ∈ X.sites, ‖levelCoeff G a₁ x‖ * ∑ j, ‖blockAvg G (φ1 - φ0) x j‖ ^ 2 ≤
      (N * Ka * V1 ^ 2) * ((A' * ε ^ 2 * Dc.total) * ρ ^ 2) ∧
    β₁ * ∑ z : Torus d (N₀ * L ^ K) × Fin d, X.starWeight z.1 z.2 * ∑ j,
      ‖barField G Dat.Ψ φ0 (z.1 + Pi.single z.2 1) j - barField G Dat.Ψ φ0 z.1 j‖ ^ 2 ≤
      (4 * d * e) * (A' * ε ^ 2 * Dc.total) ∧
    β₁ * ∑ z : Torus d (N₀ * L ^ K) × Fin d, X.starWeight z.1 z.2 * ∑ j,
      ‖svec G (φ1 - φ0) (z.1 + Pi.single z.2 1) j - svec G (φ1 - φ0) z.1 j‖ ^ 2 ≤
      (d * (N * e) * V1 ^ 2) * ((A' * ε ^ 2 * Dc.total) * ρ ^ 2) ∧
    β₁ * ∑ x ∈ X.sites, |ν₁| * ∑ j, ‖svec G φ0 x j - Dat.h x j‖ ^ 2 ≤
      (12 * e) * (A' * ε ^ 2 * Dc.total) ∧
    β₁ * ∑ x ∈ X.sites, |ν₁| * ∑ j, ‖svec G (φ1 - φ0) x j‖ ^ 2 ≤
      (N * (e * cν ^ 2) * V1 ^ 2) * ((A' * ε ^ 2 * Dc.total) * ρ ^ 2) := by
  have hT0 : 0 ≤ Dc.total := Dc.total_nonneg
  have hP : 0 ≤ A' * Dc.total := mul_nonneg hA' hT0
  obtain ⟨u1, u2, u3⟩ := unprimed_budgets X Dc a₁ ν₁ β₁ ε (Ka * A') (e * A') Dat φ0 hβ.le hcb hcg
    hrB hrGf hrGb hrM
  obtain ⟨p1, p2, p3⟩ := primed_budgets X Dc a₁ ν₁ β₁ A' Vb Ka e (e * cν ^ 2) (φ1 - φ0) hβ.le
    (fun c => by rw [← mul_assoc]; exact hcb c) (fun c => by rw [← mul_assoc]; exact hcg c) hcm
    hval hfwd hbwd
  refine ⟨u1.trans (le_of_eq (by ring)), p1.trans (primed_scale (by positivity) hP hVb0 hVb),
    u2.trans (le_of_eq (by ring)), p2.trans (primed_scale (by positivity) hP hVb0 hVb),
    u3.trans (le_of_eq (by ring)), p3.trans (primed_scale (by positivity) hP hVb0 hVb)⟩

/-- **The cost of a conversion step from the reads, the response and the cube budgets**
(P7CONV (38)–(40)). -/
theorem convCost_le_of_budgets (X : Region G) (Dc : StepDecomp X)
    {a₀ a₁ : ℕ → ℝ} {ν₀ ν₁ β₀ β₁ ρ A' ε Ka cν e V1 Vb Ksrc : ℝ}
    (Dat : BgData G N) (φ0 φ1 : G.Ω 1 × Fin N → ℂ)
    (hcoef : ∀ ℓ, β₁ * a₁ ℓ = β₀ * a₀ ℓ) (hβ : 0 < β₁) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1 / 2)
    (hb : |β₁ - β₀| ≤ 2 * ρ * β₁) (hc : |β₁ * ν₁ - β₀ * ν₀| ≤ 2 * ρ * (β₁ * |ν₁|))
    (hA' : 0 ≤ A') (hKa0 : 0 ≤ Ka) (he0 : 0 ≤ e)
    (hcb : ∀ c, β₁ * ∑ x ∈ (Dc.cube c).sites, ‖levelCoeff G a₁ x‖ ≤ (Ka * A') * Dc.wt c)
    (hcg : ∀ c, β₁ * ∑ x ∈ (Dc.cube c).sites, ((G.spacing x) ^ 2)⁻¹ ≤ (e * A') * Dc.wt c)
    (hcm : ∀ c, β₁ * ∑ _x ∈ (Dc.cube c).sites, |ν₁| ≤ (e * cν ^ 2) * (A' * Dc.wt c))
    (hrB : ∀ x ∈ X.sites, ∑ j, ‖Dat.Ψ x j - blockAvg G φ0 x j‖ ^ 2 ≤ 4 * ε ^ 2)
    (hrGf : ∀ x ∈ X.sites, ∀ μ : Fin d, G.spacing x ^ 2 * ∑ j,
      ‖barField G Dat.Ψ φ0 (x + Pi.single μ 1) j - barField G Dat.Ψ φ0 x j‖ ^ 2 ≤ 4 * ε ^ 2)
    (hrGb : ∀ x ∈ X.sites, ∀ μ : Fin d, G.spacing x ^ 2 * ∑ j,
      ‖barField G Dat.Ψ φ0 (x - Pi.single μ 1) j - barField G Dat.Ψ φ0 x j‖ ^ 2 ≤ 4 * ε ^ 2)
    (hrM : ∀ x ∈ X.sites, |ν₁| * ∑ j, ‖svec G φ0 x j - Dat.h x j‖ ^ 2 ≤
      12 * ε ^ 2 * ((G.spacing x) ^ 2)⁻¹)
    (hVb0 : 0 ≤ Vb) (hVb : Vb ≤ ρ * ε * V1)
    (hval : ∀ (x : G.Ω 1) (j : Fin N), 1 * ‖(φ1 - φ0) (x, j)‖ ≤ Vb)
    (hfwd : ∀ x ∈ G.Ω 1, ∀ (μ : Fin d) (j : Fin N),
      1 * (G.spacing x * ‖svec G (φ1 - φ0) (x + Pi.single μ 1) j - svec G (φ1 - φ0) x j‖) ≤ Vb)
    (hbwd : ∀ x ∈ G.Ω 1, ∀ (μ : Fin d) (j : Fin N),
      1 * (G.spacing x * ‖svec G (φ1 - φ0) (x - Pi.single μ 1) j - svec G (φ1 - φ0) x j‖) ≤ Vb)
    (hK : Real.sqrt ((4 * Ka) * (N * Ka * V1 ^ 2)) +
      Real.sqrt ((4 * d * e) * (d * (N * e) * V1 ^ 2)) +
      Real.sqrt ((12 * e) * (N * (e * cν ^ 2) * V1 ^ 2)) +
      (N * Ka * V1 ^ 2 + d * (N * e) * V1 ^ 2 + N * (e * cν ^ 2) * V1 ^ 2) / 2 +
      4 * d * e + 12 * e ≤ Ksrc) :
    ‖(β₁ : ℂ) * actionRegionC X a₁ ν₁ Dat φ1 - (β₀ : ℂ) * actionRegionC X a₀ ν₀ Dat φ0‖ ≤
      Ksrc * (A' * ε ^ 2) * ρ * Dc.total := by
  obtain ⟨hB, hB', hG, hG', hM, hM'⟩ := step_budgets X Dc (ρ := ρ) (A' := A') (ε := ε) (Ka := Ka)
    (cν := cν) (e := e) (V1 := V1) (Vb := Vb) Dat φ0 φ1 hβ hA' hKa0 he0 hcb hcg hcm hrB hrGf
    hrGb hrM hVb0 hVb hval hfwd hbwd
  have hAa0 : 0 ≤ A' * ε ^ 2 * Dc.total := by
    have := Dc.total_nonneg; positivity
  have key := actionRegionC_step_le X (ν₀ := ν₀) (σ := ρ) hcoef hβ.le hρ0 hAa0 hρ0
    (by positivity : 0 ≤ 4 * Ka) (by positivity : 0 ≤ 4 * d * e) (by positivity : 0 ≤ 12 * e)
    hb hc Dat φ0 (φ1 - φ0) hB hB' hG hG' hM hM'
  rw [add_sub_cancel] at key
  refine key.trans ?_
  have hS2 : 0 ≤ (N * Ka * V1 ^ 2 + d * (N * e) * V1 ^ 2 + N * (e * cν ^ 2) * V1 ^ 2) := by
    positivity
  have := step_arith (S1 := Real.sqrt ((4 * Ka) * (N * Ka * V1 ^ 2)) +
      Real.sqrt ((4 * d * e) * (d * (N * e) * V1 ^ 2)) +
      Real.sqrt ((12 * e) * (N * (e * cν ^ 2) * V1 ^ 2)))
    (S3 := 4 * d * e + 12 * e) hAa0 hρ0 hρ1 hS2 (Ksrc := Ksrc) (by linarith [hK])
  calc _ ≤ _ := this
    _ = _ := by ring

end Balaban.LargeField.ActionConv
