/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.IrrelTorusXidomGeometry
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Numerical scale comparison for the anisotropic datum
-/

@[expose] public section

namespace Balaban.SmallField

/-- With `τ = c s`, `ζ = H e` and `σ = 16 c H s`, the four numerical bounds required
by the anisotropic data constructor follow from `e ≤ ε`. -/
theorem source_to_aniso_numeric {c H s e ε : ℝ}
    (hc : 1 ≤ c) (hH : 1 ≤ H) (hs : 0 ≤ s) (he : 0 ≤ e) (hee : e ≤ ε) :
    2 * (c * s) ^ 2 * (H * e) ≤ (16 * c * H * s) ^ 2 * ε ∧
    2 * (c * s) * (H * e) ≤ (16 * c * H * s) * ε ∧
    10 * (c * s) ^ 2 * (H * e) ≤ (16 * c * H * s) ^ 2 * ε ∧
    98 * (c * s) ^ 2 * (H * e) ^ 2 ≤ (16 * c * H * s) ^ 2 * ε ^ 2 := by
  have hH2 : H ≤ H ^ 2 := by nlinarith [sq_nonneg (H - 1)]
  have hε : 0 ≤ ε := he.trans hee
  have he2 : e ^ 2 ≤ ε ^ 2 := pow_le_pow_left₀ he hee 2
  have hcoef2 : 2 * c ^ 2 * H ≤ (16 * c * H) ^ 2 := by
    have hh : 2 * H ≤ 256 * H ^ 2 := by linarith
    have := mul_le_mul_of_nonneg_left hh (sq_nonneg c)
    nlinarith
  have hcoef10 : 10 * c ^ 2 * H ≤ (16 * c * H) ^ 2 := by
    have hh : 10 * H ≤ 256 * H ^ 2 := by linarith
    have := mul_le_mul_of_nonneg_left hh (sq_nonneg c)
    nlinarith
  have hcoef98 : 98 * c ^ 2 * H ^ 2 ≤ (16 * c * H) ^ 2 := by
    nlinarith [mul_nonneg (sq_nonneg c) (sq_nonneg H)]
  have hcoefAdj : 2 * c * H ≤ 16 * c * H := by
    nlinarith [mul_nonneg (zero_le_one.trans hc) (zero_le_one.trans hH)]
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc
      _ = (2 * c ^ 2 * H) * s ^ 2 * e := by ring
      _ ≤ (2 * c ^ 2 * H) * s ^ 2 * ε := by gcongr
      _ ≤ (16 * c * H) ^ 2 * s ^ 2 * ε := by gcongr
      _ = _ := by ring
  · calc
      _ = (2 * c * H) * s * e := by ring
      _ ≤ (2 * c * H) * s * ε := by gcongr
      _ ≤ (16 * c * H) * s * ε := by gcongr
      _ = _ := by ring
  · calc
      _ = (10 * c ^ 2 * H) * s ^ 2 * e := by ring
      _ ≤ (10 * c ^ 2 * H) * s ^ 2 * ε := by gcongr
      _ ≤ (16 * c * H) ^ 2 * s ^ 2 * ε := by gcongr
      _ = _ := by ring
  · calc
      _ = (98 * c ^ 2 * H ^ 2) * s ^ 2 * e ^ 2 := by ring
      _ ≤ (98 * c ^ 2 * H ^ 2) * s ^ 2 * ε ^ 2 := by gcongr
      _ ≤ (16 * c * H) ^ 2 * s ^ 2 * ε ^ 2 := by gcongr
      _ = _ := by ring

open Balaban Balaban.Background Balaban.Multiscale Balaban.Localization Balaban.SmallField.Def6

variable {d L N₁ m₁ k N j : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
  {ν s e ε K₂ : ℝ}
  {p : CTorus d L N₁ m₁ k → Fin N → ℝ} {h : Fin N → ℝ}
  {z h' : CTorus d L N₁ m₁ k → Fin N → ℂ}

/-- The level-lattice anisotropic datum with explicit scale constants. The source witness
is the output of the strict class chart and the sharp square estimate. -/
theorem ScaledPsiC.dataHypAniso_of_levelGS_scaled
    (hL : 2 ≤ L) (hj1 : 1 ≤ j) (hjk : j < k)
    (H : ScaledPsiC
      (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) (ϱ := ϱ) j hjk.le)
      ν (scaledC0 d * s) (xiC1 d * e) j p h z h')
    (y : CTorus d L N₁ m₁ k) (f : Site d → CTorus d L N₁ m₁ k)
    (hf : f = fun x => y + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j x)
    (ψ : Site d → Spin N) (b : Spin N)
    (hψ : ∀ x i, ψ x i = (p (f x) i : ℂ) + z (f x) i)
    (hb : b = (((ν * ((L : ℝ) ^ j) ^ 2 : ℝ) : ℂ) • fun i => (h i : ℂ) + h' (f 0) i))
    (hsharp : ∀ x, ‖∑ i, ((p (f x) i : ℂ) + z (f x) i) *
          ((p (f x) i : ℂ) + z (f x) i) -
        ∑ i, (p (f x) i : ℂ) * (p (f x) i : ℂ)‖ <
          (scaledC0 d * s) ^ 2 * (xiC1 d * e))
    (hν : 0 < ν * ((L : ℝ) ^ j) ^ 2) (hs : 0 < s)
    (hτ1 : scaledC0 d * s ≤ 1)
    (hντ : ν * ((L : ℝ) ^ j) ^ 2 ≤ (scaledC0 d * s) ^ 2)
    (he : 0 < e) (hζ1 : xiC1 d * e ≤ 1 / 200) (hee : e ≤ ε)
    {Dom : Set ((Site d → Spin N) × Spin N)}
    (hchart : (ψ, b) ∈ Dom ∧ ((fun _ => ψ 0), b) ∈ Dom)
    (hK₂ : 0 ≤ K₂)
    (hsec : ∀ x μ μ', ‖ψ (x + Pi.single μ 1 + Pi.single μ' 1) -
      ψ (x + Pi.single μ 1) - ψ (x + Pi.single μ' 1) + ψ x‖ ≤ K₂) :
    DataHypAniso Dom (ν * ((L : ℝ) ^ j) ^ 2)
      (16 * scaledC0 d * xiC1 d * s) ε K₂ ψ b := by
  have hn := source_to_aniso_numeric (one_le_scaledC0 d) (one_le_xiC1 d)
    hs.le he.le hee
  have hτpos : 0 < scaledC0 d * s :=
    mul_pos (lt_of_lt_of_le zero_lt_one (one_le_scaledC0 d)) hs
  have hζpos : 0 < xiC1 d * e :=
    mul_pos (lt_of_lt_of_le zero_lt_one (one_le_xiC1 d)) he
  exact ScaledPsiC.dataHypAniso_of_levelGS hL hj1 hjk H y f hf ψ b hψ hb hsharp
    hν hτpos hτ1 hντ hζpos hζ1 hn.1 hn.2.1 hn.2.2.1 hn.2.2.2
    hchart hK₂ hsec

end Balaban.SmallField
