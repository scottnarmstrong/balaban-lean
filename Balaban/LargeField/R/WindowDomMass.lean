/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.WindowDomXi
public import Balaban.LargeField.Characteristic.RealDomain
public import Balaban.Background.CompositionEstimates
public import Balaban.Background.CompositionSystem
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Changing the mass and the radius of a real datum (blocker 4)

The clauses R1, R2 and the layer constancy of `InPsiTilde G μ δ Ψ h` do not involve the mass `μ`
or the direction `h`; the clauses R3 and R4 do.  For a unit direction `h` the quantity
`|1 - Ψ·h/|Ψ||` is at most `2`, so R3 holds for every mass `μ'` with `2 μ' L^{2k} < δ'^2`, and R4
holds for every mass.

* `abs_one_sub_inner_div_rn_le_two`: the bound `|1 - u·h/|u|| ≤ 2` for `|h| = 1`;
* `inPsiTilde_mass_change`, `inDomainR_mass_change`: a datum in the real domain of radius `δ` and
  mass `μ` is in the real domain of every larger radius `δ'` and every nonnegative mass `μ'` with
  `2 μ' L^{2k} < δ'^2`, with the direction `h` replaced by any unit vector that the datum carries on
  `Ω₁`;
* `inUnionDomainR_mass_change`: the same for `𝒟_ℝ(G; c₁, μ)` at the radius `c₁`;
* `xiCOneReal_of_inDomainR_mass`: the class domain `Ξ^c(G; 1, ε)` of a datum in a real domain of any
  mass, once the mass is small against the radius `ε / (2 K₁ + 2)`.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- **The clause R3 quantity is at most `2` for a unit direction**: `|1 - u·h/|u|| ≤ 2` when
`|h| = 1` (the quotient is bounded by `1` in absolute value, also for `u = 0`). -/
theorem abs_one_sub_inner_div_rn_le_two {u h : Fin N → ℝ} (hh : ∑ i, h i ^ 2 = 1) :
    |1 - (∑ i, u i * h i) / rn u| ≤ 2 := by
  have hCS : (∑ i, u i * h i) ^ 2 ≤ ∑ i, u i ^ 2 := by
    have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => u i) (fun i => h i)
    rwa [hh, mul_one] at this
  have habs : |∑ i, u i * h i| ≤ rn u := Real.abs_le_sqrt hCS
  have hq : |(∑ i, u i * h i) / rn u| ≤ 1 := by
    rcases (rn_nonneg u).eq_or_lt with h0 | hpos
    · rw [← h0]; simp
    · rw [abs_div, abs_of_pos hpos, div_le_one hpos]; exact habs
  obtain ⟨hq1, hq2⟩ := abs_le.1 hq
  exact abs_le.2 ⟨by linarith, by linarith⟩

/-- **A real datum of radius `δ` is a real datum of every larger radius `δ'` and every mass `μ'`
with `2 μ' L^{2k} < δ'^2`**, for any unit direction `h'` (clauses R1, R2 and the layer constancy do
not involve the mass or the direction). -/
theorem inPsiTilde_mass_change {G : GeneratingSet d L N₀ k ϱ} {μ μ' δ δ' : ℝ}
    {Ψ : Torus d (N₀ * L ^ k) → Fin N → ℝ} {h h' : Fin N → ℝ} (hP : InPsiTilde G μ δ Ψ h)
    (hδ : δ ≤ δ') (hh' : ∑ i, h' i ^ 2 = 1) (hμ' : 0 ≤ μ')
    (hmass : 2 * μ' * ((L : ℝ) ^ k) ^ 2 < δ' ^ 2) : InPsiTilde G μ' δ' Ψ h' where
  layerConst := hP.layerConst
  r1 x x' hx := (hP.r1 x x' hx).trans_le hδ
  r2 x hx := (hP.r2 x hx).trans_le hδ
  r3 x _ := by
    have hL1 : (1 : ℝ) ≤ L := by
      have := NeZero.pos L
      exact_mod_cast this
    have hℓ : ((L : ℝ) ^ G.layerIndex x) ^ 2 ≤ ((L : ℝ) ^ k) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (pow_le_pow_right₀ hL1 (layerIndex_le_k G x)) 2
    have h2 := abs_one_sub_inner_div_rn_le_two (u := Ψ x) hh'
    have hnn : 0 ≤ μ' * ((L : ℝ) ^ G.layerIndex x) ^ 2 := by positivity
    calc μ' * ((L : ℝ) ^ G.layerIndex x) ^ 2 * |1 - (∑ i, Ψ x i * h' i) / rn (Ψ x)|
        ≤ μ' * ((L : ℝ) ^ G.layerIndex x) ^ 2 * 2 := mul_le_mul_of_nonneg_left h2 hnn
      _ ≤ μ' * ((L : ℝ) ^ k) ^ 2 * 2 := by
          have := mul_le_mul_of_nonneg_left hℓ hμ'
          linarith
      _ < δ' ^ 2 := by linarith
  r4 := by
    have hpos : 0 < δ' ^ 2 := lt_of_le_of_lt (by positivity) hmass
    simpa [hh'] using hpos

/-- **The datum in a real domain of another mass and radius** (see `inPsiTilde_mass_change`). -/
theorem inDomainR_mass_change {G : GeneratingSet d L N₀ k ϱ} {D : BgData G N} {μ μ' δ δ' : ℝ}
    {hv : Fin N → ℝ} (hD : InDomainR G μ δ D) (hδ : δ ≤ δ') (hhv : ∑ i, hv i ^ 2 = 1)
    (hDh : ∀ x ∈ G.Ω 1, ∀ i, D.h x i = (hv i : ℂ)) (hμ' : 0 ≤ μ')
    (hmass : 2 * μ' * ((L : ℝ) ^ k) ^ 2 < δ' ^ 2) : InDomainR G μ' δ' D := by
  obtain ⟨Ψ, h, hP, hΨ, -⟩ := hD
  exact ⟨Ψ, hv, inPsiTilde_mass_change hP hδ hhv hμ' hmass, hΨ, hDh⟩

/-- **The real domain `𝒟_ℝ(G; c₁, μ)` at another mass**: a datum in `𝒟_ℝ(G; c₁, μ)` is in
`𝒟_ℝ(G; c₁, μ')` for every `μ' ≥ 0` with `2 μ' L^{2k} < c₁^2`, if the datum carries a unit
direction on `Ω₁`. -/
theorem inUnionDomainR_mass_change {G : GeneratingSet d L N₀ k ϱ} {D : BgData G N} {c₁ μ μ' : ℝ}
    {hv : Fin N → ℝ} (hc : 0 < c₁) (hD : InUnionDomainR G c₁ μ D) (hhv : ∑ i, hv i ^ 2 = 1)
    (hDh : ∀ x ∈ G.Ω 1, ∀ i, D.h x i = (hv i : ℂ)) (hμ' : 0 ≤ μ')
    (hmass : 2 * μ' * ((L : ℝ) ^ k) ^ 2 < c₁ ^ 2) : InUnionDomainR G c₁ μ' D := by
  obtain ⟨δ, -, hδc, hD⟩ := hD
  exact ⟨c₁, hc, le_rfl, inDomainR_mass_change hD hδc hhv hDh hμ' hmass⟩

/-- **The class domain of a datum in a real domain of any mass**: a datum in `Ψ̃(G; μ, δ)` with
`δ ≤ δ'`, `δ' ≤ c₁`, `(2 K₁ + 2) δ' ≤ ε`, and a mass `ν ≥ 0` with `2 ν L^{2k} < δ'^2` lies in
`Ξ^c(G; 1, ε)` for the coefficients `a`, the mass `ν` (`BgHyp`) and a unit direction on `Ω₁`. -/
theorem xiCOneReal_of_inDomainR_mass {G : GeneratingSet d L N₀ k ϱ} {D : BgData G N}
    {a : ℕ → ℝ} {μ ν δ δ' ε : ℝ} {hv : Fin N → ℝ} (H : BgHyp d L k ϱ a ν) (hδ0 : 0 < δ)
    (hδ : δ ≤ δ') (hδc : δ' ≤ bgC1 d L N) (hε : (2 * bgK1 d L N + 2) * δ' ≤ ε)
    (hD : InDomainR G μ δ D) (hhv : ∑ i, hv i ^ 2 = 1)
    (hDh : ∀ x ∈ G.Ω 1, ∀ i, D.h x i = (hv i : ℂ)) (hν : 0 ≤ ν)
    (hmass : 2 * ν * ((L : ℝ) ^ k) ^ 2 < δ' ^ 2) : XiCOneReal G a ν ε D :=
  xiCOneReal_of_inDomainR H (hδ0.trans_le hδ) hδc hε
    (inDomainR_mass_change hD hδ hhv hDh hν hmass)

end Balaban.LargeField
