/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.FinalBoxLocRootSum
public import Balaban.Inhabited.StepTowerChainDomNbhd
public import Balaban.Fluctuation.SizeModEntropy
public import Balaban.Fluctuation.SizeModCore

/-!
# The named constraints on the constants of the box localization (A6-3, item (L4))

* `BoxCutConsts d L k M_c v a κ α`: the hypotheses of the cut family `boxCut` of the final Hessian
  at the level `k` (mass `v`, weight `a`, macro side `M_c`, cut radius `κ`) and the constraint
  `BoxCutTies` at the cell rate `α`; `boxCutConsts_exists`.
* `RDomConsts d L N ε δ r`: the radius `r` of the sup ball around a constant unit configuration
  inside the domain `Ξ^c(1, ε)` of the class terms (`xiDom_of_close_unit`: `N r < δ²`,
  `0 < δ ≤ min (c₀, c₁)`, `(2K₁ + 2) δ ≤ ε`); `rDomConsts_exists` (`exists_close_radius`).
* `PolyTies d L κ_R λ κ α`: the decay rate `κ_R` of the polymer terms of the class beats the cell
  weight, the root-cell entropy and the label growth `λ`, `a_ent + 1 + c₁ γ + λ ≤ κ_R`,
  `γ = α + 16^d log(1 + A)`, `A = animalSumConst 16^d q`, `q = e^{α 16^d} e^{-(κ-1)}`
  (`cellGamma`, `cutRatio`); `polyTies_exists`.  `polyBoundConst`: the bound of the local form of
  the polymer terms.
  `PrefixInput` bounds the rate `P6.κ` of the class only from below, so the
  constraint is compatible with it; its witness (`κ_flow = 3^{d+1} L^{2d+1} (κ_F + 1) + a_ent + 2`)
  does not include the term `c₁ γ`.
-/

@[expose] public section

namespace Balaban.Green

/-- **The constants of the cut family** at the level `k`. -/
structure BoxCutConsts (d L k Mc : ℕ) [NeZero L] (v a κ α : ℝ) : Prop where
  hd : 0 < d
  hk : 1 ≤ k
  hv0 : 0 ≤ v
  hv1 : v ≤ 1
  ha1 : 1 / 2 ≤ a
  ha2 : a ≤ 2
  hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v
  hM : 0 < Mc
  ties : BoxCutTies d L Mc κ α

/-- **`BoxCutConsts` is satisfiable** (rule 10): `v = a = 1`, the radius `κ` of
`boxCutTies_exists` and every macro side above its bounds. -/
theorem boxCutConsts_exists (d L k : ℕ) [NeZero L] (hd : 0 < d) (hk : 1 ≤ k) {α : ℝ}
    (hα : 0 ≤ α) :
    ∃ κ : ℝ, ∀ Mc : ℕ, 4 * (pdB d L * Real.exp (pdH d * κ)) ≤ Mc →
      8 * κ * 7 ^ d ≤ pdEps d L * Mc → BoxCutConsts d L k Mc 1 1 κ α := by
  obtain ⟨κ, hκ⟩ := boxCutTies_exists d L hα
  refine ⟨κ, fun Mc h1 h2 => ?_⟩
  have hT := hκ Mc h1 h2
  have hL : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hinv : ((L : ℝ) ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith)
  have hMc : 0 < Mc := by
    have hε := pdEps_pos (d := d) (L := L) hd
    have h7 : (0 : ℝ) < 7 ^ d := by positivity
    have : (0 : ℝ) < pdEps d L * Mc := lt_of_lt_of_le (by nlinarith [hT.1]) h2
    have : (0 : ℝ) < Mc := pos_of_mul_pos_right this hε.le
    exact_mod_cast this
  exact ⟨hd, hk, zero_le_one, le_rfl, by norm_num, by norm_num, by linarith, hMc, hT⟩

/-- **The radius of the domain ball** of the class terms. -/
structure RDomConsts (d L N : ℕ) [NeZero L] (ε δ r : ℝ) : Prop where
  hδ0 : 0 < δ
  hδc0 : δ ≤ Background.bgC0 d L N
  hδc1 : δ ≤ Background.bgC1 d L N
  hr0 : 0 < r
  hr : (N : ℝ) * r < δ ^ 2
  hε : (2 * Background.bgK1 d L N + 2) * δ ≤ ε

/-- **`RDomConsts` is satisfiable** for every `ε > 0` (`exists_close_radius`). -/
theorem rDomConsts_exists {d L N : ℕ} [NeZero L] (hd : 0 < d) (i₀ : Fin N) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ r, RDomConsts d L N ε δ r := by
  obtain ⟨δ, r, h1, h2, h3, h4, h5, h6⟩ := Inhabited.exists_close_radius (d := d) (L := L) hd i₀ hε
  exact ⟨δ, r, h1, h2, h3, h4, h5, h6⟩

/-- The ratio `q = e^{α 16^d} e^{-(κ-1)}` of the count of rooted families of cells. -/
noncomputable def cutRatio (d : ℕ) (κ α : ℝ) : ℝ := Real.exp (α * 16 ^ d) * Real.exp (-(κ - 1))

theorem cutRatio_pos (d : ℕ) (κ α : ℝ) : 0 < cutRatio d κ α :=
  mul_pos (Real.exp_pos _) (Real.exp_pos _)

/-- The exponential rate per cell of the weight of a root: `γ = α + 16^d log(1 + A)`,
`A = animalSumConst 16^d q` (the cell weight and the root cells). -/
noncomputable def cellGamma (d : ℕ) (κ α : ℝ) : ℝ :=
  α + 16 ^ d * Real.log (1 + animalSumConst (16 ^ d) (cutRatio d κ α))

/-- **The decay of the polymer terms beats the cells, the root cells and the labels**:
`a_ent + 1 + c₁ γ + λ ≤ κ_R`, `γ = cellGamma d κ α`, with `λ` the growth rate of the label count
(`∑_{labels of X} amp ≤ F e^{λ d_k(X)}`). -/
def PolyTies (d L : ℕ) (κR lam κ α : ℝ) : Prop :=
  Fluctuation.aEnt d L + 1 + Fluctuation.c1 d L * cellGamma d κ α + lam ≤ κR

/-- **`PolyTies` is satisfiable**: it holds for every rate `κ_R` above a threshold depending on
`d, L, λ, κ, α`. -/
theorem polyTies_exists (d L : ℕ) (lam κ α : ℝ) :
    ∃ κ₀ : ℝ, ∀ κR, κ₀ ≤ κR → PolyTies d L κR lam κ α :=
  ⟨_, fun _ h => h⟩

/-- **The bound of the local form of a family of polymer terms** of the class: the sum `F` of the
amplitudes, the radius ratio `m / (r - m)` of the cut expansion (`m = |c| B_box ρ`, linear in the
radius `ρ` of the Gaussian variable), the cell weight `e^{γ c₁}`, the polymer entropy
`K₀(κ_R - c₁ γ)` and the factor `1 + 7^d 16^d B₃` of the patches. -/
noncomputable def polyBoundConst (d L : ℕ) (F m r κR lam κ α : ℝ) : ℝ :=
  F * (m / (r - m)) * Real.exp (cellGamma d κ α * Fluctuation.c1 d L) *
    Fluctuation.K0 d L (κR - Fluctuation.c1 d L * cellGamma d κ α - lam) *
    (1 + 7 ^ d * 16 ^ d * animalSumConst2 (16 ^ d) (cutRatio d κ α))

end Balaban.Green
