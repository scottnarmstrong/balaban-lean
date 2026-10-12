/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Observables.ImprovedFirst
public import Balaban.Observables.ImprovedConst

/-!
# Lemma 3.4, first bound: the constant part on the constant tube

`improved_first_of_const` (W111) leaves the constant part `|M(c, h) - M(v, v)| ≤ b_c` as a
hypothesis.  Here it is discharged by the Lipschitz bound in `(ψ, b)` of `ImprovedConst.lean`
(`M_const_diff_le`, the Cauchy estimate on constant configurations) when `c = Ψ(y)`, `h` and `v` lie in
the constant tube around a coordinate vector `e_{i₀}` (radius `ρ/2`, landed `LiftCtx`):

* `improved_first_of_tube` (complete backgrounds, any `ν_bg`): `b_c = 4 B_X Δ / ρ` with
  `Δ ≥ max(|c - v|, ν_bg L^{2j} |h - v|)` coordinatewise (the `b`-form);
* `improved_first_massFree` (`β_k ν_k ≤ 1`, the `ν`-free regime): no condition on `h`, `b_c = 4 B_X Δ / ρ`
  with `Δ ≥ |c - v|`.

Not covered: the gain `Δ/ρ` is the Lipschitz gain on the tube of radius `ρ ≍ ε_j²`; the reduction of an
arbitrary datum to the tube (rotation to a coordinate vector, the sphere/`ν_j` smallness
`O(ν_j + ||ψ_j|²-1|)`) is not derived; see the ledger row.
-/

@[expose] public section

namespace Balaban.Observables

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
  Balaban.SmallField.Def6 Metric Finset

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

section Tube

variable {P : Consts} {Q : ObsConsts} {β ν a : ℕ → ℝ} {Tm : Terms d L N₁ m₁ k N ϱ}
  {Ot : ObsTerms d L N₁ m₁ k N}
  {Gker : ℕ → CTorus d L N₁ m₁ k → CTorus d L N₁ m₁ k → Fld d L N₁ m₁ k N →
    Fld d L N₁ m₁ k N → Matrix (Fin N) (Fin N) ℂ}
  {ρd : (CTorus d L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) → (CTorus d L N₁ m₁ k → Fin N → ℝ) → ℝ}
  {Ek : ℝ} {j : ℕ} {ρ : ℝ}

/-- **The first bound of Lemma 3.4, constant part from the `b`-form Lipschitz bound.**
As `improved_first_of_const`, with `hconst` replaced by the tube premises: `c = Ψ₀(y) + Ψ''(y)`,
`h = h₀ + h'` and the real unit vector `v` lie in the tube of `e_{i₀}`
(`|c_i - δ_{i i₀}|, |v_i - δ_{i i₀}| ≤ ρ/2`, `m |h_i - δ_{i i₀}|, m |v_i - δ_{i i₀}| ≤ ρ/2`,
`m = ν_bg L^{2j}`), and `|c_i - v_i| ≤ Δ`, `m |h_i - v_i| ≤ Δ`.  Then the constant part is at most
`4 B_X Δ / ρ`, `B_X = β^{-1/2+ρ₁} L^{-jρ₀} e^{-κ d_j(X)}`. -/
theorem improved_first_of_tube (hO : IsObs P Q β ν a Tm Ot Gker)
    (ctx : LiftCtx P β ν a Tm ρd Ek j ρ) (hN : L ^ P.m₀ ∣ N₁)
    {X : Set (CTorus d L N₁ m₁ k)} (hX : IsPolyDom P.m₀ j X) {x : CTorus d L N₁ m₁ k} (hx : x ∈ X)
    {y : CTorus d L N₁ m₁ k} (hy : y ∈ X)
    (hlayer : ∀ z ∈ X, (Tm.gs j X).layerIndex z = j)
    {Ψ₀ : CTorus d L N₁ m₁ k → Fin N → ℝ} {h₀ : Fin N → ℝ}
    {Ψ'' : CTorus d L N₁ m₁ k → Fin N → ℂ} {h' : Fin N → ℂ} {δ ε δ₀ : ℝ}
    (hP : InPsiTildeC (Tm.gs j X) (bgMass L k (β k) (ν k)) δ ε Ψ₀ h₀ Ψ'' (fun _ => h'))
    (hβ0 : 0 < β 0) (hδ : 0 < δ) (hδε : δ ≤ ε) (hε : ε ≤ δ₀) (hc0 : δ₀ ≤ bgC0 d L N)
    (hc1 : δ₀ ≤ bgC1 d L N)
    (hεj : δ₀ + (2 * bgK1 d L N + 1) * δ₀ ≤ P.eps d L j)
    (hsmall : 128 * (3 ^ d * ((L : ℝ) ^ (P.m₀ + m₁) * (4 * d * L) + 1)) * δ ≤ δ₀)
    (i₀ : Fin N) {v : Fin N → ℝ} {Δ : ℝ} (hΔ : 0 < Δ)
    (hc : ∀ i, ‖((Ψ₀ y i : ℂ) + Ψ'' y i) - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ ρ / 2)
    (hv : ∀ i, ‖(v i : ℂ) - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ ρ / 2)
    (hvw : ∀ i, bgMass L k (β k) (ν k) * ((L : ℝ) ^ j) ^ 2 *
      ‖(v i : ℂ) - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ ρ / 2)
    (hh : ∀ i, bgMass L k (β k) (ν k) * ((L : ℝ) ^ j) ^ 2 *
      ‖((h₀ i : ℂ) + h' i) - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ ρ / 2)
    (hdc : ∀ i, ‖((Ψ₀ y i : ℂ) + Ψ'' y i) - (v i : ℂ)‖ ≤ Δ)
    (hdh : ∀ i, bgMass L k (β k) (ν k) * ((L : ℝ) ^ j) ^ 2 *
      ‖((h₀ i : ℂ) + h' i) - (v i : ℂ)‖ ≤ Δ) :
    vn (Ot.M j x X (fun z i => (Ψ₀ z i : ℂ) + Ψ'' z i) (constFld (fun i => (h₀ i : ℂ) + h' i)) -
        Ot.M j x X (constFld (fun i => (v i : ℂ))) (constFld (fun i => (v i : ℂ)))) ≤
      improvedConst
          (max (3 ^ d * ((L : ℝ) ^ (P.m₀ + m₁) * (4 * d * L) + 1)) (2 * L * (3 ^ d * (L : ℝ) ^ (P.m₀ + m₁))))
          (δ₀ / 128) (δ₀ / (128 * (3 ^ d * (L : ℝ) ^ (P.m₀ + m₁)))) *
        ((β 0) ^ (-(1 / 2 : ℝ) + Q.ρ₁) * (L : ℝ) ^ (-((j : ℝ) * Q.ρ₀)) * δ *
          Real.exp (-(P.κ - 1) * sizeJ P.m₀ j X)) +
        4 * termBound P Q β L j X * Δ / ρ := by
  refine improved_first_of_const hO ctx.sf ctx.bg ctx.j1 ctx.jk hN hX hx hy hlayer hP hβ0 hδ hδε hε
    hc0 hc1 hεj hsmall ?_
  exact M_const_diff_le hO ctx hX hx i₀ (fun i => (v i : ℂ)) (fun i => (v i : ℂ))
    (fun i => (Ψ₀ y i : ℂ) + Ψ'' y i) (fun i => (h₀ i : ℂ) + h' i) hΔ hv hc hvw hh hdc hdh

/-- **The first bound of Lemma 3.4, `ν`-free regime `β_k ν_k ≤ 1`**: the domain places no condition on
`h`, and the constant part is at most `4 B_X Δ / ρ` for `c, v` in the tube and `|c_i - v_i| ≤ Δ`. -/
theorem improved_first_massFree (hO : IsObs P Q β ν a Tm Ot Gker)
    (ctx : LiftCtx P β ν a Tm ρd Ek j ρ) (hmf : β k * ν k ≤ 1) (hN : L ^ P.m₀ ∣ N₁)
    {X : Set (CTorus d L N₁ m₁ k)} (hX : IsPolyDom P.m₀ j X) {x : CTorus d L N₁ m₁ k} (hx : x ∈ X)
    {y : CTorus d L N₁ m₁ k} (hy : y ∈ X)
    (hlayer : ∀ z ∈ X, (Tm.gs j X).layerIndex z = j)
    {Ψ₀ : CTorus d L N₁ m₁ k → Fin N → ℝ} {h₀ : Fin N → ℝ}
    {Ψ'' : CTorus d L N₁ m₁ k → Fin N → ℂ} {h' : Fin N → ℂ} {δ ε δ₀ : ℝ}
    (hP : InPsiTildeC (Tm.gs j X) (bgMass L k (β k) (ν k)) δ ε Ψ₀ h₀ Ψ'' (fun _ => h'))
    (hβ0 : 0 < β 0) (hδ : 0 < δ) (hδε : δ ≤ ε) (hε : ε ≤ δ₀) (hc0 : δ₀ ≤ bgC0 d L N)
    (hc1 : δ₀ ≤ bgC1 d L N)
    (hεj : δ₀ + (2 * bgK1 d L N + 1) * δ₀ ≤ P.eps d L j)
    (hsmall : 128 * (3 ^ d * ((L : ℝ) ^ (P.m₀ + m₁) * (4 * d * L) + 1)) * δ ≤ δ₀)
    (i₀ : Fin N) {v : Fin N → ℝ} {Δ : ℝ} (hΔ : 0 < Δ)
    (hc : ∀ i, ‖((Ψ₀ y i : ℂ) + Ψ'' y i) - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ ρ / 2)
    (hv : ∀ i, ‖(v i : ℂ) - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ ρ / 2)
    (hdc : ∀ i, ‖((Ψ₀ y i : ℂ) + Ψ'' y i) - (v i : ℂ)‖ ≤ Δ) :
    vn (Ot.M j x X (fun z i => (Ψ₀ z i : ℂ) + Ψ'' z i) (constFld (fun i => (h₀ i : ℂ) + h' i)) -
        Ot.M j x X (constFld (fun i => (v i : ℂ))) (constFld (fun i => (v i : ℂ)))) ≤
      improvedConst
          (max (3 ^ d * ((L : ℝ) ^ (P.m₀ + m₁) * (4 * d * L) + 1)) (2 * L * (3 ^ d * (L : ℝ) ^ (P.m₀ + m₁))))
          (δ₀ / 128) (δ₀ / (128 * (3 ^ d * (L : ℝ) ^ (P.m₀ + m₁)))) *
        ((β 0) ^ (-(1 / 2 : ℝ) + Q.ρ₁) * (L : ℝ) ^ (-((j : ℝ) * Q.ρ₀)) * δ *
          Real.exp (-(P.κ - 1) * sizeJ P.m₀ j X)) +
        4 * termBound P Q β L j X * Δ / ρ := by
  refine improved_first_of_const hO ctx.sf ctx.bg ctx.j1 ctx.jk hN hX hx hy hlayer hP hβ0 hδ hδε hε
    hc0 hc1 hεj hsmall ?_
  exact M_const_diff_le_massFree hO ctx hmf hX hx i₀ (fun i => (v i : ℂ)) (fun i => (v i : ℂ))
    (fun i => (Ψ₀ y i : ℂ) + Ψ'' y i) (fun i => (h₀ i : ℂ) + h' i) hΔ hv hc hdc

end Tube

end Balaban.Observables
