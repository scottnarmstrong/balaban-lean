/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Observables.LayerV2Renorm
public import Balaban.Observables.ConstPartTube

/-!
# The observable layer of the second version: the first bound of Lemma 3.4 on the constant tube

The landed consumers of `IsObs` that do not use the coefficient bounds read the coefficient `β`
only through `β_0` (the bounds (O1), (2.1), (2.2)), `β_{j-1}`, `j ≤ k` (the identification (O4))
and the running-test mass `bgMass L k (β k) (ν k)` of the domain.  Hence:

* `betaObs`: the coefficients `β` with `β_k` replaced by `ν_k^{-1} + 1`, so that `β'_k ν_k > 1`
  and the running-test mass of the landed class is the complete mass (`bgMass_betaObs`);
* `isObs_of_isObs2` (**the reduction for the observable layer**): the clauses (O1)-(O3) of an
  observable layer of the second version on the wide domain at the mass
  `bgMass L k (β' k) (ν k)`, with `β'_0 = β_0`, are those of a landed layer `IsObs` for the
  constants `P.noChi` (empty characteristic set, so that (O4) is void);
* `IsSFObs2.improved_first_of_tube`: **the first bound of Lemma 3.4 with complete backgrounds**,
  the port of the landed `improved_first_of_tube` to the second version at every scale: the
  constant part is bounded through the source `b = ν_j h`,
  `Δ ≥ max(|c - v|, ν_j |h - v|)`.  It replaces `improved_first_massFree` (the mass-free branch of
  the landed class, in which `h` was unconstrained).

The landed consumers `mFactor_sub_one_le`, `sum_R_le` use `CoeffBounds` for the same `β`; they are
ported directly in `LayerV2Renorm`.
-/

@[expose] public section

namespace Balaban.Observables

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
open Balaban.SmallField.Def6 Balaban.SmallField.Def6v2 Metric Finset

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- The coefficients `β` with `β_k` replaced by `ν_k^{-1} + 1` (so that `β'_k ν_k = 1 + ν_k > 1`);
`β'_n = β_n` for `n ≠ k`. -/
noncomputable def betaObs (β : ℕ → ℝ) (k : ℕ) (νk : ℝ) : ℕ → ℝ :=
  Function.update β k (νk⁻¹ + 1)

omit [NeZero L] [NeZero N₁] in
theorem betaObs_of_ne (β : ℕ → ℝ) (νk : ℝ) {n k : ℕ} (h : n ≠ k) : betaObs β k νk n = β n :=
  Function.update_of_ne h _ _

omit [NeZero L] [NeZero N₁] in
theorem betaObs_self (β : ℕ → ℝ) (k : ℕ) (νk : ℝ) : betaObs β k νk k = νk⁻¹ + 1 :=
  Function.update_self _ _ _

omit [NeZero L] [NeZero N₁] in
/-- The running-test mass of the landed class at `betaObs` is the complete mass `ν_k L^{-2k}`. -/
theorem bgMass_betaObs (β : ℕ → ℝ) (k : ℕ) {νk : ℝ} (hν : 0 < νk) :
    Def6.bgMass L k (betaObs β k νk k) νk = physMass L k νk := by
  have h1 : 1 < betaObs β k νk k * νk := by
    rw [betaObs_self, add_mul, inv_mul_cancel₀ hν.ne']
    linarith
  unfold Def6.bgMass physMass
  rw [ite_eq_right fun h => absurd h (not_le.2 h1)]

section Reduction

variable {P : Consts} {Q : ObsConsts} {Rg : Regime L} {β β' ν a : ℕ → ℝ}
  {Tm : Terms d L N₁ m₁ k N ϱ} {Ot : ObsTerms d L N₁ m₁ k N}
  {Gker : ℕ → CTorus d L N₁ m₁ k → CTorus d L N₁ m₁ k → Fld d L N₁ m₁ k N →
    Fld d L N₁ m₁ k N → Matrix (Fin N) (Fin N) ℂ}

/-- **The reduction of the observable layer of the second version to the landed layer.**  Let
`IsObs2` hold on the wide domain `Ξ^c_j` at a mass `μ`, and let `β', ν` be coefficients with
`β'_0 = β_0` and running-test mass `bgMass L k (β'_k) (ν_k) = μ`.  Then the terms are a landed
observable layer `IsObs` for `β', ν` and the constants `P.noChi`: the clauses (O1)-(O3) are the
same, and the identification (O4) is void (empty characteristic set). -/
theorem isObs_of_isObs2 {μ : ℝ} (hμ : Def6.bgMass L k (β' k) (ν k) = μ) (h0 : β' 0 = β 0)
    (hO : IsObs2 P Q Rg β a (xiFieldDom (aIdeal L k (a k)) μ (P.eps d L)) Tm Ot Gker) :
    IsObs P.noChi Q β' ν a Tm Ot Gker := by
  subst hμ
  exact
    { μ_euc := hO.μ_euc
      μ_bound := by rw [h0]; exact hO.μ_bound
      analyticM := hO.analyticM
      analyticR := hO.analyticR
      rotM := hO.rotM
      rotR := hO.rotR
      eucM := hO.eucM
      eucR := hO.eucR
      eucMloc := hO.eucMloc
      eucRloc := hO.eucRloc
      localM := hO.localM
      localR := hO.localR
      realM := hO.realM
      realR := hO.realR
      boundM := by rw [h0]; exact hO.boundM
      boundR := by rw [h0]; exact hO.boundR
      normM := fun j hj1 hjk x v hv => hO.normM j hj1 hjk x v (Set.mem_univ v) hv
      ident := fun Ψ₀ h₀ D _ hX =>
        absurd hX.2.1 (by rw [noChi_p, zero_div]; exact lt_irrefl 0) }

end Reduction

section Tube

variable {P : Consts} {Q : ObsConsts} {Rg : Regime L} {β a : ℕ → ℝ} {Tm : Terms d L N₁ m₁ k N ϱ}
  {Ot : ObsTerms d L N₁ m₁ k N}
  {Gker : ℕ → CTorus d L N₁ m₁ k → CTorus d L N₁ m₁ k → Fld d L N₁ m₁ k N →
    Fld d L N₁ m₁ k N → Matrix (Fin N) (Fin N) ℂ}
  {ρd : (CTorus d L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) → (CTorus d L N₁ m₁ k → Fin N → ℝ) → ℝ}
  {Ek : ℝ} {j : ℕ} {ρ : ℝ}

/-- **The first bound of Lemma 3.4 with complete backgrounds** (the port of the landed
`improved_first_of_tube` to the second version; it replaces `improved_first_massFree`).  For the
observable layer of the second version on the wide domain at the complete mass, at every scale
`1 ≤ j ≤ k`: `c = Ψ₀(y) + Ψ''(y)`, `h = h₀ + h'` and the real unit vector `v` lie in the tube of
`e_{i₀}` (`|c_i - δ_{i i₀}|, |v_i - δ_{i i₀}| ≤ ρ/2`, `ν_j |h_i - δ_{i i₀}|, ν_j |v_i - δ_{i i₀}| ≤
ρ/2`: the sources `ν_j h`, `ν_j v` within `ρ/2` of `ν_j e_{i₀}`), and `|c_i - v_i| ≤ Δ`,
`ν_j |h_i - v_i| ≤ Δ`.  Then the constant part is at most `4 B_X Δ / ρ`,
`B_X = β^{-1/2+ρ₁} L^{-jρ₀} e^{-κ d_j(X)}`; the first term is that of `improved_first_of_const`.
The constants are those of the landed statement. -/
theorem IsSFObs2.improved_first_of_tube
    (hS : IsSFObs2 P Q Rg β a (completeXiDom P Rg a N₁) Tm ρd Ek Ot Gker)
    (hBg : BgHyp d L k ϱ (aIdeal L k (a k)) (Rg.sfBgMass k)) (hν : 0 < Rg.ν k) (hj1 : 1 ≤ j)
    (hjk : j ≤ k) (hρ : 0 < ρ)
    (hrad : ∃ δ : ℝ, 0 < δ ∧ δ ≤ bgC0 d L N ∧ δ ≤ bgC1 d L N ∧
      (2 * bgK1 d L N + 2) * δ ≤ P.eps d L j ∧ (N : ℝ) * (ρ * (1 + N * rotB N)) < δ ^ 2)
    (hN : L ^ P.m₀ ∣ N₁)
    {X : Set (CTorus d L N₁ m₁ k)} (hX : IsPolyDom P.m₀ j X) {x : CTorus d L N₁ m₁ k} (hx : x ∈ X)
    {y : CTorus d L N₁ m₁ k} (hy : y ∈ X)
    (hlayer : ∀ z ∈ X, (Tm.gs j X).layerIndex z = j)
    {Ψ₀ : CTorus d L N₁ m₁ k → Fin N → ℝ} {h₀ : Fin N → ℝ}
    {Ψ'' : CTorus d L N₁ m₁ k → Fin N → ℂ} {h' : Fin N → ℂ} {δ ε δ₀ : ℝ}
    (hP : InPsiTildeC (Tm.gs j X) (Rg.sfBgMass k) δ ε Ψ₀ h₀ Ψ'' (fun _ => h'))
    (hβ0 : 0 < β 0) (hδ : 0 < δ) (hδε : δ ≤ ε) (hε : ε ≤ δ₀) (hc0 : δ₀ ≤ bgC0 d L N)
    (hc1 : δ₀ ≤ bgC1 d L N)
    (hεj : δ₀ + (2 * bgK1 d L N + 1) * δ₀ ≤ P.eps d L j)
    (hsmall : 128 * (3 ^ d * ((L : ℝ) ^ (P.m₀ + m₁) * (4 * d * L) + 1)) * δ ≤ δ₀)
    (i₀ : Fin N) {v : Fin N → ℝ} {Δ : ℝ} (hΔ : 0 < Δ)
    (hc : ∀ i, ‖((Ψ₀ y i : ℂ) + Ψ'' y i) - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ ρ / 2)
    (hv : ∀ i, ‖(v i : ℂ) - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ ρ / 2)
    (hvw : ∀ i, nuIdeal L k (Rg.ν k) j *
      ‖(v i : ℂ) - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ ρ / 2)
    (hh : ∀ i, nuIdeal L k (Rg.ν k) j *
      ‖((h₀ i : ℂ) + h' i) - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ ρ / 2)
    (hdc : ∀ i, ‖((Ψ₀ y i : ℂ) + Ψ'' y i) - (v i : ℂ)‖ ≤ Δ)
    (hdh : ∀ i, nuIdeal L k (Rg.ν k) j * ‖((h₀ i : ℂ) + h' i) - (v i : ℂ)‖ ≤ Δ) :
    vn (Ot.M j x X (fun z i => (Ψ₀ z i : ℂ) + Ψ'' z i) (constFld (fun i => (h₀ i : ℂ) + h' i)) -
        Ot.M j x X (constFld (fun i => (v i : ℂ))) (constFld (fun i => (v i : ℂ)))) ≤
      improvedConst
          (max (3 ^ d * ((L : ℝ) ^ (P.m₀ + m₁) * (4 * d * L) + 1))
            (2 * L * (3 ^ d * (L : ℝ) ^ (P.m₀ + m₁))))
          (δ₀ / 128) (δ₀ / (128 * (3 ^ d * (L : ℝ) ^ (P.m₀ + m₁)))) *
        ((β 0) ^ (-(1 / 2 : ℝ) + Q.ρ₁) * (L : ℝ) ^ (-((j : ℝ) * Q.ρ₀)) * δ *
          Real.exp (-(P.κ - 1) * sizeJ P.m₀ j X)) +
        4 * termBound P Q β L j X * Δ / ρ := by
  have hμ : Def6.bgMass L k (betaObs β k (Rg.ν k) k) (Rg.ν k) = Rg.sfBgMass k :=
    bgMass_betaObs β k hν
  have h0 : betaObs β k (Rg.ν k) 0 = β 0 := betaObs_of_ne β _ (by omega)
  have hm : Def6.bgMass L k (betaObs β k (Rg.ν k) k) (Rg.ν k) * ((L : ℝ) ^ j) ^ 2 =
      nuIdeal L k (Rg.ν k) j := by rw [hμ]; exact Rg.sfBgMass_mul_sq hjk
  have hO' : IsObs P.noChi Q (betaObs β k (Rg.ν k)) Rg.ν a Tm Ot Gker :=
    isObs_of_isObs2 hμ h0 hS.obs
  have ctx : LiftCtx P.noChi (betaObs β k (Rg.ν k)) Rg.ν a Tm (fun _ _ _ => 0) Ek j ρ :=
    ⟨isSF_of_termClauses (P := P.noChi) rfl (by rw [hμ]; exact hS.sf.terms.noChi),
      by rw [hμ]; exact hBg, hν, hj1, hjk, hρ, hrad⟩
  have hβ0' : 0 < betaObs β k (Rg.ν k) 0 := by rw [h0]; exact hβ0
  have key := Balaban.Observables.improved_first_of_tube hO' ctx hN hX hx hy hlayer
    (by rw [hμ]; exact hP) hβ0' hδ hδε hε hc0 hc1 hεj hsmall i₀ hΔ hc hv
    (fun i => by rw [hm]; exact hvw i) (fun i => by rw [hm]; exact hh i) hdc
    (fun i => by rw [hm]; exact hdh i)
  have e : termBound P.noChi Q (betaObs β k (Rg.ν k)) L j X = termBound P Q β L j X := by
    unfold termBound
    rw [h0]
    rfl
  rw [e, h0] at key
  exact key

end Tube

end Balaban.Observables
