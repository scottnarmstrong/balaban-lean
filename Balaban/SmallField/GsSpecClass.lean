/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.Def6v2Inhabited
public import Balaban.SmallField.GsSpecStrong
public import Balaban.Observables.ImprovedFirst

/-!
# The v2 term clauses with `GsSpecStrong`

`SFTermClausesStrong` extends `Def6v2.SFTermClauses` by `GsSpecStrong` of every `Tm.gs j X`;
`SFTermClausesStrong.hlayer` and `improved_first_of_const_strong` derive W111's premise `hlayer`;
`sfTermClausesStrong_witness` is the `Nonempty` witness (pinned terms, whole-level sets).
-/

@[expose] public section

namespace Balaban.SmallField.GsSpec

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.SmallField.Def6v2 Balaban.Observables Finset

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- **The term clauses of the v2 class with the strong specification of the local sets**: the
clauses of `SFTermClauses` and, for every polymer `X ∈ 𝒟_j`, `1 ≤ j ≤ k`, `GsSpecStrong` of
`Tm.gs j X`. -/
structure SFTermClausesStrong (P : Consts) (Dom : FieldDom d L N₁ m₁ k N ϱ)
    (Tm : Terms d L N₁ m₁ k N ϱ) : Prop extends SFTermClauses P Dom Tm where
  gsStrong : ∀ j, 1 ≤ j → ∀ hjk : j ≤ k, ∀ X, IsPolyDom P.m₀ j X →
    GsSpecStrong j hjk X (Tm.gs j X)

/-- **`hlayer` of W111** (`improved_first_of_const`): `X` lies in the top layer `j` of
`Tm.gs j X`. -/
theorem SFTermClausesStrong.hlayer {P : Consts} {Dom : FieldDom d L N₁ m₁ k N ϱ}
    {Tm : Terms d L N₁ m₁ k N ϱ} (h : SFTermClausesStrong P Dom Tm) {j : ℕ} (hj1 : 1 ≤ j)
    (hjk : j ≤ k) {X : Set (CTorus d L N₁ m₁ k)} (hX : IsPolyDom P.m₀ j X) :
    ∀ z ∈ X, (Tm.gs j X).layerIndex z = j := fun _ hz =>
  (h.gsStrong j hj1 hjk X hX).toGsSpecCore.layerIndex_eq hj1 hjk hz

/-- The strong clauses are inhabited: the pinned terms with all coefficients `0` (whole-level
generating sets) satisfy them for any field domain and any admissible constants with
`E₀, κ ≥ 0`, `c₉ > 0`. -/
theorem sfTermClausesStrong_pin_nonempty {P : Consts} (hE₀ : 0 ≤ P.E₀) (hκ : 0 ≤ P.κ)
    (hc9 : ∀ j, 0 < P.c₉ * ((L : ℝ) ^ j)⁻¹ ^ (((d : ℝ) - 2) / 2 + P.γ - P.α₁))
    (Dom : FieldDom d L N₁ m₁ k N ϱ) :
    Nonempty (SFTermClausesStrong P Dom (pinTerms d L N₁ m₁ k N ϱ P.κ (fun _ => 0))) := by
  refine ⟨{
    toSFTermClauses := pinTerms_clauses hE₀ hκ (fun _ => le_rfl) (fun j => by
        have := hc9 j; linarith) hc9 (fun j h => absurd rfl h)
    gsStrong := fun j hj1 hjk X _ => ?_ }⟩
  rw [pinTerms_gs hjk]
  exact levelGS_strong hj1 hjk X

/-- A concrete choice of constants for which the hypotheses of the witness hold. -/
noncomputable def witnessConsts : Consts where
  γ := 1 / 4
  α₁ := 1 / 4
  κ := 1
  E₀ := 0
  c₈ := 1
  c₉ := 1
  α₀ := 1
  B := 1
  νbar := 1
  p := fun _ => 1
  m₀ := 0

theorem sfTermClausesStrong_witness (Dom : FieldDom d L N₁ m₁ k N ϱ) :
    Nonempty (SFTermClausesStrong witnessConsts Dom
      (pinTerms d L N₁ m₁ k N ϱ witnessConsts.κ (fun _ => 0))) := by
  refine sfTermClausesStrong_pin_nonempty (by simp [witnessConsts]) (by simp [witnessConsts])
    (fun j => ?_) Dom
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  simp only [witnessConsts, one_mul]
  positivity


section Observable

variable {P : Consts} {Q : ObsConsts} {β ν a : ℕ → ℝ} {Tm : Terms d L N₁ m₁ k N ϱ}
  {Ot : ObsTerms d L N₁ m₁ k N}
  {Gker : ℕ → CTorus d L N₁ m₁ k → CTorus d L N₁ m₁ k → Fld d L N₁ m₁ k N →
    Fld d L N₁ m₁ k N → Matrix (Fin N) (Fin N) ℂ}
  {ρd : (CTorus d L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) → (CTorus d L N₁ m₁ k → Fin N → ℝ) → ℝ}
  {Ek : ℝ} {j : ℕ}

/-- **`improved_first_of_const` with `hlayer` derived from the strong specification** of the local
sets (the premise `hS` is the clause `gsStrong` of `SFTermClausesStrong`): the typing premise
"`X` lies in the top layer `j` of `𝔹_j(X)`" is no longer a hypothesis. -/
theorem improved_first_of_const_strong (hO : IsObs P Q β ν a Tm Ot Gker)
    (hsf : IsSF P β ν a Tm ρd Ek)
    (hS : ∀ j, 1 ≤ j → ∀ hjk : j ≤ k, ∀ X, IsPolyDom P.m₀ j X → GsSpecStrong j hjk X (Tm.gs j X))
    (hbg : BgHyp d L k ϱ (aIdeal L k (a k)) (bgMass L k (β k) (ν k)))
    (hj1 : 1 ≤ j) (hjk : j ≤ k) (hN : L ^ P.m₀ ∣ N₁)
    {X : Set (CTorus d L N₁ m₁ k)} (hX : IsPolyDom P.m₀ j X) {x : CTorus d L N₁ m₁ k} (hx : x ∈ X)
    {y : CTorus d L N₁ m₁ k} (hy : y ∈ X)
    {Ψ₀ : CTorus d L N₁ m₁ k → Fin N → ℝ} {h₀ : Fin N → ℝ}
    {Ψ'' : CTorus d L N₁ m₁ k → Fin N → ℂ} {h' : Fin N → ℂ} {δ ε δ₀ : ℝ}
    (hP : InPsiTildeC (Tm.gs j X) (bgMass L k (β k) (ν k)) δ ε Ψ₀ h₀ Ψ'' (fun _ => h'))
    (hβ0 : 0 < β 0) (hδ : 0 < δ) (hδε : δ ≤ ε) (hε : ε ≤ δ₀) (hc0 : δ₀ ≤ bgC0 d L N)
    (hc1 : δ₀ ≤ bgC1 d L N)
    (hεj : δ₀ + (2 * bgK1 d L N + 1) * δ₀ ≤ P.eps d L j)
    (hsmall : 128 * (3 ^ d * ((L : ℝ) ^ (P.m₀ + m₁) * (4 * d * L) + 1)) * δ ≤ δ₀)
    {v : Fin N → ℝ} {bc : ℝ}
    (hconst : vn (Ot.M j x X (constFld (fun i => (Ψ₀ y i : ℂ) + Ψ'' y i))
        (constFld (fun i => (h₀ i : ℂ) + h' i)) -
      Ot.M j x X (constFld (fun i => (v i : ℂ))) (constFld (fun i => (v i : ℂ)))) ≤ bc) :
    vn (Ot.M j x X (fun z i => (Ψ₀ z i : ℂ) + Ψ'' z i) (constFld (fun i => (h₀ i : ℂ) + h' i)) -
        Ot.M j x X (constFld (fun i => (v i : ℂ))) (constFld (fun i => (v i : ℂ)))) ≤
      improvedConst
          (max (3 ^ d * ((L : ℝ) ^ (P.m₀ + m₁) * (4 * d * L) + 1)) (2 * L * (3 ^ d * (L : ℝ) ^ (P.m₀ + m₁))))
          (δ₀ / 128) (δ₀ / (128 * (3 ^ d * (L : ℝ) ^ (P.m₀ + m₁)))) *
        ((β 0) ^ (-(1 / 2 : ℝ) + Q.ρ₁) * (L : ℝ) ^ (-((j : ℝ) * Q.ρ₀)) * δ *
          Real.exp (-(P.κ - 1) * sizeJ P.m₀ j X)) + bc :=
  improved_first_of_const hO hsf hbg hj1 hjk hN hX hx hy
    (fun _ hz => (hS j hj1 hjk X hX).toGsSpecCore.layerIndex_eq hj1 hjk hz) hP hβ0 hδ hδε hε hc0
    hc1 hεj hsmall hconst

end Observable

end Balaban.SmallField.GsSpec
