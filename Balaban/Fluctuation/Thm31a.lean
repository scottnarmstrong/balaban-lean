/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.Thm31cde
public import Balaban.Fluctuation.StepObjects
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Theorem 3.1 (a): the localization expansion of `ℰ₀^{(k+1)}(z)` (FLUCTUATION.md §3.5)

Whole-lattice case `Z_k = ∅` (`Ω_{k+1} = Ω''_{k+1} = 𝕋`; the object is `StepSetting.E0loc`).

`E0loc z = -½ ∑_{y ∈ B(z)} tr 𝕃(y,y) + ∫₀¹ ds ⟨DΦ₁(sψ')[1_{B(z)}ψ']⟩_{s,0}`.

The integral is a Theorem-3.4 average (`avg_integral_expansion`) once Proposition 3.3 is available
in the fluctuation variable `ψ̂`.  The landed `interaction_expansion` is local in the fields
`(x,w) = (ψ', C^{1/2}ψ̂)` (through `psiThick Y`), not in `ψ̂`: the map `ψ̂ ↦ C^{1/2}ψ̂` is not
local, and its decoupled expansion (LOC, `C^{1/2}(s)`) is a separate input.  `E1Marks` is
exactly the conclusion of Proposition 3.3 for the actual step, in the variable `ψ̂`, for the mark
`DΦ₁(sψ')[1_{B(z)}ψ']` and the exponent `W₁(s,ψ̂)`; `DetExpansion` is the LOC V3 + Lemma AE
expansion of `-½ ∑ tr 𝕃(y,y)` (Lemma 2.4 (c)); `BlockSplit` is the typing datum that
`ν_{p₁}` is the product of the block measures `ν_b` of Theorem 3.4.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Polymer Balaban.Multiscale Balaban.Background
  MeasureTheory

section Marks

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- **The block structure of `ν_{p₁}`** (Theorem 3.4): the fluctuation variable `ψ̂` of the unit
lattice splits into its restrictions to the `π_{k+1}`-cubes `b` of `Ω = 𝕋`, and `ν_{p₁}` is the
product of the probability measures `ν_b` (typing datum; `ProdSplit` is inhabited, see
`nonempty_prodSplit`). -/
abbrev BlockSplit (S : StepSetting d L N₁ m₁ k N ϱ) (m₀ : ℕ) : Type _ :=
  ProdSplit S.nuFl d L N₁ m₁ (k + 1) m₀

/-- **Proposition 3.3 for the actual step, in the fluctuation variable `ψ̂`, for the integrand of
`ℰ₁^{(k+1)}(z)`** (§3.5 (a)): the exponent `W₁(s,ψ̂)` of `μ_{s,0}` and the mark
`DΦ₁(sψ')[1_{B(z)}ψ']` are, for `s ∈ [0,1]` and `ν_{p₁}`-a.e. `ψ̂`, the sums of the block-local
terms `H(Y; s, ψ̂)` and `G(Y₀; s, ψ̂)` (functions of `ψ̂|_{Y∩Ω}`, bounded by `ε_U e^{-κ_U 𝗱(Y)}`,
resp. `F₀ e^{-κ_G 𝗱(Y₀)}`), holomorphic in the interpolation parameter `s` on an open set
`𝒰 ⊃ [0,1]`; together with the numerical hypotheses of Theorem 3.4 (`InterpMarks`). -/
abbrev E1Marks (S : StepSetting d L N₁ m₁ k N ϱ) (C : StepClass d L N₁ m₁ k N ϱ) {m₀ : ℕ}
    (BS : BlockSplit S m₀) (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))) : Type _ :=
  InterpMarks S.nuFl BS (S.Wone C) (fun s x =>
    (fderiv ℝ (S.Phi1 C) (s • S.shiftU x)) (S.maskU z (S.shiftU x)))

end Marks

section Thm

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  {S : StepSetting d L N₁ m₁ k N ϱ} {C : StepClass d L N₁ m₁ k N ϱ} {m₀ : ℕ}
  {BS : BlockSplit S m₀} {z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))}

open Classical in
/-- **The interpolation integral `ℰ₁^{(k+1)}(z)` has a localization expansion** (§3.5 (a)),
conditional on `E1Marks` (Proposition 3.3 in the variable `ψ̂`): `ℰ₁(z) = ∑_S E(S)` over the sets
`S` of `π_{k+1}`-cubes, with `|E(S)| ≤ C_PE (∑_{Y₀} F₀ e^{-κ₀𝗱(Y₀)}) e^{-κ' d_Ω(S)}`. -/
theorem e1loc_expansion_of_input (I : E1Marks S C BS z) :
    ∃ E : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
        Set.univ) → ℂ,
      S.E1loc C z = ∑ T, E T ∧
      ∀ T, ‖E T‖ ≤ CPE d L I.Kc I.κH I.κ0 I.κ' *
          (∑ i, I.F0 i * Real.exp (-I.κ0 * I.Lab.dl (I.y0 i))) * Real.exp (-I.κ' * dExt T) :=
  interpAvg_expansion_of_input I

end Thm

section Det

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  {S : StepSetting d L N₁ m₁ k N ϱ} {C : StepClass d L N₁ m₁ k N ϱ} {m₀ : ℕ}

/-- **The expansion of `-½ ∑_{y ∈ B(z)} tr 𝕃(y,y)`** (§3.5 (a): LOC V3 with `F(s) = 𝕃(s)(y,y)`,
Lemma AE; Lemma 2.4 (c)): a sum over sets `T` of `π_{k+1}`-cubes with terms bounded by
`c_det e^{-κ'' d_Ω(T)}`. -/
structure DetExpansion (S : StepSetting d L N₁ m₁ k N ϱ) (m₀ : ℕ)
    (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))) (κ'' cdet : ℝ) where
  term : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
    Set.univ) → ℂ
  sum_eq : -(1 / 2 : ℂ) * ∑ y ∈ S.blockU z, ∑ i, S.logA (y, i) (y, i) = ∑ T, term T
  bound : ∀ T, ‖term T‖ ≤ cdet * Real.exp (-κ'' * dExt T)

/-- `DetExpansion` is inhabited (a single term carries the whole value; the constant is
`|value| e^{κ'' M}`), for every step, every `z` and every `κ'' ≥ 0`. -/
theorem nonempty_detExpansion (S : StepSetting d L N₁ m₁ k N ϱ) (m₀ : ℕ)
    (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))) {κ'' : ℝ} (hκ : 0 ≤ κ'') :
    ∃ cdet, Nonempty (DetExpansion S m₀ z κ'' cdet) := by
  classical
  set v : ℂ := -(1 / 2 : ℂ) * ∑ y ∈ S.blockU z, ∑ i, S.logA (y, i) (y, i) with hv
  set T0 : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
    Set.univ) := ∅
  refine ⟨‖v‖ * Real.exp (κ'' * Mbig d L N₁ m₁ (k + 1)), ⟨⟨fun T => if T = T0 then v else 0,
    by simp [hv, Finset.sum_ite_eq'], fun T => ?_⟩⟩⟩
  by_cases hT : T = T0
  · simp only [hT, ite_true]
    have h1 : Real.exp (-κ'' * dExt T0) ≥ Real.exp (-κ'' * Mbig d L N₁ m₁ (k + 1)) :=
      Real.exp_le_exp.2 (by nlinarith [dExt_le_Mbig (m₀ := m₀) (j := k + 1) (Ω := Set.univ) T0])
    calc ‖v‖ = ‖v‖ * Real.exp (κ'' * Mbig d L N₁ m₁ (k + 1)) *
          Real.exp (-κ'' * Mbig d L N₁ m₁ (k + 1)) := by
          rw [mul_assoc, ← Real.exp_add]; simp
      _ ≤ _ := mul_le_mul_of_nonneg_left h1 (by positivity)
  · simp only [hT, ite_false, norm_zero]
    exact mul_nonneg (mul_nonneg (norm_nonneg _) (Real.exp_pos _).le) (Real.exp_pos _).le

open Classical in
/-- **Theorem 3.1 (a), whole-lattice case, conditional on its inputs**:
`ℰ₀^{(k+1)}(z) = ∑_S ℰ₀(z,S)` over the sets `S` of `π_{k+1}`-cubes with
`|ℰ₀(z,S)| ≤ (c_mark + c_det) e^{-κ' d_Ω(S)}` (`c_mark = C_PE ∑_{Y₀} F₀ e^{-κ₀𝗱(Y₀)}`).  The
named inputs are `E1Marks` (Proposition 3.3 for the actual step in the variable `ψ̂`) and
`DetExpansion` (Lemma 2.4 (c) with LOC V3).  The symmetry clauses are the separate later
theorem (O(N)/Euclidean equivariance of the decoupled objects). -/
theorem thm31a_of_input {BS : BlockSplit S m₀}
    {z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))}
    (I : E1Marks S C BS z) {κ'' cdet : ℝ} (hκ'' : I.κ' ≤ κ'') (D : DetExpansion S m₀ z κ'' cdet) :
    ∃ E : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
        Set.univ) → ℂ,
      S.E0loc C z = ∑ T, E T ∧
      ∀ T, ‖E T‖ ≤ (CPE d L I.Kc I.κH I.κ0 I.κ' *
          (∑ i, I.F0 i * Real.exp (-I.κ0 * I.Lab.dl (I.y0 i))) + cdet) *
        Real.exp (-I.κ' * dExt T) := by
  obtain ⟨E1, h1, h2⟩ := e1loc_expansion_of_input I
  refine ⟨fun T => D.term T + E1 T, ?_, fun T => ?_⟩
  · rw [Finset.sum_add_distrib, ← D.sum_eq, ← h1]
    rfl
  · refine (norm_add_le _ _).trans ?_
    have hd : ‖D.term T‖ ≤ cdet * Real.exp (-I.κ' * dExt T) := by
      refine (D.bound T).trans ?_
      have hc : 0 ≤ cdet := by
        have := (D.bound T).trans' (norm_nonneg _)
        rcases le_or_gt 0 cdet with h | h
        · exact h
        · nlinarith [Real.exp_pos (-κ'' * dExt T)]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hc
      nlinarith [dExt_nonneg (m₀ := m₀) (j := k + 1) (Ω := Set.univ) T]
    nlinarith [h2 T]

/-- **Theorem 3.1 (a) with the stated constant**, conditional on the same inputs: if the
mark constant is at most `K₀` and the determinant constant at most `N L^d B_𝕃 K₀` (the smallness
of `ε_U`, "`β` large", and the bound `‖𝕃(y,y)‖ ≤ N B_𝕃`), then
`|ℰ₀(z,S)| ≤ (N L^d B_𝕃 + 1) K₀ e^{-κ_a d_Ω(S)}` with `κ_a = κ'`. -/
theorem thm31a_of_input_const {BS : BlockSplit S m₀}
    {z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))}
    (I : E1Marks S C BS z) {κ'' cdet : ℝ} (hκ'' : I.κ' ≤ κ'') (D : DetExpansion S m₀ z κ'' cdet)
    {BL K0c : ℝ}
    (hmark : CPE d L I.Kc I.κH I.κ0 I.κ' *
      (∑ i, I.F0 i * Real.exp (-I.κ0 * I.Lab.dl (I.y0 i))) ≤ K0c)
    (hdet : cdet ≤ N * (L : ℝ) ^ d * BL * K0c) :
    ∃ E : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
        Set.univ) → ℂ,
      S.E0loc C z = ∑ T, E T ∧
      ∀ T, ‖E T‖ ≤ (N * (L : ℝ) ^ d * BL + 1) * K0c * Real.exp (-I.κ' * dExt T) := by
  obtain ⟨E, h1, h2⟩ := thm31a_of_input I hκ'' D
  refine ⟨E, h1, fun T => (h2 T).trans ?_⟩
  exact mul_le_mul_of_nonneg_right (by nlinarith) (Real.exp_pos _).le

end Det

end Balaban.Fluctuation
