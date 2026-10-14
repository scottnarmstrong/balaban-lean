/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.GeneralClassMatch
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The hypotheses of the expansion on the old-term functionals, from the class

The physical expansion (`interaction_expansion_hat_dm`, `physical_directTerms`) asks, for each old
term, a functional `EE τ` of the raw data that is analytic and bounded on the chart
`Ξ^c_j(𝔹_j(X); C₀, ε₂)` of its generating set `GjE τ`, with `C₀ = scaledC0 d` and
`ε₂ = C₀² ε + K₂ δ₃ + K₂ δ_fl` (the hypotheses `hEanE`, `hEbdE`).  For the zero class the family of
old terms is empty.  For a member of the class `IsSF2` the terms are analytic and bounded on
`Ξ^c_j(𝔹_j(X); 1, ε_j)`, with `𝔹_j(X) = C.Tm.gs j X` the generating set of the class term.

* `xiDom_of_xiCData`: `Ξ^c_n(𝔹; C₀, ε) ⊆ Ξ^c_n(𝔹; 1, ε')` if `C₀² ε ≤ ε'` (the same-centre
  rescaling `xiC_rescale_of_agree`, for the raw data of a datum).
* `classE_analyticOnNhd_xiCRaw_of_isSF2`, `classE_norm_le_xiCRaw_of_isSF2`: for a member of
  `IsSF2` on the main domain `completeXiDom`, matched to the step (`ClassParamMatch`), the energy
  term `ℰ^{(j)}(y, X; ·, ·)` (times a constant) is analytic on the chart
  `Ξ^c_j(C.Tm.gs j X; C₀, ε₂)` of the expansion and bounded there by `E₀ e^{-κ d_j(X)}`, **if**
  `C₀² ε₂ ≤ ε_j` (the class-radius inequality).
* `classM_analyticOnNhd_xiCRaw_of_isSF2`: the same for a component of the observable term
  `ℳ^{(j)}(x, X; ·, ·, g)` at a fixed source `g` with `‖g‖₁ < 1`.

Each holds for a chart `Ξ^c_j(𝔹; σ, ε₂)` with any `σ ≥ 1` under `σ² ε₂ ≤ ε_j` (the `_of_one_le`
versions; the landed statements are the instances `σ = C₀`).  At `σ = 1`, the chart of the
composition without radius loss (`point_facts_fl_of_one_le` at `b = 1`), the test is
`ε₂ ≤ ε_j`, P3 (4.37).

So the analyticity hypotheses of the expansion on the old-term functionals are consequences of
class membership when the functional lives on the generating set of the class term and the
class-radius inequality `C₀² ε₂ ≤ ε_j` holds.  The inequality itself is not proved (it constrains
the constants of the class against the chart radius), and nothing is said when the functional
lives on another generating set.  The generating sets `C.Tm.gs j X` are those of the class,
whatever they are.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.SmallField.Def6v2 Finset Set

section Chart

variable {d L N₁ m₁ K N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- **A chart `Ξ^c_n(𝔹; σ, ε)`, `σ ≥ 1`, lies in the chart of the class after rescaling**: the raw
data of a datum realizing a member of `Ξ^c_n(𝔹; σ, ε)` lie in `Ξ^c_n(𝔹; 1, ε')` if `σ² ε ≤ ε'`. -/
theorem xiDom_of_xiCData_of_one_le {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {A : ℕ → ℝ} {μ : ℝ}
    {n : ℕ} {σ ε ε' : ℝ} (hσ : 1 ≤ σ) (hε : σ ^ 2 * ε ≤ ε') {D : BgData G N}
    (hD : XiCData G A μ n σ ε D) : XiDom G A μ n ε' D.Ψ D.h := by
  obtain ⟨Ψ₀, h₀, Ψ'', h'', hxc, hR⟩ := hD
  refine ⟨Ψ₀, h₀, fun x i => D.Ψ x i - Ψ₀ x i, fun x i => D.h x i - h₀ i, ?_, ?_,
    xiC_rescale_of_agree hσ hε (fun x hx i => ?_) (fun x hx i => ?_) hxc⟩
  · intro x i
    ring
  · intro x i
    ring
  · rw [hR.1 x hx i]; ring
  · rw [hR.2 x hx i]; ring

/-- **The chart of the expansion lies in the chart of the class after rescaling**: the raw data
of a datum realizing a member of `Ξ^c_n(𝔹; C₀, ε)` lie in `Ξ^c_n(𝔹; 1, ε')` if `C₀² ε ≤ ε'`,
`C₀ = scaledC0 d`. -/
theorem xiDom_of_xiCData {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {A : ℕ → ℝ} {μ : ℝ} {n : ℕ}
    {ε ε' : ℝ} (hε : scaledC0 d ^ 2 * ε ≤ ε') {D : BgData G N}
    (hD : XiCData G A μ n (scaledC0 d) ε D) : XiDom G A μ n ε' D.Ψ D.h :=
  xiDom_of_xiCData_of_one_le (one_le_scaledC0 d) hε hD

end Chart

section Class

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  {S : StepSetting d L N₁ m₁ k N ϱ} {C : StepClass d L N₁ m₁ k N ϱ} {P : Consts}
  {Rg : Regime L} {β a : ℕ → ℝ} {Tm : Terms d L N₁ m₁ (k + 1) N ϱ}
  {ρ : (CTorus d L N₁ m₁ (k + 1) → Fin N → ℝ) → (Fin N → ℝ) →
    (CTorus d L N₁ m₁ (k + 1) → Fin N → ℝ) → ℝ} {E : ℝ}
  (hm : ClassParamMatch S C P Rg a Tm) (h : IsSF2 P Rg β a (completeXiDom P Rg a N₁) Tm ρ E)

include hm h in
/-- **The energy term of a member of the class is analytic on a chart `Ξ^c_j(C.Tm.gs j X; σ, ε₂)`,
`σ ≥ 1`**: if `σ² ε₂ ≤ ε_j`, the functional `(Ψ, h) ↦ c · ℰ^{(j)}(y, X; Ψ, h)` is analytic at every
point of that chart.  At `σ = 1` (the chart of the composition without radius loss) the test is
`ε₂ ≤ ε_j`, P3 (4.37). -/
theorem classE_analyticOnNhd_xiCRaw_of_isSF2_of_one_le {σ : ℝ} (hσ : 1 ≤ σ) {j : ℕ} (h1 : 1 ≤ j)
    (hjk : j ≤ k)
    (y : CTorus d L N₁ m₁ (k + 1)) {X : Set (CTorus d L N₁ m₁ (k + 1))}
    (hX : IsPolyDom C.m₀ j X) (hy : y ∈ X) {ε₂ : ℝ} (hε : σ ^ 2 * ε₂ ≤ P.eps d L j)
    (cst : ℂ) :
    AnalyticOnNhd ℂ (fun raw : RawData d L (N₁ * L ^ m₁) (k + 1) N =>
        cst * C.Tm.E j y X raw.1 raw.2)
      (XiCRaw (C.Tm.gs j X) S.a S.ν j σ ε₂) := by
  have hT := stepTermsAnalytic_of_isSF2_step hm h
  rintro p ⟨D, hD, rfl⟩
  exact analyticAt_const.mul
    (hT.analyticE j h1 hjk y X hX hy (rawOf D) (xiDom_of_xiCData_of_one_le hσ hε hD))

include hm h in
/-- **The energy term of a member of the class is analytic on the chart of the expansion**, on the
generating set of the term: if `C₀² ε₂ ≤ ε_j`, the functional
`(Ψ, h) ↦ c · ℰ^{(j)}(y, X; Ψ, h)` is analytic at every point of `Ξ^c_j(C.Tm.gs j X; C₀, ε₂)`
(at the weights and mass of the step).  This is the hypothesis `hEanE` of the expansion for this
functional. -/
theorem classE_analyticOnNhd_xiCRaw_of_isSF2 {j : ℕ} (h1 : 1 ≤ j) (hjk : j ≤ k)
    (y : CTorus d L N₁ m₁ (k + 1)) {X : Set (CTorus d L N₁ m₁ (k + 1))}
    (hX : IsPolyDom C.m₀ j X) (hy : y ∈ X) {ε₂ : ℝ} (hε : scaledC0 d ^ 2 * ε₂ ≤ P.eps d L j)
    (cst : ℂ) :
    AnalyticOnNhd ℂ (fun raw : RawData d L (N₁ * L ^ m₁) (k + 1) N =>
        cst * C.Tm.E j y X raw.1 raw.2)
      (XiCRaw (C.Tm.gs j X) S.a S.ν j (scaledC0 d) ε₂) :=
  classE_analyticOnNhd_xiCRaw_of_isSF2_of_one_le hm h (one_le_scaledC0 d) h1 hjk y hX hy hε cst

include hm h in
/-- **The energy term of a member of the class is bounded on a chart `Ξ^c_j(C.Tm.gs j X; σ, ε₂)`,
`σ ≥ 1`**: if `σ² ε₂ ≤ ε_j`, then `‖ℰ^{(j)}(y, X; Ψ, h)‖ ≤ E₀ e^{-κ d_j(X)}` there. -/
theorem classE_norm_le_xiCRaw_of_isSF2_of_one_le {σ : ℝ} (hσ : 1 ≤ σ) {j : ℕ} (h1 : 1 ≤ j)
    (hjk : j ≤ k)
    (y : CTorus d L N₁ m₁ (k + 1)) {X : Set (CTorus d L N₁ m₁ (k + 1))}
    (hX : IsPolyDom C.m₀ j X) (hy : y ∈ X) {ε₂ : ℝ} (hε : σ ^ 2 * ε₂ ≤ P.eps d L j) :
    ∀ r ∈ XiCRaw (C.Tm.gs j X) S.a S.ν j σ ε₂,
      ‖C.Tm.E j y X r.1 r.2‖ ≤ P.E₀ * Real.exp (-P.κ * sizeJ P.m₀ j X) := by
  rintro r ⟨D, hD, rfl⟩
  have hx : XiDom (C.Tm.gs j X) S.a S.ν j (P.eps d L j) D.Ψ D.h :=
    xiDom_of_xiCData_of_one_le hσ hε hD
  obtain ⟨hm0, hmT, hmW, hmν⟩ := hm
  subst hmT
  rw [hmW, hmν] at hx
  exact h.terms.boundE j h1 (hjk.trans (Nat.le_succ k)) y X (hm0 ▸ hX) hy D.Ψ D.h hx

include hm h in
/-- **The energy term of a member of the class is bounded on the chart of the expansion**: if
`C₀² ε₂ ≤ ε_j`, then `‖ℰ^{(j)}(y, X; Ψ, h)‖ ≤ E₀ e^{-κ d_j(X)}` on `Ξ^c_j(C.Tm.gs j X; C₀, ε₂)`
(the clause `boundE` of the class). -/
theorem classE_norm_le_xiCRaw_of_isSF2 {j : ℕ} (h1 : 1 ≤ j) (hjk : j ≤ k)
    (y : CTorus d L N₁ m₁ (k + 1)) {X : Set (CTorus d L N₁ m₁ (k + 1))}
    (hX : IsPolyDom C.m₀ j X) (hy : y ∈ X) {ε₂ : ℝ} (hε : scaledC0 d ^ 2 * ε₂ ≤ P.eps d L j) :
    ∀ r ∈ XiCRaw (C.Tm.gs j X) S.a S.ν j (scaledC0 d) ε₂,
      ‖C.Tm.E j y X r.1 r.2‖ ≤ P.E₀ * Real.exp (-P.κ * sizeJ P.m₀ j X) :=
  classE_norm_le_xiCRaw_of_isSF2_of_one_le hm h (one_le_scaledC0 d) h1 hjk y hX hy hε

include hm h in
/-- **A component of the observable term of a member of the class is analytic on a chart
`Ξ^c_j(C.Tm.gs j X; σ, ε₂)`, `σ ≥ 1`**, at a fixed source `g` with `‖g‖₁ < 1`, if
`σ² ε₂ ≤ ε_j`. -/
theorem classM_analyticOnNhd_xiCRaw_of_isSF2_of_one_le {σ : ℝ} (hσ : 1 ≤ σ) {j : ℕ} (h1 : 1 ≤ j)
    (hjk : j ≤ k)
    (x : CTorus d L N₁ m₁ (k + 1)) {X : Set (CTorus d L N₁ m₁ (k + 1))}
    (hX : IsPolyDom C.m₀ j X) (hx : x ∈ X) {ε₂ : ℝ} (hε : σ ^ 2 * ε₂ ≤ P.eps d L j)
    {g : Fld d L N₁ m₁ (k + 1) N} (hg : l1 g < 1) (i : Fin N) :
    AnalyticOnNhd ℂ (fun raw : RawData d L (N₁ * L ^ m₁) (k + 1) N =>
        C.Tm.M j x X raw.1 raw.2 g i)
      (XiCRaw (C.Tm.gs j X) S.a S.ν j σ ε₂) := by
  have hT := stepTermsAnalytic_of_isSF2_step hm h
  rintro p ⟨D, hD, rfl⟩
  have h3 := hT.analyticM j h1 hjk x X hX hx (D.Ψ, D.h, g)
    ⟨xiDom_of_xiCData_of_one_le hσ hε hD, hg⟩
  have hmap : AnalyticAt ℂ (fun raw : RawData d L (N₁ * L ^ m₁) (k + 1) N =>
      (raw.1, raw.2, g)) (rawOf D) :=
    AnalyticAt.prod analyticAt_fst (AnalyticAt.prod analyticAt_snd analyticAt_const)
  exact ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N => ℂ) i).analyticAt _).comp
    (h3.comp_of_eq hmap rfl)

include hm h in
/-- **A component of the observable term of a member of the class is analytic on the chart of the
expansion**, at a fixed source `g` with `‖g‖₁ < 1`: if `C₀² ε₂ ≤ ε_j`, the functional
`(Ψ, h) ↦ ℳ^{(j)}(x, X; Ψ, h, g)_i` is analytic at every point of `Ξ^c_j(C.Tm.gs j X; C₀, ε₂)`.
This is the hypothesis `hEanM` of the expansion for this functional. -/
theorem classM_analyticOnNhd_xiCRaw_of_isSF2 {j : ℕ} (h1 : 1 ≤ j) (hjk : j ≤ k)
    (x : CTorus d L N₁ m₁ (k + 1)) {X : Set (CTorus d L N₁ m₁ (k + 1))}
    (hX : IsPolyDom C.m₀ j X) (hx : x ∈ X) {ε₂ : ℝ} (hε : scaledC0 d ^ 2 * ε₂ ≤ P.eps d L j)
    {g : Fld d L N₁ m₁ (k + 1) N} (hg : l1 g < 1) (i : Fin N) :
    AnalyticOnNhd ℂ (fun raw : RawData d L (N₁ * L ^ m₁) (k + 1) N =>
        C.Tm.M j x X raw.1 raw.2 g i)
      (XiCRaw (C.Tm.gs j X) S.a S.ν j (scaledC0 d) ε₂) :=
  classM_analyticOnNhd_xiCRaw_of_isSF2_of_one_le hm h (one_le_scaledC0 d) h1 hjk x hX hx hε hg i

end Class

end Balaban.Fluctuation
