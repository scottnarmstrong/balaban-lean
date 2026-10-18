/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.XiCRawOpenWitness
public import Balaban.Fluctuation.CriticalPoint

/-!
# Zero truncation does not land in the step chart (`StepTowerLocalTruncZero`)

The step chart is the chart `Ξ^c_{k+1}(𝔹_{k+1}; 1, ε)` of a whole-lattice generating set
(`IsLevel G (k + 1)`): its first layer is the whole torus, so

* `clipRaw_of_isLevel`: `clipRaw G` is the identity there: the cut-off of `clipRaw` is the cut-off
  to the data sites of `G`, which is no truncation at all;
* `xiC_h_zero_obstruction`, `not_xiC_h_zero`: a datum of the chart has `h = h₀ + h''` at every
  site, with `ν ℓ² vn(h'') < ε` (`hAbs`) and `ν L^{2n} |‖h₀‖² - 1| < ε²` (`hnorm`).  If `h''`
  cancels `h₀` at one site, that is, if the raw datum vanishes there, then `ν ℓ² ‖h₀‖ < ε`; for
  `ε ≤ 1/2` and `ν L^{2n} ≥ 2ε` this contradicts `‖h₀‖² > 1 - ε`.  Hence a raw datum cut to zero
  outside a polymer is not in the step chart at radius `ε` in the massive range
  `ν L^{2(k+1)} ≥ 2ε`.  The truncation of the local chart to the step chart has to cut the complex
  displacement and keep a real extension, not cut the raw datum.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Multiscale Balaban.Background Balaban.SmallField
  Balaban.SmallField.Def6

section Zero

variable {d L N₁ m₁ K N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- **`clipRaw` of a whole-lattice generating set is the identity.** -/
theorem clipRaw_of_isLevel {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {n : ℕ}
    (hG : IsLevel G n) (r : Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N) : clipRaw G r = r := by
  classical
  have h1 : ∀ x, x ∈ dataSites G := fun x => (mem_dataSites G).2 (Or.inl (hG x).1)
  have h2 : ∀ x, x ∈ G.Ω 1 := fun x => (hG x).1
  refine Prod.ext (funext fun x => funext fun i => ?_) (funext fun x => funext fun i => ?_)
  · simp [clipRaw, h1 x]
  · simp [clipRaw, h2 x]

/-- **A datum of the step chart whose raw `h` vanishes at a site.**  If `h''` cancels `h₀` at a site,
then `ν ℓ² ‖h₀‖ < σ² ε` and `ν L^{2n} |‖h₀‖² - 1| < (σ ε)²`. -/
theorem xiC_h_zero_obstruction {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {n : ℕ}
    (hG : IsLevel G n) {a : ℕ → ℝ} {ν σ ε : ℝ}
    {Ψ₀ : CTorus d L N₁ m₁ K → Fin N → ℝ} {h₀ : Fin N → ℝ}
    {Ψ'' h'' : CTorus d L N₁ m₁ K → Fin N → ℂ}
    (hx : XiC G a ν n σ ε Ψ₀ h₀ Ψ'' h'') (z : CTorus d L N₁ m₁ K)
    (hz : h'' z = fun i => -((h₀ i : ℝ) : ℂ)) :
    ν * ((L : ℝ) ^ n) ^ 2 * vn (fun i => ((h₀ i : ℝ) : ℂ)) < σ ^ 2 * ε ∧
      ν * ((L : ℝ) ^ n) ^ 2 * |∑ i, h₀ i ^ 2 - 1| < (σ * ε) ^ 2 := by
  obtain ⟨-, hε, Dr, Dc, hXi, -, -, hB⟩ := hx
  have h1 := hB.hAbs z (hG z).1
  rw [(hG z).2, hz] at h1
  have hneg : vn (fun i => -((h₀ i : ℝ) : ℂ)) = vn (fun i => ((h₀ i : ℝ) : ℂ)) := by
    rw [vn_eq_sqrt, vn_eq_sqrt]
    simp only [norm_neg]
  rw [hneg] at h1
  refine ⟨?_, hXi.2.2.hnorm⟩
  have : (σ * ε) ^ 2 / ε = σ ^ 2 * ε := by field_simp
  rwa [this] at h1

/-- **No datum of the massive step chart vanishes at a site.**  For `σ = 1`, `ε ≤ 1/2` and
`2 ε ≤ ν L^{2n}`, a datum of `Ξ^c_n(𝔹; 1, ε)` of a whole-lattice generating set of level `n` has
no site at which `h''` cancels `h₀`, that is, at which the raw `h` is zero. -/
theorem not_xiC_h_zero {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {n : ℕ}
    (hG : IsLevel G n) {a : ℕ → ℝ} {ν ε : ℝ} (hε : ε ≤ 1 / 2)
    (hmass : 2 * ε ≤ ν * ((L : ℝ) ^ n) ^ 2)
    {Ψ₀ : CTorus d L N₁ m₁ K → Fin N → ℝ} {h₀ : Fin N → ℝ}
    {Ψ'' h'' : CTorus d L N₁ m₁ K → Fin N → ℂ}
    (hx : XiC G a ν n 1 ε Ψ₀ h₀ Ψ'' h'') (z : CTorus d L N₁ m₁ K) :
    h'' z ≠ fun i => -((h₀ i : ℝ) : ℂ) := by
  intro hz
  obtain ⟨h1, h2⟩ := xiC_h_zero_obstruction hG hx z hz
  have hε0 : 0 < ε := hx.2.1
  set A := ν * ((L : ℝ) ^ n) ^ 2 with hA
  have hA0 : 0 < A := by linarith
  set S := ∑ i, h₀ i ^ 2 with hS
  have hvn : vn (fun i => ((h₀ i : ℝ) : ℂ)) ^ 2 = S := by
    rw [vn_sq, hS]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hv0 := vn_nonneg (fun i => ((h₀ i : ℝ) : ℂ))
  set v := vn (fun i => ((h₀ i : ℝ) : ℂ))
  have e1 : v < ε / A := by rw [lt_div_iff₀ hA0]; nlinarith
  have e2 : v < 1 / 2 := by
    refine e1.trans_le ?_
    rw [div_le_iff₀ hA0]; nlinarith
  have e3 : S < 1 / 4 := by nlinarith
  have e4 : A * (1 - S) < ε ^ 2 := by
    have := (abs_lt.1 (show |S - 1| < ε ^ 2 / A by
      rw [lt_div_iff₀ hA0]; nlinarith [h2])).1
    rw [lt_div_iff₀ hA0] at *
    nlinarith [h2, abs_nonneg (S - 1), neg_abs_le (S - 1)]
  nlinarith

end Zero

end Balaban.Fluctuation
