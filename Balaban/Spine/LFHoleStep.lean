/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Background.HoleStepSets
public import Balaban.LargeField.Characteristic.Analytic
public import Balaban.LargeField.Operators.Setup
import Mathlib.Tactic.Linarith

/-!
# The step on a region of a history, on the multiscale fields of Def-7

The step `k → k + 1` of a history `H` (`RegionHistory`, horizon `K`, block sides `n`) on the
multiscale fields `ψ` (`MultiFieldC`, the arguments of the boundary terms): the step on a region
(`Fluctuation.HoleStep`, `LargeField.holeStepOf`) of the region step `H.step k` with the old field
`ψ_k` and the block variable `θ = ψ_{k+1}` read from `ψ`, and the multiscale field of scale `k` at
which the old boundary terms `ℬ^{(k)}(X)` are evaluated in the fluctuation integral (P5 (2.48),
P6 (4.32)): `ψ_k` replaced on the blocks of `Ω_{k+1}` by the composed field of P5 (2.39).

* `coverScale_eq`: the cover torus of the step (side `(c n_{k+1}) L^{m₁} L^{k+1}`, `M₁ = L^{m₁}`) is the
  fine torus of the history, in blocks of every side `L^i`, `i ≤ k + 1`;
* `coverField`: the component `ψ_i` of a multiscale field as a field on the blocks of the cover torus;
* `holeStepLF`: the step on a region of the history at the multiscale field `ψ`;
* `unitOfBlock`, `composedMulti`: the multiscale field of scale `k` with the field `comp` on the
  unit points of `Ω_{k+1}` (the composed field, `Fluctuation.HoleStep.composed`), `ψ_j` at the
  scales `j < k`, `ψ_k` on the other blocks, `0` above `k`; `composedMulti_of_lt`,
  `composedMulti_in`, `composedMulti_out`, `composedMulti_of_gt`;
* `oldFluct`: the fluctuation field of the multi-index of scale `k` (the components `j < k`).
-/

@[expose] public section

namespace Balaban.RootFSpine

open Balaban Balaban.LargeField Balaban.Multiscale Balaban.Localization Balaban.Fluctuation

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {N m₁ : ℕ}

omit [NeZero M] in
/-- **The cover torus of the step is the fine torus of the history**: in blocks of side `L^i`,
`i ≤ k + 1`, `(c n_{k+1}) L^{m₁} L^{k+1-i} = M n_K L^{K-i}` (`M = c M₁`, `M₁ = L^{m₁}`). -/
theorem coverScale_eq (g : Geo S n R M) (hnn : ∀ i, i < K → n i = S.L * n (i + 1))
    (hM1 : g.M1 = S.L ^ m₁) {k i : ℕ} (hi : i ≤ k + 1) (hk : k + 1 ≤ K) :
    (g.c * n (k + 1)) * S.L ^ m₁ * S.L ^ (k + 1 - i) = M * n K * S.L ^ (K - i) := by
  rw [← p6_side hM1]
  exact histScale_eq g.hM hnn hi hk

/-- **The component `ψ_i` of a multiscale field on the blocks of the cover torus** of the step. -/
def coverField (g : Geo S n R M) (hnn : ∀ i, i < K → n i = S.L * n (i + 1))
    (hM1 : g.M1 = S.L ^ m₁) {k : ℕ} (hk : k + 1 ≤ K) (ψ : MultiFieldC S n M K N) (i : ℕ)
    (hi : i ≤ k + 1) :
    Torus S.d ((g.c * n (k + 1)) * S.L ^ m₁ * S.L ^ (k + 1 - i)) → Fin N → ℂ :=
  fun z => ψ i (torusCast (coverScale_eq g hnn hM1 hi hk) z)

variable (g : Geo S n R M) (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) (hM1 : g.M1 = S.L ^ m₁)

/-- **The step on a region of the history `H` at the multiscale field `ψ`** (P5 (2.16)–(2.20)): the
step on a region of the region step `H.step k` (`holeStepOf`) with the old field `ψ_k` and the block
variable `θ = ψ_{k+1}` of `ψ`, the field `h₀` and the constants `a₁, ν, β, p₁, δ`.  The premises are
the separation `3 L ≤ ⌊R_{k-1}⌋` of the old operator set and `1 ≤ k`. -/
noncomputable def holeStepLF (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K) (hk1 : 1 ≤ k)
    (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (ψ : MultiFieldC S n M K N) (h₀ : Fin N → ℝ)
    (a₁ ν β p₁ δ : ℝ) :
    HoleStep S.d S.L (g.c * n (k + 1)) m₁ k N (minSep S.L g.M1) (minSep S.L g.M1) :=
  holeStepOf (H.step k) hM1 (hnn k (by omega)) hρ (by have := g.hc; omega) hk1
    (coverField g hnn hM1 hk ψ k (Nat.le_succ k)) (coverField g hnn hM1 hk ψ (k + 1) le_rfl) h₀
    a₁ ν β p₁ δ

/-- The unit block (side `L^k` of the cover torus) of a block of side `L^k` of the history torus. -/
def unitOfBlock {k : ℕ} (hk : k + 1 ≤ K) (y : Torus S.d (M * n K * S.L ^ (K - k))) :
    UnitTorus S.d S.L (g.c * n (k + 1)) m₁ k :=
  torusCast (coverScale_eq g hnn hM1 (Nat.le_succ k) hk).symm y

open Classical in
/-- **The multiscale field of scale `k` of the fluctuation integral** (P5 (2.48), P6 (4.32)): the
field `comp` on the blocks of side `L^k` whose unit block is a unit point of the top layer of the
generating set `G'` (the blocks of `Ω_{k+1}`; `comp` is the composed field of P5 (2.39)), `ψ_k` on
the other blocks of side `L^k`, `ψ_j` at the scales `j < k`, and `0` above `k` (the multiscale field
of a multi-index of scale `k`, `gMulti`). -/
noncomputable def composedMulti {k : ℕ} (hk : k + 1 ≤ K) {ϱ' : ℝ}
    (G' : GeneratingSet S.d S.L ((g.c * n (k + 1)) * S.L ^ m₁) (k + 1) ϱ')
    (ψ : MultiFieldC S n M K N) (comp : unitPts G' → Fin N → ℂ) : MultiFieldC S n M K N :=
  fun j y =>
    if j < k then ψ j y
    else if hj : j = k then
      (if h : unitOfBlock g hnn hM1 hk (hj ▸ y) ∈ unitPts G' then
        comp ⟨unitOfBlock g hnn hM1 hk (hj ▸ y), h⟩ else ψ j y)
    else 0

variable {g hnn hM1}

omit [NeZero M] in
theorem composedMulti_of_lt {k : ℕ} (hk : k + 1 ≤ K) {ϱ' : ℝ}
    (G' : GeneratingSet S.d S.L ((g.c * n (k + 1)) * S.L ^ m₁) (k + 1) ϱ')
    (ψ : MultiFieldC S n M K N) (comp : unitPts G' → Fin N → ℂ) {j : ℕ} (hj : j < k)
    (y : Torus S.d (M * n K * S.L ^ (K - j))) :
    composedMulti g hnn hM1 hk G' ψ comp j y = ψ j y := by
  simp [composedMulti, hj]

omit [NeZero M] in
theorem composedMulti_of_gt {k : ℕ} (hk : k + 1 ≤ K) {ϱ' : ℝ}
    (G' : GeneratingSet S.d S.L ((g.c * n (k + 1)) * S.L ^ m₁) (k + 1) ϱ')
    (ψ : MultiFieldC S n M K N) (comp : unitPts G' → Fin N → ℂ) {j : ℕ} (hj : k < j)
    (y : Torus S.d (M * n K * S.L ^ (K - j))) :
    composedMulti g hnn hM1 hk G' ψ comp j y = 0 := by
  have h1 : ¬ j < k := by omega
  have h2 : j ≠ k := by omega
  simp [composedMulti, h1, h2]

omit [NeZero M] in
theorem composedMulti_in {k : ℕ} (hk : k + 1 ≤ K) {ϱ' : ℝ}
    (G' : GeneratingSet S.d S.L ((g.c * n (k + 1)) * S.L ^ m₁) (k + 1) ϱ')
    (ψ : MultiFieldC S n M K N) (comp : unitPts G' → Fin N → ℂ)
    (y : Torus S.d (M * n K * S.L ^ (K - k))) (h : unitOfBlock g hnn hM1 hk y ∈ unitPts G') :
    composedMulti g hnn hM1 hk G' ψ comp k y = comp ⟨unitOfBlock g hnn hM1 hk y, h⟩ := by
  simp [composedMulti, h]

omit [NeZero M] in
theorem composedMulti_out {k : ℕ} (hk : k + 1 ≤ K) {ϱ' : ℝ}
    (G' : GeneratingSet S.d S.L ((g.c * n (k + 1)) * S.L ^ m₁) (k + 1) ϱ')
    (ψ : MultiFieldC S n M K N) (comp : unitPts G' → Fin N → ℂ)
    (y : Torus S.d (M * n K * S.L ^ (K - k))) (h : unitOfBlock g hnn hM1 hk y ∉ unitPts G') :
    composedMulti g hnn hM1 hk G' ψ comp k y = ψ k y := by
  simp [composedMulti, h]

/-- **The fluctuation field of the multi-index of scale `k`**: the components `ψ'_j`, `j < k`, of a
fluctuation multi-field (the variables `ψ'_j` of the large-field operators of the old scales), `0`
from `k` on (the fluctuation variables `ψ'_k` of `Ω_{k+1} ∖ Ω''_{k+1}` are variables of the new
large-field operator, not of the old terms). -/
def oldFluct (k : ℕ) (ψ' : MultiFieldC S n M K N) : MultiFieldC S n M K N :=
  fun j y => if j < k then ψ' j y else 0

end Balaban.RootFSpine
