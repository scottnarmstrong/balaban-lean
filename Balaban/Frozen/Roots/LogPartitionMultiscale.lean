module

public import Balaban.Frozen.Model.PartitionFunction
public import Balaban.Frozen.Geometry.IsPolymer
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Data.ZMod.ValMinAbs
import Balaban.Provider.LogPartitionMultiscale

/-!
# Root-F: the renormalization-group flow, observable form

The generating functional of the hard-spin `O(N)` model at low temperature has Balaban's
multiscale representation, with bounds uniform in the external field `ν ∈ (0, 1]` and in the
volume: P7 (4.15)–(4.17) (p. 533) with P4 (H.4), (H.6)–(H.7) (pp. 677–679) and P9 (4.4)–(4.7)
(p. 516). There is `δ > 0` such that for every `κ` and `c₉` there are `L, M, β₀` such that for
`β ≥ β₀`:

* `log (Z(g)/Z(0)) = ⟨g, h⟩ + ∑_{j=1}^{k_f+1} ∑_x ∑_{X ∋ x} ⟨g(x), T_j(x, X; g)⟩` on every torus
  whose side is divisible by `M L^{k_f+1}`, for some `k_f` with `L^{k_f} √ν ≤ L` and
  `1/2 ≤ L^{k_f+1} √ν` (in the proof, the number of renormalization steps before the last one);
* `T_j(x, X; ·)` vanishes unless `X` is a scale-`j` polymer containing `x`, depends only on
  `g|_X`, is analytic on `∑_x ∑_i |g_i(x)| < 1`, and on `∑_x ∑_i |g_i(x)| ≤ 1/2` is bounded by
  `c₉ L^{-j((d-2)/2 + δ)} exp(-κ |X| / (M L^j)^d)`;
* the terms of two admissible tori of sides `ℓ, ℓ'` agree on the images of a finite set
  `A ⊂ ℤ^d` contained in the box `|y_μ| < min(ℓ, ℓ')/4`: a special case of the independence of
  the torus for polymers that do not wind around it (P4 (H.4), p. 677).

The scale-`k_f+1` terms collect P7's `ℳ_n^{(k_f+1)}`, `n = 0, …, m`, and the large-field polymer
terms `𝒫^{(k_f+1)}` of P9 (4.4)–(4.6). Decision record: `notes/phase0/surface-v1-for-approval.md`.
-/

-- FROZEN_ANCHOR_PREFIX_BEGIN
@[expose] public section

namespace Balaban

/-- Root-F (main deliverable): the full renormalization-group flow, with large fields, in
observable form. -/
theorem logPartition_multiscale (d N : ℕ) (hd : 3 ≤ d) (hN : 2 ≤ N) :
    ∃ δ : ℝ, 0 < δ ∧
    ∀ κ : ℝ, 0 < κ → ∀ c₉ : ℝ, 0 < c₉ →
    ∃ L M : ℕ, 2 ≤ L ∧ 1 ≤ M ∧ ∃ β₀ : ℝ, ∀ β : ℝ, β₀ ≤ β →
    ∀ ν : ℝ, 0 < ν → ν ≤ 1 → ∀ h : EuclideanSpace ℝ (Fin N), ‖h‖ = 1 →
    ∃ kf : ℕ, (L : ℝ) ^ kf * Real.sqrt ν ≤ L ∧ 1 / 2 ≤ (L : ℝ) ^ (kf + 1) * Real.sqrt ν ∧
    ∃ T : (ℓ : ℕ) → ℕ → Torus d ℓ → Finset (Torus d ℓ) → (Torus d ℓ → Fin N → ℂ) →
        (Fin N → ℂ),
      (∀ (ℓ : ℕ) [NeZero ℓ], M * L ^ (kf + 1) ∣ ℓ →
        (∀ j x X, ¬ (j ∈ Finset.Icc 1 (kf + 1) ∧ x ∈ X ∧ IsPolymer d ℓ (M * L ^ j) X) →
          T ℓ j x X = 0) ∧
        (∀ j x X (g g' : Torus d ℓ → Fin N → ℂ), (∀ y ∈ X, g y = g' y) →
          T ℓ j x X g = T ℓ j x X g') ∧
        (∀ j x X, AnalyticOnNhd ℂ (T ℓ j x X) {g | ∑ y, ∑ i, ‖g y i‖ < 1}) ∧
        (∀ j ∈ Finset.Icc 1 (kf + 1), ∀ x X (g : Torus d ℓ → Fin N → ℂ),
          ∑ y, ∑ i, ‖g y i‖ ≤ 1 / 2 →
          ‖T ℓ j x X g‖ ≤ c₉ * (L : ℝ) ^ (-((j : ℝ) * (((d : ℝ) - 2) / 2 + δ)))
            * Real.exp (-κ * (X.card : ℝ) / ((M : ℝ) * (L : ℝ) ^ j) ^ d)) ∧
        ∀ g : Torus d ℓ → Fin N → ℂ, ∑ y, ∑ i, ‖g y i‖ < 1 →
          Complex.log (partitionFunction d N ℓ β ν h g / partitionFunction d N ℓ β ν h 0) =
            ∑ x, ∑ i, g x i * (h i : ℂ)
              + ∑ j ∈ Finset.Icc 1 (kf + 1), ∑ x, ∑ X : Finset (Torus d ℓ), ∑ i,
                  g x i * T ℓ j x X g i) ∧
      ∀ (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ'], M * L ^ (kf + 1) ∣ ℓ → M * L ^ (kf + 1) ∣ ℓ' →
        ∀ (j : ℕ) (a : Fin d → ℤ) (A : Finset (Fin d → ℤ)) (g : (Fin d → ℤ) → Fin N → ℂ),
          a ∈ A → (∀ y ∈ A, ∀ μ, 4 * |y μ| < (ℓ : ℤ) ∧ 4 * |y μ| < (ℓ' : ℤ)) →
          T ℓ j (fun μ => (a μ : ZMod ℓ)) (A.image fun y μ => (y μ : ZMod ℓ))
              (fun z => g fun μ => ZMod.valMinAbs (n := ℓ) (z μ)) =
            T ℓ' j (fun μ => (a μ : ZMod ℓ')) (A.image fun y μ => (y μ : ZMod ℓ'))
              (fun z => g fun μ => ZMod.valMinAbs (n := ℓ') (z μ)) :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by sorry
  -- FROZEN_ANCHOR_PROOF_END

-- FROZEN_ANCHOR_SUFFIX_BEGIN
end Balaban
-- FROZEN_ANCHOR_SUFFIX_END
