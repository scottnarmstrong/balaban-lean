/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RRemovedHidGaussEqNodes

/-!
# The integral of the unrolled Gaussian product over the free nodes (W923)

`notes/phase1/LF4R-PLAN.md`, leaf 6, blocker 4, item (d).  `lintegral_gauss_unrolled`: integrating the free
nodes (the nodes outside `Fx`, the others being fixed roots with prescribed values) in the unrolled Gaussian
product gives at most the product of the suprema `(c_{s-1} z_s² / 2π)^{N/2}` of the densities of the fixed
roots, for any values of the leaves.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open MeasureTheory Balaban Balaban.Multiscale RegionHistory

section GaussMain

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {H : RegionHistory S n R k0 K}

open Classical in
/-- **(d) The integral of the unrolled Gaussian product over the free nodes.**  The nodes of the forest
of the Gaussian blocks of the window (`nd`, `pa`) outside `Fx` are integrated (`Ψ`), those in `Fx` are fixed
roots with the values `u`.  The fields are read as follows: at the blocks that are not nodes (the leaves
and the other blocks) the field is `fldb`, whatever `Ψ`; at a node it is `u` or the integration variable
`Ψ`.  The integral of the product of the Gaussian factors of `gaussProd_unroll_eq` (top step and steps
`k₁ ≤ j < m'`) is at most the product, over the fixed roots, of the suprema `(c_{s-1} z_s² / 2π)^{N/2}` of
their densities; the free roots integrate to `1`. -/
theorem lintegral_gauss_unrolled {k1 m' : ℕ} (hk1 : k1 ≤ m') (hm : m' + 1 ≤ K) (Z : H.Comp (m' + 1))
    (nd : (Σ s, BlockAt S n M K s) → Prop)
    (hnd : ∀ j (y : BlockAt S n M K (j + 1)), nd ⟨j + 1, y⟩ ↔ (k1 ≤ j ∧ j ≤ m' ∧
      ∃ c ∈ H.ancFin (j + 1) (m' + 1) Z, y ∈ gaussBlocks (H.localHistory M K (j + 1) c) j))
    (hnd0 : ∀ y : BlockAt S n M K 0, ¬ nd ⟨0, y⟩)
    [Fintype {b : Σ s, BlockAt S n M K s // nd b}]
    [Fintype {q : (Σ s, BlockAt S n M K s) × {b : Σ s, BlockAt S n M K s // nd b} //
      (⟨q.1.1 + 1, blockMap S.L (M * n K * S.L ^ (K - (q.1.1 + 1))) q.1.2⟩ :
        Σ s, BlockAt S n M K s) = q.2.1 ∧ ¬ nd q.1}]
    (pa : {b : Σ s, BlockAt S n M K s // nd b} → {b : Σ s, BlockAt S n M K s // nd b})
    (hpa : ∀ b : {b : Σ s, BlockAt S n M K s // nd b},
      (nd ⟨b.1.1 + 1, blockMap S.L (M * n K * S.L ^ (K - (b.1.1 + 1))) b.1.2⟩ ∧ b.1.1 + 1 ≤ m' + 1 →
        (pa b).1 = ⟨b.1.1 + 1, blockMap S.L (M * n K * S.L ^ (K - (b.1.1 + 1))) b.1.2⟩) ∧
      (¬ (nd ⟨b.1.1 + 1, blockMap S.L (M * n K * S.L ^ (K - (b.1.1 + 1))) b.1.2⟩ ∧
        b.1.1 + 1 ≤ m' + 1) → pa b = b))
    (c z : ℕ → ℝ) (hc : ∀ j, k1 ≤ j → j < m' + 1 → 0 < c j)
    (hz : ∀ s, k1 < s → s ≤ m' + 1 → 0 < z s)
    (Fx : {b : Σ s, BlockAt S n M K s // nd b} → Prop) [DecidablePred Fx]
    (hFx : ∀ i, Fx i → pa i = i)
    (u : {b : Σ s, BlockAt S n M K s // nd b} → EuclideanSpace ℝ (Fin N))
    (fldb : ∀ s, BlockAt S n M K s → EuclideanSpace ℝ (Fin N))
    (fld : ({i : {b : Σ s, BlockAt S n M K s // nd b} // ¬ Fx i} → EuclideanSpace ℝ (Fin N)) →
      ∀ s, BlockAt S n M K s → EuclideanSpace ℝ (Fin N))
    (ft : ({i : {b : Σ s, BlockAt S n M K s // nd b} // ¬ Fx i} → EuclideanSpace ℝ (Fin N)) →
      BlockAt S n M K (m' + 1) → EuclideanSpace ℝ (Fin N))
    (hfldb : ∀ Ψ s y, ¬ nd ⟨s, y⟩ → fld Ψ s y = fldb s y)
    (hfldn : ∀ Ψ j y (h : nd ⟨j + 1, y⟩), j + 1 ≤ m' → fld Ψ (j + 1) y =
      if hF : Fx ⟨⟨j + 1, y⟩, h⟩ then u ⟨⟨j + 1, y⟩, h⟩ else Ψ ⟨⟨⟨j + 1, y⟩, h⟩, hF⟩)
    (hft : ∀ Ψ y (h : nd ⟨m' + 1, y⟩), ft Ψ y =
      if hF : Fx ⟨⟨m' + 1, y⟩, h⟩ then u ⟨⟨m' + 1, y⟩, h⟩ else Ψ ⟨⟨⟨m' + 1, y⟩, h⟩, hF⟩) :
    ∫⁻ Ψ : {i : {b : Σ s, BlockAt S n M K s // nd b} // ¬ Fx i} → EuclideanSpace ℝ (Fin N),
      ENNReal.ofReal
        ((∏ y ∈ Finset.univ.filter (fun y : BlockAt S n M K (m' + 1) =>
            ∃ c' ∈ H.ancFin (m' + 1) (m' + 1) Z,
              y ∈ gaussBlocks (H.localHistory M K (m' + 1) c') m'),
          z (m' + 1) ^ N * gaussDens (c m')
            (z (m' + 1) • ft Ψ y - ((S.L : ℝ) ^ S.d)⁻¹ •
              ∑ y' ∈ Finset.univ.filter (fun y' : BlockAt S n M K m' =>
                blockMap S.L (M * n K * S.L ^ (K - (m' + 1))) y' = y), fld Ψ m' y')) *
        ∏ j ∈ Finset.Ico k1 m',
          ∏ y ∈ Finset.univ.filter (fun y : BlockAt S n M K (j + 1) =>
              ∃ c' ∈ H.ancFin (j + 1) (m' + 1) Z,
                y ∈ gaussBlocks (H.localHistory M K (j + 1) c') j),
            z (j + 1) ^ N * gaussDens (c j)
              (z (j + 1) • fld Ψ (j + 1) y - ((S.L : ℝ) ^ S.d)⁻¹ •
                ∑ y' ∈ Finset.univ.filter (fun y' : BlockAt S n M K j =>
                  blockMap S.L (M * n K * S.L ^ (K - (j + 1))) y' = y), fld Ψ j y'))
      ∂(Measure.pi fun _ => (volume : Measure (EuclideanSpace ℝ (Fin N)))) ≤
    ∏ r ∈ Finset.univ.filter (fun r : {b : Σ s, BlockAt S n M K s // nd b} => pa r = r ∧ Fx r),
      ENNReal.ofReal ((c (r.1.1 - 1) * z r.1.1 ^ 2 / (2 * Real.pi)) ^ ((N : ℝ) / 2)) := by
  classical
  obtain ⟨B, e, el, -, -, -, hE⟩ := lintegral_gauss_unrolled_eq hk1 hm Z nd hnd hnd0 pa hpa c z hc hz Fx hFx
    u fldb fld ft hfldb hfldn hft
  rw [hE]
  obtain ⟨g1, g2, g3, g4⟩ := gauss_forest_data (H := H) Z nd hnd hnd0 hm pa hpa
  exact prod_forest_eq_le (m := S.L ^ S.d) (k1 := k1) (top := m' + 1) (N := N)
    (fun i : {b : Σ s, BlockAt S n M K s // nd b} => i.1.1) pa (by have := NeZero.pos S.L; positivity)
    g3 c z hc hz Fx B _

end GaussMain

end Balaban.LargeField
