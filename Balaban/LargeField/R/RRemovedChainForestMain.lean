/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RRemovedHidGaussEqForest

/-!
# The Gaussian integral over the free nodes of a forest: the bound (W923)

`notes/phase1/LF4R-PLAN.md`, leaf 6, blocker 4, item (4).  `lintegral_forest_nodes`: in a finite forest with
`m` children at every node, with the nodes of a set `Fx` of roots fixed at `u`, the integral over the other
nodes of the product of the Gaussian factors is at most `∏_{r ∈ Fx} (c_{s_r-1} z_{s_r}² / 2π)^{N/2}` (the
free roots integrate to `1`), whatever the leaf values.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open MeasureTheory

section ForestMain

variable {m k1 top N : ℕ} {ι Lf : Type} [Fintype ι] [DecidableEq ι] [Fintype Lf]
  (sc : ι → ℕ) (pa : ι → ι) (lp : Lf → ι)

/-- **(d) The Gaussian integral over the free nodes of a forest** (the fixed roots are the nodes of `Fx`,
with values `u`): `ext Ψ` is the full node configuration (`u` on `Fx`, `Ψ` elsewhere), and the integral
over `Ψ` of the product of the Gaussian factors is at most the product, over the roots in `Fx`, of the
suprema `(c_{s-1} z_s² / 2π)^{N/2}` of the top Gaussian density.  It does not depend on the leaf values
`Ψl`. -/
theorem lintegral_forest_nodes (hpa : ∀ i, pa i ≠ i → sc (pa i) = sc i + 1)
    (hge : ∀ i, k1 + 1 ≤ sc i)
    (hfull : ∀ i, (Finset.univ.filter fun c => pa c ≠ c ∧ pa c = i).card +
      (Finset.univ.filter fun l => lp l = i).card = m)
    (hm : 0 < m) (htop : ∀ i, sc i ≤ top) (c z : ℕ → ℝ)
    (hc : ∀ j, k1 ≤ j → j < top → 0 < c j) (hz : ∀ s, k1 < s → s ≤ top → 0 < z s)
    (Fx : ι → Prop) [DecidablePred Fx] (hFx : ∀ i, Fx i → pa i = i)
    (u : ι → EuclideanSpace ℝ (Fin N)) (Ψl : Lf → EuclideanSpace ℝ (Fin N))
    (ext : ({i // ¬ Fx i} → EuclideanSpace ℝ (Fin N)) → ι → EuclideanSpace ℝ (Fin N))
    (hext : ∀ Ψ i, ext Ψ i = if h : Fx i then u i else Ψ ⟨i, h⟩) :
    ∫⁻ Ψ : {i // ¬ Fx i} → EuclideanSpace ℝ (Fin N), ENNReal.ofReal
        (∏ i : ι, z (sc i) ^ Module.finrank ℝ (EuclideanSpace ℝ (Fin N)) *
          gaussDens (c (sc i - 1)) (z (sc i) • ext Ψ i - (m : ℝ)⁻¹ •
            ((∑ j ∈ Finset.univ.filter (fun j : ι => pa j ≠ j ∧ pa j = i), ext Ψ j) +
              ∑ l ∈ Finset.univ.filter (fun l : Lf => lp l = i), Ψl l)))
      ∂(Measure.pi fun _ : {i // ¬ Fx i} => (volume : Measure (EuclideanSpace ℝ (Fin N)))) ≤
    ∏ r ∈ Finset.univ.filter (fun r : ι => pa r = r ∧ Fx r),
      ENNReal.ofReal ((c (sc r - 1) * z (sc r) ^ 2 / (2 * Real.pi)) ^ ((N : ℝ) / 2)) := by
  classical
  obtain ⟨B, e, el, he0, hsc, hpar, hleaf, heq⟩ := lintegral_forest_nodes_eq (m := m) (k1 := k1) sc pa lp hpa
    hge hfull hm htop c z hc hz Fx hFx u Ψl ext hext
  rw [heq]
  exact prod_forest_eq_le sc pa hm htop c z hc hz Fx B (fun r => u r.1 -
    (B r).composedMean z (fun x => Ψl ((el r).symm x).1))

end ForestMain

end Balaban.LargeField
