/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.G0Gas

/-!
# G0: first properties of the gas of a kept configuration

* `gasCoupling_empty`: `b_X(∅) = 0` (the hypothesis `hb0` of `decOp_pe_hole`): the old term at the
  empty removal set is the kept term, and `ℬ′_X(∅) = 0` (`rFresh_empty`, the old small-field region
  of the empty removal set is the new one);
* `holeCl_sdiff`: the charged part of a hole closure is the charged part of the set.
-/

@[expose] public section

noncomputable section

open scoped Classical
open Finset Balaban Balaban.LargeField.Def7

namespace Balaban.LargeField.G0

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {N k : ℕ} {geo : Geo S n R M} {cs : OpConsts} {P : BudgetConsts}
  {rep : Rep S n R k0 K M N geo cs P k} {Kc : HistConfig S n R k0 K M k}

/-- **`b_X(∅) = 0`** for the decorated coupling of the gas of a kept configuration. -/
theorem gasCoupling_empty {m₁ : ℕ} {ϱ : ℝ} (C : SFCtx S n R M K N k m₁ ϱ)
    (hv : EuclideanSpace ℝ (Fin N)) (vc : Def7v2.CorrCoef S.d) (pres : RemPres rep)
    (Y : Set (Torus S.d (n k))) (keptT : Finset (Torus S.d (n k)) → BExt S n M K N → ℂ)
    (X : Finset (Torus S.d (n k))) (e : BExt S n M K N) (Φ : ∀ b, pres.Ω b) :
    gasCoupling Kc C hv vc pres Y keptT X ∅ e Φ = 0 := by
  have hYr : (fun Sc' : Finset (RemCl rep Kc) =>
      (Y ∪ ⋃ Cl ∈ Sc', (clCore Cl : Set (Torus S.d (n k))))ᶜ) ∅ = Yᶜ := by
    simp
  unfold gasCoupling r4Coupling gasOld gasFresh
  simp only [↓reduceIte, sub_self, zero_add]
  exact C.rFresh_empty hv vc e.2.2.2 hYr pres.a₁ pres.ν pres.rho (e.1 k) X

omit [NeZero S.L] in
/-- The charged part of the hole closure of a set is the charged part of the set. -/
theorem holeCl_sdiff (S₀ X : Finset (Torus S.d (n k))) :
    holeCl S₀ X \ S₀ = X \ S₀ := by
  ext b
  simp only [holeCl, Finset.mem_sdiff, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
    true_and]
  constructor
  · rintro ⟨hb | ⟨a, -, -, hbc⟩, hb0⟩
    · exact ⟨hb, hb0⟩
    · exact absurd (nnComp_subset _ hbc) hb0
  · rintro ⟨hb, hb0⟩
    exact ⟨Or.inl hb, hb0⟩

end Balaban.LargeField.G0
