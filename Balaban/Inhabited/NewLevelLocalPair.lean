/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalSetDetFlCore
public import Balaban.Fluctuation.LocalPairCast
public import Balaban.Localization.P6PairBaseHat

/-!
# The pair of the local generating set of a label polymer and its fluctuation set

The local generating set of a label polymer of the new level is
`𝔹 = castG hc (localB (k + 1) … X hsep)` and its fluctuation set is
`𝔹⁻ = castG hc (localB k … Ω_k(𝔹_{k+1}(X)) hsep)` (the top layer dropped).  This file collects the
facts of the pair `(𝔹, 𝔹⁻)` read by the clauses of the recomputed family (route R-LOC, L5).

* `castG_localB_pair`: `𝔹⁻ ≺ 𝔹`, no layer `k + 1` in `𝔹⁻`, `Ω_k(𝔹⁻) = Ω_k(𝔹)`, the top layer of
  `𝔹` lies in `Ω₁(𝔹⁻)`, `RowInHat (coverOf 𝔹) 𝔹⁻`, and `𝔹` is cube aligned and sup-separated at the
  step's cube size.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
  Balaban.SmallField.GsSpec Balaban.LargeField Finset

section Pair

variable {d L N₁ m₁ k : ℕ} [NeZero N₁] [NeZero L] {N₁' m₁' : ℕ} [NeZero N₁'] {ϱ : ℝ}

/-- **The local pair of a label polymer** (`𝔹 = castG hc (𝔹_{k+1}(X))`, `𝔹⁻ = castG hc
(𝔹_k(Ω_k(𝔹_{k+1}(X))))`): `𝔹⁻ ≺ 𝔹`, `Ω_{k+1}(𝔹⁻) = ∅`, `Ω_k(𝔹⁻) = Ω_k(𝔹)`, the top layer of `𝔹`
lies in `Ω₁(𝔹⁻)`, the rows of the pair stay in the thickened cubes (`RowInHat`), and `𝔹` is cube
aligned and sup-separated at the cube size `m₁` of the step torus (`2 ≤ m₁ ≤ m₁'`, `3 ≤ L`). -/
theorem castG_localB_pair (hc : N₁' * L ^ m₁' = N₁ * L ^ m₁) (hm₁ : 2 ≤ m₁) (hm : m₁ ≤ m₁')
    (hk : 1 ≤ k) (hL : 3 ≤ L) (X : Set (CTorus d L N₁' m₁' (k + 1)))
    (hsep : ϱ ≤ minSep L (L ^ m₁')) (a : ℕ → ℝ) (ν : ℝ) :
    Precedes (castG hc (localB k (Nat.le_succ k)
        (↑((localB (k + 1) (le_refl (k + 1)) X hsep).Ω k) : Set (CTorus d L N₁' m₁' (k + 1)))
          hsep))
      (castG hc (localB (k + 1) (le_refl (k + 1)) X hsep)) ∧
    (castG hc (localB k (Nat.le_succ k)
        (↑((localB (k + 1) (le_refl (k + 1)) X hsep).Ω k) : Set (CTorus d L N₁' m₁' (k + 1)))
          hsep)).Ω (k + 1) = ∅ ∧
    (castG hc (localB k (Nat.le_succ k)
        (↑((localB (k + 1) (le_refl (k + 1)) X hsep).Ω k) : Set (CTorus d L N₁' m₁' (k + 1)))
          hsep)).Ω k = (castG hc (localB (k + 1) (le_refl (k + 1)) X hsep)).Ω k ∧
    (∀ y ∈ (castG hc (localB (k + 1) (le_refl (k + 1)) X hsep)).Ω (k + 1),
      y ∈ (castG hc (localB k (Nat.le_succ k)
        (↑((localB (k + 1) (le_refl (k + 1)) X hsep).Ω k) : Set (CTorus d L N₁' m₁' (k + 1)))
          hsep)).Ω 1) ∧
    RowInHat (coverOf (castG hc (localB (k + 1) (le_refl (k + 1)) X hsep)))
      (castG hc (localB k (Nat.le_succ k)
        (↑((localB (k + 1) (le_refl (k + 1)) X hsep).Ω k) : Set (CTorus d L N₁' m₁' (k + 1)))
          hsep)) a ν ∧
    CubeAligned (castG hc (localB (k + 1) (le_refl (k + 1)) X hsep)) m₁ ∧
    SupSep (castG hc (localB (k + 1) (le_refl (k + 1)) X hsep)) m₁ := by
  have hP := precedes_castG_localB_drop hc (le_refl (k + 1)) (Nat.le_succ k) X hsep hsep
  have hSS := castG_localB_supSep hc hm (le_refl (k + 1)) X hsep
  refine ⟨hP, castG_localB_drop_top hc (le_refl (k + 1)) (Nat.le_succ k) X hsep hsep,
    castG_localB_drop_Ω hc (le_refl (k + 1)) (Nat.le_succ k) X hsep hsep le_rfl,
    fun y hy => ?_, p6_rowInHat_of_pair hSS hP hL,
    castG_localB_cubeAligned hc hm₁ hm (le_refl (k + 1)) X hsep, hSS⟩
  rw [castG_localB_drop_Ω hc (le_refl (k + 1)) (Nat.le_succ k) X hsep hsep hk]
  exact (castG hc (localB (k + 1) (le_refl (k + 1)) X hsep)).Ω_antitone le_rfl (by omega)
    (by omega) hy

end Pair

end Balaban.Fluctuation
