/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.RVacuumTie
public import Balaban.LargeField.Operators.StepVacuumVolume

/-!
# Records of a localized history and the necessary condition for `RVacuumB0Input` (A4-2v)

`VacuumB0Bound` asks `‖b_k + stepVacuumTerm(E_k, E_k + δ″, E_k + δ‴)‖ ≤ C |Z_{k+1} ∖ Z_k|_{k+1}`
for the localized history `a = H.localHistory (k+1) Z'`.

Before ruling R10 the first vacuum region was `(Z_k)^c ∖ Ω_{k+1}`, a complement in the whole fine
torus, which contained the fine set of the complement of `Z'`; the lemma stating this
(`compl_fineSet_subset_vacuumRegion`) documented the defect and is deleted, as it is false for the
region `(Z_{k+1} ∖ Z_k) ∖ Ω_{k+1}` of R10.  The lemmas that remain are true as stated:

* `localHistory_Z_subset_fineSet`, `localHistory_Omega_subset_fineSet`: the records lie in `Z'`;
* `norm_vacuumTerm_le_of_b0Bound`: the necessary condition that `VacuumB0Bound` and `b_bound` impose.
-/

@[expose] public section

namespace Balaban.RootFSpine

open MeasureTheory Balaban Balaban.LargeField Balaban.LargeField.Def7 Balaban.LargeField.Def7v2
  Balaban.SmallField Balaban.SmallField.Def6v2 Balaban.Multiscale RegionHistory

section Defect

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ} {M : ℕ}
  (H : RegionHistory S n R k0 K)

theorem localHistory_Z_subset_fineSet {m : ℕ} (Z : H.Comp m) (j : ℕ) :
    (H.localHistory M K m Z).Z j ⊆ fineSet (S := S) (n := n) M K m (Z.1 : Set (Torus S.d (n m))) :=
  fun _ hx => hx.2

theorem localHistory_Omega_subset_fineSet {m : ℕ} (Z : H.Comp m) (j : ℕ) :
    (H.localHistory M K m Z).Omega j ⊆
      fineSet (S := S) (n := n) M K m (Z.1 : Set (Torus S.d (n m))) :=
  fun _ hx => hx.2

end Defect

section Necessary

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {geo : Geo S n R M} {cs : OpConsts}
  {κs : ℕ → LocalHistory S n M K → ℝ}

/-- **The necessary condition.** If `VacuumB0Bound` holds, then, since `b_k` itself satisfies
`b_bound`, the vacuum term of the flow is bounded by twice the bound on `|Z_{k+1} ∖ Z_k|_{k+1}`:
`‖stepVacuumTerm‖ ≤ 2 (C_b log β_k + C_b B₀) |Z_{k+1} ∖ Z_k|_{k+1}`, on every `χ^new` configuration. -/
theorem norm_vacuumTerm_le_of_b0Bound (SD : StepData k0 geo cs N κs) (E dpp dppp : ℕ → ℝ)
    (hb : VacuumB0Bound SD E dpp dppp) (H : RegionHistory S n R k0 K) (hH : H.Admissible) (k : ℕ)
    (Z' : H.Comp (k + 1)) (o : OutT N R (H.localHistory M K (k + 1) Z') (k + 1))
    (x : NewCfg N (H.localHistory M K (k + 1) Z') k) (hv : EuclideanSpace ℝ (Fin N)) (g : GIdx S n M K N → ℂ) (hg : g ∈ l1Ball (GIdx S n M K N))
    (hχ : ChiNewAt geo cs H k Z' o x) :
    ‖(stepVacuumTerm (H.localHistory M K (k + 1) Z') k (E k) (E k + dpp k) (E k + dppp k) : ℂ)‖ ≤
      2 * ((cs.Cb * Real.log (cs.beta k) + cs.Cb * cs.B0) *
        volScale S (k + 1) {z | z ∈ (H.localHistory M K (k + 1) Z').Z (k + 1) ∧
          z ∉ (H.localHistory M K (k + 1) Z').Z k}) := by
  have h1 := hb H hH k Z' o x hv g hg hχ
  have h2 := SD.b_bound H hH k Z' o x hv g hg hχ
  have h3 := norm_sub_le
    ((SD.ker k (H.localHistory M K (k + 1) Z')).b o x hv g +
      (stepVacuumTerm (H.localHistory M K (k + 1) Z') k (E k) (E k + dpp k) (E k + dppp k) : ℂ))
    ((SD.ker k (H.localHistory M K (k + 1) Z')).b o x hv g)
  rw [add_sub_cancel_left] at h3
  linarith

end Necessary

end Balaban.RootFSpine
