/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring

/-!
# The witness expansion of the failure weight

LFR (II.7.4): for a cube `□'` the failure function of the small-field condition `χ' = A B` is
`1 - A B = (1 - A) + A (1 - B)`, and the product over the cubes `P` of a `P`-term expands as a sum
over the witness types `w : P → {blk, bd}` (`true` = `blk`):

`∏_{c ∈ P} (1 - A_c B_c) = ∑_w ∏_{c ∈ P} (if w c then 1 - A_c else A_c (1 - B_c))`.

Each term splits as a product of the factor `F^w` that reads the block condition `A` (the witness
function `baseF`) and the factor `K^w` that does not (`1 - B` for the bond witnesses): the
`P`-term `∏_{c∈P}(1 - A_c B_c) ∏_{c∉P} A_c B_c` equals `∑_w F^w K^w` (`witnessF`, `witnessK`).
-/

@[expose] public section

namespace Balaban.LargeField

open Finset

section Generic

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The failure weight `1 - A B` splits into the block witness and the bond witness. -/
theorem one_sub_mul_eq_witness (A B : ℝ) :
    1 - A * B = (1 - A) + A * (1 - B) := by ring

/-- **Witness expansion**: `∏_c (1 - A_c B_c) = ∑_{w : ι → Bool} ∏_c (if w c then 1 - A_c else A_c (1 - B_c))`. -/
theorem prod_one_sub_mul_eq_sum_witness (A B : ι → ℝ) :
    ∏ c, (1 - A c * B c) =
      ∑ w : ι → Bool, ∏ c, (if w c then 1 - A c else A c * (1 - B c)) := by
  have h : ∀ c, 1 - A c * B c = ∑ b : Bool, (if b then 1 - A c else A c * (1 - B c)) := by
    intro c
    rw [Fintype.sum_bool]
    simp only [ite_true, Bool.false_eq_true, ite_false]
    ring
  simp_rw [h]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]

end Generic

section Cubes

variable {c : Type*} [Fintype c] [DecidableEq c]

/-- The block-reading factor `F^w` of a `P`-term: `1 - A` on the block witnesses, `A` on the bond
witnesses and on the cubes outside `P`. -/
def witnessF (P : Finset c) (A : c → ℝ) (w : ↥P → Bool) : ℝ :=
  (∏ x : ↥P, if w x then 1 - A x else A x) * ∏ x ∈ Finset.univ \ P, A x

/-- The remaining factor `K^w` of a `P`-term: `1 - B` on the bond witnesses and `B` outside `P`. -/
def witnessK (P : Finset c) (B : c → ℝ) (w : ↥P → Bool) : ℝ :=
  (∏ x : ↥P, if w x then 1 else 1 - B x) * ∏ x ∈ Finset.univ \ P, B x

/-- **The `P`-term as a sum over witnesses**:
`∏_{c∈P}(1 - A_c B_c) ∏_{c∉P} A_c B_c = ∑_w F^w K^w`. -/
theorem prod_failure_mul_prod_eq_sum_witness (P : Finset c) (A B : c → ℝ) :
    (∏ x ∈ P, (1 - A x * B x)) * ∏ x ∈ Finset.univ \ P, A x * B x =
      ∑ w : ↥P → Bool, witnessF P A w * witnessK P B w := by
  have h1 := prod_one_sub_mul_eq_sum_witness (fun x : ↥P => A x) (fun x : ↥P => B x)
  rw [Finset.prod_coe_sort P (fun x => 1 - A x * B x)] at h1
  rw [h1, Finset.sum_mul, Finset.prod_mul_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  unfold witnessF witnessK
  have : ∏ x : ↥P, (if w x then 1 - A x else A x * (1 - B x)) =
      (∏ x : ↥P, if w x then 1 - A x else A x) * ∏ x : ↥P, if w x then 1 else 1 - B x := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun x _ => ?_
    by_cases hw : w x <;> simp [hw]
  rw [this]
  ring

end Cubes

end Balaban.LargeField
