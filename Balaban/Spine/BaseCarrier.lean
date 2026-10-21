/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseSmallField
public import Balaban.LargeField.Def7

/-!
# The physical base carrier at the geometry of the class (ruling R7′; A3-1 (d))

`BaseSmallFieldInput M K k₀ geo cs N` (`LargeField/Base/BaseSmallField.lean`) is stated at a general
block constant `M` and torus horizon `K`: the source is a function on the fine sites of the torus,
`GIdx S n M K N → ℂ`, and the local histories are `H.localHistory M K 1 Z'`. The fixed-geometry
statements of the earlier sections (`Prop279Phys`, `Prop279Input`) are its instances at `M = K = 1`.

* `BaseSmallFieldInput.KphysT`: at `M = K = 1`, the remainder as a function of the source on the
  physical torus `Torus d (L n₁)` (the form of ruling R7), with `KphysT_baseSource`;
* `baseSmallFieldInput_class_nonempty`: the carrier is inhabited at the geometry of the class, the
  tori `sides L K n_K` of every `n_K ≥ 1` and the class's `M`, `K = k̂_f + 1` (rule 10; the zero
  input);
* `baseStepData_at_class`: a family of carriers over the tori of the class gives the base step data on
  every torus (`baseStepData_of_input`).
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.LargeField.Def7

section Fixed

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] [NeZero S.L] {R : ℕ → ℝ} {N k0 : ℕ}
  {geo : Geo S n R 1} {cs : OpConsts}

/-- The remainder `K̃^w_0` as a function of the source on the physical torus `Torus d (L n₁)`
(`M = K = 1`). -/
noncomputable def BaseSmallFieldInput.KphysT (inp : BaseSmallFieldInput 1 1 k0 geo cs N)
    (H : RegionHistory S n R k0 1) (hH : H.Admissible) (Z' : H.Comp 1)
    (g : Torus S.d (S.L * n 1) → Fin N → ℂ) (w : BaseW (H.localHistory 1 1 1 Z') 0)
    (o : OutT N R (H.localHistory 1 1 1 Z') 1) (x : NewCfg N (H.localHistory 1 1 1 Z') 0)
    (hv : EuclideanSpace ℝ (Fin N)) : ℂ :=
  inp.Kphys H hH Z' ((baseSourceEquiv S n N).symm g) w o x hv

theorem BaseSmallFieldInput.KphysT_baseSource (inp : BaseSmallFieldInput 1 1 k0 geo cs N)
    (H : RegionHistory S n R k0 1) (hH : H.Admissible) (Z' : H.Comp 1)
    (g : GIdx S n 1 1 N → ℂ) (w : BaseW (H.localHistory 1 1 1 Z') 0)
    (o : OutT N R (H.localHistory 1 1 1 Z') 1) (x : NewCfg N (H.localHistory 1 1 1 Z') 0)
    (hv : EuclideanSpace ℝ (Fin N)) :
    inp.KphysT H hH Z' (baseSource S n N g) w o x hv = inp.Kphys H hH Z' g w o x hv := by
  unfold BaseSmallFieldInput.KphysT
  rw [← baseSourceEquiv_apply, Equiv.symm_apply_apply]

end Fixed

section Class

variable {R : ℕ → ℝ} {M K N k0 : ℕ} [NeZero M]

/-- **The carrier is inhabited at the geometry of the class** (rule 10): for the tori of the family
of every geometry of the class the zero input. -/
theorem baseSmallFieldInput_class_nonempty (S : Setting) [NeZero S.L]
    (geo : ∀ (nK : ℕ) [NeZero nK], Geo S (sides S.L K nK) R M) (cs : OpConsts) :
    ∀ (nK : ℕ) [NeZero nK], Nonempty (BaseSmallFieldInput M K k0 (geo nK) cs N) :=
  fun nK _ => baseSmallFieldInput_nonempty (geo nK) cs N k0

/-- **The base step data on the tori of the class** from a family of carriers. -/
noncomputable def baseStepData_at_class (S : Setting) [NeZero S.L]
    (geo : ∀ (nK : ℕ) [NeZero nK], Geo S (sides S.L K nK) R M) (cs : OpConsts)
    (inp : ∀ (nK : ℕ) [NeZero nK], BaseSmallFieldInput M K k0 (geo nK) cs N)
    (hz : 0 ≤ cs.z (0 + 1)) (hc : 0 ≤ cs.beta 0 * cs.aKer * (S.L : ℝ) ^ (S.d - 2))
    (nK : ℕ) [NeZero nK] : BaseStepData M K k0 (geo nK) cs N :=
  baseStepData_of_input (inp nK) hz hc

end Class

end Balaban.LargeField
