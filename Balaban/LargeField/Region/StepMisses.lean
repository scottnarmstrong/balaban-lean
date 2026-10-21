/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Region.Inclusions

/-!
# The new region misses the large-field region of the previous scale (P5 (2.3))

`RegionStep.blockMap_notMem_Omega`: the coarse cube of a cube of `Z_k` is not in `Ω_{k+1}` (the
opening of scale `k + 1` misses the coarsening `U'_k ⊇ Z_k^↑`; LFR Lemma I.3.5 (e)).
-/

@[expose] public section

namespace Balaban.LargeField

namespace RegionStep

variable {d L n0 n1 : ℕ} [NeZero n0] [NeZero n1] {Rprev Rk : ℝ}

/-- **The new region misses the large-field region of the previous scale, cube form** (P5 (2.3):
the opening of scale `k + 1` misses the coarsening `U'_k` of `Z_k`; LFR Lemma I.3.5 (e)): the
coarse cube of a cube of `Z_k` is not in `Ω_{k+1}`. -/
theorem blockMap_notMem_Omega (st : RegionStep d L n0 n1 Rprev Rk) {u : Torus d n0}
    (hu : u ∈ st.Z) : blockMap L n1 u ∉ st.Omega := fun h =>
  st.Uprime_subset_compl ⟨u, subset_nbhd _ _ hu, rfl⟩ (st.Omega_subset_OmegaPrime h)

end RegionStep

end Balaban.LargeField
