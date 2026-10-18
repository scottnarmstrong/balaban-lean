/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Background.TwoTorusRoom
public import Balaban.LargeField.Operators.MainAction

/-!
# The generating set of a history near a component

For a history without removals and a component `Zc` of `Z^pre_{k+1}`, near `Zc` (sites whose
`π_{k+1}`-cube is within `D ≤ ⌊R_k⌋ + 2` of `Zc`) the layers `Ω_j` of the generating set `𝔹_{K'}`
of the history are determined by `Zc` and the records inside `Zc` (`histGen_mem_near`): a site
outside `Zc` lies in `Ω_j` for `j ≤ k + 1`, a site of `Zc` lies in `Ω_j` iff its `π_j`-cube lies in
the domain of the step `j - 1`, and no site lies in `Ω_j` for `j > k + 1`.
-/

@[expose] public section

namespace Balaban.RootFSpine

open Balaban Balaban.Multiscale Balaban.LargeField RegionHistory

section Near

variable {d L n0 n1 : ℕ} [NeZero L] [NeZero n0] [NeZero n1] {Rprev Rk : ℝ} {ω : ℕ}
  {Zp : Set (Torus d n1)} {Z' : Finset (Torus d n1)}

omit [NeZero L] [NeZero n0] in
/-- A cube near `Z'` but outside `Z'` lies in `Ω_{k+1}` (cube form). -/
theorem omega_of_not_mem_near (st : RegionStep d L n0 n1 Rprev Rk) (hZ : st.Omegaᶜ ⊆ Zp)
    (hZ' : Z' ∈ comps ω (finOf Zp)) {D : ℕ} (hD : D < ω) {y : Torus d n1}
    (hnear : ∃ z ∈ Z', supDist y z ≤ D) (hnot : y ∉ Z') : y ∈ st.Omega := by
  by_contra hpO
  obtain ⟨z, hz, hd⟩ := hnear
  have hp : y ∈ Zp := hZ hpO
  exact hnot (mem_comp_of_close hZ' hz (mem_finOf.2 hp) (by rw [supDist_comm]; omega))

end Near

section Hist

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L]

/-- **Near a component, the layers of the generating set of the history are determined by the
component and the records inside it** (`Ω_{i+1}` is the domain of the step `i`). -/
theorem histGen_mem_near (Hl : RegionHistory S n R k0 K) (hrem : ∀ j, Hl.rem j = ∅) {k K' : ℕ}
    (hk : k + 1 ≤ K') (hK' : K' ≤ K) (hL : 2 ≤ S.L) (hR : ∀ j, 1 ≤ j → j < K' → S.Rb ≤ R j)
    (Zc : Finset (Torus S.d (n (k + 1)))) (hZc : Zc ∈ comps (S.omega (k + 1)) (Hl.F.Zp (k + 1)))
    (hω : 2 * ⌊R k⌋₊ + S.L + 11 ≤ S.omega (k + 1)) {D : ℕ} (hD : D ≤ ⌊R k⌋₊ + 2)
    (x : Torus S.d (M * n K' * S.L ^ K'))
    (hx : ∃ z ∈ Zc, supDist (cubeMap n S.L M K' (k + 1) x) z ≤ D) (i : ℕ) :
    x ∈ (Hl.histGen (M := M) (K' := K') hK' hrem hL hR).Ω (i + 1) ↔
      i + 1 ≤ k + 1 ∧ (cubeMap n S.L M K' (k + 1) x ∉ Zc ∨
        cubeMap n S.L M K' (i + 1) x ∈ (Hl.step i).Omega) := by
  have hnn := Hl.F.hnn
  have hmem := fun (j : ℕ) (y : Torus S.d (M * n K' * S.L ^ K')) =>
    Hl.mem_histGen (M := M) hK' hrem hL hR j y
  have hΩk1 : cubeMap n S.L M K' (k + 1) x ∉ Zc →
      x ∈ (Hl.histGen (M := M) (K' := K') hK' hrem hL hR).Ω (k + 1) := by
    intro hnot
    refine (hmem (k + 1) x).2 ⟨hk, ?_⟩
    exact omega_of_not_mem_near (Hl.step k) (Omega_compl_subset_Zpre' k (Hl.step k) _ _) hZc
      (D := ⌊R k⌋₊ + 2) (by omega) (by
        obtain ⟨z, hz, hd⟩ := hx
        exact ⟨z, hz, hd.trans hD⟩) hnot
  by_cases hjk : i + 1 ≤ k + 1
  · constructor
    · intro h
      exact ⟨hjk, Or.inr ((hmem (i + 1) x).1 h).2⟩
    · rintro ⟨-, h | h⟩
      · exact (Hl.histGen (M := M) (K' := K') hK' hrem hL hR).Ω_antitone (by omega)
          (show i + 1 ≤ k + 1 by omega) (by omega) (hΩk1 h)
      · exact (hmem (i + 1) x).2 ⟨by omega, h⟩
  · have hnot : x ∉ (Hl.histGen (M := M) (K' := K') hK' hrem hL hR).Ω (i + 1) := by
      intro hxj
      have hiK := ((hmem (i + 1) x).1 hxj).1
      have h2 := (Hl.histGen (M := M) (K' := K') hK' hrem hL hR).Ω_antitone (by omega)
        (show k + 2 ≤ i + 1 by omega) (by omega) hxj
      obtain ⟨-, h2⟩ := (hmem (k + 2) x).1 h2
      obtain ⟨z, hz, hd⟩ := hx
      have hzZ : z ∈ (Hl.step (k + 1)).Z := mem_step_Z_of_mem_comp Hl hrem hZc hz
      have hy : blockMap S.L (n (k + 1 + 1)) (cubeMap n S.L M K' (k + 1) x) ∈
          (Hl.step (k + 1)).Omega := by
        rw [cubeMap_succ (fun i hi => hnn i (lt_of_lt_of_le hi hK')) (by omega : k + 1 + 1 ≤ K')]
        exact h2
      have hfar := (Hl.step (k + 1)).fine_far (Nat.pos_of_ne_zero (NeZero.ne _))
        (hnn (k + 1) (by omega)) hy hzZ
      simp only [Nat.add_sub_cancel] at hfar
      have : 0 < S.L := Nat.pos_of_ne_zero (NeZero.ne _)
      nlinarith
    constructor
    · intro h; exact absurd h hnot
    · rintro ⟨h, -⟩; omega

end Hist

end Balaban.RootFSpine
