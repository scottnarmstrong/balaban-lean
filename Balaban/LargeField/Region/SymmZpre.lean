module

public import Balaban.LargeField.Region.SymmStep
public import Balaban.LargeField.Region.SymmHull

/-!
# Covariance of the full region step, including the hull closure

Extension of `Balaban/LargeField/Region/SymmStep.lean`: for corresponding steps (the region `Z_k` and
the new cubes `P, Q, R, S` correspond under affine lattice isometries commuting with the
coarsening), the sets `F''`, `Ω''`, `F^Z`, `Z^{(0)}` and `Z^pre_{k+1}` (hull closure) correspond.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban

section Step

variable {d L n0 n1 : ℕ} [NeZero n0] [NeZero n1] {Rp Rk : ℝ} {st st' : RegionStep d L n0 n1 Rp Rk}
  {e0 : Equiv.Perm (Torus d n0)} {e1 : Equiv.Perm (Torus d n1)} (h0 : IsAff e0) (h1 : IsAff e1)
  (hb : ∀ x, blockMap L n1 (e0 x) = e1 (blockMap L n1 x)) (hL : 0 < L)
  (hZ : st'.Z = e0 '' st.Z) (hP : st'.P = e1 '' st.P) (hQ : st'.Q = e1 '' st.Q)
  (hR : st'.R = e1 '' st.R) (hS : st'.S = e1 '' st.S)

include h0 h1 hb hL hZ hP hQ hR in
theorem RegionStep.image_OmegaDD : st'.OmegaDD = e1 '' st.OmegaDD := by
  show Region.OmegaDD L st'.FDD st'.Omega = e1 '' Region.OmegaDD L st.FDD st.Omega
  unfold Region.OmegaDD
  obtain ⟨hW, hW'⟩ := h1.exists_lblock hL
  have hFDD : st'.FDD = e1 '' st.FDD := by
    show Region.FDD ⌊Rk⌋₊ st'.Q st'.R = e1 '' Region.FDD ⌊Rk⌋₊ st.Q st.R
    unfold Region.FDD
    rw [Set.image_union, hQ, hR, image_nbhd h1.supDist_eq, image_nbhd h1.supDist_eq]
  rw [hFDD, RegionStep.image_Omega h0 h1 hb hL hZ hP, image_openingIn h1.supDist_eq hW hW']

include h0 h1 hb hL hZ hP hQ hR hS in
theorem RegionStep.image_Z0 : st'.Z0 = e1 '' st.Z0 := by
  show Region.Z0 L ⌊2 * Rk⌋₊ st'.FZ = e1 '' Region.Z0 L ⌊2 * Rk⌋₊ st.FZ
  unfold Region.Z0
  obtain ⟨hW, hW'⟩ := h1.exists_lblock hL
  have hFZ : st'.FZ = e1 '' st.FZ := by
    show Region.FZ st'.OmegaDD st'.S = e1 '' Region.FZ st.OmegaDD st.S
    unfold Region.FZ
    rw [Set.image_union, hS, RegionStep.image_OmegaDD h0 h1 hb hL hZ hP hQ hR,
      image_nbhd h1.supDist_eq, image_nbhd h1.supDist_eq, Equiv.image_compl]
  rw [hFZ, Equiv.image_compl, image_opening h1.supDist_eq hW hW']

include h0 h1 hb hL hZ hP hQ hR hS in
theorem RegionStep.image_Zpre (ω : ℕ) (crit : Option ℕ) :
    st'.Zpre ω crit = e1 '' st.Zpre ω crit := by
  show Region.Zpre ω crit st'.Z0 = e1 '' Region.Zpre ω crit st.Z0
  rw [RegionStep.image_Z0 h0 h1 hb hL hZ hP hQ hR hS]
  cases crit with
  | none => rfl
  | some b =>
    obtain ⟨A, hA⟩ := h1
    have hf : (e1 : Torus d n1 → Torus d n1) = A.toFun := funext hA
    show hullClosure ω b (e1 '' st.Z0) = e1 '' hullClosure ω b st.Z0
    rw [show (e1 : Torus d n1 → Torus d n1) = A.toFun from hf, A.image_hullClosure]

end Step

end Balaban.LargeField
