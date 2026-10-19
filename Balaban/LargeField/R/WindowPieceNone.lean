/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.WindowPieceY
public import Balaban.LargeField.R.WindowDomChi

/-!
# The datum of a piece in the real domain from the domain condition of its operator (blocker 4)

For a component `C` of `Z^pre_{k+1}` with the configuration `(o, xw)` of the operator of `C` (all internal
variables of `C`), `ChiDomAt` gives the three families of `ChiDomProp` that the piece lemmas need
(`families_of_chiDomAt`); the multiscale field of the operator agrees with that of the piece (output
and the new variables of scale `k`) at the scales `k + 1`, `k` (`pieceField_top_eq`,
`pieceField_k_eq`).  `piece_inDomainR_of_chiDomAt`: the datum `locData` of the piece of `C` at
`(o, newRestrict xw)` is in the real domain `Ψ̃(G; ν, η)`, the outside of `C` being tested by
`χ_{k+1}(Y)` of the post-weight field.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background Balaban.LargeField.Def7 RegionHistory

section PieceNone

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ} {M : ℕ} [NeZero M]
  [NeZero S.L] {N i : ℕ} (H : RegionHistory S n R k0 K) (g : Geo S n R M) (cs : OpConsts)
  (C : H.Comp (i + 1 + 1))

/-- The three families of the pieces from `ChiDomAt` of the operator: the first family of
`ChiDomProp` at the scales `k + 1`, `k` and the second family at the scale `k` (`k = i + 1`). -/
theorem families_of_chiDomAt {A : Set (InternalVars (H.localHistory M K (i + 1 + 1) C) (i + 1 + 1))}
    {o : OutT N R (H.localHistory M K (i + 1 + 1) C) (i + 1 + 1)}
    {xw : SubCfg N (H.localHistory M K (i + 1 + 1) C) (i + 1 + 1) A}
    (h : ChiDomAt g cs H (i + 1 + 1) C o xw) :
    let ψw := subMultiscaleField N (H.localHistory M K (i + 1 + 1) C) (i + 1 + 1)
      (Vblk R (H.localHistory M K (i + 1 + 1) C) (i + 1 + 1)) xw o
    PieceFirstFamily H g C ψw (3 * S.d * S.L * cs.delta (i + 1)) ∧
    PieceSecondFamily H C ψw (3 * cs.delta (i + 1)) ∧
    PieceZkFamily H g C ψw (3 * S.d * S.L * cs.delta i) :=
  ⟨fun q hZ hsim => h.1 (i + 1) (Nat.lt_succ_self _) q hZ hsim,
   fun y hsub hnot hfar => h.2.1 (i + 1) (Nat.succ_pos i) (Nat.le_succ _) y hsub hnot hfar,
   fun q hZ hsim => h.1 i (by omega) q hZ hsim⟩


omit [NeZero M] [NeZero S.L] in
/-- The window field agrees with the piece field at the top scale. -/
theorem pieceField_top_eq {A : Set (InternalVars (H.localHistory M K (i + 1 + 1) C) (i + 1 + 1))}
    (o : OutT N R (H.localHistory M K (i + 1 + 1) C) (i + 1 + 1))
    (xw : SubCfg N (H.localHistory M K (i + 1 + 1) C) (i + 1 + 1) A)
    (hnew : newVars (H.localHistory M K (i + 1 + 1) C) (i + 1) ⊆ A)
    (b : BlockAt S n M K (i + 1 + 1)) :
    subMultiscaleField N (H.localHistory M K (i + 1 + 1) C) (i + 1 + 1)
      (Vblk R (H.localHistory M K (i + 1 + 1) C) (i + 1 + 1)) xw o (i + 1 + 1) b =
    pieceField H C o (newRestrict (H.localHistory M K (i + 1 + 1) C) hnew xw) (i + 1 + 1) b := by
  unfold pieceField subMultiscaleField
  simp

/-- The window field agrees with the piece field at the scale `k` of the new variables. -/
theorem pieceField_k_eq {A : Set (InternalVars (H.localHistory M K (i + 1 + 1) C) (i + 1 + 1))}
    (o : OutT N R (H.localHistory M K (i + 1 + 1) C) (i + 1 + 1))
    (xw : SubCfg N (H.localHistory M K (i + 1 + 1) C) (i + 1 + 1) A)
    (hnew : newVars (H.localHistory M K (i + 1 + 1) C) (i + 1) ⊆ A)
    (b : BlockAt S n M K (i + 1)) :
    subMultiscaleField N (H.localHistory M K (i + 1 + 1) C) (i + 1 + 1)
      (Vblk R (H.localHistory M K (i + 1 + 1) C) (i + 1 + 1)) xw o (i + 1) b =
    pieceField H C o (newRestrict (H.localHistory M K (i + 1 + 1) C) hnew xw) (i + 1) b := by
  unfold pieceField subMultiscaleField
  simp only [Nat.lt_succ_self, ↓reduceIte]
  rw [subVarField_new hnew xw b]


variable (hjK : i + 1 + 1 ≤ K) {m₁ : ℕ} {ϱ : ℝ}

include hjK in
/-- **The real domain of the datum of a window piece whose component is the window component,
from the domain condition of the window operator.**  `ChiDomAt` of the operator of `C` at the
window point `(o, xw)` gives the three families (first and second at the scales `k + 1`, `k`; first
at `k`), the outside of `C` is tested by `χ_{k+1}(Y)` of the post-weight field `ψk`
(`WindowPieceY`), and the datum is that of the piece with the new variables `newRestrict xw`. -/
theorem piece_inDomainR_of_chiDomAt {ν : ℝ}
    (Cx : Def7.SFCtx S n R M K N (i + 1 + 1) m₁ ϱ) (cs : OpConsts)
    {A : Set (InternalVars (H.localHistory M K (i + 1 + 1) C) (i + 1 + 1))}
    (hnew : newVars (H.localHistory M K (i + 1 + 1) C) (i + 1) ⊆ A)
    (o : OutT N R (H.localHistory M K (i + 1 + 1) C) (i + 1 + 1))
    (xw : SubCfg N (H.localHistory M K (i + 1 + 1) C) (i + 1 + 1) A)
    (hχd : ChiDomAt Cx.geo cs H (i + 1 + 1) C o xw) (hv : EuclideanSpace ℝ (Fin N))
    (hν : 0 ≤ ν) (hunit : ‖hv‖ = 1)
    (hη : 0 < max (max (3 * S.d * S.L * cs.delta (i + 1)) (3 * cs.delta (i + 1)))
      (max (3 * S.d * S.L * cs.delta i) (max (3 * Cx.cs.delta (i + 1 + 1))
        ((S.d + 1) * Cx.cs.delta (i + 1 + 1) * (2 + (S.d + 1) * Cx.cs.delta (i + 1 + 1))))))
    (hmass : 2 * ν * ((S.L : ℝ) ^ (i + 1 + 1)) ^ 2 <
      (max (max (3 * S.d * S.L * cs.delta (i + 1)) (3 * cs.delta (i + 1)))
      (max (3 * S.d * S.L * cs.delta i) (max (3 * Cx.cs.delta (i + 1 + 1))
        ((S.d + 1) * Cx.cs.delta (i + 1 + 1) * (2 + (S.d + 1) * Cx.cs.delta (i + 1 + 1)))))) ^ 2)
    (ψk : BlockAt S n M K (i + 1 + 1) → EuclideanSpace ℝ (Fin N))
    (hvp : EuclideanSpace ℝ (Fin N)) (hχ : Cx.chiY ((H.step (i + 1 + 1)).Z)ᶜ ψk hvp ≠ 0)
    (HB : BgHyp S.d S.L (i + 1 + 1) (minSep S.L Cx.geo.M1) Cx.weights (Cx.cs.mu (i + 1 + 1)))
    (Z0 : Set (BlockAt S n M K (i + 1 + 1)))
    (hZ0C : ∀ b ∈ Z0, blockCube S n M K (i + 1 + 1) b ∈ C.1)
    (hψk : ∀ b ∈ Vblk R (H.localHistory M K (i + 1 + 1) C) (i + 1 + 1), b ∉ Z0 → ψk b = outField N o b) :
    InDomainR (locGen Cx.geo (H.locRH (i + 1 + 1) C) (i + 1) C.1 (locComp_mem H hjK C) hjK) ν
      (max (max (3 * S.d * S.L * cs.delta (i + 1)) (3 * cs.delta (i + 1)))
        (max (3 * S.d * S.L * cs.delta i) (max (3 * Cx.cs.delta (i + 1 + 1))
          ((S.d + 1) * Cx.cs.delta (i + 1 + 1) * (2 + (S.d + 1) * Cx.cs.delta (i + 1 + 1))))))
      (locData Cx.geo (H.locRH (i + 1 + 1) C) (i + 1) C.1 (locComp_mem H hjK C) hjK o
        (newRestrict (H.localHistory M K (i + 1 + 1) C) hnew xw) hv) := by
  obtain ⟨hF1, hF2, hFZ⟩ := families_of_chiDomAt H Cx.geo cs C hχd
  exact piece_inDomainR_of_chiY H C hjK Cx
    (subMultiscaleField N (H.localHistory M K (i + 1 + 1) C) (i + 1 + 1)
      (Vblk R (H.localHistory M K (i + 1 + 1) C) (i + 1 + 1)) xw o)
    o (newRestrict (H.localHistory M K (i + 1 + 1) C) hnew xw) hv hν hunit hη hmass
    (subMultiscaleField N (H.localHistory M K (i + 1 + 1) C) (i + 1 + 1)
      (Vblk R (H.localHistory M K (i + 1 + 1) C) (i + 1 + 1)) xw o)
    (pieceField_top_eq H C o xw hnew) (pieceField_k_eq H C o xw hnew) hF1 hF2 hFZ
    (fun t _ _ => pieceField_k_eq H C o xw hnew _) ψk hvp hχ HB Z0 hZ0C hψk

end PieceNone

end Balaban.LargeField
