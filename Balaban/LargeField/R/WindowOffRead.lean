/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.WindowConvPhysReadData

/-!
# The read transport for a given window field

P7 p. 501 (2.14): the backgrounds of the pieces and the window background are evaluated at the
same configuration `ψ̃`.  `window_field_read_eq_of_agree` is the read identity of
`exists_window_field_read_eq` for a *given* block field `ψ` of the window: if the physical datum of
`ψ` reads the datum `locData` of every piece on the sites of its region (the inherited value
`ψ(p_𝔹(x))` of the parent block of `x` in `𝔹_k` equals the local datum), then for every window field
`φw`, coefficient `a` and mass `ν`, the action of the region of each piece on the window generating
set equals the local action at the transported field.  Only the values of `ψ` on the parent blocks
of the piece regions enter, so `ψ` is free on the rest of the window (the core collar `Z_{k₁}` and
`U_k^∼ ∖ Z`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Fluctuation RegionHistory Balaban.Background
  Balaban.LargeField.ActionConv

section Main

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {H : RegionHistory S n R k0 K} {m' : ℕ} {N : ℕ}

/-- **The read identity for a given window field** (P7 (2.14)): if `ψ` reads the datum of each
piece on the sites of its region, the restricted action of the region of the piece on the window
generating set at the physical datum of `ψ` equals the local action at the transported field. -/
theorem window_field_read_eq_of_agree {k1 : ℕ} {Z : H.Comp (m' + 1)} (g : Geo S n R M)
    (hmK : m' + 1 ≤ K) (hL : 2 ≤ S.L) (hR : ∀ i, 1 ≤ i → i < m' + 1 → S.Rb ≤ R i)
    (hk1p : 1 ≤ k1) {ϱ : ℝ} (W : WindowPieces S.d S.L (M * n (m' + 1)) (m' + 1) ϱ)
    (hWh : W.Hyp) (href : ParentRefines (W.windowGenSet hWh) W.full)
    (hWfull : ∀ q, W.full.Ω q = (H.locGen Z M hmK hL hR).Ω q)
    (hWZ : W.Z = H.locFineFin Z (m' + 1)) (hWZk1 : W.Zk1 = H.locFineFin Z k1)
    {ι : Type*} (jf : ι → ℕ) (cf : ∀ i, H.Comp (jf i + 1))
    (hjf : ∀ i, k1 ≤ jf i ∧ jf i ≤ m') (hcf : ∀ i, cf i ∈ H.ancFin (jf i + 1) (m' + 1) Z)
    (hjK : ∀ i, jf i + 1 ≤ K)
    (Xw : ι → Region (W.windowGenSet hWh))
    (hXw : ∀ i x, x ∈ (Xw i).sites ↔
      torusCast (piece_torus_eq g H.F.hnn hmK (hjf i).2) x ∈
        Xfine g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1)
    (Xc : ∀ i, Region (locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1
      (locComp_mem H (hjK i) (cf i)) (hjK i)))
    (hXc : ∀ i, (Xc i).sites = Xfine g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1)
    (ou : ∀ i, OutT N R (locHist (H.locRH (jf i + 1) (cf i)) M K (jf i + 1) (cf i).1) (jf i + 1))
    (xu : ∀ i, NewCfg N (locHist (H.locRH (jf i + 1) (cf i)) M K (jf i + 1) (cf i).1) (jf i))
    (hv : EuclideanSpace ℝ (Fin N))
    (ψ : BlockV S.d S.L (M * n (m' + 1)) (m' + 1) → EuclideanSpace ℝ (Fin N))
    (hψ : ∀ i x, x ∈ (Xw i).sites →
      (locData g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i))
        (hjK i) (ou i) (xu i) hv).Ψ (torusCast (piece_torus_eq g H.F.hnn hmK (hjf i).2) x) =
        fun q => ((ψ (blockOf S.d S.L (M * n (m' + 1)) (m' + 1) (W.full.layerIndex x) x) q : ℝ) :
          ℂ))
    (φw : (W.windowGenSet hWh).Ω 1 × Fin N → ℂ) (a : ℕ → ℝ) (ν : ℝ) (i : ι) :
    actionRegionC (Xc i) a ν
        (locData g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i))
          (hjK i) (ou i) (xu i) hv)
        (transportField (Gl := locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1
            (locComp_mem H (hjK i) (cf i)) (hjK i))
          (Equiv.cast (congrArg (Torus S.d) (piece_torus_eq g H.F.hnn hmK (hjf i).2)))
          (physicalWindowData W hWh href ψ (fun q => hv q)).Ψ φw) =
      actionRegionC (Xw i) a ν (physicalWindowData W hWh href ψ (fun q => hv q)) φw := by
  classical
  have hxZ : ∀ x, x ∈ (Xw i).sites → x ∈ W.Z \ W.Zk1 := fun x hx => by
    obtain ⟨hx1, hx2⟩ := (mem_Xfine_cast_iff g hmK (hjf i).2 (cf i) (hjK i) x).1 ((hXw i x).1 hx)
    exact window_site_mem_diff hmK (hjf i).1 (hjf i).2 W hWZ hWZk1 (hcf i) hx1 hx2
  refine piece_actionRegionC_transport g hmK hL hR hk1p (hjf i).1 (hjf i).2 (hjK i) W hWh hWfull hWZ
    hWZk1 (hcf i) (Xw i) (hXw i) (Xc i) (hXc i) _ _ ?_ ?_ φw a ν
  · intro x hx
    have hxd : x ∈ dataSites (W.windowGenSet hWh) :=
      (mem_dataSites _).2 (Or.inl ((Xw i).sub_Ω hx))
    have hZx := hxZ x hx
    have hfullΩ : x ∈ W.full.Ω 1 :=
      (windowGenSet_mem_iff_full W hWh hZx (Finset.mem_sdiff.1 hZx).1 1).1 ((Xw i).sub_Ω hx)
    funext q
    rw [physicalWindowData_Ψ W hWh href ψ _ hxd q, inheritedField_eq_parentBlock,
      parentBlock_of_mem _ hfullΩ]
    exact congrFun (hψ i x hx) q
  · intro x hx
    have hloc1 : torusCast (piece_torus_eq g H.F.hnn hmK (hjf i).2) x ∈
        (locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i))
          (hjK i)).Ω 1 := by
      refine (Xc i).sub_Ω ?_
      rw [hXc i]; exact (hXw i x).1 hx
    unfold locData
    rw [liftMixed_h _ _ _ _ _ _ hloc1]
    funext q
    rw [physicalWindowData_h W hWh href ψ _ ((Xw i).sub_Ω hx) q]

end Main

end Balaban.LargeField
