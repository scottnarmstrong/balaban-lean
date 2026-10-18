/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.WindowConvPhysReadData
public import Balaban.LargeField.R.WindowOffRead

/-!
# The read transport `hread` for the pieces of a window

P7 p. 501 (2.14)-(2.16); `notes/phase1/astra/P7CONV.md` Part 3 §3.6.  There is one block field `ψ`
of the window, the glue of the data of the pieces, whose physical datum on the window generating set
reads on the sites of each piece the datum `locData` of the piece.  With this datum and any window
field `φw`, the restricted action of the window region of each piece equals the local action of the
piece at the field transported from `φw`; hence the normalized difference `R_i - β_k A_i^win` of
P7CONV (57) vanishes for `R_i = β_k A_i^loc` evaluated at the transported field.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Fluctuation RegionHistory Balaban.Background
  Balaban.LargeField.ActionConv

section Main

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {H : RegionHistory S n R k0 K} {m' : ℕ} {N : ℕ}

/-- **The common window configuration and the read transport** (P7 (2.14)-(2.16)).  For a family
of pieces of the window there is one block field `ψ` such that, for every window field `φw`, every
coefficient `a` and mass `ν`, and every piece `i`, the action of the region of the piece on the
window generating set at the physical datum of `ψ` and `φw` equals the action of the local region at
the local datum `locData` of the piece and the field transported from `φw`. -/
theorem exists_window_field_read_eq {k1 : ℕ} {Z : H.Comp (m' + 1)} (g : Geo S n R M)
    (hmK : m' + 1 ≤ K) (hL : 2 ≤ S.L) (hR : ∀ i, 1 ≤ i → i < m' + 1 → S.Rb ≤ R i)
    (hk1p : 1 ≤ k1) {ϱ : ℝ} (W : WindowPieces S.d S.L (M * n (m' + 1)) (m' + 1) ϱ)
    (hWh : W.Hyp) (href : ParentRefines (W.windowGenSet hWh) W.full)
    (hWfull : ∀ q, W.full.Ω q = (H.locGen Z M hmK hL hR).Ω q)
    (hWZ : W.Z = H.locFineFin Z (m' + 1)) (hWZk1 : W.Zk1 = H.locFineFin Z k1)
    {ι : Type*} (jf : ι → ℕ) (cf : ∀ i, H.Comp (jf i + 1))
    (hjf : ∀ i, k1 ≤ jf i ∧ jf i ≤ m') (hcf : ∀ i, cf i ∈ H.ancFin (jf i + 1) (m' + 1) Z)
    (hinj : Function.Injective fun i => (⟨jf i, cf i⟩ : Σ j, H.Comp (j + 1)))
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
    (hv : EuclideanSpace ℝ (Fin N)) :
    ∃ ψ : BlockV S.d S.L (M * n (m' + 1)) (m' + 1) → EuclideanSpace ℝ (Fin N),
      ∀ (φw : (W.windowGenSet hWh).Ω 1 × Fin N → ℂ) (a : ℕ → ℝ) (ν : ℝ) (i : ι),
        actionRegionC (Xc i) a ν
          (locData g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i))
            (hjK i) (ou i) (xu i) hv)
          (transportField (Gl := locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1
              (locComp_mem H (hjK i) (cf i)) (hjK i))
            (Equiv.cast (congrArg (Torus S.d) (piece_torus_eq g H.F.hnn hmK (hjf i).2)))
            (physicalWindowData W hWh href ψ (fun q => hv q)).Ψ φw) =
        actionRegionC (Xw i) a ν (physicalWindowData W hWh href ψ (fun q => hv q)) φw := by
  classical
  have hxZ : ∀ i x, x ∈ (Xw i).sites → x ∈ W.Z \ W.Zk1 := fun i x hx => by
    obtain ⟨hx1, hx2⟩ := (mem_Xfine_cast_iff g hmK (hjf i).2 (cf i) (hjK i) x).1 ((hXw i x).1 hx)
    exact window_site_mem_diff hmK (hjf i).1 (hjf i).2 W hWZ hWZk1 (hcf i) hx1 hx2
  have hfull : ∀ i x, x ∈ (Xw i).sites →
      W.full.layerIndex x = (W.windowGenSet hWh).layerIndex x := fun i x hx =>
    (windowGenSet_layerIndex_eq_full W hWh (hxZ i x hx)).symm
  have hlay : ∀ i x, x ∈ (Xw i).sites →
      (locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i))
        (hjK i)).layerIndex (torusCast (piece_torus_eq g H.F.hnn hmK (hjf i).2) x) =
      (W.windowGenSet hWh).layerIndex x := fun i x hx => by
    obtain ⟨D, hD, hlayD⟩ := exists_region_Xfine_window (j := jf i) g hmK hL hR hk1p (hjf i).1
      (hjf i).2 (hjK i) W hWh hWfull hWZ hWZk1 (hcf i)
    exact (hlayD x ((hD x).2 ((hXw i x).1 hx))).symm
  have hcl : ∀ i x, x ∈ (Xw i).sites → ∀ x', jBlock S.d S.L (M * n (m' + 1)) (m' + 1)
      (W.full.layerIndex x) x' = jBlock S.d S.L (M * n (m' + 1)) (m' + 1) (W.full.layerIndex x) x →
      x' ∈ (Xw i).sites := fun i x hx x' h =>
    (Xw i).blockClosed x hx x' (by rw [GeneratingSet.mem_blk, ← hfull i x hx]; exact h)
  have hloc1 : ∀ i x, x ∈ (Xw i).sites →
      torusCast (piece_torus_eq g H.F.hnn hmK (hjf i).2) x ∈
        (locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i))
          (hjK i)).Ω 1 := fun i x hx => by
    refine (Xc i).sub_Ω ?_
    rw [hXc i]; exact (hXw i x).1 hx
  have hconst : ∀ i x, x ∈ (Xw i).sites → ∀ x', jBlock S.d S.L (M * n (m' + 1)) (m' + 1)
      (W.full.layerIndex x) x' = jBlock S.d S.L (M * n (m' + 1)) (m' + 1) (W.full.layerIndex x) x →
      (locData g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i))
        (hjK i) (ou i) (xu i) hv).Ψ (torusCast (piece_torus_eq g H.F.hnn hmK (hjf i).2) x') =
      (locData g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i))
        (hjK i) (ou i) (xu i) hv).Ψ (torusCast (piece_torus_eq g H.F.hnn hmK (hjf i).2) x) := by
    intro i x hx x' h
    have hq := hlay i x hx
    obtain ⟨hq1, hqk, hql⟩ := (locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1
      (locComp_mem H (hjK i) (cf i)) (hjK i)).layerIndex_spec (hloc1 i x hx)
    obtain ⟨-, hqkw, -⟩ := (W.windowGenSet hWh).layerIndex_spec ((Xw i).sub_Ω hx)
    have hB := piece_block_eq g H.F.hnn hmK (hjf i).2
      (q := (locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i))
        (hjK i)).layerIndex (torusCast (piece_torus_eq g H.F.hnn hmK (hjf i).2) x)) hqk
    have hblk := (torusCast_mem_blk (W.windowGenSet hWh) (locGen g (H.locRH (jf i + 1) (cf i))
      (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i)) (piece_torus_eq g H.F.hnn hmK (hjf i).2)
      (q := (locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i))
        (hjK i)).layerIndex (torusCast (piece_torus_eq g H.F.hnn hmK (hjf i).2) x))
      (by rw [hq]; exact hqkw) hqk hB x x').1
      (by rw [hq, GeneratingSet.mem_blk, ← hfull i x hx]; exact h)
    exact (locData g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i))
      (hjK i) (ou i) (xu i) hv).Ψ_layerConst _ hq1 hqk _ hql _ hblk
  have hreal : ∀ i x, x ∈ (Xw i).sites → ∃ r : Fin N → ℝ,
      (locData g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i))
        (hjK i) (ou i) (xu i) hv).Ψ (torusCast (piece_torus_eq g H.F.hnn hmK (hjf i).2) x) =
        fun q => (r q : ℂ) := fun i x hx =>
    locData_Ψ_real g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i))
      (hjK i) (ou i) (xu i) hv ((mem_dataSites _).2 (Or.inl (hloc1 i x hx)))
  obtain ⟨ψ, hψ⟩ := exists_glued_blockField (N := N) W.full.layerIndex (fun i => ((Xw i).sites : Set _))
    (fun i x => (locData g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1
      (locComp_mem H (hjK i) (cf i)) (hjK i) (ou i) (xu i) hv).Ψ
      (torusCast (piece_torus_eq g H.F.hnn hmK (hjf i).2) x))
    (fun i i' hne x hx hx' =>
      pieces_regions_disjoint g hmK jf cf hjf hcf hinj hne x ((hXw i x).1 hx) ((hXw i' x).1 hx'))
    (fun i x hx x' h => hcl i x hx x' h) (fun i x hx x' h => hconst i x hx x' h)
    (fun i x hx => hreal i x hx)
  exact ⟨ψ, fun φw a ν i => window_field_read_eq_of_agree g hmK hL hR hk1p W hWh href hWfull hWZ
    hWZk1 jf cf hjf hcf hjK Xw hXw Xc hXc ou xu hv ψ (fun i x hx => hψ i x hx) φw a ν i⟩

/-- **`hread = 0`** (P7CONV §3.6, (57)): with `R_i = β A_i^loc` evaluated at the transported field,
for any normalization `β` (in particular `β = betaCanon S.d S.L (cs.beta (m'+1)) (m'+1) 0` and
`ν = cs.muAct (m'+1)`, the common coefficients `ak` being arbitrary) the difference to
`β A_i^win` vanishes. -/
theorem exists_window_field_hread_zero {k1 : ℕ} {Z : H.Comp (m' + 1)} (g : Geo S n R M)
    (hmK : m' + 1 ≤ K) (hL : 2 ≤ S.L) (hR : ∀ i, 1 ≤ i → i < m' + 1 → S.Rb ≤ R i)
    (hk1p : 1 ≤ k1) {ϱ : ℝ} (W : WindowPieces S.d S.L (M * n (m' + 1)) (m' + 1) ϱ)
    (hWh : W.Hyp) (href : ParentRefines (W.windowGenSet hWh) W.full)
    (hWfull : ∀ q, W.full.Ω q = (H.locGen Z M hmK hL hR).Ω q)
    (hWZ : W.Z = H.locFineFin Z (m' + 1)) (hWZk1 : W.Zk1 = H.locFineFin Z k1)
    {ι : Type*} (jf : ι → ℕ) (cf : ∀ i, H.Comp (jf i + 1))
    (hjf : ∀ i, k1 ≤ jf i ∧ jf i ≤ m') (hcf : ∀ i, cf i ∈ H.ancFin (jf i + 1) (m' + 1) Z)
    (hinj : Function.Injective fun i => (⟨jf i, cf i⟩ : Σ j, H.Comp (j + 1)))
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
    (hv : EuclideanSpace ℝ (Fin N)) :
    ∃ ψ : BlockV S.d S.L (M * n (m' + 1)) (m' + 1) → EuclideanSpace ℝ (Fin N),
      ∀ (φw : (W.windowGenSet hWh).Ω 1 × Fin N → ℂ) (ak : ℕ → ℝ) (νk βk : ℝ) (i : ι),
        (βk : ℂ) * actionRegionC (Xc i) ak νk
          (locData g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i))
            (hjK i) (ou i) (xu i) hv)
          (transportField (Gl := locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1
              (locComp_mem H (hjK i) (cf i)) (hjK i))
            (Equiv.cast (congrArg (Torus S.d) (piece_torus_eq g H.F.hnn hmK (hjf i).2)))
            (physicalWindowData W hWh href ψ (fun q => hv q)).Ψ φw) -
        (βk : ℂ) * actionRegionC (Xw i) ak νk (physicalWindowData W hWh href ψ (fun q => hv q))
          φw = 0 := by
  obtain ⟨ψ, hψ⟩ := exists_window_field_read_eq g hmK hL hR hk1p W hWh href hWfull hWZ hWZk1 jf cf
    hjf hcf hinj hjK Xw hXw Xc hXc ou xu hv
  exact ⟨ψ, fun φw ak νk βk i => by rw [hψ φw ak νk i, sub_self]⟩

end Main

end Balaban.LargeField
