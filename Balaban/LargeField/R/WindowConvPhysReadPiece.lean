/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.WindowConvPhysReadTransport
public import Balaban.LargeField.R.WindowConvPhysReadGeom
public import Balaban.LargeField.R.WindowRegion
public import Balaban.LargeField.R.ChiBridgeHist

/-!
# The local action of a piece, transported to the window generating set

P7 p. 501 (2.14)-(2.16); P6 pp. 6-7 (2.13)-(2.16).  For a piece `(j, c)` of the window of a ripe
component, the identification `e` of the level-`(m'+1)` torus with the level-`(j+1)` torus of
`locGen` carries the region `X_w` of the window generating set to `X_{Z'}`, preserves layer
indices and blocks, and maps neighbours of sites of `X_w` into `Ω₁` of `locGen`.  Hence the
restricted action of `X_{Z'}` at any local datum that agrees with the window datum on the sites, at
the field transported from a window field `φw`, equals the restricted action of `X_w` at `φw`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Fluctuation RegionHistory Balaban.Background
  Balaban.LargeField.ActionConv

theorem torusCast_equivCast_apply {d a b : ℕ} (h : a = b) (x : Torus d a) :
    Equiv.cast (congrArg (Torus d) h) x = torusCast h x := by
  subst h; rfl

theorem equivCast_add_single {d a b : ℕ} (h : a = b) (x : Torus d a) (μ : Fin d) :
    Equiv.cast (congrArg (Torus d) h) (x + Pi.single μ 1) =
      Equiv.cast (congrArg (Torus d) h) x + Pi.single μ 1 := by
  subst h; rfl

section Piece

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {H : RegionHistory S n R k0 K} {m' j : ℕ} {N : ℕ}

/-- **The local action of a piece equals the action of its region on the window** (P7 (2.14)-(2.16),
the read transport (a)-(d)).  If the local datum agrees with the window datum on the sites of the
piece (block values) and the external fields agree there, then the action of `X_{Z'}` at the local
datum and the field transported from `φw` is the action of the window region at `φw`. -/
theorem piece_actionRegionC_transport {k1 : ℕ} {Z : H.Comp (m' + 1)} (g : Geo S n R M)
    (hmK : m' + 1 ≤ K) (hL : 2 ≤ S.L) (hR : ∀ i, 1 ≤ i → i < m' + 1 → S.Rb ≤ R i)
    (hk1p : 1 ≤ k1) (hk1j : k1 ≤ j) (hj : j ≤ m') (hK : j + 1 ≤ K) {ϱ : ℝ}
    (W : WindowPieces S.d S.L (M * n (m' + 1)) (m' + 1) ϱ)
    (hWh : W.Hyp) (hWfull : ∀ q, W.full.Ω q = (H.locGen Z M hmK hL hR).Ω q)
    (hWZ : W.Z = H.locFineFin Z (m' + 1)) (hWZk1 : W.Zk1 = H.locFineFin Z k1) {c : H.Comp (j + 1)}
    (hc : c ∈ H.ancFin (j + 1) (m' + 1) Z)
    (Xw : Region (W.windowGenSet hWh))
    (hXw : ∀ x, x ∈ Xw.sites ↔
      torusCast (piece_torus_eq g H.F.hnn hmK hj) x ∈ Xfine g (H.locRH (j + 1) c) j c.1)
    (Xc : Region (locGen g (H.locRH (j + 1) c) j c.1 (locComp_mem H hK c) hK))
    (hXc : Xc.sites = Xfine g (H.locRH (j + 1) c) j c.1)
    (Dw : BgData (W.windowGenSet hWh) N)
    (Dl : BgData (locGen g (H.locRH (j + 1) c) j c.1 (locComp_mem H hK c) hK) N)
    (hΨ : ∀ x ∈ Xw.sites, Dl.Ψ (torusCast (piece_torus_eq g H.F.hnn hmK hj) x) = Dw.Ψ x)
    (hh : ∀ x ∈ Xw.sites, Dl.h (torusCast (piece_torus_eq g H.F.hnn hmK hj) x) = Dw.h x)
    (φw : (W.windowGenSet hWh).Ω 1 × Fin N → ℂ) (a : ℕ → ℝ) (ν : ℝ) :
    actionRegionC Xc a ν Dl
        (transportField (Gl := locGen g (H.locRH (j + 1) c) j c.1 (locComp_mem H hK c) hK)
          (Equiv.cast (congrArg (Torus S.d) (piece_torus_eq g H.F.hnn hmK hj))) Dw.Ψ φw) =
      actionRegionC Xw a ν Dw φw := by
  classical
  have hj1 : 1 ≤ j := by omega
  have hT := piece_torus_eq g H.F.hnn hmK hj
  set e := Equiv.cast (congrArg (Torus S.d) hT) with he_def
  have hea : ∀ x, e x = torusCast hT x := fun x => torusCast_equivCast_apply hT x
  obtain ⟨D, hD, hlayD⟩ := exists_region_Xfine_window (j := j) g hmK hL hR hk1p hk1j hj hK W hWh
    hWfull hWZ hWZk1 hc
  have hsites : ∀ x, x ∈ Xw.sites ↔ e x ∈ Xc.sites := fun x => by
    rw [hXw x, hXc, hea]
  have hlay : ∀ x ∈ Xw.sites, (locGen g (H.locRH (j + 1) c) j c.1 (locComp_mem H hK c) hK).layerIndex
      (e x) = (W.windowGenSet hWh).layerIndex x := fun x hx => by
    rw [hea]
    exact (hlayD x ((hD x).2 ((hXw x).1 hx))).symm
  refine actionRegionC_transport (Xw := Xw) (Xl := Xc) (e := e) (Dw := Dw) (Dl := Dl) (φw := φw)
    (fun x μ => equivCast_add_single hT x μ) hsites hlay ?_ ?_ (fun x hx => by rw [hea]; exact hΨ x hx)
    (fun x hx => by rw [hea]; exact hh x hx) a ν
  · intro x hx y
    have hxl : e x ∈ Xc.sites := (hsites x).1 hx
    have hq := hlay x hx
    obtain ⟨hq1, hqk, -⟩ := (locGen g (H.locRH (j + 1) c) j c.1 (locComp_mem H hK c) hK).layerIndex_spec
      (Xc.sub_Ω hxl)
    have hB := piece_block_eq g H.F.hnn hmK hj
      (q := (locGen g (H.locRH (j + 1) c) j c.1 (locComp_mem H hK c) hK).layerIndex (e x)) hqk
    rw [hq] at hB ⊢
    rw [GeneratingSet.mem_blk, GeneratingSet.mem_blk]
    have hy : y = e (e.symm y) := (e.apply_symm_apply y).symm
    rw [hy, e.symm_apply_apply, hea, hea]
    have hqw := hlay x hx
    rw [jBlock_torusCast (by omega) (by omega) hT hB, jBlock_torusCast (by omega) (by omega) hT hB]
    constructor
    · intro h; exact torusCast_injective hB h
    · intro h; rw [h]
  · intro x hx μ
    have hxl : e x ∈ Xfine g (H.locRH (j + 1) c) j c.1 := by
      have := (hsites x).1 hx
      rwa [hXc] at this
    have := locGen_nbr_mem_Ω_one g (H.locRH (j + 1) c) j c.1 (locComp_mem H hK c) hK hj1 hxl μ
    rw [equivCast_add_single hT x μ]
    refine ⟨this.1, ?_⟩
    have h2 : e (x - Pi.single μ 1) = e x - Pi.single μ 1 := by
      have := equivCast_add_single hT (x - Pi.single μ 1) μ
      rw [sub_add_cancel] at this
      rw [← he_def] at this
      rw [eq_sub_iff_add_eq, ← this]
    rw [h2]
    exact this.2

end Piece

end Balaban.LargeField
