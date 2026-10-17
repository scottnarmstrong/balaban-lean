/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RRemovedHidBridge
public import Balaban.Fluctuation.Theorem42WireAction

/-!
# The main action of a quiet step is the real part of the restricted action of a region (W937)

`notes/phase1/LF4R-PLAN.md` §8.5 items (1)–(4).  Items (1) and (2) are landed in
`Fluctuation/Theorem42WireLayers.lean`, `Theorem42WireData.lean` and `Theorem42WireAction.lean`
(`mainActionLoc_eq_cubeActionStar`: same layers of `locGen` and `histGenLevel` on `Xfine`, the hypotheses of
`cubeActionStar_eq_actionG` for `locData`, `locPhi`).  Here:

* `exists_region_Xfine`: `Xfine` is the site set of a `Region` of `locGen` (`Ω₁`-containment and block
  closure from `Xfine_blk`);
* `mainActionLoc_eq_re_actionRegionC`: `mainActionLoc = Re (β^{(k+1)}_0 · actionRegionC D …)` at the local
  data `locData` and the local background `locBg`, for every region `D` with site set `Xfine`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.LargeField Balaban.Background RegionHistory
  Balaban.LargeField.ActionConv

section Bridge

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} (g : Geo S n R M) (Hl : RegionHistory S n R k0 K) (k : ℕ)
  (Zc : Finset (Torus S.d (n (k + 1)))) (hZc : Zc ∈ comps (S.omega (k + 1)) (Hl.F.Zp (k + 1)))
  (hk : k + 1 ≤ K) (hrem : ∀ j, Hl.rem j = ∅)

theorem exists_region_Xfine (hk1 : 1 ≤ k) :
    ∃ D : Region (locGen g Hl k Zc hZc hk), D.sites = Xfine g Hl k Zc := by
  have hXΩ : Xfine g Hl k Zc ⊆ (locGen g Hl k Zc hZc hk).Ω 1 := fun z hz =>
    (locGen g Hl k Zc hZc hk).Ω_antitone le_rfl hk1 (by omega) (locGen_Ω_k g Hl k Zc hZc hk hk1 hz)
  refine ⟨⟨Xfine g Hl k Zc, hXΩ, fun x hx y hy => ?_⟩, rfl⟩
  obtain ⟨hj1, hjk, hxl⟩ := (locGen g Hl k Zc hZc hk).layerIndex_spec (hXΩ hx)
  exact Xfine_blk g Hl k Zc hZc hk hk1 hx hj1 hjk hxl hy

variable (cs : OpConsts)

include hrem in
theorem mainActionLoc_eq_re_actionRegionC (hk1 : 1 ≤ k)
    (H : BgHyp S.d S.L (k + 1) (minSep S.L g.M1) cs.aw (cs.mu (k + 1)))
    (o : OutT N R (locHist Hl M K (k + 1) Zc) (k + 1))
    (xc : NewCfg N (locHist Hl M K (k + 1) Zc) k) (hv : EuclideanSpace ℝ (Fin N))
    (hD : InUnionDomainC (locGen g Hl k Zc hZc hk) (bgC0 S.d S.L N) (bgC1 S.d S.L N) (cs.mu (k + 1))
      (locData g Hl k Zc hZc hk o xc hv))
    (D : Region (locGen g Hl k Zc hZc hk)) (hDs : D.sites = Xfine g Hl k Zc) :
    mainActionLoc g Hl k Zc hZc hk cs hrem o xc hv =
      ((betaCanon S.d S.L (cs.beta (k + 1)) (k + 1) 0 : ℂ) *
        actionRegionC D cs.aw (cs.muAct (k + 1)) (locData g Hl k Zc hZc hk o xc hv)
          (locBg g Hl k Zc hZc hk cs o xc hv)).re := by
  have h := mainActionLoc_eq_cubeActionStar g Hl k Zc hZc hk hrem cs hk1 H o xc hv hD
  rw [← hDs, cubeActionStar_eq_actionRegionC] at h
  have h2 := congrArg Complex.re h
  rwa [Complex.ofReal_re] at h2

end Bridge

end Balaban.Fluctuation
