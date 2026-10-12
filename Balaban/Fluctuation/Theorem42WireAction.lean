/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.Theorem42WireData

/-!
# `mainActionLoc` as the star cube action (FLUCTUATION.md §4.2 Step 3, LFR Definition II.5.4)

For `k ≥ 1` and the local datum in the domain `𝒟`:

* `locData_isReal`: the lifted local datum is real;
* `locBg_eq_toFieldC`: the complex local background is the real field `locPhi` (on `Ω₁`);
* `cubeActionStar_locGen_eq`: `cubeActionStar` of the local family `G^{Z'}_{k+1}` at the local
  background is `A_{𝔹_{k+1}}(X_{Z'}; ψ, φ̄) + ¼ ∑_{st(X_{Z'})} |∂φ̄|²`, the bracket of `mainActionLoc`;
* `mainActionLoc_eq_cubeActionStar`: `mainActionLoc = β₀^{(k+1)} · cubeActionStar`.

The action data of `mainActionLoc` use the generating set `𝔹_{k+1}` of the history, the field is
built on the local family; the two have the same layers on `X_{Z'}` (`Theorem42WireLayers`), and
`cubeActionStar` is evaluated with the local family.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.LargeField Balaban.Background RegionHistory

set_option linter.unusedSectionVars false

section Step

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} (g : Geo S n R M) (Hl : RegionHistory S n R k0 K) (k : ℕ)
  (Zc : Finset (Torus S.d (n (k + 1)))) (hZc : Zc ∈ comps (S.omega (k + 1)) (Hl.F.Zp (k + 1))) (hk : k + 1 ≤ K)
  (hrem : ∀ j, Hl.rem j = ∅)

theorem locData_isReal (o : OutT N R (locHist Hl M K (k + 1) Zc) (k + 1))
    (xc : NewCfg N (locHist Hl M K (k + 1) Zc) k) (hv : EuclideanSpace ℝ (Fin N)) :
    (locData g Hl k Zc hZc hk o xc hv).IsReal := by
  classical
  intro z i
  constructor
  · by_cases hz : z ∈ dataSites (locGen g Hl k Zc hZc hk)
    · unfold locData
      rw [liftMixed_Ψ _ _ _ _ _ _ hz]
      unfold mixedLift blockLift
      split_ifs <;> simp [locLiftPsi, locLiftTheta, BlockCfg.toC, blockCfgOf]
    · rw [(locData g Hl k Zc hZc hk o xc hv).Ψ_zero z hz]; simp
  · by_cases hz : z ∈ (locGen g Hl k Zc hZc hk).Ω 1
    · unfold locData
      rw [liftMixed_h _ _ _ _ _ _ hz]; simp
    · rw [(locData g Hl k Zc hZc hk o xc hv).h_zero z hz]; simp

variable (cs : OpConsts)

theorem locBg_im_zero (H : BgHyp S.d S.L (k + 1) (minSep S.L g.M1) cs.aw (cs.mu (k + 1)))
    (o : OutT N R (locHist Hl M K (k + 1) Zc) (k + 1))
    (xc : NewCfg N (locHist Hl M K (k + 1) Zc) k) (hv : EuclideanSpace ℝ (Fin N))
    (hD : InUnionDomainC (locGen g Hl k Zc hZc hk) (bgC0 S.d S.L N) (bgC1 S.d S.L N) (cs.mu (k + 1))
      (locData g Hl k Zc hZc hk o xc hv)) (p) :
    (locBg g Hl k Zc hZc hk cs o xc hv p).im = 0 :=
  bgFieldC_im_zero H hD (locData_isReal g Hl k Zc hZc hk o xc hv) p

theorem locBg_eq_toFieldC (H : BgHyp S.d S.L (k + 1) (minSep S.L g.M1) cs.aw (cs.mu (k + 1)))
    (o : OutT N R (locHist Hl M K (k + 1) Zc) (k + 1))
    (xc : NewCfg N (locHist Hl M K (k + 1) Zc) k) (hv : EuclideanSpace ℝ (Fin N))
    (hD : InUnionDomainC (locGen g Hl k Zc hZc hk) (bgC0 S.d S.L N) (bgC1 S.d S.L N) (cs.mu (k + 1))
      (locData g Hl k Zc hZc hk o xc hv)) :
    locBg g Hl k Zc hZc hk cs o xc hv =
      toFieldC (locGen g Hl k Zc hZc hk) (locPhi g Hl k Zc hZc hk cs o xc hv) := by
  funext p
  obtain ⟨z, i⟩ := p
  have him := locBg_im_zero g Hl k Zc hZc hk cs H o xc hv hD (z, i)
  unfold toFieldC locPhi
  show _ = (((barField (locGen g Hl k Zc hZc hk) (locData g Hl k Zc hZc hk o xc hv).Ψ
    (locBg g Hl k Zc hZc hk cs o xc hv) z.1 i).re : ℝ) : ℂ)
  unfold barField
  simp only [z.2, ↓reduceDIte]
  exact (Complex.ext (by simp) (by simpa using him))

include hrem in
/-- **The star cube action of the local family at the local background is the bracket of
`mainActionLoc`** (LFR Definition II.5.4; FLUCTUATION §4.2, Step 3):
`A_{X_{Z'}}(D; φ^loc) = A_{𝔹_{k+1}}(X_{Z'}; ψ, φ̄) + ¼ ∑_{b ∈ st(X_{Z'})} |∂φ̄(b)|²`, for `k ≥ 1`, with
`D = lift_{k,k+1}(ψ_k, ψ_{k+1})` the datum of the local background, `φ^loc` the complex local
background, `φ̄` its real part extended by the data (`locPhi`), `ψ` the multiscale field of the
configuration (`psiLevel`). -/
theorem cubeActionStar_locGen_eq (hk1 : 1 ≤ k)
    (H : BgHyp S.d S.L (k + 1) (minSep S.L g.M1) cs.aw (cs.mu (k + 1)))
    (o : OutT N R (locHist Hl M K (k + 1) Zc) (k + 1))
    (xc : NewCfg N (locHist Hl M K (k + 1) Zc) k) (hv : EuclideanSpace ℝ (Fin N))
    (hD : InUnionDomainC (locGen g Hl k Zc hZc hk) (bgC0 S.d S.L N) (bgC1 S.d S.L N) (cs.mu (k + 1))
      (locData g Hl k Zc hZc hk o xc hv)) :
    cubeActionStar (locGen g Hl k Zc hZc hk) cs.aw (cs.muAct (k + 1)) (Xfine g Hl k Zc)
        (locData g Hl k Zc hZc hk o xc hv).Ψ (locData g Hl k Zc hZc hk o xc hv).h
        (locBg g Hl k Zc hZc hk cs o xc hv) =
      ((actionG (histGenLevel g Hl k hk hrem) cs.aw (cs.muAct (k + 1)) hv (Xfine g Hl k Zc)
          (psiLevel g Hl k hk
            (subMultiscaleField N (locHist Hl M K (k + 1) Zc) (k + 1)
              (Vblk R (locHist Hl M K (k + 1) Zc) (k + 1)) xc o))
          (locPhi g Hl k Zc hZc hk cs o xc hv) +
        1 / 4 * starBondE (Xfine g Hl k Zc) (locPhi g Hl k Zc hZc hk cs o xc hv) : ℝ) : ℂ) := by
  classical
  rw [locBg_eq_toFieldC g Hl k Zc hZc hk cs H o xc hv hD,
    actionG_histGenLevel_eq_locGen g Hl k Zc hZc hk hrem hk1]
  have hXΩ : Xfine g Hl k Zc ⊆ (locGen g Hl k Zc hZc hk).Ω 1 := fun z hz =>
    (locGen g Hl k Zc hZc hk).Ω_antitone le_rfl hk1 (by omega) (locGen_Ω_k g Hl k Zc hZc hk hk1 hz)
  refine cubeActionStar_eq_actionG_local (by have := H.hd; omega) _ hXΩ
    (fun j hj1 hjk z hz hzl y hy => Xfine_blk g Hl k Zc hZc hk hk1 hz hj1 hjk hzl hy)
    _ _ (locData_isReal g Hl k Zc hZc hk o xc hv) _ _ _ ?_ ?_ ?_
  · intro z hz i
    unfold locPhi
    show _ = (((barField (locGen g Hl k Zc hZc hk) (locData g Hl k Zc hZc hk o xc hv).Ψ
      (locBg g Hl k Zc hZc hk cs o xc hv) z i).re : ℝ) : ℂ)
    unfold barField
    simp only [hz, ↓reduceDIte]
    exact Complex.ext (by simp) (by simpa using (locData_isReal g Hl k Zc hZc hk o xc hv z i).1)
  · intro j hj1 hjk z hz hzl i
    rcases (layer_mem_iff_of_top _ (locGen_Ω_k g Hl k Zc hZc hk hk1 hz) hj1 hjk).1 hzl with
      ⟨hj, hnt⟩ | ⟨hj, ht⟩
    · obtain rfl := hj.symm
      exact locData_Ψ_k g Hl k Zc hZc hk hrem hk1 o xc hv hz
        (fun h => hnt ((locGen_Ω_top_iff g Hl k Zc hZc hk hz).2 h)) i
    · subst hj
      exact locData_Ψ_top g Hl k Zc hZc hk hk1 o xc hv hz
        ((locGen_Ω_top_iff g Hl k Zc hZc hk hz).1 ht) i
  · intro z hz i
    have hzΩ : z ∈ (locGen g Hl k Zc hZc hk).Ω 1 :=
      (locGen g Hl k Zc hZc hk).Ω_antitone le_rfl hk1 (by omega) (locGen_Ω_k g Hl k Zc hZc hk hk1 hz)
    unfold locData
    rw [liftMixed_h _ _ _ _ _ _ hzΩ]

include hrem in
/-- **`mainActionLoc` is `β₀` times the star cube action** (Definition II.5.4 = FLUCTUATION §4.2
Step 3's `β_{k+1} A*_{k+1}(X_{Z'})` at the local background). -/
theorem mainActionLoc_eq_cubeActionStar (hk1 : 1 ≤ k)
    (H : BgHyp S.d S.L (k + 1) (minSep S.L g.M1) cs.aw (cs.mu (k + 1)))
    (o : OutT N R (locHist Hl M K (k + 1) Zc) (k + 1))
    (xc : NewCfg N (locHist Hl M K (k + 1) Zc) k) (hv : EuclideanSpace ℝ (Fin N))
    (hD : InUnionDomainC (locGen g Hl k Zc hZc hk) (bgC0 S.d S.L N) (bgC1 S.d S.L N) (cs.mu (k + 1))
      (locData g Hl k Zc hZc hk o xc hv)) :
    ((mainActionLoc g Hl k Zc hZc hk cs hrem o xc hv : ℝ) : ℂ) =
      (betaCanon S.d S.L (cs.beta (k + 1)) (k + 1) 0 : ℂ) *
        cubeActionStar (locGen g Hl k Zc hZc hk) cs.aw (cs.muAct (k + 1)) (Xfine g Hl k Zc)
          (locData g Hl k Zc hZc hk o xc hv).Ψ (locData g Hl k Zc hZc hk o xc hv).h
          (locBg g Hl k Zc hZc hk cs o xc hv) := by
  rw [cubeActionStar_locGen_eq g Hl k Zc hZc hk hrem cs hk1 H o xc hv hD]
  unfold mainActionLoc
  push_cast
  rfl

end Step

end Balaban.Fluctuation
