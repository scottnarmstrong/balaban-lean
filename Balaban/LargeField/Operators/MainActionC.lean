/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.Theorem42WireAction

/-!
# The physical action of a new large-field region at a complex source (ruling R2)

Ruling R2 (route R-YM′; `notes/phase1/Q13-YM.md` §5, `notes/phase1/astra/RADIUS.md` Part II §1):
the main action of a new large-field region is evaluated at the complete local background (the
background mass `cs.muBg`), and its factor `e^{-𝒜}` is continued to a complex source `h`.

* `locDataC`, `locBgC`: the datum and the complete local background at a complex source `h`
  (the datum `lift_{k,k+1}(ψ_k, ψ_{k+1})` with the constant source `h` on `Ω₁`);
* `mainActionLocC`: `𝒜_{k+1}(Z'; ψ, h) = β^{(k+1)}_0 A*_{X_{Z'}}(D_h; φ_h)`, the star cube action
  (complex bilinear in the field, the source and the background) at the datum `D_h` and the
  complete background `φ_h`;
* `mainActionLocC_ofReal`: at a real source it is the landed real action `mainActionLoc`
  (`k ≥ 1`, the datum in the domain `𝒟` of the background mass);
* `mainActionLocC_analytic`: **the holomorphic physical-action factor** — one function, analytic at
  every complex source whose datum lies in `𝒟`, equal to `mainActionLocC` there (Theorem 7.2
  analyticity, `theorem72_analytic`, and the holomorphy of the star cube action);
* `exp_neg_mainActionLocC_analytic`: the same for the factor `e^{-𝒜}`.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background RegionHistory Balaban.Fluctuation

set_option linter.unusedSectionVars false

section Step

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} (g : Geo S n R M) (Hl : RegionHistory S n R k0 K) (k : ℕ)
  (Zc : Finset (Torus S.d (n (k + 1)))) (hZc : Zc ∈ comps (S.omega (k + 1)) (Hl.F.Zp (k + 1)))
  (hk : k + 1 ≤ K) (cs : OpConsts)

/-- The datum `lift_{k,k+1}(ψ_k, ψ_{k+1})` of the local background at a complex source `h`. -/
noncomputable def locDataC (o : OutT N R (locHist Hl M K (k + 1) Zc) (k + 1))
    (x : NewCfg N (locHist Hl M K (k + 1) Zc) k) (h : Fin N → ℂ) :
    BgData (locGen g Hl k Zc hZc hk) N :=
  liftMixed (locGen g Hl k Zc hZc hk)
    ((isCubeUnion_fineK1 (Hl.step k).Omega).isBlockUnion (le_refl _))
    (genBoundaryLocal_top_subset (Hl.step k) g.hc (Hl.F.hnn k (by omega)) Hl.F.ok.two_le_L
      (g.three_L_le_floor Hl (k - 1)) (Hl.F.stepGeom (by omega)).rad.omega_rho
      (Omega_compl_subset_Zpre' k (Hl.step k) _ _) hZc)
    (locLiftPsi g Hl k Zc hk x).toC (locLiftTheta g Hl k Zc hk o).toC h

/-- At a real source the datum is the landed `locData`. -/
theorem locDataC_ofReal (o : OutT N R (locHist Hl M K (k + 1) Zc) (k + 1))
    (x : NewCfg N (locHist Hl M K (k + 1) Zc) k) (hv : EuclideanSpace ℝ (Fin N)) :
    locDataC g Hl k Zc hZc hk o x (fun i => (hv i : ℂ)) = locData g Hl k Zc hZc hk o x hv := rfl

/-- The complete local background at a complex source `h` (background mass `cs.muBg (k + 1)`). -/
noncomputable def locBgC (o : OutT N R (locHist Hl M K (k + 1) Zc) (k + 1))
    (x : NewCfg N (locHist Hl M K (k + 1) Zc) k) (h : Fin N → ℂ) :
    (locGen g Hl k Zc hZc hk).Ω 1 × Fin N → ℂ :=
  bgFieldC (locGen g Hl k Zc hZc hk) cs.aw (cs.muBg (k + 1)) (bgC0 S.d S.L N)
    (locDataC g Hl k Zc hZc hk o x h)

/-- At a real source the background is the landed local background `locBg`. -/
theorem locBgC_ofReal (o : OutT N R (locHist Hl M K (k + 1) Zc) (k + 1))
    (x : NewCfg N (locHist Hl M K (k + 1) Zc) k) (hv : EuclideanSpace ℝ (Fin N)) :
    locBgC g Hl k Zc hZc hk cs o x (fun i => (hv i : ℂ)) = locBg g Hl k Zc hZc hk cs o x hv := rfl

/-- **The physical action of the new large-field region at a complex source** (ruling R2):
`𝒜_{k+1}(Z'; ψ, h) = β^{(k+1)}_0 A*_{X_{Z'}}(D_h; φ_h)` with the star cube action of the local
family at the datum `D_h = locDataC h` and the complete local background `φ_h = locBgC h`; the
mass of the action is `cs.muAct (k + 1)`. -/
noncomputable def mainActionLocC (o : OutT N R (locHist Hl M K (k + 1) Zc) (k + 1))
    (x : NewCfg N (locHist Hl M K (k + 1) Zc) k) (h : Fin N → ℂ) : ℂ :=
  (betaCanon S.d S.L (cs.beta (k + 1)) (k + 1) 0 : ℂ) *
    cubeActionStar (locGen g Hl k Zc hZc hk) cs.aw (cs.muAct (k + 1)) (Xfine g Hl k Zc)
      (locDataC g Hl k Zc hZc hk o x h).Ψ (locDataC g Hl k Zc hZc hk o x h).h
      (locBgC g Hl k Zc hZc hk cs o x h)

variable (hrem : ∀ j, Hl.rem j = ∅)

/-- **At a real source the complex action is the real action** (`k ≥ 1`, the datum in the domain
`𝒟` of the background mass, the background hypotheses `BgHyp` of that mass). -/
theorem mainActionLocC_ofReal (hk1 : 1 ≤ k)
    (H : BgHyp S.d S.L (k + 1) (minSep S.L g.M1) cs.aw (cs.muBg (k + 1)))
    (o : OutT N R (locHist Hl M K (k + 1) Zc) (k + 1))
    (x : NewCfg N (locHist Hl M K (k + 1) Zc) k) (hv : EuclideanSpace ℝ (Fin N))
    (hD : InUnionDomainC (locGen g Hl k Zc hZc hk) (bgC0 S.d S.L N) (bgC1 S.d S.L N)
      (cs.muBg (k + 1)) (locData g Hl k Zc hZc hk o x hv)) :
    mainActionLocC g Hl k Zc hZc hk cs o x (fun i => (hv i : ℂ)) =
      ((mainActionLoc g Hl k Zc hZc hk cs hrem o x hv : ℝ) : ℂ) :=
  (mainActionLoc_eq_cubeActionStar g Hl k Zc hZc hk hrem cs hk1 H o x hv hD).symm

/-- The source field of the datum at a complex source: `h` on `Ω₁`, `0` elsewhere. -/
theorem locDataC_h (o : OutT N R (locHist Hl M K (k + 1) Zc) (k + 1))
    (x : NewCfg N (locHist Hl M K (k + 1) Zc) k) (h : Fin N → ℂ)
    (z : Torus S.d (g.M1 * (g.c * n (k + 1)) * S.L ^ (k + 1))) :
    (locDataC g Hl k Zc hZc hk o x h).h z =
      if z ∈ (locGen g Hl k Zc hZc hk).Ω 1 then h else 0 := by
  split_ifs with hz
  · exact liftMixed_h _ _ _ _ _ _ hz
  · exact (locDataC g Hl k Zc hZc hk o x h).h_zero z hz

/-- The source field of the datum depends analytically (affinely) on the source. -/
theorem analyticAt_locDataC_h (o : OutT N R (locHist Hl M K (k + 1) Zc) (k + 1))
    (x : NewCfg N (locHist Hl M K (k + 1) Zc) k) (h₀ : Fin N → ℂ) :
    AnalyticAt ℂ (fun h => (locDataC g Hl k Zc hZc hk o x h).h) h₀ := by
  classical
  have e : (fun h => (locDataC g Hl k Zc hZc hk o x h).h) =
      fun h z => if z ∈ (locGen g Hl k Zc hZc hk).Ω 1 then h else 0 :=
    funext fun h => funext fun z => locDataC_h g Hl k Zc hZc hk o x h z
  rw [e]
  refine analyticAt_pi_iff.2 fun z => ?_
  by_cases hz : z ∈ (locGen g Hl k Zc hZc hk).Ω 1
  · simp only [hz, ↓reduceIte]
    exact analyticAt_id
  · simp only [hz, ↓reduceIte]
    exact analyticAt_const

/-- **The holomorphic physical-action factor** (ruling R2): there is one function of the complex
source, analytic at every source whose datum lies in the domain `𝒟` of the background mass, which
is the action `mainActionLocC` there. -/
theorem mainActionLocC_analytic
    (H : BgHyp S.d S.L (k + 1) (minSep S.L g.M1) cs.aw (cs.muBg (k + 1)))
    (o : OutT N R (locHist Hl M K (k + 1) Zc) (k + 1))
    (x : NewCfg N (locHist Hl M K (k + 1) Zc) k) :
    ∃ Φ : (Fin N → ℂ) → ℂ,
      AnalyticOnNhd ℂ Φ {h | InUnionDomainC (locGen g Hl k Zc hZc hk) (bgC0 S.d S.L N)
        (bgC1 S.d S.L N) (cs.muBg (k + 1)) (locDataC g Hl k Zc hZc hk o x h)} ∧
      ∀ h, InUnionDomainC (locGen g Hl k Zc hZc hk) (bgC0 S.d S.L N) (bgC1 S.d S.L N)
          (cs.muBg (k + 1)) (locDataC g Hl k Zc hZc hk o x h) →
        Φ h = mainActionLocC g Hl k Zc hZc hk cs o x h := by
  obtain ⟨F, hF, hFe⟩ := theorem72_analytic (G := locGen g Hl k Zc hZc hk) H
  set D := fun h => locDataC g Hl k Zc hZc hk o x h with hDdef
  refine ⟨fun h => (betaCanon S.d S.L (cs.beta (k + 1)) (k + 1) 0 : ℂ) *
    cubeActionStar (locGen g Hl k Zc hZc hk) cs.aw (cs.muAct (k + 1)) (Xfine g Hl k Zc)
      (D h).Ψ (D h).h (F ((D h).Ψ, (D h).h)).1, ?_, ?_⟩
  · intro h₀ hh₀
    have hΨ : (fun h => (D h).Ψ) = fun _ => (D h₀).Ψ := rfl
    have hΨa : AnalyticAt ℂ (fun h => (D h).Ψ) h₀ := by rw [hΨ]; exact analyticAt_const
    have hha : AnalyticAt ℂ (fun h => (D h).h) h₀ := analyticAt_locDataC_h g Hl k Zc hZc hk o x h₀
    have hraw : AnalyticAt ℂ (fun h => ((D h).Ψ, (D h).h)) h₀ := hΨa.prod hha
    have hFa : AnalyticAt ℂ F ((D h₀).Ψ, (D h₀).h) := hF _ ⟨D h₀, hh₀, rfl⟩
    have hφ : AnalyticAt ℂ (fun h => (F ((D h).Ψ, (D h).h)).1) h₀ :=
      analyticAt_fst.comp (AnalyticAt.comp (f := fun h => ((D h).Ψ, (D h).h)) hFa hraw)
    exact analyticAt_const.mul (cubeActionStar_analyticAt _ hΨa hha hφ)
  · intro h hh
    have e := hFe (D h) hh
    simp only [e]
    rfl

/-- **The holomorphic factor `e^{-𝒜}`** of the new large-field region at a complex source. -/
theorem exp_neg_mainActionLocC_analytic
    (H : BgHyp S.d S.L (k + 1) (minSep S.L g.M1) cs.aw (cs.muBg (k + 1)))
    (o : OutT N R (locHist Hl M K (k + 1) Zc) (k + 1))
    (x : NewCfg N (locHist Hl M K (k + 1) Zc) k) :
    ∃ Φ : (Fin N → ℂ) → ℂ,
      AnalyticOnNhd ℂ Φ {h | InUnionDomainC (locGen g Hl k Zc hZc hk) (bgC0 S.d S.L N)
        (bgC1 S.d S.L N) (cs.muBg (k + 1)) (locDataC g Hl k Zc hZc hk o x h)} ∧
      ∀ h, InUnionDomainC (locGen g Hl k Zc hZc hk) (bgC0 S.d S.L N) (bgC1 S.d S.L N)
          (cs.muBg (k + 1)) (locDataC g Hl k Zc hZc hk o x h) →
        Φ h = Complex.exp (-mainActionLocC g Hl k Zc hZc hk cs o x h) := by
  obtain ⟨Φ, hΦ, hΦe⟩ := mainActionLocC_analytic g Hl k Zc hZc hk cs H o x
  exact ⟨fun h => Complex.exp (-Φ h), fun h hh => (hΦ h hh).neg.cexp,
    fun h hh => by simp only [hΦe h hh]⟩

end Step

end Balaban.LargeField
