/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Operators.QuietStepDataMeas
public import Balaban.LargeField.Base.BaseMainAction

/-!
# Borel measurability of the base main action on the real domain

The base main action `baseMainAction` (BASE-KERNEL §4) is the quiet main action `mainActionLoc` at
`k = 0` with the field `φ̂^X` (`baseFieldHat`): the retained spin on `Ω^c ∩ X` and the local background
`locPhi` elsewhere.  Using the glue of `QuietStepDataMeas` (`locDomain_glue`: the real domain of the
lifted data is a Borel set on which `locPhi` is continuous in the lifted configuration), the product
`1[loc data ∈ D_ℝ] · exp(-baseMainAction)` is Borel in `(ψ_1, I^new_0)`
(`measurable_baseDomainAction`).  The typing data is `BgHyp` of the local generating set at the
background mass `cs.muBg q`, for each level `q`, as in `measurable_domainAction`: a condition on the
constants and the generating set, not a proof step.
-/

@[expose] public section

namespace Balaban.LargeField

open MeasureTheory Balaban Balaban.Multiscale Balaban.Background RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} (g : Geo S n R M) (Hl : RegionHistory S n R k0 K)
  (Zc : Finset (Torus S.d (n (0 + 1))))
  (hZc : Zc ∈ comps (S.omega (0 + 1)) (Hl.F.Zp (0 + 1))) (hk : 0 + 1 ≤ K) (cs : OpConsts)
  (hrem : ∀ j, Hl.rem j = ∅) (hv : EuclideanSpace ℝ (Fin N))

open Classical in
/-- **The base main action times the real-domain indicator is Borel** in `(ψ_1, I^new_0)`. -/
theorem measurable_baseDomainAction
    (hbgB : ∀ q, BgHyp S.d S.L q (minSep S.L g.M1) cs.aw (cs.muBg q)) :
    Measurable fun p : OutT N R (locHist Hl M K (0 + 1) Zc) (0 + 1) ×
        NewCfg N (locHist Hl M K (0 + 1) Zc) 0 =>
      (if InUnionDomainR (locGen g Hl 0 Zc hZc hk) (bgC1 S.d S.L N) (cs.mu (0 + 1))
          (locData g Hl 0 Zc hZc hk p.1 p.2 hv) ∧
        InUnionDomainR (locGen g Hl 0 Zc hZc hk) (bgC1 S.d S.L N) (cs.muBg (0 + 1))
          (locData g Hl 0 Zc hZc hk p.1 p.2 hv) then (1 : ℝ) else 0) *
        Real.exp (-baseMainAction g Hl Zc hZc hk cs hrem p.1 p.2 hv) := by
  classical
  obtain ⟨E', Φ, φ, hE', hΦ, hφ, hmem, hms, hφe, hΦ1⟩ := locDomain_glue g Hl 0 Zc hZc hk cs hv hbgB
  let φ' : QY1 g N 0 × QMS g N 0 → Site S.d S.L (g.M1 * (g.c * n (0 + 1))) (0 + 1) →
      EuclideanSpace ℝ (Fin N) := fun r z =>
    if z ∈ Xfine g Hl 0 Zc ∧ z ∉ fineK1 g.M1 g.c (n (0 + 1)) S.L 0
        ((Hl.step 0).Omega : Set (Torus S.d (n (0 + 1)))) then
      WithLp.toLp 2 fun j => r.1.1 z j else φ r z
  have hφ' : ContinuousOn φ' E' := by
    refine continuousOn_pi.2 fun z => ?_
    by_cases hz : z ∈ Xfine g Hl 0 Zc ∧ z ∉ fineK1 g.M1 g.c (n (0 + 1)) S.L 0
        ((Hl.step 0).Omega : Set (Torus S.d (n (0 + 1))))
    · simp only [φ', hz]
      exact ((PiLp.continuous_toLp 2 _).comp (continuous_pi fun j =>
        (continuous_apply j).comp ((continuous_apply z).comp
          (continuous_fst.comp continuous_fst)))).continuousOn
    · simp only [φ', hz, ↓reduceIte]
      exact continuousOn_pi.1 hφ z
  have hφ'e : ∀ p, φ' (Φ p) = baseFieldHat g Hl Zc hZc hk cs p.1 p.2 hv := by
    intro p
    funext z
    simp only [φ', baseFieldHat]
    split_ifs
    · rw [hΦ1 p]
      simp [blockCfgOf]
    · exact congrFun (hφe p) z
  have hf1 := continuousOn_expAction (histGenLevel g Hl 0 hk hrem) cs.aw (cs.muAct (0 + 1)) hv
    (Xfine g Hl 0 Zc) (betaCanon S.d S.L (cs.beta (0 + 1)) (0 + 1) 0)
    (E := E') (ms := fun r => r.2) (φ := φ') continuous_snd hφ'
  have : OpensMeasurableSpace (QY1 g N 0 × QMS g N 0) := Prod.opensMeasurableSpace
  have hcomp := (measurable_indicator_mul hE' hf1).comp hΦ
  convert hcomp using 1
  funext p
  refine congrArg₂ (· * ·) ?_ ?_
  · exact if_congr (hmem p).symm rfl rfl
  · show _ = Real.exp (-(betaCanon S.d S.L (cs.beta (0 + 1)) (0 + 1) 0 *
      (actionG (histGenLevel g Hl 0 hk hrem) cs.aw (cs.muAct (0 + 1)) hv (Xfine g Hl 0 Zc)
        (Φ p).2 (φ' (Φ p)) + 1 / 4 * starBondE (Xfine g Hl 0 Zc) (φ' (Φ p)))))
    rw [hms p, hφ'e p]
    rfl

end Balaban.LargeField
