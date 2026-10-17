/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, GPT-6-Sol (astra)
-/
module

public import Balaban.LargeField.R.RRemovedWindow
public import Balaban.LargeField.R.RRemovedFracMassCore

/-!
# Complete-action removed window bound

The extra fixed-window mass cost is supplied by
`removed_quotient_le_of_history_of_mass_bound`.  The hypothesis
`hcompleteAction` is the inner-integral estimate for the actual complete-background
inherited activities; the landed development has not established it for a route R-YM history.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open MeasureTheory Balaban RegionHistory ENNReal

section Window

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} (a : LocalHistory S n M K) (k : ℕ) (Z0 : Set (BlockAt S n M K k))
  (P : OpPkg N R a k) {t s z w : OutT N R a k → SubCfg N a k P.A → ℝ} {u c0 : OutT N R a k → ℝ}
  {r : OutZero N R a k Z0 → OutRest N R a k Z0 → ℝ} (EZ : ℝ)
  (ht : ∀ o x, 0 ≤ t o x) (hs : ∀ o x, 0 ≤ s o x) (hz : ∀ o x, 0 ≤ z o x)
  (hw : ∀ o x, 0 ≤ w o x) (hu : ∀ o, 0 ≤ u o) (hc0 : ∀ o, 0 ≤ c0 o) (hr : ∀ w y, 0 ≤ r w y)
  (htm : Measurable fun p : OutT N R a k × SubCfg N a k P.A => t p.1 p.2)
  (hsm : Measurable fun p : OutT N R a k × SubCfg N a k P.A => s p.1 p.2)
  (hzm : Measurable fun p : OutT N R a k × SubCfg N a k P.A => z p.1 p.2)
  (hwm : Measurable fun p : OutT N R a k × SubCfg N a k P.A => w p.1 p.2)
  (hum : Measurable u) (hc0m : Measurable c0)
  (hrm : Measurable fun q : OutZero N R a k Z0 × OutRest N R a k Z0 => r q.1 q.2)

/-- **The complete-action window integral with the positive-mass cost** (Lemma III.8.7,
removed outcome): `KerBound` with exponent
`κ^pre - C_R λ^{2d+1} - C_m D₀^d`.  The extra term is paid once per removed window.

Landed inputs used: `removedKernel_lintegral_le` (step (1)), `window_pointwise_le` (step (2)),
`vol_of_weighted` (step (3); the weighted volumes are `zero_group_vol_le`, `tree_group_vol_le`,
`weighted_prod_le`, with the shells and balls of volume at most `1`), the core bound `hcore`
(step (4), `core_lintegral_le` from `PkgBound`), and the arithmetic `removed_exponent_le`
(`lres_at_scale`).

Named source inputs for the actual complete-background activities, all with their exact statements above:
* `Θ`, `hΘ`: the measure preserving regrouping of the integration variables
  `(ψ_k↾Z, x, w)` into window variables `Wd`, core variables `Cr` and the variables `Jv` integrated
  first (the Gaussian-only variables and the inner `ψ_k↾Z₀`); the translation `ψ'' = ψ̃ - ψ⁰`
  is part of it;
* `hcompleteAction`: the composition identity (III.1.4) with the Gaussian integration (Lemma III.1.6) and
  (2.58′): the integral over `Jv` of `F` is at most `Core · e^{Re b_win} · const · frac`, where
  `frac` is the quotient of `removedFactor_le_restricted`; `hsupp`: it vanishes off the support
  set `E` of the window characteristic functions;
* `hbw` ((S0)), `hfrac` (`removedFactor_le_restricted` with the bounds of Lemma III.8.2, `hosc`),
  `hcore` ((D5) at scale `k₁`), `hvol` (the volumes of the groups), `hFr`, `hEZ`, `hnT`, `hnZ`,
  `hκ` (the bounds on the constants and the budget `c₁ ≥ C_W`, `c₂ ≥ C'_W`);
* `hb` (the exponent `b^pre` does not read `ψ_k↾Z₀`), `hu1` (`χ_{Z''} ≤ 1`). -/
theorem removedKernel_kerBound_of_complete_window (ok : S.Ok) (hx : 1 ≤ S.lam k)
    {Cvol CEt CE' Cnat D0 Cm : ℝ} (hCE' : 0 ≤ CE') (hD0 : 0 ≤ D0) (hCvol : 0 ≤ Cvol)
    (hCR : ((N : ℝ) / 2 * Real.log 2 + N * S.p0 + |Cvol| + 2 * CE') *
        ((S.M : ℝ) ^ S.d * (2 * S.c0 * S.Rb + 2 * S.c0 + 10) ^ S.d) +
        D0 ^ S.d * (N * S.p0 + |Cvol| + |CEt|) + Cnat + 10 ≤ S.CR)
    (hu1 : ∀ o, u o ≤ 1)
    (hb : ∀ (o o' : OutT N R a k) (x : SubCfg N a k P.A) (hv : EuclideanSpace ℝ (Fin N))
      (g : GIdx S n M K N → ℂ),
      (remZeroSplit a k Z0 o).2 = (remZeroSplit a k Z0 o').2 → P.T.b o x hv g = P.T.b o' x hv g)
    {Wd Cr Jv : Type*} [MeasurableSpace Wd] [MeasurableSpace Cr] [MeasurableSpace Jv]
    {μW : Measure Wd} {μC : Measure Cr} {μJ : Measure Jv} [SFinite μW] [SFinite μC] [SFinite μJ]
    (Θ : OutZ N R a k × (SubCfg N a k P.A × OutZero N R a k Z0) ≃ᵐ Wd × (Cr × Jv))
    (hΘ : MeasurePreserving Θ
      ((outPartMeasure N (Vblk R a k) (ZBlk a k)).prod
        ((subMeasure N a k P.A).prod (outPartMeasure N (Vblk R a k) (· ∈ Z0))))
      (μW.prod (μC.prod μJ)))
    (E : OutPar N R a k → Set Wd) (hE : ∀ par, MeasurableSet (E par))
    (F : EuclideanSpace ℝ (Fin N) → (GIdx S n M K N → ℂ) → OutPar N R a k →
      OutZ N R a k × (SubCfg N a k P.A × OutZero N R a k Z0) → ℝ≥0∞)
    (hF : ∀ hv g par oz x w', F hv g par (oz, x, w') = ENNReal.ofReal
      (c0 (mergeOut a k oz par) *
        (toRKernel a k P.T.K t s z w (remZeroMerge a k Z0
            (w', (remZeroSplit a k Z0 (mergeOut a k oz par)).2)) x hv *
          Real.exp (P.T.b (remZeroMerge a k Z0
            (w', (remZeroSplit a k Z0 (mergeOut a k oz par)).2)) x hv g).re) /
        remDen a k Z0 r (mergeOut a k oz par)))
    (Core : EuclideanSpace ℝ (Fin N) → (GIdx S n M K N → ℂ) → OutPar N R a k → Wd → Cr → ℝ≥0∞)
    (bw frac : EuclideanSpace ℝ (Fin N) → (GIdx S n M K N → ℂ) → OutPar N R a k → Wd → Cr → ℝ)
    {Bw Ck Fr Fz Lc κcore κpre nZ0 nTree : ℝ}
    (hcompleteAction : ∀ hv g par w c, ∫⁻ j, F hv g par (Θ.symm (w, c, j)) ∂μJ ≤ Core hv g par w c *
      ENNReal.ofReal (Real.exp (bw hv g par w c) * Real.exp Lc * frac hv g par w c))
    (hsupp : ∀ hv g par w c, w ∉ E par → ∫⁻ j, F hv g par (Θ.symm (w, c, j)) ∂μJ = 0)
    (hbw : ∀ hv g par w c, w ∈ E par → bw hv g par w c ≤ Bw)
    (hfrac0 : ∀ hv g par w c, 0 ≤ frac hv g par w c)
    (hfrac : ∀ hv g par w c, w ∈ E par → frac hv g par w c ≤ Real.exp Fr)
    (hcore : ∀ hv g, g ∈ l1Ball (GIdx S n M K N) → ∀ par w,
      ∫⁻ c, Core hv g par w c ∂μC ≤ ENNReal.ofReal (Real.exp (-κcore)))
    (hvol : ∀ par, ENNReal.ofReal (Real.exp (Lc + Fz)) * μW (E par) ≤
      ENNReal.ofReal (Real.exp (((N : ℝ) * S.p0 * Real.log (S.lam k) + Cvol) * (nZ0 + nTree))))
    (hFr : Fr ≤ Fz + CEt * D0 ^ S.d + Cnat * S.lam k ^ (2 * S.d + 1) + 4 + Ck + Cm * D0 ^ S.d)
    (hEZ : EZ ≤ (CE' * S.lam k + CE') * ((S.M : ℝ) * S.crit k) ^ S.d)
    (hnT : nTree ≤ ((S.M : ℝ) * S.crit k) ^ S.d) (hnZ : nZ0 ≤ D0 ^ S.d)
    (hκ : κpre ≤ κcore - (Bw + Ck)) :
    KerBound a k (removedKernel a k Z0 P t s z w u c0 r EZ ht hs hz hw hu hc0 hr htm hsm hzm hwm
      hum hc0m hrm) (κpre - S.CR * S.lam k ^ (2 * S.d + 1) - Cm * D0 ^ S.d) := by
  intro hv g hg par
  have h1 := removedKernel_lintegral_le a k Z0 P EZ ht hs hz hw hu hc0 hr htm hsm hzm hwm hum hc0m
    hrm hu1 hb hv g par (F hv g par) (hF hv g par)
  have hFm : Measurable (F hv g par) :=
    measurable_removedWindowF a k Z0 P htm hsm hzm hwm hc0m hrm hv g par (F hv g par)
      (hF hv g par)
  refine h1.trans ?_
  have := window_lintegral_le_exp S ok k hx N hCE' hD0 hCvol hCR Θ hΘ (E par) (hE par)
    (F hv g par) hFm (Core hv g par) (bw hv g par) (frac hv g par) (Fz := Fz) (Lc := Lc)
    (hcompleteAction hv g par) (hsupp hv g par) (hbw hv g par) (hfrac0 hv g par) (hfrac hv g par)
    (hcore hv g hg par) (hvol par) (γ := -(Cm * D0 ^ S.d)) (by linarith) hEZ hnT hnZ hκ
  convert this using 1

end Window

end Balaban.LargeField
