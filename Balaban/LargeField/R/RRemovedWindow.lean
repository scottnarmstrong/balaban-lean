/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Operators.KerBoundOn
public import Balaban.LargeField.R.RRemovedWindowKernel
public import Balaban.LargeField.R.RRemovedWindowPoint
public import Balaban.LargeField.R.RRemovedWindowVol
public import Balaban.LargeField.R.RRemovedLres
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The window integral (III.8.5) at `γ = 0` for the removed kernel (W905)

`notes/phase1/LF4R-PLAN.md`, leaf 6; Lemma III.8.7 of the reconstruction, removed outcome.

* `removed_exponent_le`: the exponent collection: the window-proportional terms are absorbed into
  `κ^pre` (`hκ`), the others are at most `L_res` (`lres_at_scale`), so the total is at most
  `-(κ^pre - C_R λ^{2d+1})`;
* `removedKernel_kerBound_of_window`: `KerBound a k (removedKernel …) (κ^pre - C_R λ^{2d+1})`
  from the steps (1)-(4): `removedKernel_lintegral_le` (the integration order, the factor
  `e^{EZ}`), `window_pointwise_le` (the exponentials, uniformly in the core variables),
  `vol_of_weighted` with the volumes of `RRemovedWindowVol.lean` (the window variables), and the
  core bound `hcore` ((D5), `core_lintegral_le`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open MeasureTheory Balaban RegionHistory ENNReal

/-- **The exponent collection of (III.8.5) at `γ = 0`**: with `c = N p₀ log λ + C_vol ≥ 0`, the
exponent `EZ + (B_w + L_c + F_r) + (c (#Z₀ + #tree) - (L_c + F_z)) - κ_core` is at most
`-(κ^pre - C_R λ^{2d+1})`, under the source bounds `F_r ≤ F_z + C_Ẽ D₀^d + C_♮ λ^{2d+1} + 4 + C_k`
((2.58′), `|Ẽ₀| ≤ C_Ẽ D₀^d`, `|C^♮_0| ≤ C_♮ λ^{2d+1}`), `EZ ≤ (C'_E λ + C'_E) (M crit_k)^d`,
`#tree ≤ (M crit_k)^d`, `#Z₀ ≤ D₀^d`, and `κ^pre ≤ κ_core - (B_w + C_k)` (`c₁ ≥ C_W`,
`c₂ ≥ C'_W`), together with (III.8.4) (`lres_at_scale`). -/
theorem removed_exponent_le (S : Setting) (ok : S.Ok) (k : ℕ) (hx : 1 ≤ S.lam k) (N : ℕ)
    {Cvol CEt CE' Cnat D0 : ℝ} (hCE' : 0 ≤ CE') (hD0 : 0 ≤ D0) (hCvol : 0 ≤ Cvol)
    (hCR : ((N : ℝ) / 2 * Real.log 2 + N * S.p0 + |Cvol| + 2 * CE') *
        ((S.M : ℝ) ^ S.d * (2 * S.c0 * S.Rb + 2 * S.c0 + 10) ^ S.d) +
        D0 ^ S.d * (N * S.p0 + |Cvol| + |CEt|) + Cnat + 10 ≤ S.CR)
    {EZ Bw Ck Fr Fz Lc κcore κpre nZ0 nTree : ℝ}
    (hFr : Fr ≤ Fz + CEt * D0 ^ S.d + Cnat * S.lam k ^ (2 * S.d + 1) + 4 + Ck)
    (hEZ : EZ ≤ (CE' * S.lam k + CE') * ((S.M : ℝ) * S.crit k) ^ S.d)
    (hnT : nTree ≤ ((S.M : ℝ) * S.crit k) ^ S.d) (hnZ : nZ0 ≤ D0 ^ S.d)
    (hκ : κpre ≤ κcore - (Bw + Ck)) :
    EZ + (Bw + Lc + Fr) +
        (((N : ℝ) * S.p0 * Real.log (S.lam k) + Cvol) * (nZ0 + nTree) - (Lc + Fz)) - κcore ≤
      -(κpre - S.CR * S.lam k ^ (2 * S.d + 1)) := by
  have hL := (lres_at_scale S ok k hx N hCE' hD0 hCR).1
  set Q : ℝ := ((S.M : ℝ) * S.crit k) ^ S.d with hQ
  set c : ℝ := (N : ℝ) * S.p0 * Real.log (S.lam k) + Cvol with hc
  have hQ0 : 0 ≤ Q := by rw [hQ]; positivity
  have hlog : 0 ≤ Real.log (S.lam k) := Real.log_nonneg hx
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  have h1 : c * nZ0 ≤ c * D0 ^ S.d := mul_le_mul_of_nonneg_left hnZ hc0
  have h2 : c * nTree ≤ c * Q := mul_le_mul_of_nonneg_left hnT hc0
  have h3 : 0 ≤ (N : ℝ) / 2 * Real.log 2 * Q := by
    have : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    positivity
  have h4 : ((N : ℝ) / 2 * Real.log 2 + c) * Q = (N : ℝ) / 2 * Real.log 2 * Q + c * Q := by ring
  have h5 : D0 ^ S.d * (c + CEt) = D0 ^ S.d * c + D0 ^ S.d * CEt := by ring
  have h6 : c * (nZ0 + nTree) = c * nZ0 + c * nTree := by ring
  nlinarith [hL, h1, h2, h3, h4, h5, h6, hFr, hEZ, hκ]

/-- **The window integral for a generic integrand** (steps (2)-(4) of (III.8.5), with the gain
`e^{-γ}`): if `∫_J F` is bounded by `Core · e^{bw} e^{Lc} frac` on the support set `E`, with the core
bound `hcore` and the volume bound `hvol`, then `e^{EZ} ∫ F ≤ e^{-(κ^pre - C_R λ^{2d+1} + γ)}`.
`γ = 0` is the removed kernel (`removedKernel_kerBound_of_window`). -/
theorem window_lintegral_le_exp (S : Setting) (ok : S.Ok) (k : ℕ) (hx : 1 ≤ S.lam k) (N : ℕ)
    {Cvol CEt CE' Cnat D0 : ℝ} (hCE' : 0 ≤ CE') (hD0 : 0 ≤ D0) (hCvol : 0 ≤ Cvol)
    (hCR : ((N : ℝ) / 2 * Real.log 2 + N * S.p0 + |Cvol| + 2 * CE') *
        ((S.M : ℝ) ^ S.d * (2 * S.c0 * S.Rb + 2 * S.c0 + 10) ^ S.d) +
        D0 ^ S.d * (N * S.p0 + |Cvol| + |CEt|) + Cnat + 10 ≤ S.CR)
    {Y Wd Cr Jv : Type*} [MeasurableSpace Y] [MeasurableSpace Wd] [MeasurableSpace Cr]
    [MeasurableSpace Jv] {μY : Measure Y} {μW : Measure Wd} {μC : Measure Cr} {μJ : Measure Jv}
    [SFinite μW] [SFinite μC] [SFinite μJ]
    (Θ : Y ≃ᵐ Wd × (Cr × Jv)) (hΘ : MeasurePreserving Θ μY (μW.prod (μC.prod μJ)))
    (E : Set Wd) (hE : MeasurableSet E) (F : Y → ℝ≥0∞) (hFm : Measurable F)
    (Core : Wd → Cr → ℝ≥0∞) (bw frac : Wd → Cr → ℝ)
    {Bw Ck Fr Fz Lc κcore κpre nZ0 nTree EZ γ : ℝ}
    (hid : ∀ w c, ∫⁻ j, F (Θ.symm (w, c, j)) ∂μJ ≤ Core w c *
      ENNReal.ofReal (Real.exp (bw w c) * Real.exp Lc * frac w c))
    (hsupp : ∀ w c, w ∉ E → ∫⁻ j, F (Θ.symm (w, c, j)) ∂μJ = 0)
    (hbw : ∀ w c, w ∈ E → bw w c ≤ Bw) (hfrac0 : ∀ w c, 0 ≤ frac w c)
    (hfrac : ∀ w c, w ∈ E → frac w c ≤ Real.exp Fr)
    (hcore : ∀ w, ∫⁻ c, Core w c ∂μC ≤ ENNReal.ofReal (Real.exp (-κcore)))
    (hvol : ENNReal.ofReal (Real.exp (Lc + Fz)) * μW E ≤
      ENNReal.ofReal (Real.exp (((N : ℝ) * S.p0 * Real.log (S.lam k) + Cvol) * (nZ0 + nTree))))
    (hFr : Fr + γ ≤ Fz + CEt * D0 ^ S.d + Cnat * S.lam k ^ (2 * S.d + 1) + 4 + Ck)
    (hEZ : EZ ≤ (CE' * S.lam k + CE') * ((S.M : ℝ) * S.crit k) ^ S.d)
    (hnT : nTree ≤ ((S.M : ℝ) * S.crit k) ^ S.d) (hnZ : nZ0 ≤ D0 ^ S.d)
    (hκ : κpre ≤ κcore - (Bw + Ck)) :
    ENNReal.ofReal (Real.exp EZ) * ∫⁻ p, F p ∂μY ≤
      ENNReal.ofReal (Real.exp (-(κpre - S.CR * S.lam k ^ (2 * S.d + 1) + γ))) := by
  have hpt := fun w c => window_pointwise_le (fun w c => ∫⁻ j, F (Θ.symm (w, c, j)) ∂μJ)
    Core E bw frac Bw Lc Fr hid hsupp hbw hfrac0 hfrac w c
  have h2 := lintegral_window_core_le Θ hΘ F hFm Core E hE
    (Bw + Lc + Fr) κcore (((N : ℝ) * S.p0 * Real.log (S.lam k) + Cvol) * (nZ0 + nTree) -
      (Lc + Fz)) hpt hcore (vol_of_weighted hvol)
  have h3 := removed_exponent_le S ok k hx N hCE' hD0 hCvol hCR (Lc := Lc) (Fr := Fr + γ) hFr hEZ
    hnT hnZ hκ
  calc ENNReal.ofReal (Real.exp EZ) * ∫⁻ p, F p ∂μY
      ≤ ENNReal.ofReal (Real.exp EZ) * ENNReal.ofReal (Real.exp (Bw + Lc + Fr +
          (((N : ℝ) * S.p0 * Real.log (S.lam k) + Cvol) * (nZ0 + nTree) - (Lc + Fz)) -
          κcore)) := by gcongr
    _ = ENNReal.ofReal (Real.exp (EZ + (Bw + Lc + Fr +
          (((N : ℝ) * S.p0 * Real.log (S.lam k) + Cvol) * (nZ0 + nTree) - (Lc + Fz)) -
          κcore))) := by
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
        linarith

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

/-- **The window integral (III.8.5) at `γ = 0` for the removed kernel** (Lemma III.8.7, removed
outcome): `KerBound a k (removedKernel …) (κ^pre - C_R λ^{2d+1})`, the input `hwin` of
`removed_kerBound_logC_of_window`.

Landed inputs used: `removedKernel_lintegral_le` (step (1)), `window_pointwise_le` (step (2)),
`vol_of_weighted` (step (3); the weighted volumes are `zero_group_vol_le`, `tree_group_vol_le`,
`weighted_prod_le`, with the shells and balls of volume at most `1`), the core bound `hcore`
(step (4), `core_lintegral_le` from `PkgBound`), and the arithmetic `removed_exponent_le`
(`lres_at_scale`).

Named inputs (the objects not yet available), all with their exact statements above:
* `Θ`, `hΘ`: the measure preserving regrouping of the integration variables
  `(ψ_k↾Z, x, w)` into window variables `Wd`, core variables `Cr` and the variables `Jv` integrated
  first (the Gaussian-only variables and the inner `ψ_k↾Z₀`); the translation `ψ'' = ψ̃ - ψ⁰`
  is part of it;
* `hid`: the composition identity (III.1.4) with the Gaussian integration (Lemma III.1.6) and
  (2.58′): the integral over `Jv` of `F` is at most `Core · e^{Re b_win} · const · frac`, where
  `frac` is the quotient of `removedFactor_le_restricted`; `hsupp`: it vanishes off the support
  set `E` of the window characteristic functions;
* `hbw` ((S0)), `hfrac` (`removedFactor_le_restricted` with the bounds of Lemma III.8.2, `hosc`),
  `hcore` ((D5) at scale `k₁`), `hvol` (the volumes of the groups), `hFr`, `hEZ`, `hnT`, `hnZ`,
  `hκ` (the bounds on the constants and the budget `c₁ ≥ C_W`, `c₂ ≥ C'_W`);
* `hb` (the exponent `b^pre` does not read `ψ_k↾Z₀`), `hu1` (`χ_{Z''} ≤ 1`). -/
theorem removedKernel_kerBoundOn_of_window (Hs : EuclideanSpace ℝ (Fin N) → Prop) (ok : S.Ok) (hx : 1 ≤ S.lam k)
    {Cvol CEt CE' Cnat D0 : ℝ} (hCE' : 0 ≤ CE') (hD0 : 0 ≤ D0) (hCvol : 0 ≤ Cvol)
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
    (hid : ∀ hv, Hs hv → ∀ g par w c, ∫⁻ j, F hv g par (Θ.symm (w, c, j)) ∂μJ ≤ Core hv g par w c *
      ENNReal.ofReal (Real.exp (bw hv g par w c) * Real.exp Lc * frac hv g par w c))
    (hsupp : ∀ hv, Hs hv → ∀ g par w c, w ∉ E par → ∫⁻ j, F hv g par (Θ.symm (w, c, j)) ∂μJ = 0)
    (hbw : ∀ hv, Hs hv → ∀ g par w c, w ∈ E par → bw hv g par w c ≤ Bw)
    (hfrac0 : ∀ hv, Hs hv → ∀ g par w c, 0 ≤ frac hv g par w c)
    (hfrac : ∀ hv, Hs hv → ∀ g par w c, w ∈ E par → frac hv g par w c ≤ Real.exp Fr)
    (hcore : ∀ hv, Hs hv → ∀ g, g ∈ l1Ball (GIdx S n M K N) → ∀ par w,
      ∫⁻ c, Core hv g par w c ∂μC ≤ ENNReal.ofReal (Real.exp (-κcore)))
    (hvol : ∀ par, ENNReal.ofReal (Real.exp (Lc + Fz)) * μW (E par) ≤
      ENNReal.ofReal (Real.exp (((N : ℝ) * S.p0 * Real.log (S.lam k) + Cvol) * (nZ0 + nTree))))
    (hFr : Fr ≤ Fz + CEt * D0 ^ S.d + Cnat * S.lam k ^ (2 * S.d + 1) + 4 + Ck)
    (hEZ : EZ ≤ (CE' * S.lam k + CE') * ((S.M : ℝ) * S.crit k) ^ S.d)
    (hnT : nTree ≤ ((S.M : ℝ) * S.crit k) ^ S.d) (hnZ : nZ0 ≤ D0 ^ S.d)
    (hκ : κpre ≤ κcore - (Bw + Ck)) :
    KerBoundOn a k (removedKernel a k Z0 P t s z w u c0 r EZ ht hs hz hw hu hc0 hr htm hsm hzm hwm
      hum hc0m hrm) (κpre - S.CR * S.lam k ^ (2 * S.d + 1)) Hs := by
  intro hv hhv g hg par
  have h1 := removedKernel_lintegral_le a k Z0 P EZ ht hs hz hw hu hc0 hr htm hsm hzm hwm hum hc0m
    hrm hu1 hb hv g par (F hv g par) (hF hv g par)
  have hFm : Measurable (F hv g par) :=
    measurable_removedWindowF a k Z0 P htm hsm hzm hwm hc0m hrm hv g par (F hv g par)
      (hF hv g par)
  refine h1.trans ?_
  have := window_lintegral_le_exp S ok k hx N hCE' hD0 hCvol hCR Θ hΘ (E par) (hE par)
    (F hv g par) hFm (Core hv g par) (bw hv g par) (frac hv g par) (Fz := Fz) (Lc := Lc)
    (hid hv hhv g par) (hsupp hv hhv g par) (hbw hv hhv g par) (hfrac0 hv hhv g par) (hfrac hv hhv g par)
    (hcore hv hhv g hg par) (hvol par) (γ := 0) (by linarith) hEZ hnT hnZ hκ
  simpa using this

theorem removedKernel_kerBound_of_window (ok : S.Ok) (hx : 1 ≤ S.lam k)
    {Cvol CEt CE' Cnat D0 : ℝ} (hCE' : 0 ≤ CE') (hD0 : 0 ≤ D0) (hCvol : 0 ≤ Cvol)
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
    (hid : ∀ hv g par w c, ∫⁻ j, F hv g par (Θ.symm (w, c, j)) ∂μJ ≤ Core hv g par w c *
      ENNReal.ofReal (Real.exp (bw hv g par w c) * Real.exp Lc * frac hv g par w c))
    (hsupp : ∀ hv g par w c, w ∉ E par → ∫⁻ j, F hv g par (Θ.symm (w, c, j)) ∂μJ = 0)
    (hbw : ∀ hv g par w c, w ∈ E par → bw hv g par w c ≤ Bw)
    (hfrac0 : ∀ hv g par w c, 0 ≤ frac hv g par w c)
    (hfrac : ∀ hv g par w c, w ∈ E par → frac hv g par w c ≤ Real.exp Fr)
    (hcore : ∀ hv g, g ∈ l1Ball (GIdx S n M K N) → ∀ par w,
      ∫⁻ c, Core hv g par w c ∂μC ≤ ENNReal.ofReal (Real.exp (-κcore)))
    (hvol : ∀ par, ENNReal.ofReal (Real.exp (Lc + Fz)) * μW (E par) ≤
      ENNReal.ofReal (Real.exp (((N : ℝ) * S.p0 * Real.log (S.lam k) + Cvol) * (nZ0 + nTree))))
    (hFr : Fr ≤ Fz + CEt * D0 ^ S.d + Cnat * S.lam k ^ (2 * S.d + 1) + 4 + Ck)
    (hEZ : EZ ≤ (CE' * S.lam k + CE') * ((S.M : ℝ) * S.crit k) ^ S.d)
    (hnT : nTree ≤ ((S.M : ℝ) * S.crit k) ^ S.d) (hnZ : nZ0 ≤ D0 ^ S.d)
    (hκ : κpre ≤ κcore - (Bw + Ck)) :
    KerBound a k (removedKernel a k Z0 P t s z w u c0 r EZ ht hs hz hw hu hc0 hr htm hsm hzm hwm
      hum hc0m hrm) (κpre - S.CR * S.lam k ^ (2 * S.d + 1)) := by
  exact kerBound_iff_on.2 (removedKernel_kerBoundOn_of_window a k Z0 P EZ ht hs hz hw hu hc0 hr htm hsm hzm hwm hum hc0m hrm (fun _ => True) ok hx hCE' hD0 hCvol hCR hu1 hb Θ hΘ E hE F hF Core bw frac (fun hv _ g par w c => hid hv g par w c) (fun hv _ g par w c => hsupp hv g par w c) (fun hv _ g par w c => hbw hv g par w c) (fun hv _ g par w c => hfrac0 hv g par w c) (fun hv _ g par w c => hfrac hv g par w c) (fun hv _ g hg par w => hcore hv g hg par w) hvol hFr hEZ hnT hnZ hκ)

end Window

end Balaban.LargeField
