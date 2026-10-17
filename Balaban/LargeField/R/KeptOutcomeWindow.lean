module

public import Balaban.LargeField.R.RRemovedWindow
public import Balaban.LargeField.R.Outcome
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The window integral (III.8.5) for the kept outcomes (LF4K-PLAN, statements 2-3)

`keptKernel_kerBound_of_window`: for a kernel `T` equal to the outcome kernel `outcomeKernel` of
`K^pre` (the first kind `ϰ_{i+1}`, any label of `Fin 5`), `(1.26)` with exponent
`κ^pre - C_R λ^{2d+1} + γ`.  The integral over `ψ_k↾Z` and the internal variables is the one of
`window_lintegral_le_exp` (steps (2)-(4) of the removed lane) with `e^{EZ} = 1` (no `Ẽ`-term, no
denominator): the kernel is `K^pre · weight`, so step (1) is the identity
`T.absW = ofReal (K^pre · weight · e^{Re b})`.  The gain `e^{-γ}` is carried by `hFr`
(`F_r + γ ≤ …`, Lemma III.5.3 on the support of the weight).
`keptKernel_one_kerBound`, `keptKernel_two_kerBound`, `keptKernel_three_kerBound` are the
labels `ϰ₁, ϰ₂, ϰ₃`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open MeasureTheory Balaban RegionHistory ENNReal

section Kept

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} (a : LocalHistory S n M K) (k : ℕ)

/-- **The window integral for a kept outcome kernel** (Lemma III.8.7, kept outcomes): see the module
docstring. -/
theorem keptKernel_kerBound_of_window (ok : S.Ok) (hx : 1 ≤ S.lam k)
    {Cvol CEt CE' Cnat D0 : ℝ} (hCE' : 0 ≤ CE') (hD0 : 0 ≤ D0) (hCvol : 0 ≤ Cvol)
    (hCR : ((N : ℝ) / 2 * Real.log 2 + N * S.p0 + |Cvol| + 2 * CE') *
        ((S.M : ℝ) ^ S.d * (2 * S.c0 * S.Rb + 2 * S.c0 + 10) ^ S.d) +
        D0 ^ S.d * (N * S.p0 + |Cvol| + |CEt|) + Cnat + 10 ≤ S.CR)
    (P : OpPkg N R a k) (t s z w u : OutT N R a k → SubCfg N a k P.A → ℝ) (i : Fin 5)
    (T : LFKernel (OutT N R a k) (SubCfg N a k P.A) (EuclideanSpace ℝ (Fin N))
      (GIdx S n M K N))
    (hTK : ∀ o x hv, T.K o x hv = outcomeKernel
      (fun p : OutT N R a k × SubCfg N a k P.A => P.T.K p.1 p.2 hv)
      (fun p => t p.1 p.2) (fun p => s p.1 p.2) (fun p => z p.1 p.2) (fun p => w p.1 p.2)
      (fun p => u p.1 p.2) (Outcome.kept i) (o, x))
    (hTb : T.b = P.T.b)
    {Wd Cr Jv : Type*} [MeasurableSpace Wd] [MeasurableSpace Cr] [MeasurableSpace Jv]
    {μW : Measure Wd} {μC : Measure Cr} {μJ : Measure Jv} [SFinite μW] [SFinite μC] [SFinite μJ]
    (Θ : OutZ N R a k × SubCfg N a k P.A ≃ᵐ Wd × (Cr × Jv))
    (hΘ : MeasurePreserving Θ
      ((outPartMeasure N (Vblk R a k) (ZBlk a k)).prod (subMeasure N a k P.A))
      (μW.prod (μC.prod μJ)))
    (E : OutPar N R a k → Set Wd) (hE : ∀ par, MeasurableSet (E par))
    (Core : EuclideanSpace ℝ (Fin N) → (GIdx S n M K N → ℂ) → OutPar N R a k → Wd → Cr → ℝ≥0∞)
    (bw frac : EuclideanSpace ℝ (Fin N) → (GIdx S n M K N → ℂ) → OutPar N R a k → Wd → Cr → ℝ)
    {Bw Ck Fr Fz Lc κcore κpre nZ0 nTree γ : ℝ}
    (hid : ∀ hv g par w' c, ∫⁻ j, ENNReal.ofReal (outcomeKernel
          (fun p : OutT N R a k × SubCfg N a k P.A => P.T.K p.1 p.2 hv)
          (fun p => t p.1 p.2) (fun p => s p.1 p.2) (fun p => z p.1 p.2) (fun p => w p.1 p.2)
          (fun p => u p.1 p.2) (Outcome.kept i) (mergeOut a k (Θ.symm (w', c, j)).1 par,
            (Θ.symm (w', c, j)).2) *
        Real.exp (P.T.b (mergeOut a k (Θ.symm (w', c, j)).1 par) (Θ.symm (w', c, j)).2 hv g).re) ∂μJ ≤ Core hv g par w' c *
      ENNReal.ofReal (Real.exp (bw hv g par w' c) * Real.exp Lc * frac hv g par w' c))
    (hsupp : ∀ hv g par w' c, w' ∉ E par → ∫⁻ j, ENNReal.ofReal (outcomeKernel
          (fun p : OutT N R a k × SubCfg N a k P.A => P.T.K p.1 p.2 hv)
          (fun p => t p.1 p.2) (fun p => s p.1 p.2) (fun p => z p.1 p.2) (fun p => w p.1 p.2)
          (fun p => u p.1 p.2) (Outcome.kept i) (mergeOut a k (Θ.symm (w', c, j)).1 par,
            (Θ.symm (w', c, j)).2) *
        Real.exp (P.T.b (mergeOut a k (Θ.symm (w', c, j)).1 par) (Θ.symm (w', c, j)).2 hv g).re) ∂μJ = 0)
    (hbw : ∀ hv g par w c, w ∈ E par → bw hv g par w c ≤ Bw)
    (hfrac0 : ∀ hv g par w c, 0 ≤ frac hv g par w c)
    (hfrac : ∀ hv g par w c, w ∈ E par → frac hv g par w c ≤ Real.exp Fr)
    (hcore : ∀ hv g, g ∈ l1Ball (GIdx S n M K N) → ∀ par w,
      ∫⁻ c, Core hv g par w c ∂μC ≤ ENNReal.ofReal (Real.exp (-κcore)))
    (hvol : ∀ par, ENNReal.ofReal (Real.exp (Lc + Fz)) * μW (E par) ≤
      ENNReal.ofReal (Real.exp (((N : ℝ) * S.p0 * Real.log (S.lam k) + Cvol) * (nZ0 + nTree))))
    (hFr : Fr + γ ≤ Fz + CEt * D0 ^ S.d + Cnat * S.lam k ^ (2 * S.d + 1) + 4 + Ck)
    (hnT : nTree ≤ ((S.M : ℝ) * S.crit k) ^ S.d) (hnZ : nZ0 ≤ D0 ^ S.d)
    (hκ : κpre ≤ κcore - (Bw + Ck)) :
    KerBound a k T (κpre - S.CR * S.lam k ^ (2 * S.d + 1) + γ) := by
  intro hv g hg par
  have hFm : Measurable fun p : OutZ N R a k × SubCfg N a k P.A =>
      T.absW (mergeOut a k p.1 par) p.2 hv g :=
    (T.measurable_absW hv g).comp
      (((measurable_mergeOut a k par).comp measurable_fst).prodMk measurable_snd)
  have hT : ∀ p : OutZ N R a k × SubCfg N a k P.A, T.absW (mergeOut a k p.1 par) p.2 hv g =
      ENNReal.ofReal (outcomeKernel
          (fun p : OutT N R a k × SubCfg N a k P.A => P.T.K p.1 p.2 hv)
          (fun p => t p.1 p.2) (fun p => s p.1 p.2) (fun p => z p.1 p.2) (fun p => w p.1 p.2)
          (fun p => u p.1 p.2) (Outcome.kept i) (mergeOut a k p.1 par, p.2) *
        Real.exp (P.T.b (mergeOut a k p.1 par) p.2 hv g).re) := fun p => by
    simp only [LFKernel.absW, hTK, hTb]
  have h := window_lintegral_le_exp S ok k hx N hCE' hD0 hCvol hCR Θ hΘ (E par) (hE par)
    (fun p => T.absW (mergeOut a k p.1 par) p.2 hv g) hFm (Core hv g par) (bw hv g par)
    (frac hv g par) (EZ := 0) (Fz := Fz) (Lc := Lc) (by simpa only [hT] using hid hv g par) (by simpa only [hT] using hsupp hv g par)
    (hbw hv g par) (hfrac0 hv g par) (hfrac hv g par) (hcore hv g hg par) (hvol par) hFr
    (by positivity) hnT hnZ hκ
  simp only [Real.exp_zero, ENNReal.ofReal_one, one_mul] at h
  rw [lintegral_prod _ hFm.aemeasurable] at h
  exact h

/-- **`ϰ_1`** (Lemma III.5.3 (a)): `keptKernel_kerBound_of_window` at the label `Outcome.kappa1`. -/
theorem keptKernel_one_kerBound (ok : S.Ok) (hx : 1 ≤ S.lam k)
    {Cvol CEt CE' Cnat D0 : ℝ} (hCE' : 0 ≤ CE') (hD0 : 0 ≤ D0) (hCvol : 0 ≤ Cvol)
    (hCR : ((N : ℝ) / 2 * Real.log 2 + N * S.p0 + |Cvol| + 2 * CE') *
        ((S.M : ℝ) ^ S.d * (2 * S.c0 * S.Rb + 2 * S.c0 + 10) ^ S.d) +
        D0 ^ S.d * (N * S.p0 + |Cvol| + |CEt|) + Cnat + 10 ≤ S.CR)
    (P : OpPkg N R a k) (t s z w u : OutT N R a k → SubCfg N a k P.A → ℝ)
    (T : LFKernel (OutT N R a k) (SubCfg N a k P.A) (EuclideanSpace ℝ (Fin N))
      (GIdx S n M K N))
    (hTK : ∀ o x hv, T.K o x hv = outcomeKernel
      (fun p : OutT N R a k × SubCfg N a k P.A => P.T.K p.1 p.2 hv)
      (fun p => t p.1 p.2) (fun p => s p.1 p.2) (fun p => z p.1 p.2) (fun p => w p.1 p.2)
      (fun p => u p.1 p.2) Outcome.kappa1 (o, x))
    (hTb : T.b = P.T.b)
    {Wd Cr Jv : Type*} [MeasurableSpace Wd] [MeasurableSpace Cr] [MeasurableSpace Jv]
    {μW : Measure Wd} {μC : Measure Cr} {μJ : Measure Jv} [SFinite μW] [SFinite μC] [SFinite μJ]
    (Θ : OutZ N R a k × SubCfg N a k P.A ≃ᵐ Wd × (Cr × Jv))
    (hΘ : MeasurePreserving Θ
      ((outPartMeasure N (Vblk R a k) (ZBlk a k)).prod (subMeasure N a k P.A))
      (μW.prod (μC.prod μJ)))
    (E : OutPar N R a k → Set Wd) (hE : ∀ par, MeasurableSet (E par))
    (Core : EuclideanSpace ℝ (Fin N) → (GIdx S n M K N → ℂ) → OutPar N R a k → Wd → Cr → ℝ≥0∞)
    (bw frac : EuclideanSpace ℝ (Fin N) → (GIdx S n M K N → ℂ) → OutPar N R a k → Wd → Cr → ℝ)
    {Bw Ck Fr Fz Lc κcore κpre nZ0 nTree γ : ℝ}
    (hid : ∀ hv g par w' c, ∫⁻ j, ENNReal.ofReal (outcomeKernel
          (fun p : OutT N R a k × SubCfg N a k P.A => P.T.K p.1 p.2 hv)
          (fun p => t p.1 p.2) (fun p => s p.1 p.2) (fun p => z p.1 p.2) (fun p => w p.1 p.2)
          (fun p => u p.1 p.2) Outcome.kappa1 (mergeOut a k (Θ.symm (w', c, j)).1 par,
            (Θ.symm (w', c, j)).2) *
        Real.exp (P.T.b (mergeOut a k (Θ.symm (w', c, j)).1 par) (Θ.symm (w', c, j)).2 hv g).re) ∂μJ ≤ Core hv g par w' c *
      ENNReal.ofReal (Real.exp (bw hv g par w' c) * Real.exp Lc * frac hv g par w' c))
    (hsupp : ∀ hv g par w' c, w' ∉ E par → ∫⁻ j, ENNReal.ofReal (outcomeKernel
          (fun p : OutT N R a k × SubCfg N a k P.A => P.T.K p.1 p.2 hv)
          (fun p => t p.1 p.2) (fun p => s p.1 p.2) (fun p => z p.1 p.2) (fun p => w p.1 p.2)
          (fun p => u p.1 p.2) Outcome.kappa1 (mergeOut a k (Θ.symm (w', c, j)).1 par,
            (Θ.symm (w', c, j)).2) *
        Real.exp (P.T.b (mergeOut a k (Θ.symm (w', c, j)).1 par) (Θ.symm (w', c, j)).2 hv g).re) ∂μJ = 0)
    (hbw : ∀ hv g par w c, w ∈ E par → bw hv g par w c ≤ Bw)
    (hfrac0 : ∀ hv g par w c, 0 ≤ frac hv g par w c)
    (hfrac : ∀ hv g par w c, w ∈ E par → frac hv g par w c ≤ Real.exp Fr)
    (hcore : ∀ hv g, g ∈ l1Ball (GIdx S n M K N) → ∀ par w,
      ∫⁻ c, Core hv g par w c ∂μC ≤ ENNReal.ofReal (Real.exp (-κcore)))
    (hvol : ∀ par, ENNReal.ofReal (Real.exp (Lc + Fz)) * μW (E par) ≤
      ENNReal.ofReal (Real.exp (((N : ℝ) * S.p0 * Real.log (S.lam k) + Cvol) * (nZ0 + nTree))))
    (hFr : Fr + γ ≤ Fz + CEt * D0 ^ S.d + Cnat * S.lam k ^ (2 * S.d + 1) + 4 + Ck)
    (hnT : nTree ≤ ((S.M : ℝ) * S.crit k) ^ S.d) (hnZ : nZ0 ≤ D0 ^ S.d)
    (hκ : κpre ≤ κcore - (Bw + Ck)) :
    KerBound a k T (κpre - S.CR * S.lam k ^ (2 * S.d + 1) + γ) :=
  keptKernel_kerBound_of_window a k ok hx hCE' hD0 hCvol hCR P t s z w u 0 T hTK hTb Θ hΘ E hE Core bw
    frac hid hsupp hbw hfrac0 hfrac hcore hvol hFr hnT hnZ hκ

/-- **`ϰ_2`** (Lemma III.5.3 (b)): `keptKernel_kerBound_of_window` at the label `Outcome.kappa2`. -/
theorem keptKernel_two_kerBound (ok : S.Ok) (hx : 1 ≤ S.lam k)
    {Cvol CEt CE' Cnat D0 : ℝ} (hCE' : 0 ≤ CE') (hD0 : 0 ≤ D0) (hCvol : 0 ≤ Cvol)
    (hCR : ((N : ℝ) / 2 * Real.log 2 + N * S.p0 + |Cvol| + 2 * CE') *
        ((S.M : ℝ) ^ S.d * (2 * S.c0 * S.Rb + 2 * S.c0 + 10) ^ S.d) +
        D0 ^ S.d * (N * S.p0 + |Cvol| + |CEt|) + Cnat + 10 ≤ S.CR)
    (P : OpPkg N R a k) (t s z w u : OutT N R a k → SubCfg N a k P.A → ℝ)
    (T : LFKernel (OutT N R a k) (SubCfg N a k P.A) (EuclideanSpace ℝ (Fin N))
      (GIdx S n M K N))
    (hTK : ∀ o x hv, T.K o x hv = outcomeKernel
      (fun p : OutT N R a k × SubCfg N a k P.A => P.T.K p.1 p.2 hv)
      (fun p => t p.1 p.2) (fun p => s p.1 p.2) (fun p => z p.1 p.2) (fun p => w p.1 p.2)
      (fun p => u p.1 p.2) Outcome.kappa2 (o, x))
    (hTb : T.b = P.T.b)
    {Wd Cr Jv : Type*} [MeasurableSpace Wd] [MeasurableSpace Cr] [MeasurableSpace Jv]
    {μW : Measure Wd} {μC : Measure Cr} {μJ : Measure Jv} [SFinite μW] [SFinite μC] [SFinite μJ]
    (Θ : OutZ N R a k × SubCfg N a k P.A ≃ᵐ Wd × (Cr × Jv))
    (hΘ : MeasurePreserving Θ
      ((outPartMeasure N (Vblk R a k) (ZBlk a k)).prod (subMeasure N a k P.A))
      (μW.prod (μC.prod μJ)))
    (E : OutPar N R a k → Set Wd) (hE : ∀ par, MeasurableSet (E par))
    (Core : EuclideanSpace ℝ (Fin N) → (GIdx S n M K N → ℂ) → OutPar N R a k → Wd → Cr → ℝ≥0∞)
    (bw frac : EuclideanSpace ℝ (Fin N) → (GIdx S n M K N → ℂ) → OutPar N R a k → Wd → Cr → ℝ)
    {Bw Ck Fr Fz Lc κcore κpre nZ0 nTree γ : ℝ}
    (hid : ∀ hv g par w' c, ∫⁻ j, ENNReal.ofReal (outcomeKernel
          (fun p : OutT N R a k × SubCfg N a k P.A => P.T.K p.1 p.2 hv)
          (fun p => t p.1 p.2) (fun p => s p.1 p.2) (fun p => z p.1 p.2) (fun p => w p.1 p.2)
          (fun p => u p.1 p.2) Outcome.kappa2 (mergeOut a k (Θ.symm (w', c, j)).1 par,
            (Θ.symm (w', c, j)).2) *
        Real.exp (P.T.b (mergeOut a k (Θ.symm (w', c, j)).1 par) (Θ.symm (w', c, j)).2 hv g).re) ∂μJ ≤ Core hv g par w' c *
      ENNReal.ofReal (Real.exp (bw hv g par w' c) * Real.exp Lc * frac hv g par w' c))
    (hsupp : ∀ hv g par w' c, w' ∉ E par → ∫⁻ j, ENNReal.ofReal (outcomeKernel
          (fun p : OutT N R a k × SubCfg N a k P.A => P.T.K p.1 p.2 hv)
          (fun p => t p.1 p.2) (fun p => s p.1 p.2) (fun p => z p.1 p.2) (fun p => w p.1 p.2)
          (fun p => u p.1 p.2) Outcome.kappa2 (mergeOut a k (Θ.symm (w', c, j)).1 par,
            (Θ.symm (w', c, j)).2) *
        Real.exp (P.T.b (mergeOut a k (Θ.symm (w', c, j)).1 par) (Θ.symm (w', c, j)).2 hv g).re) ∂μJ = 0)
    (hbw : ∀ hv g par w c, w ∈ E par → bw hv g par w c ≤ Bw)
    (hfrac0 : ∀ hv g par w c, 0 ≤ frac hv g par w c)
    (hfrac : ∀ hv g par w c, w ∈ E par → frac hv g par w c ≤ Real.exp Fr)
    (hcore : ∀ hv g, g ∈ l1Ball (GIdx S n M K N) → ∀ par w,
      ∫⁻ c, Core hv g par w c ∂μC ≤ ENNReal.ofReal (Real.exp (-κcore)))
    (hvol : ∀ par, ENNReal.ofReal (Real.exp (Lc + Fz)) * μW (E par) ≤
      ENNReal.ofReal (Real.exp (((N : ℝ) * S.p0 * Real.log (S.lam k) + Cvol) * (nZ0 + nTree))))
    (hFr : Fr + γ ≤ Fz + CEt * D0 ^ S.d + Cnat * S.lam k ^ (2 * S.d + 1) + 4 + Ck)
    (hnT : nTree ≤ ((S.M : ℝ) * S.crit k) ^ S.d) (hnZ : nZ0 ≤ D0 ^ S.d)
    (hκ : κpre ≤ κcore - (Bw + Ck)) :
    KerBound a k T (κpre - S.CR * S.lam k ^ (2 * S.d + 1) + γ) :=
  keptKernel_kerBound_of_window a k ok hx hCE' hD0 hCvol hCR P t s z w u 1 T hTK hTb Θ hΘ E hE Core bw
    frac hid hsupp hbw hfrac0 hfrac hcore hvol hFr hnT hnZ hκ

/-- **`ϰ_3`** (Lemma III.5.3 (c)): `keptKernel_kerBound_of_window` at the label `Outcome.kappa3`. -/
theorem keptKernel_three_kerBound (ok : S.Ok) (hx : 1 ≤ S.lam k)
    {Cvol CEt CE' Cnat D0 : ℝ} (hCE' : 0 ≤ CE') (hD0 : 0 ≤ D0) (hCvol : 0 ≤ Cvol)
    (hCR : ((N : ℝ) / 2 * Real.log 2 + N * S.p0 + |Cvol| + 2 * CE') *
        ((S.M : ℝ) ^ S.d * (2 * S.c0 * S.Rb + 2 * S.c0 + 10) ^ S.d) +
        D0 ^ S.d * (N * S.p0 + |Cvol| + |CEt|) + Cnat + 10 ≤ S.CR)
    (P : OpPkg N R a k) (t s z w u : OutT N R a k → SubCfg N a k P.A → ℝ)
    (T : LFKernel (OutT N R a k) (SubCfg N a k P.A) (EuclideanSpace ℝ (Fin N))
      (GIdx S n M K N))
    (hTK : ∀ o x hv, T.K o x hv = outcomeKernel
      (fun p : OutT N R a k × SubCfg N a k P.A => P.T.K p.1 p.2 hv)
      (fun p => t p.1 p.2) (fun p => s p.1 p.2) (fun p => z p.1 p.2) (fun p => w p.1 p.2)
      (fun p => u p.1 p.2) Outcome.kappa3 (o, x))
    (hTb : T.b = P.T.b)
    {Wd Cr Jv : Type*} [MeasurableSpace Wd] [MeasurableSpace Cr] [MeasurableSpace Jv]
    {μW : Measure Wd} {μC : Measure Cr} {μJ : Measure Jv} [SFinite μW] [SFinite μC] [SFinite μJ]
    (Θ : OutZ N R a k × SubCfg N a k P.A ≃ᵐ Wd × (Cr × Jv))
    (hΘ : MeasurePreserving Θ
      ((outPartMeasure N (Vblk R a k) (ZBlk a k)).prod (subMeasure N a k P.A))
      (μW.prod (μC.prod μJ)))
    (E : OutPar N R a k → Set Wd) (hE : ∀ par, MeasurableSet (E par))
    (Core : EuclideanSpace ℝ (Fin N) → (GIdx S n M K N → ℂ) → OutPar N R a k → Wd → Cr → ℝ≥0∞)
    (bw frac : EuclideanSpace ℝ (Fin N) → (GIdx S n M K N → ℂ) → OutPar N R a k → Wd → Cr → ℝ)
    {Bw Ck Fr Fz Lc κcore κpre nZ0 nTree γ : ℝ}
    (hid : ∀ hv g par w' c, ∫⁻ j, ENNReal.ofReal (outcomeKernel
          (fun p : OutT N R a k × SubCfg N a k P.A => P.T.K p.1 p.2 hv)
          (fun p => t p.1 p.2) (fun p => s p.1 p.2) (fun p => z p.1 p.2) (fun p => w p.1 p.2)
          (fun p => u p.1 p.2) Outcome.kappa3 (mergeOut a k (Θ.symm (w', c, j)).1 par,
            (Θ.symm (w', c, j)).2) *
        Real.exp (P.T.b (mergeOut a k (Θ.symm (w', c, j)).1 par) (Θ.symm (w', c, j)).2 hv g).re) ∂μJ ≤ Core hv g par w' c *
      ENNReal.ofReal (Real.exp (bw hv g par w' c) * Real.exp Lc * frac hv g par w' c))
    (hsupp : ∀ hv g par w' c, w' ∉ E par → ∫⁻ j, ENNReal.ofReal (outcomeKernel
          (fun p : OutT N R a k × SubCfg N a k P.A => P.T.K p.1 p.2 hv)
          (fun p => t p.1 p.2) (fun p => s p.1 p.2) (fun p => z p.1 p.2) (fun p => w p.1 p.2)
          (fun p => u p.1 p.2) Outcome.kappa3 (mergeOut a k (Θ.symm (w', c, j)).1 par,
            (Θ.symm (w', c, j)).2) *
        Real.exp (P.T.b (mergeOut a k (Θ.symm (w', c, j)).1 par) (Θ.symm (w', c, j)).2 hv g).re) ∂μJ = 0)
    (hbw : ∀ hv g par w c, w ∈ E par → bw hv g par w c ≤ Bw)
    (hfrac0 : ∀ hv g par w c, 0 ≤ frac hv g par w c)
    (hfrac : ∀ hv g par w c, w ∈ E par → frac hv g par w c ≤ Real.exp Fr)
    (hcore : ∀ hv g, g ∈ l1Ball (GIdx S n M K N) → ∀ par w,
      ∫⁻ c, Core hv g par w c ∂μC ≤ ENNReal.ofReal (Real.exp (-κcore)))
    (hvol : ∀ par, ENNReal.ofReal (Real.exp (Lc + Fz)) * μW (E par) ≤
      ENNReal.ofReal (Real.exp (((N : ℝ) * S.p0 * Real.log (S.lam k) + Cvol) * (nZ0 + nTree))))
    (hFr : Fr + γ ≤ Fz + CEt * D0 ^ S.d + Cnat * S.lam k ^ (2 * S.d + 1) + 4 + Ck)
    (hnT : nTree ≤ ((S.M : ℝ) * S.crit k) ^ S.d) (hnZ : nZ0 ≤ D0 ^ S.d)
    (hκ : κpre ≤ κcore - (Bw + Ck)) :
    KerBound a k T (κpre - S.CR * S.lam k ^ (2 * S.d + 1) + γ) :=
  keptKernel_kerBound_of_window a k ok hx hCE' hD0 hCvol hCR P t s z w u 2 T hTK hTb Θ hΘ E hE Core bw
    frac hid hsupp hbw hfrac0 hfrac hcore hvol hFr hnT hnZ hκ

end Kept

end Balaban.LargeField
