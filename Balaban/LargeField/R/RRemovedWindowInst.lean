/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RRemovedWindow
public import Balaban.LargeField.R.RRemovedFracInst
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The window integral for the removed kernel: the pointwise inputs from the landed results (W910)

`notes/phase1/LF4R-PLAN.md`, leaf 6; blocker 4.  The inputs `hbw`, `hvol`, `hnZ`, `hnT`, `hFr` of
`removedKernel_kerBound_of_window` (`hfrac` is `removed_quotient_le_of_history`):

* `window_bw_le`: (S0) summed over the steps `j ∈ [k₁, k)` plus `|C_{k₁,k}| ≤ C₁₅ Σ_j |X_j|_{j+1}`
  (`quietKernel_bound`, `window_conversion`) give `Re b_win ≤ B_w`,
  `B_w = Σ_j (C_b log β_j + C_b B₀) |X_j|_{j+1} + C₁₅ Σ_j |X_j|_{j+1}`;
* `window_hvol_of_groups`: `hvol` for the window variables `(ψ_k↾Z₀, tree group, shells and balls)`
  from `zero_group_vol_le`, `tree_group_vol_le`, `weighted_prod_le`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open MeasureTheory Balaban RegionHistory ENNReal ActionConv

/-- **(S0) summed over the window steps**: `bw = Σ_j bq_j + Re C`, `bq_j ≤ cb_j v_j`,
`|Re C| ≤ C₁₅ Σ_j v_j` give `bw ≤ Σ_j cb_j v_j + C₁₅ Σ_j v_j`. -/
theorem window_bw_le {ι : Type*} (J : Finset ι) {bw Cre c15 : ℝ} (bq cb v : ι → ℝ)
    (hsplit : bw = ∑ j ∈ J, bq j + Cre) (hS0 : ∀ j ∈ J, bq j ≤ cb j * v j)
    (hC : |Cre| ≤ c15 * ∑ j ∈ J, v j) :
    bw ≤ ∑ j ∈ J, cb j * v j + c15 * ∑ j ∈ J, v j := by
  rw [hsplit]
  have h1 : ∑ j ∈ J, bq j ≤ ∑ j ∈ J, cb j * v j := Finset.sum_le_sum hS0
  linarith [le_abs_self Cre]

section Vol

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} (a : LocalHistory S n M K) (k : ℕ) (Z0 : Set (BlockAt S n M K k))

/-- **The weighted volume of the window variables** (`hvol` of `removedKernel_kerBound_of_window`, one
`par`): the window variables are `(ψ_k↾Z₀, tree group, rest)` with the balls of `χ_{Z₀}` (centre `cen`),
the spanning-tree balls of `χ̃_k` and a set `E₃` of volume at most `1` (shells, balls of `ψ''`,
`ψ_{k₁}`).  With `e^{F_z} = e^{(N/2) log β |Z₀|}`, `e^{L_c} = ∏ (w_z/π)^{N/2}` and
`p₀ = A₀ λ^{p₀}`, the weighted volume is at most `e^{(N p₀ log λ + C_vol)(#Z₀ + #tree)}`
(`zero_group_vol_le`, `tree_group_vol_le`, `weighted_prod_le`). -/
theorem window_hvol_of_groups (hN : 0 < N) {W3 : Type*} [MeasurableSpace W3] {μ3 : Measure W3}
    [SFinite μ3] {E3 : Set W3} (hE3 : μ3 E3 ≤ 1)
    (cen : {y : BlockAt S n M K k // y ∈ Vblk R a k ∧ y ∈ Z0} → EuclideanSpace ℝ (Fin N))
    (Zt : Set (Torus S.d (M * n K * S.L ^ K))) (δk : ℝ) (V2 : Set (BlockAt S n M K k))
    (P2 : BlockAt S n M K k → Prop) {ρ : Type} (e : ρ → EuclideanSpace ℝ (Fin N))
    (cb : ρ → BlockAt S n M K k)
    (par : {y : BlockAt S n M K k // y ∈ V2 ∧ P2 y} →
      {y : BlockAt S n M K k // y ∈ V2 ∧ P2 y} ⊕ ρ)
    (rk : {y : BlockAt S n M K k // y ∈ V2 ∧ P2 y} → ℕ)
    (hrk : ∀ i j, par i = Sum.inl j → rk j < rk i)
    (hreg : ∀ i : {y : BlockAt S n M K k // y ∈ V2 ∧ P2 y},
      BlockSub (S := S) (n := n) (M := M) (K := K) k i.1 (tildeRegion a k Zt))
    (hregc : ∀ c, BlockSub (S := S) (n := n) (M := M) (K := K) k (cb c) (tildeRegion a k Zt))
    (hadj : ∀ i j, par i = Sum.inl j → AdjT i.1 j.1)
    (hadjc : ∀ i c, par i = Sum.inr c → AdjT i.1 (cb c))
    {β A0 lam C6 : ℝ} (pe : ℕ) (hβ : 0 < β) (hC6 : 0 ≤ C6) (hA0 : 0 < A0) (hlam : 0 < lam)
    (hδ : δk = β ^ (-(1 / 2 : ℝ)) * (A0 * lam ^ pe))
    (wz : {y : BlockAt S n M K k // y ∈ V2 ∧ P2 y} → ℝ) (hw0 : ∀ i, 0 ≤ wz i)
    (hw : ∀ i, wz i ≤ 2 * β) {Cvol : ℝ}
    (hcc : Real.log ((volume (Metric.ball (0 : EuclideanSpace ℝ (Fin N)) 1)).toReal *
      (max 3 C6) ^ N * A0 ^ N) ≤ Cvol) {Lc Fz : ℝ}
    (hLc : Real.exp Lc = ∏ i, (wz i / Real.pi) ^ ((N : ℝ) / 2))
    (hFz : Fz = (N : ℝ) / 2 * Real.log β *
      Nat.card {y : BlockAt S n M K k // y ∈ Vblk R a k ∧ y ∈ Z0}) :
    ENNReal.ofReal (Real.exp (Lc + Fz)) *
      ((outPartMeasure N (Vblk R a k) (· ∈ Z0)).prod
        ((outPartMeasure N V2 P2).prod μ3))
      ({o | ∀ i, ‖o i - cen i‖ < C6 * β ^ (-(1 / 2 : ℝ)) * (A0 * lam ^ pe)} ×ˢ
        ({o | ∃ ψ : BlockAt S n M K k → EuclideanSpace ℝ (Fin N),
          (∀ i, ψ i.1 = o i) ∧ (∀ c, ψ (cb c) = e c) ∧ ChiTildeProp a k Zt δk ψ} ×ˢ E3)) ≤
    ENNReal.ofReal (Real.exp (((N : ℝ) * pe * Real.log lam + Cvol) *
      ((Nat.card {y : BlockAt S n M K k // y ∈ Vblk R a k ∧ y ∈ Z0} : ℝ) +
        Nat.card {y : BlockAt S n M K k // y ∈ V2 ∧ P2 y}))) := by
  have h1 := zero_group_vol_le hN (Vblk R a k) (· ∈ Z0) cen (β := β) (A0 := A0) (lam := lam)
    (C6 := C6) pe hβ hC6 hA0 hlam hcc
  have h2 := tree_group_vol_le hN a k Zt δk V2 P2 e cb par rk hrk hreg hregc hadj hadjc pe hβ hA0 hlam
    hδ wz hw0 hw hcc
  have h3 : ENNReal.ofReal (Real.exp 0) * μ3 E3 ≤ ENNReal.ofReal (Real.exp 0) := by
    simpa using hE3
  subst hFz
  rw [← hLc] at h2
  have h23 := weighted_prod_le h2 h3
  have h := weighted_prod_le h1 h23
  rw [show Lc + (N : ℝ) / 2 * Real.log β * Nat.card {y : BlockAt S n M K k // y ∈ Vblk R a k ∧ y ∈ Z0} =
    (N : ℝ) / 2 * Real.log β * Nat.card {y : BlockAt S n M K k // y ∈ Vblk R a k ∧ y ∈ Z0} + (Lc + 0) by ring]
  refine h.trans (le_of_eq ?_)
  congr 2
  ring

end Vol

section Instance

/-- `outPartMeasure` is finite, hence `σ`-finite. -/
instance outPartMeasure_sigmaFinite {α : Type} [Finite α] (N : ℕ) (V : Set α) (P : α → Prop) :
    SigmaFinite (outPartMeasure N V P) := by
  unfold outPartMeasure
  have := Fintype.ofFinite {y : α // y ∈ V ∧ P y}
  infer_instance

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

/-- **`removedKernel_kerBound_of_window` with the pointwise inputs discharged.**  The window variables are
`(ψ_k↾Z₀, tree group, rest)`, `E par` the product of the balls of `χ_{Z₀}`, the spanning-tree balls of
`χ̃_k` and a set `E₃` of volume at most `1` (`hEdef`).

Discharged: `hvol` (`window_hvol_of_groups`), `hnZ` and `hnT` (`card_boxFinset_le`, `removed_cubeVol_le`, with
the typing data `hZcard`, `hTcard` that the blocks of the groups lie in `Z₀` and in `Z`), `hbw`
(`window_bw_le`, from the per-step (S0) `hS0` of `quietKernel_bound` and `|C_{k₁,k}| ≤ C₁₅ Σ_j |X_j|_{j+1}` of
`window_conversion`), `hFr` (merged in `hfrac`, the output of `removed_quotient_le_of_history`).
Still inputs: `Θ`, `hΘ`, `hid`, `hsupp`, `hb`, `hcore`, `hκ`, `hEZ` (see the report: the landed `E_le` gives
`E_k ≤ C_E λ^{2d+1}`, not `E_k ≲ λ`). -/
theorem removedKernel_kerBound_of_window_inst (ok : S.Ok) (hx : 1 ≤ S.lam k)
    {Cvol CEt CE' Cnat Lc : ℝ} {D : ℕ} (hN : 0 < N) (hCE' : 0 ≤ CE') (hCvol : 0 ≤ Cvol)
    (hCR : ((N : ℝ) / 2 * Real.log 2 + N * S.p0 + |Cvol| + 2 * CE') *
        ((S.M : ℝ) ^ S.d * (2 * S.c0 * S.Rb + 2 * S.c0 + 10) ^ S.d) +
        (D : ℝ) ^ S.d * (N * S.p0 + |Cvol| + |CEt|) + Cnat + 10 ≤ S.CR)
    (hu1 : ∀ o, u o ≤ 1)
    (hb : ∀ (o o' : OutT N R a k) (x : SubCfg N a k P.A) (hv : EuclideanSpace ℝ (Fin N))
      (g : GIdx S n M K N → ℂ),
      (remZeroSplit a k Z0 o).2 = (remZeroSplit a k Z0 o').2 → P.T.b o x hv g = P.T.b o' x hv g)
    {Cr Jv W3 : Type*} [MeasurableSpace Cr] [MeasurableSpace Jv] [MeasurableSpace W3]
    {μC : Measure Cr} {μJ : Measure Jv} {μ3 : Measure W3} [SFinite μC] [SFinite μJ] [SFinite μ3]
    (V2 : Set (BlockAt S n M K k)) (P2 : BlockAt S n M K k → Prop)
    (Θ : OutZ N R a k × (SubCfg N a k P.A × OutZero N R a k Z0) ≃ᵐ
      (OutZero N R a k Z0 × (OutPart N V2 P2 × W3)) × (Cr × Jv))
    (hΘ : MeasurePreserving Θ
      ((outPartMeasure N (Vblk R a k) (ZBlk a k)).prod
        ((subMeasure N a k P.A).prod (outPartMeasure N (Vblk R a k) (· ∈ Z0))))
      (((outPartMeasure N (Vblk R a k) (· ∈ Z0)).prod
        ((outPartMeasure N V2 P2).prod μ3)).prod (μC.prod μJ)))
    (cen : OutPar N R a k → {y : BlockAt S n M K k // y ∈ Vblk R a k ∧ y ∈ Z0} →
      EuclideanSpace ℝ (Fin N))
    (Zt : Set (Torus S.d (M * n K * S.L ^ K))) (δk : ℝ) {ρ : Type}
    (e : OutPar N R a k → ρ → EuclideanSpace ℝ (Fin N)) (cb : ρ → BlockAt S n M K k)
    (parT : {y : BlockAt S n M K k // y ∈ V2 ∧ P2 y} →
      {y : BlockAt S n M K k // y ∈ V2 ∧ P2 y} ⊕ ρ)
    (rk : {y : BlockAt S n M K k // y ∈ V2 ∧ P2 y} → ℕ)
    (hrk : ∀ i j, parT i = Sum.inl j → rk j < rk i)
    (hreg : ∀ i : {y : BlockAt S n M K k // y ∈ V2 ∧ P2 y},
      BlockSub (S := S) (n := n) (M := M) (K := K) k i.1 (tildeRegion a k Zt))
    (hregc : ∀ c, BlockSub (S := S) (n := n) (M := M) (K := K) k (cb c) (tildeRegion a k Zt))
    (hadj : ∀ i j, parT i = Sum.inl j → AdjT i.1 j.1)
    (hadjc : ∀ i c, parT i = Sum.inr c → AdjT i.1 (cb c))
    {β0 A0 C6 : ℝ} (hβ0 : 0 < β0) (hC6 : 0 ≤ C6) (hA0 : 0 < A0)
    (hδ : δk = betaK S.d S.L k β0 ^ (-(1 / 2 : ℝ)) * (A0 * S.lam k ^ S.p0))
    (wz : {y : BlockAt S n M K k // y ∈ V2 ∧ P2 y} → ℝ) (hw0 : ∀ i, 0 ≤ wz i)
    (hw2 : ∀ i, wz i ≤ 2 * betaK S.d S.L k β0)
    (hcc : Real.log ((volume (Metric.ball (0 : EuclideanSpace ℝ (Fin N)) 1)).toReal *
      (max 3 C6) ^ N * A0 ^ N) ≤ Cvol)
    (hLc : Real.exp Lc = ∏ i, (wz i / Real.pi) ^ ((N : ℝ) / 2))
    (E3 : OutPar N R a k → Set W3) (hE3 : ∀ par, μ3 (E3 par) ≤ 1)
    (E : OutPar N R a k → Set (OutZero N R a k Z0 × (OutPart N V2 P2 × W3)))
    (hEdef : ∀ par, E par =
      {o | ∀ i, ‖o i - cen par i‖ < C6 * betaK S.d S.L k β0 ^ (-(1 / 2 : ℝ)) * (A0 * S.lam k ^ S.p0)} ×ˢ
        ({o | ∃ ψ : BlockAt S n M K k → EuclideanSpace ℝ (Fin N),
          (∀ i, ψ i.1 = o i) ∧ (∀ c, ψ (cb c) = e par c) ∧ ChiTildeProp a k Zt δk ψ} ×ˢ E3 par))
    (hE : ∀ par, MeasurableSet (E par))
    (F : EuclideanSpace ℝ (Fin N) → (GIdx S n M K N → ℂ) → OutPar N R a k →
      OutZ N R a k × (SubCfg N a k P.A × OutZero N R a k Z0) → ℝ≥0∞)
    (hF : ∀ hv g par oz x w', F hv g par (oz, x, w') = ENNReal.ofReal
      (c0 (mergeOut a k oz par) *
        (toRKernel a k P.T.K t s z w (remZeroMerge a k Z0
            (w', (remZeroSplit a k Z0 (mergeOut a k oz par)).2)) x hv *
          Real.exp (P.T.b (remZeroMerge a k Z0
            (w', (remZeroSplit a k Z0 (mergeOut a k oz par)).2)) x hv g).re) /
        remDen a k Z0 r (mergeOut a k oz par)))
    (Core : EuclideanSpace ℝ (Fin N) → (GIdx S n M K N → ℂ) → OutPar N R a k →
      OutZero N R a k Z0 × (OutPart N V2 P2 × W3) → Cr → ℝ≥0∞)
    (bw frac : EuclideanSpace ℝ (Fin N) → (GIdx S n M K N → ℂ) → OutPar N R a k →
      OutZero N R a k Z0 × (OutPart N V2 P2 × W3) → Cr → ℝ)
    {Bw Ck Fz κcore κpre c15 : ℝ}
    (hid : ∀ hv g par w c, ∫⁻ j, F hv g par (Θ.symm (w, c, j)) ∂μJ ≤ Core hv g par w c *
      ENNReal.ofReal (Real.exp (bw hv g par w c) * Real.exp Lc * frac hv g par w c))
    (hsupp : ∀ hv g par w c, w ∉ E par → ∫⁻ j, F hv g par (Θ.symm (w, c, j)) ∂μJ = 0)
    {ι : Type*} (J : Finset ι) (bq : ι → EuclideanSpace ℝ (Fin N) → (GIdx S n M K N → ℂ) →
      OutPar N R a k → OutZero N R a k Z0 × (OutPart N V2 P2 × W3) → Cr → ℝ)
    (Cre : EuclideanSpace ℝ (Fin N) → (GIdx S n M K N → ℂ) → OutPar N R a k →
      OutZero N R a k Z0 × (OutPart N V2 P2 × W3) → Cr → ℝ) (cbw vw : ι → ℝ)
    (hBw : Bw = ∑ j ∈ J, cbw j * vw j + c15 * ∑ j ∈ J, vw j)
    (hsplit : ∀ hv g par w c, w ∈ E par → bw hv g par w c = ∑ j ∈ J, bq j hv g par w c + Cre hv g par w c)
    (hS0 : ∀ hv g par w c, w ∈ E par → ∀ j ∈ J, bq j hv g par w c ≤ cbw j * vw j)
    (hC : ∀ hv g par w c, w ∈ E par → |Cre hv g par w c| ≤ c15 * ∑ j ∈ J, vw j)
    (hfrac0 : ∀ hv g par w c, 0 ≤ frac hv g par w c)
    (hFz : Fz = (N : ℝ) / 2 * Real.log (betaK S.d S.L k β0) *
      Nat.card {y : BlockAt S n M K k // y ∈ Vblk R a k ∧ y ∈ Z0})
    (hfrac : ∀ hv g par w c, w ∈ E par → frac hv g par w c ≤
      Real.exp (Fz + CEt * (D : ℝ) ^ S.d + Cnat * S.lam k ^ (2 * S.d + 1) + 4 + Ck))
    (hcore : ∀ hv g, g ∈ l1Ball (GIdx S n M K N) → ∀ par w,
      ∫⁻ c, Core hv g par w c ∂μC ≤ ENNReal.ofReal (Real.exp (-κcore)))
    {N₀ k' : ℕ} [NeZero N₀] (b0 : Torus S.d (N₀ * S.L ^ (k' - k'))) (wb : Fin S.d → ℕ)
    (hwD : ∀ i, wb i ≤ D)
    (hZcard : Nat.card {y : BlockAt S n M K k // y ∈ Vblk R a k ∧ y ∈ Z0} ≤
      (boxFinset (L := S.L) (N₀ := N₀) (k := k') b0 wb).card)
    {k0 : ℕ} {H : RegionHistory S n R k0 K} (G : S.Good)
    (hT : ∀ j, 1 ≤ j → j ≤ k0 → 4 * S.rho j + 21 ≤ n j) (hadm : H.Admissible) (hkK : k ≤ K)
    {c : H.Comp k} (hc : c.1 ∈ H.rem k)
    (hTcard : (Nat.card {y : BlockAt S n M K k // y ∈ V2 ∧ P2 y} : ℝ) ≤ BudgetConsts.cubeVol S c.1.card)
    (hEZ : EZ ≤ (CE' * S.lam k + CE') * ((S.M : ℝ) * S.crit k) ^ S.d)
    (hκ : κpre ≤ κcore - (Bw + Ck)) :
    KerBound a k (removedKernel a k Z0 P t s z w u c0 r EZ ht hs hz hw hu hc0 hr htm hsm hzm hwm
      hum hc0m hrm) (κpre - S.CR * S.lam k ^ (2 * S.d + 1)) := by
  have hβk : 0 < betaK S.d S.L k β0 := by
    unfold betaK
    have : (0 : ℝ) < S.L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne S.L)
    positivity
  have hlam : 0 < S.lam k := by linarith
  refine removedKernel_kerBound_of_window a k Z0 P EZ ht hs hz hw hu hc0 hr htm hsm hzm hwm hum hc0m hrm ok hx
    (D0 := (D : ℝ)) (nZ0 := (Nat.card {y : BlockAt S n M K k // y ∈ Vblk R a k ∧ y ∈ Z0} : ℝ))
    (nTree := (Nat.card {y : BlockAt S n M K k // y ∈ V2 ∧ P2 y} : ℝ)) hCE' (by positivity) hCvol hCR hu1 hb
    Θ hΘ E hE F hF Core bw frac hid hsupp ?_ hfrac0 hfrac hcore ?_ le_rfl hEZ ?_ ?_ hκ
  · intro hv g par w' c hw'
    rw [hsplit hv g par w' c hw']
    exact (window_bw_le J (fun j => bq j hv g par w' c) cbw vw rfl (hS0 hv g par w' c hw')
      (hC hv g par w' c hw')).trans (le_of_eq hBw.symm)
  · intro par
    rw [hEdef par]
    exact window_hvol_of_groups a k Z0 hN (hE3 par) (cen par) Zt δk V2 P2 (e par) cb parT rk hrk hreg hregc
      hadj hadjc S.p0 hβk hC6 hA0 hlam hδ wz hw0 hw2 hcc hLc hFz
  · exact hTcard.trans (removed_cubeVol_le G hT hadm hkK hc)
  · exact (Nat.cast_le.2 hZcard).trans (card_boxFinset_le b0 wb hwD)

end Instance

end Balaban.LargeField
