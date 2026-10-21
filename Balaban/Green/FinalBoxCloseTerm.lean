/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.FinalBoxCloseCut
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The rooted coefficients of a term of the final cut field on two tori (A6-3 (d))

The rooted Lemma AE for a term `τ` of the final cut field `Φ(s, w) = φ₀ + c · boxCut(s) w`
(`rootedExpansion_boxCut`) on two tori, in the window frame of `boxCut_close_twoTorus`: if the
centres agree on the read set `S`, the variables agree on the region of `C`, the term `τ'` of the second
torus is within `η` of `τ` read through the residue lift, and the entries of the two cut families differ
by at most `δ` on `S × reg C`, then

`|coef_C(τ) - coef_{e C}(τ')| ≤ (η + M_τ ε / (r - r₁ - ε)) / (e^κ - 1)^{|C|}`,
`ε = |c| |reg C| δ ρ` (`rootedCoef_boxCut_close_twoTorus`). With `boxCut_close_twoTorus_margin`, `δ` is
`P (n_C² + n_C⁴) √(C₀ e^{-c₀ (min(N, N')/2 - (J + 3) M)}) / √g · (1 + p)`.
-/

@[expose] public section

namespace Balaban.Green

open Finset Balaban.Localization Balaban.Analysis Balaban.Polymer

section Term

variable {d M L N N' k : ℕ} [NeZero N] [NeZero N'] [NeZero L] {v a : ℝ}

/-- The final cut field lies in the closed ball of radius `|c| B_box ρ` around its centre on the
polydisc of radius `e^κ` (the row bound `boxCut_row_bound`). -/
theorem linField_boxCut_mem_closedBall (hd : 0 < d) (hk : 1 ≤ k) (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v) (hM : 0 < M)
    {κ : ℝ} (hκ : 0 ≤ κ) (hMB : 4 * (pdB d L * Real.exp (pdH d * κ)) ≤ M)
    (hMκ : 8 * κ * 7 ^ d ≤ pdEps d L * M) {Nf : ℕ} {h : Fin Nf → ℂ} {p : ℝ} (hp0 : 0 ≤ p)
    (hp : ∀ i j, ‖spinProj h i j‖ ≤ p) (c : ℂ) (φ₀ : L1Torus d N × Fin Nf → ℂ) {ρ : ℝ}
    (hρ : 0 ≤ ρ) {w : L1Torus d N × Fin Nf → ℂ} (hw : ∀ q, ‖w q‖ ≤ ρ)
    {s : MacIdx d N M → ℂ} (hs : s ∈ polydisc (0 : MacIdx d N M → ℂ) (fun _ => Real.exp κ)) :
    linField φ₀ (fun s q q' => c * boxCut d L N k M v a h s q q') s w ∈
      Metric.closedBall φ₀ (‖c‖ * boxCutConst d L Nf a κ p * ρ) := by
  have hsb : ∀ z, ‖s z‖ ≤ Real.exp κ := fun z => by simpa using (hs z).le
  have hB0 : 0 ≤ ballConst d (pdEps d L / 2) :=
    ballConst_decay_nonneg (by have := pdEps_pos (d := d) (L := L) hd; positivity)
  have hm0 : 0 ≤ ‖c‖ * boxCutConst d L Nf a κ p * ρ := by
    have : 0 ≤ boxCutConst d L Nf a κ p := by
      unfold boxCutConst
      refine add_nonneg (by positivity) (mul_nonneg (div_nonneg (mul_nonneg (by norm_num)
        (mul_nonneg (by positivity) hB0)) (Real.sqrt_nonneg _)) (by positivity))
    positivity
  rw [Metric.mem_closedBall, dist_pi_le_iff hm0]
  intro q
  rw [dist_eq_norm]
  simp only [linField, add_sub_cancel_left]
  calc ‖∑ y, c * boxCut d L N k M v a h s q y * w y‖
      ≤ ∑ y, ‖c * boxCut d L N k M v a h s q y * w y‖ := norm_sum_le _ _
    _ ≤ ∑ y, ‖c‖ * ‖boxCut d L N k M v a h s q y‖ * ρ := by
        refine Finset.sum_le_sum fun y _ => ?_
        simp only [norm_mul]
        exact mul_le_mul_of_nonneg_left (hw y) (by positivity)
    _ = ‖c‖ * (∑ y, ‖boxCut d L N k M v a h s q y‖) * ρ := by
        rw [← Finset.sum_mul, ← Finset.mul_sum]
    _ ≤ ‖c‖ * boxCutConst d L Nf a κ p * ρ := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)) hρ
        exact boxCut_row_bound hd hk hv0 hv1 ha1 ha2 hmass hM hκ hMB hMκ hp hsb q

/-- **The rooted coefficients of a term of the final cut field on two tori, core.** Two tori
`N, N'`, a map of sites `f` carrying the region of `C` injectively onto the region of `e C`, `e`
injective on `C`. The centres agree on the read set `S`, the variables agree on the region of `C`, the
term `τ'` is within `η` of `τ` read through `f` on `S`, and the entries of the two cut families at
corresponding parameters differ by at most `δ` on `S × reg C`; the cut fields stay in the ball of
radius `r₁` (`|c| B_box ρ < r₁`), with room `ε = |c| |reg C| δ ρ < r - r₁`. -/
theorem rootedCoef_boxCut_close_of_regions (hd : 0 < d) (hk : 1 ≤ k) (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v) (hM : 0 < M)
    {κ : ℝ} (hκ : 1 ≤ κ) (hMB : 4 * (pdB d L * Real.exp (pdH d * κ)) ≤ M)
    (hMκ : 8 * κ * 7 ^ d ≤ pdEps d L * M) {f : L1Torus d N → L1Torus d N'}
    {e : MacIdx d N M → MacIdx d N' M} {C : Finset (MacIdx d N M)}
    (heinj : Set.InjOn e (C : Set (MacIdx d N M))) {Nf : ℕ}
    (hreg : patchReg (spinBoxPatch d N' M Nf) (C.image e) =
      spinMap (Nf := Nf) f '' patchReg (spinBoxPatch d N M Nf) C)
    (hinj : Set.InjOn (spinMap (Nf := Nf) f) (patchReg (spinBoxPatch d N M Nf) C))
    {h : Fin Nf → ℂ} {p : ℝ} (hp0 : 0 ≤ p) (hp : ∀ i j, ‖spinProj h i j‖ ≤ p)
    (c : ℂ) (φ₀ : L1Torus d N × Fin Nf → ℂ) (φ₀' : L1Torus d N' × Fin Nf → ℂ)
    {S : Set (L1Torus d N × Fin Nf)} (hφ : ∀ q ∈ S, φ₀ q = φ₀' (spinMap f q))
    {τ : (L1Torus d N × Fin Nf → ℂ) → ℂ} {τ' : (L1Torus d N' × Fin Nf → ℂ) → ℂ} {r Mτ : ℝ}
    (hτan : AnalyticOnNhd ℂ τ (Metric.ball φ₀ r)) (hτb : ∀ u ∈ Metric.ball φ₀ r, ‖τ u‖ ≤ Mτ)
    (hτ'an : AnalyticOnNhd ℂ τ' (Metric.ball φ₀' r)) {η : ℝ}
    (hττ : ∀ (u' : L1Torus d N' × Fin Nf → ℂ) (u : L1Torus d N × Fin Nf → ℂ),
      (∀ q ∈ S, u q = u' (spinMap f q)) → ‖τ' u' - τ u‖ ≤ η)
    {ρ : ℝ} (hρ : 0 ≤ ρ) {w : L1Torus d N × Fin Nf → ℂ} (hw : ∀ q, ‖w q‖ ≤ ρ)
    {w' : L1Torus d N' × Fin Nf → ℂ} (hw' : ∀ q, ‖w' q‖ ≤ ρ)
    (hww : ∀ q ∈ patchReg (spinBoxPatch d N M Nf) C, w' (spinMap f q) = w q) {δ : ℝ}
    (hδ0 : 0 ≤ δ)
    (hδ : ∀ s ∈ supN C (Real.exp κ), ∀ s' ∈ supportedOn (C.image e), (∀ i ∈ C, s' (e i) = s i) →
      ∀ q ∈ S, ∀ q' ∈ patchReg (spinBoxPatch d N M Nf) C,
        ‖boxCut d L N k M v a h s q q' - boxCut d L N' k M v a h s' (spinMap f q) (spinMap f q')‖ ≤
          δ)
    {r₁ : ℝ} (hm : ‖c‖ * boxCutConst d L Nf a κ p * ρ < r₁)
    (hr : r₁ + ‖c‖ * ((regFin (spinBoxPatch d N M Nf) C).card : ℝ) * δ * ρ < r) :
    ‖rootedCoef τ φ₀ (fun s q q' => c * boxCut d L N k M v a h s q q') w C -
        rootedCoef τ' φ₀' (fun s q q' => c * boxCut d L N' k M v a h s q q') w' (C.image e)‖ ≤
      (η + Mτ * (‖c‖ * ((regFin (spinBoxPatch d N M Nf) C).card : ℝ) * δ * ρ) /
          (r - r₁ - ‖c‖ * ((regFin (spinBoxPatch d N M Nf) C).card : ℝ) * δ * ρ)) /
        (Real.exp κ - 1) ^ C.card := by
  have hκ0 : 0 ≤ κ := by linarith
  have hR : 1 < Real.exp κ := Real.one_lt_exp_iff.2 (by linarith)
  set T : (MacIdx d N M → ℂ) → L1Torus d N × Fin Nf → L1Torus d N × Fin Nf → ℂ :=
    fun s q q' => c * boxCut d L N k M v a h s q q' with hTdef
  set T' : (MacIdx d N' M → ℂ) → L1Torus d N' × Fin Nf → L1Torus d N' × Fin Nf → ℂ :=
    fun s q q' => c * boxCut d L N' k M v a h s q q' with hT'def
  have hTd : CutDecoupling (spinBoxPatch d N M Nf) (Real.exp κ) T :=
    (cutDecoupling_boxCut hd hk hv0 hv1 ha1 ha2 hmass hM hκ0 hMB hMκ h).const_mul c
  have hT'd : CutDecoupling (spinBoxPatch d N' M Nf) (Real.exp κ) T' :=
    (cutDecoupling_boxCut hd hk hv0 hv1 ha1 ha2 hmass hM hκ0 hMB hMκ h).const_mul c
  have hTan : ∀ q q', AnalyticOnNhd ℂ (fun s => T s q q')
      (polydisc (0 : MacIdx d N M → ℂ) (fun _ => Real.exp κ)) := fun q q' s hs =>
    analyticAt_const.mul (analyticOnNhd_boxCut hd hk hv0 hv1 ha1 ha2 hmass hM hκ0 hMB hMκ h q q' s hs)
  have hT'an : ∀ q q', AnalyticOnNhd ℂ (fun s => T' s q q')
      (polydisc (0 : MacIdx d N' M → ℂ) (fun _ => Real.exp κ)) := fun q q' s hs =>
    analyticAt_const.mul (analyticOnNhd_boxCut hd hk hv0 hv1 ha1 ha2 hmass hM hκ0 hMB hMκ h q q' s hs)
  set m := ‖c‖ * boxCutConst d L Nf a κ p * ρ with hmdef
  set ε := ‖c‖ * ((regFin (spinBoxPatch d N M Nf) C).card : ℝ) * δ * ρ with hεdef
  have hε0 : 0 ≤ ε := by positivity
  have hmr : m < r := by linarith
  have hball : ∀ s ∈ polydisc (0 : MacIdx d N M → ℂ) (fun _ => Real.exp κ),
      linField φ₀ T s w ∈ Metric.ball φ₀ r₁ := fun s hs =>
    Metric.closedBall_subset_ball hm (linField_boxCut_mem_closedBall
      hd hk hv0 hv1 ha1 ha2 hmass hM hκ0 hMB hMκ hp0 hp c φ₀ hρ hw hs)
  have hball' : ∀ s ∈ polydisc (0 : MacIdx d N' M → ℂ) (fun _ => Real.exp κ),
      linField φ₀' T' s w' ∈ Metric.ball φ₀' r := fun s hs =>
    Metric.closedBall_subset_ball hmr (linField_boxCut_mem_closedBall
      hd hk hv0 hv1 ha1 ha2 hmass hM hκ0 hMB hMκ hp0 hp c φ₀' hρ hw' hs)
  have hr₁r : r₁ < r := by linarith
  have hg : AnalyticOnNhd ℂ (fun s => τ (linField φ₀ T s w))
      (polydisc (0 : MacIdx d N M → ℂ) (fun _ => Real.exp κ)) := fun s hs =>
    AnalyticAt.comp (g := τ) (f := fun s => linField φ₀ T s w)
      (hτan _ (Metric.ball_subset_ball hr₁r.le (hball s hs)))
      (analyticOnNhd_linField hTan φ₀ w s hs)
  have hg' : AnalyticOnNhd ℂ (fun s => τ' (linField φ₀' T' s w'))
      (polydisc (0 : MacIdx d N' M → ℂ) (fun _ => Real.exp κ)) := fun s hs =>
    AnalyticAt.comp (g := τ') (f := fun s => linField φ₀' T' s w') (hτ'an _ (hball' s hs))
      (analyticOnNhd_linField hT'an φ₀' w' s hs)
  refine rootedCoef_close_relabel hR e heinj hg hg' ?_
  intro s hs s' hs' hss
  have hspol : s ∈ polydisc (0 : MacIdx d N M → ℂ) (fun _ => Real.exp κ) := fun i => by
    simpa using hs.2 i
  have hs'pol : s' ∈ polydisc (0 : MacIdx d N' M → ℂ) (fun _ => Real.exp κ) := fun j => by
    by_cases hj : j ∈ C.image e
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hj
      simpa [hss i hi] using hs.2 i
    · simpa [hs' j hj] using Real.exp_pos κ
  have hTT : ∀ x ∈ S, ∀ y ∈ patchReg (spinBoxPatch d N M Nf) C,
      ‖T s x y - T' s' (spinMap f x) (spinMap f y)‖ ≤ ‖c‖ * δ := by
    intro x hx y hy
    simp only [hTdef, hT'def]
    rw [← mul_sub, norm_mul]
    exact mul_le_mul_of_nonneg_left (hδ s hs s' hs' hss x hx y hy) (norm_nonneg _)
  have huu : ∀ q ∈ S, ‖linField φ₀ T s w q - linField φ₀' T' s' w' (spinMap f q)‖ ≤ ε := by
    intro q hq
    have := linField_close hTd hT'd e (spinMap f) hinj hreg hspol hs.1 hs'pol hs'
      (φ₀ := φ₀) (φ₀' := φ₀') hww hw hTT (εφ := 0)
      (fun x hx => by rw [hφ x hx, sub_self, norm_zero]) q hq
    refine this.trans (le_of_eq ?_)
    rw [hεdef]; ring
  have h1 := norm_term_sub_le_of_transport (τ := τ) (τ' := τ') (spinMap f) hτan hτb hττ hε0 hr
    (hball s hspol) huu
  exact h1

/-- **The rooted coefficients of a term of the final cut field on two tori** (window frame): the
core `rootedCoef_boxCut_close_of_regions` with the residue lift and the cell map of the window. -/
theorem rootedCoef_boxCut_close_twoTorus (hd : 0 < d) (hk : 1 ≤ k) (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v) (hM : 0 < M)
    {κ : ℝ} (hκ : 1 ≤ κ) (hMB : 4 * (pdB d L * Real.exp (pdH d * κ)) ≤ M)
    (hMκ : 8 * κ * 7 ^ d ≤ pdEps d L * M) {J : ℕ} (hN : 2 * (J + 6) * M ≤ N)
    (hN' : 2 * (J + 6) * M ≤ N') {f : L1Torus d N → L1Torus d N'}
    (hf : ∀ x μ, f x μ = (((x μ).val : ℕ) : ZMod N')) {e : MacIdx d N M → MacIdx d N' M}
    (he : ∀ z i, (z i : ℕ) ≤ J + 4 → ((e z i : Fin (macK N' M)) : ℕ) = z i)
    {C : Finset (MacIdx d N M)} (hC : ∀ z ∈ C, ∀ i, 4 ≤ (z i : ℕ) ∧ (z i : ℕ) ≤ J)
    {Nf : ℕ} {h : Fin Nf → ℂ} {p : ℝ} (hp0 : 0 ≤ p) (hp : ∀ i j, ‖spinProj h i j‖ ≤ p)
    (c : ℂ) (φ₀ : L1Torus d N × Fin Nf → ℂ) (φ₀' : L1Torus d N' × Fin Nf → ℂ)
    {S : Set (L1Torus d N × Fin Nf)} (hφ : ∀ q ∈ S, φ₀ q = φ₀' (spinMap f q))
    {τ : (L1Torus d N × Fin Nf → ℂ) → ℂ} {τ' : (L1Torus d N' × Fin Nf → ℂ) → ℂ} {r Mτ : ℝ}
    (hτan : AnalyticOnNhd ℂ τ (Metric.ball φ₀ r)) (hτb : ∀ u ∈ Metric.ball φ₀ r, ‖τ u‖ ≤ Mτ)
    (hτ'an : AnalyticOnNhd ℂ τ' (Metric.ball φ₀' r)) {η : ℝ}
    (hττ : ∀ (u' : L1Torus d N' × Fin Nf → ℂ) (u : L1Torus d N × Fin Nf → ℂ),
      (∀ q ∈ S, u q = u' (spinMap f q)) → ‖τ' u' - τ u‖ ≤ η)
    {ρ : ℝ} (hρ : 0 ≤ ρ) {w : L1Torus d N × Fin Nf → ℂ} (hw : ∀ q, ‖w q‖ ≤ ρ)
    {w' : L1Torus d N' × Fin Nf → ℂ} (hw' : ∀ q, ‖w' q‖ ≤ ρ)
    (hww : ∀ q ∈ patchReg (spinBoxPatch d N M Nf) C, w' (spinMap f q) = w q) {δ : ℝ}
    (hδ0 : 0 ≤ δ)
    (hδ : ∀ s ∈ supN C (Real.exp κ), ∀ s' ∈ supportedOn (C.image e), (∀ i ∈ C, s' (e i) = s i) →
      ∀ q ∈ S, ∀ q' ∈ patchReg (spinBoxPatch d N M Nf) C,
        ‖boxCut d L N k M v a h s q q' - boxCut d L N' k M v a h s' (spinMap f q) (spinMap f q')‖ ≤
          δ)
    {r₁ : ℝ} (hm : ‖c‖ * boxCutConst d L Nf a κ p * ρ < r₁)
    (hr : r₁ + ‖c‖ * ((regFin (spinBoxPatch d N M Nf) C).card : ℝ) * δ * ρ < r) :
    ‖rootedCoef τ φ₀ (fun s q q' => c * boxCut d L N k M v a h s q q') w C -
        rootedCoef τ' φ₀' (fun s q q' => c * boxCut d L N' k M v a h s q q') w' (C.image e)‖ ≤
      (η + Mτ * (‖c‖ * ((regFin (spinBoxPatch d N M Nf) C).card : ℝ) * δ * ρ) /
          (r - r₁ - ‖c‖ * ((regFin (spinBoxPatch d N M Nf) C).card : ℝ) * δ * ρ)) /
        (Real.exp κ - 1) ^ C.card := by
  obtain ⟨hreg, hinj⟩ := spinBoxPatch_image (Nf := Nf) hM hN hN' hf he hC
  exact rootedCoef_boxCut_close_of_regions hd hk hv0 hv1 ha1 ha2 hmass hM hκ hMB hMκ
    (injOn_cellMap_window he hC) hreg hinj hp0 hp c φ₀ φ₀' hφ hτan hτb hτ'an hττ hρ hw hw' hww hδ0
    hδ hm hr

end Term

end Balaban.Green
