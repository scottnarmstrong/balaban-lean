/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.FinalTaggedRow
public import Balaban.Localization.DecoupledCovPrincipal

/-!
# The Stieltjes square root of the tagged parametrix family (FINALFAM2, T4)

This file belongs to the "path-tagged macroblock parametrix" of `notes/phase1/FINALFAM.md`.
**This construction is proposed in FINALFAM; the papers print no formula for it** (question 18 to
the author is pending); nothing here claims it is the papers' construction.

For the tagged parametrix family `taggedGfin s t` (with `taggedGfin 1 t = (U + t)⁻¹`) put
`taggedCfin s = π⁻¹ ∫₀^∞ t^{-1/2} taggedGfin s t dt`, in exactly the form of the integral that
defines `Localization.sqrtMat`.

* `taggedCfin_integrable`: every entry of the integrand is integrable on `(0, ∞)`, dominated by
  `(4/3) · 2 e^{Hκ} B₀ · t^{-1/2} / (g + t)`.
* `taggedCfin_row_bound`: for `0 ≤ r ≤ ε/8` and `s` in the closed polydisc,
  `∑_y e^{r dist x y} ‖taggedCfin s x y‖ ≤ (4/3) · 2 e^{Hκ} B₀ / √g`, with the entry bound
  `taggedCfin_entry_bound` and the rate-loss column bound `taggedCfin_column_bound`.
* `taggedCfin_one`: `taggedCfin 1 = Localization.sqrtMat (finalOp …)`.
* `taggedCfin_analyticOnNhd`: every entry of `s ↦ taggedCfin s` is analytic on the open polydisc
  `{s | ∀ p, ‖s p‖ < e^κ}` (via `analyticOnNhd_integral_Ioi`).

**`taggedCfin s` is not claimed to be a square root of anything for `s ≠ 1`**; only its value at
`s = 1` is identified (with the principal inverse square root of the final operator).
-/

@[expose] public section

open Finset Matrix MeasureTheory Set

namespace Balaban.Green

section Def

variable (d L N₀ k M : ℕ) [NeZero N₀] [NeZero L]

/-- **The Stieltjes square root of the tagged family** (a construction proposed in FINALFAM):
`π⁻¹ ∫₀^∞ t^{-1/2} G_fin(s, t) dt`, entrywise, in the form of `Localization.sqrtMat`. -/
noncomputable def taggedCfin (v a : ℝ) (s : MacIdx d N₀ M → ℂ) :
    Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ :=
  ((1 / Real.pi : ℝ) : ℂ) • Localization.intMat (volume.restrict (Ioi (0 : ℝ)))
    (fun t => ((t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) •
      taggedGfin Finset.univ (macBoxF d N₀ M) (fun z u => ((macChi d N₀ M z u : ℝ) : ℂ))
        (macTags d N₀ M) (finalOp d L N₀ k v a) t s)

end Def

section Main

variable {d L N₀ k M : ℕ} [NeZero N₀] [NeZero L] {v a : ℝ}

local notation "Gf" => taggedGfin Finset.univ (macBoxF d N₀ M)
  (fun z u => ((macChi d N₀ M z u : ℝ) : ℂ)) (macTags d N₀ M) (finalOp d L N₀ k v a)

theorem continuousOn_taggedMat {Z : Type*} (S : Finset Z) {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Pc : Type*} (V : Z → ι → ι → Finset Pc) (A : Z → ℝ → Matrix ι ι ℂ) (s : Pc → ℂ)
    {T : Set ℝ} (hA : ∀ z ∈ S, ContinuousOn (A z) T) :
    ContinuousOn (fun t => taggedMat S V (fun z => A z t) s) T := by
  refine continuousOn_pi.2 fun x => continuousOn_pi.2 fun y => ?_
  simp only [taggedMat, Matrix.of_apply]
  refine continuousOn_finsetSum _ fun z hz => continuousOn_const.mul ?_
  exact (continuousOn_pi.1 (continuousOn_pi.1 (hA z hz) x) y)

omit [NeZero N₀] in
theorem continuousOn_shiftMat (U : Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ) (T : Set ℝ) :
    ContinuousOn (fun t => shiftMat U t) T :=
  (continuous_const.add (Complex.continuous_ofReal.smul continuous_const)).continuousOn

/-- Continuity in `t > 0` of the entries of the tagged family of a general coercive `U`. -/
theorem continuousOn_taggedGfin_of_coercive (U : Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ)
    {g A δ ε : ℝ} (hA : 0 ≤ A) (hδ : 0 < δ) (hg : 0 < g) (hU : IsCoercive U g)
    (hUdec : ∀ x y, ‖U x y‖ ≤ A * Real.exp (-δ * dist x y)) (hε : 0 < ε) (hεδ : ε ≤ δ)
    (hεc : ε ≤ ctRate A δ g (ballConst d (δ / 4)))
    (hM : 0 < M) {κ : ℝ} (hκ : 0 ≤ κ)
    (hMB : 4 * ((16 * 7 ^ d * A * pdLip d / (g * ε) * (ballConst d (ε / 2) * ballConst d (3 * ε / 4))) * Real.exp (pdH d * κ)) ≤ M) (hMκ : 8 * κ * 7 ^ d ≤ ε * M)
    {s : MacIdx d N₀ M → ℂ} (hs : ∀ p, ‖s p‖ ≤ Real.exp κ) (x y : L1Torus d N₀) :
    ContinuousOn (fun t => taggedGfin Finset.univ (macBoxF d N₀ M) (fun z u => ((macChi d N₀ M z u : ℝ) : ℂ)) (macTags d N₀ M) U t s x y) (Ioi 0) := by
  have hbox : ∀ z : MacIdx d N₀ M, ContinuousOn
      (fun t => boxG (U) (macBoxF d N₀ M z) t) (Ioi 0) := by
    intro z
    have hH : ContinuousOn (fun t => boxH (U) (macBoxF d N₀ M z) t) (Ioi 0) := by
      unfold boxH
      exact ((continuousOn_const.mul (continuousOn_shiftMat _ _)).mul
        continuousOn_const).add continuousOn_const
    exact (Localization.contOn_matrix_inv hH fun t ht =>
      boxH_isUnit_of_coercive U hA hδ hg hU hUdec (Set.mem_Ioi.1 ht).le _).mul continuousOn_const
  have hG : ContinuousOn (fun t => taggedG Finset.univ (macBoxF d N₀ M)
      (fun z u => ((macChi d N₀ M z u : ℝ) : ℂ)) (macTags d N₀ M) (U) t s)
      (Ioi 0) := by
    unfold taggedG
    exact continuousOn_taggedMat _ _ _ _ fun z _ => continuousOn_const.mul (hbox z)
  have hK : ContinuousOn (fun t => taggedK Finset.univ (macBoxF d N₀ M)
      (fun z u => ((macChi d N₀ M z u : ℝ) : ℂ)) (macTags d N₀ M) (U) t s)
      (Ioi 0) := by
    unfold taggedK boxR
    exact continuousOn_taggedMat _ _ _ _ fun z _ =>
      continuousOn_const.sub (((continuousOn_shiftMat _ _).mul continuousOn_const).mul (hbox z))
  have hI : ContinuousOn (fun t => (1 - taggedK Finset.univ (macBoxF d N₀ M)
      (fun z u => ((macChi d N₀ M z u : ℝ) : ℂ)) (macTags d N₀ M) (U) t s)⁻¹)
      (Ioi 0) :=
    Localization.contOn_matrix_inv (continuousOn_const.sub hK) fun t ht =>
      (taggedGfin_of_coercive U hA hδ hg hU hUdec hε hεδ hεc
        (Set.mem_Ioi.1 ht).le hM hκ hMB hMκ).2.1 s hs
  have := hG.mul hI
  exact continuousOn_pi.1 (continuousOn_pi.1 this x) y


theorem continuousOn_taggedGfin (hd : 0 < d) (hk : 1 ≤ k) (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v)
    (hM : 0 < M) {κ : ℝ} (hκ : 0 ≤ κ)
    (hMB : 4 * (pdB d L * Real.exp (pdH d * κ)) ≤ M) (hMκ : 8 * κ * 7 ^ d ≤ pdEps d L * M)
    {s : MacIdx d N₀ M → ℂ} (hs : ∀ p, ‖s p‖ ≤ Real.exp κ) (x y : L1Torus d N₀) :
    ContinuousOn (fun t => Gf t s x y) (Ioi 0) := by
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  exact continuousOn_taggedGfin_of_coercive (finalOp d L N₀ k v a) (finalDecayC_pos hd).le
    (blockDecayRate_pos hd) (finalGap_pos hL) (finalMass_isCoercive hd hv0 hv1 ha1 hmass)
    (finalMass_entry_decay hd hk hv0 ha1 ha2) (pdEps_pos hd) (min_le_left _ _) (min_le_right _ _)
    hM hκ hMB hMκ hs x y

/-- Pointwise domination of the integrand: for `t > 0`,
`‖t^{-1/2} G_fin(s,t) x y‖ ≤ (4/3) · 2 e^{Hκ} B₀ · (t^{-1/2} (g + t)⁻¹)`, for a general matrix. -/
theorem taggedCfin_integrand_le_of_coercive (U : Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ)
    {g A δ ε : ℝ} (hA : 0 ≤ A) (hδ : 0 < δ) (hg : 0 < g) (hU : IsCoercive U g)
    (hUdec : ∀ x y, ‖U x y‖ ≤ A * Real.exp (-δ * dist x y)) (hε : 0 < ε) (hεδ : ε ≤ δ)
    (hεc : ε ≤ ctRate A δ g (ballConst d (δ / 4)))
    (hM : 0 < M) {κ : ℝ} (hκ : 0 ≤ κ)
    (hMB : 4 * ((16 * 7 ^ d * A * pdLip d / (g * ε) * (ballConst d (ε / 2) * ballConst d (3 * ε / 4))) * Real.exp (pdH d * κ)) ≤ M) (hMκ : 8 * κ * 7 ^ d ≤ ε * M)
    {s : MacIdx d N₀ M → ℂ} (hs : ∀ p, ‖s p‖ ≤ Real.exp κ)
    {t : ℝ} (ht : 0 < t) (x y : L1Torus d N₀) :
    ‖((t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * taggedGfin Finset.univ (macBoxF d N₀ M) (fun z u => ((macChi d N₀ M z u : ℝ) : ℂ)) (macTags d N₀ M) U t s x y‖ ≤
      4 / 3 * (2 * Real.exp (pdH d * κ) * ballConst d (ε / 2)) *
        (t ^ (-(1 / 2 : ℝ)) * (g + t)⁻¹) := by
  have h3 : 0 < t ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos ht _
  have h := taggedGfin_entry_bound_of_coercive U hA hδ hg hU hUdec hε hεδ hεc ht.le hM hκ hMB hMκ
    le_rfl (by linarith) hs x y
  simp only [neg_zero, zero_mul, Real.exp_zero, mul_one] at h
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg h3.le]
  calc _ ≤ t ^ (-(1 / 2 : ℝ)) * (4 / 3 * (2 * Real.exp (pdH d * κ) * ballConst d (ε / 2) / (g + t))) :=
        mul_le_mul_of_nonneg_left h h3.le
    _ = _ := by rw [div_eq_mul_inv]; ring


/-- **T2, for a general matrix.** Each entry of the integrand of the Stieltjes square root is
integrable on `(0, ∞)`. -/
theorem taggedCfin_integrable_of_coercive (U : Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ)
    {g A δ ε : ℝ} (hA : 0 ≤ A) (hδ : 0 < δ) (hg : 0 < g) (hU : IsCoercive U g)
    (hUdec : ∀ x y, ‖U x y‖ ≤ A * Real.exp (-δ * dist x y)) (hε : 0 < ε) (hεδ : ε ≤ δ)
    (hεc : ε ≤ ctRate A δ g (ballConst d (δ / 4)))
    (hM : 0 < M) {κ : ℝ} (hκ : 0 ≤ κ)
    (hMB : 4 * ((16 * 7 ^ d * A * pdLip d / (g * ε) * (ballConst d (ε / 2) * ballConst d (3 * ε / 4))) * Real.exp (pdH d * κ)) ≤ M) (hMκ : 8 * κ * 7 ^ d ≤ ε * M)
    {s : MacIdx d N₀ M → ℂ} (hs : ∀ p, ‖s p‖ ≤ Real.exp κ) (x y : L1Torus d N₀) :
    Integrable (fun t : ℝ => ((t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * taggedGfin Finset.univ (macBoxF d N₀ M) (fun z u => ((macChi d N₀ M z u : ℝ) : ℂ)) (macTags d N₀ M) U t s x y)
      (volume.restrict (Ioi (0 : ℝ))) := by
  refine Integrable.mono' ((Localization.integrableOn_rpow_inv_add hg).const_mul
    (4 / 3 * (2 * Real.exp (pdH d * κ) * ballConst d (ε / 2)))) ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    refine ContinuousOn.mul ?_ (continuousOn_taggedGfin_of_coercive U hA hδ hg hU hUdec hε hεδ hεc hM hκ hMB
      hMκ hs x y)
    refine Complex.continuous_ofReal.comp_continuousOn ?_
    exact fun y hy => (Real.continuousAt_rpow_const _ _
      (Or.inl (Set.mem_Ioi.mp hy).ne')).continuousWithinAt
  · exact (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun t ht =>
      taggedCfin_integrand_le_of_coercive U hA hδ hg hU hUdec hε hεδ hεc hM hκ hMB hMκ hs (Set.mem_Ioi.1 ht) x y)


/-- **T3, for a general matrix.**  Weighted row sums of the Stieltjes square root of the tagged
family: for `0 ≤ r ≤ ε/8` and `s` in the closed polydisc,
`∑_y e^{r dist x y} ‖C_fin(s) x y‖ ≤ (4/3) · 2 e^{Hκ} B₀ / √g`, where `C_fin(s)` is
`π⁻¹ ∫₀^∞ t^{-1/2} G_fin(s, t) dt` (spelled out). -/
theorem taggedCfin_row_bound_of_coercive (U : Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ)
    {g A δ ε : ℝ} (hA : 0 ≤ A) (hδ : 0 < δ) (hg : 0 < g) (hU : IsCoercive U g)
    (hUdec : ∀ x y, ‖U x y‖ ≤ A * Real.exp (-δ * dist x y)) (hε : 0 < ε) (hεδ : ε ≤ δ)
    (hεc : ε ≤ ctRate A δ g (ballConst d (δ / 4)))
    (hM : 0 < M) {κ : ℝ} (hκ : 0 ≤ κ)
    (hMB : 4 * ((16 * 7 ^ d * A * pdLip d / (g * ε) * (ballConst d (ε / 2) * ballConst d (3 * ε / 4))) * Real.exp (pdH d * κ)) ≤ M) (hMκ : 8 * κ * 7 ^ d ≤ ε * M)
    {s : MacIdx d N₀ M → ℂ} (hs : ∀ p, ‖s p‖ ≤ Real.exp κ)
    {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ ε / 8) (x : L1Torus d N₀) :
    ∑ y, Real.exp (r * dist x y) * ‖(((1 / Real.pi : ℝ) : ℂ) • Localization.intMat (volume.restrict (Ioi (0 : ℝ))) (fun t => ((t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) • taggedGfin Finset.univ (macBoxF d N₀ M) (fun z u => ((macChi d N₀ M z u : ℝ) : ℂ)) (macTags d N₀ M) U t s)) x y‖ ≤
      4 / 3 * (2 * Real.exp (pdH d * κ) * ballConst d (ε / 2)) / Real.sqrt g := by
  set c0 : ℝ := 4 / 3 * (2 * Real.exp (pdH d * κ) * ballConst d (ε / 2)) with hc0
  have hint : ∀ y, Integrable (fun t : ℝ => Real.exp (r * dist x y) *
      ‖((t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * taggedGfin Finset.univ (macBoxF d N₀ M) (fun z u => ((macChi d N₀ M z u : ℝ) : ℂ)) (macTags d N₀ M) U t s x y‖) (volume.restrict (Ioi (0 : ℝ))) :=
    fun y => (taggedCfin_integrable_of_coercive U hA hδ hg hU hUdec hε hεδ hεc hM hκ hMB hMκ hs x y).norm.const_mul _
  have hentry : ∀ y, ‖((((1 / Real.pi : ℝ) : ℂ) • Localization.intMat (volume.restrict (Ioi (0 : ℝ))) (fun t => ((t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) • taggedGfin Finset.univ (macBoxF d N₀ M) (fun z u => ((macChi d N₀ M z u : ℝ) : ℂ)) (macTags d N₀ M) U t s)) x y)‖ ≤
      (1 / Real.pi) * ∫ t in Ioi (0 : ℝ), ‖((t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * taggedGfin Finset.univ (macBoxF d N₀ M) (fun z u => ((macChi d N₀ M z u : ℝ) : ℂ)) (macTags d N₀ M) U t s x y‖ := by
    intro y
    have : ((((1 / Real.pi : ℝ) : ℂ) • Localization.intMat (volume.restrict (Ioi (0 : ℝ))) (fun t => ((t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) • taggedGfin Finset.univ (macBoxF d N₀ M) (fun z u => ((macChi d N₀ M z u : ℝ) : ℂ)) (macTags d N₀ M) U t s)) x y) = ((1 / Real.pi : ℝ) : ℂ) *
        ∫ t in Ioi (0 : ℝ), ((t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * taggedGfin Finset.univ (macBoxF d N₀ M) (fun z u => ((macChi d N₀ M z u : ℝ) : ℂ)) (macTags d N₀ M) U t s x y := rfl
    rw [this, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (by positivity)
  have hsum : ∑ y, Real.exp (r * dist x y) * ‖((((1 / Real.pi : ℝ) : ℂ) • Localization.intMat (volume.restrict (Ioi (0 : ℝ))) (fun t => ((t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) • taggedGfin Finset.univ (macBoxF d N₀ M) (fun z u => ((macChi d N₀ M z u : ℝ) : ℂ)) (macTags d N₀ M) U t s)) x y)‖ ≤
      (1 / Real.pi) * ∫ t in Ioi (0 : ℝ), ∑ y, Real.exp (r * dist x y) *
        ‖((t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * taggedGfin Finset.univ (macBoxF d N₀ M) (fun z u => ((macChi d N₀ M z u : ℝ) : ℂ)) (macTags d N₀ M) U t s x y‖ := by
    rw [integral_finsetSum _ fun y _ => hint y, Finset.mul_sum]
    refine Finset.sum_le_sum fun y _ => ?_
    rw [integral_const_mul]
    calc _ ≤ Real.exp (r * dist x y) * ((1 / Real.pi) * ∫ t in Ioi (0 : ℝ),
          ‖((t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * taggedGfin Finset.univ (macBoxF d N₀ M) (fun z u => ((macChi d N₀ M z u : ℝ) : ℂ)) (macTags d N₀ M) U t s x y‖) :=
          mul_le_mul_of_nonneg_left (hentry y) (Real.exp_pos _).le
      _ = _ := by ring
  have hI : ∫ t in Ioi (0 : ℝ), ∑ y, Real.exp (r * dist x y) *
        ‖((t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * taggedGfin Finset.univ (macBoxF d N₀ M) (fun z u => ((macChi d N₀ M z u : ℝ) : ℂ)) (macTags d N₀ M) U t s x y‖ ≤ c0 * (Real.pi / Real.sqrt (g)) := by
    rw [← Localization.integral_rpow_inv_add hg, ← integral_const_mul]
    refine integral_mono_of_nonneg ?_ ((Localization.integrableOn_rpow_inv_add hg).const_mul c0) ?_
    · exact Filter.Eventually.of_forall fun t => Finset.sum_nonneg fun y _ =>
        mul_nonneg (Real.exp_pos _).le (norm_nonneg _)
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun t ht => ?_)
      have ht0 : 0 < t := mem_Ioi.1 ht
      have h3 : 0 < t ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos ht0 _
      have hrow := taggedGfin_row_bound_of_coercive U hA hδ hg hU hUdec hε hεδ hεc ht0.le hM hκ hMB hMκ hr0 hr hs x
      have : ∑ y, Real.exp (r * dist x y) * ‖((t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * taggedGfin Finset.univ (macBoxF d N₀ M) (fun z u => ((macChi d N₀ M z u : ℝ) : ℂ)) (macTags d N₀ M) U t s x y‖ =
          t ^ (-(1 / 2 : ℝ)) * ∑ y, Real.exp (r * dist x y) * ‖taggedGfin Finset.univ (macBoxF d N₀ M) (fun z u => ((macChi d N₀ M z u : ℝ) : ℂ)) (macTags d N₀ M) U t s x y‖ := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg h3.le]; ring
      beta_reduce
      rw [this]
      calc _ ≤ t ^ (-(1 / 2 : ℝ)) * (4 / 3 * (2 * Real.exp (pdH d * κ) * ballConst d (ε / 2) / (g + t))) :=
            mul_le_mul_of_nonneg_left hrow h3.le
        _ = _ := by rw [hc0, div_eq_mul_inv]; ring
  have hpi : 0 < Real.pi := Real.pi_pos
  calc _ ≤ _ := hsum
    _ ≤ (1 / Real.pi) * (c0 * (Real.pi / Real.sqrt (g))) :=
        mul_le_mul_of_nonneg_left hI (by positivity)
    _ = _ := by field_simp


variable (hd : 0 < d) (hk : 1 ≤ k) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2)
  (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v) (hM : 0 < M) {κ : ℝ} (hκ : 0 ≤ κ)
  (hMB : 4 * (pdB d L * Real.exp (pdH d * κ)) ≤ M) (hMκ : 8 * κ * 7 ^ d ≤ pdEps d L * M)
include hd hk hv0 hv1 ha1 ha2 hmass hM hκ hMB hMκ

/-- Pointwise domination of the integrand: for `t > 0`,
`‖t^{-1/2} G_fin(s,t) x y‖ ≤ (4/3) · 2 e^{Hκ} B₀ · (t^{-1/2} (g + t)⁻¹)`. -/
theorem taggedCfin_integrand_le {s : MacIdx d N₀ M → ℂ} (hs : ∀ p, ‖s p‖ ≤ Real.exp κ)
    {t : ℝ} (ht : 0 < t) (x y : L1Torus d N₀) :
    ‖((t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * Gf t s x y‖ ≤
      4 / 3 * (2 * Real.exp (pdH d * κ) * ballConst d (pdEps d L / 2)) *
        (t ^ (-(1 / 2 : ℝ)) * (finalGap d L + t)⁻¹) := by
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  exact taggedCfin_integrand_le_of_coercive (finalOp d L N₀ k v a) (finalDecayC_pos hd).le
    (blockDecayRate_pos hd) (finalGap_pos hL) (finalMass_isCoercive hd hv0 hv1 ha1 hmass)
    (finalMass_entry_decay hd hk hv0 ha1 ha2) (pdEps_pos hd) (min_le_left _ _) (min_le_right _ _)
    hM hκ hMB hMκ hs ht x y

/-- **T2.** Each entry of the integrand of `taggedCfin` is integrable on `(0, ∞)`. -/
theorem taggedCfin_integrable {s : MacIdx d N₀ M → ℂ} (hs : ∀ p, ‖s p‖ ≤ Real.exp κ)
    (x y : L1Torus d N₀) :
    Integrable (fun t : ℝ => ((t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * Gf t s x y)
      (volume.restrict (Ioi (0 : ℝ))) := by
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  exact taggedCfin_integrable_of_coercive (finalOp d L N₀ k v a) (finalDecayC_pos hd).le
    (blockDecayRate_pos hd) (finalGap_pos hL) (finalMass_isCoercive hd hv0 hv1 ha1 hmass)
    (finalMass_entry_decay hd hk hv0 ha1 ha2) (pdEps_pos hd) (min_le_left _ _) (min_le_right _ _)
    hM hκ hMB hMκ hs x y

/-- **T3.**  Weighted row sums of `taggedCfin`: for `0 ≤ r ≤ ε/8` and `s` in the closed polydisc,
`∑_y e^{r dist x y} ‖C_fin(s) x y‖ ≤ (4/3) · 2 e^{Hκ} B₀ / √g`. -/
theorem taggedCfin_row_bound {s : MacIdx d N₀ M → ℂ} (hs : ∀ p, ‖s p‖ ≤ Real.exp κ)
    {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ pdEps d L / 8) (x : L1Torus d N₀) :
    ∑ y, Real.exp (r * dist x y) * ‖taggedCfin d L N₀ k M v a s x y‖ ≤
      4 / 3 * (2 * Real.exp (pdH d * κ) * ballConst d (pdEps d L / 2)) /
        Real.sqrt (finalGap d L) := by
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  exact taggedCfin_row_bound_of_coercive (finalOp d L N₀ k v a) (finalDecayC_pos hd).le
    (blockDecayRate_pos hd) (finalGap_pos hL) (finalMass_isCoercive hd hv0 hv1 ha1 hmass)
    (finalMass_entry_decay hd hk hv0 ha1 ha2) (pdEps_pos hd) (min_le_left _ _) (min_le_right _ _)
    hM hκ hMB hMκ hs hr0 hr x
/-- **T3, entry bound.** -/
theorem taggedCfin_entry_bound {s : MacIdx d N₀ M → ℂ} (hs : ∀ p, ‖s p‖ ≤ Real.exp κ)
    {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ pdEps d L / 8) (x y : L1Torus d N₀) :
    ‖taggedCfin d L N₀ k M v a s x y‖ ≤
      4 / 3 * (2 * Real.exp (pdH d * κ) * ballConst d (pdEps d L / 2)) /
        Real.sqrt (finalGap d L) * Real.exp (-r * dist x y) := by
  have h := taggedCfin_row_bound hd hk hv0 hv1 ha1 ha2 hmass hM hκ hMB hMκ hs hr0 hr x
  have h1 : Real.exp (r * dist x y) * ‖taggedCfin d L N₀ k M v a s x y‖ ≤ _ :=
    (Finset.single_le_sum (f := fun y => Real.exp (r * dist x y) *
      ‖taggedCfin d L N₀ k M v a s x y‖) (fun y _ => mul_nonneg (Real.exp_pos _).le
        (norm_nonneg _)) (Finset.mem_univ y)).trans h
  have h2 : Real.exp (-r * dist x y) * Real.exp (r * dist x y) = 1 := by
    rw [← Real.exp_add]; simp
  calc _ = Real.exp (-r * dist x y) * (Real.exp (r * dist x y) *
        ‖taggedCfin d L N₀ k M v a s x y‖) := by rw [← mul_assoc, h2, one_mul]
    _ ≤ Real.exp (-r * dist x y) * _ := mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
    _ = _ := by ring

/-- **T3, rate-loss column bound.** -/
theorem taggedCfin_column_bound {s : MacIdx d N₀ M → ℂ} (hs : ∀ p, ‖s p‖ ≤ Real.exp κ)
    {r r' : ℝ} (hr'0 : 0 ≤ r') (hrr : r' < r) (hr : r ≤ pdEps d L / 8) (y : L1Torus d N₀) :
    ∑ x, Real.exp (r' * dist x y) * ‖taggedCfin d L N₀ k M v a s x y‖ ≤
      4 / 3 * (2 * Real.exp (pdH d * κ) * ballConst d (pdEps d L / 2)) /
        Real.sqrt (finalGap d L) * ballConst d (r - r') := by
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hr0 : 0 ≤ r := hr'0.trans hrr.le
  have hB0 : 0 ≤ ballConst d (pdEps d L / 2) := ballConst_decay_nonneg (by
    have := pdEps_pos (d := d) (L := L) hd; positivity)
  have hterm : ∀ x : L1Torus d N₀, Real.exp (r' * dist x y) *
      ‖taggedCfin d L N₀ k M v a s x y‖ ≤
      4 / 3 * (2 * Real.exp (pdH d * κ) * ballConst d (pdEps d L / 2)) /
        Real.sqrt (finalGap d L) * Real.exp (-(r - r') * dist y x) := by
    intro x
    have h := taggedCfin_entry_bound hd hk hv0 hv1 ha1 ha2 hmass hM hκ hMB hMκ hs hr0 hr x y
    rw [dist_comm y x]
    calc _ ≤ Real.exp (r' * dist x y) * (4 / 3 * (2 * Real.exp (pdH d * κ) *
          ballConst d (pdEps d L / 2)) / Real.sqrt (finalGap d L) * Real.exp (-r * dist x y)) :=
          mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
      _ = 4 / 3 * (2 * Real.exp (pdH d * κ) * ballConst d (pdEps d L / 2)) /
          Real.sqrt (finalGap d L) * (Real.exp (r' * dist x y) * Real.exp (-r * dist x y)) := by
          ring
      _ = _ := by rw [← Real.exp_add]; congr 2; ring
  calc _ ≤ ∑ x : L1Torus d N₀, 4 / 3 * (2 * Real.exp (pdH d * κ) * ballConst d (pdEps d L / 2)) /
        Real.sqrt (finalGap d L) * Real.exp (-(r - r') * dist y x) :=
        Finset.sum_le_sum fun x _ => hterm x
    _ = _ * ∑ x : L1Torus d N₀, Real.exp (-(r - r') * dist y x) := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (ballSum_L1Torus d N₀ (by linarith) y) (by positivity)

/-- **T4.**  At the base point `s = 1`, `taggedCfin` is the principal inverse square root
`Localization.sqrtMat` of the final operator. -/
theorem taggedCfin_one :
    taggedCfin d L N₀ k M v a (fun _ => 1) = Localization.sqrtMat (finalOp d L N₀ k v a) := by
  unfold taggedCfin Localization.sqrtMat
  congr 1
  ext p q
  unfold Localization.intMat
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have h := (taggedGfin_final (N₀ := N₀) (k := k) (L := L) hd hk hv0 hv1 ha1 ha2 hmass
    (Set.mem_Ioi.1 ht).le hM hκ hMB hMκ).2.2.2
  simp only [h, shiftMat, add_comm]

/-- **T5.**  Every entry of `s ↦ taggedCfin s` is analytic on the open polydisc
`{s | ∀ p, ‖s p‖ < e^κ}`. -/
theorem taggedCfin_analyticOnNhd (x y : L1Torus d N₀) :
    AnalyticOnNhd ℂ (fun s => taggedCfin d L N₀ k M v a s x y)
      {s : MacIdx d N₀ M → ℂ | ∀ p, ‖s p‖ < Real.exp κ} := by
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hopen : IsOpen {s : MacIdx d N₀ M → ℂ | ∀ p, ‖s p‖ < Real.exp κ} := by
    have : {s : MacIdx d N₀ M → ℂ | ∀ p, ‖s p‖ < Real.exp κ} =
        ⋂ p, (fun s : MacIdx d N₀ M → ℂ => ‖s p‖) ⁻¹' Iio (Real.exp κ) := by
      ext s; simp
    rw [this]
    exact isOpen_iInter_of_finite fun p => isOpen_Iio.preimage (by fun_prop)
  have hcl : ∀ s ∈ {s : MacIdx d N₀ M → ℂ | ∀ p, ‖s p‖ < Real.exp κ},
      ∀ p, ‖s p‖ ≤ Real.exp κ := fun s hs p => (hs p).le
  have hint := Localization.analyticOnNhd_integral_Ioi (E := MacIdx d N₀ M → ℂ) hopen
    (G := fun t s => ((t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * Gf t s x y)
    (g := fun t => 4 / 3 * (2 * Real.exp (pdH d * κ) * ballConst d (pdEps d L / 2)) *
        (t ^ (-(1 / 2 : ℝ)) * (finalGap d L + t)⁻¹))
    (fun t ht => analyticOnNhd_const.mul (((taggedGfin_final (N₀ := N₀) (k := k) (L := L) hd hk
        hv0 hv1 ha1 ha2 hmass (Set.mem_Ioi.1 ht).le hM hκ hMB hMκ).2.2.1 x y).mono
        fun s hs p => (hs p).le))
    (fun s hs => ContinuousOn.mul (Complex.continuous_ofReal.comp_continuousOn
        (fun t ht => (Real.continuousAt_rpow_const _ _
          (Or.inl (Set.mem_Ioi.mp ht).ne')).continuousWithinAt))
      (continuousOn_taggedGfin hd hk hv0 hv1 ha1 ha2 hmass hM hκ hMB hMκ (hcl s hs) x y))
    (continuousOn_const.mul (ContinuousOn.mul
      (fun t ht => (Real.continuousAt_rpow_const _ _
          (Or.inl (Set.mem_Ioi.mp ht).ne')).continuousWithinAt)
      (Localization.continuousOn_inv_add_Ioi (finalGap_pos (d := d) hL))))
    ((Localization.integrableOn_rpow_inv_add (finalGap_pos (d := d) hL)).const_mul _)
    (fun t ht s hs => taggedCfin_integrand_le hd hk hv0 hv1 ha1 ha2 hmass hM hκ hMB hMκ
      (hcl s hs) ht x y)
  have := (analyticOnNhd_const (v := ((1 / Real.pi : ℝ) : ℂ))).mul hint
  exact this.congr hopen fun s _ => rfl

end Main

end Balaban.Green
