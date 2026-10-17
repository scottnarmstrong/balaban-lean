/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.CancelStationary
public import Balaban.LargeField.R.CancelRemaining
public import Balaban.LargeField.R.ActionConvReal
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# The pointwise exponent bound (2.58′) for the removed outcome (Lemma III.8.7 step (2))

`notes/phase1/LF4R-PLAN.md` §4, leaf 5 (3).  For the removed outcome (and `ϰ₅`) the factor
`e^{-𝒢^♮ - 𝒜_win} const^♮ / const` of the integrated window kernel, after division by the
denominator of `R` (Lemma III.8.2), is bounded by
`e^{(N/2) log β_k |Z₀| - Ẽ₀ + 1 + 3 + |C^♮_0| + C_{k₁,k}}`, where `𝒜_win = β_k A*_k(X_win) - C_{k₁,k}`.

* `removedFactor_le_of_identity`: the arithmetic, for real numbers satisfying the real form of
  (2.58′), the denominator identity `den = e^{-A_den - (N/2) log β_k |Z₀| + Ẽ₀}` and the bounds of
  Lemma III.6.4; the bound carries the term `A_den - β_k A*_k(Z; ψ⁰_k, φ⁰_k)`, which is `0` when the
  denominator is the source one (its action is the action `A*_k(Z; ·)` of (2.58′));
* `cancelBracket_add_Cnat1_ge`: the consequence of Lemma III.6.4 used here, on the real domain:
  `β_k{⋯} + C^♮_1 ≥ -½`, from the landed bound on `C^♮_1` (`Cnat1_le`), the bounds (b), (c) of
  Lemma III.6.4 and the non-negativity of the squares of the fluctuation action;
* `removedFactor_le`: the bound for the landed objects of (2.58′) (`cancellation_identity`), with
  the conclusions of `cancellation_identity` and `remaining_terms_of_lemma262` as hypotheses.

**Gap.** With the landed reference density (`rhoZero`, `denominator_eq`) the action of the
denominator is `β_k effActionNorm G' ψ⁰_k`, the action on all of `Ω₁(G')`, while (2.58′) has the
action `A*_k(Z; ψ⁰_k, φ⁰_k)` on the region `Z`; the difference stays in the bound as the term
`A_den - A_Z` (LF4R-PLAN §4.3 item 2).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField.ActionConv

open Balaban Balaban.Multiscale Balaban.Background Balaban.LargeField Finset

section Arith

/-- **The pointwise bound (2.58′) for the removed outcome, arithmetic form.**  Let
`G♮ + A_w - log const♮ = A_Z - A_0 + B + S_st - log const + (C₀ + C₁)` (the real form of (2.58′):
`G♮` the composed-Gaussian exponent, `A_w = β_k A*_k(X_win)`, `A_Z = β_k A*_k(Z; ψ⁰_k, φ⁰_k)`,
`A_0 = β_k A*_{0,k}(Z_{k₁}; φ⁰_k)`, `B = β_k{⋯}`, `S_st = β_k S_st`, `C^♮ = C₀ + C₁`), let
`den = e^{-A_den - nlb + Ẽ₀}` (Lemma III.8.2, `nlb = (N/2) log β_k |Z₀|`), and let `|A_0| < ¼`,
`|S_st| < ¼` (Lemma III.6.4 (a), (c)) and `B + C₁ ≥ -½` (`cancelBracket_add_Cnat1_ge`).  Then
`e^{-G♮ - (A_w - C_{k₁,k})} const♮ / const / den ≤ e^{nlb - Ẽ₀ + (A_den - A_Z) + 1 + 3 + |C₀| + C_{k₁,k}}`. -/
theorem removedFactor_le_of_identity {Gn Aw Ckk lcn lc AZ A0 B Sst C0 C1 den Aden nlb E0 : ℝ}
    (h258 : Gn + Aw - lcn = AZ - A0 + B + Sst - lc + (C0 + C1))
    (hden : den = Real.exp (-Aden - nlb + E0)) (hA0 : |A0| < 1 / 4) (hSst : |Sst| < 1 / 4)
    (hB : -(1 / 2) ≤ B + C1) :
    Real.exp (-Gn - (Aw - Ckk)) * Real.exp lcn / Real.exp lc / den ≤
      Real.exp (nlb - E0 + (Aden - AZ) + 1 + 3 + |C0| + Ckk) := by
  have e : Real.exp (-Gn - (Aw - Ckk)) * Real.exp lcn / Real.exp lc / den =
      Real.exp (-Gn - (Aw - Ckk) + lcn - lc - (-Aden - nlb + E0)) := by
    rw [hden, ← Real.exp_add, ← Real.exp_sub, ← Real.exp_sub]
  rw [e]
  refine Real.exp_le_exp.2 ?_
  have h1 := (abs_lt.1 hA0).2
  have h2 := (abs_lt.1 hSst).1
  have h3 := neg_abs_le C0
  linarith

end Arith

section Squares

variable {d L N₀ K N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ K ϱ}

theorem re_mul_self_of_im {z : ℂ} (h : z.im = 0) : (z * z).re = z.re * z.re := by
  simp [Complex.mul_re, h]

theorem re_blockPair_self_nonneg (D : Region G) {a : ℕ → ℝ} (ha : ∀ j, 0 ≤ a j)
    {v : Torus d (N₀ * L ^ K) → Fin N → ℂ} (hv : ∀ x i, (v x i).im = 0) :
    0 ≤ (D.blockPair a v v).re := by
  unfold Region.blockPair levelCoeff
  rw [Complex.re_sum]
  refine Finset.sum_nonneg fun x _ => ?_
  rw [Complex.re_ofReal_mul, Complex.re_sum]
  refine mul_nonneg (div_nonneg (ha _) (by positivity)) (Finset.sum_nonneg fun i _ => ?_)
  rw [re_mul_self_of_im (hv x i)]
  exact mul_self_nonneg _

theorem re_bondPair_self_nonneg (D : Region G) {f : Torus d (N₀ * L ^ K) → Fin N → ℂ}
    (hf : ∀ x i, (f x i).im = 0) : 0 ≤ (D.bondPair f f).re := by
  unfold Region.bondPair
  rw [Complex.re_sum]
  refine Finset.sum_nonneg fun x _ => ?_
  rw [Complex.re_sum]
  refine Finset.sum_nonneg fun μ _ => ?_
  rw [Complex.re_ofReal_mul, Complex.re_sum]
  have hw : 0 ≤ D.starWeight x μ := by
    unfold Region.starWeight
    split_ifs <;> norm_num
  refine mul_nonneg hw (Finset.sum_nonneg fun i _ => ?_)
  have him : (f (x + Pi.single μ 1) i - f x i).im = 0 := by
    rw [Complex.sub_im, hf, hf, sub_zero]
  rw [re_mul_self_of_im him]
  exact mul_self_nonneg _

theorem re_massPair_self_nonneg (D : Region G) {p : Torus d (N₀ * L ^ K) → Fin N → ℂ}
    (hp : ∀ x i, (p x i).im = 0) : 0 ≤ (D.massPair p p).re := by
  unfold Region.massPair
  rw [Complex.re_sum]
  refine Finset.sum_nonneg fun x _ => ?_
  rw [Complex.re_sum]
  refine Finset.sum_nonneg fun i _ => ?_
  rw [re_mul_self_of_im (hp x i)]
  exact mul_self_nonneg _

theorem re_dotC_self_of_im {v : Fin N → ℂ} (hv : ∀ i, (v i).im = 0) :
    (dotC v v).re = vn v ^ 2 := by
  unfold dotC vn
  rw [EuclideanSpace.norm_sq_eq, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [re_mul_self_of_im (hv i)]
  have : ‖v i‖ = |(v i).re| := by
    rw [← Complex.abs_re_eq_norm.2 (hv i)]
  rw [show ‖(WithLp.toLp 2 v : EuclideanSpace ℂ (Fin N)) i‖ = ‖v i‖ from rfl, this, sq_abs]
  ring

end Squares

section Bracket

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] [NeZero N] {ϱ ϱ' : ℝ}
  {G : GeneratingSet d L N₀ k ϱ} {G' : GeneratingSet d L N₀ k ϱ'}
  (a₁ : ℝ) (hprec : Precedes G G') (ψ0 : BlockV d L N₀ k → EuclideanSpace ℝ (Fin N))
  (h : Fin N → ℝ)

/-- **The consequence of Lemma III.6.4 used for the removed outcome** (LFR Lemma III.6.4, last
sentence: `β_k{⋯} + C^♮_1 ≥ -1`, here `≥ -½`), on the real domain: the composed-Gaussian term
`½ ∑_z β_k a^♮_z |Q_zδψ|²` controls `C^♮_1` (`Cnat1_le`, `|C^♮_1| ≤ ⅜` of it), the block, bond and
mass squares of the fluctuation action `δA*_k` are non-negative, and the multiplier term and the
`ν`-term are `< ¼` (Lemma III.6.4 (b), (c), `remaining_terms_of_lemma262`).  The data `Du`, the
window datum, `φu` and `φ⁰_k` are real (the real domain); the weights and `ν` are non-negative. -/
theorem cancelBracket_add_Cnat1_ge (Du : BgData G N) (Zb : Finset (Torus d (N₀ * L ^ (k - k))))
    {β0 : ℝ} (hβ0 : 0 ≤ β0) (ϖ : ℕ → ℝ) (aN : Torus d (N₀ * L ^ (k - k)) → ℝ)
    (haN : ∀ z ∈ Zb, 0 ≤ aN z) (D : Region G) {ν : ℝ} (hν : 0 ≤ ν) {φu : G.Ω 1 × Fin N → ℂ}
    (ha : ∀ j, 0 ≤ compWeight L a₁ j)
    (hDat : (windowData G G' hprec (compWeight L a₁) ψ0 h).IsReal) (hDu : Du.IsReal)
    (hφu : ∀ p, (φu p).im = 0)
    (hφ : ∀ p, (hprec.restrictφ (phiZero G' (compWeight L a₁) ψ0 h) p).im = 0)
    (hb : ‖(1 / 2 : ℂ) * (β0 : ℂ) * D.sitePair (hprec.restrictα (alphaZero G' (compWeight L a₁) ψ0 h))
        (svec G (φu - hprec.restrictφ (phiZero G' (compWeight L a₁) ψ0 h)))
        (svec G (φu - hprec.restrictφ (phiZero G' (compWeight L a₁) ψ0 h)))‖ < 1 / 4)
    (hc : ‖(β0 : ℂ) * nuTerm D ν (windowData G G' hprec (compWeight L a₁) ψ0 h)
        (hprec.restrictφ (phiZero G' (compWeight L a₁) ψ0 h)) φu‖ < 1 / 4) :
    -(1 / 2) ≤ (((betaK d L k β0 : ℝ) : ℂ) * ∑ z ∈ Zb, (1 / 2 : ℂ) * (aN z : ℂ) *
          dotC (kAvg (dataInc (windowData G G' hprec (compWeight L a₁) ψ0 h) Du) z)
            (kAvg (dataInc (windowData G G' hprec (compWeight L a₁) ψ0 h) Du) z) +
        (β0 : ℂ) * (deltaActionC D (compWeight L a₁) ν (windowData G G' hprec (compWeight L a₁) ψ0 h) Du
            (hprec.restrictφ (phiZero G' (compWeight L a₁) ψ0 h)) φu
            (hprec.restrictα (alphaZero G' (compWeight L a₁) ψ0 h)) +
          nuTerm D ν (windowData G G' hprec (compWeight L a₁) ψ0 h)
            (hprec.restrictφ (phiZero G' (compWeight L a₁) ψ0 h)) φu)).re +
      (Cnat1 a₁ hprec ψ0 h Du Zb β0 ϖ aN).re := by
  set Dat := windowData G G' hprec (compWeight L a₁) ψ0 h with hDatdef
  set φ := hprec.restrictφ (phiZero G' (compWeight L a₁) ψ0 h) with hφdef
  set α := hprec.restrictα (alphaZero G' (compWeight L a₁) ψ0 h) with hαdef
  set q := fun z => kAvg (dataInc Dat Du) z with hq
  set βk := betaK d L k β0 with hβk
  have hβk0 : 0 ≤ βk := by rw [hβk]; unfold betaK; positivity
  -- realness of the increments
  have hinc : ∀ x i, (dataInc Dat Du x i).im = 0 := fun x i => by
    unfold dataInc; rw [Complex.sub_im, (hDu x i).1, (hDat x i).1, sub_zero]
  have hqre : ∀ z i, (q z i).im = 0 := fun z i => by
    show (kAvg (dataInc Dat Du) z i).im = 0
    unfold kAvg
    simp [Complex.mul_im, Complex.im_sum, hinc]
  have hdφ : ∀ p, ((φu - φ) p).im = 0 := fun p => by
    rw [Pi.sub_apply, Complex.sub_im, hφu, hφ, sub_zero]
  have hv : ∀ x i, (dataInc Dat Du x i - blockAvg G (φu - φ) x i).im = 0 := fun x i => by
    rw [Complex.sub_im, hinc, blockAvg_im_of_real hdφ, sub_zero]
  have hw : ∀ x i, (wExt Dat Du φ φu x i).im = 0 := fun x i => by
    unfold wExt
    rw [Complex.sub_im, barField_im_of_real hDu hφu, barField_im_of_real hDat hφ, sub_zero]
  have hs : ∀ x i, (svec G (φu - φ) x i).im = 0 := svec_im_of_real hdφ
  -- the composed-Gaussian term
  set Q := ∑ z ∈ Zb, βk * aN z * vn (q z) ^ 2 with hQ
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg fun z hz => by have := haN z hz; positivity
  have hgauss : ((βk : ℂ) * ∑ z ∈ Zb, (1 / 2 : ℂ) * (aN z : ℂ) * dotC (q z) (q z)).re = Q / 2 := by
    rw [Complex.re_ofReal_mul, Complex.re_sum, hQ, Finset.sum_div, Finset.mul_sum]
    refine Finset.sum_congr rfl fun z _ => ?_
    have e : (1 / 2 : ℂ) * (aN z : ℂ) = ((aN z / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [e, Complex.re_ofReal_mul, re_dotC_self_of_im (hqre z)]
    ring
  -- the fluctuation action
  have hδA : -(1 / 4) ≤ ((β0 : ℂ) * deltaActionC D (compWeight L a₁) ν Dat Du φ φu α).re := by
    have e : (β0 : ℂ) * deltaActionC D (compWeight L a₁) ν Dat Du φ φu α =
        ((β0 / 2 : ℝ) : ℂ) * D.blockPair (compWeight L a₁)
            (fun x i => dataInc Dat Du x i - blockAvg G (φu - φ) x i)
            (fun x i => dataInc Dat Du x i - blockAvg G (φu - φ) x i) +
          ((β0 / 2 : ℝ) : ℂ) * D.bondPair (wExt Dat Du φ φu) (wExt Dat Du φ φu) +
          (1 / 2 : ℂ) * (β0 : ℂ) * D.sitePair α (svec G (φu - φ)) (svec G (φu - φ)) +
          ((β0 * ν / 2 : ℝ) : ℂ) * D.massPair (svec G (φu - φ)) (svec G (φu - φ)) := by
      unfold deltaActionC; push_cast; ring
    rw [e, Complex.add_re, Complex.add_re, Complex.add_re, Complex.re_ofReal_mul,
      Complex.re_ofReal_mul, Complex.re_ofReal_mul]
    have h1 := re_blockPair_self_nonneg D ha hv
    have h2 := re_bondPair_self_nonneg D hw
    have h3 := re_massPair_self_nonneg D hs
    have h4 := (abs_le.1 ((Complex.abs_re_le_norm _).trans hb.le)).1
    have h5 : 0 ≤ β0 / 2 := by positivity
    have h6 : 0 ≤ β0 * ν / 2 := by positivity
    nlinarith [mul_nonneg h5 h1, mul_nonneg h5 h2, mul_nonneg h6 h3]
  have hnu : -(1 / 4) ≤ ((β0 : ℂ) * nuTerm D ν Dat φ φu).re :=
    (abs_le.1 ((Complex.abs_re_le_norm _).trans hc.le)).1
  have hC1 : -(3 / 8 * Q) ≤ (Cnat1 a₁ hprec ψ0 h Du Zb β0 ϖ aN).re := by
    have := Cnat1_le a₁ hprec ψ0 h Du Zb hβ0 ϖ aN haN
    have h' := (abs_le.1 ((Complex.abs_re_le_norm _).trans this)).1
    simpa [hQ, hq, hβk] using h'
  have e : (((βk : ℝ) : ℂ) * ∑ z ∈ Zb, (1 / 2 : ℂ) * (aN z : ℂ) * dotC (q z) (q z) +
      (β0 : ℂ) * (deltaActionC D (compWeight L a₁) ν Dat Du φ φu α + nuTerm D ν Dat φ φu)).re =
      ((βk : ℂ) * ∑ z ∈ Zb, (1 / 2 : ℂ) * (aN z : ℂ) * dotC (q z) (q z)).re +
        ((β0 : ℂ) * deltaActionC D (compWeight L a₁) ν Dat Du φ φu α).re +
        ((β0 : ℂ) * nuTerm D ν Dat φ φu).re := by
    rw [mul_add, Complex.add_re, Complex.add_re]; ring
  rw [e, hgauss]
  linarith

end Bracket

section Landed

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] [NeZero N] {ϱ ϱ' : ℝ}
  {G : GeneratingSet d L N₀ k ϱ} {G' : GeneratingSet d L N₀ k ϱ'}

theorem constNat_pos {βk : ℝ} (hβ : 0 < βk) {aN : Torus d (N₀ * L ^ (k - k)) → ℝ}
    {Zb : Finset (Torus d (N₀ * L ^ (k - k)))} (haN : ∀ z ∈ Zb, 0 < aN z) :
    0 < constNat N βk aN Zb := by
  unfold constNat
  refine Finset.prod_pos fun z hz => Real.rpow_pos_of_pos ?_ _
  have := haN z hz
  positivity

/-- **The pointwise bound (2.58′) for the removed outcome** (Lemma III.8.7 step (2), removed
bullet), for the landed objects of `cancellation_identity`: with `𝒢^♮ = gaussNat`,
`β_k A*_k(X_win) = β₀ actionRegionC D`, `𝒜_win = β_k A*_k(X_win) - C_{k₁,k}`,
`const^♮ = constNat … aN`, `const = constNat … compWeightZ`, and a denominator
`den = e^{-A_den - (N/2) log β_k n₀ + Ẽ₀}` (Lemma III.8.2, `n₀ = |Z₀|`):
`e^{-𝒢^♮ - 𝒜_win} const^♮ / const / den ≤
  e^{(N/2) log β_k n₀ - Ẽ₀ + (A_den - β_k A*_k(Z; ψ⁰_k, φ⁰_k)) + 1 + 3 + |C^♮_0| + C_{k₁,k}}`.
Hypotheses: the identity (2.58′) (the conclusion of `cancellation_identity`), the bounds (a)-(c)
of Lemma III.6.4 (the conclusions of `remaining_terms_of_lemma262`), the real domain, positive
weights `a^♮_z`, the layers of the window blocks (for `a_z > 0`), and the denominator identity.  In
the source the action of the denominator is `β_k A*_k(Z; ψ⁰_k, φ⁰_k)`, so `A_den - A_Z = 0`; with the
landed `denominator_eq` it is `β_k effActionNorm G' ψ⁰_k` (LF4R-PLAN §4.3 item 2). -/
theorem removedFactor_le {a₁ : ℝ} (hprec : Precedes G G')
    (ψ0 : BlockV d L N₀ k → EuclideanSpace ℝ (Fin N)) (h : Fin N → ℝ) (Du : BgData G N)
    {φu : G.Ω 1 × Fin N → ℂ} (D : Region G) (Zr Zk1 : Region G')
    (Zb : Finset (Torus d (N₀ * L ^ (k - k)))) {β0 ν : ℝ} (ϖ : ℕ → ℝ)
    (aN : Torus d (N₀ * L ^ (k - k)) → ℝ) (ψk : Torus d (N₀ * L ^ (k - k)) → Fin N → ℂ)
    (hβ0 : 0 < β0) (hν : 0 ≤ ν) (ha₁ : 0 < a₁) (hL : 2 ≤ L) (ha : ∀ j, 0 ≤ compWeight L a₁ j)
    (haN : ∀ z ∈ Zb, 0 < aN z)
    (hZb : ∀ z ∈ Zb, ∀ x ∈ fib d L N₀ k k z, 1 ≤ G.layerIndex x ∧ G.layerIndex x < k)
    (hDat : (windowData G G' hprec (compWeight L a₁) ψ0 h).IsReal) (hDu : Du.IsReal)
    (hφu : ∀ p, (φu p).im = 0)
    (hφ : ∀ p, (hprec.restrictφ (phiZero G' (compWeight L a₁) ψ0 h) p).im = 0)
    (hid : gaussNat G ϖ Du.Ψ (betaK d L k β0) aN ψk Zb +
          (β0 : ℂ) * actionRegionC D (compWeight L a₁) ν Du φu -
          ((Real.log (constNat N (betaK d L k β0) aN Zb) : ℝ) : ℂ) =
        (β0 : ℂ) * actionRegionC Zr (compWeight L a₁) ν (psiZeroData G' ψ0 h)
            (phiZero G' (compWeight L a₁) ψ0 h) -
          (β0 : ℂ) * actionRegion0 Zk1 ν (psiZeroData G' ψ0 h) (phiZero G' (compWeight L a₁) ψ0 h) +
          ((betaK d L k β0 : ℝ) * ∑ z ∈ Zb, (1 / 2 : ℂ) * (aN z : ℂ) *
              dotC (kAvg (dataInc (windowData G G' hprec (compWeight L a₁) ψ0 h) Du) z)
                (kAvg (dataInc (windowData G G' hprec (compWeight L a₁) ψ0 h) Du) z) +
            (β0 : ℂ) * (deltaActionC D (compWeight L a₁) ν
                (windowData G G' hprec (compWeight L a₁) ψ0 h) Du
                (hprec.restrictφ (phiZero G' (compWeight L a₁) ψ0 h)) φu
                (hprec.restrictα (alphaZero G' (compWeight L a₁) ψ0 h)) +
              nuTerm D ν (windowData G G' hprec (compWeight L a₁) ψ0 h)
                (hprec.restrictφ (phiZero G' (compWeight L a₁) ψ0 h)) φu)) +
          (β0 : ℂ) * stTerm D (windowData G G' hprec (compWeight L a₁) ψ0 h) Du
            (hprec.restrictφ (phiZero G' (compWeight L a₁) ψ0 h)) φu -
          ((Real.log (constNat N (betaK d L k β0) (compWeightZ G a₁) Zb) : ℝ) : ℂ) +
          Cnat a₁ hprec ψ0 h Du Zb β0 ϖ aN ψk)
    (hA0 : ‖(β0 : ℂ) * actionRegion0 Zk1 ν (psiZeroData G' ψ0 h)
      (phiZero G' (compWeight L a₁) ψ0 h)‖ < 1 / 4)
    (hb : ‖(1 / 2 : ℂ) * (β0 : ℂ) * D.sitePair (hprec.restrictα (alphaZero G' (compWeight L a₁) ψ0 h))
        (svec G (φu - hprec.restrictφ (phiZero G' (compWeight L a₁) ψ0 h)))
        (svec G (φu - hprec.restrictφ (phiZero G' (compWeight L a₁) ψ0 h)))‖ < 1 / 4)
    (hst : ‖(β0 : ℂ) * stTerm D (windowData G G' hprec (compWeight L a₁) ψ0 h) Du
        (hprec.restrictφ (phiZero G' (compWeight L a₁) ψ0 h)) φu‖ < 1 / 4)
    (hnu : ‖(β0 : ℂ) * nuTerm D ν (windowData G G' hprec (compWeight L a₁) ψ0 h)
        (hprec.restrictφ (phiZero G' (compWeight L a₁) ψ0 h)) φu‖ < 1 / 4)
    {den Aden E0 : ℝ} (n0 : ℝ)
    (hden : den = Real.exp (-Aden - (N : ℝ) / 2 * Real.log (betaK d L k β0) * n0 + E0))
    (Ckk : ℝ) :
    Real.exp (-(gaussNat G ϖ Du.Ψ (betaK d L k β0) aN ψk Zb).re -
          (((β0 : ℂ) * actionRegionC D (compWeight L a₁) ν Du φu).re - Ckk)) *
        constNat N (betaK d L k β0) aN Zb / constNat N (betaK d L k β0) (compWeightZ G a₁) Zb /
        den ≤
      Real.exp ((N : ℝ) / 2 * Real.log (betaK d L k β0) * n0 - E0 +
        (Aden - ((β0 : ℂ) * actionRegionC Zr (compWeight L a₁) ν (psiZeroData G' ψ0 h)
          (phiZero G' (compWeight L a₁) ψ0 h)).re) + 1 + 3 +
        ‖Cnat0 a₁ hprec ψ0 h Du Zb β0 ϖ aN ψk‖ + Ckk) := by
  have hβk : 0 < betaK d L k β0 := by unfold betaK; positivity
  have hc1 := constNat_pos (N := N) hβk haN
  have hc2 := constNat_pos (N := N) hβk (fun z hz => compWeightZ_pos ha₁ hL G (hZb z hz))
  rw [← Real.exp_log hc1, ← Real.exp_log hc2]
  have hre := congrArg Complex.re hid
  rw [Cnat_eq_zero_add_one] at hre
  simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re] at hre
  have hB := cancelBracket_add_Cnat1_ge a₁ hprec ψ0 h Du Zb hβ0.le ϖ aN (fun z hz => (haN z hz).le) D
    hν ha hDat hDu hφu hφ hb hnu
  have hA0' : |((β0 : ℂ) * actionRegion0 Zk1 ν (psiZeroData G' ψ0 h)
      (phiZero G' (compWeight L a₁) ψ0 h)).re| < 1 / 4 :=
    (Complex.abs_re_le_norm _).trans_lt hA0
  have hst' : |((β0 : ℂ) * stTerm D (windowData G G' hprec (compWeight L a₁) ψ0 h) Du
      (hprec.restrictφ (phiZero G' (compWeight L a₁) ψ0 h)) φu).re| < 1 / 4 :=
    (Complex.abs_re_le_norm _).trans_lt hst
  simp only [Complex.add_re] at hB
  set Gn := (gaussNat G ϖ Du.Ψ (betaK d L k β0) aN ψk Zb).re
  set Aw := ((β0 : ℂ) * actionRegionC D (compWeight L a₁) ν Du φu).re
  set AZ := ((β0 : ℂ) * actionRegionC Zr (compWeight L a₁) ν (psiZeroData G' ψ0 h)
    (phiZero G' (compWeight L a₁) ψ0 h)).re
  set A0 := ((β0 : ℂ) * actionRegion0 Zk1 ν (psiZeroData G' ψ0 h)
    (phiZero G' (compWeight L a₁) ψ0 h)).re
  set Sst := ((β0 : ℂ) * stTerm D (windowData G G' hprec (compWeight L a₁) ψ0 h) Du
      (hprec.restrictφ (phiZero G' (compWeight L a₁) ψ0 h)) φu).re
  set C0 := (Cnat0 a₁ hprec ψ0 h Du Zb β0 ϖ aN ψk).re
  set C1 := (Cnat1 a₁ hprec ψ0 h Du Zb β0 ϖ aN).re
  set B := (((betaK d L k β0 : ℝ) : ℂ) * ∑ z ∈ Zb, (1 / 2 : ℂ) * (aN z : ℂ) *
          dotC (kAvg (dataInc (windowData G G' hprec (compWeight L a₁) ψ0 h) Du) z)
            (kAvg (dataInc (windowData G G' hprec (compWeight L a₁) ψ0 h) Du) z)).re +
      ((β0 : ℂ) * (deltaActionC D (compWeight L a₁) ν
          (windowData G G' hprec (compWeight L a₁) ψ0 h) Du
          (hprec.restrictφ (phiZero G' (compWeight L a₁) ψ0 h)) φu
          (hprec.restrictα (alphaZero G' (compWeight L a₁) ψ0 h)) +
        nuTerm D ν (windowData G G' hprec (compWeight L a₁) ψ0 h)
          (hprec.restrictφ (phiZero G' (compWeight L a₁) ψ0 h)) φu)).re
  have h258 : Gn + Aw - Real.log (constNat N (betaK d L k β0) aN Zb) =
      AZ - A0 + B + Sst - Real.log (constNat N (betaK d L k β0) (compWeightZ G a₁) Zb) +
        (C0 + C1) := by
    linarith [hre]
  have key := removedFactor_le_of_identity (Ckk := Ckk) (Aden := Aden) (E0 := E0)
    (nlb := (N : ℝ) / 2 * Real.log (betaK d L k β0) * n0) h258 hden hA0' hst' hB
  refine key.trans (Real.exp_le_exp.2 ?_)
  have := Complex.abs_re_le_norm (Cnat0 a₁ hprec ψ0 h Du Zb β0 ϖ aN ψk)
  linarith

end Landed

end Balaban.LargeField.ActionConv
