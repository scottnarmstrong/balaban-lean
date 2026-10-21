/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseMainAction
public import Balaban.LargeField.LF1.Violation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The `Q_1` and `S_1` gains on the base main action (P6 (3.7)-(3.8) through LF-1)

A failed `χ'_1` (`Q_1`) or `χ_1` (`S_1`) test at a cube `□'` is, through BG Theorem 5.2 (3)
(`R/ChiBridge.lean`, `chiK_eq_one_of_psiTilde`), a violation of the small-field space
`ψ_1 ∈ Ψ̃(blocks ⊂ Xc; θ)` of the block field `ψ_1` on the blocks of `Xc`, and LF-1 applied to the
main action charges the violation (`lf1_violation_gain`).  This file states the charge on
`baseMainAction`, the real-variable form that turns it into the factor `exp(-γ₀ p_0²/(8 a κ²))`
of the proof of Lemma II.7.8, and the double count over cubes.

* `baseMainAction_violation_gain_of_geometry`: a violation of `Ψ̃(·; θ)` in the top layer of the
  history's generating set at level `1` gives
  `𝒜^base_1 ≥ γ₀ β_1 θ²/2` (`β_1 = cs.beta 1`);
* `violation_gain_real`: `A ≥ γ β_1 θ²/2`, `β_1 ≥ β/2`, `δ_0 ≤ κ θ`, `δ_0² a β = p_0²` give
  `e^{-A/2} ≤ e^{-γ p_0²/(8 a κ²)}`;
* `card_mul_le_of_overlap`: if every site lies in at most `m` of the regions `R_i`, and each region
  carries at least `c` of a non-negative density, then `|I| c ≤ m ∑_T t`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open MeasureTheory Balaban Balaban.Multiscale Balaban.Background RegionHistory

/-- **Real form of the `Q_1`/`S_1` gain**: `e^{-A/2} ≤ e^{-γ p_0²/(8 a κ²)}` when
`A ≥ γ β_1 θ²/2`, `β/2 ≤ β_1`, `δ_0 ≤ κ θ` and `δ_0² a β = p_0²`. -/
theorem violation_gain_real {A γ β₁ β a p₀ δ₀ θ κ : ℝ} (ha : 0 < a) (hβ : 0 < β) (hκ : 0 < κ)
    (hγ : 0 ≤ γ) (hδ : δ₀ ^ 2 * (a * β) = p₀ ^ 2) (hδ0 : 0 ≤ δ₀) (hθ : δ₀ ≤ κ * θ)
    (hβ₁ : β / 2 ≤ β₁) (hA : γ * (β₁ * (θ ^ 2 / 2)) ≤ A) :
    Real.exp (-(A / 2)) ≤ Real.exp (-(γ * p₀ ^ 2 / (8 * a * κ ^ 2))) := by
  refine Real.exp_le_exp.mpr ?_
  have h1 : δ₀ ^ 2 ≤ (κ * θ) ^ 2 := pow_le_pow_left₀ hδ0 hθ 2
  have h2 : γ * p₀ ^ 2 / (8 * a * κ ^ 2) = γ * (β * δ₀ ^ 2) / (8 * κ ^ 2) := by
    field_simp
    nlinarith [hδ]
  rw [h2]
  have hβ1 : 0 ≤ β₁ := by linarith
  have h3 : β * δ₀ ^ 2 ≤ β * (κ * θ) ^ 2 := mul_le_mul_of_nonneg_left h1 hβ.le
  have h4 : β / 2 * θ ^ 2 ≤ β₁ * θ ^ 2 := mul_le_mul_of_nonneg_right hβ₁ (sq_nonneg θ)
  have h5 : γ * (β * δ₀ ^ 2) / (8 * κ ^ 2) ≤ γ * (β₁ * (θ ^ 2 / 2)) / 2 := by
    rw [div_le_iff₀ (by positivity)]
    have h6 : γ * (β * δ₀ ^ 2) ≤ γ * (β * (κ * θ) ^ 2) := mul_le_mul_of_nonneg_left h3 hγ
    have h7 : γ * (β * (κ * θ) ^ 2) = κ ^ 2 * (γ * (β * θ ^ 2)) := by ring
    have h8 : γ * (β * θ ^ 2) ≤ γ * (2 * (β₁ * θ ^ 2)) := by
      refine mul_le_mul_of_nonneg_left ?_ hγ
      linarith
    nlinarith [sq_nonneg κ, mul_nonneg (sq_nonneg κ) hγ]
  linarith

/-- **Double counting over cubes**: if every site of `T` lies in at most `m` of the regions `R_i`
(`i ∈ I`), each `R_i ⊆ T`, and each region carries at least `c` of the non-negative density `t`,
then `|I| c ≤ m ∑_{x ∈ T} t x` (the overlap `6^d` of P6 (3.7)-(3.8)). -/
theorem card_mul_le_of_overlap {ι σ : Type*} [DecidableEq σ] (I : Finset ι) (T : Finset σ)
    (R : ι → Finset σ) (t : σ → ℝ) (ht : ∀ x, 0 ≤ t x) (hR : ∀ i ∈ I, R i ⊆ T) (m : ℕ)
    (hm : ∀ x ∈ T, (I.filter fun i => x ∈ R i).card ≤ m) (c : ℝ)
    (hc : ∀ i ∈ I, c ≤ ∑ x ∈ R i, t x) :
    (I.card : ℝ) * c ≤ m * ∑ x ∈ T, t x := by
  classical
  have h1 : (I.card : ℝ) * c ≤ ∑ i ∈ I, ∑ x ∈ R i, t x := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum hc
  have h2 : ∑ i ∈ I, ∑ x ∈ R i, t x = ∑ x ∈ T, ((I.filter fun i => x ∈ R i).card : ℝ) * t x := by
    have : ∀ i ∈ I, ∑ x ∈ R i, t x = ∑ x ∈ T, if x ∈ R i then t x else 0 := fun i hi => by
      rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.2 (hR i hi)]
    rw [Finset.sum_congr rfl this, Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have h3 : ∑ x ∈ T, ((I.filter fun i => x ∈ R i).card : ℝ) * t x ≤ ∑ x ∈ T, (m : ℝ) * t x :=
    Finset.sum_le_sum fun x hx =>
      mul_le_mul_of_nonneg_right (by exact_mod_cast hm x hx) (ht x)
  rw [← Finset.mul_sum] at h3
  linarith

section Base

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} (g : Geo S n R M) (Hl : RegionHistory S n R k0 K)
  (Zc : Finset (Torus S.d (n (0 + 1))))
  (hZc : Zc ∈ comps (S.omega (0 + 1)) (Hl.F.Zp (0 + 1))) (hk : 0 + 1 ≤ K) (cs : OpConsts)
  (hrem : ∀ j, Hl.rem j = ∅)

/-- **A violation of `Ψ̃` costs** `γ₀ β_1 θ²/2` in the base main action (LF-1 (a), (b) on the top
layer `Λ_1 = Ω_1` of the history's generating set at level `1`; BASE-KERNEL (4.2a)-(4.2b)).
`Xc ⊆ Λ_1 ∩ X` is the set of sites where `ψ_1` is tested; the geometry premise `hX` says that
`X ∩ Λ_1` is a union of `1`-blocks (Lemma II.7.2), and `hφ` that the field `φ̂^X` is a unit field on
`Xc` (the constraint `φ·φ = 1` of the background on `Ω_1`, the spins on `Ω^c`). -/
theorem baseMainAction_violation_gain_of_geometry (hd : 2 ≤ S.d) (hL : 2 ≤ S.L)
    (hϱ : 2 * (S.d : ℝ) * S.L ≤ (S.L : ℝ) * M * S.Rb)
    (hadm : IsAdmissibleWeights (0 + 1) cs.aw) (hb : 0 ≤ cs.beta (0 + 1))
    (hμ : 0 ≤ cs.muAct (0 + 1))
    (hX : ∀ m, 1 ≤ m → m ≤ 0 + 1 → IsBlockUnion S.L (g.M1 * (g.c * n (0 + 1))) (0 + 1) m
      (Xfine g Hl 0 Zc ∩ (histGenLevel g Hl 0 hk hrem).layer m))
    (o : OutT N R (locHist Hl M K (0 + 1) Zc) (0 + 1))
    (x : NewCfg N (locHist Hl M K (0 + 1) Zc) 0) (hv : EuclideanSpace ℝ (Fin N))
    {Xc : Finset (Site S.d S.L (g.M1 * (g.c * n (0 + 1))) (0 + 1))}
    (hXcX : Xc ⊆ lam (histGenLevel g Hl 0 hk hrem) (0 + 1) ∩ Xfine g Hl 0 Zc)
    (hφ : ∀ z ∈ Xc, ‖baseFieldHat g Hl Zc hZc hk cs o x hv z‖ = 1) {θ : ℝ} (hθ : 0 ≤ θ)
    (hviol : ¬ PsiTildeSet
      {y : Blk S.d S.L (g.M1 * (g.c * n (0 + 1))) (0 + 1) (0 + 1) |
        fib S.d S.L (g.M1 * (g.c * n (0 + 1))) (0 + 1) (0 + 1) y ⊆ Xc}
      (psiLevel g Hl 0 hk
        (subMultiscaleField N (locHist Hl M K (0 + 1) Zc) (0 + 1)
          (Vblk R (locHist Hl M K (0 + 1) Zc) (0 + 1)) x o) (0 + 1)) θ) :
    gamma0 S.d * (cs.beta (0 + 1) * (θ ^ 2 / 2)) ≤
      baseMainAction g Hl Zc hZc hk cs hrem o x hv := by
  have hβ : 0 ≤ baseBeta S cs := by
    unfold baseBeta betaCanon; positivity
  have h := lf1_violation_gain (histGenLevel g Hl 0 hk hrem) (le_refl 1) hd hL hϱ hadm hμ hv hX
    hXcX
    (psiLevel g Hl 0 hk
      (subMultiscaleField N (locHist Hl M K (0 + 1) Zc) (0 + 1)
        (Vblk R (locHist Hl M K (0 + 1) Zc) (0 + 1)) x o))
    (baseFieldHat g Hl Zc hZc hk cs o x hv) hφ hθ hviol
  have h2 := starBondE_nonneg (Xfine g Hl 0 Zc) (baseFieldHat g Hl Zc hZc hk cs o x hv)
  have hLr : (0 : ℝ) < (S.L : ℝ) ^ ((0 + 1) * (S.d - 2)) := by
    have : 0 < S.L := Nat.pos_of_ne_zero (NeZero.ne S.L)
    positivity
  have e : baseBeta S cs * (S.L : ℝ) ^ ((0 + 1) * (S.d - 2)) = cs.beta (0 + 1) := by
    unfold baseBeta betaCanon
    simp only [Nat.sub_zero, Nat.zero_add]
    field_simp
  rw [baseMainAction_eq]
  refine le_trans ?_ (mul_le_mul_of_nonneg_left
    (show gamma0 S.d * ((S.L : ℝ) ^ ((0 + 1) * (S.d - 2)) * (θ ^ 2 / 2)) ≤ _ by linarith [h, h2]) hβ)
  rw [← e]
  nlinarith [mul_nonneg hβ (mul_nonneg (le_of_lt (show (0:ℝ) < gamma0 S.d from by
    unfold gamma0; have : (0:ℝ) < S.d := by exact_mod_cast (by omega : 0 < S.d)
    positivity)) (mul_nonneg hLr.le (sq_nonneg θ)))]

end Base

end Balaban.LargeField
