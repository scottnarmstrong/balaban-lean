module

public import Balaban.LargeField.Base.BaseMainAction
public import Balaban.LargeField.Base.BaseWitnessGauss
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# The block, bond and site gains of the base step (BASE-KERNEL §6, first three rows of the table)

The unconditional real-variable part of Lemma II.7.8 for the cubes of `P_1`:

* `tailQ_two_delta`, `baseBlock_gain`: block witness, `∫ g_0 1[|u| ≥ 2δ_0] ≤ 2^{N/2} e^{-L^{d-2} p_0^2}`
  (with `δ_0² = p_0(β)²/(a β)`), hence `m^w_0 ≤ (M^d 2^{N/2} e^{-L^{d-2} p_0²})^{#blk(w)}`;
* `bond_gain_real`, `baseMainAction_bond_gain`: bond witness, from (4.2): a bond with
  `|∂φ(b)| ≥ δ_0` in `Ω^c ∩ X` gives `e^{-𝒜^base/2} ≤ e^{-p_0²/(8a)}`;
* `site_gain_real`: site witness (regime (B)), `e^{-𝒜/2} ≤ e^{-p_0²/(9a)}`.

The rows for `Q_1`, `R_1`, `S_1` (P6 (3.4), (3.7), (3.8) through LF-1) and the assembly into
(6.1) are not in this file: they need the explicit retained factors of `K̃^w_0`, which depend on the
open Proposition II.7.9 (BASE-KERNEL §6, tasks 1-3).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open MeasureTheory Balaban Balaban.Multiscale Balaban.Background RegionHistory ENNReal

section Gains

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ}

/-- The one-block tail at radius `2δ_0` for the Gaussian of `t_0`:
`2^{N/2} e^{-(c (2δ_0)²/4)} = 2^{N/2} e^{-L^{d-2} p_0²}` when `c = β a L^{d-2}` and
`δ_0² a β = p_0²`. -/
theorem tailQ_two_delta (N : ℕ) (β a Ld δ₀ p₀ : ℝ) (hδ : δ₀ ^ 2 * (a * β) = p₀ ^ 2) :
    tailQ N (β * a * Ld) (2 * δ₀) =
      ENNReal.ofReal (2 ^ ((N : ℝ) / 2) * Real.exp (-(Ld * p₀ ^ 2))) := by
  have h : β * a * Ld * (2 * δ₀) ^ 2 / 4 = Ld * p₀ ^ 2 := by rw [← hδ]; ring
  unfold tailQ
  rw [h]

/-- **Block-witness gain**: `m^w_0 ≤ (M^d 2^{N/2} e^{-L^{d-2} p_0²})^{#blk(w)}`. -/
theorem baseBlock_gain [NeZero N] (a : LocalHistory S n M K) (cs : OpConsts)
    (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) (hK : 0 + 1 ≤ K)
    (hc : 0 < cs.beta 0 * cs.aKer * (S.L : ℝ) ^ (S.d - 2)) (hδ0 : 0 ≤ cs.delta 0)
    (hδ : cs.delta 0 ^ 2 * (cs.aKer * cs.beta 0) = cs.p0 0 ^ 2) (w : BaseW a 0) :
    mWit N (cs.beta 0 * cs.aKer * (S.L : ℝ) ^ (S.d - 2)) a 0 (baseF a 0 (cs.delta 0)) w ≤
      ((M : ℝ≥0∞) ^ S.d * ENNReal.ofReal (2 ^ ((N : ℝ) / 2) *
        Real.exp (-((S.L : ℝ) ^ (S.d - 2) * cs.p0 0 ^ 2)))) ^ (baseBlk a 0 w).card := by
  have h := mWit_baseF_le (N := N) a 0 hnn hK hc hδ0 w
  rwa [tailQ_two_delta N (cs.beta 0) cs.aKer _ _ _ hδ] at h

/-- **Bond-witness gain**, real form: if `A ≥ (β_1/2) t²` with `t ≥ δ_0`, `β_1 ≥ β/2`, `a, β > 0`
and `δ_0² a β = p_0²`, then `e^{-A/2} ≤ e^{-p_0²/(8a)}`. -/
theorem bond_gain_real {A β₁ β a p₀ δ₀ t : ℝ} (ha : 0 < a) (hβ : 0 < β)
    (hδ : δ₀ ^ 2 * (a * β) = p₀ ^ 2) (hδ0 : 0 ≤ δ₀) (hβ₁ : β / 2 ≤ β₁)
    (hA : β₁ / 2 * t ^ 2 ≤ A) (ht : δ₀ ≤ t) :
    Real.exp (-(A / 2)) ≤ Real.exp (-(p₀ ^ 2 / (8 * a))) := by
  refine Real.exp_le_exp.mpr ?_
  have h1 : δ₀ ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ hδ0 ht 2
  have h2 : p₀ ^ 2 / (8 * a) = β * δ₀ ^ 2 / 8 := by
    field_simp
    nlinarith [hδ]
  rw [h2]
  have h3 : 0 ≤ β₁ := by linarith
  nlinarith [mul_le_mul_of_nonneg_left h1 h3, mul_le_mul_of_nonneg_right hβ₁ (sq_nonneg t)]

/-- **Site-witness gain** (regime (B)), real form: if `A ≥ β_1 μ s² / 2`, `ν s² ≥ δ_0²`,
`β_1 ≥ β/2`, `μ ≥ (8/9) ν` (`μ ≥ ν e^{-ε}`), then `e^{-A/2} ≤ e^{-p_0²/(9a)}`. -/
theorem site_gain_real {A β₁ μ ν β a p₀ δ₀ s : ℝ} (ha : 0 < a) (hβ : 0 < β) (hν : 0 < ν)
    (hδ : δ₀ ^ 2 * (a * β) = p₀ ^ 2) (hβ₁ : β / 2 ≤ β₁) (hμ : 8 / 9 * ν ≤ μ)
    (hA : β₁ * μ / 2 * s ^ 2 ≤ A) (hs : δ₀ ^ 2 ≤ ν * s ^ 2) :
    Real.exp (-(A / 2)) ≤ Real.exp (-(p₀ ^ 2 / (9 * a))) := by
  refine Real.exp_le_exp.mpr ?_
  have h2 : p₀ ^ 2 / (9 * a) = β * δ₀ ^ 2 / 9 := by
    field_simp
    nlinarith [hδ]
  rw [h2]
  have hs2 : 0 ≤ s ^ 2 := sq_nonneg s
  have h3 : β / 2 * (8 / 9 * ν) ≤ β₁ * μ := by
    have h0 : 0 ≤ β₁ := by linarith
    calc β / 2 * (8 / 9 * ν) ≤ β₁ * (8 / 9 * ν) :=
          mul_le_mul_of_nonneg_right hβ₁ (by positivity)
      _ ≤ β₁ * μ := mul_le_mul_of_nonneg_left hμ h0
  have h4 : β / 2 * (8 / 9 * ν) * s ^ 2 ≤ β₁ * μ * s ^ 2 := mul_le_mul_of_nonneg_right h3 hs2
  nlinarith [mul_le_mul_of_nonneg_left hs hβ.le]

variable (g : Geo S n R M) (Hl : RegionHistory S n R k0 K) (Zc : Finset (Torus S.d (n (0 + 1))))
  (hZc : Zc ∈ comps (S.omega (0 + 1)) (Hl.F.Zp (0 + 1))) (hk : 0 + 1 ≤ K) (cs : OpConsts)
  (hrem : ∀ j, Hl.rem j = ∅)

/-- **Bond-witness gain for the base main action**: a bond `(z, z + e_μ)` of `Ω^c ∩ X` on which the
spin field has `|∂φ| ≥ δ_0` gives `e^{-𝒜^base_1/2} ≤ e^{-p_0²/(8a)}`.  The premise
`β/2 ≤ β^{(1)}_0` is `β^{(1)}_0 = β/(1+ξ_3^{(0)}) ≥ β/2` (BASE-KERNEL (4.2)). -/
theorem baseMainAction_bond_gain (hb : 0 ≤ cs.beta (0 + 1)) (ha : ∀ n, 0 ≤ cs.aw n)
    (hμ : 0 ≤ cs.muAct (0 + 1)) (haK : 0 < cs.aKer) (hβ : 0 < cs.beta 0)
    (hδ : cs.delta 0 ^ 2 * (cs.aKer * cs.beta 0) = cs.p0 0 ^ 2) (hδ0 : 0 ≤ cs.delta 0)
    (hβ1 : cs.beta 0 / 2 ≤ baseBeta S cs)
    (o : OutT N R (locHist Hl M K (0 + 1) Zc) (0 + 1))
    (x : NewCfg N (locHist Hl M K (0 + 1) Zc) 0) (hv : EuclideanSpace ℝ (Fin N))
    (μ : Fin S.d) (z : Site S.d S.L (g.M1 * (g.c * n (0 + 1))) (0 + 1))
    (hz : z ∈ Xfine g Hl 0 Zc ∧ z ∉ fineK1 g.M1 g.c (n (0 + 1)) S.L 0
      ((Hl.step 0).Omega : Set (Torus S.d (n (0 + 1)))))
    (hz' : z + Pi.single μ 1 ∈ Xfine g Hl 0 Zc ∧ z + Pi.single μ 1 ∉
      fineK1 g.M1 g.c (n (0 + 1)) S.L 0 ((Hl.step 0).Omega : Set (Torus S.d (n (0 + 1)))))
    (hbd : cs.delta 0 ≤
      ‖subVarField N x 0 (torusCast (histScale_eq g.hM Hl.F.hnn (Nat.zero_le 1) hk)
            (z + Pi.single μ 1)) -
          subVarField N x 0 (torusCast (histScale_eq g.hM Hl.F.hnn (Nat.zero_le 1) hk) z)‖) :
    Real.exp (-(baseMainAction g Hl Zc hZc hk cs hrem o x hv / 2)) ≤
      Real.exp (-(cs.p0 0 ^ 2 / (8 * cs.aKer))) := by
  have h := baseMainAction_bond_ge g Hl Zc hZc hk cs hrem hb ha hμ o x hv μ z hz hz'
  exact bond_gain_real haK hβ hδ hδ0 hβ1 h hbd

/-- **Site-witness gain for the base main action** (regime (B)): a site `z ∈ X` with
`ν |φ̂_z - h|² ≥ δ_0²` gives `e^{-𝒜^base_1/2} ≤ e^{-p_0²/(9a)}`, for `μ = ν_1 L^{-2} ≥ (8/9) ν`
(`μ ≥ ν e^{-ε}`, `e^{-ε} ≥ 8/9`) and `β/2 ≤ β^{(1)}_0`. -/
theorem baseMainAction_site_gain (hb : 0 ≤ cs.beta (0 + 1)) (ha : ∀ n, 0 ≤ cs.aw n)
    (hμ : 0 ≤ cs.muAct (0 + 1)) (haK : 0 < cs.aKer) (hβ : 0 < cs.beta 0) (hν : 0 < cs.nu 0)
    (hδ : cs.delta 0 ^ 2 * (cs.aKer * cs.beta 0) = cs.p0 0 ^ 2)
    (hβ1 : cs.beta 0 / 2 ≤ baseBeta S cs) (hμν : 8 / 9 * cs.nu 0 ≤ cs.muAct (0 + 1))
    (o : OutT N R (locHist Hl M K (0 + 1) Zc) (0 + 1))
    (x : NewCfg N (locHist Hl M K (0 + 1) Zc) 0) (hv : EuclideanSpace ℝ (Fin N))
    (z : Site S.d S.L (g.M1 * (g.c * n (0 + 1))) (0 + 1)) (hz : z ∈ Xfine g Hl 0 Zc)
    (hs : cs.delta 0 ^ 2 ≤ cs.nu 0 * ‖baseFieldHat g Hl Zc hZc hk cs o x hv z - hv‖ ^ 2) :
    Real.exp (-(baseMainAction g Hl Zc hZc hk cs hrem o x hv / 2)) ≤
      Real.exp (-(cs.p0 0 ^ 2 / (9 * cs.aKer))) := by
  have h := baseMainAction_site_ge g Hl Zc hZc hk cs hrem hb ha hμ o x hv z hz
  exact site_gain_real haK hβ hν hδ hβ1 hμν (by linarith [h]) hs

end Gains

end Balaban.LargeField
