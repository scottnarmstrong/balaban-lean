/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Observables.LayerV2Inhabited
public import Balaban.Observables.LayerSums
public import Balaban.SmallField.Def6v2Bridge
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The observable layer of the second version: the sums and the constant configurations

The consumers of the landed observable layer `IsObs` for the second version `IsObs2` (Scheme A:
complete backgrounds at every scale).

**Lemma 2.3** (OBSERVABLES §2.3), for an arbitrary field domain of `IsObs2`:
`IsObs2.mFactor_sub_one_le`, `IsObs2.abs_mFactor_le_two`, `IsObs2.sum_R_le`.  These statements use
the clauses (O1), (2.2) only on the data handed to them; the background mass does not enter, and
the constants are those of the landed `mFactor_sub_one_le`, `sum_R_le`.

**Lemma 3.4 at constant configurations** (OBSERVABLES §3.4; landed `ImprovedConst`).

* `const_pair_mem_xiDomM`, `M_const_diff_le_of_bounds`: the Cauchy/Lipschitz step for a function
  analytic and bounded on `Ξ^c_j` at an **arbitrary** mass `μ` (with `BgHyp`); the weight of the
  field is `m = μ L^{2j}`.  The landed `M_const_diff_le` is the case `μ = bgMass`
  (`M_const_diff_le_of_mass`).
* `IsSFObs2.M_const_diff_le`: the complete mass, where `m = ν_j`: **the Lipschitz bound in
  `(ψ, b)`, `b = ν_j h` the source**: `|M(v', w') - M(v, w)| ≤ 4 B_X Δ / ρ` for
  `|v' - v| ≤ Δ`, `|b' - b| = ν_j |w' - w| ≤ Δ`.  The constant `4 B_X / ρ` does not involve the
  mass.
* `IsSFObs2.M_const_h_lipschitz`: in the field `h` the Lipschitz constant is `4 B_X ν_j / ρ`.
* `IsSFObs2.Mobs_const_bound`: **the replacement of the mass-free branch**
  (`Mobs_const_bound_massFree`): `|M^{(j)}(x; v, w)| ≤ (4 Δ / ρ) A K₀` for `|v - e| ≤ Δ` and
  `|b - ν_j e| = ν_j |w - e| ≤ Δ`.

**The mass-free branch of the landed layer.**  For `β_k ν_k ≤ 1` the landed class has background
mass `0`, its domain contains every constant field `h`, and Liouville gives
`M^{(j)}(x; e, w) = M^{(j)}(x; e, e) = 0` for every complex `w` (`Mobs_const_eq_zero_massFree`).
With complete backgrounds this argument is not available at any scale (`Regime.sfBgMass_pos`), and
its conclusion is replaced by the bound above, in which the field enters through the source
`b = ν_j h`: the dependence on `h` at distance `D` is at most `4 B_X ν_j D / ρ`, which tends to `0`
with the mass at fixed `D`.  No statement of the form `M^{(j)}(x; e, w) = 0` is claimed: on the
pinned instance of the second version it fails (`pinObs_response_ne_zero`).

`isSFObs2_xi_witness`: the hypothesis `IsSFObs2` on the wide domain at the complete mass is
inhabited at every scale.
-/

@[expose] public section

namespace Balaban.Observables

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
open Balaban.SmallField.Def6 Balaban.SmallField.Def6v2 Metric Finset

/-! ### Lemma 2.3 for the second version -/

section Lemma23

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  {P : Consts} {Q : ObsConsts} {Rg : Regime L} {β a : ℕ → ℝ}
  {Dom : FieldDom d L N₁ m₁ k N ϱ} {Tm : Terms d L N₁ m₁ k N ϱ} {Ot : ObsTerms d L N₁ m₁ k N}
  {Gker : ℕ → CTorus d L N₁ m₁ k → CTorus d L N₁ m₁ k → Fld d L N₁ m₁ k N →
    Fld d L N₁ m₁ k N → Matrix (Fin N) (Fin N) ℂ}

/-- **Lemma 2.3 (a) for the second version**: `|m_k(x) - 1| ≤ C β^{-1+ρ₁}`, `C = obsC1 L ρ₀`, from
(O1) and the growth of the running coupling (any field domain). -/
theorem IsObs2.mFactor_sub_one_le (hL : 2 ≤ L) (hP : P.Admissible d L) (hQ : Q.ρ₀ > 0)
    (hc : CoeffBounds d L k P β Rg.ν a) (hO : IsObs2 P Q Rg β a Dom Tm Ot Gker) (hβ0 : 0 < β 0)
    (x : CTorus d L N₁ m₁ k) :
    |mFactor β Ot x - 1| ≤ obsC1 L Q.ρ₀ * (β 0) ^ (-1 + Q.ρ₁) := by
  have hLr : (1 : ℝ) < L := by
    have : (2 : ℝ) ≤ L := by exact_mod_cast hL
    linarith
  have hterm : ∀ j ∈ Icc 1 k, |(Real.sqrt (β (j - 1)))⁻¹ * Ot.μ j x| ≤
      Real.sqrt (Real.exp 1) * (β 0) ^ (-1 + Q.ρ₁) * (L : ℝ) ^ (-((j : ℝ) * Q.ρ₀)) := by
    intro j hj
    have hj1 : 1 ≤ j := (Finset.mem_Icc.1 hj).1
    have hjk : j ≤ k := (Finset.mem_Icc.1 hj).2
    obtain ⟨hpos, hlow⟩ := beta_pos_lower hL hP hc hβ0 (n := j - 1) (by omega)
    have hLp : (1 : ℝ) ≤ (L : ℝ) ^ ((j - 1) * (d - 2)) := one_le_pow₀ hLr.le
    have hlow' : β 0 / Real.exp 1 ≤ β (j - 1) := by
      refine le_trans ?_ hlow
      rw [div_le_div_iff_of_pos_right (Real.exp_pos 1)]
      nlinarith
    have hsq : Real.sqrt (β 0) / Real.sqrt (Real.exp 1) ≤ Real.sqrt (β (j - 1)) := by
      rw [← Real.sqrt_div hβ0.le]
      exact Real.sqrt_le_sqrt hlow'
    have hsq0 : 0 < Real.sqrt (β 0) / Real.sqrt (Real.exp 1) := by
      have := Real.sqrt_pos.2 hβ0
      have := Real.sqrt_pos.2 (Real.exp_pos 1)
      positivity
    have hinv : (Real.sqrt (β (j - 1)))⁻¹ ≤ Real.sqrt (Real.exp 1) / Real.sqrt (β 0) := by
      calc (Real.sqrt (β (j - 1)))⁻¹ ≤ (Real.sqrt (β 0) / Real.sqrt (Real.exp 1))⁻¹ :=
            inv_anti₀ hsq0 hsq
        _ = _ := by rw [inv_div]
    have hμ := hO.μ_bound j hj1 hjk x
    rw [abs_mul, abs_of_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _))]
    calc (Real.sqrt (β (j - 1)))⁻¹ * |Ot.μ j x|
        ≤ (Real.sqrt (Real.exp 1) / Real.sqrt (β 0)) *
          ((β 0) ^ (-(1 / 2 : ℝ) + Q.ρ₁) * (L : ℝ) ^ (-((j : ℝ) * Q.ρ₀))) := by
          gcongr
      _ = Real.sqrt (Real.exp 1) * (β 0) ^ (-1 + Q.ρ₁) * (L : ℝ) ^ (-((j : ℝ) * Q.ρ₀)) := by
          have h1 : (β 0) ^ (-1 + Q.ρ₁) =
              (β 0) ^ (-(1 / 2 : ℝ)) * (β 0) ^ (-(1 / 2 : ℝ) + Q.ρ₁) := by
            rw [← Real.rpow_add hβ0]; congr 1; ring
          have h2 : (β 0) ^ (-(1 / 2 : ℝ)) = (Real.sqrt (β 0))⁻¹ := by
            rw [Real.sqrt_eq_rpow, Real.rpow_neg hβ0.le]
          rw [h1, h2]
          field_simp
  unfold mFactor
  rw [show 1 - ∑ j ∈ Finset.Icc 1 k, (Real.sqrt (β (j - 1)))⁻¹ * Ot.μ j x - 1 =
      -∑ j ∈ Finset.Icc 1 k, (Real.sqrt (β (j - 1)))⁻¹ * Ot.μ j x by ring, abs_neg]
  calc |∑ j ∈ Finset.Icc 1 k, (Real.sqrt (β (j - 1)))⁻¹ * Ot.μ j x|
      ≤ ∑ j ∈ Finset.Icc 1 k, |(Real.sqrt (β (j - 1)))⁻¹ * Ot.μ j x| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.Icc 1 k, Real.sqrt (Real.exp 1) * (β 0) ^ (-1 + Q.ρ₁) *
          (L : ℝ) ^ (-((j : ℝ) * Q.ρ₀)) := Finset.sum_le_sum hterm
    _ = Real.sqrt (Real.exp 1) * (β 0) ^ (-1 + Q.ρ₁) *
          ∑ j ∈ Finset.Icc 1 k, (L : ℝ) ^ (-((j : ℝ) * Q.ρ₀)) := by rw [Finset.mul_sum]
    _ ≤ Real.sqrt (Real.exp 1) * (β 0) ^ (-1 + Q.ρ₁) *
          ((L : ℝ) ^ (-((1 : ℕ) * Q.ρ₀)) / (1 - (L : ℝ) ^ (-Q.ρ₀))) := by
        gcongr
        exact inner_geom hLr hQ 1 k
    _ = obsC1 L Q.ρ₀ * (β 0) ^ (-1 + Q.ρ₁) := by
        unfold obsC1
        norm_num
        ring

/-- **Lemma 2.3 (a) for the second version, the bound `|m_k| ≤ 2`.** -/
theorem IsObs2.abs_mFactor_le_two (hL : 2 ≤ L) (hP : P.Admissible d L) (hQ : Q.ρ₀ > 0)
    (hc : CoeffBounds d L k P β Rg.ν a) (hO : IsObs2 P Q Rg β a Dom Tm Ot Gker) (hβ0 : 0 < β 0)
    (hsmall : obsC1 L Q.ρ₀ * (β 0) ^ (-1 + Q.ρ₁) ≤ 1) (x : CTorus d L N₁ m₁ k) :
    |mFactor β Ot x| ≤ 2 := by
  have h := hO.mFactor_sub_one_le hL hP hQ hc hβ0 x
  have h1 : |mFactor β Ot x - 1| ≤ 1 := h.trans hsmall
  have := abs_le.1 h1
  rw [abs_le]
  constructor <;> linarith [this.1, this.2]

end Lemma23

section SumR

variable {d L : ℕ} [NeZero L]

/-- **Lemma 2.3 (b) for the second version**: for the observable layer `IsObs2` on any field
domain `Dom` (in particular the wide domain at the complete mass) and data `(Ψ_j, Φ_j)` in the
domain of the level-`j` terms,
`∑_{1 ≤ i ≤ j ≤ k} β_{i-1}^{-1} ∑_{X ∋ x, x'} |R^{ij}(x, x'; X; Ψ_j, Φ_j)|
≤ C β^{-3/2+ρ₁} (1 + |x - x'|)^{-(d-2+ρ₀)} e^{-(δ₀/2) √ν |x - x'|/L²}` when `L^k √ν ≤ L²`.  The
constant `C` is the constant of the landed `sum_R_le` (it depends only on `d, L, ρ₀, δ₀, K₀`); the
mass enters only through the decay factor `e^{-(δ₀/2) √ν |x - x'|/L²} ≤ 1`. -/
theorem IsObs2.sum_R_le (hd : 3 ≤ d) (hL : 2 ≤ L) {Q : ObsConsts} (hQ : Q.Admissible d)
    {K0 : ℝ} (hK0 : 0 ≤ K0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {N₁ m₁ k N : ℕ} [NeZero N₁] {ϱ : ℝ} {P : Consts}
      (_hP : P.Admissible d L) {Rg : Regime L} {β a : ℕ → ℝ}
      {Dom : FieldDom d L N₁ m₁ k N ϱ} {Tm : Terms d L N₁ m₁ k N ϱ}
      {Ot : ObsTerms d L N₁ m₁ k N}
      {Gker : ℕ → CTorus d L N₁ m₁ k → CTorus d L N₁ m₁ k → Fld d L N₁ m₁ k N →
        Fld d L N₁ m₁ k N → Matrix (Fin N) (Fin N) ℂ},
      CoeffBounds d L k P β Rg.ν a → IsObs2 P Q Rg β a Dom Tm Ot Gker → 0 < β 0 →
      (∀ j, 1 ≤ j → j ≤ k → ∀ x x' : CTorus d L N₁ m₁ k,
        ∑ᶠ X ∈ polysAt2 P.m₀ j x x', Real.exp (-P.κ * sizeJ P.m₀ j X) ≤ K0) →
      (L : ℝ) ^ k * Real.sqrt (Rg.ν 0) ≤ (L : ℝ) ^ 2 →
      ∀ (Ψ Φ : ℕ → Fld d L N₁ m₁ k N),
      (∀ j, 1 ≤ j → j ≤ k → ∀ X, IsPolyDom P.m₀ j X → Dom.dom j (Tm.gs j X) (Ψ j) (Φ j)) →
      ∀ x x' : CTorus d L N₁ m₁ k,
      ∑ i ∈ Icc 1 k, ∑ j ∈ Icc i k, (β (i - 1))⁻¹ *
          ∑ᶠ X ∈ polysAt2 P.m₀ j x x', matNorm (Ot.R i j x x' X (Ψ j) (Φ j)) ≤
        C * (β 0) ^ (-(3 / 2 : ℝ) + Q.ρ₁) *
          (1 + torusDist x x') ^ (-(((d : ℝ) - 2) + Q.ρ₀)) *
          Real.exp (-(Q.δ₀ / 2 * Real.sqrt (Rg.ν 0) * torusDist x x' / (L : ℝ) ^ 2)) := by
  have hLr : (1 : ℝ) < L := by
    have : (2 : ℝ) ≤ L := by exact_mod_cast hL
    linarith
  obtain ⟨Cc, hCc, hcore⟩ := core_series (d := d) (L := L) (by omega) hL hQ.ρ₀_pos hQ.δ₀_pos
  refine ⟨Real.exp 1 * K0 * Cc, by positivity, ?_⟩
  intro N₁ m₁ k N _ ϱ P hP Rg β a Dom Tm Ot Gker hc hO hβ0 hK hk Ψ Φ hdom x x'
  set z1 := torusL1 x x' with hz1
  set zd := torusDist x x' with hzd
  have hz1nn : 0 ≤ z1 := torusL1_nonneg x x'
  have hzdnn : 0 ≤ zd := torusDist_nonneg x x'
  have hzle : zd ≤ z1 := torusDist_le_torusL1 x x'
  set s := Real.sqrt (Rg.ν 0) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hterm : ∀ i ∈ Icc 1 k, ∀ j ∈ Icc i k, (β (i - 1))⁻¹ *
      ∑ᶠ X ∈ polysAt2 P.m₀ j x x', matNorm (Ot.R i j x x' X (Ψ j) (Φ j)) ≤
      (Real.exp 1 * K0 * (β 0) ^ (-(3 / 2 : ℝ) + Q.ρ₁)) *
        (((L : ℝ) ^ ((i - 1) * (d - 2)))⁻¹ * (L : ℝ) ^ (-((j : ℝ) * Q.ρ₀)) *
          Real.exp (-(Q.δ₀ * ((L : ℝ) ^ i)⁻¹ * z1))) := by
    intro i hi j hj
    have hi1 : 1 ≤ i := (Finset.mem_Icc.1 hi).1
    have hij : i ≤ j := (Finset.mem_Icc.1 hj).1
    have hjk : j ≤ k := (Finset.mem_Icc.1 hj).2
    have hj1 : 1 ≤ j := hi1.trans hij
    set RB : ℝ := (β 0) ^ (-(1 / 2 : ℝ) + Q.ρ₁) * (L : ℝ) ^ (-((j : ℝ) * Q.ρ₀)) *
      Real.exp (-(Q.δ₀ * ((L : ℝ) ^ i)⁻¹ * z1)) with hRB
    have hRB0 : 0 ≤ RB := by
      rw [hRB]
      have : 0 ≤ (β 0) ^ (-(1 / 2 : ℝ) + Q.ρ₁) := Real.rpow_nonneg hβ0.le _
      have : 0 ≤ (L : ℝ) ^ (-((j : ℝ) * Q.ρ₀)) := Real.rpow_nonneg (by linarith) _
      positivity
    have hX : ∑ᶠ X ∈ polysAt2 P.m₀ j x x', matNorm (Ot.R i j x x' X (Ψ j) (Φ j)) ≤ RB * K0 := by
      refine (finsum_mem_le_mul (c := RB)
        (g := fun X => Real.exp (-P.κ * sizeJ P.m₀ j X)) ?_).trans
        (mul_le_mul_of_nonneg_left (hK j hj1 hjk x x') hRB0)
      intro X hXmem
      obtain ⟨hXp, hxX, hx'X⟩ := hXmem
      have := hO.boundR i j hi1 hij hjk x x' X hXp hxX hx'X (Ψ j) (Φ j) (hdom j hj1 hjk X hXp)
      rw [hRB]
      calc matNorm (Ot.R i j x x' X (Ψ j) (Φ j)) ≤ _ := this
        _ = _ := by ring
    obtain ⟨hpos, hlow⟩ := beta_pos_lower hL hP hc hβ0 (n := i - 1) (by omega)
    have hLp : 0 < (L : ℝ) ^ ((i - 1) * (d - 2)) := by positivity
    have hβinv : (β (i - 1))⁻¹ ≤ Real.exp 1 / β 0 * ((L : ℝ) ^ ((i - 1) * (d - 2)))⁻¹ := by
      calc (β (i - 1))⁻¹ ≤ (β 0 * (L : ℝ) ^ ((i - 1) * (d - 2)) / Real.exp 1)⁻¹ :=
            inv_anti₀ (by positivity) hlow
        _ = _ := by field_simp
    have hsum0 : 0 ≤ ∑ᶠ X ∈ polysAt2 P.m₀ j x x', matNorm (Ot.R i j x x' X (Ψ j) (Φ j)) := by
      rw [finsum_mem_eq_finite_toFinset_sum _ (Set.toFinite _)]
      exact Finset.sum_nonneg fun X _ => norm_nonneg _
    have hpow : (β 0) ^ (-(3 / 2 : ℝ) + Q.ρ₁) = (β 0)⁻¹ * (β 0) ^ (-(1 / 2 : ℝ) + Q.ρ₁) := by
      rw [← Real.rpow_neg_one, ← Real.rpow_add hβ0]; congr 1; ring
    calc (β (i - 1))⁻¹ * ∑ᶠ X ∈ polysAt2 P.m₀ j x x', matNorm (Ot.R i j x x' X (Ψ j) (Φ j))
        ≤ (Real.exp 1 / β 0 * ((L : ℝ) ^ ((i - 1) * (d - 2)))⁻¹) * (RB * K0) :=
          mul_le_mul hβinv hX hsum0 (by positivity)
      _ = _ := by
          rw [hRB, hpow]
          field_simp
  have hcore' := hcore k z1 s hz1nn hs0 hk
  calc _ ≤ ∑ i ∈ Icc 1 k, ∑ j ∈ Icc i k, (Real.exp 1 * K0 * (β 0) ^ (-(3 / 2 : ℝ) + Q.ρ₁)) *
          (((L : ℝ) ^ ((i - 1) * (d - 2)))⁻¹ * (L : ℝ) ^ (-((j : ℝ) * Q.ρ₀)) *
            Real.exp (-(Q.δ₀ * ((L : ℝ) ^ i)⁻¹ * z1))) :=
        Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => hterm i hi j hj
    _ = (Real.exp 1 * K0 * (β 0) ^ (-(3 / 2 : ℝ) + Q.ρ₁)) *
          ∑ i ∈ Icc 1 k, ∑ j ∈ Icc i k, ((L : ℝ) ^ ((i - 1) * (d - 2)))⁻¹ *
            (L : ℝ) ^ (-((j : ℝ) * Q.ρ₀)) * Real.exp (-(Q.δ₀ * ((L : ℝ) ^ i)⁻¹ * z1)) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [Finset.mul_sum]
    _ ≤ (Real.exp 1 * K0 * (β 0) ^ (-(3 / 2 : ℝ) + Q.ρ₁)) *
          (Cc * (1 + z1) ^ (-(((d : ℝ) - 2) + Q.ρ₀)) *
            Real.exp (-(Q.δ₀ / 2 * s * z1 / (L : ℝ) ^ 2))) := by
        gcongr
    _ ≤ (Real.exp 1 * K0 * (β 0) ^ (-(3 / 2 : ℝ) + Q.ρ₁)) *
          (Cc * (1 + zd) ^ (-(((d : ℝ) - 2) + Q.ρ₀)) *
            Real.exp (-(Q.δ₀ / 2 * s * zd / (L : ℝ) ^ 2))) := by
        have hσ : 0 ≤ ((d : ℝ) - 2) + Q.ρ₀ := by
          have : (3 : ℝ) ≤ d := by exact_mod_cast hd
          linarith [hQ.ρ₀_pos]
        have h1 : (1 + z1) ^ (-(((d : ℝ) - 2) + Q.ρ₀)) ≤ (1 + zd) ^ (-(((d : ℝ) - 2) + Q.ρ₀)) :=
          Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by linarith)
        have h2 : Real.exp (-(Q.δ₀ / 2 * s * z1 / (L : ℝ) ^ 2)) ≤
            Real.exp (-(Q.δ₀ / 2 * s * zd / (L : ℝ) ^ 2)) := by
          rw [Real.exp_le_exp, neg_le_neg_iff]
          have : 0 ≤ Q.δ₀ / 2 * s / (L : ℝ) ^ 2 := by have := hQ.δ₀_pos; positivity
          have h3 := mul_le_mul_of_nonneg_left hzle this
          calc Q.δ₀ / 2 * s * zd / (L : ℝ) ^ 2 = Q.δ₀ / 2 * s / (L : ℝ) ^ 2 * zd := by ring
            _ ≤ Q.δ₀ / 2 * s / (L : ℝ) ^ 2 * z1 := h3
            _ = _ := by ring
        have hb : 0 ≤ Real.exp 1 * K0 * (β 0) ^ (-(3 / 2 : ℝ) + Q.ρ₁) := by
          have := Real.rpow_nonneg hβ0.le (-(3 / 2 : ℝ) + Q.ρ₁); positivity
        gcongr
    _ = _ := by ring

end SumR

/-! ### Lemma 3.4 at constant configurations: an arbitrary mass -/

section Const

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ} {j : ℕ} {ρ : ℝ}

/-- **Constant pairs near `e_{i₀}` lie in `Ξ^c_j(𝔹; 1, ε)` at an arbitrary mass `μ`**:
`|v - e_{i₀}| ≤ ρ` coordinatewise and `μ L^{2j} |w - e_{i₀}| ≤ ρ`, for `N ρ < δ²`,
`0 < δ ≤ min (c₀, c₁)`, `(2 K₁ + 2) δ ≤ ε` (the landed `const_pair_mem_xiDom`, in which the mass
is `bgMass`). -/
theorem const_pair_mem_xiDomM {G : GeneratingSet d L (N₁ * L ^ m₁) k ϱ} {a' : ℕ → ℝ} {μ ε : ℝ}
    (H : BgHyp d L k ϱ a' μ) (hΩ : ∀ i, j < i → G.Ω i = ∅) (hjk : j ≤ k) (hρ : 0 < ρ)
    (hrad : ∃ δ : ℝ, 0 < δ ∧ δ ≤ bgC0 d L N ∧ δ ≤ bgC1 d L N ∧
      (2 * bgK1 d L N + 2) * δ ≤ ε ∧ (N : ℝ) * ρ < δ ^ 2)
    (i₀ : Fin N) (v w : Fin N → ℂ)
    (hv : ∀ i, ‖v i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ ρ)
    (hw : ∀ i, μ * ((L : ℝ) ^ j) ^ 2 * ‖w i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ ρ) :
    XiDom G a' μ j ε (constFld v) (constFld w) := by
  obtain ⟨δ, hδ0, hδ1, hδ2, hδ3, hδ4⟩ := hrad
  exact xiDom_of_close H hΩ hjk i₀ hδ0 hδ1 hδ2 hρ hδ4 hδ3 (constFld v) w (fun _ i => hv i)
    (fun _ _ _ => rfl) hw

/-- **The Lipschitz bound at constant pairs for a function analytic and bounded on `Ξ^c_j` at an
arbitrary mass `μ`** (the Cauchy estimate on the complex line through the two pairs; the proof of
the landed `M_const_diff_le`).  Two constant pairs `(v, w)`, `(v', w')` with
`|v - e_{i₀}| ≤ ρ/2`, `m |w - e_{i₀}| ≤ ρ/2` coordinatewise, `m = μ L^{2j}`, at distance
`|v - v'| ≤ Δ`, `m |w - w'| ≤ Δ` satisfy `|F(v', w') - F(v, w)| ≤ 4 B Δ / ρ`.  The constant does not
involve the mass. -/
theorem M_const_diff_le_of_bounds {G : GeneratingSet d L (N₁ * L ^ m₁) k ϱ} {a' : ℕ → ℝ}
    {μ ε : ℝ} (H : BgHyp d L k ϱ a' μ) (hΩ : ∀ i, j < i → G.Ω i = ∅) (hjk : j ≤ k)
    (hρ : 0 < ρ)
    (hrad : ∃ δ : ℝ, 0 < δ ∧ δ ≤ bgC0 d L N ∧ δ ≤ bgC1 d L N ∧
      (2 * bgK1 d L N + 2) * δ ≤ ε ∧ (N : ℝ) * ρ < δ ^ 2)
    (F : Fld d L N₁ m₁ k N → Fld d L N₁ m₁ k N → Fin N → ℂ) {B : ℝ}
    (hF : AnalyticOnNhd ℂ (fun p : Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N => F p.1 p.2)
      {p | XiDom G a' μ j ε p.1 p.2})
    (hB : ∀ Ψ h, XiDom G a' μ j ε Ψ h → vn (F Ψ h) ≤ B)
    (i₀ : Fin N) (v w v' w' : Fin N → ℂ) {Δ : ℝ} (hΔ : 0 < Δ)
    (hv : ∀ i, ‖v i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ ρ / 2)
    (hv' : ∀ i, ‖v' i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ ρ / 2)
    (hw : ∀ i, μ * ((L : ℝ) ^ j) ^ 2 * ‖w i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ ρ / 2)
    (hw' : ∀ i, μ * ((L : ℝ) ^ j) ^ 2 * ‖w' i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ ρ / 2)
    (hdv : ∀ i, ‖v' i - v i‖ ≤ Δ)
    (hdw : ∀ i, μ * ((L : ℝ) ^ j) ^ 2 * ‖w' i - w i‖ ≤ Δ) :
    vn (F (constFld v') (constFld w') - F (constFld v) (constFld w)) ≤ 4 * B * Δ / ρ := by
  set m : ℝ := μ * ((L : ℝ) ^ j) ^ 2 with hm
  have hm0 : 0 ≤ m := by
    have := H.mass
    rw [hm]; positivity
  set r : ℝ := ρ / (2 * Δ) with hr
  have hr0 : 0 < r := by positivity
  have hmem : ∀ t : ℂ, ‖t‖ < r →
      XiDom G a' μ j ε (constFld (v + t • (v' - v))) (constFld (w + t • (w' - w))) := by
    intro t ht
    have htΔ : ‖t‖ * Δ ≤ ρ / 2 := by
      have := mul_le_mul_of_nonneg_right ht.le hΔ.le
      calc ‖t‖ * Δ ≤ r * Δ := this
        _ = ρ / 2 := by rw [hr]; field_simp
    refine const_pair_mem_xiDomM H hΩ hjk hρ hrad i₀ _ _ (fun i => ?_) (fun i => ?_)
    · have e : (v + t • (v' - v)) i - (Pi.single i₀ 1 : Fin N → ℂ) i =
          (v i - (Pi.single i₀ 1 : Fin N → ℂ) i) + t * (v' i - v i) := by
        simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; ring
      rw [e]
      calc ‖(v i - (Pi.single i₀ 1 : Fin N → ℂ) i) + t * (v' i - v i)‖
          ≤ ‖v i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ + ‖t‖ * ‖v' i - v i‖ := by
            refine (norm_add_le _ _).trans ?_; rw [norm_mul]
        _ ≤ ρ / 2 + ‖t‖ * Δ :=
            add_le_add (hv i) (mul_le_mul_of_nonneg_left (hdv i) (norm_nonneg _))
        _ ≤ ρ := by linarith
    · have e : (w + t • (w' - w)) i - (Pi.single i₀ 1 : Fin N → ℂ) i =
          (w i - (Pi.single i₀ 1 : Fin N → ℂ) i) + t * (w' i - w i) := by
        simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; ring
      rw [e]
      calc m * ‖(w i - (Pi.single i₀ 1 : Fin N → ℂ) i) + t * (w' i - w i)‖
          ≤ m * (‖w i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ + ‖t‖ * ‖w' i - w i‖) := by
            refine mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans ?_) hm0
            rw [norm_mul]
        _ = m * ‖w i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ + ‖t‖ * (m * ‖w' i - w i‖) := by ring
        _ ≤ ρ / 2 + ‖t‖ * Δ :=
            add_le_add (hw i) (mul_le_mul_of_nonneg_left (hdw i) (norm_nonneg _))
        _ ≤ ρ := by linarith
  have hBt : ∀ t : ℂ, ‖t‖ < r →
      vn (F (constFld (v + t • (v' - v))) (constFld (w + t • (w' - w)))) ≤ B :=
    fun t ht => hB _ _ (hmem t ht)
  have hdiff : DifferentiableOn ℂ (fun s : ℂ =>
      F (constFld (v + s • (v' - v))) (constFld (w + s • (w' - w)))) (ball 0 r) := by
    intro t ht
    have h1 := hF (constFld (v + t • (v' - v)), constFld (w + t • (w' - w)))
      (hmem t (mem_ball_zero_iff.1 ht))
    have h2 : AnalyticAt ℂ (fun s : ℂ => ((constFld (v + s • (v' - v)) : Fld d L N₁ m₁ k N),
        (constFld (w + s • (w' - w)) : Fld d L N₁ m₁ k N))) t :=
      (analyticAt_constFld_line v (v' - v) t).prod (analyticAt_constFld_line w (w' - w) t)
    exact (AnalyticAt.comp (g := fun p : Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N => F p.1 p.2)
      (f := fun s : ℂ => ((constFld (v + s • (v' - v)) : Fld d L N₁ m₁ k N),
        (constFld (w + s • (w' - w)) : Fld d L N₁ m₁ k N))) h1
      h2).differentiableAt.differentiableWithinAt
  have e1 : v + (1 : ℂ) • (v' - v) = v' := by simp
  have e2 : w + (1 : ℂ) • (w' - w) = w' := by simp
  have e3 : v + (0 : ℂ) • (v' - v) = v := by simp
  have e4 : w + (0 : ℂ) • (w' - w) = w := by simp
  have hp' : XiDom G a' μ j ε (constFld v') (constFld w') :=
    const_pair_mem_xiDomM H hΩ hjk hρ hrad i₀ v' w' (fun i => (hv' i).trans (by linarith))
      (fun i => (hw' i).trans (by linarith))
  have h1 : vn (F (constFld (v + (1 : ℂ) • (v' - v))) (constFld (w + (1 : ℂ) • (w' - w)))) ≤
      B := by
    rw [e1, e2]
    exact hB _ _ hp'
  have key := slice_diff_le_inv_vn hr0 hdiff hBt h1
  simp only [e1, e2, e3, e4] at key
  refine key.trans (le_of_eq ?_)
  rw [hr]; field_simp; ring

end Const

/-! ### Lemma 3.4 at constant configurations: the class at the complete mass -/

section Class

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  {P : Consts} {Q : ObsConsts} {Rg : Regime L} {β a : ℕ → ℝ} {Tm : Terms d L N₁ m₁ k N ϱ}
  {Ot : ObsTerms d L N₁ m₁ k N}
  {Gker : ℕ → CTorus d L N₁ m₁ k → CTorus d L N₁ m₁ k → Fld d L N₁ m₁ k N →
    Fld d L N₁ m₁ k N → Matrix (Fin N) (Fin N) ℂ}
  {ρd : (CTorus d L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) → (CTorus d L N₁ m₁ k → Fin N → ℝ) → ℝ}
  {Ek : ℝ} {j : ℕ} {ρ : ℝ}

/-- The landed `M_const_diff_le` (mass `bgMass`), re-derived from the statement for an arbitrary
mass. -/
theorem M_const_diff_le_of_mass {ν : ℕ → ℝ} (hO : IsObs P Q β ν a Tm Ot Gker)
    (ctx : LiftCtx P β ν a Tm ρd Ek j ρ) {X : Set (CTorus d L N₁ m₁ k)}
    (hX : IsPolyDom P.m₀ j X) {x : CTorus d L N₁ m₁ k} (hx : x ∈ X)
    (i₀ : Fin N) (v w v' w' : Fin N → ℂ) {Δ : ℝ} (hΔ : 0 < Δ)
    (hv : ∀ i, ‖v i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ ρ / 2)
    (hv' : ∀ i, ‖v' i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ ρ / 2)
    (hw : ∀ i, Def6.bgMass L k (β k) (ν k) * ((L : ℝ) ^ j) ^ 2 *
      ‖w i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ ρ / 2)
    (hw' : ∀ i, Def6.bgMass L k (β k) (ν k) * ((L : ℝ) ^ j) ^ 2 *
      ‖w' i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ ρ / 2)
    (hdv : ∀ i, ‖v' i - v i‖ ≤ Δ)
    (hdw : ∀ i, Def6.bgMass L k (β k) (ν k) * ((L : ℝ) ^ j) ^ 2 * ‖w' i - w i‖ ≤ Δ) :
    vn (Ot.M j x X (constFld v') (constFld w') - Ot.M j x X (constFld v) (constFld w)) ≤
      4 * termBound P Q β L j X * Δ / ρ := by
  obtain ⟨δ, hδ0, hδ1, hδ2, hδ3, hδ4⟩ := ctx.radius
  have hN : (0 : ℝ) ≤ N * rotB N := by unfold rotB; positivity
  have hρ0 := ctx.rho_pos
  exact M_const_diff_le_of_bounds ctx.bg (ctx.sf.gs_spec j ctx.j1 ctx.jk X hX).2 ctx.jk hρ0
    ⟨δ, hδ0, hδ1, hδ2, hδ3, by nlinarith⟩ (Ot.M j x X)
    (hO.analyticM j ctx.j1 ctx.jk x X hX hx)
    (fun Ψ h hd => hO.boundM j ctx.j1 ctx.jk x X hX hx Ψ h hd) i₀ v w v' w' hΔ hv hv' hw hw' hdv
    hdw

/-- **The normalization (2.7) at a constant physical unit configuration, second version**:
`M^{(j)}(x; v, v) = 0`. -/
theorem IsObs2.Mobs_const_zero {Dom : FieldDom d L N₁ m₁ k N ϱ}
    (hO : IsObs2 P Q Rg β a Dom Tm Ot Gker) (hj1 : 1 ≤ j) (hjk : j ≤ k)
    (x : CTorus d L N₁ m₁ k) {v : Fin N → ℝ} (hvD : v ∈ Dom.phys) (hv : v ⬝ᵥ v = 1) :
    Mobs P.m₀ Ot j x (constFld (fun i => (v i : ℂ))) (constFld (fun i => (v i : ℂ))) = 0 :=
  hO.normM j hj1 hjk x v hvD hv

/-- **(2.22) from (2.21), second version**: if every term `M(x, X; ψ, h)`, `X ∋ x`, is within
`b X` of its value at the constant physical unit configuration `(v, v)`, then
`|M^{(j)}(x; ψ, h)| ≤ ∑_{X ∋ x} b_X`. -/
theorem IsObs2.improved_second_of_first {Dom : FieldDom d L N₁ m₁ k N ϱ}
    (hO : IsObs2 P Q Rg β a Dom Tm Ot Gker) (hj1 : 1 ≤ j) (hjk : j ≤ k)
    (x : CTorus d L N₁ m₁ k) (Ψ h : Fld d L N₁ m₁ k N) {v : Fin N → ℝ} (hvD : v ∈ Dom.phys)
    (hv : v ⬝ᵥ v = 1) (b : Set (CTorus d L N₁ m₁ k) → ℝ)
    (hfirst : ∀ X ∈ polysAt P.m₀ j x,
      vn (Ot.M j x X Ψ h - Ot.M j x X (constFld (fun i => (v i : ℂ)))
        (constFld (fun i => (v i : ℂ)))) ≤ b X) :
    vn (Mobs P.m₀ Ot j x Ψ h) ≤ ∑ᶠ X ∈ polysAt P.m₀ j x, b X := by
  have hS : (polysAt P.m₀ j x).Finite := Set.toFinite _
  have h0 := hO.Mobs_const_zero hj1 hjk x hvD hv
  have hdiff : Mobs P.m₀ Ot j x Ψ h = ∑ᶠ X ∈ polysAt P.m₀ j x,
      (Ot.M j x X Ψ h - Ot.M j x X (constFld (fun i => (v i : ℂ)))
        (constFld (fun i => (v i : ℂ)))) := by
    have e : ∑ᶠ X ∈ polysAt P.m₀ j x, (Ot.M j x X Ψ h - Ot.M j x X (constFld (fun i => (v i : ℂ)))
        (constFld (fun i => (v i : ℂ)))) =
        Mobs P.m₀ Ot j x Ψ h - Mobs P.m₀ Ot j x (constFld (fun i => (v i : ℂ)))
          (constFld (fun i => (v i : ℂ))) := by
      unfold Mobs
      rw [finsum_mem_eq_finite_toFinset_sum _ hS, finsum_mem_eq_finite_toFinset_sum _ hS,
        finsum_mem_eq_finite_toFinset_sum _ hS, ← Finset.sum_sub_distrib]
    rw [e, h0, sub_zero]
  rw [hdiff]
  refine (vn_finsum_le _ hS _).trans ?_
  rw [finsum_mem_eq_finite_toFinset_sum _ hS, finsum_mem_eq_finite_toFinset_sum _ hS]
  exact Finset.sum_le_sum fun X hX => hfirst X (hS.mem_toFinset.1 hX)

section Complete

variable (hS : IsSFObs2 P Q Rg β a (completeXiDom P Rg a N₁) Tm ρd Ek Ot Gker)
  (hBg : BgHyp d L k ϱ (aIdeal L k (a k)) (Rg.sfBgMass k)) (hj1 : 1 ≤ j) (hjk : j ≤ k)
  (hρ : 0 < ρ)
  (hrad : ∃ δ : ℝ, 0 < δ ∧ δ ≤ bgC0 d L N ∧ δ ≤ bgC1 d L N ∧
    (2 * bgK1 d L N + 2) * δ ≤ P.eps d L j ∧ (N : ℝ) * ρ < δ ^ 2)
include hS hBg hj1 hjk hρ hrad

/-- **The Lipschitz bound of `M^{(j)}` in `(ψ, b)` at constant pairs, complete backgrounds**
(OBSERVABLES §3.4, "Lipschitz bound in `b`"; the port of the landed `M_const_diff_le` to the second
version at every scale).  For the observable layer on the wide domain at the complete mass, two
constant pairs `(v, w)`, `(v', w')` with `|v - e_{i₀}| ≤ ρ/2` and `ν_j |w - e_{i₀}| ≤ ρ/2`
coordinatewise -- the source `b = ν_j w` within `ρ/2` of `ν_j e_{i₀}` -- at distance
`|v - v'| ≤ Δ`, `ν_j |w - w'| = |b - b'| ≤ Δ` satisfy
`|M(x, X; v', w') - M(x, X; v, w)| ≤ 4 B_X Δ / ρ`.  The constant `4 B_X / ρ` is that of the landed
statement and does not depend on the mass. -/
theorem IsSFObs2.M_const_diff_le {X : Set (CTorus d L N₁ m₁ k)} (hX : IsPolyDom P.m₀ j X)
    {x : CTorus d L N₁ m₁ k} (hx : x ∈ X) (i₀ : Fin N) (v w v' w' : Fin N → ℂ) {Δ : ℝ}
    (hΔ : 0 < Δ)
    (hv : ∀ i, ‖v i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ ρ / 2)
    (hv' : ∀ i, ‖v' i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ ρ / 2)
    (hw : ∀ i, nuIdeal L k (Rg.ν k) j * ‖w i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ ρ / 2)
    (hw' : ∀ i, nuIdeal L k (Rg.ν k) j * ‖w' i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ ρ / 2)
    (hdv : ∀ i, ‖v' i - v i‖ ≤ Δ)
    (hdw : ∀ i, nuIdeal L k (Rg.ν k) j * ‖w' i - w i‖ ≤ Δ) :
    vn (Ot.M j x X (constFld v') (constFld w') - Ot.M j x X (constFld v) (constFld w)) ≤
      4 * termBound P Q β L j X * Δ / ρ := by
  have hm : Rg.sfBgMass k * ((L : ℝ) ^ j) ^ 2 = nuIdeal L k (Rg.ν k) j :=
    Rg.sfBgMass_mul_sq hjk
  exact M_const_diff_le_of_bounds hBg (hS.sf.terms.gs_spec j hj1 hjk X hX).2 hjk hρ hrad
    (Ot.M j x X) (hS.obs.analyticM j hj1 hjk x X hX hx)
    (fun Ψ h hd => hS.obs.boundM j hj1 hjk x X hX hx Ψ h hd) i₀ v w v' w' hΔ hv hv'
    (fun i => by rw [hm]; exact hw i) (fun i => by rw [hm]; exact hw' i) hdv
    (fun i => by rw [hm]; exact hdw i)

/-- **The dependence on the field `h` at constant pairs, complete backgrounds**: for a fixed spin
`v` and two constant fields `w, w'` with `ν_j |w - e|, ν_j |w' - e| ≤ ρ/2` at distance
`|w' - w| ≤ D`, `|M(x, X; v, w') - M(x, X; v, w)| ≤ 4 B_X ν_j D / ρ`.  The Lipschitz constant in `h`
is proportional to the mass `ν_j`: this is the form taken, with complete backgrounds, by the
independence of `h` of the mass-free branch of the landed class
(`M_const_indep_h_of_massFree`). -/
theorem IsSFObs2.M_const_h_lipschitz (hν : 0 < Rg.ν k) {X : Set (CTorus d L N₁ m₁ k)}
    (hX : IsPolyDom P.m₀ j X) {x : CTorus d L N₁ m₁ k} (hx : x ∈ X) (i₀ : Fin N)
    (v w w' : Fin N → ℂ) {D : ℝ} (hD : 0 < D)
    (hv : ∀ i, ‖v i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ ρ / 2)
    (hw : ∀ i, nuIdeal L k (Rg.ν k) j * ‖w i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ ρ / 2)
    (hw' : ∀ i, nuIdeal L k (Rg.ν k) j * ‖w' i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ ρ / 2)
    (hdw : ∀ i, ‖w' i - w i‖ ≤ D) :
    vn (Ot.M j x X (constFld v) (constFld w') - Ot.M j x X (constFld v) (constFld w)) ≤
      4 * termBound P Q β L j X * (nuIdeal L k (Rg.ν k) j * D) / ρ := by
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hνj : 0 < nuIdeal L k (Rg.ν k) j := by unfold nuIdeal; positivity
  exact hS.M_const_diff_le hBg hj1 hjk hρ hrad hX hx i₀ v w v w' (mul_pos hνj hD) hv hv hw hw'
    (fun i => by simpa using (mul_pos hνj hD).le)
    (fun i => mul_le_mul_of_nonneg_left (hdw i) hνj.le)

/-- **(2.22) at constant configurations, complete backgrounds: the replacement of the mass-free
branch** (`Mobs_const_bound_massFree`).  For the observable layer of the second version on the
wide domain at the complete mass, a constant spin `v` within `ρ/2` and `Δ` of `e_{i₀}` and a
constant field `h = w` whose source `b = ν_j w` is within `ρ/2` and `Δ` of `ν_j e_{i₀}`,
`|M^{(j)}(x; v, w)| ≤ (4 Δ / ρ) A K₀`, where `A = β^{-1/2+ρ₁} L^{-jρ₀}` and `K₀` bounds the polymer
sum `∑_{X ∋ x} e^{-κ d_j(X)}` (P5 (1.35)).  In the mass-free branch of the landed class the field
`w` was arbitrary (Liouville at zero background mass); here it is controlled through the source.
The constants are those of the landed statement. -/
theorem IsSFObs2.Mobs_const_bound (x : CTorus d L N₁ m₁ k) (i₀ : Fin N) (v w : Fin N → ℂ)
    {Δ K₀ : ℝ} (hΔ : 0 < Δ)
    (hv : ∀ i, ‖v i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ ρ / 2)
    (hw : ∀ i, nuIdeal L k (Rg.ν k) j * ‖w i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ ρ / 2)
    (hdv : ∀ i, ‖v i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ Δ)
    (hdw : ∀ i, nuIdeal L k (Rg.ν k) j * ‖w i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ Δ)
    (hK : ∑ᶠ X ∈ polysAt P.m₀ j x, Real.exp (-P.κ * sizeJ P.m₀ j X) ≤ K₀)
    (hA : 0 ≤ (β 0) ^ (-(1 / 2 : ℝ) + Q.ρ₁) * (L : ℝ) ^ (-((j : ℝ) * Q.ρ₀))) :
    vn (Mobs P.m₀ Ot j x (constFld v) (constFld w)) ≤
      4 * Δ / ρ * ((β 0) ^ (-(1 / 2 : ℝ) + Q.ρ₁) * (L : ℝ) ^ (-((j : ℝ) * Q.ρ₀)) * K₀) := by
  set A : ℝ := (β 0) ^ (-(1 / 2 : ℝ) + Q.ρ₁) * (L : ℝ) ^ (-((j : ℝ) * Q.ρ₀)) with hAdef
  have hSf : (polysAt P.m₀ j x).Finite := Set.toFinite _
  have hv0 : ∀ i, ‖(Pi.single i₀ 1 : Fin N → ℂ) i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ ρ / 2 := by
    intro i; simpa using (by linarith : (0 : ℝ) ≤ ρ / 2)
  have hw0 : ∀ i, nuIdeal L k (Rg.ν k) j *
      ‖(Pi.single i₀ 1 : Fin N → ℂ) i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ ρ / 2 := by
    intro i; simpa using (by linarith : (0 : ℝ) ≤ ρ / 2)
  have hvv : (Pi.single i₀ (1 : ℝ) : Fin N → ℝ) ⬝ᵥ (Pi.single i₀ (1 : ℝ) : Fin N → ℝ) = 1 := by
    simp [dotProduct, Pi.single_apply]
  have e : (fun i => (((Pi.single i₀ (1 : ℝ) : Fin N → ℝ) i : ℝ) : ℂ)) =
      (Pi.single i₀ 1 : Fin N → ℂ) := by
    funext i; by_cases h : i = i₀ <;> simp [h]
  have hfirst : ∀ X ∈ polysAt P.m₀ j x,
      vn (Ot.M j x X (constFld v) (constFld w) - Ot.M j x X
        (constFld (fun i => (((Pi.single i₀ (1 : ℝ) : Fin N → ℝ) i : ℝ) : ℂ)))
        (constFld (fun i => (((Pi.single i₀ (1 : ℝ) : Fin N → ℝ) i : ℝ) : ℂ)))) ≤
        4 * Δ / ρ * (A * Real.exp (-P.κ * sizeJ P.m₀ j X)) := by
    intro X hX
    rw [e]
    have h := hS.M_const_diff_le hBg hj1 hjk hρ hrad hX.1 hX.2 i₀ (Pi.single i₀ 1)
      (Pi.single i₀ 1) v w hΔ hv0 hv hw0 hw hdv hdw
    refine h.trans (le_of_eq ?_)
    unfold termBound; rw [← hAdef]; ring
  have h2 := hS.obs.improved_second_of_first hj1 hjk x (constFld v) (constFld w)
    (v := (Pi.single i₀ (1 : ℝ) : Fin N → ℝ)) (Set.mem_univ _) hvv _ hfirst
  refine h2.trans ?_
  rw [finsum_mem_eq_finite_toFinset_sum _ hSf]
  rw [finsum_mem_eq_finite_toFinset_sum _ hSf] at hK
  calc ∑ X ∈ hSf.toFinset, 4 * Δ / ρ * (A * Real.exp (-P.κ * sizeJ P.m₀ j X))
      = 4 * Δ / ρ * A * ∑ X ∈ hSf.toFinset, Real.exp (-P.κ * sizeJ P.m₀ j X) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun X _ => by ring
    _ ≤ 4 * Δ / ρ * A * K₀ := mul_le_mul_of_nonneg_left hK (by positivity)
    _ = _ := by ring

end Complete

end Class

/-! ### The hypothesis is inhabited -/

/-- **`IsSFObs2` on the wide domain at the complete mass is inhabited at every scale** (`d = L = 3`,
`N = 2`, any `m₁`, `k`, `k₀` -- also below the switch --, `ϱ ≥ R₀(3, 3)`): the member
`isSFFamily2_xi_witness` of the small-field class with its observable layer
`isObs2_xi_witness`, on every torus. -/
theorem isSFObs2_xi_witness (m₁ k k₀ N₁ : ℕ) [NeZero N₁] (ϱ : ℝ) (hϱ : bgR0 3 3 ≤ ϱ) {α₀ : ℝ}
    (hα : 0 < α₀) :
    IsSFObs2 (d := 3) (L := 3) (N₁ := N₁) (m₁ := m₁) (k := k) (N := 2) (ϱ := ϱ)
      (witnessConsts α₀) witQ ⟨k₀, witnessν k⟩ witnessβ witnessa
      (completeXiDom (witnessConsts α₀) ⟨k₀, witnessν k⟩ witnessa N₁)
      (pinTerms 3 3 N₁ m₁ k 2 ϱ (witnessConsts α₀).κ (fun _ => 0))
      (rho2 (witnessConsts α₀) ⟨k₀, witnessν k⟩ witnessβ witnessa
        (pinTerms 3 3 N₁ m₁ k 2 ϱ (witnessConsts α₀).κ (fun _ => 0)) 0) 0
      (pinObs 3 3 N₁ m₁ k 2 (witnessConsts α₀).κ (obsCoef witnessβ (fun _ => 0)))
      (fun _ _ _ _ _ => 0) :=
  ⟨(isSFFamily2_xi_witness m₁ k k₀ ϱ hϱ hα).torus N₁, isObs2_xi_witness m₁ k k₀ N₁ ϱ hα⟩

end Balaban.Observables
