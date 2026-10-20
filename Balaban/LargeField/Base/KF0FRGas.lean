/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.KF0FRBox
public import Balaban.LargeField.Base.KF0AllGoodGas
public import Balaban.Polymer.Regroup
public import Balaban.Polymer.MayerSupport
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# `KF0FRGas`: the terms of route FR regrouped on the block torus (B)

`notes/phase1/KF0-FR.md` (B). On the torus of side `s m` the block configurations are
`Φ_b = ω|_b` (`toSites`), with the product reference `blockRef (γ ⊗ π_ε)`. The terms are grouped by
their block support (`frKey`: the blocks of the site support), with the grouped weights
`f_X = ∏_{frBox t = X} F_t - 1` (`frFX`). Then:

* `integral_prod_frF_eq_blocks`: `∫ ∏_t F_t dμ = ∫ ∏_X (1 + f_X)` over the block configurations;
* `depOn_frFX`, `measurable_frFX`: `f_X` is measurable and depends on the blocks of `X` only;
* `frFX_eq_zero_of_not_isAnimal`: `f_X = 0` unless `X` is a block box;
* `frFX_dom_prod`: from the product bound of the weights `F_t - 1` (`|∫ ∏_{t∈C}(F_t - 1)| ≤ ∏ b_t`,
  `b_t ≤ b_*`), the grouped weights have an integrable dominating function and the product bound
  `|∫ ∏_{X∈𝒞} f_X| ≤ ∏_{X∈𝒞} 2 H₀ e^{-(κ₀+κ₁)|X|_St}` with `H₀ = (1+d) 3^d s^d b_* e^{(κ₀+κ₁)3^d}`,
  as `blockGen_gas` asks.
-/

@[expose] public section

open MeasureTheory Finset Balaban.Green Balaban.Polymer Balaban.LargeField.KF0Gas

namespace Balaban.LargeField.KF0FR

open SphereChart

noncomputable section

variable {N : ℕ} (h : EuclideanSpace ℝ (Fin N)) {d s m : ℕ} [NeZero s] [NeZero m]

/-- The key of a term: its block support, as a nonempty set of blocks. -/
def frKey (R : ℕ) (t : FRTerm d (s * m)) : NePoly (Torus d m) := ⟨frBox R t, frBox_nonempty R t⟩

/-- The weight `F_t - 1` of a term, on block configurations. -/
def frFB (hh : ‖h‖ = 1) (β ν ε : ℝ) (R : ℕ) (g : Torus d (s * m) → Fin N → ℂ)
    (t : FRTerm d (s * m)) (Φ : ∀ b, BlockSpace d s m (perp h × Bool) b) : ℂ :=
  frF h hh β ν ε R g t (toSites Φ) - 1

/-- The grouped weight of a set of blocks: `∏_{frBox t = X} F_t - 1`. -/
def frFX (hh : ‖h‖ = 1) (β ν ε : ℝ) (R : ℕ) (g : Torus d (s * m) → Fin N → ℂ)
    (X : NePoly (Torus d m)) (Φ : ∀ b, BlockSpace d s m (perp h × Bool) b) : ℂ :=
  keyWeight (frKey R) Finset.univ (frFB h hh β ν ε R g) X Φ

theorem one_add_frFX (hh : ‖h‖ = 1) (β ν ε : ℝ) (R : ℕ) (g : Torus d (s * m) → Fin N → ℂ)
    (X : NePoly (Torus d m)) (Φ : ∀ b, BlockSpace d s m (perp h × Bool) b) :
    1 + frFX h hh β ν ε R g X Φ =
      ∏ t ∈ Finset.univ.filter (fun t => frKey R t = X), frF h hh β ν ε R g t (toSites Φ) := by
  unfold frFX keyWeight keyTerms frFB
  simp only [add_sub_cancel]

/-- **The integral over the sites as an integral over the blocks.** -/
theorem integral_prod_frF_eq_blocks (hh : ‖h‖ = 1) {β ν ε : ℝ} (hε : 0 ≤ ε) (R : ℕ)
    (g : Torus d (s * m) → Fin N → ℂ) :
    ∫ ω, ∏ t, frF h hh β ν ε R g t ω ∂(Measure.pi fun _ => frSiteMeasure h ε) =
      ∫ Φ, ∏ X, (1 + frFX h hh β ν ε R g X Φ)
        ∂(Measure.pi (blockRef (d := d) (s := s) (m' := m) (frSiteMeasure h ε))) := by
  have hprob := isProbabilityMeasure_frSiteMeasure h hε
  rw [← map_toSites_pi (frSiteMeasure h ε)]
  rw [integral_map measurable_toSites.aemeasurable
    (Finset.measurable_prod _ fun t _ => measurable_frF h hh β ν ε R g t).aestronglyMeasurable]
  refine integral_congr_ae (Filter.Eventually.of_forall fun Φ => ?_)
  simp only [one_add_frFX]
  exact (Finset.prod_fiberwise Finset.univ (frKey R) _).symm

/-- **The grouped weights depend on the blocks of their set only.** -/
theorem depOn_frFX (hh : ‖h‖ = 1) (β ν ε : ℝ) (R : ℕ)
    (g : Torus d (s * m) → Fin N → ℂ) (X : NePoly (Torus d m)) :
    DepOn X.1 (frFX h hh β ν ε R g X) := by
  intro Φ Φ' hΦ
  have : ∀ t ∈ Finset.univ.filter (fun t => frKey R t = X),
      frF h hh β ν ε R g t (toSites Φ) = frF h hh β ν ε R g t (toSites Φ') := by
    intro t ht
    have htX : frBox R t = X.1 := by
      have := (Finset.mem_filter.1 ht).2
      rw [← this]; rfl
    refine frF_congr h hh β ν ε R g t fun y hy => ?_
    have hb : blockOf d s m y ∈ X.1 := htX ▸ blockOf_mem_frBox hy
    exact congrFun (hΦ _ hb) ⟨y, rfl⟩
  have e1 := one_add_frFX h hh β ν ε R g X Φ
  have e2 := one_add_frFX h hh β ν ε R g X Φ'
  rw [Finset.prod_congr rfl this, ← e2] at e1
  linear_combination e1

theorem measurable_frFX (hh : ‖h‖ = 1) (β ν ε : ℝ) (R : ℕ) (g : Torus d (s * m) → Fin N → ℂ)
    (X : NePoly (Torus d m)) : Measurable (frFX h hh β ν ε R g X) := by
  unfold frFX keyWeight frFB
  exact (Finset.measurable_prod _ fun t _ => measurable_const.add
    (((measurable_frF h hh β ν ε R g t).comp measurable_toSites).sub_const 1)).sub_const 1

/-- **The grouped weight of a set of blocks which is not a block box vanishes**; in particular
of every non-connected set. -/
theorem frFX_eq_zero_of_not_isAnimal (hh : ‖h‖ = 1) (β ν ε : ℝ) (R : ℕ)
    (g : Torus d (s * m) → Fin N → ℂ) (X : NePoly (Torus d m))
    (hX : ¬ IsAnimal (blockGraph d m) X.1) (Φ : ∀ b, BlockSpace d s m (perp h × Bool) b) :
    frFX h hh β ν ε R g X Φ = 0 := by
  have hempty : Finset.univ.filter (fun t : FRTerm d (s * m) => frKey R t = X) = ∅ := by
    refine Finset.filter_eq_empty_iff.2 fun t _ ht => hX ?_
    rw [← ht]; exact isAnimal_frBox R t
  unfold frFX keyWeight keyTerms
  rw [hempty, Finset.prod_empty, sub_self]

/-! ### The product bound of the grouped weights -/

/-- `(1 + b)^n ≤ 1 + 2 n b` when `n b ≤ 1/2`. -/
theorem one_add_pow_le {b : ℝ} (hb : 0 ≤ b) (n : ℕ) (hn : n * b ≤ 1 / 2) :
    (1 + b) ^ n ≤ 1 + 2 * n * b := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn' : (n : ℝ) * b ≤ 1 / 2 := by push_cast at hn; nlinarith
    have := ih hn'
    rw [pow_succ]
    push_cast at hn ⊢
    nlinarith

/-- The block-level product of weights is the site-level product. -/
theorem integral_prod_frFB_eq (hh : ‖h‖ = 1) {β ν ε : ℝ} (hε : 0 ≤ ε) (R : ℕ)
    (g : Torus d (s * m) → Fin N → ℂ) (C : Finset (FRTerm d (s * m))) :
    ∫ Φ, ∏ t ∈ C, frFB h hh β ν ε R g t Φ
        ∂(Measure.pi (blockRef (d := d) (s := s) (m' := m) (frSiteMeasure h ε))) =
      ∫ ω, ∏ t ∈ C, (frF h hh β ν ε R g t ω - 1) ∂(Measure.pi fun _ => frSiteMeasure h ε) := by
  have hprob := isProbabilityMeasure_frSiteMeasure h hε
  rw [← map_toSites_pi (frSiteMeasure h ε)]
  rw [integral_map measurable_toSites.aemeasurable
    (Finset.measurable_prod _ fun t _ =>
      (measurable_frF h hh β ν ε R g t).sub_const 1).aestronglyMeasurable]
  rfl

theorem integrable_prod_frFB (hh : ‖h‖ = 1) {β ν ε : ℝ} (hε : 0 ≤ ε) (R : ℕ)
    (g : Torus d (s * m) → Fin N → ℂ) (C : Finset (FRTerm d (s * m)))
    (hC : Integrable (fun ω => ∏ t ∈ C, (frF h hh β ν ε R g t ω - 1))
      (Measure.pi fun _ => frSiteMeasure h ε)) :
    Integrable (fun Φ => ∏ t ∈ C, frFB h hh β ν ε R g t Φ)
      (Measure.pi (blockRef (d := d) (s := s) (m' := m) (frSiteMeasure h ε))) := by
  have hprob := isProbabilityMeasure_frSiteMeasure h hε
  rw [← map_toSites_pi (frSiteMeasure h ε)] at hC
  exact (integrable_map_measure hC.aestronglyMeasurable
    measurable_toSites.aemeasurable).1 hC

/-- **The grouped weights for `blockGen_gas`**: integrable dominating function and product
bound, from the product bound of the weights `F_t - 1`. -/
theorem frFX_dom_prod (hh : ‖h‖ = 1) {β ν ε : ℝ} (hε : 0 ≤ ε) {R : ℕ} (hR : 2 * R + 1 < s)
    (g : Torus d (s * m) → Fin N → ℂ) (b : FRTerm d (s * m) → ℝ) {bs κ0 κ1 : ℝ}
    (hb0 : ∀ t, 0 ≤ b t) (hbs : ∀ t, b t ≤ bs) (hκ : 0 ≤ κ0 + κ1)
    (hsite : ∀ C : Finset (FRTerm d (s * m)),
      Integrable (fun ω => ∏ t ∈ C, (frF h hh β ν ε R g t ω - 1))
        (Measure.pi fun _ => frSiteMeasure h ε) ∧
      ‖∫ ω, ∏ t ∈ C, (frF h hh β ν ε R g t ω - 1) ∂(Measure.pi fun _ => frSiteMeasure h ε)‖ ≤
        ∏ t ∈ C, b t)
    (hsmall : ((1 + d) * 3 ^ d * s ^ d : ℝ) * bs ≤ 1 / 2) :
    Integrable (fun Φ => ∏ X, (1 + ‖frFX h hh β ν ε R g X Φ‖))
      (Measure.pi (blockRef (d := d) (s := s) (m' := m) (frSiteMeasure h ε))) ∧
    ∀ 𝒞 : Finset (NePoly (Torus d m)),
      ‖∫ Φ, ∏ X ∈ 𝒞, frFX h hh β ν ε R g X Φ
          ∂(Measure.pi (blockRef (d := d) (s := s) (m' := m) (frSiteMeasure h ε)))‖ ≤
        ∏ X ∈ 𝒞, (mayerRho (fun X : NePoly (Torus d m) => X.1) stSize κ0
          ((1 + d) * 3 ^ d * s ^ d * bs * Real.exp ((κ0 + κ1) * 3 ^ d)) X *
            Real.exp (-κ1 * stSize X.1)) := by
  set μB := Measure.pi (blockRef (d := d) (s := s) (m' := m) (frSiteMeasure h ε))
  have hint : ∀ C ⊆ (Finset.univ : Finset (FRTerm d (s * m))),
      Integrable (fun Φ => ∏ t ∈ C, frFB h hh β ν ε R g t Φ) μB := fun C _ =>
    integrable_prod_frFB h hh hε R g C (hsite C).1
  have hprod : ∀ C ⊆ (Finset.univ : Finset (FRTerm d (s * m))),
      ‖∫ Φ, ∏ t ∈ C, frFB h hh β ν ε R g t Φ ∂μB‖ ≤ ∏ t ∈ C, b t := fun C _ => by
    rw [integral_prod_frFB_eq h hh hε R g C]; exact (hsite C).2
  have hreg := regroup_prod_bound μB (key := frKey R) (U := Finset.univ) (frFB h hh β ν ε R g) b
    hint hprod
  have hbs0 : 0 ≤ bs := (hb0 (Sum.inl 0)).trans (hbs _)
  refine ⟨?_, fun 𝒞 => ?_⟩
  · -- the dominating function
    have hexp : ∀ Φ, ∏ X, (1 + ‖frFX h hh β ν ε R g X Φ‖) =
        ∑ 𝒞 ∈ (Finset.univ : Finset (NePoly (Torus d m))).powerset,
          ‖∏ X ∈ 𝒞, frFX h hh β ν ε R g X Φ‖ := by
      intro Φ
      rw [Finset.prod_one_add]
      exact Finset.sum_congr rfl fun 𝒞 _ => (norm_prod _ _).symm
    simp_rw [hexp]
    exact integrable_finsetSum _ fun 𝒞 _ => (hreg 𝒞).1.norm
  · refine (hreg 𝒞).2.trans (Finset.prod_le_prod₀ (fun X _ => ?_) fun X _ => ?_)
    · have : 1 ≤ ∏ t ∈ keyTerms (frKey R) Finset.univ X, (1 + b t) :=
        Finset.one_le_prod₀ fun t _ => by linarith [hb0 t]
      linarith
    · -- one grouped weight
      by_cases hT : keyTerms (frKey R) (Finset.univ : Finset (FRTerm d (s * m))) X = ∅
      · rw [hT, Finset.prod_empty, sub_self]
        unfold mayerRho; positivity
      · obtain ⟨t, ht⟩ := Finset.nonempty_iff_ne_empty.2 hT
        have hXt : X.1 = frBox R t := by
          have := (Finset.mem_filter.1 ht).2
          rw [← this]; rfl
        have hsubB := frBox_subset_blockBox hR t
        have hst : stSize X.1 ≤ 3 ^ d := by
          unfold stSize
          rw [hXt]
          have h1 := steiner_le (isAnimal_blockBox (blockOf d s m (frBase t))) hsubB
          have h3 := card_blockBox_le (m := m) (blockOf d s m (frBase t))
          have : (steiner (blockGraph d m) (frBox R t) : ℝ) ≤ 3 ^ d := by
            exact_mod_cast h1.trans h3
          exact this
        have hcard : ((keyTerms (frKey R) (Finset.univ : Finset (FRTerm d (s * m))) X).card : ℝ) ≤
            (1 + d) * 3 ^ d * s ^ d := by
          have hsub : keyTerms (frKey R) (Finset.univ : Finset (FRTerm d (s * m))) X ⊆
              Finset.univ.filter fun t : FRTerm d (s * m) => frBox R t = X.1 := by
            intro t' ht'
            have h2 := (Finset.mem_filter.1 ht').2
            refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
            rw [← h2]; rfl
          have h1 := (Finset.card_le_card hsub).trans (card_frBox_eq_le (s := s) R X.1)
          have h2 : X.1.card ≤ 3 ^ d := by
            rw [hXt]; exact (Finset.card_le_card hsubB).trans (card_blockBox_le _)
          have h3 : ((1 + d) * (s ^ d * X.1.card) : ℕ) ≤ (1 + d) * (s ^ d * 3 ^ d) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h2)
          have := h1.trans h3
          have : ((keyTerms (frKey R) (Finset.univ : Finset (FRTerm d (s * m))) X).card : ℝ) ≤
              ((1 + d) * (s ^ d * 3 ^ d) : ℕ) := by exact_mod_cast this
          push_cast at this
          linarith
        set n := (keyTerms (frKey R) (Finset.univ : Finset (FRTerm d (s * m))) X).card
        have hprodb : ∏ t ∈ keyTerms (frKey R) Finset.univ X, (1 + b t) ≤ (1 + bs) ^ n := by
          rw [← Finset.prod_const]
          exact Finset.prod_le_prod₀ (fun t _ => by linarith [hb0 t]) fun t _ => by
            linarith [hbs t]
        have hn : (n : ℝ) * bs ≤ 1 / 2 := by
          calc (n : ℝ) * bs ≤ ((1 + d) * 3 ^ d * s ^ d) * bs :=
                mul_le_mul_of_nonneg_right hcard hbs0
            _ ≤ 1 / 2 := hsmall
        have hpow := one_add_pow_le hbs0 n hn
        have hexp1 : 1 ≤ Real.exp ((κ0 + κ1) * 3 ^ d) * Real.exp (-(κ0 + κ1) * stSize X.1) := by
          rw [← Real.exp_add]
          exact Real.one_le_exp (by nlinarith)
        have hrho : mayerRho (fun X : NePoly (Torus d m) => X.1) stSize κ0
            ((1 + d) * 3 ^ d * s ^ d * bs * Real.exp ((κ0 + κ1) * 3 ^ d)) X *
              Real.exp (-κ1 * stSize X.1) =
            2 * ((1 + d) * 3 ^ d * s ^ d * bs) *
              (Real.exp ((κ0 + κ1) * 3 ^ d) * Real.exp (-(κ0 + κ1) * stSize X.1)) := by
          unfold mayerRho
          rw [show -(κ0 + κ1) * stSize X.1 = -κ0 * stSize X.1 + -κ1 * stSize X.1 by ring,
            Real.exp_add]
          ring
        rw [hrho]
        have h0 : 0 ≤ 2 * ((1 + d) * 3 ^ d * s ^ d * bs) := by positivity
        calc ∏ t ∈ keyTerms (frKey R) Finset.univ X, (1 + b t) - 1 ≤ 2 * n * bs := by linarith
          _ ≤ 2 * ((1 + d) * 3 ^ d * s ^ d * bs) := by nlinarith
          _ ≤ _ := le_mul_of_one_le_right h0 hexp1

end

end Balaban.LargeField.KF0FR
