/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.KF0FRAnalytic
public import Balaban.Polymer.Holomorphic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# `KF0FRPE`: the polymer expansion of route FR (B), (A)

`notes/phase1/KF0-FR.md` (B), (A). Let `U` be an open set of sources on which the weights
`F_t - 1` obey the product bound `|∫ ∏_{t∈C}(F_t - 1)| ≤ ∏_{t∈C} b_t` with `b_t ≤ b_*` and
`(1+d) 3^d s^d b_* ≤ 1/2`. With `H₀ = (1+d) 3^d s^d b_* e^{(κ₀+κ₁)3^d}` and the numerical conditions
of `blockGen_gas`, for every source of `U` (`frPE`):

* `Z(g) = c e^{⟨g,h⟩} exp ∑_Y P_g(Y)`, `P_g` the local terms of the gas of the grouped weights;
* `∑_{Y ∋ b} |P_g(Y)| e^{κ'|Y|_St} ≤ 64 e H₀ e^{-2κ₀}`;
* `P_g(Y) = 0` unless `Y` is connected;
* `g ↦ P_g(Y)` is analytic on `U`.
-/

@[expose] public section

open MeasureTheory Finset Balaban.Green Balaban.Polymer Balaban.LargeField.KF0Gas

namespace Balaban.LargeField.KF0FR

open SphereChart

noncomputable section

variable {N : ℕ} (h : EuclideanSpace ℝ (Fin N)) {d s m : ℕ} [NeZero s] [NeZero m]

/-- The Mayer activities of route FR at the source `g`. -/
def frK (hh : ‖h‖ = 1) (β ν ε : ℝ) (R : ℕ) (g : Torus d (s * m) → Fin N → ℂ) :
    NePoly (Torus d m) → ℂ :=
  mayerGenK (blockRef (d := d) (s := s) (m' := m) (frSiteMeasure h ε))
    (fun X : NePoly (Torus d m) => X.1) (frFX h hh β ν ε R g)

/-- The local terms of route FR at the source `g`. -/
def frPY (hh : ‖h‖ = 1) (β ν ε : ℝ) (R : ℕ) (g : Torus d (s * m) → Fin N → ℂ)
    (Y : Finset (Torus d m)) : ℂ :=
  PY (shareBlock (Subtype.val : NePoly (Torus d m) → Finset (Torus d m))) Subtype.val
    (frK h hh β ν ε R g) Y

/-- **The polymer expansion of route FR.** -/
theorem frPE (hh : ‖h‖ = 1) {β ν ε : ℝ} (hβ : 0 < β) (hν : 0 < ν) (hε : 0 < ε) {R : ℕ}
    (hR : 2 * R + 1 < s) (hQ : ∀ x, ∑ y, |frQ d (s * m) ν R x y| ≤ 1)
    {U : Set (Torus d (s * m) → Fin N → ℂ)} (hU : IsOpen U) (hU0 : 0 ∈ U)
    (b : FRTerm d (s * m) → ℝ) {bs κ0 κ1 κ' : ℝ} (hb0 : ∀ t, 0 ≤ b t) (hbs : ∀ t, b t ≤ bs)
    (hsite : ∀ g ∈ U, ∀ C : Finset (FRTerm d (s * m)),
      Integrable (fun ω => ∏ t ∈ C, (frF h hh β ν ε R g t ω - 1))
        (Measure.pi fun _ => frSiteMeasure h ε) ∧
      ‖∫ ω, ∏ t ∈ C, (frF h hh β ν ε R g t ω - 1) ∂(Measure.pi fun _ => frSiteMeasure h ε)‖ ≤
        ∏ t ∈ C, b t)
    (hsmall : ((1 + d) * 3 ^ d * s ^ d : ℝ) * bs ≤ 1 / 2)
    (hq : ((2 * d : ℕ) : ℝ) ^ 2 * 2 * Real.exp (-κ0) ≤ 1 / 2)
    (hκ0 : Real.log 4 + 1 ≤ κ0) (hκ' : 0 ≤ κ') (hκ : κ' + κ0 + 1 ≤ κ1 - 3 / 2)
    (hH0K : ((1 + d) * 3 ^ d * s ^ d * bs * Real.exp ((κ0 + κ1) * 3 ^ d)) *
      (4 * Real.exp (-κ0)) ≤ 1 / 4) :
    (∀ g ∈ U, partitionFunction d N (s * m) β ν h g =
      ((frConst d (s * m) N β ν R * (1 + ε) ^ Fintype.card (Torus d (s * m)) : ℝ) : ℂ) *
        Complex.exp (∑ x : Torus d (s * m), ∑ i : Fin N, g x i * (h i : ℂ)) *
        Complex.exp (∑ Y : Finset (Torus d m), frPY h hh β ν ε R g Y)) ∧
    (∀ g ∈ U, ∀ b' : Torus d m, ∑ Y ∈ (Finset.univ : Finset (Finset (Torus d m))).filter
        (fun Y => b' ∈ Y), ‖frPY h hh β ν ε R g Y‖ * Real.exp (κ' * stSize Y) ≤
      64 * Real.exp 1 * ((1 + d) * 3 ^ d * s ^ d * bs * Real.exp ((κ0 + κ1) * 3 ^ d)) *
        Real.exp (-(2 * κ0))) ∧
    (∀ (g : Torus d (s * m) → Fin N → ℂ) (Y : Finset (Torus d m)), ¬ IsAnimal (blockGraph d m) Y →
      frPY h hh β ν ε R g Y = 0) ∧
    (∀ Y : Finset (Torus d m), AnalyticOnNhd ℂ (fun g => frPY h hh β ν ε R g Y) U) := by
  have hprob := isProbabilityMeasure_frSiteMeasure h hε.le
  have hbs0 : 0 ≤ bs := (hb0 (Sum.inl 0)).trans (hbs _)
  have hκ01 : 0 ≤ κ0 + κ1 := by
    have : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    linarith
  set H0 := (1 + d) * 3 ^ d * s ^ d * bs * Real.exp ((κ0 + κ1) * 3 ^ d) with hH0def
  have hH0 : 0 ≤ H0 := by positivity
  have hdp : ∀ g ∈ U, _ := fun g hg =>
    frFX_dom_prod h hh hε.le hR g b hb0 hbs hκ01 (hsite g hg) hsmall
  have hgas : ∀ g ∈ U, _ := fun g hg =>
    blockGen_gas (blockRef (d := d) (s := s) (m' := m) (frSiteMeasure h ε)) hq hκ0 hκ' hκ hH0 hH0K
      (frFX h hh β ν ε R g) (depOn_frFX h hh β ν ε R g) (measurable_frFX h hh β ν ε R g)
      (hdp g hg).1 (hdp g hg).2
  refine ⟨fun g hg => ?_, fun g hg b' => (hgas g hg).2.1 b', fun g Y hY => ?_, fun Y => ?_⟩
  · rw [partitionFunction_eq_terms h hh hβ hν hε R hQ g, integral_prod_frF_eq_blocks h hh hε.le R g,
      (hgas g hg).1, (hgas g hg).2.2]
    rfl
  · exact PY_shareBlock_eq_zero_of_not_isAnimal (blockGraph d m) _ (fun Z hZ =>
      mayerGenK_eq_zero_of_not_isAnimal (blockGraph d m) _ (fun X : NePoly (Torus d m) => X.1)
        (frFX h hh β ν ε R g) (fun X hX Φ => frFX_eq_zero_of_not_isAnimal h hh β ν ε R g X hX Φ)
        Z hZ) Y hY
  · obtain ⟨hKb, hKP⟩ := blockGen_kp (blockRef (d := d) (s := s) (m' := m) (frSiteMeasure h ε))
      hq hκ0 hκ' hκ hH0 hH0K (frFX h hh β ν ε R 0) (measurable_frFX h hh β ν ε R 0)
      (hdp 0 hU0).1 (hdp 0 hU0).2
    have hKb' : ∀ (Z : NePoly (Torus d m)) g, g ∈ U → ‖frK h hh β ν ε R g Z‖ ≤
        sizeW (Subtype.val : NePoly (Torus d m) → Finset (Torus d m)) stSize
          (2 * (2 * H0 * (4 * Real.exp (-κ0)) * Real.exp (κ1 * 0)) * 1) (κ1 - 3 / 2) κ' 0 Z :=
      fun Z g hg => (blockGen_kp (blockRef (d := d) (s := s) (m' := m) (frSiteMeasure h ε))
        hq hκ0 hκ' hκ hH0 hH0K (frFX h hh β ν ε R g) (measurable_frFX h hh β ν ε R g)
        (hdp g hg).1 (hdp g hg).2).1 Z
    have hint0 : ∀ C : Finset (FRTerm d (s * m)),
        Integrable (fun ω => ∏ t ∈ C, (frF h hh β ν ε R 0 t ω - 1))
          (Measure.pi fun _ => frSiteMeasure h ε) := fun C => (hsite 0 hU0 C).1
    exact pe_PY_analyticOnNhd (shareBlock (Subtype.val : NePoly (Torus d m) → Finset (Torus d m)))
      (Subtype.val : NePoly (Torus d m) → Finset (Torus d m)) hKP hU
      (fun Z g => frK h hh β ν ε R g Z)
      (fun Z => (analyticOnNhd_frK h hh hε.le R hint0 Z).mono (Set.subset_univ _))
      (fun Z g hg => hKb' Z g hg) Y

/-! ### Locality in the source -/

/-- The site term at `x` depends on the source at `x` only. -/
theorem frF_congr_g (hh : ‖h‖ = 1) (β ν ε : ℝ) (R : ℕ) {g g' : Torus d (s * m) → Fin N → ℂ}
    (t : FRTerm d (s * m)) (hg : g (frBase t) = g' (frBase t)) (ω : Torus d (s * m) → perp h × Bool) :
    frF h hh β ν ε R g t ω = frF h hh β ν ε R g' t ω := by
  rcases t with x | ⟨x, μ⟩
  · show frSite h hh β ν ε R g x ω = frSite h hh β ν ε R g' x ω
    unfold frSite
    simp only [frBase] at hg
    rw [hg]
  · rfl

theorem frFX_congr_g (hh : ‖h‖ = 1) (β ν ε : ℝ) (R : ℕ) {g g' : Torus d (s * m) → Fin N → ℂ}
    (X : NePoly (Torus d m)) (hg : ∀ x, blockOf d s m x ∈ X.1 → g x = g' x)
    (Φ : ∀ b, BlockSpace d s m (perp h × Bool) b) :
    frFX h hh β ν ε R g X Φ = frFX h hh β ν ε R g' X Φ := by
  have e1 := one_add_frFX h hh β ν ε R g X Φ
  have e2 := one_add_frFX h hh β ν ε R g' X Φ
  have : ∏ t ∈ Finset.univ.filter (fun t => frKey R t = X), frF h hh β ν ε R g t (toSites Φ) =
      ∏ t ∈ Finset.univ.filter (fun t => frKey R t = X), frF h hh β ν ε R g' t (toSites Φ) := by
    refine Finset.prod_congr rfl fun t ht => frF_congr_g h hh β ν ε R t (hg _ ?_) _
    have htX : frBox R t = X.1 := by
      have := (Finset.mem_filter.1 ht).2
      rw [← this]; rfl
    rw [← htX]; exact blockOf_mem_frBox (frBase_mem_frSupp R t)
  rw [this, ← e2] at e1
  linear_combination e1

/-- **The local terms depend on the source at the sites of their blocks only.** -/
theorem frPY_congr (hh : ‖h‖ = 1) (β ν ε : ℝ) (R : ℕ) (Y : Finset (Torus d m))
    {g g' : Torus d (s * m) → Fin N → ℂ} (hg : ∀ x, blockOf d s m x ∈ Y → g x = g' x) :
    frPY h hh β ν ε R g Y = frPY h hh β ν ε R g' Y := by
  unfold frPY
  refine PY_congr _ _ Y fun Z hZ => ?_
  unfold frK mayerGenK mayerGenAct polyAct
  refine integral_congr_ae (Filter.Eventually.of_forall fun Φ => ?_)
  refine Finset.sum_congr rfl fun C hC => Finset.prod_congr rfl fun X hX => ?_
  refine frFX_congr_g h hh β ν ε R X (fun x hx => hg x ?_) Φ
  exact hZ (sub_of_mem_Cfam hC hX hx)

end

end Balaban.LargeField.KF0FR
