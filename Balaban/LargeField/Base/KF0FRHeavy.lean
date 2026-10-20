/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.KF0FRHeavyDInt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# `KF0FRHeavy`: the heavy bound (route FR, (H))

`notes/phase1/KF0-FR.md` (H). For a family `C` of terms with multiplicity at most `k` and site
supports of at most `s₁` sites, on the event of a heavy set `H ⊆ W = ∪_{t∈C} S_t`
(`frHeavy_le`):

`∫ 1_{E_H} ∏_{t∈C, S_t∩H≠∅} |F_t - 1| dμ ≤ (8^k e η)^{|H|}`,

when `K₀^{k s₁} ≤ e`. This is the hypothesis `hheavy` of `norm_integral_prod_le_marks`. The proof
expands `∏ (1 + |F_t|)` over the sets `A` of terms touching `H` (`2^{k|H|}` of them), each into the
`2^{|D|}` terms of `KF0FRHeavyD`, each bounded by `lintegral_frDterm_le`.
-/

@[expose] public section

open MeasureTheory Set Matrix Balaban.Green Balaban.Polymer
open scoped ENNReal

namespace Balaban.LargeField.KF0FR

open SphereChart

noncomputable section

variable {N : ℕ} (h : EuclideanSpace ℝ (Fin N))

variable {d ℓ : ℕ} [NeZero ℓ]

/-- The terms of `C` touching `H` are at most `k |H|`. -/
theorem card_touch_le {R k : ℕ} (C : Finset (FRTerm d ℓ))
    (hmult : ∀ x, (C.filter (fun t => x ∈ frSupp R t)).card ≤ k) (H : Finset (Torus d ℓ)) :
    (C.filter (fun t => ¬ Disjoint (frSupp R t) H)).card ≤ k * H.card := by
  have hsub : C.filter (fun t => ¬ Disjoint (frSupp R t) H) ⊆
      H.biUnion (fun x => C.filter (fun t => x ∈ frSupp R t)) := by
    intro t ht
    rw [Finset.mem_filter, Finset.not_disjoint_iff] at ht
    obtain ⟨htC, x, hx1, hx2⟩ := ht
    exact Finset.mem_biUnion.2 ⟨x, hx2, Finset.mem_filter.2 ⟨htC, hx1⟩⟩
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ ∑ x ∈ H, (C.filter (fun t => x ∈ frSupp R t)).card := Finset.card_biUnion_le
    _ ≤ ∑ _x ∈ H, k := Finset.sum_le_sum fun x _ => hmult x
    _ = k * H.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

theorem card_frSiteHull_le {R s₁ : ℕ} (hs₁ : ∀ x : Torus d ℓ, (frSupp R (Sum.inl x)).card ≤ s₁)
    (D : Finset (Torus d ℓ)) : (frSiteHull R D).card ≤ s₁ * D.card := by
  unfold frSiteHull
  calc _ ≤ ∑ x ∈ D, (frSupp R (Sum.inl x)).card := Finset.card_biUnion_le
    _ ≤ ∑ _x ∈ D, s₁ := Finset.sum_le_sum fun x _ => hs₁ x
    _ = s₁ * D.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

theorem natCast_two_pow_mul_ofReal (n : ℕ) (x : ℝ) :
    ((2 ^ n : ℕ) : ℝ≥0∞) * ENNReal.ofReal x = ENNReal.ofReal (2 ^ n * x) := by
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num)]
  simp

/-- **The heavy bound.** -/
theorem frHeavy_le (hh : ‖h‖ = 1) {β ν ε G θ p K₀ Wc η : ℝ}
    (hβ : 0 < β) (hν : 0 < ν) (hε : 0 < ε) (hp : 0 ≤ p) (R : ℕ) (g : Torus d ℓ → Fin N → ℂ)
    (hg : ∀ x, ∑ i, ‖g x i‖ ≤ G) (hQ : ∀ x, ∑ y, |frQ d ℓ ν R x y| ≤ θ)
    (hθ0 : 0 ≤ θ) (hθ : θ ≤ 1 / 4)
    (ha : 2 * G * (Real.sqrt β)⁻¹ * (Real.sqrt ν)⁻¹ ≤ p / 8)
    (hK₀ : Real.exp (2 * G * (Real.sqrt β)⁻¹ * (Real.sqrt ν)⁻¹ * p + θ / 2 * p ^ 2) ≤ K₀)
    (hWc : ∫⁻ v, ENNReal.ofReal (chartWeight h v) ≤ ENNReal.ofReal Wc)
    (hJord : (2 * Real.pi) ^ (-(Module.finrank ℝ (perp h) : ℝ) / 2) * Real.exp (-(β * ν / 128)) *
      (((Real.sqrt β)⁻¹ * ((1 - 2 * d / (2 * d + ν)) * (Real.sqrt (2 * d + ν))⁻¹))⁻¹ ^ (N - 1) *
        Wc) ≤ 1)
    (hη1 : 2 * (2 ^ Module.finrank ℝ (perp h) * Real.exp (-p ^ 2 / 8)) +
      2 * Real.exp (-(β * ν / 2) + 2 * G) * (2 ^ Module.finrank ℝ (perp h) *
        Real.exp (2 * (2 * G * (Real.sqrt β)⁻¹ * (Real.sqrt ν)⁻¹) ^ 2)) ≤ η)
    (hη2 : 2 ^ Module.finrank ℝ (perp h) * Real.exp (-p ^ 2 / 8) +
      ε * (2 ^ Module.finrank ℝ (perp h) *
        Real.exp (2 * (2 * G * (Real.sqrt β)⁻¹ * (Real.sqrt ν)⁻¹) ^ 2)) ≤ η)
    (hη3 : (2 * Real.pi) ^ (-(Module.finrank ℝ (perp h) : ℝ) / 2) *
      Real.exp ((2 * G * (Real.sqrt β)⁻¹ * (Real.sqrt ν)⁻¹) ^ 2) *
        (Real.exp (-(β * ν / 128)) + Real.exp (-(β * ν / 2) + 2 * G)) *
      (((Real.sqrt β)⁻¹ * ((1 - 2 * d / (2 * d + ν)) * (Real.sqrt (2 * d + ν))⁻¹))⁻¹ ^ (N - 1) *
        Wc) ≤ η)
    {k s₁ : ℕ} (C : Finset (FRTerm d ℓ))
    (hmult : ∀ x, (C.filter (fun t => x ∈ frSupp R t)).card ≤ k)
    (hs₁ : ∀ x : Torus d ℓ, (frSupp R (Sum.inl x)).card ≤ s₁)
    (hK : K₀ ^ (k * s₁) ≤ Real.exp 1) (H : Finset (Torus d ℓ)) :
    ∫⁻ ω, Set.indicator {ω | MarkEvent (fun _ => frOrd h p) (C.biUnion (frSupp R)) H ω}
        (fun ω => ∏ t ∈ C.filter (fun t => ¬ Disjoint (frSupp R t) H),
          ‖frF h hh β ν ε R g t ω - 1‖ₑ) ω ∂(Measure.pi fun _ => frSiteMeasure h ε) ≤
      ENNReal.ofReal ((8 ^ k * Real.exp 1 * η) ^ H.card) := by
  set W := C.biUnion (frSupp R) with hW
  set CH := C.filter (fun t => ¬ Disjoint (frSupp R t) H) with hCH
  set a := 2 * G * (Real.sqrt β)⁻¹ * (Real.sqrt ν)⁻¹ with hadef
  have hG : 0 ≤ G := by
    have : (0 : ℝ) ≤ ∑ i, ‖g 0 i‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
    linarith [hg 0]
  have hη0 : 0 ≤ η := le_trans (by positivity) hη2
  have hK1 : 1 ≤ K₀ := le_trans (Real.one_le_exp (by positivity)) hK₀
  -- the integrand, term by term
  set Ind : (Torus d ℓ → perp h × Bool) → ℝ≥0∞ := fun ω =>
    ∏ y, (frEvt h p W H y).indicator 1 (ω y) with hInd
  set gD : Finset (FRTerm d ℓ) → Finset (Torus d ℓ) → (Torus d ℓ → perp h × Bool) → ℝ≥0∞ :=
    fun A D' ω => Ind ω * ENNReal.ofReal
      ((∏ z ∈ D', chartWeight h (frField d ℓ β ν R (frPsi h ω) z)) *
        ∏ y, frSiteFac h ε β ν G a (θ / 2) A.toLeft D' (frSiteHull R A.toLeft) y (ω y)) with hgD
  have hgDm : ∀ A D', Measurable (gD A D') := by
    intro A D'
    refine (Finset.measurable_prod _ fun y _ =>
      (measurable_one.indicator (measurableSet_frEvt h p W H y)).comp (measurable_pi_apply y)).mul
      (ENNReal.measurable_ofReal.comp ((Finset.measurable_prod _ fun z _ =>
        (measurable_chartWeight h).comp ((measurable_pi_apply z).comp
          ((measurable_frField h β ν R).comp (measurable_frPsi h)))).mul
        (Finset.measurable_prod _ fun y _ =>
          (measurable_frSiteFac h ε β ν G a (θ / 2) _ _ _ y).comp (measurable_pi_apply y))))
  have hpt : ∀ ω, Set.indicator {ω | MarkEvent (fun _ => frOrd h p) W H ω}
      (fun ω => ∏ t ∈ CH, ‖frF h hh β ν ε R g t ω - 1‖ₑ) ω ≤
      ∑ A ∈ CH.powerset, ∑ D' ∈ A.toLeft.powerset, gD A D' ω := by
    intro ω
    rw [indicator_markEvent_eq h]
    have h1 : ∏ t ∈ CH, ‖frF h hh β ν ε R g t ω - 1‖ₑ ≤
        ∑ A ∈ CH.powerset, ∏ t ∈ A, ‖frF h hh β ν ε R g t ω‖ₑ := by
      rw [← Finset.prod_one_add]
      refine Finset.prod_le_prod fun t _ => ?_
      calc ‖frF h hh β ν ε R g t ω - 1‖ₑ ≤ ‖frF h hh β ν ε R g t ω‖ₑ + ‖(1 : ℂ)‖ₑ :=
            enorm_sub_le
        _ = 1 + ‖frF h hh β ν ε R g t ω‖ₑ := by rw [enorm_one, add_comm]
    have h2 : ∀ A ∈ CH.powerset, ∏ t ∈ A, ‖frF h hh β ν ε R g t ω‖ₑ ≤
        ∑ D' ∈ A.toLeft.powerset, ENNReal.ofReal
          ((∏ z ∈ D', chartWeight h (frField d ℓ β ν R (frPsi h ω) z)) *
            ∏ y, frSiteFac h ε β ν G a (θ / 2) A.toLeft D' (frSiteHull R A.toLeft) y (ω y)) := by
      intro A _
      rw [← ENNReal.ofReal_sum_of_nonneg (fun D' _ => mul_nonneg
        (Finset.prod_nonneg fun z _ => chartWeight_nonneg h _)
        (Finset.prod_nonneg fun y _ => frSiteFac_nonneg h hε.le β ν G a (θ / 2) _ _ _ y _))]
      have e : ∏ t ∈ A, ‖frF h hh β ν ε R g t ω‖ₑ =
          ENNReal.ofReal (∏ t ∈ A, ‖frF h hh β ν ε R g t ω‖) := by
        rw [ENNReal.ofReal_prod_of_nonneg (fun _ _ => norm_nonneg _)]
        exact Finset.prod_congr rfl fun t _ => (ofReal_norm _).symm
      rw [e]
      exact ENNReal.ofReal_le_ofReal (prod_norm_frF_le_sum h hh hβ hν hε R g hg hQ A ω)
    calc (∏ y, (frEvt h p W H y).indicator 1 (ω y)) *
          ∏ t ∈ CH, ‖frF h hh β ν ε R g t ω - 1‖ₑ
        ≤ Ind ω * ∑ A ∈ CH.powerset, ∑ D' ∈ A.toLeft.powerset, ENNReal.ofReal
          ((∏ z ∈ D', chartWeight h (frField d ℓ β ν R (frPsi h ω) z)) *
            ∏ y, frSiteFac h ε β ν G a (θ / 2) A.toLeft D' (frSiteHull R A.toLeft) y (ω y)) :=
          mul_le_mul' le_rfl (h1.trans (Finset.sum_le_sum h2))
      _ = _ := by simp only [Finset.mul_sum, hgD]
  -- each term
  have hterm : ∀ A ∈ CH.powerset, ∀ D' ∈ A.toLeft.powerset,
      ∫⁻ ω, gD A D' ω ∂(Measure.pi fun _ => frSiteMeasure h ε) ≤
        ENNReal.ofReal (η ^ H.card * 2 ^ A.toLeft.card * K₀ ^ (frSiteHull R A.toLeft).card) := by
    intro A hA D' hD'
    have hAC : A ⊆ C := (Finset.mem_powerset.1 hA).trans (Finset.filter_subset _ _)
    have hDW : frSiteHull R A.toLeft ⊆ W := by
      intro y hy
      obtain ⟨x, hx, hyx⟩ := Finset.mem_biUnion.1 hy
      exact Finset.mem_biUnion.2 ⟨Sum.inl x, hAC (Finset.mem_toLeft.1 hx), hyx⟩
    exact lintegral_frDterm_le h hh hβ hν hε hp hG R hθ0 hθ ha hK₀ hWc hJord hη1 hη2 hη3 W H
      A.toLeft D' (Finset.mem_powerset.1 hD') hDW
  -- the count
  have hcount : ∀ A ∈ CH.powerset, (2 : ℝ) ^ A.toLeft.card *
      (η ^ H.card * 2 ^ A.toLeft.card * K₀ ^ (frSiteHull R A.toLeft).card) ≤
      (4 ^ k * Real.exp 1 * η) ^ H.card := by
    intro A hA
    have hAk : A.toLeft.card ≤ k * H.card :=
      (Finset.card_toLeft_le.trans (Finset.card_le_card (Finset.mem_powerset.1 hA))).trans
        (card_touch_le C hmult H)
    have hWk : (frSiteHull R A.toLeft).card ≤ k * s₁ * H.card := by
      calc _ ≤ s₁ * A.toLeft.card := card_frSiteHull_le hs₁ _
        _ ≤ s₁ * (k * H.card) := Nat.mul_le_mul_left _ hAk
        _ = k * s₁ * H.card := by ring
    have h4 : (2 : ℝ) ^ A.toLeft.card * 2 ^ A.toLeft.card ≤ (4 ^ k) ^ H.card := by
      rw [← mul_pow, ← pow_mul, show (2 : ℝ) * 2 = 4 by norm_num]
      exact pow_le_pow_right₀ (by norm_num) hAk
    have hK' : K₀ ^ (frSiteHull R A.toLeft).card ≤ Real.exp 1 ^ H.card := by
      calc _ ≤ K₀ ^ (k * s₁ * H.card) := pow_le_pow_right₀ hK1 hWk
        _ = (K₀ ^ (k * s₁)) ^ H.card := by rw [pow_mul]
        _ ≤ _ := pow_le_pow_left₀ (pow_nonneg (by linarith) _) hK _
    calc (2 : ℝ) ^ A.toLeft.card * (η ^ H.card * 2 ^ A.toLeft.card *
          K₀ ^ (frSiteHull R A.toLeft).card)
        = η ^ H.card * ((2 : ℝ) ^ A.toLeft.card * 2 ^ A.toLeft.card) *
          K₀ ^ (frSiteHull R A.toLeft).card := by ring
      _ ≤ η ^ H.card * (4 ^ k) ^ H.card * Real.exp 1 ^ H.card := by gcongr
      _ = (4 ^ k * Real.exp 1 * η) ^ H.card := by rw [mul_pow, mul_pow]; ring
  have hCHk : CH.card ≤ k * H.card := card_touch_le C hmult H
  calc _ ≤ ∫⁻ ω, ∑ A ∈ CH.powerset, ∑ D' ∈ A.toLeft.powerset, gD A D' ω
        ∂(Measure.pi fun _ => frSiteMeasure h ε) := lintegral_mono hpt
    _ = ∑ A ∈ CH.powerset, ∑ D' ∈ A.toLeft.powerset,
          ∫⁻ ω, gD A D' ω ∂(Measure.pi fun _ => frSiteMeasure h ε) := by
        rw [lintegral_finsetSum _ fun A _ => Finset.measurable_sum _ fun D' _ => hgDm A D']
        exact Finset.sum_congr rfl fun A _ => lintegral_finsetSum _ fun D' _ => hgDm A D'
    _ ≤ ∑ A ∈ CH.powerset, ∑ _D' ∈ A.toLeft.powerset,
          ENNReal.ofReal (η ^ H.card * 2 ^ A.toLeft.card * K₀ ^ (frSiteHull R A.toLeft).card) :=
        Finset.sum_le_sum fun A hA => Finset.sum_le_sum fun D' hD' => hterm A hA D' hD'
    _ = ∑ A ∈ CH.powerset, ENNReal.ofReal ((2 : ℝ) ^ A.toLeft.card *
          (η ^ H.card * 2 ^ A.toLeft.card * K₀ ^ (frSiteHull R A.toLeft).card)) := by
        refine Finset.sum_congr rfl fun A _ => ?_
        rw [Finset.sum_const, Finset.card_powerset, nsmul_eq_mul]
        exact natCast_two_pow_mul_ofReal _ _
    _ ≤ ∑ _A ∈ CH.powerset, ENNReal.ofReal ((4 ^ k * Real.exp 1 * η) ^ H.card) :=
        Finset.sum_le_sum fun A hA => ENNReal.ofReal_le_ofReal (hcount A hA)
    _ = ENNReal.ofReal ((2 : ℝ) ^ CH.card * (4 ^ k * Real.exp 1 * η) ^ H.card) := by
        rw [Finset.sum_const, Finset.card_powerset, nsmul_eq_mul]
        exact natCast_two_pow_mul_ofReal _ _
    _ ≤ ENNReal.ofReal ((8 ^ k * Real.exp 1 * η) ^ H.card) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have h2 : (2 : ℝ) ^ CH.card ≤ (2 ^ k) ^ H.card := by
          rw [← pow_mul]; exact pow_le_pow_right₀ (by norm_num) hCHk
        calc (2 : ℝ) ^ CH.card * (4 ^ k * Real.exp 1 * η) ^ H.card
            ≤ (2 ^ k) ^ H.card * (4 ^ k * Real.exp 1 * η) ^ H.card := by gcongr
          _ = (8 ^ k * Real.exp 1 * η) ^ H.card := by
              rw [← mul_pow]; congr 1
              rw [show (8 : ℝ) = 2 * 4 by norm_num, mul_pow]; ring

end

end Balaban.LargeField.KF0FR
