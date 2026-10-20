/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.KfZeroGoodParts
public import Balaban.LargeField.Base.KF0FRLiftPY
public import Balaban.Analysis.SchwarzIncrement
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The case `k_f = 0` by route FR: the activities at fixed couplings

`notes/phase1/KF0-FR.md`. At fixed `β, ν, h`, the local terms `P_g(Y)` of the polymer expansion
of route FR on the tori of side `M L m` (`frPY`) define activities `blockAct (M L) P` on every
torus. When the product bound of the weights holds on the `ℓ¹` ball of sources of radius `G > 1`
and the numerical conditions of the block gas hold, these activities have the observable form of
Root-F (`kf0FR_observable`):

* the identity `Z(g) = exp(E + ⟨g,h⟩ + ∑_X p(X; g))` on the unit `ℓ¹` ball (`frPE`,
  `blockAct_sum`);
* support, locality (`frPY_congr`), analyticity (`frPE`), two-torus agreement (`frPY_agree`);
* the bound of the increments `2α/G · e^{-κ|X|/(ML)^d}` (Schwarz on the ball of radius `G`,
  `norm_sub_le_of_l1Ball`, with the weighted bound `α` of `frPE`).
-/

@[expose] public section

namespace Balaban.RootFSpine

open Balaban Balaban.Polymer Balaban.Green MeasureTheory Balaban.LargeField.SphereChart
  Balaban.LargeField.KF0FR Balaban.LargeField.KF0Gas Balaban.KF0Lift

open scoped Classical

noncomputable section

variable {d N : ℕ}

/-- The vacuum constants of route FR: the logarithm of the constant of the representation. -/
def frE (β ν ε : ℝ) (R : ℕ) (ℓ : ℕ) : ℂ :=
  if hℓ : ℓ ≠ 0 then
    haveI : NeZero ℓ := ⟨hℓ⟩
    ((Real.log (frConst d ℓ N β ν R * (1 + ε) ^ Fintype.card (Torus d ℓ)) : ℝ) : ℂ)
  else 0

theorem frConst_pos {ℓ : ℕ} [NeZero ℓ] {β ν : ℝ} (hβ : 0 < β) (hν : 0 < ν) (R : ℕ) :
    0 < frConst d ℓ N β ν R := by
  unfold frConst
  have h1 : 0 < |((Real.sqrt β)⁻¹ • kf0CR d ℓ ν R).det ^ (N - 1)| :=
    abs_pos.2 (pow_ne_zero _ (isUnit_det_frS hβ hν R).ne_zero)
  positivity

/-- The activities of route FR. -/
def frAct (h : EuclideanSpace ℝ (Fin N)) (hh : ‖h‖ = 1) (s : ℕ) [NeZero s] (β ν ε : ℝ) (R : ℕ) :
    (ℓ : ℕ) → ℕ → Finset (Torus d ℓ) → (Torus d ℓ → Fin N → ℂ) → ℂ :=
  blockAct s (fun _ _ Y g => frPY h hh β ν ε R g Y)

/-- **The activities of route FR at fixed couplings have the observable form.** -/
theorem kf0FR_observable {L M : ℕ} [NeZero (M * L)] {κ c₉ δ : ℝ} (hd : 1 ≤ d) (hs6 : 6 ≤ M * L)
    {R : ℕ} (hR4 : 4 * R + 3 ≤ M * L) (h : EuclideanSpace ℝ (Fin N)) (hh : ‖h‖ = 1)
    {β ν ε : ℝ} (hβ : 0 < β) (hν : 0 < ν) (hε : 0 < ε)
    (hQ : ∀ (m : ℕ) [NeZero m] (x : Torus d (M * L * m)),
      ∑ y, |frQ d (M * L * m) ν R x y| ≤ 1)
    {G : ℝ} (hG : 1 < G) (b : ∀ (m : ℕ) [NeZero m], FRTerm d (M * L * m) → ℝ) {bs κ0 κ1 : ℝ}
    (hb0 : ∀ (m : ℕ) [NeZero m] t, 0 ≤ b m t) (hbs : ∀ (m : ℕ) [NeZero m] t, b m t ≤ bs)
    (hsite : ∀ (m : ℕ) [NeZero m] (g : Torus d (M * L * m) → Fin N → ℂ),
      ∑ x, ∑ i, ‖g x i‖ < G → ∀ C : Finset (FRTerm d (M * L * m)),
      Integrable (fun ω => ∏ t ∈ C, (frF h hh β ν ε R g t ω - 1))
        (Measure.pi fun _ => frSiteMeasure h ε) ∧
      ‖∫ ω, ∏ t ∈ C, (frF h hh β ν ε R g t ω - 1) ∂(Measure.pi fun _ => frSiteMeasure h ε)‖ ≤
        ∏ t ∈ C, b m t)
    (hsmall : ((1 + d) * 3 ^ d * ((M * L : ℕ) : ℝ) ^ d : ℝ) * bs ≤ 1 / 2)
    (hq : ((2 * d : ℕ) : ℝ) ^ 2 * 2 * Real.exp (-κ0) ≤ 1 / 2)
    (hκ0 : Real.log 4 + 1 ≤ κ0) (hκ : 0 ≤ κ) (hκ1 : κ + κ0 + 1 ≤ κ1 - 3 / 2)
    (hH0K : ((1 + d) * 3 ^ d * ((M * L : ℕ) : ℝ) ^ d * bs * Real.exp ((κ0 + κ1) * 3 ^ d)) *
      (4 * Real.exp (-κ0)) ≤ 1 / 4)
    (hB : 2 * (64 * Real.exp 1 * ((1 + d) * 3 ^ d * ((M * L : ℕ) : ℝ) ^ d * bs *
        Real.exp ((κ0 + κ1) * 3 ^ d)) * Real.exp (-(2 * κ0))) / G ≤
      c₉ / 2 * (L : ℝ) ^ (-((1 : ℝ) * (((d : ℝ) - 2) / 2 + δ))))
    (hc₉ : 0 ≤ c₉) (kf : ℕ) :
    ObservableActivities d N L M κ c₉ δ 1 kf (frAct h hh (M * L) β ν ε R) ∧
    ∀ (ℓ : ℕ) [NeZero ℓ], M * L ^ (kf + 1) ∣ ℓ →
      ∀ g : Torus d ℓ → Fin N → ℂ, ∑ y, ∑ i, ‖g y i‖ < 1 →
        partitionFunction d N ℓ β ν h g =
          Complex.exp (frE (d := d) (N := N) β ν ε R ℓ + ∑ x, ∑ i, g x i * (h i : ℂ) +
            ∑ X, frAct h hh (M * L) β ν ε R ℓ 1 X g) := by
  have hR : 2 * R + 1 < M * L := by omega
  set α : ℝ := 64 * Real.exp 1 * ((1 + d) * 3 ^ d * ((M * L : ℕ) : ℝ) ^ d * bs *
    Real.exp ((κ0 + κ1) * 3 ^ d)) * Real.exp (-(2 * κ0)) with hα
  -- the polymer expansion on each torus
  have hPE : ∀ (m : ℕ) [NeZero m], _ := fun m _ =>
    frPE h hh (s := M * L) (m := m) hβ hν hε hR (hQ m)
      (U := {g : Torus d (M * L * m) → Fin N → ℂ | ∑ x, ∑ i, ‖g x i‖ < G})
      (isOpen_lt (continuous_finsetSum _ fun x _ => continuous_finsetSum _ fun i _ =>
        (continuous_apply i |>.comp (continuous_apply x)).norm) continuous_const)
      (by simp; linarith) (b m) (hb0 m) (hbs m) (fun g hg C => hsite m g hg C)
      (by push_cast at hsmall ⊢; exact hsmall) hq hκ0 hκ hκ1 (by push_cast at hH0K ⊢; exact hH0K)
  have hunit : ∀ (m : ℕ) [NeZero m] (g : Torus d (M * L * m) → Fin N → ℂ),
      ∑ x, ∑ i, ‖g x i‖ < 1 → g ∈ {g : Torus d (M * L * m) → Fin N → ℂ | ∑ x, ∑ i, ‖g x i‖ < G} :=
    fun m _ g hg => lt_trans hg hG
  -- the bound of one local term
  have hone : ∀ (m : ℕ) [NeZero m] (Y : Finset (Torus d m)), IsAnimal (blockGraph d m) Y →
      ∀ g : Torus d (M * L * m) → Fin N → ℂ, ∑ x, ∑ i, ‖g x i‖ < G →
        ‖frPY h hh β ν ε R g Y‖ ≤ α * Real.exp (-κ * (Y.card : ℝ)) := by
    intro m _ Y hY g hg
    obtain ⟨b', hb'⟩ := hY.1
    have h1 := (hPE m).2.1 g hg b'
    have h3 : ‖frPY h hh β ν ε R g Y‖ * Real.exp (κ * stSize Y) ≤
        ∑ Y' ∈ (Finset.univ : Finset (Finset (Torus d m))).filter (fun Y' => b' ∈ Y'),
          ‖frPY h hh β ν ε R g Y'‖ * Real.exp (κ * stSize Y') :=
      Finset.single_le_sum (f := fun Y' : Finset (Torus d m) =>
        ‖frPY h hh β ν ε R g Y'‖ * Real.exp (κ * stSize Y')) (fun _ _ => by positivity)
        (Finset.mem_filter.2 ⟨Finset.mem_univ _, hb'⟩)
    have h2 : ‖frPY h hh β ν ε R g Y‖ * Real.exp (κ * stSize Y) ≤ α := h3.trans h1
    rw [stSize_eq_card hY] at h2
    have : Real.exp (-κ * (Y.card : ℝ)) * Real.exp (κ * (Y.card : ℝ)) = 1 := by
      rw [← Real.exp_add]; simp
    calc ‖frPY h hh β ν ε R g Y‖ = ‖frPY h hh β ν ε R g Y‖ * Real.exp (κ * (Y.card : ℝ)) *
          Real.exp (-κ * (Y.card : ℝ)) := by
          rw [mul_assoc, mul_comm (Real.exp (κ * _)), this, mul_one]
      _ ≤ α * Real.exp (-κ * (Y.card : ℝ)) := mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
  refine ⟨⟨fun ℓ _ hℓ => ?_, ?_⟩, fun ℓ _ hℓ g hg => ?_⟩
  · obtain ⟨m, hm, hℓm⟩ := exists_multiple hℓ
    refine ⟨blockAct_support _ m hℓm, blockAct_analytic _ m hℓm fun Y =>
        ((hPE m).2.2.2 Y).mono fun g hg => hunit m g hg,
      blockAct_local _ m hℓm fun Y g g' hgg => frPY_congr h hh β ν ε R Y hgg,
      blockAct_bound _ m hℓm hc₉ (B := 2 * α / G) (fun Y hY g hg => ?_) hB⟩
    have hsch := Balaban.Analysis.norm_sub_le_of_l1Ball (F := fun g => frPY h hh β ν ε R g Y)
      (B := α * Real.exp (-κ * (Y.card : ℝ))) hG
      (fun g hg => (hPE m).2.2.2 Y g hg) (fun g hg => hone m Y hY g hg) hg
    calc _ ≤ 2 * (α * Real.exp (-κ * (Y.card : ℝ))) / G := hsch
      _ = 2 * α / G * Real.exp (-κ * (Y.card : ℝ)) := by ring
  · exact blockAct_agree _ hs6 hd fun m m2 _ _ A hA hX g =>
      frPY_agree h hh hε.le hR4 hs6 hd A hA hX g
  · obtain ⟨m, hm, rfl⟩ := exists_multiple hℓ
    have hg' := hunit m g hg
    unfold frAct
    rw [(hPE m).1 g hg', blockAct_sum _ m rfl (fun g' Y hY => (hPE m).2.2.1 g' Y hY) g]
    have hpos : 0 < frConst d (M * L * m) N β ν R *
        (1 + ε) ^ Fintype.card (Torus d (M * L * m)) :=
      mul_pos (frConst_pos hβ hν R) (pow_pos (by linarith) _)
    have hE : frE (d := d) (N := N) β ν ε R (M * L * m) =
        ((Real.log (frConst d (M * L * m) N β ν R *
          (1 + ε) ^ Fintype.card (Torus d (M * L * m))) : ℝ) : ℂ) := by
      unfold frE
      rw [dite_eq_left (NeZero.ne _)]
    rw [hE, Complex.exp_add, Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log hpos]

end

end Balaban.RootFSpine
