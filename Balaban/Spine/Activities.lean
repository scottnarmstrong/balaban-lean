/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.RootFInputs
public import Balaban.Correlations.Clauses
public import Balaban.Correlations.KF0RootFPartial
public import Balaban.Inhabited.RootBoundsArith

/-!
# Root-F's terms from activities in observable form

The conversion step (F3) of the assembly of Root-F (LFR Theorem IV.5.3 items 3–7; ARCH (F3)): a
family of scale-`j` activities `p_j(X; g)` satisfying `ObservableActivities` (support on scale-`j`
polymers, analyticity and a bound on the unit `ℓ¹` ball, locality, two-torus agreement) and an
exponential identity
`Z(g)/Z(0) = exp(⟨g, h⟩ + ∑_{j=1}^{kf+1} ∑_X (p_j(X; g) - p_j(X; 0)))` on every admissible torus
give
Root-F's clauses for the terms `T_j(x, X; g)_i = ∫₀¹ ∂_{g_i(x)} p_j(X; t g) dt` (`activityTerm`),
by the device `f(X; g) - f(X; 0) = ∑_{x ∈ X} ⟨g(x), ∫₀¹ ∂_{g(x)} f(X; t g) dt⟩` and the Cauchy
estimate on the half ball (`norm_kf0Deriv_le_two`).  This is the multi-scale form of
`Correlations/KF0RootFPartial.lean` (`kf0Term`), with the same proofs.
-/

@[expose] public section

namespace Balaban.RootFSpine

open Balaban Balaban.Correlations Set

open Classical in
/-- **The terms of Root-F from activities** (LFR Definition IV.5.2, the device of P7 (4.15)):
`T_j(x, X; g)_i = ∫₀¹ ∂_{g_i(x)} p_j(X; t g) dt` when `1 ≤ j ≤ kf + 1`, `x ∈ X` and `X` is a
scale-`j`
polymer (`IsPolymer d ℓ (M L^j) X`); zero otherwise. -/
noncomputable def activityTerm {d N : ℕ} (M L kf : ℕ)
    (p : (ℓ : ℕ) → ℕ → Finset (Torus d ℓ) → (Torus d ℓ → Fin N → ℂ) → ℂ) : RootFFamily d N :=
  fun ℓ j x X g =>
    if _hℓ : NeZero ℓ then
      (if j ∈ Finset.Icc 1 (kf + 1) ∧ x ∈ X ∧ IsPolymer d ℓ (M * L ^ j) X then
        fun i => kf0Deriv (p ℓ j X) g x i else 0)
    else 0

section Terms

variable {d N : ℕ} {M L kf : ℕ}
  {p : (ℓ : ℕ) → ℕ → Finset (Torus d ℓ) → (Torus d ℓ → Fin N → ℂ) → ℂ} {ℓ : ℕ} [NeZero ℓ]

open Classical in
theorem activityTerm_apply (j : ℕ) (x : Torus d ℓ) (X : Finset (Torus d ℓ))
    (g : Torus d ℓ → Fin N → ℂ) :
    activityTerm M L kf p ℓ j x X g =
      if j ∈ Finset.Icc 1 (kf + 1) ∧ x ∈ X ∧ IsPolymer d ℓ (M * L ^ j) X then
        fun i => kf0Deriv (p ℓ j X) g x i else 0 := by
  unfold activityTerm
  split
  · rfl
  · rename_i hne
    exact (hne inferInstance).elim

/-- In the range `1 ≤ j ≤ kf + 1` the term is the Cauchy integral for every `x` and every finite
`X` (it vanishes for `x ∉ X` by locality, and for non-polymers since the activity does). -/
theorem activityTerm_eq (j : ℕ) (hj : j ∈ Finset.Icc 1 (kf + 1))
    (hsupp : ∀ X : Finset (Torus d ℓ), ¬ IsPolymer d ℓ (M * L ^ j) X → ∀ g, p ℓ j X g = 0)
    (hloc : ∀ (X : Finset (Torus d ℓ)) (g g' : Torus d ℓ → Fin N → ℂ),
      (∀ y ∈ X, g y = g' y) → p ℓ j X g = p ℓ j X g')
    (x : Torus d ℓ) (X : Finset (Torus d ℓ)) (g : Torus d ℓ → Fin N → ℂ) (i : Fin N) :
    activityTerm M L kf p ℓ j x X g i = kf0Deriv (p ℓ j X) g x i := by
  rw [activityTerm_apply]
  by_cases hx : x ∈ X
  · by_cases hP : IsPolymer d ℓ (M * L ^ j) X
    · simp [hj, hx, hP]
    · have h0 : p ℓ j X = fun _ => 0 := funext (hsupp X hP)
      have : kf0Deriv (p ℓ j X) g x i = 0 := by
        rw [h0]; simp [kf0Deriv]
      simp [hx, hP, this]
  · have hc : ¬ (j ∈ Finset.Icc 1 (kf + 1) ∧ x ∈ X ∧ IsPolymer d ℓ (M * L ^ j) X) :=
      fun h => hx h.2.1
    rw [ite_eq_right_of_eq_false _ _ (eq_false hc)]
    exact (kf0Deriv_eq_zero (hloc X) g hx i).symm

end Terms

/-! ### The clauses on one admissible torus -/

section Torus

variable {d N L M : ℕ} {β ν κ c₉ δ : ℝ} {h : EuclideanSpace ℝ (Fin N)} {J kf : ℕ}
  {p : (ℓ : ℕ) → ℕ → Finset (Torus d ℓ) → (Torus d ℓ → Fin N → ℂ) → ℂ} {ℓ : ℕ} [NeZero ℓ]

/-- **The five torus clauses of Root-F for `activityTerm`**, from the torus part of
`ObservableActivities` (any top scale `J`) and the exponential identity of
`Z(g)/Z(0)` on the unit `ℓ¹` ball. -/
theorem rootFTorusClauses_activityTerm [NeZero N] (hc₉ : 0 < c₉)
    (hsupp : ∀ j X, ¬ (j ∈ Finset.Icc 1 J ∧ IsPolymer d ℓ (M * L ^ j) X) → ∀ g, p ℓ j X g = 0)
    (hana : ∀ j X, AnalyticOnNhd ℂ (p ℓ j X) {g | ∑ y, ∑ i, ‖g y i‖ < 1})
    (hloc : ∀ j X (g g' : Torus d ℓ → Fin N → ℂ), (∀ y ∈ X, g y = g' y) →
      p ℓ j X g = p ℓ j X g')
    (hbd : ∀ j ∈ Finset.Icc 1 J, ∀ X (g : Torus d ℓ → Fin N → ℂ), ∑ y, ∑ i, ‖g y i‖ < 1 →
      ‖p ℓ j X g‖ ≤ c₉ / 2 * (L : ℝ) ^ (-((j : ℝ) * (((d : ℝ) - 2) / 2 + δ)))
        * Real.exp (-κ * (X.card : ℝ) / ((M : ℝ) * (L : ℝ) ^ j) ^ d))
    (hexp : ∀ g : Torus d ℓ → Fin N → ℂ, ∑ y, ∑ i, ‖g y i‖ < 1 →
      partitionFunction d N ℓ β ν h g / partitionFunction d N ℓ β ν h 0 =
        Complex.exp (∑ x, ∑ i, g x i * (h i : ℂ)
          + ∑ j ∈ Finset.Icc 1 (kf + 1), ∑ X : Finset (Torus d ℓ), (p ℓ j X g - p ℓ j X 0))) :
    RootFTorusClauses d N L M β ν h kf κ c₉ δ (activityTerm M L kf p) ℓ := by
  -- the bound of the activities in the whole range `1 ≤ j ≤ kf + 1`
  set B : ℕ → Finset (Torus d ℓ) → ℝ := fun j X =>
    c₉ / 2 * (L : ℝ) ^ (-((j : ℝ) * (((d : ℝ) - 2) / 2 + δ)))
      * Real.exp (-κ * (X.card : ℝ) / ((M : ℝ) * (L : ℝ) ^ j) ^ d) with hBdef
  have hB0 : ∀ j X, 0 ≤ B j X := by
    intro j X
    have hLpos : 0 ≤ (L : ℝ) ^ (-((j : ℝ) * (((d : ℝ) - 2) / 2 + δ))) :=
      Real.rpow_nonneg (Nat.cast_nonneg _) _
    have := Real.exp_pos (-κ * (X.card : ℝ) / ((M : ℝ) * (L : ℝ) ^ j) ^ d)
    simp only [hBdef]
    positivity
  have hball : ∀ j X, ∀ g ∈ ball1 (Torus d ℓ) (Fin N), ‖p ℓ j X g‖ ≤ B j X := by
    intro j X g hg
    by_cases hj : j ∈ Finset.Icc 1 J
    · exact hbd j hj X g hg
    · rw [hsupp j X (fun h => hj h.1) g, norm_zero]
      exact hB0 j X
  have hsuppP : ∀ j, ∀ X : Finset (Torus d ℓ), ¬ IsPolymer d ℓ (M * L ^ j) X → ∀ g,
      p ℓ j X g = 0 := fun j X hX => hsupp j X fun h => hX h.2
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro j x X hnot
    funext g
    rw [activityTerm_apply, ite_eq_right_of_eq_false _ _ (eq_false hnot)]
    rfl
  · intro j x X g g' hgg
    rw [activityTerm_apply, activityTerm_apply]
    split_ifs
    · funext i
      exact kf0Deriv_congr (hloc j X) hgg x i
    · rfl
  · intro j x X
    by_cases hcnd : j ∈ Finset.Icc 1 (kf + 1) ∧ x ∈ X ∧ IsPolymer d ℓ (M * L ^ j) X
    · have : activityTerm M L kf p ℓ j x X = fun g i => kf0Deriv (p ℓ j X) g x i := by
        funext g
        rw [activityTerm_apply, ite_eq_left_of_eq_true _ _ (eq_true hcnd)]
      rw [this]
      exact AnalyticOnNhd.pi fun i => analyticOnNhd_kf0Deriv (α := Torus d ℓ) (β := Fin N)
        (F := p ℓ j X) (hana j X) (B := B j X) (hball j X) x i
    · have : activityTerm M L kf p ℓ j x X = fun _ => 0 := by
        funext g
        rw [activityTerm_apply, ite_eq_right_of_eq_false _ _ (eq_false hcnd)]
      rw [this]
      exact analyticOnNhd_const
  · intro j hj x X g hg
    rw [activityTerm_apply]
    split_ifs with hcnd
    · calc ‖fun i => kf0Deriv (p ℓ j X) g x i‖ ≤ 2 * B j X := by
            refine (pi_norm_le_iff_of_nonneg (by linarith [hB0 j X])).2 fun i => ?_
            exact Balaban.Inhabited.RootBoundsArith.norm_kf0Deriv_le_two
              (α := Torus d ℓ) (β := Fin N) (F := p ℓ j X) (hana j X) (hball j X) hg x i
        _ = c₉ * (L : ℝ) ^ (-((j : ℝ) * (((d : ℝ) - 2) / 2 + δ)))
            * Real.exp (-κ * (X.card : ℝ) / ((M : ℝ) * (L : ℝ) ^ j) ^ d) := by
            simp only [hBdef]; ring
    · simp only [norm_zero]
      have := hB0 j X
      simp only [hBdef] at this
      nlinarith
  · intro g hg
    refine log_partition_eq_multiscale_of_exp
      (T := fun j x X => activityTerm M L kf p ℓ j x X) ?_ ?_ hg
    · intro j x X
      by_cases hcnd : j ∈ Finset.Icc 1 (kf + 1) ∧ x ∈ X ∧ IsPolymer d ℓ (M * L ^ j) X
      · have : activityTerm M L kf p ℓ j x X = fun g i => kf0Deriv (p ℓ j X) g x i := by
          funext g
          rw [activityTerm_apply, ite_eq_left_of_eq_true _ _ (eq_true hcnd)]
        rw [this]
        exact AnalyticOnNhd.pi fun i => analyticOnNhd_kf0Deriv (α := Torus d ℓ) (β := Fin N)
          (F := p ℓ j X) (hana j X) (B := B j X) (hball j X) x i
      · have : activityTerm M L kf p ℓ j x X = fun _ => 0 := by
          funext g
          rw [activityTerm_apply, ite_eq_right_of_eq_false _ _ (eq_false hcnd)]
        rw [this]
        exact analyticOnNhd_const
    · intro g' hg'
      rw [hexp g' hg']
      congr 2
      refine Finset.sum_congr rfl fun j hj => ?_
      refine Eq.trans ?_ Finset.sum_comm
      refine Finset.sum_congr rfl fun X _ => ?_
      rw [sub_zero_eq_sum_kf0Deriv (α := Torus d ℓ) (β := Fin N) (F := p ℓ j X) (hana j X) hg']
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ => ?_
      rw [activityTerm_eq j hj (hsuppP j) (hloc j) x X g' i]

end Torus

/-! ### Agreement across tori -/

section Agreement

variable {d N L M : ℕ} {J kf : ℕ}
  {p : (ℓ : ℕ) → ℕ → Finset (Torus d ℓ) → (Torus d ℓ → Fin N → ℂ) → ℂ}

/-- **The agreement clause of Root-F for `activityTerm`**, from the support, locality and
agreement of the activities on the admissible tori. -/
theorem rootFAgreement_activityTerm
    (hsupp : ∀ (ℓ : ℕ) [NeZero ℓ], M * L ^ (kf + 1) ∣ ℓ → ∀ j X,
      ¬ (j ∈ Finset.Icc 1 J ∧ IsPolymer d ℓ (M * L ^ j) X) → ∀ g, p ℓ j X g = 0)
    (hloc : ∀ (ℓ : ℕ) [NeZero ℓ], M * L ^ (kf + 1) ∣ ℓ → ∀ j X
      (g g' : Torus d ℓ → Fin N → ℂ), (∀ y ∈ X, g y = g' y) → p ℓ j X g = p ℓ j X g')
    (hagr : ∀ (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ'], M * L ^ (kf + 1) ∣ ℓ → M * L ^ (kf + 1) ∣ ℓ' →
      ∀ (j : ℕ) (a : Fin d → ℤ) (A : Finset (Fin d → ℤ)) (g : (Fin d → ℤ) → Fin N → ℂ),
        a ∈ A → (∀ y ∈ A, ∀ μ, 4 * |y μ| < (ℓ : ℤ) ∧ 4 * |y μ| < (ℓ' : ℤ)) →
        p ℓ j (A.image fun y μ => (y μ : ZMod ℓ))
            (fun z => g fun μ => ZMod.valMinAbs (n := ℓ) (z μ)) =
          p ℓ' j (A.image fun y μ => (y μ : ZMod ℓ'))
            (fun z => g fun μ => ZMod.valMinAbs (n := ℓ') (z μ))) :
    RootFAgreement d N L M kf (activityTerm M L kf p) := by
  intro ℓ ℓ' _ _ hℓ hℓ' j a A g ha hbox
  by_cases hj : j ∈ Finset.Icc 1 (kf + 1)
  · have hsP : ∀ (m : ℕ) [NeZero m], M * L ^ (kf + 1) ∣ m → ∀ X : Finset (Torus d m),
        ¬ IsPolymer d m (M * L ^ j) X → ∀ g, p m j X g = 0 :=
      fun m _ hm X hX => hsupp m hm j X fun h => hX h.2
    funext i
    rw [activityTerm_eq j hj (hsP ℓ hℓ) (hloc ℓ hℓ j), activityTerm_eq j hj (hsP ℓ' hℓ')
      (hloc ℓ' hℓ' j)]
    unfold kf0Deriv
    refine intervalIntegral.integral_congr fun t _ => ?_
    have haℓ : ∀ μ, 4 * |a μ| < (ℓ : ℤ) := fun μ => (hbox a ha μ).1
    have haℓ' : ∀ μ, 4 * |a μ| < (ℓ' : ℤ) := fun μ => (hbox a ha μ).2
    have e1 := fun s : ℂ => shift_eq (N := N) a haℓ g i (t : ℂ) s
    have e2 := fun s : ℂ => shift_eq (N := N) a haℓ' g i (t : ℂ) s
    congr 1
    funext s
    rw [e1 s, e2 s]
    exact hagr ℓ ℓ' hℓ hℓ' j a A (fun y => ((t : ℂ) • g + s • unitSource a i) y) ha hbox
  · rw [activityTerm_apply, activityTerm_apply,
      ite_eq_right_of_eq_false _ _ (eq_false fun h => hj h.1),
      ite_eq_right_of_eq_false _ _ (eq_false fun h => hj h.1)]

end Agreement

/-! ### Root-F's clauses -/

/-- **Root-F's clauses from observable activities** (LFR Theorem IV.5.3 items 2–7): activities with
`ObservableActivities` (top scale `J`) and the exponential identity
`Z(g)/Z(0) = exp(⟨g, h⟩ + ∑_{j=1}^{kf+1} ∑_X (p_j(X; g) - p_j(X; 0)))` on every admissible torus
give the clauses `RootFClauses` for the terms `activityTerm M L kf p`. -/
theorem rootFClauses_of_activities {d N L M : ℕ} [NeZero N] {β ν κ c₉ δ : ℝ}
    {h : EuclideanSpace ℝ (Fin N)} {J kf : ℕ}
    {p : (ℓ : ℕ) → ℕ → Finset (Torus d ℓ) → (Torus d ℓ → Fin N → ℂ) → ℂ} (hc₉ : 0 < c₉)
    (hobs : ObservableActivities d N L M κ c₉ δ J kf p)
    (hexp : ∀ (ℓ : ℕ) [NeZero ℓ], M * L ^ (kf + 1) ∣ ℓ →
      ∀ g : Torus d ℓ → Fin N → ℂ, ∑ y, ∑ i, ‖g y i‖ < 1 →
        partitionFunction d N ℓ β ν h g / partitionFunction d N ℓ β ν h 0 =
          Complex.exp (∑ x, ∑ i, g x i * (h i : ℂ)
            + ∑ j ∈ Finset.Icc 1 (kf + 1), ∑ X : Finset (Torus d ℓ), (p ℓ j X g - p ℓ j X 0))) :
    RootFClauses d N L M β ν h kf κ c₉ δ (activityTerm M L kf p) := by
  obtain ⟨htor, hagr⟩ := hobs
  refine ⟨fun ℓ _ hℓ => ?_, rootFAgreement_activityTerm (J := J)
    (fun ℓ _ hℓ => (htor ℓ hℓ).1) (fun ℓ _ hℓ => (htor ℓ hℓ).2.2.1) hagr⟩
  obtain ⟨hs, ha, hl, hb⟩ := htor ℓ hℓ
  exact rootFTorusClauses_activityTerm hc₉ hs ha hl hb (hexp ℓ hℓ)

end Balaban.RootFSpine
