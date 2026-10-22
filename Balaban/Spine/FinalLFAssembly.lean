/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.LastScaleAgree
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The large-field last integral from per-torus activities (A6-4, assembly)

The assembly of `FinalLargeFieldInput` (A6-4, blocker 5, large-field half; P7 (4.11)–(4.14), LFR
Theorem IV.4.1) from per-torus activities of the scale `k + 1`, in the pattern of the small-field
half (`finalSmallFieldInput_of_localForm`): the activities `bT` are an explicit object of the
theorem (a parameter until the gas of the large-field half defines them), and each obligation is a
separate hypothesis about them.

* `observableActivities_actAdd_of_const`: adding a family that does not depend on the source keeps
  the clauses of `ObservableActivities` (every clause reads the source only through increments,
  analyticity and locality hold for constants).
* `finalLargeFieldInput_of_torusForm`: if on every torus of the family
  `∫ ρ = Ξ_box exp(E + Σ_X bT(X; g))` (`hId`), the activities have the per-torus clauses of Root-F's
  form at the rate `κ + log 2` and an amplitude as small as wanted for `β` large (`hTC`), and their
  increments are uniformly close on two tori (`hC`, A2, blocker 7), then `FinalLargeFieldInput`
  holds. The activities of the conclusion are those of the agreement step
  (`observableActivitiesAt_of_twoTorusClose`) plus the constant `E + Σ_X bT(X; 0)` of each torus
  placed on the empty set, which is not a polymer: `FinalLargeFieldInput` has no vacuum term, and
  only the increments of the activities are constrained (`A64-DESIGN.md` §1.5).
-/

@[expose] public section

open MeasureTheory Balaban Balaban.LargeField Balaban.LargeField.Def7 Balaban.LargeField.Def7v2
  Balaban.SmallField Balaban.SmallField.Def6v2 Balaban.RootFSpine.LastScale

namespace Balaban.RootFSpine

section Const

variable {d N L M : ℕ} {κ c₉ δ : ℝ} {J kf : ℕ}
  {p q : (ℓ : ℕ) → ℕ → Finset (Torus d ℓ) → (Torus d ℓ → Fin N → ℂ) → ℂ}

/-- **Adding a family that does not depend on the source** keeps the clauses of
`ObservableActivities`: every clause reads the source through increments only, and constants are
analytic and local. -/
theorem observableActivities_actAdd_of_const
    (hp : ObservableActivities d N L M κ c₉ δ J kf p)
    (hq : ∀ ℓ j X g, q ℓ j X g = q ℓ j X 0) :
    ObservableActivities d N L M κ c₉ δ J kf (actAdd p q) := by
  have hinc : ∀ ℓ j X g, actAdd p q ℓ j X g - actAdd p q ℓ j X 0 = p ℓ j X g - p ℓ j X 0 := by
    intro ℓ j X g
    simp only [actAdd]
    rw [hq ℓ j X g]
    ring
  refine ⟨fun ℓ _ hℓ => ?_, fun ℓ ℓ' _ _ hℓ hℓ' j a A g ha hbox => ?_⟩
  · obtain ⟨hs, han, hl, hb⟩ := hp.1 ℓ hℓ
    refine ⟨fun j X hX g => ?_, fun j X => ?_, fun j X g g' hgg => ?_, fun j hj X g hg => ?_⟩
    · simp only [actAdd]
      rw [hs j X hX g, hq ℓ j X g]
    · have e : actAdd p q ℓ j X = fun g => p ℓ j X g + q ℓ j X 0 :=
        funext fun g => by simp only [actAdd]; rw [hq ℓ j X g]
      rw [e]
      exact (han j X).add analyticOnNhd_const
    · simp only [actAdd]
      rw [hl j X g g' hgg, hq ℓ j X g, hq ℓ j X g']
    · rw [hinc]
      exact hb j hj X g hg
  · have e := hp.2 ℓ ℓ' hℓ hℓ' j a A g ha hbox
    rw [hinc, hinc]
    exact e

end Const

section Assembly

variable (d N : ℕ) (δ : ℝ) (T : ℝ → ℝ → Typing) (P6 : ℝ → ℝ → Def6.Consts)
  (C7 : ℝ → ℝ → Consts7) (PB : ℝ → ℝ → BudgetConsts) (cs₀ : ℝ → ℝ → OpConsts)
  (M1 c : ℝ → ℝ → ℕ) (rH ϱ : ℝ → ℝ → ℝ) (cut : ℝ → ℝ → ℝ → ℝ)

/-- The top side of the family: `sides L K nK K = nK`. -/
theorem sides_top (L K nK : ℕ) : sides L K nK K = nK := by
  simp [sides]

/-- **The large-field last integral from per-torus activities** (A6-4, assembly; P7 (4.11)–(4.14),
LFR Theorem IV.4.1). The activities `bT` of the scale `k + 1` on the tori `𝕋_ℓ` of the family are an
explicit object (they are defined by the gas of the large-field half). The hypotheses:

* `hPre`: the prefix (the dimension `d ≥ 3` and the block side `M ≥ 14`);
* `hId`: on every torus of the family and every source of the unit `ℓ¹` ball,
  `∫ ρ dψ_k = Ξ_box · exp(E + Σ_X bT(X; g))`, with a constant `E` of the torus (P7 (4.11));
* `hTC`: for every target `η > 0` and `β` large, the per-torus clauses of Root-F's form
  (`LastScaleTorusClauses`) at the rate `κ + log 2` with an amplitude at most
  `η L^{-(k+1)((d-2)/2+δ)}` (P7 (4.13)–(4.14): the activities are `O(e^{-p₂(β_{k₀})})`);
* `hC` (A2, blocker 7): the uniform two-torus closeness of the increments of `bT` at the rate
  `κ + log 2`, with a rate `λ ≥ κ + log 2` and a margin `t₀` fixed before `β`, and the amplitude
  `a_C e^{κ + log 2} ≤ (c₉/8) L^{-(k+1)((d-2)/2+δ)}`.

The activities of the conclusion are those of `observableActivitiesAt_of_twoTorusClose` (at half
the amplitude `c₉`), plus the constant `E + Σ_X bT(X; 0)` of each torus on the empty set. -/
theorem finalLargeFieldInput_of_torusForm (hPre : PrefixInput d δ T P6 C7 PB cs₀ M1 c ϱ)
    (bT : ∀ (κ c₉ β ν : ℝ) (kf k : ℕ) [NeZero (T κ c₉).L] [NeZero (T κ c₉).M] (R : ℕ → ℝ)
      (geo : ∀ (nK : ℕ) [NeZero nK],
        Geo 𝒮[d, T κ c₉, β, (cs₀ κ c₉).aKer] (sides (T κ c₉).L (kf + 1) nK) R (T κ c₉).M)
      (cs : OpConsts) (P : BudgetConsts)
      (_ : RepFam 𝒮[d, T κ c₉, β, (cs₀ κ c₉).aKer] R (kZero d (T κ c₉).L β ν) (kf + 1)
        (T κ c₉).M N geo cs P k (C7 κ c₉).m₁ (ϱ κ c₉))
      (_ : CorrCoef d) (_ : EuclideanSpace ℝ (Fin N)),
      (ℓ : ℕ) → Finset (Torus d ℓ) → (Torus d ℓ → Fin N → ℂ) → ℂ)
    (hId : ∀ κ : ℝ, 0 < κ → ∀ c₉ : ℝ, 0 < c₉ → ∃ β₀ : ℝ, ∀ β : ℝ, β₀ ≤ β →
      ∀ ν : ℝ, 0 < ν → ν * ((T κ c₉).L : ℝ) ^ 2 ≤ 7 / 8 →
      ∀ h : EuclideanSpace ℝ (Fin N), ‖h‖ = 1 → ∀ kf : ℕ, IsHorizon (T κ c₉).L ν kf →
      ∀ [NeZero (T κ c₉).L] [NeZero (T κ c₉).M],
      ∀ k : ℕ, 1 ≤ k → k ≤ kf →
      ∀ (ρ : 𝒟[d, N, T κ c₉, β, (cs₀ κ c₉).aKer, kf + 1, k]) (νk : ℝ) hM6 hkK R geo cs P F St vc,
        FlatRep d N (T κ c₉) (P6 κ c₉) (C7 κ c₉) (PB κ c₉) (cs₀ κ c₉) (M1 κ c₉) (c κ c₉)
          (rH κ c₉) (ϱ κ c₉) β ν h kf k hM6 hkK R geo cs P F St vc ρ νk →
        7 / 8 < νk * ((T κ c₉).L : ℝ) ^ 2 →
        ∃ E : ℕ → ℂ, ∀ (nK : ℕ) [NeZero nK]
          (g : GIdx 𝒮[d, T κ c₉, β, (cs₀ κ c₉).aKer] (sides (T κ c₉).L (kf + 1) nK) (T κ c₉).M
            (kf + 1) N → ℂ), g ∈ l1Ball _ →
          ∫ ψ, ρ nK ψ g = sfBoxIntegral F hM6 hkK vc h (cut κ c₉ (F.sf.β k)) nK g *
            Complex.exp (E nK + ∑ X, bT κ c₉ β ν kf k R geo cs P F vc h
              ((T κ c₉).M * sides (T κ c₉).L (kf + 1) nK (kf + 1) * (T κ c₉).L ^ (kf + 1)) X
              (fun x i => g (x, i))))
    (hTC : ∀ κ : ℝ, 0 < κ → ∀ c₉ : ℝ, 0 < c₉ → ∀ η : ℝ, 0 < η → ∃ β₀ : ℝ, ∀ β : ℝ, β₀ ≤ β →
      ∀ ν : ℝ, 0 < ν → ν * ((T κ c₉).L : ℝ) ^ 2 ≤ 7 / 8 →
      ∀ h : EuclideanSpace ℝ (Fin N), ‖h‖ = 1 → ∀ kf : ℕ, IsHorizon (T κ c₉).L ν kf →
      ∀ [NeZero (T κ c₉).L] [NeZero (T κ c₉).M],
      ∀ k : ℕ, 1 ≤ k → k ≤ kf →
      ∀ (ρ : 𝒟[d, N, T κ c₉, β, (cs₀ κ c₉).aKer, kf + 1, k]) (νk : ℝ) hM6 hkK R geo cs P F St vc,
        FlatRep d N (T κ c₉) (P6 κ c₉) (C7 κ c₉) (PB κ c₉) (cs₀ κ c₉) (M1 κ c₉) (c κ c₉)
          (rH κ c₉) (ϱ κ c₉) β ν h kf k hM6 hkK R geo cs P F St vc ρ νk →
        7 / 8 < νk * ((T κ c₉).L : ℝ) ^ 2 →
        ∃ B : ℝ, 0 ≤ B ∧
          B ≤ η * ((T κ c₉).L : ℝ) ^ (-(((k + 1 : ℕ) : ℝ) * (((d : ℝ) - 2) / 2 + δ))) ∧
          LastScaleTorusClauses d N (T κ c₉).L (T κ c₉).M kf k (κ + Real.log 2) B
            (bT κ c₉ β ν kf k R geo cs P F vc h))
    (hC : ∀ κ : ℝ, 0 < κ → ∀ c₉ : ℝ, 0 < c₉ → ∃ (lam : ℝ) (t₀ : ℕ), κ + Real.log 2 ≤ lam ∧
      ∃ β₀ : ℝ, ∀ β : ℝ, β₀ ≤ β →
      ∀ ν : ℝ, 0 < ν → ν * ((T κ c₉).L : ℝ) ^ 2 ≤ 7 / 8 →
      ∀ h : EuclideanSpace ℝ (Fin N), ‖h‖ = 1 → ∀ kf : ℕ, IsHorizon (T κ c₉).L ν kf →
      ∀ [NeZero (T κ c₉).L] [NeZero (T κ c₉).M],
      ∀ k : ℕ, 1 ≤ k → k ≤ kf →
      ∀ (ρ : 𝒟[d, N, T κ c₉, β, (cs₀ κ c₉).aKer, kf + 1, k]) (νk : ℝ) hM6 hkK R geo cs P F St vc,
        FlatRep d N (T κ c₉) (P6 κ c₉) (C7 κ c₉) (PB κ c₉) (cs₀ κ c₉) (M1 κ c₉) (c κ c₉)
          (rH κ c₉) (ϱ κ c₉) β ν h kf k hM6 hkK R geo cs P F St vc ρ νk →
        7 / 8 < νk * ((T κ c₉).L : ℝ) ^ 2 →
        ∃ aC : ℝ, 0 ≤ aC ∧ aC * Real.exp (κ + Real.log 2) ≤
            c₉ / 8 * ((T κ c₉).L : ℝ) ^ (-(((k + 1 : ℕ) : ℝ) * (((d : ℝ) - 2) / 2 + δ))) ∧
          LastScaleTwoTorusClose d N (T κ c₉).L (T κ c₉).M kf k (κ + Real.log 2) aC lam t₀
            (bT κ c₉ β ν kf k R geo cs P F vc h)) :
    FinalLargeFieldInput d N δ T P6 C7 PB cs₀ M1 c rH ϱ cut := by
  intro κ hκ c₉ hc₉
  obtain ⟨-, -, -, -, hMc, h14, hM1, -, -, -, -, -, -, -, -, hTy, -⟩ := hPre κ hκ c₉ hc₉
  have hd : 3 ≤ d := hTy.1.three_le_d
  obtain ⟨lam, t₀, hlam, β₀C, hC'⟩ := hC κ hκ c₉ hc₉
  set κ' : ℝ := κ + Real.log 2 with hκ'
  set T₀ : ℝ := 1 + 2 * Real.exp (κ' * (t₀ : ℝ)) with hT₀def
  have hT₀ : 0 < T₀ := by positivity
  obtain ⟨β₀T, hT'⟩ := hTC κ hκ c₉ hc₉ (c₉ / 16 / T₀) (by positivity)
  obtain ⟨β₀I, hI'⟩ := hId κ hκ c₉ hc₉
  refine ⟨max β₀C (max β₀T β₀I), fun β hβ ν hν hνL h hh kf hkf _ _ k hk1 hkkf ρ νk hM6 hkK R geo
    cs P F St vc hF hstop => ?_⟩
  have hβC : β₀C ≤ β := (le_max_left _ _).trans hβ
  have hβT : β₀T ≤ β := (le_max_left _ _).trans ((le_max_right _ _).trans hβ)
  have hβI : β₀I ≤ β := (le_max_right _ _).trans ((le_max_right _ _).trans hβ)
  obtain ⟨aC, haC0, haC, hCl⟩ := hC' β hβC ν hν hνL h hh kf hkf k hk1 hkkf ρ νk hM6 hkK R geo cs P
    F St vc hF hstop
  obtain ⟨B, hB0, hBη, hTl⟩ := hT' β hβT ν hν hνL h hh kf hkf k hk1 hkkf ρ νk hM6 hkK R geo cs P
    F St vc hF hstop
  obtain ⟨E, hE⟩ := hI' β hβI ν hν hνL h hh kf hkf k hk1 hkkf ρ νk hM6 hkK R geo cs P F St vc hF
    hstop
  set Λ : ℝ := ((T κ c₉).L : ℝ) ^ (-(((k + 1 : ℕ) : ℝ) * (((d : ℝ) - 2) / 2 + δ))) with hΛ
  have hLpos : (0 : ℝ) < (T κ c₉).L := by
    have := NeZero.ne (T κ c₉).L
    exact_mod_cast Nat.pos_of_ne_zero this
  have hΛ0 : 0 ≤ Λ := Real.rpow_nonneg hLpos.le _
  have hs4 : 4 ≤ (T κ c₉).M * (T κ c₉).L ^ (k + 1) := by
    have hM14 : 14 ≤ (T κ c₉).M := by
      rw [hMc]
      calc 14 ≤ c κ c₉ := h14
        _ = c κ c₉ * 1 := (mul_one _).symm
        _ ≤ c κ c₉ * M1 κ c₉ := Nat.mul_le_mul_left _ hM1
    have hL1 : 1 ≤ (T κ c₉).L ^ (k + 1) :=
      Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (NeZero.ne (T κ c₉).L))
    calc 4 ≤ (T κ c₉).M := by omega
      _ = (T κ c₉).M * 1 := (mul_one _).symm
      _ ≤ (T κ c₉).M * (T κ c₉).L ^ (k + 1) := Nat.mul_le_mul_left _ hL1
  have hamp : B + aC * Real.exp κ' + 2 * B * Real.exp (κ' * (t₀ : ℝ)) ≤ c₉ / 2 / 2 * Λ := by
    have hBb : T₀ * B ≤ c₉ / 16 * Λ := by
      have := mul_le_mul_of_nonneg_left hBη hT₀.le
      calc T₀ * B ≤ T₀ * (c₉ / 16 / T₀ * Λ) := this
        _ = c₉ / 16 * Λ := by field_simp
    calc B + aC * Real.exp κ' + 2 * B * Real.exp (κ' * (t₀ : ℝ))
        = T₀ * B + aC * Real.exp κ' := by rw [hT₀def]; ring
      _ ≤ c₉ / 16 * Λ + c₉ / 8 * Λ := add_le_add hBb haC
      _ ≤ c₉ / 2 / 2 * Λ := by nlinarith only [hΛ0, hc₉]
  obtain ⟨pp, hpp, hsum⟩ := observableActivitiesAt_of_twoTorusClose (c₉ := c₉ / 2) (δ := δ)
    (by omega : 0 < d) hkkf hs4 hB0 haC0 hκ.le le_rfl hlam hamp
    (bT κ c₉ β ν kf k R geo cs P F vc h) hTl hCl
  -- the constant of each torus, on the empty set
  set s : ℕ := (T κ c₉).M * (T κ c₉).L ^ (kf + 1) with hsdef
  let cst : ℕ → ℂ := fun ℓ => if hℓ : ℓ = 0 then 0 else
    haveI : NeZero ℓ := ⟨hℓ⟩
    E (ℓ / s) + ∑ X : Finset (Torus d ℓ), bT κ c₉ β ν kf k R geo cs P F vc h ℓ X 0
  let q : (ℓ : ℕ) → ℕ → Finset (Torus d ℓ) → (Torus d ℓ → Fin N → ℂ) → ℂ :=
    fun ℓ j X _ => if j = k + 1 ∧ X = ∅ then cst ℓ else 0
  refine ⟨actAdd pp q, ?_, fun nK _ g hg => ?_⟩
  · unfold ObservableActivitiesAt
    rw [actAt_actAdd]
    exact observableActivities_actAdd_of_const hpp fun ℓ j X g => by
      simp only [RootFSpine.actAt, q]
  · set ℓ : ℕ := (T κ c₉).M * sides (T κ c₉).L (kf + 1) nK (kf + 1) * (T κ c₉).L ^ (kf + 1)
      with hℓdef
    have hℓ : ℓ = s * nK := by rw [hℓdef, hsdef, sides_top]; ring
    have hs0 : 0 < s := by
      rw [hsdef]
      exact Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne _))
        (Nat.pos_of_ne_zero (pow_ne_zero _ (NeZero.ne _)))
    have hℓ0 : ℓ ≠ 0 := NeZero.ne ℓ
    have hdiv : s ∣ ℓ := ⟨nK, hℓ⟩
    have hnK : ℓ / s = nK := by rw [hℓ, Nat.mul_div_cancel_left _ hs0]
    have hcst : cst ℓ = E nK + ∑ X : Finset (Torus d ℓ), bT κ c₉ β ν kf k R geo cs P F vc h ℓ X 0 := by
      simp only [cst, hℓ0, ↓reduceDIte, hnK]
    have hq : ∑ X : Finset (Torus d ℓ), q ℓ (k + 1) X (fun x i => g (x, i)) = cst ℓ := by
      simp only [q, true_and]
      rw [Finset.sum_ite_eq' Finset.univ (∅ : Finset (Torus d ℓ)) (fun _ => cst ℓ)]
      simp
    have hp := hsum ℓ hdiv (fun x i => g (x, i))
    rw [hE nK g hg]
    congr 1
    congr 1
    simp only [actAdd]
    rw [Finset.sum_add_distrib, hp, hq, hcst, Finset.sum_sub_distrib]
    ring

end Assembly

end Balaban.RootFSpine
