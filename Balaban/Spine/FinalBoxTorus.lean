/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.LastScaleAgree
public import Balaban.LargeField.Def7
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Activities on all the tori of the family

A6-3, gas layer. The per-torus clauses of the last-scale activities (`LastScaleTorusClauses`,
`Spine/LastScaleAgree.lean`) are stated for every admissible side `ℓ` (`M L^{kf+1} ∣ ℓ`); the
activities of the box gas are defined on the tori `𝕋_{M n_K L^K}` of the family, `n_K = sides`.

* `TorusClausesAt`: the four clauses on one torus (the body of `LastScaleTorusClauses`), with
  `torusClausesAt_zero` (rule 10), `torusClausesAt_add` (sum of two families: the amplitudes add,
  the rate is the smaller one), `torusClausesAt_cast` (transport along an equality of sides);
* `torusFam`: the activities on every side `ℓ` from the activities on the tori of the family,
  `ℓ ↦ nK = ℓ / (M L^K)` (`torusFam_apply`), and `lastScaleTorusClauses_torusFam`: the clauses on
  every admissible torus from the clauses on the tori of the family.
-/

@[expose] public section

open Finset Balaban Balaban.LargeField Balaban.LargeField.Def7 Balaban.RootFSpine.LastScale

namespace Balaban.RootFSpine

variable {d N : ℕ}

/-- **The four clauses of the last-scale activities on one torus** (the body of
`LastScaleTorusClauses`): support on the polymers of side `M L^{k+1}` (in the increment),
analyticity on the unit `ℓ¹` ball, locality in `g|_X`, and the bound
`‖F(X; g) - F(X; 0)‖ ≤ B e^{-κ'|X|/(M L^{k+1})^d}`. -/
def TorusClausesAt (d N L M k : ℕ) (κ' B : ℝ) (ℓ : ℕ) [NeZero ℓ]
    (F : Finset (Torus d ℓ) → (Torus d ℓ → Fin N → ℂ) → ℂ) : Prop :=
  (∀ X, ¬ IsPolymer d ℓ (M * L ^ (k + 1)) X → ∀ g, F X g = F X 0) ∧
    (∀ X, AnalyticOnNhd ℂ (F X) {g | ∑ y, ∑ i, ‖g y i‖ < 1}) ∧
    (∀ X (g g' : Torus d ℓ → Fin N → ℂ), (∀ y ∈ X, g y = g' y) → F X g = F X g') ∧
    (∀ X (g : Torus d ℓ → Fin N → ℂ), ∑ y, ∑ i, ‖g y i‖ < 1 →
      ‖F X g - F X 0‖ ≤ B * Real.exp (-κ' * (X.card : ℝ) / ((M : ℝ) * (L : ℝ) ^ (k + 1)) ^ d))

/-- `LastScaleTorusClauses` is the clauses on every admissible torus. -/
theorem lastScaleTorusClauses_iff {L M kf k : ℕ} {κ' B : ℝ}
    (aT : (ℓ : ℕ) → Finset (Torus d ℓ) → (Torus d ℓ → Fin N → ℂ) → ℂ) :
    LastScaleTorusClauses d N L M kf k κ' B aT ↔
      ∀ (ℓ : ℕ) [NeZero ℓ], M * L ^ (kf + 1) ∣ ℓ → TorusClausesAt d N L M k κ' B ℓ (aT ℓ) :=
  Iff.rfl

/-- **Rule 10**: the zero family satisfies the clauses. -/
theorem torusClausesAt_zero {L M k : ℕ} {κ' B : ℝ} (hB : 0 ≤ B) (ℓ : ℕ) [NeZero ℓ] :
    TorusClausesAt d N L M k κ' B ℓ (fun _ _ => 0) :=
  ⟨fun _ _ _ => rfl, fun _ => analyticOnNhd_const, fun _ _ _ _ => rfl,
    fun _ _ _ => by rw [sub_self, norm_zero]; positivity⟩

/-- **The clauses of a sum**: the amplitudes add and the rate is at most both rates. -/
theorem torusClausesAt_add {L M k : ℕ} {κ' κ₁ κ₂ B₁ B₂ : ℝ} {ℓ : ℕ} [NeZero ℓ]
    {F₁ F₂ : Finset (Torus d ℓ) → (Torus d ℓ → Fin N → ℂ) → ℂ}
    (h₁ : TorusClausesAt d N L M k κ₁ B₁ ℓ F₁) (h₂ : TorusClausesAt d N L M k κ₂ B₂ ℓ F₂)
    (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂) (hκ₁ : κ' ≤ κ₁) (hκ₂ : κ' ≤ κ₂) :
    TorusClausesAt d N L M k κ' (B₁ + B₂) ℓ (fun X g => F₁ X g + F₂ X g) := by
  refine ⟨fun X hX g => by beta_reduce; rw [h₁.1 X hX g, h₂.1 X hX g],
    fun X => (h₁.2.1 X).add (h₂.2.1 X),
    fun X g g' hgg => by beta_reduce; rw [h₁.2.2.1 X g g' hgg, h₂.2.2.1 X g g' hgg],
    fun X g hg => ?_⟩
  have hP : 0 ≤ (X.card : ℝ) / ((M : ℝ) * (L : ℝ) ^ (k + 1)) ^ d := by positivity
  have e : ∀ κ : ℝ, -κ * (X.card : ℝ) / ((M : ℝ) * (L : ℝ) ^ (k + 1)) ^ d =
      -κ * ((X.card : ℝ) / ((M : ℝ) * (L : ℝ) ^ (k + 1)) ^ d) := fun κ => by ring
  have hm : ∀ κ, κ' ≤ κ → Real.exp (-κ * (X.card : ℝ) / ((M : ℝ) * (L : ℝ) ^ (k + 1)) ^ d) ≤
      Real.exp (-κ' * (X.card : ℝ) / ((M : ℝ) * (L : ℝ) ^ (k + 1)) ^ d) := fun κ hκ => by
    rw [e, e]
    exact Real.exp_le_exp.2 (by nlinarith)
  calc ‖F₁ X g + F₂ X g - (F₁ X 0 + F₂ X 0)‖
      = ‖(F₁ X g - F₁ X 0) + (F₂ X g - F₂ X 0)‖ := by ring_nf
    _ ≤ ‖F₁ X g - F₁ X 0‖ + ‖F₂ X g - F₂ X 0‖ := norm_add_le _ _
    _ ≤ B₁ * Real.exp (-κ₁ * (X.card : ℝ) / ((M : ℝ) * (L : ℝ) ^ (k + 1)) ^ d) +
        B₂ * Real.exp (-κ₂ * (X.card : ℝ) / ((M : ℝ) * (L : ℝ) ^ (k + 1)) ^ d) :=
        add_le_add (h₁.2.2.2 X g hg) (h₂.2.2.2 X g hg)
    _ ≤ B₁ * Real.exp (-κ' * (X.card : ℝ) / ((M : ℝ) * (L : ℝ) ^ (k + 1)) ^ d) +
        B₂ * Real.exp (-κ' * (X.card : ℝ) / ((M : ℝ) * (L : ℝ) ^ (k + 1)) ^ d) :=
        add_le_add (mul_le_mul_of_nonneg_left (hm κ₁ hκ₁) hB₁)
          (mul_le_mul_of_nonneg_left (hm κ₂ hκ₂) hB₂)
    _ = _ := by ring

/-- **Transport of the clauses along an equality of sides.** -/
theorem torusClausesAt_cast {L M k : ℕ} {κ' B : ℝ} {a b : ℕ} [NeZero a] [NeZero b] (e : a = b)
    {F : Finset (Torus d b) → (Torus d b → Fin N → ℂ) → ℂ}
    (h : TorusClausesAt d N L M k κ' B b F) :
    TorusClausesAt d N L M k κ' B a (fun X g => F (e ▸ X) (e ▸ g)) := by
  subst e
  exact h

/-- **The activities on every side** from activities `A nK` on the tori `𝕋_{M n_K L^K}` of the
family: on a side `ℓ` with `M L^K ∣ ℓ` and `nK = ℓ / (M L^K) ≠ 0`, the activities of the torus `nK`
read through the identification of the sides; `0` on the other sides. -/
noncomputable def torusFam (M L K : ℕ)
    (A : ∀ (nK : ℕ) [NeZero nK], Finset (Torus d (M * sides L K nK K * L ^ K)) →
      (Torus d (M * sides L K nK K * L ^ K) → Fin N → ℂ) → ℂ)
    (ℓ : ℕ) (X : Finset (Torus d ℓ)) (g : Torus d ℓ → Fin N → ℂ) : ℂ :=
  if h : ℓ = M * sides L K (ℓ / (M * L ^ K)) K * L ^ K ∧ ℓ / (M * L ^ K) ≠ 0 then
    haveI : NeZero (ℓ / (M * L ^ K)) := ⟨h.2⟩
    A (ℓ / (M * L ^ K)) (h.1 ▸ X) (h.1 ▸ g)
  else 0

/-- The side of the torus `nK` of the family is `M L^K nK`. -/
theorem side_eq_mul (M L K nK : ℕ) : M * sides L K nK K * L ^ K = M * L ^ K * nK := by
  rw [sides_self]; ring

/-- **The activities on the side of a torus of the family are those of the torus.** -/
theorem torusFam_apply {M L K : ℕ} (hML : 0 < M * L ^ K)
    (A : ∀ (nK : ℕ) [NeZero nK], Finset (Torus d (M * sides L K nK K * L ^ K)) →
      (Torus d (M * sides L K nK K * L ^ K) → Fin N → ℂ) → ℂ)
    (nK : ℕ) [NeZero nK] (X : Finset (Torus d (M * sides L K nK K * L ^ K)))
    (g : Torus d (M * sides L K nK K * L ^ K) → Fin N → ℂ) :
    torusFam M L K A (M * sides L K nK K * L ^ K) X g = A nK X g := by
  have hq : M * sides L K nK K * L ^ K / (M * L ^ K) = nK := by
    rw [side_eq_mul, Nat.mul_div_cancel_left _ hML]
  have key : ∀ (q : ℕ) [NeZero q], q = nK → ∀ (e : M * sides L K nK K * L ^ K =
      M * sides L K q K * L ^ K), A q (e ▸ X) (e ▸ g) = A nK X g := by
    intro q _ hqn e
    subst hqn
    rfl
  unfold torusFam
  have hc : M * sides L K nK K * L ^ K =
      M * sides L K (M * sides L K nK K * L ^ K / (M * L ^ K)) K * L ^ K ∧
      M * sides L K nK K * L ^ K / (M * L ^ K) ≠ 0 := ⟨by rw [hq], by rw [hq]; exact NeZero.ne nK⟩
  rw [dite_eq_left_of_eq_true (eq_true hc)]
  have : NeZero (M * sides L K nK K * L ^ K / (M * L ^ K)) := ⟨hc.2⟩
  exact key _ hq hc.1

/-- The activities on two equal sides correspond under the identification of the sides. -/
theorem torusFam_cast {M L K : ℕ}
    (A : ∀ (nK : ℕ) [NeZero nK], Finset (Torus d (M * sides L K nK K * L ^ K)) →
      (Torus d (M * sides L K nK K * L ^ K) → Fin N → ℂ) → ℂ)
    {a b : ℕ} (e : a = b) (X : Finset (Torus d a)) (g : Torus d a → Fin N → ℂ) :
    torusFam M L K A a X g = torusFam M L K A b (e ▸ X) (e ▸ g) := by
  subst e
  rfl

/-- **The clauses on every admissible torus from the clauses on the tori of the family**
(`M L^K ∣ ℓ`, `K = kf + 1`). -/
theorem lastScaleTorusClauses_torusFam {L M kf k : ℕ} [NeZero L] [NeZero M] {κ' B : ℝ}
    (hML : 0 < M * L ^ (kf + 1))
    (A : ∀ (nK : ℕ) [NeZero nK], Finset (Torus d (M * sides L (kf + 1) nK (kf + 1) * L ^ (kf + 1))) →
      (Torus d (M * sides L (kf + 1) nK (kf + 1) * L ^ (kf + 1)) → Fin N → ℂ) → ℂ)
    (hA : ∀ (nK : ℕ) [NeZero nK],
      TorusClausesAt d N L M k κ' B (M * sides L (kf + 1) nK (kf + 1) * L ^ (kf + 1)) (A nK)) :
    LastScaleTorusClauses d N L M kf k κ' B (torusFam M L (kf + 1) A) := by
  intro ℓ _ hdvd
  obtain ⟨nK, rfl⟩ := hdvd
  have hnK : nK ≠ 0 := by
    rintro rfl; exact NeZero.ne (M * L ^ (kf + 1) * 0) (by simp)
  have : NeZero nK := ⟨hnK⟩
  have e : M * L ^ (kf + 1) * nK = M * sides L (kf + 1) nK (kf + 1) * L ^ (kf + 1) :=
    (side_eq_mul M L (kf + 1) nK).symm
  have hfun : torusFam M L (kf + 1) A (M * L ^ (kf + 1) * nK) =
      fun X g => A nK (e ▸ X) (e ▸ g) := by
    funext X g
    rw [torusFam_cast A e X g, torusFam_apply hML A nK]
  rw [hfun]
  exact torusClausesAt_cast e (hA nK)

end Balaban.RootFSpine
