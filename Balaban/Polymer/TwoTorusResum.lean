module

public import Balaban.Polymer.TwoTorusEdgeChain
public import Balaban.Polymer.TwoTorusQuarterBox

/-!
# Resummation of the last-scale terms onto the outside of the quarter box (W845, blocker 7)

Abstract assembly (leaf 5 of `notes/phase1/TORUSLAST2.md`).  For every torus `ℓ` of an admissible
family we are given terms `T ℓ g X` indexed by the supports `X ∈ P ℓ` (a finite set of polymers)
with a support condition, a locality condition, membership in a space `W` of functions of the
parameter `g` (analyticity), and the crude bound `B e^{-κ' |X|}`.  A canonical torus `can X` is
chosen for each support `X`.  The new terms are `T (can X) g X` for `X` in the quarter box of `ℓ`,
and for `X` outside they are the old term plus the differences `T ℓ g X₀ - T (can X₀) g X₀` of the
supports `X₀` of the quarter box whose chain `Φ ℓ X₀` ends at `X`.  The sum over `X` is unchanged,
the new terms of the quarter box do not depend on the torus, and the new terms decay at the rate
`κ ≤ κ' - log 2` provided the difference of two tori decays like `e^{-λ τ}` in the margin `τ`
with `λ ≥ κ'`.
-/

@[expose] public section

noncomputable section

open scoped Classical

open Finset

namespace Balaban.Polymer

/-- **Resummation of the last-scale terms (W845, blocker 7, leaf 5).**  Conclusion: new terms
`Tn` given by the explicit formula, with (a) the same sum over `X ∈ P ℓ`, (b) the exact torus
independence on the quarter boxes, (c) the bound `(B + a e^{κ'} + 2 B e^{κ' t₀}) e^{-κ |X|}`,
(d) support, locality and membership in `W`. -/
theorem resum_lastScale {ι G S : Type*} (P : ι → Finset S) (Q : ι → S → Prop) (sz : S → ℕ)
    (τ : ι → S → ℕ) (Φ : ι → S → S) (can : S → ι) (D : Set G)
    (W : Submodule ℂ (G → ℂ)) (R : S → Prop) (Ag : S → G → G → Prop) (T : ι → G → S → ℂ)
    {B a κ κ' lam : ℝ} {t₀ : ℕ} (hB : 0 ≤ B) (ha : 0 ≤ a) (hκ : 0 ≤ κ)
    (hκ' : κ + Real.log 2 ≤ κ') (hlam : κ' ≤ lam)
    (hcanP : ∀ ℓ X, X ∈ P ℓ → Q ℓ X → X ∈ P (can X))
    (hΦP : ∀ ℓ X, X ∈ P ℓ → Q ℓ X → Φ ℓ X ∈ P ℓ ∧ ¬ Q ℓ (Φ ℓ X))
    (hΦsz : ∀ ℓ X, X ∈ P ℓ → Q ℓ X → sz (Φ ℓ X) ≤ sz X + τ ℓ X + 1)
    (hfib : ∀ ℓ Z, (((P ℓ).filter (Q ℓ)).filter (fun X => Φ ℓ X = Z)).card ≤ 2 ^ sz Z)
    (hRΦ : ∀ ℓ X, X ∈ P ℓ → Q ℓ X → R X → R (Φ ℓ X))
    (hAgΦ : ∀ ℓ X, X ∈ P ℓ → Q ℓ X → ∀ g g', Ag (Φ ℓ X) g g' → Ag X g g')
    (hsupp : ∀ ℓ X, X ∈ P ℓ → ¬ R X → ∀ g, T ℓ g X = 0)
    (hloc : ∀ ℓ X, X ∈ P ℓ → ∀ g g', Ag X g g' → T ℓ g X = T ℓ g' X)
    (han : ∀ ℓ X, X ∈ P ℓ → (fun g => T ℓ g X) ∈ W)
    (hbd : ∀ ℓ X, X ∈ P ℓ → ∀ g ∈ D, ‖T ℓ g X‖ ≤ B * Real.exp (-κ' * (sz X : ℝ)))
    (hclose : ∀ ℓ X, X ∈ P ℓ → Q ℓ X → t₀ ≤ τ ℓ X → ∀ g ∈ D,
      ‖T ℓ g X - T (can X) g X‖ ≤
        a * Real.exp (-lam * (τ ℓ X : ℝ)) * Real.exp (-κ' * (sz X : ℝ))) :
    ∃ Tn : ι → G → S → ℂ,
      (∀ ℓ g X, Tn ℓ g X = if Q ℓ X then T (can X) g X else
        T ℓ g X + ∑ X₀ ∈ ((P ℓ).filter (Q ℓ)).filter (fun X₀ => Φ ℓ X₀ = X),
          (T ℓ g X₀ - T (can X₀) g X₀)) ∧
      (∀ ℓ g, ∑ X ∈ P ℓ, Tn ℓ g X = ∑ X ∈ P ℓ, T ℓ g X) ∧
      (∀ ℓ ℓ' g X, Q ℓ X → Q ℓ' X → Tn ℓ g X = Tn ℓ' g X) ∧
      (∀ ℓ X, X ∈ P ℓ → ∀ g ∈ D, ‖Tn ℓ g X‖ ≤
        (B + a * Real.exp κ' + 2 * B * Real.exp (κ' * (t₀ : ℝ))) *
          Real.exp (-κ * (sz X : ℝ))) ∧
      (∀ ℓ X, X ∈ P ℓ → ¬ R X → ∀ g, Tn ℓ g X = 0) ∧
      (∀ ℓ X, X ∈ P ℓ → ∀ g g', Ag X g g' → Tn ℓ g X = Tn ℓ g' X) ∧
      (∀ ℓ X, X ∈ P ℓ → (fun g => Tn ℓ g X) ∈ W) := by
  set K₀ : ℝ := a * Real.exp κ' + 2 * B * Real.exp (κ' * (t₀ : ℝ)) with hK₀
  have hκ'0 : 0 ≤ κ' := by
    have : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    linarith
  have hK₀0 : 0 ≤ K₀ := by positivity
  -- the bound on each difference, in terms of the end of its chain
  have hΔ : ∀ ℓ X₀, X₀ ∈ P ℓ → Q ℓ X₀ → ∀ g ∈ D,
      ‖T ℓ g X₀ - T (can X₀) g X₀‖ ≤ K₀ * Real.exp (-κ' * (sz (Φ ℓ X₀) : ℝ)) := by
    intro ℓ X₀ hX hQ g hg
    have hz : ((sz (Φ ℓ X₀) : ℕ) : ℝ) ≤ (sz X₀ : ℝ) + (τ ℓ X₀ : ℝ) + 1 := by
      exact_mod_cast hΦsz ℓ X₀ hX hQ
    have hτ0 : (0 : ℝ) ≤ (τ ℓ X₀ : ℝ) := Nat.cast_nonneg _
    by_cases ht : t₀ ≤ τ ℓ X₀
    · refine (hclose ℓ X₀ hX hQ ht g hg).trans ?_
      rw [mul_assoc, ← Real.exp_add]
      have h1 : -lam * (τ ℓ X₀ : ℝ) + -κ' * (sz X₀ : ℝ) ≤ κ' + -κ' * (sz (Φ ℓ X₀) : ℝ) := by
        have h2 := mul_le_mul_of_nonneg_left hz hκ'0
        have h3 := mul_le_mul_of_nonneg_right hlam hτ0
        nlinarith
      calc a * Real.exp (-lam * (τ ℓ X₀ : ℝ) + -κ' * (sz X₀ : ℝ))
          ≤ a * Real.exp (κ' + -κ' * (sz (Φ ℓ X₀) : ℝ)) :=
            mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 h1) ha
        _ = a * Real.exp κ' * Real.exp (-κ' * (sz (Φ ℓ X₀) : ℝ)) := by
            rw [Real.exp_add]; ring
        _ ≤ K₀ * Real.exp (-κ' * (sz (Φ ℓ X₀) : ℝ)) := by
            refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
            rw [hK₀]
            have : 0 ≤ 2 * B * Real.exp (κ' * (t₀ : ℝ)) := by positivity
            linarith
    · have ht' : τ ℓ X₀ + 1 ≤ t₀ := by omega
      have ht'' : (τ ℓ X₀ : ℝ) + 1 ≤ (t₀ : ℝ) := by exact_mod_cast ht'
      have hb1 := hbd ℓ X₀ hX g hg
      have hb2 := hbd (can X₀) X₀ (hcanP ℓ X₀ hX hQ) g hg
      have h1 : -κ' * (sz X₀ : ℝ) ≤ κ' * (t₀ : ℝ) + -κ' * (sz (Φ ℓ X₀) : ℝ) := by
        have h2 := mul_le_mul_of_nonneg_left hz hκ'0
        have h3 := mul_le_mul_of_nonneg_left ht'' hκ'0
        nlinarith
      have h4 : Real.exp (-κ' * (sz X₀ : ℝ)) ≤
          Real.exp (κ' * (t₀ : ℝ)) * Real.exp (-κ' * (sz (Φ ℓ X₀) : ℝ)) := by
        rw [← Real.exp_add]; exact Real.exp_le_exp.2 h1
      calc ‖T ℓ g X₀ - T (can X₀) g X₀‖ ≤ ‖T ℓ g X₀‖ + ‖T (can X₀) g X₀‖ := norm_sub_le _ _
        _ ≤ 2 * B * Real.exp (-κ' * (sz X₀ : ℝ)) := by linarith
        _ ≤ 2 * B * (Real.exp (κ' * (t₀ : ℝ)) * Real.exp (-κ' * (sz (Φ ℓ X₀) : ℝ))) :=
            mul_le_mul_of_nonneg_left h4 (by positivity)
        _ ≤ K₀ * Real.exp (-κ' * (sz (Φ ℓ X₀) : ℝ)) := by
            rw [← mul_assoc]
            refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
            rw [hK₀]
            have : 0 ≤ a * Real.exp κ' := by positivity
            linarith
  refine ⟨fun ℓ g X => if Q ℓ X then T (can X) g X else
        T ℓ g X + ∑ X₀ ∈ ((P ℓ).filter (Q ℓ)).filter (fun X₀ => Φ ℓ X₀ = X),
          (T ℓ g X₀ - T (can X₀) g X₀), fun _ _ _ => rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- (a) the sum
    intro ℓ g
    rw [← Finset.sum_filter_add_sum_filter_not (P ℓ) (Q ℓ),
      ← Finset.sum_filter_add_sum_filter_not (P ℓ) (Q ℓ) (fun X => T ℓ g X)]
    have h1 : ∑ X ∈ (P ℓ).filter (Q ℓ), (if Q ℓ X then T (can X) g X else
        T ℓ g X + ∑ X₀ ∈ ((P ℓ).filter (Q ℓ)).filter (fun X₀ => Φ ℓ X₀ = X),
          (T ℓ g X₀ - T (can X₀) g X₀)) = ∑ X ∈ (P ℓ).filter (Q ℓ), T (can X) g X := by
      refine Finset.sum_congr rfl fun X hX => ?_
      simp only [(Finset.mem_filter.1 hX).2, ↓reduceIte]
    have h2 : ∑ X ∈ (P ℓ).filter (fun X => ¬ Q ℓ X), (if Q ℓ X then T (can X) g X else
        T ℓ g X + ∑ X₀ ∈ ((P ℓ).filter (Q ℓ)).filter (fun X₀ => Φ ℓ X₀ = X),
          (T ℓ g X₀ - T (can X₀) g X₀)) = ∑ X ∈ (P ℓ).filter (fun X => ¬ Q ℓ X),
        (T ℓ g X + ∑ X₀ ∈ ((P ℓ).filter (Q ℓ)).filter (fun X₀ => Φ ℓ X₀ = X),
          (T ℓ g X₀ - T (can X₀) g X₀)) := by
      refine Finset.sum_congr rfl fun X hX => ?_
      simp only [(Finset.mem_filter.1 hX).2, ↓reduceIte]
    have h3 : ∑ X ∈ (P ℓ).filter (fun X => ¬ Q ℓ X),
        ∑ X₀ ∈ ((P ℓ).filter (Q ℓ)).filter (fun X₀ => Φ ℓ X₀ = X),
          (T ℓ g X₀ - T (can X₀) g X₀) =
        ∑ X₀ ∈ (P ℓ).filter (Q ℓ), (T ℓ g X₀ - T (can X₀) g X₀) := by
      refine Finset.sum_fiberwise_of_maps_to (g := Φ ℓ) (fun X₀ hX₀ => ?_) _
      obtain ⟨hP, hQ⟩ := Finset.mem_filter.1 hX₀
      exact Finset.mem_filter.2 ⟨(hΦP ℓ X₀ hP hQ).1, (hΦP ℓ X₀ hP hQ).2⟩
    rw [h1, h2, Finset.sum_add_distrib, h3, Finset.sum_sub_distrib]
    ring
  · -- (b) torus independence
    intro ℓ ℓ' g X hQ hQ'
    simp only [hQ, hQ', ↓reduceIte]
  · -- (c) the bound
    intro ℓ X hX g hg
    have hexp : ∀ n : ℕ, Real.exp (-κ' * (n : ℝ)) ≤ Real.exp (-κ * (n : ℝ)) := by
      intro n
      refine Real.exp_le_exp.2 ?_
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg _
      have : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      nlinarith
    have hBle : B ≤ B + K₀ := by linarith
    by_cases hQ : Q ℓ X
    · simp only [hQ, ↓reduceIte]
      refine (hbd (can X) X (hcanP ℓ X hX hQ) g hg).trans ?_
      calc B * Real.exp (-κ' * (sz X : ℝ)) ≤ B * Real.exp (-κ * (sz X : ℝ)) :=
            mul_le_mul_of_nonneg_left (hexp _) hB
        _ ≤ _ := by
            refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
            linarith [show 0 ≤ 2 * B * Real.exp (κ' * (t₀ : ℝ)) by positivity,
              show 0 ≤ a * Real.exp κ' by positivity]
    · simp only [hQ, ↓reduceIte]
      have hsum : ‖∑ X₀ ∈ ((P ℓ).filter (Q ℓ)).filter (fun X₀ => Φ ℓ X₀ = X),
          (T ℓ g X₀ - T (can X₀) g X₀)‖ ≤ K₀ * Real.exp (-κ * (sz X : ℝ)) := by
        calc _ ≤ ∑ X₀ ∈ ((P ℓ).filter (Q ℓ)).filter (fun X₀ => Φ ℓ X₀ = X),
              ‖T ℓ g X₀ - T (can X₀) g X₀‖ := norm_sum_le _ _
          _ ≤ ∑ X₀ ∈ ((P ℓ).filter (Q ℓ)).filter (fun X₀ => Φ ℓ X₀ = X),
              K₀ * Real.exp (-κ' * (sz X : ℝ)) := by
              refine Finset.sum_le_sum fun X₀ hX₀ => ?_
              obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hX₀
              obtain ⟨hP, hQ0⟩ := Finset.mem_filter.1 h1
              have := hΔ ℓ X₀ hP hQ0 g hg
              rwa [h2] at this
          _ = (((P ℓ).filter (Q ℓ)).filter (fun X₀ => Φ ℓ X₀ = X)).card •
              (K₀ * Real.exp (-κ' * (sz X : ℝ))) := Finset.sum_const _
          _ ≤ ((2 : ℝ) ^ sz X) * (K₀ * Real.exp (-κ' * (sz X : ℝ))) := by
              rw [nsmul_eq_mul]
              refine mul_le_mul_of_nonneg_right ?_ (by positivity)
              exact_mod_cast hfib ℓ X
          _ = K₀ * Real.exp ((sz X : ℝ) * Real.log 2 + -κ' * (sz X : ℝ)) := by
              rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log (by norm_num)]; ring
          _ ≤ K₀ * Real.exp (-κ * (sz X : ℝ)) := by
              refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hK₀0
              have : (0 : ℝ) ≤ sz X := Nat.cast_nonneg _
              nlinarith
      calc _ ≤ ‖T ℓ g X‖ + ‖∑ X₀ ∈ ((P ℓ).filter (Q ℓ)).filter (fun X₀ => Φ ℓ X₀ = X),
              (T ℓ g X₀ - T (can X₀) g X₀)‖ := norm_add_le _ _
        _ ≤ B * Real.exp (-κ * (sz X : ℝ)) + K₀ * Real.exp (-κ * (sz X : ℝ)) := by
            refine add_le_add ((hbd ℓ X hX g hg).trans ?_) hsum
            exact mul_le_mul_of_nonneg_left (hexp _) hB
        _ = _ := by rw [hK₀]; ring
  · -- (d) support
    intro ℓ X hX hR g
    by_cases hQ : Q ℓ X
    · simp only [hQ, ↓reduceIte]
      exact hsupp (can X) X (hcanP ℓ X hX hQ) hR g
    · simp only [hQ, ↓reduceIte]
      rw [hsupp ℓ X hX hR g, zero_add]
      refine Finset.sum_eq_zero fun X₀ hX₀ => ?_
      obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hX₀
      obtain ⟨hP, hQ0⟩ := Finset.mem_filter.1 h1
      have hR0 : ¬ R X₀ := fun h => hR (h2 ▸ hRΦ ℓ X₀ hP hQ0 h)
      rw [hsupp ℓ X₀ hP hR0 g, hsupp (can X₀) X₀ (hcanP ℓ X₀ hP hQ0) hR0 g, sub_zero]
  · -- (d) locality
    intro ℓ X hX g g' hag
    by_cases hQ : Q ℓ X
    · simp only [hQ, ↓reduceIte]
      exact hloc (can X) X (hcanP ℓ X hX hQ) g g' hag
    · simp only [hQ, ↓reduceIte]
      congr 1
      · exact hloc ℓ X hX g g' hag
      · refine Finset.sum_congr rfl fun X₀ hX₀ => ?_
        obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hX₀
        obtain ⟨hP, hQ0⟩ := Finset.mem_filter.1 h1
        have hag0 : Ag X₀ g g' := hAgΦ ℓ X₀ hP hQ0 g g' (h2 ▸ hag)
        rw [hloc ℓ X₀ hP g g' hag0, hloc (can X₀) X₀ (hcanP ℓ X₀ hP hQ0) g g' hag0]
  · -- (d) membership in `W`
    intro ℓ X hX
    by_cases hQ : Q ℓ X
    · simp only [hQ, ↓reduceIte]
      exact han (can X) X (hcanP ℓ X hX hQ)
    · simp only [hQ, ↓reduceIte]
      have hsm : (fun g => ∑ X₀ ∈ ((P ℓ).filter (Q ℓ)).filter (fun X₀ => Φ ℓ X₀ = X),
          (T ℓ g X₀ - T (can X₀) g X₀)) ∈ W := by
        have : (fun g => ∑ X₀ ∈ ((P ℓ).filter (Q ℓ)).filter (fun X₀ => Φ ℓ X₀ = X),
            (T ℓ g X₀ - T (can X₀) g X₀)) = ∑ X₀ ∈ ((P ℓ).filter (Q ℓ)).filter
              (fun X₀ => Φ ℓ X₀ = X), ((fun g => T ℓ g X₀) - fun g => T (can X₀) g X₀) := by
          ext g; simp [Finset.sum_apply]
        rw [this]
        refine W.sum_mem fun X₀ hX₀ => ?_
        obtain ⟨h1, _⟩ := Finset.mem_filter.1 hX₀
        obtain ⟨hP, hQ0⟩ := Finset.mem_filter.1 h1
        exact W.sub_mem (han ℓ X₀ hP) (han (can X₀) X₀ (hcanP ℓ X₀ hP hQ0))
      have := W.add_mem (han ℓ X hX) hsm
      exact this

section Instance

/-- **The rate of the quarter-box closeness (W845).**  The bound of `finalCoef_close_quarterBox`,
`P (C₀ e^{-c₀ M (2t - 7)} + ε) / (e^{κ₁} - 1)^n` for a coefficient with `n` cells, is at most
`a e^{-λ t} e^{-κ' n}` with `a = P (C₀ e^{7 c₀ M} + ε₁)`, as soon as `λ ≤ 2 c₀ M`,
`κ' ≤ log (e^{κ₁} - 1)` and the closeness `ε` of the operators on the support is at most
`ε₁ e^{-λ t}`. -/
theorem quarterBox_rate {Pc C₀ c₀ Mr κ₁ κ' lam ε₁ ε : ℝ} {t n : ℕ} (hP : 0 ≤ Pc) (hC : 0 ≤ C₀)
    (hκ₁ : 0 < κ₁) (hκ' : κ' ≤ Real.log (Real.exp κ₁ - 1))
    (hlam : lam ≤ 2 * c₀ * Mr) (hε0 : 0 ≤ ε) (hε : ε ≤ ε₁ * Real.exp (-lam * (t : ℝ))) :
    Pc * (C₀ * Real.exp (-c₀ * (Mr * (2 * (t : ℝ) - 7))) + ε) / (Real.exp κ₁ - 1) ^ n ≤
      (Pc * (C₀ * Real.exp (7 * c₀ * Mr) + ε₁)) * Real.exp (-lam * (t : ℝ)) *
        Real.exp (-κ' * (n : ℝ)) := by
  have hbase : 0 < Real.exp κ₁ - 1 := by
    have := Real.add_one_lt_exp hκ₁.ne'
    linarith
  have hden : Real.exp (κ' * (n : ℝ)) ≤ (Real.exp κ₁ - 1) ^ n := by
    calc Real.exp (κ' * (n : ℝ)) ≤ Real.exp (Real.log (Real.exp κ₁ - 1) * (n : ℝ)) :=
          Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hκ' (Nat.cast_nonneg _))
      _ = (Real.exp κ₁ - 1) ^ n := by
          rw [mul_comm, Real.exp_nat_mul, Real.exp_log hbase]
  have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg _
  have hnum : C₀ * Real.exp (-c₀ * (Mr * (2 * (t : ℝ) - 7))) + ε ≤
      (C₀ * Real.exp (7 * c₀ * Mr) + ε₁) * Real.exp (-lam * (t : ℝ)) := by
    have h1 : Real.exp (-c₀ * (Mr * (2 * (t : ℝ) - 7))) ≤
        Real.exp (7 * c₀ * Mr) * Real.exp (-lam * (t : ℝ)) := by
      rw [← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      have : lam * (t : ℝ) ≤ 2 * c₀ * Mr * (t : ℝ) := mul_le_mul_of_nonneg_right hlam ht0
      nlinarith
    have := mul_le_mul_of_nonneg_left h1 hC
    nlinarith
  have hnum0 : 0 ≤ C₀ * Real.exp (-c₀ * (Mr * (2 * (t : ℝ) - 7))) + ε := by positivity
  have hexp : Real.exp (-κ' * (n : ℝ)) = (Real.exp (κ' * (n : ℝ)))⁻¹ := by
    rw [← Real.exp_neg]; congr 1; ring
  calc Pc * (C₀ * Real.exp (-c₀ * (Mr * (2 * (t : ℝ) - 7))) + ε) / (Real.exp κ₁ - 1) ^ n
      ≤ Pc * (C₀ * Real.exp (-c₀ * (Mr * (2 * (t : ℝ) - 7))) + ε) / Real.exp (κ' * (n : ℝ)) :=
        div_le_div_of_nonneg_left (by positivity) (Real.exp_pos _) hden
    _ = Pc * (C₀ * Real.exp (-c₀ * (Mr * (2 * (t : ℝ) - 7))) + ε) *
          Real.exp (-κ' * (n : ℝ)) := by rw [hexp, div_eq_mul_inv]
    _ ≤ Pc * ((C₀ * Real.exp (7 * c₀ * Mr) + ε₁) * Real.exp (-lam * (t : ℝ))) *
          Real.exp (-κ' * (n : ℝ)) := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hnum hP) (Real.exp_pos _).le
    _ = _ := by ring

/-- **The frame (W845).**  The cells of the macro cover, `Fin d → Fin K` (`MacIdx d N M` with
`K = macK N M`), are the cells `Balaban.Torus d K` of the chain geometry of W843: there is a
bijection that preserves the coordinates `(·).val`, so that the hypothesis "every coordinate
`z i ≤ m` or `K - m ≤ z i`" of `finalCoef_close_quarterBox` is the box of radius `m` of
`exists_edgeChain_map`. -/
theorem macIdx_torus_frame {d K : ℕ} [NeZero K] :
    ∃ e : (Fin d → Fin K) ≃ Balaban.Torus d K, (∀ z i, (e z i).val = (z i : ℕ)) ∧
      ∀ (m : ℕ) (z : Fin d → Fin K),
        ((∀ i, (z i : ℕ) ≤ m ∨ K - m ≤ (z i : ℕ)) ↔
          ∀ μ, ((e z μ).val ≤ m ∨ K - m ≤ (e z μ).val)) := by
  obtain ⟨k, rfl⟩ : ∃ k, K = k + 1 := ⟨K - 1, by have := NeZero.pos K; omega⟩
  refine ⟨Equiv.piCongrRight fun _ => (ZMod.finEquiv (k + 1)).toEquiv, fun z i => rfl, ?_⟩
  intro m z
  exact Iff.rfl

/-- **The resummation with the quarter-box closeness (W845).**  The hypothesis `hclose` of
`resum_lastScale` follows from the bound delivered by `finalCoef_close_quarterBox` (in the form
`Pc (C₀ e^{-c₀ M (2τ - 7)} + ε)/(e^{κ₁} - 1)^{|X|}` at the margin `τ`) together with a decay
`ε ≤ ε₁ e^{-λ τ}` of the closeness of the operators `E` on the support. -/
theorem resum_lastScale_of_quarterBox {ι G S : Type*} (P : ι → Finset S) (Q : ι → S → Prop)
    (sz : S → ℕ) (τ : ι → S → ℕ) (Φ : ι → S → S) (can : S → ι) (D : Set G)
    (W : Submodule ℂ (G → ℂ)) (R : S → Prop) (Ag : S → G → G → Prop) (T : ι → G → S → ℂ)
    {B κ κ' κ₁ lam Pc C₀ c₀ Mr ε₁ : ℝ} {t₀ : ℕ} (ε : ι → G → S → ℝ)
    (hB : 0 ≤ B) (hκ : 0 ≤ κ)
    (hκ' : κ + Real.log 2 ≤ κ') (hlam : κ' ≤ lam) (hP : 0 ≤ Pc) (hC : 0 ≤ C₀) (hε₁ : 0 ≤ ε₁)
    (hκ₁ : 0 < κ₁) (hκ'₁ : κ' ≤ Real.log (Real.exp κ₁ - 1)) (hlamc : lam ≤ 2 * c₀ * Mr)
    (hcanP : ∀ ℓ X, X ∈ P ℓ → Q ℓ X → X ∈ P (can X))
    (hΦP : ∀ ℓ X, X ∈ P ℓ → Q ℓ X → Φ ℓ X ∈ P ℓ ∧ ¬ Q ℓ (Φ ℓ X))
    (hΦsz : ∀ ℓ X, X ∈ P ℓ → Q ℓ X → sz (Φ ℓ X) ≤ sz X + τ ℓ X + 1)
    (hfib : ∀ ℓ Z, (((P ℓ).filter (Q ℓ)).filter (fun X => Φ ℓ X = Z)).card ≤ 2 ^ sz Z)
    (hRΦ : ∀ ℓ X, X ∈ P ℓ → Q ℓ X → R X → R (Φ ℓ X))
    (hAgΦ : ∀ ℓ X, X ∈ P ℓ → Q ℓ X → ∀ g g', Ag (Φ ℓ X) g g' → Ag X g g')
    (hsupp : ∀ ℓ X, X ∈ P ℓ → ¬ R X → ∀ g, T ℓ g X = 0)
    (hloc : ∀ ℓ X, X ∈ P ℓ → ∀ g g', Ag X g g' → T ℓ g X = T ℓ g' X)
    (han : ∀ ℓ X, X ∈ P ℓ → (fun g => T ℓ g X) ∈ W)
    (hbd : ∀ ℓ X, X ∈ P ℓ → ∀ g ∈ D, ‖T ℓ g X‖ ≤ B * Real.exp (-κ' * (sz X : ℝ)))
    (hcoef : ∀ ℓ X, X ∈ P ℓ → Q ℓ X → t₀ ≤ τ ℓ X → ∀ g ∈ D,
      ‖T ℓ g X - T (can X) g X‖ ≤
        Pc * (C₀ * Real.exp (-c₀ * (Mr * (2 * (τ ℓ X : ℝ) - 7))) + ε ℓ g X) /
          (Real.exp κ₁ - 1) ^ sz X)
    (hε0 : ∀ ℓ g X, 0 ≤ ε ℓ g X)
    (hε : ∀ ℓ X, X ∈ P ℓ → Q ℓ X → t₀ ≤ τ ℓ X → ∀ g ∈ D,
      ε ℓ g X ≤ ε₁ * Real.exp (-lam * (τ ℓ X : ℝ))) :
    ∃ Tn : ι → G → S → ℂ,
      (∀ ℓ g X, Tn ℓ g X = if Q ℓ X then T (can X) g X else
        T ℓ g X + ∑ X₀ ∈ ((P ℓ).filter (Q ℓ)).filter (fun X₀ => Φ ℓ X₀ = X),
          (T ℓ g X₀ - T (can X₀) g X₀)) ∧
      (∀ ℓ g, ∑ X ∈ P ℓ, Tn ℓ g X = ∑ X ∈ P ℓ, T ℓ g X) ∧
      (∀ ℓ ℓ' g X, Q ℓ X → Q ℓ' X → Tn ℓ g X = Tn ℓ' g X) ∧
      (∀ ℓ X, X ∈ P ℓ → ∀ g ∈ D, ‖Tn ℓ g X‖ ≤
        (B + (Pc * (C₀ * Real.exp (7 * c₀ * Mr) + ε₁)) * Real.exp κ' +
          2 * B * Real.exp (κ' * (t₀ : ℝ))) * Real.exp (-κ * (sz X : ℝ))) ∧
      (∀ ℓ X, X ∈ P ℓ → ¬ R X → ∀ g, Tn ℓ g X = 0) ∧
      (∀ ℓ X, X ∈ P ℓ → ∀ g g', Ag X g g' → Tn ℓ g X = Tn ℓ g' X) ∧
      (∀ ℓ X, X ∈ P ℓ → (fun g => Tn ℓ g X) ∈ W) := by
  refine resum_lastScale P Q sz τ Φ can D W R Ag T hB (a := Pc * (C₀ * Real.exp (7 * c₀ * Mr) + ε₁))
    (by positivity) hκ hκ' hlam hcanP hΦP hΦsz hfib hRΦ hAgΦ hsupp hloc han hbd ?_
  intro ℓ X hX hQ ht g hg
  exact (hcoef ℓ X hX hQ ht g hg).trans
    (quarterBox_rate hP hC hκ₁ hκ'₁ hlamc (hε0 ℓ g X) (hε ℓ X hX hQ ht g hg))

end Instance

end Balaban.Polymer
