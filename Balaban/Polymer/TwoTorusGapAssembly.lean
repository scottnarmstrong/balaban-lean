/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusResumInstance
public import Balaban.Polymer.TwoTorusWideBand
public import Balaban.Polymer.TwoTorusRecentre
public import Balaban.Localization.SupportMargin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Assembly of the gap-scale terms into the two-torus resummation (item 24, blocker 7)

At a scale just below the last one the terms `T ℓ g X` of the step torus `ℓ` are indexed by the
polymers `X` of the block torus `Torus d (K ℓ)` (centred coordinates, as for the last scale).  Two
regimes of supports of the quarter box occur.

* **Wide supports**, whose cyclic spread is above `(K - 26) / 25`: they have at least `K / 25`
  cells (`wide_card_of_spread`, from `card_ge_of_spread`), so the chain to the edge of the
  quarter box, of at most `K / 4` cells, is paid by the support (`margin_le_of_wide`); only the
  crude bound is used.
* **Compact supports** (spread at most `(K - 26) / 25`): `25 D + 25 < K ≤ K'`
  (`compact_margin`), so `evTerm_boxMap_of_diameter_of_coef` applies: the term on `ℓ` and the term
  on a larger torus agree once the functional of the step has corresponding coefficients on the
  families `Y(C)` (the recentred correspondence).  This closeness of the functionals is the named
  hypothesis `hFclose` of `resum_gapScale_torus`; the theorem takes it in the weaker form of a
  bound `a e^{-lam τ} e^{-κ₂ |X|}`, the exact correspondence being `a = 0`.

`resum_gapScale_torus` is `resum_lastScale` for the chain map of `lastScale_chain`, the margin
`7 |X|` for the wide supports, and the crude bound for them; the rate of the crude bound is
`κ' ≥ 7 lam + κ₂`.  `ysites_animal` is the link between the Peierls families (`Ysites`) and the
cell sets: the sites `Y[𝒞]` of a connected family form a union of cells whose set of cells is a
polymer (`IsAnimal`) of the block torus.
-/

@[expose] public section

noncomputable section

open scoped Classical

open Finset

namespace Balaban.Polymer

section Link

/-- **A connected union of cells is the union of the cells of a polymer.**  Let `S` be a nonempty
set of sites of `Torus d n`, `n = s m`, saturated for the cells of side `s`, and connected for the
nearest-neighbour adjacency within `S`.  Then the set of its cells is a polymer (`IsAnimal`) of
the block torus `Torus d m`, and `x ∈ S` iff the cell of `x` belongs to it. -/
theorem animal_of_cellUnion {d n s m : ℕ} [NeZero n] [NeZero s] [NeZero m] (hn : n = s * m)
    (S : Set (Balaban.Torus d n)) (hne : S.Nonempty)
    (hsat : ∀ x ∈ S, ∀ y : Balaban.Torus d n, (∀ μ, (x μ).val / s = (y μ).val / s) → y ∈ S)
    (hconn : ∀ x ∈ S, ∀ y ∈ S, Relation.ReflTransGen
      (fun a b => a ∈ S ∧ b ∈ S ∧ Balaban.Localization.Nbr a b) x y) :
    ∃ Yc : Finset (Balaban.Torus d m), IsAnimal (blockGraph d m) Yc ∧
      ∀ x : Balaban.Torus d n, x ∈ S ↔ (fun μ => (((x μ).val / s : ℕ) : ZMod m)) ∈ Yc := by
  subst hn
  have hpoly : Balaban.IsPolymer d (s * m) s (Finset.univ.filter (· ∈ S)) := by
    refine ⟨?_, ?_, ?_⟩
    · obtain ⟨x, hx⟩ := hne
      exact ⟨x, by simpa using hx⟩
    · intro x hx y hxy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      exact hsat x hx y hxy
    · intro x hx y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
      induction hconn x hx y hy with
      | refl => exact Relation.ReflTransGen.refl
      | tail _ hbc ih =>
        exact Relation.ReflTransGen.tail (ih hbc.1)
          ⟨by simpa using hbc.1, by simpa using hbc.2.1, hbc.2.2⟩
  refine ⟨_, isAnimal_image_blockOf hpoly, fun x => ?_⟩
  have h := siteSet_image_blockOf (s := s) (m := m) hpoly.2.1
  constructor
  · intro hx
    exact Finset.mem_image.2 ⟨x, by simpa using hx, rfl⟩
  · intro hx
    have : x ∈ siteSet d s m ((Finset.univ.filter (· ∈ S)).image (blockOf d s m)) := by
      rw [mem_siteSet]; exact hx
    rw [h] at this
    simpa using this

end Link

section Wide

/-- **A wide support has many cells.**  A polymer `Y` of `Torus d K` with two cells at cyclic
distance above `(K - 26) / 25` in a coordinate has at least `K / 25` cells. -/
theorem wide_card_of_spread {d K : ℕ} [NeZero K] {Y : Finset (Balaban.Torus d K)}
    (hA : IsAnimal (blockGraph d K) Y)
    (hw : ∃ b0 ∈ Y, ∃ y ∈ Y, ∃ μ, (K - 26) / 25 < ((y μ - b0 μ).valMinAbs).natAbs) :
    K ≤ 25 * Y.card := by
  obtain ⟨b0, hb, y, hy, μ, hD⟩ := hw
  have := card_ge_of_spread Y hA hb hy μ
  omega

/-- **The chain is paid by a wide support.**  If `K ≤ 25 c` the margin of the chain
(at most `K / 4`) is at most `7 c`. -/
theorem margin_le_of_wide {K c τ : ℕ} (h : K ≤ 25 * c) (hτ : τ ≤ K / 4) : τ ≤ 7 * c := by
  omega

/-- **A compact support is in the range of `evTerm_boxMap_of_diameter_of_coef`.**  If the cyclic
spread `D` of a support is at most `(K - 26) / 25`, then `25 D + 25 < K ≤ K'`. -/
theorem compact_margin {K K' D : ℕ} (hK : 26 ≤ K) (hKK' : K ≤ K') (hD : D ≤ (K - 26) / 25) :
    25 * D + 25 < K ∧ 25 * D + 25 < K' := by
  omega

end Wide

section Assembly

variable {d : ℕ}

/-- **The torus clause at a gap scale (item 24, blocker 7).**  The terms `T ℓ g X` of the tori `ℓ`
are indexed by the polymers `P ℓ` of `Torus d (K ℓ)` read in centred coordinates; `Q ℓ` is the
quarter box, `τ ℓ X = K ℓ / 4 - (largest absolute coordinate of X)` the margin, `can X` a torus
at least as large as every `ℓ` for which `X` lies in the quarter box, and `Wd ℓ X` the wide
supports: they have at least `K ℓ / 25` cells (`hWd`; `wide_card_of_spread`).

The closeness of the functionals at the gap scale is the named hypothesis `hFclose`: for a
support `X` of the quarter box of `ℓ` that is not wide, with margin `τ ℓ X ≥ t₀`, the terms on
`ℓ` and on `can X` satisfy `‖T ℓ g X - T (can X) g X‖ ≤ a e^{-lam τ} e^{-κ₂ |X|}`.  It follows from
the coefficient correspondence of the step's functional on the families `Y(C)`, `X = Y(C)`,
between the two tori under the recentring map (`evTerm_boxMap_of_diameter_of_coef`, with `a = 0`,
since `25 D + 25 < K ℓ ≤ K (can X)` by `compact_margin`); the approximate form is the
translation-covariant closeness of the functional on `Y(C)` with decay in the margin.

The wide supports use only the crude bound `hbd` of rate `κ' ≥ 7 lam + κ₂`: the new terms satisfy
`‖Tn ℓ g X‖ ≤ (B + (a + 2B) e^{κ₂} + 2 B e^{κ₂ t₀}) e^{-κ |X|}` for `κ + log 2 ≤ κ₂ ≤ lam`.
The other conclusions are those of `resum_lastScale_torus`: the same sum over `P ℓ`, equality of
the terms of the quarter box of two tori, support, locality, analyticity. -/
theorem resum_gapScale_torus {ι G : Type*} (K : ι → ℕ) [∀ ℓ, NeZero (K ℓ)] (hd : 0 < d)
    (hK : ∀ ℓ, 2 ≤ K ℓ) (P : ι → Finset (Finset (Fin d → ℤ)))
    (Q : ι → Finset (Fin d → ℤ) → Prop) (sz : Finset (Fin d → ℤ) → ℕ)
    (τ : ι → Finset (Fin d → ℤ) → ℕ) (can : Finset (Fin d → ℤ) → ι) (D : Set G)
    (W : Submodule ℂ (G → ℂ)) (R : Finset (Fin d → ℤ) → Prop)
    (Ag : Finset (Fin d → ℤ) → G → G → Prop) (T : ι → G → Finset (Fin d → ℤ) → ℂ)
    (Wd : ι → Finset (Fin d → ℤ) → Prop)
    {B a κ κ₂ κ' lam : ℝ} {t₀ : ℕ}
    (hP : ∀ ℓ X, X ∈ P ℓ ↔ ∃ Y, IsAnimal (blockGraph d (K ℓ)) Y ∧
      X = Y.image (fun b μ => (b μ).valMinAbs))
    (hQ : ∀ ℓ X, Q ℓ X ↔ ∀ x ∈ X, ∀ μ, (x μ).natAbs ≤ K ℓ / 4)
    (hsz : ∀ X, sz X = X.card)
    (hτ : ∀ ℓ X, τ ℓ X = K ℓ / 4 - X.sup (fun x => Finset.univ.sup fun μ => (x μ).natAbs))
    (hR : ∀ ℓ X, X ∈ P ℓ → R X)
    (hAg : ∀ X Z, X ⊆ Z → ∀ g g', Ag Z g g' → Ag X g g')
    (hcanK : ∀ ℓ X, X ∈ P ℓ → Q ℓ X → K ℓ ≤ K (can X))
    (hWd : ∀ ℓ X, X ∈ P ℓ → Q ℓ X → Wd ℓ X → K ℓ ≤ 25 * X.card)
    (hB : 0 ≤ B) (ha : 0 ≤ a) (hκ : 0 ≤ κ)
    (hκ₂ : κ + Real.log 2 ≤ κ₂) (hlam : κ₂ ≤ lam) (hκ' : 7 * lam + κ₂ ≤ κ')
    (hsupp : ∀ ℓ X, X ∈ P ℓ → ¬ R X → ∀ g, T ℓ g X = 0)
    (hloc : ∀ ℓ X, X ∈ P ℓ → ∀ g g', Ag X g g' → T ℓ g X = T ℓ g' X)
    (han : ∀ ℓ X, X ∈ P ℓ → (fun g => T ℓ g X) ∈ W)
    (hbd : ∀ ℓ X, X ∈ P ℓ → ∀ g ∈ D, ‖T ℓ g X‖ ≤ B * Real.exp (-κ' * (sz X : ℝ)))
    (hFclose : ∀ ℓ X, X ∈ P ℓ → Q ℓ X → ¬ Wd ℓ X → t₀ ≤ τ ℓ X → ∀ g ∈ D,
      ‖T ℓ g X - T (can X) g X‖ ≤
        a * Real.exp (-lam * (τ ℓ X : ℝ)) * Real.exp (-κ₂ * (sz X : ℝ))) :
    ∃ Φ : ι → Finset (Fin d → ℤ) → Finset (Fin d → ℤ),
    ∃ Tn : ι → G → Finset (Fin d → ℤ) → ℂ,
      (∀ ℓ X, X ∈ P ℓ → Q ℓ X → X ⊆ Φ ℓ X) ∧
      (∀ ℓ g X, Tn ℓ g X = if Q ℓ X then T (can X) g X else
        T ℓ g X + ∑ X₀ ∈ ((P ℓ).filter (Q ℓ)).filter (fun X₀ => Φ ℓ X₀ = X),
          (T ℓ g X₀ - T (can X₀) g X₀)) ∧
      (∀ ℓ g, ∑ X ∈ P ℓ, Tn ℓ g X = ∑ X ∈ P ℓ, T ℓ g X) ∧
      (∀ ℓ ℓ' g X, Q ℓ X → Q ℓ' X → Tn ℓ g X = Tn ℓ' g X) ∧
      (∀ ℓ X, X ∈ P ℓ → ∀ g ∈ D, ‖Tn ℓ g X‖ ≤
        (B + (a + 2 * B) * Real.exp κ₂ + 2 * B * Real.exp (κ₂ * (t₀ : ℝ))) *
          Real.exp (-κ * (sz X : ℝ))) ∧
      (∀ ℓ X, X ∈ P ℓ → ¬ R X → ∀ g, Tn ℓ g X = 0) ∧
      (∀ ℓ X, X ∈ P ℓ → ∀ g g', Ag X g g' → Tn ℓ g X = Tn ℓ g' X) ∧
      (∀ ℓ X, X ∈ P ℓ → (fun g => Tn ℓ g X) ∈ W) := by
  obtain ⟨Φ, hsub, hΦP, hΦsz, hfib, hRΦ, hAgΦ⟩ :=
    lastScale_chain K hd hK P Q sz τ R Ag hP hQ hsz hτ hR hAg
  have hcanP : ∀ ℓ X, X ∈ P ℓ → Q ℓ X → X ∈ P (can X) := by
    intro ℓ X hX hQX
    obtain ⟨Y, hY, rfl⟩ := (hP ℓ _).1 hX
    have hbox : ∀ b ∈ Y, ∀ μ, (b μ).valMinAbs.natAbs ≤ K ℓ / 4 := fun b hb μ =>
      (hQ ℓ _).1 hQX _ (Finset.mem_image_of_mem _ hb) μ
    obtain ⟨Y', hY', h⟩ := quarterBox_polymer_larger (hK ℓ) (hcanK ℓ _ hX hQX) hY hbox
    exact (hP _ _).2 ⟨Y', hY', h.symm⟩
  have hκ₂0 : 0 ≤ κ₂ := by
    have : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    linarith
  have hlam0 : 0 ≤ lam := le_trans hκ₂0 hlam
  have hκκ' : κ₂ ≤ κ' := by linarith
  have hΦsz' : ∀ ℓ X, X ∈ P ℓ → Q ℓ X →
      sz (Φ ℓ X) ≤ sz X + (fun ℓ X => if Wd ℓ X then 7 * sz X else τ ℓ X) ℓ X + 1 := by
    intro ℓ X hX hQX
    by_cases hw : Wd ℓ X
    · simp only [hw, ↓reduceIte]
      have h1 := hΦsz ℓ X hX hQX
      have h2 := hWd ℓ X hX hQX hw
      have h3 : τ ℓ X ≤ 7 * sz X := by
        rw [hsz]
        refine margin_le_of_wide h2 ?_
        rw [hτ]; omega
      omega
    · simp only [hw, ↓reduceIte]
      exact hΦsz ℓ X hX hQX
  have hbd' : ∀ ℓ X, X ∈ P ℓ → ∀ g ∈ D, ‖T ℓ g X‖ ≤ B * Real.exp (-κ₂ * (sz X : ℝ)) := by
    intro ℓ X hX g hg
    refine (hbd ℓ X hX g hg).trans ?_
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hB
    have : (0 : ℝ) ≤ sz X := Nat.cast_nonneg _
    nlinarith
  have hcl : ∀ ℓ X, X ∈ P ℓ → Q ℓ X →
      t₀ ≤ (fun ℓ X => if Wd ℓ X then 7 * sz X else τ ℓ X) ℓ X → ∀ g ∈ D,
      ‖T ℓ g X - T (can X) g X‖ ≤ (a + 2 * B) *
        Real.exp (-lam * (((fun ℓ X => if Wd ℓ X then 7 * sz X else τ ℓ X) ℓ X : ℕ) : ℝ)) *
          Real.exp (-κ₂ * (sz X : ℝ)) := by
    intro ℓ X hX hQX ht g hg
    by_cases hw : Wd ℓ X
    · simp only [hw, ↓reduceIte] at ht ⊢
      have hc := hcanP ℓ X hX hQX
      have h1 := hbd ℓ X hX g hg
      have h2 := hbd (can X) X hc g hg
      have h3 : ‖T ℓ g X - T (can X) g X‖ ≤ 2 * B * Real.exp (-κ' * (sz X : ℝ)) := by
        calc ‖T ℓ g X - T (can X) g X‖ ≤ ‖T ℓ g X‖ + ‖T (can X) g X‖ := norm_sub_le _ _
          _ ≤ 2 * B * Real.exp (-κ' * (sz X : ℝ)) := by linarith
      refine h3.trans ?_
      have h4 : Real.exp (-κ' * (sz X : ℝ)) ≤
          Real.exp (-lam * ((7 * sz X : ℕ) : ℝ)) * Real.exp (-κ₂ * (sz X : ℝ)) := by
        rw [← Real.exp_add]
        refine Real.exp_le_exp.2 ?_
        push_cast
        have : (0 : ℝ) ≤ sz X := Nat.cast_nonneg _
        nlinarith
      have h5 : 0 ≤ Real.exp (-lam * ((7 * sz X : ℕ) : ℝ)) * Real.exp (-κ₂ * (sz X : ℝ)) := by
        positivity
      calc 2 * B * Real.exp (-κ' * (sz X : ℝ))
          ≤ 2 * B * (Real.exp (-lam * ((7 * sz X : ℕ) : ℝ)) * Real.exp (-κ₂ * (sz X : ℝ))) :=
            mul_le_mul_of_nonneg_left h4 (by positivity)
        _ ≤ (a + 2 * B) * (Real.exp (-lam * ((7 * sz X : ℕ) : ℝ)) *
            Real.exp (-κ₂ * (sz X : ℝ))) :=
            mul_le_mul_of_nonneg_right (by linarith) h5
        _ = (a + 2 * B) * Real.exp (-lam * ((7 * sz X : ℕ) : ℝ)) *
            Real.exp (-κ₂ * (sz X : ℝ)) := by ring
    · simp only [hw, ↓reduceIte] at ht ⊢
      refine (hFclose ℓ X hX hQX hw ht g hg).trans ?_
      have h5 : 0 ≤ Real.exp (-lam * (τ ℓ X : ℝ)) * Real.exp (-κ₂ * (sz X : ℝ)) := by
        positivity
      calc a * Real.exp (-lam * (τ ℓ X : ℝ)) * Real.exp (-κ₂ * (sz X : ℝ))
          = a * (Real.exp (-lam * (τ ℓ X : ℝ)) * Real.exp (-κ₂ * (sz X : ℝ))) := by ring
        _ ≤ (a + 2 * B) * (Real.exp (-lam * (τ ℓ X : ℝ)) * Real.exp (-κ₂ * (sz X : ℝ))) :=
            mul_le_mul_of_nonneg_right (by linarith) h5
        _ = (a + 2 * B) * Real.exp (-lam * (τ ℓ X : ℝ)) * Real.exp (-κ₂ * (sz X : ℝ)) := by ring
  obtain ⟨Tn, h⟩ := resum_lastScale P Q sz
    (fun ℓ X => if Wd ℓ X then 7 * sz X else τ ℓ X) Φ can D W R Ag T hB
    (a := a + 2 * B) (by positivity) hκ hκ₂ hlam hcanP hΦP hΦsz' (fun ℓ Z => by convert hfib ℓ Z)
    hRΦ hAgΦ hsupp hloc han hbd' hcl
  refine ⟨Φ, Tn, hsub, ?_⟩
  convert h

end Assembly

end Balaban.Polymer
