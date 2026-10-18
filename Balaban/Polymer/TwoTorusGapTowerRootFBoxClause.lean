/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusGapTowerSitesClause
public import Balaban.Polymer.TwoTorusGapTowerRootFBoxArith

/-!
# Root-F's index types on the exact quarter box (blocker 7)

`rootF_sites_of_cellClause_box`: `rootF_sites_of_cellClause` for `4 ∣ K ℓ`, with the cell-level clause
on the cell box `4 |y_μ| ≤ K` and the conclusion on Root-F's exact box `4 |y_μ| < D K` (no shrinking
by one block).
-/

@[expose] public section

noncomputable section

namespace Balaban.Polymer.TwoTorusStep

open Balaban Balaban.Polymer

open scoped Classical

section Clause

variable {ι G : Type*} {d D : ℕ} (K n : ι → ℕ) [∀ ℓ, NeZero (n ℓ)]

theorem rootF_sites_of_cellClause_box (hK2 : ∀ ℓ, 2 ≤ K ℓ) (h4 : ∀ ℓ, 4 ∣ K ℓ)
    (hn : ∀ ℓ, n ℓ = D * K ℓ) (Tn : (Fin d → ℤ) → ι → G → Finset (Fin d → ℤ) → ℂ)
    (hcl : ∀ a : Fin d → ℤ, (∀ ℓ μ, 4 * |a μ| ≤ (K ℓ : ℤ)) → ∀ ℓ ℓ' g (A : Finset (Fin d → ℤ)),
      a ∈ A → (∀ y ∈ A, ∀ μ, 4 * |y μ| ≤ (K ℓ : ℤ) ∧ 4 * |y μ| ≤ (K ℓ' : ℤ)) →
      Tn a ℓ g A = Tn a ℓ' g A) :
    ∃ Tf : ∀ ℓ, G → Torus d (n ℓ) → Finset (Torus d (n ℓ)) → ℂ,
      (∀ ℓ g x X, ¬ (x ∈ X ∧ IsPolymer d (n ℓ) D X) → Tf ℓ g x X = 0) ∧
      (∀ ℓ g x X, x ∈ X → IsPolymer d (n ℓ) D X →
        (∀ ℓ' μ, 4 * |(((x μ).val / D : ℕ) : ZMod (K ℓ)).valMinAbs| ≤ (K ℓ' : ℤ)) →
        Tf ℓ g x X = Tn (fun μ => (((x μ).val / D : ℕ) : ZMod (K ℓ)).valMinAbs) ℓ g
          (X.image fun x μ => (((x μ).val / D : ℕ) : ZMod (K ℓ)).valMinAbs)) ∧
      ∀ (ℓ ℓ' : ι) g (a : Fin d → ℤ) (A : Finset (Fin d → ℤ)), a ∈ A →
        (∀ ℓ'' μ, 4 * |a μ| < (n ℓ'' : ℤ)) →
        (∀ y ∈ A, ∀ μ, 4 * |y μ| < (n ℓ : ℤ) ∧ 4 * |y μ| < (n ℓ' : ℤ)) →
        Tf ℓ g (fun μ => ((a μ : ℤ) : ZMod (n ℓ)))
            (A.image fun y μ => ((y μ : ℤ) : ZMod (n ℓ))) =
          Tf ℓ' g (fun μ => ((a μ : ℤ) : ZMod (n ℓ')))
            (A.image fun y μ => ((y μ : ℤ) : ZMod (n ℓ'))) := by
  refine ⟨fun ℓ g x X => if (x ∈ X ∧ IsPolymer d (n ℓ) D X ∧
      ∀ ℓ' μ, 4 * |(((x μ).val / D : ℕ) : ZMod (K ℓ)).valMinAbs| ≤ (K ℓ' : ℤ)) then
      Tn (fun μ => (((x μ).val / D : ℕ) : ZMod (K ℓ)).valMinAbs) ℓ g
        (X.image fun x μ => (((x μ).val / D : ℕ) : ZMod (K ℓ)).valMinAbs) else 0,
    fun ℓ g x X h => ite_eq_right_of_eq_false _ _ (eq_false fun h' => h ⟨h'.1, h'.2.1⟩),
    fun ℓ g x X hx hp hb => ite_eq_left_of_eq_true _ _ (eq_true ⟨hx, hp, hb⟩), ?_⟩
  intro ℓ ℓ' g a A haA hab hA
  have hD : 0 < D :=
    Nat.pos_of_ne_zero (fun h0 => NeZero.ne (n ℓ) (by rw [hn ℓ, h0, zero_mul]))
  have hK4 : ∀ ℓ'', 4 ≤ K ℓ'' := fun ℓ'' =>
    Nat.le_of_dvd (by have := hK2 ℓ''; omega) (h4 ℓ'')
  have hfine : ∀ ℓ'' (y : ℤ), 4 * |y| < (n ℓ'' : ℤ) → 4 * |y| < (D : ℤ) * K ℓ'' := by
    intro ℓ'' y h
    rw [hn ℓ''] at h; push_cast at h; exact h
  have hc : ∀ ℓ'' μ, 4 * |a μ / (D : ℤ)| ≤ (K ℓ'' : ℤ) := fun ℓ'' μ =>
    four_abs_ediv_le hD (h4 ℓ'') (hfine ℓ'' _ (hab ℓ'' μ))
  have hcA : ∀ y ∈ A, ∀ μ, 4 * |y μ / (D : ℤ)| ≤ (K ℓ : ℤ) ∧ 4 * |y μ / (D : ℤ)| ≤ (K ℓ' : ℤ) :=
    fun y hy μ => ⟨four_abs_ediv_le hD (h4 ℓ) (hfine ℓ _ (hA y hy μ).1),
      four_abs_ediv_le hD (h4 ℓ') (hfine ℓ' _ (hA y hy μ).2)⟩
  have himg : ∀ ℓ'', (∀ y ∈ A, ∀ μ, 4 * |y μ| < (n ℓ'' : ℤ)) →
      (A.image fun y μ => ((y μ : ℤ) : ZMod (n ℓ''))).image
          (fun x μ => (((x μ).val / D : ℕ) : ZMod (K ℓ'')).valMinAbs) =
        A.image fun y μ => y μ / (D : ℤ) := by
    intro ℓ'' h
    rw [Finset.image_image]
    refine Finset.image_congr (fun y hy => ?_)
    funext μ
    exact cell_valMinAbs_quarter (hn ℓ'') hD (h4 ℓ'') (hfine ℓ'' _ (h y hy μ))
  have hpoly := isPolymer_image_cast_iff_of_quarter (hn ℓ) (hn ℓ') (hK4 ℓ) (hK4 ℓ') A
    (fun y hy μ => (hA y hy μ).1) (fun y hy μ => (hA y hy μ).2)
  simp only
  have hxa : ∀ ℓ'', (fun μ => (((((a μ : ℤ) : ZMod (n ℓ'')).val / D : ℕ)) :
      ZMod (K ℓ'')).valMinAbs) = fun μ => a μ / (D : ℤ) := fun ℓ'' => funext fun μ =>
    cell_valMinAbs_quarter (hn ℓ'') hD (h4 ℓ'') (hfine ℓ'' _ (hab ℓ'' μ))
  have hmem : ∀ ℓ'', (fun μ => ((a μ : ℤ) : ZMod (n ℓ''))) ∈
      A.image fun y μ => ((y μ : ℤ) : ZMod (n ℓ'')) := fun ℓ'' =>
    Finset.mem_image_of_mem _ haA
  by_cases hp : IsPolymer d (n ℓ) D (A.image fun y μ => ((y μ : ℤ) : ZMod (n ℓ)))
  · have hp' := hpoly.1 hp
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨hmem ℓ, hp, fun ℓ'' μ => by
        rw [congrFun (hxa ℓ) μ]; exact hc ℓ'' μ⟩),
      ite_eq_left_of_eq_true _ _ (eq_true ⟨hmem ℓ', hp', fun ℓ'' μ => by
        rw [congrFun (hxa ℓ') μ]; exact hc ℓ'' μ⟩),
      hxa, hxa, himg ℓ (fun y hy μ => (hA y hy μ).1), himg ℓ' (fun y hy μ => (hA y hy μ).2)]
    refine hcl _ (fun ℓ'' μ => hc ℓ'' μ) ℓ ℓ' g _ ?_ ?_
    · exact Finset.mem_image_of_mem _ haA
    · intro y hy μ
      obtain ⟨y0, hy0, rfl⟩ := Finset.mem_image.1 hy
      exact hcA y0 hy0 μ
  · have hp' : ¬ IsPolymer d (n ℓ') D (A.image fun y μ => ((y μ : ℤ) : ZMod (n ℓ'))) :=
      fun h => hp (hpoly.2 h)
    rw [ite_eq_right_of_eq_false _ _ (eq_false fun h => hp h.2.1),
      ite_eq_right_of_eq_false _ _ (eq_false fun h => hp' h.2.1)]

end Clause

end Balaban.Polymer.TwoTorusStep
