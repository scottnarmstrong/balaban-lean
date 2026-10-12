/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.DecEquivCoef
public import Balaban.Localization.Telescope

/-!
# The coefficients `F_C` under a relabelling of the parameters

The coefficient `coef F C` is determined by the values of `F` at the points `1_A` (`A ⊆ ι`):
`F(1_A) = ∑_{C ⊆ A} F_C` (`sum_coef_unit`, the telescoping identity applied to the family `A`), and
this system of identities determines the coefficients recursively (`eq_of_sum_powerset_eq`).
Hence a bijection `κ : ι ≃ ι'` with `F'(s') = F(s' ∘ κ)` at the points `1_A` transports the
coefficients: `F'_{κ C} = F_C` (`coef_relabel`).  No commutation of derivatives or Fubini is needed.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban.Analysis

section Relabel

variable {ι ι' : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq ι'] [Fintype ι']

/-- The indicator point `1_A` of a set of parameters. -/
def indic (A : Finset ι) : ι → ℂ := fun j => if j ∈ A then 1 else 0

omit [Fintype ι] in
theorem indic_mem_unitCube (A : Finset ι) : indic A ∈ unitCube ι := fun j => by
  by_cases h : j ∈ A <;> simp [indic, h]

/-- **`F(1_A) = ∑_{C ⊆ A} F_C`.** -/
theorem sum_coef_unit {R : ℝ} (hR : 1 < R) {f : (ι → ℂ) → ℂ}
    (hf : AnalyticOnNhd ℂ f (polydisc (0 : ι → ℂ) (fun _ => R))) (A : Finset ι) :
    f (indic A) = ∑ C ∈ A.powerset, coef f C := by
  classical
  have h := telescope hR (Finset.univ.toList.filter (· ∈ A)) (nodup_filter_toList A) hf
    (s := indic A) (indic_mem_unitCube A) (fun j hj => by
      have := mem_filter_toList.mp hj
      simp [indic, this])
  rw [h, toFinset_filter_toList]
  refine Finset.sum_congr rfl fun C hC => ?_
  have hCA : C ⊆ A := Finset.mem_powerset.1 hC
  have hl : (Finset.univ.toList.filter (· ∈ A)).filter (· ∈ C) = Finset.univ.toList.filter (· ∈ C) := by
    rw [List.filter_filter]
    refine List.filter_congr fun x _ => ?_
    by_cases hx : x ∈ C
    · simp [hx, hCA hx]
    · simp [hx]
  rw [hl]
  unfold coef
  refine iterInt_congr_off _ fun j hj => ?_
  have hjC : j ∉ C := fun h => hj (mem_filter_toList.mpr h)
  by_cases hjA : j ∈ A
  · simp [zeroOn, hjA, hjC]
  · simp [zeroOn, indic, hjA]

omit [Fintype ι] in
/-- A function on finite subsets is determined by its sums over the powersets. -/
theorem eq_of_sum_powerset_eq {g h : Finset ι → ℂ}
    (hgh : ∀ A : Finset ι, ∑ C ∈ A.powerset, g C = ∑ C ∈ A.powerset, h C) (A : Finset ι) :
    g A = h A := by
  induction A using Finset.strongInduction with
  | H A ih =>
    have e := hgh A
    rw [← Finset.add_sum_erase _ _ (Finset.mem_powerset_self A),
      ← Finset.add_sum_erase _ _ (Finset.mem_powerset_self A)] at e
    have : ∑ C ∈ A.powerset.erase A, g C = ∑ C ∈ A.powerset.erase A, h C :=
      Finset.sum_congr rfl fun C hC => by
        obtain ⟨hne, hsub⟩ := Finset.mem_erase.1 hC
        exact ih C (Finset.ssubset_iff_subset_ne.2 ⟨Finset.mem_powerset.1 hsub, hne⟩)
    rw [this] at e
    exact add_right_cancel e

/-- **The coefficients are transported by a relabelling of the parameters.** -/
theorem coef_relabel {R : ℝ} (hR : 1 < R) (κ : ι ≃ ι') {f : (ι → ℂ) → ℂ} {f' : (ι' → ℂ) → ℂ}
    (hf : AnalyticOnNhd ℂ f (polydisc (0 : ι → ℂ) (fun _ => R)))
    (hf' : AnalyticOnNhd ℂ f' (polydisc (0 : ι' → ℂ) (fun _ => R)))
    (hff : ∀ s ∈ unitCube ι', f' s = f (s ∘ κ)) (C : Finset ι) :
    coef f' (C.map κ.toEmbedding) = coef f C := by
  refine eq_of_sum_powerset_eq (g := fun C => coef f' (C.map κ.toEmbedding)) (h := fun C => coef f C)
    (fun A => ?_) C
  have h1 : ∑ C ∈ A.powerset, coef f' (C.map κ.toEmbedding) =
      ∑ C' ∈ (A.map κ.toEmbedding).powerset, coef f' C' := by
    refine Finset.sum_nbij' (fun C => C.map κ.toEmbedding) (fun C' => C'.map κ.symm.toEmbedding)
      (fun C hC => ?_) (fun C' hC' => ?_) (fun C _ => ?_) (fun C' _ => ?_) (fun C _ => rfl)
    · exact Finset.mem_powerset.2 (Finset.map_subset_map.2 (Finset.mem_powerset.1 hC))
    · refine Finset.mem_powerset.2 fun j hj => ?_
      obtain ⟨i, hi, rfl⟩ := Finset.mem_map.1 hj
      have := Finset.mem_powerset.1 hC' hi
      obtain ⟨a, ha, rfl⟩ := Finset.mem_map.1 this
      simpa using ha
    · ext j; simp
    · ext j; simp
  rw [h1, ← sum_coef_unit hR hf', ← sum_coef_unit hR hf, hff _ (indic_mem_unitCube _)]
  congr 1
  funext j
  simp [indic, Function.comp]

end Relabel

end Balaban.Localization
