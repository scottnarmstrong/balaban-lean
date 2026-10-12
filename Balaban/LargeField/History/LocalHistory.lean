module

public import Balaban.LargeField.History.RegionLineage

/-!
# Localized histories and the gain clock (Part I, Definitions I.4.4, I.4.7 item 5)

* `rawLocalHistory`: the raw records of a history intersected with a component `Z` of `Z^pre_k` as
  fine sets (not the localized history; `localHistory` of `LocalRegion` is the lineage
  localization of Definition I.4.4); `historiesWithFinal k Z` is the set `𝔥_k(Z)` of admissible region
  histories whose pre-`R` region at scale `k` is `Z`, with `Z` as only component.
* `gain`: the gain clock `b(Z)` of Definition I.4.6: `b' = μ` if the component contains a new cube,
  otherwise the maximum of `b` over the old parts, where a kept ripe component has `b = k`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban

namespace RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ}
  (H : RegionHistory S n R k0)

/-- The fine set (a subset of the fine torus `𝕋_{M n_K L^K}`) of a set of cubes of `𝕋_j`. -/
def fineSet (M K j : ℕ) (A : Set (Torus S.d (n j))) : Set (Torus S.d (M * n K * S.L ^ K)) :=
  {x | cubeMap n S.L M K j x ∈ A}

/-- The records of a history restricted to a component, as fine sets (Definition I.4.4): for each
scale the region `Z_j`, the new cubes `P, Q, R, S` (`Sset`) of the step into scale `j+1` and the derived
sets, all intersected with the fine set of `Z`. -/
structure LocalHistory (S : Setting) (n : ℕ → ℕ) (M K : ℕ) where
  Z : ℕ → Set (Torus S.d (M * n K * S.L ^ K))
  P : ℕ → Set (Torus S.d (M * n K * S.L ^ K))
  Q : ℕ → Set (Torus S.d (M * n K * S.L ^ K))
  R : ℕ → Set (Torus S.d (M * n K * S.L ^ K))
  Sset : ℕ → Set (Torus S.d (M * n K * S.L ^ K))
  OmegaPrime : ℕ → Set (Torus S.d (M * n K * S.L ^ K))
  Omega : ℕ → Set (Torus S.d (M * n K * S.L ^ K))
  OmegaDD : ℕ → Set (Torus S.d (M * n K * S.L ^ K))

/-- The *raw* records of a history intersected with the fine set of a component `Z` of `Z^pre_k`.
It can contain records of components removed below `Z` (when later cubes re-cover their fine
sites), so it is not the localized history; see `localHistory` in `LocalRegion`, which contains
no such records and is contained in it. -/
def rawLocalHistory (M K k : ℕ) (Z : H.Comp k) : LocalHistory S n M K where
  Z j := fineSet (S := S) (n := n) M K j (H.step j).Z ∩ fineSet M K k Z.1
  P j := fineSet M K (j + 1) (H.step j).P ∩ fineSet M K k Z.1
  Q j := fineSet M K (j + 1) (H.step j).Q ∩ fineSet M K k Z.1
  R j := fineSet M K (j + 1) (H.step j).R ∩ fineSet M K k Z.1
  Sset j := fineSet M K (j + 1) (H.step j).S ∩ fineSet M K k Z.1
  OmegaPrime j := fineSet M K (j + 1) (H.step j).OmegaPrime ∩ fineSet M K k Z.1
  Omega j := fineSet M K (j + 1) (H.step j).Omega ∩ fineSet M K k Z.1
  OmegaDD j := fineSet M K (j + 1) (H.step j).OmegaDD ∩ fineSet M K k Z.1

/-- `𝔥_k(Z)`: the admissible region histories (on the same tori) whose pre-`R` region at scale `k`
is `Z` and has `Z` as its only component. -/
def historiesWithFinal (k : ℕ) (Z : Finset (Torus S.d (n k))) : Set (RegionHistory S n R k0) :=
  {H' | H'.Admissible ∧ H'.F.Zp k = Z ∧ comps (S.omega k) Z = {Z}}

open Classical in
/-- The gain clock `b(Z)` (Definition I.4.6): the scale of the last new cube or kept `R` event
in the history of `Z` (Definition I.4.7 item 5). -/
noncomputable def gain : ∀ k, H.Comp k → ℕ
  | 0 => fun _ => 0
  | k + 1 => fun Z' =>
      if (Z'.1 ∩ H.newCubes (k + 1)).Nonempty then k + 1
      else (H.parts k Z').sup fun c =>
        if 1 ≤ k ∧ k ≤ k0 ∧ S.Ripe k (H.bk k c) then k else gain k c

theorem gain_le : ∀ k (Z : H.Comp k), H.gain k Z ≤ k := by
  classical
  intro k
  induction k with
  | zero => intro Z; simp [gain]
  | succ k ih =>
    intro Z'
    unfold gain
    split_ifs with h
    · exact le_rfl
    · refine (Finset.sup_le fun c _ => ?_).trans (Nat.le_succ k)
      split_ifs
      · exact le_rfl
      · exact ih c

theorem gain_of_new (k : ℕ) (Z' : H.Comp (k + 1)) (h : (Z'.1 ∩ H.newCubes (k + 1)).Nonempty) :
    H.gain (k + 1) Z' = k + 1 := by
  classical
  unfold gain; rw [ite_eq_left h]

end RegionHistory

end Balaban.LargeField
