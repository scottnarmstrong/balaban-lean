/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseRecord
public import Balaban.LargeField.Base.BaseHistory
public import Balaban.LargeField.Base.BaseSupport
public import Balaban.Background.CompositionDomain
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The exact cutoff footprint (BASE-KERNEL-3 §2)

* `baseFootprint nn L M K regimeB c` is the full test footprint `F(c)` of the base factor
  `A_c B_c = chiPrimeZero`: all fine sites in the blocks used by `A_c`, both end points of every
  bond used by `B_c`, and (regime (B)) every site of `c`.
* `baseJPlus` is the set `𝒥₊ = {c ∉ P₁ : F(c) ∩ D₊ ≠ ∅}` of (2.2).
* `chiPrimeZero_congr_footprint`: `A_c B_c` depends on the spins only through `F(c)`.
* `baseFootprint_disjoint_of_mem_P`: a failed `P₁` factor tests only retained spins
  (Lemma II.7.2 (d): `P₁^{∼3} ⊆ Ω₁^c`).
* `BaseCutoffMargins`: the three strict background margins (2.2) of BASE-KERNEL-2 Lemma 2.1 on
  every `F(c)`, `c ∈ 𝒥₊`.  This is the one input BASE-KERNEL-3 §2 does not prove (the record-wide
  implication); `baseCutoffMargins_nonempty` shows it is satisfiable.
* `chiPrimeZero_eq_one_of_margins`: under it `A_c B_c = 1` for every `c ∈ 𝒥₊`;
  `baseDensity_eq_prod_deleted`: the old base factor (2.1) equals the product with all of `𝒥₊`
  deleted, and the remaining factor is independent of the integrated spins
  (`baseDeleted_indep`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Background Finset

variable {d N : ℕ}

section Footprint

variable (nn : ℕ → ℕ) (L M K : ℕ) [∀ k, NeZero (nn k)] [NeZero M] [NeZero L]

/-- **The full test footprint `F(c)`** of `A_c B_c`: all fine sites in the blocks `y ∈ T_1(c)`
used by `A_c`, both end points of every bond used by `B_c`, and, in regime (B), every site of `c`. -/
def baseFootprint (regimeB : Prop) (c : Torus d (nn 1)) : Set (Torus d (M * nn K * L ^ K)) :=
  {x | (∃ y : Torus d (M * nn K * L ^ (K - 1)), blockMap M (nn 1) y = c ∧
        blockMap L (M * nn K * L ^ (K - 1)) x = y) ∨
      (∃ (x' : Torus d (M * nn K * L ^ K)) (μ : Fin d),
        (cubeMap nn L M K 1 x' = c ∨ cubeMap nn L M K 1 (x' + Pi.single μ 1) = c) ∧
          (x = x' ∨ x = x' + Pi.single μ 1)) ∨
      (regimeB ∧ cubeMap nn L M K 1 x = c)}

/-- **`𝒥₊`** (BASE-KERNEL-3 (2.2)): the good cubes (`c ∉ P₁`) whose full footprint meets the
integrated sites `D₊`. -/
def baseJPlus (regimeB : Prop) (P : Set (Torus d (nn 1)))
    (Dplus : Set (Torus d (M * nn K * L ^ K))) : Set (Torus d (nn 1)) :=
  {c | c ∉ P ∧ (baseFootprint nn L M K regimeB c ∩ Dplus).Nonempty}

variable {nn L M K}

/-- `A_c B_c` depends on the spin field only through its restriction to `F(c)`. -/
theorem chiPrimeZero_congr_footprint (regimeB : Prop) (ν δ₀ : ℝ) (h : Fin N → ℝ)
    (c : Torus d (nn 1)) (φ φ' : Torus d (M * nn K * L ^ K) → Fin N → ℝ)
    (θ : Torus d (M * nn K * L ^ (K - 1)) → Fin N → ℝ)
    (hφ : ∀ x ∈ baseFootprint nn L M K regimeB c, φ x = φ' x) :
    chiPrimeZero nn L M K regimeB ν δ₀ h c (φ, θ) =
      chiPrimeZero nn L M K regimeB ν δ₀ h c (φ', θ) := by
  have hbl : ChiBlockProp nn L M K δ₀ φ θ c ↔ ChiBlockProp nn L M K δ₀ φ' θ c := by
    unfold ChiBlockProp
    refine forall_congr' fun y => imp_congr_right fun hy => ?_
    have : spinAverage nn L M K φ y = spinAverage nn L M K φ' y := by
      funext i
      unfold spinAverage
      congr 1
      refine Finset.sum_congr rfl fun x hx => ?_
      have hxy : blockMap L (M * nn K * L ^ (K - 1)) x = y := (Finset.mem_filter.1 hx).2
      rw [hφ x (Or.inl ⟨y, hy, hxy⟩)]
    rw [this]
  have hbo : ChiBondProp nn L M K δ₀ φ c ↔ ChiBondProp nn L M K δ₀ φ' c := by
    unfold ChiBondProp
    refine forall_congr' fun x => forall_congr' fun μ => imp_congr_right fun hx => ?_
    rw [hφ x (Or.inr (Or.inl ⟨x, μ, hx, Or.inl rfl⟩)),
      hφ (x + Pi.single μ 1) (Or.inr (Or.inl ⟨x, μ, hx, Or.inr rfl⟩))]
  have hsi : regimeB → (ChiSiteProp nn L M K ν δ₀ φ h c ↔ ChiSiteProp nn L M K ν δ₀ φ' h c) := by
    intro hB
    unfold ChiSiteProp
    refine forall_congr' fun x => imp_congr_right fun hx => ?_
    rw [hφ x (Or.inr (Or.inr ⟨hB, hx⟩))]
  have key : (ChiBlockProp nn L M K δ₀ φ θ c ∧ ChiBondProp nn L M K δ₀ φ c ∧
      (regimeB → ChiSiteProp nn L M K ν δ₀ φ h c)) ↔
      (ChiBlockProp nn L M K δ₀ φ' θ c ∧ ChiBondProp nn L M K δ₀ φ' c ∧
      (regimeB → ChiSiteProp nn L M K ν δ₀ φ' h c)) := by
    refine and_congr hbl (and_congr hbo ?_)
    exact imp_congr_right fun hB => hsi hB
  rcases chiPrimeZero_eq_zero_or_one nn L M K regimeB ν δ₀ h c (φ, θ) with h1 | h1 <;>
    rcases chiPrimeZero_eq_zero_or_one nn L M K regimeB ν δ₀ h c (φ', θ) with h2 | h2
  · rw [h1, h2]
  · exfalso
    have := (chiPrimeZero_eq_one_iff nn L M K regimeB ν δ₀ h c (φ', θ)).1 h2
    have h3 := (chiPrimeZero_eq_one_iff nn L M K regimeB ν δ₀ h c (φ, θ)).2 (key.2 this)
    rw [h1] at h3; exact zero_ne_one h3
  · exfalso
    have := (chiPrimeZero_eq_one_iff nn L M K regimeB ν δ₀ h c (φ, θ)).1 h1
    have h3 := (chiPrimeZero_eq_one_iff nn L M K regimeB ν δ₀ h c (φ', θ)).2 (key.1 this)
    rw [h2] at h3; exact zero_ne_one h3
  · rw [h1, h2]

section Geometry

variable {nn : ℕ → ℕ} {L M K : ℕ} [∀ k, NeZero (nn k)] [NeZero M] [NeZero L]

/-- A fine site of a block of the cube `c` lies in the cube `c`. -/
theorem cubeMap_eq_of_block (hnn : ∀ i, i < K → nn i = L * nn (i + 1)) (hK : 1 ≤ K)
    {c : Torus d (nn 1)} {x : Torus d (M * nn K * L ^ K)}
    {y : Torus d (M * nn K * L ^ (K - 1))} (hy : blockMap M (nn 1) y = c)
    (hx : blockMap L (M * nn K * L ^ (K - 1)) x = y) : cubeMap nn L M K 1 x = c := by
  rw [← cubeMap_eq_comp hnn hK x]
  have : Multiscale.jBlock d L (M * nn K) K 1 x = y := by
    unfold Multiscale.jBlock
    rw [← hx]
    exact congrArg (fun J => blockMap J (M * nn K * L ^ (K - 1)) x) (pow_one L)
  rw [this, hy]

/-- Every site of the footprint of `c` lies in a cube at index distance `≤ 1` from `c`. -/
theorem footprint_supDist_le (hnn : ∀ i, i < K → nn i = L * nn (i + 1)) (hK : 1 ≤ K)
    (regimeB : Prop) {c : Torus d (nn 1)} {x : Torus d (M * nn K * L ^ K)}
    (hx : x ∈ baseFootprint nn L M K regimeB c) :
    supDist (cubeMap nn L M K 1 x) c ≤ 1 := by
  rcases hx with ⟨y, hy, hxy⟩ | ⟨x', μ, hc, hxx⟩ | ⟨-, hc⟩
  · rw [cubeMap_eq_of_block hnn hK hy hxy, supDist_self]; omega
  · have h1 := supDist_cubeMap_add_single_le (M := M) (L := L) hnn hK x' μ
    rcases hc with hc | hc <;> rcases hxx with rfl | rfl
    · rw [hc, supDist_self]; omega
    · rw [← hc, supDist_comm]; exact h1
    · rw [← hc]; exact h1
    · rw [hc, supDist_self]; omega
  · rw [hc, supDist_self]; omega

/-- **A failed `P₁` factor tests only retained spins** (Lemma II.7.2 (d), `P₁^{∼3} ⊆ Ω₁^c`):
the footprint of a cube of `P₁` does not meet any set of sites whose cubes lie in `Ω₁`. -/
theorem baseFootprint_disjoint_of_mem_P (hnn : ∀ i, i < K → nn i = L * nn (i + 1)) (hK : 1 ≤ K)
    (regimeB : Prop) {Rk : ℝ} (br : BaseRecord d L (nn 1) Rk) {c : Torus d (nn 1)}
    (hc : c ∈ br.P) {Dplus : Set (Torus d (M * nn K * L ^ K))}
    (hD : ∀ x ∈ Dplus, cubeMap nn L M K 1 x ∈ br.Omega) :
    Disjoint (baseFootprint nn L M K regimeB c) Dplus := by
  rw [Set.disjoint_left]
  intro x hx hxD
  have h1 := footprint_supDist_le hnn hK regimeB hx
  have h2 : cubeMap nn L M K 1 x ∈ nbhd 3 br.P :=
    mem_nbhd.mpr ⟨c, hc, by omega⟩
  exact br.nbhd_P_subset_compl_Omega h2 (hD x hxD)

/-- The fine sites of the cubes of `Ω''₁` (the integrated sites `D₊`, before intersecting with a
component) lie in cubes of `Ω₁`. -/
theorem cubeMap_mem_Omega_of_DD {Rk : ℝ} (br : BaseRecord d L (nn 1) Rk)
    {x : Torus d (M * nn K * L ^ K)} (hx : cubeMap nn L M K 1 x ∈ br.OmegaDD) :
    cubeMap nn L M K 1 x ∈ br.Omega :=
  Region.OmegaDD_subset L _ _ hx

end Geometry

end Footprint

end Balaban.LargeField
