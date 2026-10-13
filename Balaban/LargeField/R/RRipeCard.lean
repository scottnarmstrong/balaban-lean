module

public import Balaban.LargeField.R.ChainCount
public import Balaban.LargeField.R.RipeBox
public import Balaban.LargeField.History.FlowBook
import Mathlib.Tactic.Linarith

/-!
# Removed components are small boxes (cardinality and diameter)

The large-field operation `R^{(k)}` removes the *ripe* components of `Z^pre_k`
(Definition I.4.1, `RegionHistory.Admissible`).  A ripe component has the geometric window of
Part III, Lemma III.1.2 (`RegionHistory.ripe_window`), and its `Z_k` is one box of side at most
`crit_k = 2ρ_k + 10` scale-`k` cubes in every direction (`RipeWindow.lin_eq_box`).  This file
states the consequences for a *removed* component `c ∈ Rem_k`, in the form the cover-extension
estimate of `notes/phase1/VMOD-37.md` §2 (OPEN-R-FINE-EXTRA) will consume:

* `removed_ripe`: a removed component is ripe, `1 ≤ k ≤ k₀`;
* `removed_ripeWindow`: it has the window `RipeWindow`;
* `removed_eq_box`, `removed_card_le`: it is a box with sides in `[1, crit_k]`, so it has at most
  `crit_k ^ d` cubes;
* `removed_supDist_lt`: any two of its cubes are at torus sup-distance `< crit_k` (scale-`k`
  cube units);
* `removed_sep`: two distinct components of `Z^pre_k` are at sup-distance `≥ ω_k`;
* `coverIdx`, `card_coverIdx_le`, `removed_coverIdx_card_le`: the number of block positions
  (aligned groups of `L` cubes per direction, the `π'_k`-boxes in cube-index units) meeting a
  box of side `s` is at most `∏ (s_i + L - 1)`, hence at most `(crit_k + 2L)^d`.

NOT proved here: the cover-extension estimate (2) of VMOD-37 itself, the charge inequality (3),
and everything analytic about `R`.  This file is pure finite geometry.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban

namespace RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}
  {H : RegionHistory S n R k0 K}

/-- A removed component is ripe (this is the admissibility `H.Admissible`), and the scale `k`
satisfies `1 ≤ k ≤ k₀` because `Rem_k = ∅` otherwise. -/
theorem removed_ripe (hadm : H.Admissible) {k : ℕ} {c : H.Comp k} (hc : c.1 ∈ H.rem k) :
    S.Ripe k (H.bk k c) ∧ 1 ≤ k ∧ k ≤ k0 := by
  refine ⟨hadm k c hc, ?_, ?_⟩
  · by_contra h
    have : k = 0 := by omega
    rw [H.rem_empty k (Or.inl this)] at hc
    exact Finset.notMem_empty _ hc
  · by_contra h
    rw [H.rem_empty k (Or.inr (by omega))] at hc
    exact Finset.notMem_empty _ hc

/-- A removed component has the geometric window of Lemma III.1.2. -/
theorem removed_ripeWindow (G : S.Good)
    (hT : ∀ j, 1 ≤ j → j ≤ k0 → 4 * S.rho j + 21 ≤ n j) (hadm : H.Admissible) {k : ℕ}
    (hkK : k ≤ K) {c : H.Comp k} (hc : c.1 ∈ H.rem k) : H.RipeWindow k c := by
  obtain ⟨hr, -, hk0⟩ := removed_ripe hadm hc
  exact ripe_window G hT hk0 hkK hr

/-- **A removed component is one box** of sides in `[1, crit_k]`, `crit_k = 2ρ_k + 10`. -/
theorem removed_eq_box (G : S.Good)
    (hT : ∀ j, 1 ≤ j → j ≤ k0 → 4 * S.rho j + 21 ≤ n j) (hadm : H.Admissible) {k : ℕ}
    (hkK : k ≤ K) {c : H.Comp k} (hc : c.1 ∈ H.rem k) :
    ∃ (a : Torus S.d (n k)) (sd : Fin S.d → ℕ),
      (c.1 : Set (Torus S.d (n k))) = box a sd ∧ ∀ i, 1 ≤ sd i ∧ sd i ≤ S.crit k := by
  obtain ⟨-, hk1, hk0⟩ := removed_ripe hadm hc
  have W := removed_ripeWindow G hT hadm hkK hc
  obtain ⟨-, hcov, -⟩ := W.unique_box k c W.point.2.2.le (Desc.refl c)
  exact comp_eq_box_of_covered hk1 hk0 (hT k hk1 hk0) c hcov

/-- **Cardinality**: a removed component has at most `crit_k ^ d = (2ρ_k + 10)^d` cubes
(`Set.ncard` form). -/
theorem removed_ncard_le (G : S.Good)
    (hT : ∀ j, 1 ≤ j → j ≤ k0 → 4 * S.rho j + 21 ≤ n j) (hadm : H.Admissible) {k : ℕ}
    (hkK : k ≤ K) {c : H.Comp k} (hc : c.1 ∈ H.rem k) :
    (c.1 : Set (Torus S.d (n k))).ncard ≤ (2 * S.rho k + 10) ^ S.d := by
  obtain ⟨a, sd, hbox, hsd⟩ := removed_eq_box G hT hadm hkK hc
  rw [hbox]
  refine (ncard_box_le a sd).trans ?_
  calc ∏ i, sd i ≤ ∏ _i : Fin S.d, S.crit k := by
        apply Finset.prod_le_prod
        intro i _; exact (hsd i).2
    _ = (2 * S.rho k + 10) ^ S.d := by simp [Setting.crit]

/-- **Cardinality** (`Finset.card` form). -/
theorem removed_card_le (G : S.Good)
    (hT : ∀ j, 1 ≤ j → j ≤ k0 → 4 * S.rho j + 21 ≤ n j) (hadm : H.Admissible) {k : ℕ}
    (hkK : k ≤ K) {c : H.Comp k} (hc : c.1 ∈ H.rem k) :
    c.1.card ≤ (2 * S.rho k + 10) ^ S.d := by
  have := removed_ncard_le G hT hadm hkK hc
  rwa [Set.ncard_coe_finset] at this

end RegionHistory

/-- Two points of a box of sides `≤ m` are at torus sup-distance `< m` (`0 < m`). -/
theorem supDist_lt_of_mem_box {d n : ℕ} [NeZero n] {a x y : Torus d n} {sd : Fin d → ℕ} {m : ℕ}
    (hm : 0 < m) (hsd : ∀ i, sd i ≤ m) (hx : x ∈ box a sd) (hy : y ∈ box a sd) :
    supDist x y < m := by
  have : supDist x y ≤ m - 1 := by
    rw [supDist_le_iff]
    intro i
    obtain ⟨j, hj, hxj⟩ := hx i
    obtain ⟨j', hj', hyj⟩ := hy i
    rw [cycNorm_le_iff]
    refine ⟨(j : ℤ) - j', ?_, ?_⟩
    · have h1 := hsd i
      rw [abs_le]
      constructor <;> omega
    · rw [hxj, hyj]; push_cast; ring
  omega

namespace RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}
  {H : RegionHistory S n R k0 K}

/-- **Diameter**: any two cubes of a removed component are at torus sup-distance `< crit_k`,
in units of scale-`k` cubes (`supDist` on `Torus d (n k)`). -/
theorem removed_supDist_lt (G : S.Good)
    (hT : ∀ j, 1 ≤ j → j ≤ k0 → 4 * S.rho j + 21 ≤ n j) (hadm : H.Admissible) {k : ℕ}
    (hkK : k ≤ K) {c : H.Comp k} (hc : c.1 ∈ H.rem k) {x y : Torus S.d (n k)}
    (hx : x ∈ c.1) (hy : y ∈ c.1) : supDist x y < 2 * S.rho k + 10 := by
  obtain ⟨a, sd, hbox, hsd⟩ := removed_eq_box G hT hadm hkK hc
  have hx' : x ∈ box a sd := hbox ▸ (Finset.mem_coe.mpr hx)
  have hy' : y ∈ box a sd := hbox ▸ (Finset.mem_coe.mpr hy)
  exact supDist_lt_of_mem_box (m := 2 * S.rho k + 10) (by omega) (fun i => (hsd i).2) hx' hy'

/-- **Separation**: two distinct components of `Z^pre_k` are at torus sup-distance `≥ ω_k`
(Lemma I.2.12 (a)); in particular so are two distinct removed components. -/
theorem comp_sep {k : ℕ} {c c' : H.Comp k} (hne : c ≠ c') {x y : Torus S.d (n k)}
    (hx : x ∈ c.1) (hy : y ∈ c'.1) : S.omega k ≤ supDist x y :=
  comps_sep c.2 c'.2 (fun h => hne (Subtype.ext h)) hx hy

end RegionHistory

end Balaban.LargeField
