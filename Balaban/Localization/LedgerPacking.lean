/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.LedgerCounter
public import Balaban.Localization.GraphGmCount
public import Balaban.Localization.P6PairOp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Packing bound for the ledger of an actual cover (VMOD-23 (2.1)-(2.5))

Source: `notes/phase1/VMOD-23.md` §1-§2, P3 (4.50)-(4.52), P6 (4.29)-(4.34).

* `cubeIdx_layer_unique` (T1): a point carries at most one layer index in `cubeIdx G`;
  `p6FsharpC_cubeIdx_layer_unique` specializes to the common cover of the P6 pair, and
  `ledgerFamily_not_in_one_cover` says W209's family is not a family of index sets of one cover.
* `card_idx_in_cells_le` (T2, (2.1)): `|V_R| ≤ A′ |R|`, `A′ = (L^{m₀})^d`.
* `sum_exp_card_le`, `sum_exp_card_le_idx` (T3, (2.2)).
* `fixed_support_sum_of_candidates` (T4, (2.3)-(2.5)): conditional on the open candidate-region
  bound `|R| ≤ c₀ + c₁ D` (OPEN-P6-CANDIDATE-REGION).
* T5, consistency: for a fixed ledger the landed `boundary_gm3_fixed_Y_rate` gives `≤ 1`
  (`singleton_fiber_landed_bound`); over all ledgers inside a fixed candidate set T3 gives
  `≤ exp(|V| e^{-κ₂})`; for the ABSTRACT record `no_uniform_fiber_constant` shows no bound holds.
  These do not conflict: `ledgerFamily_sum_le` instantiates T3 at the singleton family.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Finset

section Unique

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}

/-- **T1.** The layers of a cover's generating set are disjoint, so a point `y` is a base of
cube indices in at most one layer. -/
theorem cubeIdx_layer_unique (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) {j j' : ℕ}
    {y : CTorus d L N₁ m₁ K} (h : (j, y) ∈ cubeIdx G) (h' : (j', y) ∈ cubeIdx G) : j = j' := by
  by_contra hne
  obtain ⟨⟨h1, hK⟩, hl, -⟩ := (mem_cubeIdx G).1 h
  obtain ⟨⟨h1', hK'⟩, hl', -⟩ := (mem_cubeIdx G).1 h'
  exact G.layer_disjoint h1 hK h1' hK' hne hl hl'

/-- **T1 corollary.** W209's family `{{(j,0)} : 1 ≤ j ≤ J}`, `J ≥ 2`, is not a family of subsets
of the cube index set of one cover: abstract record ⇒ unbounded
(`no_uniform_fiber_constant`), actual cover ⇒ excluded. -/
theorem ledgerFamily_not_in_one_cover (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) {J : ℕ}
    (hJ : 2 ≤ J) :
    ¬ ∀ C ∈ ledgerFamily (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) J,
        C ⊆ cubeIdx G := by
  intro h
  have h1 := h {((1, 0) : ℕ × CTorus d L N₁ m₁ K)} (mem_ledgerFamily.2 ⟨1, le_rfl, by omega, rfl⟩)
    (Finset.mem_singleton_self _)
  have h2 := h {((2, 0) : ℕ × CTorus d L N₁ m₁ K)} (mem_ledgerFamily.2 ⟨2, by omega, hJ, rfl⟩)
    (Finset.mem_singleton_self _)
  have := cubeIdx_layer_unique G h1 h2
  omega

end Unique

section P6

open Balaban.LargeField

variable {d M1 c n1 L k n0 m₁ : ℕ} [NeZero L] [NeZero M1] [NeZero c] [NeZero n0] [NeZero n1]

/-- **T1 for the P6 common cover** `p6FsharpC`. -/
theorem p6FsharpC_cubeIdx_layer_unique (hn : n0 = L * n1) {ρ' : ℕ} (hρ : 3 * L ≤ ρ')
    (hc : 5 ≤ c) (Z : Set (Torus d n0)) (hM1 : M1 = L ^ m₁) {j j' : ℕ}
    {y : CTorus d L (c * n1) m₁ (k + 1)}
    (h : (j, y) ∈ cubeIdx (p6FsharpC (k := k) (m₁ := m₁) hn hρ hc Z hM1))
    (h' : (j', y) ∈ cubeIdx (p6FsharpC (k := k) (m₁ := m₁) hn hρ hc Z hM1)) : j = j' :=
  cubeIdx_layer_unique _ h h'

end P6

section Packing

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}

open Classical in
/-- `V_R`: the cube indices of the cover whose layer cell lies in `R`. -/
noncomputable def idxInCells (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) (m₀ : ℕ)
    (R : Finset (ℕ × CTorus d L N₁ m₁ K)) : Finset (ℕ × CTorus d L N₁ m₁ K) :=
  (cubeIdx G).filter fun P => cellOfCube (L := L) m₀ m₁ P ∈ R

theorem mem_idxInCells {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {m₀ : ℕ}
    {R : Finset (ℕ × CTorus d L N₁ m₁ K)} {P : ℕ × CTorus d L N₁ m₁ K} :
    P ∈ idxInCells G m₀ R ↔ P ∈ cubeIdx G ∧ cellOfCube (L := L) m₀ m₁ P ∈ R := by
  classical
  simp [idxInCells]

/-- **T2 (VMOD-23 (2.1), first inequality).**  `|V_R| ≤ A′ |R|`, `A′ = (L^{m₀})^d`.
Hypothesis inherited from `card_deriv_in_cell`: `L ^ m₀ ∣ N₁`. -/
theorem card_idx_in_cells_le (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) {m₀ : ℕ}
    (hN : L ^ m₀ ∣ N₁) (R : Finset (ℕ × CTorus d L N₁ m₁ K)) :
    (idxInCells G m₀ R).card ≤ (L ^ m₀) ^ d * R.card := by
  classical
  have hD : ∀ P ∈ idxInCells G m₀ R, P.1 ≤ K ∧ CubeBase (K := K) m₁ P.1 P.2 := fun P hP => by
    obtain ⟨⟨h1, h2⟩, -, h3⟩ := (mem_cubeIdx G).1 (mem_idxInCells.1 hP).1
    exact ⟨h2, h3⟩
  calc (idxInCells G m₀ R).card
      ≤ (L ^ m₀) ^ d * ((idxInCells G m₀ R).image (cellOfCube (L := L) m₀ m₁)).card :=
        Finset.card_le_mul_card_image _ _ fun c _ => card_deriv_in_cell hN _ hD c
    _ ≤ (L ^ m₀) ^ d * R.card := by
        refine Nat.mul_le_mul_left _ (Finset.card_le_card ?_)
        intro c hc
        obtain ⟨P, hP, rfl⟩ := Finset.mem_image.1 hc
        exact (mem_idxInCells.1 hP).2

/-- **T3 (VMOD-23 (2.2)).**  For any family of subsets of a finite set `V`,
`∑ e^{-κ₂ |C|} ≤ (1 + e^{-κ₂})^{|V|} ≤ exp (|V| e^{-κ₂})`. -/
theorem sum_exp_card_le {P : Type*} [DecidableEq P] (V : Finset P) (𝔉 : Finset (Finset P))
    (h𝔉 : ∀ C ∈ 𝔉, C ⊆ V) (κ₂ : ℝ) :
    ∑ C ∈ 𝔉, Real.exp (-κ₂ * C.card) ≤ (1 + Real.exp (-κ₂)) ^ V.card ∧
      (1 + Real.exp (-κ₂)) ^ V.card ≤ Real.exp (V.card * Real.exp (-κ₂)) := by
  have hpos : 0 ≤ Real.exp (-κ₂) := (Real.exp_pos _).le
  constructor
  · have hbin : ∑ C ∈ V.powerset, Real.exp (-κ₂ * C.card) = (1 + Real.exp (-κ₂)) ^ V.card := by
      have := Finset.sum_pow_mul_eq_add_pow (Real.exp (-κ₂)) (1 : ℝ) V
      rw [add_comm, ← this]
      refine Finset.sum_congr rfl fun C _ => ?_
      rw [one_pow, mul_one, ← Real.exp_nat_mul]
      ring_nf
    rw [← hbin]
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun C hC => Finset.mem_powerset.2 (h𝔉 C hC))
      fun _ _ _ => (Real.exp_pos _).le
  · calc (1 + Real.exp (-κ₂)) ^ V.card ≤ (Real.exp (Real.exp (-κ₂))) ^ V.card := by
          refine pow_le_pow_left₀ (by linarith) ?_ _
          linarith [Real.add_one_le_exp (Real.exp (-κ₂))]
      _ = Real.exp (V.card * Real.exp (-κ₂)) := by rw [← Real.exp_nat_mul]

/-- **T3 corollary** for `V = V_R`: `∑ e^{-κ₂|C|} ≤ exp (A′ |R| e^{-κ₂})`. -/
theorem sum_exp_card_le_idx (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) {m₀ : ℕ}
    (hN : L ^ m₀ ∣ N₁) (R : Finset (ℕ × CTorus d L N₁ m₁ K))
    (𝔉 : Finset (Finset (ℕ × CTorus d L N₁ m₁ K))) (h𝔉 : ∀ C ∈ 𝔉, C ⊆ idxInCells G m₀ R)
    (κ₂ : ℝ) :
    ∑ C ∈ 𝔉, Real.exp (-κ₂ * C.card) ≤
      Real.exp ((((L ^ m₀) ^ d : ℕ) : ℝ) * R.card * Real.exp (-κ₂)) := by
  classical
  refine ((sum_exp_card_le _ 𝔉 h𝔉 κ₂).1.trans (sum_exp_card_le _ 𝔉 h𝔉 κ₂).2).trans ?_
  refine Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
  have := card_idx_in_cells_le G hN R
  exact_mod_cast this

/-- **T4 (VMOD-23 (2.3)-(2.5)), conditional fixed-support theorem.**  The hypothesis
`hR : |R| ≤ c₀ + c₁ D` is the candidate-region bound, an OPEN geometric input
(OPEN-P6-CANDIDATE-REGION); it is not proved here.  `a C` are the coefficients, bounded termwise
by `E_b exp(-κ₀ Δ - 2ρ D - κ₂ |C|)`.  Conclusion with `A′ = (L^{m₀})^d`, `q = A′ c₁ e^{-κ₂}`,
`H = exp (A′ c₀ e^{-κ₂})`. -/
theorem fixed_support_sum_of_candidates {E : Type*} [NormedAddCommGroup E]
    (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) {m₀ : ℕ} (hN : L ^ m₀ ∣ N₁)
    (R : Finset (ℕ × CTorus d L N₁ m₁ K))
    (𝔉 : Finset (Finset (ℕ × CTorus d L N₁ m₁ K))) (h𝔉 : ∀ C ∈ 𝔉, C ⊆ idxInCells G m₀ R)
    (a : Finset (ℕ × CTorus d L N₁ m₁ K) → E)
    (c₀ c₁ D Eb κ₀ Δ ρ κ₂ : ℝ) (hEb : 0 ≤ Eb)
    (hR : (R.card : ℝ) ≤ c₀ + c₁ * D)
    (ha : ∀ C ∈ 𝔉, ‖a C‖ ≤ Eb * Real.exp (-κ₀ * Δ - 2 * ρ * D - κ₂ * C.card)) :
    ‖∑ C ∈ 𝔉, a C‖ ≤
      Eb * Real.exp ((((L ^ m₀) ^ d : ℕ) : ℝ) * c₀ * Real.exp (-κ₂)) *
        Real.exp (-κ₀ * Δ - (2 * ρ - (((L ^ m₀) ^ d : ℕ) : ℝ) * c₁ * Real.exp (-κ₂)) * D) := by
  set A : ℝ := (((L ^ m₀) ^ d : ℕ) : ℝ) with hA
  have hA0 : 0 ≤ A := by positivity
  have hS := sum_exp_card_le_idx G hN R 𝔉 h𝔉 κ₂
  have hexp : A * R.card * Real.exp (-κ₂) ≤ A * (c₀ + c₁ * D) * Real.exp (-κ₂) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hR hA0) (Real.exp_pos _).le
  have h1 : ∑ C ∈ 𝔉, Real.exp (-κ₂ * C.card) ≤ Real.exp (A * (c₀ + c₁ * D) * Real.exp (-κ₂)) :=
    hS.trans (Real.exp_le_exp.2 hexp)
  calc ‖∑ C ∈ 𝔉, a C‖ ≤ ∑ C ∈ 𝔉, ‖a C‖ := norm_sum_le _ _
    _ ≤ ∑ C ∈ 𝔉, Eb * Real.exp (-κ₀ * Δ - 2 * ρ * D) * Real.exp (-κ₂ * C.card) := by
        refine Finset.sum_le_sum fun C hC => (ha C hC).trans (le_of_eq ?_)
        have : Real.exp (-κ₀ * Δ - 2 * ρ * D - κ₂ * C.card) =
            Real.exp (-κ₀ * Δ - 2 * ρ * D) * Real.exp (-κ₂ * C.card) := by
          rw [← Real.exp_add]; congr 1; ring
        rw [this]; ring
    _ = Eb * Real.exp (-κ₀ * Δ - 2 * ρ * D) * ∑ C ∈ 𝔉, Real.exp (-κ₂ * C.card) := by
        rw [Finset.mul_sum]
    _ ≤ Eb * Real.exp (-κ₀ * Δ - 2 * ρ * D) * Real.exp (A * (c₀ + c₁ * D) * Real.exp (-κ₂)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = _ := by
        rw [mul_assoc, mul_assoc Eb, mul_comm (Real.exp (A * c₀ * Real.exp (-κ₂))),
          ← mul_assoc, mul_assoc Eb, ← Real.exp_add, ← Real.exp_add]
        congr 2
        ring

omit [NeZero N₁] [NeZero L] in
/-- **T5 (consistency).**  W209's singleton family satisfies T3 with `V` = its points:
`J e^{-κ₂} ≤ exp (J e^{-κ₂})`, consistent with `sum_ledgerFamily`.  The bound `exp (|V|
e^{-κ₂})` grows with `|V| ≥ J`, so it does not contradict `no_uniform_fiber_constant`: there the
points `(j,0)` lie in no common cover (`ledgerFamily_not_in_one_cover`), hence in no `V_R`. -/
theorem ledgerFamily_sum_le (J : ℕ) (κ₂ : ℝ) :
    ∑ C ∈ ledgerFamily (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) J,
        Real.exp (-κ₂ * C.card) ≤ Real.exp (J * Real.exp (-κ₂)) := by
  rw [sum_ledgerFamily]
  linarith [Real.add_one_le_exp (J * Real.exp (-κ₂))]

end Packing

end Balaban.Localization
