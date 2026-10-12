/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.PolymerCount
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The fixed-output count with derivative witnesses (GRAPH-GM-2 §4, P3 (4.50))

The count of effective derivative families at a fixed whole output `Y`.  The index is the family
`𝒞` of active complementary derivative cubes, not a parameter label hidden in a hole.

* `fixed_output_count`: Theorem 4.1 (4.1)–(4.4) in a generic form.  `Cube` are the derivative
  cubes, `Cell` the active output `M`-cells, `cellOf` the cell containing a cube, `D P` the
  completion cells of a derivative `P`.  The fibre is the set of families with the same whole
  output: the cells `Yc` of `Y` outside the source base `Bc` are the same for all of them.
* `boundary_gm3_fixed_Y`: the same on the torus, with the cells `(n, base)` of layer `n` and
  the derivative cubes `(n, y)` of layer `n`; the bound `|derivatives in a cell| ≤ (L^{m₀})^d`
  (`A' = (M/M₁)^d`) is proved from `card_cubeBases_cell`.
* `rate_conditions`: the sufficient explicit conditions (4.5).

The three inputs of (4.1) (`C ⊆ V(Y)`, ownership of every new output cell, at most `G`
completion cells per derivative) are hypotheses: they are the named assertions of
OPEN-P6-WITNESS-GEOMETRY (`deriv_mem_output_new`, `completion_cells_le`, ownership).
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Finset

section Generic

variable {Cube Cell : Type*} [DecidableEq Cube] [DecidableEq Cell]

/-- **Theorem 4.1 (fixed-`Y` count), generic form.**  Let `𝔉` be a finite collection of
effective derivative families with the same whole output `Y`: for each `𝒞 ∈ 𝔉`, `𝒞` consists of
admissible derivative cubes (`Deriv`) lying in new active output cells (`Yc \ Bc`), every new
active output cell has an owner `P ∈ 𝒞` (it belongs to `D P`), and `|D P| ≤ G`; at most `A'`
derivative cubes lie in one cell.  If `x = κ₂/2 ≥ 1` and `x ≥ log (G A')`, then
`∑_{𝒞 ∈ 𝔉} e^{-κ₂ |𝒞|} ≤ 1`. -/
theorem fixed_output_count (cellOf : Cube → Cell) (D : Cube → Finset Cell)
    (Deriv : Finset Cube) (Yc Bc : Finset Cell) (G A' : ℕ) (hG : 1 ≤ G) (hA : 1 ≤ A')
    (hfib : ∀ c, (Deriv.filter fun P => cellOf P = c).card ≤ A')
    (hD : ∀ P, (D P).card ≤ G) (𝔉 : Finset (Finset Cube))
    (h𝔉 : ∀ C ∈ 𝔉, C ⊆ Deriv ∧ (∀ P ∈ C, cellOf P ∈ Yc \ Bc) ∧ Yc \ Bc ⊆ C.biUnion D)
    (κ₂ : ℝ) (h1 : 1 ≤ κ₂ / 2) (hlog : Real.log ((G : ℝ) * (A' : ℝ)) ≤ κ₂ / 2) :
    ∑ C ∈ 𝔉, Real.exp (-κ₂ * C.card) ≤ 1 := by
  classical
  set x : ℝ := κ₂ / 2 with hx
  set V : Finset Cube := Deriv.filter fun P => cellOf P ∈ Yc \ Bc with hV
  set b : ℕ := (Yc \ Bc).card with hb
  have hGpos : (0 : ℝ) < G := by exact_mod_cast hG
  have hApos : (0 : ℝ) < A' := by exact_mod_cast hA
  -- the number of candidate cubes
  have hVcard : V.card ≤ A' * b := by
    have : V ⊆ (Yc \ Bc).biUnion fun c => Deriv.filter fun P => cellOf P = c := by
      intro P hP
      rw [hV, Finset.mem_filter] at hP
      exact Finset.mem_biUnion.2 ⟨cellOf P, hP.2, Finset.mem_filter.2 ⟨hP.1, rfl⟩⟩
    refine (Finset.card_le_card this).trans ((Finset.card_biUnion_le).trans ?_)
    calc ∑ c ∈ Yc \ Bc, (Deriv.filter fun P => cellOf P = c).card
        ≤ ∑ _c ∈ Yc \ Bc, A' := Finset.sum_le_sum fun c _ => hfib c
      _ = A' * b := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  -- the number of new cells is at most `G |𝒞|`
  have hbC : ∀ C ∈ 𝔉, (b : ℝ) ≤ G * C.card := by
    intro C hC
    have h := (h𝔉 C hC).2.2
    have h2 : b ≤ ∑ P ∈ C, (D P).card :=
      (Finset.card_le_card h).trans Finset.card_biUnion_le
    have h3 : ∑ P ∈ C, (D P).card ≤ C.card * G := by
      calc ∑ P ∈ C, (D P).card ≤ ∑ _P ∈ C, G := Finset.sum_le_sum fun P _ => hD P
        _ = C.card * G := by rw [Finset.sum_const, smul_eq_mul]
    have : b ≤ C.card * G := h2.trans h3
    have : (b : ℝ) ≤ C.card * G := by exact_mod_cast this
    linarith
  have hx1 : 1 ≤ x := h1
  have hex : (G : ℝ) * A' ≤ Real.exp x := by
    have hpos : 0 < (G : ℝ) * A' := mul_pos hGpos hApos
    calc (G : ℝ) * A' = Real.exp (Real.log (G * A')) := (Real.exp_log hpos).symm
      _ ≤ Real.exp x := Real.exp_le_exp.2 hlog
  have hexp_neg : Real.exp (-x) ≤ 1 / ((G : ℝ) * A') := by
    rw [Real.exp_neg, le_div_iff₀ (mul_pos hGpos hApos), inv_mul_le_iff₀ (Real.exp_pos x)]
    simpa using hex
  -- split the exponent
  have hsplit : ∀ C ∈ 𝔉, Real.exp (-κ₂ * C.card) ≤
      Real.exp (-x * b / G) * Real.exp (-x * C.card) := by
    intro C hC
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    have h1' := hbC C hC
    have hxb : x * b / G ≤ x * C.card := by
      rw [div_le_iff₀ hGpos]
      have := mul_le_mul_of_nonneg_left h1' (by linarith : (0 : ℝ) ≤ x)
      linarith
    have hk : κ₂ = 2 * x := by rw [hx]; ring
    have e : -x * b / G = -(x * b / G) := by ring
    rw [hk, e]; linarith
  have hsub : 𝔉 ⊆ V.powerset := by
    intro C hC
    rw [Finset.mem_powerset]
    intro P hP
    rw [hV, Finset.mem_filter]
    exact ⟨(h𝔉 C hC).1 hP, (h𝔉 C hC).2.1 P hP⟩
  have hsum : ∑ C ∈ 𝔉, Real.exp (-x * C.card) ≤ (Real.exp (-x) + 1) ^ V.card := by
    calc ∑ C ∈ 𝔉, Real.exp (-x * C.card)
        ≤ ∑ C ∈ V.powerset, Real.exp (-x * C.card) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => (Real.exp_pos _).le
      _ = ∑ C ∈ V.powerset, Real.exp (-x) ^ C.card * 1 ^ (V.card - C.card) := by
          refine Finset.sum_congr rfl fun C _ => ?_
          rw [one_pow, mul_one, ← Real.exp_nat_mul]; congr 1; ring
      _ = (Real.exp (-x) + 1) ^ V.card := Finset.sum_pow_mul_eq_add_pow _ _ _
  have hpow : (Real.exp (-x) + 1) ^ V.card ≤ Real.exp (V.card * Real.exp (-x)) := by
    have : Real.exp (-x) + 1 ≤ Real.exp (Real.exp (-x)) := Real.add_one_le_exp _
    calc (Real.exp (-x) + 1) ^ V.card ≤ (Real.exp (Real.exp (-x))) ^ V.card :=
          pow_le_pow_left₀ (by positivity) this _
      _ = _ := by rw [← Real.exp_nat_mul]
  have hVe : (V.card : ℝ) * Real.exp (-x) ≤ b / G := by
    have h1 : (V.card : ℝ) ≤ A' * b := by exact_mod_cast hVcard
    calc (V.card : ℝ) * Real.exp (-x) ≤ (A' * b) * (1 / (G * A')) :=
          mul_le_mul h1 hexp_neg (Real.exp_pos _).le (by positivity)
      _ = b / G := by field_simp
  calc ∑ C ∈ 𝔉, Real.exp (-κ₂ * C.card)
      ≤ ∑ C ∈ 𝔉, Real.exp (-x * b / G) * Real.exp (-x * C.card) :=
        Finset.sum_le_sum hsplit
    _ = Real.exp (-x * b / G) * ∑ C ∈ 𝔉, Real.exp (-x * C.card) := by rw [Finset.mul_sum]
    _ ≤ Real.exp (-x * b / G) * Real.exp (V.card * Real.exp (-x)) :=
        mul_le_mul_of_nonneg_left (hsum.trans hpow) (Real.exp_pos _).le
    _ ≤ Real.exp (-x * b / G) * Real.exp (b / G) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hVe) (Real.exp_pos _).le
    _ = Real.exp ((1 - x) * b / G) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ 1 := by
        rw [Real.exp_le_one_iff]
        have : (0 : ℝ) ≤ b := Nat.cast_nonneg _
        have : (1 - x) * b ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) this
        exact div_nonpos_of_nonpos_of_nonneg this hGpos.le

end Generic

section Torus

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ : ℕ}

/-- The cell of layer `n` containing the derivative cube `(n, y)`. -/
def cellOfCube (m₀ m₁ : ℕ) (P : ℕ × CTorus d L N₁ m₁ K) : ℕ × CTorus d L N₁ m₁ K :=
  (P.1, cbase (cellSide L m₀ m₁ P.1) P.2)

/-- At most `(L^{m₀})^d = (M/M₁)^d` derivative cubes (aligned bases of layer `n`) lie in a cell. -/
theorem card_deriv_in_cell (hN : L ^ m₀ ∣ N₁) (Deriv : Finset (ℕ × CTorus d L N₁ m₁ K))
    (hDeriv : ∀ P ∈ Deriv, P.1 ≤ K ∧ CubeBase (K := K) m₁ P.1 P.2)
    (c : ℕ × CTorus d L N₁ m₁ K) :
    (Deriv.filter fun P => cellOfCube (L := L) m₀ m₁ P = c).card ≤ (L ^ m₀) ^ d := by
  classical
  by_cases hne : (Deriv.filter fun P => cellOfCube (L := L) m₀ m₁ P = c).Nonempty
  · obtain ⟨P₀, hP₀⟩ := hne
    rw [Finset.mem_filter] at hP₀
    have hc : c = (P₀.1, cbase (cellSide L m₀ m₁ P₀.1) P₀.2) := hP₀.2.symm
    have hal : Aligned (cellSide L m₀ m₁ c.1) c.2 := by
      rw [hc]; exact aligned_cbase _
    have hnK : c.1 ≤ K := by rw [hc]; exact (hDeriv P₀ hP₀.1).1
    rw [← card_cubeBases_cell (K := K) (m₁ := m₁) hN hnK hal]
    refine Finset.card_le_card_of_injOn (fun P => P.2) ?_ ?_
    · intro P hP
      rw [Finset.mem_coe, Finset.mem_filter] at hP
      obtain ⟨hPD, hPc⟩ := hP
      have h1 : P.1 = c.1 := by rw [← hPc]; rfl
      have h2 : cbase (cellSide L m₀ m₁ c.1) P.2 = c.2 := by
        have := congrArg Prod.snd hPc
        simpa [cellOfCube, h1] using this
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
      refine ⟨by have := (hDeriv P hPD).2; rw [h1] at this; exact this, ?_⟩
      have h3 := mem_box_cbase (cellSide_pos (L := L) m₀ m₁ P.1) P.2
      rw [h1, h2] at h3
      exact h3
    · intro P hP P' hP' h
      rw [Finset.mem_coe, Finset.mem_filter] at hP hP'
      have h1 : P.1 = c.1 := by rw [← hP.2]; rfl
      have h1' : P'.1 = c.1 := by rw [← hP'.2]; rfl
      exact Prod.ext (h1.trans h1'.symm) h
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne]; simp

/-- **Theorem 4.1 on the torus (`boundary_gm3_fixed_Y`).**  The families of derivative cubes
`(n, y)` with the same whole output (the same new active output cells `Yc \ Bc`, `Bc` the source
base) satisfy `∑ e^{-κ₂ |𝒞|} ≤ 1` provided `κ₂/2 ≥ 1` and `κ₂/2 ≥ log (G A')` with
`G = (2L+1)^d`, `A' = (L^{m₀})^d`.  The premises on each family are the witness assertions:
`C ⊆ Deriv` and `cellOfCube P ∈ Yc \ Bc` (`deriv_mem_output_new`), every new cell is in some
`D P` (ownership), and `|D P| ≤ (2L+1)^d` (`completion_cells_le`). -/
theorem boundary_gm3_fixed_Y (hN : L ^ m₀ ∣ N₁) (Deriv : Finset (ℕ × CTorus d L N₁ m₁ K))
    (hDeriv : ∀ P ∈ Deriv, P.1 ≤ K ∧ CubeBase (K := K) m₁ P.1 P.2)
    (D : ℕ × CTorus d L N₁ m₁ K → Finset (ℕ × CTorus d L N₁ m₁ K))
    (hD : ∀ P, (D P).card ≤ (2 * L + 1) ^ d)
    (Yc Bc : Finset (ℕ × CTorus d L N₁ m₁ K))
    (𝔉 : Finset (Finset (ℕ × CTorus d L N₁ m₁ K)))
    (h𝔉 : ∀ C ∈ 𝔉, C ⊆ Deriv ∧ (∀ P ∈ C, cellOfCube (L := L) m₀ m₁ P ∈ Yc \ Bc) ∧
      Yc \ Bc ⊆ C.biUnion D)
    (κ₂ : ℝ) (h1 : 1 ≤ κ₂ / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ κ₂ / 2) :
    ∑ C ∈ 𝔉, Real.exp (-κ₂ * C.card) ≤ 1 := by
  have hL0 : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  exact fixed_output_count (cellOfCube (L := L) m₀ m₁) D Deriv Yc Bc ((2 * L + 1) ^ d)
    ((L ^ m₀) ^ d) (Nat.one_le_pow _ _ (by omega)) (Nat.one_le_pow _ _ (Nat.one_le_pow _ _ hL0))
    (card_deriv_in_cell hN Deriv hDeriv) hD 𝔉 h𝔉 κ₂ h1 hlog

end Torus

section Rate

/-- **The sufficient explicit conditions (4.5)**: with `κ₂ = κ₁/2 - 1`, the conditions
`κ₁ ≥ 6` and `κ₁ ≥ 4 d log ((2L+1) L^{m₀}) + 2` give `κ₂/2 ≥ 1` and
`κ₂/2 ≥ log ((2L+1)^d (L^{m₀})^d)`. -/
theorem rate_conditions (d L m₀ : ℕ) (hL : 1 ≤ L) (κ₁ : ℝ) (h6 : 6 ≤ κ₁)
    (hκ : 4 * d * Real.log (((2 * L + 1 : ℕ) : ℝ) * ((L ^ m₀ : ℕ) : ℝ)) + 2 ≤ κ₁) :
    1 ≤ (κ₁ / 2 - 1) / 2 ∧
      Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ₁ / 2 - 1) / 2 := by
  refine ⟨by linarith, ?_⟩
  have h1 : (0 : ℝ) < ((2 * L + 1 : ℕ) : ℝ) := by positivity
  have h2 : (0 : ℝ) < ((L ^ m₀ : ℕ) : ℝ) := by
    have : 0 < L ^ m₀ := Nat.pow_pos hL
    exact_mod_cast this
  have : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) =
      d * Real.log (((2 * L + 1 : ℕ) : ℝ) * ((L ^ m₀ : ℕ) : ℝ)) := by
    rw [← Real.log_pow]
    congr 1
    push_cast
    rw [mul_pow, ← pow_mul]
  rw [this]
  linarith

end Rate

end Balaban.Localization
