/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.SizeModCells
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Admissible pairs: existence, attainment and the cell count (FLUCTUATION.md §1.2)

* `exists_admissible_of_IsDj`: for `X ∈ 𝒟_j` an admissible pair exists, so `dcovModE X ≠ ⊤`.
* `exists_admissible_eq_dcovModE`: the infimum defining `dcovModE` is attained.
* `exists_near_of_mem`: a cell of `Z ∩ Ω` lies in a cube of `𝒦`, hence within index distance
  `L - 1` of a cell met by the structure.
* `card_image_cbase_le`: the cells met by a connected structure number `≤ 3^d (cost + 1)`.
* `cellCount_le_of_admissible`: `n_π(Z ∩ Ω) ≤ (3 (2L-1))^d (1 + cost)`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ j : ℕ}

section Exist

/-- For `X ∈ 𝒟_j` there is an admissible pair, with all `π'_j`-cubes of `X` and a structure
spanning `X`. -/
theorem exists_admissible_of_IsDj {Ω X : Set (CTorus d L N₁ m₁ K)} (hX : IsDj m₀ j X) :
    ∃ 𝒦 W E, ModAdmissible m₀ j Ω X 𝒦 W E := by
  classical
  obtain ⟨hne, hU, hconn⟩ := hX
  have hL : 0 < L * cellSide L m₀ m₁ j :=
    Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne L)) (cellSide_pos m₀ m₁ j)
  let W : Finset (CTorus d L N₁ m₁ K) := Finset.univ.filter (· ∈ X)
  let E : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K) :=
    Finset.univ.filter fun p => p.1 ∈ X ∧ p.2 ∈ X ∧ Nbr p.1 p.2
  refine ⟨{b | Aligned (cellSide L m₀ m₁ j) b ∧ box b (L * cellSide L m₀ m₁ j) ⊆ X}, W, E,
    fun b hb => hb, fun z hz => ?_, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · obtain ⟨b, hb1, hb2, hb3⟩ := hU z hz.1
    exact Set.mem_iUnion₂.2 ⟨b, ⟨hb1, hb3⟩, hb2⟩
  · obtain ⟨x, hx⟩ := hne
    exact ⟨x, by simp [W, hx]⟩
  · intro p hp
    simpa [E, W] using (Finset.mem_filter.1 hp).2
  · intro x hx y hy
    have hx' : x ∈ X := by simpa [W] using hx
    have hy' : y ∈ X := by simpa [W] using hy
    refine Relation.ReflTransGen.mono (fun u v huv => ?_) x y (hconn x hx' y hy')
    simp only [E, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Or.inl huv
  · intro x hx; simpa [W] using hx
  · intro b hb
    refine ⟨b, ?_, mem_box_self b hL⟩
    simpa [W] using hb.2 (mem_box_self b hL)

omit [NeZero N₁] [NeZero L] in
theorem bondCost_scaleW_nonneg (E : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K)) :
    0 ≤ bondCost (scaleW L m₀ m₁ j) E :=
  Finset.sum_nonneg fun p _ => by unfold scaleW; positivity

private theorem finite_tuples (Ω X : Set (CTorus d L N₁ m₁ K)) :
    {p : Set (CTorus d L N₁ m₁ K) × Finset (CTorus d L N₁ m₁ K) ×
        Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K) |
      ModAdmissible m₀ j Ω X p.1 p.2.1 p.2.2}.Finite :=
  Set.toFinite _

/-- **The infimum defining `dcovModE` is attained** (there are finitely many pairs). -/
theorem exists_admissible_eq_dcovModE {Ω X : Set (CTorus d L N₁ m₁ K)}
    (h : ∃ 𝒦 W E, ModAdmissible m₀ j Ω X 𝒦 W E) :
    ∃ 𝒦 W E, ModAdmissible m₀ j Ω X 𝒦 W E ∧
      ENNReal.ofReal (bondCost (scaleW L m₀ m₁ j) E) = dcovModE m₀ j Ω X := by
  obtain ⟨𝒦, W, E, hE⟩ := h
  obtain ⟨p, hp, hmin⟩ := Set.exists_min_image _
    (fun p : Set (CTorus d L N₁ m₁ K) × Finset (CTorus d L N₁ m₁ K) ×
        Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K) => bondCost (scaleW L m₀ m₁ j) p.2.2)
    (finite_tuples (m₀ := m₀) (j := j) Ω X) ⟨(𝒦, W, E), hE⟩
  refine ⟨p.1, p.2.1, p.2.2, hp, le_antisymm ?_ ?_⟩
  · refine le_iInf fun 𝒦' => le_iInf fun W' => le_iInf fun E' => le_iInf fun h' => ?_
    exact ENNReal.ofReal_le_ofReal (hmin (𝒦', W', E') h')
  · exact (iInf_le_of_le p.1 (iInf_le_of_le p.2.1 (iInf_le_of_le p.2.2 (iInf_le_of_le hp le_rfl))))

theorem dcovModE_ne_top {Ω X : Set (CTorus d L N₁ m₁ K)}
    (h : ∃ 𝒦 W E, ModAdmissible m₀ j Ω X 𝒦 W E) : dcovModE m₀ j Ω X ≠ ⊤ := by
  obtain ⟨𝒦, W, E, -, he⟩ := exists_admissible_eq_dcovModE h
  rw [← he]; exact ENNReal.ofReal_ne_top

theorem dcovModE_ne_top_of_IsDj {Ω X : Set (CTorus d L N₁ m₁ K)} (hX : IsDj m₀ j X) :
    dcovModE m₀ j Ω X ≠ ⊤ :=
  dcovModE_ne_top (exists_admissible_of_IsDj hX)

omit [NeZero N₁] [NeZero L] in
theorem dcovMod_nonneg (Ω X : Set (CTorus d L N₁ m₁ K)) : 0 ≤ dcovMod m₀ j Ω X :=
  ENNReal.toReal_nonneg

omit [NeZero N₁] [NeZero L] in
theorem dcovModE_le_of_admissible {Ω X 𝒦 : Set (CTorus d L N₁ m₁ K)}
    {W : Finset (CTorus d L N₁ m₁ K)} {E : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K)}
    (h : ModAdmissible m₀ j Ω X 𝒦 W E) :
    dcovModE m₀ j Ω X ≤ ENNReal.ofReal (bondCost (scaleW L m₀ m₁ j) E) :=
  iInf_le_of_le 𝒦 (iInf_le_of_le W (iInf_le_of_le E (iInf_le_of_le h le_rfl)))

omit [NeZero N₁] [NeZero L] in
/-- Any admissible pair bounds `dcovMod` from above. -/
theorem dcovMod_le_of_admissible {Ω X 𝒦 : Set (CTorus d L N₁ m₁ K)}
    {W : Finset (CTorus d L N₁ m₁ K)} {E : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K)}
    (h : ModAdmissible m₀ j Ω X 𝒦 W E) :
    dcovMod m₀ j Ω X ≤ bondCost (scaleW L m₀ m₁ j) E := by
  have hle := dcovModE_le_of_admissible h
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
  rwa [ENNReal.toReal_ofReal (bondCost_scaleW_nonneg E)] at this

/-- An admissible pair realising `dcovMod`. -/
theorem exists_admissible_eq_dcovMod {Ω X : Set (CTorus d L N₁ m₁ K)}
    (h : ∃ 𝒦 W E, ModAdmissible m₀ j Ω X 𝒦 W E) :
    ∃ 𝒦 W E, ModAdmissible m₀ j Ω X 𝒦 W E ∧ bondCost (scaleW L m₀ m₁ j) E = dcovMod m₀ j Ω X := by
  obtain ⟨𝒦, W, E, hE, he⟩ := exists_admissible_eq_dcovModE h
  refine ⟨𝒦, W, E, hE, ?_⟩
  unfold dcovMod
  rw [← he, ENNReal.toReal_ofReal (bondCost_scaleW_nonneg E)]

end Exist

section Count

/-- A cell base of `Z ∩ Ω` lies within index distance `L - 1` of a cell met by the structure. -/
theorem exists_near_of_mem (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K)
    {Z Ω 𝒦 : Set (CTorus d L N₁ m₁ K)} {W : Finset (CTorus d L N₁ m₁ K)}
    {E : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K)}
    (h : ModAdmissible m₀ j Ω Z 𝒦 W E) {t : CTorus d L N₁ m₁ K}
    (ht : Aligned (cellSide L m₀ m₁ j) t) (htZ : t ∈ Z ∩ Ω) :
    ∃ c ∈ W.image (cbase (cellSide L m₀ m₁ j)), Near (L - 1) (cellSide L m₀ m₁ j) c t := by
  have hdvd := cellSide_dvd (K := K) (m₁ := m₁) hN hj
  have ha0 := cellSide_pos (L := L) m₀ m₁ j
  obtain ⟨hK, hcov, -, -, hmeet⟩ := h
  obtain ⟨q, hq, htq⟩ := Set.mem_iUnion₂.1 (hcov htZ)
  obtain ⟨x, hxW, hxq⟩ := hmeet q hq
  have hqal := (hK q hq).1
  have hcx : cbase (cellSide L m₀ m₁ j) x ∈ box q (L * cellSide L m₀ m₁ j) :=
    (cell_subset_cube hdvd ha0 hqal hxq) (mem_box_self _ ha0)
  obtain ⟨r, hr, htr⟩ := aligned_diff hdvd ha0 hqal ht (aligned_cbase x) htq hcx
  have hL1 : 1 ≤ L := Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  refine ⟨cbase (cellSide L m₀ m₁ j) x, Finset.mem_image_of_mem _ hxW, r, fun μ => ?_, htr⟩
  have := hr μ
  rw [abs_le]
  push_cast [Nat.cast_sub hL1]
  constructor <;> omega

/-- The constant `c₁` of (G1): `(3 (2L - 1))^d`.  (FLUCTUATION.md has `(2L+3)^d`, from P6's
covering of a tree by few large cubes; the constant here comes from the landed block count
`card_cells_le`.) -/
def c1 (d L : ℕ) : ℝ := ((3 * (2 * L - 1) : ℕ) : ℝ) ^ d

open Classical in
/-- **The cells met by a connected structure**: `#(cells met) ≤ 3^d (cost + 1)`. -/
theorem card_image_cbase_le (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K)
    {W : Finset (CTorus d L N₁ m₁ K)} {E : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K)}
    (hc : ConnStruct W E) :
    ((W.image (cbase (cellSide L m₀ m₁ j))).card : ℝ) ≤
      3 ^ d * (bondCost (scaleW L m₀ m₁ j) E + 1) := by
  set a := cellSide L m₀ m₁ j with ha
  have ha0 : 0 < a := cellSide_pos m₀ m₁ j
  obtain ⟨m, hm⟩ := cellSide_dvd (K := K) (m₁ := m₁) hN hj
  have hmne : NeZero m := ⟨fun h => by
    have : (N₁ * L ^ m₁) * L ^ K ≠ 0 := NeZero.ne _
    rw [hm, h] at this; simp at this⟩
  have hc1 := card_cells_le (d := d) hm ha0 hc
  have hc2 := card_cbase_le (d := d) hm W
  have hnat : a * (W.image (cbase a)).card ≤ 3 ^ d * (E.card + a) :=
    (Nat.mul_le_mul_left _ hc2).trans hc1
  have haR : (a : ℝ) = (L : ℝ) ^ (m₀ + m₁ + j) := by
    rw [ha]; unfold cellSide; push_cast; congr 1; ring
  have hapos : (0 : ℝ) < a := by exact_mod_cast ha0
  have hcostE : bondCost (scaleW L m₀ m₁ j) E = E.card / a := by
    unfold bondCost scaleW
    rw [Finset.sum_const, nsmul_eq_mul, ← haR]; ring
  have hR : (a : ℝ) * (W.image (cbase a)).card ≤ (3 : ℝ) ^ d * (E.card + a) := by
    exact_mod_cast hnat
  rw [hcostE]
  have e : (E.card : ℝ) / a + 1 = (E.card + a) / a := by field_simp
  rw [e, ← mul_div_assoc, le_div_iff₀ hapos]
  nlinarith [hR]

open Classical in
/-- **`n_π(Z ∩ Ω) ≤ c₁ (1 + cost)`** for every admissible pair. -/
theorem cellCount_le_of_admissible (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K)
    {Z Ω 𝒦 : Set (CTorus d L N₁ m₁ K)} {W : Finset (CTorus d L N₁ m₁ K)}
    {E : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K)}
    (h : ModAdmissible m₀ j Ω Z 𝒦 W E) :
    (cellCount (cellSide L m₀ m₁ j) (Z ∩ Ω) : ℝ) ≤
      c1 d L * (1 + bondCost (scaleW L m₀ m₁ j) E) := by
  set a := cellSide L m₀ m₁ j with ha
  have ha0 : 0 < a := cellSide_pos m₀ m₁ j
  have hL1 : 1 ≤ L := Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  set A := W.image (cbase a) with hA
  have hsub : (Finset.univ.filter fun b : CTorus d L N₁ m₁ K =>
      Aligned a b ∧ box b a ⊆ Z ∩ Ω) ⊆
      A.biUnion fun c => Finset.univ.filter fun t => Near (L - 1) a c t := by
    intro t ht
    obtain ⟨hal, hbox⟩ := (Finset.mem_filter.1 ht).2
    obtain ⟨c, hcA, hcn⟩ := exists_near_of_mem hN hj h hal (hbox (mem_box_self t ha0))
    exact Finset.mem_biUnion.2 ⟨c, hcA, by simpa using hcn⟩
  have h1 : cellCount a (Z ∩ Ω) ≤ A.card * (2 * L - 1) ^ d := by
    unfold cellCount
    calc _ ≤ _ := Finset.card_le_card hsub
      _ ≤ ∑ c ∈ A, (Finset.univ.filter fun t => Near (L - 1) a c t).card := Finset.card_biUnion_le
      _ ≤ ∑ _c ∈ A, (2 * L - 1) ^ d := by
          refine Finset.sum_le_sum fun c _ => ?_
          have := card_near_le (d := d) (n := (N₁ * L ^ m₁) * L ^ K) (L - 1) a c
          have e : 2 * (L - 1) + 1 = 2 * L - 1 := by omega
          rwa [e] at this
      _ = _ := by simp
  have h2 := card_image_cbase_le hN hj h.2.2.1
  have h1R : (cellCount a (Z ∩ Ω) : ℝ) ≤ (A.card : ℝ) * ((2 * L - 1 : ℕ) : ℝ) ^ d := by
    exact_mod_cast h1
  have hc0 : (0 : ℝ) ≤ ((2 * L - 1 : ℕ) : ℝ) ^ d := by positivity
  calc (cellCount a (Z ∩ Ω) : ℝ) ≤ (A.card : ℝ) * ((2 * L - 1 : ℕ) : ℝ) ^ d := h1R
    _ ≤ (3 ^ d * (bondCost (scaleW L m₀ m₁ j) E + 1)) * ((2 * L - 1 : ℕ) : ℝ) ^ d :=
        mul_le_mul_of_nonneg_right h2 hc0
    _ = c1 d L * (1 + bondCost (scaleW L m₀ m₁ j) E) := by
        unfold c1
        push_cast
        rw [mul_pow]
        ring

end Count

end Balaban.Fluctuation
