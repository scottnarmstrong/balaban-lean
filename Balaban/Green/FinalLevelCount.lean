/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.FinalLiftDecayCoef
public import Balaban.Green.FinalLiftDecaySum
public import Balaban.Green.FinalLogDetLocal
public import Balaban.Green.BlockDistance
public import Balaban.LargeField.R.RRemovedCapEnergy
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# The read sets, the sites at each distance level and their count (blocker 5)

Counting lemmas on the torus: a ball of the `ℓ¹` distance with radius `R` has at most `(2R+1)^d`
points; a fibre of the unit-block map has at most `(L^k)^d` points;  Path distance: in a generating set with `Ω₁` the whole torus every two
sites are at path distance at most `∑_i (b_i - a_i).val`.
-/

@[expose] public section

open Finset Set MeasureTheory Metric Balaban Balaban.Multiscale Balaban.Background
  Balaban.Localization Balaban.Analysis Balaban.SmallField Balaban.SmallField.Def6
  Balaban.SmallField.Def6v2 Balaban.SmallField.GsSpec Balaban.Fluctuation Balaban.Inhabited
  Balaban.LargeField Balaban.LargeField.ActionConv

namespace Balaban.Green

section Count

variable {d m : ℕ} [NeZero m]

/-- A ball of the `ℓ¹` distance of radius `R` has at most `(2R+1)^d` points. -/
theorem card_torus_ball_le (t : Balaban.Torus d m) (R : ℕ) :
    (univ.filter fun w : Balaban.Torus d m => torusDist d m t w ≤ R).card ≤ (2 * R + 1) ^ d := by
  classical
  have hsub : (univ.filter fun w : Balaban.Torus d m => torusDist d m t w ≤ R) ⊆
      Fintype.piFinset (fun i => univ.filter fun v : ZMod m => (cycRep (t i - v)).natAbs ≤ R) := by
    intro w hw
    rw [Fintype.mem_piFinset]
    intro i
    have hw' := (mem_filter.1 hw).2
    have h1 : ((cycRep (t i - w i)).natAbs : ℝ) ≤ torusDist d m t w :=
      Finset.single_le_sum (f := fun i => ((cycRep (t i - w i)).natAbs : ℝ))
        (fun _ _ => Nat.cast_nonneg _) (mem_univ i)
    exact mem_filter.2 ⟨mem_univ _, by exact_mod_cast h1.trans hw'⟩
  calc _ ≤ _ := Finset.card_le_card hsub
    _ = ∏ i, (univ.filter fun v : ZMod m => (cycRep (t i - v)).natAbs ≤ R).card :=
        Fintype.card_piFinset _
    _ ≤ ∏ _i : Fin d, (2 * R + 1) := Finset.prod_le_prod fun i _ => card_cyc_ball_le _ R
    _ = (2 * R + 1) ^ d := by simp

/-- The residues with a given quotient by `s` are at most `s`. -/
theorem card_val_div_le {s : ℕ} (hs : 0 < s) (c : ℕ) :
    (univ.filter fun v : ZMod m => v.val / s = c).card ≤ s := by
  classical
  have hmap : ∀ v ∈ (univ.filter fun v : ZMod m => v.val / s = c), v.val % s ∈ range s := fun v _ =>
    mem_range.2 (Nat.mod_lt _ hs)
  refine (card_le_card_of_injOn (fun v : ZMod m => v.val % s) hmap ?_).trans (by simp)
  intro v hv w hw hvw
  have hv' : v.val / s = c := by simpa using hv
  have hw' : w.val / s = c := by simpa using hw
  apply ZMod.val_injective
  have e1 := Nat.div_add_mod v.val s
  have e2 := Nat.div_add_mod w.val s
  simp only at hvw
  rw [hv'] at e1
  rw [hw'] at e2
  omega

/-- The sites of the fine torus with a given unit block: at most `(L^k)^d`. -/
theorem card_unitBlock_fiber_le {d L N₁ m₁ k : ℕ} [NeZero L] [NeZero N₁]
    (u : UnitTorus d L N₁ m₁ k) :
    (univ.filter fun x : CTorus d L N₁ m₁ (k + 1) => unitBlock x = u).card ≤ (L ^ k) ^ d := by
  classical
  have hs : 0 < L ^ k := pow_pos (NeZero.pos L) k
  rcases (univ.filter fun x : CTorus d L N₁ m₁ (k + 1) => unitBlock x = u).eq_empty_or_nonempty with
    h | ⟨x0, hx0⟩
  · rw [h]; simp
  have hsub : (univ.filter fun x : CTorus d L N₁ m₁ (k + 1) => unitBlock x = u) ⊆
      Fintype.piFinset (fun i => univ.filter fun v : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1)) =>
        v.val / L ^ k = (x0 i).val / L ^ k) := by
    intro x hx
    rw [Fintype.mem_piFinset]
    intro i
    have hx' := (mem_filter.1 hx).2
    have hx0' := (mem_filter.1 hx0).2
    exact mem_filter.2 ⟨mem_univ _, (unitBlock_eq_iff x x0).1 (hx'.trans hx0'.symm) i⟩
  calc _ ≤ _ := Finset.card_le_card hsub
    _ = ∏ i, (univ.filter fun v : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1)) =>
        v.val / L ^ k = (x0 i).val / L ^ k).card := Fintype.card_piFinset _
    _ ≤ ∏ _i : Fin d, L ^ k := Finset.prod_le_prod fun i _ => card_val_div_le hs _
    _ = (L ^ k) ^ d := by simp

end Count

section Path

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- In a generating set with `Ω₁` the whole torus, the path distance of two sites is at most the
sum of the coordinate differences (each in `[0, m)`). -/
theorem pathDist_le_sumVal (G : GeneratingSet d L N₀ k ϱ) (hΩ : G.Ω 1 = Finset.univ) :
    ∀ (n : ℕ) (a b : Balaban.Torus d (N₀ * L ^ k)), ∑ i, (b i - a i).val = n →
      G.pathDist a b ≤ ENNReal.ofReal n := by
  intro n
  induction n with
  | zero =>
    intro a b h
    have hab : a = b := by
      funext i
      have h0 : (b i - a i).val = 0 := (Finset.sum_eq_zero_iff.1 h) i (mem_univ i)
      exact (sub_eq_zero.1 ((ZMod.val_eq_zero _).1 h0)).symm
    subst hab
    rw [GeneratingSet.pathDist_self (hΩ ▸ mem_univ a)]
    exact bot_le
  | succ n ih =>
    intro a b h
    obtain ⟨i, hi⟩ : ∃ i, (b i - a i).val ≠ 0 := by
      by_contra hcon
      push Not at hcon
      simp [hcon] at h
    have hpos : 1 ≤ (b i - a i).val := Nat.one_le_iff_ne_zero.2 hi
    have hm : 1 < N₀ * L ^ k := by
      have := ZMod.val_lt (b i - a i)
      omega
    have : Fact (1 < N₀ * L ^ k) := ⟨hm⟩
    obtain ⟨a', ha'def⟩ : ∃ a' : Balaban.Torus d (N₀ * L ^ k), a' =
        a + Pi.single i (1 : ZMod (N₀ * L ^ k)) := ⟨_, rfl⟩
    have hval : ∀ j, (b j - a' j).val =
        if j = i then (b i - a i).val - 1 else (b j - a j).val := by
      intro j
      by_cases hj : j = i
      · subst hj
        rw [ha'def]
        simp only [Pi.add_apply, Pi.single_eq_same, ite_true]
        rw [show b j - (a j + 1) = (b j - a j) - 1 by ring,
          ZMod.val_sub (by rw [ZMod.val_one]; exact hpos), ZMod.val_one]
      · rw [ha'def]
        simp [hj]
    have hsum : ∑ j, (b j - a' j).val = n := by
      have h1 := Finset.add_sum_erase univ (fun j => (b j - a j).val) (mem_univ i)
      have h2 := Finset.add_sum_erase univ (fun j => (b j - a' j).val) (mem_univ i)
      have h3 : ∑ j ∈ univ.erase i, (b j - a' j).val =
          ∑ j ∈ univ.erase i, (b j - a j).val :=
        Finset.sum_congr rfl fun j hj => by rw [hval j]; simp [Finset.ne_of_mem_erase hj]
      have h4 : (b i - a' i).val = (b i - a i).val - 1 := by simpa using hval i
      omega
    have ha : a ∈ G.Ω 1 := hΩ ▸ mem_univ a
    have ha' : a' ∈ G.Ω 1 := hΩ ▸ mem_univ _
    have e1 : G.pathDist a a' ≤ ENNReal.ofReal 1 :=
      (GeneratingSet.pathDist_le_bondCost ha ha' ⟨i, Or.inl ha'def⟩).trans
        (ENNReal.ofReal_le_ofReal (G.bondCost_le_one ha _))
    calc G.pathDist a b ≤ G.pathDist a a' + G.pathDist a' b :=
          G.pathDist_triangle _ _ _
      _ ≤ ENNReal.ofReal 1 + ENNReal.ofReal n := add_le_add e1 (ih _ _ hsum)
      _ = ENNReal.ofReal ((n + 1 : ℕ) : ℝ) := by
          rw [← ENNReal.ofReal_add (by norm_num) (Nat.cast_nonneg n)]
          congr 1; push_cast; ring

/-- Every two sites are at path distance at most `d (N₀ L^k)`. -/
theorem pathDist_le_dim_mul (G : GeneratingSet d L N₀ k ϱ) (hΩ : G.Ω 1 = Finset.univ)
    (a b : Balaban.Torus d (N₀ * L ^ k)) :
    G.pathDist a b ≤ ENNReal.ofReal ((d * (N₀ * L ^ k) : ℕ) : ℝ) := by
  refine (pathDist_le_sumVal G hΩ _ a b rfl).trans (ENNReal.ofReal_le_ofReal ?_)
  have : ∑ i, (b i - a i).val ≤ ∑ _i : Fin d, (N₀ * L ^ k) :=
    Finset.sum_le_sum fun i _ => (ZMod.val_lt _).le
  have h2 : ((∑ i, (b i - a i).val : ℕ) : ℝ) ≤ ((d * (N₀ * L ^ k) : ℕ) : ℝ) := by
    exact_mod_cast this.trans (by simp)
  exact h2

end Path

section Step

variable {d d' N₀ N N₁ m₁ kS L M : ℕ} [NeZero N₀] [NeZero N₁] [NeZero L] {ϱ : ℝ}
  (S : StepSetting d' L N₁ m₁ kS N ϱ) (e : L1Torus d N₀ ≃ S.U × Fin N)

/-- Every unit point is the unit block of a site: the unit point of the site. -/
theorem exists_unitPt_eq (u : S.U) : ∃ x : CTorus d' L N₁ m₁ (kS + 1), unitPt S.hG' x = u := by
  obtain ⟨x, -, hx⟩ := (mem_unitPts S.G').1 u.2
  exact ⟨x, Subtype.ext hx⟩

omit [NeZero N₀] in
/-- **The read sets at distance level `n`** (`hS` of `norm_coef_cutoff_class_le_lift`): the explicit
set of `q` whose unit point is that of a site `x` lying in an `L^j`-block meeting `X`, or whose
block-site `z` (a site of an `L^j`-block meeting `X`) is at path distance `< n` of a site of `Ω₁`
equal or adjacent to `x`.  It satisfies the clause `hS`. -/
theorem readSet_hS :
    ∀ (n j : ℕ) (_y : CTorus d' L N₁ m₁ (kS + 1)) (X : Set (CTorus d' L N₁ m₁ (kS + 1))) (q : L1Torus d N₀)
      (x : CTorus d' L N₁ m₁ (kS + 1)),
      (e q).1 = unitPt S.hG' x →
      ((∃ z ∈ X, jBlock d' L (N₁ * L ^ m₁) (kS + 1) j x =
          jBlock d' L (N₁ * L ^ m₁) (kS + 1) j z) ∨
        ∃ z, (∃ z' ∈ X, jBlock d' L (N₁ * L ^ m₁) (kS + 1) j z =
            jBlock d' L (N₁ * L ^ m₁) (kS + 1) j z') ∧
          ∃ ω ∈ (stepG d' L N₁ m₁ kS ϱ).Ω 1, (ω = x ∨ Adj ω x) ∧
            (stepG d' L N₁ m₁ kS ϱ).pathDist z ω < ENNReal.ofReal (n : ℝ)) →
      q ∈ {q : L1Torus d N₀ | ∃ x : CTorus d' L N₁ m₁ (kS + 1), (e q).1 = unitPt S.hG' x ∧
        ((∃ z ∈ X, jBlock d' L (N₁ * L ^ m₁) (kS + 1) j x =
            jBlock d' L (N₁ * L ^ m₁) (kS + 1) j z) ∨
          ∃ z, (∃ z' ∈ X, jBlock d' L (N₁ * L ^ m₁) (kS + 1) j z =
              jBlock d' L (N₁ * L ^ m₁) (kS + 1) j z') ∧
            ∃ ω ∈ (stepG d' L N₁ m₁ kS ϱ).Ω 1, (ω = x ∨ Adj ω x) ∧
              (stepG d' L N₁ m₁ kS ϱ).pathDist z ω < ENNReal.ofReal (n : ℝ))} :=
  fun _ _ _ _ _ x hq hc => ⟨x, hq, hc⟩


/-- **Reach** (`hreach`): every polymer reaches the region of `C` at the level `Nm`, the torus
diameter bound `d' (N₁ L^{m₁} L^{kS+1}) + 1` (every two sites are at path distance at most
`d' (N₁ L^{m₁} L^{kS+1})`). -/
theorem exists_level_reach (hM : 0 < M) {C : Finset (MacIdx d N₀ M)} (hC : C.Nonempty)
    (Sset : ℕ → ℕ → CTorus d' L N₁ m₁ (kS + 1) → Set (CTorus d' L N₁ m₁ (kS + 1)) →
      Set (L1Torus d N₀))
    (hS : ∀ (n j : ℕ) y X (q : L1Torus d N₀) (x : CTorus d' L N₁ m₁ (kS + 1)),
      (e q).1 = unitPt S.hG' x →
      ((∃ z ∈ X, jBlock d' L (N₁ * L ^ m₁) (kS + 1) j x =
          jBlock d' L (N₁ * L ^ m₁) (kS + 1) j z) ∨
        ∃ z, (∃ z' ∈ X, jBlock d' L (N₁ * L ^ m₁) (kS + 1) j z =
            jBlock d' L (N₁ * L ^ m₁) (kS + 1) j z') ∧
          ∃ ω ∈ (stepG d' L N₁ m₁ kS ϱ).Ω 1, (ω = x ∨ Adj ω x) ∧
            (stepG d' L N₁ m₁ kS ϱ).pathDist z ω < ENNReal.ofReal (n : ℝ)) →
      q ∈ Sset n j y X)
    (j : ℕ) (y : CTorus d' L N₁ m₁ (kS + 1)) (X : Set (CTorus d' L N₁ m₁ (kS + 1))) (hy : y ∈ X) :
    ∃ n ≤ d' * ((N₁ * L ^ m₁) * L ^ (kS + 1)) + 1, ∃ q ∈ Sset n j y X,
      q ∈ macRegion d N₀ M C := by
  obtain ⟨p, hp⟩ := hC
  obtain ⟨q, hq⟩ := macCore_nonempty (d := d) (m := N₀) (M := M) p
  have hqR : q ∈ macRegion d N₀ M C :=
    mem_macRegion.2 ⟨p, hp, macCore_subset_box p hM hq⟩
  obtain ⟨x, hx⟩ := exists_unitPt_eq S (e q).1
  refine ⟨d' * ((N₁ * L ^ m₁) * L ^ (kS + 1)) + 1, le_rfl, q, ?_, hqR⟩
  refine hS _ j y X q x hx.symm (Or.inr ⟨y, ⟨y, hy, rfl⟩, x, S.hG.Ω_one ▸ mem_univ x, Or.inl rfl, ?_⟩)
  refine (pathDist_le_dim_mul (stepG d' L N₁ m₁ kS ϱ) S.hG.Ω_one y x).trans_lt ?_
  rw [ENNReal.ofReal_lt_ofReal_iff (by positivity)]
  push_cast
  linarith


/-- **Sites at each level** (`hW`): a site `z'` of the polymer in an `L^j`-block meeting the read
set is among the sites `w` with `d(x, w) ≤ L^{kS+1} n + d' L^{kS+1} + 1`, `x` a site whose unit
point is that of a point of the region of `C` (torus-distance majorant of the path distance, by
`pathDist_ge_torusDist_top`). -/
theorem exists_mem_level_set {C : Finset (MacIdx d N₀ M)}
    (Sset : ℕ → ℕ → CTorus d' L N₁ m₁ (kS + 1) → Set (CTorus d' L N₁ m₁ (kS + 1)) →
      Set (L1Torus d N₀))
    (hSsub : ∀ (n j : ℕ) y X (q : L1Torus d N₀), q ∈ Sset n j y X →
      ∃ x : CTorus d' L N₁ m₁ (kS + 1), (e q).1 = unitPt S.hG' x ∧
      ((∃ z ∈ X, jBlock d' L (N₁ * L ^ m₁) (kS + 1) j x =
          jBlock d' L (N₁ * L ^ m₁) (kS + 1) j z) ∨
        ∃ z, (∃ z' ∈ X, jBlock d' L (N₁ * L ^ m₁) (kS + 1) j z =
            jBlock d' L (N₁ * L ^ m₁) (kS + 1) j z') ∧
          ∃ ω ∈ (stepG d' L N₁ m₁ kS ϱ).Ω 1, (ω = x ∨ Adj ω x) ∧
            (stepG d' L N₁ m₁ kS ϱ).pathDist z ω < ENNReal.ofReal (n : ℝ)))
    (W : ℕ → Finset (CTorus d' L N₁ m₁ (kS + 1)))
    (hWdef : ∀ n w, w ∈ W n ↔ ∃ x : CTorus d' L N₁ m₁ (kS + 1),
      (∃ q ∈ macRegion d N₀ M C, (e q).1 = unitPt S.hG' x) ∧
        Green.torusDist d' ((N₁ * L ^ m₁) * L ^ (kS + 1)) x w ≤
          ((L ^ (kS + 1) * n + d' * L ^ (kS + 1) + 1 : ℕ) : ℝ))
    (n j : ℕ) (hj : j ≤ kS + 1) (y : CTorus d' L N₁ m₁ (kS + 1))
    (X : Set (CTorus d' L N₁ m₁ (kS + 1)))
    (h : ∃ q ∈ Sset n j y X, q ∈ macRegion d N₀ M C) : ∃ w ∈ W n, w ∈ X := by
  obtain ⟨q, hqS, hqR⟩ := h
  obtain ⟨x, hx, hc⟩ := hSsub n j y X q hqS
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hB : (0 : ℝ) < (L : ℝ) ^ (kS + 1) := by positivity
  have hblk : ∀ a b : CTorus d' L N₁ m₁ (kS + 1),
      jBlock d' L (N₁ * L ^ m₁) (kS + 1) j a = jBlock d' L (N₁ * L ^ m₁) (kS + 1) j b →
      Green.torusDist d' ((N₁ * L ^ m₁) * L ^ (kS + 1)) a b ≤ d' * (L : ℝ) ^ (kS + 1) := by
    intro a b hb
    have h1 := torusDist_le_of_blockMap_eq (d := d') (side_eq (N₀ := N₁ * L ^ m₁) (L := L)
      (k := kS + 1) hj) (pow_pos (NeZero.pos L) j) hb
    refine h1.trans ?_
    push_cast
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL1 hj) (Nat.cast_nonneg _)
  have hxR : ∃ q ∈ macRegion d N₀ M C, (e q).1 = unitPt S.hG' x := ⟨q, hqR, hx⟩
  rcases hc with ⟨z, hz, hb⟩ | ⟨z, ⟨z', hz', hb⟩, ω, hω, hωx, hlt⟩
  · refine ⟨z, (hWdef n z).2 ⟨x, hxR, (hblk x z hb).trans ?_⟩, hz⟩
    push_cast
    have : (0 : ℝ) ≤ (L : ℝ) ^ (kS + 1) * n := by positivity
    linarith
  · refine ⟨z', (hWdef n z').2 ⟨x, hxR, ?_⟩, hz'⟩
    have h1 : Green.torusDist d' ((N₁ * L ^ m₁) * L ^ (kS + 1)) x ω ≤ 1 := by
      rcases hωx with rfl | hadj
      · rw [Green.torusDist_self_eq_zero]; norm_num
      · rw [Green.torusDist_comm_gen]; exact hadj.torusDist_le
    have h2 : Green.torusDist d' ((N₁ * L ^ m₁) * L ^ (kS + 1)) ω z ≤ (L : ℝ) ^ (kS + 1) * n := by
      have h3 := (LargeField.pathDist_ge_torusDist_top (stepG d' L N₁ m₁ kS ϱ) z ω).trans_lt hlt
      have h4 := ((ENNReal.ofReal_lt_ofReal_iff' ).1 h3).1
      rw [Green.torusDist_comm_gen, div_lt_iff₀ hB] at h4
      linarith
    have h5 := hblk z z' hb
    have t1 := Green.torusDist_triangle_gen (d := d') (m := (N₁ * L ^ m₁) * L ^ (kS + 1)) x ω z
    have t2 := Green.torusDist_triangle_gen (d := d') (m := (N₁ * L ^ m₁) * L ^ (kS + 1)) x z z'
    push_cast
    linarith


/-- **The count** `|W n| ≤ Cw (n+1)^{d'}`, `Cw = |C| (8M+1)^d (L^{kS})^{d'} (2 L^{kS+1} + 2 d' L^{kS+1} + 3)^{d'}`:
the region of `C` has at most `|C| (8M+1)^d` points of the macro torus, each unit point has at most
`(L^{kS})^{d'}` sites, and an `ℓ¹` ball of radius `R` has at most `(2R+1)^{d'}` points; the bound does
not depend on the torus size. -/
theorem card_level_set_le (hM : 0 < M) (C : Finset (MacIdx d N₀ M))
    (W : ℕ → Finset (CTorus d' L N₁ m₁ (kS + 1)))
    (hWdef : ∀ n w, w ∈ W n ↔ ∃ x : CTorus d' L N₁ m₁ (kS + 1),
      (∃ q ∈ macRegion d N₀ M C, (e q).1 = unitPt S.hG' x) ∧
        Green.torusDist d' ((N₁ * L ^ m₁) * L ^ (kS + 1)) x w ≤
          ((L ^ (kS + 1) * n + d' * L ^ (kS + 1) + 1 : ℕ) : ℝ)) (n : ℕ) :
    ((W n).card : ℝ) ≤ ((C.card * (8 * M + 1) ^ d * (L ^ kS) ^ d' *
      (2 * L ^ (kS + 1) + 2 * d' * L ^ (kS + 1) + 3) ^ d' : ℕ) : ℝ) * ((n : ℝ) + 1) ^ d' := by
  classical
  set R : Finset (CTorus d' L N₁ m₁ (kS + 1)) := univ.filter fun x =>
    ∃ q ∈ macRegion d N₀ M C, (e q).1 = unitPt S.hG' x with hRdef
  set A : Finset (UnitTorus d' L N₁ m₁ kS) :=
    (C.biUnion (macBoxF d N₀ M)).image fun q => (e q).1.1 with hAdef
  have hA : A.card ≤ C.card * (8 * M + 1) ^ d :=
    card_image_le.trans (card_biUnion_macBoxF_le hM C)
  have hRsub : R ⊆ A.biUnion fun u => univ.filter fun x : CTorus d' L N₁ m₁ (kS + 1) =>
      unitBlock x = u := by
    intro x hx
    obtain ⟨q, hq, hqx⟩ := (mem_filter.1 hx).2
    refine mem_biUnion.2 ⟨(e q).1.1, mem_image.2 ⟨q, mem_biUnion_macBoxF.2 hq, rfl⟩, ?_⟩
    refine mem_filter.2 ⟨mem_univ _, ?_⟩
    rw [hqx]; rfl
  have hR : R.card ≤ C.card * (8 * M + 1) ^ d * (L ^ kS) ^ d' :=
    (Finset.card_le_card hRsub).trans (card_biUnion_le_card_mul _ _ _ fun u _ => card_unitBlock_fiber_le u) |>.trans
      (Nat.mul_le_mul_right _ hA)
  have hWsub : W n ⊆ R.biUnion fun x => univ.filter fun w : CTorus d' L N₁ m₁ (kS + 1) =>
      Green.torusDist d' ((N₁ * L ^ m₁) * L ^ (kS + 1)) x w ≤
        ((L ^ (kS + 1) * n + d' * L ^ (kS + 1) + 1 : ℕ) : ℝ) := by
    intro w hw
    obtain ⟨x, hx, hxw⟩ := (hWdef n w).1 hw
    exact mem_biUnion.2 ⟨x, mem_filter.2 ⟨mem_univ _, hx⟩, mem_filter.2 ⟨mem_univ _, hxw⟩⟩
  have hball := fun x : CTorus d' L N₁ m₁ (kS + 1) => card_torus_ball_le x
    (L ^ (kS + 1) * n + d' * L ^ (kS + 1) + 1)
  have hcard : (W n).card ≤ R.card * (2 * (L ^ (kS + 1) * n + d' * L ^ (kS + 1) + 1) + 1) ^ d' :=
    (Finset.card_le_card hWsub).trans (card_biUnion_le_card_mul _ _ _ fun x _ => hball x)
  have hr : 2 * (L ^ (kS + 1) * n + d' * L ^ (kS + 1) + 1) + 1 ≤
      (2 * L ^ (kS + 1) + 2 * d' * L ^ (kS + 1) + 3) * (n + 1) := by
    generalize L ^ (kS + 1) = B
    nlinarith [Nat.zero_le (d' * B * n), Nat.zero_le B, Nat.zero_le n]
  have h1 : (W n).card ≤ (C.card * (8 * M + 1) ^ d * (L ^ kS) ^ d') *
      ((2 * L ^ (kS + 1) + 2 * d' * L ^ (kS + 1) + 3) * (n + 1)) ^ d' :=
    hcard.trans (Nat.mul_le_mul hR (Nat.pow_le_pow_left hr d'))
  have h2 : ((W n).card : ℝ) ≤ (((C.card * (8 * M + 1) ^ d * (L ^ kS) ^ d') *
      ((2 * L ^ (kS + 1) + 2 * d' * L ^ (kS + 1) + 3) * (n + 1)) ^ d' : ℕ) : ℝ) :=
    Nat.cast_le.2 h1
  refine h2.trans (le_of_eq ?_)
  push_cast
  rw [mul_pow]
  ring

end Step

end Balaban.Green
