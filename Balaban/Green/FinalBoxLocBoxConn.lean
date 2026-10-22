/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.FinalBoxLocTies
public import Balaban.Polymer.BlockTorus

/-!
# The boxes of the macro cover are connected (A6-3, item (L4))

The support clause (W3) of the local form needs the regions `R ∪ ⋃_{i ∈ C} B_i` of the rooted
coefficients to be connected sets of blocks, so the boxes `B_z = {x : dist(x, C_z) < 2M}` must be.

* `exists_step_toward`: a site `x ≠ y` has a neighbour one step closer to `y` in the `ℓ¹` torus
  distance;
* `reflTransGen_toward_core`: a site of the box is joined to every core site within distance `2M`
  inside the box;
* `reflTransGen_core`: two sites of the core `C_z` (a product of intervals of residues) are joined
  inside the core, by steps of `±1` of the representatives;
* `isAnimal_macBoxF`: the box `B_z` is a nonempty connected set of the nearest-neighbour graph.
-/

@[expose] public section

namespace Balaban.Green

open Finset

variable {d m M : ℕ} [NeZero m]

/-- The `ℓ¹` torus distance with values in `ℕ`. -/
def natDist (x y : Balaban.Torus d m) : ℕ := ∑ i, (cycRep (x i - y i)).natAbs

omit [NeZero m] in
theorem torusDist_eq_natDist (x y : Balaban.Torus d m) :
    torusDist d m x y = (natDist x y : ℝ) := by
  unfold torusDist natDist
  push_cast
  rfl

theorem eq_of_natDist_eq_zero {x y : Balaban.Torus d m} (h : natDist x y = 0) : x = y := by
  funext i
  have hi : (cycRep (x i - y i)).natAbs = 0 :=
    (Finset.sum_eq_zero_iff.1 h) i (Finset.mem_univ _)
  have h0 : cycRep (x i - y i) = cycRep (0 : ZMod m) := by
    rw [Int.natAbs_eq_zero.1 hi]
    unfold cycRep
    simp
  exact sub_eq_zero.1 (cycRep_injective h0)

omit [NeZero m] in
theorem one_val_of_two_le (hm : 2 ≤ m) : (1 : ZMod m).val = 1 := by
  rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (by omega)]

theorem two_le_of_ne {a b : ZMod m} (h : a ≠ b) : 2 ≤ m := by
  by_contra hm
  have hm1 : m = 1 := by have := NeZero.ne m; omega
  subst hm1
  exact h (Subsingleton.elim a b)

/-- Stepping down: `cycRep (a - 1) = cycRep a - 1` when `cycRep a > 0`. -/
theorem cycRep_sub_one {a : ZMod m} (ha : 0 < cycRep a) : cycRep (a - 1) = cycRep a - 1 := by
  have hv := ZMod.val_lt a
  unfold cycRep at ha ⊢
  by_cases h1 : a.val ≤ m / 2
  · simp only [h1, ↓reduceIte] at ha ⊢
    have ha0 : 0 < a.val := by exact_mod_cast ha
    have hm : 2 ≤ m := by omega
    have hsub : (a - 1).val = a.val - 1 := by
      rw [ZMod.val_sub (by rw [one_val_of_two_le hm]; omega), one_val_of_two_le hm]
    have hc : a.val - 1 ≤ m / 2 := by omega
    rw [hsub]
    simp only [hc, ↓reduceIte]
    rw [Nat.cast_sub (by omega : 1 ≤ a.val)]
    push_cast
    ring
  · simp only [h1, ↓reduceIte] at ha
    exfalso
    omega

/-- Stepping up: `cycRep (a + 1) = cycRep a + 1` when `cycRep a < 0`. -/
theorem cycRep_add_one {a : ZMod m} (ha : cycRep a < 0) : cycRep (a + 1) = cycRep a + 1 := by
  have hv := ZMod.val_lt a
  unfold cycRep at ha ⊢
  by_cases h1 : a.val ≤ m / 2
  · simp only [h1, ↓reduceIte] at ha
    exfalso
    omega
  · simp only [h1, ↓reduceIte] at ha ⊢
    have hm : 2 ≤ m := by omega
    by_cases hlt : a.val + 1 < m
    · have hadd : (a + 1).val = a.val + 1 := by
        rw [ZMod.val_add_of_lt (by rw [one_val_of_two_le hm]; omega), one_val_of_two_le hm]
      have hc : ¬ a.val + 1 ≤ m / 2 := by omega
      rw [hadd]
      simp only [hc, ↓reduceIte]
      push_cast
      ring
    · have heq : a.val + 1 = m := by omega
      have h0 : a + 1 = 0 := by
        rw [← ZMod.natCast_zmod_val a, ← Nat.cast_one, ← Nat.cast_add, heq, ZMod.natCast_self]
      rw [h0, ZMod.val_zero]
      simp only [Nat.zero_le, ↓reduceIte]
      push_cast
      omega

/-- **A step toward `y`**: a site `x ≠ y` has a nearest neighbour `x'` with
`dist(x', y) = dist(x, y) - 1`. -/
theorem exists_step_toward {x y : Balaban.Torus d m} (hxy : x ≠ y) :
    ∃ x', (Polymer.blockGraph d m).Adj x x' ∧ natDist x' y + 1 = natDist x y := by
  obtain ⟨μ, hμ⟩ : ∃ μ, x μ ≠ y μ := by
    by_contra h
    push Not at h
    exact hxy (funext h)
  have hm : 2 ≤ m := two_le_of_ne hμ
  have h10 : (1 : ZMod m) ≠ 0 := by
    intro h
    have := one_val_of_two_le hm
    rw [h, ZMod.val_zero] at this
    omega
  have hne : cycRep (x μ - y μ) ≠ 0 := by
    intro h
    have h0 : cycRep (x μ - y μ) = cycRep (0 : ZMod m) := by
      rw [h]; unfold cycRep; simp
    exact hμ (sub_eq_zero.1 (cycRep_injective h0))
  -- the distance changes only in the coordinate `μ`
  have hsum : ∀ x' : Balaban.Torus d m, (∀ i, i ≠ μ → x' i = x i) →
      (cycRep (x' μ - y μ)).natAbs + 1 = (cycRep (x μ - y μ)).natAbs →
      natDist x' y + 1 = natDist x y := by
    intro x' hx' hμ'
    unfold natDist
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ μ),
      ← Finset.add_sum_erase _ _ (Finset.mem_univ μ)]
    have : ∑ i ∈ Finset.univ.erase μ, (cycRep (x' i - y i)).natAbs =
        ∑ i ∈ Finset.univ.erase μ, (cycRep (x i - y i)).natAbs :=
      Finset.sum_congr rfl fun i hi => by rw [hx' i (Finset.ne_of_mem_erase hi)]
    rw [this]
    omega
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · refine ⟨x + Pi.single μ 1, ⟨?_, μ, Or.inl rfl⟩, hsum _ (fun i hi => by simp [hi]) ?_⟩
    · intro h
      have h2 := congrFun h μ
      simp only [Pi.add_apply, Pi.single_eq_same] at h2
      exact h10 (by linear_combination -h2)
    · have e : (x + Pi.single μ 1 : Balaban.Torus d m) μ - y μ = (x μ - y μ) + 1 := by
        simp only [Pi.add_apply, Pi.single_eq_same]; ring
      rw [e, cycRep_add_one hneg]
      omega
  · refine ⟨x - Pi.single μ 1, ⟨?_, μ, Or.inr (by simp)⟩, hsum _ (fun i hi => by simp [hi]) ?_⟩
    · intro h
      have h2 := congrFun h μ
      simp only [Pi.sub_apply, Pi.single_eq_same] at h2
      exact h10 (by linear_combination h2)
    · have e : (x - Pi.single μ 1 : Balaban.Torus d m) μ - y μ = (x μ - y μ) - 1 := by
        simp only [Pi.sub_apply, Pi.single_eq_same]; ring
      rw [e, cycRep_sub_one hpos]
      omega

theorem reflTransGen_symm_of {α : Type*} {r : α → α → Prop} (hr : ∀ a b, r a b → r b a)
    {a b : α} (h : Relation.ReflTransGen r a b) : Relation.ReflTransGen r b a := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.head (hr _ _ hbc) ih

/-- The relation of the nearest-neighbour steps inside a set of blocks. -/
def stepIn (S : Finset (Balaban.Torus d m)) (a b : Balaban.Torus d m) : Prop :=
  a ∈ S ∧ b ∈ S ∧ (Polymer.blockGraph d m).Adj a b

omit [NeZero m] in
theorem stepIn_symm (S : Finset (Balaban.Torus d m)) (a b : Balaban.Torus d m)
    (h : stepIn S a b) : stepIn S b a :=
  ⟨h.2.1, h.1, h.2.2.symm⟩

/-- **A site of the box is joined inside the box to every core site within distance `2M`.** -/
theorem reflTransGen_toward_core {z : MacIdx d m M} {y : L1Torus d m} (hy : y ∈ macCore d m M z) :
    ∀ n : ℕ, ∀ x : L1Torus d m, natDist (m := m) x y = n → (n : ℝ) < 2 * M →
      Relation.ReflTransGen (stepIn (macBoxF d m M z)) x y := by
  intro n
  induction n with
  | zero =>
    intro x hx _
    obtain rfl := eq_of_natDist_eq_zero hx
    exact Relation.ReflTransGen.refl
  | succ n ih =>
    intro x hx hlt
    have hxy : x ≠ y := by
      intro h; rw [h] at hx
      have : natDist (m := m) y y = 0 := by
        unfold natDist; simp [cycRep]
      omega
    obtain ⟨x', hadj, hd⟩ := exists_step_toward hxy
    have hmem : ∀ u : L1Torus d m, ((natDist (m := m) u y : ℕ) : ℝ) < 2 * M →
        u ∈ macBoxF d m M z := by
      intro u hu
      exact mem_macBoxF.2 (lt_of_le_of_lt (Metric.infDist_le_dist_of_mem hy)
        ((torusDist_eq_natDist (d := d) (m := m) u y).trans_lt hu))
    have hx'n : natDist (m := m) x' y = n := by omega
    have hn : (n : ℝ) < 2 * M := by
      have : (n : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast Nat.le_succ n
      linarith
    refine Relation.ReflTransGen.head ⟨hmem x (by rw [hx]; exact hlt),
      hmem x' (by rw [hx'n]; exact hn), hadj⟩ (ih x' hx'n hn)

/-- The distance of the representatives in the coordinates. -/
def valDist (x y : Balaban.Torus d m) : ℕ := ∑ i, Nat.dist (x i).val (y i).val

omit [NeZero m] in
theorem macCell_mono {a b : ZMod m} (h : a.val ≤ b.val) :
    (macCell m M a : ℕ) ≤ macCell m M b := by
  show min (a.val / M) (macK m M - 1) ≤ min (b.val / M) (macK m M - 1)
  exact min_le_min_right _ (Nat.div_le_div_right h)

/-- The sites of the core `C_z`, as a predicate on the torus. -/
def InCore (z : MacIdx d m M) (y : Balaban.Torus d m) : Prop := ∀ i, macCell m M (y i) = z i

theorem mem_macBoxF_of_inCore (hM : 0 < M) {z : MacIdx d m M} {u : Balaban.Torus d m}
    (hu : InCore z u) : u ∈ macBoxF d m M z :=
  mem_macBoxF.2 (macCore_subset_box z hM (show u ∈ macCore d m M z from hu))

/-- **Two core sites are joined inside the core.** -/
theorem reflTransGen_core (hM : 0 < M) {z : MacIdx d m M} {y' : Balaban.Torus d m}
    (hy' : InCore z y') :
    ∀ n : ℕ, ∀ y : Balaban.Torus d m, valDist (m := m) y y' = n → InCore z y →
      Relation.ReflTransGen (stepIn (macBoxF d m M z)) y y' := by
  intro n
  induction n with
  | zero =>
    intro y hy _
    have : y = y' := by
      funext i
      have hi : Nat.dist (y i).val (y' i).val = 0 :=
        (Finset.sum_eq_zero_iff.1 hy) i (Finset.mem_univ _)
      exact ZMod.val_injective _ (Nat.eq_of_dist_eq_zero hi)
    obtain rfl := this
    exact Relation.ReflTransGen.refl
  | succ n ih =>
    intro y hy hyc
    obtain ⟨μ, hμ⟩ : ∃ μ, (y μ).val ≠ (y' μ).val := by
      by_contra h
      push Not at h
      have : valDist (m := m) y y' = 0 := by
        unfold valDist
        exact Finset.sum_eq_zero fun i _ => by rw [h i, Nat.dist_self]
      omega
    have hm : 2 ≤ m := two_le_of_ne (a := y μ) (b := y' μ) fun h => hμ (by rw [h])
    have h1 := one_val_of_two_le hm
    have hcore : ∀ u : Balaban.Torus d m, (∀ i, i ≠ μ → u i = y i) →
        ((y μ).val ≤ (u μ).val ∧ (u μ).val ≤ (y' μ).val ∨
          (y' μ).val ≤ (u μ).val ∧ (u μ).val ≤ (y μ).val) → InCore z u := by
      intro u hu hbet i
      by_cases hi : i = μ
      · rw [hi]
        have e1 : macCell m M (y μ) = z μ := hyc μ
        have e2 : macCell m M (y' μ) = z μ := hy' μ
        apply Fin.ext
        rcases hbet with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
        · have a1 := macCell_mono (M := M) h₁
          have a2 := macCell_mono (M := M) h₂
          rw [e1] at a1; rw [e2] at a2
          omega
        · have a1 := macCell_mono (M := M) h₁
          have a2 := macCell_mono (M := M) h₂
          rw [e2] at a1; rw [e1] at a2
          omega
      · rw [hu i hi]; exact hyc i
    have hsum : ∀ u : Balaban.Torus d m, (∀ i, i ≠ μ → u i = y i) →
        Nat.dist (u μ).val (y' μ).val + 1 = Nat.dist (y μ).val (y' μ).val →
        valDist (m := m) u y' = n := by
      intro u hu hd
      have : valDist (m := m) u y' + 1 = valDist (m := m) y y' := by
        unfold valDist
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ μ),
          ← Finset.add_sum_erase _ _ (Finset.mem_univ μ)]
        have : ∑ i ∈ Finset.univ.erase μ, Nat.dist (u i).val (y' i).val =
            ∑ i ∈ Finset.univ.erase μ, Nat.dist (y i).val (y' i).val :=
          Finset.sum_congr rfl fun i hi => by rw [hu i (Finset.ne_of_mem_erase hi)]
        rw [this]
        omega
      omega
    rcases lt_or_gt_of_ne hμ with hlt | hgt
    · set u : Balaban.Torus d m := Function.update y μ (y μ + 1) with hudef
      have hu1 : ∀ i, i ≠ μ → u i = y i := fun i hi => by rw [hudef, Function.update_of_ne hi]
      have huμ : (u μ).val = (y μ).val + 1 := by
        rw [hudef, Function.update_self]
        have hv := ZMod.val_lt (y' μ)
        rw [ZMod.val_add_of_lt (by rw [h1]; omega), h1]
      have huc : InCore z u := hcore u hu1 (Or.inl ⟨by omega, by omega⟩)
      have hadj : (Polymer.blockGraph d m).Adj y u := by
        refine ⟨fun h => ?_, μ, Or.inl ?_⟩
        · have : (y μ).val = (u μ).val := by rw [h]
          omega
        · funext i
          by_cases hi : i = μ
          · subst hi
            rw [hudef, Function.update_self]
            simp
          · rw [hudef, Function.update_of_ne hi]
            simp [hi]
      refine Relation.ReflTransGen.head ⟨mem_macBoxF_of_inCore hM hyc,
        mem_macBoxF_of_inCore hM huc, hadj⟩ (ih u (hsum u hu1 ?_) huc)
      unfold Nat.dist
      rw [huμ]
      omega
    · set u : Balaban.Torus d m := Function.update y μ (y μ - 1) with hudef
      have hu1 : ∀ i, i ≠ μ → u i = y i := fun i hi => by rw [hudef, Function.update_of_ne hi]
      have huμ : (u μ).val = (y μ).val - 1 := by
        rw [hudef, Function.update_self]
        rw [ZMod.val_sub (by rw [h1]; omega), h1]
      have huc : InCore z u := hcore u hu1 (Or.inr ⟨by omega, by omega⟩)
      have hadj : (Polymer.blockGraph d m).Adj y u := by
        refine ⟨fun h => ?_, μ, Or.inr ?_⟩
        · have : (y μ).val = (u μ).val := by rw [h]
          omega
        · funext i
          by_cases hi : i = μ
          · subst hi
            simp [hudef]
          · simp [hudef, hi]
      refine Relation.ReflTransGen.head ⟨mem_macBoxF_of_inCore hM hyc,
        mem_macBoxF_of_inCore hM huc, hadj⟩ (ih u (hsum u hu1 ?_) huc)
      unfold Nat.dist
      rw [huμ]
      omega

/-- **The boxes of the macro cover are connected**: `B_z` is a nonempty connected set of blocks. -/
theorem isAnimal_macBoxF (hM : 0 < M) (z : MacIdx d m M) :
    Polymer.IsAnimal (Polymer.blockGraph d m) (macBoxF d m M z) := by
  obtain ⟨y₀, hy₀⟩ := macCore_nonempty (d := d) (m := m) (M := M) z
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have hto : ∀ x ∈ macBoxF d m M z,
      Relation.ReflTransGen (stepIn (macBoxF d m M z)) x y₀ := by
    intro x hx
    have hx' : Metric.infDist x (macCore d m M z) < 2 * M := mem_macBoxF.1 hx
    obtain ⟨y, hy, hxy⟩ := (Metric.infDist_lt_iff (macCore_nonempty z)).1 hx'
    have hxy' : ((natDist (m := m) x y : ℕ) : ℝ) < 2 * M :=
      (torusDist_eq_natDist (d := d) (m := m) x y).symm.trans_lt hxy
    exact (reflTransGen_toward_core hy _ x rfl hxy').trans
      (reflTransGen_core hM (y' := y₀) (fun i => hy₀ i) _ y rfl (fun i => hy i))
  refine (Polymer.isAnimal_iff (H := Polymer.blockGraph d m)
    (macBoxF d m M z : Finset (Balaban.Torus d m))).2
    ⟨⟨y₀, mem_macBoxF.2 (macCore_subset_box z hM hy₀)⟩, fun x hx x' hx' => ?_⟩
  exact (hto x hx).trans (reflTransGen_symm_of (stepIn_symm _) (hto x' hx'))

end Balaban.Green
