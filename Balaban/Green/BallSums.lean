/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Balaban.Frozen.Model.Torus

/-!
# Ball sums on the `ℓ¹` lattice

For `r > 0` put `ballConst d r = ((1 + e^{-r}) / (1 - e^{-r}))^d`.  Then

* `Balaban.Green.ballSum_torus`: on the torus `(ℤ/mℤ)^d` with the `ℓ¹` torus distance
  `∑ᵢ cycDist (xᵢ) (yᵢ)`, `∑_y e^{-r dist x y} ≤ ballConst d r`;
* `Balaban.Green.ballSum_l1Int`: on `ℤ^d` with the `ℓ¹` distance, the same bound for the sum over
  any finite subset.

The types `L1Torus d m` and `L1Int d` carry the corresponding `PseudoMetricSpace` instances, so
that the Combes–Thomas hypothesis `hK` (at `r = δ₀/4`) holds with `κ = ballConst d (δ₀/4)`
(`ballSum_L1Torus`, `ballSum_L1Int_subtype`).
-/

@[expose] public section

open Finset

namespace Balaban.Green

/-- The constant `((1 + e^{-r}) / (1 - e^{-r}))^d` bounding `ℓ¹` ball sums. -/
noncomputable def ballConst (d : ℕ) (r : ℝ) : ℝ :=
  ((1 + Real.exp (-r)) / (1 - Real.exp (-r))) ^ d

/-! ### One-dimensional sums -/

lemma sum_natAbs_le {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (R : ℕ) (S : Finset ℤ)
    (hS : ∀ k ∈ S, k.natAbs ≤ R) : ∑ k ∈ S, q ^ k.natAbs ≤ (1 + q) / (1 - q) := by
  set T : Finset ℤ := (range R).image (fun n : ℕ => ((n + 1 : ℕ) : ℤ)) with hT
  set T' : Finset ℤ := (range R).image (fun n : ℕ => -((n + 1 : ℕ) : ℤ)) with hT'
  have hsub : S ⊆ insert 0 (T ∪ T') := by
    intro k hk
    have := hS k hk
    rcases lt_trichotomy k 0 with h | h | h
    · refine Finset.mem_insert_of_mem (Finset.mem_union_right _ ?_)
      refine Finset.mem_image.2 ⟨k.natAbs - 1, Finset.mem_range.2 (by omega), ?_⟩
      omega
    · simp [h]
    · refine Finset.mem_insert_of_mem (Finset.mem_union_left _ ?_)
      refine Finset.mem_image.2 ⟨k.natAbs - 1, Finset.mem_range.2 (by omega), ?_⟩
      omega
  have hnn : ∀ k : ℤ, 0 ≤ q ^ k.natAbs := fun k => pow_nonneg hq0 _
  have hgeo : ∑ n ∈ range R, q ^ (n + 1) ≤ q / (1 - q) := by
    have h1 : (∑ n ∈ range R, q ^ n) * (1 - q) = 1 - q ^ R := geom_sum_mul_neg q R
    have h2 : 0 < 1 - q := by linarith
    have h3 : ∑ n ∈ range R, q ^ n ≤ 1 / (1 - q) := by
      rw [le_div_iff₀ h2, h1]
      have := pow_nonneg hq0 R
      linarith
    calc ∑ n ∈ range R, q ^ (n + 1) = q * ∑ n ∈ range R, q ^ n := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun n _ => by ring
      _ ≤ q * (1 / (1 - q)) := mul_le_mul_of_nonneg_left h3 hq0
      _ = q / (1 - q) := by ring
  have hTs : ∑ k ∈ T, q ^ k.natAbs = ∑ n ∈ range R, q ^ (n + 1) := by
    rw [hT, Finset.sum_image (fun a _ b _ h => by simpa using h)]
    exact Finset.sum_congr rfl fun n _ => by simp only [Int.natAbs_natCast]
  have hT's : ∑ k ∈ T', q ^ k.natAbs = ∑ n ∈ range R, q ^ (n + 1) := by
    rw [hT', Finset.sum_image (fun a _ b _ h => by simpa using h)]
    exact Finset.sum_congr rfl fun n _ => by simp only [Int.natAbs_neg, Int.natAbs_natCast]
  have hU : ∑ k ∈ T ∪ T', q ^ k.natAbs ≤ ∑ k ∈ T, q ^ k.natAbs + ∑ k ∈ T', q ^ k.natAbs := by
    have := Finset.sum_union_inter (s₁ := T) (s₂ := T') (f := fun k : ℤ => q ^ k.natAbs)
    have h0 : 0 ≤ ∑ k ∈ T ∩ T', q ^ k.natAbs := Finset.sum_nonneg fun k _ => hnn k
    linarith
  calc ∑ k ∈ S, q ^ k.natAbs ≤ ∑ k ∈ insert 0 (T ∪ T'), q ^ k.natAbs :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun k _ _ => hnn k
    _ ≤ 1 + (q / (1 - q) + q / (1 - q)) := by
        have h0 : (0 : ℤ) ∉ T ∪ T' := by
          simp only [hT, hT', Finset.mem_union, Finset.mem_image]
          rintro (⟨n, _, h⟩ | ⟨n, _, h⟩) <;> omega
        rw [Finset.sum_insert h0]
        simp only [Int.natAbs_zero, pow_zero]
        linarith
    _ = (1 + q) / (1 - q) := by
        have : (1 - q) ≠ 0 := by linarith
        field_simp; ring

lemma sum_shift_le {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (x : ℤ) (R : ℕ) (T : Finset ℤ)
    (hT : ∀ a ∈ T, (a - x).natAbs ≤ R) :
    ∑ a ∈ T, q ^ (a - x).natAbs ≤ (1 + q) / (1 - q) := by
  have : ∑ a ∈ T, q ^ (a - x).natAbs = ∑ k ∈ T.image (fun a => a - x), q ^ k.natAbs := by
    rw [Finset.sum_image (fun a _ b _ h => by simpa using h)]
  rw [this]
  refine sum_natAbs_le hq0 hq1 R _ fun k hk => ?_
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hk
  exact hT a ha

/-! ### Cyclic distance on `ZMod m` -/

section Cyc

variable {m : ℕ} [NeZero m]

/-- The representative of `a : ZMod m` of minimal absolute value (in `(-m/2, m/2]`). -/
def cycRep (a : ZMod m) : ℤ := if a.val ≤ m / 2 then (a.val : ℤ) else (a.val : ℤ) - m

lemma cast_cycRep (a : ZMod m) : ((cycRep a : ℤ) : ZMod m) = a := by
  unfold cycRep
  split_ifs
  · simp
  · simp

lemma cycRep_injective : Function.Injective (cycRep (m := m)) := fun a b h => by
  rw [← cast_cycRep a, ← cast_cycRep b, h]

lemma natAbs_cycRep_le (a : ZMod m) : (cycRep a).natAbs ≤ m := by
  have := ZMod.val_lt a
  unfold cycRep; split_ifs <;> omega

/-- Minimality of `cycRep`. -/
lemma natAbs_cycRep_le_of_cast (a : ZMod m) (k : ℤ) (hk : (k : ZMod m) = a) :
    (cycRep a).natAbs ≤ k.natAbs := by
  have hval : ((a.val : ℤ)) = k % m := by
    rw [← hk, ZMod.val_intCast]
  have hm : (0 : ℤ) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  have h1 : k % m + k / m * m = k := by
    have := Int.emod_add_mul_ediv k m
    linarith [mul_comm (m : ℤ) (k / m)]
  have h2 := Int.emod_nonneg k hm.ne'
  have h3 := Int.emod_lt_of_pos k hm
  set j := k / m
  set v := k % m
  have hm2 : (m / 2 : ℕ) * 2 ≤ m := Nat.div_mul_le_self m 2
  have hm3 : m < (m / 2 + 1) * 2 := by omega
  unfold cycRep
  split_ifs with h
  · rw [hval]
    rcases le_or_gt 0 j with hj | hj
    · have : 0 ≤ j * m := mul_nonneg hj hm.le
      omega
    · have : j * m ≤ -m := by nlinarith
      omega
  · rw [hval]
    rcases le_or_gt 0 j with hj | hj
    · have : 0 ≤ j * m := mul_nonneg hj hm.le
      omega
    · have : j * m ≤ -m := by nlinarith
      omega

lemma natAbs_cycRep_add_le (a b : ZMod m) :
    (cycRep (a + b)).natAbs ≤ (cycRep a).natAbs + (cycRep b).natAbs := by
  have := natAbs_cycRep_le_of_cast (a + b) (cycRep a + cycRep b) (by
    push_cast; rw [cast_cycRep, cast_cycRep])
  exact this.trans (Int.natAbs_add_le _ _)

lemma natAbs_cycRep_neg (a : ZMod m) : (cycRep (-a)).natAbs = (cycRep a).natAbs := by
  apply le_antisymm
  · have := natAbs_cycRep_le_of_cast (-a) (-cycRep a) (by push_cast; rw [cast_cycRep])
    simpa using this
  · have := natAbs_cycRep_le_of_cast a (-cycRep (-a)) (by push_cast; rw [cast_cycRep]; simp)
    simpa using this

omit [NeZero m] in
lemma natAbs_cycRep_zero : (cycRep (0 : ZMod m)).natAbs = 0 := by
  simp [cycRep]

lemma sum_cyc_le {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (x : ZMod m) :
    ∑ y : ZMod m, q ^ (cycRep (x - y)).natAbs ≤ (1 + q) / (1 - q) := by
  have e : ∑ y : ZMod m, q ^ (cycRep (x - y)).natAbs = ∑ c : ZMod m, q ^ (cycRep c).natAbs :=
    Fintype.sum_equiv (Equiv.subLeft x) _ _ fun _ => rfl
  rw [e]
  have : ∑ c : ZMod m, q ^ (cycRep c).natAbs
      = ∑ k ∈ (Finset.univ : Finset (ZMod m)).image cycRep, q ^ k.natAbs :=
    (Finset.sum_image (f := fun k : ℤ => q ^ k.natAbs) (g := cycRep)
      (s := (Finset.univ : Finset (ZMod m))) (fun a _ b _ h => cycRep_injective h)).symm
  rw [this]
  refine sum_natAbs_le hq0 hq1 m _ fun k hk => ?_
  obtain ⟨a, _, rfl⟩ := Finset.mem_image.1 hk
  exact natAbs_cycRep_le a

end Cyc

/-! ### The `ℓ¹` torus -/

section Torus

variable (d m : ℕ) [NeZero m]

/-- The `ℓ¹` distance on the torus `(ℤ/mℤ)^d`. -/
noncomputable def torusDist (x y : Balaban.Torus d m) : ℝ :=
  ∑ i, ((cycRep (x i - y i)).natAbs : ℝ)

lemma exp_neg_mul_natCast (r : ℝ) (n : ℕ) : Real.exp (-r * (n : ℝ)) = Real.exp (-r) ^ n := by
  rw [← Real.exp_nat_mul]; ring_nf

lemma exp_one_sub_pos {r : ℝ} (hr : 0 < r) : 0 < Real.exp (-r) ∧ Real.exp (-r) < 1 :=
  ⟨Real.exp_pos _, by rw [← Real.exp_zero]; exact Real.exp_lt_exp.2 (by linarith)⟩

/-- Ball sums on the `ℓ¹` torus: `∑_y e^{-r dist(x,y)} ≤ ((1+e^{-r})/(1-e^{-r}))^d`. -/
theorem ballSum_torus {r : ℝ} (hr : 0 < r) (x : Balaban.Torus d m) :
    ∑ y : Balaban.Torus d m, Real.exp (-r * torusDist d m x y) ≤ ballConst d r := by
  obtain ⟨hq0, hq1⟩ := exp_one_sub_pos hr
  set q := Real.exp (-r) with hq
  have e1 : ∀ y : Balaban.Torus d m, Real.exp (-r * torusDist d m x y) =
      ∏ i, q ^ (cycRep (x i - y i)).natAbs := by
    intro y
    rw [torusDist, Finset.mul_sum, Real.exp_sum]
    exact Finset.prod_congr rfl fun i _ => exp_neg_mul_natCast r _
  simp only [e1]
  have := Finset.prod_univ_sum (fun _ : Fin d => (Finset.univ : Finset (ZMod m)))
    (fun i a => q ^ (cycRep (x i - a)).natAbs)
  rw [Fintype.piFinset_univ] at this
  rw [← this, ballConst]
  calc ∏ i : Fin d, ∑ a : ZMod m, q ^ (cycRep (x i - a)).natAbs
      ≤ ∏ _i : Fin d, (1 + q) / (1 - q) :=
        Finset.prod_le_prod₀ (fun i _ => Finset.sum_nonneg fun a _ => pow_nonneg hq0.le _)
          fun i _ => sum_cyc_le hq0.le hq1 (x i)
    _ = _ := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- The torus `(ℤ/mℤ)^d` with the `ℓ¹` metric. -/
def L1Torus (d m : ℕ) : Type := Balaban.Torus d m

instance : Fintype (L1Torus d m) := inferInstanceAs (Fintype (Balaban.Torus d m))
instance : DecidableEq (L1Torus d m) := inferInstanceAs (DecidableEq (Balaban.Torus d m))

noncomputable instance : PseudoMetricSpace (L1Torus d m) where
  dist x y := torusDist d m x y
  dist_self x := by simp [torusDist, natAbs_cycRep_zero]
  dist_comm x y := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← natAbs_cycRep_neg (x i - y i), neg_sub]
  dist_triangle x y z := by
    show torusDist d m x z ≤ torusDist d m x y + torusDist d m y z
    unfold torusDist
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    have := natAbs_cycRep_add_le (x i - y i) (y i - z i)
    rw [sub_add_sub_cancel] at this
    exact_mod_cast this

lemma dist_L1Torus (x y : L1Torus d m) : dist x y = torusDist d m x y := rfl

/-- The Combes–Thomas ball-sum hypothesis on the `ℓ¹` torus. -/
theorem ballSum_L1Torus {r : ℝ} (hr : 0 < r) (x : L1Torus d m) :
    ∑ y : L1Torus d m, Real.exp (-r * dist x y) ≤ ballConst d r :=
  ballSum_torus d m hr x

end Torus

/-! ### The `ℓ¹` lattice `ℤ^d` -/

section Lattice

variable (d : ℕ)

/-- The `ℓ¹` distance on `ℤ^d`. -/
noncomputable def l1IntDist (x y : Fin d → ℤ) : ℝ := ∑ i, ((x i - y i).natAbs : ℝ)

/-- Ball sums on `ℤ^d` over any finite subset. -/
theorem ballSum_l1Int {r : ℝ} (hr : 0 < r) (x : Fin d → ℤ) (S : Finset (Fin d → ℤ)) :
    ∑ y ∈ S, Real.exp (-r * l1IntDist d x y) ≤ ballConst d r := by
  obtain ⟨hq0, hq1⟩ := exp_one_sub_pos hr
  set q := Real.exp (-r) with hq
  have e1 : ∀ y : Fin d → ℤ, Real.exp (-r * l1IntDist d x y) =
      ∏ i, q ^ (x i - y i).natAbs := by
    intro y
    rw [l1IntDist, Finset.mul_sum, Real.exp_sum]
    exact Finset.prod_congr rfl fun i _ => exp_neg_mul_natCast r _
  simp only [e1]
  set R : ℕ := S.sup fun y => ∑ i, (x i - y i).natAbs with hR
  have hRle : ∀ y ∈ S, ∀ i, (x i - y i).natAbs ≤ R := by
    intro y hy i
    have h1 : (∑ i, (x i - y i).natAbs) ≤ R := Finset.le_sup (f := fun y => ∑ i, (x i - y i).natAbs) hy
    exact (Finset.single_le_sum (f := fun i => (x i - y i).natAbs) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ i)).trans h1
  set B : Finset (Fin d → ℤ) :=
    Fintype.piFinset (fun i => (Finset.Icc (x i - R) (x i + R))) with hB
  have hSB : S ⊆ B := by
    intro y hy
    rw [hB, Fintype.mem_piFinset]
    intro i
    have := hRle y hy i
    rw [Finset.mem_Icc]; omega
  calc ∑ y ∈ S, ∏ i, q ^ (x i - y i).natAbs ≤ ∑ y ∈ B, ∏ i, q ^ (x i - y i).natAbs :=
        Finset.sum_le_sum_of_subset_of_nonneg hSB fun y _ _ =>
          Finset.prod_nonneg fun i _ => pow_nonneg hq0.le _
    _ = ∏ i, ∑ a ∈ Finset.Icc (x i - R) (x i + R), q ^ (x i - a).natAbs :=
        (Finset.prod_univ_sum (fun i => Finset.Icc (x i - R) (x i + R))
          (fun i a => q ^ (x i - a).natAbs)).symm
    _ ≤ ∏ _i : Fin d, (1 + q) / (1 - q) := by
        refine Finset.prod_le_prod₀ (fun i _ => Finset.sum_nonneg fun a _ => pow_nonneg hq0.le _)
          fun i _ => ?_
        have := sum_shift_le hq0.le hq1 (x i) R (Finset.Icc (x i - R) (x i + R)) (fun a ha => by
          rw [Finset.mem_Icc] at ha; omega)
        calc _ = ∑ a ∈ Finset.Icc (x i - R) (x i + R), q ^ (a - x i).natAbs :=
              Finset.sum_congr rfl fun a _ => by rw [← Int.natAbs_neg, neg_sub]
          _ ≤ _ := this
    _ = _ := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ballConst]

/-- The lattice `ℤ^d` with the `ℓ¹` metric. -/
def L1Int (d : ℕ) : Type := Fin d → ℤ

noncomputable instance : PseudoMetricSpace (L1Int d) where
  dist x y := l1IntDist d x y
  dist_self x := by simp [l1IntDist]
  dist_comm x y := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Int.natAbs_neg, neg_sub]
  dist_triangle x y z := by
    show l1IntDist d x z ≤ l1IntDist d x y + l1IntDist d y z
    unfold l1IntDist
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    have := Int.natAbs_add_le (x i - y i) (y i - z i)
    rw [sub_add_sub_cancel] at this
    exact_mod_cast this

instance : DecidableEq (L1Int d) := inferInstanceAs (DecidableEq (Fin d → ℤ))

lemma dist_L1Int (x y : L1Int d) : dist x y = l1IntDist d x y := rfl

/-- The Combes–Thomas ball-sum hypothesis on a finite subset of `ℤ^d` (subtype metric). -/
theorem ballSum_L1Int_subtype {r : ℝ} (hr : 0 < r) (Λ : Finset (L1Int d)) (x : Λ) :
    ∑ y : Λ, Real.exp (-r * dist x y) ≤ ballConst d r := by
  have := ballSum_l1Int d hr (show Fin d → ℤ from x.1) (show Finset (Fin d → ℤ) from Λ)
  rw [← Finset.sum_coe_sort] at this
  exact this

end Lattice

end Balaban.Green
