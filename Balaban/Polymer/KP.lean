module

public import Balaban.Polymer.Cluster
public import Balaban.Polymer.SeriesIneq
public import Balaban.Polymer.SeriesEq

/-!
# The Kotecký–Preiss bound for the cluster sums
-/

@[expose] public section

noncomputable section

open scoped Classical

open Finset

namespace Balaban.Polymer

section Seq

variable {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]

/-- The normalized solution of the block recursion. -/
def zN (c : ℕ → 𝕜) (n : ℕ) : 𝕜 := ZZ c n / (n.factorial : 𝕜)

theorem zN_zero (c : ℕ → 𝕜) : zN c 0 = 1 := by simp [zN, ZZ_zero]

theorem zz_rec (c : ℕ → 𝕜) (n : ℕ) :
    ((n : 𝕜) + 1) * zN c (n + 1) =
      -∑ m ∈ range (n + 1), ((m : 𝕜) + 1) * (c (m + 1) / ((m + 1).factorial : 𝕜)) * zN c (n - m) := by
  have hn : ((n.factorial : ℕ) : 𝕜) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  rw [zN, ZZ_succ, Nat.factorial_succ]
  push_cast
  have hn1 : ((n : 𝕜) + 1) ≠ 0 := by exact_mod_cast n.succ_ne_zero
  field_simp
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun m hm => ?_)
  have hmn : m ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hm)
  have hm1 : ((m.factorial : ℕ) : 𝕜) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
  have hm2 : (((n - m).factorial : ℕ) : 𝕜) ≠ 0 := by exact_mod_cast (n - m).factorial_ne_zero
  have hm3 : ((m : 𝕜) + 1) ≠ 0 := by exact_mod_cast m.succ_ne_zero
  rw [Nat.cast_choose 𝕜 hmn, zN, Nat.factorial_succ]
  push_cast
  field_simp

end Seq

section Positive

variable {P : Type*} [Fintype P] (inc : P → P → Prop) (κ : P → ℝ)

/-- The nonnegative form `(-1)^n φ^T` of the Ursell function of a cluster of `n+1` polymers. -/
def aaw {n : ℕ} (X : Fin (n + 1) → P) : ℝ := (-1 : ℝ) ^ n * (clusterUrsell inc X Finset.univ : ℝ)

omit [Fintype P] in
theorem aaw_nonneg {n : ℕ} (X : Fin (n + 1) → P) : 0 ≤ aaw inc X := by
  have := ursell_sign (clusterGraph inc X) n Finset.univ (by simp)
  unfold aaw clusterUrsell
  exact_mod_cast this

omit [Fintype P] in
theorem aaw_perm {n : ℕ} (X : Fin (n + 1) → P) (σ : Equiv.Perm (Fin (n + 1))) :
    aaw inc (X ∘ σ) = aaw inc X := by
  unfold aaw
  have := clusterUrsell_comap inc σ.toEmbedding X Finset.univ
  rw [Finset.map_univ_equiv] at this
  rw [show (X ∘ σ) = (X ∘ σ.toEmbedding) from rfl, this]

/-- The block sums `s_n(R)`: clusters of `n+1` polymers, one of which satisfies `R`. -/
def sp (R : P → Prop) (n : ℕ) : ℝ :=
  (((n + 1).factorial : ℕ) : ℝ)⁻¹ * ∑ X : Fin (n + 1) → P,
    (if ∃ i, R (X i) then (1 : ℝ) else 0) * aaw inc X * ∏ i, κ (X i)

theorem sp_nonneg (hκ : ∀ x, 0 ≤ κ x) (R : P → Prop) (n : ℕ) : 0 ≤ sp inc κ R n := by
  unfold sp
  refine mul_nonneg (by positivity) (Finset.sum_nonneg (fun X _ => ?_))
  have := aaw_nonneg inc X
  have : 0 ≤ ∏ i, κ (X i) := Finset.prod_nonneg (fun i _ => hκ _)
  positivity

/-- The rooted sums `z_N(Y)` for the activities `-κ`. -/
def zq (Y : P) (N : ℕ) : ℝ := zN (blkc inc Y (fun x => -κ x)) N

theorem rootedSum_neg (Y : P) (N : ℕ) :
    rootedSum inc Y (fun x => -κ x) N =
      ∑ X' : Fin N → P, aaw inc (Fin.cons Y X' : Fin (N + 1) → P) * ∏ i, κ (X' i) := by
  unfold rootedSum
  refine Finset.sum_congr rfl (fun X' _ => ?_)
  simp only [aaw, Finset.prod_neg, Finset.card_univ, Fintype.card_fin]
  ring

theorem zq_eq (Y : P) (N : ℕ) :
    zq inc κ Y N = (((N.factorial : ℕ) : ℝ))⁻¹ *
      ∑ X' : Fin N → P, aaw inc (Fin.cons Y X' : Fin (N + 1) → P) * ∏ i, κ (X' i) := by
  rw [zq, zN, ← rootedSum_eq, rootedSum_neg, div_eq_inv_mul]

theorem zq_nonneg (hκ : ∀ x, 0 ≤ κ x) (Y : P) (N : ℕ) : 0 ≤ zq inc κ Y N := by
  rw [zq_eq]
  refine mul_nonneg (by positivity) (Finset.sum_nonneg (fun X' _ => ?_))
  have := aaw_nonneg inc (Fin.cons Y X' : Fin (N + 1) → P)
  have : 0 ≤ ∏ i, κ (X' i) := Finset.prod_nonneg (fun i _ => hκ _)
  positivity

theorem blkc_neg (Y : P) (n : ℕ) :
    blkc inc Y (fun x => -κ x) (n + 1) = -(((n + 1).factorial : ℕ) : ℝ) * sp inc κ (lnk inc Y) n := by
  unfold blkc sp
  have hf : (((n + 1).factorial : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (n + 1).factorial_ne_zero
  rw [neg_mul, ← mul_assoc, mul_inv_cancel₀ hf, one_mul, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun X _ => ?_)
  simp only [aaw, Finset.prod_neg, Finset.card_univ, Fintype.card_fin]
  ring

theorem sum_cons_pi {n : ℕ} (g : (Fin (n + 1) → P) → ℝ) :
    ∑ X, g X = ∑ Y : P, ∑ X' : Fin n → P, g (Fin.cons Y X') := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (Fin.consEquiv (fun _ => P)) _ _ (fun _ => rfl)).symm

theorem sum_root_eq (R : P → Prop) (n : ℕ) :
    ∑ X : Fin (n + 1) → P, (if R (X 0) then (1 : ℝ) else 0) * (aaw inc X * ∏ j, κ (X j)) =
      (n.factorial : ℝ) * ∑ Y : P, (if R Y then κ Y else 0) * zq inc κ Y n := by
  rw [sum_cons_pi, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun Y _ => ?_)
  have hf : ((n.factorial : ℕ) : ℝ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  rw [zq_eq]
  by_cases hR : R Y
  · simp only [hR, ite_true, Fin.cons_zero, Fin.prod_univ_succ, Fin.cons_succ, one_mul]
    have : ∑ X' : Fin n → P, aaw inc (Fin.cons Y X' : Fin (n + 1) → P) * (κ Y * ∏ i, κ (X' i)) =
        κ Y * ∑ X' : Fin n → P, aaw inc (Fin.cons Y X' : Fin (n + 1) → P) * ∏ i, κ (X' i) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun _ _ => by ring)
    rw [this]; field_simp
  · simp [hR]

theorem sum_swap_eq (R : P → Prop) (n : ℕ) (i : Fin (n + 1)) :
    ∑ X : Fin (n + 1) → P, (if R (X i) then (1 : ℝ) else 0) * (aaw inc X * ∏ j, κ (X j)) =
    ∑ X : Fin (n + 1) → P, (if R (X 0) then (1 : ℝ) else 0) * (aaw inc X * ∏ j, κ (X j)) := by
  set σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap 0 i with hσ
  let e : (Fin (n + 1) → P) ≃ (Fin (n + 1) → P) := Equiv.arrowCongr σ.symm (Equiv.refl P)
  rw [← Equiv.sum_comp e (fun X => (if R (X 0) then (1 : ℝ) else 0) * (aaw inc X * ∏ j, κ (X j)))]
  refine Finset.sum_congr rfl (fun X _ => ?_)
  have h1 : (e X) = X ∘ σ := by
    ext j; simp [e, Equiv.arrowCongr]
  rw [h1, aaw_perm]
  have h2 : ∏ j, κ ((X ∘ σ) j) = ∏ j, κ (X j) := Equiv.prod_comp σ (fun j => κ (X j))
  rw [h2]
  simp [σ]

theorem sp_le (hκ : ∀ x, 0 ≤ κ x) (R : P → Prop) (n : ℕ) :
    sp inc κ R n ≤ ∑ Y : P, (if R Y then κ Y else 0) * zq inc κ Y n := by
  unfold sp
  have hF : ∀ X : Fin (n + 1) → P, 0 ≤ aaw inc X * ∏ j, κ (X j) := fun X =>
    mul_nonneg (aaw_nonneg inc X) (Finset.prod_nonneg (fun j _ => hκ _))
  have hind : ∀ X : Fin (n + 1) → P, (if ∃ i, R (X i) then (1 : ℝ) else 0) ≤
      ∑ i : Fin (n + 1), (if R (X i) then (1 : ℝ) else 0) := by
    intro X
    by_cases h : ∃ i, R (X i)
    · obtain ⟨i, hi⟩ := h
      simp only [show (∃ i, R (X i)) from ⟨i, hi⟩, ite_true]
      calc (1 : ℝ) = (if R (X i) then (1 : ℝ) else 0) := by simp [hi]
        _ ≤ _ := Finset.single_le_sum (f := fun i => (if R (X i) then (1 : ℝ) else 0))
            (fun _ _ => by split_ifs <;> norm_num) (Finset.mem_univ i)
    · simp only [h, ite_false]
      exact Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num)
  have h1 : ∑ X : Fin (n + 1) → P, (if ∃ i, R (X i) then (1 : ℝ) else 0) * aaw inc X * ∏ i, κ (X i) ≤
      ((n + 1 : ℕ) : ℝ) * (n.factorial : ℝ) * ∑ Y : P, (if R Y then κ Y else 0) * zq inc κ Y n := by
    calc _ ≤ ∑ X : Fin (n + 1) → P, (∑ i : Fin (n + 1), (if R (X i) then (1 : ℝ) else 0)) *
            (aaw inc X * ∏ j, κ (X j)) := by
          refine Finset.sum_le_sum (fun X _ => ?_)
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_right (hind X) (hF X)
      _ = ∑ i : Fin (n + 1), ∑ X : Fin (n + 1) → P,
            (if R (X i) then (1 : ℝ) else 0) * (aaw inc X * ∏ j, κ (X j)) := by
          simp_rw [Finset.sum_mul]; exact Finset.sum_comm
      _ = ∑ i : Fin (n + 1), ∑ X : Fin (n + 1) → P,
            (if R (X 0) then (1 : ℝ) else 0) * (aaw inc X * ∏ j, κ (X j)) :=
          Finset.sum_congr rfl (fun i _ => sum_swap_eq inc κ R n i)
      _ = _ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, sum_root_eq, nsmul_eq_mul]
          push_cast; ring
  have hf : (((n + 1).factorial : ℕ) : ℝ) = ((n : ℝ) + 1) * (n.factorial : ℝ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have hpos : (0 : ℝ) < (((n + 1).factorial : ℕ) : ℝ) := by exact_mod_cast (n + 1).factorial_pos
  calc _ ≤ (((n + 1).factorial : ℕ) : ℝ)⁻¹ * (((n + 1 : ℕ) : ℝ) * (n.factorial : ℝ) *
        ∑ Y : P, (if R Y then κ Y else 0) * zq inc κ Y n) :=
        mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hpos.le)
    _ = _ := by
        rw [hf]; push_cast
        field_simp

theorem exp_bound (hκ : ∀ x, 0 ≤ κ x) (Y : P) (M : ℕ) :
    ∑ n ∈ range (M + 1), zq inc κ Y n ≤
      Real.exp (∑ m ∈ range M, sp inc κ (lnk inc Y) m) := by
  have key := exp_ineq (fun k => sp inc κ (lnk inc Y) (k - 1)) (fun n => zq inc κ Y n)
    (fun k => sp_nonneg inc κ hκ _ _) (by simp [zq, zN_zero]) ?_ M
  · simpa using key
  · intro n
    have h := zz_rec (blkc inc Y (fun x => -κ x)) n
    have h2 : ∀ m : ℕ, blkc inc Y (fun x => -κ x) (m + 1) / (((m + 1).factorial : ℕ) : ℝ) =
        - sp inc κ (lnk inc Y) m := by
      intro m
      have hf : (((m + 1).factorial : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (m + 1).factorial_ne_zero
      rw [blkc_neg]; field_simp
    simp only [zq]
    rw [h]
    simp only [h2, Nat.add_sub_cancel]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    ring

theorem kp_partial (hκ : ∀ x, 0 ≤ κ x) (a : P → ℝ)
    (hKP : ∀ Y, ∑ Y', (if lnk inc Y Y' then κ Y' * Real.exp (a Y') else 0) ≤ a Y) :
    ∀ (M : ℕ) (Y : P), ∑ n ∈ range (M + 1), zq inc κ Y n ≤ Real.exp (a Y) := by
  have ha0 : ∀ Y, 0 ≤ a Y := fun Y => le_trans (Finset.sum_nonneg (fun Y' _ => by
    split_ifs
    · exact mul_nonneg (hκ _) (Real.exp_pos _).le
    · exact le_refl _)) (hKP Y)
  intro M
  induction M with
  | zero =>
    intro Y
    simp only [zero_add, range_one, sum_singleton, zq, zN_zero]
    exact Real.one_le_exp (ha0 Y)
  | succ M ih =>
    intro Y
    refine (exp_bound inc κ hκ Y (M + 1)).trans (Real.exp_le_exp.mpr ?_)
    calc ∑ m ∈ range (M + 1), sp inc κ (lnk inc Y) m
        ≤ ∑ m ∈ range (M + 1), ∑ Y', (if lnk inc Y Y' then κ Y' else 0) * zq inc κ Y' m :=
          Finset.sum_le_sum (fun m _ => sp_le inc κ hκ _ m)
      _ = ∑ Y', (if lnk inc Y Y' then κ Y' else 0) * ∑ m ∈ range (M + 1), zq inc κ Y' m := by
          rw [Finset.sum_comm]
          simp_rw [Finset.mul_sum]
      _ ≤ ∑ Y', (if lnk inc Y Y' then κ Y' * Real.exp (a Y') else 0) := by
          refine Finset.sum_le_sum (fun Y' _ => ?_)
          by_cases h : lnk inc Y Y'
          · simp only [h, ite_true]
            exact mul_le_mul_of_nonneg_left (ih Y') (hκ _)
          · simp [h]
      _ ≤ a Y := hKP Y

theorem sp_sum_le (hκ : ∀ x, 0 ≤ κ x) (a : P → ℝ)
    (hKP : ∀ Y, ∑ Y', (if lnk inc Y Y' then κ Y' * Real.exp (a Y') else 0) ≤ a Y)
    (R : P → Prop) (M : ℕ) :
    ∑ m ∈ range M, sp inc κ R m ≤ ∑ Y, (if R Y then κ Y * Real.exp (a Y) else 0) := by
  calc ∑ m ∈ range M, sp inc κ R m
      ≤ ∑ m ∈ range M, ∑ Y, (if R Y then κ Y else 0) * zq inc κ Y m :=
        Finset.sum_le_sum (fun m _ => sp_le inc κ hκ R m)
    _ = ∑ Y, (if R Y then κ Y else 0) * ∑ m ∈ range M, zq inc κ Y m := by
        rw [Finset.sum_comm]
        simp_rw [Finset.mul_sum]
    _ ≤ _ := by
        refine Finset.sum_le_sum (fun Y _ => ?_)
        by_cases h : R Y
        · simp only [h, ite_true]
          refine mul_le_mul_of_nonneg_left ?_ (hκ _)
          rcases M with _ | M
          · simp only [range_zero, sum_empty]; exact (Real.exp_pos _).le
          · exact kp_partial inc κ hκ a hKP M Y
        · simp [h]

end Positive

end Balaban.Polymer
