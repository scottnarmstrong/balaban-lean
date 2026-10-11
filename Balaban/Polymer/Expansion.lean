module

public import Balaban.Polymer.KP

/-!
# The cluster expansion `Ξ = exp L`

For a finite set `P` of polymers with an incompatibility relation `inc`, activities
`K : P → ℂ`, the partition function `Xi inc K` is the sum over pairwise compatible sets of the
products of activities, and `logSeries inc K` is the cluster sum with Ursell function weights.
-/

@[expose] public section

noncomputable section

open scoped Classical

open Finset

namespace Balaban.Polymer

variable {P : Type*} [Fintype P] (inc : P → P → Prop)

/-- Pairwise compatible families. -/
def Compat (Γ : Finset P) : Prop := ∀ x ∈ Γ, ∀ y ∈ Γ, x ≠ y → ¬ lnk inc x y

/-- The partition function of the polymer gas. -/
def Xi (K : P → ℂ) : ℂ := ∑ Γ ∈ (Finset.univ : Finset (Finset P)).filter (Compat inc), ∏ X ∈ Γ, K X

/-- The cluster term of order `n + 1`. -/
def clTerm (K : P → ℂ) (n : ℕ) : ℂ :=
  (((n + 1).factorial : ℕ) : ℂ)⁻¹ *
    ∑ X : Fin (n + 1) → P, (clusterUrsell inc X Finset.univ : ℂ) * ∏ i, K (X i)

/-- The cluster sum. -/
def logSeries (K : P → ℂ) : ℂ := ∑' n, clTerm inc K n

variable (κ : P → ℝ)

omit [Fintype P] in
theorem norm_ursell_eq {n : ℕ} (X : Fin (n + 1) → P) :
    ‖(clusterUrsell inc X Finset.univ : ℂ)‖ = aaw inc X := by
  have h0 := aaw_nonneg inc X
  have : aaw inc X = (-1 : ℝ) ^ n * (clusterUrsell inc X Finset.univ : ℝ) := rfl
  rw [Complex.norm_intCast, ← abs_of_nonneg h0, this, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
    one_mul]

theorem norm_clTerm_le (K : P → ℂ) (hK : ∀ x, ‖K x‖ ≤ κ x) (n : ℕ) :
    ‖clTerm inc K n‖ ≤ sp inc κ (fun _ => True) n := by
  unfold clTerm sp
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun X _ => ?_))
  rw [norm_mul, norm_ursell_eq, norm_prod]
  have hex : (∃ i : Fin (n + 1), True) := ⟨0, trivial⟩
  simp only [hex, ite_true, one_mul]
  exact mul_le_mul_of_nonneg_left (Finset.prod_le_prod₀ (fun i _ => norm_nonneg _)
    (fun i _ => hK _)) (aaw_nonneg inc X)

theorem clTerm_smul (K : P → ℂ) (c : ℂ) (n : ℕ) :
    clTerm inc (fun x => c * K x) n = c ^ (n + 1) * clTerm inc K n := by
  unfold clTerm
  have : ∀ X : Fin (n + 1) → P, ∏ i, (c * K (X i)) = c ^ (n + 1) * ∏ i, K (X i) := by
    intro X; rw [Finset.prod_mul_distrib]; simp
  simp_rw [this]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun X _ => ?_)
  ring

theorem clTerm_eq_root (K : P → ℂ) (n : ℕ) :
    ((n : ℂ) + 1) * clTerm inc K n = ∑ Y, K Y * zN (blkc inc Y K) n := by
  unfold clTerm
  rw [sum_cons_pi]
  have hf : ((n.factorial : ℕ) : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have hn : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast n.succ_ne_zero
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun Y _ => ?_)
  rw [zN, ← rootedSum_eq, rootedSum]
  have : ∑ X' : Fin n → P, (clusterUrsell inc (Fin.cons Y X' : Fin (n + 1) → P) Finset.univ : ℂ) *
      ∏ i, K ((Fin.cons Y X' : Fin (n + 1) → P) i) =
      K Y * ∑ X' : Fin n → P, (clusterUrsell inc (Fin.cons Y X' : Fin (n + 1) → P) Finset.univ : ℂ) *
        ∏ i, K (X' i) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun X' _ => ?_)
    rw [Fin.prod_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    ring
  rw [this, Nat.factorial_succ]
  push_cast
  field_simp

/-- The Kotecký–Preiss hypothesis with weights `κ` and `a`. -/
structure KPCond (κ a : P → ℝ) : Prop where
  nonneg : ∀ x, 0 ≤ κ x
  bound : ∀ Y, ∑ Y', (if lnk inc Y Y' then κ Y' * Real.exp (a Y') else 0) ≤ a Y

variable {κ} {a : P → ℝ}

theorem summable_sp (h : KPCond inc κ a) (R : P → Prop) : Summable (sp inc κ R) :=
  summable_of_sum_range_le (fun n => sp_nonneg inc κ h.nonneg R n)
    (fun M => sp_sum_le inc κ h.nonneg a h.bound R M)

theorem summable_zq (h : KPCond inc κ a) (Y : P) : Summable (zq inc κ Y) := by
  refine summable_of_sum_range_le (c := Real.exp (a Y)) (fun n => zq_nonneg inc κ h.nonneg Y n)
    (fun M => ?_)
  rcases M with _ | M
  · simp only [range_zero, sum_empty]; exact (Real.exp_pos _).le
  · exact kp_partial inc κ h.nonneg a h.bound M Y

/-- Restriction of the activities to the polymers compatible with `Y`. -/
def Kc (Y : P) (K : P → ℂ) : P → ℂ := fun x => if lnk inc Y x then 0 else K x

omit [Fintype P] in
theorem prod_Kc {n : ℕ} (Y : P) (K : P → ℂ) (X : Fin n → P) :
    ∏ i, Kc inc Y K (X i) = if (∃ i, lnk inc Y (X i)) then 0 else ∏ i, K (X i) := by
  by_cases h : ∃ i, lnk inc Y (X i)
  · obtain ⟨i, hi⟩ := h
    simp only [show (∃ i, lnk inc Y (X i)) from ⟨i, hi⟩, ite_true]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [Kc, hi])
  · simp only [h, ite_false]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    have : ¬ lnk inc Y (X i) := fun hh => h ⟨i, hh⟩
    simp [Kc, this]

theorem clTerm_sub_Kc (Y : P) (K : P → ℂ) (n : ℕ) :
    clTerm inc K n - clTerm inc (Kc inc Y K) n =
      blkc inc Y K (n + 1) / (((n + 1).factorial : ℕ) : ℂ) := by
  unfold clTerm blkc
  rw [← mul_sub, div_eq_inv_mul, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl (fun X _ => ?_)
  rw [prod_Kc]
  by_cases h : ∃ i, lnk inc Y (X i)
  · simp [h]
  · simp [h]

theorem norm_rootedSum_le (K : P → ℂ) (hK : ∀ x, ‖K x‖ ≤ κ x) (Y : P) (N : ℕ) :
    ‖rootedSum inc Y K N‖ ≤ rootedSum inc Y (fun x => -κ x) N := by
  rw [rootedSum_neg]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun X' _ => ?_))
  rw [norm_mul, norm_ursell_eq, norm_prod]
  exact mul_le_mul_of_nonneg_left (Finset.prod_le_prod₀ (fun i _ => norm_nonneg _)
    (fun i _ => hK _)) (aaw_nonneg inc _)

theorem norm_zN_le (K : P → ℂ) (hK : ∀ x, ‖K x‖ ≤ κ x) (Y : P) (N : ℕ) :
    ‖zN (blkc inc Y K) N‖ ≤ zq inc κ Y N := by
  rw [zN, ← rootedSum_eq, zq, zN, ← rootedSum_eq, norm_div, Complex.norm_natCast, div_eq_inv_mul,
    div_eq_inv_mul]
  refine mul_le_mul_of_nonneg_left (norm_rootedSum_le inc K hK Y N) (by positivity)

theorem norm_blkc_le (K : P → ℂ) (hK : ∀ x, ‖K x‖ ≤ κ x) (Y : P) (n : ℕ) :
    ‖blkc inc Y K (n + 1) / (((n + 1).factorial : ℕ) : ℂ)‖ ≤ sp inc κ (lnk inc Y) n := by
  rw [norm_div, Complex.norm_natCast, div_eq_inv_mul, sp]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  unfold blkc
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun X _ => ?_))
  rw [norm_mul, norm_mul, norm_ursell_eq, norm_prod]
  by_cases h : ∃ i, lnk inc Y (X i)
  · simp only [h, ite_true, norm_one, one_mul]
    exact mul_le_mul_of_nonneg_left (Finset.prod_le_prod₀ (fun i _ => norm_nonneg _)
      (fun i _ => hK _)) (aaw_nonneg inc X)
  · simp [h]

theorem Q_exp (h : KPCond inc κ a) (K : P → ℂ) (hK : ∀ x, ‖K x‖ ≤ κ x) (Y : P) :
    ∑' n, zN (blkc inc Y K) n = Complex.exp (logSeries inc (Kc inc Y K) - logSeries inc K) := by
  have hKc : ∀ x, ‖Kc inc Y K x‖ ≤ κ x := fun x => by
    unfold Kc; split_ifs
    · simpa using (le_trans (norm_nonneg _) (hK x))
    · exact hK x
  have hsz : Summable (fun n => ‖zN (blkc inc Y K) n‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_zN_le inc K hK Y) (summable_zq inc h Y)
  set aa : ℕ → ℂ := fun n => if n = 0 then 0 else blkc inc Y K n / ((n.factorial : ℕ) : ℂ) with haa
  have haa1 : ∀ n, aa (n + 1) = blkc inc Y K (n + 1) / (((n + 1).factorial : ℕ) : ℂ) := by
    intro n; simp [haa]
  have hsa : Summable (fun n => ‖aa n‖) := by
    rw [← summable_nat_add_iff 1]
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_) (summable_sp inc h (lnk inc Y))
    rw [haa1]; exact norm_blkc_le inc K hK Y n
  have hmain := exp_eq aa (fun n => zN (blkc inc Y K) n) (by simp [haa]) (zN_zero _)
    (fun n => by
      rw [zz_rec]
      simp only [haa1])
    hsa hsz
  rw [hmain]
  congr 1
  have hs1 : Summable (fun n => clTerm inc K n) :=
    Summable.of_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (norm_clTerm_le inc κ K hK) (summable_sp inc h (fun _ => True)))
  have hs2 : Summable (fun n => clTerm inc (Kc inc Y K) n) :=
    Summable.of_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (norm_clTerm_le inc κ (Kc inc Y K) hKc) (summable_sp inc h (fun _ => True)))
  rw [logSeries, logSeries, ← Summable.tsum_sub hs2 hs1]
  have e1 : ∑' n, aa n = ∑' n, aa (n + 1) := by
    rw [hsa.of_norm.tsum_eq_zero_add]; simp [haa]
  have e2 : ∑' n, aa (n + 1) = ∑' n, (clTerm inc K n - clTerm inc (Kc inc Y K) n) :=
    tsum_congr (fun n => by rw [haa1, clTerm_sub_Kc])
  rw [e1, e2, ← tsum_neg]
  exact tsum_congr (fun n => (neg_sub _ _))

end Balaban.Polymer
