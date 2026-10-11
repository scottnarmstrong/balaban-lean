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

section XiDeriv

variable (hrefl : ∀ x, inc x x)

omit [Fintype P] in
theorem lnk_refl (hrefl : ∀ x, inc x x) (x : P) : lnk inc x x := Or.inl (hrefl x)

theorem Xi_smul (K : P → ℂ) (s : ℂ) :
    Xi inc (fun x => s * K x) =
      ∑ Γ ∈ (Finset.univ : Finset (Finset P)).filter (Compat inc), s ^ Γ.card * ∏ X ∈ Γ, K X := by
  unfold Xi
  refine Finset.sum_congr rfl (fun Γ _ => ?_)
  rw [Finset.prod_mul_distrib, Finset.prod_const]

theorem Xi_deriv_identity (hrefl : ∀ x, inc x x) (K : P → ℂ) (s : ℂ) :
    ∑ Γ ∈ (Finset.univ : Finset (Finset P)).filter (Compat inc),
        (Γ.card : ℂ) * s ^ (Γ.card - 1) * ∏ X ∈ Γ, K X =
      ∑ Y, K Y * Xi inc (fun x => s * Kc inc Y K x) := by
  set C := (Finset.univ : Finset (Finset P)).filter (Compat inc) with hC
  have hL : ∀ Γ ∈ C, (Γ.card : ℂ) * s ^ (Γ.card - 1) * ∏ X ∈ Γ, K X =
      ∑ Y ∈ Γ, s ^ (Γ.card - 1) * ∏ X ∈ Γ, K X := by
    intro Γ _
    rw [Finset.sum_const, nsmul_eq_mul]; ring
  rw [Finset.sum_congr rfl hL]
  rw [Finset.sum_comm' (t' := Finset.univ) (s' := fun Y => C.filter (fun Γ => Y ∈ Γ))
    (fun Γ Y => by simp [and_comm])]
  refine Finset.sum_congr rfl (fun Y _ => ?_)
  -- the rooted sum for `Y`
  have hA : Xi inc (fun x => s * Kc inc Y K x) =
      ∑ Γ' ∈ C.filter (fun Γ' => ∀ X ∈ Γ', ¬ lnk inc Y X), s ^ Γ'.card * ∏ X ∈ Γ', K X := by
    rw [Xi_smul]
    conv_rhs => rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun Γ' _ => ?_)
    by_cases h : ∀ X ∈ Γ', ¬ lnk inc Y X
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h)]
      congr 1
      exact Finset.prod_congr rfl (fun X hX => by simp [Kc, h X hX])
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h)]
      obtain ⟨X, hX, hl⟩ : ∃ X ∈ Γ', lnk inc Y X := by
        by_contra hcon
        exact h (fun X hX hl => hcon ⟨X, hX, hl⟩)
      rw [Finset.prod_eq_zero hX (by simp [Kc, hl]), mul_zero]
  rw [hA, Finset.mul_sum]
  have hYnot : ∀ Γ' ∈ C.filter (fun Γ' => ∀ X ∈ Γ', ¬ lnk inc Y X), Y ∉ Γ' := fun Γ' hΓ' hY =>
    (Finset.mem_filter.mp hΓ').2 Y hY (lnk_refl inc hrefl Y)
  refine Finset.sum_nbij' (fun Γ => Γ.erase Y) (fun Γ' => insert Y Γ') ?_ ?_ ?_ ?_ ?_
  · intro Γ hΓ
    simp only [hC, Finset.mem_filter, Finset.mem_univ, true_and] at hΓ ⊢
    obtain ⟨hcomp, hY⟩ := hΓ
    refine ⟨fun x hx y hy hxy => hcomp x (Finset.mem_of_mem_erase hx) y (Finset.mem_of_mem_erase hy) hxy, ?_⟩
    intro X hX
    exact hcomp Y hY X (Finset.mem_of_mem_erase hX) (Finset.ne_of_mem_erase hX).symm
  · intro Γ' hΓ'
    have hY := hYnot Γ' hΓ'
    simp only [hC, Finset.mem_filter, Finset.mem_univ, true_and] at hΓ' ⊢
    obtain ⟨hcomp, hl⟩ := hΓ'
    refine ⟨?_, Finset.mem_insert_self _ _⟩
    intro x hx y hy hxy
    rcases Finset.mem_insert.mp hx with rfl | hx'
    · rcases Finset.mem_insert.mp hy with rfl | hy'
      · exact absurd rfl hxy
      · exact hl y hy'
    · rcases Finset.mem_insert.mp hy with rfl | hy'
      · exact fun h => hl x hx' ((lnk_symm inc _ _).mp h)
      · exact hcomp x hx' y hy' hxy
  · intro Γ hΓ
    simp only [Finset.mem_filter] at hΓ
    exact Finset.insert_erase hΓ.2
  · intro Γ' hΓ'
    exact Finset.erase_insert (hYnot Γ' hΓ')
  · intro Γ hΓ
    simp only [Finset.mem_filter] at hΓ
    rw [Finset.card_erase_of_mem hΓ.2, ← Finset.mul_prod_erase Γ K hΓ.2]
    ring

end XiDeriv

section LogDeriv

variable (h : KPCond inc κ a)

omit [Fintype P] in
theorem Kc_smul (Y : P) (K : P → ℂ) (c : ℂ) :
    Kc inc Y (fun x => c * K x) = fun x => c * Kc inc Y K x := by
  funext x; unfold Kc; split_ifs <;> simp

theorem zN_smul (Y : P) (K : P → ℂ) (c : ℂ) (n : ℕ) :
    zN (blkc inc Y (fun x => c * K x)) n = c ^ n * zN (blkc inc Y K) n := by
  have hp : ∀ X' : Fin n → P, ∏ i, (c * K (X' i)) = c ^ n * ∏ i, K (X' i) := by
    intro X'; rw [Finset.prod_mul_distrib]; simp
  have : rootedSum inc Y (fun x => c * K x) n = c ^ n * rootedSum inc Y K n := by
    unfold rootedSum
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun X' _ => by rw [hp]; ring)
  rw [zN, zN, ← rootedSum_eq, ← rootedSum_eq, this, mul_div_assoc]

/-- The coefficients of `s ↦ logSeries (s K)` as a power series in `s`. -/
def ccSeq (K : P → ℂ) (m : ℕ) : ℂ := if m = 0 then 0 else clTerm inc K (m - 1)

theorem ccSeq_succ (K : P → ℂ) (n : ℕ) : ccSeq inc K (n + 1) = clTerm inc K n := by
  simp [ccSeq]

include h in
theorem summable_ccSeq (K : P → ℂ) (hK : ∀ x, ‖K x‖ ≤ κ x) :
    Summable (fun m => ‖ccSeq inc K m‖) := by
  have hnorm : Summable (fun n => ‖clTerm inc K n‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_clTerm_le inc κ K hK)
      (summable_sp inc h (fun _ => True))
  rw [← summable_nat_add_iff 1]
  simpa [ccSeq_succ] using hnorm

include h in
theorem logSeries_smul_eq (K : P → ℂ) (hK : ∀ x, ‖K x‖ ≤ κ x) {y : ℝ} (hy : |y| ≤ 1) :
    logSeries inc (fun x => (y : ℂ) * K x) = ∑' m, ccSeq inc K m * (y : ℂ) ^ m := by
  have hsy : Summable (fun m => ccSeq inc K m * (y : ℂ) ^ m) := by
    refine Summable.of_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun m => ?_)
      (summable_ccSeq inc h K hK))
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (abs_nonneg _) hy)
  rw [hsy.tsum_eq_zero_add]
  simp only [ccSeq, logSeries, clTerm_smul]
  simp only [Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel, pow_zero, mul_one, ite_true,
    zero_add]
  exact tsum_congr (fun n => mul_comm _ _)

include h in
theorem continuousOn_logSeries (K : P → ℂ) (hK : ∀ x, ‖K x‖ ≤ κ x) :
    ContinuousOn (fun y : ℝ => logSeries inc (fun x => (y : ℂ) * K x)) (Set.Icc 0 1) := by
  refine (continuousOn_powSeries (ccSeq inc K) (summable_ccSeq inc h K hK)).congr (fun y hy => ?_)
  exact logSeries_smul_eq inc h K hK (abs_le.mpr ⟨by linarith [hy.1], hy.2⟩)

include h in
theorem hasDerivAt_logSeries (K : P → ℂ) (hK : ∀ x, ‖K x‖ ≤ κ x) {s : ℝ} (hs : |s| < 1) :
    HasDerivAt (fun y : ℝ => logSeries inc (fun x => (y : ℂ) * K x))
      (∑ Y, K Y * ∑' n, zN (blkc inc Y (fun x => (s : ℂ) * K x)) n) s := by
  have hsum := summable_ccSeq inc h K hK
  have hD := hasDerivAt_powSeries (ccSeq inc K) hsum hs
  have hev : (fun y : ℝ => logSeries inc (fun x => (y : ℂ) * K x)) =ᶠ[nhds s]
      (fun y : ℝ => ∑' m, ccSeq inc K m * (y : ℂ) ^ m) := by
    have : {y : ℝ | |y| < 1} ∈ nhds s := (isOpen_lt continuous_abs continuous_const).mem_nhds hs
    filter_upwards [this] with y hy using logSeries_smul_eq inc h K hK hy.le
  refine (hD.congr_of_eventuallyEq hev).congr_deriv ?_
  rw [tsum_deriv_shift (ccSeq inc K) hsum hs]
  have hk : ∀ Y, Summable (fun n => K Y * zN (blkc inc Y (fun x => (s : ℂ) * K x)) n) := by
    intro Y
    have hKs : ∀ x, ‖(s : ℂ) * K x‖ ≤ κ x := fun x => by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      calc |s| * ‖K x‖ ≤ 1 * ‖K x‖ := mul_le_mul_of_nonneg_right hs.le (norm_nonneg _)
        _ ≤ κ x := by rw [one_mul]; exact hK x
    refine Summable.mul_left _ (Summable.of_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (norm_zN_le inc _ hKs Y) (summable_zq inc h Y)))
  have : ∀ n : ℕ, ((n : ℂ) + 1) * ccSeq inc K (n + 1) * (s : ℂ) ^ n =
      ∑ Y, K Y * zN (blkc inc Y (fun x => (s : ℂ) * K x)) n := by
    intro n
    rw [ccSeq_succ, clTerm_eq_root, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun Y _ => ?_)
    rw [zN_smul]; ring
  simp_rw [this]
  rw [Summable.tsum_finsetSum (fun Y _ => hk Y)]
  refine Finset.sum_congr rfl (fun Y _ => ?_)
  rw [tsum_mul_left]

end LogDeriv

section Main

variable (h : KPCond inc κ a) (hrefl : ∀ x, inc x x)

include h hrefl in
theorem xi_eq_exp_aux : ∀ (N : ℕ) (K : P → ℂ), (∀ x, ‖K x‖ ≤ κ x) →
    (Finset.univ.filter (fun x => K x ≠ 0)).card = N →
      Xi inc K = Complex.exp (logSeries inc K) := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro K hK hN
  set C : Finset (Finset P) := (Finset.univ : Finset (Finset P)).filter (Compat inc) with hC
  set Ψ : ℝ → ℂ := fun s => Xi inc (fun x => (s : ℂ) * K x) with hΨ
  set Φ : ℝ → ℂ := fun s => Complex.exp (logSeries inc (fun x => (s : ℂ) * K x)) with hΦ
  have hKs : ∀ s : ℝ, |s| ≤ 1 → ∀ x, ‖(s : ℂ) * K x‖ ≤ κ x := fun s hs x => by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc |s| * ‖K x‖ ≤ 1 * ‖K x‖ := mul_le_mul_of_nonneg_right hs (norm_nonneg _)
      _ ≤ κ x := by rw [one_mul]; exact hK x
  have hdΨ : ∀ s : ℝ, HasDerivAt Ψ
      (∑ Y, K Y * Xi inc (fun x => (s : ℂ) * Kc inc Y K x)) s := by
    intro s
    have hform : Ψ = fun s : ℝ => ∑ Γ ∈ C, (s : ℂ) ^ Γ.card * ∏ X ∈ Γ, K X :=
      funext (fun s => Xi_smul inc K (s : ℂ))
    rw [hform]
    have := HasDerivAt.fun_sum (u := C) (x := s)
      (A := fun (Γ : Finset P) (y : ℝ) => (y : ℂ) ^ Γ.card * ∏ X ∈ Γ, K X)
      (A' := fun (Γ : Finset P) => (Γ.card : ℂ) * (s : ℂ) ^ (Γ.card - 1) * ∏ X ∈ Γ, K X)
      (fun Γ _ => ((hasDerivAt_pow Γ.card (s : ℂ)).comp_ofReal).mul_const (∏ X ∈ Γ, K X))
    rw [← Xi_deriv_identity inc hrefl K (s : ℂ)]
    exact this
  have hdΦ : ∀ s : ℝ, |s| < 1 → HasDerivAt Φ
      (∑ Y, K Y * Xi inc (fun x => (s : ℂ) * Kc inc Y K x)) s := by
    intro s hs
    have hL := hasDerivAt_logSeries inc h K hK hs
    have := hL.cexp
    convert this using 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun Y _ => ?_)
    by_cases hKY : K Y = 0
    · simp [hKY]
    · rw [Q_exp inc h (fun x => (s : ℂ) * K x) (hKs s hs.le) Y, Kc_smul]
      have hKc' : ∀ x, ‖(s : ℂ) * Kc inc Y K x‖ ≤ κ x := fun x => by
        have := hKs s hs.le x
        unfold Kc
        split_ifs
        · simpa using (le_trans (norm_nonneg _) (hK x))
        · exact this
      have hY : Y ∈ Finset.univ.filter (fun x => K x ≠ 0) := by simp [hKY]
      have hsub : Finset.univ.filter (fun x => (s : ℂ) * Kc inc Y K x ≠ 0) ⊆
          (Finset.univ.filter (fun x => K x ≠ 0)).erase Y := by
        intro x hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, ne_eq, mul_eq_zero, not_or] at hx
        simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨?_, ?_⟩
        · rintro rfl
          exact hx.2 (by simp [Kc, lnk_refl inc hrefl x])
        · intro hx0
          exact hx.2 (by simp [Kc, hx0])
      have hlt : (Finset.univ.filter (fun x => (s : ℂ) * Kc inc Y K x ≠ 0)).card < N := by
        refine (Finset.card_le_card hsub).trans_lt ?_
        rw [Finset.card_erase_of_mem hY, hN]
        have : 0 < N := hN ▸ Finset.card_pos.mpr ⟨Y, hY⟩
        omega
      rw [ih _ hlt _ hKc' rfl, Complex.exp_sub]
      have := Complex.exp_ne_zero (logSeries inc (fun x => (s : ℂ) * K x))
      field_simp
  have hΨ0 : Ψ 0 = 1 := by
    simp only [hΨ, Xi_smul, Complex.ofReal_zero]
    rw [Finset.sum_eq_single ∅]
    · simp
    · intro Γ _ hΓ
      rw [zero_pow (Finset.card_ne_zero.mpr (Finset.nonempty_iff_ne_empty.mpr hΓ)), zero_mul]
    · intro hmem
      exact absurd (by simp [Compat]) hmem
  have hΦ0 : Φ 0 = 1 := by
    simp only [hΦ, logSeries, clTerm_smul, Complex.ofReal_zero]
    simp
  have hD : ∀ s ∈ Set.Ioo (-1 : ℝ) 1, Ψ s = Φ s := by
    intro s hs
    have hconst := IsOpen.is_const_of_deriv_eq_zero (f := fun y => Ψ y - Φ y) isOpen_Ioo
      isPreconnected_Ioo
      (fun y hy => ((hdΨ y).fun_sub (hdΦ y (abs_lt.mpr ⟨(Set.mem_Ioo.mp hy).1, (Set.mem_Ioo.mp hy).2⟩))).differentiableAt.differentiableWithinAt)
      (fun y hy => by
        have := (hdΨ y).fun_sub (hdΦ y (abs_lt.mpr ⟨(Set.mem_Ioo.mp hy).1, (Set.mem_Ioo.mp hy).2⟩))
        rw [this.deriv]; simp)
      (y := 0) hs (Set.mem_Ioo.mpr ⟨by norm_num, by norm_num⟩)
    simp only [hΨ0, hΦ0, sub_self] at hconst
    exact sub_eq_zero.mp hconst
  have hEq : Set.EqOn Ψ Φ (Set.Icc 0 1) := by
    refine Set.EqOn.of_subset_closure (s := Set.Ico 0 1) (fun y hy => ?_) ?_ ?_
      Set.Ico_subset_Icc_self ?_
    · exact hD y (Set.mem_Ioo.mpr ⟨by linarith [hy.1], hy.2⟩)
    · exact (continuous_iff_continuousAt.mpr (fun y => (hdΨ y).continuousAt)).continuousOn
    · exact Complex.continuous_exp.comp_continuousOn (continuousOn_logSeries inc h K hK)
    · rw [closure_Ico (by norm_num)]
  have := hEq (Set.mem_Icc.mpr ⟨zero_le_one, le_rfl⟩)
  simpa [hΨ, hΦ] using this

end Main

end Balaban.Polymer
