module

public import Balaban.LargeField.R.WindowIdeal
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The coefficient error of the composed weight (Part III, Lemma III.1.6, (III.1.6))

`composedWeight_err`: if the flow constants satisfy `2|log ϖ_j| + |log (c^id_j / c_j)| ≤ X q^{j+1}`
(`k₁ ≤ j < k`; SF Theorem 5.3 and P4 (5.28)) then `|a^♮_z / a_z - 1| ≤ η_k = 12 c_ξ q^k / (β (1 - q))`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

namespace BlockTree

variable {m k1 k : ℕ} (B : BlockTree m k1 k)

theorem nBlocks_top : B.nBlocks k = 1 := by
  unfold nBlocks
  rw [Finset.card_eq_one]
  refine ⟨0, ?_⟩
  ext i
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
  constructor
  · rintro ⟨hi, hs⟩
    by_contra h0
    have := B.scale_par i (by omega) h0
    have := B.scale_le (B.par i) (by have := B.par_lt i (by omega) h0; omega)
    omega
  · rintro rfl; exact ⟨by omega, B.root_scale⟩

/-- The volume fractions of the leaves add up to `1`. -/
theorem sum_leafFrac (hm : 0 < m) : ∑ x : Fin B.nLeaf, blockFrac m k (B.leafScale x) = 1 := by
  have h := B.frac_level hm k le_rfl
  rw [B.nBlocks_top] at h
  have hf : (Finset.univ.filter (fun x : Fin B.nLeaf => B.leafScale x < k)) = Finset.univ := by
    ext x; simp [B.leafScale_lt x]
  rw [hf] at h
  simpa [blockFrac] using h.symm

theorem blockFrac_nonneg (m k s : ℕ) : 0 ≤ blockFrac m k s := by unfold blockFrac; positivity

theorem sum_scale_le (hm : 0 < m) (G : ℕ → ℝ) (hG : ∀ s, k1 < s → s ≤ k → 0 ≤ G s) :
    ∑ i ∈ Finset.range (B.n + 1), G (B.scale i) * blockFrac m k (B.scale i) ≤
      ∑ s ∈ Finset.Ioc k1 k, G s := by
  rw [B.sum_scale hm G]
  have h1 : ∀ x : Fin B.nLeaf, ∑ s ∈ Finset.Ioc (B.leafScale x) k, G s ≤ ∑ s ∈ Finset.Ioc k1 k, G s := by
    intro x
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro s hs
      simp only [Finset.mem_Ioc] at hs ⊢
      have := B.leafScale_ge x
      omega
    · intro s hs _
      simp only [Finset.mem_Ioc] at hs
      exact hG s hs.1 hs.2
  calc ∑ x : Fin B.nLeaf, blockFrac m k (B.leafScale x) * ∑ s ∈ Finset.Ioc (B.leafScale x) k, G s
      ≤ ∑ x : Fin B.nLeaf, blockFrac m k (B.leafScale x) * ∑ s ∈ Finset.Ioc k1 k, G s :=
        Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (h1 x) (blockFrac_nonneg _ _ _)
    _ = ∑ s ∈ Finset.Ioc k1 k, G s := by rw [← Finset.sum_mul, B.sum_leafFrac hm, one_mul]

theorem sum_scale_ge (hm : 0 < m) (F : ℕ → ℝ) (hF : ∀ s, k1 < s → s ≤ k → 0 ≤ F s) :
    F k ≤ ∑ i ∈ Finset.range (B.n + 1), F (B.scale i) * blockFrac m k (B.scale i) := by
  rw [B.sum_scale hm F]
  have h1 : ∀ x : Fin B.nLeaf, F k ≤ ∑ s ∈ Finset.Ioc (B.leafScale x) k, F s := by
    intro x
    refine Finset.single_le_sum (f := F) (fun s hs => ?_) (Finset.mem_Ioc.mpr ⟨B.leafScale_lt x, le_rfl⟩)
    simp only [Finset.mem_Ioc] at hs
    have := B.leafScale_ge x
    exact hF s (by omega) hs.2
  calc F k = ∑ x : Fin B.nLeaf, blockFrac m k (B.leafScale x) * F k := by
        rw [← Finset.sum_mul, B.sum_leafFrac hm, one_mul]
    _ ≤ _ := Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (h1 x) (blockFrac_nonneg _ _ _)

/-- The ideal inverse precision is at least `(β_k a)⁻¹` (the top block alone). -/
theorem precSum_ideal_ge {L d : ℕ} (hmL : m = L ^ d) (hL : 2 ≤ L) (hd : 2 ≤ d) {a βk : ℝ}
    (ha : 0 < a) (hβ : 0 < βk) :
    (βk * a)⁻¹ ≤ B.precSum (idealCoeff L d k βk a) (fun _ => 1) := by
  have hm : 0 < m := by rw [hmL]; positivity
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  set F : ℕ → ℝ := fun s => (((L : ℝ) ^ 2) ^ (k - s))⁻¹ with hF
  have hF0 : ∀ s, 0 ≤ F s := fun s => by simp only [hF]; positivity
  have hF1 : F k = 1 := by simp [hF]
  have hpos : 0 < (βk * a)⁻¹ := by positivity
  unfold precSum
  rw [Finset.sum_congr rfl fun i hi => B.ideal_term hmL hL hd ha hβ hi, ← Finset.mul_sum]
  have := B.sum_scale_ge hm F (fun s _ _ => hF0 s)
  rw [hF1] at this
  nlinarith

/-- The ratio `ρ_j = ϖ_j² c^id_j / c_j` of the actual and ideal term of scale `j + 1`. -/
noncomputable def rhoRatio (k : ℕ) (z cId c : ℕ → ℝ) (j : ℕ) : ℝ := varpi k z j ^ 2 * cId j / c j

/-- The relative error of the inverse composed precision against the ideal one is the sum of the
weighted errors `|ρ_j - 1|` of the layers. -/
theorem precSum_rel {L d : ℕ} (hmL : m = L ^ d) (hL : 2 ≤ L) (hd : 2 ≤ d) {a βk : ℝ}
    (ha : 0 < a) (hβ : 0 < βk) (c z : ℕ → ℝ) (hc : ∀ j, k1 ≤ j → j < k → c j ≠ 0) :
    |B.precSum c z / B.precSum (idealCoeff L d k βk a) (fun _ => 1) - 1| ≤
      ∑ s ∈ Finset.Ioc k1 k, (((L : ℝ) ^ 2) ^ (k - s))⁻¹ *
        |rhoRatio k z (idealCoeff L d k βk a) c (s - 1) - 1| := by
  have hm : 0 < m := by rw [hmL]; positivity
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  set cI := idealCoeff L d k βk a with hcI
  have hcI0 : ∀ j, j ≤ k → cI j ≠ 0 := by
    intro j _
    show idealCoeff L d k βk a j ≠ 0
    unfold idealCoeff
    have : 0 < (L : ℝ) ^ (d - 2) := by positivity
    positivity
  set F : ℕ → ℝ := fun s => (((L : ℝ) ^ 2) ^ (k - s))⁻¹ with hF
  have hF0 : ∀ s, 0 ≤ F s := fun s => by simp only [hF]; positivity
  have hF1 : F k = 1 := by simp [hF]
  have hS0 : B.precSum cI (fun _ => 1) =
      ∑ i ∈ Finset.range (B.n + 1), (βk * a)⁻¹ * (F (B.scale i) * blockFrac m k (B.scale i)) :=
    Finset.sum_congr rfl fun i hi => B.ideal_term hmL hL hd ha hβ hi
  have hpos : 0 < (βk * a)⁻¹ := by positivity
  have hlow : (βk * a)⁻¹ ≤ B.precSum cI (fun _ => 1) := by
    rw [hS0, ← Finset.mul_sum]
    have := B.sum_scale_ge hm F (fun s _ _ => hF0 s)
    rw [hF1] at this
    nlinarith
  have hS0pos : 0 < B.precSum cI (fun _ => 1) := lt_of_lt_of_le hpos hlow
  -- difference
  set G : ℕ → ℝ := fun s => F s * |rhoRatio k z cI c (s - 1) - 1| with hG
  have hdiff : |B.precSum c z - B.precSum cI (fun _ => 1)| ≤
      (βk * a)⁻¹ * ∑ i ∈ Finset.range (B.n + 1), G (B.scale i) * blockFrac m k (B.scale i) := by
    unfold precSum
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi => ?_)
    have hge := B.scale_ge i (by have := Finset.mem_range.mp hi; omega)
    have hle := B.scale_le i (by have := Finset.mem_range.mp hi; omega)
    have hT := B.ideal_term hmL hL hd ha hβ hi
    have hci := hcI0 (B.scale i - 1) (by omega)
    have hcc := hc (B.scale i - 1) (by omega) (by omega)
    have e1 : varpi k z (B.scale i - 1) ^ 2 * blockFrac m k (B.scale i) ^ 2 / c (B.scale i - 1) -
        varpi k (fun _ => (1 : ℝ)) (B.scale i - 1) ^ 2 * blockFrac m k (B.scale i) ^ 2 /
          cI (B.scale i - 1) =
        (rhoRatio k z cI c (B.scale i - 1) - 1) *
          (varpi k (fun _ => (1 : ℝ)) (B.scale i - 1) ^ 2 * blockFrac m k (B.scale i) ^ 2 /
            cI (B.scale i - 1)) := by
      rw [varpi_one]; unfold rhoRatio; field_simp
    rw [e1, abs_mul, hT, abs_of_nonneg (mul_nonneg hpos.le (mul_nonneg (hF0 _) (blockFrac_nonneg _ _ _)))]
    simp only [hG]
    have := blockFrac_nonneg m k (B.scale i)
    have := hF0 (B.scale i)
    nlinarith [abs_nonneg (rhoRatio k z cI c (B.scale i - 1) - 1), mul_nonneg (mul_nonneg hpos.le (hF0 (B.scale i))) (blockFrac_nonneg m k (B.scale i))]
  have hG0 : ∀ s, k1 < s → s ≤ k → 0 ≤ G s := fun s _ _ => by simp only [hG]; exact mul_nonneg (hF0 s) (abs_nonneg _)
  have hup := B.sum_scale_le hm G hG0
  rw [abs_sub_comm] at hdiff
  have : |B.precSum c z / B.precSum cI (fun _ => 1) - 1| =
      |B.precSum c z - B.precSum cI (fun _ => 1)| / B.precSum cI (fun _ => 1) := by
    rw [show B.precSum c z / B.precSum cI (fun _ => 1) - 1 =
      (B.precSum c z - B.precSum cI (fun _ => 1)) / B.precSum cI (fun _ => 1) by field_simp,
      abs_div, abs_of_pos hS0pos]
  rw [this, div_le_iff₀ hS0pos]
  rw [abs_sub_comm] at hdiff
  calc |B.precSum c z - B.precSum cI (fun _ => 1)|
      ≤ (βk * a)⁻¹ * ∑ s ∈ Finset.Ioc k1 k, G s := hdiff.trans (mul_le_mul_of_nonneg_left hup hpos.le)
    _ ≤ (∑ s ∈ Finset.Ioc k1 k, G s) * B.precSum cI (fun _ => 1) := by
        have hGs : 0 ≤ ∑ s ∈ Finset.Ioc k1 k, G s :=
          Finset.sum_nonneg fun s hs => hG0 s (Finset.mem_Ioc.mp hs).1 (Finset.mem_Ioc.mp hs).2
        nlinarith

end BlockTree

/-- `|e^y - 1| ≤ 2 |y|` bound for the ratios: if `2|log ϖ_j| + |log (c^id_j / c_j)| ≤ x ≤ 1` then
`|ρ_j - 1| ≤ 2 x`. -/
theorem rhoRatio_sub_one_le {k : ℕ} {z cId c : ℕ → ℝ} {j : ℕ} {x : ℝ} (hv : 0 < varpi k z j)
    (hci : 0 < cId j) (hc : 0 < c j)
    (hx : 2 * |Real.log (varpi k z j)| + |Real.log (cId j / c j)| ≤ x) (hx1 : x ≤ 1) :
    |BlockTree.rhoRatio k z cId c j - 1| ≤ 2 * x := by
  have hρ : BlockTree.rhoRatio k z cId c j = Real.exp (2 * Real.log (varpi k z j) + Real.log (cId j / c j)) := by
    unfold BlockTree.rhoRatio
    rw [Real.exp_add, Real.exp_log (by positivity), show 2 * Real.log (varpi k z j) =
      Real.log (varpi k z j ^ 2) by rw [Real.log_pow]; norm_num, Real.exp_log (by positivity)]
    field_simp
  have hy : |2 * Real.log (varpi k z j) + Real.log (cId j / c j)| ≤ x := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_two]; exact hx
  rw [hρ]
  exact (Real.abs_exp_sub_one_le (hy.trans hx1)).trans (by linarith)

/-- The geometric sum of the layer weights. -/
theorem sum_layers_le {L : ℕ} (hL : 2 ≤ L) {q : ℝ} (hq : 0 < q) (hr : ((L : ℝ) ^ 2 * q)⁻¹ ≤ 1 / 2)
    (k1 k : ℕ) :
    ∑ s ∈ Finset.Ioc k1 k, (((L : ℝ) ^ 2) ^ (k - s))⁻¹ * q ^ s ≤ 2 * q ^ k := by
  have hL' : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  set r : ℝ := ((L : ℝ) ^ 2 * q)⁻¹ with hrdef
  have hr0 : 0 ≤ r := by rw [hrdef]; positivity
  have h1 : ∀ s ∈ Finset.Ioc k1 k, (((L : ℝ) ^ 2) ^ (k - s))⁻¹ * q ^ s = q ^ k * r ^ (k - s) := by
    intro s hs
    have hsk := (Finset.mem_Ioc.mp hs).2
    have : q ^ k = q ^ s * q ^ (k - s) := by rw [← pow_add]; congr 1; omega
    rw [this, hrdef, inv_pow, mul_pow]
    have : (0 : ℝ) < q ^ (k - s) := by positivity
    have : (0 : ℝ) < ((L : ℝ) ^ 2) ^ (k - s) := by positivity
    field_simp
  rw [Finset.sum_congr rfl h1]
  by_cases hk : k1 ≤ k
  · rw [sum_Ioc_reflect (fun t => q ^ k * r ^ t) hk, ← Finset.mul_sum]
    have hgeom : (∑ t ∈ Finset.range (k - k1), r ^ t) * (1 - r) = 1 - r ^ (k - k1) := geom_sum_mul_neg r _
    have hpow : 0 ≤ r ^ (k - k1) := by positivity
    have hsum : ∑ t ∈ Finset.range (k - k1), r ^ t ≤ 2 := by
      have h0 : 0 ≤ ∑ t ∈ Finset.range (k - k1), r ^ t := Finset.sum_nonneg fun t _ => by positivity
      nlinarith
    have : 0 ≤ q ^ k := by positivity
    nlinarith
  · have : Finset.Ioc k1 k = ∅ := by
      ext s; simp only [Finset.mem_Ioc, Finset.notMem_empty, iff_false]; omega
    rw [this]; simp only [Finset.sum_empty]; positivity

/-- (III.1.6), second part: `|ϖ_n - 1| ≤ 4 Z r^{n+1}` if `|log z_i| ≤ Z r^i` for `n < i ≤ k`
(`r ≤ 1/2`, `2 Z r^{n+1} ≤ 1`).  With `Z = 3 α₀ c_ξ / (2β)` and `r = L^{-(α+2γ)}` this is
`|ϖ_n - 1| ≤ ς_n = (6 α₀ c_ξ / β) L^{-(n+1)(α+2γ)}`. -/
theorem varpi_sub_one_le {k n : ℕ} {z : ℕ → ℝ} {Z r : ℝ} (hr0 : 0 < r) (hr : r ≤ 1 / 2) (hZ : 0 ≤ Z)
    (hz : ∀ i, n < i → i ≤ k → 0 < z i ∧ |Real.log (z i)| ≤ Z * r ^ i)
    (hsmall : 2 * Z * r ^ (n + 1) ≤ 1) :
    |varpi k z n - 1| ≤ 4 * Z * r ^ (n + 1) := by
  by_cases hnk : n < k
  · have hpos : ∀ i' ∈ Finset.range (k - n), 0 < z (k - i') := fun i' hi' =>
      (hz _ (by have := Finset.mem_range.mp hi'; omega) (by omega)).1
    have hlog : Real.log (varpi k z n) = -∑ i' ∈ Finset.range (k - n), Real.log (z (k - i')) := by
      unfold varpi
      rw [Real.log_prod (fun i' hi' => (inv_pos.mpr (hpos i' hi')).ne')]
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun i' hi' => Real.log_inv _
    have hvpos : 0 < varpi k z n := Finset.prod_pos fun i' hi' => inv_pos.mpr (hpos i' hi')
    have hx : |Real.log (varpi k z n)| ≤ 2 * Z * r ^ (n + 1) := by
      rw [hlog, abs_neg]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have h1 : ∑ i' ∈ Finset.range (k - n), |Real.log (z (k - i'))| ≤
          ∑ i' ∈ Finset.range (k - n), Z * r ^ (k - i') :=
        Finset.sum_le_sum fun i' hi' =>
          (hz _ (by have := Finset.mem_range.mp hi'; omega) (by omega)).2
      refine h1.trans ?_
      have h2 : ∑ i' ∈ Finset.range (k - n), Z * r ^ (k - i') =
          ∑ t ∈ Finset.range (k - n), Z * r ^ (n + 1 + t) := by
        rw [← Finset.sum_range_reflect (fun t => Z * r ^ (n + 1 + t)) (k - n)]
        refine Finset.sum_congr rfl fun i' hi' => ?_
        have := Finset.mem_range.mp hi'
        congr 2; omega
      rw [h2]
      have hgeom : (∑ t ∈ Finset.range (k - n), r ^ t) * (1 - r) = 1 - r ^ (k - n) := geom_sum_mul_neg r _
      have hpow : 0 ≤ r ^ (k - n) := by positivity
      have hsum : ∑ t ∈ Finset.range (k - n), r ^ t ≤ 2 := by
        have h0 : 0 ≤ ∑ t ∈ Finset.range (k - n), r ^ t := Finset.sum_nonneg fun t _ => by positivity
        nlinarith
      calc ∑ t ∈ Finset.range (k - n), Z * r ^ (n + 1 + t)
          = Z * r ^ (n + 1) * ∑ t ∈ Finset.range (k - n), r ^ t := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun t _ => by rw [pow_add]; ring
        _ ≤ Z * r ^ (n + 1) * 2 := mul_le_mul_of_nonneg_left hsum (by positivity)
        _ = _ := by ring
    have hexp : varpi k z n = Real.exp (Real.log (varpi k z n)) := (Real.exp_log hvpos).symm
    have := Real.abs_exp_sub_one_le ((hx.trans hsmall))
    rw [← hexp] at this
    linarith
  · have : varpi k z n = 1 := by
      unfold varpi; rw [show k - n = 0 by omega]; simp
    rw [this]; simp; positivity

/-- `q = L^{-2γ}`: `0 < q < 1` and `L^{-2} q^{-1} ≤ 1/2` (for `0 < γ ≤ 1/2`). -/
theorem q_facts {L : ℕ} (hL : 2 ≤ L) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ ≤ 1 / 2) :
    0 < (L : ℝ) ^ (-(2 * γ)) ∧ (L : ℝ) ^ (-(2 * γ)) < 1 ∧
      (((L : ℝ) ^ 2) * (L : ℝ) ^ (-(2 * γ)))⁻¹ ≤ 1 / 2 := by
  have hL1 : (1 : ℝ) < L := by exact_mod_cast (by omega : 1 < L)
  have hL2 : (2 : ℝ) ≤ L := by exact_mod_cast hL
  refine ⟨Real.rpow_pos_of_pos (by linarith) _, Real.rpow_lt_one_of_one_lt_of_neg hL1 (by linarith), ?_⟩
  have h1 : ((L : ℝ) ^ 2) * (L : ℝ) ^ (-(2 * γ)) = (L : ℝ) ^ (2 - 2 * γ) := by
    rw [show (2 - 2 * γ : ℝ) = 2 + (-(2 * γ)) by ring, Real.rpow_add (by linarith)]
    norm_cast
  rw [h1]
  have h2 : (L : ℝ) ^ (1 : ℝ) ≤ (L : ℝ) ^ (2 - 2 * γ) :=
    Real.rpow_le_rpow_of_exponent_le hL1.le (by linarith)
  rw [Real.rpow_one] at h2
  rw [inv_eq_one_div]
  exact (one_div_le_one_div_of_le (by linarith) h2).trans (by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith)

namespace BlockTree

variable {m k1 k : ℕ} (B : BlockTree m k1 k)

/-- **(III.1.6), the coefficient error**: if the flow constants satisfy the bound of SF Theorem 5.3,
`2|log ϖ_j| + |log (c^id_j / c_j)| ≤ x_j := (3 c_ξ / (2β(1-q))) q^{j+1}` for `k₁ ≤ j < k`
(`q = L^{-2γ}`), then `a^♮_z = a_z (1 + η_z)` with `|η_z| ≤ η_k = 12 c_ξ q^k / (β (1 - q))`. -/
theorem composedWeight_err {L d : ℕ} (hmL : m = L ^ d) (hL : 2 ≤ L) (hd : 2 ≤ d)
    {a βk β cξ γ q : ℝ} (ha : 0 < a) (hβk : 0 < βk) (hβ : 0 < β) (hcξ : 0 ≤ cξ)
    (hγ : 0 < γ) (hγ2 : γ ≤ 1 / 2) (hq : q = (L : ℝ) ^ (-(2 * γ)))
    (c z : ℕ → ℝ) (hz : ∀ s, k1 < s → s ≤ k → 0 < z s) (hc : ∀ j, k1 ≤ j → j < k → 0 < c j)
    (hlog : ∀ j, k1 ≤ j → j < k →
      2 * |Real.log (varpi k z j)| + |Real.log (idealCoeff L d k βk a j / c j)| ≤
        3 * cξ * q ^ (j + 1) / (2 * β * (1 - q)))
    (hsmall : 3 * cξ * q / (2 * β * (1 - q)) ≤ 1)
    (hη : 12 * cξ * q ^ k / (β * (1 - q)) ≤ 1 / 2) :
    |B.composedWeight βk c z / B.blockWeight L a - 1| ≤ 12 * cξ * q ^ k / (β * (1 - q)) := by
  obtain ⟨hq0, hq1, hr⟩ := q_facts hL hγ hγ2
  rw [← hq] at hq0 hq1 hr
  have hm : 0 < m := by rw [hmL]; positivity
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  set cI := idealCoeff L d k βk a with hcI
  have h1q : 0 < 1 - q := by linarith
  set X : ℝ := 3 * cξ / (2 * β * (1 - q)) with hX
  have hX0 : 0 ≤ X := by positivity
  -- the ratio bound
  have hrho : ∀ s ∈ Finset.Ioc k1 k, |BlockTree.rhoRatio k z cI c (s - 1) - 1| ≤ 2 * (X * q ^ s) := by
    intro s hs
    have hs' := Finset.mem_Ioc.mp hs
    have hvpos : 0 < varpi k z (s - 1) := by
      unfold varpi
      refine Finset.prod_pos fun i' hi' => ?_
      have := Finset.mem_range.mp hi'
      exact inv_pos.mpr (hz _ (by omega) (by omega))
    have hcI0 : 0 < cI (s - 1) := by
      show 0 < idealCoeff L d k βk a (s - 1)
      unfold idealCoeff
      have : 0 < (L : ℝ) ^ (d - 2) := by positivity
      positivity
    have hlog' := hlog (s - 1) (by omega) (by omega)
    rw [show s - 1 + 1 = s by omega] at hlog'
    have hxq : X * q ^ s ≤ 1 := by
      have : q ^ s ≤ q := by
        calc q ^ s ≤ q ^ 1 := pow_le_pow_of_le_one hq0.le hq1.le (by omega)
          _ = q := pow_one q
      have h3 : 3 * cξ * q / (2 * β * (1 - q)) = X * q := by rw [hX]; ring
      nlinarith
    have hlog'' : 2 * |Real.log (varpi k z (s - 1))| + |Real.log (cI (s - 1) / c (s - 1))| ≤ X * q ^ s := by
      have : 3 * cξ * q ^ s / (2 * β * (1 - q)) = X * q ^ s := by rw [hX]; ring
      rwa [this] at hlog'
    exact rhoRatio_sub_one_le hvpos hcI0 (hc (s - 1) (by omega) (by omega)) hlog'' hxq
  have hS := B.precSum_rel hmL hL hd ha hβk c z (fun j h1 h2 => (hc j h1 h2).ne')
  have hsum : ∑ s ∈ Finset.Ioc k1 k, (((L : ℝ) ^ 2) ^ (k - s))⁻¹ *
      |BlockTree.rhoRatio k z cI c (s - 1) - 1| ≤ 2 * X * (2 * q ^ k) := by
    calc _ ≤ ∑ s ∈ Finset.Ioc k1 k, (2 * X) * ((((L : ℝ) ^ 2) ^ (k - s))⁻¹ * q ^ s) := by
          refine Finset.sum_le_sum fun s hs => ?_
          have h0 : (0 : ℝ) ≤ (((L : ℝ) ^ 2) ^ (k - s))⁻¹ := by positivity
          calc _ ≤ (((L : ℝ) ^ 2) ^ (k - s))⁻¹ * (2 * (X * q ^ s)) :=
                mul_le_mul_of_nonneg_left (hrho s hs) h0
            _ = _ := by ring
      _ = (2 * X) * ∑ s ∈ Finset.Ioc k1 k, (((L : ℝ) ^ 2) ^ (k - s))⁻¹ * q ^ s := by
          rw [Finset.mul_sum]
      _ ≤ (2 * X) * (2 * q ^ k) :=
          mul_le_mul_of_nonneg_left (sum_layers_le hL hq0 hr k1 k) (by positivity)
  have hδ : 2 * X * (2 * q ^ k) = 6 * cξ * q ^ k / (β * (1 - q)) := by rw [hX]; field_simp; ring
  have hδ' : 6 * cξ * q ^ k / (β * (1 - q)) ≤ 1 / 4 := by
    have : 12 * cξ * q ^ k / (β * (1 - q)) = 2 * (6 * cξ * q ^ k / (β * (1 - q))) := by ring
    linarith
  -- the ratio u = S / S0
  set S := B.precSum c z
  set S0 := B.precSum cI (fun _ => 1)
  have hu : |S / S0 - 1| ≤ 6 * cξ * q ^ k / (β * (1 - q)) := by
    refine hS.trans (hsum.trans ?_); rw [hδ]
  set δ := 6 * cξ * q ^ k / (β * (1 - q)) with hδdef
  have hupos : 1 / 2 ≤ S / S0 := by
    have := (abs_le.mp hu).1; linarith
  have hS0pos : 0 < S0 := lt_of_lt_of_le (by positivity) (B.precSum_ideal_ge hmL hL hd ha hβk)
  have hupos' : 0 < S / S0 := by linarith
  have hSpos : 0 < S := by
    have := mul_pos hupos' hS0pos
    rwa [div_mul_cancel₀ _ hS0pos.ne'] at this
  have hratio : B.composedWeight βk c z / B.blockWeight L a = S0 / S := by
    rw [← B.composedWeight_ideal hmL hL hd ha hβk]
    unfold composedWeight
    rw [composedPrecision_eq, composedPrecision_eq]
    show S⁻¹ / βk / (S0⁻¹ / βk) = S0 / S
    have hne : βk ≠ 0 := hβk.ne'
    field_simp
  rw [hratio]
  have hu1 : |S / S0 - 1| ≤ δ := hu
  have e : S0 / S - 1 = -((S / S0 - 1) / (S / S0)) := by
    field_simp; ring
  rw [e, abs_neg, abs_div, abs_of_pos hupos', div_le_iff₀ hupos']
  have h12 : 12 * cξ * q ^ k / (β * (1 - q)) = 2 * δ := by rw [hδdef]; ring
  have hδ0 : 0 ≤ δ := by rw [hδdef]; positivity
  rw [h12]
  nlinarith [abs_nonneg (S / S0 - 1), mul_nonneg hδ0 (sub_nonneg.mpr hupos)]

end BlockTree

end Balaban.LargeField
