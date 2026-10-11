module

public import Balaban.Correlations.GreenIdentification
public import Balaban.Correlations.KernelDictionary
public import Balaban.Correlations.KernelPointwise
public import Balaban.Correlations.FineGreenLimits
public import Balaban.Green.InfiniteVolume
public import Balaban.Green.InfiniteVolumeUnique
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# The infinite-volume Gaussian kernels: (G1), (G3), (G5)

For the free flow `α_i = a L^{(i+1)(d-2)}` the `j`-th term of the multiscale decomposition of
`-Δ + μ` on the torus of side `L^{j+1}(m+1)` is (`Balaban.termKernel_zero`,
`Balaban.termKernel_succ`, from the dictionary of `Balaban.Correlations.KernelDictionary`)

`T_j = L^{2(j+1)} G_{j+1} - L^{2j} G_j`  (`G_0 = 0`),

where `G_J` is the entry of the inverse of the unit-lattice fine operator
`fineHamiltonian d ℓ (L^J) M (μ L^{2J}) a_J` (`Balaban.Gent`).  The landed Green package gives:
the entries are Cauchy as the torus grows (`Balaban.Green.fineGreen_cauchy_coarse`), so `T_j`
converges (G1, `termKernel_converges`; `tLim` is the limit `t_j^μ`), and they are Lipschitz in the
mass uniformly in the torus (`Balaban.Green.fineGreen_lipschitz`), so `t_j^μ` has a limit as
`μ ↓ 0` (G3, `tLim_exists_zero`; `t0Lim` is `t_j^0`).  The mass range is `μ L^{2(j+1)} ≤ 1`,
i.e. unit-lattice masses in `[0, 1]` (option (b) of the brief: `KernelHyp` only asks for this
range).  `prolong_bound` is (G5): the prolongation is the fine-to-block kernel (dictionary) and the
pointwise bound `oneScale_pointwise` applies.
-/

@[expose] public section

namespace Balaban

open Matrix Filter Topology Balaban.Green

section Entries

variable {d L : ℕ} [NeZero L]

/-- The entry at the sites `x, y ∈ ℤ^d` of the inverse of the fine operator on the torus of side
`ℓ` (blocks of side `N`, coarse side `M`). -/
noncomputable def Gent (d ℓ N M : ℕ) [NeZero ℓ] [NeZero M] (ν a : ℝ) (x y : Fin d → ℤ) : ℝ :=
  (fineHamiltonian d ℓ N M ν a)⁻¹ (castTorus ℓ x) (castTorus ℓ y)

theorem Gent_congr {ℓ ℓ' M M' : ℕ} [NeZero ℓ] [NeZero ℓ'] [NeZero M] [NeZero M'] (N : ℕ)
    (hℓ : ℓ = ℓ') (hM : M = M') (ν a : ℝ) (x y : Fin d → ℤ) :
    Gent d ℓ N M ν a x y = Gent d ℓ' N M' ν a x y := by
  subst hℓ hM
  rfl

/-- The inverse of `blockHamiltonian μ (a / N²)` in terms of `Gent` at the unit-lattice mass
`ν = μ N²`. -/
theorem blockHamiltonian_inv_entry {ℓ N M : ℕ} [NeZero ℓ] [NeZero M] (hℓ : ℓ = N * M)
    (hN : 0 < N) (hd : 0 < d) {μ a : ℝ} (hμ : 0 ≤ μ) (ha : 0 < a) (x y : Fin d → ℤ) :
    (blockHamiltonian d ℓ N M μ (a / (N : ℝ) ^ 2))⁻¹ (castTorus ℓ x) (castTorus ℓ y) =
      (N : ℝ) ^ 2 * Gent d ℓ N M (μ * (N : ℝ) ^ 2) a x y := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hc : (N : ℝ) ^ 2 ≠ 0 := by positivity
  unfold Gent
  rw [fineHamiltonian_inv hℓ hN hd (by positivity) ha, mul_div_cancel_right₀ _ hc,
    Matrix.smul_apply, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hc, one_mul]


variable {a μ : ℝ}

theorem termKernel_eq_termDirect (ha : 0 < a) (hμ : 0 < μ) (j m : ℕ)
    (x y : Fin d → ℤ) :
    termKernel d L (freeSeq d L a) μ (j + 1) j m x y =
      termDirect d L j (L * (m + 1) * L ^ j) (L * (m + 1)) (m + 1)
        (latticeLaplacian d (L * (m + 1) * L ^ j) μ) (freeSeq d L a)
        (castTorus (L * (m + 1) * L ^ j) x) (castTorus (L * (m + 1) * L ^ j) y) := by
  unfold termKernel
  rw [fluctTerm_eq_termDirect (L := L) (m := m + 1) j 0 (j + 1) (by omega) _ (freeSeq d L a)
    (latticeLaplacian_posDef hμ) (fun i => freeSeq_pos ha i)]
  exact termDirect_congr j (by ring) (by ring) (by ring) μ (freeSeq d L a) x y

theorem termKernel_zero (hd : 2 ≤ d) (hL : 1 < L) (ha : 0 < a) (hμ : 0 < μ) (m : ℕ)
    (x y : Fin d → ℤ) :
    termKernel d L (freeSeq d L a) μ (0 + 1) 0 m x y =
      ((L : ℝ)) ^ 2 * Gent d (L * (m + 1)) L (m + 1) (μ * (L : ℝ) ^ 2) a x y := by
  unfold termKernel
  rw [fluctTerm_eq_termDirect (L := L) (m := m + 1) 0 0 (0 + 1) (by omega) _ (freeSeq d L a)
    (latticeLaplacian_posDef hμ) (fun i => freeSeq_pos ha i)]
  have h := termDirect_freeSeq_zero (d := d) (L := L) (ℓ := L ^ (0 + 1) * (m + 1))
    (m₂ := L ^ 0 * (m + 1)) hd hL ha hμ
  have hN : 0 < L ^ (0 + 1) := Nat.pos_of_ne_zero (pow_ne_zero _ (NeZero.ne L))
  have key := blockHamiltonian_inv_entry (d := d) (ℓ := L ^ (0 + 1) * (m + 1)) (N := L ^ (0 + 1))
    (M := L ^ 0 * (m + 1)) (by simp) hN (by omega) hμ.le (aScale_pos hL ha le_rfl) x y
  simp only [Nat.cast_pow] at key
  show termDirect d L 0 (L ^ (0 + 1) * (m + 1)) (L ^ (0 + 1) * (m + 1)) (L ^ 0 * (m + 1))
      (latticeLaplacian d (L ^ (0 + 1) * (m + 1)) μ) (freeSeq d L a)
      (castTorus (L ^ (0 + 1) * (m + 1)) x) (castTorus (L ^ (0 + 1) * (m + 1)) y) = _
  rw [h, key, aScale_one hL]
  simp only [zero_add, pow_one, pow_zero, one_mul]

theorem termKernel_succ (hd : 2 ≤ d) (hL : 1 < L) (ha : 0 < a) (hμ : 0 < μ) {j : ℕ} (hj : 1 ≤ j)
    (m : ℕ) (x y : Fin d → ℤ) :
    termKernel d L (freeSeq d L a) μ (j + 1) j m x y =
      ((L : ℝ) ^ (j + 1)) ^ 2 * Gent d (L * (m + 1) * L ^ j) (L ^ (j + 1)) (m + 1)
          (μ * ((L : ℝ) ^ (j + 1)) ^ 2) (aScale L a (j + 1)) x y -
        ((L : ℝ) ^ j) ^ 2 * Gent d (L * (m + 1) * L ^ j) (L ^ j) (L * (m + 1))
          (μ * ((L : ℝ) ^ j) ^ 2) (aScale L a j) x y := by
  rw [termKernel_eq_termDirect ha hμ]
  have h := termDirect_freeSeq_succ (d := d) (L := L) (ℓ := L * (m + 1) * L ^ j)
    (ℓ₁ := L * (m + 1)) (m₂ := m + 1) hd hL ha hμ hj (mul_comm _ _) rfl
  rw [h, Matrix.sub_apply]
  have hN1 : 0 < L ^ (j + 1) := Nat.pos_of_ne_zero (pow_ne_zero _ (NeZero.ne L))
  have hN0 : 0 < L ^ j := Nat.pos_of_ne_zero (pow_ne_zero _ (NeZero.ne L))
  have k1 := blockHamiltonian_inv_entry (d := d) (ℓ := L * (m + 1) * L ^ j) (N := L ^ (j + 1))
    (M := m + 1) (a := aScale L a (j + 1)) (by ring) hN1 (by omega) hμ.le
    (aScale_pos hL ha (by omega)) x y
  have k2 := blockHamiltonian_inv_entry (d := d) (ℓ := L * (m + 1) * L ^ j) (N := L ^ j)
    (M := L * (m + 1)) (mul_comm _ _) hN0 (by omega) hμ.le (aScale_pos hL ha hj) x y
  simp only [Nat.cast_pow] at k1 k2
  rw [k1, k2]

section CauchyLipschitz

theorem gent_cauchy_coarse (hd : 0 < d) (k : ℕ) {ν a : ℝ} (hν : 0 ≤ ν) (ha1 : 1 / 2 ≤ a)
    (ha2 : a ≤ 2) (x y : Fin d → ℤ) :
    CauchySeq (fun m : ℕ => Gent d ((m + 1) * L ^ k) (L ^ k) (m + 1) ν a x y) := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨R₁, hR₁⟩ := exists_sqBox x
  obtain ⟨R₂, hR₂⟩ := exists_sqBox y
  obtain ⟨j₀, hj₀⟩ := fineGreen_cauchy_coarse (d := d) (L := L) (k := k) hd hν ha1 ha2
    (max R₁ R₂) (ε / 2) (by positivity)
  refine ⟨j₀, fun m hm n hn => ?_⟩
  have h := hj₀ m hm n hn x (sqBox_mono (le_max_left _ _) hR₁) y
    (sqBox_mono (le_max_right _ _) hR₂)
  rw [Real.dist_eq]
  unfold Gent
  linarith

theorem gent_cauchy_mul (hd : 0 < d) (k : ℕ) {ν a : ℝ} (hν : 0 ≤ ν) (ha1 : 1 / 2 ≤ a)
    (ha2 : a ≤ 2) (x y : Fin d → ℤ) :
    CauchySeq (fun m : ℕ => Gent d (L * (m + 1) * L ^ k) (L ^ k) (L * (m + 1)) ν a x y) := by
  have hL : 1 ≤ L := Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hφ : Tendsto (fun m : ℕ => L * (m + 1) - 1) atTop atTop :=
    tendsto_atTop_mono (fun m => by
      have : m + 1 ≤ L * (m + 1) := Nat.le_mul_of_pos_left _ hL
      show m ≤ L * (m + 1) - 1
      omega) tendsto_id
  have hc := (gent_cauchy_coarse (L := L) hd k hν ha1 ha2 x y).comp_tendsto hφ
  have e : (fun m : ℕ => Gent d ((m + 1) * L ^ k) (L ^ k) (m + 1) ν a x y) ∘
      (fun m : ℕ => L * (m + 1) - 1) =
      fun m : ℕ => Gent d (L * (m + 1) * L ^ k) (L ^ k) (L * (m + 1)) ν a x y := by
    funext m
    have h1 : 1 ≤ L * (m + 1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos m) |>.trans' hL
    have h2 : L * (m + 1) - 1 + 1 = L * (m + 1) := by omega
    simp only [Function.comp]
    exact Gent_congr (L ^ k) (by rw [h2]) h2 ν a x y
  rw [e] at hc
  exact hc

omit [NeZero L] in
theorem half_le_of_lo (hL : 1 < L) {a : ℝ} (hlo : 1 ≤ 2 * a * (1 - ((L : ℝ) ^ 2)⁻¹)) :
    1 / 2 ≤ a := by
  have hx : (1 : ℝ) < L := by exact_mod_cast hL
  have h1 : ((L : ℝ) ^ 2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (one_lt_pow₀ hx (by norm_num))
  have hc : 0 < ((L : ℝ) ^ 2)⁻¹ := by positivity
  have h3 : 0 < 1 - ((L : ℝ) ^ 2)⁻¹ := by linarith
  have ha0 : 0 < a := by
    by_contra h
    push Not at h
    nlinarith
  nlinarith

omit [NeZero L] in
theorem aScale_mem (hL : 1 < L) {a : ℝ} (hlo : 1 ≤ 2 * a * (1 - ((L : ℝ) ^ 2)⁻¹)) (hhi : a ≤ 2)
    {J : ℕ} (hJ : 1 ≤ J) : 1 / 2 ≤ aScale L a J ∧ aScale L a J ≤ 2 := by
  have hx : (1 : ℝ) < L := by exact_mod_cast hL
  have h1 : ((L : ℝ) ^ 2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (one_lt_pow₀ hx (by norm_num))
  have h2 : ((L : ℝ) ^ (2 * J))⁻¹ < 1 :=
    inv_lt_one_of_one_lt₀ (one_lt_pow₀ hx (by omega))
  have h3 : 0 < 1 - ((L : ℝ) ^ 2)⁻¹ := by linarith
  have h4 : 0 < 1 - ((L : ℝ) ^ (2 * J))⁻¹ := by linarith
  have h5 : ((L : ℝ) ^ (2 * J))⁻¹ ≤ ((L : ℝ) ^ 2)⁻¹ := by
    apply inv_anti₀ (by positivity)
    exact pow_le_pow_right₀ hx.le (by omega)
  have ha0 : 0 < a := by linarith [half_le_of_lo hL hlo]
  have he0 : 0 < ((L : ℝ) ^ (2 * J))⁻¹ := by positivity
  unfold aScale
  constructor
  · rw [le_div_iff₀ h4]
    nlinarith
  · rw [div_le_iff₀ h4]
    nlinarith

theorem gent_tendsto_F1 (hd : 0 < d) (j : ℕ) {ν a : ℝ} (hν : 0 ≤ ν) (ha1 : 1 / 2 ≤ a)
    (ha2 : a ≤ 2) (x y : Fin d → ℤ) :
    ∃ l, Tendsto (fun m : ℕ => Gent d (L * (m + 1) * L ^ j) (L ^ (j + 1)) (m + 1) ν a x y)
      atTop (𝓝 l) := by
  have h := gent_cauchy_coarse (L := L) hd (j + 1) hν ha1 ha2 x y
  have e : (fun m : ℕ => Gent d (L * (m + 1) * L ^ j) (L ^ (j + 1)) (m + 1) ν a x y) =
      fun m : ℕ => Gent d ((m + 1) * L ^ (j + 1)) (L ^ (j + 1)) (m + 1) ν a x y := by
    funext m
    exact Gent_congr (L ^ (j + 1)) (by ring) rfl ν a x y
  rw [e]
  exact cauchySeq_tendsto_of_complete h

theorem gent_tendsto_F0 (hd : 0 < d) (j : ℕ) {ν a : ℝ} (hν : 0 ≤ ν) (ha1 : 1 / 2 ≤ a)
    (ha2 : a ≤ 2) (x y : Fin d → ℤ) :
    ∃ l, Tendsto (fun m : ℕ => Gent d (L * (m + 1) * L ^ j) (L ^ j) (L * (m + 1)) ν a x y)
      atTop (𝓝 l) :=
  cauchySeq_tendsto_of_complete (gent_cauchy_mul (L := L) hd j hν ha1 ha2 x y)

/-- **(G1)**: the torus kernels converge as the torus grows. -/
theorem termKernel_converges (hd : 3 ≤ d) (hL : 1 < L) {a μ : ℝ}
    (hlo : 1 ≤ 2 * a * (1 - ((L : ℝ) ^ 2)⁻¹)) (hhi : a ≤ 2) (hμ : 0 < μ) (j : ℕ)
    (x y : Fin d → ℤ) :
    ∃ l, Tendsto (fun m : ℕ => termKernel d L (freeSeq d L a) μ (j + 1) j m x y) atTop
      (𝓝 l) := by
  have hx : (1 : ℝ) < L := by exact_mod_cast hL
  have h1 : ((L : ℝ) ^ 2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (one_lt_pow₀ hx (by norm_num))
  have hhalf := half_le_of_lo hL hlo
  have ha0 : 0 < a := by linarith
  have hd0 : 0 < d := by omega
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · obtain ⟨l, hl⟩ := gent_tendsto_F1 (L := L) hd0 0 (ν := μ * (L : ℝ) ^ 2 ) (a := a)
      (by positivity) hhalf hhi x y
    refine ⟨(L : ℝ) ^ 2 * l, ?_⟩
    have e : (fun m : ℕ => termKernel d L (freeSeq d L a) μ (0 + 1) 0 m x y) =
        fun m : ℕ => (L : ℝ) ^ 2 * Gent d (L * (m + 1) * L ^ 0) (L ^ (0 + 1)) (m + 1)
          (μ * (L : ℝ) ^ 2) a x y := by
      funext m
      rw [termKernel_zero (by omega) hL ha0 hμ]
      simp
    rw [e]
    exact hl.const_mul _
  · obtain ⟨hlo1, hhi1⟩ := aScale_mem hL hlo hhi (J := j + 1) (by omega)
    obtain ⟨hlo2, hhi2⟩ := aScale_mem hL hlo hhi (J := j) hj
    obtain ⟨l₁, hl₁⟩ := gent_tendsto_F1 (L := L) hd0 j (ν := μ * ((L : ℝ) ^ (j + 1)) ^ 2)
      (a := aScale L a (j + 1)) (by positivity) hlo1 hhi1 x y
    obtain ⟨l₂, hl₂⟩ := gent_tendsto_F0 (L := L) hd0 j (ν := μ * ((L : ℝ) ^ j) ^ 2)
      (a := aScale L a j) (by positivity) hlo2 hhi2 x y
    refine ⟨((L : ℝ) ^ (j + 1)) ^ 2 * l₁ - ((L : ℝ) ^ j) ^ 2 * l₂, ?_⟩
    have e : (fun m : ℕ => termKernel d L (freeSeq d L a) μ (j + 1) j m x y) =
        fun m : ℕ => ((L : ℝ) ^ (j + 1)) ^ 2 * Gent d (L * (m + 1) * L ^ j) (L ^ (j + 1)) (m + 1)
          (μ * ((L : ℝ) ^ (j + 1)) ^ 2) (aScale L a (j + 1)) x y -
        ((L : ℝ) ^ j) ^ 2 * Gent d (L * (m + 1) * L ^ j) (L ^ j) (L * (m + 1))
          (μ * ((L : ℝ) ^ j) ^ 2) (aScale L a j) x y := by
      funext m
      exact termKernel_succ (by omega) hL ha0 hμ hj m x y
    rw [e]
    exact (hl₁.const_mul _).sub (hl₂.const_mul _)

theorem gent_lipschitz (hd : 0 < d) (k : ℕ) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧ ∀ {ℓ N M : ℕ} [NeZero ℓ] [NeZero M], N = L ^ k → ℓ = M * L ^ k →
      ∀ {ν₁ ν₂ a : ℝ}, 0 ≤ ν₁ → ν₁ ≤ 1 → 0 ≤ ν₂ → ν₂ ≤ 1 → 1 / 2 ≤ a → a ≤ 2 →
      ∀ x y : Fin d → ℤ, |Gent d ℓ N M ν₁ a x y - Gent d ℓ N M ν₂ a x y| ≤ Λ * |ν₁ - ν₂| := by
  obtain ⟨Λ, hΛ, h⟩ := fineGreen_lipschitz (L := L) hd k
  refine ⟨Λ, hΛ, ?_⟩
  intro ℓ N M _ _ hN hℓ ν₁ ν₂ a h1 h2 h3 h4 h5 h6 x y
  subst hN hℓ
  exact h h1 h2 h3 h4 h5 h6 _ _

/-- Lipschitz dependence of the torus kernels on the mass, uniformly in the torus. -/
theorem termKernel_lipschitz (hd : 3 ≤ d) (hL : 1 < L) {a : ℝ}
    (hlo : 1 ≤ 2 * a * (1 - ((L : ℝ) ^ 2)⁻¹)) (hhi : a ≤ 2) (j : ℕ) (x y : Fin d → ℤ) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧ ∀ (m : ℕ) {μ₁ μ₂ : ℝ}, 0 < μ₁ → μ₁ * (L : ℝ) ^ (2 * (j + 1)) ≤ 1 →
      0 < μ₂ → μ₂ * (L : ℝ) ^ (2 * (j + 1)) ≤ 1 →
      |termKernel d L (freeSeq d L a) μ₁ (j + 1) j m x y -
          termKernel d L (freeSeq d L a) μ₂ (j + 1) j m x y| ≤ Λ * |μ₁ - μ₂| := by
  have hx : (1 : ℝ) < L := by exact_mod_cast hL
  have hhalf := half_le_of_lo hL hlo
  have ha0 : 0 < a := by linarith
  have hd0 : 0 < d := by omega
  have hLpos : (0 : ℝ) < L := by linarith
  -- the mass bounds
  have hmass : ∀ {μ : ℝ} {i : ℕ}, 0 < μ → i ≤ j + 1 → μ * (L : ℝ) ^ (2 * (j + 1)) ≤ 1 →
      μ * ((L : ℝ) ^ i) ^ 2 ≤ 1 := by
    intro μ i hμ hi h
    have : ((L : ℝ) ^ i) ^ 2 ≤ (L : ℝ) ^ (2 * (j + 1)) := by
      rw [← pow_mul, mul_comm]
      exact pow_le_pow_right₀ hx.le (by omega)
    exact (mul_le_mul_of_nonneg_left this hμ.le).trans h
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · obtain ⟨Λ, hΛ, hG⟩ := gent_lipschitz (L := L) hd0 1
    refine ⟨(L : ℝ) ^ 2 * (Λ * (L : ℝ) ^ 2), by positivity, ?_⟩
    intro m μ₁ μ₂ h1 h1' h2 h2'
    rw [termKernel_zero (by omega) hL ha0 h1, termKernel_zero (by omega) hL ha0 h2,
      ← mul_sub, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (L : ℝ) ^ 2)]
    have hb := hG (ℓ := L * (m + 1)) (N := L) (M := m + 1) (by simp) (by ring)
      (ν₁ := μ₁ * (L : ℝ) ^ 2) (ν₂ := μ₂ * (L : ℝ) ^ 2) (a := a) (by positivity)
      (by simpa using hmass h1 (i := 1) le_rfl h1') (by positivity)
      (by simpa using hmass h2 (i := 1) le_rfl h2') hhalf hhi x y
    have e : |μ₁ * (L : ℝ) ^ 2 - μ₂ * (L : ℝ) ^ 2| = (L : ℝ) ^ 2 * |μ₁ - μ₂| := by
      rw [← sub_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (L : ℝ) ^ 2), mul_comm]
    rw [e] at hb
    calc (L : ℝ) ^ 2 * _ ≤ (L : ℝ) ^ 2 * (Λ * ((L : ℝ) ^ 2 * |μ₁ - μ₂|)) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ = _ := by ring
  · obtain ⟨hlo1, hhi1⟩ := aScale_mem hL hlo hhi (J := j + 1) (by omega)
    obtain ⟨hlo2, hhi2⟩ := aScale_mem hL hlo hhi (J := j) hj
    obtain ⟨Λ₁, hΛ₁, hG₁⟩ := gent_lipschitz (L := L) hd0 (j + 1)
    obtain ⟨Λ₂, hΛ₂, hG₂⟩ := gent_lipschitz (L := L) hd0 j
    refine ⟨((L : ℝ) ^ (j + 1)) ^ 2 * (Λ₁ * ((L : ℝ) ^ (j + 1)) ^ 2) +
      ((L : ℝ) ^ j) ^ 2 * (Λ₂ * ((L : ℝ) ^ j) ^ 2), by positivity, ?_⟩
    intro m μ₁ μ₂ h1 h1' h2 h2'
    rw [termKernel_succ (by omega) hL ha0 h1 hj, termKernel_succ (by omega) hL ha0 h2 hj]
    have hb₁ := hG₁ (ℓ := L * (m + 1) * L ^ j) (N := L ^ (j + 1)) (M := m + 1) rfl (by ring)
      (ν₁ := μ₁ * ((L : ℝ) ^ (j + 1)) ^ 2) (ν₂ := μ₂ * ((L : ℝ) ^ (j + 1)) ^ 2)
      (a := aScale L a (j + 1)) (by positivity) (hmass h1 le_rfl h1') (by positivity)
      (hmass h2 le_rfl h2') hlo1 hhi1 x y
    have hb₂ := hG₂ (ℓ := L * (m + 1) * L ^ j) (N := L ^ j) (M := L * (m + 1)) rfl rfl
      (ν₁ := μ₁ * ((L : ℝ) ^ j) ^ 2) (ν₂ := μ₂ * ((L : ℝ) ^ j) ^ 2)
      (a := aScale L a j) (by positivity) (hmass h1 (by omega) h1') (by positivity)
      (hmass h2 (by omega) h2') hlo2 hhi2 x y
    have e₁ : |μ₁ * ((L : ℝ) ^ (j + 1)) ^ 2 - μ₂ * ((L : ℝ) ^ (j + 1)) ^ 2| =
        ((L : ℝ) ^ (j + 1)) ^ 2 * |μ₁ - μ₂| := by
      rw [← sub_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((L : ℝ) ^ (j + 1)) ^ 2),
        mul_comm]
    have e₂ : |μ₁ * ((L : ℝ) ^ j) ^ 2 - μ₂ * ((L : ℝ) ^ j) ^ 2| =
        ((L : ℝ) ^ j) ^ 2 * |μ₁ - μ₂| := by
      rw [← sub_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((L : ℝ) ^ j) ^ 2),
        mul_comm]
    rw [e₁] at hb₁
    rw [e₂] at hb₂
    have hsplit : ∀ A B C D : ℝ, |A - B - (C - D)| ≤ |A - C| + |B - D| := by
      intro A B C D
      calc |A - B - (C - D)| = |(A - C) - (B - D)| := by ring_nf
        _ ≤ |A - C| + |B - D| := abs_sub _ _
    refine (hsplit _ _ _ _).trans ?_
    rw [← mul_sub, ← mul_sub, abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((L : ℝ) ^ (j + 1)) ^ 2),
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((L : ℝ) ^ j) ^ 2)]
    have c1 := mul_le_mul_of_nonneg_left hb₁ (by positivity : (0 : ℝ) ≤ ((L : ℝ) ^ (j + 1)) ^ 2)
    have c2 := mul_le_mul_of_nonneg_left hb₂ (by positivity : (0 : ℝ) ≤ ((L : ℝ) ^ j) ^ 2)
    nlinarith [c1, c2]

end CauchyLipschitz

section Limits

/-- The infinite-volume kernel `t_j^μ(x, y)`: the limit of the torus kernels. -/
noncomputable def tLim (d L : ℕ) [NeZero L] (a μ : ℝ) (j : ℕ) (x y : Fin d → ℤ) : ℝ :=
  limUnder atTop (fun m : ℕ => termKernel d L (freeSeq d L a) μ (j + 1) j m x y)

theorem tendsto_tLim (hd : 3 ≤ d) (hL : 1 < L) {a μ : ℝ}
    (hlo : 1 ≤ 2 * a * (1 - ((L : ℝ) ^ 2)⁻¹)) (hhi : a ≤ 2) (hμ : 0 < μ) (j : ℕ)
    (x y : Fin d → ℤ) :
    Tendsto (fun m : ℕ => termKernel d L (freeSeq d L a) μ (j + 1) j m x y) atTop
      (𝓝 (tLim d L a μ j x y)) :=
  tendsto_nhds_limUnder (termKernel_converges hd hL hlo hhi hμ j x y)

theorem tLim_lipschitz (hd : 3 ≤ d) (hL : 1 < L) {a : ℝ}
    (hlo : 1 ≤ 2 * a * (1 - ((L : ℝ) ^ 2)⁻¹)) (hhi : a ≤ 2) (j : ℕ) (x y : Fin d → ℤ) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧ ∀ {μ₁ μ₂ : ℝ}, 0 < μ₁ → μ₁ * (L : ℝ) ^ (2 * (j + 1)) ≤ 1 →
      0 < μ₂ → μ₂ * (L : ℝ) ^ (2 * (j + 1)) ≤ 1 →
      |tLim d L a μ₁ j x y - tLim d L a μ₂ j x y| ≤ Λ * |μ₁ - μ₂| := by
  obtain ⟨Λ, hΛ, h⟩ := termKernel_lipschitz hd hL hlo hhi j x y
  refine ⟨Λ, hΛ, fun h1 h1' h2 h2' => ?_⟩
  have := ((tendsto_tLim hd hL hlo hhi h1 j x y).sub
    (tendsto_tLim hd hL hlo hhi h2 j x y)).abs
  exact le_of_tendsto this (Eventually.of_forall fun m => h m h1 h1' h2 h2')

/-- **(G3)**: the limit `μ ↓ 0` of the infinite-volume kernels exists. -/
theorem tLim_exists_zero (hd : 3 ≤ d) (hL : 1 < L) {a : ℝ}
    (hlo : 1 ≤ 2 * a * (1 - ((L : ℝ) ^ 2)⁻¹)) (hhi : a ≤ 2) (j : ℕ) (x y : Fin d → ℤ) :
    ∃ l, Tendsto (fun μ : ℝ => tLim d L a μ j x y) (𝓝[>] 0) (𝓝 l) := by
  obtain ⟨Λ, hΛ, h⟩ := tLim_lipschitz hd hL hlo hhi j x y
  have hLp : (0 : ℝ) < (L : ℝ) ^ (2 * (j + 1)) := by
    have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  rw [← cauchy_map_iff_exists_tendsto, Metric.cauchy_iff]
  refine ⟨inferInstance, fun ε hε => ?_⟩
  set δ : ℝ := min ((L : ℝ) ^ (2 * (j + 1)))⁻¹ (ε / (2 * Λ + 2)) with hδ
  have hδ0 : 0 < δ := lt_min (inv_pos.2 hLp) (by positivity)
  refine ⟨(fun μ : ℝ => tLim d L a μ j x y) '' Set.Ioo 0 δ,
    Filter.image_mem_map (Ioo_mem_nhdsGT hδ0), ?_⟩
  rintro _ ⟨μ₁, hμ₁, rfl⟩ _ ⟨μ₂, hμ₂, rfl⟩
  have hr : ∀ μ, μ ∈ Set.Ioo 0 δ → μ * (L : ℝ) ^ (2 * (j + 1)) ≤ 1 := by
    intro μ hμ
    have h1 : μ < ((L : ℝ) ^ (2 * (j + 1)))⁻¹ := hμ.2.trans_le (min_le_left _ _)
    have := mul_lt_mul_of_pos_right h1 hLp
    rw [inv_mul_cancel₀ hLp.ne'] at this
    exact this.le
  rw [Real.dist_eq]
  refine lt_of_le_of_lt (h hμ₁.1 (hr _ hμ₁) hμ₂.1 (hr _ hμ₂)) ?_
  have hd1 : |μ₁ - μ₂| < δ := by
    rw [abs_lt]; constructor <;> linarith [hμ₁.1, hμ₁.2, hμ₂.1, hμ₂.2]
  have hd2 : δ ≤ ε / (2 * Λ + 2) := min_le_right _ _
  calc Λ * |μ₁ - μ₂| ≤ Λ * (ε / (2 * Λ + 2)) :=
        mul_le_mul_of_nonneg_left (hd1.le.trans hd2) hΛ
    _ < ε := by
        rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith

/-- The kernel at `μ = 0`: the limit of `t_j^μ` as `μ ↓ 0`. -/
noncomputable def t0Lim (d L : ℕ) [NeZero L] (a : ℝ) (j : ℕ) (x y : Fin d → ℤ) : ℝ :=
  limUnder (𝓝[>] 0) (fun μ : ℝ => tLim d L a μ j x y)

theorem tendsto_t0Lim (hd : 3 ≤ d) (hL : 1 < L) {a : ℝ}
    (hlo : 1 ≤ 2 * a * (1 - ((L : ℝ) ^ 2)⁻¹)) (hhi : a ≤ 2) (j : ℕ) (x y : Fin d → ℤ) :
    Tendsto (fun μ : ℝ => tLim d L a μ j x y) (𝓝[>] 0) (𝓝 (t0Lim d L a j x y)) :=
  tendsto_nhds_limUnder (tLim_exists_zero hd hL hlo hhi j x y)

end Limits

section Prolongation

/-- **(G5)** the prolongation kernels are bounded, uniformly in the torus, `J` and the mass in the
range `μ L^{2J} ≤ 1`. -/
theorem prolong_bound (hd : 3 ≤ d) (hL : 3 ≤ L) {a : ℝ}
    (hlo : 1 ≤ 2 * a * (1 - ((L : ℝ) ^ 2)⁻¹)) (hhi : a ≤ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (J m : ℕ) {μ : ℝ}, 0 < μ → μ * (L : ℝ) ^ (2 * J) ≤ 1 →
      ∀ y u, |prolong (L := L) (m := m + 1) J (latticeLaplacian d (L ^ J * (m + 1)) μ)
        (freeSeq d L a) y u| ≤ C := by
  obtain ⟨K₀, hK₀, hK⟩ := oneScale_pointwise (d := d) (L := L) hd hL
  have hL1 : 1 < L := by omega
  have hx : (1 : ℝ) < L := by exact_mod_cast hL1
  have ha0 : 0 < a := by linarith [half_le_of_lo hL1 hlo]
  refine ⟨max 1 K₀, zero_le_one.trans (le_max_left _ _), ?_⟩
  intro J m μ hμ hJ y u
  rcases Nat.eq_zero_or_pos J with rfl | hJ1
  · simp only [prolong, Matrix.one_apply]
    split_ifs <;> simp
  · obtain ⟨n, rfl⟩ : ∃ n, J = n + 1 := ⟨J - 1, by omega⟩
    obtain ⟨haJ1, haJ2⟩ := aScale_mem hL1 hlo hhi (J := n + 1) (by omega)
    have haJ0 : 0 < aScale L a (n + 1) := by linarith
    have hA := latticeLaplacian_posDef (d := d) (ℓ := L ^ (n + 1) * (m + 1)) hμ
    have hpos := invScale_pos d L n (a := freeSeq d L a) (fun i => freeSeq_pos ha0 i)
    rw [prolong_eq_blockSpinProlong n hA (fun i => freeSeq_pos ha0 i),
      blockSpinProlong_eq_schurProlong hA _ (inv_pos.2 hpos), inv_inv, compositeAvg_eq]
    have hN : 0 < L ^ (n + 1) := Nat.pos_of_ne_zero (pow_ne_zero _ (NeZero.ne L))
    have hs := invScale_freeSeq_mul (d := d) (L := L) (by omega) hL1 ha0 (j := n + 1) (by omega)
    have hK' := schurProlong_blockAverage (d := d) (ℓ := L ^ (n + 1) * (m + 1)) (N := L ^ (n + 1))
      (m := L ^ 0 * (m + 1)) (by simp) hN (by omega) hμ haJ0 hs
    rw [hK']
    have hν : μ * ((L ^ (n + 1) : ℕ) : ℝ) ^ 2 ≤ 1 := by
      simpa [Nat.cast_pow, ← pow_mul, mul_comm] using hJ
    have := hK (k := n + 1) (N₀ := L ^ 0 * (m + 1)) (ℓ := L ^ (n + 1) * (m + 1)) (by omega)
      (by ring) (ν := μ * ((L ^ (n + 1) : ℕ) : ℝ) ^ 2) (a := aScale L a (n + 1))
      (by positivity) hν haJ1 haJ2 u y
    refine this.trans ?_
    have hr := blockDecayRate_pos (d := d) (by omega)
    have he : Real.exp (-(blockDecayRate d * torusDist d (L ^ 0 * (m + 1))
        (blockMap (L ^ (n + 1)) (L ^ 0 * (m + 1)) y) u)) ≤ 1 := by
      apply Real.exp_le_one_iff.2
      have := torusDist_nonneg_gen (d := d) (blockMap (L ^ (n + 1)) (L ^ 0 * (m + 1)) y) u
      nlinarith
    calc K₀ * _ ≤ K₀ * 1 := mul_le_mul_of_nonneg_left he hK₀
      _ ≤ max 1 K₀ := by rw [mul_one]; exact le_max_right _ _

end Prolongation

end Entries

end Balaban
