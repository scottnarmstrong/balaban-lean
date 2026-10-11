module

public import Balaban.Multiscale.Pointwise48
public import Balaban.Green.OneScaleDecay
public import Balaban.Green.TranslationInvariant
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# Pointwise decay of the fine-to-block kernel (G-2(ii), single layer)

`oneScale_pointwise`: the entries of `K = a G Q*` (`Balaban.Green.fineToBlockKernel`) satisfy
`|K(x, y')| ≤ K₀ e^{-δ₀ dist(block x, y')}` for every fine site `x` (not only in the block `L²`
sense of `fineToBlockKernel_decay`), with `K₀, δ₀` depending on `d, L, Λ` only, uniformly in
`k ≥ 1`, the volume, `ν ∈ [0, Λ]` and `a ∈ [1/2, 2]`.  It is the pointwise Proposition 4.8
(`Balaban.Multiscale.prop48`) applied to the single-scale generating set (`oneScaleSet`); it
needs `d ≥ 3`, `L ≥ 3`.
-/

@[expose] public section

namespace Balaban.Green

open Matrix Finset Balaban Balaban.Multiscale

variable {d L : ℕ} [NeZero L]

theorem oneScale_pointwise_le (hd : 3 ≤ d) (hL : 3 ≤ L) (Λ : ℝ) (hΛ : 0 ≤ Λ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {k N₀ ℓ : ℕ} [NeZero N₀] [NeZero ℓ], 1 ≤ k → ℓ = N₀ * L ^ k →
      ∀ {ν a : ℝ}, 0 ≤ ν → ν ≤ Λ → 1 / 2 ≤ a → a ≤ 2 → ∀ (y' : Torus d N₀) (x : Torus d ℓ),
      |fineToBlockKernel d ℓ (L ^ k) N₀ ν a x y'| ≤
        K * Real.exp (-(blockDecayRate d * torusDist d N₀ (blockMap (L ^ k) N₀ x) y')) := by
  classical
  obtain ⟨K2, hK2, hP⟩ := prop48 (d := d) (L := L) hd hL Λ hΛ
  have hd0 : 0 < d := by omega
  refine ⟨2 * K2 * Real.exp (blockDecayRate d * d), by positivity, ?_⟩
  intro k N₀ ℓ _ _ hk hℓ0 ν a hν hν1 ha1 ha2 y' x
  subst hℓ0
  have hε := agmonRate_pos hd0
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hN : 0 < L ^ k := Nat.pos_of_ne_zero (pow_ne_zero _ (NeZero.ne L))
  have hNr : (0 : ℝ) < ((L : ℝ) ^ k) := by positivity
  have hℓ : N₀ * L ^ k = L ^ k * N₀ := mul_comm _ _
  have hm : N₀ * L ^ k = L ^ k * (N₀ * L ^ (k - k)) := side_eq (N₀ := N₀) (L := L) le_rfl
  obtain ⟨z', hz'⟩ := exists_blockMap_eq hℓ hN y'
  set ϱ : ℝ := 1 + 2 * d * Real.log L / agmonRate d with hϱdef
  set G := oneScaleSet d L N₀ k ϱ with hG
  have hΩ : G.Ω 1 = Finset.univ := oneScaleSet_Ω_of_le ϱ hk
  have hlog : 0 ≤ Real.log L :=
    Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L))
  have hϱ : 1 ≤ ϱ := by
    have : 0 ≤ 2 * d * Real.log L / agmonRate d := by positivity
    rw [hϱdef]; linarith
  have hsep : (L : ℝ) ^ d ≤ Real.exp (agmonRate d / 2 * (ϱ - 1)) := by
    have : agmonRate d / 2 * (ϱ - 1) = Real.log ((L : ℝ) ^ d) := by
      rw [hϱdef, Real.log_pow]; field_simp; ring
    rw [this, Real.exp_log (by positivity)]
  have hadm : IsAdmissibleWeights k (fun _ : ℕ => a) := fun j _ _ => ⟨ha1, ha2⟩
  have hα : ∀ x, ‖(0 : G.Ω 1 → ℂ) x‖ ≤ coerciveConst d / (2 * (G.spacing x) ^ 2) := by
    intro x
    simp only [Pi.zero_apply, norm_zero]
    exact div_nonneg (coerciveConst_pos hd0).le (by positivity)
  have hν' : 0 ≤ ν / ((L : ℝ) ^ k) ^ 2 := by positivity
  have hν'1 : ν / ((L : ℝ) ^ k) ^ 2 * ((L : ℝ) ^ k) ^ 2 ≤ Λ := by
    rw [div_mul_cancel₀ _ (by positivity)]; exact hν1
  set B := blockHamiltonian d (N₀ * L ^ k) (L ^ k) N₀ (ν / ((L : ℝ) ^ k) ^ 2)
    (a / ((L : ℝ) ^ k) ^ 2) with hB
  have hBinv : B * B⁻¹ = 1 :=
    blockHamiltonian_mul_inv hℓ hN hd0 hν' (by positivity)
  set w : Torus d (N₀ * L ^ k) → ℝ := B⁻¹ *ᵥ blockIndicator (L ^ k) N₀ y' with hw
  have hBw : B *ᵥ w = blockIndicator (L ^ k) N₀ y' := by
    rw [hw, Matrix.mulVec_mulVec, hBinv, Matrix.one_mulVec]
  set f : G.Ω 1 → ℂ := fun j => ((blockIndicator (ℓ := N₀ * L ^ k) (L ^ k) N₀ y' (j : Torus d (N₀ * L ^ k)) : ℝ) : ℂ) with hf
  have hu : dirichletOperator G (fun _ => a) (ν / ((L : ℝ) ^ k) ^ 2) 0 *ᵥ
      (fun j : G.Ω 1 => (w j : ℂ)) = f := by
    funext i
    have h := oneScale_dirichlet_mulVec hk ϱ (ν / ((L : ℝ) ^ k) ^ 2) a w i
    rw [hBw] at h
    exact h
  have hsupp : ∀ i : G.Ω 1, f i ≠ 0 → jBlock d L N₀ k k i = jBlock d L N₀ k k z' := by
    intro i hi
    have hFx : blockIndicator (ℓ := N₀ * L ^ k) (L ^ k) N₀ y' (i : Torus d (N₀ * L ^ k)) ≠ 0 := by
      intro h0; apply hi; simp [hf, h0]
    have h1 : blockMap (L ^ k) N₀ (i : Torus d (N₀ * L ^ k)) = blockMap (L ^ k) N₀ z' := by
      rw [blockIndicator_support y' _ hFx, hz']
    exact (blockMap_eq_iff_of_sides hℓ hm _ _).1 h1
  let S : PtSetting G Λ :=
    { a := fun _ => a, ν := ν / ((L : ℝ) ^ k) ^ 2, α := 0, f := f, j' := k, y' := z'
      hd := hd, hL := hL, hν0 := hν', hν1 := hν'1, ha := hadm, hα := hα, hϱ := hϱ,
      hsep := hsep, hj'1 := hk, hj'k := le_rfl, hy' := mem_layer_k ϱ z', hsupp := hsupp }
  have hDu : IsUnit (dirichletOperator G (fun _ => a) (ν / ((L : ℝ) ^ k) ^ 2) 0) :=
    dirichletOperator_isUnit G hd0 hν' hadm 0 hα
  have hSu : S.u = fun j : G.Ω 1 => (w j : ℂ) := by
    have h1 : dirichletOperator G (fun _ => a) (ν / ((L : ℝ) ^ k) ^ 2) 0 *ᵥ S.u = f :=
      S.hu
    have h2 := h1.trans hu.symm
    have h3 := congrArg (fun v => (dirichletOperator G (fun _ => a) (ν / ((L : ℝ) ^ k) ^ 2) 0)⁻¹ *ᵥ v) h2
    simp only [Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hDu), Matrix.one_mulVec] at h3
    exact h3
  have hxΩ : x ∈ G.Ω 1 := by rw [hΩ]; exact Finset.mem_univ x
  have hMf : ∀ i, ‖S.f i‖ ≤ 1 := by
    intro i
    show ‖((blockIndicator (ℓ := N₀ * L ^ k) (L ^ k) N₀ y' (i : Torus d (N₀ * L ^ k)) : ℝ) : ℂ)‖ ≤ 1
    rw [Complex.norm_real, Real.norm_eq_abs]
    unfold blockIndicator
    split_ifs <;> simp
  obtain ⟨hfin, htop⟩ := hP G S zero_le_one hMf hxΩ
  have hKx : fineToBlockKernel d (N₀ * L ^ k) (L ^ k) N₀ ν a x y' =
      a * (((L : ℝ) ^ k) ^ 2)⁻¹ * w x := by
    simp only [fineToBlockKernel, Matrix.smul_apply, smul_eq_mul]
    rw [mul_blockPullbackMatrix_apply, fineHamiltonian_inv hℓ hN hd0 hν (by linarith),
      Matrix.smul_mulVec]
    simp [hw, hB, Nat.cast_pow, mul_assoc]
  have hwU : |w x| ≤ S.U x := by
    have h := S.norm_ut_le_U x
    have e : S.ut x = (w x : ℂ) := by
      simp only [PtSetting.ut, zeroExt, hxΩ, ↓reduceDIte, hSu]
    rw [e, Complex.norm_real, Real.norm_eq_abs] at h
    exact h
  have hcoarse := torusDist_coarse_le (d := d) hℓ hN (z := x) (z' := z') rfl hz'
  have hpd := oneScale_pathDist_ge hk ϱ x z'
  have hSy : S.y' = z' := rfl
  have hSj : S.j' = k := rfl
  rw [hKx]
  have hcoef : 0 ≤ a * (((L : ℝ) ^ k) ^ 2)⁻¹ := by positivity
  by_cases hinf : G.pathDist x z' = ⊤
  · have h0 := htop (by rw [hSy]; exact hinf)
    have : |w x| ≤ 0 := h0 ▸ hwU
    have hw0 : w x = 0 := abs_nonpos_iff.1 this
    rw [hw0, mul_zero, abs_zero]; positivity
  · have hU := hfin (by rw [hSy]; exact hinf)
    rw [hSy, hSj] at hU
    set t0 := torusDist d (N₀ * L ^ k) x z' / (L : ℝ) ^ k with ht0
    have ht : t0 ≤ (G.pathDist x z').toReal := by
      have := ENNReal.toReal_mono hinf hpd
      rwa [ENNReal.toReal_ofReal (div_nonneg (torusDist_nonneg' _ _) hNr.le)] at this
    have hcoarse' : torusDist d N₀ (blockMap (L ^ k) N₀ x) y' ≤ t0 + d := by
      simpa [ht0] using hcoarse
    have hexp : Real.exp (-(agmonRate d / 2 * (G.pathDist x z').toReal)) ≤
        Real.exp (blockDecayRate d * d) *
          Real.exp (-(blockDecayRate d * torusDist d N₀ (blockMap (L ^ k) N₀ x) y')) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.2
      unfold blockDecayRate
      nlinarith [mul_nonneg hε.le (sub_nonneg.2 ht), mul_nonneg hε.le (sub_nonneg.2 hcoarse')]
    have hLk : (((L : ℝ) ^ k) ^ 2)⁻¹ * ((L : ℝ) ^ (2 * k) * 1) = 1 := by
      rw [pow_mul', mul_one, inv_mul_cancel₀ (by positivity)]
    rw [abs_mul, abs_of_nonneg hcoef]
    have hw' : |w x| ≤ K2 * Real.exp (-(agmonRate d / 2 * (G.pathDist x z').toReal)) *
        ((L : ℝ) ^ (2 * k) * 1) := hwU.trans hU
    calc a * (((L : ℝ) ^ k) ^ 2)⁻¹ * |w x|
        ≤ a * (((L : ℝ) ^ k) ^ 2)⁻¹ * (K2 * Real.exp (-(agmonRate d / 2 *
            (G.pathDist x z').toReal)) * ((L : ℝ) ^ (2 * k) * 1)) :=
          mul_le_mul_of_nonneg_left hw' hcoef
      _ = a * (K2 * Real.exp (-(agmonRate d / 2 * (G.pathDist x z').toReal))) := by
          have : a * (((L : ℝ) ^ k) ^ 2)⁻¹ * (K2 * Real.exp (-(agmonRate d / 2 * (G.pathDist x z').toReal)) * ((L : ℝ) ^ (2 * k) * 1)) = a * (K2 * Real.exp (-(agmonRate d / 2 * (G.pathDist x z').toReal))) * ((((L : ℝ) ^ k) ^ 2)⁻¹ * ((L : ℝ) ^ (2 * k) * 1)) := by ring
          rw [this, hLk, mul_one]
      _ ≤ 2 * (K2 * (Real.exp (blockDecayRate d * d) *
            Real.exp (-(blockDecayRate d * torusDist d N₀ (blockMap (L ^ k) N₀ x) y')))) := by
          apply mul_le_mul ha2 (mul_le_mul_of_nonneg_left hexp hK2) (by positivity)
          norm_num
      _ = _ := by ring

/-- `oneScale_pointwise_le` at `Λ = 1`: the unit-lattice masses `ν ∈ [0, 1]`. -/
theorem oneScale_pointwise (hd : 3 ≤ d) (hL : 3 ≤ L) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {k N₀ ℓ : ℕ} [NeZero N₀] [NeZero ℓ], 1 ≤ k → ℓ = N₀ * L ^ k →
      ∀ {ν a : ℝ}, 0 ≤ ν → ν ≤ 1 → 1 / 2 ≤ a → a ≤ 2 → ∀ (y' : Torus d N₀) (x : Torus d ℓ),
      |fineToBlockKernel d ℓ (L ^ k) N₀ ν a x y'| ≤
        K * Real.exp (-(blockDecayRate d * torusDist d N₀ (blockMap (L ^ k) N₀ x) y')) :=
  oneScale_pointwise_le hd hL 1 zero_le_one

end Balaban.Green
