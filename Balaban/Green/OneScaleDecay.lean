/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Multiscale.ScaleMismatch
public import Balaban.Green.UnitLattice
public import Balaban.Green.BlockDistance
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# Single-scale block decay (G-5, reduction to G-2(i))

On the fine torus `Torus d (N₀ * L ^ k)` with unit fine spacing consider the single-scale
operator `-Δ + ν/N² + (a/N²) P` (`P = Q* Q` the projection onto the `N`-block constants,
`N = L ^ k`), i.e. `N⁻²` times the unit-lattice operator `fineHamiltonian = N² (-Δ) + ν + a P` of
GREEN.md (`ℓ_j = 1` units, `η = N⁻¹`).  Taking the generating set with `Ω_1 = … = Ω_k` the whole
torus (`Balaban.Green.oneScaleSet`; the layer `k` is everything), the multiscale Dirichlet
operator `H_D(0)` of `Balaban.Multiscale` is exactly this operator, and the landed
`Balaban.Multiscale.green_G2i` gives block-to-block decay in the path metric, which here is
bounded below by the torus distance over `N` (`oneScale_pathDist_ge`).

**Norm.**  For a function `h` on the fine torus and a coarse site `y` put
`‖h‖_{y} = ((N^d)⁻¹ ∑_{x ∈ block y} h(x)²)^{1/2}`
(`Balaban.Green.blockL2`), the `L²` norm over the block of `y` in unit-lattice measure
(fine sites have mass `N⁻ᵈ`).  The main result `Balaban.Green.oneScale_blockDecay`:
for `F` supported in the block of `y'`,

`‖H⁻¹ F‖_{y} ≤ C₀ e^{-δ₀ dist(y, y')} ‖F‖_{y'}`,

`H = fineHamiltonian d ℓ N N₀ ν a`, `ν ≥ 0`, `a ∈ [1/2, 2]`, with `dist` the `ℓ¹` torus distance
of the coarse torus (the unit-lattice distance) and
`C₀ = (13 L / c) e^{δ₀ d}`, `δ₀ = agmonRate d / 2`, depending on `d, L` only (uniform in `k`,
`N₀`, `ν ≥ 0`, `a`).  This is the fine-to-block bound that replaces the pointwise bound of
GREEN.md G-5(a) (the pointwise statement needs G-2(ii)).
-/

@[expose] public section

namespace Balaban.Green

open Matrix Finset Balaban Balaban.Multiscale

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L]

/-! ### The single-scale generating set -/

/-- The generating set `Ω_1 = … = Ω_k` = the whole torus (`Ω_{k+1} = ∅`): the single-scale case of
GREEN.md §1.2 (the layer `k` is the whole torus). -/
noncomputable def oneScaleSet (d L N₀ k : ℕ) [NeZero N₀] [NeZero L] (ϱ : ℝ) :
    GeneratingSet d L N₀ k ϱ where
  Ω j := if j ≤ k then Finset.univ else ∅
  top := by simp
  subset := by intro j _ hjk; simp [hjk]
  blockUnion := by
    intro j _ hjk x x' _
    simp [hjk]
  separation := by
    intro j _ hjk x hx
    exfalso
    simp [hjk.le] at hx

theorem oneScaleSet_Ω_of_le (ϱ : ℝ) {j : ℕ} (hj : j ≤ k) :
    (oneScaleSet d L N₀ k ϱ).Ω j = Finset.univ := by
  simp [oneScaleSet, hj]

theorem mem_layer_k (ϱ : ℝ) (x : Torus d (N₀ * L ^ k)) :
    x ∈ (oneScaleSet d L N₀ k ϱ).layer k := by
  rw [GeneratingSet.mem_layer]
  refine ⟨by simp [oneScaleSet], ?_⟩
  simp [oneScaleSet]

theorem layer_eq_empty (ϱ : ℝ) {j : ℕ} (hj : j < k) :
    (oneScaleSet d L N₀ k ϱ).layer j = ∅ := by
  ext x
  simp only [GeneratingSet.mem_layer, Finset.notMem_empty, iff_false, not_and, not_not]
  intro _
  simp [oneScaleSet, hj]

theorem oneScale_spacing (hk : 1 ≤ k) (ϱ : ℝ) (x : Torus d (N₀ * L ^ k)) :
    (oneScaleSet d L N₀ k ϱ).spacing x = (L : ℝ) ^ k :=
  (oneScaleSet d L N₀ k ϱ).spacing_eq hk le_rfl (mem_layer_k ϱ x)

/-! ### Identification of the Dirichlet operator -/

theorem blockProjMatrix_eq_of_sides {ℓ N m₁ m₂ : ℕ} [NeZero ℓ] [NeZero m₁] [NeZero m₂]
    (h₁ : ℓ = N * m₁) (h₂ : ℓ = N * m₂) :
    blockProjMatrix d ℓ N m₁ = blockProjMatrix d ℓ N m₂ := by
  ext x x'
  simp only [blockProjMatrix, blockMap_eq_iff_of_sides h₁ h₂ x x']

/-- For the single-scale set the full matrix `-Δ + ν + Q* a Q` is
`blockHamiltonian ν (a / N²)` with `N = L ^ k`. -/
theorem oneScale_fullMatrix (hk : 1 ≤ k) (ϱ ν a : ℝ) :
    fullMatrix (oneScaleSet d L N₀ k ϱ) (fun _ => a) ν =
      blockHamiltonian d (N₀ * L ^ k) (L ^ k) N₀ ν (a / ((L : ℝ) ^ k) ^ 2) := by
  unfold fullMatrix avgMatrix blockHamiltonian
  congr 1
  rw [Finset.sum_eq_single k]
  · congr 1
    ext x x'
    have hm : N₀ * L ^ k = L ^ k * (N₀ * L ^ (k - k)) := side_eq (N₀ := N₀) (L := L) le_rfl
    have hm' : N₀ * L ^ k = L ^ k * N₀ := mul_comm _ _
    simp only [layerProjMatrix, mem_layer_k ϱ, and_self, ite_true]
    rw [blockProjMatrix_eq_of_sides hm hm']
  · intro j hj hne
    have hjk : j < k := lt_of_le_of_ne (Finset.mem_Icc.1 hj).2 hne
    have : layerProjMatrix (oneScaleSet d L N₀ k ϱ) j = 0 := by
      ext x x'
      have hx : x ∉ (oneScaleSet d L N₀ k ϱ).layer j := by
        rw [layer_eq_empty ϱ hjk]; simp
      simp [layerProjMatrix, hx]
    rw [this, smul_zero]
  · intro h
    exact absurd (Finset.mem_Icc.2 ⟨hk, le_rfl⟩) h

/-- The unit-lattice operator is `N²` times `blockHamiltonian (ν / N²) (a / N²)`. -/
theorem fineHamiltonian_eq {ℓ N m : ℕ} [NeZero ℓ] [NeZero m] (hN : 0 < N) (ν a : ℝ) :
    fineHamiltonian d ℓ N m ν a =
      ((N : ℝ) ^ 2) • blockHamiltonian d ℓ N m (ν / (N : ℝ) ^ 2) (a / (N : ℝ) ^ 2) := by
  have hc : (N : ℝ) ^ 2 ≠ 0 := by positivity
  unfold fineHamiltonian blockHamiltonian
  rw [smul_add, smul_smul, mul_div_cancel₀ _ hc]

/-- For the single-scale set, `H_D(0)` applied to the real vector `w` is the real vector
`(-Δ + ν + a P / N²) w`. -/
theorem oneScale_dirichlet_mulVec (hk : 1 ≤ k) (ϱ ν a : ℝ) (w : Torus d (N₀ * L ^ k) → ℝ)
    (i : (oneScaleSet d L N₀ k ϱ).Ω 1) :
    (dirichletOperator (oneScaleSet d L N₀ k ϱ) (fun _ => a) ν 0 *ᵥ
        (fun j : (oneScaleSet d L N₀ k ϱ).Ω 1 => (w j : ℂ))) i =
      ((blockHamiltonian d (N₀ * L ^ k) (L ^ k) N₀ ν (a / ((L : ℝ) ^ k) ^ 2) *ᵥ w) i : ℝ) := by
  have hΩ := oneScaleSet_Ω_of_le (d := d) (L := L) (N₀ := N₀) (k := k) ϱ (j := 1) hk
  have h0 : Matrix.diagonal (0 : (oneScaleSet d L N₀ k ϱ).Ω 1 → ℂ) = 0 := Matrix.diagonal_zero
  unfold dirichletOperator
  rw [oneScale_fullMatrix hk, h0, add_zero]
  simp only [Matrix.mulVec, dotProduct, restrictOp, Matrix.submatrix_apply, Matrix.map_apply]
  push_cast
  rw [Finset.sum_coe_sort ((oneScaleSet d L N₀ k ϱ).Ω 1)
    (fun j => (algebraMap ℝ ℂ ((blockHamiltonian d (N₀ * L ^ k) (L ^ k) N₀ ν
      (a / ((L : ℝ) ^ k) ^ 2)) i j)) * (w j : ℂ)),
    Finset.sum_congr hΩ fun _ _ => rfl]
  simp [Algebra.algebraMap_eq_smul_one]

/-! ### The path metric dominates the torus distance -/

theorem oneScale_pathDist_ge (hk : 1 ≤ k) (ϱ : ℝ) (z z' : Torus d (N₀ * L ^ k)) :
    ENNReal.ofReal (torusDist d (N₀ * L ^ k) z z' / (L : ℝ) ^ k) ≤
      (oneScaleSet d L N₀ k ϱ).pathDist z z' := by
  set G := oneScaleSet d L N₀ k ϱ with hG
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hL : (0 : ℝ) < (L : ℝ) ^ k := by positivity
  have hF : ∀ x x', x ∈ G.Ω 1 → x' ∈ G.Ω 1 → Adj x x' →
      |torusDist d (N₀ * L ^ k) x z' / (L : ℝ) ^ k -
          torusDist d (N₀ * L ^ k) x' z' / (L : ℝ) ^ k| ≤ G.bondCost x x' := by
    intro x x' _ _ hadj
    have hb : G.bondCost x x' = 1 / (L : ℝ) ^ k := by
      unfold GeneratingSet.bondCost
      rw [hG, oneScale_spacing hk, oneScale_spacing hk, max_self]
    rw [hb, ← sub_div, abs_div, abs_of_pos hL]
    have h1 := Adj.torusDist_le hadj
    have t1 := torusDist_triangle' x x' z'
    have t2 := torusDist_triangle' x' x z'
    have c := torusDist_comm' (d := d) (L := L) (N₀ := N₀) (k := k) x x'
    have : |torusDist d (N₀ * L ^ k) x z' - torusDist d (N₀ * L ^ k) x' z'| ≤ 1 := by
      rw [abs_le]; constructor <;> linarith
    exact div_le_div_of_nonneg_right this hL.le
  have h := G.ofReal_sub_le_pathDist (fun x => torusDist d (N₀ * L ^ k) x z' / (L : ℝ) ^ k) hF z' z
  simp only [torusDist_self', zero_div, sub_zero] at h
  rwa [GeneratingSet.pathDist_comm] at h

/-! ### The core block decay -/

/-- The decay rate `δ₀ = agmonRate d / 2` of the single-scale block bound. -/
noncomputable def blockDecayRate (d : ℕ) : ℝ := agmonRate d / 2

/-- The constant `C₀ = (13 L / c) e^{δ₀ d}` of the single-scale block bound. -/
noncomputable def blockDecayConst (d L : ℕ) : ℝ :=
  13 * L / poincareConst d * Real.exp (blockDecayRate d * d)

theorem blockDecayRate_pos (hd : 0 < d) : 0 < blockDecayRate d := by
  unfold blockDecayRate; have := agmonRate_pos hd; positivity

theorem blockDecayConst_pos (hd : 0 < d) : 0 < blockDecayConst d L := by
  unfold blockDecayConst
  have := poincareConst_pos hd
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  positivity

/-- **Core single-scale block decay (raw form).**  If `B w = F` for
`B = -Δ + ν/N² + (a/N²) P` (`N = L ^ k`) and `F` is supported in the block `y'`, then
`‖w‖_{ℓ²(block y)} ≤ C₀ e^{-δ₀ dist(y, y')} N² ‖F‖_{ℓ²}`, for `ν ≥ 0`, `a ∈ [1/2, 2]`. -/
theorem oneScale_core (hd : 0 < d) (hk : 1 ≤ k) {ν a : ℝ} (hν : 0 ≤ ν) (ha1 : 1 / 2 ≤ a)
    (ha2 : a ≤ 2) {w F : Torus d (N₀ * L ^ k) → ℝ}
    (hBw : blockHamiltonian d (N₀ * L ^ k) (L ^ k) N₀ (ν / ((L : ℝ) ^ k) ^ 2)
      (a / ((L : ℝ) ^ k) ^ 2) *ᵥ w = F) {y y' : Torus d N₀}
    (hF : ∀ x, F x ≠ 0 → blockMap (L ^ k) N₀ x = y') :
    Real.sqrt (∑ x ∈ blockFibre (L ^ k) N₀ y, w x ^ 2) ≤
      blockDecayConst d L * Real.exp (-(blockDecayRate d * torusDist d N₀ y y')) *
        ((L : ℝ) ^ k) ^ 2 * Real.sqrt (∑ x, F x ^ 2) := by
  classical
  have hε := agmonRate_pos hd
  have hp0 := poincareConst_pos hd
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hN : 0 < L ^ k := Nat.pos_of_ne_zero (pow_ne_zero _ (NeZero.ne L))
  have hℓ : N₀ * L ^ k = L ^ k * N₀ := mul_comm _ _
  have hm : N₀ * L ^ k = L ^ k * (N₀ * L ^ (k - k)) := side_eq (N₀ := N₀) (L := L) le_rfl
  obtain ⟨z, hz⟩ := exists_blockMap_eq hℓ hN y
  obtain ⟨z', hz'⟩ := exists_blockMap_eq hℓ hN y'
  set ϱ : ℝ := 1 + 2 * Real.log L / agmonRate d with hϱdef
  set G := oneScaleSet d L N₀ k ϱ with hG
  have hΩ : G.Ω 1 = Finset.univ := oneScaleSet_Ω_of_le ϱ hk
  have hlog : 0 ≤ Real.log L := Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L))
  have hϱ : 1 ≤ ϱ := by
    have : 0 ≤ 2 * Real.log L / agmonRate d := by positivity
    rw [hϱdef]; linarith
  have hsep : (L : ℝ) ≤ Real.exp (agmonRate d / 2 * (ϱ - 1)) := by
    have : agmonRate d / 2 * (ϱ - 1) = Real.log L := by
      rw [hϱdef]; field_simp; ring
    rw [this, Real.exp_log hL0]
  have hadm : IsAdmissibleWeights k (fun _ : ℕ => a) := fun j _ _ => ⟨ha1, ha2⟩
  have hα : ∀ x, ‖(0 : G.Ω 1 → ℂ) x‖ ≤ coerciveConst d / (2 * (G.spacing x) ^ 2) := by
    intro x
    simp only [Pi.zero_apply, norm_zero]
    exact div_nonneg (coerciveConst_pos hd).le (by positivity)
  have hν' : 0 ≤ ν / ((L : ℝ) ^ k) ^ 2 := by positivity
  set u : G.Ω 1 → ℂ := fun j => (w j : ℂ) with hu_def
  set f : G.Ω 1 → ℂ := fun j => (F j : ℂ) with hf_def
  have hu : dirichletOperator G (fun _ => a) (ν / ((L : ℝ) ^ k) ^ 2) 0 *ᵥ u = f := by
    funext i
    have h := oneScale_dirichlet_mulVec hk ϱ (ν / ((L : ℝ) ^ k) ^ 2) a w i
    rw [hBw] at h
    exact h
  have hsupp : ∀ x : G.Ω 1, f x ≠ 0 → jBlock d L N₀ k k x = jBlock d L N₀ k k z' := by
    intro x hx
    have hFx : F x ≠ 0 := by
      intro h0; apply hx; simp [hf_def, h0]
    have h1 : blockMap (L ^ k) N₀ (x : Torus d (N₀ * L ^ k)) = blockMap (L ^ k) N₀ z' := by
      rw [hF _ hFx, hz']
    exact (blockMap_eq_iff_of_sides hℓ hm _ _).1 h1
  set t : ℝ := torusDist d (N₀ * L ^ k) z z' / (L : ℝ) ^ k with ht_def
  have ht0 : 0 ≤ t := div_nonneg (torusDist_nonneg' _ _) (by positivity)
  have ht : ENNReal.ofReal t ≤ G.pathDist z z' := oneScale_pathDist_ge hk ϱ z z'
  have key := green_G2i G hd hν' hadm 0 hα hk le_rfl hk le_rfl (mem_layer_k ϱ z)
    (mem_layer_k ϱ z') hu hsupp ht0 ht hε.le le_rfl hϱ hsep
  have hblk : G.blk k z = blockFibre (L ^ k) N₀ y := by
    ext x
    rw [GeneratingSet.mem_blk, mem_blockFibre, ← hz]
    exact blockMap_eq_iff_of_sides hm hℓ x z
  have hval : ∀ x, ‖zeroExt (G.Ω 1) u x‖ = |w x| := by
    intro x
    have hmem : x ∈ G.Ω 1 := by rw [hΩ]; exact Finset.mem_univ x
    simp [zeroExt, hmem, hu_def]
  have hsum : ∑ x ∈ G.blk k z, ‖zeroExt (G.Ω 1) u x‖ ^ 2 =
      ∑ x ∈ blockFibre (L ^ k) N₀ y, w x ^ 2 := by
    rw [hblk]
    exact Finset.sum_congr rfl fun x _ => by rw [hval, sq_abs]
  have hnorm : Green.sqNorm f = ∑ x, F x ^ 2 := by
    have h1 := Finset.sum_coe_sort (G.Ω 1) (fun x : Torus d (N₀ * L ^ k) => ‖(F x : ℂ)‖ ^ 2)
    have h2 : ∑ x ∈ G.Ω 1, ‖(F x : ℂ)‖ ^ 2 = ∑ x, F x ^ 2 := by
      rw [Finset.sum_congr hΩ fun _ _ => rfl]
      exact Finset.sum_congr rfl fun x _ => by rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    exact h1.trans h2
  have hLHS : Real.sqrt (∑ x ∈ blockFibre (L ^ k) N₀ y, w x ^ 2) ≤
      13 * L / poincareConst d * Real.exp (-(agmonRate d / 2 * t)) * ((L : ℝ) ^ k) ^ 2 *
        Real.sqrt (Green.sqNorm f) := by
    rw [← hsum]
    have h0 : 0 ≤ (L : ℝ) ^ k * Real.sqrt (∑ x ∈ G.blk k z, ∑ μ : Fin d,
        ‖zeroExt (G.Ω 1) u (x + Pi.single μ 1) - zeroExt (G.Ω 1) u x‖ ^ 2) :=
      mul_nonneg (pow_nonneg hL0.le k) (Real.sqrt_nonneg _)
    linarith [key]
  have hd1 := torusDist_coarse_le hℓ hN hz hz'
  have hd2 : torusDist d N₀ y y' ≤ t + d := by
    push_cast at hd1
    rw [ht_def]; exact hd1
  have hexp : Real.exp (-(agmonRate d / 2 * t)) ≤
      Real.exp (blockDecayRate d * d) * Real.exp (-(blockDecayRate d * torusDist d N₀ y y')) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    unfold blockDecayRate
    nlinarith [mul_nonneg hε.le (sub_nonneg.2 hd2)]
  have hC : 0 ≤ 13 * (L : ℝ) / poincareConst d := div_nonneg (by positivity) hp0.le
  have hS : 0 ≤ ((L : ℝ) ^ k) ^ 2 * Real.sqrt (∑ x, F x ^ 2) := by positivity
  calc Real.sqrt (∑ x ∈ blockFibre (L ^ k) N₀ y, w x ^ 2)
      ≤ 13 * L / poincareConst d * Real.exp (-(agmonRate d / 2 * t)) * ((L : ℝ) ^ k) ^ 2 *
          Real.sqrt (Green.sqNorm f) := hLHS
    _ ≤ 13 * L / poincareConst d * (Real.exp (blockDecayRate d * d) *
          Real.exp (-(blockDecayRate d * torusDist d N₀ y y'))) * ((L : ℝ) ^ k) ^ 2 *
          Real.sqrt (∑ x, F x ^ 2) := by
        rw [hnorm]
        have := mul_le_mul_of_nonneg_left hexp hC
        calc _ = (13 * (L : ℝ) / poincareConst d * Real.exp (-(agmonRate d / 2 * t))) *
              (((L : ℝ) ^ k) ^ 2 * Real.sqrt (∑ x, F x ^ 2)) := by ring
          _ ≤ (13 * (L : ℝ) / poincareConst d * (Real.exp (blockDecayRate d * d) *
              Real.exp (-(blockDecayRate d * torusDist d N₀ y y')))) *
              (((L : ℝ) ^ k) ^ 2 * Real.sqrt (∑ x, F x ^ 2)) :=
            mul_le_mul_of_nonneg_right this hS
          _ = _ := by ring
    _ = _ := by unfold blockDecayConst; ring

end Balaban.Green
