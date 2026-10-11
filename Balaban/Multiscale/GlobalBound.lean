/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Multiscale.Pointwise48
public import Balaban.Multiscale.Counting

/-!
# The global weighted bound (GREEN.md G-2(iv), consumed bound C1)

For `u = G_D(α) f`, with `ℓ² |f| ≤ C_f` on `Ω₁` (i.e. `|f|₂ ≤ C_f`), we prove
`|ũ|₀ + |∂u|₁ + |Δ^D u|₂ ≤ B₀ C_f`.

The source `f` is decomposed over the blocks of the generating set: for `y ∈ Ω₁` let `f_y` be the
restriction of `f` to the block of `y` (at the layer of `y`), so that `f = ∑_y ℓ(y)^{-d} f_y`
(`sum_siteWeight_blockPiece`, each block has `ℓ^d` sites).  The landed pointwise decay
`prop48` bounds each piece, and the counting lemma `sum_siteWeight_decay_le` sums the decay.
-/

@[expose] public section

noncomputable section

namespace Balaban.Multiscale

open Finset Matrix Balaban Balaban.LatticeGreen

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- The restriction of `f` to the block of `y` at the layer of `y`. -/
def blockPiece (G : GeneratingSet d L N₀ k ϱ) (f : G.Ω 1 → ℂ) (y : G.Ω 1) : G.Ω 1 → ℂ :=
  fun x => if jBlock d L N₀ k (G.layerIndex y) x = jBlock d L N₀ k (G.layerIndex y) y
    then f x else 0

/-- Each block has `ℓ^d` sites, so the weights `ℓ(y)^{-d}` of the sites of a block add up to `1`. -/
theorem sum_siteWeight_blockPiece (G : GeneratingSet d L N₀ k ϱ) (f : G.Ω 1 → ℂ)
    (x : G.Ω 1) :
    ∑ y : G.Ω 1, (siteWeight G y : ℂ) * blockPiece G f y x = f x := by
  classical
  obtain ⟨hj1, hjk, hxl⟩ := G.layerIndex_spec x.2
  set j := G.layerIndex (x : Torus d (N₀ * L ^ k)) with hj
  have hcond : ∀ y : G.Ω 1, (jBlock d L N₀ k (G.layerIndex (y : Torus d (N₀ * L ^ k))) x =
      jBlock d L N₀ k (G.layerIndex (y : Torus d (N₀ * L ^ k))) y) ↔
      jBlock d L N₀ k j y = jBlock d L N₀ k j x := by
    intro y
    obtain ⟨hj1', hjk', hyl⟩ := G.layerIndex_spec y.2
    constructor
    · intro h
      have hxl' : (x : Torus d (N₀ * L ^ k)) ∈ G.layer (G.layerIndex (y : Torus d (N₀ * L ^ k))) :=
        (G.mem_layer_iff hj1' hjk' h.symm).1 hyl
      have : G.layerIndex (y : Torus d (N₀ * L ^ k)) = j :=
        (G.layerIndex_eq hj1' hjk' hxl').symm ▸ rfl
      rw [← this]; exact h.symm
    · intro h
      have hyl' : (y : Torus d (N₀ * L ^ k)) ∈ G.layer j := (G.mem_layer_iff hj1 hjk h).2 hxl
      have : G.layerIndex (y : Torus d (N₀ * L ^ k)) = j := G.layerIndex_eq hj1 hjk hyl'
      rw [this]; exact h.symm
  have hw : ∀ y : G.Ω 1, jBlock d L N₀ k j y = jBlock d L N₀ k j x →
      siteWeight G y = (((L : ℝ) ^ j)⁻¹) ^ d := by
    intro y h
    have hyl' : (y : Torus d (N₀ * L ^ k)) ∈ G.layer j :=
      (G.mem_layer_iff hj1 hjk h).2 hxl
    unfold siteWeight
    rw [G.layerIndex_eq hj1 hjk hyl']
  have key : ∀ y : G.Ω 1, (siteWeight G y : ℂ) * blockPiece G f y x =
      ((if jBlock d L N₀ k j y = jBlock d L N₀ k j x then (((L : ℝ) ^ j)⁻¹) ^ d else 0 : ℝ) : ℂ) *
        f x := by
    intro y
    unfold blockPiece
    by_cases h : jBlock d L N₀ k j y = jBlock d L N₀ k j x
    · have h' := (hcond y).2 h
      simp only [h', h, ↓reduceIte, hw y h]
    · have h' : ¬ (jBlock d L N₀ k (G.layerIndex (y : Torus d (N₀ * L ^ k))) x =
          jBlock d L N₀ k (G.layerIndex (y : Torus d (N₀ * L ^ k))) y) := fun h2 => h ((hcond y).1 h2)
      simp [h, h']
  simp_rw [key]
  rw [← Finset.sum_mul]
  have hsum : ∑ y : G.Ω 1, (if jBlock d L N₀ k j y = jBlock d L N₀ k j x then
      (((L : ℝ) ^ j)⁻¹) ^ d else 0 : ℝ) = 1 := by
    rw [Finset.sum_coe_sort (G.Ω 1) (fun y => if jBlock d L N₀ k j y = jBlock d L N₀ k j x then
      (((L : ℝ) ^ j)⁻¹) ^ d else 0 : Torus d (N₀ * L ^ k) → ℝ)]
    rw [Finset.sum_subset (Finset.subset_univ (G.Ω 1))]
    · rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      have hfib : (Finset.univ.filter fun y : Torus d (N₀ * L ^ k) =>
          jBlock d L N₀ k j y = jBlock d L N₀ k j x) =
          blockFibre (L ^ j) (N₀ * L ^ (k - j)) (jBlock d L N₀ k j x) := by
        ext y
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_blockFibre]; rfl
      rw [hfib, card_blockFibre (side_eq hjk)]
      push_cast
      have : (0 : ℝ) < (L : ℝ) ^ j := by
        have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
        positivity
      rw [← mul_pow, mul_inv_cancel₀ this.ne', one_pow]
    · intro y _ hy
      have : ¬ jBlock d L N₀ k j y = jBlock d L N₀ k j x := by
        intro h
        exact hy (G.layer_subset hj1 hjk ((G.mem_layer_iff hj1 hjk h).2 hxl))
      simp [this]
  rw [← Complex.ofReal_sum, hsum, Complex.ofReal_one, one_mul]

theorem mem_layer_of_blockPiece (G : GeneratingSet d L N₀ k ϱ) (y x : G.Ω 1)
    (h : jBlock d L N₀ k (G.layerIndex (y : Torus d (N₀ * L ^ k))) x =
      jBlock d L N₀ k (G.layerIndex (y : Torus d (N₀ * L ^ k))) y) :
    G.spacing (x : Torus d (N₀ * L ^ k)) = G.spacing (y : Torus d (N₀ * L ^ k)) := by
  obtain ⟨hj1, hjk, hyl⟩ := G.layerIndex_spec y.2
  have hxl := (G.mem_layer_iff hj1 hjk h.symm).1 hyl
  rw [G.spacing_eq hj1 hjk hxl, G.spacing_eq hj1 hjk hyl]

theorem PtSetting.spacing_mul_diff_le_U {G : GeneratingSet d L N₀ k ϱ} (S : PtSetting G)
    (x : Torus d (N₀ * L ^ k)) (μ : Fin d) :
    G.spacing x * ‖S.ut (x + Pi.single μ 1) - S.ut x‖ ≤ S.U x := by
  unfold PtSetting.U
  have h1 : ‖S.ut (x + Pi.single μ 1) - S.ut x‖ ≤
      ∑ μ' : Fin d, ‖S.ut (x + Pi.single μ' 1) - S.ut x‖ :=
    by
    apply Finset.single_le_sum (f := fun μ' : Fin d => ‖S.ut (x + Pi.single μ' 1) - S.ut x‖)
    · intro μ' _
      exact norm_nonneg _
    · exact Finset.mem_univ μ
  have h2 := mul_le_mul_of_nonneg_left h1 (spacing_pos G (x := x)).le
  linarith [norm_nonneg (S.ut x)]

/-- **Pointwise global bound.**  If `ℓ² |f| ≤ C_f` on `Ω₁` then for `u = H_D(α)⁻¹ f` and every
`x ∈ Ω₁`, `|ũ(x)|` and `ℓ(x) |ũ(x + e_μ) - ũ(x)|` are at most `B C_f`. -/
theorem global_pointwise (hd : 3 ≤ d) (hL : 3 ≤ L) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ {k N₀ : ℕ} [NeZero N₀] {ϱ : ℝ} (G : GeneratingSet d L N₀ k ϱ)
      {a : ℕ → ℝ} {ν : ℝ}, 0 ≤ ν → ν * ((L : ℝ) ^ k) ^ 2 ≤ 1 →
      IsAdmissibleWeights k a → ∀ {α : G.Ω 1 → ℂ},
      (∀ x, ‖α x‖ ≤ coerciveConst d / (2 * (G.spacing x) ^ 2)) →
      2 * d * Real.log L ≤ agmonRate d / 2 / 2 * (ϱ - 1) → ∀ (f : G.Ω 1 → ℂ) {Cf : ℝ},
      0 ≤ Cf → (∀ x : G.Ω 1, (G.spacing (x : Torus d (N₀ * L ^ k))) ^ 2 * ‖f x‖ ≤ Cf) →
      ∀ {x : Torus d (N₀ * L ^ k)}, x ∈ G.Ω 1 →
      ‖zeroExt (G.Ω 1) ((dirichletOperator G a ν α)⁻¹ *ᵥ f) x‖ ≤ B * Cf ∧
      ∀ μ : Fin d, G.spacing x * ‖zeroExt (G.Ω 1) ((dirichletOperator G a ν α)⁻¹ *ᵥ f)
        (x + Pi.single μ 1) - zeroExt (G.Ω 1) ((dirichletOperator G a ν α)⁻¹ *ᵥ f) x‖ ≤ B * Cf := by
  classical
  obtain ⟨K2, hK2, hP⟩ := prop48 (d := d) (L := L) hd hL
  have hε := agmonRate_pos (d := d) (by omega)
  have hγ0 : 0 < agmonRate d / 2 := by positivity
  refine ⟨K2 * countConst d L (agmonRate d / 2), mul_nonneg hK2 ?_, ?_⟩
  · exact tsum_nonneg fun m => by positivity
  intro k N₀ _ ϱ G a ν hν0 hν1 ha α hα hϱ f Cf hCf hf x hx
  have hL3 : (1 : ℝ) < L := by exact_mod_cast (by omega : 1 < L)
  have hlog : 0 < Real.log L := Real.log_pos hL3
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hϱ1 : 1 < ϱ := by
    by_contra hcon
    push Not at hcon
    have : agmonRate d / 2 / 2 * (ϱ - 1) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
    have : 0 < 2 * d * Real.log L := by positivity
    linarith
  have hsep : (L : ℝ) ^ d ≤ Real.exp (agmonRate d / 2 * (ϱ - 1)) := by
    rw [← Real.exp_log (by positivity : (0 : ℝ) < (L : ℝ) ^ d), Real.log_pow]
    apply Real.exp_le_exp.2
    have h1 : 0 < ϱ - 1 := by linarith
    have : 0 ≤ agmonRate d / 2 * (ϱ - 1) := by positivity
    nlinarith
  -- the pieces
  let S : G.Ω 1 → PtSetting G := fun y =>
    { a := a, ν := ν, α := α, f := blockPiece G f y
      j' := G.layerIndex (y : Torus d (N₀ * L ^ k)), y' := y
      hd := hd, hL := hL, hν0 := hν0, hν1 := hν1, ha := ha, hα := hα, hϱ := hϱ1.le, hsep := hsep
      hj'1 := (G.layerIndex_spec y.2).1, hj'k := (G.layerIndex_spec y.2).2.1
      hy' := (G.layerIndex_spec y.2).2.2
      hsupp := by
        intro z hz
        by_contra hne
        exact hz (by simp [blockPiece, hne]) }
  have hSu : ∀ y, (S y).u = (dirichletOperator G a ν α)⁻¹ *ᵥ blockPiece G f y := fun y => rfl
  have hfeq : f = ∑ y : G.Ω 1, (siteWeight G y : ℂ) • blockPiece G f y := by
    funext z
    rw [Finset.sum_apply]
    simpa using (sum_siteWeight_blockPiece G f z).symm
  have hu : (dirichletOperator G a ν α)⁻¹ *ᵥ f =
      ∑ y : G.Ω 1, (siteWeight G y : ℂ) • (S y).u := by
    conv_lhs => rw [hfeq]
    rw [Matrix.mulVec_sum]
    simp_rw [Matrix.mulVec_smul]
    exact Finset.sum_congr rfl fun y _ => rfl
  have hut : ∀ p, zeroExt (G.Ω 1) ((dirichletOperator G a ν α)⁻¹ *ᵥ f) p =
      ∑ y : G.Ω 1, (siteWeight G y : ℂ) * (S y).ut p := by
    intro p
    rw [hu]
    simp only [PtSetting.ut, zeroExt]
    split_ifs with h
    · simp [Finset.sum_apply]
    · simp
  -- the piece bounds
  have hpiece : ∀ y : G.Ω 1, (S y).U x ≤ K2 * decay (agmonRate d / 2) (G.pathDist x y) * Cf := by
    intro y
    obtain ⟨hj1, hjk, hyl⟩ := G.layerIndex_spec y.2
    have hsp : G.spacing (y : Torus d (N₀ * L ^ k)) = (L : ℝ) ^ G.layerIndex (y : Torus d (N₀ * L ^ k)) :=
      G.spacing_eq hj1 hjk hyl
    have hLp : (0 : ℝ) < (L : ℝ) ^ G.layerIndex (y : Torus d (N₀ * L ^ k)) := by
      have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
      positivity
    set Mf : ℝ := Cf / ((L : ℝ) ^ G.layerIndex (y : Torus d (N₀ * L ^ k))) ^ 2 with hMf
    have hMf0 : 0 ≤ Mf := by positivity
    have hMfb : ∀ i, ‖(S y).f i‖ ≤ Mf := by
      intro i
      change ‖blockPiece G f y i‖ ≤ Mf
      unfold blockPiece
      split_ifs with h
      · have h1 := hf i
        rw [mem_layer_of_blockPiece G y i h, hsp] at h1
        rw [hMf, le_div_iff₀ (by positivity)]
        linarith
      · simpa using hMf0
    have hF : (L : ℝ) ^ (2 * G.layerIndex (y : Torus d (N₀ * L ^ k))) * Mf = Cf := by
      rw [hMf, pow_mul']
      field_simp
    obtain ⟨h1, h2⟩ := hP G (S y) hMf0 hMfb hx
    by_cases ht : G.pathDist x (y : Torus d (N₀ * L ^ k)) = ⊤
    · have h3 : (S y).U x = 0 := h2 ht
      rw [h3]
      simp [decay, ht]
    · have h3 : (S y).U x ≤ K2 * Real.exp (-(agmonRate d / 2 *
          (G.pathDist x (y : Torus d (N₀ * L ^ k))).toReal)) *
          ((L : ℝ) ^ (2 * G.layerIndex (y : Torus d (N₀ * L ^ k))) * Mf) := h1 ht
      rw [hF] at h3
      simpa [decay, ht] using h3
  have hsum : ∑ y : G.Ω 1, siteWeight G y * (S y).U x ≤ K2 * countConst d L (agmonRate d / 2) * Cf := by
    have hc := sum_siteWeight_decay_le G hϱ1 hγ0 hϱ hx
    calc _ ≤ ∑ y : G.Ω 1, siteWeight G y * (K2 * decay (agmonRate d / 2) (G.pathDist x y) * Cf) :=
          Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (hpiece y) (siteWeight_nonneg G _)
      _ = K2 * Cf * ∑ y : G.Ω 1, siteWeight G y * decay (agmonRate d / 2) (G.pathDist x y) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun y _ => by ring
      _ ≤ K2 * Cf * countConst d L (agmonRate d / 2) :=
          mul_le_mul_of_nonneg_left hc (by positivity)
      _ = _ := by ring
  have hU0 : ∀ y : G.Ω 1, ‖(S y).ut x‖ ≤ (S y).U x := fun y => (S y).norm_ut_le_U x
  refine ⟨?_, fun μ => ?_⟩
  · rw [hut x]
    calc _ ≤ ∑ y : G.Ω 1, ‖(siteWeight G y : ℂ) * (S y).ut x‖ := norm_sum_le _ _
      _ ≤ ∑ y : G.Ω 1, siteWeight G y * (S y).U x := by
          refine Finset.sum_le_sum fun y _ => ?_
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (siteWeight_nonneg G _)]
          exact mul_le_mul_of_nonneg_left (hU0 y) (siteWeight_nonneg G _)
      _ ≤ _ := hsum
  · rw [hut, hut, ← Finset.sum_sub_distrib]
    have hdiff : ∀ y : G.Ω 1, G.spacing x * ‖(S y).ut (x + Pi.single μ 1) - (S y).ut x‖ ≤
        (S y).U x := fun y => PtSetting.spacing_mul_diff_le_U (S y) x μ
    calc _ = G.spacing x * ‖∑ y : G.Ω 1, (siteWeight G y : ℂ) *
          ((S y).ut (x + Pi.single μ 1) - (S y).ut x)‖ := by
          congr 2
          exact Finset.sum_congr rfl fun y _ => by ring
      _ ≤ G.spacing x * ∑ y : G.Ω 1, siteWeight G y * ‖(S y).ut (x + Pi.single μ 1) - (S y).ut x‖ := by
          refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans ?_) (spacing_pos G (x := x)).le
          refine le_of_eq (Finset.sum_congr rfl fun y _ => ?_)
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (siteWeight_nonneg G _)]
      _ = ∑ y : G.Ω 1, siteWeight G y * (G.spacing x * ‖(S y).ut (x + Pi.single μ 1) - (S y).ut x‖) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun y _ => by ring
      _ ≤ ∑ y : G.Ω 1, siteWeight G y * (S y).U x :=
          Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (hdiff y) (siteWeight_nonneg G _)
      _ ≤ _ := hsum

end Balaban.Multiscale
