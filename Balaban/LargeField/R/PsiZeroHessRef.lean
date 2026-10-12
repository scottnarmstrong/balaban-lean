/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.PsiZeroHessInput
public import Balaban.Multiscale.ConstraintField

/-!
# The first variation at the reference vector (PSIZERO-HESS §4, row 7)

`blockAvg_sub_le`: the residual `Ψ(x) - Qφ(x)` of a top-layer site is the average over its `k`-block of the
differences `Ψ(y) - φ(y)`, hence bounded by the supremum of these differences.
`firstVar_re_le`: with the residual of every site over a box `Z` bounded by `ρ`, the first variation of a
perturbation `v ∈ SuppSpace Z` is at most `a_k L^{k(d-2)} √|Z| ρ ‖v‖` (the envelope formula (2.6) and the
Cauchy-Schwarz inequality).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background Finset

section Ref

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ k ϱ} {a : ℕ → ℝ}

/-- The residual at a top-layer site is the block average of the differences. -/
theorem residual_vn_le (hk : 1 ≤ k) (D : BgData G N) (φ : G.Ω 1 × Fin N → ℂ) {x : Torus d (N₀ * L ^ k)}
    (hx : x ∈ G.layer k) {ρ : ℝ}
    (hρ : ∀ y (hy : y ∈ G.blk k x), vn (fun i => φ (⟨y, blk_subset_Ω G hk le_rfl hx hy⟩, i) - D.Ψ y i) ≤ ρ) :
    vn (fun i => D.Ψ x i - blockAvg G φ x i) ≤ ρ := by
  classical
  have hli : G.layerIndex x = k := G.layerIndex_eq hk le_rfl hx
  have hsub := blk_subset_Ω G hk le_rfl hx
  have hcard : ((G.blk k x).card : ℝ) = ((L : ℝ) ^ k) ^ d := by
    rw [card_blk G k le_rfl x]; push_cast; ring
  have hpos : (0 : ℝ) < ((L : ℝ) ^ k) ^ d := by
    have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  set c : ℝ := (((L : ℝ) ^ k) ^ d)⁻¹ with hc
  have hΨ : ∀ y ∈ G.blk k x, D.Ψ y = D.Ψ x := fun y hy => D.Ψ_layerConst k hk le_rfl x hx y hy
  have hvec : (WithLp.toLp 2 (fun i => D.Ψ x i - blockAvg G φ x i) : EuclideanSpace ℂ (Fin N)) =
      (c : ℂ) • ∑ y ∈ (G.blk k x).attach, (WithLp.toLp 2 (fun i =>
        D.Ψ y i - φ (⟨y, hsub y.2⟩, i)) : EuclideanSpace ℂ (Fin N)) := by
    ext i
    simp only [PiLp.smul_apply, WithLp.ofLp_sum, Finset.sum_apply, smul_eq_mul]
    have e1 : ∑ y ∈ (G.blk k x).attach, (D.Ψ (y : Torus d (N₀ * L ^ k)) i -
        φ (⟨y, hsub y.2⟩, i)) = ((G.blk k x).card : ℂ) * D.Ψ x i - ∑ y ∈ G.blk k x, svec G φ y i := by
      rw [Finset.sum_sub_distrib]
      congr 1
      · rw [Finset.sum_attach (G.blk k x) (fun y => D.Ψ y i)]
        rw [Finset.sum_congr rfl fun y hy => by rw [hΨ y hy]]
        simp
      · rw [← Finset.sum_attach (G.blk k x) (fun y => svec G φ y i)]
        exact Finset.sum_congr rfl fun y _ => (svec_of_mem G φ ⟨y, hsub y.2⟩ i).symm
    rw [e1]
    unfold blockAvg
    rw [hli]
    have hcq : ((c : ℝ) : ℂ) * ((((L : ℝ) ^ k) ^ d : ℝ) : ℂ) = 1 := by
      rw [hc, ← Complex.ofReal_mul, inv_mul_cancel₀ hpos.ne', Complex.ofReal_one]
    have hcc : ((G.blk k x).card : ℂ) = (((L : ℝ) ^ k) ^ d : ℝ) := by exact_mod_cast hcard
    rw [hcc]
    have hc' : (((((L : ℝ) ^ k) ^ d)⁻¹ : ℝ) : ℂ) = (c : ℂ) := by rw [hc]
    rw [hc']
    linear_combination (-(D.Ψ x i)) * hcq
  have hnorm := calc vn (fun i => D.Ψ x i - blockAvg G φ x i)
      = ‖(WithLp.toLp 2 (fun i => D.Ψ x i - blockAvg G φ x i) : EuclideanSpace ℂ (Fin N))‖ := rfl
    _ = c * ‖∑ y ∈ (G.blk k x).attach, (WithLp.toLp 2 (fun i =>
          D.Ψ y i - φ (⟨y, hsub y.2⟩, i)) : EuclideanSpace ℂ (Fin N))‖ := by
        rw [hvec, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    _ ≤ c * ∑ y ∈ (G.blk k x).attach, ρ := by
        refine mul_le_mul_of_nonneg_left (le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun y _ => ?_))
          (by positivity)
        have := hρ y y.2
        calc ‖(WithLp.toLp 2 (fun i => D.Ψ y i - φ (⟨y, hsub y.2⟩, i)) : EuclideanSpace ℂ (Fin N))‖
            = vn (fun i => D.Ψ y i - φ (⟨y, hsub y.2⟩, i)) := rfl
          _ = vn (fun i => φ (⟨y, hsub y.2⟩, i) - D.Ψ y i) := by
              unfold vn
              rw [← norm_neg]
              congr 1
              ext i; simp
          _ ≤ ρ := this
    _ = ρ := by
        rw [Finset.sum_const, Finset.card_attach, nsmul_eq_mul, hcard, hc]
        field_simp
  exact hnorm

theorem abs_sum_mul_le_vn (x y : Fin N → ℂ) : ‖∑ i, x i * y i‖ ≤ vn x * vn y := by
  have hv : ∀ z : Fin N → ℂ, vn z = Real.sqrt (∑ i, ‖z i‖ ^ 2) := fun z => by
    unfold vn; rw [EuclideanSpace.norm_eq]
  rw [hv, hv]
  calc ‖∑ i, x i * y i‖ ≤ ∑ i, ‖x i * y i‖ := norm_sum_le _ _
    _ = ∑ i, ‖x i‖ * ‖y i‖ := Finset.sum_congr rfl fun i _ => norm_mul _ _
    _ ≤ _ := by
        have := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun i => ‖x i‖) (fun i => ‖y i‖)
        simpa using this

/-- The sum over the fine sites of a function of their `k`-blocks, supported on the boxes of `Z`
(all of whose sites lie over `Ω_k`), is `L^{kd}` times the sum over `Z`. -/
theorem sum_fiber_top (hk : 1 ≤ k) {Z : Finset (Torus d (N₀ * L ^ (k - k)))}
    (hΩ : OverTop G (Z : Set (Torus d (N₀ * L ^ (k - k))))) (H : Torus d (N₀ * L ^ (k - k)) → ℝ) :
    ∑ x : Torus d (N₀ * L ^ k), (if jBlock d L N₀ k k x ∈ Z then H (jBlock d L N₀ k k x) else 0) =
      ((L : ℝ) ^ k) ^ d * ∑ z ∈ Z, H z := by
  classical
  have hZ : ∀ y ∈ Z, ((Finset.univ.filter fun x : Torus d (N₀ * L ^ k) => jBlock d L N₀ k k x ∈ Z).filter
      fun x => jBlock d L N₀ k k x = y).card = (L ^ k) ^ d := by
    intro y hy
    have h := (topLift_block_count hΩ hk (Finset.mem_coe.2 hy)).1
    rw [← h]
    congr 1
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨h ▸ hy, h⟩
  calc ∑ x : Torus d (N₀ * L ^ k), (if jBlock d L N₀ k k x ∈ Z then H (jBlock d L N₀ k k x) else 0)
      = ∑ x ∈ Finset.univ.filter (fun x : Torus d (N₀ * L ^ k) => jBlock d L N₀ k k x ∈ Z),
          H (jBlock d L N₀ k k x) := by rw [Finset.sum_filter]
    _ = ∑ y ∈ Z, ∑ x ∈ (Finset.univ.filter (fun x : Torus d (N₀ * L ^ k) => jBlock d L N₀ k k x ∈ Z)).filter
          (fun x => jBlock d L N₀ k k x = y), H (jBlock d L N₀ k k x) :=
        (Finset.sum_fiberwise_of_maps_to (fun x hx => (Finset.mem_filter.1 hx).2) _).symm
    _ = ∑ y ∈ Z, ((L : ℝ) ^ k) ^ d * H y := by
        refine Finset.sum_congr rfl fun y hy => ?_
        rw [Finset.sum_congr rfl (fun x hx => by rw [(Finset.mem_filter.1 hx).2]), Finset.sum_const,
          hZ y hy, nsmul_eq_mul]
        push_cast; ring
    _ = _ := by rw [← Finset.mul_sum]

/-- **The envelope bound (row 7).**  If the residual `Ψ - Qφ` of every site over `Z` is at most `ρ`, then the first
variation of `v ∈ SuppSpace Z` satisfies `|b₁(v)| ≤ a_k L^{k(d-2)} √|Z| ρ ‖v‖`. -/
theorem firstVar_re_le (hd : 2 ≤ d) (hk : 1 ≤ k) (ha : IsAdmissibleWeights k a)
    {Z : Finset (Torus d (N₀ * L ^ (k - k)))} (hΩ : OverTop G (Z : Set (Torus d (N₀ * L ^ (k - k)))))
    (v : SuppSpace Z N) (D : BgData G N) (φ : G.Ω 1 × Fin N → ℂ) {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hρ : ∀ x ∈ G.layer k, jBlock d L N₀ k k x ∈ Z → vn (fun i => D.Ψ x i - blockAvg G φ x i) ≤ ρ) :
    |(firstVar a D (topTangent G v) φ).re| ≤
      a k * (L : ℝ) ^ (k * (d - 2)) * ρ * Real.sqrt Z.card * ‖v‖ := by
  classical
  have hak : 0 ≤ a k := by linarith [(ha k hk le_rfl).1]
  have hLk : (0 : ℝ) < (L : ℝ) ^ k := pow_pos (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)) k
  set H : Torus d (N₀ * L ^ (k - k)) → ℝ := fun z => a k / ((L : ℝ) ^ k) ^ 2 * (‖extSupp Z v z‖ * ρ) with hH
  have hH0 : ∀ z, 0 ≤ H z := fun z => by positivity
  set T : Torus d (N₀ * L ^ k) → ℝ := fun x =>
    if jBlock d L N₀ k k x ∈ Z then H (jBlock d L N₀ k k x) else 0 with hT
  have hT0 : ∀ x, 0 ≤ T x := fun x => by
    simp only [hT]; split_ifs
    · exact hH0 _
    · exact le_rfl
  -- termwise bound
  have hterm : ∀ x : G.Ω 1, ‖((a (G.layerIndex (x : Torus d (N₀ * L ^ k))) /
      ((L : ℝ) ^ G.layerIndex (x : Torus d (N₀ * L ^ k))) ^ 2 : ℝ) : ℂ) *
        ∑ i, (topTangent G v).Ψ x i * (D.Ψ x i - blockAvg G φ x i)‖ ≤ T x := by
    intro x
    have hx1 : (x : Torus d (N₀ * L ^ k)) ∈ G.Ω 1 := x.2
    have hds : (x : Torus d (N₀ * L ^ k)) ∈ dataSites G := (mem_dataSites G).2 (Or.inl hx1)
    by_cases hz : jBlock d L N₀ k k (x : Torus d (N₀ * L ^ k)) ∈ Z
    · have hxk : (x : Torus d (N₀ * L ^ k)) ∈ G.Ω k := hΩ _ hz
      have hxl : (x : Torus d (N₀ * L ^ k)) ∈ G.layer k := G.mem_layer.2 ⟨hxk, by rw [G.top]; simp⟩
      have hli : G.layerIndex (x : Torus d (N₀ * L ^ k)) = k := G.layerIndex_eq hk le_rfl hxl
      have hres := hρ x hxl hz
      have hE : vn (fun i => (topTangent G v).Ψ x i) = ‖extSupp Z v (jBlock d L N₀ k k x)‖ := by
        unfold vn
        rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        show ‖(topTangent G v).Ψ (x : Torus d (N₀ * L ^ k)) i‖ ^ 2 = _
        rw [topTangent_Ψ v hds i]
        simp
      simp only [hT, hz, ↓reduceIte, hH, hli]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      calc a k / ((L : ℝ) ^ k) ^ 2 * ‖∑ i, (topTangent G v).Ψ x i * (D.Ψ x i - blockAvg G φ x i)‖
          ≤ a k / ((L : ℝ) ^ k) ^ 2 * (vn (fun i => (topTangent G v).Ψ x i) *
            vn (fun i => D.Ψ x i - blockAvg G φ x i)) :=
            mul_le_mul_of_nonneg_left (abs_sum_mul_le_vn _ _) (by positivity)
        _ ≤ _ := by
            rw [hE]
            exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hres (norm_nonneg _)) (by positivity)
    · have : ∀ i, (topTangent G v).Ψ x i = 0 := fun i => by
        rw [topTangent_Ψ v hds i]; simp [extSupp, hz]
      simp [hT, hz, this]
  have h1 : ‖firstVar a D (topTangent G v) φ‖ ≤ ∑ x : G.Ω 1, T x :=
    le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun x _ => hterm x)
  have h2 : ∑ x : G.Ω 1, T x ≤ ∑ x : Torus d (N₀ * L ^ k), T x := by
    rw [Finset.sum_coe_sort (G.Ω 1) T]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun x _ _ => hT0 x)
  have h3 : ∑ x : Torus d (N₀ * L ^ k), T x = ((L : ℝ) ^ k) ^ d * ∑ z ∈ Z, H z :=
    sum_fiber_top hk hΩ H
  have h4 : ∑ z ∈ Z, ‖extSupp Z v z‖ ≤ Real.sqrt Z.card * ‖v‖ := by
    have hcs := Real.sum_mul_le_sqrt_mul_sqrt Z (fun _ => (1 : ℝ)) (fun z => ‖extSupp Z v z‖)
    have hsq : ∑ z ∈ Z, ‖extSupp Z v z‖ ^ 2 = ‖v‖ ^ 2 := by
      have e2 : ∑ z ∈ Z, ‖extSupp Z v z‖ ^ 2 = ∑ z, ‖extSupp Z v z‖ ^ 2 :=
        Finset.sum_subset (Finset.subset_univ Z) (fun x _ hx => by simp [extSupp, hx])
      rw [e2, sum_sq_extSupp]
    simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hcs
    rw [hsq, Real.sqrt_sq (norm_nonneg v)] at hcs
    exact hcs
  have hsum : ∑ z ∈ Z, H z = a k / ((L : ℝ) ^ k) ^ 2 * ρ * ∑ z ∈ Z, ‖extSupp Z v z‖ := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun z _ => by simp only [hH]; ring
  have hd2 : ((L : ℝ) ^ k) ^ d = (L : ℝ) ^ (k * (d - 2)) * ((L : ℝ) ^ k) ^ 2 := by
    rw [pow_mul, ← pow_add]
    congr 1; omega
  calc |(firstVar a D (topTangent G v) φ).re| ≤ ‖firstVar a D (topTangent G v) φ‖ := Complex.abs_re_le_norm _
    _ ≤ ((L : ℝ) ^ k) ^ d * ∑ z ∈ Z, H z := by rw [← h3]; exact h1.trans h2
    _ = a k * (L : ℝ) ^ (k * (d - 2)) * ρ * ∑ z ∈ Z, ‖extSupp Z v z‖ := by
        rw [hsum, hd2]; field_simp
    _ ≤ a k * (L : ℝ) ^ (k * (d - 2)) * ρ * (Real.sqrt Z.card * ‖v‖) :=
        mul_le_mul_of_nonneg_left h4 (by positivity)
    _ = _ := by ring

end Ref

section GradFinal

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ k ϱ} {a : ℕ → ℝ}
  [NeZero N]

/-- `C_T = 12 d (D + 2) + 4`: the tube radius of the reference configuration is `C_T δ`. -/
noncomputable def tubeConst (d D : ℕ) : ℝ := 12 * d * (D + 2) + 4

theorem tubeRad_zero (d D : ℕ) (δ : ℝ) : tubeRad d D δ 0 = tubeConst d D * δ := by
  unfold tubeRad tubeConst; ring

theorem tubeConst_pos (d D : ℕ) : 0 < tubeConst d D := by unfold tubeConst; positivity

/-- The radius for the gradient estimate. -/
noncomputable def etaGrad (d L N D : ℕ) [NeZero L] : ℝ :=
  min (min (bgC0 d L N) (bgC1 d L N)) (etaHess d L N D) / tubeConst d D

/-- The gradient constant `Gr_k = 2 K₁ C_T D^{d/2} L^{k(d-2)}`. -/
noncomputable def gradConst (d L N k D : ℕ) [NeZero L] : ℝ :=
  2 * bgK1 d L N * tubeConst d D * Real.sqrt ((D : ℝ) ^ d) * (L : ℝ) ^ (k * (d - 2))

theorem etaGrad_pos (d L N D : ℕ) [NeZero L] (hd : 0 < d) : 0 < etaGrad d L N D := by
  unfold etaGrad
  have := tubeConst_pos d D
  have := etaHess_pos d L N D hd
  have := bgC0_pos d L N hd
  have := Balaban.Localization.bgC1_pos' (d := d) (L := L) (N := N) hd
  positivity

theorem gradConst_nonneg (d L N k D : ℕ) [NeZero L] : 0 ≤ gradConst d L N k D := by
  have := bgK1_pos (d := d) (L := L) (N := N)
  have := tubeConst_pos d D
  unfold gradConst; positivity

/-- **Row 7, tube at the reference vector** (`tube_merge` at displacement `ν = 0`, (4.1)): the block field
`ψ_{k,0}` equal to the reference vector on `Z₀` and to `ψ_k` off it lies in the tube of radius `C_T δ`. -/
theorem psiZero_ref_tube {D : ℕ} (hd : 2 ≤ d) (hk : 1 ≤ k) (b0 : Torus d (N₀ * L ^ (k - k)))
    (w : Fin d → ℕ) (hw1 : ∀ i, 1 ≤ w i) (hwD : ∀ i, w i ≤ D) (hm : D + 2 ≤ N₀ * L ^ (k - k))
    {X : Set (Torus d (N₀ * L ^ (k - k)))} (hXreg : box b0 w ∪ shellOut (box b0 w) ⊆ X)
    (hΩ : OverTop G (box b0 w ∪ shellOut (box b0 w)))
    (hdata : ∀ x ∈ dataSites G, jBlock d L N₀ k k x ∈ X) {δ : ℝ} (hδ : 0 < δ)
    {ψk : BlockField d L N₀ k N} (hψk : TubeOn G (X \ box b0 w) δ ψk) :
    TubeOn G Set.univ (tubeConst d D * δ)
      (mergeField (boxFinset b0 w) ψk (centrePt ψk b0 w)) := by
  have := tube_merge G hd hk b0 w hw1 hwD hm hXreg hΩ hdata hδ hψk (centrePt ψk b0 w) (le_refl (0 : ℝ))
    (by simp)
  rwa [tubeRad_zero] at this

end GradFinal


end Balaban.LargeField
