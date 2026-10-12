/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.DecoupledCube
public import Balaban.Multiscale.ConstraintSup

/-!
# The decoupled Green's operator: (DG1) and the pointwise bounds (DG2), (DG3)

* `commK_local_bound`: the commutator bound (K) in local form -- the bound at one point `x`
  uses the values of `s` on the block of `x` and the gradient bounds at `x` only (the proof of
  `commK_sup_bound` verbatim);
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Finset Matrix

theorem commK_local_bound {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}
    (G : GeneratingSet d L N₀ k ϱ) (hd : 0 < d) (hL : 1 ≤ L) {a : ℕ → ℝ}
    (ha : IsAdmissibleWeights k a)
    (ν : ℝ) (α : G.Ω 1 → ℂ) {δ : ℝ} {φ : Torus d (N₀ * L ^ k) → Fin N → ℂ}
    (hφ : IsSmoothField G δ φ) (hδ : 0 ≤ δ) (s : G.Ω 1 × Fin N → ℂ) {V : ℝ} (hV0 : 0 ≤ V)
    (x : G.Ω 1)
    (hV : ∀ y ∈ G.blk (G.layerIndex (x : Torus d (N₀ * L ^ k))) x, ∀ i, ‖svec G s y i‖ ≤ V)
    (hf : ∀ (μ : Fin d) (i : Fin N),
      G.spacing x * ‖svec G s ((x : Torus d (N₀ * L ^ k)) + Pi.single μ 1) i - svec G s x i‖ ≤ V)
    (hb : ∀ (μ : Fin d) (i : Fin N),
      G.spacing x * ‖svec G s ((x : Torus d (N₀ * L ^ k)) - Pi.single μ 1) i - svec G s x i‖ ≤ L * V) :
    G.spacing x ^ 2 * ‖(commK (dirichletOperator G a ν α) (restrictField G φ) *ᵥ s) x‖ ≤
      commKConst d L N * δ * V := by
  obtain ⟨hj1, hjk, hxl⟩ := G.layerIndex_spec x.2
  set j := G.layerIndex (x : Torus d (N₀ * L ^ k)) with hjdef
  have hsp : G.spacing x = (L : ℝ) ^ j := G.spacing_eq hj1 hjk hxl
  have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hLj : (0 : ℝ) < (L : ℝ) ^ j := by positivity
  have h := commK_pointwise G ha ν α hφ hδ (isAgmonWeight_zero G) (le_refl (0 : ℝ)) s hj1 hjk x hxl
  simp only [zero_mul, Real.exp_zero, one_mul, mul_one] at h
  rw [hsp] at h ⊢
  set p : Torus d (N₀ * L ^ k) := (x : Torus d (N₀ * L ^ k)) with hp
  set ℓ : ℝ := (L : ℝ) ^ j with hℓ
  have hNV : 0 ≤ (N : ℝ) * V := by positivity
  -- vector norms
  have hvx : vn (svec G s p) ≤ N * V := vn_le_card_mul hV0 (hV p (G.mem_blk.2 rfl))
  have hvf : ∀ μ : Fin d, ℓ * vn (svec G s (p + Pi.single μ 1) - svec G s p) ≤ N * V := by
    intro μ
    have hm : 0 ≤ V / ℓ := by positivity
    have := vn_le_card_mul (v := svec G s (p + Pi.single μ 1) - svec G s p) hm (fun i => by
      rw [le_div_iff₀ hLj, mul_comm]
      have := hf μ i
      rw [hsp] at this
      simpa using this)
    calc ℓ * vn _ ≤ ℓ * (N * (V / ℓ)) := mul_le_mul_of_nonneg_left this hLj.le
      _ = N * V := by field_simp
  have hvb : ∀ μ : Fin d, ℓ * vn (svec G s (p - Pi.single μ 1) - svec G s p) ≤ N * (L * V) := by
    intro μ
    have hm : 0 ≤ L * V / ℓ := by positivity
    have := vn_le_card_mul (v := svec G s (p - Pi.single μ 1) - svec G s p) hm (fun i => by
      rw [le_div_iff₀ hLj, mul_comm]
      have := hb μ i
      rw [hsp] at this
      simpa using this)
    calc ℓ * vn _ ≤ ℓ * (N * (L * V / ℓ)) := mul_le_mul_of_nonneg_left this hLj.le
      _ = N * (L * V) := by field_simp
  -- the block average
  have hblk : (((L : ℝ) ^ j) ^ d)⁻¹ * ∑ y ∈ G.blk j p, vn (svec G s y) ≤ N * V := by
    have hc := card_blk_cast G j hjk x
    have hsum : ∑ y ∈ G.blk j p, vn (svec G s y) ≤ (G.blk j p).card * (N * V) := by
      rw [← nsmul_eq_mul, ← Finset.sum_const]
      exact Finset.sum_le_sum fun y hy => vn_le_card_mul hV0 (hV y hy)
    rw [hc] at hsum
    have hp : (0 : ℝ) < ((L : ℝ) ^ j) ^ d := by positivity
    rw [inv_mul_le_iff₀ hp]
    linarith
  have hsumμ : (∑ μ : Fin d, (vn (svec G s (p + Pi.single μ 1) - svec G s p) +
      vn (svec G s (p - Pi.single μ 1) - svec G s p))) * ℓ ≤ d * (N * V + N * (L * V)) := by
    rw [Finset.sum_mul]
    calc _ ≤ ∑ _μ : Fin d, (N * V + N * (L * V)) := by
          refine Finset.sum_le_sum fun μ _ => ?_
          have := hvf μ
          have := hvb μ
          nlinarith
      _ = _ := by simp; ring
  -- assemble
  have hlead : ℓ * ‖(commK (dirichletOperator G a ν α) (restrictField G φ) *ᵥ s) x‖ ≤ _ := h
  have hb2 : 0 ≤ ∑ μ : Fin d, (vn (svec G s (p + Pi.single μ 1) - svec G s p) +
      vn (svec G s (p - Pi.single μ 1) - svec G s p)) :=
    Finset.sum_nonneg fun μ _ => add_nonneg (vn_nonneg _) (vn_nonneg _)
  have hmul := mul_le_mul_of_nonneg_left hlead hLj.le
  calc ℓ ^ 2 * ‖(commK (dirichletOperator G a ν α) (restrictField G φ) *ᵥ s) x‖
      = ℓ * (ℓ * ‖(commK (dirichletOperator G a ν α) (restrictField G φ) *ᵥ s) x‖) := by ring
    _ ≤ _ := hmul
    _ ≤ commKConst d L N * δ * V := by
        unfold commKConst
        have e : ∀ A B C : ℝ, ℓ * (δ * A + δ * ℓ⁻¹ * B + 4 * d * δ * ℓ⁻¹ * C) =
            δ * (A * ℓ) + δ * B + 4 * d * δ * C := by
          intro A B C; field_simp
        rw [e]
        have h1 := mul_le_mul_of_nonneg_left hsumμ hδ
        have h2 := mul_le_mul_of_nonneg_left hvx hδ
        have h3 := mul_le_mul_of_nonneg_left hblk (by positivity : (0 : ℝ) ≤ 4 * d * δ)
        have h4 : 0 ≤ (d : ℝ) * (L - 1) * N * V * δ := by
          have : (0 : ℝ) ≤ L - 1 := by linarith
          positivity
        nlinarith
variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ} {α : G.Ω 1 → ℂ}

theorem Kz_apply (α : G.Ω 1 → ℂ) (q : ℕ × CTorus d L N₁ m₁ K) (x y : G.Ω 1) :
    Kz G a ν q x y = dirichletOperator G a ν α x y *
      (((chi G q x : ℝ) : ℂ) - ((chi G q y : ℝ) : ℂ)) := by
  rw [Kz_eq a ν α q]
  unfold chiD
  rw [Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal]
  ring

theorem Kz_mulVec_eq_commK (α : G.Ω 1 → ℂ) (q : ℕ × CTorus d L N₁ m₁ K) (u : G.Ω 1 → ℂ)
    (x : G.Ω 1) :
    (Kz G a ν q *ᵥ u) x =
      (commK (dirichletOperator G a ν α) (restrictField G (chiField G q)) *ᵥ
        (fun p : G.Ω 1 × Fin 1 => u p.1)) x := by
  rw [commK_mulVec]
  simp only [Matrix.mulVec, dotProduct, Kz_apply α q, Finset.univ_unique, Finset.sum_singleton]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp [restrictField, chiField]

/-- **Support of the commutator.** If `K_z u (x) ≠ 0` then `x` is an interior point of `□_z`. -/
theorem inner_of_Kz_ne_zero (S : DGSetting G a ν) {q : ℕ × CTorus d L N₁ m₁ K}
    (hq : q ∈ cubeIdx G) (u : G.Ω 1 → ℂ) (x : G.Ω 1) (h : (Kz G a ν q *ᵥ u) x ≠ 0) :
    Inner q x := by
  by_contra hI
  obtain ⟨hn1, hnK, hxl⟩ := G.layerIndex_spec x.2
  set n := G.layerIndex (x : CTorus d L N₁ m₁ K) with hn
  have hz : ∀ z : CTorus d L N₁ m₁ K,
      ((∃ μ : Fin d, z = (x : CTorus d L N₁ m₁ K) + Pi.single μ 1 ∨
        z = (x : CTorus d L N₁ m₁ K) - Pi.single μ 1) ∨ SameCell (L ^ n) (x : CTorus d L N₁ m₁ K) z) →
      chi G q z = 0 := by
    intro z hnear
    by_contra hne
    exact hI (inner_of_near S.cover_sep S.hM (by have := S.hL; omega) hq hn1 hnK hxl
      (inBox_of_chi_ne_zero hne) hnear)
  have hx0 : chi G q (x : CTorus d L N₁ m₁ K) = 0 := hz _ (Or.inr (SameCell.refl _ _))
  have e : ∀ z : CTorus d L N₁ m₁ K, chi G q z = 0 → chiField G q z = fun _ => 0 := by
    intro z hz0; funext i; unfold chiField; rw [hz0]; simp
  apply h
  rw [Kz_mulVec_eq_commK (α := 0) q u x]
  refine commK_apply_eq_zero ν 0 _ x (fun μ => ?_) (fun y hy => ?_)
  · have h1 := hz _ (Or.inl ⟨μ, Or.inl rfl⟩)
    have h2 := hz _ (Or.inl ⟨μ, Or.inr rfl⟩)
    rw [e _ h1, e _ h2, e _ hx0]; exact ⟨rfl, rfl⟩
  · have hy' := G.mem_blk.1 hy
    have h1 := hz y (Or.inr (sameCell_of_jBlock_eq hnK hy'.symm))
    rw [e _ h1, e _ hx0]

theorem svec_scalar (u : G.Ω 1 → ℂ) (y : CTorus d L N₁ m₁ K) (i : Fin 1) :
    svec G (fun p : G.Ω 1 × Fin 1 => u p.1) y i = zeroExt (G.Ω 1) u y := rfl

theorem pathDist_adj_le_one {x y : CTorus d L N₁ m₁ K} (hx : x ∈ G.Ω 1) (hy : y ∈ G.Ω 1)
    (hadj : Adj x y) : G.pathDist x y ≤ ENNReal.ofReal 1 :=
  (G.pathDist_le_bondCost hx hy hadj).trans (ENNReal.ofReal_le_ofReal (G.bondCost_le_one hx y))

/-- **The cut commutator on a cube solution, weighted.** For `f` with `w ℓ² |f| ≤ C`,
`w ℓ² |K_z G^{(z)} c_z f| ≤ B_K C / M₁`. -/
theorem Kz_cube_weighted (hd : 3 ≤ d) (hL : 3 ≤ L) :
    ∃ Bk : ℝ, 0 ≤ Bk ∧ ∀ {N₁ m₁ K : ℕ} [NeZero N₁] {ϱ : ℝ}
      (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) {a : ℕ → ℝ} {ν : ℝ}, DGSetting G a ν →
      ∀ {α : G.Ω 1 → ℂ}, AdmPot G α → ∀ {q : ℕ × CTorus d L N₁ m₁ K}, q ∈ cubeIdx G →
      ∀ {w : CTorus d L N₁ m₁ K → ℝ}, IsWeight G (gammaW d) w →
      ∀ (f : G.Ω 1 → ℂ) {C : ℝ}, 0 ≤ C →
      (∀ x : G.Ω 1, w x * (G.spacing (x : CTorus d L N₁ m₁ K)) ^ 2 * ‖f x‖ ≤ C) →
      ∀ x : G.Ω 1, w x * ((G.spacing (x : CTorus d L N₁ m₁ K)) ^ 2 *
        ‖((Kz G a ν q * cubeG G a ν α q) *ᵥ f) x‖) ≤ Bk * C / (L : ℝ) ^ m₁ := by
  obtain ⟨Bw, hBw, hW⟩ := cube_weighted (d := d) (L := L) hd hL
  refine ⟨commKConst d L 1 * Cchi d L * Bw * Real.exp (2 * gammaW d * d), ?_, ?_⟩
  · have := Cchi_nonneg d L
    have : 0 ≤ commKConst d L 1 := by unfold commKConst; positivity
    positivity
  intro N₁ m₁ K _ ϱ G a ν S α hα q hq w hw f C hC hfC x
  have hd0 : 0 < d := by omega
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have hM0 : (0 : ℝ) < (L : ℝ) ^ m₁ := by positivity
  have hρ := S.one_lt_rho
  have hγ0 := gammaW_nonneg hd0
  have hBk0 : 0 ≤ commKConst d L 1 * Cchi d L * Bw * Real.exp (2 * gammaW d * d) := by
    have := Cchi_nonneg d L
    have : 0 ≤ commKConst d L 1 := by unfold commKConst; positivity
    positivity
  -- the source restricted to the cube
  set g : G.Ω 1 → ℂ := cD G q *ᵥ f with hgdef
  have hgsupp : ∀ z : G.Ω 1, g z ≠ 0 → (z : CTorus d L N₁ m₁ K) ∈ box q := by
    intro z hz
    by_contra hnb
    exact hz (by rw [hgdef, cD_mulVec]; simp [hnb])
  have hgC : ∀ z : G.Ω 1, w z * (G.spacing (z : CTorus d L N₁ m₁ K)) ^ 2 * ‖g z‖ ≤ C := by
    intro z
    rw [hgdef, cD_mulVec]
    split_ifs
    · exact hfC z
    · simpa using hC
  have hu : cubeG G a ν α q *ᵥ f = (cubeH G a ν α q)⁻¹ *ᵥ g := cubeG_mulVec q f
  have hrw : ((Kz G a ν q * cubeG G a ν α q) *ᵥ f) = Kz G a ν q *ᵥ ((cubeH G a ν α q)⁻¹ *ᵥ g) := by
    rw [← Matrix.mulVec_mulVec, hu]
  rw [hrw]
  set u : G.Ω 1 → ℂ := (cubeH G a ν α q)⁻¹ *ᵥ g with hudef
  by_cases hK0 : (Kz G a ν q *ᵥ u) x = 0
  · rw [hK0]; simp only [norm_zero, mul_zero]
    positivity
  have hI := inner_of_Kz_ne_zero S hq u x hK0
  obtain ⟨hW1, hW2, -⟩ := hW G S hα hq hw g hgsupp hC hgC
  have hwx := hw.pos x
  obtain ⟨hn1, hnK, hxl⟩ := G.layerIndex_spec x.2
  set n := G.layerIndex (x : CTorus d L N₁ m₁ K) with hn
  -- the solution is zero outside the cube
  have hcg : cD G q *ᵥ g = g := by
    funext z; rw [cD_mulVec]; by_cases hz : (z : CTorus d L N₁ m₁ K) ∈ box q
    · simp [hz]
    · have : g z = 0 := by_contra fun h => hz (hgsupp z h)
      simp [this]
  have hzero : ∀ y : CTorus d L N₁ m₁ K, y ∉ box q → zeroExt (G.Ω 1) u y = 0 := by
    intro y hy
    by_cases hyΩ : y ∈ G.Ω 1
    · have e : zeroExt (G.Ω 1) u y = u ⟨y, hyΩ⟩ := by simp [zeroExt, hyΩ]
      rw [e]
      have := cubeG_supp S hα hq g ⟨y, hyΩ⟩ hy
      have hc : cubeG G a ν α q *ᵥ g = (cubeH G a ν α q)⁻¹ *ᵥ (cD G q *ᵥ g) := cubeG_mulVec q g
      rw [hcg] at hc
      rw [hudef, ← hc]; exact this
    · exact zeroExt_not_mem _ _ hyΩ
  have hBC := mul_nonneg hBw hC
  -- value bound at points at path distance at most `ρ` from `x`
  have hval : ∀ (y : CTorus d L N₁ m₁ K), y ∈ G.Ω 1 → ∀ {ρ : ℝ}, 0 ≤ ρ →
      G.pathDist x y ≤ ENNReal.ofReal ρ →
      ‖zeroExt (G.Ω 1) u y‖ ≤ Bw * C * Real.exp (gammaW d * ρ) / w x := by
    intro y hyΩ ρ hρ0 hdist
    have hwxy := hw.le_mul hγ0 hρ0 hdist
    rw [le_div_iff₀ hwx]
    by_cases hyb : y ∈ box q
    · have h1 := hW1 hyΩ hyb
      have e : zeroExt (G.Ω 1) u y = solExt G (cubeH G a ν α q)⁻¹ g y := rfl
      rw [e]
      calc ‖solExt G (cubeH G a ν α q)⁻¹ g y‖ * w x
          ≤ ‖solExt G (cubeH G a ν α q)⁻¹ g y‖ * (w y * Real.exp (gammaW d * ρ)) :=
            mul_le_mul_of_nonneg_left hwxy (norm_nonneg _)
        _ = (w y * ‖solExt G (cubeH G a ν α q)⁻¹ g y‖) * Real.exp (gammaW d * ρ) := by ring
        _ ≤ Bw * C * Real.exp (gammaW d * ρ) :=
            mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    · rw [hzero y hyb, norm_zero, zero_mul]
      exact mul_nonneg hBC (Real.exp_pos _).le
  have hVx : ∀ {ρ : ℝ}, 0 ≤ ρ → ρ ≤ 2 * d → Bw * C * Real.exp (gammaW d * ρ) / w x ≤
      Bw * C * Real.exp (2 * gammaW d * d) / w x := by
    intro ρ hρ0 hρ2
    apply div_le_div_of_nonneg_right _ hwx.le
    apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 _) hBC
    nlinarith
  set V : ℝ := Bw * C * Real.exp (2 * gammaW d * d) / w x with hV
  have hV0 : 0 ≤ V := by positivity
  have hLV : V ≤ L * V := le_mul_of_one_le_left hV0 hL1
  have hVw : V * w x = Bw * C * Real.exp (2 * gammaW d * d) := by
    rw [hV]; field_simp
  -- the hypotheses of the local commutator bound
  have hsmooth := chiField_isSmooth S.aligned S.cover_sep (by omega : 1 ≤ d) (by omega : 2 ≤ L) hq
  have hδ : 0 ≤ Cchi d L / (L : ℝ) ^ m₁ := div_nonneg (Cchi_nonneg d L) hM0.le
  have hxΩ : (x : CTorus d L N₁ m₁ K) ∈ G.Ω 1 := x.2
  have hxV : ‖zeroExt (G.Ω 1) u x‖ ≤ V := by
    refine (hval x hxΩ (le_refl 0) (by simp [G.pathDist_self hxΩ])).trans ?_
    simpa using hVx (le_refl 0) (by positivity)
  have hfwd : ∀ μ : Fin d, G.spacing (x : CTorus d L N₁ m₁ K) *
      ‖zeroExt (G.Ω 1) u ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) -
        zeroExt (G.Ω 1) u x‖ ≤ V := by
    intro μ
    have h := hW2 hxΩ hI.self hI.add_single μ
    have e : ∀ y, zeroExt (G.Ω 1) u y = solExt G (cubeH G a ν α q)⁻¹ g y := fun y => rfl
    simp only [e]
    rw [← mul_le_mul_iff_of_pos_right hwx, hVw]
    nlinarith [mul_nonneg hBC (sub_nonneg.2 (Real.one_le_exp (by positivity : 0 ≤ 2 * gammaW d * d)))]
  have hbwd : ∀ μ : Fin d, G.spacing (x : CTorus d L N₁ m₁ K) *
      ‖zeroExt (G.Ω 1) u ((x : CTorus d L N₁ m₁ K) - Pi.single μ 1) -
        zeroExt (G.Ω 1) u x‖ ≤ L * V := by
    intro μ
    by_cases hyΩ : ((x : CTorus d L N₁ m₁ K) - Pi.single μ 1) ∈ G.Ω 1
    · set y : CTorus d L N₁ m₁ K := (x : CTorus d L N₁ m₁ K) - Pi.single μ 1 with hy
      have hadj : Adj y (x : CTorus d L N₁ m₁ K) := ⟨μ, Or.inl (by rw [hy]; simp)⟩
      have hyb : y ∈ box q := hI.sub_single μ
      have hye : ∀ ν' : Fin d, y + Pi.single ν' 1 ∈ box q := fun ν' => hI.sub_add_single μ ν'
      have h := hW2 hyΩ hyb hye μ
      have hyx : y + Pi.single μ 1 = (x : CTorus d L N₁ m₁ K) := by rw [hy]; simp
      rw [hyx] at h
      have e : ∀ z, zeroExt (G.Ω 1) u z = solExt G (cubeH G a ν α q)⁻¹ g z := fun z => rfl
      have hsp := spacing_adj_le G hρ.le hyΩ hxΩ hadj
      have hd1 := (G.pathDist_comm (x : CTorus d L N₁ m₁ K) y) ▸
        (G.pathDist_le_bondCost hyΩ hxΩ hadj |>.trans
          (ENNReal.ofReal_le_ofReal (G.bondCost_le_one hyΩ _)))
      have hwxy := hw.le_mul hγ0 zero_le_one hd1
      have hwy := hw.pos y
      simp only [e] at h ⊢
      set Dn := ‖solExt G (cubeH G a ν α q)⁻¹ g y - solExt G (cubeH G a ν α q)⁻¹ g x‖ with hDn
      have hnn := norm_nonneg
        (solExt G (cubeH G a ν α q)⁻¹ g y - solExt G (cubeH G a ν α q)⁻¹ g x)
      rw [norm_sub_rev] at h
      rw [← mul_le_mul_iff_of_pos_right hwx]
      have hsp0 := (spacing_pos G (x := y)).le
      have hE : Real.exp (gammaW d * 1) ≤ Real.exp (2 * gammaW d * d) :=
        Real.exp_le_exp.2 (by
          have : (1 : ℝ) ≤ d := by exact_mod_cast hd0
          nlinarith)
      calc G.spacing (x : CTorus d L N₁ m₁ K) * Dn * w x
          ≤ (L * G.spacing y) * Dn * (w y * Real.exp (gammaW d * 1)) := by
            gcongr
        _ = L * Real.exp (gammaW d * 1) * (w y * (G.spacing y * Dn)) := by ring
        _ ≤ L * Real.exp (gammaW d * 1) * (Bw * C) := by
            gcongr
        _ ≤ L * Real.exp (2 * gammaW d * d) * (Bw * C) := by gcongr
        _ = L * V * w x := by rw [mul_assoc (L : ℝ) V, hVw]; ring
    · have hz : zeroExt (G.Ω 1) u ((x : CTorus d L N₁ m₁ K) - Pi.single μ 1) = 0 :=
        zeroExt_not_mem _ _ hyΩ
      rw [hz, zero_sub, norm_neg]
      have hadj : Adj (x : CTorus d L N₁ m₁ K) ((x : CTorus d L N₁ m₁ K) - Pi.single μ 1) :=
        ⟨μ, Or.inr (by simp)⟩
      have hsp := spacing_le_of_adj_not_mem G hρ (by omega : 1 ≤ L) hxΩ hyΩ hadj
      calc _ ≤ (L : ℝ) * ‖zeroExt (G.Ω 1) u x‖ :=
            mul_le_mul_of_nonneg_right hsp (norm_nonneg _)
        _ ≤ L * V := mul_le_mul_of_nonneg_left hxV (by positivity)
  have hloc := commK_local_bound G hd0 (by omega : 1 ≤ L) S.weights ν (0 : G.Ω 1 → ℂ) hsmooth hδ
    (fun p : G.Ω 1 × Fin 1 => u p.1) hV0 x
    (fun y hy i => by
      rw [svec_scalar]
      have hy' := G.mem_blk.1 hy
      have hyl : y ∈ G.layer n := (G.mem_layer_iff hn1 hnK hy').2 hxl
      have hyΩ : y ∈ G.Ω 1 := G.layer_subset hn1 hnK hyl
      have hd2 := G.pathDist_block_le hn1 hnK hxl hy'
      exact (hval y hyΩ (by positivity) hd2).trans (hVx (by positivity) le_rfl))
    (fun μ i => by simp only [svec_scalar]; exact hfwd μ)
    (fun μ i => by simp only [svec_scalar]; exact hbwd μ)
  rw [Kz_mulVec_eq_commK (α := 0) q u x]
  calc w x * (G.spacing (x : CTorus d L N₁ m₁ K) ^ 2 * ‖(commK (dirichletOperator G a ν 0)
        (restrictField G (chiField G q)) *ᵥ fun p : G.Ω 1 × Fin 1 => u p.1) x‖)
      ≤ w x * (commKConst d L 1 * (Cchi d L / (L : ℝ) ^ m₁) * V) :=
        mul_le_mul_of_nonneg_left hloc hwx.le
    _ = commKConst d L 1 * Cchi d L * Bw * Real.exp (2 * gammaW d * d) * C / (L : ℝ) ^ m₁ := by
        rw [hV]; field_simp

/-- **(DG1)** `‖𝒦_s(A)‖ ≤ 1/4` in the weighted norm `|·|_{2,w}`, for `M₁ ≥ c_* e^{N₀ κ₁}`. -/
theorem dg1 (hd : 3 ≤ d) (hL : 3 ≤ L) :
    ∃ cstar : ℝ, 0 ≤ cstar ∧ ∀ {N₁ m₁ K : ℕ} [NeZero N₁] {ϱ : ℝ}
      (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) {a : ℕ → ℝ} {ν : ℝ}, DGSetting G a ν →
      ∀ {α : G.Ω 1 → ℂ}, AdmPot G α → ∀ {κ : ℝ}, 0 ≤ κ →
      cstar * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁ →
      ∀ {s : ℕ × CTorus d L N₁ m₁ K → ℂ}, (∀ P, ‖s P‖ ≤ Real.exp κ) →
      ∀ {w : CTorus d L N₁ m₁ K → ℝ}, IsWeight G (gammaW d) w →
      ∀ (f : G.Ω 1 → ℂ) {C : ℝ}, 0 ≤ C →
      (∀ x : G.Ω 1, w x * (G.spacing (x : CTorus d L N₁ m₁ K)) ^ 2 * ‖f x‖ ≤ C) →
      ∀ x : G.Ω 1, w x * (G.spacing (x : CTorus d L N₁ m₁ K)) ^ 2 *
        ‖(Kcal G a ν α s *ᵥ f) x‖ ≤ C / 4 := by
  obtain ⟨Bk, hBk, hK⟩ := Kz_cube_weighted (d := d) (L := L) hd hL
  refine ⟨12 * 5 ^ d * Bk, by positivity, ?_⟩
  intro N₁ m₁ K _ ϱ G a ν S α hα κ hκ hMκ s hs w hw f C hC hfC x
  classical
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have hM0 : (0 : ℝ) < (L : ℝ) ^ m₁ := by positivity
  have hwx := hw.pos x
  have hsp := (spacing_pos G (x := (x : CTorus d L N₁ m₁ K))).le
  have hexp : 0 < Real.exp (N0 d L * κ) := Real.exp_pos _
  -- the sum over centres
  set T : (ℕ × CTorus d L N₁ m₁ K) → ℂ := fun q =>
    sProd G s q * (((Kz G a ν q * cubeG G a ν α q) *ᵥ f) x) with hT
  have hsum : (Kcal G a ν α s *ᵥ f) x = ∑ q ∈ cubeIdx G, T q := by
    unfold Kcal
    rw [Matrix.sum_mulVec, Finset.sum_apply]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul]
  have hfilter : ∑ q ∈ (cubeIdx G).filter (fun q => (x : CTorus d L N₁ m₁ K) ∈ box q), T q =
      ∑ q ∈ cubeIdx G, T q := by
    refine Finset.sum_filter_of_ne fun q hq hne => ?_
    have h1 : (((Kz G a ν q * cubeG G a ν α q) *ᵥ f) x) ≠ 0 := right_ne_zero_of_mul hne
    rw [← Matrix.mulVec_mulVec] at h1
    exact (inner_of_Kz_ne_zero S hq _ x h1).self
  obtain ⟨hn1, hnK, hxl⟩ := G.layerIndex_spec x.2
  have hcard := card_inBox_le (G := G) S.cover_sep (by omega : 1 ≤ L) hn1 hnK hxl
    (s := 5 / 2) (by norm_num) 5 (by norm_num)
  have hterm : ∀ q ∈ (cubeIdx G).filter (fun q => (x : CTorus d L N₁ m₁ K) ∈ box q),
      w x * (G.spacing (x : CTorus d L N₁ m₁ K)) ^ 2 * ‖T q‖ ≤
        Real.exp (N0 d L * κ) * (Bk * C / (L : ℝ) ^ m₁) := by
    intro q hq
    have hqi := (Finset.mem_filter.1 hq).1
    have h1 := hK G S hα hqi hw f hC hfC x
    have h2 := norm_sProd_le S.aligned S.cover_sep S.hM (by omega : 1 ≤ L) hqi hκ hs
    calc w x * (G.spacing (x : CTorus d L N₁ m₁ K)) ^ 2 * ‖T q‖
        = ‖sProd G s q‖ * (w x * ((G.spacing (x : CTorus d L N₁ m₁ K)) ^ 2 *
            ‖((Kz G a ν q * cubeG G a ν α q) *ᵥ f) x‖)) := by
          rw [hT]; simp only [norm_mul]; ring
      _ ≤ Real.exp (N0 d L * κ) * (Bk * C / (L : ℝ) ^ m₁) :=
          mul_le_mul h2 h1 (by positivity) hexp.le
  rw [hsum, ← hfilter]
  calc w x * (G.spacing (x : CTorus d L N₁ m₁ K)) ^ 2 *
        ‖∑ q ∈ (cubeIdx G).filter (fun q => (x : CTorus d L N₁ m₁ K) ∈ box q), T q‖
      ≤ w x * (G.spacing (x : CTorus d L N₁ m₁ K)) ^ 2 *
        ∑ q ∈ (cubeIdx G).filter (fun q => (x : CTorus d L N₁ m₁ K) ∈ box q), ‖T q‖ :=
        mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ = ∑ q ∈ (cubeIdx G).filter (fun q => (x : CTorus d L N₁ m₁ K) ∈ box q),
          w x * (G.spacing (x : CTorus d L N₁ m₁ K)) ^ 2 * ‖T q‖ := by rw [Finset.mul_sum]
    _ ≤ ∑ q ∈ (cubeIdx G).filter (fun q => (x : CTorus d L N₁ m₁ K) ∈ box q),
          Real.exp (N0 d L * κ) * (Bk * C / (L : ℝ) ^ m₁) := Finset.sum_le_sum hterm
    _ = ((cubeIdx G).filter (fun q => (x : CTorus d L N₁ m₁ K) ∈ box q)).card *
          (Real.exp (N0 d L * κ) * (Bk * C / (L : ℝ) ^ m₁)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (3 * 5 ^ d) * (Real.exp (N0 d L * κ) * (Bk * C / (L : ℝ) ^ m₁)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        have hf : (cubeIdx G).filter (fun q => (x : CTorus d L N₁ m₁ K) ∈ box q) =
            (cubeIdx G).filter (fun q => InBox m₁ q.1 q.2 (5 / 2 * (L : ℝ) ^ (q.1 + m₁))
              (x : CTorus d L N₁ m₁ K)) :=
          Finset.filter_congr fun q _ => mem_box
        rw [hf]
        exact_mod_cast hcard
    _ ≤ C / 4 := by
        have h4 : 12 * 5 ^ d * Bk * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁ := hMκ
        rw [show (3 * 5 ^ d : ℝ) * (Real.exp (N0 d L * κ) * (Bk * C / (L : ℝ) ^ m₁)) =
          (3 * 5 ^ d * Bk * Real.exp (N0 d L * κ)) * C / (L : ℝ) ^ m₁ by ring]
        rw [div_le_iff₀ hM0]
        nlinarith [mul_le_mul_of_nonneg_right h4 hC]

end Balaban.Localization
