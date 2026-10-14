/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.DecoupledCovUnit
public import Balaban.Localization.DecoupledCovariance
public import Balaban.Localization.DecoupledXClose

/-!
# I-4c (vi): closeness of the constrained covariance away from the parameters

LOCALIZATION.md §3.4, Theorem I-4c (vi). The weighted closeness (DG6) of `Ĝ_{k,x,s}` to
`H_{k,x}⁻¹` (`XData.dg6`, values only) is completed by the gradient (`XData.dg6_grad`: the same
decomposition `(G*_s - G*_1) g + G_D (𝒦_s - 𝒦_1) g`, the first term supported in `W`, the second by
the Agmon energy estimate) and used, through the commutator `K_x(φ₀)`, for the constrained
operator:

* `gradOn_add_le`, `gradOn_sub_le`, `gradOn_supp_le`, `Gd_grad_le`, `XData.gradOn_Gstarx_bound`:
  weighted gradient calculus;
* `XData.dg6_grad`: `‖w ∂(Ĝ_s - H⁻¹) f‖² ≤ B e^{2 N₀ κ} ‖ℓ f‖²`;
* `deltaOp`, `vecM_deltaOp`, `vecGrad_deltaOp`: the same for `N`-vector fields;
* `decZ_sub_eq`: `Z_s - Z_1 = Δ (1 - Ψ_s) + G_1 F M_s⁻¹ K Δ (1 - Ψ_1)` with `Z = Ĝ - Π`,
  `Ψ = F M⁻¹ N`, `Δ = Ĝ_s - Ĝ_1` (using `M_s - M_1 = -K Δ F`, `N_s - N_1 = -K Δ`);
* `vecM_decZ_sub_le`: `‖ℓ⁻¹ e^{ε r} (Z_s - Z_1) f‖² ≤ B e^{2 N₀ κ} ‖ℓ f‖²`, `r` the truncated path
  distance to a set `W` containing every cube with `s_z ≠ 1`.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Finset Matrix

section GradClose

variable {d L N₁ m₁ k : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} {a : ℕ → ℝ} {aT x ν : ℝ}
  {α : G.Ω 1 → ℂ} {κ : ℝ} {s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ}

theorem norm_add_sq_le' (p q : ℂ) : ‖p + q‖ ^ 2 ≤ 2 * ‖p‖ ^ 2 + 2 * ‖q‖ ^ 2 := by
  have h := norm_add_le p q
  nlinarith [sq_nonneg (‖p‖ - ‖q‖), norm_nonneg p, norm_nonneg q, norm_nonneg (p + q)]

theorem gradOn_add_le (ε : ℝ) (r : CTorus d L N₁ m₁ (k + 1) → ℝ)
    (Λ : Finset (CTorus d L N₁ m₁ (k + 1))) (u v : G.Ω 1 → ℂ) :
    gradOn G ε r Λ (u + v) ≤ 2 * gradOn G ε r Λ u + 2 * gradOn G ε r Λ v := by
  unfold gradOn
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun y _ => ?_
  split_ifs
  · rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun μ _ => ?_
    have h1 : ∀ z : CTorus d L N₁ m₁ (k + 1), zeroExt (G.Ω 1) (u + v) z =
        zeroExt (G.Ω 1) u z + zeroExt (G.Ω 1) v z := zeroExt_add' _ u v
    rw [h1, h1, h1]
    have e1 : zeroExt (G.Ω 1) u (y + Pi.single μ 1) + zeroExt (G.Ω 1) v (y + Pi.single μ 1) -
        (zeroExt (G.Ω 1) u y + zeroExt (G.Ω 1) v y) =
        (zeroExt (G.Ω 1) u (y + Pi.single μ 1) - zeroExt (G.Ω 1) u y) +
        (zeroExt (G.Ω 1) v (y + Pi.single μ 1) - zeroExt (G.Ω 1) v y) := by ring
    have e2 : zeroExt (G.Ω 1) u (y - Pi.single μ 1) + zeroExt (G.Ω 1) v (y - Pi.single μ 1) -
        (zeroExt (G.Ω 1) u y + zeroExt (G.Ω 1) v y) =
        (zeroExt (G.Ω 1) u (y - Pi.single μ 1) - zeroExt (G.Ω 1) u y) +
        (zeroExt (G.Ω 1) v (y - Pi.single μ 1) - zeroExt (G.Ω 1) v y) := by ring
    rw [e1, e2]
    have h3 := norm_add_sq_le' (zeroExt (G.Ω 1) u (y + Pi.single μ 1) - zeroExt (G.Ω 1) u y)
      (zeroExt (G.Ω 1) v (y + Pi.single μ 1) - zeroExt (G.Ω 1) v y)
    have h4 := norm_add_sq_le' (zeroExt (G.Ω 1) u (y - Pi.single μ 1) - zeroExt (G.Ω 1) u y)
      (zeroExt (G.Ω 1) v (y - Pi.single μ 1) - zeroExt (G.Ω 1) v y)
    have hw := (Real.exp_pos (ε * r y)).le
    have hw2 : 0 ≤ Real.exp (ε * r y) ^ 2 := sq_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left (add_le_add h3 h4) hw2]
  · simp

theorem gradOn_sub_le (ε : ℝ) (r : CTorus d L N₁ m₁ (k + 1) → ℝ)
    (Λ : Finset (CTorus d L N₁ m₁ (k + 1))) (u v : G.Ω 1 → ℂ) :
    gradOn G ε r Λ (u - v) ≤ 2 * gradOn G ε r Λ u + 2 * gradOn G ε r Λ v := by
  have h : u - v = u + (-1 : ℂ) • v := by simp [sub_eq_add_neg]
  have h2 : gradOn G ε r Λ ((-1 : ℂ) • v) = gradOn G ε r Λ v := by
    unfold gradOn
    refine Finset.sum_congr rfl fun y _ => ?_
    split_ifs
    · congr 1
      refine Finset.sum_congr rfl fun μ _ => ?_
      have hz : ∀ z : CTorus d L N₁ m₁ (k + 1), zeroExt (G.Ω 1) ((-1 : ℂ) • v) z =
          -zeroExt (G.Ω 1) v z := by
        intro z
        by_cases hz : z ∈ G.Ω 1 <;> simp [zeroExt, hz]
      rw [hz, hz, hz]
      simp only [neg_sub_neg, norm_sub_rev]
    · rfl
  rw [h]
  have := gradOn_add_le ε r Λ u ((-1 : ℂ) • v)
  rw [h2] at this
  exact this

theorem truncSetDistR_le_one_of_adj (W : Finset (CTorus d L N₁ m₁ (k + 1))) (T : ℝ)
    {x y : CTorus d L N₁ m₁ (k + 1)} (hx : x ∈ G.Ω 1) (hy : y ∈ G.Ω 1) (hyW : y ∈ W)
    (hadj : Adj x y) : truncSetDistR G W T x ≤ 1 := by
  have h1 := setDist_adj_le W hx hy hyW hadj
  unfold truncSetDistR
  have h2 : min (siteSetDist G W x) (ENNReal.ofReal T) ≤ ENNReal.ofReal 1 :=
    (min_le_left _ _).trans h1
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h2
  simpa using this

theorem zeroExt_ne_zero_mem {ι : Type*} [DecidableEq ι] {Λ : Finset ι} (u : Λ → ℂ) {z : ι}
    (h : zeroExt Λ u z ≠ 0) : ∃ hz : z ∈ Λ, u ⟨z, hz⟩ ≠ 0 := by
  by_cases hz : z ∈ Λ
  · exact ⟨hz, by rwa [zeroExt_mem' u hz] at h⟩
  · exact absurd (zeroExt_not_mem _ _ hz) h

theorem gradOn_supp_le (W : Finset (CTorus d L N₁ m₁ (k + 1))) (T : ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (u : G.Ω 1 → ℂ) (hu : ∀ z : G.Ω 1, u z ≠ 0 → (z : CTorus d L N₁ m₁ (k + 1)) ∈ W) :
    gradOn G ε (truncSetDistR G W T) Finset.univ u ≤
      Real.exp (2 * ε) * gradOn G 0 (fun _ => 0) Finset.univ u := by
  classical
  unfold gradOn
  simp only [Finset.mem_univ, ↓reduceIte, mul_zero, Real.exp_zero, one_pow, one_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun y hy => ?_
  set S : ℝ := ∑ μ : Fin d, (‖zeroExt (G.Ω 1) u (y + Pi.single μ 1) - zeroExt (G.Ω 1) u y‖ ^ 2 +
    ‖zeroExt (G.Ω 1) u (y - Pi.single μ 1) - zeroExt (G.Ω 1) u y‖ ^ 2) with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun μ _ => by positivity
  have hrle : truncSetDistR G W T y ≤ 1 ∨ S = 0 := by
    by_cases hy0 : zeroExt (G.Ω 1) u y ≠ 0
    · obtain ⟨hyΩ, hyu⟩ := zeroExt_ne_zero_mem u hy0
      left
      rw [truncSetDistR_of_mem G T (hu _ hyu) hy]
      exact zero_le_one
    · push Not at hy0
      by_cases hn : ∃ μ : Fin d, zeroExt (G.Ω 1) u (y + Pi.single μ 1) ≠ 0 ∨
          zeroExt (G.Ω 1) u (y - Pi.single μ 1) ≠ 0
      · left
        obtain ⟨μ, h | h⟩ := hn
        · obtain ⟨hz, hzu⟩ := zeroExt_ne_zero_mem u h
          exact truncSetDistR_le_one_of_adj W T hy hz (hu _ hzu) ⟨μ, Or.inl rfl⟩
        · obtain ⟨hz, hzu⟩ := zeroExt_ne_zero_mem u h
          refine truncSetDistR_le_one_of_adj W T hy hz (hu _ hzu) ⟨μ, Or.inr ?_⟩
          simp
      · right
        push Not at hn
        rw [hS]
        refine Finset.sum_eq_zero fun μ _ => ?_
        rw [(hn μ).1, (hn μ).2, hy0]
        simp
  rcases hrle with h | h
  · have : Real.exp (ε * truncSetDistR G W T y) ^ 2 ≤ Real.exp (2 * ε) := by
      rw [← Real.exp_nat_mul]
      refine Real.exp_le_exp.2 ?_
      push_cast
      nlinarith
    exact mul_le_mul_of_nonneg_right this hS0
  · rw [h]; simp

/-- The gradient bound for `G*_{x,s}`, in terms of the source `g` itself. -/
noncomputable def gradStarConstX (d : ℕ) : ℝ := 2 * (3 * 5 ^ d) * ((136 + 1024 * d) * (3 * 5 ^ d))

/-- The closeness constant of the gradient. -/
noncomputable def gradCloseConstX (d : ℕ) : ℝ :=
  (24 * gradStarConstX d + 32 + 512 * d) * (16 / 9)

theorem gradStarConstX_nonneg (d : ℕ) : 0 ≤ gradStarConstX d := by
  unfold gradStarConstX; positivity

/-! ### The gradient closeness for the data `Dec2.XData` of a pair `(C, G)`

The statements `XData.gradOn_Gstarx_bound`, `Gd_grad_le`, `XData.dg6_grad` below are their instances
at `C = coverOf G` (`XData.toCover`, `Dec2.xCover_self`). -/

namespace Dec2

section GradCover

variable {C : DecCover d L N₁ m₁ (k + 1)} {Cx : ℝ}

/-- The gradient bound for `G*_{x,s}` of a pair `(C, G)`, in terms of the source `g` itself. -/
theorem XData.gradOn_Gstarx_bound (D : XData C G a aT ν x α κ s Cx) {ε : ℝ}
    {r : CTorus d L N₁ m₁ (k + 1) → ℝ} (W : XWeight G ε r) (g : G.Ω 1 → ℂ) :
    gradOn G ε r Finset.univ (Gstarx C G a aT x ν α s *ᵥ g) ≤
      gradStarConstX d * Real.exp (N0 d L * κ) ^ 2 * agmonSource G ε r g := by
  have h1 := gradOn_Gstarx_le (ε := ε) (r := r) D g
  have h3 := sum_agmonSource_cD_le D.st ε r g
  have h4 : ∑ q ∈ C.cubeIdx, gradP C G q ε r (cubeGx G a aT x ν α q *ᵥ g) ≤
      (136 + 1024 * d) * ((3 * 5 ^ d : ℝ) * agmonSource G ε r g) := by
    calc _ ≤ ∑ q ∈ C.cubeIdx, (136 + 1024 * d) * agmonSource G ε r (cD G q *ᵥ g) :=
          Finset.sum_le_sum fun q hq => D.gradP_cube_le W hq g
      _ = (136 + 1024 * d) * ∑ q ∈ C.cubeIdx, agmonSource G ε r (cD G q *ᵥ g) := by
          rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left h3 (by positivity)
  have hE0 : 0 ≤ Real.exp (N0 d L * κ) ^ 2 := sq_nonneg _
  calc _ ≤ _ := h1
    _ ≤ (2 * (3 * 5 ^ d) : ℝ) * (Real.exp (N0 d L * κ) ^ 2 *
        ((136 + 1024 * d) * ((3 * 5 ^ d : ℝ) * agmonSource G ε r g))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h4 hE0) (by positivity)
    _ = _ := by unfold gradStarConstX; ring

/-- The weighted gradient of `H_{k,x}⁻¹ h` for the standing data `XCover` of a pair `(C, G)`. -/
theorem Gd_grad_le (S : XCover C G a aT ν Cx) (hα : AdmPot G α) (hx : 0 ≤ x)
    {r : CTorus d L N₁ m₁ (k + 1) → ℝ} (hr : IsAgmonWeight G r) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ xAgmonRate d L) (h : G.Ω 1 → ℂ) :
    gradOn G ε r Finset.univ ((xDirichletOperator G a aT x ν α)⁻¹ *ᵥ h) ≤
      (64 + 1024 * d) * agmonSource G ε r h := by
  have hd : 0 < d := by have := S.hd; omega
  have hdet := (Matrix.isUnit_iff_isUnit_det _).1 (xDirichlet_isUnit S hα hx)
  have hu : cutXOperator G a aT x ν ∅ α *ᵥ ((xDirichletOperator G a aT x ν α)⁻¹ *ᵥ h) = h := by
    rw [cutXOperator_empty, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet,
      Matrix.one_mulVec]
  have hen := x_agmon_energy_cut_of_ak G (cutAligned_empty G) hd S.hL
    S.mass S.ha ⟨S.hak1, S.hak2⟩ S.haT1 S.haT2 hx α (AdmPot.le_eighth' S.hd hα) hr hε0 hε1 hu
  have hε12 : ε ≤ 1 / 2 := by
    have := xAgmonRate_le_agmonRate (d := d) (L := L) hd (by have := S.hL; omega)
    linarith [agmonRate_le hd]
  have hgr := gradOn_le G (cut := ∅) (Λ := Finset.univ) (fun y _ μ => by simp) hr hε0 hε12
    ((xDirichletOperator G a aT x ν α)⁻¹ *ᵥ h)
  have hE := cutEnergy_nonneg (∅ : Finset (CTorus d L N₁ m₁ (k + 1) × Fin d))
    (agmonField G ε r ((xDirichletOperator G a aT x ν α)⁻¹ *ᵥ h))
  have hC : 0 ≤ cwsq G (agmonField G ε r ((xDirichletOperator G a aT x ν α)⁻¹ *ᵥ h)) := by
    unfold cwsq
    exact Finset.sum_nonneg fun z _ => mul_nonneg (invSqSpacing_nonneg G z) (sq_nonneg _)
  have hε2 : ε ^ 2 ≤ 1 / 4 := by nlinarith
  have hd1 : (0 : ℝ) ≤ d := by positivity
  have hS0 := agmonSource_nonneg G ε r h
  set E := cutEnergy (∅ : Finset (CTorus d L N₁ m₁ (k + 1) × Fin d))
    (agmonField G ε r ((xDirichletOperator G a aT x ν α)⁻¹ *ᵥ h))
  set C := cwsq G (agmonField G ε r ((xDirichletOperator G a aT x ν α)⁻¹ *ᵥ h))
  have hEb : E ≤ 16 * agmonSource G ε r h := by linarith
  have hCb : C ≤ 256 * agmonSource G ε r h := by linarith
  have h16 : 16 * ε ^ 2 * (d * C) ≤ 1024 * d * agmonSource G ε r h := by
    calc 16 * ε ^ 2 * (d * C) ≤ 16 * (1 / 4) * (d * C) := by
          gcongr
      _ = 4 * (d * C) := by ring
      _ ≤ 4 * (d * (256 * agmonSource G ε r h)) := by gcongr
      _ = 1024 * d * agmonSource G ε r h := by ring
  nlinarith

/-- **(DG6), closeness of the gradient, for a pair `(C, G)`.** The weighted gradient of
`G_{k,x,s} f - H_{k,x}⁻¹ f`, with the weight `e^{ε r}`, `r` the truncated path distance to `W`,
is bounded by the unweighted source: the companion of `XData.dg6` needed for the commutator
`K_x(φ₀)`. -/
theorem XData.dg6_grad (D : XData C G a aT ν x α κ s Cx) {W : Finset (CTorus d L N₁ m₁ (k + 1))}
    (hW : ∀ z ∈ C.cubeIdx, C.sProd s z ≠ 1 → intBox z ⊆ W) (T : ℝ) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ xAgmonRate d L) (f : G.Ω 1 → ℂ) :
    gradOn G ε (truncSetDistR G W T) Finset.univ
        (Gsx C G a aT x ν α s *ᵥ f - (xDirichletOperator G a aT x ν α)⁻¹ *ᵥ f) ≤
      gradCloseConstX d * Real.exp (N0 d L * κ) ^ 2 * agmonSource G 0 (fun _ => 0) f := by
  have hd : 0 < d := by have := D.st.hd; omega
  have hr := isAgmonWeight_truncSetDistR G W T
  have H0 : XWeight G 0 (fun _ => 0) :=
    ⟨isAgmonWeight_zero G, le_rfl, (xAgmonRate_pos hd D.st.hL).le⟩
  have hE1 : 1 ≤ Real.exp (N0 d L * κ) := Real.one_le_exp (by have := D.κ0; positivity)
  have D1 : XData C G a aT ν x α 0 (fun _ => 1) Cx :=
    ⟨D.st, D.Cx_nn, D.pot, D.x0, le_rfl, by
      simp only [mul_zero, Real.exp_zero, mul_one]
      have := cstarX_pos d L D.Cx_nn
      nlinarith [D.big], fun P => by simp⟩
  set g := (1 - Kcalx C G a aT x ν α s)⁻¹ *ᵥ f with hg
  set A := (Gstarx C G a aT x ν α s - Gstarx C G a aT x ν α (fun _ => 1)) *ᵥ g with hA
  set h := (Kcalx C G a aT x ν α s - Kcalx C G a aT x ν α (fun _ => 1)) *ᵥ g with hh
  rw [Gsx_sub_Gd D.st D.pot D.x0 D.isUnit_one_sub f]
  have hsplit := gradOn_add_le (G := G) ε (truncSetDistR G W T) Finset.univ A
    ((xDirichletOperator G a aT x ν α)⁻¹ *ᵥ h)
  have hg0 := D.neumann_src H0 f
  have hgnn := agmonSource_nonneg G 0 (fun _ => 0) g
  have hS0 := agmonSource_nonneg G 0 (fun _ => 0) f
  have hE2 : 1 ≤ Real.exp (N0 d L * κ) ^ 2 := one_le_pow₀ hE1
  -- the term `A`
  have hAsupp : ∀ z : G.Ω 1, A z ≠ 0 → (z : CTorus d L N₁ m₁ (k + 1)) ∈ W := by
    intro z hz
    by_contra hn
    apply hz
    have := Gstarx_diff_zero D.st D.pot D.x0 hW g hn
    rw [zeroExt_mem' _ z.2] at this
    rw [hA]
    simpa [Matrix.sub_mulVec, zeroExt_mem' _ z.2] using this
  have hε12 : ε ≤ 1 / 2 := by
    have := xAgmonRate_le_agmonRate (d := d) (L := L) hd (by have := D.st.hL; omega)
    linarith [agmonRate_le hd]
  have hexp : Real.exp (2 * ε) ≤ 3 := by
    calc Real.exp (2 * ε) ≤ Real.exp 1 := Real.exp_le_exp.2 (by linarith)
      _ ≤ 3 := by have := Real.exp_one_lt_d9; linarith
  have hA1 : gradOn G ε (truncSetDistR G W T) Finset.univ A ≤
      3 * (2 * (gradStarConstX d * Real.exp (N0 d L * κ) ^ 2 * agmonSource G 0 (fun _ => 0) g) +
        2 * (gradStarConstX d * Real.exp (N0 d L * 0) ^ 2 * agmonSource G 0 (fun _ => 0) g)) := by
    have h1 := gradOn_supp_le W T hε0 A hAsupp
    have h2 : gradOn G 0 (fun _ => 0) Finset.univ A ≤
        2 * gradOn G 0 (fun _ => 0) Finset.univ (Gstarx C G a aT x ν α s *ᵥ g) +
        2 * gradOn G 0 (fun _ => 0) Finset.univ (Gstarx C G a aT x ν α (fun _ => 1) *ᵥ g) := by
      rw [hA, Matrix.sub_mulVec]; exact gradOn_sub_le _ _ _ _ _
    have h3 := D.gradOn_Gstarx_bound H0 g
    have h4 := D1.gradOn_Gstarx_bound H0 g
    have hg0' : 0 ≤ gradOn G 0 (fun _ => 0) Finset.univ A := gradOn_nonneg _ _ _ _ _
    calc _ ≤ Real.exp (2 * ε) * gradOn G 0 (fun _ => 0) Finset.univ A := h1
      _ ≤ 3 * gradOn G 0 (fun _ => 0) Finset.univ A :=
          mul_le_mul_of_nonneg_right hexp hg0'
      _ ≤ _ := by gcongr; linarith
  -- the term `G_D h`
  have hh_supp : ∀ z : G.Ω 1, h z ≠ 0 → (z : CTorus d L N₁ m₁ (k + 1)) ∈ W := by
    intro z hz
    by_contra hn
    exact hz (Kcalx_diff_zero D.st hW g hn)
  have hSrc : agmonSource G ε (truncSetDistR G W T) h = agmonSource G 0 (fun _ => 0) h := by
    simp only [agmonSource_eq]
    refine Finset.sum_congr rfl fun z _ => ?_
    by_cases hz : h z = 0
    · rw [hz]; simp
    · rw [truncSetDistR_of_mem G T (hh_supp z hz) z.2]; simp
  have hhK : agmonSource G 0 (fun _ => 0) h ≤ (1 / 4) * agmonSource G 0 (fun _ => 0) g := by
    rw [hh, Matrix.sub_mulVec]
    have := agmonSource_sub_le G 0 (fun _ => 0) (Kcalx C G a aT x ν α s *ᵥ g)
      (Kcalx C G a aT x ν α (fun _ => 1) *ᵥ g)
    have h1 := D.dg1 H0 g
    have h2 := D1.dg1 H0 g
    linarith
  have hBd := Gd_grad_le D.st D.pot D.x0 hr hε0 hε1 h
  rw [hSrc] at hBd
  simp only [mul_zero, Real.exp_zero, one_pow, mul_one] at hA1
  have hgs := gradStarConstX_nonneg d
  have hdd : (0 : ℝ) ≤ d := by positivity
  set E := Real.exp (N0 d L * κ) ^ 2 with hEdef
  set X := agmonSource G 0 (fun _ => 0) g with hX
  have hgsEX : 0 ≤ gradStarConstX d * E * X := by positivity
  have hgsX : gradStarConstX d * X ≤ gradStarConstX d * E * X := by
    have : gradStarConstX d * X * 1 ≤ gradStarConstX d * X * E := by
      apply mul_le_mul_of_nonneg_left hE2 (by positivity)
    nlinarith
  have key : gradOn G ε (truncSetDistR G W T) Finset.univ A +
      gradOn G ε (truncSetDistR G W T) Finset.univ ((xDirichletOperator G a aT x ν α)⁻¹ *ᵥ h) ≤
      12 * (gradStarConstX d * E * X) + (64 + 1024 * d) / 4 * X := by
    nlinarith [mul_le_mul_of_nonneg_left hhK (by positivity : (0 : ℝ) ≤ 64 + 1024 * d)]
  have hg0' : X ≤ 16 / 9 * agmonSource G 0 (fun _ => 0) f := hg0
  calc _ ≤ 2 * gradOn G ε (truncSetDistR G W T) Finset.univ A + 2 *
        gradOn G ε (truncSetDistR G W T) Finset.univ ((xDirichletOperator G a aT x ν α)⁻¹ *ᵥ h) :=
        hsplit
    _ ≤ 2 * (12 * (gradStarConstX d * E * X) + (64 + 1024 * d) / 4 * X) := by linarith
    _ ≤ (24 * gradStarConstX d + 32 + 512 * d) * E * X := by
        have h1 : (32 + 512 * (d : ℝ)) * X ≤ (32 + 512 * (d : ℝ)) * X * E := by
          have := mul_le_mul_of_nonneg_left hE2 (by positivity : (0 : ℝ) ≤ (32 + 512 * (d : ℝ)) * X)
          linarith
        nlinarith
    _ ≤ (24 * gradStarConstX d + 32 + 512 * d) * E * (16 / 9 * agmonSource G 0 (fun _ => 0) f) := by
        apply mul_le_mul_of_nonneg_left hg0'
        positivity
    _ = _ := by unfold gradCloseConstX; ring

end GradCover

end Dec2

theorem XData.gradOn_Gstarx_bound (D : XData G a aT ν x α κ s) {ε : ℝ}
    {r : CTorus d L N₁ m₁ (k + 1) → ℝ} (W : XWeight G ε r) (g : G.Ω 1 → ℂ) :
    gradOn G ε r Finset.univ (Gstarx G a aT x ν α s *ᵥ g) ≤
      gradStarConstX d * Real.exp (N0 d L * κ) ^ 2 * agmonSource G ε r g :=
  D.toCover.gradOn_Gstarx_bound W g

theorem Gd_grad_le (S : XSetting G a aT ν) (hα : AdmPot G α) (hx : 0 ≤ x)
    {r : CTorus d L N₁ m₁ (k + 1) → ℝ} (hr : IsAgmonWeight G r) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ xAgmonRate d L) (h : G.Ω 1 → ℂ) :
    gradOn G ε r Finset.univ ((xDirichletOperator G a aT x ν α)⁻¹ *ᵥ h) ≤
      (64 + 1024 * d) * agmonSource G ε r h :=
  Dec2.Gd_grad_le (Dec2.xCover_self S) hα hx hr hε0 hε1 h

/-- **(DG6), closeness of the gradient.** The weighted gradient of `G_{k,x,s} f - H_{k,x}⁻¹ f`,
with the weight `e^{ε r}`, `r` the truncated path distance to `W`, is bounded by the unweighted
source: the companion of `XData.dg6` needed for the commutator `K_x(φ₀)`. -/
theorem XData.dg6_grad (D : XData G a aT ν x α κ s) {W : Finset (CTorus d L N₁ m₁ (k + 1))}
    (hW : ∀ z ∈ cubeIdx G, sProd G s z ≠ 1 → intBox z ⊆ W) (T : ℝ) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ xAgmonRate d L) (f : G.Ω 1 → ℂ) :
    gradOn G ε (truncSetDistR G W T) Finset.univ
        (Gsx G a aT x ν α s *ᵥ f - (xDirichletOperator G a aT x ν α)⁻¹ *ᵥ f) ≤
      gradCloseConstX d * Real.exp (N0 d L * κ) ^ 2 * agmonSource G 0 (fun _ => 0) f :=
  D.toCover.dg6_grad hW T hε0 hε1 f

end GradClose

section DeltaVec

variable {d L N₁ m₁ k : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {N : ℕ} {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} {a : ℕ → ℝ} {aT x ν : ℝ}
  {α : G.Ω 1 → ℂ} {κ : ℝ} {s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ}

/-- The difference `Δ = Ĝ_{k,x,s} - H_{k,x}⁻¹` acting on `N`-vector fields. -/
noncomputable def deltaOp (G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ) (a : ℕ → ℝ)
    (aT x ν : ℝ) (α : G.Ω 1 → ℂ) (s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ) :
    Matrix (G.Ω 1 × Fin N) (G.Ω 1 × Fin N) ℂ :=
  liftOp N (Gsx G a aT x ν α s) - liftOp N (xDirichletOperator G a aT x ν α)⁻¹

theorem comp_deltaOp (g : G.Ω 1 × Fin N → ℂ) (i : Fin N) :
    comp G (deltaOp G a aT x ν α s *ᵥ g) i =
      Gsx G a aT x ν α s *ᵥ comp G g i - (xDirichletOperator G a aT x ν α)⁻¹ *ᵥ comp G g i := by
  unfold deltaOp
  rw [Matrix.sub_mulVec]
  have : comp G (liftOp N (Gsx G a aT x ν α s) *ᵥ g - liftOp N (xDirichletOperator G a aT x ν α)⁻¹ *ᵥ g) i =
      comp G (liftOp N (Gsx G a aT x ν α s) *ᵥ g) i -
        comp G (liftOp N (xDirichletOperator G a aT x ν α)⁻¹ *ᵥ g) i := rfl
  rw [this, comp_liftOp', comp_liftOp']

/-- `vecM_deltaOp` for the data `Dec2.XData` of the pair `(coverOf G, G)`. -/
theorem vecM_deltaOp_cover {Cx : ℝ} (D : Dec2.XData (coverOf G) G a aT ν x α κ s Cx)
    {W : Finset (CTorus d L N₁ m₁ (k + 1))}
    (hW : ∀ z ∈ cubeIdx G, sProd G s z ≠ 1 → intBox z ⊆ W) (T : ℝ) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ xAgmonRate d L) (g : G.Ω 1 × Fin N → ℂ) :
    vecM G ε (truncSetDistR G W T) (deltaOp G a aT x ν α s *ᵥ g) ≤
      closeConstX d * Real.exp (N0 d L * κ) ^ 2 * vecSrc G 0 (fun _ => 0) g := by
  rw [vecM_eq, vecSrc, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [comp_deltaOp]
  exact D.dg6 hW T hε0 hε1 _

/-- `vecGrad_deltaOp` for the data `Dec2.XData` of the pair `(coverOf G, G)`. -/
theorem vecGrad_deltaOp_cover {Cx : ℝ} (D : Dec2.XData (coverOf G) G a aT ν x α κ s Cx)
    {W : Finset (CTorus d L N₁ m₁ (k + 1))}
    (hW : ∀ z ∈ cubeIdx G, sProd G s z ≠ 1 → intBox z ⊆ W) (T : ℝ) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ xAgmonRate d L) (g : G.Ω 1 × Fin N → ℂ) :
    vecGradOn G ε (truncSetDistR G W T) Finset.univ (deltaOp G a aT x ν α s *ᵥ g) ≤
      gradCloseConstX d * Real.exp (N0 d L * κ) ^ 2 * vecSrc G 0 (fun _ => 0) g := by
  rw [vecGradOn_eq, vecSrc, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [comp_deltaOp]
  exact D.dg6_grad hW T hε0 hε1 _

theorem vecM_deltaOp (D : XData G a aT ν x α κ s) {W : Finset (CTorus d L N₁ m₁ (k + 1))}
    (hW : ∀ z ∈ cubeIdx G, sProd G s z ≠ 1 → intBox z ⊆ W) (T : ℝ) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ xAgmonRate d L) (g : G.Ω 1 × Fin N → ℂ) :
    vecM G ε (truncSetDistR G W T) (deltaOp G a aT x ν α s *ᵥ g) ≤
      closeConstX d * Real.exp (N0 d L * κ) ^ 2 * vecSrc G 0 (fun _ => 0) g :=
  vecM_deltaOp_cover D.toCover hW T hε0 hε1 g

theorem vecGrad_deltaOp (D : XData G a aT ν x α κ s) {W : Finset (CTorus d L N₁ m₁ (k + 1))}
    (hW : ∀ z ∈ cubeIdx G, sProd G s z ≠ 1 → intBox z ⊆ W) (T : ℝ) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ xAgmonRate d L) (g : G.Ω 1 × Fin N → ℂ) :
    vecGradOn G ε (truncSetDistR G W T) Finset.univ (deltaOp G a aT x ν α s *ᵥ g) ≤
      gradCloseConstX d * Real.exp (N0 d L * κ) ^ 2 * vecSrc G 0 (fun _ => 0) g :=
  vecGrad_deltaOp_cover D.toCover hW T hε0 hε1 g

end DeltaVec

section ZClose

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} {a : ℕ → ℝ} {aT x ν : ℝ}
  {α : G.Ω 1 → ℂ} {κ δ : ℝ} {s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ}
  {φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ}

theorem abstract_identity {V S : Type*} [Fintype V] [Fintype S] [DecidableEq V] [DecidableEq S]
    (Gs G1 : Matrix V V ℂ) (F : Matrix V S ℂ) (K : Matrix S V ℂ) (M1 Ms Yi Zi : Matrix S S ℂ)
    (N1 Ns : Matrix S V ℂ) (hMs : Ms = M1 - K * (Gs - G1) * F) (hNs : Ns = N1 - K * (Gs - G1))
    (hY : Yi * Ms = 1) (hZ : M1 * Zi = 1) :
    (Gs - Gs * F * Yi * Ns) - (G1 - G1 * F * Zi * N1) =
      (Gs - G1) * (1 - F * Yi * Ns) +
        G1 * F * Yi * K * (Gs - G1) * (1 - F * Zi * N1) := by
  have hkey : Zi - Yi + Yi * (K * (Gs - G1) * F) * Zi = 0 := by
    have h1 : Yi * Ms * Zi = Zi := by rw [hY, Matrix.one_mul]
    rw [hMs] at h1
    have h2 : Yi * (M1 - K * (Gs - G1) * F) * Zi = Yi - Yi * (K * (Gs - G1) * F) * Zi := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc Yi M1 Zi, hZ, Matrix.mul_one]
    rw [h2] at h1
    rw [show Zi - Yi + Yi * (K * (Gs - G1) * F) * Zi =
      Zi - (Yi - Yi * (K * (Gs - G1) * F) * Zi) by abel, h1, sub_self]
  have e : ((Gs - Gs * F * Yi * Ns) - (G1 - G1 * F * Zi * N1)) -
      ((Gs - G1) * (1 - F * Yi * Ns) +
        G1 * F * Yi * K * (Gs - G1) * (1 - F * Zi * N1)) =
      G1 * F * ((Zi - Yi + Yi * (K * (Gs - G1) * F) * Zi) * N1) := by
    rw [hNs]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
      Matrix.mul_assoc]
    abel
  rw [hkey, Matrix.zero_mul, Matrix.mul_zero] at e
  exact sub_eq_zero.1 e

variable (G a aT x ν α s φ) in
/-- `Z_{x,s} = Ĝ_{k,x,s} - Π_{x,s}`: the operator between `Q` and `Q*` in `C_x(s)`. -/
noncomputable def decZ : Matrix (G.Ω 1 × Fin N) (G.Ω 1 × Fin N) ℂ :=
  liftOp N (Gsx G a aT x ν α s) - decPi G a aT x ν α s φ

/-- The algebraic identity behind the closeness of the covariance:
`Z_s - Z_1 = Δ (1 - Ψ_s) + G_1 F M_s⁻¹ K Δ (1 - Ψ_1)`, `Ψ_s = F M_s⁻¹ N_s`, `Δ = Ĝ_s - Ĝ_1`. -/
theorem decZ_sub_eq (hMs : IsUnit (decM G a aT x ν α s φ))
    (hM1 : IsUnit (decM G a aT x ν α (fun _ => 1) φ)) :
    decZ G a aT x ν α s φ - decZ G a aT x ν α (fun _ => 1) φ =
      (liftOp N (Gsx G a aT x ν α s) - liftOp N (Gsx G a aT x ν α (fun _ => 1))) *
          (1 - fieldMul (restrictField G φ) * (decM G a aT x ν α s φ)⁻¹ *
            decN G a aT x ν α s φ) +
        liftOp N (Gsx G a aT x ν α (fun _ => 1)) * fieldMul (restrictField G φ) *
          (decM G a aT x ν α s φ)⁻¹ * commK (xDirichletOperator G a aT x ν α) (restrictField G φ) *
          (liftOp N (Gsx G a aT x ν α s) - liftOp N (Gsx G a aT x ν α (fun _ => 1))) *
          (1 - fieldMul (restrictField G φ) * (decM G a aT x ν α (fun _ => 1) φ)⁻¹ *
            decN G a aT x ν α (fun _ => 1) φ) := by
  unfold decZ decPi
  refine abstract_identity _ _ _ _ (decM G a aT x ν α (fun _ => 1) φ) (decM G a aT x ν α s φ)
    _ _ _ _ ?_ ?_ ?_ ?_
  · unfold decM constraintM
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
    abel
  · unfold decN constraintN
    simp only [Matrix.mul_sub]
    abel
  · exact Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hMs)
  · exact Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hM1)

theorem vecSrc_sub_le (ε : ℝ) (r : CTorus d L N₁ m₁ (k + 1) → ℝ) (u v : G.Ω 1 × Fin N → ℂ) :
    vecSrc G ε r (u - v) ≤ 2 * vecSrc G ε r u + 2 * vecSrc G ε r v := by
  unfold vecSrc
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  exact agmonSource_sub_le G ε r (comp G u i) (comp G v i)

theorem vecM_sub_le (ε : ℝ) (r : CTorus d L N₁ m₁ (k + 1) → ℝ) (u v : G.Ω 1 × Fin N → ℂ) :
    vecM G ε r (u - v) ≤ 2 * vecM G ε r u + 2 * vecM G ε r v := by
  rw [vecM_eq, vecM_eq, vecM_eq, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  exact cwsq_agmonField_sub_le (G := G) ε r (comp G u i) (comp G v i)

theorem vecM_add_le (ε : ℝ) (r : CTorus d L N₁ m₁ (k + 1) → ℝ) (u v : G.Ω 1 × Fin N → ℂ) :
    vecM G ε r (u + v) ≤ 2 * vecM G ε r u + 2 * vecM G ε r v := by
  have h : u + v = u - (-1 : ℂ) • v := by simp
  have h2 : vecM G ε r ((-1 : ℂ) • v) = vecM G ε r v := by
    rw [vecM_eq, vecM_eq]
    refine Finset.sum_congr rfl fun i _ => ?_
    unfold cwsq
    refine Finset.sum_congr rfl fun z _ => ?_
    congr 1
    have : agmonField G ε r (comp G ((-1 : ℂ) • v) i) z = -agmonField G ε r (comp G v i) z := by
      unfold agmonField
      have hz : zeroExt (G.Ω 1) (comp G ((-1 : ℂ) • v) i) z = -zeroExt (G.Ω 1) (comp G v i) z := by
        by_cases hz : z ∈ G.Ω 1 <;> simp [zeroExt, hz, Multiscale.comp]
      rw [hz]; ring
    rw [this, norm_neg]
  rw [h]
  have := vecM_sub_le ε r u ((-1 : ℂ) • v)
  rw [h2] at this
  exact this

section PsiBoundsCover

variable {Cx : ℝ} (D : Dec2.XData (coverOf G) G a aT ν x α κ s Cx) {ε : ℝ}
  {r : CTorus d L N₁ m₁ (k + 1) → ℝ}
  (W : XWeight G ε r) (hφ : IsConstraintField G δ φ) (hδ : 0 ≤ δ)
  (hsm : δ ^ 2 * smallConstX d L κ ≤ 1 / 4)
include D W hφ hδ hsm

theorem vecSrc_Psi_le_cover (f : G.Ω 1 × Fin N → ℂ) :
    vecSrc G ε r ((fieldMul (restrictField G φ) * (decM G a aT x ν α s φ)⁻¹ *
      decN G a aT x ν α s φ) *ᵥ f) ≤ 45 * vecSrc G ε r f := by
  rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have h1 := vecSrc_fieldMul_le (ε := ε) (r := r) hφ
    ((decM G a aT x ν α s φ)⁻¹ *ᵥ (decN G a aT x ν α s φ *ᵥ f))
  have h2 := decM_inv_le_cover D W hφ hδ hsm (decN G a aT x ν α s φ *ᵥ f)
  have h3 := decN_src_le_cover D W hφ hδ hsm f
  have h4 := vecSrc_nonneg G ε r f
  linarith

theorem vecSrc_one_sub_Psi_le_cover (f : G.Ω 1 × Fin N → ℂ) :
    vecSrc G ε r ((1 - fieldMul (restrictField G φ) * (decM G a aT x ν α s φ)⁻¹ *
      decN G a aT x ν α s φ) *ᵥ f) ≤ 92 * vecSrc G ε r f := by
  have e : (1 - fieldMul (restrictField G φ) * (decM G a aT x ν α s φ)⁻¹ *
      decN G a aT x ν α s φ) *ᵥ f = f - (fieldMul (restrictField G φ) *
        (decM G a aT x ν α s φ)⁻¹ * decN G a aT x ν α s φ) *ᵥ f := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
  rw [e]
  have h1 := vecSrc_sub_le ε r f ((fieldMul (restrictField G φ) *
    (decM G a aT x ν α s φ)⁻¹ * decN G a aT x ν α s φ) *ᵥ f)
  have h2 := vecSrc_Psi_le_cover D W hφ hδ hsm f
  linarith

end PsiBoundsCover

section PsiBounds

variable (D : XData G a aT ν x α κ s) {ε : ℝ} {r : CTorus d L N₁ m₁ (k + 1) → ℝ}
  (W : XWeight G ε r) (hφ : IsConstraintField G δ φ) (hδ : 0 ≤ δ)
  (hsm : δ ^ 2 * smallConstX d L κ ≤ 1 / 4)
include D W hφ hδ hsm

theorem vecSrc_Psi_le (f : G.Ω 1 × Fin N → ℂ) :
    vecSrc G ε r ((fieldMul (restrictField G φ) * (decM G a aT x ν α s φ)⁻¹ *
      decN G a aT x ν α s φ) *ᵥ f) ≤ 45 * vecSrc G ε r f :=
  vecSrc_Psi_le_cover D.toCover W hφ hδ hsm f

theorem vecSrc_one_sub_Psi_le (f : G.Ω 1 × Fin N → ℂ) :
    vecSrc G ε r ((1 - fieldMul (restrictField G φ) * (decM G a aT x ν α s φ)⁻¹ *
      decN G a aT x ν α s φ) *ᵥ f) ≤ 92 * vecSrc G ε r f :=
  vecSrc_one_sub_Psi_le_cover D.toCover W hφ hδ hsm f

end PsiBounds

/-- The constant of the closeness of `Z`. -/
noncomputable def zCloseConst (d L : ℕ) : ℝ :=
  184 * closeConstX d + 207 * (valConstX d * commXConst d L * (gradCloseConstX d + closeConstX d))

theorem closeConstX_nonneg (d : ℕ) : 0 ≤ closeConstX d := by unfold closeConstX; positivity

theorem gradCloseConstX_nonneg (d : ℕ) : 0 ≤ gradCloseConstX d := by
  unfold gradCloseConstX gradStarConstX; positivity

theorem smallConstX_mono (d L : ℕ) {κ : ℝ} (hκ : 0 ≤ κ) : smallConstX d L 0 ≤ smallConstX d L κ := by
  unfold smallConstX kConstX
  have h1 : (1 : ℝ) ≤ Real.exp (N0 d L * κ) ^ 2 := by
    have : (1 : ℝ) ≤ Real.exp (N0 d L * κ) := Real.one_le_exp (by positivity)
    exact one_le_pow₀ this
  have h2 : Real.exp (N0 d L * 0) ^ 2 = 1 := by simp
  rw [h2]
  have hc := commXConst_nonneg d L
  have hv : 0 ≤ gradConstX d + valConstX d := by unfold gradConstX valConstX; positivity
  have := mul_le_mul_of_nonneg_left h1 (mul_nonneg hc hv)
  nlinarith [mul_nonneg hc hv]

theorem delta_sq_le_eighth (d L : ℕ) {κ δ : ℝ} (hsm : δ ^ 2 * smallConstX d L κ ≤ 1 / 4) :
    δ ^ 2 ≤ 1 / 8 := by
  have h2 : (2 : ℝ) ≤ smallConstX d L κ := by
    unfold smallConstX
    have := kConstX_nonneg d L κ
    linarith
  nlinarith [sq_nonneg δ]

section ZMainCover

variable {Cx : ℝ} (D : Dec2.XData (coverOf G) G a aT ν x α κ s Cx)
  {W : Finset (CTorus d L N₁ m₁ (k + 1))}
  (hW : ∀ z ∈ cubeIdx G, sProd G s z ≠ 1 → intBox z ⊆ W) (T : ℝ) {ε : ℝ} (hε0 : 0 ≤ ε)
  (hε1 : ε ≤ xAgmonRate d L) (hφ : IsConstraintField G δ φ) (hδ : 0 ≤ δ)
  (hsm : δ ^ 2 * smallConstX d L κ ≤ 1 / 4)
include D hW hε0 hε1 hφ hδ hsm

/-- **Closeness of `Z_{x,s} = Ĝ_{k,x,s} - Π_{x,s}` to `Z_{x,1}`** for the data `Dec2.XData` of the
pair `(coverOf G, G)` in the weighted block norm:
`‖ℓ⁻¹ e^{ε r} (Z_s - Z_1) f‖² ≤ B e^{2 N₀ κ} ‖ℓ f‖²` with the unweighted source, `r` the truncated
path distance to the set `W` containing the cubes with `s_z ≠ 1`. -/
theorem vecM_decZ_sub_le_cover (f : G.Ω 1 × Fin N → ℂ) :
    vecM G ε (truncSetDistR G W T)
        ((decZ G a aT x ν α s φ - decZ G a aT x ν α (fun _ => 1) φ) *ᵥ f) ≤
      zCloseConst d L * Real.exp (N0 d L * κ) ^ 2 * vecSrc G 0 (fun _ => 0) f := by
  classical
  set r := truncSetDistR G W T with hrdef
  have hr := isAgmonWeight_truncSetDistR G W T
  have WW : XWeight G ε r := ⟨hr, hε0, hε1⟩
  have H0 : XWeight G 0 (fun _ => 0) := D.weight_zero
  have hE1 : 1 ≤ Real.exp (N0 d L * κ) := Real.one_le_exp (by have := D.κ0; positivity)
  have hE2 : 1 ≤ Real.exp (N0 d L * κ) ^ 2 := one_le_pow₀ hE1
  have D1 : Dec2.XData (coverOf G) G a aT ν x α 0 (fun _ => 1) Cx :=
    ⟨D.st, D.Cx_nn, D.pot, D.x0, le_rfl, by
      simp only [mul_zero, Real.exp_zero, mul_one]
      have := Dec2.cstarX_pos d L D.Cx_nn
      nlinarith [D.big], fun P => by simp⟩
  have hsm1 : δ ^ 2 * smallConstX d L 0 ≤ 1 / 4 :=
    le_trans (mul_le_mul_of_nonneg_left (smallConstX_mono d L D.κ0) (sq_nonneg δ)) hsm
  have hMs := decM_isUnit_cover D hφ hδ hsm
  have hM1 := decM_isUnit_cover D1 hφ hδ hsm1
  have hGsone : Gsx G a aT x ν α (fun _ => 1) = (xDirichletOperator G a aT x ν α)⁻¹ := by
    have h := Dec2.Gsx_one D.st D.pot D.x0 D1.isUnit_one_sub
    exact h
  have hΔ : liftOp N (Gsx G a aT x ν α s) - liftOp N (Gsx G a aT x ν α (fun _ => 1)) =
      deltaOp G a aT x ν α s := by
    unfold deltaOp; rw [hGsone]
  have hG1 : liftOp N (Gsx G a aT x ν α (fun _ => 1)) =
      liftOp N (xDirichletOperator G a aT x ν α)⁻¹ := by rw [hGsone]
  rw [decZ_sub_eq hMs hM1, hΔ, Matrix.add_mulVec]
  set S := vecSrc G 0 (fun _ => 0) f with hS
  have hS0 : 0 ≤ S := vecSrc_nonneg G 0 _ f
  set E := Real.exp (N0 d L * κ) ^ 2 with hEdef
  -- the first term
  have hP1 := vecSrc_one_sub_Psi_le_cover D H0 hφ hδ hsm f
  have hP1' := vecSrc_one_sub_Psi_le_cover D1 H0 hφ hδ hsm1 f
  have hA := vecM_deltaOp_cover D hW T hε0 hε1
    ((1 - fieldMul (restrictField G φ) * (decM G a aT x ν α s φ)⁻¹ * decN G a aT x ν α s φ) *ᵥ f)
  have hcc := closeConstX_nonneg d
  have hgc := gradCloseConstX_nonneg d
  have hvc : 0 ≤ valConstX d := by unfold valConstX; positivity
  have hck := commXConst_nonneg d L
  have hA2 : vecM G ε r (deltaOp G a aT x ν α s *ᵥ
      ((1 - fieldMul (restrictField G φ) * (decM G a aT x ν α s φ)⁻¹ *
        decN G a aT x ν α s φ) *ᵥ f)) ≤ (closeConstX d * 92) * E * S := by
    refine hA.trans ?_
    calc closeConstX d * E * vecSrc G 0 (fun _ => 0) ((1 - fieldMul (restrictField G φ) *
          (decM G a aT x ν α s φ)⁻¹ * decN G a aT x ν α s φ) *ᵥ f)
        ≤ closeConstX d * E * (92 * S) := by gcongr
      _ = _ := by ring
  -- the second term
  set w2 := (1 - fieldMul (restrictField G φ) * (decM G a aT x ν α (fun _ => 1) φ)⁻¹ *
    decN G a aT x ν α (fun _ => 1) φ) *ᵥ f with hw2
  set u2 := deltaOp G a aT x ν α s *ᵥ w2 with hu2
  have hM2 := vecM_deltaOp_cover D hW T hε0 hε1 w2
  have hG2 := vecGrad_deltaOp_cover D hW T hε0 hε1 w2
  have hw2S : vecSrc G 0 (fun _ => 0) w2 ≤ 92 * S := hP1'
  have hM2' : vecM G ε r u2 ≤ (closeConstX d * 92) * E * S := by
    refine hM2.trans ?_
    calc closeConstX d * E * vecSrc G 0 (fun _ => 0) w2 ≤ closeConstX d * E * (92 * S) := by
          gcongr
      _ = _ := by ring
  have hG2' : vecGradOn G ε r Finset.univ u2 ≤ (gradCloseConstX d * 92) * E * S := by
    refine hG2.trans ?_
    calc gradCloseConstX d * E * vecSrc G 0 (fun _ => 0) w2 ≤ gradCloseConstX d * E * (92 * S) := by
          gcongr
      _ = _ := by ring
  have hhd : 0 < d := by have := D.st.hd; omega
  have hε2 : ε ≤ agmonRate d :=
    hε1.trans (xAgmonRate_le_agmonRate hhd (by have := D.st.hL; omega))
  have hK := agmonSource_commKx_le_of_ak (ν := ν) G hhd D.st.ha ⟨D.st.hak1, D.st.hak2⟩ D.st.haT1 D.x0 α hφ.toIsSmoothField hδ
    hr hε0 hε2 u2 Finset.univ (fun y hy => absurd (Finset.mem_univ _) hy)
  have hδ8 := delta_sq_le_eighth d L hsm
  have hk2 : agmonSource G ε r (commK (xDirichletOperator G a aT x ν α) (restrictField G φ) *ᵥ u2) ≤
      commXConst d L * (1 / 8) * ((gradCloseConstX d * 92 + closeConstX d * 92) * E * S) := by
    refine hK.trans ?_
    have hsum : vecGradOn G ε r Finset.univ u2 + vecM G ε r u2 ≤
        (gradCloseConstX d * 92 + closeConstX d * 92) * E * S := by nlinarith
    have hnn : 0 ≤ vecGradOn G ε r Finset.univ u2 + vecM G ε r u2 := by
      have h1 := vecM_nonneg (G := G) ε r u2
      have h2 : 0 ≤ vecGradOn G ε r Finset.univ u2 := by
        rw [vecGradOn_eq]
        exact Finset.sum_nonneg fun i _ => gradOn_nonneg _ _ _ _ _
      linarith
    calc commXConst d L * δ ^ 2 * (vecGradOn G ε r Finset.univ u2 + vecM G ε r u2)
        ≤ commXConst d L * (1 / 8) * (vecGradOn G ε r Finset.univ u2 + vecM G ε r u2) := by
          gcongr
      _ ≤ _ := by gcongr
  set Ku := commK (xDirichletOperator G a aT x ν α) (restrictField G φ) *ᵥ u2 with hKu
  have hv := decM_inv_le_cover D WW hφ hδ hsm Ku
  have hFv := vecSrc_fieldMul_le (ε := ε) (r := r) hφ ((decM G a aT x ν α s φ)⁻¹ *ᵥ Ku)
  have hG1b := Gsx_vec_bounds_cover D1 WW
    (fieldMul (restrictField G φ) *ᵥ ((decM G a aT x ν α s φ)⁻¹ *ᵥ Ku))
  have hB : vecM G ε r (liftOp N (Gsx G a aT x ν α (fun _ => 1)) *ᵥ
      (fieldMul (restrictField G φ) *ᵥ ((decM G a aT x ν α s φ)⁻¹ *ᵥ Ku))) ≤
      valConstX d * (9 * (commXConst d L * (1 / 8) *
        ((gradCloseConstX d * 92 + closeConstX d * 92) * E * S))) := by
    refine hG1b.1.trans ?_
    simp only [mul_zero, Real.exp_zero, one_pow, mul_one]
    have hn := agmonSource_nonneg G ε r Ku
    have hn2 := agmonSource_nonneg G ε r ((decM G a aT x ν α s φ)⁻¹ *ᵥ Ku)
    gcongr
    linarith
  have hsecond : (liftOp N (Gsx G a aT x ν α (fun _ => 1)) * fieldMul (restrictField G φ) *
      (decM G a aT x ν α s φ)⁻¹ * commK (xDirichletOperator G a aT x ν α) (restrictField G φ) *
      deltaOp G a aT x ν α s *
      (1 - fieldMul (restrictField G φ) * (decM G a aT x ν α (fun _ => 1) φ)⁻¹ *
        decN G a aT x ν α (fun _ => 1) φ)) *ᵥ f =
      liftOp N (Gsx G a aT x ν α (fun _ => 1)) *ᵥ
        (fieldMul (restrictField G φ) *ᵥ ((decM G a aT x ν α s φ)⁻¹ *ᵥ Ku)) := by
    simp only [← Matrix.mulVec_mulVec]
    rfl
  have hfirst : (deltaOp G a aT x ν α s *
      (1 - fieldMul (restrictField G φ) * (decM G a aT x ν α s φ)⁻¹ *
        decN G a aT x ν α s φ)) *ᵥ f = deltaOp G a aT x ν α s *ᵥ
      ((1 - fieldMul (restrictField G φ) * (decM G a aT x ν α s φ)⁻¹ *
        decN G a aT x ν α s φ) *ᵥ f) := by rw [Matrix.mulVec_mulVec]
  rw [hfirst, hsecond]
  refine (vecM_add_le ε r _ _).trans ?_
  have hz : zCloseConst d L * E * S = 2 * ((closeConstX d * 92) * E * S) +
      2 * (valConstX d * (9 * (commXConst d L * (1 / 8) *
        ((gradCloseConstX d * 92 + closeConstX d * 92) * E * S)))) := by
    unfold zCloseConst; ring
  rw [hz]
  linarith

end ZMainCover

section ZMain

variable (D : XData G a aT ν x α κ s) {W : Finset (CTorus d L N₁ m₁ (k + 1))}
  (hW : ∀ z ∈ cubeIdx G, sProd G s z ≠ 1 → intBox z ⊆ W) (T : ℝ) {ε : ℝ} (hε0 : 0 ≤ ε)
  (hε1 : ε ≤ xAgmonRate d L) (hφ : IsConstraintField G δ φ) (hδ : 0 ≤ δ)
  (hsm : δ ^ 2 * smallConstX d L κ ≤ 1 / 4)
include D hW hε0 hε1 hφ hδ hsm

/-- **Closeness of `Z_{x,s} = Ĝ_{k,x,s} - Π_{x,s}` to `Z_{x,1}`** in the weighted block norm:
`‖ℓ⁻¹ e^{ε r} (Z_s - Z_1) f‖² ≤ B e^{2 N₀ κ} ‖ℓ f‖²` with the unweighted source, `r` the truncated
path distance to the set `W` containing the cubes with `s_z ≠ 1`. -/
theorem vecM_decZ_sub_le (f : G.Ω 1 × Fin N → ℂ) :
    vecM G ε (truncSetDistR G W T)
        ((decZ G a aT x ν α s φ - decZ G a aT x ν α (fun _ => 1) φ) *ᵥ f) ≤
      zCloseConst d L * Real.exp (N0 d L * κ) ^ 2 * vecSrc G 0 (fun _ => 0) f :=
  vecM_decZ_sub_le_cover D.toCover hW T hε0 hε1 hφ hδ hsm f

end ZMain

end ZClose

end Balaban.Localization
