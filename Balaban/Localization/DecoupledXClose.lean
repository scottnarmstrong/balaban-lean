/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.DecoupledXLocal
public import Balaban.Localization.DecoupledClose
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# (DG6): closeness of `G_{k,x,s}(A)` to `G_{k,x}(A)` away from the parameters

If every centre `z` with `s_z ≠ 1` has its interaction cube inside a set `W` then
`G_{k,x,s}(A) f - H_{k,x}(A)⁻¹ f` decays away from `W`, in the weighted `L²` form with the weight
`e^{ε r}`, `r` the (truncated) path distance to `W` (`truncSetDistR`), and an unweighted source:

* `truncSetDistR`, `isAgmonWeight_truncSetDistR`: the weight exponent;
* `Gsx_sub_Gd`: `(G_s - G_D) f = (G*_s - G*_1) g + G_D (𝒦_s - 𝒦_1) g`, `g = (1 - 𝒦_s)⁻¹ f`;
* `Gsx_one`: `G_{k,x,1} = H_{k,x}⁻¹` (the identification at `s ≡ 1`);
* `XData.dg6`: `‖ℓ⁻¹ e^{ε r}(G_s - G_D) f‖² ≤ B e^{2 N₀ κ} ‖ℓ f‖²`.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Finset Matrix

variable {d L N₁ m₁ k : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}

section Weight

/-- The path distance to a set of sites, truncated at `T`, as a real number. -/
noncomputable def truncSetDistR {K : ℕ} (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ)
    (W : Finset (CTorus d L N₁ m₁ K)) (T : ℝ) (y : CTorus d L N₁ m₁ K) : ℝ :=
  (min (siteSetDist G W y) (ENNReal.ofReal T)).toReal

theorem abs_truncSetDistR_sub_le {K : ℕ} (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ)
    (W : Finset (CTorus d L N₁ m₁ K)) (T : ℝ) {y y' : CTorus d L N₁ m₁ K} {c : ℝ} (hc : 0 ≤ c)
    (h1 : siteSetDist G W y ≤ ENNReal.ofReal c + siteSetDist G W y')
    (h2 : siteSetDist G W y' ≤ ENNReal.ofReal c + siteSetDist G W y) :
    |truncSetDistR G W T y - truncSetDistR G W T y'| ≤ c := by
  have key : ∀ a b : ENNReal, a ≤ ENNReal.ofReal c + b →
      min a (ENNReal.ofReal T) ≤ ENNReal.ofReal c + min b (ENNReal.ofReal T) := by
    intro a b hab
    rcases le_total b (ENNReal.ofReal T) with hb | hb
    · rw [min_eq_left hb]; exact (min_le_left _ _).trans hab
    · rw [min_eq_right hb]; exact (min_le_right _ _).trans le_add_self
  exact abs_toReal_sub_le hc (key _ _ h1) (key _ _ h2)

theorem isAgmonWeight_truncSetDistR {K : ℕ} (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ)
    (W : Finset (CTorus d L N₁ m₁ K)) (T : ℝ) : IsAgmonWeight G (truncSetDistR G W T) where
  bond := by
    intro y y' hy hy' hadj
    refine abs_truncSetDistR_sub_le G W T (G.bondCost_nonneg y y') ?_ ?_
    · exact (setDist_triangle W y y').trans (by
        gcongr; exact G.pathDist_le_bondCost hy hy' hadj)
    · refine (setDist_triangle W y' y).trans (by
        gcongr
        rw [GeneratingSet.bondCost_comm]; exact G.pathDist_le_bondCost hy' hy hadj.symm)
  block := by
    intro j hj hjk y y' hy h
    have hd : (0 : ℝ) ≤ 2 * d := by positivity
    have h1 := G.pathDist_block_le hj hjk hy h
    have h2 : G.pathDist y' y ≤ ENNReal.ofReal (2 * d) := by
      rw [GeneratingSet.pathDist_comm]; exact h1
    refine abs_truncSetDistR_sub_le G W T hd ?_ ?_
    · exact (setDist_triangle W y y').trans (by gcongr)
    · exact (setDist_triangle W y' y).trans (by gcongr)

theorem truncSetDistR_of_mem {K : ℕ} (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ)
    {W : Finset (CTorus d L N₁ m₁ K)} (T : ℝ) {y : CTorus d L N₁ m₁ K} (hy : y ∈ W)
    (hyΩ : y ∈ G.Ω 1) : truncSetDistR G W T y = 0 := by
  simp [truncSetDistR, setDist_of_mem W hy hyΩ]

end Weight

section Algebra

variable {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} {a : ℕ → ℝ} {aT x ν : ℝ}
  {α : G.Ω 1 → ℂ} {κ : ℝ} {s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ}

theorem xDirichlet_isUnit (S : XSetting G a aT ν) (hα : AdmPot G α) (hx : 0 ≤ x) :
    IsUnit (xDirichletOperator G a aT x ν α) :=
  xDirichletOperator_isUnit_sharp G S.dg.hL S.hk S.dg.mass S.ha S.haT1 S.haT2 hx α
    (AdmPot.le_eighth S.dg hα)

/-- **The algebraic identity behind (DG6)**:
`(G_s - G_D) f = (G*_s - G*_1) g + G_D (𝒦_s - 𝒦_1) g`, `g = (1 - 𝒦_s)⁻¹ f`. -/
theorem Gsx_sub_Gd (S : XSetting G a aT ν) (hα : AdmPot G α) (hx : 0 ≤ x)
    (hU : IsUnit (1 - Kcalx G a aT x ν α s)) (f : G.Ω 1 → ℂ) :
    Gsx G a aT x ν α s *ᵥ f - (xDirichletOperator G a aT x ν α)⁻¹ *ᵥ f =
      (Gstarx G a aT x ν α s - Gstarx G a aT x ν α (fun _ => 1)) *ᵥ
          ((1 - Kcalx G a aT x ν α s)⁻¹ *ᵥ f) +
      (xDirichletOperator G a aT x ν α)⁻¹ *ᵥ
        ((Kcalx G a aT x ν α s - Kcalx G a aT x ν α (fun _ => 1)) *ᵥ
          ((1 - Kcalx G a aT x ν α s)⁻¹ *ᵥ f)) := by
  have hHU := xDirichlet_isUnit S hα hx
  have hdetH := (Matrix.isUnit_iff_isUnit_det _).1 hHU
  have hdetK := (Matrix.isUnit_iff_isUnit_det _).1 hU
  have hpar := parametrix_x S hα hx
  set Gd := (xDirichletOperator G a aT x ν α)⁻¹ with hGd
  have h1 : Gstarx G a aT x ν α (fun _ => 1) =
      Gd * (1 - Kcalx G a aT x ν α (fun _ => 1)) := by
    rw [← hpar, ← Matrix.mul_assoc, hGd, Matrix.nonsing_inv_mul _ hdetH, Matrix.one_mul]
  set g := (1 - Kcalx G a aT x ν α s)⁻¹ *ᵥ f with hg
  have hg1 : (1 - Kcalx G a aT x ν α s) *ᵥ g = f := by
    rw [hg, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdetK, Matrix.one_mulVec]
  have e : Gsx G a aT x ν α s *ᵥ f = Gstarx G a aT x ν α s *ᵥ g := by
    rw [hg, Gsx, ← Matrix.mulVec_mulVec]
  have hA1g : Gstarx G a aT x ν α (fun _ => 1) *ᵥ g =
      Gd *ᵥ (g - Kcalx G a aT x ν α (fun _ => 1) *ᵥ g) := by
    rw [h1, ← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec]
  have hf : f = g - Kcalx G a aT x ν α s *ᵥ g := by
    rw [← hg1, Matrix.sub_mulVec, Matrix.one_mulVec]
  rw [e, Matrix.sub_mulVec, Matrix.sub_mulVec, hA1g, Matrix.mulVec_sub, Matrix.mulVec_sub]
  conv_lhs => rw [hf, Matrix.mulVec_sub]
  abel

/-- At `s ≡ 1` with `1 - 𝒦_1` invertible, `G_{k,x,1} = H_{k,x}⁻¹`. -/
theorem Gsx_one (S : XSetting G a aT ν) (hα : AdmPot G α) (hx : 0 ≤ x)
    (hU : IsUnit (1 - Kcalx G a aT x ν α (fun _ => 1))) :
    Gsx G a aT x ν α (fun _ => 1) = (xDirichletOperator G a aT x ν α)⁻¹ := by
  have hdetK := (Matrix.isUnit_iff_isUnit_det _).1 hU
  have hpar := parametrix_x S hα hx
  have h1 : xDirichletOperator G a aT x ν α * Gsx G a aT x ν α (fun _ => 1) = 1 := by
    unfold Gsx
    rw [← Matrix.mul_assoc, hpar, Matrix.mul_nonsing_inv _ hdetK]
  exact (Matrix.inv_eq_right_inv h1).symm

/-- `(G*_s - G*_1) g` vanishes off `W`. -/
theorem Gstarx_diff_zero (S : XSetting G a aT ν) (hα : AdmPot G α) (hx : 0 ≤ x)
    {W : Finset (CTorus d L N₁ m₁ (k + 1))}
    (hW : ∀ z ∈ cubeIdx G, sProd G s z ≠ 1 → intBox z ⊆ W) (g : G.Ω 1 → ℂ)
    {y : CTorus d L N₁ m₁ (k + 1)} (hy : y ∉ W) :
    zeroExt (G.Ω 1) (Gstarx G a aT x ν α s *ᵥ g) y -
      zeroExt (G.Ω 1) (Gstarx G a aT x ν α (fun _ => 1) *ᵥ g) y = 0 := by
  rw [zeroExt_Gstarx, zeroExt_Gstarx, ← Finset.sum_sub_distrib]
  refine Finset.sum_eq_zero fun z hz => ?_
  by_cases hc : sProd G s z = 1
  · rw [hc, sProd_one]; ring
  · have hb : y ∉ intBox z := fun h => hy (hW z hz hc h)
    have : zeroExt (G.Ω 1) (cubeGx G a aT x ν α z *ᵥ g) y = 0 := by
      by_cases hyΩ : y ∈ G.Ω 1
      · rw [zeroExt_mem' _ hyΩ]; exact cubeGx_supp S hα hx hz g ⟨y, hyΩ⟩ hb
      · exact zeroExt_not_mem _ _ hyΩ
    rw [this]; simp

/-- `(𝒦_s - 𝒦_1) g` vanishes off `W`. -/
theorem Kcalx_diff_zero (S : XSetting G a aT ν)
    {W : Finset (CTorus d L N₁ m₁ (k + 1))}
    (hW : ∀ z ∈ cubeIdx G, sProd G s z ≠ 1 → intBox z ⊆ W) (g : G.Ω 1 → ℂ) {y : G.Ω 1}
    (hy : (y : CTorus d L N₁ m₁ (k + 1)) ∉ W) :
    ((Kcalx G a aT x ν α s - Kcalx G a aT x ν α (fun _ => 1)) *ᵥ g) y = 0 := by
  rw [Matrix.sub_mulVec, Pi.sub_apply]
  unfold Kcalx
  rw [Matrix.sum_mulVec, Matrix.sum_mulVec, Finset.sum_apply, Finset.sum_apply,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_eq_zero fun z hz => ?_
  by_cases hc : sProd G s z = 1
  · rw [hc, sProd_one]; ring
  · have hb : (y : CTorus d L N₁ m₁ (k + 1)) ∉ intBox z := fun h => hy (hW z hz hc h)
    have := rowSupp_Kzx_cubeGx (x := x) (α := α) S hz g y hb
    rw [Matrix.smul_mulVec, Matrix.smul_mulVec, Pi.smul_apply, Pi.smul_apply, smul_eq_mul,
      smul_eq_mul, this]
    simp

end Algebra

/-! ### (DG6) in the weighted `L²` form -/

section Close

variable {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} {a : ℕ → ℝ} {aT x ν : ℝ}
  {α : G.Ω 1 → ℂ} {κ : ℝ} {s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ}

theorem cwsq_agmonField_sub_le (ε : ℝ) (r : CTorus d L N₁ m₁ (k + 1) → ℝ) (u v : G.Ω 1 → ℂ) :
    cwsq G (agmonField G ε r (u - v)) ≤
      2 * cwsq G (agmonField G ε r u) + 2 * cwsq G (agmonField G ε r v) := by
  unfold cwsq
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun z _ => ?_
  have e : agmonField G ε r (u - v) z = agmonField G ε r u z - agmonField G ε r v z := by
    unfold agmonField; rw [zeroExt_sub']; ring
  rw [e]
  have h2 : ‖agmonField G ε r u z - agmonField G ε r v z‖ ^ 2 ≤
      2 * ‖agmonField G ε r u z‖ ^ 2 + 2 * ‖agmonField G ε r v z‖ ^ 2 := by
    have h := norm_sub_le (agmonField G ε r u z) (agmonField G ε r v z)
    nlinarith [sq_nonneg (‖agmonField G ε r u z‖ - ‖agmonField G ε r v z‖),
      norm_nonneg (agmonField G ε r u z), norm_nonneg (agmonField G ε r v z),
      norm_nonneg (agmonField G ε r u z - agmonField G ε r v z)]
  have h0 := invSqSpacing_nonneg G z
  nlinarith [mul_le_mul_of_nonneg_left h2 h0]

theorem Gd_cwsq_le (S : XSetting G a aT ν) (hα : AdmPot G α) (hx : 0 ≤ x)
    {r : CTorus d L N₁ m₁ (k + 1) → ℝ} (hr : IsAgmonWeight G r) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ xAgmonRate d L) (h : G.Ω 1 → ℂ) :
    cwsq G (agmonField G ε r ((xDirichletOperator G a aT x ν α)⁻¹ *ᵥ h)) ≤
      256 * agmonSource G ε r h := by
  have hdet := (Matrix.isUnit_iff_isUnit_det _).1 (xDirichlet_isUnit S hα hx)
  have hu : cutXOperator G a aT x ν ∅ α *ᵥ ((xDirichletOperator G a aT x ν α)⁻¹ *ᵥ h) = h := by
    rw [cutXOperator_empty, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet,
      Matrix.one_mulVec]
  have hen := x_agmon_energy_cut G (cutAligned_empty G) (by have := S.dg.hd; omega) S.dg.hL S.hk
    S.dg.mass S.ha S.haT1 S.haT2 hx α (AdmPot.le_eighth S.dg hα) hr hε0 hε1 hu
  have hE := cutEnergy_nonneg (∅ : Finset (CTorus d L N₁ m₁ (k + 1) × Fin d))
    (agmonField G ε r ((xDirichletOperator G a aT x ν α)⁻¹ *ᵥ h))
  linarith

/-- The closeness constant. -/
noncomputable def closeConstX (d : ℕ) : ℝ := (2048 * (3 * 5 ^ d) ^ 2 + 128) * (16 / 9)

/-- **(DG6), closeness, weighted `L²` form.** If every centre `z` with `s_z ≠ 1` has its
interaction cube inside `W`, then with the weight `e^{ε r}`, `r` the truncated path distance to `W`,
`‖ℓ⁻¹ e^{ε r} (G_{k,x,s} - H_{k,x}⁻¹) f‖² ≤ B e^{2 N₀ κ} ‖ℓ f‖²` (unweighted source). -/
theorem XData.dg6 (D : XData G a aT ν x α κ s) {W : Finset (CTorus d L N₁ m₁ (k + 1))}
    (hW : ∀ z ∈ cubeIdx G, sProd G s z ≠ 1 → intBox z ⊆ W) (T : ℝ) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ xAgmonRate d L) (f : G.Ω 1 → ℂ) :
    cwsq G (agmonField G ε (truncSetDistR G W T)
        (Gsx G a aT x ν α s *ᵥ f - (xDirichletOperator G a aT x ν α)⁻¹ *ᵥ f)) ≤
      closeConstX d * Real.exp (N0 d L * κ) ^ 2 * agmonSource G 0 (fun _ => 0) f := by
  have hd : 0 < d := by have := D.st.dg.hd; omega
  have hr := isAgmonWeight_truncSetDistR G W T
  have H0 : XWeight G 0 (fun _ => 0) :=
    ⟨isAgmonWeight_zero G, le_rfl, (xAgmonRate_pos hd D.st.dg.hL).le⟩
  have hE1 : 1 ≤ Real.exp (N0 d L * κ) := Real.one_le_exp (by have := D.κ0; positivity)
  have D1 : XData G a aT ν x α 0 (fun _ => 1) :=
    ⟨D.st, D.pot, D.x0, le_rfl, by
      simp only [mul_zero, Real.exp_zero, mul_one]
      have := cstarX_pos d L
      nlinarith [D.big], fun P => by simp⟩
  set g := (1 - Kcalx G a aT x ν α s)⁻¹ *ᵥ f with hg
  set A := (Gstarx G a aT x ν α s - Gstarx G a aT x ν α (fun _ => 1)) *ᵥ g with hA
  set h := (Kcalx G a aT x ν α s - Kcalx G a aT x ν α (fun _ => 1)) *ᵥ g with hh
  rw [Gsx_sub_Gd D.st D.pot D.x0 D.isUnit_one_sub f]
  have hsplit : cwsq G (agmonField G ε (truncSetDistR G W T)
      (A + (xDirichletOperator G a aT x ν α)⁻¹ *ᵥ h)) ≤
      2 * cwsq G (agmonField G ε (truncSetDistR G W T) A) +
      2 * cwsq G (agmonField G ε (truncSetDistR G W T) ((xDirichletOperator G a aT x ν α)⁻¹ *ᵥ h)) := by
    unfold cwsq
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun z _ => ?_
    have e : agmonField G ε (truncSetDistR G W T) (A + (xDirichletOperator G a aT x ν α)⁻¹ *ᵥ h) z =
        agmonField G ε (truncSetDistR G W T) A z +
          agmonField G ε (truncSetDistR G W T) ((xDirichletOperator G a aT x ν α)⁻¹ *ᵥ h) z := by
      unfold agmonField; rw [zeroExt_add']; ring
    rw [e]
    set p := agmonField G ε (truncSetDistR G W T) A z
    set q := agmonField G ε (truncSetDistR G W T) ((xDirichletOperator G a aT x ν α)⁻¹ *ᵥ h) z
    have h2 : ‖p + q‖ ^ 2 ≤ 2 * ‖p‖ ^ 2 + 2 * ‖q‖ ^ 2 := by
      have h := norm_add_le p q
      nlinarith [sq_nonneg (‖p‖ - ‖q‖), norm_nonneg p, norm_nonneg q, norm_nonneg (p + q)]
    have h0 := invSqSpacing_nonneg G z
    nlinarith [mul_le_mul_of_nonneg_left h2 h0]
  refine hsplit.trans ?_
  -- the Neumann bound for the intermediate vector
  have hg0 := D.neumann_src H0 f
  have hgnn := agmonSource_nonneg G 0 (fun _ => 0) g
  -- the term `A`
  have hAeq : cwsq G (agmonField G ε (truncSetDistR G W T) A) =
      cwsq G (agmonField G 0 (fun _ => 0) A) := by
    unfold cwsq
    refine Finset.sum_congr rfl fun z _ => ?_
    congr 1
    rw [norm_agmonField, norm_agmonField]
    by_cases hz0 : zeroExt (G.Ω 1) A z = 0
    · rw [hz0]; simp
    · have hzΩ : z ∈ G.Ω 1 := by
        by_contra hn; exact hz0 (zeroExt_not_mem _ _ hn)
      have hzW : z ∈ W := by
        by_contra hn
        apply hz0
        have := Gstarx_diff_zero D.st D.pot D.x0 hW g hn
        rw [hA, Matrix.sub_mulVec, zeroExt_sub']
        exact this
      rw [truncSetDistR_of_mem G T hzW hzΩ]
      simp
  have hAbd : cwsq G (agmonField G 0 (fun _ => 0) A) ≤
      2 * (256 * (3 * 5 ^ d : ℝ) ^ 2 * Real.exp (N0 d L * κ) ^ 2 * agmonSource G 0 (fun _ => 0) g) +
      2 * (256 * (3 * 5 ^ d : ℝ) ^ 2 * Real.exp (N0 d L * 0) ^ 2 *
        agmonSource G 0 (fun _ => 0) g) := by
    have := cwsq_agmonField_sub_le (G := G) 0 (fun _ => 0)
      (Gstarx G a aT x ν α s *ᵥ g) (Gstarx G a aT x ν α (fun _ => 1) *ᵥ g)
    rw [hA, Matrix.sub_mulVec]
    refine this.trans ?_
    have h1 := cwsq_Gstarx_le D H0 g
    have h2 := cwsq_Gstarx_le D1 H0 g
    linarith
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
    have := agmonSource_sub_le G 0 (fun _ => 0) (Kcalx G a aT x ν α s *ᵥ g)
      (Kcalx G a aT x ν α (fun _ => 1) *ᵥ g)
    have h1 := D.dg1 H0 g
    have h2 := D1.dg1 H0 g
    linarith
  have hBd := Gd_cwsq_le D.st D.pot D.x0 hr hε0 hε1 h
  rw [hAeq]
  have hE2 : 1 ≤ Real.exp (N0 d L * κ) ^ 2 := one_le_pow₀ hE1
  have hn0 : (0 : ℝ) ≤ (3 * 5 ^ d : ℝ) ^ 2 := sq_nonneg _
  simp only [mul_zero, Real.exp_zero, one_pow, mul_one] at hAbd
  have hS0 := agmonSource_nonneg G 0 (fun _ => 0) f
  have key : 2 * cwsq G (agmonField G 0 (fun _ => 0) A) +
      2 * cwsq G (agmonField G ε (truncSetDistR G W T) ((xDirichletOperator G a aT x ν α)⁻¹ *ᵥ h)) ≤
      (1024 * (3 * 5 ^ d : ℝ) ^ 2 * (Real.exp (N0 d L * κ) ^ 2 + 1) + 128) *
        agmonSource G 0 (fun _ => 0) g := by
    have := mul_le_mul_of_nonneg_left hhK (by norm_num : (0 : ℝ) ≤ 256)
    rw [hSrc] at hBd
    nlinarith
  calc _ ≤ _ := key
    _ ≤ (1024 * (3 * 5 ^ d : ℝ) ^ 2 * (Real.exp (N0 d L * κ) ^ 2 + 1) + 128) *
        ((16 / 9) * agmonSource G 0 (fun _ => 0) f) :=
        mul_le_mul_of_nonneg_left hg0 (by positivity)
    _ ≤ _ := by
        unfold closeConstX
        have : (1024 * (3 * 5 ^ d : ℝ) ^ 2 * (Real.exp (N0 d L * κ) ^ 2 + 1) + 128) ≤
            (2048 * (3 * 5 ^ d : ℝ) ^ 2 + 128) * Real.exp (N0 d L * κ) ^ 2 := by
          nlinarith [mul_nonneg hn0 (sub_nonneg.2 hE2)]
        calc _ ≤ ((2048 * (3 * 5 ^ d : ℝ) ^ 2 + 128) * Real.exp (N0 d L * κ) ^ 2) *
              ((16 / 9) * agmonSource G 0 (fun _ => 0) f) :=
            mul_le_mul_of_nonneg_right this (by positivity)
          _ = _ := by ring

end Close

end Balaban.Localization
