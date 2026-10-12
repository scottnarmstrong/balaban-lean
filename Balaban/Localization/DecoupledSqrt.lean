/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.DecoupledCovCont
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The `x`-integrals of I-4c (ii): `C^{1/2}(s)` and `𝕃(s)`

LOCALIZATION.md §3.4 (Def-L6): with `C_x(s)` of `Balaban/Localization/DecoupledCovBound.lean`,

`C^{1/2}(s) = π⁻¹ ∫₀^∞ x^{-1/2} C_x(s) dx`  (`decCovSqrt`),
`𝕃(s) = log a_k (1 - P) + log (a_k + b) P - ∫₀^∞ (C_x(s) - A_{k,x}) dx`  (`decLog`),

both defined as entrywise Bochner integrals over `(0, ∞)`. The integrability of the entries and
the operator bounds follow from `decCov_sub_le`:

* `decCovSqrt_bound`: `‖C^{1/2}(s) f‖ ≤ B₅ ‖f‖`, `B₅ = a_k^{-1/2} (1 + B₄ a_k⁻¹)` (the shape of
  P3 (3.24));
* `decLog_bound`: `‖𝕃(s) f‖ ≤ (max |log a_k| |log (a_k + b)| + B₄ a_k⁻¹) ‖f‖`.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Finset Matrix Set MeasureTheory Real

/-! ### Euclidean norms -/

section N2

variable {ι : Type*} [Fintype ι]

/-- The Euclidean norm `√(∑ ‖vᵢ‖²)`. -/
noncomputable def n2 (v : ι → ℂ) : ℝ := Real.sqrt (Green.sqNorm v)

theorem n2_nonneg (v : ι → ℂ) : 0 ≤ n2 v := Real.sqrt_nonneg _

theorem n2_sq (v : ι → ℂ) : n2 v ^ 2 = Green.sqNorm v :=
  Real.sq_sqrt (Green.sqNorm_nonneg v)

theorem n2_eq_norm (v : ι → ℂ) : n2 v = ‖(WithLp.toLp 2 v : EuclideanSpace ℂ ι)‖ := by
  rw [EuclideanSpace.norm_eq]
  rfl

theorem n2_add_le (u v : ι → ℂ) : n2 (u + v) ≤ n2 u + n2 v := by
  rw [n2_eq_norm, n2_eq_norm, n2_eq_norm]
  exact norm_add_le (WithLp.toLp 2 u : EuclideanSpace ℂ ι) (WithLp.toLp 2 v)

theorem sqNorm_le_iff {u f : ι → ℂ} {c : ℝ} (hc : 0 ≤ c) :
    Green.sqNorm u ≤ c ^ 2 * Green.sqNorm f ↔ n2 u ≤ c * n2 f := by
  rw [← n2_sq u, ← n2_sq f, ← mul_pow]
  exact pow_le_pow_iff_left₀ (n2_nonneg _) (mul_nonneg hc (n2_nonneg _)) two_ne_zero

theorem n2_smul (c : ℂ) (v : ι → ℂ) : n2 (c • v) = ‖c‖ * n2 v := by
  unfold n2
  rw [sqNorm_smul, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]

theorem n2_sub_le (u v : ι → ℂ) : n2 (u - v) ≤ n2 u + n2 v := by
  have : u - v = u + (-1 : ℂ) • v := by simp [sub_eq_add_neg]
  rw [this]
  refine (n2_add_le _ _).trans ?_
  rw [n2_smul]
  simp

variable [DecidableEq ι]

theorem norm_entry_le (M : Matrix ι ι ℂ) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ f : ι → ℂ, Green.sqNorm (M *ᵥ f) ≤ c ^ 2 * Green.sqNorm f) (p q : ι) :
    ‖M p q‖ ≤ c := by
  have h1 := h (Pi.single q 1)
  have h2 : Green.sqNorm (Pi.single q (1 : ℂ) : ι → ℂ) = 1 := by
    unfold Green.sqNorm
    rw [Finset.sum_eq_single q]
    · simp
    · intro j _ hj; simp [hj]
    · simp
  rw [h2, mul_one] at h1
  have h3 : ‖M p q‖ ^ 2 ≤ Green.sqNorm (M *ᵥ Pi.single q 1) := by
    unfold Green.sqNorm
    have : (M *ᵥ (Pi.single q 1 : ι → ℂ)) p = M p q := by
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    calc ‖M p q‖ ^ 2 = ‖(M *ᵥ (Pi.single q 1 : ι → ℂ)) p‖ ^ 2 := by rw [this]
      _ ≤ _ := Finset.single_le_sum (f := fun i => ‖(M *ᵥ (Pi.single q 1 : ι → ℂ)) i‖ ^ 2)
          (fun i _ => sq_nonneg _) (Finset.mem_univ p)
  exact (abs_le_of_sq_le_sq' (h3.trans h1) hc).2

/-- Bound of a combination `c₁ (1 - P) + c₂ P` of complementary orthogonal projections. -/
theorem sqNorm_twoProj_le {P : Matrix ι ι ℂ} (hh : Pᴴ = P) (hi : P * P = P) (c₁ c₂ : ℂ)
    (h : ι → ℂ) :
    Green.sqNorm ((c₁ • (1 - P) + c₂ • P) *ᵥ h) ≤ (max ‖c₁‖ ‖c₂‖) ^ 2 * Green.sqNorm h := by
  rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec]
  have h1 : Pᴴ * (1 - P) = 0 := by rw [hh, Matrix.mul_sub, Matrix.mul_one, hi, sub_self]
  have h2 : (1 - P)ᴴ * P = 0 := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hh, Matrix.sub_mul, Matrix.one_mul,
      hi, sub_self]
  have o1 := star_mulVec_dot_eq_zero P (1 - P) h h1
  have o2 := star_mulVec_dot_eq_zero (1 - P) P h h2
  rw [add_comm, sqNorm_add_of_orth]
  · rw [sqNorm_smul, sqNorm_smul]
    have hP := sqNorm_proj hh hi h
    have hu := sqNorm_nonneg' (P *ᵥ h)
    have hw := sqNorm_nonneg' ((1 - P) *ᵥ h)
    have m1 : ‖c₁‖ ^ 2 ≤ (max ‖c₁‖ ‖c₂‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (le_max_left _ _) 2
    have m2 : ‖c₂‖ ^ 2 ≤ (max ‖c₁‖ ‖c₂‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) 2
    nlinarith [mul_le_mul_of_nonneg_right m1 hw, mul_le_mul_of_nonneg_right m2 hu]
  · rw [star_smul, smul_dotProduct, dotProduct_smul, o1]; simp
  · rw [star_smul, smul_dotProduct, dotProduct_smul, o2]; simp

end N2

/-! ### The standing hypotheses and the integrands -/

section Integrals

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} {a : ℕ → ℝ} {aT ν : ℝ}
  {α : G.Ω 1 → ℂ} {κ δ : ℝ} {s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ}
  {φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ}
variable {κι : Type*} [Fintype κι] [DecidableEq κι]
  {Q : Matrix κι (G.Ω 1) ℂ} {P : Matrix κι κι ℂ}

/-- The standing hypotheses of I-4c: the data of (DG7) for every `x ≥ 0` (the decoupling vector
`s` with `|s_P| ≤ e^κ` and `M₁` large), the constraint field `φ₀` with `δ ≤ δ_*`, and the unit
lattice. -/
structure CovStanding (G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ) (a : ℕ → ℝ) (aT ν : ℝ)
    (α : G.Ω 1 → ℂ) (κ : ℝ) (s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ) (δ : ℝ)
    (φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) {κι : Type*} [Fintype κι] [DecidableEq κι]
    (Q : Matrix κι (G.Ω 1) ℂ) (P : Matrix κι κι ℂ) : Prop where
  fam : ∀ x, 0 ≤ x → XData G a aT ν x α κ s
  field : IsConstraintField G δ φ
  nonneg : 0 ≤ δ
  small : δ ^ 2 * smallConstX d L κ ≤ 1 / 4
  unit : IsUnitLattice G Q P

/-- The constant `B₄ = √(B₄²)` of I-4c (ii). -/
noncomputable def covB4 (d L : ℕ) (ak κ : ℝ) : ℝ := Real.sqrt (covBsq d L ak κ)

theorem covB4_nonneg (d L : ℕ) (ak κ : ℝ) : 0 ≤ covB4 d L ak κ := Real.sqrt_nonneg _

theorem covB4_sq (d L : ℕ) (ak κ : ℝ) : covB4 d L ak κ ^ 2 = covBsq d L ak κ :=
  Real.sq_sqrt (covBsq_nonneg d L ak κ)

theorem CovStanding.hak (H : CovStanding G a aT ν α κ s δ φ Q P) : 0 < a k := by
  have D := H.fam 0 le_rfl
  have := D.st.ha k D.st.hk le_rfl
  linarith [this.1]

theorem CovStanding.hakx (H : CovStanding G a aT ν α κ s δ φ Q P) {x : ℝ} (hx : 0 ≤ x) :
    0 < a k + x := by
  have := H.hak
  linarith

theorem CovStanding.hb (H : CovStanding G a aT ν α κ s δ φ Q P) : 0 ≤ aT / (L : ℝ) ^ 2 := by
  have D := H.fam 0 le_rfl
  have := D.st.haT1
  positivity

/-- **I-4c (ii)**, matrix entries and operator form: `‖C_x(s) - A_{k,x}‖ ≤ B₄ (a_k + x)⁻²`. -/
theorem CovStanding.sub_le (H : CovStanding G a aT ν α κ s δ φ Q P) {x : ℝ} (hx : 0 ≤ x)
    (f : κι × Fin N → ℂ) :
    Green.sqNorm ((decCov G a aT x ν α s φ Q P -
        covA (a k) (aT / (L : ℝ) ^ 2) x (liftOp N P)) *ᵥ f) ≤
      (covB4 d L (a k) κ * ((a k + x)⁻¹) ^ 2) ^ 2 * Green.sqNorm f := by
  have h := decCov_sub_le (H.fam x hx) H.field H.nonneg H.small H.unit f
  calc _ ≤ covBsq d L (a k) κ * ((a k + x)⁻¹) ^ 4 * Green.sqNorm f := h
    _ = _ := by rw [mul_pow, covB4_sq]; ring

theorem CovStanding.covA_le (H : CovStanding G a aT ν α κ s δ φ Q P) {x : ℝ} (hx : 0 ≤ x)
    (f : κι × Fin N → ℂ) :
    Green.sqNorm (covA (a k) (aT / (L : ℝ) ^ 2) x (liftOp N P) *ᵥ f) ≤
      ((a k + x)⁻¹) ^ 2 * Green.sqNorm f := by
  obtain ⟨hPh, hPi⟩ := liftOp_herm_idem (N := N) H.unit
  exact sqNorm_covA_le (H.hakx hx) H.hb hPh hPi f

theorem CovStanding.decCov_le (H : CovStanding G a aT ν α κ s δ φ Q P) {x : ℝ} (hx : 0 ≤ x)
    (f : κι × Fin N → ℂ) :
    Green.sqNorm (decCov G a aT x ν α s φ Q P *ᵥ f) ≤
      (((a k + x)⁻¹) + covB4 d L (a k) κ * ((a k + x)⁻¹) ^ 2) ^ 2 * Green.sqNorm f := by
  have h1 := H.covA_le hx f
  have h2 := H.sub_le hx f
  have hα : 0 ≤ (a k + x)⁻¹ := inv_nonneg.2 (H.hakx hx).le
  have hB := covB4_nonneg d L (a k) κ
  have hc : 0 ≤ (a k + x)⁻¹ + covB4 d L (a k) κ * ((a k + x)⁻¹) ^ 2 := by positivity
  rw [sqNorm_le_iff hc]
  rw [sqNorm_le_iff hα] at h1
  rw [sqNorm_le_iff (by positivity)] at h2
  have e : decCov G a aT x ν α s φ Q P *ᵥ f =
      covA (a k) (aT / (L : ℝ) ^ 2) x (liftOp N P) *ᵥ f +
        (decCov G a aT x ν α s φ Q P - covA (a k) (aT / (L : ℝ) ^ 2) x (liftOp N P)) *ᵥ f := by
    rw [Matrix.sub_mulVec]; abel
  rw [e]
  refine (n2_add_le _ _).trans ?_
  nlinarith

/-! ### The integrands and the integrals -/

/-- The integrand `x^{-1/2} C_x(s)` of `C^{1/2}`. -/
noncomputable def decSqrtInt (G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ) (a : ℕ → ℝ)
    (aT ν : ℝ) (α : G.Ω 1 → ℂ) (s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ)
    (φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) {κι : Type*} [Fintype κι] [DecidableEq κι]
    (Q : Matrix κι (G.Ω 1) ℂ) (P : Matrix κι κι ℂ) (x : ℝ) :
    Matrix (κι × Fin N) (κι × Fin N) ℂ :=
  ((x ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) • decCov G a aT x ν α s φ Q P

/-- **The square root** `C^{1/2}(s) = π⁻¹ ∫₀^∞ x^{-1/2} C_x(s) dx`. -/
noncomputable def decCovSqrt (G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ) (a : ℕ → ℝ)
    (aT ν : ℝ) (α : G.Ω 1 → ℂ) (s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ)
    (φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) {κι : Type*} [Fintype κι] [DecidableEq κι]
    (Q : Matrix κι (G.Ω 1) ℂ) (P : Matrix κι κι ℂ) :
    Matrix (κι × Fin N) (κι × Fin N) ℂ :=
  ((1 / π : ℝ) : ℂ) • intMat (volume.restrict (Ioi (0 : ℝ))) (decSqrtInt G a aT ν α s φ Q P)

/-- **The logarithm** `𝕃(s) = log a_k (1 - P) + log (a_k + b) P - ∫₀^∞ (C_x(s) - A_{k,x}) dx`. -/
noncomputable def decLog (G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ) (a : ℕ → ℝ)
    (aT ν : ℝ) (α : G.Ω 1 → ℂ) (s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ)
    (φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) {κι : Type*} [Fintype κι] [DecidableEq κι]
    (Q : Matrix κι (G.Ω 1) ℂ) (P : Matrix κι κι ℂ) :
    Matrix (κι × Fin N) (κι × Fin N) ℂ :=
  ((Real.log (a k) : ℝ) : ℂ) • (1 - liftOp N P) +
      ((Real.log (a k + aT / (L : ℝ) ^ 2) : ℝ) : ℂ) • liftOp N P -
    intMat (volume.restrict (Ioi (0 : ℝ)))
      (fun x => decCov G a aT x ν α s φ Q P - covA (a k) (aT / (L : ℝ) ^ 2) x (liftOp N P))

section Integrability

variable (H : CovStanding G a aT ν α κ s δ φ Q P)
include H

theorem entry_decCov_le {x : ℝ} (hx : 0 ≤ x) (p q : κι × Fin N) :
    ‖decCov G a aT x ν α s φ Q P p q‖ ≤
      (a k + x)⁻¹ + covB4 d L (a k) κ * ((a k + x)⁻¹) ^ 2 := by
  have hα : 0 ≤ (a k + x)⁻¹ := inv_nonneg.2 (H.hakx hx).le
  have hB := covB4_nonneg d L (a k) κ
  exact norm_entry_le _ (by positivity) (fun f => H.decCov_le hx f) p q

theorem entry_decCov_sub_le {x : ℝ} (hx : 0 ≤ x) (p q : κι × Fin N) :
    ‖(decCov G a aT x ν α s φ Q P - covA (a k) (aT / (L : ℝ) ^ 2) x (liftOp N P)) p q‖ ≤
      covB4 d L (a k) κ * ((a k + x)⁻¹) ^ 2 := by
  have hB := covB4_nonneg d L (a k) κ
  exact norm_entry_le _ (by positivity) (fun f => H.sub_le hx f) p q

theorem continuousOn_decCov_entry (p q : κι × Fin N) :
    ContinuousOn (fun x => decCov G a aT x ν α s φ Q P p q) (Ici 0) :=
  continuousOn_pi.1 (continuousOn_pi.1 (continuousOn_decCov H.fam H.field H.nonneg H.small) p) q

theorem integrable_decSqrtInt (p q : κι × Fin N) :
    Integrable (fun x => decSqrtInt G a aT ν α s φ Q P x p q) (volume.restrict (Ioi (0 : ℝ))) := by
  have hak := H.hak
  have hB := covB4_nonneg d L (a k) κ
  have hg : Integrable (fun x : ℝ => x ^ (-(1 / 2 : ℝ)) * (a k + x)⁻¹ +
      covB4 d L (a k) κ * (x ^ (-(1 / 2 : ℝ)) * ((a k + x)⁻¹) ^ 2)) (volume.restrict (Ioi 0)) :=
    (integrableOn_rpow_inv_add hak).add ((integrableOn_rpow_inv_add_sq hak).const_mul _)
  refine Integrable.mono' hg ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    unfold decSqrtInt
    simp only [Matrix.smul_apply, smul_eq_mul]
    refine ContinuousOn.mul ?_ ((continuousOn_decCov_entry H p q).mono Ioi_subset_Ici_self)
    refine Complex.continuous_ofReal.comp_continuousOn ?_
    exact fun x hx => (Real.continuousAt_rpow_const _ _ (Or.inl (mem_Ioi.mp hx).ne')).continuousWithinAt
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun x hx => ?_)
    have hx0 : 0 < x := mem_Ioi.mp hx
    have h3 : 0 < x ^ (-(1 / 2 : ℝ)) := rpow_pos_of_pos hx0 _
    unfold decSqrtInt
    simp only [Matrix.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg h3.le]
    have := entry_decCov_le H hx0.le p q
    calc x ^ (-(1 / 2 : ℝ)) * ‖decCov G a aT x ν α s φ Q P p q‖
        ≤ x ^ (-(1 / 2 : ℝ)) * ((a k + x)⁻¹ + covB4 d L (a k) κ * ((a k + x)⁻¹) ^ 2) :=
          mul_le_mul_of_nonneg_left this h3.le
      _ = _ := by ring

theorem integrable_decSub (p q : κι × Fin N) :
    Integrable (fun x => (decCov G a aT x ν α s φ Q P -
        covA (a k) (aT / (L : ℝ) ^ 2) x (liftOp N P)) p q) (volume.restrict (Ioi (0 : ℝ))) := by
  have hak := H.hak
  have hB := covB4_nonneg d L (a k) κ
  have hg : Integrable (fun x : ℝ => covB4 d L (a k) κ * ((a k + x)⁻¹) ^ 2)
      (volume.restrict (Ioi 0)) := (integrableOn_inv_add_sq hak).const_mul _
  refine Integrable.mono' hg ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    have h1 := continuousOn_decCov_entry H p q
    have h2 : ContinuousOn (fun x => covA (a k) (aT / (L : ℝ) ^ 2) x (liftOp N P) p q) (Ici 0) :=
      continuousOn_pi.1 (continuousOn_pi.1
        (continuousOn_covA H.hak H.hb (liftOp N P)) p) q
    exact (h1.sub h2).mono Ioi_subset_Ici_self
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun x hx => ?_)
    exact entry_decCov_sub_le H (mem_Ioi.mp hx).le p q

end Integrability

/-! ### The operator bounds -/

/-- The constant `B₅ = a_k^{-1/2} (1 + B₄ / a_k)` of I-4c (ii) (the shape of P3 (3.24)). -/
noncomputable def covB5 (d L : ℕ) (ak κ : ℝ) : ℝ :=
  (Real.sqrt ak)⁻¹ * (1 + covB4 d L ak κ / ak)

section Bounds

variable (H : CovStanding G a aT ν α κ s δ φ Q P)
include H

/-- The dominating function `x^{-1/2} (α + B₄ α²)`, `α = (a_k + x)⁻¹`. -/
noncomputable def sqrtDom (d L : ℕ) (ak κ : ℝ) (x : ℝ) : ℝ :=
  x ^ (-(1 / 2 : ℝ)) * (ak + x)⁻¹ + covB4 d L ak κ * (x ^ (-(1 / 2 : ℝ)) * ((ak + x)⁻¹) ^ 2)

omit H in
theorem integrable_sqrtDom {ak : ℝ} (hak : 0 < ak) (d L : ℕ) (κ : ℝ) :
    Integrable (sqrtDom d L ak κ) (volume.restrict (Ioi (0 : ℝ))) :=
  (integrableOn_rpow_inv_add hak).add ((integrableOn_rpow_inv_add_sq hak).const_mul _)

omit H in
theorem sqrtDom_nonneg (d L : ℕ) (ak κ : ℝ) {x : ℝ} (hx : 0 < x) (hak : 0 < ak) :
    0 ≤ sqrtDom d L ak κ x := by
  have h3 : 0 < x ^ (-(1 / 2 : ℝ)) := rpow_pos_of_pos hx _
  have := covB4_nonneg d L ak κ
  unfold sqrtDom
  have : 0 < ak + x := by linarith
  positivity

theorem decCovSqrt_bound (f : κι × Fin N → ℂ) :
    Green.sqNorm (decCovSqrt G a aT ν α s φ Q P *ᵥ f) ≤
      (covB5 d L (a k) κ) ^ 2 * Green.sqNorm f := by
  have hak := H.hak
  have hB := covB4_nonneg d L (a k) κ
  have hmain := sqNorm_intMat_le (volume.restrict (Ioi (0 : ℝ)))
    (decSqrtInt G a aT ν α s φ Q P) (integrable_decSqrtInt H) (sqrtDom d L (a k) κ)
    (integrable_sqrtDom hak d L κ)
    ((ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun x hx =>
      sqrtDom_nonneg d L (a k) κ (mem_Ioi.mp hx) hak))
    ((ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun x hx f => by
      have hx0 : 0 < x := mem_Ioi.mp hx
      have h1 := H.decCov_le hx0.le f
      have h3 : 0 < x ^ (-(1 / 2 : ℝ)) := rpow_pos_of_pos hx0 _
      unfold decSqrtInt
      rw [Matrix.smul_mulVec, sqNorm_smul, Complex.norm_real, Real.norm_of_nonneg h3.le]
      have e : sqrtDom d L (a k) κ x = x ^ (-(1 / 2 : ℝ)) *
          ((a k + x)⁻¹ + covB4 d L (a k) κ * ((a k + x)⁻¹) ^ 2) := by
        unfold sqrtDom; ring
      rw [e, mul_pow, mul_assoc]
      exact mul_le_mul_of_nonneg_left h1 (sq_nonneg _))) f
  set I := intMat (volume.restrict (Ioi (0 : ℝ))) (decSqrtInt G a aT ν α s φ Q P) with hI
  set Gi := ∫ x, sqrtDom d L (a k) κ x ∂(volume.restrict (Ioi (0 : ℝ))) with hGi
  have hGi0 : 0 ≤ Gi := integral_nonneg_of_ae
    ((ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun x hx =>
      sqrtDom_nonneg d L (a k) κ (mem_Ioi.mp hx) hak))
  have hGi1 : Gi ≤ π / Real.sqrt (a k) * (1 + covB4 d L (a k) κ / a k) := by
    have e : Gi = (∫ x in Ioi (0 : ℝ), x ^ (-(1 / 2 : ℝ)) * ((a k) + x)⁻¹) +
        covB4 d L (a k) κ * ∫ x in Ioi (0 : ℝ), x ^ (-(1 / 2 : ℝ)) * (((a k) + x)⁻¹) ^ 2 := by
      rw [hGi]
      unfold sqrtDom
      rw [integral_add (integrableOn_rpow_inv_add hak)
        ((integrableOn_rpow_inv_add_sq hak).const_mul _), integral_const_mul]
    rw [e, integral_rpow_inv_add hak]
    have := integral_rpow_inv_add_sq_le hak
    have h2 := mul_le_mul_of_nonneg_left this hB
    have : π / Real.sqrt (a k) * (1 + covB4 d L (a k) κ / a k) =
        π / Real.sqrt (a k) + covB4 d L (a k) κ * ((a k)⁻¹ * (π / Real.sqrt (a k))) := by
      field_simp
    rw [this]
    linarith
  have hpi : 0 < π := Real.pi_pos
  have hB5 : (1 / π) * Gi ≤ covB5 d L (a k) κ := by
    unfold covB5
    calc (1 / π) * Gi ≤ (1 / π) * (π / Real.sqrt (a k) * (1 + covB4 d L (a k) κ / a k)) :=
          mul_le_mul_of_nonneg_left hGi1 (by positivity)
      _ = _ := by field_simp
  unfold decCovSqrt
  rw [Matrix.smul_mulVec, sqNorm_smul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have h0 : 0 ≤ (1 / π) * Gi := by positivity
  have h2 : ((1 / π) * Gi) ^ 2 ≤ (covB5 d L (a k) κ) ^ 2 := pow_le_pow_left₀ h0 hB5 2
  have hs0 := sqNorm_nonneg' f
  calc (1 / π) ^ 2 * Green.sqNorm (I *ᵥ f) ≤ (1 / π) ^ 2 * (Gi ^ 2 * Green.sqNorm f) :=
        mul_le_mul_of_nonneg_left hmain (by positivity)
    _ = ((1 / π) * Gi) ^ 2 * Green.sqNorm f := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right h2 hs0

/-- The constant of the logarithm: `max |log a_k| |log (a_k + b)| + B₄ / a_k`. -/
noncomputable def covBLog (d L : ℕ) (ak b κ : ℝ) : ℝ :=
  max |Real.log ak| |Real.log (ak + b)| + covB4 d L ak κ / ak

theorem decLog_bound (f : κι × Fin N → ℂ) :
    Green.sqNorm (decLog G a aT ν α s φ Q P *ᵥ f) ≤
      (covBLog d L (a k) (aT / (L : ℝ) ^ 2) κ) ^ 2 * Green.sqNorm f := by
  have hak := H.hak
  have hB := covB4_nonneg d L (a k) κ
  obtain ⟨hPh, hPi⟩ := liftOp_herm_idem (N := N) H.unit
  set μ := volume.restrict (Ioi (0 : ℝ)) with hμ
  set Mx := max |Real.log (a k)| |Real.log (a k + aT / (L : ℝ) ^ 2)| with hMx
  have hbase := sqNorm_twoProj_le hPh hPi ((Real.log (a k) : ℝ) : ℂ)
    ((Real.log (a k + aT / (L : ℝ) ^ 2) : ℝ) : ℂ) f
  simp only [Complex.norm_real, Real.norm_eq_abs] at hbase
  have hint := sqNorm_intMat_le μ
    (fun x => decCov G a aT x ν α s φ Q P - covA (a k) (aT / (L : ℝ) ^ 2) x (liftOp N P))
    (integrable_decSub H) (fun x => covB4 d L (a k) κ * ((a k + x)⁻¹) ^ 2)
    ((integrableOn_inv_add_sq hak).const_mul _)
    ((ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun x hx => by
      have : 0 < a k + x := by have := mem_Ioi.mp hx; linarith
      positivity))
    ((ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun x hx f =>
      H.sub_le (mem_Ioi.mp hx).le f)) f
  have hI : ∫ x, covB4 d L (a k) κ * ((a k + x)⁻¹) ^ 2 ∂μ = covB4 d L (a k) κ / a k := by
    rw [integral_const_mul, hμ, integral_inv_add_sq hak]
    field_simp
  rw [hI] at hint
  have hMx0 : 0 ≤ Mx := le_trans (abs_nonneg _) (le_max_left _ _)
  have hBa : 0 ≤ covB4 d L (a k) κ / a k := by positivity
  rw [sqNorm_le_iff hMx0] at hbase
  rw [sqNorm_le_iff hBa] at hint
  unfold decLog
  refine (sqNorm_le_iff (by unfold covBLog; positivity)).2 ?_
  rw [Matrix.sub_mulVec]
  refine (n2_sub_le _ _).trans ?_
  unfold covBLog
  nlinarith [n2_nonneg f]

end Bounds

end Integrals

end Balaban.Localization
