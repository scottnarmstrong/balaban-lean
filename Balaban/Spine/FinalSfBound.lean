/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.FinalSfMeas
public import Balaban.Spine.InheritedBound
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Boundedness and integrability of the small-field factor on the whole torus

A6-3 (a), item 1. -/

@[expose] public section

open MeasureTheory Balaban Balaban.Multiscale Balaban.Background Balaban.LargeField
  Balaban.LargeField.Def7 Balaban.LargeField.Def7v2 Balaban.SmallField Balaban.SmallField.Def6
  Balaban.SmallField.Def6v2 Balaban.Localization

namespace Balaban.RootFSpine

section Generic

/-- A bounded Borel function on a finite product of Euclidean spaces, supported in a bounded set,
is integrable. -/
theorem integrable_of_bdd_support {ι : Type*} [Fintype ι] {N : ℕ}
    {f : (ι → EuclideanSpace ℝ (Fin N)) → ℂ} (hf : Measurable f) (r M : ℝ)
    (hsupp : ∀ ψ, f ψ ≠ 0 → ∀ b, ‖ψ b‖ ≤ r) (hb : ∀ ψ, ‖f ψ‖ ≤ M) : Integrable f := by
  classical
  set K : Set (ι → EuclideanSpace ℝ (Fin N)) := Set.pi Set.univ fun _ => Metric.closedBall 0 r
    with hK
  have hKc : IsCompact K := isCompact_univ_pi fun _ => isCompact_closedBall _ _
  have hKm : volume K < ⊤ := hKc.measure_lt_top
  have hfK : IntegrableOn f K := by
    refine Measure.integrableOn_of_bounded (M := M) hKm.ne hf.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall hb
  refine (integrableOn_iff_integrable_of_support_subset ?_).1 hfK
  intro ψ hψ
  simp only [Function.mem_support] at hψ
  intro b _
  exact mem_closedBall_zero_iff.2 (hsupp ψ hψ b)

/-- The modulus of a finite sum over a finite index set is bounded by a nonnegative bound summed
over a finite superset. -/
theorem norm_finsum_mem_le {ι : Type*} {s : Set ι} (hs : s.Finite) {F : ι → ℂ} {b : ι → ℝ}
    (hb : ∀ i ∈ s, ‖F i‖ ≤ b i) (b0 : ∀ i, 0 ≤ b i) (T : Finset ι) (hsT : ∀ i ∈ s, i ∈ T) :
    ‖∑ᶠ i ∈ s, F i‖ ≤ ∑ i ∈ T, b i := by
  classical
  rw [finsum_mem_eq_finite_toFinset_sum _ hs]
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_sum fun i hi => hb i (hs.mem_toFinset.1 hi)).trans ?_
  exact Finset.sum_le_sum_of_subset_of_nonneg (fun i hi => hsT i (hs.mem_toFinset.1 hi))
    fun i _ _ => b0 i

section Corr

variable {d L N₁ m₁ k N : ℕ}

/-- `|v_i| ≤ rn v`. -/
theorem abs_le_rn (v : Fin N → ℝ) (i : Fin N) : |v i| ≤ rn v := by
  unfold rn
  refine Real.abs_le_sqrt ?_
  exact Finset.single_le_sum (f := fun i => v i ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ i)

/-- The bilinear square of a real vector of norm at most `2` has modulus at most `4`. -/
theorem norm_dot_real_self (v : Fin N → ℝ) (hv : rn v ≤ 2) :
    ‖dot (fun i => (v i : ℂ)) (fun i => (v i : ℂ))‖ ≤ 4 := by
  have h1 : dot (fun i => (v i : ℂ)) (fun i => (v i : ℂ)) = ((∑ i, v i ^ 2 : ℝ) : ℂ) := by
    unfold dot; push_cast; exact Finset.sum_congr rfl fun i _ => by ring
  rw [h1, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _),
    ← rn_sq]
  have := rn_nonneg v
  nlinarith

/-- The pairing of a fixed vector with the unit direction of a real vector. -/
theorem norm_dot_unitDir (h : Fin N → ℝ) (v : Fin N → ℝ) (hpos : 0 < rn v) :
    ‖dot (fun i => (h i : ℂ)) (unitDirC (fun i => (v i : ℂ)))‖ ≤ ∑ i, |h i| := by
  rw [unitDirC_real v hpos]
  unfold dot
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_div,
    abs_of_pos hpos]
  have : |v i| / rn v ≤ 1 := (div_le_one hpos).2 (abs_le_rn v i)
  nlinarith [abs_nonneg (h i)]

/-- **A bound for the pair term at real fields of norm in `(0, 2]`.** -/
theorem norm_corrPair_le {c₁ c₂ : ℂ} {νj : ℝ} {ψ : Def6.Fld d L N₁ m₁ k N} {h : Fin N → ℝ}
    {y x : Localization.CTorus d L N₁ m₁ k} {vy vx : Fin N → ℝ}
    (hy : ψ y = fun i => (vy i : ℂ)) (hx : ψ x = fun i => (vx i : ℂ))
    (hy0 : 0 < rn vy) (hx0 : 0 < rn vx) (hy2 : rn vy ≤ 2) (hx2 : rn vx ≤ 2) :
    ‖corrPair c₁ c₂ νj ψ (fun i => (h i : ℂ)) y x‖ ≤
      4 * ‖c₁‖ + ‖c₂‖ * |νj| * (2 * ∑ i, |h i|) := by
  unfold corrPair
  rw [hx, hy]
  have a1 := norm_dot_real_self vx hx2
  have a2 := norm_dot_real_self vy hy2
  have b1 := norm_dot_unitDir h vx hx0
  have b2 := norm_dot_unitDir h vy hy0
  refine (norm_add_le _ _).trans ?_
  have e1 : ‖1 / 2 * c₁ * (dot (fun i => (vx i : ℂ)) (fun i => (vx i : ℂ)) -
      dot (fun i => (vy i : ℂ)) (fun i => (vy i : ℂ)))‖ ≤ 4 * ‖c₁‖ := by
    rw [norm_mul]
    have : ‖(1 / 2 : ℂ) * c₁‖ = ‖c₁‖ / 2 := by
      rw [norm_mul]; simp; ring
    rw [this]
    have := (norm_sub_le _ _).trans (add_le_add a1 a2)
    nlinarith [norm_nonneg c₁]
  have e2 : ‖c₂ * ((νj : ℂ) * (dot (fun i => (h i : ℂ)) (unitDirC (fun i => (vx i : ℂ))) -
      dot (fun i => (h i : ℂ)) (unitDirC (fun i => (vy i : ℂ)))))‖ ≤
      ‖c₂‖ * |νj| * (2 * ∑ i, |h i|) := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_assoc]
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (abs_nonneg _))
      (norm_nonneg _)
    exact (norm_sub_le _ _).trans (by linarith)
  linarith

end Corr

end Generic

section Ctx

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N m₁ j : ℕ} {ϱ : ℝ} (C : SFCtx S n R M K N (j + 1) m₁ ϱ)
  (hv : EuclideanSpace ℝ (Fin N)) (vc : CorrCoef S.d)
  {P6 : Def6.Consts} {k0 : ℕ} (hm0 : P6.m₀ = C.m₀)
  (hTm : SFTermClauses P6 (sfDom P6 k0 C.sf C.N₁) (C.sf.Tm C.N₁))
  (hdomJ : ∀ ψk ∈ Asupp C hv, ∀ jj, 1 ≤ jj → jj ≤ j + 1 → ∀ X, Def6.IsPolyDom C.m₀ jj X →
    (sfDom P6 k0 C.sf C.N₁).dom jj ((C.sf.Tm C.N₁).gs jj X)
      (C.psiJ (Set.univ : Set (Torus S.d (n (j + 1)))) ψk hv jj) (Def6.constFld (hC hv)))

include hm0 hTm hdomJ in
/-- The localized terms `ℰ^{(j')}` of the whole torus are bounded on the support. -/
theorem exists_bound_Eterms {jj : ℕ} (hj1 : 1 ≤ jj) (hj : jj ≤ j + 1) :
    ∃ B : ℝ, ∀ ψk ∈ Asupp C hv,
      ‖∑ y ∈ C.alignedIn jj (Set.univ : Set (Torus S.d (n (j + 1)))),
        ∑ᶠ X ∈ {X : Set (Localization.CTorus S.d S.L C.N₁ m₁ (j + 1)) |
          Def6.IsPolyDom C.m₀ jj X ∧ y ∈ X ∧
            X ⊆ C.sset (thickY R (Set.univ : Set (Torus S.d (n (j + 1)))))},
          (C.sf.Tm C.N₁).E jj y X (C.psiJ (Set.univ : Set (Torus S.d (n (j + 1)))) ψk hv jj)
            (Def6.constFld (hC hv))‖ ≤ B := by
  classical
  set Fp := (Set.toFinite {X : Set (Localization.CTorus S.d S.L C.N₁ m₁ (j + 1)) |
    Def6.IsPolyDom C.m₀ jj X}).toFinset with hFp
  refine ⟨∑ y ∈ C.alignedIn jj (Set.univ : Set (Torus S.d (n (j + 1)))),
    ∑ X ∈ Fp, |P6.E₀ * Real.exp (-P6.κ * sizeJ P6.m₀ jj X)|, fun ψk hψ => ?_⟩
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun y _ => ?_)
  refine norm_finsum_mem_le (Set.toFinite _)
    (b := fun X => |P6.E₀ * Real.exp (-P6.κ * sizeJ P6.m₀ jj X)|) ?_ (fun _ => abs_nonneg _) Fp ?_
  · intro X hX
    obtain ⟨hXp, hyX, -⟩ := hX
    have hXp' : Def6.IsPolyDom P6.m₀ jj X := by rw [hm0]; exact hXp
    exact (hTm.boundE jj hj1 hj y X hXp' hyX _ _ (hdomJ ψk hψ jj hj1 hj X hXp)).trans
      (le_abs_self _)
  · intro X hX
    exact (Set.Finite.mem_toFinset _).2 hX.1

variable (hpsiR : ∀ ψk ∈ Asupp C hv, ∀ jj, 1 ≤ jj → jj ≤ j + 1 →
    ∀ x : Localization.CTorus S.d S.L C.N₁ m₁ (j + 1), ∃ v : Fin N → ℝ,
      (∀ i, C.psiJ (Set.univ : Set (Torus S.d (n (j + 1)))) ψk hv jj x i = (v i : ℂ)) ∧
        0 < rn v ∧ rn v ≤ 2)

include hpsiR in
/-- The correction `corrSum` of P5 (1.8) is bounded on the support. -/
theorem exists_bound_corrSum {jj : ℕ} (hj1 : 1 ≤ jj) (hj : jj ≤ j + 1) :
    ∃ B : ℝ, ∀ ψk ∈ Asupp C hv,
      ‖corrSum (fun y x => vc.v1 jj (unlift jj (x - y))) (fun y x => vc.v2 jj (unlift jj (x - y)))
        (nuIdeal S.L (j + 1) (C.sf.ν (j + 1)) jj)
        (C.alignedIn jj (Set.univ : Set (Torus S.d (n (j + 1)))))
        (C.alignedIn jj (thickY R (Set.univ : Set (Torus S.d (n (j + 1))))))
        (C.psiJ (Set.univ : Set (Torus S.d (n (j + 1)))) ψk hv jj) (hC hv)‖ ≤ B := by
  classical
  refine ⟨∑ y ∈ C.alignedIn jj (Set.univ : Set (Torus S.d (n (j + 1)))),
    ∑ x ∈ C.alignedIn jj (thickY R (Set.univ : Set (Torus S.d (n (j + 1))))),
      (4 * ‖vc.v1 jj (unlift jj (x - y))‖ + ‖vc.v2 jj (unlift jj (x - y))‖ *
        |nuIdeal S.L (j + 1) (C.sf.ν (j + 1)) jj| * (2 * ∑ i, |hv i|)), fun ψk hψ => ?_⟩
  unfold corrSum
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun y _ => ?_)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => ?_)
  obtain ⟨vy, hvy, hy0, hy2⟩ := hpsiR ψk hψ jj hj1 hj y
  obtain ⟨vx, hvx, hx0, hx2⟩ := hpsiR ψk hψ jj hj1 hj x
  exact norm_corrPair_le (h := fun i => hv i) (funext hvy) (funext hvx) hy0 hx0 hy2 hx2

end Ctx

end Balaban.RootFSpine
