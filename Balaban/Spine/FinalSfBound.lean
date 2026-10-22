/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.FinalSfMeas
public import Balaban.Spine.InheritedBound
public import Balaban.LargeField.R.SmallFactorAction
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Boundedness and integrability of the small-field factor of a cut

A6-3 (a), item 1, and its cut version (A6-4, `CutSfDomInput`): `sfFactor2 C vc Y` is bounded when,
on the support of `χ_k(Y)`, replacement fields equal to the inherited field on `Y^≈` (resp. to
the lift of the block field on `Y`) lie in the domains of the terms, the inherited field is real
with norm in `(0, 2]` on `Y^≈` and the real background is a unit field on the sites of `Y`
(`exists_bound_sfFactor2_of_dom`).  For the whole torus the replacement fields are the fields
themselves (`exists_bound_sfFactor2`, `measInt_sfFactor2_univ_of_dom`). -/

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

/-- The bilinear square of a real vector of positive norm is in the slit plane. -/
theorem dot_real_mem_slitPlane (v : Fin N → ℝ) (hpos : 0 < rn v) :
    dot (fun i => (v i : ℂ)) (fun i => (v i : ℂ)) ∈ Complex.slitPlane := by
  have h1 : dot (fun i => (v i : ℂ)) (fun i => (v i : ℂ)) = ((∑ i, v i ^ 2 : ℝ) : ℂ) := by
    unfold dot; push_cast; exact Finset.sum_congr rfl fun i _ => by ring
  rw [h1]
  refine Or.inl ?_
  rw [Complex.ofReal_re, ← rn_sq]
  positivity

end Corr

/-- `Function.Injective` of the identification of tori of equal side. -/
theorem torusCast_injective' {d a b : ℕ} (h : a = b) :
    Function.Injective (torusCast (d := d) h) := by
  subst h; exact fun _ _ hxy => hxy

theorem torusCast_surjective' {d a b : ℕ} (h : a = b) :
    Function.Surjective (torusCast (d := d) h) := by
  subst h; exact fun y => ⟨y, rfl⟩

/-- A finite sum of nonnegative terms over the image of an injective map is at most the full sum. -/
theorem sum_comp_injective_le {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β] {φ : α → β}
    (hφ : Function.Injective φ) (F : β → ℝ) (hF : ∀ b, 0 ≤ F b) :
    ∑ a, F (φ a) ≤ ∑ b, F b := by
  rw [← Finset.sum_image (f := F) (s := Finset.univ) (g := φ) (fun a _ b _ h => hφ h)]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun b _ _ => hF b

end Generic

section Ctx

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N m₁ j : ℕ} {ϱ : ℝ} (C : SFCtx S n R M K N (j + 1) m₁ ϱ)
  (hv : EuclideanSpace ℝ (Fin N)) (vc : CorrCoef S.d)
  {P6 : Def6.Consts} {k0 : ℕ} (hm0 : P6.m₀ = C.m₀)
  (hTm : SFTermClauses P6 (sfDom P6 k0 C.sf C.N₁) (C.sf.Tm C.N₁))
  (Y : Set (Torus S.d (n (j + 1))))
  (hrepJ : ∀ jj, 1 ≤ jj → jj ≤ j + 1 → ∀ ψk ∈ AsuppY C hv Y,
    ∃ Ψe : Def6.Fld S.d S.L C.N₁ m₁ (j + 1) N,
      (∀ x ∈ C.sset (thickY R Y), Ψe x = C.psiJ Y ψk hv jj x) ∧
      ∀ X, Def6.IsPolyDom C.m₀ jj X → X ⊆ C.sset (thickY R Y) →
        (sfDom P6 k0 C.sf C.N₁).dom jj ((C.sf.Tm C.N₁).gs jj X) Ψe (Def6.constFld (hC hv)))

include hm0 hTm hrepJ in
/-- The localized terms `ℰ^{(j')}` of the cut are bounded on the support. -/
theorem exists_bound_Eterms {jj : ℕ} (hj1 : 1 ≤ jj) (hj : jj ≤ j + 1) :
    ∃ B : ℝ, ∀ ψk ∈ AsuppY C hv Y,
      ‖∑ y ∈ C.alignedIn jj Y,
        ∑ᶠ X ∈ {X : Set (Localization.CTorus S.d S.L C.N₁ m₁ (j + 1)) |
          Def6.IsPolyDom C.m₀ jj X ∧ y ∈ X ∧ X ⊆ C.sset (thickY R Y)},
          (C.sf.Tm C.N₁).E jj y X (C.psiJ Y ψk hv jj) (Def6.constFld (hC hv))‖ ≤ B := by
  classical
  set Fp := (Set.toFinite {X : Set (Localization.CTorus S.d S.L C.N₁ m₁ (j + 1)) |
    Def6.IsPolyDom C.m₀ jj X}).toFinset with hFp
  refine ⟨∑ y ∈ C.alignedIn jj Y,
    ∑ X ∈ Fp, |P6.E₀ * Real.exp (-P6.κ * sizeJ P6.m₀ jj X)|, fun ψk hψ => ?_⟩
  obtain ⟨Ψe, hag, hdom⟩ := hrepJ jj hj1 hj ψk hψ
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun y _ => ?_)
  refine norm_finsum_mem_le (Set.toFinite _)
    (b := fun X => |P6.E₀ * Real.exp (-P6.κ * sizeJ P6.m₀ jj X)|) ?_ (fun _ => abs_nonneg _) Fp ?_
  · intro X hX
    obtain ⟨hXp, hyX, hXY⟩ := hX
    have hXp' : Def6.IsPolyDom P6.m₀ jj X := by rw [hm0]; exact hXp
    rw [hTm.localE jj y X _ Ψe _ _ fun x hx => ⟨(hag x (hXY hx)).symm, rfl⟩]
    exact (hTm.boundE jj hj1 hj y X hXp' hyX _ _ (hdom X hXp hXY)).trans (le_abs_self _)
  · intro X hX
    exact (Set.Finite.mem_toFinset _).2 hX.1

/-- The source `g` of the unit `ℓ¹` ball, read on the Def-6 torus, has `Def6.l1 < 1`. -/
theorem l1_sfG_lt_one (g : GIdx S n M K N → ℂ) (hg : g ∈ LargeField.l1Ball (GIdx S n M K N)) :
    Def6.l1 (sfG C.geo C.hnn C.hkK C.hT g) < 1 := by
  classical
  have hinj : Function.Injective (fun x : Localization.CTorus S.d S.L C.N₁ m₁ (j + 1) =>
      bgToFine C.geo C.hnn C.hkK (sfToBg C.geo C.hT x)) :=
    (torusCast_injective' _).comp (torusCast_injective' _)
  have hsum : ∑ y : Torus S.d (M * n K * S.L ^ K), ∑ i : Fin N, ‖g (y, i)‖ < 1 := by
    have := hg
    unfold LargeField.l1Ball at this
    simp only [Set.mem_ofPred_eq] at this
    rwa [Fintype.sum_prod_type] at this
  calc Def6.l1 (sfG C.geo C.hnn C.hkK C.hT g)
      ≤ ∑ x : Localization.CTorus S.d S.L C.N₁ m₁ (j + 1), ∑ i : Fin N,
          ‖g (bgToFine C.geo C.hnn C.hkK (sfToBg C.geo C.hT x), i)‖ :=
        Finset.sum_le_sum fun x _ => vn_le_sum_norm _
    _ ≤ ∑ y : Torus S.d (M * n K * S.L ^ K), ∑ i : Fin N, ‖g (y, i)‖ :=
        sum_comp_injective_le hinj (fun y => ∑ i : Fin N, ‖g (y, i)‖)
          (fun _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
    _ < 1 := hsum

include hm0 hTm hrepJ in
/-- The aggregated terms `ℳ^{(j')}` of the cut are bounded on the support. -/
theorem exists_bound_MresJ (g : GIdx S n M K N → ℂ)
    (hg : Def6.l1 (sfG C.geo C.hnn C.hkK C.hT g) < 1) {jj : ℕ} (hj1 : 1 ≤ jj) (hj : jj ≤ j + 1) :
    ∃ B : ℝ, ∀ ψk ∈ AsuppY C hv Y, ∀ (x : Localization.CTorus S.d S.L C.N₁ m₁ (j + 1)) (i : Fin N),
      ‖C.MresJ Y ψk hv g jj x i‖ ≤ B := by
  classical
  set Fp := (Set.toFinite {X : Set (Localization.CTorus S.d S.L C.N₁ m₁ (j + 1)) |
    Def6.IsPolyDom C.m₀ jj X}).toFinset with hFp
  refine ⟨∑ X ∈ Fp, |P6.c₉ * ((S.L : ℝ) ^ jj)⁻¹ ^ (((S.d : ℝ) - 2) / 2 + P6.γ - P6.α₁) *
      Real.exp (-P6.κ * sizeJ P6.m₀ jj X)|, fun ψk hψ x i => ?_⟩
  obtain ⟨Ψe, hag, hdom⟩ := hrepJ jj hj1 hj ψk hψ
  unfold SFCtx.MresJ
  have hcoord : (∑ᶠ X ∈ {X : Set (Localization.CTorus S.d S.L C.N₁ m₁ (j + 1)) |
        Def6.IsPolyDom C.m₀ jj X ∧ x ∈ X ∧ X ⊆ C.sset (thickY R Y)},
      (C.sf.Tm C.N₁).M jj x X (C.psiJ Y ψk hv jj)
        (Def6.constFld (hC hv)) (sfG C.geo C.hnn C.hkK C.hT g)) i =
      ∑ᶠ X ∈ {X : Set (Localization.CTorus S.d S.L C.N₁ m₁ (j + 1)) |
        Def6.IsPolyDom C.m₀ jj X ∧ x ∈ X ∧ X ⊆ C.sset (thickY R Y)},
      (C.sf.Tm C.N₁).M jj x X (C.psiJ Y ψk hv jj)
        (Def6.constFld (hC hv)) (sfG C.geo C.hnn C.hkK C.hT g) i := by
    rw [finsum_mem_eq_finite_toFinset_sum _ (Set.toFinite _),
      finsum_mem_eq_finite_toFinset_sum _ (Set.toFinite _), Finset.sum_apply]
  rw [hcoord]
  refine norm_finsum_mem_le (Set.toFinite _)
    (b := fun X => |P6.c₉ * ((S.L : ℝ) ^ jj)⁻¹ ^ (((S.d : ℝ) - 2) / 2 + P6.γ - P6.α₁) *
      Real.exp (-P6.κ * sizeJ P6.m₀ jj X)|) ?_ (fun _ => abs_nonneg _) Fp ?_
  · intro X hX
    obtain ⟨hXp, hxX, hXY⟩ := hX
    have hXp' : Def6.IsPolyDom P6.m₀ jj X := by rw [hm0]; exact hXp
    rw [hTm.localM jj x X _ Ψe _ _ _ _ fun z hz => ⟨(hag z (hXY hz)).symm, rfl, rfl⟩]
    exact ((norm_le_vn _ i).trans
      (hTm.boundM jj hj1 hj x X hXp' hxX _ _ _ (hdom X hXp hXY) hg).le).trans
      (le_abs_self _)
  · intro X hX
    exact (Set.Finite.mem_toFinset _).2 hX.1

/-- A source of the unit `ℓ¹` ball has all entries of modulus `< 1`. -/
theorem norm_entry_le_one (g : GIdx S n M K N → ℂ) (hg : g ∈ LargeField.l1Ball (GIdx S n M K N))
    (y : Torus S.d (M * n K * S.L ^ K)) (i : Fin N) : ‖g (y, i)‖ ≤ 1 := by
  classical
  have h1 : ∑ p : GIdx S n M K N, ‖g p‖ < 1 := by
    have := hg
    unfold LargeField.l1Ball at this
    rwa [Set.mem_ofPred_eq] at this
  exact ((Finset.single_le_sum (f := fun p : GIdx S n M K N => ‖g p‖) (fun _ _ => norm_nonneg _)
    (Finset.mem_univ (y, i))).trans h1.le)

include hm0 hTm hrepJ in
/-- **The source term `ℱ_k` of the cut is bounded on the support.** -/
theorem exists_bound_Fres (g : GIdx S n M K N → ℂ)
    (hgl : g ∈ LargeField.l1Ball (GIdx S n M K N))
    (hphi : ∀ ψk ∈ AsuppY C hv Y, ∀ z ∈ C.bgSet Y, ∀ i, |(C.phiBar Y ψk hv z) i| ≤ 1) :
    ∃ B : ℝ, ∀ ψk ∈ AsuppY C hv Y, ‖C.Fres Y ψk hv g‖ ≤ B := by
  classical
  have hg := l1_sfG_lt_one C g hgl
  have hM : ∀ jj ∈ Finset.Icc 1 (j + 1), ∃ B : ℝ, ∀ ψk ∈ AsuppY C hv Y,
      ∀ (x : Localization.CTorus S.d S.L C.N₁ m₁ (j + 1)) (i : Fin N),
      ‖C.MresJ Y ψk hv g jj x i‖ ≤ B :=
    fun jj hjj => exists_bound_MresJ C hv hm0 hTm Y hrepJ g hg (Finset.mem_Icc.1 hjj).1
      (Finset.mem_Icc.1 hjj).2
  choose! BM hBM using hM
  refine ⟨(∑ x ∈ C.bgSet Y, ∑ _i : Fin N, (1 : ℝ)) +
    ∑ jj ∈ Finset.Icc 1 (j + 1), ∑ _x : Localization.CTorus S.d S.L C.N₁ m₁ (j + 1),
      ∑ _i : Fin N, |BM jj|, fun ψk hψ => ?_⟩
  unfold SFCtx.Fres
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x hx => ?_)
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have := norm_entry_le_one g hgl (bgToFine C.geo C.hnn C.hkK x) i
    have h2 := hphi ψk hψ x hx i
    nlinarith [norm_nonneg (g (bgToFine C.geo C.hnn C.hkK x, i)), abs_nonneg ((C.phiBar
      Y ψk hv x) i)]
  · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun jj hjj => ?_)
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => ?_)
    by_cases hx : x ∈ C.sset Y
    · simp only [hx, ↓reduceIte]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      rw [norm_mul]
      have h1 : ‖sfG C.geo C.hnn C.hkK C.hT g x i‖ ≤ 1 := by
        refine (norm_le_vn _ i).trans ?_
        refine le_trans ?_ hg.le
        exact Finset.single_le_sum (f := fun x => vn (sfG C.geo C.hnn C.hkK C.hT g x))
          (fun _ _ => vn_nonneg _) (Finset.mem_univ x)
      have h2 := hBM jj hjj ψk hψ x i
      nlinarith [norm_nonneg (sfG C.geo C.hnn C.hkK C.hT g x i),
        norm_nonneg (C.MresJ Y ψk hv g jj x i), le_abs_self (BM jj)]
    · simp only [hx, ↓reduceIte, norm_zero]
      exact Finset.sum_nonneg fun _ _ => abs_nonneg _

include hm0 in
/-- **The remainders `ℛ^{(k)}_n` of the cut are bounded on the support.** -/
theorem exists_bound_Rres (g : GIdx S n M K N → ℂ)
    (hg : Def6.l1 (sfG C.geo C.hnn C.hkK C.hT g) < 1) {fac : ℕ → ℝ}
    (hRt : RTermsH4 (ϱ := ϱ) P6 C.sf.β C.sf.ν C.sf.a C.N₁ (C.sf.Rt C.N₁) fac)
    (hrepR : ∀ ψk ∈ AsuppY C hv Y, ∃ Ψr : Def6.Fld S.d S.L C.N₁ m₁ (j + 1) N,
      (∀ x ∈ C.sset Y, Ψr x = sfLiftK C.geo C.hnn C.hkK C.hT ψk x) ∧
      Def6.XiDom (Def6.topGS S.d S.L C.N₁ m₁ (j + 1) ϱ)
        (Def6.aIdeal S.L (j + 1) (C.sf.a (j + 1)))
        (Def6.bgMass S.L (j + 1) (C.sf.β (j + 1)) (C.sf.ν (j + 1))) (j + 1)
        (P6.eps S.d S.L (j + 1)) Ψr (Def6.constFld (hC hv))) :
    ∃ B : ℝ, ∀ ψk ∈ AsuppY C hv Y, ‖C.Rres Y ψk hv g‖ ≤ B := by
  classical
  set Fp := (Set.toFinite {X : Set (Localization.CTorus S.d S.L C.N₁ m₁ (j + 1)) |
    Def6.IsPolyDom C.m₀ (j + 1) X}).toFinset with hFp
  refine ⟨∑ nn ∈ Finset.Icc 1 (C.m₀ + m₁), ∑ X ∈ Fp,
    |fac nn * (C.sf.β (j + 1))⁻¹ ^ (nn + 1) * Real.exp (-P6.κ * sizeJ P6.m₀ (j + 1) X)|,
    fun ψk hψ => ?_⟩
  obtain ⟨Ψr, hag, hdom⟩ := hrepR ψk hψ
  unfold SFCtx.Rres
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun nn hnn => ?_)
  have hnn' := Finset.mem_Icc.1 hnn
  refine norm_finsum_mem_le (Set.toFinite _)
    (b := fun X => |fac nn * (C.sf.β (j + 1))⁻¹ ^ (nn + 1) *
      Real.exp (-P6.κ * sizeJ P6.m₀ (j + 1) X)|) ?_ (fun _ => abs_nonneg _) Fp ?_
  · intro X hX
    obtain ⟨hXp, hXY⟩ := hX
    have hXp' : Def6.IsPolyDom P6.m₀ (j + 1) X := by rw [hm0]; exact hXp
    rw [hRt.loc nn X _ Ψr _ _ _ _ fun z hz => ⟨(hag z (hXY hz)).symm, rfl, rfl⟩]
    exact (hRt.bound nn hnn'.1 (by rw [hm0]; exact hnn'.2) X hXp' _ _ _ hdom
      (fun _ => Set.mem_univ _) hg).trans (le_abs_self _)
  · intro X hX
    exact (Set.Finite.mem_toFinset _).2 hX.1

/-- A finite sum of functions with bounds on a set has a bound on the set. -/
theorem exists_bound_sum' {α ι : Type*} {A : Set α} (T : Finset ι) {f : ι → α → ℂ}
    (h : ∀ i ∈ T, ∃ B : ℝ, ∀ a ∈ A, ‖f i a‖ ≤ B) :
    ∃ B : ℝ, ∀ a ∈ A, ‖∑ i ∈ T, f i a‖ ≤ B := by
  classical
  choose! B hB using h
  exact ⟨∑ i ∈ T, B i, fun a ha => (norm_sum_le _ _).trans
    (Finset.sum_le_sum fun i hi => hB i hi a ha)⟩

variable (hpsiR : ∀ ψk ∈ AsuppY C hv Y, ∀ jj, 1 ≤ jj → jj ≤ j + 1 →
    ∀ x ∈ C.sset (thickY R Y), ∃ v : Fin N → ℝ,
      (∀ i, C.psiJ Y ψk hv jj x i = (v i : ℂ)) ∧ 0 < rn v ∧ rn v ≤ 2)

include hpsiR in
/-- The correction `corrSum` of P5 (1.8) of the cut is bounded on the support. -/
theorem exists_bound_corrSum {jj : ℕ} (hj1 : 1 ≤ jj) (hj : jj ≤ j + 1) :
    ∃ B : ℝ, ∀ ψk ∈ AsuppY C hv Y,
      ‖corrSum (fun y x => vc.v1 jj (unlift jj (x - y))) (fun y x => vc.v2 jj (unlift jj (x - y)))
        (nuIdeal S.L (j + 1) (C.sf.ν (j + 1)) jj)
        (C.alignedIn jj Y) (C.alignedIn jj (thickY R Y))
        (C.psiJ Y ψk hv jj) (hC hv)‖ ≤ B := by
  classical
  refine ⟨∑ y ∈ C.alignedIn jj Y, ∑ x ∈ C.alignedIn jj (thickY R Y),
      (4 * ‖vc.v1 jj (unlift jj (x - y))‖ + ‖vc.v2 jj (unlift jj (x - y))‖ *
        |nuIdeal S.L (j + 1) (C.sf.ν (j + 1)) jj| * (2 * ∑ i, |hv i|)), fun ψk hψ => ?_⟩
  unfold corrSum
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun y hy => ?_)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x hx => ?_)
  obtain ⟨vy, hvy, hy0, hy2⟩ := hpsiR ψk hψ jj hj1 hj y
    (sset_subset_sset_thickY C Y (alignedIn_subset_sset C jj Y hy))
  obtain ⟨vx, hvx, hx0, hx2⟩ := hpsiR ψk hψ jj hj1 hj x (alignedIn_subset_sset C jj _ hx)
  exact norm_corrPair_le (h := fun i => hv i) (funext hvy) (funext hvx) hy0 hx0 hy2 hx2

include hm0 hTm hrepJ hpsiR in
/-- `ℰ_k` of the cut is bounded on the support. -/
theorem exists_bound_EresK2 :
    ∃ B : ℝ, ∀ ψk ∈ AsuppY C hv Y, ‖EresK2 C vc Y ψk hv‖ ≤ B := by
  unfold EresK2
  refine exists_bound_sum' _ fun jj hjj => ?_
  have hj1 := (Finset.mem_Icc.1 hjj).1
  have hj := (Finset.mem_Icc.1 hjj).2
  obtain ⟨B1, h1⟩ := exists_bound_Eterms C hv hm0 hTm Y hrepJ hj1 hj
  obtain ⟨B2, h2⟩ := exists_bound_corrSum C hv vc Y hpsiR hj1 hj
  refine ⟨B1 + B2, fun ψk hψ => ?_⟩
  unfold EresJ2
  exact (norm_sub_le _ _).trans (add_le_add (h1 ψk hψ) (h2 ψk hψ))

/-- The weights of the ideal flow are nonnegative. -/
theorem weights_nonneg
    (HB : BgHyp S.d S.L (j + 1) (minSep S.L C.geo.M1) C.weights (C.cs.muBg (j + 1)))
    (hL : 2 ≤ S.L) (n' : ℕ) : 0 ≤ C.weights n' := by
  have ha₁ : 0 < Def6.aIdeal S.L (j + 1) (C.sf.a (j + 1)) 1 :=
    lt_of_lt_of_le (by norm_num) (HB.weights 1 le_rfl (by omega)).1
  have hw : C.weights = compWeight S.L (Def6.aIdeal S.L (j + 1) (C.sf.a (j + 1)) 1) :=
    funext fun r => aIdeal_eq_compWeight hL (j + 1) (C.sf.a (j + 1)) r
  rw [hw]
  exact compWeight_nonneg hL ha₁ n'

/-- The single-scale action is nonnegative. -/
theorem actStar2_nonneg
    (HB : BgHyp S.d S.L (j + 1) (minSep S.L C.geo.M1) C.weights (C.cs.muBg (j + 1)))
    (hL : 2 ≤ S.L) (hact : 0 ≤ C.cs.muAct (j + 1)) (Y : Set (Torus S.d (n (j + 1))))
    (ψk : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N)) :
    0 ≤ actStar2 C Y ψk hv := by
  unfold actStar2
  exact add_nonneg (actionG_nonneg _ (weights_nonneg C HB hL) hact _ _ _ _)
    (mul_nonneg (by norm_num) (starBondE_nonneg _ _))

/-- `0 ≤ χ_k(Y) ≤ 1`. -/
theorem chiY_mem_Icc (Y : Set (Torus S.d (n (j + 1))))
    (ψk : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N)) :
    0 ≤ C.chiY Y ψk hv ∧ C.chiY Y ψk hv ≤ 1 := by
  unfold SFCtx.chiY cubeProd
  have h : ∀ y0 : Torus S.d (n (j + 1)), 0 ≤ chiKLong (M1 := C.geo.M1)
      (N₁ := C.geo.c * n (j + 1)) (L := S.L) (q := j + 1) (N := N) C.weights (C.cs.mu (j + 1))
      (C.cs.delta (j + 1)) (fun i => hv i) C.geo.c (n (j + 1)) (dirRadius R (j + 1)) y0
      (blockCfgOf C.geo C.hnn le_rfl C.hkK ψk) ∧ chiKLong (M1 := C.geo.M1)
      (N₁ := C.geo.c * n (j + 1)) (L := S.L) (q := j + 1) (N := N) C.weights (C.cs.mu (j + 1))
      (C.cs.delta (j + 1)) (fun i => hv i) C.geo.c (n (j + 1)) (dirRadius R (j + 1)) y0
      (blockCfgOf C.geo C.hnn le_rfl C.hkK ψk) ≤ 1 := by
    intro y0
    unfold chiKLong charFn
    by_cases hp : ChiKLongProp (N₁ := C.geo.c * n (j + 1)) (L := S.L) (M1 := C.geo.M1) (q := j + 1)
        C.weights (C.cs.mu (j + 1)) (C.cs.delta (j + 1)) (fun i => hv i) C.geo.c (n (j + 1))
        (dirRadius R (j + 1)) y0 (blockCfgOf C.geo C.hnn le_rfl C.hkK ψk)
    · simp [Set.indicator, hp]
    · simp [Set.indicator, hp]
  refine ⟨Finset.prod_nonneg fun y _ => (h y).1, ?_⟩
  exact Finset.prod_le_one₀ (fun y _ => (h y).1) fun y _ => (h y).2

include hm0 hTm hrepJ hpsiR in
/-- **`sfFactor2` of a cut is bounded** (A6-3 (a), item 1; A6-4): on the support the exponent has
real part at most the sum of the bounds of its terms (the action is nonnegative), and off the
support the factor is `0`. -/
theorem exists_bound_sfFactor2_of_dom (g : GIdx S n M K N → ℂ)
    (hgl : g ∈ LargeField.l1Ball (GIdx S n M K N))
    (HB : BgHyp S.d S.L (j + 1) (minSep S.L C.geo.M1) C.weights (C.cs.muBg (j + 1)))
    (hL : 2 ≤ S.L) (hact : 0 ≤ C.cs.muAct (j + 1)) (hβ : 0 ≤ C.sf.β (j + 1))
    (hphi : ∀ ψk ∈ AsuppY C hv Y, ∀ z ∈ C.bgSet Y, ∀ i, |(C.phiBar Y ψk hv z) i| ≤ 1)
    {fac : ℕ → ℝ} (hRt : RTermsH4 (ϱ := ϱ) P6 C.sf.β C.sf.ν C.sf.a C.N₁ (C.sf.Rt C.N₁) fac)
    (hrepR : ∀ ψk ∈ AsuppY C hv Y, ∃ Ψr : Def6.Fld S.d S.L C.N₁ m₁ (j + 1) N,
      (∀ x ∈ C.sset Y, Ψr x = sfLiftK C.geo C.hnn C.hkK C.hT ψk x) ∧
      Def6.XiDom (Def6.topGS S.d S.L C.N₁ m₁ (j + 1) ϱ)
        (Def6.aIdeal S.L (j + 1) (C.sf.a (j + 1)))
        (Def6.bgMass S.L (j + 1) (C.sf.β (j + 1)) (C.sf.ν (j + 1))) (j + 1)
        (P6.eps S.d S.L (j + 1)) Ψr (Def6.constFld (hC hv))) :
    ∃ Mb : ℝ, ∀ ψk : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N),
      ‖sfFactor2 C vc Y ψk hv g‖ ≤ Mb := by
  classical
  have hg := l1_sfG_lt_one C g hgl
  obtain ⟨BE, hBE⟩ := exists_bound_EresK2 C hv vc hm0 hTm Y hrepJ hpsiR
  obtain ⟨BF, hBF⟩ := exists_bound_Fres C hv hm0 hTm Y hrepJ g hgl hphi
  obtain ⟨BR, hBR⟩ := exists_bound_Rres C hv hm0 Y g hg hRt hrepR
  refine ⟨max 0 (Real.exp (BE + |C.sf.E C.N₁ * volK M Y| + BF + BR)), fun ψk => ?_⟩
  by_cases hψ : ψk ∈ AsuppY C hv Y
  · refine le_trans ?_ (le_max_right _ _)
    unfold sfFactor2
    rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs]
    have hchi := chiY_mem_Icc C hv Y ψk
    rw [abs_of_nonneg hchi.1]
    have hre : (Ares2 C vc Y ψk hv + C.Fres Y ψk hv g + C.Rres Y ψk hv g).re ≤
        BE + |C.sf.E C.N₁ * volK M Y| + BF + BR := by
      have hA0 := actStar2_nonneg C hv HB hL hact Y ψk
      have hb0 : 0 ≤ betaCanon S.d S.L (C.sf.β (j + 1)) (j + 1) 0 := by
        unfold betaCanon; exact div_nonneg hβ (by positivity)
      have e1 : (Ares2 C vc Y ψk hv).re =
          -(betaCanon S.d S.L (C.sf.β (j + 1)) (j + 1) 0 * actStar2 C Y ψk hv) +
          (EresK2 C vc Y ψk hv).re - C.sf.E C.N₁ * volK M Y := by
        unfold Ares2
        simp [Complex.sub_re, Complex.add_re, Complex.neg_re, Complex.mul_re]
      have h2 := (Complex.re_le_norm _).trans (hBE ψk hψ)
      have h3 := (Complex.re_le_norm _).trans (hBF ψk hψ)
      have h4 := (Complex.re_le_norm _).trans (hBR ψk hψ)
      simp only [Complex.add_re, e1]
      nlinarith [mul_nonneg hb0 hA0, neg_le_abs (C.sf.E C.N₁ * volK M Y)]
    calc _ ≤ 1 * Real.exp (Ares2 C vc Y ψk hv + C.Fres Y ψk hv g + C.Rres Y ψk hv g).re :=
          mul_le_mul_of_nonneg_right hchi.2 (Real.exp_pos _).le
      _ ≤ _ := by rw [one_mul]; exact Real.exp_le_exp.2 hre
  · refine le_trans ?_ (le_max_left _ _)
    have h0 : C.chiY Y ψk hv = 0 := by
      by_contra hne; exact hψ hne
    unfold sfFactor2
    rw [h0]; simp

include hm0 hTm in
/-- **`sfFactor2` of the whole torus is bounded** (A6-3 (a), item 1): `exists_bound_sfFactor2_of_dom`
with the fields themselves as replacement fields. -/
theorem exists_bound_sfFactor2
    (hdomJ : ∀ ψk ∈ Asupp C hv, ∀ jj, 1 ≤ jj → jj ≤ j + 1 → ∀ X, Def6.IsPolyDom C.m₀ jj X →
      (sfDom P6 k0 C.sf C.N₁).dom jj ((C.sf.Tm C.N₁).gs jj X)
        (C.psiJ (Set.univ : Set (Torus S.d (n (j + 1)))) ψk hv jj) (Def6.constFld (hC hv)))
    (hpsiR : ∀ ψk ∈ Asupp C hv, ∀ jj, 1 ≤ jj → jj ≤ j + 1 →
      ∀ x : Localization.CTorus S.d S.L C.N₁ m₁ (j + 1), ∃ v : Fin N → ℝ,
        (∀ i, C.psiJ (Set.univ : Set (Torus S.d (n (j + 1)))) ψk hv jj x i = (v i : ℂ)) ∧
          0 < rn v ∧ rn v ≤ 2)
    (g : GIdx S n M K N → ℂ)
    (hgl : g ∈ LargeField.l1Ball (GIdx S n M K N))
    (HB : BgHyp S.d S.L (j + 1) (minSep S.L C.geo.M1) C.weights (C.cs.muBg (j + 1)))
    (hL : 2 ≤ S.L) (hact : 0 ≤ C.cs.muAct (j + 1)) (hβ : 0 ≤ C.sf.β (j + 1))
    (hphi : ∀ ψk ∈ Asupp C hv, ∀ z i,
      |(C.phiBar (Set.univ : Set (Torus S.d (n (j + 1)))) ψk hv z) i| ≤ 1)
    {fac : ℕ → ℝ} (hRt : RTermsH4 (ϱ := ϱ) P6 C.sf.β C.sf.ν C.sf.a C.N₁ (C.sf.Rt C.N₁) fac)
    (hdomR : ∀ ψk ∈ Asupp C hv, Def6.XiDom (Def6.topGS S.d S.L C.N₁ m₁ (j + 1) ϱ)
      (Def6.aIdeal S.L (j + 1) (C.sf.a (j + 1)))
      (Def6.bgMass S.L (j + 1) (C.sf.β (j + 1)) (C.sf.ν (j + 1))) (j + 1)
      (P6.eps S.d S.L (j + 1)) (sfLiftK C.geo C.hnn C.hkK C.hT ψk) (Def6.constFld (hC hv))) :
    ∃ Mb : ℝ, ∀ ψk : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N),
      ‖sfFactor2 C vc (Set.univ : Set (Torus S.d (n (j + 1)))) ψk hv g‖ ≤ Mb :=
  exists_bound_sfFactor2_of_dom C hv vc hm0 hTm Set.univ
    (fun jj hj1 hj ψk hψ => ⟨C.psiJ Set.univ ψk hv jj, fun _ _ => rfl,
      fun X hX _ => hdomJ ψk hψ jj hj1 hj X hX⟩)
    (fun ψk hψ jj hj1 hj x _ => hpsiR ψk hψ jj hj1 hj x) g hgl HB hL hact hβ
    (fun ψk hψ z _ i => hphi ψk hψ z i) hRt
    (fun ψk hψ => ⟨sfLiftK C.geo C.hnn C.hkK C.hT ψk, fun _ _ => rfl, hdomR ψk hψ⟩)

include hm0 hTm in
/-- **`sfFactor2` of the whole torus is integrable** (A6-3 (a), item 1; the premise of the Gaussian
reduction `integral_sfFactor2_gauss` and of the expansion): measurable, bounded, and supported in a
bounded set of block fields. -/
theorem measInt_sfFactor2_univ_of_dom
    (hdomJ : ∀ ψk ∈ Asupp C hv, ∀ jj, 1 ≤ jj → jj ≤ j + 1 → ∀ X, Def6.IsPolyDom C.m₀ jj X →
      (sfDom P6 k0 C.sf C.N₁).dom jj ((C.sf.Tm C.N₁).gs jj X)
        (C.psiJ (Set.univ : Set (Torus S.d (n (j + 1)))) ψk hv jj) (Def6.constFld (hC hv)))
    {r : ℝ} (hpsiR : ∀ ψk ∈ Asupp C hv, ∀ jj, 1 ≤ jj → jj ≤ j + 1 →
      ∀ x : Localization.CTorus S.d S.L C.N₁ m₁ (j + 1), ∃ v : Fin N → ℝ,
        (∀ i, C.psiJ (Set.univ : Set (Torus S.d (n (j + 1)))) ψk hv jj x i = (v i : ℂ)) ∧
          0 < rn v ∧ rn v ≤ 2)
    (g : GIdx S n M K N → ℂ)
    (hgl : g ∈ LargeField.l1Ball (GIdx S n M K N))
    (HB : BgHyp S.d S.L (j + 1) (minSep S.L C.geo.M1) C.weights (C.cs.muBg (j + 1)))
    (hL : 2 ≤ S.L) (hact : 0 ≤ C.cs.muAct (j + 1)) (hβ : 0 ≤ C.sf.β (j + 1))
    (hAD : Asupp C hv ⊆ DomSet C hv (C.cs.muBg (j + 1)))
    (hphi : ∀ ψk ∈ Asupp C hv, ∀ z i,
      |(C.phiBar (Set.univ : Set (Torus S.d (n (j + 1)))) ψk hv z) i| ≤ 1)
    (hsupp : ∀ ψk ∈ Asupp C hv, ∀ b, ‖ψk b‖ ≤ r)
    {fac : ℕ → ℝ} (hRt : RTermsH4 (ϱ := ϱ) P6 C.sf.β C.sf.ν C.sf.a C.N₁ (C.sf.Rt C.N₁) fac)
    (hdomR : ∀ ψk ∈ Asupp C hv, Def6.XiDom (Def6.topGS S.d S.L C.N₁ m₁ (j + 1) ϱ)
      (Def6.aIdeal S.L (j + 1) (C.sf.a (j + 1)))
      (Def6.bgMass S.L (j + 1) (C.sf.β (j + 1)) (C.sf.ν (j + 1))) (j + 1)
      (P6.eps S.d S.L (j + 1)) (sfLiftK C.geo C.hnn C.hkK C.hT ψk) (Def6.constFld (hC hv)))
    (hmu : C.cs.mu (j + 1) = C.cs.muBg (j + 1)) :
    Measurable (fun ψk : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N) =>
      sfFactor2 C vc (Set.univ : Set (Torus S.d (n (j + 1)))) ψk hv g) ∧
    Integrable fun ψk : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N) =>
      sfFactor2 C vc (Set.univ : Set (Torus S.d (n (j + 1)))) ψk hv g := by
  have hg := l1_sfG_lt_one C g hgl
  have hslit : ∀ ψk ∈ Asupp C hv, ∀ jj, 1 ≤ jj → jj ≤ j + 1 → ∀ x,
      dot (C.psiJ (Set.univ : Set (Torus S.d (n (j + 1)))) ψk hv jj x)
        (C.psiJ (Set.univ : Set (Torus S.d (n (j + 1)))) ψk hv jj x) ∈ Complex.slitPlane := by
    intro ψk hψ jj hj1 hj x
    obtain ⟨v, hv1, hv0, -⟩ := hpsiR ψk hψ jj hj1 hj x
    have : C.psiJ (Set.univ : Set (Torus S.d (n (j + 1)))) ψk hv jj x = fun i => (v i : ℂ) :=
      funext hv1
    rw [this]
    exact dot_real_mem_slitPlane v hv0
  obtain ⟨Mb, hMb⟩ := exists_bound_sfFactor2 C hv vc hm0 hTm hdomJ hpsiR g hgl HB hL hact hβ hphi
    hRt hdomR
  have hmeas := measurable_sfFactor2_univ_of_dom C hv vc hm0 HB hTm hAD hdomJ hslit g hg hRt hdomR hmu
  refine ⟨hmeas, integrable_of_bdd_support hmeas r Mb ?_ hMb⟩
  intro ψk hne b
  refine hsupp ψk ?_ b
  intro h0
  apply hne
  unfold sfFactor2
  rw [h0]; simp

end Ctx

end Balaban.RootFSpine
