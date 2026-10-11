module

public import Balaban.Polymer.Mayer
public import Balaban.Analysis.AnalyticLimit
public import Balaban.Analysis.Cauchy

/-!
# Analyticity of the Mayer activities in the marks `λ`

The potentials `H_λ t Φ = H₀ t Φ + ∑_j λ_j G_j t Φ` are affine in the marks `λ ∈ ℂ^ι`.  Integrals
of polynomials in `λ` with bounded measurable coefficients are polynomials (`LamPoly`), the
activities `K(Y, λ)` are uniform limits on the polydisc of such integrals (truncated exponentials),
so they are analytic (`analyticOnNhd_mayerK_marks`).  Mathlib has no several-variable
"differentiable implies analytic", hence this route.
-/

@[expose] public section

noncomputable section

open scoped Classical

open Finset MeasureTheory Filter

namespace Balaban.Polymer

section LamPoly

/-- Functions of the marks and the configuration which are polynomial in the marks with bounded
measurable coefficients. -/
inductive LamPoly (ι : Type*) {B : Type*} (Ω : B → Type*) [∀ b, MeasurableSpace (Ω b)] :
    ((ι → ℂ) → (∀ b, Ω b) → ℂ) → Prop where
  | const (a : (∀ b, Ω b) → ℂ) : Measurable a → Bdd a → LamPoly ι Ω (fun _ => a)
  | add {Q Q' : (ι → ℂ) → (∀ b, Ω b) → ℂ} : LamPoly ι Ω Q → LamPoly ι Ω Q' →
      LamPoly ι Ω (fun l Φ => Q l Φ + Q' l Φ)
  | mulFun {Q : (ι → ℂ) → (∀ b, Ω b) → ℂ} (a : (∀ b, Ω b) → ℂ) : Measurable a → Bdd a →
      LamPoly ι Ω Q → LamPoly ι Ω (fun l Φ => a Φ * Q l Φ)
  | mulVar {Q : (ι → ℂ) → (∀ b, Ω b) → ℂ} (j : ι) (g : (∀ b, Ω b) → ℂ) : Measurable g → Bdd g →
      LamPoly ι Ω Q → LamPoly ι Ω (fun l Φ => l j * (g Φ * Q l Φ))

variable {B : Type*} {Ω : B → Type*} [∀ b, MeasurableSpace (Ω b)] {ι : Type*}

theorem LamPoly.measurable {Q : (ι → ℂ) → (∀ b, Ω b) → ℂ} (h : LamPoly ι Ω Q) (l : ι → ℂ) :
    Measurable (Q l) := by
  induction h with
  | const a ha _ => exact ha
  | add _ _ ih1 ih2 => exact ih1.add ih2
  | mulFun a ha _ _ ih => exact ha.mul ih
  | mulVar j g hg _ _ ih => exact measurable_const.mul (hg.mul ih)

theorem LamPoly.bdd {Q : (ι → ℂ) → (∀ b, Ω b) → ℂ} (h : LamPoly ι Ω Q) (l : ι → ℂ) :
    Bdd (Q l) := by
  induction h with
  | const a _ hb => exact hb
  | add _ _ ih1 ih2 =>
    obtain ⟨C1, h1⟩ := ih1; obtain ⟨C2, h2⟩ := ih2
    exact ⟨C1 + C2, fun x => (norm_add_le _ _).trans (add_le_add (h1 x) (h2 x))⟩
  | mulFun a _ hb _ ih =>
    obtain ⟨C1, h1⟩ := hb; obtain ⟨C2, h2⟩ := ih
    exact ⟨C1 * C2, fun x => by
      rw [norm_mul]; exact mul_le_mul (h1 x) (h2 x) (norm_nonneg _) ((norm_nonneg _).trans (h1 x))⟩
  | mulVar j g _ hb _ ih =>
    obtain ⟨C1, h1⟩ := hb; obtain ⟨C2, h2⟩ := ih
    exact ⟨‖l j‖ * (C1 * C2), fun x => by
      rw [norm_mul, norm_mul]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul (h1 x) (h2 x) (norm_nonneg _) ((norm_nonneg _).trans (h1 x)))
        (norm_nonneg _)⟩

theorem LamPoly.congr {Q Q' : (ι → ℂ) → (∀ b, Ω b) → ℂ} (h : ∀ l Φ, Q l Φ = Q' l Φ)
    (hQ : LamPoly ι Ω Q) : LamPoly ι Ω Q' := by
  have : Q = Q' := funext fun l => funext fun Φ => h l Φ
  exact this ▸ hQ

theorem LamPoly.mul {Q Q' : (ι → ℂ) → (∀ b, Ω b) → ℂ} (hQ : LamPoly ι Ω Q)
    (hQ' : LamPoly ι Ω Q') : LamPoly ι Ω (fun l Φ => Q l Φ * Q' l Φ) := by
  induction hQ' with
  | const a ha hb =>
    exact (LamPoly.mulFun a ha hb hQ).congr (fun l Φ => mul_comm _ _)
  | add _ _ ih1 ih2 =>
    exact (LamPoly.add ih1 ih2).congr (fun l Φ => (mul_add _ _ _).symm)
  | mulFun a ha hb _ ih =>
    exact (LamPoly.mulFun a ha hb ih).congr (fun l Φ => by ring)
  | mulVar j g hg hb _ ih =>
    exact (LamPoly.mulVar j g hg hb ih).congr (fun l Φ => by ring)

theorem LamPoly.zero : LamPoly ι Ω (fun _ _ => (0 : ℂ)) :=
  LamPoly.const (fun _ => 0) measurable_const ⟨0, fun _ => by simp⟩

theorem LamPoly.one : LamPoly ι Ω (fun _ _ => (1 : ℂ)) :=
  LamPoly.const (fun _ => 1) measurable_const ⟨1, fun _ => by simp⟩

theorem LamPoly.sum {κ : Type*} (s : Finset κ) {Q : κ → (ι → ℂ) → (∀ b, Ω b) → ℂ}
    (h : ∀ k ∈ s, LamPoly ι Ω (Q k)) : LamPoly ι Ω (fun l Φ => ∑ k ∈ s, Q k l Φ) := by
  induction s using Finset.induction_on with
  | empty => simpa using (LamPoly.zero (ι := ι) (Ω := Ω))
  | insert k s hk ih =>
    have := LamPoly.add (h k (Finset.mem_insert_self _ _))
      (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))
    exact this.congr (fun l Φ => by rw [Finset.sum_insert hk])

theorem LamPoly.prod {κ : Type*} (s : Finset κ) {Q : κ → (ι → ℂ) → (∀ b, Ω b) → ℂ}
    (h : ∀ k ∈ s, LamPoly ι Ω (Q k)) : LamPoly ι Ω (fun l Φ => ∏ k ∈ s, Q k l Φ) := by
  induction s using Finset.induction_on with
  | empty => simpa using (LamPoly.one (ι := ι) (Ω := Ω))
  | insert k s hk ih =>
    have := LamPoly.mul (h k (Finset.mem_insert_self _ _))
      (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))
    exact this.congr (fun l Φ => by rw [Finset.prod_insert hk])

theorem LamPoly.pow {Q : (ι → ℂ) → (∀ b, Ω b) → ℂ} (h : LamPoly ι Ω Q) (n : ℕ) :
    LamPoly ι Ω (fun l Φ => Q l Φ ^ n) :=
  (LamPoly.prod (Finset.range n) (Q := fun _ => Q) (fun _ _ => h)).congr
    (fun l Φ => by simp)

theorem LamPoly.smul {Q : (ι → ℂ) → (∀ b, Ω b) → ℂ} (h : LamPoly ι Ω Q) (c : ℂ) :
    LamPoly ι Ω (fun l Φ => c * Q l Φ) :=
  LamPoly.mulFun (fun _ => c) measurable_const ⟨‖c‖, fun _ => le_rfl⟩ h

/-- The affine functions `a(Φ) + ∑_j λ_j g_j(Φ)` are polynomial in the marks. -/
theorem LamPoly.affine [Fintype ι] (a : (∀ b, Ω b) → ℂ) (ha : Measurable a) (hab : Bdd a)
    (g : ι → (∀ b, Ω b) → ℂ) (hg : ∀ j, Measurable (g j)) (hgb : ∀ j, Bdd (g j)) :
    LamPoly ι Ω (fun l Φ => a Φ + ∑ j, l j * g j Φ) := by
  refine LamPoly.add (LamPoly.const a ha hab) ?_
  exact (LamPoly.sum Finset.univ (Q := fun j l Φ => l j * (g j Φ * 1))
    (fun j _ => LamPoly.mulVar j (g j) (hg j) (hgb j) LamPoly.one)).congr
    (fun l Φ => Finset.sum_congr rfl (fun j _ => by ring))


section Analytic

variable [Fintype B] (μ : ∀ b, Measure (Ω b)) [∀ b, IsProbabilityMeasure (μ b)]

theorem integrable_of_bdd {F : (∀ b, Ω b) → ℂ} (hm : Measurable F) (hb : Bdd F) :
    Integrable F (Measure.pi μ) := by
  obtain ⟨C, hC⟩ := hb
  exact Integrable.of_bound hm.aestronglyMeasurable C (Eventually.of_forall hC)

omit [(b : B) → MeasurableSpace (Ω b)] [Fintype B] in
theorem Bdd.mul_fun {F G : (∀ b, Ω b) → ℂ} (hF : Bdd F) (hG : Bdd G) :
    Bdd (fun Φ => F Φ * G Φ) := by
  obtain ⟨C1, h1⟩ := hF; obtain ⟨C2, h2⟩ := hG
  exact ⟨C1 * C2, fun x => by
    rw [norm_mul]; exact mul_le_mul (h1 x) (h2 x) (norm_nonneg _) ((norm_nonneg _).trans (h1 x))⟩

/-- Integrals of polynomials in the marks are analytic in the marks. -/
theorem LamPoly.analytic_integral [Fintype ι] {Q : (ι → ℂ) → (∀ b, Ω b) → ℂ}
    (h : LamPoly ι Ω Q) (w : (∀ b, Ω b) → ℂ) (hw : Measurable w) (hwb : Bdd w) :
    AnalyticOnNhd ℂ (fun l => ∫ Φ, w Φ * Q l Φ ∂(Measure.pi μ)) Set.univ := by
  induction h generalizing w with
  | const a ha hab =>
    exact analyticOnNhd_const
  | add h1 h2 ih1 ih2 =>
    rename_i Q1 Q2
    have e : ∀ l, ∫ Φ, w Φ * (Q1 l Φ + Q2 l Φ) ∂(Measure.pi μ) =
        ∫ Φ, w Φ * Q1 l Φ ∂(Measure.pi μ) + ∫ Φ, w Φ * Q2 l Φ ∂(Measure.pi μ) := by
      intro l
      have hi1 : Integrable (fun Φ => w Φ * Q1 l Φ) (Measure.pi μ) :=
        integrable_of_bdd μ (F := fun Φ => w Φ * Q1 l Φ) (hw.mul (h1.measurable l))
          (hwb.mul_fun (h1.bdd l))
      have hi2 : Integrable (fun Φ => w Φ * Q2 l Φ) (Measure.pi μ) :=
        integrable_of_bdd μ (F := fun Φ => w Φ * Q2 l Φ) (hw.mul (h2.measurable l))
          (hwb.mul_fun (h2.bdd l))
      rw [← integral_add hi1 hi2]
      exact integral_congr_ae (Eventually.of_forall (fun Φ => by simp only []; ring))
    simp_rw [e]
    exact (ih1 w hw hwb).add (ih2 w hw hwb)
  | mulFun a ha hab hQ ih =>
    rename_i Q1
    have e : ∀ l, ∫ Φ, w Φ * (a Φ * Q1 l Φ) ∂(Measure.pi μ) =
        ∫ Φ, (w Φ * a Φ) * Q1 l Φ ∂(Measure.pi μ) := fun l =>
      integral_congr_ae (Eventually.of_forall (fun Φ => by simp only []; ring))
    simp_rw [e]
    exact ih (fun Φ => w Φ * a Φ) (hw.mul ha) (hwb.mul_fun hab)
  | mulVar j g hg hgb hQ ih =>
    rename_i Q1
    have e : ∀ l, ∫ Φ, w Φ * (l j * (g Φ * Q1 l Φ)) ∂(Measure.pi μ) =
        l j * ∫ Φ, (w Φ * g Φ) * Q1 l Φ ∂(Measure.pi μ) := by
      intro l
      rw [← integral_const_mul]
      exact integral_congr_ae (Eventually.of_forall (fun Φ => by simp only []; ring))
    simp_rw [e]
    have hproj : AnalyticOnNhd ℂ (fun l : ι → ℂ => l j) Set.univ := fun l _ =>
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => ℂ) j).analyticAt l
    exact hproj.mul (ih (fun Φ => w Φ * g Φ) (hw.mul hg) (hwb.mul_fun hgb))

end Analytic

section Marks

variable [Fintype B] (μ : ∀ b, Measure (Ω b)) [∀ b, IsProbabilityMeasure (μ b)]
  {T : Type*} [Fintype T] (sup : T → Finset B) {ι : Type*} [Fintype ι]

/-- The truncated exponential series `∑_{n=1}^{N} z^n / n!`. -/
def truncExp (N : ℕ) (z : ℂ) : ℂ := ∑ n ∈ Finset.range N, z ^ (n + 1) / ((n + 1).factorial : ℂ)

omit [Fintype B] [∀ b, MeasurableSpace (Ω b)] [Fintype T] [Fintype ι] in
theorem norm_sub_truncExp_le (N : ℕ) (z : ℂ) :
    ‖Complex.exp z - 1 - truncExp N z‖ ≤ ‖z‖ ^ (N + 1) * Real.exp ‖z‖ := by
  have h := Complex.norm_exp_sub_sum_le_norm_mul_exp z (N + 1)
  rw [Finset.sum_range_succ'] at h
  have e : Complex.exp z - 1 - truncExp N z =
      Complex.exp z - (∑ m ∈ Finset.range N, z ^ (m + 1) / ((m + 1).factorial : ℂ) +
        z ^ 0 / (Nat.factorial 0 : ℂ)) := by
    unfold truncExp; simp; ring
  rw [e]; exact h

omit [Fintype B] [∀ b, MeasurableSpace (Ω b)] [Fintype T] [Fintype ι] in
theorem norm_truncExp_le {N : ℕ} {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖truncExp N z‖ ≤ 2 * Real.exp 1 + 1 := by
  have h1 := norm_sub_truncExp_le N z
  have h2 : ‖z‖ ^ (N + 1) * Real.exp ‖z‖ ≤ Real.exp 1 := by
    have : ‖z‖ ^ (N + 1) ≤ 1 := pow_le_one₀ (norm_nonneg _) hz
    calc _ ≤ 1 * Real.exp ‖z‖ := by gcongr
      _ ≤ _ := by rw [one_mul]; exact Real.exp_le_exp.mpr hz
  have h3 : ‖Complex.exp z - 1‖ ≤ Real.exp 1 + 1 := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_one]
    exact add_le_add ((Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.mpr hz)) le_rfl
  have : ‖truncExp N z‖ ≤ ‖Complex.exp z - 1‖ + ‖Complex.exp z - 1 - truncExp N z‖ := by
    calc ‖truncExp N z‖ = ‖(Complex.exp z - 1) - (Complex.exp z - 1 - truncExp N z)‖ := by
          congr 1; ring
      _ ≤ _ := norm_sub_le _ _
  linarith

/-- The potential with marks. -/
def Hlam (a : T → (∀ b, Ω b) → ℂ) (g : ι → T → (∀ b, Ω b) → ℂ) (l : ι → ℂ) (t : T)
    (Φ : ∀ b, Ω b) : ℂ := a t Φ + ∑ j, l j * g j t Φ

/-- The truncated integrand. -/
def mayerActN (N : ℕ) (H : T → (∀ b, Ω b) → ℂ) (Y : NePoly B) (Φ : ∀ b, Ω b) : ℂ :=
  ∑ C ∈ Cfam sup (fun _ : Finset T => True) Y.1, ∏ t ∈ C, truncExp N (H t Φ)

omit [Fintype B] in
theorem lamPoly_mayerActN [DecidableEq ι] (N : ℕ) (a : T → (∀ b, Ω b) → ℂ)
    (g : ι → T → (∀ b, Ω b) → ℂ)
    (ha : ∀ t, Measurable (a t)) (hab : ∀ t, Bdd (a t))
    (hg : ∀ j t, Measurable (g j t)) (hgb : ∀ j t, Bdd (g j t)) (Y : NePoly B) :
    LamPoly ι Ω (fun l Φ => mayerActN sup N (Hlam a g l) Y Φ) := by
  unfold mayerActN
  refine LamPoly.sum _ (fun C _ => LamPoly.prod _ (fun t _ => ?_))
  unfold truncExp
  refine LamPoly.sum _ (fun n _ => ?_)
  have hP := LamPoly.affine (ι := ι) (Ω := Ω) (a t) (ha t) (hab t) (fun j => g j t)
    (fun j => hg j t) (fun j => hgb j t)
  have := (hP.pow (n + 1)).smul (((n + 1).factorial : ℂ)⁻¹)
  exact this.congr (fun l Φ => by unfold Hlam; ring)

end Marks

section Limit

variable [Fintype B] (μ : ∀ b, Measure (Ω b)) [∀ b, IsProbabilityMeasure (μ b)]
  {T : Type*} [Fintype T] (sup : T → Finset B) {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype B] [Fintype T] [DecidableEq ι] in
theorem measurable_Hlam {a : T → (∀ b, Ω b) → ℂ} {g : ι → T → (∀ b, Ω b) → ℂ}
    (ha : ∀ t, Measurable (a t)) (hg : ∀ j t, Measurable (g j t)) (l : ι → ℂ) (t : T) :
    Measurable (Hlam a g l t) := by
  unfold Hlam
  exact (ha t).add (Finset.measurable_sum _ (fun j _ => measurable_const.mul (hg j t)))

/-- **Analyticity in the marks.**  If the potentials `a t + ∑_j λ_j g_j t` are bounded by
`q < 1` for `λ` in a polydisc, then the Mayer activities are analytic in `λ` there. -/
theorem analyticOnNhd_mayerK_marks {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (r : ι → ℝ)
    {a : T → (∀ b, Ω b) → ℂ} {g : ι → T → (∀ b, Ω b) → ℂ}
    (ha : ∀ t, Measurable (a t)) (hab : ∀ t, Bdd (a t))
    (hg : ∀ j t, Measurable (g j t)) (hgb : ∀ j t, Bdd (g j t))
    (hbound : ∀ l ∈ Balaban.Analysis.polydisc (0 : ι → ℂ) r, ∀ t Φ, ‖Hlam a g l t Φ‖ ≤ q)
    (Y : NePoly B) :
    AnalyticOnNhd ℂ (fun l => mayerK μ sup (Hlam a g l) Y) (Balaban.Analysis.polydisc 0 r) := by
  set ρ : ℝ := 2 * Real.exp 1 + 1 with hρ
  set Θ : (T → ℂ) → ℂ := fun v => ∑ C ∈ Cfam sup (fun _ : Finset T => True) Y.1, ∏ t ∈ C, v t
    with hΘdef
  have hΘ : Continuous Θ := continuous_finsetSum _ (fun C _ =>
    continuous_finsetProd _ (fun t _ => continuous_apply t))
  set K : Set (T → ℂ) := Metric.closedBall 0 ρ with hKdef
  have hK : IsCompact K := isCompact_closedBall _ _
  have huc : UniformContinuousOn Θ K := hK.uniformContinuousOn_of_continuous hΘ.continuousOn
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hΘ.continuousOn
  have hq1' : q ≤ 1 := hq1.le
  have hρ1 : Real.exp 1 + 1 ≤ ρ := by have := Real.exp_pos 1; rw [hρ]; linarith
  have hρ2 : 2 * Real.exp 1 + 1 ≤ ρ := le_of_eq hρ.symm
  -- membership in the compact ball
  have hmemN : ∀ N, ∀ l ∈ Balaban.Analysis.polydisc (0 : ι → ℂ) r, ∀ Φ : ∀ b, Ω b,
      (fun t => truncExp N (Hlam a g l t Φ)) ∈ K := by
    intro N l hl Φ
    rw [hKdef, mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (by positivity)]
    intro t
    exact (norm_truncExp_le ((hbound l hl t Φ).trans hq1')).trans le_rfl
  have hmem : ∀ l ∈ Balaban.Analysis.polydisc (0 : ι → ℂ) r, ∀ Φ : ∀ b, Ω b,
      (fun t => Complex.exp (Hlam a g l t Φ) - 1) ∈ K := by
    intro l hl Φ
    rw [hKdef, mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (by positivity)]
    intro t
    have hz := (hbound l hl t Φ).trans hq1'
    refine le_trans ?_ hρ1
    refine (norm_sub_le _ _).trans ?_
    rw [norm_one]
    exact add_le_add ((Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.mpr hz)) le_rfl
  have hPoly := fun N => lamPoly_mayerActN sup N a g ha hab hg hgb Y
  have hfN : ∀ N, AnalyticOnNhd ℂ
      (fun l => ∫ Φ, mayerActN sup N (Hlam a g l) Y Φ ∂(Measure.pi μ))
      (Balaban.Analysis.polydisc 0 r) := by
    intro N
    have := (hPoly N).analytic_integral μ (fun _ => 1) measurable_const ⟨1, fun _ => by simp⟩
    simp only [one_mul] at this
    exact this.mono (Set.subset_univ _)
  have hint : ∀ N l, Integrable (fun Φ => mayerActN sup N (Hlam a g l) Y Φ) (Measure.pi μ) :=
    fun N l => integrable_of_bdd μ ((hPoly N).measurable l) ((hPoly N).bdd l)
  have hintF : ∀ l ∈ Balaban.Analysis.polydisc (0 : ι → ℂ) r,
      Integrable (fun Φ => mayerAct sup (Hlam a g l) Y Φ) (Measure.pi μ) := by
    intro l hl
    refine integrable_of_bdd μ (measurable_mayerAct (measurable_Hlam ha hg l) Y) ?_
    exact bdd_mayerAct (fun t => ⟨q, fun Φ => hbound l hl t Φ⟩) Y
  have hreal : (Measure.pi μ).real Set.univ = 1 := by simp
  refine Balaban.Analysis.analyticOnNhd_of_tendstoUniformlyOn (M := M)
    (f := fun N l => ∫ Φ, mayerActN sup N (Hlam a g l) Y Φ ∂(Measure.pi μ))
    (Balaban.Analysis.isOpen_polydisc 0 r) hfN (fun N l hl => ?_) ?_
  · have := norm_integral_le_of_norm_le_const (μ := Measure.pi μ)
      (f := fun Φ => mayerActN sup N (Hlam a g l) Y Φ) (C := M)
      (Eventually.of_forall (fun Φ => hM _ (hmemN N l hl Φ)))
    rwa [hreal, mul_one] at this
  · rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    obtain ⟨δ, hδ, hδε⟩ := Metric.uniformContinuousOn_iff.mp huc (ε / 2) (half_pos hε)
    have hlim : Tendsto (fun N : ℕ => q ^ (N + 1) * Real.exp 1) atTop (nhds 0) := by
      have := (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).comp (tendsto_add_atTop_nat 1)
      simpa using this.mul_const (Real.exp 1)
    filter_upwards [hlim.eventually (gt_mem_nhds hδ)] with N hN
    intro l hl
    have hdist : ∀ Φ : ∀ b, Ω b, ‖mayerAct sup (Hlam a g l) Y Φ - mayerActN sup N (Hlam a g l) Y Φ‖
        ≤ ε / 2 := by
      intro Φ
      have hv := hmem l hl Φ
      have hvN := hmemN N l hl Φ
      have hd : dist (fun t => Complex.exp (Hlam a g l t Φ) - 1)
          (fun t => truncExp N (Hlam a g l t Φ)) < δ := by
        refine lt_of_le_of_lt ?_ hN
        rw [dist_pi_le_iff (by positivity)]
        intro t
        rw [dist_eq_norm]
        refine (norm_sub_truncExp_le N _).trans ?_
        have hz := hbound l hl t Φ
        gcongr
        · exact hz.trans hq1'
      have := hδε _ hv _ hvN hd
      rw [dist_eq_norm] at this
      exact this.le
    rw [dist_eq_norm]
    have hF := hintF l hl
    have h1 : mayerK μ sup (Hlam a g l) Y - ∫ Φ, mayerActN sup N (Hlam a g l) Y Φ ∂(Measure.pi μ) =
        ∫ Φ, (mayerAct sup (Hlam a g l) Y Φ - mayerActN sup N (Hlam a g l) Y Φ) ∂(Measure.pi μ) := by
      unfold mayerK
      rw [integral_sub hF (hint N l)]
    rw [h1]
    have := norm_integral_le_of_norm_le_const (μ := Measure.pi μ)
      (f := fun Φ => mayerAct sup (Hlam a g l) Y Φ - mayerActN sup N (Hlam a g l) Y Φ)
      (C := ε / 2) (Eventually.of_forall hdist)
    rw [hreal, mul_one] at this
    linarith

end Limit

end LamPoly

end Balaban.Polymer
