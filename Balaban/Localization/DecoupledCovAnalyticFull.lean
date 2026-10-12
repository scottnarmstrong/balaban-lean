/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.DecoupledCovAnalytic
public import Balaban.Localization.DecoupledCovParam
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# I-4c (iii): analyticity of `C_x(s)`, `C^{1/2}(s)` and `𝕃(s)` in `(s, φ₀, α₀)`

LOCALIZATION.md §3.4, Theorem I-4c (iii). The landed `rectAt_decCov` has `φ₀` frozen; here all of
`(s, φ₀, α₀)` vary.

* `IsConstraintFieldStrict`: the constraint-field conditions with strict inequalities (the
  statement of §3.4 "Objects"); `IsConstraintFieldStrict.toIsConstraintField` links it to the landed
  predicate, which is not changed; `isOpen_strictField`;
* `DecData`, `DecDom`, `isOpen_decDom`: the space of data `(s, φ₀, α₀)` and its open domain
  (polydisc `|s_P| < e^κ`, strict field conditions, strict potential bound);
* `rectAt_decCov_full`: the entries of `C_x(s)` are analytic in `(s, φ₀, α₀)` on `DecDom`
  for every `x ≥ 0`;
* `analyticOnNhd_decCovSqrt_entry`, `analyticOnNhd_decLog_entry`: the entries of `C^{1/2}(s)` and
  `𝕃(s)` are analytic on `DecDom` (the `x`-integrals are uniform limits of partial integrals,
  `analyticOnNhd_integral_Ioi`, with the dominating functions from I-4c (ii)).
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Finset Matrix MeasureTheory Set Filter Topology

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} {a : ℕ → ℝ} {aT ν : ℝ}

/-! ### The open set of data -/

/-- The strict version of `IsConstraintField` (P3 (3.2) / LOCALIZATION §3.4 "Objects" with strict
inequalities): its set is open. -/
structure IsConstraintFieldStrict (G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ) (δ : ℝ)
    (φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) : Prop where
  grad : ∀ x ∈ G.Ω 1, ∀ μ : Fin d,
    vn (φ (x + Pi.single μ 1) - φ x) < δ / G.spacing x ∧
      vn (φ (x - Pi.single μ 1) - φ x) < δ / G.spacing x
  lap : ∀ x ∈ G.Ω 1,
    vn (fun i => ∑ μ : Fin d, (φ (x + Pi.single μ 1) i + φ (x - Pi.single μ 1) i - 2 * φ x i)) <
      δ / G.spacing x ^ 2
  bound : ∀ x ∈ G.Ω 1, vn (φ x) < 3 / 2
  sq : ∀ x ∈ G.Ω 1, ‖∑ i, φ x i * φ x i - 1‖ < δ

theorem IsConstraintFieldStrict.toIsConstraintField {δ : ℝ}
    {φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ} (h : IsConstraintFieldStrict G δ φ) :
    IsConstraintField G δ φ where
  grad x hx μ := ⟨(h.grad x hx μ).1.le, (h.grad x hx μ).2.le⟩
  lap x hx := (h.lap x hx).le
  bound x hx := (h.bound x hx).le
  sq x hx := (h.sq x hx).le

theorem continuous_vn : Continuous (fun v : Fin N → ℂ => vn v) := by
  unfold vn
  exact continuous_norm.comp (PiLp.continuous_toLp 2 _)

theorem isOpen_strictField (δ : ℝ) :
    IsOpen {φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ | IsConstraintFieldStrict G δ φ} := by
  have hc : ∀ x : CTorus d L N₁ m₁ (k + 1), Continuous (fun φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ => φ x) :=
    fun x => continuous_apply x
  have e : {φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ | IsConstraintFieldStrict G δ φ} =
      ⋂ x ∈ (G.Ω 1 : Set (CTorus d L N₁ m₁ (k + 1))),
        ((⋂ μ : Fin d, {φ | vn (φ (x + Pi.single μ 1) - φ x) < δ / G.spacing x} ∩
          {φ | vn (φ (x - Pi.single μ 1) - φ x) < δ / G.spacing x}) ∩
        {φ | vn (fun i => ∑ μ : Fin d, (φ (x + Pi.single μ 1) i + φ (x - Pi.single μ 1) i
            - 2 * φ x i)) < δ / G.spacing x ^ 2} ∩
        {φ | vn (φ x) < 3 / 2} ∩ {φ | ‖∑ i, φ x i * φ x i - 1‖ < δ}) := by
    ext φ
    simp only [mem_ofPred_eq, mem_iInter, mem_inter_iff, Finset.mem_coe]
    constructor
    · intro h x hx
      exact ⟨⟨⟨fun μ => h.grad x hx μ, h.lap x hx⟩, h.bound x hx⟩, h.sq x hx⟩
    · intro h
      exact ⟨fun x hx μ => (h x hx).1.1.1 μ, fun x hx => (h x hx).1.1.2,
        fun x hx => (h x hx).1.2, fun x hx => (h x hx).2⟩
  rw [e]
  refine Set.Finite.isOpen_biInter (Finset.finite_toSet _) fun x _ => ?_
  refine IsOpen.inter (IsOpen.inter (IsOpen.inter (isOpen_iInter_of_finite fun μ => ?_) ?_) ?_) ?_
  · refine IsOpen.inter ?_ ?_
    · exact isOpen_lt (continuous_vn.comp ((hc _).sub (hc _))) continuous_const
    · exact isOpen_lt (continuous_vn.comp ((hc _).sub (hc _))) continuous_const
  · refine isOpen_lt (continuous_vn.comp ?_) continuous_const
    refine continuous_pi fun i => continuous_finsetSum _ fun μ _ => ?_
    exact ((((continuous_apply i).comp (hc _)).add ((continuous_apply i).comp (hc _))).sub
      (continuous_const.mul ((continuous_apply i).comp (hc _))))
  · exact isOpen_lt (continuous_vn.comp (hc _)) continuous_const
  · refine isOpen_lt (continuous_norm.comp ?_) continuous_const
    exact (continuous_finsetSum _ fun i _ => ((continuous_apply i).comp (hc _)).mul
      ((continuous_apply i).comp (hc _))).sub continuous_const

/-! ### The space of data and its open domain -/

/-- The space of data `(s, φ₀, α₀)`. -/
abbrev DecData (G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ) (N : ℕ) : Type _ :=
  DecParams G × ((CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) × (G.Ω 1 → ℂ))

/-- The open domain of the data: `|s_P| < e^κ`, the strict constraint-field conditions with
parameter `δ` and the strict potential bound. -/
def DecDom (G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ) (N : ℕ) (κ δ : ℝ) :
    Set (DecData G N) :=
  {p | (∀ P, ‖p.1 P‖ < Real.exp κ) ∧ IsConstraintFieldStrict G δ p.2.1 ∧
    ∀ w, ‖p.2.2 w‖ < coerciveConst d / (2 * (G.spacing (w : CTorus d L N₁ m₁ (k + 1))) ^ 2)}

theorem isOpen_decDom (κ δ : ℝ) : IsOpen (DecDom G N κ δ) := by
  have h1 : IsOpen {p : DecData G N | ∀ P, ‖p.1 P‖ < Real.exp κ} := by
    have : {p : DecData G N | ∀ P, ‖p.1 P‖ < Real.exp κ} =
        ⋂ P, {p : DecData G N | ‖p.1 P‖ < Real.exp κ} := by ext p; simp
    rw [this]
    exact isOpen_iInter_of_finite fun P => isOpen_lt
      (continuous_norm.comp ((continuous_apply P).comp continuous_fst)) continuous_const
  have h2 : IsOpen {p : DecData G N | IsConstraintFieldStrict G δ p.2.1} :=
    (isOpen_strictField (G := G) δ).preimage (continuous_fst.comp continuous_snd)
  have h3 : IsOpen {p : DecData G N | ∀ w : G.Ω 1,
      ‖p.2.2 w‖ < coerciveConst d / (2 * (G.spacing (w : CTorus d L N₁ m₁ (k + 1))) ^ 2)} := by
    have : {p : DecData G N | ∀ w : G.Ω 1,
        ‖p.2.2 w‖ < coerciveConst d / (2 * (G.spacing (w : CTorus d L N₁ m₁ (k + 1))) ^ 2)} =
        ⋂ w : G.Ω 1, {p : DecData G N |
        ‖p.2.2 w‖ < coerciveConst d / (2 * (G.spacing (w : CTorus d L N₁ m₁ (k + 1))) ^ 2)} := by
      ext p; simp
    rw [this]
    exact isOpen_iInter_of_finite fun w => isOpen_lt
      (continuous_norm.comp ((continuous_apply w).comp (continuous_snd.comp continuous_snd)))
      continuous_const
  exact h1.inter (h2.inter h3)

/-! ### Analyticity of `C_x(s)` in `(s, φ₀, α₀)` -/

theorem RectAt.comp' {E' E m n : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E']
    [NormedAddCommGroup E] [NormedSpace ℂ E] {M : E → Matrix m n ℂ} {f : E' → E} {e : E'}
    (hM : RectAt M (f e)) (hf : AnalyticAt ℂ f e) : RectAt (fun e' => M (f e')) e :=
  fun i j => (hM i j).comp hf

theorem RectAt.transpose' {E m n : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {M : E → Matrix m n ℂ} {e : E} (hM : RectAt M e) : RectAt (fun e' => (M e')ᵀ) e :=
  fun i j => hM j i

theorem analyticAt_field_coord (t : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) (e : DecData G N) :
    AnalyticAt ℂ (fun p : DecData G N => p.2.1 t i) e :=
  ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N => ℂ) i).analyticAt _).comp
    (((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : CTorus d L N₁ m₁ (k + 1) => Fin N → ℂ) t).analyticAt _).comp
      (analyticAt_fst.comp analyticAt_snd))

theorem rectAt_fieldMul (e : DecData G N) :
    RectAt (fun p : DecData G N => fieldMul (restrictField G p.2.1)) e := by
  intro q y
  by_cases h : q.1 = y
  · simp only [fieldMul, h, ↓reduceIte, restrictField]
    exact analyticAt_field_coord (y : CTorus d L N₁ m₁ (k + 1)) q.2 e
  · simp only [fieldMul, h, ↓reduceIte]
    exact analyticAt_const

section Cov

variable {x : ℝ} {κι : Type*} [Fintype κι] [DecidableEq κι] {Q : Matrix κι (G.Ω 1) ℂ}
  {P : Matrix κι κι ℂ}

theorem rectAt_decCov_full (S : XSetting G a aT ν) (hx : 0 ≤ x) {κ : ℝ} (hκ : 0 ≤ κ)
    (hM : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δ : ℝ} (hδ : 0 ≤ δ)
    (hsm : δ ^ 2 * smallConstX d L κ ≤ 1 / 4) {e : DecData G N} (he : e ∈ DecDom G N κ δ) :
    RectAt (fun p : DecData G N => decCov G a aT x ν p.2.2 (extS G p.1) p.2.1 Q P) e := by
  have hα : AdmPot G e.2.2 := fun w => (he.2.2 w).le
  have hs : ∀ P, ‖extS G e.1 P‖ ≤ Real.exp κ := by
    intro P
    unfold extS
    split_ifs with h
    · exact (he.1 ⟨P, h⟩).le
    · simpa using Real.one_le_exp hκ
  have D : XData G a aT ν x e.2.2 κ (extS G e.1) := ⟨S, hα, hx, hκ, hM, hs⟩
  have hφ : IsConstraintField G δ e.2.1 := he.2.1.toIsConstraintField
  have hpr : AnalyticAt ℂ (fun p : DecData G N => ((p.1, p.2.2) : DecParams G × (G.Ω 1 → ℂ))) e :=
    AnalyticAt.prod analyticAt_fst (analyticAt_snd.comp analyticAt_snd)
  have hHx : RectAt (fun p : DecData G N => xDirichletOperator G a aT x ν p.2.2) e :=
    RectAt.comp' (f := fun p : DecData G N => ((p.1, p.2.2) : DecParams G × (G.Ω 1 → ℂ)))
      (rectAt_xDirichlet (G := G) a aT x ν ((e.1, e.2.2) : DecParams G × (G.Ω 1 → ℂ))) hpr
  have hGs : RectAt (fun p : DecData G N => Gsx G a aT x ν p.2.2 (extS G p.1)) e :=
    RectAt.comp' (f := fun p : DecData G N => ((p.1, p.2.2) : DecParams G × (G.Ω 1 → ℂ)))
      (matAt_Gsx S hx hα D.isUnit_one_sub) hpr
  have hGl := hGs.liftOp (N := N)
  have hHl := hHx.liftOp (N := N)
  have hF := rectAt_fieldMul (G := G) (N := N) e
  have hK : RectAt (fun p : DecData G N =>
      commK (xDirichletOperator G a aT x ν p.2.2) (restrictField G p.2.1)) e := by
    unfold commK
    exact (hF.transpose'.mul hHl).sub (hHx.mul hF.transpose')
  have hMa : RectAt (fun p : DecData G N =>
      decM G a aT x ν p.2.2 (extS G p.1) p.2.1) e := by
    unfold decM constraintM
    exact (hF.transpose'.mul hF).sub ((hK.mul hGl).mul hF)
  have hNa : RectAt (fun p : DecData G N =>
      decN G a aT x ν p.2.2 (extS G p.1) p.2.1) e := by
    unfold decN constraintN
    exact hF.transpose'.sub (hK.mul hGl)
  have hdet : (decM G a aT x ν e.2.2 (extS G e.1) e.2.1).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).1 (decM_isUnit D hφ hδ hsm)).ne_zero
  have hMi := hMa.inv hdet
  have hPi : RectAt (fun p : DecData G N =>
      decPi G a aT x ν p.2.2 (extS G p.1) p.2.1) e := by
    unfold decPi
    exact (((hGl.mul hF).mul hMi).mul hNa)
  unfold decCov
  have hA := RectAt.const (E := DecData G N)
    (covA (a k) (aT / (L : ℝ) ^ 2) x (liftOp N P)) e
  refine hA.add (RectAt.smul_const _ ?_)
  exact (((hA.mul (RectAt.const _ e)).mul (hGl.sub hPi)).mul (RectAt.const _ e)).mul hA

end Cov

/-! ### Analyticity of `C^{1/2}(s)` and `𝕃(s)` in `(s, φ₀, α₀)` -/

section Integrals

variable {x : ℝ} {κι : Type*} [Fintype κι] [DecidableEq κι] {Q : Matrix κι (G.Ω 1) ℂ}
  {P : Matrix κι κι ℂ}

/-- The standing hypotheses `CovStanding` hold at every point of the domain. -/
theorem covStanding_of_mem (S : XSetting G a aT ν) {κ : ℝ} (hκ : 0 ≤ κ)
    (hM : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δ : ℝ} (hδ : 0 ≤ δ)
    (hsm : δ ^ 2 * smallConstX d L κ ≤ 1 / 4) (hU : IsUnitLattice G Q P) {e : DecData G N}
    (he : e ∈ DecDom G N κ δ) :
    CovStanding G a aT ν e.2.2 κ (extS G e.1) δ e.2.1 Q P := by
  have hα : AdmPot G e.2.2 := fun w => (he.2.2 w).le
  have hs : ∀ P, ‖extS G e.1 P‖ ≤ Real.exp κ := by
    intro P
    unfold extS
    split_ifs with h
    · exact (he.1 ⟨P, h⟩).le
    · simpa using Real.one_le_exp hκ
  exact ⟨fun x hx => ⟨S, hα, hx, hκ, hM, hs⟩, he.2.1.toIsConstraintField, hδ, hsm, hU⟩

theorem continuousOn_inv_add_Ioi {ak : ℝ} (hak : 0 < ak) :
    ContinuousOn (fun y : ℝ => (ak + y)⁻¹) (Ioi 0) :=
  (continuousOn_const.add continuousOn_id).inv₀ fun y hy => by
    have := mem_Ioi.mp hy
    show ak + y ≠ 0
    exact (by linarith : 0 < ak + y).ne'

theorem XSetting.hak_pos (S : XSetting G a aT ν) : 0 < a k := by
  have := S.ha k S.hk le_rfl
  linarith [this.1]

variable (S : XSetting G a aT ν) {κ : ℝ} (hκ : 0 ≤ κ)
  (hM : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δ : ℝ} (hδ : 0 ≤ δ)
  (hsm : δ ^ 2 * smallConstX d L κ ≤ 1 / 4) (hU : IsUnitLattice G Q P)
include S hκ hM hδ hsm hU

/-- **I-4c (iii), the square root**: every entry of `C^{1/2}(s)` is analytic in `(s, φ₀, α₀)` on
the open domain `DecDom`. -/
theorem analyticOnNhd_decCovSqrt_entry (p q : κι × Fin N) :
    AnalyticOnNhd ℂ (fun e : DecData G N =>
      decCovSqrt G a aT ν e.2.2 (extS G e.1) e.2.1 Q P p q) (DecDom G N κ δ) := by
  have hak := S.hak_pos
  have hB := covB4_nonneg d L (a k) κ
  have hint : AnalyticOnNhd ℂ (fun e : DecData G N => ∫ y in Ioi (0 : ℝ),
      ((y ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * decCov G a aT y ν e.2.2 (extS G e.1) e.2.1 Q P p q)
      (DecDom G N κ δ) := by
    refine analyticOnNhd_integral_Ioi (g := sqrtDom d L (a k) κ) (isOpen_decDom κ δ) ?_ ?_ ?_ ?_ ?_
    · intro y hy e he
      exact analyticAt_const.mul (rectAt_decCov_full S hy.le hκ hM hδ hsm he p q)
    · intro e he
      have H := covStanding_of_mem S hκ hM hδ hsm hU he
      refine ContinuousOn.mul ?_ ((continuousOn_decCov_entry H p q).mono Ioi_subset_Ici_self)
      refine Complex.continuous_ofReal.comp_continuousOn ?_
      exact fun y hy => (Real.continuousAt_rpow_const _ _ (Or.inl (mem_Ioi.mp hy).ne')).continuousWithinAt
    · unfold sqrtDom
      refine ContinuousOn.add ?_ (ContinuousOn.mul continuousOn_const ?_)
      · refine ContinuousOn.mul ?_ ?_
        · exact fun y hy => (Real.continuousAt_rpow_const _ _ (Or.inl (mem_Ioi.mp hy).ne')).continuousWithinAt
        · exact continuousOn_inv_add_Ioi hak
      · refine ContinuousOn.mul ?_ ?_
        · exact fun y hy => (Real.continuousAt_rpow_const _ _ (Or.inl (mem_Ioi.mp hy).ne')).continuousWithinAt
        · exact (continuousOn_inv_add_Ioi hak).pow 2
    · exact integrable_sqrtDom hak d L κ
    · intro y hy e he
      have H := covStanding_of_mem S hκ hM hδ hsm hU he
      have h3 : 0 < y ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hy _
      simp only [norm_mul, Complex.norm_real, Real.norm_of_nonneg h3.le]
      have := entry_decCov_le H hy.le p q
      calc y ^ (-(1 / 2 : ℝ)) * ‖decCov G a aT y ν e.2.2 (extS G e.1) e.2.1 Q P p q‖
          ≤ y ^ (-(1 / 2 : ℝ)) * ((a k + y)⁻¹ + covB4 d L (a k) κ * ((a k + y)⁻¹) ^ 2) :=
            mul_le_mul_of_nonneg_left this h3.le
        _ = sqrtDom d L (a k) κ y := by unfold sqrtDom; ring
  intro e he
  have := (analyticAt_const (v := ((1 / Real.pi : ℝ) : ℂ))).mul (hint e he)
  refine this.congr (Filter.Eventually.of_forall fun e' => ?_)
  simp only [decCovSqrt, intMat, decSqrtInt, Matrix.smul_apply, smul_eq_mul, Matrix.smul_apply]
  rfl

/-- **I-4c (iii), the logarithm**: every entry of `𝕃(s)` is analytic in `(s, φ₀, α₀)` on the open
domain `DecDom`. -/
theorem analyticOnNhd_decLog_entry (p q : κι × Fin N) :
    AnalyticOnNhd ℂ (fun e : DecData G N =>
      decLog G a aT ν e.2.2 (extS G e.1) e.2.1 Q P p q) (DecDom G N κ δ) := by
  have hak := S.hak_pos
  have hB := covB4_nonneg d L (a k) κ
  have hint : AnalyticOnNhd ℂ (fun e : DecData G N => ∫ y in Ioi (0 : ℝ),
      (decCov G a aT y ν e.2.2 (extS G e.1) e.2.1 Q P -
        covA (a k) (aT / (L : ℝ) ^ 2) y (liftOp N P)) p q) (DecDom G N κ δ) := by
    refine analyticOnNhd_integral_Ioi (g := fun y => covB4 d L (a k) κ * ((a k + y)⁻¹) ^ 2)
      (isOpen_decDom κ δ) ?_ ?_ ?_ ?_ ?_
    · intro y hy e he
      simp only [Matrix.sub_apply]
      exact (rectAt_decCov_full S hy.le hκ hM hδ hsm he p q).sub analyticAt_const
    · intro e he
      have H := covStanding_of_mem S hκ hM hδ hsm hU he
      have h1 := continuousOn_decCov_entry H p q
      have h2 : ContinuousOn (fun y => covA (a k) (aT / (L : ℝ) ^ 2) y (liftOp N P) p q) (Ici 0) :=
        continuousOn_pi.1 (continuousOn_pi.1
          (continuousOn_covA H.hak H.hb (liftOp N P)) p) q
      exact (h1.sub h2).mono Ioi_subset_Ici_self
    · refine ContinuousOn.mul continuousOn_const ?_
      exact (continuousOn_inv_add_Ioi hak).pow 2
    · exact (integrableOn_inv_add_sq hak).const_mul _
    · intro y hy e he
      have H := covStanding_of_mem S hκ hM hδ hsm hU he
      exact entry_decCov_sub_le H hy.le p q
  intro e he
  have := (analyticAt_const (v := (((Real.log (a k) : ℝ) : ℂ) • (1 - liftOp N P) +
      ((Real.log (a k + aT / (L : ℝ) ^ 2) : ℝ) : ℂ) • liftOp N P) p q)).sub (hint e he)
  refine this.congr (Filter.Eventually.of_forall fun e' => ?_)
  simp only [decLog, intMat, Matrix.sub_apply, Pi.sub_apply]

end Integrals

end Balaban.Localization
