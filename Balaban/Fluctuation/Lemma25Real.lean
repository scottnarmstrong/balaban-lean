/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.Lemma25
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Lemma 2.4 (c): `C^{(k)1/2}` has real entries; Lemma 2.5 for the fluctuation field

For real data (`α` real, `φ` real, `Q = unitQ` real) the operator `covOp = 𝒜` has real entries
(`isRealMat_covOp`; the limit `xH0` of the x-variant operators, the constrained part, products and
inverses of real matrices), hence so do its resolvents and the resolvent integral `sqrtMat`
(`isRealMat_sqrtMat`), which is `C^{(k)1/2}` (`decCovSqrt_isRealMat`).  The fluctuation field
`ψ = ψ^{(k)} + β^{-1/2} C^{(k)1/2} ψ̂` is thus a real field (`fluctPsi`), and `lemma25_field` is
Lemma 2.5 for it, without hypotheses on the field.
-/

@[expose] public section

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Localization Finset
  Matrix

namespace Balaban.Fluctuation

section RealMat

variable {m n o : Type*}

/-- A complex matrix with real entries. -/
def IsRealMat (A : Matrix m n ℂ) : Prop := ∀ p q, starRingEnd ℂ (A p q) = A p q

theorem IsRealMat.add {A B : Matrix m n ℂ} (hA : IsRealMat A) (hB : IsRealMat B) :
    IsRealMat (A + B) := fun p q => by simp [hA p q, hB p q]

theorem IsRealMat.sub {A B : Matrix m n ℂ} (hA : IsRealMat A) (hB : IsRealMat B) :
    IsRealMat (A - B) := fun p q => by simp [hA p q, hB p q]

theorem IsRealMat.mul [Fintype n] {A : Matrix m n ℂ} {B : Matrix n o ℂ} (hA : IsRealMat A)
    (hB : IsRealMat B) : IsRealMat (A * B) := fun p q => by
  simp [Matrix.mul_apply, map_sum, hA _ _, hB _ _]

theorem IsRealMat.smul_real {A : Matrix m n ℂ} (c : ℝ) (hA : IsRealMat A) :
    IsRealMat ((c : ℂ) • A) := fun p q => by simp [hA p q]

theorem isRealMat_one [DecidableEq m] : IsRealMat (1 : Matrix m m ℂ) := fun p q => by
  simp only [Matrix.one_apply]; split_ifs <;> simp

theorem IsRealMat.transpose {A : Matrix m n ℂ} (hA : IsRealMat A) : IsRealMat Aᵀ :=
  fun p q => hA q p

theorem IsRealMat.inv [Fintype m] [DecidableEq m] {A : Matrix m m ℂ} (hA : IsRealMat A) :
    IsRealMat A⁻¹ := by
  have hmap : A.map (starRingEnd ℂ) = A := Matrix.ext fun p q => hA p q
  intro p q
  have e : (A⁻¹).map (starRingEnd ℂ) = (A.map (starRingEnd ℂ))⁻¹ := by
    have h1 : (starRingEnd ℂ).mapMatrix A⁻¹ = ((starRingEnd ℂ).mapMatrix A)⁻¹ := by
      rw [Matrix.inv_def, Matrix.inv_def, Ring.inverse_eq_inv']
      rw [← RingHom.map_adjugate, ← RingHom.map_det]
      ext r s
      simp [RingHom.mapMatrix_apply]
    exact h1
  have := congrFun (congrFun e p) q
  rw [hmap] at this
  simpa using this

theorem isRealMat_liftOp {ι : Type*} (N : ℕ) {A : Matrix ι ι ℂ} (hA : IsRealMat A) :
    IsRealMat (liftOp N A) := fun p q => by
  unfold liftOp; split_ifs
  · exact hA _ _
  · simp

theorem isRealMat_liftRect {κι ι : Type*} (N : ℕ) {A : Matrix κι ι ℂ} (hA : IsRealMat A) :
    IsRealMat (liftRect N A) := fun p q => by
  unfold liftRect; split_ifs
  · exact hA _ _
  · simp

theorem isRealMat_fieldMul {ι : Type*} [DecidableEq ι] {N : ℕ} {φ : ι → Fin N → ℂ}
    (hφ : ∀ y i, starRingEnd ℂ (φ y i) = φ y i) : IsRealMat (fieldMul φ) := fun p q => by
  unfold fieldMul; split_ifs
  · exact hφ _ _
  · simp

end RealMat

section Constrained

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}

theorem isRealMat_constrainedOp {A : Matrix ι ι ℂ} (hA : IsRealMat A) {φ : ι → Fin N → ℂ}
    (hφ : ∀ y i, starRingEnd ℂ (φ y i) = φ y i) : IsRealMat (constrainedOp A φ) := by
  have hF := isRealMat_fieldMul hφ
  have hL := isRealMat_liftOp N hA
  have hC : IsRealMat (constraintForm A φ) := by
    unfold constraintForm
    exact (hF.transpose.mul hL).mul hF
  unfold constrainedOp
  exact (((hL.mul hF).mul hC.inv).mul hF.transpose).mul hL

end Constrained


section Cov

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
  {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} {a : ℕ → ℝ} {aT ν : ℝ}
  {α : G.Ω 1 → ℂ} {φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ}

theorem isRealMat_xDirichlet (x : ℝ) (hα : ∀ w, starRingEnd ℂ (α w) = α w) :
    IsRealMat (xDirichletOperator G a aT x ν α) := by
  unfold xDirichletOperator
  refine IsRealMat.add (fun p q => ?_) (fun p q => ?_)
  · simp [Green.restrictOp, Matrix.submatrix_apply, Matrix.map_apply]
  · by_cases h : p = q <;> simp [h, hα]

theorem isRealMat_xH0 (hfam : ∀ x, 0 ≤ x → XData G a aT ν x α 0 (fun _ => 1))
    (hα : ∀ w, starRingEnd ℂ (α w) = α w) : IsRealMat (xH0 G a ν α) := by
  have D0 := hfam 0 le_rfl
  have hak : 0 < a k := by
    have := (⟨D0.st.hak1, D0.st.hak2⟩ : _ ∧ _)
    linarith [this.1]
  have hb : 0 ≤ aT / (L : ℝ) ^ 2 := by
    have := D0.st.haT1
    positivity
  have h1 := tendsto_xDirichlet (aT := aT) (ν := ν) hak hb α
  intro p q
  have h2 : Filter.Tendsto (fun x : ℝ => xDirichletOperator G a aT x ν α p q) Filter.atTop
      (nhds (xH0 G a ν α p q)) := ((continuous_id.matrix_elem p q).tendsto _).comp h1
  have h3 := (Complex.continuous_conj.tendsto _).comp h2
  have h4 : (fun x : ℝ => starRingEnd ℂ (xDirichletOperator G a aT x ν α p q)) =
      fun x => xDirichletOperator G a aT x ν α p q := funext fun x => isRealMat_xDirichlet x hα p q
  have h5 : Filter.Tendsto (fun x : ℝ => xDirichletOperator G a aT x ν α p q) Filter.atTop
      (nhds (starRingEnd ℂ (xH0 G a ν α p q))) := by
    have := h3
    simp only [Function.comp_def] at this
    rwa [h4] at this
  exact (tendsto_nhds_unique h5 h2)

theorem isRealMat_covOp {κι : Type*} [Fintype κι] [DecidableEq κι] {Q : Matrix κι (G.Ω 1) ℂ}
    {P : Matrix κι κι ℂ} (hfam : ∀ x, 0 ≤ x → XData G a aT ν x α 0 (fun _ => 1))
    (hα : ∀ w, starRingEnd ℂ (α w) = α w) (hφ : ∀ y i, starRingEnd ℂ (φ y i) = φ y i)
    (hQ : IsRealMat Q) (hP : IsRealMat P) : IsRealMat (covOp G a aT ν α φ Q P) := by
  have hH := isRealMat_xH0 hfam hα
  have hCO := isRealMat_constrainedOp (N := N) hH.inv
    (φ := restrictField G φ) (fun y i => hφ _ _)
  have hW : IsRealMat (liftOp N (xH0 G a ν α)⁻¹ - constrainedOp (xH0 G a ν α)⁻¹ (restrictField G φ)) :=
    (isRealMat_liftOp N hH.inv).sub hCO
  have hR := isRealMat_liftRect (N := N) hQ
  unfold covOp
  exact ((isRealMat_one.smul_real _).add ((isRealMat_liftOp N hP).smul_real _)).sub
    (((hR.mul hW).mul hR.transpose).smul_real _)

end Cov

section Sqrt

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem isRealMat_sqrtMat {A : Matrix ι ι ℂ} (hA : IsRealMat A) : IsRealMat (sqrtMat A) := by
  intro p q
  have e : sqrtMat A p q = ((1 / Real.pi : ℝ) : ℂ) * ∫ x in Set.Ioi (0 : ℝ),
      (((x ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) * (((x : ℂ) • (1 : Matrix ι ι ℂ) + A)⁻¹ p q) := rfl
  rw [e, map_mul, Complex.conj_ofReal, ← integral_conj]
  congr 1
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
  have hM : IsRealMat (((x : ℂ) • (1 : Matrix ι ι ℂ) + A)) :=
    ((isRealMat_one (m := ι)).smul_real x).add hA
  have hMi := hM.inv p q
  rw [map_mul, Complex.conj_ofReal, hMi]

end Sqrt

section Unit

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
  {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} {a : ℕ → ℝ} {aT ν : ℝ}
  {α : G.Ω 1 → ℂ} {δ : ℝ} {φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ}

theorem isRealMat_unitQ : IsRealMat (unitQ G) := fun b y => by
  simpa using unitQ_real G b y

theorem isRealMat_unitP : IsRealMat (unitP G) := fun b b' => by
  unfold unitP; split_ifs
  · exact Complex.conj_ofReal _
  · simp

/-- **`C^{(k)1/2}` has real entries for real data** (Lemma 2.4 (c), reality). -/
theorem decCovSqrt_isRealMat (hfam : ∀ x, 0 ≤ x → XData G a aT ν x α 0 (fun _ => 1))
    (hφ : IsConstraintField G δ φ) (hδ : 0 ≤ δ) (hsm : δ ^ 2 * smallConstX d L 0 ≤ 1 / 4)
    (hα : ∀ w, starRingEnd ℂ (α w) = α w) (hφr : ∀ y i, starRingEnd ℂ (φ y i) = φ y i) :
    IsRealMat (decCovSqrt G a aT ν α (fun _ => 1) φ (unitQ G) (unitP G)) := by
  rw [(lemma24_c_principal hfam hφ hδ hsm).1]
  exact isRealMat_sqrtMat (isRealMat_covOp hfam hα hφr isRealMat_unitQ isRealMat_unitP)

theorem mulVec_im_zero {ι : Type*} [Fintype ι] {C : Matrix ι ι ℂ} (hC : IsRealMat C)
    {v : ι → ℂ} (hv : ∀ q, (v q).im = 0) (p : ι) : ((C *ᵥ v) p).im = 0 := by
  have h1 : starRingEnd ℂ ((C *ᵥ v) p) = (C *ᵥ v) p := by
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [hC p q]
    congr 1
    exact Complex.conj_eq_iff_im.2 (hv q)
  exact Complex.conj_eq_iff_im.1 h1

end Unit

section Field

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱ' : ℝ}
  {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} {G' : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ'}

/-- The multiplier of real data is real. -/
theorem bgMult_isReal {a : ℕ → ℝ} {ν : ℝ} (H : BgHyp d L (k + 1) ϱ' a ν) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ : δ ≤ bgC1 d L N) {D : BgData G' N} (hD : InDomainR G' ν δ D) (x : G'.Ω 1) :
    starRingEnd ℂ (bgMult G' a ν D x) = bgMult G' a ν D x := by
  obtain ⟨φ, α, hs, -, hu, -, hmin, hmu⟩ := bg_real H hδ0 hδ hD
  have hreal := isReal_of_inDomainR hD
  have hf : bgField G' a ν D = φ := bgField_eq hmin hmu
  have hm : bgMult G' a ν D = α := by
    funext y
    unfold bgMult
    rw [hf]
    exact mult_formula hs.1 y
  rw [hm]
  have hcj := isSmallSolution_conj D hreal hs
  exact congrFun (hu _ _ hcj).2 x

theorem fluctShift_im_zero (hG' : IsLevel G' (k + 1)) {a₁ : ℝ} {ν : ℝ}
    (H' : BgHyp d L (k + 1) ϱ' (compWeight L a₁) ν) {D' : BgData G' N} {δ' : ℝ} (hδ'0 : 0 < δ')
    (hδ'c1 : δ' ≤ bgC1 d L N) (hD'R : InDomainR G' ν δ' D') {δ : ℝ} (hδ0 : 0 < δ)
    (hχ : ChiUBounds G' ν δ D' (bgField G' (compWeight L a₁) ν D')
      (bgMult G' (compWeight L a₁) ν D')) {aT : ℝ}
    (hfam : ∀ x, 0 ≤ x → XData G' (compWeight L a₁) aT ν x (bgMult G' (compWeight L a₁) ν D') 0
      (fun _ => 1))
    (hsm : δ ^ 2 * smallConstX d L 0 ≤ 1 / 4) (β : ℝ) (ψh : unitPts G' → Rn N)
    (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) :
    (fluctShift hG' (compWeight L a₁) aT ν D' β ψh x i).im = 0 := by
  have hDU' : InUnionDomainR G' (bgC1 d L N) ν D' := ⟨δ', hδ'0, hδ'c1, hD'R⟩
  obtain ⟨-, hunit, -, -⟩ := theorem71 H' hDU'
  have hcf := isConstraintField_of_chiU hG' hχ hδ0.le hunit
  have hα := bgMult_isReal H' hδ'0 hδ'c1 hD'R
  have hφr : ∀ y i, starRingEnd ℂ (svec G' (bgField G' (compWeight L a₁) ν D') y i) =
      svec G' (bgField G' (compWeight L a₁) ν D') y i := by
    intro y i
    by_cases hy : y ∈ G'.Ω 1
    · rw [svec_of_mem G' _ ⟨y, hy⟩ i]
      exact Complex.conj_eq_iff_im.2 ((hunit ⟨y, hy⟩).1 i)
    · rw [svec_of_not_mem G' _ hy]; simp
  have hC := decCovSqrt_isRealMat hfam hcf hδ0.le hsm hα hφr
  have hv : ∀ q : unitPts G' × Fin N, ((fun q : unitPts G' × Fin N => (ψh q.1 q.2 : ℂ)) q).im = 0 :=
    fun q => Complex.ofReal_im _
  have := mulVec_im_zero hC hv (unitPt hG' x, i)
  unfold fluctShift
  rw [Complex.im_ofReal_mul, this, mul_zero]

/-- **The fluctuation field** `ψ = ψ^{(k)}(θ) + β^{-1/2} C^{(k)1/2} ψ̂` as a real field on the fine
torus (the real part; `C^{(k)1/2}` has real entries, `fluctShift_im_zero`). -/
noncomputable def fluctPsi (hG : IsLevel G k) (hG' : IsLevel G' (k + 1)) (a : ℕ → ℝ)
    (aT ν : ℝ) (D' : BgData G' N) (β : ℝ) (ψh : unitPts G' → Rn N) :
    CTorus d L N₁ m₁ (k + 1) → Fin N → ℝ := fun x i =>
  ((psiK hG hG' a ν D').Ψ x i + fluctShift hG' a aT ν D' β ψh x i).re

theorem fluctPsi_layerConst (hG : IsLevel G k) (hG' : IsLevel G' (k + 1)) (a : ℕ → ℝ)
    (aT ν : ℝ) (D' : BgData G' N) (β : ℝ) (ψh : unitPts G' → Rn N) :
    IsLayerConstant G (fluctPsi hG hG' a aT ν D' β ψh) := by
  intro n hn1 hnk x hx x' hx'
  have hnk' : n = k := by
    have h1 := G.layerIndex_eq hn1 hnk hx
    rw [(hG x).2] at h1
    exact h1.symm
  subst hnk'
  have hb : unitBlock x' = unitBlock x := GeneratingSet.mem_blk.1 hx'
  have hu : unitPt hG' x' = unitPt hG' x := Subtype.ext hb
  funext i
  have h1 := congrFun ((psiK hG hG' a ν D').Ψ_layerConst n hn1 hnk x hx x' hx') i
  unfold fluctPsi fluctShift
  rw [h1, hu]

/-- **Lemma 2.5, for the fluctuation field itself**: for every real `ψ̂`, the real field
`ψ = ψ^{(k)}(θ) + β^{-1/2} C^{(k)1/2} ψ̂` (`fluctPsi`) satisfies
`χ_k(ψ) χ_{(2.2)}(θ, ψ) χ_fl(ψ̂) = χ_fl(ψ̂)`.  Premises as in `lemma25`, without the field
hypotheses (the field is constructed; `C^{(k)1/2}` is real). -/
theorem lemma25_field {a₁ : ℝ} (ha₁ : 0 < a₁) {ν : ℝ} (hG : IsLevel G k)
    (hG' : IsLevel G' (k + 1)) (H : BgHyp d L (k + 1) ϱ (compWeight L a₁) ν)
    (H' : BgHyp d L (k + 1) ϱ' (compWeight L a₁) ν)
    {D' : BgData G' N} {δ' : ℝ} (hδ'0 : 0 < δ') (hδ' : δ' ≤ thm73C3 d L N / 2)
    (hD'R : InDomainR G' ν δ' D') {h₀ : Fin N → ℝ} (hh₀ : ∀ x i, D'.h x i = (h₀ i : ℂ))
    {δ : ℝ} (hδ0 : 0 < δ) {aT : ℝ}
    (hfam : ∀ x, 0 ≤ x → XData G' (compWeight L a₁) aT ν x (bgMult G' (compWeight L a₁) ν D') 0
      (fun _ => 1))
    (hsm : δ ^ 2 * smallConstX d L 0 ≤ 1 / 4)
    (hχu : chiU G' (compWeight L a₁) ν δ D' = 1)
    (hnorm : ν * ((L : ℝ) ^ k) ^ 2 * |∑ i, h₀ i ^ 2 - 1| < (1 * δ) ^ 2)
    {β p₁ B₅ K₂ : ℝ} (hβ : 0 < β) (hp₁ : 0 < p₁)
    (hB5 : max 1 (Real.sqrt N * covSupConst d L N (compWeight L a₁ k)) ≤ B₅)
    (hK2 : max (max 1 (cK2 d L N)) (Real.sqrt N * cK2 d L N) ≤ K₂)
    (hp40 : p₁ / (β ^ (1 / 2 : ℝ) * δ) ≤ (3 * B₅ * K₂)⁻¹)
    (hrad : B₅ * β ^ (-(1 / 2 : ℝ)) * p₁ ≤ fluctRadius d L N)
    (ψh : unitPts G' → Rn N) :
    chiXi G (compWeight L a₁) ν δ (fluctPsi hG hG' (compWeight L a₁) aT ν D' β ψh) h₀ *
        chi22 G' δ D' (fluctPsi hG hG' (compWeight L a₁) aT ν D' β ψh) *
        chiFl (unitPts G') N p₁ ψh = chiFl (unitPts G') N p₁ ψh := by
  have hd0 : 0 < d := by have := H.hd; omega
  obtain ⟨hδ'1, -, hδ'c1, -⟩ := theta_consts hd0 hδ'0 hδ'
  have hDU1 : InUnionDomainR G' (thm73C1 d L N) ν D' := ⟨δ', hδ'0, hδ'1, hD'R⟩
  have hBreal := (criticalPoint_real ha₁ hG hG' (le_refl (k + 1)) H H' D' hDU1).1
  have hχ := (chiU_eq_one_iff _ _ _ _).1 hχu
  refine lemma25 ha₁ hG hG' H H' hδ'0 hδ' hD'R hh₀ (fluctPsi_layerConst hG hG' _ aT ν D' β ψh)
    hδ0 hfam hsm hχu hnorm hβ hp₁ hB5 hK2 hp40 hrad ψh ?_
  intro x i
  have hre : ((psiK hG hG' (compWeight L a₁) ν D').Ψ x i).im = 0 := (hBreal x i).1
  have him := fluctShift_im_zero hG' H' hδ'0 hδ'c1 hD'R hδ0 hχ hfam hsm β ψh x i
  apply Complex.ext
  · simp [fluctPsi]
  · simp [fluctPsi, hre, him]

end Field

end Balaban.Fluctuation
