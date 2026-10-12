/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.Def6AvgSumConds
public import Balaban.SmallField.Def6AvgMomLimit

/-!
# Reynolds averaging: the second moment of the averaged family

(H.5)(4) of I-6 for `avgFamily`: the second-moment sum of the averaged family is the mean over the
paving offsets of the second moments `MomY (offs t)` of the translated polymers of `T∞` through the
centres `offs t`, each of which vanishes (`momY_tsum_zero`).

* `D2_const_mul`, `tensB_GEs`, `tensB_avg`: the tensor of the averaged term is the mean of the
  tensors of the translated cut-off terms, which are the tensors of `GE` at the translate;
* `avgFamily_moment`: the moment condition for the averaged family.
-/

@[expose] public section

namespace Balaban.SmallField.Def6

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.Fluctuation
  Balaban.SmallField Filter Metric Set

section Calc

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem D2_const_mul {f : E → ℂ} {c : E} (hf : AnalyticAt ℂ f c) (a : ℂ) (v w : E) :
    D2 (fun x => a * f x) c v w = a * D2 f c v w := by
  unfold D2
  have h1 : fderiv ℂ (fun x => a * f x) =ᶠ[nhds c] fun x => a • fderiv ℂ f x := by
    filter_upwards [hf.eventually_analyticAt] with x hx
    rw [fderiv_const_mul hx.differentiableAt]
  rw [h1.fderiv_eq, fderiv_fun_const_smul hf.fderiv.differentiableAt]
  simp

end Calc

variable {d L m₁ k N : ℕ} [NeZero L] {ϱ : ℝ}

theorem shiftCfg_single (t : Site d) (X : Finset (Site d)) (x : ↥X) (i : Fin N) :
    shiftCfg t X (Pi.single (Sum.inl (x, i)) (1 : ℂ) : Cfg d N X) =
      (Pi.single (Sum.inl (⟨x.1 + t, add_mem_shiftFin x.1 x.2⟩, i)) (1 : ℂ) : Cfg d N (shiftFin t X)) := by
  ext (⟨⟨w, hw⟩, i'⟩ | i')
  · simp only [shiftCfg, reCfg_inl, Pi.single_apply, Sum.inl.injEq, Prod.mk.injEq, Subtype.mk.injEq]
    have : (w - t = x.1) ↔ (w = x.1 + t) := by
      constructor
      · intro h; rw [← h]; simp
      · intro h; rw [h]; simp
    simp only [Subtype.ext_iff, this]
  · simp [shiftCfg, reCfg_inr]

section Moment

variable {P : Consts} {β ν a : ℕ → ℝ} {Ek : ℕ → ℝ}
  {Tm : ∀ (N₁ : ℕ) [NeZero N₁], Terms d L N₁ m₁ k N ϱ}
  {ρd : ∀ (N₁ : ℕ) [NeZero N₁], (CTorus d L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) →
    (CTorus d L N₁ m₁ k → Fin N → ℝ) → ℝ}
  {j : ℕ}

variable (hF : IsSFFamily P β ν a Tm ρd Ek) (hn : MomNum d L N k j ϱ P) {i₀ i₁ : Fin N}
include hF hn

theorem GE_analyticAt_all {y : Site d} (X' : Finset (Site d)) :
    AnalyticAt ℂ (GE P β ν a Tm j i₀ (nuIdeal L k (ν k) j) y X') (refPt i₀ (nuIdeal L k (ν k) j) X') := by
  have hρ0 := liftRadius_pos (d := d) (L := L) (eps_pos hF.admissible.α₀_pos j) i₀
  by_cases h : InfPoly (L := L) (m₁ := m₁) (k := k) P.m₀ j X' ∧ y ∈ X'
  · exact GE_analyticAt hF hn h.1 h.2 (mem_ball_self hρ0)
  · have : GE P β ν a Tm j i₀ (nuIdeal L k (ν k) j) y X' = fun _ => 0 :=
      funext fun c => GE_eq_zero h _ c
    rw [this]; exact analyticAt_const

variable (hne : i₁ ≠ i₀)
include hne

/-- **The tensor of the translate**: the tensor of `GEs t X` is the tensor of `GE` at the centre
`offs t` of the translate `X + offs t`. -/
theorem tensB_GEs {Mb : ℕ} (t : Fin d → Fin Mb) (X : Finset (Site d)) (x x' : ↥X) :
    tensB i₀ i₁ (nuIdeal L k (ν k) j) X (GEs P β ν a Tm j i₀ (nuIdeal L k (ν k) j) t X) x x' =
      tensB i₀ i₁ (nuIdeal L k (ν k) j) (shiftFin (offs t) X)
        (GE P β ν a Tm j i₀ (nuIdeal L k (ν k) j) (offs t) (shiftFin (offs t) X))
        ⟨x.1 + offs t, add_mem_shiftFin x.1 x.2⟩ ⟨x'.1 + offs t, add_mem_shiftFin x'.1 x'.2⟩ := by
  have hρ0 := liftRadius_pos (d := d) (L := L) (eps_pos hF.admissible.α₀_pos j) i₀
  unfold tensB
  refine D2_congr_slice ((GEs_tubeHyp hF hn hne t X).analytic _ (mem_ball_self hρ0))
    (GE_analyticAt_all hF hn (y := offs t) (shiftFin (offs t) X)) (δ := 1) one_pos fun s t' _ _ => ?_
  unfold GEs
  congr 1
  have h1 := shiftCfg_single (N := N) (offs t) X x i₁
  have h2 := shiftCfg_single (N := N) (offs t) X x' i₁
  have e : ∀ (c c' c'' : Cfg d N X), shiftCfg (offs t) X (c + s • c' + t' • c'') =
      shiftCfg (offs t) X c + s • shiftCfg (offs t) X c' + t' • shiftCfg (offs t) X c'' := by
    intro c c' c''
    unfold shiftCfg
    rw [reCfg_add, reCfg_add, reCfg_smul, reCfg_smul]
  rw [e, h1, h2]
  unfold shiftCfg
  rw [reCfg_refPt]


omit hne in
theorem summable_MomY (y : Site d) :
    Summable fun X' : Finset (Site d) => MomY P β ν a Tm j i₀ i₁ y X' := by
  have hC : 0 ≤ momC (d := d) L m₁ P (liftRadius d L N P j) y * (24 * Real.exp 1) := by
    have := momC_nonneg hF (y := y) (L := L) (m₁ := m₁) (j := j)
    positivity
  refine Summable.of_norm ?_
  refine (summable_shapes (L := L) (m₁ := m₁) (m₀ := P.m₀) (j := j) hn.hjk (κ := P.κ - 1)
    (by linarith [hn.hκ, aEnt_nonneg d L]) y (MomY P β ν a Tm j i₀ i₁ y) hC
    (fun X' hy hX => MomY_bound hF hn hy hX)
    (fun X' h => MomY_eq_zero (fun h' => h ⟨h'.2, h'.1⟩))).1

/-- The equivalence of a polymer with its translate. -/
def shiftSub {Mb : ℕ} (t : Fin d → Fin Mb) (X : Finset (Site d)) : ↥X ≃ ↥(shiftFin (offs t) X) where
  toFun x := ⟨x.1 + offs t, add_mem_shiftFin x.1 x.2⟩
  invFun z := ⟨z.1 - offs t, mem_shiftFin.1 z.2⟩
  left_inv x := by ext; simp
  right_inv z := by ext; simp

/-- **The second moment of a translated cut-off term is that of `T∞` at the translate.** -/
theorem mom_GEs_eq {Mb : ℕ} (t : Fin d → Fin Mb) (X : Finset (Site d)) :
    ∑ x : ↥X, ∑ x' : ↥X, tensB i₀ i₁ (nuIdeal L k (ν k) j) X
        (GEs P β ν a Tm j i₀ (nuIdeal L k (ν k) j) t X) x x' *
        (∑ μ, (((x.1 μ - x'.1 μ : ℤ) : ℂ)) ^ 2) =
      MomY P β ν a Tm j i₀ i₁ (offs t) (shiftFin (offs t) X) := by
  unfold MomY
  refine Fintype.sum_equiv (shiftSub t X) _ _ fun x => ?_
  refine Fintype.sum_equiv (shiftSub t X) _ _ fun x' => ?_
  rw [tensB_GEs hF hn hne t X x x']
  have : ∀ μ, (((shiftSub t X x).1 μ - (shiftSub t X x').1 μ : ℤ) : ℂ) = ((x.1 μ - x'.1 μ : ℤ) : ℂ) := by
    intro μ
    simp [shiftSub]
  simp only [this]
  rfl

/-- **The tensor of the averaged term** is the mean of the tensors of the translated terms. -/
theorem tensB_avg
    (r : (↥(GG d L j) ⧸ KK d L P.m₀ m₁ j) → (Fin d → Fin (L ^ (P.m₀ + m₁))))
    (hr : ∀ (i₀ : Fin N) (νj : ℝ) (X : Finset (Site d)) (c : Cfg d N X),
      avgB P β ν a Tm j i₀ νj X c = (Fintype.card (↥(GG d L j) ⧸ KK d L P.m₀ m₁ j) : ℂ)⁻¹ *
        ∑ q, GEs P β ν a Tm j i₀ νj (r q) X c)
    (X : Finset (Site d)) (x x' : ↥X) :
    tensB i₀ i₁ (nuIdeal L k (ν k) j) X
        ((avgFamily P β ν a Tm j i₀ (nuIdeal L k (ν k) j) (liftRadius d L N P j)).term X) x x' =
      (Fintype.card (↥(GG d L j) ⧸ KK d L P.m₀ m₁ j) : ℂ)⁻¹ *
        ∑ q, tensB i₀ i₁ (nuIdeal L k (ν k) j) X
          (GEs P β ν a Tm j i₀ (nuIdeal L k (ν k) j) (r q) X) x x' := by
  have hρ0 := liftRadius_pos (d := d) (L := L) (eps_pos hF.admissible.α₀_pos j) i₀
  have hT := avgB_tubeHyp hF hn hne X
  set ρ := liftRadius d L N P j with hρ
  set νj := nuIdeal L k (ν k) j with hνj
  have hanaq : ∀ q, AnalyticAt ℂ (GEs P β ν a Tm j i₀ νj (r q) X) (refPt i₀ νj X) := fun q =>
    (GEs_tubeHyp hF hn hne (r q) X).analytic _ (mem_ball_self hρ0)
  have hsum : AnalyticAt ℂ (fun c => ∑ q, GEs P β ν a Tm j i₀ νj (r q) X c) (refPt i₀ νj X) :=
    Finset.analyticAt_fun_sum _ fun q _ => hanaq q
  have ha2 : AnalyticAt ℂ (fun c => (Fintype.card (↥(GG d L j) ⧸ KK d L P.m₀ m₁ j) : ℂ)⁻¹ *
      ∑ q, GEs P β ν a Tm j i₀ νj (r q) X c) (refPt i₀ νj X) := analyticAt_const.mul hsum
  have ha1 : AnalyticAt ℂ ((avgFamily P β ν a Tm j i₀ νj ρ).term X) (refPt i₀ νj X) :=
    hT.trickFn_analytic _ (ball_subset_tube i₀ νj ρ X (mem_ball_self hρ0))
  unfold tensB
  rw [D2_congr_slice (f₂ := fun c => (Fintype.card (↥(GG d L j) ⧸ KK d L P.m₀ m₁ j) : ℂ)⁻¹ *
      ∑ q, GEs P β ν a Tm j i₀ νj (r q) X c) (c₂ := refPt i₀ νj X)
    (v₂ := (Pi.single (Sum.inl (x, i₁)) 1 : Cfg d N X))
    (w₂ := (Pi.single (Sum.inl (x', i₁)) 1 : Cfg d N X)) ha1 ha2 (δ := ρ / 2) (by linarith)
    (fun s t' hs ht => ?_)]
  · rw [D2_const_mul hsum, D2_sum Finset.univ (fun q _ => hanaq q)]
  · set c : Cfg d N X := refPt i₀ νj X + s • (Pi.single (Sum.inl (x, i₁)) 1 : Cfg d N X) +
      t' • (Pi.single (Sum.inl (x', i₁)) 1 : Cfg d N X) with hc
    have hcb : c ∈ ball (refPt i₀ νj X) ρ := by
      rw [mem_ball, dist_eq_norm, hc, add_assoc, add_sub_cancel_left]
      refine lt_of_le_of_lt (norm_add_le _ _) ?_
      have e1 := norm_single_one_le (Sum.inl (x, i₁) : Idx d N X)
      have e2 := norm_single_one_le (Sum.inl (x', i₁) : Idx d N X)
      rw [norm_smul, norm_smul]
      nlinarith [norm_nonneg s, norm_nonneg t']
    show trickFn i₀ νj ρ (avgB P β ν a Tm j i₀ νj X) c = _
    rw [trickFn_of_ball hT hcb, hr i₀ νj X c]


/-- **The second moment of one polymer of the averaged family** is the mean over the offsets of
the second moments of `T∞` through the centres `offs (r q)` of the translates. -/
theorem avg_mom_term
    (r : (↥(GG d L j) ⧸ KK d L P.m₀ m₁ j) → (Fin d → Fin (L ^ (P.m₀ + m₁))))
    (hr : ∀ (i₀ : Fin N) (νj : ℝ) (X : Finset (Site d)) (c : Cfg d N X),
      avgB P β ν a Tm j i₀ νj X c = (Fintype.card (↥(GG d L j) ⧸ KK d L P.m₀ m₁ j) : ℂ)⁻¹ *
        ∑ q, GEs P β ν a Tm j i₀ νj (r q) X c) (X : Finset (Site d)) :
    ∑ x : ↥X, ∑ x' : ↥X, tensB i₀ i₁ (nuIdeal L k (ν k) j) X
        ((avgFamily P β ν a Tm j i₀ (nuIdeal L k (ν k) j) (liftRadius d L N P j)).term X) x x' *
        (∑ μ, (((x.1 μ - x'.1 μ : ℤ) : ℂ)) ^ 2) =
      (Fintype.card (↥(GG d L j) ⧸ KK d L P.m₀ m₁ j) : ℂ)⁻¹ *
        ∑ q, MomY P β ν a Tm j i₀ i₁ (offs (r q)) (shiftFin (offs (r q)) X) := by
  have hpt : ∀ x x' : ↥X, tensB i₀ i₁ (nuIdeal L k (ν k) j) X
        ((avgFamily P β ν a Tm j i₀ (nuIdeal L k (ν k) j) (liftRadius d L N P j)).term X) x x' *
        (∑ μ, (((x.1 μ - x'.1 μ : ℤ) : ℂ)) ^ 2) =
      (Fintype.card (↥(GG d L j) ⧸ KK d L P.m₀ m₁ j) : ℂ)⁻¹ *
        ∑ q, tensB i₀ i₁ (nuIdeal L k (ν k) j) X
          (GEs P β ν a Tm j i₀ (nuIdeal L k (ν k) j) (r q) X) x x' *
          (∑ μ, (((x.1 μ - x'.1 μ : ℤ) : ℂ)) ^ 2) := by
    intro x x'
    rw [tensB_avg hF hn hne r hr X x x', mul_assoc, Finset.sum_mul]
  rw [Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun x' _ => hpt x x']
  simp_rw [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_congr rfl fun x _ => Finset.sum_comm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => ?_
  exact mom_GEs_eq hF hn hne (r q) X

omit hF hn hne in
theorem mem_avgPolys_of_momY_ne_zero {Mb : ℕ} (hMb : Mb = L ^ (P.m₀ + m₁)) (t : Fin d → Fin Mb)
    {X : Finset (Site d)}
    (h : MomY P β ν a Tm j i₀ i₁ (offs t) (shiftFin (offs t) X) ≠ 0) :
    X ∈ avgPolys (d := d) L m₁ k P j := by
  subst hMb
  by_contra hXn
  apply h
  apply MomY_eq_zero
  rintro ⟨hI, hmem⟩
  exact hXn ⟨by simpa using mem_shiftFin.1 hmem, t, hI⟩

open Classical in
/-- **(H.5)(4) for the averaged family** (CLASS-RULINGS Q-A, Q-B (1)): the second moment of the
Reynolds average is the mean over the paving offsets of the second moments of `T∞` through the
centres `offs t`, each of which vanishes. -/
theorem avgFamily_moment :
    ∑' X : (avgFamily P β ν a Tm j i₀ (nuIdeal L k (ν k) j) (liftRadius d L N P j)).polys,
      ∑ x : ↥X.1, ∑ x' : ↥X.1, tensB i₀ i₁ (nuIdeal L k (ν k) j) X.1
        ((avgFamily P β ν a Tm j i₀ (nuIdeal L k (ν k) j) (liftRadius d L N P j)).term X.1) x x' *
        (∑ μ, (((x.1 μ - x'.1 μ : ℤ) : ℂ)) ^ 2) = 0 := by
  obtain ⟨r, hr⟩ := avgB_eq_sum hF hn.hj1 hn.hjk
  have h1 := fun X : (avgFamily P β ν a Tm j i₀ (nuIdeal L k (ν k) j) (liftRadius d L N P j)).polys =>
    avg_mom_term hF hn hne r hr X.1
  rw [tsum_congr h1]
  have hsupp : Function.support (fun X : Finset (Site d) =>
      (Fintype.card (↥(GG d L j) ⧸ KK d L P.m₀ m₁ j) : ℂ)⁻¹ *
        ∑ q, MomY P β ν a Tm j i₀ i₁ (offs (r q)) (shiftFin (offs (r q)) X)) ⊆
      avgPolys (d := d) L m₁ k P j := by
    intro X hX
    have hX' : ∑ q, MomY P β ν a Tm j i₀ i₁ (offs (r q)) (shiftFin (offs (r q)) X) ≠ 0 := by
      intro h0
      apply hX
      simp only [h0, mul_zero]
    obtain ⟨q, -, hq⟩ := Finset.exists_ne_zero_of_sum_ne_zero hX'
    exact mem_avgPolys_of_momY_ne_zero rfl (r q) hq
  have hsum : ∀ q ∈ (Finset.univ : Finset (↥(GG d L j) ⧸ KK d L P.m₀ m₁ j)),
      Summable fun X : Finset (Site d) =>
        MomY P β ν a Tm j i₀ i₁ (offs (r q)) (shiftFin (offs (r q)) X) :=
    fun q _ => ((shiftEquiv (offs (r q))).summable_iff.2
      (summable_MomY hF hn (i₀ := i₀) (i₁ := i₁) (offs (r q)))).congr fun X => rfl
  refine Eq.trans (tsum_subtype_eq_of_support_subset hsupp) ?_
  rw [tsum_mul_left, Summable.tsum_finsetSum hsum]
  have h2 : ∀ q : ↥(GG d L j) ⧸ KK d L P.m₀ m₁ j,
      ∑' X : Finset (Site d), MomY P β ν a Tm j i₀ i₁ (offs (r q)) (shiftFin (offs (r q)) X) = 0 := by
    intro q
    refine ((shiftEquiv (offs (r q))).tsum_eq
      (fun X' => MomY P β ν a Tm j i₀ i₁ (offs (r q)) X')).trans ?_
    exact momY_tsum_zero hF hn hne (offs (r q))
  rw [Finset.sum_congr rfl fun q _ => h2 q]
  simp

end Moment

end Balaban.SmallField.Def6
