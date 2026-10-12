/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.PsiZeroSmooth
public import Balaban.Background.MinimizerExpansion
import Mathlib

/-!
# The complex effective action of Lemma III.3.3 (analytic extension of `effAction`)

`effAction G a ψ = A_k(𝔹; ψ̃, φ_k(𝔹; ψ̃))` is defined with the real-valued action (norms squared) and the real background
`bgField`.  Its complex counterpart is the *bilinear* action `actionRawC` at the complex background `bgFieldC`
(Definition 5 (b)) of the lifted complex data:

* `effC`: `ψ ↦ actionRawC (rawMapC ψ) (bgFun (rawMapC ψ)).1`, with `bgFun` the analytic function of the raw data of
  Theorem 7.2;
* `effC_analyticAt`: `effC` is complex analytic at every real block field of the tube `Ψ̃(𝔹; δ)`, `δ ≤ min (c₀, c₁)`;
* `effC_ofReal`: on real block fields of the tube, `effC (ι ψ) = effAction ψ` (reality of the data and of the
  background field `bgField`, `action_eq_rawC_of_real`).
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background


set_option linter.unusedSectionVars false

section ActionC

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} (G : GeneratingSet d L N₀ k ϱ)

/-- The bilinear (complex-valued) action on the raw data `(Ψ, h)` and the field `φ`. -/
noncomputable def actionRawC (a : ℕ → ℝ) (ν : ℝ) (Ψ h : Torus d (N₀ * L ^ k) → Fin N → ℂ)
    (φ : G.Ω 1 × Fin N → ℂ) : ℂ :=
  (1 / 2) * ∑ x : G.Ω 1, ((a (G.layerIndex (x : Torus d (N₀ * L ^ k))) /
      ((L : ℝ) ^ G.layerIndex (x : Torus d (N₀ * L ^ k))) ^ 2 : ℝ) : ℂ) *
      ∑ i, (Ψ x i - blockAvg G φ x i) * (Ψ x i - blockAvg G φ x i) +
  (1 / 2) * ∑ x : Torus d (N₀ * L ^ k), ∑ μ : Fin d,
      (if x ∈ G.Ω 1 ∨ x + Pi.single μ 1 ∈ G.Ω 1 then
        ∑ i, (barField G Ψ φ (x + Pi.single μ 1) i - barField G Ψ φ x i) *
          (barField G Ψ φ (x + Pi.single μ 1) i - barField G Ψ φ x i) else 0) +
  (ν : ℂ) / 2 * ∑ x : G.Ω 1, ∑ i, (φ (x, i) - h x i) * (φ (x, i) - h x i)

theorem actionC_eq_rawC (a : ℕ → ℝ) (ν : ℝ) (D : BgData G N) (φ : G.Ω 1 × Fin N → ℂ) :
    actionC G a ν D φ = actionRawC G a ν D.Ψ D.h φ := rfl

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- Coordinate of an analytic Pi-valued map. -/
theorem analyticAt_apply {ι : Type*} {F : ι → Type*} [∀ i, NormedAddCommGroup (F i)]
    [∀ i, NormedSpace ℂ (F i)] [Fintype ι] {f : V → ∀ i, F i} {v : V} (hf : AnalyticAt ℂ f v) (i : ι) :
    AnalyticAt ℂ (fun w => f w i) v :=
  (ContinuousLinearMap.proj (R := ℂ) (φ := F) i).analyticAt _ |>.comp hf

theorem psiC_analyticAt_svec {φ : V → G.Ω 1 × Fin N → ℂ} {v : V} (hφ : AnalyticAt ℂ φ v)
    (y : Torus d (N₀ * L ^ k)) (i : Fin N) : AnalyticAt ℂ (fun v => svec G (φ v) y i) v := by
  by_cases hy : y ∈ G.Ω 1
  · have : (fun v => svec G (φ v) y i) = fun v => φ v (⟨y, hy⟩, i) :=
      funext fun v => svec_of_mem G (φ v) ⟨y, hy⟩ i
    rw [this]
    exact analyticAt_apply hφ _
  · have : (fun v => svec G (φ v) y i) = fun _ => 0 := funext fun v => svec_of_not_mem G (φ v) hy i
    rw [this]
    exact analyticAt_const

theorem psiC_analyticAt_blockAvg {φ : V → G.Ω 1 × Fin N → ℂ} {v : V} (hφ : AnalyticAt ℂ φ v)
    (x : Torus d (N₀ * L ^ k)) (i : Fin N) : AnalyticAt ℂ (fun v => blockAvg G (φ v) x i) v := by
  unfold blockAvg
  exact analyticAt_const.fun_mul (Finset.analyticAt_fun_sum _ fun y _ => psiC_analyticAt_svec G hφ y i)

theorem psiC_analyticAt_barField {Ψ : V → Torus d (N₀ * L ^ k) → Fin N → ℂ} {φ : V → G.Ω 1 × Fin N → ℂ}
    {v : V} (hΨ : AnalyticAt ℂ Ψ v) (hφ : AnalyticAt ℂ φ v) (x : Torus d (N₀ * L ^ k)) (i : Fin N) :
    AnalyticAt ℂ (fun v => barField G (Ψ v) (φ v) x i) v := by
  unfold barField
  by_cases hx : x ∈ G.Ω 1
  · simp only [hx, dite_true]
    exact analyticAt_apply hφ _
  · simp only [hx, dite_false]
    exact analyticAt_apply (analyticAt_apply hΨ x) i

theorem analyticAt_actionRawC (a : ℕ → ℝ) (ν : ℝ) {Ψ h : V → Torus d (N₀ * L ^ k) → Fin N → ℂ}
    {φ : V → G.Ω 1 × Fin N → ℂ} {v : V} (hΨ : AnalyticAt ℂ Ψ v) (hh : AnalyticAt ℂ h v)
    (hφ : AnalyticAt ℂ φ v) : AnalyticAt ℂ (fun v => actionRawC G a ν (Ψ v) (h v) (φ v)) v := by
  unfold actionRawC
  refine (((analyticAt_const.fun_mul ?_).fun_add (analyticAt_const.fun_mul ?_)).fun_add (analyticAt_const.fun_mul ?_))
  · refine Finset.analyticAt_fun_sum _ fun x _ => analyticAt_const.fun_mul (Finset.analyticAt_fun_sum _ fun i _ => ?_)
    have h1 := (analyticAt_apply (analyticAt_apply hΨ x) i).fun_sub (psiC_analyticAt_blockAvg G hφ x i)
    exact h1.fun_mul h1
  · refine Finset.analyticAt_fun_sum _ fun x _ => Finset.analyticAt_fun_sum _ fun μ _ => ?_
    by_cases hc : x ∈ G.Ω 1 ∨ x + Pi.single μ 1 ∈ G.Ω 1
    · simp only [hc, ite_true]
      refine Finset.analyticAt_fun_sum _ fun i _ => ?_
      have h1 := (psiC_analyticAt_barField G hΨ hφ (x + Pi.single μ 1) i).fun_sub (psiC_analyticAt_barField G hΨ hφ x i)
      exact h1.fun_mul h1
    · simp only [hc, ite_false]
      exact analyticAt_const
  · refine Finset.analyticAt_fun_sum _ fun x _ => Finset.analyticAt_fun_sum _ fun i _ => ?_
    have h1 := (analyticAt_apply hφ (x, i)).fun_sub (analyticAt_apply (analyticAt_apply hh x) i)
    exact h1.fun_mul h1

theorem ofReal_norm_sq_eq {z : ℂ} (hz : z.im = 0) : ((‖z‖ : ℝ) : ℂ) ^ 2 = z * z := by
  obtain ⟨r, rfl⟩ : ∃ r : ℝ, z = (r : ℂ) := ⟨z.re, Complex.ext (by simp) (by simpa using hz)⟩
  rw [Complex.norm_real, Real.norm_eq_abs, ← Complex.ofReal_pow, ← Complex.ofReal_mul, sq_abs, sq]

theorem psiC_svec_im {φ : G.Ω 1 × Fin N → ℂ} (hφ : ∀ p, (φ p).im = 0) (y : Torus d (N₀ * L ^ k)) (i : Fin N) :
    (svec G φ y i).im = 0 := by
  by_cases hy : y ∈ G.Ω 1
  · rw [svec_of_mem G φ ⟨y, hy⟩ i]; exact hφ _
  · rw [svec_of_not_mem G φ hy i]; simp

theorem psiC_blockAvg_im {φ : G.Ω 1 × Fin N → ℂ} (hφ : ∀ p, (φ p).im = 0) (x : Torus d (N₀ * L ^ k)) (i : Fin N) :
    (blockAvg G φ x i).im = 0 := by
  unfold blockAvg
  rw [Complex.im_ofReal_mul, Complex.im_sum]
  simp [psiC_svec_im G hφ]

theorem psiC_barField_im {Ψ : Torus d (N₀ * L ^ k) → Fin N → ℂ} {φ : G.Ω 1 × Fin N → ℂ}
    (hΨ : ∀ x i, (Ψ x i).im = 0) (hφ : ∀ p, (φ p).im = 0) (x : Torus d (N₀ * L ^ k)) (i : Fin N) :
    (barField G Ψ φ x i).im = 0 := by
  unfold barField
  by_cases hx : x ∈ G.Ω 1
  · simp only [hx, dite_true]; exact hφ _
  · simp only [hx, dite_false]; exact hΨ x i

/-- On real data and a real field the bilinear action is the action. -/
theorem action_eq_rawC_of_real (a : ℕ → ℝ) (ν : ℝ) (D : BgData G N) (hD : D.IsReal)
    (φ : G.Ω 1 × Fin N → ℂ) (hφ : ∀ p, (φ p).im = 0) :
    ((action G a ν D φ : ℝ) : ℂ) = actionRawC G a ν D.Ψ D.h φ := by
  have e1 : ∀ x i, ((‖D.Ψ x i - blockAvg G φ x i‖ : ℝ) : ℂ) ^ 2 =
      (D.Ψ x i - blockAvg G φ x i) * (D.Ψ x i - blockAvg G φ x i) := fun x i =>
    ofReal_norm_sq_eq (by simp [(hD x i).1, psiC_blockAvg_im G hφ x i])
  have e2 : ∀ x μ i, ((‖barField G D.Ψ φ (x + Pi.single μ 1) i - barField G D.Ψ φ x i‖ : ℝ) : ℂ) ^ 2 =
      (barField G D.Ψ φ (x + Pi.single μ 1) i - barField G D.Ψ φ x i) *
        (barField G D.Ψ φ (x + Pi.single μ 1) i - barField G D.Ψ φ x i) := fun x μ i =>
    ofReal_norm_sq_eq (by
      simp [psiC_barField_im G (fun x i => (hD x i).1) hφ])
  have e3 : ∀ (x : G.Ω 1) i, ((‖φ (x, i) - D.h x i‖ : ℝ) : ℂ) ^ 2 = (φ (x, i) - D.h x i) * (φ (x, i) - D.h x i) :=
    fun x i => ofReal_norm_sq_eq (by simp [hφ, (hD x i).2])
  unfold action actionRawC
  push_cast
  simp only [apply_ite (fun r : ℝ => (r : ℂ)), Complex.ofReal_zero, Complex.ofReal_sum, Complex.ofReal_pow]
  simp_rw [e1, e2, e3]

end ActionC

section Eff

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} (G : GeneratingSet d L N₀ k ϱ) (a : ℕ → ℝ)

/-- Complex block fields `ψ_k : 𝕋^{(k)} → ℂ^N`. -/
abbrev BlockFieldC (d L N₀ k N : ℕ) : Type := Torus d (N₀ * L ^ (k - k)) → Fin N → ℂ

/-- The raw data `(Ψ, h̃)` of a complex block field. -/
noncomputable def rawMapC (ψ : BlockFieldC d L N₀ k N) : RawData d L N₀ k N :=
  ((dataC G ψ).Ψ, (dataC G ψ).h)

theorem rawMapC_ofReal (ψ : BlockField d L N₀ k N) :
    rawMapC G (fun z i => (ψ z i : ℂ)) = rawMap G ψ := rfl

theorem analyticAt_rawMapC (ψ : BlockFieldC d L N₀ k N) : AnalyticAt ℂ (rawMapC G (N := N)) ψ := by
  classical
  refine AnalyticAt.prod ?_ ?_ <;> refine AnalyticAt.pi fun x => AnalyticAt.pi fun i => ?_
  · by_cases hx : x ∈ dataSites G
    · have : (fun ψ : BlockFieldC d L N₀ k N => (dataC G ψ).Ψ x i) =
          fun ψ => ψ (jBlock d L N₀ k k x) i :=
        funext fun ψ => congrFun (liftSingle_Ψ G ψ 0 hx) i
      rw [this]
      exact analyticAt_apply (analyticAt_apply analyticAt_id (jBlock d L N₀ k k x)) i
    · have : (fun ψ : BlockFieldC d L N₀ k N => (dataC G ψ).Ψ x i) = fun _ => 0 :=
        funext fun ψ => by simp [(dataC G ψ).Ψ_zero x hx]
      rw [this]
      exact analyticAt_const
  · have : (fun ψ : BlockFieldC d L N₀ k N => (dataC G ψ).h x i) = fun _ => 0 := by
      funext ψ
      by_cases hx : x ∈ G.Ω 1
      · exact congrFun (liftSingle_h G ψ 0 hx) i
      · simp [(dataC G ψ).h_zero x hx]
    rw [this]
    exact analyticAt_const

variable {a} (H : BgHyp d L k ϱ a 0)

/-- The analytic function of the raw data returning the complex background `(bgFieldC, bgMultC)`
(Theorem 7.2, analyticity). -/
noncomputable def bgFun : RawData d L N₀ k N → (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ) :=
  (theorem72_analytic (G := G) (N := N) H).choose

theorem bgFun_analytic : AnalyticOnNhd ℂ (bgFun G H) {p | ∃ D : BgData G N,
        InUnionDomainC G (bgC0 d L N) (bgC1 d L N) 0 D ∧ p = (D.Ψ, D.h)} :=
  (theorem72_analytic (G := G) (N := N) H).choose_spec.1

theorem bgFun_eq (D : BgData G N) (hD : InUnionDomainC G (bgC0 d L N) (bgC1 d L N) 0 D) :
    bgFun G H (D.Ψ, D.h) = (bgFieldC G a 0 (bgC0 d L N) D, bgMultC G a 0 (bgC0 d L N) D) :=
  (theorem72_analytic (G := G) (N := N) H).choose_spec.2 D hD

/-- **The complex effective action**: `ψ ↦ A^C_k(𝔹_k; ψ̃, φ^C_k(𝔹_k; ψ̃))`, the bilinear action at the complex
background field `bgFieldC` of the lifted complex data. -/
noncomputable def effC (ψ : BlockFieldC d L N₀ k N) : ℂ :=
  actionRawC G a 0 (rawMapC G ψ).1 (rawMapC G ψ).2 (bgFun G H (rawMapC G ψ)).1

/-- The complex effective action is analytic at the real points of the tube. -/
theorem effC_analyticAt {δ : ℝ} (hδ : 0 < δ) (hδ0 : δ ≤ bgC0 d L N) (hδ1 : δ ≤ bgC1 d L N)
    {ψ : BlockField d L N₀ k N} (ht : TubeOn G Set.univ δ ψ) :
    AnalyticAt ℂ (effC G H) (fun z i => (ψ z i : ℂ)) := by
  have hR : AnalyticAt ℂ (rawMapC G (N := N)) (fun z i => (ψ z i : ℂ)) :=
    analyticAt_rawMapC (N := N) G _
  have hB : AnalyticAt ℂ (bgFun G H) (rawMapC G (fun z i => (ψ z i : ℂ))) :=
    bgFun_analytic G H _ ⟨dataR G ψ, inUnionDomainC_of_tube G hδ hδ0 hδ1 ht, rfl⟩
  exact analyticAt_actionRawC G a 0 (analyticAt_fst.comp hR) (analyticAt_snd.comp hR)
    (analyticAt_fst.comp (hB.comp hR))


/-- The Def-5 background field of real tube data is real. -/
theorem bgField_im (H : BgHyp d L k ϱ a 0) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ bgC1 d L N) {ψ : BlockField d L N₀ k N}
    (ht : TubeOn G Set.univ δ ψ) (p : G.Ω 1 × Fin N) : (bgField G a 0 (dataR G ψ) p).im = 0 := by
  obtain ⟨φ, α, hs, hb, hu, hunit, hmin, hmu⟩ := bg_real H hδ hδ1 (inDomainR_of_tube G hδ ht)
  rw [bgField_eq hmin hmu]
  exact (hunit p.1).1 p.2

/-- **The complex effective action extends the real one**: on the real tube, `effC (ι ψ) = effAction ψ`. -/
theorem effC_ofReal {δ : ℝ} (hδ : 0 < δ) (hδ0 : δ ≤ bgC0 d L N) (hδ1 : δ ≤ bgC1 d L N)
    {ψ : BlockField d L N₀ k N} (ht : TubeOn G Set.univ δ ψ) :
    effC G H (fun z i => (ψ z i : ℂ)) = (effAction G a ψ : ℂ) := by
  have hR := inUnionDomainR_of_tube G hδ hδ1 ht
  have hC := inUnionDomainC_of_tube G hδ hδ0 hδ1 ht
  have hbg : (bgFun G H (rawMapC G (fun z i => (ψ z i : ℂ)))).1 = bgField G a 0 (dataR G ψ) := by
    have h1 : rawMapC G (fun z i => (ψ z i : ℂ)) = ((dataR G ψ).Ψ, (dataR G ψ).h) := rfl
    rw [h1, bgFun_eq G H _ hC]
    exact (theorem72_real H hR).1
  unfold effC
  rw [hbg]
  have hD : (dataR G ψ).IsReal := isReal_of_inDomainR (inDomainR_of_tube G hδ ht)
  rw [effAction, action_eq_rawC_of_real G a 0 (dataR G ψ) hD _ (bgField_im G H hδ hδ1 ht)]
  rfl

end Eff

end Balaban.LargeField
