/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.PsiZeroHessEnv
public import Balaban.LargeField.R.PsiZeroHessSmooth

/-!
# Envelope formula and Hessian lower bound from the sandwich (PSIZERO-HESS §5, rows 3-4)

`effOn_derivs`: for a perturbation `v` supported over the top layer, the derivative of `effOn` in the direction `v`
is the first variation `b₁(v)` (the envelope formula (2.5)), and the second derivative is bounded below by `2c`
whenever the quadratic form `A(tJv, τ) + ½ ∑ Re α |τ|²` of the Lagrangian expansion is bounded below by `c t²`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background Filter Topology

section Grad

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ k ϱ} {a : ℕ → ℝ}
  {Z : Finset (Torus d (N₀ * L ^ (k - k)))}

theorem topTangent_isReal (v : SuppSpace Z N) : (topTangent G v).IsReal := by
  intro x i
  refine ⟨?_, by simp [topTangent_h]⟩
  by_cases hx : x ∈ dataSites G
  · simp [topTangent_Ψ v hx]
  · simp [(topTangent G v).Ψ_zero x hx]

theorem topTangent_zero_off (hΩ : OverTop G (Z : Set (Torus d (N₀ * L ^ (k - k))))) (hk : 1 ≤ k)
    (v : SuppSpace Z N) {x : Torus d (N₀ * L ^ k)} (hx : x ∉ G.Ω 1) : (topTangent G v).Ψ x = 0 := by
  funext i
  exact topLift_zero_collar hΩ v (fun h => hx (G.Ω_antitone le_rfl hk (by omega) h)) i

/-- Homogeneity of the action of a pure tangent datum at the field `0`. -/
theorem action_zero_line_scale (E : BgData G N) (hE : ∀ x, x ∉ G.Ω 1 → E.Ψ x = 0)
    (hEh : ∀ x, E.h x = 0) (t : ℝ) :
    action G a 0 ((bgZero G N).lineAt E (t : ℂ)) 0 = t ^ 2 * action G a 0 ((bgZero G N).lineAt E (1 : ℝ)) 0 := by
  have hb : ∀ s : ℂ, barField G ((bgZero G N).lineAt E s).Ψ (0 : G.Ω 1 × Fin N → ℂ) = 0 := fun s => by
    rw [barField_line (bgZero G N) E hE s]
    exact barField_zero _ (fun x _ => rfl)
  unfold action
  rw [hb, hb, blockAvg_zero]
  simp only [BgData.lineAt, bgZero, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, zero_add,
    hEh, mul_zero, sub_zero, sub_self, norm_zero, ite_self, Finset.sum_const_zero,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div, add_zero, norm_mul,
    Complex.norm_real, Complex.ofReal_one, one_mul, mul_pow, Real.norm_eq_abs, sq_abs]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.mul_sum]
  ring

/-- **Envelope formula and Hessian lower bound (rows 3-4).**  Let `ψ` be a block field of the tube
`Ψ̃(𝔹_k; η)` and `v` a perturbation supported in a box `Z` over the top layer.  Then the derivative of `effOn`
at `ψ↾Z` in the direction `v` is the first variation `b₁(v)`, and its second derivative is `≥ 2c` as soon as the
Lagrangian quadratic form is `≥ c t²` (hypothesis `hQ`, proved in `PsiZeroHessCoerc`). -/
theorem effOn_derivs (H : BgHyp d L k ϱ a 0) (hk : 1 ≤ k) {η : ℝ} (hη : 0 < η) (hη0 : η ≤ bgC0 d L N)
    (hη1 : η ≤ bgC1 d L N) (hΩ : OverTop G (Z : Set (Torus d (N₀ * L ^ (k - k)))))
    {ψ : BlockField d L N₀ k N} (ht : TubeOn G Set.univ η ψ) (v : SuppSpace Z N) (c : ℝ)
    (hQ : ∀ (t : ℝ) (τ : G.Ω 1 × Fin N → ℂ), (∀ (x : G.Ω 1) i, (τ (x, i)).im = 0) →
      c * t ^ 2 ≤ action G a 0 ((bgZero G N).lineAt (topTangent G v) (t : ℂ)) τ +
        1 / 2 * ∑ x : G.Ω 1, (bgMult G a 0 (dataR G ψ) x).re * ∑ i, ‖τ (x, i)‖ ^ 2) :
    fderiv ℝ (effOn G a Z ψ) (restrictSupp Z ψ) v =
        (firstVar a (dataR G ψ) (topTangent G v) (bgField G a 0 (dataR G ψ))).re ∧
      2 * c ≤ fderiv ℝ (fderiv ℝ (effOn G a Z ψ)) (restrictSupp Z ψ) v v := by
  set x0 := restrictSupp Z ψ with hx0def
  have hm0 : mergeField Z ψ x0 = ψ := mergeField_restrict (fun _ _ => rfl)
  have hx0 : TubeOn G Set.univ η (mergeField Z ψ x0) := by rw [hm0]; exact ht
  have hF : ContDiffAt ℝ 2 (effOn G a Z ψ) x0 := contDiffAt_effOn G Z H hη hη0 hη1 ψ hx0
  obtain ⟨hd, hd2⟩ := line_derivs hF v
  set E := topTangent G v with hE
  set D := dataR G ψ with hD
  have hlineC : Continuous fun t : ℝ => x0 + t • v := by fun_prop
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), TubeOn G Set.univ η (mergeField Z ψ (x0 + t • v)) := by
    have hU := isOpen_tube_merge G Z ψ η
    have : ContinuousAt (fun t : ℝ => x0 + t • v) 0 := hlineC.continuousAt
    exact this.eventually (hU.mem_nhds (by simpa using hx0))
  have hDdom : InUnionDomainR G (bgC1 d L N) 0 D := inUnionDomainR_of_tube G hη hη1 ht
  have hEo : ∀ x, x ∉ G.Ω 1 → E.Ψ x = 0 := fun x hx => topTangent_zero_off hΩ hk v hx
  have hEh : ∀ x, E.h x = 0 := fun x => funext fun i => topTangent_h v x i
  have hER : E.IsReal := topTangent_isReal v
  have hg0 : effOn G a Z ψ (x0 + (0 : ℝ) • v) = action G a 0 D (bgField G a 0 D) := by
    simp only [zero_smul, add_zero]
    show effAction G a (mergeField Z ψ x0) = _
    rw [hm0]; rfl
  have hsand : ∀ᶠ t in 𝓝 (0 : ℝ),
      effOn G a Z ψ (x0 + t • v) ≤ effOn G a Z ψ (x0 + (0 : ℝ) • v) +
          (firstVar a D E (bgField G a 0 D)).re * t +
          action G a 0 ((bgZero G N).lineAt E (1 : ℝ)) 0 * t ^ 2 ∧
        c * t ^ 2 + effOn G a Z ψ (x0 + (0 : ℝ) • v) + (firstVar a D E (bgField G a 0 D)).re * t ≤
          effOn G a Z ψ (x0 + t • v) := by
    filter_upwards [hev] with t htube
    have hDt : InUnionDomainR G (bgC1 d L N) 0 (D.lineAt E (t : ℂ)) := by
      have := inUnionDomainR_of_tube G hη hη1 htube
      rwa [hD, hE, ← dataR_merge_line ψ v t]
    have hFt : effOn G a Z ψ (x0 + t • v) =
        action G a 0 (D.lineAt E (t : ℂ)) (bgField G a 0 (D.lineAt E (t : ℂ))) := by
      show effAction G a (mergeField Z ψ (x0 + t • v)) = _
      unfold effAction
      rw [hD, hE, ← dataR_merge_line ψ v t]
    obtain ⟨h1, h2⟩ := effAction_sandwich H hDdom hER hEo hEh t hDt
    have hsc := action_zero_line_scale (a := a) E hEo hEh t
    have hrel : ∀ x i, ((bgField G a 0 (D.lineAt E (t : ℂ)) - bgField G a 0 D) (x, i)).im = 0 := by
      obtain ⟨-, hU0, -, -⟩ := theorem71 H hDdom
      obtain ⟨-, hUt, -, -⟩ := theorem71 H hDt
      intro x i
      simp [(hUt x).1 i, (hU0 x).1 i]
    have hq := hQ t _ hrel
    rw [hFt, hg0]
    constructor
    · rw [hsc] at h1; linarith
    · rw [h2]; linarith
  have hup : ∀ᶠ t in 𝓝 (0 : ℝ), (fun s : ℝ => effOn G a Z ψ (x0 + s • v)) t ≤
      (fun s : ℝ => effOn G a Z ψ (x0 + s • v)) 0 + (firstVar a D E (bgField G a 0 D)).re * t +
        action G a 0 ((bgZero G N).lineAt E (1 : ℝ)) 0 * t ^ 2 := by
    filter_upwards [hsand] with t ht; exact ht.1
  have hlo : ∀ᶠ t in 𝓝 (0 : ℝ), (fun s : ℝ => effOn G a Z ψ (x0 + s • v)) 0 +
      (firstVar a D E (bgField G a 0 D)).re * t + c * t ^ 2 ≤
        (fun s : ℝ => effOn G a Z ψ (x0 + s • v)) t := by
    filter_upwards [hsand] with t ht; linarith [ht.2]
  have := hess_of_sandwich hd hd2 hup hlo
  simpa using this

end Grad

end Balaban.LargeField
