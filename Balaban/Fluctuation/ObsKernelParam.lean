/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.ObsRowCoeff

/-!
# The observable kernel as an analytic, local, bounded function of the raw datum

Zero class of the step.  For a function `E (r, ψ̂)` analytic in the raw datum `r` and the hat
variable `ψ̂`, the coordinate derivative `hatCoeff E r e = d/dζ|₀ E (r, ζ • e)` is analytic in `r`
(`hatCoeff_analyticOnNhd`), bounded by the Cauchy estimate uniformly in `r`
(`norm_hatCoeff_le_of_forall`), and depends on `r` only through the function `E (r, ·)`
(`hatCoeff_congr`).

For the family `Ev` of the sharp hat expansion, `obsHker_param_of_Ev` shows that the finite
kernel `obsHker 𝒴 (obsRowCoeff S Ev D m) m₀ T`, as a function of the raw datum `rawOf D`, is
analytic, local on the thickening of the domains carrying the label `T`, and bounded by the
kernel bound of `ObsMarkHalf`, uniformly in the datum.  The kernel does not involve the source.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Polymer Balaban.SmallField.Def6 Balaban.Multiscale
  Balaban.Background Balaban.SmallField Metric

/-! ### The coefficient as a function of the parameter -/

section Generic

variable {R P : Type*} [NormedAddCommGroup R] [NormedSpace ℂ R] [Fintype P]

/-- **Analyticity in the parameter.**  If `E` is analytic at every point of `A × {‖ψ p‖ ≤ cψ}`,
then `r ↦ hatCoeff E r e` is analytic at every point of `A`. -/
theorem hatCoeff_analyticOnNhd {E : R × (P → ℂ) → ℂ} {A : Set R} {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hE : AnalyticOnNhd ℂ E (A ×ˢ {ψ : P → ℂ | ∀ p, ‖ψ p‖ ≤ cψ})) (e : P → ℂ) :
    AnalyticOnNhd ℂ (fun r => hatCoeff E r e) A := by
  intro r₀ hr₀
  set G : R × ℂ → ℂ := fun p => E (p.1, p.2 • e) with hGdef
  have hmap : AnalyticAt ℂ (fun p : R × ℂ => (p.1, p.2 • e)) (r₀, 0) :=
    AnalyticAt.prod analyticAt_fst (AnalyticAt.smul analyticAt_snd analyticAt_const)
  have hmem : (r₀, (0 : ℂ) • e) ∈ A ×ˢ {ψ : P → ℂ | ∀ p, ‖ψ p‖ ≤ cψ} :=
    ⟨hr₀, fun p => by simpa using hcψ⟩
  have hG : AnalyticAt ℂ G (r₀, 0) := (hE _ hmem).comp_of_eq hmap (by simp)
  have hf : AnalyticAt ℂ (fun p : R × ℂ => fderiv ℂ G p (0, 1)) (r₀, 0) :=
    AnalyticAt.comp ((ContinuousLinearMap.apply ℂ ℂ ((0 : R), (1 : ℂ))).analyticAt (fderiv ℂ G (r₀, 0)))
      hG.fderiv
  have hline : AnalyticAt ℂ (fun r : R => (r, (0 : ℂ))) r₀ :=
    AnalyticAt.prod analyticAt_id analyticAt_const
  have h2 : AnalyticAt ℂ (fun r : R => fderiv ℂ G (r, 0) (0, 1)) r₀ :=
    hf.comp_of_eq hline rfl
  refine h2.congr ?_
  have hev : ∀ᶠ p in nhds ((r₀, (0 : ℂ))), AnalyticAt ℂ G p := hG.eventually_analyticAt
  have hcont : Filter.Tendsto (fun r : R => (r, (0 : ℂ))) (nhds r₀) (nhds (r₀, 0)) :=
    (continuous_id.prodMk continuous_const).tendsto r₀
  filter_upwards [hcont.eventually hev] with r hr
  have hd : HasFDerivAt G (fderiv ℂ G (r, 0)) (r, 0) := hr.differentiableAt.hasFDerivAt
  have hl : HasDerivAt (fun ζ : ℂ => (r, ζ)) ((0 : R), (1 : ℂ)) 0 :=
    (hasDerivAt_const (0 : ℂ) r).prodMk (hasDerivAt_id 0)
  have := hd.comp_hasDerivAt (0 : ℂ) hl
  exact this.deriv.symm

/-- **Cauchy bound, uniform in the parameter.** -/
theorem norm_hatCoeff_le_of_forall {E : R × (P → ℂ) → ℂ} {A : Set R} {cψ B : ℝ} (hcψ : 0 < cψ)
    (hE : AnalyticOnNhd ℂ E (A ×ˢ {ψ : P → ℂ | ∀ p, ‖ψ p‖ ≤ cψ}))
    (hB : ∀ u ∈ A ×ˢ {ψ : P → ℂ | ∀ p, ‖ψ p‖ ≤ cψ}, ‖E u‖ ≤ B) {e : P → ℂ}
    (he : ∀ p, ‖e p‖ ≤ 1) : ∀ r ∈ A, ‖hatCoeff E r e‖ ≤ B / cψ :=
  fun _ hr => norm_hatCoeff_le hcψ hr hE hB he

omit [NormedAddCommGroup R] [NormedSpace ℂ R] [Fintype P] in
/-- **Locality**: the coefficient depends on `r` only through the slice `ζ ↦ E (r, ζ • e)` near
`0`; in particular it is the same for two parameters with `E r = E r'` on the hat ball. -/
theorem hatCoeff_congr {E : R × (P → ℂ) → ℂ} {cψ : ℝ} (hcψ : 0 < cψ) {r r' : R} {e : P → ℂ}
    (h : ∀ ζ : ℂ, ‖ζ‖ < cψ → E (r, ζ • e) = E (r', ζ • e)) :
    hatCoeff E r e = hatCoeff E r' e := by
  unfold hatCoeff
  have : (fun ζ : ℂ => E (r, ζ • e)) =ᶠ[nhds 0] fun ζ => E (r', ζ • e) := by
    filter_upwards [ball_mem_nhds (0 : ℂ) hcψ] with ζ hζ
    exact h ζ (by simpa using hζ)
  exact this.deriv_eq

end Generic

/-! ### The kernel as a function of the raw datum -/

section Kernel

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ)

/-- **The observable kernel, as a function of the raw datum.**

Hypotheses on the family `Ev` (on a set `A` of raw data, e.g. `A = XiCRaw …`, and the hat ball of
radius `cψ`): analyticity, `AgHatDir` locality, and the decay bound.  These are the clauses 2, 3, 4
of the conclusion of `obsRowCoeff_of_sharpHat` (equivalently the conclusions of
`fsite_expansion_hat_dir`); `B = Q δ₁`.  For `𝒴` a family of domains with `IsDj` and `L^m₀ ∣ N₁`,
and every mark `m` and label set `T`, with `kerr r := obsHker 𝒴 (fun Y => hatCoeff (Ev Y) r
(obsUnitVec S m)) m₀ T`:

* (i) `kerr` is analytic at every point of `A`; for a datum `D` with `rawOf D ∈ A`, `kerr (rawOf D)`
  is the kernel `obsHker 𝒴 (obsRowCoeff S Ev D m) m₀ T` of `ObsMarkHalf`;
* (ii) if `r, r' ∈ A` agree (`agreeOn`) on the thickening `thickSet S.G' Z` of a set `Z` containing
  every domain of `𝒴` with label `T`, then `kerr r = kerr r'`;
* (iii) `‖kerr r‖ ≤ (B / cψ) * exp (-(2 κdec) * dExt T)` for every `r ∈ A`. -/
theorem obsHker_param_of_Ev {m₀ : ℕ}
    {A : Set (RawData d L (N₁ * L ^ m₁) (k + 1) N)} {cψ B κdec : ℝ} (hcψ : 0 < cψ) (hB : 0 ≤ B)
    (hκdec : 0 ≤ κdec)
    (Ev : Set (CTorus d L N₁ m₁ (k + 1)) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (S.U × Fin N → ℂ) → ℂ)
    (hd : ∀ Y, ∀ u ∈ A ×ˢ {ψh : S.U × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
      ∀ u' ∈ A ×ˢ {ψh : S.U × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        AgHatDir S.hG' Y u u' → Ev Y u = Ev Y u')
    (hb : ∀ Y, ∀ u ∈ A ×ˢ {ψh : S.U × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
      ‖Ev Y u‖ ≤ B * Real.exp (-2 * κdec * treeLenCov S.G' m₀ Y))
    (ha : ∀ Y, AnalyticOnNhd ℂ (Ev Y) (A ×ˢ {ψh : S.U × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ}))
    (𝒴 : Finset (Set (CTorus d L N₁ m₁ (k + 1)))) (hN : L ^ m₀ ∣ N₁)
    (hdj : ∀ Y ∈ 𝒴, IsDj m₀ (k + 1) Y) (m : ObsMarkIdx S)
    (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ)) :
    AnalyticOnNhd ℂ (fun r => obsHker 𝒴 (fun Y => hatCoeff (Ev Y) r (obsUnitVec S m)) m₀ T) A ∧
    (∀ D : BgData S.G' N, rawOf D ∈ A →
      obsHker 𝒴 (obsRowCoeff S Ev D m) m₀ T =
        obsHker 𝒴 (fun Y => hatCoeff (Ev Y) (rawOf D) (obsUnitVec S m)) m₀ T) ∧
    (∀ Z : Set (CTorus d L N₁ m₁ (k + 1)), (∀ Y ∈ 𝒴, obsRowLabel m₀ (k + 1) Y = T → Y ⊆ Z) →
      ∀ r ∈ A, ∀ r' ∈ A, agreeOn (thickSet S.G' Z) r r' →
        obsHker 𝒴 (fun Y => hatCoeff (Ev Y) r (obsUnitVec S m)) m₀ T =
          obsHker 𝒴 (fun Y => hatCoeff (Ev Y) r' (obsUnitVec S m)) m₀ T) ∧
    (∀ r ∈ A, ‖obsHker 𝒴 (fun Y => hatCoeff (Ev Y) r (obsUnitVec S m)) m₀ T‖ ≤
        (B / cψ) * Real.exp (-(2 * κdec) * dExt T)) := by
  classical
  have he := norm_obsUnitVec_le S m
  refine ⟨?_, fun D _ => rfl, ?_, ?_⟩
  · unfold obsHker
    have := Finset.analyticOnNhd_sum (𝕜 := ℂ) (𝒴.filter (fun Y => obsRowLabel m₀ (k + 1) Y = T))
      (fun Y _ => hatCoeff_analyticOnNhd hcψ.le (ha Y) (obsUnitVec S m))
    convert this using 1
    ext r
    simp [Finset.sum_apply]
  · intro Z hZ r hr r' hr' hag
    unfold obsHker
    refine Finset.sum_congr rfl fun Y hY => ?_
    rw [Finset.mem_filter] at hY
    refine hatCoeff_congr hcψ fun ζ hζ => hd Y (r, ζ • obsUnitVec S m) ⟨hr, smul_mem_ball he hζ⟩ (r', ζ • obsUnitVec S m)
      ⟨hr', smul_mem_ball he hζ⟩
      ⟨agreeOn_mono (thickSet_mono (hZ Y hY.1 hY.2)) hag, fun _ _ _ => rfl⟩
  · intro r hr
    refine norm_obsHker_le hN hdj (div_nonneg hB hcψ.le) (by linarith) (fun Y _ => ?_) T
    have := norm_hatCoeff_le hcψ hr (ha Y) (hb Y) he
    rw [← treeLenCov_eq_treeLenCovOne S.hG' m₀ Y]
    rw [show -(2 * κdec) * treeLenCov S.G' m₀ Y = -2 * κdec * treeLenCov S.G' m₀ Y by ring]
    rwa [mul_div_right_comm] at this

end Kernel

end Balaban.Fluctuation
