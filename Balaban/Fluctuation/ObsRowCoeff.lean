/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.SharpVF
public import Balaban.Fluctuation.ObsRowLabels
public import Balaban.Fluctuation.ObsCauchyTwoOrders
public import Balaban.Fluctuation.Prop33Level

/-!
# Coordinate-derivative coefficients of the sharp hat terms and the observable kernel

Zero class of the step.  Under the premises of the landed sharp hat expansion
`fsite_expansion_hat_dir` (carried verbatim, with the generating set `Gp = S.G'` of a step
setting `S`), let `Ev Y` be its terms, indexed by the polymer domains `Y`.  For a mark
`m = (u, a) : ObsMarkIdx S` let `e_{u,a}` (`obsUnitVec`) be the hat vector with `1` at the
coordinate `(u, a)` and `0` elsewhere (sup norm `1` for the norm in which the hat ball
`{ψ̂ | ∀ p, ‖ψ̂ p‖ ≤ c_ψ}` is defined).

* `obsRowCoeff`: `a_Y(m) = d/dζ|₀ Ev Y (rawOf D, ζ • e_m)`.
* `deriv_slice_sum`: `Σ_Y a_Y = d/dζ|₀ F(ζ • e_m)` for the expanded function `F`.
* `norm_hatCoeff_le`: Cauchy estimate `‖a_Y‖ ≤ B_Y / c_ψ` from `norm_deriv_zero_le`.
* `hatCoeff_eq_zero_of_local`: `a_Y = 0` unless `Y` contains a site of the unit point `u`
  (by `AgHatDir`).
* `obsHker`: the kernel indexed by cube labels,
  `h(m, T) = Σ_{Y, obsRowLabel Y = T} a_Y(m)`; at most one `Y` contributes
  (`obsRowLabel_injective`); its sum over `T`, its two support clauses and its decay bound in
  `dExt T` are proved, and assembled in `obsRowCoeff_of_sharpHat`.

The remainder marks, the tilt family and the `ObsMarks` inhabitant are NOT constructed here; zero
class only.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Polymer Balaban.SmallField.Def6 Balaban.Multiscale
  Balaban.Background Balaban.SmallField Metric

/-! ### Slices of an analytic function along a hat direction -/

section Slice

variable {R P : Type*} [NormedAddCommGroup R] [NormedSpace ℂ R] [Fintype P]

/-- The coordinate derivative of `E (r, ·)` at `0` along the hat vector `e`:
`d/dζ|₀ E (r, ζ • e)`. -/
noncomputable def hatCoeff (E : R × (P → ℂ) → ℂ) (r : R) (e : P → ℂ) : ℂ :=
  deriv (fun ζ : ℂ => E (r, ζ • e)) 0

theorem differentiableOn_slice {E : R × (P → ℂ) → ℂ} {A : Set R} {cψ : ℝ} {r : R} (hr : r ∈ A)
    (hE : AnalyticOnNhd ℂ E (A ×ˢ {ψ : P → ℂ | ∀ p, ‖ψ p‖ ≤ cψ})) {e : P → ℂ}
    (he : ∀ p, ‖e p‖ ≤ 1) : DifferentiableOn ℂ (fun ζ : ℂ => E (r, ζ • e)) (ball 0 cψ) := by
  intro ζ hζ
  have hmem : (r, ζ • e) ∈ A ×ˢ {ψ : P → ℂ | ∀ p, ‖ψ p‖ ≤ cψ} := by
    refine ⟨hr, fun p => ?_⟩
    have h1 : ‖ζ‖ < cψ := by simpa using hζ
    simp only [Pi.smul_apply, smul_eq_mul, norm_mul]
    calc ‖ζ‖ * ‖e p‖ ≤ ‖ζ‖ * 1 := by gcongr; exact he p
      _ ≤ cψ := by linarith
  have := (hE _ hmem).comp_of_eq (f := fun ζ : ℂ => (r, ζ • e))
    (analyticAt_const.prod (analyticAt_id.smul analyticAt_const)) rfl
  exact this.differentiableAt.differentiableWithinAt

omit [Fintype P] in
theorem smul_mem_ball {cψ : ℝ} {e : P → ℂ} (he : ∀ p, ‖e p‖ ≤ 1) {ζ : ℂ} (hζ : ‖ζ‖ < cψ) :
    ∀ p, ‖(ζ • e) p‖ ≤ cψ := by
  intro p
  simp only [Pi.smul_apply, smul_eq_mul, norm_mul]
  calc ‖ζ‖ * ‖e p‖ ≤ ‖ζ‖ * 1 := by gcongr; exact he p
    _ ≤ cψ := by linarith

/-- **Cauchy bound** for the coordinate derivative. -/
theorem norm_hatCoeff_le {E : R × (P → ℂ) → ℂ} {A : Set R} {cψ B : ℝ} (hcψ : 0 < cψ) {r : R}
    (hr : r ∈ A) (hE : AnalyticOnNhd ℂ E (A ×ˢ {ψ : P → ℂ | ∀ p, ‖ψ p‖ ≤ cψ}))
    (hB : ∀ u ∈ A ×ˢ {ψ : P → ℂ | ∀ p, ‖ψ p‖ ≤ cψ}, ‖E u‖ ≤ B) {e : P → ℂ}
    (he : ∀ p, ‖e p‖ ≤ 1) : ‖hatCoeff E r e‖ ≤ B / cψ :=
  norm_deriv_zero_le hcψ (differentiableOn_slice hr hE he) fun ζ hζ =>
    hB _ ⟨hr, smul_mem_ball he (by simpa using hζ)⟩

omit [NormedAddCommGroup R] [NormedSpace ℂ R] [Fintype P] in
/-- **Vanishing**: if `E (r, ζ • e)` does not depend on `ζ` for `‖ζ‖ < cψ`, the coefficient is
zero. -/
theorem hatCoeff_eq_zero_of_const {E : R × (P → ℂ) → ℂ} {cψ : ℝ} (hcψ : 0 < cψ) {r : R}
    {e : P → ℂ} (h : ∀ ζ : ℂ, ‖ζ‖ < cψ → E (r, ζ • e) = E (r, 0)) : hatCoeff E r e = 0 := by
  unfold hatCoeff
  have : (fun ζ : ℂ => E (r, ζ • e)) =ᶠ[nhds 0] fun _ => E (r, 0) := by
    filter_upwards [ball_mem_nhds (0 : ℂ) hcψ] with ζ hζ
    exact h ζ (by simpa using hζ)
  rw [this.deriv_eq, deriv_const]

/-- **Exact finite sum**: the derivative of an expanded function is the sum of the coefficients. -/
theorem deriv_slice_sum {ι : Type*} {𝒴 : Finset ι} {E : ι → R × (P → ℂ) → ℂ} {A : Set R}
    {cψ : ℝ} (hcψ : 0 < cψ) {r : R} (hr : r ∈ A)
    (hE : ∀ Y, AnalyticOnNhd ℂ (E Y) (A ×ˢ {ψ : P → ℂ | ∀ p, ‖ψ p‖ ≤ cψ})) {e : P → ℂ}
    (he : ∀ p, ‖e p‖ ≤ 1) {F : (P → ℂ) → ℂ}
    (hF : ∀ ψ : P → ℂ, (∀ p, ‖ψ p‖ ≤ cψ) → F ψ = ∑ Y ∈ 𝒴, E Y (r, ψ)) :
    deriv (fun ζ : ℂ => F (ζ • e)) 0 = ∑ Y ∈ 𝒴, hatCoeff (E Y) r e := by
  have h1 : (fun ζ : ℂ => F (ζ • e)) =ᶠ[nhds 0] fun ζ => ∑ Y ∈ 𝒴, E Y (r, ζ • e) := by
    filter_upwards [ball_mem_nhds (0 : ℂ) hcψ] with ζ hζ
    exact hF _ (smul_mem_ball he (by simpa using hζ))
  rw [h1.deriv_eq]
  have hd : ∀ Y ∈ 𝒴, DifferentiableAt ℂ (fun ζ : ℂ => E Y (r, ζ • e)) 0 := fun Y _ =>
    (differentiableOn_slice hr (hE Y) he).differentiableAt (ball_mem_nhds (0 : ℂ) hcψ)
  exact deriv_fun_sum hd

end Slice

/-! ### The kernel indexed by cube labels -/

section Kernel

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ : ℕ}

open Classical in
/-- **The kernel** `h(T) = Σ_{Y ∈ 𝒴, obsRowLabel Y = T} c Y`, for coefficients `c Y`. -/
noncomputable def obsHker (𝒴 : Finset (Set (CTorus d L N₁ m₁ K))) (c : Set (CTorus d L N₁ m₁ K) → ℂ)
    (m₀ : ℕ) (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ K Set.univ)) :
    ℂ :=
  ∑ Y ∈ 𝒴.filter (fun Y => obsRowLabel m₀ K Y = T), c Y

variable {𝒴 : Finset (Set (CTorus d L N₁ m₁ K))} {c : Set (CTorus d L N₁ m₁ K) → ℂ}

/-- At the label of `Y ∈ 𝒴`, exactly one domain contributes. -/
theorem obsHker_label (hN : L ^ m₀ ∣ N₁) (hdj : ∀ Y ∈ 𝒴, IsDj m₀ K Y) {Y} (hY : Y ∈ 𝒴) :
    obsHker 𝒴 c m₀ (obsRowLabel m₀ K Y) = c Y := by
  classical
  unfold obsHker
  have : 𝒴.filter (fun Y' => obsRowLabel m₀ K Y' = obsRowLabel m₀ K Y) = {Y} := by
    ext Y'
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨h1, h2⟩
      exact obsRowLabel_injective hN (hdj _ h1) (hdj _ hY) h2
    · rintro rfl; exact ⟨hY, rfl⟩
  rw [this, Finset.sum_singleton]

theorem obsHker_eq_zero_of_not_label {T} (h : ∀ Y ∈ 𝒴, obsRowLabel m₀ K Y ≠ T) :
    obsHker 𝒴 c m₀ T = 0 := by
  classical
  unfold obsHker
  have : 𝒴.filter (fun Y => obsRowLabel m₀ K Y = T) = ∅ := by
    ext Y; simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
    exact fun hY => h Y hY
  rw [this, Finset.sum_empty]

/-- A nonzero kernel value comes from a domain with that label and a nonzero coefficient. -/
theorem exists_of_obsHker_ne_zero {T} (h : obsHker 𝒴 c m₀ T ≠ 0) :
    ∃ Y ∈ 𝒴, obsRowLabel m₀ K Y = T ∧ c Y ≠ 0 := by
  classical
  obtain ⟨Y, hY, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  rw [Finset.mem_filter] at hY
  exact ⟨Y, hY.1, hY.2, hne⟩

/-- **Sum identity**: summing the kernel over all label sets `T` gives `Σ_Y c Y`. -/
theorem sum_obsHker : ∑ T, obsHker 𝒴 c m₀ T = ∑ Y ∈ 𝒴, c Y := by
  classical
  unfold obsHker
  exact Finset.sum_fiberwise 𝒴 (fun Y => obsRowLabel m₀ K Y) c

/-- **Decay bound** of the kernel in `dExt T` from a decay bound of the coefficients in the
covariance tree length. -/
theorem norm_obsHker_le (hN : L ^ m₀ ∣ N₁) (hdj : ∀ Y ∈ 𝒴, IsDj m₀ K Y) {Ch κh : ℝ}
    (hCh : 0 ≤ Ch) (hκh : 0 ≤ κh)
    (hb : ∀ Y ∈ 𝒴, ‖c Y‖ ≤ Ch * Real.exp (-κh * treeLenCovOne m₀ K Y)) (T) :
    ‖obsHker 𝒴 c m₀ T‖ ≤ Ch * Real.exp (-κh * dExt T) := by
  by_cases hT : ∃ Y ∈ 𝒴, obsRowLabel m₀ K Y = T
  · obtain ⟨Y, hY, rfl⟩ := hT
    rw [obsHker_label hN hdj hY]
    refine (hb Y hY).trans ?_
    have := dExt_obsRowLabel_le hN (hdj Y hY)
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by nlinarith)) hCh
  · push Not at hT
    rw [obsHker_eq_zero_of_not_label hT, norm_zero]
    positivity

end Kernel

/-! ### The sharp hat expansion along a mark -/

section Marks

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ)

open Classical in
/-- **The hat vector `e_{u,a}`** of the mark `m = (u, a)`: `1` at the coordinate `(u, a)` of the
hat variable, `0` elsewhere. -/
noncomputable def obsUnitVec (m : ObsMarkIdx S) : S.U × Fin N → ℂ := Pi.single m 1

theorem norm_obsUnitVec_le (m : ObsMarkIdx S) (p : S.U × Fin N) : ‖obsUnitVec S m p‖ ≤ 1 := by
  classical
  unfold obsUnitVec
  rw [Pi.single_apply]
  split_ifs <;> simp

/-- **The coefficient** `a_Y(m) = d/dζ|₀ Ev Y (rawOf D, ζ • e_m)` of the term `Ev Y`. -/
noncomputable def obsRowCoeff
    (Ev : Set (CTorus d L N₁ m₁ (k + 1)) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (S.U × Fin N → ℂ) → ℂ)
    (D : BgData S.G' N) (m : ObsMarkIdx S) (Y : Set (CTorus d L N₁ m₁ (k + 1))) : ℂ :=
  hatCoeff (Ev Y) (rawOf D) (obsUnitVec S m)

variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ} {X₁f : Finset (CTorus d L N₁ m₁ (k + 1))} {j : ℕ}
variable {m₀ : ℕ} {X 𝒦X : Set (CTorus d L N₁ m₁ (k + 1))}

/-- **Coefficients and kernel of the sharp hat expansion of one site functional along the marks, exact
locality.**  The statement of `obsRowCoeff_of_sharpHat` with the locality clause of `Ev` for raw data
agreeing on `Y` itself and hat variables agreeing at the unit points of `Y` (from
`fsite_expansion_hat_rawY`); `obsRowCoeff_of_sharpHat` is its corollary.
Premises: exactly those of `fsite_expansion_hat_dir` (with `Gp = S.G'`), plus `0 < cψ`.  The
family `Ev` is that of the landed theorem; with `a_Y = obsRowCoeff`, `Ch = Q δ₁ / cψ`
(`Q = cK2' d L N (famConst d L BG₂ κ)`) and `κh = 2 κdec`, for every datum `D` of `Ξ` and every
mark `m`:

* `Σ_Y a_Y = d/dζ|₀ F(ζ • e_m)`, `F` the expanded function;
* `‖a_Y‖ ≤ Ch * exp (-2 κdec * treeLenCovOne m₀ (k+1) Y)`;
* `a_Y = 0` unless `Y` has a site of the unit point of `m`;
* `obsHker (obsRowLabel Y) = a_Y` for `Y` in the family; `Σ_T obsHker T = Σ_Y a_Y`;
* `obsHker T ≠ 0` puts the mark cube `obsMarkCube S m₀ m` and the root cube of the site `y` in
  `T`;
* `‖obsHker T‖ ≤ Ch * exp (-κh * dExt T)`. -/
theorem obsRowCoeff_of_sharpHat_rawY (hC : FlCore N S.G' Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hk : 1 ≤ k) (hG : IsLevel Hm k) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 < cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    (hcov : CovSetup S.G' m₀ j X 𝒦X)
    (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) = X1 S.G' m₀ j 𝒦X)
    (hconn : HatConn S.G') (hrow : RowInHat (coverOf S.G') Hm (compWeight L a₁) ν)
    (hopt : ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X) ∧ MeetsOne m₀ j 𝒦X W₀ ∧
        bondCost (scaleW L m₀ m₁ j) E₀ = treeLenCovOne m₀ j X)
    (hΔ : treeLenCovOne m₀ j X = 0)
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (y : CTorus d L N₁ m₁ (k + 1)) (hy : y ∈ X₁f) (iy : Fin N) :
    ∃ Ev : Set (CTorus d L N₁ m₁ (k + 1)) →
        RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts S.G' × Fin N → ℂ) → ℂ,
      (∀ D : BgData S.G' N, XiCData S.G' (compWeight L a₁) ν (k + 1) 1 eps D →
        ∀ ψh : unitPts S.G' × Fin N → ℂ, (∀ p, ‖ψh p‖ ≤ cψ) →
        svec Hm (flFieldOne S.G' Hm BG₂ κ a₁ ν D (hatLift S.G' a₁ ν S.hG' cc D ψh)) y iy =
        ∑ Y ∈ polymerDomains (fun i : ParIdx S.G' (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1)
          S.G' m₀ (X1 S.G' m₀ j 𝒦X), Ev Y (rawOf D, ψh)) ∧
      (∀ Y, ∀ u ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        ∀ u' ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        agreeOn Y u.1 u'.1 → (∀ y ∈ Y, ∀ i, u.2 (unitPt S.hG' y, i) = u'.2 (unitPt S.hG' y, i)) →
        Ev Y u = Ev Y u') ∧
      (∀ Y, ∀ u ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        ‖Ev Y u‖ ≤ (cK2' d L N (famConst d L BG₂ κ) * δ₁) *
          Real.exp (-2 * κdec * treeLenCov S.G' m₀ Y)) ∧
      (∀ Y, AnalyticOnNhd ℂ (Ev Y) (XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ})) ∧
      (∀ D : BgData S.G' N, XiCData S.G' (compWeight L a₁) ν (k + 1) 1 eps D →
        ∀ m : ObsMarkIdx S,
        (deriv (fun ζ : ℂ => svec Hm (flFieldOne S.G' Hm BG₂ κ a₁ ν D
            (hatLift S.G' a₁ ν S.hG' cc D (ζ • obsUnitVec S m))) y iy) 0 =
          ∑ Y ∈ polymerDomains (fun i : ParIdx S.G' (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) =>
            i.1.1) S.G' m₀ (X1 S.G' m₀ j 𝒦X), obsRowCoeff S Ev D m Y) ∧
        (∀ Y, ‖obsRowCoeff S Ev D m Y‖ ≤ (cK2' d L N (famConst d L BG₂ κ) * δ₁ / cψ) *
          Real.exp (-2 * κdec * treeLenCovOne m₀ (k + 1) Y)) ∧
        (∀ Y, (∀ y' ∈ Y, unitPt S.hG' y' ≠ m.1) → obsRowCoeff S Ev D m Y = 0) ∧
        (∀ Y ∈ polymerDomains (fun i : ParIdx S.G' (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) =>
            i.1.1) S.G' m₀ (X1 S.G' m₀ j 𝒦X),
          obsHker (polymerDomains (fun i : ParIdx S.G' (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) =>
            i.1.1) S.G' m₀ (X1 S.G' m₀ j 𝒦X)) (obsRowCoeff S Ev D m) m₀ (obsRowLabel m₀ (k + 1) Y) =
          obsRowCoeff S Ev D m Y) ∧
        (∑ T, obsHker (polymerDomains (fun i : ParIdx S.G' (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) =>
            i.1.1) S.G' m₀ (X1 S.G' m₀ j 𝒦X)) (obsRowCoeff S Ev D m) m₀ T =
          ∑ Y ∈ polymerDomains (fun i : ParIdx S.G' (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) =>
            i.1.1) S.G' m₀ (X1 S.G' m₀ j 𝒦X), obsRowCoeff S Ev D m Y) ∧
        (∀ T, obsHker (polymerDomains (fun i : ParIdx S.G' (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) =>
            i.1.1) S.G' m₀ (X1 S.G' m₀ j 𝒦X)) (obsRowCoeff S Ev D m) m₀ T ≠ 0 →
          obsMarkCube S m₀ m ∈ T ∧ rootCube (m₀ := m₀) (blockIndex y) ∈ T) ∧
        (∀ T, ‖obsHker (polymerDomains (fun i : ParIdx S.G' (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) =>
            i.1.1) S.G' m₀ (X1 S.G' m₀ j 𝒦X)) (obsRowCoeff S Ev D m) m₀ T‖ ≤
          (cK2' d L N (famConst d L BG₂ κ) * δ₁ / cψ) * Real.exp (-(2 * κdec) * dExt T))) ∧
      ∃ (F₁ : DecParams S.G' × RawData d L (N₁ * L ^ m₁) (k + 1) N →
          (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ))
        (Sol : Dec2.DecParams (coverOf S.G') × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)),
        (∀ (s : DecParams S.G') (D : BgData S.G' N), (∀ P, ‖s P‖ < Real.exp κ) →
          InUnionDomainC S.G' (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : S.G'.Ω 1 × Fin N → ℂ)
            (α : S.G'.Ω 1 → ℂ), IsDecBg S.G' (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
            F₁ (s, rawOf D) = (φ, α)) ∧
        (∀ p : Dec2.DecParams (coverOf S.G') × Edat Hm N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
          StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
            (Sol p).1 = dphi Hm (Dec2.decG (coverOf S.G') Hm (compWeight L a₁) ν p.1) p.2.2.1 p.2.1
              (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
            Dec2.DecFixed (coverOf S.G') Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
              (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
            Small Hm (Sol p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
            Small Hm (Sol p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
            SupBounds Hm (Sol p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
            (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
              Dec2.DecFixed (coverOf S.G') Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
                (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol p).2)) ∧
        Ev = evTerm (fun i : ParIdx S.G' (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) S.G' m₀
          (X1 S.G' m₀ j 𝒦X)
          (fun u s => siteFun S.G' Hm y iy
            (F₁ (extParams S.G' (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s, u.1))
            (Sol (extParams S.G' (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s,
              flEdat S.G' Hm (F₁ (extParams S.G' (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s, u.1))
                u.1.1 (hatPsiF S.G' a₁ ν S.hG' cc F₁
                  (extParams S.G' (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s) u.1 u.2))).1
            (u.1, hatPsiF S.G' a₁ ν S.hG' cc F₁
              (extParams S.G' (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s) u.1 u.2)) := by
  classical
  obtain ⟨Ev, hs, hd, hb, ha, hex⟩ := fsite_expansion_hat_rawY hC hk hG S.hG' cc hcψ.le hMX hdm hα
    hsm hδ₁ hcov hX₁ hconn hrow hopt hΔ hκ₀ hκdec hκ h1 hlog y hy iy
  refine ⟨Ev, hs, hd, hb, ha, fun D hD m => ?_, hex⟩
  have hd3 : 3 ≤ d := hC.HBp.hd
  have hN : L ^ m₀ ∣ N₁ := hcov.hN
  have hdj : ∀ Y ∈ polymerDomains (fun i : ParIdx S.G' (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) =>
      i.1.1) S.G' m₀ (X1 S.G' m₀ j 𝒦X), IsDj m₀ (k + 1) Y := fun Y hY =>
    isDj_of_polymerDomains (fun i : ParIdx S.G' (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1)
      S.hG' hcov hd3 (fun i => i.1.2) hopt hY
  have hr : rawOf D ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps := ⟨D, hD, rfl⟩
  have he := norm_obsUnitVec_le S m
  have hd0 : 0 < d := by omega
  have hB0 : 0 ≤ famConst d L BG₂ κ := by
    have := famConst_ge_one (L := L) hC.hS2.fam.2.1 κ hd0; linarith
  have hCh : 0 ≤ cK2' d L N (famConst d L BG₂ κ) * δ₁ / cψ :=
    div_nonneg (mul_nonneg (cK2'_nonneg hB0) hC.δ₁_pos.le) hcψ.le
  have hxX : y ∈ X1 S.G' m₀ j 𝒦X := by rw [← hX₁]; exact hy
  have hcoef : ∀ Y, ‖obsRowCoeff S Ev D m Y‖ ≤ (cK2' d L N (famConst d L BG₂ κ) * δ₁ / cψ) *
      Real.exp (-2 * κdec * treeLenCovOne m₀ (k + 1) Y) := by
    intro Y
    have := norm_hatCoeff_le hcψ hr (ha Y) (hb Y) he
    rw [← treeLenCov_eq_treeLenCovOne S.hG' m₀ Y]
    unfold obsRowCoeff
    rwa [mul_div_right_comm] at this
  have hvan : ∀ Y, (∀ y' ∈ Y, unitPt S.hG' y' ≠ m.1) → obsRowCoeff S Ev D m Y = 0 := by
    intro Y hY
    refine hatCoeff_eq_zero_of_const hcψ fun ζ hζ => hd Y (rawOf D, ζ • obsUnitVec S m) ⟨hr, smul_mem_ball he hζ⟩
      (rawOf D, 0) ⟨hr, fun p => by simpa using hcψ.le⟩ (agreeOn_refl _ _) (fun y' hy' i' => ?_)
    have : (unitPt S.hG' y', i') ≠ m := fun h => hY y' hy' (by rw [← h])
    simp [obsUnitVec, this]
  have hκ2 : 0 ≤ 2 * κdec := by linarith
  refine ⟨?_, hcoef, hvan, fun Y hY => obsHker_label hN hdj hY, sum_obsHker, ?_, ?_⟩
  · have := deriv_slice_sum (𝒴 := polymerDomains
      (fun i : ParIdx S.G' (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) S.G' m₀
      (X1 S.G' m₀ j 𝒦X)) hcψ hr ha he
      (F := fun ψh => svec Hm (flFieldOne S.G' Hm BG₂ κ a₁ ν D (hatLift S.G' a₁ ν S.hG' cc D ψh)) y iy)
      (fun ψ hψ => hs D hD ψ hψ)
    exact this
  · intro T hT
    obtain ⟨Y, hY, rfl, hne⟩ := exists_of_obsHker_ne_zero hT
    refine ⟨?_, rootCube_mem_obsRowLabel_of_polymerDomains
      (fun i : ParIdx S.G' (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) hN S.hG' hcov hd3
      (fun i => i.1.2) hopt rfl hY hxX⟩
    by_contra hno
    have hno' : ∀ y' ∈ Y, unitPt S.hG' y' ≠ m.1 := by
      intro y' hy' hu
      exact hno (cellOf_mem_obsRowLabel S hN (hdj Y hY) hy' hu)
    exact hne (hvan Y hno')
  · intro T
    refine norm_obsHker_le hN hdj hCh hκ2 (fun Y _ => ?_) T
    have := hcoef Y
    rwa [show -(2 * κdec) * treeLenCovOne m₀ (k + 1) Y = -2 * κdec * treeLenCovOne m₀ (k + 1) Y
      by ring]


/-- **Coefficients and kernel of the sharp hat expansion of one site functional along the marks.**
Premises: exactly those of `fsite_expansion_hat_dir` (with `Gp = S.G'`), plus `0 < cψ`.  The
family `Ev` is that of the landed theorem; with `a_Y = obsRowCoeff`, `Ch = Q δ₁ / cψ`
(`Q = cK2' d L N (famConst d L BG₂ κ)`) and `κh = 2 κdec`, for every datum `D` of `Ξ` and every
mark `m`:

* `Σ_Y a_Y = d/dζ|₀ F(ζ • e_m)`, `F` the expanded function;
* `‖a_Y‖ ≤ Ch * exp (-2 κdec * treeLenCovOne m₀ (k+1) Y)`;
* `a_Y = 0` unless `Y` has a site of the unit point of `m`;
* `obsHker (obsRowLabel Y) = a_Y` for `Y` in the family; `Σ_T obsHker T = Σ_Y a_Y`;
* `obsHker T ≠ 0` puts the mark cube `obsMarkCube S m₀ m` and the root cube of the site `y` in
  `T`;
* `‖obsHker T‖ ≤ Ch * exp (-κh * dExt T)`. -/
theorem obsRowCoeff_of_sharpHat (hC : FlCore N S.G' Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hk : 1 ≤ k) (hG : IsLevel Hm k) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 < cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    (hcov : CovSetup S.G' m₀ j X 𝒦X)
    (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) = X1 S.G' m₀ j 𝒦X)
    (hconn : HatConn S.G') (hrow : RowInHat (coverOf S.G') Hm (compWeight L a₁) ν)
    (hopt : ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X) ∧ MeetsOne m₀ j 𝒦X W₀ ∧
        bondCost (scaleW L m₀ m₁ j) E₀ = treeLenCovOne m₀ j X)
    (hΔ : treeLenCovOne m₀ j X = 0)
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (y : CTorus d L N₁ m₁ (k + 1)) (hy : y ∈ X₁f) (iy : Fin N) :
    ∃ Ev : Set (CTorus d L N₁ m₁ (k + 1)) →
        RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts S.G' × Fin N → ℂ) → ℂ,
      (∀ D : BgData S.G' N, XiCData S.G' (compWeight L a₁) ν (k + 1) 1 eps D →
        ∀ ψh : unitPts S.G' × Fin N → ℂ, (∀ p, ‖ψh p‖ ≤ cψ) →
        svec Hm (flFieldOne S.G' Hm BG₂ κ a₁ ν D (hatLift S.G' a₁ ν S.hG' cc D ψh)) y iy =
        ∑ Y ∈ polymerDomains (fun i : ParIdx S.G' (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1)
          S.G' m₀ (X1 S.G' m₀ j 𝒦X), Ev Y (rawOf D, ψh)) ∧
      (∀ Y, ∀ u ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        ∀ u' ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        AgHatDir S.hG' Y u u' → Ev Y u = Ev Y u') ∧
      (∀ Y, ∀ u ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        ‖Ev Y u‖ ≤ (cK2' d L N (famConst d L BG₂ κ) * δ₁) *
          Real.exp (-2 * κdec * treeLenCov S.G' m₀ Y)) ∧
      (∀ Y, AnalyticOnNhd ℂ (Ev Y) (XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ})) ∧
      ∀ D : BgData S.G' N, XiCData S.G' (compWeight L a₁) ν (k + 1) 1 eps D →
        ∀ m : ObsMarkIdx S,
        (deriv (fun ζ : ℂ => svec Hm (flFieldOne S.G' Hm BG₂ κ a₁ ν D
            (hatLift S.G' a₁ ν S.hG' cc D (ζ • obsUnitVec S m))) y iy) 0 =
          ∑ Y ∈ polymerDomains (fun i : ParIdx S.G' (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) =>
            i.1.1) S.G' m₀ (X1 S.G' m₀ j 𝒦X), obsRowCoeff S Ev D m Y) ∧
        (∀ Y, ‖obsRowCoeff S Ev D m Y‖ ≤ (cK2' d L N (famConst d L BG₂ κ) * δ₁ / cψ) *
          Real.exp (-2 * κdec * treeLenCovOne m₀ (k + 1) Y)) ∧
        (∀ Y, (∀ y' ∈ Y, unitPt S.hG' y' ≠ m.1) → obsRowCoeff S Ev D m Y = 0) ∧
        (∀ Y ∈ polymerDomains (fun i : ParIdx S.G' (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) =>
            i.1.1) S.G' m₀ (X1 S.G' m₀ j 𝒦X),
          obsHker (polymerDomains (fun i : ParIdx S.G' (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) =>
            i.1.1) S.G' m₀ (X1 S.G' m₀ j 𝒦X)) (obsRowCoeff S Ev D m) m₀ (obsRowLabel m₀ (k + 1) Y) =
          obsRowCoeff S Ev D m Y) ∧
        (∑ T, obsHker (polymerDomains (fun i : ParIdx S.G' (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) =>
            i.1.1) S.G' m₀ (X1 S.G' m₀ j 𝒦X)) (obsRowCoeff S Ev D m) m₀ T =
          ∑ Y ∈ polymerDomains (fun i : ParIdx S.G' (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) =>
            i.1.1) S.G' m₀ (X1 S.G' m₀ j 𝒦X), obsRowCoeff S Ev D m Y) ∧
        (∀ T, obsHker (polymerDomains (fun i : ParIdx S.G' (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) =>
            i.1.1) S.G' m₀ (X1 S.G' m₀ j 𝒦X)) (obsRowCoeff S Ev D m) m₀ T ≠ 0 →
          obsMarkCube S m₀ m ∈ T ∧ rootCube (m₀ := m₀) (blockIndex y) ∈ T) ∧
        (∀ T, ‖obsHker (polymerDomains (fun i : ParIdx S.G' (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) =>
            i.1.1) S.G' m₀ (X1 S.G' m₀ j 𝒦X)) (obsRowCoeff S Ev D m) m₀ T‖ ≤
          (cK2' d L N (famConst d L BG₂ κ) * δ₁ / cψ) * Real.exp (-(2 * κdec) * dExt T)) := by
  obtain ⟨Ev, hs, hd, hb, ha, hrow', -⟩ := obsRowCoeff_of_sharpHat_rawY S hC hk hG cc hcψ hMX hdm hα
    hsm hδ₁ hcov hX₁ hconn hrow hopt hΔ hκ₀ hκdec hκ h1 hlog y hy iy
  exact ⟨Ev, hs, fun Y u hu u' hu' h => hd Y u hu u' hu' (agreeOn_mono (fun x hx => Or.inl hx) h.1) h.2,
    hb, ha, hrow'⟩

end Marks

end Balaban.Fluctuation
