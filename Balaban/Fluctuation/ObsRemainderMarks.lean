/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.ObsRowCoeff
public import Balaban.Fluctuation.ObsMeanBlock

/-!
# The remainder marks of the sharp hat terms

Zero class of the step.  The `ObsMarks` inhabitant and the tilt family are NOT constructed here.

## Analysis along a ray

For an analytic family `E Y` of terms and a hat configuration `ψ̂` with `‖ψ̂ p‖ ≤ p₁`, put
`e_Y(ζ) = E Y (r, ζ • ψ̂)`; it is analytic for `|ζ| < ρ = cψ / p₁`.  With `q = p₁ / cψ ≤ 1/4`:

* `norm_remExt_ray_le`: `‖remExt e_Y u‖ ≤ 8 B q²` for all `u`, when `‖E Y‖ ≤ B` on the hat ball;
* `differentiableOn_remExt_ray`: `u ↦ remExt e_Y u` is analytic on `|u| < 3/2`;
* `hatCoeff_eq_sum`: the derivative at `0` along `ψ̂` is `Σ_p ψ̂ p * a(p)`, with `a(p)` the
  coordinate derivative `hatCoeff (E Y) r (Pi.single p 1)` of the kernel part;
* `ray_decomp`: for `|t| < 3/2`, the derivative of the expanded function along the ray is the
  kernel part plus the sum of the remainders;
* `remExt_ray_congr`, `measurable_ray_rem`: dependence on `ψ̂` through finitely many coordinates,
  and measurability in `ψ̂`.

## The marks on the block configurations

`obsHat Φ` is the clipped hat configuration (`ObsMeanBlock.blockMark`); `obsRemG` the remainder of
a term along it; `obsGr` the family indexed by the domains plus a dummy index.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Polymer Balaban.SmallField.Def6 Balaban.Multiscale
  Balaban.Background Balaban.SmallField Metric MeasureTheory

/-! ### Analysis along a ray -/

section Ray

variable {R P : Type*} [NormedAddCommGroup R] [NormedSpace ℂ R] [Fintype P] [DecidableEq P]

omit [Fintype P] [DecidableEq P] in
theorem smul_mem_ball_p {cψ p₁ : ℝ} (hp : 0 < p₁) {ψ : P → ℂ} (hψ : ∀ p, ‖ψ p‖ ≤ p₁) {ζ : ℂ}
    (hζ : ‖ζ‖ < cψ / p₁) : ∀ p, ‖(ζ • ψ) p‖ ≤ cψ := by
  intro p
  simp only [Pi.smul_apply, smul_eq_mul, norm_mul]
  calc ‖ζ‖ * ‖ψ p‖ ≤ (cψ / p₁) * p₁ := by
        apply mul_le_mul hζ.le (hψ p) (norm_nonneg _) (by linarith [norm_nonneg ζ])
    _ = cψ := by field_simp

omit [DecidableEq P] in
theorem analyticAt_fix {E : R × (P → ℂ) → ℂ} {A : Set R} {cψ : ℝ} {r : R} (hr : r ∈ A)
    (hE : AnalyticOnNhd ℂ E (A ×ˢ {ψ : P → ℂ | ∀ p, ‖ψ p‖ ≤ cψ})) {x : P → ℂ}
    (hx : ∀ p, ‖x p‖ ≤ cψ) : AnalyticAt ℂ (fun y : P → ℂ => E (r, y)) x :=
  (hE (r, x) ⟨hr, hx⟩).comp_of_eq (f := fun y : P → ℂ => (r, y))
    (analyticAt_const.prod analyticAt_id) rfl

omit [DecidableEq P] in
theorem differentiableOn_ray {E : R × (P → ℂ) → ℂ} {A : Set R} {cψ p₁ : ℝ} (hp : 0 < p₁) {r : R}
    (hr : r ∈ A) (hE : AnalyticOnNhd ℂ E (A ×ˢ {ψ : P → ℂ | ∀ p, ‖ψ p‖ ≤ cψ})) {ψ : P → ℂ}
    (hψ : ∀ p, ‖ψ p‖ ≤ p₁) :
    DifferentiableOn ℂ (fun ζ : ℂ => E (r, ζ • ψ)) (ball 0 (cψ / p₁)) := by
  intro ζ hζ
  have := (hE (r, ζ • ψ) ⟨hr, smul_mem_ball_p hp hψ (by simpa using hζ)⟩).comp_of_eq
    (f := fun ζ : ℂ => (r, ζ • ψ)) (analyticAt_const.prod (analyticAt_id.smul analyticAt_const))
    rfl
  exact this.differentiableAt.differentiableWithinAt

omit [NormedAddCommGroup R] [NormedSpace ℂ R] [DecidableEq P] in
theorem hatCoeff_eq_fderiv (E : R × (P → ℂ) → ℂ) (r : R) (e : P → ℂ)
    (hE : DifferentiableAt ℂ (fun ψ : P → ℂ => E (r, ψ)) 0) :
    hatCoeff E r e = fderiv ℂ (fun ψ : P → ℂ => E (r, ψ)) 0 e := by
  unfold hatCoeff
  have h1 : HasDerivAt (fun ζ : ℂ => ζ • e) e 0 := by
    simpa using (hasDerivAt_id (0 : ℂ)).smul_const e
  have h2 : HasFDerivAt (fun ψ : P → ℂ => E (r, ψ)) (fderiv ℂ (fun ψ : P → ℂ => E (r, ψ)) 0)
      ((fun ζ : ℂ => ζ • e) 0) := by simpa using hE.hasFDerivAt
  exact (h2.comp_hasDerivAt (0 : ℂ) h1).deriv

omit [NormedAddCommGroup R] [NormedSpace ℂ R] in
/-- **Linearity**: the derivative at `0` along `ψ` is the linear map of the coordinate
derivatives applied to `ψ`. -/
theorem hatCoeff_eq_sum (E : R × (P → ℂ) → ℂ) (r : R) (ψ : P → ℂ)
    (hE : DifferentiableAt ℂ (fun ψ : P → ℂ => E (r, ψ)) 0) :
    hatCoeff E r ψ = ∑ p, ψ p * hatCoeff E r (Pi.single p 1) := by
  classical
  rw [hatCoeff_eq_fderiv E r ψ hE]
  have h : ψ = ∑ p, ψ p • (Pi.single p 1 : P → ℂ) := by
    ext q; simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [h]
  rw [map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [map_smul, hatCoeff_eq_fderiv E r _ hE, smul_eq_mul]

variable {A : Set R} {cψ p₁ : ℝ}

theorem inv_div_le_of {cψ p₁ : ℝ} (hq : p₁ / cψ ≤ 1 / 4) :
    (cψ / p₁)⁻¹ ≤ 1 / 4 := by rwa [inv_div]

theorem four_le_of {cψ p₁ : ℝ} (hcψ : 0 < cψ) (hp : 0 < p₁) (hq : p₁ / cψ ≤ 1 / 4) :
    4 ≤ cψ / p₁ := by
  have := le_of_inv_le_one_div (div_pos hcψ hp) (by norm_num) (inv_div_le_of hq)
  exact this

omit [DecidableEq P] in
/-- **Bound of the remainder along the ray**, for every `u`. -/
theorem norm_remExt_ray_le {E : R × (P → ℂ) → ℂ} (hcψ : 0 < cψ) (hp : 0 < p₁)
    (hq : p₁ / cψ ≤ 1 / 4) {r : R} (hr : r ∈ A)
    (hE : AnalyticOnNhd ℂ E (A ×ˢ {ψ : P → ℂ | ∀ p, ‖ψ p‖ ≤ cψ})) {B : ℝ}
    (hB : ∀ x ∈ A ×ˢ {ψ : P → ℂ | ∀ p, ‖ψ p‖ ≤ cψ}, ‖E x‖ ≤ B) {ψ : P → ℂ}
    (hψ : ∀ p, ‖ψ p‖ ≤ p₁) (u : ℂ) :
    ‖remExt (fun ζ : ℂ => E (r, ζ • ψ)) u‖ ≤ 8 * B * (p₁ / cψ) ^ 2 := by
  have := norm_remExt_le (div_pos hcψ hp) (inv_div_le_of hq) (differentiableOn_ray hp hr hE hψ)
    (fun ζ hζ => hB _ ⟨hr, smul_mem_ball_p hp hψ (by simpa using hζ)⟩) u
  rwa [inv_div] at this

omit [DecidableEq P] in
theorem differentiableOn_remExt_ray {E : R × (P → ℂ) → ℂ} (hcψ : 0 < cψ) (hp : 0 < p₁)
    (hq : p₁ / cψ ≤ 1 / 4) {r : R} (hr : r ∈ A)
    (hE : AnalyticOnNhd ℂ E (A ×ˢ {ψ : P → ℂ | ∀ p, ‖ψ p‖ ≤ cψ})) {ψ : P → ℂ}
    (hψ : ∀ p, ‖ψ p‖ ≤ p₁) :
    DifferentiableOn ℂ (remExt (fun ζ : ℂ => E (r, ζ • ψ))) (ball 0 (3 / 2)) :=
  differentiableOn_remExt (div_pos hcψ hp) (inv_div_le_of hq) (differentiableOn_ray hp hr hE hψ)

/-- **Kernel plus remainder**: for `|t| < 3/2`, the derivative along the ray of the expanded
function is the linear (kernel) part plus the sum of the remainders. -/
theorem ray_decomp {ι : Type*} {𝒴 : Finset ι} {E : ι → R × (P → ℂ) → ℂ} (hcψ : 0 < cψ)
    (hp : 0 < p₁) (hq : p₁ / cψ ≤ 1 / 4) {r : R} (hr : r ∈ A)
    (hE : ∀ Y ∈ 𝒴, AnalyticOnNhd ℂ (E Y) (A ×ˢ {ψ : P → ℂ | ∀ p, ‖ψ p‖ ≤ cψ})) {ψ : P → ℂ}
    (hψ : ∀ p, ‖ψ p‖ ≤ p₁) {F : (P → ℂ) → ℂ}
    (hF : ∀ ψ : P → ℂ, (∀ p, ‖ψ p‖ ≤ cψ) → F ψ = ∑ Y ∈ 𝒴, E Y (r, ψ)) {t : ℂ}
    (ht : ‖t‖ < 3 / 2) :
    deriv (fun ζ : ℂ => F (ζ • ψ)) t =
      ∑ p, ψ p * ∑ Y ∈ 𝒴, hatCoeff (E Y) r (Pi.single p 1) +
        ∑ Y ∈ 𝒴, remExt (fun ζ : ℂ => E Y (r, ζ • ψ)) t := by
  have hρ : 0 < cψ / p₁ := div_pos hcψ hp
  have h4 := four_le_of hcψ hp hq
  have htb : t ∈ ball (0 : ℂ) (cψ / p₁) := by
    rw [mem_ball_zero_iff]; linarith
  have hnh : ball (0 : ℂ) (cψ / p₁) ∈ nhds t := isOpen_ball.mem_nhds htb
  have h1 : (fun ζ : ℂ => F (ζ • ψ)) =ᶠ[nhds t] fun ζ => ∑ Y ∈ 𝒴, E Y (r, ζ • ψ) := by
    filter_upwards [hnh] with ζ hζ
    exact hF _ (smul_mem_ball_p hp hψ (by simpa using hζ))
  have hd : ∀ Y ∈ 𝒴, DifferentiableAt ℂ (fun ζ : ℂ => E Y (r, ζ • ψ)) t := fun Y _ =>
    (differentiableOn_ray hp hr (hE Y ‹_›) hψ).differentiableAt hnh
  have hd0 : ∀ Y ∈ 𝒴, DifferentiableAt ℂ (fun ψ : P → ℂ => E Y (r, ψ)) 0 := fun Y hY =>
    (analyticAt_fix hr (hE Y hY) (x := 0) (fun p => by simpa using hcψ.le)).differentiableAt
  rw [h1.deriv_eq, deriv_fun_sum hd]
  have h2 : ∀ Y ∈ 𝒴, deriv (fun ζ : ℂ => E Y (r, ζ • ψ)) t =
      remExt (fun ζ : ℂ => E Y (r, ζ • ψ)) t + ∑ p, ψ p * hatCoeff (E Y) r (Pi.single p 1) := by
    intro Y hY
    rw [remExt_eq_of_lt _ ht, ← hatCoeff_eq_sum (E Y) r ψ (hd0 Y hY)]
    unfold hatCoeff; ring
  rw [Finset.sum_congr rfl h2, Finset.sum_add_distrib, add_comm]
  congr 1
  simp_rw [Finset.mul_sum]
  exact Finset.sum_comm

omit [NormedAddCommGroup R] [NormedSpace ℂ R] [Fintype P] [DecidableEq P] in
/-- The remainder depends on the hat configuration only through the coordinates the term reads. -/
theorem remExt_ray_congr {E : R × (P → ℂ) → ℂ} (hcψ : 0 < cψ) (hp : 0 < p₁)
    (hq : p₁ / cψ ≤ 1 / 4) {r : R} {ψ ψ' : P → ℂ}
    (hloc : ∀ ζ : ℂ, ‖ζ‖ < cψ / p₁ → E (r, ζ • ψ) = E (r, ζ • ψ')) (u : ℂ) :
    remExt (fun ζ : ℂ => E (r, ζ • ψ)) u = remExt (fun ζ : ℂ => E (r, ζ • ψ')) u := by
  have h4 := four_le_of hcψ hp hq
  by_cases hu : ‖u‖ < 3 / 2
  · have hq' : ∀ v : ℂ, ‖v‖ < 3 / 2 →
        deriv (fun ζ : ℂ => E (r, ζ • ψ)) v = deriv (fun ζ : ℂ => E (r, ζ • ψ')) v := by
      intro v hv
      refine Filter.EventuallyEq.deriv_eq ?_
      filter_upwards [(isOpen_ball (x := (0 : ℂ)) (ε := cψ / p₁)).mem_nhds
        (show v ∈ ball (0 : ℂ) (cψ / p₁) by rw [mem_ball_zero_iff]; linarith)] with ζ hζ
      exact hloc ζ (by simpa using hζ)
    rw [remExt_eq_of_lt _ hu, remExt_eq_of_lt _ hu, hq' u hu, hq' 0 (by simp)]
  · rw [remExt_eq_zero_of_le _ (not_lt.1 hu), remExt_eq_zero_of_le _ (not_lt.1 hu)]

omit [DecidableEq P] in
/-- Continuity of the remainder in the hat configuration on the ball of radius `p₁`. -/
theorem continuousOn_ray_rem {E : R × (P → ℂ) → ℂ} (hcψ : 0 < cψ) (hp : 0 < p₁)
    (hq : p₁ / cψ ≤ 1 / 4) {r : R} (hr : r ∈ A)
    (hE : AnalyticOnNhd ℂ E (A ×ˢ {ψ : P → ℂ | ∀ p, ‖ψ p‖ ≤ cψ})) {u : ℂ} (hu : ‖u‖ < 3 / 2) :
    ContinuousOn (fun ψ : P → ℂ => remExt (fun ζ : ℂ => E (r, ζ • ψ)) u)
      {ψ : P → ℂ | ∀ p, ‖ψ p‖ ≤ p₁} := by
  have h4 := four_le_of hcψ hp hq
  have hder : ∀ v : ℂ, ‖v‖ < 3 / 2 → ∀ ψ : P → ℂ, (∀ p, ‖ψ p‖ ≤ p₁) →
      deriv (fun ζ : ℂ => E (r, ζ • ψ)) v =
        fderiv ℂ (fun y : P → ℂ => E (r, y)) (v • ψ) ψ := by
    intro v hv ψ hψ
    have hg := analyticAt_fix hr hE (x := v • ψ)
      (smul_mem_ball_p hp hψ (show ‖v‖ < cψ / p₁ by linarith))
    have h1 : HasDerivAt (fun ζ : ℂ => ζ • ψ) ψ v := by
      simpa using (hasDerivAt_id v).smul_const ψ
    have h2 : HasFDerivAt (fun y : P → ℂ => E (r, y)) (fderiv ℂ (fun y : P → ℂ => E (r, y)) (v • ψ))
        ((fun ζ : ℂ => ζ • ψ) v) := hg.differentiableAt.hasFDerivAt
    exact (h2.comp_hasDerivAt v h1).deriv
  have hcont : ∀ v : ℂ, ‖v‖ < 3 / 2 → ContinuousOn
      (fun ψ : P → ℂ => fderiv ℂ (fun y : P → ℂ => E (r, y)) (v • ψ) ψ)
      {ψ : P → ℂ | ∀ p, ‖ψ p‖ ≤ p₁} := by
    intro v hv ψ0 hψ0
    refine ContinuousAt.continuousWithinAt ?_
    have hg := analyticAt_fix hr hE (x := v • ψ0)
      (smul_mem_ball_p hp hψ0 (show ‖v‖ < cψ / p₁ by linarith))
    have hc1 : ContinuousAt (fderiv ℂ (fun y : P → ℂ => E (r, y))) (v • ψ0) :=
      hg.fderiv.continuousAt
    have hc2 : ContinuousAt (fun ψ : P → ℂ => v • ψ) ψ0 := (continuous_id.const_smul v).continuousAt
    exact (hc1.comp_of_eq hc2 rfl).clm_apply continuousAt_id
  rw [show (fun ψ : P → ℂ => remExt (fun ζ : ℂ => E (r, ζ • ψ)) u) = fun ψ => remExt (fun ζ : ℂ => E (r, ζ • ψ)) u from rfl]
  refine ((hcont u hu).sub (hcont 0 (by simp))).congr fun ψ hψ => ?_
  rw [remExt_eq_of_lt _ hu, hder u hu ψ hψ, hder 0 (by simp) ψ hψ]
  rfl

omit [DecidableEq P] in
/-- **Measurability** of the remainder in a measurable family of hat configurations in the ball
of radius `p₁`. -/
theorem measurable_ray_rem {α : Type*} [MeasurableSpace α] {E : R × (P → ℂ) → ℂ}
    (hcψ : 0 < cψ) (hp : 0 < p₁) (hq : p₁ / cψ ≤ 1 / 4) {r : R} (hr : r ∈ A)
    (hE : AnalyticOnNhd ℂ E (A ×ˢ {ψ : P → ℂ | ∀ p, ‖ψ p‖ ≤ cψ})) {Ψ : α → (P → ℂ)}
    (hΨ : Measurable Ψ) (hΨb : ∀ a p, ‖Ψ a p‖ ≤ p₁) (u : ℂ) :
    Measurable (fun a => remExt (fun ζ : ℂ => E (r, ζ • Ψ a)) u) := by
  by_cases hu : ‖u‖ < 3 / 2
  · have hc := continuousOn_ray_rem hcψ hp hq hr hE hu
    have hs := hc.domRestrict
    have hm : Measurable (Set.domRestrict {ψ : P → ℂ | ∀ p, ‖ψ p‖ ≤ p₁}
        (fun ψ : P → ℂ => remExt (fun ζ : ℂ => E (r, ζ • ψ)) u)) := hs.measurable
    exact hm.comp (hΨ.subtype_mk (p := fun ψ : P → ℂ => ∀ p, ‖ψ p‖ ≤ p₁) (h := hΨb))
  · have : (fun a => remExt (fun ζ : ℂ => E (r, ζ • Ψ a)) u) = fun _ => 0 := by
      funext a; exact remExt_eq_zero_of_le _ (not_lt.1 hu)
    rw [this]; exact measurable_const

end Ray

/-! ### The clipped hat configuration of a block configuration -/

section Block

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) (m₀ : ℕ) (hp : 0 < S.p₁)

/-- **The clipped hat configuration** of a block configuration `Φ`: the coordinate `(u, a)` is the
mark `blockMark u a Φ` of `ObsMeanBlock`, the coordinate `a` of the fluctuation vector at `u`
if its norm is `< p₁`, and `0` otherwise. -/
noncomputable def obsHat (Φ : ∀ b, (S.blockSplit m₀ hp).Ωb b) : S.U × Fin N → ℂ :=
  fun q => blockMark S m₀ hp q.1 q.2 Φ

/-- **The unclipped hat configuration**: the coordinates of the fluctuation vectors. -/
noncomputable def obsHatTrue (Φ : ∀ b, (S.blockSplit m₀ hp).Ωb b) : S.U × Fin N → ℂ :=
  fun q => ((Φ (S.cellOf m₀ q.1) ⟨q.1, rfl⟩ q.2 : ℝ) : ℂ)

theorem norm_obsHat_le (Φ : ∀ b, (S.blockSplit m₀ hp).Ωb b) (q : S.U × Fin N) :
    ‖obsHat S m₀ hp Φ q‖ ≤ S.p₁ := norm_blockMark_le S m₀ hp q.1 q.2 Φ

theorem measurable_obsHat : Measurable (obsHat S m₀ hp) :=
  Measurable.of_eval fun q => measurable_blockMark S m₀ hp q.1 q.2

/-- **The clipping is invisible almost everywhere**: for the block product measure, the clipped
and the unclipped hat configuration agree. -/
theorem ae_obsHat_eq_true :
    ∀ᵐ Φ ∂(Measure.pi (S.blockSplit m₀ hp).μ), obsHat S m₀ hp Φ = obsHatTrue S m₀ hp Φ := by
  have := isProbabilityMeasure_fluctMeasure1 N hp
  have h1 : ∀ u : S.U, ∀ᵐ Φ ∂(Measure.pi (S.blockSplit m₀ hp).μ),
      ‖Φ (S.cellOf m₀ u) ⟨u, rfl⟩‖ < S.p₁ := by
    intro u
    have h2 : ∀ᵐ y ∂((S.blockSplit m₀ hp).μ (S.cellOf m₀ u)), ‖y ⟨u, rfl⟩‖ < S.p₁ := by
      show ∀ᵐ y ∂(Measure.pi fun _ : {v : S.U // S.cellOf m₀ v = S.cellOf m₀ u} =>
        fluctMeasure1 N S.p₁), ‖y ⟨u, rfl⟩‖ < S.p₁
      exact (measurePreserving_eval (fun _ : {v : S.U // S.cellOf m₀ v = S.cellOf m₀ u} =>
        fluctMeasure1 N S.p₁) ⟨u, rfl⟩).quasiMeasurePreserving.ae (ae_norm_lt_fluctMeasure1 N S.p₁)
    exact (measurePreserving_eval (S.blockSplit m₀ hp).μ (S.cellOf m₀ u)).quasiMeasurePreserving.ae h2
  filter_upwards [ae_all_iff.2 h1] with Φ hΦ
  funext q
  exact clippedCoord_of_lt q.2 (hΦ q.1)

variable (Ev : Set (CTorus d L N₁ m₁ (k + 1)) →
  RawData d L (N₁ * L ^ m₁) (k + 1) N × (S.U × Fin N → ℂ) → ℂ) (D : BgData S.G' N)

/-- **The remainder mark of the term `Ev Y`**: `R_Y(u, ψ̂) = remExt e_Y u` for
`e_Y(ζ) = Ev Y (rawOf D, ζ • ψ̂)`, at the clipped hat configuration `ψ̂ = obsHat Φ`. -/
noncomputable def obsRemG (Y : Set (CTorus d L N₁ m₁ (k + 1))) (u : ℂ)
    (Φ : ∀ b, (S.blockSplit m₀ hp).Ωb b) : ℂ :=
  remExt (fun ζ : ℂ => Ev Y (rawOf D, ζ • obsHat S m₀ hp Φ)) u

variable {S m₀ hp Ev D}
variable {A : Set (RawData d L (N₁ * L ^ m₁) (k + 1) N)} {cψ : ℝ}

/-- **Global bound**: `|R_Y(u, ψ̂(Φ))| ≤ 8 B q²` for all `u` and all block configurations. -/
theorem norm_obsRemG_le (hcψ : 0 < cψ) (hq : S.p₁ / cψ ≤ 1 / 4) (hr : rawOf D ∈ A)
    {Y : Set (CTorus d L N₁ m₁ (k + 1))}
    (hE : AnalyticOnNhd ℂ (Ev Y) (A ×ˢ {ψ : S.U × Fin N → ℂ | ∀ p, ‖ψ p‖ ≤ cψ})) {B : ℝ}
    (hB : ∀ x ∈ A ×ˢ {ψ : S.U × Fin N → ℂ | ∀ p, ‖ψ p‖ ≤ cψ}, ‖Ev Y x‖ ≤ B) (u : ℂ)
    (Φ : ∀ b, (S.blockSplit m₀ hp).Ωb b) :
    ‖obsRemG S m₀ hp Ev D Y u Φ‖ ≤ 8 * B * (S.p₁ / cψ) ^ 2 :=
  norm_remExt_ray_le hcψ hp hq hr hE hB (norm_obsHat_le S m₀ hp Φ) u

/-- **Analyticity** of `u ↦ R_Y(u, ψ̂(Φ))` on the disc `|u| < 3/2`. -/
theorem differentiableOn_obsRemG (hcψ : 0 < cψ) (hq : S.p₁ / cψ ≤ 1 / 4) (hr : rawOf D ∈ A)
    {Y : Set (CTorus d L N₁ m₁ (k + 1))}
    (hE : AnalyticOnNhd ℂ (Ev Y) (A ×ˢ {ψ : S.U × Fin N → ℂ | ∀ p, ‖ψ p‖ ≤ cψ}))
    (Φ : ∀ b, (S.blockSplit m₀ hp).Ωb b) :
    DifferentiableOn ℂ (fun u => obsRemG S m₀ hp Ev D Y u Φ) (ball 0 (3 / 2)) :=
  differentiableOn_remExt_ray hcψ hp hq hr hE (norm_obsHat_le S m₀ hp Φ)

/-- **Measurability** in the block configuration, for every `u`. -/
theorem measurable_obsRemG (hcψ : 0 < cψ) (hq : S.p₁ / cψ ≤ 1 / 4) (hr : rawOf D ∈ A)
    {Y : Set (CTorus d L N₁ m₁ (k + 1))}
    (hE : AnalyticOnNhd ℂ (Ev Y) (A ×ˢ {ψ : S.U × Fin N → ℂ | ∀ p, ‖ψ p‖ ≤ cψ})) (u : ℂ) :
    Measurable (obsRemG S m₀ hp Ev D Y u) :=
  measurable_ray_rem hcψ hp hq hr hE (measurable_obsHat S m₀ hp) (norm_obsHat_le S m₀ hp) u

/-- **Block dependence**: `R_Y(u, ψ̂(Φ))` depends on `Φ` only through the blocks of the cube label
of `Y`, by the locality `AgHatDir` of the term. -/
theorem depOn_obsRemG (hN : L ^ m₀ ∣ N₁) (hcψ : 0 < cψ) (hq : S.p₁ / cψ ≤ 1 / 4)
    (hr : rawOf D ∈ A) {Y : Set (CTorus d L N₁ m₁ (k + 1))} (hY : IsDj m₀ (k + 1) Y)
    (hd : ∀ u ∈ A ×ˢ {ψ : S.U × Fin N → ℂ | ∀ p, ‖ψ p‖ ≤ cψ},
      ∀ u' ∈ A ×ˢ {ψ : S.U × Fin N → ℂ | ∀ p, ‖ψ p‖ ≤ cψ},
        AgHatDir S.hG' Y u u' → Ev Y u = Ev Y u') (u : ℂ) :
    DepOn (Ω := (S.blockSplit m₀ hp).Ωb) (blocksOf (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (K := k + 1) m₀ (k + 1) Set.univ Y) (obsRemG S m₀ hp Ev D Y u) := by
  intro Φ Φ' h
  unfold obsRemG
  refine remExt_ray_congr hcψ hp hq (fun ζ hζ => ?_) u
  refine hd (rawOf D, ζ • obsHat S m₀ hp Φ) ⟨hr, smul_mem_ball_p hp (norm_obsHat_le S m₀ hp Φ) (by simpa using hζ)⟩
    (rawOf D, ζ • obsHat S m₀ hp Φ') ⟨hr, smul_mem_ball_p hp (norm_obsHat_le S m₀ hp Φ') (by simpa using hζ)⟩
    ⟨agreeOn_refl _ _, fun y' hy' i => ?_⟩
  have hT := cellOf_mem_obsRowLabel S hN hY hy' (rfl : unitPt S.hG' y' = unitPt S.hG' y')
  have := depOn_blockMark S m₀ hp (unitPt S.hG' y') i hT Φ Φ' h
  simp only [Pi.smul_apply, smul_eq_mul]
  show ζ * blockMark S m₀ hp _ i Φ = ζ * blockMark S m₀ hp _ i Φ'
  rw [this]

theorem obsRowCoeff_eq_single [DecidableEq (S.U × Fin N)] (q : S.U × Fin N)
    (Y : Set (CTorus d L N₁ m₁ (k + 1))) :
    hatCoeff (Ev Y) (rawOf D) (Pi.single q 1) = obsRowCoeff S Ev D q Y := by
  unfold obsRowCoeff obsUnitVec
  congr 2
  exact Subsingleton.elim _ _

/-- **Kernel plus remainder, exactly.**  For the expanded function `F` (equal to `Σ_Y Ev Y` on the
hat ball) and `|t| < 3/2`:
`d/dt F(t ψ̂) = Σ_q ψ̂_q · Σ_Y a_Y(q) + Σ_Y R_Y(t, ψ̂)` at `ψ̂ = obsHat Φ`, where
`a_Y(q) = obsRowCoeff` are the coefficients of the landed kernel. -/
theorem obsRemG_ray_decomp (hcψ : 0 < cψ) (hq : S.p₁ / cψ ≤ 1 / 4) (hr : rawOf D ∈ A)
    {𝒴 : Finset (Set (CTorus d L N₁ m₁ (k + 1)))}
    (ha : ∀ Y ∈ 𝒴, AnalyticOnNhd ℂ (Ev Y) (A ×ˢ {ψ : S.U × Fin N → ℂ | ∀ p, ‖ψ p‖ ≤ cψ}))
    {F : (S.U × Fin N → ℂ) → ℂ}
    (hF : ∀ ψ : S.U × Fin N → ℂ, (∀ p, ‖ψ p‖ ≤ cψ) → F ψ = ∑ Y ∈ 𝒴, Ev Y (rawOf D, ψ))
    (Φ : ∀ b, (S.blockSplit m₀ hp).Ωb b) {t : ℂ} (ht : ‖t‖ < 3 / 2) :
    deriv (fun ζ : ℂ => F (ζ • obsHat S m₀ hp Φ)) t =
      ∑ q, obsHat S m₀ hp Φ q * ∑ Y ∈ 𝒴, obsRowCoeff S Ev D q Y +
        ∑ Y ∈ 𝒴, obsRemG S m₀ hp Ev D Y t Φ := by
  classical
  have := ray_decomp (𝒴 := 𝒴) (E := fun Y => Ev Y) (r := rawOf D) hcψ hp hq hr ha
    (norm_obsHat_le S m₀ hp Φ) hF ht
  rw [this]
  simp only [obsRowCoeff_eq_single]
  rfl

end Block

/-! ### The index type, the labels and the constants -/

section Index

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) (m₀ : ℕ) (hp : 0 < S.p₁)
  (Ev : Set (CTorus d L N₁ m₁ (k + 1)) →
    RawData d L (N₁ * L ^ m₁) (k + 1) N × (S.U × Fin N → ℂ) → ℂ) (D : BgData S.G' N)
  (𝒴 : Finset (Set (CTorus d L N₁ m₁ (k + 1))))

/-- **The remainder index type**: the polymer domains `Y ∈ 𝒴`, plus one dummy index `none` (so
that the type is nonempty even when `𝒴` is empty). -/
abbrev RemIdx : Type _ := Option {Y // Y ∈ 𝒴}

/-- **The remainder marks**: `G_Y(u, Φ) = R_Y(u, ψ̂(Φ))` for the domain `Y`, and `0` for the dummy
index. -/
noncomputable def obsGr : RemIdx 𝒴 → ℂ → (∀ b, (S.blockSplit m₀ hp).Ωb b) → ℂ
  | none, _, _ => 0
  | some Y, u, Φ => obsRemG S m₀ hp Ev D Y.1 u Φ

variable {Lb : Type*}

/-- **The labels of the remainder marks**: the label `lab Y` of the domain `Y`, and the label
`y₀` for the dummy index. -/
def obsRemLab (lab : {Y // Y ∈ 𝒴} → Lb) (y₀ : Lb) : RemIdx 𝒴 → Lb
  | none => y₀
  | some Y => lab Y

variable {S m₀ hp Ev D 𝒴}

theorem sum_obsGr (t : ℂ) (Φ : ∀ b, (S.blockSplit m₀ hp).Ωb b) :
    ∑ r, obsGr S m₀ hp Ev D 𝒴 r t Φ = ∑ Y ∈ 𝒴, obsRemG S m₀ hp Ev D Y t Φ := by
  rw [Fintype.sum_option]
  simp only [obsGr, zero_add]
  exact Finset.sum_coe_sort 𝒴 (fun Y => obsRemG S m₀ hp Ev D Y t Φ)

variable {A : Set (RawData d L (N₁ * L ^ m₁) (k + 1) N)} {cψ : ℝ}

/-- **The fields of the remainder marks** (conclusion of `obsRemainder_of_clauses`): with
`q = p₁ / cψ` and `c₀ = 8 C0 q²`,
`0 < c₀`; `boundr` with `F_r = c₀`; `measr`; `depr`; analyticity on `|u| < 3/2`; the root clause;
the weighted sum `Σ_r F_r e^{-κ0 𝗱(y_r)} ≤ c₀ (K0 + 1)`; almost-everywhere agreement of the clipped
and the unclipped remainder. -/
def ObsRemFields (S : StepSetting d L N₁ m₁ k N ϱ) (m₀ : ℕ) (hp : 0 < S.p₁)
    (Ev : Set (CTorus d L N₁ m₁ (k + 1)) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (S.U × Fin N → ℂ) → ℂ) (D : BgData S.G' N)
    (𝒴 : Finset (Set (CTorus d L N₁ m₁ (k + 1)))) (cψ C0 κG κ0 : ℝ)
    (Lab : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ Lb)
    (lab : {Y // Y ∈ 𝒴} → Lb) (y₀ : Lb)
    (bx : CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1) Set.univ) :
    Prop :=
    0 < 8 * C0 * (S.p₁ / cψ) ^ 2 ∧
    (∀ r u Φ, ‖obsGr S m₀ hp Ev D 𝒴 r u Φ‖ ≤
      8 * C0 * (S.p₁ / cψ) ^ 2 * Real.exp (-κG * Lab.dl (obsRemLab 𝒴 lab y₀ r))) ∧
    (∀ r u, Measurable (obsGr S m₀ hp Ev D 𝒴 r u)) ∧
    (∀ r u, DepOn (Ω := (S.blockSplit m₀ hp).Ωb)
      (blocksOf (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1) Set.univ
        (Lab.ysite (obsRemLab 𝒴 lab y₀ r))) (obsGr S m₀ hp Ev D 𝒴 r u)) ∧
    (∀ r Φ, DifferentiableOn ℂ (fun u => obsGr S m₀ hp Ev D 𝒴 r u Φ) (ball 0 (3 / 2))) ∧
    (∀ r, bx ∈ blocksOf (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ (Lab.ysite (obsRemLab 𝒴 lab y₀ r))) ∧
    (∑ r, 8 * C0 * (S.p₁ / cψ) ^ 2 * Real.exp (-κ0 * Lab.dl (obsRemLab 𝒴 lab y₀ r)) ≤
      8 * C0 * (S.p₁ / cψ) ^ 2 * (K0 d L κ0 + 1)) ∧
    (∀ Y ∈ 𝒴, ∀ u, ∀ᵐ Φ ∂(Measure.pi (S.blockSplit m₀ hp).μ),
      obsRemG S m₀ hp Ev D Y u Φ =
        remExt (fun ζ : ℂ => Ev Y (rawOf D, ζ • obsHatTrue S m₀ hp Φ)) u)

/-- **The remainder marks of the sharp hat terms, from the clauses of the expansion.**

Premises: the clauses of the landed sharp hat expansion for the family `Ev` (analyticity `ha`,
locality `hd`, the decay bound `hb` with `C0 = Q δ₁`, `κd = 2 κdec`), `p₁ ≤ cψ / 4`, the labels
`lab Y` of the domains in a label system `Lab` (`ysite (lab Y) = Y`, `dl (lab Y) = d(Y)`), a label
`y₀` containing the root cube `bx` (for the dummy index), and `bx` in the cube label of every domain.
Conclusions, with `q = p₁ / cψ` and `c₀ = 8 C0 q²` (the constant `F_r` of every index):

1. `0 < c₀`;
2. `boundr`: `‖G_r(u, Φ)‖ ≤ c₀ e^{-κG 𝗱(y_r)}` for all `u` and `Φ` (`κG ≤ κd`);
3. `measr`, 4. `depr` (blocks of the label), 5. analyticity on `|u| < 3/2`, 6. the root clause;
7. the weighted sum `Σ_r F_r e^{-κ0 𝗱(y_r)} ≤ c₀ (K0 + 1)`;
8. almost everywhere, the clipped and the unclipped remainder agree. -/
theorem obsRemainder_of_clauses (hN : L ^ m₀ ∣ N₁) (hcψ : 0 < cψ) (hq : S.p₁ / cψ ≤ 1 / 4)
    (hr : rawOf D ∈ A)
    (ha : ∀ Y ∈ 𝒴, AnalyticOnNhd ℂ (Ev Y) (A ×ˢ {ψ : S.U × Fin N → ℂ | ∀ p, ‖ψ p‖ ≤ cψ}))
    (hdj : ∀ Y ∈ 𝒴, IsDj m₀ (k + 1) Y)
    (hd : ∀ Y ∈ 𝒴, ∀ u ∈ A ×ˢ {ψ : S.U × Fin N → ℂ | ∀ p, ‖ψ p‖ ≤ cψ},
      ∀ u' ∈ A ×ˢ {ψ : S.U × Fin N → ℂ | ∀ p, ‖ψ p‖ ≤ cψ},
        AgHatDir S.hG' Y u u' → Ev Y u = Ev Y u')
    {C0 κd : ℝ} (hC0 : 0 < C0)
    (hb : ∀ Y ∈ 𝒴, ∀ x ∈ A ×ˢ {ψ : S.U × Fin N → ℂ | ∀ p, ‖ψ p‖ ≤ cψ},
      ‖Ev Y x‖ ≤ C0 * Real.exp (-κd * treeLenCovOne m₀ (k + 1) Y))
    (Lab : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ Lb)
    (lab : {Y // Y ∈ 𝒴} → Lb) (y₀ : Lb)
    (hysite : ∀ Y, Lab.ysite (lab Y) = Y.1)
    (hdl : ∀ Y, Lab.dl (lab Y) = treeLenCovOne m₀ (k + 1) Y.1)
    (bx : CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1) Set.univ)
    (hbx : ∀ Y ∈ 𝒴, bx ∈ obsRowLabel m₀ (k + 1) Y)
    (hy₀ : bx ∈ blocksOf (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ (Lab.ysite y₀))
    {κG κ0 : ℝ} (hκG : κG ≤ κd) (hκ0 : aEnt d L + 1 ≤ κ0) :
    ObsRemFields S m₀ hp Ev D 𝒴 cψ C0 κG κ0 Lab lab y₀ bx := by
  unfold ObsRemFields
  have hpc : 0 < S.p₁ / cψ := div_pos hp hcψ
  have hc0 : 0 < 8 * C0 * (S.p₁ / cψ) ^ 2 := by positivity
  have htl : ∀ Y : {Y // Y ∈ 𝒴}, 0 ≤ treeLenCovOne m₀ (k + 1) Y.1 := fun Y => by
    rw [← hdl Y]; exact Lab.dl_nonneg _
  refine ⟨hc0, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r u Φ
    cases r with
    | none =>
      simp only [obsGr, norm_zero]; positivity
    | some Y =>
      simp only [obsGr, obsRemLab]
      refine (norm_obsRemG_le hcψ hq hr (ha Y.1 Y.2) (hb Y.1 Y.2) u Φ).trans ?_
      rw [hdl Y, show 8 * (C0 * Real.exp (-κd * treeLenCovOne m₀ (k + 1) Y.1)) * (S.p₁ / cψ) ^ 2 =
        8 * C0 * (S.p₁ / cψ) ^ 2 * Real.exp (-κd * treeLenCovOne m₀ (k + 1) Y.1) by ring]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hc0.le
      nlinarith [htl Y]
  · intro r u
    cases r with
    | none => exact measurable_const
    | some Y => exact measurable_obsRemG hcψ hq hr (ha Y.1 Y.2) u
  · intro r u
    cases r with
    | none => exact fun Φ Φ' _ => rfl
    | some Y =>
      simp only [obsRemLab, hysite Y]
      exact depOn_obsRemG hN hcψ hq hr (hdj Y.1 Y.2) (hd Y.1 Y.2) u
  · intro r Φ
    cases r with
    | none => exact differentiableOn_const _
    | some Y => exact differentiableOn_obsRemG hcψ hq hr (ha Y.1 Y.2) Φ
  · intro r
    cases r with
    | none => exact hy₀
    | some Y => simp only [obsRemLab, hysite Y]; exact hbx Y.1 Y.2
  · rw [Fintype.sum_option]
    simp only [obsRemLab, hdl]
    have hK := entropy_thick hN le_rfl 𝒴 hdj hκ0 bx
    have hκ00 : 0 ≤ κ0 := by linarith [aEnt_nonneg d L]
    have h1 : Real.exp (-κ0 * Lab.dl y₀) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith [Lab.dl_nonneg y₀]
    have h2 : ∑ Y : {Y // Y ∈ 𝒴}, Real.exp (-κ0 * treeLenCovOne m₀ (k + 1) Y.1) ≤ K0 d L κ0 := by
      refine le_trans (le_of_eq ?_) hK
      refine Finset.sum_congr rfl fun Y _ => ?_
      simp [mem_blocksOf.1 (hbx Y.1 Y.2)]
    rw [← Finset.mul_sum]
    nlinarith [mul_le_mul_of_nonneg_left h1 hc0.le, mul_le_mul_of_nonneg_left h2 hc0.le]
  · intro Y hY u
    filter_upwards [ae_obsHat_eq_true S m₀ hp] with Φ hΦ
    simp only [obsRemG, hΦ]

end Index

/-! ### The remainder marks under the premises of the sharp hat expansion -/

section SharpHat

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ)
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ} {X₁f : Finset (CTorus d L N₁ m₁ (k + 1))} {j : ℕ}
variable {m₀ : ℕ} {X 𝒦X : Set (CTorus d L N₁ m₁ (k + 1))}

omit [NeZero L] in
theorem cK2'_pos_of {B : ℝ} (hB : 0 ≤ B) : 0 < cK2' d L N B := by
  have h1 := cA_ge d L N
  have h2 := cF_pos d L
  unfold cK2' cN'
  positivity

/-- **The remainder marks of the sharp hat terms** (`_of_sharpHat`).  Premises: exactly those of
`obsRowCoeff_of_sharpHat` that are used here (`FlCore`, the covering setup, the optimal tree; the
numerical premises of the landed `fsite_expansion_hat_dir` enter only through the clauses of `Ev`),
`0 < p₁`,
`p₁ ≤ cψ / 4`, the family `Ev` with the four clauses the landed theorem gives it (expansion,
locality, decay, analyticity), and a label system `Lab` containing the domains of the expansion
(`lab Y` with site set `Y` and size `d^cov(Y)`; `y₀` a label containing the root cube, for the dummy
index).  For every datum `D` of `Ξ`:

* `ObsRemFields` with `C0 = Q δ₁`, `bx` the root cube of `y`, `κG ≤ 2 κdec`: the global bound
  `8 Q δ₁ q²` (`q = p₁/cψ`), measurability, block dependence, analyticity on `|u| < 3/2`, the root
  clause, the weighted sum, almost-everywhere agreement with the unclipped remainder;
* **kernel plus remainder**: for `|t| < 3/2` and every block configuration `Φ`, the derivative at
  `t` of the expanded function along the ray `ζ ↦ ζ • ψ̂(Φ)` equals
  `Σ_q ψ̂_q Σ_Y a_Y(q) + Σ_r G_r(t, Φ)` with `a_Y = obsRowCoeff`. -/
theorem obsRemainder_of_sharpHat (hC : FlCore N S.G' Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (cc : ℂ) {cψ : ℝ} (hcψ : 0 < cψ)
    (hcov : CovSetup S.G' m₀ j X 𝒦X)
    (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) = X1 S.G' m₀ j 𝒦X)
    (hopt : ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X) ∧ MeetsOne m₀ j 𝒦X W₀ ∧
        bondCost (scaleW L m₀ m₁ j) E₀ = treeLenCovOne m₀ j X)
    {κdec : ℝ}
    (y : CTorus d L N₁ m₁ (k + 1)) (hy : y ∈ X₁f) (iy : Fin N)
    (hp : 0 < S.p₁) (hq : S.p₁ / cψ ≤ 1 / 4)
    (Ev : Set (CTorus d L N₁ m₁ (k + 1)) →
        RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts S.G' × Fin N → ℂ) → ℂ)
    (hs : ∀ D : BgData S.G' N, XiCData S.G' (compWeight L a₁) ν (k + 1) 1 eps D →
        ∀ ψh : unitPts S.G' × Fin N → ℂ, (∀ p, ‖ψh p‖ ≤ cψ) →
        svec Hm (flFieldOne S.G' Hm BG₂ κ a₁ ν D (hatLift S.G' a₁ ν S.hG' cc D ψh)) y iy =
        ∑ Y ∈ polymerDomains (fun i : ParIdx S.G' (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1)
          S.G' m₀ (X1 S.G' m₀ j 𝒦X), Ev Y (rawOf D, ψh))
    (hd : ∀ Y, ∀ u ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        ∀ u' ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        AgHatDir S.hG' Y u u' → Ev Y u = Ev Y u')
    (hb : ∀ Y, ∀ u ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        ‖Ev Y u‖ ≤ (cK2' d L N (famConst d L BG₂ κ) * δ₁) *
          Real.exp (-2 * κdec * treeLenCov S.G' m₀ Y))
    (ha : ∀ Y, AnalyticOnNhd ℂ (Ev Y) (XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ}))
    {Lb : Type*}
    (Lab : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ Lb)
    (lab : {Y // Y ∈ polymerDomains
      (fun i : ParIdx S.G' (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1)
      S.G' m₀ (X1 S.G' m₀ j 𝒦X)} → Lb) (y₀ : Lb)
    (hysite : ∀ Y, Lab.ysite (lab Y) = Y.1)
    (hdl : ∀ Y, Lab.dl (lab Y) = treeLenCovOne m₀ (k + 1) Y.1)
    (hy₀ : rootCube (m₀ := m₀) (blockIndex y) ∈ blocksOf (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (K := k + 1) m₀ (k + 1) Set.univ (Lab.ysite y₀))
    {κG κ0 : ℝ} (hκG : κG ≤ 2 * κdec) (hκ0 : aEnt d L + 1 ≤ κ0) :
    ∀ D : BgData S.G' N, XiCData S.G' (compWeight L a₁) ν (k + 1) 1 eps D →
      ObsRemFields S m₀ hp Ev D (polymerDomains
        (fun i : ParIdx S.G' (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1)
        S.G' m₀ (X1 S.G' m₀ j 𝒦X)) cψ (cK2' d L N (famConst d L BG₂ κ) * δ₁) κG κ0 Lab lab y₀
        (rootCube (m₀ := m₀) (blockIndex y)) ∧
      ∀ (Φ : ∀ b, (S.blockSplit m₀ hp).Ωb b) (t : ℂ), ‖t‖ < 3 / 2 →
        deriv (fun ζ : ℂ => svec Hm (flFieldOne S.G' Hm BG₂ κ a₁ ν D
            (hatLift S.G' a₁ ν S.hG' cc D (ζ • obsHat S m₀ hp Φ))) y iy) t =
          ∑ q, obsHat S m₀ hp Φ q * ∑ Y ∈ polymerDomains
            (fun i : ParIdx S.G' (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1)
            S.G' m₀ (X1 S.G' m₀ j 𝒦X), obsRowCoeff S Ev D q Y +
          ∑ r, obsGr S m₀ hp Ev D (polymerDomains
            (fun i : ParIdx S.G' (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1)
            S.G' m₀ (X1 S.G' m₀ j 𝒦X)) r t Φ := by
  classical
  intro D hD
  have hd3 : 3 ≤ d := hC.HBp.hd
  have hN : L ^ m₀ ∣ N₁ := hcov.hN
  have hdj : ∀ Y ∈ polymerDomains (fun i : ParIdx S.G' (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) =>
      i.1.1) S.G' m₀ (X1 S.G' m₀ j 𝒦X), IsDj m₀ (k + 1) Y := fun Y hY =>
    isDj_of_polymerDomains (fun i : ParIdx S.G' (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1)
      S.hG' hcov hd3 (fun i => i.1.2) hopt hY
  have hxX : y ∈ X1 S.G' m₀ j 𝒦X := by rw [← hX₁]; exact hy
  have hr : rawOf D ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps := ⟨D, hD, rfl⟩
  have hd0 : 0 < d := by omega
  have hB0 : 0 ≤ famConst d L BG₂ κ := by
    have := famConst_ge_one (L := L) hC.hS2.fam.2.1 κ hd0; linarith
  have hC0 : 0 < cK2' d L N (famConst d L BG₂ κ) * δ₁ :=
    mul_pos (cK2'_pos_of hB0) hC.δ₁_pos
  have hbx : ∀ Y ∈ polymerDomains
      (fun i : ParIdx S.G' (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1)
      S.G' m₀ (X1 S.G' m₀ j 𝒦X), rootCube (m₀ := m₀) (blockIndex y) ∈ obsRowLabel m₀ (k + 1) Y :=
    fun Y hY => rootCube_mem_obsRowLabel_of_polymerDomains
      (fun i : ParIdx S.G' (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) hN S.hG' hcov hd3
      (fun i => i.1.2) hopt rfl hY hxX
  have hb' : ∀ Y ∈ polymerDomains
      (fun i : ParIdx S.G' (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1)
      S.G' m₀ (X1 S.G' m₀ j 𝒦X), ∀ x ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        ‖Ev Y x‖ ≤ (cK2' d L N (famConst d L BG₂ κ) * δ₁) *
          Real.exp (-(2 * κdec) * treeLenCovOne m₀ (k + 1) Y) := by
    intro Y _ x hx
    have := hb Y x hx
    rwa [treeLenCov_eq_treeLenCovOne S.hG' m₀ Y, show -2 * κdec = -(2 * κdec) by ring] at this
  refine ⟨obsRemainder_of_clauses hN hcψ hq hr (fun Y _ => ha Y) hdj (fun Y _ => hd Y) hC0 hb'
    Lab lab y₀ hysite hdl _ hbx hy₀ hκG hκ0, fun Φ t ht => ?_⟩
  rw [sum_obsGr]
  exact obsRemG_ray_decomp hcψ hq hr (fun Y _ => ha Y)
    (F := fun ψ => svec Hm (flFieldOne S.G' Hm BG₂ κ a₁ ν D (hatLift S.G' a₁ ν S.hG' cc D ψ)) y iy)
    (fun ψ hψ => hs D hD ψ hψ) Φ ht

end SharpHat

end Balaban.Fluctuation
