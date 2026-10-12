/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.PsiZeroHessInput
public import Balaban.LargeField.R.PsiZeroHessGrad

/-!
# The upper Hessian bound of the effective action (Lemma III.8.2, the quadratic form bounded above)

The sandwich of `PsiZeroHessEnv` (`effAction_sandwich`) also bounds the Hessian of `effOn` from above: along a
perturbation `v` supported over the top layer,
`F(t) ≤ F(0) + t b₁ + A(t J v, 0)` with `A(tJv, 0) = ½ a_k L^{k(d-2)} t² ‖v‖²`, so that
`⟨v, D²F v⟩ ≤ a_k L^{k(d-2)} ‖v‖² ≤ 2 L^{k(d-2)} ‖v‖²` (`effOn_hess_le`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background Filter Topology

/-- Second-order touching from above only: a parabola bound from above forces `g'' ≤ 2C`. -/
theorem hess_upper_of_upper {g g' : ℝ → ℝ} {g2 b C : ℝ}
    (hd : ∀ᶠ t in 𝓝 (0 : ℝ), HasDerivAt g (g' t) t) (hd2 : HasDerivAt g' g2 0)
    (hup : ∀ᶠ t in 𝓝 (0 : ℝ), g t ≤ g 0 + b * t + C * t ^ 2) : g' 0 = b ∧ g2 ≤ 2 * C := by
  have h0 : HasDerivAt g (g' 0) 0 := hd.self_of_nhds
  have hb := deriv_eq_of_upper h0 hup
  refine ⟨hb, ?_⟩
  by_contra hlt
  push Not at hlt
  set s := g2 - 2 * C with hs
  have hpos : 0 < s := by linarith
  have hh2 : HasDerivAt (fun t => g' t - b - 2 * C * t) s 0 := by
    refine ((hd2.sub_const b).sub ((hasDerivAt_id' (0 : ℝ)).const_mul (2 * C))).congr_deriv ?_
    simp [hs]
  have hz : g' 0 - b - 2 * C * 0 = 0 := by rw [hb]; ring
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < g' t - b - 2 * C * t := by
    have hslope := hh2.tendsto_slope_zero_right
    have : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t⁻¹ • ((g' (0 + t) - b - 2 * C * (0 + t)) -
        (g' 0 - b - 2 * C * 0)) := hslope.eventually (lt_mem_nhds hpos)
    filter_upwards [this, self_mem_nhdsWithin] with t ht htpos
    have htpos' : (0 : ℝ) < t := htpos
    simp only [zero_add, hz, sub_zero, smul_eq_mul] at ht
    by_contra hge
    push Not at hge
    have : t⁻¹ * (g' t - b - 2 * C * t) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.2 htpos'.le) hge
    linarith
  obtain ⟨ε, hε, hεsub⟩ : ∃ ε > 0, ∀ t, 0 < t → t < ε →
      0 < g' t - b - 2 * C * t ∧ HasDerivAt g (g' t) t := by
    have h2 : ∀ᶠ t in 𝓝[>] (0 : ℝ), HasDerivAt g (g' t) t := nhdsWithin_le_nhds hd
    have h3 := hev.and h2
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at h3
    obtain ⟨ε, hε, h⟩ := h3
    refine ⟨ε, hε, fun t ht0 htε => h ?_ ht0⟩
    rw [Real.dist_eq, sub_zero, abs_of_pos ht0]; exact htε
  have hlow : ∀ᶠ t in 𝓝[>] (0 : ℝ), g t - g 0 - b * t - C * t ^ 2 ≤ 0 := by
    filter_upwards [nhdsWithin_le_nhds hup] with t ht
    linarith
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hlow
  obtain ⟨ρ, hρ, hρ'⟩ := hlow
  set t := min (ε / 2) (ρ / 2) with ht
  have htpos : 0 < t := lt_min (by linarith) (by linarith)
  have htε : t < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have htρ : t < ρ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hge := hρ' (by rw [Real.dist_eq, sub_zero, abs_of_pos htpos]; exact htρ) htpos
  have hderiv : ∀ x ∈ Set.Ioo 0 t, HasDerivAt (fun y => g y - g 0 - b * y - C * y ^ 2)
      (g' x - b - 2 * C * x) x := by
    intro x hx
    have hx' := (hεsub x hx.1 (lt_trans hx.2 htε)).2
    refine (hasDerivAt_parab (g0 := g 0) (b := b) (M := C) hx').congr_deriv ?_
    ring
  have hcont : ContinuousOn (fun y => g y - g 0 - b * y - C * y ^ 2) (Set.Icc 0 t) := by
    intro x hx
    rcases eq_or_lt_of_le hx.1 with h | h
    · subst h
      have : ContinuousAt g 0 := h0.continuousAt
      exact (((this.sub continuousAt_const).sub (continuousAt_const.mul continuousAt_id)).sub
        (continuousAt_const.mul (continuousAt_id.pow 2))).continuousWithinAt
    · have hx' := (hεsub x h (lt_of_le_of_lt hx.2 htε)).2
      exact (((hx'.continuousAt.sub continuousAt_const).sub (continuousAt_const.mul continuousAt_id)).sub
        (continuousAt_const.mul (continuousAt_id.pow 2))).continuousWithinAt
  obtain ⟨ξ, hξ, hξe⟩ := exists_hasDerivAt_eq_slope (fun y => g y - g 0 - b * y - C * y ^ 2)
    (fun x => g' x - b - 2 * C * x) htpos hcont hderiv
  have hξpos := (hεsub ξ hξ.1 (lt_trans hξ.2 htε)).1
  simp only [sub_self, mul_zero, sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at hξe
  have : g t - g 0 - b * t - C * t ^ 2 = (g' ξ - b - 2 * C * ξ) * t := by
    field_simp at hξe
    linarith
  nlinarith [mul_pos hξpos htpos]

section Upper

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ k ϱ} {a : ℕ → ℝ}
  {Z : Finset (Torus d (N₀ * L ^ (k - k)))}

/-- **Upper Hessian bound from the sandwich**: the second derivative of `effOn` at `ψ↾Z` in a direction `v`
supported over the top layer is at most `2 A(Jv, 0)`. -/
theorem effOn_hess_le_action (H : BgHyp d L k ϱ a 0) (hk : 1 ≤ k) {η : ℝ} (hη : 0 < η)
    (hη0 : η ≤ bgC0 d L N) (hη1 : η ≤ bgC1 d L N) (hΩ : OverTop G (Z : Set (Torus d (N₀ * L ^ (k - k)))))
    {ψ : BlockField d L N₀ k N} (ht : TubeOn G Set.univ η ψ) (v : SuppSpace Z N) :
    fderiv ℝ (fderiv ℝ (effOn G a Z ψ)) (restrictSupp Z ψ) v v ≤
      2 * action G a 0 ((bgZero G N).lineAt (topTangent G v) (1 : ℝ)) 0 := by
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
  have hup : ∀ᶠ t in 𝓝 (0 : ℝ), (fun s : ℝ => effOn G a Z ψ (x0 + s • v)) t ≤
      (fun s : ℝ => effOn G a Z ψ (x0 + s • v)) 0 + (firstVar a D E (bgField G a 0 D)).re * t +
        action G a 0 ((bgZero G N).lineAt E (1 : ℝ)) 0 * t ^ 2 := by
    filter_upwards [hev] with t htube
    have hDt : InUnionDomainR G (bgC1 d L N) 0 (D.lineAt E (t : ℂ)) := by
      have := inUnionDomainR_of_tube G hη hη1 htube
      rwa [hD, hE, ← dataR_merge_line ψ v t]
    have hFt : effOn G a Z ψ (x0 + t • v) =
        action G a 0 (D.lineAt E (t : ℂ)) (bgField G a 0 (D.lineAt E (t : ℂ))) := by
      show effAction G a (mergeField Z ψ (x0 + t • v)) = _
      unfold effAction
      rw [hD, hE, ← dataR_merge_line ψ v t]
    obtain ⟨h1, -⟩ := effAction_sandwich H hDdom hER hEo hEh t hDt
    have hsc := action_zero_line_scale (a := a) E hEo hEh t
    simp only [hFt, hg0]
    rw [hsc] at h1
    linarith
  have := (hess_upper_of_upper hd hd2 hup).2
  simpa using this

variable [NeZero N]

/-- The weighted sum over `Ω₁` of the tangent datum of a perturbation of the top blocks. -/
theorem sum_topTangent (hΩ : OverTop G (Z : Set (Torus d (N₀ * L ^ (k - k))))) (hk : 1 ≤ k) (v : SuppSpace Z N) :
     ∑ x : G.Ω 1, (a (G.layerIndex (x : Torus d (N₀ * L ^ k))) /
      ((L : ℝ) ^ G.layerIndex (x : Torus d (N₀ * L ^ k))) ^ 2) *
      ∑ i, ‖(topTangent G v).Ψ x i‖ ^ 2 = a k * (L : ℝ) ^ (k * d) / (L : ℝ) ^ (2 * k) * ‖v‖ ^ 2 := by
  classical
  set F : Torus d (N₀ * L ^ k) → ℝ := fun x => (a (G.layerIndex x) / ((L : ℝ) ^ G.layerIndex x) ^ 2) *
      ∑ i, ‖(topTangent G v).Ψ x i‖ ^ 2 with hF
  have h1 : ∑ x : G.Ω 1, F x = ∑ x ∈ G.Ω 1, F x := Finset.sum_coe_sort (G.Ω 1) F
  have hzero : ∀ x, jBlock d L N₀ k k x ∉ Z → F x = 0 := by
    intro x hx
    have : ∀ i, (topTangent G v).Ψ x i = 0 := by
      intro i
      by_cases hds : x ∈ dataSites G
      · rw [topTangent_Ψ v hds]; simp [extSupp, hx]
      · simp [(topTangent G v).Ψ_zero x hds]
    simp [hF, this]
  have h2 : ∑ x ∈ G.Ω 1, F x = ∑ x, F x := by
    refine Finset.sum_subset (Finset.subset_univ _) (fun x _ hx => ?_)
    have : ∀ i, (topTangent G v).Ψ x i = 0 := fun i => by
      rw [topTangent_zero_off hΩ hk v hx]; rfl
    simp [hF, this]
  have h3 : ∑ x, F x = ∑ x ∈ Finset.univ.filter (fun x => jBlock d L N₀ k k x ∈ Z), F x := by
    symm
    refine Finset.sum_subset (Finset.filter_subset _ _) (fun x _ hx => hzero x ?_)
    simpa using hx
  have h4 := Finset.sum_fiberwise_of_maps_to (s := Finset.univ.filter (fun x : Torus d (N₀ * L ^ k) => jBlock d L N₀ k k x ∈ Z))
    (t := Z) (g := jBlock d L N₀ k k) (f := F) (fun x hx => by simpa using hx)
  have h5 : ∀ z ∈ Z, ∑ x ∈ (Finset.univ.filter (fun x : Torus d (N₀ * L ^ k) => jBlock d L N₀ k k x ∈ Z)).filter
      (fun x => jBlock d L N₀ k k x = z), F x = a k * (L : ℝ) ^ (k * d) / (L : ℝ) ^ (2 * k) * ‖extSupp Z v z‖ ^ 2 := by
    intro z hz
    obtain ⟨hcnt, hall⟩ := topLift_block_count hΩ hk hz
    have : (Finset.univ.filter (fun x : Torus d (N₀ * L ^ k) => jBlock d L N₀ k k x ∈ Z)).filter
        (fun x => jBlock d L N₀ k k x = z) = Finset.univ.filter (fun x => jBlock d L N₀ k k x = z) := by
      ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · exact fun h => h.2
      · exact fun h => ⟨h ▸ hz, h⟩
    rw [this]
    have hx : ∀ x ∈ Finset.univ.filter (fun x : Torus d (N₀ * L ^ k) => jBlock d L N₀ k k x = z),
        F x = a k / (L : ℝ) ^ (2 * k) * ‖extSupp Z v z‖ ^ 2 := by
      intro x hxx
      have hxz : jBlock d L N₀ k k x = z := by simpa using hxx
      obtain ⟨-, hds, hlay, -⟩ := topLift_extSupp hΩ hk v (x := x) (hxz ▸ hz) 0
      have hΨ : ∀ i, ‖(topTangent G v).Ψ x i‖ ^ 2 = (extSupp Z v z i) ^ 2 := by
        intro i
        rw [topTangent_Ψ v hds, hxz]
        simp
      simp only [hF, hlay, hΨ]
      rw [sq_norm_euc, ← pow_mul]
      ring
    rw [Finset.sum_congr rfl hx, Finset.sum_const, nsmul_eq_mul, hcnt]
    push_cast
    rw [← pow_mul, pow_mul']
    ring
  rw [h1, h2, h3, ← h4, Finset.sum_congr rfl h5, ← Finset.mul_sum]
  congr 1
  rw [← sum_sq_extSupp]
  refine Finset.sum_subset (Finset.subset_univ _) (fun z _ hz => ?_)
  simp [extSupp, hz]

/-- `A(Jv, 0) = ½ a_k L^{k(d-2)} ‖v‖²`... in the unsimplified form `½ a_k L^{kd} L^{-2k} ‖v‖²`. -/
theorem action_topTangent (hΩ : OverTop G (Z : Set (Torus d (N₀ * L ^ (k - k))))) (hk : 1 ≤ k)
    (v : SuppSpace Z N) :
    action G a 0 ((bgZero G N).lineAt (topTangent G v) (1 : ℝ)) 0 =
      (1 / 2) * (a k * (L : ℝ) ^ (k * d) / (L : ℝ) ^ (2 * k) * ‖v‖ ^ 2) := by
  have hEo : ∀ x, x ∉ G.Ω 1 → (topTangent G v).Ψ x = 0 := fun x hx => topTangent_zero_off hΩ hk v hx
  have hEh : ∀ x, (topTangent G v).h x = 0 := fun x => funext fun i => topTangent_h v x i
  rw [← sum_topTangent hΩ hk v]
  unfold action
  have hb : ∀ s : ℂ, barField G ((bgZero G N).lineAt (topTangent G v) s).Ψ (0 : G.Ω 1 × Fin N → ℂ) = 0 :=
    fun s => by
      rw [barField_line (bgZero G N) (topTangent G v) hEo s]
      exact barField_zero _ (fun x _ => rfl)
  rw [hb, blockAvg_zero]
  simp [BgData.lineAt, bgZero, hEh]

/-- **The upper Hessian bound**: `⟨v, D²(effOn) v⟩ ≤ 2 L^{k(d-2)} ‖v‖²` at every point of the tube
(`a_k ≤ 2`). -/
theorem effOn_hess_le (H : BgHyp d L k ϱ a 0) (hk : 1 ≤ k) (hd : 2 ≤ d) {η : ℝ} (hη : 0 < η)
    (hη0 : η ≤ bgC0 d L N) (hη1 : η ≤ bgC1 d L N) (hΩ : OverTop G (Z : Set (Torus d (N₀ * L ^ (k - k)))))
    {ψ : BlockField d L N₀ k N} (ht : TubeOn G Set.univ η ψ) (v : SuppSpace Z N) :
    fderiv ℝ (fderiv ℝ (effOn G a Z ψ)) (restrictSupp Z ψ) v v ≤ 2 * (L : ℝ) ^ (k * (d - 2)) * ‖v‖ ^ 2 := by
  refine (effOn_hess_le_action H hk hη hη0 hη1 hΩ ht v).trans ?_
  rw [action_topTangent hΩ hk v]
  have hak : a k ≤ 2 := (H.weights k hk le_rfl).2
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have e : (L : ℝ) ^ (k * d) / (L : ℝ) ^ (2 * k) = (L : ℝ) ^ (k * (d - 2)) := by
    rw [div_eq_iff (by positivity), ← pow_add]
    congr 1
    obtain ⟨e, rfl⟩ : ∃ e, d = e + 2 := ⟨d - 2, by omega⟩
    simp only [Nat.add_sub_cancel]; ring
  have : a k * (L : ℝ) ^ (k * d) / (L : ℝ) ^ (2 * k) = a k * (L : ℝ) ^ (k * (d - 2)) := by
    rw [mul_div_assoc, e]
  rw [this]
  have hp : 0 ≤ (L : ℝ) ^ (k * (d - 2)) * ‖v‖ ^ 2 := by positivity
  nlinarith

end Upper

end Balaban.LargeField
