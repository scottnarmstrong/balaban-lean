/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepTowerThetaG
public import Balaban.Inhabited.DetOutputTermsWitnessG
public import Balaban.Inhabited.DetPackageFromTowerG
public import Balaban.Inhabited.StepScaleDataG
public import Balaban.Inhabited.RenormThetaChartTowerG
public import Balaban.Fluctuation.RenormThetaDatum
public import Balaban.Fluctuation.RenormThetaChart
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The two-radii determinant lemmas at the general tower

For `T : StepTowerThetaG d L N κmin`:

* `xiCData_mono_radius`: the chart grows with the radius (moved from `StepTowerTheta`);
* `renE0_theta_domain_of_le`, `exists_renDetGrouped_ambient_of_le`: the renormalized datum lies in
  the step chart at every radius `ε₂` at least the chart radius of the margin, and the regrouped
  determinant term has an ambient analytic extension (moved from `StepTowerTheta`);
* `StepTowerThetaG.detExpansion_scale`: the determinant family at chart radius `2 t`;
* `StepTowerThetaG.detGrouped_ambient`: the determinant part of `E0θ` on the renormalization
  domain with the ambient analytic extensions of the regrouped terms.

The fixed `3, 3, 2` statements `StepTowerTheta.detExpansion_scale` and
`StepTowerTheta.detGrouped_ambient` are the case `T = R.toG`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Analysis Balaban.Inhabited.LevelStep
  LocalCover Filter Topology

section Mono

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ k ϱ}
  {ν σ ε ε₂ : ℝ}

theorem xiCBounds_mono {Dr Dc : BgData G N} {Ψ'' h'' : Torus d (N₀ * L ^ k) → Fin N → ℂ}
    {φr φc : G.Ω 1 × Fin N → ℂ} {αr αc : G.Ω 1 → ℂ} (hσ : 0 ≤ σ) (hε0 : 0 < ε) (hε : ε ≤ ε₂)
    (hb : XiCBounds G ν σ ε Dr Dc Ψ'' h'' φr φc αr αc) :
    XiCBounds G ν σ ε₂ Dr Dc Ψ'' h'' φr φc αr αc := by
  have h1 : σ * ε ≤ σ * ε₂ := mul_le_mul_of_nonneg_left hε hσ
  have h2 : σ ^ 2 * ε ≤ σ ^ 2 * ε₂ := mul_le_mul_of_nonneg_left hε (by positivity)
  have hε2 : 0 < ε₂ := hε0.trans_le hε
  have hp : ∀ x : Torus d (N₀ * L ^ k), 0 < G.spacing x := fun x => by
    have := G.spacing_ge_one x; linarith
  have e : ∀ e : ℝ, 0 < e → (σ * e) ^ 2 / e = σ ^ 2 * e := fun e he => by field_simp
  refine ⟨fun x hx μ => ?_, fun x hx => ?_, fun x => ?_, fun x => ?_, fun x hx => ?_,
    fun z hz z' hz' hadj => ?_, fun x hx => ?_, fun x => ?_⟩
  · obtain ⟨g1, g2⟩ := hb.grad x hx μ
    exact ⟨g1.trans_le (div_le_div_of_nonneg_right h1 (hp x).le),
      g2.trans_le (div_le_div_of_nonneg_right h1 (hp x).le)⟩
  · exact (hb.lap x hx).trans_le (div_le_div_of_nonneg_right h2 (by have := hp x; positivity))
  · exact (hb.mult x).trans_le h2
  · exact (hb.val x).trans_le hε
  · exact (hb.close x hx).trans_le h2
  · exact (hb.collarBond z hz z' hz' hadj).trans_le h1
  · have := hb.hAbs x hx
    rw [e ε hε0] at this
    rw [e ε₂ hε2]
    exact this.trans_le h2
  · exact (hb.hDot x).trans_le (pow_le_pow_left₀ (mul_nonneg hσ hε0.le) h1 2)

theorem xiC_mono_radius {n : ℕ} {a : ℕ → ℝ} {Ψ₀ : Torus d (N₀ * L ^ k) → Fin N → ℝ}
    {h₀ : Fin N → ℝ} {Ψ'' h'' : Torus d (N₀ * L ^ k) → Fin N → ℂ} (hσ : 0 ≤ σ) (hε : ε ≤ ε₂)
    (h : XiC G a ν n σ ε Ψ₀ h₀ Ψ'' h'') : XiC G a ν n σ ε₂ Ψ₀ h₀ Ψ'' h'' := by
  obtain ⟨hs, hε0, Dr, Dc, hXr, hC, hU, hb⟩ := h
  exact ⟨hs, hε0.trans_le hε, Dr, Dc, ⟨hXr.1, hXr.2.1, xiBounds_mono hσ hε0.le hε hXr.2.2⟩, hC, hU,
    xiCBounds_mono hσ hε0 hε hb⟩

end Mono

section MonoData

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
  {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν σ ε ε₂ : ℝ} {n : ℕ}

/-- **Radius monotonicity of the chart**: `Ξ^c_n(𝔹; σ, ε) ⊆ Ξ^c_n(𝔹; σ, ε₂)` for `ε ≤ ε₂`. -/
theorem xiCData_mono_radius {D : BgData G N} (hσ : 0 ≤ σ) (hε : ε ≤ ε₂)
    (h : XiCData G a ν n σ ε D) : XiCData G a ν n σ ε₂ D := by
  obtain ⟨Ψ₀, h₀, Ψ'', h'', hX, hR⟩ := h
  exact ⟨Ψ₀, h₀, Ψ'', h'', xiC_mono_radius hσ hε hX, hR⟩

end MonoData

section Ambient

open Balaban.Fluctuation

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
variable {S : StepSetting d L N₁ m₁ k N ϱ}

/-- **The renormalized datum lies in the step chart at every radius `ε₂ ≥ εs`.**  This is
`renE0_theta_domain` followed by `xiCData_mono_radius`. -/
theorem renE0_theta_domain_of_le (S : StepSetting d L N₁ m₁ k N ϱ)
    (H : BgHyp d L (k + 1) ϱ S.a S.ν) (εren εstep ε₂ r₀ : ℝ)
    (hM : ThetaChartMargin d L N εren εstep r₀) (hle : εstep ≤ ε₂)
    (D : BgData S.G' N) (hD : XiCOneReal S.G' S.a S.ν εren D)
    (ξ : Fin 3 → ℂ) (hξ : ‖ξ‖ < r₀) :
    XiCData S.G' S.a S.ν (k + 1) 1 ε₂ (renThetaDatum S εren D ξ) :=
  xiCData_mono_radius zero_le_one hle (renE0_theta_domain S H εren εstep r₀ hM D hD ξ hξ)

/-- **The ambient analytic extension, for a record at a chart radius `ε₂ ≥ εs`.**  As
`exists_renDetGrouped_ambient`, with the record `E` at any radius `ε₂ ≥ εstep`. -/
theorem exists_renDetGrouped_ambient_of_le {m₀ : ℕ}
    {z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))} {εstep ε₂ κ'' cdet : ℝ}
    (E : DetExpansionLocC S m₀ z ε₂ κ'' cdet)
    (H : BgHyp d L (k + 1) ϱ S.a S.ν) (εren r₀ : ℝ)
    (hM : ThetaChartMargin d L N εren εstep r₀) (hle : εstep ≤ ε₂) (hm : m₀ = 1)
    (X : Set (CTorus d L N₁ m₁ (k + 1))) :
    ∃ F : RawData d L (N₁ * L ^ m₁) (k + 1) N × (Fin 3 → ℂ) → ℂ,
      AnalyticOnNhd ℂ F (expDom S.G' (XiCOneReal S.G' S.a S.ν εren) r₀) ∧
      ∀ (D : BgData S.G' N) (ξ : Fin 3 → ℂ), XiCOneReal S.G' S.a S.ν εren D → ‖ξ‖ < r₀ →
        F ((D.Ψ, D.h), ξ) = E.detGrouped (renThetaDatum S εren D ξ) X := by
  subst hm
  choose A hAan hAeq using E.analyticAt_raw
  refine ⟨fun q => ∑ T ∈ detCollarFibre 1 X,
    A T ((fun x i => (1 + renZeta εren q.2) * q.1.1 x i), q.1.2), ?_, ?_⟩
  · rintro ⟨p, ξ'⟩ ⟨D, hD, hp, hξ⟩
    simp only at hp hξ
    subst hp
    have hθ := renE0_theta_domain_of_le S H εren εstep ε₂ r₀ hM hle D hD ξ' hξ
    refine Finset.analyticAt_fun_sum _ fun T _ => ?_
    have hTh := analyticOnNhd_renThetaRaw εren Set.univ ((D.Ψ, D.h), ξ') trivial
    have hA : AnalyticAt ℂ (A T) ((fun x i => (1 + renZeta εren ξ') * D.Ψ x i), D.h) :=
      hAan T _ hθ
    exact AnalyticAt.comp_of_eq hA hTh rfl
  · intro D ξ hD hξ
    have hθ := renE0_theta_domain_of_le S H εren εstep ε₂ r₀ hM hle D hD ξ hξ
    unfold DetExpansionLocC.detGrouped detCollarGrouped
    refine Finset.sum_congr rfl fun T _ => ?_
    exact hAeq T _ hθ

end Ambient

section TowerFamilyG

variable {d L N : ℕ} [NeZero L] {κmin : ℝ}

/-- **The determinant family at every scale, at chart radius `2 t`, general `d`, `L`, `N`.**  For
every scale `k ≥ 1`, `L ∣ N₁`, `5 < N₁`, `0 ≤ ν`, `ν L^{2(k+1)} ≤ 1`: the datum of the step lies in
the chart at radius `2 t`, and for every root `z` the record has an element at radius `2 t` with
the rate and constant of `detExpansionLocC_scale_of_towerG` and the term formula. -/
theorem StepTowerThetaG.detExpansion_scale (T : StepTowerThetaG d L N κmin)
    (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (hLN : L ∣ N₁) (hN5 : 5 < N₁) {ν : ℝ}
    (hν0 : 0 ≤ ν) (hν : ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1) (β p₁ : ℝ) :
    XiCData (T.step k hk N₁ ν β p₁).G' (compWeight L 1) ν (k + 1) 1 (2 * T.t)
        (T.step k hk N₁ ν β p₁).D' ∧
      ∀ z, ∃ E : DetExpansionLocC (T.step k hk N₁ ν β p₁) 1 z (2 * T.t)
          ((T.κ - Real.log 2 - 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) / (2 * d * L))
          ((L : ℝ) ^ d * ((1 / 2 : ℝ) * N * covBLogMax d L T.κ /
            (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp T.κ)))),
        ∀ D T', E.term D T' = ∑ y ∈ (T.step k hk N₁ ν β p₁).blockU z,
          detActivityBg 1 (compWeight L 1) 1 ν (rho4 d L N T.BG T.κ) D y T' := by
  have h := detExpansionLocC_scale_of_towerG T.hd T.hL T.hN T.m₁_four
    (by have := T.t_pos; positivity) (Classical.choice T.core2) T.large_block T.dom_margin2
    T.coer_margin2 T.δc_small T.det_z k hk N₁ hLN hN5 hν0 hν β p₁ T.δ
  unfold StepTowerG.step
  exact h

/-- **The chart margin at any class radius `e ≤ t`, general tower**, with chart radius at most
`2 e`. -/
theorem StepTowerThetaG.thetaChartMargin_of_le {d L N : ℕ} [NeZero L] {κmin : ℝ}
    (T : StepTowerThetaG d L N κmin) {e : ℝ} (he : 0 < e) (het : e ≤ T.t) :
    ThetaChartMargin d L N e (e + xiK2 d L N * (3 / 2 * e * T.r₀)) T.r₀ ∧
      e + xiK2 d L N * (3 / 2 * e * T.r₀) ≤ 2 * e := by
  have hM := thetaChartMargin_of_stepTowerRenSolG T.toStepTowerRenSolG
  have hr := T.r₀_pos
  have hX : 0 ≤ xiC1 d := by unfold xiC1; positivity
  have hK1 := bgK1_pos d L N
  have hK2 := cK2_pos d L N
  have hxK : 0 < xiK2 d L N := by unfold xiK2; positivity
  have hδ : (3 / 2 : ℝ) * e * T.r₀ ≤ (3 / 2 : ℝ) * T.t * T.r₀ :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left het (by norm_num)) hr.le
  refine ⟨⟨he, hr, by positivity, hδ.trans hM.δ_one, ?_, ?_, hδ.trans hM.star, ?_, ?_, rfl⟩, ?_⟩
  · have := mul_le_mul_of_nonneg_left het (by positivity : (0 : ℝ) ≤ (4 * d + 6) * (2 * d + 1))
    have h2 := hM.small
    nlinarith
  · have := mul_le_mul_of_nonneg_left het hX
    linarith [hM.data]
  · have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left het hX) hK1.le
    linarith [hM.K₁]
  · have h1 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left het hX) hK1.le
    have h2 := mul_le_mul_of_nonneg_left hδ hK2.le
    linarith [hM.c₀]
  · have h := mul_le_mul_of_nonneg_left T.r₀_xi he.le
    nlinarith

/-- **The determinant part of `E0θ` at renormalization radius `e ≤ t`, at the general tower.**  At
every scale there is a family `E z` of determinant records at chart radius `2 t` with the term
formula, and

* the value at `ξ = 0`: `renE0θ_det e E z S.D' 0` is the determinant term
  `-(1/2) ∑_y ∑_i log A_C(y, i)(y, i)` of the step;
* for every root `z` and hull `X` an ambient function `F`, analytic on the renormalization domain
  `expDom (XiCOneReal … e) T.r₀`, equal there to the regrouped determinant term at the
  renormalized datum, bounded there by `C_hull e^{-λ_hull sizeJ X}`, and equal at `ξ = 0` to the
  regrouped term at the datum itself. -/
theorem StepTowerThetaG.detGrouped_ambient_at (T : StepTowerThetaG d L N κmin)
    {e : ℝ} (he : 0 < e) (het : e ≤ T.t)
    (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (hLN : L ∣ N₁) (hN5 : 5 < N₁) {ν : ℝ}
    (hν0 : 0 ≤ ν) (hν : ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1) (β p₁ : ℝ) :
    ∃ E : ∀ z : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))),
        DetExpansionLocC (T.step k hk N₁ ν β p₁) 1 z (2 * T.t)
          ((T.κ - Real.log 2 - 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) / (2 * d * L))
          ((L : ℝ) ^ d * ((1 / 2 : ℝ) * N * covBLogMax d L T.κ /
            (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp T.κ)))),
      (∀ z D T', (E z).term D T' = ∑ y ∈ (T.step k hk N₁ ν β p₁).blockU z,
          detActivityBg 1 (compWeight L 1) 1 ν (rho4 d L N T.BG T.κ) D y T') ∧
      (∀ z, renE0θ_det e E z (T.step k hk N₁ ν β p₁).D' 0 =
          -(1 / 2 : ℂ) * ∑ y ∈ (T.step k hk N₁ ν β p₁).blockU z, ∑ i : Fin N,
            (T.step k hk N₁ ν β p₁).logAC (y, i) (y, i)) ∧
      ∀ (z : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))))
        (X : Set (CTorus d L N₁ T.m₁ (k + 1))),
        ∃ F : RawData d L (N₁ * L ^ T.m₁) (k + 1) N × (Fin 3 → ℂ) → ℂ,
          AnalyticOnNhd ℂ F (expDom (T.step k hk N₁ ν β p₁).G'
            (XiCOneReal (T.step k hk N₁ ν β p₁).G'
              (T.step k hk N₁ ν β p₁).a (T.step k hk N₁ ν β p₁).ν e)
            T.r₀) ∧
          ∀ (D : BgData (T.step k hk N₁ ν β p₁).G' N),
            XiCOneReal (T.step k hk N₁ ν β p₁).G'
              (T.step k hk N₁ ν β p₁).a (T.step k hk N₁ ν β p₁).ν e D →
            (∀ ξ : Fin 3 → ℂ, ‖ξ‖ < T.r₀ →
              F ((D.Ψ, D.h), ξ) =
                (E z).detGrouped (renThetaDatum (T.step k hk N₁ ν β p₁) e D ξ) X ∧
              ‖F ((D.Ψ, D.h), ξ)‖ ≤ hullConst d L
                  ((T.κ - Real.log 2 - 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) / (2 * d * L))
                  ((L : ℝ) ^ d * ((1 / 2 : ℝ) * N * covBLogMax d L T.κ /
                    (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp T.κ)))) *
                Real.exp (-hullRate d L
                  ((T.κ - Real.log 2 - 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) / (2 * d * L)) *
                  sizeJ 1 (k + 1) X)) ∧
            F ((D.Ψ, D.h), 0) = (E z).detGrouped D X := by
  obtain ⟨hD0, hfam⟩ := T.detExpansion_scale k hk N₁ hLN hN5 hν0 hν β p₁
  choose E hE using hfam
  have hH := bgHyp_lvG (k := k) T.hd T.hL (bgR0_le_rhoSepG T.m₁ T.hd T.hL) hν0 hν
  obtain ⟨hM, hle0⟩ := T.thetaChartMargin_of_le he het
  have hN1 : L ^ 1 ∣ N₁ := by simpa using hLN
  have hrate := T.detRate_nonneg
  have hconst := T.detConst_nonneg
  have hle : e + xiK2 d L N * (3 / 2 * e * T.r₀) ≤ 2 * T.t := by linarith
  refine ⟨E, hE, fun z => renE0θ_det_zero e E z hD0, fun z X => ?_⟩
  obtain ⟨F, hFan, hFeq⟩ := exists_renDetGrouped_ambient_of_le (E z) hH e T.r₀ hM hle rfl X
  refine ⟨F, hFan, fun D hD => ⟨fun ξ hξ => ⟨hFeq D ξ hD hξ, ?_⟩, ?_⟩⟩
  · rw [hFeq D ξ hD hξ]
    exact (E z).detGrouped_bound T.hL hN1 hconst hrate
      (renE0_theta_domain_of_le _ hH e _ (2 * T.t) T.r₀ hM hle D hD ξ hξ) X
  · have := hFeq D 0 hD (by simpa using T.r₀_pos)
    rwa [renThetaDatum_zero] at this


/-- **The determinant part of `E0θ` on the renormalization domain, at the general tower.**  The
case `e = t` of `StepTowerThetaG.detGrouped_ambient_at`: at every scale there is a family `E z` of
determinant records at chart radius `2 t` with the term formula, and

* the value at `ξ = 0`: `renE0θ_det T.t E z S.D' 0` is the determinant term
  `-(1/2) ∑_y ∑_i log A_C(y, i)(y, i)` of the step;
* for every root `z` and hull `X` an ambient function `F`, analytic on the renormalization domain
  `expDom (XiCOneReal … T.t) T.r₀`, equal there to the regrouped determinant term at the
  renormalized datum, bounded there by `C_hull e^{-λ_hull sizeJ X}`, and equal at `ξ = 0` to the
  regrouped term at the datum itself. -/
theorem StepTowerThetaG.detGrouped_ambient (T : StepTowerThetaG d L N κmin)
    (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (hLN : L ∣ N₁) (hN5 : 5 < N₁) {ν : ℝ}
    (hν0 : 0 ≤ ν) (hν : ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1) (β p₁ : ℝ) :
    ∃ E : ∀ z : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))),
        DetExpansionLocC (T.step k hk N₁ ν β p₁) 1 z (2 * T.t)
          ((T.κ - Real.log 2 - 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) / (2 * d * L))
          ((L : ℝ) ^ d * ((1 / 2 : ℝ) * N * covBLogMax d L T.κ /
            (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp T.κ)))),
      (∀ z D T', (E z).term D T' = ∑ y ∈ (T.step k hk N₁ ν β p₁).blockU z,
          detActivityBg 1 (compWeight L 1) 1 ν (rho4 d L N T.BG T.κ) D y T') ∧
      (∀ z, renE0θ_det T.t E z (T.step k hk N₁ ν β p₁).D' 0 =
          -(1 / 2 : ℂ) * ∑ y ∈ (T.step k hk N₁ ν β p₁).blockU z, ∑ i : Fin N,
            (T.step k hk N₁ ν β p₁).logAC (y, i) (y, i)) ∧
      ∀ (z : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))))
        (X : Set (CTorus d L N₁ T.m₁ (k + 1))),
        ∃ F : RawData d L (N₁ * L ^ T.m₁) (k + 1) N × (Fin 3 → ℂ) → ℂ,
          AnalyticOnNhd ℂ F (expDom (T.step k hk N₁ ν β p₁).G'
            (XiCOneReal (T.step k hk N₁ ν β p₁).G'
              (T.step k hk N₁ ν β p₁).a (T.step k hk N₁ ν β p₁).ν T.t)
            T.r₀) ∧
          ∀ (D : BgData (T.step k hk N₁ ν β p₁).G' N),
            XiCOneReal (T.step k hk N₁ ν β p₁).G'
              (T.step k hk N₁ ν β p₁).a (T.step k hk N₁ ν β p₁).ν T.t D →
            (∀ ξ : Fin 3 → ℂ, ‖ξ‖ < T.r₀ →
              F ((D.Ψ, D.h), ξ) =
                (E z).detGrouped (renThetaDatum (T.step k hk N₁ ν β p₁) T.t D ξ) X ∧
              ‖F ((D.Ψ, D.h), ξ)‖ ≤ hullConst d L
                  ((T.κ - Real.log 2 - 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) / (2 * d * L))
                  ((L : ℝ) ^ d * ((1 / 2 : ℝ) * N * covBLogMax d L T.κ /
                    (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp T.κ)))) *
                Real.exp (-hullRate d L
                  ((T.κ - Real.log 2 - 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) / (2 * d * L)) *
                  sizeJ 1 (k + 1) X)) ∧
            F ((D.Ψ, D.h), 0) = (E z).detGrouped D X := by
  exact T.detGrouped_ambient_at T.t_pos le_rfl k hk N₁ hLN hN5 hν0 hν β p₁

end TowerFamilyG

end Balaban.Inhabited
