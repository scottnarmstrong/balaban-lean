/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.HatLabelsAct
public import Balaban.Fluctuation.InteractionLoc
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# From the ψ̂-local expansion to label activities (Theorem 3.4 input)

`HatTerms` is the conclusion of Proposition 3.3 in the variable `ψ̂`
(`Balaban.Localization.interaction_expansion_hat`) in the form needed to build label activities:
the localized expansion `LocInt` (terms local under `AgHatF`, bounded by `ε_U e^{-a d^cov(Y)}`)
together with the two properties of the terms that the existential statement of
`interaction_expansion_hat` does not export, namely that the labels `Y` are domains of
`𝒟_{k+1}` (`polymerDomains`, `isDj_of_isMultiDom`) and that the terms are measurable in `ψ̂`
(they are analytic).

`labelAct_of_hatTerms` turns it into a `LabelAct` on `CubeLabels` (the thickenings of the
domains), with the entropy bound (G2), the activity bound `ε_H e^{-κ_H 𝗱}` and the dependence on
the block variables of the cubes inside the label.
-/

@[expose] public section

namespace Balaban.Fluctuation

open MeasureTheory Balaban Balaban.Localization Balaban.Multiscale Balaban.Polymer

section Terms

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- The constant `A = 1 + 2^d c₁ c_G` of the size of the thickening: `𝗱(Z) ≤ A d(Y) + B`. -/
noncomputable def hatA (d L : ℕ) : ℝ := 1 + 2 ^ d * c1 d L * cG d L

/-- The constant `B = 2^d c₁ c_G`. -/
noncomputable def hatB (d L : ℕ) : ℝ := 2 ^ d * c1 d L * cG d L

/-- The prefactor `ε_H = R_σ ε_U e^{c₁ + a B / A}` of the label activities. -/
noncomputable def hatEpsH (d L : ℕ) (Rσ εU a : ℝ) : ℝ :=
  Rσ * εU * Real.exp (c1 d L + a * hatB d L / hatA d L)

/-- The rate `κ_H = a / A - c₁` of the label activities. -/
noncomputable def hatKappaH (d L : ℕ) (a : ℝ) : ℝ := a / hatA d L - c1 d L

theorem hatA_pos (d L : ℕ) [NeZero L] : 0 < hatA d L := by
  have : 0 ≤ cG d L := by unfold cG; positivity
  have : 0 ≤ c1 d L := by unfold c1; positivity
  unfold hatA; positivity

variable (S : StepSetting d L N₁ m₁ k N ϱ) (m₀ : ℕ) {Λ F' : Type}
  [NormedAddCommGroup Λ] [NormedSpace ℂ Λ]

/-- **Proposition 3.3 in the variable `ψ̂`, as label terms.**  The terms `T_Y` of the domains
`Y ∈ 𝒴` are local in `ψ̂` (`AgHatF`), bounded by `|σ| b_Y` with `b_Y ≤ ε_U e^{-a d^cov_{k+1}(Y)}`,
analytic in `(Θ, σ)` (`LocInt`), the domains are in `𝒟_{k+1}`, and the terms are measurable in
the hat variable on the disk `|ψ̂| ≤ ρ`.  `emb` is the embedding of the hat variable into the
ray space of the expansion. -/
structure HatTerms (emb : (S.U × Fin N → ℂ) → F') (ρ Rσ εU a : ℝ) (Θ₀ : Λ) (SΛ : Set Λ)
    (XW : Set (F' × F')) (val : F' → F' → ℂ → Λ → ℂ) (AgΘ : Set (CTorus d L N₁ m₁ (k + 1)) → Λ → Λ → Prop)
    (AgF : Set (CTorus d L N₁ m₁ (k + 1)) → F' → F' → Prop) where
  /-- the domains -/
  𝒴 : Finset (Set (CTorus d L N₁ m₁ (k + 1)))
  /-- the terms -/
  T : Set (CTorus d L N₁ m₁ (k + 1)) → F' → F' → ℂ → Λ → ℂ
  /-- the bounds -/
  b : Set (CTorus d L N₁ m₁ (k + 1)) → ℝ
  loc : LocInt SΛ XW Rσ 𝒴 T val b AgΘ AgF
  dom : ∀ Y ∈ 𝒴, IsDj m₀ (k + 1) Y
  bd : ∀ Y ∈ 𝒴, b Y ≤ εU * Real.exp (-a * treeLenCovOne m₀ (k + 1) Y)
  mem : Θ₀ ∈ SΛ
  agΘ : ∀ Y, AgΘ Y Θ₀ Θ₀
  xw : ∀ ψ ∈ hatDisk S.U N ρ, (emb ψ, emb ψ) ∈ XW
  ag : ∀ Y ψ ψ', AgHatF S.G' S.hG' Y ψ ψ' → AgF Y (emb ψ) (emb ψ')
  meas : ∀ Y ∈ 𝒴, ∀ σ : ℂ, ‖σ‖ < Rσ →
    Measurable (fun ψ : hatDisk S.U N ρ => T Y (emb ψ.1) (emb ψ.1) σ Θ₀)

open Classical in
/-- **Label activities from the ψ̂-local expansion.**  For `HatTerms` there are `CubeLabels`
(the thickenings of the domains, of size `d^cov_{k+1}`) and activities `H(Z; u, Φ)` of the block
variables `Φ` of `ν_{p₁}`, measurable, depending only on the cubes inside `Z`, bounded by
`ε_H e^{-κ_H 𝗱(Z)}`, with the entropy bound `∑_{Z ⊇ □} e^{-κ₀ 𝗱(Z)} ≤ K_c`; holomorphic in the
interpolation parameter `u` on `|u| < R_σ`; and summing to the expanded function at the hat
variable of `Φ`. -/
theorem labelAct_of_hatTerms {emb : (S.U × Fin N → ℂ) → F'} {ρ Rσ εU a : ℝ} {Θ₀ : Λ}
    {SΛ : Set Λ} {XW : Set (F' × F')} {val : F' → F' → ℂ → Λ → ℂ}
    {AgΘ : Set (CTorus d L N₁ m₁ (k + 1)) → Λ → Λ → Prop}
    {AgF : Set (CTorus d L N₁ m₁ (k + 1)) → F' → F' → Prop}
    (I : HatTerms S m₀ emb ρ Rσ εU a Θ₀ SΛ XW val AgΘ AgF)
    (hN : L ^ m₀ ∣ N₁) (hL : 2 ≤ L) (hp : 0 < S.p₁) (hρ : 0 < ρ) (hRσ : 0 ≤ Rσ)
    (hεU : 0 ≤ εU) (ha : 0 ≤ a) {κ0 Kc : ℝ} (hκ0 : aEnt d L + 1 ≤ κ0) (hKc : K0 d L κ0 ≤ Kc) :
    ∃ (Lb : Type) (_ : Fintype Lb)
      (Lab : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
        Set.univ Lb)
      (A : ℂ → LabelAct Lab (S.blockSplit m₀ hp).Ωb (hatEpsH d L Rσ εU a) (hatKappaH d L a) κ0 Kc),
      (∀ y Φ, DifferentiableOn ℂ (fun u => (A u).H y Φ) (Metric.ball 0 Rσ)) ∧
      (∀ u : ℂ, ‖u‖ < Rσ → ∀ Φ, ∑ y, (A u).H y Φ =
        val (emb (S.hatOf m₀ ρ hp Φ)) (emb (S.hatOf m₀ ρ hp Φ)) u Θ₀) := by
  obtain ⟨𝒴, T, b, loc, dom, bd, Θmem, agΘ, hxw, hag, hmeas⟩ := I
  -- the thickenings
  have hex : ∀ Y : Set (CTorus d L N₁ m₁ (k + 1)), ∃ Z, IsDj m₀ (k + 1) Y →
      (IsDj m₀ (k + 1) Z ∧ Y ⊆ Z ∧
        (∀ y ∈ psiThick Y, box (cbase (cellSide L m₀ m₁ (k + 1)) y) (cellSide L m₀ m₁ (k + 1)) ⊆ Z) ∧
        treeLenCovOne m₀ (k + 1) Z ≤ treeLenCovOne m₀ (k + 1) Y +
          2 ^ d * c1 d L * (1 + treeLenCovOne m₀ (k + 1) Y) * cG d L) := by
    intro Y
    by_cases h : IsDj m₀ (k + 1) Y
    · obtain ⟨Z, hZ⟩ := thick_spec hN le_rfl hL h
      exact ⟨Z, fun _ => hZ⟩
    · exact ⟨Y, fun h' => absurd h' h⟩
  choose Zf hZf using hex
  set 𝒵 := 𝒴.image Zf with h𝒵def
  have h𝒵 : ∀ Z ∈ 𝒵, IsDj m₀ (k + 1) Z := by
    intro Z hZ
    obtain ⟨Y, hY, rfl⟩ := Finset.mem_image.1 hZ
    exact (hZf Y (dom Y hY)).1
  have hA := hatA_pos d L
  have hΩ : IsPiUnion m₀ (k + 1) (Set.univ : Set (CTorus d L N₁ m₁ (k + 1))) :=
    fun z _ => ⟨cbase (cellSide L m₀ m₁ (k + 1)) z, aligned_cbase z,
      mem_box_cbase (cellSide_pos (L := L) m₀ m₁ (k + 1)) z, Set.subset_univ _⟩
  -- the activities
  let Hf : ℂ → {Z // Z ∈ 𝒵} → (∀ b, (S.blockSplit m₀ hp).Ωb b) → ℂ := fun u Z Φ =>
    if ‖u‖ < Rσ then ∑ Y ∈ 𝒴.filter (fun Y => Zf Y = Z.1),
      T Y (emb (S.hatOf m₀ ρ hp Φ)) (emb (S.hatOf m₀ ρ hp Φ)) u Θ₀ else 0
  have hHmeas : ∀ u Z, Measurable (Hf u Z) := by
    intro u Z
    by_cases hu : ‖u‖ < Rσ
    · simp only [Hf, hu, ite_true]
      refine Finset.measurable_sum _ fun Y hY => ?_
      exact (hmeas Y (Finset.mem_filter.1 hY).1 u hu).comp (S.measurable_hatOf m₀ ρ hρ hp)
    · simp only [Hf, hu, ite_false]
      exact measurable_const
  have hHdep : ∀ u (Z : {Z // Z ∈ 𝒵}), DepOn (blocksOf m₀ (k + 1) Set.univ Z.1) (Hf u Z) := by
    intro u Z Φ Φ' h
    by_cases hu : ‖u‖ < Rσ
    · simp only [Hf, hu, ite_true]
      refine Finset.sum_congr rfl fun Y hY => ?_
      obtain ⟨hY1, hY2⟩ := Finset.mem_filter.1 hY
      have hspec := hZf Y (dom Y hY1)
      have hAg : AgHatF S.G' S.hG' Y (S.hatOf m₀ ρ hp Φ) (S.hatOf m₀ ρ hp Φ') :=
        S.agHatF_hatOf m₀ hspec.2.2.1 ρ hp Φ Φ' (fun b hb => h b (hY2 ▸ hb))
      exact loc.loc Y hY1 (emb (S.hatOf m₀ ρ hp Φ), emb (S.hatOf m₀ ρ hp Φ))
        (hxw _ (S.hatOf_mem m₀ hρ hp Φ)) (emb (S.hatOf m₀ ρ hp Φ'), emb (S.hatOf m₀ ρ hp Φ'))
        (hxw _ (S.hatOf_mem m₀ hρ hp Φ')) u hu Θ₀ Θmem Θ₀ Θmem (agΘ Y) (hag Y _ _ hAg) (hag Y _ _ hAg)
    · simp [Hf, hu]
  have hHbound : ∀ u (Z : {Z // Z ∈ 𝒵}) Φ, ‖Hf u Z Φ‖ ≤ hatEpsH d L Rσ εU a *
      Real.exp (-hatKappaH d L a * treeLenCovOne m₀ (k + 1) Z.1) := by
    intro u Z Φ
    set tZ := treeLenCovOne m₀ (k + 1) Z.1 with htZ
    have hε0 : 0 ≤ hatEpsH d L Rσ εU a := by unfold hatEpsH; positivity
    by_cases hu : ‖u‖ < Rσ
    · simp only [Hf, hu, ite_true]
      have hZdj := h𝒵 Z.1 Z.2
      set C : ℝ := Rσ * εU * (Real.exp (a * hatB d L / hatA d L) *
        Real.exp (-(a / hatA d L) * tZ)) with hC
      have hC0 : 0 ≤ C := by rw [hC]; positivity
      have hterm : ∀ Y ∈ 𝒴.filter (fun Y => Zf Y = Z.1),
          ‖T Y (emb (S.hatOf m₀ ρ hp Φ)) (emb (S.hatOf m₀ ρ hp Φ)) u Θ₀‖ ≤ C := by
        intro Y hY
        obtain ⟨hY1, hY2⟩ := Finset.mem_filter.1 hY
        have h1 := loc.bound Y hY1 (emb (S.hatOf m₀ ρ hp Φ), emb (S.hatOf m₀ ρ hp Φ))
          (hxw _ (S.hatOf_mem m₀ hρ hp Φ)) u hu Θ₀ Θmem
        have hspec := hZf Y (dom Y hY1)
        have h2 : tZ ≤ hatA d L * treeLenCovOne m₀ (k + 1) Y + hatB d L := by
          rw [htZ, ← hY2]
          have := hspec.2.2.2
          unfold hatA hatB
          nlinarith
        have h3 := hat_exp_bound hA ha h2
        have h4 : ‖u‖ * b Y ≤ ‖u‖ * (εU * Real.exp (-a * treeLenCovOne m₀ (k + 1) Y)) :=
          mul_le_mul_of_nonneg_left (bd Y hY1) (norm_nonneg u)
        have h5 : ‖u‖ * (εU * Real.exp (-a * treeLenCovOne m₀ (k + 1) Y)) ≤
            Rσ * (εU * Real.exp (-a * treeLenCovOne m₀ (k + 1) Y)) :=
          mul_le_mul_of_nonneg_right hu.le (by positivity)
        have h6 : Rσ * (εU * Real.exp (-a * treeLenCovOne m₀ (k + 1) Y)) ≤ C := by
          rw [hC]
          calc Rσ * (εU * Real.exp (-a * treeLenCovOne m₀ (k + 1) Y))
              ≤ Rσ * (εU * (Real.exp (a * hatB d L / hatA d L) *
                  Real.exp (-(a / hatA d L) * tZ))) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 hεU) hRσ
            _ = _ := by ring
        exact h1.trans (h4.trans (h5.trans h6))
      calc ‖∑ Y ∈ 𝒴.filter (fun Y => Zf Y = Z.1),
            T Y (emb (S.hatOf m₀ ρ hp Φ)) (emb (S.hatOf m₀ ρ hp Φ)) u Θ₀‖
          ≤ ∑ Y ∈ 𝒴.filter (fun Y => Zf Y = Z.1),
            ‖T Y (emb (S.hatOf m₀ ρ hp Φ)) (emb (S.hatOf m₀ ρ hp Φ)) u Θ₀‖ := norm_sum_le _ _
        _ ≤ ∑ Y ∈ 𝒴.filter (fun Y => Zf Y = Z.1), C := Finset.sum_le_sum hterm
        _ = ((𝒴.filter (fun Y => Zf Y = Z.1)).card : ℝ) * C := by simp
        _ ≤ Real.exp (c1 d L * (1 + tZ)) * C := by
            refine mul_le_mul_of_nonneg_right ?_ hC0
            exact card_fiber_thick hN le_rfl 𝒴 dom Zf (fun Y hY => (hZf Y (dom Y hY)).2.1) hZdj
        _ = _ := by
            rw [hC]
            unfold hatEpsH hatKappaH
            have : Real.exp (c1 d L * (1 + tZ)) * (Real.exp (a * hatB d L / hatA d L) *
                Real.exp (-(a / hatA d L) * tZ)) =
                Real.exp (c1 d L + a * hatB d L / hatA d L) *
                  Real.exp (-(a / hatA d L - c1 d L) * tZ) := by
              rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
            calc Real.exp (c1 d L * (1 + tZ)) * (Rσ * εU * (Real.exp (a * hatB d L / hatA d L) *
                  Real.exp (-(a / hatA d L) * tZ)))
                = Rσ * εU * (Real.exp (c1 d L * (1 + tZ)) * (Real.exp (a * hatB d L / hatA d L) *
                  Real.exp (-(a / hatA d L) * tZ))) := by ring
              _ = _ := by rw [this]; ring
    · simp only [Hf, hu, ite_false, norm_zero]
      positivity
  have hHent : ∀ b : CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1) Set.univ,
      ∑ Z : {Z // Z ∈ 𝒵}, (if box b.1 (cellSide L m₀ m₁ (k + 1)) ⊆ Z.1 then
        Real.exp (-κ0 * treeLenCovOne m₀ (k + 1) Z.1) else 0) ≤ Kc :=
    fun b => (entropy_thick hN le_rfl 𝒵 h𝒵 hκ0 b).trans hKc
  have hhol : ∀ (Z : {Z // Z ∈ 𝒵}) Φ, DifferentiableOn ℂ (fun u => Hf u Z Φ) (Metric.ball 0 Rσ) := by
    intro Z Φ
    have hd : DifferentiableOn ℂ (fun u => ∑ Y ∈ 𝒴.filter (fun Y => Zf Y = Z.1),
        T Y (emb (S.hatOf m₀ ρ hp Φ)) (emb (S.hatOf m₀ ρ hp Φ)) u Θ₀) (Metric.ball 0 Rσ) := by
      refine DifferentiableOn.fun_sum (𝕜 := ℂ) (A := fun Y (u : ℂ) => T Y (emb (S.hatOf m₀ ρ hp Φ))
        (emb (S.hatOf m₀ ρ hp Φ)) u Θ₀) fun Y hY => ?_
      have han : AnalyticOnNhd ℂ (fun p : Λ × ℂ => T Y (emb (S.hatOf m₀ ρ hp Φ))
          (emb (S.hatOf m₀ ρ hp Φ)) p.2 p.1) (SΛ ×ˢ Metric.ball (0 : ℂ) Rσ) :=
        loc.analytic Y (Finset.mem_filter.1 hY).1
          (emb (S.hatOf m₀ ρ hp Φ), emb (S.hatOf m₀ ρ hp Φ)) (hxw _ (S.hatOf_mem m₀ hρ hp Φ))
      have hc : AnalyticOnNhd ℂ (fun u : ℂ => ((Θ₀, u) : Λ × ℂ)) (Metric.ball 0 Rσ) :=
        AnalyticOnNhd.prod (analyticOnNhd_const : AnalyticOnNhd ℂ (fun _ : ℂ => Θ₀) (Metric.ball 0 Rσ))
          (analyticOnNhd_id : AnalyticOnNhd ℂ (fun u : ℂ => u) (Metric.ball 0 Rσ))
      exact (han.comp hc (fun u hu => ⟨Θmem, hu⟩)).differentiableOn
    refine hd.congr fun u hu => ?_
    have hu' : ‖u‖ < Rσ := by simpa using hu
    simp [Hf, hu']
  have hsum : ∀ u : ℂ, ‖u‖ < Rσ → ∀ Φ, ∑ Z : {Z // Z ∈ 𝒵}, Hf u Z Φ =
      val (emb (S.hatOf m₀ ρ hp Φ)) (emb (S.hatOf m₀ ρ hp Φ)) u Θ₀ := by
    intro u hu Φ
    simp only [Hf, hu, ite_true]
    rw [Finset.sum_coe_sort 𝒵 (fun Z => ∑ Y ∈ 𝒴.filter (fun Y => Zf Y = Z),
      T Y (emb (S.hatOf m₀ ρ hp Φ)) (emb (S.hatOf m₀ ρ hp Φ)) u Θ₀),
      Finset.sum_fiberwise_of_maps_to (fun Y hY => Finset.mem_image_of_mem Zf hY)]
    exact (loc.sum (emb (S.hatOf m₀ ρ hp Φ), emb (S.hatOf m₀ ρ hp Φ))
      (hxw _ (S.hatOf_mem m₀ hρ hp Φ)) u hu Θ₀ Θmem).symm
  exact ⟨{Z // Z ∈ 𝒵}, inferInstance, thickLabels 𝒵 h𝒵,
    fun u => ⟨Hf u, hHmeas u, hHdep u, fun Z Φ => hHbound u Z Φ, hHent⟩, hhol, hsum⟩

theorem ae_norm_lt_fluctMeasure1 (N : ℕ) (p : ℝ) :
    ∀ᵐ x ∂fluctMeasure1 N p, ‖x‖ < p := by
  rw [ae_iff]
  have hs : MeasurableSet {x : Rn N | ¬ ‖x‖ < p} :=
    (measurableSet_lt measurable_norm measurable_const).compl
  unfold fluctMeasure1
  rw [Measure.smul_apply, withDensity_apply _ hs]
  have : ∫⁻ x in {x : Rn N | ¬ ‖x‖ < p}, ENNReal.ofReal (fluctDensity N p x) = 0 := by
    rw [setLIntegral_congr_fun hs (g := fun _ => 0) (fun x hx => by
      have : ¬ ‖x‖ < p := hx
      simp [fluctDensity, this])]
    simp
  rw [this]; simp

/-- **The fluctuation variable lies in the disk `|ψ̂(u)| < p₁` `ν_{p₁}`-almost surely.** -/
theorem StepSetting.ae_norm_nuFl (hp : 0 < S.p₁) :
    ∀ᵐ x ∂S.nuFl, ∀ u, ‖x u‖ < S.p₁ := by
  have := isProbabilityMeasure_fluctMeasure1 N hp
  rw [ae_all_iff]
  intro u
  exact (measurePreserving_eval (fun _ : S.U => fluctMeasure1 N S.p₁) u).quasiMeasurePreserving.ae
    (ae_norm_lt_fluctMeasure1 N S.p₁)

/-- **The sum identity, almost surely**: on the support of `ν_{p₁}` (for `p₁ ≤ ρ`) the hat variable
of the block variables of `x` is the complexification of `x`. -/
theorem StepSetting.ae_hatOf_restr {ρ : ℝ} (hρ : 0 < ρ) (hp : 0 < S.p₁) (hpρ : S.p₁ ≤ ρ) :
    ∀ᵐ x ∂S.nuFl, S.hatOf m₀ ρ hp ((S.blockSplit m₀ hp).restr x) = S.hatC x := by
  filter_upwards [S.ae_norm_nuFl hp] with x hx
  exact S.hatOf_restr m₀ hρ hp x fun u => ((hx u).trans_le hpρ).le

/-- **`HatTerms` is inhabited** (no domains, zero expanded function): for every step and all
parameters. -/
theorem nonempty_hatTerms (ρ Rσ εU a : ℝ) :
    Nonempty (HatTerms S m₀ (F' := Unit) (fun _ => ()) ρ Rσ εU a (0 : ℂ) Set.univ Set.univ
      (fun _ _ _ _ => (0 : ℂ)) (fun _ _ _ => True) (fun _ _ _ => True)) :=
  ⟨{ 𝒴 := ∅
     T := fun _ _ _ _ _ => 0
     b := fun _ => 0
     loc := ⟨by simp, fun Y hY => absurd hY (Finset.notMem_empty Y),
       fun Y hY => absurd hY (Finset.notMem_empty Y), fun Y hY => absurd hY (Finset.notMem_empty Y),
       fun Y hY => absurd hY (Finset.notMem_empty Y)⟩
     dom := fun Y hY => absurd hY (Finset.notMem_empty Y)
     bd := fun Y hY => absurd hY (Finset.notMem_empty Y)
     mem := Set.mem_univ _
     agΘ := fun _ => trivial
     xw := fun _ _ => Set.mem_univ _
     ag := fun _ _ _ _ => trivial
     meas := fun Y hY => absurd hY (Finset.notMem_empty Y) }⟩

end Terms

end Balaban.Fluctuation
