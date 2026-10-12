/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.HatLabelsTerms
public import Balaban.Fluctuation.Thm31Inhab
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Label activities with direct labels (`TRUE-LOCAL.md` §4)

The labels are the domains `Y ∈ 𝒴` themselves (`thickLabels 𝒴`, each fibre a singleton), so
the label sum is the term sum and the rate is unchanged.

Where the landed conversion `labelAct_of_hatTerms` loses: (1) `AgHatF Y` involves the block
thickening `blockThick Y ⊄ Y`, so the activity of `Y` depends on the blocks of a thickening `Z`
with `Z ⊇ psiThick Y` and `d^cov(Z) ≤ hatA · d^cov(Y) + hatB` (`hat_exp_bound`); this is the only
source of `hatA` and `hatB`; (2) several `Y` share a thickening, the fibre has `≤ e^{c₁(1+𝗱(Z))}`
elements (`card_fiber_thick`), which gives the `- c₁` in `hatKappaH` and the factor
`e^{c₁}` in `hatEpsH`.  With identity labels neither occurs: the bound is
`‖H(Y)‖ ≤ R_σ ε_U e^{-a 𝗱(Y)}`, i.e. `ε_H = R_σ ε_U`, `κ_H = a`.  The constant `c₁` survives only
inside the entropy constant `K₀ d L κ₀` of `entropy_thick` (`κ₀ ≥ a_Ent + 1`), unchanged.

`DirectTerms` differs from `HatTerms` in one field, `ag`: agreement of the block variables on
`blocksOf Y` (the blocks inside `Y`) implies the agreement `AgF Y` of the expansion variables.
**This field is the open physical locality theorem (OPEN-PHYSICAL-FOOTPRINT-LOCAL of
`notes/phase1/TRUE-LOCAL.md`).**  The physical terms are not yet shown to satisfy it; no landed
declaration produces a `DirectTerms` for the physical expansion.
-/

@[expose] public section

namespace Balaban.Fluctuation

open MeasureTheory Balaban Balaban.Localization Balaban.Multiscale Balaban.Polymer

section DirectTerms

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

variable (S : StepSetting d L N₁ m₁ k N ϱ) (m₀ : ℕ) {Λ F' : Type}
  [NormedAddCommGroup Λ] [NormedSpace ℂ Λ]

/-- **The direct-label input.**  As `HatTerms`, except for the field `ag` (the open input):
two block configurations that agree on the blocks inside `Y` have hat variables that agree in the
sense `AgF Y` of the localization of the terms of `Y`. -/
structure DirectTerms (hp : 0 < S.p₁) (emb : (S.U × Fin N → ℂ) → F') (ρ Rσ εU a : ℝ) (Θ₀ : Λ)
    (SΛ : Set Λ) (XW : Set (F' × F')) (val : F' → F' → ℂ → Λ → ℂ)
    (AgΘ : Set (CTorus d L N₁ m₁ (k + 1)) → Λ → Λ → Prop)
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
  /-- **open input (OPEN-PHYSICAL-FOOTPRINT-LOCAL)**: sharp locality on the blocks of `Y` -/
  ag : ∀ Y ∈ 𝒴, ∀ Φ Φ' : (∀ b, (S.blockSplit m₀ hp).Ωb b),
    (∀ b ∈ blocksOf m₀ (k + 1) Set.univ Y, Φ b = Φ' b) →
      AgF Y (emb (S.hatOf m₀ ρ hp Φ)) (emb (S.hatOf m₀ ρ hp Φ'))
  meas : ∀ Y ∈ 𝒴, ∀ σ : ℂ, ‖σ‖ < Rσ →
    Measurable (fun ψ : hatDisk S.U N ρ => T Y (emb ψ.1) (emb ψ.1) σ Θ₀)

open Classical in
/-- **Label activities with direct labels.**  The labels are the domains of `𝒴` (`thickLabels`),
the activity of `Y` is `T_Y` at the hat variable of `Φ`, bounded by `(R_σ ε_U) e^{-a 𝗱(Y)}`
(rate `κ_H = a`, prefactor `ε_H = R_σ ε_U`), entropy bound `K_c ≥ K₀`; holomorphic in `u` and
summing to the expanded function.  Compare `labelAct_of_hatTerms` (rate `a/hatA - c₁`). -/
theorem labelAct_of_directTerms {hp : 0 < S.p₁} {emb : (S.U × Fin N → ℂ) → F'}
    {ρ Rσ εU a : ℝ} {Θ₀ : Λ}
    {SΛ : Set Λ} {XW : Set (F' × F')} {val : F' → F' → ℂ → Λ → ℂ}
    {AgΘ : Set (CTorus d L N₁ m₁ (k + 1)) → Λ → Λ → Prop}
    {AgF : Set (CTorus d L N₁ m₁ (k + 1)) → F' → F' → Prop}
    (I : DirectTerms S m₀ hp emb ρ Rσ εU a Θ₀ SΛ XW val AgΘ AgF)
    (hN : L ^ m₀ ∣ N₁) (hρ : 0 < ρ) (hRσ : 0 ≤ Rσ) (hεU : 0 ≤ εU)
    {κ0 Kc : ℝ} (hκ0 : aEnt d L + 1 ≤ κ0) (hKc : K0 d L κ0 ≤ Kc) :
    ∃ A : ℂ → LabelAct (thickLabels I.𝒴 I.dom) (S.blockSplit m₀ hp).Ωb (Rσ * εU) a κ0 Kc,
      (∀ y Φ, DifferentiableOn ℂ (fun u => (A u).H y Φ) (Metric.ball 0 Rσ)) ∧
      (∀ u : ℂ, ‖u‖ < Rσ → ∀ Φ, ∑ y, (A u).H y Φ =
        val (emb (S.hatOf m₀ ρ hp Φ)) (emb (S.hatOf m₀ ρ hp Φ)) u Θ₀) := by
  obtain ⟨𝒴, T, b, loc, dom, bd, Θmem, agΘ, hxw, hag, hmeas⟩ := I
  let Hf : ℂ → {Y // Y ∈ 𝒴} → (∀ b, (S.blockSplit m₀ hp).Ωb b) → ℂ := fun u Y Φ =>
    if ‖u‖ < Rσ then T Y.1 (emb (S.hatOf m₀ ρ hp Φ)) (emb (S.hatOf m₀ ρ hp Φ)) u Θ₀ else 0
  have hHmeas : ∀ u Y, Measurable (Hf u Y) := by
    intro u Y
    by_cases hu : ‖u‖ < Rσ
    · simp only [Hf, hu, ite_true]
      exact (hmeas Y.1 Y.2 u hu).comp (S.measurable_hatOf m₀ ρ hρ hp)
    · simp only [Hf, hu, ite_false]
      exact measurable_const
  have hHdep : ∀ u (Y : {Y // Y ∈ 𝒴}), DepOn (blocksOf m₀ (k + 1) Set.univ Y.1) (Hf u Y) := by
    intro u Y Φ Φ' h
    by_cases hu : ‖u‖ < Rσ
    · simp only [Hf, hu, ite_true]
      have hAg := hag Y.1 Y.2 Φ Φ' h
      exact loc.loc Y.1 Y.2 (emb (S.hatOf m₀ ρ hp Φ), emb (S.hatOf m₀ ρ hp Φ))
        (hxw _ (S.hatOf_mem m₀ hρ hp Φ)) (emb (S.hatOf m₀ ρ hp Φ'), emb (S.hatOf m₀ ρ hp Φ'))
        (hxw _ (S.hatOf_mem m₀ hρ hp Φ')) u hu Θ₀ Θmem Θ₀ Θmem (agΘ Y.1) hAg hAg
    · simp [Hf, hu]
  have hHbound : ∀ u (Y : {Y // Y ∈ 𝒴}) Φ, ‖Hf u Y Φ‖ ≤ Rσ * εU *
      Real.exp (-a * treeLenCovOne m₀ (k + 1) Y.1) := by
    intro u Y Φ
    by_cases hu : ‖u‖ < Rσ
    · simp only [Hf, hu, ite_true]
      have h1 := loc.bound Y.1 Y.2 (emb (S.hatOf m₀ ρ hp Φ), emb (S.hatOf m₀ ρ hp Φ))
        (hxw _ (S.hatOf_mem m₀ hρ hp Φ)) u hu Θ₀ Θmem
      have h4 : ‖u‖ * b Y.1 ≤ ‖u‖ * (εU * Real.exp (-a * treeLenCovOne m₀ (k + 1) Y.1)) :=
        mul_le_mul_of_nonneg_left (bd Y.1 Y.2) (norm_nonneg u)
      have h5 : ‖u‖ * (εU * Real.exp (-a * treeLenCovOne m₀ (k + 1) Y.1)) ≤
          Rσ * (εU * Real.exp (-a * treeLenCovOne m₀ (k + 1) Y.1)) :=
        mul_le_mul_of_nonneg_right hu.le (by positivity)
      calc _ ≤ _ := h1.trans (h4.trans h5)
        _ = _ := by ring
    · simp only [Hf, hu, ite_false, norm_zero]
      positivity
  have hHent : ∀ b : CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1) Set.univ,
      ∑ Y : {Y // Y ∈ 𝒴}, (if box b.1 (cellSide L m₀ m₁ (k + 1)) ⊆ Y.1 then
        Real.exp (-κ0 * treeLenCovOne m₀ (k + 1) Y.1) else 0) ≤ Kc :=
    fun b => (entropy_thick hN le_rfl 𝒴 dom hκ0 b).trans hKc
  have hhol : ∀ (Y : {Y // Y ∈ 𝒴}) Φ, DifferentiableOn ℂ (fun u => Hf u Y Φ)
      (Metric.ball 0 Rσ) := by
    intro Y Φ
    have han : AnalyticOnNhd ℂ (fun p : Λ × ℂ => T Y.1 (emb (S.hatOf m₀ ρ hp Φ))
        (emb (S.hatOf m₀ ρ hp Φ)) p.2 p.1) (SΛ ×ˢ Metric.ball (0 : ℂ) Rσ) :=
      loc.analytic Y.1 Y.2 (emb (S.hatOf m₀ ρ hp Φ), emb (S.hatOf m₀ ρ hp Φ))
        (hxw _ (S.hatOf_mem m₀ hρ hp Φ))
    have hc : AnalyticOnNhd ℂ (fun u : ℂ => ((Θ₀, u) : Λ × ℂ)) (Metric.ball 0 Rσ) :=
      AnalyticOnNhd.prod (analyticOnNhd_const : AnalyticOnNhd ℂ (fun _ : ℂ => Θ₀)
        (Metric.ball 0 Rσ)) (analyticOnNhd_id : AnalyticOnNhd ℂ (fun u : ℂ => u) (Metric.ball 0 Rσ))
    have hd := (han.comp hc (fun u hu => ⟨Θmem, hu⟩)).differentiableOn
    refine hd.congr fun u hu => ?_
    have hu' : ‖u‖ < Rσ := by simpa using hu
    simp [Hf, hu']
  have hsum : ∀ u : ℂ, ‖u‖ < Rσ → ∀ Φ, ∑ Y : {Y // Y ∈ 𝒴}, Hf u Y Φ =
      val (emb (S.hatOf m₀ ρ hp Φ)) (emb (S.hatOf m₀ ρ hp Φ)) u Θ₀ := by
    intro u hu Φ
    simp only [Hf, hu, ite_true]
    rw [Finset.sum_coe_sort 𝒴 (fun Y => T Y (emb (S.hatOf m₀ ρ hp Φ))
      (emb (S.hatOf m₀ ρ hp Φ)) u Θ₀)]
    exact (loc.sum (emb (S.hatOf m₀ ρ hp Φ), emb (S.hatOf m₀ ρ hp Φ))
      (hxw _ (S.hatOf_mem m₀ hρ hp Φ)) u hu Θ₀ Θmem).symm
  exact ⟨fun u => ⟨Hf u, hHmeas u, hHdep u, fun Y Φ => hHbound u Y Φ, hHent⟩, hhol, hsum⟩

/-- **`DirectTerms` is inhabited with a nonempty family**: `𝒴 = {univ}` (the whole torus is a
domain), with zero terms and zero expanded function, for every step and every `εU ≥ 0`. -/
theorem nonempty_directTerms (hp : 0 < S.p₁) (ρ Rσ εU a : ℝ) (hεU : 0 ≤ εU) :
    ∃ I : DirectTerms S m₀ hp (F' := Unit) (fun _ => ()) ρ Rσ εU a (0 : ℂ) Set.univ Set.univ
      (fun _ _ _ _ => (0 : ℂ)) (fun _ _ _ => True) (fun _ _ _ => True), I.𝒴.Nonempty := by
  have hY : IsDj m₀ (k + 1) (Set.univ : Set (CTorus d L N₁ m₁ (k + 1))) :=
    isDj_univ d L N₁ m₁ (k + 1) m₀ (k + 1)
  refine ⟨{ 𝒴 := {Set.univ}
            T := fun _ _ _ _ _ => 0
            b := fun _ => 0
            loc := ⟨by simp, fun Y _ _ _ => analyticOnNhd_const, by simp, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl,
              fun _ _ _ _ _ _ => rfl⟩
            dom := fun Y hy => by rw [Finset.mem_singleton.1 hy]; exact hY
            bd := fun _ _ => by positivity
            mem := Set.mem_univ _
            agΘ := fun _ => trivial
            xw := fun _ _ => Set.mem_univ _
            ag := fun _ _ _ _ _ => trivial
            meas := fun _ _ _ _ => measurable_const }, ⟨Set.univ, Finset.mem_singleton_self _⟩⟩

end DirectTerms

end Balaban.Fluctuation
