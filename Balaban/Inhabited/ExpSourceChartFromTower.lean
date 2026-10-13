/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepTowerOfG
public import Balaban.Inhabited.StepTowerScale
public import Balaban.Fluctuation.ExpSourceChart
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The chart identity of the exponentiated source at every scale of a fixed tower

`expSourceChart_scale_fromTower` restates `expSourceChart_scale` for one tower
`T : StepTower κmin` and its per-scale package `D : StepScaleData T …`: the landed proof is re-run
with its tower prologue replaced by the fields of `T` and `D`.  `expSourceChart_scale_of_fromTower`
re-derives the landed statement from it.

Source activity with common labels and the chart/determinant joint endpoint are not in this file.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep Filter Topology

open Classical in
/-- **The chart identity of the exponentiated source at every scale of the tower `T`.**  The
conclusion of `expSourceChart_scale` at the step `T.step k hk N₁ ν β p₁`, the radius `T.t`, and the
constants `T.BG₂`, `T.κ`. -/
theorem expSourceChart_scale_fromTower {κmin : ℝ} (T : StepTower κmin)
    (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁]
    (ν : ℝ) (hνpos : 0 < ν) (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) (β p₁ : ℝ) (hp0 : 0 < p₁)
    (D : StepScaleData T k hk N₁ ν β p₁) :
    ∃ Jr : (T.step k hk N₁ ν β p₁).JointRep T.t (2 * p₁),
    ∃ val : ((((T.step k hk N₁ ν β p₁).U × Fin 2 → ℂ) ×
          ((T.step k hk N₁ ν β p₁).U × Fin 2 → ℂ))) →
        (((T.step k hk N₁ ν β p₁).U × Fin 2 → ℂ) × ((T.step k hk N₁ ν β p₁).U × Fin 2 → ℂ)) →
          ℂ → (RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 ×
            (CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) → ℂ,
      (∀ x w σ Θ, val x w σ Θ =
        (-((T.step k hk N₁ ν β p₁).β : ℂ)) * raySrc3
          (hatFun (T.step k hk N₁ ν β p₁).G' (T.step k hk N₁ ν β p₁).a₁
            (T.step k hk N₁ ν β p₁).ν T.t (T.step k hk N₁ ν β p₁).hG'
            (((T.step k hk N₁ ν β p₁).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
            (interactionOne (T.step k hk N₁ ν β p₁).hG (T.step k hk N₁ ν β p₁).hG'
              (le_refl (k + 1)) (T.step k hk N₁ ν β p₁).a₁ (T.step k hk N₁ ν β p₁).ν T.t))
          taylorWeight x.1 w.1 σ Θ.1 +
        ((T.step k hk N₁ ν β p₁).β : ℂ) * (∑ s : CTorus 3 3 N₁ T.m₁ (k + 1) × Fin 2,
          Θ.2 s.1 s.2 *
          dirTermSrc (hatFun (T.step k hk N₁ ν β p₁).G' (T.step k hk N₁ ν β p₁).a₁
            (T.step k hk N₁ ν β p₁).ν T.t (T.step k hk N₁ ν β p₁).hG'
            (((T.step k hk N₁ ν β p₁).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
            (onXi (T.step k hk N₁ ν β p₁).G' (T.step k hk N₁ ν β p₁).a₁
              (T.step k hk N₁ ν β p₁).ν T.t
              (fun D' ψ' => svec (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁))
                (flFieldOne (T.step k hk N₁ ν β p₁).G' (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁))
                  T.BG₂ T.κ (T.step k hk N₁ ν β p₁).a₁ (T.step k hk N₁ ν β p₁).ν D' ψ')
                s.1 s.2)))
            (fun _ => (1 : ℂ)) x.2 w.2 σ Θ.1)) ∧
      ∀ (g : Fld 3 3 N₁ T.m₁ (k + 1) 2) (x : (T.step k hk N₁ ν β p₁).EC),
        (∀ r : ℝ, r ∈ Set.Icc (0 : ℝ) 1 → ∀ q, ‖((r : ℂ) • x) q‖ ≤ 2 * p₁) →
        ∀ τ : ℝ, τ ∈ Set.Icc (0 : ℝ) 1 →
          Jr.W2 (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) g
              (rawOf (T.step k hk N₁ ν β p₁).D', (τ : ℂ) • x) =
            val (x, x) (x, x) (τ : ℂ)
                (rawOf (T.step k hk N₁ ν β p₁).D',
                  fun y i => g y i / ((T.step k hk N₁ ν β p₁).β : ℂ)) -
              val (x, x) (x, x) (τ : ℂ) (rawOf (T.step k hk N₁ ν β p₁).D', 0) := by
  classical
  have h4 := T.m₁_four
  have ht0 := T.t_pos
  have hν0 : 0 ≤ ν := hνpos.le

  have hMX := T.large_block
  have hdm := T.dom_margin
  have hα := T.coer_margin
  have hsmX := T.δc_small
  have hc7 := T.c7_cap
  have g1 := T.t_cap
  have g2 := T.bg0_cap
  have g3 := T.cK2_cap
  have g4 := T.cK2'_cap
  have g5 := T.bg1_cap
  have hcψ0 := D.cψ_pos
  have hr0 := D.r_pos
  have hδ₁ := D.fl_radius
  obtain ⟨R0⟩ := D.ray
  have hHB := bgHyp_lv (k := k) T.m₁ hν0 hν
  have hC := D.core
  have hD := D.xi
  have hβ0 : 0 < β := by
    by_contra hb
    replace hb := not_lt.mp hb
    have hb' : β * 3 ^ k ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hb (by positivity)
    have : lvCpsi T.κ T.t (β * 3 ^ k) = 0 := by
      unfold lvCpsi
      rw [Real.sqrt_eq_zero_of_nonpos hb']; simp
    linarith
  have hmem := compWeight_three_mem hk
  have hCs : 0 ≤ covSupConstC 3 3 2 (compWeight 3 (1 : ℝ) k) T.κ :=
    covSupConstC_nonneg (by norm_num) (by norm_num) (by linarith [hmem.1]) T.κ
  have hpc : 2 * p₁ < lvCpsi T.κ T.t (β * 3 ^ k) := by
    have : 0 < lvR T.κ T.t (β * 3 ^ k) p₁ * p₁ := mul_pos hr0 hp0
    nlinarith [D.ray_margin]
  have hbU : 0 ≤ (T.step k hk N₁ ν β p₁).betaU := R0.betaU_pos.le
  have hδp : Real.sqrt ((2 : ℕ) : ℝ) *
      ((T.step k hk N₁ ν β p₁).betaU ^ (-(1 / 2 : ℝ)) *
        (covSupConstC 3 3 2 (compWeight 3 (1 : ℝ) k) T.κ * (2 * p₁))) < T.t := by
    refine lt_of_le_of_lt ?_ hδ₁
    rw [(T.step k hk N₁ ν β p₁).norm_betaU_rpow (show 0 ≤ β by linarith)]
    have hb := Real.rpow_nonneg hbU (-(1 / 2 : ℝ))
    have hs := Real.sqrt_nonneg ((2 : ℕ) : ℝ)
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hpc.le hCs) hb) hs
  obtain ⟨Jr⟩ := (T.step k hk N₁ ν β p₁).nonempty_jointRep (pp := 2 * p₁)
    hC hMX hdm hα hsmX one_pos hc7 (R := 2) (by norm_num) g5 (by
      show 0 ≤ β
      linarith) (by linarith) hδp
  refine ⟨Jr, _, fun x w σ Θ => rfl, ?_⟩
  intro g x hx τ hτ
  refine Jr.W2_eq_val_sub hC one_pos hHB hc7 (R := 2) le_rfl g5 g1 g2 g3 g4 hMX hdm hα hsmX
    hcψ0.le hδ₁ hpc hD g ?_ x hx hτ _ (fun x w σ Θ => rfl)
  have : (T.step k hk N₁ ν β p₁).β ≠ 0 := by
    show β ≠ 0
    exact hβ0.ne'
  exact_mod_cast this

open Classical in
/-- **Check.**  The landed `expSourceChart_scale`, re-derived from
`expSourceChart_scale_fromTower`, `exists_stepTower` and `StepTower.scale`. -/
theorem expSourceChart_scale_of_fromTower {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ) :
    ∃ (m₁ : ℕ) (t δ β₀ BG₂ κ : ℝ), 2 ≤ β₀ ∧ 0 < t ∧ 0 < δ ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁], 3 ∣ N₁ → 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
      ∀ p₁ : ℝ, 0 < p₁ → p₁ ≤ pLog A₁ p (β * 3 ^ k) →
      ∀ S : StepSetting 3 3 N₁ m₁ k 2 (rhoSep m₁),
        S = hatStepK (N₁ := N₁) k m₁ hk ν β p₁ δ →
      ∃ Jr : S.JointRep t (2 * p₁),
      ∃ val : ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) → ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) →
            ℂ → (RawData 3 3 (N₁ * 3 ^ m₁) (k + 1) 2 × (CTorus 3 3 N₁ m₁ (k + 1) → Fin 2 → ℂ)) → ℂ,
        (∀ x w σ Θ, val x w σ Θ =
          (-(S.β : ℂ)) * raySrc3 (hatFun S.G' S.a₁ S.ν t S.hG'
            ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
            (interactionOne S.hG S.hG' (le_refl (k + 1)) S.a₁ S.ν t)) taylorWeight x.1 w.1 σ Θ.1 +
          (S.β : ℂ) * (∑ s : CTorus 3 3 N₁ m₁ (k + 1) × Fin 2, Θ.2 s.1 s.2 *
            dirTermSrc (hatFun S.G' S.a₁ S.ν t S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
              (onXi S.G' S.a₁ S.ν t
                (fun D ψ' => svec (stepG 3 3 N₁ m₁ k (rhoSep m₁))
                  (flFieldOne S.G' (stepG 3 3 N₁ m₁ k (rhoSep m₁)) BG₂ κ S.a₁ S.ν D ψ')
                  s.1 s.2)))
              (fun _ => (1 : ℂ)) x.2 w.2 σ Θ.1)) ∧
        ∀ (g : Fld 3 3 N₁ m₁ (k + 1) 2) (x : S.EC),
          (∀ r : ℝ, r ∈ Set.Icc (0 : ℝ) 1 → ∀ q, ‖((r : ℂ) • x) q‖ ≤ 2 * p₁) →
          ∀ τ : ℝ, τ ∈ Set.Icc (0 : ℝ) 1 →
            Jr.W2 (zeroClass 3 3 N₁ m₁ k 2 (rhoSep m₁)) g (rawOf S.D', (τ : ℂ) • x) =
              val (x, x) (x, x) (τ : ℂ) (rawOf S.D', fun y i => g y i / (S.β : ℂ)) -
                val (x, x) (x, x) (τ : ℂ) (rawOf S.D', 0) := by
  classical
  obtain ⟨T⟩ := exists_stepTower 0
  obtain ⟨βray, hβray, hscale⟩ := T.scale hA p
  refine ⟨T.m₁, T.t, T.δ, βray, T.BG₂, T.κ, hβray, T.t_pos, T.δ_pos, ?_⟩
  intro k hk N₁ _ h3N hN ν hνpos hν β hβ p₁ hp0 hp₁ S hS
  subst hS
  obtain ⟨D⟩ := hscale k hk N₁ h3N hN ν hνpos.le hν β hβ p₁ hp0 hp₁
  exact expSourceChart_scale_fromTower T k hk N₁ ν hνpos hν β p₁ hp0 D

end Balaban.Inhabited
