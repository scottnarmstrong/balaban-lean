/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepTowerThetaDetG
public import Balaban.Inhabited.RenormDetFibreTower
public import Balaban.Fluctuation.RenormExpCauchy
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The determinant part of the new energy function on the cover, general tower

For the general tower with the determinant data at the doubled chart radius (`StepTowerThetaG`),
and a renormalization radius `0 < e ≤ t`, the determinant part `renE0θ_det e` of the new energy
function is a localized expansion over the renormalization cover `renYs`, in the type of the
`expE0` field of the renormalization input.

The terms are `t_Y(q) = ∑_{X : Φ X = Y} F_X(q)`, a finite sum over the polymers in the fibre of
`renFibreMap`, where `F_X` is the ambient analytic function of
`StepTowerThetaG.detGrouped_ambient_at`.  The rate survives the regrouping under the explicit
hull hypothesis of `StepTowerG.renDetFibre_spec` on `κ`.

## Main results

* `StepTowerThetaG.renE0_fibre_det_at`: the four clauses of `IsLocExp` for `renE0θ_det e`.
* `StepTowerThetaG.renE0_fibre_det`: the case `e = t`.
* `StepTowerThetaG.expE0_det_scale_of_tower_at`, `StepTowerThetaG.expE0_det_scale_of_tower`:
  the `expE0`-shaped statements.

## What is not asserted

Determinant summand only; the marked energy terms are not included.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep LocalCover

section TowerG

variable {d L N : ℕ} [NeZero L] {κmin : ℝ}

open Classical in
/-- **The determinant part on the cover at radius `e ≤ t`, general tower (the four clauses).**
Under the hull hypothesis `hhull` of `StepTowerG.renDetFibre_spec`, at every scale there is one
family `z ↦ E z` of determinant records at chart radius `2 t` with the term formula, such that for
every root `z` there are ambient analytic functions `F_X` (one per polymer `X`) for which the
terms `t_Y = ∑_{Φ X = Y} F_X` make `renE0θ_det e E z` a localized expansion over `renYs` with
rate `3 κ_dec / 2` in `renDY` and constant `hullConst · e^{c₁ log 2} · e^{hullRate}`; the value at
`ξ = 0` is the determinant term of the step.  Determinant part only. -/
theorem StepTowerThetaG.renE0_fibre_det_at (T : StepTowerThetaG d L N κmin)
    (hhull : 2 * d * L * (1 + collarB d L) *
        (renDetA d L 1 * (3 / 2 * T.κdec + c1 d L * Real.log 2) + c1 d L * Real.log 2) +
      Real.log 2 + 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ) ≤ T.κ)
    {e : ℝ} (he : 0 < e) (het : e ≤ T.t)
    (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (hLN : L ∣ N₁) (hN5 : 5 < N₁) {ν : ℝ}
    (hν0 : 0 ≤ ν) (hν : ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1) (β p₁ : ℝ) :
    ∃ E : ∀ z : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))),
        DetExpansionLocC (T.step k hk N₁ ν β p₁) 1 z (2 * T.t)
          ((T.κ - Real.log 2 - 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) / (2 * d * L))
          ((L : ℝ) ^ d * ((1 / 2 : ℝ) * N * covBLogMax d L T.κ /
            (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp T.κ)))),
      (∀ z, renE0θ_det e E z (T.step k hk N₁ ν β p₁).D' 0 =
          -(1 / 2 : ℂ) * ∑ y ∈ (T.step k hk N₁ ν β p₁).blockU z, ∑ i : Fin N,
            (T.step k hk N₁ ν β p₁).logAC (y, i) (y, i)) ∧
      ∀ z : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))),
        ∃ F : Set (CTorus d L N₁ T.m₁ (k + 1)) →
            RawData d L (N₁ * L ^ T.m₁) (k + 1) N × (Fin 3 → ℂ) → ℂ,
          (∀ X, AnalyticOnNhd ℂ (F X) (expDom (lvTopG d L N₁ T.m₁ k (rhoSepG d L T.m₁))
            (XiCOneReal (lvTopG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (compWeight L 1) ν e)
            T.r₀)) ∧
          IsLocExp (N := N) (lvTopG d L N₁ T.m₁ k (rhoSepG d L T.m₁))
            (XiCOneReal (lvTopG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (compWeight L 1) ν e) T.r₀
            (renYs (renCube (lvTopG d L N₁ T.m₁ k (rhoSepG d L T.m₁))
                (X1 (lvTopG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) 1 k (fam 1 (blockSite k z))))
              (lvTopG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) 1
              (X1 (lvTopG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) 1 k (fam 1 (blockSite k z))))
            (renDY (lvTopG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) 1) (3 / 2 * T.κdec)
            (hullConst d L
                ((T.κ - Real.log 2 - 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) / (2 * d * L))
                ((L : ℝ) ^ d * ((1 / 2 : ℝ) * N * covBLogMax d L T.κ /
                  (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp T.κ)))) *
              Real.exp (c1 d L * Real.log 2) *
              Real.exp (hullRate d L
                ((T.κ - Real.log 2 - 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) / (2 * d * L))))
            (renE0θ_det e E z)
            (fun Y q => ∑ X ∈ Finset.univ.filter (fun X : Set (CTorus d L N₁ T.m₁ (k + 1)) =>
                renFibreMap (lvTopG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) 1
                  (X1 (lvTopG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) 1 k
                    (fam 1 (blockSite k z))) X = Y),
              F X q) := by
  obtain ⟨E, hE, hzero, hamb⟩ := T.detGrouped_ambient_at he het k hk N₁ hLN hN5 hν0 hν β p₁
  refine ⟨E, hzero, fun z => ?_⟩
  choose F hFan hFr using hamb z
  refine ⟨F, hFan, ?_⟩
  have hN1 : L ^ 1 ∣ N₁ := by simpa using hLN
  have h3 : 3 ≤ L ^ (1 + T.m₁) :=
    calc 3 ≤ L := T.hL
      _ = L ^ 1 := (pow_one L).symm
      _ ≤ L ^ (1 + T.m₁) := Nat.pow_le_pow_right (by have := T.hL; omega) (by omega)
  have hH := bgHyp_lvG (k := k) T.hd T.hL (bgR0_le_rhoSepG T.m₁ T.hd T.hL) hν0 hν
  obtain ⟨hM, hle0⟩ := T.thetaChartMargin_of_le he het
  have hle : e + xiK2 d L N * (3 / 2 * e * T.r₀) ≤ 2 * T.t := by linarith
  have hrate := T.detRate_nonneg
  have hconst := T.detConst_nonneg
  have hspec := T.toStepTowerG.renDetFibre_spec hhull
  have hA := renDetA_pos d L 1 T.hd
  have hH0 : 0 ≤ hullConst d L
      ((T.κ - Real.log 2 - 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) / (2 * d * L))
      ((L : ℝ) ^ d * ((1 / 2 : ℝ) * N * covBLogMax d L T.κ /
        (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp T.κ)))) := by
    unfold hullConst; exact mul_nonneg hconst (Real.exp_pos _).le
  have hlam : 0 ≤ hullRate d L
      ((T.κ - Real.log 2 - 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) / (2 * d * L)) := by
    have hκ0 : 0 ≤ 3 / 2 * T.κdec := by
      have := T.κdec_lower; have := T.κ0_nonneg; linarith
    have h1 : 0 ≤ 3 / 2 * T.κdec + c1 d L * Real.log 2 := by
      have := one_le_c1 d L
      have : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      positivity
    have h2 : 3 / 2 * T.κdec + c1 d L * Real.log 2 ≤
        hullRate d L (detRateG d L T.κ) / renDetA d L 1 := by linarith
    have h3 := (le_div_iff₀ hA).1 h2
    exact le_trans (by positivity) h3
  obtain ⟨hS, hopt, hΔ, hG, hx⟩ :=
    T.toStepTowerG.renDetFibre_root k hk N₁ hLN hN5 hν0 hν z
  have hθ : ∀ D : BgData (T.step k hk N₁ ν β p₁).G' N,
      XiCOneReal (T.step k hk N₁ ν β p₁).G' (T.step k hk N₁ ν β p₁).a
        (T.step k hk N₁ ν β p₁).ν e D → ∀ ξ : Fin 3 → ℂ, ‖ξ‖ < T.r₀ →
      XiCData (T.step k hk N₁ ν β p₁).G' (compWeight L 1) ν (k + 1) 1 (2 * T.t)
        (renThetaDatum (T.step k hk N₁ ν β p₁) e D ξ) :=
    fun D hD ξ hξ => renE0_theta_domain_of_le _ hH e _ (2 * T.t) T.r₀ hM hle D hD ξ hξ
  have ht0 : ∀ D' : BgData (T.step k hk N₁ ν β p₁).G' N,
      XiCData (T.step k hk N₁ ν β p₁).G' (compWeight L 1) ν (k + 1) 1 (2 * T.t) D' →
      ∀ X : Set (CTorus d L N₁ T.m₁ (k + 1)),
        ¬ (IsPolyDom 1 (k + 1) X ∧ ∃ x ∈ X,
          x ∈ X1 (lvTopG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) 1 k (fam 1 (blockSite k z))) →
        (E z).detGrouped D' X = 0 := by
    intro D' hD' X hX
    by_contra hne
    obtain ⟨hpoly, hroot⟩ := (E z).detGrouped_anchor T.hL hN1 hD' hne
    exact hX ⟨hpoly, blockSite k z, hroot (rootSite_mem_box_rootCube (m₀ := 1) (K := k + 1) z),
      hx⟩
  have hsub : ∀ {X : Set (CTorus d L N₁ T.m₁ (k + 1))}, X ⊆ ↑(renFibreMap
      (lvTopG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) 1
      (X1 (lvTopG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) 1 k (fam 1 (blockSite k z))) X) :=
    fun {X} => subset_renFibreMap hS hG
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- sum identity
    intro D hD ξ hξ
    have h1 := sum_renRegroup hS hG ((E z).detGrouped (renThetaDatum
      (T.step k hk N₁ ν β p₁) e D ξ)) (ht0 _ (hθ D hD ξ hξ))
    have h2 : ∑ X, (E z).detGrouped (renThetaDatum (T.step k hk N₁ ν β p₁) e D ξ)
        X = ∑ X ∈ (Finset.univ : Finset (Finset (CubeB (d := d) (L := L) (N₁ := N₁)
          (m₁ := T.m₁) (K := k + 1) 1 (k + 1) Set.univ))).image detCollarHull,
        (E z).detGrouped (renThetaDatum (T.step k hk N₁ ν β p₁) e D ξ) X := by
      symm
      refine Finset.sum_subset (Finset.subset_univ _) fun X _ hX => ?_
      unfold DetExpansionLocC.detGrouped detCollarGrouped
      refine Finset.sum_eq_zero fun T' hT' => absurd ?_ hX
      rw [← mem_detCollarFibre.1 hT']
      exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
    refine (renE0θ_det_eq_sum_collar e E z D ξ).symm.trans ?_
    rw [← h2, ← h1]
    refine Finset.sum_congr rfl fun Y _ => Finset.sum_congr rfl fun X _ => ?_
    exact ((hFr X D hD).1 ξ hξ).1.symm
  · -- analyticity
    intro Y _
    exact Finset.analyticOnNhd_fun_sum _ fun X _ => hFan X
  · -- locality
    rintro Y _ ⟨p, ξ⟩ ⟨D, hD, rfl, hξq⟩ ⟨p', ξ'⟩ ⟨D', hD', rfl, hξq'⟩ hξ hag
    simp only at hξ hag hξq hξq'
    subst hξ
    refine Finset.sum_congr rfl fun X hX => ?_
    have hΦ := (Finset.mem_filter.1 hX).2
    rw [((hFr X D hD).1 _ hξq).1, ((hFr X D' hD').1 _ hξq').1]
    refine (E z).detGrouped_local T.hL hN1 h3 (hθ D hD _ hξq) (hθ D' hD' _ hξq')
      fun v hv => ?_
    have hvY : v ∈ Y := by
      rw [← hΦ, ← Finset.mem_coe]; exact hsub hv
    obtain ⟨a, b⟩ := hag v hvY
    exact renThetaDatum_agree _ _ a b
  · -- bound
    rintro Y _ ⟨p, ξ⟩ ⟨D, hD, rfl, hξq⟩
    simp only at hξq
    have hsum : ∑ X ∈ Finset.univ.filter (fun X : Set (CTorus d L N₁ T.m₁ (k + 1)) =>
          renFibreMap (lvTopG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) 1
            (X1 (lvTopG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) 1 k (fam 1 (blockSite k z))) X = Y),
        F X ((D.Ψ, D.h), ξ) = ∑ X ∈ Finset.univ.filter
          (fun X : Set (CTorus d L N₁ T.m₁ (k + 1)) =>
            renFibreMap (lvTopG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) 1
              (X1 (lvTopG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) 1 k
                (fam 1 (blockSite k z))) X = Y),
        (E z).detGrouped (renThetaDatum (T.step k hk N₁ ν β p₁) e D ξ) X :=
      Finset.sum_congr rfl fun X _ => ((hFr X D hD).1 ξ hξq).1
    rw [hsum]
    exact renRegroup_norm_le hS hG T.hd hopt hΔ
      ((E z).detGrouped (renThetaDatum (T.step k hk N₁ ν β p₁) e D ξ))
      hH0 hlam (ht0 _ (hθ D hD _ hξq))
      (fun X _ _ => (E z).detGrouped_bound T.hL hN1 hconst hrate (hθ D hD _ hξq) X)
      hspec Y

open Classical in
/-- **The determinant part on the cover, general tower (the four clauses).**  The case `e = t` of
`StepTowerThetaG.renE0_fibre_det_at`. -/
theorem StepTowerThetaG.renE0_fibre_det (T : StepTowerThetaG d L N κmin)
    (hhull : 2 * d * L * (1 + collarB d L) *
        (renDetA d L 1 * (3 / 2 * T.κdec + c1 d L * Real.log 2) + c1 d L * Real.log 2) +
      Real.log 2 + 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ) ≤ T.κ)
    (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (hLN : L ∣ N₁) (hN5 : 5 < N₁) {ν : ℝ}
    (hν0 : 0 ≤ ν) (hν : ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1) (β p₁ : ℝ) :
    ∃ E : ∀ z : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))),
        DetExpansionLocC (T.step k hk N₁ ν β p₁) 1 z (2 * T.t)
          ((T.κ - Real.log 2 - 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) / (2 * d * L))
          ((L : ℝ) ^ d * ((1 / 2 : ℝ) * N * covBLogMax d L T.κ /
            (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp T.κ)))),
      (∀ z, renE0θ_det T.t E z (T.step k hk N₁ ν β p₁).D' 0 =
          -(1 / 2 : ℂ) * ∑ y ∈ (T.step k hk N₁ ν β p₁).blockU z, ∑ i : Fin N,
            (T.step k hk N₁ ν β p₁).logAC (y, i) (y, i)) ∧
      ∀ z : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))),
        ∃ F : Set (CTorus d L N₁ T.m₁ (k + 1)) →
            RawData d L (N₁ * L ^ T.m₁) (k + 1) N × (Fin 3 → ℂ) → ℂ,
          (∀ X, AnalyticOnNhd ℂ (F X) (expDom (lvTopG d L N₁ T.m₁ k (rhoSepG d L T.m₁))
            (XiCOneReal (lvTopG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (compWeight L 1) ν T.t)
            T.r₀)) ∧
          IsLocExp (N := N) (lvTopG d L N₁ T.m₁ k (rhoSepG d L T.m₁))
            (XiCOneReal (lvTopG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (compWeight L 1) ν T.t) T.r₀
            (renYs (renCube (lvTopG d L N₁ T.m₁ k (rhoSepG d L T.m₁))
                (X1 (lvTopG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) 1 k (fam 1 (blockSite k z))))
              (lvTopG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) 1
              (X1 (lvTopG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) 1 k (fam 1 (blockSite k z))))
            (renDY (lvTopG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) 1) (3 / 2 * T.κdec)
            (hullConst d L
                ((T.κ - Real.log 2 - 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) / (2 * d * L))
                ((L : ℝ) ^ d * ((1 / 2 : ℝ) * N * covBLogMax d L T.κ /
                  (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp T.κ)))) *
              Real.exp (c1 d L * Real.log 2) *
              Real.exp (hullRate d L
                ((T.κ - Real.log 2 - 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) / (2 * d * L))))
            (renE0θ_det T.t E z)
            (fun Y q => ∑ X ∈ Finset.univ.filter (fun X : Set (CTorus d L N₁ T.m₁ (k + 1)) =>
                renFibreMap (lvTopG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) 1
                  (X1 (lvTopG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) 1 k
                    (fam 1 (blockSite k z))) X = Y),
              F X q) :=
  T.renE0_fibre_det_at hhull T.t_pos le_rfl k hk N₁ hLN hN5 hν0 hν β p₁

/-- **The determinant-only `expE0` statement at every scale, general tower, radius `e ≤ t`.**
NOT the physical `expE0` field: the marked energy terms are missing. -/
theorem StepTowerThetaG.expE0_det_scale_of_tower_at (T : StepTowerThetaG d L N κmin)
    (hhull : 2 * d * L * (1 + collarB d L) *
        (renDetA d L 1 * (3 / 2 * T.κdec + c1 d L * Real.log 2) + c1 d L * Real.log 2) +
      Real.log 2 + 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ) ≤ T.κ)
    {e : ℝ} (he : 0 < e) (het : e ≤ T.t)
    (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (hLN : L ∣ N₁) (hN5 : 5 < N₁) {ν : ℝ}
    (hν0 : 0 ≤ ν) (hν : ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1) (β p₁ : ℝ) :
    ∃ E : ∀ z : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))),
        DetExpansionLocC (T.step k hk N₁ ν β p₁) 1 z (2 * T.t)
          ((T.κ - Real.log 2 - 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) / (2 * d * L))
          ((L : ℝ) ^ d * ((1 / 2 : ℝ) * N * covBLogMax d L T.κ /
            (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp T.κ)))),
      (∀ z, renE0θ_det e E z (T.step k hk N₁ ν β p₁).D' 0 =
          -(1 / 2 : ℂ) * ∑ y ∈ (T.step k hk N₁ ν β p₁).blockU z, ∑ i : Fin N,
            (T.step k hk N₁ ν β p₁).logAC (y, i) (y, i)) ∧
      ∀ z : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))), ∃ term,
        IsLocExp (N := N) (lvTopG d L N₁ T.m₁ k (rhoSepG d L T.m₁))
          (XiCOneReal (lvTopG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (compWeight L 1) ν e) T.r₀
          (renYs (renCube (lvTopG d L N₁ T.m₁ k (rhoSepG d L T.m₁))
              (X1 (lvTopG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) 1 k (fam 1 (blockSite k z))))
            (lvTopG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) 1
            (X1 (lvTopG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) 1 k (fam 1 (blockSite k z))))
          (renDY (lvTopG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) 1) (3 / 2 * T.κdec)
          (hullConst d L
              ((T.κ - Real.log 2 - 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) / (2 * d * L))
              ((L : ℝ) ^ d * ((1 / 2 : ℝ) * N * covBLogMax d L T.κ /
                (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp T.κ)))) *
            Real.exp (c1 d L * Real.log 2) *
            Real.exp (hullRate d L
              ((T.κ - Real.log 2 - 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) / (2 * d * L))))
          (renE0θ_det e E z) term := by
  obtain ⟨E, hz, h⟩ := T.renE0_fibre_det_at hhull he het k hk N₁ hLN hN5 hν0 hν β p₁
  refine ⟨E, hz, fun z => ?_⟩
  obtain ⟨F, -, hF⟩ := h z
  exact ⟨_, hF⟩

/-- **The determinant-only `expE0` statement at every scale, general tower.**  The case `e = t`
of `StepTowerThetaG.expE0_det_scale_of_tower_at`. -/
theorem StepTowerThetaG.expE0_det_scale_of_tower (T : StepTowerThetaG d L N κmin)
    (hhull : 2 * d * L * (1 + collarB d L) *
        (renDetA d L 1 * (3 / 2 * T.κdec + c1 d L * Real.log 2) + c1 d L * Real.log 2) +
      Real.log 2 + 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ) ≤ T.κ)
    (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (hLN : L ∣ N₁) (hN5 : 5 < N₁) {ν : ℝ}
    (hν0 : 0 ≤ ν) (hν : ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1) (β p₁ : ℝ) :
    ∃ E : ∀ z : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))),
        DetExpansionLocC (T.step k hk N₁ ν β p₁) 1 z (2 * T.t)
          ((T.κ - Real.log 2 - 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) / (2 * d * L))
          ((L : ℝ) ^ d * ((1 / 2 : ℝ) * N * covBLogMax d L T.κ /
            (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp T.κ)))),
      (∀ z, renE0θ_det T.t E z (T.step k hk N₁ ν β p₁).D' 0 =
          -(1 / 2 : ℂ) * ∑ y ∈ (T.step k hk N₁ ν β p₁).blockU z, ∑ i : Fin N,
            (T.step k hk N₁ ν β p₁).logAC (y, i) (y, i)) ∧
      ∀ z : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))), ∃ term,
        IsLocExp (N := N) (lvTopG d L N₁ T.m₁ k (rhoSepG d L T.m₁))
          (XiCOneReal (lvTopG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (compWeight L 1) ν T.t) T.r₀
          (renYs (renCube (lvTopG d L N₁ T.m₁ k (rhoSepG d L T.m₁))
              (X1 (lvTopG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) 1 k (fam 1 (blockSite k z))))
            (lvTopG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) 1
            (X1 (lvTopG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) 1 k (fam 1 (blockSite k z))))
          (renDY (lvTopG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) 1) (3 / 2 * T.κdec)
          (hullConst d L
              ((T.κ - Real.log 2 - 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) / (2 * d * L))
              ((L : ℝ) ^ d * ((1 / 2 : ℝ) * N * covBLogMax d L T.κ /
                (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp T.κ)))) *
            Real.exp (c1 d L * Real.log 2) *
            Real.exp (hullRate d L
              ((T.κ - Real.log 2 - 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) / (2 * d * L))))
          (renE0θ_det T.t E z) term :=
  T.expE0_det_scale_of_tower_at hhull T.t_pos le_rfl k hk N₁ hLN hN5 hν0 hν β p₁

end TowerG

end Balaban.Inhabited
