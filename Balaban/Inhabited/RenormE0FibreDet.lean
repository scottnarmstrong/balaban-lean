/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepTowerTheta
public import Balaban.Inhabited.RenormDetFibreTower
public import Balaban.Fluctuation.RenormExpCauchy
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The determinant part of the new energy function as a localized expansion on the cover

For the shared tower with the determinant data at the doubled chart radius (`StepTowerTheta`), the
determinant part `renE0θ_det` of the new energy function is a localized expansion over the
renormalization cover `renYs`, in exactly the type of the `expE0` field of `RenormExpInput`.

The terms are `t_Y(q) = ∑_{X : Φ X = Y} F_X(q)`, a finite sum over the polymers in the fibre of
`renFibreMap`, where `F_X` is the ambient analytic function of
`StepTowerTheta.detGrouped_ambient` (chosen once).  All fibre facts are for the one family of
records at chart radius `2 t`.

## Main results

* `renE0_fibre_det`: the four clauses of `IsLocExp` for `renE0θ_det` at rate `3 κ_dec / 2`
  and constant `hullConst · e^{c₁ log 2} · e^{hullRate}`.
* `expE0_det_scale_of_tower`: the `expE0`-shaped statement at every scale, together with the
  value at `ξ = 0`.

## What is not asserted

`renE0θ_det` is only the determinant summand of the new energy function.  The marked energy
terms are not included, so `expE0_det_scale_of_tower` is **not** the physical `expE0` field of the
renormalization input record; it is the determinant summand, proved unconditionally.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep LocalCover

open Classical in
/-- **The determinant part on the cover (the four clauses).**  For `renDetFibreMin ≤ κmin`, at
every scale there is one family `z ↦ E z` of determinant records at chart radius `2 t` with the
term formula, such that for every root `z` there are ambient analytic functions `F_X` (one per
polymer `X`) for which the terms `t_Y = ∑_{Φ X = Y} F_X` make `renE0θ_det R.t E z` a localized
expansion over `renYs` with rate `3 κ_dec / 2` in `renDY` and constant
`hullConst · e^{c₁ log 2} · e^{hullRate}`; the value at `ξ = 0` is the determinant term of the
step.  Determinant part only. -/
theorem renE0_fibre_det {κmin : ℝ} (R : StepTowerTheta κmin) (hR : renDetFibreMin ≤ κmin)
    (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (h3N : 3 ∣ N₁) (hN : 5 < N₁) {ν : ℝ}
    (hν0 : 0 ≤ ν) (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) (β p₁ : ℝ) :
    ∃ E : ∀ z : Torus 3 (N₁ * 3 ^ R.m₁ * 3 ^ (k + 1 - (k + 1))),
        DetExpansionLocC (R.toStepTower.step k hk N₁ ν β p₁) 1 z (2 * R.t)
          (towerDetRate R.κ) (towerDetConst R.κ),
      (∀ z, renE0θ_det R.t E z (R.toStepTower.step k hk N₁ ν β p₁).D' 0 =
          -(1 / 2 : ℂ) * ∑ y ∈ (R.toStepTower.step k hk N₁ ν β p₁).blockU z, ∑ i : Fin 2,
            (R.toStepTower.step k hk N₁ ν β p₁).logAC (y, i) (y, i)) ∧
      ∀ z : Torus 3 (N₁ * 3 ^ R.m₁ * 3 ^ (k + 1 - (k + 1))),
        ∃ F : Set (CTorus 3 3 N₁ R.m₁ (k + 1)) →
            RawData 3 3 (N₁ * 3 ^ R.m₁) (k + 1) 2 × (Fin 3 → ℂ) → ℂ,
          (∀ X, AnalyticOnNhd ℂ (F X) (expDom (lvTop N₁ R.m₁ k (rhoSep R.m₁))
            (XiCOneReal (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν R.t) R.r₀)) ∧
          IsLocExp (N := 2) (lvTop N₁ R.m₁ k (rhoSep R.m₁))
            (XiCOneReal (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν R.t) R.r₀
            (renYs (renCube (lvTop N₁ R.m₁ k (rhoSep R.m₁))
                (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (blockSite k z))))
              (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1
              (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (blockSite k z))))
            (renDY (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1) (3 / 2 * R.κdec)
            (hullConst 3 3 (towerDetRate R.κ) (towerDetConst R.κ) *
              Real.exp (c1 3 3 * Real.log 2) * Real.exp (hullRate 3 3 (towerDetRate R.κ)))
            (renE0θ_det R.t E z)
            (fun Y q => ∑ X ∈ Finset.univ.filter (fun X : Set (CTorus 3 3 N₁ R.m₁ (k + 1)) =>
                renFibreMap (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1
                  (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (blockSite k z))) X = Y),
              F X q) := by
  obtain ⟨E, hE, hzero, hamb⟩ := R.detGrouped_ambient k hk N₁ h3N hN hν0 hν β p₁
  refine ⟨E, hzero, fun z => ?_⟩
  choose F hFan hFr using hamb z
  refine ⟨F, hFan, ?_⟩
  have hstep : detHullThreshold ≤ κmin := le_trans stepHullMin_le_renDetFibreMin hR
  have hN1 : (3 : ℕ) ^ 1 ∣ N₁ := by simpa using h3N
  have h3 : 3 ≤ 3 ^ (1 + R.m₁) := by
    calc 3 = 3 ^ 1 := by norm_num
      _ ≤ 3 ^ (1 + R.m₁) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hH := bgHyp_lv (k := k) R.m₁ hν0 hν
  have hM := thetaChartMargin_of_stepTowerRenSol R.toStepTowerRenSol
  have hle := R.εs_le
  have hrate := towerDetRate_nonneg R.toStepTower
  have hconst := towerDetConst_nonneg R.toStepTower
  have hhr := towerDetHullRate_ge R.toStepTower hstep
  have hκ0 : 0 ≤ 3 / 2 * R.κdec := by
    have := R.κdec_lower; have := R.κ0_nonneg; linarith
  have hH0 : 0 ≤ hullConst 3 3 (towerDetRate R.κ) (towerDetConst R.κ) := by
    unfold hullConst; exact mul_nonneg hconst (Real.exp_pos _).le
  have hlam : 0 ≤ hullRate 3 3 (towerDetRate R.κ) :=
    le_trans (by linarith) hhr
  obtain ⟨hS, hopt, hΔ, hG, hx⟩ := renDetFibre_root R.toStepTower k hk N₁ h3N hN hν0 hν z
  have hθ : ∀ D : BgData (R.toStepTower.step k hk N₁ ν β p₁).G' 2,
      XiCOneReal (R.toStepTower.step k hk N₁ ν β p₁).G' (R.toStepTower.step k hk N₁ ν β p₁).a
        (R.toStepTower.step k hk N₁ ν β p₁).ν R.t D → ∀ ξ : Fin 3 → ℂ, ‖ξ‖ < R.r₀ →
      XiCData (R.toStepTower.step k hk N₁ ν β p₁).G' (compWeight 3 1) ν (k + 1) 1 (2 * R.t)
        (renThetaDatum (R.toStepTower.step k hk N₁ ν β p₁) R.t D ξ) :=
    fun D hD ξ hξ => renE0_theta_domain_of_le _ hH R.t _ (2 * R.t) R.r₀ hM hle D hD ξ hξ
  have ht0 : ∀ D' : BgData (R.toStepTower.step k hk N₁ ν β p₁).G' 2,
      XiCData (R.toStepTower.step k hk N₁ ν β p₁).G' (compWeight 3 1) ν (k + 1) 1 (2 * R.t) D' →
      ∀ X : Set (CTorus 3 3 N₁ R.m₁ (k + 1)),
        ¬ (IsPolyDom 1 (k + 1) X ∧ ∃ x ∈ X,
          x ∈ X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (blockSite k z))) →
        (E z).detGrouped D' X = 0 := by
    intro D' hD' X hX
    by_contra hne
    obtain ⟨hpoly, hroot⟩ := (E z).detGrouped_anchor (by norm_num) hN1 hD' hne
    exact hX ⟨hpoly, blockSite k z, hroot (rootSite_mem_box_rootCube (m₀ := 1) (K := k + 1) z),
      hx⟩
  have hsub : ∀ {X : Set (CTorus 3 3 N₁ R.m₁ (k + 1))}, X ⊆ ↑(renFibreMap
      (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1
      (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (blockSite k z))) X) :=
    fun {X} => subset_renFibreMap hS hG
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- sum identity
    intro D hD ξ hξ
    have h1 := sum_renRegroup hS hG ((E z).detGrouped (renThetaDatum
      (R.toStepTower.step k hk N₁ ν β p₁) R.t D ξ)) (ht0 _ (hθ D hD ξ hξ))
    have h2 : ∑ X, (E z).detGrouped (renThetaDatum (R.toStepTower.step k hk N₁ ν β p₁) R.t D ξ)
        X = ∑ X ∈ (Finset.univ : Finset (Finset (CubeB (d := 3) (L := 3) (N₁ := N₁)
          (m₁ := R.m₁) (K := k + 1) 1 (k + 1) Set.univ))).image detCollarHull,
        (E z).detGrouped (renThetaDatum (R.toStepTower.step k hk N₁ ν β p₁) R.t D ξ) X := by
      symm
      refine Finset.sum_subset (Finset.subset_univ _) fun X _ hX => ?_
      unfold DetExpansionLocC.detGrouped detCollarGrouped
      refine Finset.sum_eq_zero fun T' hT' => absurd ?_ hX
      rw [← mem_detCollarFibre.1 hT']
      exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
    refine (renE0θ_det_eq_sum_collar R.t E z D ξ).symm.trans ?_
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
    refine (E z).detGrouped_local (by norm_num) hN1 h3 (hθ D hD _ hξq) (hθ D' hD' _ hξq')
      fun v hv => ?_
    have hvY : v ∈ Y := by
      rw [← hΦ, ← Finset.mem_coe]; exact hsub hv
    obtain ⟨a, b⟩ := hag v hvY
    exact renThetaDatum_agree _ _ a b
  · -- bound
    rintro Y _ ⟨p, ξ⟩ ⟨D, hD, rfl, hξq⟩
    simp only at hξq
    have hsum : ∑ X ∈ Finset.univ.filter (fun X : Set (CTorus 3 3 N₁ R.m₁ (k + 1)) =>
          renFibreMap (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1
            (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (blockSite k z))) X = Y),
        F X ((D.Ψ, D.h), ξ) = ∑ X ∈ Finset.univ.filter
          (fun X : Set (CTorus 3 3 N₁ R.m₁ (k + 1)) =>
            renFibreMap (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1
              (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (blockSite k z))) X = Y),
        (E z).detGrouped (renThetaDatum (R.toStepTower.step k hk N₁ ν β p₁) R.t D ξ) X :=
      Finset.sum_congr rfl fun X _ => ((hFr X D hD).1 ξ hξq).1
    rw [hsum]
    exact renRegroup_norm_le hS hG (by norm_num) hopt hΔ
      ((E z).detGrouped (renThetaDatum (R.toStepTower.step k hk N₁ ν β p₁) R.t D ξ))
      hH0 hlam (ht0 _ (hθ D hD _ hξq))
      (fun X _ _ => (E z).detGrouped_bound (by norm_num) hN1 hconst hrate (hθ D hD _ hξq) X)
      (renDetFibreMin_spec R.toStepTower hR) Y

/-- **The determinant-only `expE0` statement at every scale.**  This is NOT the physical `expE0`
field of the renormalization input record: the marked energy terms are missing from `E0θ`, and
`renE0θ_det` is only the determinant summand of the new energy function.  What is proved,
unconditionally for `renDetFibreMin ≤ κmin`, is that the determinant summand has the shape of
that field: for every root `z`, a localized expansion over `renYs` at rate `3 κ_dec / 2` and
constant `H′ = hullConst · e^{c₁ log 2} · e^{hullRate}`; and that its value at `ξ = 0` is the
determinant term of the step. -/
theorem expE0_det_scale_of_tower {κmin : ℝ} (R : StepTowerTheta κmin)
    (hR : renDetFibreMin ≤ κmin) (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (h3N : 3 ∣ N₁)
    (hN : 5 < N₁) {ν : ℝ} (hν0 : 0 ≤ ν) (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) (β p₁ : ℝ) :
    ∃ E : ∀ z : Torus 3 (N₁ * 3 ^ R.m₁ * 3 ^ (k + 1 - (k + 1))),
        DetExpansionLocC (R.toStepTower.step k hk N₁ ν β p₁) 1 z (2 * R.t)
          (towerDetRate R.κ) (towerDetConst R.κ),
      (∀ z, renE0θ_det R.t E z (R.toStepTower.step k hk N₁ ν β p₁).D' 0 =
          -(1 / 2 : ℂ) * ∑ y ∈ (R.toStepTower.step k hk N₁ ν β p₁).blockU z, ∑ i : Fin 2,
            (R.toStepTower.step k hk N₁ ν β p₁).logAC (y, i) (y, i)) ∧
      ∀ z : Torus 3 (N₁ * 3 ^ R.m₁ * 3 ^ (k + 1 - (k + 1))), ∃ term,
        IsLocExp (N := 2) (lvTop N₁ R.m₁ k (rhoSep R.m₁))
          (XiCOneReal (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν R.t) R.r₀
          (renYs (renCube (lvTop N₁ R.m₁ k (rhoSep R.m₁))
              (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (blockSite k z))))
            (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1
            (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (blockSite k z))))
          (renDY (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1) (3 / 2 * R.κdec)
          (hullConst 3 3 (towerDetRate R.κ) (towerDetConst R.κ) *
            Real.exp (c1 3 3 * Real.log 2) * Real.exp (hullRate 3 3 (towerDetRate R.κ)))
          (renE0θ_det R.t E z) term := by
  obtain ⟨E, hz, h⟩ := renE0_fibre_det R hR k hk N₁ h3N hN hν0 hν β p₁
  refine ⟨E, hz, fun z => ?_⟩
  obtain ⟨F, -, hF⟩ := h z
  exact ⟨_, hF⟩

end Balaban.Inhabited
