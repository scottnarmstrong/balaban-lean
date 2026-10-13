/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepTowerTheta
public import Balaban.Inhabited.RenormDetFibreTower
public import Balaban.Inhabited.RenormE0FibreDetG
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

* `renE0_fibre_det_at`: the four clauses at a renormalization radius `e ≤ t`, a corollary of
  `StepTowerThetaG.renE0_fibre_det_at`; `renE0_fibre_det` is its case `e = t`.
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
/-- **The determinant part on the cover at radius `e <= t` (the four clauses).**  For `renDetFibreMin ≤ κmin`, at
every scale there is one family `z ↦ E z` of determinant records at chart radius `2 t` with the
term formula, such that for every root `z` there are ambient analytic functions `F_X` (one per
polymer `X`) for which the terms `t_Y = ∑_{Φ X = Y} F_X` make `renE0θ_det e E z` a localized
expansion over `renYs` with rate `3 κ_dec / 2` in `renDY` and constant
`hullConst · e^{c₁ log 2} · e^{hullRate}`; the value at `ξ = 0` is the determinant term of the
step.  Determinant part only. -/
theorem renE0_fibre_det_at {κmin : ℝ} (R : StepTowerTheta κmin) (hR : renDetFibreMin ≤ κmin)
    {e : ℝ} (he : 0 < e) (het : e ≤ R.t)
    (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (h3N : 3 ∣ N₁) (hN : 5 < N₁) {ν : ℝ}
    (hν0 : 0 ≤ ν) (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) (β p₁ : ℝ) :
    ∃ E : ∀ z : Torus 3 (N₁ * 3 ^ R.m₁ * 3 ^ (k + 1 - (k + 1))),
        DetExpansionLocC (R.toStepTower.step k hk N₁ ν β p₁) 1 z (2 * R.t)
          (towerDetRate R.κ) (towerDetConst R.κ),
      (∀ z, renE0θ_det e E z (R.toStepTower.step k hk N₁ ν β p₁).D' 0 =
          -(1 / 2 : ℂ) * ∑ y ∈ (R.toStepTower.step k hk N₁ ν β p₁).blockU z, ∑ i : Fin 2,
            (R.toStepTower.step k hk N₁ ν β p₁).logAC (y, i) (y, i)) ∧
      ∀ z : Torus 3 (N₁ * 3 ^ R.m₁ * 3 ^ (k + 1 - (k + 1))),
        ∃ F : Set (CTorus 3 3 N₁ R.m₁ (k + 1)) →
            RawData 3 3 (N₁ * 3 ^ R.m₁) (k + 1) 2 × (Fin 3 → ℂ) → ℂ,
          (∀ X, AnalyticOnNhd ℂ (F X) (expDom (lvTop N₁ R.m₁ k (rhoSep R.m₁))
            (XiCOneReal (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν e) R.r₀)) ∧
          IsLocExp (N := 2) (lvTop N₁ R.m₁ k (rhoSep R.m₁))
            (XiCOneReal (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν e) R.r₀
            (renYs (renCube (lvTop N₁ R.m₁ k (rhoSep R.m₁))
                (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (blockSite k z))))
              (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1
              (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (blockSite k z))))
            (renDY (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1) (3 / 2 * R.κdec)
            (hullConst 3 3 (towerDetRate R.κ) (towerDetConst R.κ) *
              Real.exp (c1 3 3 * Real.log 2) * Real.exp (hullRate 3 3 (towerDetRate R.κ)))
            (renE0θ_det e E z)
            (fun Y q => ∑ X ∈ Finset.univ.filter (fun X : Set (CTorus 3 3 N₁ R.m₁ (k + 1)) =>
                renFibreMap (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1
                  (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (blockSite k z))) X = Y),
              F X q) := by
  have h := R.toG.renE0_fibre_det_at (R.toStepTower.hhull_renDetFibre_toG hR) he het k hk N₁
    h3N hN hν0 (by simpa using hν) β p₁
  unfold StepTowerG.step at h
  rw [rhoSepG_three] at h
  dsimp only [StepTowerTheta.toG_m₁, StepTowerTheta.toG_κ, StepTowerTheta.toG_t,
    StepTowerTheta.toG_BG, StepTowerTheta.toG_r₀, StepTowerTheta.toG_κdec] at h
  have e1 : (R.κ - Real.log 2 - 2 * Real.log ((detDeg 3 3 + 1 : ℕ) : ℝ)) /
      (2 * ((3 : ℕ) : ℝ) * ((3 : ℕ) : ℝ)) = towerDetRate R.κ := by
    unfold towerDetRate; norm_num
  have e2 : ((3 : ℕ) : ℝ) ^ 3 * ((1 / 2 : ℝ) * (2 : ℕ) * covBLogMax 3 3 R.κ /
      (1 - ((detDeg 3 3 + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp R.κ))) = towerDetConst R.κ :=
    StepTower.det_const_eq _ _
  rw [e1, e2] at h
  exact h

/-- **The determinant-only `expE0` statement at every scale.**  This is NOT the physical `expE0`
field of the renormalization input record: the marked energy terms are missing from `E0θ`, and
`renE0θ_det` is only the determinant summand of the new energy function.  What is proved,
unconditionally for `renDetFibreMin ≤ κmin`, is that the determinant summand has the shape of
that field: for every root `z`, a localized expansion over `renYs` at rate `3 κ_dec / 2` and
constant `H′ = hullConst · e^{c₁ log 2} · e^{hullRate}`; and that its value at `ξ = 0` is the
determinant term of the step. -/
theorem expE0_det_scale_of_tower_at {κmin : ℝ} (R : StepTowerTheta κmin)
    (hR : renDetFibreMin ≤ κmin) {e : ℝ} (he : 0 < e)
    (het : e ≤ R.t) (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (h3N : 3 ∣ N₁)
    (hN : 5 < N₁) {ν : ℝ} (hν0 : 0 ≤ ν) (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) (β p₁ : ℝ) :
    ∃ E : ∀ z : Torus 3 (N₁ * 3 ^ R.m₁ * 3 ^ (k + 1 - (k + 1))),
        DetExpansionLocC (R.toStepTower.step k hk N₁ ν β p₁) 1 z (2 * R.t)
          (towerDetRate R.κ) (towerDetConst R.κ),
      (∀ z, renE0θ_det e E z (R.toStepTower.step k hk N₁ ν β p₁).D' 0 =
          -(1 / 2 : ℂ) * ∑ y ∈ (R.toStepTower.step k hk N₁ ν β p₁).blockU z, ∑ i : Fin 2,
            (R.toStepTower.step k hk N₁ ν β p₁).logAC (y, i) (y, i)) ∧
      ∀ z : Torus 3 (N₁ * 3 ^ R.m₁ * 3 ^ (k + 1 - (k + 1))), ∃ term,
        IsLocExp (N := 2) (lvTop N₁ R.m₁ k (rhoSep R.m₁))
          (XiCOneReal (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν e) R.r₀
          (renYs (renCube (lvTop N₁ R.m₁ k (rhoSep R.m₁))
              (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (blockSite k z))))
            (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1
            (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (blockSite k z))))
          (renDY (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1) (3 / 2 * R.κdec)
          (hullConst 3 3 (towerDetRate R.κ) (towerDetConst R.κ) *
            Real.exp (c1 3 3 * Real.log 2) * Real.exp (hullRate 3 3 (towerDetRate R.κ)))
          (renE0θ_det e E z) term := by
  obtain ⟨E, hz, h⟩ := renE0_fibre_det_at R hR he het k hk N₁ h3N hN hν0 hν β p₁
  refine ⟨E, hz, fun z => ?_⟩
  obtain ⟨F, -, hF⟩ := h z
  exact ⟨_, hF⟩

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
              F X q) :=
  renE0_fibre_det_at R hR R.t_pos le_rfl k hk N₁ h3N hN hν0 hν β p₁

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
          (renE0θ_det R.t E z) term :=
  expE0_det_scale_of_tower_at R hR R.t_pos le_rfl k hk N₁ h3N hN hν0 hν β p₁

end Balaban.Inhabited
