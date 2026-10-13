/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepTowerScale
public import Balaban.Inhabited.DetPackageFromTowerG
public import Balaban.Inhabited.StepOutputConsts
public import Balaban.Fluctuation.DetRateGeneral
public import Balaban.Fluctuation.DetCollarHullSymm
public import Balaban.Fluctuation.DetRotation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# The determinant part of the zero-class step output at the shared tower

The determinant terms of the zero-class step are landed in four pieces, each with its own
existential record: the expansion record at the shared tower (`detExpansionLocC_scale_fromTower`),
regrouping on collar hulls with bound, anchor and locality (`DetCollarHull`), covariance under the
lattice symmetries (`DetSymmGroup`, `DetCollarHullSymm`) and invariance under spin rotations
(`DetRotation`).  All records have the same term formula, the sum of `detActivityBg` over the
root block, so the properties of the activities transfer to every record with that formula.

* `detTerm_sym_of_formula`, `detTerm_rot_of_formula` (generic transfer, now in
  `DetPackageFromTowerG`): for records with the term formula, covariance of the terms and of the
  regrouped terms under a symmetry of the generated group (`L = 3`), and invariance of both under a
  spin rotation of a datum of the chart.
* `detPackage_fromTower`: at every scale of a shared tower `T : StepTower κmin`, one family
  `z ↦ E z` of records carrying the sum identity, the bound at the hull rate, the anchor, the
  locality, the lattice covariance and the rotation invariance.  Nothing is assumed beyond `T`
  and the scale conditions.  It is the case `q = 1` of `StepTowerG.detPackage_fromTowerG`
  (through `StepTower.toG`, `detCollarHullC_one` and `detGroupedC_one`).
* `towerDetHullRate_ge`: the hull rate is at least `3 κ_dec / 2` once `κmin` is at least
  `detHullThreshold`.

## What is not proved

This is the zero class and chart data only.  The inclusion of the class domain in the chart and the
class symmetry clause are not proved here.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep
  Balaban.Localization.DecEquiv Matrix

/-! ### The rate -/

/-- The determinant rate `(κ - log 2 - 2 log(detDeg 3 3 + 1)) / 18` of the tower. -/
noncomputable abbrev towerDetRate (κ : ℝ) : ℝ :=
  (κ - Real.log 2 - 2 * Real.log ((detDeg 3 3 + 1 : ℕ) : ℝ)) / 18

/-- The determinant constant `27 covBLogMax / (1 - (detDeg 3 3 + 1)² · 2 / e^κ)` of the tower. -/
noncomputable abbrev towerDetConst (κ : ℝ) : ℝ :=
  27 * covBLogMax 3 3 κ / (1 - ((detDeg 3 3 + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp κ))

/-- The threshold on `κmin` for the hull rate: `18 (1 + B)(3 κ_dec / 2 + c₁ log 2) + log 2 +
2 log(detDeg 3 3 + 1)` with `B = c_G c₁ = 60750`, `c₁ = 3375` and
`κ_dec = 100 (a_Ent + 1 + 3375 + 10)` (the value of the tower, with `κ₀ = a_Ent + 2`, retuned from `a_Ent + 1` per `notes/phase1/TOWERJOIN.md` §1). -/
noncomputable def detHullThreshold : ℝ :=
  18 * 60751 * (3 / 2 * (100 * (aEnt 3 3 + 2 + 3375 + 10)) + 3375 * Real.log 2) +
    Real.log 2 + 2 * Real.log ((detDeg 3 3 + 1 : ℕ) : ℝ)

/-- The general rate at `d = L = 3` is the landed `towerDetRate`. -/
theorem _root_.Balaban.Fluctuation.detRateG_three (κ : ℝ) : detRateG 3 3 κ = towerDetRate κ := by
  unfold detRateG towerDetRate
  norm_num

theorem collarB_three : collarB 3 3 = 60750 := by
  unfold collarB; rw [cG_three, c1_three]; norm_num

/-- **The hull rate in terms of the rate.**  If `κ ≥ 18 (1 + B)(κ_out + c₁ log 2) + log 2 +
2 log(detDeg + 1)` then `κ_out ≤ hullRate 3 3 ((κ - log 2 - 2 log(detDeg + 1))/18)`.  The
instance `d = L = 3` of `hullRate_ge_general`. -/
theorem hullRate_ge_of_le {κ kout : ℝ}
    (h : 18 * 60751 * (kout + 3375 * Real.log 2) + Real.log 2 +
      2 * Real.log ((detDeg 3 3 + 1 : ℕ) : ℝ) ≤ κ) :
    kout ≤ hullRate 3 3 (towerDetRate κ) := by
  rw [← detRateG_three]
  refine hullRate_ge_general (by norm_num) (by norm_num) ?_
  rw [collarB_three, c1_three]
  norm_num
  push_cast at h ⊢
  linarith

/-- The landed `hullRate_ge_of_le` as the instance `d = L = 3` of `hullRate_ge_general`. -/
theorem _root_.Balaban.Fluctuation.hullRate_ge_of_le_of_general {κ kout : ℝ}
    (h : 18 * 60751 * (kout + 3375 * Real.log 2) + Real.log 2 +
      2 * Real.log ((detDeg 3 3 + 1 : ℕ) : ℝ) ≤ κ) :
    kout ≤ hullRate 3 3 (towerDetRate κ) :=
  hullRate_ge_of_le h

/-- **The threshold for the hull rate.**  For `κmin ≥ detHullThreshold`, every tower
`T : StepTower κmin` has hull rate at least `κ_out = 3 κ_dec / 2`. -/
theorem towerDetHullRate_ge {κmin : ℝ} (T : StepTower κmin) (h : detHullThreshold ≤ κmin) :
    3 * T.κdec / 2 ≤ hullRate 3 3 (towerDetRate T.κ) := by
  have := hullRate_ge_of_le (κ := T.κ) (kout := 3 * T.κdec / 2) (by
    unfold detHullThreshold at h
    have := T.κmin_le
    have e : 3 * T.κdec / 2 = 3 / 2 * (100 * (aEnt 3 3 + 2 + 3375 + 10)) := by
      rw [T.κdec_eq, T.κ0_eq, c1_three]; ring
    rw [e]; linarith)
  exact this

/-! ### The package -/

section Package

variable {κmin : ℝ}

theorem towerDetRate_nonneg (T : StepTower κmin) : 0 ≤ towerDetRate T.κ := by
  have h := T.toG.detRate_nonneg
  unfold towerDetRate
  norm_num at h ⊢
  exact h

theorem towerDetConst_nonneg (T : StepTower κmin) : 0 ≤ towerDetConst T.κ := by
  have h := T.toG.detConst_nonneg
  unfold towerDetConst
  rw [StepTower.det_const_eq] at h
  exact h

open Classical in
/-- **The determinant package of the zero-class step at the shared tower.**  For a tower
`T : StepTower κmin`, a scale `k ≥ 1`, a torus with `3 ∣ N₁`, `5 < N₁`, a mass `ν` with
`0 ≤ ν`, `ν 3^{2(k+1)} ≤ 1` and any `β`, `p₁`, there is ONE family `z ↦ E z` of records at the
step `T.step k hk N₁ ν β p₁`, with the term formula at the constants of `T`, such that for chart
data `D` (`XiCData … T.t D`):

* sum: the regrouped terms add up to the root trace;
* bound: `‖(E z).detGrouped D X‖ ≤ hullConst 3 3 rate const · exp (-hullRate 3 3 rate · sizeJ X)`;
* anchor: a nonzero regrouped term sits on a polymer domain containing the root box;
* locality: data of the chart agreeing on `X` have the same regrouped term at `X`;
* lattice covariance: for `σ` in the generated group there is a lattice symmetry preserving the
  chart with `(E (rootAct σ z)).detGrouped (Sy.sym D) (σ '' X) = (E z).detGrouped D X`;
* rotation invariance: for `Rᵀ R = 1` and `D` in the chart the terms and the regrouped terms are
  unchanged under `D.rot R`; for real orthogonal `Q` the rotated datum is again in the chart.

No hypothesis beyond `T` and the scale conditions. -/
theorem detPackage_fromTower (T : StepTower κmin)
    (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (h3N : 3 ∣ N₁) (hN5 : 5 < N₁) {ν : ℝ}
    (hν0 : 0 ≤ ν) (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) (β p₁ : ℝ) :
    ∃ E : ∀ z : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))),
        DetExpansionLocC (T.step k hk N₁ ν β p₁) 1 z T.t (towerDetRate T.κ)
          (towerDetConst T.κ),
      (∀ z D T', (E z).term D T' = ∑ y ∈ (T.step k hk N₁ ν β p₁).blockU z,
        detActivityBg 1 (compWeight 3 1) 1 ν (rho4 3 3 2 T.BG T.κ) D y T') ∧
      (∀ z (D : BgData (T.step k hk N₁ ν β p₁).G' 2),
        XiCData (T.step k hk N₁ ν β p₁).G' (compWeight 3 1) ν (k + 1) 1 T.t D →
        ∑ X ∈ (Finset.univ : Finset (Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁)
            (K := k + 1) 1 (k + 1) Set.univ))).image detCollarHull, (E z).detGrouped D X =
          rootTrace (T.step k hk N₁ ν β p₁).G' (T.step k hk N₁ ν β p₁).a 1 ν
            (unitQ (T.step k hk N₁ ν β p₁).G') (unitP (T.step k hk N₁ ν β p₁).G')
            ((T.step k hk N₁ ν β p₁).blockU z) (fun _ => 1)
            (svec (T.step k hk N₁ ν β p₁).G' (bgFieldC (T.step k hk N₁ ν β p₁).G'
              (T.step k hk N₁ ν β p₁).a ν (bgC0 3 3 2) D))
            (bgMultC (T.step k hk N₁ ν β p₁).G' (T.step k hk N₁ ν β p₁).a ν (bgC0 3 3 2) D)) ∧
      (∀ z (D : BgData (T.step k hk N₁ ν β p₁).G' 2),
        XiCData (T.step k hk N₁ ν β p₁).G' (compWeight 3 1) ν (k + 1) 1 T.t D →
        ∀ X : Set (CTorus 3 3 N₁ T.m₁ (k + 1)),
          ‖(E z).detGrouped D X‖ ≤ hullConst 3 3 (towerDetRate T.κ) (towerDetConst T.κ) *
            Real.exp (-hullRate 3 3 (towerDetRate T.κ) * sizeJ 1 (k + 1) X)) ∧
      (∀ z (D : BgData (T.step k hk N₁ ν β p₁).G' 2),
        XiCData (T.step k hk N₁ ν β p₁).G' (compWeight 3 1) ν (k + 1) 1 T.t D →
        ∀ X : Set (CTorus 3 3 N₁ T.m₁ (k + 1)), (E z).detGrouped D X ≠ 0 →
          IsPolyDom 1 (k + 1) X ∧
            box (rootCube (m₀ := 1) (K := k + 1) z).1 (cellSide 3 1 T.m₁ (k + 1)) ⊆ X) ∧
      (∀ z (D D₂ : BgData (T.step k hk N₁ ν β p₁).G' 2),
        XiCData (T.step k hk N₁ ν β p₁).G' (compWeight 3 1) ν (k + 1) 1 T.t D →
        XiCData (T.step k hk N₁ ν β p₁).G' (compWeight 3 1) ν (k + 1) 1 T.t D₂ →
        ∀ X : Set (CTorus 3 3 N₁ T.m₁ (k + 1)),
          (∀ v ∈ X, D.Ψ v = D₂.Ψ v ∧ D.h v = D₂.h v) →
          (E z).detGrouped D X = (E z).detGrouped D₂ X) ∧
      (∀ {σ : Equiv.Perm (CTorus 3 3 N₁ T.m₁ (k + 1))},
        GenSymm 3 N₁ T.m₁ (k + 1) (k + 1) 1 σ →
        ∃ Sy : LatSymm (T.step k hk N₁ ν β p₁).G' (T.step k hk N₁ ν β p₁).G' σ,
          (∀ D : BgData (T.step k hk N₁ ν β p₁).G' 2,
            XiCData (T.step k hk N₁ ν β p₁).G' (compWeight 3 1) ν (k + 1) 1 T.t D →
            XiCData (T.step k hk N₁ ν β p₁).G' (compWeight 3 1) ν (k + 1) 1 T.t (Sy.sym D)) ∧
          ∀ z, (∀ (D : BgData (T.step k hk N₁ ν β p₁).G' 2) T',
              (E (rootAct σ z)).term (Sy.sym D) (cubeAct σ T') = (E z).term D T') ∧
            ∀ (D : BgData (T.step k hk N₁ ν β p₁).G' 2)
              (X : Set (CTorus 3 3 N₁ T.m₁ (k + 1))),
              (E (rootAct σ z)).detGrouped (Sy.sym D) (σ '' X) = (E z).detGrouped D X) ∧
      (∀ z (D : BgData (T.step k hk N₁ ν β p₁).G' 2),
        XiCData (T.step k hk N₁ ν β p₁).G' (compWeight 3 1) ν (k + 1) 1 T.t D →
        ∀ {R : Matrix (Fin 2) (Fin 2) ℂ}, Rᵀ * R = 1 →
          (∀ T', (E z).term (D.rot R) T' = (E z).term D T') ∧
          ∀ X : Set (CTorus 3 3 N₁ T.m₁ (k + 1)),
            (E z).detGrouped (D.rot R) X = (E z).detGrouped D X) ∧
      (∀ (D : BgData (T.step k hk N₁ ν β p₁).G' 2),
        XiCData (T.step k hk N₁ ν β p₁).G' (compWeight 3 1) ν (k + 1) 1 T.t D →
        ∀ {Q : Matrix (Fin 2) (Fin 2) ℝ}, Qᵀ * Q = 1 →
          XiCData (T.step k hk N₁ ν β p₁).G' (compWeight 3 1) ν (k + 1) 1 T.t
            (D.rot (cmat Q))) := by
  classical
  have hN : (3 : ℕ) ^ 1 ∣ N₁ := by simpa using h3N
  have h := T.toG.detPackage_fromTowerG (q := 1) rfl k hk N₁ h3N hN5 hν0 (by simpa using hν) β p₁
  unfold StepTowerG.step at h
  rw [rhoSepG_three] at h
  dsimp only [StepTower.toG_m₁, StepTower.toG_κ, StepTower.toG_t, StepTower.toG_BG,
    StepTower.toG_δ] at h
  have e1 : (T.κ - Real.log 2 - 2 * Real.log ((detDeg 3 3 + 1 : ℕ) : ℝ)) /
      (2 * ((3 : ℕ) : ℝ) * ((3 : ℕ) : ℝ)) = towerDetRate T.κ := by
    unfold towerDetRate; norm_num
  have e2 : ((3 : ℕ) : ℝ) ^ 3 * ((1 / 2 : ℝ) * (2 : ℕ) * covBLogMax 3 3 T.κ /
      (1 - ((detDeg 3 3 + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp T.κ))) = towerDetConst T.κ :=
    StepTower.det_const_eq _ _
  rw [e1, e2] at h
  have e3 : (detCollarHullC (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) (m₀ := 1) 1) =
      detCollarHull := funext fun X => detCollarHullC_one hN X
  obtain ⟨E, hE, hsum, hbd, han, hloc, hcov, hrot, hxi⟩ := h
  have hC1 : ∀ z D X, (E z).detGroupedC 1 D X = (E z).detGrouped D X :=
    fun z D X => (E z).detGroupedC_one hN D X
  refine ⟨E, hE, ?_, ?_, ?_, ?_, ?_, ?_, hxi⟩
  · intro z D hD
    calc _ = ∑ X ∈ (Finset.univ : Finset (Finset (CubeB (d := 3) (L := 3) (N₁ := N₁)
          (m₁ := T.m₁) (K := k + 1) 1 (k + 1) Set.univ))).image (detCollarHullC 1),
          (E z).detGroupedC 1 D X := by
          rw [e3]; exact Finset.sum_congr rfl fun X _ => (hC1 z D X).symm
      _ = _ := hsum z D hD
  · intro z D hD X
    exact le_of_eq_of_le (congrArg norm (hC1 z D X).symm) (hbd z D hD X)
  · intro z D hD X hX
    exact han z D hD X (fun h0 => hX ((hC1 z D X).symm.trans h0))
  · intro z D D₂ hD hD₂ X hX
    exact (hC1 z D X).symm.trans ((hloc z D D₂ hD hD₂ X hX).trans (hC1 z D₂ X))
  · intro σ hσ
    obtain ⟨Sy, hSy, hc⟩ := hcov hσ
    refine ⟨Sy, hSy, fun z => ⟨(hc z).1, fun D X => ?_⟩⟩
    exact (hC1 _ _ _).symm.trans (((hc z).2 D X).trans (hC1 z D X))
  · intro z D hD R hR
    obtain ⟨h1, h2⟩ := hrot z D hD hR
    exact ⟨h1, fun X => (hC1 _ _ _).symm.trans ((h2 X).trans (hC1 z D X))⟩

end Package

end Balaban.Inhabited
