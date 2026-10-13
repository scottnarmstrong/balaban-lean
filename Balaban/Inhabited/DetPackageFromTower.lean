/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepTowerScale
public import Balaban.Inhabited.StepOutputConsts
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

* `detTerm_sym_of_formula`, `detTerm_rot_of_formula` (generic transfer): for records with the term
  formula, covariance of the terms and of the regrouped terms under a symmetry of the generated
  group (`L = 3`), and invariance of both under a spin rotation of a datum of the chart.
* `detPackage_fromTower`: at every scale of a shared tower `T : StepTower κmin`, one family
  `z ↦ E z` of records carrying the sum identity, the bound at the hull rate, the anchor, the
  locality, the lattice covariance and the rotation invariance.  Nothing is assumed beyond `T`
  and the scale conditions.
* `towerDetHullRate_ge`: the hull rate is at least `3 κ_dec / 2` once `κmin` is at least
  `detHullThreshold`.
* `detPackage_instance`: the package at `k = 1`, `N₁ = 6`.

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

/-! ### Generic transfer lemmas for records with the term formula -/

section Transfer

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ} {S : StepSetting d L N₁ m₁ k N ϱ}
  {m₀ : ℕ} {eps : ℝ}

open Classical in
/-- **Covariance of the terms and of the regrouped terms for records with the term formula.**
For `L = 3`, `L ^ m₀ ∣ N₁`, a level top set and `σ` in the generated group there is a lattice
symmetry `Sy` preserving the chart such that any records `E` (root `z`) and `E'` (root
`rootAct σ z`), both with the term formula at the weight `ρ`, satisfy
`E'.term (Sy.sym D) (σ • T) = E.term D T` and
`E'.detGrouped (Sy.sym D) (σ '' X) = E.detGrouped D X`. -/
theorem detTerm_sym_of_formula (hG : IsLevel S.G' (k + 1)) (hL : L = 3) (hN : L ^ m₀ ∣ N₁)
    {σ : Equiv.Perm (CTorus d L N₁ m₁ (k + 1))}
    (h : GenSymm L N₁ m₁ (k + 1) (k + 1) m₀ σ) (ρ : ℝ) :
    ∃ Sy : LatSymm S.G' S.G' σ,
      (∀ D : BgData S.G' N, XiCData S.G' S.a S.ν (k + 1) 1 eps D →
        XiCData S.G' S.a S.ν (k + 1) 1 eps (Sy.sym D)) ∧
      ∀ {z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))} {κ₁ c₁ κ₂ c₂ : ℝ}
        (E : DetExpansionLocC S m₀ z eps κ₁ c₁)
        (E' : DetExpansionLocC S m₀ (rootAct σ z) eps κ₂ c₂),
        (∀ D T, E.term D T = ∑ y ∈ S.blockU z, detActivityBg m₀ S.a S.a₁ S.ν ρ D y T) →
        (∀ D T, E'.term D T =
          ∑ y ∈ S.blockU (rootAct σ z), detActivityBg m₀ S.a S.a₁ S.ν ρ D y T) →
        (∀ (D : BgData S.G' N) T, E'.term (Sy.sym D) (cubeAct σ T) = E.term D T) ∧
        ∀ (D : BgData S.G' N) (X : Set (CTorus d L N₁ m₁ (k + 1))),
          E'.detGrouped (Sy.sym D) (σ '' X) = E.detGrouped D X := by
  obtain ⟨Sy, hSy⟩ := sum_detActivityBg_sym_genSymm S hG hN h
  refine ⟨Sy, fun D hD => xiCData_sym Sy hD, fun {z} _ _ _ _ E E' hE hE' => ?_⟩
  have ht : ∀ (D : BgData S.G' N) T, E'.term (Sy.sym D) (cubeAct σ T) = E.term D T := by
    intro D T
    rw [hE', hE]
    exact hSy ρ D z T
  exact ⟨ht, fun D X => detCollarGrouped_comp hL hN h (ht D) X⟩

variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
  {c BG κ Kc Cx c₂ BG₂ δ₁ δc : ℝ}

/-- **Invariance of the terms and of the regrouped terms under a spin rotation of the datum.**
For a record `E` with the term formula at the weight `rho4 d L N BG κ`, `Rᵀ R = 1` and `D` in the
chart: `E.term (D.rot R) T = E.term D T` and `E.detGrouped (D.rot R) X = E.detGrouped D X`. -/
theorem detTerm_rot_of_formula
    (hC : FlCore N S.G' Hm S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (hk : 1 ≤ k) (hδc : 0 ≤ δc)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    {z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))} {κ₁ c₁ : ℝ}
    (E : DetExpansionLocC S m₀ z eps κ₁ c₁)
    (hE : ∀ D T, E.term D T =
      ∑ y ∈ S.blockU z, detActivityBg m₀ S.a S.a₁ S.ν (rho4 d L N BG κ) D y T)
    {R : Matrix (Fin N) (Fin N) ℂ} (hR : Rᵀ * R = 1) {D : BgData S.G' N}
    (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps D) :
    (∀ T, E.term (D.rot R) T = E.term D T) ∧
      ∀ X : Set (CTorus d L N₁ m₁ (k + 1)), E.detGrouped (D.rot R) X = E.detGrouped D X := by
  have ht : ∀ T, E.term (D.rot R) T = E.term D T := fun T => by
    rw [hE, hE]
    exact Finset.sum_congr rfl fun y _ => detActivityBg_rot hC hk hδc hMX hsm hdm hα hR hD y T
  refine ⟨ht, fun X => ?_⟩
  unfold DetExpansionLocC.detGrouped detCollarGrouped
  exact Finset.sum_congr rfl fun T _ => ht T

end Transfer

/-! ### The rate -/

/-- The determinant rate `(κ - log 2 - 2 log(detDeg 3 3 + 1)) / 18` of the tower. -/
noncomputable abbrev towerDetRate (κ : ℝ) : ℝ :=
  (κ - Real.log 2 - 2 * Real.log ((detDeg 3 3 + 1 : ℕ) : ℝ)) / 18

/-- The determinant constant `27 covBLogMax / (1 - (detDeg 3 3 + 1)² · 2 / e^κ)` of the tower. -/
noncomputable abbrev towerDetConst (κ : ℝ) : ℝ :=
  27 * covBLogMax 3 3 κ / (1 - ((detDeg 3 3 + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp κ))

/-- The threshold on `κmin` for the hull rate: `18 (1 + B)(3 κ_dec / 2 + c₁ log 2) + log 2 +
2 log(detDeg 3 3 + 1)` with `B = c_G c₁ = 60750`, `c₁ = 3375` and
`κ_dec = 100 (a_Ent + 1 + 3375 + 10)` (the value of the tower, with `κ₀ = a_Ent + 1`). -/
noncomputable def detHullThreshold : ℝ :=
  18 * 60751 * (3 / 2 * (100 * (aEnt 3 3 + 1 + 3375 + 10)) + 3375 * Real.log 2) +
    Real.log 2 + 2 * Real.log ((detDeg 3 3 + 1 : ℕ) : ℝ)

theorem collarB_three : collarB 3 3 = 60750 := by
  unfold collarB; rw [cG_three, c1_three]; norm_num

/-- **The hull rate in terms of the rate.**  If `κ ≥ 18 (1 + B)(κ_out + c₁ log 2) + log 2 +
2 log(detDeg + 1)` then `κ_out ≤ hullRate 3 3 ((κ - log 2 - 2 log(detDeg + 1))/18)`. -/
theorem hullRate_ge_of_le {κ kout : ℝ}
    (h : 18 * 60751 * (kout + 3375 * Real.log 2) + Real.log 2 +
      2 * Real.log ((detDeg 3 3 + 1 : ℕ) : ℝ) ≤ κ) :
    kout ≤ hullRate 3 3 (towerDetRate κ) := by
  unfold hullRate
  rw [collarB_three, c1_three]
  have : kout + 3375 * Real.log 2 ≤ towerDetRate κ / (1 + 60750) := by
    rw [le_div_iff₀ (by norm_num)]
    unfold towerDetRate
    rw [le_div_iff₀ (by norm_num)]
    linarith
  linarith

/-- **The threshold for the hull rate.**  For `κmin ≥ detHullThreshold`, every tower
`T : StepTower κmin` has hull rate at least `κ_out = 3 κ_dec / 2`. -/
theorem towerDetHullRate_ge {κmin : ℝ} (T : StepTower κmin) (h : detHullThreshold ≤ κmin) :
    3 * T.κdec / 2 ≤ hullRate 3 3 (towerDetRate T.κ) := by
  have := hullRate_ge_of_le (κ := T.κ) (kout := 3 * T.κdec / 2) (by
    unfold detHullThreshold at h
    have := T.κmin_le
    have e : 3 * T.κdec / 2 = 3 / 2 * (100 * (aEnt 3 3 + 1 + 3375 + 10)) := by
      rw [T.κdec_eq, T.κ0_eq, c1_three]; ring
    rw [e]; linarith)
  exact this

/-! ### The package -/

section Package

variable {κmin : ℝ}

theorem towerDetRate_nonneg (T : StepTower κmin) : 0 ≤ towerDetRate T.κ := by
  have h1 := T.det_rate
  have h2 : 0 ≤ T.κ' := by
    rw [T.κ'_eq]; have := T.κ0_nonneg; have := T.κdec_lower; linarith
  exact le_trans h2 h1

theorem towerDetConst_nonneg (T : StepTower κmin) : 0 ≤ towerDetConst T.κ := by
  have hκ : 0 ≤ T.κ := by
    have h := T.κ_lower
    have h0 := T.κ0_nonneg
    have h1 := T.κdec_lower
    have : (0 : ℝ) ≤ 4 * ((3 : ℕ) : ℝ) * (((2 * 3 + 1) ^ 3 : ℕ) : ℝ) * T.κdec := by
      have : (0 : ℝ) ≤ T.κdec := by linarith
      positivity
    linarith
  have h1 := one_le_covBLog 3 (L := 3) (by norm_num) (a := 2) (by norm_num) (2 / (3 : ℝ) ^ 2) hκ
  have h2 := T.det_z
  unfold towerDetConst covBLogMax
  exact div_nonneg (by positivity) (by linarith)

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
  obtain ⟨hE0, -⟩ := detExpansionLocC_scale_fromTower T k hk N₁ h3N hN5 hν0 hν β p₁
  choose E hE using hE0
  have hN : (3 : ℕ) ^ 1 ∣ N₁ := by simpa using h3N
  have hSD := dgSetting_lv (N₁ := N₁) (k := k) T.m₁_four hN5 hν0 hν
  have hHB := bgHyp_lv (k := k) T.m₁ hν0 hν
  have hC : FlCore 2 (lvTop N₁ T.m₁ k (rhoSep T.m₁)) (lvLow N₁ T.m₁ k (rhoSep T.m₁)) 1 ν T.c
      T.BG T.κ T.t (levelKc 3 3) (Cchi 3 3) T.c₂ T.BG₂ T.t :=
    flCore_level_transfer (Classical.choice T.core) hSD (opSetting_lv T.m₁_four hN5 hν0 hν)
      (isLevel_lvLow hk) isLevel_lvTop hHB
  have hδc : 0 ≤ T.δc := by
    have : 0 ≤ decDomMargin 3 3 2 T.BG T.κ (xiC1 3 * T.t) := by
      have : 0 < K4 3 3 2 T.BG T.κ := K4_pos hC.hS.fam.2.1 (by norm_num)
      have := one_le_xiC1 3
      have := T.t_pos
      unfold decDomMargin; positivity
    linarith [T.dom_margin]
  have h3 : 3 ≤ 3 ^ (1 + T.m₁) := by
    calc 3 = 3 ^ 1 := by norm_num
      _ ≤ 3 ^ (1 + T.m₁) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hrate := towerDetRate_nonneg T
  have hconst := towerDetConst_nonneg T
  refine ⟨E, hE, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z D hD
    exact (E z).detGrouped_sum hD
  · intro z D hD X
    exact (E z).detGrouped_bound (by norm_num) hN hconst hrate hD X
  · intro z D hD X hX
    exact (E z).detGrouped_anchor (by norm_num) hN hD hX
  · intro z D D₂ hD hD₂ X h
    exact (E z).detGrouped_local (by norm_num) hN h3 hD hD₂ h
  · intro σ h
    obtain ⟨Sy, hSy, hT⟩ := detTerm_sym_of_formula (S := T.step k hk N₁ ν β p₁)
      (m₀ := 1) (eps := T.t) isLevel_lvTop rfl hN h (rho4 3 3 2 T.BG T.κ)
    exact ⟨Sy, hSy, fun z => hT (E z) (E (rootAct σ z)) (hE z) (hE (rootAct σ z))⟩
  · intro z D hD R hR
    exact detTerm_rot_of_formula (S := T.step k hk N₁ ν β p₁) (m₀ := 1) hC hk hδc
      T.large_block T.δc_small T.dom_margin T.coer_margin (E z) (hE z) hR hD
  · intro D hD Q hQ
    exact xiCData_rot hQ hD

/-- **Non-vacuity at one scale** (`k = 1`, `N₁ = 6`, `ν = 0`, `β = 0`, `p₁ = 1`): for every
`κmin` there is a tower `T`, a datum `D` of the chart at the step, and a family of records with the
term formula for which the sum identity and the bound at the hull rate hold at `D`. -/
theorem detPackage_instance (κmin : ℝ) :
    ∃ T : StepTower κmin, ∃ D : BgData (T.step 1 le_rfl 6 0 0 1).G' 2,
      XiCData (T.step 1 le_rfl 6 0 0 1).G' (compWeight 3 1) 0 (1 + 1) 1 T.t D ∧
      ∃ E : ∀ z : Torus 3 (6 * 3 ^ T.m₁ * 3 ^ (1 + 1 - (1 + 1))),
          DetExpansionLocC (T.step 1 le_rfl 6 0 0 1) 1 z T.t (towerDetRate T.κ)
            (towerDetConst T.κ),
        (∀ z D T', (E z).term D T' = ∑ y ∈ (T.step 1 le_rfl 6 0 0 1).blockU z,
          detActivityBg 1 (compWeight 3 1) 1 0 (rho4 3 3 2 T.BG T.κ) D y T') ∧
        ∀ z (X : Set (CTorus 3 3 6 T.m₁ (1 + 1))),
          ‖(E z).detGrouped D X‖ ≤ hullConst 3 3 (towerDetRate T.κ) (towerDetConst T.κ) *
            Real.exp (-hullRate 3 3 (towerDetRate T.κ) * sizeJ 1 (1 + 1) X) := by
  obtain ⟨T⟩ := exists_stepTower κmin
  obtain ⟨βray, -, ⟨hS⟩⟩ := T.scale_instance
  obtain ⟨E, hE, -, hb, -⟩ := detPackage_fromTower T 1 le_rfl 6 (by norm_num) (by norm_num)
    (ν := 0) le_rfl (by norm_num) 0 1
  exact ⟨T, _, hS.xi, E, hE, fun z X => hb z _ hS.xi X⟩

end Package

end Balaban.Inhabited
