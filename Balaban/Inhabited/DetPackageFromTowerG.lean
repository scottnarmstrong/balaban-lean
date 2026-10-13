/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.DetOutputTermsWitnessG
public import Balaban.Inhabited.StepScaleDataG
public import Balaban.Inhabited.StepTowerGScalars
public import Balaban.Fluctuation.DetCollarCenteredFibre
public import Balaban.Fluctuation.DetSymmGroup
public import Balaban.Fluctuation.DetRotation
public import Balaban.Fluctuation.InteractionSymmRot
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# The determinant package of one step at the general tower, odd block size

For `T : StepTowerG d L N κmin` and odd `L = 2 q + 1`, at every scale of the tower one family
`z ↦ E z` of records `DetExpansionLocC` carrying the sum identity, the bound at the hull rate, the
anchor, the locality, the lattice covariance and the rotation invariance, all for the regrouping
along the centred collar hull `detCollarHullC q`.  The fixed `d = L = 3`, `N = 2` statement
`detPackage_fromTower` is the case `q = 1` (`detCollarHullC_three`, `detGroupedC_one`).

* `detTerm_symC_of_formula`, `detTerm_sym_of_formula`, `detTerm_rot_of_formula`,
  `detTerm_rotC_of_formula`: transfer of covariance and of rotation invariance to every record with
  the term formula (the first and the third landed earlier in `DetPackageFromTower`).
* `StepTowerG.detRate_nonneg`, `StepTowerG.detConst_nonneg`: the rate and the constant are
  nonnegative.
* `StepTowerG.detPackage_fromTowerG`: the package.
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
/-- **Covariance of the terms and of the centred regrouped terms for records with the term
formula.**  For `L = 2 q + 1`, `L ^ m₀ ∣ N₁`, a level top set and `σ` in the generated group there
is a lattice symmetry `Sy` preserving the chart such that any records `E` (root `z`) and `E'`
(root `rootAct σ z`), both with the term formula at the weight `ρ`, satisfy
`E'.term (Sy.sym D) (σ • T) = E.term D T` and
`E'.detGroupedC q (Sy.sym D) (σ '' X) = E.detGroupedC q D X`. -/
theorem detTerm_symC_of_formula (hG : IsLevel S.G' (k + 1)) {q : ℕ} (hL : L = 2 * q + 1)
    (hN : L ^ m₀ ∣ N₁) {σ : Equiv.Perm (CTorus d L N₁ m₁ (k + 1))}
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
          E'.detGroupedC q (Sy.sym D) (σ '' X) = E.detGroupedC q D X := by
  obtain ⟨Sy, hSy⟩ := sum_detActivityBg_sym_genSymm S hG hN h
  refine ⟨Sy, fun D hD => xiCData_sym Sy hD, fun {z} _ _ _ _ E E' hE hE' => ?_⟩
  have ht : ∀ (D : BgData S.G' N) T, E'.term (Sy.sym D) (cubeAct σ T) = E.term D T := by
    intro D T
    rw [hE', hE]
    exact hSy ρ D z T
  exact ⟨ht, fun D X => detCollarGroupedC_comp hL hN h (ht D) X⟩

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
  obtain ⟨Sy, hSy, hT⟩ := detTerm_symC_of_formula (m₀ := m₀) (eps := eps) hG
    (q := 1) (by omega) hN h ρ
  refine ⟨Sy, hSy, fun {z} {κ₁ c₁ κ₂ c₂} E E' hE hE' => ?_⟩
  obtain ⟨h1, h2⟩ := hT E E' hE hE'
  refine ⟨h1, fun D X => ?_⟩
  rw [← E'.detGroupedC_one hN, ← E.detGroupedC_one hN]
  exact h2 D X

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

/-- **Invariance of the centred regrouped terms under a spin rotation of the datum**: the second
clause of `detTerm_rot_of_formula` for `detGroupedC q`. -/
theorem detTerm_rotC_of_formula
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
    (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps D) (q : ℕ) :
    ∀ X : Set (CTorus d L N₁ m₁ (k + 1)), E.detGroupedC q (D.rot R) X = E.detGroupedC q D X := by
  have ht := (detTerm_rot_of_formula hC hk hδc hMX hsm hdm hα E hE hR hD).1
  intro X
  unfold DetExpansionLocC.detGroupedC detCollarGroupedC
  exact Finset.sum_congr rfl fun T _ => ht T

end Transfer

/-! ### The package -/

section Package

variable {d L N : ℕ} [NeZero L] {κmin : ℝ}

/-- The rate of the general determinant package is nonnegative. -/
theorem StepTowerG.detRate_nonneg (T : StepTowerG d L N κmin) :
    0 ≤ (T.κ - Real.log 2 - 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) / (2 * d * L) := by
  have h2 : 0 ≤ T.κ' := T.marks_hκ'
  exact le_trans h2 T.det_rate

/-- The constant of the general determinant package is nonnegative. -/
theorem StepTowerG.detConst_nonneg (T : StepTowerG d L N κmin) :
    0 ≤ (L : ℝ) ^ d * ((1 / 2 : ℝ) * N * covBLogMax d L T.κ /
      (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp T.κ))) := by
  have hκ : 0 ≤ T.κ := by
    have h := T.κ_lower
    have h1 := T.marks_κdec_nonneg
    have : (0 : ℝ) ≤ 4 * (d : ℝ) * (((2 * L + 1) ^ d : ℕ) : ℝ) * T.κdec := by positivity
    linarith
  have hL1 : 1 ≤ L := le_trans (by norm_num) T.hL
  have h1 := one_le_covBLog d hL1 (a := 2) (by norm_num) (2 / (L : ℝ) ^ 2) hκ
  have h2 := T.det_z
  unfold covBLogMax
  exact mul_nonneg (by positivity) (div_nonneg (by positivity) (by linarith))

open Classical in
/-- **The determinant package of one step at the general tower, odd block size.**  For a tower
`T : StepTowerG d L N κmin`, odd `L = 2 q + 1`, a scale `k ≥ 1`, a torus with `L ∣ N₁`, `5 < N₁`
and a mass `ν` with `0 ≤ ν`, `ν L^{2(k+1)} ≤ 1` and any `β`, `p₁`, there is ONE family
`z ↦ E z` of records at the step `T.step k hk N₁ ν β p₁`, with the term formula at the constants
of `T`, such that for chart data `D` (`XiCData … T.t D`):

* sum: the regrouped terms (along `detCollarHullC q`) add up to the root trace;
* bound: `‖(E z).detGroupedC q D X‖ ≤ hullConst d L rate const · exp (-hullRate d L rate · sizeJ X)`;
* anchor: a nonzero regrouped term sits on a polymer domain containing the root box;
* locality: data of the chart agreeing on `X` have the same regrouped term at `X`;
* lattice covariance: for `σ` in the generated group there is a lattice symmetry preserving the
  chart with `(E (rootAct σ z)).detGroupedC q (Sy.sym D) (σ '' X) = (E z).detGroupedC q D X`;
* rotation invariance: for `Rᵀ R = 1` and `D` in the chart the terms and the regrouped terms are
  unchanged under `D.rot R`; for real orthogonal `Q` the rotated datum is again in the chart.

The rate is `(κ - log 2 - 2 log (detDeg d L + 1)) / (2 d L)` and the constant
`L^d · ½ N covBLogMax d L κ / (1 - (detDeg d L + 1)² · 2 / e^κ)`.  No hypothesis beyond `T` and
the scale conditions. -/
theorem StepTowerG.detPackage_fromTowerG (T : StepTowerG d L N κmin) {q : ℕ}
    (hLq : L = 2 * q + 1) (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (hLN : L ∣ N₁)
    (hN5 : 5 < N₁) {ν : ℝ} (hν0 : 0 ≤ ν) (hν : ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1)
    (β p₁ : ℝ) :
    ∃ E : ∀ z : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))),
        DetExpansionLocC (T.step k hk N₁ ν β p₁) 1 z T.t
          ((T.κ - Real.log 2 - 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) / (2 * d * L))
          ((L : ℝ) ^ d * ((1 / 2 : ℝ) * N * covBLogMax d L T.κ /
            (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp T.κ)))),
      (∀ z D T', (E z).term D T' = ∑ y ∈ (T.step k hk N₁ ν β p₁).blockU z,
        detActivityBg 1 (compWeight L 1) 1 ν (rho4 d L N T.BG T.κ) D y T') ∧
      (∀ z (D : BgData (T.step k hk N₁ ν β p₁).G' N),
        XiCData (T.step k hk N₁ ν β p₁).G' (compWeight L 1) ν (k + 1) 1 T.t D →
        ∑ X ∈ (Finset.univ : Finset (Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁)
            (K := k + 1) 1 (k + 1) Set.univ))).image (detCollarHullC q),
          (E z).detGroupedC q D X =
          rootTrace (T.step k hk N₁ ν β p₁).G' (T.step k hk N₁ ν β p₁).a 1 ν
            (unitQ (T.step k hk N₁ ν β p₁).G') (unitP (T.step k hk N₁ ν β p₁).G')
            ((T.step k hk N₁ ν β p₁).blockU z) (fun _ => 1)
            (svec (T.step k hk N₁ ν β p₁).G' (bgFieldC (T.step k hk N₁ ν β p₁).G'
              (T.step k hk N₁ ν β p₁).a ν (bgC0 d L N) D))
            (bgMultC (T.step k hk N₁ ν β p₁).G' (T.step k hk N₁ ν β p₁).a ν (bgC0 d L N) D)) ∧
      (∀ z (D : BgData (T.step k hk N₁ ν β p₁).G' N),
        XiCData (T.step k hk N₁ ν β p₁).G' (compWeight L 1) ν (k + 1) 1 T.t D →
        ∀ X : Set (CTorus d L N₁ T.m₁ (k + 1)),
          ‖(E z).detGroupedC q D X‖ ≤
            hullConst d L
                ((T.κ - Real.log 2 - 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) / (2 * d * L))
                ((L : ℝ) ^ d * ((1 / 2 : ℝ) * N * covBLogMax d L T.κ /
                  (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp T.κ)))) *
              Real.exp (-hullRate d L
                ((T.κ - Real.log 2 - 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) / (2 * d * L)) *
                sizeJ 1 (k + 1) X)) ∧
      (∀ z (D : BgData (T.step k hk N₁ ν β p₁).G' N),
        XiCData (T.step k hk N₁ ν β p₁).G' (compWeight L 1) ν (k + 1) 1 T.t D →
        ∀ X : Set (CTorus d L N₁ T.m₁ (k + 1)), (E z).detGroupedC q D X ≠ 0 →
          IsPolyDom 1 (k + 1) X ∧
            box (rootCube (m₀ := 1) (K := k + 1) z).1 (cellSide L 1 T.m₁ (k + 1)) ⊆ X) ∧
      (∀ z (D D₂ : BgData (T.step k hk N₁ ν β p₁).G' N),
        XiCData (T.step k hk N₁ ν β p₁).G' (compWeight L 1) ν (k + 1) 1 T.t D →
        XiCData (T.step k hk N₁ ν β p₁).G' (compWeight L 1) ν (k + 1) 1 T.t D₂ →
        ∀ X : Set (CTorus d L N₁ T.m₁ (k + 1)),
          (∀ v ∈ X, D.Ψ v = D₂.Ψ v ∧ D.h v = D₂.h v) →
          (E z).detGroupedC q D X = (E z).detGroupedC q D₂ X) ∧
      (∀ {σ : Equiv.Perm (CTorus d L N₁ T.m₁ (k + 1))},
        GenSymm L N₁ T.m₁ (k + 1) (k + 1) 1 σ →
        ∃ Sy : LatSymm (T.step k hk N₁ ν β p₁).G' (T.step k hk N₁ ν β p₁).G' σ,
          (∀ D : BgData (T.step k hk N₁ ν β p₁).G' N,
            XiCData (T.step k hk N₁ ν β p₁).G' (compWeight L 1) ν (k + 1) 1 T.t D →
            XiCData (T.step k hk N₁ ν β p₁).G' (compWeight L 1) ν (k + 1) 1 T.t (Sy.sym D)) ∧
          ∀ z, (∀ (D : BgData (T.step k hk N₁ ν β p₁).G' N) T',
              (E (rootAct σ z)).term (Sy.sym D) (cubeAct σ T') = (E z).term D T') ∧
            ∀ (D : BgData (T.step k hk N₁ ν β p₁).G' N)
              (X : Set (CTorus d L N₁ T.m₁ (k + 1))),
              (E (rootAct σ z)).detGroupedC q (Sy.sym D) (σ '' X) =
                (E z).detGroupedC q D X) ∧
      (∀ z (D : BgData (T.step k hk N₁ ν β p₁).G' N),
        XiCData (T.step k hk N₁ ν β p₁).G' (compWeight L 1) ν (k + 1) 1 T.t D →
        ∀ {R : Matrix (Fin N) (Fin N) ℂ}, Rᵀ * R = 1 →
          (∀ T', (E z).term (D.rot R) T' = (E z).term D T') ∧
          ∀ X : Set (CTorus d L N₁ T.m₁ (k + 1)),
            (E z).detGroupedC q (D.rot R) X = (E z).detGroupedC q D X) ∧
      (∀ (D : BgData (T.step k hk N₁ ν β p₁).G' N),
        XiCData (T.step k hk N₁ ν β p₁).G' (compWeight L 1) ν (k + 1) 1 T.t D →
        ∀ {Q : Matrix (Fin N) (Fin N) ℝ}, Qᵀ * Q = 1 →
          XiCData (T.step k hk N₁ ν β p₁).G' (compWeight L 1) ν (k + 1) 1 T.t
            (D.rot (cmat Q))) := by
  classical
  have hE0 := (detExpansionLocC_scale_of_towerG T.hd T.hL T.hN T.m₁_four T.t_pos
    (Classical.choice T.core) T.large_block T.dom_margin T.coer_margin T.δc_small T.det_z k hk N₁
    hLN hN5 hν0 hν β p₁ T.δ).2
  choose E hE using hE0
  have hN : L ^ 1 ∣ N₁ := by simpa using hLN
  have hq1 : 1 ≤ q := by have := T.hL; omega
  have hC := flCore_stepG (N := N) T.hd T.hL T.m₁_four (Classical.choice T.core) hk hN5 hν0 hν
  have hδc := δc_nonneg_of_flCore T.hd T.t_pos hC T.dom_margin
  have h3 : 3 ≤ L ^ (1 + T.m₁) :=
    calc 3 ≤ L := T.hL
      _ = L ^ 1 := (pow_one L).symm
      _ ≤ L ^ (1 + T.m₁) := Nat.pow_le_pow_right (by have := T.hL; omega) (by omega)
  have hrate := T.detRate_nonneg
  have hconst := T.detConst_nonneg
  refine ⟨E, hE, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z D hD
    exact (E z).detGroupedC_sum q hD
  · intro z D hD X
    exact (E z).detGroupedC_bound (by omega) hN hconst hrate hD X
  · intro z D hD X hX
    exact (E z).detGroupedC_anchor (by omega) hN hD hX
  · intro z D D₂ hD hD₂ X h
    exact (E z).detGroupedC_local hq1 (by have := T.hL; omega) hN h3 hD hD₂ h
  · intro σ h
    obtain ⟨Sy, hSy, hT⟩ := detTerm_symC_of_formula (S := T.step k hk N₁ ν β p₁)
      (m₀ := 1) (eps := T.t) isLevel_lvTopG hLq hN h (rho4 d L N T.BG T.κ)
    exact ⟨Sy, hSy, fun z => hT (E z) (E (rootAct σ z)) (hE z) (hE (rootAct σ z))⟩
  · intro z D hD R hR
    exact ⟨(detTerm_rot_of_formula (S := T.step k hk N₁ ν β p₁) (m₀ := 1) hC hk hδc
      T.large_block T.δc_small T.dom_margin T.coer_margin (E z) (hE z) hR hD).1,
      detTerm_rotC_of_formula (S := T.step k hk N₁ ν β p₁) (m₀ := 1) hC hk hδc
      T.large_block T.δc_small T.dom_margin T.coer_margin (E z) (hE z) hR hD q⟩
  · intro D hD Q hQ
    exact xiCData_rot hQ hD

end Package

end Balaban.Inhabited
