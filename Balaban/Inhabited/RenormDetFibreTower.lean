/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.DetPackageFromTower
public import Balaban.Inhabited.StepOutputPhysical
public import Balaban.Inhabited.RenormLocC1ZeroWitness
public import Balaban.Fluctuation.RenormDetFibreMap
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# The fibre regrouping of the determinant terms at the shared tower

The determinant terms of the zero-class step at the shared tower are indexed by polymers `X`
(`DetPackageFromTower`).  Here they are regrouped over the renormalization cover `renYs` of the
root neighbourhood through the fibre map `renFibreMap` of `RenormDetFibreMap`.

* `renDetFibre_root`: at every scale and root, the hypotheses of the fibre-map theorems for
  `G = lvTop`, `m₀ = 1`, `X₁ = X1 G 1 k (fam 1 (blockSite k z))`: `CovSetup`, the attained tree,
  `Δ = 0`, `IsLevel`, and the root site lies in `X₁`.
* `renDetFibre_support`: for a polymer containing the root box, the fibre map lands in the cover,
  contains the polymer, and `renDY (Φ X) ≤ A sizeJ X + A`; `renDetFibre_support_of_ne_zero`
  is the form for a polymer in the support of a determinant record.
* `renDetFibreMin`: the threshold on `κmin` above which the output rate `3 κ_dec / 2` survives the
  regrouping (`renDetFibreMin_spec`), and `stepHullMin ≤ renDetFibreMin`.
* `renFibreTerm`: the regrouped term `t_Y = ∑_{Φ X = Y} t X`.
* `renDetFibre_tower`: for `renDetFibreMin ≤ κmin`, one family of records at every scale with the
  sum identity over `renYs`, the bound at rate `3 κ_dec / 2` in `renDY`, and locality on `Y`.

Determinant part only, at `ξ = 0`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep LocalCover

section Setting

variable {κmin : ℝ}

/-- The core of the step at the shared tower (shared by the root setting). -/
theorem renDetFibre_flCore (T : StepTower κmin) (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁]
    (hN5 : 5 < N₁) {ν : ℝ} (hν0 : 0 ≤ ν) (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) :
    FlCore 2 (lvTop N₁ T.m₁ k (rhoSep T.m₁)) (lvLow N₁ T.m₁ k (rhoSep T.m₁)) 1 ν T.c
      T.BG T.κ T.t (levelKc 3 3) (Cchi 3 3) T.c₂ T.BG₂ T.t := by
  obtain ⟨hC₀⟩ := T.core
  have hSD := dgSetting_lv (N₁ := N₁) (k := k) T.m₁_four hN5 hν0 hν
  have hHB := bgHyp_lv (k := k) T.m₁ hν0 hν
  exact flCore_level_transfer hC₀ hSD (opSetting_lv T.m₁_four hN5 hν0 hν) (isLevel_lvLow hk)
    isLevel_lvTop hHB

/-- **T1 (root setting).**  At every scale `k ≥ 1` of the tower and every block root `z`, for
`G = lvTop`, `m₀ = 1` and `X₁ = X1 G 1 k (fam 1 (blockSite k z))`: the covering setup of the
cube of the root, an attained tree of length `0`, `Δ = 0`, the level property, and the root site
of the block lies in `X₁`. -/
theorem renDetFibre_root (T : StepTower κmin) (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁]
    (h3N : 3 ∣ N₁) (hN5 : 5 < N₁) {ν : ℝ} (hν0 : 0 ≤ ν) (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1)
    (z : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1)))) :
    CovSetup (lvTop N₁ T.m₁ k (rhoSep T.m₁)) 1 k (cube 1 k (blockSite k z))
        (fam 1 (blockSite k z)) ∧
      (∃ (W₀ : Finset (CTorus 3 3 N₁ T.m₁ (k + 1)))
        (E₀ : Finset (CTorus 3 3 N₁ T.m₁ (k + 1) × CTorus 3 3 N₁ T.m₁ (k + 1))),
        ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ cube 1 k (blockSite k z)) ∧
          MeetsOne 1 k (fam 1 (blockSite k z)) W₀ ∧
          bondCost (scaleW 3 1 T.m₁ k) E₀ = treeLenCovOne 1 k (cube 1 k (blockSite k z))) ∧
      treeLenCovOne 1 k (cube 1 k (blockSite k z)) = 0 ∧
      IsLevel (lvTop N₁ T.m₁ k (rhoSep T.m₁)) (k + 1) ∧
      blockSite k z ∈ X1 (lvTop N₁ T.m₁ k (rhoSep T.m₁)) 1 k (fam 1 (blockSite k z)) := by
  have hC := renDetFibre_flCore T k hk N₁ hN5 hν0 hν
  have hN3 : 3 ^ 1 ∣ N₁ := by simpa using h3N
  obtain ⟨hV, -⟩ := renLoc_fin_domains (N := 2) (lvLow N₁ T.m₁ k (rhoSep T.m₁)) hC.Sp
    isLevel_lvTop (m₀ := 1) le_rfl hN3
  obtain ⟨hcov, hX₁, hopt, hΔ, -⟩ := hV z
  refine ⟨hcov, hopt, hΔ, isLevel_lvTop, ?_⟩
  rw [← hX₁, coe_nbhdF]
  have := mem_nbhdF_self (m₀ := 1) (blockSite k z)
  rwa [← Finset.mem_coe, coe_nbhdF] at this

/-- **T1 (the support of the determinant family).**  For a polymer `X` containing the root box
of `z`: the fibre map sends `X` into the renormalization cover, `X ⊆ Φ X`, and
`renDY (Φ X) ≤ A sizeJ X + A` with `A = renDetA 3 3 1`. -/
theorem renDetFibre_support (T : StepTower κmin) (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁]
    (h3N : 3 ∣ N₁) (hN5 : 5 < N₁) {ν : ℝ} (hν0 : 0 ≤ ν) (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1)
    (z : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))))
    {X : Set (CTorus 3 3 N₁ T.m₁ (k + 1))} (hX : IsPolyDom 1 (k + 1) X)
    (hroot : box (rootCube (m₀ := 1) (K := k + 1) z).1 (cellSide 3 1 T.m₁ (k + 1)) ⊆ X) :
    renFibreMap (lvTop N₁ T.m₁ k (rhoSep T.m₁)) 1
        (X1 (lvTop N₁ T.m₁ k (rhoSep T.m₁)) 1 k (fam 1 (blockSite k z))) X ∈
      renYs (renCube (lvTop N₁ T.m₁ k (rhoSep T.m₁))
          (X1 (lvTop N₁ T.m₁ k (rhoSep T.m₁)) 1 k (fam 1 (blockSite k z))))
        (lvTop N₁ T.m₁ k (rhoSep T.m₁)) 1
        (X1 (lvTop N₁ T.m₁ k (rhoSep T.m₁)) 1 k (fam 1 (blockSite k z))) ∧
      X ⊆ ↑(renFibreMap (lvTop N₁ T.m₁ k (rhoSep T.m₁)) 1
        (X1 (lvTop N₁ T.m₁ k (rhoSep T.m₁)) 1 k (fam 1 (blockSite k z))) X) ∧
      renDY (lvTop N₁ T.m₁ k (rhoSep T.m₁)) 1
          (renFibreMap (lvTop N₁ T.m₁ k (rhoSep T.m₁)) 1
            (X1 (lvTop N₁ T.m₁ k (rhoSep T.m₁)) 1 k (fam 1 (blockSite k z))) X) ≤
        renDetA 3 3 1 * sizeJ 1 (k + 1) X + renDetA 3 3 1 := by
  obtain ⟨hS, hopt, hΔ, hG, hx⟩ := renDetFibre_root T k hk N₁ h3N hN5 hν0 hν z
  have hx0 : ∃ x ∈ X, x ∈ X1 (lvTop N₁ T.m₁ k (rhoSep T.m₁)) 1 k (fam 1 (blockSite k z)) :=
    ⟨blockSite k z, hroot (rootSite_mem_box_rootCube (m₀ := 1) (K := k + 1) z), hx⟩
  exact ⟨renFibreMap_mem_renYs hS hG hX hx0, subset_renFibreMap hS hG,
    renDY_renFibreMap_le hS hG (by norm_num) hopt hΔ hX hx0⟩

end Setting

/-! ### The rate threshold -/

/-- **T2: the threshold on `κmin`.**  `A · detHullThreshold + 18 (1 + B) c₁ log 2` with
`A = renDetA 3 3 1`, `B = collarB 3 3` and `c₁ = c1 3 3`. -/
noncomputable def renDetFibreMin : ℝ :=
  renDetA 3 3 1 * detHullThreshold + 18 * (1 + collarB 3 3) * (c1 3 3 * Real.log 2)

theorem renDetA_three_one : renDetA 3 3 1 = 93767625 := by
  unfold renDetA; rw [c1_three]; norm_num

theorem detHullThreshold_nonneg : 0 ≤ detHullThreshold := by
  have hent := aEnt_nonneg 3 3
  have hl : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hg : 0 ≤ Real.log ((detDeg 3 3 + 1 : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast Nat.le_add_left 1 _)
  unfold detHullThreshold
  nlinarith

/-- The joint tower can be taken at the larger threshold. -/
theorem stepHullMin_le_renDetFibreMin : stepHullMin ≤ renDetFibreMin := by
  have h0 := detHullThreshold_nonneg
  have hl : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  unfold renDetFibreMin stepHullMin
  rw [renDetA_three_one, collarB_three, c1_three]
  nlinarith

/-- **T2: the output rate survives the fibre regrouping.**  For `renDetFibreMin ≤ κmin`,
`κ_out = 3 κ_dec / 2 ≤ hullRate / A - c₁ log 2`. -/
theorem renDetFibreMin_spec {κmin : ℝ} (T : StepTower κmin) (h : renDetFibreMin ≤ κmin) :
    3 / 2 * T.κdec ≤ hullRate 3 3 (towerDetRate T.κ) / renDetA 3 3 1 - c1 3 3 * Real.log 2 := by
  have hl : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hg : 0 ≤ Real.log ((detDeg 3 3 + 1 : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast Nat.le_add_left 1 _)
  have e : 3 / 2 * T.κdec = 3 / 2 * (100 * (aEnt 3 3 + 2 + 3375 + 10)) := by
    rw [T.κdec_eq, T.κ0_eq, c1_three]
  have hκ := T.κmin_le
  have hA : (0 : ℝ) < renDetA 3 3 1 := by rw [renDetA_three_one]; norm_num
  have h1 : renDetA 3 3 1 * (3 / 2 * T.κdec + 3375 * Real.log 2) ≤
      hullRate 3 3 (towerDetRate T.κ) := by
    refine hullRate_ge_of_le (κ := T.κ) (kout := renDetA 3 3 1 * (3 / 2 * T.κdec +
      3375 * Real.log 2)) ?_
    unfold renDetFibreMin detHullThreshold at h
    rw [renDetA_three_one, collarB_three, c1_three] at h
    rw [renDetA_three_one, e]
    nlinarith
  rw [le_sub_iff_add_le, le_div_iff₀ hA, c1_three]
  linarith

section Terms

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}

open Classical in
/-- **The regrouped term** `t_Y = ∑_{Φ X = Y} t X` of a family `t` on the polymers. -/
noncomputable abbrev renFibreTerm (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) (m₀ : ℕ)
    (X₁ : Set (CTorus d L N₁ m₁ K)) {E : Type*} [AddCommMonoid E]
    (t : Set (CTorus d L N₁ m₁ K) → E) (Y : Finset (CTorus d L N₁ m₁ K)) : E :=
  ∑ X ∈ Finset.univ.filter (fun X : Set (CTorus d L N₁ m₁ K) => renFibreMap G m₀ X₁ X = Y), t X

end Terms

section Tower

variable {κmin : ℝ}

/-- **T1, support form.**  For a record `E` of the determinant terms at the step of the tower and
a datum `D` of the chart, a polymer `X` with `E.detGrouped D X ≠ 0` satisfies the three
conclusions of `renDetFibre_support`. -/
theorem renDetFibre_support_of_ne_zero (T : StepTower κmin) (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ)
    [NeZero N₁] (h3N : 3 ∣ N₁) (hN5 : 5 < N₁) {ν : ℝ} (hν0 : 0 ≤ ν)
    (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) (β p₁ : ℝ)
    (z : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1)))) {κ₁ c₁ : ℝ}
    (E : DetExpansionLocC (T.step k hk N₁ ν β p₁) 1 z T.t κ₁ c₁)
    {D : BgData (T.step k hk N₁ ν β p₁).G' 2}
    (hD : XiCData (T.step k hk N₁ ν β p₁).G' (compWeight 3 1) ν (k + 1) 1 T.t D)
    {X : Set (CTorus 3 3 N₁ T.m₁ (k + 1))} (hX : E.detGrouped D X ≠ 0) :
    renFibreMap (lvTop N₁ T.m₁ k (rhoSep T.m₁)) 1
        (X1 (lvTop N₁ T.m₁ k (rhoSep T.m₁)) 1 k (fam 1 (blockSite k z))) X ∈
      renYs (renCube (lvTop N₁ T.m₁ k (rhoSep T.m₁))
          (X1 (lvTop N₁ T.m₁ k (rhoSep T.m₁)) 1 k (fam 1 (blockSite k z))))
        (lvTop N₁ T.m₁ k (rhoSep T.m₁)) 1
        (X1 (lvTop N₁ T.m₁ k (rhoSep T.m₁)) 1 k (fam 1 (blockSite k z))) ∧
      X ⊆ ↑(renFibreMap (lvTop N₁ T.m₁ k (rhoSep T.m₁)) 1
        (X1 (lvTop N₁ T.m₁ k (rhoSep T.m₁)) 1 k (fam 1 (blockSite k z))) X) ∧
      renDY (lvTop N₁ T.m₁ k (rhoSep T.m₁)) 1
          (renFibreMap (lvTop N₁ T.m₁ k (rhoSep T.m₁)) 1
            (X1 (lvTop N₁ T.m₁ k (rhoSep T.m₁)) 1 k (fam 1 (blockSite k z))) X) ≤
        renDetA 3 3 1 * sizeJ 1 (k + 1) X + renDetA 3 3 1 := by
  have hN : (3 : ℕ) ^ 1 ∣ N₁ := by simpa using h3N
  obtain ⟨hpoly, hroot⟩ := E.detGrouped_anchor (by norm_num) hN hD hX
  exact renDetFibre_support T k hk N₁ h3N hN5 hν0 hν z hpoly hroot

open Classical in
/-- **T3: the regrouped determinant terms at the tower.**  For `renDetFibreMin ≤ κmin`, at every
scale there is one family `z ↦ E z` of records with the term formula such that, for chart data
`D`, with `t_Y = renFibreTerm … ((E z).detGrouped D) Y` and `X₁ = X1 G 1 k (fam 1 (blockSite k z))`:

* the terms `t_Y`, `Y ∈ renYs`, add up to the root trace;
* `‖t_Y‖ ≤ H′ exp(-(3 κ_dec / 2) renDY Y)` for every finset `Y`, with
  `H′ = hullConst · exp(c₁ log 2) · exp(hullRate)`;
* two chart data agreeing (`Ψ` and `h`) on the sites of `Y` have the same `t_Y`. -/
theorem renDetFibre_tower (T : StepTower κmin) (hT : renDetFibreMin ≤ κmin)
    (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (h3N : 3 ∣ N₁) (hN5 : 5 < N₁) {ν : ℝ}
    (hν0 : 0 ≤ ν) (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) (β p₁ : ℝ) :
    ∃ E : ∀ z : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))),
        DetExpansionLocC (T.step k hk N₁ ν β p₁) 1 z T.t (towerDetRate T.κ)
          (towerDetConst T.κ),
      (∀ z D T', (E z).term D T' = ∑ y ∈ (T.step k hk N₁ ν β p₁).blockU z,
        detActivityBg 1 (compWeight 3 1) 1 ν (rho4 3 3 2 T.BG T.κ) D y T') ∧
      (∀ z (D : BgData (T.step k hk N₁ ν β p₁).G' 2),
        XiCData (T.step k hk N₁ ν β p₁).G' (compWeight 3 1) ν (k + 1) 1 T.t D →
        ∑ Y ∈ renYs (renCube (lvTop N₁ T.m₁ k (rhoSep T.m₁))
              (X1 (lvTop N₁ T.m₁ k (rhoSep T.m₁)) 1 k (fam 1 (blockSite k z))))
            (lvTop N₁ T.m₁ k (rhoSep T.m₁)) 1
            (X1 (lvTop N₁ T.m₁ k (rhoSep T.m₁)) 1 k (fam 1 (blockSite k z))),
          renFibreTerm (lvTop N₁ T.m₁ k (rhoSep T.m₁)) 1
            (X1 (lvTop N₁ T.m₁ k (rhoSep T.m₁)) 1 k (fam 1 (blockSite k z)))
            ((E z).detGrouped D) Y =
          rootTrace (T.step k hk N₁ ν β p₁).G' (T.step k hk N₁ ν β p₁).a 1 ν
            (unitQ (T.step k hk N₁ ν β p₁).G') (unitP (T.step k hk N₁ ν β p₁).G')
            ((T.step k hk N₁ ν β p₁).blockU z) (fun _ => 1)
            (svec (T.step k hk N₁ ν β p₁).G' (bgFieldC (T.step k hk N₁ ν β p₁).G'
              (T.step k hk N₁ ν β p₁).a ν (bgC0 3 3 2) D))
            (bgMultC (T.step k hk N₁ ν β p₁).G' (T.step k hk N₁ ν β p₁).a ν (bgC0 3 3 2) D)) ∧
      (∀ z (D : BgData (T.step k hk N₁ ν β p₁).G' 2),
        XiCData (T.step k hk N₁ ν β p₁).G' (compWeight 3 1) ν (k + 1) 1 T.t D →
        ∀ Y : Finset (CTorus 3 3 N₁ T.m₁ (k + 1)),
          ‖renFibreTerm (lvTop N₁ T.m₁ k (rhoSep T.m₁)) 1
              (X1 (lvTop N₁ T.m₁ k (rhoSep T.m₁)) 1 k (fam 1 (blockSite k z)))
              ((E z).detGrouped D) Y‖ ≤
            hullConst 3 3 (towerDetRate T.κ) (towerDetConst T.κ) *
              Real.exp (c1 3 3 * Real.log 2) * Real.exp (hullRate 3 3 (towerDetRate T.κ)) *
              Real.exp (-(3 / 2 * T.κdec) *
                renDY (lvTop N₁ T.m₁ k (rhoSep T.m₁)) 1 Y)) ∧
      (∀ z (D D₂ : BgData (T.step k hk N₁ ν β p₁).G' 2),
        XiCData (T.step k hk N₁ ν β p₁).G' (compWeight 3 1) ν (k + 1) 1 T.t D →
        XiCData (T.step k hk N₁ ν β p₁).G' (compWeight 3 1) ν (k + 1) 1 T.t D₂ →
        ∀ Y : Finset (CTorus 3 3 N₁ T.m₁ (k + 1)),
          (∀ v ∈ Y, D.Ψ v = D₂.Ψ v ∧ D.h v = D₂.h v) →
          renFibreTerm (lvTop N₁ T.m₁ k (rhoSep T.m₁)) 1
              (X1 (lvTop N₁ T.m₁ k (rhoSep T.m₁)) 1 k (fam 1 (blockSite k z)))
              ((E z).detGrouped D) Y =
            renFibreTerm (lvTop N₁ T.m₁ k (rhoSep T.m₁)) 1
              (X1 (lvTop N₁ T.m₁ k (rhoSep T.m₁)) 1 k (fam 1 (blockSite k z)))
              ((E z).detGrouped D₂) Y) := by
  have hstep : detHullThreshold ≤ κmin := le_trans stepHullMin_le_renDetFibreMin hT
  obtain ⟨E, hE, hsum, hbd, hanc, hloc, -, -, -⟩ :=
    detPackage_fromTower T k hk N₁ h3N hN5 hν0 hν β p₁
  have hN : (3 : ℕ) ^ 1 ∣ N₁ := by simpa using h3N
  have h3 : 3 ≤ 3 ^ (1 + T.m₁) := by
    calc 3 = 3 ^ 1 := by norm_num
      _ ≤ 3 ^ (1 + T.m₁) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hrate := towerDetHullRate_ge T hstep
  have hκ0 : 0 ≤ 3 / 2 * T.κdec := by
    have := T.κdec_lower; have := T.κ0_nonneg; linarith
  have hconst := towerDetConst_nonneg T
  have hH : 0 ≤ hullConst 3 3 (towerDetRate T.κ) (towerDetConst T.κ) := by
    unfold hullConst; exact mul_nonneg hconst (Real.exp_pos _).le
  refine ⟨E, hE, ?_, ?_, ?_⟩
  · intro z D hD
    obtain ⟨hS, hopt, hΔ, hG, hx⟩ := renDetFibre_root T k hk N₁ h3N hN5 hν0 hν z
    have ht0 : ∀ X : Set (CTorus 3 3 N₁ T.m₁ (k + 1)),
        ¬ (IsPolyDom 1 (k + 1) X ∧ ∃ x ∈ X,
          x ∈ X1 (lvTop N₁ T.m₁ k (rhoSep T.m₁)) 1 k (fam 1 (blockSite k z))) →
        (E z).detGrouped D X = 0 := by
      intro X hX
      by_contra hne
      obtain ⟨hpoly, hroot⟩ := hanc z D hD X hne
      exact hX ⟨hpoly, blockSite k z, hroot (rootSite_mem_box_rootCube (m₀ := 1) (K := k + 1) z),
        hx⟩
    have h1 := sum_renRegroup hS hG ((E z).detGrouped D) ht0
    have h2 : ∑ X, (E z).detGrouped D X = ∑ X ∈ (Finset.univ : Finset (Finset
        (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1) Set.univ))).image
        detCollarHull, (E z).detGrouped D X := by
      symm
      refine Finset.sum_subset (Finset.subset_univ _) fun X _ hX => ?_
      unfold DetExpansionLocC.detGrouped detCollarGrouped
      refine Finset.sum_eq_zero fun T' hT' => absurd ?_ hX
      rw [← mem_detCollarFibre.1 hT']
      exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
    rw [← hsum z D hD, ← h2, ← h1]
  · intro z D hD Y
    obtain ⟨hS, hopt, hΔ, hG, hx⟩ := renDetFibre_root T k hk N₁ h3N hN5 hν0 hν z
    have ht0 : ∀ X : Set (CTorus 3 3 N₁ T.m₁ (k + 1)),
        ¬ (IsPolyDom 1 (k + 1) X ∧ ∃ x ∈ X,
          x ∈ X1 (lvTop N₁ T.m₁ k (rhoSep T.m₁)) 1 k (fam 1 (blockSite k z))) →
        (E z).detGrouped D X = 0 := by
      intro X hX
      by_contra hne
      obtain ⟨hpoly, hroot⟩ := hanc z D hD X hne
      exact hX ⟨hpoly, blockSite k z, hroot (rootSite_mem_box_rootCube (m₀ := 1) (K := k + 1) z),
        hx⟩
    exact renRegroup_norm_le hS hG (by norm_num) hopt hΔ ((E z).detGrouped D) hH
      (hκ0.trans (hrate.trans' (le_of_eq (by ring)))) ht0
      (fun X hX _ => hbd z D hD X) (renDetFibreMin_spec T hT) Y
  · intro z D D₂ hD hD₂ Y hY
    obtain ⟨hS, hopt, hΔ, hG, hx⟩ := renDetFibre_root T k hk N₁ h3N hN5 hν0 hν z
    refine Finset.sum_congr rfl fun X hX => ?_
    have hΦ := (Finset.mem_filter.1 hX).2
    refine (E z).detGrouped_local (by norm_num) hN h3 hD hD₂ fun v hv => hY v ?_
    rw [← hΦ, ← Finset.mem_coe]
    exact subset_renFibreMap hS hG hv

end Tower

end Balaban.Inhabited
