/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.DetPackageFromTower
public import Balaban.Inhabited.StepOutputPhysical
public import Balaban.Inhabited.StepOutputPhysicalG
public import Balaban.Inhabited.DetPackageFromTowerG
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

namespace StepTowerG

variable {d L N : ℕ} [NeZero L]

/-- **The core of the step at the general tower.**  Shared by the root setting. -/
theorem renDetFibre_flCore (T : StepTowerG d L N κmin) (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ)
    [NeZero N₁] (hN5 : 5 < N₁) {ν : ℝ} (hν0 : 0 ≤ ν) (hν : ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1) :
    FlCore N (lvTopG d L N₁ T.m₁ k (rhoSepG d L T.m₁))
      (lvLowG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) 1 ν T.c T.BG T.κ T.t (levelKc d L)
      (Cchi d L) T.c₂ T.BG₂ T.t :=
  flCore_stepG T.hd T.hL T.m₁_four (Classical.choice T.core) hk hN5 hν0 hν

/-- **T1 (root setting), general tower.**  At every scale `k ≥ 1` of the tower and every block
root `z`, for `G = lvTopG`, `m₀ = 1` and `X₁ = X1 G 1 k (fam 1 (blockSite k z))`: the covering
setup of the cube of the root, an attained tree of length `0`, `Δ = 0`, the level property, and
the root site of the block lies in `X₁`. -/
theorem renDetFibre_root (T : StepTowerG d L N κmin) (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ)
    [NeZero N₁] (hLN : L ∣ N₁) (hN5 : 5 < N₁) {ν : ℝ} (hν0 : 0 ≤ ν)
    (hν : ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1)
    (z : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1)))) :
    CovSetup (lvTopG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) 1 k (cube 1 k (blockSite k z))
        (fam 1 (blockSite k z)) ∧
      (∃ (W₀ : Finset (CTorus d L N₁ T.m₁ (k + 1)))
        (E₀ : Finset (CTorus d L N₁ T.m₁ (k + 1) × CTorus d L N₁ T.m₁ (k + 1))),
        ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ cube 1 k (blockSite k z)) ∧
          MeetsOne 1 k (fam 1 (blockSite k z)) W₀ ∧
          bondCost (scaleW L 1 T.m₁ k) E₀ = treeLenCovOne 1 k (cube 1 k (blockSite k z))) ∧
      treeLenCovOne 1 k (cube 1 k (blockSite k z)) = 0 ∧
      IsLevel (lvTopG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (k + 1) ∧
      blockSite k z ∈ X1 (lvTopG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) 1 k
        (fam 1 (blockSite k z)) := by
  have hC := T.renDetFibre_flCore k hk N₁ hN5 hν0 hν
  have hN3 : L ^ 1 ∣ N₁ := by simpa using hLN
  obtain ⟨hV, -⟩ := renLoc_fin_domains (N := N) (lvLowG d L N₁ T.m₁ k (rhoSepG d L T.m₁))
    hC.Sp isLevel_lvTopG (m₀ := 1) le_rfl hN3
  obtain ⟨hcov, hX₁, hopt, hΔ, -⟩ := hV z
  refine ⟨hcov, hopt, hΔ, isLevel_lvTopG, ?_⟩
  rw [← hX₁, coe_nbhdF]
  have := mem_nbhdF_self (m₀ := 1) (blockSite k z)
  rwa [← Finset.mem_coe, coe_nbhdF] at this

/-- **T1 (the support of the determinant family), general tower.**  For a polymer `X` containing
the root box of `z`: the fibre map sends `X` into the renormalization cover, `X ⊆ Φ X`, and
`renDY (Φ X) ≤ A sizeJ X + A` with `A = renDetA d L 1`. -/
theorem renDetFibre_support (T : StepTowerG d L N κmin) (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ)
    [NeZero N₁] (hLN : L ∣ N₁) (hN5 : 5 < N₁) {ν : ℝ} (hν0 : 0 ≤ ν)
    (hν : ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1)
    (z : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))))
    {X : Set (CTorus d L N₁ T.m₁ (k + 1))} (hX : IsPolyDom 1 (k + 1) X)
    (hroot : box (rootCube (m₀ := 1) (K := k + 1) z).1 (cellSide L 1 T.m₁ (k + 1)) ⊆ X) :
    renFibreMap (lvTopG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) 1
        (X1 (lvTopG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) 1 k (fam 1 (blockSite k z))) X ∈
      renYs (renCube (lvTopG d L N₁ T.m₁ k (rhoSepG d L T.m₁))
          (X1 (lvTopG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) 1 k (fam 1 (blockSite k z))))
        (lvTopG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) 1
        (X1 (lvTopG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) 1 k (fam 1 (blockSite k z))) ∧
      X ⊆ ↑(renFibreMap (lvTopG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) 1
        (X1 (lvTopG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) 1 k (fam 1 (blockSite k z))) X) ∧
      renDY (lvTopG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) 1
          (renFibreMap (lvTopG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) 1
            (X1 (lvTopG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) 1 k (fam 1 (blockSite k z))) X) ≤
        renDetA d L 1 * sizeJ 1 (k + 1) X + renDetA d L 1 := by
  obtain ⟨hS, hopt, hΔ, hG, hx⟩ := T.renDetFibre_root k hk N₁ hLN hN5 hν0 hν z
  have hx0 : ∃ x ∈ X, x ∈ X1 (lvTopG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) 1 k
      (fam 1 (blockSite k z)) :=
    ⟨blockSite k z, hroot (rootSite_mem_box_rootCube (m₀ := 1) (K := k + 1) z), hx⟩
  exact ⟨renFibreMap_mem_renYs hS hG hX hx0, subset_renFibreMap hS hG,
    renDY_renFibreMap_le hS hG T.hd hopt hΔ hX hx0⟩

end StepTowerG

/-- The core of the step at the shared tower (shared by the root setting).  Corollary of
`StepTowerG.renDetFibre_flCore` through `T.toG`. -/
theorem renDetFibre_flCore (T : StepTower κmin) (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁]
    (hN5 : 5 < N₁) {ν : ℝ} (hν0 : 0 ≤ ν) (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) :
    FlCore 2 (lvTop N₁ T.m₁ k (rhoSep T.m₁)) (lvLow N₁ T.m₁ k (rhoSep T.m₁)) 1 ν T.c
      T.BG T.κ T.t (levelKc 3 3) (Cchi 3 3) T.c₂ T.BG₂ T.t := by
  have h := T.toG.renDetFibre_flCore k hk N₁ hN5 hν0 (by simpa using hν)
  rw [rhoSepG_three] at h
  exact h

/-- **T1 (root setting).**  At every scale `k ≥ 1` of the tower and every block root `z`, for
`G = lvTop`, `m₀ = 1` and `X₁ = X1 G 1 k (fam 1 (blockSite k z))`: the covering setup of the
cube of the root, an attained tree of length `0`, `Δ = 0`, the level property, and the root site
of the block lies in `X₁`.  Corollary of `StepTowerG.renDetFibre_root`. -/
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
  have h := T.toG.renDetFibre_root k hk N₁ h3N hN5 hν0 (by simpa using hν) z
  rw [rhoSepG_three] at h
  exact h

/-- **T1 (the support of the determinant family).**  For a polymer `X` containing the root box
of `z`: the fibre map sends `X` into the renormalization cover, `X ⊆ Φ X`, and
`renDY (Φ X) ≤ A sizeJ X + A` with `A = renDetA 3 3 1`.  Corollary of
`StepTowerG.renDetFibre_support`. -/
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
  have h := T.toG.renDetFibre_support k hk N₁ h3N hN5 hν0 (by simpa using hν) z hX hroot
  rw [rhoSepG_three] at h
  exact h

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

/-- The fixed threshold `renDetFibreMin ≤ κmin` implies the general hull hypothesis of
`StepTowerG.renDetFibre_spec` at `T.toG`. -/
theorem StepTower.hhull_renDetFibre_toG {κmin : ℝ} (T : StepTower κmin)
    (h : renDetFibreMin ≤ κmin) :
    2 * (3 : ℕ) * (3 : ℕ) * (1 + collarB 3 3) *
        (renDetA 3 3 1 * (3 / 2 * T.toG.κdec + c1 3 3 * Real.log 2) + c1 3 3 * Real.log 2) +
      Real.log 2 + 2 * Real.log ((detDeg 3 3 + 1 : ℕ) : ℝ) ≤ T.toG.κ := by
  have hl : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hg : 0 ≤ Real.log ((detDeg 3 3 + 1 : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast Nat.le_add_left 1 _)
  have e : T.toG.κdec = 100 * (aEnt 3 3 + 2 + 3375 + 10) := by
    show T.κdec = _
    rw [T.κdec_eq, T.κ0_eq, c1_three]
  have hκ := T.κmin_le
  unfold renDetFibreMin detHullThreshold at h
  rw [renDetA_three_one, collarB_three, c1_three] at h
  rw [e, renDetA_three_one, collarB_three, c1_three]
  have : T.κ = T.toG.κ := rfl
  push_cast at h hg ⊢
  linarith

namespace StepTowerG

variable {d L N : ℕ} [NeZero L] {κmin : ℝ}

/-- **T2, general tower: the output rate survives the fibre regrouping.**  Under the explicit
threshold `2 d L (1 + B) (A (3 κ_dec / 2 + c₁ log 2) + c₁ log 2) + log 2 + 2 log (detDeg d L + 1)
≤ κ` (`A = renDetA d L 1`, `B = collarB d L`), `κ_out = 3 κ_dec / 2 ≤ hullRate / A - c₁ log 2`. -/
theorem renDetFibre_spec (T : StepTowerG d L N κmin)
    (hhull : 2 * d * L * (1 + collarB d L) *
        (renDetA d L 1 * (3 / 2 * T.κdec + c1 d L * Real.log 2) + c1 d L * Real.log 2) +
      Real.log 2 + 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ) ≤ T.κ) :
    3 / 2 * T.κdec ≤ hullRate d L (detRateG d L T.κ) / renDetA d L 1 - c1 d L * Real.log 2 := by
  have hA := renDetA_pos d L 1 T.hd
  have h1 : renDetA d L 1 * (3 / 2 * T.κdec + c1 d L * Real.log 2) ≤
      hullRate d L (detRateG d L T.κ) :=
    hullRate_ge_general (by have := T.hd; omega) (by have := T.hL; omega) hhull
  rw [le_sub_iff_add_le, le_div_iff₀ hA]
  linarith

end StepTowerG

/-- **T2: the output rate survives the fibre regrouping.**  For `renDetFibreMin ≤ κmin`,
`κ_out = 3 κ_dec / 2 ≤ hullRate / A - c₁ log 2`.  Corollary of
`StepTowerG.renDetFibre_spec`. -/
theorem renDetFibreMin_spec {κmin : ℝ} (T : StepTower κmin) (h : renDetFibreMin ≤ κmin) :
    3 / 2 * T.κdec ≤ hullRate 3 3 (towerDetRate T.κ) / renDetA 3 3 1 - c1 3 3 * Real.log 2 := by
  rw [← detRateG_three]
  exact T.toG.renDetFibre_spec (T.hhull_renDetFibre_toG h)

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

namespace StepTowerG

variable {d L N : ℕ} [NeZero L] {κmin : ℝ}

/-- **T1, support form, general tower and odd `L = 2 q + 1`.**  For a record `E` of the
determinant terms at the step of the tower and a datum `D` of the chart, a polymer `X` with
`E.detGroupedC q D X ≠ 0` satisfies the three conclusions of `StepTowerG.renDetFibre_support`. -/
theorem renDetFibre_support_of_ne_zero (T : StepTowerG d L N κmin) {q : ℕ}
    (hLq : L = 2 * q + 1) (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ)
    [NeZero N₁] (hLN : L ∣ N₁) (hN5 : 5 < N₁) {ν : ℝ} (hν0 : 0 ≤ ν)
    (hν : ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1) (β p₁ : ℝ)
    (z : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1)))) {κ₁ c₁ : ℝ}
    (E : DetExpansionLocC (T.step k hk N₁ ν β p₁) 1 z T.t κ₁ c₁)
    {D : BgData (T.step k hk N₁ ν β p₁).G' N}
    (hD : XiCData (T.step k hk N₁ ν β p₁).G' (compWeight L 1) ν (k + 1) 1 T.t D)
    {X : Set (CTorus d L N₁ T.m₁ (k + 1))} (hX : E.detGroupedC q D X ≠ 0) :
    renFibreMap (lvTopG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) 1 (X1 (lvTopG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) 1 k (fam 1 (blockSite k z))) X ∈
      renYs (renCube (lvTopG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (X1 (lvTopG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) 1 k (fam 1 (blockSite k z))))
        (lvTopG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) 1 (X1 (lvTopG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) 1 k (fam 1 (blockSite k z))) ∧
      X ⊆ ↑(renFibreMap (lvTopG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) 1 (X1 (lvTopG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) 1 k (fam 1 (blockSite k z))) X) ∧
      renDY (lvTopG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) 1 (renFibreMap (lvTopG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) 1 (X1 (lvTopG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) 1 k (fam 1 (blockSite k z))) X) ≤
        renDetA d L 1 * sizeJ 1 (k + 1) X + renDetA d L 1 := by
  have hN : L ^ 1 ∣ N₁ := by simpa using hLN
  obtain ⟨hpoly, hroot⟩ := E.detGroupedC_anchor (q := q) (by omega) hN hD hX
  exact T.renDetFibre_support k hk N₁ hLN hN5 hν0 hν z hpoly hroot

open Classical in
/-- **T3, general tower and odd `L = 2 q + 1`: the regrouped determinant terms.**  Under the
explicit threshold `hhull` of `StepTowerG.renDetFibre_spec` on `T.κ`, at every scale there is one
family `z ↦ E z` of records with the term formula such that, for chart data `D`, with
`t_Y = renFibreTerm … ((E z).detGroupedC q D) Y` and `X₁ = X1 G 1 k (fam 1 (blockSite k z))`:
the terms `t_Y`, `Y ∈ renYs`, add up to the root trace; `‖t_Y‖ ≤ H′ exp(-(3 κ_dec / 2) renDY Y)`
with `H′ = hullConst · exp(c₁ log 2) · exp(hullRate)`; and two chart data agreeing (`Ψ` and `h`)
on the sites of `Y` have the same `t_Y`. -/
theorem renDetFibre_tower (T : StepTowerG d L N κmin) {q : ℕ} (hLq : L = 2 * q + 1)
    (hhull : 2 * d * L * (1 + collarB d L) *
        (renDetA d L 1 * (3 / 2 * T.κdec + c1 d L * Real.log 2) + c1 d L * Real.log 2) +
      Real.log 2 + 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ) ≤ T.κ)
    (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (hLN : L ∣ N₁) (hN5 : 5 < N₁) {ν : ℝ}
    (hν0 : 0 ≤ ν) (hν : ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1) (β p₁ : ℝ) :
    ∃ E : ∀ z : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))),
        DetExpansionLocC (T.step k hk N₁ ν β p₁) 1 z T.t
          ((T.κ - Real.log 2 - 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) / (2 * d * L))
          ((L : ℝ) ^ d * ((1 / 2 : ℝ) * N * covBLogMax d L T.κ /
          (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp T.κ)))),
      (∀ z D T', (E z).term D T' = ∑ y ∈ (T.step k hk N₁ ν β p₁).blockU z,
        detActivityBg 1 (compWeight L 1) 1 ν (rho4 d L N T.BG T.κ) D y T') ∧
      (∀ z (D : BgData (T.step k hk N₁ ν β p₁).G' N),
        XiCData (T.step k hk N₁ ν β p₁).G' (compWeight L 1) ν (k + 1) 1 T.t D →
        ∑ Y ∈ renYs (renCube (lvTopG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (X1 (lvTopG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) 1 k (fam 1 (blockSite k z))))
            (lvTopG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) 1 (X1 (lvTopG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) 1 k (fam 1 (blockSite k z))),
          renFibreTerm (lvTopG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) 1 (X1 (lvTopG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) 1 k (fam 1 (blockSite k z)))
            ((E z).detGroupedC q D) Y =
          rootTrace (T.step k hk N₁ ν β p₁).G' (T.step k hk N₁ ν β p₁).a 1 ν
            (unitQ (T.step k hk N₁ ν β p₁).G') (unitP (T.step k hk N₁ ν β p₁).G')
            ((T.step k hk N₁ ν β p₁).blockU z) (fun _ => 1)
            (svec (T.step k hk N₁ ν β p₁).G' (bgFieldC (T.step k hk N₁ ν β p₁).G'
              (T.step k hk N₁ ν β p₁).a ν (bgC0 d L N) D))
            (bgMultC (T.step k hk N₁ ν β p₁).G' (T.step k hk N₁ ν β p₁).a ν (bgC0 d L N) D)) ∧
      (∀ z (D : BgData (T.step k hk N₁ ν β p₁).G' N),
        XiCData (T.step k hk N₁ ν β p₁).G' (compWeight L 1) ν (k + 1) 1 T.t D →
        ∀ Y : Finset (CTorus d L N₁ T.m₁ (k + 1)),
          ‖renFibreTerm (lvTopG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) 1 (X1 (lvTopG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) 1 k (fam 1 (blockSite k z)))
              ((E z).detGroupedC q D) Y‖ ≤
            hullConst d L ((T.κ - Real.log 2 - 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) / (2 * d * L))
                ((L : ℝ) ^ d * ((1 / 2 : ℝ) * N * covBLogMax d L T.κ /
          (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp T.κ)))) *
              Real.exp (c1 d L * Real.log 2) *
              Real.exp (hullRate d L ((T.κ - Real.log 2 - 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) / (2 * d * L))) *
              Real.exp (-(3 / 2 * T.κdec) * renDY (lvTopG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) 1 Y)) ∧
      (∀ z (D D₂ : BgData (T.step k hk N₁ ν β p₁).G' N),
        XiCData (T.step k hk N₁ ν β p₁).G' (compWeight L 1) ν (k + 1) 1 T.t D →
        XiCData (T.step k hk N₁ ν β p₁).G' (compWeight L 1) ν (k + 1) 1 T.t D₂ →
        ∀ Y : Finset (CTorus d L N₁ T.m₁ (k + 1)),
          (∀ v ∈ Y, D.Ψ v = D₂.Ψ v ∧ D.h v = D₂.h v) →
          renFibreTerm (lvTopG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) 1 (X1 (lvTopG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) 1 k (fam 1 (blockSite k z)))
              ((E z).detGroupedC q D) Y =
            renFibreTerm (lvTopG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) 1 (X1 (lvTopG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) 1 k (fam 1 (blockSite k z)))
              ((E z).detGroupedC q D₂) Y) := by
  obtain ⟨E, hE, hsum, hbd, hanc, hloc, -, -, -⟩ :=
    T.detPackage_fromTowerG hLq k hk N₁ hLN hN5 hν0 hν β p₁
  have hN : L ^ 1 ∣ N₁ := by simpa using hLN
  have hspec := T.renDetFibre_spec hhull
  have hA := renDetA_pos d L 1 T.hd
  have hκ0 : 0 ≤ 3 / 2 * T.κdec := by
    have := T.κdec_lower; have := T.κ0_nonneg; linarith
  have hconst := T.detConst_nonneg
  have hH : 0 ≤ hullConst d L ((T.κ - Real.log 2 - 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) / (2 * d * L))
      ((L : ℝ) ^ d * ((1 / 2 : ℝ) * N * covBLogMax d L T.κ /
          (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp T.κ)))) := by
    unfold hullConst; exact mul_nonneg hconst (Real.exp_pos _).le
  have hlam : 0 ≤ hullRate d L ((T.κ - Real.log 2 - 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) / (2 * d * L)) := by
    have h1 : 0 ≤ 3 / 2 * T.κdec + c1 d L * Real.log 2 := by
      have := one_le_c1 d L
      have : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      positivity
    have h2 : 3 / 2 * T.κdec + c1 d L * Real.log 2 ≤
        hullRate d L (detRateG d L T.κ) / renDetA d L 1 := by linarith
    have h3 := (le_div_iff₀ hA).1 h2
    exact le_trans (by positivity) h3
  refine ⟨E, hE, ?_, ?_, ?_⟩
  · intro z D hD
    obtain ⟨hS, hopt, hΔ, hG, hx⟩ := T.renDetFibre_root k hk N₁ hLN hN5 hν0 hν z
    have ht0 : ∀ X : Set (CTorus d L N₁ T.m₁ (k + 1)),
        ¬ (IsPolyDom 1 (k + 1) X ∧ ∃ x ∈ X, x ∈ X1 (lvTopG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) 1 k
          (fam 1 (blockSite k z))) → (E z).detGroupedC q D X = 0 := by
      intro X hX
      by_contra hne
      obtain ⟨hpoly, hroot⟩ := hanc z D hD X hne
      exact hX ⟨hpoly, blockSite k z, hroot (rootSite_mem_box_rootCube (m₀ := 1) (K := k + 1) z),
        hx⟩
    have h1 := sum_renRegroup hS hG ((E z).detGroupedC q D) ht0
    have h2 : ∑ X, (E z).detGroupedC q D X = ∑ X ∈ (Finset.univ : Finset (Finset
        (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1) Set.univ))).image
        (detCollarHullC q), (E z).detGroupedC q D X := by
      symm
      refine Finset.sum_subset (Finset.subset_univ _) fun X _ hX => ?_
      unfold DetExpansionLocC.detGroupedC detCollarGroupedC
      refine Finset.sum_eq_zero fun T' hT' => absurd ?_ hX
      rw [← mem_detCollarFibreC.1 hT']
      exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
    rw [← hsum z D hD, ← h2, ← h1]
  · intro z D hD Y
    obtain ⟨hS, hopt, hΔ, hG, hx⟩ := T.renDetFibre_root k hk N₁ hLN hN5 hν0 hν z
    have ht0 : ∀ X : Set (CTorus d L N₁ T.m₁ (k + 1)),
        ¬ (IsPolyDom 1 (k + 1) X ∧ ∃ x ∈ X, x ∈ X1 (lvTopG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) 1 k
          (fam 1 (blockSite k z))) → (E z).detGroupedC q D X = 0 := by
      intro X hX
      by_contra hne
      obtain ⟨hpoly, hroot⟩ := hanc z D hD X hne
      exact hX ⟨hpoly, blockSite k z, hroot (rootSite_mem_box_rootCube (m₀ := 1) (K := k + 1) z),
        hx⟩
    exact renRegroup_norm_le hS hG T.hd hopt hΔ ((E z).detGroupedC q D) hH hlam ht0
      (fun X hX _ => hbd z D hD X) hspec Y
  · intro z D D₂ hD hD₂ Y hY
    obtain ⟨hS, hopt, hΔ, hG, hx⟩ := T.renDetFibre_root k hk N₁ hLN hN5 hν0 hν z
    have hq1 : 1 ≤ q := by have := T.hL; omega
    have h3 : 3 ≤ L ^ (1 + T.m₁) :=
      calc 3 ≤ L := T.hL
        _ = L ^ 1 := (pow_one L).symm
        _ ≤ L ^ (1 + T.m₁) := Nat.pow_le_pow_right (by have := T.hL; omega) (by omega)
    refine Finset.sum_congr rfl fun X hX => ?_
    have hΦ := (Finset.mem_filter.1 hX).2
    refine (E z).detGroupedC_local hq1 (by have := T.hL; omega) hN h3 hD hD₂ fun v hv => hY v ?_
    rw [← hΦ, ← Finset.mem_coe]
    exact subset_renFibreMap hS hG hv

end StepTowerG

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
  classical
  have hN : (3 : ℕ) ^ 1 ∣ N₁ := by simpa using h3N
  have h := T.toG.renDetFibre_tower (q := 1) rfl (T.hhull_renDetFibre_toG hT) k hk N₁ h3N hN5
    hν0 (by simpa using hν) β p₁
  unfold StepTowerG.step at h
  rw [rhoSepG_three] at h
  dsimp only [StepTower.toG_m₁, StepTower.toG_κ, StepTower.toG_t, StepTower.toG_BG,
    StepTower.toG_δ, StepTower.toG_κdec] at h
  have e1 : (T.κ - Real.log 2 - 2 * Real.log ((detDeg 3 3 + 1 : ℕ) : ℝ)) /
      (2 * ((3 : ℕ) : ℝ) * ((3 : ℕ) : ℝ)) = towerDetRate T.κ := by
    unfold towerDetRate; norm_num
  have e2 : ((3 : ℕ) : ℝ) ^ 3 * ((1 / 2 : ℝ) * (2 : ℕ) * covBLogMax 3 3 T.κ /
      (1 - ((detDeg 3 3 + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp T.κ))) = towerDetConst T.κ :=
    StepTower.det_const_eq _ _
  rw [e1, e2] at h
  obtain ⟨E, hE, hsum, hbd, hloc⟩ := h
  have hC1 : ∀ z D X, (E z).detGroupedC 1 D X = (E z).detGrouped D X :=
    fun z D X => (E z).detGroupedC_one hN D X
  have hf : ∀ z (D : BgData (T.step k hk N₁ ν β p₁).G' 2),
      (E z).detGrouped D = (E z).detGroupedC 1 D :=
    fun z D => funext fun X => (hC1 z D X).symm
  refine ⟨E, hE, ?_, ?_, ?_⟩
  · intro z D hD
    refine Eq.trans (Finset.sum_congr rfl fun Y _ => ?_) (hsum z D hD)
    exact congrArg (fun f => renFibreTerm _ 1 _ f Y) (hf z D)
  · intro z D hD Y
    refine le_of_eq_of_le ?_ (hbd z D hD Y)
    exact congrArg (fun f => ‖renFibreTerm _ 1 _ f Y‖) (hf z D)
  · intro z D D₂ hD hD₂ Y hY
    refine Eq.trans (congrArg (fun f => renFibreTerm _ 1 _ f Y) (hf z D))
      (Eq.trans (hloc z D D₂ hD hD₂ Y hY) ?_)
    exact congrArg (fun f => renFibreTerm _ 1 _ f Y) (hf z D₂).symm

end Tower

end Balaban.Inhabited
