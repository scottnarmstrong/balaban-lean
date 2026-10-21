/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseTwoTorusCov
public import Balaban.LargeField.Base.BaseXSqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The first step's shifted covariance and its square root on two tori

For the whole-lattice generating set `levelGS 1` of two first-step tori `CTorus d L N₁ m₁ 1` and
`CTorus d L N₁' m₁ 1`, identified on a centred box by `boxMap`, the shifted covariance
`(1 + x)⁻¹ P_e + Ĝ_{0,s} - Π_{0,s}` of `BaseXCov` (the x-variant chain at `x' = 0` and mass
`ν + x`) has rows that correspond at the sites of a set `Y` of the box when the data correspond on
the reading set of `baseCovX_exact` (LFR D-IV.9, the localized rows): sets `Sr ⊆ Y` such that every
active interaction cube lies inside `Sr` or is disjoint from `Y`, `Y` contains the neighbours of
`Sr` in the lattice and in the layer blocks, the parameters correspond on the cubes inside `Sr`,
the potentials on `Sr`, the fields on `Y`.

* `basePart_mulVec_rows`: the rows of `P_e` at a site read only the field at that site;
* `baseCovX_mulVec_rows_twoTorus`: the vector form of the correspondence at the sites of `Y`;
* `baseCovX_rows_twoTorus`: the entries at two sites of `Y` correspond, uniformly in `x`
  (`x` enters only through the mass `ν + x` of the cover setting; no bound on `x` is used);
* `baseCovX_sqrt_rows_twoTorus`: the same for the Stieltjes square root
  `π⁻¹ ∫₀^∞ x^{-1/2} C_x(s) dx`, the integrands agreeing for every `x > 0`.
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.LargeField.Base.XC

open Balaban Balaban.Localization Balaban.Fluctuation Balaban.SmallField.Def6 Balaban.Polymer
  Balaban.Multiscale
  Balaban.Background Matrix Balaban.Polymer.TwoTorusStep

section Part

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}

/-- **The rows of `P_e` read only the field at the site**:
`(P_e w)(y, i) = e_y(i) ∑_j e_y(j) w(y, j)`. -/
theorem basePart_mulVec_rows (e : ι → Fin N → ℂ) (w : ι × Fin N → ℂ) (y : ι) (i : Fin N) :
    (basePart e *ᵥ w) (y, i) = e y i * ∑ j, e y j * w (y, j) := by
  unfold basePart
  rw [← Matrix.mulVec_mulVec, fieldMul_mulVec, fieldMul_transpose_mulVec]

end Part

section TwoTori

variable {d L N₁ N₁' m₁ N : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ : ℝ} {Cx : ℝ}

set_option hygiene false in
local notation "bm" => boxMap ((N₁ * L ^ m₁) * L ^ 1) ((N₁' * L ^ m₁) * L ^ 1)
set_option hygiene false in
local notation "GA" => levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := 1) (ϱ := ϱ) 1 le_rfl
set_option hygiene false in
local notation "GB" => levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := 1) (ϱ := ϱ) 1 le_rfl
set_option hygiene false in
local notation "ιb" x:max => Subtype.mk (bm (x : Balaban.Localization.CTorus d L N₁ m₁ 1))
  (levelGS_mem_Ω_one (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (K := 1) (ϱ := ϱ)
    (le_refl 1) le_rfl _)

variable {a : ℕ → ℝ} {aT ν x κ δ : ℝ}
  {Sr Y : Finset (Balaban.Localization.CTorus d L N₁ m₁ 1)} {R : ℕ}
  {s : ℕ × Balaban.Localization.CTorus d L N₁ m₁ 1 → ℂ}
  {s' : ℕ × Balaban.Localization.CTorus d L N₁' m₁ 1 → ℂ}
  {α : (GA).Ω 1 → ℂ} {α' : (GB).Ω 1 → ℂ}
  {φ : Balaban.Localization.CTorus d L N₁ m₁ 1 → Fin N → ℂ}
  {φ' : Balaban.Localization.CTorus d L N₁' m₁ 1 → Fin N → ℂ}

/-- **The neighbourhood hypothesis transfers to the second torus.**  Let `Sr ⊆ Y` be sets of sites
of the box of radius `R` such that `Y` contains the lattice neighbours and layer-block mates of
the sites of `Sr` on the first torus.  Then `bm '' Y` contains those of the sites of `bm '' Sr` on
the second torus: `boxMap` commutes with the lattice translations inside the box, and a site of
the second torus in the `L`-block of an image lies in the image of a site of the box of radius
`R + L` (`inBox_of_jBlock_eq`, `jBlock_boxMap_iff`). -/
theorem nbr_image_twoTorus (hSY : Sr ⊆ Y) (hYR : ∀ y ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ 1) y)
    (hn : 4 * R + 12 * L ^ (1 + m₁) + 3 * L ^ 1 + 5 < (N₁ * L ^ m₁) * L ^ 1)
    (hn' : 4 * R + 12 * L ^ (1 + m₁) + 3 * L ^ 1 + 5 < (N₁' * L ^ m₁) * L ^ 1)
    (hnbr : ∀ p q : (GA).Ω 1, (p : Balaban.Localization.CTorus d L N₁ m₁ 1) ∈ Sr →
    ((q : Balaban.Localization.CTorus d L N₁ m₁ 1) = p ∨
      (∃ μ : Fin d, (q : Balaban.Localization.CTorus d L N₁ m₁ 1) =
          (p : Balaban.Localization.CTorus d L N₁ m₁ 1) + Pi.single μ 1 ∨
        (q : Balaban.Localization.CTorus d L N₁ m₁ 1) =
          (p : Balaban.Localization.CTorus d L N₁ m₁ 1) - Pi.single μ 1) ∨
      (q : Balaban.Localization.CTorus d L N₁ m₁ 1) ∈
        (GA).blk ((GA).layerIndex (p : Balaban.Localization.CTorus d L N₁ m₁ 1)) p) →
    (q : Balaban.Localization.CTorus d L N₁ m₁ 1) ∈ Y) :
    ∀ p q : (GB).Ω 1, (p : Balaban.Localization.CTorus d L N₁' m₁ 1) ∈ Sr.image bm →
    ((q : Balaban.Localization.CTorus d L N₁' m₁ 1) = p ∨
      (∃ μ : Fin d, (q : Balaban.Localization.CTorus d L N₁' m₁ 1) =
          (p : Balaban.Localization.CTorus d L N₁' m₁ 1) + Pi.single μ 1 ∨
        (q : Balaban.Localization.CTorus d L N₁' m₁ 1) =
          (p : Balaban.Localization.CTorus d L N₁' m₁ 1) - Pi.single μ 1) ∨
      (q : Balaban.Localization.CTorus d L N₁' m₁ 1) ∈
        (GB).blk ((GB).layerIndex (p : Balaban.Localization.CTorus d L N₁' m₁ 1)) p) →
    (q : Balaban.Localization.CTorus d L N₁' m₁ 1) ∈ Y.image bm := by
  classical
  have hL1 : 1 ≤ L ^ 1 := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (NeZero.ne L))
  have hLL : L ^ 1 ≤ L ^ (1 + m₁) := Nat.pow_le_pow_right (Nat.pos_of_ne_zero (NeZero.ne L))
    (by omega)
  intro p q hp h
  obtain ⟨p0, hp0, hpe⟩ := Finset.mem_image.1 hp
  have hp0R := hYR p0 (hSY hp0)
  let P0 : (GA).Ω 1 := ⟨p0, levelGS_mem_Ω_one (le_refl 1) le_rfl _⟩
  have hP0 : (P0 : Balaban.Localization.CTorus d L N₁ m₁ 1) ∈ Sr := hp0
  rcases h with h | ⟨μ, h | h⟩ | h
  · rw [h, ← hpe]; exact Finset.mem_image_of_mem _ (hSY hp0)
  · let Q0 : (GA).Ω 1 := ⟨p0 + Pi.single μ 1, levelGS_mem_Ω_one (le_refl 1) le_rfl _⟩
    have hQ := hnbr P0 Q0 hP0 (Or.inr (Or.inl ⟨μ, Or.inl rfl⟩))
    have : (q : Balaban.Localization.CTorus d L N₁' m₁ 1) = bm (p0 + Pi.single μ 1) := by
      rw [boxMap_add_single (ρ := R) (by omega) (by omega) hp0R μ, hpe, h]
    rw [this]; exact Finset.mem_image_of_mem _ hQ
  · let Q0 : (GA).Ω 1 := ⟨p0 - Pi.single μ 1, levelGS_mem_Ω_one (le_refl 1) le_rfl _⟩
    have hQ := hnbr P0 Q0 hP0 (Or.inr (Or.inl ⟨μ, Or.inr rfl⟩))
    have : (q : Balaban.Localization.CTorus d L N₁' m₁ 1) = bm (p0 - Pi.single μ 1) := by
      rw [boxMap_sub_single (ρ := R) (by omega) (by omega) hp0R μ, hpe, h]
    rw [this]; exact Finset.mem_image_of_mem _ hQ
  · -- the layer block of the image
    obtain ⟨h1, h2, hl⟩ := (GB).layerIndex_spec p.2
    have hn1 : (GB).layerIndex (p : Balaban.Localization.CTorus d L N₁' m₁ 1) = 1 := by omega
    rw [hn1] at h
    have hbl := GeneratingSet.mem_blk.1 h
    have hpB : InBox d R ((N₁' * L ^ m₁) * L ^ 1) (p : Balaban.Localization.CTorus d L N₁' m₁ 1) := by
      rw [← hpe]; exact inBox_boxMap (by omega) hp0R
    have hqB : InBox d (R + L ^ 1) ((N₁' * L ^ m₁) * L ^ 1) (q : Balaban.Localization.CTorus d L N₁' m₁ 1) :=
      inBox_of_jBlock_eq (k := 0) (N₁ := N₁') (m := 1) (by omega)
        (by have h1 : L ^ (0 + 1) = L ^ 1 := rfl; rw [h1]; omega) hpB hbl
    set q0 : Balaban.Localization.CTorus d L N₁ m₁ 1 :=
      boxMap ((N₁' * L ^ m₁) * L ^ 1) ((N₁ * L ^ m₁) * L ^ 1) q with hq0
    have hq0R : InBox d (R + L ^ 1) ((N₁ * L ^ m₁) * L ^ 1) q0 := inBox_boxMap (by omega) hqB
    have hqq : bm q0 = q := boxMap_boxMap (by omega) hqB
    have hjb := (jBlock_boxMap_iff (K := 1) (j := 1) (N₁' := N₁') (ρ := R + L ^ 1) le_rfl
      (by omega) (by omega) hq0R (inBox_mono (by omega) hp0R)).2
      (by rw [hqq, hpe]; exact hbl)
    let Q0 : (GA).Ω 1 := ⟨q0, levelGS_mem_Ω_one (le_refl 1) le_rfl _⟩
    have hQ := hnbr P0 Q0 hP0 (Or.inr (Or.inr (by
      obtain ⟨g1, g2, gl⟩ := (GA).layerIndex_spec P0.2
      have gn : (GA).layerIndex (P0 : Balaban.Localization.CTorus d L N₁ m₁ 1) = 1 := by omega
      rw [gn]; exact GeneratingSet.mem_blk.2 hjb)))
    rw [← hqq]; exact Finset.mem_image_of_mem _ hQ

section Vec

variable (hCx : 0 ≤ Cx) (hκ : 0 ≤ κ)
  (hM : Dec2.cstarX d L Cx * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) (hδ : 0 ≤ δ)
  (hsm : δ ^ 2 * smallConstX d L κ ≤ 1 / 4)
  (hαA : AdmPot (GA) α) (hαB : AdmPot (GB) α')
  (hs : ∀ P, ‖s P‖ ≤ Real.exp κ) (hs' : ∀ P, ‖s' P‖ ≤ Real.exp κ)
  (hφA : IsConstraintField (GA) δ φ) (hφB : IsConstraintField (GB) δ φ')
  (hSY : Sr ⊆ Y) (hYR : ∀ y ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ 1) y)
  (hn : 4 * R + 12 * L ^ (1 + m₁) + 3 * L ^ 1 + 5 < (N₁ * L ^ m₁) * L ^ 1)
  (hn' : 4 * R + 12 * L ^ (1 + m₁) + 3 * L ^ 1 + 5 < (N₁' * L ^ m₁) * L ^ 1)
  (hα : ∀ y : (GA).Ω 1, (y : Balaban.Localization.CTorus d L N₁ m₁ 1) ∈ Sr → α' (ιb y) = α y)
  (hdich : ∀ q ∈ (coverOf (GA)).cubeIdx, (coverOf (GA)).sProd s q ≠ 0 →
    SubI (GA) (intBox q) Sr ∨ DisjI (GA) (intBox q) Y)
  (hdich' : ∀ q ∈ (coverOf (GB)).cubeIdx, (coverOf (GB)).sProd s' q ≠ 0 →
    SubI (GB) (intBox q) (Sr.image bm) ∨ DisjI (GB) (intBox q) (Y.image bm))
  (hnbr : ∀ p q : (GA).Ω 1, (p : Balaban.Localization.CTorus d L N₁ m₁ 1) ∈ Sr →
    ((q : Balaban.Localization.CTorus d L N₁ m₁ 1) = p ∨
      (∃ μ : Fin d, (q : Balaban.Localization.CTorus d L N₁ m₁ 1) =
          (p : Balaban.Localization.CTorus d L N₁ m₁ 1) + Pi.single μ 1 ∨
        (q : Balaban.Localization.CTorus d L N₁ m₁ 1) =
          (p : Balaban.Localization.CTorus d L N₁ m₁ 1) - Pi.single μ 1) ∨
      (q : Balaban.Localization.CTorus d L N₁ m₁ 1) ∈
        (GA).blk ((GA).layerIndex (p : Balaban.Localization.CTorus d L N₁ m₁ 1)) p) →
    (q : Balaban.Localization.CTorus d L N₁ m₁ 1) ∈ Y)
  (hagree : ∀ q ∈ innerCentres (GA) Sr,
    (coverOf (GB)).sProd s' (Prod.map id bm q) = (coverOf (GA)).sProd s q)
  (hφ : ∀ u ∈ Y, φ' (bm u) = φ u)
include hCx hκ hM hδ hsm hαA hαB hs hs' hφA hφB hSY hYR hn hn' hα hdich hdich' hnbr
  hagree hφ

/-- **The vector form of the correspondence of the shifted covariance on two tori.**  Under the
reading hypotheses of `baseCovX_exact` (stated on both tori), for vectors `w`, `w'` corresponding
on `Y`, the shifted covariances `(1 + x)⁻¹ P_e + Ĝ_{0,s} - Π_{0,s}` of the two tori applied to
them correspond at every site of `Y`. -/
theorem baseCovX_mulVec_rows_twoTorus (SA : Dec2.XCover (coverOf (GA)) (GA) a aT (ν + x) Cx)
    (SB : Dec2.XCover (coverOf (GB)) (GB) a aT (ν + x) Cx) {w : (GA).Ω 1 × Fin N → ℂ} {w' : (GB).Ω 1 × Fin N → ℂ}
    (hw : ∀ y : (GA).Ω 1, (y : Balaban.Localization.CTorus d L N₁ m₁ 1) ∈ Y → ∀ i,
      w' (ιb y, i) = w (y, i))
    (y : (GA).Ω 1) (hy : (y : Balaban.Localization.CTorus d L N₁ m₁ 1) ∈ Y) (i : Fin N) :
    (((1 + (x : ℂ))⁻¹ • basePart (restrictField (GB) φ') +
        liftOp N (Dec2.Gsx (coverOf (GB)) (GB) a aT 0 (ν + x) α' s') -
        Dec2.decPi (coverOf (GB)) (GB) a aT 0 (ν + x) α' s' φ') *ᵥ w') (ιb y, i) =
      (((1 + (x : ℂ))⁻¹ • basePart (restrictField (GA) φ) +
        liftOp N (Dec2.Gsx (coverOf (GA)) (GA) a aT 0 (ν + x) α s) -
        Dec2.decPi (coverOf (GA)) (GA) a aT 0 (ν + x) α s φ) *ᵥ w) (y, i) := by
  have DA : Dec2.XData (coverOf (GA)) (GA) a aT (ν + x) 0 α κ s Cx := ⟨SA, hCx, hαA, le_rfl, hκ, hM, hs⟩
  have DB : Dec2.XData (coverOf (GB)) (GB) a aT (ν + x) 0 α' κ s' Cx :=
    ⟨SB, hCx, hαB, le_rfl, hκ, hM, hs'⟩
  have hMA := decM_isUnit_cover DA hφA hδ hsm
  have hMB := decM_isUnit_cover DB hφB hδ hsm
  have hrow : ∀ z y : (GA).Ω 1, (z : Balaban.Localization.CTorus d L N₁ m₁ 1) ∈ Sr →
      xDirichletOperator (GA) a aT 0 (ν + x) α z y ≠ 0 →
      (y : Balaban.Localization.CTorus d L N₁ m₁ 1) ∈ Y :=
    fun p q hp hpq => hnbr p q hp (xDirichlet_row_cases α hpq)
  have hrow' : ∀ z y : (GB).Ω 1, (z : Balaban.Localization.CTorus d L N₁' m₁ 1) ∈ Sr.image bm →
      xDirichletOperator (GB) a aT 0 (ν + x) α' z y ≠ 0 →
      (y : Balaban.Localization.CTorus d L N₁' m₁ 1) ∈ Y.image bm :=
    fun p q hp hpq => nbr_image_twoTorus hSY hYR hn hn' hnbr p q hp (xDirichlet_row_cases α' hpq)
  have hZ := decZ_rows_Sr (k := 0) (x₀ := 0) SA SB le_rfl hSY hYR hn hn' hαA hαB hα
    DA.isUnit_one_sub DB.isUnit_one_sub hdich hdich' hrow hrow' hagree hφ hMA hMB
    (w := w) (w' := w') (fun y hy i => hw y (hSY hy) i) y hy i
  have hP : (basePart (restrictField (GB) φ') *ᵥ w') (ιb y, i) =
      (basePart (restrictField (GA) φ) *ᵥ w) (y, i) := by
    rw [basePart_mulVec_rows, basePart_mulVec_rows]
    have e1 : φ' (bm (y : Balaban.Localization.CTorus d L N₁ m₁ 1)) = φ y := hφ _ hy
    simp only [restrictField]
    rw [e1]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hw y hy j]
  have e : ∀ {N₁ : ℕ} [NeZero N₁] {G : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ}
      (β : G.Ω 1 → ℂ) (σ : ℕ × Balaban.Localization.CTorus d L N₁ m₁ 1 → ℂ)
      (ψ : Balaban.Localization.CTorus d L N₁ m₁ 1 → Fin N → ℂ),
      ((1 + (x : ℂ))⁻¹ • basePart (restrictField G ψ) +
        liftOp N (Dec2.Gsx (coverOf G) G a aT 0 (ν + x) β σ) -
        Dec2.decPi (coverOf G) G a aT 0 (ν + x) β σ ψ) =
      (1 + (x : ℂ))⁻¹ • basePart (restrictField G ψ) + decZ G a aT 0 (ν + x) β σ ψ :=
    fun _ _ _ => baseCovX_eq_add_decZ
  rw [e, e, Matrix.add_mulVec, Matrix.add_mulVec, Pi.add_apply, Pi.add_apply, Matrix.smul_mulVec,
    Matrix.smul_mulVec, Pi.smul_apply, Pi.smul_apply, hP, hZ]

/-- **The rows of the shifted covariance correspond on two tori** (entries at two sites of `Y`).
Under the reading hypotheses of `baseCovX_exact`, the entries at `((y, i), (z, j))`, `y, z ∈ Y`, of
the shifted covariance `(1 + x)⁻¹ P_e + Ĝ_{0,s} - Π_{0,s}` of the two tori correspond under
`boxMap`, for every mass shift `x` for which the cover setting holds. -/
theorem baseCovX_rows_twoTorus (SA : Dec2.XCover (coverOf (GA)) (GA) a aT (ν + x) Cx)
    (SB : Dec2.XCover (coverOf (GB)) (GB) a aT (ν + x) Cx) (y z : (GA).Ω 1)
    (hy : (y : Balaban.Localization.CTorus d L N₁ m₁ 1) ∈ Y)
    (hz : (z : Balaban.Localization.CTorus d L N₁ m₁ 1) ∈ Y) (i j : Fin N) :
    ((1 + (x : ℂ))⁻¹ • basePart (restrictField (GB) φ') +
        liftOp N (Dec2.Gsx (coverOf (GB)) (GB) a aT 0 (ν + x) α' s') -
        Dec2.decPi (coverOf (GB)) (GB) a aT 0 (ν + x) α' s' φ') (ιb y, i) (ιb z, j) =
      ((1 + (x : ℂ))⁻¹ • basePart (restrictField (GA) φ) +
        liftOp N (Dec2.Gsx (coverOf (GA)) (GA) a aT 0 (ν + x) α s) -
        Dec2.decPi (coverOf (GA)) (GA) a aT 0 (ν + x) α s φ) (y, i) (z, j) := by
  have hK1 : 1 ≤ L ^ 1 := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (NeZero.ne L))
  have hm' : 2 * R + 1 < (N₁' * L ^ m₁) * L ^ (0 + 1) := by
    have h1 : L ^ (0 + 1) = L ^ 1 := rfl
    rw [h1]; omega
  obtain ⟨hinj, -, -⟩ := boxMap_bij_Sr (ϱ := ϱ) (k := 0) (N₁' := N₁') (T := Y) hYR hm'
  refine (mulVec_single_entry _ (ιb y, i) (ιb z, j)).symm.trans
    (Eq.trans ?_ (mulVec_single_entry _ (y, i) (z, j)))
  refine baseCovX_mulVec_rows_twoTorus SA SB (hCx := hCx) (hκ := hκ) (hM := hM) (hδ := hδ)
    (hsm := hsm) (hαA := hαA) (hαB := hαB) (hs := hs) (hs' := hs') (hφA := hφA) (hφB := hφB)
    (hSY := hSY) (hYR := hYR) (hn := hn) (hn' := hn') (hα := hα) (hdich := hdich)
    (hdich' := hdich') (hnbr := hnbr) (hagree := hagree) (hφ := hφ)
    (w := Pi.single (z, j) 1)
    (w' := Pi.single (ιb z, j) 1) (fun u hu i' => ?_) y hy i
  by_cases huz : u = z
  · subst huz
    by_cases hij : i' = j <;> simp [hij]
  · have : (ιb u : (GB).Ω 1) ≠ ιb z := fun h => huz (hinj u z hu hz h)
    simp [huz, this]

open MeasureTheory Set in
/-- **The Stieltjes square root of the shifted covariance on two tori.**  Under the reading
hypotheses of `baseCovX_exact` (stated on both tori; they do not involve the shift), the entries at
two sites of `Y` of `π⁻¹ ∫₀^∞ x^{-1/2} C_x(s) dx` correspond under `boxMap`: the integrands agree
for every `x > 0` (`baseCovX_rows_twoTorus` at the cover setting of mass `ν + x`). -/
theorem baseCovX_sqrt_rows_twoTorus (SA : Dec2.XCover (coverOf (GA)) (GA) a aT ν Cx)
    (SB : Dec2.XCover (coverOf (GB)) (GB) a aT ν Cx) (y z : (GA).Ω 1)
    (hy : (y : Balaban.Localization.CTorus d L N₁ m₁ 1) ∈ Y)
    (hz : (z : Balaban.Localization.CTorus d L N₁ m₁ 1) ∈ Y) (i j : Fin N) :
    ((1 / Real.pi : ℝ) : ℂ) * ∫ x in Ioi (0 : ℝ), ((x ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        ((1 + (x : ℂ))⁻¹ • basePart (restrictField (GB) φ') +
          liftOp N (Dec2.Gsx (coverOf (GB)) (GB) a aT 0 (ν + x) α' s') -
          Dec2.decPi (coverOf (GB)) (GB) a aT 0 (ν + x) α' s' φ') (ιb y, i) (ιb z, j) =
      ((1 / Real.pi : ℝ) : ℂ) * ∫ x in Ioi (0 : ℝ), ((x ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        ((1 + (x : ℂ))⁻¹ • basePart (restrictField (GA) φ) +
          liftOp N (Dec2.Gsx (coverOf (GA)) (GA) a aT 0 (ν + x) α s) -
          Dec2.decPi (coverOf (GA)) (GA) a aT 0 (ν + x) α s φ) (y, i) (z, j) := by
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  rw [baseCovX_rows_twoTorus (xCover_add_mass SA (mem_Ioi.mp hx).le)
    (xCover_add_mass SB (mem_Ioi.mp hx).le) (hCx := hCx) (hκ := hκ) (hM := hM) (hδ := hδ)
    (hsm := hsm) (hαA := hαA) (hαB := hαB) (hs := hs) (hs' := hs') (hφA := hφA) (hφB := hφB)
    (hSY := hSY) (hYR := hYR) (hn := hn) (hn' := hn') (hα := hα) (hdich := hdich)
    (hdich' := hdich') (hnbr := hnbr) (hagree := hagree) (hφ := hφ) y z hy hz
    i j]

end Vec

end TwoTori

end Balaban.LargeField.Base.XC
