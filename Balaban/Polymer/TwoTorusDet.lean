/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusDecCov
public import Balaban.Fluctuation.DetCauchyBgActivity
public import Balaban.Fluctuation.RowsCompose

/-!
# The determinant terms on two tori

For the top level `levelGS (k + 1)` of two fine tori `CTorus d L N₁ m₁ (k + 1)` and
`CTorus d L N₁' m₁ (k + 1)`, identified on a centred box by `boxMap` (`bm` on the fine tori, `bU`
on the unit lattices, `cubeMap` on the level-`(k+1)` cubes), this file compares the terms of the
rooted determinant expansion `detActivityBg` (`Fluctuation/DetCauchyBgActivity`).

## D1: the decoupled logarithm

* `unitImage_inj`: the map `ιu` of unit points is injective on unit points with a fine site in the
  box.
* `decLog_diag_transport`: the diagonal entries of
  `𝕃(s) = log a_k (1 - P) + log (a_k + b) P - ∫₀^∞ (C_x(s) - A_{k,x}) dx` (`decLog`) agree at
  corresponding unit points whose `(k+1)`-block lies in a component `Y` of the cut, under the
  hypotheses of `decCov_rows_transport` for every `x ≥ 0`; `decLog_rows_transport`: the same for
  the rows of `𝕃(s) h`; `rootTrace_single_transport`: the rooted trace of one unit block.

## D2: the background inputs

* `rowsCov_R_mem_Y_and_rowsDep`: the sites `R(S_Y)` read by the `x`-variant rows lie in `Y`, and
  their approximate-field footprints lie in `RowsDep (S_Y)`.
* `decBg_inputs_twoTorus`: from raw data agreeing on `RowsDep (S_Y)`, the decoupled multipliers
  correspond on `S_Y` and the extended decoupled fields `barField D.Ψ (decBgField)` on `R(S_Y)`
  (the hypotheses `hα`, `hφR` of D1), via `decBg_component_unique` at `j = K = k + 1`.

## D3: the rooted trace, its mixed differences and the activity

* `rootTraceBg_single_twoTorus`: `rootTraceBg {b} D s` on two tori, for one cut configuration.
* `rootTraceBg_cutPt_twoTorus`: the same at the cut points `1_I`, `1_{I'}` of corresponding sets of
  parameter cubes in the box, with raw data agreeing on a box (`inBox_of_rowsDep_top`).
* `mixDiff_rootTraceBg_twoTorus`: the mixed differences `Δ_J`, `Δ_{J'}` agree.
* `piHull_boxMap`, `hullSet_image_top`, `hullOf_image_top`: the hull of `(ιu y, J')` is the
  `cubeMap`-image of the hull of `(y, J)`.
* `detActivityBg_twoTorus`: the activity of a polymer `Y` (in the box, containing the root cube of
  `y`) equals the activity of `cubeMap '' Y` on the second torus.

The statements hold at cut parameter vectors only (the parameters vanish on the parameter cubes off
the selected family); the determinant activity only evaluates the decoupled logarithm at cut
points, so no value at `s ≡ 1` is compared.
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Polymer.TwoTorusStep

open Balaban Balaban.Localization Balaban.Fluctuation Balaban.SmallField Balaban.SmallField.Def6
  Balaban.Polymer Balaban.Multiscale Balaban.Background Balaban.Analysis Matrix

/-! ### D1: the diagonal of the decoupled logarithm on two tori -/

section LogRows

open MeasureTheory Set

variable {d L N₁ N₁' m₁ k N : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ : ℝ}

set_option hygiene false in
local notation "bm" => boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1))
set_option hygiene false in
local notation "bU" => boxMap ((N₁ * L ^ m₁) * L ^ (k + 1 - k)) ((N₁' * L ^ m₁) * L ^ (k + 1 - k))
set_option hygiene false in
local notation "GA" => levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  (k + 1) le_rfl
set_option hygiene false in
local notation "GB" => levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  (k + 1) le_rfl
set_option hygiene false in
local notation "ιb" x:max => Subtype.mk (bm (x : CTorus d L N₁ m₁ (k + 1)))
  (levelGS_mem_Ω_one (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (K := k + 1) (ϱ := ϱ)
    (Nat.le_add_left 1 k) le_rfl _)
set_option hygiene false in
local notation "ιu" b:max => Subtype.mk (bU (b : UnitTorus d L N₁ m₁ k))
  (mem_unitPts_levelTop (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := k) (ϱ := ϱ) _)

/-- **The unit points of the box are carried injectively.**  Two unit points with fine sites in
the box of radius `ρ` have the same image only if they are equal.  Margin:
`2 ρ + 3 L^(k+1) + 5 < N₁ L^m₁ L^(k+1)` (and for `N₁'`). -/
theorem unitImage_inj {ρ : ℕ} (hn : 2 * ρ + 3 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 2 * ρ + 3 * L ^ (k + 1) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1))
    {b1 b2 : unitPts (GA)} {y1 y2 : CTorus d L N₁ m₁ (k + 1)}
    (hy1 : unitBlock y1 = (b1 : UnitTorus d L N₁ m₁ k))
    (hy2 : unitBlock y2 = (b2 : UnitTorus d L N₁ m₁ k))
    (hy1R : InBox d ρ ((N₁ * L ^ m₁) * L ^ (k + 1)) y1)
    (hy2R : InBox d ρ ((N₁ * L ^ m₁) * L ^ (k + 1)) y2)
    (h : ((ιu b1) : unitPts (GB)) = ιu b2) : b1 = b2 := by
  have e := congrArg Subtype.val h
  rw [unitImage_val (N₁' := N₁') hn b1 hy1 hy1R, unitImage_val (N₁' := N₁') hn b2 hy2 hy2R] at e
  have e2 := (jBlock_boxMap_iff (m₁ := m₁) (j := k) (Nat.le_succ k) hn hn' hy1R hy2R).2 e
  exact Subtype.ext (hy1.symm.trans (e2.trans hy2))

omit [NeZero N₁'] in
/-- The diagonal entries of `(1 - P)` and `P` (lifted to `N` components) do not depend on the unit
point: `P_{bb} = L^{-d}`. -/
theorem liftOp_unitP_diag (b : unitPts (GA)) (i : Fin N) :
    liftOp N (unitP (GA)) (b, i) (b, i) = (((((L ^ 1 : ℕ) : ℝ) ^ d)⁻¹ : ℝ) : ℂ) := by
  simp [liftOp, unitP]

/-- The diagonal entries of `A_{k,x}` at corresponding unit points agree. -/
theorem covA_unit_diag_transport (c bb x₀ : ℝ) (b : unitPts (GA)) (i : Fin N) :
    covA c bb x₀ (liftOp N (unitP (GB))) (ιu b, i) (ιu b, i) =
      covA c bb x₀ (liftOp N (unitP (GA))) (b, i) (b, i) := by
  have h1 := liftOp_unitP_diag (N := N) b i
  have h2 := liftOp_unitP_diag (N := N) (N₁ := N₁') (ϱ := ϱ) (ιu b) i
  simp only [covA, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply_eq,
    smul_eq_mul]
  rw [h1, h2]

/-- A diagonal entry is the row of the matrix applied to the unit vector of the entry. -/
theorem entry_eq_mulVec_single {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ)
    (p : ι) : M p p = (M *ᵥ Pi.single p 1) p := by
  simp

/-- **D1: the diagonal of the decoupled logarithm `𝕃(s)` on two tori.**  Under the hypotheses of
`decCov_rows_transport` for every `x ≥ 0` (the component `Y` with its image `Y'`, the block sets,
the cut factors, the multipliers on `S_Y`, the fields on `R(S_Y)`, the data `XData` at every
`x ≥ 0`), the diagonal entries of `𝕃(s)` at a unit point whose `(k+1)`-block lies in `Y` and at its
image agree.  The logarithmic terms are the same constants on both tori; the integrand
`C_x(s) - A_{k,x}` has corresponding diagonal entries for every `x > 0` (`decCov_rows_transport`
applied to the unit vectors, which correspond by `unitImage_inj`).  No integrability is used: the
two integrands agree pointwise on `(0, ∞)`.  Margin:
`4 R + 12 L^(k+1+m₁) + 3 L^(k+1) + 5 < N₁ L^m₁ L^(k+1)` (and for `N₁'`). -/
theorem decLog_diag_transport {a : ℕ → ℝ} {aT ν δ κ : ℝ}
    {X₁ Y : Finset (CTorus d L N₁ m₁ (k + 1))} {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ (k + 1))}
    {X₁' Y' : Finset (CTorus d L N₁' m₁ (k + 1))} {𝒞' : Finset (ℕ × CTorus d L N₁' m₁ (k + 1))}
    (hconn : HatConn (GA)) (hconn' : HatConn (GB))
    (hY : IsNnComp ((Vset X₁ 𝒞).filter fun x => x ∈ (GA).Ω 1) Y)
    (hYc : IsNnComp ((Vset X₁' 𝒞').filter fun x => x ∈ (GB).Ω 1) Y')
    {s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ} {s' : ℕ × CTorus d L N₁' m₁ (k + 1) → ℂ}
    (hs0 : ∀ P ∈ parCubes (GA) X₁, P ∉ 𝒞 → s P = 0)
    (hs0' : ∀ P ∈ parCubes (GB) X₁', P ∉ 𝒞' → s' P = 0)
    (hY' : Y.image bm = Y') (hB' : (SY (GA) X₁ 𝒞 Y).image bm = SY (GB) X₁' 𝒞' Y')
    (hagree : ∀ q ∈ innerCentres (GA) (SY (GA) X₁ 𝒞 Y),
      sProd (GB) s' (Prod.map id bm q) = sProd (GA) s q)
    {R : ℕ} (hYR : ∀ x ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    (hn : 4 * R + 12 * L ^ (k + 1 + m₁) + 3 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 4 * R + 12 * L ^ (k + 1 + m₁) + 3 * L ^ (k + 1) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1))
    {α : (GA).Ω 1 → ℂ} {α' : (GB).Ω 1 → ℂ}
    (hα : ∀ x : (GA).Ω 1, (x : CTorus d L N₁ m₁ (k + 1)) ∈ SY (GA) X₁ 𝒞 Y → α' (ιb x) = α x)
    {φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ} {φ' : CTorus d L N₁' m₁ (k + 1) → Fin N → ℂ}
    (hφR : ∀ u ∈ rowsCov_R (GA) a aT ν α X₁ 𝒞 Y, φ' (bm u) = φ u)
    (hfam : ∀ x, 0 ≤ x → XData (GA) a aT ν x α κ s)
    (hfam' : ∀ x, 0 ≤ x → XData (GB) a aT ν x α' κ s')
    (hφ : IsConstraintField (GA) δ φ) (hφ' : IsConstraintField (GB) δ φ') (hδ : 0 ≤ δ)
    (hsm : δ ^ 2 * smallConstX d L κ ≤ 1 / 4)
    {b : unitPts (GA)} (hb : UnitOut (GA) Y b) (i : Fin N) :
    decLog (GB) a aT ν α' s' φ' (unitQ (GB)) (unitP (GB)) (ιu b, i) (ιu b, i) =
      decLog (GA) a aT ν α s φ (unitQ (GA)) (unitP (GA)) (b, i) (b, i) := by
  classical
  have hj1 : 1 ≤ k + 1 := Nat.le_add_left 1 k
  have hKm : L ^ (k + 1) ≤ L ^ (k + 1 + m₁) :=
    Nat.pow_le_pow_right (Nat.pos_of_ne_zero (NeZero.ne L)) (Nat.le_add_right _ _)
  have hK1 : 1 ≤ L ^ (k + 1) := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (NeZero.ne L))
  have hnu : 2 * (R + L ^ (k + 1)) + 3 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1) := by
    omega
  have hnu' : 2 * (R + L ^ (k + 1)) + 3 * L ^ (k + 1) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1) := by
    omega
  have hSYY := SY_subset_levelGS (ϱ := ϱ) (X₁ := X₁) (𝒞 := 𝒞) (Y := Y) hj1 le_rfl
  -- every unit point read by the rows has a fine site in the box of radius `R + L^(k+1)`
  have hsite : ∀ b' : unitPts (GA), (UnitOut (GA) Y b' ∨ UnitIn (GA) X₁ 𝒞 Y b') →
      ∃ y : CTorus d L N₁ m₁ (k + 1), unitBlock y = (b' : UnitTorus d L N₁ m₁ k) ∧
        InBox d (R + L ^ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1)) y := by
    rintro b' (hb' | ⟨y, hy, hyb⟩)
    · obtain ⟨y, -, hy⟩ := (mem_unitPts _).1 b'.2
      exact ⟨y, hy, inBox_mono (Nat.le_add_right _ _)
        (hYR _ (hb' ⟨y, levelGS_mem_Ω_one hj1 le_rfl y⟩ (by rw [hy])))⟩
    · obtain ⟨y', hy', -, hy'R⟩ := unit_anchor (ϱ := ϱ) (by omega) (hYR _ (hSYY hy)) b'
        (hyb.symm.trans (unitBlock1_unitBlock _))
      exact ⟨y', hy', hy'R⟩
  obtain ⟨y0, hy0, hy0R⟩ := hsite b (Or.inl hb)
  have hh : ∀ b' : unitPts (GA), (UnitOut (GA) Y b' ∨ UnitIn (GA) X₁ 𝒞 Y b') → ∀ j,
      (Pi.single (ιu b, i) (1 : ℂ) : unitPts (GB) × Fin N → ℂ) (ιu b', j) =
        (Pi.single (b, i) (1 : ℂ) : unitPts (GA) × Fin N → ℂ) (b', j) := by
    intro b' hb' j
    obtain ⟨y1, hy1, hy1R⟩ := hsite b' hb'
    by_cases e : (b', j) = (b, i)
    · simp only [Prod.mk.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      simp
    · have e' : ((ιu b', j) : unitPts (GB) × Fin N) ≠ (ιu b, i) := by
        intro h
        apply e
        have h1 := congrArg Prod.fst h
        have h2 := congrArg Prod.snd h
        simp only at h1 h2
        rw [unitImage_inj hnu hnu' hy1 hy0 hy1R hy0R h1, h2]
      rw [Pi.single_eq_of_ne e', Pi.single_eq_of_ne e]
  -- the integrands agree on `(0, ∞)`
  have hint : ∫ x in Ioi (0 : ℝ), (decCov (GB) a aT x ν α' s' φ' (unitQ (GB)) (unitP (GB)) -
        covA (a k) (aT / (L : ℝ) ^ 2) x (liftOp N (unitP (GB)))) (ιu b, i) (ιu b, i) =
      ∫ x in Ioi (0 : ℝ), (decCov (GA) a aT x ν α s φ (unitQ (GA)) (unitP (GA)) -
        covA (a k) (aT / (L : ℝ) ^ 2) x (liftOp N (unitP (GA)))) (b, i) (b, i) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    have hx0 : 0 ≤ x := (mem_Ioi.mp hx).le
    simp only [Matrix.sub_apply]
    rw [covA_unit_diag_transport, entry_eq_mulVec_single (decCov (GB) a aT x ν α' s' φ' _ _),
      entry_eq_mulVec_single (decCov (GA) a aT x ν α s φ _ _),
      decCov_rows_transport hconn hconn' hY hYc hs0 hs0' hY' hB' hagree hYR hn hn' hα hφR
        (hfam x hx0) (hfam' x hx0) hφ hφ' hδ hsm _ _ hh b hb i]
  simp only [Matrix.sub_apply] at hint
  unfold decLog
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_eq,
    smul_eq_mul, intMat]
  simp only [liftOp_unitP_diag]
  rw [hint]

/-- **D1, rows of `𝕃(s) h`.**  Under the hypotheses of `decLog_diag_transport`, if the inputs
correspond on the unit points read by the rows of `C_x(s)` (`UnitOut` or `UnitIn`), the rows of
`𝕃(s) h` and `𝕃(s') h'` correspond at every unit point whose `(k+1)`-block lies in `Y`.  The
projection term `P h` is read off from `A_{k,x} h` at `c = 1`, `b = 1`, `x = 0`
(`A h = h - P h / 2`); the integral term is `intMat_mulVec_apply` with the landed integrability
`integrable_decSub` and the rows of `C_x(s) - A_{k,x}` for every `x > 0`.  Margin as in
`decLog_diag_transport`. -/
theorem decLog_rows_transport {a : ℕ → ℝ} {aT ν δ κ : ℝ}
    {X₁ Y : Finset (CTorus d L N₁ m₁ (k + 1))} {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ (k + 1))}
    {X₁' Y' : Finset (CTorus d L N₁' m₁ (k + 1))} {𝒞' : Finset (ℕ × CTorus d L N₁' m₁ (k + 1))}
    (hconn : HatConn (GA)) (hconn' : HatConn (GB))
    (hY : IsNnComp ((Vset X₁ 𝒞).filter fun x => x ∈ (GA).Ω 1) Y)
    (hYc : IsNnComp ((Vset X₁' 𝒞').filter fun x => x ∈ (GB).Ω 1) Y')
    {s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ} {s' : ℕ × CTorus d L N₁' m₁ (k + 1) → ℂ}
    (hs0 : ∀ P ∈ parCubes (GA) X₁, P ∉ 𝒞 → s P = 0)
    (hs0' : ∀ P ∈ parCubes (GB) X₁', P ∉ 𝒞' → s' P = 0)
    (hY' : Y.image bm = Y') (hB' : (SY (GA) X₁ 𝒞 Y).image bm = SY (GB) X₁' 𝒞' Y')
    (hagree : ∀ q ∈ innerCentres (GA) (SY (GA) X₁ 𝒞 Y),
      sProd (GB) s' (Prod.map id bm q) = sProd (GA) s q)
    {R : ℕ} (hYR : ∀ x ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    (hn : 4 * R + 12 * L ^ (k + 1 + m₁) + 3 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 4 * R + 12 * L ^ (k + 1 + m₁) + 3 * L ^ (k + 1) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1))
    {α : (GA).Ω 1 → ℂ} {α' : (GB).Ω 1 → ℂ}
    (hα : ∀ x : (GA).Ω 1, (x : CTorus d L N₁ m₁ (k + 1)) ∈ SY (GA) X₁ 𝒞 Y → α' (ιb x) = α x)
    {φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ} {φ' : CTorus d L N₁' m₁ (k + 1) → Fin N → ℂ}
    (hφR : ∀ u ∈ rowsCov_R (GA) a aT ν α X₁ 𝒞 Y, φ' (bm u) = φ u)
    (hfam : ∀ x, 0 ≤ x → XData (GA) a aT ν x α κ s)
    (hfam' : ∀ x, 0 ≤ x → XData (GB) a aT ν x α' κ s')
    (hφ : IsConstraintField (GA) δ φ) (hφ' : IsConstraintField (GB) δ φ') (hδ : 0 ≤ δ)
    (hsm : δ ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (h : unitPts (GA) × Fin N → ℂ) (h' : unitPts (GB) × Fin N → ℂ)
    (hh : ∀ b' : unitPts (GA), (UnitOut (GA) Y b' ∨ UnitIn (GA) X₁ 𝒞 Y b') → ∀ i,
      h' (ιu b', i) = h (b', i))
    {b : unitPts (GA)} (hb : UnitOut (GA) Y b) (i : Fin N) :
    (decLog (GB) a aT ν α' s' φ' (unitQ (GB)) (unitP (GB)) *ᵥ h') (ιu b, i) =
      (decLog (GA) a aT ν α s φ (unitQ (GA)) (unitP (GA)) *ᵥ h) (b, i) := by
  classical
  have hj1 : 1 ≤ k + 1 := Nat.le_add_left 1 k
  have hKm : L ^ (k + 1) ≤ L ^ (k + 1 + m₁) :=
    Nat.pow_le_pow_right (Nat.pos_of_ne_zero (NeZero.ne L)) (Nat.le_add_right _ _)
  have hnu : 2 * R + 5 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1) := by omega
  have hnu' : 2 * R + 5 * L ^ (k + 1) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1) := by omega
  have Hs := (standing_pair hfam hφ hδ hsm).1
  have Hs' := (standing_pair hfam' hφ' hδ hsm).1
  -- a fine site of the block of `b`
  obtain ⟨y0, -, hy0⟩ := (mem_unitPts _).1 b.2
  have hy0Y : y0 ∈ Y := hb ⟨y0, levelGS_mem_Ω_one hj1 le_rfl y0⟩ (by rw [hy0])
  have hb0 : unitBlock1 (b : UnitTorus d L N₁ m₁ k) =
      jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) y0 := by
    rw [← hy0, unitBlock1_unitBlock]
  have hbo : ∀ b3 : unitPts (GA), unitBlock1 (b3 : UnitTorus d L N₁ m₁ k) =
      unitBlock1 (b : UnitTorus d L N₁ m₁ k) → ∀ j, h' (ιu b3, j) = h (b3, j) :=
    fun b3 h3 j => hh b3 (Or.inl fun y hy => hb y (hy.trans h3)) j
  -- the projection term
  have hP : (liftOp N (unitP (GB)) *ᵥ h') (ιu b, i) = (liftOp N (unitP (GA)) *ᵥ h) (b, i) := by
    have e := covA_unit_rows_transport (N := N) 1 1 0 hnu hnu' (hYR _ hy0Y) hb0 hbo i
    rw [covA_mulVec_eq, covA_mulVec_eq] at e
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hh b (Or.inl hb) i] at e
    norm_num at e
    linear_combination e
  -- the integral term
  have hint : ∫ x in Ioi (0 : ℝ), ((decCov (GB) a aT x ν α' s' φ' (unitQ (GB)) (unitP (GB)) -
        covA (a k) (aT / (L : ℝ) ^ 2) x (liftOp N (unitP (GB)))) *ᵥ h') (ιu b, i) =
      ∫ x in Ioi (0 : ℝ), ((decCov (GA) a aT x ν α s φ (unitQ (GA)) (unitP (GA)) -
        covA (a k) (aT / (L : ℝ) ^ 2) x (liftOp N (unitP (GA)))) *ᵥ h) (b, i) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    have hx0 : 0 ≤ x := (mem_Ioi.mp hx).le
    simp only [Matrix.sub_mulVec, Pi.sub_apply]
    rw [decCov_rows_transport hconn hconn' hY hYc hs0 hs0' hY' hB' hagree hYR hn hn' hα hφR
        (hfam x hx0) (hfam' x hx0) hφ hφ' hδ hsm h h' hh b hb i,
      covA_unit_rows_transport _ _ _ hnu hnu' (hYR _ hy0Y) hb0 hbo i]
  have e1 := intMat_mulVec_apply (integrable_decSub Hs) h (b, i)
  have e2 := intMat_mulVec_apply (integrable_decSub Hs') h' (ιu b, i)
  unfold decLog
  simp only [Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec, Pi.sub_apply,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.one_mulVec]
  rw [e1, e2, hint, hP, hh b (Or.inl hb) i]

/-- **D1 for the rooted trace of one unit block.**  The rooted trace
`-(1/2) ∑_i 𝕃(s)_{(b,i),(b,i)}` (`rootTrace` of `{b}`) at corresponding unit points, under the
hypotheses of `decLog_diag_transport` for the extended parameters `extS G s`. -/
theorem rootTrace_single_transport {a : ℕ → ℝ} {aT ν δ κ : ℝ}
    {X₁ Y : Finset (CTorus d L N₁ m₁ (k + 1))} {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ (k + 1))}
    {X₁' Y' : Finset (CTorus d L N₁' m₁ (k + 1))} {𝒞' : Finset (ℕ × CTorus d L N₁' m₁ (k + 1))}
    (hconn : HatConn (GA)) (hconn' : HatConn (GB))
    (hY : IsNnComp ((Vset X₁ 𝒞).filter fun x => x ∈ (GA).Ω 1) Y)
    (hYc : IsNnComp ((Vset X₁' 𝒞').filter fun x => x ∈ (GB).Ω 1) Y')
    {s : DecParams (GA)} {s' : DecParams (GB)}
    (hs0 : ∀ P ∈ parCubes (GA) X₁, P ∉ 𝒞 → extS (GA) s P = 0)
    (hs0' : ∀ P ∈ parCubes (GB) X₁', P ∉ 𝒞' → extS (GB) s' P = 0)
    (hY' : Y.image bm = Y') (hB' : (SY (GA) X₁ 𝒞 Y).image bm = SY (GB) X₁' 𝒞' Y')
    (hagree : ∀ q ∈ innerCentres (GA) (SY (GA) X₁ 𝒞 Y),
      sProd (GB) (extS (GB) s') (Prod.map id bm q) = sProd (GA) (extS (GA) s) q)
    {R : ℕ} (hYR : ∀ x ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    (hn : 4 * R + 12 * L ^ (k + 1 + m₁) + 3 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 4 * R + 12 * L ^ (k + 1 + m₁) + 3 * L ^ (k + 1) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1))
    {α : (GA).Ω 1 → ℂ} {α' : (GB).Ω 1 → ℂ}
    (hα : ∀ x : (GA).Ω 1, (x : CTorus d L N₁ m₁ (k + 1)) ∈ SY (GA) X₁ 𝒞 Y → α' (ιb x) = α x)
    {φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ} {φ' : CTorus d L N₁' m₁ (k + 1) → Fin N → ℂ}
    (hφR : ∀ u ∈ rowsCov_R (GA) a aT ν α X₁ 𝒞 Y, φ' (bm u) = φ u)
    (hfam : ∀ x, 0 ≤ x → XData (GA) a aT ν x α κ (extS (GA) s))
    (hfam' : ∀ x, 0 ≤ x → XData (GB) a aT ν x α' κ (extS (GB) s'))
    (hφ : IsConstraintField (GA) δ φ) (hφ' : IsConstraintField (GB) δ φ') (hδ : 0 ≤ δ)
    (hsm : δ ^ 2 * smallConstX d L κ ≤ 1 / 4)
    {b : unitPts (GA)} (hb : UnitOut (GA) Y b) :
    rootTrace (GB) a aT ν (unitQ (GB)) (unitP (GB)) {ιu b} s' φ' α' =
      rootTrace (GA) a aT ν (unitQ (GA)) (unitP (GA)) {b} s φ α := by
  unfold rootTrace
  rw [Finset.sum_singleton, Finset.sum_singleton]
  refine congrArg _ (Finset.sum_congr rfl fun i _ => ?_)
  exact decLog_diag_transport hconn hconn' hY hYc hs0 hs0' hY' hB' hagree hYR hn hn' hα hφR hfam
    hfam' hφ hφ' hδ hsm hb i

end LogRows

/-! ### D2: the background inputs on two tori -/

section BgInputs

variable {d L N₁ N₁' m₁ k N : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ : ℝ}

set_option hygiene false in
local notation "bm" => boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1))
set_option hygiene false in
local notation "GA" => levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  (k + 1) le_rfl
set_option hygiene false in
local notation "GB" => levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  (k + 1) le_rfl
set_option hygiene false in
local notation "ιb" x:max => Subtype.mk (bm (x : CTorus d L N₁ m₁ (k + 1)))
  (levelGS_mem_Ω_one (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (K := k + 1) (ϱ := ϱ)
    (Nat.le_add_left 1 k) le_rfl _)

omit [NeZero N₁'] in
/-- **The field sites `R(S_Y)` lie in `Y`, and their approximate-field footprints in the raw-data
read set `RowsDep (S_Y)`** (one torus, the top level `levelGS (k + 1)`).  The sites of `R(S_Y)`
read by the `x`-variant rows at a site `z ∈ S_Y` lie in `resSites z` (`rowsCov_R_subset_resSites`),
so their footprints `approxDep` lie in `resDep z`; that the sites themselves lie in `Y` is
`row_in_Y`.  (The `x`-variant rows need not be rows of `H_D`, so the inclusion is into the
`resDep` part of `RowsDep`.) -/
theorem rowsCov_R_mem_Y_and_rowsDep {a b : ℕ → ℝ} {aT ν ν' : ℝ} (S : XSetting (GA) b aT ν')
    {α : (GA).Ω 1 → ℂ} {X₁ Y : Finset (CTorus d L N₁ m₁ (k + 1))}
    {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ (k + 1))}
    {u : CTorus d L N₁ m₁ (k + 1)} (hu : u ∈ rowsCov_R (GA) b aT ν' α X₁ 𝒞 Y) :
    u ∈ Y ∧ ∀ z ∈ approxDep (GA) u, RowsDep (GA) a ν (SY (GA) X₁ 𝒞 Y) z := by
  have hj1 : 1 ≤ k + 1 := Nat.le_add_left 1 k
  refine ⟨?_, fun z hz => ?_⟩
  · rcases hu with hu | ⟨z, y, hz, rfl, x₀, -, hne⟩
    · exact SY_subset_levelGS hj1 le_rfl hu
    · exact row_in_Y S hz hne
  · obtain ⟨w, hw, huw⟩ := rowsCov_R_subset_resSites hu
    exact Or.inl ⟨⟨w, levelGS_mem_Ω_one hj1 le_rfl w⟩, hw, approxDep_subset_resDep huw hz⟩

/-- **D2: the background inputs of the decoupled covariance on two tori, from the raw data.**  Let
`D`, `D'` be data in the union domains of Theorem I-4b on the two tori, `s`, `s'` parameters in the
polydisc, and `(Y, S_Y)`, `(Y', S_{Y'})` corresponding components of the cut with corresponding cut
factors, as in `decBg_value_twoTorus` at the level `j = K = k + 1`.  If the raw data agree on
`RowsDep (S_Y)`, then the decoupled multipliers `α_s = decBgMult` correspond on `S_Y`, and the
extended decoupled fields `φ̄_s = barField D.Ψ (decBgField)` correspond on the sites `R(S_Y)` read
by the `x`-variant rows (for any `x`-variant constants `b, a_T, ν'` with an `XSetting`): these are
the hypotheses `hα`, `hφR` of `decCov_rows_transport` and `decLog_diag_transport`.  The proof is
`decBg_component_unique` (multipliers on `S_Y`, fields at the sites of `Y` whose footprint lies in
`RowsDep (S_Y)`) and `rowsCov_R_mem_Y_and_rowsDep`.  Margin:
`4 R + 12 L^(k+1+m₁) + 7 L^(k+1) + 5 < N₁ L^m₁ L^(k+1)` (and for `N₁'`). -/
theorem decBg_inputs_twoTorus {c BG : ℝ} (hS : DecSpecs d L c BG) {a : ℕ → ℝ} {ν : ℝ}
    (SA : DGSetting (GA) a ν) (SB : DGSetting (GB) a ν) (hconn : HatConn (GA))
    (hconn' : HatConn (GB)) (HB : BgHyp d L (k + 1) ϱ a ν) {κ : ℝ} (hκ : 0 ≤ κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    {s : DecParams (GA)} {s' : DecParams (GB)} (hs : ∀ P, ‖s P‖ < Real.exp κ)
    (hs' : ∀ P, ‖s' P‖ < Real.exp κ)
    {D : BgData (GA) N} {D' : BgData (GB) N}
    (hDd : InUnionDomainC (GA) (bgC0 d L N) (c7 d L N BG κ) ν D)
    (hDd' : InUnionDomainC (GB) (bgC0 d L N) (c7 d L N BG κ) ν D')
    {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ (k + 1))} {X₁ Y : Finset (CTorus d L N₁ m₁ (k + 1))}
    {𝒞' : Finset (ℕ × CTorus d L N₁' m₁ (k + 1))} {X₁' Y' : Finset (CTorus d L N₁' m₁ (k + 1))}
    (hY : IsNnComp ((Vset X₁ 𝒞).filter fun x => x ∈ (GA).Ω 1) Y)
    (hYc : IsNnComp ((Vset X₁' 𝒞').filter fun x => x ∈ (GB).Ω 1) Y')
    (hs0 : ∀ P ∈ parCubes (GA) X₁, P ∉ 𝒞 → extS (GA) s P = 0)
    (hs0' : ∀ P ∈ parCubes (GB) X₁', P ∉ 𝒞' → extS (GB) s' P = 0)
    (hY' : Y.image bm = Y') (hB' : (SY (GA) X₁ 𝒞 Y).image bm = SY (GB) X₁' 𝒞' Y')
    (hagree : ∀ q ∈ innerCentres (GA) (SY (GA) X₁ 𝒞 Y),
      sProd (GB) (extS (GB) s') (Prod.map id bm q) = sProd (GA) (extS (GA) s) q)
    {R : ℕ} (hYR : ∀ x ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    (hn : 4 * R + 12 * L ^ (k + 1 + m₁) + 7 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 4 * R + 12 * L ^ (k + 1 + m₁) + 7 * L ^ (k + 1) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hD : RawBoxAgree {z | RowsDep (GA) a ν (SY (GA) X₁ 𝒞 Y) z} (rawOf D) (rawOf D'))
    {b : ℕ → ℝ} {aT ν' : ℝ} (SX : XSetting (GA) b aT ν') :
    (∀ x : (GA).Ω 1, (x : CTorus d L N₁ m₁ (k + 1)) ∈ SY (GA) X₁ 𝒞 Y →
      decBgMult (GB) a ν (rho4 d L N BG κ) s' D' (ιb x) =
        decBgMult (GA) a ν (rho4 d L N BG κ) s D x) ∧
    (∀ u ∈ rowsCov_R (GA) b aT ν' (decBgMult (GA) a ν (rho4 d L N BG κ) s D) X₁ 𝒞 Y,
      barField (GB) D'.Ψ (decBgField (GB) a ν (rho4 d L N BG κ) s' D') (bm u) =
        barField (GA) D.Ψ (decBgField (GA) a ν (rho4 d L N BG κ) s D) u) := by
  have hj1 : 1 ≤ k + 1 := Nat.le_add_left 1 k
  obtain ⟨δ, ε, hδ0, hδε, hε, hδ, hνε, hDC⟩ := id hDd
  obtain ⟨δ', ε', hδ0', hδε', hε', hδ', hνε', hDC'⟩ := id hDd'
  obtain ⟨φ, α, hsol, huniq, -⟩ := i4b_exists_unique hS SA HB hκ hM (fun P => (hs P).le) hδ0 hδε
    hε hδ hνε hDC
  obtain ⟨φ', α', hsol', huniq', -⟩ := i4b_exists_unique hS SB HB hκ hM (fun P => (hs' P).le) hδ0'
    hδε' hε' hδ' hνε' hDC'
  obtain ⟨e1, e2⟩ := decBg_eq hsol huniq
  obtain ⟨e1', e2'⟩ := decBg_eq hsol' huniq'
  rw [e1, e2, e1', e2']
  obtain ⟨hmult, -, hfield, -⟩ := decBg_component_unique hj1 le_rfl hS SA SB hconn hconn' HB hκ hM
    (fun P => (hs P).le) (fun P => (hs' P).le) hδ0 hδε hε hδ hνε hδ0' hδε' hε' hδ' hνε' hDC hDC'
    hY hYc hs0 hs0' hY' hB' hagree hYR hn hn' hD hsol hsol'
  refine ⟨hmult, fun u hu => ?_⟩
  obtain ⟨huY, hdep⟩ := rowsCov_R_mem_Y_and_rowsDep (a := a) (ν := ν) SX hu
  funext i
  simp only [barField, levelGS_mem_Ω_one hj1 le_rfl, ↓reduceDIte]
  exact hfield ⟨u, levelGS_mem_Ω_one hj1 le_rfl u⟩ huY (fun z hz => hD z (hdep z hz)) i

end BgInputs

/-! ### D3: the rooted trace with its background on two tori -/

section TraceBg

variable {d L N₁ N₁' m₁ k N : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ ϱm ϱm' : ℝ}

set_option hygiene false in
local notation "bm" => boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1))
set_option hygiene false in
local notation "bU" => boxMap ((N₁ * L ^ m₁) * L ^ (k + 1 - k)) ((N₁' * L ^ m₁) * L ^ (k + 1 - k))
set_option hygiene false in
local notation "GA" => levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  (k + 1) le_rfl
set_option hygiene false in
local notation "GB" => levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  (k + 1) le_rfl
set_option hygiene false in
local notation "ιu" b:max => Subtype.mk (bU (b : UnitTorus d L N₁ m₁ k))
  (mem_unitPts_levelTop (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := k) (ϱ := ϱ) _)

/-- **D3 (one cut configuration): the rooted trace of one unit block with its background, on two
tori.**  Let `D`, `D'` be data of the charts `Ξ^c(𝔹_{k+1}; 1, ε)` of the top levels of the two
tori (`FlCore` on each torus, with the same constants), `s`, `s'` cut parameters in the polydisc of
radius `e^κ`, and `(Y, S_Y)`, `(Y', S_{Y'})` corresponding components of the cut with
corresponding cut factors (the hypotheses of `decLog_diag_transport` for `extS s`, `extS s'`).  If
the raw data agree on `RowsDep (S_Y)`, then the rooted trace `rootTraceBg {b} D s` of a unit block
`b` whose `(k+1)`-block lies in `Y` equals that of the corresponding block on the second torus.
The background inputs are `decBg_inputs_twoTorus`; the standing hypotheses of the covariance at
the background are `covStanding_rootTraceBg` on each torus; the trace is
`rootTrace_single_transport`.  Margin: `4 R + 12 L^(k+1+m₁) + 7 L^(k+1) + 5 < N₁ L^m₁ L^(k+1)`
(and for `N₁'`). -/
theorem rootTraceBg_single_twoTorus
    {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
    {Hm' : GeneratingSet d L (N₁' * L ^ m₁) (k + 1) ϱm'}
    {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ}
    (hC : FlCore N (GA) Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hC' : FlCore N (GB) Hm' a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (hk : 1 ≤ k) {δc : ℝ}
    (hδc : 0 ≤ δc) (hcap : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hαK : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hconn : HatConn (GA)) (hconn' : HatConn (GB))
    {s : DecParams (GA)} {s' : DecParams (GB)} (hs : ∀ P, ‖s P‖ < Real.exp κ)
    (hs' : ∀ P, ‖s' P‖ < Real.exp κ)
    {D : BgData (GA) N} {D' : BgData (GB) N}
    (hD : XiCData (GA) (compWeight L a₁) ν (k + 1) 1 eps D)
    (hD' : XiCData (GB) (compWeight L a₁) ν (k + 1) 1 eps D')
    {X₁ Y : Finset (CTorus d L N₁ m₁ (k + 1))} {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ (k + 1))}
    {X₁' Y' : Finset (CTorus d L N₁' m₁ (k + 1))} {𝒞' : Finset (ℕ × CTorus d L N₁' m₁ (k + 1))}
    (hY : IsNnComp ((Vset X₁ 𝒞).filter fun x => x ∈ (GA).Ω 1) Y)
    (hYc : IsNnComp ((Vset X₁' 𝒞').filter fun x => x ∈ (GB).Ω 1) Y')
    (hs0 : ∀ P ∈ parCubes (GA) X₁, P ∉ 𝒞 → extS (GA) s P = 0)
    (hs0' : ∀ P ∈ parCubes (GB) X₁', P ∉ 𝒞' → extS (GB) s' P = 0)
    (hY' : Y.image bm = Y') (hB' : (SY (GA) X₁ 𝒞 Y).image bm = SY (GB) X₁' 𝒞' Y')
    (hagree : ∀ q ∈ innerCentres (GA) (SY (GA) X₁ 𝒞 Y),
      sProd (GB) (extS (GB) s') (Prod.map id bm q) = sProd (GA) (extS (GA) s) q)
    {R : ℕ} (hYR : ∀ x ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    (hn : 4 * R + 12 * L ^ (k + 1 + m₁) + 7 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 4 * R + 12 * L ^ (k + 1 + m₁) + 7 * L ^ (k + 1) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hraw : RawBoxAgree {z | RowsDep (GA) (compWeight L a₁) ν (SY (GA) X₁ 𝒞 Y) z} (rawOf D)
      (rawOf D'))
    {b : unitPts (GA)} (hb : UnitOut (GA) Y b) :
    rootTraceBg (GB) (compWeight L a₁) a₁ ν (rho4 d L N BG κ) (unitQ (GB)) (unitP (GB)) {ιu b}
        D' s' =
      rootTraceBg (GA) (compWeight L a₁) a₁ ν (rho4 d L N BG κ) (unitQ (GA)) (unitP (GA)) {b}
        D s := by
  have H := covStanding_rootTraceBg hC hk hδc hcap hsm hmar hαK hD hs
  have H' := covStanding_rootTraceBg hC' hk hδc hcap hsm hmar hαK hD' hs'
  obtain ⟨hmult, hfld⟩ := decBg_inputs_twoTorus hC.hS hC.Sp hC'.Sp hconn hconn' hC.HBp hC.hκ.le
    hC.hM hs hs' (inUnionDomainC_of_xiCData hC hD) (inUnionDomainC_of_xiCData hC' hD') hY hYc
    hs0 hs0' hY' hB' hagree hYR hn hn' hraw (H.fam 0 le_rfl).st
  unfold rootTraceBg
  exact rootTrace_single_transport hconn hconn' hY hYc hs0 hs0' hY' hB' hagree hYR (by omega)
    (by omega) hmult hfld H.fam H'.fam H.field H'.field H.nonneg H.small hb

omit [NeZero N₁'] in
/-- The footprint `approxDep x` of a site of the box of radius `ρ` lies in the box of radius
`ρ + 2 L^(k+1)` (top level `levelGS (k + 1)`). -/
theorem inBox_of_mem_approxDep_top {ρ : ℕ}
    (hn : 2 * (ρ + 2 * L ^ (k + 1)) + 1 < (N₁ * L ^ m₁) * L ^ (k + 1))
    {x z : CTorus d L N₁ m₁ (k + 1)} (hx : InBox d ρ ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    (hz : z ∈ approxDep (GA) x) : InBox d (ρ + 2 * L ^ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1)) z := by
  unfold approxDep at hz
  rcases Finset.mem_insert.1 hz with rfl | hz
  · exact inBox_mono (Nat.le_add_right _ _) hx
  · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hz
    obtain ⟨hqb, hne⟩ := (mem_active _).1 hq
    have hq1 : q.1 = k + 1 := ((mem_blockIdx_levelGS le_rfl q).1 hqb).1
    rw [hq1] at hne
    exact inBox_of_bump_ne_zero (N₀ := N₁ * L ^ m₁) (k := k + 1) (k + 1) x q.2 hx hn hne

omit [NeZero N₁'] in
/-- **The raw-data read set `RowsDep (S_Y)` lies in the box of radius `R + 3 L^(k+1)`** when `Y`
lies in the box of radius `R` (top level `levelGS (k + 1)`). -/
theorem inBox_of_rowsDep_top {a : ℕ → ℝ} {ν : ℝ} (S : DGSetting (GA) a ν)
    {X₁ Y : Finset (CTorus d L N₁ m₁ (k + 1))} {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ (k + 1))}
    {R : ℕ} (hYR : ∀ x ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    (hn : 2 * (R + 3 * L ^ (k + 1)) + 1 < (N₁ * L ^ m₁) * L ^ (k + 1))
    {z : CTorus d L N₁ m₁ (k + 1)} (hz : RowsDep (GA) a ν (SY (GA) X₁ 𝒞 Y) z) :
    InBox d (R + 3 * L ^ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1)) z := by
  have hj1 : 1 ≤ k + 1 := Nat.le_add_left 1 k
  rcases hz with ⟨x, hx, hzx⟩ | ⟨y, hy, hzy⟩
  · have hxR := hYR _ (SY_subset_levelGS hj1 le_rfl hx)
    unfold resDep at hzx
    obtain ⟨w, hw, hzw⟩ := Finset.mem_biUnion.1 hzx
    have hwR := inBox_of_mem_resSites_levelGS hj1 le_rfl (by omega) hxR hw
    have := inBox_of_mem_approxDep_top (ρ := R + L ^ (k + 1)) (by omega) hwR hzw
    exact inBox_mono (by omega) this
  · have hyR := hYR _ (rowSite_subset S hy)
    exact inBox_mono (by omega) (inBox_of_mem_approxDep_top (by omega) hyR hzy)

omit [NeZero N₁'] in
/-- The coercion of the cube `cubeP P` is the patch `Pset m₁ P`. -/
theorem coe_cubeP_eq_Pset (P : ℕ × CTorus d L N₁ m₁ (k + 1)) :
    ((cubeP P : Finset (CTorus d L N₁ m₁ (k + 1))) : Set (CTorus d L N₁ m₁ (k + 1))) =
      Pset m₁ P := by
  ext x; simp [mem_cubeP, Pset]

/-- The cube `cubeP P` of a cube centre of the box goes to the cube of the image centre. -/
theorem cubeP_image_top {ρ : ℕ}
    (hn : 2 * ρ + 5 * (L * cellSide L 0 m₁ (k + 1)) < (N₁ * L ^ m₁) * L ^ (k + 1))
    {P : ℕ × CTorus d L N₁ m₁ (k + 1)} (hP : P ∈ cubeIdx (GA))
    (hP0 : InBox d ρ ((N₁ * L ^ m₁) * L ^ (k + 1)) P.2) :
    (cubeP P).image bm = cubeP (Prod.map id bm P) := by
  apply Finset.coe_injective
  rw [Finset.coe_image, coe_cubeP_eq_Pset, coe_cubeP_eq_Pset]
  exact pset_image_q (m₀ := 0) (N₁' := N₁') le_rfl hn hP hP0

/-- `Vset` of the images is the image of `Vset`, for patches in the box. -/
theorem vset_image_top {ρ : ℕ}
    (hn : 2 * ρ + 5 * (L * cellSide L 0 m₁ (k + 1)) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (X₁ : Finset (CTorus d L N₁ m₁ (k + 1))) {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ (k + 1))}
    (h𝒞 : ∀ P ∈ 𝒞, P ∈ cubeIdx (GA) ∧ InBox d ρ ((N₁ * L ^ m₁) * L ^ (k + 1)) P.2) :
    Vset (X₁.image bm) (𝒞.image (Prod.map id bm)) = (Vset X₁ 𝒞).image bm := by
  unfold Vset
  rw [Finset.image_union, Finset.image_biUnion, Finset.biUnion_image]
  congr 1
  refine Finset.biUnion_congr rfl fun P hP => ?_
  exact (cubeP_image_top (N₁' := N₁') hn (h𝒞 P hP).1 (h𝒞 P hP).2).symm

/-- **D3 (cut points): the rooted trace of one unit block with its background at a cut point, on
two tori.**  Let `I` be a set of parameter cubes of the first torus and `I'` the corresponding set
of the second torus (`patches I' = Prod.map id bm '' patches I`), with the cubes of `I` and the
`(k+1)`-block of the unit point `b` in the box of radius `R`.  If the raw data agree on the box
of radius `R + 3 L^(k+1)`, then the rooted traces of `{b}` and `{ιu b}` with their backgrounds at
the cut points `1_I`, `1_{I'}` are equal.  The cut configuration is `X₁ =` the `(k+1)`-block of `b`,
`𝒞 = patches I`, `Y = V(X₁, 𝒞)` (the cut parameter vanishes on every parameter cube off `I`); the
image of the block set and the cut factors are `SY_image` and `hagree_boxMap`.  Margins:
`4 R + 12 L^(k+1+m₁) + 7 L^(k+1) + 5 < N₁ L^m₁ L^(k+1)` and `2 R₁ + 5 L · cellSide L 0 m₁ (k+1) <
N₁ L^m₁ L^(k+1)`, `R₁ = R + (3 L^(k+1+m₁) + 3 L^(k+3)) + L^(k+1+m₁)` (and for `N₁'`). -/
theorem rootTraceBg_cutPt_twoTorus
    {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
    {Hm' : GeneratingSet d L (N₁' * L ^ m₁) (k + 1) ϱm'}
    {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ}
    (hC : FlCore N (GA) Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hC' : FlCore N (GB) Hm' a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (hk : 1 ≤ k) {δc : ℝ}
    (hδc : 0 ≤ δc) (hcap : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hαK : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hconn : HatConn (GA)) (hconn' : HatConn (GB))
    {D : BgData (GA) N} {D' : BgData (GB) N}
    (hD : XiCData (GA) (compWeight L a₁) ν (k + 1) 1 eps D)
    (hD' : XiCData (GB) (compWeight L a₁) ν (k + 1) 1 eps D')
    (I : Finset (cubeIdx (GA))) (I' : Finset (cubeIdx (GB)))
    (hI' : patches I' = (patches I).image (Prod.map id bm))
    {b : unitPts (GA)} {R : ℕ}
    (hbR : ∀ x : CTorus d L N₁ m₁ (k + 1), unitBlock1 (unitBlock x) =
      unitBlock1 (b : UnitTorus d L N₁ m₁ k) → InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    (hIR : ∀ P ∈ patches I, ∀ x ∈ cubeP P, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    (hn : 4 * R + 12 * L ^ (k + 1 + m₁) + 7 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 4 * R + 12 * L ^ (k + 1 + m₁) + 7 * L ^ (k + 1) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hnS : 2 * (R + (3 * L ^ (k + 1 + m₁) + 3 * L ^ (k + 1 + 2)) + L ^ (k + 1 + m₁)) +
      5 * (L * cellSide L 0 m₁ (k + 1)) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnS' : 2 * (R + (3 * L ^ (k + 1 + m₁) + 3 * L ^ (k + 1 + 2)) + L ^ (k + 1 + m₁)) +
      5 * (L * cellSide L 0 m₁ (k + 1)) < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hraw : RawBoxAgree {z | InBox d (R + 3 * L ^ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1)) z}
      (rawOf D) (rawOf D')) :
    rootTraceBg (GB) (compWeight L a₁) a₁ ν (rho4 d L N BG κ) (unitQ (GB)) (unitP (GB)) {ιu b}
        D' (cutPt I') =
      rootTraceBg (GA) (compWeight L a₁) a₁ ν (rho4 d L N BG κ) (unitQ (GA)) (unitP (GA)) {b}
        D (cutPt I) := by
  classical
  have hj1 : 1 ≤ k + 1 := Nat.le_add_left 1 k
  have hKm : L ^ (k + 1) ≤ L ^ (k + 1 + m₁) :=
    Nat.pow_le_pow_right (Nat.pos_of_ne_zero (NeZero.ne L)) (Nat.le_add_right _ _)
  have hK1 : 1 ≤ L ^ (k + 1) := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (NeZero.ne L))
  have hcs : L ^ (k + 1 + m₁) ≤ L * cellSide L 0 m₁ (k + 1) := by
    unfold cellSide
    rw [Nat.add_zero]
    exact Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero (NeZero.ne L))
  -- the cut configuration
  set X₁ : Finset (CTorus d L N₁ m₁ (k + 1)) := Finset.univ.filter fun x =>
    unitBlock1 (unitBlock x) = unitBlock1 (b : UnitTorus d L N₁ m₁ k) with hX₁
  set 𝒞 : Finset (ℕ × CTorus d L N₁ m₁ (k + 1)) := patches I with h𝒞
  set Y : Finset (CTorus d L N₁ m₁ (k + 1)) := (Vset X₁ 𝒞).filter fun x => x ∈ (GA).Ω 1 with hY
  have hΩA : ∀ x : CTorus d L N₁ m₁ (k + 1), x ∈ (GA).Ω 1 := levelGS_mem_Ω_one hj1 le_rfl
  have hΩB : ∀ x : CTorus d L N₁' m₁ (k + 1), x ∈ (GB).Ω 1 := levelGS_mem_Ω_one hj1 le_rfl
  have hYV : Y = Vset X₁ 𝒞 := Finset.filter_true_of_mem fun x _ => hΩA x
  have hXR : ∀ x ∈ X₁, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x := fun x hx =>
    hbR x (Finset.mem_filter.1 hx).2
  have h𝒞R : ∀ P ∈ 𝒞, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) P.2 := fun P hP =>
    hIR P hP P.2 (mem_cubeP.2 (SameCell.refl _ _))
  have h𝒞I : ∀ P ∈ 𝒞, P ∈ cubeIdx (GA) := fun P hP => (mem_patches.1 hP).1
  have hYR : ∀ x ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x := by
    intro x hx
    rw [hYV] at hx
    rcases Finset.mem_union.1 hx with hx | hx
    · exact hXR x hx
    · obtain ⟨P, hP, hxP⟩ := Finset.mem_biUnion.1 hx
      exact hIR P hP x hxP
  -- the image configuration
  have hρS : 2 * R + 5 * (L * cellSide L 0 m₁ (k + 1)) < (N₁ * L ^ m₁) * L ^ (k + 1) := by omega
  have hVimg : Vset (X₁.image bm) (𝒞.image (Prod.map id bm)) = (Vset X₁ 𝒞).image bm :=
    vset_image_top (N₁' := N₁') hρS X₁ fun P hP => ⟨h𝒞I P hP, h𝒞R P hP⟩
  have hYc : IsNnComp ((Vset (X₁.image bm) (𝒞.image (Prod.map id bm))).filter
      fun x => x ∈ (GB).Ω 1) (Y.image bm) := by
    rw [Finset.filter_true_of_mem fun x _ => hΩB x, hVimg, ← hYV]
    exact ⟨subset_rfl, fun _ _ y hy _ => hy⟩
  have hYA : IsNnComp ((Vset X₁ 𝒞).filter fun x => x ∈ (GA).Ω 1) Y :=
    ⟨subset_rfl, fun _ _ y hy _ => hy⟩
  -- the cut parameters
  have hs0 : ∀ P ∈ parCubes (GA) X₁, P ∉ 𝒞 → extS (GA) (cutPt I) P = 0 := by
    intro P hP hPC
    have hPc : P ∈ cubeIdx (GA) := (Finset.mem_filter.1 hP).1
    have hPI : (⟨P, hPc⟩ : cubeIdx (GA)) ∉ I := fun h => hPC (mem_patches.2 ⟨hPc, h⟩)
    simp [extS, hPc, cutPt, hPI]
  have hs0' : ∀ P ∈ parCubes (GB) (X₁.image bm), P ∉ 𝒞.image (Prod.map id bm) →
      extS (GB) (cutPt I') P = 0 := by
    intro P hP hPC
    have hPc : P ∈ cubeIdx (GB) := (Finset.mem_filter.1 hP).1
    have hPI : (⟨P, hPc⟩ : cubeIdx (GB)) ∉ I' := fun h => hPC (by
      rw [h𝒞, ← hI']; exact mem_patches.2 ⟨hPc, h⟩)
    simp [extS, hPc, cutPt, hPI]
  have hsP : ∀ P ∈ cubeIdx (GA),
      InBox d (R + (3 * L ^ (k + 1 + m₁) + 3 * L ^ (k + 1 + 2)) + L ^ (k + 1 + m₁))
        ((N₁ * L ^ m₁) * L ^ (k + 1)) P.2 →
      extS (GB) (cutPt I') (Prod.map id bm P) = extS (GA) (cutPt I) P := by
    intro P hPc hPR
    obtain ⟨y0, rfl, hb0⟩ := exists_of_mem_cubeIdx (ϱ := ϱ) le_rfl hPc
    have hPc' : Prod.map id bm ((k + 1, y0) : ℕ × CTorus d L N₁ m₁ (k + 1)) ∈ cubeIdx (GB) :=
      (mem_cubeIdx_levelGS le_rfl _).2 ⟨rfl, hj1,
        aligned_boxMap (pow_dvd_side le_rfl N₁) (pow_dvd_side le_rfl N₁') hb0⟩
    have hiff : (⟨_, hPc'⟩ : cubeIdx (GB)) ∈ I' ↔ (⟨_, hPc⟩ : cubeIdx (GA)) ∈ I := by
      rw [← (mem_patches (G := GB)).trans (exists_prop_of_true hPc')]
      rw [← (mem_patches (G := GA)).trans (exists_prop_of_true hPc)]
      rw [hI', Finset.mem_image]
      constructor
      · rintro ⟨Q, hQ, hQe⟩
        have hQR := h𝒞R Q hQ
        have := injOn_idxMap (N₁' := N₁')
          (ρ := R + (3 * L ^ (k + 1 + m₁) + 3 * L ^ (k + 1 + 2)) + L ^ (k + 1 + m₁))
          (by omega) (inBox_mono (by omega) hQR) hPR hQe
        rw [← this]; exact hQ
      · intro h; exact ⟨_, h, rfl⟩
    simp only [extS, hPc, hPc', ↓reduceDIte, cutPt]
    by_cases h : (⟨_, hPc⟩ : cubeIdx (GA)) ∈ I
    · rw [ite_eq_left_iff.2 (fun h' => absurd (hiff.2 h) h'), ite_eq_left_iff.2 (fun h' => absurd h h')]
    · rw [ite_eq_right_iff.2 (fun h' => absurd h' (mt hiff.1 h)), ite_eq_right_iff.2 (fun h' => absurd h' h)]
  have hB' := SY_image (ϱ := ϱ) (N₁' := N₁') hj1 le_rfl hnS hnS' hXR h𝒞R hYR
  have hagree := hagree_boxMap (ϱ := ϱ) (N₁' := N₁') hj1 le_rfl hnS hnS'
    (SY_subset_levelGS (ϱ := ϱ) (X₁ := X₁) (𝒞 := 𝒞) hj1 le_rfl) hYR hsP
  have hraw' : RawBoxAgree {z | RowsDep (GA) (compWeight L a₁) ν (SY (GA) X₁ 𝒞 Y) z} (rawOf D)
      (rawOf D') := fun z hz => hraw z (inBox_of_rowsDep_top hC.Sp hYR (by omega) hz)
  have hb : UnitOut (GA) Y b := by
    intro y hy
    rw [hYV]
    exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, hy⟩)
  exact rootTraceBg_single_twoTorus hC hC' hk hδc hcap hsm hmar hαK hconn hconn'
    (norm_cutPt_lt_exp hC.hκ I) (norm_cutPt_lt_exp hC'.hκ I') hD hD' hYA hYc hs0 hs0' rfl hB'
    hagree hYR hn hn' hraw' hb

omit [NeZero N₁'] in
/-- The number of patches of a set of parameter cubes is its cardinality. -/
theorem card_patches_eq {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} (J : Finset (cubeIdx G)) :
    (patches J).card = J.card := by
  unfold patches
  exact Finset.card_image_of_injective _ Subtype.val_injective

/-- **D3 (mixed differences): the mixed differences of the rooted trace with its background, on two
tori.**  For a set `J` of parameter cubes of the first torus with patches in the box of radius `R`
and the corresponding set `J'` of the second torus (`patches J' = Prod.map id bm '' patches J`),
`Δ_{J'} F' = Δ_J F` for `F = rootTraceBg {b} D`, `F' = rootTraceBg {ιu b} D'`, under the
hypotheses of `rootTraceBg_cutPt_twoTorus`.  The subsets `I ⊆ J` correspond to the subsets
`I' ⊆ J'` with `patches I' = Prod.map id bm '' patches I` (`Prod.map id bm` is injective on the
box), with the same cardinalities. -/
theorem mixDiff_rootTraceBg_twoTorus
    {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
    {Hm' : GeneratingSet d L (N₁' * L ^ m₁) (k + 1) ϱm'}
    {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ}
    (hC : FlCore N (GA) Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hC' : FlCore N (GB) Hm' a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (hk : 1 ≤ k) {δc : ℝ}
    (hδc : 0 ≤ δc) (hcap : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hαK : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hconn : HatConn (GA)) (hconn' : HatConn (GB))
    {D : BgData (GA) N} {D' : BgData (GB) N}
    (hD : XiCData (GA) (compWeight L a₁) ν (k + 1) 1 eps D)
    (hD' : XiCData (GB) (compWeight L a₁) ν (k + 1) 1 eps D')
    (J : Finset (cubeIdx (GA))) (J' : Finset (cubeIdx (GB)))
    (hJ' : patches J' = (patches J).image (Prod.map id bm))
    {b : unitPts (GA)} {R : ℕ}
    (hbR : ∀ x : CTorus d L N₁ m₁ (k + 1), unitBlock1 (unitBlock x) =
      unitBlock1 (b : UnitTorus d L N₁ m₁ k) → InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    (hJR : ∀ P ∈ patches J, ∀ x ∈ cubeP P, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    (hn : 4 * R + 12 * L ^ (k + 1 + m₁) + 7 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 4 * R + 12 * L ^ (k + 1 + m₁) + 7 * L ^ (k + 1) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hnS : 2 * (R + (3 * L ^ (k + 1 + m₁) + 3 * L ^ (k + 1 + 2)) + L ^ (k + 1 + m₁)) +
      5 * (L * cellSide L 0 m₁ (k + 1)) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnS' : 2 * (R + (3 * L ^ (k + 1 + m₁) + 3 * L ^ (k + 1 + 2)) + L ^ (k + 1 + m₁)) +
      5 * (L * cellSide L 0 m₁ (k + 1)) < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hraw : RawBoxAgree {z | InBox d (R + 3 * L ^ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1)) z}
      (rawOf D) (rawOf D')) :
    mixDiff J' (rootTraceBg (GB) (compWeight L a₁) a₁ ν (rho4 d L N BG κ) (unitQ (GB))
        (unitP (GB)) {ιu b} D') =
      mixDiff J (rootTraceBg (GA) (compWeight L a₁) a₁ ν (rho4 d L N BG κ) (unitQ (GA))
        (unitP (GA)) {b} D) := by
  classical
  have hKm : L ^ (k + 1) ≤ L ^ (k + 1 + m₁) :=
    Nat.pow_le_pow_right (Nat.pos_of_ne_zero (NeZero.ne L)) (Nat.le_add_right _ _)
  set f : ℕ × CTorus d L N₁ m₁ (k + 1) → ℕ × CTorus d L N₁' m₁ (k + 1) := Prod.map id bm with hf
  have hJbox : ∀ P ∈ patches J, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) P.2 := fun P hP =>
    hJR P hP P.2 (mem_cubeP.2 (SameCell.refl _ _))
  have hinj : Set.InjOn f ↑(patches J) := fun P hP Q hQ h =>
    injOn_idxMap (N₁' := N₁') (ρ := R) (by omega) (hJbox P hP) (hJbox Q hQ) h
  -- the correspondence of subsets
  let i : Finset (cubeIdx (GA)) → Finset (cubeIdx (GB)) := fun I =>
    J'.filter fun P' => ∃ P ∈ I, f P.1 = P'.1
  let j : Finset (cubeIdx (GB)) → Finset (cubeIdx (GA)) := fun I' =>
    J.filter fun P => ∃ P' ∈ I', f P.1 = P'.1
  have hpatch : ∀ I ⊆ J, patches (i I) = (patches I).image f := by
    intro I hI
    ext Q'
    simp only [mem_patches, Finset.mem_image, Finset.mem_filter, i]
    constructor
    · rintro ⟨hQ', -, P, hP, hPQ⟩
      exact ⟨P.1, ⟨P.2, hP⟩, hPQ⟩
    · rintro ⟨Q, ⟨hQ, hQI⟩, rfl⟩
      have hm : f Q ∈ patches J' := by
        rw [hJ']; exact Finset.mem_image_of_mem _ (mem_patches.2 ⟨hQ, hI hQI⟩)
      obtain ⟨hQ', hQJ'⟩ := mem_patches.1 hm
      exact ⟨hQ', hQJ', ⟨Q, hQ⟩, hQI, rfl⟩
  have hcard : ∀ I ⊆ J, (i I).card = I.card := by
    intro I hI
    rw [← card_patches_eq, hpatch I hI, Finset.card_image_of_injOn
      (hinj.mono (Finset.coe_subset.2 (show patches I ⊆ patches J from
        Finset.image_subset_image hI))), card_patches_eq]
  have hJJ : J'.card = J.card := by
    rw [← card_patches_eq, hJ', Finset.card_image_of_injOn hinj, card_patches_eq]
  unfold mixDiff
  symm
  refine Finset.sum_nbij' i j (fun I hI => ?_) (fun I' hI' => ?_) (fun I hI => ?_)
    (fun I' hI' => ?_) (fun I hI => ?_)
  · exact Finset.mem_powerset.2 (Finset.filter_subset _ _)
  · exact Finset.mem_powerset.2 (Finset.filter_subset _ _)
  · have hIJ := Finset.mem_powerset.1 hI
    ext P
    simp only [Finset.mem_filter, i, j]
    constructor
    · rintro ⟨hPJ, P', ⟨-, Q, hQ, hQP'⟩, hPP'⟩
      have : P.1 = Q.1 := hinj (mem_patches.2 ⟨P.2, hPJ⟩) (mem_patches.2 ⟨Q.2, hIJ hQ⟩)
        (hPP'.trans hQP'.symm)
      rw [Subtype.ext this]; exact hQ
    · intro hP
      have hm : f P.1 ∈ patches J' := by
        rw [hJ']; exact Finset.mem_image_of_mem _ (mem_patches.2 ⟨P.2, hIJ hP⟩)
      obtain ⟨hP', hPJ'⟩ := mem_patches.1 hm
      exact ⟨hIJ hP, ⟨f P.1, hP'⟩, ⟨hPJ', P, hP, rfl⟩, rfl⟩
  · have hIJ := Finset.mem_powerset.1 hI'
    ext P'
    simp only [Finset.mem_filter, i, j]
    constructor
    · rintro ⟨-, P, ⟨-, Q', hQ', hPQ'⟩, hPP'⟩
      rw [Subtype.ext (hPP'.symm.trans hPQ')]; exact hQ'
    · intro hP'
      have hm : P'.1 ∈ patches J' := mem_patches.2 ⟨P'.2, hIJ hP'⟩
      rw [hJ'] at hm
      obtain ⟨Q, hQ, hQe⟩ := Finset.mem_image.1 hm
      obtain ⟨hQc, hQJ⟩ := mem_patches.1 hQ
      exact ⟨hIJ hP', ⟨Q, hQc⟩, ⟨hQJ, P', hP', hQe⟩, hQe⟩
  · have hIJ := Finset.mem_powerset.1 hI
    rw [hJJ, hcard I hIJ, rootTraceBg_cutPt_twoTorus hC hC' hk hδc hcap hsm hmar hαK hconn
      hconn' hD hD' I (i I) (hpatch I hIJ) hbR
      (fun P hP => hJR P (Finset.image_subset_image hIJ hP)) hn hn' hnS hnS' hraw]

end TraceBg

/-! ### The hull of a set of parameter cubes on two tori -/

section Hull

variable {d L N₁ N₁' m₁ k : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ : ℝ} {m₀ : ℕ}

set_option hygiene false in
local notation "bm" => boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1))
set_option hygiene false in
local notation "bm'" => boxMap ((N₁' * L ^ m₁) * L ^ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1))
set_option hygiene false in
local notation "aK" => cellSide L m₀ m₁ (k + 1)

omit [NeZero N₁] [NeZero N₁'] [NeZero L] in
/-- An aligned `π′_K` box (side `L a_K`) that meets a set of the box of radius `ρ` lies in the box
of radius `ρ + 2 L a_K`. -/
theorem inBox_of_box_meets {ρ : ℕ}
    (hn : 2 * (ρ + 2 * (L * aK)) + 1 < (N₁ * L ^ m₁) * L ^ (k + 1))
    {S : Set (CTorus d L N₁ m₁ (k + 1))} (hS : ∀ x ∈ S, InBox d ρ ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    {b : CTorus d L N₁ m₁ (k + 1)} (hb : (box b (L * aK) ∩ S).Nonempty) :
    ∀ x ∈ box b (L * aK), InBox d (ρ + 2 * (L * aK)) ((N₁ * L ^ m₁) * L ^ (k + 1)) x := by
  obtain ⟨s, hsb, hsS⟩ := hb
  have hbR := inBox_of_mem_box_left (by omega) (hS s hsS) hsb
  intro x hx
  exact inBox_mono (by omega) (inBox_of_mem_box_right (by omega) hbR hx)

omit [NeZero N₁'] in
/-- The sites of the cubes of the `π′_K`-hull of a set of the box of radius `ρ` lie in the box of
radius `ρ + 2 L a_K`. -/
theorem inBox_of_mem_piHull {ρ : ℕ}
    (hn : 2 * (ρ + 2 * (L * aK)) + 1 < (N₁ * L ^ m₁) * L ^ (k + 1))
    {S : Set (CTorus d L N₁ m₁ (k + 1))} (hS : ∀ x ∈ S, InBox d ρ ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    {c : CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1) Set.univ}
    (hc : c ∈ piHull m₀ S) :
    ∀ x ∈ box c.1 aK, InBox d (ρ + 2 * (L * aK)) ((N₁ * L ^ m₁) * L ^ (k + 1)) x := by
  obtain ⟨b, ⟨-, hb⟩, hcb⟩ := mem_piHull.1 hc
  exact fun x hx => inBox_of_box_meets hn hS hb x (hcb hx)

/-- **The `π′_K`-hull on two tori, one inclusion.**  For a set `S` of the box of radius `ρ`, the
image of the hull of `S` under `cubeMap` lies in the hull of `bm '' S`.  Margin:
`2 (ρ + 2 L a_K) + L a_K < N₁ L^m₁ L^(k+1)`. -/
theorem piHull_boxMap_subset (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁') {ρ : ℕ}
    (hn : 2 * (ρ + 2 * (L * aK)) + L * aK < (N₁ * L ^ m₁) * L ^ (k + 1))
    {S : Set (CTorus d L N₁ m₁ (k + 1))}
    (hS : ∀ x ∈ S, InBox d ρ ((N₁ * L ^ m₁) * L ^ (k + 1)) x) :
    (piHull m₀ S).image (cubeMap hN hN' le_rfl) ⊆ piHull m₀ (bm '' S) := by
  intro c' hc'
  obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hc'
  obtain ⟨b, ⟨hba, hb⟩, hcb⟩ := mem_piHull.1 hc
  have ha0 : 0 < L * aK := Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne L)) (cellSide_pos m₀ m₁ _)
  have hbox := inBox_of_box_meets (by omega) hS hb
  have himg : bm '' box b (L * aK) = box (bm b) (L * aK) :=
    image_box_boxMap (r := ρ + 2 * (L * aK)) hn ha0 hbox
  have hcs : aK ≤ L * aK := cellSide_le_mul
  have himc : bm '' box c.1 aK = box (bm c.1) aK :=
    image_box_boxMap (r := ρ + 2 * (L * aK)) (by omega) (cellSide_pos m₀ m₁ _)
      fun x hx => hbox x (hcb hx)
  obtain ⟨s, hsb, hsS⟩ := hb
  refine mem_piHull.2 ⟨bm b, ⟨aligned_boxMap (cellSide_dvd (K := k + 1) (m₁ := m₁) hN le_rfl)
    (cellSide_dvd (K := k + 1) (m₁ := m₁) hN' le_rfl) hba, bm s, ?_, s, hsS, rfl⟩, ?_⟩
  · rw [← himg]; exact ⟨s, hsb, rfl⟩
  · show box (bm c.1) aK ⊆ box (bm b) (L * aK)
    rw [← himg, ← himc]
    exact Set.image_mono hcb

/-- **The `π′_K`-hull on two tori.**  For a set `S` of the box of radius `ρ`,
`piHull (bm '' S) = cubeMap '' piHull S`.  Margin: `2 (ρ + 2 L a_K) + L a_K < N₁ L^m₁ L^(k+1)`
(and for `N₁'`). -/
theorem piHull_boxMap (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁') {ρ : ℕ}
    (hn : 2 * (ρ + 2 * (L * aK)) + L * aK < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 2 * (ρ + 2 * (L * aK)) + L * aK < (N₁' * L ^ m₁) * L ^ (k + 1))
    {S : Set (CTorus d L N₁ m₁ (k + 1))}
    (hS : ∀ x ∈ S, InBox d ρ ((N₁ * L ^ m₁) * L ^ (k + 1)) x) :
    piHull m₀ (bm '' S) = (piHull m₀ S).image (cubeMap hN hN' le_rfl) := by
  refine subset_antisymm (fun c' hc' => ?_) (piHull_boxMap_subset hN hN' hn hS)
  have ha0 : 0 < L * aK := Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne L)) (cellSide_pos m₀ m₁ _)
  have hS' : ∀ x ∈ bm '' S, InBox d ρ ((N₁' * L ^ m₁) * L ^ (k + 1)) x := by
    rintro _ ⟨x, hx, rfl⟩
    exact inBox_boxMap (by omega) (hS x hx)
  have h1 := piHull_boxMap_subset (N₁ := N₁') (N₁' := N₁) hN' hN hn' hS'
  rw [image_image_boxMap (by omega) hS] at h1
  have hc'R := inBox_of_mem_piHull (by omega) hS' hc'
  refine Finset.mem_image.2 ⟨cubeMap hN' hN le_rfl c', h1 (Finset.mem_image_of_mem _ hc'), ?_⟩
  exact cubeMap_cubeMap (r := ρ + 2 * (L * aK)) hN' hN le_rfl hn
    (hc'R c'.1 (mem_box_self _ (cellSide_pos m₀ m₁ _)))

omit [NeZero N₁'] in
/-- The root set of the coarse site of a fine site `x` is the cell of side `a_K` of `x`. -/
theorem rootSet_blockIndex (x : CTorus d L N₁ m₁ (k + 1)) :
    rootSet m₀ (blockIndex x) = box (cbase aK x) aK := by
  show box (cbase aK (rootSite (blockIndex x))) aK = _
  rw [rootSite_blockIndex, blockBase, cbase_cbase_of_dvd_hull (Nat.pos_of_ne_zero (NeZero.ne _))
    (pow_dvd_cellSide (m₀ := m₀))]

/-- The cell of side `a_K` of a site, on two tori: `bm '' box (cbase a_K x) a_K` is the cell of
`bm x`, when the cell lies in the box of radius `ρ`.  Margin: `2 ρ + a_K < N₁ L^m₁ L^(k+1)`. -/
theorem cell_image (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁') {ρ : ℕ}
    (hn : 2 * ρ + aK < (N₁ * L ^ m₁) * L ^ (k + 1)) (x : CTorus d L N₁ m₁ (k + 1))
    (hbox : ∀ y ∈ box (cbase aK x) aK, InBox d ρ ((N₁ * L ^ m₁) * L ^ (k + 1)) y) :
    bm '' box (cbase aK x) aK = box (cbase aK (bm x)) aK := by
  rw [image_box_boxMap hn (cellSide_pos m₀ m₁ _) hbox,
    cbase_boxMap (cellSide_dvd (K := k + 1) (m₁ := m₁) hN le_rfl)
      (cellSide_dvd (K := k + 1) (m₁ := m₁) hN' le_rfl) (cellSide_pos m₀ m₁ _) hn x hbox]

end Hull

/-! ### D3: the determinant activity on two tori -/

section Activity

variable {d L N₁ N₁' m₁ k N : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ ϱm ϱm' : ℝ} {m₀ : ℕ}

set_option hygiene false in
local notation "bm" => boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1))
set_option hygiene false in
local notation "bm'" => boxMap ((N₁' * L ^ m₁) * L ^ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1))
set_option hygiene false in
local notation "bU" => boxMap ((N₁ * L ^ m₁) * L ^ (k + 1 - k)) ((N₁' * L ^ m₁) * L ^ (k + 1 - k))
set_option hygiene false in
local notation "GA" => levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  (k + 1) le_rfl
set_option hygiene false in
local notation "GB" => levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  (k + 1) le_rfl
set_option hygiene false in
local notation "ιu" b:max => Subtype.mk (bU (b : UnitTorus d L N₁ m₁ k))
  (mem_unitPts_levelTop (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := k) (ϱ := ϱ) _)
set_option hygiene false in
local notation "aK" => cellSide L m₀ m₁ (k + 1)

/-- A cube centre of the top level goes to a cube centre of the top level of the second torus. -/
theorem mem_cubeIdx_image_top {P : ℕ × CTorus d L N₁ m₁ (k + 1)} (hP : P ∈ cubeIdx (GA)) :
    Prod.map id bm P ∈ cubeIdx (GB) := by
  obtain ⟨y0, rfl, hb0⟩ := exists_of_mem_cubeIdx (ϱ := ϱ) le_rfl hP
  exact (mem_cubeIdx_levelGS le_rfl _).2 ⟨rfl, Nat.le_add_left 1 k,
    aligned_boxMap (pow_dvd_side le_rfl N₁) (pow_dvd_side le_rfl N₁') hb0⟩

/-- The patches of the set of image cubes are the images of the patches. -/
theorem patches_filter_image (J : Finset (cubeIdx (GA))) :
    patches (Finset.univ.filter fun P' : cubeIdx (GB) => ∃ P ∈ J, Prod.map id bm P.1 = P'.1) =
      (patches J).image (Prod.map id bm) := by
  ext Q'
  simp only [mem_patches, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨-, P, hP, rfl⟩
    exact ⟨P.1, ⟨P.2, hP⟩, rfl⟩
  · rintro ⟨Q, ⟨hQ, hQJ⟩, rfl⟩
    exact ⟨mem_cubeIdx_image_top hQ, ⟨Q, hQ⟩, hQJ, rfl⟩

omit [NeZero N₁] [NeZero N₁'] [NeZero L] in
/-- Two sites in the same `(k+1)`-block have the same coarse site. -/
theorem blockIndex_eq_of_jBlock_eq {x x' : CTorus d L N₁ m₁ (k + 1)}
    (h : jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) x = jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) x') :
    blockIndex x = blockIndex x' := h

/-- **The hull set on two tori.**  Let `x₀` be a fine site of the unit point `y`, and `J`, `J'`
corresponding sets of parameter cubes (`patches J' = Prod.map id bm '' patches J`).  If the root
cube of `y` and the patches of `J` lie in the box of radius `r`, then the hull set of `(ιu y, J')`
is the image of the hull set of `(y, J)`.  Margins: `2 r + 3 L^(k+1) + 5`, `2 r + a_K` and
`2 r + 5 L · cellSide L 0 m₁ (k+1)` below `N₁ L^m₁ L^(k+1)` (the first also for `N₁'`). -/
theorem hullSet_image_top (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁') {r : ℕ}
    (hn1 : 2 * r + 3 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn2 : 2 * r + aK < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn3 : 2 * r + 5 * (L * cellSide L 0 m₁ (k + 1)) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (y : unitPts (GA)) (J : Finset (cubeIdx (GA))) (J' : Finset (cubeIdx (GB)))
    (hJ' : patches J' = (patches J).image (Prod.map id bm))
    (hbox : ∀ x ∈ hullSet m₀ (rootIdxOf y) (patches J),
      InBox d r ((N₁ * L ^ m₁) * L ^ (k + 1)) x) :
    hullSet m₀ (rootIdxOf (ιu y)) (patches J') = bm '' hullSet m₀ (rootIdxOf y) (patches J) := by
  obtain ⟨x0, -, hx0⟩ := (mem_unitPts _).1 y.2
  have hr0 : rootIdxOf y = blockIndex x0 := rootIdxOf_eq hx0
  have hx0R : InBox d r ((N₁ * L ^ m₁) * L ^ (k + 1)) x0 := by
    refine hbox x0 (Or.inl ?_)
    rw [hr0]; exact mem_rootSet_blockIndex x0
  have hr1 : rootIdxOf (ιu y) = blockIndex (bm x0) :=
    rootIdxOf_eq (unitImage_val (N₁' := N₁') hn1 y hx0 hx0R).symm
  unfold hullSet
  rw [Set.image_union, Set.image_iUnion₂, hJ', Finset.set_biUnion_finset_image]
  congr 1
  · rw [hr0, hr1, rootSet_blockIndex, rootSet_blockIndex]
    refine (cell_image hN hN' hn2 x0 fun z hz => hbox z (Or.inl ?_)).symm
    rw [hr0, rootSet_blockIndex]; exact hz
  · refine Set.iUnion₂_congr fun P hP => ?_
    have hPc : P ∈ cubeIdx (GA) := (mem_patches.1 hP).1
    have hP0 : InBox d r ((N₁ * L ^ m₁) * L ^ (k + 1)) P.2 :=
      hbox P.2 (Or.inr (Set.mem_iUnion₂.2 ⟨P, hP, self_mem_Pset P⟩))
    exact (pset_image_q (m₀ := 0) (N₁' := N₁') le_rfl hn3 hPc hP0).symm

/-- **The hull on two tori.**  Under the hypotheses of `hullSet_image_top`, the hull of
`(ιu y, J')` is the `cubeMap`-image of the hull of `(y, J)`.  Margin also
`2 (r + 2 L a_K) + L a_K < N₁ L^m₁ L^(k+1)` (and for `N₁'`). -/
theorem hullOf_image_top (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁') {r : ℕ}
    (hn1 : 2 * r + 3 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn3 : 2 * r + 5 * (L * cellSide L 0 m₁ (k + 1)) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnH : 2 * (r + 2 * (L * aK)) + L * aK < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnH' : 2 * (r + 2 * (L * aK)) + L * aK < (N₁' * L ^ m₁) * L ^ (k + 1))
    (y : unitPts (GA)) (J : Finset (cubeIdx (GA))) (J' : Finset (cubeIdx (GB)))
    (hJ' : patches J' = (patches J).image (Prod.map id bm))
    (hbox : ∀ x ∈ hullSet m₀ (rootIdxOf y) (patches J),
      InBox d r ((N₁ * L ^ m₁) * L ^ (k + 1)) x) :
    hullOf m₀ (rootIdxOf (ιu y)) (patches J') =
      (hullOf m₀ (rootIdxOf y) (patches J)).image (cubeMap hN hN' le_rfl) := by
  have hcs : aK ≤ L * aK := cellSide_le_mul
  unfold hullOf
  rw [hullSet_image_top hN hN' hn1 (by omega) hn3 y J J' hJ' hbox]
  exact piHull_boxMap hN hN' hnH hnH' hbox

/-- **D3: the determinant activity of a polymer on two tori.**  Let `Y` be a set of level-`(k+1)`
cubes of the first torus with sites in the box of radius `r`, containing the root cube of the unit
point `y`, and `Y' = cubeMap '' Y`.  Under the standing hypotheses of the charts on the two tori
(`FlCore`, data `D`, `D'` of the charts) and if the raw data agree on the box of radius
`r + 3 L^(k+1)`, the determinant activities agree:
`detActivityBg D' (ιu y) Y' = detActivityBg D y Y`.  The sets `J` of parameter cubes with hull `Y`
correspond to the sets `J'` with hull `Y'` (`hullOf_image_top`; the patches lie in the box because
they lie in the sites of the hull), and the mixed differences agree
(`mixDiff_rootTraceBg_twoTorus`).  Margins: `4 r + 12 L^(k+1+m₁) + 7 L^(k+1) + 5`,
`2 r₁ + 5 L · cellSide L 0 m₁ (k+1)` (`r₁ = r + (3 L^(k+1+m₁) + 3 L^(k+3)) + L^(k+1+m₁)`) and
`2 (r + 2 L a_K) + L a_K` below `N₁ L^m₁ L^(k+1)` and `N₁' L^m₁ L^(k+1)`. -/
theorem detActivityBg_twoTorus (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁')
    {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
    {Hm' : GeneratingSet d L (N₁' * L ^ m₁) (k + 1) ϱm'}
    {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ}
    (hC : FlCore N (GA) Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hC' : FlCore N (GB) Hm' a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (hk : 1 ≤ k) {δc : ℝ}
    (hδc : 0 ≤ δc) (hcap : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hαK : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hconn : HatConn (GA)) (hconn' : HatConn (GB))
    {D : BgData (GA) N} {D' : BgData (GB) N}
    (hD : XiCData (GA) (compWeight L a₁) ν (k + 1) 1 eps D)
    (hD' : XiCData (GB) (compWeight L a₁) ν (k + 1) 1 eps D')
    (y : unitPts (GA))
    (Y : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ))
    (hyY : rootCube (m₀ := m₀) (rootIdxOf y) ∈ Y) {r : ℕ}
    (hYr : ∀ x ∈ sitesOf Y, InBox d r ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    (hn : 4 * r + 12 * L ^ (k + 1 + m₁) + 7 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 4 * r + 12 * L ^ (k + 1 + m₁) + 7 * L ^ (k + 1) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hnS : 2 * (r + (3 * L ^ (k + 1 + m₁) + 3 * L ^ (k + 1 + 2)) + L ^ (k + 1 + m₁)) +
      5 * (L * cellSide L 0 m₁ (k + 1)) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnS' : 2 * (r + (3 * L ^ (k + 1 + m₁) + 3 * L ^ (k + 1 + 2)) + L ^ (k + 1 + m₁)) +
      5 * (L * cellSide L 0 m₁ (k + 1)) < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hnH : 2 * (r + 2 * (L * aK)) + L * aK < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnH' : 2 * (r + 2 * (L * aK)) + L * aK < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hraw : RawBoxAgree {z | InBox d (r + 3 * L ^ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1)) z}
      (rawOf D) (rawOf D')) :
    detActivityBg m₀ (compWeight L a₁) a₁ ν (rho4 d L N BG κ) D' (ιu y)
        (Y.image (cubeMap hN hN' le_rfl)) =
      detActivityBg m₀ (compWeight L a₁) a₁ ν (rho4 d L N BG κ) D y Y := by
  classical
  have hcs : aK ≤ L * aK := cellSide_le_mul
  have ha0 : 0 < L * aK := Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne L)) (cellSide_pos m₀ m₁ _)
  have hK1 : 1 ≤ L ^ (k + 1) := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (NeZero.ne L))
  have hn3 : 2 * r + 5 * (L * cellSide L 0 m₁ (k + 1)) < (N₁ * L ^ m₁) * L ^ (k + 1) := by omega
  have hn3' : 2 * r + 5 * (L * cellSide L 0 m₁ (k + 1)) < (N₁' * L ^ m₁) * L ^ (k + 1) := by
    omega
  set f : ℕ × CTorus d L N₁ m₁ (k + 1) → ℕ × CTorus d L N₁' m₁ (k + 1) := Prod.map id bm with hf
  set f' : ℕ × CTorus d L N₁' m₁ (k + 1) → ℕ × CTorus d L N₁ m₁ (k + 1) := Prod.map id bm'
    with hf'
  -- the root cell of `y` lies in the box
  have hroot : ∀ x ∈ rootSet m₀ (rootIdxOf y), InBox d r ((N₁ * L ^ m₁) * L ^ (k + 1)) x :=
    fun x hx => hYr x (mem_sitesOf.2 ⟨_, hyY, hx⟩)
  -- the hull set of a set with hull `Y` lies in the box
  have hboxA : ∀ J : Finset (cubeIdx (GA)), hullOf m₀ (rootIdxOf y) (patches J) = Y →
      ∀ x ∈ hullSet m₀ (rootIdxOf y) (patches J), InBox d r ((N₁ * L ^ m₁) * L ^ (k + 1)) x := by
    intro J hJ x hx
    refine hYr x ?_
    rw [← hJ]
    exact subset_sitesOf_piHull hN _ hx
  -- the sites of `Y'`
  have hY'sites : sitesOf (Y.image (cubeMap hN hN' le_rfl)) = bm '' sitesOf Y :=
    sitesOf_image_cubeMap hN hN' le_rfl (by omega) Y hYr
  have hY'r : ∀ x ∈ sitesOf (Y.image (cubeMap hN hN' le_rfl)),
      InBox d r ((N₁' * L ^ m₁) * L ^ (k + 1)) x := by
    rw [hY'sites]
    rintro _ ⟨x, hx, rfl⟩
    exact inBox_boxMap (by omega) (hYr x hx)
  -- the correspondence of sets of parameter cubes
  let i : Finset (cubeIdx (GA)) → Finset (cubeIdx (GB)) := fun J =>
    Finset.univ.filter fun P' => ∃ P ∈ J, f P.1 = P'.1
  let j : Finset (cubeIdx (GB)) → Finset (cubeIdx (GA)) := fun J' =>
    Finset.univ.filter fun P => ∃ P' ∈ J', f' P'.1 = P.1
  have hpi : ∀ J, patches (i J) = (patches J).image f := patches_filter_image
  have hpj : ∀ J', patches (j J') = (patches J').image f' :=
    patches_filter_image (N₁ := N₁') (N₁' := N₁)
  -- patches of a set with hull `Y` (resp. `Y'`) lie in the box
  have hPA : ∀ J : Finset (cubeIdx (GA)), hullOf m₀ (rootIdxOf y) (patches J) = Y →
      ∀ P ∈ J, InBox d r ((N₁ * L ^ m₁) * L ^ (k + 1)) P.1.2 := fun J hJ P hP =>
    hboxA J hJ P.1.2 (Or.inr (Set.mem_iUnion₂.2 ⟨P.1, mem_patches.2 ⟨P.2, hP⟩, self_mem_Pset _⟩))
  have hPB : ∀ J' : Finset (cubeIdx (GB)),
      hullOf m₀ (rootIdxOf (ιu y)) (patches J') = Y.image (cubeMap hN hN' le_rfl) →
      ∀ P' ∈ J', ∀ x ∈ Pset m₁ P'.1, InBox d r ((N₁' * L ^ m₁) * L ^ (k + 1)) x := by
    intro J' hJ' P' hP' x hx
    refine hY'r x ?_
    rw [← hJ']
    exact subset_sitesOf_piHull hN' _ (Or.inr (Set.mem_iUnion₂.2
      ⟨P'.1, mem_patches.2 ⟨P'.2, hP'⟩, hx⟩))
  have hleft : ∀ J : Finset (cubeIdx (GA)), (∀ P ∈ J, InBox d r ((N₁ * L ^ m₁) * L ^ (k + 1))
      P.1.2) → j (i J) = J := by
    intro J hJ
    ext P
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, i, j]
    constructor
    · rintro ⟨P', ⟨Q, hQ, hQP'⟩, hP'P⟩
      have e : f' (f Q.1) = Q.1 := Prod.ext rfl (boxMap_boxMap (by omega) (hJ Q hQ))
      rw [hQP', hP'P] at e
      rw [Subtype.ext e]; exact hQ
    · intro hP
      exact ⟨⟨f P.1, mem_cubeIdx_image_top P.2⟩, ⟨P, hP, rfl⟩,
        Prod.ext rfl (boxMap_boxMap (by omega) (hJ P hP))⟩
  have hright : ∀ J' : Finset (cubeIdx (GB)), (∀ P' ∈ J', InBox d r
      ((N₁' * L ^ m₁) * L ^ (k + 1)) P'.1.2) → i (j J') = J' := by
    intro J' hJ'
    ext P'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, i, j]
    constructor
    · rintro ⟨P, ⟨Q', hQ', hQ'P⟩, hPP'⟩
      have e : f (f' Q'.1) = Q'.1 := Prod.ext rfl (boxMap_boxMap (by omega) (hJ' Q' hQ'))
      rw [hQ'P, hPP'] at e
      rw [Subtype.ext e]; exact hQ'
    · intro hP'
      exact ⟨⟨f' P'.1, mem_cubeIdx_image_top (N₁ := N₁') (N₁' := N₁) P'.2⟩, ⟨P', hP', rfl⟩,
        Prod.ext rfl (boxMap_boxMap (by omega) (hJ' P' hP'))⟩
  unfold detActivityBg
  symm
  refine Finset.sum_nbij' i j (fun J hJ => ?_) (fun J' hJ' => ?_) (fun J hJ => ?_)
    (fun J' hJ' => ?_) (fun J hJ => ?_)
  · -- `i J` has hull `Y'`
    obtain ⟨-, hJY⟩ := Finset.mem_filter.1 hJ
    refine Finset.mem_filter.2 ⟨Finset.mem_powerset.2 (Finset.subset_univ _), ?_⟩
    rw [hullOf_image_top hN hN' (by omega) hn3 hnH hnH' y J (i J) (hpi J) (hboxA J hJY), hJY]
  · -- `j J'` has hull `Y`
    obtain ⟨-, hJY⟩ := Finset.mem_filter.1 hJ'
    refine Finset.mem_filter.2 ⟨Finset.mem_powerset.2 (Finset.subset_univ _), ?_⟩
    have hJ'box : ∀ P' ∈ J', InBox d r ((N₁' * L ^ m₁) * L ^ (k + 1)) P'.1.2 :=
      fun P' hP' => hPB J' hJY P' hP' P'.1.2 (self_mem_Pset _)
    have hbox : ∀ x ∈ hullSet m₀ (rootIdxOf y) (patches (j J')),
        InBox d r ((N₁ * L ^ m₁) * L ^ (k + 1)) x := by
      rintro x (hx | hx)
      · exact hroot x hx
      · obtain ⟨P, hP, hxP⟩ := Set.mem_iUnion₂.1 hx
        rw [hpj] at hP
        obtain ⟨P', hP', rfl⟩ := Finset.mem_image.1 hP
        obtain ⟨hP'c, hP'J⟩ := mem_patches.1 hP'
        rw [← pset_image_q (m₀ := 0) (N₁ := N₁') (N₁' := N₁) le_rfl hn3' hP'c
          (hJ'box ⟨P', hP'c⟩ hP'J)] at hxP
        obtain ⟨z, hz, rfl⟩ := hxP
        exact inBox_boxMap (by omega) (hPB J' hJY ⟨P', hP'c⟩ hP'J z hz)
    have e := hullOf_image_top hN hN' (by omega) hn3 hnH hnH' y (j J') (i (j J')) (hpi _) hbox
    rw [hright J' hJ'box, hJY] at e
    have hT : ∀ x ∈ sitesOf (hullOf m₀ (rootIdxOf y) (patches (j J'))),
        InBox d (r + 2 * (L * aK)) ((N₁ * L ^ m₁) * L ^ (k + 1)) x := by
      intro x hx
      obtain ⟨c, hc, hxc⟩ := mem_sitesOf.1 hx
      exact inBox_of_mem_piHull (by omega) hbox hc x hxc
    have hYr' : ∀ x ∈ sitesOf Y, InBox d (r + 2 * (L * aK)) ((N₁ * L ^ m₁) * L ^ (k + 1)) x :=
      fun x hx => inBox_mono (by omega) (hYr x hx)
    have e2 := congrArg (Finset.image (cubeMap hN' hN le_rfl)) e
    rw [image_image_cubeMap (r := r + 2 * (L * aK)) hN hN' le_rfl hnH' Y hYr',
      image_image_cubeMap (r := r + 2 * (L * aK)) hN hN' le_rfl hnH' _ hT] at e2
    exact e2.symm
  · obtain ⟨-, hJY⟩ := Finset.mem_filter.1 hJ
    exact hleft J (hPA J hJY)
  · obtain ⟨-, hJY⟩ := Finset.mem_filter.1 hJ'
    exact hright J' fun P' hP' => hPB J' hJY P' hP' P'.1.2 (self_mem_Pset _)
  · -- the mixed differences agree
    obtain ⟨-, hJY⟩ := Finset.mem_filter.1 hJ
    obtain ⟨x0, -, hx0⟩ := (mem_unitPts _).1 y.2
    have hbR : ∀ x : CTorus d L N₁ m₁ (k + 1), unitBlock1 (unitBlock x) =
        unitBlock1 (y : UnitTorus d L N₁ m₁ k) → InBox d r ((N₁ * L ^ m₁) * L ^ (k + 1)) x := by
      intro x hx
      refine hroot x ?_
      have h : jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) x =
          jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) x0 := by
        rw [← unitBlock1_unitBlock x, ← unitBlock1_unitBlock x0, hx, hx0]
      rw [rootIdxOf_eq hx0, ← blockIndex_eq_of_jBlock_eq h]
      exact mem_rootSet_blockIndex x
    have hJR : ∀ P ∈ patches J, ∀ x ∈ cubeP P, InBox d r ((N₁ * L ^ m₁) * L ^ (k + 1)) x := by
      intro P hP x hx
      refine hboxA J hJY x (Or.inr (Set.mem_iUnion₂.2 ⟨P, hP, ?_⟩))
      rw [← coe_cubeP_eq_Pset]; exact hx
    exact (mixDiff_rootTraceBg_twoTorus hC hC' hk hδc hcap hsm hmar hαK hconn hconn' hD hD' J
      (i J) (hpi J) hbR hJR hn hn' hnS hnS' hraw).symm

end Activity

end Balaban.Polymer.TwoTorusStep
