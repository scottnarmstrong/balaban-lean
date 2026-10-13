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
on the unit lattices), this file compares the terms of the rooted determinant expansion.

* `unitImage_inj`: the map `ιu` of unit points is injective on unit points with a fine site in the
  box.
* `decLog_diag_transport` (D1): the diagonal entries of the decoupled logarithm
  `𝕃(s) = log a_k (1 - P) + log (a_k + b) P - ∫₀^∞ (C_x(s) - A_{k,x}) dx` (`decLog`) agree at
  corresponding unit points whose `(k+1)`-block lies in a component `Y` of the cut, under the
  hypotheses of `decCov_rows_transport` for every `x ≥ 0`; `rootTrace_single_transport` is the
  rooted trace of one unit block.
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Polymer.TwoTorusStep

open Balaban Balaban.Localization Balaban.Fluctuation Balaban.SmallField.Def6 Balaban.Polymer
  Balaban.Multiscale Balaban.Background Balaban.Analysis Matrix

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

end Balaban.Polymer.TwoTorusStep
