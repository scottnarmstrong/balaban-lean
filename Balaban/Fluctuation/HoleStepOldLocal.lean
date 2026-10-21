/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.HoleStepPointLocal
public import Balaban.Fluctuation.HoleStepOldCoef
public import Balaban.Localization.I5Param

/-!
# The locality (AE2) of the re-expansion of an old boundary term (OPEN-P6-ACTIVE-COMPOSITE-LOC, R12)

P6 p. 34: the old term `ℬ^{(k)}(X)` evaluated at the composed field with the localization vectors
`v_b(w) = slocOf X₁loc (coreExt X₁ w) b` is expanded by Lemma AE in the parameters `w` of the cover
cubes off the core `X₁`.  Under the reading R12 (`notes/phase1/PLAN-B.md`) the hypothesis (AE2) of
Lemma AE is the statement OPEN-P6-ACTIVE-COMPOSITE-LOC; this file proves it from the single-pair
locality of `Fluctuation/HoleStepPointLocal.lean`, for an old term that reads the composed field at
the unit points of a finite set `Rd`, under the standing conditions of the decoupled objects of the
pair `(coverOf G′, G′)` at the localization vectors (the domain of Theorem I-4b and of the covariance,
OPEN-H7-MIXED) and two geometric conditions on the localization domains.

* `famInd`: the indicator vector of a family `J` of cover cubes (all its parameters equal to `1`);
* `reachSet`: **the region `Y(J)` reached by a family**: the sites of the footprint cubes of the
  active closures, from the read unit points `b ∈ Rd`, at the localization vectors of `famInd J`;
* `extS_slocVec`, `slocVec_ne_zero`, `actC_slocVec_mono`, `sProd_slocVec_eq`, `norm_slocVec_le`:
  the localization vectors of two parameter vectors supported on `J` and agreeing on the cubes of
  `J` inside `Y(J)` have the same factors on the closures;
* `oldInterp_localityAEOn`: **(AE2) for the interpolated old term**: `LocalityAEOn` of
  `w ↦ oldInterp … w` with the connectivity region `reachSet`;
* `oldCoef_eq_zero_of_not_reached`: `T(X, J) = 0` unless every cube of `J` lies in `Y(J)` (the
  coefficients are rooted at the read set through chains of active centres).
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.LargeField
  Balaban.SmallField

namespace HoleStep

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱ' : ℝ}
  (S : HoleStep d L N₁ m₁ k N ϱ ϱ')

open Classical in
/-- The indicator vector of a family `J` of cover cubes. -/
noncomputable def famInd {C : DecCover d L N₁ m₁ (k + 1)} (J : Finset C.cubeIdx) :
    Dec2.DecParams C :=
  fun P => if P ∈ J then 1 else 0

open Classical in
/-- **The region reached by a family `J`** (the connectivity region `Y(J)` of Lemma AE for the
re-expansion of an old term read at the unit points of `Rd`): the sites of the footprint cubes of
the active closures of the seeds `{b}`, `b ∈ Rd`, at the localization vectors of `famInd J`. -/
def reachSet (C : DecCover d L N₁ m₁ (k + 1)) (X₁loc : S.U → Finset (CTorus d L N₁ m₁ (k + 1)))
    (X₁ : Finset (CTorus d L N₁ m₁ (k + 1))) (D : ℕ) (Rd : Finset S.U) (J : Finset C.cubeIdx) :
    Set (CTorus d L N₁ m₁ (k + 1)) :=
  {x | ∃ b ∈ Rd, ∃ q ∈ actComp C D (Dec2.extS C (S.slocOf C X₁loc (coreExt C X₁ (famInd J)) b))
    {(unitRep b : CTorus d L N₁ m₁ (k + 1))}, ∃ P ∈ C.Qset q, x ∈ cubeP P}

variable {S}

open Classical in
/-- The extended localization vector on a cover cube. -/
theorem extS_slocVec (C : DecCover d L N₁ m₁ (k + 1))
    (X₁loc : S.U → Finset (CTorus d L N₁ m₁ (k + 1))) (X₁ : Finset (CTorus d L N₁ m₁ (k + 1)))
    (w : Dec2.DecParams C) (b : S.U) {P : ℕ × CTorus d L N₁ m₁ (k + 1)} (hP : P ∈ C.cubeIdx) :
    Dec2.extS C (S.slocOf C X₁loc (coreExt C X₁ w) b) P =
      (if cubeP P ⊆ X₁ then 1 else w ⟨P, hP⟩) * (if cubeP P ⊆ X₁loc b then 1 else 0) := by
  simp [Dec2.extS, hP, slocOf, coreExt]

open Classical in
/-- A non-zero factor of a localization vector: the cube lies in the localization domain, and in
the core or carries a non-zero parameter. -/
theorem slocVec_ne_zero {C : DecCover d L N₁ m₁ (k + 1)}
    {X₁loc : S.U → Finset (CTorus d L N₁ m₁ (k + 1))} {X₁ : Finset (CTorus d L N₁ m₁ (k + 1))}
    {w : Dec2.DecParams C} {b : S.U} {P : ℕ × CTorus d L N₁ m₁ (k + 1)} (hP : P ∈ C.cubeIdx)
    (h : Dec2.extS C (S.slocOf C X₁loc (coreExt C X₁ w) b) P ≠ 0) :
    cubeP P ⊆ X₁loc b ∧ (cubeP P ⊆ X₁ ∨ w ⟨P, hP⟩ ≠ 0) := by
  rw [extS_slocVec C X₁loc X₁ w b hP] at h
  by_cases h1 : cubeP P ⊆ X₁loc b
  · refine ⟨h1, ?_⟩
    by_cases h2 : cubeP P ⊆ X₁
    · exact Or.inl h2
    · right
      simpa [h1, h2] using h
  · simp [h1] at h

/-- The active centres of the localization vector of `w` (supported on `J`) are active for the
localization vector of the indicator of `J`. -/
theorem actC_slocVec_mono {C : DecCover d L N₁ m₁ (k + 1)}
    {X₁loc : S.U → Finset (CTorus d L N₁ m₁ (k + 1))} {X₁ : Finset (CTorus d L N₁ m₁ (k + 1))}
    {J : Finset C.cubeIdx} {w : Dec2.DecParams C} (hw : w ∈ supportedOn J) (b : S.U)
    (q : ℕ × CTorus d L N₁ m₁ (k + 1))
    (hq : ActC C (Dec2.extS C (S.slocOf C X₁loc (coreExt C X₁ w) b)) q) :
    ActC C (Dec2.extS C (S.slocOf C X₁loc (coreExt C X₁ (famInd J)) b)) q := by
  classical
  have hq2 := (Dec2.sProd_ne_zero_iff _ q).1 hq.2
  refine ⟨hq.1, (Dec2.sProd_ne_zero_iff _ q).2 fun P hP => ?_⟩
  have hPC : P ∈ C.cubeIdx := Dec2.Qset_subset_cubeIdx q hP
  obtain ⟨h1, h2⟩ := slocVec_ne_zero hPC (hq2 P hP)
  rw [extS_slocVec C X₁loc X₁ _ b hPC]
  by_cases h3 : cubeP P ⊆ X₁
  · simp [h1, h3]
  · have hw0 : w ⟨P, hPC⟩ ≠ 0 := h2.resolve_left h3
    have hJ : (⟨P, hPC⟩ : C.cubeIdx) ∈ J := by
      by_contra hJ
      exact hw0 (hw _ hJ)
    simp [h1, h3, famInd, hJ]

/-- **Two parameter vectors supported on `J` agreeing on the cubes of `J` inside the reached region
have the same factors on the closures of the indicator of `J`.** -/
theorem sProd_slocVec_eq {C : DecCover d L N₁ m₁ (k + 1)}
    {X₁loc : S.U → Finset (CTorus d L N₁ m₁ (k + 1))} {X₁ : Finset (CTorus d L N₁ m₁ (k + 1))}
    {D : ℕ} {Rd : Finset S.U} {J : Finset C.cubeIdx} {w w' : Dec2.DecParams C}
    (hw : w ∈ supportedOn J) (hw' : w' ∈ supportedOn J)
    (hag : ∀ P ∈ J, (cubeP (P : ℕ × CTorus d L N₁ m₁ (k + 1)) : Set (CTorus d L N₁ m₁ (k + 1))) ⊆
      S.reachSet C X₁loc X₁ D Rd J → w P = w' P)
    {b : S.U} (hb : b ∈ Rd) {q : ℕ × CTorus d L N₁ m₁ (k + 1)}
    (hq : q ∈ actComp C D (Dec2.extS C (S.slocOf C X₁loc (coreExt C X₁ (famInd J)) b))
      {(unitRep b : CTorus d L N₁ m₁ (k + 1))}) :
    C.sProd (Dec2.extS C (S.slocOf C X₁loc (coreExt C X₁ w) b)) q =
      C.sProd (Dec2.extS C (S.slocOf C X₁loc (coreExt C X₁ w') b)) q := by
  classical
  unfold DecCover.sProd
  refine Finset.prod_congr rfl fun P hP => ?_
  have hPC : P ∈ C.cubeIdx := Dec2.Qset_subset_cubeIdx q hP
  rw [extS_slocVec C X₁loc X₁ w b hPC, extS_slocVec C X₁loc X₁ w' b hPC]
  by_cases h3 : cubeP P ⊆ X₁
  · simp [h3]
  · simp only [h3, ↓reduceIte]
    congr 1
    by_cases hJ : (⟨P, hPC⟩ : C.cubeIdx) ∈ J
    · refine hag _ hJ fun x hx => ⟨b, hb, q, hq, P, hP, hx⟩
    · rw [hw _ hJ, hw' _ hJ]

/-- A localization vector of a parameter vector in the polydisc of radius `R ≥ 1` is in that
polydisc. -/
theorem norm_slocVec_le {C : DecCover d L N₁ m₁ (k + 1)}
    {X₁loc : S.U → Finset (CTorus d L N₁ m₁ (k + 1))} {X₁ : Finset (CTorus d L N₁ m₁ (k + 1))}
    {w : Dec2.DecParams C} {R : ℝ} (hR : 1 ≤ R) (hw : ∀ P, ‖w P‖ ≤ R) (b : S.U)
    (P : C.cubeIdx) : ‖S.slocOf C X₁loc (coreExt C X₁ w) b P‖ ≤ R := by
  classical
  have hR0 : (0 : ℝ) ≤ R := by linarith
  unfold slocOf coreExt
  split_ifs <;> simp [hR, hw, hR0]

/-- **(AE2) for the interpolated old term** (OPEN-P6-ACTIVE-COMPOSITE-LOC under R12).  For an old
term `B` reading the composed field only at the unit points of `Rd`, the cover `coverOf G′`, the
localization domains `X₁loc`, the core `X₁` and parameters in the polydisc of radius `R`
(`1 ≤ R ≤ e^κ`): two parameter vectors supported on `J` that agree on the cubes of `J` inside the
reached region `Y(J)` give the same value of `F_X`.  Hypotheses beyond those of
`composed_eq_of_hull`: the standing conditions of the covariance at every vector of the polydisc of
radius `e^κ` (`hstand`), a centre covering each read point with its footprint in the core and in its
localization domain (`hcov`), and interaction boxes of centres with footprint in a localization domain
at distance `4 L^{k+1}` from the complement of `Ω₁(G′)` (`hlocdeep`). -/
theorem oldInterp_localityAEOn {Kc Cx Cx₂ c BG : ℝ} (hS : Dec2.DecSpecs d L Kc Cx c BG)
    (Sb : Dec2.CoverBase (coverOf S.G') S.G' S.a S.ν Kc Cx)
    (SX : Dec2.XCover (coverOf S.G') S.G' S.a S.a₁ S.ν Cx₂)
    (HB : BgHyp d L (k + 1) ϱ' S.a S.ν) {κ : ℝ} (hκ : 0 ≤ κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    {δ ε : ℝ} (hδ0 : 0 < δ) (hδε : δ ≤ ε) (hε : ε ≤ bgC0 d L N) (hδ : δ ≤ c7 d L N BG κ)
    (hνε : S.ν * ((L : ℝ) ^ (k + 1)) ^ 2 * ε ^ 2 ≤ δ ^ 2) (hD' : InDomainC S.G' S.ν δ ε S.D')
    {D : ℕ} (hDD : L ^ (k + 1) + 2 * L ^ (k + 1) ≤ D)
    (X₁loc : S.U → Finset (CTorus d L N₁ m₁ (k + 1))) (X₁ : Finset (CTorus d L N₁ m₁ (k + 1)))
    (inner : Finset S.U) (ψout : S.U → Fin N → ℂ) {B : (S.U → Fin N → ℂ) → ℂ} {Rd : Finset S.U}
    (hB : ∀ c c' : S.U → Fin N → ℂ, (∀ b ∈ Rd, c b = c' b) → B c = B c')
    {R : ℝ} (hR1 : 1 ≤ R) (hRk : R ≤ Real.exp κ)
    (hstand : ∀ v : Dec2.DecParams (coverOf S.G'), (∀ P, ‖v P‖ ≤ Real.exp κ) →
      AdmPot S.G' (Dec2.decBgMult (coverOf S.G') S.G' S.a S.ν (rho4 d L N BG κ) v S.D') ∧
      (∀ x : ℝ, 0 < x → IsUnit (1 - Dec2.Kcalx (coverOf S.G') S.G' S.a S.a₁ x S.ν
        (Dec2.decBgMult (coverOf S.G') S.G' S.a S.ν (rho4 d L N BG κ) v S.D') (Dec2.extS _ v))) ∧
      (∀ x : ℝ, 0 < x → IsUnit (Dec2.decM (coverOf S.G') S.G' S.a S.a₁ x S.ν
        (Dec2.decBgMult (coverOf S.G') S.G' S.a S.ν (rho4 d L N BG κ) v S.D') (Dec2.extS _ v)
        (svec S.G' (Dec2.decBgField (coverOf S.G') S.G' S.a S.ν (rho4 d L N BG κ) v S.D')))))
    (hcov : ∀ b ∈ Rd, ∃ q ∈ (coverOf S.G').cubeIdx,
      (unitRep b : CTorus d L N₁ m₁ (k + 1)) ∈ intBox q ∧
        ∀ P ∈ (coverOf S.G').Qset q, cubeP P ⊆ X₁ ∧ cubeP P ⊆ X₁loc b)
    (hlocdeep : ∀ b ∈ Rd, ∀ q ∈ (coverOf S.G').cubeIdx,
      (∀ P ∈ (coverOf S.G').Qset q, cubeP P ⊆ X₁loc b) → ∀ x ∈ intBox q,
        ∀ z : CTorus d L N₁ m₁ (k + 1), supDist x z ≤ 4 * L ^ (k + 1) → z ∈ S.G'.Ω 1) :
    LocalityAEOn R Set.univ
      (fun P : (coverOf S.G').cubeIdx =>
        (cubeP (P : ℕ × CTorus d L N₁ m₁ (k + 1)) : Set (CTorus d L N₁ m₁ (k + 1))))
      (S.reachSet (coverOf S.G') X₁loc X₁ D Rd) (fun _ u u' => u = u')
      (fun ψin w => S.oldInterp (coverOf S.G') (rho4 d L N BG κ) X₁loc X₁ inner ψout B ψin w) := by
  classical
  intro J u u' _ _ w w' hw hw' hag huu
  subst huu
  have hE1 : (1 : ℝ) ≤ Real.exp κ := Real.one_le_exp_iff.2 hκ
  have hwle : ∀ P, ‖w P‖ ≤ R := fun P => (hw.2 P).le
  have hwle' : ∀ P, ‖w' P‖ ≤ R := fun P => (hw'.2 P).le
  unfold oldInterp
  refine hB _ _ fun b hb => ?_
  set v := S.slocOf (coverOf S.G') X₁loc (coreExt (coverOf S.G') X₁ w) b with hvdef
  set v' := S.slocOf (coverOf S.G') X₁loc (coreExt (coverOf S.G') X₁ w') b with hv'def
  have hv : ∀ P, ‖v P‖ ≤ Real.exp κ := fun P => (norm_slocVec_le hR1 hwle b P).trans hRk
  have hv' : ∀ P, ‖v' P‖ ≤ Real.exp κ := fun P => (norm_slocVec_le hR1 hwle' b P).trans hRk
  obtain ⟨hadm, hU, hMu⟩ := hstand v hv
  obtain ⟨hadm', hU', hMu'⟩ := hstand v' hv'
  have hsup := actC_slocVec_mono (X₁loc := X₁loc) (X₁ := X₁) hw.1 b
  have hsup' := actC_slocVec_mono (X₁loc := X₁loc) (X₁ := X₁) hw'.1 b
  have hcomp : ∀ q ∈ actComp (coverOf S.G') D (Dec2.extS _ (S.slocOf (coverOf S.G') X₁loc
        (coreExt (coverOf S.G') X₁ (famInd J)) b)) {(unitRep b : CTorus d L N₁ m₁ (k + 1))},
      (coverOf S.G').sProd (Dec2.extS _ v) q = (coverOf S.G').sProd (Dec2.extS _ v') q :=
    fun q hq => sProd_slocVec_eq hw.1 hw'.1 (fun P hP hPY => hag P hP hPY) hb hq
  -- the active centres of `v` have their footprints in the localization domain of `b`
  have hfoot : ∀ q, ActC (coverOf S.G') (Dec2.extS _ v) q →
      ∀ P ∈ (coverOf S.G').Qset q, cubeP P ⊆ X₁loc b := by
    intro q hq P hP
    have hPC : P ∈ (coverOf S.G').cubeIdx := Dec2.Qset_subset_cubeIdx q hP
    exact (slocVec_ne_zero hPC ((Dec2.sProd_ne_zero_iff _ q).1 hq.2 P hP)).1
  have hdeep : ∀ y ∈ actHull (coverOf S.G') D (Dec2.extS _ v) {(unitRep b : CTorus d L N₁ m₁ (k + 1))},
      ∀ z : CTorus d L N₁ m₁ (k + 1), supDist y z ≤ 2 * L ^ (k + 1) → z ∈ S.G'.Ω 1 := by
    intro y hy z hyz
    obtain ⟨q, hq, x, hx, hxy⟩ := exists_of_mem_actHull hy
    have hqa := act_of_mem_actComp hq
    refine hlocdeep b hb q hqa.1 (hfoot q hqa) x hx z ?_
    have := supDist_triangle x y z
    omega
  -- the read point is covered by an active centre
  obtain ⟨q₀, hq₀C, hbq₀, hq₀P⟩ := hcov b hb
  have hq₀act : ActC (coverOf S.G') (Dec2.extS _ v) q₀ := by
    refine ⟨hq₀C, (Dec2.sProd_ne_zero_iff _ q₀).2 fun P hP => ?_⟩
    have hPC : P ∈ (coverOf S.G').cubeIdx := Dec2.Qset_subset_cubeIdx q₀ hP
    rw [hvdef, extS_slocVec _ X₁loc X₁ w b hPC]
    simp [(hq₀P P hP).1, (hq₀P P hP).2]
  have hbT : (unitRep b : CTorus d L N₁ m₁ (k + 1)) ∈
      actHull (coverOf S.G') D (Dec2.extS _ v) {(unitRep b : CTorus d L N₁ m₁ (k + 1))} :=
    seed_subset_actHull (fun y hy => ⟨q₀, hq₀act, by rw [Finset.mem_singleton.1 hy]; exact hbq₀⟩)
      _ (Finset.mem_singleton_self _)
  exact S.composed_eq_of_hull hS Sb SX HB hκ hM hv hv' hδ0 hδε hε hδ hνε hD' hDD _ hsup hsup'
    hcomp hdeep hadm hadm' hU hU' hMu hMu' rfl rfl hbT (fun _ _ => rfl)

/-- **The coefficients of the re-expansion are rooted at the read set** (Lemma AE with (AE2)
`oldInterp_localityAEOn`): `T(X, J) = 0` unless every cube of `J` lies in the region `Y(J)` reached
from the read unit points through chains of active centres. -/
theorem oldCoef_eq_zero_of_not_reached {Kc Cx Cx₂ c BG : ℝ} (hS : Dec2.DecSpecs d L Kc Cx c BG)
    (Sb : Dec2.CoverBase (coverOf S.G') S.G' S.a S.ν Kc Cx)
    (SX : Dec2.XCover (coverOf S.G') S.G' S.a S.a₁ S.ν Cx₂)
    (HB : BgHyp d L (k + 1) ϱ' S.a S.ν) {κ : ℝ} (hκ : 0 ≤ κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    {δ ε : ℝ} (hδ0 : 0 < δ) (hδε : δ ≤ ε) (hε : ε ≤ bgC0 d L N) (hδ : δ ≤ c7 d L N BG κ)
    (hνε : S.ν * ((L : ℝ) ^ (k + 1)) ^ 2 * ε ^ 2 ≤ δ ^ 2) (hD' : InDomainC S.G' S.ν δ ε S.D')
    {D : ℕ} (hDD : L ^ (k + 1) + 2 * L ^ (k + 1) ≤ D)
    (X₁loc : S.U → Finset (CTorus d L N₁ m₁ (k + 1))) (X₁ : Finset (CTorus d L N₁ m₁ (k + 1)))
    (inner : Finset S.U) (ψout : S.U → Fin N → ℂ) {B : (S.U → Fin N → ℂ) → ℂ} {Rd : Finset S.U}
    (hB : ∀ c c' : S.U → Fin N → ℂ, (∀ b ∈ Rd, c b = c' b) → B c = B c')
    {R : ℝ} (hR1 : 1 < R) (hRk : R ≤ Real.exp κ)
    (hstand : ∀ v : Dec2.DecParams (coverOf S.G'), (∀ P, ‖v P‖ ≤ Real.exp κ) →
      AdmPot S.G' (Dec2.decBgMult (coverOf S.G') S.G' S.a S.ν (rho4 d L N BG κ) v S.D') ∧
      (∀ x : ℝ, 0 < x → IsUnit (1 - Dec2.Kcalx (coverOf S.G') S.G' S.a S.a₁ x S.ν
        (Dec2.decBgMult (coverOf S.G') S.G' S.a S.ν (rho4 d L N BG κ) v S.D') (Dec2.extS _ v))) ∧
      (∀ x : ℝ, 0 < x → IsUnit (Dec2.decM (coverOf S.G') S.G' S.a S.a₁ x S.ν
        (Dec2.decBgMult (coverOf S.G') S.G' S.a S.ν (rho4 d L N BG κ) v S.D') (Dec2.extS _ v)
        (svec S.G' (Dec2.decBgField (coverOf S.G') S.G' S.a S.ν (rho4 d L N BG κ) v S.D')))))
    (hcov : ∀ b ∈ Rd, ∃ q ∈ (coverOf S.G').cubeIdx,
      (unitRep b : CTorus d L N₁ m₁ (k + 1)) ∈ intBox q ∧
        ∀ P ∈ (coverOf S.G').Qset q, cubeP P ⊆ X₁ ∧ cubeP P ⊆ X₁loc b)
    (hlocdeep : ∀ b ∈ Rd, ∀ q ∈ (coverOf S.G').cubeIdx,
      (∀ P ∈ (coverOf S.G').Qset q, cubeP P ⊆ X₁loc b) → ∀ x ∈ intBox q,
        ∀ z : CTorus d L N₁ m₁ (k + 1), supDist x z ≤ 4 * L ^ (k + 1) → z ∈ S.G'.Ω 1)
    {J : Finset (coverOf S.G').cubeIdx}
    (hJ : ¬ IsConnectedFamily
      (fun P : (coverOf S.G').cubeIdx =>
        (cubeP (P : ℕ × CTorus d L N₁ m₁ (k + 1)) : Set (CTorus d L N₁ m₁ (k + 1))))
      (S.reachSet (coverOf S.G') X₁loc X₁ D Rd) J) (ψin : inner → Rn N) :
    S.oldCoef (coverOf S.G') (rho4 d L N BG κ) X₁loc X₁ inner ψout B J ψin = 0 :=
  coef_eq_zero_of_not_connected_on hR1
    (oldInterp_localityAEOn hS Sb SX HB hκ hM hδ0 hδε hε hδ hνε hD' hDD X₁loc X₁ inner ψout hB
      hR1.le hRk hstand hcov hlocdeep) (fun _ _ _ => rfl) (Set.mem_univ ψin) hJ

end HoleStep

end Balaban.Fluctuation
