/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.HoleStepMeasure
public import Balaban.Localization.AbstractExpansion

/-!
# The re-expansion of an old boundary term in the step on a region (P6 (4.32)–(4.34))

P6 p. 34: an old boundary term `ℬ^{(k)}(X)` of `ℬ''^{(k)}` (its domain meets `Ω_{k+1}`) is evaluated at
the composed field `ψ^{(k)}_loc(θ) + β_k^{-1/2} C^{(k)1/2}_loc ψ̂` of P5 (2.39); "at first we consider
this term as localized in `X ∩ Ω_{k+1}`, we introduce the same localization extension as before, and
we apply the proof of Proposition 4.3 [3]": the decoupling parameters `s_P` of the cover cubes `P` not
inside the uncut core `X₁` (`X₁` the sites of `X ∩ Ω_{k+1}`, P3 (4.41)) are introduced in the
localization vectors of every unit point, and the term at `s = 1` is the sum over the families `J`
of parameter cubes of the mixed-derivative coefficients of Lemma AE (P3 (4.41), (4.43), (4.47)).

For the step on a region (`HoleStep`), the cover `C`, the localization domains `X₁loc` of the unit
points (P5 (2.18)), the core `X₁` and an old term `B` (a function of the field on the unit points of
`Ω_{k+1}`):

* `coreExt`: the decoupling vector with the cubes inside the core set to `1`; `coreExt_one`;
* `oldInterp`: the interpolated old term `F_X(s) = B(ψ_k(s; ψ̂))`, the composed field at the
  localization vectors `slocOf C X₁loc (coreExt C X₁ s)`; `oldInterp_one`: at `s = 1` it is the old
  term at the composed field of the measure (`oldAt` at `slocOf C X₁loc 1`);
* `oldCoef`: **the coefficient `T(X, J)`**, the coefficient `coef` of Lemma AE of `F_X` at the
  family `J`;
* `sum_oldCoef_eq_of_analytic`: `B(ψ_k(ψ̂)) = ∑_J T(X, J)` when `F_X` is analytic on a polydisc of
  radius `> 1` (Lemma AE, `sum_coef_eq`);
* `oldCoef_eq_zero_of_core`: `T(X, J) = 0` when `J` contains a cube inside the core;
* `composed_congr_sloc`, `oldCoef_eq_zero_of_far`: the composed field at a unit point depends on the
  localization vectors only through the vector of that point, so if `B` reads only the unit points of
  `Rd`, then `T(X, J) = 0` when `J` contains a cube inside no localization domain `X₁loc b`, `b ∈ Rd`
  (the dependence on `s` is through the domains `R_{k+1}(□′)` of the read unit points only).
-/

@[expose] public section

namespace Balaban.Fluctuation

open MeasureTheory Balaban.Localization

namespace HoleStep

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱ' : ℝ}
  (S : HoleStep d L N₁ m₁ k N ϱ ϱ')

open Classical in
/-- **The decoupling vector with the core set to `1`** (P3 (4.41): only the cover cubes not inside
the uncut core `X₁` carry a parameter). -/
noncomputable def coreExt (C : DecCover d L N₁ m₁ (k + 1)) (X₁ : Finset (CTorus d L N₁ m₁ (k + 1)))
    (s : Dec2.DecParams C) : Dec2.DecParams C :=
  fun P => if cubeP (P : ℕ × CTorus d L N₁ m₁ (k + 1)) ⊆ X₁ then 1 else s P

theorem coreExt_one (C : DecCover d L N₁ m₁ (k + 1)) (X₁ : Finset (CTorus d L N₁ m₁ (k + 1))) :
    coreExt C X₁ 1 = 1 := by
  classical
  funext P
  simp only [coreExt, Pi.one_apply, ite_self]

open Classical in
theorem coreExt_of_subset (C : DecCover d L N₁ m₁ (k + 1)) (X₁ : Finset (CTorus d L N₁ m₁ (k + 1)))
    (s : Dec2.DecParams C) {P : C.cubeIdx} (hP : cubeP (P : ℕ × CTorus d L N₁ m₁ (k + 1)) ⊆ X₁) :
    coreExt C X₁ s P = 1 := by
  simp [coreExt, hP]

open Classical in
theorem coreExt_of_not_subset (C : DecCover d L N₁ m₁ (k + 1))
    (X₁ : Finset (CTorus d L N₁ m₁ (k + 1))) (s : Dec2.DecParams C) {P : C.cubeIdx}
    (hP : ¬ cubeP (P : ℕ × CTorus d L N₁ m₁ (k + 1)) ⊆ X₁) : coreExt C X₁ s P = s P := by
  simp [coreExt, hP]

/-- **The interpolated old term** `F_X(s)` of P6 (4.32): the old term `B` at the composed field of
P5 (2.39) with the localization vectors `slocOf C X₁loc (coreExt C X₁ s)` (the parameters `s` on the
cover cubes outside the core `X₁`, inside the localization domain of each unit point). -/
noncomputable def oldInterp (C : DecCover d L N₁ m₁ (k + 1)) (ρ : ℝ)
    (X₁loc : S.U → Finset (CTorus d L N₁ m₁ (k + 1))) (X₁ : Finset (CTorus d L N₁ m₁ (k + 1)))
    (inner : Finset S.U) (ψout : S.U → Fin N → ℂ) (B : (S.U → Fin N → ℂ) → ℂ)
    (ψin : inner → Rn N) (s : Dec2.DecParams C) : ℂ :=
  B (S.composed C ρ (S.slocOf C X₁loc (coreExt C X₁ s)) (S.fill inner ψin ψout))

/-- At `s = 1` the interpolated old term is the old term at the composed field of the measure. -/
theorem oldInterp_one (C : DecCover d L N₁ m₁ (k + 1)) (ρ : ℝ)
    (X₁loc : S.U → Finset (CTorus d L N₁ m₁ (k + 1))) (X₁ : Finset (CTorus d L N₁ m₁ (k + 1)))
    (inner : Finset S.U) (ψout : S.U → Fin N → ℂ) (B : (S.U → Fin N → ℂ) → ℂ)
    (ψin : inner → Rn N) :
    S.oldInterp C ρ X₁loc X₁ inner ψout B ψin 1 =
      S.oldAt C ρ (S.slocOf C X₁loc 1) inner ψout B ψin := by
  unfold oldInterp oldAt
  rw [coreExt_one]

/-- **The coefficient `T(X, J)` of the re-expansion of an old term** (P6 (4.32)–(4.33), P3 (4.43)):
the mixed-derivative coefficient of Lemma AE (`coef`) of the interpolated old term `F_X` at the
family `J` of cover cubes, as a function of the integration variables. -/
noncomputable def oldCoef (C : DecCover d L N₁ m₁ (k + 1)) (ρ : ℝ)
    (X₁loc : S.U → Finset (CTorus d L N₁ m₁ (k + 1))) (X₁ : Finset (CTorus d L N₁ m₁ (k + 1)))
    (inner : Finset S.U) (ψout : S.U → Fin N → ℂ) (B : (S.U → Fin N → ℂ) → ℂ)
    (J : Finset C.cubeIdx) (ψin : inner → Rn N) : ℂ :=
  coef (S.oldInterp C ρ X₁loc X₁ inner ψout B ψin) J

/-- **The old term is the sum of its coefficients** (Lemma AE, P3 (4.43)): if the interpolated old
term is analytic on the polydisc of radius `R > 1`, then
`B(ψ_k(ψ̂)) = ∑_J T(X, J)` at the composed field of the measure. -/
theorem sum_oldCoef_eq_of_analytic (C : DecCover d L N₁ m₁ (k + 1)) (ρ : ℝ)
    (X₁loc : S.U → Finset (CTorus d L N₁ m₁ (k + 1))) (X₁ : Finset (CTorus d L N₁ m₁ (k + 1)))
    (inner : Finset S.U) (ψout : S.U → Fin N → ℂ) (B : (S.U → Fin N → ℂ) → ℂ)
    (ψin : inner → Rn N) {R : ℝ} (hR : 1 < R)
    (hana : AnalyticOnNhd ℂ (S.oldInterp C ρ X₁loc X₁ inner ψout B ψin)
      (Analysis.polydisc (0 : Dec2.DecParams C) fun _ => R)) :
    S.oldAt C ρ (S.slocOf C X₁loc 1) inner ψout B ψin =
      ∑ J : Finset C.cubeIdx, S.oldCoef C ρ X₁loc X₁ inner ψout B J ψin := by
  rw [← S.oldInterp_one C ρ X₁loc X₁ inner ψout B ψin]
  exact sum_coef_eq hR hana

/-- **The cubes of the core carry no parameter**: `T(X, J) = 0` when `J` contains a cover cube inside
the core `X₁`. -/
theorem oldCoef_eq_zero_of_core (C : DecCover d L N₁ m₁ (k + 1)) (ρ : ℝ)
    (X₁loc : S.U → Finset (CTorus d L N₁ m₁ (k + 1))) (X₁ : Finset (CTorus d L N₁ m₁ (k + 1)))
    (inner : Finset S.U) (ψout : S.U → Fin N → ℂ) (B : (S.U → Fin N → ℂ) → ℂ)
    {J : Finset C.cubeIdx} {P : C.cubeIdx} (hPJ : P ∈ J)
    (hP : cubeP (P : ℕ × CTorus d L N₁ m₁ (k + 1)) ⊆ X₁) (ψin : inner → Rn N) :
    S.oldCoef C ρ X₁loc X₁ inner ψout B J ψin = 0 := by
  refine coef_eq_zero_of_inv hPJ fun w _ τ => ?_
  have hc : coreExt C X₁ (w + τ • (Pi.single P 1 : Dec2.DecParams C)) = coreExt C X₁ w := by
    funext Q
    by_cases hQ : Q = P
    · subst hQ
      rw [coreExt_of_subset C X₁ _ hP, coreExt_of_subset C X₁ _ hP]
    · classical
      simp only [coreExt, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_eq_of_ne hQ,
        mul_zero, add_zero]
  unfold oldInterp
  rw [hc]

/-- The composed field at a unit point depends on the localization vectors only through the vector
of that point. -/
theorem composed_congr_sloc (C : DecCover d L N₁ m₁ (k + 1)) (ρ : ℝ)
    {sloc sloc' : S.U → Dec2.DecParams C} (ψhat : S.U → Fin N → ℂ) {b : S.U}
    (hb : sloc b = sloc' b) : S.composed C ρ sloc ψhat b = S.composed C ρ sloc' ψhat b := by
  funext i
  unfold composed psiLoc shiftLoc
  rw [hb]

/-- **The dependence on the parameters is through the localization domains of the read unit points**:
if the old term `B` reads only the unit points of `Rd`, then `T(X, J) = 0` when `J` contains a cover
cube that lies in no localization domain `X₁loc b` of a point `b ∈ Rd`. -/
theorem oldCoef_eq_zero_of_far (C : DecCover d L N₁ m₁ (k + 1)) (ρ : ℝ)
    (X₁loc : S.U → Finset (CTorus d L N₁ m₁ (k + 1))) (X₁ : Finset (CTorus d L N₁ m₁ (k + 1)))
    (inner : Finset S.U) (ψout : S.U → Fin N → ℂ) {B : (S.U → Fin N → ℂ) → ℂ}
    {Rd : Set S.U} (hB : ∀ c c' : S.U → Fin N → ℂ, (∀ b ∈ Rd, c b = c' b) → B c = B c')
    {J : Finset C.cubeIdx} {P : C.cubeIdx} (hPJ : P ∈ J)
    (hfar : ∀ b ∈ Rd, ¬ cubeP (P : ℕ × CTorus d L N₁ m₁ (k + 1)) ⊆ X₁loc b)
    (ψin : inner → Rn N) :
    S.oldCoef C ρ X₁loc X₁ inner ψout B J ψin = 0 := by
  refine coef_eq_zero_of_inv hPJ fun w _ τ => ?_
  unfold oldInterp
  refine hB _ _ fun b hb => S.composed_congr_sloc C ρ _ ?_
  funext Q
  by_cases hQ : Q = P
  · subst hQ
    rw [slocOf_of_not_subset C X₁loc _ b Q (hfar b hb),
      slocOf_of_not_subset C X₁loc _ b Q (hfar b hb)]
  · classical
    simp only [slocOf, coreExt, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_eq_of_ne hQ,
      mul_zero, add_zero]

end HoleStep

end Balaban.Fluctuation
