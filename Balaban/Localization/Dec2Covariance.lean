/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.DecSqrtCutFactor
public import Balaban.Localization.Decoupled2FpX
public import Balaban.Localization.Decoupled2Self

/-!
# The decoupled covariance and its square root for a pair `(C, H)`

For a cover `C` and a separate operator generating set `H` (namespace `Dec2`), this file writes
down the constraint matrices `decM`, `decN`, `decPi`, the covariance `decCov`, the integrand
`decSqrtInt` and the square root `decCovSqrt`: the formulas of the one-generating-set chain
(`DecoupledCovariance.lean`, `DecoupledCovBound.lean`, `DecoupledSqrt.lean`) with the Green's
operator `Gsx G ...` replaced by `Dec2.Gsx C H ...`; the Dirichlet operator is that of `H`.

* `decM_self`, ..., `decCovSqrt_self`: at `C = coverOf G`, `H = G` they are the landed objects.
* `decCov_BD_of_GsxBD`, `decCovSqrt_BD_of_GsxBD`: block diagonality of the covariance and of its
  square root, from block diagonality of `Dec2.Gsx C H` (explicit hypothesis) and the condition
  `HRespects` that the operator of `H` does not connect the core of `C` across the blocks.
* `Gsx_BD`: block diagonality of `Dec2.Gsx C H` for a union of nearest-neighbour components of
  `Yreg C H s`, under `XFootLocal C H` and `HatConn C H`.

The physical statement `OPEN-P6-MIXED-COV-ROWS` of `notes/phase1/VMOD-34.md` (bounds, locality in
the data with two backgrounds, the `unitQ/unitP` splitting) is NOT proved here.
-/

@[expose] public section

namespace Balaban.Localization.Dec2

open Balaban Balaban.Multiscale Balaban.Background Finset Matrix

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}

section Defs

variable (C : DecCover d L N₁ m₁ (k + 1)) (H : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ)
  (a : ℕ → ℝ) (aT x ν : ℝ) (α : H.Ω 1 → ℂ) (s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ)
  (φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)

/-- `M_{x,s} = φ₀² - K_x(φ₀) G_{k,x,s} φ₀` for the pair `(C, H)`. -/
noncomputable def decM : Matrix (H.Ω 1) (H.Ω 1) ℂ :=
  constraintM (xDirichletOperator H a aT x ν α) (Gsx C H a aT x ν α s) (restrictField H φ)

/-- `N_{x,s} f = φ₀ f - K_x(φ₀) G_{k,x,s} f` for the pair `(C, H)`. -/
noncomputable def decN : Matrix (H.Ω 1) (H.Ω 1 × Fin N) ℂ :=
  constraintN (xDirichletOperator H a aT x ν α) (Gsx C H a aT x ν α s) (restrictField H φ)

/-- `Π_{x,s} = G_{k,x,s} φ₀ M_{x,s}⁻¹ N_{x,s}` for the pair `(C, H)`. -/
noncomputable def decPi : Matrix (H.Ω 1 × Fin N) (H.Ω 1 × Fin N) ℂ :=
  liftOp N (Gsx C H a aT x ν α s) * fieldMul (restrictField H φ) *
    (decM C H a aT x ν α s φ)⁻¹ * decN C H a aT x ν α s φ

variable {κι : Type*} [Fintype κι] [DecidableEq κι]

/-- The decoupled constrained covariance of the pair `(C, H)`. -/
noncomputable def decCov (Q : Matrix κι (H.Ω 1) ℂ) (P : Matrix κι κι ℂ) :
    Matrix (κι × Fin N) (κι × Fin N) ℂ :=
  covA (a k) (aT / (L : ℝ) ^ 2) x (liftOp N P) +
    (((a k) ^ 2 / (L : ℝ) ^ (2 * k) : ℝ) : ℂ) •
      (covA (a k) (aT / (L : ℝ) ^ 2) x (liftOp N P) * liftRect N Q *
        (liftOp N (Gsx C H a aT x ν α s) - decPi C H a aT x ν α s φ) * (liftRect N Q)ᵀ *
        covA (a k) (aT / (L : ℝ) ^ 2) x (liftOp N P))

end Defs

/-- The integrand `x^{-1/2} C_x(s)` of `C^{1/2}` for the pair `(C, H)`. -/
noncomputable def decSqrtInt (C : DecCover d L N₁ m₁ (k + 1))
    (H : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ) (a : ℕ → ℝ) (aT ν : ℝ) (α : H.Ω 1 → ℂ)
    (s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ) (φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)
    {κι : Type*} [Fintype κι] [DecidableEq κι]
    (Q : Matrix κι (H.Ω 1) ℂ) (P : Matrix κι κι ℂ) (x : ℝ) :
    Matrix (κι × Fin N) (κι × Fin N) ℂ :=
  ((x ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) • decCov C H a aT x ν α s φ Q P

/-- The square root `C^{1/2}(s) = π⁻¹ ∫₀^∞ x^{-1/2} C_x(s) dx` for the pair `(C, H)`. -/
noncomputable def decCovSqrt (C : DecCover d L N₁ m₁ (k + 1))
    (H : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ) (a : ℕ → ℝ) (aT ν : ℝ) (α : H.Ω 1 → ℂ)
    (s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ) (φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)
    {κι : Type*} [Fintype κι] [DecidableEq κι]
    (Q : Matrix κι (H.Ω 1) ℂ) (P : Matrix κι κι ℂ) :
    Matrix (κι × Fin N) (κι × Fin N) ℂ :=
  ((1 / Real.pi : ℝ) : ℂ) •
    intMat (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
      (decSqrtInt C H a aT ν α s φ Q P)

/-! ### Reduction to the single generating set -/

section Self

variable {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} (a : ℕ → ℝ) (aT x ν : ℝ)
  (α : G.Ω 1 → ℂ) (s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ)
  (φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)
  {κι : Type*} [Fintype κι] [DecidableEq κι]

theorem decM_self :
    decM (coverOf G) G a aT x ν α s φ = Balaban.Localization.decM G a aT x ν α s φ := rfl

theorem decN_self :
    decN (coverOf G) G a aT x ν α s φ = Balaban.Localization.decN G a aT x ν α s φ := rfl

theorem decPi_self :
    decPi (coverOf G) G a aT x ν α s φ = Balaban.Localization.decPi G a aT x ν α s φ := rfl

theorem decCov_self (Q : Matrix κι (G.Ω 1) ℂ) (P : Matrix κι κι ℂ) :
    decCov (coverOf G) G a aT x ν α s φ Q P =
      Balaban.Localization.decCov G a aT x ν α s φ Q P := rfl

theorem decSqrtInt_self (Q : Matrix κι (G.Ω 1) ℂ) (P : Matrix κι κι ℂ) :
    decSqrtInt (coverOf G) G a aT ν α s φ Q P x =
      Balaban.Localization.decSqrtInt G a aT ν α s φ Q P x := rfl

theorem decCovSqrt_self (Q : Matrix κι (G.Ω 1) ℂ) (P : Matrix κι κι ℂ) :
    decCovSqrt (coverOf G) G a aT ν α s φ Q P =
      Balaban.Localization.decCovSqrt G a aT ν α s φ Q P := rfl

end Self

/-! ### Geometric input: block diagonality of `Dec2.Gsx C H` -/

section GsxBD

variable {C : DecCover d L N₁ m₁ (k + 1)} {H : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
  {a : ℕ → ℝ} {aT x ν Cx : ℝ} {α : H.Ω 1 → ℂ} {s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ}

theorem Gsx_apply_eq_zero_of_not_core (S : FootLocalGeom C) (y y' : H.Ω 1)
    (hy : (y : CTorus d L N₁ m₁ (k + 1)) ∉ Core C s) : Gsx C H a aT x ν α s y y' = 0 := by
  by_contra h
  refine hy (dg5x_support_fp (a := a) (aT := aT) (x := x) (ν := ν) (α := α) S s
    (Pi.single y' (1 : ℂ)) y ?_)
  rw [Balaban.Localization.mulVec_single_apply]; exact h

theorem mem_Yreg_of_mem_core (y : H.Ω 1) (hy : (y : CTorus d L N₁ m₁ (k + 1)) ∈ Core C s) :
    (y : CTorus d L N₁ m₁ (k + 1)) ∈ Yreg C H s := by
  classical
  unfold Core at hy
  rw [Finset.mem_biUnion] at hy
  obtain ⟨z, hz, hyz⟩ := hy
  unfold Yreg
  rw [Finset.mem_filter, Finset.mem_biUnion]
  exact ⟨⟨z, hz, box_subset_hatBox z (coreBox_subset_box hyz)⟩, y.2⟩

theorem Gsx_apply_eq_zero_of_comp (S : XCover C H a aT ν Cx) (hx : 0 ≤ x)
    (hconn : HatConn C H) (hα : AdmPot H α) (hU : IsUnit (1 - Kcalx C H a aT x ν α s))
    {Y' : Finset (CTorus d L N₁ m₁ (k + 1))} (hY : IsNnComp (Yreg C H s) Y')
    {y y' : H.Ω 1} (hy : (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y')
    (hy' : (y' : CTorus d L N₁ m₁ (k + 1)) ∉ Y') : Gsx C H a aT x ν α s y y' = 0 := by
  have h := dg5x_local S hx hconn hα hα hU hU hY (fun _ _ => rfl)
    (f := Pi.single y' (1 : ℂ)) (f' := 0) (fun z hz => by
      have : z ≠ y' := fun h => hy' (h ▸ hz)
      simp [this]) y hy
  rw [Balaban.Localization.mulVec_single_apply] at h
  simpa using h

/-- **Block diagonality of `Dec2.Gsx C H`** for a union `Y'` of nearest-neighbour components of
`Yreg C H s`, for the pair `(C, H)` under `XFootLocal` and `HatConn C H`. -/
theorem Gsx_BD (S : XFootLocal C H a aT ν Cx) (hx : 0 ≤ x) (hconn : HatConn C H)
    (hα : AdmPot H α) (hU : IsUnit (1 - Kcalx C H a aT x ν α s))
    {Y' : Finset (CTorus d L N₁ m₁ (k + 1))} (hY : IsNnComp (Yreg C H s) Y') :
    BD (fun y : H.Ω 1 => (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y')
      (fun y : H.Ω 1 => (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y') (Gsx C H a aT x ν α s) := by
  classical
  intro y y' h
  have hcore : (y : CTorus d L N₁ m₁ (k + 1)) ∈ Core C s := by
    by_contra hc; exact h (Gsx_apply_eq_zero_of_not_core S.toFootLocalGeom y y' hc)
  have hyr := mem_Yreg_of_mem_core y hcore
  constructor
  · intro hy; by_contra hy'
    exact h (Gsx_apply_eq_zero_of_comp S.toXCover hx hconn hα hU hY hy hy')
  · intro hy'; by_contra hy
    have hY2 := Balaban.Localization.isNnComp_sdiff hY
    exact h (Gsx_apply_eq_zero_of_comp S.toXCover hx hconn hα hU hY2
      (Finset.mem_sdiff.2 ⟨hyr, hy⟩) (fun hh => (Finset.mem_sdiff.1 hh).2 hy'))

end GsxBD

/-! ### Algebraic block diagonality, conditional on `Gsx` -/

section Cov

variable {C : DecCover d L N₁ m₁ (k + 1)} {H : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
  {a : ℕ → ℝ} {aT x ν : ℝ} {α : H.Ω 1 → ℂ} {s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ}
  {φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ}
  {κι : Type*} [Fintype κι] [DecidableEq κι]

/-- The proviso for the operator of `H`: a non-zero matrix element of `H_{k,x}` from a site to a
site of the core of the cover `C` does not cross the boundary of `Y'`.  (The core is that of `C`,
`Dec2.Core C s`, not that of `H`.) -/
abbrev HRespects (C : DecCover d L N₁ m₁ (k + 1))
    (H : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ) (a : ℕ → ℝ) (aT x ν : ℝ)
    (α : H.Ω 1 → ℂ) (s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ)
    (Y' : Finset (CTorus d L N₁ m₁ (k + 1))) : Prop :=
  ∀ y y' : H.Ω 1, xDirichletOperator H a aT x ν α y y' ≠ 0 →
    (y' : CTorus d L N₁ m₁ (k + 1)) ∈ Core C s →
    ((y : CTorus d L N₁ m₁ (k + 1)) ∈ Y' ↔ (y' : CTorus d L N₁ m₁ (k + 1)) ∈ Y')

section Blocks

variable (S : FootLocalGeom C) {Y' : Finset (CTorus d L N₁ m₁ (k + 1))}
  (hG : BD (fun y : H.Ω 1 => (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y')
    (fun y : H.Ω 1 => (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y') (Gsx C H a aT x ν α s))
  (hH : HRespects C H a aT x ν α s Y')
include S hG hH

local notation "cY" => (fun y : H.Ω 1 => (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y')

theorem commK_Gsx_BD_of_GsxBD :
    BD cY (fun p : H.Ω 1 × Fin N => (p.1 : CTorus d L N₁ m₁ (k + 1)) ∈ Y')
      (commK (xDirichletOperator H a aT x ν α) (restrictField H φ) *
        liftOp N (Gsx C H a aT x ν α s)) := by
  intro y q h
  rw [Matrix.mul_apply] at h
  obtain ⟨p, -, hp⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  have h1 := left_ne_zero_of_mul hp
  have h2 := right_ne_zero_of_mul hp
  have hG' : Gsx C H a aT x ν α s p.1 q.1 ≠ 0 := by
    intro h0; apply h2; simp [liftOp, h0]
  have hHp : xDirichletOperator H a aT x ν α y p.1 ≠ 0 := by
    intro h0; apply h1
    rw [show p = (p.1, p.2) from rfl, Balaban.Localization.commK_apply, h0, zero_mul]
  have hcore : (p.1 : CTorus d L N₁ m₁ (k + 1)) ∈ Core C s := by
    by_contra hc; exact hG' (Gsx_apply_eq_zero_of_not_core S p.1 q.1 hc)
  exact (hH y p.1 hHp hcore).trans (hG p.1 q.1 hG')

theorem decM_BD_of_GsxBD :
    BD cY cY (decM C H a aT x ν α s φ) := by
  unfold decM constraintM
  exact ((fieldMul_BD cY _).transpose.mul (fieldMul_BD cY _)).sub
    ((commK_Gsx_BD_of_GsxBD S hG hH).mul (fieldMul_BD cY _))

theorem decN_BD_of_GsxBD :
    BD cY (fun p : H.Ω 1 × Fin N => (p.1 : CTorus d L N₁ m₁ (k + 1)) ∈ Y')
      (decN C H a aT x ν α s φ) := by
  unfold decN constraintN
  exact (fieldMul_BD cY _).transpose.sub (commK_Gsx_BD_of_GsxBD S hG hH)

theorem decPi_BD_of_GsxBD (hM : IsUnit (decM C H a aT x ν α s φ)) :
    BD (fun p : H.Ω 1 × Fin N => (p.1 : CTorus d L N₁ m₁ (k + 1)) ∈ Y')
      (fun p : H.Ω 1 × Fin N => (p.1 : CTorus d L N₁ m₁ (k + 1)) ∈ Y')
      (decPi C H a aT x ν α s φ) := by
  unfold decPi
  exact (((BD.liftOp hG).mul (fieldMul_BD cY _)).mul
    ((decM_BD_of_GsxBD S hG hH).inv hM)).mul (decN_BD_of_GsxBD S hG hH)

theorem decCov_sub_BD_of_GsxBD (hM : IsUnit (decM C H a aT x ν α s φ))
    (cκ : κι → Prop) (Q : Matrix κι (H.Ω 1) ℂ) (P : Matrix κι κι ℂ)
    (hQ : BD cκ cY Q) (hP : BD cκ cκ P) :
    BD (fun p : κι × Fin N => cκ p.1) (fun p : κι × Fin N => cκ p.1)
      (decCov C H a aT x ν α s φ Q P -
        covA (a k) (aT / (L : ℝ) ^ 2) x (liftOp N P)) := by
  have hA := covA_BD (N := N) cκ hP (a k) (aT / (L : ℝ) ^ 2) x
  have hQl : BD (fun p : κι × Fin N => cκ p.1)
      (fun p : H.Ω 1 × Fin N => (p.1 : CTorus d L N₁ m₁ (k + 1)) ∈ Y') (liftRect N Q) :=
    BD.liftOp hQ
  have hT := (BD.liftOp hG).sub (decPi_BD_of_GsxBD S hG hH hM)
  unfold decCov
  rw [add_sub_cancel_left]
  exact (((hA.mul hQl).mul hT).mul hQl.transpose |>.mul hA).smul _

theorem decCov_BD_of_GsxBD (hM : IsUnit (decM C H a aT x ν α s φ))
    (cκ : κι → Prop) (Q : Matrix κι (H.Ω 1) ℂ) (P : Matrix κι κι ℂ)
    (hQ : BD cκ cY Q) (hP : BD cκ cκ P) :
    BD (fun p : κι × Fin N => cκ p.1) (fun p : κι × Fin N => cκ p.1)
      (decCov C H a aT x ν α s φ Q P) := by
  have h := (decCov_sub_BD_of_GsxBD S hG hH hM cκ Q P hQ hP).add
    (covA_BD (N := N) cκ hP (a k) (aT / (L : ℝ) ^ 2) x)
  rwa [sub_add_cancel] at h

end Blocks

/-- **The square root of the pair covariance is block diagonal**, if for every `x > 0` the
hypotheses of `decCov_BD_of_GsxBD` hold.  No integrability is needed (`intMat_BD`). -/
theorem decCovSqrt_BD_of_GsxBD (S : FootLocalGeom C) {Y' : Finset (CTorus d L N₁ m₁ (k + 1))}
    (hG : ∀ x : ℝ, 0 < x →
      BD (fun y : H.Ω 1 => (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y')
        (fun y : H.Ω 1 => (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y') (Gsx C H a aT x ν α s))
    (hH : ∀ x : ℝ, 0 < x → HRespects C H a aT x ν α s Y')
    (hM : ∀ x : ℝ, 0 < x → IsUnit (decM C H a aT x ν α s φ))
    (cκ : κι → Prop) (Q : Matrix κι (H.Ω 1) ℂ) (P : Matrix κι κι ℂ)
    (hQ : BD cκ (fun y : H.Ω 1 => (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y') Q) (hP : BD cκ cκ P) :
    BD (fun p : κι × Fin N => cκ p.1) (fun p : κι × Fin N => cκ p.1)
      (decCovSqrt C H a aT ν α s φ Q P) := by
  unfold decCovSqrt
  refine BD.smul _ (intMat_BD _ _ fun x hx => ?_)
  unfold decSqrtInt
  exact BD.smul _ (decCov_BD_of_GsxBD S (hG x hx) (hH x hx) (hM x hx) cκ Q P hQ hP)

end Cov

/-! ### Non-vacuity at the self-cover -/

section SelfBD

variable {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} {a : ℕ → ℝ} {aT x ν : ℝ}
  {α : G.Ω 1 → ℂ} {s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ}
  {φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ}
  {κι : Type*} [Fintype κι] [DecidableEq κι]

/-- At the self-cover the hypotheses of `decCov_BD_of_GsxBD` hold under the landed hypotheses
(`Gsx_BD` of the single-cover chain, `HRespects` of the single-cover chain), so the pair
statement is not vacuous. -/
theorem decCov_BD_self (S : XSetting G a aT ν) (hx : 0 ≤ x) (hconn : Balaban.Localization.HatConn G)
    (hα : AdmPot G α) (hU : IsUnit (1 - Balaban.Localization.Kcalx G a aT x ν α s))
    {Y' : Finset (CTorus d L N₁ m₁ (k + 1))}
    (hY : IsNnComp (Balaban.Localization.Yreg G s) Y')
    (hH : Balaban.Localization.HRespects G a aT x ν α s Y')
    (hM : IsUnit (Balaban.Localization.decM G a aT x ν α s φ))
    (cκ : κι → Prop) (Q : Matrix κι (G.Ω 1) ℂ) (P : Matrix κι κι ℂ)
    (hQ : BD cκ (fun y : G.Ω 1 => (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y') Q) (hP : BD cκ cκ P) :
    BD (fun p : κι × Fin N => cκ p.1) (fun p : κι × Fin N => cκ p.1)
      (decCov (coverOf G) G a aT x ν α s φ Q P) :=
  decCov_BD_of_GsxBD (footLocalGeom_coverOf G)
    (Balaban.Localization.Gsx_BD S hx hconn hα hU hY) hH hM cκ Q P hQ hP

/-- Square-root version at the self-cover. -/
theorem decCovSqrt_BD_self {Y' : Finset (CTorus d L N₁ m₁ (k + 1))}
    (S : ∀ x : ℝ, 0 < x → XSetting G a aT ν) (hconn : Balaban.Localization.HatConn G)
    (hα : AdmPot G α)
    (hU : ∀ x : ℝ, 0 < x → IsUnit (1 - Balaban.Localization.Kcalx G a aT x ν α s))
    (hY : IsNnComp (Balaban.Localization.Yreg G s) Y')
    (hH : ∀ x : ℝ, 0 < x → Balaban.Localization.HRespects G a aT x ν α s Y')
    (hM : ∀ x : ℝ, 0 < x → IsUnit (Balaban.Localization.decM G a aT x ν α s φ))
    (cκ : κι → Prop) (Q : Matrix κι (G.Ω 1) ℂ) (P : Matrix κι κι ℂ)
    (hQ : BD cκ (fun y : G.Ω 1 => (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y') Q) (hP : BD cκ cκ P) :
    BD (fun p : κι × Fin N => cκ p.1) (fun p : κι × Fin N => cκ p.1)
      (decCovSqrt (coverOf G) G a aT ν α s φ Q P) :=
  decCovSqrt_BD_of_GsxBD (footLocalGeom_coverOf G)
    (fun x hx => Balaban.Localization.Gsx_BD (S x hx) hx.le hconn hα (hU x hx) hY) hH hM cκ Q P hQ hP

end SelfBD

end Balaban.Localization.Dec2
