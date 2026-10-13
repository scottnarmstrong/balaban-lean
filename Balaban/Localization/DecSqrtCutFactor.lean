/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.YregBlocks
import Mathlib.Tactic.Linarith

/-!
# The decoupled covariance square root at a cut configuration: block diagonality and locality

**One generating set (self-cover).** Everything here concerns the decoupled covariance
`decCov` and its square root `decCovSqrt = π⁻¹ ∫₀^∞ x^{-1/2} C_x dx` built from a single generating
set `G`, with the cover and the operator both taken from `G`. The mixed statement needed for the
boundary term of the sixth step (cover of one generating set, operator of another) is not proved
here.

* `decCov_BD`: for every `x ≥ 0`, the whole decoupled covariance `C_x(s)` is block diagonal for
  the labels of a union `Y'` of nearest-neighbour components of `Yreg s` (the correction
  `C_x - A_x` is block diagonal by `decCov_sub_BD`, the baseline `A_x` by `BD.liftOp`, `BD.one`).
* `CovStanding.decCovSqrt_BD_of_respects`, `CovStanding.decCovSqrt_BD_unit`: the square root is
  block diagonal. The integrand `x^{-1/2} C_x` has vanishing off-block entries for every `x > 0`,
  so the entrywise integral does (`intMat_BD`; no integrability is used). The unit-lattice form has
  no `UnionOfBlocks` hypothesis.
* `CovStanding.decCovSqrt_agree`, `CovStanding.decCovSqrt_agree_unit`: for two cut configurations
  and two data that agree on `Y'` (cut factors of the cubes inside `Y'`, potentials and fields on
  `Y'`), the matrix elements of `decCovSqrt` between labelled sites are equal.
* `CovStanding.decCovSqrt_mulVec_eq`: the fluctuation field `(C^{1/2} ψ̂) b` at a labelled site
  `b` depends only on the components of `ψ̂` at labelled sites and on the data on `Y'`.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Finset Matrix Set MeasureTheory Real

section Sqrt

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} {a : ℕ → ℝ} {aT ν κ κ' δ δ' : ℝ}
  {α α' : G.Ω 1 → ℂ} {s s' : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ}
  {φ φ' : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ}
  {κι : Type*} [Fintype κι] [DecidableEq κι]
  {Q : Matrix κι (G.Ω 1) ℂ} {P : Matrix κι κι ℂ}

omit [NeZero N₁] [NeZero L] [Fintype κι] in
/-- The baseline `A_x` of the decoupled covariance is block diagonal when `P` is. -/
theorem covA_BD (cκ : κι → Prop) (hP : BD cκ cκ P) (r r' x : ℝ) :
    BD (fun p : κι × Fin N => cκ p.1) (fun p : κι × Fin N => cκ p.1)
      (covA r r' x (liftOp N P)) := by
  have hPl : BD (fun p : κι × Fin N => cκ p.1) (fun p : κι × Fin N => cκ p.1) (liftOp N P) :=
    BD.liftOp hP
  unfold covA
  exact ((BD.one _).sub hPl).smul _ |>.add (hPl.smul _)

/-- **The whole decoupled covariance is block diagonal** (under the two provisos of
`CovStanding.decCov_sub_BD`). -/
theorem CovStanding.decCov_BD_of_respects {x : ℝ}
    (H : CovStanding G a aT ν α κ s δ φ Q P) (hx : 0 ≤ x) (hconn : HatConn G)
    {Y' : Finset (CTorus d L N₁ m₁ (k + 1))} (hY : IsNnComp (Yreg G s) Y')
    (hH : HRespects G a aT x ν α s Y') (cκ : κι → Prop)
    (hQ : BD cκ (fun y : G.Ω 1 => (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y') Q) (hP : BD cκ cκ P) :
    BD (fun p : κι × Fin N => cκ p.1) (fun p : κι × Fin N => cκ p.1)
      (decCov G a aT x ν α s φ Q P) := by
  have h := (H.decCov_sub_BD hx hconn hY hH cκ hQ hP).add (covA_BD (N := N) cκ hP (a k) (aT / (L : ℝ) ^ 2) x)
  rwa [sub_add_cancel] at h

/-- **The square root `C^{1/2}(s)` is block diagonal** for a union `Y'` of nearest-neighbour
components of `Yreg s`, under the two provisos (`HRespects` for every `x > 0`; labels of `Q`, `P`). -/
theorem CovStanding.decCovSqrt_BD_of_respects
    (H : CovStanding G a aT ν α κ s δ φ Q P) (hconn : HatConn G)
    {Y' : Finset (CTorus d L N₁ m₁ (k + 1))} (hY : IsNnComp (Yreg G s) Y')
    (hH : ∀ x : ℝ, 0 < x → HRespects G a aT x ν α s Y') (cκ : κι → Prop)
    (hQ : BD cκ (fun y : G.Ω 1 => (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y') Q) (hP : BD cκ cκ P) :
    BD (fun p : κι × Fin N => cκ p.1) (fun p : κι × Fin N => cκ p.1)
      (decCovSqrt G a aT ν α s φ Q P) := by
  unfold decCovSqrt
  refine BD.smul _ (intMat_BD _ _ fun x hx => ?_)
  unfold decSqrtInt
  exact BD.smul _ (H.decCov_BD_of_respects hx.le hconn hY (hH x hx) cκ hQ hP)

/-- **T1. The square root of the decoupled covariance is block diagonal for the unit lattice**, for
every union `Y'` of nearest-neighbour components of `Yreg s`. Hypotheses: `CovStanding` for
`unitQ`, `unitP` (all `x ≥ 0`) and `HatConn`; labels `unitLabel G Y'`. -/
theorem CovStanding.decCovSqrt_BD_unit
    (H : CovStanding G a aT ν α κ s δ φ (unitQ G) (unitP G)) (hconn : HatConn G)
    {Y' : Finset (CTorus d L N₁ m₁ (k + 1))} (hY : IsNnComp (Yreg G s) Y') :
    BD (fun p : unitPts G × Fin N => unitLabel G Y' p.1)
      (fun p : unitPts G × Fin N => unitLabel G Y' p.1)
      (decCovSqrt G a aT ν α s φ (unitQ G) (unitP G)) :=
  H.decCovSqrt_BD_of_respects hconn hY
    (fun x hx => hRespects_of_hatConn (H.fam x hx.le).st hconn hY) (unitLabel G Y')
    (unitQ_label_top (unionOfTopBlocks_of_isNnComp (H.fam 0 le_rfl).st.dg hconn hY))
    (unitP_label_top (unionOfTopBlocks_of_isNnComp (H.fam 0 le_rfl).st.dg hconn hY))

/-- Locality of the whole covariance `C_x`: the baseline does not depend on the data. -/
theorem CovStanding.decCov_agree {x : ℝ}
    (H : CovStanding G a aT ν α κ s δ φ Q P) (H' : CovStanding G a aT ν α' κ' s' δ' φ' Q P)
    (hx : 0 ≤ x) (hconn : HatConn G)
    {Y' : Finset (CTorus d L N₁ m₁ (k + 1))} (hY : IsNnComp (Yreg G s) Y')
    (hY' : IsNnComp (Yreg G s') Y')
    (hs : ∀ q ∈ cubeIdx G, SubI G (intBox q) Y' → sProd G s q = sProd G s' q)
    (hA : ∀ y : G.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y' → α y = α' y)
    (hφ : ∀ y : CTorus d L N₁ m₁ (k + 1), y ∈ Y' → φ y = φ' y) (cκ : κι → Prop)
    (hQ : BD cκ (fun y : G.Ω 1 => (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y') Q) (hP : BD cκ cκ P) :
    BAgree (fun p : κι × Fin N => cκ p.1) (fun p : κι × Fin N => cκ p.1)
      (decCov G a aT x ν α s φ Q P) (decCov G a aT x ν α' s' φ' Q P) := by
  intro i j hi hj
  have h := H.decCov_sub_agree H' hx hconn hY hY' hs hA hφ cκ hQ hP i j hi hj
  simp only [Matrix.sub_apply] at h
  linear_combination h

/-- **T2. Locality of the square root.** Two data that agree on a union `Y'` of components of both
`Yreg s` and `Yreg s'` (cut factors of the cubes inside `Y'`, potentials and fields on `Y'`) give
`decCovSqrt` the same matrix elements between labelled sites. The integrands agree for every
`x > 0`, so no integrability is used. -/
theorem CovStanding.decCovSqrt_agree
    (H : CovStanding G a aT ν α κ s δ φ Q P) (H' : CovStanding G a aT ν α' κ' s' δ' φ' Q P)
    (hconn : HatConn G)
    {Y' : Finset (CTorus d L N₁ m₁ (k + 1))} (hY : IsNnComp (Yreg G s) Y')
    (hY' : IsNnComp (Yreg G s') Y')
    (hs : ∀ q ∈ cubeIdx G, SubI G (intBox q) Y' → sProd G s q = sProd G s' q)
    (hA : ∀ y : G.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y' → α y = α' y)
    (hφ : ∀ y : CTorus d L N₁ m₁ (k + 1), y ∈ Y' → φ y = φ' y) (cκ : κι → Prop)
    (hQ : BD cκ (fun y : G.Ω 1 => (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y') Q) (hP : BD cκ cκ P) :
    BAgree (fun p : κι × Fin N => cκ p.1) (fun p : κι × Fin N => cκ p.1)
      (decCovSqrt G a aT ν α s φ Q P) (decCovSqrt G a aT ν α' s' φ' Q P) := by
  intro p q hp hq
  have e : ∀ x : ℝ, 0 < x → decSqrtInt G a aT ν α s φ Q P x p q =
      decSqrtInt G a aT ν α' s' φ' Q P x p q := fun x hx => by
    unfold decSqrtInt
    rw [Matrix.smul_apply, Matrix.smul_apply,
      H.decCov_agree H' hx.le hconn hY hY' hs hA hφ cκ hQ hP p q hp hq]
  have hint : intMat (volume.restrict (Ioi (0 : ℝ))) (decSqrtInt G a aT ν α s φ Q P) p q =
      intMat (volume.restrict (Ioi (0 : ℝ))) (decSqrtInt G a aT ν α' s' φ' Q P) p q := by
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact e x hx
  unfold decCovSqrt
  rw [Matrix.smul_apply, Matrix.smul_apply, hint]

/-- **T2, unit lattice.** The labels are `unitLabel G Y'`; no `UnionOfBlocks` hypothesis. -/
theorem CovStanding.decCovSqrt_agree_unit
    (H : CovStanding G a aT ν α κ s δ φ (unitQ G) (unitP G))
    (H' : CovStanding G a aT ν α' κ' s' δ' φ' (unitQ G) (unitP G)) (hconn : HatConn G)
    {Y' : Finset (CTorus d L N₁ m₁ (k + 1))} (hY : IsNnComp (Yreg G s) Y')
    (hY' : IsNnComp (Yreg G s') Y')
    (hs : ∀ q ∈ cubeIdx G, SubI G (intBox q) Y' → sProd G s q = sProd G s' q)
    (hA : ∀ y : G.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y' → α y = α' y)
    (hφ : ∀ y : CTorus d L N₁ m₁ (k + 1), y ∈ Y' → φ y = φ' y) :
    BAgree (fun p : unitPts G × Fin N => unitLabel G Y' p.1)
      (fun p : unitPts G × Fin N => unitLabel G Y' p.1)
      (decCovSqrt G a aT ν α s φ (unitQ G) (unitP G))
      (decCovSqrt G a aT ν α' s' φ' (unitQ G) (unitP G)) :=
  H.decCovSqrt_agree H' hconn hY hY' hs hA hφ (unitLabel G Y')
    (unitQ_label_top (unionOfTopBlocks_of_isNnComp (H.fam 0 le_rfl).st.dg hconn hY))
    (unitP_label_top (unionOfTopBlocks_of_isNnComp (H.fam 0 le_rfl).st.dg hconn hY))

/-- **T3. The fluctuation field `C^{1/2} ψ̂` at a labelled site.** If `ψ̂`, `ψ̂'` agree at the
labelled sites and the data agree on `Y'`, the values of `C^{1/2} ψ̂` and `C'^{1/2} ψ̂'` agree at
every labelled site (general labels, under the two provisos). -/
theorem CovStanding.decCovSqrt_mulVec_eq
    (H : CovStanding G a aT ν α κ s δ φ Q P) (H' : CovStanding G a aT ν α' κ' s' δ' φ' Q P)
    (hconn : HatConn G)
    {Y' : Finset (CTorus d L N₁ m₁ (k + 1))} (hY : IsNnComp (Yreg G s) Y')
    (hY' : IsNnComp (Yreg G s') Y')
    (hs : ∀ q ∈ cubeIdx G, SubI G (intBox q) Y' → sProd G s q = sProd G s' q)
    (hA : ∀ y : G.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y' → α y = α' y)
    (hφ : ∀ y : CTorus d L N₁ m₁ (k + 1), y ∈ Y' → φ y = φ' y) (cκ : κι → Prop)
    (hQ : BD cκ (fun y : G.Ω 1 => (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y') Q) (hP : BD cκ cκ P)
    (hH : ∀ x : ℝ, 0 < x → HRespects G a aT x ν α s Y')
    (ψ ψ' : κι × Fin N → ℂ) (hψ : ∀ j, cκ j.1 → ψ j = ψ' j)
    (b : κι × Fin N) (hb : cκ b.1) :
    (decCovSqrt G a aT ν α s φ Q P *ᵥ ψ) b = (decCovSqrt G a aT ν α' s' φ' Q P *ᵥ ψ') b := by
  have hBD := H.decCovSqrt_BD_of_respects hconn hY hH cκ hQ hP
  have hAg := H.decCovSqrt_agree H' hconn hY hY' hs hA hφ cκ hQ hP
  simp only [Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hj : cκ j.1
  · rw [hAg b j hb hj, hψ j hj]
  · have : decCovSqrt G a aT ν α s φ Q P b j = 0 := by
      by_contra h
      exact hj ((hBD b j h).1 hb)
    have h2 : decCovSqrt G a aT ν α' s' φ' Q P b j = 0 := by
      by_contra h
      exact hj ((H'.decCovSqrt_BD_of_respects hconn hY'
        (fun x hx => hRespects_of_hatConn (H'.fam x hx.le).st hconn hY') cκ hQ hP b j h).1 hb)
    rw [this, h2, zero_mul, zero_mul]

/-- **T3, unit lattice.** For `b` a unit point whose block lies in `Y'`. -/
theorem CovStanding.decCovSqrt_mulVec_eq_unit
    (H : CovStanding G a aT ν α κ s δ φ (unitQ G) (unitP G))
    (H' : CovStanding G a aT ν α' κ' s' δ' φ' (unitQ G) (unitP G)) (hconn : HatConn G)
    {Y' : Finset (CTorus d L N₁ m₁ (k + 1))} (hY : IsNnComp (Yreg G s) Y')
    (hY' : IsNnComp (Yreg G s') Y')
    (hs : ∀ q ∈ cubeIdx G, SubI G (intBox q) Y' → sProd G s q = sProd G s' q)
    (hA : ∀ y : G.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y' → α y = α' y)
    (hφ : ∀ y : CTorus d L N₁ m₁ (k + 1), y ∈ Y' → φ y = φ' y)
    (ψ ψ' : unitPts G × Fin N → ℂ) (hψ : ∀ j, unitLabel G Y' j.1 → ψ j = ψ' j)
    (b : unitPts G × Fin N) (hb : unitLabel G Y' b.1) :
    (decCovSqrt G a aT ν α s φ (unitQ G) (unitP G) *ᵥ ψ) b =
      (decCovSqrt G a aT ν α' s' φ' (unitQ G) (unitP G) *ᵥ ψ') b :=
  H.decCovSqrt_mulVec_eq H' hconn hY hY' hs hA hφ (unitLabel G Y')
    (unitQ_label_top (unionOfTopBlocks_of_isNnComp (H.fam 0 le_rfl).st.dg hconn hY))
    (unitP_label_top (unionOfTopBlocks_of_isNnComp (H.fam 0 le_rfl).st.dg hconn hY))
    (fun x hx => hRespects_of_hatConn (H.fam x hx.le).st hconn hY) ψ ψ' hψ b hb

end Sqrt

end Balaban.Localization
