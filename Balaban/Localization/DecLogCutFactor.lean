/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.DecCovCutSupport
public import Balaban.Localization.DecLogZero
import Mathlib.Tactic.Linarith

/-!
# Block diagonality of the decoupled logarithm

Continuation of `DecCovCutSupport.lean` (DET-CUT-FACTOR of `notes/phase1/ROOTDET.md` §2).

* `intMat_BD`: the entrywise integral over `x > 0` of a family of matrices that are block diagonal
  for every `x > 0` is block diagonal (no integrability is needed: a vanishing entry integrates to
  zero).
* `baseline_BD`: the baseline blocks `log a_k (1 - P) + log (a_k + aT/L²) P` of `decLog`.
* `decLog_BD_of_integrand`, `CovStanding.decLog_BD_of_respects`: `decLog` is block diagonal for the
  labels, under the two provisos of `DecCovCutSupport.lean` (named hypotheses).

The decay (forest) bound and the count of cut sets per cube set are not proved here.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Finset Matrix Set MeasureTheory Real

section Integral

variable {ι : Type*}

/-- The entrywise integral over `x > 0` of matrices that are block diagonal for every `x > 0` is
block diagonal. -/
theorem intMat_BD (c : ι → Prop) (F : ℝ → Matrix ι ι ℂ)
    (hF : ∀ x, 0 < x → BD c c (F x)) :
    BD c c (intMat (volume.restrict (Ioi (0 : ℝ))) F) := by
  intro i j h
  by_contra hc
  apply h
  show ∫ x, F x i j ∂(volume.restrict (Ioi (0 : ℝ))) = 0
  refine integral_eq_zero_of_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  by_contra hne
  exact hc (hF x hx i j hne)

end Integral

section Decoupled

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} {a : ℕ → ℝ} {aT ν κ δ : ℝ}
  {α : G.Ω 1 → ℂ} {s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ}
  {φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ}
  {κι : Type*} [Fintype κι] [DecidableEq κι]

omit [Fintype κι] in
/-- The baseline blocks of `decLog` are block diagonal when `P` is. -/
theorem baseline_BD (cκ : κι → Prop) (P : Matrix κι κι ℂ) (hP : BD cκ cκ P) (r r' : ℂ) :
    BD (fun p : κι × Fin N => cκ p.1) (fun p : κι × Fin N => cκ p.1)
      (r • (1 - liftOp N P) + r' • liftOp N P) :=
  ((BD.one _).sub (BD.liftOp hP)).smul r |>.add ((BD.liftOp hP).smul r')

/-- **`decLog` is block diagonal**, given block diagonality of the integrand `decCov - covA` for
all `x > 0` (that is the content of `decCov_sub_BD` under the provisos). -/
theorem decLog_BD_of_integrand (cκ : κι → Prop) (Q : Matrix κι (G.Ω 1) ℂ) (P : Matrix κι κι ℂ)
    (hP : BD cκ cκ P)
    (hint : ∀ x : ℝ, 0 < x →
      BD (fun p : κι × Fin N => cκ p.1) (fun p : κι × Fin N => cκ p.1)
        (decCov G a aT x ν α s φ Q P - covA (a k) (aT / (L : ℝ) ^ 2) x (liftOp N P))) :
    BD (fun p : κι × Fin N => cκ p.1) (fun p : κι × Fin N => cκ p.1)
      (decLog G a aT ν α s φ Q P) := by
  unfold decLog
  exact (baseline_BD cκ P hP _ _).sub (intMat_BD _ _ hint)

/-- **`decLog` is block diagonal for a union `Y'` of nearest-neighbour components of `Yreg s`**,
under the two named provisos: `HRespects` for every `x > 0` and the label compatibility of `Q`, `P`
(`hQ`, `hP`). The standing hypotheses are `CovStanding` and `HatConn`. -/
theorem CovStanding.decLog_BD_of_respects {Q : Matrix κι (G.Ω 1) ℂ} {P : Matrix κι κι ℂ}
    (H : CovStanding G a aT ν α κ s δ φ Q P) (hconn : HatConn G)
    {Y' : Finset (CTorus d L N₁ m₁ (k + 1))} (hY : IsNnComp (Yreg G s) Y')
    (hH : ∀ x : ℝ, 0 < x → HRespects G a aT x ν α s Y') (cκ : κι → Prop)
    (hQ : BD cκ (fun y : G.Ω 1 => (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y') Q) (hP : BD cκ cκ P) :
    BD (fun p : κι × Fin N => cκ p.1) (fun p : κι × Fin N => cκ p.1)
      (decLog G a aT ν α s φ Q P) :=
  decLog_BD_of_integrand cκ Q P hP fun x hx =>
    H.decCov_sub_BD hx.le hconn hY (hH x hx) cκ hQ hP

end Decoupled

end Balaban.Localization
