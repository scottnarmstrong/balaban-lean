/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Operators.KerBound

/-!
# The bound (1.26) on a set of external fields

`KerBoundOn a k T κ Hs` is the bound (1.26) of `KerBound` for the external fields `h` with `Hs h`
only.  `KerBound` is the case `Hs = True` (`kerBound_iff_on`); `KerBoundAt` is the case `Hs = {h}`,
which is all that the removed gas bound (`lf4R_removed`) reads, and `KerBoundUnit` the case of unit
external fields (the physical field of Root-F is a unit vector, `Def7.FieldClauses.h_unit`).  The
window estimates need `‖h‖ = 1` (`pt_Du`), and the kernel support does not force it.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open MeasureTheory Balaban RegionHistory

section KerBoundOn

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ}

/-- **The bound (1.26) on the external fields satisfying `Hs`.** -/
def KerBoundOn (a : LocalHistory S n M K) (k : ℕ) {A : Set (InternalVars a k)}
    (T : LFKernel (OutT N R a k) (SubCfg N a k A) (EuclideanSpace ℝ (Fin N)) (GIdx S n M K N))
    (κ : ℝ) (Hs : EuclideanSpace ℝ (Fin N) → Prop) : Prop :=
  ∀ (hv : EuclideanSpace ℝ (Fin N)), Hs hv → ∀ (g : GIdx S n M K N → ℂ),
    g ∈ l1Ball (GIdx S n M K N) → ∀ par : OutPar N R a k,
      ∫⁻ oz, ∫⁻ x, T.absW (mergeOut a k oz par) x hv g ∂(subMeasure N a k A)
        ∂(outPartMeasure N (Vblk R a k) (ZBlk a k)) ≤ ENNReal.ofReal (Real.exp (-κ))

/-- The bound (1.26) at one external field. -/
abbrev KerBoundAt (a : LocalHistory S n M K) (k : ℕ) {A : Set (InternalVars a k)}
    (T : LFKernel (OutT N R a k) (SubCfg N a k A) (EuclideanSpace ℝ (Fin N)) (GIdx S n M K N))
    (hv : EuclideanSpace ℝ (Fin N)) (κ : ℝ) : Prop :=
  KerBoundOn a k T κ (fun h => h = hv)

/-- The bound (1.26) for the unit external fields. -/
abbrev KerBoundUnit (a : LocalHistory S n M K) (k : ℕ) {A : Set (InternalVars a k)}
    (T : LFKernel (OutT N R a k) (SubCfg N a k A) (EuclideanSpace ℝ (Fin N)) (GIdx S n M K N))
    (κ : ℝ) : Prop :=
  KerBoundOn a k T κ (fun h => ‖h‖ = 1)

variable {a : LocalHistory S n M K} {k : ℕ} {A : Set (InternalVars a k)}
  {T : LFKernel (OutT N R a k) (SubCfg N a k A) (EuclideanSpace ℝ (Fin N)) (GIdx S n M K N)}
  {κ κ' : ℝ} {Hs Hs' : EuclideanSpace ℝ (Fin N) → Prop}

theorem kerBound_iff_on : KerBound a k T κ ↔ KerBoundOn a k T κ (fun _ => True) :=
  ⟨fun h hv _ g hg par => h hv g hg par, fun h hv g hg par => h hv trivial g hg par⟩

theorem KerBound.toOn (h : KerBound a k T κ) (Hs : EuclideanSpace ℝ (Fin N) → Prop) :
    KerBoundOn a k T κ Hs := fun hv _ g hg par => h hv g hg par

theorem KerBound.toUnit (h : KerBound a k T κ) : KerBoundUnit a k T κ := h.toOn _

theorem KerBound.toAt (h : KerBound a k T κ) (hv : EuclideanSpace ℝ (Fin N)) :
    KerBoundAt a k T hv κ := h.toOn _

theorem KerBoundOn.mono (h : KerBoundOn a k T κ' Hs) (hκ : κ ≤ κ') : KerBoundOn a k T κ Hs := by
  intro hv hh g hg par
  refine (h hv hh g hg par).trans (ENNReal.ofReal_le_ofReal ?_)
  exact Real.exp_le_exp.2 (by linarith)

theorem KerBoundOn.mono_pred (h : KerBoundOn a k T κ Hs) (hs : ∀ hv, Hs' hv → Hs hv) :
    KerBoundOn a k T κ Hs' := fun hv hh g hg par => h hv (hs hv hh) g hg par

theorem KerBoundUnit.toAt (h : KerBoundUnit a k T κ) {hv : EuclideanSpace ℝ (Fin N)}
    (hu : ‖hv‖ = 1) : KerBoundAt a k T hv κ :=
  h.mono_pred fun _ hh => by rw [hh]; exact hu

end KerBoundOn

end Balaban.LargeField
