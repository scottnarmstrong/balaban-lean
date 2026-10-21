/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.FinalBoxLocCore
import Mathlib.Tactic.Linarith

/-!
# The rooted Lemma AE for a function of the parameters that forgets the unrooted cells

`rootedExpansion_of_cutTo`: let `f` be analytic on the polydisc of radius `e^κ` (`κ ≥ 1`), with
`‖f s - f 0‖ ≤ b` there, such that at the parameters vanishing off `C`, `f s = f (cutTo A s)` for
`A` the rooted component of `C` at a root set `S`.  Then `f 1 = f 0 + ∑_{C ≠ ∅ rooted} coef_C f`, the
coefficients of the non-rooted families vanish, and `‖coef_C f‖ ≤ b e^{-(κ-1)|C|}`.  This is the proof
of `Green.rootedExpansion_linField` for an arbitrary `f` (there `f s = τ (Φ(s, w))`).
-/

@[expose] public section

namespace Balaban.LargeField.Base

open Finset Balaban.Localization Balaban.Analysis Balaban.Green

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι]

open Classical in
theorem rootedExpansion_of_cutTo {κ : ℝ} (hκ : 1 ≤ κ) {P : ι → Set Ω} {S : Set Ω}
    {f : (ι → ℂ) → ℂ} (hfan : AnalyticOnNhd ℂ f (polydisc (0 : ι → ℂ) (fun _ => Real.exp κ)))
    (hcut : ∀ (C : Finset ι) (s : ι → ℂ), s ∈ polydisc (0 : ι → ℂ) (fun _ => Real.exp κ) →
      s ∈ supportedOn C → f s = f (cutTo (rootComp P S C) s))
    {b : ℝ} (hb : ∀ s ∈ polydisc (0 : ι → ℂ) (fun _ => Real.exp κ), ‖f s - f 0‖ ≤ b) :
    f 1 = f 0 + ∑ C ∈ Finset.univ.filter (fun C : Finset ι => C.Nonempty ∧ IsRootedFamily P S C),
          coef f C ∧
      (∀ C, ¬ IsRootedFamily P S C → coef f C = 0) ∧
      (∀ C, C.Nonempty → ‖coef f C‖ ≤ b * Real.exp (-(κ - 1) * C.card)) := by
  have hR : 1 < Real.exp κ := Real.one_lt_exp_iff.2 (by linarith)
  have hzero : ∀ C, ¬ IsRootedFamily P S C → coef f C = 0 := fun C hC =>
    coef_eq_zero_of_not_rooted hR (fun s hs hsC => hcut C s hs hsC) hC
  have hbd : ∀ C, C.Nonempty → ‖coef f C‖ ≤ b * Real.exp (-(κ - 1) * C.card) := by
    intro C hC
    have hg : AnalyticOnNhd ℂ (fun s => f s - f 0)
        (polydisc (0 : ι → ℂ) (fun _ => Real.exp κ)) := fun s hs =>
      (hfan s hs).sub analyticAt_const
    have h1 : coef f C = coef (fun s => f s - f 0) C := (coef_sub_const hC f (f 0)).symm
    rw [h1]
    exact norm_coef_le_exp hκ hg hb C
  refine ⟨?_, hzero, hbd⟩
  have hsum := sum_coef_eq hR hfan
  rw [hsum, ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun C : Finset ι => C.Nonempty)]
  have hnot : (Finset.univ.filter fun C : Finset ι => ¬ C.Nonempty) = {∅} := by
    ext C; simp [Finset.not_nonempty_iff_eq_empty]
  rw [hnot, Finset.sum_singleton, add_comm]
  congr 1
  · exact coef_empty f
  · rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ.filter fun C : Finset ι => C.Nonempty)
      (fun C => IsRootedFamily P S C)]
    rw [Finset.filter_filter]
    have h0 : ∑ C ∈ (Finset.univ.filter fun C : Finset ι => C.Nonempty).filter
        (fun C => ¬ IsRootedFamily P S C), coef f C = 0 :=
      Finset.sum_eq_zero fun C hC => hzero C (Finset.mem_filter.1 hC).2
    rw [h0, add_zero]

end Balaban.LargeField.Base
