/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.ActionConvPieces

/-!
# The single-piece restriction of a window family (blocker 4)

`PieceWindowSetup.single W i`: the family of the one piece `i` (window region `X_i`).  Every per-piece
estimate of the window chain, applied to `W.single i`, is the estimate for the piece `i` with constants
that may depend on `i`; this is how the per-piece constants of `window_conversion_piecesP` are obtained.
-/

@[expose] public section

namespace Balaban.LargeField.ActionConv

open Balaban.Multiscale Balaban.Background

variable {d L N₀ K N : ℕ} [NeZero N₀] [NeZero L] {U : Type*} {S : Set U} {ι : Type*} [Fintype ι]
  {sc : ι → ℕ} {k1 k : ℕ}

/-- **The window family of one piece.** -/
@[reducible] def PieceWindowSetup.single (W : PieceWindowSetup d L N₀ K N S ι sc k1 k) (i : ι) :
    PieceWindowSetup d L N₀ K N S PUnit.{1} (fun _ => sc i) k1 k where
  sc_mem := fun _ => W.sc_mem i
  ϱw := W.ϱw
  Gw := W.Gw
  Xw := fun _ => W.Xw i
  Xwin := W.Xw i
  Xwin_sites := by simp
  Xw_disj := by
    intro a _ b _ hab
    exact absurd (Subsingleton.elim a b) hab
  ak := W.ak
  νk := W.νk
  βk := W.βk
  Datw := W.Datw
  φw := W.φw
  N₀c := fun _ => W.N₀c i
  Kc := fun _ => W.Kc i
  ϱc := fun _ => W.ϱc i
  Gc := fun _ => W.Gc i
  Xc := fun _ => W.Xc i
  br := fun _ => W.br i
  chain := fun _ => W.chain i
  decomp := fun _ => W.decomp i
  mcount := fun _ => W.mcount i
  mcount_eq := fun _ => W.mcount_eq i

end Balaban.LargeField.ActionConv
