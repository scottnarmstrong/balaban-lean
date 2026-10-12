/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Operators.DomainIdentity
public import Balaban.LargeField.History.StepCover
public import Balaban.LargeField.R.StepGlue
public import Balaban.LargeField.R.WindowGenGlue

/-!
# Inhabitation of step and variable-set data

* `ancCover_exists`: for every region history, every step and every component `Z'` there are
  variable sets `AY` (all internal variables of each old part) and `A'` (the new variables and
  the images of all old ones) with `AncCover` (non-degenerate: `AY` is everything);
* `oldCover_exists`: for every step `st` and every `ω_k`, `cb ≥ 1` there are a good-component
  predicate (all components), single-cube boxes and counts with `OldCover`;
* `preStep_nonempty`, `gluePieces_nonempty`: these structures are data (no hypotheses); the
  empty step and the empty family with an arbitrary generating set are members.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.LargeField

section Anc

variable {S : Setting} [NeZero S.L] {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ} {M : ℕ} [NeZero M]
  {H : RegionHistory S n R k0 K} {k : ℕ}

/-- **`AncCover` is inhabited** for every history, step and component. -/
theorem ancCover_exists (hK : k + 1 ≤ K) (Z' : H.Comp (k + 1)) :
    ∃ (AY : ∀ Y : H.Comp k, Y ∈ H.parts k Z' → Set (InternalVars (H.localHistory M K k Y) k))
      (A' : Set (InternalVars (H.localHistory M K (k + 1) Z') (k + 1))),
      AncCover hK Z' AY A' := by
  refine ⟨fun _ _ => Set.univ,
    newVars (H.localHistory M K (k + 1) Z') k ∪
      {p | ∃ (Y : H.Comp k) (hY : Y ∈ H.parts k Z') (q : InternalVars (H.localHistory M K k Y) k),
        ancInc hK hY q = p}, ?_, ?_, ?_⟩
  · exact Set.subset_union_left
  · intro Y hY q _
    exact Or.inr ⟨Y, hY, q, rfl⟩
  · intro p hp hnn
    rcases hp with h | ⟨Y, hY, q, hq⟩
    · exact absurd h hnn
    · exact ⟨Y, hY, q, Set.mem_univ _, hq⟩

end Anc

section Old

variable {d L n0 n1 : ℕ} [NeZero n0] [NeZero n1] {Rprev Rk : ℝ}
  (st : RegionStep d L n0 n1 Rprev Rk)

omit [NeZero n1] in
/-- **`OldCover` is inhabited** for every step: every component is good and covered by its
single-site boxes of side `1`. -/
theorem oldCover_exists (ωk : ℕ) :
    ∃ (G : Finset (Torus d n0) → Prop) (ν : Finset (Torus d n0) → ℕ)
      (bx : Finset (Torus d n0) → Finset (Torus d n0 × (Fin d → ℕ))),
      st.OldCover G ωk 1 ν bx := by
  classical
  refine ⟨fun _ => True, fun Y => Y.card, fun Y => Y.image fun y => (y, fun _ => 1), ?_, ?_, ?_, ?_⟩
  · intro Y _ _; exact Finset.card_image_le
  · intro Y _ _ b hb i
    obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hb
    exact le_rfl
  · intro Y _ _ y hy
    refine Set.mem_iUnion₂.mpr ⟨(y, fun _ => 1), Finset.mem_image.mpr ⟨y, hy, rfl⟩, ?_⟩
    exact fun i => ⟨0, by norm_num, by simp⟩
  · intro Y hY _
    obtain ⟨x, hx⟩ := comp_nonempty hY
    exact Finset.card_pos.mpr ⟨x, hx⟩

end Old

/-- **`PreStep` is inhabited** (it is data without hypotheses): the empty step. -/
theorem preStep_nonempty (d L n0 n1 : ℕ) (Rprev Rk : ℝ) : Nonempty (PreStep d L n0 n1 Rprev Rk) :=
  ⟨⟨∅, ∅, ∅, ∅, ∅⟩⟩

/-- **`GluePieces` is inhabited** (data without hypotheses): any generating set, empty regions. -/
theorem gluePieces_nonempty {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {ι : Type*}
    (G : Balaban.Multiscale.GeneratingSet d L N₀ k ϱ) :
    Nonempty (GluePieces d L N₀ k ϱ ι) :=
  ⟨⟨fun _ => G, fun _ => ∅⟩⟩

end Balaban.Inhabited
