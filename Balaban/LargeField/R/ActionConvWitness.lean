/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.ActionConvWindow

/-!
# Inhabitation of the action-conversion input (hard rule 10)

For the window setup on the empty generating set (`Ω_j = ∅`, no cubes, one step `k₁ = 0`, `k = 1`),
`ActionConvInput` holds (the estimates are vacuous or `0 ≤ 0`):
`ActionConvInput.nonempty`.  The setup structures `WindowSetup`, `ConvChain`, `StepDecomp` are
inhabited by the same data.
-/

@[expose] public section

namespace Balaban.LargeField.ActionConv

open Balaban.Multiscale Balaban.Background Balaban.Fluctuation Finset

variable {d L N₀ K N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- The generating set with all `Ω_j` empty. -/
def GeneratingSet.emptySet : GeneratingSet d L N₀ K ϱ where
  Ω := fun _ => ∅
  top := rfl
  subset := fun _ _ _ => Finset.empty_subset _
  blockUnion := fun _ _ _ x x' _ => by simp
  separation := fun _ _ _ x _ y hy => by simp at hy

/-- The zero data on the empty generating set. -/
def zeroData : BgData (GeneratingSet.emptySet (d := d) (L := L) (N₀ := N₀) (K := K) (ϱ := ϱ)) N where
  Ψ := fun _ _ => 0
  h := fun _ _ => 0
  Ψ_layerConst := fun _ _ _ _ _ _ _ => rfl
  h_layerConst := fun _ _ _ _ _ _ _ => rfl
  Ψ_zero := fun _ _ => rfl
  h_zero := fun _ _ => rfl

theorem actionRegionC_bot {G : GeneratingSet d L N₀ K ϱ} (a : ℕ → ℝ) (ν : ℝ) (Dat : BgData G N)
    (φ : G.Ω 1 × Fin N → ℂ) : actionRegionC (Region.bot : Region G) a ν Dat φ = 0 :=
  (Region.actionRegionC_additive a ν Dat φ).bot

/-- The trivial step decomposition of the empty region. -/
def StepDecomp.empty {G : GeneratingSet d L N₀ K ϱ} : StepDecomp (Region.bot : Region G) where
  ι := Empty
  κ := Empty
  cube := fun i => i.elim
  wt := fun i => i.elim
  wt_nonneg := fun i => i.elim
  cube_disj := fun i => i.elim
  cube_union := by simp [Region.bot]
  wall := fun q => q.elim
  wall_disj := fun q => q.elim
  wall_union := by
    ext b
    simp [Region.crossing, Region.bot]
  wallCube := fun q => q.elim
  inc := 0
  inc_le := fun i => i.elim

variable {U : Type*} [NormedAddCommGroup U] [NormedSpace ℂ U]

/-- **Inhabitation of `ActionConvInput`**: for the trivial window (empty generating set), the
setup exists and the input holds. -/
theorem ActionConvInput.nonempty (S : Set U) :
    ∃ W : WindowSetup d L N₀ K N S 0 1,
      Nonempty (ActionConvInput W 0 1 0 0 0 0 0 0 (fun _ => 1) (fun _ => 0) (fun _ _ _ => 0)) := by
  let G : GeneratingSet d L N₀ K (0 : ℝ) := GeneratingSet.emptySet
  let W : WindowSetup d L N₀ K N S 0 1 :=
    { ϱw := 0
      Gw := G
      Xw := fun _ => Region.bot
      Xwin := Region.bot
      Xwin_sites := by simp [Region.bot]
      Xw_disj := fun _ _ _ _ _ => by simp [Region.bot]
      ak := fun _ => 0
      νk := 0
      βk := 1
      Datw := fun _ => zeroData
      φw := fun _ => 0
      ϱc := fun _ => 0
      Gc := fun _ => G
      Xc := fun _ => Region.bot
      br := fun _ => MassBranch.complete
      chain := fun j =>
        { β := fun _ => 1
          a := fun _ _ => 0
          ν := fun _ => 0
          e := fun _ => 0
          Dat := fun _ _ => zeroData
          φ := fun _ _ => 0
          α := fun _ _ => 0
          β_ne := fun _ _ _ => one_ne_zero
          coeff := fun n h1 h2 => by omega
          mass := fun n h1 h2 => by omega
          same_h := fun n h1 h2 => by omega
          el := fun n h1 h2 => by omega
          unit := fun n h1 h2 => by omega }
      decomp := fun _ => StepDecomp.empty
      mcount := fun _ => 0
      mcount_eq := fun j => (Finset.sum_eq_zero fun i _ => (i : Empty).elim).symm }
  refine ⟨W, ⟨?_⟩⟩
  have hA : ∀ (j : ℕ) (u : U), (W.chain j).T u 1 = 0 := fun j u => by
    simp [ConvChain.T, W, actionRegionC_bot]
  have hB : ∀ (j : ℕ) (u : U), (W.βk : ℂ) * actionRegionC (W.Xw j) W.ak W.νk (W.Datw u) (W.φw u) = 0 :=
    fun j u => by simp [W, actionRegionC_bot]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j _ n h1 h2; omega
  · intro j _ n h1 h2
    have : n = 1 := by omega
    subst this
    have : (fun u => (W.chain j).T u 1) = fun _ => (0 : ℂ) := funext fun u => hA j u
    rw [this]; exact analyticOnNhd_const
  · intro j _ n h1 h2; omega
  · intro j _ n h1 h2; omega
  · intro j _ n h1 h2; omega
  · intro j _ n h1 h2; omega
  · intro j _ u _
    simp [WindowSetup.bgRem, hA, W]
    exact actionRegionC_bot _ _ _ _
  · intro j _
    have : (fun u => (W.βk : ℂ) * actionRegionC (W.Xw j) W.ak W.νk (W.Datw u) (W.φw u)) =
        fun _ => (0 : ℂ) := funext fun u => hB j u
    rw [this]; exact analyticOnNhd_const

end Balaban.LargeField.ActionConv
