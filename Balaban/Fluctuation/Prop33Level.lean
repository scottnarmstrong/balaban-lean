/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.TreeLengthCov
public import Balaban.Fluctuation.CriticalPoint
import Mathlib.Tactic.Linarith

/-!
# The multiscale covering size of a level generating set is the single-scale size

For a generating set `G` of level `lev` (`IsLevel G lev`: every site lies in the layer `lev`), the
multiscale functional `d̃^cov` (`treeLenCov`) is the single-scale covering size
`d^cov_{lev}` of FLUCTUATION Definition 1.1 on the whole torus (`treeLenCovOne m₀ lev`):
`treeLenCov_eq_treeLenCovOne`.  This is the conversion needed to state the bound of Proposition 3.3
in terms of `d^cov_{k+1}(Y)`: the generating set `Gp` of the proposition has level `n + 1 = k + 1`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Multiscale

section Level

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {lev : ℕ}

/-- In a level generating set the bond weight of the multiscale size is the scale weight. -/
theorem bondW_eq_scaleW {m₀ : ℕ} (hG : IsLevel G lev) (x y : CTorus d L N₁ m₁ K) :
    bondW G m₀ x y = scaleW L m₀ m₁ lev x y := by
  unfold bondW scaleW
  rw [(hG x).2, (hG y).2, min_self, ← mul_inv, ← pow_add]

/-- **Conversion `d̃^cov = d^cov_{lev}`.**  For a generating set of level `lev` the multiscale
covering size of every set `Y` equals the single-scale covering size at scale `lev`. -/
theorem treeLenCov_eq_treeLenCovOne (hG : IsLevel G lev) (m₀ : ℕ)
    (Y : Set (CTorus d L N₁ m₁ K)) : treeLenCov G m₀ Y = treeLenCovOne m₀ lev Y := by
  obtain ⟨h1, hK⟩ := hG.bounds
  have hW : (bondW G m₀ : CTorus d L N₁ m₁ K → CTorus d L N₁ m₁ K → ℝ) =
      scaleW L m₀ m₁ lev := by
    funext x y; exact bondW_eq_scaleW hG x y
  unfold treeLenCov treeLenCovOne
  congr 1
  ext x
  simp only [Set.mem_ofPred_eq]
  rw [hW]
  constructor
  · rintro ⟨𝒦, W, E, hch, hc, hWY, hm, rfl⟩
    refine ⟨𝒦 lev, W, E, ?_, hc, hWY, fun b hb => hm lev h1 hK b hb, rfl⟩
    obtain ⟨ha, hb⟩ := hch lev h1 hK
    exact ⟨fun b hb' => ⟨(ha b hb').1, (ha b hb').2.1⟩, fun z hz => by
      obtain ⟨b, hb', hzb⟩ := hb z hz (hG.mem_layer z)
      exact ⟨b, hb', hzb⟩⟩
  · rintro ⟨𝒦, W, E, hch, hc, hWY, hm, rfl⟩
    classical
    refine ⟨fun n => if n = lev then 𝒦 else ∅, W, E, ?_, hc, hWY, ?_, rfl⟩
    · intro n hn1 hnK
      by_cases hn : n = lev
      · subst hn
        simp only [↓reduceIte]
        refine ⟨fun b hb => ⟨(hch.1 b hb).1, (hch.1 b hb).2, fun z _ => ?_⟩, fun z hz _ => ?_⟩
        · exact Finset.mem_coe.2 (hG.mem_layer z)
        · exact hch.2 z hz
      · simp only [hn, ↓reduceIte]
        refine ⟨fun b hb => absurd hb (Set.notMem_empty b), fun z _ hzl => ?_⟩
        exact absurd (Finset.mem_coe.1 hzl)
          (G.layer_disjoint h1 hK hn1 hnK (Ne.symm hn) (hG.mem_layer z))
    · intro n hn1 hnK b hb
      by_cases hn : n = lev
      · subst hn
        simp only [↓reduceIte] at hb
        exact hm b hb
      · simp only [hn, ↓reduceIte] at hb
        exact absurd hb (Set.notMem_empty b)

end Level

end Balaban.Fluctuation
