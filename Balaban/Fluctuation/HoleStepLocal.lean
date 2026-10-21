/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.HoleStep
public import Balaban.Localization.P6PairCover

/-!
# The step on a region restricted to a local set (reading HS-1′)

Reading HS-1′ (`notes/phase1/PLAN-B.md`; P5 (2.18)–(2.20): the approximate background "depends
only on `R_{k+1}(□')`", P3 Proposition 2.3, P6 p. 33): the coefficient of an old boundary term is
computed on the local pair, the restriction of the pair `(coverOf G′, G′)` of the step to a local
set.  The restriction of a generating set `G` to a set `B` (a local generating set, for instance
`𝔹_j(V)`) is the layerwise intersection.

* `GeneratingSet.inter`: the layerwise intersection of two generating sets with the same
  separation (the separation of the intersection is inherited from one of the two sets at each
  pair of sites);
* `CubeAligned.inter`, `supSep_inter`, `precedes_inter`: cube alignment, sup-separation and the
  order `≺` pass to the intersections;
* `HoleStep.restrict`: the step on a region restricted to the local sets `B ≺ B'` (old set
  `G ∩ B`, set of (2.17) `G′ ∩ B'`), with a datum of the restricted set; `unitPts_restrict_subset`:
  its unit points are unit points of the step.
-/

@[expose] public section

namespace Balaban.Multiscale.GeneratingSet

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- **The layerwise intersection of two generating sets** with the same separation `ϱ`:
`Ω_j(G ∩ B) = Ω_j(G) ∩ Ω_j(B)`. -/
def inter (G B : GeneratingSet d L N₀ k ϱ) : GeneratingSet d L N₀ k ϱ where
  Ω j := G.Ω j ∩ B.Ω j
  top := by rw [G.top, Finset.empty_inter]
  subset j hj hjk := Finset.inter_subset_inter (G.subset j hj hjk) (B.subset j hj hjk)
  blockUnion j hj hjk x x' h := by
    simp only [Finset.mem_inter, G.blockUnion j hj hjk x x' h, B.blockUnion j hj hjk x x' h]
  separation j hj hjk x hx y hy := by
    rw [Finset.mem_inter, not_and_or] at hx
    rw [Finset.mem_inter] at hy
    rcases hx with hx | hx
    · exact G.separation j hj hjk x hx y hy.1
    · exact B.separation j hj hjk x hx y hy.2

theorem inter_Ω (G B : GeneratingSet d L N₀ k ϱ) (j : ℕ) :
    (G.inter B).Ω j = G.Ω j ∩ B.Ω j := rfl

theorem inter_Ω_subset_left (G B : GeneratingSet d L N₀ k ϱ) (j : ℕ) :
    (G.inter B).Ω j ⊆ G.Ω j :=
  Finset.inter_subset_left

end Balaban.Multiscale.GeneratingSet

namespace Balaban.Localization

open Balaban.Multiscale

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- The intersection of two cube-aligned sets is cube aligned. -/
theorem CubeAligned.inter {G B : GeneratingSet d L N₀ k ϱ} {m₁ : ℕ} (hG : CubeAligned G m₁)
    (hB : CubeAligned B m₁) : CubeAligned (G.inter B) m₁ where
  two_le := hG.two_le
  dvd := hG.dvd
  union j hj hjk x x' h := by
    simp only [GeneratingSet.inter_Ω, Finset.mem_inter, hG.union j hj hjk x x' h,
      hB.union j hj hjk x x' h]

/-- The intersection of two sup-separated sets is sup-separated. -/
theorem supSep_inter {G B : GeneratingSet d L N₀ k ϱ} {m₁ : ℕ} (hG : SupSep G m₁)
    (hB : SupSep B m₁) : SupSep (G.inter B) m₁ := by
  intro j hj hjk x hx y hy
  rw [GeneratingSet.inter_Ω, Finset.mem_inter, not_and_or] at hx
  rw [GeneratingSet.inter_Ω, Finset.mem_inter] at hy
  rcases hx with hx | hx
  · exact hG j hj hjk x hx y hy.1
  · exact hB j hj hjk x hx y hy.2

end Balaban.Localization

namespace Balaban.Background

open Balaban.Multiscale

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ ϱ' : ℝ}

/-- The order `≺` passes to the intersections with two local sets `B ≺ B'`. -/
theorem precedes_inter {G B : GeneratingSet d L N₀ k ϱ} {G' B' : GeneratingSet d L N₀ k ϱ'}
    (h : Precedes G G') (hB : Precedes B B') : Precedes (G.inter B) (G'.inter B') :=
  fun i hi hik => Finset.inter_subset_inter (h i hi hik) (hB i hi hik)

end Balaban.Background

namespace Balaban.Fluctuation

open Balaban.Multiscale Balaban.Background Balaban.Localization

namespace HoleStep

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱ' : ℝ}

/-- **The step on a region restricted to the local sets `B ≺ B'`** (reading HS-1′): the old set
`G ∩ B`, the set of (2.17) `G′ ∩ B'`, a datum `D''` of the restricted set with the constant field
`h₀` of the step, and the constants of the step. -/
def restrict (S : HoleStep d L N₁ m₁ k N ϱ ϱ')
    (B : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ) (B' : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ')
    (hBB : Precedes B B') (hBtop : B'.Ω (k + 1) ⊆ B.Ω k) (D'' : BgData (S.G'.inter B') N)
    (hh : ∀ x ∈ (S.G'.inter B').Ω 1, ∀ i, D''.h x i = (S.h₀ i : ℂ)) :
    HoleStep d L N₁ m₁ k N ϱ ϱ' where
  G := S.G.inter B
  G' := S.G'.inter B'
  hpre := precedes_inter S.hpre hBB
  topG := by rw [GeneratingSet.inter_Ω, S.topG, Finset.empty_inter]
  topIn := Finset.inter_subset_inter S.topIn hBtop
  hk1 := S.hk1
  D' := D''
  h₀ := S.h₀
  hh₀ := hh
  a₁ := S.a₁
  ν := S.ν
  β := S.β
  p₁ := S.p₁
  δ := S.δ

/-- The unit points of the restricted step are unit points of the step. -/
theorem unitPts_restrict_subset (S : HoleStep d L N₁ m₁ k N ϱ ϱ')
    (B : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ) (B' : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ')
    (hBB : Precedes B B') (hBtop : B'.Ω (k + 1) ⊆ B.Ω k) (D'' : BgData (S.G'.inter B') N)
    (hh : ∀ x ∈ (S.G'.inter B').Ω 1, ∀ i, D''.h x i = (S.h₀ i : ℂ)) :
    unitPts (S.restrict B B' hBB hBtop D'' hh).G' ⊆ unitPts S.G' := by
  intro b hb
  obtain ⟨x, hx, rfl⟩ := (mem_unitPts _).1 hb
  refine (mem_unitPts _).2 ⟨x, ?_, rfl⟩
  rw [GeneratingSet.mem_layer] at hx ⊢
  refine ⟨(Finset.mem_inter.1 hx.1).1, ?_⟩
  rw [S.G'.top]
  exact Finset.notMem_empty _

end HoleStep

end Balaban.Fluctuation
