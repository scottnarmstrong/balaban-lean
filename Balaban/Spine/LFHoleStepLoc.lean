/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.LFOldH7
public import Balaban.Fluctuation.HoleStepLocal
public import Balaban.LargeField.Background.HoleStepCover

/-!
# The step on a region of a history restricted to a local set (reading HS-1′)

Reading HS-1′ (`notes/phase1/PLAN-B.md`; P5 (2.18)–(2.20), P3 Proposition 2.3, P6 p. 33): the
coefficient of an old boundary term is computed on the local pair, the restriction of the pair
`(coverOf G′, G′)` of the step on a region of a history to the local set `𝔹_{k+1}(V)` of a set `V`
of the cover torus.  The datum of the local pair is the mixed lift of the same fields (`ψ_k` and
`θ = z ψ_{k+1}`) on the restricted set, so the coefficient reads the fields only at the data sites of
the restricted set.

* `locB`: `𝔹_{k+1}(V)` on the cover torus (`SmallField.GsSpec.localB`);
* `holeStepLoc`: the step on a region of the history restricted to `𝔹_{k+1}(V)`
  (`Fluctuation.HoleStep.restrict`);
* `cubeOfC_mem_of_unitPts_loc`: the unit points of the restricted step lie in `Ω_{k+1}` (so the
  transfer `h7Domain_composedMulti_of_inner` applies to it);
* `holeStepLoc_cubeAligned`, `holeStepLoc_supSep`, `holeStepLoc_coverBase`, `holeStepLoc_xCover`:
  the restricted set of (2.17) is cube aligned and sup-separated, so the restricted pair has the
  cover estimates of the landed development (`Dec2.CoverBase`, `Dec2.XCover`).

The coefficient on the local pair is `oldCoefLF` at the restricted step and its cover
(`oldCoefLF g hnn hM1 (holeStepLoc …) H hk (coverOf (holeStepLoc …).G') …`).
-/

@[expose] public section

open MeasureTheory Balaban Balaban.LargeField Balaban.LargeField.Def7 Balaban.Multiscale
  Balaban.Localization Balaban.Fluctuation Balaban.LargeField.RegionHistory Balaban.Background

namespace Balaban.RootFSpine

section Local

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {N m₁ : ℕ}
  (g : Geo S n R M) (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) (hM1 : g.M1 = S.L ^ m₁)

omit [∀ k, NeZero (n k)] [NeZero M] [NeZero S.L] in
include hM1 in
/-- The separation of the local set: `minSep L M₁ ≤ minSep L L^{m₁}`. -/
theorem minSep_le_locB : minSep S.L g.M1 ≤ minSep S.L (S.L ^ m₁) := by rw [hM1]

/-- **`𝔹_{k+1}(V)` on the cover torus of the step** (P3 (4.4)–(4.6), `SmallField.GsSpec.localB`):
the top layer is the union of the cubes of `𝕋_{k+1}` inside `V`. -/
noncomputable def locB {k : ℕ} (V : Set (CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1))) :
    GeneratingSet S.d S.L ((g.c * n (k + 1)) * S.L ^ m₁) (k + 1) (minSep S.L g.M1) :=
  SmallField.GsSpec.localB (k + 1) le_rfl V (minSep_le_locB g hM1)

/-- **The step on a region of the history restricted to `𝔹_{k+1}(V)`** (reading HS-1′): the old set
`𝔹_k(W_k) ∩ 𝔹_{k+1}(V)`, the set of (2.17) `G′ ∩ 𝔹_{k+1}(V)`, and the mixed lift of the old field
`ψ_k` and of the block variable `θ = z ψ_{k+1}` on the restricted set. -/
noncomputable def holeStepLoc (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K) (hk1 : 1 ≤ k)
    (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (ψ : MultiFieldC S n M K N) (z : ℝ) (h₀ : Fin N → ℝ)
    (a₁ ν β p₁ δ : ℝ) (V : Set (CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1))) :
    HoleStep S.d S.L (g.c * n (k + 1)) m₁ k N (minSep S.L g.M1) (minSep S.L g.M1) :=
  (holeStepLF g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).restrict (locB g hM1 V) (locB g hM1 V)
    (SmallField.precedes_refl _) ((locB g hM1 V).subset k hk1 (Nat.le_succ k))
    (liftMixed ((holeStepLF g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).G'.inter (locB g hM1 V))
      (((holeStepLF g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).G'.inter (locB g hM1 V)).blockUnion
        (k + 1) (by omega) le_rfl) subset_rfl
      (coverField g hnn hM1 hk ψ k (Nat.le_succ k))
      (coverField g hnn hM1 hk (scaleMulti z ψ) (k + 1) le_rfl) (fun i => (h₀ i : ℂ)))
    (fun _ hx _ => by rw [liftMixed_h _ _ _ _ _ _ hx]; rfl)

omit [NeZero M] in
theorem holeStepLoc_G' (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K) (hk1 : 1 ≤ k)
    (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (ψ : MultiFieldC S n M K N) (z : ℝ) (h₀ : Fin N → ℝ)
    (a₁ ν β p₁ δ : ℝ) (V : Set (CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1))) :
    (holeStepLoc g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).G' =
      (holeStepLF g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).G'.inter (locB g hM1 V) := rfl

omit [NeZero M] in
/-- **The unit points of the restricted step lie in `Ω_{k+1}`** (`cubeOfC_mem_of_unitPts`). -/
theorem cubeOfC_mem_of_unitPts_loc (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K)
    (hk1 : 1 ≤ k) (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (ψ : MultiFieldC S n M K N) (z : ℝ)
    (h₀ : Fin N → ℝ) (a₁ ν β p₁ δ : ℝ) (V : Set (CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)))
    (b : (holeStepLoc g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).U) :
    cubeOfC (c := g.c) (n1 := n (k + 1)) hM1 (unitRep b) ∈ (H.step k).Omega :=
  cubeOfC_mem_of_unitPts g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ
    ⟨b.1, HoleStep.unitPts_restrict_subset _ _ _ _ _ _ _ b.2⟩

omit [NeZero M] in
/-- **The restricted set of (2.17) is cube aligned** (`m₁ ≥ 2`). -/
theorem holeStepLoc_cubeAligned (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K)
    (hk1 : 1 ≤ k) (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (ψ : MultiFieldC S n M K N) (z : ℝ)
    (h₀ : Fin N → ℝ) (a₁ ν β p₁ δ : ℝ) (V : Set (CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)))
    (hm₁ : 2 ≤ m₁) :
    CubeAligned (holeStepLoc g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).G' m₁ := by
  have hc := g.hc
  exact (p6TopC_cubeAligned hM1 (hnn k (by omega)) hρ (by omega) hm₁).inter
    (localB_cubeAligned le_rfl V (minSep_le_locB g hM1) hm₁)

omit [NeZero M] in
/-- **The restricted set of (2.17) is sup-separated.** -/
theorem holeStepLoc_supSep (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K)
    (hk1 : 1 ≤ k) (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (ψ : MultiFieldC S n M K N) (z : ℝ)
    (h₀ : Fin N → ℝ) (a₁ ν β p₁ δ : ℝ) (V : Set (CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1))) :
    SupSep (holeStepLoc g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).G' m₁ := by
  have hc := g.hc
  exact supSep_inter (p6TopC_supSep hM1 (hnn k (by omega)) hρ (by omega))
    (localB_supSep le_rfl V (minSep_le_locB g hM1))

omit [NeZero M] in
/-- **The cover base of the restricted pair** `(coverOf G′_V, G′_V)` (as `p6TopC_coverBase`). -/
theorem holeStepLoc_coverBase (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K)
    (hk1 : 1 ≤ k) (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (ψ : MultiFieldC S n M K N) (z : ℝ)
    (h₀ : Fin N → ℝ) (a₁ ν β p₁ δ : ℝ) (V : Set (CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)))
    (hm₁ : 2 ≤ m₁) (hN : 5 < g.c * n (k + 1)) (hM : 4 * S.L ^ 2 ≤ S.L ^ m₁) {a : ℕ → ℝ} {ν' : ℝ}
    (hd : 3 ≤ S.d) (hL : 3 ≤ S.L) (hν : 0 ≤ ν') (hνL : ν' * ((S.L : ℝ) ^ (k + 1)) ^ 2 ≤ 1)
    (ha : IsAdmissibleWeights (k + 1) a)
    (hag : 2 * S.d * Real.log S.L ≤ agmonRate S.d / 16 * (minSep S.L g.M1 - 1)) :
    Dec2.CoverBase (coverOf (holeStepLoc g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).G')
      (holeStepLoc g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).G' a ν' (Dec2.mixedKc S.d S.L)
      (Cchi S.d S.L) :=
  coverBase_of_aligned_supSep (holeStepLoc_cubeAligned g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V hm₁)
    (holeStepLoc_supSep g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V) hN hM hd hL hν hνL ha hag

omit [NeZero M] in
/-- **`Dec2.XCover` of the restricted pair** (the weights `a_k`, `a_{k+1} = a_T` in `[1/2, 2]`). -/
theorem holeStepLoc_xCover (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K)
    (hk1 : 1 ≤ k) (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (ψ : MultiFieldC S n M K N) (z : ℝ)
    (h₀ : Fin N → ℝ) (a₁ ν β p₁ δ : ℝ) (V : Set (CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)))
    (hm₁ : 2 ≤ m₁) (hN : 5 < g.c * n (k + 1)) (hM : 4 * S.L ^ 2 ≤ S.L ^ m₁) {a : ℕ → ℝ} {ν' : ℝ}
    (hd : 3 ≤ S.d) (hL : 3 ≤ S.L) (hν : 0 ≤ ν') (hνL : ν' * ((S.L : ℝ) ^ (k + 1)) ^ 2 ≤ 1)
    (ha : IsAdmissibleWeights (k + 1) a)
    (hag : 2 * S.d * Real.log S.L ≤ agmonRate S.d / 16 * (minSep S.L g.M1 - 1)) {aT : ℝ}
    (haT1 : 1 / 2 ≤ aT) (haT2 : aT ≤ 2) :
    Dec2.XCover (coverOf (holeStepLoc g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).G')
      (holeStepLoc g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).G' a aT ν' (Cchi S.d S.L) :=
  ⟨(holeStepLoc_coverBase g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V hm₁ hN hM hd hL hν hνL ha
      hag).toCoverGeom, (ha k hk1 (Nat.le_succ k)).1, (ha k hk1 (Nat.le_succ k)).2, haT1, haT2⟩

end Local

end Balaban.RootFSpine
