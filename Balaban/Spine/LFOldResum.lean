/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.LFOldBBound
public import Balaban.Fluctuation.LocalPairLevelInner
public import Balaban.Fluctuation.LocalPairDepth

/-!
# The resummation over the decoupling families at a mark site (P3 (4.45)–(4.49); P6 p. 34)

This file proves the named input `OldResumSite`.

* `subset_cubeIdx_locG'`: **the cubes of a family are cubes of the cover of its local pair** when the
  collar `r'` of the local set is at least the side `L^{k+1+m₁}` of the cells of the top layer (the
  layers of `G′ ∩ 𝔹_{k+1}(V)` are those of `G′` on the cells inside `V`); hence `|J_V| = |J|`
  (`card_locCubes_eq`).
-/

@[expose] public section

open MeasureTheory Balaban Balaban.LargeField Balaban.LargeField.Def7 Balaban.Multiscale
  Balaban.Localization Balaban.Fluctuation Balaban.LargeField.RegionHistory Balaban.Background
  Balaban.Polymer

namespace Balaban.RootFSpine

section Resum

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {N m₁ : ℕ}
  (g : Geo S n R M) (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) (hM1 : g.M1 = S.L ^ m₁)

omit [NeZero M] in
/-- **The cubes of a family are cubes of the cover of its local pair** (reading HS-1′): if the collar
`r'` of the local set `V(X, J)` is at least `L^{k+1+m₁}`, every cube `(j, y)` of a family `J` of
cubes of the cover of `G′` is a cube of the cover of `G′ ∩ 𝔹_{k+1}(V(X, J))`: the cell of side
`L^{k+1+m₁}` of its base lies in `V(X, J)`, so the base is in the top layer of `𝔹_{k+1}(V(X, J))`
and the layers of the two sets agree there. -/
theorem subset_cubeIdx_locG' (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K)
    (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) {ρ r r' : ℕ} (hr' : S.L ^ (k + 1 + m₁) ≤ r')
    (X : Finset (Torus S.d (n k))) {J : Finset (ℕ × CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1))}
    (hJ : J ∈ allJ g hnn hM1 H hk hρ ρ) :
    J ⊆ (coverOf (locG' g hnn hM1 H hk hρ (locSetXJ g hM1 H r r' X J))).cubeIdx := by
  classical
  intro P hP
  have hPg : P ∈ (coverOf (stepG' g hnn hM1 H hk hρ)).cubeIdx :=
    (Finset.mem_filter.1 (Finset.mem_powerset.1 hJ hP)).1
  obtain ⟨hj, hlay, hbase⟩ := (mem_cubeIdx _).1 hPg
  refine (mem_cubeIdx _).2 ⟨hj, ?_, hbase⟩
  obtain ⟨hyΩ, hyΩ'⟩ := (GeneratingSet.mem_layer _).1 hlay
  have htop : P.2 ∈ (locB g hM1 (locSetXJ g hM1 H r r' X J)).Ω (k + 1) := by
    refine (mem_localB_Ω_top_sameCell le_rfl _ (minSep_le_locB g hM1) P.2).2 fun w hw => ?_
    refine ⟨P.2, Or.inr ⟨P, hP, (mem_cubeP).2 (SameCell.refl _ _)⟩, ?_⟩
    exact (supDist_le_of_sameCell (pow_pos (Nat.pos_of_ne_zero (NeZero.ne S.L)) _) hw).trans hr'
  have hB : P.2 ∈ (locB g hM1 (locSetXJ g hM1 H r r' X J)).Ω P.1 :=
    GeneratingSet.Ω_antitone (locB g hM1 (locSetXJ g hM1 H r r' X J)) hj.1 hj.2 (Nat.le_succ _) htop
  refine (GeneratingSet.mem_layer _).2 ⟨?_, fun h => hyΩ' ?_⟩
  · show P.2 ∈ (stepG' g hnn hM1 H hk hρ).Ω P.1 ∩ (locB g hM1 (locSetXJ g hM1 H r r' X J)).Ω P.1
    exact Finset.mem_inter.2 ⟨hyΩ, hB⟩
  · have h' : P.2 ∈ (stepG' g hnn hM1 H hk hρ).Ω (P.1 + 1) ∩
        (locB g hM1 (locSetXJ g hM1 H r r' X J)).Ω (P.1 + 1) := h
    exact (Finset.mem_inter.1 h').1

omit [NeZero M] in
/-- **`|J_V| = |J|`** for the families of the old part (`subset_cubeIdx_locG'`). -/
theorem card_locCubes_eq (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K)
    (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) {ρ r r' : ℕ} (hr' : S.L ^ (k + 1 + m₁) ≤ r')
    (X : Finset (Torus S.d (n k))) {J : Finset (ℕ × CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1))}
    (hJ : J ∈ allJ g hnn hM1 H hk hρ ρ) :
    (locCubes g (coverOf (locG' g hnn hM1 H hk hρ (locSetXJ g hM1 H r r' X J))) J).card = J.card := by
  classical
  have hsub := subset_cubeIdx_locG' g hnn hM1 H hk hρ (r := r) hr' X hJ
  unfold locCubes
  rw [← Finset.card_map (Function.Embedding.subtype _)]
  congr 1
  ext P
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
    Function.Embedding.coe_subtype]
  constructor
  · rintro ⟨Q, hQ, rfl⟩
    exact hQ
  · intro hP
    exact ⟨⟨P, hsub hP⟩, hP, rfl⟩

end Resum

end Balaban.RootFSpine
