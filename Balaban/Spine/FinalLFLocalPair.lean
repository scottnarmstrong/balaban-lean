/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.HoleStepLocal
public import Balaban.LargeField.Def7SmallField

/-!
# The local pair of the last integral deep in the small-field region (reading B-1″)

Reading B-1″ (`notes/phase1/PLAN-B.md`): every piece of the last integral at a localization domain
is computed on the local pair, the restriction (`GeneratingSet.inter`, reading HS-1′) of the
generating set of the problem to a local set. The small-field factor of a history reads the
background of the minimal generating set `𝔹_k(W₂(Z^c))` (`SFCtx.genW`), whose layers are all full on
`W₂(Z^c)`; the multi-level part lies outside it, in `Z`. So the local pair of a local set inside the
top layer is the same for the region and for the whole torus:

* `genSF_top_subset`: the top layer of `𝔹_q(W)` lies in every layer `n ≤ q`;
* `genSF_univ_Ω`: the layers `n ≤ q` of `𝔹_q(univ)` are the whole torus;
* **`genSF_inter_eq_univ_inter`**: for a generating set `B` whose layers `n ≤ q` lie in the top layer
  of `𝔹_q(W)`, `𝔹_q(W) ∩ B = 𝔹_q(univ) ∩ B`;
* **`SFCtx.genW_inter_eq`**: the instance at the generating set `genW Y = 𝔹_k(W₂(Y))` of the
  small-field factor on `Y`: `genW Y ∩ B = genW univ ∩ B`.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale

section MinLayer

variable {d M1 N₁ L q : ℕ} [NeZero L] [NeZero M1] [NeZero N₁]

/-- The layers of `𝔹_j(X)` decrease: `Ω_n ⊆ Ω_m` for `m ≤ n`. -/
theorem minLayer_anti {j : ℕ} (X : Finset (Torus d (M1 * N₁ * L ^ q))) {m n : ℕ} (hmn : m ≤ n) :
    minLayer M1 N₁ L q j X n ⊆ minLayer M1 N₁ L q j X m := by
  induction n, hmn using Nat.le_induction with
  | base => exact subset_rfl
  | succ n _ ih => exact (minLayer_succ_subset X).trans ih

variable {c n : ℕ}

/-- The top layer of `𝔹_q(W)` lies in every layer `m ≤ q`. -/
theorem genSF_top_subset (W : Set (Torus d n)) {m : ℕ} (hm : m ≤ q) :
    (genSF (M1 := M1) (N₁ := N₁) (L := L) (c := c) (n := n) (le_refl q) W).Ω q ⊆
      (genSF (M1 := M1) (N₁ := N₁) (L := L) (c := c) (n := n) (le_refl q) W).Ω m :=
  minLayer_anti _ hm

/-- The layers `m ≤ q` of `𝔹_q(univ)` are the whole torus. -/
theorem genSF_univ_Ω {m : ℕ} (hm : m ≤ q) :
    (genSF (M1 := M1) (N₁ := N₁) (L := L) (c := c) (n := n) (le_refl q)
      (Set.univ : Set (Torus d n))).Ω m = Finset.univ := by
  refine Finset.eq_univ_of_forall fun x => minLayer_anti _ hm ?_
  show x ∈ minLayer M1 N₁ L q q (cubePre M1 N₁ L q (L ^ q * (c * M1)) n Set.univ) q
  rw [minLayer_self, mem_cubeInterior]
  intro y _
  rw [mem_cubePre]
  trivial

/-- **The local pair deep in the small-field region** (reading B-1″): for a generating set `B`
whose layers `m ≤ q` lie in the top layer of `𝔹_q(W)`, the restrictions of `𝔹_q(W)` and of
`𝔹_q(univ)` to `B` are equal. -/
theorem genSF_inter_eq_univ_inter (W : Set (Torus d n))
    (B : GeneratingSet d L (M1 * N₁) q (minSep L M1))
    (hB : ∀ m, m ≤ q → B.Ω m ⊆
      (genSF (M1 := M1) (N₁ := N₁) (L := L) (c := c) (n := n) (le_refl q) W).Ω q) :
    (genSF (M1 := M1) (N₁ := N₁) (L := L) (c := c) (n := n) (le_refl q) W).inter B =
      (genSF (M1 := M1) (N₁ := N₁) (L := L) (c := c) (n := n) (le_refl q)
        (Set.univ : Set (Torus d n))).inter B := by
  unfold GeneratingSet.inter
  congr 1
  funext m
  by_cases hm : m ≤ q
  · rw [genSF_univ_Ω hm, Finset.univ_inter,
      Finset.inter_eq_right.mpr ((hB m hm).trans (genSF_top_subset W hm))]
  · have h1 : q < m := by omega
    show minLayer M1 N₁ L q q _ m ∩ B.Ω m = minLayer M1 N₁ L q q _ m ∩ B.Ω m
    rw [minLayer_of_gt _ h1, minLayer_of_gt _ h1]

end MinLayer

namespace Def7

section Ctx

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N k m₁ : ℕ} {ϱ : ℝ}

/-- **The local pair of the small-field factor on `Y` deep inside `Y`** (reading B-1″): for a
generating set `B` of the level-`k` torus whose layers `m ≤ k` lie in the top layer of
`genW Y = 𝔹_k(W₂(Y))`, `genW Y ∩ B = genW univ ∩ B`. The regional and the whole-torus pieces
computed on `B` are therefore the same. -/
theorem SFCtx.genW_inter_eq (C : SFCtx S n R M K N k m₁ ϱ) (Y : Set (Torus S.d (n k)))
    (B : GeneratingSet S.d S.L (C.geo.M1 * (C.geo.c * n k)) k (minSep S.L C.geo.M1))
    (hB : ∀ m, m ≤ k → B.Ω m ⊆ (C.genW Y).Ω k) :
    (C.genW Y).inter B = (C.genW Set.univ).inter B := by
  have hW : W2 R (Set.univ : Set (Torus S.d (n k))) = Set.univ :=
    Set.eq_univ_of_univ_subset ((subset_nbhd _ _).trans (subset_nbhd _ _))
  have e : C.genW Set.univ = genSF (M1 := C.geo.M1) (N₁ := C.geo.c * n k) (L := S.L)
      (c := C.geo.c) (n := n k) (le_refl k) Set.univ := by
    show genSF _ (W2 R Set.univ) = _
    rw [hW]
  rw [e]
  exact genSF_inter_eq_univ_inter (W2 R Y) B hB

end Ctx

end Def7

end Balaban.LargeField
