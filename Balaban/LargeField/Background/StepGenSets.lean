module

public import Balaban.LargeField.Background.CubeUnion
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The generating sets of a step: the abstract constructions (Part II, Definition II.2.4)

Generic constructions on the level-`q` torus `Torus d (M1 * N₁ * L ^ q)`; the instantiation in the
region calculus (Lemma II.2.5) is in `Balaban.LargeField.Background.StepGenSetsFlow`.

* `genCube` (i): `G_k(□) = 𝔹_k(□^{∼2})`, level `k`;
* `GeneratingSet.withTop` and `genCubeMixed` (ii): the top layer of `𝔹_{k+1}(□'^{∼2})`
  replaced by `Ω_{k+1} ∩ □'^{∼2}`;
* `genSF` (iii): `𝔹_j(W)` for `j ≤ k` on the level-`k` torus, with `𝔹_j(W) ≺ 𝔹_k(W)`;
* `boundaryGenSet` (iv)/(v): the family `Ω_n = (Ω_n(W) ∖ Ω_{k+1}) ∪ (Ω_n(U) ∩ Ω_{k+1})`, a generating
  set under the separation hypotheses `BoundaryHyp`.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Finset

set_option linter.unusedSectionVars false

/-! ### Replacing the top layer -/

section WithTop

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- Replace the top layer `Ω_k` of a generating set by a smaller union of `k`-blocks. -/
noncomputable def _root_.Balaban.Multiscale.GeneratingSet.withTop (G : Multiscale.GeneratingSet d L N₀ k ϱ)
    (Y : Finset (Torus d (N₀ * L ^ k))) (hY : IsBlockUnion L N₀ k k Y) (hYG : Y ⊆ G.Ω k) :
    Multiscale.GeneratingSet d L N₀ k ϱ := by
  classical
  exact
  { Ω := fun n => if n = k then Y else G.Ω n
    top := by
      simp [G.top]
    subset := by
      intro j hj1 hjk
      by_cases hjk' : j = k
      · subst hjk'
        simp [G.top]
      · have hjne : j ≠ k := hjk'
        by_cases hj1k : j + 1 = k
        · simp only [hj1k, ↓reduceIte, hjne]
          have e : G.Ω (j + 1) = G.Ω k := congrArg G.Ω hj1k
          have hYj : Y ⊆ G.Ω (j + 1) := by rw [e]; exact hYG
          exact hYj.trans (G.subset j hj1 hjk)
        · simp only [hj1k, hjne, ↓reduceIte]
          exact G.subset j hj1 hjk
    blockUnion := by
      intro j hj1 hjk
      by_cases hjk' : j = k
      · subst hjk'; simpa using hY
      · simpa [hjk'] using G.blockUnion j hj1 hjk
    separation := by
      intro j hj1 hjk x hx y hy
      have hjne : j ≠ k := by omega
      simp only [hjne, ↓reduceIte] at hx
      by_cases hj1k : j + 1 = k
      · simp only [hj1k, ↓reduceIte] at hy
        have e : G.Ω (j + 1) = G.Ω k := congrArg G.Ω hj1k
        have hYj : Y ⊆ G.Ω (j + 1) := by rw [e]; exact hYG
        exact G.separation j hj1 hjk x hx y (hYj hy)
      · simp only [hj1k, ↓reduceIte] at hy
        exact G.separation j hj1 hjk x hx y hy }

theorem _root_.Balaban.Multiscale.GeneratingSet.withTop_Ω (G : Multiscale.GeneratingSet d L N₀ k ϱ)
    (Y : Finset (Torus d (N₀ * L ^ k))) (hY : IsBlockUnion L N₀ k k Y) (hYG : Y ⊆ G.Ω k) (n : ℕ) :
    (G.withTop Y hY hYG).Ω n = if n = k then Y else G.Ω n := rfl

end WithTop

variable {d M1 N₁ L q : ℕ} [NeZero L] [NeZero M1] [NeZero N₁]

/-! ### (i), (ii), (iii): cubes and the small-field set -/

section Cubes

variable (c n : ℕ)

/-- **Definition II.2.4 (i)**: `G_k(□) = 𝔹_k(□^{∼2})` on the level-`k` torus; the cube `□` is the
point `a` of `𝕋_k = Torus d n` (cubes of side `L ^ k * (c * M1)`). -/
noncomputable def genCube (a : Torus d n) :
    Multiscale.GeneratingSet d L (M1 * N₁) q (minSep L M1) :=
  minimalGenSet (le_refl q) (cubePre M1 N₁ L q (L ^ q * (c * M1)) n (nbhd 2 {a}))

variable {c n}

theorem genCube_Ω (a : Torus d n) (m : ℕ) :
    (genCube (M1 := M1) (N₁ := N₁) (L := L) (q := q) c n a).Ω m =
      minLayer M1 N₁ L q q (cubePre M1 N₁ L q (L ^ q * (c * M1)) n (nbhd 2 {a})) m := rfl

/-- **Definition II.2.4 (ii)**: `G_{k+1}(□')`, level `q = k+1`: the layers `Ω_1, …, Ω_k` of
`𝔹_{k+1}(□'^{∼2})` and the top layer `Ω_{k+1} ∩ □'^{∼2}`, where `Ω_{k+1}` is the fine set `Om`. -/
noncomputable def genCubeMixed (hm : N₁ * L ^ (q - q) = c * n) (a : Torus d n)
    (Om : Finset (Torus d (M1 * N₁ * L ^ q))) (hOm : IsBlockUnion L (M1 * N₁) q q Om) :
    Multiscale.GeneratingSet d L (M1 * N₁) q (minSep L M1) :=
  (genCube (M1 := M1) (N₁ := N₁) (L := L) (q := q) c n a).withTop
    (Om ∩ cubePre M1 N₁ L q (L ^ q * (c * M1)) n (nbhd 2 {a}))
    (fun x x' h => by
      have h1 := (isCubeUnion_cubePre (M1 := M1) (N₁ := N₁) (L := L) (q := q) (le_refl q) hm
        (nbhd 2 {a})).isBlockUnion (le_refl q) x x' h
      simp only [Finset.mem_inter, hOm x x' h, h1])
    (by
      intro x hx
      have hc := isCubeUnion_cubePre (M1 := M1) (N₁ := N₁) (L := L) (q := q) (le_refl q) hm
        (nbhd 2 {a})
      rw [genCube_Ω, minLayer_self, hc.cubeInterior_eq]
      exact (Finset.mem_inter.1 hx).2)

/-- **Definition II.2.4 (iii)**: `𝔹_j(W)` for `j ≤ q`, `W` a set of `π_q`-cubes (the cube
`π_q` has side `L ^ q * (c * M1)`), as a level-`q` generating set. -/
noncomputable def genSF {j : ℕ} (hj : j ≤ q) (W : Set (Torus d n)) :
    Multiscale.GeneratingSet d L (M1 * N₁) q (minSep L M1) :=
  minimalGenSet hj (cubePre M1 N₁ L q (L ^ q * (c * M1)) n W)

/-- **Definition II.2.4 (iii)**: `𝔹_j(W_k) ≺ 𝔹_k(W_k)` for `j ≤ k`. -/
theorem genSF_precedes {j : ℕ} (hj : j ≤ q) (hm : N₁ * L ^ (q - q) = c * n) (W : Set (Torus d n)) :
    Background.Precedes (genSF (M1 := M1) (N₁ := N₁) (L := L) (c := c) (n := n) hj W)
      (genSF (M1 := M1) (N₁ := N₁) (L := L) (c := c) (n := n) (le_refl q) W) :=
  fun m _ _ => minLayer_le_minLayer hj (le_refl q)
    (isCubeUnion_cubePre (le_refl q) hm W) m

end Cubes

/-! ### (iv), (v): the boundary family -/

section Boundary

variable (M1 N₁ L) (k : ℕ)

/-- The layers `Ω_n = (Ω_n(W) ∖ Om) ∪ (Ω_n(U) ∩ Om)` of Definition II.2.4 (iv), with the
`Ω_n(W)` the layers of `𝔹_k(W)` and the `Ω_n(U)` those of `𝔹_{k+1}(U)` (so the top layer is
`U ∩ Om`, and all layers `n ≥ k + 2` are empty). -/
def boundaryLayer (W U Om : Finset (Torus d (M1 * N₁ * L ^ (k + 1)))) (n : ℕ) :
    Finset (Torus d (M1 * N₁ * L ^ (k + 1))) :=
  (minLayer M1 N₁ L (k + 1) k W n \ Om) ∪ (minLayer M1 N₁ L (k + 1) (k + 1) U n ∩ Om)

/-- The hypotheses under which the boundary family is a generating set (the separation between
the `Ω_{k+1}`-side and the `Ω_{k+1}^c`-side; Lemma II.2.5 (a) (iv), (v)). -/
structure BoundaryHyp (W U Om : Finset (Torus d (M1 * N₁ * L ^ (k + 1)))) : Prop where
  omBlock : IsBlockUnion L (M1 * N₁) (k + 1) (k + 1) Om
  wUnion : IsCubeUnion M1 N₁ L (k + 1) k W
  uUnion : IsCubeUnion M1 N₁ L (k + 1) (k + 1) U
  far₁ : ∀ x ∈ Om, x ∉ U → ∀ y ∈ minLayer M1 N₁ L (k + 1) k W 1, y ∉ Om →
    minSep L M1 * (L : ℝ) ^ k < Green.torusDist d (M1 * N₁ * L ^ (k + 1)) x y
  far₂ : ∀ x ∉ Om, x ∉ W → ∀ y ∈ Om ∩ minLayer M1 N₁ L (k + 1) (k + 1) U 1,
    minSep L M1 * (L : ℝ) ^ k < Green.torusDist d (M1 * N₁ * L ^ (k + 1)) x y

variable {M1 N₁ L k}

section
variable {W U Om : Finset (Torus d (M1 * N₁ * L ^ (k + 1)))}

theorem minSep_nonneg : 0 ≤ minSep L M1 := by unfold minSep; positivity

theorem minSep_pow_le {n : ℕ} (hn : n ≤ k) :
    minSep L M1 * (L : ℝ) ^ n ≤ minSep L M1 * (L : ℝ) ^ k := by
  have hL : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL hn) minSep_nonneg

theorem boundaryLayer_top : boundaryLayer M1 N₁ L k W U Om (k + 1 + 1) = ∅ := by
  unfold boundaryLayer
  rw [minLayer_of_gt W (by omega), minLayer_of_gt U (by omega)]
  simp

theorem boundaryLayer_succ_subset (n : ℕ) :
    boundaryLayer M1 N₁ L k W U Om (n + 1) ⊆ boundaryLayer M1 N₁ L k W U Om n := by
  unfold boundaryLayer
  refine Finset.union_subset_union ?_ ?_
  · exact Finset.sdiff_subset_sdiff (minLayer_succ_subset W) (Finset.Subset.refl _)
  · exact Finset.inter_subset_inter (minLayer_succ_subset U) (Finset.Subset.refl _)

theorem minLayer_antitone {q j : ℕ} {X : Finset (Torus d (M1 * N₁ * L ^ q))} {a b : ℕ}
    (hab : a ≤ b) : minLayer M1 N₁ L q j X b ⊆ minLayer M1 N₁ L q j X a := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hab
  induction t with
  | zero => exact Finset.Subset.refl _
  | succ t ih => exact (minLayer_succ_subset X).trans (ih (by omega))

/-- **Definition II.2.4 (iv)/(v)**: the boundary family as a generating set of level `k+1`. -/
noncomputable def boundaryGenSet (W U Om : Finset (Torus d (M1 * N₁ * L ^ (k + 1))))
    (h : BoundaryHyp M1 N₁ L k W U Om) :
    Multiscale.GeneratingSet d L (M1 * N₁) (k + 1) (minSep L M1) where
  Ω := boundaryLayer M1 N₁ L k W U Om
  top := boundaryLayer_top
  subset := fun n _ _ => boundaryLayer_succ_subset n
  blockUnion := by
    intro n hn1 hnk x x' hxx'
    have hOm := h.omBlock x x' (Background.jBlock_eq_of_le hnk le_rfl hxx')
    simp only [boundaryLayer, Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter,
      minLayer_blockUnion W hnk hxx', minLayer_blockUnion U hnk hxx', hOm]
  separation := by
    intro n hn1 hnk x hx y hy
    have hnk' : n ≤ k := by omega
    simp only [boundaryLayer, Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter, not_or,
      not_and, not_not] at hx hy
    obtain ⟨hx1, hx2⟩ := hx
    have hle := minSep_pow_le (L := L) (M1 := M1) hnk'
    rcases hy with ⟨hyW, hyOm⟩ | ⟨hyU, hyOm⟩
    · by_cases hxOm : x ∈ Om
      · have hxU : x ∉ U := fun hxU =>
          hx2 (h.uUnion.subset_minLayer (by omega : n ≤ k + 1) hxU) hxOm
        exact lt_of_le_of_lt hle
          (h.far₁ x hxOm hxU y (minLayer_antitone (by omega : 1 ≤ n + 1) hyW) hyOm)
      · have hxW : x ∉ minLayer M1 N₁ L (k + 1) k W n := fun hh => hxOm (hx1 hh)
        have hnk2 : n < k := by
          by_contra hge
          rw [minLayer_of_gt W (by omega : k < n + 1)] at hyW
          exact absurd hyW (Finset.notMem_empty _)
        rw [minLayer_of_lt W hnk2] at hxW
        exact torusDist_gt_of_not_mem_nearStep (by omega) hxW hyW
    · by_cases hxOm : x ∈ Om
      · have hxU : x ∉ minLayer M1 N₁ L (k + 1) (k + 1) U n := hx2 |> fun hh hh' => hh hh' hxOm
        rw [minLayer_of_lt U (by omega : n < k + 1)] at hxU
        exact torusDist_gt_of_not_mem_nearStep (by omega) hxU hyU
      · have hxW : x ∉ W := fun hxW => hxOm (hx1 (h.wUnion.subset_minLayer hnk' hxW))
        exact lt_of_le_of_lt hle
          (h.far₂ x hxOm hxW y
            (Finset.mem_inter.2 ⟨hyOm, minLayer_antitone (by omega : 1 ≤ n + 1) hyU⟩))

theorem boundaryGenSet_Ω (W U Om : Finset (Torus d (M1 * N₁ * L ^ (k + 1))))
    (h : BoundaryHyp M1 N₁ L k W U Om) (n : ℕ) :
    (boundaryGenSet W U Om h).Ω n = boundaryLayer M1 N₁ L k W U Om n := rfl

end

end Boundary

end Balaban.LargeField
