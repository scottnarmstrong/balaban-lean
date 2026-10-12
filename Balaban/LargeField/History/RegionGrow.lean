module

public import Balaban.LargeField.History.GainClock

/-!
# Regions grow across several scales (Part I, Lemma I.4.3 (b))

In the overwritten history `Z_j ⊂ Z_{j+1} ⊂ ⋯ ⊂ Z_k` as fine sets.  `Zov j t` is the region of
scale `j` after the overwrites of the scales `j, …, j + t - 1`.  With the maps
`cubeMap n L M K j : 𝕋_fine → 𝕋_j` (so that `cm s j (cubeMap j x) = cubeMap (j + s) x`, no cast
between `Torus (n (j + 1 + s))` and `Torus (n (j + (s + 1)))` is needed) the statement is

* `regions_grow`: `x ∈ Z_j^{(t)} ⇒ x ∈ Z_{j+s}^{(t-s)}` for `s ≤ t`, and `x ∈ Z^pre_{j+s}` for
  `1 ≤ s ≤ t`;
* `fine_regions_grow`: the same for the fine sets `fineSet M K j (Zov j t)`;
* `fine_lineage_subset`: `Lin_j(Z) ⊂ Z` as fine sets.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban

namespace RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}
  (H : RegionHistory S n R k0 K) {M : ℕ} [NeZero M]

include H in
theorem neZero_L : NeZero S.L := ⟨by have := H.F.ok.two_le_L; omega⟩

/-- The coarsening `cm s j` is compatible with the maps from the fine torus. -/
theorem cm_cubeMap [NeZero S.L] (hnn : ∀ i, i < K → n i = S.L * n (i + 1))
    (x : Torus S.d (M * n K * S.L ^ K)) :
    ∀ (s j : ℕ), j + s ≤ K → cm (S := S) (n := n) s j (cubeMap n S.L M K j x) =
      cubeMap n S.L M K (j + s) x := by
  intro s
  induction s with
  | zero => intro j _; rfl
  | succ s ih =>
    intro j hj
    show blockMap S.L (n (j + s + 1)) (cm s j (cubeMap n S.L M K j x)) = _
    rw [ih j (by omega)]
    exact cubeMap_succ hnn (by omega) x

/-- **Lemma I.4.3 (b), several scales**: the overwritten region at scale `j` is contained in the
overwritten region at scale `j + s`, as fine sets. -/
theorem regions_grow {j t s : ℕ} (hs : s ≤ t) (hjt : j + t ≤ K) {x : Torus S.d (M * n K * S.L ^ K)}
    (hx : cubeMap n S.L M K j x ∈ H.Zov j t) : cubeMap n S.L M K (j + s) x ∈ H.Zov (j + s) (t - s) := by
  have := H.neZero_L
  have hmem : ∀ u, u < t → j + u ≤ K → cubeMap n S.L M K (j + u) x ∈ (H.step (j + u)).Z := by
    intro u hu hjuK
    have := hx.2 u hu
    rwa [cm_cubeMap H.F.hnn x u j hjuK] at this
  refine ⟨?_, fun s' hs' => ?_⟩
  · -- `x ∈ Z^pre_{j+s}`
    rcases Nat.eq_zero_or_pos s with h0 | hpos
    · subst h0; exact hx.1
    · obtain ⟨u, rfl⟩ : ∃ u, s = u + 1 := ⟨s - 1, by omega⟩
      have h1 := hmem u (by omega) (by omega)
      have h2 := H.blockMap_Z_subset_Zpre (j + u) h1
      rwa [cubeMap_succ H.F.hnn (by omega) x] at h2
  · rw [cm_cubeMap H.F.hnn x s' (j + s) (by omega)]
    have := hmem (s + s') (by omega) (by omega)
    rwa [← Nat.add_assoc] at this

/-- The fine form of `regions_grow`. -/
theorem fine_regions_grow {j t s : ℕ} (hs : s ≤ t) (hjt : j + t ≤ K) :
    fineSet (S := S) (n := n) M K j (H.Zov j t) ⊆
      fineSet (S := S) (n := n) M K (j + s) (H.Zov (j + s) (t - s)) :=
  fun _ hx => H.regions_grow hs hjt hx

/-- The chain `Z_j ⊂ Z_{j+1} ⊂ ⋯ ⊂ Z_T` of the overwritten regions after all overwrites up to
scale `T`: `Zov j (T - j) ⊂ Zov j' (T - j')` as fine sets for `j ≤ j' ≤ T ≤ K`. -/
theorem fine_regions_chain {j j' T : ℕ} (hj : j ≤ j') (hT : j' ≤ T) (hK : T ≤ K) :
    fineSet (S := S) (n := n) M K j (H.Zov j (T - j)) ⊆
      fineSet (S := S) (n := n) M K j' (H.Zov j' (T - j')) := by
  obtain ⟨s, rfl⟩ : ∃ s, j' = j + s := ⟨j' - j, by omega⟩
  have := H.fine_regions_grow (M := M) (K := K) (j := j) (t := T - j) (s := s) (by omega) (by omega)
  rwa [show T - j - s = T - (j + s) by omega] at this

/-- `Lin_j(Z) ⊂ Z` as fine sets (Lemma I.4.3 (c)). -/
theorem fine_lineage_subset {j t : ℕ} (hjt : j + t ≤ K) (Z : H.Comp (j + t)) :
    fineSet (S := S) (n := n) M K j (H.lineage j t Z) ⊆
      fineSet (S := S) (n := n) M K (j + t) (Z.1 : Set (Torus S.d (n (j + t)))) := by
  have := H.neZero_L
  intro x hx
  have h : cubeMap n S.L M K j x ∈ {y | y ∈ H.Zov j t ∧ cm (S := S) (n := n) t j y ∈ Z.1} := by
    rw [← H.lineage_eq_inter j t Z hjt]; exact hx
  have h2 : cm (S := S) (n := n) t j (cubeMap n S.L M K j x) ∈ Z.1 := h.2
  show cubeMap n S.L M K (j + t) x ∈ (Z.1 : Set (Torus S.d (n (j + t))))
  rwa [cm_cubeMap H.F.hnn x t j hjt] at h2

end RegionHistory

end Balaban.LargeField
