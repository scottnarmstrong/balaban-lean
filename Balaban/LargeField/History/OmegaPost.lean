module

public import Balaban.LargeField.History.RegionHistory
public import Balaban.LargeField.Def7Hist
public import Balaban.LargeField.Region.Inclusions
public import Balaban.LargeField.Region.Generating

/-!
# The post-removal domain `Ω_k^post` (LF-RECONSTRUCTION Definition I.3.11)

The landed `Def7.OmegaCube H k` is the raw (pre-removal) domain: `Set.univ` for `k = 0` and
`(H.step (k-1)).Omega` for `k ≥ 1`.  After the operation `R^{(k)}` removes the components `Rem_k`
of `Z^pre_k`, Definition I.3.11 overwrites the small-field domain by adjoining the removed
components.  `notes/phase1/VMOD-20.md` §1 (1.1) and `VMOD-21.md` §3 show that the inclusion
needed by the boundary-term size estimate (P6 p. 34) holds only for the post-removal domain.

Dictionary (note -> landed): `Ω_k^pre` = `Def7.OmegaCube H k`; `Rem_k` = `H.rem k`;
`Z_k` = `(H.step k).Z`; `Z^pre_k` = `H.F.Zpre k`; the coarsening `p : T_k -> T_{k+1}` =
`blockMap S.L (n (k+1))`, and on the fine torus `cubeMap n S.L M K j`.  The step `H.step k` takes
`T_k` to `T_{k+1}`, so `(H.step k).Omega` is the pre-removal domain `Ω_{k+1}^pre`.

* `removedSet`, `omegaPost`: the union of the removed components and `Ω_k^post`.
* `omegaPost_compl_subset_Z`: `(Ω_k^post)ᶜ ⊆ Z_k`.
* `OmegaCube_subset_omegaPost`, `omegaPost_eq_OmegaCube_iff`: `Ω_k^post ⊇ Ω_k^pre`, with
  equality exactly when the removed set lies in the raw domain (in particular when `Rem_k = ∅`).
* `omegaNext_subset_post`, `omegaNext_subset_post_fine`: `p⁻¹(Ω_{k+1}^pre) ⊆ Ω_k^post`.
* `omegaPost_reset_eq_univ`: if the removed set is all of `Z^pre_k` then `Ω_k^post` is everything.
-/

@[expose] public section

namespace Balaban.LargeField.RegionHistory

open Balaban Balaban.LargeField

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}

/-- The union of the components removed by `R^{(k)}`. -/
def removedSet (H : RegionHistory S n R k0 K) (k : ℕ) : Set (Torus S.d (n k)) :=
  ⋃ c ∈ H.rem k, (c : Set (Torus S.d (n k)))

/-- The post-removal small-field domain `Ω_k^post = Ω_k^pre ∪ ⋃ Rem_k`
(Definition I.3.11), with `Ω_k^pre = Def7.OmegaCube H k`. -/
def omegaPost (H : RegionHistory S n R k0 K) (k : ℕ) : Set (Torus S.d (n k)) :=
  Def7.OmegaCube H k ∪ H.removedSet k

theorem mem_removedSet_iff (H : RegionHistory S n R k0 K) {k : ℕ} {x : Torus S.d (n k)} :
    x ∈ H.removedSet k ↔ ∃ c ∈ H.rem k, x ∈ c := by
  simp [removedSet]

theorem OmegaCube_subset_omegaPost (H : RegionHistory S n R k0 K) (k : ℕ) :
    Def7.OmegaCube H k ⊆ H.omegaPost k := Set.subset_union_left

theorem removedSet_subset_omegaPost (H : RegionHistory S n R k0 K) (k : ℕ) :
    H.removedSet k ⊆ H.omegaPost k := Set.subset_union_right

/-- The true relation to the raw domain: `Ω_k^post = Ω_k^pre` exactly when the removed set lies
in `Ω_k^pre`. -/
theorem omegaPost_eq_OmegaCube_iff (H : RegionHistory S n R k0 K) (k : ℕ) :
    H.omegaPost k = Def7.OmegaCube H k ↔ H.removedSet k ⊆ Def7.OmegaCube H k :=
  Set.union_eq_left

theorem omegaPost_eq_OmegaCube_of_rem_empty (H : RegionHistory S n R k0 K) {k : ℕ}
    (h : H.rem k = ∅) : H.omegaPost k = Def7.OmegaCube H k := by
  rw [omegaPost_eq_OmegaCube_iff]
  intro x hx
  obtain ⟨c, hc, -⟩ := H.mem_removedSet_iff.mp hx
  simp [h] at hc

/-- **`(Ω_k^post)ᶜ ⊆ Z_k`.** -/
theorem omegaPost_compl_subset_Z (H : RegionHistory S n R k0 K) (k : ℕ) :
    (H.omegaPost k)ᶜ ⊆ (H.step k).Z := by
  intro x hx
  rw [omegaPost, Set.mem_compl_iff, Set.mem_union, not_or] at hx
  obtain ⟨hx1, hx2⟩ := hx
  cases k with
  | zero => exact absurd (by simp [Def7.OmegaCube]) hx1
  | succ j =>
    rw [H.Z_eq]
    refine ⟨?_, hx2⟩
    exact ((H.step j).Z0_subset_Zpre _ _) ((H.step j).Omega_compl_subset_Z0 hx1)

/-- **Nesting**: a cube over `Ω_{k+1}^pre` belongs to `Ω_k^post`. -/
theorem omegaNext_subset_post (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k < K)
    (hL : 0 < S.L) {x : Torus S.d (n k)}
    (hx : blockMap S.L (n (k + 1)) x ∈ (H.step k).Omega) : x ∈ H.omegaPost k := by
  by_contra h
  exact (H.step k).not_mem_Z_of_mem_Omega hL (H.F.hnn k hk) hx
    (H.omegaPost_compl_subset_Z k h)

/-- The fine-torus version of `omegaNext_subset_post`. -/
theorem omegaNext_subset_post_fine (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K)
    (hL : 0 < S.L) [NeZero S.L] (M : ℕ) [NeZero M] (z : Torus S.d (M * n K * S.L ^ K))
    (hz : cubeMap n S.L M K (k + 1) z ∈ (H.step k).Omega) :
    cubeMap n S.L M K k z ∈ H.omegaPost k := by
  apply H.omegaNext_subset_post hk hL
  rw [cubeMap_succ H.F.hnn hk]
  exact hz

/-- If the removed set is all of `Z^pre_k`, the post-removal domain is the whole torus. -/
theorem omegaPost_reset_eq_univ (H : RegionHistory S n R k0 K) {k : ℕ}
    (hrem : H.removedSet k = H.F.Zpre k) : H.omegaPost k = Set.univ := by
  cases k with
  | zero => simp [omegaPost, Def7.OmegaCube]
  | succ j =>
    refine Set.eq_univ_of_forall fun x => ?_
    by_cases hx : x ∈ Def7.OmegaCube H (j + 1)
    · exact Or.inl hx
    · exact Or.inr (hrem ▸ ((H.step j).Z0_subset_Zpre _ _) ((H.step j).Omega_compl_subset_Z0 hx))

end Balaban.LargeField.RegionHistory
