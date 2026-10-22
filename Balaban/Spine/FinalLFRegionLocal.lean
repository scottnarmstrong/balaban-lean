/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.FinalLFKerLocal
public import Balaban.LargeField.R.LocalLemmas

/-!
# The region data of a history near a set of cubes are those of its components there (A6-4)

For a history without removals up to the scale `k`, the domains `Ω_{j+1}`, `Ω''_{j+1}` (`j < k`) and the
regions `Z_j` (`j ≤ k`) over a fine site `x` are those of the localized history of the component of
`Z_k` containing the cube of `x` (Lemma I.3.9 (b): `Ω^c ∩ Lin = Ω^c(loc)`; `Ω^c ⊆ Z^{(0)} ⊆ Z^pre`), and
over a site outside `Z_k` the site lies in `Ω_{j+1}`, `Ω''_{j+1}` and outside `Z_j`. Hence two such
histories whose components meeting a set `X` of cubes of `𝕋_k` correspond (the same cubes and the same
localized histories) have the same region data on the fine set of `X`
(`regionData_eq_on_of_corr`): the locality hypothesis of the boundary terms (`D7` `loc_hist`) for the
scales `j < k`, as needed for the decorated couplings of the record gas.

* `mem_Zpre_iff_mem_lin_of_rem`, `not_mem_Zpre_of_not_mem_Zp`;
* `mem_Omega_iff_loc`, `mem_OmegaDD_iff_loc`, `mem_Z_iff_loc`: over a component;
* `mem_Omega_of_not_mem_Zp`, `mem_OmegaDD_of_not_mem_Zp`, `not_mem_Z_of_not_mem_Zp`: off `Z_k`;
* **`regionData_eq_on_of_corr`**.
-/

@[expose] public section

open Balaban Balaban.LargeField Balaban.LargeField.Def7 RegionHistory

namespace Balaban.RootFSpine

section Single

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  (H : RegionHistory S n R k0 K) {k : ℕ} (hkK : k ≤ K) (hrem : ∀ i, i ≤ k → H.rem i = ∅)
include hkK hrem

/-- Over a component of `Z_k`, the cubes of `Z^pre_j` are those of the lineage. -/
theorem mem_Zpre_iff_mem_lin_of_rem {j : ℕ} (hjk : j ≤ k) (c : H.Comp k)
    (x : Torus S.d (M * n K * S.L ^ K)) (hx : cubeMap n S.L M K k x ∈ c.1) :
    cubeMap n S.L M K j x ∈ H.F.Zpre j ↔
      cubeMap n S.L M K j x ∈ ((H.lin j k c : Finset _) : Set (Torus S.d (n j))) := by
  rw [mem_lin_iff_of_rem_between hjk hkK (fun i _ hi => hrem i hi.le) c x]
  exact ⟨fun h => ⟨h, hx⟩, fun h => h.1⟩

/-- Off `Z_k`, no cube of `Z^pre_j` lies under the site. -/
theorem not_mem_Zpre_of_not_mem_Zp {j : ℕ} (hjk : j ≤ k) (x : Torus S.d (M * n K * S.L ^ K))
    (hx : cubeMap n S.L M K k x ∉ H.Zp k) : cubeMap n S.L M K j x ∉ H.F.Zpre j := fun h =>
  hx (mem_finOf.mpr (cubeMap_mem_Zpre_of_rem_between hjk hkK (fun i _ hi => hrem i hi.le) h))

/-- A cube of `Ω^c_{j+1}` or `Ω''^c_{j+1}` over a component lies in its lineage. -/
theorem mem_lin_of_mem_Z0 {j : ℕ} (hjk : j < k) (c : H.Comp k) (x : Torus S.d (M * n K * S.L ^ K))
    (hx : cubeMap n S.L M K k x ∈ c.1) (h : cubeMap n S.L M K (j + 1) x ∈ (H.step j).Z0) :
    cubeMap n S.L M K (j + 1) x ∈ ((H.lin (j + 1) k c : Finset _) : Set (Torus S.d (n (j + 1)))) :=
  (mem_Zpre_iff_mem_lin_of_rem H hkK hrem hjk c x hx).1
    ((H.step j).Z0_subset_Zpre (S.omega (j + 1)) (critOpt S k0 (j + 1)) h)

/-- `Ω_{j+1}` over a component is that of its localized history. -/
theorem mem_Omega_iff_loc {j : ℕ} (hjk : j < k) (c : H.Comp k) (x : Torus S.d (M * n K * S.L ^ K))
    (hx : cubeMap n S.L M K k x ∈ c.1) :
    cubeMap n S.L M K (j + 1) x ∈ (H.step j).Omega ↔
      cubeMap n S.L M K (j + 1) x ∈ ((H.locRH k c).step j).Omega := by
  obtain ⟨-, hΩ, -, -⟩ := locRH_derived c hjk (by omega)
  rw [← not_iff_not]
  change _ ∈ (H.step j).Omegaᶜ ↔ _ ∈ ((H.locRH k c).step j).Omegaᶜ
  rw [← hΩ]
  exact ⟨fun h => ⟨h, mem_lin_of_mem_Z0 H hkK hrem hjk c x hx ((H.step j).Omega_compl_subset_Z0 h)⟩,
    fun h => h.1⟩

/-- `Ω''_{j+1}` over a component is that of its localized history. -/
theorem mem_OmegaDD_iff_loc {j : ℕ} (hjk : j < k) (c : H.Comp k)
    (x : Torus S.d (M * n K * S.L ^ K)) (hx : cubeMap n S.L M K k x ∈ c.1) :
    cubeMap n S.L M K (j + 1) x ∈ (H.step j).OmegaDD ↔
      cubeMap n S.L M K (j + 1) x ∈ ((H.locRH k c).step j).OmegaDD := by
  obtain ⟨-, -, hDD, -⟩ := locRH_derived c hjk (by omega)
  rw [← not_iff_not]
  change _ ∈ (H.step j).OmegaDDᶜ ↔ _ ∈ ((H.locRH k c).step j).OmegaDDᶜ
  rw [← hDD]
  exact ⟨fun h => ⟨h, mem_lin_of_mem_Z0 H hkK hrem hjk c x hx
    ((H.step j).OmegaDD_compl_subset_Z0 h)⟩, fun h => h.1⟩

/-- `Z_j` over a component is that of its localized history. -/
theorem mem_Z_iff_loc {j : ℕ} (hjk : j ≤ k) (c : H.Comp k) (x : Torus S.d (M * n K * S.L ^ K))
    (hx : cubeMap n S.L M K k x ∈ c.1) :
    cubeMap n S.L M K j x ∈ (H.step j).Z ↔ cubeMap n S.L M K j x ∈ ((H.locRH k c).step j).Z := by
  rw [locRH_Z c hjk (by omega), ← mem_Zpre_iff_mem_lin_of_rem H hkK hrem hjk c x hx, H.Z_eq j,
    hrem j hjk]
  simp

/-- Off `Z_k`, the site lies in `Ω_{j+1}`. -/
theorem mem_Omega_of_not_mem_Zp {j : ℕ} (hjk : j < k) (x : Torus S.d (M * n K * S.L ^ K))
    (hx : cubeMap n S.L M K k x ∉ H.Zp k) : cubeMap n S.L M K (j + 1) x ∈ (H.step j).Omega := by
  by_contra h
  exact not_mem_Zpre_of_not_mem_Zp H hkK hrem (j := j + 1) (by omega) x hx
    ((H.step j).Z0_subset_Zpre _ _ ((H.step j).Omega_compl_subset_Z0 h))

/-- Off `Z_k`, the site lies in `Ω''_{j+1}`. -/
theorem mem_OmegaDD_of_not_mem_Zp {j : ℕ} (hjk : j < k) (x : Torus S.d (M * n K * S.L ^ K))
    (hx : cubeMap n S.L M K k x ∉ H.Zp k) : cubeMap n S.L M K (j + 1) x ∈ (H.step j).OmegaDD := by
  by_contra h
  exact not_mem_Zpre_of_not_mem_Zp H hkK hrem (j := j + 1) (by omega) x hx
    ((H.step j).Z0_subset_Zpre _ _ ((H.step j).OmegaDD_compl_subset_Z0 h))

/-- Off `Z_k`, the site lies outside `Z_j`. -/
theorem not_mem_Z_of_not_mem_Zp {j : ℕ} (hjk : j ≤ k) (x : Torus S.d (M * n K * S.L ^ K))
    (hx : cubeMap n S.L M K k x ∉ H.Zp k) : cubeMap n S.L M K j x ∉ (H.step j).Z := fun h =>
  not_mem_Zpre_of_not_mem_Zp H hkK hrem hjk x hx (H.Z_subset_Zpre j h)

end Single

section Two

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  {A B : RegionHistory S n R k0 K} {k : ℕ} (hkK : k ≤ K)
  (hA : ∀ i, i ≤ k → A.rem i = ∅) (hB : ∀ i, i ≤ k → B.rem i = ∅)
  {X : Finset (Torus S.d (n k))}
  (hAB : ∀ c : A.Comp k, (c.1 ∩ X).Nonempty → ∃ c' : B.Comp k, c'.1 = c.1 ∧
    B.localHistory M K k c' = A.localHistory M K k c)
  (hBA : ∀ c' : B.Comp k, (c'.1 ∩ X).Nonempty → ∃ c : A.Comp k, c.1 = c'.1 ∧
    A.localHistory M K k c = B.localHistory M K k c')
include hkK hA hB hAB hBA

omit [NeZero M] hkK hA hB in
/-- The component of the first history over a site of `X` (if any) corresponds to a component of
the second history over the same site, and conversely. -/
theorem cases_of_corr (x : Torus S.d (M * n K * S.L ^ K)) (hxX : cubeMap n S.L M K k x ∈ X) :
    (∃ (c : A.Comp k) (c' : B.Comp k), cubeMap n S.L M K k x ∈ c.1 ∧
        cubeMap n S.L M K k x ∈ c'.1 ∧ c'.1 = c.1 ∧
        B.localHistory M K k c' = A.localHistory M K k c) ∨
      (cubeMap n S.L M K k x ∉ A.Zp k ∧ cubeMap n S.L M K k x ∉ B.Zp k) := by
  by_cases hxA : cubeMap n S.L M K k x ∈ A.Zp k
  · obtain ⟨Y, hY, hyY⟩ := mem_comp_self (ω := S.omega k) hxA
    obtain ⟨c', hc'1, hc'2⟩ := hAB ⟨Y, hY⟩ ⟨_, Finset.mem_inter.2 ⟨hyY, hxX⟩⟩
    exact Or.inl ⟨⟨Y, hY⟩, c', hyY, hc'1 ▸ hyY, hc'1, hc'2⟩
  · refine Or.inr ⟨hxA, fun hxB => ?_⟩
    obtain ⟨Y', hY', hyY'⟩ := mem_comp_self (ω := S.omega k) hxB
    obtain ⟨c, hc1, -⟩ := hBA ⟨Y', hY'⟩ ⟨_, Finset.mem_inter.2 ⟨hyY', hxX⟩⟩
    exact hxA (comp_subset c.2 (hc1 ▸ hyY'))

/-- **The region data of two histories agree on the fine set of `X`** when their components meeting
`X` correspond: `Ω_j`, `Z_j` for `j ≤ k` and `Ω''_{j+1}` for `j < k` (the locality hypothesis of
the boundary terms below the scale `k`). -/
theorem regionData_eq_on_of_corr :
    (∀ j, j ≤ k →
      fineSet (S := S) (n := n) M K j (OmegaCube A j) ∩
          fineSet (S := S) (n := n) M K k (X : Set (Torus S.d (n k))) =
        fineSet (S := S) (n := n) M K j (OmegaCube B j) ∩
          fineSet (S := S) (n := n) M K k (X : Set (Torus S.d (n k))) ∧
      (globalLH A M).Z j ∩ fineSet (S := S) (n := n) M K k (X : Set (Torus S.d (n k))) =
        (globalLH B M).Z j ∩ fineSet (S := S) (n := n) M K k (X : Set (Torus S.d (n k)))) ∧
    ∀ j, j < k →
      (globalLH A M).OmegaDD j ∩ fineSet (S := S) (n := n) M K k (X : Set (Torus S.d (n k))) =
        (globalLH B M).OmegaDD j ∩ fineSet (S := S) (n := n) M K k (X : Set (Torus S.d (n k))) := by
  refine ⟨fun j hj => ⟨?_, ?_⟩, fun j hj => ?_⟩
  · ext x
    simp only [Set.mem_inter_iff]
    refine and_congr_left fun hxX => ?_
    cases j with
    | zero => exact Iff.rfl
    | succ j =>
      change cubeMap n S.L M K (j + 1) x ∈ (A.step j).Omega ↔
        cubeMap n S.L M K (j + 1) x ∈ (B.step j).Omega
      rcases cases_of_corr hAB hBA x hxX with ⟨c, c', hc, hc', h1, h2⟩ | ⟨hnA, hnB⟩
      · rw [mem_Omega_iff_loc A hkK hA (by omega) c x hc,
          mem_Omega_iff_loc B hkK hB (by omega) c' x hc',
          locRH_step_eq_of_localHistory_eq hkK c' c h1 h2 j]
      · exact iff_of_true (mem_Omega_of_not_mem_Zp A hkK hA (by omega) x hnA)
          (mem_Omega_of_not_mem_Zp B hkK hB (by omega) x hnB)
  · ext x
    simp only [Set.mem_inter_iff]
    refine and_congr_left fun hxX => ?_
    change cubeMap n S.L M K j x ∈ (A.step j).Z ↔ cubeMap n S.L M K j x ∈ (B.step j).Z
    rcases cases_of_corr hAB hBA x hxX with ⟨c, c', hc, hc', h1, h2⟩ | ⟨hnA, hnB⟩
    · rw [mem_Z_iff_loc A hkK hA hj c x hc, mem_Z_iff_loc B hkK hB hj c' x hc',
        locRH_step_eq_of_localHistory_eq hkK c' c h1 h2 j]
    · exact iff_of_false (not_mem_Z_of_not_mem_Zp A hkK hA hj x hnA)
        (not_mem_Z_of_not_mem_Zp B hkK hB hj x hnB)
  · ext x
    simp only [Set.mem_inter_iff]
    refine and_congr_left fun hxX => ?_
    change cubeMap n S.L M K (j + 1) x ∈ (A.step j).OmegaDD ↔
      cubeMap n S.L M K (j + 1) x ∈ (B.step j).OmegaDD
    rcases cases_of_corr hAB hBA x hxX with ⟨c, c', hc, hc', h1, h2⟩ | ⟨hnA, hnB⟩
    · rw [mem_OmegaDD_iff_loc A hkK hA hj c x hc, mem_OmegaDD_iff_loc B hkK hB hj c' x hc',
        locRH_step_eq_of_localHistory_eq hkK c' c h1 h2 j]
    · exact iff_of_true (mem_OmegaDD_of_not_mem_Zp A hkK hA hj x hnA)
        (mem_OmegaDD_of_not_mem_Zp B hkK hB hj x hnB)

end Two

end Balaban.RootFSpine
