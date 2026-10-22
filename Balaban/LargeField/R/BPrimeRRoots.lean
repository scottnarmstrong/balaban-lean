/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.BPrimeCubeRegion

/-!
# The roots of the residual of `R` and their P3 geometry

The residual `sfExp2At(Y₁) - sfExp2At(Y₂)` of the exponents of the old and the new small-field
region is the sum of the pair functionals of its roots (`sfExp2At_sub_eq_roots`): the cubes `c` of
`𝕋_k` (`cubePair`) and the polymers `X ∈ 𝒟_j`, `1 ≤ j < k` (`polyPair`), plus the terms of the top
level `k` (which read only the data), the vacuum terms and `ℛ^{(k)}`.  The roots are localized in the
whole-lattice generating set of the top level (`rLevelGS`): a cube is the local cube
`LocalCover.cube m₀ (k - 1)` of its corner with the chosen family `{corner}`, a polymer carries an
optimal chosen family.

* `RRoot`, `rRoots`, `rootLevel`, `rootX`, `rootFam`, `rootX₁`, `rootX₁f`, `rootIdx`, `rootPair`;
* `sum_rootPair`, `sfExp2At_sub_eq_rootPair`: the residual as the sum over the roots;
* `covSetup_root`, `hopt_root`: the P3 geometry of every root.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
  Balaban.SmallField.GsSpec

section Cast

theorem torusCast_add_of_eq {d a b : ℕ} [NeZero a] (h : a = b) (x y : Torus d a) :
    (GsSpec.torusCast (x + y) : Torus d b) = GsSpec.torusCast x + GsSpec.torusCast y := by
  subst h
  rw [torusCast_self', torusCast_self', torusCast_self']

theorem torusCast_single_of_eq {d a b : ℕ} [NeZero a] (h : a = b) (ν : Fin d) :
    (GsSpec.torusCast (Pi.single ν 1 : Torus d a) : Torus d b) = Pi.single ν 1 := by
  subst h
  rw [torusCast_self']

theorem intTorus_single {d m : ℕ} (ν : Fin d) :
    (intTorus (Pi.single ν (1 : ℤ)) : Torus d m) = Pi.single ν 1 := by
  funext μ
  rw [intTorus_apply]
  by_cases h : μ = ν
  · subst h; simp
  · simp [h]

end Cast

namespace Def7.SFCtx

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N k m₁ : ℕ} {ϱ : ℝ} (C : SFCtx S n R M K N k m₁ ϱ)

/-- The roots of the residual of `R`: the cubes of `𝕋_k` and the pairs `(j, X)`, `X ∈ 𝒟_j`. -/
abbrev RRoot : Type :=
  Torus S.d (n k) ⊕ (Σ _ : ℕ, Set (Localization.CTorus S.d S.L C.N₁ m₁ k))

open Classical in
/-- **The roots of the residual of `R`**: all cubes of `𝕋_k` and the polymers of `𝒟_j`,
`1 ≤ j ≤ k - 1`. -/
noncomputable def rRoots : Finset C.RRoot :=
  (Finset.univ.map Function.Embedding.inl) ∪
    (((Finset.Icc 1 (k - 1)).sigma fun j => Def7v2.polyIdx C j).map Function.Embedding.inr)

/-- The whole-lattice generating set of the top level `k` on the Def-6 torus, in which the roots
are localized. -/
noncomputable def rLevelGS : GeneratingSet S.d S.L (C.N₁ * S.L ^ m₁) k (1 : ℝ) :=
  Def6.levelGS k le_rfl

theorem isLevel_rLevelGS (hk1 : 1 ≤ k) : Fluctuation.IsLevel C.rLevelGS k :=
  Fluctuation.isLevel_levelGS hk1 le_rfl

/-- The level of a root: `k - 1` for a cube (one `π'_{k-1}`-cube), `j` for a polymer of `𝒟_j`. -/
def rootLevel : C.RRoot → ℕ
  | Sum.inl _ => k - 1
  | Sum.inr ⟨j, _⟩ => j

/-- The set of a root: the cube (the local cube of its corner), or the polymer. -/
def rootX : C.RRoot → Set (Localization.CTorus S.d S.L C.N₁ m₁ k)
  | Sum.inl c => LocalCover.cube C.m₀ (k - 1) (C.cubeCorner c)
  | Sum.inr ⟨_, X⟩ => X

open Classical in
/-- The chosen family of a root: `{corner}` for a cube, an optimal family for a polymer. -/
noncomputable def rootFam : C.RRoot → Set (Localization.CTorus S.d S.L C.N₁ m₁ k)
  | Sum.inl c => LocalCover.fam C.m₀ (C.cubeCorner c)
  | Sum.inr ⟨j, X⟩ => if h : Def6.IsPolyDom C.m₀ j X then
      (Fluctuation.exists_optimal_chosen h).choose else ∅

/-- The region `X₁` of a root. -/
noncomputable def rootX₁ (r : C.RRoot) : Set (Localization.CTorus S.d S.L C.N₁ m₁ k) :=
  X1 C.rLevelGS C.m₀ (C.rootLevel r) (C.rootFam r)

open Classical in
/-- The region `X₁` of a root as a finite set. -/
noncomputable def rootX₁f (r : C.RRoot) : Finset (Localization.CTorus S.d S.L C.N₁ m₁ k) :=
  Finset.univ.filter fun x => x ∈ C.rootX₁ r

theorem coe_rootX₁f (r : C.RRoot) : (↑(C.rootX₁f r) : Set _) = C.rootX₁ r := by
  ext x
  simp [rootX₁f]

/-- The labels of the cut parameters of a root. -/
abbrev rootIdx (r : C.RRoot) : Type := ↥(rootLabs C.rLevelGS (C.rootX₁ r))

variable (Y₁ Y₂ : Set (Torus S.d (n k))) (hv : EuclideanSpace ℝ (Fin N))
  (vc : Def7v2.CorrCoef S.d) (g : GIdx S n M K N → ℂ)

/-- **The pair functional of a root** (old minus new root). -/
noncomputable def rootPair : C.RRoot → (BlockAt S n M K k → Fin N → ℂ) →
    ((C.genWC Y₁).Ω 1 × Fin N → ℂ) → ((C.genWC Y₂).Ω 1 × Fin N → ℂ) → ℂ
  | Sum.inl c => C.cubePair hv Y₁ Y₂ vc g c
  | Sum.inr ⟨j, X⟩ => C.polyPair Y₁ Y₂ hv g j X

/-- **The sum of the pair functionals over the roots**: the cubes and the polymers of the levels
`1 ≤ j ≤ k - 1`. -/
theorem sum_rootPair (u : BlockAt S n M K k → Fin N → ℂ) (φ₁ : (C.genWC Y₁).Ω 1 × Fin N → ℂ)
    (φ₂ : (C.genWC Y₂).Ω 1 × Fin N → ℂ) :
    ∑ r ∈ C.rRoots, C.rootPair Y₁ Y₂ hv vc g r u φ₁ φ₂ =
      ∑ c, C.cubePair hv Y₁ Y₂ vc g c u φ₁ φ₂ +
        ∑ j ∈ Finset.Icc 1 (k - 1), ∑ X ∈ Def7v2.polyIdx C j, C.polyPair Y₁ Y₂ hv g j X u φ₁ φ₂ := by
  classical
  unfold rRoots
  rw [Finset.sum_union]
  · rw [Finset.sum_map, Finset.sum_map, Finset.sum_sigma]
    rfl
  · rw [Finset.disjoint_left]
    intro r h1 h2
    obtain ⟨c, -, rfl⟩ := Finset.mem_map.1 h1
    obtain ⟨p, -, hp⟩ := Finset.mem_map.1 h2
    cases hp

/-- **The residual of the exponents is the sum over the roots**, plus the terms of the top level
`k` (which read only the data), the vacuum terms and `ℛ^{(k)}`. -/
theorem sfExp2At_sub_eq_rootPair (hk1 : 1 ≤ k) (u : BlockAt S n M K k → Fin N → ℂ)
    (φ₁ : (C.genWC Y₁).Ω 1 × Fin N → ℂ) (φ₂ : (C.genWC Y₂).Ω 1 × Fin N → ℂ) :
    Def7v2.sfExp2At C vc Y₁ u hv g (castΩField C.coarseSide_eq (C.genW Y₁) φ₁) -
        Def7v2.sfExp2At C vc Y₂ u hv g (castΩField C.coarseSide_eq (C.genW Y₂) φ₂) =
      ∑ r ∈ C.rRoots, C.rootPair Y₁ Y₂ hv vc g r u φ₁ φ₂ +
        ∑ X ∈ Def7v2.polyIdx C k, C.polyPair Y₁ Y₂ hv g k X u φ₁ φ₂ -
        (((C.sf.E C.N₁ * volK M Y₁ : ℝ) : ℂ) - ((C.sf.E C.N₁ * volK M Y₂ : ℝ) : ℂ)) +
        (C.RresC Y₁ u hv g - C.RresC Y₂ u hv g) := by
  rw [Def7v2.sfExp2At_sub_eq_roots, sum_rootPair]
  have hIcc : Finset.Icc 1 k = insert k (Finset.Icc 1 (k - 1)) := by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have hk : k ∉ Finset.Icc 1 (k - 1) := by
    simp only [Finset.mem_Icc]
    omega
  rw [hIcc, Finset.sum_insert hk]
  unfold cubePair polyPair
  ring

/-- A polymer root is a polymer of `𝒟_j`, `1 ≤ j ≤ k - 1`. -/
theorem rRoots_inr {j : ℕ} {X : Set (Localization.CTorus S.d S.L C.N₁ m₁ k)}
    (hr : (Sum.inr ⟨j, X⟩ : C.RRoot) ∈ C.rRoots) :
    1 ≤ j ∧ j ≤ k - 1 ∧ Def6.IsPolyDom C.m₀ j X := by
  classical
  have hmem : (⟨j, X⟩ : Σ _ : ℕ, Set (Localization.CTorus S.d S.L C.N₁ m₁ k)) ∈
      (Finset.Icc 1 (k - 1)).sigma fun j => Def7v2.polyIdx C j := by
    rcases Finset.mem_union.1 hr with h | h
    · obtain ⟨c, -, hc⟩ := Finset.mem_map.1 h
      cases hc
    · obtain ⟨p, hp, hpe⟩ := Finset.mem_map.1 h
      cases hpe
      exact hp
  obtain ⟨hj, hX⟩ := Finset.mem_sigma.1 hmem
  have hX' : X ∈ Def7v2.polyIdx C j := hX
  unfold Def7v2.polyIdx at hX'
  have h2 := (Set.Finite.mem_toFinset _).1 hX'
  exact ⟨(Finset.mem_Icc.1 hj).1, (Finset.mem_Icc.1 hj).2, h2⟩

/-- **The P3 covering setup of every root** in the whole-lattice set of the top level. -/
theorem covSetup_root (hk1 : 1 ≤ k) (hN : S.L ^ C.m₀ ∣ C.N₁) (hL : 2 ≤ S.L) {r : C.RRoot}
    (hr : r ∈ C.rRoots) : CovSetup C.rLevelGS C.m₀ (C.rootLevel r) (C.rootX r) (C.rootFam r) := by
  classical
  rcases r with c | ⟨j, X⟩
  · show CovSetup C.rLevelGS C.m₀ (k - 1) (LocalCover.cube C.m₀ (k - 1) (C.cubeCorner c))
      (LocalCover.fam C.m₀ (C.cubeCorner c))
    exact LocalCover.covSetup (C.isLevel_rLevelGS hk1) hN (by omega) (C.cubeCorner c)
  · have hmem : (⟨j, X⟩ : Σ _ : ℕ, Set (Localization.CTorus S.d S.L C.N₁ m₁ k)) ∈
        (Finset.Icc 1 (k - 1)).sigma fun j => Def7v2.polyIdx C j := by
      rcases Finset.mem_union.1 hr with h | h
      · obtain ⟨c, -, hc⟩ := Finset.mem_map.1 h
        cases hc
      · obtain ⟨p, hp, hpe⟩ := Finset.mem_map.1 h
        cases hpe
        exact hp
    obtain ⟨hj, hX⟩ := Finset.mem_sigma.1 hmem
    have hX' : X ∈ Def7v2.polyIdx C j := hX
    unfold Def7v2.polyIdx at hX'
    have h2 := (Set.Finite.mem_toFinset _).1 hX'
    have hpoly : Def6.IsPolyDom C.m₀ j X := h2
    have hj' : j ≤ k - 1 := (Finset.mem_Icc.1 hj).2
    show CovSetup C.rLevelGS C.m₀ j X (if h : Def6.IsPolyDom C.m₀ j X then
      (Fluctuation.exists_optimal_chosen h).choose else ∅)
    simp only [hpoly, ↓reduceDIte]
    exact Fluctuation.covSetup_of_chosen (C.isLevel_rLevelGS hk1) hN (by omega) hL
      (Fluctuation.exists_optimal_chosen hpoly).choose_spec.choose_spec.choose_spec.1

/-- **The optimal connected structure of every root** (the premise `hopt`). -/
theorem hopt_root {r : C.RRoot} (hr : r ∈ C.rRoots) :
    ∃ (W₀ : Finset (Localization.CTorus S.d S.L C.N₁ m₁ k))
      (E₀ : Finset (Localization.CTorus S.d S.L C.N₁ m₁ k ×
        Localization.CTorus S.d S.L C.N₁ m₁ k)),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ C.rootX r) ∧ MeetsOne C.m₀ (C.rootLevel r) (C.rootFam r) W₀ ∧
        bondCost (scaleW S.L C.m₀ m₁ (C.rootLevel r)) E₀ =
          treeLenCovOne C.m₀ (C.rootLevel r) (C.rootX r) := by
  classical
  rcases r with c | ⟨j, X⟩
  · exact LocalCover.hopt (j := k - 1) C.m₀ (by omega) (C.cubeCorner c)
  · obtain ⟨-, -, hpoly⟩ := C.rRoots_inr hr
    show ∃ (W₀ : Finset (Localization.CTorus S.d S.L C.N₁ m₁ k))
      (E₀ : Finset (Localization.CTorus S.d S.L C.N₁ m₁ k ×
        Localization.CTorus S.d S.L C.N₁ m₁ k)),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X) ∧ MeetsOne C.m₀ j (if h : Def6.IsPolyDom C.m₀ j X then
        (Fluctuation.exists_optimal_chosen h).choose else ∅) W₀ ∧
        bondCost (scaleW S.L C.m₀ m₁ j) E₀ = treeLenCovOne C.m₀ j X
    simp only [hpoly, ↓reduceDIte]
    obtain ⟨W, E, -, h1, h2, h3, h4⟩ := (Fluctuation.exists_optimal_chosen hpoly).choose_spec
    exact ⟨W, E, h1, h2, h3, h4⟩

/-- **The covering size of a cube root is `0`.** -/
theorem treeLen_root_inl (c : Torus S.d (n k)) :
    treeLenCovOne C.m₀ (C.rootLevel (Sum.inl c)) (C.rootX (Sum.inl c)) = 0 :=
  LocalCover.treeLen_eq_zero (j := k - 1) C.m₀ (by omega) (C.cubeCorner c)

/-- **The region `X₁` of a root is closed under the `k`-blocks** (it is a union of cells). -/
theorem mem_rootX₁_of_sameCell (hN : S.L ^ C.m₀ ∣ C.N₁) (r : C.RRoot)
    {x y : Localization.CTorus S.d S.L C.N₁ m₁ k} (hx : x ∈ C.rootX₁ r)
    (hxy : SameCell (S.L ^ k) y x) : y ∈ C.rootX₁ r :=
  mem_X1_of_sameCell hN hx (hxy.mono (by unfold cellSide; exact pow_dvd_pow _ (by omega)))

/-- **The sites of a cube lie in the region of its root, with their `k`-blocks** (the premise `hA`
of `cubePair_loc`). -/
theorem cube_mem_rootX₁f (hk1 : 1 ≤ k) (hN : S.L ^ C.m₀ ∣ C.N₁) (hL : 2 ≤ S.L)
    (hMm : C.geo.c * C.geo.M1 = S.L ^ (C.m₀ + m₁)) (c : Torus S.d (n k)) :
    ∀ s, C.tCubeOfC s = c → ∀ y, SameCell (S.L ^ k) y s → y ∈ C.rootX₁f (Sum.inl c) := by
  intro s hs y hy
  have hsS : s ∈ C.rootX (Sum.inl c) := by
    show s ∈ LocalCover.cube C.m₀ (k - 1) (C.cubeCorner c)
    rw [← C.sset_singleton_eq hMm hk1 hN, C.tCubeOfC_cubeCorner, mem_sset_iff_cube]
    exact hs
  have hcov := C.covSetup_root hk1 hN hL (r := Sum.inl c) (Finset.mem_union_left _
    (Finset.mem_map_of_mem _ (Finset.mem_univ c)))
  have hsX := hcov.X_sub hsS
  rw [← Finset.mem_coe, C.coe_rootX₁f]
  exact C.mem_rootX₁_of_sameCell hN (Sum.inl c) hsX hy

/-- **The neighbours of the sites of a cube lie in the region of its root** (the premise `hAν` of
`cubePair_loc`). -/
theorem cube_nbr_mem_rootX₁f (hk1 : 1 ≤ k) (hN : S.L ^ C.m₀ ∣ C.N₁) (hL : 2 ≤ S.L)
    (hMm : C.geo.c * C.geo.M1 = S.L ^ (C.m₀ + m₁)) (c : Torus S.d (n k)) :
    ∀ (z : BgT C.geo k) (ν : Fin S.d), C.tCubeOfBg z = c →
      (GsSpec.torusCast (z + Pi.single ν 1) : Localization.CTorus S.d S.L C.N₁ m₁ k) ∈
        C.rootX₁f (Sum.inl c) := by
  intro z ν hz
  have hX : C.rootX₁ (Sum.inl c) = LocalCover.nbhd C.m₀ (C.cubeCorner c) :=
    LocalCover.X1_eq (C.isLevel_rLevelGS hk1) hN (j := k - 1) (by omega) (C.cubeCorner c)
  have hcell : S.L * cellSide S.L C.m₀ m₁ (k - 1) = cellSide S.L C.m₀ m₁ k := by
    unfold cellSide; rw [← pow_succ']; congr 1; omega
  have hx : (GsSpec.torusCast z : Localization.CTorus S.d S.L C.N₁ m₁ k) ∈
      Localization.box (LocalCover.corner C.m₀ (C.cubeCorner c)) (cellSide S.L C.m₀ m₁ k) := by
    have h1 : (GsSpec.torusCast z : Localization.CTorus S.d S.L C.N₁ m₁ k) ∈
        LocalCover.cube C.m₀ (k - 1) (C.cubeCorner c) := by
      rw [← C.sset_singleton_eq hMm hk1 hN, C.tCubeOfC_cubeCorner, mem_sset_iff_cube,
        C.tCubeOfC_torusCast]
      exact hz
    unfold LocalCover.cube at h1
    rwa [hcell] at h1
  have e : (GsSpec.torusCast (z + Pi.single ν 1) : Localization.CTorus S.d S.L C.N₁ m₁ k) =
      GsSpec.torusCast z + (intTorus (Pi.single ν (1 : ℤ)) : Localization.CTorus S.d S.L C.N₁ m₁ k) := by
    rw [torusCast_add_of_eq C.hT.symm, torusCast_single_of_eq C.hT.symm, intTorus_single]
  rw [← Finset.mem_coe, C.coe_rootX₁f, hX, e]
  refine add_intTorus_mem_cellNbhd (by omega) hx _ fun μ => ?_
  have h1 : |(Pi.single ν (1 : ℤ) : Fin S.d → ℤ) μ| ≤ 1 := by
    by_cases h : μ = ν
    · subst h; simp
    · simp [h]
  have h2 : (1 : ℤ) ≤ (((S.L - 1) * cellSide S.L C.m₀ m₁ k : ℕ) : ℤ) := by
    have := cellSide_pos (L := S.L) (m₁ := m₁) C.m₀ k
    have h3 : 1 ≤ (S.L - 1) * cellSide S.L C.m₀ m₁ k := Nat.one_le_iff_ne_zero.2
      (Nat.mul_ne_zero (by omega) (by omega))
    exact_mod_cast h3
  linarith

end Def7.SFCtx

end Balaban.LargeField
