module

public import Balaban.LargeField.Background.StepGenSets
public import Balaban.LargeField.Region.Locality
public import Balaban.LargeField.Geometry.LocalGlobal
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The generating sets of a step in the region calculus (Part II, Lemma II.2.5)

Let `st` be the step `k → k+1` of the region calculus (`RegionStep d L n0 n1 Rprev Rk`,
`n0 = L n1`), `M = c M1` the cube factor, and `T = Torus d (M1 (c n1) L^(k+1))` the level-`k+1`
fine torus; a cube of `𝕋_k` (`𝕋_{k+1}`) is a fibre of `blockMap (L^k (c M1)) n0`
(`blockMap (L^(k+1) (c M1)) n1`), `fineK`, `fineK1` turn sets of cubes into fine sets. With
`W_k = (Z_k^c)^{≈2}`, `U_{k+1} = (Z^pre_{k+1})^≈`, `Ω_{k+1}` and, for a component `Z'` of
`Z^pre_{k+1}`, `U_{Z'} = Z'^≈`:

* `boundaryHyp_flow`: the global family `G^∂_{k+1}` of Definition II.2.4 (iv) is a generating set
  (Lemma II.2.5 (a));
* `boundaryHyp_local`: the same for the local family `G^{Z'}_{k+1}` of (v).
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale

set_option linter.unusedSectionVars false

variable {d M1 c n1 L k n0 : ℕ} [NeZero L] [NeZero M1] [NeZero c] [NeZero n0] [NeZero n1]

/-! ### Fine sets of sets of cubes -/

section Fine

variable (M1 c n1 L k)

/-- The fine set of a set of `π_k`-cubes (`𝕋_k = Torus d n0`) on the level-`(k+1)` torus. -/
noncomputable def fineK (n0 : ℕ) (A : Set (Torus d n0)) :
    Finset (Torus d (M1 * (c * n1) * L ^ (k + 1))) :=
  cubePre M1 (c * n1) L (k + 1) (L ^ k * (c * M1)) n0 A

/-- The fine set of a set of `π_{k+1}`-cubes (`𝕋_{k+1} = Torus d n1`). -/
noncomputable def fineK1 (A : Set (Torus d n1)) :
    Finset (Torus d (M1 * (c * n1) * L ^ (k + 1))) :=
  cubePre M1 (c * n1) L (k + 1) (L ^ (k + 1) * (c * M1)) n1 A

variable {M1 c n1 L k}

theorem mem_fineK {A : Set (Torus d n0)} {x : Torus d (M1 * (c * n1) * L ^ (k + 1))} :
    x ∈ fineK M1 c n1 L k n0 A ↔ blockMap (L ^ k * (c * M1)) n0 x ∈ A := mem_cubePre

theorem mem_fineK1 {A : Set (Torus d n1)} {x : Torus d (M1 * (c * n1) * L ^ (k + 1))} :
    x ∈ fineK1 M1 c n1 L k A ↔ blockMap (L ^ (k + 1) * (c * M1)) n1 x ∈ A := mem_cubePre

theorem isCubeUnion_fineK1 (A : Set (Torus d n1)) :
    IsCubeUnion M1 (c * n1) L (k + 1) (k + 1) (fineK1 M1 c n1 L k A) :=
  isCubeUnion_cubePre (le_refl _) (by simp) A

theorem isCubeUnion_fineK (hn : n0 = L * n1) (A : Set (Torus d n0)) :
    IsCubeUnion M1 (c * n1) L (k + 1) k (fineK M1 c n1 L k n0 A) :=
  isCubeUnion_cubePre (Nat.le_succ k) (by rw [hn, show k + 1 - k = 1 by omega, pow_one]; ring) A

/-- The `π_{k+1}`-cube of a site is the coarsening of its `π_k`-cube. -/
theorem blockMap_k_succ (hn : n0 = L * n1) (x : Torus d (M1 * (c * n1) * L ^ (k + 1))) :
    blockMap L n1 (blockMap (L ^ k * (c * M1)) n0 x) = blockMap (L ^ (k + 1) * (c * M1)) n1 x := by
  have hℓ : M1 * (c * n1) * L ^ (k + 1) = (L ^ k * (c * M1)) * n0 := by rw [hn]; ring
  rw [blockMap_comp hℓ hn]
  congr 1; ring

/-- Coarse distance of cubes gives fine `ℓ¹` distance. -/
theorem torusDist_ge_of_cubes {P m : ℕ} [NeZero m]
    (hP : M1 * (c * n1) * L ^ (k + 1) = P * m) (hPpos : 0 < P)
    {x y : Torus d (M1 * (c * n1) * L ^ (k + 1))} {t : ℕ}
    (h : t ≤ supDist (blockMap P m x) (blockMap P m y)) :
    (P : ℝ) * t + 1 ≤ Green.torusDist d (M1 * (c * n1) * L ^ (k + 1)) x y + P := by
  have h1 := torusDist_lower (d := d) hP hPpos x y
  have h2 : (P : ℝ) * t ≤ (P : ℝ) * supDist (blockMap P m x) (blockMap P m y) :=
    mul_le_mul_of_nonneg_left (by exact_mod_cast h) (Nat.cast_nonneg _)
  linarith

end Fine

/-! ### The flow sets and their separation -/

section Flow

variable (M1 c n1 L k)

/-- `W_k = (Z_k^c)^{≈2}` as a fine set (scale `k`; `ρ' = ⌊R_{k-1}⌋`, `≈` adds `ρ' + 1`). -/
noncomputable def stepW (ρ' : ℕ) (Z : Set (Torus d n0)) :
    Finset (Torus d (M1 * (c * n1) * L ^ (k + 1))) :=
  fineK M1 c n1 L k n0 (thick2 ρ' Zᶜ)

/-- `U = Zp^≈` as a fine set (scale `k+1`; `ρ = ⌊R_k⌋`, `≈` adds `ρ + 1`); `Zp = Z^pre_{k+1}`
or a component of it. -/
noncomputable def stepU (ρ : ℕ) (Zp : Set (Torus d n1)) :
    Finset (Torus d (M1 * (c * n1) * L ^ (k + 1))) :=
  fineK1 M1 c n1 L k (thick ρ Zp)

variable {M1 c n1 L k}

theorem minSep_pow_lt_P1 (hc : 6 ≤ c) :
    minSep L M1 * (L : ℝ) ^ k < ((L ^ (k + 1) * (c * M1) : ℕ) : ℝ) := by
  unfold minSep
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hM : (0 : ℝ) < M1 := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M1)
  have hc' : (6 : ℝ) ≤ c := by exact_mod_cast hc
  have hp : (0 : ℝ) < (L : ℝ) ^ k * L * M1 := by positivity
  have h6 := mul_le_mul_of_nonneg_right hc' hp.le
  push_cast
  rw [pow_succ]
  nlinarith

theorem minSep_pow_lt_P0 {ρ : ℕ} (hρ : 3 * L ≤ ρ) :
    minSep L M1 * (L : ℝ) ^ k <
      ((L ^ k * (c * M1) : ℕ) : ℝ) * ((2 * ρ + 2 : ℕ) : ℝ) := by
  unfold minSep
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hM : (0 : ℝ) < M1 := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M1)
  have hc1 : (1 : ℝ) ≤ c := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne c)
  have hρ' : (3 : ℝ) * L ≤ ρ := by exact_mod_cast hρ
  have hp : (0 : ℝ) < (L : ℝ) ^ k * M1 := by positivity
  have h1 := mul_le_mul_of_nonneg_right hc1 hp.le
  have h2 := mul_le_mul_of_nonneg_left (show (6 : ℝ) * L + 2 ≤ 2 * ρ + 2 by linarith) (mul_nonneg hp.le (by linarith : (0 : ℝ) ≤ c))
  push_cast
  nlinarith

variable {Rprev Rk : ℝ} (st : RegionStep d L n0 n1 Rprev Rk)

/-- **Separation from `U`** (Lemma II.2.5 (a), (iv)): a site `x` whose `π_{k+1}`-cube is outside
`S^≈ = S^{∼(ρ+1)}` is far from every site `y` whose `π_{k+1}`-cube lies in `S`. -/
theorem far_U (hc : 6 ≤ c) (ρ : ℕ) (S : Set (Torus d n1))
    {x y : Torus d (M1 * (c * n1) * L ^ (k + 1))}
    (hxU : x ∉ stepU M1 c n1 L k ρ S)
    (hy : blockMap (L ^ (k + 1) * (c * M1)) n1 y ∈ S) :
    minSep L M1 * (L : ℝ) ^ k < Green.torusDist d (M1 * (c * n1) * L ^ (k + 1)) x y := by
  have hP : M1 * (c * n1) * L ^ (k + 1) = (L ^ (k + 1) * (c * M1)) * n1 := by ring
  have hPpos : 0 < L ^ (k + 1) * (c * M1) := Nat.pos_of_ne_zero (by
    have := NeZero.ne L; have := NeZero.ne M1; have := NeZero.ne c; positivity)
  unfold stepU at hxU
  rw [mem_fineK1] at hxU
  have ht : ρ + 2 ≤ supDist (blockMap (L ^ (k + 1) * (c * M1)) n1 x)
      (blockMap (L ^ (k + 1) * (c * M1)) n1 y) := by
    by_contra hlt
    push Not at hlt
    exact hxU (mem_nbhd.2 ⟨_, hy, by omega⟩)
  have h := torusDist_ge_of_cubes (M1 := M1) (c := c) (n1 := n1) (L := L) (k := k) hP hPpos
    (x := x) (y := y) ht
  have h2 := minSep_pow_lt_P1 (M1 := M1) (L := L) (k := k) (c := c) hc
  have h3 : (0 : ℝ) ≤ ρ := Nat.cast_nonneg _
  push_cast at h h2
  have h4 : (0 : ℝ) ≤ (L : ℝ) ^ (k + 1) * ((c : ℝ) * M1) := by positivity
  nlinarith [h, h2, mul_nonneg h3 h4]

/-- **Separation from `W`** (Lemma II.2.5 (a), (iv)): a site outside `W_k` is far from every site
of `Ω_{k+1}` (Lemma I.3.5 (f)). -/
theorem far_W (hn : n0 = L * n1) (hL : 0 < L) (hρ : 3 * L ≤ ⌊Rprev⌋₊)
    {x y : Torus d (M1 * (c * n1) * L ^ (k + 1))}
    (hx : x ∉ stepW M1 c n1 L k ⌊Rprev⌋₊ st.Z) (hy : y ∈ fineK1 M1 c n1 L k st.Omega) :
    minSep L M1 * (L : ℝ) ^ k < Green.torusDist d (M1 * (c * n1) * L ^ (k + 1)) x y := by
  have hP : M1 * (c * n1) * L ^ (k + 1) = (L ^ k * (c * M1)) * n0 := by rw [hn]; ring
  have hPpos : 0 < L ^ k * (c * M1) := Nat.pos_of_ne_zero (by
    have := NeZero.ne L; have := NeZero.ne M1; have := NeZero.ne c; positivity)
  unfold stepW at hx
  rw [mem_fineK1] at hy
  rw [mem_fineK] at hx
  have hy' : blockMap L n1 (blockMap (L ^ k * (c * M1)) n0 y) ∈ st.Omega := by
    rw [blockMap_k_succ hn]; exact hy
  have hbZ : blockMap (L ^ k * (c * M1)) n0 y ∉ st.Z := st.not_mem_Z_of_mem_Omega hL hn hy'
  have ht : 2 * ⌊Rprev⌋₊ + 3 ≤ supDist (blockMap (L ^ k * (c * M1)) n0 x)
      (blockMap (L ^ k * (c * M1)) n0 y) := by
    by_contra hlt
    push Not at hlt
    apply hx
    rw [thick2_eq]
    exact mem_nbhd.2 ⟨_, hbZ, by omega⟩
  have h := torusDist_ge_of_cubes (M1 := M1) (c := c) (n1 := n1) (L := L) (k := k) hP hPpos
    (x := x) (y := y) ht
  have h2 := minSep_pow_lt_P0 (M1 := M1) (L := L) (k := k) (c := c) hρ
  push_cast at h h2
  nlinarith [h, h2]

/-- **Lemma II.2.5 (a), (iv)**: the hypotheses of `boundaryGenSet` hold for the global family
`G^∂_{k+1}` of the region calculus (`Zp ⊇ Ω_{k+1}ᶜ`, e.g. `Z^pre_{k+1}`). -/
theorem boundaryHyp_flow (hc : 6 ≤ c) (hn : n0 = L * n1) (hL : 0 < L) (hρ : 3 * L ≤ ⌊Rprev⌋₊)
    {Zp : Set (Torus d n1)} (hZ : st.Omegaᶜ ⊆ Zp) :
    BoundaryHyp M1 (c * n1) L k (stepW M1 c n1 L k ⌊Rprev⌋₊ st.Z) (stepU M1 c n1 L k ⌊Rk⌋₊ Zp)
      (fineK1 M1 c n1 L k st.Omega) where
  omBlock := (isCubeUnion_fineK1 st.Omega).isBlockUnion (le_refl _)
  wUnion := isCubeUnion_fineK hn _
  uUnion := isCubeUnion_fineK1 _
  far₁ := by
    intro x _ hxU y _ hy
    refine far_U hc _ Zp hxU ?_
    rw [mem_fineK1] at hy
    exact hZ hy
  far₂ := by
    intro x _ hxW y hy
    exact far_W st hn hL hρ hxW (Finset.mem_inter.1 hy).1

/-! ### The local family of a component -/

section Local

variable {ω : ℕ} {Zp : Set (Torus d n1)} {Z' : Finset (Torus d n1)}

variable (M1 c n1 L k) in
/-- The local `W`: `W_k ∩ U_{Z'}` (Definition II.2.4 (v)). -/
noncomputable def stepWLoc (ρ' ρ : ℕ) (Z : Set (Torus d n0))
    (Z' : Set (Torus d n1)) : Finset (Torus d (M1 * (c * n1) * L ^ (k + 1))) :=
  stepW M1 c n1 L k ρ' Z ∩ stepU M1 c n1 L k ρ Z'

theorem isCubeUnion_stepWLoc (hn : n0 = L * n1) (ρ' ρ : ℕ) (Z : Set (Torus d n0))
    (Z' : Set (Torus d n1)) :
    IsCubeUnion M1 (c * n1) L (k + 1) k (stepWLoc M1 c n1 L k ρ' ρ Z Z') :=
  (isCubeUnion_fineK hn _).inter ((isCubeUnion_fineK1 _).of_le (Nat.le_succ k) le_rfl)

theorem eleven_le_P1 (hc : 11 ≤ c) {j : ℕ} (hj : j ≤ k + 1) :
    11 * M1 * L ^ j ≤ L ^ (k + 1) * (c * M1) := by
  have hL : 1 ≤ L := Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  calc 11 * M1 * L ^ j ≤ 11 * M1 * L ^ (k + 1) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hL hj)
    _ ≤ (c * M1) * L ^ (k + 1) := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hc)
    _ = L ^ (k + 1) * (c * M1) := by ring

/-- Sites within `P1` of each other lie in the same or adjacent `π_{k+1}`-cubes. -/
theorem cubes_close {x y : Torus d (M1 * (c * n1) * L ^ (k + 1))} {D : ℕ}
    (hD : D ≤ L ^ (k + 1) * (c * M1)) (h : supDist x y ≤ D) :
    supDist (blockMap (L ^ (k + 1) * (c * M1)) n1 x) (blockMap (L ^ (k + 1) * (c * M1)) n1 y)
      ≤ 1 :=
  supDist_blockMap_le_one (by ring) hD x y h

/-- If `y` is within `D ≤ P1` of a site whose cube is in `S^≈`, the cube of `y` is within `ρ + 2`
of `S`. -/
theorem cube_near {ρ D : ℕ} (S : Set (Torus d n1))
    (hD : D ≤ L ^ (k + 1) * (c * M1)) {y u : Torus d (M1 * (c * n1) * L ^ (k + 1))}
    (hyu : supDist y u ≤ D) (hu : blockMap (L ^ (k + 1) * (c * M1)) n1 u ∈ thick ρ S) :
    ∃ z ∈ S, supDist (blockMap (L ^ (k + 1) * (c * M1)) n1 y) z ≤ ρ + 2 := by
  obtain ⟨z, hz, hdz⟩ := mem_nbhd.1 hu
  have h1 := cubes_close (M1 := M1) (c := c) (n1 := n1) (L := L) (k := k) hD hyu
  have h2 := supDist_triangle (blockMap (L ^ (k + 1) * (c * M1)) n1 y)
    (blockMap (L ^ (k + 1) * (c * M1)) n1 u) z
  exact ⟨z, hz, by omega⟩

variable (st : RegionStep d L n0 n1 Rprev Rk)

/-- **Lemma II.2.5 (a), (v)**: the hypotheses of `boundaryGenSet` hold for the local family
`G^{Z'}_{k+1}` of a component `Z'` of `Z^pre_{k+1}` (width `ω ≥ 2⌊R_k⌋ + L + 11`). -/
theorem boundaryHyp_local (hc : 14 ≤ c) (hn : n0 = L * n1) (hL : 2 ≤ L)
    (hρ : 3 * L ≤ ⌊Rprev⌋₊) (hω : 2 * ⌊Rk⌋₊ + L + 11 ≤ ω)
    (hZ : st.Omegaᶜ ⊆ Zp) (hZ' : Z' ∈ comps ω (finOf Zp)) :
    BoundaryHyp M1 (c * n1) L k
      (stepWLoc M1 c n1 L k ⌊Rprev⌋₊ ⌊Rk⌋₊ st.Z (Z' : Set (Torus d n1)))
      (stepU M1 c n1 L k ⌊Rk⌋₊ (Z' : Set (Torus d n1))) (fineK1 M1 c n1 L k st.Omega) where
  omBlock := (isCubeUnion_fineK1 st.Omega).isBlockUnion (le_refl _)
  wUnion := isCubeUnion_stepWLoc hn _ _ _ _
  uUnion := isCubeUnion_fineK1 _
  far₁ := by
    intro x _ hxU y hyW hyOm
    have hk : 1 ≤ k := by
      by_contra h
      rw [minLayer_of_gt _ (by omega : k < 1)] at hyW
      exact absurd hyW (Finset.notMem_empty _)
    obtain ⟨w, hwW, hyw⟩ := exists_near_of_mem_minLayer' _ hL (Nat.le_succ k) hk hyW
    have hwU := (Finset.mem_inter.1 hwW).2
    unfold stepU at hwU
    rw [mem_fineK1] at hwU
    obtain ⟨z, hz, hdz⟩ := cube_near (k := k) (c := c) (M1 := M1) (n1 := n1) (L := L)
      (Z' : Set (Torus d n1)) (eleven_le_P1 (by omega) (Nat.le_succ k)) hyw hwU
    have hq : blockMap (L ^ (k + 1) * (c * M1)) n1 y ∈ Zp := by
      rw [mem_fineK1] at hyOm
      exact hZ hyOm
    have hqZ' : blockMap (L ^ (k + 1) * (c * M1)) n1 y ∈ (Z' : Set (Torus d n1)) := by
      refine mem_comp_of_close hZ' (Finset.mem_coe.1 hz) (mem_finOf.2 hq) ?_
      rw [supDist_comm]
      omega
    exact far_U (by omega) _ _ hxU hqZ'
  far₂ := by
    intro x hxOm hxW y hy
    have hL0 : 0 < L := by omega
    by_cases hxWk : x ∈ stepW M1 c n1 L k ⌊Rprev⌋₊ st.Z
    · have hxU : x ∉ stepU M1 c n1 L k ⌊Rk⌋₊ (Z' : Set (Torus d n1)) := fun h =>
        hxW (Finset.mem_inter.2 ⟨hxWk, h⟩)
      obtain ⟨hyOm, hyU⟩ := Finset.mem_inter.1 hy
      obtain ⟨u, huU, hyu⟩ := exists_near_of_mem_minLayer' _ hL le_rfl (by omega : 1 ≤ k + 1) hyU
      have hu := huU
      unfold stepU at hu
      rw [mem_fineK1] at hu
      obtain ⟨z, hz, hdz⟩ := cube_near (k := k) (c := c) (M1 := M1) (n1 := n1) (L := L)
        (Z' : Set (Torus d n1)) (eleven_le_P1 (by omega) le_rfl) hyu hu
      have hs : blockMap (L ^ (k + 1) * (c * M1)) n1 x ∈ Zp := by
        rw [mem_fineK1] at hxOm
        exact hZ hxOm
      have ht : 2 ≤ supDist (blockMap (L ^ (k + 1) * (c * M1)) n1 x)
          (blockMap (L ^ (k + 1) * (c * M1)) n1 y) := by
        by_contra hlt
        push Not at hlt
        have hsZ' : blockMap (L ^ (k + 1) * (c * M1)) n1 x ∈ Z' := by
          refine mem_comp_of_close hZ' (Finset.mem_coe.1 hz) (mem_finOf.2 hs) ?_
          have h3 := supDist_triangle (blockMap (L ^ (k + 1) * (c * M1)) n1 x)
            (blockMap (L ^ (k + 1) * (c * M1)) n1 y) z
          rw [supDist_comm z]
          omega
        apply hxU
        unfold stepU
        rw [mem_fineK1]
        exact subset_nbhd _ _ (Finset.mem_coe.2 hsZ')
      have hP : M1 * (c * n1) * L ^ (k + 1) = (L ^ (k + 1) * (c * M1)) * n1 := by ring
      have hPpos : 0 < L ^ (k + 1) * (c * M1) := Nat.pos_of_ne_zero (by
        have := NeZero.ne L; have := NeZero.ne M1; have := NeZero.ne c; positivity)
      have h := torusDist_ge_of_cubes (M1 := M1) (c := c) (n1 := n1) (L := L) (k := k) hP hPpos
        (x := x) (y := y) ht
      have h2 := minSep_pow_lt_P1 (M1 := M1) (L := L) (k := k) (c := c) (by omega)
      push_cast at h h2
      linarith
    · exact far_W st hn hL0 hρ hxWk (Finset.mem_inter.1 hy).1

theorem eleven_add_one_le_P1 (hc : 14 ≤ c) {j : ℕ} (hj : j ≤ k + 1) :
    11 * M1 * L ^ j + 1 ≤ L ^ (k + 1) * (c * M1) := by
  have hL : 1 ≤ L := Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hB : 1 ≤ M1 * L ^ j := Nat.one_le_iff_ne_zero.2 (by
    have := NeZero.ne L; have := NeZero.ne M1; positivity)
  calc 11 * M1 * L ^ j + 1 ≤ 14 * M1 * L ^ j := by
        have : 14 * M1 * L ^ j = 11 * M1 * L ^ j + 3 * (M1 * L ^ j) := by ring
        omega
    _ ≤ 14 * M1 * L ^ (k + 1) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hL hj)
    _ ≤ (c * M1) * L ^ (k + 1) := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hc)
    _ = L ^ (k + 1) * (c * M1) := by ring

variable (hc : 14 ≤ c) (hn : n0 = L * n1) (hL : 2 ≤ L) (hρ : 3 * L ≤ ⌊Rprev⌋₊)
  (hω : 2 * ⌊Rk⌋₊ + L + 11 ≤ ω) (hZ : st.Omegaᶜ ⊆ Zp) (hZ' : Z' ∈ comps ω (finOf Zp))

variable (M1 c n1 L k) in
/-- **Definition II.2.4 (iv)**: the global boundary family `G^∂_{k+1}` of the region calculus,
with `Ω_n = (Ω_n(W_k) ∖ Ω_{k+1}) ∪ (Ω_n(U_{k+1}) ∩ Ω_{k+1})`, `W_k = (Z_k^c)^{≈2}`,
`U_{k+1} = (Z^pre_{k+1})^≈` (here `Zp = Z^pre_{k+1}`, any set containing `Ω_{k+1}ᶜ`). -/
noncomputable def genBoundary (hc : 14 ≤ c) (hn : n0 = L * n1) (hL : 2 ≤ L)
    (hρ : 3 * L ≤ ⌊Rprev⌋₊) (hZ : st.Omegaᶜ ⊆ Zp) :
    Multiscale.GeneratingSet d L (M1 * (c * n1)) (k + 1) (minSep L M1) :=
  boundaryGenSet _ _ _ (boundaryHyp_flow st (le_trans (by norm_num) hc) hn
    (lt_of_lt_of_le (by norm_num) hL) hρ hZ)

variable (M1 c n1 L k) in
/-- **Definition II.2.4 (v)**: the local boundary family `G^{Z'}_{k+1}` of a component `Z'` of
`Z^pre_{k+1}` (`W_k` replaced by `W_k ∩ U_{Z'}` and `U_{k+1}` by `U_{Z'} = Z'^≈`). -/
noncomputable def genBoundaryLocal (hc : 14 ≤ c) (hn : n0 = L * n1) (hL : 2 ≤ L)
    (hρ : 3 * L ≤ ⌊Rprev⌋₊) (hω : 2 * ⌊Rk⌋₊ + L + 11 ≤ ω) (hZ : st.Omegaᶜ ⊆ Zp)
    (hZ' : Z' ∈ comps ω (finOf Zp)) :
    Multiscale.GeneratingSet d L (M1 * (c * n1)) (k + 1) (minSep L M1) :=
  boundaryGenSet _ _ _ (boundaryHyp_local st hc hn hL hρ hω hZ hZ')

include hc hL in
/-- Every data site of the local family lies within `11 M1 L^{k+1} + 1` of a site of `U_{Z'}`. -/
theorem genBoundaryLocal_near {u : Torus d (M1 * (c * n1) * L ^ (k + 1))}
    (hu : u ∈ Background.dataSites (genBoundaryLocal M1 c n1 L k st hc hn hL hρ hω hZ hZ')) :
    ∃ v ∈ stepU M1 c n1 L k ⌊Rk⌋₊ (Z' : Set (Torus d n1)),
      supDist u v ≤ 11 * M1 * L ^ (k + 1) + 1 := by
  have hΩ : ∀ z ∈ (genBoundaryLocal M1 c n1 L k st hc hn hL hρ hω hZ hZ').Ω 1,
      ∃ v ∈ stepU M1 c n1 L k ⌊Rk⌋₊ (Z' : Set (Torus d n1)),
        supDist z v ≤ 11 * M1 * L ^ (k + 1) := by
    intro z hz
    unfold genBoundaryLocal at hz
    rw [boundaryGenSet_Ω] at hz
    simp only [boundaryLayer, Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter] at hz
    rcases hz with ⟨hzW, -⟩ | ⟨hzU, -⟩
    · have hk : 1 ≤ k := by
        by_contra h
        rw [minLayer_of_gt _ (by omega : k < 1)] at hzW
        exact absurd hzW (Finset.notMem_empty _)
      obtain ⟨w, hwW, hzw⟩ := exists_near_of_mem_minLayer' _ hL (Nat.le_succ k) hk hzW
      refine ⟨w, (Finset.mem_inter.1 hwW).2, hzw.trans ?_⟩
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (Nat.le_succ k))
    · exact exists_near_of_mem_minLayer' _ hL le_rfl (by omega) hzU
  rcases (Background.mem_dataSites _).1 hu with h | h
  · obtain ⟨v, hv, hd⟩ := hΩ u h
    exact ⟨v, hv, by omega⟩
  · obtain ⟨-, x', hx', hadj⟩ := (Background.mem_collar _).1 h
    obtain ⟨v, hv, hd⟩ := hΩ x' hx'
    have h1 : supDist u x' ≤ 1 := by
      have h2 := supDist_le_torusDist u x'
      have h3 := Multiscale.Adj.torusDist_le hadj.symm
      have : (supDist u x' : ℝ) ≤ 1 := h2.trans h3
      exact_mod_cast this
    exact ⟨v, hv, (supDist_triangle u x' v).trans (by omega)⟩

include hc hL in
/-- **Lemma II.2.5 (b)**: the data sites `Ω₁ ∪ C(Ω₁)` of the local family `G^{Z'}_{k+1}` lie in
(the fine set of) `V_{Z'} = U_{Z'}^{∼1}`. -/
theorem genBoundaryLocal_subset_V {u : Torus d (M1 * (c * n1) * L ^ (k + 1))}
    (hu : u ∈ Background.dataSites (genBoundaryLocal M1 c n1 L k st hc hn hL hρ hω hZ hZ')) :
    blockMap (L ^ (k + 1) * (c * M1)) n1 u ∈ nbhd 1 (thick ⌊Rk⌋₊ (Z' : Set (Torus d n1))) := by
  obtain ⟨v, hv, hd⟩ := genBoundaryLocal_near st hc hn hL hρ hω hZ hZ' hu
  have hv' := hv
  unfold stepU at hv'
  rw [mem_fineK1] at hv'
  exact mem_nbhd.2 ⟨_, hv', cubes_close (eleven_add_one_le_P1 (by omega) le_rfl) hd⟩

include hc hL in
/-- **Lemma II.2.5 (b)**: the pieces of the local families of distinct components `Z' ≠ Z''` are at
fine distance `≥ 2`: no bond joins them and no collar site of one lies in the other. -/
theorem genBoundaryLocal_far {Z'' : Finset (Torus d n1)} (hZ'' : Z'' ∈ comps ω (finOf Zp))
    (hne : Z' ≠ Z'') {u w : Torus d (M1 * (c * n1) * L ^ (k + 1))}
    (hu : u ∈ Background.dataSites (genBoundaryLocal M1 c n1 L k st hc hn hL hρ hω hZ hZ'))
    (hw : w ∈ Background.dataSites (genBoundaryLocal M1 c n1 L k st hc hn hL hρ hω hZ hZ'')) :
    2 ≤ supDist u w := by
  obtain ⟨v, hv, hd⟩ := genBoundaryLocal_near st hc hn hL hρ hω hZ hZ' hu
  obtain ⟨v', hv', hd'⟩ := genBoundaryLocal_near st hc hn hL hρ hω hZ hZ'' hw
  have e1 := hv
  have e2 := hv'
  unfold stepU at e1 e2
  rw [mem_fineK1] at e1 e2
  have hsep := nbhd_disjoint_of_comps hZ' hZ'' hne (⌊Rk⌋₊ + 1) _ e1 _ e2
  have hP : M1 * (c * n1) * L ^ (k + 1) = (L ^ (k + 1) * (c * M1)) * n1 := by ring
  have h3 := two_mul_add_one_le_supDist (M1 := M1) (N₁ := c * n1) (L := L) (q := k + 1) hP
    (x := v) (y := v') (by omega)
  have h4 := supDist_triangle v u v'
  have h5 := supDist_triangle u w v'
  have h6 := supDist_comm v u
  have h7 := supDist_comm w v'
  have hB : 1 ≤ M1 * L ^ (k + 1) := Nat.one_le_iff_ne_zero.2 (by
    have := NeZero.ne L; have := NeZero.ne M1; positivity)
  have h8 : 14 * (M1 * L ^ (k + 1)) ≤ L ^ (k + 1) * (c * M1) := by
    calc 14 * (M1 * L ^ (k + 1)) = L ^ (k + 1) * (14 * M1) := by ring
      _ ≤ L ^ (k + 1) * (c * M1) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hc)
  have h9 : 11 * M1 * L ^ (k + 1) = 11 * (M1 * L ^ (k + 1)) := by ring
  omega

include hc hL in
/-- **Lemma II.2.5 (c)** (agreement): on the fine set of `E_{Z'} = Z'^{∼⌊R_k⌋}` the layers of the
local family `G^{Z'}_{k+1}` and of the global family `G^∂_{k+1}` coincide. -/
theorem genBoundaryLocal_agree {x : Torus d (M1 * (c * n1) * L ^ (k + 1))}
    (hx : blockMap (L ^ (k + 1) * (c * M1)) n1 x ∈ nbhd ⌊Rk⌋₊ (Z' : Set (Torus d n1)))
    (n : ℕ) :
    x ∈ (genBoundaryLocal M1 c n1 L k st hc hn hL hρ hω hZ hZ').Ω n ↔
      x ∈ (genBoundary M1 c n1 L k st hc hn hL hρ (Zp := Zp) hZ).Ω n := by
  have hnear1 : ∀ y : Torus d (M1 * (c * n1) * L ^ (k + 1)),
      supDist (blockMap (L ^ (k + 1) * (c * M1)) n1 x)
        (blockMap (L ^ (k + 1) * (c * M1)) n1 y) ≤ 1 →
      blockMap (L ^ (k + 1) * (c * M1)) n1 y ∈ thick ⌊Rk⌋₊ (Z' : Set (Torus d n1)) := by
    intro y hy
    obtain ⟨z, hz, hdz⟩ := mem_nbhd.1 hx
    refine mem_nbhd.2 ⟨z, hz, ?_⟩
    have h3 := supDist_triangle (blockMap (L ^ (k + 1) * (c * M1)) n1 y)
      (blockMap (L ^ (k + 1) * (c * M1)) n1 x) z
    have h4 := supDist_comm (blockMap (L ^ (k + 1) * (c * M1)) n1 y)
      (blockMap (L ^ (k + 1) * (c * M1)) n1 x)
    omega
  -- the cube of a site within one `π_k`-cube of `x` is within `⌊R_k⌋ + 1` of `Z'`
  have hnear : ∀ y : Torus d (M1 * (c * n1) * L ^ (k + 1)),
      supDist (blockMap (L ^ k * (c * M1)) n0 x) (blockMap (L ^ k * (c * M1)) n0 y) ≤ 1 →
      blockMap (L ^ (k + 1) * (c * M1)) n1 y ∈ thick ⌊Rk⌋₊ (Z' : Set (Torus d n1)) := by
    intro y hy
    refine hnear1 y ?_
    have h1 := supDist_blockMap_le (d := d) (L := L) (m := n1) (n := n0) hn
      (blockMap (L ^ k * (c * M1)) n0 x) (blockMap (L ^ k * (c * M1)) n0 y)
    rw [blockMap_k_succ hn, blockMap_k_succ hn] at h1
    have h2 : (supDist (blockMap (L ^ k * (c * M1)) n0 x)
        (blockMap (L ^ k * (c * M1)) n0 y) + L - 1) / L < 2 :=
      (Nat.div_lt_iff_lt_mul (by omega)).2 (by omega)
    omega
  have hP0 : M1 * (c * n1) * L ^ (k + 1) = (L ^ k * (c * M1)) * n0 := by rw [hn]; ring
  have hP1 : M1 * (c * n1) * L ^ (k + 1) = (L ^ (k + 1) * (c * M1)) * n1 := by ring
  have hM12 : 12 * M1 ≤ c * M1 := Nat.mul_le_mul_right _ (by omega)
  have hAW : ∀ m, m ≤ k + 1 → (x ∈ minLayer M1 (c * n1) L (k + 1) k
      (stepWLoc M1 c n1 L k ⌊Rprev⌋₊ ⌊Rk⌋₊ st.Z (Z' : Set (Torus d n1))) m ↔
      x ∈ minLayer M1 (c * n1) L (k + 1) k (stepW M1 c n1 L k ⌊Rprev⌋₊ st.Z) m) := by
    intro m hm
    by_cases hmk : m ≤ k
    · refine minLayer_local_pi (M := c * M1) _ hL (Nat.le_succ k) hM12 hP0 hmk fun y hy => ?_
      unfold stepWLoc
      simp only [Finset.mem_inter]
      have : y ∈ stepU M1 c n1 L k ⌊Rk⌋₊ (Z' : Set (Torus d n1)) := by
        unfold stepU; rw [mem_fineK1]; exact hnear y hy
      exact ⟨fun h => h.1, fun h => ⟨h, this⟩⟩
    · rw [minLayer_of_gt _ (by omega : k < m), minLayer_of_gt _ (by omega : k < m)]
  have hAU : ∀ m, m ≤ k + 1 → (x ∈ minLayer M1 (c * n1) L (k + 1) (k + 1)
      (stepU M1 c n1 L k ⌊Rk⌋₊ (Z' : Set (Torus d n1))) m ↔
      x ∈ minLayer M1 (c * n1) L (k + 1) (k + 1) (stepU M1 c n1 L k ⌊Rk⌋₊ Zp) m) := by
    intro m hm
    refine minLayer_local_pi (M := c * M1) _ hL le_rfl hM12 hP1 hm fun y hy => ?_
    have hy1 := hnear1 y hy
    have hy2 : blockMap (L ^ (k + 1) * (c * M1)) n1 y ∈ thick ⌊Rk⌋₊ Zp :=
      nbhd_mono le_rfl (fun z hz => mem_finOf.1 (comp_subset hZ' (Finset.mem_coe.1 hz))) hy1
    unfold stepU
    rw [mem_fineK1, mem_fineK1]
    exact ⟨fun _ => hy2, fun _ => hy1⟩
  unfold genBoundaryLocal genBoundary
  rw [boundaryGenSet_Ω, boundaryGenSet_Ω]
  by_cases hn1 : n ≤ k + 1
  · simp only [boundaryLayer, Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter,
      hAW n hn1, hAU n hn1]
  · have hk : k + 1 < n := by omega
    simp [boundaryLayer, minLayer_of_gt _ (by omega : k < n), minLayer_of_gt _ hk]

end Local

end Flow

end Balaban.LargeField
