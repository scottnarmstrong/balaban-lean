module

public import Balaban.LargeField.Region.SymmLat
public import Balaban.LargeField.Background.StepGenSetsFlow
public import Balaban.Background.EquivarianceLat
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Lattice covariance of the generating sets of a level-`q` torus

For an affine lattice isometry `A` of the level-`q` torus `Torus d (M1 * N₁ * L ^ q)` aligned to the
cubes of side `c M1 L^q` (`A.Aligned (c * M1 * L ^ q)`), the block maps of all scales `≤ q`
(`jBlock`), the cube indices `fineCubeIdx` and the cubes of `𝕋_q` commute with `A` up to affine
isometries of the quotient tori.  Hence the layers of the minimal generating sets
(`minLayer`, `cubeInterior`, `nearStep`) are covariant (`minLayer_map`) and `A` is a lattice symmetry
(`LatSymm`) between the minimal generating sets of a set and of its image, between `genCube`s of
corresponding cubes, etc.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background

theorem AffIso.Aligned.mono {d ℓ : ℕ} (A : AffIso d ℓ) {P P' : ℕ} (h : A.Aligned P')
    (hdiv : P ∣ P') : A.Aligned P :=
  fun i => dvd_trans hdiv (h i)

theorem AffIso.toFun_injective {d ℓ : ℕ} (A : AffIso d ℓ) : Function.Injective A.toFun :=
  fun x y h => by simpa [A.invFun_toFun] using congrArg A.invFun h

theorem AffIso.image_nbhd {d ℓ : ℕ} [NeZero ℓ] (A : AffIso d ℓ) (m : ℕ) (X : Set (Torus d ℓ)) :
    A.toFun '' nbhd m X = nbhd m (A.toFun '' X) :=
  _root_.Balaban.LargeField.image_nbhd (e := A.toEquiv) A.supDist_eq m X

theorem AffIso.image_thick2 {d ℓ : ℕ} [NeZero ℓ] (A : AffIso d ℓ) (r : ℕ) (X : Set (Torus d ℓ)) :
    A.toFun '' thick2 r X = thick2 r (A.toFun '' X) := by
  unfold thick2 thick
  rw [A.image_nbhd, A.image_nbhd]

theorem AffIso.image_thick {d ℓ : ℕ} [NeZero ℓ] (A : AffIso d ℓ) (r : ℕ) (X : Set (Torus d ℓ)) :
    A.toFun '' thick r X = thick r (A.toFun '' X) :=
  A.image_nbhd _ X

theorem AffIso.image_compl {d ℓ : ℕ} (A : AffIso d ℓ) (X : Set (Torus d ℓ)) :
    A.toFun '' Xᶜ = (A.toFun '' X)ᶜ :=
  A.toEquiv.image_compl X

section Gen

variable {d L N₀ q : ℕ} [NeZero L] [NeZero N₀] {ϱ : ℝ}

/-- The nearest-neighbour structure of an affine lattice isometry. -/
def AffIso.nbr (A : AffIso d (N₀ * L ^ q)) : NbrSymm A.toEquiv :=
  ⟨A.perm, A.flip, fun x μ => A.toFun_add_single x μ⟩

theorem jBlock_aff0 (A : AffIso d (N₀ * L ^ q)) (hal : A.Aligned (L ^ q)) {n' : ℕ} (hn : n' ≤ q)
    (x : Torus d (N₀ * L ^ q)) :
    jBlock d L N₀ q n' (A.toFun x) =
      (A.coarse (L ^ n') (N₀ * L ^ (q - n'))).toFun (jBlock d L N₀ q n' x) := by
  have hpos : 0 < L ^ n' := by have := NeZero.pos L; positivity
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hn
  refine A.blockMap_toFun (side_eq hn) hpos ?_ x
  exact AffIso.Aligned.mono A hal ⟨L ^ t, by ring⟩

/-- A lattice symmetry from the layers: if `A` maps the layers of `G` onto those of `G'`, it is a
lattice symmetry from `G` to `G'`. -/
def AffIso.latSymm (A : AffIso d (N₀ * L ^ q)) (hal : A.Aligned (L ^ q))
    {G G' : GeneratingSet d L N₀ q ϱ}
    (h : ∀ m, G'.Ω m = (G.Ω m).map A.toEquiv.toEmbedding) : LatSymm G G' A.toEquiv :=
  { A.nbr with
    omega := fun j _ _ x => by rw [h j, Finset.mem_map_equiv, Equiv.symm_apply_apply]
    block := fun n' h1 hq _ x y => by
      have e := fun z => jBlock_aff0 A hal hq z
      show jBlock d L N₀ q n' (A.toFun x) = jBlock d L N₀ q n' (A.toFun y) ↔ _
      rw [e, e]
      exact ⟨fun hh => (A.coarse (L ^ n') (N₀ * L ^ (q - n'))).toFun_injective hh,
        fun hh => by rw [hh]⟩ }

end Gen

section Level

variable {d L M1 N₁ q : ℕ} [NeZero L] [NeZero M1] [NeZero N₁] (A : AffIso d (M1 * N₁ * L ^ q))


variable {A} {c : ℕ} (hal : A.Aligned (c * M1 * L ^ q))
include hal

theorem AffIso.blockMap_level {P m : ℕ} (hℓ : M1 * N₁ * L ^ q = P * m) (hP : 0 < P)
    (hdiv : P ∣ c * M1 * L ^ q) (x : Torus d (M1 * N₁ * L ^ q)) :
    blockMap P m (A.toFun x) = (A.coarse P m).toFun (blockMap P m x) :=
  A.blockMap_toFun hℓ hP (AffIso.Aligned.mono A hal hdiv) x

theorem fineCubeIdx_aff {n' : ℕ} (hn : n' ≤ q) (x : Torus d (M1 * N₁ * L ^ q)) :
    fineCubeIdx M1 N₁ L q n' (A.toFun x) =
      (A.coarse (L ^ n' * M1) (N₁ * L ^ (q - n'))).toFun (fineCubeIdx M1 N₁ L q n' x) := by
  have hpos : 0 < L ^ n' * M1 := by have := NeZero.pos L; have := NeZero.pos M1; positivity
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hn
  refine AffIso.blockMap_level hal (fine_eq_cube hn) hpos ?_ x
  exact ⟨c * L ^ t, by ring⟩

theorem jBlock_aff {n' : ℕ} (hn : n' ≤ q) (x : Torus d (M1 * N₁ * L ^ q)) :
    jBlock d L (M1 * N₁) q n' (A.toFun x) =
      (A.coarse (L ^ n') (M1 * N₁ * L ^ (q - n'))).toFun (jBlock d L (M1 * N₁) q n' x) := by
  have hpos : 0 < L ^ n' := by have := NeZero.pos L; positivity
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hn
  refine AffIso.blockMap_level hal (side_eq hn) hpos ?_ x
  exact ⟨c * M1 * L ^ t, by ring⟩

theorem cube_aff {m : ℕ} (hm : N₁ = c * m) (x : Torus d (M1 * N₁ * L ^ q)) :
    blockMap (L ^ q * (c * M1)) m (A.toFun x) =
      (A.coarse (L ^ q * (c * M1)) m).toFun (blockMap (L ^ q * (c * M1)) m x) := by
  have hpos : 0 < L ^ q * (c * M1) := by
    have := NeZero.pos L; have := NeZero.pos M1
    have hc : 0 < c := by
      rcases Nat.eq_zero_or_pos c with h | h
      · exact absurd (by simpa [h] using hm) (NeZero.ne N₁)
      · exact h
    positivity
  refine AffIso.blockMap_level hal (by rw [hm]; ring) hpos ?_ x
  exact ⟨1, by ring⟩

end Level


section Layers

variable {d L M1 N₁ q c : ℕ} [NeZero L] [NeZero M1] [NeZero N₁] {A : AffIso d (M1 * N₁ * L ^ q)}
  (hal : A.Aligned (c * M1 * L ^ q))
include hal

theorem cubeInterior_map {j : ℕ} (hj : j ≤ q) (X : Finset (Torus d (M1 * N₁ * L ^ q))) :
    cubeInterior M1 N₁ L q j (X.map A.toEquiv.toEmbedding) =
      (cubeInterior M1 N₁ L q j X).map A.toEquiv.toEmbedding := by
  classical
  ext x
  obtain ⟨x0, rfl⟩ := A.toEquiv.surjective x
  simp only [Finset.mem_map_equiv, Equiv.symm_apply_apply, mem_cubeInterior]
  have key : ∀ y0 : Torus d (M1 * N₁ * L ^ q),
      fineCubeIdx M1 N₁ L q j (A.toEquiv y0) = (A.coarse (L ^ j * M1) (N₁ * L ^ (q - j))).toFun
        (fineCubeIdx M1 N₁ L q j y0) := fun y0 => fineCubeIdx_aff hal hj y0
  constructor
  · intro h y0 hy0
    have := h (A.toEquiv y0) (by
      rw [key, key, hy0])
    simpa only [Equiv.symm_apply_apply] using this
  · intro h y hy
    obtain ⟨y0, rfl⟩ := A.toEquiv.surjective y
    rw [key, key] at hy
    simpa only [Equiv.symm_apply_apply] using
      h y0 ((A.coarse (L ^ j * M1) (N₁ * L ^ (q - j))).toFun_injective hy)

theorem nearStep_map {n' : ℕ} (hn : n' ≤ q) (X : Finset (Torus d (M1 * N₁ * L ^ q))) :
    nearStep M1 N₁ L q n' (X.map A.toEquiv.toEmbedding) =
      (nearStep M1 N₁ L q n' X).map A.toEquiv.toEmbedding := by
  classical
  ext x
  obtain ⟨x0, rfl⟩ := A.toEquiv.surjective x
  simp only [Finset.mem_map_equiv, Equiv.symm_apply_apply, mem_nearStep]
  have key : ∀ y0 : Torus d (M1 * N₁ * L ^ q),
      fineCubeIdx M1 N₁ L q n' (A.toEquiv y0) = (A.coarse (L ^ n' * M1) (N₁ * L ^ (q - n'))).toFun
        (fineCubeIdx M1 N₁ L q n' y0) := fun y0 => fineCubeIdx_aff hal hn y0
  constructor
  · rintro ⟨y, hy, hd⟩
    refine ⟨A.toEquiv.symm y, hy, ?_⟩
    obtain ⟨y0, rfl⟩ := A.toEquiv.surjective y
    rw [key, key, AffIso.supDist_eq] at hd
    simpa only [Equiv.symm_apply_apply] using hd
  · rintro ⟨y0, hy0, hd⟩
    refine ⟨A.toEquiv y0, by simpa only [Equiv.symm_apply_apply] using hy0, ?_⟩
    rw [key, key, AffIso.supDist_eq]
    exact hd

theorem minLayerAux_map {j : ℕ} (hj : j ≤ q) (X : Finset (Torus d (M1 * N₁ * L ^ q))) (t : ℕ) :
    minLayerAux M1 N₁ L q j (X.map A.toEquiv.toEmbedding) t =
      (minLayerAux M1 N₁ L q j X t).map A.toEquiv.toEmbedding := by
  induction t with
  | zero => exact cubeInterior_map hal hj X
  | succ t ih =>
    show nearStep M1 N₁ L q (j - (t + 1)) _ = (nearStep M1 N₁ L q (j - (t + 1)) _).map _
    rw [ih]
    exact nearStep_map hal (by omega) _

theorem minLayer_map {j : ℕ} (hj : j ≤ q) (X : Finset (Torus d (M1 * N₁ * L ^ q))) (m : ℕ) :
    minLayer M1 N₁ L q j (X.map A.toEquiv.toEmbedding) m =
      (minLayer M1 N₁ L q j X m).map A.toEquiv.toEmbedding := by
  classical
  unfold minLayer
  split_ifs with h
  · exact minLayerAux_map hal hj X _
  · simp

end Layers


section Cubes

variable {d L M1 N₁ q c : ℕ} [NeZero L] [NeZero M1] [NeZero N₁] {A : AffIso d (M1 * N₁ * L ^ q)}
  (hal : A.Aligned (c * M1 * L ^ q))
include hal

theorem cubePre_map {P m : ℕ} (hℓ : M1 * N₁ * L ^ q = P * m) (hP : 0 < P)
    (hdiv : P ∣ c * M1 * L ^ q) (B : Set (Torus d m)) :
    (cubePre M1 N₁ L q P m B).map A.toEquiv.toEmbedding =
      cubePre M1 N₁ L q P m ((A.coarse P m).toFun '' B) := by
  ext x
  obtain ⟨x0, rfl⟩ := A.toEquiv.surjective x
  rw [Finset.mem_map_equiv, Equiv.symm_apply_apply, mem_cubePre, mem_cubePre, AffIso.toEquiv_apply,
    AffIso.blockMap_level hal hℓ hP hdiv]
  exact ((A.coarse P m).toFun_injective.mem_set_image).symm

variable {n : ℕ} [NeZero n] (hm : N₁ = c * n)
include hm

theorem genCube_map (a : Torus d n) :
    ∀ m, (genCube (M1 := M1) (N₁ := N₁) (L := L) (q := q) c n
        ((A.coarse (L ^ q * (c * M1)) n).toFun a)).Ω m =
      ((genCube (M1 := M1) (N₁ := N₁) (L := L) (q := q) c n a).Ω m).map A.toEquiv.toEmbedding := by
  intro m
  have hpos : 0 < L ^ q * (c * M1) := by
    have := NeZero.pos L; have := NeZero.pos M1
    have hc : 0 < c := by
      rcases Nat.eq_zero_or_pos c with h | h
      · exact absurd (by simpa [h] using hm) (NeZero.ne N₁)
      · exact h
    positivity
  rw [genCube_Ω, genCube_Ω, ← minLayer_map hal le_rfl, cubePre_map hal (by rw [hm]; ring) hpos
    ⟨1, by ring⟩, AffIso.image_nbhd, Set.image_singleton]

/-- The lattice symmetry between the generating sets of corresponding cubes. -/
noncomputable def genCube_latSymm (a : Torus d n) (hq : A.Aligned (L ^ q)) :
    LatSymm (genCube (M1 := M1) (N₁ := N₁) (L := L) (q := q) c n a)
      (genCube (M1 := M1) (N₁ := N₁) (L := L) (q := q) c n
        ((A.coarse (L ^ q * (c * M1)) n).toFun a)) A.toEquiv :=
  A.latSymm hq (genCube_map hal hm a)

end Cubes


section Mixed

theorem genCubeMixed_Ω' {d L M1 N₁ q c n : ℕ} [NeZero L] [NeZero M1] [NeZero N₁]
    (hm1 : N₁ * L ^ (q - q) = c * n) (a : Torus d n) (Om : Finset (Torus d (M1 * N₁ * L ^ q)))
    (hOm : IsBlockUnion L (M1 * N₁) q q Om) (m : ℕ) :
    (genCubeMixed hm1 a Om hOm).Ω m =
      if m = q then Om ∩ cubePre M1 N₁ L q (L ^ q * (c * M1)) n (nbhd 2 {a})
      else (genCube (M1 := M1) (N₁ := N₁) (L := L) (q := q) c n a).Ω m := rfl

variable {d L M1 N₁ q c : ℕ} [NeZero L] [NeZero M1] [NeZero N₁] {A : AffIso d (M1 * N₁ * L ^ q)}
  (hal : A.Aligned (c * M1 * L ^ q)) {n : ℕ} [NeZero n] (hm : N₁ = c * n)
include hal hm

theorem genCubeMixed_map (hm1 : N₁ * L ^ (q - q) = c * n) (a : Torus d n)
    (Om Om' : Finset (Torus d (M1 * N₁ * L ^ q))) (hOm : IsBlockUnion L (M1 * N₁) q q Om)
    (hOm' : IsBlockUnion L (M1 * N₁) q q Om') (hOO : Om' = Om.map A.toEquiv.toEmbedding) :
    ∀ m, (genCubeMixed hm1 ((A.coarse (L ^ q * (c * M1)) n).toFun a) Om' hOm').Ω m =
      ((genCubeMixed hm1 a Om hOm).Ω m).map A.toEquiv.toEmbedding := by
  intro m
  have hpos : 0 < L ^ q * (c * M1) := by
    have := NeZero.pos L; have := NeZero.pos M1
    have hc : 0 < c := by
      rcases Nat.eq_zero_or_pos c with h | h
      · exact absurd (by simpa [h] using hm) (NeZero.ne N₁)
      · exact h
    positivity
  rw [genCubeMixed_Ω', genCubeMixed_Ω']
  by_cases hmq : m = q
  · simp only [hmq, ↓reduceIte]
    rw [hOO, Finset.map_inter, cubePre_map hal (by rw [hm]; ring) hpos ⟨1, by ring⟩,
      AffIso.image_nbhd, Set.image_singleton]
  · simp only [hmq, ↓reduceIte]
    exact genCube_map hal hm a m

end Mixed

section Boundary

variable {d L M1 N₁ k c : ℕ} [NeZero L] [NeZero M1] [NeZero N₁]
  {A : AffIso d (M1 * N₁ * L ^ (k + 1))} (hal : A.Aligned (c * M1 * L ^ (k + 1)))
include hal

theorem boundaryGenSet_map (W U Om : Finset (Torus d (M1 * N₁ * L ^ (k + 1))))
    (h : BoundaryHyp M1 N₁ L k W U Om) (W' U' Om' : Finset (Torus d (M1 * N₁ * L ^ (k + 1))))
    (h' : BoundaryHyp M1 N₁ L k W' U' Om') (hW : W' = W.map A.toEquiv.toEmbedding)
    (hU : U' = U.map A.toEquiv.toEmbedding) (hO : Om' = Om.map A.toEquiv.toEmbedding) :
    ∀ m, (boundaryGenSet W' U' Om' h').Ω m =
      ((boundaryGenSet W U Om h).Ω m).map A.toEquiv.toEmbedding := by
  intro m
  rw [boundaryGenSet_Ω, boundaryGenSet_Ω]
  unfold boundaryLayer
  rw [hW, hU, hO, minLayer_map hal (Nat.le_succ k), minLayer_map hal le_rfl, Finset.map_union,
    Finset.map_sdiff, Finset.map_inter]

end Boundary


section Flow

variable {d M1 c n1 L k n0 : ℕ} [NeZero L] [NeZero M1] [NeZero c] [NeZero n0] [NeZero n1]
  {A : AffIso d (M1 * (c * n1) * L ^ (k + 1))} (hal : A.Aligned (c * M1 * L ^ (k + 1)))
  (hn : n0 = L * n1)
include hal hn

theorem fineK_map (X : Set (Torus d n0)) :
    (fineK M1 c n1 L k n0 X).map A.toEquiv.toEmbedding =
      fineK M1 c n1 L k n0 ((A.coarse (L ^ k * (c * M1)) n0).toFun '' X) := by
  have hpos : 0 < L ^ k * (c * M1) := by
    have := NeZero.pos L; have := NeZero.pos c; have := NeZero.pos M1; positivity
  refine cubePre_map hal (by rw [hn]; ring) hpos ?_ X
  exact ⟨L, by ring⟩

theorem fineK1_map (X : Set (Torus d n1)) :
    (fineK1 M1 c n1 L k X).map A.toEquiv.toEmbedding =
      fineK1 M1 c n1 L k ((A.coarse (L ^ (k + 1) * (c * M1)) n1).toFun '' X) := by
  have hpos : 0 < L ^ (k + 1) * (c * M1) := by
    have := NeZero.pos L; have := NeZero.pos c; have := NeZero.pos M1; positivity
  refine cubePre_map hal (by ring) hpos ?_ X
  exact ⟨1, by ring⟩

end Flow


section FlowSets

variable {d M1 c n1 L k n0 : ℕ} [NeZero L] [NeZero M1] [NeZero c] [NeZero n0] [NeZero n1]
  {A : AffIso d (M1 * (c * n1) * L ^ (k + 1))} (hal : A.Aligned (c * M1 * L ^ (k + 1)))
  (hn : n0 = L * n1)
include hal hn

theorem stepW_map (ρ' : ℕ) (Z : Set (Torus d n0)) :
    (stepW M1 c n1 L k ρ' Z).map A.toEquiv.toEmbedding =
      stepW M1 c n1 L k ρ' ((A.coarse (L ^ k * (c * M1)) n0).toFun '' Z) := by
  unfold stepW
  rw [fineK_map hal hn, AffIso.image_thick2, AffIso.image_compl]

theorem stepU_map (ρ : ℕ) (Zp : Set (Torus d n1)) :
    (stepU M1 c n1 L k ρ Zp).map A.toEquiv.toEmbedding =
      stepU M1 c n1 L k ρ ((A.coarse (L ^ (k + 1) * (c * M1)) n1).toFun '' Zp) := by
  unfold stepU
  rw [fineK1_map hal hn, AffIso.image_thick]

theorem stepWLoc_map (ρ' ρ : ℕ) (Z : Set (Torus d n0)) (Z' : Set (Torus d n1)) :
    (stepWLoc M1 c n1 L k ρ' ρ Z Z').map A.toEquiv.toEmbedding =
      stepWLoc M1 c n1 L k ρ' ρ ((A.coarse (L ^ k * (c * M1)) n0).toFun '' Z)
        ((A.coarse (L ^ (k + 1) * (c * M1)) n1).toFun '' Z') := by
  unfold stepWLoc
  rw [Finset.map_inter, stepW_map hal hn, stepU_map hal hn]

variable {Rprev Rk : ℝ} {ω : ℕ} {Zp Zp' : Set (Torus d n1)} {Z' Z'' : Finset (Torus d n1)}
  (st st' : RegionStep d L n0 n1 Rprev Rk) (hc : 14 ≤ c) (hL : 2 ≤ L) (hρ : 3 * L ≤ ⌊Rprev⌋₊)
  (hω : 2 * ⌊Rk⌋₊ + L + 11 ≤ ω) (hZ : st.Omegaᶜ ⊆ Zp) (hZ' : Z' ∈ comps ω (finOf Zp))
  (hZ2 : st'.Omegaᶜ ⊆ Zp') (hZ'2 : Z'' ∈ comps ω (finOf Zp'))
  (hstZ : st'.Z = (A.coarse (L ^ k * (c * M1)) n0).toFun '' st.Z)
  (hstO : st'.Omega = (A.coarse (L ^ (k + 1) * (c * M1)) n1).toFun '' st.Omega)
  (hZZ : (Z'' : Set (Torus d n1)) = (A.coarse (L ^ (k + 1) * (c * M1)) n1).toFun '' (Z' : Set _))

include hstZ hstO hZZ

/-- **Covariance of the local boundary generating set** `G^{Z'}_{k+1}` of a component. -/
theorem genBoundaryLocal_map :
    ∀ m, (genBoundaryLocal M1 c n1 L k st' hc hn hL hρ hω hZ2 hZ'2).Ω m =
      ((genBoundaryLocal M1 c n1 L k st hc hn hL hρ hω hZ hZ').Ω m).map A.toEquiv.toEmbedding := by
  intro m
  unfold genBoundaryLocal
  refine boundaryGenSet_map hal _ _ _ _ _ _ _ _ ?_ ?_ ?_ m
  · rw [stepWLoc_map hal hn, hstZ, hZZ]
  · rw [stepU_map hal hn, hZZ]
  · rw [fineK1_map hal hn, hstO]

end FlowSets


section FlowOmega

variable {d L M : ℕ} [NeZero L] [NeZero M] {nn : ℕ → ℕ} [∀ i, NeZero (nn i)] {Rbase : ℝ}
  {lam R : ℕ → ℝ} {crit : ℕ → Option ℕ} {K₀ K : ℕ}

theorem cubeMap_aff (hnn : ∀ i, i < K → nn i = L * nn (i + 1)) {j : ℕ} (hj : j ≤ K)
    (A : AffIso d (M * nn K * L ^ K)) (hal : A.Aligned (M * L ^ K)) (x : Torus d (M * nn K * L ^ K)) :
    cubeMap nn L M K j (A.toFun x) =
      (A.coarse (L ^ j * M) (nn j)).toFun (cubeMap nn L M K j x) := by
  have hpos : 0 < L ^ j * M := by have := NeZero.pos L; have := NeZero.pos M; positivity
  exact A.blockMap_toFun (fine_eq hnn hj) hpos (AffIso.Aligned.mono A hal (dvd_pow_mul hj M L)) x

theorem flowOmega_map (S S' : RegionSeq d L nn Rbase lam R crit K₀)
    (hnn : ∀ i, i < K → nn i = L * nn (i + 1))
    (A : AffIso d (M * nn K * L ^ K)) (hal : A.Aligned (M * L ^ K))
    (hΩ : ∀ j, j ≤ K → S'.OmegaAt j = (A.coarse (L ^ j * M) (nn j)).toFun '' S.OmegaAt j) (j : ℕ) :
    flowOmega M S' K j = (flowOmega M S K j).map A.toEquiv.toEmbedding := by
  ext x
  obtain ⟨x0, rfl⟩ := A.toEquiv.surjective x
  rw [Finset.mem_map_equiv, Equiv.symm_apply_apply, mem_flowOmega, mem_flowOmega]
  refine and_congr_right fun hj => ?_
  rw [AffIso.toEquiv_apply, cubeMap_aff hnn hj A hal, hΩ j hj]
  exact (A.coarse (L ^ j * M) (nn j)).toFun_injective.mem_set_image

end FlowOmega

section CastGen

variable {d L q : ℕ} [NeZero L] {ϱ : ℝ} {N₀ N₀' : ℕ} [NeZero N₀] [NeZero N₀']

theorem AffIso.cast_cast {ℓ ℓ' ℓ'' : ℕ} (A : AffIso d ℓ) (h : ℓ = ℓ') (h' : ℓ' = ℓ'') :
    (A.cast h).cast h' = A.cast (h.trans h') := by
  subst h; subst h'; rfl

theorem castGen_map (h : N₀ = N₀') {G G' : GeneratingSet d L N₀ q ϱ} (A : AffIso d (N₀ * L ^ q))
    (hG : ∀ j, G'.Ω j = (G.Ω j).map A.toEquiv.toEmbedding) (j : ℕ) :
    (castGen h G').Ω j =
      ((castGen h G).Ω j).map (A.cast (congrArg (· * L ^ q) h)).toEquiv.toEmbedding := by
  subst h
  have : A.cast (congrArg (· * L ^ q) rfl) = A := by cases A; rfl
  rw [this]
  exact hG j

end CastGen

end Balaban.LargeField
