/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalFluctGen

/-!
# IndexMatch for the local generator: the covers of `𝔹_{k+1}` and `𝔹_{k+1}(Y)` inside `Y`

The replacement of P3 pp. 78-79 recomputes each term of the step on the local generator
`𝔹_{k+1}(Y) = localB (k + 1) … Y`.  Its first input is that the decoupling cover of the ambient
level set `𝔹_{k+1}` and that of `𝔹_{k+1}(Y)` coincide inside `Y`: the same cubes, the same
partition functions `χ_z` and the same footprints `𝒬(z)` wherever only cubes with base in a
`𝒞_{k+1}`-cube of `Y` are involved.  (Near `∂Y` the local generator has cubes of lower layers and
the partition functions differ.)

* `mem_cubeIdx_congr_of_layer`, `coverDenom_congr_of_active`, `chi_congr_of_active`,
  `qset_coverOf_congr`: two generating sets with the same layers at the relevant bases have the same
  cover cubes, partition functions and footprints there;
* `mem_layer_iff_of_mem_top`: a site of `Ω_K` lies in no layer other than `K`;
* `level_localB_layer_iff`, `level_localB_mem_cubeIdx_iff`, `level_localB_chi_eq`,
  `level_localB_qset_eq`: the instance ambient level set (`IsLevel 𝔹_{k+1} (k + 1)`) versus
  `localB (k + 1) … Y`.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Finset Balaban.Fluctuation
  Balaban.LargeField Balaban.SmallField.GsSpec

section Cross

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱ' : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {G' : GeneratingSet d L (N₁ * L ^ m₁) K ϱ'}

/-- **The cover cubes of two generating sets with the same layers at the base of a cube agree
there**: `q ∈ cubeIdx G ↔ q ∈ cubeIdx G'` when the base `q.2` lies in the same layers `1 ≤ n ≤ K`
of `G` and of `G'`. -/
theorem mem_cubeIdx_congr_of_layer {q : ℕ × CTorus d L N₁ m₁ K}
    (h : ∀ n, 1 ≤ n → n ≤ K → (q.2 ∈ G.layer n ↔ q.2 ∈ G'.layer n)) :
    q ∈ cubeIdx G ↔ q ∈ cubeIdx G' := by
  rw [mem_cubeIdx, mem_cubeIdx]
  constructor
  · rintro ⟨hn, hl, hb⟩; exact ⟨hn, (h q.1 hn.1 hn.2).1 hl, hb⟩
  · rintro ⟨hn, hl, hb⟩; exact ⟨hn, (h q.1 hn.1 hn.2).2 hl, hb⟩

/-- **The partition of unity of two covers agrees at a site where their active cubes agree**: if
every cube whose bump does not vanish at `x` is a cube of `coverOf G` exactly when it is one of
`coverOf G'`, the denominators `D(x) = ∑_z h̃_z(x)` coincide and so do all the `χ_z(x)`. -/
theorem coverDenom_congr_of_active {x : CTorus d L N₁ m₁ K}
    (h : ∀ q : ℕ × CTorus d L N₁ m₁ K, cubeBump m₁ q.1 q.2 x ≠ 0 →
      (q ∈ cubeIdx G ↔ q ∈ cubeIdx G')) :
    coverDenom G x = coverDenom G' x := by
  classical
  unfold coverDenom
  rw [← Finset.sum_filter_ne_zero, ← Finset.sum_filter_ne_zero (s := cubeIdx G')]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext q
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hq, hne⟩; exact ⟨(h q hne).1 hq, hne⟩
  · rintro ⟨hq, hne⟩; exact ⟨(h q hne).2 hq, hne⟩

theorem chi_congr_of_active {x : CTorus d L N₁ m₁ K}
    (h : ∀ q : ℕ × CTorus d L N₁ m₁ K, cubeBump m₁ q.1 q.2 x ≠ 0 →
      (q ∈ cubeIdx G ↔ q ∈ cubeIdx G')) (q : ℕ × CTorus d L N₁ m₁ K) :
    chi G q x = chi G' q x := by
  unfold chi
  rw [coverDenom_congr_of_active h]

/-- **The footprints `𝒬(z)` of two covers agree** when every cube meeting the hat box of `z` is a
cube of `coverOf G` exactly when it is one of `coverOf G'`. -/
theorem qset_coverOf_congr {q : ℕ × CTorus d L N₁ m₁ K}
    (h : ∀ q' : ℕ × CTorus d L N₁ m₁ K, (∃ y, SameCell (L ^ (q'.1 + m₁)) y q'.2 ∧
      InBox m₁ q.1 q.2 (hatRad L m₁ q.1) y) → (q' ∈ cubeIdx G ↔ q' ∈ cubeIdx G')) :
    (coverOf G).Qset q = (coverOf G').Qset q := by
  ext q'
  rw [DecCover.mem_Qset, DecCover.mem_Qset]
  constructor
  · rintro ⟨hq', hy⟩; exact ⟨(h q' hy).1 hq', hy⟩
  · rintro ⟨hq', hy⟩; exact ⟨(h q' hy).2 hq', hy⟩

/-- A site of the top domain `Ω_K` lies in the layer `n` (`1 ≤ n ≤ K`) exactly when `n = K`. -/
theorem mem_layer_iff_of_mem_top {x : CTorus d L N₁ m₁ K} (hx : x ∈ G.Ω K) {n : ℕ}
    (hn : 1 ≤ n) (hnK : n ≤ K) : x ∈ G.layer n ↔ n = K := by
  rw [GeneratingSet.mem_layer]
  constructor
  · rintro ⟨-, hx'⟩
    by_contra hne
    exact hx' (G.Ω_antitone (by omega) (by omega) (by omega) hx)
  · rintro rfl
    exact ⟨hx, by rw [G.top]; exact Finset.notMem_empty _⟩

end Cross

section LevelLocal

variable {d L N₁ m₁ k : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}

/-- **IndexMatch, layers**: at a site whose `𝒞_{k+1}`-cube lies in `Y`, the ambient level set
`𝔹_{k+1}` (`IsLevel`) and the literal local generator `𝔹_{k+1}(Y) = localB (k + 1) … Y` have the
same layers (both: the top layer `k + 1` only). -/
theorem level_localB_layer_iff (hG' : IsLevel Gp (k + 1)) (hk : k + 1 ≤ k + 1)
    (Y : Set (CTorus d L N₁ m₁ (k + 1))) {ϱl : ℝ} (hsep : ϱl ≤ minSep L (L ^ m₁))
    {x : CTorus d L N₁ m₁ (k + 1)}
    (hx : ∀ y : CTorus d L N₁ m₁ (k + 1),
      fineCubeIdx (L ^ m₁) N₁ L (k + 1) (k + 1)
          (torusCast y : Torus d (L ^ m₁ * N₁ * L ^ (k + 1))) =
        fineCubeIdx (L ^ m₁) N₁ L (k + 1) (k + 1)
          (torusCast x : Torus d (L ^ m₁ * N₁ * L ^ (k + 1))) → y ∈ Y)
    {n : ℕ} (hn : 1 ≤ n) (hnK : n ≤ k + 1) :
    x ∈ Gp.layer n ↔ x ∈ (GsSpec.localB (k + 1) hk Y hsep).layer n := by
  rw [mem_layer_iff_of_mem_top ((Gp.mem_layer).1 (hG'.mem_layer x)).1 hn hnK,
    mem_layer_iff_of_mem_top ((GsSpec.mem_localB_Ω_top x).2 hx) hn hnK]

/-- **IndexMatch, cover cubes**: a cube whose base has its `𝒞_{k+1}`-cube in `Y` is a cube of the
cover of the ambient level set exactly when it is a cube of the cover of `𝔹_{k+1}(Y)`. -/
theorem level_localB_mem_cubeIdx_iff (hG' : IsLevel Gp (k + 1)) (hk : k + 1 ≤ k + 1)
    (Y : Set (CTorus d L N₁ m₁ (k + 1))) {ϱl : ℝ} (hsep : ϱl ≤ minSep L (L ^ m₁))
    {q : ℕ × CTorus d L N₁ m₁ (k + 1)}
    (hq : ∀ y : CTorus d L N₁ m₁ (k + 1),
      fineCubeIdx (L ^ m₁) N₁ L (k + 1) (k + 1)
          (torusCast y : Torus d (L ^ m₁ * N₁ * L ^ (k + 1))) =
        fineCubeIdx (L ^ m₁) N₁ L (k + 1) (k + 1)
          (torusCast q.2 : Torus d (L ^ m₁ * N₁ * L ^ (k + 1))) → y ∈ Y) :
    q ∈ cubeIdx Gp ↔ q ∈ cubeIdx (GsSpec.localB (k + 1) hk Y hsep) :=
  mem_cubeIdx_congr_of_layer fun _ hn hnK => level_localB_layer_iff hG' hk Y hsep hq hn hnK

/-- **IndexMatch, partition of unity**: at a site `x` all of whose active cubes (non-vanishing
bump) have their base in a `𝒞_{k+1}`-cube of `Y`, the partition functions `χ_z(x)` of the covers of
the ambient level set and of `𝔹_{k+1}(Y)` coincide. -/
theorem level_localB_chi_eq (hG' : IsLevel Gp (k + 1)) (hk : k + 1 ≤ k + 1)
    (Y : Set (CTorus d L N₁ m₁ (k + 1))) {ϱl : ℝ} (hsep : ϱl ≤ minSep L (L ^ m₁))
    {x : CTorus d L N₁ m₁ (k + 1)}
    (hx : ∀ q : ℕ × CTorus d L N₁ m₁ (k + 1), cubeBump m₁ q.1 q.2 x ≠ 0 →
      ∀ y : CTorus d L N₁ m₁ (k + 1),
        fineCubeIdx (L ^ m₁) N₁ L (k + 1) (k + 1)
            (torusCast y : Torus d (L ^ m₁ * N₁ * L ^ (k + 1))) =
          fineCubeIdx (L ^ m₁) N₁ L (k + 1) (k + 1)
            (torusCast q.2 : Torus d (L ^ m₁ * N₁ * L ^ (k + 1))) → y ∈ Y)
    (q : ℕ × CTorus d L N₁ m₁ (k + 1)) :
    chi Gp q x = chi (GsSpec.localB (k + 1) hk Y hsep) q x :=
  chi_congr_of_active (fun q' hq' => level_localB_mem_cubeIdx_iff hG' hk Y hsep (hx q' hq')) q

/-- **IndexMatch, footprints**: if every cube meeting the hat box of `z` has its base in a
`𝒞_{k+1}`-cube of `Y`, the footprint `𝒬(z)` is the same for the covers of the ambient level set
and of `𝔹_{k+1}(Y)`. -/
theorem level_localB_qset_eq (hG' : IsLevel Gp (k + 1)) (hk : k + 1 ≤ k + 1)
    (Y : Set (CTorus d L N₁ m₁ (k + 1))) {ϱl : ℝ} (hsep : ϱl ≤ minSep L (L ^ m₁))
    {q : ℕ × CTorus d L N₁ m₁ (k + 1)}
    (hq : ∀ q' : ℕ × CTorus d L N₁ m₁ (k + 1), (∃ y, SameCell (L ^ (q'.1 + m₁)) y q'.2 ∧
        InBox m₁ q.1 q.2 (hatRad L m₁ q.1) y) →
      ∀ y : CTorus d L N₁ m₁ (k + 1),
        fineCubeIdx (L ^ m₁) N₁ L (k + 1) (k + 1)
            (torusCast y : Torus d (L ^ m₁ * N₁ * L ^ (k + 1))) =
          fineCubeIdx (L ^ m₁) N₁ L (k + 1) (k + 1)
            (torusCast q'.2 : Torus d (L ^ m₁ * N₁ * L ^ (k + 1))) → y ∈ Y) :
    (coverOf Gp).Qset q = (coverOf (GsSpec.localB (k + 1) hk Y hsep)).Qset q :=
  qset_coverOf_congr fun q' hq' => level_localB_mem_cubeIdx_iff hG' hk Y hsep (hq q' hq')

end LevelLocal

end Balaban.Localization
