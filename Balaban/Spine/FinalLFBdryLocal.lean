/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.FinalLFRegionLocal
public import Balaban.LargeField.R.RRawHoleComponent

/-!
# The boundary domains of a history near a set of cubes are those of its components there (A6-4)

For two histories without removals up to the scale `k` whose components meeting a set `X` of
cubes of `𝕋_k` correspond (the same cubes and the same localized histories), the cube-level region
`Ω_k` agrees on the cubes of `X` and of the components meeting `X`, the nearest-neighbour components
of `Ω_k^c` meeting `X` agree, `X ∩ Z_k` agrees, and hence `X` is a boundary domain of one history iff
it is one of the other (`mem_bdryDoms_iff_of_corr`): the boundary terms of a history at `X` are
indexed by the records of its components meeting `X` (the decoration of the couplings of the record
gas).

* `omegaCube_iff_of_comp`, `omegaCube_of_not_mem_Zp`, `omegaCube_iff_on_of_corr`;
* `nnComp_subset_of_agree`, `nnComp_eq_of_corr`;
* `dmodOmega_of_corr`, `inter_Z_eq_of_corr`, **`mem_bdryDoms_iff_of_corr`**;
* the fine level: `supDist_castT`, `supDist_cubeMap_le_one`, `cube_supDist_le_one_of_nbr`,
  `omegaPost_eq_of_rem`, `omegaComp_subset_over`, `omegaComp_eq_of_corr`, `d7Pull_inter_eq_of_corr`,
  `fineValidAt_of_corr`, **`fineValidAt_iff_of_corr`**, **`d7SizeAt_eq_of_corr`**,
  **`mem_bdryDomsAt_iff_of_corr`** (the valid labels and their sizes agree).
-/

@[expose] public section

open Balaban Balaban.LargeField Balaban.LargeField.Def7 RegionHistory

namespace Balaban.RootFSpine

/-- **Nearest-neighbour components of sets agreeing on a set `C`**: if `T` and `T'` agree on `C`
and the component of `a` in `T` lies in `C`, it lies in the component of `a` in `T'`. -/
theorem nnComp_subset_of_agree {d m : ℕ} {T T' C : Set (Torus d m)} (hTC : ∀ u ∈ C, u ∈ T ↔ u ∈ T')
    {a : Torus d m} (haT' : a ∈ T') (hC : nnComp T a ⊆ C) : nnComp T a ⊆ nnComp T' a := by
  rintro b ⟨hbT, hab⟩
  have key : ∀ v, Relation.ReflTransGen (fun u v => u ∈ T ∧ v ∈ T ∧ NNAdj u v) a v →
      v ∈ nnComp T' a := by
    intro v hv
    induction hv with
    | refl => exact mem_nnComp_self haT'
    | tail hpath hstep ih =>
      have hvC : _ ∈ C := hC ⟨hstep.2.1, hpath.tail hstep⟩
      have hv' := (hTC _ hvC).1 hstep.2.1
      exact ⟨hv', ih.2.tail ⟨ih.1, hv', hstep.2.2⟩⟩
  exact key b hab

section Fine

/-- The cast of tori along an equality of sides preserves the index distance. -/
theorem supDist_castT {d a b : ℕ} (h : a = b) (x y : Torus d a) :
    supDist (Balaban.Localization.castT h x) (Balaban.Localization.castT h y) = supDist x y := by
  subst h; rfl

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M m₀ m₁ : ℕ} [NeZero M]
  [NeZero S.L]

/-- Coarsening a pair of fine sites at distance `≤ 1` gives cubes at distance `≤ 1`. -/
theorem supDist_cubeMap_le_one (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) {k : ℕ} (hkK : k ≤ K)
    {x y : Torus S.d (M * n K * S.L ^ K)} (h : supDist x y ≤ 1) :
    supDist (cubeMap n S.L M K k x) (cubeMap n S.L M K k y) ≤ 1 := by
  have hB : 1 ≤ S.L ^ k * M := Nat.one_le_iff_ne_zero.2 (mul_ne_zero
    (pow_ne_zero _ (NeZero.ne S.L)) (NeZero.ne M))
  have h1 := supDist_blockMap_le (L := S.L ^ k * M) (m := n k) (fine_eq hnn hkK) x y
  unfold cubeMap
  refine h1.trans ?_
  calc (supDist x y + S.L ^ k * M - 1) / (S.L ^ k * M) ≤ (1 + S.L ^ k * M - 1) / (S.L ^ k * M) :=
        Nat.div_le_div_right (by omega)
    _ = 1 := by rw [show 1 + S.L ^ k * M - 1 = S.L ^ k * M by omega, Nat.div_self (by omega)]

/-- Nearest neighbours of the frame torus lie in cubes at distance `≤ 1`. -/
theorem cube_supDist_le_one_of_nbr (F : FineSizeFrame S n M K m₀ m₁)
    (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) {k : ℕ} (hkK : k ≤ K)
    {u v : Balaban.Localization.CTorus S.d S.L F.N₁ m₁ K} (h : Balaban.Localization.Nbr u v) :
    supDist (cubeMap n S.L M K k (Balaban.Localization.castT F.side u))
      (cubeMap n S.L M K k (Balaban.Localization.castT F.side v)) ≤ 1 := by
  have : NeZero (F.N₁ * S.L ^ m₁ * S.L ^ K) :=
    ⟨Nat.mul_ne_zero (Nat.mul_ne_zero F.posN₁.ne' (pow_ne_zero _ (NeZero.ne S.L)))
      (pow_ne_zero _ (NeZero.ne S.L))⟩
  refine supDist_cubeMap_le_one hnn hkK ?_
  rw [supDist_castT]
  exact NNAdj.supDist_le_one h

end Fine

section Corr

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {A B : RegionHistory S n R k0 K} {k : ℕ} (hkK : k ≤ K)
  (hA : ∀ i, i ≤ k → A.rem i = ∅) (hB : ∀ i, i ≤ k → B.rem i = ∅)

include hkK hA hB in
/-- **`Ω_k` over corresponding components** (cube level). -/
theorem omegaCube_iff_of_comp (c : A.Comp k) (c' : B.Comp k) (h1 : c'.1 = c.1)
    (h2 : B.localHistory M K k c' = A.localHistory M K k c) {a : Torus S.d (n k)} (ha : a ∈ c.1) :
    a ∈ OmegaCube A k ↔ a ∈ OmegaCube B k := by
  cases k with
  | zero => exact (A.F.isEmpty_comp_zero.false c).elim
  | succ j =>
    obtain ⟨x, rfl⟩ := exists_site_of_cube (M := M) A.F.hnn hkK a
    change cubeMap n S.L M K (j + 1) x ∈ (A.step j).Omega ↔
      cubeMap n S.L M K (j + 1) x ∈ (B.step j).Omega
    rw [mem_Omega_iff_loc A hkK hA (Nat.lt_succ_self j) c x ha,
      mem_Omega_iff_loc B hkK hB (Nat.lt_succ_self j) c' x (h1 ▸ ha),
      locRH_step_eq_of_localHistory_eq hkK c' c h1 h2 j]

omit [NeZero M] [NeZero S.L] in
/-- Off `Z_k` the cube lies in `Ω_k`. -/
theorem omegaCube_of_not_mem_Zp (H : RegionHistory S n R k0 K) {a : Torus S.d (n k)}
    (ha : a ∉ H.Zp k) : a ∈ OmegaCube H k := by
  cases k with
  | zero => trivial
  | succ j =>
    by_contra h
    exact ha (mem_finOf.mpr (H.OmegaCube_compl_subset_Zpre (Nat.succ_pos j) h))

variable {X : Finset (Torus S.d (n k))}
  (hAB : ∀ c : A.Comp k, (c.1 ∩ X).Nonempty → ∃ c' : B.Comp k, c'.1 = c.1 ∧
    B.localHistory M K k c' = A.localHistory M K k c)
  (hBA : ∀ c' : B.Comp k, (c'.1 ∩ X).Nonempty → ∃ c : A.Comp k, c.1 = c'.1 ∧
    A.localHistory M K k c = B.localHistory M K k c')

omit [NeZero M] [NeZero S.L] in
include hBA in
/-- A cube of `X` off `Z_k(A)` is off `Z_k(B)`. -/
theorem not_mem_Zp_of_corr {a : Torus S.d (n k)} (haX : a ∈ X) (ha : a ∉ A.Zp k) :
    a ∉ B.Zp k := fun hb => by
  obtain ⟨Y', hY', hyY'⟩ := mem_comp_self (ω := S.omega k) hb
  obtain ⟨c, hc1, -⟩ := hBA ⟨Y', hY'⟩ ⟨a, Finset.mem_inter.2 ⟨hyY', haX⟩⟩
  exact ha (comp_subset c.2 (hc1 ▸ hyY'))

include hkK hA hB hAB hBA in
/-- **`Ω_k` on the cubes of `X`.** -/
theorem omegaCube_iff_on_of_corr {a : Torus S.d (n k)} (haX : a ∈ X) :
    a ∈ OmegaCube A k ↔ a ∈ OmegaCube B k := by
  by_cases ha : a ∈ A.Zp k
  · obtain ⟨Y, hY, hyY⟩ := mem_comp_self (ω := S.omega k) ha
    obtain ⟨c', h1, h2⟩ := hAB ⟨Y, hY⟩ ⟨a, Finset.mem_inter.2 ⟨hyY, haX⟩⟩
    exact omegaCube_iff_of_comp hkK hA hB ⟨Y, hY⟩ c' h1 h2 hyY
  · exact iff_of_true (omegaCube_of_not_mem_Zp A ha)
      (omegaCube_of_not_mem_Zp B (not_mem_Zp_of_corr hBA haX ha))

include hkK hA hB hAB hBA in
/-- **The nearest-neighbour components of `Ω_k^c` at the cubes of `X` agree.** -/
theorem nnComp_eq_of_corr {a : Torus S.d (n k)} (haX : a ∈ X) (ha : a ∉ OmegaCube A k) :
    nnComp (OmegaCube A k)ᶜ a = nnComp (OmegaCube B k)ᶜ a := by
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with rfl | h
    · exact absurd trivial ha
    · exact h
  have haZ : a ∈ A.Zp k := mem_finOf.mpr (A.OmegaCube_compl_subset_Zpre hk1 ha)
  obtain ⟨Y, hY, hyY⟩ := mem_comp_self (ω := S.omega k) haZ
  obtain ⟨c', h1, h2⟩ := hAB ⟨Y, hY⟩ ⟨a, Finset.mem_inter.2 ⟨hyY, haX⟩⟩
  have hagree : ∀ u ∈ (Y : Set (Torus S.d (n k))),
      u ∈ (OmegaCube A k)ᶜ ↔ u ∈ (OmegaCube B k)ᶜ := fun u hu =>
    not_congr (omegaCube_iff_of_comp hkK hA hB ⟨Y, hY⟩ c' h1 h2 hu)
  have haB : a ∈ (OmegaCube B k)ᶜ := (hagree a hyY).1 ha
  have hCA : nnComp (OmegaCube A k)ᶜ a ⊆ (Y : Set (Torus S.d (n k))) := fun b hb =>
    A.mem_comp_of_nnPath hY (A.OmegaCube_compl_subset_Zpre hk1) hyY hb.2
  have hCB : nnComp (OmegaCube B k)ᶜ a ⊆ (Y : Set (Torus S.d (n k))) := by
    intro b hb
    have := B.mem_comp_of_nnPath c'.2 (B.OmegaCube_compl_subset_Zpre hk1) (h1 ▸ hyY) hb.2
    rwa [h1] at this
  exact Set.Subset.antisymm (nnComp_subset_of_agree hagree haB hCA)
    (nnComp_subset_of_agree (fun u hu => (hagree u hu).symm) ha hCB)

include hkK hA hB hAB hBA in
/-- One direction of the agreement of `𝒟_k(mod Ω_k^c)`. -/
theorem dmodOmega_of_corr (h : DmodOmega (OmegaCube A k) X) : DmodOmega (OmegaCube B k) X := by
  refine ⟨h.1, fun a ha => ?_⟩
  by_cases hd : Disjoint (nnComp (OmegaCube B k)ᶜ a) (X : Set (Torus S.d (n k)))
  · exact Or.inr hd
  · left
    obtain ⟨b, hbC, hbX⟩ := Set.not_disjoint_iff.1 hd
    have hbB : b ∉ OmegaCube B k := hbC.1
    have hbA : b ∉ OmegaCube A k := fun hb => hbB ((omegaCube_iff_on_of_corr hkK hA hB hAB hBA
      hbX).1 hb)
    rw [← nnComp_eq_of_mem hbC, ← nnComp_eq_of_corr hkK hA hB hAB hBA hbX hbA]
    exact h.comp_subset hbA (mem_nnComp_self hbA) hbX

omit [NeZero M] [NeZero S.L] in
include hA hB hAB hBA in
/-- `X ∩ Z_k` agrees. -/
theorem inter_Z_eq_of_corr :
    (X : Set (Torus S.d (n k))) ∩ (A.step k).Z = (X : Set (Torus S.d (n k))) ∩ (B.step k).Z := by
  ext a
  simp only [Set.mem_inter_iff, Finset.mem_coe]
  refine and_congr_right fun haX => ?_
  rw [A.Z_eq k, B.Z_eq k, hA k le_rfl, hB k le_rfl]
  simp only [Finset.notMem_empty, Set.iUnion_of_empty, Set.iUnion_empty, Set.sdiff_empty]
  constructor
  · intro h
    by_contra hb
    exact not_mem_Zp_of_corr (A := B) (B := A) hAB haX (fun h' => hb (mem_finOf.mp h'))
      (mem_finOf.mpr h)
  · intro h
    by_contra ha
    exact not_mem_Zp_of_corr hBA haX (fun h' => ha (mem_finOf.mp h')) (mem_finOf.mpr h)

include hkK hA hB hAB hBA in
/-- **`X` is a boundary domain of one history iff it is one of the other.** -/
theorem mem_bdryDoms_iff_of_corr :
    X ∈ bdryDoms (OmegaCube A k) (A.step k).Z ↔ X ∈ bdryDoms (OmegaCube B k) (B.step k).Z := by
  rw [mem_bdryDoms, mem_bdryDoms]
  unfold IsBdryDom
  have hZ := inter_Z_eq_of_corr hA hB hAB hBA
  have hZ' : (X : Set (Torus S.d (n k))) \ (A.step k).Z =
      (X : Set (Torus S.d (n k))) \ (B.step k).Z := by
    rw [← Set.sdiff_self_inter, hZ, Set.sdiff_self_inter]
  constructor
  · rintro ⟨hd, h1, h2⟩
    exact ⟨dmodOmega_of_corr hkK hA hB hAB hBA hd, hZ ▸ h1, hZ' ▸ h2⟩
  · rintro ⟨hd, h1, h2⟩
    exact ⟨dmodOmega_of_corr hkK hB hA hBA hAB hd, hZ.symm ▸ h1, hZ'.symm ▸ h2⟩

omit [NeZero S.L] in
/-- Without removals at the scale `k`, the post-removal region is the raw region. -/
theorem omegaPost_eq_of_rem (H : RegionHistory S n R k0 K) (h : H.rem k = ∅) :
    H.omegaPost k = OmegaCube H k := by
  unfold RegionHistory.omegaPost RegionHistory.removedSet
  rw [h]
  simp

variable {m₀ m₁ : ℕ} (F : FineSizeFrame S n M K m₀ m₁)

omit [NeZero S.L] in
/-- A nearest-neighbour path of fine sites in the complement of the fine raw region that starts over
a component stays over it. -/
theorem omegaComp_subset_over (H : RegionHistory S n R k0 K) (hkK : k ≤ K) (hk1 : 1 ≤ k)
    (c : H.Comp k) {z : Balaban.Localization.CTorus S.d S.L F.N₁ m₁ K}
    (hz : cubeMap n S.L M K k (Balaban.Localization.castT F.side z) ∈ c.1) :
    Fluctuation.OmegaComp (d7Pull F k (OmegaCube H k)) z ⊆
      {u | cubeMap n S.L M K k (Balaban.Localization.castT F.side u) ∈ c.1} := by
  have : NeZero S.L := ⟨by have := H.F.ok.two_le_L; omega⟩
  rintro y ⟨-, hzy⟩
  induction hzy with
  | refl => exact hz
  | tail _ hstep ih =>
    have hvZ := H.OmegaCube_compl_subset_Zpre hk1 hstep.2.1
    exact mem_comp_of_close c.2 ih (mem_finOf.mpr hvZ)
      (lt_of_le_of_lt (cube_supDist_le_one_of_nbr F H.F.hnn hkK hstep.2.2)
        (by have := omega_ge_eleven S k; omega))

include hkK hA hB hAB hBA in
/-- **The fine components of `Ω_k^c` at the sites over `X` agree.** -/
theorem omegaComp_eq_of_corr {w : Balaban.Localization.CTorus S.d S.L F.N₁ m₁ K}
    (hwX : w ∈ d7Pull F k (X : Set (Torus S.d (n k)))) (hw : w ∉ d7Pull F k (OmegaCube A k)) :
    Fluctuation.OmegaComp (d7Pull F k (OmegaCube A k)) w =
      Fluctuation.OmegaComp (d7Pull F k (OmegaCube B k)) w := by
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with rfl | h
    · exact absurd trivial hw
    · exact h
  have haZ : cubeMap n S.L M K k (Balaban.Localization.castT F.side w) ∈ A.Zp k :=
    mem_finOf.mpr (A.OmegaCube_compl_subset_Zpre hk1 hw)
  obtain ⟨Y, hY, hyY⟩ := mem_comp_self (ω := S.omega k) haZ
  obtain ⟨c', h1, h2⟩ := hAB ⟨Y, hY⟩ ⟨_, Finset.mem_inter.2 ⟨hyY, hwX⟩⟩
  have hagree : ∀ u ∈ {u : Balaban.Localization.CTorus S.d S.L F.N₁ m₁ K |
      cubeMap n S.L M K k (Balaban.Localization.castT F.side u) ∈ Y},
      u ∈ (d7Pull F k (OmegaCube A k))ᶜ ↔ u ∈ (d7Pull F k (OmegaCube B k))ᶜ := fun u hu =>
    not_congr (omegaCube_iff_of_comp hkK hA hB ⟨Y, hY⟩ c' h1 h2 hu)
  have hwB : w ∈ (d7Pull F k (OmegaCube B k))ᶜ := (hagree w hyY).1 hw
  have hCA := omegaComp_subset_over F A hkK hk1 ⟨Y, hY⟩ (z := w) hyY
  have hCB : Fluctuation.OmegaComp (d7Pull F k (OmegaCube B k)) w ⊆
      {u | cubeMap n S.L M K k (Balaban.Localization.castT F.side u) ∈ Y} := by
    have := omegaComp_subset_over F B hkK hk1 c' (z := w) (h1 ▸ hyY)
    rwa [h1] at this
  exact Set.Subset.antisymm (nnComp_subset_of_agree hagree hwB hCA)
    (nnComp_subset_of_agree (fun u hu => (hagree u hu).symm) hw hCB)

include hkK hA hB hAB hBA in
/-- The fine sets of `X ∩ Ω_k` agree. -/
theorem d7Pull_inter_eq_of_corr :
    d7Pull F k (X : Set (Torus S.d (n k))) ∩ d7Pull F k (OmegaCube A k) =
      d7Pull F k (X : Set (Torus S.d (n k))) ∩ d7Pull F k (OmegaCube B k) := by
  ext u
  simp only [Set.mem_inter_iff]
  exact and_congr_right fun hu => omegaCube_iff_on_of_corr hkK hA hB hAB hBA hu

include hkK hA hB hAB hBA in
/-- One direction of the agreement of the valid labels. -/
theorem fineValidAt_of_corr (h : FineValidAt F k (OmegaCube A k) X) :
    FineValidAt F k (OmegaCube B k) X := by
  obtain ⟨hne, hconn, hcomp, hfin⟩ := h
  refine ⟨hne, hconn, fun z hz => ?_, ?_⟩
  · by_cases hd : Disjoint (Fluctuation.OmegaComp (d7Pull F k (OmegaCube B k)) z)
        (d7Pull F k (X : Set (Torus S.d (n k))))
    · exact Or.inr hd
    · left
      obtain ⟨w, hwC, hwX⟩ := Set.not_disjoint_iff.1 hd
      have hwB : w ∉ d7Pull F k (OmegaCube B k) := hwC.1
      have hwA : w ∉ d7Pull F k (OmegaCube A k) := fun h' =>
        hwB ((omegaCube_iff_on_of_corr hkK hA hB hAB hBA hwX).1 h')
      have e1 : Fluctuation.OmegaComp (d7Pull F k (OmegaCube B k)) w =
          Fluctuation.OmegaComp (d7Pull F k (OmegaCube B k)) z := nnComp_eq_of_mem hwC
      rw [← e1, ← omegaComp_eq_of_corr hkK hA hB hAB hBA F hwX hwA]
      rcases hcomp w hwA with h' | h'
      · exact h'
      · exact absurd hwX (Set.disjoint_left.1 h' (mem_nnComp_self hwA))
  · rwa [← dcovModE_congr_inter (d7Pull_inter_eq_of_corr hkK hA hB hAB hBA F)]

include hkK hA hB hAB hBA in
/-- **`X` is a valid label of one history iff it is one of the other.** -/
theorem fineValidAt_iff_of_corr :
    FineValidAt F k (OmegaCube A k) X ↔ FineValidAt F k (OmegaCube B k) X :=
  ⟨fineValidAt_of_corr hkK hA hB hAB hBA F, fineValidAt_of_corr hkK hB hA hBA hAB F⟩

include hkK hA hB hAB hBA in
/-- **The size of `X` is the same for the two histories.** -/
theorem d7SizeAt_eq_of_corr : d7SizeAt F k (OmegaCube A k) X = d7SizeAt F k (OmegaCube B k) X := by
  unfold d7SizeAt d7SizeAtE
  rw [dcovModE_congr_inter (d7Pull_inter_eq_of_corr hkK hA hB hAB hBA F)]

include hkK hA hB hAB hBA in
/-- **The valid boundary domains agree.** -/
theorem mem_bdryDomsAt_iff_of_corr :
    X ∈ bdryDomsAt F k (OmegaCube A k) (A.step k).Z ↔
      X ∈ bdryDomsAt F k (OmegaCube B k) (B.step k).Z := by
  rw [mem_bdryDomsAt, mem_bdryDomsAt, mem_bdryDoms_iff_of_corr hkK hA hB hAB hBA,
    fineValidAt_iff_of_corr hkK hA hB hAB hBA F]

end Corr

end Balaban.RootFSpine
