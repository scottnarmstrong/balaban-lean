/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.BPrimeRAggregate
public import Balaban.LargeField.Def7WitData

/-!
# `ℬ′` of the step `R` on the boundary domains of `𝕋_k`

The final domains of `ℬ′` (`rDomains`, the sets `Y = X₁ ∪ ⋃ D(P_i)` of the whole-lattice set of the
top level) are unions of cells of side `a_k`, i.e. fine sets of sets `X` of cubes of `𝕋_k`, the
boundary domains of the representation.  Here `ℬ′` is written on them (`rFresh`, the argument `fresh`
of `r4Coupling` / `gasR4Decor_eq`), for the old small-field regions `Yr Γ` of the removal sets `Γ`:

* `SFCtx.tSetOf`, `SFCtx.sset_tSetOf`: a union of cells is the fine set of its cubes;
* `SFCtx.rDomains_cellClosed`, `SFCtx.rDomainsT`;
* `SFCtx.rFresh`, `SFCtx.rFresh_empty` (the hypothesis `hfresh` of `gasR4Decor_eq`);
* `SFCtx.sum_rFresh_eq`: `Σ_X ℬ′_X(Γ) = Σ_Y rBPrime Y`, the aggregate of `rBPrime_aggregate` on the
  boundary domains;
* `volK_sdiff_biUnion`: the vacuum term of the residual is the sum of the volumes of the removed
  components (row (d): it is carried by the removed weights, `VacuumTie.removed_weight_shift`);
* `not_mem_rem_one`, `eq_empty_of_rem_one`, `r4Coupling_rFresh_rem_one`: at the scale `1` the step
  `R` removes nothing (`not_ripe_one`), so `ℬ′` vanishes there.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
  Balaban.SmallField.GsSpec

namespace Def7.SFCtx

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N k m₁ : ℕ} {ϱ : ℝ} (C : SFCtx S n R M K N k m₁ ϱ)

open Classical in
/-- The cubes of `𝕋_k` met by a set of the Def-6 torus. -/
noncomputable def tSetOf (Y : Set (Localization.CTorus S.d S.L C.N₁ m₁ k)) :
    Finset (Torus S.d (n k)) :=
  Finset.univ.filter fun c => ∃ x ∈ Y, C.tCubeOfC x = c

/-- **A union of cells of side `a_k` is the fine set of its cubes of `𝕋_k`.** -/
theorem sset_tSetOf (hMm : C.geo.c * C.geo.M1 = S.L ^ (C.m₀ + m₁))
    {Y : Set (Localization.CTorus S.d S.L C.N₁ m₁ k)}
    (hY : ∀ x ∈ Y, ∀ y, SameCell (cellSide S.L C.m₀ m₁ k) y x → y ∈ Y) :
    C.sset ↑(C.tSetOf Y) = Y := by
  classical
  ext y
  rw [mem_sset_iff_cube, Finset.mem_coe, tSetOf, Finset.mem_filter]
  constructor
  · rintro ⟨-, x, hx, hxy⟩
    refine hY x hx y ?_
    have := (C.tCubeOfC_eq_iff y x).1 hxy.symm
    rwa [← C.cellSide_eq_blk hMm] at this
  · intro hy
    exact ⟨Finset.mem_univ _, y, hy, rfl⟩

/-- **The final domains of `ℬ′` are unions of cells of side `a_k`.** -/
theorem rDomains_cellClosed (hk1 : 1 ≤ k) (hN : S.L ^ C.m₀ ∣ C.N₁)
    {Y : Set (Localization.CTorus S.d S.L C.N₁ m₁ k)} (hY : Y ∈ C.rDomains) :
    ∀ x ∈ Y, ∀ y, SameCell (cellSide S.L C.m₀ m₁ k) y x → y ∈ Y := by
  classical
  unfold rDomains bPrimeDomains polymerDomains at hY
  obtain ⟨r, -, hYr⟩ := Finset.mem_biUnion.1 hY
  obtain ⟨Cf, -, rfl⟩ := Finset.mem_image.1 hYr
  intro x hx y hxy
  have ha := cellSide_dvd (L := S.L) (m₁ := m₁) (K := k) hN (le_refl k)
  have ha0 := cellSide_pos (L := S.L) (m₁ := m₁) C.m₀ k
  rcases hx with hx | hx
  · exact Or.inl (mem_X1_of_sameCell hN hx hxy)
  · right
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.1 hx
    refine Set.mem_iUnion₂.2 ⟨i, hi, ?_⟩
    obtain ⟨b, hb, hxb⟩ := Set.mem_iUnion₂.1 hxi
    refine Set.mem_iUnion₂.2 ⟨b, hb, ?_⟩
    have hk : (i.1 : ℕ × Localization.CTorus S.d S.L C.N₁ m₁ k).1 = k :=
      level_eq_of_mem_cubeIdx (C.isLevel_rLevelGS hk1) (rootLabs_mem i)
    dsimp only at hb hxb ⊢
    have hbA : Localization.Aligned (cellSide S.L C.m₀ m₁ k) b := by
      have h1 := hb.1
      rw [hk] at h1
      exact h1
    rw [hk] at hxb ⊢
    have hcell := cell_subset_cube ha ha0 hbA hxb
    exact hcell ((Def7.SFCtx.mem_box_cbase_iff ha ha0 x y).2 hxy)

open Classical in
/-- The final domains of `ℬ′` as sets of cubes of `𝕋_k`. -/
noncomputable def rDomainsT : Finset (Finset (Torus S.d (n k))) := C.rDomains.image C.tSetOf

variable (hv : EuclideanSpace ℝ (Fin N)) (vc : Def7v2.CorrCoef S.d) (g : GIdx S n M K N → ℂ)

/-- **`ℬ′_X(Γ)` of the step `R` on a boundary domain `X ⊂ 𝕋_k`**: `rBPrime` for the old small-field
region `Yr Γ` of the removal set `Γ` and the new region `Y₂`, at the fine set of `X`. -/
noncomputable def rFresh {Zt : Type*} (Yr : Finset Zt → Set (Torus S.d (n k)))
    (Y₂ : Set (Torus S.d (n k))) (a₁ ν rho : ℝ) (u : BlockAt S n M K k → Fin N → ℂ)
    (X : Finset (Torus S.d (n k))) (Γ : Finset Zt) : ℂ :=
  C.rBPrime (Yr Γ) Y₂ hv vc g a₁ ν rho Γ (C.sset ↑X) u

/-- **`ℬ′` vanishes for no removed member** (`hfresh` of `gasR4Decor_eq`), when the old region of
the empty removal set is the new region. -/
theorem rFresh_empty {Zt : Type*} {Yr : Finset Zt → Set (Torus S.d (n k))}
    {Y₂ : Set (Torus S.d (n k))} (hYr : Yr ∅ = Y₂) (a₁ ν rho : ℝ)
    (u : BlockAt S n M K k → Fin N → ℂ) (X : Finset (Torus S.d (n k))) :
    C.rFresh hv vc g Yr Y₂ a₁ ν rho u X ∅ = 0 := by
  unfold rFresh
  rw [hYr]
  exact C.rBPrime_self hv vc g Y₂ a₁ ν rho ∅ _ u

/-- **The aggregate of `ℬ′` on the boundary domains**: the sum of `ℬ′_X(Γ)` over the final domains
`X ⊂ 𝕋_k` is the sum of `rBPrime` over the final domains `Y` (the left side of
`rBPrime_aggregate` (1)). -/
theorem sum_rFresh_eq (hk1 : 1 ≤ k) (hN : S.L ^ C.m₀ ∣ C.N₁)
    (hMm : C.geo.c * C.geo.M1 = S.L ^ (C.m₀ + m₁)) {Zt : Type*}
    (Yr : Finset Zt → Set (Torus S.d (n k))) (Y₂ : Set (Torus S.d (n k))) (a₁ ν rho : ℝ)
    (u : BlockAt S n M K k → Fin N → ℂ) (Γ : Finset Zt) :
    ∑ X ∈ C.rDomainsT, C.rFresh hv vc g Yr Y₂ a₁ ν rho u X Γ =
      ∑ Y ∈ C.rDomains, C.rBPrime (Yr Γ) Y₂ hv vc g a₁ ν rho Γ Y u := by
  classical
  have hsset : ∀ Y ∈ C.rDomains, C.sset ↑(C.tSetOf Y) = Y := fun Y hY =>
    C.sset_tSetOf hMm (C.rDomains_cellClosed hk1 hN hY)
  unfold rDomainsT
  rw [Finset.sum_image]
  · refine Finset.sum_congr rfl fun Y hY => ?_
    unfold rFresh
    rw [hsset Y hY]
  · intro Y hY Y' hY' h
    rw [← hsset Y hY, ← hsset Y' hY']
    exact congrArg (fun X : Finset (Torus S.d (n k)) => C.sset ↑X) h

/-- **The decorated coupling of the step `R` vanishes for no removed member** (P7 (3.26) with
`fresh = ℬ′`): the hypothesis of `gasDecor_eq` / `gasR4Decor_eq`, for any old and kept boundary terms
with `old x ∅ = kept x` (e.g. `old x Γ = ℬ(X, 𝔸′ ∪ Γ)`, `kept x = ℬ̂(X; 𝔸′)`). -/
theorem r4Coupling_rFresh_empty {Zt Xt : Type*} {Yr : Finset Zt → Set (Torus S.d (n k))}
    {Y₂ : Set (Torus S.d (n k))} (hYr : Yr ∅ = Y₂) (a₁ ν rho : ℝ)
    (u : BlockAt S n M K k → Fin N → ℂ) (dom : Xt → Finset (Torus S.d (n k)))
    (old : Xt → Finset Zt → ℂ) (kept : Xt → ℂ) (hbase : ∀ x, old x ∅ = kept x) (x : Xt) :
    r4Coupling old (fun x Γ => C.rFresh hv vc g Yr Y₂ a₁ ν rho u (dom x) Γ) kept x ∅ = 0 :=
  r4Coupling_empty old _ kept hbase (fun x => C.rFresh_empty hv vc g hYr a₁ ν rho u (dom x)) x

end Def7.SFCtx

/-! ### The scale `k = 1`: `R` removes nothing -/

section KOne

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}

/-- **At the scale `1` the step `R` removes nothing** (LFR Part I §I.5.5, base: no component of
`Z^pre_1` is ripe, `t^* ≥ 1 + n_q(1) > 1`, `Def7.not_ripe_one`; a removed component is ripe,
`RegionHistory.Admissible`). -/
theorem not_mem_rem_one (G : S.Good) {H : RegionHistory S n R k0 K} (hH : H.Admissible)
    (hK : 1 ≤ K) (c : H.Comp 1) : c.1 ∉ H.rem 1 :=
  fun hc => Def7.not_ripe_one G H hK c (hH 1 c hc)

/-- Every family of removed components of the scale `1` is empty. -/
theorem eq_empty_of_rem_one (G : S.Good) {H : RegionHistory S n R k0 K} (hH : H.Admissible)
    (hK : 1 ≤ K) {Γ : Finset (H.Comp 1)} (hΓ : ∀ c ∈ Γ, c.1 ∈ H.rem 1) : Γ = ∅ :=
  Finset.eq_empty_of_forall_notMem fun c hc => not_mem_rem_one G hH hK c (hΓ c hc)

variable {M : ℕ} [NeZero M] [NeZero S.L] {N m₁ : ℕ} {ϱ : ℝ}

/-- **`ℬ′` vanishes at the scale `1`**: the coupling `r4Coupling` of the removed components of a
scale-`1` history, with `fresh = ℬ′ = rFresh`, is `0` (`eq_empty_of_rem_one`,
`r4Coupling_rFresh_empty`): the step `R` with ripe components, where `rBPrime_aggregate` is used,
has `k ≥ 2`. -/
theorem r4Coupling_rFresh_rem_one (C : Def7.SFCtx S n R M K N 1 m₁ ϱ)
    (hv : EuclideanSpace ℝ (Fin N)) (vc : Def7v2.CorrCoef S.d) (g : GIdx S n M K N → ℂ)
    (G : S.Good) {H : RegionHistory S n R k0 K} (hH : H.Admissible) (hK : 1 ≤ K) {Xt : Type*}
    {Yr : Finset (H.Comp 1) → Set (Torus S.d (n 1))} {Y₂ : Set (Torus S.d (n 1))}
    (hYr : Yr ∅ = Y₂) (a₁ ν rho : ℝ) (u : BlockAt S n M K 1 → Fin N → ℂ)
    (dom : Xt → Finset (Torus S.d (n 1))) (old : Xt → Finset (H.Comp 1) → ℂ) (kept : Xt → ℂ)
    (hbase : ∀ x, old x ∅ = kept x) (x : Xt) {Γ : Finset (H.Comp 1)}
    (hΓ : ∀ c ∈ Γ, c.1 ∈ H.rem 1) :
    r4Coupling old (fun x Γ => C.rFresh hv vc g Yr Y₂ a₁ ν rho u (dom x) Γ) kept x Γ = 0 := by
  rw [eq_empty_of_rem_one G hH hK hΓ]
  exact C.r4Coupling_rFresh_empty hv vc g hYr a₁ ν rho u dom old kept hbase x

end KOne

/-! ### The vacuum term of the residual (row (d)) -/

section Vacuum

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {k : ℕ}

/-- **The vacuum term of the residual is the sum of the volumes of the removed components**: for
pairwise disjoint removed regions `Z_m ⊂ Y₂`, `|Y₂| - |Y₂ ∖ ⋃_m Z_m| = Σ_m |Z_m|` (in scale-`k`
units). -/
theorem volK_sdiff_biUnion (M : ℕ) {ι : Type*} (Y₂ : Set (Torus S.d (n k)))
    (Z : ι → Set (Torus S.d (n k))) (Γ : Finset ι) (hZ : ∀ m ∈ Γ, Z m ⊆ Y₂)
    (hdisj : (Γ : Set ι).PairwiseDisjoint Z) :
    Def7.volK (S := S) M Y₂ - Def7.volK (S := S) M (Y₂ \ ⋃ m ∈ Γ, Z m) =
      ∑ m ∈ Γ, Def7.volK (S := S) M (Z m) := by
  classical
  unfold Def7.volK
  have hU : (⋃ m ∈ Γ, Z m) ⊆ Y₂ := Set.iUnion₂_subset hZ
  have h1 : ((Y₂ \ ⋃ m ∈ Γ, Z m).ncard : ℝ) + ((⋃ m ∈ Γ, Z m).ncard : ℝ) = (Y₂.ncard : ℝ) := by
    exact_mod_cast Set.ncard_sdiff_add_ncard_of_subset hU (Set.toFinite _)
  have h2 : ((⋃ m ∈ Γ, Z m).ncard : ℝ) = ∑ m ∈ Γ, ((Z m).ncard : ℝ) := by
    have e : (⋃ m ∈ Γ, Z m) = ↑(Γ.biUnion fun m => (Z m).toFinset) := by
      ext x; simp
    rw [e, Set.ncard_coe_finset, Finset.card_biUnion]
    · push_cast
      exact Finset.sum_congr rfl fun m _ => by rw [Set.ncard_eq_toFinset_card']
    · intro m hm m' hm' hne
      exact Set.disjoint_toFinset.2 (hdisj hm hm' hne)
  rw [← Finset.sum_mul, ← h2, ← sub_mul]
  congr 1
  linarith

end Vacuum

end Balaban.LargeField
