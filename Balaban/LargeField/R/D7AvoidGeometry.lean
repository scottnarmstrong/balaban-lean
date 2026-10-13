/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Def7FineSize

/-!
# Labels of the boundary terms that avoid the components removed by `R`

The operation `R` removes the ripe components `Rem_k` of the large-field region at scale `k`;
the post-removal small-field region is `Ω_k^post = Ω_k^pre ∪ ⋃ Rem_k`
(`RegionHistory.omegaPost`, `removedSet`).  VMOD-40 §1 (P7 (3.26)-(3.28)): a boundary term whose
label `X` is disjoint from every removed component is untouched by `R`.  This file proves the
geometry of such labels, with no analysis:

* `inter_omegaPost_of_disjoint`, `d7Pull_inter_omegaPost_of_disjoint` (T1): for a label `X`
  disjoint from the removed set, `X ∩ Ω_k^post = X ∩ Ω_k^pre`, and the same for the fine lifts.
* `dcovModE_congr_inter` (T2): the modular covering size `d^cov_j(X mod Ω^c)` depends on `Ω` only
  through `X ∩ Ω`.  Hence `d7SizeE_eq_d7SizePreE_of_disjoint` and
  `d7Size_eq_d7SizePre_of_disjoint`: for a label avoiding the removed set the sizes before and
  after `R` are equal.
* T3: validity.  `fineValid_of_fineValidPre` (landed) gives `FineValidPre -> FineValid`.  The
  converse can fail, and the failure is exactly the following.  A connected component of the
  complement of the raw (pre-`R`) fine region may contain removed cells; after `R` it splits into
  several components of the complement of the post region.  A label that contains some of these
  pieces and misses others is post-valid and need not be pre-valid.
  `djMod_of_post_of_comp_avoids` / `fineValidPre_of_fineValid_of_comp_avoids`: post-validity
  gives pre-validity when every raw complement component that meets `X_f` without being
  contained in `X_f` avoids the removed cells.  `exists_split_comp_of_fineValid_not_pre` is the
  converse: a post-valid, not pre-valid label has such a component, and it meets the removed
  cells.

Only the geometry of labels is proved here.  `Balaban.LargeField.R.D7BoundTransport` uses it to
transport the bound field of the boundary-term record.
-/

@[expose] public section

namespace Balaban.LargeField.Def7

open Balaban Balaban.Localization RegionHistory

/-! ### Fine lifts and unions -/

section Pull

variable {S : Setting} {n : ℕ → ℕ} {M K m₀ m₁ : ℕ}

theorem d7Pull_union (F : FineSizeFrame S n M K m₀ m₁) (j : ℕ) (Y Y' : Set (Torus S.d (n j))) :
    d7Pull F j (Y ∪ Y') = d7Pull F j Y ∪ d7Pull F j Y' := rfl

end Pull

/-! ### T1: the regions seen from a label avoiding the removed set -/

section Regions

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M m₀ m₁ : ℕ}

/-- **T1.** For a set `X` of cubes disjoint from the removed components, `X ∩ Ω_k^post` equals
`X ∩ Ω_k^pre`. -/
theorem inter_omegaPost_of_disjoint (H : RegionHistory S n R k0 K) (k : ℕ)
    {X : Set (Torus S.d (n k))} (h : Disjoint X (H.removedSet k)) :
    X ∩ H.omegaPost k = X ∩ OmegaCube H k := by
  ext x
  simp only [omegaPost, Set.mem_inter_iff, Set.mem_union]
  constructor
  · rintro ⟨hx, hx' | hx'⟩
    · exact ⟨hx, hx'⟩
    · exact absurd hx' (Set.disjoint_left.1 h hx)
  · rintro ⟨hx, hx'⟩
    exact ⟨hx, Or.inl hx'⟩

/-- **T1, fine lifts.** For `X` disjoint from the removed components the fine sets satisfy
`X_f ∩ Ω_f^post = X_f ∩ Ω_f^pre`. -/
theorem d7Pull_inter_omegaPost_of_disjoint (F : FineSizeFrame S n M K m₀ m₁)
    (H : RegionHistory S n R k0 K) (k : ℕ) {X : Set (Torus S.d (n k))}
    (h : Disjoint X (H.removedSet k)) :
    d7Pull F k X ∩ d7Pull F k (H.omegaPost k) = d7Pull F k X ∩ d7Pull F k (OmegaCube H k) := by
  rw [← d7Pull_inter, ← d7Pull_inter, inter_omegaPost_of_disjoint H k h]

end Regions

/-! ### T2: the modular size depends on `Ω` only through `X ∩ Ω` -/

section Size

variable {d L N₁ m₁ K j : ℕ} [NeZero N₁] [NeZero L] {m₀ : ℕ}

omit [NeZero N₁] [NeZero L] in
theorem modAdmissible_congr_inter {Ω Ω' X 𝒦 : Set (Localization.CTorus d L N₁ m₁ K)}
    {W : Finset (Localization.CTorus d L N₁ m₁ K)} {E : Finset (Localization.CTorus d L N₁ m₁ K × Localization.CTorus d L N₁ m₁ K)}
    (h : X ∩ Ω = X ∩ Ω') (hE : Fluctuation.ModAdmissible m₀ j Ω X 𝒦 W E) :
    Fluctuation.ModAdmissible m₀ j Ω' X 𝒦 W E :=
  ⟨hE.1, h ▸ hE.2.1, hE.2.2⟩

omit [NeZero N₁] [NeZero L] in
/-- **T2.** The modular covering size `d^cov_j(X mod Ω^c)` depends on `Ω` only through
`X ∩ Ω` (the cover clause of `ModAdmissible` is `X ∩ Ω ⊆ ⋃ boxes`, every other clause is about
`X`). -/
theorem dcovModE_congr_inter {Ω Ω' X : Set (Localization.CTorus d L N₁ m₁ K)} (h : X ∩ Ω = X ∩ Ω') :
    Fluctuation.dcovModE m₀ j Ω X = Fluctuation.dcovModE m₀ j Ω' X := by
  refine le_antisymm ?_ ?_
  · refine le_iInf fun 𝒦 => le_iInf fun W => le_iInf fun E => le_iInf fun hE => ?_
    exact Fluctuation.dcovModE_le_of_admissible (modAdmissible_congr_inter h.symm hE)
  · refine le_iInf fun 𝒦 => le_iInf fun W => le_iInf fun E => le_iInf fun hE => ?_
    exact Fluctuation.dcovModE_le_of_admissible (modAdmissible_congr_inter h hE)

end Size

section Sizes

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] [NeZero S.L] {R : ℕ → ℝ}
  {k0 K M m₀ m₁ : ℕ} {k : ℕ}

/-- **T2, in `[0, ∞]`.**  For a label disjoint from the removed components the size after `R`
equals the size before `R`. -/
theorem d7SizeE_eq_d7SizePreE_of_disjoint (F : FineSizeFrame S n M K m₀ m₁)
    (A : LabHist S n R k0 K) (X : Finset (Torus S.d (n k)))
    (h : Disjoint (X : Set (Torus S.d (n k))) (A.H.removedSet k)) :
    d7SizeE F A k X = d7SizePreE F A k X :=
  dcovModE_congr_inter (d7Pull_inter_omegaPost_of_disjoint F A.H k h)

/-- **T2.**  For a label disjoint from the removed components the real sizes `d7Size` and
`d7SizePre` are equal. -/
theorem d7Size_eq_d7SizePre_of_disjoint (F : FineSizeFrame S n M K m₀ m₁)
    (A : LabHist S n R k0 K) (X : Finset (Torus S.d (n k)))
    (h : Disjoint (X : Set (Torus S.d (n k))) (A.H.removedSet k)) :
    d7Size F A k X = d7SizePre F A k X := by
  unfold d7Size d7SizePre d7SizeAt
  rw [show d7SizeAtE F k (A.H.omegaPost k) X = d7SizeAtE F k (OmegaCube A.H k) X from
    d7SizeE_eq_d7SizePreE_of_disjoint F A X h]

end Sizes

/-! ### T3: validity of a label avoiding the removed set -/

section Valid

variable {d L N₁ m₁ K j : ℕ} [NeZero N₁] [NeZero L] {m₀ : ℕ}

omit [NeZero N₁] [NeZero L] in
/-- The component of a site of the raw complement lies in its component in the post complement,
when it contains no cell of `C`. -/
theorem omegaComp_subset_of_disjoint {Ω C : Set (Localization.CTorus d L N₁ m₁ K)}
    {z : Localization.CTorus d L N₁ m₁ K} (hz : z ∈ Ωᶜ)
    (hC : Disjoint (Fluctuation.OmegaComp Ω z) C) :
    Fluctuation.OmegaComp Ω z ⊆ Fluctuation.OmegaComp (Ω ∪ C) z := by
  have key : ∀ y, Relation.ReflTransGen (fun u v => u ∈ Ωᶜ ∧ v ∈ Ωᶜ ∧ Nbr u v) z y →
      Relation.ReflTransGen (fun u v => u ∈ (Ω ∪ C)ᶜ ∧ v ∈ (Ω ∪ C)ᶜ ∧ Nbr u v) z y := by
    intro y hy
    induction hy with
    | refl => exact Relation.ReflTransGen.refl
    | tail hab hbc ih =>
      rename_i b c
      have hb : b ∈ Fluctuation.OmegaComp Ω z := ⟨hbc.1, hab⟩
      have hc : c ∈ Fluctuation.OmegaComp Ω z := ⟨hbc.2.1, hab.tail hbc⟩
      exact ih.tail ⟨fun h => h.elim hbc.1 (Set.disjoint_left.1 hC hb), fun h =>
        h.elim hbc.2.1 (Set.disjoint_left.1 hC hc), hbc.2.2⟩
  have _ := hz
  rintro y ⟨hy, hzy⟩
  exact ⟨fun h => h.elim hy (Set.disjoint_left.1 hC ⟨hy, hzy⟩), key y hzy⟩

omit [NeZero N₁] [NeZero L] in
/-- **T3 (geometry).**  Let `Ω_+ = Ω ∪ C`.  If `X ∈ 𝒟_j(mod Ω_+^c)` and every component of
`Ω^c` that meets `X` without being contained in `X` contains no cell of `C`, then
`X ∈ 𝒟_j(mod Ω^c)`. -/
theorem djMod_of_post_of_comp_avoids {Ω C X : Set (Localization.CTorus d L N₁ m₁ K)}
    (hpost : Fluctuation.DjMod m₀ j (Ω ∪ C) X)
    (h : ∀ z ∈ Ωᶜ, (Fluctuation.OmegaComp Ω z ∩ X).Nonempty →
      ¬ Fluctuation.OmegaComp Ω z ⊆ X → Disjoint (Fluctuation.OmegaComp Ω z) C) :
    Fluctuation.DjMod m₀ j Ω X := by
  refine ⟨hpost.1, fun z hz => ?_⟩
  by_cases hsub : Fluctuation.OmegaComp Ω z ⊆ X
  · exact Or.inl hsub
  by_cases hd : Disjoint (Fluctuation.OmegaComp Ω z) X
  · exact Or.inr hd
  exfalso
  have hne : (Fluctuation.OmegaComp Ω z ∩ X).Nonempty := Set.not_disjoint_iff_nonempty_inter.1 hd
  have hC := h z hz hne hsub
  have hzC : z ∈ (Ω ∪ C)ᶜ := fun h' =>
    h'.elim hz (Set.disjoint_left.1 hC ⟨hz, Relation.ReflTransGen.refl⟩)
  have hsub' := omegaComp_subset_of_disjoint hz hC
  rcases hpost.2 z hzC with h1 | h1
  · exact hsub (hsub'.trans h1)
  · obtain ⟨y, hy1, hy2⟩ := hne
    exact Set.disjoint_left.1 h1 (hsub' hy1) hy2

omit [NeZero N₁] [NeZero L] in
/-- **T3 (failure).**  If `X ∈ 𝒟_j(mod (Ω ∪ C)^c)` but `X ∉ 𝒟_j(mod Ω^c)`, some component of
`Ω^c` meets `X`, is not contained in `X`, and contains a cell of `C`: removal split a component
of `Ω^c` into pieces, some in `X` and some not. -/
theorem exists_split_comp_of_djMod_not {Ω C X : Set (Localization.CTorus d L N₁ m₁ K)}
    (hpost : Fluctuation.DjMod m₀ j (Ω ∪ C) X) (hnot : ¬ Fluctuation.DjMod m₀ j Ω X) :
    ∃ z ∈ Ωᶜ, (Fluctuation.OmegaComp Ω z ∩ X).Nonempty ∧
      ¬ Fluctuation.OmegaComp Ω z ⊆ X ∧ ¬ Disjoint (Fluctuation.OmegaComp Ω z) C := by
  by_contra hcon
  refine hnot (djMod_of_post_of_comp_avoids hpost fun z hz hne hsub => ?_)
  by_contra hd
  exact hcon ⟨z, hz, hne, hsub, hd⟩

end Valid

section ValidLabels

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] [NeZero S.L] {R : ℕ → ℝ}
  {k0 K M m₀ m₁ : ℕ} {k : ℕ}

/-- **T3.**  A post-valid label is pre-valid when every component of the complement of the raw
fine region that meets `X_f` without being contained in `X_f` contains no removed cell.  (The
labels `X` avoiding the removed set need no separate hypothesis: the condition is on the
components.) -/
theorem fineValidPre_of_fineValid_of_comp_avoids (F : FineSizeFrame S n M K m₀ m₁)
    (A : LabHist S n R k0 K) (X : Finset (Torus S.d (n k))) (hv : FineValid F A k X)
    (h : ∀ z ∈ (d7Pull F k (OmegaCube A.H k))ᶜ,
      (Fluctuation.OmegaComp (d7Pull F k (OmegaCube A.H k)) z ∩
        d7Pull F k (X : Set (Torus S.d (n k)))).Nonempty →
      ¬ Fluctuation.OmegaComp (d7Pull F k (OmegaCube A.H k)) z ⊆
        d7Pull F k (X : Set (Torus S.d (n k))) →
      Disjoint (Fluctuation.OmegaComp (d7Pull F k (OmegaCube A.H k)) z)
        (d7Pull F k (A.H.removedSet k))) :
    FineValidPre F A k X :=
  fineValidPre_of_djMod F A (djMod_of_post_of_comp_avoids hv.1 h)

/-- **T3 (failure of the converse).**  A label that is post-valid but not pre-valid has a
component of the raw fine complement meeting `X_f`, not contained in `X_f`, and containing a
removed cell. -/
theorem exists_split_comp_of_fineValid_not_pre (F : FineSizeFrame S n M K m₀ m₁)
    (A : LabHist S n R k0 K) (X : Finset (Torus S.d (n k))) (hv : FineValid F A k X)
    (hn : ¬ FineValidPre F A k X) :
    ∃ z ∈ (d7Pull F k (OmegaCube A.H k))ᶜ,
      (Fluctuation.OmegaComp (d7Pull F k (OmegaCube A.H k)) z ∩
        d7Pull F k (X : Set (Torus S.d (n k)))).Nonempty ∧
      ¬ Fluctuation.OmegaComp (d7Pull F k (OmegaCube A.H k)) z ⊆
        d7Pull F k (X : Set (Torus S.d (n k))) ∧
      ¬ Disjoint (Fluctuation.OmegaComp (d7Pull F k (OmegaCube A.H k)) z)
        (d7Pull F k (A.H.removedSet k)) :=
  exists_split_comp_of_djMod_not hv.1 fun hd => hn (fineValidPre_of_djMod F A hd)

/-- **T3.**  For a label avoiding the removed set, pre-validity implies post-validity (landed
as `fineValid_of_fineValidPre` for every label), and a pre-valid label is a post-valid one with
the same size. -/
theorem fineValid_and_size_of_fineValidPre_of_disjoint (F : FineSizeFrame S n M K m₀ m₁)
    (A : LabHist S n R k0 K) (X : Finset (Torus S.d (n k)))
    (h : Disjoint (X : Set (Torus S.d (n k))) (A.H.removedSet k)) (hv : FineValidPre F A k X) :
    FineValid F A k X ∧ d7Size F A k X = d7SizePre F A k X :=
  ⟨fineValid_of_fineValidPre hv, d7Size_eq_d7SizePre_of_disjoint F A X h⟩

end ValidLabels

end Balaban.LargeField.Def7
