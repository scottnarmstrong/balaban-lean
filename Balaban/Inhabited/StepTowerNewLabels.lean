/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepTowerNewLabelsHull
public import Balaban.Fluctuation.LocalClassDensityHZero
public import Balaban.Fluctuation.LocalClassDensityValClass

/-!
# The energy labels of the new level from the class chain, on the step chart
(`StepTowerNewLabels`)

The class chain at the tower (`e0CoeffFamily_class_exists_tower_struct_step`, at `d = L = 3`,
`N = 2`, `eps = T.t`) gives, with one representative bundle `Jr` and root by root, a coefficient
family `e z θ T′` over the sets `T′` of level-`(k+1)` cubes of index one: analytic on the parameters
`physV` of the step chart, bounded there by a number `b z T′`, non-zero only on rooted polymers of
index one, and summing at every datum of the chart to the representative `E0locJ C z` of the per-block
density `ℰ₀^{(k+1)}(z)` of the step (P4 (2.56)–(2.60): determinant, fluctuation and the marked
inherited energy).

**The labels.**  The labels are the cube sets `T′` (`𝒯E = Finset.univ`); the label `T′` lives on the
polymer `Y(T′) = sitesOf (piHull m₀ (sitesOf T′))` of index `m₀` (the `π′`-hull,
`StepTowerNewLabelsHull.lean`) and its centre is the block of the site:
`Tl T′ y Y q = e (blockIndex y) (π (clipRaw 𝔹 q), 0) T′` if `Y = Y(T′)`, `0` otherwise, with
`𝔹 = S.G'` and `π` a continuous linear projection onto `rawSub` (`exists_rawSub_proj`).  The
per-label bound is `EbE T′ y Y = b (blockIndex y) T′` if `Y = Y(T′)`, `0` otherwise.  Both are fixed
by their defining equations (`hTl`, `hEbE`), as the averages `AE` are fixed by `hAE` in
`localClass_newLevel_of_expansion`.

`newLabels_stepChart_of_rootFamily`: on the step chart `Ξ^c_{k+1}(𝔹; 1, ε)`, `ε ≤ eps`,
* the labels depend on the centre only through its block (`hTlblock`);
* a non-zero label lives on a polymer of index `m₀` containing its centre;
* the labels are analytic and bounded by `EbE`;
* **the expansion identity** `Σ_{Y ∋ y} Σ_{T′} Tl T′ y Y q = densE0 C y q` (the form of `hDz`,
  with the density `densE0`, whose block dependence `hDzblock` is the landed `densE0_block`).

`newLabels_hDz_of_radius`: the premise `hDz` of `localClass_newLevel_of_expansion(_rho)` verbatim
(class domain `xiFieldDom S.a S.ν (P.eps d L)` at `levelGS (k + 1)`) when `S.G' = levelGS (k + 1)`
(true by definition at the tower) and `P.eps d L (k + 1) ≤ eps`.  The last condition fails for the
towers of the landed interface (`StepTowerNewLabelsRadius.lean`, `not_newLevel_cover_and_room`).

Not here: the counterterms and the field-substitution terms of P4 (4.14)–(4.20) (`densE0` is the
`ξ = 0` part of the density of P4 (4.22) before the vacuum subtraction); the labels on the local
charts of `𝔹_{k+1}(Y⁺)` (the recomputed terms and the replacement identity); the per-centre sum
`hsum`; `hDzfull`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Fluctuation Balaban.Multiscale Balaban.Background Balaban.Localization
  Balaban.SmallField Balaban.SmallField.Def6 Balaban.SmallField.Def6v2

section Labels

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ eps pp : ℝ}
  {S : StepSetting d L N₁ m₁ k N ϱ} (Jr : S.JointRep eps pp) (C : StepClass d L N₁ m₁ k N ϱ)

/-- At a pair of the step chart the cut-off lies in `rawSub`, the projection fixes it, and the
parameter with zero source lies in `physV`. -/
theorem clipRaw_physV_of_xiDom
    (π : RawData d L (N₁ * L ^ m₁) (k + 1) N →L[ℂ] rawSub N S.G')
    (hπ : ∀ r (h : r ∈ rawSub N S.G'), π r = ⟨r, h⟩) {ε : ℝ} (hε : ε ≤ eps)
    {q : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N}
    (hq : XiDom S.G' S.a S.ν (k + 1) ε q.1 q.2) :
    ∃ h : clipRaw S.G' q ∈ rawSub N S.G', π (clipRaw S.G' q) = ⟨clipRaw S.G' q, h⟩ ∧
      ((⟨clipRaw S.G' q, h⟩ : rawSub N S.G'),
        (0 : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)) ∈ physV S S.a₁ S.ν eps := by
  obtain ⟨D, hD, hcl⟩ := clipRaw_mem_xiCRaw_of_xiDom hε hq
  have hmem : clipRaw S.G' q ∈ rawSub N S.G' := hcl ▸ rawOf_mem_rawSub D
  refine ⟨hmem, hπ _ hmem, ?_⟩
  have hsub : (⟨clipRaw S.G' q, hmem⟩ : rawSub N S.G') = ⟨rawOf D, rawOf_mem_rawSub D⟩ :=
    Subtype.ext hcl
  rw [hsub]
  exact StepSetting.JointRep.rawOf_zero_mem_physV hD

/-- **The labels depend on the centre only through its block** (the input `hTlblock`). -/
theorem newLabels_block
    (π : RawData d L (N₁ * L ^ m₁) (k + 1) N →L[ℂ] rawSub N S.G') {m₀ : ℕ}
    (e : RootIdx d L N₁ m₁ (k + 1) → physParam N S →
      Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1) Set.univ) →
        ℂ)
    (Tl : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1)
        Set.univ) → CTorus d L N₁ m₁ (k + 1) → Set (CTorus d L N₁ m₁ (k + 1)) →
      Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N → ℂ)
    (hTl : ∀ T y Y q, Tl T y Y q =
      if sitesOf (piHull m₀ (sitesOf T)) = Y then e (blockIndex y) (π (clipRaw S.G' q), 0) T
      else 0) :
    ∀ T ∈ (Finset.univ : Finset (Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
        (K := k + 1) 1 (k + 1) Set.univ))), ∀ y y' Y q,
      blockBase (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L (k + 1) y =
        blockBase (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L (k + 1) y' →
      Tl T y Y q = Tl T y' Y q := by
  intro T _ y y' Y q hyy
  have hb : blockIndex y = blockIndex y' :=
    rootSite_injective (by rw [rootSite_blockIndex, rootSite_blockIndex, hyy])
  rw [hTl, hTl, hb]

/-- **A non-zero label lives on a polymer of index `m₀` containing its centre.** -/
theorem newLabels_support {m₀ : ℕ} (hN : L ^ m₀ ∣ N₁)
    (π : RawData d L (N₁ * L ^ m₁) (k + 1) N →L[ℂ] rawSub N S.G')
    (e : RootIdx d L N₁ m₁ (k + 1) → physParam N S →
      Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1) Set.univ) →
        ℂ)
    (hsupp : ∀ z θ T, e z θ T ≠ 0 →
      rootCube (m₀ := 1) z ∈ T ∧ IsPolyDom 1 (k + 1) (sitesOf T))
    (Tl : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1)
        Set.univ) → CTorus d L N₁ m₁ (k + 1) → Set (CTorus d L N₁ m₁ (k + 1)) →
      Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N → ℂ)
    (hTl : ∀ T y Y q, Tl T y Y q =
      if sitesOf (piHull m₀ (sitesOf T)) = Y then e (blockIndex y) (π (clipRaw S.G' q), 0) T
      else 0) :
    ∀ T y Y q, Tl T y Y q ≠ 0 → IsPolyDom m₀ (k + 1) Y ∧ y ∈ Y := by
  intro T y Y q h
  rw [hTl] at h
  split_ifs at h with hY
  · obtain ⟨hr, hp⟩ := hsupp _ _ _ h
    subst hY
    exact rootHull_mem hN y hr hp
  · exact absurd rfl h

/-- **The labels are analytic on the step chart** `Ξ^c_{k+1}(𝔹; 1, ε)`, `ε ≤ eps`. -/
theorem newLabels_analytic {m₀ : ℕ}
    (π : RawData d L (N₁ * L ^ m₁) (k + 1) N →L[ℂ] rawSub N S.G')
    (hπ : ∀ r (h : r ∈ rawSub N S.G'), π r = ⟨r, h⟩)
    (e : RootIdx d L N₁ m₁ (k + 1) → physParam N S →
      Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1) Set.univ) →
        ℂ)
    (hean : ∀ z T, AnalyticOnNhd ℂ (fun θ => e z θ T) (physV S S.a₁ S.ν eps))
    (Tl : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1)
        Set.univ) → CTorus d L N₁ m₁ (k + 1) → Set (CTorus d L N₁ m₁ (k + 1)) →
      Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N → ℂ)
    (hTl : ∀ T y Y q, Tl T y Y q =
      if sitesOf (piHull m₀ (sitesOf T)) = Y then e (blockIndex y) (π (clipRaw S.G' q), 0) T
      else 0) {ε : ℝ} (hε : ε ≤ eps) :
    ∀ T y Y, AnalyticOnNhd ℂ (Tl T y Y) {q | XiDom S.G' S.a S.ν (k + 1) ε q.1 q.2} := by
  intro T y Y q hq
  by_cases hY : sitesOf (piHull m₀ (sitesOf T)) = Y
  · have hfun : Tl T y Y = fun q => e (blockIndex y) (π (clipRaw S.G' q), 0) T := by
      funext q; simp only [hTl, hY, ↓reduceIte]
    rw [hfun]
    obtain ⟨_, hπq, hθ⟩ := clipRaw_physV_of_xiDom π hπ hε hq
    have hin : AnalyticAt ℂ (fun q : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N =>
        ((π (clipRaw S.G' q), (0 : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)) :
          physParam N S)) q :=
      (π.analyticAt _ |>.comp (analyticAt_clipRaw q)).prod analyticAt_const
    have hout := hean (blockIndex y) T _ (show ((π (clipRaw S.G' q),
      (0 : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)) : physParam N S) ∈
        physV S S.a₁ S.ν eps by rw [hπq]; exact hθ)
    exact AnalyticAt.comp_of_eq hout hin rfl
  · have hfun : Tl T y Y = fun _ => 0 := by
      funext q; simp only [hTl, hY, ↓reduceIte]
    rw [hfun]
    exact analyticAt_const

/-- **The labels are bounded on the step chart** by the per-label bounds `EbE`. -/
theorem newLabels_bound {m₀ : ℕ}
    (π : RawData d L (N₁ * L ^ m₁) (k + 1) N →L[ℂ] rawSub N S.G')
    (hπ : ∀ r (h : r ∈ rawSub N S.G'), π r = ⟨r, h⟩)
    (e : RootIdx d L N₁ m₁ (k + 1) → physParam N S →
      Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1) Set.univ) →
        ℂ)
    (b : RootIdx d L N₁ m₁ (k + 1) →
      Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1) Set.univ) →
        ℝ)
    (hbd : ∀ z T, ∀ θ ∈ physV S S.a₁ S.ν eps, ‖e z θ T‖ ≤ b z T)
    (Tl : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1)
        Set.univ) → CTorus d L N₁ m₁ (k + 1) → Set (CTorus d L N₁ m₁ (k + 1)) →
      Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N → ℂ)
    (hTl : ∀ T y Y q, Tl T y Y q =
      if sitesOf (piHull m₀ (sitesOf T)) = Y then e (blockIndex y) (π (clipRaw S.G' q), 0) T
      else 0)
    (EbE : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1)
        Set.univ) → CTorus d L N₁ m₁ (k + 1) → Set (CTorus d L N₁ m₁ (k + 1)) → ℝ)
    (hEbE : ∀ T y Y, EbE T y Y =
      if sitesOf (piHull m₀ (sitesOf T)) = Y then b (blockIndex y) T else 0)
    {ε : ℝ} (hε : ε ≤ eps) :
    ∀ T y Y (q : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N),
      XiDom S.G' S.a S.ν (k + 1) ε q.1 q.2 → ‖Tl T y Y q‖ ≤ EbE T y Y := by
  intro T y Y q hq
  rw [hTl, hEbE]
  split_ifs with hY
  · obtain ⟨_, hπq, hθ⟩ := clipRaw_physV_of_xiDom π hπ hε hq
    rw [hπq]
    exact hbd _ _ _ hθ
  · simp

open Classical in
/-- **The expansion identity of the labels on the step chart** (the form of `hDz`): at every pair
`q` of `Ξ^c_{k+1}(𝔹; 1, ε)`, `ε ≤ eps`, and every site `y`, the sum over the polymers `Y ∋ y` of
index `m₀` of the labels is the per-block density `densE0 C y q` of the step. -/
theorem newLabels_sum_eq_densE0 {m₀ : ℕ} (hN : L ^ m₀ ∣ N₁)
    (π : RawData d L (N₁ * L ^ m₁) (k + 1) N →L[ℂ] rawSub N S.G')
    (hπ : ∀ r (h : r ∈ rawSub N S.G'), π r = ⟨r, h⟩)
    (e : RootIdx d L N₁ m₁ (k + 1) → physParam N S →
      Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1) Set.univ) →
        ℂ)
    (hsupp : ∀ z θ T, e z θ T ≠ 0 →
      rootCube (m₀ := 1) z ∈ T ∧ IsPolyDom 1 (k + 1) (sitesOf T))
    (hval : ∀ z (D : BgData S.G' N), XiCData S.G' S.a S.ν (k + 1) 1 eps D →
      Jr.E0locJ C z (rawOf D) =
        ∑ T, e z ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub N S.G'), 0) T)
    (Tl : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1)
        Set.univ) → CTorus d L N₁ m₁ (k + 1) → Set (CTorus d L N₁ m₁ (k + 1)) →
      Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N → ℂ)
    (hTl : ∀ T y Y q, Tl T y Y q =
      if sitesOf (piHull m₀ (sitesOf T)) = Y then e (blockIndex y) (π (clipRaw S.G' q), 0) T
      else 0)
    {ε : ℝ} (hε : ε ≤ eps) :
    ∀ y (q : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N),
      XiDom S.G' S.a S.ν (k + 1) ε q.1 q.2 →
      ∑ᶠ Y ∈ polysAt m₀ (k + 1) y, ∑ T ∈ Finset.univ, Tl T y Y q = Jr.densE0 C y q := by
  intro y q hq
  obtain ⟨hmem, hπq, -⟩ := clipRaw_physV_of_xiDom π hπ hε hq
  have hinner : ∀ Y, ∑ T ∈ Finset.univ, Tl T y Y q =
      ∑ T ∈ Finset.univ.filter (fun T => sitesOf (piHull m₀ (sitesOf T)) = Y),
        e (blockIndex y) ((⟨clipRaw S.G' q, hmem⟩ : rawSub N S.G'), 0) T := by
    intro Y
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [hTl, hπq]
  simp_rw [hinner]
  rw [finsum_polysAt_regroup (m₀ := m₀) (fun T => sitesOf (piHull m₀ (sitesOf T)))
    (fun T => e (blockIndex y) ((⟨clipRaw S.G' q, hmem⟩ : rawSub N S.G'), 0) T) y
    (fun T hT => by
      obtain ⟨hr, hp⟩ := hsupp _ _ _ hT
      exact rootHull_mem hN y hr hp)]
  have h1 := Jr.densE0_rootSite_eq_sum C e hval hε hq (blockIndex y)
  simp only [hmem, dite_true] at h1
  rw [← h1]
  refine Jr.densE0_block C ?_ q
  rw [blockBase_rootSite, rootSite_blockIndex]

/-- **The energy labels of the new level on the step chart, from the class chain.**  For a
coefficient family `e` with the clauses of the chain at every root (analytic and bounded on
`physV`, rooted polymer support of index one, value `E0locJ C z` at every datum of the chart), the
labels `Tl` and bounds `EbE` fixed by `hTl`, `hEbE` satisfy, on `Ξ^c_{k+1}(𝔹; 1, ε)`, `ε ≤ eps`:
block dependence, polymer support of index `m₀`, analyticity, the per-label bound and the expansion
identity of the density `densE0`. -/
theorem newLabels_stepChart_of_rootFamily {m₀ : ℕ} (hN : L ^ m₀ ∣ N₁)
    (π : RawData d L (N₁ * L ^ m₁) (k + 1) N →L[ℂ] rawSub N S.G')
    (hπ : ∀ r (h : r ∈ rawSub N S.G'), π r = ⟨r, h⟩)
    (e : RootIdx d L N₁ m₁ (k + 1) → physParam N S →
      Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1) Set.univ) →
        ℂ)
    (b : RootIdx d L N₁ m₁ (k + 1) →
      Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1) Set.univ) →
        ℝ)
    (hean : ∀ z T, AnalyticOnNhd ℂ (fun θ => e z θ T) (physV S S.a₁ S.ν eps))
    (hbd : ∀ z T, ∀ θ ∈ physV S S.a₁ S.ν eps, ‖e z θ T‖ ≤ b z T)
    (hsupp : ∀ z θ T, e z θ T ≠ 0 →
      rootCube (m₀ := 1) z ∈ T ∧ IsPolyDom 1 (k + 1) (sitesOf T))
    (hval : ∀ z (D : BgData S.G' N), XiCData S.G' S.a S.ν (k + 1) 1 eps D →
      Jr.E0locJ C z (rawOf D) =
        ∑ T, e z ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub N S.G'), 0) T)
    (Tl : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1)
        Set.univ) → CTorus d L N₁ m₁ (k + 1) → Set (CTorus d L N₁ m₁ (k + 1)) →
      Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N → ℂ)
    (hTl : ∀ T y Y q, Tl T y Y q =
      if sitesOf (piHull m₀ (sitesOf T)) = Y then e (blockIndex y) (π (clipRaw S.G' q), 0) T
      else 0)
    (EbE : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1)
        Set.univ) → CTorus d L N₁ m₁ (k + 1) → Set (CTorus d L N₁ m₁ (k + 1)) → ℝ)
    (hEbE : ∀ T y Y, EbE T y Y =
      if sitesOf (piHull m₀ (sitesOf T)) = Y then b (blockIndex y) T else 0) :
    (∀ T ∈ (Finset.univ : Finset (Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
        (K := k + 1) 1 (k + 1) Set.univ))), ∀ y y' Y q,
      blockBase (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L (k + 1) y =
        blockBase (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L (k + 1) y' →
      Tl T y Y q = Tl T y' Y q) ∧
    (∀ T y Y q, Tl T y Y q ≠ 0 → IsPolyDom m₀ (k + 1) Y ∧ y ∈ Y) ∧
    (∀ ε, ε ≤ eps → ∀ T y Y,
      AnalyticOnNhd ℂ (Tl T y Y) {q | XiDom S.G' S.a S.ν (k + 1) ε q.1 q.2}) ∧
    (∀ ε, ε ≤ eps → ∀ T y Y (q : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N),
      XiDom S.G' S.a S.ν (k + 1) ε q.1 q.2 → ‖Tl T y Y q‖ ≤ EbE T y Y) ∧
    (∀ ε, ε ≤ eps → ∀ y (q : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N),
      XiDom S.G' S.a S.ν (k + 1) ε q.1 q.2 →
      ∑ᶠ Y ∈ polysAt m₀ (k + 1) y, ∑ T ∈ Finset.univ, Tl T y Y q = Jr.densE0 C y q) :=
  ⟨newLabels_block π e Tl hTl, newLabels_support hN π e hsupp Tl hTl,
    fun _ hε => newLabels_analytic π hπ e hean Tl hTl hε,
    fun _ hε => newLabels_bound π hπ e b hbd Tl hTl EbE hEbE hε,
    fun _ hε => newLabels_sum_eq_densE0 Jr C hN π hπ e hsupp hval Tl hTl hε⟩

/-- **The premise `hDz` of the new-level theorem, at the radius condition.**  If the generating
set of the step is the whole-level set `levelGS (k + 1)` (true by definition for the tower's step)
and the class radius of the new level does not exceed the radius of the step chart,
`P.eps d L (k + 1) ≤ eps`, the labels satisfy `hDz` of `localClass_newLevel_of_expansion(_rho)`
verbatim, with `𝒯E = Finset.univ`, weights `S.a`, mass `S.ν` and density `densE0 C`.  (For the
towers of the landed interface the radius condition contradicts the inherited room:
`not_newLevel_cover_and_room`.) -/
theorem newLabels_hDz_of_radius {m₀ : ℕ} (hN : L ^ m₀ ∣ N₁)
    (π : RawData d L (N₁ * L ^ m₁) (k + 1) N →L[ℂ] rawSub N S.G')
    (hπ : ∀ r (h : r ∈ rawSub N S.G'), π r = ⟨r, h⟩)
    (e : RootIdx d L N₁ m₁ (k + 1) → physParam N S →
      Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1) Set.univ) →
        ℂ)
    (hsupp : ∀ z θ T, e z θ T ≠ 0 →
      rootCube (m₀ := 1) z ∈ T ∧ IsPolyDom 1 (k + 1) (sitesOf T))
    (hval : ∀ z (D : BgData S.G' N), XiCData S.G' S.a S.ν (k + 1) 1 eps D →
      Jr.E0locJ C z (rawOf D) =
        ∑ T, e z ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub N S.G'), 0) T)
    (Tl : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1)
        Set.univ) → CTorus d L N₁ m₁ (k + 1) → Set (CTorus d L N₁ m₁ (k + 1)) →
      Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N → ℂ)
    (hTl : ∀ T y Y q, Tl T y Y q =
      if sitesOf (piHull m₀ (sitesOf T)) = Y then e (blockIndex y) (π (clipRaw S.G' q), 0) T
      else 0)
    (hG : S.G' = levelGS (ϱ := ϱ) (N₁ := N₁) (m₁ := m₁) (k + 1) (le_refl (k + 1)))
    {P : Consts} (hε : P.eps d L (k + 1) ≤ eps) :
    ∀ y (q : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N),
      (xiFieldDom S.a S.ν (P.eps d L) : FieldDom d L N₁ m₁ (k + 1) N ϱ).dom (k + 1)
        (levelGS (ϱ := ϱ) (N₁ := N₁) (m₁ := m₁) (k + 1) (le_refl (k + 1))) q.1 q.2 →
      ∑ᶠ Y ∈ polysAt m₀ (k + 1) y, ∑ T ∈ Finset.univ, Tl T y Y q = Jr.densE0 C y q := by
  intro y q hq
  have hq' : XiDom S.G' S.a S.ν (k + 1) (P.eps d L (k + 1)) q.1 q.2 := by
    rw [hG]; exact hq
  exact newLabels_sum_eq_densE0 Jr C hN π hπ e hsupp hval Tl hTl hε y q hq'

end Labels

end Balaban.Inhabited
