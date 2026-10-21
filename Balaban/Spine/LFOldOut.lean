/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.LFOldCluster
public import Balaban.Spine.LFBdryHole

/-!
# The output labels of the re-expanded old boundary terms (FLUCTUATION Theorem 3.1 (c); P6 p. 34–35)

The cluster term of a mark at a set `T` of cubes of the region `Ω' = Ω_{k+1}` of the frame torus
(`oldClusterLF`) is a term of `ℬ''^{(k+1)}` localized in the domain `Ŷ(T)`: the sites of the cubes
of `T` with the components of `Ω'^c` next to them (FLUCTUATION Theorem 3.1 (c), the output domains
of the expectation of the measure of P5 (3.2); P6 p. 34–35).  This file defines the output label and
proves that it is a valid label of scale `k + 1` with size `d_Ω(T)`, and that it contains the old
label of a mark whose cubes lie in `T`.

* `outLabel`: **the output label of a set `T` of cubes**, the cubes of `𝕋_{k+1}` of `Ŷ(T)`;
* `outLabel_spec`: for `T ≠ ∅` with `d_Ω(T) < ∞`, its fine set is `Ŷ(T)`, it is valid at `Ω_{k+1}`
  (`FineValidAt`, ruling R11) and its size is `d_Ω(T)` (`dExt`);
* `subset_Yhat_of_connected`: a connected set meeting `Ω'` whose sites in `Ω'` lie in `A` lies in
  `Ŷ(A)`;
* `d7Pull_subset_outLabel`: **the old label lies in the output label** when the cubes of the site
  of its mark lie in `T`;
* `holeClose_subset_Yhat_of_connected`, `markSite_holeClose_subset_outLabel`,
  `markSite_subset_outLabel`: **the site of a mark and the components of `Ω_{k+1}^c` meeting it lie
  in the output label**.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L]

omit [NeZero N₁] [NeZero L] in
/-- **A connected set lies in `Ŷ(A)` when its sites in `Ω` lie in `A`** and it meets `Ω`: a site
outside `Ω` is joined inside the set to a site of `Ω`; the last site before entering `Ω` lies in the
component of `Ω^c` of the starting site and is next to a site of `A`. -/
theorem subset_Yhat_of_connected {Ω A X : Set (CTorus d L N₁ m₁ K)} (hX : SiteConnected X)
    (hm : (X ∩ Ω).Nonempty) (hA : X ∩ Ω ⊆ A) : X ⊆ Yhat Ω A := by
  intro x hx
  by_cases hxΩ : x ∈ Ω
  · exact Or.inl (hA ⟨hx, hxΩ⟩)
  obtain ⟨t, htX, htΩ⟩ := hm
  have key : ∀ b, Relation.ReflTransGen (fun u v => u ∈ X ∧ v ∈ X ∧ Nbr u v) x b →
      (b ∈ Ω → x ∈ Yhat Ω A) ∧ (b ∉ Ω → x ∈ Yhat Ω A ∨ b ∈ OmegaComp Ω x) := by
    intro b hb
    induction hb with
    | refl => exact ⟨fun h => absurd h hxΩ, fun _ => Or.inr (mem_comp_self hxΩ)⟩
    | @tail b c _ hbc ih =>
      obtain ⟨hbX, hcX, hn⟩ := hbc
      by_cases hbΩ : b ∈ Ω
      · exact ⟨fun _ => ih.1 hbΩ, fun _ => Or.inl (ih.1 hbΩ)⟩
      · rcases ih.2 hbΩ with h | hbC
        · exact ⟨fun _ => h, fun _ => Or.inl h⟩
        · refine ⟨fun hcΩ => Or.inr ⟨b, hbΩ, ⟨c, hA ⟨hcX, hcΩ⟩, hn.symm⟩, ?_⟩, fun hcΩ => ?_⟩
          · rw [← comp_eq_of_rtg hbC.2]
            exact mem_comp_self hxΩ
          · exact Or.inr ⟨hcΩ, hbC.2.tail ⟨hbΩ, hcΩ, hn⟩⟩
  exact (key t (hX x hx t htX)).1 htΩ

omit [NeZero N₁] [NeZero L] in
/-- **The hole closure of a connected set lies in `Ŷ(A)`** when the set meets `Ω`, its sites in `Ω`
lie in `A` and `A ⊆ Ω`: a component of `Ω^c` meeting the set is the component of a site next to `A`. -/
theorem holeClose_subset_Yhat_of_connected {Ω A X : Set (CTorus d L N₁ m₁ K)} (hX : SiteConnected X)
    (hm : (X ∩ Ω).Nonempty) (hA : X ∩ Ω ⊆ A) (hAΩ : A ⊆ Ω) : holeClose Ω X ⊆ Yhat Ω A := by
  have hXY := subset_Yhat_of_connected hX hm hA
  rintro y (hy | hy)
  · exact hXY hy
  · obtain ⟨z, ⟨hzX, hzΩ⟩, hyz⟩ := Set.mem_iUnion₂.1 hy
    rcases hXY hzX with hzA | ⟨w, hw, hwA, hzw⟩
    · exact absurd (hAΩ hzA) hzΩ
    · refine Or.inr ⟨w, hw, hwA, ?_⟩
      rw [comp_eq_of_rtg hzw.2]
      exact hyz

end Balaban.Fluctuation

open MeasureTheory Balaban Balaban.LargeField Balaban.LargeField.Def7 Balaban.Multiscale
  Balaban.Localization Balaban.Fluctuation Balaban.LargeField.RegionHistory Balaban.Background
  Balaban.Polymer

namespace Balaban.RootFSpine

section Out

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {M K m₀ m₁ : ℕ} [NeZero S.L]
  (F : FineSizeFrame S n M K m₀ m₁) (hnn : ∀ i, i < K → n i = S.L * n (i + 1))

open Classical in
/-- **The output label of a set `T` of cubes** of the region `Ω' = Ω_{k+1}` of the frame torus
(FLUCTUATION Theorem 3.1 (c); P6 p. 34–35): the cubes of `𝕋_{k+1}` of `Ŷ(T)`, the sites of the cubes
of `T` with the components of `Ω'^c` next to them. -/
noncomputable def outLabel (k : ℕ) (Om' : Set (Torus S.d (n (k + 1))))
    (T : Finset (CubeB (d := S.d) (L := S.L) (N₁ := F.N₁) (m₁ := m₁) (K := K) m₀ (k + 1)
      (d7Pull F (k + 1) Om'))) : Finset (Torus S.d (n (k + 1))) :=
  Finset.univ.filter (· ∈ cubeIdx F (k + 1) '' Yhat (d7Pull F (k + 1) Om') (sitesOf T))

omit [∀ k, NeZero (n k)] [NeZero S.L] in
/-- The sites of a set of cubes of a region lie in the region. -/
theorem sitesOf_subset {j : ℕ} {Ω : Set (CTorus S.d S.L F.N₁ m₁ K)}
    (T : Finset (CubeB (d := S.d) (L := S.L) (N₁ := F.N₁) (m₁ := m₁) (K := K) m₀ j Ω)) :
    sitesOf T ⊆ Ω := fun _ hz => by
  obtain ⟨b, -, hzb⟩ := mem_sitesOf.1 hz
  exact b.2.2 hzb

include hnn in
/-- **The output label of a set of cubes** `T ≠ ∅` with `d_Ω(T) < ∞`: its fine set is `Ŷ(T)`, it is a
valid label at `Ω_{k+1}` (`FineValidAt`, ruling R11), and its size is `d_Ω(T)`. -/
theorem outLabel_spec {k : ℕ} (hk : k + 1 ≤ K) (Om' : Set (Torus S.d (n (k + 1))))
    (T : Finset (CubeB (d := S.d) (L := S.L) (N₁ := F.N₁) (m₁ := m₁) (K := K) m₀ (k + 1)
      (d7Pull F (k + 1) Om'))) (hT : T.Nonempty)
    (hfin : dOmega m₀ (k + 1) (d7Pull F (k + 1) Om') (sitesOf T) ≠ ⊤) :
    d7Pull F (k + 1) (outLabel F k Om' T : Set (Torus S.d (n (k + 1)))) =
        Yhat (d7Pull F (k + 1) Om') (sitesOf T) ∧
      FineValidAt F (k + 1) Om' (outLabel F k Om' T) ∧
      d7SizeAt F (k + 1) Om' (outLabel F k Om' T) = dExt T := by
  classical
  obtain ⟨b, hb⟩ := hT
  have hne : (sitesOf T).Nonempty :=
    ⟨b.1, mem_sitesOf.2 ⟨b, hb, mem_box_self b.1 (cellSide_pos m₀ m₁ (k + 1))⟩⟩
  have hY := djModFin_Yhat (sitesOf_subset F T) hne hfin
  have hcl : ∀ y ∈ Yhat (d7Pull F (k + 1) Om') (sitesOf T),
      Localization.box (cbase (cellSide S.L m₀ m₁ (k + 1)) y) (cellSide S.L m₀ m₁ (k + 1)) ⊆
        Yhat (d7Pull F (k + 1) Om') (sitesOf T) :=
    fun y hy => hY.cell_subset F.divN₁ hk (d7Pull_isPiUnion F hnn hk Om') hy
  have hpull : d7Pull F (k + 1) (outLabel F k Om' T : Set (Torus S.d (n (k + 1)))) =
      Yhat (d7Pull F (k + 1) Om') (sitesOf T) := by
    unfold outLabel
    rw [Finset.coe_filter]
    simp only [Finset.mem_univ, true_and, Set.ofPred_mem_eq]
    exact d7Pull_cubeIdx_image F hnn hk hcl
  refine ⟨hpull, ?_, ?_⟩
  · unfold FineValidAt
    rw [hpull]
    exact hY
  · unfold d7SizeAt d7SizeAtE dExt
    rw [hpull]
    simp only [hfin, ↓reduceIte]
    unfold dOmega
    simp only [hY.2.1, ↓reduceIte]

include hnn in
/-- **The old label lies in the output label** (FLUCTUATION Theorem 3.1 (c); P6 p. 34): if the old
label `X` is valid (at any region of scale `k`) and meets `Ω_{k+1}`, and the cubes of `Ω_{k+1}` inside the site
of the mark of `(X, J)` lie in `T` (the cluster term is zero otherwise), then the fine set of `X` lies
in `Ŷ(T)`, the fine set of the output label. -/
theorem d7Pull_subset_outLabel {R : ℕ → ℝ} {k0 : ℕ} [NeZero M] {g : Geo S n R M}
    (hM1 : g.M1 = S.L ^ m₁) (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K)
    (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) {Om : Set (Torus S.d (n k))} {X : Finset (Torus S.d (n k))}
    (hX : FineValidAt F k Om X)
    (hXm : (d7Pull F k (X : Set (Torus S.d (n k))) ∩
      d7Pull F (k + 1) (OmegaCube H (k + 1))).Nonempty) (r r' : ℕ)
    (J : Finset (ℕ × CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)))
    (T : Finset (CubeB (d := S.d) (L := S.L) (N₁ := F.N₁) (m₁ := m₁) (K := K) m₀ (k + 1)
      (d7Pull F (k + 1) (OmegaCube H (k + 1)))))
    (hT : blocksOf m₀ (k + 1) (d7Pull F (k + 1) (OmegaCube H (k + 1)))
      (markSite g hnn hM1 F H hk hρ r r' X J) ⊆ T)
    (hfin : dOmega m₀ (k + 1) (d7Pull F (k + 1) (OmegaCube H (k + 1))) (sitesOf T) ≠ ⊤) :
    d7Pull F k (X : Set (Torus S.d (n k))) ⊆
      d7Pull F (k + 1) (outLabel F k (OmegaCube H (k + 1)) T : Set (Torus S.d (n (k + 1)))) := by
  have ha0 := cellSide_pos (L := S.L) m₀ m₁ (k + 1)
  have hsub : d7Pull F k (X : Set (Torus S.d (n k))) ∩ d7Pull F (k + 1) (OmegaCube H (k + 1)) ⊆
      sitesOf T := by
    rintro x ⟨hxX, hxΩ⟩
    have hcell : Localization.box (cbase (cellSide S.L m₀ m₁ (k + 1)) x)
        (cellSide S.L m₀ m₁ (k + 1)) ⊆ d7Pull F (k + 1) (OmegaCube H (k + 1)) := by
      rcases cell_dichotomy F.divN₁ hk (d7Pull_isPiUnion F hnn hk (OmegaCube H (k + 1)))
          (aligned_cbase (a := cellSide S.L m₀ m₁ (k + 1)) x) with h | h
      · exact h
      · exact absurd hxΩ (h (mem_box_cbase ha0 x))
    have hmem : (⟨cbase (cellSide S.L m₀ m₁ (k + 1)) x, aligned_cbase x, hcell⟩ :
        CubeB (d := S.d) (L := S.L) (N₁ := F.N₁) (m₁ := m₁) (K := K) m₀ (k + 1)
          (d7Pull F (k + 1) (OmegaCube H (k + 1)))) ∈ T := by
      refine hT (mem_blocksOf.2 fun y hy => ⟨x, Or.inl (Or.inl (Or.inl ⟨hxX, hxΩ⟩)), ?_⟩)
      exact Localization.box_mono _ (Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero (NeZero.ne S.L))) hy
    exact mem_sitesOf.2 ⟨_, hmem, mem_box_cbase ha0 x⟩
  obtain ⟨x, hx⟩ := hXm
  have hTne : T.Nonempty := by
    obtain ⟨b, hb, -⟩ := mem_sitesOf.1 (hsub hx)
    exact ⟨b, hb⟩
  rw [(outLabel_spec F hnn hk (OmegaCube H (k + 1)) T hTne hfin).1]
  exact subset_Yhat_of_connected hX.2.1 ⟨x, hx⟩ hsub

include hnn in
/-- **The hole closure of the site of a mark lies in the output label** (P6 p. 34; FLUCTUATION
Theorem 3.1 (c)): for a family `J` with a good site (`GoodJ` at `Ω_{k+1}`) and a set `T` of cubes of
`Ω_{k+1}` with `d_Ω(T) < ∞` containing the cubes of `Ω_{k+1}` inside the site (the cluster term is
zero otherwise), the site and the components of `Ω_{k+1}^c` meeting it lie in `Ŷ(T)`, the fine set of
the output label of `T`. -/
theorem markSite_holeClose_subset_outLabel {R : ℕ → ℝ} {k0 : ℕ} [NeZero M] {g : Geo S n R M}
    (hM1 : g.M1 = S.L ^ m₁) (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K)
    (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (r r' : ℕ) (X : Finset (Torus S.d (n k)))
    (J : Finset (ℕ × CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)))
    (hJ : GoodJ g hnn hM1 F H hk hρ r r' (d7Pull F (k + 1) (OmegaCube H (k + 1))) X J)
    (T : Finset (CubeB (d := S.d) (L := S.L) (N₁ := F.N₁) (m₁ := m₁) (K := K) m₀ (k + 1)
      (d7Pull F (k + 1) (OmegaCube H (k + 1)))))
    (hT : blocksOf m₀ (k + 1) (d7Pull F (k + 1) (OmegaCube H (k + 1)))
      (markSite g hnn hM1 F H hk hρ r r' X J) ⊆ T)
    (hfin : dOmega m₀ (k + 1) (d7Pull F (k + 1) (OmegaCube H (k + 1))) (sitesOf T) ≠ ⊤) :
    holeClose (d7Pull F (k + 1) (OmegaCube H (k + 1))) (markSite g hnn hM1 F H hk hρ r r' X J) ⊆
      d7Pull F (k + 1) (outLabel F k (OmegaCube H (k + 1)) T : Set (Torus S.d (n (k + 1)))) := by
  obtain ⟨hDj, hm⟩ := hJ
  have hsites : sitesOf (blocksOf m₀ (k + 1) (d7Pull F (k + 1) (OmegaCube H (k + 1)))
      (markSite g hnn hM1 F H hk hρ r r' X J)) =
      markSite g hnn hM1 F H hk hρ r r' X J ∩ d7Pull F (k + 1) (OmegaCube H (k + 1)) :=
    sitesOf_blocksOf F.divN₁ hk (d7Pull_isPiUnion F hnn hk (OmegaCube H (k + 1))) hDj.2.1
  have hsub : markSite g hnn hM1 F H hk hρ r r' X J ∩ d7Pull F (k + 1) (OmegaCube H (k + 1)) ⊆
      sitesOf T := by
    rw [← hsites]
    intro z hz
    obtain ⟨b, hb, hzb⟩ := mem_sitesOf.1 hz
    exact mem_sitesOf.2 ⟨b, hT hb, hzb⟩
  have hTne : T.Nonempty := by
    obtain ⟨z, hz⟩ := hm
    obtain ⟨b, hb, -⟩ := mem_sitesOf.1 (hsub hz)
    exact ⟨b, hb⟩
  rw [(outLabel_spec F hnn hk (OmegaCube H (k + 1)) T hTne hfin).1]
  exact holeClose_subset_Yhat_of_connected hDj.2.2 hm hsub (sitesOf_subset F T)

include hnn in
/-- **The site of a mark lies in the output label** (`markSite_holeClose_subset_outLabel`). -/
theorem markSite_subset_outLabel {R : ℕ → ℝ} {k0 : ℕ} [NeZero M] {g : Geo S n R M}
    (hM1 : g.M1 = S.L ^ m₁) (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K)
    (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (r r' : ℕ) (X : Finset (Torus S.d (n k)))
    (J : Finset (ℕ × CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)))
    (hJ : GoodJ g hnn hM1 F H hk hρ r r' (d7Pull F (k + 1) (OmegaCube H (k + 1))) X J)
    (T : Finset (CubeB (d := S.d) (L := S.L) (N₁ := F.N₁) (m₁ := m₁) (K := K) m₀ (k + 1)
      (d7Pull F (k + 1) (OmegaCube H (k + 1)))))
    (hT : blocksOf m₀ (k + 1) (d7Pull F (k + 1) (OmegaCube H (k + 1)))
      (markSite g hnn hM1 F H hk hρ r r' X J) ⊆ T)
    (hfin : dOmega m₀ (k + 1) (d7Pull F (k + 1) (OmegaCube H (k + 1))) (sitesOf T) ≠ ⊤) :
    markSite g hnn hM1 F H hk hρ r r' X J ⊆
      d7Pull F (k + 1) (outLabel F k (OmegaCube H (k + 1)) T : Set (Torus S.d (n (k + 1)))) :=
  (subset_holeClose _ _).trans
    (markSite_holeClose_subset_outLabel F hnn hM1 H hk hρ r r' X J hJ T hT hfin)

end Out

end Balaban.RootFSpine
