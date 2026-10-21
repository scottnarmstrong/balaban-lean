/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.LFOldHS2
public import Balaban.LargeField.R.RGasCoreConn
public import Balaban.LargeField.R.RRawHoleComponent

/-!
# The re-expanded old boundary terms on the local pairs of reading HS-2

Pieces 5c–5q (the coefficient, the marks, the cluster terms, `oldB` and its bound) are cores over the
readings of the local pair (`holeStepLocAt glob`, the local sets `V(σ X, J)`; `Spine/LFOldLocCoef` …
`Spine/LFOldBBound`).  This file gives their instances for reading HS-2 (`glob = true`,
`σ = stencilX`) and the conditions of the cores at the output labels from the named inputs of reading
HS-2.

* the geometry of the stencil at an output label: `linked_of_siteConnected_d7Pull` (a connected fine
  set of cubes is linked at the cube level), `siteConnected_d7Pull_stencilX` (the fine set of the
  stencil `X^{∼3}` of a connected label is connected), `exists_toFrame_eq` (the frame map is onto),
  `d7Pull_stencilX_inter_subset_markSiteAt` (the sites of the stencil in `Ω_{k+1}` lie in the mark
  site: they are sites of the core of `V₂(X, J)`), **`d7Pull_stencilX_subset_outLabel`** (the fine set
  of the stencil lies in the output label `Ŷ(T)` of every set `T` of cubes with `d_Ω(T) < ∞` containing
  the cubes of the mark site in `Ω_{k+1}`);
* `locConds_of_h7MixedLoc2`: **the local conditions of the core bounds at an output label from the
  named inputs `H7MixedInnerLoc2`, `H7MixedDatumLoc2`** (the condition D1, `CubesOfIn`, holds at the
  fine set of the output label);
* `oldCoefLoc2`, `norm_oldCoefLoc2_le_of_inputs` (the coefficient of reading HS-2 and its bound),
  `oldB2` and **`norm_oldB2_le`** (the re-expanded old boundary terms of reading HS-2 and their (D7)
  bound, from the two named inputs and the resummation `OldResumSiteAt stencilX`, which
  `oldResumSite2_holds` proves).
-/

@[expose] public section

open MeasureTheory Balaban Balaban.LargeField Balaban.LargeField.Def7 Balaban.Multiscale
  Balaban.Localization Balaban.Fluctuation Balaban.LargeField.RegionHistory Balaban.Background
  Balaban.Polymer

namespace Balaban.RootFSpine

section Geometry

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {N m₁ : ℕ}
  (g : Geo S n R M) (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) (hM1 : g.M1 = S.L ^ m₁)

omit [NeZero M] in
include hnn in
/-- **A connected fine set of cubes is linked at the level of the cubes** (steps of index distance
`≤ 1`, `reach_down`). -/
theorem linked_of_siteConnected_d7Pull {m₀ : ℕ} (F : FineSizeFrame S n M K m₀ m₁)
    {k : ℕ} (hkK : k ≤ K) {X : Set (Torus S.d (n k))}
    (hX : SiteConnected (d7Pull F k X)) :
    ∀ x ∈ X, ∀ y ∈ X, Linked 2 X x y := by
  have : NeZero (cellSide S.L m₀ m₁ k) := ⟨(cellSide_pos m₀ m₁ k).ne'⟩
  intro x hx y hy
  obtain ⟨zx, hzx⟩ := siteCube_surj' (fine_side_eq F hnn hkK) x
  obtain ⟨zy, hzy⟩ := siteCube_surj' (fine_side_eq F hnn hkK) y
  have hpre := d7Pull_eq_preimage_siteCube F k X
  have hzxX : zx ∈ d7Pull F k X := by rw [hpre]; simp [hzx, hx]
  have hzyX : zy ∈ d7Pull F k X := by rw [hpre]; simp [hzy, hy]
  have hp := hX zx hzxX zy hzyX
  rw [hpre] at hp
  have hc := reach_down (fine_side_eq F hnn hkK) X hp
  rw [hzx, hzy] at hc
  exact rtgMono (fun a b h => ⟨h.1, h.2.1, by have := NNAdj.supDist_le_one h.2.2; omega⟩) hc

omit [NeZero M] in
include hnn in
/-- **The fine set of the stencil of a connected set of cubes is connected** (`halo_reach_of_linked`,
`siteConnected_d7Pull`). -/
theorem siteConnected_d7Pull_stencilX {m₀ : ℕ} (F : FineSizeFrame S n M K m₀ m₁)
    {k : ℕ} (hkK : k ≤ K) {X : Finset (Torus S.d (n k))}
    (hX : SiteConnected (d7Pull F k (X : Set (Torus S.d (n k))))) :
    SiteConnected (d7Pull F k (stencilX X : Set (Torus S.d (n k)))) := by
  have hL := linked_of_siteConnected_d7Pull hnn F hkK hX
  have hset : (stencilX X : Set (Torus S.d (n k))) = nbhd 3 (X : Set (Torus S.d (n k))) := by
    ext u; exact mem_stencilX
  rw [hset]
  exact siteConnected_d7Pull F hnn hkK _ (halo_reach_of_linked (by norm_num) hL)

end Geometry

end Balaban.RootFSpine

namespace Balaban.RootFSpine

section Geometry2

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {N m₁ : ℕ}
  (g : Geo S n R M) (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) (hM1 : g.M1 = S.L ^ m₁)

omit [NeZero M] in
/-- **The frame map of the cover torus of the step is onto.** -/
theorem exists_toFrame_eq {m₀ : ℕ} (F : FineSizeFrame S n M K m₀ m₁) {k : ℕ} (hk : k + 1 ≤ K)
    (z : CTorus S.d S.L F.N₁ m₁ K) :
    ∃ x : CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1), toFrame g hnn hM1 F hk x = z := by
  have h1 : ∀ {a b : ℕ} (h : a = b) (y : Torus S.d b),
      LargeField.torusCast h (LargeField.torusCast h.symm y) = y := fun h y => by subst h; rfl
  have h2 : ∀ {a b : ℕ} (h : a = b) (y : Torus S.d a), castT h.symm (castT h y) = y :=
    fun h y => by subst h; rfl
  refine ⟨LargeField.torusCast (coverSide g hnn hM1 hk).symm (castT F.side z), ?_⟩
  unfold toFrame fineOfC
  rw [h1, h2]

omit [NeZero M] in
/-- **The sites of `Ω_{k+1}` in the stencil of `X` lie in the mark site of reading HS-2**: they are
frame sites of the core of the local set `V₂(X, J)` (the `r`-collar of `Ω_{k+1} ∩ X^{∼3}`). -/
theorem d7Pull_stencilX_inter_subset_markSiteAt {m₀ : ℕ} (F : FineSizeFrame S n M K m₀ m₁)
    (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K) (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊)
    (r r' : ℕ) (X : Finset (Torus S.d (n k)))
    (J : Finset (ℕ × CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1))) :
    d7Pull F k (stencilX X : Set (Torus S.d (n k))) ∩ d7Pull F (k + 1) (OmegaCube H (k + 1)) ⊆
      markSiteAt g hnn hM1 F H hk hρ r r' (stencilX X) X J := by
  rintro z ⟨hz1, hz2⟩
  obtain ⟨x, rfl⟩ := exists_toFrame_eq g hnn hM1 F hk z
  have hxA : x ∈ activeCoreC (c := g.c) (n1 := n (k + 1)) (n0 := n k) (k := k) (H.step k) hM1
      (stencilX X) := by
    refine (mem_activeCoreC _).2 ⟨?_, ?_⟩
    · rw [← cubeMap_fineOfC_k g hnn hM1 hk x]
      exact (toFrame_mem_d7Pull_iff g hnn hM1 F hk x).1 hz1
    · rw [← cubeMap_fineOfC_succ g hnn hM1 hk x]
      exact (toFrame_mem_d7Pull_iff g hnn hM1 F hk x).1 hz2
  have hxC : x ∈ collarCoreC (c := g.c) (k := k) (H.step k) hM1 r (stencilX X) :=
    (mem_collarCoreC _).2 ⟨x, hxA, by rw [LargeField.supDist_self]; exact Nat.zero_le _⟩
  refine markBaseAt_subset_markSiteAt g hnn hM1 F H hk hρ r r' (stencilX X) X J ?_
  exact Or.inl (Or.inr ⟨x, collarCoreC_subset_locSetXJ g hM1 H r r' (stencilX X) J hxC, rfl⟩)

end Geometry2

end Balaban.RootFSpine

namespace Balaban.RootFSpine

section Geometry3

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {N m₁ : ℕ}
  (g : Geo S n R M) (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) (hM1 : g.M1 = S.L ^ m₁)

omit [NeZero M] in
open Classical in
/-- **The fine set of the stencil of an old label lies in the output label** (reading HS-2): for an
old label `X` of `oldDoms`, a family `J` with a good site (local set `V₂(X, J)`), and a set `T` of cubes
of `Ω_{k+1}` with `d_Ω(T) < ∞` containing the cubes of `Ω_{k+1}` inside the mark site, the fine set of
`X^{∼3}` lies in `Ŷ(T)`: it is connected (`siteConnected_d7Pull_stencilX`), meets `Ω_{k+1}`, and its
sites in `Ω_{k+1}` lie in the mark site (`d7Pull_stencilX_inter_subset_markSiteAt`), whose cubes in
`Ω_{k+1}` lie in `T` (`subset_Yhat_of_connected`). -/
theorem d7Pull_stencilX_subset_outLabel {m₀ : ℕ} (F : FineSizeFrame S n M K m₀ m₁)
    (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K) (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊)
    (r r' : ℕ) {X : Finset (Torus S.d (n k))} (hXd : X ∈ oldDoms F H k)
    (J : Finset (ℕ × CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)))
    (T : Finset (CubeB (d := S.d) (L := S.L) (N₁ := F.N₁) (m₁ := m₁) (K := K) m₀ (k + 1)
      (d7Pull F (k + 1) (OmegaCube H (k + 1)))))
    (hfin : dOmega m₀ (k + 1) (d7Pull F (k + 1) (OmegaCube H (k + 1))) (sitesOf T) ≠ ⊤)
    (hJ : GoodJAt g hnn hM1 F H hk hρ r r' (d7Pull F (k + 1) (OmegaCube H (k + 1))) (stencilX X) X J)
    (hT : blocksOf m₀ (k + 1) (d7Pull F (k + 1) (OmegaCube H (k + 1)))
      (markSiteAt g hnn hM1 F H hk hρ r r' (stencilX X) X J) ⊆ T) :
    d7Pull F k (stencilX X : Set (Torus S.d (n k))) ⊆
      d7Pull F (k + 1) (outLabel F k (OmegaCube H (k + 1)) T : Set (Torus S.d (n (k + 1)))) := by
  obtain ⟨hb, hm⟩ := Finset.mem_filter.1 hXd
  have hXv := (mem_bdryDomsAt.1 hb).2
  obtain ⟨hDj, -⟩ := hJ
  have hsites : sitesOf (blocksOf m₀ (k + 1) (d7Pull F (k + 1) (OmegaCube H (k + 1)))
      (markSiteAt g hnn hM1 F H hk hρ r r' (stencilX X) X J)) =
      markSiteAt g hnn hM1 F H hk hρ r r' (stencilX X) X J ∩ d7Pull F (k + 1) (OmegaCube H (k + 1)) :=
    sitesOf_blocksOf F.divN₁ hk (d7Pull_isPiUnion F hnn hk (OmegaCube H (k + 1))) hDj.2.1
  have hsub : d7Pull F k (stencilX X : Set (Torus S.d (n k))) ∩
      d7Pull F (k + 1) (OmegaCube H (k + 1)) ⊆ sitesOf T := by
    intro z hz
    have hz' : z ∈ sitesOf (blocksOf m₀ (k + 1) (d7Pull F (k + 1) (OmegaCube H (k + 1)))
        (markSiteAt g hnn hM1 F H hk hρ r r' (stencilX X) X J)) := by
      rw [hsites]
      exact ⟨d7Pull_stencilX_inter_subset_markSiteAt g hnn hM1 F H hk hρ r r' X J hz, hz.2⟩
    obtain ⟨b, hb', hzb⟩ := mem_sitesOf.1 hz'
    exact mem_sitesOf.2 ⟨b, hT hb', hzb⟩
  have hmS : (d7Pull F k (stencilX X : Set (Torus S.d (n k))) ∩
      d7Pull F (k + 1) (OmegaCube H (k + 1))).Nonempty := by
    obtain ⟨x, hx1, hx2⟩ := hm
    exact ⟨x, by
      have : castT F.side x ∈ fineSet (S := S) (n := n) M K k (X : Set (Torus S.d (n k))) := hx1
      exact subset_stencilX X this, hx2⟩
  have hTne : T.Nonempty := by
    obtain ⟨z, hz⟩ := hmS
    obtain ⟨b, hb', -⟩ := mem_sitesOf.1 (hsub hz)
    exact ⟨b, hb'⟩
  rw [(outLabel_spec F hnn hk (OmegaCube H (k + 1)) T hTne hfin).1]
  exact subset_Yhat_of_connected
    (siteConnected_d7Pull_stencilX hnn F (Nat.le_of_succ_le hk) hXv.2.1) hmS hsub

end Geometry3

end Balaban.RootFSpine

namespace Balaban.RootFSpine

section Conds

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {N m₁ : ℕ}
  (g : Geo S n R M) (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) (hM1 : g.M1 = S.L ^ m₁)

/-- **The local conditions of the old part at an output label from the named inputs of reading
HS-2**: for a target field of the H7 domain of scale `k + 1` at the fine set of `Y`, every old label
`X` and every family `J` with a good site whose cubes in `Ω_{k+1}` lie in a set `T` of cubes with
output label `Y` and `d_Ω(T) < ∞`, the named inputs `H7MixedInnerLoc2`, `H7MixedDatumLoc2` give the
conditions `hloc` of `norm_oldBAtAt_le_of_dom` for the local pair of reading HS-2: the condition D1
holds at the fine set of `Y`, since the stencil of `X` (`d7Pull_stencilX_subset_outLabel`) and the
data sites of the local pair (which lie in the mark site) lie in it (`cubesOfIn_fineSet`). -/
theorem locConds_of_h7MixedLoc2 {m₀ : ℕ} {Fr : FineSizeFrame S n M K m₀ m₁} {k : ℕ}
    (hk : k + 1 ≤ K) {A : LabHist S n R k0 K} (hk1 : 1 ≤ k) (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊)
    (z : ℝ) (h₀ : Fin N → ℝ) (a₁ ν β p₁ δ : ℝ) {aw μs ε ε1 νs : ℕ → ℝ} {hv : EuclideanSpace ℝ (Fin N)}
    {BG δb κ κ₁ rψ : ℝ} (hL : 2 ≤ S.L) (ρ r r' : ℕ)
    (hIn : H7MixedInnerLoc2 g hnn hM1 A.H hk hk1 hρ z h₀ a₁ ν β p₁ δ (rho4 S.d S.L N BG κ) ρ r r' aw
      μs ε ε1 νs (hC hv) (Real.exp κ₁) rψ)
    (hDat : H7MixedDatumLoc2 g hnn hM1 A.H hk hk1 hρ z h₀ a₁ ν β p₁ δ aw μs ε ε1 νs (hC hv) ν δb)
    (Y : Finset (Torus S.d (n (k + 1)))) {ψ : MultiFieldC S n M K N} {ψ' : MultiFieldC S n M K N}
    {gf : Torus S.d (M * n K * S.L ^ K) → Fin N → ℂ}
    (htgt : H7Domain g.M1 g.c g.hM hnn (globalLH A.H M) (k + 1) hk
      (fineSet (S := S) (n := n) M K (k + 1) (Y : Set (Torus S.d (n (k + 1))))) aw μs ε ε1 νs
      (hC hv) ψ ψ' gf)
    {X : Finset (Torus S.d (n k))} (hXd : X ∈ oldDoms Fr A.H k)
    (J : Finset (ℕ × CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)))
    (T : Finset (CubeB (d := S.d) (L := S.L) (N₁ := Fr.N₁) (m₁ := m₁) (K := K) m₀ (k + 1)
      (d7Pull Fr (k + 1) (OmegaCube A.H (k + 1)))))
    (hTY : outLabel Fr k (OmegaCube A.H (k + 1)) T = Y)
    (hfin : dOmega m₀ (k + 1) (d7Pull Fr (k + 1) (OmegaCube A.H (k + 1))) (sitesOf T) ≠ ⊤)
    (hJ : GoodJAt g hnn hM1 Fr A.H hk hρ r r' (d7Pull Fr (k + 1) (OmegaCube A.H (k + 1))) (stencilX X)
      X J)
    (hT : blocksOf m₀ (k + 1) (d7Pull Fr (k + 1) (OmegaCube A.H (k + 1)))
      (markSiteAt g hnn hM1 Fr A.H hk hρ r r' (stencilX X) X J) ⊆ T) :
    InDomainC (holeStepLoc2 g hnn hM1 A.H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ
        (locSetXJ2 g hM1 A.H r r' X J)).G' ν δb δb
      (holeStepLoc2 g hnn hM1 A.H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ (locSetXJ2 g hM1 A.H r r' X J)).D' ∧
      ∀ ψo : (holeStepLoc2 g hnn hM1 A.H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ
          (locSetXJ2 g hM1 A.H r r' X J)).U → Fin N → ℂ, (∀ b, vn (ψo b) < rψ) →
        ∀ s : Dec2.DecParams (coverOf (holeStepLoc2 g hnn hM1 A.H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ
          (locSetXJ2 g hM1 A.H r r' X J)).G'),
        (∀ P, ‖s P‖ < Real.exp κ₁) →
        H7Domain g.M1 g.c g.hM hnn (globalLH A.H M) k (Nat.le_of_succ_le hk)
          (fineSet (S := S) (n := n) M K k (X : Set (Torus S.d (n k)))) aw μs ε ε1 νs (hC hv)
          (composedMulti g hnn hM1 hk (holeStepLoc2 g hnn hM1 A.H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ
              (locSetXJ2 g hM1 A.H r r' X J)).G' ψ
            ((holeStepLoc2 g hnn hM1 A.H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ
              (locSetXJ2 g hM1 A.H r r' X J)).composed
              (coverOf (holeStepLoc2 g hnn hM1 A.H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ
                (locSetXJ2 g hM1 A.H r r' X J)).G') (rho4 S.d S.L N BG κ)
              ((holeStepLoc2 g hnn hM1 A.H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ
                (locSetXJ2 g hM1 A.H r r' X J)).slocOf
                (coverOf (holeStepLoc2 g hnn hM1 A.H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ
                  (locSetXJ2 g hM1 A.H r r' X J)).G')
                (locDomsLF g hM1 (holeStepLoc2 g hnn hM1 A.H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ
                  (locSetXJ2 g hM1 A.H r r' X J)) ρ)
                (HoleStep.coreExt (coverOf (holeStepLoc2 g hnn hM1 A.H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ
                  (locSetXJ2 g hM1 A.H r r' X J)).G')
                  (collarCoreC (c := g.c) (A.H.step k) hM1 r X) s)) ψo))
          ψ' gf := by
  have hmark := subset_outLabel_of_mark g hnn hM1 Fr A.H hk hρ stencilX r r' hXd J Y T hTY hfin hJ hT
  have hst := d7Pull_stencilX_subset_outLabel g hnn hM1 Fr A.H hk hρ r r' hXd J T hfin hJ hT
  rw [hTY] at hst
  have hdata : fineOfC g hnn hM1 hk '' (dataSites (locG' g hnn hM1 A.H hk hρ
      (locSetXJ2 g hM1 A.H r r' X J)) : Set (CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1))) ⊆
      fineSet (S := S) (n := n) M K (k + 1) (Y : Set (Torus S.d (n (k + 1)))) := by
    rintro _ ⟨x, hx, rfl⟩
    exact fineOfC_mem_of_toFrame_mem g hnn hM1 Fr hk (hmark.2
      (markBaseAt_subset_markSiteAt g hnn hM1 Fr A.H hk hρ r r' (stencilX X) X J
        (Or.inr ⟨x, hx, rfl⟩)))
  have hY := cubesOfIn_fineSet (Set.union_subset (fineSet_subset_of_d7Pull_subset Fr hst) hdata)
  exact ⟨hDat _ _ ψ ψ' gf htgt (cubesOfIn_fineSet hdata), fun ψo hψo s hs =>
    h7Domain_composedMulti_loc2 g hnn hM1 A.H hk hk1 hρ z h₀ a₁ ν β p₁ δ (rho4 S.d S.L N BG κ) ρ r r'
      aw μs ε ε1 νs (hC hv) hL hIn X J htgt hY hψo hs⟩

end Conds

end Balaban.RootFSpine

namespace Balaban.RootFSpine

section Inst

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {N m₁ : ℕ}
  (g : Geo S n R M) (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) (hM1 : g.M1 = S.L ^ m₁)

/-- **The coefficient `T(X, J)` of an old boundary term on its local pair of reading HS-2**: the core
`oldCoefLocAt` at the restricted global datum (`holeStepLoc2`) and the local set `V₂(X, J)`. -/
noncomputable abbrev oldCoefLoc2 (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K)
    (hk1 : 1 ≤ k) (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (ψ : MultiFieldC S n M K N) (z : ℝ)
    (h₀ : Fin N → ℝ) (a₁ ν β p₁ δ : ℝ) (ρc : ℝ) (ρ r r' : ℕ) {geo : Geo S n R M} {cs : OpConsts}
    {P : BudgetConsts} (rep : Rep S n R k0 K M N geo cs P k) (A : LabHist S n R k0 K)
    (X : Finset (Torus S.d (n k))) (ψ' : MultiFieldC S n M K N) (hv : EuclideanSpace ℝ (Fin N))
    (gx : GIdx S n M K N → ℂ) (J : Finset (ℕ × CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)))
    (ψhat : (holeStepLF g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).U → Fin N → ℂ) : ℂ :=
  oldCoefLocAt (glob := true) (σ := stencilX) g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ ρc ρ r r' rep A
    X ψ' hv gx J ψhat

/-- **The bound of the coefficient of an old boundary term on its local pair of reading HS-2** (P6
(4.33)–(4.34) at one coefficient): for an old label `X` of the record, a family `J`, a target field of
the H7 domain of scale `k + 1` at a set `Y_f` containing the cubes of `𝕋_{k+1}` of the sites of the
stencil of `X` and of the data sites of the local pair (`CubesOfIn`), and a fluctuation field
`|ψ̂_b| < r_ψ`, `|T(X, J)| ≤ fac · e^{-rate · d^cov(X)} · e^{-(κ₁ - 1)|J_V|}`; from the standing
conditions of Theorems I-4b, I-4c and the two named inputs of reading HS-2
(`norm_oldCoefLocAt_le_of_dom`). -/
theorem norm_oldCoefLoc2_le_of_inputs {m₀ : ℕ} {Fr : FineSizeFrame S n M K m₀ m₁} {k : ℕ}
    (hk : k + 1 ≤ K) {cs : OpConsts} {P : BudgetConsts} {rep : Rep S n R k0 K M N g cs P k}
    {Zof : LabHist S n R k0 K → Set (Torus S.d (n k))} {aw μs ε ε1 νs : ℕ → ℝ} {fac rate : ℝ}
    {hv : EuclideanSpace ℝ (Fin N)}
    (hrec : D7BdryPost Fr hnn (Nat.le_of_succ_le hk) rep Zof aw μs ε ε1 νs fac rate hv)
    {A : LabHist S n R k0 K} (hA : A ∈ rep.hist) {X : Finset (Torus S.d (n k))}
    (hX : X ∈ bdryDomsPost Fr A k (Zof A)) (hk1 : 1 ≤ k) (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (z : ℝ)
    (h₀ : Fin N → ℝ) (a₁ ν β p₁ δ : ℝ) {c BG δb δc κ κ₁ rψ : ℝ}
    (hS : Dec2.DecSpecs S.d S.L (Dec2.mixedKc S.d S.L) (Cchi S.d S.L) c BG)
    (HB : BgHyp S.d S.L (k + 1) (minSep S.L g.M1) (compWeight S.L a₁) ν)
    (hm₁ : 2 ≤ m₁) (hN : 5 < g.c * n (k + 1)) (hM : 4 * S.L ^ 2 ≤ S.L ^ m₁)
    (hag : 2 * S.d * Real.log S.L ≤ agmonRate S.d / 16 * (minSep S.L g.M1 - 1))
    (ha₁ : 1 / 2 ≤ a₁) (ha₂ : a₁ ≤ 2) (hκ : 0 < κ)
    (hMc : c * Real.exp (N0 S.d S.L * κ) ≤ (S.L : ℝ) ^ m₁)
    (hMX : Dec2.cstarX S.d S.L (Cchi S.d S.L) * Real.exp (N0 S.d S.L * κ) ≤ (S.L : ℝ) ^ m₁)
    (hδ0 : 0 < δb) (hε : δb ≤ bgC0 S.d S.L N) (hδ : δb ≤ c7 S.d S.L N BG κ)
    (hphi : 3 * δb + K4 S.d S.L N BG κ * δb < 1 / 2)
    (hmarD : K4 S.d S.L N BG κ * δb + 2 * δb +
      K4 S.d S.L N BG κ * δb * (K4 S.d S.L N BG κ * δb + 2 * (1 + 3 * δb)) < δc)
    (hαD : K4 S.d S.L N BG κ * δb < coerciveConst S.d / 2)
    (hsm : δc ^ 2 * smallConstX S.d S.L κ ≤ 1 / 4) (hκ₁ : 1 ≤ κ₁) (hκ₁κ : κ₁ ≤ κ) (ρ r r' : ℕ)
    (hIn : H7MixedInnerLoc2 g hnn hM1 A.H hk hk1 hρ z h₀ a₁ ν β p₁ δ (rho4 S.d S.L N BG κ) ρ r r'
      aw μs ε ε1 νs (hC hv) (Real.exp κ₁) rψ)
    (hDat : H7MixedDatumLoc2 g hnn hM1 A.H hk hk1 hρ z h₀ a₁ ν β p₁ δ aw μs ε ε1 νs (hC hv) ν δb)
    (J : Finset (ℕ × CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)))
    {Yf : Set (Torus S.d (M * n K * S.L ^ K))} {ψ : MultiFieldC S n M K N}
    {q' : FinFieldC S n M K N} {gx : GIdx S n M K N → ℂ}
    (htgt : H7Domain g.M1 g.c g.hM hnn (globalLH A.H M) (k + 1) hk Yf aw μs ε ε1 νs (hC hv) ψ
      (extK q') (fun x i => gx (x, i)))
    (hY : CubesOfIn (S := S) (n := n) (M := M) (K := K) (k + 1) Yf
      (fineSet (S := S) (n := n) M K k (stencilX X : Set (Torus S.d (n k))) ∪
        fineOfC g hnn hM1 hk '' (dataSites (locG' g hnn hM1 A.H hk hρ
          (locSetXJ2 g hM1 A.H r r' X J)) : Set (CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)))))
    {ψhat : (holeStepLF g hnn hM1 A.H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).U → Fin N → ℂ}
    (hψloc : ∀ b : (holeStepLoc2 g hnn hM1 A.H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ
      (locSetXJ2 g hM1 A.H r r' X J)).U, vn (restrictU _ _ _ _ _ _ _ ψhat b) < rψ) :
    ‖oldCoefLoc2 g hnn hM1 A.H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ (rho4 S.d S.L N BG κ) ρ r r' rep A X
        (extK q') hv gx J ψhat‖ ≤
      fac * Real.exp (-rate * d7Size Fr A k X) *
        Real.exp (-(κ₁ - 1) * (locCubes g (coverOf (holeStepLoc2 g hnn hM1 A.H hk hk1 hρ ψ z h₀ a₁
          ν β p₁ δ (locSetXJ2 g hM1 A.H r r' X J)).G') J).card) := by
  have hL : 2 ≤ S.L := by have := HB.hL; omega
  exact norm_oldCoefLocAt_le_of_dom g hnn hM1 true stencilX hk hrec hA hX hk1 hρ z h₀ a₁ ν β p₁ δ
    hS HB hm₁ hN hM hag ha₁ ha₂ hκ hMc hMX hδ0 hε hδ hphi hmarD hαD hsm hκ₁ hκ₁κ ρ r r' J
    (hDat (locSetXJ2 g hM1 A.H r r' X J) Yf ψ (extK q') (fun x i => gx (x, i)) htgt
      (fun x hx => hY x (Or.inr hx)))
    (fun ψo hψo s hs => h7Domain_composedMulti_loc2 g hnn hM1 A.H hk hk1 hρ z h₀ a₁ ν β p₁ δ
      (rho4 S.d S.L N BG κ) ρ r r' aw μs ε ε1 νs (hC hv) hL hIn X J htgt hY hψo hs) hψloc

end Inst

end Balaban.RootFSpine


namespace Balaban.RootFSpine

section OldB2

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {N m₁ : ℕ}
  (g : Geo S n R M) (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) (hM1 : g.M1 = S.L ^ m₁)

/-- **The re-expanded old boundary terms of reading HS-2** as boundary terms of scale `k + 1` (the
core `oldBOf` at the restricted global datum and the local sets `V₂(X, J)`). -/
noncomputable abbrev oldB2 {m₀ : ℕ} (F : FineSizeFrame S n M K m₀ m₁) {k : ℕ} (hk : k + 1 ≤ K)
    (hk1 : 1 ≤ k) (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (z : ℝ) (h₀ : Fin N → ℝ)
    (a₁ ν β p₁ δ : ℝ)
    (inner : ∀ (A : LabHist S n R k0 K) (ψ : MultiFieldC S n M K N),
      Finset (holeStepLF g hnn hM1 A.H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).U)
    (cb : ∀ (A : LabHist S n R k0 K) (ψ : MultiFieldC S n M K N), inner A ψ →
      CubeB (d := S.d) (L := S.L) (N₁ := F.N₁) (m₁ := m₁) (K := K) m₀ (k + 1)
        (d7Pull F (k + 1) (OmegaCube A.H (k + 1))))
    (hp : 0 < p₁)
    (I : ∀ (A : LabHist S n R k0 K) (ψ _ : MultiFieldC S n M K N) (_ : GIdx S n M K N → ℂ),
      LocInteraction (fun b => {u : inner A ψ // cb A ψ u = b} → Rn N))
    (ψout : ∀ (A : LabHist S n R k0 K) (ψ : MultiFieldC S n M K N),
      (holeStepLF g hnn hM1 A.H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).U → Fin N → ℂ) (rψ : ℝ)
    (ρc : ℝ) (ρ r r' : ℕ) {geo : Geo S n R M} {cs : OpConsts} {P : BudgetConsts}
    (rep : Rep S n R k0 K M N geo cs P k) (hv : EuclideanSpace ℝ (Fin N)) :
    BTerms S n R k0 K M N (k + 1) :=
  oldBOf g hnn hM1 true F stencilX hk hk1 hρ z h₀ a₁ ν β p₁ δ inner cb hp I ψout rψ ρc ρ r r' rep hv

/-- **The (D7) bound of the re-expanded old boundary terms of reading HS-2** (P6 (4.34); LFR Lemma
IV.1.5 (iii)): at a history `𝔸` of the record, an output label `Y` and a field `p` in the H7 domain of
scale `k + 1` at the fine set of `Y`, with `κ' ≥ rate' + c₁ log 2 + 2`,
`|oldB₂(𝔸, Y)| ≤ 2^{c₁} C_PE fac C_res L^d c₁ K₀(rate-κ_X) c₁ K₀(κ₀) e^{-rate' d^pre_{k+1}(Y)}`.
Conditional on the named inputs `H7MixedInnerLoc2`, `H7MixedDatumLoc2` of reading HS-2; the
resummation `OldResumSiteAt stencilX` holds (`oldResumSite2_holds`). -/
theorem norm_oldB2_le {m₀ : ℕ} {Fr : FineSizeFrame S n M K m₀ m₁} {k : ℕ}
    (hk : k + 1 ≤ K) {cs : OpConsts} {P : BudgetConsts} {rep : Rep S n R k0 K M N g cs P k}
    {Zof : LabHist S n R k0 K → Set (Torus S.d (n k))} {aw μs ε ε1 νs : ℕ → ℝ} {fac rate : ℝ}
    {hv : EuclideanSpace ℝ (Fin N)}
    (hrec : D7BdryPost Fr hnn (Nat.le_of_succ_le hk) rep Zof aw μs ε ε1 νs fac rate hv)
    {A : LabHist S n R k0 K} (hA : A ∈ rep.hist) (hk1 : 1 ≤ k) (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊)
    (z : ℝ) (h₀ : Fin N → ℝ) (a₁ ν β p₁ δ : ℝ) {c BG δb δc κ κ₁ rψ : ℝ}
    (hS : Dec2.DecSpecs S.d S.L (Dec2.mixedKc S.d S.L) (Cchi S.d S.L) c BG)
    (HB : BgHyp S.d S.L (k + 1) (minSep S.L g.M1) (compWeight S.L a₁) ν)
    (hm₁ : 2 ≤ m₁) (hN : 5 < g.c * n (k + 1)) (hM : 4 * S.L ^ 2 ≤ S.L ^ m₁)
    (hag : 2 * S.d * Real.log S.L ≤ agmonRate S.d / 16 * (minSep S.L g.M1 - 1))
    (ha₁ : 1 / 2 ≤ a₁) (ha₂ : a₁ ≤ 2) (hκ : 0 < κ)
    (hMc : c * Real.exp (N0 S.d S.L * κ) ≤ (S.L : ℝ) ^ m₁)
    (hMX : Dec2.cstarX S.d S.L (Cchi S.d S.L) * Real.exp (N0 S.d S.L * κ) ≤ (S.L : ℝ) ^ m₁)
    (hδ0 : 0 < δb) (hε : δb ≤ bgC0 S.d S.L N) (hδ : δb ≤ c7 S.d S.L N BG κ)
    (hphi : 3 * δb + K4 S.d S.L N BG κ * δb < 1 / 2)
    (hmarD : K4 S.d S.L N BG κ * δb + 2 * δb +
      K4 S.d S.L N BG κ * δb * (K4 S.d S.L N BG κ * δb + 2 * (1 + 3 * δb)) < δc)
    (hαD : K4 S.d S.L N BG κ * δb < coerciveConst S.d / 2)
    (hsm : δc ^ 2 * smallConstX S.d S.L κ ≤ 1 / 4) (hκ₁ : 1 ≤ κ₁) (hκ₁κ : κ₁ ≤ κ) (ρ r r' : ℕ)
    (hIn : H7MixedInnerLoc2 g hnn hM1 A.H hk hk1 hρ z h₀ a₁ ν β p₁ δ (rho4 S.d S.L N BG κ) ρ r r'
      aw μs ε ε1 νs (hC hv) (Real.exp κ₁) rψ)
    (hDat : H7MixedDatumLoc2 g hnn hM1 A.H hk hk1 hρ z h₀ a₁ ν β p₁ δ aw μs ε ε1 νs (hC hv) ν δb)
    (hXs : ∀ X ∈ oldDoms Fr A.H k, X ∈ bdryDomsPost Fr A k (Zof A))
    (Y : Finset (Torus S.d (n (k + 1)))) (p : FinFieldC S n M K N × FinFieldC S n M K N ×
      (GIdx S n M K N → ℂ))
    (htgt : H7Domain g.M1 g.c g.hM hnn (globalLH A.H M) (k + 1) hk
      (fineSet (S := S) (n := n) M K (k + 1) (Y : Set (Torus S.d (n (k + 1))))) aw μs ε ε1 νs
      (hC hv) (extK p.1) (extK p.2.1) (fun x i => p.2.2 (x, i)))
    (inner : ∀ (A : LabHist S n R k0 K) (ψ : MultiFieldC S n M K N),
      Finset (holeStepLF g hnn hM1 A.H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).U)
    (cb : ∀ (A : LabHist S n R k0 K) (ψ : MultiFieldC S n M K N), inner A ψ →
      CubeB (d := S.d) (L := S.L) (N₁ := Fr.N₁) (m₁ := m₁) (K := K) m₀ (k + 1)
        (d7Pull Fr (k + 1) (OmegaCube A.H (k + 1))))
    (hcb : ∀ u : inner A (extK p.1), toFrame g hnn hM1 Fr hk
      (unitRep (u : (holeStepLF g hnn hM1 A.H hk hk1 hρ (extK p.1) z h₀ a₁ ν β p₁ δ).U)) ∈
        Localization.box (cb A (extK p.1) u).1 (cellSide S.L m₀ m₁ (k + 1)))
    (hp : 0 < p₁)
    (I : ∀ (A : LabHist S n R k0 K) (ψ _ : MultiFieldC S n M K N) (_ : GIdx S n M K N → ℂ),
      LocInteraction (fun b => {u : inner A ψ // cb A ψ u = b} → Rn N))
    (ψout : ∀ (A : LabHist S n R k0 K) (ψ : MultiFieldC S n M K N),
      (holeStepLF g hnn hM1 A.H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).U → Fin N → ℂ)
    (hrψ : 0 < rψ) (hfac : 0 < fac) {κX κV Cres rate' : ℝ}
    (hres : OldResumSiteAt g hnn hM1 Fr A.H hk hρ ρ r r' stencilX κ₁ κX κV Cres) (hCres : 0 < Cres)
    (hκV : (I A (extK p.1) (extK p.2.1) p.2.2).κH ≤ κV) (hαX : aEnt S.d S.L + 1 ≤ rate - κX)
    (hκ' : rate' + Real.log 2 * c1 S.d S.L + 2 ≤ (I A (extK p.1) (extK p.2.1) p.2.2).κ') :
    ‖oldB2 g hnn hM1 Fr hk hk1 hρ z h₀ a₁ ν β p₁ δ inner cb hp I ψout rψ
        (rho4 S.d S.L N BG κ) ρ r r' rep hv A Y (extK p.1) (extK p.2.1) (hC hv) p.2.2‖ ≤
      Real.exp (Real.log 2 * c1 S.d S.L) *
        (CPE S.d S.L ((I A (extK p.1) (extK p.2.1) p.2.2).Kc + 1)
          (I A (extK p.1) (extK p.2.1) p.2.2).κH (I A (extK p.1) (extK p.2.1) p.2.2).κ0
          (I A (extK p.1) (extK p.2.1) p.2.2).κ' * (fac * Cres)) *
        ((S.L : ℝ) ^ S.d * c1 S.d S.L * K0 S.d S.L (rate - κX)) *
        (c1 S.d S.L * K0 S.d S.L (I A (extK p.1) (extK p.2.1) p.2.2).κ0) *
        Real.exp (-rate' * d7SizePre Fr A (k + 1) Y) := by
  have hL : 2 ≤ S.L := by have := HB.hL; omega
  exact norm_oldBOf_le_of_dom g hnn hM1 true stencilX hk hrec hA hk1 hρ z h₀ a₁ ν β p₁ δ
    hS HB hm₁ hN hM hag ha₁ ha₂ hκ hMc hMX hδ0 hε hδ hphi hmarD hαD hsm hκ₁ hκ₁κ ρ r r' hXs Y p
    (fun X hX J T hTY hfin hJ hT => locConds_of_h7MixedLoc2 g hnn hM1 hk hk1 hρ z h₀ a₁ ν β p₁ δ hL ρ
      r r' hIn hDat Y htgt hX J T hTY hfin hJ hT)
    inner cb hcb hp I ψout hrψ hfac hres hCres hκV hαX hκ'

end OldB2

end Balaban.RootFSpine

