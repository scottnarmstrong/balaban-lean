/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.LFOldOut

/-!
# The re-expanded old boundary terms at an output label (P6 (4.32)–(4.34); P3 (4.45)–(4.49))

The old part of the boundary terms of the step on a region at an output label `Y` is the sum, over the
sets `T` of cubes of `Ω_{k+1}` with output label `Y` (`outLabel`, the domains `Ŷ(T)` of FLUCTUATION
Theorem 3.1 (c)), over the old labels `X` and over the sites `V` of their marks, of the cluster term
of the mark of `(X, V)` at `T`.  The mark of `(X, V)` is the sum of the marks `oldMarkLF` of the
decoupling families `J` of `X` whose site is `V` (P3 (4.45): "we do a partial resummation of the terms
over the domains `Y₁` determining a fixed `Y`").

* `stepG'`, `locRange`, `allJ`: the set of P5 (2.17) of the step, the localization range, and the
  families of cubes of its cover inside the localization range;
* `famAt`, `sitesX`: the families of `X` with good site `V`, and the good sites of the marks of `X`;
* `OldResumSite`: **the resummation over the decoupling families at a mark site** (named input,
  open; P3 (4.45)–(4.49), P6 p. 34);
* `oldMarkSite`, `oldMarkSite_dep`, `measurable_oldMarkSite`, `norm_oldMarkSite_le`: the mark of
  `(X, V)`, its locality, measurability and bound;
* `oldClusterSite`, `norm_oldClusterSite_le`: its cluster term at `T` and the bound
  `C_PE fac C_res e^{-(rate-κ_X) d(X)} e^{-κ₀ 𝗱(V)} e^{-κ' d_Ω(T)}`;
* `oldBAt`: **the old part of the boundary terms at an output label `Y`**.
-/

@[expose] public section

open MeasureTheory Balaban Balaban.LargeField Balaban.LargeField.Def7 Balaban.Multiscale
  Balaban.Localization Balaban.Fluctuation Balaban.LargeField.RegionHistory Balaban.Background
  Balaban.Polymer

namespace Balaban.RootFSpine

section SiteMarks

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {N m₁ : ℕ}
  (g : Geo S n R M) (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) (hM1 : g.M1 = S.L ^ m₁)

/-- **The set of P5 (2.17) of the step on a region of the history** (`p6TopC`; it does not depend on
the fields, `holeStepLF_G'_eq`). -/
noncomputable def stepG' (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K)
    (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) :
    GeneratingSet S.d S.L ((g.c * n (k + 1)) * S.L ^ m₁) (k + 1) (minSep S.L g.M1) :=
  p6TopC (H.step k) hM1 (hnn k (by omega)) hρ (by have := g.hc; omega)

omit [NeZero M] in
theorem holeStepLF_G'_eq (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K) (hk1 : 1 ≤ k)
    (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (ψ : MultiFieldC S n M K N) (z : ℝ) (h₀ : Fin N → ℝ)
    (a₁ ν β p₁ δ : ℝ) :
    (holeStepLF g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).G' = stepG' g hnn hM1 H hk hρ := rfl

/-- **The localization range of the step** (P5 (2.18), reading HS-1): the sites of the cubes of
`𝕋_{k+1}` within `ρ` cubes of a cube of `Ω_{k+1}` (the union of the localization domains `locDomC` of
the sites of `Ω_{k+1}`). -/
def locRange (H : RegionHistory S n R k0 K) {k : ℕ} (ρ : ℕ) :
    Set (CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)) :=
  {y | ∃ x, cubeOfC (c := g.c) (n1 := n (k + 1)) hM1 x ∈ (H.step k).Omega ∧
    y ∈ locDomC (c := g.c) (n1 := n (k + 1)) hM1 ρ x}

open Classical in
/-- **The families of decoupling cubes of the step**: the sets of cubes of the cover of `G′` of levels
`k`, `k + 1` inside the localization range (the parameters of the other cubes do not enter the
localization vectors of the unit points, `slocOf`, `locDomsLF`; the localization range lies in the
layers `k`, `k + 1` of `G′` when `ρ ≤ ⌊R_k⌋`, since `Ω_{k+1} ⊂ Ω'_{k+1}` is far from `W_k^c`). -/
noncomputable def allJ (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K)
    (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (ρ : ℕ) :
    Finset (Finset (ℕ × CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1))) :=
  ((coverOf (stepG' g hnn hM1 H hk hρ)).cubeIdx.filter fun P => k ≤ P.1 ∧
    (cubeP P : Set (CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1))) ⊆ locRange g hM1 H ρ).powerset

open Classical in
/-- **The families of an old label `X` with the good site `V`** (P3 (4.45): the domains `Y₁`
determining a fixed site). -/
noncomputable def famAt {m₀ : ℕ} (F : FineSizeFrame S n M K m₀ m₁) (H : RegionHistory S n R k0 K)
    {k : ℕ} (hk : k + 1 ≤ K) (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (ρ r r' : ℕ)
    (X : Finset (Torus S.d (n k))) (V : Set (CTorus S.d S.L F.N₁ m₁ K)) :
    Finset (Finset (ℕ × CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1))) :=
  (allJ g hnn hM1 H hk hρ ρ).filter fun J =>
    GoodJ g hnn hM1 F H hk hρ r r' (d7Pull F (k + 1) (OmegaCube H (k + 1))) X J ∧
      markSite g hnn hM1 F H hk hρ r r' X J = V

open Classical in
/-- **The good sites of the marks of an old label `X`.** -/
noncomputable def sitesX {m₀ : ℕ} (F : FineSizeFrame S n M K m₀ m₁) (H : RegionHistory S n R k0 K)
    {k : ℕ} (hk : k + 1 ≤ K) (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (ρ r r' : ℕ)
    (X : Finset (Torus S.d (n k))) : Finset (Set (CTorus S.d S.L F.N₁ m₁ K)) :=
  ((allJ g hnn hM1 H hk hρ ρ).filter fun J =>
    GoodJ g hnn hM1 F H hk hρ r r' (d7Pull F (k + 1) (OmegaCube H (k + 1))) X J).image
      (markSite g hnn hM1 F H hk hρ r r' X)

omit [NeZero M] in
/-- A family with the site `V` has the site `V` and a good site. -/
theorem mem_famAt {m₀ : ℕ} {F : FineSizeFrame S n M K m₀ m₁} {H : RegionHistory S n R k0 K}
    {k : ℕ} {hk : k + 1 ≤ K} {hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊} {ρ r r' : ℕ}
    {X : Finset (Torus S.d (n k))} {V : Set (CTorus S.d S.L F.N₁ m₁ K)}
    {J : Finset (ℕ × CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1))} :
    J ∈ famAt g hnn hM1 F H hk hρ ρ r r' X V ↔ J ∈ allJ g hnn hM1 H hk hρ ρ ∧
      GoodJ g hnn hM1 F H hk hρ r r' (d7Pull F (k + 1) (OmegaCube H (k + 1))) X J ∧
        markSite g hnn hM1 F H hk hρ r r' X J = V := by
  classical
  simp [famAt]

omit [NeZero M] in
/-- **A good site of a mark is a set of `𝒟_{k+1}` meeting `Ω_{k+1}`**, the site of a good family. -/
theorem exists_of_mem_sitesX {m₀ : ℕ} {F : FineSizeFrame S n M K m₀ m₁}
    {H : RegionHistory S n R k0 K} {k : ℕ} {hk : k + 1 ≤ K} {hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊}
    {ρ r r' : ℕ} {X : Finset (Torus S.d (n k))} {V : Set (CTorus S.d S.L F.N₁ m₁ K)}
    (hV : V ∈ sitesX g hnn hM1 F H hk hρ ρ r r' X) :
    ∃ J ∈ famAt g hnn hM1 F H hk hρ ρ r r' X V, IsDj m₀ (k + 1) V ∧
      (V ∩ d7Pull F (k + 1) (OmegaCube H (k + 1))).Nonempty := by
  classical
  obtain ⟨J, hJ, rfl⟩ := Finset.mem_image.1 hV
  obtain ⟨hJa, hJg⟩ := Finset.mem_filter.1 hJ
  exact ⟨J, (mem_famAt g hnn hM1).2 ⟨hJa, hJg, rfl⟩, hJg⟩

/-- **The resummation over the decoupling families at a mark site** (named input, **open**; P3
(4.45)–(4.49), P6 p. 34: "the inequalities (4.48), (4.49) [3] hold with `d_j(X)`, `d̃_{j+1}(Y)`
replaced by `d_k(X mod Ω_k^c)`, `d_{k+1}(Y mod Ω^c_{k+1})`"): for every old label `X` meeting
`Ω_{k+1}` and every site `V`, the families `J` of `X` with the site `V` satisfy
`∑_J e^{-(κ₁-1)|J_V|} ≤ C_res e^{κ_X d_k(X)} e^{-κ_V 𝗱(V)}` (`J_V` the cubes of `J` in the cover of
the local pair).  The proof needs the levels of the cover cubes in the localization domains near
`Ω_{k+1}` (a bounded number of cubes per cell), the size of the site by `d_k(X)` and `|J_V|`
(P3 (4.48)) and the count of the reached families of cover cubes from one cube (P3 (4.49)). -/
def OldResumSite {m₀ : ℕ} (F : FineSizeFrame S n M K m₀ m₁) (H : RegionHistory S n R k0 K) {k : ℕ}
    (hk : k + 1 ≤ K) (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (ρ r r' : ℕ) (κ₁ κX κV Cres : ℝ) : Prop :=
  ∀ X ∈ oldDoms F H k, ∀ V : Set (CTorus S.d S.L F.N₁ m₁ K),
    ∑ J ∈ famAt g hnn hM1 F H hk hρ ρ r r' X V,
        Real.exp (-(κ₁ - 1) *
          (locCubes g (coverOf (locG' g hnn hM1 H hk hρ (locSetXJ g hM1 H r r' X J))) J).card) ≤
      Cres * Real.exp (κX * d7SizeAt F k (H.omegaPost k) X) *
        Real.exp (-κV * treeLenCovOne (d := S.d) (L := S.L) (N₁ := F.N₁) (m₁ := m₁) (K := K) m₀
          (k + 1) V)

/-- **The mark of `(X, V)`** (P3 (4.45), P6 p. 34): the sum of the marks of the families of `X` with
the site `V`. -/
noncomputable def oldMarkSite {m₀ : ℕ} (F : FineSizeFrame S n M K m₀ m₁)
    (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K) (hk1 : 1 ≤ k)
    (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (ψ : MultiFieldC S n M K N) (z : ℝ) (h₀ : Fin N → ℝ)
    (a₁ ν β p₁ δ : ℝ) (inner : Finset (holeStepLF g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).U)
    {Cb : Type*} (cb : inner → Cb)
    (ψout : (holeStepLF g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).U → Fin N → ℂ) (rψ : ℝ)
    (ρc : ℝ) (ρ r r' : ℕ) {geo : Geo S n R M} {cs : OpConsts} {P : BudgetConsts}
    (rep : Rep S n R k0 K M N geo cs P k) (A : LabHist S n R k0 K) (X : Finset (Torus S.d (n k)))
    (ψ' : MultiFieldC S n M K N) (hv : EuclideanSpace ℝ (Fin N)) (gx : GIdx S n M K N → ℂ)
    (V : Set (CTorus S.d S.L F.N₁ m₁ K)) (Φ : ∀ b, {u : inner // cb u = b} → Rn N) : ℂ :=
  ∑ J ∈ famAt g hnn hM1 F H hk hρ ρ r r' X V,
    oldMarkLF g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ inner cb ψout rψ ρc ρ r r' rep A X ψ' hv gx J
      Φ

/-- **The mark of `(X, V)` depends only on the cubes inside `V`.** -/
theorem oldMarkSite_dep {m₀ : ℕ} (F : FineSizeFrame S n M K m₀ m₁)
    (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K) (hk1 : 1 ≤ k)
    (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (ψ : MultiFieldC S n M K N) (z : ℝ) (h₀ : Fin N → ℝ)
    (a₁ ν β p₁ δ : ℝ) {Ω : Set (CTorus S.d S.L F.N₁ m₁ K)}
    (inner : Finset (holeStepLF g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).U)
    (cb : inner → CubeB (d := S.d) (L := S.L) (N₁ := F.N₁) (m₁ := m₁) (K := K) m₀ (k + 1) Ω)
    (hcb : ∀ u : inner, toFrame g hnn hM1 F hk
      (unitRep (u : (holeStepLF g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).U)) ∈
        Localization.box (cb u).1 (cellSide S.L m₀ m₁ (k + 1)))
    (ψout : (holeStepLF g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).U → Fin N → ℂ) (rψ : ℝ)
    (ρc : ℝ) (ρ r r' : ℕ) {geo : Geo S n R M} {cs : OpConsts} {P : BudgetConsts}
    (rep : Rep S n R k0 K M N geo cs P k) (A : LabHist S n R k0 K) (X : Finset (Torus S.d (n k)))
    (ψ' : MultiFieldC S n M K N) (hv : EuclideanSpace ℝ (Fin N)) (gx : GIdx S n M K N → ℂ)
    (V : Set (CTorus S.d S.L F.N₁ m₁ K)) :
    DepOn (blocksOf m₀ (k + 1) Ω V)
      (oldMarkSite g hnn hM1 F H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ inner cb ψout rψ ρc ρ r r' rep A X ψ'
        hv gx V) := by
  intro Φ Φ' h
  unfold oldMarkSite
  refine Finset.sum_congr rfl fun J hJ => ?_
  have hJV := ((mem_famAt g hnn hM1).1 hJ).2.2
  have := oldMarkLF_depOn_markSite g hnn hM1 F H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ inner cb hcb ψout rψ
    ρc ρ r r' rep A X ψ' hv gx J
  rw [hJV] at this
  exact this Φ Φ' h

/-- **The mark of `(X, V)` is measurable** (each mark `oldMarkLF` is, `measurable_oldMarkLF`). -/
theorem measurable_oldMarkSite {m₀ : ℕ} {Fr : FineSizeFrame S n M K m₀ m₁} {k : ℕ}
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
    (hIn : H7MixedInnerLoc g hnn hM1 A.H hk hk1 hρ z h₀ a₁ ν β p₁ δ (rho4 S.d S.L N BG κ) ρ r aw μs
      ε ε1 νs (hC hv) (Real.exp κ₁) rψ)
    (hDat : H7MixedDatumLoc g hnn hM1 A.H hk hk1 hρ z h₀ a₁ ν β p₁ δ aw μs ε ε1 νs (hC hv) ν δb)
    {Yf : Set (Torus S.d (M * n K * S.L ^ K))} {ψ : MultiFieldC S n M K N}
    {q' : FinFieldC S n M K N} {gx : GIdx S n M K N → ℂ}
    (htgt : H7Domain g.M1 g.c g.hM hnn (globalLH A.H M) (k + 1) hk Yf aw μs ε ε1 νs (hC hv) ψ
      (extK q') (fun x i => gx (x, i)))
    {X : Finset (Torus S.d (n k))} (hX : X ∈ bdryDomsPost Fr A k (Zof A))
    (hXY : fineSet (S := S) (n := n) M K k (X : Set (Torus S.d (n k))) ⊆ Yf)
    (V : Set (CTorus S.d S.L Fr.N₁ m₁ K))
    (hVJ : ∀ J ∈ famAt g hnn hM1 Fr A.H hk hρ ρ r r' X V,
      ∀ x ∈ dataSites (holeStepLoc g hnn hM1 A.H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ
        (locSetXJ g hM1 A.H r r' X J)).G', fineOfC g hnn hM1 hk x ∈ Yf)
    (inner : Finset (holeStepLF g hnn hM1 A.H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).U)
    {Cb : Type*} (cb : inner → Cb)
    (ψout : (holeStepLF g hnn hM1 A.H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).U → Fin N → ℂ) :
    Measurable (oldMarkSite g hnn hM1 Fr A.H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ inner cb ψout rψ
      (rho4 S.d S.L N BG κ) ρ r r' rep A X (extK q') hv gx V) := by
  unfold oldMarkSite
  exact Finset.measurable_sum _ fun J hJ => measurable_oldMarkLF g hnn hM1 hk hrec hA hX hk1 hρ z h₀ a₁ ν β p₁ δ hS HB hm₁ hN hM hag ha₁ ha₂ hκ hMc hMX hδ0 hε hδ hphi hmarD hαD hsm hκ₁ hκ₁κ ρ r r' hIn hDat J htgt
    hXY (hVJ J hJ) inner cb ψout

/-- **The bound of the mark of `(X, V)`** (P6 (4.34) at each family, `norm_oldMarkLF_le`):
`|G_{X,V}| ≤ fac e^{-rate d^cov(X)} ∑_J e^{-(κ₁-1)|J_V|}` over the families of `X` with the site `V`. -/
theorem norm_oldMarkSite_le {m₀ : ℕ} {Fr : FineSizeFrame S n M K m₀ m₁} {k : ℕ}
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
    (hIn : H7MixedInnerLoc g hnn hM1 A.H hk hk1 hρ z h₀ a₁ ν β p₁ δ (rho4 S.d S.L N BG κ) ρ r aw μs
      ε ε1 νs (hC hv) (Real.exp κ₁) rψ)
    (hDat : H7MixedDatumLoc g hnn hM1 A.H hk hk1 hρ z h₀ a₁ ν β p₁ δ aw μs ε ε1 νs (hC hv) ν δb)
    {Yf : Set (Torus S.d (M * n K * S.L ^ K))} {ψ : MultiFieldC S n M K N}
    {q' : FinFieldC S n M K N} {gx : GIdx S n M K N → ℂ}
    (htgt : H7Domain g.M1 g.c g.hM hnn (globalLH A.H M) (k + 1) hk Yf aw μs ε ε1 νs (hC hv) ψ
      (extK q') (fun x i => gx (x, i)))
    {X : Finset (Torus S.d (n k))} (hX : X ∈ bdryDomsPost Fr A k (Zof A))
    (hXY : fineSet (S := S) (n := n) M K k (X : Set (Torus S.d (n k))) ⊆ Yf)
    (V : Set (CTorus S.d S.L Fr.N₁ m₁ K))
    (hVJ : ∀ J ∈ famAt g hnn hM1 Fr A.H hk hρ ρ r r' X V,
      ∀ x ∈ dataSites (holeStepLoc g hnn hM1 A.H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ
        (locSetXJ g hM1 A.H r r' X J)).G', fineOfC g hnn hM1 hk x ∈ Yf)
    (inner : Finset (holeStepLF g hnn hM1 A.H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).U)
    {Cb : Type*} (cb : inner → Cb)
    (ψout : (holeStepLF g hnn hM1 A.H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).U → Fin N → ℂ)
    (hrψ : 0 < rψ) (Φ : ∀ b, {u : inner // cb u = b} → Rn N) :
    ‖oldMarkSite g hnn hM1 Fr A.H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ inner cb ψout rψ
        (rho4 S.d S.L N BG κ) ρ r r' rep A X (extK q') hv gx V Φ‖ ≤
      fac * Real.exp (-rate * d7Size Fr A k X) *
        ∑ J ∈ famAt g hnn hM1 Fr A.H hk hρ ρ r r' X V, Real.exp (-(κ₁ - 1) *
          (locCubes g (coverOf (locG' g hnn hM1 A.H hk hρ (locSetXJ g hM1 A.H r r' X J))) J).card) := by
  unfold oldMarkSite
  rw [Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun J hJ => ?_)
  exact norm_oldMarkLF_le g hnn hM1 hk hrec hA hX hk1 hρ z h₀ a₁ ν β p₁ δ hS HB hm₁ hN hM hag ha₁ ha₂ hκ hMc hMX hδ0 hε hδ hphi hmarD hαD hsm hκ₁ hκ₁κ ρ r r' hIn hDat J htgt hXY (hVJ J hJ) inner cb ψout hrψ Φ

/-- **The cluster term of the mark of `(X, V)`** at the set `T` of cubes of `Ω_{k+1}` on the frame
torus (Theorem 3.4, `markTerm`): the product measures `cubeMeasure` of the variables of the cubes,
the interaction `I`, the mark `oldMarkSite` with site `V`. -/
noncomputable def oldClusterSite {m₀ : ℕ} (F : FineSizeFrame S n M K m₀ m₁)
    (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K) (hk1 : 1 ≤ k)
    (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (ψ : MultiFieldC S n M K N) (z : ℝ) (h₀ : Fin N → ℝ)
    (a₁ ν β p₁ δ : ℝ) (inner : Finset (holeStepLF g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).U)
    (cb : inner → CubeB (d := S.d) (L := S.L) (N₁ := F.N₁) (m₁ := m₁) (K := K) m₀ (k + 1)
      (d7Pull F (k + 1) (OmegaCube H (k + 1))))
    (hp : 0 < p₁) (I : LocInteraction (fun b => {u : inner // cb u = b} → Rn N))
    (ψout : (holeStepLF g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).U → Fin N → ℂ) (rψ : ℝ)
    (ρc : ℝ) (ρ r r' : ℕ) {geo : Geo S n R M} {cs : OpConsts} {P : BudgetConsts}
    (rep : Rep S n R k0 K M N geo cs P k) (A : LabHist S n R k0 K) (X : Finset (Torus S.d (n k)))
    (ψ' : MultiFieldC S n M K N) (hv : EuclideanSpace ℝ (Fin N)) (gx : GIdx S n M K N → ℂ)
    (V : Set (CTorus S.d S.L F.N₁ m₁ K))
    (T : Finset (CubeB (d := S.d) (L := S.L) (N₁ := F.N₁) (m₁ := m₁) (K := K) m₀ (k + 1)
      (d7Pull F (k + 1) (OmegaCube H (k + 1))))) : ℂ :=
  haveI := (holeStepLF g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).isProbabilityMeasure_cubeMeasure
    inner cb hp
  markTerm ((holeStepLF g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).cubeMeasure inner cb) I.A V
    (oldMarkSite g hnn hM1 F H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ inner cb ψout rψ ρc ρ r r' rep A X ψ' hv
      gx V) T

/-- **The bound of the cluster term of the mark of `(X, V)`** (P6 (4.34); Theorem 3.4 with the mark's
site added to the labels; P3 (4.45)–(4.49) through the named input `OldResumSite`): for an old label
`X` meeting `Ω_{k+1}`, a good site `V` of its marks whose families satisfy the condition of the
local pairs, and constants with `κ_H ≤ κ_V`,
`|∫₀¹ G*_{X,V}(T) du| ≤ C_PE fac C_res e^{-(rate-κ_X) d^cov(X)} e^{-κ₀ 𝗱(V)} e^{-κ' d_Ω(T)}`.
Conditional on `H7MixedInnerLoc`, `H7MixedDatumLoc`, `OldResumSite`. -/
theorem norm_oldClusterSite_le {m₀ : ℕ} {Fr : FineSizeFrame S n M K m₀ m₁} {k : ℕ}
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
    (hIn : H7MixedInnerLoc g hnn hM1 A.H hk hk1 hρ z h₀ a₁ ν β p₁ δ (rho4 S.d S.L N BG κ) ρ r aw μs
      ε ε1 νs (hC hv) (Real.exp κ₁) rψ)
    (hDat : H7MixedDatumLoc g hnn hM1 A.H hk hk1 hρ z h₀ a₁ ν β p₁ δ aw μs ε ε1 νs (hC hv) ν δb)
    {Yf : Set (Torus S.d (M * n K * S.L ^ K))} {ψ : MultiFieldC S n M K N}
    {q' : FinFieldC S n M K N} {gx : GIdx S n M K N → ℂ}
    (htgt : H7Domain g.M1 g.c g.hM hnn (globalLH A.H M) (k + 1) hk Yf aw μs ε ε1 νs (hC hv) ψ
      (extK q') (fun x i => gx (x, i)))
    {X : Finset (Torus S.d (n k))} (hX : X ∈ bdryDomsPost Fr A k (Zof A))
    (hXY : fineSet (S := S) (n := n) M K k (X : Set (Torus S.d (n k))) ⊆ Yf)
    (V : Set (CTorus S.d S.L Fr.N₁ m₁ K))
    (hVJ : ∀ J ∈ famAt g hnn hM1 Fr A.H hk hρ ρ r r' X V,
      ∀ x ∈ dataSites (holeStepLoc g hnn hM1 A.H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ
        (locSetXJ g hM1 A.H r r' X J)).G', fineOfC g hnn hM1 hk x ∈ Yf)
    (hXd : X ∈ oldDoms Fr A.H k) (hVs : V ∈ sitesX g hnn hM1 Fr A.H hk hρ ρ r r' X)
    (inner : Finset (holeStepLF g hnn hM1 A.H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).U)
    (cb : inner → CubeB (d := S.d) (L := S.L) (N₁ := Fr.N₁) (m₁ := m₁) (K := K) m₀ (k + 1)
      (d7Pull Fr (k + 1) (OmegaCube A.H (k + 1))))
    (hcb : ∀ u : inner, toFrame g hnn hM1 Fr hk
      (unitRep (u : (holeStepLF g hnn hM1 A.H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).U)) ∈
        Localization.box (cb u).1 (cellSide S.L m₀ m₁ (k + 1)))
    (hp : 0 < p₁) (I : LocInteraction (fun b => {u : inner // cb u = b} → Rn N))
    (ψout : (holeStepLF g hnn hM1 A.H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).U → Fin N → ℂ)
    (hrψ : 0 < rψ) (hfac : 0 < fac) {κX κV Cres : ℝ}
    (hres : OldResumSite g hnn hM1 Fr A.H hk hρ ρ r r' κ₁ κX κV Cres) (hCres : 0 < Cres)
    (hκV : I.κH ≤ κV) (T : Finset (CubeB (d := S.d) (L := S.L) (N₁ := Fr.N₁) (m₁ := m₁) (K := K) m₀ (k + 1)
      (d7Pull Fr (k + 1) (OmegaCube A.H (k + 1))))) :
    ‖oldClusterSite g hnn hM1 Fr A.H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ inner cb hp I ψout rψ
        (rho4 S.d S.L N BG κ) ρ r r' rep A X (extK q') hv gx V T‖ ≤
      CPE S.d S.L (I.Kc + 1) I.κH I.κ0 I.κ' *
        (fac * Cres * Real.exp (-(rate - κX) * d7Size Fr A k X)) *
        Real.exp (-I.κ0 * treeLenCovOne (d := S.d) (L := S.L) (N₁ := Fr.N₁) (m₁ := m₁) (K := K)
          m₀ (k + 1) V) *
        Real.exp (-I.κ' * dExt T) := by
  obtain ⟨-, -, hVd, hm⟩ := exists_of_mem_sitesX g hnn hM1 hVs
  set t := treeLenCovOne (d := S.d) (L := S.L) (N₁ := Fr.N₁) (m₁ := m₁) (K := K) m₀ (k + 1) V
    with ht
  set D := d7Size Fr A k X with hD
  have htn : 0 ≤ t := treeLenCovOne_nonneg _ _ _
  have hsum := hres X hXd V
  have hB : 0 < fac * Cres * Real.exp (-(rate - κX) * D) * Real.exp (-κV * t) := by positivity
  have hG : ∀ Φ, ‖oldMarkSite g hnn hM1 Fr A.H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ inner cb ψout rψ
      (rho4 S.d S.L N BG κ) ρ r r' rep A X (extK q') hv gx V Φ‖ ≤
      fac * Cres * Real.exp (-(rate - κX) * D) * Real.exp (-κV * t) := fun Φ => by
    refine (norm_oldMarkSite_le g hnn hM1 hk hrec hA hk1 hρ z h₀ a₁ ν β p₁ δ hS HB hm₁ hN hM hag ha₁ ha₂ hκ hMc hMX hδ0 hε hδ hphi hmarD hαD hsm hκ₁ hκ₁κ ρ r r' hIn hDat htgt hX hXY V hVJ inner cb ψout hrψ Φ).trans ?_
    calc fac * Real.exp (-rate * D) * ∑ J ∈ famAt g hnn hM1 Fr A.H hk hρ ρ r r' X V,
          Real.exp (-(κ₁ - 1) * (locCubes g (coverOf (locG' g hnn hM1 A.H hk hρ
            (locSetXJ g hM1 A.H r r' X J))) J).card)
        ≤ fac * Real.exp (-rate * D) * (Cres * Real.exp (κX * D) * Real.exp (-κV * t)) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = fac * Cres * Real.exp (-(rate - κX) * D) * Real.exp (-κV * t) := by
          rw [show -(rate - κX) * D = -rate * D + κX * D by ring, Real.exp_add]; ring
  have := (holeStepLF g hnn hM1 A.H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).isProbabilityMeasure_cubeMeasure
    inner cb hp
  have hspec := markTerm_spec_of_norm_le I
    ((holeStepLF g hnn hM1 A.H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).cubeMeasure inner cb) Fr.divN₁ hk
    (d7Pull_isPiUnion Fr hnn hk (OmegaCube A.H (k + 1))) V hVd hm _
    (measurable_oldMarkSite g hnn hM1 hk hrec hA hk1 hρ z h₀ a₁ ν β p₁ δ hS HB hm₁ hN hM hag ha₁ ha₂ hκ hMc hMX hδ0 hε hδ hphi hmarD hαD hsm hκ₁ hκ₁κ ρ r r' hIn hDat htgt hX hXY V hVJ inner cb ψout)
    (oldMarkSite_dep g hnn hM1 Fr A.H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ inner cb hcb ψout rψ
      (rho4 S.d S.L N BG κ) ρ r r' rep A X (extK q') hv gx V) hB hG T
  refine hspec.1.trans ?_
  have hCPE : 0 ≤ CPE S.d S.L (I.Kc + 1) I.κH I.κ0 I.κ' := by
    have := one_le_c1 S.d S.L
    unfold CPE
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (by linarith))
      (Real.exp_pos _).le
  have hexp : Real.exp (-κV * t) * Real.exp ((I.κH - I.κ0) * t) ≤ Real.exp (-I.κ0 * t) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.2 (by nlinarith)
  calc CPE S.d S.L (I.Kc + 1) I.κH I.κ0 I.κ' *
        (fac * Cres * Real.exp (-(rate - κX) * D) * Real.exp (-κV * t)) *
        Real.exp ((I.κH - I.κ0) * t) * Real.exp (-I.κ' * dExt T)
      = CPE S.d S.L (I.Kc + 1) I.κH I.κ0 I.κ' * (fac * Cres * Real.exp (-(rate - κX) * D)) *
        (Real.exp (-κV * t) * Real.exp ((I.κH - I.κ0) * t)) * Real.exp (-I.κ' * dExt T) := by ring
    _ ≤ CPE S.d S.L (I.Kc + 1) I.κH I.κ0 I.κ' * (fac * Cres * Real.exp (-(rate - κX) * D)) *
        Real.exp (-I.κ0 * t) * Real.exp (-I.κ' * dExt T) := by
      refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp ?_) (Real.exp_pos _).le
      exact mul_nonneg hCPE (by positivity)

open Classical in
/-- **The old part of the boundary terms at an output label `Y`** (P6 (4.32)–(4.34); FLUCTUATION
Theorem 3.1 (c)): the sum, over the sets `T` of cubes of `Ω_{k+1}` with output label `Y`, over the old
labels `X ∈ Xs` and over the good sites `V` of their marks whose cubes lie in `T`, of the cluster
terms of the marks of `(X, V)` at `T` (the terms with cubes of `V` outside `T` vanish, Theorem 3.4). -/
noncomputable def oldBAt {m₀ : ℕ} (F : FineSizeFrame S n M K m₀ m₁) (H : RegionHistory S n R k0 K)
    {k : ℕ} (hk : k + 1 ≤ K) (hk1 : 1 ≤ k) (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (ψ : MultiFieldC S n M K N)
    (z : ℝ) (h₀ : Fin N → ℝ) (a₁ ν β p₁ δ : ℝ)
    (inner : Finset (holeStepLF g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).U)
    (cb : inner → CubeB (d := S.d) (L := S.L) (N₁ := F.N₁) (m₁ := m₁) (K := K) m₀ (k + 1)
      (d7Pull F (k + 1) (OmegaCube H (k + 1))))
    (hp : 0 < p₁) (I : LocInteraction (fun b => {u : inner // cb u = b} → Rn N))
    (ψout : (holeStepLF g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).U → Fin N → ℂ) (rψ : ℝ)
    (ρc : ℝ) (ρ r r' : ℕ) {geo : Geo S n R M} {cs : OpConsts} {P : BudgetConsts}
    (rep : Rep S n R k0 K M N geo cs P k) (A : LabHist S n R k0 K)
    (Xs : Finset (Finset (Torus S.d (n k)))) (ψ' : MultiFieldC S n M K N)
    (hv : EuclideanSpace ℝ (Fin N)) (gx : GIdx S n M K N → ℂ) (Y : Finset (Torus S.d (n (k + 1)))) :
    ℂ :=
  ∑ T ∈ Finset.univ.filter (fun T => outLabel F k (OmegaCube H (k + 1)) T = Y),
    ∑ X ∈ Xs, ∑ V ∈ (sitesX g hnn hM1 F H hk hρ ρ r r' X).filter
        (fun V => blocksOf m₀ (k + 1) (d7Pull F (k + 1) (OmegaCube H (k + 1))) V ⊆ T),
      oldClusterSite g hnn hM1 F H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ inner cb hp I ψout rψ ρc ρ r r' rep A
        X ψ' hv gx V T

end SiteMarks

end Balaban.RootFSpine
