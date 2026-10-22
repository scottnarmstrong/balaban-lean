/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.LFOldHS2Chain
public import Balaban.Spine.LFOldDatumPre

/-!
# The chain of reading HS-2 for the pre-`R` records (ruling R17; target (3c) of W1154e)

The step's boundary terms of scale `k + 1` are pre-`R` records: their H7 domain is taken at the
pre-`R` records `globalLHPre H M (k + 1)` (ruling R17).  The chain of reading HS-2 (`norm_oldB2_le`) is
stated with the target domain at the global records `globalLH H M`; this file states it at the pre-`R`
records.  The source domain of scale `k` (the record's post-`R` terms, `D7BdryPost`) is unchanged: the
two records have the same holes below the top scale (`omegaCNb_globalLHPre_of_ne`), so the transfer
`h7Domain_composedMulti_of_inner_withZ` applies.  The named inputs are asked at the local sets of their
use (`J ∈ allJ ρ`) and with the external field of the datum the physical field (ruling R16,
`h₀ = Re h = hv`).

* `H7MixedInnerLoc2Pre`: OPEN-H7-MIXED (remaining part) for the pre-`R` records (**open**);
* `h7Domain_composedMulti_loc2Pre`: the composite lies in the source H7 domain;
* `locConds_of_h7MixedLoc2Pre`: the local conditions of the old part at an output label from
  `H7MixedInnerLoc2Pre` and `H7MixedDatumLoc2Pre` (the latter proved, `h7MixedDatumLoc2Pre_holds`);
* `norm_oldB2Pre_le`: **the (D7) bound of the re-expanded old boundary terms of reading HS-2 at a field
  of the H7 domain of the pre-`R` records**.
-/

@[expose] public section

open MeasureTheory Balaban Balaban.LargeField Balaban.LargeField.Def7 Balaban.Multiscale
  Balaban.Localization Balaban.Fluctuation Balaban.LargeField.RegionHistory Balaban.Background
  Balaban.Polymer

namespace Balaban.RootFSpine

set_option linter.unusedSectionVars false

section Pre

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {N m₁ : ℕ}
  (g : Geo S n R M) (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) (hM1 : g.M1 = S.L ^ m₁)

/-- **OPEN-H7-MIXED, the remaining part, for the pre-`R` records** (restatement of `H7MixedInnerLoc2`,
ruling R17; **open**): for an old label `X` and a family `J ∈ allJ ρ`, the condition `H7MixedInnerLocXJ`
with the target H7 domain of scale `k + 1` at `globalLHPre H M (k + 1)`. -/
def H7MixedInnerLoc2Pre (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K) (hk1 : 1 ≤ k)
    (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (z : ℝ) (h₀ : Fin N → ℝ) (a₁ ν β p₁ δ ρc : ℝ) (ρ r r' : ℕ)
    (aw μs ε ε1 νs : ℕ → ℝ) (h : Fin N → ℂ) (Rp rψ : ℝ) : Prop :=
  ∀ (X : Finset (Torus S.d (n k))) (J : Finset (ℕ × CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1))),
    J ∈ allJ g hnn hM1 H hk hρ ρ →
    H7MixedInnerLocXJ g hnn hM1 (globalLHPre H M (k + 1)) H hk hk1 hρ z h₀ a₁ ν β p₁ δ ρc ρ r r' aw μs
      ε ε1 νs h Rp rψ X J

/-- **The composite of the local pair of reading HS-2 lies in the source H7 domain, from a field of the
target domain of the pre-`R` records** (`h7Domain_composedMulti_loc2_withZ` at the regions of
`globalLHPre H M (k + 1)`, whose holes below the top scale are those of the global records). -/
theorem h7Domain_composedMulti_loc2Pre (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K)
    (hk1 : 1 ≤ k) (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (z : ℝ) (h₀ : Fin N → ℝ) (a₁ ν β p₁ δ ρc : ℝ)
    (ρ r r' : ℕ) (aw μs ε ε1 νs : ℕ → ℝ) (h : Fin N → ℂ) {Rp rψ : ℝ} (hL : 2 ≤ S.L)
    (hIn : H7MixedInnerLoc2Pre g hnn hM1 H hk hk1 hρ z h₀ a₁ ν β p₁ δ ρc ρ r r' aw μs ε ε1 νs h Rp rψ)
    (X : Finset (Torus S.d (n k))) (J : Finset (ℕ × CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)))
    (hJa : J ∈ allJ g hnn hM1 H hk hρ ρ)
    {Yf : Set (Torus S.d (M * n K * S.L ^ K))} {ψ ψ' : MultiFieldC S n M K N}
    {gf : Torus S.d (M * n K * S.L ^ K) → Fin N → ℂ}
    (htgt : H7Domain g.M1 g.c g.hM hnn (globalLHPre H M (k + 1)) (k + 1) hk Yf aw μs ε ε1 νs h ψ ψ' gf)
    (hY : CubesOfIn (S := S) (n := n) (M := M) (K := K) (k + 1) Yf
      (fineSet (S := S) (n := n) M K k (stencilX X : Set (Torus S.d (n k))) ∪
        fineOfC g hnn hM1 hk '' (dataSites (locG' g hnn hM1 H hk hρ (locSetXJ2 g hM1 H r r' X J)) :
          Set (CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)))))
    {ψhat : (holeStepLoc2 g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ
      (locSetXJ2 g hM1 H r r' X J)).U → Fin N → ℂ}
    (hψhat : ∀ b, vn (ψhat b) < rψ)
    {s : Dec2.DecParams (coverOf (holeStepLoc2 g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ
      (locSetXJ2 g hM1 H r r' X J)).G')}
    (hs : ∀ P, ‖s P‖ < Rp) :
    H7Domain g.M1 g.c g.hM hnn (globalLH H M) k (Nat.le_of_succ_le hk)
      (fineSet (S := S) (n := n) M K k (X : Set (Torus S.d (n k)))) aw μs ε ε1 νs h
      (composedMulti g hnn hM1 hk
        (holeStepLoc2 g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ (locSetXJ2 g hM1 H r r' X J)).G' ψ
        ((holeStepLoc2 g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ (locSetXJ2 g hM1 H r r' X J)).composed
          (coverOf (holeStepLoc2 g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ
            (locSetXJ2 g hM1 H r r' X J)).G') ρc
          ((holeStepLoc2 g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ (locSetXJ2 g hM1 H r r' X J)).slocOf
            (coverOf (holeStepLoc2 g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ
              (locSetXJ2 g hM1 H r r' X J)).G')
            (locDomsLF g hM1 (holeStepLoc2 g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ
              (locSetXJ2 g hM1 H r r' X J)) ρ)
            (HoleStep.coreExt
              (coverOf (holeStepLoc2 g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ
                (locSetXJ2 g hM1 H r r' X J)).G')
              (collarCoreC (c := g.c) (H.step k) hM1 r X) s)) ψhat))
      ψ' gf :=
  h7Domain_composedMulti_loc2_withZ g hnn hM1 H hk hk1 hρ z h₀ a₁ ν β p₁ δ ρc ρ r r' aw μs ε ε1 νs h hL
    (globalLHPre H M (k + 1)).Z (fun j hj => omegaCNb_globalLHPre_of_ne H (by omega) 3) X J (hIn X J hJa)
    htgt hY hψhat hs

/-- **The local conditions of the old part at an output label from the named inputs, for the pre-`R`
records** (ruling R17): for a target field of the H7 domain of `globalLHPre A.H M (k + 1)` at the fine set
of `Y` (external field `hC hv`, the datum's field `h₀ = hv`, ruling R16), every old label `X` and every
family `J ∈ allJ ρ` with a good site whose cubes in `Ω_{k+1}` lie in a set `T` of cubes with output label
`Y`, the named inputs `H7MixedInnerLoc2Pre`, `H7MixedDatumLoc2Pre` give the conditions `hloc` of
`norm_oldBAtAt_le_of_dom_allJ` (`locConds_of_h7MixedLoc2_withZ`). -/
theorem locConds_of_h7MixedLoc2Pre {m₀ : ℕ} {Fr : FineSizeFrame S n M K m₀ m₁} {k : ℕ}
    (hk : k + 1 ≤ K) {A : LabHist S n R k0 K} (hk1 : 1 ≤ k) (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊)
    (z : ℝ) (h₀ : Fin N → ℝ) (a₁ ν β p₁ δ : ℝ) {aw μs ε ε1 νs : ℕ → ℝ} {hv : EuclideanSpace ℝ (Fin N)}
    {BG δb κ κ₁ rψ : ℝ} (hL : 2 ≤ S.L) (ρ r r' : ℕ)
    (hIn : H7MixedInnerLoc2Pre g hnn hM1 A.H hk hk1 hρ z h₀ a₁ ν β p₁ δ (rho4 S.d S.L N BG κ) ρ r r'
      aw μs ε ε1 νs (hC hv) (Real.exp κ₁) rψ)
    (hDat : H7MixedDatumLoc2Pre g hnn hM1 A.H hk hk1 hρ z h₀ a₁ ν β p₁ δ ρ r r' aw μs ε ε1 νs ν δb)
    (hh₀ : ∀ i, h₀ i = hv i)
    (Y : Finset (Torus S.d (n (k + 1)))) {ψ : MultiFieldC S n M K N} {ψ' : MultiFieldC S n M K N}
    {gf : Torus S.d (M * n K * S.L ^ K) → Fin N → ℂ}
    (htgt : H7Domain g.M1 g.c g.hM hnn (globalLHPre A.H M (k + 1)) (k + 1) hk
      (fineSet (S := S) (n := n) M K (k + 1) (Y : Set (Torus S.d (n (k + 1))))) aw μs ε ε1 νs
      (hC hv) ψ ψ' gf)
    {X : Finset (Torus S.d (n k))} (hXd : X ∈ oldDoms Fr A.H k)
    (J : Finset (ℕ × CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1))) (hJa : J ∈ allJ g hnn hM1 A.H hk hρ ρ)
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
  have he : (fun i => (h₀ i : ℂ)) = hC hv := funext fun i => by simp [hC, hh₀]
  have hD := hDat X J hJa
  rw [he] at hD
  exact locConds_of_h7MixedLoc2_withZ g hnn hM1 hk hk1 hρ z h₀ a₁ ν β p₁ δ hL ρ r r'
    (globalLHPre A.H M (k + 1)).Z (fun j hj => omegaCNb_globalLHPre_of_ne A.H (by omega) 3) Y htgt hXd J
    (hIn X J hJa) hD T hTY hfin hJ hT

/-- **The (D7) bound of the re-expanded old boundary terms of reading HS-2, at a field of the H7 domain
of the pre-`R` records** (P6 (4.34); LFR Lemma IV.1.5 (iii); ruling R17): as `norm_oldB2_le`, with the
target H7 domain of scale `k + 1` at `globalLHPre A.H M (k + 1)`, the named inputs `H7MixedInnerLoc2Pre`
(open) and `H7MixedDatumLoc2Pre` (proved, `h7MixedDatumLoc2Pre_holds`) and the datum's external field the
physical field (`h₀ = hv`, ruling R16). -/
theorem norm_oldB2Pre_le {m₀ : ℕ} {Fr : FineSizeFrame S n M K m₀ m₁} {k : ℕ}
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
    (hIn : H7MixedInnerLoc2Pre g hnn hM1 A.H hk hk1 hρ z h₀ a₁ ν β p₁ δ (rho4 S.d S.L N BG κ) ρ r r'
      aw μs ε ε1 νs (hC hv) (Real.exp κ₁) rψ)
    (hDat : H7MixedDatumLoc2Pre g hnn hM1 A.H hk hk1 hρ z h₀ a₁ ν β p₁ δ ρ r r' aw μs ε ε1 νs ν δb)
    (hh₀ : ∀ i, h₀ i = hv i)
    (hXs : ∀ X ∈ oldDoms Fr A.H k, X ∈ bdryDomsPost Fr A k (Zof A))
    (Y : Finset (Torus S.d (n (k + 1)))) (p : FinFieldC S n M K N × FinFieldC S n M K N ×
      (GIdx S n M K N → ℂ))
    (htgt : H7Domain g.M1 g.c g.hM hnn (globalLHPre A.H M (k + 1)) (k + 1) hk
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
  exact norm_oldBOf_le_of_dom_allJ g hnn hM1 true stencilX hk hrec hA hk1 hρ z h₀ a₁ ν β p₁ δ
    hS HB hm₁ hN hM hag ha₁ ha₂ hκ hMc hMX hδ0 hε hδ hphi hmarD hαD hsm hκ₁ hκ₁κ ρ r r' hXs Y p
    (fun X hX J hJa T hTY hfin hJ hT => locConds_of_h7MixedLoc2Pre g hnn hM1 hk hk1 hρ z h₀ a₁ ν β p₁ δ
      hL ρ r r' hIn hDat hh₀ Y htgt hX J hJa T hTY hfin hJ hT)
    inner cb hcb hp I ψout hrψ hfac hres hCres hκV hαX hκ'

end Pre

end Balaban.RootFSpine
