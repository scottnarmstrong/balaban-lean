/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.LFOldCoefBound
public import Balaban.Fluctuation.HoleStepMarks

/-!
# The marks of the re-expanded old boundary terms (P6 (4.32)–(4.34))

For the step on a region of a history and an old label `X` with a family `J` of cover cubes, the
mark of the cluster expansion of the measure of the step is the coefficient `T(X, J)` of the local
pair (reading HS-1′, `oldCoefLoc`), as a function of the variables of the cubes of the block structure
of the measure, cut off outside the ball `|ψ̂_b| < r_ψ` of the unit points of the local pair
(`HoleStep.markOf`):

* `locUnits`: the unit points of the local pair, as unit points of the step;
* `oldCoefLoc_congr`: the coefficient reads the fluctuation field only there;
* `oldMarkLF`: **the mark of `(X, J)`**;
* `oldMarkLF_dep`: it depends only on the cubes of the integration variables of the local pair;
* `norm_oldMarkLF_le`: **the bound of P6 (4.34) for the mark**, `|G_{X,J}| ≤ fac e^{-rate d^cov(X)}
  e^{-(κ₁ - 1)|J_V|}`;
* `measurable_oldMarkLF`: it is measurable (the coefficient is analytic in the fluctuation field on the
  ball, `analyticOnNhd_oldCoefLoc_fluct`).

The bound and the measurability are conditional on the two named inputs of OPEN-H7-MIXED for the
local pair (`H7MixedInnerLoc`, `H7MixedDatumLoc`), through `norm_oldCoefLoc_le_of_inputs` and
`analyticOnNhd_oldCoefLoc_fluct`.
-/

@[expose] public section

open MeasureTheory Balaban Balaban.LargeField Balaban.LargeField.Def7 Balaban.Multiscale
  Balaban.Localization Balaban.Fluctuation Balaban.LargeField.RegionHistory Balaban.Background

namespace Balaban.RootFSpine

section Marks

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {N m₁ : ℕ}
  (g : Geo S n R M) (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) (hM1 : g.M1 = S.L ^ m₁)

open Classical in
/-- **The unit points of the local pair, as unit points of the step.** -/
noncomputable def locUnits (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K) (hk1 : 1 ≤ k)
    (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (ψ : MultiFieldC S n M K N) (z : ℝ) (h₀ : Fin N → ℝ)
    (a₁ ν β p₁ δ : ℝ) (V : Set (CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1))) :
    Finset (holeStepLF g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).U :=
  Finset.univ.filter fun b =>
    (b : UnitTorus S.d S.L (g.c * n (k + 1)) m₁ k) ∈
      unitPts (holeStepLoc g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).G'

omit [NeZero M] in
/-- A unit point of the local pair is in `locUnits`. -/
theorem mem_locUnits (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K) (hk1 : 1 ≤ k)
    (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (ψ : MultiFieldC S n M K N) (z : ℝ) (h₀ : Fin N → ℝ)
    (a₁ ν β p₁ δ : ℝ) (V : Set (CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)))
    (b : (holeStepLoc g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).U) :
    (⟨b.1, HoleStep.unitPts_restrict_subset _ _ _ _ _ _ _ b.2⟩ :
      (holeStepLF g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).U) ∈
      locUnits g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V := by
  classical
  simp only [locUnits, Finset.mem_filter, Finset.mem_univ, true_and]
  exact b.2

/-- **The coefficient reads the fluctuation field only at the unit points of the local pair.** -/
theorem oldCoefLoc_congr (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K) (hk1 : 1 ≤ k)
    (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (ψ : MultiFieldC S n M K N) (z : ℝ) (h₀ : Fin N → ℝ)
    (a₁ ν β p₁ δ : ℝ) (ρc : ℝ) (ρ r r' : ℕ) {geo : Geo S n R M} {cs : OpConsts}
    {P : BudgetConsts} (rep : Rep S n R k0 K M N geo cs P k) (A : LabHist S n R k0 K)
    (X : Finset (Torus S.d (n k))) (ψ' : MultiFieldC S n M K N) (hv : EuclideanSpace ℝ (Fin N))
    (gx : GIdx S n M K N → ℂ) (J : Finset (ℕ × CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)))
    (ψ₁ ψ₂ : (holeStepLF g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).U → Fin N → ℂ)
    (h : ∀ b ∈ locUnits g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ (locSetXJ g hM1 H r r' X J),
      ψ₁ b = ψ₂ b) :
    oldCoefLoc g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ ρc ρ r r' rep A X ψ' hv gx J ψ₁ =
      oldCoefLoc g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ ρc ρ r r' rep A X ψ' hv gx J ψ₂ := by
  unfold oldCoefLoc
  congr 1
  funext b
  exact h _ (mem_locUnits g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ _ b)

/-- **The mark of the re-expanded old term `(X, J)`** (P6 (4.32)–(4.33)): the coefficient on the
local pair as a function of the variables of the cubes of the block structure of the measure
(`inner`, the cube assignment `cb`, the fixed values `ψout`), cut off outside the ball `|ψ̂_b| < r_ψ`
of the unit points of the local pair. -/
noncomputable def oldMarkLF (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K) (hk1 : 1 ≤ k)
    (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (ψ : MultiFieldC S n M K N) (z : ℝ) (h₀ : Fin N → ℝ)
    (a₁ ν β p₁ δ : ℝ) {m₀ : ℕ} {Ω : Set (CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1))}
    (inner : Finset (holeStepLF g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).U)
    (cb : inner → CubeB (d := S.d) (L := S.L) (N₁ := g.c * n (k + 1)) (m₁ := m₁) (K := k + 1) m₀
      (k + 1) Ω)
    (ψout : (holeStepLF g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).U → Fin N → ℂ) (rψ : ℝ)
    (ρc : ℝ) (ρ r r' : ℕ) {geo : Geo S n R M} {cs : OpConsts} {P : BudgetConsts}
    (rep : Rep S n R k0 K M N geo cs P k) (A : LabHist S n R k0 K) (X : Finset (Torus S.d (n k)))
    (ψ' : MultiFieldC S n M K N) (hv : EuclideanSpace ℝ (Fin N)) (gx : GIdx S n M K N → ℂ)
    (J : Finset (ℕ × CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1))) :
    (∀ b, {u : inner // cb u = b} → Rn N) → ℂ :=
  (holeStepLF g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).markOf inner cb ψout
    (locUnits g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ (locSetXJ g hM1 H r r' X J)) rψ
    (oldCoefLoc g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ ρc ρ r r' rep A X ψ' hv gx J)

open Classical in
/-- **The mark depends only on the cubes of the integration variables of the local pair.** -/
theorem oldMarkLF_dep (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K) (hk1 : 1 ≤ k)
    (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (ψ : MultiFieldC S n M K N) (z : ℝ) (h₀ : Fin N → ℝ)
    (a₁ ν β p₁ δ : ℝ) {m₀ : ℕ} {Ω : Set (CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1))}
    (inner : Finset (holeStepLF g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).U)
    (cb : inner → CubeB (d := S.d) (L := S.L) (N₁ := g.c * n (k + 1)) (m₁ := m₁) (K := k + 1) m₀
      (k + 1) Ω)
    (ψout : (holeStepLF g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).U → Fin N → ℂ) (rψ : ℝ)
    (ρc : ℝ) (ρ r r' : ℕ) {geo : Geo S n R M} {cs : OpConsts} {P : BudgetConsts}
    (rep : Rep S n R k0 K M N geo cs P k) (A : LabHist S n R k0 K) (X : Finset (Torus S.d (n k)))
    (ψ' : MultiFieldC S n M K N) (hv : EuclideanSpace ℝ (Fin N)) (gx : GIdx S n M K N → ℂ)
    (J : Finset (ℕ × CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1))) :
    Polymer.DepOn ((inner.attach.filter fun u : inner => (u : (holeStepLF g hnn hM1 H hk hk1 hρ ψ z
        h₀ a₁ ν β p₁ δ).U) ∈ locUnits g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ
          (locSetXJ g hM1 H r r' X J)).image cb)
      (oldMarkLF g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ inner cb ψout rψ ρc ρ r r' rep A X ψ' hv
        gx J) :=
  HoleStep.markOf_dep _ inner cb ψout _ rψ _
    (oldCoefLoc_congr g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ ρc ρ r r' rep A X ψ' hv gx J)

/-- **The bound of P6 (4.34) for the mark of `(X, J)`**: under the hypotheses of
`norm_oldCoefLoc_le_of_inputs` and `r_ψ > 0`, `|G_{X,J}(Φ)| ≤ fac e^{-rate d^cov(X)}
e^{-(κ₁ - 1)|J_V|}` for every value `Φ` of the variables of the cubes (the mark vanishes off the
ball). -/
theorem norm_oldMarkLF_le {m₀' : ℕ} {Fr : FineSizeFrame S n M K m₀' m₁} {k : ℕ}
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
    (hIn : H7MixedInnerLoc g hnn hM1 A.H hk hk1 hρ z h₀ a₁ ν β p₁ δ (rho4 S.d S.L N BG κ) ρ r aw μs
      ε ε1 νs (hC hv) (Real.exp κ₁) rψ)
    (hDat : H7MixedDatumLoc g hnn hM1 A.H hk hk1 hρ z h₀ a₁ ν β p₁ δ aw μs ε ε1 νs (hC hv) ν δb)
    (J : Finset (ℕ × CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)))
    {Yf : Set (Torus S.d (M * n K * S.L ^ K))} {ψ : MultiFieldC S n M K N}
    {q' : FinFieldC S n M K N} {gx : GIdx S n M K N → ℂ}
    (htgt : H7Domain g.M1 g.c g.hM hnn (globalLH A.H M) (k + 1) hk Yf aw μs ε ε1 νs (hC hv) ψ
      (extK q') (fun x i => gx (x, i)))
    (hXY : fineSet (S := S) (n := n) M K k (X : Set (Torus S.d (n k))) ⊆ Yf)
    (hV : ∀ x ∈ dataSites (holeStepLoc g hnn hM1 A.H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ
      (locSetXJ g hM1 A.H r r' X J)).G', fineOfC g hnn hM1 hk x ∈ Yf)
    {m₀ : ℕ} {Ω : Set (CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1))}
    (inner : Finset (holeStepLF g hnn hM1 A.H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).U)
    (cb : inner → CubeB (d := S.d) (L := S.L) (N₁ := g.c * n (k + 1)) (m₁ := m₁) (K := k + 1) m₀
      (k + 1) Ω)
    (ψout : (holeStepLF g hnn hM1 A.H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).U → Fin N → ℂ)
    (hrψ : 0 < rψ) (Φ : ∀ b, {u : inner // cb u = b} → Rn N) :
    ‖oldMarkLF g hnn hM1 A.H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ inner cb ψout rψ (rho4 S.d S.L N BG κ) ρ r
        r' rep A X (extK q') hv gx J Φ‖ ≤
      fac * Real.exp (-rate * d7Size Fr A k X) *
        Real.exp (-(κ₁ - 1) * (locCubes g (coverOf (holeStepLoc g hnn hM1 A.H hk hk1 hρ ψ z h₀ a₁ ν
          β p₁ δ (locSetXJ g hM1 A.H r r' X J)).G') J).card) := by
  have hT : ∀ ψh : (holeStepLF g hnn hM1 A.H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).U → Fin N → ℂ,
      (∀ b ∈ locUnits g hnn hM1 A.H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ (locSetXJ g hM1 A.H r r' X J),
        vn (ψh b) < rψ) →
      ‖oldCoefLoc g hnn hM1 A.H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ (rho4 S.d S.L N BG κ) ρ r r' rep A X
          (extK q') hv gx J ψh‖ ≤
        fac * Real.exp (-rate * d7Size Fr A k X) *
          Real.exp (-(κ₁ - 1) * (locCubes g (coverOf (holeStepLoc g hnn hM1 A.H hk hk1 hρ ψ z h₀ a₁
            ν β p₁ δ (locSetXJ g hM1 A.H r r' X J)).G') J).card) :=
    fun ψh hψh => norm_oldCoefLoc_le_of_inputs g hnn hM1 hk hrec hA hX hk1 hρ z h₀ a₁ ν β p₁ δ hS HB hm₁ hN hM hag ha₁ ha₂ hκ hMc hMX hδ0 hε hδ hphi hmarD hαD hsm hκ₁ hκ₁κ ρ r r' hIn hDat J htgt hXY hV
      (fun b => hψh _ (mem_locUnits g hnn hM1 A.H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ _ b))
  have hB0 := (norm_nonneg _).trans (hT 0 fun b _ => by simpa [vn] using hrψ)
  exact HoleStep.markOf_bound _ inner cb ψout _ rψ _ hB0 hT Φ

/-- **The mark of `(X, J)` is measurable** (the coefficient is analytic in the fluctuation field on
the ball, `analyticOnNhd_oldCoefLoc_fluct`). -/
theorem measurable_oldMarkLF {m₀' : ℕ} {Fr : FineSizeFrame S n M K m₀' m₁} {k : ℕ}
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
    (hIn : H7MixedInnerLoc g hnn hM1 A.H hk hk1 hρ z h₀ a₁ ν β p₁ δ (rho4 S.d S.L N BG κ) ρ r aw μs
      ε ε1 νs (hC hv) (Real.exp κ₁) rψ)
    (hDat : H7MixedDatumLoc g hnn hM1 A.H hk hk1 hρ z h₀ a₁ ν β p₁ δ aw μs ε ε1 νs (hC hv) ν δb)
    (J : Finset (ℕ × CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)))
    {Yf : Set (Torus S.d (M * n K * S.L ^ K))} {ψ : MultiFieldC S n M K N}
    {q' : FinFieldC S n M K N} {gx : GIdx S n M K N → ℂ}
    (htgt : H7Domain g.M1 g.c g.hM hnn (globalLH A.H M) (k + 1) hk Yf aw μs ε ε1 νs (hC hv) ψ
      (extK q') (fun x i => gx (x, i)))
    (hXY : fineSet (S := S) (n := n) M K k (X : Set (Torus S.d (n k))) ⊆ Yf)
    (hV : ∀ x ∈ dataSites (holeStepLoc g hnn hM1 A.H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ
      (locSetXJ g hM1 A.H r r' X J)).G', fineOfC g hnn hM1 hk x ∈ Yf)
    {m₀ : ℕ} {Ω : Set (CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1))}
    (inner : Finset (holeStepLF g hnn hM1 A.H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).U)
    (cb : inner → CubeB (d := S.d) (L := S.L) (N₁ := g.c * n (k + 1)) (m₁ := m₁) (K := k + 1) m₀
      (k + 1) Ω)
    (ψout : (holeStepLF g hnn hM1 A.H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).U → Fin N → ℂ) :
    Measurable (oldMarkLF g hnn hM1 A.H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ inner cb ψout rψ
      (rho4 S.d S.L N BG κ) ρ r r' rep A X (extK q') hv gx J) := by
  have han := analyticOnNhd_oldCoefLoc_fluct g hnn hM1 hk hrec hA hX hk1 hρ z h₀ a₁ ν β p₁ δ hS HB hm₁ hN hM hag ha₁ ha₂ hκ hMc hMX hδ0 hε hδ hphi hmarD hαD hsm hκ₁ hκ₁κ ρ r r' hIn hDat J htgt hXY hV
  refine HoleStep.measurable_markOf _ inner cb ψout _ rψ _ ?_
  refine han.continuousOn.comp (f := fun ψh => restrictU _ _ _ _ _ _ _ ψh) ?_ ?_
  · exact (continuous_pi fun b => continuous_apply _).continuousOn
  · intro ψh hψh b
    exact hψh _ (mem_locUnits g hnn hM1 A.H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ _ b)

end Marks

end Balaban.RootFSpine
