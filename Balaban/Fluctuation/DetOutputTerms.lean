/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.DetCauchyBgActivity
public import Balaban.Fluctuation.RootMarkGeom
public import Balaban.Localization.XiCRawOpen
public import Balaban.Localization.FootprintMargin
public import Balaban.Localization.I5Local
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The determinant part of the step as a family of localized terms

`DetCauchyBgActivity` constructs, for a datum `D` of the chart `Ξ^c(𝔹_{k+1}; 1, ε)`, the activities
`detActivityBg D y Y` of the rooted determinant of the unit block `y`, and an element of the
structure `DetExpansionC` of the step.  That structure records the terms at the one datum of the
step, their sum and their bound.  This file records the remaining proved properties.

## The root of a unit block

* `rootIdxOf_eq_unitBlock1`: the root index of a unit block `y` is its `L`-block
  `unitBlock1 y` (for every generating set).
* `rootIdxOf_eq_of_mem_blockU`, `rootCube_rootIdxOf_of_mem_blockU`: for a unit block `y` of the
  block `B(z)` of a step, the root index of `y` is `z` and its root cube is `rootCube z`.

## The record

* `DetExpansionLocC S m₀ z ε κ'' c_det`: terms `term D T` defined for every block datum `D`, with,
  for the data of the chart `Ξ^c(𝔹_{k+1}; 1, ε)`:
  - `sum_eq`: the terms add up to the rooted trace of `B(z)` at the uncut background of `D`;
  - `bound`: `‖term D T‖ ≤ c_det e^{-κ'' d(T)}`, with the same constants for all data;
  - `anchor`: a non-zero term has the root cube of `z` in `T`, and `T` is a polymer;
  - `local_resDep`: two data whose raw data agree on the sets `resDep x`, `x` a site of `T` in
    `Ω₁`, have the same term;
  - `analyticAt_raw`: there is one function of all raw data, analytic at the raw datum of every
    datum of the chart, which is the term there.
* `DetExpansionLocC.toDetExpansionC`, `DetExpansionLocC.atDatum`: the forgetful maps to
  `DetExpansionC` at the datum of the step and at every datum of the family `S.withDatum D`.
* `DetExpansionLocC.withDatum`: the record of `S` is a record of every step `S.withDatum D`.
* `DetExpansionLocC.weaken`, `term_eq_zero_of_not_mem`, `term_eq_of_agreeOn` (locality in terms of
  the thickening `thickSet` of `I5Local`), `analyticOnNhd_rawSub` (the term is analytic on the
  chart as an open subset of the subspace `rawSub` of raw data of data).
* `exists_detExpansionLocC_of_chart`: the record has an element whose terms are the sums over
  `y ∈ B(z)` of the activities `detActivityBg D y T`.

## The dependency set

* `detDepRadius L n = 3 L^n - 1`, `resDep_coordNear`, `thickSet_coordNear`: for a generating set of
  level `n` every site of `resDep x` is, in each coordinate, at distance at most `3 L^n - 1` from
  `x` (distance of lifts, `CoordNear`); hence the dependency set of a term lies in the
  neighbourhood of radius `3 L^n - 1` of its polymer.
* `detDepRadius_lt_cellSide`: this radius is less than one cell of `π_K` when `3 ≤ L^{m₀ + m₁}`.
* `DetExpansionLocC.term_eq_of_agree_near`: two data of the chart which agree at all sites within
  this distance of the polymer `T` have the same term.

## What is not proved

* Sharp locality: the class asks that a term depend on the datum on its polymer only
  (`SFTermClauses.localE`).  The dependency set proved here is the polymer and a collar of width
  `3 L^{k+1} - 1` sites around it.
* Analyticity on a domain of fields of the class.  The analyticity is at the raw data of the data
  of the chart; the chart is open in the subspace `rawSub` and not in the space of all raw data.
* The size of the constant against the energy constant of the class (`DetPrefactor`), the
  covariance of the terms under the symmetries of the paving (`DetActivitySymm`), the agreement of
  the terms on different tori, the renormalization of the constant part, and the identification
  of the full output density of the step.  Nothing is said about general classes.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.Analysis
  Balaban.SmallField Balaban.SmallField.Def6 Finset Matrix

/-! ### The root of a unit block -/

section Root

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}

/-- **The root index of a unit block is its `L`-block**: the coarse site of the block of side
`L^{k+1}` containing the sites of the unit block `y` is `unitBlock1 y`. -/
theorem rootIdxOf_eq_unitBlock1 (y : unitPts G) :
    rootIdxOf y = unitBlock1 (y : UnitTorus d L N₁ m₁ k) := by
  obtain ⟨x, -, hx⟩ := (mem_unitPts G).1 y.2
  rw [rootIdxOf_eq hx, ← hx]
  exact ((mem_fineBlock_iff_unitBlock1 (z := blockIndex x)).1 rfl).symm

variable {m₀ : ℕ} {S : StepSetting d L N₁ m₁ k N ϱ}
  {z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))}

/-- For a unit block `y` of the block `B(z)` of a step, the root index of `y` is `z`. -/
theorem rootIdxOf_eq_of_mem_blockU {y : S.U} (hy : y ∈ S.blockU z) : rootIdxOf y = z := by
  rw [rootIdxOf_eq_unitBlock1]
  simpa [StepSetting.blockU] using hy

/-- For a unit block `y` of the block `B(z)` of a step, the root cube of `y` is the root cube of
`z`: the cube of `π_{k+1}` that contains the block `B(z)`. -/
theorem rootCube_rootIdxOf_of_mem_blockU {y : S.U} (hy : y ∈ S.blockU z) :
    rootCube (m₀ := m₀) (rootIdxOf y) = rootCube (m₀ := m₀) (K := k + 1) z := by
  rw [rootIdxOf_eq_of_mem_blockU hy]

/-- The root cube of a unit block is the cell of the block (`StepSetting.cellOf`). -/
theorem cellOf_eq_rootCube_rootIdxOf (y : S.U) :
    S.cellOf m₀ y = rootCube (m₀ := m₀) (rootIdxOf y) := by
  have hy : y ∈ S.blockU (unitBlock1 (y : UnitTorus d L N₁ m₁ k)) := by
    simp [StepSetting.blockU]
  rw [cellOf_eq_rootCube hy, rootIdxOf_eq_unitBlock1]

end Root

/-! ### The record -/

section Record

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- **The determinant part of the step as a family of localized terms.**  For a step `S`, a root
`z` and a radius `ε` of the chart `Ξ^c(𝔹_{k+1}; 1, ε)`: terms `term D T`, defined for every block
datum `D` and every finite set `T` of cubes of `π_{k+1}`, such that for the data `D` of the chart

* `sum_eq`: the terms add up to the rooted trace `-½ ∑_{y ∈ B(z)} tr 𝕃(y, y)` of the block `B(z)`
  at the uncut background `(bgFieldC, bgMultC)` of `D`;
* `bound`: `‖term D T‖ ≤ c_det e^{-κ'' d(T)}`, with the same `c_det`, `κ''` for all data;
* `anchor`: if `term D T ≠ 0` then the root cube of `z` belongs to `T` and the sites of `T` form
  a polymer;
* `local_resDep`: two data of the chart whose raw data agree on the sets `resDep x`, `x` a site
  of `T` in `Ω₁`, have the same term at `T`;
* `analyticAt_raw`: there is a function of all raw data which is analytic at the raw datum of
  every datum of the chart and is the term at `T` there.

The last two fields are weaker than the clauses of the class: the dependency set is larger than
the polymer, and the analyticity is at the points of a set which is not open in the space of raw
data. -/
structure DetExpansionLocC (S : StepSetting d L N₁ m₁ k N ϱ) (m₀ : ℕ)
    (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))) (eps κ'' cdet : ℝ) where
  /-- The term of the set `T` of cubes as a function of the block datum. -/
  term : BgData S.G' N → Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀
    (k + 1) Set.univ) → ℂ
  sum_eq : ∀ D : BgData S.G' N, XiCData S.G' S.a S.ν (k + 1) 1 eps D →
    rootTrace S.G' S.a S.a₁ S.ν (unitQ S.G') (unitP S.G') (S.blockU z) (fun _ => 1)
        (svec S.G' (bgFieldC S.G' S.a S.ν (bgC0 d L N) D))
        (bgMultC S.G' S.a S.ν (bgC0 d L N) D) = ∑ T, term D T
  bound : ∀ D : BgData S.G' N, XiCData S.G' S.a S.ν (k + 1) 1 eps D →
    ∀ T, ‖term D T‖ ≤ cdet * Real.exp (-κ'' * dExt T)
  anchor : ∀ D : BgData S.G' N, XiCData S.G' S.a S.ν (k + 1) 1 eps D →
    ∀ T, term D T ≠ 0 →
      rootCube (m₀ := m₀) (K := k + 1) z ∈ T ∧ IsPolyDom m₀ (k + 1) (sitesOf T)
  local_resDep : ∀ D D₂ : BgData S.G' N, XiCData S.G' S.a S.ν (k + 1) 1 eps D →
    XiCData S.G' S.a S.ν (k + 1) 1 eps D₂ → ∀ T,
    (∀ x : S.G'.Ω 1, (x : CTorus d L N₁ m₁ (k + 1)) ∈ sitesOf T →
      ∀ w ∈ resDep S.G' (x : CTorus d L N₁ m₁ (k + 1)),
        D.Ψ w = D₂.Ψ w ∧ (w ∈ S.G'.Ω 1 → D.h w = D₂.h w)) → term D T = term D₂ T
  analyticAt_raw : ∀ T, ∃ A : RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ,
    (∀ D : BgData S.G' N, XiCData S.G' S.a S.ν (k + 1) 1 eps D → AnalyticAt ℂ A (rawOf D)) ∧
    ∀ D : BgData S.G' N, XiCData S.G' S.a S.ν (k + 1) 1 eps D → A (rawOf D) = term D T

namespace DetExpansionLocC

variable {S : StepSetting d L N₁ m₁ k N ϱ} {m₀ : ℕ}
  {z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))} {eps κ'' cdet : ℝ}

/-- **The forgetful map to `DetExpansionC`**: if the datum of the step is a datum of the chart,
the terms at that datum form a `DetExpansionC` with the same rate and constant. -/
def toDetExpansionC (E : DetExpansionLocC S m₀ z eps κ'' cdet)
    (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps S.D') : DetExpansionC S m₀ z κ'' cdet where
  term := E.term S.D'
  sum_eq := by
    rw [← rootTrace_one_eq_logAC S z]
    exact E.sum_eq S.D' hD
  bound := E.bound S.D' hD

@[simp] theorem toDetExpansionC_term (E : DetExpansionLocC S m₀ z eps κ'' cdet)
    (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps S.D') :
    (E.toDetExpansionC hD).term = E.term S.D' := rfl

/-- **The forgetful map at a datum of the family**: for a datum `D` of the chart with the
constant field `h ≡ h₀` of the step, the terms at `D` form a `DetExpansionC` of the step
`S.withDatum D`, with the same rate and constant. -/
def atDatum (E : DetExpansionLocC S m₀ z eps κ'' cdet) (D : BgData S.G' N)
    (hDh : ∀ y i, D.h y i = (S.h₀ i : ℂ)) (hX : XiCData S.G' S.a S.ν (k + 1) 1 eps D) :
    DetExpansionC (S.withDatum D hDh) m₀ z κ'' cdet where
  term := E.term D
  sum_eq := by
    rw [← rootTrace_one_eq_logAC (S.withDatum D hDh) z]
    exact E.sum_eq D hX
  bound := E.bound D hX

@[simp] theorem atDatum_term (E : DetExpansionLocC S m₀ z eps κ'' cdet) (D : BgData S.G' N)
    (hDh : ∀ y i, D.h y i = (S.h₀ i : ℂ)) (hX : XiCData S.G' S.a S.ν (k + 1) 1 eps D) :
    (E.atDatum D hDh hX).term = E.term D := rfl

/-- **The record does not depend on the datum of the step**: a record of `S` is a record of the
step `S.withDatum D` (same generating set, weights, mass, blocks and chart). -/
def withDatum (E : DetExpansionLocC S m₀ z eps κ'' cdet) (D : BgData S.G' N)
    (hDh : ∀ y i, D.h y i = (S.h₀ i : ℂ)) :
    DetExpansionLocC (S.withDatum D hDh) m₀ z eps κ'' cdet where
  term := E.term
  sum_eq := E.sum_eq
  bound := E.bound
  anchor := E.anchor
  local_resDep := E.local_resDep
  analyticAt_raw := E.analyticAt_raw

/-- A smaller rate and a larger constant. -/
def weaken (E : DetExpansionLocC S m₀ z eps κ'' cdet) {κ₂ cdet₂ : ℝ} (h0 : 0 ≤ cdet)
    (hc : cdet ≤ cdet₂) (hκ : κ₂ ≤ κ'') : DetExpansionLocC S m₀ z eps κ₂ cdet₂ where
  term := E.term
  sum_eq := E.sum_eq
  bound := fun D hD T => (E.bound D hD T).trans (by
    have hd := dExt_nonneg (m₀ := m₀) (j := k + 1) (Ω := Set.univ) T
    have he : Real.exp (-κ'' * dExt T) ≤ Real.exp (-κ₂ * dExt T) :=
      Real.exp_le_exp.2 (by nlinarith)
    exact mul_le_mul hc he (Real.exp_pos _).le (h0.trans hc))
  anchor := E.anchor
  local_resDep := E.local_resDep
  analyticAt_raw := E.analyticAt_raw

@[simp] theorem weaken_term (E : DetExpansionLocC S m₀ z eps κ'' cdet) {κ₂ cdet₂ : ℝ}
    (h0 : 0 ≤ cdet) (hc : cdet ≤ cdet₂) (hκ : κ₂ ≤ κ'') :
    (E.weaken h0 hc hκ).term = E.term := rfl

/-- A term vanishes at a set of cubes that does not contain the root cube of `z`. -/
theorem term_eq_zero_of_not_mem (E : DetExpansionLocC S m₀ z eps κ'' cdet) {D : BgData S.G' N}
    (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps D)
    {T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ)} (hT : rootCube (m₀ := m₀) (K := k + 1) z ∉ T) : E.term D T = 0 := by
  by_contra h
  exact hT (E.anchor D hD T h).1

/-- A term vanishes at a set of cubes that is not a polymer. -/
theorem term_eq_zero_of_not_isPolyDom (E : DetExpansionLocC S m₀ z eps κ'' cdet)
    {D : BgData S.G' N} (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps D)
    {T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ)} (hT : ¬ IsPolyDom m₀ (k + 1) (sitesOf T)) : E.term D T = 0 := by
  by_contra h
  exact hT (E.anchor D hD T h).2

/-- **Locality in the thickening `thickSet`** (`I5Local`): two data of the chart whose raw data
agree on the sites of `T` and on the sets `resDep x`, `x` a site of `T` in `Ω₁`, have the same
term at `T`. -/
theorem term_eq_of_agreeOn (E : DetExpansionLocC S m₀ z eps κ'' cdet) {D D₂ : BgData S.G' N}
    (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps D) (hD₂ : XiCData S.G' S.a S.ν (k + 1) 1 eps D₂)
    (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ))
    (h : agreeOn (thickSet S.G' (sitesOf T)) (rawOf D) (rawOf D₂)) :
    E.term D T = E.term D₂ T := by
  refine E.local_resDep D D₂ hD hD₂ T fun x hx w hw => ?_
  have hw' := h w (Or.inr ⟨x, hx, x.2, hw⟩)
  exact ⟨hw'.1, fun _ => hw'.2⟩

/-- **Analyticity on the chart as an open subset of the subspace of data.**  The chart is open in
the subspace `rawSub` of raw data of data (`isOpen_preimage_xiCRaw`), and on it the term is an
analytic function of the raw datum. -/
theorem analyticOnNhd_rawSub (E : DetExpansionLocC S m₀ z eps κ'' cdet)
    (H : BgHyp d L (k + 1) ϱ S.a S.ν)
    (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ)) :
    AnalyticOnNhd ℂ (fun e : rawSub N S.G' => E.term (bgOfRaw e.1 e.2) T)
      (((↑) : rawSub N S.G' → RawData d L (N₁ * L ^ m₁) (k + 1) N) ⁻¹'
        XiCRaw S.G' S.a S.ν (k + 1) 1 eps) := by
  obtain ⟨A, hA, hAv⟩ := E.analyticAt_raw T
  have hopen := isOpen_preimage_xiCRaw (G := S.G') (N := N) (n := k + 1) (σ := 1) (ε := eps) H
  have h1 : AnalyticOnNhd ℂ (fun e : rawSub N S.G' =>
      A (e : RawData d L (N₁ * L ^ m₁) (k + 1) N))
      (((↑) : rawSub N S.G' → RawData d L (N₁ * L ^ m₁) (k + 1) N) ⁻¹'
        XiCRaw S.G' S.a S.ν (k + 1) 1 eps) := by
    rintro e ⟨D, hD, he⟩
    have h2 : AnalyticAt ℂ A ((rawSub N S.G').subtypeL e) := by
      show AnalyticAt ℂ A (e : RawData d L (N₁ * L ^ m₁) (k + 1) N)
      rw [he]
      exact hA D hD
    exact h2.comp ((rawSub N S.G').subtypeL.analyticAt e)
  refine h1.congr hopen fun e he => ?_
  obtain ⟨D, hD, hDe⟩ := he
  have hbg : bgOfRaw e.1 e.2 = D := BgData.eq_of_raw ((rawOf_bgOfRaw e.1 e.2).trans hDe)
  show A (e : RawData d L (N₁ * L ^ m₁) (k + 1) N) = E.term (bgOfRaw e.1 e.2) T
  rw [hbg, hDe]
  exact hAv D hD

end DetExpansionLocC

end Record

/-! ### The record is inhabited on the chart -/

section Chart

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱm : ℝ} {m₀ : ℕ}
variable (S : StepSetting d L N₁ m₁ k N ϱ)
  {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
  {c BG κ eps Kc Cx c₂ BG₂ δ₁ δc : ℝ}

open Classical in
/-- **The localized determinant family of a step on the chart.**  Under `FlCore`, the cap and the
margins of the covariance chart, `HatConn`, `L^{m₀} ∣ N₁` and the rate condition
`e^κ > 2 (detDeg d L + 1)²`, the record `DetExpansionLocC` of the block `B(z)` has an element whose
term at the datum `D` and the polymer `T` is the sum over the unit blocks `y ∈ B(z)` of the
activities `detActivityBg D y T`; its rate is `(κ - log 2 - 2 log (detDeg d L + 1)) / (2 d L)` and
its constant is `L^d · ½ N covBLog d L a_k (a₁/L²) κ / (1 - (detDeg d L + 1)² · 2 / e^κ)`, which
involves neither the torus, nor `z`, nor the datum. -/
theorem exists_detExpansionLocC_of_chart
    (hC : FlCore N S.G' Hm S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (hδc : 0 ≤ δc)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4) (hconn : HatConn S.G') (hN : L ^ m₀ ∣ N₁)
    (hz : ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp κ) < 1)
    (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))) :
    ∃ E : DetExpansionLocC S m₀ z eps
        ((κ - Real.log 2 - 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) / (2 * d * L))
        ((L : ℝ) ^ d * ((1 / 2 : ℝ) * N * covBLog d L (S.a k) (S.a₁ / (L : ℝ) ^ 2) κ /
          (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp κ)))),
      ∀ D T, E.term D T =
        ∑ y ∈ S.blockU z, detActivityBg m₀ S.a S.a₁ S.ν (rho4 d L N BG κ) D y T := by
  have hc : 0 ≤ covBLog d L (S.a k) (S.a₁ / (L : ℝ) ^ 2) κ := by
    unfold covBLog
    have := covB4_nonneg d L (S.a k) κ
    have := (xSetting_of_flCore hC S.hk1).hak_pos
    positivity
  have hC0 : 0 ≤ (1 / 2 : ℝ) * N * covBLog d L (S.a k) (S.a₁ / (L : ℝ) ^ 2) κ /
      (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp κ)) :=
    div_nonneg (by positivity) (by linarith)
  refine ⟨⟨fun D T => ∑ y ∈ S.blockU z,
    detActivityBg m₀ S.a S.a₁ S.ν (rho4 d L N BG κ) D y T, fun D hD => ?_, fun D hD T => ?_,
    fun D hD T hT => ?_, fun D D₂ hD hD₂ T hdata => ?_, fun T => ?_⟩, fun _ _ => rfl⟩
  · rw [← rootTraceBg_one_eq_of_flCore hC hD,
      rootTraceBg_eq_sum_single S.a S.a₁ S.ν (rho4 d L N BG κ) (S.blockU z) D (fun _ => 1),
      Finset.sum_comm]
    exact Finset.sum_congr rfl fun y _ =>
      sum_detActivityBg_eq S.a S.a₁ S.ν (rho4 d L N BG κ) D y
  · refine (norm_sum_le _ _).trans ?_
    have hb : ∀ y ∈ S.blockU z,
        ‖detActivityBg m₀ S.a S.a₁ S.ν (rho4 d L N BG κ) D y T‖ ≤
          (1 / 2 : ℝ) * N * covBLog d L (S.a k) (S.a₁ / (L : ℝ) ^ 2) κ /
            (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp κ)) *
          Real.exp (-((κ - Real.log 2 - 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) /
            (2 * d * L)) * dExt T) := fun y _ =>
      norm_detActivityBg_le hC S.hk1 hδc hMX hsm hdm hα hconn hD hN y hz T
    refine (Finset.sum_le_sum hb).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    have hcard : ((S.blockU z).card : ℝ) ≤ (L : ℝ) ^ d := by
      exact_mod_cast card_blockU_le S z
    have he : 0 ≤ Real.exp (-((κ - Real.log 2 - 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) /
        (2 * d * L)) * dExt T) := (Real.exp_pos _).le
    calc ((S.blockU z).card : ℝ) * ((1 / 2 : ℝ) * N *
            covBLog d L (S.a k) (S.a₁ / (L : ℝ) ^ 2) κ /
              (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp κ)) *
            Real.exp (-((κ - Real.log 2 - 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) /
              (2 * d * L)) * dExt T))
        ≤ (L : ℝ) ^ d * ((1 / 2 : ℝ) * N *
            covBLog d L (S.a k) (S.a₁ / (L : ℝ) ^ 2) κ /
              (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp κ)) *
            Real.exp (-((κ - Real.log 2 - 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) /
              (2 * d * L)) * dExt T)) :=
          mul_le_mul_of_nonneg_right hcard (mul_nonneg hC0 he)
      _ = _ := by ring
  · obtain ⟨y, hy, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hT
    have h := detActivityBg_ne_zero_imp hC S.hk1 hδc hMX hsm hdm hα hconn hD hN hne
    rw [rootIdxOf_eq_of_mem_blockU hy] at h
    exact h
  · exact Finset.sum_congr rfl fun y _ =>
      detActivityBg_eq_of_agree hC S.hk1 hδc hMX hsm hdm hα hconn hD hD₂ hN y T hdata
  · choose A hA hAv using fun y : S.U =>
      exists_analytic_detActivityBg_raw (m₀ := m₀) hC S.hk1 hδc hMX hsm hdm hα y T
    exact ⟨fun r => ∑ y ∈ S.blockU z, A y r,
      fun D hD => Finset.analyticAt_fun_sum _ fun y _ => hA y D hD,
      fun D hD => Finset.sum_congr rfl fun y _ => hAv y D hD⟩

end Chart

/-! ### The dependency set -/

section Dependency

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ}

/-- **The radius of the dependency set** of a term of the determinant, for a generating set of
level `n`: `r_det = 3 L^n - 1` sites (in each coordinate). -/
noncomputable def detDepRadius (L n : ℕ) : ℝ := 3 * (L : ℝ) ^ n - 1

omit [NeZero N₁] in
theorem detDepRadius_nonneg (n : ℕ) : 0 ≤ detDepRadius L n := by
  have hL1 : (1 : ℝ) ≤ (L : ℝ) ^ n :=
    one_le_pow₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L))
  unfold detDepRadius
  linarith

omit [NeZero N₁] in
/-- The radius of the dependency set is less than one cell of `π_K`, of side
`L^{K + m₀ + m₁}`, as soon as `3 ≤ L^{m₀ + m₁}`. -/
theorem detDepRadius_lt_cellSide {m₀ : ℕ} (h : 3 ≤ L ^ (m₀ + m₁)) (K : ℕ) :
    detDepRadius L K < (cellSide L m₀ m₁ K : ℝ) := by
  have hL1 : (1 : ℝ) ≤ (L : ℝ) ^ K :=
    one_le_pow₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L))
  have h3 : (3 : ℝ) ≤ (L : ℝ) ^ (m₀ + m₁) := by exact_mod_cast h
  have e : (cellSide L m₀ m₁ K : ℝ) = (L : ℝ) ^ K * (L : ℝ) ^ (m₀ + m₁) := by
    unfold cellSide
    push_cast
    rw [← pow_add]
    congr 1
    omega
  rw [e]
  unfold detDepRadius
  nlinarith

/-- **The dependency set of a site** for a generating set of level `n`: every site read by the
residual at `x` (`resDep x`) is, in each coordinate, at distance at most `3 L^n - 1` from `x`
(distance of lifts): a row site is within `L^n` of `x` and the approximate field at a row site
reads within `2 L^n - 1` of it. -/
theorem resDep_coordNear {n : ℕ} (hG : IsLevel G n) {x v : Torus d (N₁ * L ^ m₁ * L ^ K)}
    (hv : v ∈ resDep G x) (μ : Fin d) :
    CoordNear (N₁ * L ^ m₁ * L ^ K) (detDepRadius L n) (v μ) (x μ) := by
  classical
  unfold resDep at hv
  obtain ⟨u, hu, hvu⟩ := Finset.mem_biUnion.1 hv
  have h1 := (approxDep_coord_bound hG hvu μ).symm
  have h2 := resSites_coord_bound hG hu μ
  refine (h1.trans h2).mono ?_
  unfold detDepRadius
  linarith

/-- **The dependency set of a set of sites** for a generating set of level `n`: every site of
the thickening `thickSet G Y` (the set `Y` and the sets `resDep x`, `x ∈ Y ∩ Ω₁`) is, in each
coordinate, at distance at most `3 L^n - 1` from a site of `Y`. -/
theorem thickSet_coordNear {n : ℕ} (hG : IsLevel G n) (Y : Set (CTorus d L N₁ m₁ K))
    {v : CTorus d L N₁ m₁ K} (hv : v ∈ thickSet G Y) :
    ∃ x ∈ Y, ∀ μ, CoordNear (N₁ * L ^ m₁ * L ^ K) (detDepRadius L n) (v μ) (x μ) := by
  rcases hv with hv | ⟨x, hx, -, hvx⟩
  · exact ⟨v, hv, fun μ => CoordNear.refl (detDepRadius_nonneg n) _⟩
  · exact ⟨x, hx, fun μ => resDep_coordNear hG hvx μ⟩

end Dependency

section DependencyStep

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  {S : StepSetting d L N₁ m₁ k N ϱ} {m₀ : ℕ}
  {z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))} {eps κ'' cdet : ℝ}

/-- **Locality of a term in a neighbourhood of its polymer.**  Two data of the chart whose raw
data agree at every site which is, in each coordinate, within `r_det = 3 L^{k+1} - 1` of a site of
`T` have the same term at `T`.  (The generating set of a step has level `k + 1`.) -/
theorem DetExpansionLocC.term_eq_of_agree_near (E : DetExpansionLocC S m₀ z eps κ'' cdet)
    {D D₂ : BgData S.G' N} (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps D)
    (hD₂ : XiCData S.G' S.a S.ν (k + 1) 1 eps D₂)
    (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ))
    (h : ∀ v : CTorus d L N₁ m₁ (k + 1), (∃ x ∈ sitesOf T, ∀ μ,
      CoordNear (N₁ * L ^ m₁ * L ^ (k + 1)) (detDepRadius L (k + 1)) (v μ) (x μ)) →
      D.Ψ v = D₂.Ψ v ∧ D.h v = D₂.h v) :
    E.term D T = E.term D₂ T :=
  E.term_eq_of_agreeOn hD hD₂ T fun v hv => h v (thickSet_coordNear S.hG' _ hv)

end DependencyStep

end Balaban.Fluctuation
