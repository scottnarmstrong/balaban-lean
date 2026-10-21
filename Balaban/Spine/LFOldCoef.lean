/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.LFHoleStepPhi
public import Balaban.Fluctuation.HoleStepOldCoef

/-!
# The coefficients of the re-expansion of the old boundary terms of a history (P6 (4.32)–(4.34))

For the step on a region of a history (`holeStepLF`, or any `HoleStep` on the cover torus of the step)
and a boundary term `ℬ^{(k)}(X, 𝔸)` of the representation whose domain meets `Ω_{k+1}`:

* `oldTermLF`: the old term as a function of the field on the unit points of `Ω_{k+1}` (at the
  multiscale field `composedMulti`); `oldLF_eq_sum`: `ℬ''^{(k)}` is the sum of these over the old
  domains;
* `locDomsLF`: the localization domains `R_{k+1}(□′)` of the unit points (P5 (2.18), `locDomC`),
  `locSloc_eq`;
* `oldCoefLF`: **the coefficient `T(X, J)`** of P6 (4.32)–(4.33) (`HoleStep.oldCoef`), with the uncut
  core `X₁` = the sites within `r` of `X ∩ Ω_{k+1}` (`collarCoreC`; P6 p. 34 with the pair condition of
  P3 (2.14), the reading of `notes/phase1/PLAN-B.md`, OPEN-P6-X1-INSTANTIATION) and the localization
  domains `locDomsLF`;
* `sum_oldCoefLF_eq_of_analytic`: at the composed field of the measure the old term is `∑_J T(X, J)`
  when its interpolation is analytic on a polydisc of radius `> 1`;
* `oldCoefLF_eq_zero_of_core`: no cube inside the core carries a parameter;
* `oldCoefLF_eq_zero_of_far`: if the old term reads only the unit points of `Rd`, the families with a
  cube in no domain `R_{k+1}(□′)`, `□′ ∈ Rd`, have coefficient `0`.
-/

@[expose] public section

open MeasureTheory Balaban Balaban.LargeField Balaban.LargeField.Def7 Balaban.Multiscale
  Balaban.Localization Balaban.Fluctuation

namespace Balaban.RootFSpine

section History

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {N m₁ : ℕ}
  (g : Geo S n R M) (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) (hM1 : g.M1 = S.L ^ m₁)

/-- **One old boundary term `ℬ^{(k)}(X, 𝔸)`** as a function of the field on the unit points of the
top layer of `G'` (the blocks of `Ω_{k+1}`), at the multiscale field `composedMulti`, the fluctuation
field `ψ'`, the physical field and the external field `gx`. -/
noncomputable def oldTermLF {geo : Geo S n R M} {cs : OpConsts} {P : BudgetConsts} {k : ℕ}
    (rep : Rep S n R k0 K M N geo cs P k) (A : LabHist S n R k0 K) (X : Finset (Torus S.d (n k)))
    (hk : k + 1 ≤ K) {ϱ' : ℝ}
    (G' : GeneratingSet S.d S.L ((g.c * n (k + 1)) * S.L ^ m₁) (k + 1) ϱ')
    (ψ ψ' : MultiFieldC S n M K N) (hv : EuclideanSpace ℝ (Fin N)) (gx : GIdx S n M K N → ℂ)
    (comp : unitPts G' → Fin N → ℂ) : ℂ :=
  rep.B A X (composedMulti g hnn hM1 hk G' ψ comp) ψ' (hC hv) gx

/-- `ℬ''^{(k)}` is the sum of the old terms over the old domains. -/
theorem oldLF_eq_sum {geo : Geo S n R M} {cs : OpConsts} {P : BudgetConsts} {k : ℕ}
    (rep : Rep S n R k0 K M N geo cs P k) (A : LabHist S n R k0 K)
    (Xs : Finset (Finset (Torus S.d (n k)))) (hk : k + 1 ≤ K) {ϱ' : ℝ}
    (G' : GeneratingSet S.d S.L ((g.c * n (k + 1)) * S.L ^ m₁) (k + 1) ϱ')
    (ψ ψ' : MultiFieldC S n M K N) (hv : EuclideanSpace ℝ (Fin N)) (gx : GIdx S n M K N → ℂ)
    (comp : unitPts G' → Fin N → ℂ) :
    oldLF g hnn hM1 rep A Xs hk G' ψ ψ' hv gx comp =
      ∑ X ∈ Xs, oldTermLF g hnn hM1 rep A X hk G' ψ ψ' hv gx comp := rfl

variable {k : ℕ} {ϱ ϱ' : ℝ} (St : HoleStep S.d S.L (g.c * n (k + 1)) m₁ k N ϱ ϱ')

/-- **The localization domains `R_{k+1}(□′)` of the unit points** (P5 (2.18)): the sites of the cubes
of `𝕋_{k+1}` within `ρ` cubes of the cube of the unit point (`locDomC`). -/
noncomputable def locDomsLF (ρ : ℕ) : St.U → Finset (CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)) :=
  fun b => locDomC (c := g.c) (n1 := n (k + 1)) hM1 ρ (unitRep b)

omit [NeZero M] in
theorem locSloc_eq (Cv : DecCover S.d S.L (g.c * n (k + 1)) m₁ (k + 1)) (ρ : ℕ)
    (s : Dec2.DecParams Cv) : locSloc g hM1 St Cv ρ s = St.slocOf Cv (locDomsLF g hM1 St ρ) s :=
  rfl

/-- **The coefficient `T(X, J)` of the re-expansion of an old boundary term of a history** (P6 (4.32)–
(4.33), P3 (4.43)): `HoleStep.oldCoef` of the old term `oldTermLF` with the localization domains
`R_{k+1}(□′)` (`locDomsLF`, radius `ρ = ⌊R_k⌋`) and the uncut core, the sites within `r` of
`X ∩ Ω_{k+1}` (`collarCoreC`). -/
noncomputable def oldCoefLF (H : RegionHistory S n R k0 K) (hk : k + 1 ≤ K)
    (Cv : DecCover S.d S.L (g.c * n (k + 1)) m₁ (k + 1)) (ρc : ℝ) (ρ r : ℕ) (inner : Finset St.U)
    (ψout : St.U → Fin N → ℂ) {geo : Geo S n R M} {cs : OpConsts} {P : BudgetConsts}
    (rep : Rep S n R k0 K M N geo cs P k) (A : LabHist S n R k0 K) (X : Finset (Torus S.d (n k)))
    (ψ ψ' : MultiFieldC S n M K N) (hv : EuclideanSpace ℝ (Fin N)) (gx : GIdx S n M K N → ℂ)
    (J : Finset Cv.cubeIdx) (ψin : inner → Rn N) : ℂ :=
  St.oldCoef Cv ρc (locDomsLF g hM1 St ρ) (collarCoreC (c := g.c) (H.step k) hM1 r X) inner ψout
    (oldTermLF g hnn hM1 rep A X hk St.G' ψ ψ' hv gx) J ψin

/-- **An old term of a history is the sum of its coefficients** (P6 (4.33) before the resummation):
at the composed field of the measure (`locSloc` at `s = 1`), `ℬ^{(k)}(X) = ∑_J T(X, J)`, when the
interpolated old term is analytic on a polydisc of radius `R > 1`. -/
theorem sum_oldCoefLF_eq_of_analytic (H : RegionHistory S n R k0 K) (hk : k + 1 ≤ K)
    (Cv : DecCover S.d S.L (g.c * n (k + 1)) m₁ (k + 1)) (ρc : ℝ) (ρ r : ℕ) (inner : Finset St.U)
    (ψout : St.U → Fin N → ℂ) {geo : Geo S n R M} {cs : OpConsts} {P : BudgetConsts}
    (rep : Rep S n R k0 K M N geo cs P k) (A : LabHist S n R k0 K) (X : Finset (Torus S.d (n k)))
    (ψ ψ' : MultiFieldC S n M K N) (hv : EuclideanSpace ℝ (Fin N)) (gx : GIdx S n M K N → ℂ)
    (ψin : inner → Rn N) {Rp : ℝ} (hR : 1 < Rp)
    (hana : AnalyticOnNhd ℂ (St.oldInterp Cv ρc (locDomsLF g hM1 St ρ)
      (collarCoreC (c := g.c) (H.step k) hM1 r X) inner ψout
      (oldTermLF g hnn hM1 rep A X hk St.G' ψ ψ' hv gx) ψin)
      (Analysis.polydisc (0 : Dec2.DecParams Cv) fun _ => Rp)) :
    St.oldAt Cv ρc (locSloc g hM1 St Cv ρ 1) inner ψout
        (oldTermLF g hnn hM1 rep A X hk St.G' ψ ψ' hv gx) ψin =
      ∑ J : Finset Cv.cubeIdx,
        oldCoefLF g hnn hM1 St H hk Cv ρc ρ r inner ψout rep A X ψ ψ' hv gx J ψin :=
  St.sum_oldCoef_eq_of_analytic Cv ρc _ _ inner ψout _ ψin hR hana

/-- **No cube of the uncut core carries a parameter**: `T(X, J) = 0` when `J` contains a cover cube
inside the core. -/
theorem oldCoefLF_eq_zero_of_core (H : RegionHistory S n R k0 K) (hk : k + 1 ≤ K)
    (Cv : DecCover S.d S.L (g.c * n (k + 1)) m₁ (k + 1)) (ρc : ℝ) (ρ r : ℕ) (inner : Finset St.U)
    (ψout : St.U → Fin N → ℂ) {geo : Geo S n R M} {cs : OpConsts} {P : BudgetConsts}
    (rep : Rep S n R k0 K M N geo cs P k) (A : LabHist S n R k0 K) (X : Finset (Torus S.d (n k)))
    (ψ ψ' : MultiFieldC S n M K N) (hv : EuclideanSpace ℝ (Fin N)) (gx : GIdx S n M K N → ℂ)
    {J : Finset Cv.cubeIdx} {Q : Cv.cubeIdx} (hQJ : Q ∈ J)
    (hQ : cubeP (Q : ℕ × CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)) ⊆
      collarCoreC (c := g.c) (H.step k) hM1 r X) (ψin : inner → Rn N) :
    oldCoefLF g hnn hM1 St H hk Cv ρc ρ r inner ψout rep A X ψ ψ' hv gx J ψin = 0 :=
  St.oldCoef_eq_zero_of_core Cv ρc _ _ inner ψout _ hQJ hQ ψin

/-- **The parameters are read through the localization domains of the read unit points**: if the old
term reads only the unit points of `Rd`, then `T(X, J) = 0` when `J` contains a cover cube inside no
domain `R_{k+1}(□′)` of a point of `Rd`. -/
theorem oldCoefLF_eq_zero_of_far (H : RegionHistory S n R k0 K) (hk : k + 1 ≤ K)
    (Cv : DecCover S.d S.L (g.c * n (k + 1)) m₁ (k + 1)) (ρc : ℝ) (ρ r : ℕ) (inner : Finset St.U)
    (ψout : St.U → Fin N → ℂ) {geo : Geo S n R M} {cs : OpConsts} {P : BudgetConsts}
    (rep : Rep S n R k0 K M N geo cs P k) (A : LabHist S n R k0 K) (X : Finset (Torus S.d (n k)))
    (ψ ψ' : MultiFieldC S n M K N) (hv : EuclideanSpace ℝ (Fin N)) (gx : GIdx S n M K N → ℂ)
    {Rd : Set St.U}
    (hB : ∀ c c' : St.U → Fin N → ℂ, (∀ b ∈ Rd, c b = c' b) →
      oldTermLF g hnn hM1 rep A X hk St.G' ψ ψ' hv gx c =
        oldTermLF g hnn hM1 rep A X hk St.G' ψ ψ' hv gx c')
    {J : Finset Cv.cubeIdx} {Q : Cv.cubeIdx} (hQJ : Q ∈ J)
    (hfar : ∀ b ∈ Rd, ¬ cubeP (Q : ℕ × CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)) ⊆
      locDomsLF g hM1 St ρ b) (ψin : inner → Rn N) :
    oldCoefLF g hnn hM1 St H hk Cv ρc ρ r inner ψout rep A X ψ ψ' hv gx J ψin = 0 :=
  St.oldCoef_eq_zero_of_far Cv ρc _ _ inner ψout hB hQJ hfar ψin

end History

end Balaban.RootFSpine
