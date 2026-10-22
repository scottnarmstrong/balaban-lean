/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.LFOldStepClauses

/-!
# The clause `bound` of (D7) for the old part in the form of the step

`oldStepB_hC`: at the physical field `h = hC hv` the old part in the form of the step is the old part
`oldB2` of reading HS-2 with the datum's external field `Re h` and the physical field `hv`.

`oldStepB_bound` (clause `bound` of (D7), P6 (4.34), LFR Lemma IV.1.5 (iii)): from `norm_oldB2Pre_le`
(the named input `H7MixedInnerLoc2Pre`, ladder item 4; `H7MixedDatumLoc2Pre`, proved by
`h7MixedDatumLoc2Pre_holds`; the resummation `OldResumSiteAt stencilX`, proved by
`oldResumSite2_holds`), the record's (D7) and the constants of the interaction family (`hBo`: the
constant of `norm_oldB2Pre_le` is below `Bo`).
-/

@[expose] public section

open MeasureTheory Balaban Balaban.LargeField Balaban.LargeField.Def7 Balaban.Multiscale
  Balaban.Localization Balaban.Fluctuation Balaban.LargeField.RegionHistory Balaban.Background
  Balaban.Polymer

namespace Balaban.RootFSpine

section StepBound

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {N m₁ : ℕ}
  (g : Geo S n R M) (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) (hM1 : g.M1 = S.L ^ m₁)

/-- **The old part in the form of the step at the physical field** is the old part `oldB2` of reading
HS-2 with the datum's external field `Re (hC hv)` and the physical field `hv`. -/
theorem oldStepB_hC {m₀ : ℕ} (F : FineSizeFrame S n M K m₀ m₁) {k : ℕ} (hk : k + 1 ≤ K)
    (hk1 : 1 ≤ k) (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (z a₁ ν β p₁ δ : ℝ)
    (inner : ∀ A : LabHist S n R k0 K, Finset (unitPts (stepG' g hnn hM1 A.H hk hρ)))
    (cb : ∀ A : LabHist S n R k0 K, inner A →
      CubeB (d := S.d) (L := S.L) (N₁ := F.N₁) (m₁ := m₁) (K := K) m₀ (k + 1)
        (d7Pull F (k + 1) (OmegaCube A.H (k + 1))))
    (hp : 0 < p₁)
    (IF : ∀ A : LabHist S n R k0 K,
      LocIntFam (fun b => {u : inner A // cb A u = b} → Rn N) (OldPrm S n M K N))
    (ψout : ∀ A : LabHist S n R k0 K, MultiFieldC S n M K N → (Fin N → ℂ) →
      unitPts (stepG' g hnn hM1 A.H hk hρ) → Fin N → ℂ)
    (rψ ρc : ℝ) (ρ r r' : ℕ) {geo : Geo S n R M} {cs : OpConsts} {P : BudgetConsts}
    (rep : Rep S n R k0 K M N geo cs P k) (hv : EuclideanSpace ℝ (Fin N)) (A : LabHist S n R k0 K)
    (Y : Finset (Torus S.d (n (k + 1)))) (ψ ψ' : MultiFieldC S n M K N) (gx : GIdx S n M K N → ℂ) :
    oldStepB g hnn hM1 F hk hk1 hρ z a₁ ν β p₁ δ inner cb hp IF ψout rψ ρc ρ r r' rep A Y ψ ψ' (hC hv)
        gx =
      oldB2 g hnn hM1 F hk hk1 hρ z (reExt (hC hv)) a₁ ν β p₁ δ (fun A _ => inner A)
        (fun A _ => cb A) hp (fun A ψ ψ' gx => (IF A).at (ψ, ψ', hC hv, gx))
        (fun A ψ => ψout A ψ (hC hv)) rψ ρc ρ r r' rep hv A Y ψ ψ' (hC hv) gx := by
  simp only [oldStepB, oldB2, oldBOf, oldBOfAt, reExtE_hC]

/-- **The clause `bound` of (D7) for the old part in the form of the step** (P6 (4.34); LFR Lemma
IV.1.5 (iii); `norm_oldB2Pre_le`): for a record of scale `k + 1` whose boundary terms are `oldStepB …`
re-expanding the terms of `rep` (its histories histories of `rep`, `hhist`), at a field of the H7 domain
of the pre-`R` records (ruling R17) at the physical field, the old part is below
`Bo e^{-rate' d^pre_{k+1}(Y)}`, given the record's (D7) at the regions `Z_k` of the step, the constants of
the background and decoupling theory, the named input `H7MixedInnerLoc2Pre` (ladder item 4) and
`H7MixedDatumLoc2Pre` (proved, `h7MixedDatumLoc2Pre_holds`) at the datum's field `Re (hC hv)`, the
resummation `OldResumSiteAt stencilX` (proved, `oldResumSite2_holds`), and the constants of the
interaction family (`hκV`, `hκ'`; `hBo`: the constant of `norm_oldB2Pre_le` below `Bo`). -/
theorem oldStepB_bound {m₀ : ℕ} (F : FineSizeFrame S n M K m₀ m₁) {k : ℕ} (hk : k + 1 ≤ K)
    (hk1 : 1 ≤ k) (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (z a₁ ν β p₁ δ : ℝ)
    (inner : ∀ A : LabHist S n R k0 K, Finset (unitPts (stepG' g hnn hM1 A.H hk hρ)))
    (cb : ∀ A : LabHist S n R k0 K, inner A →
      CubeB (d := S.d) (L := S.L) (N₁ := F.N₁) (m₁ := m₁) (K := K) m₀ (k + 1)
        (d7Pull F (k + 1) (OmegaCube A.H (k + 1))))
    (hcb : ∀ (A : LabHist S n R k0 K) (u : inner A), toFrame g hnn hM1 F hk (unitRep
      (u : unitPts (stepG' g hnn hM1 A.H hk hρ))) ∈
        Localization.box (cb A u).1 (cellSide S.L m₀ m₁ (k + 1)))
    (hp : 0 < p₁)
    (IF : ∀ A : LabHist S n R k0 K,
      LocIntFam (fun b => {u : inner A // cb A u = b} → Rn N) (OldPrm S n M K N))
    (ψout : ∀ A : LabHist S n R k0 K, MultiFieldC S n M K N → (Fin N → ℂ) →
      unitPts (stepG' g hnn hM1 A.H hk hρ) → Fin N → ℂ)
    (rψ : ℝ) (ρ r r' : ℕ) {cs : OpConsts} {P : BudgetConsts}
    (rep : Rep S n R k0 K M N g cs P k) {aw μs ε ε1 νs : ℕ → ℝ} {fac rate : ℝ}
    {hv : EuclideanSpace ℝ (Fin N)}
    (hrec : D7BdryPost F hnn (Nat.le_of_succ_le hk) rep (fun A => (A.H.step k).Z) aw μs ε ε1 νs fac
      rate hv)
    {cs' : OpConsts} {P' : BudgetConsts} (rep' : Rep S n R k0 K M N g cs' P' (k + 1))
    (hhist : ∀ A ∈ rep'.hist, A ∈ rep.hist)
    {c BG δb δc κ κ₁ : ℝ}
    (hB : rep'.B = oldStepB g hnn hM1 F hk hk1 hρ z a₁ ν β p₁ δ inner cb hp IF ψout rψ
      (rho4 S.d S.L N BG κ) ρ r r' rep)
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
    (hsm : δc ^ 2 * smallConstX S.d S.L κ ≤ 1 / 4) (hκ₁ : 1 ≤ κ₁) (hκ₁κ : κ₁ ≤ κ)
    (hIn : ∀ A ∈ rep'.hist, H7MixedInnerLoc2Pre g hnn hM1 A.H hk hk1 hρ z (reExt (hC hv)) a₁ ν β p₁ δ
      (rho4 S.d S.L N BG κ) ρ r r' aw μs ε ε1 νs (hC hv) (Real.exp κ₁) rψ)
    (hDat : ∀ A ∈ rep'.hist, H7MixedDatumLoc2Pre g hnn hM1 A.H hk hk1 hρ z (reExt (hC hv)) a₁ ν β p₁
      δ ρ r r' aw μs ε ε1 νs ν δb)
    (hrψ : 0 < rψ) (hfac : 0 < fac) {κX κV Cres rate' Bo : ℝ}
    (hres : ∀ A ∈ rep'.hist, OldResumSiteAt g hnn hM1 F A.H hk hρ ρ r r' stencilX κ₁ κX κV Cres)
    (hCres : 0 < Cres) (hκV : ∀ A, (IF A).κH ≤ κV) (hαX : aEnt S.d S.L + 1 ≤ rate - κX)
    (hκ' : ∀ A, rate' + Real.log 2 * c1 S.d S.L + 2 ≤ (IF A).κ')
    (hBo : ∀ A ∈ rep'.hist, Real.exp (Real.log 2 * c1 S.d S.L) *
        (CPE S.d S.L ((IF A).Kc + 1) (IF A).κH (IF A).κ0 (IF A).κ' * (fac * Cres)) *
        ((S.L : ℝ) ^ S.d * c1 S.d S.L * K0 S.d S.L (rate - κX)) *
        (c1 S.d S.L * K0 S.d S.L (IF A).κ0) < Bo)
    (Zof : LabHist S n R k0 K → Set (Torus S.d (n (k + 1)))) :
    D7Clause.bound.Holds F hnn hk rep' Zof aw μs ε ε1 νs Bo rate' hv := by
  intro A hA Y _ h hh p htgt
  obtain rfl : h = hC hv := hh
  rw [hB, oldStepB_hC]
  refine (norm_oldB2Pre_le g hnn hM1 hk hrec (hhist A hA) hk1 hρ z (reExt (hC hv)) a₁ ν β p₁ δ hS HB
    hm₁ hN hM hag ha₁ ha₂ hκ hMc hMX hδ0 hε hδ hphi hmarD hαD hsm hκ₁ hκ₁κ ρ r r' (hIn A hA)
    (hDat A hA) (reExt_hC hv) (fun X hX => mem_bdryDomsPost_of_mem_oldDoms hX) Y p htgt
    (fun A _ => inner A) (fun A _ => cb A) (hcb A) hp
    (fun A ψ ψ' gx => (IF A).at (ψ, ψ', hC hv, gx)) (fun A ψ => ψout A ψ (hC hv)) hrψ hfac (hres A hA)
    hCres (hκV A) hαX (hκ' A)).trans_lt ?_
  exact mul_lt_mul_of_pos_right (hBo A hA) (Real.exp_pos _)

/-- The finite-dimensional space of the arguments `(ψ, ψ', g)` of the clauses `analytic`, `bound` of
(D7) (fields at the scales `≤ K`). -/
abbrev D7Arg (S : Setting) (n : ℕ → ℕ) [∀ k, NeZero (n k)] (M K N : ℕ) [NeZero M] [NeZero S.L] :
    Type :=
  FinFieldC S n M K N × FinFieldC S n M K N × (GIdx S n M K N → ℂ)

open Classical in
/-- **The clause `analytic` of (D7) for the old part in the form of the step** (`oldBAtAt_analyticOnNhd`):
for a record of scale `k + 1` whose boundary terms are `oldStepB …`, if at every history and label there
are an open set `Pset` of arguments containing the H7 domain of the pre-`R` records at the physical
field, an open set `𝒰 ⊇ [0, 1]` of interpolation parameters and a compact measurable set `Q` of cube
variables carrying the cube measure, on which the activities of the interaction family are analytic in
`(argument, u)` and continuous in the cube variables, and the marks of the old labels are measurable,
analytic in the argument, continuous on `Q` and bounded (`hdat`; P6 (4.32)–(4.34), the analyticity of
the coefficients `oldCoefLoc2_analytic_family_LF` on the domain of the local pairs), then the old part is
analytic on the H7 domain. -/
theorem oldStepB_analytic {m₀ : ℕ} (F : FineSizeFrame S n M K m₀ m₁) {k : ℕ} (hk : k + 1 ≤ K)
    (hk1 : 1 ≤ k) (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (z a₁ ν β p₁ δ : ℝ)
    (inner : ∀ A : LabHist S n R k0 K, Finset (unitPts (stepG' g hnn hM1 A.H hk hρ)))
    (cb : ∀ A : LabHist S n R k0 K, inner A →
      CubeB (d := S.d) (L := S.L) (N₁ := F.N₁) (m₁ := m₁) (K := K) m₀ (k + 1)
        (d7Pull F (k + 1) (OmegaCube A.H (k + 1))))
    (hcb : ∀ (A : LabHist S n R k0 K) (u : inner A), toFrame g hnn hM1 F hk (unitRep
      (u : unitPts (stepG' g hnn hM1 A.H hk hρ))) ∈
        Localization.box (cb A u).1 (cellSide S.L m₀ m₁ (k + 1)))
    (hp : 0 < p₁)
    (IF : ∀ A : LabHist S n R k0 K,
      LocIntFam (fun b => {u : inner A // cb A u = b} → Rn N) (OldPrm S n M K N))
    (ψout : ∀ A : LabHist S n R k0 K, MultiFieldC S n M K N → (Fin N → ℂ) →
      unitPts (stepG' g hnn hM1 A.H hk hρ) → Fin N → ℂ)
    (rψ ρc : ℝ) (ρ r r' : ℕ) {geo : Geo S n R M} {cs : OpConsts} {P : BudgetConsts}
    (rep : Rep S n R k0 K M N geo cs P k)
    {cs' : OpConsts} {P' : BudgetConsts} (rep' : Rep S n R k0 K M N g cs' P' (k + 1))
    (hB : rep'.B = oldStepB g hnn hM1 F hk hk1 hρ z a₁ ν β p₁ δ inner cb hp IF ψout rψ ρc ρ r r' rep)
    (Zof : LabHist S n R k0 K → Set (Torus S.d (n (k + 1)))) (aw μs ε ε1 νs : ℕ → ℝ) (fac rate : ℝ)
    (hv : EuclideanSpace ℝ (Fin N))
    (hdat : ∀ A ∈ rep'.hist, ∀ Y ∈ bdryDomsPre F A (k + 1) (Zof A),
      ∃ (Pset : Set (D7Arg S n M K N)) (𝒰 : Set ℂ)
        (Q : Set (∀ b, {u : inner A // cb A u = b} → Rn N)),
        IsOpen Pset ∧
        {p : D7Arg S n M K N | H7Domain g.M1 g.c g.hM hnn (globalLHPre A.H M (k + 1)) (k + 1) hk
          (fineSet (S := S) (n := n) M K (k + 1) (Y : Set (Torus S.d (n (k + 1))))) aw μs ε ε1 νs
          (hC hv) (extK p.1) (extK p.2.1) (fun x i => p.2.2 (x, i))} ⊆ Pset ∧
        IsOpen 𝒰 ∧ (∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → (s : ℂ) ∈ 𝒰) ∧ IsCompact Q ∧
        MeasurableSet Q ∧
        (∀ᵐ Φ ∂(Measure.pi ((holeStepLF g hnn hM1 A.H hk hk1 hρ 0 z (reExt (hC hv)) a₁ ν β p₁
          δ).cubeMeasure (inner A) (cb A))), Φ ∈ Q) ∧
        (∀ y, ∀ Φ ∈ Q, AnalyticOnNhd ℂ (fun q : D7Arg S n M K N × ℂ =>
          ((IF A).A (extK q.1.1, extK q.1.2.1, hC hv, q.1.2.2) q.2).H y Φ) (Pset ×ˢ 𝒰)) ∧
        (∀ y, ∀ e ∈ Pset, ∀ w ∈ 𝒰,
          ContinuousOn (((IF A).A (extK e.1, extK e.2.1, hC hv, e.2.2) w).H y) Q) ∧
        ∀ X ∈ oldDoms F A.H k, ∀ V ∈ sitesXAt (σ := stencilX) g hnn hM1 F A.H hk hρ ρ r r' X,
          (∀ e ∈ Pset, Measurable (oldMarkSiteAt (glob := true) (σ := stencilX) g hnn hM1 F A.H hk hk1
            hρ (extK e.1) z (reExt (hC hv)) a₁ ν β p₁ δ (inner A) (cb A) (ψout A (extK e.1) (hC hv))
            rψ ρc ρ r r' rep A X (extK e.2.1) (reExtE (hC hv)) e.2.2 V)) ∧
          (∀ Φ ∈ Q, AnalyticOnNhd ℂ (fun e : D7Arg S n M K N => oldMarkSiteAt (glob := true)
            (σ := stencilX) g hnn hM1 F A.H hk hk1 hρ (extK e.1) z (reExt (hC hv)) a₁ ν β p₁ δ
            (inner A) (cb A) (ψout A (extK e.1) (hC hv)) rψ ρc ρ r r' rep A X (extK e.2.1)
            (reExtE (hC hv)) e.2.2 V Φ) Pset) ∧
          (∀ e ∈ Pset, ContinuousOn (oldMarkSiteAt (glob := true) (σ := stencilX) g hnn hM1 F A.H hk
            hk1 hρ (extK e.1) z (reExt (hC hv)) a₁ ν β p₁ δ (inner A) (cb A)
            (ψout A (extK e.1) (hC hv)) rψ ρc ρ r r' rep A X (extK e.2.1) (reExtE (hC hv)) e.2.2 V) Q) ∧
          ∃ Bm > 0, ∀ e ∈ Pset, ∀ Φ, ‖oldMarkSiteAt (glob := true) (σ := stencilX) g hnn hM1 F A.H
            hk hk1 hρ (extK e.1) z (reExt (hC hv)) a₁ ν β p₁ δ (inner A) (cb A)
            (ψout A (extK e.1) (hC hv)) rψ ρc ρ r r' rep A X (extK e.2.1) (reExtE (hC hv)) e.2.2 V Φ‖ ≤
            Bm) :
    D7Clause.analytic.Holds F hnn hk rep' Zof aw μs ε ε1 νs fac rate hv := by
  intro A hA Y hY h hh
  obtain rfl : h = hC hv := hh
  rw [hB]
  obtain ⟨Pset, 𝒰, Q, hP, hsub, h𝒰, hseg, hQ, hQm, hμQ, hAhol, hAcont, hmark⟩ := hdat A hA Y hY
  exact (oldBAtAt_analyticOnNhd g hnn hM1 true F A.H stencilX hk hk1 hρ 0 z (reExt (hC hv)) a₁ ν β
    p₁ δ (inner A) (cb A) (hcb A) hp (IF A) (fun e : D7Arg S n M K N =>
      ((extK e.1, extK e.2.1, hC hv, e.2.2) : OldPrm S n M K N))
    (fun e => extK e.1) (fun e => extK e.2.1) (fun e => e.2.2)
    (fun e => ψout A (extK e.1) (hC hv)) rψ ρc ρ r r' rep A (oldDoms F A.H k) (reExtE (hC hv)) Y hP
    h𝒰 hseg hQ hQm hμQ hAhol hAcont hmark).mono hsub

end StepBound

end Balaban.RootFSpine
