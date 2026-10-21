/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.LFOldMarkBound
public import Balaban.Fluctuation.HoleStepAnalytic

/-!
# The bound of the coefficient of an old boundary term on its local pair (P6 (4.33)–(4.34))

The coefficient `T(X, J)` of the re-expansion of an old boundary term on its local pair (reading
HS-1′, `oldCoefLoc`) satisfies the bound of P6 (4.34) at one coefficient,
`|T(X, J)| ≤ fac · e^{-rate · d^cov(X)} · e^{-(κ₁ - 1)|J|}`, with the constant and the rate of the
record's (D7):

* `analyticAt_truncK_composedMulti`: the composed multiscale field is affine in the composed field;
* `analyticAt_oldTermLF`: the old term at the composed multiscale field is analytic in the composed
  field where that field lies in the source H7 domain (the record's (D7) `analytic`);
* `norm_oldCoefLoc_le_of_inputs`: **the bound of the coefficient**, from the record's (D7), the
  standing conditions of the local pair (Theorems I-4b, I-4c; `holeStepLoc_coverBase`,
  `holeStepLoc_xCover`), the analyticity in the parameters (`HoleStep.analyticOnNhd_oldInterp`), the
  bound at every parameter (`norm_oldInterp_loc_lt`) and the Cauchy estimate of Lemma AE;
  conditional on the two named inputs of OPEN-H7-MIXED for the local pair (`H7MixedInnerLoc`,
  `H7MixedDatumLoc`).
-/

@[expose] public section

open MeasureTheory Balaban Balaban.LargeField Balaban.LargeField.Def7 Balaban.Multiscale
  Balaban.Localization Balaban.Fluctuation Balaban.LargeField.RegionHistory Balaban.Background

namespace Balaban.RootFSpine

section CoefBound

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {N m₁ : ℕ}
  (g : Geo S n R M) (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) (hM1 : g.M1 = S.L ^ m₁)

/-- **The composed multiscale field is affine in the composed field**: its truncation is analytic. -/
theorem analyticAt_truncK_composedMulti {k : ℕ} (hk : k + 1 ≤ K) {ϱ' : ℝ}
    (G' : GeneratingSet S.d S.L ((g.c * n (k + 1)) * S.L ^ m₁) (k + 1) ϱ')
    (ψ : MultiFieldC S n M K N) (comp₀ : unitPts G' → Fin N → ℂ) :
    AnalyticAt ℂ (fun comp : unitPts G' → Fin N → ℂ =>
      truncK (composedMulti g hnn hM1 hk G' ψ comp)) comp₀ := by
  classical
  refine analyticAt_pi_iff.2 fun j => analyticAt_pi_iff.2 fun y => analyticAt_pi_iff.2 fun i => ?_
  simp only [truncK, composedMulti]
  split_ifs with h1 h2 h3
  · exact analyticAt_const
  · exact ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N => ℂ) i).comp
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : unitPts G' => Fin N → ℂ) _)).analyticAt _
  · exact analyticAt_const
  · exact analyticAt_const

/-- **The old term is analytic in the composed field** where the composed multiscale field lies in
the source H7 domain (the record's (D7) `analytic`). -/
theorem analyticAt_oldTermLF {m₀ : ℕ} {Fr : FineSizeFrame S n M K m₀ m₁} {k : ℕ} (hk : k + 1 ≤ K)
    {geo : Geo S n R M} {cs : OpConsts} {P : BudgetConsts} {rep : Rep S n R k0 K M N geo cs P k}
    {Zof : LabHist S n R k0 K → Set (Torus S.d (n k))} {aw μs ε ε1 νs : ℕ → ℝ} {fac rate : ℝ}
    {hv : EuclideanSpace ℝ (Fin N)}
    (hrec : D7BdryPost Fr hnn (Nat.le_of_succ_le hk) rep Zof aw μs ε ε1 νs fac rate hv)
    (hgeo : geo = g) {A : LabHist S n R k0 K} (hA : A ∈ rep.hist) {X : Finset (Torus S.d (n k))}
    (hX : X ∈ bdryDomsPost Fr A k (Zof A)) {ϱ' : ℝ}
    (G' : GeneratingSet S.d S.L ((g.c * n (k + 1)) * S.L ^ m₁) (k + 1) ϱ')
    (ψ : MultiFieldC S n M K N) (q' : FinFieldC S n M K N) (gx : GIdx S n M K N → ℂ)
    (comp₀ : unitPts G' → Fin N → ℂ)
    (hdom : H7Domain g.M1 g.c g.hM hnn (globalLH A.H M) k (Nat.le_of_succ_le hk)
      (fineSet (S := S) (n := n) M K k (X : Set (Torus S.d (n k)))) aw μs ε ε1 νs (hC hv)
      (composedMulti g hnn hM1 hk G' ψ comp₀) (extK q') (fun x i => gx (x, i))) :
    AnalyticAt ℂ (oldTermLF g hnn hM1 rep A X hk G' ψ (extK q') hv gx) comp₀ := by
  subst hgeo
  have hA' := hrec.analytic A hA X hX (hC hv) rfl
    (truncK (composedMulti geo hnn hM1 hk G' ψ comp₀), q', gx)
    (by
      simp only [Set.mem_ofPred_eq]
      rw [extK_truncK_composedMulti]
      exact hdom)
  have hin : AnalyticAt ℂ (fun comp : unitPts G' → Fin N → ℂ =>
      (truncK (composedMulti geo hnn hM1 hk G' ψ comp), q', gx)) comp₀ :=
    (analyticAt_truncK_composedMulti geo hnn hM1 hk G' ψ comp₀).prod analyticAt_const
  refine (hA'.comp_of_eq hin rfl).congr (Filter.Eventually.of_forall fun comp => ?_)
  simp only [Function.comp_apply, oldTermLF, extK_truncK_composedMulti]

/-- **The bound of the coefficient of an old boundary term on its local pair** (P6 (4.33)–(4.34) at
one coefficient; reading HS-1′): for an old label `X` of the record (with (D7) `hrec`), a family `J`
of cover cubes, a target field of the H7 domain of scale `k + 1` at a set `Y_f` containing `X` and the
data sites of the local pair, and a fluctuation field `|ψ̂| < r_ψ`,
`|T(X, J)| ≤ fac · e^{-rate · d^cov(X)} · e^{-(κ₁ - 1)|J_V|}`, `J_V` the cubes of the local cover with
the labels of `J`; from the standing conditions of Theorems I-4b and I-4c for the local pair and the
two named inputs of OPEN-H7-MIXED for the local pair. -/
theorem norm_oldCoefLoc_le_of_inputs {m₀ : ℕ} {Fr : FineSizeFrame S n M K m₀ m₁} {k : ℕ}
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
    {ψhat : (holeStepLF g hnn hM1 A.H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).U → Fin N → ℂ}
    (hψhat : ∀ b, vn (ψhat b) < rψ) :
    ‖oldCoefLoc g hnn hM1 A.H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ (rho4 S.d S.L N BG κ) ρ r r' rep A X
        (extK q') hv gx J ψhat‖ ≤
      fac * Real.exp (-rate * d7Size Fr A k X) *
        Real.exp (-(κ₁ - 1) * (locCubes g (coverOf (holeStepLoc g hnn hM1 A.H hk hk1 hρ ψ z h₀ a₁ ν
          β p₁ δ (locSetXJ g hM1 A.H r r' X J)).G') J).card) := by
  have hc := g.hc
  have hL : 2 ≤ S.L := by have := HB.hL; omega
  have Sb := holeStepLoc_coverBase g hnn hM1 A.H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ
    (locSetXJ g hM1 A.H r r' X J) hm₁ hN hM HB.hd HB.hL HB.mass HB.massLe HB.weights hag
  have SX := holeStepLoc_xCover g hnn hM1 A.H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ
    (locSetXJ g hM1 A.H r r' X J) hm₁ hN hM HB.hd HB.hL HB.mass HB.massLe HB.weights hag ha₁ ha₂
  have hD := hDat (locSetXJ g hM1 A.H r r' X J) Yf ψ (extK q') (fun x i => gx (x, i)) htgt hV
  have hνε : ν * ((S.L : ℝ) ^ (k + 1)) ^ 2 * δb ^ 2 ≤ δb ^ 2 :=
    mul_le_of_le_one_left (sq_nonneg _) HB.massLe
  have hfill : ∀ ψo : (holeStepLoc g hnn hM1 A.H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ
      (locSetXJ g hM1 A.H r r' X J)).U → Fin N → ℂ,
      (holeStepLoc g hnn hM1 A.H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ (locSetXJ g hM1 A.H r r' X J)).fill ∅
        (fun b => absurd b.2 (Finset.notMem_empty _)) ψo = ψo := fun ψo => by
    funext b i
    simp [HoleStep.fill]
  have hψloc : ∀ b : (holeStepLoc g hnn hM1 A.H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ
      (locSetXJ g hM1 A.H r r' X J)).U, vn (restrictU _ _ _ _ _ _ _ ψhat b) < rψ :=
    fun b => hψhat _
  refine norm_oldCoefLoc_le g hnn hM1 A.H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ (rho4 S.d S.L N BG κ) ρ r r'
    rep A X (extK q') hv gx J ψhat hκ₁ ?_ ?_
  · refine (holeStepLoc g hnn hM1 A.H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ
      (locSetXJ g hM1 A.H r r' X J)).analyticOnNhd_oldInterp hS Sb SX (Cchi_nonneg S.d S.L) HB hκ
      hMc hMX hδ0 hε hδ hνε hphi hmarD hαD hsm hD hκ₁κ _ _ _ _ _ _ fun s hs => ?_
    erw [hfill]
    exact analyticAt_oldTermLF g hnn hM1 hk hrec rfl hA hX _ ψ q' gx _
      (h7Domain_composedMulti_loc g hnn hM1 A.H hk hk1 hρ z h₀ a₁ ν β p₁ δ (rho4 S.d S.L N BG κ) ρ r
        aw μs ε ε1 νs (hC hv) hL hIn (locSetXJ g hM1 A.H r r' X J) X htgt hXY hV hψloc
        (fun P => by simpa using hs P))
  · intro s hs
    exact (norm_oldInterp_loc_lt g hnn hM1 hk hrec rfl hA hX hk1 hρ z h₀ a₁ ν β p₁ δ
      (rho4 S.d S.L N BG κ) ρ r hL hIn (locSetXJ g hM1 A.H r r' X J) htgt hXY hV hψloc
      (fun P => by simpa using hs P)).le

end CoefBound

end Balaban.RootFSpine
