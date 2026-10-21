/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.LFHoleStep
public import Balaban.Spine.StepDensity
public import Balaban.LargeField.Def7SmallFieldC
public import Balaban.Fluctuation.HoleStepMeasure

/-!
# The exponent of the fluctuation integral of the large-field step (P5 (2.16), (2.38), (2.48))

The integrand of the step `T^{(k)}` (P5 (2.16), `stepDensity`) on a history is the kernel
`∏_y t_k(z ψ_{k+1}(y), (Qψ_k)(y))` times the small-field factor `χ_k(Z^c_k) exp(𝒜_k + ℱ_k + ℛ^{(k)})(Z^c_k)`
of (D1), the large-field operators of the history and `exp ℬ^{(k)}`.  In the fluctuation integral
the characteristic function `χ_k` is carried by the large-field operator `T'^{(k)}` and the measure
`dμ'(Ω''_{k+1}; ψ̂)` (P5 (2.44)–(2.47); it is not part of the exponent), and the exponent of
(2.48) is, up to a constant, the logarithm of the rest at the composed field (2.39) (P5 (2.38)).  This
file defines that logarithm, holomorphic in the field, and the objects of P5 (3.1)–(3.2) for the step
on a region of a history.

* `stepAvgWith`: the block average with values in any real vector space (`stepAvg` is the instance
  `ℝ^N`, `stepAvg_eq_with`; `stepAvgWith_blockToC`);
* `logKernelC`: the exponent `-(c/2) ∑_y (θ(y) - Qψ_k(y)) · (θ(y) - Qψ_k(y))` of the kernel of
  `T^{(k)}`, holomorphic; `stepKernel_eq_exp`: at real fields the kernel is
  `((c/2π)^{N/2})^{|T^{(k+1)}|} exp(logKernelC)`;
* `logIntegrandC`: the logarithm `logKernelC + 𝒜_k + ℱ_k + ℛ^{(k)}` of the integrand of (2.16) on `Y`
  without `χ_k` (`Def7.SFCtx.sfExpC`); `stepKernel_mul_sfFactor`: at real fields with real background,
  kernel times small-field factor is `((c/2π)^{N/2})^{|T^{(k+1)}|} χ_k(Y) exp(logIntegrandC)`;
* `phiLF`: the logarithm of the integrand as a function of the field on the unit points of
  `Ω_{k+1}` (through `composedMulti`), at `Y = Z^c_k` and `θ = z ψ_{k+1}`;
* `oldDoms`, `oldLF`: the old boundary domains meeting `Ω_{k+1}` and the old boundary terms
  `ℬ''^{(k)} = ∑_{X ∩ Ω_{k+1} ≠ ∅} ℬ^{(k)}(X)` (P5 p. 512) at the composed multiscale field;
* `locDomsLF`, `locSloc`: the localization domains of P5 (2.18) (`locDomC`, `ρ = ⌊R_k⌋`, in the deep
  part of `Ω₁(G′)`) and the localization vectors (`slocOf`);
* `expWLF`, `oldTotalLF`: the exponent of the measure of P5 (3.2) and
  `ℬ''^{(k+1)} = ∫₀¹ ⟨ℬ''^{(k)}⟩''_u du` (FLUCTUATION Theorem 3.1 (c)) for the step on a region of a
  history; `partFun_one_eq_mul_exp_oldTotalLF`: the fluctuation integral with the old terms is the
  one without them times `exp ℬ''^{(k+1)}`.
-/

@[expose] public section

open MeasureTheory Balaban Balaban.LargeField Balaban.LargeField.Def7 Balaban.Multiscale
  Balaban.Localization Balaban.Fluctuation

namespace Balaban.RootFSpine

/-! ### The kernel of `T^{(k)}` -/

section Kernel

variable {S : Setting} {n : ℕ → ℕ} [∀ j, NeZero (n j)] {M K : ℕ} [NeZero M] [NeZero S.L] {N : ℕ}

/-- The block average `(Qψ_k)(y) = L^{-d} ∑_{y' ⊂ y} ψ_k(y')` with values in any real vector
space (`stepAvg` is the instance `ℝ^N`). -/
noncomputable def stepAvgWith {E : Type*} [AddCommGroup E] [Module ℝ E] (k : ℕ)
    (ψ : BlockAt S n M K k → E) (y : BlockAt S n M K (k + 1)) : E :=
  ((S.L : ℝ) ^ S.d)⁻¹ • ∑ y' ∈ Finset.univ.filter (fun y' : BlockAt S n M K k =>
      blockMap S.L (M * n K * S.L ^ (K - (k + 1))) y' = y), ψ y'

theorem stepAvg_eq_with (k : ℕ) (ψ : BlockAt S n M K k → EuclideanSpace ℝ (Fin N)) :
    stepAvg k ψ = stepAvgWith k ψ := rfl

/-- The block average commutes with the complexification. -/
theorem stepAvgWith_blockToC (k : ℕ) (ψ : BlockAt S n M K k → EuclideanSpace ℝ (Fin N))
    (y : BlockAt S n M K (k + 1)) :
    stepAvgWith k (blockToC ψ) y = hC (stepAvg k ψ y) := by
  unfold stepAvgWith stepAvg blockToC
  rw [hC_smul_sum]

/-- **The exponent of the kernel of `T^{(k)}`**, holomorphic in the fields:
`-(c/2) ∑_{y ∈ T^{(k+1)}} (θ(y) - (Qψ_k)(y)) · (θ(y) - (Qψ_k)(y))` with the bilinear product. -/
noncomputable def logKernelC (k : ℕ) (c : ℝ) (θ : BlockAt S n M K (k + 1) → Fin N → ℂ)
    (ψ : BlockAt S n M K k → Fin N → ℂ) : ℂ :=
  ∑ y, -((c / 2 : ℝ) : ℂ) *
    SmallField.dot (θ y - stepAvgWith k ψ y) (θ y - stepAvgWith k ψ y)

/-- **The kernel of `T^{(k)}` at real fields** is `((c/2π)^{N/2})^{|T^{(k+1)}|} exp(logKernelC)` at
the block variable `z θ`. -/
theorem stepKernel_eq_exp (k : ℕ) (c z : ℝ) (θ : BlockAt S n M K (k + 1) → EuclideanSpace ℝ (Fin N))
    (ψ : BlockAt S n M K k → EuclideanSpace ℝ (Fin N)) :
    ((stepKernel k c z θ ψ : ℝ) : ℂ) =
      ((((c / (2 * Real.pi)) ^ ((N : ℝ) / 2)) ^ Fintype.card (BlockAt S n M K (k + 1)) : ℝ) : ℂ) *
        Complex.exp (logKernelC k c (blockToC fun y => z • θ y) (blockToC ψ)) := by
  have hl : logKernelC k c (blockToC fun y => z • θ y) (blockToC ψ) =
      ((∑ y, -(c / 2) * ‖z • θ y - stepAvg k ψ y‖ ^ 2 : ℝ) : ℂ) := by
    unfold logKernelC
    push_cast
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [stepAvgWith_blockToC]
    show _ * SmallField.dot (hC (z • θ y) - hC _) (hC (z • θ y) - hC _) = _
    rw [← hC_sub, dot_hC]
    push_cast
    ring
  rw [hl, ← Complex.ofReal_exp, ← Complex.ofReal_mul]
  congr 1
  unfold stepKernel gaussT
  rw [Real.exp_sum, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]

/-- **The logarithm of the integrand of P5 (2.16)** on `Y` at a complex field `ψ_k` on the
`k`-blocks, without the characteristic function `χ_k`: the exponent of the kernel at the block
variable `θ` plus the exponent `𝒜_k + ℱ_k + ℛ^{(k)}` of the small-field factor on `Y`. -/
noncomputable def logIntegrandC {R : ℕ → ℝ} {k m₁ : ℕ} {ϱ : ℝ} (C : SFCtx S n R M K N k m₁ ϱ)
    (Y : Set (Torus S.d (n k))) (c : ℝ) (θ : BlockAt S n M K (k + 1) → Fin N → ℂ)
    (hv : EuclideanSpace ℝ (Fin N)) (gx : GIdx S n M K N → ℂ)
    (ψ : BlockAt S n M K k → Fin N → ℂ) : ℂ :=
  logKernelC k c θ ψ + C.sfExpC Y ψ hv gx

/-- **The integrand of (2.16) at real fields** (kernel times small-field factor of (D1)) is
`((c/2π)^{N/2})^{|T^{(k+1)}|} χ_k(Y) exp(logIntegrandC)`, when the complex background is real. -/
theorem stepKernel_mul_sfFactor {R : ℕ → ℝ} {k m₁ : ℕ} {ϱ : ℝ} (C : SFCtx S n R M K N k m₁ ϱ)
    (Y : Set (Torus S.d (n k))) (c z : ℝ) (θ : BlockAt S n M K (k + 1) → EuclideanSpace ℝ (Fin N))
    (hv : EuclideanSpace ℝ (Fin N)) (gx : GIdx S n M K N → ℂ)
    (ψ : BlockAt S n M K k → EuclideanSpace ℝ (Fin N))
    (hre : ∀ x i, (C.phiBarC Y (blockToC ψ) hv x i).im = 0) :
    ((stepKernel k c z θ ψ : ℝ) : ℂ) * C.sfFactor Y ψ hv gx =
      ((((c / (2 * Real.pi)) ^ ((N : ℝ) / 2)) ^ Fintype.card (BlockAt S n M K (k + 1)) : ℝ) : ℂ) *
        ((C.chiY Y ψ hv : ℝ) : ℂ) *
          Complex.exp (logIntegrandC C Y c (blockToC fun y => z • θ y) hv gx (blockToC ψ)) := by
  rw [stepKernel_eq_exp, C.sfFactor_eq_mul_exp Y hv gx ψ hre]
  unfold logIntegrandC
  rw [Complex.exp_add]
  ring

end Kernel

/-! ### The step on a region of a history -/

section History

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {N m₁ : ℕ}
  (g : Geo S n R M) (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) (hM1 : g.M1 = S.L ^ m₁)

/-- **The logarithm of the integrand of (2.16) on the unit points of `Ω_{k+1}`** (P5 (2.38), (2.48)):
`logIntegrandC` on `Y` at the block variable `θ = z ψ_{k+1}` and at the field of scale `k` of the
multiscale field `composedMulti` (the field `comp` on the unit points of `G'`, `ψ_k` elsewhere). -/
noncomputable def phiLF {k : ℕ} (hk : k + 1 ≤ K) {ϱ' : ℝ}
    (G' : GeneratingSet S.d S.L ((g.c * n (k + 1)) * S.L ^ m₁) (k + 1) ϱ') {m₁' : ℕ} {ϱ : ℝ}
    (C : SFCtx S n R M K N k m₁' ϱ) (Y : Set (Torus S.d (n k))) (c z : ℝ)
    (ψ : MultiFieldC S n M K N) (hv : EuclideanSpace ℝ (Fin N)) (gx : GIdx S n M K N → ℂ)
    (comp : unitPts G' → Fin N → ℂ) : ℂ :=
  logIntegrandC C Y c (scaleMulti z ψ (k + 1)) hv gx (composedMulti g hnn hM1 hk G' ψ comp k)

open Classical in
/-- **The old boundary domains meeting `Ω_{k+1}`** (P5 p. 512): the boundary domains `X` of the
post-`R` class at scale `k` (`bdryDomsAt` at `Ω_k^post`, for `Z_k`) whose fine sets meet the fine
set of `Ω_{k+1}` (the old labels of `oldAssign`). -/
noncomputable def oldDoms {m₀ m₁'' : ℕ} (F : FineSizeFrame S n M K m₀ m₁'')
    (H : RegionHistory S n R k0 K) (k : ℕ) : Finset (Finset (Torus S.d (n k))) :=
  (bdryDomsAt F k (H.omegaPost k) (H.step k).Z).filter fun X =>
    (d7Pull F k (X : Set (Torus S.d (n k))) ∩ d7Pull F (k + 1) (OmegaCube H (k + 1))).Nonempty

/-- **The old boundary terms `ℬ''^{(k)}`** (P5 p. 512, (2.48)): the sum of the boundary terms
`ℬ^{(k)}(X, 𝔸)` of the representation over the domains `Xs` (the old domains meeting `Ω_{k+1}`,
`oldDoms`), at the multiscale field `composedMulti` (the field `comp` on the unit points of `G'`),
the fluctuation field `ψ'`, the physical field and the external field `gx`. -/
noncomputable def oldLF {geo : Geo S n R M} {cs : OpConsts} {P : BudgetConsts} {k : ℕ}
    (rep : Rep S n R k0 K M N geo cs P k) (A : LabHist S n R k0 K)
    (Xs : Finset (Finset (Torus S.d (n k)))) (hk : k + 1 ≤ K) {ϱ' : ℝ}
    (G' : GeneratingSet S.d S.L ((g.c * n (k + 1)) * S.L ^ m₁) (k + 1) ϱ')
    (ψ ψ' : MultiFieldC S n M K N) (hv : EuclideanSpace ℝ (Fin N)) (gx : GIdx S n M K N → ℂ)
    (comp : unitPts G' → Fin N → ℂ) : ℂ :=
  ∑ X ∈ Xs, rep.B A X (composedMulti g hnn hM1 hk G' ψ comp) ψ' (hC hv) gx

variable {k : ℕ} {ϱ ϱ' : ℝ}
  (St : HoleStep S.d S.L (g.c * n (k + 1)) m₁ k N ϱ ϱ')

open Classical in
/-- **The localization domains of P5 (2.18)** of the unit points (reading HS-1): the sites of the
cubes of `𝕋_{k+1}` within `ρ` cubes of the cube of the unit point (`locDomC`, `R_{k+1}(□′)`) whose
`4 L^{k+1+m₁}`-ball lies in `Ω₁(G′)` (P3 (2.14): `X₁ ⊂ Ω₁`, with the margin of the cross lemmas). -/
noncomputable def locDomsLF (ρ : ℕ) : St.U → Finset (CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)) :=
  fun b => (locDomC (c := g.c) (n1 := n (k + 1)) hM1 ρ (unitRep b)).filter fun y =>
    ∀ z : CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1),
      supDist y z ≤ 4 * S.L ^ (k + 1 + m₁) → z ∈ St.G'.Ω 1

/-- **The localization vectors of P5 (2.18)** of the step on a region of a history: at the unit
point `b`, the decoupling vector `s` vanishing on the cover cubes outside the localization domain
of `b` (`locDomsLF`). -/
noncomputable def locSloc (Cv : DecCover S.d S.L (g.c * n (k + 1)) m₁ (k + 1)) (ρ : ℕ)
    (s : Dec2.DecParams Cv) : St.U → Dec2.DecParams Cv :=
  St.slocOf Cv (locDomsLF g hM1 St ρ) s

/-- **The exponent of the measure of P5 (3.2)** for the step on a region of a history: `HoleStep.expW`
with the logarithm `phiLF` of the integrand on `Y` and the old boundary terms `oldLF`. -/
noncomputable def expWLF (hk : k + 1 ≤ K) (Cv : DecCover S.d S.L (g.c * n (k + 1)) m₁ (k + 1))
    (ρc : ℝ) (sloc : St.U → Dec2.DecParams Cv) (inner : Finset St.U) (ψout : St.U → Fin N → ℂ)
    {m₁' : ℕ} {ϱs : ℝ} (C : SFCtx S n R M K N k m₁' ϱs) (Y : Set (Torus S.d (n k))) (c z : ℝ)
    {geo : Geo S n R M} {cs : OpConsts} {P : BudgetConsts} (rep : Rep S n R k0 K M N geo cs P k)
    (A : LabHist S n R k0 K) (Xs : Finset (Finset (Torus S.d (n k))))
    (ψ ψ' : MultiFieldC S n M K N) (hv : EuclideanSpace ℝ (Fin N)) (gx : GIdx S n M K N → ℂ)
    (u : ℝ) (ψin : inner → Rn N) : ℂ :=
  St.expW Cv ρc sloc inner ψout (phiLF g hnn hM1 hk St.G' C Y c z ψ hv gx)
    (oldLF g hnn hM1 rep A Xs hk St.G' ψ ψ' hv gx) u ψin

/-- **`ℬ''^{(k+1)} = ∫₀¹ ⟨ℬ''^{(k)}⟩''_u du`** (P5 (3.2); FLUCTUATION Theorem 3.1 (c)) for the step on
a region of a history: `HoleStep.oldTotal` with `phiLF` and `oldLF`. -/
noncomputable def oldTotalLF (hk : k + 1 ≤ K) (Cv : DecCover S.d S.L (g.c * n (k + 1)) m₁ (k + 1))
    (ρc : ℝ) (sloc : St.U → Dec2.DecParams Cv) (inner : Finset St.U) (ψout : St.U → Fin N → ℂ)
    {m₁' : ℕ} {ϱs : ℝ} (C : SFCtx S n R M K N k m₁' ϱs) (Y : Set (Torus S.d (n k))) (c z : ℝ)
    {geo : Geo S n R M} {cs : OpConsts} {P : BudgetConsts} (rep : Rep S n R k0 K M N geo cs P k)
    (A : LabHist S n R k0 K) (Xs : Finset (Finset (Torus S.d (n k))))
    (ψ ψ' : MultiFieldC S n M K N) (hv : EuclideanSpace ℝ (Fin N)) (gx : GIdx S n M K N → ℂ) : ℂ :=
  St.oldTotal Cv ρc sloc inner ψout (phiLF g hnn hM1 hk St.G' C Y c z ψ hv gx)
    (oldLF g hnn hM1 rep A Xs hk St.G' ψ ψ' hv gx)

/-- **`ℬ''^{(k+1)}` is the difference of the logarithms of the fluctuation integrals** for the step
on a region of a history (P5 (3.1)): with the family of exponents of class `C¹` and nonvanishing
partition functions on `[0, 1]`. -/
theorem partFun_one_eq_mul_exp_oldTotalLF (hk : k + 1 ≤ K)
    (Cv : DecCover S.d S.L (g.c * n (k + 1)) m₁ (k + 1)) (ρc : ℝ) (sloc : St.U → Dec2.DecParams Cv)
    (inner : Finset St.U) (ψout : St.U → Fin N → ℂ) {m₁' : ℕ} {ϱs : ℝ}
    (C : SFCtx S n R M K N k m₁' ϱs) (Y : Set (Torus S.d (n k))) (c z : ℝ) {geo : Geo S n R M}
    {cs : OpConsts} {P : BudgetConsts} (rep : Rep S n R k0 K M N geo cs P k)
    (A : LabHist S n R k0 K) (Xs : Finset (Finset (Torus S.d (n k))))
    (ψ ψ' : MultiFieldC S n M K N) (hv : EuclideanSpace ℝ (Fin N)) (gx : GIdx S n M K N → ℂ)
    (hp : 0 < St.p₁) {U : Set ℝ}
    (hC1 : IsC1Family U (expWLF g hnn hM1 St hk Cv ρc sloc inner ψout C Y c z rep A Xs ψ ψ' hv gx)
      (fun _ => St.oldAt Cv ρc sloc inner ψout (oldLF g hnn hM1 rep A Xs hk St.G' ψ ψ' hv gx)))
    (hZ : ∀ u ∈ Set.Icc (0 : ℝ) 1, partFun (St.nuIn inner)
      (expWLF g hnn hM1 St hk Cv ρc sloc inner ψout C Y c z rep A Xs ψ ψ' hv gx) u ≠ 0) :
    partFun (St.nuIn inner)
        (expWLF g hnn hM1 St hk Cv ρc sloc inner ψout C Y c z rep A Xs ψ ψ' hv gx) 1 =
      partFun (St.nuIn inner)
          (expWLF g hnn hM1 St hk Cv ρc sloc inner ψout C Y c z rep A Xs ψ ψ' hv gx) 0 *
        Complex.exp (oldTotalLF g hnn hM1 St hk Cv ρc sloc inner ψout C Y c z rep A Xs ψ ψ' hv gx) :=
  St.partFun_one_eq_mul_exp_oldTotal Cv ρc sloc inner ψout _ _ hp hC1 hZ

end History

end Balaban.RootFSpine
