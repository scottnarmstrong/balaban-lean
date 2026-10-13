/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.History.PostWeightSupport
public import Balaban.LargeField.History.LocalOutputTransport
public import Balaban.LargeField.History.ParentR2Y
public import Balaban.LargeField.History.EarlyMassRatio

/-!
# The parent domain under the integral of (D1) (`D1ParentDomain`)

`notes/phase1/Q13-ACTIVE.md`.  For a history `A` of a representation at scale `k = j + 1`, a block
field `ψ_k` and internal variables `x` with nonvanishing weighted integrand
`W_A(ψ_k, g, x) ≠ 0` (`PostWeightSupport`), the datum of the small-field solver near
`Y = Z_k(A)ᶜ` lies in the quantitative real domain `Ψ̃(G_k; ν, η)`, with
`η = max (3 d L δ_j) (4 (d+1) δ_k)` and `ν` the physical solver mass `sfBgMassAt L k ν_k`.

## How the hypotheses are discharged

* The activity factor over each retained component `C` (`hActLoc`) is `ChiDomAt` at the
  configuration `outOf ψ_k` and the component `x_C` of the integration variable, by
  `chiDomAt_of_postWeighted_ne_zero`.  The retained components of the region history `A.H` at
  scale `k` (`C.1 ∉ A.H.rem k`) are exactly the elements of `PostComp A k` (the same subtype), so
  the product of D1 runs over the components used by `ParentDomain`.
* `χ_Y ≠ 0` comes from `W_A ≠ 0` (`chiY_ne_zero_of_postWeighted_ne_zero`); the clauses over `Y`
  follow from it and the cube `BgHyp` (`ParentR2Y`).
* `hmass` holds in the early regime (`EarlyMassRatio`).

## Scope

The theorem is for the scales `k ≤ k₀` (`hk`).  Above `k₀` a directional condition on the retained
sites is missing (`Q13-YDOMAIN.md` §2).  The transfer to composed inherited fields
(`CanonicalPrecedes`, `RegionalLocalPairAgreement`), the reference margins and the strict tube are
not treated.  The history `A` need not belong to `rep.hist`; the statement holds for every
`LabHist`.  The context `Cx` is the one of the representation (`Cx.geo = geo`, `Cx.cs = cs`, as for
`RepFam.ctx`).
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background RegionHistory Balaban.LargeField.Def7
  Balaban.SmallField.Def6v2

section Core

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ} {M : ℕ} [NeZero M]
  [NeZero S.L] {N m₁ j : ℕ} {ϱ : ℝ} (H : RegionHistory S n R k0 K)
  (Cx : SFCtx S n R M K N (j + 1) m₁ ϱ)

/-- **`inPsiTilde_genW_of_chiY` with the local active factor.** -/
theorem inPsiTilde_genW_of_chiY_local (ψk : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N))
    (hv : EuclideanSpace ℝ (Fin N)) (ν : ℝ) (hν : 0 ≤ ν) (hunit : ‖hv‖ = 1)
    (hδ : 0 < Cx.cs.delta (j + 1)) (hδ1 : (S.d + 1) * Cx.cs.delta (j + 1) ≤ 1)
    (hχ : Cx.chiY ((H.step (j + 1)).Z)ᶜ ψk hv ≠ 0)
    (HB : BgHyp S.d S.L (j + 1) (minSep S.L Cx.geo.M1) Cx.weights (Cx.cs.mu (j + 1)))
    (hmass : 2 * ν * ((S.L : ℝ) ^ (j + 1)) ^ 2 <
      (max (3 * S.d * S.L * Cx.cs.delta j) (4 * (S.d + 1) * Cx.cs.delta (j + 1))) ^ 2)
    (hActLoc : ∀ C : H.Comp (j + 1), C.1 ∉ H.rem (j + 1) →
      (∃ t ∈ dataSites (Cx.genW ((H.step (j + 1)).Z)ᶜ), parentSiteCube Cx t ∈ C.1) →
      ∃ (A : Set (InternalVars (H.localHistory M K (j + 1) C) (j + 1)))
        (x : SubCfg N (H.localHistory M K (j + 1) C) (j + 1) A),
        ChiDomAt Cx.geo Cx.cs H (j + 1) C
          (outOf R (H.localHistory M K (j + 1) C) (j + 1) ψk) x) :
    InPsiTilde (Cx.genW ((H.step (j + 1)).Z)ᶜ) ν
      (max (3 * S.d * S.L * Cx.cs.delta j) (4 * (S.d + 1) * Cx.cs.delta (j + 1)))
      (parentPsi Cx ψk) (fun i => hv i) := by
  have hd : (0 : ℝ) ≤ S.d := Nat.cast_nonneg _
  have hε : 0 < (S.d + 1) * Cx.cs.delta (j + 1) := by positivity
  refine inPsiTilde_genW_of_factors_local H Cx ψk hv ν (4 * (S.d + 1) * Cx.cs.delta (j + 1)) hν
    hunit (by positivity) hmass hActLoc ?_ ?_
  · intro s _ hY
    refine (parentPsi_sphere_over_Y Cx _ ψk hv hχ HB hY).trans_le ?_
    nlinarith
  · intro s s' hp hY _
    refine (parentPsi_pair_over_Y Cx _ ψk hv hχ hp (Or.inl hY)).trans_le ?_
    nlinarith

/-- **The early-regime parent domain with the local active factor.**  At the scales
`1 ≤ k = j + 1 ≤ k₀` with `Cx.cs.delta = deltaRun`, from `χ_Y ≠ 0`, the cube `BgHyp` and the
local activity factor. -/
theorem inPsiTilde_genW_of_early_chiY_local {d : ℕ} {β ν0 a ε : ℝ} {b nr : ℕ → ℝ} {A0 : ℝ}
    {p0 : ℕ} (ψk : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N))
    (hv : EuclideanSpace ℝ (Fin N))
    (hreg : RunningHyp d S.L β ν0 a ε b nr) (hg : KZeroGenuine β ν0)
    (hk : j + 1 ≤ kZero d S.L β ν0) (hA0 : 0 ≤ A0) (hl0 : 0 ≤ runLam a b (j + 1))
    (hlam : 2 * a * Real.exp (2 * ε) < A0 ^ 2 * runLam a b (j + 1) ^ (2 * p0))
    (hδrun : Cx.cs.delta = deltaRun A0 p0 a b)
    (hunit : ‖hv‖ = 1)
    (hδ : 0 < Cx.cs.delta (j + 1)) (hδ1 : (S.d + 1) * Cx.cs.delta (j + 1) ≤ 1)
    (hχ : Cx.chiY ((H.step (j + 1)).Z)ᶜ ψk hv ≠ 0)
    (HB : BgHyp S.d S.L (j + 1) (minSep S.L Cx.geo.M1) Cx.weights (Cx.cs.mu (j + 1)))
    (hActLoc : ∀ C : H.Comp (j + 1), C.1 ∉ H.rem (j + 1) →
      (∃ t ∈ dataSites (Cx.genW ((H.step (j + 1)).Z)ᶜ), parentSiteCube Cx t ∈ C.1) →
      ∃ (A : Set (InternalVars (H.localHistory M K (j + 1) C) (j + 1)))
        (x : SubCfg N (H.localHistory M K (j + 1) C) (j + 1) A),
        ChiDomAt Cx.geo Cx.cs H (j + 1) C
          (outOf R (H.localHistory M K (j + 1) C) (j + 1) ψk) x) :
    InPsiTilde (Cx.genW ((H.step (j + 1)).Z)ᶜ) (sfBgMassAt S.L (j + 1) (nr (j + 1)))
      (max (3 * S.d * S.L * Cx.cs.delta j) (4 * (S.d + 1) * Cx.cs.delta (j + 1)))
      (parentPsi Cx ψk) (fun i => hv i) := by
  have hd : (0 : ℝ) ≤ S.d := Nat.cast_nonneg _
  have hηYδ : deltaRun A0 p0 a b (j + 1) ≤ 4 * (S.d + 1) * Cx.cs.delta (j + 1) := by
    rw [← congrFun hδrun (j + 1)]
    nlinarith
  have hm := hmass_of_early (S := S) (j := j) hreg hg hk hA0 hl0 hlam hηYδ
  rw [← congrFun hδrun j] at hm
  have hν : 0 ≤ sfBgMassAt S.L (j + 1) (nr (j + 1)) := by
    obtain ⟨δ, hδp, -, he⟩ := hreg.nu_eq (j + 1)
    unfold sfBgMassAt
    refine physMass_nonneg _ _ ?_
    rw [he]
    have := hreg.hν
    positivity
  exact inPsiTilde_genW_of_chiY_local H Cx ψk hv _ hν hunit hδ hδ1 hχ HB hm hActLoc

/-- The real domain for the datum from the real domain for the field. -/
theorem inDomainR_of_inPsiTilde (ψk : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N))
    (hv : EuclideanSpace ℝ (Fin N)) (ν η : ℝ)
    (h : InPsiTilde (Cx.genW ((H.step (j + 1)).Z)ᶜ) ν η (parentPsi Cx ψk) (fun i => hv i)) :
    InDomainR (Cx.genW ((H.step (j + 1)).Z)ᶜ) ν η
      (liftSingle (Cx.genW ((H.step (j + 1)).Z)ᶜ) (Cx.liftData ψk) (hC hv)) :=
  ⟨parentPsi Cx ψk, fun i => hv i, h,
    fun x hx i => liftSingle_Ψ_eq_parentPsi Cx _ ψk hv hx i,
    fun x hx i => by rw [liftSingle_h _ _ _ hx]; rfl⟩

end Core

section D1

open Balaban.LargeField.Def7v2

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ} {M : ℕ} [NeZero M]
  [NeZero S.L] {N m₁ j : ℕ} {ϱ : ℝ} {geo : Geo S n R M} {cs : OpConsts} {P : BudgetConsts}
  (Cx : SFCtx S n R M K N (j + 1) m₁ ϱ) (rep : Rep S n R k0 K M N geo cs P (j + 1))
  (A : LabHist S n R k0 K)

/-- The components of `Z_k(A)` of the post-`R` product of D1 and the retained components of the
region history `A.H` are the same subtype, so a family of `ChiDomAt` facts indexed by `PostComp`
gives the local activity factor of `ParentDomain`. -/
theorem hActLoc_of_forall (hgeo : Cx.geo = geo) (hcs : Cx.cs = cs)
    (ψk : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N))
    (x : GCfg (fun c : PostComp A (j + 1) => A.H.localHistory M K (j + 1) c.1) (j + 1)
      (postOp geo cs rep.SD rep.KD A Cx.hkK))
    (hc : ∀ c : PostComp A (j + 1),
      ChiDomAt geo cs A.H (j + 1) c.1 (outOf R (A.H.localHistory M K (j + 1) c.1) (j + 1) ψk) (x c)) :
    ∀ C : A.H.Comp (j + 1), C.1 ∉ A.H.rem (j + 1) →
      (∃ t ∈ dataSites (Cx.genW ((A.H.step (j + 1)).Z)ᶜ), parentSiteCube Cx t ∈ C.1) →
      ∃ (B : Set (InternalVars (A.H.localHistory M K (j + 1) C) (j + 1)))
        (y : SubCfg N (A.H.localHistory M K (j + 1) C) (j + 1) B),
        ChiDomAt Cx.geo Cx.cs A.H (j + 1) C
          (outOf R (A.H.localHistory M K (j + 1) C) (j + 1) ψk) y := by
  intro C hC _
  rw [hgeo, hcs]
  exact ⟨_, x ⟨C, hC⟩, hc ⟨C, hC⟩⟩

variable {d : ℕ} {β ν0 a ε : ℝ} {b nr : ℕ → ℝ} {A0 : ℝ} {p0 : ℕ}
  (ψk : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N)) (hv : EuclideanSpace ℝ (Fin N))
  (g : GIdx S n M K N → ℂ)

/-- **The datum lies in the real domain wherever the weighted integrand of (D1) is nonzero**
(first version of the form clause), scales `k = j + 1 ≤ k₀`.

Typing: `hgeo`, `hcs` (the context is the one of the representation), `hunit : ‖h‖ = 1`,
`HB` (the admissible weights of the cube solver).  Standing regime: `hreg`, `hg`, `hk`,
`hδrun`, `hA0`, `hl0`.  Smallness: `hδ`, `hδ1` (on `δ_k`) and the largeness condition `hlam`.
No hypothesis asserts a domain or a characteristic property. -/
theorem inPsiTilde_of_postWeighted_ne_zero (hgeo : Cx.geo = geo) (hcs : Cx.cs = cs)
    (hreg : RunningHyp d S.L β ν0 a ε b nr) (hg' : KZeroGenuine β ν0)
    (hk : j + 1 ≤ kZero d S.L β ν0) (hA0 : 0 ≤ A0) (hl0 : 0 ≤ runLam a b (j + 1))
    (hlam : 2 * a * Real.exp (2 * ε) < A0 ^ 2 * runLam a b (j + 1) ^ (2 * p0))
    (hδrun : Cx.cs.delta = deltaRun A0 p0 a b) (hunit : ‖hv‖ = 1)
    (hδ : 0 < Cx.cs.delta (j + 1)) (hδ1 : (S.d + 1) * Cx.cs.delta (j + 1) ≤ 1)
    (HB : BgHyp S.d S.L (j + 1) (minSep S.L Cx.geo.M1) Cx.weights (Cx.cs.mu (j + 1)))
    (x : GCfg (fun c : PostComp A (j + 1) => A.H.localHistory M K (j + 1) c.1) (j + 1)
      (postOp geo cs rep.SD rep.KD A Cx.hkK))
    (hW : postWeighted Cx rep A ψk hv g x ≠ 0) :
    InPsiTilde (Cx.genW ((A.H.step (j + 1)).Z)ᶜ) (sfBgMassAt S.L (j + 1) (nr (j + 1)))
      (max (3 * S.d * S.L * Cx.cs.delta j) (4 * (S.d + 1) * Cx.cs.delta (j + 1)))
      (parentPsi Cx ψk) (fun i => hv i) :=
  inPsiTilde_genW_of_early_chiY_local A.H Cx ψk hv hreg hg' hk hA0 hl0 hlam hδrun hunit hδ hδ1
    (chiY_ne_zero_of_postWeighted_ne_zero Cx rep A ψk hv g x hW) HB
    (hActLoc_of_forall Cx rep A hgeo hcs ψk x
      (chiDomAt_of_postWeighted_ne_zero Cx rep A ψk hv g x hW))

/-- The `InDomainR` form of `inPsiTilde_of_postWeighted_ne_zero`. -/
theorem inDomainR_of_postWeighted_ne_zero (hgeo : Cx.geo = geo) (hcs : Cx.cs = cs)
    (hreg : RunningHyp d S.L β ν0 a ε b nr) (hg' : KZeroGenuine β ν0)
    (hk : j + 1 ≤ kZero d S.L β ν0) (hA0 : 0 ≤ A0) (hl0 : 0 ≤ runLam a b (j + 1))
    (hlam : 2 * a * Real.exp (2 * ε) < A0 ^ 2 * runLam a b (j + 1) ^ (2 * p0))
    (hδrun : Cx.cs.delta = deltaRun A0 p0 a b) (hunit : ‖hv‖ = 1)
    (hδ : 0 < Cx.cs.delta (j + 1)) (hδ1 : (S.d + 1) * Cx.cs.delta (j + 1) ≤ 1)
    (HB : BgHyp S.d S.L (j + 1) (minSep S.L Cx.geo.M1) Cx.weights (Cx.cs.mu (j + 1)))
    (x : GCfg (fun c : PostComp A (j + 1) => A.H.localHistory M K (j + 1) c.1) (j + 1)
      (postOp geo cs rep.SD rep.KD A Cx.hkK))
    (hW : postWeighted Cx rep A ψk hv g x ≠ 0) :
    InDomainR (Cx.genW ((A.H.step (j + 1)).Z)ᶜ) (sfBgMassAt S.L (j + 1) (nr (j + 1)))
      (max (3 * S.d * S.L * Cx.cs.delta j) (4 * (S.d + 1) * Cx.cs.delta (j + 1)))
      (liftSingle (Cx.genW ((A.H.step (j + 1)).Z)ᶜ) (Cx.liftData ψk) (hC hv)) :=
  inDomainR_of_inPsiTilde A.H Cx ψk hv _ _
    (inPsiTilde_of_postWeighted_ne_zero Cx rep A ψk hv g hgeo hcs hreg hg' hk hA0 hl0 hlam hδrun
      hunit hδ hδ1 HB x hW)

/-- **Integrated form.**  If the post term of the history `A` is nonzero at `ψ_k`, the datum lies in
the domain. -/
theorem inPsiTilde_of_postTerm_ne_zero (hgeo : Cx.geo = geo) (hcs : Cx.cs = cs)
    (hreg : RunningHyp d S.L β ν0 a ε b nr) (hg' : KZeroGenuine β ν0)
    (hk : j + 1 ≤ kZero d S.L β ν0) (hA0 : 0 ≤ A0) (hl0 : 0 ≤ runLam a b (j + 1))
    (hlam : 2 * a * Real.exp (2 * ε) < A0 ^ 2 * runLam a b (j + 1) ^ (2 * p0))
    (hδrun : Cx.cs.delta = deltaRun A0 p0 a b) (hunit : ‖hv‖ = 1)
    (hδ : 0 < Cx.cs.delta (j + 1)) (hδ1 : (S.d + 1) * Cx.cs.delta (j + 1) ≤ 1)
    (HB : BgHyp S.d S.L (j + 1) (minSep S.L Cx.geo.M1) Cx.weights (Cx.cs.mu (j + 1)))
    (hT : postTerm Cx rep A ψk hv g ≠ 0) :
    InPsiTilde (Cx.genW ((A.H.step (j + 1)).Z)ᶜ) (sfBgMassAt S.L (j + 1) (nr (j + 1)))
      (max (3 * S.d * S.L * Cx.cs.delta j) (4 * (S.d + 1) * Cx.cs.delta (j + 1)))
      (parentPsi Cx ψk) (fun i => hv i) := by
  obtain ⟨x, hx⟩ := exists_postWeighted_ne_zero_of_postTerm_ne_zero Cx rep A ψk hv g hT
  exact inPsiTilde_of_postWeighted_ne_zero Cx rep A ψk hv g hgeo hcs hreg hg' hk hA0 hl0 hlam
    hδrun hunit hδ hδ1 HB x hx

/-- **The dichotomy for the next consumer**: at every `ψ_k` the post term of the history vanishes
or the datum lies in the domain. -/
theorem postTerm_eq_zero_or_inPsiTilde (hgeo : Cx.geo = geo) (hcs : Cx.cs = cs)
    (hreg : RunningHyp d S.L β ν0 a ε b nr) (hg' : KZeroGenuine β ν0)
    (hk : j + 1 ≤ kZero d S.L β ν0) (hA0 : 0 ≤ A0) (hl0 : 0 ≤ runLam a b (j + 1))
    (hlam : 2 * a * Real.exp (2 * ε) < A0 ^ 2 * runLam a b (j + 1) ^ (2 * p0))
    (hδrun : Cx.cs.delta = deltaRun A0 p0 a b) (hunit : ‖hv‖ = 1)
    (hδ : 0 < Cx.cs.delta (j + 1)) (hδ1 : (S.d + 1) * Cx.cs.delta (j + 1) ≤ 1)
    (HB : BgHyp S.d S.L (j + 1) (minSep S.L Cx.geo.M1) Cx.weights (Cx.cs.mu (j + 1))) :
    postTerm Cx rep A ψk hv g = 0 ∨
      InPsiTilde (Cx.genW ((A.H.step (j + 1)).Z)ᶜ) (sfBgMassAt S.L (j + 1) (nr (j + 1)))
        (max (3 * S.d * S.L * Cx.cs.delta j) (4 * (S.d + 1) * Cx.cs.delta (j + 1)))
        (parentPsi Cx ψk) (fun i => hv i) := by
  by_cases h : postTerm Cx rep A ψk hv g = 0
  · exact Or.inl h
  · exact Or.inr (inPsiTilde_of_postTerm_ne_zero Cx rep A ψk hv g hgeo hcs hreg hg' hk hA0 hl0
      hlam hδrun hunit hδ hδ1 HB h)

/-! ### Second version of the form clause (the one used by `IsRep2`) -/

variable (vc : CorrCoef S.d)

/-- `inPsiTilde_of_postWeighted_ne_zero` for the second version (`postWeighted2`). -/
theorem inPsiTilde_of_postWeighted2_ne_zero (hgeo : Cx.geo = geo) (hcs : Cx.cs = cs)
    (hreg : RunningHyp d S.L β ν0 a ε b nr) (hg' : KZeroGenuine β ν0)
    (hk : j + 1 ≤ kZero d S.L β ν0) (hA0 : 0 ≤ A0) (hl0 : 0 ≤ runLam a b (j + 1))
    (hlam : 2 * a * Real.exp (2 * ε) < A0 ^ 2 * runLam a b (j + 1) ^ (2 * p0))
    (hδrun : Cx.cs.delta = deltaRun A0 p0 a b) (hunit : ‖hv‖ = 1)
    (hδ : 0 < Cx.cs.delta (j + 1)) (hδ1 : (S.d + 1) * Cx.cs.delta (j + 1) ≤ 1)
    (HB : BgHyp S.d S.L (j + 1) (minSep S.L Cx.geo.M1) Cx.weights (Cx.cs.mu (j + 1)))
    (x : GCfg (fun c : PostComp A (j + 1) => A.H.localHistory M K (j + 1) c.1) (j + 1)
      (postOp geo cs rep.SD rep.KD A Cx.hkK))
    (hW : postWeighted2 Cx vc rep A ψk hv g x ≠ 0) :
    InPsiTilde (Cx.genW ((A.H.step (j + 1)).Z)ᶜ) (sfBgMassAt S.L (j + 1) (nr (j + 1)))
      (max (3 * S.d * S.L * Cx.cs.delta j) (4 * (S.d + 1) * Cx.cs.delta (j + 1)))
      (parentPsi Cx ψk) (fun i => hv i) :=
  inPsiTilde_genW_of_early_chiY_local A.H Cx ψk hv hreg hg' hk hA0 hl0 hlam hδrun hunit hδ hδ1
    (chiY_ne_zero_of_postWeighted2_ne_zero Cx vc rep A ψk hv g x hW) HB
    (hActLoc_of_forall Cx rep A hgeo hcs ψk x
      (chiDomAt_of_postWeighted2_ne_zero Cx vc rep A ψk hv g x hW))

/-- The `InDomainR` form, second version. -/
theorem inDomainR_of_postWeighted2_ne_zero (hgeo : Cx.geo = geo) (hcs : Cx.cs = cs)
    (hreg : RunningHyp d S.L β ν0 a ε b nr) (hg' : KZeroGenuine β ν0)
    (hk : j + 1 ≤ kZero d S.L β ν0) (hA0 : 0 ≤ A0) (hl0 : 0 ≤ runLam a b (j + 1))
    (hlam : 2 * a * Real.exp (2 * ε) < A0 ^ 2 * runLam a b (j + 1) ^ (2 * p0))
    (hδrun : Cx.cs.delta = deltaRun A0 p0 a b) (hunit : ‖hv‖ = 1)
    (hδ : 0 < Cx.cs.delta (j + 1)) (hδ1 : (S.d + 1) * Cx.cs.delta (j + 1) ≤ 1)
    (HB : BgHyp S.d S.L (j + 1) (minSep S.L Cx.geo.M1) Cx.weights (Cx.cs.mu (j + 1)))
    (x : GCfg (fun c : PostComp A (j + 1) => A.H.localHistory M K (j + 1) c.1) (j + 1)
      (postOp geo cs rep.SD rep.KD A Cx.hkK))
    (hW : postWeighted2 Cx vc rep A ψk hv g x ≠ 0) :
    InDomainR (Cx.genW ((A.H.step (j + 1)).Z)ᶜ) (sfBgMassAt S.L (j + 1) (nr (j + 1)))
      (max (3 * S.d * S.L * Cx.cs.delta j) (4 * (S.d + 1) * Cx.cs.delta (j + 1)))
      (liftSingle (Cx.genW ((A.H.step (j + 1)).Z)ᶜ) (Cx.liftData ψk) (hC hv)) :=
  inDomainR_of_inPsiTilde A.H Cx ψk hv _ _
    (inPsiTilde_of_postWeighted2_ne_zero Cx rep A ψk hv g vc hgeo hcs hreg hg' hk hA0 hl0 hlam
      hδrun hunit hδ hδ1 HB x hW)

/-- **Integrated form, second version.**  A nonzero second-version post term has its datum in the
domain. -/
theorem inPsiTilde_of_postTerm2_ne_zero (hgeo : Cx.geo = geo) (hcs : Cx.cs = cs)
    (hreg : RunningHyp d S.L β ν0 a ε b nr) (hg' : KZeroGenuine β ν0)
    (hk : j + 1 ≤ kZero d S.L β ν0) (hA0 : 0 ≤ A0) (hl0 : 0 ≤ runLam a b (j + 1))
    (hlam : 2 * a * Real.exp (2 * ε) < A0 ^ 2 * runLam a b (j + 1) ^ (2 * p0))
    (hδrun : Cx.cs.delta = deltaRun A0 p0 a b) (hunit : ‖hv‖ = 1)
    (hδ : 0 < Cx.cs.delta (j + 1)) (hδ1 : (S.d + 1) * Cx.cs.delta (j + 1) ≤ 1)
    (HB : BgHyp S.d S.L (j + 1) (minSep S.L Cx.geo.M1) Cx.weights (Cx.cs.mu (j + 1)))
    (hT : postTerm2 Cx vc rep A ψk hv g ≠ 0) :
    InPsiTilde (Cx.genW ((A.H.step (j + 1)).Z)ᶜ) (sfBgMassAt S.L (j + 1) (nr (j + 1)))
      (max (3 * S.d * S.L * Cx.cs.delta j) (4 * (S.d + 1) * Cx.cs.delta (j + 1)))
      (parentPsi Cx ψk) (fun i => hv i) := by
  obtain ⟨x, hx⟩ := exists_postWeighted2_ne_zero_of_postTerm2_ne_zero Cx vc rep A ψk hv g hT
  exact inPsiTilde_of_postWeighted2_ne_zero Cx rep A ψk hv g vc hgeo hcs hreg hg' hk hA0 hl0 hlam
    hδrun hunit hδ hδ1 HB x hx

/-- **The dichotomy, second version**: at every `ψ_k` the second-version post term of the history
vanishes or the datum lies in the domain. -/
theorem postTerm2_eq_zero_or_inPsiTilde (hgeo : Cx.geo = geo) (hcs : Cx.cs = cs)
    (hreg : RunningHyp d S.L β ν0 a ε b nr) (hg' : KZeroGenuine β ν0)
    (hk : j + 1 ≤ kZero d S.L β ν0) (hA0 : 0 ≤ A0) (hl0 : 0 ≤ runLam a b (j + 1))
    (hlam : 2 * a * Real.exp (2 * ε) < A0 ^ 2 * runLam a b (j + 1) ^ (2 * p0))
    (hδrun : Cx.cs.delta = deltaRun A0 p0 a b) (hunit : ‖hv‖ = 1)
    (hδ : 0 < Cx.cs.delta (j + 1)) (hδ1 : (S.d + 1) * Cx.cs.delta (j + 1) ≤ 1)
    (HB : BgHyp S.d S.L (j + 1) (minSep S.L Cx.geo.M1) Cx.weights (Cx.cs.mu (j + 1))) :
    postTerm2 Cx vc rep A ψk hv g = 0 ∨
      InPsiTilde (Cx.genW ((A.H.step (j + 1)).Z)ᶜ) (sfBgMassAt S.L (j + 1) (nr (j + 1)))
        (max (3 * S.d * S.L * Cx.cs.delta j) (4 * (S.d + 1) * Cx.cs.delta (j + 1)))
        (parentPsi Cx ψk) (fun i => hv i) := by
  by_cases h : postTerm2 Cx vc rep A ψk hv g = 0
  · exact Or.inl h
  · exact Or.inr (inPsiTilde_of_postTerm2_ne_zero Cx rep A ψk hv g vc hgeo hcs hreg hg' hk hA0 hl0
      hlam hδrun hunit hδ hδ1 HB h)

end D1

end Balaban.LargeField
