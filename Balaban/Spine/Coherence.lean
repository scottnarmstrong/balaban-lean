/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Def7v2Variants

/-!
# Torus coherence of the large-field data, and the running hypothesis up to a scale

Spine-local predicates used by the class predicates of `Balaban/Spine/RootFInputs.lean`.

* `LFCoherent F`: the large-field half of (D8) of LFR Definition II.6.2, in the form of D-IV.9.
  Every localized datum of the large-field part of a family of representations whose support lies in
  the image of a box `{y ∈ ℤ^d : |y_μ - c_μ| < ℓ/4}` is the push-forward of one datum attached to
  the corresponding finite subset of `ℤ^d`, the same for all tori of the family. The data are the
  step kernels and boundary factors of the localized histories (S0)–(S2), the kept kernels, their
  variable sets `I''` and exponents (S3), and the boundary terms `ℬ^{(k)}(X, 𝔸)` (D7). Two tori of
  the family (`n_K = nK₁, nK₂`) are compared through the representatives in `ℤ^d` nearest to a
  centre `c` (`liftNear`). Points, sets, blocks, variables, configurations and sources correspond
  when their representatives agree and lie in the box of both tori (`PtCorr`, `SetCorr`, `BlkCorr`,
  `VarCorr`, `OutCorr`, `CfgCorr`, `GCorr`, `MultiCorr`, `HistCorr`). The small-field half of (D8)
  is the landed clause `D8SF` of `IsRep2`/`IsRepFlat2`.
* `RunningHypTo` (now `Balaban.LargeField.RunningHypTo`, `Analytic/Constants.lean`): the hypothesis (I.2) of LFR (A-IV.2) on the running coefficients
  (`β_j = β L^{j(d-2)} γ_j`, `ν_j = ν L^{2j} δ_j`, `|log γ_j|, |log δ_j| ≤ ε ≤ 1/20`,
  `a ∈ (1, 3/2)`) at the scales `j ≤ k` only. The landed `RunningHyp` asks it at every scale. -/

@[expose] public section

namespace Balaban.RootFSpine

open Balaban Balaban.LargeField Balaban.LargeField.Def7 RegionHistory

/-!
### Correspondence through a box of `ℤ^d`
-/

section Box

variable {d : ℕ}

/-- The representative in `ℤ^d` of a point of the torus `𝕋_m` that is nearest to the centre `c`. -/
def liftNear {m : ℕ} (c : Fin d → ℤ) (x : Torus d m) : Fin d → ℤ :=
  fun μ => c μ + ZMod.valMinAbs (x μ - (c μ : ZMod m))

/-- `y` lies in the box `{|y_μ - c_μ| < min(m₁, m₂)/4}` (LFR D-IV.9), whose images in `𝕋_{m₁}` and
`𝕋_{m₂}` are injective and preserve adjacency. -/
def InBox (m₁ m₂ : ℕ) (c y : Fin d → ℤ) : Prop :=
  ∀ μ, 4 * |y μ - c μ| < (m₁ : ℤ) ∧ 4 * |y μ - c μ| < (m₂ : ℤ)

/-- Two points of the tori `𝕋_{m₁}`, `𝕋_{m₂}` correspond: they have the same representative near
`c`, in the box. -/
def PtCorr {m₁ m₂ : ℕ} (c : Fin d → ℤ) (x₁ : Torus d m₁) (x₂ : Torus d m₂) : Prop :=
  liftNear c x₁ = liftNear c x₂ ∧ InBox m₁ m₂ c (liftNear c x₁)

/-- Two sets of the tori correspond: both lie in the image of the box, and each is the image of the
other. -/
def SetCorr {m₁ m₂ : ℕ} (c : Fin d → ℤ) (A₁ : Set (Torus d m₁)) (A₂ : Set (Torus d m₂)) : Prop :=
  (∀ x ∈ A₁, InBox m₁ m₂ c (liftNear c x)) ∧ (∀ x ∈ A₂, InBox m₁ m₂ c (liftNear c x)) ∧
    ∀ x₁ x₂, liftNear c x₁ = liftNear c x₂ → (x₁ ∈ A₁ ↔ x₂ ∈ A₂)

end Box

/-!
### Blocks, variables, configurations, histories of two tori of a family
-/

section Family

variable {S : Setting} {n₁ n₂ : ℕ → ℕ} {M K N : ℕ}

/-- A `j₁`-block of the first family and a `j₂`-block of the second correspond: `j₁ = j₂` and they
contain corresponding sites. -/
def BlkCorr (c : Fin S.d → ℤ) (j₁ j₂ : ℕ) (y₁ : BlockAt S n₁ M K j₁) (y₂ : BlockAt S n₂ M K j₂) :
    Prop :=
  j₁ = j₂ ∧ ∃ (x₁ : Torus S.d (M * n₁ K * S.L ^ K)) (x₂ : Torus S.d (M * n₂ K * S.L ^ K)),
    Multiscale.jBlock S.d S.L (M * n₁ K) K j₁ x₁ = y₁ ∧
    Multiscale.jBlock S.d S.L (M * n₂ K) K j₂ x₂ = y₂ ∧ PtCorr c x₁ x₂

/-- Two localized histories correspond: each record of the second is the image of the record of the
first, in the box. -/
def HistCorr (c : Fin S.d → ℤ) (a₁ : LocalHistory S n₁ M K) (a₂ : LocalHistory S n₂ M K) : Prop :=
  ∀ j, SetCorr c (a₁.Z j) (a₂.Z j) ∧ SetCorr c (a₁.P j) (a₂.P j) ∧ SetCorr c (a₁.Q j) (a₂.Q j) ∧
    SetCorr c (a₁.R j) (a₂.R j) ∧ SetCorr c (a₁.Sset j) (a₂.Sset j) ∧
    SetCorr c (a₁.OmegaPrime j) (a₂.OmegaPrime j) ∧ SetCorr c (a₁.Omega j) (a₂.Omega j) ∧
    SetCorr c (a₁.OmegaDD j) (a₂.OmegaDD j)

/-- Two internal variables correspond: same scale, same kind, corresponding blocks. -/
def VarCorr (c : Fin S.d → ℤ) {a₁ : LocalHistory S n₁ M K} {a₂ : LocalHistory S n₂ M K} {k : ℕ}
    (p₁ : InternalVars a₁ k) (p₂ : InternalVars a₂ k) : Prop :=
  p₁.1.2.1 = p₂.1.2.1 ∧ BlkCorr c (p₁.1.1 : ℕ) (p₂.1.1 : ℕ) p₁.1.2.2 p₂.1.2.2

/-- Two output configurations (on sets of `k`-blocks) correspond: equal values at corresponding
blocks (`outField` is `0` off the set). -/
def OutCorr (c : Fin S.d → ℤ) (k : ℕ) {V₁ : Set (BlockAt S n₁ M K k)}
    {V₂ : Set (BlockAt S n₂ M K k)} (o₁ : OutConfig N V₁) (o₂ : OutConfig N V₂) : Prop :=
  ∀ y₁ y₂, BlkCorr c k k y₁ y₂ → outField N o₁ y₁ = outField N o₂ y₂

/-- Two configurations of internal variables correspond: equal values at corresponding variables. -/
def CfgCorr (c : Fin S.d → ℤ) {a₁ : LocalHistory S n₁ M K} {a₂ : LocalHistory S n₂ M K} {k : ℕ}
    {A₁ : Set (InternalVars a₁ k)} {A₂ : Set (InternalVars a₂ k)} (x₁ : SubCfg N a₁ k A₁)
    (x₂ : SubCfg N a₂ k A₂) : Prop :=
  ∀ (p₁ : A₁) (p₂ : A₂), VarCorr c p₁.1 p₂.1 → VarVal.toEuc (x₁ p₁) = VarVal.toEuc (x₂ p₂)

/-- Two external sources correspond: equal values at corresponding sites. -/
def GCorr (c : Fin S.d → ℤ) (g₁ : GIdx S n₁ M K N → ℂ) (g₂ : GIdx S n₂ M K N → ℂ) : Prop :=
  ∀ x₁ x₂ i, PtCorr c x₁ x₂ → g₁ (x₁, i) = g₂ (x₂, i)

/-- Two multiscale fields correspond: equal values at corresponding blocks of every scale. -/
def MultiCorr (c : Fin S.d → ℤ) (ψ₁ : MultiFieldC S n₁ M K N) (ψ₂ : MultiFieldC S n₂ M K N) :
    Prop :=
  ∀ j y₁ y₂, BlkCorr c j j y₁ y₂ → ψ₁ j y₁ = ψ₂ j y₂

end Family

/-!
### The large-field half of (D8)
-/

section Coherent

variable {S : Setting} [NeZero S.L] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M] {N : ℕ}
  {geo : ∀ (nK : ℕ) [NeZero nK], Geo S (sides S.L K nK) R M} {cs : OpConsts} {P : BudgetConsts}
  {k m₁ : ℕ} {ϱ : ℝ}

/-- **The large-field half of (D8)** (LFR Definition II.6.2 (D8), version 1.2 D-IV.9): for any two
tori `n_K = nK₁, nK₂` of the family and any centre `c`, the localized large-field data supported in
the image of the box of both tori agree at corresponding arguments:
* the step kernel `K_j(Z', a)` and boundary factor `b_j(Z', a)` of a localized history of an
  admissible history, when the localized histories and their sets `V` correspond;
* the kept variable sets `I''`, kept kernels and kept exponents `κ_j(Z, a)`, likewise;
* the boundary terms `ℬ^{(k)}(X, 𝔸)` of two histories of the representations, when the domains `X`,
  the records of the two histories on `X` and the localized histories of the components of `Z_k`
  meeting `X` correspond (the two-torus form of the locality clause of (D7)). -/
def LFCoherent (F : RepFam S R k0 K M N geo cs P k m₁ ϱ) : Prop :=
  ∀ (nK₁ nK₂ : ℕ) [NeZero nK₁] [NeZero nK₂] (c : Fin S.d → ℤ),
    (∀ (H₁ : RegionHistory S (sides S.L K nK₁) R k0 K)
        (H₂ : RegionHistory S (sides S.L K nK₂) R k0 K), H₁.Admissible → H₂.Admissible →
      ∀ (j : ℕ) (Z₁ : H₁.Comp (j + 1)) (Z₂ : H₂.Comp (j + 1)),
        HistCorr c (H₁.localHistory M K (j + 1) Z₁) (H₂.localHistory M K (j + 1) Z₂) →
        SetCorr c (Vsites R (H₁.localHistory M K (j + 1) Z₁) (j + 1))
          (Vsites R (H₂.localHistory M K (j + 1) Z₂) (j + 1)) →
        ∀ o₁ o₂ x₁ x₂ hv g₁ g₂, OutCorr c (j + 1) o₁ o₂ → CfgCorr c x₁ x₂ → GCorr c g₁ g₂ →
          ((F.lf nK₂).SD.ker j (H₂.localHistory M K (j + 1) Z₂)).K o₂ x₂ hv =
              ((F.lf nK₁).SD.ker j (H₁.localHistory M K (j + 1) Z₁)).K o₁ x₁ hv ∧
            ((F.lf nK₂).SD.ker j (H₂.localHistory M K (j + 1) Z₂)).b o₂ x₂ hv g₂ =
              ((F.lf nK₁).SD.ker j (H₁.localHistory M K (j + 1) Z₁)).b o₁ x₁ hv g₁) ∧
    (∀ (H₁ : RegionHistory S (sides S.L K nK₁) R k0 K)
        (H₂ : RegionHistory S (sides S.L K nK₂) R k0 K), H₁.Admissible → H₂.Admissible →
      ∀ (j : ℕ) (Z₁ : H₁.Comp j) (Z₂ : H₂.Comp j),
        HistCorr c (H₁.localHistory M K j Z₁) (H₂.localHistory M K j Z₂) →
        SetCorr c (Vsites R (H₁.localHistory M K j Z₁) j) (Vsites R (H₂.localHistory M K j Z₂) j) →
        (F.lf nK₂).κK j (H₂.localHistory M K j Z₂) = (F.lf nK₁).κK j (H₁.localHistory M K j Z₁) ∧
        ∀ ϰ : Fin 5,
          (∀ p₁ p₂, VarCorr c p₁ p₂ →
            (p₁ ∈ ((F.lf nK₁).KD.datum j (H₁.localHistory M K j Z₁) ϰ).Ikeep ↔
              p₂ ∈ ((F.lf nK₂).KD.datum j (H₂.localHistory M K j Z₂) ϰ).Ikeep)) ∧
          ∀ o₁ o₂ x₁ x₂ hv g₁ g₂, OutCorr c j o₁ o₂ → CfgCorr c x₁ x₂ → GCorr c g₁ g₂ →
            ((F.lf nK₂).KD.datum j (H₂.localHistory M K j Z₂) ϰ).ker.K o₂ x₂ hv =
                ((F.lf nK₁).KD.datum j (H₁.localHistory M K j Z₁) ϰ).ker.K o₁ x₁ hv ∧
              ((F.lf nK₂).KD.datum j (H₂.localHistory M K j Z₂) ϰ).ker.b o₂ x₂ hv g₂ =
                ((F.lf nK₁).KD.datum j (H₁.localHistory M K j Z₁) ϰ).ker.b o₁ x₁ hv g₁) ∧
    ∀ A₁ ∈ (F.lf nK₁).hist, ∀ A₂ ∈ (F.lf nK₂).hist,
      ∀ (X₁ : Finset (Torus S.d (sides S.L K nK₁ k))) (X₂ : Finset (Torus S.d (sides S.L K nK₂ k))),
        X₁ ∈ bdryDoms (OmegaCube A₁.H k) (A₁.H.step k).Z →
        X₂ ∈ bdryDoms (OmegaCube A₂.H k) (A₂.H.step k).Z →
        SetCorr c (fineSet (S := S) M K k (X₁ : Set (Torus S.d (sides S.L K nK₁ k))))
          (fineSet (S := S) M K k (X₂ : Set (Torus S.d (sides S.L K nK₂ k)))) →
        (∀ j, j ≤ k →
          SetCorr c (fineSet (S := S) M K j (OmegaCube A₁.H j) ∩
              fineSet (S := S) M K k (X₁ : Set (Torus S.d (sides S.L K nK₁ k))))
            (fineSet (S := S) M K j (OmegaCube A₂.H j) ∩
              fineSet (S := S) M K k (X₂ : Set (Torus S.d (sides S.L K nK₂ k)))) ∧
          SetCorr c ((globalLH A₁.H M).OmegaDD j ∩
              fineSet (S := S) M K k (X₁ : Set (Torus S.d (sides S.L K nK₁ k))))
            ((globalLH A₂.H M).OmegaDD j ∩
              fineSet (S := S) M K k (X₂ : Set (Torus S.d (sides S.L K nK₂ k)))) ∧
          SetCorr c ((globalLH A₁.H M).Z j ∩
              fineSet (S := S) M K k (X₁ : Set (Torus S.d (sides S.L K nK₁ k))))
            ((globalLH A₂.H M).Z j ∩
              fineSet (S := S) M K k (X₂ : Set (Torus S.d (sides S.L K nK₂ k))))) →
        (∀ c₁ : PostComp A₁ k, (c₁.1.1 ∩ X₁).Nonempty → ∃ c₂ : PostComp A₂ k,
          SetCorr c (fineSet (S := S) M K k (c₁.1.1 : Set (Torus S.d (sides S.L K nK₁ k))))
            (fineSet (S := S) M K k (c₂.1.1 : Set (Torus S.d (sides S.L K nK₂ k)))) ∧
          HistCorr c (A₁.H.localHistory M K k c₁.1) (A₂.H.localHistory M K k c₂.1)) →
        (∀ c₂ : PostComp A₂ k, (c₂.1.1 ∩ X₂).Nonempty → ∃ c₁ : PostComp A₁ k,
          SetCorr c (fineSet (S := S) M K k (c₁.1.1 : Set (Torus S.d (sides S.L K nK₁ k))))
            (fineSet (S := S) M K k (c₂.1.1 : Set (Torus S.d (sides S.L K nK₂ k))))) →
        ∀ ψ₁ ψ'₁ ψ₂ ψ'₂ h g₁ g₂, MultiCorr c ψ₁ ψ₂ → MultiCorr c ψ'₁ ψ'₂ → GCorr c g₁ g₂ →
          (F.lf nK₂).B A₂ X₂ ψ₂ ψ'₂ h g₂ = (F.lf nK₁).B A₁ X₁ ψ₁ ψ'₁ h g₁

end Coherent

section GamConst

variable {S : Setting} [NeZero S.L] {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ}
  [NeZero M] {N : ℕ} {geo : Geo S n R M} {cs : OpConsts} {P : BudgetConsts} {k : ℕ}

/-- **The kept costs are the constants of LFR Definition III.5.2**:
`γ_i(ϰ) = log C_dec + A'₃ λ̂_i^{p_R}` with `C_dec = 5`, a function of the scale only.  It is an
invariant of the class (the kept data of every step are built with it, `KeptScaleData.gam_val`);
it makes the pinned exponents torus coherent. -/
def GamConst (rep : Rep S n R k0 K M N geo cs P k) : Prop :=
  ∀ i l, rep.KD.gam i l = Real.log 5 + S.A3' * S.lam i ^ S.pR

end GamConst

end Balaban.RootFSpine
