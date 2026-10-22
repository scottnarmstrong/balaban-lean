/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Def7v2Form
public import Balaban.LargeField.Def7SmallFieldC

/-!
# The holomorphic exponent of the second version of (D1) at a background field

The exponent `𝒜₂ + ℱ + ℛ` of the small-field factor `sfFactor2` (Def-7 v2, `Def7v2Form`) reads the
background `φ_k = bg(𝔹_k(W_k); lift ψ_k)` through `φ̄_k` (the action, the star bonds, `⟨χ_Y g, φ̄_k⟩`)
and through the composed fields `ψ^{(j)}_k` (the terms `ℰ^{(j)}`, `ℳ^{(j)}` and the correction of
P5 (1.8)).  The localization of the residual of `R` (P7 (3.22)–(3.25), P3 §4) inserts a decoupled
background field in place of `φ_k`.  This file states the exponent at a general background field
`φ` of `𝔹_k(W_k)`, holomorphic in the field `ψ_k`, through the cores of `Def7SmallFieldC`:

* `actStar2At`, `EresJ2At`, `EresK2At`, `Ares2At`, `sfExp2At`: `A*_k` (mass `sfActMass2`),
  `ℰ^{(j)}` with the correction `corrSum`, `ℰ_k`, `𝒜_k` and the exponent `𝒜₂ + ℱ + ℛ` at `φ`;
* `actStar2At_blockToC`, `EresJ2At_blockToC`, `Ares2At_blockToC`, `sfExp2At_blockToC`: at a real
  field with real background and `φ = φ_k` these are the second-version objects;
* `sfFactor2_eq_mul_exp`: `sfFactor2 = χ_k(Y) exp(sfExp2At … φ_k)`.
-/

@[expose] public section

namespace Balaban.LargeField.Def7v2

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.SmallField.Def6
  Balaban.SmallField.Def6v2 Balaban.LargeField.Def7

section Restricted

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N k m₁ : ℕ} {ϱ : ℝ} (C : SFCtx S n R M K N k m₁ ϱ)
  (vc : CorrCoef S.d) (Y : Set (Torus S.d (n k))) (ψC : BlockAt S n M K k → Fin N → ℂ)
  (hv : EuclideanSpace ℝ (Fin N)) (g : GIdx S n M K N → ℂ)

/-- **`A*_k(Y; ψ_k, φ)`, second version, at a background field `φ`** of `𝔹_k(W_k)`: the
holomorphic action with half star bonds of the physical mass `sfActMass2 = cs.muAct k`. -/
noncomputable def actStar2At (φ : (C.genW Y).Ω 1 × Fin N → ℂ) : ℂ :=
  C.actStarAt Y ψC hv (sfActMass2 C.cs k) φ

/-- **`ℰ^{(j)}(Y; ψ^{(j)}, h)`, second version, at a background field `φ`** (P5 (1.8)): the
localized terms at the composed field of `φ` minus the restricted antisymmetric sum `corrSum` of the
coefficient data `vc`. -/
noncomputable def EresJ2At (φ : (C.genW Y).Ω 1 × Fin N → ℂ) (j : ℕ) : ℂ :=
  C.EresMainAt Y ψC hv φ j -
    corrSum (fun y x => vc.v1 j (unlift j (x - y))) (fun y x => vc.v2 j (unlift j (x - y)))
      (nuIdeal S.L k (C.sf.ν k) j) (C.alignedIn j Y) (C.alignedIn j (thickY R Y))
      (C.psiJAt Y ψC hv φ j) (hC hv)

/-- `ℰ_k = ∑_{j=1}^k ℰ^{(j)}`, second version, at a background field `φ` (P5 (1.7)). -/
noncomputable def EresK2At (φ : (C.genW Y).Ω 1 × Fin N → ℂ) : ℂ :=
  ∑ j ∈ Finset.Icc 1 k, EresJ2At C vc Y ψC hv φ j

/-- **`𝒜_k = -β_k A*_k + ℰ_k - E_k |Y|_k`, second version, at a background field `φ`** (P5 (1.6)). -/
noncomputable def Ares2At (φ : (C.genW Y).Ω 1 × Fin N → ℂ) : ℂ :=
  -((betaCanon S.d S.L (C.sf.β k) k 0 : ℝ) : ℂ) * actStar2At C Y ψC hv φ +
    EresK2At C vc Y ψC hv φ - ((C.sf.E C.N₁ * volK M Y : ℝ) : ℂ)

/-- **The exponent `𝒜₂ + ℱ + ℛ` of the second version of (D1) at a background field `φ`.** -/
noncomputable def sfExp2At (φ : (C.genW Y).Ω 1 × Fin N → ℂ) : ℂ :=
  Ares2At C vc Y ψC hv φ + C.FresAt Y ψC hv g φ + C.RresC Y ψC hv g

section Real

variable (ψk : BlockAt S n M K k → EuclideanSpace ℝ (Fin N))
  (hre : ∀ z i, (C.phiBarC Y (blockToC ψk) hv z i).im = 0)
include hre

/-- At a real field with real background, `actStar2At` at `φ_k` is `actStar2`. -/
theorem actStar2At_blockToC :
    actStar2At C Y (blockToC ψk) hv (C.phiKC Y (blockToC ψk) hv) =
      ((actStar2 C Y ψk hv : ℝ) : ℂ) :=
  C.actStarAt_blockToC Y hv ψk hre (sfActMass2 C.cs k)

omit hre in
/-- At a real field, `EresJ2At` at `φ_k` is `EresJ2`. -/
theorem EresJ2At_blockToC (j : ℕ) :
    EresJ2At C vc Y (blockToC ψk) hv (C.phiKC Y (blockToC ψk) hv) j = EresJ2 C vc Y ψk hv j :=
  rfl

omit hre in
/-- At a real field, `EresK2At` at `φ_k` is `EresK2`. -/
theorem EresK2At_blockToC :
    EresK2At C vc Y (blockToC ψk) hv (C.phiKC Y (blockToC ψk) hv) = EresK2 C vc Y ψk hv :=
  rfl

/-- At a real field with real background, `Ares2At` at `φ_k` is `Ares2`. -/
theorem Ares2At_blockToC :
    Ares2At C vc Y (blockToC ψk) hv (C.phiKC Y (blockToC ψk) hv) = Ares2 C vc Y ψk hv := by
  unfold Ares2At Ares2
  rw [actStar2At_blockToC C Y hv ψk hre, EresK2At_blockToC]

/-- **At a real field with real background, `sfExp2At` at `φ_k` is the exponent of the second
version of (D1).** -/
theorem sfExp2At_blockToC :
    sfExp2At C vc Y (blockToC ψk) hv g (C.phiKC Y (blockToC ψk) hv) =
      Ares2 C vc Y ψk hv + C.Fres Y ψk hv g + C.Rres Y ψk hv g := by
  unfold sfExp2At
  rw [Ares2At_blockToC C vc Y hv ψk hre, ← SFCtx.Rres_eq]
  congr 2
  exact C.FresC_blockToC Y hv g ψk hre

/-- **The small-field factor of the second version of (D1)** at a real field with real background:
`χ_k(Y) exp(𝒜₂ + ℱ + ℛ)(Y) = χ_k(Y) exp(sfExp2At … φ_k)`. -/
theorem sfFactor2_eq_mul_exp :
    sfFactor2 C vc Y ψk hv g =
      ((C.chiY Y ψk hv : ℝ) : ℂ) *
        Complex.exp (sfExp2At C vc Y (blockToC ψk) hv g (C.phiKC Y (blockToC ψk) hv)) := by
  unfold sfFactor2
  rw [sfExp2At_blockToC C vc Y hv g ψk hre]

end Real

end Restricted

end Balaban.LargeField.Def7v2
