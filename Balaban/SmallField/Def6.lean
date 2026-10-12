/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.Def6Terms
public import Balaban.SmallField.TaylorCauchy

/-!
# Def-6: the small-field class `ℛ^sf_k` at `λ = ∞` (SMALLFIELD.md §1.1-§1.3, §1.6) -- DRAFT

Draft for review (to be proposed to the author for freezing).  Hypotheses in the numbering of
P4, P1's in brackets.  Ambient: the fine torus `CTorus d L N₁ m₁ k` (unit spacing), the whole-lattice
generating sets `levelGS j`, and the landed Def-5 objects `bgField`, `action`, `composeField`.

Conventions fixed by the orchestrator (FLUCTUATION.md F-1, 2026-10-12):
* the analyticity domains of the local terms and of `ℱ_k` are `Ξ^c_j(𝔹_j(X); 1, ε_j)` (landed
  `XiC`), through `XiDom`; the data domain of radius `Kε_j` of SMALLFIELD v2 ruling (iv) is
  withdrawn;
* the passage from `ν`-free to complete backgrounds at `k₀` is handled by FLUCTUATION Lemma 2.9; the
  class has no separate switch clause, only the mass `bgMass` of the backgrounds;
* sizes are the covering functional (`sizeJ = treeLenCovOne`, the single-scale case of
  `treeLenCov`).

Contents: `Consts`, `Terms` (the localized data `ℰ^{(j)}(y, X; ·)`, `ℳ^{(j)}(x, X; ·)`, the
generating sets `𝔹_j(X)`), the composite `ℰ_k`, `ℱ_k`, the per-torus class `IsSF` ((H.1)-(H.4),
(H.7)), the renormalization conditions `RenormCond` (H.5), the coefficient bounds `CoeffBounds`
(H.6), the class of families over tori `IsSFFamily`, and the clause `ContAtZero` (CONT).
-/

@[expose] public section

namespace Balaban.SmallField.Def6

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Finset Filter Topology

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- **The constants** `𝗰` of SMALLFIELD §1.1: `γ ∈ (0, 1/2)`, `α₁ ∈ (0, 1 - 2γ)`, `κ`, `E₀`, `c₈`,
`c₉`, `α₀`, `B`, `ν̄`, the radius constant `p` of `χ_k` (`β_k^{-1/2} p(β_k)`; P4 p. 679) and the
RG exponent `m₀`. -/
structure Consts where
  γ : ℝ
  α₁ : ℝ
  κ : ℝ
  E₀ : ℝ
  c₈ : ℝ
  c₉ : ℝ
  α₀ : ℝ
  B : ℝ
  νbar : ℝ
  p : ℝ → ℝ
  m₀ : ℕ

/-- `α = (d-2)/2 - γ` (P4 §6). -/
noncomputable def Consts.alpha (d : ℕ) (P : Consts) : ℝ := ((d : ℝ) - 2) / 2 - P.γ

/-- **The admissible ranges of the constants** (SMALLFIELD §1.1; P4 §6): `0 < γ < 1/2`,
`0 < α₁ < 1 - 2γ`, `0 < α₀`, `0 < κ`, `0 < ν̄ ≤ 7/8 L^{-2}`. -/
structure Consts.Admissible (d L : ℕ) (P : Consts) : Prop where
  γ_pos : 0 < P.γ
  γ_lt : P.γ < 1 / 2
  α₁_pos : 0 < P.α₁
  α₁_lt : P.α₁ < 1 - 2 * P.γ
  α₀_pos : 0 < P.α₀
  κ_pos : 0 < P.κ
  νbar_pos : 0 < P.νbar
  νbar_le : P.νbar ≤ 7 / 8 * ((L : ℝ) ^ 2)⁻¹
  c₈_pos : 0 < P.c₈

/-- `ε_j = α₀ (1 + Σ_{n ≥ j} n^{-2}) L^{-jα}` (P4 (H.1)). -/
noncomputable def Consts.eps (d L : ℕ) (P : Consts) (j : ℕ) : ℝ :=
  epsSeq L (P.alpha d) P.α₀ j

/-- The gap (E) for the sequence `ε_j` of the class (P3 (4.51); SMALLFIELD §1.7). -/
theorem Consts.eps_gapE (d L : ℕ) (P : Consts) (hα₀ : 0 ≤ P.α₀) :
    GapE L (P.alpha d) (P.eps d L) :=
  epsSeq_gapE L (P.alpha d) P.α₀ hα₀

/-! ### The localized data -/

/-- **The localized data of the class** at one torus: the terms `ℰ^{(j)}(y, X; ψ, h)` ((H.2),
(H.4)), the terms `ℳ^{(j)}(x, X; ψ, h, g)` of (H.7) and the minimal generating sets `𝔹_j(X)` of a
polymer (P3 (4.7)).  The sites `y` stand for their `j`-blocks (`y` is `L^j`-aligned). -/
structure Terms (d L N₁ m₁ k N : ℕ) [NeZero L] [NeZero N₁] (ϱ : ℝ) where
  E : ℕ → CTorus d L N₁ m₁ k → Set (CTorus d L N₁ m₁ k) → Fld d L N₁ m₁ k N →
    Fld d L N₁ m₁ k N → ℂ
  M : ℕ → CTorus d L N₁ m₁ k → Set (CTorus d L N₁ m₁ k) → Fld d L N₁ m₁ k N →
    Fld d L N₁ m₁ k N → Fld d L N₁ m₁ k N → (Fin N → ℂ)
  gs : ℕ → Set (CTorus d L N₁ m₁ k) → GeneratingSet d L (N₁ * L ^ m₁) k ϱ

section Sums

variable (m₀ : ℕ) (Tm : Terms d L N₁ m₁ k N ϱ)

/-- The polymers of `𝒟_j` containing the site `y`. -/
def polysAt (j : ℕ) (y : CTorus d L N₁ m₁ k) : Set (Set (CTorus d L N₁ m₁ k)) :=
  {X | IsPolyDom m₀ j X ∧ y ∈ X}

open Classical in
/-- **`ℰ^{(j)}(y; ψ, h) = Σ_{X ∈ 𝒟_j, X ∋ y} ℰ^{(j)}(y, X; ψ, h)`** (H.4) [P1 (H.5)]. -/
noncomputable def Eloc (j : ℕ) (y : CTorus d L N₁ m₁ k) (ψ h : Fld d L N₁ m₁ k N) : ℂ :=
  ∑ᶠ X ∈ polysAt m₀ j y, Tm.E j y X ψ h

open Classical in
/-- **`ℰ^{(j)}(ψ, h) = Σ_{y ∈ Λ_j} ℰ^{(j)}(y; ψ, h)`** (H.2) [P1 (H.2)], the sum over the
`L^j`-aligned sites. -/
noncomputable def Edens (j : ℕ) (ψ h : Fld d L N₁ m₁ k N) : ℂ :=
  ∑ y ∈ (Finset.univ : Finset (CTorus d L N₁ m₁ k)).filter (Aligned (L ^ j)),
    Eloc m₀ Tm j y ψ h

open Classical in
/-- **`ℳ^{(j)}(x; ψ, h, g) = Σ_{X ∈ 𝒟_j, X ∋ x} ℳ^{(j)}(x, X; ψ, h, g)`** (H.7) [P1 (H.9)]. -/
noncomputable def Mloc (j : ℕ) (x : CTorus d L N₁ m₁ k) (ψ h g : Fld d L N₁ m₁ k N) :
    Fin N → ℂ :=
  ∑ᶠ X ∈ polysAt m₀ j x, Tm.M j x X ψ h g

/-- **`ℱ^{(j)}(ψ, h, g) = ⟨g, ℳ^{(j)}(·; ψ, h, g)⟩₁`** (H.7) [P1 (H.9)]. -/
noncomputable def Floc (j : ℕ) (ψ h g : Fld d L N₁ m₁ k N) : ℂ :=
  ∑ x : CTorus d L N₁ m₁ k, ∑ i, g x i * Mloc m₀ Tm j x ψ h g i

end Sums

/-! ### The composite action `ℰ_k`, `ℱ_k` -/

section Composite

variable (P : Consts) (m₀ : ℕ) (Tm : Terms d L N₁ m₁ k N ϱ)

/-- The top generating set `𝔹_k` (whole lattice). -/
noncomputable abbrev topGS (d L N₁ m₁ k : ℕ) [NeZero L] [NeZero N₁] (ϱ : ℝ) :
    GeneratingSet d L (N₁ * L ^ m₁) k ϱ := levelGS k le_rfl

/-- The pair `(ψ_k^{(j)}, h)` of (H.2): `composeData` of `𝔹_j` over `𝔹_k` (I-2 (6.2)), and `0` for
`j > k`. -/
noncomputable def composedPair (a : ℕ → ℝ) (ν : ℝ) (j : ℕ)
    (D : BgData (topGS d L N₁ m₁ k ϱ) N) : Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N :=
  if hj : j ≤ k then ((composedData (ϱ := ϱ) (m₁ := m₁) a ν hj D).Ψ,
    (composedData (ϱ := ϱ) (m₁ := m₁) a ν hj D).h) else (0, 0)

/-- **`ℰ_k(ψ_k, h) = Σ_{j=1}^k ℰ^{(j)}(ψ_k^{(j)}(ψ_k, h), h)`** (H.2) [P1 (H.2), (H.3)], with
`ψ_k^{(j)}` the minimizer of the connecting problem (P1 (2.6), (2.14)): `composeField` of I-2. -/
noncomputable def Ecomp (a : ℕ → ℝ) (ν : ℝ) (D : BgData (topGS d L N₁ m₁ k ϱ) N) : ℂ :=
  ∑ j ∈ Finset.Icc 1 k, Edens m₀ Tm j (composedPair a ν j D).1 (composedPair a ν j D).2

/-- **`ℱ_k(ψ_k, h, g) = ⟨g, φ_k⟩₁ + Σ_{j=1}^k ℱ^{(j)}(ψ_k^{(j)}(ψ_k, h), h, g)`** (H.7)
[P1 (H.9)], `φ_k = bgField` of Def-5. -/
noncomputable def Fcomp (a : ℕ → ℝ) (ν : ℝ) (D : BgData (topGS d L N₁ m₁ k ϱ) N)
    (g : Fld d L N₁ m₁ k N) : ℂ :=
  (∑ x : CTorus d L N₁ m₁ k, ∑ i, g x i * svec (topGS d L N₁ m₁ k ϱ)
      (bgField (topGS d L N₁ m₁ k ϱ) a ν D) x i) +
    ∑ j ∈ Finset.Icc 1 k, Floc m₀ Tm j (composedPair a ν j D).1 (composedPair a ν j D).2 g

/-- The `ℓ¹` norm `Σ_x |g(x)|` of a source `g`. -/
noncomputable def l1 (g : Fld d L N₁ m₁ k N) : ℝ := ∑ x, vn (g x)

end Composite

/-! ### The class on one torus: (H.1)-(H.4), (H.7) -/

/-- **The small-field class on one torus** (Def-6; SMALLFIELD §1.3, §1.6): `ρ(Ψ₀, h₀, g)` is a
density of the main-action form with effective action given by `Tm`.  Parameters: the constants `P`,
the running coefficients `β, ν, a` ((H.6)) and the constant `Ek` of `E_k |T_1^{(k)}|`.  The kernel
sequence of every background and domain is the ideal flow matched at step `k` (`aIdeal`), the mass
is `bgMass` (P5 (1.9)).

* `density` (H.1) [P1 (H.1)]: `ρ_k = χ_k exp[-β_k A_k + ℰ_k - E_k |T_1^{(k)}| + ℱ_k]`,
  `A_k` the action `action` of Def-5 at `φ_k = bgField`, `χ_k` the characteristic function of
  `Ξ_k(1, β_k^{-1/2} p(β_k))` (landed `Xi`);
* `gs_spec`: `𝔹_j(X)` is a generating set of level `j` whose first domain contains `X`;
* `analyticE`, `analyticM` (H.2), (H.4), (H.7) [P1 (H.2), (H.5), (H.9)]: analytic on
  `Ξ^c_j(𝔹_j(X); 1, ε_j)` (resp. times `{‖g‖₁ < 1}`) -- the ruling F-1;
* `rotE`, `eucE` (H.3) [P1 (H.4)], `rotM`, `eucM` (H.7): `O(N)`, `SO(N, ℂ)` and Euclidean
  invariance (equivariance for `ℳ`), termwise;
* `localE`, `localM` (H.4) [P1 (H.5)]: the term depends on `(ψ|_X, h|_X)` only;
* `boundE`, `boundM` (H.4), (H.7): `|ℰ(y, X)| ≤ E₀ e^{-κ d_j(X)}`,
  `|ℳ(x, X)| < c₉ ξ_j^{(d-2)/2+γ-α₁} e^{-κ d_j(X)}` on the domain, `d_j` the covering functional. -/
structure IsSF (P : Consts) (β ν a : ℕ → ℝ) (Tm : Terms d L N₁ m₁ k N ϱ)
    (ρ : (CTorus d L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) → (CTorus d L N₁ m₁ k → Fin N → ℝ) → ℝ)
    (Ek : ℝ) : Prop where
  density : ∀ (Ψ₀ : CTorus d L N₁ m₁ k → Fin N → ℝ) (h₀ : Fin N → ℝ)
    (g : CTorus d L N₁ m₁ k → Fin N → ℝ) (D : BgData (topGS d L N₁ m₁ k ϱ) N),
    Realizes D Ψ₀ h₀ → l1 (fun x i => (g x i : ℂ)) < 1 →
    (ρ Ψ₀ h₀ g : ℂ) =
      open Classical in
      if Xi (topGS d L N₁ m₁ k ϱ) (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) k 1
          (P.p (β k) / Real.sqrt (β k)) Ψ₀ h₀
      then Complex.exp (-(β k : ℂ) * (action (topGS d L N₁ m₁ k ϱ) (aIdeal L k (a k))
            (bgMass L k (β k) (ν k)) D
            (bgField (topGS d L N₁ m₁ k ϱ) (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) D) : ℝ) +
          Ecomp P.m₀ Tm (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) D -
          (Ek : ℂ) * (((N₁ * L ^ m₁) ^ d : ℕ) : ℂ) +
          Fcomp P.m₀ Tm (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) D (fun x i => (g x i : ℂ)))
      else 0
  gs_spec : ∀ j, 1 ≤ j → j ≤ k → ∀ X, IsPolyDom P.m₀ j X →
    X ⊆ ↑((Tm.gs j X).Ω 1) ∧ ∀ i, j < i → (Tm.gs j X).Ω i = ∅
  analyticE : ∀ j, 1 ≤ j → j ≤ k → ∀ y X, IsPolyDom P.m₀ j X → y ∈ X →
    AnalyticOnNhd ℂ (fun p : Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N => Tm.E j y X p.1 p.2)
      {p | XiDom (Tm.gs j X) (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) j (P.eps d L j)
        p.1 p.2}
  analyticM : ∀ j, 1 ≤ j → j ≤ k → ∀ x X, IsPolyDom P.m₀ j X → x ∈ X →
    AnalyticOnNhd ℂ (fun p : Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N =>
        Tm.M j x X p.1 p.2.1 p.2.2)
      {p | XiDom (Tm.gs j X) (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) j (P.eps d L j)
        p.1 p.2.1 ∧ l1 p.2.2 < 1}
  rotE : ∀ j, 1 ≤ j → j ≤ k → ∀ y X, IsPolyDom P.m₀ j X → y ∈ X → ∀ R : Matrix (Fin N) (Fin N) ℂ,
    IsRot R → ∀ Ψ h,
      XiDom (Tm.gs j X) (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) j (P.eps d L j) Ψ h →
      XiDom (Tm.gs j X) (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) j (P.eps d L j)
        (rotField R Ψ) (rotField R h) →
      Tm.E j y X (rotField R Ψ) (rotField R h) = Tm.E j y X Ψ h
  eucE : ∀ j, 1 ≤ j → j ≤ k → ∀ y X, IsPolyDom P.m₀ j X → y ∈ X →
    ∀ r ∈ latSymGroup (N₁ := N₁) (m₁ := m₁) (k := k) (d := d) L j, ∀ Ψ h,
      XiDom (Tm.gs j X) (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) j (P.eps d L j) Ψ h →
      XiDom (Tm.gs j (r '' X)) (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) j (P.eps d L j)
        (actField r Ψ) (actField r h) →
      Tm.E j (blockBase L j (r y)) (r '' X) (actField r Ψ) (actField r h) = Tm.E j y X Ψ h
  rotM : ∀ j, 1 ≤ j → j ≤ k → ∀ x X, IsPolyDom P.m₀ j X → x ∈ X → ∀ R : Matrix (Fin N) (Fin N) ℂ,
    IsRot R → ∀ Ψ h g,
      XiDom (Tm.gs j X) (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) j (P.eps d L j) Ψ h →
      XiDom (Tm.gs j X) (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) j (P.eps d L j)
        (rotField R Ψ) (rotField R h) →
      Tm.M j x X (rotField R Ψ) (rotField R h) (rotField R g) = R.mulVec (Tm.M j x X Ψ h g)
  eucM : ∀ j, 1 ≤ j → j ≤ k → ∀ x X, IsPolyDom P.m₀ j X → x ∈ X →
    ∀ r ∈ latSymGroup (N₁ := N₁) (m₁ := m₁) (k := k) (d := d) L j, ∀ Ψ h g,
      XiDom (Tm.gs j X) (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) j (P.eps d L j) Ψ h →
      XiDom (Tm.gs j (r '' X)) (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) j (P.eps d L j)
        (actField r Ψ) (actField r h) →
      Tm.M j (r x) (r '' X) (actField r Ψ) (actField r h) (actField r g) = Tm.M j x X Ψ h g
  localE : ∀ j y X Ψ Ψ' h h', (∀ x ∈ X, Ψ x = Ψ' x ∧ h x = h' x) →
    Tm.E j y X Ψ h = Tm.E j y X Ψ' h'
  localM : ∀ j x X Ψ Ψ' h h' g g', (∀ z ∈ X, Ψ z = Ψ' z ∧ h z = h' z ∧ g z = g' z) →
    Tm.M j x X Ψ h g = Tm.M j x X Ψ' h' g'
  boundE : ∀ j, 1 ≤ j → j ≤ k → ∀ y X, IsPolyDom P.m₀ j X → y ∈ X → ∀ Ψ h,
    XiDom (Tm.gs j X) (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) j (P.eps d L j) Ψ h →
    ‖Tm.E j y X Ψ h‖ ≤ P.E₀ * Real.exp (-P.κ * sizeJ P.m₀ j X)
  boundM : ∀ j, 1 ≤ j → j ≤ k → ∀ x X, IsPolyDom P.m₀ j X → x ∈ X → ∀ Ψ h g,
    XiDom (Tm.gs j X) (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) j (P.eps d L j) Ψ h →
    l1 g < 1 →
    vn (Tm.M j x X Ψ h g) <
      P.c₉ * ((L : ℝ) ^ j)⁻¹ ^ (((d : ℝ) - 2) / 2 + P.γ - P.α₁) *
        Real.exp (-P.κ * sizeJ P.m₀ j X)

/-! ### (H.5): the renormalization conditions -/

section Renorm

variable (m₀ : ℕ) (Tm : Terms d L N₁ m₁ k N ϱ)

/-- The constant field `x ↦ v`. -/
def constFld (v : Fin N → ℂ) : Fld d L N₁ m₁ k N := fun _ => v

/-- The direction "`δ_{(block x)} e_i`": a unit perturbation of `ψ` on the `j`-block of `x`
in the component `i` (the derivative `∂/∂ψ_i(x)` of a function of block-constant fields). -/
noncomputable def blockDir (L j : ℕ) (x : CTorus d L N₁ m₁ k) (i : Fin N) :
    Fld d L N₁ m₁ k N :=
  open Classical in fun z i' => if cbase (L ^ j) z = x ∧ i' = i then 1 else 0

/-- `|x|²` in the units of the level-`j` lattice, for the representative of `x` of minimal
absolute value (equal to the `ℤ^d` norm for non-winding configurations). -/
noncomputable def liftSq (L j : ℕ) (x : CTorus d L N₁ m₁ k) : ℝ :=
  ∑ μ, ((ZMod.valMinAbs (x μ) : ℝ) / (L : ℝ) ^ j) ^ 2

open Classical in
/-- **The second-moment sum of (H.5)(4)** on one torus:
`Σ_{x ∈ Λ_j} (∂²/∂ψ_{i₁}(x)∂ψ_{i₁}(0)) ℰ^{(j)}(0; ·, e_{i₀}) (e_{i₀}) · |x|²`, where
`tr[∂²ℰ/∂ψ(x)∂ψ(0) (e₂ ⊗ e₂)]` is the `(i₁, i₁)`-component. -/
noncomputable def momentSum (j : ℕ) (i₀ i₁ : Fin N) : ℂ :=
  ∑ x ∈ (Finset.univ : Finset (CTorus d L N₁ m₁ k)).filter (Aligned (L ^ j)),
    D2 (fun ψ : Fld d L N₁ m₁ k N => Eloc m₀ Tm j 0 ψ (constFld (Pi.single i₀ 1)))
      (constFld (Pi.single i₀ 1)) (blockDir L j x i₁) (blockDir L j 0 i₁) * (liftSq L j x : ℂ)

end Renorm

/-- **The renormalization conditions (H.5)** [P1 (H.6), (H.7)] at the scale `j`, for the family of
tori `N₁ ↦ Tm N₁` and the reference point `(e_{i₀}, e_{i₀})` of `(ψ, h)` (`b = ν_j h`), for all
`i₀ ≠ i₁` (equivalent to one pair by `O(N)`-invariance (H.3)):
1. `𝒱^{(j)}(e, ν_j e) = 0`;
2. `∂_b 𝒱^{(j)}(e, ν_j e) · e = 0`, written `∂_h 𝒱 · e = 0` (P1) and required for `ν_j > 0`;
3. `Σ_{y'} ∂_{ψ(y')} ℰ^{(j)}(0; e, ν_j e) · e = 0` (the derivative along the constant direction);
4. `Σ_x tr[lim_{T → ℤ^d} ∂²ℰ/∂ψ(x)∂ψ(0) (e₂ ⊗ e₂)] |x|² = 0`: the limit of the finite-torus sums
   along the family `N₁ → ∞`.
Conditions 1-3 hold on every torus.  The scale-`j` coefficient is `ν_j = ν_k s_{jk}²` (`nuIdeal`). -/
structure RenormCond (m₀ : ℕ) (k : ℕ) (νk : ℝ)
    (Tm : ∀ (N₁ : ℕ) [NeZero N₁], Terms d L N₁ m₁ k N ϱ) (j : ℕ) : Prop where
  val : ∀ (N₁ : ℕ) [NeZero N₁] (i₀ : Fin N),
    Eloc m₀ (Tm N₁) j 0 (constFld (Pi.single i₀ 1)) (constFld (Pi.single i₀ 1)) = 0
  dh : ∀ (N₁ : ℕ) [NeZero N₁] (i₀ : Fin N), 0 < nuIdeal L k νk j →
    fderiv ℂ (fun h : Fin N → ℂ => Eloc m₀ (Tm N₁) j 0 (constFld (Pi.single i₀ 1)) (constFld h))
      (Pi.single i₀ 1) (Pi.single i₀ 1) = 0
  dpsi : ∀ (N₁ : ℕ) [NeZero N₁] (i₀ : Fin N),
    fderiv ℂ (fun ψ : Fld d L N₁ m₁ k N => Eloc m₀ (Tm N₁) j 0 ψ (constFld (Pi.single i₀ 1)))
      (constFld (Pi.single i₀ 1)) (constFld (Pi.single i₀ 1)) = 0
  moment : ∀ (i₀ i₁ : Fin N), i₀ ≠ i₁ →
    Tendsto (fun n : ℕ => haveI : NeZero (n + 1) := ⟨Nat.succ_ne_zero n⟩
      momentSum m₀ (Tm (n + 1)) j i₀ i₁) atTop (𝓝 0)

/-! ### (H.6): the coefficient bounds -/

/-- **The coefficient bounds (H.6)** [P1 (H.8)] and P4 (1.4), (H.1)-(H.2), at step `k`: the
sequences `β, ν` are the running coefficients of the flow (landed `Flow.betaSeq`, `Flow.nuSeq`) for
a solution `ξ` of the step equations with `|ξ^{(n)}| ≤ (c₈/4) q^{n+1}`, `q = L^{-2γ}`,
`c₈ q ≤ 1 - q` (so `γ_n^{±1}, δ_n^{±1} < exp(c₈ Σ_{j ≤ n} L^{-2γj})`), and
`β_k > B L^{k(d-2)}`, `0 < ν_k ≤ ν̄`, `a_k ∈ [9/10 (1 - L^{-2})^{-1}, 3/2)`. -/
structure CoeffBounds (d L k : ℕ) (P : Consts) (β ν a : ℕ → ℝ) : Prop where
  flow : ∃ (ξ : ℕ → Fin 3 → ℂ) (β₀ ν₀ : ℝ),
    (∀ n, ‖ξ n‖ ≤ P.c₈ / 4 * Flow.rate (L : ℝ) P.γ ^ (n + 1)) ∧
      P.c₈ * Flow.rate (L : ℝ) P.γ ≤ 1 - Flow.rate (L : ℝ) P.γ ∧
      ∀ n, n ≤ k → ((β n : ℝ) : ℂ) = Flow.betaSeq (L : ℝ) d ξ (β₀ : ℂ) n ∧
        ((ν n : ℝ) : ℂ) = Flow.nuSeq (L : ℝ) ξ (ν₀ : ℂ) n
  beta_gt : P.B * (L : ℝ) ^ (k * (d - 2)) < β k
  nu_pos : 0 < ν k
  nu_le : ν k ≤ P.νbar
  a_ge : 9 / 10 * (1 - ((L : ℝ) ^ 2)⁻¹)⁻¹ ≤ a k
  a_lt : a k < 3 / 2

/-! ### The class of families over tori -/

/-- **Def-6: the small-field class `ℛ^sf_k(β, a, ν; B, ν̄; 𝗰)` at `λ = ∞`** (SMALLFIELD §1.3; P4
(H.1)-(H.7), P1's in brackets; the small-field part of LF Def-7 in the P5 form, §1.6): a family
over the tori `N₁ ≥ 1` of densities of the form `IsSF`, with the renormalization conditions (H.5)
at every scale `j ≤ k` and the coefficient bounds (H.6).  (CONT) is the clause `ContAtZero` on
families in `ν`. -/
structure IsSFFamily (P : Consts) (β ν a : ℕ → ℝ)
    (Tm : ∀ (N₁ : ℕ) [NeZero N₁], Terms d L N₁ m₁ k N ϱ)
    (ρ : ∀ (N₁ : ℕ) [NeZero N₁], (CTorus d L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) →
      (CTorus d L N₁ m₁ k → Fin N → ℝ) → ℝ)
    (Ek : ℕ → ℝ) : Prop where
  admissible : P.Admissible d L
  coeff : CoeffBounds d L k P β ν a
  torus : ∀ (N₁ : ℕ) [NeZero N₁], IsSF P β ν a (Tm N₁) (ρ N₁) (Ek N₁)
  renorm : ∀ j, 1 ≤ j → j ≤ k → RenormCond (d := d) (L := L) (m₁ := m₁) (N := N) (ϱ := ϱ)
    P.m₀ k (ν k) Tm j

/-! ### (CONT): continuity in `ν` down to `ν = 0` -/

/-- **Clause (CONT)** (SMALLFIELD §3.5; CORRELATIONS (F1)) for a family `ν ↦ (β(ν), a(ν), Tm(ν))`
on the torus `N₁`: for each `j ≤ k` and polymer `X`, as `ν ↓ 0` the coefficients `β_k(ν), a_k(ν)` and
the localized terms `ℰ^{(j)}_ν(y, X; ψ, b)`, `ℳ^{(j)}_ν(x, X; ψ, b, g)` in the variables
`b = ν_j h` converge uniformly on a `ν`-independent nonempty open set of `(ψ, b)` (resp.
`(ψ, b, g)`) which lies in the domain `Ξ^c_j` (in the variables `(ψ, h = b/ν_j)`) for all small `ν`.
Here `ν ↦ νv ν k` is the sequence of running mass coefficients of the family. -/
structure ContAtZero (P : Consts) (N₁ : ℕ) [NeZero N₁] (β a : ℝ → ℕ → ℝ) (νv : ℝ → ℕ → ℝ)
    (Tm : ℝ → Terms d L N₁ m₁ k N ϱ) : Prop where
  coeffs : ∃ βl al : ℝ, Tendsto (fun ν => β ν k) (𝓝[>] 0) (𝓝 βl) ∧
    Tendsto (fun ν => a ν k) (𝓝[>] 0) (𝓝 al)
  termsE : ∀ j, 1 ≤ j → j ≤ k → ∀ y X, IsPolyDom P.m₀ j X → y ∈ X →
    ∃ U : Set (Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N), IsOpen U ∧ U.Nonempty ∧
      (∀ᶠ ν in 𝓝[>] 0, ∀ p ∈ U,
        XiDom ((Tm ν).gs j X) (aIdeal L k (a ν k)) (bgMass L k (β ν k) (νv ν k)) j
          (P.eps d L j) p.1 ((nuIdeal L k (νv ν k) j)⁻¹ • p.2)) ∧
      ∃ f : Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N → ℂ,
        TendstoUniformlyOn
          (fun ν p => (Tm ν).E j y X p.1 ((nuIdeal L k (νv ν k) j)⁻¹ • p.2)) f (𝓝[>] 0) U
  termsM : ∀ j, 1 ≤ j → j ≤ k → ∀ x X, IsPolyDom P.m₀ j X → x ∈ X →
    ∃ U : Set (Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N), IsOpen U ∧ U.Nonempty ∧
      (∀ᶠ ν in 𝓝[>] 0, ∀ p ∈ U,
        XiDom ((Tm ν).gs j X) (aIdeal L k (a ν k)) (bgMass L k (β ν k) (νv ν k)) j
          (P.eps d L j) p.1 ((nuIdeal L k (νv ν k) j)⁻¹ • p.2.1) ∧ l1 p.2.2 < 1) ∧
      ∃ f : Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N → (Fin N → ℂ),
        TendstoUniformlyOn
          (fun ν p => (Tm ν).M j x X p.1 ((nuIdeal L k (νv ν k) j)⁻¹ • p.2.1) p.2.2) f
          (𝓝[>] 0) U

end Balaban.SmallField.Def6
