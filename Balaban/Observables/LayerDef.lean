/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.Def6
public import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Def-O: the observable layer on a small-field representation (OBSERVABLES.md §2.1) -- DRAFT

Draft for review.  Def-O is an extra conjunct of the small-field class (OBSERVABLES §2.4, A1): it
is stated on the carriers of the landed draft `Balaban/SmallField/Def6.lean` (`Terms`, `Fld`,
`XiDom`, `IsPolyDom`, `l1`, `Mloc`, `rotField`, `IsRot`, `fullJSymGroup`, `pavingSymGroup`, `actField`) and is a
separate structure `IsObs`, so that it can be added to `IsSF` as fields later.  The symmetry
clauses `rotM`, `eucM` (resp. `rotR`, `eucR`) are copied from `rotM`/`eucM` of `IsSF` and carry the same
symmetry repair (CLASS-RULINGS Q-A): the termwise clauses `eucM`, `eucR` are for the group
`pavingSymGroup` of the fixed paving only, the covariance of the densities `Mobs`, `Robs` (and of
`μ_j`) is for the whole-lattice group `fullJSymGroup` (`eucMloc`, `eucRloc`, `μ_euc`).

The data of the layer (`ObsTerms`, for `1 ≤ i ≤ j ≤ k`):

* `μ j x ∈ ℝ` (O1), invariant under the isometries of the level-`j` lattice, `|μ_j| ≤ β^{-1/2+ρ₁}
  L^{-jρ₀}`; `m_k = 1 - ∑_{j ≤ k} β_{j-1}^{-1/2} μ_j` (`mFactor`);
* `M j x X ψ h ∈ ℂ^N` (O2): `M^{(j)}(x, X; ψ, h)`, analytic on `Ξ^c_j(𝔹_j(X); 1, ε_j)` (the domain
  of the landed class, after the ruling F-1), `O(N)`-covariant, Euclid-invariant, local, real on
  real data, `|M^{(j)}| ≤ β^{-1/2+ρ₁} L^{-jρ₀} e^{-κ d_j(X)}`, and the normalization
  `M^{(j)}(x; h, h) = ∑_{X ∋ x} M^{(j)}(x, X; h, h) = 0` at the constant unit configurations;
* `R i j x x' X ψ h ∈ ℂ^{N × N}` (O3): `R^{ij}(x, x'; X; ψ, h)`, same domain, tensor covariance
  `R ↦ R·R·Rᵀ`, Euclid-invariant, local, real, with the operator-norm bound
  `β^{-1/2+ρ₁} L^{-jρ₀} e^{-δ₀ L^{-i} |x - x'|₁} e^{-κ d_j(X)}`.

(O4), the identification: on the support of `χ_k` (the real data `(Ψ₀, h₀) ∈ Ξ_k(1, β_k^{-1/2} p)`
with a realizing datum `D`), the whole-lattice generating function `ℱ_k = Fcomp` of Def-6 is
analytic in `g` on `‖g‖₁ < 1`, its first `g`-derivative at `0` is `⟨·, M_k⟩` and its second
`g`-derivative at `0` is `⟨·, G_k ·⟩`, with `M_k = m_k φ_k + ∑_j β_{j-1}^{-1/2} M^{(j)}` (2.4) and
`G_k = C_k + R_k` (2.5).  The Gaussian kernels `G^{(j)} = H_{j-1} C^{(j-1)} H_{j-1}^*` are not
objects of the landed Def-6; they are a parameter `Gker` of `IsObs` (the lattice Gaussian
kernels of the step), whose structure at the constant configuration is Lemma 2.1
(`Balaban/Observables/LayerStructure.lean`).

(O5) (CONT, TORUS) is not part of this file: it is the family-level clause to be added together
with `ContAtZero` and `IsSFFamily` of Def-6.
-/

@[expose] public section

namespace Balaban.Observables

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
open Balaban.SmallField.Def6 Finset

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- The exponents and the decay constant of the observable layer (OBSERVABLES §1.3):
`ρ₀`, `ρ₁` and `δ₀ = κ/M`.  The admissible ranges are those of the Lean `C1Star` (and Lemma 1.1);
see `ObsConsts.Admissible`. -/
structure ObsConsts where
  ρ₀ : ℝ
  ρ₁ : ℝ
  δ₀ : ℝ

/-- Admissible ranges: `0 < ρ₀ ≤ d - 2`, `0 < ρ₁ < 1`, `0 < δ₀` (the ranges of `C1Star`). -/
structure ObsConsts.Admissible (d : ℕ) (Q : ObsConsts) : Prop where
  ρ₀_pos : 0 < Q.ρ₀
  ρ₀_le : Q.ρ₀ ≤ (d : ℝ) - 2
  ρ₁_pos : 0 < Q.ρ₁
  ρ₁_lt : Q.ρ₁ < 1
  δ₀_pos : 0 < Q.δ₀

/-- **The data of the observable layer** on one torus: the scalars `μ_j(x)`, the vector terms
`M^{(j)}(x, X; ψ, h)` and the matrix terms `R^{ij}(x, x'; X; ψ, h)`. -/
structure ObsTerms (d L N₁ m₁ k N : ℕ) [NeZero L] [NeZero N₁] where
  μ : ℕ → CTorus d L N₁ m₁ k → ℝ
  M : ℕ → CTorus d L N₁ m₁ k → Set (CTorus d L N₁ m₁ k) → Fld d L N₁ m₁ k N →
    Fld d L N₁ m₁ k N → (Fin N → ℂ)
  R : ℕ → ℕ → CTorus d L N₁ m₁ k → CTorus d L N₁ m₁ k → Set (CTorus d L N₁ m₁ k) →
    Fld d L N₁ m₁ k N → Fld d L N₁ m₁ k N → Matrix (Fin N) (Fin N) ℂ

/-- The operator norm of a complex matrix on `ℓ²(Fin N)`. -/
noncomputable def matNorm (A : Matrix (Fin N) (Fin N) ℂ) : ℝ :=
  ‖Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℂ) A‖

theorem vn_mulVec_le (A : Matrix (Fin N) (Fin N) ℂ) (v : Fin N → ℂ) :
    vn (A.mulVec v) ≤ matNorm A * vn v := by
  have h := (Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℂ) A).le_opNorm (WithLp.toLp 2 v)
  rw [Matrix.toEuclideanCLM_toLp] at h
  exact h

/-- The `ℓ¹` distance `|x - x'|₁` of two sites of the torus, through the representatives of
minimal absolute value. -/
noncomputable def torusL1 (x x' : CTorus d L N₁ m₁ k) : ℝ :=
  ∑ μ, |(ZMod.valMinAbs (x μ - x' μ) : ℝ)|

section Sums

variable (m₀ : ℕ)

/-- The polymers of `𝒟_j` containing both `x` and `x'`. -/
def polysAt2 (j : ℕ) (x x' : CTorus d L N₁ m₁ k) : Set (Set (CTorus d L N₁ m₁ k)) :=
  {X | IsPolyDom m₀ j X ∧ x ∈ X ∧ x' ∈ X}

open Classical in
/-- **`M^{(j)}(x; ψ, h) = ∑_{X ∈ 𝒟_j, X ∋ x} M^{(j)}(x, X; ψ, h)`**. -/
noncomputable def Mobs (Ot : ObsTerms d L N₁ m₁ k N) (j : ℕ) (x : CTorus d L N₁ m₁ k)
    (ψ h : Fld d L N₁ m₁ k N) : Fin N → ℂ :=
  ∑ᶠ X ∈ polysAt m₀ j x, Ot.M j x X ψ h

open Classical in
/-- **`R^{ij}(x, x'; ψ, h) = ∑_{X ∈ 𝒟_j, X ∋ x, x'} R^{ij}(x, x'; X; ψ, h)`**. -/
noncomputable def Robs (Ot : ObsTerms d L N₁ m₁ k N) (i j : ℕ) (x x' : CTorus d L N₁ m₁ k)
    (ψ h : Fld d L N₁ m₁ k N) : Matrix (Fin N) (Fin N) ℂ :=
  ∑ᶠ X ∈ polysAt2 m₀ j x x', Ot.R i j x x' X ψ h

end Sums

/-- **`m_k(x) = 1 - ∑_{j=1}^k β_{j-1}^{-1/2} μ_j(x)`** (O1). -/
noncomputable def mFactor (β : ℕ → ℝ) (Ot : ObsTerms d L N₁ m₁ k N) (x : CTorus d L N₁ m₁ k) : ℝ :=
  1 - ∑ j ∈ Finset.Icc 1 k, (Real.sqrt (β (j - 1)))⁻¹ * Ot.μ j x

section Identification

variable (P : Consts) (β ν a : ℕ → ℝ) (Tm : Terms d L N₁ m₁ k N ϱ)
  (Ot : ObsTerms d L N₁ m₁ k N)

/-- **`M_k(x; ψ_k, h)`** (2.4): `m_k(x) φ_k(x) + ∑_{j=1}^k β_{j-1}^{-1/2} ∑_{X ∋ x}
M^{(j)}(x, X; ψ_k^{(j)}, h)`, with `φ_k = bgField` of Def-5 and `ψ_k^{(j)} = composedPair`. -/
noncomputable def Mk (D : BgData (topGS d L N₁ m₁ k ϱ) N) (x : CTorus d L N₁ m₁ k) : Fin N → ℂ :=
  fun i => (mFactor β Ot x : ℂ) *
      svec (topGS d L N₁ m₁ k ϱ) (bgField (topGS d L N₁ m₁ k ϱ) (aIdeal L k (a k))
        (bgMass L k (β k) (ν k)) D) x i +
    ∑ j ∈ Finset.Icc 1 k, ((Real.sqrt (β (j - 1)))⁻¹ : ℂ) *
      Mobs P.m₀ Ot j x (composedPair (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) j D).1
        (composedPair (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) j D).2 i

variable (Gker : ℕ → CTorus d L N₁ m₁ k → CTorus d L N₁ m₁ k → Fld d L N₁ m₁ k N →
  Fld d L N₁ m₁ k N → Matrix (Fin N) (Fin N) ℂ)

/-- **`C_k(x, x')`** (2.5): `∑_{j=1}^k β_{j-1}^{-1} m_k(x) G^{(j)}(x, x'; ψ_k^{(j)}, h) m_k(x')`. -/
noncomputable def Ck (D : BgData (topGS d L N₁ m₁ k ϱ) N) (x x' : CTorus d L N₁ m₁ k) :
    Matrix (Fin N) (Fin N) ℂ :=
  ∑ j ∈ Finset.Icc 1 k, ((β (j - 1))⁻¹ * mFactor β Ot x * mFactor β Ot x' : ℝ) •
    Gker j x x' (composedPair (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) j D).1
      (composedPair (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) j D).2

/-- **`R_k(x, x')`** (2.5): `∑_{1 ≤ i ≤ j ≤ k} β_{i-1}^{-1} ∑_{X ∋ x, x'} R^{ij}(x, x'; X;
ψ_k^{(j)}, h)`. -/
noncomputable def Rk (D : BgData (topGS d L N₁ m₁ k ϱ) N) (x x' : CTorus d L N₁ m₁ k) :
    Matrix (Fin N) (Fin N) ℂ :=
  ∑ i ∈ Finset.Icc 1 k, ∑ j ∈ Finset.Icc i k, ((β (i - 1))⁻¹ : ℝ) •
    Robs P.m₀ Ot i j x x' (composedPair (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) j D).1
      (composedPair (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) j D).2

/-- **`G_k = C_k + R_k`** (2.5). -/
noncomputable def Gk (D : BgData (topGS d L N₁ m₁ k ϱ) N) (x x' : CTorus d L N₁ m₁ k) :
    Matrix (Fin N) (Fin N) ℂ :=
  Ck β ν a Ot Gker D x x' + Rk P β ν a Ot D x x'

end Identification

/-- **Def-O: the observable layer on a small-field representation** (OBSERVABLES §2.1; DRAFT).
For the constants `P` of Def-6, the observable constants `Q` (`ρ₀, ρ₁, δ₀`), the running
coefficients `β, ν, a`, the localized data `Tm` of Def-6, the data `Ot` of the layer and the
Gaussian kernels `Gker`.  All clauses are for the scales `1 ≤ i ≤ j ≤ k`, polymers `X ∈ 𝒟_j` and
sites `x, x' ∈ X`, on the domains `Ξ^c_j(𝔹_j(X); 1, ε_j)` of the class.

* `μ_euc`, `μ_bound` (O1); `analyticM`, `rotM`, `eucM`, `eucMloc`, `localM`, `realM`, `boundM`, `normM` (O2);
  `analyticR`, `rotR`, `eucR`, `eucRloc`, `localR`, `realR`, `boundR` (O3); `ident` (O4).
* The symmetry clauses have the form of `IsSF.rotM`, `IsSF.eucM`. -/
structure IsObs (P : Consts) (Q : ObsConsts) (β ν a : ℕ → ℝ) (Tm : Terms d L N₁ m₁ k N ϱ)
    (Ot : ObsTerms d L N₁ m₁ k N)
    (Gker : ℕ → CTorus d L N₁ m₁ k → CTorus d L N₁ m₁ k → Fld d L N₁ m₁ k N →
      Fld d L N₁ m₁ k N → Matrix (Fin N) (Fin N) ℂ) : Prop where
  /-- (O1): `μ_j` is invariant under the isometries of the level-`j` lattice (hence
  `L^j`-periodic). -/
  μ_euc : ∀ j, 1 ≤ j → j ≤ k →
    ∀ r ∈ fullJSymGroup (N₁ := N₁) (m₁ := m₁) (k := k) (d := d) L j, ∀ x, Ot.μ j (r x) = Ot.μ j x
  /-- (O1): `|μ_j(x)| ≤ β^{-1/2+ρ₁} L^{-jρ₀}`. -/
  μ_bound : ∀ j, 1 ≤ j → j ≤ k → ∀ x, |Ot.μ j x| ≤
    (β 0) ^ (-(1 / 2 : ℝ) + Q.ρ₁) * (L : ℝ) ^ (-((j : ℝ) * Q.ρ₀))
  analyticM : ∀ j, 1 ≤ j → j ≤ k → ∀ x X, IsPolyDom P.m₀ j X → x ∈ X →
    AnalyticOnNhd ℂ (fun p : Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N => Ot.M j x X p.1 p.2)
      {p | XiDom (Tm.gs j X) (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) j (P.eps d L j)
        p.1 p.2}
  analyticR : ∀ i j, 1 ≤ i → i ≤ j → j ≤ k → ∀ x x' X, IsPolyDom P.m₀ j X → x ∈ X → x' ∈ X →
    ∀ a₁ a₂ : Fin N,
    AnalyticOnNhd ℂ
      (fun p : Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N => Ot.R i j x x' X p.1 p.2 a₁ a₂)
      {p | XiDom (Tm.gs j X) (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) j (P.eps d L j)
        p.1 p.2}
  rotM : ∀ j, 1 ≤ j → j ≤ k → ∀ x X, IsPolyDom P.m₀ j X → x ∈ X → ∀ R : Matrix (Fin N) (Fin N) ℂ,
    IsRot R → ∀ Ψ h,
      XiDom (Tm.gs j X) (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) j (P.eps d L j) Ψ h →
      XiDom (Tm.gs j X) (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) j (P.eps d L j)
        (rotField R Ψ) (rotField R h) →
      Ot.M j x X (rotField R Ψ) (rotField R h) = R.mulVec (Ot.M j x X Ψ h)
  rotR : ∀ i j, 1 ≤ i → i ≤ j → j ≤ k → ∀ x x' X, IsPolyDom P.m₀ j X → x ∈ X → x' ∈ X →
    ∀ R : Matrix (Fin N) (Fin N) ℂ, IsRot R → ∀ Ψ h,
      XiDom (Tm.gs j X) (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) j (P.eps d L j) Ψ h →
      XiDom (Tm.gs j X) (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) j (P.eps d L j)
        (rotField R Ψ) (rotField R h) →
      Ot.R i j x x' X (rotField R Ψ) (rotField R h) = R * Ot.R i j x x' X Ψ h * R.transpose
  eucM : ∀ j, 1 ≤ j → j ≤ k → ∀ x X, IsPolyDom P.m₀ j X → x ∈ X →
    ∀ r ∈ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k) (d := d) L P.m₀ j, ∀ Ψ h,
      XiDom (Tm.gs j X) (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) j (P.eps d L j) Ψ h →
      XiDom (Tm.gs j (r '' X)) (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) j (P.eps d L j)
        (actField r Ψ) (actField r h) →
      Ot.M j (r x) (r '' X) (actField r Ψ) (actField r h) = Ot.M j x X Ψ h
  eucR : ∀ i j, 1 ≤ i → i ≤ j → j ≤ k → ∀ x x' X, IsPolyDom P.m₀ j X → x ∈ X → x' ∈ X →
    ∀ r ∈ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k) (d := d) L P.m₀ j, ∀ Ψ h,
      XiDom (Tm.gs j X) (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) j (P.eps d L j) Ψ h →
      XiDom (Tm.gs j (r '' X)) (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) j (P.eps d L j)
        (actField r Ψ) (actField r h) →
      Ot.R i j (r x) (r x') (r '' X) (actField r Ψ) (actField r h) = Ot.R i j x x' X Ψ h
  eucMloc : ∀ j, 1 ≤ j → ∀ hjk : j ≤ k, ∀ x,
    ∀ r ∈ fullJSymGroup (N₁ := N₁) (m₁ := m₁) (k := k) (d := d) L j, ∀ Ψ h,
      XiDom (levelGS (ϱ := ϱ) (N₁ := N₁) (m₁ := m₁) j hjk) (aIdeal L k (a k))
        (bgMass L k (β k) (ν k)) j (P.eps d L j) Ψ h →
      XiDom (levelGS (ϱ := ϱ) (N₁ := N₁) (m₁ := m₁) j hjk) (aIdeal L k (a k))
        (bgMass L k (β k) (ν k)) j (P.eps d L j) (actField r Ψ) (actField r h) →
      Mobs P.m₀ Ot j (r x) (actField r Ψ) (actField r h) = Mobs P.m₀ Ot j x Ψ h
  eucRloc : ∀ i j, 1 ≤ i → i ≤ j → ∀ hjk : j ≤ k, ∀ x x',
    ∀ r ∈ fullJSymGroup (N₁ := N₁) (m₁ := m₁) (k := k) (d := d) L j, ∀ Ψ h,
      XiDom (levelGS (ϱ := ϱ) (N₁ := N₁) (m₁ := m₁) j hjk) (aIdeal L k (a k))
        (bgMass L k (β k) (ν k)) j (P.eps d L j) Ψ h →
      XiDom (levelGS (ϱ := ϱ) (N₁ := N₁) (m₁ := m₁) j hjk) (aIdeal L k (a k))
        (bgMass L k (β k) (ν k)) j (P.eps d L j) (actField r Ψ) (actField r h) →
      Robs P.m₀ Ot i j (r x) (r x') (actField r Ψ) (actField r h) = Robs P.m₀ Ot i j x x' Ψ h
  localM : ∀ j x X Ψ Ψ' h h', (∀ z ∈ X, Ψ z = Ψ' z ∧ h z = h' z) →
    Ot.M j x X Ψ h = Ot.M j x X Ψ' h'
  localR : ∀ i j x x' X Ψ Ψ' h h', (∀ z ∈ X, Ψ z = Ψ' z ∧ h z = h' z) →
    Ot.R i j x x' X Ψ h = Ot.R i j x x' X Ψ' h'
  /-- (O2): `M^{(j)}` is real on real data. -/
  realM : ∀ j, 1 ≤ j → j ≤ k → ∀ x X, IsPolyDom P.m₀ j X → x ∈ X → ∀ Ψ h,
    XiDom (Tm.gs j X) (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) j (P.eps d L j) Ψ h →
    (∀ z i, (Ψ z i).im = 0) → (∀ z i, (h z i).im = 0) → ∀ i, (Ot.M j x X Ψ h i).im = 0
  /-- (O3): `R^{ij}` is real on real data. -/
  realR : ∀ i j, 1 ≤ i → i ≤ j → j ≤ k → ∀ x x' X, IsPolyDom P.m₀ j X → x ∈ X → x' ∈ X →
    ∀ Ψ h,
    XiDom (Tm.gs j X) (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) j (P.eps d L j) Ψ h →
    (∀ z i, (Ψ z i).im = 0) → (∀ z i, (h z i).im = 0) → ∀ a₁ a₂ : Fin N, (Ot.R i j x x' X Ψ h a₁ a₂).im = 0
  /-- (2.1): `|M^{(j)}| ≤ β^{-1/2+ρ₁} L^{-jρ₀} e^{-κ d_j(X)}`. -/
  boundM : ∀ j, 1 ≤ j → j ≤ k → ∀ x X, IsPolyDom P.m₀ j X → x ∈ X → ∀ Ψ h,
    XiDom (Tm.gs j X) (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) j (P.eps d L j) Ψ h →
    vn (Ot.M j x X Ψ h) ≤ (β 0) ^ (-(1 / 2 : ℝ) + Q.ρ₁) * (L : ℝ) ^ (-((j : ℝ) * Q.ρ₀)) *
      Real.exp (-P.κ * sizeJ P.m₀ j X)
  /-- (2.2): `|R^{ij}| ≤ β^{-1/2+ρ₁} L^{-jρ₀} e^{-δ₀ L^{-i}|x-x'|₁} e^{-κ d_j(X)}`, in the
  operator norm. -/
  boundR : ∀ i j, 1 ≤ i → i ≤ j → j ≤ k → ∀ x x' X, IsPolyDom P.m₀ j X → x ∈ X → x' ∈ X →
    ∀ Ψ h,
    XiDom (Tm.gs j X) (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) j (P.eps d L j) Ψ h →
    matNorm (Ot.R i j x x' X Ψ h) ≤ (β 0) ^ (-(1 / 2 : ℝ) + Q.ρ₁) *
      (L : ℝ) ^ (-((j : ℝ) * Q.ρ₀)) *
      Real.exp (-(Q.δ₀ * ((L : ℝ) ^ i)⁻¹ * torusL1 x x')) * Real.exp (-P.κ * sizeJ P.m₀ j X)
  /-- (2.1), the normalization (2.7): `M^{(j)}(x; h, h) = 0` at the constant unit configurations
  `ψ ≡ h`. -/
  normM : ∀ j, 1 ≤ j → j ≤ k → ∀ x, ∀ v : Fin N → ℝ, v ⬝ᵥ v = 1 →
    Mobs P.m₀ Ot j x (constFld (fun i => (v i : ℂ))) (constFld (fun i => (v i : ℂ))) = 0
  /-- (O4), (2.3)-(2.5): the identification of the first two `g`-derivatives of the whole-lattice
  generating function `ℱ_k` at `g = 0`, on the support of `χ_k`. -/
  ident : ∀ (Ψ₀ : CTorus d L N₁ m₁ k → Fin N → ℝ) (h₀ : Fin N → ℝ)
    (D : BgData (topGS d L N₁ m₁ k ϱ) N), Realizes D Ψ₀ h₀ →
    Xi (topGS d L N₁ m₁ k ϱ) (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) k 1
      (P.p (β k) / Real.sqrt (β k)) Ψ₀ h₀ →
    AnalyticOnNhd ℂ (Fcomp P.m₀ Tm (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) D)
        {g | l1 g < 1} ∧
      (∀ u : Fld d L N₁ m₁ k N,
        fderiv ℂ (Fcomp P.m₀ Tm (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) D) 0 u =
          ∑ x, ∑ i, u x i * Mk P β ν a Ot D x i) ∧
      ∀ u v : Fld d L N₁ m₁ k N,
        D2 (Fcomp P.m₀ Tm (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) D) 0 u v =
          ∑ x, ∑ x', ∑ i, ∑ i', u x i * Gk P β ν a Ot Gker D x x' i i' * v x' i'

/-- A small-field representation carrying an observable layer: the conjunction of Def-6's `IsSF`
and Def-O. -/
structure IsSFObs (P : Consts) (Q : ObsConsts) (β ν a : ℕ → ℝ) (Tm : Terms d L N₁ m₁ k N ϱ)
    (ρ : (CTorus d L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) → (CTorus d L N₁ m₁ k → Fin N → ℝ) → ℝ)
    (Ek : ℝ) (Ot : ObsTerms d L N₁ m₁ k N)
    (Gker : ℕ → CTorus d L N₁ m₁ k → CTorus d L N₁ m₁ k → Fld d L N₁ m₁ k N →
      Fld d L N₁ m₁ k N → Matrix (Fin N) (Fin N) ℂ) : Prop where
  sf : IsSF P β ν a Tm ρ Ek
  obs : IsObs P Q β ν a Tm Ot Gker

end Balaban.Observables
