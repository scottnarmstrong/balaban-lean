/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Observables.LayerDef
public import Balaban.SmallField.Def6v2Source
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Def-O v2: the observable layer with a regime and a field domain -- DRAFT

**Draft, pending Roland's answer to Q13** (`notes/phase1/Q13-ANSWER-astra.md`).  Second version of
`Observables.IsObs` implementing `notes/phase1/CLASS-RULINGS-2.md` (items 2, 3, 4); the landed
`IsObs` is unchanged.

* `Mk2`, `Ck2`, `Rk2`, `Gk2`: the objects (2.4), (2.5) of OBSERVABLES §2.1 with the **background
  mass** `μ` as a parameter (item 2: the solver mass is `bgMassAt(k₀, k, ν_k)`);
* `IsObs2`: the clauses (O1)-(O4) of `IsObs` with every `XiDom … (bgMass …)` replaced by the field
  domain `Dom` (item 4: "replace every `XiDom` used for … observable `analyticM/R`, `boundM/R`,
  rotation, locality and realness by this restricted domain, preserving the birth-level tag `j`"),
  the normalization (2.7) at the physical unit fields `Dom.phys` (the axial normalization), and the
  identification (O4) on the support of `χ_k` at the background mass of the regime and the physical
  fields.  The complex field line of a constant `h` is finite on the pinned domain, so the Liouville
  argument of `Mobs_const_eq_zero_massFree` does not apply (item 4);
* `ObsSourceTerms`, `ObsSourceForm`: the physical-source form `M^{obs}_j(x, X; Ψ, h) =
  M̃^{obs}_j(x, X; Ψ, ν_j h)`, `R^{obs}_{ij} = R̃^{obs}_{ij}(·, ν_j h)` (item 3), the bounds on the
  restricted `b`-domain and the **mass-weighted reference derivative** `dbM`
  (`ν_j |D_b M̃(e, ν_j e)[u]| ≤ C_D B_X |u|`; item 4: "a Cauchy estimate on this finite chart using
  the `ν_j`-weighted `b` derivative and the axial normalization"; its constant-part gain is an
  explicit input until proved for the physical terms).  At `ν_j = 0` the factorization says that
  the terms do not depend on `h` (`ObsSourceForm.indepM_of_nu_zero`).
-/

@[expose] public section

namespace Balaban.Observables

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
open Balaban.SmallField.Def6 Balaban.SmallField.Def6v2 Finset

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

section Identification

variable (P : Consts) (β a : ℕ → ℝ) (μ : ℝ) (Ot : ObsTerms d L N₁ m₁ k N)

/-- **`M_k(x; ψ_k, h)`** (2.4) with the background mass `μ`:
`m_k(x) φ_k^μ(x) + ∑_j β_{j-1}^{-1/2} ∑_{X ∋ x} M^{(j)}(x, X; ψ_k^{(j)}, h)`. -/
noncomputable def Mk2 (D : BgData (topGS d L N₁ m₁ k ϱ) N) (x : CTorus d L N₁ m₁ k) :
    Fin N → ℂ :=
  fun i => (mFactor β Ot x : ℂ) *
      svec (topGS d L N₁ m₁ k ϱ) (bgField (topGS d L N₁ m₁ k ϱ) (aIdeal L k (a k)) μ D) x i +
    ∑ j ∈ Finset.Icc 1 k, (((Real.sqrt (β (j - 1)))⁻¹ : ℝ) : ℂ) *
      Mobs P.m₀ Ot j x (composedPair (aIdeal L k (a k)) μ j D).1
        (composedPair (aIdeal L k (a k)) μ j D).2 i

variable (Gker : ℕ → CTorus d L N₁ m₁ k → CTorus d L N₁ m₁ k → Fld d L N₁ m₁ k N →
  Fld d L N₁ m₁ k N → Matrix (Fin N) (Fin N) ℂ)

/-- **`C_k(x, x')`** (2.5) with the background mass `μ`. -/
noncomputable def Ck2 (D : BgData (topGS d L N₁ m₁ k ϱ) N) (x x' : CTorus d L N₁ m₁ k) :
    Matrix (Fin N) (Fin N) ℂ :=
  ∑ j ∈ Finset.Icc 1 k, ((β (j - 1))⁻¹ * mFactor β Ot x * mFactor β Ot x' : ℝ) •
    Gker j x x' (composedPair (aIdeal L k (a k)) μ j D).1
      (composedPair (aIdeal L k (a k)) μ j D).2

/-- **`R_k(x, x')`** (2.5) with the background mass `μ`. -/
noncomputable def Rk2 (D : BgData (topGS d L N₁ m₁ k ϱ) N) (x x' : CTorus d L N₁ m₁ k) :
    Matrix (Fin N) (Fin N) ℂ :=
  ∑ i ∈ Finset.Icc 1 k, ∑ j ∈ Finset.Icc i k, ((β (i - 1))⁻¹ : ℝ) •
    Robs P.m₀ Ot i j x x' (composedPair (aIdeal L k (a k)) μ j D).1
      (composedPair (aIdeal L k (a k)) μ j D).2

/-- **`G_k = C_k + R_k`** (2.5) with the background mass `μ`. -/
noncomputable def Gk2 (D : BgData (topGS d L N₁ m₁ k ϱ) N) (x x' : CTorus d L N₁ m₁ k) :
    Matrix (Fin N) (Fin N) ℂ :=
  Ck2 β a μ Ot Gker D x x' + Rk2 P β a μ Ot D x x'

end Identification

/-- **Def-O v2: the observable layer on a small-field representation, second version**
(OBSERVABLES §2.1; CLASS-RULINGS-2 items 2, 3, 4).  The clauses of `IsObs` on the field domain
`Dom` (the pinned domain for the Q13 route), with the regime `Rg`: `μ_euc`, `μ_bound` (O1);
`analyticM`, `rotM`, `eucM`, `eucMloc`, `localM`, `realM`, `boundM`, `normM` (O2); `analyticR`,
`rotR`, `eucR`, `eucRloc`, `localR`, `realR`, `boundR` (O3); `ident` (O4).  Draft pending Roland's
answer to Q13. -/
structure IsObs2 (P : Consts) (Q : ObsConsts) (Rg : Regime L) (β a : ℕ → ℝ)
    (Dom : FieldDom d L N₁ m₁ k N ϱ) (Tm : Terms d L N₁ m₁ k N ϱ)
    (Ot : ObsTerms d L N₁ m₁ k N)
    (Gker : ℕ → CTorus d L N₁ m₁ k → CTorus d L N₁ m₁ k → Fld d L N₁ m₁ k N →
      Fld d L N₁ m₁ k N → Matrix (Fin N) (Fin N) ℂ) : Prop where
  μ_euc : ∀ j, 1 ≤ j → j ≤ k →
    ∀ r ∈ fullJSymGroup (N₁ := N₁) (m₁ := m₁) (k := k) (d := d) L j, ∀ x, Ot.μ j (r x) = Ot.μ j x
  μ_bound : ∀ j, 1 ≤ j → j ≤ k → ∀ x, |Ot.μ j x| ≤
    (β 0) ^ (-(1 / 2 : ℝ) + Q.ρ₁) * (L : ℝ) ^ (-((j : ℝ) * Q.ρ₀))
  analyticM : ∀ j, 1 ≤ j → j ≤ k → ∀ x X, IsPolyDom P.m₀ j X → x ∈ X →
    AnalyticOnNhd ℂ (fun p : Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N => Ot.M j x X p.1 p.2)
      {p | Dom.dom j (Tm.gs j X) p.1 p.2}
  analyticR : ∀ i j, 1 ≤ i → i ≤ j → j ≤ k → ∀ x x' X, IsPolyDom P.m₀ j X → x ∈ X → x' ∈ X →
    ∀ a₁ a₂ : Fin N,
    AnalyticOnNhd ℂ
      (fun p : Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N => Ot.R i j x x' X p.1 p.2 a₁ a₂)
      {p | Dom.dom j (Tm.gs j X) p.1 p.2}
  rotM : ∀ j, 1 ≤ j → j ≤ k → ∀ x X, IsPolyDom P.m₀ j X → x ∈ X → ∀ R : Matrix (Fin N) (Fin N) ℂ,
    IsRot R → ∀ Ψ h, Dom.dom j (Tm.gs j X) Ψ h →
      Dom.dom j (Tm.gs j X) (rotField R Ψ) (rotField R h) →
      Ot.M j x X (rotField R Ψ) (rotField R h) = R.mulVec (Ot.M j x X Ψ h)
  rotR : ∀ i j, 1 ≤ i → i ≤ j → j ≤ k → ∀ x x' X, IsPolyDom P.m₀ j X → x ∈ X → x' ∈ X →
    ∀ R : Matrix (Fin N) (Fin N) ℂ, IsRot R → ∀ Ψ h, Dom.dom j (Tm.gs j X) Ψ h →
      Dom.dom j (Tm.gs j X) (rotField R Ψ) (rotField R h) →
      Ot.R i j x x' X (rotField R Ψ) (rotField R h) = R * Ot.R i j x x' X Ψ h * R.transpose
  eucM : ∀ j, 1 ≤ j → j ≤ k → ∀ x X, IsPolyDom P.m₀ j X → x ∈ X →
    ∀ r ∈ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k) (d := d) L P.m₀ j, ∀ Ψ h,
      Dom.dom j (Tm.gs j X) Ψ h → Dom.dom j (Tm.gs j (r '' X)) (actField r Ψ) (actField r h) →
      Ot.M j (r x) (r '' X) (actField r Ψ) (actField r h) = Ot.M j x X Ψ h
  eucR : ∀ i j, 1 ≤ i → i ≤ j → j ≤ k → ∀ x x' X, IsPolyDom P.m₀ j X → x ∈ X → x' ∈ X →
    ∀ r ∈ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k) (d := d) L P.m₀ j, ∀ Ψ h,
      Dom.dom j (Tm.gs j X) Ψ h → Dom.dom j (Tm.gs j (r '' X)) (actField r Ψ) (actField r h) →
      Ot.R i j (r x) (r x') (r '' X) (actField r Ψ) (actField r h) = Ot.R i j x x' X Ψ h
  eucMloc : ∀ j, 1 ≤ j → ∀ hjk : j ≤ k, ∀ x,
    ∀ r ∈ fullJSymGroup (N₁ := N₁) (m₁ := m₁) (k := k) (d := d) L j, ∀ Ψ h,
      Dom.dom j (levelGS (ϱ := ϱ) (N₁ := N₁) (m₁ := m₁) j hjk) Ψ h →
      Dom.dom j (levelGS (ϱ := ϱ) (N₁ := N₁) (m₁ := m₁) j hjk) (actField r Ψ) (actField r h) →
      Mobs P.m₀ Ot j (r x) (actField r Ψ) (actField r h) = Mobs P.m₀ Ot j x Ψ h
  eucRloc : ∀ i j, 1 ≤ i → i ≤ j → ∀ hjk : j ≤ k, ∀ x x',
    ∀ r ∈ fullJSymGroup (N₁ := N₁) (m₁ := m₁) (k := k) (d := d) L j, ∀ Ψ h,
      Dom.dom j (levelGS (ϱ := ϱ) (N₁ := N₁) (m₁ := m₁) j hjk) Ψ h →
      Dom.dom j (levelGS (ϱ := ϱ) (N₁ := N₁) (m₁ := m₁) j hjk) (actField r Ψ) (actField r h) →
      Robs P.m₀ Ot i j (r x) (r x') (actField r Ψ) (actField r h) = Robs P.m₀ Ot i j x x' Ψ h
  localM : ∀ j x X Ψ Ψ' h h', (∀ z ∈ X, Ψ z = Ψ' z ∧ h z = h' z) →
    Ot.M j x X Ψ h = Ot.M j x X Ψ' h'
  localR : ∀ i j x x' X Ψ Ψ' h h', (∀ z ∈ X, Ψ z = Ψ' z ∧ h z = h' z) →
    Ot.R i j x x' X Ψ h = Ot.R i j x x' X Ψ' h'
  realM : ∀ j, 1 ≤ j → j ≤ k → ∀ x X, IsPolyDom P.m₀ j X → x ∈ X → ∀ Ψ h,
    Dom.dom j (Tm.gs j X) Ψ h →
    (∀ z i, (Ψ z i).im = 0) → (∀ z i, (h z i).im = 0) → ∀ i, (Ot.M j x X Ψ h i).im = 0
  realR : ∀ i j, 1 ≤ i → i ≤ j → j ≤ k → ∀ x x' X, IsPolyDom P.m₀ j X → x ∈ X → x' ∈ X →
    ∀ Ψ h, Dom.dom j (Tm.gs j X) Ψ h →
    (∀ z i, (Ψ z i).im = 0) → (∀ z i, (h z i).im = 0) →
      ∀ a₁ a₂ : Fin N, (Ot.R i j x x' X Ψ h a₁ a₂).im = 0
  boundM : ∀ j, 1 ≤ j → j ≤ k → ∀ x X, IsPolyDom P.m₀ j X → x ∈ X → ∀ Ψ h,
    Dom.dom j (Tm.gs j X) Ψ h →
    vn (Ot.M j x X Ψ h) ≤ (β 0) ^ (-(1 / 2 : ℝ) + Q.ρ₁) * (L : ℝ) ^ (-((j : ℝ) * Q.ρ₀)) *
      Real.exp (-P.κ * sizeJ P.m₀ j X)
  boundR : ∀ i j, 1 ≤ i → i ≤ j → j ≤ k → ∀ x x' X, IsPolyDom P.m₀ j X → x ∈ X → x' ∈ X →
    ∀ Ψ h, Dom.dom j (Tm.gs j X) Ψ h →
    matNorm (Ot.R i j x x' X Ψ h) ≤ (β 0) ^ (-(1 / 2 : ℝ) + Q.ρ₁) *
      (L : ℝ) ^ (-((j : ℝ) * Q.ρ₀)) *
      Real.exp (-(Q.δ₀ * ((L : ℝ) ^ i)⁻¹ * torusL1 x x')) * Real.exp (-P.κ * sizeJ P.m₀ j X)
  /-- (2.7), the axial normalization: `M^{(j)}(x; h, h) = 0` at the constant physical unit
  configurations `ψ ≡ h` -/
  normM : ∀ j, 1 ≤ j → j ≤ k → ∀ x, ∀ v : Fin N → ℝ, v ∈ Dom.phys → v ⬝ᵥ v = 1 →
    Mobs P.m₀ Ot j x (constFld (fun i => (v i : ℂ))) (constFld (fun i => (v i : ℂ))) = 0
  /-- (O4), on the support of `χ_k` (background mass of the regime) at the physical fields -/
  ident : ∀ (Ψ₀ : CTorus d L N₁ m₁ k → Fin N → ℝ) (h₀ : Fin N → ℝ)
    (D : BgData (topGS d L N₁ m₁ k ϱ) N), h₀ ∈ Dom.phys → Realizes D Ψ₀ h₀ →
    Xi (topGS d L N₁ m₁ k ϱ) (aIdeal L k (a k)) (Rg.bgMass k) k 1
      (P.p (β k) / Real.sqrt (β k)) Ψ₀ h₀ →
    AnalyticOnNhd ℂ (Fcomp P.m₀ Tm (aIdeal L k (a k)) (Rg.bgMass k) D)
        {g | Def6.l1 g < 1} ∧
      (∀ u : Fld d L N₁ m₁ k N,
        fderiv ℂ (Fcomp P.m₀ Tm (aIdeal L k (a k)) (Rg.bgMass k) D) 0 u =
          ∑ x, ∑ i, u x i * Mk2 P β a (Rg.bgMass k) Ot D x i) ∧
      ∀ u v : Fld d L N₁ m₁ k N,
        D2 (Fcomp P.m₀ Tm (aIdeal L k (a k)) (Rg.bgMass k) D) 0 u v =
          ∑ x, ∑ x', ∑ i, ∑ i', u x i * Gk2 P β a (Rg.bgMass k) Ot Gker D x x' i i' * v x' i'

/-- A small-field representation of the second version carrying an observable layer. -/
structure IsSFObs2 (P : Consts) (Q : ObsConsts) (Rg : Regime L) (β a : ℕ → ℝ)
    (Dom : FieldDom d L N₁ m₁ k N ϱ) (Tm : Terms d L N₁ m₁ k N ϱ)
    (ρ : (CTorus d L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) → (CTorus d L N₁ m₁ k → Fin N → ℝ) → ℝ)
    (Ek : ℝ) (Ot : ObsTerms d L N₁ m₁ k N)
    (Gker : ℕ → CTorus d L N₁ m₁ k → CTorus d L N₁ m₁ k → Fld d L N₁ m₁ k N →
      Fld d L N₁ m₁ k N → Matrix (Fin N) (Fin N) ℂ) : Prop where
  sf : IsSF2 P Rg β a Dom Tm ρ Ek
  obs : IsObs2 P Q Rg β a Dom Tm Ot Gker

/-! ### The physical-source form of the observable terms -/

/-- **The source-form data of the observable terms** (CLASS-RULINGS-2 item 3):
`M̃^{obs}_j(x, X; Ψ, b)` and `R̃^{obs}_{ij}(x, x', X; Ψ, b)`, `b = ν_j h`. -/
structure ObsSourceTerms (d L N₁ m₁ k N : ℕ) where
  /-- `M̃^{obs}_j(x, X; Ψ, b)` -/
  M : ℕ → CTorus d L N₁ m₁ k → Set (CTorus d L N₁ m₁ k) → Fld d L N₁ m₁ k N →
    Fld d L N₁ m₁ k N → (Fin N → ℂ)
  /-- `R̃^{obs}_{ij}(x, x', X; Ψ, b)` -/
  R : ℕ → ℕ → CTorus d L N₁ m₁ k → CTorus d L N₁ m₁ k → Set (CTorus d L N₁ m₁ k) →
    Fld d L N₁ m₁ k N → Fld d L N₁ m₁ k N → Matrix (Fin N) (Fin N) ℂ

/-- **`ObsSourceForm`: the physical-source form of the observable terms** (CLASS-RULINGS-2 items
3, 4), for the masses `ν` (`ν_j = nuIdeal L k ν_k j`), the field domain `Dom`, the reference
direction `e = e_{i₀}` and the derivative constant `C_D`:
* `factM`, `factR`: `M^{obs}_j(x, X; Ψ, h) = M̃^{obs}_j(x, X; Ψ, ν_j h)` and the same for `R^{obs}`
  on the field domain (at `ν_j = 0`: independence of `h`);
* `boundM`, `boundR`: the bounds (2.1), (2.2) on the restricted `b`-domain `srcDom`;
* `dbM`: **the mass-weighted reference derivative**
  `ν_j |D_b M̃^{obs}_j(x, X; e, ν_j e)[u]| ≤ C_D β^{-1/2+ρ₁} L^{-jρ₀} e^{-κ d_j(X)} |u|`, the input of
  the constant-part bound that replaces the mass-free branch of `ImprovedConst` (item 4).
Draft pending Roland's answer to Q13. -/
structure ObsSourceForm (P : Consts) (Q : ObsConsts) (β ν : ℕ → ℝ)
    (Dom : FieldDom d L N₁ m₁ k N ϱ) (Tm : Terms d L N₁ m₁ k N ϱ)
    (Ot : ObsTerms d L N₁ m₁ k N) (St : ObsSourceTerms d L N₁ m₁ k N) (i₀ : Fin N) (CD : ℝ) :
    Prop where
  factM : ∀ j, 1 ≤ j → j ≤ k → ∀ x X, IsPolyDom P.m₀ j X → x ∈ X → ∀ Ψ h,
    Dom.dom j (Tm.gs j X) Ψ h →
      Ot.M j x X Ψ h = St.M j x X Ψ ((nuIdeal L k (ν k) j : ℂ) • h)
  factR : ∀ i j, 1 ≤ i → i ≤ j → j ≤ k → ∀ x x' X, IsPolyDom P.m₀ j X → x ∈ X → x' ∈ X → ∀ Ψ h,
    Dom.dom j (Tm.gs j X) Ψ h →
      Ot.R i j x x' X Ψ h = St.R i j x x' X Ψ ((nuIdeal L k (ν k) j : ℂ) • h)
  boundM : ∀ j, 1 ≤ j → j ≤ k → ∀ x X, IsPolyDom P.m₀ j X → x ∈ X → ∀ Ψ b,
    srcDom Dom (nuIdeal L k (ν k) j) j (Tm.gs j X) Ψ b →
      vn (St.M j x X Ψ b) ≤ (β 0) ^ (-(1 / 2 : ℝ) + Q.ρ₁) * (L : ℝ) ^ (-((j : ℝ) * Q.ρ₀)) *
        Real.exp (-P.κ * sizeJ P.m₀ j X)
  boundR : ∀ i j, 1 ≤ i → i ≤ j → j ≤ k → ∀ x x' X, IsPolyDom P.m₀ j X → x ∈ X → x' ∈ X →
    ∀ Ψ b, srcDom Dom (nuIdeal L k (ν k) j) j (Tm.gs j X) Ψ b →
      matNorm (St.R i j x x' X Ψ b) ≤ (β 0) ^ (-(1 / 2 : ℝ) + Q.ρ₁) *
        (L : ℝ) ^ (-((j : ℝ) * Q.ρ₀)) *
        Real.exp (-(Q.δ₀ * ((L : ℝ) ^ i)⁻¹ * torusL1 x x')) * Real.exp (-P.κ * sizeJ P.m₀ j X)
  dbM : ∀ j, 1 ≤ j → j ≤ k → ∀ x X, IsPolyDom P.m₀ j X → x ∈ X → ∀ u : Fin N → ℂ,
    nuIdeal L k (ν k) j *
        vn (fderiv ℂ (fun b : Fin N → ℂ => St.M j x X (constFld (Pi.single i₀ 1)) (constFld b))
          ((nuIdeal L k (ν k) j : ℂ) • Pi.single i₀ 1) u) ≤
      CD * ((β 0) ^ (-(1 / 2 : ℝ) + Q.ρ₁) * (L : ℝ) ^ (-((j : ℝ) * Q.ρ₀)) *
        Real.exp (-P.κ * sizeJ P.m₀ j X)) * vn u

/-- **The `ν_j = 0` limit clause for the observable terms** (CLASS-RULINGS-2 item 3): at
`ν_j = 0` the term `M^{obs}_j` does not depend on `h` (the case `ν_j = 0` of `factM`). -/
theorem ObsSourceForm.indepM_of_nu_zero {P : Consts} {Q : ObsConsts} {β ν : ℕ → ℝ}
    {Dom : FieldDom d L N₁ m₁ k N ϱ} {Tm : Terms d L N₁ m₁ k N ϱ} {Ot : ObsTerms d L N₁ m₁ k N}
    {St : ObsSourceTerms d L N₁ m₁ k N} {i₀ : Fin N} {CD : ℝ}
    (S : ObsSourceForm P Q β ν Dom Tm Ot St i₀ CD) {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k)
    (hν : nuIdeal L k (ν k) j = 0) {x : CTorus d L N₁ m₁ k} {X : Set (CTorus d L N₁ m₁ k)}
    (hX : IsPolyDom P.m₀ j X) (hx : x ∈ X) {Ψ h h' : Fld d L N₁ m₁ k N}
    (hd : Dom.dom j (Tm.gs j X) Ψ h) (hd' : Dom.dom j (Tm.gs j X) Ψ h') :
    Ot.M j x X Ψ h = Ot.M j x X Ψ h' := by
  rw [S.factM j hj1 hjk x X hX hx Ψ h hd, S.factM j hj1 hjk x X hX hx Ψ h' hd', hν]
  simp

end Balaban.Observables
