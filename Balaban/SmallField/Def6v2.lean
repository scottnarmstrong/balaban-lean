/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.Def6v2Domain
public import Balaban.SmallField.Def6Inhabited
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Def-6 v2: the small-field class with a regime and a field domain -- DRAFT

**Draft, pending Roland's answer to Q13** (`notes/phase1/Q13-ANSWER-astra.md`).  Second version of
`Def6.IsSF`, `Def6.IsSFFamily`, implementing `notes/phase1/CLASS-RULINGS-2.md`; the landed classes
are unchanged and their theorems are not affected.

Changes with respect to the landed class:

* **units** (item 1): the exponent of the density is
  `-(β_k L^{-k(d-2)}) action(G, a, ν_k L^{-2k}, D, φ_k^μ) + ℰ_k - E_k |T_1^{(k)}| + ℱ_k` (`expo2`),
  with the fine-unit coefficient `betaFine`;
* **mass split** (items 1, 2): the mass argument of `action` is the **physical** mass
  `Rg.physMass k = ν_k L^{-2k}`; the evaluated field is the solver output
  `φ_k^μ = bgField(…, μ_k, D)` computed with the **background** mass `Rg.bgMass k = bgMassAt(k₀,
  k, ν_k)`, which is also the mass of `χ_k` (`Xi`), of the compositions `ψ_k^{(j)}` and of the
  domains;
* **field domain** (items 4, 5, 7): every occurrence of `XiDom … (bgMass …)` in the term clauses
  is the parameter `Dom : FieldDom`, with the birth-level tag `j`; the density identity is stated at
  the real fields `Dom.phys`.

The term clauses are `SFTermClauses P Dom Tm` ((H.2)-(H.4), (H.7)); the class on one torus is
`IsSF2` (`density` and `terms`), the class of families `IsSFFamily2`.  The volume normalization
`E_k |T_1^{(k)}|` is unchanged: `|T_1^{(k)}| = (N₁ L^{m₁})^d` is the number of `k`-blocks of the fine
torus (item 1, "check the volume normalization separately").

**Restriction (theorem (c)).**  `SFTermClauses.mono`: the term clauses restrict to smaller
domains.  `IsSF.termClauses`: a member of the landed class satisfies the term clauses on the landed
domain.  `IsSF.toV2`, `IsSFFamily.toV2`: if the new domain is contained in the landed one and the
background masses agree, the **terms** of a member of the landed class are the terms of a member of
the new class, whose density is the old density multiplied by the explicit real factor
`exp(β_k A_k(μ_k) - β_k L^{-k(d-2)} A_k(ν_k L^{-2k}))` (`rhoV2`).  The only clause that prevents a
verbatim transfer (same density) is `density`: the unit prefactor and the mass of the action
(items 1, 2).

**Ambiguity recorded.**  The renormalization conditions (H.5) are kept verbatim (`Def6.RenormCond`:
reference points `(e_{i₀}, e_{i₀})`, every coordinate direction `i₀`).  CLASS-RULINGS-2 does not say
at which reference vector (H.5) is imposed on a single pinned chart; Q13-ANSWER (3.2) ("aligned
constant background `ψ = U h_*`, `b = V h_*`") suggests `h_*`.  On `pinFieldDom h_*` only the
reference point with `e_{i₀} = h_*` lies in the domain; on `pinAllFieldDom` all of them do.
-/

@[expose] public section

namespace Balaban.SmallField.Def6v2

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
  Balaban.SmallField.Def6 Finset

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-! ### The term clauses on a field domain -/

/-- **The clauses (H.2)-(H.4), (H.7) of the small-field class on a field domain** (the fields of
`Def6.IsSF` other than `density`, with every `XiDom … (bgMass …)` replaced by the parameter `Dom`;
CLASS-RULINGS-2 "Lean-ready class interface": "replace every `XiDom` used for `analyticE/M`,
`boundE/M`, rotation, locality … by this restricted domain, preserving the birth-level tag `j`").
The source `g` keeps its own domain `‖g‖₁ < 1`.  Draft pending Roland's answer to Q13. -/
structure SFTermClauses (P : Consts) (Dom : FieldDom d L N₁ m₁ k N ϱ)
    (Tm : Terms d L N₁ m₁ k N ϱ) : Prop where
  gs_spec : ∀ j, 1 ≤ j → j ≤ k → ∀ X, IsPolyDom P.m₀ j X →
    X ⊆ ↑((Tm.gs j X).Ω 1) ∧ ∀ i, j < i → (Tm.gs j X).Ω i = ∅
  analyticE : ∀ j, 1 ≤ j → j ≤ k → ∀ y X, IsPolyDom P.m₀ j X → y ∈ X →
    AnalyticOnNhd ℂ (fun p : Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N => Tm.E j y X p.1 p.2)
      {p | Dom.dom j (Tm.gs j X) p.1 p.2}
  analyticM : ∀ j, 1 ≤ j → j ≤ k → ∀ x X, IsPolyDom P.m₀ j X → x ∈ X →
    AnalyticOnNhd ℂ (fun p : Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N =>
        Tm.M j x X p.1 p.2.1 p.2.2)
      {p | Dom.dom j (Tm.gs j X) p.1 p.2.1 ∧ Def6.l1 p.2.2 < 1}
  rotE : ∀ j, 1 ≤ j → j ≤ k → ∀ y X, IsPolyDom P.m₀ j X → y ∈ X → ∀ R : Matrix (Fin N) (Fin N) ℂ,
    IsRot R → ∀ Ψ h, Dom.dom j (Tm.gs j X) Ψ h →
      Dom.dom j (Tm.gs j X) (rotField R Ψ) (rotField R h) →
      Tm.E j y X (rotField R Ψ) (rotField R h) = Tm.E j y X Ψ h
  pavingGS : ∀ j, 1 ≤ j → j ≤ k → ∀ X, IsPolyDom P.m₀ j X →
    ∀ r ∈ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k) (d := d) L P.m₀ j, ∀ i,
      (((Tm.gs j (r '' X)).Ω i : Finset (CTorus d L N₁ m₁ k)) : Set (CTorus d L N₁ m₁ k)) =
        r '' (((Tm.gs j X).Ω i : Finset (CTorus d L N₁ m₁ k)) : Set (CTorus d L N₁ m₁ k))
  eucE : ∀ j, 1 ≤ j → j ≤ k → ∀ y X, IsPolyDom P.m₀ j X → y ∈ X →
    ∀ r ∈ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k) (d := d) L P.m₀ j, ∀ Ψ h,
      Dom.dom j (Tm.gs j X) Ψ h → Dom.dom j (Tm.gs j (r '' X)) (actField r Ψ) (actField r h) →
      Tm.E j (blockBase L j (r y)) (r '' X) (actField r Ψ) (actField r h) = Tm.E j y X Ψ h
  eucEloc : ∀ j, 1 ≤ j → ∀ hjk : j ≤ k, ∀ y,
    ∀ r ∈ fullJSymGroup (N₁ := N₁) (m₁ := m₁) (k := k) (d := d) L j, ∀ Ψ h,
      Dom.dom j (levelGS (ϱ := ϱ) (N₁ := N₁) (m₁ := m₁) j hjk) Ψ h →
      Dom.dom j (levelGS (ϱ := ϱ) (N₁ := N₁) (m₁ := m₁) j hjk) (actField r Ψ) (actField r h) →
      Eloc P.m₀ Tm j (blockBase L j (r y)) (actField r Ψ) (actField r h) = Eloc P.m₀ Tm j y Ψ h
  rotM : ∀ j, 1 ≤ j → j ≤ k → ∀ x X, IsPolyDom P.m₀ j X → x ∈ X → ∀ R : Matrix (Fin N) (Fin N) ℂ,
    IsRot R → ∀ Ψ h g, Dom.dom j (Tm.gs j X) Ψ h →
      Dom.dom j (Tm.gs j X) (rotField R Ψ) (rotField R h) →
      Tm.M j x X (rotField R Ψ) (rotField R h) (rotField R g) = R.mulVec (Tm.M j x X Ψ h g)
  eucM : ∀ j, 1 ≤ j → j ≤ k → ∀ x X, IsPolyDom P.m₀ j X → x ∈ X →
    ∀ r ∈ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k) (d := d) L P.m₀ j, ∀ Ψ h g,
      Dom.dom j (Tm.gs j X) Ψ h → Dom.dom j (Tm.gs j (r '' X)) (actField r Ψ) (actField r h) →
      Tm.M j (r x) (r '' X) (actField r Ψ) (actField r h) (actField r g) = Tm.M j x X Ψ h g
  eucMloc : ∀ j, 1 ≤ j → ∀ hjk : j ≤ k, ∀ x,
    ∀ r ∈ fullJSymGroup (N₁ := N₁) (m₁ := m₁) (k := k) (d := d) L j, ∀ Ψ h g,
      Dom.dom j (levelGS (ϱ := ϱ) (N₁ := N₁) (m₁ := m₁) j hjk) Ψ h →
      Dom.dom j (levelGS (ϱ := ϱ) (N₁ := N₁) (m₁ := m₁) j hjk) (actField r Ψ) (actField r h) →
      Mloc P.m₀ Tm j (r x) (actField r Ψ) (actField r h) (actField r g) =
        Mloc P.m₀ Tm j x Ψ h g
  localE : ∀ j y X Ψ Ψ' h h', (∀ x ∈ X, Ψ x = Ψ' x ∧ h x = h' x) →
    Tm.E j y X Ψ h = Tm.E j y X Ψ' h'
  localM : ∀ j x X Ψ Ψ' h h' g g', (∀ z ∈ X, Ψ z = Ψ' z ∧ h z = h' z ∧ g z = g' z) →
    Tm.M j x X Ψ h g = Tm.M j x X Ψ' h' g'
  boundE : ∀ j, 1 ≤ j → j ≤ k → ∀ y X, IsPolyDom P.m₀ j X → y ∈ X → ∀ Ψ h,
    Dom.dom j (Tm.gs j X) Ψ h → ‖Tm.E j y X Ψ h‖ ≤ P.E₀ * Real.exp (-P.κ * sizeJ P.m₀ j X)
  boundM : ∀ j, 1 ≤ j → j ≤ k → ∀ x X, IsPolyDom P.m₀ j X → x ∈ X → ∀ Ψ h g,
    Dom.dom j (Tm.gs j X) Ψ h → Def6.l1 g < 1 →
    vn (Tm.M j x X Ψ h g) <
      P.c₉ * ((L : ℝ) ^ j)⁻¹ ^ (((d : ℝ) - 2) / 2 + P.γ - P.α₁) *
        Real.exp (-P.κ * sizeJ P.m₀ j X)

/-- **The term clauses restrict to smaller field domains.** -/
theorem SFTermClauses.mono {P : Consts} {Dom Dom' : FieldDom d L N₁ m₁ k N ϱ}
    {Tm : Terms d L N₁ m₁ k N ϱ} (hsub : ∀ j G Ψ h, Dom'.dom j G Ψ h → Dom.dom j G Ψ h)
    (h : SFTermClauses P Dom Tm) : SFTermClauses P Dom' Tm where
  gs_spec := h.gs_spec
  analyticE := fun j hj1 hjk y X hX hy =>
    (h.analyticE j hj1 hjk y X hX hy).mono fun _ hp => hsub _ _ _ _ hp
  analyticM := fun j hj1 hjk x X hX hx =>
    (h.analyticM j hj1 hjk x X hX hx).mono fun _ hp => ⟨hsub _ _ _ _ hp.1, hp.2⟩
  rotE := fun j hj1 hjk y X hX hy R hR Ψ hh h1 h2 =>
    h.rotE j hj1 hjk y X hX hy R hR Ψ hh (hsub _ _ _ _ h1) (hsub _ _ _ _ h2)
  pavingGS := h.pavingGS
  eucE := fun j hj1 hjk y X hX hy r hr Ψ hh h1 h2 =>
    h.eucE j hj1 hjk y X hX hy r hr Ψ hh (hsub _ _ _ _ h1) (hsub _ _ _ _ h2)
  eucEloc := fun j hj1 hjk y r hr Ψ hh h1 h2 =>
    h.eucEloc j hj1 hjk y r hr Ψ hh (hsub _ _ _ _ h1) (hsub _ _ _ _ h2)
  rotM := fun j hj1 hjk x X hX hx R hR Ψ hh g h1 h2 =>
    h.rotM j hj1 hjk x X hX hx R hR Ψ hh g (hsub _ _ _ _ h1) (hsub _ _ _ _ h2)
  eucM := fun j hj1 hjk x X hX hx r hr Ψ hh g h1 h2 =>
    h.eucM j hj1 hjk x X hX hx r hr Ψ hh g (hsub _ _ _ _ h1) (hsub _ _ _ _ h2)
  eucMloc := fun j hj1 hjk x r hr Ψ hh g h1 h2 =>
    h.eucMloc j hj1 hjk x r hr Ψ hh g (hsub _ _ _ _ h1) (hsub _ _ _ _ h2)
  localE := h.localE
  localM := h.localM
  boundE := fun j hj1 hjk y X hX hy Ψ hh h1 =>
    h.boundE j hj1 hjk y X hX hy Ψ hh (hsub _ _ _ _ h1)
  boundM := fun j hj1 hjk x X hX hx Ψ hh g h1 hg =>
    h.boundM j hj1 hjk x X hX hx Ψ hh g (hsub _ _ _ _ h1) hg

/-- **A member of the landed class satisfies the term clauses on the landed domain**
`Ξ^c_j(𝔹_j(X); 1, ε_j)` with the running-test mass `Def6.bgMass`. -/
theorem _root_.Balaban.SmallField.Def6.IsSF.termClauses {P : Consts} {β ν a : ℕ → ℝ}
    {Tm : Terms d L N₁ m₁ k N ϱ}
    {ρ : (CTorus d L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) → (CTorus d L N₁ m₁ k → Fin N → ℝ) → ℝ}
    {Ek : ℝ} (h : IsSF P β ν a Tm ρ Ek) :
    SFTermClauses P (xiFieldDom (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) (P.eps d L)) Tm where
  gs_spec := h.gs_spec
  analyticE := h.analyticE
  analyticM := h.analyticM
  rotE := h.rotE
  pavingGS := h.pavingGS
  eucE := h.eucE
  eucEloc := h.eucEloc
  rotM := h.rotM
  eucM := h.eucM
  eucMloc := h.eucMloc
  localE := h.localE
  localM := h.localM
  boundE := h.boundE
  boundM := h.boundM

/-! ### The density: units and the mass split -/

/-- **The exponent of the density (H.1), second version** (CLASS-RULINGS-2 item 1):
`-(β_k L^{-k(d-2)}) action(G, a, ν_k L^{-2k}, D, φ_k^μ) + ℰ_k - E_k |T_1^{(k)}| + ℱ_k`.
The mass argument of the fine-unit `action` is the **physical** mass `Rg.physMass k`; its field is
the solver output `φ_k^μ = bgField` computed with the **background** mass `Rg.bgMass k`, which is
also the mass of the compositions inside `ℰ_k = Ecomp`, `ℱ_k = Fcomp`.  At `μ_k = 0` the physical
mass term `(ν_k L^{-2k}/2) Σ |φ - h|²` is still present.  Draft pending Roland's answer to Q13. -/
noncomputable def expo2 (P : Consts) (Rg : Regime L) (β a : ℕ → ℝ) (Tm : Terms d L N₁ m₁ k N ϱ)
    (Ek : ℝ) (D : BgData (topGS d L N₁ m₁ k ϱ) N) (g : Fld d L N₁ m₁ k N) : ℂ :=
  -((betaFine d L k (β k) : ℝ) : ℂ) *
      ((action (topGS d L N₁ m₁ k ϱ) (aIdeal L k (a k)) (Rg.physMass k) D
        (bgField (topGS d L N₁ m₁ k ϱ) (aIdeal L k (a k)) (Rg.bgMass k) D) : ℝ) : ℂ) +
    Ecomp P.m₀ Tm (aIdeal L k (a k)) (Rg.bgMass k) D -
    (Ek : ℂ) * (((N₁ * L ^ m₁) ^ d : ℕ) : ℂ) +
    Fcomp P.m₀ Tm (aIdeal L k (a k)) (Rg.bgMass k) D g

/-- **The small-field class on one torus, second version** (Def-6 v2; CLASS-RULINGS-2 items 1, 2,
4, 5, 7).  Parameters: the constants `P`, the regime `Rg` (a priori `k₀`, physical masses `ν_j`),
the running coefficients `β, a`, the field domain `Dom`, the localized data `Tm`, the density `ρ`
and the constant `Ek`.
* `density` (H.1) (items 1, 2): for the real physical fields `h₀ ∈ Dom.phys`,
  `ρ_k = χ_k exp[expo2]`, `χ_k` the characteristic function of `Ξ_k(1, β_k^{-1/2} p(β_k))` at the
  background mass;
* `terms`: the clauses (H.2)-(H.4), (H.7) on the field domain `Dom` (`SFTermClauses`).
Draft pending Roland's answer to Q13. -/
structure IsSF2 (P : Consts) (Rg : Regime L) (β a : ℕ → ℝ) (Dom : FieldDom d L N₁ m₁ k N ϱ)
    (Tm : Terms d L N₁ m₁ k N ϱ)
    (ρ : (CTorus d L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) → (CTorus d L N₁ m₁ k → Fin N → ℝ) → ℝ)
    (Ek : ℝ) : Prop where
  density : ∀ (Ψ₀ : CTorus d L N₁ m₁ k → Fin N → ℝ) (h₀ : Fin N → ℝ)
    (g : CTorus d L N₁ m₁ k → Fin N → ℝ) (D : BgData (topGS d L N₁ m₁ k ϱ) N),
    h₀ ∈ Dom.phys → Realizes D Ψ₀ h₀ → Def6.l1 (fun x i => (g x i : ℂ)) < 1 →
    (ρ Ψ₀ h₀ g : ℂ) =
      open Classical in
      if Xi (topGS d L N₁ m₁ k ϱ) (aIdeal L k (a k)) (Rg.bgMass k) k 1
          (P.p (β k) / Real.sqrt (β k)) Ψ₀ h₀
      then Complex.exp (expo2 P Rg β a Tm Ek D (fun x i => (g x i : ℂ)))
      else 0
  terms : SFTermClauses P Dom Tm

/-- **Def-6 v2: the small-field class of families over the tori** (CLASS-RULINGS-2): `IsSF2` on
every torus (with a field domain on every torus), torus independence of the terms (P4 (H.4)), the
renormalization conditions (H.5) at every scale `j ≤ k` (kept verbatim, see the module docstring)
and the coefficient bounds (H.6) for the physical masses of the regime.  Draft pending Roland's
answer to Q13. -/
structure IsSFFamily2 (P : Consts) (Rg : Regime L) (β a : ℕ → ℝ)
    (Dom : ∀ (N₁ : ℕ) [NeZero N₁], FieldDom d L N₁ m₁ k N ϱ)
    (Tm : ∀ (N₁ : ℕ) [NeZero N₁], Terms d L N₁ m₁ k N ϱ)
    (ρ : ∀ (N₁ : ℕ) [NeZero N₁], (CTorus d L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) →
      (CTorus d L N₁ m₁ k → Fin N → ℝ) → ℝ)
    (Ek : ℕ → ℝ) : Prop where
  admissible : P.Admissible d L
  coeff : CoeffBounds d L k P β Rg.ν a
  torus : ∀ (N₁ : ℕ) [NeZero N₁], IsSF2 P Rg β a (Dom N₁) (Tm N₁) (ρ N₁) (Ek N₁)
  torusIndep : TorusIndep P.m₀ Tm
  renorm : ∀ j, 1 ≤ j → j ≤ k → RenormCond (d := d) (L := L) (m₁ := m₁) (N := N) (ϱ := ϱ)
    P.m₀ k (Rg.ν k) Tm j

/-- The standing hypotheses of the background theory for the background mass of a regime
(`d ≥ 3`, `L ≥ 3`, `ϱ ≥ R₀(d, L)`, the coefficient bounds (H.6)). -/
theorem bgHyp_of_class2 {d L k : ℕ} [NeZero L] {ϱ : ℝ} {P : Consts} {Rg : Regime L}
    {β a : ℕ → ℝ} (hP : P.Admissible d L) (hC : CoeffBounds d L k P β Rg.ν a) (hd : 3 ≤ d)
    (hL : 3 ≤ L) (hϱ : bgR0 d L ≤ ϱ) : BgHyp d L k ϱ (aIdeal L k (a k)) (Rg.bgMass k) where
  hd := hd
  hL := hL
  hϱ := hϱ
  weights := fun _ hj hjk => aIdeal_mem hL hC.a_ge hC.a_lt hj hjk
  mass := Rg.bgMass_nonneg hC.nu_pos.le
  massLe := by
    have hL3 : (3 : ℝ) ≤ L := by exact_mod_cast hL
    have h1 := hP.νbar_le
    have h2 := hC.nu_le
    have h3 : Rg.bgMass k * ((L : ℝ) ^ k) ^ 2 ≤ Rg.physMass k * ((L : ℝ) ^ k) ^ 2 :=
      mul_le_mul_of_nonneg_right (Rg.bgMass_le_physMass hC.nu_pos.le) (by positivity)
    have h4 : Rg.physMass k * ((L : ℝ) ^ k) ^ 2 = Rg.ν k := physMass_mul_sq k _
    have : ((L : ℝ) ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith)
    linarith

/-! ### Restriction: from the landed class to the second version (theorem (c)) -/

open Classical in
/-- **The density of the second version for a member of the landed class**: the old density
multiplied by the explicit real factor `exp(β_k A_k(μ_k) - β_k L^{-k(d-2)} A_k(ν_k L^{-2k}))`
(the unit prefactor and the mass of the action, CLASS-RULINGS-2 items 1, 2), `A_k(m)` the fine-unit
action of mass `m` at the background field of mass `μ_k`, for the realizing datum of `(Ψ₀, h₀)`. -/
noncomputable def rhoV2 (Rg : Regime L) (β a : ℕ → ℝ)
    (ρ : (CTorus d L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) → (CTorus d L N₁ m₁ k → Fin N → ℝ) → ℝ)
    (Ψ₀ : CTorus d L N₁ m₁ k → Fin N → ℝ) (h₀ : Fin N → ℝ)
    (g : CTorus d L N₁ m₁ k → Fin N → ℝ) : ℝ :=
  if hD : ∃ D : BgData (topGS d L N₁ m₁ k ϱ) N, Realizes D Ψ₀ h₀ then
    ρ Ψ₀ h₀ g * Real.exp (β k * action (topGS d L N₁ m₁ k ϱ) (aIdeal L k (a k)) (Rg.bgMass k)
        hD.choose (bgField (topGS d L N₁ m₁ k ϱ) (aIdeal L k (a k)) (Rg.bgMass k) hD.choose) -
      betaFine d L k (β k) * action (topGS d L N₁ m₁ k ϱ) (aIdeal L k (a k)) (Rg.physMass k)
        hD.choose (bgField (topGS d L N₁ m₁ k ϱ) (aIdeal L k (a k)) (Rg.bgMass k) hD.choose))
  else ρ Ψ₀ h₀ g

/-- **Theorem (c), one torus: restriction of the landed class to the second version.**  Let
`(Tm, ρ)` be a member of the landed class `Def6.IsSF`.  If the field domain `Dom` is contained in
the landed domain `Ξ^c_j(𝔹; 1, ε_j)` (e.g. the pinned domain, `pinFieldDom_sub_xi`) and the
background mass of the regime `(k₀, ν)` at scale `k` is the running-test mass of the landed class,
then the same terms `Tm` with the density `rhoV2` form a member of `IsSF2` on `Dom`.  The term
clauses transfer verbatim; the clause `density` holds for the reweighted density only (units and
mass split, items 1, 2). -/
theorem _root_.Balaban.SmallField.Def6.IsSF.toV2 {P : Consts} {β ν a : ℕ → ℝ}
    {Tm : Terms d L N₁ m₁ k N ϱ}
    {ρ : (CTorus d L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) → (CTorus d L N₁ m₁ k → Fin N → ℝ) → ℝ}
    {Ek : ℝ} (h : IsSF P β ν a Tm ρ Ek) {k₀ : ℕ}
    (hμ : bgMassAt L k₀ k (ν k) = bgMass L k (β k) (ν k)) {Dom : FieldDom d L N₁ m₁ k N ϱ}
    (hsub : ∀ j G Ψ h', Dom.dom j G Ψ h' →
      XiDom G (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) j (P.eps d L j) Ψ h') :
    IsSF2 P ⟨k₀, ν⟩ β a Dom Tm (rhoV2 (ϱ := ϱ) ⟨k₀, ν⟩ β a ρ) Ek where
  terms := h.termClauses.mono hsub
  density := by
    intro Ψ₀ h₀ g D _ hR hg
    classical
    have hb : (⟨k₀, ν⟩ : Regime L).bgMass k = bgMass L k (β k) (ν k) := hμ
    have old := h.density Ψ₀ h₀ g D hR hg
    have e : rhoV2 (ϱ := ϱ) ⟨k₀, ν⟩ β a ρ Ψ₀ h₀ g =
        ρ Ψ₀ h₀ g * Real.exp (β k * action (topGS d L N₁ m₁ k ϱ) (aIdeal L k (a k))
            ((⟨k₀, ν⟩ : Regime L).bgMass k) D
            (bgField (topGS d L N₁ m₁ k ϱ) (aIdeal L k (a k)) ((⟨k₀, ν⟩ : Regime L).bgMass k) D) -
          betaFine d L k (β k) * action (topGS d L N₁ m₁ k ϱ) (aIdeal L k (a k))
            ((⟨k₀, ν⟩ : Regime L).physMass k) D
            (bgField (topGS d L N₁ m₁ k ϱ) (aIdeal L k (a k))
              ((⟨k₀, ν⟩ : Regime L).bgMass k) D)) := by
      unfold rhoV2
      split_ifs with hD
      · rw [show hD.choose = D from realizes_unique hD.choose_spec hR]
      · exact absurd ⟨D, hR⟩ hD
    rw [e]
    unfold expo2
    rw [hb, Complex.ofReal_mul, Complex.ofReal_exp, old]
    by_cases hX : Xi (topGS d L N₁ m₁ k ϱ) (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) k 1
        (P.p (β k) / Real.sqrt (β k)) Ψ₀ h₀
    · simp only [hX, ↓reduceIte]
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    · simp only [hX, ↓reduceIte, zero_mul]

/-- **Theorem (c), families: restriction of the landed class to the second version**, for the
field domains contained in the landed ones (in particular the pinned domains at any real unit
`h_*` and radius `r_h`) and a regime whose background mass at scale `k` is the running-test mass.
The clauses `admissible`, `coeff`, `torusIndep`, `renorm` are the same. -/
theorem _root_.Balaban.SmallField.Def6.IsSFFamily.toV2 {P : Consts} {β ν a : ℕ → ℝ}
    {Tm : ∀ (N₁ : ℕ) [NeZero N₁], Terms d L N₁ m₁ k N ϱ}
    {ρ : ∀ (N₁ : ℕ) [NeZero N₁], (CTorus d L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) →
      (CTorus d L N₁ m₁ k → Fin N → ℝ) → ℝ}
    {Ek : ℕ → ℝ} (h : IsSFFamily P β ν a Tm ρ Ek) {k₀ : ℕ}
    (hμ : bgMassAt L k₀ k (ν k) = bgMass L k (β k) (ν k))
    {Dom : ∀ (N₁ : ℕ) [NeZero N₁], FieldDom d L N₁ m₁ k N ϱ}
    (hsub : ∀ (N₁ : ℕ) [NeZero N₁], ∀ j G Ψ h', (Dom N₁).dom j G Ψ h' →
      XiDom G (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) j (P.eps d L j) Ψ h') :
    IsSFFamily2 P ⟨k₀, ν⟩ β a Dom Tm
      (fun N₁ _ => rhoV2 (ϱ := ϱ) ⟨k₀, ν⟩ β a (ρ N₁)) Ek where
  admissible := h.admissible
  coeff := h.coeff
  torus := fun N₁ _ => (h.torus N₁).toV2 hμ (hsub N₁)
  torusIndep := h.torusIndep
  renorm := h.renorm

/-- **Theorem (c) for the pinned domain**: a member of the landed class whose running-test mass at
`k` is the background mass of the regime gives a member of the second version on the pinned
domain at every real vector `h_*` and every radius `r_h` (the domain is empty unless `h_*` is a
unit vector). -/
theorem _root_.Balaban.SmallField.Def6.IsSFFamily.toPin {P : Consts} {β ν a : ℕ → ℝ}
    {Tm : ∀ (N₁ : ℕ) [NeZero N₁], Terms d L N₁ m₁ k N ϱ}
    {ρ : ∀ (N₁ : ℕ) [NeZero N₁], (CTorus d L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) →
      (CTorus d L N₁ m₁ k → Fin N → ℝ) → ℝ}
    {Ek : ℕ → ℝ} (h : IsSFFamily P β ν a Tm ρ Ek) {k₀ : ℕ}
    (hμ : bgMassAt L k₀ k (ν k) = bgMass L k (β k) (ν k)) (hStar : Fin N → ℝ) (rH : ℝ) :
    IsSFFamily2 P ⟨k₀, ν⟩ β a
      (fun _ _ => pinFieldDom hStar rH (aIdeal L k (a k)) (bgMassAt L k₀ k (ν k)) (P.eps d L)) Tm
      (fun N₁ _ => rhoV2 (ϱ := ϱ) ⟨k₀, ν⟩ β a (ρ N₁)) Ek :=
  h.toV2 hμ fun N₁ _ j G Ψ h' hp => by
    have hp' : Pin hStar rH G (aIdeal L k (a k)) (bgMassAt L k₀ k (ν k)) j (P.eps d L j) Ψ h' := hp
    rw [← hμ]; exact hp'.xiDom

end Balaban.SmallField.Def6v2
