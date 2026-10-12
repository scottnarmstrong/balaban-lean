/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.Def6v2
public import Balaban.SmallField.Def6v2RefJet
public import Balaban.SmallField.RenormAnisoBridge
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Def-6 v2, part 3: the physical-source form of the terms (`SourceForm`) -- DRAFT

**Draft, pending Roland's answer to Q13.**  CLASS-RULINGS-2 item 3 and `notes/phase1/PIN-I6.md`.

The physical source of the terms born at level `j` is `b_j = ν_j h`, `ν_j = nuIdeal L k ν_k j` (P1
p. 123 (3.13)-(3.14), p. 146 (3.104), (3.106); SMALLFIELD §1.3 (H.5)).  It is **not** the operator
`b` of P5 (H.5), which is the exponent of the large-field kernels (item 3: "the two uses of the
letter should be renamed in Lean": here the source is always called `src`/`b_j`, and the data of
the source form are `SourceTerms`).

* `SourceTerms`: the functions `Ẽ_j(y, X; Ψ, b)`, `M̃_j(x, X; Ψ, b, g)`;
* `srcDom Dom ν_j`: the **restricted** `b`-domain, the image of the field domain under
  `h ↦ ν_j h`.  On the pinned chart it is the ball `‖b - ν_j h_*‖ < ν_j r_h` (`srcDom_pin_lt`), of
  radius proportional to the mass: no mass-uniform transverse `b`-disc is demanded;
* `srcPack`: the centred packed form of `Ẽ_j(0, X; ·)` on a polymer shape of `ℤ^d` (the
  coordinates `(ψ|_X, b)` of `RenormDefs.Cfg`), the object of the anisotropic I-6;
* `SourceForm`: the clauses
  - `factE`, `factM` (item 3): `E_j(y, X; Ψ, h) = Ẽ_j(y, X; Ψ, ν_j h)` and the same for `ℳ`, on the
    field domain; at `ν_j = 0` they say that the terms do not depend on `h`
    (`SourceForm.indepE_of_nu_zero`, `indepM_of_nu_zero`: the separate `ν_j = 0` limit clause of
    item 3);
  - `analyticE`, `analyticM` (for `ν_j > 0`), `boundE`, `boundM`: analyticity and the bounds
    (H.4), (H.7) on the restricted `b`-domain;
  - `dbE`: the mass-weighted reference derivative, `ν_j |D_b Ẽ(e, ν_j e)[u]| ≤ C_D E₀ e^{-κ d_j} |u|`
    (item 3, item 4: "the `ν_j`-weighted `b` derivative");
  - `refJet` (**PIN-I6 §3**): the reference-jet certificate `RefJet` of every centred term, with
    `r = r_j = anisoRadius` and `M_X = E₀ e^{-κ d_j(X)}`.  PIN-I6 §2 (`pinI6_no_uniform_bound`)
    shows that the pinned class without it does not admit the I-6 bound.
* `sourceOf`, `sourceForm_of_pos`: for `ν_j > 0` the factorization is the reparametrization
  `Ẽ(Ψ, b) = E(Ψ, b/ν_j)`, and `factE`, `factM`, analyticity and the bounds follow from the class
  ("for `ν_j > 0` mere reparametrization is vacuous"); the content of `SourceForm` is `dbE` and
  `refJet`.
-/

@[expose] public section

namespace Balaban.SmallField.Def6v2

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
  Balaban.SmallField.Def6 Finset

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- **The source-form data** (CLASS-RULINGS-2 item 3): `Ẽ_j(y, X; Ψ, b)` and `M̃_j(x, X; Ψ, b, g)`,
functions of the spin data and of the physical source `b = ν_j h`. -/
structure SourceTerms (d L N₁ m₁ k N : ℕ) where
  /-- `Ẽ_j(y, X; Ψ, b)` -/
  E : ℕ → CTorus d L N₁ m₁ k → Set (CTorus d L N₁ m₁ k) → Fld d L N₁ m₁ k N →
    Fld d L N₁ m₁ k N → ℂ
  /-- `M̃_j(x, X; Ψ, b, g)` -/
  M : ℕ → CTorus d L N₁ m₁ k → Set (CTorus d L N₁ m₁ k) → Fld d L N₁ m₁ k N →
    Fld d L N₁ m₁ k N → Fld d L N₁ m₁ k N → (Fin N → ℂ)

/-- **The restricted `b`-domain** of the level-`j` terms (item 3: "the restricted analytic `b`
domain"): the image of the field domain under `h ↦ ν_j h`. -/
def srcDom (Dom : FieldDom d L N₁ m₁ k N ϱ) (νj : ℝ) (j : ℕ)
    (G : GeneratingSet d L (N₁ * L ^ m₁) k ϱ) (Ψ b : Fld d L N₁ m₁ k N) : Prop :=
  ∃ h : Fld d L N₁ m₁ k N, Dom.dom j G Ψ h ∧ b = (νj : ℂ) • h

/-- **On the pinned chart the source ball has radius `ν_j r_h`** (Q13-ANSWER §4: "on the pinned
chart `|b_⊥| ≤ m r_h`"): `‖b(x) - ν_j h_*‖ ≤ ν_j r_h`.  The restricted domain contains no
mass-uniform transverse `b`-disc. -/
theorem srcDom_pin_lt {hStar : Fin N → ℝ} {rH : ℝ} {a : ℕ → ℝ} {μ : ℝ} {ε : ℕ → ℝ} {νj : ℝ}
    (hν : 0 ≤ νj) {j : ℕ} {G : GeneratingSet d L (N₁ * L ^ m₁) k ϱ} {Ψ b : Fld d L N₁ m₁ k N}
    (h : srcDom (pinFieldDom hStar rH a μ ε) νj j G Ψ b) (x : CTorus d L N₁ m₁ k) :
    vn (fun i => b x i - (νj : ℂ) * (hStar i : ℂ)) ≤ νj * rH := by
  obtain ⟨hf, hd, rfl⟩ := h
  have hp : Pin hStar rH G a μ j (ε j) Ψ hf := hd
  have h1 := (hp.vn_sub_lt x).le
  have e : (fun i => ((νj : ℂ) • hf) x i - (νj : ℂ) * (hStar i : ℂ)) =
      fun i => (νj : ℂ) * (hf x i - (hStar i : ℂ)) := by
    funext i; simp only [Pi.smul_apply, smul_eq_mul]; ring
  rw [e, vn_smul_real, abs_of_nonneg hν]
  exact mul_le_mul_of_nonneg_left h1 hν

/-- **The centred packed form of the source term** `Ẽ_j(0, X; ·)` on a polymer shape `X'` of
`ℤ^d`: the configuration `c = (ψ|_{X'}, b)` gives the torus spin field `fieldOf` (`c` on the blocks
of `X'`, `e_{i₀}` elsewhere) and the constant source `b`.  For `ν_j > 0` and the reparametrized
source terms it is the landed `Def6.Eaux` (`srcPack_sourceOf`). -/
noncomputable def srcPack (St : SourceTerms d L N₁ m₁ k N) (j : ℕ) (i₀ : Fin N)
    (X' : Finset (Site d)) (c : Cfg d N X') : ℂ :=
  St.E j 0 (Ypoly j X') (fieldOf j i₀ X' c) (fun _ i => c (Sum.inr i))

/-- **`SourceForm`: the physical-source form of the terms of a class member** (CLASS-RULINGS-2
item 3; PIN-I6 §3), for the masses `ν`, the field domain `Dom`, the terms `Tm`, the source data
`St`, the reference direction `e = e_{i₀}` (the pinned chart at `h_* = e_{i₀}`; a general `h_*` is
reached by a rotation, PIN-I6 §4) and the derivative constant `C_D`.  See the module docstring for
the clauses.  Draft pending Roland's answer to Q13. -/
structure SourceForm (P : Consts) (ν : ℕ → ℝ) (Dom : FieldDom d L N₁ m₁ k N ϱ)
    (Tm : Terms d L N₁ m₁ k N ϱ) (St : SourceTerms d L N₁ m₁ k N) (i₀ : Fin N) (CD : ℝ) :
    Prop where
  /-- item 3: `E_j(y, X; Ψ, h) = Ẽ_j(y, X; Ψ, ν_j h)` -/
  factE : ∀ j, 1 ≤ j → j ≤ k → ∀ y X, IsPolyDom P.m₀ j X → y ∈ X → ∀ Ψ h,
    Dom.dom j (Tm.gs j X) Ψ h →
      Tm.E j y X Ψ h = St.E j y X Ψ ((nuIdeal L k (ν k) j : ℂ) • h)
  /-- item 3: `ℳ_j(x, X; Ψ, h, g) = M̃_j(x, X; Ψ, ν_j h, g)` -/
  factM : ∀ j, 1 ≤ j → j ≤ k → ∀ x X, IsPolyDom P.m₀ j X → x ∈ X → ∀ Ψ h g,
    Dom.dom j (Tm.gs j X) Ψ h →
      Tm.M j x X Ψ h g = St.M j x X Ψ ((nuIdeal L k (ν k) j : ℂ) • h) g
  /-- analyticity on the restricted `b`-domain, for a positive mass -/
  analyticE : ∀ j, 1 ≤ j → j ≤ k → 0 < nuIdeal L k (ν k) j → ∀ y X, IsPolyDom P.m₀ j X → y ∈ X →
    AnalyticOnNhd ℂ (fun p : Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N => St.E j y X p.1 p.2)
      {p | srcDom Dom (nuIdeal L k (ν k) j) j (Tm.gs j X) p.1 p.2}
  analyticM : ∀ j, 1 ≤ j → j ≤ k → 0 < nuIdeal L k (ν k) j → ∀ x X, IsPolyDom P.m₀ j X → x ∈ X →
    AnalyticOnNhd ℂ (fun p : Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N =>
        St.M j x X p.1 p.2.1 p.2.2)
      {p | srcDom Dom (nuIdeal L k (ν k) j) j (Tm.gs j X) p.1 p.2.1 ∧ Def6.l1 p.2.2 < 1}
  /-- the bound (H.4) on the restricted `b`-domain -/
  boundE : ∀ j, 1 ≤ j → j ≤ k → ∀ y X, IsPolyDom P.m₀ j X → y ∈ X → ∀ Ψ b,
    srcDom Dom (nuIdeal L k (ν k) j) j (Tm.gs j X) Ψ b →
      ‖St.E j y X Ψ b‖ ≤ P.E₀ * Real.exp (-P.κ * sizeJ P.m₀ j X)
  /-- the bound (H.7) on the restricted `b`-domain -/
  boundM : ∀ j, 1 ≤ j → j ≤ k → ∀ x X, IsPolyDom P.m₀ j X → x ∈ X → ∀ Ψ b g,
    srcDom Dom (nuIdeal L k (ν k) j) j (Tm.gs j X) Ψ b → Def6.l1 g < 1 →
      vn (St.M j x X Ψ b g) <
        P.c₉ * ((L : ℝ) ^ j)⁻¹ ^ (((d : ℝ) - 2) / 2 + P.γ - P.α₁) *
          Real.exp (-P.κ * sizeJ P.m₀ j X)
  /-- the mass-weighted reference derivative in the source (items 3, 4) -/
  dbE : ∀ j, 1 ≤ j → j ≤ k → ∀ y X, IsPolyDom P.m₀ j X → y ∈ X → ∀ u : Fin N → ℂ,
    nuIdeal L k (ν k) j *
        ‖fderiv ℂ (fun b : Fin N → ℂ => St.E j y X (constFld (Pi.single i₀ 1)) (constFld b))
          ((nuIdeal L k (ν k) j : ℂ) • Pi.single i₀ 1) u‖ ≤
      CD * (P.E₀ * Real.exp (-P.κ * sizeJ P.m₀ j X)) * vn u
  /-- **PIN-I6 §3**: the reference-jet certificate of every centred term (value, first and second
  jets at `(e, ν_j e)`, in particular the second transverse-`b` derivative, of the sizes of the
  anisotropic polydisc of radius `r_j`) -/
  refJet : ∀ j, 1 ≤ j → j ≤ k →
    ∀ X' ∈ liftPolys (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P j,
      RefJet i₀ (nuIdeal L k (ν k) j) (anisoRadius d L N P j)
        (P.E₀ * Real.exp (-P.κ * sizeJ (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P.m₀ j
          (Ypoly j X'))) X' (srcPack St j i₀ X')

section Consequences

variable {P : Consts} {ν : ℕ → ℝ} {Dom : FieldDom d L N₁ m₁ k N ϱ} {Tm : Terms d L N₁ m₁ k N ϱ}
  {St : SourceTerms d L N₁ m₁ k N} {i₀ : Fin N} {CD : ℝ}

/-- **The `ν_j = 0` limit clause** (CLASS-RULINGS-2 item 3: "at `ν_j = 0` require these physical
terms to be `h` independent"): the case `ν_j = 0` of `factE`. -/
theorem SourceForm.indepE_of_nu_zero (S : SourceForm P ν Dom Tm St i₀ CD) {j : ℕ} (hj1 : 1 ≤ j)
    (hjk : j ≤ k) (hν : nuIdeal L k (ν k) j = 0) {y : CTorus d L N₁ m₁ k}
    {X : Set (CTorus d L N₁ m₁ k)} (hX : IsPolyDom P.m₀ j X) (hy : y ∈ X)
    {Ψ h h' : Fld d L N₁ m₁ k N} (hd : Dom.dom j (Tm.gs j X) Ψ h)
    (hd' : Dom.dom j (Tm.gs j X) Ψ h') : Tm.E j y X Ψ h = Tm.E j y X Ψ h' := by
  rw [S.factE j hj1 hjk y X hX hy Ψ h hd, S.factE j hj1 hjk y X hX hy Ψ h' hd', hν]
  simp

/-- The `ν_j = 0` limit clause for `ℳ`. -/
theorem SourceForm.indepM_of_nu_zero (S : SourceForm P ν Dom Tm St i₀ CD) {j : ℕ} (hj1 : 1 ≤ j)
    (hjk : j ≤ k) (hν : nuIdeal L k (ν k) j = 0) {x : CTorus d L N₁ m₁ k}
    {X : Set (CTorus d L N₁ m₁ k)} (hX : IsPolyDom P.m₀ j X) (hx : x ∈ X)
    {Ψ h h' : Fld d L N₁ m₁ k N} (g : Fld d L N₁ m₁ k N) (hd : Dom.dom j (Tm.gs j X) Ψ h)
    (hd' : Dom.dom j (Tm.gs j X) Ψ h') : Tm.M j x X Ψ h g = Tm.M j x X Ψ h' g := by
  rw [S.factM j hj1 hjk x X hX hx Ψ h g hd, S.factM j hj1 hjk x X hX hx Ψ h' g hd', hν]
  simp

/-- The certificate gives the bound of PIN-I6 (2.4) on the second transverse source derivative
of every centred term. -/
theorem SourceForm.d2_bperp (S : SourceForm P ν Dom Tm St i₀ CD) {j : ℕ} (hj1 : 1 ≤ j)
    (hjk : j ≤ k) {X' : Finset (Site d)}
    (hX' : X' ∈ liftPolys (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P j) {i₁ : Fin N}
    (hne : i₁ ≠ i₀) :
    ‖D2 (srcPack St j i₀ X') (refPt i₀ (nuIdeal L k (ν k) j) X') (Pi.single (Sum.inr i₁) 1)
        (Pi.single (Sum.inr i₁) 1)‖ ≤
      4 * (P.E₀ * Real.exp (-P.κ * sizeJ (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P.m₀ j
        (Ypoly j X'))) / anisoRadius d L N P j ^ 2 :=
  (S.refJet j hj1 hjk X' hX').d2_bperp hne

end Consequences

/-! ### Positive mass: the reparametrization -/

/-- **The reparametrized source terms** `Ẽ(Ψ, b) = E(Ψ, b / ν_j)`, `M̃(Ψ, b, g) = ℳ(Ψ, b / ν_j, g)`
(for `ν_j > 0`). -/
noncomputable def sourceOf (ν : ℕ → ℝ) (Tm : Terms d L N₁ m₁ k N ϱ) :
    SourceTerms d L N₁ m₁ k N where
  E := fun j y X Ψ b => Tm.E j y X Ψ ((nuIdeal L k (ν k) j : ℂ)⁻¹ • b)
  M := fun j x X Ψ b g => Tm.M j x X Ψ ((nuIdeal L k (ν k) j : ℂ)⁻¹ • b) g

omit [NeZero L] [NeZero N₁] in
theorem inv_smul_smul_fld {c : ℝ} (hc : c ≠ 0) (h : Fld d L N₁ m₁ k N) :
    (c : ℂ)⁻¹ • ((c : ℂ) • h) = h := by
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  rw [smul_smul, inv_mul_cancel₀ hc', one_smul]

/-- For the reparametrized source terms the centred packed form is the landed `Def6.Eaux`. -/
theorem srcPack_sourceOf (ν : ℕ → ℝ) (Tm : Terms d L N₁ m₁ k N ϱ) (j : ℕ) (i₀ : Fin N)
    (X' : Finset (Site d)) (c : Cfg d N X') :
    srcPack (sourceOf ν Tm) j i₀ X' c = Eaux Tm j i₀ (nuIdeal L k (ν k) j) X' c := by
  show Tm.E j 0 (Ypoly j X') (fieldOf j i₀ X' c)
      ((nuIdeal L k (ν k) j : ℂ)⁻¹ • fun _ i => c (Sum.inr i)) =
    Tm.E j 0 (Ypoly j X') (fieldOf j i₀ X' c) (hOf (nuIdeal L k (ν k) j) X' c)
  congr 1
  funext x i
  simp [hOf, div_eq_inv_mul]

/-- **For positive masses the source form is the reparametrization** (CLASS-RULINGS-2 item 3: "for
`ν_j > 0` mere reparametrization is vacuous"): the factorization, the analyticity and the bounds on
the restricted `b`-domain follow from the term clauses of the class.  What remains to be supplied is
the mass-weighted derivative `dbE` and the reference-jet certificate `refJet` (PIN-I6). -/
theorem sourceForm_of_pos {P : Consts} {ν : ℕ → ℝ} {Dom : FieldDom d L N₁ m₁ k N ϱ}
    {Tm : Terms d L N₁ m₁ k N ϱ} {i₀ : Fin N} {CD : ℝ} (hT : SFTermClauses P Dom Tm)
    (hν : ∀ j, 1 ≤ j → j ≤ k → 0 < nuIdeal L k (ν k) j)
    (hdb : ∀ j, 1 ≤ j → j ≤ k → ∀ y X, IsPolyDom P.m₀ j X → y ∈ X → ∀ u : Fin N → ℂ,
      nuIdeal L k (ν k) j *
          ‖fderiv ℂ (fun b : Fin N → ℂ =>
            (sourceOf ν Tm).E j y X (constFld (Pi.single i₀ 1)) (constFld b))
            ((nuIdeal L k (ν k) j : ℂ) • Pi.single i₀ 1) u‖ ≤
        CD * (P.E₀ * Real.exp (-P.κ * sizeJ P.m₀ j X)) * vn u)
    (hjet : ∀ j, 1 ≤ j → j ≤ k →
      ∀ X' ∈ liftPolys (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P j,
        RefJet i₀ (nuIdeal L k (ν k) j) (anisoRadius d L N P j)
          (P.E₀ * Real.exp (-P.κ * sizeJ (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P.m₀ j
            (Ypoly j X'))) X' (srcPack (sourceOf ν Tm) j i₀ X')) :
    SourceForm P ν Dom Tm (sourceOf ν Tm) i₀ CD where
  factE := fun j hj1 hjk y X _ _ Ψ h _ => by
    show _ = Tm.E j y X Ψ ((nuIdeal L k (ν k) j : ℂ)⁻¹ • ((nuIdeal L k (ν k) j : ℂ) • h))
    rw [inv_smul_smul_fld (hν j hj1 hjk).ne']
  factM := fun j hj1 hjk x X _ _ Ψ h g _ => by
    show _ = Tm.M j x X Ψ ((nuIdeal L k (ν k) j : ℂ)⁻¹ • ((nuIdeal L k (ν k) j : ℂ) • h)) g
    rw [inv_smul_smul_fld (hν j hj1 hjk).ne']
  analyticE := fun j hj1 hjk hpos y X hX hy => by
    set T : (Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N) →L[ℂ]
        (Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N) :=
      (ContinuousLinearMap.fst ℂ _ _).prod
        ((nuIdeal L k (ν k) j : ℂ)⁻¹ • ContinuousLinearMap.snd ℂ _ _) with hTdef
    have hmaps : Set.MapsTo T
        {p | srcDom Dom (nuIdeal L k (ν k) j) j (Tm.gs j X) p.1 p.2}
        {p | Dom.dom j (Tm.gs j X) p.1 p.2} := by
      rintro p ⟨h, hd, hb⟩
      show Dom.dom j (Tm.gs j X) p.1 ((nuIdeal L k (ν k) j : ℂ)⁻¹ • p.2)
      rw [hb, inv_smul_smul_fld hpos.ne']; exact hd
    exact (hT.analyticE j hj1 hjk y X hX hy).comp (fun p _ => T.analyticAt p) hmaps
  analyticM := fun j hj1 hjk hpos x X hX hx => by
    set T : (Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N) →L[ℂ]
        (Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N) :=
      (ContinuousLinearMap.fst ℂ _ _).prod
        (((nuIdeal L k (ν k) j : ℂ)⁻¹ • (ContinuousLinearMap.fst ℂ _ _).comp
            (ContinuousLinearMap.snd ℂ _ _)).prod
          ((ContinuousLinearMap.snd ℂ _ _).comp (ContinuousLinearMap.snd ℂ _ _))) with hTdef
    have hmaps : Set.MapsTo T
        {p | srcDom Dom (nuIdeal L k (ν k) j) j (Tm.gs j X) p.1 p.2.1 ∧ Def6.l1 p.2.2 < 1}
        {p | Dom.dom j (Tm.gs j X) p.1 p.2.1 ∧ Def6.l1 p.2.2 < 1} := by
      rintro p ⟨⟨h, hd, hb⟩, hg⟩
      refine ⟨?_, hg⟩
      show Dom.dom j (Tm.gs j X) p.1 ((nuIdeal L k (ν k) j : ℂ)⁻¹ • p.2.1)
      rw [hb, inv_smul_smul_fld hpos.ne']; exact hd
    exact (hT.analyticM j hj1 hjk x X hX hx).comp (fun p _ => T.analyticAt p) hmaps
  boundE := fun j hj1 hjk y X hX hy Ψ b ⟨h, hd, hb⟩ => by
    show ‖Tm.E j y X Ψ ((nuIdeal L k (ν k) j : ℂ)⁻¹ • b)‖ ≤ _
    rw [hb, inv_smul_smul_fld (hν j hj1 hjk).ne']
    exact hT.boundE j hj1 hjk y X hX hy Ψ h hd
  boundM := fun j hj1 hjk x X hX hx Ψ b g ⟨h, hd, hb⟩ hg => by
    show vn (Tm.M j x X Ψ ((nuIdeal L k (ν k) j : ℂ)⁻¹ • b) g) < _
    rw [hb, inv_smul_smul_fld (hν j hj1 hjk).ne']
    exact hT.boundM j hj1 hjk x X hX hx Ψ h g hd hg
  dbE := hdb
  refJet := hjet

end Balaban.SmallField.Def6v2
