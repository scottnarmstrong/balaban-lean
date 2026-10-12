/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.Def6v2Bridge
public import Balaban.SmallField.RenormClassFamily
public import Balaban.SmallField.RenormAnisoBridgeInf

/-!
# The objects of the bridge Def-6 to I-6 with the background mass as a parameter

The landed bridge defines its data domains and the Reynolds-averaged term family through the
coefficients `(β, ν)` of the landed class, which enter only through the running-test mass
`Def6.bgMass L k (β k) (ν k)` of the analyticity domain `Ξ^c_j` (zero below the switch).  Here the
same objects are defined with the **solver mass `μ` as a parameter**:

* `liftDomInfM`: the data domain of the lifted family of `T∞` (landed `liftDomInf`);
* `ExtNM`, `ExtEvM`, `SuppM`, `FBM`, `ExtAllM`: the cut-off term of `T∞` on block states and its
  support (landed `ExtN`, `ExtEv`, `Supp`, `FB`, `ExtAll`);
* `avgFBM`, `avgBM`, `avgFamilyAM`, `avgDomM`: the Reynolds average over the cosets of the paving
  group, the averaged term family on the anisotropic tube and its data domain (landed `avgFB`,
  `avgB`, `avgFamilyA`, `avgDom`).

Each landed object is the new one at the mass `bgMass` (`liftDomInf_eq`, `FB_eq`, `avgB_eq`,
`avgFamilyA_eq`, `avgDom_eq`: definitional).  The second version of the class (Scheme A) uses them
at the complete mass `Rg.sfBgMass k`.  The family `liftInfA` of `T∞` itself and the polymers and
sizes `avgPolys`, `avgDist` do not involve the mass.
-/

@[expose] public section

namespace Balaban.SmallField.Def6v2

open Balaban Balaban.SmallField Balaban.Multiscale Balaban.Background Balaban.Localization
  Balaban.SmallField.Def6 Filter

variable {d L m₁ k N : ℕ} [NeZero L] {ϱ : ℝ}

section Defs

variable (P : Consts) (a : ℕ → ℝ) (μ : ℝ)
  (Tm : ∀ (N₁ : ℕ) [NeZero N₁], Terms d L N₁ m₁ k N ϱ) (j : ℕ)

/-- **The data domain of the lifted family of `T∞` at the solver mass `μ`** (landed
`Def6.liftDomInf`): the configurations `(ψ, b)`, `b = ν_j h`, such that for every polymer of `T∞`
containing the origin and every torus of the sequence on which it is a non-winding polymer, the
restriction to the polymer extends to torus fields in `Ξ^c_j(𝔹_j(Y); 1, ε_j)` at the mass `μ`.
Here `νk` is the mass coefficient `ν_k` of the source coordinate (`ν_j = nuIdeal L k νk j`). -/
def liftDomInfM (νk : ℝ) (i₀ : Fin N) : Set ((Site d → Spin N) × Spin N) :=
  {p | ∀ X' : Finset (Site d), (0 : Site d) ∈ X' →
    InfPoly (L := L) (m₁ := m₁) (k := k) P.m₀ j X' → ∀ n : ℕ,
    GoodAt L m₁ k P.m₀ j X' n →
    haveI : NeZero (torusSeq L P.m₀ n) := ⟨torusSeq_ne_zero P.m₀ n⟩
    ∃ (Ψ h : Fld d L (torusSeq L P.m₀ n) m₁ k N),
      (∀ x ∈ Ypoly (L := L) (N₁ := torusSeq L P.m₀ n) (m₁ := m₁) (k := k) j X',
        Ψ x = fieldOf j i₀ X' (pack X' p.1 p.2) x ∧
          h x = hOf (nuIdeal L k νk j) X' (pack X' p.1 p.2) x) ∧
      XiDom ((Tm (torusSeq L P.m₀ n)).gs j (Ypoly j X')) (aIdeal L k (a k)) μ j (P.eps d L j)
        Ψ h}

/-- `ψ, h` extend, on the torus `n` of the sequence, to a datum of `Ξ^c_j(𝔹_j(Y); 1, ε_j)` at the
solver mass `μ` which agrees with them on the lift `Y` of the polymer `X'` (landed `Def6.ExtN`). -/
def ExtNM (n : ℕ) (X' : Finset (Fin d → ℤ)) (ψ h : InfFld d N) : Prop :=
  ∃ (Ψ h' : Fld d L (torusSeq L P.m₀ n) m₁ k N),
    (∀ x ∈ Ypoly (L := L) (N₁ := torusSeq L P.m₀ n) (m₁ := m₁) (k := k) j X',
      Ψ x = pullFld j ψ x ∧ h' x = pullFld j h x) ∧
    XiDom ((Tm (torusSeq L P.m₀ n)).gs j (Ypoly j X')) (aIdeal L k (a k)) μ j (P.eps d L j) Ψ h'

/-- Eventually along the tori of the sequence the data extend into the analyticity domain at the
mass `μ` (landed `Def6.ExtEv`). -/
def ExtEvM (X' : Finset (Fin d → ℤ)) (ψ h : InfFld d N) : Prop :=
  ∀ᶠ n in atTop, ExtNM P a μ Tm j n X' ψ h

/-- The support of the cut-off term at the mass `μ` (landed `Def6.Supp`). -/
def SuppM (s : BSt d N) : Prop :=
  InfPoly (L := L) (m₁ := m₁) (k := k) P.m₀ j s.X ∧ s.y ∈ s.X ∧ ExtEvM P a μ Tm j s.X s.ψ s.h

open Classical in
/-- **The cut-off term of `T∞` on block states at the solver mass `μ`** (landed `Def6.FB`):
`ℰ_∞(y, X'; ψ, h)` for a polymer of `T∞` containing the centre `y`, on data that extend eventually
into the analyticity domain at the mass `μ`; `0` otherwise. -/
noncomputable def FBM (s : BSt d N) : ℂ :=
  if SuppM P a μ Tm j s then Einf P.m₀ Tm j s.y s.X s.ψ s.h else 0

/-- The data extend into the analyticity domain at the mass `μ` on every torus of the sequence on
which the polymer is good (landed `Def6.ExtAll`). -/
def ExtAllM (X' : Finset (Site d)) (ψ h : InfFld d N) : Prop :=
  ∀ n, GoodAt L m₁ k P.m₀ j X' n → ExtNM P a μ Tm j n X' ψ h

/-- **The Reynolds average over the cosets `G_j / H_j` of the cut-off term of `T∞`** at the mass
`μ` (landed `Def6.avgFB`). -/
noncomputable def avgFBM (s : BSt d N) : ℂ :=
  reynolds (KK d L P.m₀ m₁ j) (actG (d := d) (N := N) L j) (FBM P a μ Tm j) s

/-- **The Reynolds average over paving offsets and the point group of the term of `T∞`** at the
mass `μ`, as a function of the configuration of the centred polymer `X ∋ 0` (landed
`Def6.avgB`). -/
noncomputable def avgBM (i₀ : Fin N) (νj : ℝ) (X : Finset (Site d)) (c : Cfg d N X) : ℂ :=
  avgFBM P a μ Tm j ⟨X, 0, fieldInfOf L j i₀ X c, hInfOf νj X c⟩

/-- **The averaged centred term family on the anisotropic tube at the solver mass `μ`** (landed
`Def6.avgFamilyA`): the polymers `avgPolys` and sizes `avgDist` (independent of the mass), the term
the extension to `TubeAniso i₀ νj r` of the Reynolds average `avgBM`. -/
noncomputable def avgFamilyAM (i₀ : Fin N) (νj r : ℝ) : TermFamily d N where
  polys := avgPolys (d := d) L m₁ k P j
  dist := avgDist (d := d) L m₁ k P j
  term := fun X c => trickFnA i₀ νj r (avgBM P a μ Tm j i₀ νj X) c

/-- **The data domain of the averaged family at the solver mass `μ`** (landed `Def6.avgDom`): the
configurations `(ψ, b)` such that for every polymer of the family and every active translate, the
induced fields of `ℤ^d` extend into the analyticity domain at the mass `μ` on every good torus. -/
def avgDomM (i₀ : Fin N) (νj : ℝ) : Set ((Site d → Spin N) × Spin N) :=
  {p | ∀ X ∈ avgPolys (d := d) L m₁ k P j, ∀ t : Fin d → Fin (L ^ (P.m₀ + m₁)),
    InfPoly (L := L) (m₁ := m₁) (k := k) P.m₀ j (shiftFin (offs t) X) →
      ExtAllM P a μ Tm j (shiftFin (offs t) X)
        (fieldInfOf L j i₀ (shiftFin (offs t) X) (shiftCfg (offs t) X (pack X p.1 p.2)))
        (hInfOf νj (shiftFin (offs t) X) (shiftCfg (offs t) X (pack X p.1 p.2)))}

end Defs

/-! ### The landed objects are the new ones at the running-test mass -/

section Landed

variable (P : Consts) (β ν a : ℕ → ℝ)
  (Tm : ∀ (N₁ : ℕ) [NeZero N₁], Terms d L N₁ m₁ k N ϱ) (j : ℕ)

theorem liftDomInf_eq (i₀ : Fin N) :
    liftDomInf P β ν a Tm j i₀ =
      liftDomInfM P a (Def6.bgMass L k (β k) (ν k)) Tm j (ν k) i₀ := rfl

theorem ExtN_eq (n : ℕ) (X' : Finset (Fin d → ℤ)) (ψ h : InfFld d N) :
    ExtN P β ν a Tm j n X' ψ h = ExtNM P a (Def6.bgMass L k (β k) (ν k)) Tm j n X' ψ h := rfl

theorem FB_eq (s : BSt d N) :
    FB P β ν a Tm j s = FBM P a (Def6.bgMass L k (β k) (ν k)) Tm j s := rfl

theorem avgB_eq (i₀ : Fin N) (νj : ℝ) (X : Finset (Site d)) (c : Cfg d N X) :
    avgB P β ν a Tm j i₀ νj X c =
      avgBM P a (Def6.bgMass L k (β k) (ν k)) Tm j i₀ νj X c := rfl

/-- The landed averaged family is the averaged family at the running-test mass `bgMass`. -/
theorem avgFamilyA_eq (i₀ : Fin N) (νj r : ℝ) :
    avgFamilyA P β ν a Tm j i₀ νj r =
      avgFamilyAM P a (Def6.bgMass L k (β k) (ν k)) Tm j i₀ νj r := rfl

/-- The landed data domain of the averaged family is the data domain at the mass `bgMass`. -/
theorem avgDom_eq (i₀ : Fin N) (νj : ℝ) :
    avgDom P β ν a Tm j i₀ νj = avgDomM P a (Def6.bgMass L k (β k) (ν k)) Tm j i₀ νj := rfl

end Landed

/-! ### The objects do not involve the radius function of `χ_k` -/

section NoChi

variable (P : Consts) (a : ℕ → ℝ) (μ : ℝ)
  (Tm : ∀ (N₁ : ℕ) [NeZero N₁], Terms d L N₁ m₁ k N ϱ) (j : ℕ)

theorem liftDomInfM_noChi (νk : ℝ) (i₀ : Fin N) :
    liftDomInfM P.noChi a μ Tm j νk i₀ = liftDomInfM P a μ Tm j νk i₀ := rfl

theorem avgFamilyAM_noChi (i₀ : Fin N) (νj r : ℝ) :
    avgFamilyAM P.noChi a μ Tm j i₀ νj r = avgFamilyAM P a μ Tm j i₀ νj r := rfl

theorem avgDomM_noChi (i₀ : Fin N) (νj : ℝ) :
    avgDomM P.noChi a μ Tm j i₀ νj = avgDomM P a μ Tm j i₀ νj := rfl

theorem liftInfA_noChi (i₀ : Fin N) (νj r : ℝ) :
    liftInfA (L := L) (m₁ := m₁) (k := k) P.noChi Tm j i₀ νj r =
      liftInfA (L := L) (m₁ := m₁) (k := k) P Tm j i₀ νj r := rfl

theorem liftInf_noChi (i₀ : Fin N) (νj r : ℝ) :
    liftInf (L := L) (m₁ := m₁) (k := k) P.noChi Tm j i₀ νj r =
      liftInf (L := L) (m₁ := m₁) (k := k) P Tm j i₀ νj r := rfl

theorem anisoRadius_noChi (N : ℕ) :
    anisoRadius d L N P.noChi j = anisoRadius d L N P j := rfl

theorem liftRadius_noChi (N : ℕ) :
    liftRadius d L N P.noChi j = liftRadius d L N P j := rfl

end NoChi

end Balaban.SmallField.Def6v2
