/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepTowerRotLabels
public import Balaban.Inhabited.StepTowerRotFields
public import Balaban.Inhabited.StepTowerNewLevelE0Sum
public import Balaban.SmallField.IrrelTorus

/-!
# The system of the new level's coefficient (`NewLevelSystem`, `NewLevelFormula`)

Route R-LOC of `notes/phase1/SPINE.md`, section "A4-1b (iii)", layer L2 (c): the objects from which
the class chain builds the coefficient `e` of the new level of a polymer expansion, with the
equations that define them, bundled so that the coefficient can be recomputed on another background
generating set.

* `DecFieldPin`, `DecSolPin`, `FkPin`: the defining properties of a decoupled background field, of a
  decoupled fluctuation field and of a background field of a generating set, on their domains.
* `ZeroSourceSystem`: the zero-source family: the direct terms `I` (the physical terms of the
  localization expansion of the block energy at the decoupled fields `F₂`, `Sol₂`, with the formula
  of the source `val`), the family `A = labelActFamilyOn … I` of their activities and the
  zero-source family `A₀ = zeroSourceAct A 2` on the labels `thickLabels I.𝒴 I.dom`.
* `OldTermSystem`: the inherited levels: the old terms `Eτ` with their domains, generating sets and
  the pins of the decoupled fields used to localize them.
* `NewLevelSystem S C z Jr`: the activities (zero-source, thick, extended by zero to the root-union
  labels), the marks (the bridge marks of the decoupling pairs `F₁`, `Sol` and the marks `G₁` of the
  old terms) with their equations, and `NewLevelSystem.coeff`, the determinant part plus the
  interpolation coefficient of the marked cluster expansion (`newLevelDetBg`, `gsumCoeff`).
* `OldTermSettings`: the settings of the inherited levels at the step radius (a field `OS` of the
  system); `NewLevelConsts`, `NewLevelSystem.HasConsts`: the constants of a system.
* `NewLevelFormula S C z Jr K e`: `e` is the coefficient of a system with the constants `K` on the
  step chart.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Fluctuation Balaban.Multiscale Balaban.Background Balaban.Localization
  Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited Balaban.Polymer
  Balaban.SmallField Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep Matrix Metric Set
  MeasureTheory Balaban.Inhabited.MarkBudgetAudit Balaban.SmallField.Def6v2
  Balaban.SmallField.GsSpec Balaban.Analysis

section Pins

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- **The defining property of a decoupled background field**: on the union domain it is the field
of the decoupled background `IsDecBg`. -/
def DecFieldPin (S : StepSetting d L N₁ m₁ k N ϱ) (κ BG : ℝ)
    (F : DecParams S.G' × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ)) : Prop :=
  ∀ (s : DecParams S.G') (D : BgData S.G' N), (∀ P, ‖s P‖ < Real.exp κ) →
    InUnionDomainC S.G' (bgC0 d L N) (c7 d L N BG κ) S.ν D → ∀ (φ : S.G'.Ω 1 × Fin N → ℂ)
      (α : S.G'.Ω 1 → ℂ), IsDecBg S.G' (compWeight L S.a₁) S.ν (rho4 d L N BG κ) s D φ α →
      F (s, rawOf D) = (φ, α)

/-- **The defining property of a decoupled fluctuation field**: on the strict data (radii `δ₀`,
`δ₁`) it is the unique small solution of the decoupled fluctuation equation. -/
def DecSolPin (S : StepSetting d L N₁ m₁ k N ϱ) (κ BG₂ δ₀ δ₁ : ℝ)
    (Sol : Dec2.DecParams (coverOf S.G') × Edat (stepG d L N₁ m₁ k ϱ) N →
      ((stepG d L N₁ m₁ k ϱ).Ω 1 × Fin N → ℂ) × ((stepG d L N₁ m₁ k ϱ).Ω 1 → ℂ)) : Prop :=
  ∀ p : Dec2.DecParams (coverOf S.G') × Edat (stepG d L N₁ m₁ k ϱ) N,
    (∀ P, ‖p.1 P‖ < Real.exp κ) →
    StrictDataM (stepG d L N₁ m₁ k ϱ) N false δ₀ δ₁ p.2 →
      (Sol p).1 = dphi (stepG d L N₁ m₁ k ϱ) (Dec2.decG (coverOf S.G')
          (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) S.ν p.1) p.2.2.1 p.2.1
          (pertSource (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2)
          (Sol p).2 ∧
        Dec2.DecFixed (coverOf S.G') (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) S.ν p.1 false
          p.2.2.1 p.2.1
          (pertSource (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2)
          (Sol p).2 ∧
        Background.Small (stepG d L N₁ m₁ k ϱ) (Sol p).2
          (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Background.Small (stepG d L N₁ m₁ k ϱ) (Sol p).2
          (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds (stepG d L N₁ m₁ k ϱ) (Sol p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : (stepG d L N₁ m₁ k ϱ).Ω 1 → ℂ, Background.Small (stepG d L N₁ m₁ k ϱ) δα'
            (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf S.G') (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) S.ν p.1
            false p.2.2.1 p.2.1
            (pertSource (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) δα' →
          δα' = (Sol p).2)

/-- **The defining property of the background field of a generating set**: on the union domain it
is the background field and multiplier `bgFieldC`, `bgMultC`. -/
def FkPin (S : StepSetting d L N₁ m₁ k N ϱ) {ϱ₁ : ℝ}
    (Gk : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁)
    (Fk : RawData d L (N₁ * L ^ m₁) (k + 1) N → ((Gk).Ω 1 × Fin N → ℂ) × ((Gk).Ω 1 → ℂ)) :
    Prop :=
  ∀ D : BgData Gk N, InUnionDomainC Gk (bgC0 d L N) (bgC1 d L N) S.ν D →
    Fk (rawOf D) = (bgFieldC Gk (compWeight L S.a₁) S.ν (bgC0 d L N) D,
      bgMultC Gk (compWeight L S.a₁) S.ν (bgC0 d L N) D)

/-- **The formula of the zero-source terms**: the direct terms at a raw datum without source are
`-β ∑_z [Y ∈ polyDom_z] ∫ ω ∂_w³ evTerm_z(Y)` of the block energy at the decoupled fields `F₂`,
`Sol₂` (P6 Lemma 4.1, P3 (4.44)-(4.47)). -/
def ZeroSourceTermFormula (S : StepSetting d L N₁ m₁ k N ϱ)
    (F₂ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      DecParams S.G' × RawData d L (N₁ * L ^ m₁) (k + 1) N →
        (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ))
    (Sol₂ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf S.G') × Edat (stepG d L N₁ m₁ k ϱ) N →
        ((stepG d L N₁ m₁ k ϱ).Ω 1 × Fin N → ℂ) × ((stepG d L N₁ m₁ k ϱ).Ω 1 → ℂ))
    (Tf : Set (CTorus d L N₁ m₁ (k + 1)) → (S.U × Fin N → ℂ) × (S.U × Fin N → ℂ) →
      (S.U × Fin N → ℂ) × (S.U × Fin N → ℂ) → ℂ →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ) :
    Prop :=
        (∀ (Y : Set (CTorus d L N₁ m₁ (k + 1)))
          (x w : (S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)) (σ : ℂ)
          (Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N),
          Tf Y x w σ (Θ, 0) = -(S.β : ℂ) *
            ∑ z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))), if Y ∈ polyDom S.G'
                (LocalCover.nbhdF 1 (LocalCover.blockSite k z)) 1 k
                (LocalCover.fam 1 (LocalCover.blockSite k z)) then
              rayTerm (dl3 (evTerm
                (fun i : ParIdx S.G' (↑(LocalCover.nbhdF 1 (LocalCover.blockSite k z)) : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1)
                S.G' 1 (X1 S.G' 1 k (LocalCover.fam 1 (LocalCover.blockSite k z)))
                (fun u s => blockEnergyFun S.G' (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) S.ν k z
                  (F₂ z (extParams S.G' (↑(LocalCover.nbhdF 1 (LocalCover.blockSite k z)) : Set (CTorus d L N₁ m₁ (k + 1))) s, u.1))
                  (Sol₂ z (extParams S.G' (↑(LocalCover.nbhdF 1 (LocalCover.blockSite k z)) : Set (CTorus d L N₁ m₁ (k + 1))) s,
                    flEdat S.G' (stepG d L N₁ m₁ k ϱ) (F₂ z (extParams S.G' (↑(LocalCover.nbhdF 1 (LocalCover.blockSite k z)) : Set (CTorus d L N₁ m₁ (k + 1))) s, u.1))
                      u.1.1 (hatPsiF S.G' S.a₁ S.ν S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₂ z)
                        (extParams S.G' (↑(LocalCover.nbhdF 1 (LocalCover.blockSite k z)) : Set (CTorus d L N₁ m₁ (k + 1))) s) u.1 u.2))).1
                  (u.1, hatPsiF S.G' S.a₁ S.ν S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₂ z)
                    (extParams S.G' (↑(LocalCover.nbhdF 1 (LocalCover.blockSite k z)) : Set (CTorus d L N₁ m₁ (k + 1))) s) u.1 u.2)) Y) w.1) taylorWeight x.1 σ Θ
            else 0)

/-- **The formula of the source of the direct terms** (`val`): the Taylor remainder of the interaction
in the hat variable, `-β` times the ray source of the interaction plus `β` times the sum over the
sites of the source of the direct terms at the flux field. -/
def ZeroSourceValFormula (S : StepSetting d L N₁ m₁ k N ϱ) (κ BG₂ t : ℝ)
    (val : ((S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)) → ((S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)) →
      ℂ → (RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)) → ℂ) :
    Prop :=
          (∀ x w σ Θ, val x w σ Θ =
            (-(S.β : ℂ)) * raySrc3 (hatFun S.G' S.a₁ S.ν t S.hG'
              ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
              (interactionOne S.hG S.hG' (le_refl (k + 1)) S.a₁ S.ν t)) taylorWeight x.1 w.1 σ
                Θ.1 +
            (S.β : ℂ) * (∑ s : CTorus d L N₁ m₁ (k + 1) × Fin N, Θ.2 s.1 s.2 *
              dirTermSrc (hatFun S.G' S.a₁ S.ν t S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
                (onXi S.G' S.a₁ S.ν t
                  (fun D ψ' => svec (stepG d L N₁ m₁ k ϱ)
                    (flFieldOne S.G' (stepG d L N₁ m₁ k ϱ) BG₂ κ S.a₁ S.ν D ψ')
                      s.1 s.2)))
                (fun _ => (1 : ℂ)) x.2 w.2 σ Θ.1))

/-- **The zero-source system.**  The direct terms `I` of the physical expansion (domains `I.𝒴`,
terms `I.T`) with the source `val`, the decoupled fields `F₂`, `Sol₂` they are computed from and
their formulas.  The activity family of the direct terms is `ZeroSourceSystem.A` and the
zero-source family `ZeroSourceSystem.A₀ = zeroSourceAct A 2` on the labels
`ZeroSourceSystem.Lab₀ = thickLabels I.𝒴 I.dom`. -/
structure ZeroSourceSystem (S : StepSetting d L N₁ m₁ k N ϱ) (hp : 0 < S.p₁)
    (t p₁ κ BG BG₂ : ℝ) where
  /-- the amplitude of the direct terms -/
  εU : ℝ
  /-- the rate of the activities -/
  κH : ℝ
  /-- the radius of the hat variables of the carrier of the terms -/
  cψ : ℝ
  /-- the radius of the carrier of the terms -/
  Rr : ℝ
  /-- the entropy rate of the labels -/
  κ0 : ℝ
  /-- the source -/
  val : ((S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)) → ((S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)) →
    ℂ → (RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)) → ℂ
  /-- the direct terms -/
  I : DirectTerms S 1 hp (fun ψ => (ψ, ψ)) p₁ 2 εU κH
    (rawOf S.D', (0 : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)) (physSΛEta S S.a₁ S.ν t (1 / S.β))
    (physXW S cψ 2 2 Rr) val (physAgΘ S) (AgFDirPair S)
  hF : DirectTermsFamilyOn S 1 (physInclScaled N S (((1 / S.β : ℝ)) : ℂ)) I
    (physVq S S.a₁ S.ν t 1)
  hεU : 0 ≤ εU
  hN : L ^ 1 ∣ N₁
  hp₁ : 0 < p₁
  hκ0 : aEnt d L + 1 ≤ κ0
  /-- the decoupled background fields of the terms -/
  F₂ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
    DecParams S.G' × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ)
  /-- the decoupled fluctuation fields of the terms -/
  Sol₂ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
    Dec2.DecParams (coverOf S.G') × Edat (stepG d L N₁ m₁ k ϱ) N →
      ((stepG d L N₁ m₁ k ϱ).Ω 1 × Fin N → ℂ) × ((stepG d L N₁ m₁ k ϱ).Ω 1 → ℂ)
  hF₂ : ∀ z, DecFieldPin S κ BG (F₂ z)
  hSol₂ : ∀ z, DecSolPin S κ BG₂ (2 * (K4 d L N BG κ * (xiC1 d * t))) t (Sol₂ z)
  hT : ZeroSourceTermFormula S F₂ Sol₂ I.T
  hval : ZeroSourceValFormula S κ BG₂ t val

namespace ZeroSourceSystem

variable {S : StepSetting d L N₁ m₁ k N ϱ} {hp : 0 < S.p₁} {t p₁ κ BG BG₂ : ℝ}
  (Z : ZeroSourceSystem S hp t p₁ κ BG BG₂)

/-- **The activity family of the direct terms** (`labelActFamilyOn` of `I`). -/
noncomputable def A : physParam N S → ℂ → LabelAct (thickLabels Z.I.𝒴 Z.I.dom)
    (S.blockSplit 1 hp).Ωb (2 * Z.εU) Z.κH Z.κ0 (2 * (K0 d L Z.κ0 + 1)) :=
  labelActFamilyOn S 1 (physInclScaled N S (((1 / S.β : ℝ)) : ℂ)) Z.I Z.hF Z.hN Z.hp₁
    (by norm_num) Z.hεU Z.hκ0 (by have := K0_pos d L Z.κ0; linarith)

/-- The labels of the zero-source family: the domains of the direct terms. -/
noncomputable abbrev Lab₀ : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1
    (k + 1) Set.univ {Y // Y ∈ Z.I.𝒴} :=
  thickLabels Z.I.𝒴 Z.I.dom

/-- **The zero-source family**: `A⁰(θ, u) = u² A((θ.1, 0), u)` for `‖u‖ < 2`. -/
noncomputable def A₀ : physParam N S → ℂ → LabelAct Z.Lab₀ (S.blockSplit 1 hp).Ωb
    (2 ^ 2 * (2 * Z.εU)) Z.κH Z.κ0 (2 * (K0 d L Z.κ0 + 1)) :=
  zeroSourceAct Z.A 2 zero_le_two

end ZeroSourceSystem

/-- **The inherited levels.**  The old terms `Eτ` of the polymers `τ`, indexed by a finite type, the
generating sets `Gk τ`, `Gj τ` of their localization and the decoupled fields `F₁L τ`, `SolL τ`,
`FkL τ` they are evaluated at, with the pins of the fields; `κ, BG, BG₂, δ₁` are the constants of
the pins. -/
structure OldTermSystem (S : StepSetting d L N₁ m₁ k N ϱ) (t : ℝ) where
  /-- the index set of the old terms -/
  ι : Type
  fin : Fintype ι
  /-- the cover parameter -/
  m₀ : ℕ
  /-- the level of the term -/
  jL : ι → ℕ
  /-- the label cubes of the term -/
  X₁f : ι → Finset (CTorus d L N₁ m₁ (k + 1))
  /-- the cover set of the term -/
  𝒦X : ι → Set (CTorus d L N₁ m₁ (k + 1))
  /-- the polymer of the term (`X ∪ □(y)` for the label `(j, y, X)`), whose length enters the bound
  of the term -/
  XL : ι → Set (CTorus d L N₁ m₁ (k + 1))
  /-- the separation of the generating sets `Gk` -/
  ϱ₁ : ℝ
  Gk : ι → GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁
  Gj : ι → GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ
  /-- the old terms -/
  Eτ : ι → RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ
  F₁L : ι → DecParams S.G' × RawData d L (N₁ * L ^ m₁) (k + 1) N →
    (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ)
  SolL : ι → Dec2.DecParams (coverOf S.G') × Edat (stepG d L N₁ m₁ k ϱ) N →
    ((stepG d L N₁ m₁ k ϱ).Ω 1 × Fin N → ℂ) × ((stepG d L N₁ m₁ k ϱ).Ω 1 → ℂ)
  FkL : ∀ τ, RawData d L (N₁ * L ^ m₁) (k + 1) N → ((Gk τ).Ω 1 × Fin N → ℂ) × ((Gk τ).Ω 1 → ℂ)
  /-- the radius of the hat variable of the localization -/
  ρ : ℝ
  κ : ℝ
  BG : ℝ
  BG₂ : ℝ
  δ₁ : ℝ
  hF₁L : ∀ τ, DecFieldPin S κ BG (F₁L τ)
  hSolL : ∀ τ, DecSolPin S κ BG₂ (2 * (K4 d L N BG κ * (xiC1 d * t))) δ₁ (SolL τ)
  hFkL : ∀ τ, FkPin S (Gk τ) (FkL τ)

attribute [instance] OldTermSystem.fin

/-- **The settings of the inherited levels at the step radius** (the base premises of the class
chain, `StepTowerG.e0CoeffFamily_class_of_families_core_onSet_agree_phi_formula`): the background
and fluctuation settings of each old term (`BgSetting`, `FlSetting` with the step's level-`k` set,
constants `(c_B, r₀, δ₃)` and `(K_c, C_χ, c₂, δ_fl)`), its covering setup on the polymer `O.XL τ`, the
frozen region `X₁f τ = X1`, the trees realizing the length of `O.XL τ`, the analyticity of the
background field `FkL τ` of its generating set, and `L^{m₀} ∣ N₁`. -/
structure OldTermSettings (S : StepSetting d L N₁ m₁ k N ϱ) (t : ℝ) (O : OldTermSystem S t) where
  cB : ℝ
  r₀ : ℝ
  δ₃ : ℝ
  Kc : ℝ
  Cx : ℝ
  c₂ : ℝ
  δfl : ℝ
  X₀ : O.ι → Finset (CTorus d L N₁ m₁ (k + 1))
  hB : ∀ τ, BgSetting N S.G' (O.Gk τ) (O.Gj τ) S.a₁ S.ν cB O.BG O.κ r₀ t δ₃ (X₀ τ) (O.X₁f τ)
    (O.jL τ)
  hF : ∀ τ, FlSetting N S.G' (O.Gk τ) (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν O.κ O.BG t δ₃ Kc Cx c₂ O.BG₂
    O.δ₁ δfl (O.X₁f τ)
  hcov : ∀ τ, CovSetup S.G' O.m₀ (O.jL τ) (O.XL τ) (O.𝒦X τ)
  hX₁ : ∀ τ, (↑(O.X₁f τ) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 S.G' O.m₀ (O.jL τ) (O.𝒦X τ)
  hopt : ∀ τ, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
    (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
    ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ O.XL τ) ∧ MeetsOne O.m₀ (O.jL τ) (O.𝒦X τ) W₀ ∧
      bondCost (scaleW L O.m₀ m₁ (O.jL τ)) E₀ = treeLenCovOne O.m₀ (O.jL τ) (O.XL τ)
  hFkan : ∀ τ, AnalyticOnNhd ℂ (O.FkL τ) {p | ∃ D : BgData (O.Gk τ) N,
    InUnionDomainC (O.Gk τ) (bgC0 d L N) (bgC1 d L N) S.ν D ∧ p = (D.Ψ, D.h)}
  hN : L ^ O.m₀ ∣ N₁

/-- **The constants of a system of the new level** (the record the class chain exposes with
`NewLevelFormula`): those of the decoupling pairs `(κ, B_G, B_{G₂})`, the radius `p₁` of the hat
variable and the rate `κ₀` of the zero-source family; the constants `(κ, B_G, B_{G₂}, δ₁, ρ, m₀)` of
the inherited levels; and the constants `(c_B, r₀, δ₃, K_c, C_χ, c₂, δ_fl)` of their settings. -/
structure NewLevelConsts where
  κ : ℝ
  BG : ℝ
  BG₂ : ℝ
  p₁ : ℝ
  κ0 : ℝ
  κO : ℝ
  BGO : ℝ
  BG₂O : ℝ
  δ₁O : ℝ
  ρO : ℝ
  m₀O : ℕ
  cB : ℝ
  r₀ : ℝ
  δ₃ : ℝ
  Kc : ℝ
  Cx : ℝ
  c₂ : ℝ
  δfl : ℝ

open Classical in
/-- **The system of the coefficient of the new level.**  For the step `S`, the class `C` and the
root `z`, with the joint representation `Jr` at the radius `t`: the zero-source system `Z` and the
inherited levels `O`; the thick activities `AC` of the domains `𝒴C` of the inherited polymers
(`hAC`: on the chart they are the explicit family `H` of the localized old terms `hH`); the marks
`G₁` of the old terms (`hG₁`) and the bridge marks of the decoupling pairs `F₁`, `Sol` (`hF₁`,
`hSol`), both local (`hG₁dep`, `hbrdep`); and the old terms are the old terms of `C` (`hEJ`: they
sum to the inherited energy). -/
structure NewLevelSystem (S : StepSetting d L N₁ m₁ k N ϱ) (C : StepClass d L N₁ m₁ k N ϱ)
    (z : RootIdx d L N₁ m₁ (k + 1)) {t pp : ℝ} (Jr : S.JointRep t pp) where
  hp : 0 < S.p₁
  /-- the radius of the hat variable -/
  p₁ : ℝ
  /-- the constants of the decoupling pairs -/
  κ : ℝ
  BG : ℝ
  BG₂ : ℝ
  Z : ZeroSourceSystem S hp t p₁ κ BG BG₂
  O : OldTermSystem S t
  /-- the settings of the inherited levels at the step radius -/
  OS : OldTermSettings S t O
  hEJ : ∀ D : BgData S.G' N, XiCData S.G' S.a S.ν (k + 1) 1 t D → ∀ w : S.EC,
    Jr.EJ C (rawOf D, w) = ∑ τ, O.Eτ τ (Jr.PJ (O.jL τ) (rawOf D, w))
  /-- the marks of the old terms -/
  G₁ : physParam N S →
    {q // q ∈ markedIdx (fun _ : O.ι => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1))))
      (fun τ => polyDom S.G' (O.X₁f τ) O.m₀ (O.jL τ) (O.𝒦X τ)) z} →
    ℂ → (∀ b, (S.blockSplit 1 hp).Ωb b) → ℂ
  hG₁ : ∀ θ q u Φ, G₁ θ q u Φ =
    if (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
        XiCRaw S.G' (compWeight L S.a₁) S.ν (k + 1) 1 t ∧ ‖u‖ < corrU then
      (S.β : ℂ) * deriv (fun t' : ℂ => evDec (O.X₁f q.1.1) O.m₀ (O.jL q.1.1) (O.𝒦X q.1.1) S.a₁ S.ν
        S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (O.F₁L q.1.1) (O.SolL q.1.1)
        (eTermFun S.G' (O.Gk q.1.1) (O.Gj q.1.1) (stepG d L N₁ m₁ k ϱ)
          (compWeight L S.a₁) (O.FkL q.1.1)
          (fun r => (S.β : ℂ)⁻¹ * O.Eτ q.1.1 r))
        (S.blockU z) u t' q.1.2
        ((θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N), S.hatOf 1 O.ρ hp Φ)) 0
    else 0
  /-- the domains of the thick activities -/
  𝒴C : Finset (Set (CTorus d L N₁ m₁ (k + 1)))
  h𝒴 : 𝒴C = Finset.univ.biUnion fun τ => polyDom S.G' (O.X₁f τ) O.m₀ (O.jL τ) (O.𝒦X τ)
  h𝒴dj : ∀ Y ∈ 𝒴C, IsDj 1 (k + 1) Y
  /-- the explicit thick activities of the localized old terms -/
  H : physParam N S → {Y // Y ∈ 𝒴C} → ℂ → (∀ b, (S.blockSplit 1 hp).Ωb b) → ℂ
  hH : ∀ θ Y u Φ, H θ Y u Φ =
    if (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
        XiCRaw S.G' (compWeight L S.a₁) S.ν (k + 1) 1 t ∧ ‖u‖ < corrU then
      ∑ τ, if Y.1 ∈ polyDom S.G' (O.X₁f τ) O.m₀ (O.jL τ) (O.𝒦X τ) then
        (S.β : ℂ) * (evDec (O.X₁f τ) O.m₀ (O.jL τ) (O.𝒦X τ) S.a₁ S.ν S.hG'
          ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (O.F₁L τ) (O.SolL τ)
          (eTermFun S.G' (O.Gk τ) (O.Gj τ) (stepG d L N₁ m₁ k ϱ)
            (compWeight L S.a₁) (O.FkL τ)
            (fun r => (S.β : ℂ)⁻¹ * O.Eτ τ r)) (S.blockU z) u 0
            Y.1 ((θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N), S.hatOf 1 O.ρ hp Φ) -
          evDec (O.X₁f τ) O.m₀ (O.jL τ) (O.𝒦X τ) S.a₁ S.ν S.hG'
          ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (O.F₁L τ) (O.SolL τ)
          (eTermFun S.G' (O.Gk τ) (O.Gj τ) (stepG d L N₁ m₁ k ϱ)
            (compWeight L S.a₁) (O.FkL τ)
            (fun r => (S.β : ℂ)⁻¹ * O.Eτ τ r)) (S.blockU z) 0 0
            Y.1 ((θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N), S.hatOf 1 O.ρ hp Φ))
      else 0
    else 0
  /-- the amplitude of the thick activities -/
  εC : ℝ
  hεC : 0 ≤ εC
  AC : physParam N S → ℂ → LabelAct (thickLabels (m₀ := 1) (j := k + 1) 𝒴C h𝒴dj)
    (S.blockSplit 1 hp).Ωb εC Z.κH Z.κ0 (K0 d L Z.κ0)
  hAC : ∀ θ ∈ physV S S.a₁ S.ν t, ∀ u Y, (AC θ u).H Y = H θ Y u
  hZ : ZeroSourceFields S hp Jr Z.Lab₀ Z.A₀
  hL : 2 ≤ L
  hκ02 : aEnt d L + 2 ≤ Z.κ0
  hdomC : ∀ τ, ∀ Y ∈ polyDom S.G' (O.X₁f τ) O.m₀ (O.jL τ) (O.𝒦X τ), IsDj 1 (k + 1) Y
  hdomE : ∀ b, ∀ Y ∈ e1DomG S b, IsDj 1 (k + 1) Y
  /-- the decoupling pairs of the bridge marks -/
  F₁ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) × Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
    DecParams S.G' × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ)
  Sol : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) × Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
    Dec2.DecParams (coverOf S.G') × Edat (stepG d L N₁ m₁ k ϱ) N →
      ((stepG d L N₁ m₁ k ϱ).Ω 1 × Fin N → ℂ) × ((stepG d L N₁ m₁ k ϱ).Ω 1 → ℂ)
  hF₁ : ∀ b, DecFieldPin S κ BG (F₁ (z, b))
  hSol : ∀ b, DecSolPin S κ BG₂ (2 * (K4 d L N BG κ * (xiC1 d * t))) t (Sol (z, b))
  /-- the locality of the marks of the old terms: the mark of `q` depends only on the blocks of its
  bridge -/
  hG₁dep : ∀ θ q u, DepOn (blocksOf 1 (k + 1) Set.univ (bridge 1 z q.1.2)) (G₁ θ q u)
  /-- the locality of the bridge marks: the mark of the bridge `i` depends only on its blocks -/
  hbrdep : ∀ θ (i : {Y' // Y' ∈ bridgeFamily 1
      (fun _ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) =>
        (Set.univ : Set (CTorus d L N₁ m₁ (k + 1)))) (e1DomG S) z}) u,
    DepOn (blocksOf 1 (k + 1) Set.univ i.1)
      (e1MarkGParamG S (fun b => F₁ (z, b)) (fun b => Sol (z, b)) p₁ hp z t θ i u)

namespace NewLevelSystem

variable {S : StepSetting d L N₁ m₁ k N ϱ} {C : StepClass d L N₁ m₁ k N ϱ}
  {z : RootIdx d L N₁ m₁ (k + 1)} {t pp : ℝ} {Jr : S.JointRep t pp}
  (NS : NewLevelSystem S C z Jr)

/-- The labels of the thick activities extended by zero to the root-union labels of the old
domains. -/
noncomputable abbrev thickCommonLabels :=
  commonLabels (thickLabels (m₀ := 1) (j := k + 1) NS.𝒴C NS.h𝒴dj) NS.Z.hN NS.hL
    (fun _ : NS.O.ι => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1))))
    (fun τ => polyDom S.G' (NS.O.X₁f τ) NS.O.m₀ (NS.O.jL τ) (NS.O.𝒦X τ)) NS.hdomC

/-- The index type of the labels of the sum of the zero-source and the thick activities. -/
abbrev Lb1 : Type :=
  {Y // Y ∈ NS.Z.I.𝒴} ⊕ ({Y // Y ∈ NS.𝒴C} ⊕ RootUnionLb 1
    (fun _ : NS.O.ι => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1))))
    (fun τ => polyDom S.G' (NS.O.X₁f τ) NS.O.m₀ (NS.O.jL τ) (NS.O.𝒦X τ)))

/-- The labels of the sum of the zero-source and the thick activities. -/
noncomputable abbrev Lab1 : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1
    (k + 1) Set.univ NS.Lb1 := NS.Z.Lab₀.sum NS.thickCommonLabels

/-- The common labels of all roots: the labels of the activities and the root-union labels of the
bridges of the domains of the step. -/
noncomputable abbrev Lab := commonLabels NS.Lab1 NS.Z.hN NS.hL
    (fun _ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1))))
    (e1DomG S) NS.hdomE

/-- The thick activities extended by zero. -/
noncomputable abbrev thickCommonAct :=
  commonAct NS.AC NS.Z.hN NS.hL
    (fun _ : NS.O.ι => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1))))
    (fun τ => polyDom S.G' (NS.O.X₁f τ) NS.O.m₀ (NS.O.jL τ) (NS.O.𝒦X τ)) NS.hdomC NS.hεC NS.hκ02

/-- The sum of the zero-source and the thick activities. -/
noncomputable abbrev A1 : physParam N S → ℂ → LabelAct NS.Lab1 (S.blockSplit 1 NS.hp).Ωb
    (max (2 ^ 2 * (2 * NS.Z.εU)) NS.εC) NS.Z.κH NS.Z.κ0
    (2 * (K0 d L NS.Z.κ0 + 1) + (K0 d L NS.Z.κ0 + rootUnionK d L 1 m₁ NS.Z.κ0)) :=
  fun θ u => (NS.Z.A₀ θ u).sum (NS.thickCommonAct θ u)

/-- **The activities of the new level**: the sum of the zero-source and the thick activities,
extended by zero to the root-union labels of the bridges. -/
noncomputable abbrev A :=
  commonAct NS.A1 NS.Z.hN NS.hL
    (fun _ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1))))
    (e1DomG S) NS.hdomE
    (le_max_of_le_right NS.hεC) NS.hκ02

/-- The label of the bridge domain of the mark of the old term `q`. -/
noncomputable def y1 (q : {q // q ∈ markedIdx
      (fun _ : NS.O.ι => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1))))
      (fun τ => polyDom S.G' (NS.O.X₁f τ) NS.O.m₀ (NS.O.jL τ) (NS.O.𝒦X τ)) z}) :
    NS.Lb1 ⊕ RootUnionLb 1 (fun _ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) =>
      (Set.univ : Set (CTorus d L N₁ m₁ (k + 1)))) (e1DomG S) :=
  Sum.inl (Sum.inr (Sum.inr ⟨z, ⟨bridge 1 z q.1.2, bridge_mem_bridgeFamily_of_mem q.2⟩⟩))

/-- The anchors of the bridge marks: the root-union labels of the bridges of `z`, and the labels of
the bridge domains of the marks of the old terms. -/
noncomputable def y0 :
    ({Y' // Y' ∈ bridgeFamily 1 (fun _ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) =>
      (Set.univ : Set (CTorus d L N₁ m₁ (k + 1)))) (e1DomG S) z} ⊕
      {q // q ∈ markedIdx (fun _ : NS.O.ι => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1))))
        (fun τ => polyDom S.G' (NS.O.X₁f τ) NS.O.m₀ (NS.O.jL τ) (NS.O.𝒦X τ)) z}) →
      NS.Lb1 ⊕ RootUnionLb 1 (fun _ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) =>
        (Set.univ : Set (CTorus d L N₁ m₁ (k + 1)))) (e1DomG S) :=
  Sum.elim (commonAnchor NS.Lb1 (fun _ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) =>
    (Set.univ : Set (CTorus d L N₁ m₁ (k + 1)))) (e1DomG S) z) NS.y1

/-- **The marks of the new level**: the bridge marks of the decoupling pairs `F₁`, `Sol` and the
marks `G₁` of the old terms. -/
noncomputable def G (θ : physParam N S) :
    ({Y' // Y' ∈ bridgeFamily 1 (fun _ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) =>
      (Set.univ : Set (CTorus d L N₁ m₁ (k + 1)))) (e1DomG S) z} ⊕
      {q // q ∈ markedIdx (fun _ : NS.O.ι => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1))))
        (fun τ => polyDom S.G' (NS.O.X₁f τ) NS.O.m₀ (NS.O.jL τ) (NS.O.𝒦X τ)) z}) →
      ℂ → (∀ b, (S.blockSplit 1 NS.hp).Ωb b) → ℂ :=
  Sum.elim (fun i u Φ => e1MarkGParamG S (fun b => NS.F₁ (z, b)) (fun b => NS.Sol (z, b))
    NS.p₁ NS.hp z t θ i u Φ) (NS.G₁ θ)

/-- **The locality of the marks of the new level**: the mark of the anchor `i` depends only on the
blocks of the site set of its label (the fields `hbrdep`, `hG₁dep`). -/
theorem G_dep (θ : physParam N S)
    (i : {Y' // Y' ∈ bridgeFamily 1 (fun _ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) =>
      (Set.univ : Set (CTorus d L N₁ m₁ (k + 1)))) (e1DomG S) z} ⊕
      {q // q ∈ markedIdx (fun _ : NS.O.ι => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1))))
        (fun τ => polyDom S.G' (NS.O.X₁f τ) NS.O.m₀ (NS.O.jL τ) (NS.O.𝒦X τ)) z}) (u : ℂ) :
    DepOn (blocksOf 1 (k + 1) Set.univ (NS.Lab.ysite (NS.y0 i))) (NS.G θ i u) := by
  rcases i with i | q
  · exact NS.hbrdep θ i u
  · exact NS.hG₁dep θ q u

/-- **The coefficient of the system** (P3 (4.41)-(4.47), P4 (2.56)): the determinant part of the
block of the root plus the interpolation coefficient of the marked cluster expansion with the
activities `A` and the marks `G` (`newLevelDetBg`, `gsumCoeff`). -/
noncomputable def coeff (θ : physParam N S)
    (T' : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1)
      Set.univ)) : ℂ :=
  newLevelDetBg S.G' (compWeight L 1) 1 S.ν (rho4 d L N NS.BG NS.κ) (S.blockU z) θ T' +
    gsumCoeff (S.blockSplit 1 NS.hp).μ NS.Lab (NS.A θ) NS.y0 (NS.G θ) T'


/-- The constants of the system (`NewLevelConsts`). -/
def consts : NewLevelConsts :=
  ⟨NS.κ, NS.BG, NS.BG₂, NS.p₁, NS.Z.κ0, NS.O.κ, NS.O.BG, NS.O.BG₂, NS.O.δ₁, NS.O.ρ, NS.O.m₀,
    NS.OS.cB, NS.OS.r₀, NS.OS.δ₃, NS.OS.Kc, NS.OS.Cx, NS.OS.c₂, NS.OS.δfl⟩

/-- **The system has the constants `K`.** -/
structure HasConsts (K : NewLevelConsts) : Prop where
  κ : NS.κ = K.κ
  BG : NS.BG = K.BG
  BG₂ : NS.BG₂ = K.BG₂
  p₁ : NS.p₁ = K.p₁
  κ0 : NS.Z.κ0 = K.κ0
  κO : NS.O.κ = K.κO
  BGO : NS.O.BG = K.BGO
  BG₂O : NS.O.BG₂ = K.BG₂O
  δ₁O : NS.O.δ₁ = K.δ₁O
  ρO : NS.O.ρ = K.ρO
  m₀O : NS.O.m₀ = K.m₀O
  cB : NS.OS.cB = K.cB
  r₀ : NS.OS.r₀ = K.r₀
  δ₃ : NS.OS.δ₃ = K.δ₃
  Kc : NS.OS.Kc = K.Kc
  Cx : NS.OS.Cx = K.Cx
  c₂ : NS.OS.c₂ = K.c₂
  δfl : NS.OS.δfl = K.δfl

/-- A system has its own constants (non-vacuity of `HasConsts`). -/
theorem hasConsts_consts : NS.HasConsts NS.consts :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end NewLevelSystem

/-- **The old terms are the irrelevant terms of the class** (weak form): the old term of `τ` is
the term `irrelTorus` of the terms `C.Tm` of the class at the cube `y τ` and the polymer `X τ` of
level `jL τ` (P1 (3.112)-(3.113)); nothing is said of the generating sets the terms are composed
on. -/
def OldTermsAreIrrelW (S : StepSetting d L N₁ m₁ k N ϱ) (C : StepClass d L N₁ m₁ k N ϱ) {t : ℝ}
    (O : OldTermSystem S t) : Prop :=
  O.m₀ = C.m₀ ∧ ∃ (i₀ i₁ : Fin N) (y : O.ι → CTorus d L N₁ m₁ (k + 1))
    (X : O.ι → Set (CTorus d L N₁ m₁ (k + 1))), ∀ τ r,
    O.Eτ τ r = irrelTorus C.m₀ C.Tm i₀ i₁ (O.jL τ) (y τ) (X τ) r.1 r.2

/-- **The old terms are the irrelevant terms of the class, composed on the class generating sets**
(ruling R13): the old term of `τ` is `irrelTorus` of `C.Tm` at the label `(jL τ, y τ, X τ)`
(`1 ≤ jL τ ≤ k`, `y τ ∈ X τ` aligned to `L^{jL τ}`, `X τ ∈ 𝒟_{jL τ}`), and it is composed on the
generating set `C.Tm.gs (jL τ) (X τ)` of the class (P1 (3.112)-(3.113), P3 (4.4)-(4.6)); its polymer
`O.XL τ` is `X τ ∪ □(y τ)`. -/
def OldTermsAreIrrel (S : StepSetting d L N₁ m₁ k N ϱ) (C : StepClass d L N₁ m₁ k N ϱ) {t : ℝ}
    (O : OldTermSystem S t) : Prop :=
  O.m₀ = C.m₀ ∧ ∃ (i₀ i₁ : Fin N) (y : O.ι → CTorus d L N₁ m₁ (k + 1))
    (X : O.ι → Set (CTorus d L N₁ m₁ (k + 1))),
    (∀ τ r, O.Eτ τ r = irrelTorus C.m₀ C.Tm i₀ i₁ (O.jL τ) (y τ) (X τ) r.1 r.2) ∧
    ∀ τ, O.Gj τ = C.Tm.gs (O.jL τ) (X τ) ∧ 1 ≤ O.jL τ ∧ O.jL τ ≤ k ∧
      Aligned (L ^ O.jL τ) (y τ) ∧ IsPolyDom C.m₀ (O.jL τ) (X τ) ∧ y τ ∈ X τ ∧
      O.XL τ = X τ ∪ box (cbase (cellSide L C.m₀ m₁ (O.jL τ)) (y τ) -
        natT fun _ => L / 2 * cellSide L C.m₀ m₁ (O.jL τ)) (L * cellSide L C.m₀ m₁ (O.jL τ))

theorem OldTermsAreIrrel.toW {S : StepSetting d L N₁ m₁ k N ϱ} {C : StepClass d L N₁ m₁ k N ϱ}
    {t : ℝ} {O : OldTermSystem S t} (h : OldTermsAreIrrel S C O) : OldTermsAreIrrelW S C O := by
  obtain ⟨hm, i₀, i₁, y, X, hE, -⟩ := h
  exact ⟨hm, i₀, i₁, y, X, hE⟩

/-- **`e` is the coefficient of a system with the given inherited levels `O` and constants `K`** on
the step chart. -/
def NewLevelFormulaFor (S : StepSetting d L N₁ m₁ k N ϱ) (C : StepClass d L N₁ m₁ k N ϱ)
    (z : RootIdx d L N₁ m₁ (k + 1)) {t pp : ℝ} (Jr : S.JointRep t pp) (O : OldTermSystem S t)
    (K : NewLevelConsts)
    (e : physParam N S → Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1
      (k + 1) Set.univ) → ℂ) : Prop :=
  ∃ NS : NewLevelSystem S C z Jr, NS.O = O ∧ NS.HasConsts K ∧
    ∀ θ ∈ physV S S.a₁ S.ν t, ∀ T', e θ T' = NS.coeff θ T'

/-- **`e` is the coefficient of a system of the class `C` with the constants `K`** (weak form) on
the step chart: the inherited levels are the irrelevant terms of `C` (`OldTermsAreIrrelW`); the
system carries the settings of the inherited levels (`NewLevelSystem.OS`) and its constants are those
of `K`. -/
def NewLevelFormulaW (S : StepSetting d L N₁ m₁ k N ϱ) (C : StepClass d L N₁ m₁ k N ϱ)
    (z : RootIdx d L N₁ m₁ (k + 1)) {t pp : ℝ} (Jr : S.JointRep t pp) (K : NewLevelConsts)
    (e : physParam N S → Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1
      (k + 1) Set.univ) → ℂ) : Prop :=
  ∃ NS : NewLevelSystem S C z Jr, OldTermsAreIrrelW S C NS.O ∧ NS.HasConsts K ∧
    ∀ θ ∈ physV S S.a₁ S.ν t, ∀ T', e θ T' = NS.coeff θ T'

/-- **`e` is the coefficient of a system of the class `C` with the constants `K`** on the step
chart: the inherited levels are the irrelevant terms of `C`, composed on the generating sets of the
class (`OldTermsAreIrrel`, ruling R13); the system carries the settings of the inherited levels
(`NewLevelSystem.OS`) and its constants are those of `K`. -/
def NewLevelFormula (S : StepSetting d L N₁ m₁ k N ϱ) (C : StepClass d L N₁ m₁ k N ϱ)
    (z : RootIdx d L N₁ m₁ (k + 1)) {t pp : ℝ} (Jr : S.JointRep t pp) (K : NewLevelConsts)
    (e : physParam N S → Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1
      (k + 1) Set.univ) → ℂ) : Prop :=
  ∃ NS : NewLevelSystem S C z Jr, OldTermsAreIrrel S C NS.O ∧ NS.HasConsts K ∧
    ∀ θ ∈ physV S S.a₁ S.ν t, ∀ T', e θ T' = NS.coeff θ T'

/-- **The class is in the regime of ruling R13** at the cube exponent `s` and the collar `r₀`: the
block-index margin of the composition on `𝔹_j(X̂)`
(`(5 L + 13) L^s + ⌊L/2⌋ L^{m₀} + r₀ L ≤ (L - 2) L^{m₀+1}`), `s` is the cube exponent `hatScale` of
the separation `ϱ` and is below `m₀`, and the generating sets of the class are the local sets
`𝔹_j(X̂)` (`HatSpec`). -/
def ClassHatCond (C : StepClass d L N₁ m₁ k N ϱ) (s : ℕ) (r₀ : ℝ) : Prop :=
  (((5 * L + 13) * L ^ s + L / 2 * L ^ C.m₀ : ℕ) : ℝ) + r₀ * L ≤
      (((L - 2 : ℕ)) : ℝ) * (L : ℝ) ^ (C.m₀ + 1) ∧
    hatScale L m₁ ϱ = s ∧ s < C.m₀ ∧
    ∀ j, 1 ≤ j → j ≤ k → ∀ X, IsPolyDom C.m₀ j X → HatSpec C.m₀ j X (C.Tm.gs j X)

theorem NewLevelFormula.toW {S : StepSetting d L N₁ m₁ k N ϱ} {C : StepClass d L N₁ m₁ k N ϱ}
    {z : RootIdx d L N₁ m₁ (k + 1)} {t pp : ℝ} {Jr : S.JointRep t pp} {K : NewLevelConsts}
    {e : physParam N S → Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1
      (k + 1) Set.univ) → ℂ}
    (h : NewLevelFormula S C z Jr K e) : NewLevelFormulaW S C z Jr K e := by
  obtain ⟨NS, hO, hK, h⟩ := h
  exact ⟨NS, hO.toW, hK, h⟩

theorem NewLevelFormulaW.of_for {S : StepSetting d L N₁ m₁ k N ϱ} {C : StepClass d L N₁ m₁ k N ϱ}
    {z : RootIdx d L N₁ m₁ (k + 1)} {t pp : ℝ} {Jr : S.JointRep t pp} {O : OldTermSystem S t}
    {K : NewLevelConsts}
    {e : physParam N S → Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1
      (k + 1) Set.univ) → ℂ}
    (hO : OldTermsAreIrrelW S C O) (h : NewLevelFormulaFor S C z Jr O K e) :
    NewLevelFormulaW S C z Jr K e := by
  obtain ⟨NS, rfl, hK, h⟩ := h
  exact ⟨NS, hO, hK, h⟩

theorem NewLevelFormula.of_for {S : StepSetting d L N₁ m₁ k N ϱ} {C : StepClass d L N₁ m₁ k N ϱ}
    {z : RootIdx d L N₁ m₁ (k + 1)} {t pp : ℝ} {Jr : S.JointRep t pp} {O : OldTermSystem S t}
    {K : NewLevelConsts}
    {e : physParam N S → Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1
      (k + 1) Set.univ) → ℂ}
    (hO : OldTermsAreIrrel S C O) (h : NewLevelFormulaFor S C z Jr O K e) :
    NewLevelFormula S C z Jr K e := by
  obtain ⟨NS, rfl, hK, h⟩ := h
  exact ⟨NS, hO, hK, h⟩

/-- `NewLevelFormula` along an equality of the constants. -/
theorem NewLevelFormula.congr_consts {S : StepSetting d L N₁ m₁ k N ϱ}
    {C : StepClass d L N₁ m₁ k N ϱ} {z : RootIdx d L N₁ m₁ (k + 1)} {t pp : ℝ}
    {Jr : S.JointRep t pp} {K K' : NewLevelConsts}
    {e : physParam N S → Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1
      (k + 1) Set.univ) → ℂ}
    (h : NewLevelFormula S C z Jr K e) (hK : K = K') : NewLevelFormula S C z Jr K' e :=
  hK ▸ h

/-- **The coefficient of a system is the coefficient of a system** (non-vacuity of
`NewLevelFormulaFor`: it holds for the family `NS.coeff` and the constants `NS.consts` of every
system, whose inhabitation for the physical step is the content of the formula theorems of the
class chain,
`StepTowerG.e0CoeffFamily_class_exists_tower_struct_step_collar_classEps_ren_rot_formula`). -/
theorem NewLevelSystem.formulaFor_coeff {S : StepSetting d L N₁ m₁ k N ϱ}
    {C : StepClass d L N₁ m₁ k N ϱ} {z : RootIdx d L N₁ m₁ (k + 1)} {t pp : ℝ}
    {Jr : S.JointRep t pp} (NS : NewLevelSystem S C z Jr) :
    NewLevelFormulaFor S C z Jr NS.O NS.consts NS.coeff :=
  ⟨NS, rfl, NS.hasConsts_consts, fun _ _ _ => rfl⟩

/-- The coefficient of a system whose inherited levels are the irrelevant terms of `C` satisfies
`NewLevelFormula` with the constants of the system. -/
theorem NewLevelSystem.formula_coeff {S : StepSetting d L N₁ m₁ k N ϱ}
    {C : StepClass d L N₁ m₁ k N ϱ} {z : RootIdx d L N₁ m₁ (k + 1)} {t pp : ℝ}
    {Jr : S.JointRep t pp} (NS : NewLevelSystem S C z Jr) (h : OldTermsAreIrrel S C NS.O) :
    NewLevelFormula S C z Jr NS.consts NS.coeff :=
  NewLevelFormula.of_for h NS.formulaFor_coeff

end Pins

end Balaban.Inhabited
