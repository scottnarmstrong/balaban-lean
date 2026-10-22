/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.LocalIsoFF
public import Balaban.Polymer.TwoTorusEv
public import Balaban.Fluctuation.NewLevelTermsBgLocal
import Mathlib.Tactic.Linarith

/-!
# Local generating sets on two tori: the recomputed terms `evDecBg`

The term `evDecBg … Y` of the step's expansion (on the level set `GA = levelGS (k + 1)`, cover data
`(m₀, j, 𝒦_X)`, region `X₁`) recomputed on a local generating set `Gb` with the canonical transport,
and the term of `bm '' Y` on the second torus recomputed on `Gb'`, agree when `Gb`, `Hm` are carried
onto `Gb'`, `Hm'` by the box map.  The step's expansion is compared by the landed whole-lattice
lemmas (`evTerm_boxMap_of_eq` for the connected families, `coef_relabel_injOn` for their
coefficients, `extS_extParams_boxMap_of_eq` for the extended parameters); the functional at the
cut points is the exact local transport `OmegaIso.FFmarkedBg_canon_eq`.

* `OmegaIso.resZ_eq`: the restrictions of corresponding hat variables to the unit points;
* `OmegaIso.evDecBg_canon_twoTorus_core`: the terms on two tori, from the analyticity of the first
  functional in the cut parameters (`hFan`) and the premises of the decoupling pairs on sets of
  parameters containing the transported parameters of the polydisc (`hF`, `hF'`, `hex`, `hv`, `hv'`;
  all one-torus facts).
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Polymer.LocalIso

open Balaban Balaban.Localization Balaban.Background Balaban.Multiscale Balaban.Polymer
  Balaban.Polymer.TwoTorusStep Balaban.Fluctuation Balaban.SmallField Balaban.SmallField.Def6
  Balaban.Analysis Matrix MeasureTheory

variable {d L N₁ N₁' m₁ k N : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ ϱb ϱb' ϱm ϱm' : ℝ}

set_option hygiene false in
local notation "bk" => boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1))
set_option hygiene false in
local notation "ck" => (Prod.map id bk : ℕ × CTorus d L N₁ m₁ (k + 1) → ℕ × CTorus d L N₁' m₁ (k + 1))
set_option hygiene false in
local notation "GA" => levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  (k + 1) le_rfl
set_option hygiene false in
local notation "GB" => levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  (k + 1) le_rfl
set_option hygiene false in
local notation "ρ₁" => R + (3 * L ^ (k + 1 + m₁) + 3 * L ^ (k + 1 + 2)) + L ^ (k + 1 + m₁)

namespace OmegaIso

variable {Gb : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱb}
  {Gb' : GeneratingSet d L (N₁' * L ^ m₁) (k + 1) ϱb'}
  {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
  {Hm' : GeneratingSet d L (N₁' * L ^ m₁) (k + 1) ϱm'} {ρ : ℕ}

/-- **The restrictions of corresponding hat variables to the unit points of `Gb`, `Gb'`.** -/
theorem resZ_eq (hI : OmegaIso Gb Gb' ρ) (hGA : IsLevel (GA) (k + 1))
    (hGB : IsLevel (GB) (k + 1)) {ψh : unitPts (GA) × Fin N → ℂ}
    {ψh' : unitPts (GB) × Fin N → ℂ}
    (hhat : ∀ x, InBox d ρ ((N₁ * L ^ m₁) * L ^ (k + 1)) x →
      ∀ i, ψh' (unitPt hGB (bk x), i) = ψh (unitPt hGA x, i))
    (b : unitPts Gb) (i : Fin N) :
    resZ (GB) Gb' ψh' (hI.unitEquiv b, i) = resZ (GA) Gb ψh (b, i) := by
  obtain ⟨x, hx⟩ := exists_site b
  rw [resZ_apply, resZ_apply]
  simp only [dite_eq_left (mem_unitPts_of_isLevel hGB _), dite_eq_left (mem_unitPts_of_isLevel hGA _)]
  have h1 : (⟨((hI.unitEquiv b : unitPts Gb') : UnitTorus d L N₁' m₁ k),
      mem_unitPts_of_isLevel hGB _⟩ : unitPts (GB)) = unitPt hGB (bk (x : CTorus d L N₁ m₁ (k + 1))) :=
    Subtype.ext (by rw [hI.unitEquiv_site hx, coe_e]; rfl)
  have h2 : (⟨((b : unitPts Gb) : UnitTorus d L N₁ m₁ k), mem_unitPts_of_isLevel hGA _⟩ :
      unitPts (GA)) = unitPt hGA (x : CTorus d L N₁ m₁ (k + 1)) :=
    Subtype.ext (by rw [← hx]; rfl)
  rw [h1, h2]
  exact hhat x (hI.boxG x x.2) i

/-- **The recomputed terms on two tori** (core).  Let `Gb`, `Hm` be carried onto `Gb'`, `Hm'` by
the box map (`OmegaIso` with the radius `ρ ≤ R`); the step's covering setups on the two tori with
`X₁` and its image (in the box of radius `R`), the label `Y` in that box; data `D`, `D'`
corresponding on the box of radius `ρ + 1`, hat variables corresponding at the sites of the box
of radius `ρ` (`hhat`), the mask `Zm` and its image.  Let the first marked functional be analytic in
the cut parameters on the polydisc of radius `e^κ` (`hFan`), and at every parameter of sets `Sg`, `Sg'`
containing the transported parameters of the polydisc (`hSg`, `hSg'`) let the decoupling pairs have
their properties (`hF`, `hF'`, `hex`, `hv`, `hv'`; the point triples lie in the realizable sets `Rl`,
`Rl'`), and `Φ'`, `Φ` agree on corresponding realizable inputs (`hΦ`).  Then the terms `evDecBg` of `bm '' Y` on the
second torus and of `Y` on the first agree.  Margins: those of `evTerm_boxMap_of_eq` (`hnF`) and of
`extS_extParams_boxMap_of_eq` (`hnS`). -/
theorem evDecBg_canon_twoTorus_core (hI : OmegaIso Gb Gb' ρ) (hH : OmegaIso Hm Hm' ρ)
    (hGA : IsLevel (GA) (k + 1)) (hGB : IsLevel (GB) (k + 1)) (a₁ ν ρb : ℝ) (cc : ℂ)
    {κ : ℝ} (hκ : 0 < κ) {m₀ j : ℕ} {X 𝒦X : Set (CTorus d L N₁ m₁ (k + 1))}
    {X' 𝒦X' : Set (CTorus d L N₁' m₁ (k + 1))} {X₁f : Finset (CTorus d L N₁ m₁ (k + 1))}
    (hcov : CovSetup (GA) m₀ j X 𝒦X)
    (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) = X1 (GA) m₀ j 𝒦X)
    (hcov' : CovSetup (GB) m₀ j X' 𝒦X')
    (hX₁' : (↑(X₁f.image bk) : Set (CTorus d L N₁' m₁ (k + 1))) = X1 (GB) m₀ j 𝒦X')
    {R : ℕ} (hρR : ρ ≤ R) (hX₁R : ∀ x ∈ X₁f, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    {Y : Set (CTorus d L N₁ m₁ (k + 1))}
    (hYR : ∀ y ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) y)
    (hnS : 2 * (ρ₁) + 5 * (L * cellSide L 0 m₁ (k + 1)) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnS' : 2 * (ρ₁) + 5 * (L * cellSide L 0 m₁ (k + 1)) < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hnF : 2 * R + 5 * (L * cellSide L m₀ m₁ (k + 1)) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnF' : 2 * R + 5 * (L * cellSide L m₀ m₁ (k + 1)) < (N₁' * L ^ m₁) * L ^ (k + 1))
    {F₁ : DecParams Gb × RawData d L (N₁ * L ^ m₁) (k + 1) N → (Gb.Ω 1 × Fin N → ℂ) × (Gb.Ω 1 → ℂ)}
    {F₁' : DecParams Gb' × RawData d L (N₁' * L ^ m₁) (k + 1) N →
      (Gb'.Ω 1 × Fin N → ℂ) × (Gb'.Ω 1 → ℂ)}
    {Sol : Dec2.DecParams (coverOf Gb) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    {Sol' : Dec2.DecParams (coverOf Gb') × Edat Hm' N → (Hm'.Ω 1 × Fin N → ℂ) × (Hm'.Ω 1 → ℂ)}
    {Φ : ((Gb.Ω 1 × Fin N → ℂ) × (Gb.Ω 1 → ℂ)) → (Hm.Ω 1 × Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ}
    {Φ' : ((Gb'.Ω 1 × Fin N → ℂ) × (Gb'.Ω 1 → ℂ)) → (Hm'.Ω 1 × Fin N → ℂ) →
      RawData d L (N₁' * L ^ m₁) (k + 1) N × (CTorus d L N₁' m₁ (k + 1) → Fin N → ℂ) → ℂ}
    (Zm : Finset (unitPts Gb)) (um tm : ℂ)
    {D : BgData Gb N} {D' : BgData Gb' N}
    (hΨ : FieldCorr (ρ + 1) D.Ψ D'.Ψ) (hh : FieldCorr (ρ + 1) D.h D'.h)
    {ψh : unitPts (GA) × Fin N → ℂ} {ψh' : unitPts (GB) × Fin N → ℂ}
    (hhat : ∀ x, InBox d ρ ((N₁ * L ^ m₁) * L ^ (k + 1)) x →
      ∀ i, ψh' (unitPt hGB (bk x), i) = ψh (unitPt hGA x, i))
    (hFan : AnalyticOnNhd ℂ (FFmarkedBg (GA) X₁f Gb a₁ ν (BgTransport.canon (GA) Gb N) cc F₁ Sol Φ
      Zm um tm (rawOf D, (BgTransport.canon (GA) Gb N).res ψh))
      (polydisc (0 : ParIdx (GA) (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) → ℂ)
        (fun _ => Real.exp κ)))
    {Sg : Set (DecParams Gb)} {Sg' : Set (DecParams Gb')}
    (hSg : ∀ w ∈ polydisc (0 : ParIdx (GA) (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) → ℂ)
        (fun _ => Real.exp κ),
      (BgTransport.canon (GA) Gb N).par
        (extParams (GA) (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) w) ∈ Sg)
    (hSg' : ∀ w ∈ polydisc (0 : ParIdx (GB) (↑(X₁f.image bk) : Set (CTorus d L N₁' m₁ (k + 1))) → ℂ)
        (fun _ => Real.exp κ),
      (BgTransport.canon (GB) Gb' N).par
        (extParams (GB) (↑(X₁f.image bk) : Set (CTorus d L N₁' m₁ (k + 1))) w) ∈ Sg')
    (hF : ∀ σ ∈ Sg,
      ∀ φ α, Dec2.IsDecBg (coverOf Gb) Gb (compWeight L a₁) ν ρb σ D φ α →
        F₁ (σ, rawOf D) = (φ, α))
    (hF' : ∀ σ ∈ Sg',
      ∀ φ α, Dec2.IsDecBg (coverOf Gb') Gb' (compWeight L a₁) ν ρb σ D' φ α →
        F₁' (σ, rawOf D') = (φ, α))
    (hex : ∀ σ ∈ Sg,
      ∃ φ α, Dec2.IsDecBg (coverOf Gb) Gb (compWeight L a₁) ν ρb σ D φ α)
    {r : ℝ}
    {Rl : Set (((Gb.Ω 1 × Fin N → ℂ) × (Gb.Ω 1 → ℂ)) × (Hm.Ω 1 × Fin N → ℂ) ×
        (RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)))}
    {Rl' : Set (((Gb'.Ω 1 × Fin N → ℂ) × (Gb'.Ω 1 → ℂ)) × (Hm'.Ω 1 × Fin N → ℂ) ×
        (RawData d L (N₁' * L ^ m₁) (k + 1) N × (CTorus d L N₁' m₁ (k + 1) → Fin N → ℂ)))}
    (hv : ∀ σ ∈ Sg,
      let p : Dec2.DecParams (coverOf Gb) × Edat Hm N :=
        (σ, flEdat Gb Hm (F₁ (σ, rawOf D)) D.Ψ
          (markedHatPsiFBg Gb a₁ ν (liftZ Gb) cc F₁ Zm um tm σ (rawOf D) (resZ (GA) Gb ψh)))
      (Sol p).1 = dphi Hm (Dec2.decG (coverOf Gb) Hm (compWeight L a₁) ν p.1) p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Dec2.DecFixed (coverOf Gb) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Small Hm (Sol p).2 r ∧ (F₁ (σ, rawOf D), (Sol p).1, (rawOf D, p.2.2.2.1)) ∈ Rl)
    (hv' : ∀ σ' ∈ Sg',
      let p' : Dec2.DecParams (coverOf Gb') × Edat Hm' N :=
        (σ', flEdat Gb' Hm' (F₁' (σ', rawOf D')) D'.Ψ
          (markedHatPsiFBg Gb' a₁ ν (liftZ Gb') cc F₁' (Zm.map hI.unitEquiv.toEmbedding) um tm σ'
            (rawOf D') (resZ (GB) Gb' ψh')))
      (Sol' p').1 = dphi Hm' (Dec2.decG (coverOf Gb') Hm' (compWeight L a₁) ν p'.1) p'.2.2.1
          p'.2.1 (pertSource Hm' (compWeight L a₁) p'.2.2.2.1 p'.2.2.2.2) (Sol' p').2 ∧
        (∀ δα', Small Hm' δα' r → Dec2.DecFixed (coverOf Gb') Hm' (compWeight L a₁) ν p'.1 false
          p'.2.2.1 p'.2.1 (pertSource Hm' (compWeight L a₁) p'.2.2.2.1 p'.2.2.2.2) δα' →
          δα' = (Sol' p').2) ∧
        (F₁' (σ', rawOf D'), (Sol' p').1, (rawOf D', p'.2.2.2.1)) ∈ Rl')
    (hΦ : ∀ (t : ((Gb.Ω 1 × Fin N → ℂ) × (Gb.Ω 1 → ℂ)) × (Hm.Ω 1 × Fin N → ℂ) ×
        (RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)))
      (t' : ((Gb'.Ω 1 × Fin N → ℂ) × (Gb'.Ω 1 → ℂ)) × (Hm'.Ω 1 × Fin N → ℂ) ×
        (RawData d L (N₁' * L ^ m₁) (k + 1) N × (CTorus d L N₁' m₁ (k + 1) → Fin N → ℂ))),
      t ∈ Rl → t' ∈ Rl' → (∀ x i, t'.1.1 (hI.e x, i) = t.1.1 (x, i)) → (∀ x, t'.1.2 (hI.e x) = t.1.2 x) →
      (∀ y i, t'.2.1 (hH.e y, i) = t.2.1 (y, i)) →
      FieldCorr (ρ + 1) t.2.2.1.1 t'.2.2.1.1 → FieldCorr (ρ + 1) t.2.2.1.2 t'.2.2.1.2 →
      FieldCorr (ρ + 1) t.2.2.2 t'.2.2.2 → Φ' t'.1 t'.2.1 t'.2.2 = Φ t.1 t.2.1 t.2.2) :
    evDecBg (GB) (X₁f.image bk) m₀ j 𝒦X' Gb' a₁ ν (BgTransport.canon (GB) Gb' N) cc F₁' Sol' Φ'
        (Zm.map hI.unitEquiv.toEmbedding) um tm (bk '' Y)
        (rawOf D', (BgTransport.canon (GB) Gb' N).res ψh') =
      evDecBg (GA) X₁f m₀ j 𝒦X Gb a₁ ν (BgTransport.canon (GA) Gb N) cc F₁ Sol Φ Zm um tm Y
        (rawOf D, (BgTransport.canon (GA) Gb N).res ψh) := by
  classical
  have hE1 : 1 < Real.exp κ := Real.one_lt_exp_iff.2 hκ
  have hKm : L ^ (k + 1) ≤ L ^ (k + 1 + m₁) :=
    Nat.pow_le_pow_right (Nat.pos_of_ne_zero (NeZero.ne L)) (Nat.le_add_right _ _)
  have hρ1 : 2 * (ρ₁) + 1 < (N₁' * L ^ m₁) * L ^ (k + 1) := by
    have := Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne L)) (cellSide_pos (L := L) 0 m₁ (k + 1))
    omega
  have hψ := hI.resZ_eq hGA hGB hhat
  -- the functional at corresponding cut points
  have hcore : ∀ (C : Finset (ParIdx (GA) (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1)))))
      (hCR : ∀ i ∈ C, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) i.1.1.2)
      (s : ParIdx (GA) (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) → ℂ)
      (s' : ParIdx (GB) (↑(X₁f.image bk) : Set (CTorus d L N₁' m₁ (k + 1))) → ℂ),
      s ∈ supN C (Real.exp κ) →
      (∀ i', (∀ i ∈ C, i'.1.1 ≠ ck i.1.1) → s' i' = 0) →
      (∀ i ∈ C, ∀ i', i'.1.1 = ck i.1.1 → s' i' = s i) →
      FFmarkedBg (GB) (X₁f.image bk) Gb' a₁ ν (BgTransport.canon (GB) Gb' N) cc F₁' Sol' Φ'
          (Zm.map hI.unitEquiv.toEmbedding) um tm
          (rawOf D', (BgTransport.canon (GB) Gb' N).res ψh') s' =
        FFmarkedBg (GA) X₁f Gb a₁ ν (BgTransport.canon (GA) Gb N) cc F₁ Sol Φ Zm um tm
          (rawOf D, (BgTransport.canon (GA) Gb N).res ψh) s := by
    intro C hCR s s' hs hs0' hss
    -- the extended parameters at the cubes of the box
    have hσ' : ∀ (i : ParIdx (GA) (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))))
        (i' : ParIdx (GB) (↑(X₁f.image bk) : Set (CTorus d L N₁' m₁ (k + 1)))),
        InBox d (ρ₁) ((N₁ * L ^ m₁) * L ^ (k + 1)) i.1.1.2 → i'.1.1 = ck i.1.1 → s' i' = s i := by
      intro i i' hib hi'
      by_cases hiC : i ∈ C
      · exact hss i hiC i' hi'
      · rw [hs.1 i hiC]
        refine hs0' i' fun j hj hjc => hiC ?_
        have hjb : InBox d (ρ₁) ((N₁ * L ^ m₁) * L ^ (k + 1)) j.1.1.2 :=
          inBox_mono (by omega) (hCR j hj)
        have := injOn_idxMap (N₁' := N₁') (ρ := ρ₁) hρ1 hjb hib (hjc.symm.trans hi')
        have hji : j = i := Subtype.ext (Subtype.ext this)
        exact hji ▸ hj
    have hS : ∀ P ∈ cubeIdx Gb, P.2 ∈ Gb.Ω (k + 1) →
        Dec2.extS (coverOf (GB)) (extParams (GB) (↑(X₁f.image bk) :
          Set (CTorus d L N₁' m₁ (k + 1))) s') (ck P) =
        Dec2.extS (coverOf (GA)) (extParams (GA) (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s) P := by
      intro P hP htop
      have hPA : P ∈ cubeIdx (GA) := mem_cubeIdx_of_isLevel hGA hP (top_of_base_mem hP htop)
      exact extS_extParams_boxMap_of_eq hnS hnS' (fun x hx => hX₁R x (Finset.mem_coe.1 hx))
        Finset.coe_image s s' hσ' hPA (inBox_mono (by omega) (hI.base_inBox hP))
    -- the transported parameters lie in the polydisc
    have hsp : s ∈ polydisc (0 : ParIdx (GA) (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) → ℂ)
        (fun _ => Real.exp κ) := fun i => by simpa using hs.2 i
    have hsp' : s' ∈ polydisc (0 : ParIdx (GB) (↑(X₁f.image bk) :
        Set (CTorus d L N₁' m₁ (k + 1))) → ℂ) (fun _ => Real.exp κ) := by
      intro i'
      simp only [Pi.zero_apply, sub_zero]
      by_cases h : ∃ i ∈ C, i'.1.1 = ck i.1.1
      · obtain ⟨i, hi, hi'⟩ := h
        rw [hss i hi i' hi']
        exact hs.2 i
      · simp only [not_exists, not_and] at h
        rw [hs0' i' h, norm_zero]
        exact Real.exp_pos κ
    have hσκ := hSg s hsp
    have hσκ' := hSg' s' hsp'
    exact hI.FFmarkedBg_canon_eq ν hH a₁ ρb cc s s' hS Zm um tm hΨ hh hψ rfl rfl
      (hF _ hσκ) (hF' _ hσκ') (hex _ hσκ) (hv _ hσκ) (hv' _ hσκ') hΦ
  unfold evDecBg
  rw [← hX₁, ← hX₁']
  refine evTerm_boxMap_of_eq hcov.hN hcov'.hN hnF hnF' (fun x hx => hX₁R x (Finset.mem_coe.1 hx))
    hYR Finset.coe_image _ _ _ _ ?_
  intro C hCm C' h2 h1
  have hYC := ((mem_connFams (fun i : ParIdx (GA) (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) =>
    i.1.1)).1 hCm).2
  have hCR : ∀ i ∈ C, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) i.1.1.2 := by
    intro i hi
    apply hYR
    rw [← hYC]
    right
    simp only [Set.mem_iUnion]
    exact ⟨i, hi, Pset_subset_Dsites hcov.hU hcov.hN i.1.2 (self_mem_Pset _)⟩
  by_cases hCe : C = ∅
  · subst hCe
    have hC'e : C' = ∅ := Finset.eq_empty_of_forall_notMem fun i' hi' => by
      obtain ⟨i, hi, -⟩ := h1 i' hi'
      simp at hi
    subst hC'e
    rw [coef_empty_eq, coef_empty_eq]
    exact hcore ∅ (fun i hi => by simp at hi) 0 0
      ⟨fun i _ => rfl, fun i => by simpa using Real.exp_pos κ⟩ (fun _ _ => rfl)
      (fun i hi => by simp at hi)
  · obtain ⟨i₀, hi₀⟩ := Finset.nonempty_of_ne_empty hCe
    obtain ⟨i₀', -, -⟩ := h2 i₀ hi₀
    choose f hf using h2
    set e : ParIdx (GA) (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) →
        ParIdx (GB) (↑(X₁f.image bk) : Set (CTorus d L N₁' m₁ (k + 1))) :=
      fun i => if hi : i ∈ C then f i hi else i₀' with he_def
    have he : ∀ i ∈ C, e i ∈ C' ∧ (e i).1.1 = ck i.1.1 := by
      intro i hi
      simp only [he_def, hi, ↓reduceDIte]
      exact hf i hi
    have hinj : Set.InjOn e ↑C := by
      intro i hi i₂ hi₂ hii
      have hc : ck i.1.1 = ck i₂.1.1 := by
        rw [← (he i hi).2, ← (he i₂ hi₂).2, hii]
      exact Subtype.ext (Subtype.ext (injOn_idxMap (N₁' := N₁') (ρ := R) (by omega)
        (hCR i hi) (hCR i₂ hi₂) hc))
    have hCimg : C.image e = C' := by
      ext i'
      constructor
      · intro h
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 h
        exact (he i hi).1
      · intro hi'
        obtain ⟨i, hi, hc⟩ := h1 i' hi'
        exact Finset.mem_image.2 ⟨i, hi, Subtype.ext (Subtype.ext ((he i hi).2.trans hc.symm))⟩
    rw [← hCimg]
    refine coef_relabel_injOn hE1 e hinj hFan (fun s hs s' hs' hss => ?_)
    refine hcore C hCR s s' hs (fun i' hi' => hs' i' fun hmem => ?_) (fun i hi i' hc => ?_)
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hmem
      exact hi' i hi (he i hi).2
    · have : i' = e i := Subtype.ext (Subtype.ext (hc.trans (he i hi).2.symm))
      rw [this]
      exact hss i hi

end OmegaIso

end Balaban.Polymer.LocalIso
