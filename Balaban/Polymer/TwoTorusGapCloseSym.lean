/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusEv
public import Balaban.Polymer.TwoTorusTranslate
public import Balaban.Fluctuation.DetSymmGroup
public import Balaban.Fluctuation.LocalClassLatHat

/-!
# Translation covariance of the marked cut-parameter functional (item 24, blocker 7)

The landed translation covariance of the step terms (`evTerm_translate_step`, `TwoTorusTranslate`)
concerns the functionals `fnOfDec` in the site fluctuation field.  The marked functional `FFmarked`
of the decoupled expansion (the hat variable on the unit points, the covariance square root, the
fluctuation solution, the masked tangent) was transported between two tori only (`TwoTorusEv`).
This file proves its covariance under a lattice symmetry of the step torus (the translations by
multiples of the cell side are the instances used later):

* `hatPsiF_sym`, `markedHatPsiF_sym`: the decoupled tangent is transported, the hat variable and the
  mask being relabelled by the action of the symmetry on the unit points;
* `FFmarked_sym`: `FFmarked` at the transported data and cut parameters equals `FFmarked` at the
  original ones composed with the relabelling of the parameters; `analyticOnNhd_FFmarked_sym`,
  `coef_FFmarked_sym`: the transported functional is analytic and its coefficients are the
  transported coefficients;
* `covSetup_translate`, `X1_translate`: the geometric data of a cover and its read region are
  translated by a multiple of the cell side.

-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Polymer.TwoTorusStep

open Balaban Balaban.Localization Balaban.Analysis Balaban.Fluctuation Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.Polymer Balaban.Multiscale Balaban.Background

section Cov

open Balaban.Localization.DetUnitIncidence Balaban.Localization.DecEquiv
  Balaban.Localization.DetDecCov Finset Matrix
variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ} {m₀ : ℕ} {σ : Equiv.Perm (CTorus d L N₁ m₁ (k + 1))}

/-- The permutation of the unit points induced by a symmetry `σ` that preserves the unit blocks sends the unit point of a site `x` to the unit point of `σ x`. -/
theorem unitPt_sym (hG : IsLevel Gp (k + 1)) (S : LatSymm Gp Gp σ) (hU : UnitBlockPres σ)
    (x : CTorus d L N₁ m₁ (k + 1)) :
    unitAct Gp S hU (unitPt hG x) = unitPt hG (σ x) :=
  Subtype.ext (unitAct_unitBlock Gp S hU (hG.mem_layer x))

/-- The inverse permutation of the unit points sends the unit point of `x` to the unit point of `σ⁻¹ x`. -/
theorem unitAct_symm_unitPt (hG : IsLevel Gp (k + 1)) (S : LatSymm Gp Gp σ) (hU : UnitBlockPres σ)
    (x : CTorus d L N₁ m₁ (k + 1)) :
    (unitAct Gp S hU).symm (unitPt hG x) = unitPt hG (σ.symm x) :=
  (Equiv.symm_apply_eq _).2 (by rw [unitPt_sym hG S hU, Equiv.apply_symm_apply])

/-- **The decoupled fluctuation field is transported by a lattice symmetry.**  If the decoupled background at the transported cut parameters and the transported datum is the transport of the background at the original ones (`hFs`), then `ψ'(s) = liftC (cc • C^{1/2}(s) ψ̂)` at `(σ s, σ Θ)` with the hat variable relabelled by the action of `σ` on the unit points is the transport `x ↦ ψ'(s)(σ⁻¹ x)`: the covariance of the square root `C^{1/2}` (`decCovSqrt_rm_pair`) and of the lift to the fine lattice. -/
theorem hatPsiF_sym (hG : IsLevel Gp (k + 1)) (S : LatSymm Gp Gp σ) (hU : UnitBlockPres σ)
    (CS : CoverSymm (coverOf Gp) σ) (cc : ℂ)
    {F₁ : DecParams Gp × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    (s : DecParams Gp) (Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N)
    (hFs : F₁ (CS.par s, symRaw σ Θ) = (S.fld (F₁ (s, Θ)).1, S.mul (F₁ (s, Θ)).2))
    (ψh : unitPts Gp × Fin N → ℂ) :
    hatPsiF Gp a₁ ν hG cc F₁ (CS.par s) (symRaw σ Θ)
        (fun r => ψh (((unitAct Gp S hU).symm) r.1, r.2)) =
      symSite σ (hatPsiF Gp a₁ ν hG cc F₁ s Θ ψh) := by
  classical
  have hu := unitBlock_unitAct_iff Gp S hU
  have hss : ∀ P, Dec2.extS (coverOf Gp) (CS.par s) (CS.τ P) = Dec2.extS (coverOf Gp) s P := by
    intro P; exact (CS.extS_par s _).trans (by simp)
  have hbar : barField Gp (symRaw σ Θ).1 (S.fld (F₁ (s, Θ)).1) =
      symSite σ (barField Gp Θ.1 (F₁ (s, Θ)).1) := by
    funext y i
    obtain ⟨x, rfl⟩ := σ.surjective y
    show barField Gp (fun z => Θ.1 (σ.symm z)) (S.fld (F₁ (s, Θ)).1) (σ x) i =
      barField Gp Θ.1 (F₁ (s, Θ)).1 (σ.symm (σ x)) i
    rw [barField_sym_raw_pair S, Equiv.symm_apply_apply]
  have hsq : hatSqrtF Gp a₁ ν F₁ (CS.par s) (symRaw σ Θ) =
      rm ((unitAct Gp S hU).prodCongr (Equiv.refl (Fin N))) (hatSqrtF Gp a₁ ν F₁ s Θ) := by
    unfold hatSqrtF
    rw [hFs]
    simp only
    rw [hbar]
    exact decCovSqrt_rm_pair S hU CS.idx CS.chi CS.box CS.qset hu (compWeight L a₁) a₁ ν _ hss _
  funext y i
  obtain ⟨x, rfl⟩ := σ.surjective y
  simp only [symSite, Equiv.symm_apply_apply]
  unfold hatPsiF
  rw [liftC_apply, liftC_apply, hsq, ← unitPt_sym hG S hU x]
  simp only [Pi.smul_apply, smul_eq_mul]
  congr 1
  have := rm_mulVec_apply ((unitAct Gp S hU).prodCongr (Equiv.refl (Fin N)))
      (hatSqrtF Gp a₁ ν F₁ s Θ) ψh (unitPt hG x, i)
  exact this

/-- The masked decoupled tangent is transported by a lattice symmetry, with the mask `Zm` replaced by the mask `Zm'` that corresponds to it on the unit points (`hZ`): `hatPsiF_sym` and `markedHatPsiF_apply`. -/
theorem markedHatPsiF_sym (hG : IsLevel Gp (k + 1)) (S : LatSymm Gp Gp σ) (hU : UnitBlockPres σ)
    (CS : CoverSymm (coverOf Gp) σ) (cc : ℂ)
    {F₁ : DecParams Gp × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    (s : DecParams Gp) (Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N)
    (hFs : F₁ (CS.par s, symRaw σ Θ) = (S.fld (F₁ (s, Θ)).1, S.mul (F₁ (s, Θ)).2))
    (ψh : unitPts Gp × Fin N → ℂ) {Zm Zm' : Finset (unitPts Gp)}
    (hZ : ∀ y, unitAct Gp S hU y ∈ Zm' ↔ y ∈ Zm) (um tm : ℂ) :
    markedHatPsiF a₁ ν hG cc F₁ Zm' um tm (CS.par s) (symRaw σ Θ)
        (fun r => ψh (((unitAct Gp S hU).symm) r.1, r.2)) =
      symSite σ (markedHatPsiF a₁ ν hG cc F₁ Zm um tm s Θ ψh) := by
  classical
  funext y i
  obtain ⟨x, rfl⟩ := σ.surjective y
  have h := congrFun (congrFun (hatPsiF_sym (a₁ := a₁) (ν := ν) hG S hU CS cc s Θ hFs ψh) (σ x)) i
  refine (markedHatPsiF_apply hG cc F₁ Zm' um tm _ _ _ _ i).trans ?_
  show _ = markedHatPsiF a₁ ν hG cc F₁ Zm um tm s Θ ψh (σ.symm (σ x)) i
  rw [Equiv.symm_apply_apply, markedHatPsiF_apply]
  rw [h]
  simp only [symSite, Equiv.symm_apply_apply]
  rw [← unitPt_sym hG S hU x]
  have := hZ (unitPt hG x)
  by_cases hx : unitPt hG x ∈ Zm
  · simp [hx, this.2 hx]
  · have hx' : unitAct Gp S hU (unitPt hG x) ∉ Zm' := fun h => hx (this.1 h)
    simp [hx, hx']

/-- **Covariance of the marked cut-parameter functional under a lattice symmetry.**  Let `σ` be a lattice symmetry of the generating set `Gp` (together with the symmetry `Sm` of `Hm`) that preserves the unit blocks and is compatible with the cover, the blocks and the polymers, and let the read region move as `X₁f' = σ X₁f`.  If the block functional `Φ'` is the transport of `Φ` on the realizable triples (`hΦ`) and the masks correspond (`hZ`), then for every vector of cut parameters `s'` of the polydisc `FFmarked X₁f' … Φ' Zm' … (σ Θ, σ ψ̂) s' = FFmarked X₁f … Φ Zm … (Θ, ψ̂) (s' ∘ κ)`, `κ` the relabelling of the cut parameters (`parEquiv`).  The proof follows the fan composite of the local class terms (`fanLC_sym_cover_pair`): the decoupled background is transported (`F₁_sym`), the data of the fluctuation problem and its solution are transported (`flEdat_sym_pair`, `Sol_sym_pair`), and the tangent is transported (`markedHatPsiF_sym`). -/
theorem FFmarked_sym
    (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (hk : 1 ≤ k)
    (hHm : IsLevel Hm k) (hG : IsLevel Gp (k + 1)) (cc : ℂ) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hαK : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    {F₁ : DecParams Gp × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    (hF₁ : ∀ (s : DecParams Gp) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
        (α : Gp.Ω 1 → ℂ), IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    {Sol : Dec2.DecParams (coverOf Gp) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    (hSol : ∀ p : Dec2.DecParams (coverOf Gp) × Edat Hm N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol p).1 = dphi Hm (Dec2.decG (coverOf Gp) Hm (compWeight L a₁) ν p.1) p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Dec2.DecFixed (coverOf Gp) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Small Hm (Sol p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm (Sol p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm (Sol p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gp) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol p).2))
    (S : LatSymm Gp Gp σ) (Sm : LatSymm Hm Hm σ) (hU : UnitBlockPres σ)
    (CS : CoverSymm (coverOf Gp) σ) (B : BlockSymm Gp σ) (P : PolymerSymm Gp m₀ σ CS.τ)
    {X₁f X₁f' : Finset (CTorus d L N₁ m₁ (k + 1))}
    (hX : (↑X₁f' : Set (CTorus d L N₁ m₁ (k + 1))) = σ '' (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))))
    {Φ Φ' : ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) → (Hm.Ω 1 × Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ}
    (hΦ : ∀ (bg : (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) δφ u,
      (bg, δφ, u) ∈ FlReal Gp Hm a₁ ν BG κ eps X₁f BG₂ δ₁ →
      ((S.fld bg.1, S.mul bg.2), Sm.fld δφ, symU σ u) ∈ FlReal Gp Hm a₁ ν BG κ eps X₁f' BG₂ δ₁ →
      Φ' (S.fld bg.1, S.mul bg.2) (Sm.fld δφ) (symU σ u) = Φ bg δφ u)
    {Zm Zm' : Finset (unitPts Gp)} (hZ : ∀ y, unitAct Gp S hU y ∈ Zm' ↔ y ∈ Zm)
    {um tm : ℂ}
    (hum : (‖um‖ + ‖tm‖) * markedRad d L N k a₁ κ cψ cc < δ₁)
    {D : BgData Gp N} (hD : XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D)
    {ψh : unitPts Gp × Fin N → ℂ} (hψh : ∀ p, ‖ψh p‖ ≤ cψ)
    {s' : ParIdx Gp (↑X₁f' : Set (CTorus d L N₁ m₁ (k + 1))) → ℂ}
    (hs : ∀ i, ‖s' i‖ < Real.exp κ) :
    FFmarked X₁f' a₁ ν hG cc F₁ Sol Φ' Zm' um tm
        (symRaw σ (rawOf D), fun r => ψh (((unitAct Gp S hU).symm) r.1, r.2)) s' =
      FFmarked X₁f a₁ ν hG cc F₁ Sol Φ Zm um tm (rawOf D, ψh) (s' ∘ parEquiv CS P hX) := by
  classical
  have hE1 : 1 < Real.exp κ := Real.one_lt_exp_iff.2 hC.hκ
  have hs1 : ∀ i, ‖(s' ∘ parEquiv CS P hX) i‖ < Real.exp κ := fun i => hs _
  set sA := extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) (s' ∘ parEquiv CS P hX) with hsA
  have hsAb : ∀ Q, ‖sA Q‖ < Real.exp κ := norm_extParams_lt hE1 hs1
  have hext := extParams_sym CS P hX s'
  have hFs : F₁ (CS.par sA, symRaw σ (rawOf D)) =
      (S.fld (F₁ (sA, rawOf D)).1, S.mul (F₁ (sA, rawOf D)).2) := F₁_sym hC hF₁ S CS B hsAb hD
  have hmh := markedHatPsiF_sym (a₁ := a₁) (ν := ν) hG S hU CS cc sA (rawOf D) hFs ψh hZ um tm
  have hψb := markedHatPsiF_mem_flBallLC hC hk hHm hG cc hcψ hMX hmar hαK hsm hF₁ hsAb hD hψh Zm hum
  have hψb' := symSite_mem_flBallLC Sm hψb
  have hss : ∀ Q, Dec2.extS (coverOf Gp) (CS.par sA) (CS.τ Q) = Dec2.extS (coverOf Gp) sA Q := by
    intro Q; exact (CS.extS_par sA _).trans (by simp)
  have hsB : ∀ Q, ‖(CS.par sA) Q‖ < Real.exp κ := fun Q => hsAb _
  have hs1B : ∀ (Q : ℕ × CTorus d L N₁ m₁ (k + 1)) (hQ : Q ∈ cubeIdx Gp),
      Q ∉ parCubes Gp X₁f' → (CS.par sA) ⟨Q, hQ⟩ = 1 := by
    intro Q hQ hQn
    have := extParams_hs1 (Gp := Gp) (X₁f := X₁f') s' Q hQ hQn
    rw [hext] at this
    exact this
  have hD' := xiCData_sym S hD
  obtain ⟨φ, α, δφ, δα, hI, hF, hstr, hS1, hmem⟩ := point_facts_core hC hF₁ hSol hsAb
    (extParams_hs1 (s' ∘ parEquiv CS P hX)) hD hψb.1
  have hψσ : markedHatPsiF a₁ ν hG cc F₁ Zm' um tm (CS.par sA) (rawOf (S.sym D))
      (fun r => ψh (((unitAct Gp S hU).symm) r.1, r.2)) =
      symSite σ (markedHatPsiF a₁ ν hG cc F₁ Zm um tm sA (rawOf D) ψh) := hmh
  have hψb2 : markedHatPsiF a₁ ν hG cc F₁ Zm' um tm (CS.par sA) (rawOf (S.sym D))
      (fun r => ψh (((unitAct Gp S hU).symm) r.1, r.2)) ∈ FlBallLC Hm δ₁ := by
    rw [hψσ]; exact hψb'
  obtain ⟨φ', α', δφ', δα', hI', hF', hstr', hS1', hmem'⟩ := point_facts_core hC hF₁ hSol hsB hs1B
    hD' hψb2.1
  have hF'' : F₁ (CS.par sA, rawOf (S.sym D)) = (S.fld φ, S.mul α) := by
    have := hFs
    rw [hF] at this
    exact this
  have hpa : (φ', α') = (S.fld φ, S.mul α) := by rw [← hF', hF'']
  obtain ⟨h1, h2⟩ := Prod.mk.inj hpa
  subst φ'
  subst α'
  set ψ' := markedHatPsiF a₁ ν hG cc F₁ Zm um tm sA (rawOf D) ψh with hψ'
  have hE := flEdat_sym_pair S Sm (φ, α) D.Ψ ψ'
  have hSolr := Sol_sym_pair hSol hSol Sm CS.idx CS.chi CS.box CS.qset hss hsAb
    (φ₀ := (flEdat Gp Hm (φ, α) D.Ψ ψ').1) (α₀ := (flEdat Gp Hm (φ, α) D.Ψ ψ').2.1)
    (δΨ := (flEdat Gp Hm (φ, α) D.Ψ ψ').2.2.1) (f₁ := (flEdat Gp Hm (φ, α) D.Ψ ψ').2.2.2)
    hstr (by rw [← hE]; rw [hψσ] at hstr'; exact hstr')
  have hSa : (Sol (sA, flEdat Gp Hm (φ, α) D.Ψ ψ')).1 = δφ := by rw [hS1]
  have hSb : (Sol (CS.par sA, flEdat Gp Hm (S.fld φ, S.mul α) (symSite σ D.Ψ)
      (symSite σ ψ'))).1 = Sm.fld δφ := by
    rw [hE, hSolr, hSa]
  unfold FFmarked
  rw [hext]
  dsimp only
  rw [← hsA]
  rw [hmh, hFs, hF]
  have hSa' : (Sol (sA, flEdat Gp Hm (φ, α) (rawOf D).1 ψ')).1 = δφ := hSa
  have hδ' : δφ' = Sm.fld δφ := by
    rw [hψσ] at hS1'
    have h0 := congrArg Prod.fst hS1'
    exact h0.symm.trans hSb
  have hm2 : ((S.fld (φ, α).1, S.mul (φ, α).2), Sm.fld δφ, symU σ (rawOf D, ψ')) ∈
      FlReal Gp Hm a₁ ν BG κ eps X₁f' BG₂ δ₁ := by
    have h3 := hmem'
    rw [hδ', hψσ] at h3
    exact h3
  show Φ' (S.fld (φ, α).1, S.mul (φ, α).2)
    (Sol (CS.par sA, flEdat Gp Hm (S.fld φ, S.mul α) (symSite σ D.Ψ) (symSite σ ψ'))).1
    (symU σ (rawOf D, ψ')) = _
  rw [hSb, hSa']
  exact hΦ (φ, α) δφ (rawOf D, ψ') hmem hm2
end Cov

section SymLemmas

open Balaban.Localization.DetUnitIncidence Balaban.Localization.DecEquiv Balaban.Localization.DetDecCov

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ} {m₀ : ℕ} {σ : Equiv.Perm (CTorus d L N₁ m₁ (k + 1))}

/-- **Analyticity of the transported marked functional.**  Under the hypotheses of `coef_FFmarked_sym` (with the identity `hΦ` valid for all arguments), the transported functional is analytic in the cut parameters on the polydisc, since it is the original functional composed with the linear relabelling `s' ↦ s' ∘ κ` (`FFmarked_sym` holds on the whole polydisc). -/
theorem analyticOnNhd_FFmarked_sym
    (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (hk : 1 ≤ k)
    (hHm : IsLevel Hm k) (hG : IsLevel Gp (k + 1)) (cc : ℂ) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hαK : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    {F₁ : DecParams Gp × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    (hF₁ : ∀ (s : DecParams Gp) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
        (α : Gp.Ω 1 → ℂ), IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    {Sol : Dec2.DecParams (coverOf Gp) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    (hSol : ∀ p : Dec2.DecParams (coverOf Gp) × Edat Hm N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol p).1 = dphi Hm (Dec2.decG (coverOf Gp) Hm (compWeight L a₁) ν p.1) p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Dec2.DecFixed (coverOf Gp) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Small Hm (Sol p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm (Sol p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm (Sol p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gp) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol p).2))
    (S : LatSymm Gp Gp σ) (Sm : LatSymm Hm Hm σ) (hU : UnitBlockPres σ)
    (CS : CoverSymm (coverOf Gp) σ) (B : BlockSymm Gp σ) (P : PolymerSymm Gp m₀ σ CS.τ)
    {X₁f X₁f' : Finset (CTorus d L N₁ m₁ (k + 1))}
    (hX : (↑X₁f' : Set (CTorus d L N₁ m₁ (k + 1))) = σ '' (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))))
    {Φ Φ' : ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) → (Hm.Ω 1 × Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ}
    (hΦ : ∀ (bg : (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) δφ u,
      Φ' (S.fld bg.1, S.mul bg.2) (Sm.fld δφ) (symU σ u) = Φ bg δφ u)
    {Zm Zm' : Finset (unitPts Gp)} (hZ : ∀ y, unitAct Gp S hU y ∈ Zm' ↔ y ∈ Zm)
    {um tm : ℂ}
    (hum : (‖um‖ + ‖tm‖) * markedRad d L N k a₁ κ cψ cc < δ₁)
    {D : BgData Gp N} (hD : XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D)
    {ψh : unitPts Gp × Fin N → ℂ} (hψh : ∀ p, ‖ψh p‖ ≤ cψ)
    (hF : AnalyticOnNhd ℂ (FFmarked X₁f a₁ ν hG cc F₁ Sol Φ Zm um tm (rawOf D, ψh))
      (polydisc (0 : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) → ℂ)
        (fun _ => Real.exp κ)))
    :
    AnalyticOnNhd ℂ (FFmarked X₁f' a₁ ν hG cc F₁ Sol Φ' Zm' um tm
        (symRaw σ (rawOf D), fun r => ψh (((unitAct Gp S hU).symm) r.1, r.2)))
      (polydisc (0 : ParIdx Gp (↑X₁f' : Set (CTorus d L N₁ m₁ (k + 1))) → ℂ)
        (fun _ => Real.exp κ)) := by
  have hE1 : 1 < Real.exp κ := Real.one_lt_exp_iff.2 hC.hκ
  have h1 := analyticOnNhd_comp_relabel (R := Real.exp κ) (parEquiv CS P hX) hF
  refine h1.congr (isOpen_polydisc _ _) fun s hs => ?_
  exact (FFmarked_sym hC hk hHm hG cc hcψ hMX hmar hαK hsm hF₁ hSol S Sm hU CS B P hX
    (fun bg δφ u _ _ => hΦ bg δφ u) hZ hum hD hψh (fun i => by simpa using hs i)).symm

/-- **The coefficients of the marked functional are transported by a lattice symmetry.**  For every family `C` of cut parameters, the coefficient of the transported functional at the relabelled family `κ C` equals the coefficient of the original functional at `C` (`FFmarked_sym` and `coef_relabel`). -/
theorem coef_FFmarked_sym
    (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (hk : 1 ≤ k)
    (hHm : IsLevel Hm k) (hG : IsLevel Gp (k + 1)) (cc : ℂ) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hαK : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    {F₁ : DecParams Gp × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    (hF₁ : ∀ (s : DecParams Gp) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
        (α : Gp.Ω 1 → ℂ), IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    {Sol : Dec2.DecParams (coverOf Gp) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    (hSol : ∀ p : Dec2.DecParams (coverOf Gp) × Edat Hm N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol p).1 = dphi Hm (Dec2.decG (coverOf Gp) Hm (compWeight L a₁) ν p.1) p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Dec2.DecFixed (coverOf Gp) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Small Hm (Sol p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm (Sol p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm (Sol p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gp) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol p).2))
    (S : LatSymm Gp Gp σ) (Sm : LatSymm Hm Hm σ) (hU : UnitBlockPres σ)
    (CS : CoverSymm (coverOf Gp) σ) (B : BlockSymm Gp σ) (P : PolymerSymm Gp m₀ σ CS.τ)
    {X₁f X₁f' : Finset (CTorus d L N₁ m₁ (k + 1))}
    (hX : (↑X₁f' : Set (CTorus d L N₁ m₁ (k + 1))) = σ '' (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))))
    {Φ Φ' : ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) → (Hm.Ω 1 × Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ}
    (hΦ : ∀ (bg : (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) δφ u,
      Φ' (S.fld bg.1, S.mul bg.2) (Sm.fld δφ) (symU σ u) = Φ bg δφ u)
    {Zm Zm' : Finset (unitPts Gp)} (hZ : ∀ y, unitAct Gp S hU y ∈ Zm' ↔ y ∈ Zm)
    {um tm : ℂ}
    (hum : (‖um‖ + ‖tm‖) * markedRad d L N k a₁ κ cψ cc < δ₁)
    {D : BgData Gp N} (hD : XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D)
    {ψh : unitPts Gp × Fin N → ℂ} (hψh : ∀ p, ‖ψh p‖ ≤ cψ)
    (hF : AnalyticOnNhd ℂ (FFmarked X₁f a₁ ν hG cc F₁ Sol Φ Zm um tm (rawOf D, ψh))
      (polydisc (0 : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) → ℂ)
        (fun _ => Real.exp κ)))
    (C : Finset (ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))))) :
    coef (FFmarked X₁f' a₁ ν hG cc F₁ Sol Φ' Zm' um tm
        (symRaw σ (rawOf D), fun r => ψh (((unitAct Gp S hU).symm) r.1, r.2)))
      (C.map (parEquiv CS P hX).toEmbedding) =
      coef (FFmarked X₁f a₁ ν hG cc F₁ Sol Φ Zm um tm (rawOf D, ψh)) C := by
  have hE1 : 1 < Real.exp κ := Real.one_lt_exp_iff.2 hC.hκ
  have hF' := analyticOnNhd_FFmarked_sym hC hk hHm hG cc hcψ hMX hmar hαK hsm hF₁ hSol S Sm hU CS B P
    hX hΦ hZ hum hD hψh hF
  exact coef_relabel hE1 (parEquiv CS P hX) hF hF' (fun s hs =>
    FFmarked_sym hC hk hHm hG cc hcψ hMX hmar hαK hsm hF₁ hSol S Sm hU CS B P hX
      (fun bg δφ u _ _ => hΦ bg δφ u) hZ hum hD hψh (fun i => lt_of_le_of_lt (hs i) hE1)) C

end SymLemmas


section Cover

open Balaban.Localization.DetUnitIncidence Balaban.Localization.DecEquiv

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {m₀ j : ℕ}

omit [NeZero N₁] [NeZero L] in
/-- The image of a box under the translation by `t` is the box with base point translated by `t`. -/
theorem image_box_translate (b t : CTorus d L N₁ m₁ K) (s : ℕ) :
    (Equiv.addRight t) '' box b s = box (b + t) s := by
  ext z
  obtain ⟨x, rfl⟩ : ∃ x, z = x + t := ⟨z - t, by abel⟩
  rw [show x + t = (Equiv.addRight t) x from rfl, (Equiv.addRight t).injective.mem_set_image]
  exact (mem_box_add_iff b t x s).symm

omit [NeZero N₁] [NeZero L] in
/-- A translation by a multiple of the cell side of the top level `K` is a multiple of the cell side of every level `n ≤ K`. -/
theorem cellSide_dvd_translate {t : CTorus d L N₁ m₁ K} {n : ℕ} (hn : n ≤ K)
    (ht : ∀ μ, L ^ (K + m₀ + m₁) ∣ (t μ).val) (μ : Fin d) :
    cellSide L m₀ m₁ n ∣ (t μ).val :=
  (pow_dvd_pow L (by omega)).trans (ht μ)

/-- Alignment to the cell side of level `n ≤ K` is invariant under translation by a multiple of the cell side of level `K`. -/
theorem aligned_image_translate {t : CTorus d L N₁ m₁ K} (hN : L ^ m₀ ∣ N₁) {n : ℕ} (hn : n ≤ K)
    (ht : ∀ μ, L ^ (K + m₀ + m₁) ∣ (t μ).val) (b : CTorus d L N₁ m₁ K) :
    Aligned (cellSide L m₀ m₁ n) (b + t) ↔ Aligned (cellSide L m₀ m₁ n) b :=
  aligned_add_iff (cellSide_dvd hN hn) b t (cellSide_dvd_translate hn ht)

/-- **The geometric data of a cover is translated.**  If `(X, 𝒦X)` carries the data `CovSetup` of a step, then `(X + t, 𝒦X + t)` carries it as well, for a translation `t` by a multiple of the cell side of the top level (the layers of `G` are invariant under `t`). -/
theorem covSetup_translate {t : CTorus d L N₁ m₁ K} (S : LatSymm G G (Equiv.addRight t))
    (ht : ∀ μ, L ^ (K + m₀ + m₁) ∣ (t μ).val) {X 𝒦X : Set (CTorus d L N₁ m₁ K)}
    (h : CovSetup G m₀ j X 𝒦X) :
    CovSetup G m₀ j ((Equiv.addRight t) '' X) ((Equiv.addRight t) '' 𝒦X) := by
  have hj : j ≤ K := by have := h.hjK; omega
  have hK : K ≤ K := le_rfl
  refine ⟨h.hU, h.hN, h.hjK, ⟨?_, ?_⟩, ?_⟩
  · rintro _ ⟨b, hb, rfl⟩
    obtain ⟨h1, h2⟩ := h.chosen.1 b hb
    refine ⟨(aligned_image_translate h.hN hj ht b).2 h1, ?_⟩
    show box (b + t) _ ⊆ _
    rw [← image_box_translate]
    exact Set.image_mono h2
  · rintro _ ⟨z, hz, rfl⟩
    obtain ⟨b, hb, hzb⟩ := h.chosen.2 z hz
    refine ⟨b + t, ⟨b, hb, rfl⟩, ?_⟩
    rw [← image_box_translate]
    exact ⟨z, hzb, rfl⟩
  · rintro _ ⟨b, hb, rfl⟩
    obtain ⟨b', h1, h2, h3⟩ := h.nest b hb
    refine ⟨b' + t, (aligned_image_translate h.hN hK ht b').2 h1, ?_, ?_⟩
    · show box (b + t) _ ⊆ _
      rw [← image_box_translate, ← image_box_translate]
      exact Set.image_mono h2
    · rw [← image_box_translate]
      rintro _ ⟨x, hx, rfl⟩
      exact (S.mem_layer (by have := h.hjK; omega) le_rfl x).2 (h3 hx)

/-- The read region `X₁` of a cover is translated with the cover: `X₁(𝒦X + t) = X₁(𝒦X) + t`. -/
theorem X1_translate {t : CTorus d L N₁ m₁ K} (S : LatSymm G G (Equiv.addRight t))
    (ht : ∀ μ, L ^ (K + m₀ + m₁) ∣ (t μ).val) {X 𝒦X : Set (CTorus d L N₁ m₁ K)}
    (h : CovSetup G m₀ j X 𝒦X) :
    X1 G m₀ j ((Equiv.addRight t) '' 𝒦X) = (Equiv.addRight t) '' X1 G m₀ j 𝒦X := by
  have hj : j ≤ K := by have := h.hjK; omega
  have hK1 : 1 ≤ K := by have := h.hjK; omega
  ext z
  obtain ⟨x, rfl⟩ : ∃ x, z = x + t := ⟨z - t, by abel⟩
  rw [show x + t = (Equiv.addRight t) x from rfl, (Equiv.addRight t).injective.mem_set_image]
  unfold X1
  simp only [Set.mem_iUnion, exists_prop]
  constructor
  · rintro ⟨b, ⟨hb1, hb2, q, ⟨q0, hq0, rfl⟩, hq⟩, hx⟩
    obtain ⟨b0, rfl⟩ : ∃ b0, b = b0 + t := ⟨b - t, by abel⟩
    refine ⟨b0, ⟨(aligned_image_translate h.hN le_rfl ht b0).1 hb1, ?_, q0, hq0, ?_⟩,
      (mem_box_add_iff b0 t x _).1 hx⟩
    · intro y hy
      have := hb2 ((mem_box_add_iff b0 t y _).2 hy)
      exact (S.mem_layer hK1 le_rfl y).1 this
    · intro y hy
      have := hq ((mem_box_add_iff q0 t y _).2 hy)
      exact (mem_box_add_iff b0 t y _).1 this
  · rintro ⟨b, ⟨hb1, hb2, q, hq, hqb⟩, hx⟩
    refine ⟨b + t, ⟨(aligned_image_translate h.hN le_rfl ht b).2 hb1, ?_, q + t, ⟨q, hq, rfl⟩, ?_⟩,
      (mem_box_add_iff b t x _).2 hx⟩
    · intro y hy
      obtain ⟨y0, rfl⟩ : ∃ y0, y = y0 + t := ⟨y - t, by abel⟩
      exact (S.mem_layer hK1 le_rfl y0).2 (hb2 ((mem_box_add_iff b t y0 _).1 hy))
    · intro y hy
      obtain ⟨y0, rfl⟩ : ∃ y0, y = y0 + t := ⟨y - t, by abel⟩
      exact (mem_box_add_iff b t y0 _).2 (hqb ((mem_box_add_iff q t y0 _).1 hy))

end Cover

section RecentringInt

variable {d : ℕ}

/-- **The recentring vector at integer level.**  Under the hypotheses of `exists_recentring`, and if the points of `X₁ ∪ Y` have centred representatives of absolute value at most `q` with `2 q + 2 (D + (D + 1) / 4) < n`, the recentring vector `z` (a multiple of `a`) can be chosen so that the integer sums `x_μ + z_μ` of the centred representatives, and not only their residues modulo `n`, are at most `D + (D + 1) / 4` in absolute value.  The vector of `exists_recentring` is reduced modulo `n` by the integer `n m_μ` that brings the base point to its centred representative; for the other points the two integers differ by a multiple of `n` of size less than `n`. -/
theorem exists_recentring_int {n a L D q : ℕ} [NeZero n] (hd : 0 < d) (ha : 0 < a) (hL : 2 ≤ L)
    (han : a ∣ n) {X₁ Y : Set (Torus d n)} (hbox : ∃ b, box b (L * a) ⊆ X₁)
    (hD : ∀ x ∈ X₁, ∀ y ∈ X₁ ∪ Y, ∀ μ, |(x μ - y μ).valMinAbs| ≤ D) (hn : 25 * D + 25 < n)
    (hq : ∀ x ∈ X₁ ∪ Y, ∀ μ, |(x μ).valMinAbs| ≤ q) (hqn : 2 * q + 2 * (D + (D + 1) / 4) < n) :
    ∃ z : Fin d → ℤ, (∀ μ, (a : ℤ) ∣ z μ) ∧
      ∀ x ∈ X₁ ∪ Y, ∀ μ, |(x μ).valMinAbs + z μ| ≤ ((D + (D + 1) / 4 : ℕ) : ℤ) := by
  obtain ⟨z0, hz0, hbx⟩ := exists_recentring hd ha hL hbox hD hn
  obtain ⟨b, hb⟩ := hbox
  have hbX : b ∈ X₁ := hb ⟨fun _ => 0, fun _ => Nat.mul_pos (by omega) ha, by funext μ; simp [natT]⟩
  set r := D + (D + 1) / 4 with hr
  have hw : ∀ x ∈ X₁ ∪ Y, ∀ μ, ∃ k : ℤ, (x μ).valMinAbs + z0 μ -
      (x μ + ((z0 μ : ℤ) : ZMod n)).valMinAbs = n * k := by
    intro x hx μ
    have h1 : (((x μ + ((z0 μ : ℤ) : ZMod n)).valMinAbs : ℤ) : ZMod n) =
        (((x μ).valMinAbs + z0 μ : ℤ) : ZMod n) := by
      rw [ZMod.coe_valMinAbs]; push_cast; simp
    obtain ⟨k, hk⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ n).1 h1
    exact ⟨k, hk⟩
  choose k0 hk0 using fun μ => hw b (Or.inl hbX) μ
  refine ⟨fun μ => z0 μ - n * k0 μ, fun μ => ?_, fun x hx μ => ?_⟩
  · exact dvd_sub (hz0 μ) (dvd_mul_of_dvd_left (Int.natCast_dvd_natCast.2 han) _)
  · obtain ⟨kx, hkx⟩ := hw x hx μ
    have hwx : |(x μ + ((z0 μ : ℤ) : ZMod n)).valMinAbs| ≤ (r : ℤ) := hbx x hx μ
    have hw0 : |(b μ + ((z0 μ : ℤ) : ZMod n)).valMinAbs| ≤ (r : ℤ) := hbx b (Or.inl hbX) μ
    have hqx := hq x hx μ
    have hqb := hq b (Or.inl hbX) μ
    have hk0μ := hk0 μ
    show |(x μ).valMinAbs + (z0 μ - n * k0 μ)| ≤ _
    generalize (x μ + ((z0 μ : ℤ) : ZMod n)).valMinAbs = wx at hkx hwx ⊢
    generalize (b μ + ((z0 μ : ℤ) : ZMod n)).valMinAbs = w0 at hk0μ hw0
    have he : ((n : ℤ) ∣ ((x μ).valMinAbs - (b μ).valMinAbs) - (wx - w0)) :=
      ⟨kx - k0 μ, by linear_combination hkx - hk0μ⟩
    have habs : |((x μ).valMinAbs - (b μ).valMinAbs) - (wx - w0)| < n := by
      rw [abs_le] at hwx hw0 hqx hqb
      rw [abs_lt]
      have : (2 * q + 2 * r : ℕ) < n := hqn
      constructor <;> omega
    have h0 := Int.eq_zero_of_abs_lt_dvd he habs
    have h1 : (n : ℤ) * (kx - k0 μ) = 0 := by linear_combination -hkx + hk0μ + h0
    have : (x μ).valMinAbs + (z0 μ - n * k0 μ) = wx := by linear_combination hkx + h1
    rw [this]; exact hwx

/-- If the integer sums of the centred representatives of `c` and of `z` are at most `r` in absolute value and `2 r + 1 < n`, then the translate `c + z` lies in the centred box of radius `r`. -/
theorem inBox_add_intCast {n r : ℕ} [NeZero n] (hn : 2 * r + 1 < n) (c : Torus d n)
    (z : Fin d → ℤ) (hc : ∀ μ, |(c μ).valMinAbs + z μ| ≤ r) :
    InBox d r n (c + fun μ => ((z μ : ℤ) : ZMod n)) := by
  intro μ
  have h1 : (c + fun μ => ((z μ : ℤ) : ZMod n)) μ = (((c μ).valMinAbs + z μ : ℤ) : ZMod n) := by
    simp
  rw [h1, valMinAbs_intCast_of_abs_le hn (hc μ)]
  exact hc μ

end RecentringInt


end Balaban.Polymer.TwoTorusStep
