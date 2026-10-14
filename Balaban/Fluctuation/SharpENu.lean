/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.InteractionHatE
public import Balaban.Fluctuation.InteractionHatNu
public import Balaban.Fluctuation.SharpEngine
public import Balaban.Fluctuation.PhysicalFNuFanRawY
public import Balaban.Fluctuation.PhysicalReadsE
public import Balaban.Fluctuation.ObsRayBase
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Sharp locality of the old-energy term and of the mass block

The old-energy summand `E` and the mass-variation block summand `ν` of the localized interaction
expand over the polymer domains `Y` with terms that depend on the hat variable only at the unit
points of the sites of `Y` (the relation `AgHatDir`), the raw data still agreeing on the thick set
of `Y`.  These are the sharp versions of `eterm_expansion_hat` and `nublock_expansion_hat`.

* `eTermFun_local_dir`: `eTermFun_local` with the fluctuation variable assumed equal only on the
  sites of `X₁` (the proof reads it only at data sites, which lie in `X₁`).
* `eterm_expansion_hat_dir`, `nublock_expansion_hat_dir`: one `Ev` with the value identity, both
  locality clauses (landed `AgHat` and sharp `AgHatDir`), the bound and analyticity.

* `eterm_locInt_hat_dm_dir`, `eterms_locInt_hat_dm_dir`, `mterms_locInt_hat_dm_dir`,
  `nupart_locInt_hat_dm_dir`, `nupart_locInt_bound_hat_dm_dir`: the localized-integral statements
  that the assembler consumes, with the hat variable compared by `AgHatFDir` and the raw datum
  compared on `Y` itself (from `eterm_expansion_hat_rawY`, `nublock_expansion_hat_rawY`; no new
  relation is defined here).

The V and F summands, the assembly (`PhysicalSharpLoc`) and `physical_directTerms` are separate and
not treated here.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Analysis
  Balaban.Fluctuation Finset Matrix Set Metric

section SharpE

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱ₁ ϱ₂ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Gk : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁}
variable {Gj : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₂}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ r₀ eps δ₃ : ℝ} {X₀ X₁f : Finset (CTorus d L N₁ m₁ (k + 1))} {j : ℕ}
variable {Kc Cx c₂ BG₂ δ₁ δfl : ℝ} {m₀ : ℕ} {X 𝒦X : Set (CTorus d L N₁ m₁ (k + 1))}

/-- **Locality of the old-term functional, exact form**: as `eTermFun_local_dir`, with the raw data
assumed equal on `X₁` itself (not on `thickSet X₁`), and the background field assumed equal only at
the sites it is read at, namely the composite sites `composeDep Gk Gp x` of the data sites `x`
(these lie in `X₁`). -/
theorem eTermFun_local_rawY (hB : BgSetting N Gp Gk Gj a₁ ν c BG κ r₀ eps δ₃ X₀ X₁f j)
    (hF : FlSetting N Gp Gk Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl X₁f)
    (hcov : CovSetup Gp m₀ j X 𝒦X) (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp m₀ j 𝒦X)
    (Fk : RawData d L (N₁ * L ^ m₁) (k + 1) N → (Gk.Ω 1 × Fin N → ℂ) × (Gk.Ω 1 → ℂ))
    (E : RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ)
    {t t' : ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) × (Hm.Ω 1 × Fin N → ℂ) ×
      (RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ))}
    (hφ : ∀ x ∈ dataSites Gk, ∀ y : Gp.Ω 1,
      (y : CTorus d L N₁ m₁ (k + 1)) ∈ composeDep Gk Gp x → ∀ i, t.1.1 (y, i) = t'.1.1 (y, i))
    (hδ : ∀ y : Hm.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) →
      ∀ i, t.2.1 (y, i) = t'.2.1 (y, i))
    (hag : agreeOn (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) t.2.2.1 t'.2.2.1)
    (hψ : ∀ y ∈ (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))), t.2.2.2 y = t'.2.2.2 y) :
    eTermFun Gp Gk Gj Hm (compWeight L a₁) Fk E t.1 t.2.1 t.2.2 =
      eTermFun Gp Gk Gj Hm (compWeight L a₁) Fk E t'.1 t'.2.1 t'.2.2 := by
  classical
  have hX₁Ω : (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) ⊆ ↑(Gp.Ω 1) := fun x hx =>
    X1_subset_Omega1 hcov (hX₁ ▸ hx)
  have hXthick : ∀ y ∈ X₁f, t.2.2.1.1 y = t'.2.2.1.1 y ∧ t.2.2.1.2 y = t'.2.2.1.2 y := fun y hy =>
    hag y (Finset.mem_coe.2 hy)
  refine congrArg E (congrArg (D2raw Gk Gj (compWeight L a₁) Fk) ?_)
  refine Prod.ext (funext fun x => funext fun i => ?_) (funext fun x => funext fun i => ?_)
  · show composeField Gk Gp (compWeight L a₁) t.1.1 t.2.2.1.1 x i +
        composeField Gk Hm (compWeight L a₁) t.2.1 t.2.2.2 x i =
      composeField Gk Gp (compWeight L a₁) t'.1.1 t'.2.2.1.1 x i +
        composeField Gk Hm (compWeight L a₁) t'.2.1 t'.2.2.2 x i
    by_cases hx : x ∈ dataSites Gk
    · congr 1
      · refine composeField_congr (G := Gk) (G' := Gp) (compWeight L a₁) (fun y hy jj => ?_)
          (fun jj => congrFun (hXthick x (hB.dep x hx x (self_mem_composeDep x))).1 jj) i
        have hyX := hB.dep x hx y hy
        have hyΩ : y ∈ Gp.Ω 1 := hX₁Ω (Finset.mem_coe.2 hyX)
        rw [svec_of_mem' t.1.1 hyΩ jj, svec_of_mem' t'.1.1 hyΩ jj]
        exact hφ x hx ⟨y, hyΩ⟩ hy jj
      · refine composeField_congr (G := Gk) (G' := Hm) (compWeight L a₁) (fun y hy jj => ?_)
          (fun jj => congrFun (hψ x (Finset.mem_coe.2 (hF.depm x hx x
            (self_mem_composeDep x)))) jj) i
        have hyX := hF.depm x hx y hy
        by_cases hyΩ : y ∈ Hm.Ω 1
        · rw [svec_of_mem' t.2.1 hyΩ jj, svec_of_mem' t'.2.1 hyΩ jj]
          exact hδ ⟨y, hyΩ⟩ (Finset.mem_coe.2 hyX) jj
        · rw [svec_of_not_mem Hm t.2.1 hyΩ jj, svec_of_not_mem Hm t'.2.1 hyΩ jj]
    · rw [composeField_of_not_mem _ _ _ hx, composeField_of_not_mem _ _ _ hx,
        composeField_of_not_mem _ _ _ hx, composeField_of_not_mem _ _ _ hx]
  · show (if x ∈ Gk.Ω 1 then t.2.2.1.2 x i else 0) = (if x ∈ Gk.Ω 1 then t'.2.2.1.2 x i else 0)
    by_cases hx : x ∈ Gk.Ω 1
    · simp only [hx, ↓reduceIte]
      have hxd : x ∈ dataSites Gk := (mem_dataSites Gk).2 (Or.inl hx)
      exact congrFun (hXthick x (hB.dep x hxd x (self_mem_composeDep x))).2 i
    · simp [hx]

/-- **Locality of the old-term functional, sharp form**: as `eTermFun_local`, with the fluctuation
variable assumed equal only on the sites of `X₁`. -/
theorem eTermFun_local_dir (hB : BgSetting N Gp Gk Gj a₁ ν c BG κ r₀ eps δ₃ X₀ X₁f j)
    (hF : FlSetting N Gp Gk Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl X₁f)
    (hcov : CovSetup Gp m₀ j X 𝒦X) (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp m₀ j 𝒦X)
    (Fk : RawData d L (N₁ * L ^ m₁) (k + 1) N → (Gk.Ω 1 × Fin N → ℂ) × (Gk.Ω 1 → ℂ))
    (E : RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ)
    {t t' : ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) × (Hm.Ω 1 × Fin N → ℂ) ×
      (RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ))}
    (hφ : ∀ y : Gp.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) →
      ∀ i, t.1.1 (y, i) = t'.1.1 (y, i))
    (hδ : ∀ y : Hm.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) →
      ∀ i, t.2.1 (y, i) = t'.2.1 (y, i))
    (hag : agreeOn (thickSet Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1)))) t.2.2.1 t'.2.2.1)
    (hψ : ∀ y ∈ (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))), t.2.2.2 y = t'.2.2.2 y) :
    eTermFun Gp Gk Gj Hm (compWeight L a₁) Fk E t.1 t.2.1 t.2.2 =
      eTermFun Gp Gk Gj Hm (compWeight L a₁) Fk E t'.1 t'.2.1 t'.2.2 :=
  eTermFun_local_rawY hB hF hcov hX₁ Fk E
    (fun x hx y hy i => hφ y (Finset.mem_coe.2 (hB.dep x hx y hy)) i) hδ
    (fun y hy => hag y (Or.inl hy)) hψ

/-- **Exact locality of the old-term functional, in the fan form.**  `fan_local_rawY` at
`Φ := eTermFun … Fk E`: for sharp agreement on a component `compY … C` of the marked family (raw data
on the component, hat variables at the unit points of the component) the composite is the same.  The
background field is needed only at the composite sites of the data sites; there it is the sum of the
approximate field, which reads the raw data inside `X₁` (`approxField_composeDep_congr`), and the
correction, which agrees on the component (`i4b_local_of_agree_on_component`). -/
theorem eterm_fan_local_rawY (hB : BgSetting N Gp Gk Gj a₁ ν c BG κ r₀ eps δ₃ X₀ X₁f j)
    (hF : FlSetting N Gp Gk Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl X₁f)
    (hk : 1 ≤ k) (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    (hcov : CovSetup Gp m₀ j X 𝒦X) (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp m₀ j 𝒦X)
    (hconn : HatConn Gp) (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
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
    (Fk : RawData d L (N₁ * L ^ m₁) (k + 1) N → (Gk.Ω 1 × Fin N → ℂ) × (Gk.Ω 1 → ℂ))
    (E : RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ) :
    LocalityAEOn (Real.exp κ)
      (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ})
      (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => Pset m₁ i.1.1)
      (compY (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1)
        (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))))
      (fun C u u' => agreeOn (compY
        (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1)
        (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) C) u.1 u'.1 ∧
        ∀ y ∈ compY (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1)
          (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) C,
          ∀ i, u.2 (unitPt hG' y, i) = u'.2 (unitPt hG' y, i))
      (fun u s => (eTermFun Gp Gk Gj Hm (compWeight L a₁) Fk E) (F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s, u.1))
        (Sol (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s,
          flEdat Gp Hm (F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s, u.1))
            u.1.1 (hatPsiF Gp a₁ ν hG' cc F₁
              (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s) u.1 u.2))).1
        (u.1, hatPsiF Gp a₁ ν hG' cc F₁
          (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s) u.1 u.2)) := by
  classical
  have hC := flCore_of hB hF
  have hX₁Ω : (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) ⊆ ↑(Gp.Ω 1) := fun x hx =>
    X1_subset_Omega1 hcov (hX₁ ▸ hx)
  have hd0 : 0 < d := by have := hC.HBp.hd; omega
  have hc1 := one_le_xiC1 d
  have hε := hC.eps_pos
  have hδ0 : 0 < xiC1 d * eps := by positivity
  have hδ1' : xiC1 d * eps ≤ c7 d L N BG κ := hC.c7le
  have hδ0' : xiC1 d * eps ≤ bgC0 d L N := hδ1'.trans ((c7_le_bgC1 d L N BG κ).trans
    (bgC1_le_bgC0 d L N hd0))
  have hνε : ν * ((L : ℝ) ^ (k + 1)) ^ 2 * (xiC1 d * eps) ^ 2 ≤ (xiC1 d * eps) ^ 2 := by
    have := hC.HBp.massLe; nlinarith [sq_nonneg (xiC1 d * eps)]
  refine fan_local_rawY hC hk hG hG' cc hcψ hMX hdm hα hsm hδ₁ hcov hX₁ hconn hrow hF₁ hSol
    (eTermFun Gp Gk Gj Hm (compWeight L a₁) Fk E)
    (fun {sx sx'} hs hs' {D D'} hD hD' {Y} C hY hs1 hs0
      hag hX₁c h𝒞 hdata ψh ψh' hh {φ φ₂} {α α₂} hI hI₂ Hh Hh' {δα δα'} hfix hsmδ hfix' hsmδ'
      hmemY hαY hψY => ?_)
  have hflc := fluct_correction_rows_of_agree_on_component hC hk hG' hG cc hconn hrow hMX hdm hα
    hsm hF₁ hs hs' hD hD' hY hs1 hs0 hag hX₁c h𝒞 hdata ψh ψh' hh hI hI₂ Hh Hh'
    hfix hsmδ hfix' hsmδ'
  have hXY' : ∀ x ∈ X₁f, x ∈ Y := fun x hx => (hmemY x).2 (subset_compY
    (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) C (Finset.mem_coe.2 hx))
  have hDom := xiCData_inDomainC hC.HBp hC.small1 hD
  have hDom' := xiCData_inDomainC hC.HBp hC.small1 hD'
  obtain ⟨-, hφd, -⟩ := i4b_local_of_agree_on_component hC.hS hC.Sp hconn hC.HBp hC.hκ.le hC.hM
    (fun P => (hs P).le) (fun P => (hs' P).le) hδ0 le_rfl hδ0' hδ1' hνε hDom hDom' hG' hY
    hs1 hs0 hag hdata hI hI₂
  have hΨh : ∀ y ∈ X₁f, D.Ψ y = D'.Ψ y ∧ D.h y = D'.h y := fun y hy =>
    ⟨(hdata y (hXY' y hy)).1, (hdata y (hXY' y hy)).2 (hX₁Ω (Finset.mem_coe.2 hy))⟩
  refine eTermFun_local_rawY hB hF hcov hX₁ Fk E
    (t := ((φ, α), _, (rawOf D, hatPsiF Gp a₁ ν hG' cc F₁ sx (rawOf D) ψh)))
    (t' := ((φ₂, α₂), _, (rawOf D', hatPsiF Gp a₁ ν hG' cc F₁ sx' (rawOf D') ψh')))
    (fun x hx y hy i => ?_) (fun y hy i => hflc.2 y (hXY' _ (by simpa using hy)) i)
    (fun y hy => hΨh y (by simpa using hy)) (fun y hy => hψY y (hXY' y (by simpa using hy)))
  have hyX : (y : CTorus d L N₁ m₁ (k + 1)) ∈ X₁f := hB.dep x hx y hy
  have h1 := hφd y (hXY' _ hyX) i
  have h2 : approxField Gp (compWeight L a₁) ν D.Ψ D.h y i =
      approxField Gp (compWeight L a₁) ν D'.Ψ D'.h y i :=
    congrFun (approxField_composeDep_congr hB hG' hΨh hx hy) i
  show φ (y, i) = φ₂ (y, i)
  rw [h2] at h1
  exact sub_left_injective h1

/-- **An old term expands over the domains `Y ⊃ X₁`, exact locality**: `eterm_expansion_hat_dir`
with one locality clause, for raw data agreeing on `Y` itself and hat variables agreeing at the unit
points of `Y`.  Obtained from `i5_functional_hatLC_rawY_of_fan` and `eterm_fan_local_rawY`; the thick
statement `eterm_expansion_hat_dir` is its corollary and returns the same `Ev`. -/
theorem eterm_expansion_hat_rawY_of_one_le {b : ℝ} (hb₁ : 1 ≤ b) (hbC : b ≤ scaledC0 d)
    (hB : BgSetting N Gp Gk Gj a₁ ν c BG κ r₀ eps δ₃ X₀ X₁f j)
    (hF : FlSetting N Gp Gk Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl X₁f)
    (hk : 1 ≤ k) (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    (hcov : CovSetup Gp m₀ j X 𝒦X) (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp m₀ j 𝒦X)
    (hconn : HatConn Gp) (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
    (hopt : ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X) ∧ MeetsOne m₀ j 𝒦X W₀ ∧
        bondCost (scaleW L m₀ m₁ j) E₀ = treeLenCovOne m₀ j X)
    {κdec κ₀ Eb : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hEb : 0 ≤ Eb) {E : RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ}
    (hEan : AnalyticOnNhd ℂ E (XiCRaw Gj (compWeight L a₁) ν j b
      (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)))
    (hEbd : ∀ r ∈ XiCRaw Gj (compWeight L a₁) ν j b
      (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      ‖E r‖ ≤ Eb * Real.exp (-(κdec - 1) * treeLenCovOne m₀ j X)) :
    ∃ Ev : Set (CTorus d L N₁ m₁ (k + 1)) →
        RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gp × Fin N → ℂ) → ℂ,
      (∀ D : BgData Gp N, XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D →
        ∀ ψh : unitPts Gp × Fin N → ℂ, (∀ p, ‖ψh p‖ ≤ cψ) →
        flComp hB hF E (rawOf D, hatLift Gp a₁ ν hG' cc D ψh) =
        ∑ Y ∈ polymerDomains (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1)
          Gp m₀ (X1 Gp m₀ j 𝒦X), Ev Y (rawOf D, ψh)) ∧
      (∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        ∀ u' ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        agreeOn Y u.1 u'.1 → (∀ y ∈ Y, ∀ i, u.2 (unitPt hG' y, i) = u'.2 (unitPt hG' y, i)) →
        Ev Y u = Ev Y u') ∧
      (∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        ‖Ev Y u‖ ≤ Eb * Real.exp (-κ₀ * treeLenCovOne m₀ j X - 2 * κdec * treeLenCov Gp m₀ Y)) ∧
      (∀ Y, AnalyticOnNhd ℂ (Ev Y) (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ})) := by
  classical
  obtain ⟨Fk, hFkan, hFk⟩ := theorem72_analytic (G := Gk) (a := compWeight L a₁) (ν := ν) hB.HBk
  have hC := flCore_of hB hF
  obtain ⟨Ev, h1', h2', h3', h4'⟩ := i5_functional_hatLC_rawY_of_fan hC hk hG hG' cc hcψ hMX hdm hα
    hsm hδ₁ hcov hX₁ hopt hκ₀ hκdec hκ h1 hlog hEb
    (Φ := eTermFun Gp Gk Gj Hm (compWeight L a₁) Fk E)
    (eTermFun_analytic_of_one_le hb₁ hbC hB hF hFkan hFk hEan)
    (fun t ht => eTermFun_bound_of_one_le hb₁ hbC hB hF hFk hEbd ht)
    (fun {F₁} hF₁ {Sol} hSol => eterm_fan_local_rawY hB hF hk hG hG' cc hcψ hMX hdm hα hsm hδ₁ hcov
      hX₁ hconn hrow hF₁ hSol Fk E)
  refine ⟨Ev, fun D hD ψh hψh => ?_, h2', h3', h4'⟩
  rw [← h1' D hD ψh hψh]
  exact (eTermFun_value hB hF hFk E hD
    (hatLift_mem_flBallLC hC hk hG hG' cc hcψ hMX hdm hα hsm hδ₁ hD hψh)).symm

/-- **An old term expands over the domains `Y ⊃ X₁`, exact locality**: `eterm_expansion_hat_dir`
with one locality clause, for raw data agreeing on `Y` itself and hat variables agreeing at the unit
points of `Y`.  Obtained from `i5_functional_hatLC_rawY_of_fan` and `eterm_fan_local_rawY`; the thick
statement `eterm_expansion_hat_dir` is its corollary and returns the same `Ev`. -/
theorem eterm_expansion_hat_rawY (hB : BgSetting N Gp Gk Gj a₁ ν c BG κ r₀ eps δ₃ X₀ X₁f j)
    (hF : FlSetting N Gp Gk Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl X₁f)
    (hk : 1 ≤ k) (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    (hcov : CovSetup Gp m₀ j X 𝒦X) (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp m₀ j 𝒦X)
    (hconn : HatConn Gp) (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
    (hopt : ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X) ∧ MeetsOne m₀ j 𝒦X W₀ ∧
        bondCost (scaleW L m₀ m₁ j) E₀ = treeLenCovOne m₀ j X)
    {κdec κ₀ Eb : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hEb : 0 ≤ Eb) {E : RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ}
    (hEan : AnalyticOnNhd ℂ E (XiCRaw Gj (compWeight L a₁) ν j (scaledC0 d)
      (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)))
    (hEbd : ∀ r ∈ XiCRaw Gj (compWeight L a₁) ν j (scaledC0 d)
      (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      ‖E r‖ ≤ Eb * Real.exp (-(κdec - 1) * treeLenCovOne m₀ j X)) :
    ∃ Ev : Set (CTorus d L N₁ m₁ (k + 1)) →
        RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gp × Fin N → ℂ) → ℂ,
      (∀ D : BgData Gp N, XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D →
        ∀ ψh : unitPts Gp × Fin N → ℂ, (∀ p, ‖ψh p‖ ≤ cψ) →
        flComp hB hF E (rawOf D, hatLift Gp a₁ ν hG' cc D ψh) =
        ∑ Y ∈ polymerDomains (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1)
          Gp m₀ (X1 Gp m₀ j 𝒦X), Ev Y (rawOf D, ψh)) ∧
      (∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        ∀ u' ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        agreeOn Y u.1 u'.1 → (∀ y ∈ Y, ∀ i, u.2 (unitPt hG' y, i) = u'.2 (unitPt hG' y, i)) →
        Ev Y u = Ev Y u') ∧
      (∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        ‖Ev Y u‖ ≤ Eb * Real.exp (-κ₀ * treeLenCovOne m₀ j X - 2 * κdec * treeLenCov Gp m₀ Y)) ∧
      (∀ Y, AnalyticOnNhd ℂ (Ev Y) (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ})) :=
  eterm_expansion_hat_rawY_of_one_le (one_le_scaledC0 d) le_rfl hB hF hk hG hG' cc hcψ hMX hdm hα hsm hδ₁ hcov hX₁ hconn hrow hopt hκ₀ hκdec hκ h1 hlog hEb hEan hEbd

/-- **An old term expands over the domains `Y ⊃ X₁`, with terms local in `ψ̂` at the unit points
of `Y` only** (sharp form of `eterm_expansion_hat`; the landed `AgHat` clause is also returned). -/
theorem eterm_expansion_hat_dir (hB : BgSetting N Gp Gk Gj a₁ ν c BG κ r₀ eps δ₃ X₀ X₁f j)
    (hF : FlSetting N Gp Gk Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl X₁f)
    (hk : 1 ≤ k) (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    (hcov : CovSetup Gp m₀ j X 𝒦X) (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp m₀ j 𝒦X)
    (hconn : HatConn Gp) (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
    (hopt : ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X) ∧ MeetsOne m₀ j 𝒦X W₀ ∧
        bondCost (scaleW L m₀ m₁ j) E₀ = treeLenCovOne m₀ j X)
    {κdec κ₀ Eb : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hEb : 0 ≤ Eb) {E : RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ}
    (hEan : AnalyticOnNhd ℂ E (XiCRaw Gj (compWeight L a₁) ν j (scaledC0 d)
      (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)))
    (hEbd : ∀ r ∈ XiCRaw Gj (compWeight L a₁) ν j (scaledC0 d)
      (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      ‖E r‖ ≤ Eb * Real.exp (-(κdec - 1) * treeLenCovOne m₀ j X)) :
    ∃ Ev : Set (CTorus d L N₁ m₁ (k + 1)) →
        RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gp × Fin N → ℂ) → ℂ,
      (∀ D : BgData Gp N, XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D →
        ∀ ψh : unitPts Gp × Fin N → ℂ, (∀ p, ‖ψh p‖ ≤ cψ) →
        flComp hB hF E (rawOf D, hatLift Gp a₁ ν hG' cc D ψh) =
        ∑ Y ∈ polymerDomains (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1)
          Gp m₀ (X1 Gp m₀ j 𝒦X), Ev Y (rawOf D, ψh)) ∧
      (∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        ∀ u' ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        AgHat hG' Y u u' → Ev Y u = Ev Y u') ∧
      (∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        ∀ u' ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        AgHatDir hG' Y u u' → Ev Y u = Ev Y u') ∧
      (∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        ‖Ev Y u‖ ≤ Eb * Real.exp (-κ₀ * treeLenCovOne m₀ j X - 2 * κdec * treeLenCov Gp m₀ Y)) ∧
      (∀ Y, AnalyticOnNhd ℂ (Ev Y) (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ})) := by
  obtain ⟨Ev, hs, hd, hb, ha⟩ := eterm_expansion_hat_rawY hB hF hk hG hG' cc hcψ hMX hdm hα hsm hδ₁
    hcov hX₁ hconn hrow hopt hκ₀ hκdec hκ h1 hlog hEb hEan hEbd
  have hd' : ∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        ∀ u' ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        AgHatDir hG' Y u u' → Ev Y u = Ev Y u' :=
    fun Y u hu u' hu' h => hd Y u hu u' hu' (agreeOn_mono (fun x hx => Or.inl hx) h.1) h.2
  exact ⟨Ev, hs, fun Y u hu u' hu' h => hd' Y u hu u' hu' (agHatDir_of_agHat hG' h), hd', hb, ha⟩

/-- **Ray-differentiable form of `eterm_locInt_hat_dm_dir`.**  The statement of `eterm_locInt_hat_dm_dir` together with the
differentiability of the terms along the complex hat ray `z ↦ z • ψ̂` on `‖z‖ < 3/2`. -/
theorem eterm_locInt_hat_dm_dir_ray (hB : BgSetting N Gp Gk Gj a₁ ν c BG κ r₀ eps δ₃ X₀ X₁f j)
    (hF : FlSetting N Gp Gk Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl X₁f)
    (hk : 1 ≤ k) (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    (hcov : CovSetup Gp m₀ j X 𝒦X) (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp m₀ j 𝒦X)
    (hconn : HatConn Gp) (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
    (hopt : ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X) ∧ MeetsOne m₀ j 𝒦X W₀ ∧
        bondCost (scaleW L m₀ m₁ j) E₀ = treeLenCovOne m₀ j X)
    {κdec κ₀ Eb : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hEb : 0 ≤ Eb) {E : RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ}
    (hEan : AnalyticOnNhd ℂ E (XiCRaw Gj (compWeight L a₁) ν j (scaledC0 d)
      (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)))
    (hEbd : ∀ r ∈ XiCRaw Gj (compWeight L a₁) ν j (scaledC0 d)
      (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      ‖E r‖ ≤ Eb * Real.exp (-(κdec - 1) * treeLenCovOne m₀ j X))
    {ω : ℂ → ℂ} (hωc : Continuous ω) {R₁ : ℝ} (hR₁ : 1 < R₁)
    (hω : AnalyticOnNhd ℂ ω (ball (0 : ℂ) R₁)) {Mω : ℝ} (hMω : 0 ≤ Mω)
    (hωb : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → ‖ω (t : ℂ)‖ ≤ Mω) {r Rσ : ℝ} (hr : 0 < r) :
    ∃ Ev : Set (CTorus d L N₁ m₁ (k + 1)) →
        RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gp × Fin N → ℂ) → ℂ,
      LocIntDm (IsDj m₀ (k + 1)) (id : (unitPts Gp × Fin N → ℂ) → _)
        (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps) (HatRaysO Gp cψ R₁ Rσ r) Rσ
        (polymerDomains (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) Gp m₀
          (X1 Gp m₀ j 𝒦X))
        (fun Y x₀ w σ Θ => dirTerm (Ev Y) ω x₀ w σ Θ)
        (fun x₀ w σ Θ => dirTermSrc (hatFun Gp a₁ ν eps hG' cc (flComp hB hF E)) ω x₀ w σ Θ)
        (fun Y => Mω * ((Eb * Real.exp (-κ₀ * treeLenCovOne m₀ j X
          - 2 * κdec * treeLenCov Gp m₀ Y)) / r))
        (fun Y Θ Θ' => agreeOn Y Θ Θ') (AgHatFDir hG')
      ∧ (∀ (Y : Set (CTorus d L N₁ m₁ (k + 1))) (Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N),
        Θ ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps → ∀ ψ : unitPts Gp × Fin N → ℂ,
        (∀ p, (R₁ + r) * (3 / 2) * ‖ψ p‖ ≤ cψ) →
        DifferentiableOn ℂ (fun z : ℂ => dirTerm (Ev Y) ω (z • ψ) (z • ψ) 1 Θ)
          (ball (0 : ℂ) (3 / 2))) := by
  classical
  obtain ⟨Ev, hsum, hloc, hbd, hanY⟩ := eterm_expansion_hat_rawY hB hF hk hG hG' cc hcψ hMX hdm hα hsm
    hδ₁ hcov hX₁ hconn hrow hopt hκ₀ hκdec hκ h1 hlog hEb hEan hEbd
  have hd : 3 ≤ d := (flCore_of hB hF).HBp.hd
  have hray : ∀ (Y : Set (CTorus d L N₁ m₁ (k + 1))) (Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N),
      Θ ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps → ∀ ψ : unitPts Gp × Fin N → ℂ,
      (∀ p, (R₁ + r) * (3 / 2) * ‖ψ p‖ ≤ cψ) →
      DifferentiableOn ℂ (fun z : ℂ => dirTerm (Ev Y) ω (z • ψ) (z • ψ) 1 Θ)
        (ball (0 : ℂ) (3 / 2)) :=
    fun Y Θ hΘ ψ hψ => differentiableOn_dirTerm_ray_ball hR₁ hr hω (hanY Y) hΘ ψ hψ
  refine ⟨Ev, ?_, hray⟩
  have hbase := locInt_dir1 (S := XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps)
    (B := hatBall (N := N) Gp cψ)
    (f := hatFun Gp a₁ ν eps hG' cc (flComp hB hF E))
    (polymerDomains (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) Gp m₀
      (X1 Gp m₀ j 𝒦X)) (Evs := Ev)
    (b := fun Y => Eb * Real.exp (-κ₀ * treeLenCovOne m₀ j X - 2 * κdec * treeLenCov Gp m₀ Y))
    (AgΘ := fun Y Θ Θ' => agreeOn Y Θ Θ')
    (AgF := AgHatFDir hG') (Rσ := Rσ) hR₁ hω hωc hMω hωb hr
    (isOpen_hatBall cψ) (fun Y => (hanY Y).mono (Set.prod_mono le_rfl (hatBall_subset cψ)))
    (fun Y u hu => hbd Y u ⟨hu.1, hatBall_subset cψ hu.2⟩)
    (fun Y a a' c' c'' p q ha hb y hy i => by simp [ha y hy i, hb y hy i])
    (fun Y Θ hΘ Θ' hΘ' z hz z' hz' h1' h2' =>
      hloc Y (Θ, z) ⟨hΘ, hatBall_subset cψ hz⟩ (Θ', z') ⟨hΘ', hatBall_subset cψ hz'⟩ h1' h2')
    (fun Θ hΘ ψh hψ => by
      obtain ⟨D, hD, rfl⟩ := hΘ
      rw [hatFun_rawOf hG' cc _ hD]
      exact hsum D hD ψh (hatBall_subset cψ hψ))
  exact LocIntDm.mk hbase (fun Y hY => isDj_of_polyDom hG' hcov hd hopt hY)
    (diagCont_dirTerm _ hR₁ hωc hr
      (fun Y => (hanY Y).mono (Set.prod_mono le_rfl (hatBall_subset cψ))))

/-- **The `δ𝓔'`-term of one old term in the variable `ψ̂`** (hat version of `eterm_locInt`).

Sharp form: the hat variable is compared only at the unit points of the sites of `Y`, the raw
datum only on `Y` itself. -/
theorem eterm_locInt_hat_dm_dir (hB : BgSetting N Gp Gk Gj a₁ ν c BG κ r₀ eps δ₃ X₀ X₁f j)
    (hF : FlSetting N Gp Gk Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl X₁f)
    (hk : 1 ≤ k) (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    (hcov : CovSetup Gp m₀ j X 𝒦X) (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp m₀ j 𝒦X)
    (hconn : HatConn Gp) (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
    (hopt : ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X) ∧ MeetsOne m₀ j 𝒦X W₀ ∧
        bondCost (scaleW L m₀ m₁ j) E₀ = treeLenCovOne m₀ j X)
    {κdec κ₀ Eb : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hEb : 0 ≤ Eb) {E : RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ}
    (hEan : AnalyticOnNhd ℂ E (XiCRaw Gj (compWeight L a₁) ν j (scaledC0 d)
      (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)))
    (hEbd : ∀ r ∈ XiCRaw Gj (compWeight L a₁) ν j (scaledC0 d)
      (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      ‖E r‖ ≤ Eb * Real.exp (-(κdec - 1) * treeLenCovOne m₀ j X))
    {ω : ℂ → ℂ} (hωc : Continuous ω) {R₁ : ℝ} (hR₁ : 1 < R₁)
    (hω : AnalyticOnNhd ℂ ω (ball (0 : ℂ) R₁)) {Mω : ℝ} (hMω : 0 ≤ Mω)
    (hωb : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → ‖ω (t : ℂ)‖ ≤ Mω) {r Rσ : ℝ} (hr : 0 < r) :
    ∃ Ev : Set (CTorus d L N₁ m₁ (k + 1)) →
        RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gp × Fin N → ℂ) → ℂ,
      LocIntDm (IsDj m₀ (k + 1)) (id : (unitPts Gp × Fin N → ℂ) → _)
        (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps) (HatRaysO Gp cψ R₁ Rσ r) Rσ
        (polymerDomains (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) Gp m₀
          (X1 Gp m₀ j 𝒦X))
        (fun Y x₀ w σ Θ => dirTerm (Ev Y) ω x₀ w σ Θ)
        (fun x₀ w σ Θ => dirTermSrc (hatFun Gp a₁ ν eps hG' cc (flComp hB hF E)) ω x₀ w σ Θ)
        (fun Y => Mω * ((Eb * Real.exp (-κ₀ * treeLenCovOne m₀ j X
          - 2 * κdec * treeLenCov Gp m₀ Y)) / r))
        (fun Y Θ Θ' => agreeOn Y Θ Θ') (AgHatFDir hG') := by
  classical
  exact (eterm_locInt_hat_dm_dir_ray hB hF hk hG hG' cc (cψ := cψ) hcψ hMX (δc := δc) hdm hα hsm hδ₁ hcov hX₁ hconn hrow hopt (κdec := κdec) (κ₀ := κ₀) (Eb := Eb) hκ₀ hκdec hκ h1 hlog hEb (E := E) hEan hEbd (ω := ω) hωc (R₁ := R₁) hR₁ hω (Mω := Mω) hMω hωb (r := r) (Rσ := Rσ) hr).imp fun _ h => h.1


end SharpE

section SharpEFamily

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ eps : ℝ}

/-- **Ray-differentiable form of `eterms_locInt_hat_dm_dir`.**  The statement of `eterms_locInt_hat_dm_dir` together with the
differentiability of the terms along the complex hat ray `z ↦ z • ψ̂` on `‖z‖ < 3/2`. -/
theorem eterms_locInt_hat_dm_dir_ray {τι : Type*} [DecidableEq τι] (𝒯 : Finset τι) {ϱ₁ ϱ₂ : τι → ℝ}
    {Gk : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₁ τ)}
    {Gj : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₂ τ)}
    {r₀ δ₃ : ℝ} {X₀ X₁f : τι → Finset (CTorus d L N₁ m₁ (k + 1))} {j m₀ : τι → ℕ}
    {X 𝒦X : τι → Set (CTorus d L N₁ m₁ (k + 1))} {Kc Cx c₂ BG₂ δ₁ δfl : ℝ}
    (hB : ∀ τ ∈ 𝒯, BgSetting N Gp (Gk τ) (Gj τ) a₁ ν c BG κ r₀ eps δ₃ (X₀ τ) (X₁f τ) (j τ))
    (hF : ∀ τ ∈ 𝒯, FlSetting N Gp (Gk τ) Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl (X₁f τ))
    (hk : 1 ≤ k) (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    (hcov : ∀ τ ∈ 𝒯, CovSetup Gp (m₀ τ) (j τ) (X τ) (𝒦X τ))
    (hX₁ : ∀ τ ∈ 𝒯, (↑(X₁f τ) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp (m₀ τ) (j τ) (𝒦X τ))
    (hconn : HatConn Gp) (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
    (hopt : ∀ τ ∈ 𝒯, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X τ) ∧ MeetsOne (m₀ τ) (j τ) (𝒦X τ) W₀ ∧
        bondCost (scaleW L (m₀ τ) m₁ (j τ)) E₀ = treeLenCovOne (m₀ τ) (j τ) (X τ))
    {κdec κ₀ : ℝ} {Eb : τι → ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : ∀ τ ∈ 𝒯, Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀ τ) ^ d : ℕ) : ℝ)) ≤
      (κ / 2 - 1) / 2)
    (hEb : ∀ τ ∈ 𝒯, 0 ≤ Eb τ) {E : τι → RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ}
    (hEan : ∀ τ ∈ 𝒯, AnalyticOnNhd ℂ (E τ) (XiCRaw (Gj τ) (compWeight L a₁) ν (j τ) (scaledC0 d)
      (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)))
    (hEbd : ∀ τ ∈ 𝒯, ∀ r ∈ XiCRaw (Gj τ) (compWeight L a₁) ν (j τ) (scaledC0 d)
      (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      ‖E τ r‖ ≤ Eb τ * Real.exp (-(κdec - 1) * treeLenCovOne (m₀ τ) (j τ) (X τ)))
    {ω : ℂ → ℂ} (hωc : Continuous ω) {R₁ : ℝ} (hR₁ : 1 < R₁)
    (hω : AnalyticOnNhd ℂ ω (ball (0 : ℂ) R₁)) {Mω : ℝ} (hMω : 0 ≤ Mω)
    (hωb : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → ‖ω (t : ℂ)‖ ≤ Mω) {r Rσ : ℝ} (hr : 0 < r) :
    ∃ (T : τι → Set (CTorus d L N₁ m₁ (k + 1)) → (unitPts Gp × Fin N → ℂ) →
        (unitPts Gp × Fin N → ℂ) → ℂ → RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ),
      LocIntDm (fun Y => ∃ τ ∈ 𝒯, IsDj (m₀ τ) (k + 1) Y) (id : (unitPts Gp × Fin N → ℂ) → _)
        (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps) (HatRaysO Gp cψ R₁ Rσ r) Rσ
        (𝒯.biUnion fun τ => polyDom Gp (X₁f τ) (m₀ τ) (j τ) (𝒦X τ))
        (fun Y x₀ w σ Θ => ∑ τ ∈ 𝒯, if Y ∈ polyDom Gp (X₁f τ) (m₀ τ) (j τ) (𝒦X τ) then
          T τ Y x₀ w σ Θ else 0)
        (fun x₀ w σ Θ => ∑ τ ∈ 𝒯, if h : τ ∈ 𝒯 then
          dirTermSrc (hatFun Gp a₁ ν eps hG' cc (flComp (hB τ h) (hF τ h) (E τ))) ω x₀ w σ Θ
          else 0)
        (fun Y => ∑ τ ∈ 𝒯, if Y ∈ polyDom Gp (X₁f τ) (m₀ τ) (j τ) (𝒦X τ) then
          Mω * ((Eb τ * Real.exp (-κ₀ * treeLenCovOne (m₀ τ) (j τ)
          (X τ) - 2 * κdec * treeLenCov Gp (m₀ τ) Y)) / r) else 0)
        (fun Y Θ Θ' => agreeOn Y Θ Θ') (AgHatFDir hG')
      ∧ (∀ (Y : Set (CTorus d L N₁ m₁ (k + 1))) (Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N),
        Θ ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps → ∀ ψ : unitPts Gp × Fin N → ℂ,
        (∀ p, (R₁ + r) * (3 / 2) * ‖ψ p‖ ≤ cψ) →
        DifferentiableOn ℂ (fun z : ℂ => ∑ τ ∈ 𝒯,
          if Y ∈ polyDom Gp (X₁f τ) (m₀ τ) (j τ) (𝒦X τ) then
            T τ Y (z • ψ) (z • ψ) 1 Θ else 0) (ball (0 : ℂ) (3 / 2))) := by
  classical
  have hex : ∀ τ, ∃ (Ev : Set (CTorus d L N₁ m₁ (k + 1)) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gp × Fin N → ℂ) → ℂ), τ ∈ 𝒯 →
      LocIntDm (fun Y => ∃ τ' ∈ 𝒯, IsDj (m₀ τ') (k + 1) Y) (id : (unitPts Gp × Fin N → ℂ) → _)
        (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps) (HatRaysO Gp cψ R₁ Rσ r) Rσ
        (polymerDomains (fun i : ParIdx Gp (↑(X₁f τ) : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1)
          Gp (m₀ τ) (X1 Gp (m₀ τ) (j τ) (𝒦X τ)))
        (fun Y x₀ w σ Θ => dirTerm (Ev Y) ω x₀ w σ Θ)
        (fun x₀ w σ Θ => if h : τ ∈ 𝒯 then
          dirTermSrc (hatFun Gp a₁ ν eps hG' cc (flComp (hB τ h) (hF τ h) (E τ))) ω x₀ w σ Θ
          else 0)
        (fun Y => Mω * ((Eb τ * Real.exp (-κ₀ * treeLenCovOne (m₀ τ) (j τ)
          (X τ) - 2 * κdec * treeLenCov Gp (m₀ τ) Y)) / r))
        (fun Y Θ Θ' => agreeOn Y Θ Θ') (AgHatFDir hG') ∧
      (∀ (Y : Set (CTorus d L N₁ m₁ (k + 1))) (Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N),
        Θ ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps → ∀ ψ : unitPts Gp × Fin N → ℂ,
        (∀ p, (R₁ + r) * (3 / 2) * ‖ψ p‖ ≤ cψ) →
        DifferentiableOn ℂ (fun z : ℂ => dirTerm (Ev Y) ω (z • ψ) (z • ψ) 1 Θ)
          (ball (0 : ℂ) (3 / 2))) := by
    intro τ
    by_cases hτ : τ ∈ 𝒯
    · obtain ⟨Ev, hEv, hray⟩ := eterm_locInt_hat_dm_dir_ray (hB τ hτ) (hF τ hτ) hk hG hG' cc hcψ hMX hdm hα hsm hδ₁
        (hcov τ hτ) (hX₁ τ hτ) hconn hrow (hopt τ hτ) hκ₀ hκdec hκ h1 (hlog τ hτ) (hEb τ hτ)
        (hEan τ hτ) (hEbd τ hτ) hωc hR₁ hω hMω hωb hr (Rσ := Rσ)
      exact ⟨Ev, fun _ => ⟨by simpa [hτ] using hEv.mono_P fun Y hY => ⟨τ, hτ, hY⟩, hray⟩⟩
    · exact ⟨fun _ _ => 0, fun h => absurd h hτ⟩
  choose Ev hEv using hex
  refine ⟨fun τ Y x₀ w σ Θ => dirTerm (Ev τ Y) ω x₀ w σ Θ,
    LocIntDm.finsum 𝒯 (fun τ hτ => (hEv τ hτ).1), fun Y Θ hΘ ψ hψ => ?_⟩
  apply DifferentiableOn.fun_sum
  intro τ hτ
  by_cases hY : Y ∈ polyDom Gp (X₁f τ) (m₀ τ) (j τ) (𝒦X τ)
  · simpa only [hY, ite_true] using (hEv τ hτ).2 Y Θ hΘ ψ hψ
  · simpa only [hY, ite_false] using differentiableOn_const (0 : ℂ)

/-- **The `δ𝓔'`-part for a finite family of old terms, in the variable `ψ̂`** (hat version of
`eterms_locInt`).

Sharp form: the hat variable is compared only at the unit points of the sites of `Y`, the raw
datum only on `Y` itself. -/
theorem eterms_locInt_hat_dm_dir {τι : Type*} [DecidableEq τι] (𝒯 : Finset τι) {ϱ₁ ϱ₂ : τι → ℝ}
    {Gk : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₁ τ)}
    {Gj : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₂ τ)}
    {r₀ δ₃ : ℝ} {X₀ X₁f : τι → Finset (CTorus d L N₁ m₁ (k + 1))} {j m₀ : τι → ℕ}
    {X 𝒦X : τι → Set (CTorus d L N₁ m₁ (k + 1))} {Kc Cx c₂ BG₂ δ₁ δfl : ℝ}
    (hB : ∀ τ ∈ 𝒯, BgSetting N Gp (Gk τ) (Gj τ) a₁ ν c BG κ r₀ eps δ₃ (X₀ τ) (X₁f τ) (j τ))
    (hF : ∀ τ ∈ 𝒯, FlSetting N Gp (Gk τ) Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl (X₁f τ))
    (hk : 1 ≤ k) (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    (hcov : ∀ τ ∈ 𝒯, CovSetup Gp (m₀ τ) (j τ) (X τ) (𝒦X τ))
    (hX₁ : ∀ τ ∈ 𝒯, (↑(X₁f τ) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp (m₀ τ) (j τ) (𝒦X τ))
    (hconn : HatConn Gp) (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
    (hopt : ∀ τ ∈ 𝒯, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X τ) ∧ MeetsOne (m₀ τ) (j τ) (𝒦X τ) W₀ ∧
        bondCost (scaleW L (m₀ τ) m₁ (j τ)) E₀ = treeLenCovOne (m₀ τ) (j τ) (X τ))
    {κdec κ₀ : ℝ} {Eb : τι → ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : ∀ τ ∈ 𝒯, Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀ τ) ^ d : ℕ) : ℝ)) ≤
      (κ / 2 - 1) / 2)
    (hEb : ∀ τ ∈ 𝒯, 0 ≤ Eb τ) {E : τι → RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ}
    (hEan : ∀ τ ∈ 𝒯, AnalyticOnNhd ℂ (E τ) (XiCRaw (Gj τ) (compWeight L a₁) ν (j τ) (scaledC0 d)
      (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)))
    (hEbd : ∀ τ ∈ 𝒯, ∀ r ∈ XiCRaw (Gj τ) (compWeight L a₁) ν (j τ) (scaledC0 d)
      (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      ‖E τ r‖ ≤ Eb τ * Real.exp (-(κdec - 1) * treeLenCovOne (m₀ τ) (j τ) (X τ)))
    {ω : ℂ → ℂ} (hωc : Continuous ω) {R₁ : ℝ} (hR₁ : 1 < R₁)
    (hω : AnalyticOnNhd ℂ ω (ball (0 : ℂ) R₁)) {Mω : ℝ} (hMω : 0 ≤ Mω)
    (hωb : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → ‖ω (t : ℂ)‖ ≤ Mω) {r Rσ : ℝ} (hr : 0 < r) :
    ∃ (T : τι → Set (CTorus d L N₁ m₁ (k + 1)) → (unitPts Gp × Fin N → ℂ) →
        (unitPts Gp × Fin N → ℂ) → ℂ → RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ),
      LocIntDm (fun Y => ∃ τ ∈ 𝒯, IsDj (m₀ τ) (k + 1) Y) (id : (unitPts Gp × Fin N → ℂ) → _)
        (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps) (HatRaysO Gp cψ R₁ Rσ r) Rσ
        (𝒯.biUnion fun τ => polyDom Gp (X₁f τ) (m₀ τ) (j τ) (𝒦X τ))
        (fun Y x₀ w σ Θ => ∑ τ ∈ 𝒯, if Y ∈ polyDom Gp (X₁f τ) (m₀ τ) (j τ) (𝒦X τ) then
          T τ Y x₀ w σ Θ else 0)
        (fun x₀ w σ Θ => ∑ τ ∈ 𝒯, if h : τ ∈ 𝒯 then
          dirTermSrc (hatFun Gp a₁ ν eps hG' cc (flComp (hB τ h) (hF τ h) (E τ))) ω x₀ w σ Θ
          else 0)
        (fun Y => ∑ τ ∈ 𝒯, if Y ∈ polyDom Gp (X₁f τ) (m₀ τ) (j τ) (𝒦X τ) then
          Mω * ((Eb τ * Real.exp (-κ₀ * treeLenCovOne (m₀ τ) (j τ)
          (X τ) - 2 * κdec * treeLenCov Gp (m₀ τ) Y)) / r) else 0)
        (fun Y Θ Θ' => agreeOn Y Θ Θ') (AgHatFDir hG') := by
  classical
  exact (eterms_locInt_hat_dm_dir_ray (τι := τι) 𝒯 (ϱ₁ := ϱ₁) (ϱ₂ := ϱ₂) (Gk := Gk) (Gj := Gj) (r₀ := r₀) (δ₃ := δ₃) (X₀ := X₀) (X₁f := X₁f) (j := j) (m₀ := m₀) (X := X) (𝒦X := 𝒦X) (Kc := Kc) (Cx := Cx) (c₂ := c₂) (BG₂ := BG₂) (δ₁ := δ₁) (δfl := δfl) hB hF hk hG hG' cc (cψ := cψ) hcψ hMX (δc := δc) hdm hα hsm hδ₁ hcov hX₁ hconn hrow hopt (κdec := κdec) (κ₀ := κ₀) (Eb := Eb) hκ₀ hκdec hκ h1 hlog hEb (E := E) hEan hEbd (ω := ω) hωc (R₁ := R₁) hR₁ hω (Mω := Mω) hMω hωb (r := r) (Rσ := Rσ) hr).imp fun _ h => h.1

/-- **The `𝓜`-terms of the source along the fluctuation, in the variable `ψ̂`** (hat version of
`mterms_locInt`).

Sharp form: the hat variable is compared only at the unit points of the sites of `Y`, the raw
datum only on `Y` itself. -/
theorem mterms_locInt_hat_dm_dir {τι : Type*} [DecidableEq τι] (𝒯 : Finset τι) {ϱ₁ ϱ₂ : τι → ℝ}
    {Gk : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₁ τ)}
    {Gj : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₂ τ)}
    {r₀ δ₃ : ℝ} {X₀ X₁f : τι → Finset (CTorus d L N₁ m₁ (k + 1))} {j m₀ : τι → ℕ}
    {X 𝒦X : τι → Set (CTorus d L N₁ m₁ (k + 1))} {Kc Cx c₂ BG₂ δ₁ δfl : ℝ}
    (ys : τι → CTorus d L N₁ m₁ (k + 1)) (is : τι → Fin N) (hys : ∀ τ ∈ 𝒯, ys τ ∈ X₁f τ)
    (hB : ∀ τ ∈ 𝒯, BgSetting N Gp (Gk τ) (Gj τ) a₁ ν c BG κ r₀ eps δ₃ (X₀ τ) (X₁f τ) (j τ))
    (hF : ∀ τ ∈ 𝒯, FlSetting N Gp (Gk τ) Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl (X₁f τ))
    (hk : 1 ≤ k) (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    (hcov : ∀ τ ∈ 𝒯, CovSetup Gp (m₀ τ) (j τ) (X τ) (𝒦X τ))
    (hX₁ : ∀ τ ∈ 𝒯, (↑(X₁f τ) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp (m₀ τ) (j τ) (𝒦X τ))
    (hconn : HatConn Gp) (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
    (hopt : ∀ τ ∈ 𝒯, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X τ) ∧ MeetsOne (m₀ τ) (j τ) (𝒦X τ) W₀ ∧
        bondCost (scaleW L (m₀ τ) m₁ (j τ)) E₀ = treeLenCovOne (m₀ τ) (j τ) (X τ))
    {κdec κ₀ : ℝ} {Eb : τι → ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : ∀ τ ∈ 𝒯, Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀ τ) ^ d : ℕ) : ℝ)) ≤
      (κ / 2 - 1) / 2)
    (hEb : ∀ τ ∈ 𝒯, 0 ≤ Eb τ) {E : τι → RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ}
    (hEan : ∀ τ ∈ 𝒯, AnalyticOnNhd ℂ (E τ) (XiCRaw (Gj τ) (compWeight L a₁) ν (j τ) (scaledC0 d)
      (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)))
    (hEbd : ∀ τ ∈ 𝒯, ∀ r ∈ XiCRaw (Gj τ) (compWeight L a₁) ν (j τ) (scaledC0 d)
      (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      ‖E τ r‖ ≤ Eb τ * Real.exp (-(κdec - 1) * treeLenCovOne (m₀ τ) (j τ) (X τ)))
    {ω : ℂ → ℂ} (hωc : Continuous ω) {R₁ : ℝ} (hR₁ : 1 < R₁)
    (hω : AnalyticOnNhd ℂ ω (ball (0 : ℂ) R₁)) {Mω : ℝ} (hMω : 0 ≤ Mω)
    (hωb : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → ‖ω (t : ℂ)‖ ≤ Mω) {r Rσ : ℝ} (hr : 0 < r) :
    ∃ (𝒴 : τι → Finset (Set (CTorus d L N₁ m₁ (k + 1))))
      (T : τι → Set (CTorus d L N₁ m₁ (k + 1)) → (unitPts Gp × Fin N → ℂ) →
        (unitPts Gp × Fin N → ℂ) → ℂ → RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ),
      LocIntDm (fun Y => ∃ τ ∈ 𝒯, IsDj (m₀ τ) (k + 1) Y) (id : (unitPts Gp × Fin N → ℂ) → _)
        (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ l1Ball d L N₁ m₁ (k + 1) N)
        (HatRaysO Gp cψ R₁ Rσ r) Rσ
        (𝒯.biUnion 𝒴)
        (fun Y x₀ w σ p => ∑ τ ∈ 𝒯, if Y ∈ 𝒴 τ then p.2 (ys τ) (is τ) * T τ Y x₀ w σ p.1 else 0)
        (fun x₀ w σ p => ∑ τ ∈ 𝒯, if h : τ ∈ 𝒯 then
          p.2 (ys τ) (is τ) * dirTermSrc (hatFun Gp a₁ ν eps hG' cc
            (flComp (hB τ h) (hF τ h) (E τ))) ω x₀ w σ p.1 else 0)
        (fun Y => ∑ τ ∈ 𝒯, if Y ∈ 𝒴 τ then 1 * (Mω * ((Eb τ * Real.exp (-κ₀ * treeLenCovOne
          (m₀ τ) (j τ) (X τ) - 2 * κdec * treeLenCov Gp (m₀ τ) Y)) / r)) else 0)
        (fun Y p p' => agreeOn Y p.1 p'.1 ∧ ∀ x ∈ Y, p.2 x = p'.2 x)
        (AgHatFDir hG') := by
  classical
  have hex : ∀ τ, ∃ (Ev : Set (CTorus d L N₁ m₁ (k + 1)) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gp × Fin N → ℂ) → ℂ), τ ∈ 𝒯 →
      LocIntDm (fun Y => ∃ τ' ∈ 𝒯, IsDj (m₀ τ') (k + 1) Y) (id : (unitPts Gp × Fin N → ℂ) → _)
        (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ l1Ball d L N₁ m₁ (k + 1) N)
        (HatRaysO Gp cψ R₁ Rσ r) Rσ
        (polymerDomains (fun i : ParIdx Gp (↑(X₁f τ) : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1)
          Gp (m₀ τ) (X1 Gp (m₀ τ) (j τ) (𝒦X τ)))
        (fun Y x₀ w σ p => p.2 (ys τ) (is τ) * dirTerm (Ev Y) ω x₀ w σ p.1)
        (fun x₀ w σ p => if h : τ ∈ 𝒯 then
          p.2 (ys τ) (is τ) * dirTermSrc (hatFun Gp a₁ ν eps hG' cc
            (flComp (hB τ h) (hF τ h) (E τ))) ω x₀ w σ p.1 else 0)
        (fun Y => 1 * (Mω * ((Eb τ * Real.exp (-κ₀ * treeLenCovOne (m₀ τ) (j τ)
          (X τ) - 2 * κdec * treeLenCov Gp (m₀ τ) Y)) / r)))
        (fun Y p p' => agreeOn Y p.1 p'.1 ∧ ∀ x ∈ Y, p.2 x = p'.2 x)
        (AgHatFDir hG') := by
    intro τ
    by_cases hτ : τ ∈ 𝒯
    · obtain ⟨Ev, hEv⟩ := eterm_locInt_hat_dm_dir (hB τ hτ) (hF τ hτ) hk hG hG' cc hcψ hMX hdm hα hsm hδ₁
        (hcov τ hτ) (hX₁ τ hτ) hconn hrow (hopt τ hτ) hκ₀ hκdec hκ h1 (hlog τ hτ) (hEb τ hτ)
        (hEan τ hτ) (hEbd τ hτ) hωc hR₁ hω hMω hωb hr (Rσ := Rσ)
      refine ⟨Ev, fun _ => ?_⟩
      have := (hEv.mono_P (P' := fun Y => ∃ τ' ∈ 𝒯, IsDj (m₀ τ') (k + 1) Y)
        fun Y hY => ⟨τ, hτ, hY⟩).mulAmp (SG := l1Ball d L N₁ m₁ (k + 1) N) (amp := fun g => g (ys τ) (is τ))
        (Ma := 1)
        ((analyticOnNhd_coord (ys τ) (is τ)).mono (Set.subset_univ _))
        (fun g hg => norm_le_of_mem_l1Ball hg (ys τ) (is τ))
        (AgG := fun Y g g' => ∀ x ∈ Y, g x = g' x) (by
          intro Y hY g _ g' _ hag
          have hyY : ys τ ∈ Y := subset_of_mem_polymerDomains hY (by
            rw [← hX₁ τ hτ]; exact hys τ hτ)
          exact congrFun (hag _ hyY) _)
      simpa [hτ] using this
    · exact ⟨fun _ _ => 0, fun h => absurd h hτ⟩
  choose Ev hEv using hex
  exact ⟨fun τ => polymerDomains (fun i : ParIdx Gp (↑(X₁f τ) : Set (CTorus d L N₁ m₁ (k + 1))) =>
      i.1.1) Gp (m₀ τ) (X1 Gp (m₀ τ) (j τ) (𝒦X τ)),
    fun τ Y x₀ w σ Θ => dirTerm (Ev τ Y) ω x₀ w σ Θ, LocIntDm.finsum 𝒯 (fun τ hτ => hEv τ hτ)⟩

end SharpEFamily

section SharpNu

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ} {X₁f : Finset (CTorus d L N₁ m₁ (k + 1))} {j : ℕ}
variable {m₀ : ℕ} {X 𝒦X : Set (CTorus d L N₁ m₁ (k + 1))}

/-- **The mass block expands over the domains `Y ⊃ X₁`, exact locality** (`nublock_expansion_hat_dir`
with one locality clause, for raw data agreeing on `Y` itself and hat variables agreeing at the unit
points of `Y`).  Obtained from `i5_functional_hat_rawY_of_fan` and `nublock_fan_local_rawY`; the term
The thick corollary uses the same `Ev` selected here. -/
theorem nublock_expansion_hat_rawY (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hk : 1 ≤ k) (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    {Bh : ℝ} (hBh0 : 0 ≤ Bh)
    (hBh : ∀ D : BgData Gp N, XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D →
      ∀ x i, ‖D.h x i‖ ≤ Bh)
    (hcov : CovSetup Gp m₀ j X 𝒦X)
    (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp m₀ j 𝒦X)
    (hconn : HatConn Gp) (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
    (hopt : ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X) ∧ MeetsOne m₀ j 𝒦X W₀ ∧
        bondCost (scaleW L m₀ m₁ j) E₀ = treeLenCovOne m₀ j X)
    (hΔ : treeLenCovOne m₀ j X = 0)
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))))
    (hZ : (↑(blockSites d L N₁ m₁ (k + 1) k z) : Set (CTorus d L N₁ m₁ (k + 1))) ⊆ ↑X₁f) :
    ∃ Ev : Set (CTorus d L N₁ m₁ (k + 1)) →
        RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gp × Fin N → ℂ) → ℂ,
      (∀ D : BgData Gp N, XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D →
        ∀ ψh : unitPts Gp × Fin N → ℂ, (∀ p, ‖ψh p‖ ≤ cψ) →
        nuBlockFun Gp Hm k z (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D,
            bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D)
          (flFieldOne Gp Hm BG₂ κ a₁ ν D (hatLift Gp a₁ ν hG' cc D ψh))
          (rawOf D, hatLift Gp a₁ ν hG' cc D ψh) =
          ∑ Y ∈ polyDom Gp X₁f m₀ j 𝒦X, Ev Y (rawOf D, ψh)) ∧
      (∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        ∀ u' ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        agreeOn Y u.1 u'.1 → (∀ y ∈ Y, ∀ i, u.2 (unitPt hG' y, i) = u'.2 (unitPt hG' y, i)) →
        Ev Y u = Ev Y u') ∧
      (∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        ‖Ev Y u‖ ≤ nuBd d L N k (cK2' d L N (famConst d L BG₂ κ) * δ₁)
          (K4 d L N BG κ * (xiC1 d * eps) + (1 + 3 * (xiC1 d * eps)) + Bh) *
          Real.exp (-2 * κdec * treeLenCov Gp m₀ Y)) ∧
      (∀ Y, AnalyticOnNhd ℂ (Ev Y) (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ})) := by
  have hd0 : 0 < d := by have := hC.HBp.hd; omega
  have hB0 : 0 ≤ famConst d L BG₂ κ := by
    have := famConst_ge_one (L := L) hC.hS2.fam.2.1 κ hd0; linarith
  have hV : 0 ≤ cK2' d L N (famConst d L BG₂ κ) * δ₁ :=
    mul_nonneg (cK2'_nonneg hB0) hC.δ₁_pos.le
  have hB1 : 0 ≤ K4 d L N BG κ * (xiC1 d * eps) + (1 + 3 * (xiC1 d * eps)) + Bh := by
    have hK4 : 0 < K4 d L N BG κ := K4_pos (L := L) (N := N) (κ := κ) hC.hS.fam.2.1 hd0
    have hx1 := one_le_xiC1 d
    have hx2 := hC.eps_pos
    have hx3 : 0 ≤ xiC1 d * eps := by positivity
    have hx4 := mul_nonneg hK4.le hx3
    linarith
  have hEb : 0 ≤ nuBd d L N k (cK2' d L N (famConst d L BG₂ κ) * δ₁)
      (K4 d L N BG κ * (xiC1 d * eps) + (1 + 3 * (xiC1 d * eps)) + Bh) := by
    unfold nuBd; positivity
  obtain ⟨Ev, h1', h2', h3', h4', -⟩ := i5_functional_hat_rawY_of_fan hC hk hG hG' cc hcψ hMX hdm hα hsm hδ₁ hcov
    hX₁ hopt hκ₀ hκdec hκ h1 hlog hEb (Φ := nuBlockFun Gp Hm k z)
    ((nuBlockFun_analytic (Gp := Gp) (Hm := Hm) k z).mono (Set.subset_univ _))
    (fun t ht => by
      rw [hΔ]; simpa using nuBlockFun_bound hC le_rfl hG' hBh0 hBh z ht)
    (fun {F₁} hF₁ {Sol} hSol => nublock_fan_local_rawY hC hk hG hG' cc hcψ hMX hdm hα hsm hδ₁ hcov hX₁
      hconn hrow hF₁ hSol z hZ)
  refine ⟨Ev, h1', h2', fun Y u hu => ?_, h4'⟩
  have := h3' Y u hu
  rw [hΔ] at this
  simpa using this


/-- **The mass block expands over the domains `Y ⊃ X₁`, with terms local in `ψ̂` at the unit
points of `Y` only** (sharp form of `nublock_expansion_hat`). -/
theorem nublock_expansion_hat_dir (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hk : 1 ≤ k) (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    {Bh : ℝ} (hBh0 : 0 ≤ Bh)
    (hBh : ∀ D : BgData Gp N, XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D →
      ∀ x i, ‖D.h x i‖ ≤ Bh)
    (hcov : CovSetup Gp m₀ j X 𝒦X)
    (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp m₀ j 𝒦X)
    (hconn : HatConn Gp) (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
    (hopt : ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X) ∧ MeetsOne m₀ j 𝒦X W₀ ∧
        bondCost (scaleW L m₀ m₁ j) E₀ = treeLenCovOne m₀ j X)
    (hΔ : treeLenCovOne m₀ j X = 0)
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))))
    (hZ : (↑(blockSites d L N₁ m₁ (k + 1) k z) : Set (CTorus d L N₁ m₁ (k + 1))) ⊆ ↑X₁f) :
    ∃ Ev : Set (CTorus d L N₁ m₁ (k + 1)) →
        RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gp × Fin N → ℂ) → ℂ,
      (∀ D : BgData Gp N, XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D →
        ∀ ψh : unitPts Gp × Fin N → ℂ, (∀ p, ‖ψh p‖ ≤ cψ) →
        nuBlockFun Gp Hm k z (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D,
            bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D)
          (flFieldOne Gp Hm BG₂ κ a₁ ν D (hatLift Gp a₁ ν hG' cc D ψh))
          (rawOf D, hatLift Gp a₁ ν hG' cc D ψh) =
          ∑ Y ∈ polyDom Gp X₁f m₀ j 𝒦X, Ev Y (rawOf D, ψh)) ∧
      (∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        ∀ u' ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        AgHat hG' Y u u' → Ev Y u = Ev Y u') ∧
      (∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        ∀ u' ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        AgHatDir hG' Y u u' → Ev Y u = Ev Y u') ∧
      (∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        ‖Ev Y u‖ ≤ nuBd d L N k (cK2' d L N (famConst d L BG₂ κ) * δ₁)
          (K4 d L N BG κ * (xiC1 d * eps) + (1 + 3 * (xiC1 d * eps)) + Bh) *
          Real.exp (-2 * κdec * treeLenCov Gp m₀ Y)) ∧
      (∀ Y, AnalyticOnNhd ℂ (Ev Y) (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ})) := by
  obtain ⟨Ev, hs, hd, hb, ha⟩ := nublock_expansion_hat_rawY hC hk hG hG' cc hcψ hMX hdm hα hsm hδ₁ hBh0 hBh
    hcov hX₁ hconn hrow hopt hΔ hκ₀ hκdec hκ h1 hlog z hZ
  have hd' : ∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        ∀ u' ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        AgHatDir hG' Y u u' → Ev Y u = Ev Y u' :=
    fun Y u hu u' hu' h => hd Y u hu u' hu' (agreeOn_mono (fun x hx => Or.inl hx) h.1) h.2
  exact ⟨Ev, hs, fun Y u hu u' hu' h => hd' Y u hu u' hu' (agHatDir_of_agHat hG' h), hd', hb, ha⟩

end SharpNu

section SharpNuPart

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ}
variable {j : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → ℕ}
variable {X 𝒦X : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Set (CTorus d L N₁ m₁ (k + 1))}
variable {X₁z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Finset (CTorus d L N₁ m₁ (k + 1))}
variable {m₀ : ℕ}

/-- **Ray-differentiable form of `nupart_locInt_hat_dm_dir`.**  The statement of `nupart_locInt_hat_dm_dir` together with the
differentiability of the terms along the complex hat ray `z ↦ z • ψ̂` on `‖z‖ < 3/2`. -/
theorem nupart_locInt_hat_dm_dir_ray (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hk : 1 ≤ k) (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    {Bh : ℝ} (hBh0 : 0 ≤ Bh)
    (hBh : ∀ D : BgData Gp N, XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D →
      ∀ x i, ‖D.h x i‖ ≤ Bh)
    (hcov : ∀ z, CovSetup Gp m₀ (j z) (X z) (𝒦X z))
    (hX₁ : ∀ z, (↑(X₁z z) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp m₀ (j z) (𝒦X z))
    (hconn : HatConn Gp) (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
    (hopt : ∀ z, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X z) ∧ MeetsOne m₀ (j z) (𝒦X z) W₀ ∧
        bondCost (scaleW L m₀ m₁ (j z)) E₀ = treeLenCovOne m₀ (j z) (X z))
    (hΔ : ∀ z, treeLenCovOne m₀ (j z) (X z) = 0)
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hZ : ∀ z, (↑(blockSites d L N₁ m₁ (k + 1) k z) : Set (CTorus d L N₁ m₁ (k + 1))) ⊆
      ↑(X₁z z))
    {ω : ℂ → ℂ} (hωc : Continuous ω) {R₁ : ℝ} (hR₁ : 1 < R₁)
    (hω : AnalyticOnNhd ℂ ω (ball (0 : ℂ) R₁)) {Mω : ℝ} (hMω : 0 ≤ Mω)
    (hωb : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → ‖ω (t : ℂ)‖ ≤ Mω) {r Rσ : ℝ} (hr : 0 < r) :
    ∃ T : Set (CTorus d L N₁ m₁ (k + 1)) → (unitPts Gp × Fin N → ℂ) →
        (unitPts Gp × Fin N → ℂ) → ℂ → RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ,
      LocIntDm (IsDj m₀ (k + 1)) (id : (unitPts Gp × Fin N → ℂ) → _)
        (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps) (HatRaysO Gp cψ R₁ Rσ r) Rσ
        (Finset.univ.biUnion fun z => polyDom Gp (X₁z z) m₀ (j z) (𝒦X z)) T
        (fun x₀ w σ Θ => dirTermSrc (hatFun Gp a₁ ν eps hG' cc (onXi Gp a₁ ν eps
          (fun D ψ' => nuTotal Gp Hm a₁ ν BG₂ κ D ψ'))) ω x₀ w σ Θ)
        (fun Y => Mω * ((∑ z, if Y ∈ polyDom Gp (X₁z z) m₀ (j z) (𝒦X z) then
          nuBd d L N k (cK2' d L N (famConst d L BG₂ κ) * δ₁)
            (K4 d L N BG κ * (xiC1 d * eps) + (1 + 3 * (xiC1 d * eps)) + Bh) *
            Real.exp (-2 * κdec * treeLenCov Gp m₀ Y) else 0) / r))
        (fun Y Θ Θ' => agreeOn Y Θ Θ') (AgHatFDir hG')
      ∧ (∀ (Y : Set (CTorus d L N₁ m₁ (k + 1))) (Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N),
        Θ ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps → ∀ ψ : unitPts Gp × Fin N → ℂ,
        (∀ p, (R₁ + r) * (3 / 2) * ‖ψ p‖ ≤ cψ) →
        DifferentiableOn ℂ (fun z : ℂ => T Y (z • ψ) (z • ψ) 1 Θ) (ball (0 : ℂ) (3 / 2))) := by
  classical
  have hex : ∀ z, ∃ Ev : Set (CTorus d L N₁ m₁ (k + 1)) →
        RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gp × Fin N → ℂ) → ℂ,
      (∀ D : BgData Gp N, XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D →
        ∀ ψh : unitPts Gp × Fin N → ℂ, (∀ p, ‖ψh p‖ ≤ cψ) →
        nuBlockFun Gp Hm k z (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D,
            bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D)
          (flFieldOne Gp Hm BG₂ κ a₁ ν D (hatLift Gp a₁ ν hG' cc D ψh))
          (rawOf D, hatLift Gp a₁ ν hG' cc D ψh) =
          ∑ Y ∈ polyDom Gp (X₁z z) m₀ (j z) (𝒦X z), Ev Y (rawOf D, ψh)) ∧
      (∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        ∀ u' ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        agreeOn Y u.1 u'.1 → (∀ y ∈ Y, ∀ i, u.2 (unitPt hG' y, i) = u'.2 (unitPt hG' y, i)) →
        Ev Y u = Ev Y u') ∧
      (∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        ‖Ev Y u‖ ≤ nuBd d L N k (cK2' d L N (famConst d L BG₂ κ) * δ₁)
          (K4 d L N BG κ * (xiC1 d * eps) + (1 + 3 * (xiC1 d * eps)) + Bh) *
          Real.exp (-2 * κdec * treeLenCov Gp m₀ Y)) ∧
      (∀ Y, AnalyticOnNhd ℂ (Ev Y) (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ})) :=
    fun z => nublock_expansion_hat_rawY hC hk hG hG' cc hcψ hMX hdm hα hsm hδ₁ hBh0 hBh (hcov z)
      (hX₁ z) hconn hrow (hopt z) (hΔ z) hκ₀ hκdec hκ h1 hlog z (hZ z)
  choose Ev hsum hloc hbd han using hex
  refine ⟨fun Y x₀ w σ Θ => dirTerm (fun u => ∑ z, if Y ∈ polyDom Gp (X₁z z) m₀ (j z) (𝒦X z) then
    Ev z Y u else 0) ω x₀ w σ Θ, ?_, ?_⟩
  have hanO : ∀ z Y, AnalyticOnNhd ℂ (Ev z Y) (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
      hatBall (N := N) Gp cψ) := fun z Y =>
    (han z Y).mono (Set.prod_mono le_rfl (hatBall_subset cψ))
  have hd : 3 ≤ d := hC.HBp.hd
  have hanS : ∀ Y, AnalyticOnNhd ℂ
      (fun u => ∑ z, if Y ∈ polyDom Gp (X₁z z) m₀ (j z) (𝒦X z) then Ev z Y u else 0)
      (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ hatBall (N := N) Gp cψ) := by
    intro Y u hu
    refine Finset.analyticAt_fun_sum _ fun z _ => ?_
    by_cases hY : Y ∈ polyDom Gp (X₁z z) m₀ (j z) (𝒦X z)
    · simpa only [hY, ite_true] using hanO z Y u hu
    · simp only [hY, ite_false]; exact analyticAt_const
  refine LocIntDm.mk (locInt_dir1 (S := XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps)
    (B := hatBall (N := N) Gp cψ)
    (f := hatFun Gp a₁ ν eps hG' cc (onXi Gp a₁ ν eps
      (fun D ψ' => nuTotal Gp Hm a₁ ν BG₂ κ D ψ')))
    (Finset.univ.biUnion fun z => polyDom Gp (X₁z z) m₀ (j z) (𝒦X z))
    (Evs := fun Y u => ∑ z, if Y ∈ polyDom Gp (X₁z z) m₀ (j z) (𝒦X z) then Ev z Y u else 0)
    (b := fun Y => ∑ z, if Y ∈ polyDom Gp (X₁z z) m₀ (j z) (𝒦X z) then
      nuBd d L N k (cK2' d L N (famConst d L BG₂ κ) * δ₁)
        (K4 d L N BG κ * (xiC1 d * eps) + (1 + 3 * (xiC1 d * eps)) + Bh) *
        Real.exp (-2 * κdec * treeLenCov Gp m₀ Y) else 0)
    (AgΘ := fun Y Θ Θ' => agreeOn Y Θ Θ')
    (AgF := AgHatFDir hG') (Rσ := Rσ) hR₁ hω hωc hMω hωb hr
    (isOpen_hatBall cψ) ?_ ?_ ?_ ?_ ?_) ?_ ?_
  · intro Y u hu
    refine Finset.analyticAt_fun_sum _ fun z _ => ?_
    by_cases hY : Y ∈ polyDom Gp (X₁z z) m₀ (j z) (𝒦X z)
    · simpa only [hY, ite_true] using hanO z Y u hu
    · simp only [hY, ite_false]; exact analyticAt_const
  · intro Y u hu
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun z _ => ?_)
    by_cases hY : Y ∈ polyDom Gp (X₁z z) m₀ (j z) (𝒦X z)
    · simpa only [hY, ite_true] using hbd z Y u ⟨hu.1, hatBall_subset cψ hu.2⟩
    · simp [hY]
  · intro Y a a' c' c'' p q ha hb y hy i
    simp [ha y hy i, hb y hy i]
  · intro Y Θ hΘ Θ' hΘ' z hz z' hz' h1' h2'
    refine Finset.sum_congr rfl fun z'' _ => ?_
    by_cases hY : Y ∈ polyDom Gp (X₁z z'') m₀ (j z'') (𝒦X z'')
    · simp only [hY, ite_true]
      exact hloc z'' Y (Θ, z) ⟨hΘ, hatBall_subset cψ hz⟩ (Θ', z')
        ⟨hΘ', hatBall_subset cψ hz'⟩ h1' h2'
    · simp [hY]
  · rintro Θ ⟨D, hD, rfl⟩ ψh hψ
    rw [hatFun_rawOf hG' cc _ hD, onXi_rawOf hD, ← sum_nuBlockFun (n := k) a₁ ν BG₂ κ D _,
      Finset.sum_comm]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [hsum z D hD ψh (hatBall_subset cψ hψ), Finset.sum_ite_mem,
      Finset.inter_eq_right.2 (Finset.subset_biUnion_of_mem
        (fun z => polyDom Gp (X₁z z) m₀ (j z) (𝒦X z)) (Finset.mem_univ z))]
  · intro Y hY
    obtain ⟨z₀, -, hz₀⟩ := Finset.mem_biUnion.1 hY
    exact isDj_of_polyDom hG' (hcov z₀) hd (hopt z₀) hz₀
  · exact diagCont_dirTerm _ hR₁ hωc hr hanS
  · intro Y Θ hΘ ψ hψ
    refine differentiableOn_dirTerm_ray_ball hR₁ hr hω ?_ hΘ ψ hψ
    intro u hu
    refine Finset.analyticAt_fun_sum _ fun z _ => ?_
    by_cases hY : Y ∈ polyDom Gp (X₁z z) m₀ (j z) (𝒦X z)
    · simpa only [hY, ite_true] using han z Y u hu
    · simp only [hY, ite_false]; exact analyticAt_const

/-- **The `ν`-part of the localized interaction in the variable `ψ̂`**: `σ ∫₀¹ ω(t') ∂_w V_{ν,1}`
along a `ψ̂`-ray, with `V_{ν,1}` along the decoupled fluctuation (`nuTotal`), is a localized
expansion over the domains `Y ⊃ X₁(z)`.

Sharp form: the hat variable is compared only at the unit points of the sites of `Y`, the raw
datum only on `Y` itself. -/
theorem nupart_locInt_hat_dm_dir (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hk : 1 ≤ k) (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    {Bh : ℝ} (hBh0 : 0 ≤ Bh)
    (hBh : ∀ D : BgData Gp N, XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D →
      ∀ x i, ‖D.h x i‖ ≤ Bh)
    (hcov : ∀ z, CovSetup Gp m₀ (j z) (X z) (𝒦X z))
    (hX₁ : ∀ z, (↑(X₁z z) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp m₀ (j z) (𝒦X z))
    (hconn : HatConn Gp) (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
    (hopt : ∀ z, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X z) ∧ MeetsOne m₀ (j z) (𝒦X z) W₀ ∧
        bondCost (scaleW L m₀ m₁ (j z)) E₀ = treeLenCovOne m₀ (j z) (X z))
    (hΔ : ∀ z, treeLenCovOne m₀ (j z) (X z) = 0)
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hZ : ∀ z, (↑(blockSites d L N₁ m₁ (k + 1) k z) : Set (CTorus d L N₁ m₁ (k + 1))) ⊆
      ↑(X₁z z))
    {ω : ℂ → ℂ} (hωc : Continuous ω) {R₁ : ℝ} (hR₁ : 1 < R₁)
    (hω : AnalyticOnNhd ℂ ω (ball (0 : ℂ) R₁)) {Mω : ℝ} (hMω : 0 ≤ Mω)
    (hωb : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → ‖ω (t : ℂ)‖ ≤ Mω) {r Rσ : ℝ} (hr : 0 < r) :
    ∃ T : Set (CTorus d L N₁ m₁ (k + 1)) → (unitPts Gp × Fin N → ℂ) →
        (unitPts Gp × Fin N → ℂ) → ℂ → RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ,
      LocIntDm (IsDj m₀ (k + 1)) (id : (unitPts Gp × Fin N → ℂ) → _)
        (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps) (HatRaysO Gp cψ R₁ Rσ r) Rσ
        (Finset.univ.biUnion fun z => polyDom Gp (X₁z z) m₀ (j z) (𝒦X z)) T
        (fun x₀ w σ Θ => dirTermSrc (hatFun Gp a₁ ν eps hG' cc (onXi Gp a₁ ν eps
          (fun D ψ' => nuTotal Gp Hm a₁ ν BG₂ κ D ψ'))) ω x₀ w σ Θ)
        (fun Y => Mω * ((∑ z, if Y ∈ polyDom Gp (X₁z z) m₀ (j z) (𝒦X z) then
          nuBd d L N k (cK2' d L N (famConst d L BG₂ κ) * δ₁)
            (K4 d L N BG κ * (xiC1 d * eps) + (1 + 3 * (xiC1 d * eps)) + Bh) *
            Real.exp (-2 * κdec * treeLenCov Gp m₀ Y) else 0) / r))
        (fun Y Θ Θ' => agreeOn Y Θ Θ') (AgHatFDir hG') := by
  classical
  exact (nupart_locInt_hat_dm_dir_ray hC hk hG hG' cc (cψ := cψ) hcψ hMX (δc := δc) hdm hα hsm hδ₁ (Bh := Bh) hBh0 hBh hcov hX₁ hconn hrow hopt hΔ (κdec := κdec) (κ₀ := κ₀) hκ₀ hκdec hκ h1 hlog hZ (ω := ω) hωc (R₁ := R₁) hR₁ hω (Mω := Mω) hMω hωb (r := r) (Rσ := Rσ) hr).imp fun _ h => h.1

/-- **Ray-differentiable form of `nupart_locInt_bound_hat_dm_dir`.**  The statement of `nupart_locInt_bound_hat_dm_dir` together with the
differentiability of the terms along the complex hat ray `z ↦ z • ψ̂` on `‖z‖ < 3/2`. -/
theorem nupart_locInt_bound_hat_dm_dir_ray (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hk : 1 ≤ k) (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    {Bh : ℝ} (hBh0 : 0 ≤ Bh)
    (hBh : ∀ D : BgData Gp N, XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D →
      ∀ x i, ‖D.h x i‖ ≤ Bh)
    (hcov : ∀ z, CovSetup Gp m₀ (j z) (X z) (𝒦X z))
    (hX₁ : ∀ z, (↑(X₁z z) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp m₀ (j z) (𝒦X z))
    (hconn : HatConn Gp) (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
    (hopt : ∀ z, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X z) ∧ MeetsOne m₀ (j z) (𝒦X z) W₀ ∧
        bondCost (scaleW L m₀ m₁ (j z)) E₀ = treeLenCovOne m₀ (j z) (X z))
    (hΔ : ∀ z, treeLenCovOne m₀ (j z) (X z) = 0)
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hZ : ∀ z, (↑(blockSites d L N₁ m₁ (k + 1) k z) : Set (CTorus d L N₁ m₁ (k + 1))) ⊆
      ↑(X₁z z))
    {ω : ℂ → ℂ} (hωc : Continuous ω) {R₁ : ℝ} (hR₁ : 1 < R₁)
    (hω : AnalyticOnNhd ℂ ω (ball (0 : ℂ) R₁)) {Mω : ℝ} (hMω : 0 ≤ Mω)
    (hωb : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → ‖ω (t : ℂ)‖ ≤ Mω) {r Rσ : ℝ} (hr : 0 < r) :
    ∃ T : Set (CTorus d L N₁ m₁ (k + 1)) → (unitPts Gp × Fin N → ℂ) →
        (unitPts Gp × Fin N → ℂ) → ℂ → RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ,
      LocIntDm (IsDj m₀ (k + 1)) (id : (unitPts Gp × Fin N → ℂ) → _)
        (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps) (HatRaysO Gp cψ R₁ Rσ r) Rσ
        (Finset.univ.biUnion fun z => polyDom Gp (X₁z z) m₀ (j z) (𝒦X z)) T
        (fun x₀ w σ Θ => dirTermSrc (hatFun Gp a₁ ν eps hG' cc (onXi Gp a₁ ν eps
          (fun D ψ' => nuTotal Gp Hm a₁ ν BG₂ κ D ψ'))) ω x₀ w σ Θ)
        (fun Y => Mω * (c1 d L * ((L : ℝ) ^ (m₀ + m₁)) ^ d *
          nuBd d L N k (cK2' d L N (famConst d L BG₂ κ) * δ₁)
            (K4 d L N BG κ * (xiC1 d * eps) + (1 + 3 * (xiC1 d * eps)) + Bh) / r) *
          Real.exp (-(2 * κdec - 1) * treeLenCovOne m₀ (k + 1) Y))
        (fun Y Θ Θ' => agreeOn Y Θ Θ') (AgHatFDir hG')
      ∧ (∀ (Y : Set (CTorus d L N₁ m₁ (k + 1))) (Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N),
        Θ ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps → ∀ ψ : unitPts Gp × Fin N → ℂ,
        (∀ p, (R₁ + r) * (3 / 2) * ‖ψ p‖ ≤ cψ) →
        DifferentiableOn ℂ (fun z : ℂ => T Y (z • ψ) (z • ψ) 1 Θ) (ball (0 : ℂ) (3 / 2))) := by
  classical
  have hd : 3 ≤ d := hC.HBp.hd
  have hd0 : 0 < d := by omega
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hc1 : 0 ≤ c1 d L := by unfold c1; positivity
  have hB0 : 0 ≤ famConst d L BG₂ κ := by
    have := famConst_ge_one (L := L) hC.hS2.fam.2.1 κ hd0; linarith
  have hV : 0 ≤ cK2' d L N (famConst d L BG₂ κ) * δ₁ :=
    mul_nonneg (cK2'_nonneg hB0) hC.δ₁_pos.le
  have hB1 : 0 ≤ K4 d L N BG κ * (xiC1 d * eps) + (1 + 3 * (xiC1 d * eps)) + Bh := by
    have hK4 : 0 < K4 d L N BG κ := K4_pos (L := L) (N := N) (κ := κ) hC.hS.fam.2.1 hd0
    have hx1 := one_le_xiC1 d
    have hx2 := hC.eps_pos
    have hx3 : 0 ≤ xiC1 d * eps := by positivity
    have hx4 := mul_nonneg hK4.le hx3
    linarith
  have hEb : 0 ≤ nuBd d L N k (cK2' d L N (famConst d L BG₂ κ) * δ₁)
      (K4 d L N BG κ * (xiC1 d * eps) + (1 + 3 * (xiC1 d * eps)) + Bh) := by
    unfold nuBd; positivity
  obtain ⟨T, hT, hray⟩ := nupart_locInt_hat_dm_dir_ray hC hk hG hG' cc hcψ hMX hdm hα hsm hδ₁ hBh0 hBh hcov hX₁
    hconn hrow hopt hΔ hκ₀ hκdec hκ h1 hlog hZ hωc hR₁ hω hMω hωb hr (Rσ := Rσ)
  refine ⟨T, hT.mono_on fun Y hY => ?_, hray⟩
  obtain ⟨z₀, -, hz₀⟩ := Finset.mem_biUnion.1 hY
  have hMD := polyDom_isMultiDom (hcov z₀) hd (hopt z₀) hz₀
  have hcard : ((Finset.univ.filter fun z => Y ∈ polyDom Gp (X₁z z) m₀ (j z)
      (𝒦X z)).card : ℝ) ≤ c1 d L * ((L : ℝ) ^ (m₀ + m₁)) ^ d * (1 + treeLenCov Gp m₀ Y) := by
    refine card_blocks_filter_le hG' le_rfl (hcov z₀).hN hMD _ (fun z hz => ?_)
    have h1' := subset_polyDom (Finset.mem_filter.1 hz).2
    rw [← hX₁ z] at h1'
    exact fun x hx => h1' (hZ z hx)
  have ht0 := treeLenCov_nonneg Gp m₀ Y
  have hv : 0 ≤ nuBd d L N k (cK2' d L N (famConst d L BG₂ κ) * δ₁)
      (K4 d L N BG κ * (xiC1 d * eps) + (1 + 3 * (xiC1 d * eps)) + Bh) *
        Real.exp (-2 * κdec * treeLenCov Gp m₀ Y) := by positivity
  have hs := sum_ite_card_le _ hv hcard
  rw [← treeLenCov_eq_treeLenCovOne hG' m₀ Y]
  have key := one_add_mul_exp_le (treeLenCov Gp m₀ Y) κdec
  have hCn : 0 ≤ Mω * (c1 d L * ((L : ℝ) ^ (m₀ + m₁)) ^ d *
      nuBd d L N k (cK2' d L N (famConst d L BG₂ κ) * δ₁)
        (K4 d L N BG κ * (xiC1 d * eps) + (1 + 3 * (xiC1 d * eps)) + Bh) / r) := by positivity
  calc Mω * ((∑ z, if Y ∈ polyDom Gp (X₁z z) m₀ (j z) (𝒦X z) then
          nuBd d L N k (cK2' d L N (famConst d L BG₂ κ) * δ₁)
            (K4 d L N BG κ * (xiC1 d * eps) + (1 + 3 * (xiC1 d * eps)) + Bh) *
            Real.exp (-2 * κdec * treeLenCov Gp m₀ Y) else 0) / r)
      ≤ Mω * ((c1 d L * ((L : ℝ) ^ (m₀ + m₁)) ^ d * (1 + treeLenCov Gp m₀ Y) *
          (nuBd d L N k (cK2' d L N (famConst d L BG₂ κ) * δ₁)
            (K4 d L N BG κ * (xiC1 d * eps) + (1 + 3 * (xiC1 d * eps)) + Bh) *
            Real.exp (-2 * κdec * treeLenCov Gp m₀ Y))) / r) := by
        refine mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hs hr.le) hMω
    _ = (Mω * (c1 d L * ((L : ℝ) ^ (m₀ + m₁)) ^ d *
          nuBd d L N k (cK2' d L N (famConst d L BG₂ κ) * δ₁)
            (K4 d L N BG κ * (xiC1 d * eps) + (1 + 3 * (xiC1 d * eps)) + Bh) / r)) *
          ((1 + treeLenCov Gp m₀ Y) * Real.exp (-2 * κdec * treeLenCov Gp m₀ Y)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left key hCn

/-- **The `ν`-part in the variable `ψ̂` with the volume-uniform bound**
`C e^{-(2 κ_dec - 1) d^cov_{k+1}(Y)}` (the hat version of `nupart_locInt_bound`).

Sharp form: the hat variable is compared only at the unit points of the sites of `Y`, the raw
datum only on `Y` itself. -/
theorem nupart_locInt_bound_hat_dm_dir (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hk : 1 ≤ k) (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    {Bh : ℝ} (hBh0 : 0 ≤ Bh)
    (hBh : ∀ D : BgData Gp N, XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D →
      ∀ x i, ‖D.h x i‖ ≤ Bh)
    (hcov : ∀ z, CovSetup Gp m₀ (j z) (X z) (𝒦X z))
    (hX₁ : ∀ z, (↑(X₁z z) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp m₀ (j z) (𝒦X z))
    (hconn : HatConn Gp) (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
    (hopt : ∀ z, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X z) ∧ MeetsOne m₀ (j z) (𝒦X z) W₀ ∧
        bondCost (scaleW L m₀ m₁ (j z)) E₀ = treeLenCovOne m₀ (j z) (X z))
    (hΔ : ∀ z, treeLenCovOne m₀ (j z) (X z) = 0)
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hZ : ∀ z, (↑(blockSites d L N₁ m₁ (k + 1) k z) : Set (CTorus d L N₁ m₁ (k + 1))) ⊆
      ↑(X₁z z))
    {ω : ℂ → ℂ} (hωc : Continuous ω) {R₁ : ℝ} (hR₁ : 1 < R₁)
    (hω : AnalyticOnNhd ℂ ω (ball (0 : ℂ) R₁)) {Mω : ℝ} (hMω : 0 ≤ Mω)
    (hωb : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → ‖ω (t : ℂ)‖ ≤ Mω) {r Rσ : ℝ} (hr : 0 < r) :
    ∃ T : Set (CTorus d L N₁ m₁ (k + 1)) → (unitPts Gp × Fin N → ℂ) →
        (unitPts Gp × Fin N → ℂ) → ℂ → RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ,
      LocIntDm (IsDj m₀ (k + 1)) (id : (unitPts Gp × Fin N → ℂ) → _)
        (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps) (HatRaysO Gp cψ R₁ Rσ r) Rσ
        (Finset.univ.biUnion fun z => polyDom Gp (X₁z z) m₀ (j z) (𝒦X z)) T
        (fun x₀ w σ Θ => dirTermSrc (hatFun Gp a₁ ν eps hG' cc (onXi Gp a₁ ν eps
          (fun D ψ' => nuTotal Gp Hm a₁ ν BG₂ κ D ψ'))) ω x₀ w σ Θ)
        (fun Y => Mω * (c1 d L * ((L : ℝ) ^ (m₀ + m₁)) ^ d *
          nuBd d L N k (cK2' d L N (famConst d L BG₂ κ) * δ₁)
            (K4 d L N BG κ * (xiC1 d * eps) + (1 + 3 * (xiC1 d * eps)) + Bh) / r) *
          Real.exp (-(2 * κdec - 1) * treeLenCovOne m₀ (k + 1) Y))
        (fun Y Θ Θ' => agreeOn Y Θ Θ') (AgHatFDir hG') := by
  classical
  exact (nupart_locInt_bound_hat_dm_dir_ray hC hk hG hG' cc (cψ := cψ) hcψ hMX (δc := δc) hdm hα hsm hδ₁ (Bh := Bh) hBh0 hBh hcov hX₁ hconn hrow hopt hΔ (κdec := κdec) (κ₀ := κ₀) hκ₀ hκdec hκ h1 hlog hZ (ω := ω) hωc (R₁ := R₁) hR₁ hω (Mω := Mω) hMω hωb (r := r) (Rσ := Rσ) hr).imp fun _ h => h.1

end SharpNuPart

end Balaban.Localization
