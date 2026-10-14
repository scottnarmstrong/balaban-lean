/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.SharpAssemblyEta
public import Balaban.Fluctuation.InteractionVBlockScaled
public import Balaban.Fluctuation.InteractionEnergyScaled
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The sharp assembly of the physical expansion with the scale-uniform potential majorant

Package 3 ("scaled propagation") of `notes/phase1/PHYSCUBIC.md` §4, targets T1 and T2.

The landed chain from the block expansion to the direct terms of the physical expansion carries, in
the potential (`V`) summand, the majorant `energyBd` of the block energy, which grows like `L^{nd}`.
`InteractionVBlockScaled` proved the block bound with the scale-correct majorant `energyBdScaled`
(`L^{n(d-2)}` times a constant, `energyBdScaled_eq`).  This file repeats, with `energyBdScaled`, the
part of the landed chain that carries the potential majorant, and nothing else:

* `vblock_expansion_hat_dir_scaled`, `vblock_locInt_hat_dir_scaled`, `vpart_locInt_hat_dir_dm_scaled`:
  the hat potential summand in its sharp form (`SharpVF`), with `blockEnergyFun_bound_scaled`;
* `hat_vpart_bound_dm_dir_scaled` (`SharpAssembly`): the resummed potential bound;
* `interaction_expansion_hat_bound_dm_dir_eta_scaled`, `interaction_expansion_hat_dm_core_dir_eta_scaled`
  (`SharpAssemblyEta`): the assembly on the slice of sources of `l1`-size at most `eta`;
* `physical_directTerms_eta_scaled`: a `DirectTerms` instance on the slice, whose bound is the
  amplitude `prop33EpsEtaScaled` (the landed `prop33EpsEta` with the potential term
  `3 c_1 M^d |E| / r^3` evaluated at `energyBdScaled`) times `|c_beta|`, plus the `nu`-term.

The old-term, source, observable and `nu` summands, and the combinators `LocIntDm.assemble`,
`addLift`, `wsum`, `comap`, are the landed ones: they do not depend on the majorant of the
potential summand.  The new hypotheses are `IsLevel Hm k`, `IsLevel Gp (k+1)`, which the landed
theorems already carry as `hG`, `hG'`.

What is proved: the direct terms of the physical step exponent at the physical point, with the
potential amplitude in physical units.  What is not proved: the activity bound (`StepActivityDirectScaled`)
and anything for general scale or class.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Analysis
  Balaban.Fluctuation Finset Matrix Set Metric


/-- **The amplitude of `(3.2)` with the potential term in physical units.**  The landed
`prop33EpsEta` with its first term `3 c_1 M^d |E| / r^3`, `E` the block-energy majorant `energyBd`,
replaced by `3 c_1 M^d |E_sc| / r^3` with `E_sc = energyBdScaled`; the other two terms
(old terms `rho_E c_1 (L^{k+1})^d M^d / r` and sources `eta (cK2' delta_1 + rho_M) / r`) are
unchanged.  `energyBdScaled` does not depend on the mass `nu`, so `nu` is not an argument. -/
noncomputable def prop33EpsEtaScaled (d L N m₁ n m₀ : ℕ) (a₁ BG BG₂ κ δ₁ r ρE ρM η : ℝ) : ℝ :=
  3 * c1 d L * ((L : ℝ) ^ (m₀ + m₁)) ^ d * ‖energyBdScaled d L N (compWeight L a₁) n
      (cK2' d L N (famConst d L BG₂ κ) * δ₁) δ₁ (rho4 d L N BG κ)‖ / r ^ 3 +
    ρE * c1 d L * ((L : ℝ) ^ (n + 1)) ^ d * ((L : ℝ) ^ (m₀ + m₁)) ^ d / r +
    η * (cK2' d L N (famConst d L BG₂ κ) * δ₁ + ρM) / r

section Block

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ} {X₁f : Finset (CTorus d L N₁ m₁ (k + 1))} {j : ℕ}
variable {m₀ : ℕ} {X 𝒦X : Set (CTorus d L N₁ m₁ (k + 1))}

/-- **The block energy expands over the domains `Y ⊃ X₁`, scale-uniform majorant, exact locality**
(`vblock_expansion_hat_dir_scaled` with the locality clause for raw data agreeing on `Y` itself and
hat variables agreeing at the unit points of `Y`).  The thick corollary
`vblock_expansion_hat_dir_scaled` uses the same `Ev` selected here. -/
theorem vblock_expansion_hat_rawY_scaled (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hk : 1 ≤ k) (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
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
    (hZ : readSites Hm k z ⊆ ↑X₁f)
    (hmar : BlockMargin Gp X₁f (↑(blockSites d L N₁ m₁ (k + 1) k z) : Set (CTorus d L N₁ m₁ (k + 1)))) :
    ∃ Ev : Set (CTorus d L N₁ m₁ (k + 1)) →
        RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gp × Fin N → ℂ) → ℂ,
      (∀ D : BgData Gp N, XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D →
        ∀ ψh : unitPts Gp × Fin N → ℂ, (∀ p, ‖ψh p‖ ≤ cψ) →
        hatFun Gp a₁ ν eps hG' cc (blockEnergyOne Gp Hm a₁ ν BG₂ κ eps k z) (rawOf D, ψh) =
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
        ‖Ev Y u‖ ≤ energyBdScaled d L N (compWeight L a₁) k
          (cK2' d L N (famConst d L BG₂ κ) * δ₁) δ₁ (rho4 d L N BG κ) *
          Real.exp (-2 * κdec * treeLenCov Gp m₀ Y)) ∧
      (∀ Y, AnalyticOnNhd ℂ (Ev Y) (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ})) ∧
      ∃ (F₁ : DecParams Gp × RawData d L (N₁ * L ^ m₁) (k + 1) N →
          (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ))
        (Sol : Dec2.DecParams (coverOf Gp) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)),
        (∀ (s : DecParams Gp) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
          InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
            (α : Gp.Ω 1 → ℂ), IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
            F₁ (s, rawOf D) = (φ, α)) ∧
        (∀ p : Dec2.DecParams (coverOf Gp) × Edat Hm N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
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
                (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol p).2)) ∧
        Ev = evTerm (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) Gp m₀
          (X1 Gp m₀ j 𝒦X)
          (fun u s => blockEnergyFun Gp Hm (compWeight L a₁) ν k z (F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s, u.1))
            (Sol (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s,
              flEdat Gp Hm (F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s, u.1))
                u.1.1 (hatPsiF Gp a₁ ν hG' cc F₁
                  (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s) u.1 u.2))).1
            (u.1, hatPsiF Gp a₁ ν hG' cc F₁
              (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s) u.1 u.2)) := by
  have hd0 : 0 < d := by have := hC.HBp.hd; omega
  have hB0 : 0 ≤ famConst d L BG₂ κ := by
    have := famConst_ge_one (L := L) hC.hS2.fam.2.1 κ hd0; linarith
  have hV : 0 ≤ cK2' d L N (famConst d L BG₂ κ) * δ₁ :=
    mul_nonneg (cK2'_nonneg hB0) hC.δ₁_pos.le
  have hρ : 0 ≤ rho4 d L N BG κ := by
    have hBG := hC.hS.fam.2.1
    have hB1 : 0 ≤ famConst d L BG κ := by
      have := famConst_ge_one (L := L) hBG κ hd0; linarith
    unfold rho4
    exact (c6'_pos hB1 (by have := gamma1_pos hd0; positivity)).le
  have ha : 0 ≤ compWeight L a₁ k :=
    (hC.HBp.weights k hk (by omega)).1.trans' (by norm_num)
  have hEb := energyBdScaled_nonneg (d := d) (L := L) (N := N) ha hV hC.δ₁_pos.le hρ
  obtain ⟨Ev, h1', h2', h3', h4', h5'⟩ := i5_functional_hat_rawY_of_fan hC hk hG hG' cc hcψ hMX hdm hα hsm hδ₁ hcov hX₁
    hopt hκ₀ hκdec hκ h1 hlog hEb
    (Φ := blockEnergyFun Gp Hm (compWeight L a₁) ν k z)
    ((blockEnergyFun_analytic _ ν k z).mono (Set.subset_univ _))
    (fun t ht => by
      rw [hΔ]; simpa using blockEnergyFun_bound_scaled hC hG hG' hk le_rfl z ht)
    (fun {F₁} hF₁ {Sol} hSol => vblock_fan_local_rawY hC hk hG hG' cc hcψ hMX hdm hα hsm hδ₁ hcov hX₁
      hconn hrow hF₁ hSol z hZ hmar)
  refine ⟨Ev, fun D hD ψh hψh => ?_, h2', fun Y u hu => ?_, h4', h5'⟩
  · rw [hatFun_rawOf hG' cc _ hD, blockEnergyOne_rawOf hD k z]
    exact h1' D hD ψh hψh
  · have := h3' Y u hu
    rw [hΔ] at this
    simpa using this


/-- **The block energy expands over the domains `Y ⊃ X₁`, with terms local in `ψ̂`, sharp form**
(`vblock_expansion_hat` with the locality clause for `AgHatDir`: the hat variable is read only at
the unit points of the sites of `Y`). -/
theorem vblock_expansion_hat_dir_scaled (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hk : 1 ≤ k) (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
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
    (hZ : readSites Hm k z ⊆ ↑X₁f)
    (hmar : BlockMargin Gp X₁f (↑(blockSites d L N₁ m₁ (k + 1) k z) : Set (CTorus d L N₁ m₁ (k + 1)))) :
    ∃ Ev : Set (CTorus d L N₁ m₁ (k + 1)) →
        RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gp × Fin N → ℂ) → ℂ,
      (∀ D : BgData Gp N, XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D →
        ∀ ψh : unitPts Gp × Fin N → ℂ, (∀ p, ‖ψh p‖ ≤ cψ) →
        hatFun Gp a₁ ν eps hG' cc (blockEnergyOne Gp Hm a₁ ν BG₂ κ eps k z) (rawOf D, ψh) =
        ∑ Y ∈ polymerDomains (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1)
          Gp m₀ (X1 Gp m₀ j 𝒦X), Ev Y (rawOf D, ψh)) ∧
      (∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        ∀ u' ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        AgHatDir hG' Y u u' → Ev Y u = Ev Y u') ∧
      (∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        ‖Ev Y u‖ ≤ energyBdScaled d L N (compWeight L a₁) k
          (cK2' d L N (famConst d L BG₂ κ) * δ₁) δ₁ (rho4 d L N BG κ) *
          Real.exp (-2 * κdec * treeLenCov Gp m₀ Y)) ∧
      (∀ Y, AnalyticOnNhd ℂ (Ev Y) (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ})) := by
  obtain ⟨Ev, hs, hd, hb, ha, -⟩ := vblock_expansion_hat_rawY_scaled hC hk hG hG' cc hcψ hMX hdm hα hsm hδ₁
    hcov hX₁ hconn hrow hopt hΔ hκ₀ hκdec hκ h1 hlog z hZ hmar
  exact ⟨Ev, hs, fun Y u hu u' hu' h => hd Y u hu u' hu' (agreeOn_mono (fun x hx => Or.inl hx) h.1) h.2, hb, ha⟩

end Block

section LocHatDir
variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ} {X₁f : Finset (CTorus d L N₁ m₁ (k + 1))} {j : ℕ}
variable {m₀ : ℕ} {X 𝒦X : Set (CTorus d L N₁ m₁ (k + 1))}
/-- **The potential part of the localized interaction, one block, in the variable `ψ̂`, sharp form**: as `vblock_locInt_hat`, with the directional
terms depending on `(x₀, w)` only through their values at the unit points of the sites of `Y`
itself (`AgHatFDir`).
The last conjunct exhibits the terms, as in `vblock_expansion_hat_rawY_scaled`. -/
theorem vblock_locInt_hat_dir_scaled (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hk : 1 ≤ k) (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
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
    (hZ : readSites Hm k z ⊆ ↑X₁f)
    (hmar : BlockMargin Gp X₁f (↑(blockSites d L N₁ m₁ (k + 1) k z) : Set (CTorus d L N₁ m₁ (k + 1))))
    {ω : ℂ → ℂ} (hωc : Continuous ω) {R₁ : ℝ} (hR₁ : 1 < R₁)
    (hω : AnalyticOnNhd ℂ ω (ball (0 : ℂ) R₁)) {Mω : ℝ} (hMω : 0 ≤ Mω)
    (hωb : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → ‖ω (t : ℂ)‖ ≤ Mω) {r Rσ : ℝ} (hr : 0 < r) :
    ∃ Ev : Set (CTorus d L N₁ m₁ (k + 1)) →
        RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gp × Fin N → ℂ) → ℂ,
      (∀ D : BgData Gp N, XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D →
        ∀ ψh : unitPts Gp × Fin N → ℂ, (∀ p, ‖ψh p‖ ≤ cψ) →
        hatFun Gp a₁ ν eps hG' cc (blockEnergyOne Gp Hm a₁ ν BG₂ κ eps k z) (rawOf D, ψh) =
        ∑ Y ∈ polymerDomains (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1)
          Gp m₀ (X1 Gp m₀ j 𝒦X), Ev Y (rawOf D, ψh)) ∧
      (∀ Y, AnalyticOnNhd ℂ (Ev Y) (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ})) ∧
      LocInt (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps) (HatRays Gp cψ R₁ Rσ r) Rσ
        (polymerDomains (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) Gp m₀
          (X1 Gp m₀ j 𝒦X))
        (fun Y x₀ w σ Θ => rayTerm (dl3 (Ev Y) w) ω x₀ σ Θ)
        (fun x₀ w σ Θ => raySrc3 (hatFun Gp a₁ ν eps hG' cc
          (blockEnergyOne Gp Hm a₁ ν BG₂ κ eps k z)) ω x₀ w σ Θ)
        (fun Y => Mω * (6 * ‖energyBdScaled d L N (compWeight L a₁) k
          (cK2' d L N (famConst d L BG₂ κ) * δ₁) δ₁ (rho4 d L N BG κ) *
          Real.exp (-2 * κdec * treeLenCov Gp m₀ Y)‖ / r ^ 3))
        (fun Y Θ Θ' => agreeOn Y Θ Θ') (AgHatFDir hG') ∧
      ∃ (F₁ : DecParams Gp × RawData d L (N₁ * L ^ m₁) (k + 1) N →
          (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ))
        (Sol : Dec2.DecParams (coverOf Gp) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)),
        (∀ (s : DecParams Gp) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
          InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
            (α : Gp.Ω 1 → ℂ), IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
            F₁ (s, rawOf D) = (φ, α)) ∧
        (∀ p : Dec2.DecParams (coverOf Gp) × Edat Hm N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
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
                (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol p).2)) ∧
        Ev = evTerm (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) Gp m₀
          (X1 Gp m₀ j 𝒦X)
          (fun u s => blockEnergyFun Gp Hm (compWeight L a₁) ν k z (F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s, u.1))
            (Sol (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s,
              flEdat Gp Hm (F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s, u.1))
                u.1.1 (hatPsiF Gp a₁ ν hG' cc F₁
                  (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s) u.1 u.2))).1
            (u.1, hatPsiF Gp a₁ ν hG' cc F₁
              (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s) u.1 u.2)) := by
  classical
  obtain ⟨Ev, hsum, hloc, hbd, hanY, hEv⟩ := vblock_expansion_hat_rawY_scaled hC hk hG hG' cc hcψ hMX
    hdm hα hsm hδ₁ hcov hX₁ hconn hrow hopt hΔ hκ₀ hκdec hκ h1 hlog z hZ hmar
  refine ⟨Ev, hsum, hanY, ?_, hEv⟩
  refine locInt_dir3 (S := XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps)
    (B := {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ})
    (f := hatFun Gp a₁ ν eps hG' cc (blockEnergyOne Gp Hm a₁ ν BG₂ κ eps k z)) _ hR₁ hω hωc hMω
    hωb hr hanY (fun Y u hu => hbd Y u hu) ?_ ?_ ?_
  · intro Y a a' b b' p q ha hb y hy i
    simp [ha y hy i, hb y hy i]
  · intro Y Θ hΘ Θ' hΘ' z hz z' hz' h1' h2'
    exact hloc Y (Θ, z) ⟨hΘ, hz⟩ (Θ', z') ⟨hΘ', hz'⟩ h1' h2'
  · intro Θ hΘ ψh hψh
    obtain ⟨D, hD, rfl⟩ := hΘ
    exact hsum D hD ψh hψh
end LocHatDir

section VPartHatDir
variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ}
/-- **Ray-differentiable form of `vpart_locInt_hat_dir_dm_scaled`.**  The statement of `vpart_locInt_hat_dir_dm_scaled` together with the
differentiability of the terms along the complex hat ray `z ↦ z • ψ̂` on `‖z‖ < 3/2`.
The last conjunct gives the terms explicitly: `T z Y x₀ w σ Θ = rayTerm (dl3 (Ev_z Y) w) ω x₀ σ Θ`
with `Ev_z = evTerm … FF_z`, `FF_z` the block energy functional of the block `z` at a pair
`(F₁ z, Sol z)` with their defining properties. -/
theorem vpart_locInt_hat_dir_dm_scaled_ray (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hk : 1 ≤ k) (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    (ha₁ : 0 < a₁)
    (H : BgHyp d L (k + 1) ϱm (compWeight L a₁) ν) (hc7 : c7 d L N BG κ ≤ thm73C3 d L N)
    {R : ℝ} (hR : 2 ≤ R) (hRs : R * δ₁ ≤ deltaStar d L N)
    (hsmall : cK2 d L N * (R * δ₁) < bgC0 d L N / 2)
    (hnum : cK2 d L N * δ₁ ≤ c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hnum' : cK2' d L N (famConst d L BG₂ κ) * δ₁ ≤
      c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hreal : ∀ D' : BgData Gp N, XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D' →
      ∀ ψ' ∈ FlBall Hm δ₁, IsLayerConstant Hm ψ' → ∃ D : BgData Hm N,
      (∀ x i, D.h x i = D'.h x i) ∧
      compTangent hG hG' le_rfl (compWeight L a₁)
        (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D') D' D = ψ' ∧
      ∀ t : ℂ, ‖t‖ < R → InUnionDomainC Hm (bgC0 d L N) (bgC1 d L N) ν
        ((composeData (hG.precedes hG' le_rfl) (compWeight L a₁)
          (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D') D').lineAt
          (tangentData D (composeData (hG.precedes hG' le_rfl) (compWeight L a₁)
            (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D') D')) t))
    {m₀ j : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → ℕ}
    {X 𝒦X : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Set (CTorus d L N₁ m₁ (k + 1))}
    {X₁f : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Finset (CTorus d L N₁ m₁ (k + 1))}
    (hcov : ∀ z, CovSetup Gp (m₀ z) (j z) (X z) (𝒦X z))
    (hX₁ : ∀ z, (↑(X₁f z) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp (m₀ z) (j z) (𝒦X z))
    (hconn : HatConn Gp) (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
    (hopt : ∀ z, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X z) ∧ MeetsOne (m₀ z) (j z) (𝒦X z) W₀ ∧
        bondCost (scaleW L (m₀ z) m₁ (j z)) E₀ = treeLenCovOne (m₀ z) (j z) (X z))
    (hΔ : ∀ z, treeLenCovOne (m₀ z) (j z) (X z) = 0)
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : ∀ z, Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀ z) ^ d : ℕ) : ℝ)) ≤
      (κ / 2 - 1) / 2)
    (hZ : ∀ z, readSites Hm k z ⊆ ↑(X₁f z))
    (hmar : ∀ z, BlockMargin Gp (X₁f z)
      (↑(blockSites d L N₁ m₁ (k + 1) k z) : Set (CTorus d L N₁ m₁ (k + 1))))
    {ω : ℂ → ℂ} (hωc : Continuous ω) {R₁ : ℝ} (hR₁ : 1 < R₁)
    (hω : AnalyticOnNhd ℂ ω (ball (0 : ℂ) R₁)) {Mω : ℝ} (hMω : 0 ≤ Mω)
    (hωb : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → ‖ω (t : ℂ)‖ ≤ Mω) {r Rσ : ℝ} (hr : 0 < r) :
    ∃ (T : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Set (CTorus d L N₁ m₁ (k + 1)) →
        (unitPts Gp × Fin N → ℂ) → (unitPts Gp × Fin N → ℂ) → ℂ →
        RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ),
      LocIntDm (fun Y => ∃ z, IsDj (m₀ z) (k + 1) Y) (id : (unitPts Gp × Fin N → ℂ) → _)
        (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps) (HatRays Gp cψ R₁ Rσ r) Rσ
        (Finset.univ.biUnion fun z => polyDom Gp (X₁f z) (m₀ z) (j z) (𝒦X z))
        (fun Y x₀ w σ Θ => ∑ z, if Y ∈ polyDom Gp (X₁f z) (m₀ z) (j z) (𝒦X z) then
          T z Y x₀ w σ Θ else 0)
        (fun x₀ w σ Θ => raySrc3 (hatFun Gp a₁ ν eps hG' cc
          (interactionOne hG hG' le_rfl a₁ ν eps)) ω x₀ w σ Θ)
        (fun Y => ∑ z, if Y ∈ polyDom Gp (X₁f z) (m₀ z) (j z) (𝒦X z) then
          Mω * (6 * ‖energyBdScaled d L N (compWeight L a₁) k
          (cK2' d L N (famConst d L BG₂ κ) * δ₁) δ₁ (rho4 d L N BG κ) *
          Real.exp (-2 * κdec * treeLenCov Gp (m₀ z) Y)‖ / r ^ 3) else 0)
        (fun Y Θ Θ' => agreeOn Y Θ Θ') (AgHatFDir hG')
      ∧ (∀ (Y : Set (CTorus d L N₁ m₁ (k + 1))) (Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N),
        Θ ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps → ∀ ψ : unitPts Gp × Fin N → ℂ,
        (∀ p, (R₁ + r) * (3 / 2) * ‖ψ p‖ ≤ cψ) →
        DifferentiableOn ℂ (fun ζ : ℂ =>
          ∑ z, if Y ∈ polyDom Gp (X₁f z) (m₀ z) (j z) (𝒦X z) then
            T z Y (ζ • ψ) (ζ • ψ) 1 Θ else 0) (ball (0 : ℂ) (3 / 2))) ∧
      ∃ (F₁ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
            DecParams Gp × RawData d L (N₁ * L ^ m₁) (k + 1) N → (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ))
          (Sol : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
            Dec2.DecParams (coverOf Gp) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)),
        (∀ z (s : DecParams Gp) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
          InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
            (α : Gp.Ω 1 → ℂ), IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
            F₁ z (s, rawOf D) = (φ, α)) ∧
        (∀ z (p : Dec2.DecParams (coverOf Gp) × Edat Hm N), (∀ P, ‖p.1 P‖ < Real.exp κ) →
          StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
            (Sol z p).1 = dphi Hm (Dec2.decG (coverOf Gp) Hm (compWeight L a₁) ν p.1) p.2.2.1 p.2.1
              (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol z p).2 ∧
            Dec2.DecFixed (coverOf Gp) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
              (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol z p).2 ∧
            Small Hm (Sol z p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
            Small Hm (Sol z p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
            SupBounds Hm (Sol z p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
            (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
              Dec2.DecFixed (coverOf Gp) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
                (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol z p).2)) ∧
        T = fun z Y x₀ w σ Θ => rayTerm (dl3 (evTerm
          (fun i : ParIdx Gp (↑(X₁f z) : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) Gp (m₀ z)
          (X1 Gp (m₀ z) (j z) (𝒦X z))
          (fun u s => blockEnergyFun Gp Hm (compWeight L a₁) ν k z
            (F₁ z (extParams Gp (↑(X₁f z) : Set (CTorus d L N₁ m₁ (k + 1))) s, u.1))
            (Sol z (extParams Gp (↑(X₁f z) : Set (CTorus d L N₁ m₁ (k + 1))) s,
              flEdat Gp Hm (F₁ z (extParams Gp (↑(X₁f z) : Set (CTorus d L N₁ m₁ (k + 1))) s, u.1))
                u.1.1 (hatPsiF Gp a₁ ν hG' cc (F₁ z)
                  (extParams Gp (↑(X₁f z) : Set (CTorus d L N₁ m₁ (k + 1))) s) u.1 u.2))).1
            (u.1, hatPsiF Gp a₁ ν hG' cc (F₁ z)
              (extParams Gp (↑(X₁f z) : Set (CTorus d L N₁ m₁ (k + 1))) s) u.1 u.2)) Y) w) ω x₀ σ Θ := by
  classical
  have hex : ∀ z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))), ∃ (Ev : Set (CTorus d L N₁ m₁ (k + 1)) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gp × Fin N → ℂ) → ℂ),
      (∀ D : BgData Gp N, XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D →
        ∀ ψh : unitPts Gp × Fin N → ℂ, (∀ p, ‖ψh p‖ ≤ cψ) →
        hatFun Gp a₁ ν eps hG' cc (blockEnergyOne Gp Hm a₁ ν BG₂ κ eps k z) (rawOf D, ψh) =
        ∑ Y ∈ polymerDomains (fun i : ParIdx Gp (↑(X₁f z) : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1)
          Gp (m₀ z) (X1 Gp (m₀ z) (j z) (𝒦X z)), Ev Y (rawOf D, ψh)) ∧
      (∀ Y, AnalyticOnNhd ℂ (Ev Y) (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ})) ∧
      LocInt (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps) (HatRays Gp cψ R₁ Rσ r) Rσ
        (polymerDomains (fun i : ParIdx Gp (↑(X₁f z) : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1)
          Gp (m₀ z) (X1 Gp (m₀ z) (j z) (𝒦X z)))
        (fun Y x₀ w σ Θ => rayTerm (dl3 (Ev Y) w) ω x₀ σ Θ)
        (fun x₀ w σ Θ => raySrc3 (hatFun Gp a₁ ν eps hG' cc
          (blockEnergyOne Gp Hm a₁ ν BG₂ κ eps k z)) ω x₀ w σ Θ)
        (fun Y => Mω * (6 * ‖energyBdScaled d L N (compWeight L a₁) k
          (cK2' d L N (famConst d L BG₂ κ) * δ₁) δ₁ (rho4 d L N BG κ) *
          Real.exp (-2 * κdec * treeLenCov Gp (m₀ z) Y)‖ / r ^ 3))
        (fun Y Θ Θ' => agreeOn Y Θ Θ') (AgHatFDir hG') ∧
      ∃ (F₁ : DecParams Gp × RawData d L (N₁ * L ^ m₁) (k + 1) N →
          (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ))
        (Sol : Dec2.DecParams (coverOf Gp) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)),
        (∀ (s : DecParams Gp) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
          InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
            (α : Gp.Ω 1 → ℂ), IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
            F₁ (s, rawOf D) = (φ, α)) ∧
        (∀ p : Dec2.DecParams (coverOf Gp) × Edat Hm N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
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
                (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol p).2)) ∧
        Ev = evTerm (fun i : ParIdx Gp (↑(X₁f z) : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) Gp
          (m₀ z) (X1 Gp (m₀ z) (j z) (𝒦X z))
          (fun u s => blockEnergyFun Gp Hm (compWeight L a₁) ν k z
            (F₁ (extParams Gp (↑(X₁f z) : Set (CTorus d L N₁ m₁ (k + 1))) s, u.1))
            (Sol (extParams Gp (↑(X₁f z) : Set (CTorus d L N₁ m₁ (k + 1))) s,
              flEdat Gp Hm (F₁ (extParams Gp (↑(X₁f z) : Set (CTorus d L N₁ m₁ (k + 1))) s, u.1))
                u.1.1 (hatPsiF Gp a₁ ν hG' cc F₁
                  (extParams Gp (↑(X₁f z) : Set (CTorus d L N₁ m₁ (k + 1))) s) u.1 u.2))).1
            (u.1, hatPsiF Gp a₁ ν hG' cc F₁
              (extParams Gp (↑(X₁f z) : Set (CTorus d L N₁ m₁ (k + 1))) s) u.1 u.2)) := fun z =>
    vblock_locInt_hat_dir_scaled hC hk hG hG' cc hcψ hMX hdm hα hsm hδ₁ (hcov z) (hX₁ z) hconn hrow (hopt z)
      (hΔ z) hκ₀ hκdec hκ h1 (hlog z) z (hZ z) (hmar z) hωc hR₁ hω hMω hωb hr
  choose Ev hEvsum hEvan hEv hEvF using hex
  choose F₁ Sol hF₁ hSol hEvEq using hEvF
  have hrayV : ∀ (Y : Set (CTorus d L N₁ m₁ (k + 1))) (Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N),
      Θ ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps → ∀ ψ : unitPts Gp × Fin N → ℂ,
      (∀ p, (R₁ + r) * (3 / 2) * ‖ψ p‖ ≤ cψ) →
      DifferentiableOn ℂ (fun ζ : ℂ =>
        ∑ z, if Y ∈ polyDom Gp (X₁f z) (m₀ z) (j z) (𝒦X z) then
          rayTerm (dl3 (Ev z Y) (ζ • ψ)) ω (ζ • ψ) 1 Θ else 0) (ball (0 : ℂ) (3 / 2)) := by
    intro Y Θ hΘ ψ hψ
    apply DifferentiableOn.fun_sum
    intro z _
    by_cases hY : Y ∈ polyDom Gp (X₁f z) (m₀ z) (j z) (𝒦X z)
    · simp only [hY, ite_true]
      exact differentiableOn_rayTerm_dl3_ray_ball hR₁ hr hω (hEvan z Y) hΘ ψ hψ
    · simp only [hY, ite_false]; exact differentiableOn_const _
  refine ⟨fun z Y x₀ w σ Θ => rayTerm (dl3 (Ev z Y) w) ω x₀ σ Θ, ?_, hrayV, F₁, Sol, hF₁, hSol,
    funext fun z => by rw [hEvEq z]⟩
  have hd : 3 ≤ d := hC.HBp.hd
  refine (LocIntDm.finsum Finset.univ (fun z _ => LocIntDm.mk
    (P := fun Y => ∃ z', IsDj (m₀ z') (k + 1) Y) (e := (id : (unitPts Gp × Fin N → ℂ) → _))
    (hEv z) (fun Y hY => ⟨z, isDj_of_polyDom hG' (hcov z) hd (hopt z) hY⟩)
    (diagCont_rayTerm _ hR₁ hωc hr (hEvan z)))).congr_val ?_
  rintro ⟨x₀, w⟩ hxw σ hσ Θ ⟨D', hD, rfl⟩
  have hreal1 : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → ‖(t : ℂ)‖ < R₁ := fun t ht => by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]; linarith [ht.2]
  have hdisc : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → ∀ τ : ℂ, ‖τ‖ ≤ r →
      (σ * (t : ℂ)) • x₀ + τ • w ∈ {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ} :=
    fun t ht τ hτ => hxw σ hσ t (hreal1 t ht) τ hτ
  have hsum' : ∀ z, ∀ Θ ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps,
      ∀ ψh ∈ {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
      hatFun Gp a₁ ν eps hG' cc (blockEnergyOne Gp Hm a₁ ν BG₂ κ eps k z) (Θ, ψh) =
        ∑ Y ∈ polymerDomains (fun i : ParIdx Gp (↑(X₁f z) : Set (CTorus d L N₁ m₁ (k + 1))) =>
          i.1.1) Gp (m₀ z) (X1 Gp (m₀ z) (j z) (𝒦X z)), Ev z Y (Θ, ψh) := by
    intro z Θ hΘ ψh hψh
    obtain ⟨D'', hD'', rfl⟩ := hΘ
    exact hEvsum z D'' hD'' ψh hψh
  have hint : ∀ z, IntervalIntegrable (fun t : ℝ => ω (t : ℂ) * dirS3
      (hatFun Gp a₁ ν eps hG' cc (blockEnergyOne Gp Hm a₁ ν BG₂ κ eps k z)) w (rawOf D')
      ((σ * (t : ℂ)) • x₀)) MeasureTheory.volume 0 1 := fun z =>
    raySrc3_intervalIntegrable (S := XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps)
      (B := {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ}) _ (Evs := Ev z)
      (fun Y => hEvan z Y) (hsum' z) hωc ⟨D', hD, rfl⟩ hr hdisc
  have hψmem : ∀ ψh : unitPts Gp × Fin N → ℂ, (∀ p, ‖ψh p‖ ≤ cψ) →
      hatLift Gp a₁ ν hG' cc D' ψh ∈ FlBall Hm δ₁ := fun ψh hψh =>
    (hatLift_mem_flBallLC hC hk hG hG' cc hcψ hMX hdm hα hsm hδ₁ hD hψh).1
  unfold raySrc3
  rw [← Finset.mul_sum, ← intervalIntegral.integral_finsetSum (fun z _ => hint z)]
  congr 1
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [Set.uIcc_of_le zero_le_one] at ht
  simp only
  rw [← Finset.mul_sum]
  congr 1
  rw [dirS3_hatFun hG' cc _ hD]
  have hs : ∀ z, dirS3 (hatFun Gp a₁ ν eps hG' cc (blockEnergyOne Gp Hm a₁ ν BG₂ κ eps k z)) w
      (rawOf D') ((σ * (t : ℂ)) • x₀) =
      dirS3 (blockEnergyOne Gp Hm a₁ ν BG₂ κ eps k z) (hatLift Gp a₁ ν hG' cc D' w) (rawOf D')
        (hatLift Gp a₁ ν hG' cc D' ((σ * (t : ℂ)) • x₀)) := fun z =>
    dirS3_hatFun hG' cc _ hD _ _
  simp only [hs]
  refine dirS3_interactionOne hC hG hG' le_rfl ha₁ H hc7 hR hRs hsmall hnum hnum' hD
    (hreal D' hD) (isLayerConstant_hatLift hG hG' cc D' _) (isLayerConstant_hatLift hG hG' cc D' _)
    hr (fun τ hτ => ?_) ?_
  · rw [← hatLift_add_smul]
    exact hψmem _ (hdisc t ht τ hτ.le)
  · intro z
    have hcd := contDiffAt_line_of_sum (S := XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps)
      (B := {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ}) _ (Evs := Ev z)
      (fun Y => hEvan z Y) (hsum' z) ⟨D', hD, rfl⟩ (z := (σ * (t : ℂ)) • x₀) (w := w) hr
      (fun τ hτ => hdisc t ht τ hτ)
    have e : (fun τ : ℂ => blockEnergyOne Gp Hm a₁ ν BG₂ κ eps k z
        (rawOf D', hatLift Gp a₁ ν hG' cc D' ((σ * (t : ℂ)) • x₀) +
          τ • hatLift Gp a₁ ν hG' cc D' w)) =
        fun τ : ℂ => hatFun Gp a₁ ν eps hG' cc (blockEnergyOne Gp Hm a₁ ν BG₂ κ eps k z)
          (rawOf D', (σ * (t : ℂ)) • x₀ + τ • w) :=
      funext fun τ => (hatFun_line hG' cc _ hD _ _ τ).symm
    rw [e]; exact hcd

/-- **The potential part of the localized interaction in the variable `ψ̂`** (Proposition 3.3,
the `V`-part, hat version of `vpart_locInt`): for the exact interaction potential `V^{(k)}` of
Lemma 2.3 (b), as a function of the raw data `Θ` and the hat variable `ψ̂`
(`ψ' = liftC (cc • C^{1/2}(1) ψ̂)`), `σ ∫₀¹ ω(t') ∂_w³ V(σ t' x₀) dt'` along the `ψ̂`-ray is a
localized expansion over the domains `Y ⊃ X₁`: the terms are analytic in `(Θ, σ)`, bounded by
`|σ| M_ω 6 E e^{-2 κ d̃^{cov}_{k+1}(Y)} / r³`, vanish at `σ = 0`, and depend on `Θ` through
its values on `Y` itself and on `(x₀, w)` through their values at the unit points of the sites of
`Y` itself (`AgHatFDir`, sharp form of `vpart_locInt_hat_dm`). -/
theorem vpart_locInt_hat_dir_dm_scaled (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hk : 1 ≤ k) (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    (ha₁ : 0 < a₁)
    (H : BgHyp d L (k + 1) ϱm (compWeight L a₁) ν) (hc7 : c7 d L N BG κ ≤ thm73C3 d L N)
    {R : ℝ} (hR : 2 ≤ R) (hRs : R * δ₁ ≤ deltaStar d L N)
    (hsmall : cK2 d L N * (R * δ₁) < bgC0 d L N / 2)
    (hnum : cK2 d L N * δ₁ ≤ c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hnum' : cK2' d L N (famConst d L BG₂ κ) * δ₁ ≤
      c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hreal : ∀ D' : BgData Gp N, XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D' →
      ∀ ψ' ∈ FlBall Hm δ₁, IsLayerConstant Hm ψ' → ∃ D : BgData Hm N,
      (∀ x i, D.h x i = D'.h x i) ∧
      compTangent hG hG' le_rfl (compWeight L a₁)
        (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D') D' D = ψ' ∧
      ∀ t : ℂ, ‖t‖ < R → InUnionDomainC Hm (bgC0 d L N) (bgC1 d L N) ν
        ((composeData (hG.precedes hG' le_rfl) (compWeight L a₁)
          (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D') D').lineAt
          (tangentData D (composeData (hG.precedes hG' le_rfl) (compWeight L a₁)
            (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D') D')) t))
    {m₀ j : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → ℕ}
    {X 𝒦X : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Set (CTorus d L N₁ m₁ (k + 1))}
    {X₁f : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Finset (CTorus d L N₁ m₁ (k + 1))}
    (hcov : ∀ z, CovSetup Gp (m₀ z) (j z) (X z) (𝒦X z))
    (hX₁ : ∀ z, (↑(X₁f z) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp (m₀ z) (j z) (𝒦X z))
    (hconn : HatConn Gp) (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
    (hopt : ∀ z, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X z) ∧ MeetsOne (m₀ z) (j z) (𝒦X z) W₀ ∧
        bondCost (scaleW L (m₀ z) m₁ (j z)) E₀ = treeLenCovOne (m₀ z) (j z) (X z))
    (hΔ : ∀ z, treeLenCovOne (m₀ z) (j z) (X z) = 0)
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : ∀ z, Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀ z) ^ d : ℕ) : ℝ)) ≤
      (κ / 2 - 1) / 2)
    (hZ : ∀ z, readSites Hm k z ⊆ ↑(X₁f z))
    (hmar : ∀ z, BlockMargin Gp (X₁f z)
      (↑(blockSites d L N₁ m₁ (k + 1) k z) : Set (CTorus d L N₁ m₁ (k + 1))))
    {ω : ℂ → ℂ} (hωc : Continuous ω) {R₁ : ℝ} (hR₁ : 1 < R₁)
    (hω : AnalyticOnNhd ℂ ω (ball (0 : ℂ) R₁)) {Mω : ℝ} (hMω : 0 ≤ Mω)
    (hωb : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → ‖ω (t : ℂ)‖ ≤ Mω) {r Rσ : ℝ} (hr : 0 < r) :
    ∃ (T : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Set (CTorus d L N₁ m₁ (k + 1)) →
        (unitPts Gp × Fin N → ℂ) → (unitPts Gp × Fin N → ℂ) → ℂ →
        RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ),
      LocIntDm (fun Y => ∃ z, IsDj (m₀ z) (k + 1) Y) (id : (unitPts Gp × Fin N → ℂ) → _)
        (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps) (HatRays Gp cψ R₁ Rσ r) Rσ
        (Finset.univ.biUnion fun z => polyDom Gp (X₁f z) (m₀ z) (j z) (𝒦X z))
        (fun Y x₀ w σ Θ => ∑ z, if Y ∈ polyDom Gp (X₁f z) (m₀ z) (j z) (𝒦X z) then
          T z Y x₀ w σ Θ else 0)
        (fun x₀ w σ Θ => raySrc3 (hatFun Gp a₁ ν eps hG' cc
          (interactionOne hG hG' le_rfl a₁ ν eps)) ω x₀ w σ Θ)
        (fun Y => ∑ z, if Y ∈ polyDom Gp (X₁f z) (m₀ z) (j z) (𝒦X z) then
          Mω * (6 * ‖energyBdScaled d L N (compWeight L a₁) k
          (cK2' d L N (famConst d L BG₂ κ) * δ₁) δ₁ (rho4 d L N BG κ) *
          Real.exp (-2 * κdec * treeLenCov Gp (m₀ z) Y)‖ / r ^ 3) else 0)
        (fun Y Θ Θ' => agreeOn Y Θ Θ') (AgHatFDir hG') := by
  classical
  exact (vpart_locInt_hat_dir_dm_scaled_ray hC hk hG hG' cc (cψ := cψ) hcψ hMX (δc := δc) hdm hα hsm hδ₁ ha₁ H hc7 (R := R) hR hRs hsmall hnum hnum' hreal (m₀ := m₀) (j := j) (X := X) (𝒦X := 𝒦X) (X₁f := X₁f) hcov hX₁ hconn hrow hopt hΔ (κdec := κdec) (κ₀ := κ₀) hκ₀ hκdec hκ h1 hlog hZ hmar (ω := ω) hωc (R₁ := R₁) hR₁ hω (Mω := Mω) hMω hωb (r := r) (Rσ := Rσ) hr).imp fun _ h => h.1

end VPartHatDir

section SharpAssemble
variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ eps : ℝ}
/-- **Ray-differentiable form of `hat_vpart_bound_dm_dir_scaled`.**  The statement of `hat_vpart_bound_dm_dir_scaled` together with the
differentiability of the terms along the complex hat ray `z ↦ z • ψ̂` on `‖z‖ < 3/2`.
The last conjunct gives the terms explicitly: `T Y = ∑_z [Y ∈ polyDom_z] rayTerm (dl3 (Ev_z Y) w) …`
with `Ev_z` as in `vpart_locInt_hat_dir_dm_scaled_ray`. -/
theorem hat_vpart_bound_dm_dir_scaled_ray {Kc Cx c₂ BG₂ δ₁ : ℝ}
    (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hconn : HatConn Gp) (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    {R₁ : ℝ} (hR₁ : 1 < R₁) {r Rσ : ℝ} (hr : 0 < r)
    (hk : 1 ≤ k) (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsmX : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    (ha₁ : 0 < a₁)
    (H : BgHyp d L (k + 1) ϱm (compWeight L a₁) ν) (hc7 : c7 d L N BG κ ≤ thm73C3 d L N)
    {R : ℝ} (hR : 2 ≤ R) (hRs : R * δ₁ ≤ deltaStar d L N)
    (hsmall : cK2 d L N * (R * δ₁) < bgC0 d L N / 2)
    (hnum : cK2 d L N * δ₁ ≤ c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hnum' : cK2' d L N (famConst d L BG₂ κ) * δ₁ ≤
      c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hreal : ∀ D' : BgData Gp N, XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D' →
      ∀ ψ' ∈ FlBall Hm δ₁, IsLayerConstant Hm ψ' → ∃ D : BgData Hm N,
      (∀ x i, D.h x i = D'.h x i) ∧
      compTangent hG hG' le_rfl (compWeight L a₁)
        (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D') D' D = ψ' ∧
      ∀ t : ℂ, ‖t‖ < R → InUnionDomainC Hm (bgC0 d L N) (bgC1 d L N) ν
        ((composeData (hG.precedes hG' le_rfl) (compWeight L a₁)
          (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D') D').lineAt
          (tangentData D (composeData (hG.precedes hG' le_rfl) (compWeight L a₁)
            (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D') D')) t))
    {m₀ : ℕ} {jV : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → ℕ}
    {XV 𝒦XV : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Set (CTorus d L N₁ m₁ (k + 1))}
    {X₁V : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Finset (CTorus d L N₁ m₁ (k + 1))}
    (hcovV : ∀ z, CovSetup Gp (m₀) (jV z) (XV z) (𝒦XV z))
    (hX₁V : ∀ z, (↑(X₁V z) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp (m₀) (jV z) (𝒦XV z))
    (hoptV : ∀ z, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XV z) ∧ MeetsOne (m₀) (jV z) (𝒦XV z) W₀ ∧
        bondCost (scaleW L (m₀) m₁ (jV z)) E₀ = treeLenCovOne (m₀) (jV z) (XV z))
    (hΔV : ∀ z, treeLenCovOne (m₀) (jV z) (XV z) = 0)
    (hlogV : ∀ _z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))),
      Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hZV : ∀ z, readSites Hm k z ⊆ ↑(X₁V z))
    (hmarV : ∀ z, BlockMargin Gp (X₁V z)
      (↑(blockSites d L N₁ m₁ (k + 1) k z) : Set (CTorus d L N₁ m₁ (k + 1)))) :
    ∃ T : Set (CTorus d L N₁ m₁ (k + 1)) → (unitPts Gp × Fin N → ℂ) → (unitPts Gp × Fin N → ℂ) →
        ℂ → RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ,
      LocIntDm (IsDj m₀ (k + 1)) (id : (unitPts Gp × Fin N → ℂ) → _)
        (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps) (HatRaysO Gp cψ R₁ Rσ r) Rσ
        (Finset.univ.biUnion fun z => polyDom Gp (X₁V z) m₀ (jV z) (𝒦XV z)) T
        (fun x₀ w σ Θ => raySrc3 (hatFun Gp a₁ ν eps hG' cc
          (interactionOne hG hG' le_rfl a₁ ν eps)) taylorWeight x₀ w σ Θ)
        (fun Y => (3 * c1 d L * ((L : ℝ) ^ (m₀ + m₁)) ^ d * ‖energyBdScaled d L N (compWeight L a₁) k
          (cK2' d L N (famConst d L BG₂ κ) * δ₁) δ₁ (rho4 d L N BG κ)‖ / r ^ 3) *
          Real.exp (-(2 * κdec - 1) * treeLenCovOne m₀ (k + 1) Y))
        (fun Y Θ Θ' => agreeOn Y Θ Θ') (AgHatFDir hG')
      ∧ (∀ (Y : Set (CTorus d L N₁ m₁ (k + 1))) (Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N),
        Θ ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps → ∀ ψ : unitPts Gp × Fin N → ℂ,
        (∀ p, (R₁ + r) * (3 / 2) * ‖ψ p‖ ≤ cψ) →
        DifferentiableOn ℂ (fun z : ℂ => T Y (z • ψ) (z • ψ) 1 Θ) (ball (0 : ℂ) (3 / 2))) ∧
      ∃ (F₁ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
            DecParams Gp × RawData d L (N₁ * L ^ m₁) (k + 1) N → (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ))
          (Sol : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
            Dec2.DecParams (coverOf Gp) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)),
        (∀ z (s : DecParams Gp) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
          InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
            (α : Gp.Ω 1 → ℂ), IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
            F₁ z (s, rawOf D) = (φ, α)) ∧
        (∀ z (p : Dec2.DecParams (coverOf Gp) × Edat Hm N), (∀ P, ‖p.1 P‖ < Real.exp κ) →
          StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
            (Sol z p).1 = dphi Hm (Dec2.decG (coverOf Gp) Hm (compWeight L a₁) ν p.1) p.2.2.1 p.2.1
              (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol z p).2 ∧
            Dec2.DecFixed (coverOf Gp) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
              (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol z p).2 ∧
            Small Hm (Sol z p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
            Small Hm (Sol z p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
            SupBounds Hm (Sol z p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
            (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
              Dec2.DecFixed (coverOf Gp) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
                (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol z p).2)) ∧
        T = fun Y x₀ w σ Θ =>
          ∑ z, if Y ∈ polyDom Gp (X₁V z) m₀ (jV z) (𝒦XV z) then
            rayTerm (dl3 (evTerm
              (fun i : ParIdx Gp (↑(X₁V z) : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) Gp m₀
              (X1 Gp m₀ (jV z) (𝒦XV z))
              (fun u s => blockEnergyFun Gp Hm (compWeight L a₁) ν k z
                (F₁ z (extParams Gp (↑(X₁V z) : Set (CTorus d L N₁ m₁ (k + 1))) s, u.1))
                (Sol z (extParams Gp (↑(X₁V z) : Set (CTorus d L N₁ m₁ (k + 1))) s,
                  flEdat Gp Hm (F₁ z (extParams Gp (↑(X₁V z) : Set (CTorus d L N₁ m₁ (k + 1))) s, u.1))
                    u.1.1 (hatPsiF Gp a₁ ν hG' cc (F₁ z)
                      (extParams Gp (↑(X₁V z) : Set (CTorus d L N₁ m₁ (k + 1))) s) u.1 u.2))).1
                (u.1, hatPsiF Gp a₁ ν hG' cc (F₁ z)
                  (extParams Gp (↑(X₁V z) : Set (CTorus d L N₁ m₁ (k + 1))) s) u.1 u.2)) Y) w) taylorWeight x₀ σ Θ
          else 0 := by
  classical
  have hd : 3 ≤ d := hC.HBp.hd
  have hd0 : 0 < d := by omega
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hc1 : 0 ≤ c1 d L := by unfold c1; positivity
  have hB0 : 0 ≤ famConst d L BG₂ κ := by
    have := famConst_ge_one (L := L) hC.hS2.fam.2.1 κ hd0; linarith
  have hK2 : 0 ≤ cK2' d L N (famConst d L BG₂ κ) * δ₁ :=
    mul_nonneg (cK2'_nonneg hB0) hC.δ₁_pos.le
  have hr3 : 0 < r ^ 3 := by positivity
  have hM0 : 0 ≤ ((L : ℝ) ^ (m₀ + m₁)) ^ d := by positivity
  have hP0 : 0 ≤ ((L : ℝ) ^ (k + 1)) ^ d := by positivity
  -- the potential part, with its labels
  obtain ⟨TV, hLV0, hrayV, F₁, Sol, hF₁, hSol, hTV⟩ := vpart_locInt_hat_dir_dm_scaled_ray (m₀ := fun _ => m₀) (j := jV) (X := XV) (𝒦X := 𝒦XV)
    (X₁f := X₁V) hC hk hG hG' cc hcψ hMX hdm hα hsmX hδ₁ ha₁ H hc7 hR hRs hsmall hnum hnum'
    hreal hcovV hX₁V hconn hrow hoptV hΔV hκ₀ hκdec hκ h1 hlogV hZV hmarV continuous_taylorWeight
    hR₁ (analyticOnNhd_taylorWeight _) (Mω := 1 / 2) (by norm_num)
    (fun t ht => norm_taylorWeight_le t ht) hr (Rσ := Rσ)
  have hLV := (hLV0.mono_P (P' := IsDj m₀ (k + 1)) fun Y hY => hY.elim fun _ h => h).mono_XW (hatRaysO_subset (N := N) (Gp := Gp) cψ R₁ Rσ r)
  have hbV : ∀ Y ∈ Finset.univ.biUnion
      (fun z => polyDom Gp (X₁V z) m₀ (jV z) (𝒦XV z)),
      (∑ z, if Y ∈ polyDom Gp (X₁V z) m₀ (jV z) (𝒦XV z) then
        (1 / 2 : ℝ) * (6 * ‖energyBdScaled d L N (compWeight L a₁) k
          (cK2' d L N (famConst d L BG₂ κ) * δ₁) δ₁ (rho4 d L N BG κ) *
          Real.exp (-2 * κdec * treeLenCov Gp m₀ Y)‖ / r ^ 3) else 0) ≤
      (3 * c1 d L * ((L : ℝ) ^ (m₀ + m₁)) ^ d * ‖energyBdScaled d L N (compWeight L a₁) k
          (cK2' d L N (famConst d L BG₂ κ) * δ₁) δ₁ (rho4 d L N BG κ)‖ / r ^ 3) *
        Real.exp (-(2 * κdec - 1) * treeLenCovOne m₀ (k + 1) Y) := by
    intro Y hY
    obtain ⟨z₀, -, hz₀⟩ := Finset.mem_biUnion.1 hY
    have hMD := polyDom_isMultiDom (hcovV z₀) hd (hoptV z₀) hz₀
    have hcard : ((Finset.univ.filter fun z => Y ∈ polyDom Gp (X₁V z) m₀ (jV z)
        (𝒦XV z)).card : ℝ) ≤ c1 d L * ((L : ℝ) ^ (m₀ + m₁)) ^ d * (1 + treeLenCov Gp m₀ Y) := by
      refine card_blocks_filter_le hG' le_rfl (hcovV z₀).hN hMD _ (fun z hz => ?_)
      have h1' := subset_polyDom (Finset.mem_filter.1 hz).2
      rw [← hX₁V z] at h1'
      intro x hx
      exact h1' (hZV z ⟨x, Finset.mem_coe.1 hx, Or.inl rfl⟩)
    have ht0 := treeLenCov_nonneg Gp m₀ Y
    set Eb := ‖energyBdScaled d L N (compWeight L a₁) k
      (cK2' d L N (famConst d L BG₂ κ) * δ₁) δ₁ (rho4 d L N BG κ)‖ with hEb
    have hv : 0 ≤ (1 / 2 : ℝ) * (6 * ‖energyBdScaled d L N (compWeight L a₁) k
          (cK2' d L N (famConst d L BG₂ κ) * δ₁) δ₁ (rho4 d L N BG κ) *
          Real.exp (-2 * κdec * treeLenCov Gp m₀ Y)‖ / r ^ 3) := by positivity
    refine (sum_ite_card_le _ hv hcard).trans ?_
    rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le, ← hEb,
      ← treeLenCov_eq_treeLenCovOne hG' m₀ Y]
    have key := one_add_mul_exp_le (treeLenCov Gp m₀ Y) κdec
    have hCV : 0 ≤ 3 * c1 d L * ((L : ℝ) ^ (m₀ + m₁)) ^ d * Eb / r ^ 3 := by positivity
    calc c1 d L * ((L : ℝ) ^ (m₀ + m₁)) ^ d * (1 + treeLenCov Gp m₀ Y) *
          ((1 / 2 : ℝ) * (6 * (Eb * Real.exp (-2 * κdec * treeLenCov Gp m₀ Y)) / r ^ 3))
        = (3 * c1 d L * ((L : ℝ) ^ (m₀ + m₁)) ^ d * Eb / r ^ 3) *
          ((1 + treeLenCov Gp m₀ Y) * Real.exp (-2 * κdec * treeLenCov Gp m₀ Y)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left key hCV
  have hLV' := hLV.mono_on hbV
  subst hTV
  exact ⟨_, hLV', hrayV, F₁, Sol, hF₁, hSol, rfl⟩

/-- The potential part with the resummed bound, for the sharp agreement `AgHatFDir`. -/
theorem hat_vpart_bound_dm_dir_scaled {Kc Cx c₂ BG₂ δ₁ : ℝ}
    (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hconn : HatConn Gp) (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    {R₁ : ℝ} (hR₁ : 1 < R₁) {r Rσ : ℝ} (hr : 0 < r)
    (hk : 1 ≤ k) (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsmX : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    (ha₁ : 0 < a₁)
    (H : BgHyp d L (k + 1) ϱm (compWeight L a₁) ν) (hc7 : c7 d L N BG κ ≤ thm73C3 d L N)
    {R : ℝ} (hR : 2 ≤ R) (hRs : R * δ₁ ≤ deltaStar d L N)
    (hsmall : cK2 d L N * (R * δ₁) < bgC0 d L N / 2)
    (hnum : cK2 d L N * δ₁ ≤ c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hnum' : cK2' d L N (famConst d L BG₂ κ) * δ₁ ≤
      c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hreal : ∀ D' : BgData Gp N, XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D' →
      ∀ ψ' ∈ FlBall Hm δ₁, IsLayerConstant Hm ψ' → ∃ D : BgData Hm N,
      (∀ x i, D.h x i = D'.h x i) ∧
      compTangent hG hG' le_rfl (compWeight L a₁)
        (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D') D' D = ψ' ∧
      ∀ t : ℂ, ‖t‖ < R → InUnionDomainC Hm (bgC0 d L N) (bgC1 d L N) ν
        ((composeData (hG.precedes hG' le_rfl) (compWeight L a₁)
          (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D') D').lineAt
          (tangentData D (composeData (hG.precedes hG' le_rfl) (compWeight L a₁)
            (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D') D')) t))
    {m₀ : ℕ} {jV : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → ℕ}
    {XV 𝒦XV : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Set (CTorus d L N₁ m₁ (k + 1))}
    {X₁V : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Finset (CTorus d L N₁ m₁ (k + 1))}
    (hcovV : ∀ z, CovSetup Gp (m₀) (jV z) (XV z) (𝒦XV z))
    (hX₁V : ∀ z, (↑(X₁V z) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp (m₀) (jV z) (𝒦XV z))
    (hoptV : ∀ z, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XV z) ∧ MeetsOne (m₀) (jV z) (𝒦XV z) W₀ ∧
        bondCost (scaleW L (m₀) m₁ (jV z)) E₀ = treeLenCovOne (m₀) (jV z) (XV z))
    (hΔV : ∀ z, treeLenCovOne (m₀) (jV z) (XV z) = 0)
    (hlogV : ∀ _z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))),
      Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hZV : ∀ z, readSites Hm k z ⊆ ↑(X₁V z))
    (hmarV : ∀ z, BlockMargin Gp (X₁V z)
      (↑(blockSites d L N₁ m₁ (k + 1) k z) : Set (CTorus d L N₁ m₁ (k + 1)))) :
    ∃ T : Set (CTorus d L N₁ m₁ (k + 1)) → (unitPts Gp × Fin N → ℂ) → (unitPts Gp × Fin N → ℂ) →
        ℂ → RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ,
      LocIntDm (IsDj m₀ (k + 1)) (id : (unitPts Gp × Fin N → ℂ) → _)
        (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps) (HatRaysO Gp cψ R₁ Rσ r) Rσ
        (Finset.univ.biUnion fun z => polyDom Gp (X₁V z) m₀ (jV z) (𝒦XV z)) T
        (fun x₀ w σ Θ => raySrc3 (hatFun Gp a₁ ν eps hG' cc
          (interactionOne hG hG' le_rfl a₁ ν eps)) taylorWeight x₀ w σ Θ)
        (fun Y => (3 * c1 d L * ((L : ℝ) ^ (m₀ + m₁)) ^ d * ‖energyBdScaled d L N (compWeight L a₁) k
          (cK2' d L N (famConst d L BG₂ κ) * δ₁) δ₁ (rho4 d L N BG κ)‖ / r ^ 3) *
          Real.exp (-(2 * κdec - 1) * treeLenCovOne m₀ (k + 1) Y))
        (fun Y Θ Θ' => agreeOn Y Θ Θ') (AgHatFDir hG') := by
  classical
  exact (hat_vpart_bound_dm_dir_scaled_ray (Kc := Kc) (Cx := Cx) (c₂ := c₂) (BG₂ := BG₂) (δ₁ := δ₁) hC hconn hrow (κdec := κdec) (κ₀ := κ₀) hκ₀ hκdec hκ h1 (R₁ := R₁) hR₁ (r := r) (Rσ := Rσ) hr hk hG hG' cc (cψ := cψ) hcψ hMX (δc := δc) hdm hα hsmX hδ₁ ha₁ H hc7 (R := R) hR hRs hsmall hnum hnum' hreal (m₀ := m₀) (jV := jV) (XV := XV) (𝒦XV := 𝒦XV) (X₁V := X₁V) hcovV hX₁V hoptV hΔV hlogV hZV hmarV).imp fun _ h => h.1

/-- **Ray-differentiable form of `interaction_expansion_hat_bound_dm_dir_eta_scaled`.**  The statement of `interaction_expansion_hat_bound_dm_dir_eta_scaled` together with the
differentiability of the terms along the complex hat ray `z ↦ z • ψ̂` on `‖z‖ < 3/2`.
The last two conjuncts: the labels are the union of the label sets of the four parts, and at zero
source, on labels outside the old-term and observable label sets, the term is the potential part
`-cβ ∑_z [Y ∈ polyDom_z] rayTerm (dl3 (Ev_z Y) w₁) taylorWeight x₁ σ Θ`, `Ev_z = evTerm … FF_z` at a
pair `(F₁ z, Sol z)` with their defining properties. -/
theorem interaction_expansion_hat_bound_dm_dir_eta_scaled_ray {Kc Cx c₂ BG₂ δ₁ : ℝ}
    (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (cβ : ℂ)
    (hconn : HatConn Gp) (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    {R₁ : ℝ} (hR₁ : 1 < R₁) {r Rσ : ℝ} (hr : 0 < r)
    {η : ℝ} (hη0 : 0 < η)
    -- the hat variable
    (hk : 1 ≤ k) (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsmX : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    -- the potential part
    (ha₁ : 0 < a₁)
    (H : BgHyp d L (k + 1) ϱm (compWeight L a₁) ν) (hc7 : c7 d L N BG κ ≤ thm73C3 d L N)
    {R : ℝ} (hR : 2 ≤ R) (hRs : R * δ₁ ≤ deltaStar d L N)
    (hsmall : cK2 d L N * (R * δ₁) < bgC0 d L N / 2)
    (hnum : cK2 d L N * δ₁ ≤ c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hnum' : cK2' d L N (famConst d L BG₂ κ) * δ₁ ≤
      c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hreal : ∀ D' : BgData Gp N, XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D' →
      ∀ ψ' ∈ FlBall Hm δ₁, IsLayerConstant Hm ψ' → ∃ D : BgData Hm N,
      (∀ x i, D.h x i = D'.h x i) ∧
      compTangent hG hG' le_rfl (compWeight L a₁)
        (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D') D' D = ψ' ∧
      ∀ t : ℂ, ‖t‖ < R → InUnionDomainC Hm (bgC0 d L N) (bgC1 d L N) ν
        ((composeData (hG.precedes hG' le_rfl) (compWeight L a₁)
          (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D') D').lineAt
          (tangentData D (composeData (hG.precedes hG' le_rfl) (compWeight L a₁)
            (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D') D')) t))
    {m₀ : ℕ} {jV : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → ℕ}
    {XV 𝒦XV : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Set (CTorus d L N₁ m₁ (k + 1))}
    {X₁V : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Finset (CTorus d L N₁ m₁ (k + 1))}
    (hcovV : ∀ z, CovSetup Gp (m₀) (jV z) (XV z) (𝒦XV z))
    (hX₁V : ∀ z, (↑(X₁V z) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp (m₀) (jV z) (𝒦XV z))
    (hoptV : ∀ z, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XV z) ∧ MeetsOne (m₀) (jV z) (𝒦XV z) W₀ ∧
        bondCost (scaleW L (m₀) m₁ (jV z)) E₀ = treeLenCovOne (m₀) (jV z) (XV z))
    (hΔV : ∀ z, treeLenCovOne (m₀) (jV z) (XV z) = 0)
    (hlogV : ∀ _z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))), Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤
      (κ / 2 - 1) / 2)
    (hZV : ∀ z, readSites Hm k z ⊆ ↑(X₁V z))
    (hmarV : ∀ z, BlockMargin Gp (X₁V z)
      (↑(blockSites d L N₁ m₁ (k + 1) k z) : Set (CTorus d L N₁ m₁ (k + 1))))
    -- the old terms
    {τι : Type*} [DecidableEq τι] (𝒯E : Finset τι) {ϱ₁ ϱ₂ : τι → ℝ}
    {GkE : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₁ τ)}
    {GjE : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₂ τ)} {r₀ δ₃ δfl : ℝ}
    {X₀E X₁E : τι → Finset (CTorus d L N₁ m₁ (k + 1))} {jE : τι → ℕ}
    {XE 𝒦XE : τι → Set (CTorus d L N₁ m₁ (k + 1))} {EbE : τι → ℝ}
    (hBE : ∀ τ ∈ 𝒯E, BgSetting N Gp (GkE τ) (GjE τ) a₁ ν c BG κ r₀ eps δ₃ (X₀E τ) (X₁E τ) (jE τ))
    (hFE : ∀ τ ∈ 𝒯E, FlSetting N Gp (GkE τ) Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl (X₁E τ))
    (hcovE : ∀ τ ∈ 𝒯E, CovSetup Gp (m₀) (jE τ) (XE τ) (𝒦XE τ))
    (hX₁E : ∀ τ ∈ 𝒯E, (↑(X₁E τ) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp (m₀) (jE τ) (𝒦XE τ))
    (hoptE : ∀ τ ∈ 𝒯E, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XE τ) ∧ MeetsOne (m₀) (jE τ) (𝒦XE τ) W₀ ∧
        bondCost (scaleW L (m₀) m₁ (jE τ)) E₀ = treeLenCovOne (m₀) (jE τ) (XE τ))
    (hlogE : ∀ τ ∈ 𝒯E, Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) *
      (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hEbE : ∀ τ ∈ 𝒯E, 0 ≤ EbE τ) {EE : τι → RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ}
    (hEanE : ∀ τ ∈ 𝒯E, AnalyticOnNhd ℂ (EE τ) (XiCRaw (GjE τ) (compWeight L a₁) ν (jE τ)
      (scaledC0 d) (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)))
    (hEbdE : ∀ τ ∈ 𝒯E, ∀ r ∈ XiCRaw (GjE τ) (compWeight L a₁) ν (jE τ) (scaledC0 d)
      (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      ‖EE τ r‖ ≤ EbE τ * Real.exp (-(κdec - 1) * treeLenCovOne (m₀) (jE τ) (XE τ)))
    -- the sites of the source
    {jF : CTorus d L N₁ m₁ (k + 1) × Fin N → ℕ}
    {XF 𝒦XF : CTorus d L N₁ m₁ (k + 1) × Fin N → Set (CTorus d L N₁ m₁ (k + 1))}
    {X₁F : CTorus d L N₁ m₁ (k + 1) × Fin N → Finset (CTorus d L N₁ m₁ (k + 1))}
    (hcovF : ∀ s, CovSetup Gp (m₀) (jF s) (XF s) (𝒦XF s))
    (hX₁F : ∀ s, (↑(X₁F s) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp (m₀) (jF s) (𝒦XF s))
    (hoptF : ∀ s, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XF s) ∧ MeetsOne (m₀) (jF s) (𝒦XF s) W₀ ∧
        bondCost (scaleW L (m₀) m₁ (jF s)) E₀ = treeLenCovOne (m₀) (jF s) (XF s))
    (hΔF : ∀ s, treeLenCovOne (m₀) (jF s) (XF s) = 0)
    (hlogF : ∀ _s : CTorus d L N₁ m₁ (k + 1) × Fin N, Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤
      (κ / 2 - 1) / 2)
    (hyF : ∀ s : CTorus d L N₁ m₁ (k + 1) × Fin N, s.1 ∈ X₁F s)
    -- the observable terms
    {μι : Type*} [DecidableEq μι] (𝒯M : Finset μι) {ϱ₁M ϱ₂M : μι → ℝ}
    {GkM : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₁M τ)}
    {GjM : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₂M τ)}
    {X₀M X₁M : μι → Finset (CTorus d L N₁ m₁ (k + 1))} {jM : μι → ℕ}
    {XM 𝒦XM : μι → Set (CTorus d L N₁ m₁ (k + 1))} {EbM : μι → ℝ}
    (ys : μι → CTorus d L N₁ m₁ (k + 1)) (is : μι → Fin N) (hys : ∀ τ ∈ 𝒯M, ys τ ∈ X₁M τ)
    (hBM : ∀ τ ∈ 𝒯M, BgSetting N Gp (GkM τ) (GjM τ) a₁ ν c BG κ r₀ eps δ₃ (X₀M τ) (X₁M τ) (jM τ))
    (hFM : ∀ τ ∈ 𝒯M, FlSetting N Gp (GkM τ) Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl (X₁M τ))
    (hcovM : ∀ τ ∈ 𝒯M, CovSetup Gp (m₀) (jM τ) (XM τ) (𝒦XM τ))
    (hX₁M : ∀ τ ∈ 𝒯M, (↑(X₁M τ) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp (m₀) (jM τ) (𝒦XM τ))
    (hoptM : ∀ τ ∈ 𝒯M, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XM τ) ∧ MeetsOne (m₀) (jM τ) (𝒦XM τ) W₀ ∧
        bondCost (scaleW L (m₀) m₁ (jM τ)) E₀ = treeLenCovOne (m₀) (jM τ) (XM τ))
    (hlogM : ∀ τ ∈ 𝒯M, Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) *
      (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hEbM : ∀ τ ∈ 𝒯M, 0 ≤ EbM τ) {EM : μι → RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ}
    (hEanM : ∀ τ ∈ 𝒯M, AnalyticOnNhd ℂ (EM τ) (XiCRaw (GjM τ) (compWeight L a₁) ν (jM τ)
      (scaledC0 d) (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)))
    (hEbdM : ∀ τ ∈ 𝒯M, ∀ r ∈ XiCRaw (GjM τ) (compWeight L a₁) ν (jM τ) (scaledC0 d)
      (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      ‖EM τ r‖ ≤ EbM τ * Real.exp (-(κdec - 1) * treeLenCovOne (m₀) (jM τ) (XM τ)))
    -- the sizes of the old terms and of the observable terms (the source bounds of (3.2)-(3.4)):
    -- the bounds of the terms rooted at one site (resp. at one source site) add up to `ρ`
    (rE : τι → CTorus d L N₁ m₁ (k + 1)) (hrE : ∀ τ ∈ 𝒯E, rE τ ∈ X₁E τ) {ρE : ℝ} (hρE0 : 0 ≤ ρE)
    (hρE : ∀ x : CTorus d L N₁ m₁ (k + 1), ∑ τ ∈ 𝒯E.filter (fun τ => rE τ = x),
      EbE τ * Real.exp (-κ₀ * treeLenCovOne m₀ (jE τ) (XE τ)) ≤ ρE)
    {ρM : ℝ} (hρM0 : 0 ≤ ρM)
    (hρM : ∀ p : CTorus d L N₁ m₁ (k + 1) × Fin N, ∑ τ ∈ 𝒯M.filter (fun τ => (ys τ, is τ) = p),
      EbM τ * Real.exp (-κ₀ * treeLenCovOne m₀ (jM τ) (XM τ)) ≤ ρM) :
    ∃ (𝒴 : Finset (Set (CTorus d L N₁ m₁ (k + 1))))
      (T : Set (CTorus d L N₁ m₁ (k + 1)) →
        ((unitPts Gp × Fin N → ℂ) × (unitPts Gp × Fin N → ℂ)) →
        ((unitPts Gp × Fin N → ℂ) × (unitPts Gp × Fin N → ℂ)) → ℂ →
        RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ),
      LocIntDm (IsDj m₀ (k + 1)) (fun ψ : unitPts Gp × Fin N → ℂ => (ψ, ψ))
        (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ l1BallEta d L N₁ m₁ (k + 1) N η)
        {xw : ((unitPts Gp × Fin N → ℂ) × (unitPts Gp × Fin N → ℂ)) ×
            ((unitPts Gp × Fin N → ℂ) × (unitPts Gp × Fin N → ℂ)) |
          (xw.1.1, xw.2.1) ∈ HatRaysO Gp cψ R₁ Rσ r ∧ (xw.1.2, xw.2.2) ∈ HatRaysO Gp cψ R₁ Rσ r}
        Rσ 𝒴 T
        (fun x w σ p =>
          (-cβ) * raySrc3 (hatFun Gp a₁ ν eps hG' cc (interactionOne hG hG' le_rfl a₁ ν eps))
            taylorWeight x.1 w.1 σ p.1 +
          cβ * (∑ τ ∈ 𝒯E, if h : τ ∈ 𝒯E then
            dirTermSrc (hatFun Gp a₁ ν eps hG' cc (flComp (hBE τ h) (hFE τ h) (EE τ)))
              (fun _ => (1 : ℂ)) x.1 w.1 σ p.1 else 0) +
          cβ * (∑ s : CTorus d L N₁ m₁ (k + 1) × Fin N, p.2 s.1 s.2 *
            dirTermSrc (hatFun Gp a₁ ν eps hG' cc (onXi Gp a₁ ν eps
              (fun D ψ' => svec Hm (flFieldOne Gp Hm BG₂ κ a₁ ν D ψ') s.1 s.2)))
              (fun _ => (1 : ℂ)) x.2 w.2 σ p.1) +
          cβ * (∑ τ ∈ 𝒯M, if h : τ ∈ 𝒯M then
            p.2 (ys τ) (is τ) * dirTermSrc (hatFun Gp a₁ ν eps hG' cc
              (flComp (hBM τ h) (hFM τ h) (EM τ))) (fun _ => (1 : ℂ)) x.2 w.2 σ p.1 else 0))
        (fun Y => prop33EpsEtaScaled d L N m₁ k m₀ a₁ BG BG₂ κ δ₁ r ρE ρM η * ‖cβ‖ *
          Real.exp (-(2 * κdec - 1) * treeLenCovOne m₀ (k + 1) Y))
        (fun Y p p' => agreeOn Y p.1 p'.1 ∧ ∀ x ∈ Y, p.2 x = p'.2 x)
        (fun Y a a' => AgHatFDir hG' Y a.1 a'.1 ∧ AgHatFDir hG' Y a.2 a'.2)
      ∧ (∀ (Y : Set (CTorus d L N₁ m₁ (k + 1)))
          (q : RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)),
        q ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ l1BallEta d L N₁ m₁ (k + 1) N η →
        ∀ ψ : unitPts Gp × Fin N → ℂ, (∀ p, (R₁ + r) * (3 / 2) * ‖ψ p‖ ≤ cψ) →
        DifferentiableOn ℂ (fun ζ : ℂ => T Y (ζ • ψ, ζ • ψ) (ζ • ψ, ζ • ψ) 1 q)
          (ball (0 : ℂ) (3 / 2))) ∧
      𝒴 = (Finset.univ.biUnion fun z => polyDom Gp (X₁V z) m₀ (jV z) (𝒦XV z)) ∪
          (𝒯E.biUnion fun τ => polyDom Gp (X₁E τ) m₀ (jE τ) (𝒦XE τ)) ∪
          (Finset.univ.biUnion fun s => polymerDomains
            (fun i : ParIdx Gp (↑(X₁F s) : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) Gp m₀
            (X1 Gp m₀ (jF s) (𝒦XF s))) ∪
          (𝒯M.biUnion fun τ => polyDom Gp (X₁M τ) m₀ (jM τ) (𝒦XM τ)) ∧
      ∃ (F₁ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
            DecParams Gp × RawData d L (N₁ * L ^ m₁) (k + 1) N → (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ))
          (Sol : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
            Dec2.DecParams (coverOf Gp) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)),
        (∀ z (s : DecParams Gp) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
          InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
            (α : Gp.Ω 1 → ℂ), IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
            F₁ z (s, rawOf D) = (φ, α)) ∧
        (∀ z (p : Dec2.DecParams (coverOf Gp) × Edat Hm N), (∀ P, ‖p.1 P‖ < Real.exp κ) →
          StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
            (Sol z p).1 = dphi Hm (Dec2.decG (coverOf Gp) Hm (compWeight L a₁) ν p.1) p.2.2.1 p.2.1
              (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol z p).2 ∧
            Dec2.DecFixed (coverOf Gp) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
              (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol z p).2 ∧
            Small Hm (Sol z p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
            Small Hm (Sol z p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
            SupBounds Hm (Sol z p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
            (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
              Dec2.DecFixed (coverOf Gp) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
                (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol z p).2)) ∧
        (∀ (Y : Set (CTorus d L N₁ m₁ (k + 1)))
          (x w : (unitPts Gp × Fin N → ℂ) × (unitPts Gp × Fin N → ℂ)) (σ : ℂ)
          (Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N),
          Y ∉ 𝒯E.biUnion (fun τ => polyDom Gp (X₁E τ) m₀ (jE τ) (𝒦XE τ)) →
          Y ∉ 𝒯M.biUnion (fun τ => polyDom Gp (X₁M τ) m₀ (jM τ) (𝒦XM τ)) →
          T Y x w σ (Θ, 0) = -cβ *
            ∑ z, if Y ∈ polyDom Gp (X₁V z) m₀ (jV z) (𝒦XV z) then
              rayTerm (dl3 (evTerm
                (fun i : ParIdx Gp (↑(X₁V z) : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) Gp m₀
                (X1 Gp m₀ (jV z) (𝒦XV z))
                (fun u s => blockEnergyFun Gp Hm (compWeight L a₁) ν k z
                  (F₁ z (extParams Gp (↑(X₁V z) : Set (CTorus d L N₁ m₁ (k + 1))) s, u.1))
                  (Sol z (extParams Gp (↑(X₁V z) : Set (CTorus d L N₁ m₁ (k + 1))) s,
                    flEdat Gp Hm (F₁ z (extParams Gp (↑(X₁V z) : Set (CTorus d L N₁ m₁ (k + 1))) s, u.1))
                      u.1.1 (hatPsiF Gp a₁ ν hG' cc (F₁ z)
                        (extParams Gp (↑(X₁V z) : Set (CTorus d L N₁ m₁ (k + 1))) s) u.1 u.2))).1
                  (u.1, hatPsiF Gp a₁ ν hG' cc (F₁ z)
                    (extParams Gp (↑(X₁V z) : Set (CTorus d L N₁ m₁ (k + 1))) s) u.1 u.2)) Y) w.1) taylorWeight x.1 σ Θ
            else 0) ∧
      ∃ (F₂ : CTorus d L N₁ m₁ (k + 1) × Fin N →
            DecParams Gp × RawData d L (N₁ * L ^ m₁) (k + 1) N →
              (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ))
          (Sol₂ : CTorus d L N₁ m₁ (k + 1) × Fin N →
            Dec2.DecParams (coverOf Gp) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)),
        (∀ (a : CTorus d L N₁ m₁ (k + 1) × Fin N) (s : DecParams Gp) (D : BgData Gp N),
          (∀ P, ‖s P‖ < Real.exp κ) →
          InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
            (α : Gp.Ω 1 → ℂ), IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
            F₂ a (s, rawOf D) = (φ, α)) ∧
        (∀ (a : CTorus d L N₁ m₁ (k + 1) × Fin N) (p : Dec2.DecParams (coverOf Gp) × Edat Hm N),
          (∀ P, ‖p.1 P‖ < Real.exp κ) →
          StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
            (Sol₂ a p).1 = dphi Hm (Dec2.decG (coverOf Gp) Hm (compWeight L a₁) ν p.1) p.2.2.1 p.2.1
              (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol₂ a p).2 ∧
            Dec2.DecFixed (coverOf Gp) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
              (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol₂ a p).2 ∧
            Small Hm (Sol₂ a p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
            Small Hm (Sol₂ a p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
            SupBounds Hm (Sol₂ a p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
            (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
              Dec2.DecFixed (coverOf Gp) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
                (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol₂ a p).2)) ∧
        ∀ (Y : Set (CTorus d L N₁ m₁ (k + 1)))
          (x w : (unitPts Gp × Fin N → ℂ) × (unitPts Gp × Fin N → ℂ)) (σ : ℂ)
          (Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N)
          (g : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ),
          Y ∉ 𝒯M.biUnion (fun τ => polyDom Gp (X₁M τ) m₀ (jM τ) (𝒦XM τ)) →
          T Y x w σ (Θ, g) = T Y x w σ (Θ, 0) + cβ *
            ∑ s : CTorus d L N₁ m₁ (k + 1) × Fin N,
              if Y ∈ polyDom Gp (X₁F s) m₀ (jF s) (𝒦XF s) then
                g s.1 s.2 * dirTerm (evTerm
                  (fun i : ParIdx Gp (↑(X₁F s) : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) Gp m₀
                  (X1 Gp m₀ (jF s) (𝒦XF s))
                  (fun u t => siteFun Gp Hm s.1 s.2
                    (F₂ s (extParams Gp (↑(X₁F s) : Set (CTorus d L N₁ m₁ (k + 1))) t, u.1))
                    (Sol₂ s (extParams Gp (↑(X₁F s) : Set (CTorus d L N₁ m₁ (k + 1))) t,
                      flEdat Gp Hm
                        (F₂ s (extParams Gp (↑(X₁F s) : Set (CTorus d L N₁ m₁ (k + 1))) t, u.1))
                        u.1.1 (hatPsiF Gp a₁ ν hG' cc (F₂ s)
                          (extParams Gp (↑(X₁F s) : Set (CTorus d L N₁ m₁ (k + 1))) t) u.1 u.2))).1
                    (u.1, hatPsiF Gp a₁ ν hG' cc (F₂ s)
                      (extParams Gp (↑(X₁F s) : Set (CTorus d L N₁ m₁ (k + 1))) t) u.1 u.2)) Y)
                  (fun _ => (1 : ℂ)) x.2 w.2 σ Θ
              else 0 := by
  classical
  have hd : 3 ≤ d := hC.HBp.hd
  have hd0 : 0 < d := by omega
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hc1 : 0 ≤ c1 d L := by unfold c1; positivity
  have hB0 : 0 ≤ famConst d L BG₂ κ := by
    have := famConst_ge_one (L := L) hC.hS2.fam.2.1 κ hd0; linarith
  have hK2 : 0 ≤ cK2' d L N (famConst d L BG₂ κ) * δ₁ :=
    mul_nonneg (cK2'_nonneg hB0) hC.δ₁_pos.le
  have hr3 : 0 < r ^ 3 := by positivity
  have hM0 : 0 ≤ ((L : ℝ) ^ (m₀ + m₁)) ^ d := by positivity
  have hP0 : 0 ≤ ((L : ℝ) ^ (k + 1)) ^ d := by positivity
  obtain ⟨TV, hV, hrayV, F₁, Sol, hF₁, hSol, hTV⟩ := hat_vpart_bound_dm_dir_scaled_ray hC hconn hrow hκ₀ hκdec hκ h1 hR₁ hr hk hG hG' cc hcψ hMX hdm
    hα hsmX hδ₁ ha₁ H hc7 hR hRs hsmall hnum hnum' hreal hcovV hX₁V hoptV hΔV hlogV hZV hmarV
    (Rσ := Rσ)
  obtain ⟨TE, hE, hrayE⟩ := hat_eparts_bound_dm_dir_ray hC hconn hrow hκ₀ hκdec hκ h1 hR₁ hr hk hG hG' cc hcψ hMX
    hdm hα hsmX hδ₁ 𝒯E hBE hFE hcovE hX₁E hoptE hlogE hEbE hEanE hEbdE rE hrE hρE0 hρE
    (Rσ := Rσ)
  obtain ⟨TF, hF, hrayF, hTF0, F₂, Sol₂, hF₂, hSol₂, hTFg⟩ := hat_fparts_bound_dm_dir_eta_ray hC hconn hrow hκ₀ hκdec hκ h1 hR₁ hr hη0 hk hG hG' cc hcψ hMX
    hdm hα hsmX hδ₁ hcovF hX₁F hoptF hΔF hlogF hyF (Rσ := Rσ)
  obtain ⟨TM, hM, hrayM⟩ := hat_mparts_bound_dm_dir_eta_ray hC hconn hrow hκ₀ hκdec hκ h1 hR₁ hr hη0 hk hG hG' cc hcψ hMX
    hdm hα hsmX hδ₁ 𝒯M ys is hys hBM hFM hcovM hX₁M hoptM hlogM hEbM hEanM hEbdM hρM0 hρM
    (Rσ := Rσ)
  have hnV : ∀ Y : Set (CTorus d L N₁ m₁ (k + 1)), 0 ≤ (3 * c1 d L * ((L : ℝ) ^ (m₀ + m₁)) ^ d *
      ‖energyBdScaled d L N (compWeight L a₁) k
          (cK2' d L N (famConst d L BG₂ κ) * δ₁) δ₁ (rho4 d L N BG κ)‖ / r ^ 3) *
        Real.exp (-(2 * κdec - 1) * treeLenCovOne m₀ (k + 1) Y) := fun Y => by positivity
  have hnE : ∀ Y : Set (CTorus d L N₁ m₁ (k + 1)), 0 ≤ (ρE * c1 d L * ((L : ℝ) ^ (k + 1)) ^ d *
      ((L : ℝ) ^ (m₀ + m₁)) ^ d / r) *
        Real.exp (-(2 * κdec - 1) * treeLenCovOne m₀ (k + 1) Y) := fun Y => by positivity
  have hnF : ∀ Y : Set (CTorus d L N₁ m₁ (k + 1)), 0 ≤ (η * (cK2' d L N (famConst d L BG₂ κ) * δ₁) / r) *
      Real.exp (-(2 * κdec - 1) * treeLenCovOne m₀ (k + 1) Y) := fun Y => by positivity
  have hnM : ∀ Y : Set (CTorus d L N₁ m₁ (k + 1)), 0 ≤ (η * ρM / r) *
      Real.exp (-(2 * κdec - 1) * treeLenCovOne m₀ (k + 1) Y) := fun Y => by positivity
  obtain ⟨𝒴, T, b, hb, hL0', hrayT, h𝒴, hT⟩ := LocIntDm.assemble_ray
    (AgΘ := fun Y Θ Θ' => agreeOn Y Θ Θ')
    (AgG := fun Y (g g' : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) => ∀ x ∈ Y, g x = g' x)
    hV hE hF hM (-cβ) cβ cβ cβ hnV hnE hnF hnM
    (P' := fun u => ∃ ψ : unitPts Gp × Fin N → ℂ, (∀ p, (R₁ + r) * (3 / 2) * ‖ψ p‖ ≤ cψ) ∧
      u = fun ζ : ℂ => ζ • ψ) (s := ball (0 : ℂ) (3 / 2))
    (fun Y u hu Θ hΘ => by obtain ⟨ψ, hψ, rfl⟩ := hu; exact hrayV Y Θ hΘ ψ hψ)
    (fun Y u hu Θ hΘ => by obtain ⟨ψ, hψ, rfl⟩ := hu; exact hrayE Y Θ hΘ ψ hψ)
    (fun Y u hu q hq => by obtain ⟨ψ, hψ, rfl⟩ := hu; exact hrayF Y q hq ψ hψ)
    (fun Y u hu q hq => by obtain ⟨ψ, hψ, rfl⟩ := hu; exact hrayM Y q hq ψ hψ)
  have hrayT' : ∀ (Y : Set (CTorus d L N₁ m₁ (k + 1)))
      (q : RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)),
      q ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ l1BallEta d L N₁ m₁ (k + 1) N η →
      ∀ ψ : unitPts Gp × Fin N → ℂ, (∀ p, (R₁ + r) * (3 / 2) * ‖ψ p‖ ≤ cψ) →
      DifferentiableOn ℂ (fun ζ : ℂ => T Y (ζ • ψ, ζ • ψ) (ζ • ψ, ζ • ψ) 1 q)
        (ball (0 : ℂ) (3 / 2)) :=
    fun Y q hq ψ hψ => hrayT Y (fun ζ => ζ • ψ) ⟨ψ, hψ, rfl⟩ q hq
  refine ⟨𝒴, T, (hL0'.mono_XW (XW' := {xw : ((unitPts Gp × Fin N → ℂ) × (unitPts Gp × Fin N → ℂ)) ×
            ((unitPts Gp × Fin N → ℂ) × (unitPts Gp × Fin N → ℂ)) |
          (xw.1.1, xw.2.1) ∈ HatRaysO Gp cψ R₁ Rσ r ∧ (xw.1.2, xw.2.2) ∈ HatRaysO Gp cψ R₁ Rσ r})
    (fun xw h => ⟨h.1, h.1, h.2, h.2⟩)).mono fun Y => (hb Y).trans (le_of_eq ?_), hrayT', h𝒴,
    F₁, Sol, hF₁, hSol, ?_, F₂, Sol₂, hF₂, hSol₂, ?_⟩
  · simp only [norm_neg, prop33EpsEtaScaled]
    ring
  · intro Y x w σ Θ hYE hYM
    subst hT hTV
    dsimp only
    rw [ite_eq_right hYE, ite_eq_right hYM, hTF0, mul_zero, ite_self, add_zero, add_zero, add_zero]
    by_cases hYV : Y ∈ Finset.univ.biUnion fun z => polyDom Gp (X₁V z) m₀ (jV z) (𝒦XV z)
    · rw [ite_eq_left hYV]
    · rw [ite_eq_right hYV, Finset.sum_eq_zero, mul_zero]
      intro z _
      exact ite_eq_right fun h => hYV (Finset.mem_biUnion.2 ⟨z, Finset.mem_univ _, h⟩)
  · intro Y x w σ Θ g hYM
    subst hT
    dsimp only
    rw [hTFg Y x.2 w.2 σ Θ g, hTF0 Y x.2 w.2 σ Θ, ite_eq_right hYM, ite_eq_right hYM]
    by_cases hYF : Y ∈ Finset.univ.biUnion fun s : CTorus d L N₁ m₁ (k + 1) × Fin N =>
        polyDom Gp (X₁F s) m₀ (jF s) (𝒦XF s)
    · rw [ite_eq_left hYF, ite_eq_left hYF]
      ring
    · rw [ite_eq_right hYF, ite_eq_right hYF, Finset.sum_eq_zero]
      · ring
      · intro s _
        exact ite_eq_right fun h => hYF (Finset.mem_biUnion.2 ⟨s, Finset.mem_univ _, h⟩)

/-- **The four parts in the variable `ψ̂` with the sharp agreement relation, without the mass
variation** (the sharp version of `interaction_expansion_hat_bound_dm`). -/
theorem interaction_expansion_hat_bound_dm_dir_eta_scaled {Kc Cx c₂ BG₂ δ₁ : ℝ}
    (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (cβ : ℂ)
    (hconn : HatConn Gp) (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    {R₁ : ℝ} (hR₁ : 1 < R₁) {r Rσ : ℝ} (hr : 0 < r)
    {η : ℝ} (hη0 : 0 < η)
    -- the hat variable
    (hk : 1 ≤ k) (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsmX : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    -- the potential part
    (ha₁ : 0 < a₁)
    (H : BgHyp d L (k + 1) ϱm (compWeight L a₁) ν) (hc7 : c7 d L N BG κ ≤ thm73C3 d L N)
    {R : ℝ} (hR : 2 ≤ R) (hRs : R * δ₁ ≤ deltaStar d L N)
    (hsmall : cK2 d L N * (R * δ₁) < bgC0 d L N / 2)
    (hnum : cK2 d L N * δ₁ ≤ c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hnum' : cK2' d L N (famConst d L BG₂ κ) * δ₁ ≤
      c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hreal : ∀ D' : BgData Gp N, XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D' →
      ∀ ψ' ∈ FlBall Hm δ₁, IsLayerConstant Hm ψ' → ∃ D : BgData Hm N,
      (∀ x i, D.h x i = D'.h x i) ∧
      compTangent hG hG' le_rfl (compWeight L a₁)
        (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D') D' D = ψ' ∧
      ∀ t : ℂ, ‖t‖ < R → InUnionDomainC Hm (bgC0 d L N) (bgC1 d L N) ν
        ((composeData (hG.precedes hG' le_rfl) (compWeight L a₁)
          (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D') D').lineAt
          (tangentData D (composeData (hG.precedes hG' le_rfl) (compWeight L a₁)
            (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D') D')) t))
    {m₀ : ℕ} {jV : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → ℕ}
    {XV 𝒦XV : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Set (CTorus d L N₁ m₁ (k + 1))}
    {X₁V : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Finset (CTorus d L N₁ m₁ (k + 1))}
    (hcovV : ∀ z, CovSetup Gp (m₀) (jV z) (XV z) (𝒦XV z))
    (hX₁V : ∀ z, (↑(X₁V z) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp (m₀) (jV z) (𝒦XV z))
    (hoptV : ∀ z, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XV z) ∧ MeetsOne (m₀) (jV z) (𝒦XV z) W₀ ∧
        bondCost (scaleW L (m₀) m₁ (jV z)) E₀ = treeLenCovOne (m₀) (jV z) (XV z))
    (hΔV : ∀ z, treeLenCovOne (m₀) (jV z) (XV z) = 0)
    (hlogV : ∀ _z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))), Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤
      (κ / 2 - 1) / 2)
    (hZV : ∀ z, readSites Hm k z ⊆ ↑(X₁V z))
    (hmarV : ∀ z, BlockMargin Gp (X₁V z)
      (↑(blockSites d L N₁ m₁ (k + 1) k z) : Set (CTorus d L N₁ m₁ (k + 1))))
    -- the old terms
    {τι : Type*} [DecidableEq τι] (𝒯E : Finset τι) {ϱ₁ ϱ₂ : τι → ℝ}
    {GkE : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₁ τ)}
    {GjE : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₂ τ)} {r₀ δ₃ δfl : ℝ}
    {X₀E X₁E : τι → Finset (CTorus d L N₁ m₁ (k + 1))} {jE : τι → ℕ}
    {XE 𝒦XE : τι → Set (CTorus d L N₁ m₁ (k + 1))} {EbE : τι → ℝ}
    (hBE : ∀ τ ∈ 𝒯E, BgSetting N Gp (GkE τ) (GjE τ) a₁ ν c BG κ r₀ eps δ₃ (X₀E τ) (X₁E τ) (jE τ))
    (hFE : ∀ τ ∈ 𝒯E, FlSetting N Gp (GkE τ) Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl (X₁E τ))
    (hcovE : ∀ τ ∈ 𝒯E, CovSetup Gp (m₀) (jE τ) (XE τ) (𝒦XE τ))
    (hX₁E : ∀ τ ∈ 𝒯E, (↑(X₁E τ) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp (m₀) (jE τ) (𝒦XE τ))
    (hoptE : ∀ τ ∈ 𝒯E, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XE τ) ∧ MeetsOne (m₀) (jE τ) (𝒦XE τ) W₀ ∧
        bondCost (scaleW L (m₀) m₁ (jE τ)) E₀ = treeLenCovOne (m₀) (jE τ) (XE τ))
    (hlogE : ∀ τ ∈ 𝒯E, Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) *
      (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hEbE : ∀ τ ∈ 𝒯E, 0 ≤ EbE τ) {EE : τι → RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ}
    (hEanE : ∀ τ ∈ 𝒯E, AnalyticOnNhd ℂ (EE τ) (XiCRaw (GjE τ) (compWeight L a₁) ν (jE τ)
      (scaledC0 d) (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)))
    (hEbdE : ∀ τ ∈ 𝒯E, ∀ r ∈ XiCRaw (GjE τ) (compWeight L a₁) ν (jE τ) (scaledC0 d)
      (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      ‖EE τ r‖ ≤ EbE τ * Real.exp (-(κdec - 1) * treeLenCovOne (m₀) (jE τ) (XE τ)))
    -- the sites of the source
    {jF : CTorus d L N₁ m₁ (k + 1) × Fin N → ℕ}
    {XF 𝒦XF : CTorus d L N₁ m₁ (k + 1) × Fin N → Set (CTorus d L N₁ m₁ (k + 1))}
    {X₁F : CTorus d L N₁ m₁ (k + 1) × Fin N → Finset (CTorus d L N₁ m₁ (k + 1))}
    (hcovF : ∀ s, CovSetup Gp (m₀) (jF s) (XF s) (𝒦XF s))
    (hX₁F : ∀ s, (↑(X₁F s) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp (m₀) (jF s) (𝒦XF s))
    (hoptF : ∀ s, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XF s) ∧ MeetsOne (m₀) (jF s) (𝒦XF s) W₀ ∧
        bondCost (scaleW L (m₀) m₁ (jF s)) E₀ = treeLenCovOne (m₀) (jF s) (XF s))
    (hΔF : ∀ s, treeLenCovOne (m₀) (jF s) (XF s) = 0)
    (hlogF : ∀ _s : CTorus d L N₁ m₁ (k + 1) × Fin N, Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤
      (κ / 2 - 1) / 2)
    (hyF : ∀ s : CTorus d L N₁ m₁ (k + 1) × Fin N, s.1 ∈ X₁F s)
    -- the observable terms
    {μι : Type*} [DecidableEq μι] (𝒯M : Finset μι) {ϱ₁M ϱ₂M : μι → ℝ}
    {GkM : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₁M τ)}
    {GjM : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₂M τ)}
    {X₀M X₁M : μι → Finset (CTorus d L N₁ m₁ (k + 1))} {jM : μι → ℕ}
    {XM 𝒦XM : μι → Set (CTorus d L N₁ m₁ (k + 1))} {EbM : μι → ℝ}
    (ys : μι → CTorus d L N₁ m₁ (k + 1)) (is : μι → Fin N) (hys : ∀ τ ∈ 𝒯M, ys τ ∈ X₁M τ)
    (hBM : ∀ τ ∈ 𝒯M, BgSetting N Gp (GkM τ) (GjM τ) a₁ ν c BG κ r₀ eps δ₃ (X₀M τ) (X₁M τ) (jM τ))
    (hFM : ∀ τ ∈ 𝒯M, FlSetting N Gp (GkM τ) Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl (X₁M τ))
    (hcovM : ∀ τ ∈ 𝒯M, CovSetup Gp (m₀) (jM τ) (XM τ) (𝒦XM τ))
    (hX₁M : ∀ τ ∈ 𝒯M, (↑(X₁M τ) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp (m₀) (jM τ) (𝒦XM τ))
    (hoptM : ∀ τ ∈ 𝒯M, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XM τ) ∧ MeetsOne (m₀) (jM τ) (𝒦XM τ) W₀ ∧
        bondCost (scaleW L (m₀) m₁ (jM τ)) E₀ = treeLenCovOne (m₀) (jM τ) (XM τ))
    (hlogM : ∀ τ ∈ 𝒯M, Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) *
      (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hEbM : ∀ τ ∈ 𝒯M, 0 ≤ EbM τ) {EM : μι → RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ}
    (hEanM : ∀ τ ∈ 𝒯M, AnalyticOnNhd ℂ (EM τ) (XiCRaw (GjM τ) (compWeight L a₁) ν (jM τ)
      (scaledC0 d) (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)))
    (hEbdM : ∀ τ ∈ 𝒯M, ∀ r ∈ XiCRaw (GjM τ) (compWeight L a₁) ν (jM τ) (scaledC0 d)
      (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      ‖EM τ r‖ ≤ EbM τ * Real.exp (-(κdec - 1) * treeLenCovOne (m₀) (jM τ) (XM τ)))
    -- the sizes of the old terms and of the observable terms (the source bounds of (3.2)-(3.4)):
    -- the bounds of the terms rooted at one site (resp. at one source site) add up to `ρ`
    (rE : τι → CTorus d L N₁ m₁ (k + 1)) (hrE : ∀ τ ∈ 𝒯E, rE τ ∈ X₁E τ) {ρE : ℝ} (hρE0 : 0 ≤ ρE)
    (hρE : ∀ x : CTorus d L N₁ m₁ (k + 1), ∑ τ ∈ 𝒯E.filter (fun τ => rE τ = x),
      EbE τ * Real.exp (-κ₀ * treeLenCovOne m₀ (jE τ) (XE τ)) ≤ ρE)
    {ρM : ℝ} (hρM0 : 0 ≤ ρM)
    (hρM : ∀ p : CTorus d L N₁ m₁ (k + 1) × Fin N, ∑ τ ∈ 𝒯M.filter (fun τ => (ys τ, is τ) = p),
      EbM τ * Real.exp (-κ₀ * treeLenCovOne m₀ (jM τ) (XM τ)) ≤ ρM) :
    ∃ (𝒴 : Finset (Set (CTorus d L N₁ m₁ (k + 1))))
      (T : Set (CTorus d L N₁ m₁ (k + 1)) →
        ((unitPts Gp × Fin N → ℂ) × (unitPts Gp × Fin N → ℂ)) →
        ((unitPts Gp × Fin N → ℂ) × (unitPts Gp × Fin N → ℂ)) → ℂ →
        RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ),
      LocIntDm (IsDj m₀ (k + 1)) (fun ψ : unitPts Gp × Fin N → ℂ => (ψ, ψ))
        (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ l1BallEta d L N₁ m₁ (k + 1) N η)
        {xw : ((unitPts Gp × Fin N → ℂ) × (unitPts Gp × Fin N → ℂ)) ×
            ((unitPts Gp × Fin N → ℂ) × (unitPts Gp × Fin N → ℂ)) |
          (xw.1.1, xw.2.1) ∈ HatRaysO Gp cψ R₁ Rσ r ∧ (xw.1.2, xw.2.2) ∈ HatRaysO Gp cψ R₁ Rσ r}
        Rσ 𝒴 T
        (fun x w σ p =>
          (-cβ) * raySrc3 (hatFun Gp a₁ ν eps hG' cc (interactionOne hG hG' le_rfl a₁ ν eps))
            taylorWeight x.1 w.1 σ p.1 +
          cβ * (∑ τ ∈ 𝒯E, if h : τ ∈ 𝒯E then
            dirTermSrc (hatFun Gp a₁ ν eps hG' cc (flComp (hBE τ h) (hFE τ h) (EE τ)))
              (fun _ => (1 : ℂ)) x.1 w.1 σ p.1 else 0) +
          cβ * (∑ s : CTorus d L N₁ m₁ (k + 1) × Fin N, p.2 s.1 s.2 *
            dirTermSrc (hatFun Gp a₁ ν eps hG' cc (onXi Gp a₁ ν eps
              (fun D ψ' => svec Hm (flFieldOne Gp Hm BG₂ κ a₁ ν D ψ') s.1 s.2)))
              (fun _ => (1 : ℂ)) x.2 w.2 σ p.1) +
          cβ * (∑ τ ∈ 𝒯M, if h : τ ∈ 𝒯M then
            p.2 (ys τ) (is τ) * dirTermSrc (hatFun Gp a₁ ν eps hG' cc
              (flComp (hBM τ h) (hFM τ h) (EM τ))) (fun _ => (1 : ℂ)) x.2 w.2 σ p.1 else 0))
        (fun Y => prop33EpsEtaScaled d L N m₁ k m₀ a₁ BG BG₂ κ δ₁ r ρE ρM η * ‖cβ‖ *
          Real.exp (-(2 * κdec - 1) * treeLenCovOne m₀ (k + 1) Y))
        (fun Y p p' => agreeOn Y p.1 p'.1 ∧ ∀ x ∈ Y, p.2 x = p'.2 x)
        (fun Y a a' => AgHatFDir hG' Y a.1 a'.1 ∧ AgHatFDir hG' Y a.2 a'.2) := by
  classical
  exact (interaction_expansion_hat_bound_dm_dir_eta_scaled_ray (Kc := Kc) (Cx := Cx) (c₂ := c₂) (BG₂ := BG₂) (δ₁ := δ₁) hC cβ hconn hrow (κdec := κdec) (κ₀ := κ₀) hκ₀ hκdec hκ h1 (R₁ := R₁) hR₁ (r := r) (Rσ := Rσ) hr (η := η) hη0 hk hG hG' cc (cψ := cψ) hcψ hMX (δc := δc) hdm hα hsmX hδ₁ ha₁ H hc7 (R := R) hR hRs hsmall hnum hnum' hreal (m₀ := m₀) (jV := jV) (XV := XV) (𝒦XV := 𝒦XV) (X₁V := X₁V) hcovV hX₁V hoptV hΔV hlogV hZV hmarV (τι := τι) 𝒯E (ϱ₁ := ϱ₁) (ϱ₂ := ϱ₂) (GkE := GkE) (GjE := GjE) (r₀ := r₀) (δ₃ := δ₃) (δfl := δfl) (X₀E := X₀E) (X₁E := X₁E) (jE := jE) (XE := XE) (𝒦XE := 𝒦XE) (EbE := EbE) hBE hFE hcovE hX₁E hoptE hlogE hEbE (EE := EE) hEanE hEbdE (jF := jF) (XF := XF) (𝒦XF := 𝒦XF) (X₁F := X₁F) hcovF hX₁F hoptF hΔF hlogF hyF (μι := μι) 𝒯M (ϱ₁M := ϱ₁M) (ϱ₂M := ϱ₂M) (GkM := GkM) (GjM := GjM) (X₀M := X₀M) (X₁M := X₁M) (jM := jM) (XM := XM) (𝒦XM := 𝒦XM) (EbM := EbM) ys is hys hBM hFM hcovM hX₁M hoptM hlogM hEbM (EM := EM) hEanM hEbdM rE hrE (ρE := ρE) hρE0 hρE (ρM := ρM) hρM0 hρM).imp fun _ => Exists.imp fun _ h => h.1

/-- **Ray-differentiable form of `interaction_expansion_hat_dm_core_dir_eta_scaled`.**  The statement of `interaction_expansion_hat_dm_core_dir_eta_scaled` together with the
differentiability of the terms along the complex hat ray `z ↦ z • ψ̂` on `‖z‖ < 3/2`.
The last two conjuncts: the labels are those of the four parts and of the `ν`-part, and at zero
source, for `cν = 0`, on labels outside the old-term and observable label sets, the term is the
potential part, as in `interaction_expansion_hat_bound_dm_dir_eta_scaled_ray`. -/
theorem interaction_expansion_hat_dm_core_dir_eta_scaled_ray {Kc Cx c₂ BG₂ δ₁ : ℝ}
    (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (cβ : ℂ)
    (hconn : HatConn Gp) (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    {R₁ : ℝ} (hR₁ : 1 < R₁) {r Rσ : ℝ} (hr : 0 < r)
    {η : ℝ} (hη0 : 0 < η)
    -- the hat variable
    (hk : 1 ≤ k) (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsmX : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    -- the potential part
    (ha₁ : 0 < a₁)
    (H : BgHyp d L (k + 1) ϱm (compWeight L a₁) ν) (hc7 : c7 d L N BG κ ≤ thm73C3 d L N)
    {R : ℝ} (hR : 2 ≤ R) (hRs : R * δ₁ ≤ deltaStar d L N)
    (hsmall : cK2 d L N * (R * δ₁) < bgC0 d L N / 2)
    (hnum : cK2 d L N * δ₁ ≤ c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hnum' : cK2' d L N (famConst d L BG₂ κ) * δ₁ ≤
      c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hsm : 2 * (compC4 d * (bgK1 d L N * (xiC1 d * eps))) + 5 * (R * δ₁) ≤ bgC1 d L N)
    {m₀ : ℕ} {jV : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → ℕ}
    {XV 𝒦XV : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Set (CTorus d L N₁ m₁ (k + 1))}
    {X₁V : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Finset (CTorus d L N₁ m₁ (k + 1))}
    (hcovV : ∀ z, CovSetup Gp (m₀) (jV z) (XV z) (𝒦XV z))
    (hX₁V : ∀ z, (↑(X₁V z) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp (m₀) (jV z) (𝒦XV z))
    (hoptV : ∀ z, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XV z) ∧ MeetsOne (m₀) (jV z) (𝒦XV z) W₀ ∧
        bondCost (scaleW L (m₀) m₁ (jV z)) E₀ = treeLenCovOne (m₀) (jV z) (XV z))
    (hΔV : ∀ z, treeLenCovOne (m₀) (jV z) (XV z) = 0)
    (hlogV : ∀ _z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))), Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤
      (κ / 2 - 1) / 2)
    (hZV : ∀ z, readSites Hm k z ⊆ ↑(X₁V z))
    (hmarV : ∀ z, BlockMargin Gp (X₁V z)
      (↑(blockSites d L N₁ m₁ (k + 1) k z) : Set (CTorus d L N₁ m₁ (k + 1))))
    -- the old terms
    {τι : Type*} [DecidableEq τι] (𝒯E : Finset τι) {ϱ₁ ϱ₂ : τι → ℝ}
    {GkE : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₁ τ)}
    {GjE : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₂ τ)} {r₀ δ₃ δfl : ℝ}
    {X₀E X₁E : τι → Finset (CTorus d L N₁ m₁ (k + 1))} {jE : τι → ℕ}
    {XE 𝒦XE : τι → Set (CTorus d L N₁ m₁ (k + 1))} {EbE : τι → ℝ}
    (hBE : ∀ τ ∈ 𝒯E, BgSetting N Gp (GkE τ) (GjE τ) a₁ ν c BG κ r₀ eps δ₃ (X₀E τ) (X₁E τ) (jE τ))
    (hFE : ∀ τ ∈ 𝒯E, FlSetting N Gp (GkE τ) Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl (X₁E τ))
    (hcovE : ∀ τ ∈ 𝒯E, CovSetup Gp (m₀) (jE τ) (XE τ) (𝒦XE τ))
    (hX₁E : ∀ τ ∈ 𝒯E, (↑(X₁E τ) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp (m₀) (jE τ) (𝒦XE τ))
    (hoptE : ∀ τ ∈ 𝒯E, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XE τ) ∧ MeetsOne (m₀) (jE τ) (𝒦XE τ) W₀ ∧
        bondCost (scaleW L (m₀) m₁ (jE τ)) E₀ = treeLenCovOne (m₀) (jE τ) (XE τ))
    (hlogE : ∀ τ ∈ 𝒯E, Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) *
      (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hEbE : ∀ τ ∈ 𝒯E, 0 ≤ EbE τ) {EE : τι → RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ}
    (hEanE : ∀ τ ∈ 𝒯E, AnalyticOnNhd ℂ (EE τ) (XiCRaw (GjE τ) (compWeight L a₁) ν (jE τ)
      (scaledC0 d) (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)))
    (hEbdE : ∀ τ ∈ 𝒯E, ∀ r ∈ XiCRaw (GjE τ) (compWeight L a₁) ν (jE τ) (scaledC0 d)
      (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      ‖EE τ r‖ ≤ EbE τ * Real.exp (-(κdec - 1) * treeLenCovOne (m₀) (jE τ) (XE τ)))
    -- the sites of the source
    {jF : CTorus d L N₁ m₁ (k + 1) × Fin N → ℕ}
    {XF 𝒦XF : CTorus d L N₁ m₁ (k + 1) × Fin N → Set (CTorus d L N₁ m₁ (k + 1))}
    {X₁F : CTorus d L N₁ m₁ (k + 1) × Fin N → Finset (CTorus d L N₁ m₁ (k + 1))}
    (hcovF : ∀ s, CovSetup Gp (m₀) (jF s) (XF s) (𝒦XF s))
    (hX₁F : ∀ s, (↑(X₁F s) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp (m₀) (jF s) (𝒦XF s))
    (hoptF : ∀ s, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XF s) ∧ MeetsOne (m₀) (jF s) (𝒦XF s) W₀ ∧
        bondCost (scaleW L (m₀) m₁ (jF s)) E₀ = treeLenCovOne (m₀) (jF s) (XF s))
    (hΔF : ∀ s, treeLenCovOne (m₀) (jF s) (XF s) = 0)
    (hlogF : ∀ _s : CTorus d L N₁ m₁ (k + 1) × Fin N, Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤
      (κ / 2 - 1) / 2)
    (hyF : ∀ s : CTorus d L N₁ m₁ (k + 1) × Fin N, s.1 ∈ X₁F s)
    -- the observable terms
    {μι : Type*} [DecidableEq μι] (𝒯M : Finset μι) {ϱ₁M ϱ₂M : μι → ℝ}
    {GkM : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₁M τ)}
    {GjM : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₂M τ)}
    {X₀M X₁M : μι → Finset (CTorus d L N₁ m₁ (k + 1))} {jM : μι → ℕ}
    {XM 𝒦XM : μι → Set (CTorus d L N₁ m₁ (k + 1))} {EbM : μι → ℝ}
    (ys : μι → CTorus d L N₁ m₁ (k + 1)) (is : μι → Fin N) (hys : ∀ τ ∈ 𝒯M, ys τ ∈ X₁M τ)
    (hBM : ∀ τ ∈ 𝒯M, BgSetting N Gp (GkM τ) (GjM τ) a₁ ν c BG κ r₀ eps δ₃ (X₀M τ) (X₁M τ) (jM τ))
    (hFM : ∀ τ ∈ 𝒯M, FlSetting N Gp (GkM τ) Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl (X₁M τ))
    (hcovM : ∀ τ ∈ 𝒯M, CovSetup Gp (m₀) (jM τ) (XM τ) (𝒦XM τ))
    (hX₁M : ∀ τ ∈ 𝒯M, (↑(X₁M τ) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp (m₀) (jM τ) (𝒦XM τ))
    (hoptM : ∀ τ ∈ 𝒯M, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XM τ) ∧ MeetsOne (m₀) (jM τ) (𝒦XM τ) W₀ ∧
        bondCost (scaleW L (m₀) m₁ (jM τ)) E₀ = treeLenCovOne (m₀) (jM τ) (XM τ))
    (hlogM : ∀ τ ∈ 𝒯M, Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) *
      (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hEbM : ∀ τ ∈ 𝒯M, 0 ≤ EbM τ) {EM : μι → RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ}
    (hEanM : ∀ τ ∈ 𝒯M, AnalyticOnNhd ℂ (EM τ) (XiCRaw (GjM τ) (compWeight L a₁) ν (jM τ)
      (scaledC0 d) (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)))
    (hEbdM : ∀ τ ∈ 𝒯M, ∀ r ∈ XiCRaw (GjM τ) (compWeight L a₁) ν (jM τ) (scaledC0 d)
      (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      ‖EM τ r‖ ≤ EbM τ * Real.exp (-(κdec - 1) * treeLenCovOne (m₀) (jM τ) (XM τ)))
    -- the sizes of the old terms and of the observable terms (the source bounds of (3.2)-(3.4)):
    -- the bounds of the terms rooted at one site (resp. at one source site) add up to `ρ`
    (rE : τι → CTorus d L N₁ m₁ (k + 1)) (hrE : ∀ τ ∈ 𝒯E, rE τ ∈ X₁E τ) {ρE : ℝ} (hρE0 : 0 ≤ ρE)
    (hρE : ∀ x : CTorus d L N₁ m₁ (k + 1), ∑ τ ∈ 𝒯E.filter (fun τ => rE τ = x),
      EbE τ * Real.exp (-κ₀ * treeLenCovOne m₀ (jE τ) (XE τ)) ≤ ρE)
    {ρM : ℝ} (hρM0 : 0 ≤ ρM)
    (hρM : ∀ p : CTorus d L N₁ m₁ (k + 1) × Fin N, ∑ τ ∈ 𝒯M.filter (fun τ => (ys τ, is τ) = p),
      EbM τ * Real.exp (-κ₀ * treeLenCovOne m₀ (jM τ) (XM τ)) ≤ ρM)
    -- the `ν`-part: the bound on the external field and the block margin of the blocks
    {Bh : ℝ} (hBh0 : 0 ≤ Bh)
    (hBh : ∀ D : BgData Gp N, XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D →
      ∀ x i, ‖D.h x i‖ ≤ Bh) (cν : ℂ)
    (hZν : ∀ z, (↑(blockSites d L N₁ m₁ (k + 1) k z) : Set (CTorus d L N₁ m₁ (k + 1))) ⊆ ↑(X₁V z)) :
    ∃ (𝒴 : Finset (Set (CTorus d L N₁ m₁ (k + 1))))
      (T : Set (CTorus d L N₁ m₁ (k + 1)) →
        ((unitPts Gp × Fin N → ℂ) × (unitPts Gp × Fin N → ℂ)) →
        ((unitPts Gp × Fin N → ℂ) × (unitPts Gp × Fin N → ℂ)) → ℂ →
        RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ),
      LocIntDm (IsDj m₀ (k + 1)) (fun ψ : unitPts Gp × Fin N → ℂ => (ψ, ψ))
        (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ l1BallEta d L N₁ m₁ (k + 1) N η)
        {xw : ((unitPts Gp × Fin N → ℂ) × (unitPts Gp × Fin N → ℂ)) ×
            ((unitPts Gp × Fin N → ℂ) × (unitPts Gp × Fin N → ℂ)) |
          (xw.1.1, xw.2.1) ∈ HatRaysO Gp cψ R₁ Rσ r ∧ (xw.1.2, xw.2.2) ∈ HatRaysO Gp cψ R₁ Rσ r}
        Rσ 𝒴 T
        (fun x w σ p =>
          (-cβ) * raySrc3 (hatFun Gp a₁ ν eps hG' cc (interactionOne hG hG' le_rfl a₁ ν eps))
            taylorWeight x.1 w.1 σ p.1 +
          cβ * (∑ τ ∈ 𝒯E, if h : τ ∈ 𝒯E then
            dirTermSrc (hatFun Gp a₁ ν eps hG' cc (flComp (hBE τ h) (hFE τ h) (EE τ)))
              (fun _ => (1 : ℂ)) x.1 w.1 σ p.1 else 0) +
          cβ * (∑ s : CTorus d L N₁ m₁ (k + 1) × Fin N, p.2 s.1 s.2 *
            dirTermSrc (hatFun Gp a₁ ν eps hG' cc (onXi Gp a₁ ν eps
              (fun D ψ' => svec Hm (flFieldOne Gp Hm BG₂ κ a₁ ν D ψ') s.1 s.2)))
              (fun _ => (1 : ℂ)) x.2 w.2 σ p.1) +
          cβ * (∑ τ ∈ 𝒯M, if h : τ ∈ 𝒯M then
            p.2 (ys τ) (is τ) * dirTermSrc (hatFun Gp a₁ ν eps hG' cc
              (flComp (hBM τ h) (hFM τ h) (EM τ))) (fun _ => (1 : ℂ)) x.2 w.2 σ p.1 else 0) +
          cν * dirTermSrc (hatFun Gp a₁ ν eps hG' cc (onXi Gp a₁ ν eps
            (fun D ψ' => nuTotal Gp Hm a₁ ν BG₂ κ D ψ'))) (fun _ => (1 : ℂ)) x.1 w.1 σ p.1)
        (fun Y => prop33EpsEtaScaled d L N m₁ k m₀ a₁ BG BG₂ κ δ₁ r ρE ρM η * ‖cβ‖ *
          Real.exp (-(2 * κdec - 1) * treeLenCovOne m₀ (k + 1) Y) +
          ‖cν‖ * (1 * (c1 d L * ((L : ℝ) ^ (m₀ + m₁)) ^ d *
            nuBd d L N k (cK2' d L N (famConst d L BG₂ κ) * δ₁)
              (K4 d L N BG κ * (xiC1 d * eps) + (1 + 3 * (xiC1 d * eps)) + Bh) / r) *
            Real.exp (-(2 * κdec - 1) * treeLenCovOne m₀ (k + 1) Y)))
        (fun Y p p' => agreeOn Y p.1 p'.1 ∧ ∀ x ∈ Y, p.2 x = p'.2 x)
        (fun Y a a' => AgHatFDir hG' Y a.1 a'.1 ∧ AgHatFDir hG' Y a.2 a'.2)
      ∧ (∀ (Y : Set (CTorus d L N₁ m₁ (k + 1)))
          (q : RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)),
        q ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ l1BallEta d L N₁ m₁ (k + 1) N η →
        ∀ ψ : unitPts Gp × Fin N → ℂ, (∀ p, (R₁ + r) * (3 / 2) * ‖ψ p‖ ≤ cψ) →
        DifferentiableOn ℂ (fun ζ : ℂ => T Y (ζ • ψ, ζ • ψ) (ζ • ψ, ζ • ψ) 1 q)
          (ball (0 : ℂ) (3 / 2))) ∧
      𝒴 = (Finset.univ.biUnion fun z => polyDom Gp (X₁V z) m₀ (jV z) (𝒦XV z)) ∪
          (𝒯E.biUnion fun τ => polyDom Gp (X₁E τ) m₀ (jE τ) (𝒦XE τ)) ∪
          (Finset.univ.biUnion fun s => polymerDomains
            (fun i : ParIdx Gp (↑(X₁F s) : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) Gp m₀
            (X1 Gp m₀ (jF s) (𝒦XF s))) ∪
          (𝒯M.biUnion fun τ => polyDom Gp (X₁M τ) m₀ (jM τ) (𝒦XM τ)) ∪
          (Finset.univ.biUnion fun z => polyDom Gp (X₁V z) m₀ (jV z) (𝒦XV z)) ∧
      ∃ (F₁ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
            DecParams Gp × RawData d L (N₁ * L ^ m₁) (k + 1) N → (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ))
          (Sol : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
            Dec2.DecParams (coverOf Gp) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)),
        (∀ z (s : DecParams Gp) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
          InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
            (α : Gp.Ω 1 → ℂ), IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
            F₁ z (s, rawOf D) = (φ, α)) ∧
        (∀ z (p : Dec2.DecParams (coverOf Gp) × Edat Hm N), (∀ P, ‖p.1 P‖ < Real.exp κ) →
          StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
            (Sol z p).1 = dphi Hm (Dec2.decG (coverOf Gp) Hm (compWeight L a₁) ν p.1) p.2.2.1 p.2.1
              (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol z p).2 ∧
            Dec2.DecFixed (coverOf Gp) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
              (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol z p).2 ∧
            Small Hm (Sol z p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
            Small Hm (Sol z p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
            SupBounds Hm (Sol z p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
            (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
              Dec2.DecFixed (coverOf Gp) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
                (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol z p).2)) ∧
        (∀ (Y : Set (CTorus d L N₁ m₁ (k + 1)))
          (x w : (unitPts Gp × Fin N → ℂ) × (unitPts Gp × Fin N → ℂ)) (σ : ℂ)
          (Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N),
          cν = 0 →
          Y ∉ 𝒯E.biUnion (fun τ => polyDom Gp (X₁E τ) m₀ (jE τ) (𝒦XE τ)) →
          Y ∉ 𝒯M.biUnion (fun τ => polyDom Gp (X₁M τ) m₀ (jM τ) (𝒦XM τ)) →
          T Y x w σ (Θ, 0) = -cβ *
            ∑ z, if Y ∈ polyDom Gp (X₁V z) m₀ (jV z) (𝒦XV z) then
              rayTerm (dl3 (evTerm
                (fun i : ParIdx Gp (↑(X₁V z) : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) Gp m₀
                (X1 Gp m₀ (jV z) (𝒦XV z))
                (fun u s => blockEnergyFun Gp Hm (compWeight L a₁) ν k z
                  (F₁ z (extParams Gp (↑(X₁V z) : Set (CTorus d L N₁ m₁ (k + 1))) s, u.1))
                  (Sol z (extParams Gp (↑(X₁V z) : Set (CTorus d L N₁ m₁ (k + 1))) s,
                    flEdat Gp Hm (F₁ z (extParams Gp (↑(X₁V z) : Set (CTorus d L N₁ m₁ (k + 1))) s, u.1))
                      u.1.1 (hatPsiF Gp a₁ ν hG' cc (F₁ z)
                        (extParams Gp (↑(X₁V z) : Set (CTorus d L N₁ m₁ (k + 1))) s) u.1 u.2))).1
                  (u.1, hatPsiF Gp a₁ ν hG' cc (F₁ z)
                    (extParams Gp (↑(X₁V z) : Set (CTorus d L N₁ m₁ (k + 1))) s) u.1 u.2)) Y) w.1) taylorWeight x.1 σ Θ
            else 0) ∧
      ∃ (F₂ : CTorus d L N₁ m₁ (k + 1) × Fin N →
            DecParams Gp × RawData d L (N₁ * L ^ m₁) (k + 1) N →
              (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ))
          (Sol₂ : CTorus d L N₁ m₁ (k + 1) × Fin N →
            Dec2.DecParams (coverOf Gp) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)),
        (∀ (a : CTorus d L N₁ m₁ (k + 1) × Fin N) (s : DecParams Gp) (D : BgData Gp N),
          (∀ P, ‖s P‖ < Real.exp κ) →
          InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
            (α : Gp.Ω 1 → ℂ), IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
            F₂ a (s, rawOf D) = (φ, α)) ∧
        (∀ (a : CTorus d L N₁ m₁ (k + 1) × Fin N) (p : Dec2.DecParams (coverOf Gp) × Edat Hm N),
          (∀ P, ‖p.1 P‖ < Real.exp κ) →
          StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
            (Sol₂ a p).1 = dphi Hm (Dec2.decG (coverOf Gp) Hm (compWeight L a₁) ν p.1) p.2.2.1 p.2.1
              (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol₂ a p).2 ∧
            Dec2.DecFixed (coverOf Gp) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
              (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol₂ a p).2 ∧
            Small Hm (Sol₂ a p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
            Small Hm (Sol₂ a p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
            SupBounds Hm (Sol₂ a p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
            (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
              Dec2.DecFixed (coverOf Gp) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
                (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol₂ a p).2)) ∧
        ∀ (Y : Set (CTorus d L N₁ m₁ (k + 1)))
          (x w : (unitPts Gp × Fin N → ℂ) × (unitPts Gp × Fin N → ℂ)) (σ : ℂ)
          (Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N)
          (g : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ),
          Y ∉ 𝒯M.biUnion (fun τ => polyDom Gp (X₁M τ) m₀ (jM τ) (𝒦XM τ)) →
          T Y x w σ (Θ, g) = T Y x w σ (Θ, 0) + cβ *
            ∑ s : CTorus d L N₁ m₁ (k + 1) × Fin N,
              if Y ∈ polyDom Gp (X₁F s) m₀ (jF s) (𝒦XF s) then
                g s.1 s.2 * dirTerm (evTerm
                  (fun i : ParIdx Gp (↑(X₁F s) : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) Gp m₀
                  (X1 Gp m₀ (jF s) (𝒦XF s))
                  (fun u t => siteFun Gp Hm s.1 s.2
                    (F₂ s (extParams Gp (↑(X₁F s) : Set (CTorus d L N₁ m₁ (k + 1))) t, u.1))
                    (Sol₂ s (extParams Gp (↑(X₁F s) : Set (CTorus d L N₁ m₁ (k + 1))) t,
                      flEdat Gp Hm
                        (F₂ s (extParams Gp (↑(X₁F s) : Set (CTorus d L N₁ m₁ (k + 1))) t, u.1))
                        u.1.1 (hatPsiF Gp a₁ ν hG' cc (F₂ s)
                          (extParams Gp (↑(X₁F s) : Set (CTorus d L N₁ m₁ (k + 1))) t) u.1 u.2))).1
                    (u.1, hatPsiF Gp a₁ ν hG' cc (F₂ s)
                      (extParams Gp (↑(X₁F s) : Set (CTorus d L N₁ m₁ (k + 1))) t) u.1 u.2)) Y)
                  (fun _ => (1 : ℂ)) x.2 w.2 σ Θ
              else 0 := by
  classical
  have hreal := hreal_level hC hG hG' le_rfl ha₁ H hc7 (by linarith) hsm
  obtain ⟨𝒴, T, hL, hrayL, h𝒴, F₁, Sol, hF₁, hSol, hT0, F₂, Sol₂, hF₂, hSol₂, hTg⟩ :=
    interaction_expansion_hat_bound_dm_dir_eta_scaled_ray (Rσ := Rσ) hC cβ hconn hrow hκ₀ hκdec hκ h1
    hR₁ hr hη0 hk hG hG' cc hcψ hMX hdm hα hsmX hδ₁ ha₁ H hc7 hR hRs hsmall hnum hnum' hreal hcovV
    hX₁V hoptV hΔV hlogV hZV hmarV 𝒯E hBE hFE hcovE hX₁E hoptE hlogE hEbE hEanE hEbdE hcovF hX₁F
    hoptF hΔF hlogF hyF 𝒯M ys is hys hBM hFM hcovM hX₁M hoptM hlogM hEbM hEanM hEbdM rE hrE hρE0
    hρE hρM0 hρM
  have hd : 3 ≤ d := hC.HBp.hd
  have hd0 : 0 < d := by omega
  have hL0' : 0 ≤ c1 d L := by unfold c1; positivity
  have hB0 : 0 ≤ famConst d L BG₂ κ := by
    have := famConst_ge_one (L := L) hC.hS2.fam.2.1 κ hd0; linarith
  have hK2 : 0 ≤ cK2' d L N (famConst d L BG₂ κ) * δ₁ :=
    mul_nonneg (cK2'_nonneg hB0) hC.δ₁_pos.le
  have hM0 : 0 ≤ ((L : ℝ) ^ (m₀ + m₁)) ^ d := by positivity
  -- the `ν`-part
  obtain ⟨Tν, hν, hrayν⟩ := nupart_locInt_bound_hat_dm_dir_ray (m₀ := m₀) (j := jV) (X := XV) (𝒦X := 𝒦XV)
    (X₁z := X₁V) hC hk hG hG' cc hcψ hMX hdm hα hsmX hδ₁ hBh0 hBh hcovV hX₁V hconn hrow hoptV hΔV
    hκ₀ hκdec hκ h1 (hlogV 0) hZν (ω := fun _ => (1 : ℂ)) continuous_const hR₁
    analyticOnNhd_const (Mω := 1) zero_le_one (fun t ht => by simp) hr (Rσ := Rσ)
  obtain ⟨T', hT', hrayT', hT'eq⟩ := LocIntDm.addLift_ray (SG := l1BallEta d L N₁ m₁ (k + 1) N η) (π := Prod.fst)
    (Rσ := Rσ) (F := unitPts Gp × Fin N → ℂ)
    (F' := (unitPts Gp × Fin N → ℂ) × (unitPts Gp × Fin N → ℂ))
    (AgG := fun Y (g g' : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) => ∀ x ∈ Y, g x = g' x)
    (AgF' := fun Y a a' => AgHatFDir hG' Y a.1 a'.1 ∧ AgHatFDir hG' Y a.2 a'.2)
    (fun xw hxw => hxw.1) (fun Y a a' h => h.1) (fun _ => rfl) hν hL cν
    (P' := fun u => ∃ ψ : unitPts Gp × Fin N → ℂ, (∀ p, (R₁ + r) * (3 / 2) * ‖ψ p‖ ≤ cψ) ∧
      u = fun ζ : ℂ => (ζ • ψ, ζ • ψ)) (s := ball (0 : ℂ) (3 / 2))
    (fun Y u hu q hq => by obtain ⟨ψ, hψ, rfl⟩ := hu; exact hrayL Y q hq ψ hψ)
    (fun Y u hu Θ hΘ => by obtain ⟨ψ, hψ, rfl⟩ := hu; exact hrayν Y Θ hΘ ψ hψ)
  have hEps : 0 ≤ prop33EpsEtaScaled d L N m₁ k m₀ a₁ BG BG₂ κ δ₁ r ρE ρM η := by
    unfold prop33EpsEtaScaled; positivity
  have hnu0 : 0 ≤ nuBd d L N k (cK2' d L N (famConst d L BG₂ κ) * δ₁)
      (K4 d L N BG κ * (xiC1 d * eps) + (1 + 3 * (xiC1 d * eps)) + Bh) := by
    have hK4 : 0 < K4 d L N BG κ := K4_pos (L := L) (N := N) (κ := κ) hC.hS.fam.2.1 hd0
    have hx1 := one_le_xiC1 d
    have hx2 := hC.eps_pos
    have hx3 : 0 ≤ xiC1 d * eps := by positivity
    have hx4 := mul_nonneg hK4.le hx3
    unfold nuBd
    have : 0 ≤ K4 d L N BG κ * (xiC1 d * eps) + (1 + 3 * (xiC1 d * eps)) + Bh := by linarith
    positivity
  refine ⟨_, _, (hT'.congr_val ?_).mono fun Y => ?_,
    fun Y q hq ψ hψ => hrayT' Y (fun ζ => (ζ • ψ, ζ • ψ)) ⟨ψ, hψ, rfl⟩ q hq, by rw [h𝒴],
    F₁, Sol, hF₁, hSol, ?_, F₂, Sol₂, hF₂, hSol₂, ?_⟩
  · intro xw hxw σ hσ p hp'
    rfl
  · have hb1 : 0 ≤ prop33EpsEtaScaled d L N m₁ k m₀ a₁ BG BG₂ κ δ₁ r ρE ρM η * ‖cβ‖ *
        Real.exp (-(2 * κdec - 1) * treeLenCovOne m₀ (k + 1) Y) := by positivity
    have hb2 : 0 ≤ ‖cν‖ * (1 * (c1 d L * ((L : ℝ) ^ (m₀ + m₁)) ^ d *
            nuBd d L N k (cK2' d L N (famConst d L BG₂ κ) * δ₁)
              (K4 d L N BG κ * (xiC1 d * eps) + (1 + 3 * (xiC1 d * eps)) + Bh) / r) *
            Real.exp (-(2 * κdec - 1) * treeLenCovOne m₀ (k + 1) Y)) := by positivity
    split_ifs <;> simp only [one_mul] at * <;> linarith
  · intro Y x w σ Θ hν hYE hYM
    subst hT'eq hν
    dsimp only
    rw [zero_mul, ite_self, add_zero]
    by_cases hY : Y ∈ 𝒴
    · rw [ite_eq_left hY]
      exact hT0 Y x w σ Θ hYE hYM
    · rw [ite_eq_right hY, Finset.sum_eq_zero, mul_zero]
      intro z _
      refine ite_eq_right fun h => hY ?_
      rw [h𝒴]
      exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_biUnion.2 ⟨z, Finset.mem_univ _, h⟩)))
  · intro Y x w σ Θ g hYM
    subst hT'eq
    dsimp only
    by_cases hY : Y ∈ 𝒴
    · rw [ite_eq_left hY, ite_eq_left hY, hTg Y x w σ Θ g hYM]
      ring
    · rw [ite_eq_right hY, ite_eq_right hY, Finset.sum_eq_zero]
      · ring
      · intro s _
        refine ite_eq_right fun h => hY ?_
        rw [h𝒴]
        exact Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_biUnion.2 ⟨s, Finset.mem_univ _, h⟩))

/-- **Proposition 3.3 in the variable `ψ̂`, with the sharp agreement relation.**  The statement of
`interaction_expansion_hat_dm` with `AgHatF` replaced by `AgHatFDir`: the terms are local in the
hat variable for equality at the unit points of the sites of the label `Y` itself. -/
theorem interaction_expansion_hat_dm_core_dir_eta_scaled {Kc Cx c₂ BG₂ δ₁ : ℝ}
    (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (cβ : ℂ)
    (hconn : HatConn Gp) (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    {R₁ : ℝ} (hR₁ : 1 < R₁) {r Rσ : ℝ} (hr : 0 < r)
    {η : ℝ} (hη0 : 0 < η)
    -- the hat variable
    (hk : 1 ≤ k) (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsmX : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    -- the potential part
    (ha₁ : 0 < a₁)
    (H : BgHyp d L (k + 1) ϱm (compWeight L a₁) ν) (hc7 : c7 d L N BG κ ≤ thm73C3 d L N)
    {R : ℝ} (hR : 2 ≤ R) (hRs : R * δ₁ ≤ deltaStar d L N)
    (hsmall : cK2 d L N * (R * δ₁) < bgC0 d L N / 2)
    (hnum : cK2 d L N * δ₁ ≤ c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hnum' : cK2' d L N (famConst d L BG₂ κ) * δ₁ ≤
      c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hsm : 2 * (compC4 d * (bgK1 d L N * (xiC1 d * eps))) + 5 * (R * δ₁) ≤ bgC1 d L N)
    {m₀ : ℕ} {jV : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → ℕ}
    {XV 𝒦XV : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Set (CTorus d L N₁ m₁ (k + 1))}
    {X₁V : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Finset (CTorus d L N₁ m₁ (k + 1))}
    (hcovV : ∀ z, CovSetup Gp (m₀) (jV z) (XV z) (𝒦XV z))
    (hX₁V : ∀ z, (↑(X₁V z) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp (m₀) (jV z) (𝒦XV z))
    (hoptV : ∀ z, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XV z) ∧ MeetsOne (m₀) (jV z) (𝒦XV z) W₀ ∧
        bondCost (scaleW L (m₀) m₁ (jV z)) E₀ = treeLenCovOne (m₀) (jV z) (XV z))
    (hΔV : ∀ z, treeLenCovOne (m₀) (jV z) (XV z) = 0)
    (hlogV : ∀ _z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))), Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤
      (κ / 2 - 1) / 2)
    (hZV : ∀ z, readSites Hm k z ⊆ ↑(X₁V z))
    (hmarV : ∀ z, BlockMargin Gp (X₁V z)
      (↑(blockSites d L N₁ m₁ (k + 1) k z) : Set (CTorus d L N₁ m₁ (k + 1))))
    -- the old terms
    {τι : Type*} [DecidableEq τι] (𝒯E : Finset τι) {ϱ₁ ϱ₂ : τι → ℝ}
    {GkE : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₁ τ)}
    {GjE : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₂ τ)} {r₀ δ₃ δfl : ℝ}
    {X₀E X₁E : τι → Finset (CTorus d L N₁ m₁ (k + 1))} {jE : τι → ℕ}
    {XE 𝒦XE : τι → Set (CTorus d L N₁ m₁ (k + 1))} {EbE : τι → ℝ}
    (hBE : ∀ τ ∈ 𝒯E, BgSetting N Gp (GkE τ) (GjE τ) a₁ ν c BG κ r₀ eps δ₃ (X₀E τ) (X₁E τ) (jE τ))
    (hFE : ∀ τ ∈ 𝒯E, FlSetting N Gp (GkE τ) Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl (X₁E τ))
    (hcovE : ∀ τ ∈ 𝒯E, CovSetup Gp (m₀) (jE τ) (XE τ) (𝒦XE τ))
    (hX₁E : ∀ τ ∈ 𝒯E, (↑(X₁E τ) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp (m₀) (jE τ) (𝒦XE τ))
    (hoptE : ∀ τ ∈ 𝒯E, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XE τ) ∧ MeetsOne (m₀) (jE τ) (𝒦XE τ) W₀ ∧
        bondCost (scaleW L (m₀) m₁ (jE τ)) E₀ = treeLenCovOne (m₀) (jE τ) (XE τ))
    (hlogE : ∀ τ ∈ 𝒯E, Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) *
      (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hEbE : ∀ τ ∈ 𝒯E, 0 ≤ EbE τ) {EE : τι → RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ}
    (hEanE : ∀ τ ∈ 𝒯E, AnalyticOnNhd ℂ (EE τ) (XiCRaw (GjE τ) (compWeight L a₁) ν (jE τ)
      (scaledC0 d) (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)))
    (hEbdE : ∀ τ ∈ 𝒯E, ∀ r ∈ XiCRaw (GjE τ) (compWeight L a₁) ν (jE τ) (scaledC0 d)
      (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      ‖EE τ r‖ ≤ EbE τ * Real.exp (-(κdec - 1) * treeLenCovOne (m₀) (jE τ) (XE τ)))
    -- the sites of the source
    {jF : CTorus d L N₁ m₁ (k + 1) × Fin N → ℕ}
    {XF 𝒦XF : CTorus d L N₁ m₁ (k + 1) × Fin N → Set (CTorus d L N₁ m₁ (k + 1))}
    {X₁F : CTorus d L N₁ m₁ (k + 1) × Fin N → Finset (CTorus d L N₁ m₁ (k + 1))}
    (hcovF : ∀ s, CovSetup Gp (m₀) (jF s) (XF s) (𝒦XF s))
    (hX₁F : ∀ s, (↑(X₁F s) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp (m₀) (jF s) (𝒦XF s))
    (hoptF : ∀ s, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XF s) ∧ MeetsOne (m₀) (jF s) (𝒦XF s) W₀ ∧
        bondCost (scaleW L (m₀) m₁ (jF s)) E₀ = treeLenCovOne (m₀) (jF s) (XF s))
    (hΔF : ∀ s, treeLenCovOne (m₀) (jF s) (XF s) = 0)
    (hlogF : ∀ _s : CTorus d L N₁ m₁ (k + 1) × Fin N, Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤
      (κ / 2 - 1) / 2)
    (hyF : ∀ s : CTorus d L N₁ m₁ (k + 1) × Fin N, s.1 ∈ X₁F s)
    -- the observable terms
    {μι : Type*} [DecidableEq μι] (𝒯M : Finset μι) {ϱ₁M ϱ₂M : μι → ℝ}
    {GkM : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₁M τ)}
    {GjM : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₂M τ)}
    {X₀M X₁M : μι → Finset (CTorus d L N₁ m₁ (k + 1))} {jM : μι → ℕ}
    {XM 𝒦XM : μι → Set (CTorus d L N₁ m₁ (k + 1))} {EbM : μι → ℝ}
    (ys : μι → CTorus d L N₁ m₁ (k + 1)) (is : μι → Fin N) (hys : ∀ τ ∈ 𝒯M, ys τ ∈ X₁M τ)
    (hBM : ∀ τ ∈ 𝒯M, BgSetting N Gp (GkM τ) (GjM τ) a₁ ν c BG κ r₀ eps δ₃ (X₀M τ) (X₁M τ) (jM τ))
    (hFM : ∀ τ ∈ 𝒯M, FlSetting N Gp (GkM τ) Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl (X₁M τ))
    (hcovM : ∀ τ ∈ 𝒯M, CovSetup Gp (m₀) (jM τ) (XM τ) (𝒦XM τ))
    (hX₁M : ∀ τ ∈ 𝒯M, (↑(X₁M τ) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp (m₀) (jM τ) (𝒦XM τ))
    (hoptM : ∀ τ ∈ 𝒯M, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XM τ) ∧ MeetsOne (m₀) (jM τ) (𝒦XM τ) W₀ ∧
        bondCost (scaleW L (m₀) m₁ (jM τ)) E₀ = treeLenCovOne (m₀) (jM τ) (XM τ))
    (hlogM : ∀ τ ∈ 𝒯M, Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) *
      (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hEbM : ∀ τ ∈ 𝒯M, 0 ≤ EbM τ) {EM : μι → RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ}
    (hEanM : ∀ τ ∈ 𝒯M, AnalyticOnNhd ℂ (EM τ) (XiCRaw (GjM τ) (compWeight L a₁) ν (jM τ)
      (scaledC0 d) (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)))
    (hEbdM : ∀ τ ∈ 𝒯M, ∀ r ∈ XiCRaw (GjM τ) (compWeight L a₁) ν (jM τ) (scaledC0 d)
      (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      ‖EM τ r‖ ≤ EbM τ * Real.exp (-(κdec - 1) * treeLenCovOne (m₀) (jM τ) (XM τ)))
    -- the sizes of the old terms and of the observable terms (the source bounds of (3.2)-(3.4)):
    -- the bounds of the terms rooted at one site (resp. at one source site) add up to `ρ`
    (rE : τι → CTorus d L N₁ m₁ (k + 1)) (hrE : ∀ τ ∈ 𝒯E, rE τ ∈ X₁E τ) {ρE : ℝ} (hρE0 : 0 ≤ ρE)
    (hρE : ∀ x : CTorus d L N₁ m₁ (k + 1), ∑ τ ∈ 𝒯E.filter (fun τ => rE τ = x),
      EbE τ * Real.exp (-κ₀ * treeLenCovOne m₀ (jE τ) (XE τ)) ≤ ρE)
    {ρM : ℝ} (hρM0 : 0 ≤ ρM)
    (hρM : ∀ p : CTorus d L N₁ m₁ (k + 1) × Fin N, ∑ τ ∈ 𝒯M.filter (fun τ => (ys τ, is τ) = p),
      EbM τ * Real.exp (-κ₀ * treeLenCovOne m₀ (jM τ) (XM τ)) ≤ ρM)
    -- the `ν`-part: the bound on the external field and the block margin of the blocks
    {Bh : ℝ} (hBh0 : 0 ≤ Bh)
    (hBh : ∀ D : BgData Gp N, XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D →
      ∀ x i, ‖D.h x i‖ ≤ Bh) (cν : ℂ)
    (hZν : ∀ z, (↑(blockSites d L N₁ m₁ (k + 1) k z) : Set (CTorus d L N₁ m₁ (k + 1))) ⊆ ↑(X₁V z)) :
    ∃ (𝒴 : Finset (Set (CTorus d L N₁ m₁ (k + 1))))
      (T : Set (CTorus d L N₁ m₁ (k + 1)) →
        ((unitPts Gp × Fin N → ℂ) × (unitPts Gp × Fin N → ℂ)) →
        ((unitPts Gp × Fin N → ℂ) × (unitPts Gp × Fin N → ℂ)) → ℂ →
        RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ),
      LocIntDm (IsDj m₀ (k + 1)) (fun ψ : unitPts Gp × Fin N → ℂ => (ψ, ψ))
        (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ l1BallEta d L N₁ m₁ (k + 1) N η)
        {xw : ((unitPts Gp × Fin N → ℂ) × (unitPts Gp × Fin N → ℂ)) ×
            ((unitPts Gp × Fin N → ℂ) × (unitPts Gp × Fin N → ℂ)) |
          (xw.1.1, xw.2.1) ∈ HatRaysO Gp cψ R₁ Rσ r ∧ (xw.1.2, xw.2.2) ∈ HatRaysO Gp cψ R₁ Rσ r}
        Rσ 𝒴 T
        (fun x w σ p =>
          (-cβ) * raySrc3 (hatFun Gp a₁ ν eps hG' cc (interactionOne hG hG' le_rfl a₁ ν eps))
            taylorWeight x.1 w.1 σ p.1 +
          cβ * (∑ τ ∈ 𝒯E, if h : τ ∈ 𝒯E then
            dirTermSrc (hatFun Gp a₁ ν eps hG' cc (flComp (hBE τ h) (hFE τ h) (EE τ)))
              (fun _ => (1 : ℂ)) x.1 w.1 σ p.1 else 0) +
          cβ * (∑ s : CTorus d L N₁ m₁ (k + 1) × Fin N, p.2 s.1 s.2 *
            dirTermSrc (hatFun Gp a₁ ν eps hG' cc (onXi Gp a₁ ν eps
              (fun D ψ' => svec Hm (flFieldOne Gp Hm BG₂ κ a₁ ν D ψ') s.1 s.2)))
              (fun _ => (1 : ℂ)) x.2 w.2 σ p.1) +
          cβ * (∑ τ ∈ 𝒯M, if h : τ ∈ 𝒯M then
            p.2 (ys τ) (is τ) * dirTermSrc (hatFun Gp a₁ ν eps hG' cc
              (flComp (hBM τ h) (hFM τ h) (EM τ))) (fun _ => (1 : ℂ)) x.2 w.2 σ p.1 else 0) +
          cν * dirTermSrc (hatFun Gp a₁ ν eps hG' cc (onXi Gp a₁ ν eps
            (fun D ψ' => nuTotal Gp Hm a₁ ν BG₂ κ D ψ'))) (fun _ => (1 : ℂ)) x.1 w.1 σ p.1)
        (fun Y => prop33EpsEtaScaled d L N m₁ k m₀ a₁ BG BG₂ κ δ₁ r ρE ρM η * ‖cβ‖ *
          Real.exp (-(2 * κdec - 1) * treeLenCovOne m₀ (k + 1) Y) +
          ‖cν‖ * (1 * (c1 d L * ((L : ℝ) ^ (m₀ + m₁)) ^ d *
            nuBd d L N k (cK2' d L N (famConst d L BG₂ κ) * δ₁)
              (K4 d L N BG κ * (xiC1 d * eps) + (1 + 3 * (xiC1 d * eps)) + Bh) / r) *
            Real.exp (-(2 * κdec - 1) * treeLenCovOne m₀ (k + 1) Y)))
        (fun Y p p' => agreeOn Y p.1 p'.1 ∧ ∀ x ∈ Y, p.2 x = p'.2 x)
        (fun Y a a' => AgHatFDir hG' Y a.1 a'.1 ∧ AgHatFDir hG' Y a.2 a'.2) := by
  classical
  exact (interaction_expansion_hat_dm_core_dir_eta_scaled_ray (Kc := Kc) (Cx := Cx) (c₂ := c₂) (BG₂ := BG₂) (δ₁ := δ₁) hC cβ hconn hrow (κdec := κdec) (κ₀ := κ₀) hκ₀ hκdec hκ h1 (R₁ := R₁) hR₁ (r := r) (Rσ := Rσ) hr (η := η) hη0 hk hG hG' cc (cψ := cψ) hcψ hMX (δc := δc) hdm hα hsmX hδ₁ ha₁ H hc7 (R := R) hR hRs hsmall hnum hnum' hsm (m₀ := m₀) (jV := jV) (XV := XV) (𝒦XV := 𝒦XV) (X₁V := X₁V) hcovV hX₁V hoptV hΔV hlogV hZV hmarV (τι := τι) 𝒯E (ϱ₁ := ϱ₁) (ϱ₂ := ϱ₂) (GkE := GkE) (GjE := GjE) (r₀ := r₀) (δ₃ := δ₃) (δfl := δfl) (X₀E := X₀E) (X₁E := X₁E) (jE := jE) (XE := XE) (𝒦XE := 𝒦XE) (EbE := EbE) hBE hFE hcovE hX₁E hoptE hlogE hEbE (EE := EE) hEanE hEbdE (jF := jF) (XF := XF) (𝒦XF := 𝒦XF) (X₁F := X₁F) hcovF hX₁F hoptF hΔF hlogF hyF (μι := μι) 𝒯M (ϱ₁M := ϱ₁M) (ϱ₂M := ϱ₂M) (GkM := GkM) (GjM := GjM) (X₀M := X₀M) (X₁M := X₁M) (jM := jM) (XM := XM) (𝒦XM := 𝒦XM) (EbM := EbM) ys is hys hBM hFM hcovM hX₁M hoptM hlogM hEbM (EM := EM) hEanM hEbdM rE hrE (ρE := ρE) hρE0 hρE (ρM := ρM) hρM0 hρM (Bh := Bh) hBh0 hBh cν hZν).imp fun _ => Exists.imp fun _ h => h.1



end SharpAssemble

end Balaban.Localization

namespace Balaban.Fluctuation

open MeasureTheory Balaban Balaban.Localization Balaban.Multiscale Balaban.Polymer
  Balaban.Background Balaban.SmallField Balaban.Analysis Finset Matrix Set Metric

section SharpPhysical

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ eps : ℝ}

variable (S : StepSetting d L N₁ m₁ k N ϱ)
    {ρ εU : ℝ} {Kc Cx c₂ BG₂ δ₁ : ℝ}
    (hC : FlCore N S.G' Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (cβ : ℂ)
    (hconn : HatConn S.G') (hrow : RowInHat (coverOf S.G') Hm (compWeight L a₁) ν)
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    {R₁ : ℝ} (hR₁ : 1 < R₁) {r Rσ : ℝ} (hr : 0 < r)
    {η : ℝ} (hη0 : 0 < η)
    -- the hat variable
    (hk : 1 ≤ k) (hG : IsLevel Hm k) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsmX : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    -- the potential part
    (ha₁ : 0 < a₁)
    (H : BgHyp d L (k + 1) ϱm (compWeight L a₁) ν) (hc7 : c7 d L N BG κ ≤ thm73C3 d L N)
    {R : ℝ} (hR : 2 ≤ R) (hRs : R * δ₁ ≤ deltaStar d L N)
    (hsmall : cK2 d L N * (R * δ₁) < bgC0 d L N / 2)
    (hnum : cK2 d L N * δ₁ ≤ c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hnum' : cK2' d L N (famConst d L BG₂ κ) * δ₁ ≤
      c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hsm : 2 * (compC4 d * (bgK1 d L N * (xiC1 d * eps))) + 5 * (R * δ₁) ≤ bgC1 d L N)
    {m₀ : ℕ} {jV : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → ℕ}
    {XV 𝒦XV : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Set (CTorus d L N₁ m₁ (k + 1))}
    {X₁V : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Finset (CTorus d L N₁ m₁ (k + 1))}
    (hcovV : ∀ z, CovSetup S.G' (m₀) (jV z) (XV z) (𝒦XV z))
    (hX₁V : ∀ z, (↑(X₁V z) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 S.G' (m₀) (jV z) (𝒦XV z))
    (hoptV : ∀ z, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XV z) ∧ MeetsOne (m₀) (jV z) (𝒦XV z) W₀ ∧
        bondCost (scaleW L (m₀) m₁ (jV z)) E₀ = treeLenCovOne (m₀) (jV z) (XV z))
    (hΔV : ∀ z, treeLenCovOne (m₀) (jV z) (XV z) = 0)
    (hlogV : ∀ _z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))), Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤
      (κ / 2 - 1) / 2)
    (hZV : ∀ z, readSites Hm k z ⊆ ↑(X₁V z))
    (hmarV : ∀ z, BlockMargin S.G' (X₁V z)
      (↑(blockSites d L N₁ m₁ (k + 1) k z) : Set (CTorus d L N₁ m₁ (k + 1))))
    -- the old terms
    {τι : Type*} [DecidableEq τι] (𝒯E : Finset τι) {ϱ₁ ϱ₂ : τι → ℝ}
    {GkE : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₁ τ)}
    {GjE : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₂ τ)} {r₀ δ₃ δfl : ℝ}
    {X₀E X₁E : τι → Finset (CTorus d L N₁ m₁ (k + 1))} {jE : τι → ℕ}
    {XE 𝒦XE : τι → Set (CTorus d L N₁ m₁ (k + 1))} {EbE : τι → ℝ}
    (hBE : ∀ τ ∈ 𝒯E, BgSetting N S.G' (GkE τ) (GjE τ) a₁ ν c BG κ r₀ eps δ₃ (X₀E τ) (X₁E τ) (jE τ))
    (hFE : ∀ τ ∈ 𝒯E, FlSetting N S.G' (GkE τ) Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl (X₁E τ))
    (hcovE : ∀ τ ∈ 𝒯E, CovSetup S.G' (m₀) (jE τ) (XE τ) (𝒦XE τ))
    (hX₁E : ∀ τ ∈ 𝒯E, (↑(X₁E τ) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 S.G' (m₀) (jE τ) (𝒦XE τ))
    (hoptE : ∀ τ ∈ 𝒯E, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XE τ) ∧ MeetsOne (m₀) (jE τ) (𝒦XE τ) W₀ ∧
        bondCost (scaleW L (m₀) m₁ (jE τ)) E₀ = treeLenCovOne (m₀) (jE τ) (XE τ))
    (hlogE : ∀ τ ∈ 𝒯E, Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) *
      (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hEbE : ∀ τ ∈ 𝒯E, 0 ≤ EbE τ) {EE : τι → RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ}
    (hEanE : ∀ τ ∈ 𝒯E, AnalyticOnNhd ℂ (EE τ) (XiCRaw (GjE τ) (compWeight L a₁) ν (jE τ)
      (scaledC0 d) (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)))
    (hEbdE : ∀ τ ∈ 𝒯E, ∀ r ∈ XiCRaw (GjE τ) (compWeight L a₁) ν (jE τ) (scaledC0 d)
      (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      ‖EE τ r‖ ≤ EbE τ * Real.exp (-(κdec - 1) * treeLenCovOne (m₀) (jE τ) (XE τ)))
    -- the sites of the source
    {jF : CTorus d L N₁ m₁ (k + 1) × Fin N → ℕ}
    {XF 𝒦XF : CTorus d L N₁ m₁ (k + 1) × Fin N → Set (CTorus d L N₁ m₁ (k + 1))}
    {X₁F : CTorus d L N₁ m₁ (k + 1) × Fin N → Finset (CTorus d L N₁ m₁ (k + 1))}
    (hcovF : ∀ s, CovSetup S.G' (m₀) (jF s) (XF s) (𝒦XF s))
    (hX₁F : ∀ s, (↑(X₁F s) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 S.G' (m₀) (jF s) (𝒦XF s))
    (hoptF : ∀ s, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XF s) ∧ MeetsOne (m₀) (jF s) (𝒦XF s) W₀ ∧
        bondCost (scaleW L (m₀) m₁ (jF s)) E₀ = treeLenCovOne (m₀) (jF s) (XF s))
    (hΔF : ∀ s, treeLenCovOne (m₀) (jF s) (XF s) = 0)
    (hlogF : ∀ _s : CTorus d L N₁ m₁ (k + 1) × Fin N, Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤
      (κ / 2 - 1) / 2)
    (hyF : ∀ s : CTorus d L N₁ m₁ (k + 1) × Fin N, s.1 ∈ X₁F s)
    -- the observable terms
    {μι : Type*} [DecidableEq μι] (𝒯M : Finset μι) {ϱ₁M ϱ₂M : μι → ℝ}
    {GkM : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₁M τ)}
    {GjM : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₂M τ)}
    {X₀M X₁M : μι → Finset (CTorus d L N₁ m₁ (k + 1))} {jM : μι → ℕ}
    {XM 𝒦XM : μι → Set (CTorus d L N₁ m₁ (k + 1))} {EbM : μι → ℝ}
    (ys : μι → CTorus d L N₁ m₁ (k + 1)) (is : μι → Fin N) (hys : ∀ τ ∈ 𝒯M, ys τ ∈ X₁M τ)
    (hBM : ∀ τ ∈ 𝒯M, BgSetting N S.G' (GkM τ) (GjM τ) a₁ ν c BG κ r₀ eps δ₃ (X₀M τ) (X₁M τ) (jM τ))
    (hFM : ∀ τ ∈ 𝒯M, FlSetting N S.G' (GkM τ) Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl (X₁M τ))
    (hcovM : ∀ τ ∈ 𝒯M, CovSetup S.G' (m₀) (jM τ) (XM τ) (𝒦XM τ))
    (hX₁M : ∀ τ ∈ 𝒯M, (↑(X₁M τ) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 S.G' (m₀) (jM τ) (𝒦XM τ))
    (hoptM : ∀ τ ∈ 𝒯M, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XM τ) ∧ MeetsOne (m₀) (jM τ) (𝒦XM τ) W₀ ∧
        bondCost (scaleW L (m₀) m₁ (jM τ)) E₀ = treeLenCovOne (m₀) (jM τ) (XM τ))
    (hlogM : ∀ τ ∈ 𝒯M, Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) *
      (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hEbM : ∀ τ ∈ 𝒯M, 0 ≤ EbM τ) {EM : μι → RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ}
    (hEanM : ∀ τ ∈ 𝒯M, AnalyticOnNhd ℂ (EM τ) (XiCRaw (GjM τ) (compWeight L a₁) ν (jM τ)
      (scaledC0 d) (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)))
    (hEbdM : ∀ τ ∈ 𝒯M, ∀ r ∈ XiCRaw (GjM τ) (compWeight L a₁) ν (jM τ) (scaledC0 d)
      (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      ‖EM τ r‖ ≤ EbM τ * Real.exp (-(κdec - 1) * treeLenCovOne (m₀) (jM τ) (XM τ)))
    -- the sizes of the old terms and of the observable terms (the source bounds of (3.2)-(3.4)):
    -- the bounds of the terms rooted at one site (resp. at one source site) add up to `ρ`
    (rE : τι → CTorus d L N₁ m₁ (k + 1)) (hrE : ∀ τ ∈ 𝒯E, rE τ ∈ X₁E τ) {ρE : ℝ} (hρE0 : 0 ≤ ρE)
    (hρE : ∀ x : CTorus d L N₁ m₁ (k + 1), ∑ τ ∈ 𝒯E.filter (fun τ => rE τ = x),
      EbE τ * Real.exp (-κ₀ * treeLenCovOne m₀ (jE τ) (XE τ)) ≤ ρE)
    {ρM : ℝ} (hρM0 : 0 ≤ ρM)
    (hρM : ∀ p : CTorus d L N₁ m₁ (k + 1) × Fin N, ∑ τ ∈ 𝒯M.filter (fun τ => (ys τ, is τ) = p),
      EbM τ * Real.exp (-κ₀ * treeLenCovOne m₀ (jM τ) (XM τ)) ≤ ρM)
    -- the `ν`-part: the bound on the external field and the block margin of the blocks
    {Bh : ℝ} (hBh0 : 0 ≤ Bh)
    (hBh : ∀ D : BgData S.G' N, XiCData S.G' (compWeight L a₁) ν (k + 1) 1 eps D →
      ∀ x i, ‖D.h x i‖ ≤ Bh) (cν : ℂ)
    (hZν : ∀ z, (↑(blockSites d L N₁ m₁ (k + 1) k z) : Set (CTorus d L N₁ m₁ (k + 1))) ⊆ ↑(X₁V z))
    (hRσ : 0 < Rσ) (hc : (Rσ * R₁ + r) * ρ < cψ)
    {Θ₀ : RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)}
    (hΘ₀ : Θ₀ ∈ physSΛEta S a₁ ν eps η)
    (hεb : prop33EpsEtaScaled d L N m₁ k m₀ a₁ BG BG₂ κ δ₁ r ρE ρM η * ‖cβ‖ +
      ‖cν‖ * (1 * (c1 d L * ((L : ℝ) ^ (m₀ + m₁)) ^ d *
        nuBd d L N k (cK2' d L N (famConst d L BG₂ κ) * δ₁)
          (K4 d L N BG κ * (xiC1 d * eps) + (1 + 3 * (xiC1 d * eps)) + Bh) / r)) ≤ εU)



include hC hconn hrow hκ₀ hκdec hκ h1 hR₁ hr hη0 hk hG hcψ hMX hdm hα hsmX hδ₁ ha₁ H hc7 hR hRs hsmall hnum hnum' hsm hcovV hX₁V hoptV hΔV hlogV hZV hmarV hBE hFE hcovE hX₁E hoptE hlogE hEbE hEanE hEbdE hcovF hX₁F hoptF hΔF hlogF hyF hys hBM hFM hcovM hX₁M hoptM hlogM hEbM hEanM hEbdM hrE hρE0 hρE hρM0 hρM hBh0 hBh hZν

variable (hN : L ^ m₀ ∣ N₁) (hp : 0 < S.p₁)

include hRσ hc hΘ₀ hεb hN hp

/-- **`physical_directTerms_eta_scaled`.**  As `physical_directTerms_eta`, with the amplitude
hypothesis `hεb` in terms of `prop33EpsEtaScaled` (the potential term in physical units).  The
`DirectTerms` instance lives on the `eta`-slice; its terms are sharply local (the relation `physAgΘ`
is agreement of the raw datum and the source on `Y` itself) and its bound is the amplitude of `hεb`
times the decay factor. -/
theorem physical_directTerms_eta_scaled :
    ∃ I : DirectTerms S m₀ hp (fun ψ => (ψ, ψ)) ρ Rσ εU (2 * κdec - 1) Θ₀ (physSΛEta S a₁ ν eps η)
      (physXW S cψ R₁ Rσ r) (physVal (EE := EE) (EM := EM) S cβ hG cc 𝒯E hBE hFE 𝒯M ys is hBM hFM cν) (physAgΘ S) (AgFDirPair S),
      PhysicalSharpLocEta S cψ R₁ Rσ r a₁ ν eps η I.𝒴 I.T ∧
        I.b = fun Y : Set (CTorus d L N₁ m₁ (k + 1)) =>
          prop33EpsEtaScaled d L N m₁ k m₀ a₁ BG BG₂ κ δ₁ r ρE ρM η * ‖cβ‖ *
          Real.exp (-(2 * κdec - 1) * treeLenCovOne m₀ (k + 1) Y) +
          ‖cν‖ * (1 * (c1 d L * ((L : ℝ) ^ (m₀ + m₁)) ^ d *
            nuBd d L N k (cK2' d L N (famConst d L BG₂ κ) * δ₁)
              (K4 d L N BG κ * (xiC1 d * eps) + (1 + 3 * (xiC1 d * eps)) + Bh) / r) *
            Real.exp (-(2 * κdec - 1) * treeLenCovOne m₀ (k + 1) Y)) := by
  classical
  obtain ⟨𝒴, T, hD0⟩ := interaction_expansion_hat_dm_core_dir_eta_scaled (Kc := Kc) (Cx := Cx) (c₂ := c₂) (BG₂ := BG₂) (δ₁ := δ₁) hC cβ hconn hrow (κdec := κdec) (κ₀ := κ₀) hκ₀ hκdec hκ h1 (R₁ := R₁) hR₁ (r := r) (Rσ := Rσ) hr (η := η) hη0 hk hG S.hG' cc (cψ := cψ) hcψ hMX (δc := δc) hdm hα hsmX hδ₁ ha₁ H hc7 (R := R) hR hRs hsmall hnum hnum' hsm (m₀ := m₀) (jV := jV) (XV := XV) (𝒦XV := 𝒦XV) (X₁V := X₁V) hcovV hX₁V hoptV hΔV hlogV hZV hmarV (τι := τι) 𝒯E (ϱ₁ := ϱ₁) (ϱ₂ := ϱ₂) (GkE := GkE) (GjE := GjE) (r₀ := r₀) (δ₃ := δ₃) (δfl := δfl) (X₀E := X₀E) (X₁E := X₁E) (jE := jE) (XE := XE) (𝒦XE := 𝒦XE) (EbE := EbE) hBE hFE hcovE hX₁E hoptE hlogE hEbE (EE := EE) hEanE hEbdE (jF := jF) (XF := XF) (𝒦XF := 𝒦XF) (X₁F := X₁F) hcovF hX₁F hoptF hΔF hlogF hyF (μι := μι) 𝒯M (ϱ₁M := ϱ₁M) (ϱ₂M := ϱ₂M) (GkM := GkM) (GjM := GjM) (X₀M := X₀M) (X₁M := X₁M) (jM := jM) (XM := XM) (𝒦XM := 𝒦XM) (EbM := EbM) ys is hys hBM hFM hcovM hX₁M hoptM hlogM hEbM (EM := EM) hEanM hEbdM rE hrE (ρE := ρE) hρE0 hρE (ρM := ρM) hρM0 hρM (Bh := Bh) hBh0 hBh cν hZν
  have hS : PhysicalSharpLocEta S cψ R₁ Rσ r a₁ ν eps η 𝒴 T :=
    fun Y hY xw hxw xw' hxw' σ hσ Θ hΘ Θ' hΘ' hag h1' h2' =>
      hD0.loc.loc Y hY xw hxw xw' hxw' σ hσ Θ hΘ Θ' hΘ' hag h1' h2'
  have hD := hD0.comap (F' := (unitPts S.G' × Fin N → ℂ) × (unitPts S.G' × Fin N → ℂ)) id
    (XW' := physXW S cψ R₁ Rσ r) (fun xw h => h) (AgF' := AgFPair S)
    (fun Y a a' h => agFDirPair_of_agFPair S h) (e' := fun ψ => (ψ, ψ)) (fun _ => rfl)
  have hexp : ∀ Y : Set (CTorus d L N₁ m₁ (k + 1)),
      0 ≤ Real.exp (-(2 * κdec - 1) * treeLenCovOne m₀ (k + 1) Y) := fun Y => (Real.exp_pos _).le
  refine ⟨{ 𝒴 := 𝒴
            T := T
            b := fun Y : Set (CTorus d L N₁ m₁ (k + 1)) =>
              prop33EpsEtaScaled d L N m₁ k m₀ a₁ BG BG₂ κ δ₁ r ρE ρM η * ‖cβ‖ *
              Real.exp (-(2 * κdec - 1) * treeLenCovOne m₀ (k + 1) Y) +
              ‖cν‖ * (1 * (c1 d L * ((L : ℝ) ^ (m₀ + m₁)) ^ d *
                nuBd d L N k (cK2' d L N (famConst d L BG₂ κ) * δ₁)
                  (K4 d L N BG κ * (xiC1 d * eps) + (1 + 3 * (xiC1 d * eps)) + Bh) / r) *
                Real.exp (-(2 * κdec - 1) * treeLenCovOne m₀ (k + 1) Y))
            loc := { hD.loc with loc := hS }
            dom := hD.dom
            bd := fun Y _ => by
              calc _ = (prop33EpsEtaScaled d L N m₁ k m₀ a₁ BG BG₂ κ δ₁ r ρE ρM η * ‖cβ‖ +
                  ‖cν‖ * (1 * (c1 d L * ((L : ℝ) ^ (m₀ + m₁)) ^ d *
                    nuBd d L N k (cK2' d L N (famConst d L BG₂ κ) * δ₁)
                      (K4 d L N BG κ * (xiC1 d * eps) + (1 + 3 * (xiC1 d * eps)) + Bh) / r))) *
                  Real.exp (-(2 * κdec - 1) * treeLenCovOne m₀ (k + 1) Y) := by ring
                _ ≤ _ := mul_le_mul_of_nonneg_right hεb (hexp Y)
            mem := hΘ₀
            agΘ := fun Y => ⟨fun x _ => ⟨rfl, rfl⟩, fun x _ => rfl⟩
            xw := fun ψ hψ => ⟨hatRaysO_pair S hψ hRσ.le (by linarith) hr.le hc,
              hatRaysO_pair S hψ hRσ.le (by linarith) hr.le hc⟩
            ag := fun Y hY Φ Φ' h => by
              have h' := S.agHatFDir_hatOf m₀ (cell_subset_of_isDj hN (hD.dom Y hY)) ρ hp Φ Φ' h
              exact ⟨h', h'⟩
            meas := fun Y hY σ hσ => by
              have hcont := hD.cont Y hY σ hσ Θ₀ hΘ₀
              refine (continuousOn_iff_continuous_domRestrict.1 (hcont.mono ?_)).measurable
              intro ψ hψ
              exact ⟨hatRaysO_pair S hψ hRσ.le (by linarith) hr.le hc,
                hatRaysO_pair S hψ hRσ.le (by linarith) hr.le hc⟩ }, hS, rfl⟩

end SharpPhysical

end Balaban.Fluctuation
