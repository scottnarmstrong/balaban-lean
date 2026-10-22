/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.Decoupled2Background
public import Balaban.Localization.DecoupledFieldHolder
public import Balaban.Background.HolderFull
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Theorem I-4b: the Hölder bound of the decoupled background field (LOCALIZATION.md §3.3 (ii))

P3 Prop. 2.1 and p. 57: the decoupled background fields `φ_k(s)` satisfy all the bounds of P2
Prop. 1.1 with the constant `K₄`, among them the Hölder bound of `∂φ_k(s)`.  The field is
`φ_k(s) = φ₀ + δφ(s)` with `δφ(s)` the field of Theorem I-4a (`IsDecBg.field`), so its Hölder bound
is the one of `δφ(s)` (`i4a_holder`) plus the one of the approximate field `φ₀`
(`approxField_holder`), through `extField_holder_of_increment`, the core of `bgFieldC_holder`.

* `DecSpecs.mono_c`, `decHolSpecs_exists`: one constant `c` for the specs of I-4a and the Hölder
  spec `HolSpec`;
* `i4bHolConst`, **`i4b_holder`**: for `|s_P| ≤ e^{κ₁}` and data in `Ψ̃^c(δ, ε)` with `δ ≤ c₇`,
  every component of the extension `extField φ_k(s) φ₀` (the decoupled field on `Ω₁`, the
  approximate field on the collar) has
  `|∂φ_k(s)ᵢ|_{(θ),2-θ} ≤ ((B_H e^{N₀κ₁}/θ)(c_F + (3/2) K₂') C₃ + C_H) δ`;
* `Dec2.isDecBg_self_iff`, `Dec2.decBgField_self`: the decoupled background field of the cover of
  `G` is the one of `G`; `Dec2.i4b_holder_self`: the Hölder bound for it.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Finset Matrix

section Specs

variable {d L : ℕ} [NeZero L]

/-- The specs of Theorem I-4a are monotone in the constant `c` of the size condition. -/
theorem DecSpecs.mono_c {c c' BG : ℝ} (h : DecSpecs d L c BG) (hc : c ≤ c') :
    DecSpecs d L c' BG :=
  ⟨h.fam.mono_c hc, h.dg2.mono hc le_rfl, h.close.mono hc le_rfl, h.one.mono_c hc, h.an.mono_c hc⟩

/-- **One constant `c` for the specs of Theorem I-4a and the Hölder spec.** -/
theorem decHolSpecs_exists (hd : 3 ≤ d) (hL : 3 ≤ L) :
    ∃ c BG BH : ℝ, DecSpecs d L c BG ∧ HolSpec d L c BH := by
  obtain ⟨c, BG, hS⟩ := decSpecs_exists (d := d) (L := L) hd hL
  obtain ⟨c', BH, hH⟩ := holSpec_exists (d := d) (L := L) hd hL
  exact ⟨max c c', BG, BH, hS.mono_c (le_max_left _ _), hH.mono (le_max_right _ _) le_rfl⟩

end Specs

/-- The constant of the Hölder bound of Theorem I-4b:
`(B_H e^{N₀κ₁}/θ)(c_F + (3/2) K₂') C₃ + C_H`. -/
noncomputable def i4bHolConst (d L N : ℕ) [NeZero L] (BG BH κ θ : ℝ) : ℝ :=
  BH * Real.exp (N0 d L * κ) / θ *
      ((cF d L + 3 / 2 * cK2' d L N (famConst d L BG κ)) * lemma53Const d L) + cHold d L

section Holder

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ}

/-- **Theorem I-4b, the Hölder bound** (P3 Prop. 2.1, p. 57; LOCALIZATION.md §3.3 (ii)): for `s`
with `|s_P| ≤ e^{κ₁}` and data in `Ψ̃^c(δ, ε)` with the hypotheses of Theorem 5.2, `δ ≤ c₇`, every
component of the decoupled background field, extended to the collar by the approximate field, has
`|∂φ_k(s)ᵢ|_{(θ),2-θ} ≤ i4bHolConst · δ`. -/
theorem i4b_holder {c BG BH : ℝ} (hS : DecSpecs d L c BG) (hH : HolSpec d L c BH)
    (S : DGSetting G a ν) (HB : BgHyp d L K ϱ a ν) {κ : ℝ} (hκ : 0 ≤ κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {s : DecParams G}
    (hs : ∀ P, ‖s P‖ ≤ Real.exp κ) {δ ε : ℝ} (hδ0 : 0 < δ) (hδε : δ ≤ ε)
    (hε : ε ≤ bgC0 d L N) (hδ : δ ≤ c7 d L N BG κ)
    (hνε : ν * ((L : ℝ) ^ K) ^ 2 * ε ^ 2 ≤ δ ^ 2) {D : BgData G N} (hD : InDomainC G ν δ ε D)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (i : Fin N) :
    HolderSeminormLE G (fun y => extField G (decBgField G a ν (rho4 d L N BG κ) s D)
        (approxField G a ν D.Ψ D.h) y i) θ (2 - θ) (i4bHolConst d L N BG BH κ θ * δ) := by
  have hd0 : 0 < d := by have := HB.hd; omega
  have hBG := hS.fam.2.1
  obtain ⟨W⟩ := DataWit.exists hD
  have Hd := decHyp_of_data (N := N) HB hBG hδ0 hδε hε hδ hνε W
  obtain ⟨h1, h2, -⟩ := c7_facts (L := L) (N := N) hd0 hBG hδ0.le hδ
  have hdc := deltaClose_le_deltaStar' (d := d) (L := L) (N := N) (BG := BG) (κ := κ)
  have hdcp := deltaClose_pos (d := d) (L := L) (N := N) (κ := κ) hd0 hBG
  have hle : lemma53Const d L * δ ≤ deltaStar' d L N (famConst d L BG κ) (gamma1 d / 8) := by
    linarith
  obtain ⟨φ, α, hid, huniq, hsK, -, -⟩ := i4b_exists_unique hS S HB hκ hM hs hδ0 hδε hε hδ hνε hD
  have hinc := i4a_holder hS.fam hH S hκ hM hs Hd hle hid.small hsK hθ0 hθ1 i
  rw [pertSource_zeroΨ] at hinc
  have hφ : (fun p => φ p - approxField G a ν D.Ψ D.h p.1 p.2) = dphi G (decG G a ν s)
      (0 : G.Ω 1 → ℂ) (approxField G a ν D.Ψ D.h)
      (residual G a ν D (approxField G a ν D.Ψ D.h)) α := by
    rw [hid.field]
    funext p
    ring
  rw [← hφ] at hinc
  obtain ⟨hδa, -, -, -⟩ := bgC1_facts d L N hd0 h1
  have hdelta := approxDelta_le d L hδa
  have Sa : ApproxSetting d L K ϱ a ν δ ε :=
    HB.approxSetting hδ0 hδε (hε.trans (bgC0_le d L N)) hdelta.1 hνε
  have hext := extField_holder_of_increment Sa W hdelta.2 (hdelta.1.trans (by norm_num))
    hθ0.le hθ1.le i hinc
  rw [(decBg_eq hid huniq).1]
  refine holder_mono hext (le_of_eq ?_)
  unfold i4bHolConst
  ring

end Holder

namespace Dec2

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ}

/-- The decoupled background fields of the cover of `G` are those of `G`. -/
theorem isDecBg_self_iff {ρ : ℝ} {s : DecParams (coverOf G)} {D : BgData G N}
    {φ : G.Ω 1 × Fin N → ℂ} {α : G.Ω 1 → ℂ} :
    IsDecBg (coverOf G) G a ν ρ s D φ α ↔ Balaban.Localization.IsDecBg G a ν ρ s D φ α :=
  ⟨fun h => ⟨h.small, h.fixed, h.field⟩, fun h => ⟨h.small, h.fixed, h.field⟩⟩

/-- **The decoupled background field of the cover of `G` is the one of `G`.** -/
theorem decBgField_self (ρ : ℝ) (s : DecParams (coverOf G)) (D : BgData G N) :
    decBgField (coverOf G) G a ν ρ s D = Balaban.Localization.decBgField G a ν ρ s D := by
  classical
  by_cases hex : ∃! p : (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ),
      Balaban.Localization.IsDecBg G a ν ρ s D p.1 p.2
  · obtain ⟨⟨φ, α⟩, hp, hu⟩ := hex
    have hu' : ∀ φ' α', Balaban.Localization.IsDecBg G a ν ρ s D φ' α' → φ' = φ ∧ α' = α :=
      fun φ' α' h' => Prod.ext_iff.1 (hu (φ', α') h')
    rw [(Balaban.Localization.decBg_eq hp hu').1,
      (decBg_eq (isDecBg_self_iff.2 hp) fun φ' α' h' => hu' φ' α' (isDecBg_self_iff.1 h')).1]
  · have hex2 : ¬ ∃! p : (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ),
        IsDecBg (coverOf G) G a ν ρ s D p.1 p.2 := by
      rintro ⟨p, hp, hu⟩
      exact hex ⟨p, isDecBg_self_iff.1 hp, fun q hq => hu q (isDecBg_self_iff.2 hq)⟩
    unfold decBgField Balaban.Localization.decBgField
    simp only [hex, hex2, ↓reduceDIte]

/-- **Theorem I-4b, the Hölder bound, for the cover of `G`** (`i4b_holder` through
`decBgField_self`). -/
theorem i4b_holder_self {c BG BH : ℝ} (hS : Balaban.Localization.DecSpecs d L c BG)
    (hH : HolSpec d L c BH) (S : DGSetting G a ν) (HB : BgHyp d L K ϱ a ν) {κ : ℝ} (hκ : 0 ≤ κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {s : DecParams (coverOf G)}
    (hs : ∀ P, ‖s P‖ ≤ Real.exp κ) {δ ε : ℝ} (hδ0 : 0 < δ) (hδε : δ ≤ ε)
    (hε : ε ≤ bgC0 d L N) (hδ : δ ≤ c7 d L N BG κ)
    (hνε : ν * ((L : ℝ) ^ K) ^ 2 * ε ^ 2 ≤ δ ^ 2) {D : BgData G N} (hD : InDomainC G ν δ ε D)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (i : Fin N) :
    HolderSeminormLE G (fun y => extField G (decBgField (coverOf G) G a ν (rho4 d L N BG κ) s D)
        (approxField G a ν D.Ψ D.h) y i) θ (2 - θ) (i4bHolConst d L N BG BH κ θ * δ) := by
  rw [decBgField_self]
  exact i4b_holder hS hH S HB hκ hM hs hδ0 hδε hε hδ hνε hD hθ0 hθ1 i

end Dec2

end Balaban.Localization
