/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.Decoupled2FieldClose
public import Balaban.Localization.DecoupledBackground

/-!
# Theorem I-4b: the decoupled background field, for a cover `C` and an operator `H`

The decoupled background field `(φ_k(s), α_k(s)) = (φ₀ + δφ(s), δα(s))` of the pair `(C, H)`, built
from Theorem I-4a in mode U with the data `(δΨ = 0, φ₀ = approxField, α₀ = 0, f₁ = residual)` of
Lemma 5.3.  `DecSpecs d L Kc Cx c BG` is one set of constants for all the inputs of I-4a.

* `IsDecBg`, `decBgField`, `decBgMult`: the field and the multiplier, defined through `∃!`;
* `i4b_exists_unique`, `i4b_one`: existence and uniqueness, `s = 1` is `bgFieldC`;
* `i4b_close`: closeness (I-4b (iii)); `i4b_analytic`: analyticity in `(s, data)`.

The locality (I-4b (iv)) is `i4b_local` in `Decoupled2BackgroundLocal.lean`.
-/

@[expose] public section

namespace Balaban.Localization.Dec2

open Balaban Balaban.Multiscale Balaban.Background Balaban.Reflection Finset Matrix

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {C : DecCover d L N₁ m₁ K} {H : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ}
  {Kc Cx : ℝ} {α : H.Ω 1 → ℂ}

/-- One set of constants for all the inputs of Theorem I-4a (`specs_exist`). -/
structure DecSpecs (d L : ℕ) [NeZero L] (Kc Cx c BG : ℝ) : Prop where
  fam : FamSpec d L Kc Cx c BG
  dg2 : Dg2Spec d L Kc Cx c BG
  close : CloseSpec d L Kc Cx c BG
  one : OneSpec d L Kc Cx c
  an : AnSpec d L Kc Cx c

theorem decSpecs_exists {d L : ℕ} [NeZero L] (hd : 3 ≤ d) (hL : 3 ≤ L) (hKc : 0 ≤ Kc) (hCx : 0 ≤ Cx) :
    ∃ c BG : ℝ, DecSpecs d L Kc Cx c BG := by
  obtain ⟨c, BG, h1, h2, h3, h4, h5⟩ := specs_exist (d := d) (L := L) (Kc := Kc) (Cx := Cx) hd hL hKc hCx
  exact ⟨c, BG, h1, h2, h3, h4, h5⟩


variable (C H a ν) in
/-- **The decoupled background field** at the parameters `s`: `(φ, α)` with `α` a fixed point of
`𝒩_s` in the ball `|α|₂ ≤ ρ` for the data `(φ₀, 0, 0, f₀)` of Lemma 5.3 (mode U), and
`φ = φ₀ + δφ` with `δφ = G_s(α)(f₀ - α φ₀)`. -/
structure IsDecBg (ρ : ℝ) (s : DecParams C) (D : BgData H N) (φ : H.Ω 1 × Fin N → ℂ)
    (α : H.Ω 1 → ℂ) : Prop where
  small : Small H α ρ
  fixed : DecFixed C H a ν s true (0 : H.Ω 1 → ℂ) (approxField H a ν D.Ψ D.h)
    (residual H a ν D (approxField H a ν D.Ψ D.h)) α
  field : φ = fun p => approxField H a ν D.Ψ D.h p.1 p.2 +
    dphi H (decG C H a ν s) (0 : H.Ω 1 → ℂ) (approxField H a ν D.Ψ D.h)
      (residual H a ν D (approxField H a ν D.Ψ D.h)) α p

variable (C H a ν) in
open Classical in
/-- The decoupled background field `φ_k(s)` (`0` if there is no unique one; `i4b_exists_unique`
shows that it exists and is unique in the range of Theorem I-4b). -/
noncomputable def decBgField (ρ : ℝ) (s : DecParams C) (D : BgData H N) :
    H.Ω 1 × Fin N → ℂ :=
  if Hh : ∃! p : (H.Ω 1 × Fin N → ℂ) × (H.Ω 1 → ℂ), IsDecBg C H a ν ρ s D p.1 p.2
    then Hh.exists.choose.1 else 0

variable (C H a ν) in
open Classical in
/-- The decoupled multiplier `α_k(s)`. -/
noncomputable def decBgMult (ρ : ℝ) (s : DecParams C) (D : BgData H N) : H.Ω 1 → ℂ :=
  if Hh : ∃! p : (H.Ω 1 × Fin N → ℂ) × (H.Ω 1 → ℂ), IsDecBg C H a ν ρ s D p.1 p.2
    then Hh.exists.choose.2 else 0

theorem decBg_eq {ρ : ℝ} {s : DecParams C} {D : BgData H N} {φ : H.Ω 1 × Fin N → ℂ}
    {α : H.Ω 1 → ℂ} (h : IsDecBg C H a ν ρ s D φ α)
    (hu : ∀ φ' α', IsDecBg C H a ν ρ s D φ' α' → φ' = φ ∧ α' = α) :
    decBgField C H a ν ρ s D = φ ∧ decBgMult C H a ν ρ s D = α := by
  classical
  have Hh : ∃! p : (H.Ω 1 × Fin N → ℂ) × (H.Ω 1 → ℂ), IsDecBg C H a ν ρ s D p.1 p.2 :=
    ⟨(φ, α), h, fun p hp => Prod.ext (hu p.1 p.2 hp).1 (hu p.1 p.2 hp).2⟩
  have e : Hh.exists.choose = (φ, α) := Hh.unique Hh.exists.choose_spec h
  refine ⟨?_, ?_⟩
  · unfold decBgField; simp only [Hh, ↓reduceDIte]; rw [e]
  · unfold decBgMult; simp only [Hh, ↓reduceDIte]; rw [e]

/-- **Theorem I-4b (existence, uniqueness, bounds)**: for `s` with `|s_P| ≤ e^{κ₁}` and data in
`Ψ̃^c(δ, ε)` with the hypotheses of Theorem 5.2, `δ ≤ c₇`: the decoupled background field exists
and is unique in the ball, and it satisfies the bounds P2 (1.15) with the constant `K₄ δ`
(`BgBounds`), `|δφ|₀, |∂δφ|₁, |Δ δφ|₂, |δα|₂ ≤ K₂' C₃ δ`. -/
theorem i4b_exists_unique {c BG : ℝ} (hS : DecSpecs d L Kc Cx c BG) (S : CoverBase C H a ν Kc Cx)
    (HB : BgHyp d L K ϱ a ν) {κ : ℝ} (hκ : 0 ≤ κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {s : DecParams C}
    (hs : ∀ P, ‖s P‖ ≤ Real.exp κ) {δ ε : ℝ} (hδ0 : 0 < δ) (hδε : δ ≤ ε)
    (hε : ε ≤ bgC0 d L N) (hδ : δ ≤ c7 d L N BG κ)
    (hνε : ν * ((L : ℝ) ^ K) ^ 2 * ε ^ 2 ≤ δ ^ 2) {D : BgData H N} (hD : InDomainC H ν δ ε D) :
    ∃ (φ : H.Ω 1 × Fin N → ℂ) (α : H.Ω 1 → ℂ),
      IsDecBg C H a ν (rho4 d L N BG κ) s D φ α ∧
      (∀ φ' α', IsDecBg C H a ν (rho4 d L N BG κ) s D φ' α' → φ' = φ ∧ α' = α) ∧
      Small H α (cK2' d L N (famConst d L BG κ) * (lemma53Const d L * δ)) ∧
      SupBounds H (fun p => φ p - approxField H a ν D.Ψ D.h p.1 p.2)
        (cK2' d L N (famConst d L BG κ) * (lemma53Const d L * δ)) ∧
      BgBounds H D φ α (K4 d L N BG κ * δ) := by
  have hd0 : 0 < d := by have := HB.hd; omega
  have hBG := hS.fam.2.1
  obtain ⟨W⟩ := DataWit.exists hD
  have Hd := decHyp_of_data (N := N) HB hBG hδ0 hδε hε hδ hνε W
  obtain ⟨h1, h2, -⟩ := c7_facts (L := L) (N := N) hd0 hBG hδ0.le hδ
  have hCδ : 0 < lemma53Const d L * δ := mul_pos (lemma53Const_pos d L) hδ0
  have hdc := deltaClose_le_deltaStar' (d := d) (L := L) (N := N) (BG := BG) (κ := κ)
  have hdcp := deltaClose_pos (d := d) (L := L) (N := N) (κ := κ) hd0 hBG
  have hle : lemma53Const d L * δ ≤ deltaStar' d L N (famConst d L BG κ) (gamma1 d / 8) := by
    linarith
  obtain ⟨δα, hfix, hsm, hsK, hsup, huniq, -⟩ :=
    i4a_exists_unique hS.fam C H S hκ hM hs Hd hle hle
  rw [pertSource_zeroΨ] at hfix hsup huniq
  have hB0 : 0 ≤ famConst d L BG κ := by
    have := famConst_ge_one (L := L) hBG κ hd0; linarith
  have hk := cK2'_nonneg (d := d) (L := L) (N := N) hB0
  have hid : IsDecBg C H a ν (rho4 d L N BG κ) s D
      (fun p => approxField H a ν D.Ψ D.h p.1 p.2 + dphi H (decG C H a ν s) (0 : H.Ω 1 → ℂ)
        (approxField H a ν D.Ψ D.h) (residual H a ν D (approxField H a ν D.Ψ D.h)) δα p) δα :=
    ⟨hsm, hfix, rfl⟩
  refine ⟨_, δα, hid, ?_, hsK, ?_, ?_⟩
  · intro φ' α' h'
    have e := huniq α' h'.small h'.fixed
    subst e
    exact ⟨h'.field, rfl⟩
  · have : (fun p : H.Ω 1 × Fin N => (approxField H a ν D.Ψ D.h p.1 p.2 + dphi H (decG C H a ν s)
        (0 : H.Ω 1 → ℂ) (approxField H a ν D.Ψ D.h)
        (residual H a ν D (approxField H a ν D.Ψ D.h)) δα p) -
        approxField H a ν D.Ψ D.h p.1 p.2) = dphi H (decG C H a ν s) (0 : H.Ω 1 → ℂ)
        (approxField H a ν D.Ψ D.h) (residual H a ν D (approxField H a ν D.Ψ D.h)) δα := by
      funext p; ring
    rw [this]; exact hsup
  · obtain ⟨hδa, -, hC32, -⟩ := bgC1_facts d L N hd0 h1
    have Sa : ApproxSetting d L K ϱ a ν δ ε :=
      HB.approxSetting hδ0 hδε (hε.trans (bgC0_le d L N)) (approxDelta_le d L hδa).1 hνε
    have hl := lemma53 Sa hδa D W.real W (fun x hx i => W.real_Ψ hx i) (fun x hx i => W.real_h hx i)
    have hsup' : SupBounds H (dphi H (decG C H a ν s) (0 : H.Ω 1 → ℂ)
        (approxField H a ν D.Ψ D.h) (residual H a ν D (approxField H a ν D.Ψ D.h)) δα)
        (cK2' d L N (famConst d L BG κ) * (lemma53Const d L * δ)) := hsup
    have hkk : 0 ≤ cK2' d L N (famConst d L BG κ) * (lemma53Const d L * δ) := by positivity
    have hX : 0 ≤ (1 + L + 2 * d * (L : ℝ) ^ 2) * (lemma53Const d L * δ) := by positivity
    have hNk : 0 ≤ (N : ℝ) * (cK2' d L N (famConst d L BG κ) * (lemma53Const d L * δ)) := by
      positivity
    have e : K4 d L N BG κ * δ = (1 + L + 2 * d * (L : ℝ) ^ 2) * (lemma53Const d L * δ) +
        N * (cK2' d L N (famConst d L BG κ) * (lemma53Const d L * δ)) +
        cK2' d L N (famConst d L BG κ) * (lemma53Const d L * δ) := by
      unfold K4; ring
    refine bgBounds_of_parts (HB.green (G := H)).sep_gt_one (by have := HB.hL; omega) hCδ.le
      (by positivity) hl.2.1 (fun y hy => (hl.1 y hy).2) hsup' (fun x => (hsK x).trans ?_)
      (by linarith)
    linarith

/-- The identification of a fixed point of `𝒩_1` in the ball with a solution of (P-1), (P-2). -/
theorem isPerturbed_of_decFixed_one {c BG : ℝ} (hS : DecSpecs d L Kc Cx c BG) (S : CoverBase C H a ν Kc Cx)
    {κ : ℝ} (hκ : 0 ≤ κ) (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    {α₀ : H.Ω 1 → ℂ} {φ₀ δΨ : CTorus d L N₁ m₁ K → Fin N → ℂ} {f₁ : H.Ω 1 × Fin N → ℂ}
    {δ₀ δ₁ : ℝ} (Hh : DecHyp H a ν true α₀ φ₀ δΨ f₁ δ₀ δ₁)
    (hδ₀ : δ₀ ≤ deltaStar' d L N (famConst d L BG κ) (gamma1 d / 8))
    (hδ₁ : δ₁ ≤ deltaStar' d L N (famConst d L BG κ) (gamma1 d / 8)) {δα : H.Ω 1 → ℂ}
    (hfix : DecFixed C H a ν (fun _ => 1) true α₀ φ₀ (pertSource H a δΨ f₁) δα)
    (hsmall : Small H δα (rho4 d L N BG κ)) :
    IsPerturbed H a ν α₀ φ₀ (pertSource H a δΨ f₁)
      (dphi H (decG C H a ν (fun _ => 1)) α₀ φ₀ (pertSource H a δΨ f₁) δα) δα := by
  have hd0 : 0 < d := by have := S.hd; omega
  have hE : 1 ≤ Real.exp (N0 d L * κ) := Real.one_le_exp (by unfold N0; positivity)
  have hMc : c ≤ (L : ℝ) ^ m₁ := by
    refine le_trans ?_ hM
    have := hS.one.1; nlinarith
  set B : ℝ := famConst d L BG κ with hB
  set Γ : ℝ := gamma1 d / 8 with hΓdef
  have hB0 : 0 ≤ B := by have := famConst_ge_one (L := L) hS.fam.2.1 κ hd0; linarith
  have hΓ : 0 < Γ := by have := gamma1_pos hd0; positivity
  have hC := coreHyp'_small (d := d) (L := L) (N := N) hB0 hΓ Hh.δ₀_nn Hh.δ₁_nn hδ₀ hδ₁
  have hfam : ∀ δα' : H.Ω 1 → ℂ, Small H δα' (c6' d L N B Γ) →
      dphi H (decG C H a ν (fun _ => 1)) α₀ φ₀ (pertSource H a δΨ f₁) δα' =
        dphi H (greenD H a ν) α₀ φ₀ (pertSource H a δΨ f₁) δα' := by
    intro δα' hs
    have hsm' : Small H (α₀ + δα') Γ := Hh.setup.poly hs (by linarith [hC.poly, hC.ρ_nn])
    unfold dphi
    rw [decG_one hS.one S hMc (admPot_of_small hd0 hsm')]
  have hfixG : Nmap H (dirichletOperator H a ν α₀) true φ₀ (pertSource H a δΨ f₁)
      (dphi H (greenD H a ν) α₀ φ₀ (pertSource H a δΨ f₁) δα) = δα := by
    rw [← hfam δα hsmall]; exact hfix
  have hpoly : δ₀ + 2 * c6' d L N B Γ ≤ gamma1 d := by linarith [hC.poly]
  have hP := perturbed_of_fixed Hh.green Hh.alpha0 hC.ρ_nn hpoly hsmall hfixG
  rw [hfam δα hsmall]; exact hP

/-- **Theorem I-4b (i), `s = 1`**: the decoupled background field at `s ≡ 1` is the background
field `bgFieldC` of Theorem 5.2 (and the multiplier is `bgMultC`). -/
theorem i4b_one {c BG : ℝ} (hS : DecSpecs d L Kc Cx c BG) (S : CoverBase C H a ν Kc Cx)
    (HB : BgHyp d L K ϱ a ν) {κ : ℝ} (hκ : 0 ≤ κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δ ε : ℝ} (hδ0 : 0 < δ) (hδε : δ ≤ ε)
    (hε : ε ≤ bgC0 d L N) (hδ : δ ≤ c7 d L N BG κ)
    (hνε : ν * ((L : ℝ) ^ K) ^ 2 * ε ^ 2 ≤ δ ^ 2) {D : BgData H N} (hD : InDomainC H ν δ ε D)
    {φ : H.Ω 1 × Fin N → ℂ} {α : H.Ω 1 → ℂ}
    (h : IsDecBg C H a ν (rho4 d L N BG κ) (fun _ => 1) D φ α) :
    IsSmallSolution H a ν (bgC0 d L N) D φ α ∧ bgFieldC H a ν (bgC0 d L N) D = φ ∧
      bgMultC H a ν (bgC0 d L N) D = α := by
  have hd0 : 0 < d := by have := HB.hd; omega
  have hBG := hS.fam.2.1
  obtain ⟨W⟩ := DataWit.exists hD
  have Hd := decHyp_of_data (N := N) HB hBG hδ0 hδε hε hδ hνε W
  obtain ⟨h1, h2, h3⟩ := c7_facts (L := L) (N := N) hd0 hBG hδ0.le hδ
  have hCδ : 0 < lemma53Const d L * δ := mul_pos (lemma53Const_pos d L) hδ0
  have hdc := deltaClose_le_deltaStar' (d := d) (L := L) (N := N) (BG := BG) (κ := κ)
  have hdcp := deltaClose_pos (d := d) (L := L) (N := N) (κ := κ) hd0 hBG
  have hle : lemma53Const d L * δ ≤ deltaStar' d L N (famConst d L BG κ) (gamma1 d / 8) := by
    linarith
  have hfix : DecFixed C H a ν (fun _ => 1) true (0 : H.Ω 1 → ℂ) (approxField H a ν D.Ψ D.h)
      (pertSource H a (0 : CTorus d L N₁ m₁ K → Fin N → ℂ)
        (residual H a ν D (approxField H a ν D.Ψ D.h))) α := by
    rw [pertSource_zeroΨ]; exact h.fixed
  have hP := isPerturbed_of_decFixed_one hS S hκ hM Hd hle hle hfix h.small
  rw [pertSource_zeroΨ] at hP
  have hEL : IsEL H a ν D φ α := by
    have := (isPerturbed_iff_isEL (a := a) (ν := ν) D (approxField H a ν D.Ψ D.h) _ α).1 hP
    rw [h.field]
    convert this using 1
  have hc0 := bgC0_pos d L N hd0
  obtain ⟨φ', α', hd', hu', hsm', -, -⟩ := i4b_exists_unique hS S HB hκ hM
    (s := fun _ => 1) (fun P => by simpa using Real.one_le_exp hκ) hδ0 hδε hε hδ hνε hD
  obtain ⟨e1, e2⟩ := hu' φ α h
  have hsol : IsSmallSolution H a ν (bgC0 d L N) D φ α := by
    refine ⟨hEL, fun x => ?_⟩
    have := hsm' x
    rw [e2]
    have := h3
    linarith [hsm' x]
  obtain ⟨φ'', α'', hs'', -, hu''⟩ := theorem52_exists (N := N) HB hδ0 hδε hε h1 hνε hD
  have hun : ∀ φ₂ α₂, IsSmallSolution H a ν (bgC0 d L N) D φ₂ α₂ → φ₂ = φ ∧ α₂ = α := by
    intro φ₂ α₂ h₂
    obtain ⟨a1, a2⟩ := hu'' φ₂ α₂ h₂
    obtain ⟨b1, b2⟩ := hu'' φ α hsol
    exact ⟨a1.trans b1.symm, a2.trans b2.symm⟩
  exact ⟨hsol, (bgFieldC_eq hsol hun).1, (bgFieldC_eq hsol hun).2⟩

/-- **Theorem I-4b (iii): closeness.**  Let `W` be a set of sites containing the thickened
interaction cubes of all the centres with `s_z ≠ 1` (`hW`, the set `𝒲` of (DG6)).  The decoupled
background fields at `s` and at `s ≡ 1` differ at a site `x` by at most
`closeConst · e^{-γ_w d(x, W)}` (value, forward gradient, Laplacian: twice that), and so do the
multipliers.  Here `closeConst = O(C₃ δ)` (so `O(K₄ δ)`); `siteSetDist` is the scaled distance. -/
theorem i4b_close {c BG : ℝ} (hS : DecSpecs d L Kc Cx c BG) (S : CoverBase C H a ν Kc Cx)
    (HB : BgHyp d L K ϱ a ν) {κ : ℝ} (hκ : 0 ≤ κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {s : DecParams C}
    (hs : ∀ P, ‖s P‖ ≤ Real.exp κ) {W : Finset (CTorus d L N₁ m₁ K)}
    (hW : ∀ z ∈ C.cubeIdx, C.sProd (extS C s) z ≠ 1 → intBox z ⊆ W)
    {δ ε : ℝ} (hδ0 : 0 < δ) (hδε : δ ≤ ε) (hε : ε ≤ bgC0 d L N) (hδ : δ ≤ c7 d L N BG κ)
    (hνε : ν * ((L : ℝ) ^ K) ^ 2 * ε ^ 2 ≤ δ ^ 2) {D : BgData H N} (hD : InDomainC H ν δ ε D)
    {φ φ1 : H.Ω 1 × Fin N → ℂ} {α α1 : H.Ω 1 → ℂ}
    (h : IsDecBg C H a ν (rho4 d L N BG κ) s D φ α)
    (h1 : IsDecBg C H a ν (rho4 d L N BG κ) (fun _ => 1) D φ1 α1) :
    (∀ x : H.Ω 1, H.spacing (x : CTorus d L N₁ m₁ K) ^ 2 * ‖α x - α1 x‖ ≤
        closeConst d L N BG κ (lemma53Const d L * δ) *
          decay (gammaW d) (siteSetDist H W x)) ∧
    (∀ (y : CTorus d L N₁ m₁ K) (i : Fin N),
      ‖svec H (φ - φ1) y i‖ ≤ 2 * closeConst d L N BG κ (lemma53Const d L * δ) *
        decay (gammaW d) (siteSetDist H W y)) ∧
    (∀ x ∈ H.Ω 1, ∀ (μ : Fin d) (i : Fin N), H.spacing x *
      ‖svec H (φ - φ1) (x + Pi.single μ 1) i - svec H (φ - φ1) x i‖ ≤
        2 * closeConst d L N BG κ (lemma53Const d L * δ) *
          decay (gammaW d) (siteSetDist H W x)) ∧
    (∀ x ∈ H.Ω 1, ∀ i : Fin N, H.spacing x ^ 2 * ‖∑ μ : Fin d,
      (2 * svec H (φ - φ1) x i - svec H (φ - φ1) (x + Pi.single μ 1) i -
        svec H (φ - φ1) (x - Pi.single μ 1) i)‖ ≤
        2 * closeConst d L N BG κ (lemma53Const d L * δ) *
          decay (gammaW d) (siteSetDist H W x)) := by
  have hd0 : 0 < d := by have := HB.hd; omega
  have hBG := hS.fam.2.1
  obtain ⟨Wd⟩ := DataWit.exists hD
  have Hd := decHyp_of_data (N := N) HB hBG hδ0 hδε hε hδ hνε Wd
  obtain ⟨-, h2, -⟩ := c7_facts (L := L) (N := N) hd0 hBG hδ0.le hδ
  have hCδ : 0 < lemma53Const d L * δ := mul_pos (lemma53Const_pos d L) hδ0
  have hdcp := deltaClose_pos (d := d) (L := L) (N := N) (κ := κ) hd0 hBG
  have hle : lemma53Const d L * δ ≤ deltaClose d L N BG κ := by linarith
  have hfix : DecFixed C H a ν s true (0 : H.Ω 1 → ℂ) (approxField H a ν D.Ψ D.h)
      (pertSource H a (0 : CTorus d L N₁ m₁ K → Fin N → ℂ)
        (residual H a ν D (approxField H a ν D.Ψ D.h))) α := by
    rw [pertSource_zeroΨ]; exact h.fixed
  have hfix1 : DecFixed C H a ν (fun _ => 1) true (0 : H.Ω 1 → ℂ) (approxField H a ν D.Ψ D.h)
      (pertSource H a (0 : CTorus d L N₁ m₁ K → Fin N → ℂ)
        (residual H a ν D (approxField H a ν D.Ψ D.h))) α1 := by
    rw [pertSource_zeroΨ]; exact h1.fixed
  have hsol := i4a_close hS.fam hS.dg2 hS.close hS.one S hκ hM hs hW Hd hle hle hfix h.small
    hfix1 h1.small
  have e : φ - φ1 = dphi H (decG C H a ν s) (0 : H.Ω 1 → ℂ) (approxField H a ν D.Ψ D.h)
      (pertSource H a (0 : CTorus d L N₁ m₁ K → Fin N → ℂ)
        (residual H a ν D (approxField H a ν D.Ψ D.h))) α -
      dphi H (decG C H a ν (fun _ => 1)) (0 : H.Ω 1 → ℂ) (approxField H a ν D.Ψ D.h)
      (pertSource H a (0 : CTorus d L N₁ m₁ K → Fin N → ℂ)
        (residual H a ν D (approxField H a ν D.Ψ D.h))) α1 := by
    rw [pertSource_zeroΨ, h.field, h1.field]
    funext p; simp only [Pi.sub_apply]; ring
  rw [e]
  exact hsol

/-! ### Analyticity -/

/-- **Theorem I-4b (i): analyticity in `(s, data)`.**  There is one function `F` of the
parameters `s` and the raw data `(Ψ, h̃)` of all fields, analytic at every `(s, (D.Ψ, D.h))` with
`|s_P| < e^{κ₁}` and `D` in the union domain `𝒟` of Theorem 5.2 (with `c₁ = c₇`), which returns the
decoupled background field `(φ_k(s), α_k(s))` there. -/
theorem i4b_analytic {c BG : ℝ} (hS : DecSpecs d L Kc Cx c BG) (S : CoverBase C H a ν Kc Cx)
    (HB : BgHyp d L K ϱ a ν) {κ : ℝ} (hκ : 0 ≤ κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) :
    ∃ F : DecParams C × RawData d L (N₁ * L ^ m₁) K N →
        (H.Ω 1 × Fin N → ℂ) × (H.Ω 1 → ℂ),
      AnalyticOnNhd ℂ F {q | (∀ P, ‖q.1 P‖ < Real.exp κ) ∧ ∃ D : BgData H N,
        InUnionDomainC H (bgC0 d L N) (c7 d L N BG κ) ν D ∧ q.2 = (D.Ψ, D.h)} ∧
      ∀ (s : DecParams C) (D : BgData H N), (∀ P, ‖s P‖ < Real.exp κ) →
        InUnionDomainC H (bgC0 d L N) (c7 d L N BG κ) ν D →
        ∀ (φ : H.Ω 1 × Fin N → ℂ) (α : H.Ω 1 → ℂ),
          IsDecBg C H a ν (rho4 d L N BG κ) s D φ α → F (s, (D.Ψ, D.h)) = (φ, α) := by
  have hd0 : 0 < d := by have := HB.hd; omega
  have hBG := hS.fam.2.1
  have hΔ0 := deltaClose_pos (d := d) (L := L) (N := N) (κ := κ) hd0 hBG
  have hΔ := deltaClose_le_deltaStar' (d := d) (L := L) (N := N) (BG := BG) (κ := κ)
  obtain ⟨sol, hsolan, hsolprop⟩ := i4a_analytic (N := N) hS.fam hS.an S hκ hM true
    hΔ0.le hΔ0.le hΔ hΔ
  refine ⟨fun q => (fun r => approxField H a ν q.2.1 q.2.2 r.1 r.2 +
    (sol (q.1, rawQ H a ν q.2)).1 r, (sol (q.1, rawQ H a ν q.2)).2), ?_, ?_⟩
  · rintro ⟨s, p⟩ ⟨hs, D, ⟨δ, ε, hδ0, hδε, hε, hδc, hνε, hDC⟩, rfl⟩
    obtain ⟨W⟩ := DataWit.exists hDC
    obtain ⟨h1, h2, -⟩ := c7_facts (L := L) (N := N) hd0 hBG hδ0.le hδc
    obtain ⟨hδa, -, hC32, -⟩ := bgC1_facts d L N hd0 h1
    have Sa : ApproxSetting d L K ϱ a ν δ ε :=
      HB.approxSetting hδ0 hδε (hε.trans (bgC0_le d L N)) (approxDelta_le d L hδa).1 hνε
    have hp0 := data_mem_approxDomain Sa W hδa
    have hq := analyticAt_rawQ H a ν hp0
    have hStrict := strictDataM_rawQ (a := a) (ν := ν) (κ := κ) (Δ := deltaClose d L N BG κ) HB
      hBG hδ0 hδε hε hδc hνε (by linarith) W
    have hmem : ((s, rawQ H a ν ((D.Ψ, D.h) : RawData d L (N₁ * L ^ m₁) K N)) :
        DecParams C × Edat H N) ∈ {p : DecParams C × Edat H N |
          (∀ P, ‖p.1 P‖ < Real.exp κ) ∧ StrictDataM H N true (deltaClose d L N BG κ)
            (deltaClose d L N BG κ) p.2} := ⟨hs, hStrict⟩
    have hmap : AnalyticAt ℂ (fun q : DecParams C × RawData d L (N₁ * L ^ m₁) K N =>
        (q.1, rawQ H a ν q.2)) (s, ((D.Ψ, D.h) : RawData d L (N₁ * L ^ m₁) K N)) :=
      analyticAt_fst.prod (AnalyticAt.comp_of_eq (f := fun q : DecParams C × RawData d L (N₁ * L ^ m₁) K N => q.2) hq analyticAt_snd rfl)
    have hcomp : AnalyticAt ℂ (fun q : DecParams C × RawData d L (N₁ * L ^ m₁) K N =>
        sol (q.1, rawQ H a ν q.2)) (s, ((D.Ψ, D.h) : RawData d L (N₁ * L ^ m₁) K N)) :=
      AnalyticAt.comp_of_eq (f := fun q : DecParams C × RawData d L (N₁ * L ^ m₁) K N =>
        (q.1, rawQ H a ν q.2)) (hsolan _ hmem) hmap rfl
    have hc1 : AnalyticAt ℂ (fun q : DecParams C × RawData d L (N₁ * L ^ m₁) K N =>
        (sol (q.1, rawQ H a ν q.2)).1) (s, ((D.Ψ, D.h) : RawData d L (N₁ * L ^ m₁) K N)) :=
      AnalyticAt.comp_of_eq (f := fun q : DecParams C × RawData d L (N₁ * L ^ m₁) K N =>
        sol (q.1, rawQ H a ν q.2)) (analyticAt_fst) hcomp rfl
    have hc2 : AnalyticAt ℂ (fun q : DecParams C × RawData d L (N₁ * L ^ m₁) K N =>
        (sol (q.1, rawQ H a ν q.2)).2) (s, ((D.Ψ, D.h) : RawData d L (N₁ * L ^ m₁) K N)) :=
      AnalyticAt.comp_of_eq (f := fun q : DecParams C × RawData d L (N₁ * L ^ m₁) K N =>
        sol (q.1, rawQ H a ν q.2)) (analyticAt_snd) hcomp rfl
    have hc0 : ∀ r : H.Ω 1 × Fin N, AnalyticAt ℂ
        (fun q : DecParams C × RawData d L (N₁ * L ^ m₁) K N =>
          approxField H a ν q.2.1 q.2.2 r.1 r.2) (s, ((D.Ψ, D.h) : RawData d L (N₁ * L ^ m₁) K N)) :=
      fun r => AnalyticAt.comp_of_eq (f := fun q : DecParams C × RawData d L (N₁ * L ^ m₁) K N =>
        q.2) (analyticAt_approx_coord hp0 r.1 r.2) analyticAt_snd rfl
    refine AnalyticAt.prod (analyticAt_pi_iff.2 fun r => ?_) hc2
    exact (hc0 r).add (analyticAt_pi_iff.1 hc1 r)
  · intro s D hs ⟨δ, ε, hδ0, hδε, hε, hδc, hνε, hDC⟩ φ α hI
    obtain ⟨W⟩ := DataWit.exists hDC
    have hStrict := strictDataM_rawQ (a := a) (ν := ν) (κ := κ) (Δ := deltaClose d L N BG κ) HB
      hBG hδ0 hδε hε hδc hνε (by
        obtain ⟨-, h2, -⟩ := c7_facts (L := L) (N := N) hd0 hBG hδ0.le hδc
        linarith) W
    obtain ⟨hfx, -, -, -, -, huniq⟩ := hsolprop (s, rawQ H a ν ((D.Ψ, D.h) :
      RawData d L (N₁ * L ^ m₁) K N)) hs hStrict
    have hQ : rawQ H a ν ((D.Ψ, D.h) : RawData d L (N₁ * L ^ m₁) K N) =
        (approxField H a ν D.Ψ D.h, 0, 0, residual H a ν D (approxField H a ν D.Ψ D.h)) :=
      Prod.ext rfl (Prod.ext rfl (Prod.ext rfl (rawQ_residual H a ν D)))
    simp only [hQ] at huniq hfx ⊢
    have hfix : DecFixed C H a ν s true (0 : H.Ω 1 → ℂ) (approxField H a ν D.Ψ D.h)
        (pertSource H a (0 : CTorus d L N₁ m₁ K → Fin N → ℂ)
          (residual H a ν D (approxField H a ν D.Ψ D.h))) α := by
      rw [pertSource_zeroΨ]; exact hI.fixed
    have e := huniq α hI.small hfix
    rw [pertSource_zeroΨ] at hfx
    refine Prod.ext ?_ e.symm
    rw [hI.field, hfx, ← e]

end Balaban.Localization.Dec2
