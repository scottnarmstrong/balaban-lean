/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.DecoupledFieldClose
public import Balaban.Localization.DecoupledFieldLocal
public import Balaban.Localization.DecoupledSolveAnalytic
public import Balaban.Background.Def5
public import Balaban.Background.Theorem52Analytic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Theorem I-4b: the decoupled background field (LOCALIZATION.md §3.3)

The decoupled background field `(φ_k(s), α_k(s)) = (φ₀ + δφ(s), δα(s))` is built from Theorem I-4a
in mode U with the data `(δΨ = 0, φ₀ = approxField, α₀ = 0, f₁ = residual)` of Lemma 5.3, i.e. the
data of the proof of Theorem 5.2 (`rawQ`).

* `DecSpecs`: one set of constants for all the inputs of I-4a;
* `IsDecBg ρ s D φ α`: `(φ, α)` is the decoupled background field at the parameters `s`
  (`α` the fixed point of `𝒩_s` in the ball `|α|₂ ≤ ρ`, `φ = φ₀ + δφ`);
* `decBgField`, `decBgMult`: the field and the multiplier, defined through `∃!` (as `bgFieldC`);
* `i4b_exists_unique`, `i4b_one`, `i4b_bounds`: existence and uniqueness, `s = 1` is `bgFieldC`,
  the bounds of Theorem 5.2 (3) with the constant `K₄`;
* `i4b_analytic`: analyticity in `(s, data)`;
* `i4b_close`: closeness (I-4b (iii));
* `i4b_local`: locality in comparison form (I-4b (iv)).
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Finset Matrix

/-! ### Constants -/

/-- One set of constants for all the inputs of Theorem I-4a (`specs_exist`). -/
structure DecSpecs (d L : ℕ) [NeZero L] (c BG : ℝ) : Prop where
  fam : FamSpec d L c BG
  dg2 : Dg2Spec d L c BG
  close : CloseSpec d L c BG
  one : OneSpec d L c
  an : AnSpec d L c

theorem decSpecs_exists {d L : ℕ} [NeZero L] (hd : 3 ≤ d) (hL : 3 ≤ L) :
    ∃ c BG : ℝ, DecSpecs d L c BG := by
  obtain ⟨c, BG, h1, h2, h3, h4, h5⟩ := specs_exist (d := d) (L := L) hd hL
  exact ⟨c, BG, h1, h2, h3, h4, h5⟩

section Constants

variable (d L N : ℕ) [NeZero L] (BG κ : ℝ)

/-- The radius of the ball of uniqueness of I-4a for the family `G_s`. -/
noncomputable def rho4 : ℝ := c6' d L N (famConst d L BG κ) (gamma1 d / 8)

/-- The constant `c₇` of Theorem I-4b: the smallness of `δ`. -/
noncomputable def c7 : ℝ :=
  min (bgC1 d L N) (min (deltaClose d L N BG κ / (2 * lemma53Const d L))
    (bgC0 d L N / (2 * (cK2' d L N (famConst d L BG κ) * lemma53Const d L + 1))))

/-- The constant `K₄` of Theorem I-4b. -/
noncomputable def K4 : ℝ :=
  lemma53Const d L * (1 + L + 2 * d * (L : ℝ) ^ 2 + (N + 1) * cK2' d L N (famConst d L BG κ))

variable {d L N BG κ}

omit [NeZero L] in
theorem deltaStar'_le_one' {B Γ : ℝ} : deltaStar' d L N B Γ ≤ 1 :=
  (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _))

theorem bgC1_pos' (hd : 0 < d) : 0 < bgC1 d L N := by
  have h1 := approxDelta_pos d L
  have h2 := deltaStar_pos (d := d) (L := L) (N := N) hd
  have h3 := lemma53Const_pos d L
  have h4 := bgC0_pos d L N hd
  have h5 := bgK1_pos d L N
  unfold bgC1
  refine lt_min (lt_min h1 ?_) (lt_min ?_ ?_) <;> positivity

theorem deltaClose_pos (hd : 0 < d) (hBG : 0 ≤ BG) : 0 < deltaClose d L N BG κ := by
  have hB0 : 0 ≤ famConst d L BG κ := by
    have := famConst_ge_one (L := L) hBG κ hd; linarith
  have hΓ : 0 < gamma1 d / 8 := by have := gamma1_pos hd; positivity
  have h1 := deltaStar'_pos (d := d) (L := L) (N := N) hB0 hΓ
  have h2 := closeLam_nonneg (d := d) (L := L) (N := N) hB0 hd
  have h3 := closeM0_nonneg (d := d) (L := L) (N := N) hBG hB0
  unfold deltaClose
  refine lt_min h1 (lt_min one_pos (lt_min ?_ ?_)) <;> positivity

theorem deltaClose_le_deltaStar' : deltaClose d L N BG κ ≤
    deltaStar' d L N (famConst d L BG κ) (gamma1 d / 8) := min_le_left _ _

theorem c7_pos (hd : 0 < d) (hBG : 0 ≤ BG) : 0 < c7 d L N BG κ := by
  have hB0 : 0 ≤ famConst d L BG κ := by
    have := famConst_ge_one (L := L) hBG κ hd; linarith
  have h1 := bgC1_pos' (d := d) (L := L) (N := N) hd
  have h2 := deltaClose_pos (d := d) (L := L) (N := N) (κ := κ) hd hBG
  have h3 := bgC0_pos d L N hd
  have h4 := lemma53Const_pos d L
  have h5 := cK2'_nonneg (d := d) (L := L) (N := N) hB0
  unfold c7
  refine lt_min h1 (lt_min ?_ ?_) <;> positivity

end Constants


/-! ### The data of Theorem I-4a from Lemma 5.3 -/

section Data

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ}

/-- The hypotheses of Proposition 5.1 are the hypotheses of Theorem I-4a in mode U. -/
theorem DecHyp.ofProp51 {α₀ : G.Ω 1 → ℂ} {φ₀ δΨ : CTorus d L N₁ m₁ K → Fin N → ℂ}
    {f₁ : G.Ω 1 × Fin N → ℂ} {δ₀ δ₁ : ℝ} (H : Prop51Hyp G a ν α₀ φ₀ δΨ f₁ δ₀ δ₁) :
    DecHyp G a ν true α₀ φ₀ δΨ f₁ δ₀ δ₁ :=
  ⟨H.green, H.δ₀_nn, H.δ₁_nn, H.δ₀_le.trans deltaStar_le_one, H.smooth, H.phiBd, H.alpha0,
    H.f₁_bd, H.dPsi, fun _ => H.g0, fun _ => H.gl⟩

/-- The conditions on `δ` extracted from `δ ≤ c₇`. -/
theorem c7_facts {BG κ δ : ℝ} (hd : 0 < d) (hBG : 0 ≤ BG) (hδ0 : 0 ≤ δ) (hδ : δ ≤ c7 d L N BG κ) :
    δ ≤ bgC1 d L N ∧ lemma53Const d L * δ ≤ deltaClose d L N BG κ / 2 ∧
      cK2' d L N (famConst d L BG κ) * (lemma53Const d L * δ) ≤ bgC0 d L N / 2 := by
  have hC := lemma53Const_pos d L
  have hB0 : 0 ≤ famConst d L BG κ := by
    have := famConst_ge_one (L := L) hBG κ hd; linarith
  have hk := cK2'_nonneg (d := d) (L := L) (N := N) hB0
  have h0 := bgC0_pos d L N hd
  unfold c7 at hδ
  refine ⟨hδ.trans (min_le_left _ _), ?_, ?_⟩
  · have := hδ.trans ((min_le_right _ _).trans (min_le_left _ _))
    rw [le_div_iff₀ (by positivity)] at this
    linarith
  · have := hδ.trans ((min_le_right _ _).trans (min_le_right _ _))
    rw [le_div_iff₀ (by positivity)] at this
    nlinarith

/-- **Lemma 5.3 gives the data of Theorem I-4a**: for data in `Ψ̃^c(δ, ε)` with `δ ≤ c₇`, the
approximate field, `α₀ = 0`, `δΨ = 0`, `f₁ = residual` satisfy the hypotheses of I-4a in mode U
with `δ₀ = δ₁ = C₃ δ`. -/
theorem decHyp_of_data {BG κ δ ε : ℝ} (HB : BgHyp d L K ϱ a ν) (hBG : 0 ≤ BG)
    (hδ0 : 0 < δ) (hδε : δ ≤ ε) (hε : ε ≤ bgC0 d L N) (hδ : δ ≤ c7 d L N BG κ)
    (hνε : ν * ((L : ℝ) ^ K) ^ 2 * ε ^ 2 ≤ δ ^ 2) {D : BgData G N} (W : DataWit G ν δ ε D) :
    DecHyp G a ν true (0 : G.Ω 1 → ℂ) (approxField G a ν D.Ψ D.h) (0 : CTorus d L N₁ m₁ K → Fin N → ℂ)
      (residual G a ν D (approxField G a ν D.Ψ D.h)) (lemma53Const d L * δ)
      (lemma53Const d L * δ) := by
  have hd0 : 0 < d := by have := HB.hd; omega
  obtain ⟨h1, -, -⟩ := c7_facts (L := L) (N := N) hd0 hBG hδ0.le hδ
  obtain ⟨hδa, h2, hC32, -⟩ := bgC1_facts d L N hd0 h1
  have S : ApproxSetting d L K ϱ a ν δ ε :=
    HB.approxSetting hδ0 hδε (hε.trans (bgC0_le d L N)) (approxDelta_le d L hδa).1 hνε
  have hCδ : 0 < lemma53Const d L * δ := mul_pos (lemma53Const_pos d L) hδ0
  exact DecHyp.ofProp51 (prop51Hyp_of_data (N := N) HB S hδa W (by linarith) hC32)

end Data


/-! ### The decoupled background field -/

section Field

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ}

variable (G a ν) in
/-- **The decoupled background field** at the parameters `s`: `(φ, α)` with `α` a fixed point of
`𝒩_s` in the ball `|α|₂ ≤ ρ` for the data `(φ₀, 0, 0, f₀)` of Lemma 5.3 (mode U), and
`φ = φ₀ + δφ` with `δφ = G_s(α)(f₀ - α φ₀)`. -/
structure IsDecBg (ρ : ℝ) (s : DecParams G) (D : BgData G N) (φ : G.Ω 1 × Fin N → ℂ)
    (α : G.Ω 1 → ℂ) : Prop where
  small : Small G α ρ
  fixed : DecFixed G a ν s true (0 : G.Ω 1 → ℂ) (approxField G a ν D.Ψ D.h)
    (residual G a ν D (approxField G a ν D.Ψ D.h)) α
  field : φ = fun p => approxField G a ν D.Ψ D.h p.1 p.2 +
    dphi G (decG G a ν s) (0 : G.Ω 1 → ℂ) (approxField G a ν D.Ψ D.h)
      (residual G a ν D (approxField G a ν D.Ψ D.h)) α p

variable (G a ν) in
open Classical in
/-- The decoupled background field `φ_k(s)` (`0` if there is no unique one; `i4b_exists_unique`
shows that it exists and is unique in the range of Theorem I-4b). -/
noncomputable def decBgField (ρ : ℝ) (s : DecParams G) (D : BgData G N) :
    G.Ω 1 × Fin N → ℂ :=
  if H : ∃! p : (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ), IsDecBg G a ν ρ s D p.1 p.2
    then H.exists.choose.1 else 0

variable (G a ν) in
open Classical in
/-- The decoupled multiplier `α_k(s)`. -/
noncomputable def decBgMult (ρ : ℝ) (s : DecParams G) (D : BgData G N) : G.Ω 1 → ℂ :=
  if H : ∃! p : (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ), IsDecBg G a ν ρ s D p.1 p.2
    then H.exists.choose.2 else 0

theorem decBg_eq {ρ : ℝ} {s : DecParams G} {D : BgData G N} {φ : G.Ω 1 × Fin N → ℂ}
    {α : G.Ω 1 → ℂ} (h : IsDecBg G a ν ρ s D φ α)
    (hu : ∀ φ' α', IsDecBg G a ν ρ s D φ' α' → φ' = φ ∧ α' = α) :
    decBgField G a ν ρ s D = φ ∧ decBgMult G a ν ρ s D = α := by
  classical
  have H : ∃! p : (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ), IsDecBg G a ν ρ s D p.1 p.2 :=
    ⟨(φ, α), h, fun p hp => Prod.ext (hu p.1 p.2 hp).1 (hu p.1 p.2 hp).2⟩
  have e : H.exists.choose = (φ, α) := H.unique H.exists.choose_spec h
  refine ⟨?_, ?_⟩
  · unfold decBgField; simp only [H, ↓reduceDIte]; rw [e]
  · unfold decBgMult; simp only [H, ↓reduceDIte]; rw [e]

/-- **Theorem I-4b (existence, uniqueness, bounds)**: for `s` with `|s_P| ≤ e^{κ₁}` and data in
`Ψ̃^c(δ, ε)` with the hypotheses of Theorem 5.2, `δ ≤ c₇`: the decoupled background field exists
and is unique in the ball, and it satisfies the bounds P2 (1.15) with the constant `K₄ δ`
(`BgBounds`), `|δφ|₀, |∂δφ|₁, |Δ δφ|₂, |δα|₂ ≤ K₂' C₃ δ`. -/
theorem i4b_exists_unique {c BG : ℝ} (hS : DecSpecs d L c BG) (S : DGSetting G a ν)
    (HB : BgHyp d L K ϱ a ν) {κ : ℝ} (hκ : 0 ≤ κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {s : DecParams G}
    (hs : ∀ P, ‖s P‖ ≤ Real.exp κ) {δ ε : ℝ} (hδ0 : 0 < δ) (hδε : δ ≤ ε)
    (hε : ε ≤ bgC0 d L N) (hδ : δ ≤ c7 d L N BG κ)
    (hνε : ν * ((L : ℝ) ^ K) ^ 2 * ε ^ 2 ≤ δ ^ 2) {D : BgData G N} (hD : InDomainC G ν δ ε D) :
    ∃ (φ : G.Ω 1 × Fin N → ℂ) (α : G.Ω 1 → ℂ),
      IsDecBg G a ν (rho4 d L N BG κ) s D φ α ∧
      (∀ φ' α', IsDecBg G a ν (rho4 d L N BG κ) s D φ' α' → φ' = φ ∧ α' = α) ∧
      Small G α (cK2' d L N (famConst d L BG κ) * (lemma53Const d L * δ)) ∧
      SupBounds G (fun p => φ p - approxField G a ν D.Ψ D.h p.1 p.2)
        (cK2' d L N (famConst d L BG κ) * (lemma53Const d L * δ)) ∧
      BgBounds G D φ α (K4 d L N BG κ * δ) := by
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
    i4a_exists_unique hS.fam G S hκ hM hs Hd hle hle
  rw [pertSource_zeroΨ] at hfix hsup huniq
  have hB0 : 0 ≤ famConst d L BG κ := by
    have := famConst_ge_one (L := L) hBG κ hd0; linarith
  have hk := cK2'_nonneg (d := d) (L := L) (N := N) hB0
  have hid : IsDecBg G a ν (rho4 d L N BG κ) s D
      (fun p => approxField G a ν D.Ψ D.h p.1 p.2 + dphi G (decG G a ν s) (0 : G.Ω 1 → ℂ)
        (approxField G a ν D.Ψ D.h) (residual G a ν D (approxField G a ν D.Ψ D.h)) δα p) δα :=
    ⟨hsm, hfix, rfl⟩
  refine ⟨_, δα, hid, ?_, hsK, ?_, ?_⟩
  · intro φ' α' h'
    have e := huniq α' h'.small h'.fixed
    subst e
    exact ⟨h'.field, rfl⟩
  · have : (fun p : G.Ω 1 × Fin N => (approxField G a ν D.Ψ D.h p.1 p.2 + dphi G (decG G a ν s)
        (0 : G.Ω 1 → ℂ) (approxField G a ν D.Ψ D.h)
        (residual G a ν D (approxField G a ν D.Ψ D.h)) δα p) -
        approxField G a ν D.Ψ D.h p.1 p.2) = dphi G (decG G a ν s) (0 : G.Ω 1 → ℂ)
        (approxField G a ν D.Ψ D.h) (residual G a ν D (approxField G a ν D.Ψ D.h)) δα := by
      funext p; ring
    rw [this]; exact hsup
  · obtain ⟨hδa, -, hC32, -⟩ := bgC1_facts d L N hd0 h1
    have Sa : ApproxSetting d L K ϱ a ν δ ε :=
      HB.approxSetting hδ0 hδε (hε.trans (bgC0_le d L N)) (approxDelta_le d L hδa).1 hνε
    have hl := lemma53 Sa hδa D W.real W (fun x hx i => W.real_Ψ hx i) (fun x hx i => W.real_h hx i)
    have hsup' : SupBounds G (dphi G (decG G a ν s) (0 : G.Ω 1 → ℂ)
        (approxField G a ν D.Ψ D.h) (residual G a ν D (approxField G a ν D.Ψ D.h)) δα)
        (cK2' d L N (famConst d L BG κ) * (lemma53Const d L * δ)) := hsup
    have hkk : 0 ≤ cK2' d L N (famConst d L BG κ) * (lemma53Const d L * δ) := by positivity
    have hX : 0 ≤ (1 + L + 2 * d * (L : ℝ) ^ 2) * (lemma53Const d L * δ) := by positivity
    have hNk : 0 ≤ (N : ℝ) * (cK2' d L N (famConst d L BG κ) * (lemma53Const d L * δ)) := by
      positivity
    have e : K4 d L N BG κ * δ = (1 + L + 2 * d * (L : ℝ) ^ 2) * (lemma53Const d L * δ) +
        N * (cK2' d L N (famConst d L BG κ) * (lemma53Const d L * δ)) +
        cK2' d L N (famConst d L BG κ) * (lemma53Const d L * δ) := by
      unfold K4; ring
    refine bgBounds_of_parts (HB.green (G := G)).sep_gt_one (by have := HB.hL; omega) hCδ.le
      (by positivity) hl.2.1 (fun y hy => (hl.1 y hy).2) hsup' (fun x => (hsK x).trans ?_)
      (by linarith)
    linarith

/-- The identification of a fixed point of `𝒩_1` in the ball with a solution of (P-1), (P-2). -/
theorem isPerturbed_of_decFixed_one {c BG : ℝ} (hS : DecSpecs d L c BG) (S : DGSetting G a ν)
    {κ : ℝ} (hκ : 0 ≤ κ) (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    {α₀ : G.Ω 1 → ℂ} {φ₀ δΨ : CTorus d L N₁ m₁ K → Fin N → ℂ} {f₁ : G.Ω 1 × Fin N → ℂ}
    {δ₀ δ₁ : ℝ} (H : DecHyp G a ν true α₀ φ₀ δΨ f₁ δ₀ δ₁)
    (hδ₀ : δ₀ ≤ deltaStar' d L N (famConst d L BG κ) (gamma1 d / 8))
    (hδ₁ : δ₁ ≤ deltaStar' d L N (famConst d L BG κ) (gamma1 d / 8)) {δα : G.Ω 1 → ℂ}
    (hfix : DecFixed G a ν (fun _ => 1) true α₀ φ₀ (pertSource G a δΨ f₁) δα)
    (hsmall : Small G δα (rho4 d L N BG κ)) :
    IsPerturbed G a ν α₀ φ₀ (pertSource G a δΨ f₁)
      (dphi G (decG G a ν (fun _ => 1)) α₀ φ₀ (pertSource G a δΨ f₁) δα) δα := by
  have hd0 : 0 < d := by have := S.hd; omega
  have hE : 1 ≤ Real.exp (N0 d L * κ) := Real.one_le_exp (by unfold N0; positivity)
  have hMc : c ≤ (L : ℝ) ^ m₁ := by
    refine le_trans ?_ hM
    have := hS.one.1; nlinarith
  set B : ℝ := famConst d L BG κ with hB
  set Γ : ℝ := gamma1 d / 8 with hΓdef
  have hB0 : 0 ≤ B := by have := famConst_ge_one (L := L) hS.fam.2.1 κ hd0; linarith
  have hΓ : 0 < Γ := by have := gamma1_pos hd0; positivity
  have hC := coreHyp'_small (d := d) (L := L) (N := N) hB0 hΓ H.δ₀_nn H.δ₁_nn hδ₀ hδ₁
  have hfam : ∀ δα' : G.Ω 1 → ℂ, Small G δα' (c6' d L N B Γ) →
      dphi G (decG G a ν (fun _ => 1)) α₀ φ₀ (pertSource G a δΨ f₁) δα' =
        dphi G (greenD G a ν) α₀ φ₀ (pertSource G a δΨ f₁) δα' := by
    intro δα' hs
    have hsm' : Small G (α₀ + δα') Γ := H.setup.poly hs (by linarith [hC.poly, hC.ρ_nn])
    unfold dphi
    rw [decG_one hS.one S hMc (admPot_of_small hd0 hsm')]
  have hfixG : Nmap G (dirichletOperator G a ν α₀) true φ₀ (pertSource G a δΨ f₁)
      (dphi G (greenD G a ν) α₀ φ₀ (pertSource G a δΨ f₁) δα) = δα := by
    rw [← hfam δα hsmall]; exact hfix
  have hpoly : δ₀ + 2 * c6' d L N B Γ ≤ gamma1 d := by linarith [hC.poly]
  have hP := perturbed_of_fixed H.green H.alpha0 hC.ρ_nn hpoly hsmall hfixG
  rw [hfam δα hsmall]; exact hP

/-- **Theorem I-4b (i), `s = 1`**: the decoupled background field at `s ≡ 1` is the background
field `bgFieldC` of Theorem 5.2 (and the multiplier is `bgMultC`). -/
theorem i4b_one {c BG : ℝ} (hS : DecSpecs d L c BG) (S : DGSetting G a ν)
    (HB : BgHyp d L K ϱ a ν) {κ : ℝ} (hκ : 0 ≤ κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δ ε : ℝ} (hδ0 : 0 < δ) (hδε : δ ≤ ε)
    (hε : ε ≤ bgC0 d L N) (hδ : δ ≤ c7 d L N BG κ)
    (hνε : ν * ((L : ℝ) ^ K) ^ 2 * ε ^ 2 ≤ δ ^ 2) {D : BgData G N} (hD : InDomainC G ν δ ε D)
    {φ : G.Ω 1 × Fin N → ℂ} {α : G.Ω 1 → ℂ}
    (h : IsDecBg G a ν (rho4 d L N BG κ) (fun _ => 1) D φ α) :
    IsSmallSolution G a ν (bgC0 d L N) D φ α ∧ bgFieldC G a ν (bgC0 d L N) D = φ ∧
      bgMultC G a ν (bgC0 d L N) D = α := by
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
  have hfix : DecFixed G a ν (fun _ => 1) true (0 : G.Ω 1 → ℂ) (approxField G a ν D.Ψ D.h)
      (pertSource G a (0 : CTorus d L N₁ m₁ K → Fin N → ℂ)
        (residual G a ν D (approxField G a ν D.Ψ D.h))) α := by
    rw [pertSource_zeroΨ]; exact h.fixed
  have hP := isPerturbed_of_decFixed_one hS S hκ hM Hd hle hle hfix h.small
  rw [pertSource_zeroΨ] at hP
  have hEL : IsEL G a ν D φ α := by
    have := (isPerturbed_iff_isEL (a := a) (ν := ν) D (approxField G a ν D.Ψ D.h) _ α).1 hP
    rw [h.field]
    convert this using 1
  have hc0 := bgC0_pos d L N hd0
  obtain ⟨φ', α', hd', hu', hsm', -, -⟩ := i4b_exists_unique hS S HB hκ hM
    (s := fun _ => 1) (fun P => by simpa using Real.one_le_exp hκ) hδ0 hδε hε hδ hνε hD
  obtain ⟨e1, e2⟩ := hu' φ α h
  have hsol : IsSmallSolution G a ν (bgC0 d L N) D φ α := by
    refine ⟨hEL, fun x => ?_⟩
    have := hsm' x
    rw [e2]
    have := h3
    linarith [hsm' x]
  obtain ⟨φ'', α'', hs'', -, hu''⟩ := theorem52_exists (N := N) HB hδ0 hδε hε h1 hνε hD
  have hun : ∀ φ₂ α₂, IsSmallSolution G a ν (bgC0 d L N) D φ₂ α₂ → φ₂ = φ ∧ α₂ = α := by
    intro φ₂ α₂ h₂
    obtain ⟨a1, a2⟩ := hu'' φ₂ α₂ h₂
    obtain ⟨b1, b2⟩ := hu'' φ α hsol
    exact ⟨a1.trans b1.symm, a2.trans b2.symm⟩
  exact ⟨hsol, (bgFieldC_eq hsol hun).1, (bgFieldC_eq hsol hun).2⟩

end Field

end Balaban.Localization
