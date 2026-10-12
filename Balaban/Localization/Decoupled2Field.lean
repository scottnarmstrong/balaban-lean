/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.Decoupled2Close
public import Balaban.Localization.DecoupledField

/-!
# Theorem I-4a: the decoupled Green family, for a cover `C` and an operator `H`

The Lipschitz bound `dg4_lipschitz_fwd'` and the specification `FamSpec` of the family
`α ↦ G_s(α)` (a `GreenFamily` on the polydisc `|α|₂ ≤ γ₁/8`), with the constants `(c, B_G)` that
depend on the constants `Kc`, `Cx` of the pair (`CoverBase`).
-/

@[expose] public section

namespace Balaban.Localization.Dec2

open Balaban Balaban.Multiscale Balaban.Background Balaban.Reflection Finset Matrix

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {C : DecCover d L N₁ m₁ K} {H : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ}
  {Kc Cx : ℝ} {α : H.Ω 1 → ℂ}

/-- **(DG4), the Lipschitz bound in `A`**, including the gradient bond pointing into a site
(`fwd'`): for `|A|₂, |A'|₂ ≤ γ₁/8` the increments of the pointwise quantities of
`G_s(A) f - G_s(A') f` are bounded by `4 B_G e^{N₀κ₁} γ₁⁻¹ |A - A'|₂ |f|₂`. -/
theorem dg4_lipschitz_fwd' (hd : 3 ≤ d) (hL : 3 ≤ L) (hKc : 0 ≤ Kc) (hCx : 0 ≤ Cx) :
    ∃ cstar BG : ℝ, 0 ≤ cstar ∧ 0 ≤ BG ∧ ∀ {N₁ m₁ K : ℕ} [NeZero N₁] {ϱ : ℝ}
      (C : DecCover d L N₁ m₁ K) (H : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) {a : ℕ → ℝ} {ν : ℝ}, CoverBase C H a ν Kc Cx →
      ∀ {κ : ℝ}, 0 ≤ κ → cstar * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁ →
      ∀ {s : DecParams C}, (∀ P, ‖s P‖ ≤ Real.exp κ) →
      ∀ (f : H.Ω 1 → ℂ) {Cb : ℝ}, 0 ≤ Cb →
      (∀ x : H.Ω 1, (H.spacing (x : CTorus d L N₁ m₁ K)) ^ 2 * ‖f x‖ ≤ Cb) →
      ∀ {A A' : H.Ω 1 → ℂ},
      (∀ z : H.Ω 1, (H.spacing (z : CTorus d L N₁ m₁ K)) ^ 2 * ‖A z‖ ≤ gamma1 d / 8) →
      (∀ z : H.Ω 1, (H.spacing (z : CTorus d L N₁ m₁ K)) ^ 2 * ‖A' z‖ ≤ gamma1 d / 8) →
      ∀ {ε : ℝ}, 0 ≤ ε →
      (∀ z : H.Ω 1, (H.spacing (z : CTorus d L N₁ m₁ K)) ^ 2 * ‖A z - A' z‖ ≤ ε) →
      ∀ x ∈ H.Ω 1,
      ‖(zeroExt (H.Ω 1) (Gs C H a ν A (extS C s) *ᵥ f) x -
        zeroExt (H.Ω 1) (Gs C H a ν A' (extS C s) *ᵥ f) x)‖ ≤
        4 * (BG * Real.exp (N0 d L * κ) * Cb) * ε / gamma1 d ∧
      (∀ μ : Fin d, H.spacing x *
        ‖((zeroExt (H.Ω 1) (Gs C H a ν A (extS C s) *ᵥ f) (x + Pi.single μ 1) -
          zeroExt (H.Ω 1) (Gs C H a ν A (extS C s) *ᵥ f) x) -
          (zeroExt (H.Ω 1) (Gs C H a ν A' (extS C s) *ᵥ f) (x + Pi.single μ 1) -
          zeroExt (H.Ω 1) (Gs C H a ν A' (extS C s) *ᵥ f) x))‖ ≤
        4 * (BG * Real.exp (N0 d L * κ) * Cb) * ε / gamma1 d) ∧
      (∀ μ : Fin d, x + Pi.single μ 1 ∈ H.Ω 1 → H.spacing (x + Pi.single μ 1) *
        ‖((zeroExt (H.Ω 1) (Gs C H a ν A (extS C s) *ᵥ f) (x + Pi.single μ 1) -
          zeroExt (H.Ω 1) (Gs C H a ν A (extS C s) *ᵥ f) x) -
          (zeroExt (H.Ω 1) (Gs C H a ν A' (extS C s) *ᵥ f) (x + Pi.single μ 1) -
          zeroExt (H.Ω 1) (Gs C H a ν A' (extS C s) *ᵥ f) x))‖ ≤
        4 * (BG * Real.exp (N0 d L * κ) * Cb) * ε / gamma1 d) ∧
      (H.spacing x) ^ 2 * ‖∑ μ : Fin d, ((2 * zeroExt (H.Ω 1) (Gs C H a ν A (extS C s) *ᵥ f) x -
        zeroExt (H.Ω 1) (Gs C H a ν A (extS C s) *ᵥ f) (x + Pi.single μ 1) -
        zeroExt (H.Ω 1) (Gs C H a ν A (extS C s) *ᵥ f) (x - Pi.single μ 1)) -
        (2 * zeroExt (H.Ω 1) (Gs C H a ν A' (extS C s) *ᵥ f) x -
        zeroExt (H.Ω 1) (Gs C H a ν A' (extS C s) *ᵥ f) (x + Pi.single μ 1) -
        zeroExt (H.Ω 1) (Gs C H a ν A' (extS C s) *ᵥ f) (x - Pi.single μ 1)))‖ ≤
        4 * (BG * Real.exp (N0 d L * κ) * Cb) * ε / gamma1 d := by
  obtain ⟨cstar, BG, hc, hB, Hh⟩ := dg2_sup (d := d) (L := L) (Kc := Kc) (Cx := Cx) hd hL hKc hCx
  refine ⟨cstar, BG, hc, hB, ?_⟩
  intro N₁ m₁ K _ ϱ C H a ν S κ hκ hMκ s hs f Cb hC hfC A A' hA hA' ε hε hAA x hx
  have hd0 : 0 < d := by omega
  have hγ1 : 0 < gamma1 d := gamma1_pos hd0
  set V : ℝ := BG * Real.exp (N0 d L * κ) * Cb with hV
  set ε' : ℝ := min ε (gamma1 d / 4) with hε'
  have hε'0 : 0 ≤ ε' := le_min hε (by positivity)
  have hε'4 : ε' ≤ gamma1 d / 4 := min_le_right _ _
  have hAA' : ∀ z : H.Ω 1, (H.spacing (z : CTorus d L N₁ m₁ K)) ^ 2 * ‖A z - A' z‖ ≤ ε' := by
    intro z
    refine le_min (hAA z) ?_
    calc (H.spacing (z : CTorus d L N₁ m₁ K)) ^ 2 * ‖A z - A' z‖
        ≤ (H.spacing (z : CTorus d L N₁ m₁ K)) ^ 2 * (‖A z‖ + ‖A' z‖) :=
          mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by positivity)
      _ = (H.spacing (z : CTorus d L N₁ m₁ K)) ^ 2 * ‖A z‖ +
          (H.spacing (z : CTorus d L N₁ m₁ K)) ^ 2 * ‖A' z‖ := by ring
      _ ≤ gamma1 d / 4 := by linarith [hA z, hA' z]
  have hε'ε : ε' ≤ ε := min_le_left _ _
  have hV0 : 0 ≤ V := by positivity
  -- the admissibility conversions
  have hrpos : ∀ z : H.Ω 1, 0 < (H.spacing (z : CTorus d L N₁ m₁ K)) ^ 2 := fun z => by
    have := spacing_pos H (x := (z : CTorus d L N₁ m₁ K)); positivity
  have hadm_le : ∀ B : H.Ω 1 → ℂ,
      (∀ z : H.Ω 1, (H.spacing (z : CTorus d L N₁ m₁ K)) ^ 2 * ‖B z‖ ≤ gamma1 d) → AdmPot H B := by
    intro B hB z
    have h := hB z
    have hz := hrpos z
    unfold gamma1 at h
    rw [le_div_iff₀ (by positivity)]
    linarith
  have hw1 : IsWeight H (gammaW d) (fun _ => (1 : ℝ)) := IsWeight.one H (gammaW_nonneg hd0)
  have hcase : ∀ B : H.Ω 1 → ℂ,
      (∀ z : H.Ω 1, (H.spacing (z : CTorus d L N₁ m₁ K)) ^ 2 * ‖B z‖ ≤ gamma1 d) →
      IsUnit (1 - Kcal C H a ν B (extS C s)) ∧
      SupBdW H (fun _ => (1 : ℝ)) (zeroExt (H.Ω 1) (Gs C H a ν B (extS C s) *ᵥ f)) V := by
    intro B hB
    have hs' : ∀ P, ‖extS C s P‖ ≤ Real.exp κ := by
      intro P
      unfold extS
      split_ifs with h
      · exact hs ⟨P, h⟩
      · simpa using Real.one_le_exp hκ
    exact Hh C H S (hadm_le B hB) hκ hMκ hs' hw1 f hC (fun z => by simpa using hfC z)
  have hanal : ∀ (B : H.Ω 1 → ℂ), (∀ z : H.Ω 1,
      (H.spacing (z : CTorus d L N₁ m₁ K)) ^ 2 * ‖B z‖ < gamma1 d) → ∀ y : CTorus d L N₁ m₁ K,
      AnalyticAt ℂ (fun B' : H.Ω 1 → ℂ => zeroExt (H.Ω 1) (Gs C H a ν B' (extS C s) *ᵥ f) y) B := by
    intro B hB y
    have hB' : ∀ z : H.Ω 1, (H.spacing (z : CTorus d L N₁ m₁ K)) ^ 2 * ‖B z‖ ≤ gamma1 d :=
      fun z => (hB z).le
    obtain ⟨hU, -⟩ := hcase B hB'
    have hMat := matAt_Gs S (e := (s, B)) (hadm_le B hB') hU
    have h := analyticAt_zeroExt_mulVec hMat f y
    exact h.comp (f := fun B' : H.Ω 1 → ℂ => (s, B')) (x := B)
      (AnalyticAt.prod (analyticAt_const (v := s)) analyticAt_id)
  have run : ∀ Fo : (H.Ω 1 → ℂ) → ℂ,
      (∀ B : H.Ω 1 → ℂ, (∀ z : H.Ω 1,
        (H.spacing (z : CTorus d L N₁ m₁ K)) ^ 2 * ‖B z‖ < gamma1 d) → AnalyticAt ℂ Fo B) →
      (∀ B : H.Ω 1 → ℂ, (∀ z : H.Ω 1,
        (H.spacing (z : CTorus d L N₁ m₁ K)) ^ 2 * ‖B z‖ ≤ gamma1 d) → ‖Fo B‖ ≤ V) →
      ‖Fo A - Fo A'‖ ≤ 4 * V * ε / gamma1 d := by
    intro Fo hFa hFb
    have := lipschitz_obs (fun z : H.Ω 1 => (H.spacing (z : CTorus d L N₁ m₁ K)) ^ 2) hrpos hγ1 Fo
      hFa hFb hA' hε'0 hε'4 hAA'
    refine this.trans ?_
    have : 4 * V * ε' / gamma1 d ≤ 4 * V * ε / gamma1 d := by
      apply div_le_div_of_nonneg_right _ hγ1.le
      nlinarith
    exact this
  have hsp := (spacing_pos H (x := x)).le
  have hnrm : ∀ (r : ℝ), 0 ≤ r → ∀ z : ℂ, ‖(r : ℂ) * z‖ = r * ‖z‖ := fun r hr z => by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]
  refine ⟨?_, fun μ => ?_, fun μ hxe => ?_, ?_⟩
  · have := run (fun B => zeroExt (H.Ω 1) (Gs C H a ν B (extS C s) *ᵥ f) x)
      (fun B hB => hanal B hB x)
      (fun B hB => by
        have := ((hcase B hB).2.val x hx)
        simpa using this)
    simpa using this
  · have := run (fun B => ((H.spacing x : ℝ) : ℂ) *
        (zeroExt (H.Ω 1) (Gs C H a ν B (extS C s) *ᵥ f) (x + Pi.single μ 1) -
          zeroExt (H.Ω 1) (Gs C H a ν B (extS C s) *ᵥ f) x))
      (fun B hB => analyticAt_const.mul ((hanal B hB (x + Pi.single μ 1)).sub (hanal B hB x)))
      (fun B hB => by
        have h := ((hcase B hB).2.fwd x hx μ)
        rw [hnrm _ hsp]
        simpa using h)
    rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hsp] at this
    exact this
  · have hsp' := (spacing_pos H (x := x + Pi.single μ 1)).le
    have hnrm' : ∀ z : ℂ, ‖((H.spacing (x + Pi.single μ 1) : ℝ) : ℂ) * z‖ =
        H.spacing (x + Pi.single μ 1) * ‖z‖ := fun z => by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hsp']
    have := run (fun B => ((H.spacing (x + Pi.single μ 1) : ℝ) : ℂ) *
        (zeroExt (H.Ω 1) (Gs C H a ν B (extS C s) *ᵥ f) (x + Pi.single μ 1) -
          zeroExt (H.Ω 1) (Gs C H a ν B (extS C s) *ᵥ f) x))
      (fun B hB => analyticAt_const.mul ((hanal B hB (x + Pi.single μ 1)).sub (hanal B hB x)))
      (fun B hB => by
        have h := ((hcase B hB).2.fwd' x hx μ hxe)
        rw [hnrm']
        simpa using h)
    rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hsp'] at this
    exact this
  · have := run (fun B => (((H.spacing x) ^ 2 : ℝ) : ℂ) *
        ∑ μ : Fin d, (2 * zeroExt (H.Ω 1) (Gs C H a ν B (extS C s) *ᵥ f) x -
          zeroExt (H.Ω 1) (Gs C H a ν B (extS C s) *ᵥ f) (x + Pi.single μ 1) -
          zeroExt (H.Ω 1) (Gs C H a ν B (extS C s) *ᵥ f) (x - Pi.single μ 1)))
      (fun B hB => analyticAt_const.mul (Finset.analyticAt_fun_sum _ fun μ _ =>
        (((analyticAt_const (v := (2 : ℂ))).mul (hanal B hB x)).sub
          (hanal B hB (x + Pi.single μ 1))).sub (hanal B hB (x - Pi.single μ 1))))
      (fun B hB => by
        have h := ((hcase B hB).2.lap x hx)
        rw [hnrm _ (by positivity)]
        simpa using h)
    rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)] at this
    rw [← Finset.sum_sub_distrib] at this
    exact this



/-- **The specification of the decoupled Green family** with the constants `(c, B_G)`: for
`M₁ ≥ c e^{N₀ κ₁}` and parameters `|s_P| ≤ e^{κ₁}`, `α ↦ G_s(α)` is a `GreenFamily` on the
polydisc `|α|₂ ≤ γ₁/8` with constant `famConst d L B_G κ₁` (R-B2 of LOCALIZATION.md §3.3), and
`G_s(α) g` has the sup bounds including the Laplacian with the same constant. -/
def FamSpec (d L : ℕ) [NeZero L] (Kc Cx cstar BG : ℝ) : Prop :=
  0 ≤ cstar ∧ 0 ≤ BG ∧ ∀ {N₁ m₁ K : ℕ} [NeZero N₁] {ϱ : ℝ}
      (C : DecCover d L N₁ m₁ K) (H : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) {a : ℕ → ℝ} {ν : ℝ}, CoverBase C H a ν Kc Cx →
      ∀ {κ : ℝ}, 0 ≤ κ → cstar * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁ →
      ∀ {s : DecParams C}, (∀ P, ‖s P‖ ≤ Real.exp κ) → ∀ (N : ℕ),
      (GreenFamily H N (fun α => Gs C H a ν α (extS C s)) (famConst d L BG κ) (gamma1 d / 8) ∧
      ∀ {α : H.Ω 1 → ℂ}, Small H α (gamma1 d / 8) → ∀ (g : H.Ω 1 × Fin N → ℂ) {Cb : ℝ}, 0 ≤ Cb →
        SrcBound H g Cb →
        SupBounds H (liftOp N (Gs C H a ν α (extS C s)) *ᵥ g) (famConst d L BG κ * Cb)) ∧
      ∀ {α : H.Ω 1 → ℂ}, AdmPot H α → IsUnit (1 - Kcal C H a ν α (extS C s))

theorem FamSpec.mono_c {d L : ℕ} [NeZero L] {c c' BG : ℝ} (h : FamSpec d L Kc Cx c BG) (hc : c ≤ c') :
    FamSpec d L Kc Cx c' BG := by
  have hn : 0 ≤ c' := h.1.trans hc
  refine ⟨hn, h.2.1, ?_⟩
  intro N₁ m₁ K _ ϱ C H a ν S κ hκ hM s hs N
  exact h.2.2 C H S hκ (le_trans (mul_le_mul_of_nonneg_right hc (Real.exp_pos _).le) hM) hs N

theorem FamSpec.mono_BG {d L : ℕ} [NeZero L] {c BG BG' : ℝ} (h : FamSpec d L Kc Cx c BG)
    (hB : BG ≤ BG') : FamSpec d L Kc Cx c BG' := by
  refine ⟨h.1, h.2.1.trans hB, ?_⟩
  intro N₁ m₁ K _ ϱ C H a ν S κ hκ hM s hs N
  obtain ⟨⟨hfam, hsup⟩, hunit⟩ := h.2.2 C H S hκ hM hs N
  have hd0 : 0 < d := by have := S.hd; omega
  have hle := famConst_mono (d := d) (L := L) hd0 hB κ
  have hB0 : 0 ≤ famConst d L BG κ := by
    have := famConst_ge_one (L := L) h.2.1 κ hd0; linarith
  refine ⟨⟨⟨hB0.trans hle, ?_, ?_⟩, ?_⟩, hunit⟩
  · intro α hα g Cb hC hg
    exact (hfam.bound hα g hC hg).mono (mul_le_mul_of_nonneg_right hle hC)
  · intro α α' hα hα' g Cb Δ hC hg hΔ0 hΔ
    refine (hfam.diff hα hα' g hC hg hΔ0 hΔ).mono ?_
    have h1 : famConst d L BG κ * Cb ≤ famConst d L BG' κ * Cb :=
      mul_le_mul_of_nonneg_right hle hC
    have h2 : Δ * (famConst d L BG κ * Cb) ≤ Δ * (famConst d L BG' κ * Cb) :=
      mul_le_mul_of_nonneg_left h1 hΔ0
    exact mul_le_mul hle h2 (mul_nonneg hΔ0 (mul_nonneg hB0 hC)) (hB0.trans hle)
  · intro α hα g Cb hC hg
    exact (hsup hα g hC hg).mono (mul_le_mul_of_nonneg_right hle hC)

/-- **The decoupled Green operators form a Green family.** -/
theorem decGreenFamily (hd : 3 ≤ d) (hL : 3 ≤ L) (hKc : 0 ≤ Kc) (hCx : 0 ≤ Cx) : ∃ cstar BG : ℝ, FamSpec d L Kc Cx cstar BG := by
  obtain ⟨c1, B1, hc1, hB1, Hh1⟩ := dg2_sup (d := d) (L := L) (Kc := Kc) (Cx := Cx) hd hL hKc hCx
  obtain ⟨c2, B2, hc2, hB2, Hh2⟩ := dg4_lipschitz_fwd' (d := d) (L := L) (Kc := Kc) (Cx := Cx) hd hL hKc hCx
  have hd0 : 0 < d := by omega
  have hγ := gamma1_pos hd0
  refine ⟨max c1 c2, max B1 B2, le_max_of_le_left hc1, le_max_of_le_left hB1, ?_⟩
  intro N₁ m₁ K _ ϱ C H a ν S κ hκ hMκ s hs N
  have hE : 0 < Real.exp (N0 d L * κ) := Real.exp_pos _
  have hMκ1 : c1 * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁ :=
    le_trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hE.le) hMκ
  have hMκ2 : c2 * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁ :=
    le_trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hE.le) hMκ
  have hBG : 0 ≤ max B1 B2 := le_max_of_le_left hB1
  have hϱ := S.one_lt_rho
  have hL2 : 2 ≤ L := by omega
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have hs' : ∀ P, ‖extS C s P‖ ≤ Real.exp κ := by
    intro P
    unfold extS
    split_ifs with h
    · exact hs ⟨P, h⟩
    · simpa using Real.one_le_exp hκ
  set b : ℝ := max B1 B2 * Real.exp (N0 d L * κ) with hb
  have hb0 : 0 ≤ b := by positivity

  have hw1 : IsWeight H (gammaW d) (fun _ => (1 : ℝ)) := IsWeight.one H (gammaW_nonneg hd0)
  have hFam : 1 ≤ famConst d L (max B1 B2) κ := famConst_ge_one hBG κ hd0
  have hLb : (L : ℝ) * b ≤ famConst d L (max B1 B2) κ := by
    unfold famConst
    have : 0 ≤ (L : ℝ) * (4 * (max B1 B2 * Real.exp (N0 d L * κ)) / gamma1 d) := by positivity
    rw [hb]; linarith
  have hLl : (L : ℝ) * (4 * b / gamma1 d) ≤ famConst d L (max B1 B2) κ := by
    unfold famConst
    have : 0 ≤ (L : ℝ) * (max B1 B2 * Real.exp (N0 d L * κ)) := by positivity
    rw [hb]; linarith
  have hsup : ∀ {α : H.Ω 1 → ℂ}, Small H α (gamma1 d / 8) → ∀ (g : H.Ω 1 × Fin N → ℂ) {Cb : ℝ},
      0 ≤ Cb → SrcBound H g Cb →
      SupBounds H (liftOp N (Gs C H a ν α (extS C s)) *ᵥ g) (famConst d L (max B1 B2) κ * Cb) := by
    intro α hα g Cb hC hg
    have hadm := admPot_of_small hd0 hα
    have hsc := supBounds_liftOp (N := N) (G := H) (M := Gs C H a ν α (extS C s)) hϱ hL2 hb0
      (fun f C' hC' hf => (((Hh1 C H S hadm hκ hMκ1 hs' hw1 f hC' (fun x => by simpa using hf x)).2).mono
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hE.le) hC')))
      g hC hg
    refine hsc.mono ?_
    calc (L : ℝ) * (b * Cb) = (L * b) * Cb := by ring
      _ ≤ famConst d L (max B1 B2) κ * Cb := mul_le_mul_of_nonneg_right hLb hC
  have hunit : ∀ {α : H.Ω 1 → ℂ}, AdmPot H α → IsUnit (1 - Kcal C H a ν α (extS C s)) := by
    intro α hα
    exact (Hh1 C H S hα hκ hMκ1 hs' hw1 (0 : H.Ω 1 → ℂ) (Cb := 0) le_rfl (by simp)).1
  refine ⟨⟨⟨by linarith, ?_, ?_⟩, hsup⟩, hunit⟩
  · intro α hα g Cb hC hg
    exact (Balaban.Background.SupBounds.star (hsup hα g hC hg))
  · intro α α' hα hα' g Cb Δ hC hg hΔ0 hΔ
    have hadm := admPot_of_small hd0 hα
    have hadm' := admPot_of_small hd0 hα'
    have hdiff := starBound_sub_liftOp (N := N) (G := H) (M := Gs C H a ν α (extS C s))
      (M' := Gs C H a ν α' (extS C s)) hϱ hL2 (b := 4 * b * Δ / gamma1 d) (by positivity)
      (fun f C' hC' hf x hx => by
        obtain ⟨v1, v2, v3, -⟩ := Hh2 C H S hκ hMκ2 hs f hC' (fun z => hf z) hα hα' hΔ0 hΔ x hx
        have hm : 4 * (B2 * Real.exp (N0 d L * κ) * C') * Δ / gamma1 d ≤
            4 * b * Δ / gamma1 d * C' := by
          rw [hb]
          have : B2 * Real.exp (N0 d L * κ) ≤ max B1 B2 * Real.exp (N0 d L * κ) :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) hE.le
          calc 4 * (B2 * Real.exp (N0 d L * κ) * C') * Δ / gamma1 d
              = 4 * (B2 * Real.exp (N0 d L * κ)) * Δ / gamma1 d * C' := by ring
            _ ≤ 4 * (max B1 B2 * Real.exp (N0 d L * κ)) * Δ / gamma1 d * C' := by gcongr
        exact ⟨v1.trans hm, fun μ => (v2 μ).trans hm, fun μ hxe => (v3 μ hxe).trans hm⟩)
      g hC hg
    refine hdiff.mono ?_
    set B := famConst d L (max B1 B2) κ with hBdef
    have hB1' : 1 ≤ B := hFam
    have hΔC : 0 ≤ Δ * Cb := by positivity
    calc (L : ℝ) * (4 * b * Δ / gamma1 d * Cb) = (L * (4 * b / gamma1 d)) * (Δ * Cb) := by ring
      _ ≤ B * (Δ * Cb) := mul_le_mul_of_nonneg_right hLl hΔC
      _ ≤ B * (B * (Δ * Cb)) := by
          apply mul_le_mul_of_nonneg_left _ (by linarith)
          nlinarith
      _ = B * (Δ * (B * Cb)) := by ring


end Balaban.Localization.Dec2
