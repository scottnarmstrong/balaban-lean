/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.Decoupled2SolveAnalytic
public import Balaban.Localization.DecoupledFieldClose

/-!
# Theorem I-4a (d): closeness to `s = 1` away from the parameters, for a cover `C` and an operator `H`

`Dg2Spec` and `CloseSpec` are the conclusions of `dg2_sup` and `dg6` for all pairs `(C, H)` with
`CoverBase C H a ν Kc Cx`; `specs_exist` provides one set of constants for all the inputs of I-4a.
-/

@[expose] public section

namespace Balaban.Localization.Dec2

open Balaban Balaban.Multiscale Balaban.Background Balaban.Reflection Finset Matrix

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {C : DecCover d L N₁ m₁ K} {H : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ}
  {Kc Cx : ℝ} {α : H.Ω 1 → ℂ}


/-- The conclusion of `dg2_sup` (weighted pointwise bounds of `G_s`) with the constants
`(c, B_G)`. -/
def Dg2Spec (d L : ℕ) [NeZero L] (Kc Cx cstar BG : ℝ) : Prop :=
  0 ≤ cstar ∧ 0 ≤ BG ∧ ∀ {N₁ m₁ K : ℕ} [NeZero N₁] {ϱ : ℝ}
      (C : DecCover d L N₁ m₁ K) (H : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) {a : ℕ → ℝ} {ν : ℝ}, CoverBase C H a ν Kc Cx →
      ∀ {α : H.Ω 1 → ℂ}, AdmPot H α → ∀ {κ : ℝ}, 0 ≤ κ →
      cstar * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁ →
      ∀ {s : ℕ × CTorus d L N₁ m₁ K → ℂ}, (∀ P, ‖s P‖ ≤ Real.exp κ) →
      ∀ {w : CTorus d L N₁ m₁ K → ℝ}, IsWeight H (gammaW d) w →
      ∀ (f : H.Ω 1 → ℂ) {Cb : ℝ}, 0 ≤ Cb →
      (∀ x : H.Ω 1, w x * (H.spacing (x : CTorus d L N₁ m₁ K)) ^ 2 * ‖f x‖ ≤ Cb) →
      IsUnit (1 - Kcal C H a ν α s) ∧
      SupBdW H w (zeroExt (H.Ω 1) (Gs C H a ν α s *ᵥ f)) (BG * Real.exp (N0 d L * κ) * Cb)

theorem Dg2Spec.mono {c c' BG BG' : ℝ} (h : Dg2Spec d L Kc Cx c BG) (hc : c ≤ c') (hB : BG ≤ BG') :
    Dg2Spec d L Kc Cx c' BG' := by
  refine ⟨h.1.trans hc, h.2.1.trans hB, ?_⟩
  intro N₁ m₁ K _ ϱ C H a ν S α hα κ hκ hM s hs w hw f Cb hC hf
  obtain ⟨hU, hS⟩ := h.2.2 C H S hα hκ
    (le_trans (mul_le_mul_of_nonneg_right hc (Real.exp_pos _).le) hM) hs hw f hC hf
  exact ⟨hU, hS.mono (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hB (Real.exp_pos _).le) hC)⟩

theorem dg2Spec_exists (hd : 3 ≤ d) (hL : 3 ≤ L) (hKc : 0 ≤ Kc) (hCx : 0 ≤ Cx) : ∃ c BG : ℝ, Dg2Spec d L Kc Cx c BG := by
  obtain ⟨c, B, hc, hB, Hh⟩ := dg2_sup (d := d) (L := L) (Kc := Kc) (Cx := Cx) hd hL hKc hCx
  refine ⟨c, B, hc, hB, ?_⟩
  intro N₁ m₁ K _ ϱ C H a ν S α hα κ hκ hM s hs w hw f Cb hC hf
  exact Hh C H S hα hκ hM hs hw f hC hf

/-- The conclusion of `dg6` (closeness of `G_s` to `G_D` away from `W`) with the constants
`(c, B_G)`. -/
def CloseSpec (d L : ℕ) [NeZero L] (Kc Cx cstar BG : ℝ) : Prop :=
  0 ≤ cstar ∧ 0 ≤ BG ∧ ∀ {N₁ m₁ K : ℕ} [NeZero N₁] {ϱ : ℝ}
      (C : DecCover d L N₁ m₁ K) (H : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) {a : ℕ → ℝ} {ν : ℝ}, CoverBase C H a ν Kc Cx →
      ∀ {α : H.Ω 1 → ℂ}, AdmPot H α → ∀ {κ : ℝ}, 0 ≤ κ →
      cstar * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁ →
      ∀ {s : ℕ × CTorus d L N₁ m₁ K → ℂ}, (∀ P, ‖s P‖ ≤ Real.exp κ) →
      ∀ {W : Finset (CTorus d L N₁ m₁ K)},
      (∀ z ∈ C.cubeIdx, C.sProd s z ≠ 1 → intBox z ⊆ W) →
      ∀ (f : H.Ω 1 → ℂ) {Cb : ℝ}, 0 ≤ Cb →
      (∀ x : H.Ω 1, (H.spacing (x : CTorus d L N₁ m₁ K)) ^ 2 * ‖f x‖ ≤ Cb) →
      ∀ x ∈ H.Ω 1,
      ‖Gdiff C H a ν α s f x‖ ≤ BG * Real.exp (N0 d L * κ) * decay (gammaW d) (siteSetDist H W x) * Cb ∧
      (∀ μ : Fin d, H.spacing x * ‖Gdiff C H a ν α s f (x + Pi.single μ 1) -
        Gdiff C H a ν α s f x‖ ≤
        BG * Real.exp (N0 d L * κ) * decay (gammaW d) (siteSetDist H W x) * Cb) ∧
      (H.spacing x) ^ 2 * ‖∑ μ : Fin d, (2 * Gdiff C H a ν α s f x -
        Gdiff C H a ν α s f (x + Pi.single μ 1) - Gdiff C H a ν α s f (x - Pi.single μ 1))‖ ≤
        BG * Real.exp (N0 d L * κ) * decay (gammaW d) (siteSetDist H W x) * Cb

theorem CloseSpec.mono {c c' BG BG' : ℝ} (h : CloseSpec d L Kc Cx c BG) (hc : c ≤ c') (hB : BG ≤ BG') :
    CloseSpec d L Kc Cx c' BG' := by
  refine ⟨h.1.trans hc, h.2.1.trans hB, ?_⟩
  intro N₁ m₁ K _ ϱ C H a ν S α hα κ hκ hM s hs W hW f Cb hC hf x hx
  have hM' : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁ :=
    le_trans (mul_le_mul_of_nonneg_right hc (Real.exp_pos _).le) hM
  obtain ⟨h1, h2, h3⟩ := h.2.2 C H S hα hκ hM' hs hW f hC hf x hx
  have hmono : BG * Real.exp (N0 d L * κ) * decay (gammaW d) (siteSetDist H W x) * Cb ≤
      BG' * Real.exp (N0 d L * κ) * decay (gammaW d) (siteSetDist H W x) * Cb := by
    have := decay_nonneg (gammaW d) (siteSetDist H W x)
    have := (Real.exp_pos (N0 d L * κ)).le
    gcongr
  exact ⟨h1.trans hmono, fun μ => (h2 μ).trans hmono, h3.trans hmono⟩

theorem closeSpec_exists (hd : 3 ≤ d) (hL : 3 ≤ L) (hKc : 0 ≤ Kc) (hCx : 0 ≤ Cx) : ∃ c BG : ℝ, CloseSpec d L Kc Cx c BG := by
  obtain ⟨c, B, hc, hB, Hh⟩ := dg6 (d := d) (L := L) (Kc := Kc) (Cx := Cx) hd hL hKc hCx
  refine ⟨c, B, hc, hB, ?_⟩
  intro N₁ m₁ K _ ϱ C H a ν S α hα κ hκ hM s hs W hW f Cb hC hf x hx
  exact Hh C H S hα hκ hM hs hW f hC hf x hx


/-- **One set of constants for all the inputs of Theorem I-4a.** -/
theorem specs_exist (hd : 3 ≤ d) (hL : 3 ≤ L) (hKc : 0 ≤ Kc) (hCx : 0 ≤ Cx) : ∃ c BG : ℝ, FamSpec d L Kc Cx c BG ∧ Dg2Spec d L Kc Cx c BG ∧
    CloseSpec d L Kc Cx c BG ∧ OneSpec d L Kc Cx c ∧ AnSpec d L Kc Cx c := by
  obtain ⟨c1, B1, h1⟩ := decGreenFamily (d := d) (L := L) (Kc := Kc) (Cx := Cx) hd hL hKc hCx
  obtain ⟨c2, B2, h2⟩ := dg2Spec_exists (d := d) (L := L) (Kc := Kc) (Cx := Cx) hd hL hKc hCx
  obtain ⟨c3, B3, h3⟩ := closeSpec_exists (d := d) (L := L) (Kc := Kc) (Cx := Cx) hd hL hKc hCx
  obtain ⟨c4, h4⟩ := oneSpec_exists (d := d) (L := L) (Kc := Kc) (Cx := Cx) hd hL hKc hCx
  obtain ⟨c5, h5⟩ := anSpec_exists (d := d) (L := L) (Kc := Kc) (Cx := Cx) hd hL hKc hCx
  set c := max (max (max (max c1 c2) c3) c4) c5 with hc
  set B := max (max B1 B2) B3 with hB
  refine ⟨c, B, (h1.mono_c ?_).mono_BG ?_, h2.mono ?_ ?_, h3.mono ?_ ?_, h4.mono_c ?_, h5.mono_c ?_⟩
  all_goals simp [hc, hB]

/-- **The part of `δφ(s) - δφ(1)` coming from `G_s - G_D`** (via `dg6`): weighted bounds with the
weight `e^{γ_w min(d(x, W), t)}`. -/
theorem wsup_close {c BG6 : ℝ} (hC : CloseSpec d L Kc Cx c BG6) (S : CoverBase C H a ν Kc Cx)
    {α : H.Ω 1 → ℂ} (hα : AdmPot H α) {κ : ℝ} (hκ : 0 ≤ κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    {s : ℕ × CTorus d L N₁ m₁ K → ℂ} (hs : ∀ P, ‖s P‖ ≤ Real.exp κ)
    {W : Finset (CTorus d L N₁ m₁ K)} (hW : ∀ z ∈ C.cubeIdx, C.sProd s z ≠ 1 → intBox z ⊆ W)
    (g : H.Ω 1 × Fin N → ℂ) {Cb : ℝ} (hCn : 0 ≤ Cb) (hg : SrcBound H g Cb) {t : ℝ} :
    WSup H (wgt H W t (gammaW d)) (liftOp N (Gs C H a ν α s) *ᵥ g -
        liftOp N (dirichletOperator H a ν α)⁻¹ *ᵥ g)
      (L * Real.exp (gammaW d) * (BG6 * Real.exp (N0 d L * κ) * Cb)) := by
  have hd0 : 0 < d := by have := S.hd; omega
  have hγ := gammaW_nonneg hd0
  have hB6 : 0 ≤ BG6 * Real.exp (N0 d L * κ) * Cb := by
    have := hC.2.1; positivity
  have hω := isWeight_wgt (G := H) W t hγ
  refine wsup_of_fwd S.one_lt_rho (by have := S.hL; omega) hγ hω hB6 ?_ ?_ ?_
  · intro y i
    rw [svec_liftOp_sub]
    by_cases hy : y ∈ H.Ω 1
    · obtain ⟨h1, -, -⟩ := hC.2.2 C H S hα hκ hM hs hW (comp H g i) hCn (fun x => hg x i) y hy
      have e : zeroExt (H.Ω 1) (Gs C H a ν α s *ᵥ comp H g i) y -
          zeroExt (H.Ω 1) ((dirichletOperator H a ν α)⁻¹ *ᵥ comp H g i) y =
          Gdiff C H a ν α s (comp H g i) y := rfl
      rw [e]
      have hw := wgt_mul_decay (G := H) W t hγ y
      have hbc : 0 ≤ BG6 * Real.exp (N0 d L * κ) * Cb := hB6
      calc wgt H W t (gammaW d) y * ‖Gdiff C H a ν α s (comp H g i) y‖
          ≤ wgt H W t (gammaW d) y * (BG6 * Real.exp (N0 d L * κ) *
            decay (gammaW d) (siteSetDist H W y) * Cb) :=
            mul_le_mul_of_nonneg_left h1 (wgt_pos W t _ y).le
        _ = (wgt H W t (gammaW d) y * decay (gammaW d) (siteSetDist H W y)) *
            (BG6 * Real.exp (N0 d L * κ) * Cb) := by ring
        _ ≤ 1 * (BG6 * Real.exp (N0 d L * κ) * Cb) := mul_le_mul_of_nonneg_right hw hbc
        _ = _ := one_mul _
    · rw [zeroExt_not_mem _ _ hy, zeroExt_not_mem _ _ hy, sub_zero, norm_zero, mul_zero]
      exact hB6
  · intro x hx μ i
    simp only [svec_liftOp_sub]
    obtain ⟨-, h2, -⟩ := hC.2.2 C H S hα hκ hM hs hW (comp H g i) hCn (fun x => hg x i) x hx
    have e : ∀ y : CTorus d L N₁ m₁ K, zeroExt (H.Ω 1) (Gs C H a ν α s *ᵥ comp H g i) y -
          zeroExt (H.Ω 1) ((dirichletOperator H a ν α)⁻¹ *ᵥ comp H g i) y =
          Gdiff C H a ν α s (comp H g i) y := fun y => rfl
    simp only [e]
    have hw := wgt_mul_decay (G := H) W t hγ x
    calc wgt H W t (gammaW d) x * (H.spacing x * ‖Gdiff C H a ν α s (comp H g i) (x + Pi.single μ 1) -
          Gdiff C H a ν α s (comp H g i) x‖)
        ≤ wgt H W t (gammaW d) x * (BG6 * Real.exp (N0 d L * κ) *
            decay (gammaW d) (siteSetDist H W x) * Cb) :=
            mul_le_mul_of_nonneg_left (h2 μ) (wgt_pos W t _ x).le
      _ = (wgt H W t (gammaW d) x * decay (gammaW d) (siteSetDist H W x)) *
          (BG6 * Real.exp (N0 d L * κ) * Cb) := by ring
      _ ≤ 1 * (BG6 * Real.exp (N0 d L * κ) * Cb) := mul_le_mul_of_nonneg_right hw hB6
      _ = _ := one_mul _
  · intro x hx i
    simp only [svec_liftOp_sub]
    obtain ⟨-, -, h3⟩ := hC.2.2 C H S hα hκ hM hs hW (comp H g i) hCn (fun x => hg x i) x hx
    have e : ∀ y : CTorus d L N₁ m₁ K, zeroExt (H.Ω 1) (Gs C H a ν α s *ᵥ comp H g i) y -
          zeroExt (H.Ω 1) ((dirichletOperator H a ν α)⁻¹ *ᵥ comp H g i) y =
          Gdiff C H a ν α s (comp H g i) y := fun y => rfl
    simp only [e]
    have hw := wgt_mul_decay (G := H) W t hγ x
    calc wgt H W t (gammaW d) x * (H.spacing x ^ 2 * ‖∑ μ : Fin d,
          (2 * Gdiff C H a ν α s (comp H g i) x - Gdiff C H a ν α s (comp H g i) (x + Pi.single μ 1) -
            Gdiff C H a ν α s (comp H g i) (x - Pi.single μ 1))‖)
        ≤ wgt H W t (gammaW d) x * (BG6 * Real.exp (N0 d L * κ) *
            decay (gammaW d) (siteSetDist H W x) * Cb) :=
            mul_le_mul_of_nonneg_left h3 (wgt_pos W t _ x).le
      _ = (wgt H W t (gammaW d) x * decay (gammaW d) (siteSetDist H W x)) *
          (BG6 * Real.exp (N0 d L * κ) * Cb) := by ring
      _ ≤ 1 * (BG6 * Real.exp (N0 d L * κ) * Cb) := mul_le_mul_of_nonneg_right hw hB6
      _ = _ := one_mul _


/-- **The weighted bounds of `G_D(A) g`** for a weighted source `g` (from `dg2_sup` at `s = 1`). -/
theorem wsup_green {c BG : ℝ} (hD : Dg2Spec d L Kc Cx c BG) (h1 : OneSpec d L Kc Cx c) (S : CoverBase C H a ν Kc Cx)
    (hM0 : c ≤ (L : ℝ) ^ m₁) {A : H.Ω 1 → ℂ} (hA : AdmPot H A)
    {ω : CTorus d L N₁ m₁ K → ℝ} (hω : IsWeight H (gammaW d) ω)
    (g : H.Ω 1 × Fin N → ℂ) {Cb : ℝ} (hC : 0 ≤ Cb)
    (hg : ∀ (x : H.Ω 1) (i : Fin N), ω x * (H.spacing (x : CTorus d L N₁ m₁ K)) ^ 2 *
      ‖g (x, i)‖ ≤ Cb) :
    WSup H ω (liftOp N (dirichletOperator H a ν A)⁻¹ *ᵥ g) (L * Real.exp (gammaW d) * (BG * Cb)) := by
  have hd0 : 0 < d := by have := S.hd; omega
  have hγ := gammaW_nonneg hd0
  have hone : Gs C H a ν A (fun _ => 1) = (dirichletOperator H a ν A)⁻¹ := (h1.2 C H S hA hM0).2
  have hM00 : c * Real.exp (N0 d L * 0) ≤ (L : ℝ) ^ m₁ := by simpa using hM0
  refine wsup_liftOp S.one_lt_rho (by have := S.hL; omega) hγ hω hD.2.1 (fun f C' hC' hf => ?_)
    g hC hg
  have := (hD.2.2 C H S hA (κ := 0) le_rfl hM00 (s := fun _ => 1) (by simp) hω f hC' hf).2
  rw [hone] at this
  simpa using this


/-- **The resolvent identity for vector fields**:
`(Ĝ(A) - Ĝ(A')) F = Ĝ(A) (-(A - A') Ĝ(A') F)`. -/
theorem green_sub_vec (S : CoverBase C H a ν Kc Cx) {A A' : H.Ω 1 → ℂ} (hA : AdmPot H A)
    (hA' : AdmPot H A') (F : H.Ω 1 × Fin N → ℂ) :
    liftOp N (dirichletOperator H a ν A)⁻¹ *ᵥ F - liftOp N (dirichletOperator H a ν A')⁻¹ *ᵥ F =
      liftOp N (dirichletOperator H a ν A)⁻¹ *ᵥ
        (fun p => -(A p.1 - A' p.1) * (liftOp N (dirichletOperator H a ν A')⁻¹ *ᵥ F) p) := by
  have hd0 : 0 < d := by have := S.hd; omega
  funext ⟨x, i⟩
  rw [Pi.sub_apply, liftOp_mulVec, liftOp_mulVec, liftOp_mulVec]
  have := congrFun (green_sub_eq_mulVec H hd0 S.mass S.weights A A' hA hA' (fun z => F (z, i))) x
  rw [Pi.sub_apply] at this
  rw [this]
  congr 1
  funext y
  rw [liftOp_mulVec]


omit [NeZero N₁] [NeZero L] in
theorem extS_norm_le {κ : ℝ} (hκ : 0 ≤ κ) {s : DecParams C} (hs : ∀ P, ‖s P‖ ≤ Real.exp κ) :
    ∀ P, ‖extS C s P‖ ≤ Real.exp κ := by
  intro P
  unfold extS
  split_ifs with h
  · exact hs ⟨P, h⟩
  · simpa using Real.one_le_exp hκ

/-- **The three pieces of `δφ(s) - δφ(1)`** (Step 4 of I-4a): the source term `G_s - G_D`
(`dg6`), the linear term in the difference of the potentials and the resolvent term
(`G_D(A) - G_D(A') = -G_D(A)(A - A')G_D(A')`). -/
theorem close_pieces {c BG : ℝ} (hD : Dg2Spec d L Kc Cx c BG) (hCl : CloseSpec d L Kc Cx c BG)
    (h1 : OneSpec d L Kc Cx c) (S : CoverBase C H a ν Kc Cx) {κ : ℝ} (hκ : 0 ≤ κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) (hM0 : c ≤ (L : ℝ) ^ m₁)
    {s : DecParams C} (hs : ∀ P, ‖s P‖ ≤ Real.exp κ) {W : Finset (CTorus d L N₁ m₁ K)}
    (hW : ∀ z ∈ C.cubeIdx, C.sProd (extS C s) z ≠ 1 → intBox z ⊆ W) (t : ℝ)
    {α₀ : H.Ω 1 → ℂ} {φ₀ : CTorus d L N₁ m₁ K → Fin N → ℂ} {Fs : H.Ω 1 × Fin N → ℂ}
    {δα δα' : H.Ω 1 → ℂ} {CF X E : ℝ} (hCF0 : 0 ≤ CF) (hX0 : 0 ≤ X) (hE0 : 0 ≤ E)
    (hAdm : AdmPot H (α₀ + δα)) (hAdm' : AdmPot H (α₀ + δα'))
    (hF₀ : SrcBound H (Fsrc φ₀ Fs δα) CF) (hphi : ∀ x ∈ H.Ω 1, vn (φ₀ x) ≤ 3 / 2)
    (he : ∀ x : H.Ω 1, wgt H W t (gammaW d) x *
      (H.spacing (x : CTorus d L N₁ m₁ K) ^ 2 * ‖δα x - δα' x‖) ≤ E)
    (hdp' : SupBounds H (dphi H (decG C H a ν (fun _ => 1)) α₀ φ₀ Fs δα') X) :
    WSup H (wgt H W t (gammaW d))
      (dphi H (decG C H a ν s) α₀ φ₀ Fs δα - dphi H (decG C H a ν (fun _ => 1)) α₀ φ₀ Fs δα')
      (L * Real.exp (gammaW d) * (BG * Real.exp (N0 d L * κ) * CF) +
        L * Real.exp (gammaW d) * (BG * (3 / 2 * E)) +
        L * Real.exp (gammaW d) * (BG * (E * X))) := by
  classical
  have hd0 : 0 < d := by have := S.hd; omega
  have hγ := gammaW_nonneg hd0
  have hBG : 0 ≤ BG := hD.2.1
  set ω : CTorus d L N₁ m₁ K → ℝ := wgt H W t (gammaW d) with hωdef
  have hω : IsWeight H (gammaW d) ω := isWeight_wgt W t hγ
  have hω0 : ∀ y, 0 ≤ ω y := fun y => (wgt_pos W t _ y).le
  set F₀ : H.Ω 1 × Fin N → ℂ := Fsrc φ₀ Fs δα with hF₀def
  set F₁ : H.Ω 1 × Fin N → ℂ := Fsrc φ₀ Fs δα' with hF₁def
  have hs' := extS_norm_le hκ hs
  have Ta := wsup_close (H := H) hCl S hAdm hκ hM hs' hW F₀ hCF0 hF₀ (t := t)
  have hdiffsrc : ∀ (x : H.Ω 1) (i : Fin N), ω x * (H.spacing (x : CTorus d L N₁ m₁ K)) ^ 2 *
      ‖(F₀ - F₁) (x, i)‖ ≤ 3 / 2 * E := by
    intro x i
    have hphi' : ‖φ₀ x i‖ ≤ 3 / 2 := (norm_le_vn _ i).trans (hphi x x.2)
    have e2 : (F₀ - F₁) (x, i) = -((δα x - δα' x) * φ₀ x i) := by
      simp only [hF₀def, hF₁def, Fsrc, Pi.sub_apply]; ring
    rw [e2, norm_neg, norm_mul]
    calc ω x * H.spacing (x : CTorus d L N₁ m₁ K) ^ 2 * (‖δα x - δα' x‖ * ‖φ₀ x i‖)
        = (ω x * (H.spacing (x : CTorus d L N₁ m₁ K) ^ 2 * ‖δα x - δα' x‖)) * ‖φ₀ x i‖ := by ring
      _ ≤ E * (3 / 2) := mul_le_mul (he x) hphi' (norm_nonneg _) hE0
      _ = _ := by ring
  have Tb := wsup_green (H := H) hD h1 S hM0 hAdm hω (F₀ - F₁) (by positivity) hdiffsrc
  have hone' : decG C H a ν (fun _ => 1) (α₀ + δα') = (dirichletOperator H a ν (α₀ + δα'))⁻¹ :=
    decG_one h1 S hM0 hAdm'
  have hsrcc : ∀ (x : H.Ω 1) (i : Fin N), ω x * (H.spacing (x : CTorus d L N₁ m₁ K)) ^ 2 *
      ‖(fun p : H.Ω 1 × Fin N => -((α₀ + δα) p.1 - (α₀ + δα') p.1) *
        (liftOp N (dirichletOperator H a ν (α₀ + δα'))⁻¹ *ᵥ F₁) p) (x, i)‖ ≤ E * X := by
    intro x i
    have hv : ‖(liftOp N (dirichletOperator H a ν (α₀ + δα'))⁻¹ *ᵥ F₁) (x, i)‖ ≤ X := by
      have h2 := hdp'.val x i
      rw [svec_of_mem] at h2
      have : dphi H (decG C H a ν (fun _ => 1)) α₀ φ₀ Fs δα' =
          liftOp N (dirichletOperator H a ν (α₀ + δα'))⁻¹ *ᵥ F₁ := by
        unfold dphi; rw [hone']
      rwa [this] at h2
    simp only [norm_mul, norm_neg]
    have e3 : (α₀ + δα) x - (α₀ + δα') x = δα x - δα' x := by simp
    rw [e3]
    calc ω x * H.spacing (x : CTorus d L N₁ m₁ K) ^ 2 *
          (‖δα x - δα' x‖ * ‖(liftOp N (dirichletOperator H a ν (α₀ + δα'))⁻¹ *ᵥ F₁) (x, i)‖)
        = (ω x * (H.spacing (x : CTorus d L N₁ m₁ K) ^ 2 * ‖δα x - δα' x‖)) *
          ‖(liftOp N (dirichletOperator H a ν (α₀ + δα'))⁻¹ *ᵥ F₁) (x, i)‖ := by ring
      _ ≤ E * X := mul_le_mul (he x) hv (norm_nonneg _) hE0
  have Tc := wsup_green (H := H) hD h1 S hM0 hAdm hω
    (fun p : H.Ω 1 × Fin N => -((α₀ + δα) p.1 - (α₀ + δα') p.1) *
      (liftOp N (dirichletOperator H a ν (α₀ + δα'))⁻¹ *ᵥ F₁) p) (by positivity) hsrcc
  have hsum : dphi H (decG C H a ν s) α₀ φ₀ Fs δα -
      dphi H (decG C H a ν (fun _ => 1)) α₀ φ₀ Fs δα' =
      (liftOp N (Gs C H a ν (α₀ + δα) (extS C s)) *ᵥ F₀ -
        liftOp N (dirichletOperator H a ν (α₀ + δα))⁻¹ *ᵥ F₀) +
      liftOp N (dirichletOperator H a ν (α₀ + δα))⁻¹ *ᵥ (F₀ - F₁) +
      liftOp N (dirichletOperator H a ν (α₀ + δα))⁻¹ *ᵥ
        (fun p : H.Ω 1 × Fin N => -((α₀ + δα) p.1 - (α₀ + δα') p.1) *
          (liftOp N (dirichletOperator H a ν (α₀ + δα'))⁻¹ *ᵥ F₁) p) := by
    have e1' : dphi H (decG C H a ν (fun _ => 1)) α₀ φ₀ Fs δα' =
        liftOp N (dirichletOperator H a ν (α₀ + δα'))⁻¹ *ᵥ F₁ := by
      unfold dphi; rw [hone']
    rw [e1', ← green_sub_vec S hAdm hAdm' F₁]
    exact vec_telescope (M0 := (dirichletOperator H a ν (α₀ + δα))⁻¹) F₀ F₁
  rw [hsum]
  exact (Ta.add hω0 Tb).add hω0 Tc

/-- **The weighted bound for the difference of the potentials** from the weighted bounds of the
difference of the fields (`δα = 𝒩(δφ)` at both parameters). -/
theorem close_nmap {ιU : Bool} {α₀ : H.Ω 1 → ℂ}
    {φ₀ δΨ : CTorus d L N₁ m₁ K → Fin N → ℂ} {f₁ : H.Ω 1 × Fin N → ℂ} {δ₀ δ₁ : ℝ}
    (Hh : DecHyp H a ν ιU α₀ φ₀ δΨ f₁ δ₀ δ₁) {s : DecParams C}
    {δα δα' : H.Ω 1 → ℂ}
    (hfix : DecFixed C H a ν s ιU α₀ φ₀ (pertSource H a δΨ f₁) δα)
    (hfix' : DecFixed C H a ν (fun _ => 1) ιU α₀ φ₀ (pertSource H a δΨ f₁) δα')
    {X V : ℝ} (hX0 : 0 ≤ X) (hV0 : 0 ≤ V)
    (hstar : StarBound H (dphi H (decG C H a ν s) α₀ φ₀ (pertSource H a δΨ f₁) δα) X)
    (hstar' : StarBound H (dphi H (decG C H a ν (fun _ => 1)) α₀ φ₀ (pertSource H a δΨ f₁) δα') X)
    {W : Finset (CTorus d L N₁ m₁ K)} {t : ℝ}
    (hWS : WSup H (wgt H W t (gammaW d))
      (dphi H (decG C H a ν s) α₀ φ₀ (pertSource H a δΨ f₁) δα -
        dphi H (decG C H a ν (fun _ => 1)) α₀ φ₀ (pertSource H a δΨ f₁) δα') V)
    (x : H.Ω 1) :
    wgt H W t (gammaW d) x * (H.spacing (x : CTorus d L N₁ m₁ K) ^ 2 * ‖δα x - δα' x‖) ≤
      (N * (cF d L * δ₁) + commKConst d L N * δ₀ * wFac d + N * (2 * d + 8) * wFac d * X) * V := by
  have hd0 : 0 < d := by have := Hh.green.hd; omega
  have hγ := gammaW_nonneg hd0
  have hω : IsWeight H (gammaW d) (wgt H W t (gammaW d)) := isWeight_wgt W t hγ
  have hFsb : SrcBound H (pertSource H a δΨ f₁) (cF d L * δ₁) :=
    pertSource_bound Hh.green Hh.δ₁_nn Hh.dPsi Hh.f₁_bd
  have hN := Nmap_diff_weighted (G := H) (a := a) (ν := ν) (ιU := ιU) Hh.green (α₀ := α₀)
    (φ₀ := φ₀) (Fs := pertSource H a δΨ f₁) Hh.smooth Hh.δ₀_nn hFsb (x := x)
    ((Hh.alpha0 x).trans Hh.δ₀_le) hγ hω (E := V) hV0 hX0 hX0 hstar hstar' hWS.val
    (fun μ i => hWS.fwd x x.2 μ i) (fun μ i => hWS.bwd x x.2 μ i)
  have hx1 := congrFun hfix x
  have hx2 := congrFun hfix' x
  have : wgt H W t (gammaW d) x * (H.spacing (x : CTorus d L N₁ m₁ K) ^ 2 * ‖δα x - δα' x‖) =
      wgt H W t (gammaW d) x * (H.spacing (x : CTorus d L N₁ m₁ K) ^ 2 *
        ‖Nmap H (dirichletOperator H a ν α₀) ιU φ₀ (pertSource H a δΨ f₁)
            (dphi H (decG C H a ν s) α₀ φ₀ (pertSource H a δΨ f₁) δα) x -
          Nmap H (dirichletOperator H a ν α₀) ιU φ₀ (pertSource H a δΨ f₁)
            (dphi H (decG C H a ν (fun _ => 1)) α₀ φ₀ (pertSource H a δΨ f₁) δα') x‖) := by
    rw [hx1, hx2]
  rw [this]
  refine hN.trans (le_of_eq ?_)
  unfold wFac; ring



/-- **Theorem I-4a (d), the estimate.**  The solutions at `s` and at `s ≡ 1` differ by a weighted
amount of the size of the source `G_s - G_D`, with the weight `e^{γ_w min(d(·, W), t)}`. -/
theorem i4a_close_core {c BG : ℝ} (hF : FamSpec d L Kc Cx c BG) (hD : Dg2Spec d L Kc Cx c BG)
    (hCl : CloseSpec d L Kc Cx c BG) (h1 : OneSpec d L Kc Cx c) (S : CoverBase C H a ν Kc Cx) {κ : ℝ} (hκ : 0 ≤ κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {s : DecParams C}
    (hs : ∀ P, ‖s P‖ ≤ Real.exp κ) {W : Finset (CTorus d L N₁ m₁ K)}
    (hW : ∀ z ∈ C.cubeIdx, C.sProd (extS C s) z ≠ 1 → intBox z ⊆ W)
    {ιU : Bool} {α₀ : H.Ω 1 → ℂ} {φ₀ δΨ : CTorus d L N₁ m₁ K → Fin N → ℂ}
    {f₁ : H.Ω 1 × Fin N → ℂ} {δ₀ δ₁ : ℝ} (Hh : DecHyp H a ν ιU α₀ φ₀ δΨ f₁ δ₀ δ₁)
    (hδ₀ : δ₀ ≤ deltaClose d L N BG κ) (hδ₁ : δ₁ ≤ deltaClose d L N BG κ)
    {δα δα' : H.Ω 1 → ℂ}
    (hfix : DecFixed C H a ν s ιU α₀ φ₀ (pertSource H a δΨ f₁) δα)
    (hsm : Small H δα (c6' d L N (famConst d L BG κ) (gamma1 d / 8)))
    (hfix' : DecFixed C H a ν (fun _ => 1) ιU α₀ φ₀ (pertSource H a δΨ f₁) δα')
    (hsm' : Small H δα' (c6' d L N (famConst d L BG κ) (gamma1 d / 8))) (t : ℝ) :
    (∀ x : H.Ω 1, wgt H W t (gammaW d) x *
        (H.spacing (x : CTorus d L N₁ m₁ K) ^ 2 * ‖δα x - δα' x‖) ≤ closeConst d L N BG κ δ₁) ∧
    WSup H (wgt H W t (gammaW d))
      (dphi H (decG C H a ν s) α₀ φ₀ (pertSource H a δΨ f₁) δα -
        dphi H (decG C H a ν (fun _ => 1)) α₀ φ₀ (pertSource H a δΨ f₁) δα')
      (2 * closeConst d L N BG κ δ₁) := by
  classical
  have hd0 : 0 < d := by have := S.hd; omega
  have hBG : 0 ≤ BG := hF.2.1
  set B : ℝ := famConst d L BG κ with hB
  set Γ : ℝ := gamma1 d / 8 with hΓdef
  have hB0 : 0 ≤ B := by have := famConst_ge_one (L := L) hBG κ hd0; linarith
  have hΓ : 0 < Γ := by have := gamma1_pos hd0; positivity
  have hdc : deltaClose d L N BG κ ≤ deltaStar' d L N B Γ := min_le_left _ _
  have hdc1 : deltaClose d L N BG κ ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hdc2 : deltaClose d L N BG κ ≤
      1 / (2 * closeLam d L N B * closeM0 d L N BG B + 1) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hdc3 : deltaClose d L N BG κ ≤ 1 / (2 * closeLam d L N B + 1) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hδ₀' : δ₀ ≤ deltaStar' d L N B Γ := hδ₀.trans hdc
  have hδ₁' : δ₁ ≤ deltaStar' d L N B Γ := hδ₁.trans hdc
  have hc0 : 0 ≤ c := hF.1
  have hE1 : 1 ≤ Real.exp (N0 d L * κ) := Real.one_le_exp (by unfold N0; positivity)
  have hM0 : c ≤ (L : ℝ) ^ m₁ := by nlinarith
  have hs1 : ∀ P : C.cubeIdx, ‖(fun _ : C.cubeIdx => (1 : ℂ)) P‖ ≤ Real.exp κ := fun P => by
    simpa using Real.one_le_exp hκ
  obtain ⟨δα₀, hfix₀, hs6₀, hsK₀, hdp₀, huniq₀, -⟩ :=
    i4a_exists_unique hF C H S hκ hM hs Hh hδ₀' hδ₁'
  obtain ⟨δα₁, hfix₁, hs6₁, hsK₁, hdp₁, huniq₁, -⟩ :=
    i4a_exists_unique hF C H S hκ hM hs1 Hh hδ₀' hδ₁'
  have e0 : δα = δα₀ := huniq₀ δα hsm hfix
  have e1 : δα' = δα₁ := huniq₁ δα' hsm' hfix'
  set Fs : H.Ω 1 × Fin N → ℂ := pertSource H a δΨ f₁ with hFsdef
  set X : ℝ := cK2' d L N B * δ₁ with hXdef
  have hcK := cK2'_nonneg (d := d) (L := L) (N := N) hB0
  have hX0 : 0 ≤ X := by have := Hh.δ₁_nn; positivity
  have hsK : Small H δα X := by rw [e0]; exact hsK₀
  have hdp : SupBounds H (dphi H (decG C H a ν s) α₀ φ₀ Fs δα) X := by rw [e0]; exact hdp₀
  have hdp' : SupBounds H (dphi H (decG C H a ν (fun _ => 1)) α₀ φ₀ Fs δα') X := by
    rw [e1]; exact hdp₁
  have hC' := coreHyp'_small (d := d) (L := L) (N := N) hB0 hΓ Hh.δ₀_nn Hh.δ₁_nn hδ₀' hδ₁'
  have hpoly : δ₀ + c6' d L N B Γ ≤ Γ := by linarith [hC'.poly, hC'.ρ_nn]
  have hAdm : AdmPot H (α₀ + δα) :=
    admPot_of_small hd0 (fun y => ((Small.add Hh.alpha0 hsm) y).trans hpoly)
  have hAdm' : AdmPot H (α₀ + δα') :=
    admPot_of_small hd0 (fun y => ((Small.add Hh.alpha0 hsm') y).trans hpoly)
  have hγ := gammaW_nonneg hd0
  have hω0 : ∀ y, 0 ≤ wgt H W t (gammaW d) y := fun y => (wgt_pos W t _ y).le
  set e : H.Ω 1 → ℝ := fun x => wgt H W t (gammaW d) x *
    (H.spacing (x : CTorus d L N₁ m₁ K) ^ 2 * ‖δα x - δα' x‖) with hedef
  have he0 : ∀ x, 0 ≤ e x := fun x => by
    have := spacing_pos H (x := (x : CTorus d L N₁ m₁ K)); have := hω0 x; positivity
  set E : ℝ := ⨆ x, e x with hEdef
  have he_le : ∀ x, e x ≤ E := fun x => le_ciSup (Set.finite_range e).bddAbove x
  have hE0 : 0 ≤ E := Real.iSup_nonneg he0
  set CF : ℝ := cF d L * δ₁ + 3 / 2 * X with hCFdef
  have hCF0 : 0 ≤ CF := by
    have := Balaban.Background.cF_pos d L; have := Hh.δ₁_nn; positivity
  have hF₀ : SrcBound H (Fsrc φ₀ Fs δα) CF := Fsrc_bd Hh.setup hsK
  have hWS := close_pieces hD hCl h1 S hκ hM hM0 hs hW t hCF0 hX0 hE0 hAdm hAdm' hF₀ Hh.phiBd
    he_le hdp'
  set Va : ℝ := closeConst d L N BG κ δ₁ with hVa
  have hVa0 : 0 ≤ Va := by
    have := Balaban.Background.cF_pos d L; have := Hh.δ₁_nn
    rw [hVa]; unfold closeConst; positivity
  set M : ℝ := L * Real.exp (gammaW d) * BG * (3 / 2 + X) with hMdef
  have hM_0 : 0 ≤ M := by positivity
  have hV₁ : L * Real.exp (gammaW d) * (BG * Real.exp (N0 d L * κ) * CF) +
      L * Real.exp (gammaW d) * (BG * (3 / 2 * E)) + L * Real.exp (gammaW d) * (BG * (E * X)) =
      Va + M * E := by
    rw [hVa, hMdef]; unfold closeConst; rw [hCFdef, hXdef]; ring
  rw [hV₁] at hWS
  set Λ : ℝ := N * (cF d L * δ₁) + commKConst d L N * δ₀ * wFac d +
    N * (2 * d + 8) * wFac d * X with hΛdef
  have hstar : StarBound H (dphi H (decG C H a ν s) α₀ φ₀ Fs δα) X :=
    Balaban.Background.SupBounds.star hdp
  have hstar' : StarBound H (dphi H (decG C H a ν (fun _ => 1)) α₀ φ₀ Fs δα') X :=
    Balaban.Background.SupBounds.star hdp'
  have hVaME : 0 ≤ Va + M * E := by positivity
  have hall : ∀ x : H.Ω 1, e x ≤ Λ * (Va + M * E) := fun x =>
    close_nmap Hh hfix hfix' hX0 hVaME hstar hstar' hWS x
  have hw0 : 0 ≤ wFac d := by have := wFac_ge_one d hd0; linarith
  have hcF0 := (Balaban.Background.cF_pos d L).le
  have hKc0 : 0 ≤ commKConst d L N := by unfold commKConst; positivity
  have hΛ0 : 0 ≤ Λ := by
    have := Hh.δ₀_nn; have := Hh.δ₁_nn
    rw [hΛdef]; positivity
  have hEΛ : E ≤ Λ * (Va + M * E) := Real.iSup_le hall (mul_nonneg hΛ0 hVaME)
  -- smallness
  have hlam0 := closeLam_nonneg (d := d) (L := L) (N := N) hB0 hd0
  have hm00 := closeM0_nonneg (d := d) (L := L) (N := N) hBG hB0
  have hdc0 : 0 ≤ deltaClose d L N BG κ := by
    have h1' := (deltaStar'_pos (d := d) (L := L) (N := N) hB0 hΓ).le
    have h2' : 0 ≤ 1 / (2 * closeLam d L N B * closeM0 d L N BG B + 1) := by positivity
    have h3' : 0 ≤ 1 / (2 * closeLam d L N B + 1) := by positivity
    exact le_min h1' (le_min zero_le_one (le_min h2' h3'))
  have hΛle : Λ ≤ closeLam d L N B * deltaClose d L N BG κ := by
    have t1 : N * (cF d L * δ₁) ≤ (N * cF d L) * deltaClose d L N BG κ := by
      rw [← mul_assoc]; exact mul_le_mul_of_nonneg_left hδ₁ (by positivity)
    have t2 : commKConst d L N * δ₀ * wFac d ≤ (commKConst d L N * wFac d) *
        deltaClose d L N BG κ := by
      have := mul_le_mul_of_nonneg_left hδ₀ (mul_nonneg hKc0 hw0)
      calc commKConst d L N * δ₀ * wFac d = commKConst d L N * wFac d * δ₀ := by ring
        _ ≤ _ := this
    have t3 : N * (2 * d + 8) * wFac d * X ≤ (N * (2 * d + 8) * wFac d * cK2' d L N B) *
        deltaClose d L N BG κ := by
      have := mul_le_mul_of_nonneg_left hδ₁ (by positivity :
        (0 : ℝ) ≤ N * (2 * d + 8) * wFac d * cK2' d L N B)
      calc N * (2 * d + 8) * wFac d * X = N * (2 * d + 8) * wFac d * cK2' d L N B * δ₁ := by
            rw [hXdef]; ring
        _ ≤ _ := this
    calc Λ ≤ (N * cF d L) * deltaClose d L N BG κ + (commKConst d L N * wFac d) *
          deltaClose d L N BG κ + (N * (2 * d + 8) * wFac d * cK2' d L N B) *
          deltaClose d L N BG κ := by rw [hΛdef]; exact add_le_add (add_le_add t1 t2) t3
      _ = _ := by unfold closeLam; ring
  have hMle : M ≤ closeM0 d L N BG B := by
    have hX1 : X ≤ cK2' d L N B := by
      rw [hXdef]
      calc cK2' d L N B * δ₁ ≤ cK2' d L N B * 1 :=
            mul_le_mul_of_nonneg_left (hδ₁.trans hdc1) hcK
        _ = _ := mul_one _
    unfold closeM0
    rw [hMdef]
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  obtain ⟨hs2M, hs2⟩ := close_smallness hlam0 hm00 hM_0 hΛle hMle hdc0 hdc2 hdc3
  obtain ⟨hEVa, hVE⟩ := close_arith hM_0 hVa0 hs2M hs2 hEΛ hE0
  exact ⟨fun x => (he_le x).trans hEVa, hWS.mono hVE⟩


/-- **Theorem I-4a (d): closeness to `s = 1` away from the parameters.**  Let `W` be a set of sites
containing the interaction cube of every centre with `s_z ≠ 1`.  Then the solutions of the decoupled
systems at `s` and at `s ≡ 1` (same data, `δ₀, δ₁ ≤ deltaClose`) satisfy, at every site `x`,
`|δα(s) - δα(1)|₂(x)` and the value, forward gradient and Laplacian of `δφ(s) - δφ(1)` are at most
`closeConst · e^{-γ_w d(x, W)}` (resp. twice that), with `closeConst = O(δ₁)`. -/
theorem i4a_close {c BG : ℝ} (hF : FamSpec d L Kc Cx c BG) (hD : Dg2Spec d L Kc Cx c BG)
    (hCl : CloseSpec d L Kc Cx c BG) (h1 : OneSpec d L Kc Cx c) (S : CoverBase C H a ν Kc Cx) {κ : ℝ} (hκ : 0 ≤ κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {s : DecParams C}
    (hs : ∀ P, ‖s P‖ ≤ Real.exp κ) {W : Finset (CTorus d L N₁ m₁ K)}
    (hW : ∀ z ∈ C.cubeIdx, C.sProd (extS C s) z ≠ 1 → intBox z ⊆ W)
    {ιU : Bool} {α₀ : H.Ω 1 → ℂ} {φ₀ δΨ : CTorus d L N₁ m₁ K → Fin N → ℂ}
    {f₁ : H.Ω 1 × Fin N → ℂ} {δ₀ δ₁ : ℝ} (Hh : DecHyp H a ν ιU α₀ φ₀ δΨ f₁ δ₀ δ₁)
    (hδ₀ : δ₀ ≤ deltaClose d L N BG κ) (hδ₁ : δ₁ ≤ deltaClose d L N BG κ)
    {δα δα' : H.Ω 1 → ℂ}
    (hfix : DecFixed C H a ν s ιU α₀ φ₀ (pertSource H a δΨ f₁) δα)
    (hsm : Small H δα (c6' d L N (famConst d L BG κ) (gamma1 d / 8)))
    (hfix' : DecFixed C H a ν (fun _ => 1) ιU α₀ φ₀ (pertSource H a δΨ f₁) δα')
    (hsm' : Small H δα' (c6' d L N (famConst d L BG κ) (gamma1 d / 8))) :
    (∀ x : H.Ω 1, H.spacing (x : CTorus d L N₁ m₁ K) ^ 2 * ‖δα x - δα' x‖ ≤
        closeConst d L N BG κ δ₁ * decay (gammaW d) (siteSetDist H W x)) ∧
    (∀ (y : CTorus d L N₁ m₁ K) (i : Fin N),
      ‖svec H (dphi H (decG C H a ν s) α₀ φ₀ (pertSource H a δΨ f₁) δα -
        dphi H (decG C H a ν (fun _ => 1)) α₀ φ₀ (pertSource H a δΨ f₁) δα') y i‖ ≤
        2 * closeConst d L N BG κ δ₁ * decay (gammaW d) (siteSetDist H W y)) ∧
    (∀ x ∈ H.Ω 1, ∀ (μ : Fin d) (i : Fin N), H.spacing x *
      ‖svec H (dphi H (decG C H a ν s) α₀ φ₀ (pertSource H a δΨ f₁) δα -
        dphi H (decG C H a ν (fun _ => 1)) α₀ φ₀ (pertSource H a δΨ f₁) δα') (x + Pi.single μ 1) i -
        svec H (dphi H (decG C H a ν s) α₀ φ₀ (pertSource H a δΨ f₁) δα -
        dphi H (decG C H a ν (fun _ => 1)) α₀ φ₀ (pertSource H a δΨ f₁) δα') x i‖ ≤
        2 * closeConst d L N BG κ δ₁ * decay (gammaW d) (siteSetDist H W x)) ∧
    (∀ x ∈ H.Ω 1, ∀ i : Fin N, H.spacing x ^ 2 * ‖∑ μ : Fin d,
      (2 * svec H (dphi H (decG C H a ν s) α₀ φ₀ (pertSource H a δΨ f₁) δα -
        dphi H (decG C H a ν (fun _ => 1)) α₀ φ₀ (pertSource H a δΨ f₁) δα') x i -
      svec H (dphi H (decG C H a ν s) α₀ φ₀ (pertSource H a δΨ f₁) δα -
        dphi H (decG C H a ν (fun _ => 1)) α₀ φ₀ (pertSource H a δΨ f₁) δα') (x + Pi.single μ 1) i -
      svec H (dphi H (decG C H a ν s) α₀ φ₀ (pertSource H a δΨ f₁) δα -
        dphi H (decG C H a ν (fun _ => 1)) α₀ φ₀ (pertSource H a δΨ f₁) δα') (x - Pi.single μ 1) i)‖ ≤
        2 * closeConst d L N BG κ δ₁ * decay (gammaW d) (siteSetDist H W x)) := by
  have hd0 : 0 < d := by have := S.hd; omega
  have hγ := gammaW_pos' hd0
  have core := fun t => i4a_close_core hF hD hCl h1 S hκ hM hs hW Hh hδ₀ hδ₁ hfix hsm hfix' hsm' t
  refine ⟨fun x => ?_, fun y i => ?_, fun x hx μ i => ?_, fun x hx i => ?_⟩
  · refine decay_of_weighted hγ _ (fun t _ => ?_)
    exact (core t).1 x
  · refine decay_of_weighted hγ _ (fun t _ => ?_)
    exact (core t).2.val y i
  · refine decay_of_weighted hγ _ (fun t _ => ?_)
    exact (core t).2.fwd x hx μ i
  · refine decay_of_weighted hγ _ (fun t _ => ?_)
    exact (core t).2.lap x hx i


end Balaban.Localization.Dec2
