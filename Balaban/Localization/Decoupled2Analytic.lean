/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.Decoupled2Gs
public import Balaban.Localization.DecoupledAnalytic

/-!
# (DG4) for a cover `C` and an operator `H`: analyticity and the Lipschitz bound

`DecParams C` is the space of parameters `s_P`, `P ∈ C.cubeIdx`.
-/

@[expose] public section

namespace Balaban.Localization.Dec2

open Balaban Balaban.Multiscale Balaban.Background Balaban.Reflection Finset Matrix

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {C : DecCover d L N₁ m₁ K} {H : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ}
  {Kc Cx : ℝ}

/-- The decoupling parameters live on the (finite) set of centres. -/
abbrev DecParams (C : DecCover d L N₁ m₁ K) : Type := C.cubeIdx → ℂ

/-- Extension of a vector of parameters of the centres by `1` (the factors of `s_z` only involve
centres, `Qset_subset`). -/
noncomputable def extS (C : DecCover d L N₁ m₁ K) (s : DecParams C) :
    ℕ × CTorus d L N₁ m₁ K → ℂ :=
  fun P => if h : P ∈ C.cubeIdx then s ⟨P, h⟩ else 1

theorem Qset_subset_cubeIdx (q : ℕ × CTorus d L N₁ m₁ K) : C.Qset q ⊆ C.cubeIdx := by
  intro P hP
  exact ((C.mem_Qset).1 hP).1

theorem analyticAt_sProd (q : ℕ × CTorus d L N₁ m₁ K) (e : DecParams C × (H.Ω 1 → ℂ)) :
    AnalyticAt ℂ (fun p : DecParams C × (H.Ω 1 → ℂ) => C.sProd (extS C p.1) q) e := by
  unfold DecCover.sProd
  refine Finset.analyticAt_fun_prod _ fun P hP => ?_
  have hP' : P ∈ C.cubeIdx := Qset_subset_cubeIdx q hP
  have : (fun p : DecParams C × (H.Ω 1 → ℂ) => extS C p.1 P) = fun p => p.1 ⟨P, hP'⟩ := by
    funext p; simp [extS, hP']
  rw [this]
  exact ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : C.cubeIdx => ℂ) ⟨P, hP'⟩).analyticAt _).comp
    analyticAt_fst


theorem matAt_cubeH (q : ℕ × CTorus d L N₁ m₁ K) (e : DecParams C × (H.Ω 1 → ℂ)) :
    MatAt (fun p : DecParams C × (H.Ω 1 → ℂ) => cubeH H a ν p.2 q) e := by
  have : (fun p : DecParams C × (H.Ω 1 → ℂ) => cubeH H a ν p.2 q) =
      fun p => cubeH H a ν 0 q + Matrix.diagonal p.2 := by
    funext p; exact cutOperator_eq_add a ν _ p.2
  rw [this]
  refine MatAt.add (MatAt.const _ e) ?_
  intro i j
  by_cases hij : i = j
  · subst hij
    simp only [Matrix.diagonal_apply_eq]
    exact ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : H.Ω 1 => ℂ) i).analyticAt _).comp
      analyticAt_snd
  · simp only [Matrix.diagonal_apply_ne _ hij]
    exact analyticAt_const

theorem matAt_cubeG (S : CoverBase C H a ν Kc Cx) {q : ℕ × CTorus d L N₁ m₁ K} (hq : q ∈ C.cubeIdx)
    {e : DecParams C × (H.Ω 1 → ℂ)} (hα : AdmPot H e.2) :
    MatAt (fun p : DecParams C × (H.Ω 1 → ℂ) => cubeG H a ν p.2 q) e := by
  unfold cubeG
  refine MatAt.mul (MatAt.inv (matAt_cubeH q e) ?_) (MatAt.const _ e)
  exact ((Matrix.isUnit_iff_isUnit_det _).1 (cubeH_isUnit S hα hq)).ne_zero

theorem matAt_Kcal (S : CoverBase C H a ν Kc Cx) {e : DecParams C × (H.Ω 1 → ℂ)} (hα : AdmPot H e.2) :
    MatAt (fun p : DecParams C × (H.Ω 1 → ℂ) => Kcal C H a ν p.2 (extS C p.1)) e := by
  unfold Kcal
  refine MatAt.sum _ fun q hq => ?_
  exact MatAt.smul (analyticAt_sProd q e) (MatAt.mul (MatAt.const _ e) (matAt_cubeG S hq hα))

theorem matAt_Gstar (S : CoverBase C H a ν Kc Cx) {e : DecParams C × (H.Ω 1 → ℂ)} (hα : AdmPot H e.2) :
    MatAt (fun p : DecParams C × (H.Ω 1 → ℂ) => Gstar C H a ν p.2 (extS C p.1)) e := by
  unfold Gstar
  refine MatAt.sum _ fun q hq => ?_
  exact MatAt.smul (analyticAt_sProd q e) (MatAt.mul (MatAt.const _ e) (matAt_cubeG S hq hα))

theorem matAt_Gs (S : CoverBase C H a ν Kc Cx) {e : DecParams C × (H.Ω 1 → ℂ)} (hα : AdmPot H e.2)
    (hU : IsUnit (1 - Kcal C H a ν e.2 (extS C e.1))) :
    MatAt (fun p : DecParams C × (H.Ω 1 → ℂ) => Gs C H a ν p.2 (extS C p.1)) e := by
  unfold Gs
  refine MatAt.mul (matAt_Gstar S hα) (MatAt.inv (MatAt.sub (MatAt.const _ e) (matAt_Kcal S hα)) ?_)
  exact ((Matrix.isUnit_iff_isUnit_det _).1 hU).ne_zero

/-- **(DG4), analyticity**: every entry of `G_s(A)` is analytic in `(s, A)` on the polydisc
`|s_P| < e^{κ₁}`, `|A|₂ < γ₁`. -/
theorem dg4_analytic (hd : 3 ≤ d) (hL : 3 ≤ L) (hKc : 0 ≤ Kc) (hCx : 0 ≤ Cx) :
    ∃ cstar : ℝ, 0 ≤ cstar ∧ ∀ {N₁ m₁ K : ℕ} [NeZero N₁] {ϱ : ℝ}
      (C : DecCover d L N₁ m₁ K) (H : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) {a : ℕ → ℝ} {ν : ℝ}, CoverBase C H a ν Kc Cx →
      ∀ {κ : ℝ}, 0 ≤ κ → cstar * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁ →
      ∀ x y : H.Ω 1, AnalyticOnNhd ℂ
        (fun p : DecParams C × (H.Ω 1 → ℂ) => Gs C H a ν p.2 (extS C p.1) x y)
        {p | (∀ P, ‖p.1 P‖ < Real.exp κ) ∧
          ∀ z, ‖p.2 z‖ < coerciveConst d / (2 * (H.spacing (z : CTorus d L N₁ m₁ K)) ^ 2)} := by
  obtain ⟨cstar, BG, hc, hB, Hh⟩ := dg2_sup (d := d) (L := L) (Kc := Kc) (Cx := Cx) hd hL hKc hCx
  refine ⟨cstar, hc, ?_⟩
  intro N₁ m₁ K _ ϱ C H a ν S κ hκ hMκ x y e he
  have hα : AdmPot H e.2 := fun z => (he.2 z).le
  have hs : ∀ P, ‖extS C e.1 P‖ ≤ Real.exp κ := by
    intro P
    unfold extS
    split_ifs with h
    · exact (he.1 ⟨P, h⟩).le
    · simpa using Real.one_le_exp hκ
  have hd0 : 0 < d := by omega
  obtain ⟨hU, -⟩ := Hh C H S hα hκ hMκ hs (w := fun _ => 1) (IsWeight.one H (gammaW_nonneg hd0))
    (0 : H.Ω 1 → ℂ) (Cb := 0) le_rfl (by simp)
  exact matAt_Gs S hα hU x y

/-- **(DG4), the Lipschitz bound in `A`**: for `|A|₂, |A'|₂ ≤ γ₁/8` the increments of the four
pointwise quantities of `G_s(A) f - G_s(A') f` are bounded by `4 B_G e^{N₀κ₁} γ₁⁻¹ |A - A'|₂ |f|₂`. -/
theorem dg4_lipschitz (hd : 3 ≤ d) (hL : 3 ≤ L) (hKc : 0 ≤ Kc) (hCx : 0 ≤ Cx) :
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
  refine ⟨?_, fun μ => ?_, ?_⟩
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

end Balaban.Localization.Dec2
