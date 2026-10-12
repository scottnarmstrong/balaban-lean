/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.DecoupledClose
public import Balaban.Localization.DecoupledAnalytic
public import Balaban.Background.ContractionCoreAnalytic
public import Balaban.Background.ContractionAnalytic

/-!
# Theorem I-4a (LOCALIZATION.md §3.2): the decoupled Green family

The abstract fixed-point core (`Balaban/Background/ContractionCore.lean`) is applied to the
family `α ↦ G_s(α)` of the decoupled Green's operators.  This file contains the Green family
instance: the Lipschitz bound of `dg4_lipschitz` in the form that includes the gradient bond
pointing into a site (`fwd'`), the passage from scalar sources to vector fields (with the wall
bonds costing a factor `L`), and the resulting `GreenFamily`.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Finset Matrix

section Lip

variable {d L : ℕ} [NeZero L]

/-- **(DG4), the Lipschitz bound in `A`**, including the gradient bond pointing into a site
(`fwd'`): for `|A|₂, |A'|₂ ≤ γ₁/8` the increments of the pointwise quantities of
`G_s(A) f - G_s(A') f` are bounded by `4 B_G e^{N₀κ₁} γ₁⁻¹ |A - A'|₂ |f|₂`. -/
theorem dg4_lipschitz_fwd' (hd : 3 ≤ d) (hL : 3 ≤ L) :
    ∃ cstar BG : ℝ, 0 ≤ cstar ∧ 0 ≤ BG ∧ ∀ {N₁ m₁ K : ℕ} [NeZero N₁] {ϱ : ℝ}
      (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) {a : ℕ → ℝ} {ν : ℝ}, DGSetting G a ν →
      ∀ {κ : ℝ}, 0 ≤ κ → cstar * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁ →
      ∀ {s : DecParams G}, (∀ P, ‖s P‖ ≤ Real.exp κ) →
      ∀ (f : G.Ω 1 → ℂ) {C : ℝ}, 0 ≤ C →
      (∀ x : G.Ω 1, (G.spacing (x : CTorus d L N₁ m₁ K)) ^ 2 * ‖f x‖ ≤ C) →
      ∀ {A A' : G.Ω 1 → ℂ},
      (∀ z : G.Ω 1, (G.spacing (z : CTorus d L N₁ m₁ K)) ^ 2 * ‖A z‖ ≤ gamma1 d / 8) →
      (∀ z : G.Ω 1, (G.spacing (z : CTorus d L N₁ m₁ K)) ^ 2 * ‖A' z‖ ≤ gamma1 d / 8) →
      ∀ {ε : ℝ}, 0 ≤ ε →
      (∀ z : G.Ω 1, (G.spacing (z : CTorus d L N₁ m₁ K)) ^ 2 * ‖A z - A' z‖ ≤ ε) →
      ∀ x ∈ G.Ω 1,
      ‖(zeroExt (G.Ω 1) (Gs G a ν A (extS G s) *ᵥ f) x -
        zeroExt (G.Ω 1) (Gs G a ν A' (extS G s) *ᵥ f) x)‖ ≤
        4 * (BG * Real.exp (N0 d L * κ) * C) * ε / gamma1 d ∧
      (∀ μ : Fin d, G.spacing x *
        ‖((zeroExt (G.Ω 1) (Gs G a ν A (extS G s) *ᵥ f) (x + Pi.single μ 1) -
          zeroExt (G.Ω 1) (Gs G a ν A (extS G s) *ᵥ f) x) -
          (zeroExt (G.Ω 1) (Gs G a ν A' (extS G s) *ᵥ f) (x + Pi.single μ 1) -
          zeroExt (G.Ω 1) (Gs G a ν A' (extS G s) *ᵥ f) x))‖ ≤
        4 * (BG * Real.exp (N0 d L * κ) * C) * ε / gamma1 d) ∧
      (∀ μ : Fin d, x + Pi.single μ 1 ∈ G.Ω 1 → G.spacing (x + Pi.single μ 1) *
        ‖((zeroExt (G.Ω 1) (Gs G a ν A (extS G s) *ᵥ f) (x + Pi.single μ 1) -
          zeroExt (G.Ω 1) (Gs G a ν A (extS G s) *ᵥ f) x) -
          (zeroExt (G.Ω 1) (Gs G a ν A' (extS G s) *ᵥ f) (x + Pi.single μ 1) -
          zeroExt (G.Ω 1) (Gs G a ν A' (extS G s) *ᵥ f) x))‖ ≤
        4 * (BG * Real.exp (N0 d L * κ) * C) * ε / gamma1 d) ∧
      (G.spacing x) ^ 2 * ‖∑ μ : Fin d, ((2 * zeroExt (G.Ω 1) (Gs G a ν A (extS G s) *ᵥ f) x -
        zeroExt (G.Ω 1) (Gs G a ν A (extS G s) *ᵥ f) (x + Pi.single μ 1) -
        zeroExt (G.Ω 1) (Gs G a ν A (extS G s) *ᵥ f) (x - Pi.single μ 1)) -
        (2 * zeroExt (G.Ω 1) (Gs G a ν A' (extS G s) *ᵥ f) x -
        zeroExt (G.Ω 1) (Gs G a ν A' (extS G s) *ᵥ f) (x + Pi.single μ 1) -
        zeroExt (G.Ω 1) (Gs G a ν A' (extS G s) *ᵥ f) (x - Pi.single μ 1)))‖ ≤
        4 * (BG * Real.exp (N0 d L * κ) * C) * ε / gamma1 d := by
  obtain ⟨cstar, BG, hc, hB, H⟩ := dg2_sup (d := d) (L := L) hd hL
  refine ⟨cstar, BG, hc, hB, ?_⟩
  intro N₁ m₁ K _ ϱ G a ν S κ hκ hMκ s hs f C hC hfC A A' hA hA' ε hε hAA x hx
  have hd0 : 0 < d := by omega
  have hγ1 : 0 < gamma1 d := gamma1_pos hd0
  set V : ℝ := BG * Real.exp (N0 d L * κ) * C with hV
  set ε' : ℝ := min ε (gamma1 d / 4) with hε'
  have hε'0 : 0 ≤ ε' := le_min hε (by positivity)
  have hε'4 : ε' ≤ gamma1 d / 4 := min_le_right _ _
  have hAA' : ∀ z : G.Ω 1, (G.spacing (z : CTorus d L N₁ m₁ K)) ^ 2 * ‖A z - A' z‖ ≤ ε' := by
    intro z
    refine le_min (hAA z) ?_
    calc (G.spacing (z : CTorus d L N₁ m₁ K)) ^ 2 * ‖A z - A' z‖
        ≤ (G.spacing (z : CTorus d L N₁ m₁ K)) ^ 2 * (‖A z‖ + ‖A' z‖) :=
          mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by positivity)
      _ = (G.spacing (z : CTorus d L N₁ m₁ K)) ^ 2 * ‖A z‖ +
          (G.spacing (z : CTorus d L N₁ m₁ K)) ^ 2 * ‖A' z‖ := by ring
      _ ≤ gamma1 d / 4 := by linarith [hA z, hA' z]
  have hε'ε : ε' ≤ ε := min_le_left _ _
  have hV0 : 0 ≤ V := by positivity
  -- the admissibility conversions
  have hrpos : ∀ z : G.Ω 1, 0 < (G.spacing (z : CTorus d L N₁ m₁ K)) ^ 2 := fun z => by
    have := spacing_pos G (x := (z : CTorus d L N₁ m₁ K)); positivity
  have hadm_le : ∀ B : G.Ω 1 → ℂ,
      (∀ z : G.Ω 1, (G.spacing (z : CTorus d L N₁ m₁ K)) ^ 2 * ‖B z‖ ≤ gamma1 d) → AdmPot G B := by
    intro B hB z
    have h := hB z
    have hz := hrpos z
    unfold gamma1 at h
    rw [le_div_iff₀ (by positivity)]
    linarith
  have hw1 : IsWeight G (gammaW d) (fun _ => (1 : ℝ)) := IsWeight.one G (gammaW_nonneg hd0)
  have hcase : ∀ B : G.Ω 1 → ℂ,
      (∀ z : G.Ω 1, (G.spacing (z : CTorus d L N₁ m₁ K)) ^ 2 * ‖B z‖ ≤ gamma1 d) →
      IsUnit (1 - Kcal G a ν B (extS G s)) ∧
      SupBdW G (fun _ => (1 : ℝ)) (zeroExt (G.Ω 1) (Gs G a ν B (extS G s) *ᵥ f)) V := by
    intro B hB
    have hs' : ∀ P, ‖extS G s P‖ ≤ Real.exp κ := by
      intro P
      unfold extS
      split_ifs with h
      · exact hs ⟨P, h⟩
      · simpa using Real.one_le_exp hκ
    exact H G S (hadm_le B hB) hκ hMκ hs' hw1 f hC (fun z => by simpa using hfC z)
  have hanal : ∀ (B : G.Ω 1 → ℂ), (∀ z : G.Ω 1,
      (G.spacing (z : CTorus d L N₁ m₁ K)) ^ 2 * ‖B z‖ < gamma1 d) → ∀ y : CTorus d L N₁ m₁ K,
      AnalyticAt ℂ (fun B' : G.Ω 1 → ℂ => zeroExt (G.Ω 1) (Gs G a ν B' (extS G s) *ᵥ f) y) B := by
    intro B hB y
    have hB' : ∀ z : G.Ω 1, (G.spacing (z : CTorus d L N₁ m₁ K)) ^ 2 * ‖B z‖ ≤ gamma1 d :=
      fun z => (hB z).le
    obtain ⟨hU, -⟩ := hcase B hB'
    have hMat := matAt_Gs S (e := (s, B)) (hadm_le B hB') hU
    have h := analyticAt_zeroExt_mulVec hMat f y
    exact h.comp (f := fun B' : G.Ω 1 → ℂ => (s, B')) (x := B)
      (AnalyticAt.prod (analyticAt_const (v := s)) analyticAt_id)
  have run : ∀ Fo : (G.Ω 1 → ℂ) → ℂ,
      (∀ B : G.Ω 1 → ℂ, (∀ z : G.Ω 1,
        (G.spacing (z : CTorus d L N₁ m₁ K)) ^ 2 * ‖B z‖ < gamma1 d) → AnalyticAt ℂ Fo B) →
      (∀ B : G.Ω 1 → ℂ, (∀ z : G.Ω 1,
        (G.spacing (z : CTorus d L N₁ m₁ K)) ^ 2 * ‖B z‖ ≤ gamma1 d) → ‖Fo B‖ ≤ V) →
      ‖Fo A - Fo A'‖ ≤ 4 * V * ε / gamma1 d := by
    intro Fo hFa hFb
    have := lipschitz_obs (fun z : G.Ω 1 => (G.spacing (z : CTorus d L N₁ m₁ K)) ^ 2) hrpos hγ1 Fo
      hFa hFb hA' hε'0 hε'4 hAA'
    refine this.trans ?_
    have : 4 * V * ε' / gamma1 d ≤ 4 * V * ε / gamma1 d := by
      apply div_le_div_of_nonneg_right _ hγ1.le
      nlinarith
    exact this
  have hsp := (spacing_pos G (x := x)).le
  have hnrm : ∀ (r : ℝ), 0 ≤ r → ∀ z : ℂ, ‖(r : ℂ) * z‖ = r * ‖z‖ := fun r hr z => by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]
  refine ⟨?_, fun μ => ?_, fun μ hxe => ?_, ?_⟩
  · have := run (fun B => zeroExt (G.Ω 1) (Gs G a ν B (extS G s) *ᵥ f) x)
      (fun B hB => hanal B hB x)
      (fun B hB => by
        have := ((hcase B hB).2.val x hx)
        simpa using this)
    simpa using this
  · have := run (fun B => ((G.spacing x : ℝ) : ℂ) *
        (zeroExt (G.Ω 1) (Gs G a ν B (extS G s) *ᵥ f) (x + Pi.single μ 1) -
          zeroExt (G.Ω 1) (Gs G a ν B (extS G s) *ᵥ f) x))
      (fun B hB => analyticAt_const.mul ((hanal B hB (x + Pi.single μ 1)).sub (hanal B hB x)))
      (fun B hB => by
        have h := ((hcase B hB).2.fwd x hx μ)
        rw [hnrm _ hsp]
        simpa using h)
    rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hsp] at this
    exact this
  · have hsp' := (spacing_pos G (x := x + Pi.single μ 1)).le
    have hnrm' : ∀ z : ℂ, ‖((G.spacing (x + Pi.single μ 1) : ℝ) : ℂ) * z‖ =
        G.spacing (x + Pi.single μ 1) * ‖z‖ := fun z => by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hsp']
    have := run (fun B => ((G.spacing (x + Pi.single μ 1) : ℝ) : ℂ) *
        (zeroExt (G.Ω 1) (Gs G a ν B (extS G s) *ᵥ f) (x + Pi.single μ 1) -
          zeroExt (G.Ω 1) (Gs G a ν B (extS G s) *ᵥ f) x))
      (fun B hB => analyticAt_const.mul ((hanal B hB (x + Pi.single μ 1)).sub (hanal B hB x)))
      (fun B hB => by
        have h := ((hcase B hB).2.fwd' x hx μ hxe)
        rw [hnrm']
        simpa using h)
    rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hsp'] at this
    exact this
  · have := run (fun B => (((G.spacing x) ^ 2 : ℝ) : ℂ) *
        ∑ μ : Fin d, (2 * zeroExt (G.Ω 1) (Gs G a ν B (extS G s) *ᵥ f) x -
          zeroExt (G.Ω 1) (Gs G a ν B (extS G s) *ᵥ f) (x + Pi.single μ 1) -
          zeroExt (G.Ω 1) (Gs G a ν B (extS G s) *ᵥ f) (x - Pi.single μ 1)))
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


end Lip

section Vec

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ}

theorem SupBdW.mono {w : CTorus d L N₁ m₁ K → ℝ} {v : CTorus d L N₁ m₁ K → ℂ} {V V' : ℝ}
    (h : SupBdW G w v V) (hV : V ≤ V') : SupBdW G w v V' :=
  ⟨fun x hx => (h.val x hx).trans hV, fun x hx μ => (h.fwd x hx μ).trans hV,
    fun x hx μ hxe => (h.fwd' x hx μ hxe).trans hV, fun x hx => (h.lap x hx).trans hV⟩

/-- **Wall sites have spacing `L`**: a site of `Ω₁` with a neighbour outside `Ω₁` is in layer `1`. -/
theorem spacing_wall_eq {x y : CTorus d L N₁ m₁ K} (hϱ : 1 < ϱ) (hL : 2 ≤ L) (hx : x ∈ G.Ω 1)
    (hy : y ∉ G.Ω 1) (h : Adj x y) : G.spacing x = L := by
  obtain ⟨hj1, hjk, hxl⟩ := G.layerIndex_spec hx
  have h1 := layerIndex_eq_one_of_adj_not_mem hϱ hL hx hy h
  rw [G.spacing_eq hj1 hjk hxl, h1, pow_one]

theorem svec_liftOp_sub (A B : Matrix (G.Ω 1) (G.Ω 1) ℂ) (g : G.Ω 1 × Fin N → ℂ)
    (y : CTorus d L N₁ m₁ K) (i : Fin N) :
    svec G (liftOp N A *ᵥ g - liftOp N B *ᵥ g) y i =
      zeroExt (G.Ω 1) (A *ᵥ comp G g i) y - zeroExt (G.Ω 1) (B *ᵥ comp G g i) y := by
  rw [← svec_liftOp, ← svec_liftOp]
  unfold svec zeroExt
  split_ifs <;> simp

/-- **From scalar sources to vector fields** (wall bonds cost a factor `L`): if `zeroExt (M f)`
satisfies the four pointwise bounds with constant `b C` for every scalar source with `|f|₂ ≤ C`,
then `liftOp M g` satisfies `SupBounds` with constant `L b C`. -/
theorem supBounds_liftOp (hϱ : 1 < ϱ) (hL : 2 ≤ L) {M : Matrix (G.Ω 1) (G.Ω 1) ℂ} {b : ℝ}
    (hb : 0 ≤ b)
    (h : ∀ (f : G.Ω 1 → ℂ) {C : ℝ}, 0 ≤ C →
      (∀ x : G.Ω 1, (G.spacing (x : CTorus d L N₁ m₁ K)) ^ 2 * ‖f x‖ ≤ C) →
      SupBdW G (fun _ => (1 : ℝ)) (zeroExt (G.Ω 1) (M *ᵥ f)) (b * C))
    (g : G.Ω 1 × Fin N → ℂ) {C : ℝ} (hC : 0 ≤ C) (hg : SrcBound G g C) :
    SupBounds G (liftOp N M *ᵥ g) (L * (b * C)) := by
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have hbC : 0 ≤ b * C := mul_nonneg hb hC
  have hmono : b * C ≤ L * (b * C) := by nlinarith
  have hsd : ∀ i : Fin N, SupBdW G (fun _ => (1 : ℝ)) (zeroExt (G.Ω 1) (M *ᵥ comp G g i)) (b * C) :=
    fun i => h (comp G g i) hC (fun x => hg x i)
  refine ⟨fun y i => ?_, fun x hx μ i => ?_, fun x hx μ i => ?_, fun x hx i => ?_⟩
  · rw [svec_liftOp]
    by_cases hy : y ∈ G.Ω 1
    · have := (hsd i).val y hy
      simp only [one_mul] at this
      exact this.trans hmono
    · rw [zeroExt_not_mem _ _ hy, norm_zero]; exact hbC.trans hmono
  · rw [svec_liftOp, svec_liftOp]
    have := (hsd i).fwd x hx μ
    simp only [one_mul] at this
    exact this.trans hmono
  · rw [svec_liftOp, svec_liftOp]
    by_cases hy : x - Pi.single μ 1 ∈ G.Ω 1
    · have hxy : x - Pi.single μ 1 + Pi.single μ 1 ∈ G.Ω 1 := by simpa using hx
      have := (hsd i).fwd' (x - Pi.single μ 1) hy μ hxy
      simp only [one_mul, sub_add_cancel] at this
      rw [norm_sub_rev]
      exact this.trans hmono
    · rw [zeroExt_not_mem _ _ hy, zero_sub, norm_neg,
        spacing_wall_eq hϱ hL hx hy ⟨μ, Or.inr (by simp)⟩]
      have := (hsd i).val x hx
      simp only [one_mul] at this
      calc (L : ℝ) * ‖zeroExt (G.Ω 1) (M *ᵥ comp G g i) x‖ ≤ L * (b * C) :=
            mul_le_mul_of_nonneg_left this (by linarith)
        _ = _ := rfl
  · rw [svec_liftOp]
    have := (hsd i).lap x hx
    simp only [one_mul] at this
    refine le_trans ?_ (this.trans hmono)
    refine le_of_eq ?_
    simp only [svec_liftOp]


/-- **Differences of vector fields** (wall bonds cost a factor `L`): the `StarBound` of the
difference `(liftOp M - liftOp M') g`, from the pointwise bounds of the scalar differences. -/
theorem starBound_sub_liftOp (hϱ : 1 < ϱ) (hL : 2 ≤ L) {M M' : Matrix (G.Ω 1) (G.Ω 1) ℂ} {b : ℝ}
    (hb : 0 ≤ b)
    (h : ∀ (f : G.Ω 1 → ℂ) {C : ℝ}, 0 ≤ C →
      (∀ x : G.Ω 1, (G.spacing (x : CTorus d L N₁ m₁ K)) ^ 2 * ‖f x‖ ≤ C) →
      ∀ x ∈ G.Ω 1,
      ‖zeroExt (G.Ω 1) (M *ᵥ f) x - zeroExt (G.Ω 1) (M' *ᵥ f) x‖ ≤ b * C ∧
      (∀ μ : Fin d, G.spacing x *
        ‖(zeroExt (G.Ω 1) (M *ᵥ f) (x + Pi.single μ 1) - zeroExt (G.Ω 1) (M *ᵥ f) x) -
          (zeroExt (G.Ω 1) (M' *ᵥ f) (x + Pi.single μ 1) - zeroExt (G.Ω 1) (M' *ᵥ f) x)‖ ≤
          b * C) ∧
      (∀ μ : Fin d, x + Pi.single μ 1 ∈ G.Ω 1 → G.spacing (x + Pi.single μ 1) *
        ‖(zeroExt (G.Ω 1) (M *ᵥ f) (x + Pi.single μ 1) - zeroExt (G.Ω 1) (M *ᵥ f) x) -
          (zeroExt (G.Ω 1) (M' *ᵥ f) (x + Pi.single μ 1) - zeroExt (G.Ω 1) (M' *ᵥ f) x)‖ ≤
          b * C))
    (g : G.Ω 1 × Fin N → ℂ) {C : ℝ} (hC : 0 ≤ C) (hg : SrcBound G g C) :
    StarBound G ((liftOp N M - liftOp N M') *ᵥ g) (L * (b * C)) := by
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have hbC : 0 ≤ b * C := mul_nonneg hb hC
  have hmono : b * C ≤ L * (b * C) := by nlinarith
  rw [Matrix.sub_mulVec]
  have hsd := fun i : Fin N => h (comp G g i) hC (fun x => hg x i)
  refine ⟨fun y i => ?_, fun x hx μ i => ?_, fun x hx μ i => ?_⟩
  · rw [svec_liftOp_sub]
    by_cases hy : y ∈ G.Ω 1
    · exact ((hsd i y hy).1).trans hmono
    · rw [zeroExt_not_mem _ _ hy, zeroExt_not_mem _ _ hy, sub_zero, norm_zero]
      exact hbC.trans hmono
  · simp only [svec_liftOp_sub]
    have := (hsd i x hx).2.1 μ
    refine (le_of_eq ?_).trans (this.trans hmono)
    congr 2
    ring
  · simp only [svec_liftOp_sub]
    by_cases hy : x - Pi.single μ 1 ∈ G.Ω 1
    · have hxy : x - Pi.single μ 1 + Pi.single μ 1 ∈ G.Ω 1 := by simpa using hx
      have := (hsd i (x - Pi.single μ 1) hy).2.2 μ hxy
      simp only [sub_add_cancel] at this
      refine (le_of_eq ?_).trans (this.trans hmono)
      rw [← norm_neg]
      congr 2
      ring
    · rw [zeroExt_not_mem _ _ hy, zeroExt_not_mem _ _ hy,
        spacing_wall_eq hϱ hL hx hy ⟨μ, Or.inr (by simp)⟩]
      have := (hsd i x hx).1
      calc (L : ℝ) * ‖0 - 0 - (zeroExt (G.Ω 1) (M *ᵥ comp G g i) x -
            zeroExt (G.Ω 1) (M' *ᵥ comp G g i) x)‖
          = L * ‖zeroExt (G.Ω 1) (M *ᵥ comp G g i) x -
            zeroExt (G.Ω 1) (M' *ᵥ comp G g i) x‖ := by
            rw [sub_self, zero_sub, norm_neg]
        _ ≤ L * (b * C) := mul_le_mul_of_nonneg_left this (by linarith)

end Vec

section Family

variable {d L : ℕ} [NeZero L]

/-- `|α|₂ ≤ γ₁/8` is admissible. -/
theorem admPot_of_small {N₁ m₁ K : ℕ} [NeZero N₁] {ϱ : ℝ}
    {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} (hd : 0 < d) {α : G.Ω 1 → ℂ}
    (h : Small G α (gamma1 d / 8)) : AdmPot G α := by
  intro z
  have hz := h z
  have hp : 0 < (G.spacing (z : CTorus d L N₁ m₁ K)) ^ 2 := by
    have := spacing_pos G (x := (z : CTorus d L N₁ m₁ K)); positivity
  have hc : 0 < coerciveConst d := by
    have := gamma1_pos hd; unfold gamma1 at this; linarith
  rw [le_div_iff₀ (by positivity)]
  unfold gamma1 at hz
  nlinarith

/-- The constant of the Green family of `G_s`: `B = 1 + L b + 4 L b / γ₁`, `b = B_G e^{N₀ κ₁}`. -/
noncomputable def famConst (d L : ℕ) (BG κ : ℝ) : ℝ :=
  1 + L * (BG * Real.exp (N0 d L * κ)) + L * (4 * (BG * Real.exp (N0 d L * κ)) / gamma1 d)

omit [NeZero L] in
theorem famConst_ge_one {BG : ℝ} (hBG : 0 ≤ BG) (κ : ℝ) (hd : 0 < d) :
    1 ≤ famConst d L BG κ := by
  have := gamma1_pos hd
  unfold famConst
  have : 0 ≤ (L : ℝ) * (BG * Real.exp (N0 d L * κ)) := by positivity
  have : 0 ≤ (L : ℝ) * (4 * (BG * Real.exp (N0 d L * κ)) / gamma1 d) := by positivity
  linarith

/-- **The decoupled Green operators form a Green family** (R-B2 of LOCALIZATION.md §3.3): for
`M₁ ≥ c_* e^{N₀ κ₁}` and parameters `|s_P| ≤ e^{κ₁}`, `α ↦ G_s(α)` is a `GreenFamily` on the
polydisc `|α|₂ ≤ γ₁/8` with constant `famConst`. -/
theorem decGreenFamily (hd : 3 ≤ d) (hL : 3 ≤ L) :
    ∃ cstar BG : ℝ, 0 ≤ cstar ∧ 0 ≤ BG ∧ ∀ {N₁ m₁ K : ℕ} [NeZero N₁] {ϱ : ℝ}
      (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) {a : ℕ → ℝ} {ν : ℝ}, DGSetting G a ν →
      ∀ {κ : ℝ}, 0 ≤ κ → cstar * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁ →
      ∀ {s : DecParams G}, (∀ P, ‖s P‖ ≤ Real.exp κ) → ∀ (N : ℕ),
      GreenFamily G N (fun α => Gs G a ν α (extS G s)) (famConst d L BG κ) (gamma1 d / 8) := by
  obtain ⟨c1, B1, hc1, hB1, H1⟩ := dg2_sup (d := d) (L := L) hd hL
  obtain ⟨c2, B2, hc2, hB2, H2⟩ := dg4_lipschitz_fwd' (d := d) (L := L) hd hL
  have hd0 : 0 < d := by omega
  have hγ := gamma1_pos hd0
  refine ⟨max c1 c2, max B1 B2, le_max_of_le_left hc1, le_max_of_le_left hB1, ?_⟩
  intro N₁ m₁ K _ ϱ G a ν S κ hκ hMκ s hs N
  have hE : 0 < Real.exp (N0 d L * κ) := Real.exp_pos _
  have hMκ1 : c1 * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁ :=
    le_trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hE.le) hMκ
  have hMκ2 : c2 * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁ :=
    le_trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hE.le) hMκ
  have hBG : 0 ≤ max B1 B2 := le_max_of_le_left hB1
  have hϱ := S.one_lt_rho
  have hL2 : 2 ≤ L := by omega
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have hs' : ∀ P, ‖extS G s P‖ ≤ Real.exp κ := by
    intro P
    unfold extS
    split_ifs with h
    · exact hs ⟨P, h⟩
    · simpa using Real.one_le_exp hκ
  set b : ℝ := max B1 B2 * Real.exp (N0 d L * κ) with hb
  have hb0 : 0 ≤ b := by positivity
  have hw1 : IsWeight G (gammaW d) (fun _ => (1 : ℝ)) := IsWeight.one G (gammaW_nonneg hd0)
  have hFam : 1 ≤ famConst d L (max B1 B2) κ := famConst_ge_one hBG κ hd0
  have hLb : (L : ℝ) * b ≤ famConst d L (max B1 B2) κ := by
    unfold famConst
    have : 0 ≤ (L : ℝ) * (4 * (max B1 B2 * Real.exp (N0 d L * κ)) / gamma1 d) := by positivity
    rw [hb]; linarith
  have hLl : (L : ℝ) * (4 * b / gamma1 d) ≤ famConst d L (max B1 B2) κ := by
    unfold famConst
    have : 0 ≤ (L : ℝ) * (max B1 B2 * Real.exp (N0 d L * κ)) := by positivity
    rw [hb]; linarith
  refine ⟨by linarith, ?_, ?_⟩
  · intro α hα g C hC hg
    have hadm := admPot_of_small hd0 hα
    have hsc := supBounds_liftOp (N := N) (G := G) (M := Gs G a ν α (extS G s)) hϱ hL2 hb0
      (fun f C' hC' hf => (((H1 G S hadm hκ hMκ1 hs' hw1 f hC' (fun x => by simpa using hf x)).2).mono
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hE.le) hC')))
      g hC hg
    refine (Balaban.Background.SupBounds.star hsc).mono ?_
    calc (L : ℝ) * (b * C) = (L * b) * C := by ring
      _ ≤ famConst d L (max B1 B2) κ * C := mul_le_mul_of_nonneg_right hLb hC
  · intro α α' hα hα' g C Δ hC hg hΔ0 hΔ
    have hadm := admPot_of_small hd0 hα
    have hadm' := admPot_of_small hd0 hα'
    have hdiff := starBound_sub_liftOp (N := N) (G := G) (M := Gs G a ν α (extS G s))
      (M' := Gs G a ν α' (extS G s)) hϱ hL2 (b := 4 * b * Δ / gamma1 d) (by positivity)
      (fun f C' hC' hf x hx => by
        obtain ⟨v1, v2, v3, -⟩ := H2 G S hκ hMκ2 hs f hC' (fun z => hf z) hα hα' hΔ0 hΔ x hx
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
    have hΔC : 0 ≤ Δ * C := by positivity
    calc (L : ℝ) * (4 * b * Δ / gamma1 d * C) = (L * (4 * b / gamma1 d)) * (Δ * C) := by ring
      _ ≤ B * (Δ * C) := mul_le_mul_of_nonneg_right hLl hΔC
      _ ≤ B * (B * (Δ * C)) := by
          apply mul_le_mul_of_nonneg_left _ (by linarith)
          nlinarith
      _ = B * (Δ * (B * C)) := by ring

end Family

end Balaban.Localization
