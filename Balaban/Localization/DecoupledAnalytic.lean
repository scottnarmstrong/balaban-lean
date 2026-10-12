/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.DecoupledMain
public import Balaban.Analysis.Cauchy

/-!
# (DG4): analyticity of `G_s(A)` in `(s, A)` and the Lipschitz bound in `A`

Matrix-valued analytic functions: `MatAt M e` means every entry of `M` is analytic at `e`.  Sums,
products, scalar multiples and inverses (where the determinant does not vanish) preserve it.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Finset Matrix

section MatAn

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Every entry of the matrix-valued function `M` is analytic at `e`. -/
def MatAt (M : E → Matrix ι ι ℂ) (e : E) : Prop :=
  ∀ i j, AnalyticAt ℂ (fun e' => M e' i j) e

theorem MatAt.const (C : Matrix ι ι ℂ) (e : E) : MatAt (fun _ => C) e :=
  fun _ _ => analyticAt_const

theorem MatAt.add {M N : E → Matrix ι ι ℂ} {e : E} (hM : MatAt M e) (hN : MatAt N e) :
    MatAt (fun e' => M e' + N e') e := fun i j => (hM i j).add (hN i j)

theorem MatAt.sub {M N : E → Matrix ι ι ℂ} {e : E} (hM : MatAt M e) (hN : MatAt N e) :
    MatAt (fun e' => M e' - N e') e := fun i j => (hM i j).sub (hN i j)

theorem MatAt.mul [Fintype ι] {M N : E → Matrix ι ι ℂ} {e : E} (hM : MatAt M e) (hN : MatAt N e) :
    MatAt (fun e' => M e' * N e') e := by
  intro i j
  simp_rw [Matrix.mul_apply]
  exact Finset.analyticAt_fun_sum _ fun k _ => (hM i k).mul (hN k j)

theorem MatAt.smul {c : E → ℂ} {M : E → Matrix ι ι ℂ} {e : E} (hc : AnalyticAt ℂ c e)
    (hM : MatAt M e) : MatAt (fun e' => c e' • M e') e := by
  intro i j
  simp only [Matrix.smul_apply, smul_eq_mul]
  exact hc.mul (hM i j)

theorem MatAt.sum {κ : Type*} [Fintype ι] (s : Finset κ) {M : κ → E → Matrix ι ι ℂ} {e : E}
    (h : ∀ k ∈ s, MatAt (M k) e) : MatAt (fun e' => ∑ k ∈ s, M k e') e := by
  intro i j
  simp_rw [Matrix.sum_apply]
  exact Finset.analyticAt_fun_sum _ fun k hk => h k hk i j

theorem MatAt.inv [Fintype ι] [DecidableEq ι] {M : E → Matrix ι ι ℂ} {e : E} (hM : MatAt M e) (hdet : (M e).det ≠ 0) :
    MatAt (fun e' => (M e')⁻¹) e := fun i j => analyticAt_inv_apply hM hdet i j

end MatAn

section Params

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ}

/-- The decoupling parameters live on the (finite) set of centres. -/
abbrev DecParams (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) : Type := cubeIdx G → ℂ

/-- Extension of a vector of parameters of the centres by `1` (the factors of `s_z` only involve
centres, `Qset_subset`). -/
noncomputable def extS (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) (s : DecParams G) :
    ℕ × CTorus d L N₁ m₁ K → ℂ :=
  fun P => if h : P ∈ cubeIdx G then s ⟨P, h⟩ else 1

theorem Qset_subset_cubeIdx (q : ℕ × CTorus d L N₁ m₁ K) : Qset G q ⊆ cubeIdx G := by
  intro P hP
  exact ((mem_Qset).1 hP).1

theorem analyticAt_sProd (q : ℕ × CTorus d L N₁ m₁ K) (e : DecParams G × (G.Ω 1 → ℂ)) :
    AnalyticAt ℂ (fun p : DecParams G × (G.Ω 1 → ℂ) => sProd G (extS G p.1) q) e := by
  unfold sProd
  refine Finset.analyticAt_fun_prod _ fun P hP => ?_
  have hP' : P ∈ cubeIdx G := Qset_subset_cubeIdx q hP
  have : (fun p : DecParams G × (G.Ω 1 → ℂ) => extS G p.1 P) = fun p => p.1 ⟨P, hP'⟩ := by
    funext p; simp [extS, hP']
  rw [this]
  exact ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : cubeIdx G => ℂ) ⟨P, hP'⟩).analyticAt _).comp
    analyticAt_fst

theorem cutOperator_eq_add (a : ℕ → ℝ) (ν : ℝ)
    (cut : Finset (CTorus d L N₁ m₁ K × Fin d)) (α : G.Ω 1 → ℂ) :
    cutOperator G a ν cut α = cutOperator G a ν cut 0 + Matrix.diagonal α := by
  unfold cutOperator
  simp

theorem matAt_cubeH (q : ℕ × CTorus d L N₁ m₁ K) (e : DecParams G × (G.Ω 1 → ℂ)) :
    MatAt (fun p : DecParams G × (G.Ω 1 → ℂ) => cubeH G a ν p.2 q) e := by
  have : (fun p : DecParams G × (G.Ω 1 → ℂ) => cubeH G a ν p.2 q) =
      fun p => cubeH G a ν 0 q + Matrix.diagonal p.2 := by
    funext p; exact cutOperator_eq_add a ν _ p.2
  rw [this]
  refine MatAt.add (MatAt.const _ e) ?_
  intro i j
  by_cases hij : i = j
  · subst hij
    simp only [Matrix.diagonal_apply_eq]
    exact ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : G.Ω 1 => ℂ) i).analyticAt _).comp
      analyticAt_snd
  · simp only [Matrix.diagonal_apply_ne _ hij]
    exact analyticAt_const

theorem matAt_cubeG (S : DGSetting G a ν) {q : ℕ × CTorus d L N₁ m₁ K} (hq : q ∈ cubeIdx G)
    {e : DecParams G × (G.Ω 1 → ℂ)} (hα : AdmPot G e.2) :
    MatAt (fun p : DecParams G × (G.Ω 1 → ℂ) => cubeG G a ν p.2 q) e := by
  unfold cubeG
  refine MatAt.mul (MatAt.inv (matAt_cubeH q e) ?_) (MatAt.const _ e)
  exact ((Matrix.isUnit_iff_isUnit_det _).1 (cubeH_isUnit S hα hq)).ne_zero

theorem matAt_Kcal (S : DGSetting G a ν) {e : DecParams G × (G.Ω 1 → ℂ)} (hα : AdmPot G e.2) :
    MatAt (fun p : DecParams G × (G.Ω 1 → ℂ) => Kcal G a ν p.2 (extS G p.1)) e := by
  unfold Kcal
  refine MatAt.sum _ fun q hq => ?_
  exact MatAt.smul (analyticAt_sProd q e) (MatAt.mul (MatAt.const _ e) (matAt_cubeG S hq hα))

theorem matAt_Gstar (S : DGSetting G a ν) {e : DecParams G × (G.Ω 1 → ℂ)} (hα : AdmPot G e.2) :
    MatAt (fun p : DecParams G × (G.Ω 1 → ℂ) => Gstar G a ν p.2 (extS G p.1)) e := by
  unfold Gstar
  refine MatAt.sum _ fun q hq => ?_
  exact MatAt.smul (analyticAt_sProd q e) (MatAt.mul (MatAt.const _ e) (matAt_cubeG S hq hα))

theorem matAt_Gs (S : DGSetting G a ν) {e : DecParams G × (G.Ω 1 → ℂ)} (hα : AdmPot G e.2)
    (hU : IsUnit (1 - Kcal G a ν e.2 (extS G e.1))) :
    MatAt (fun p : DecParams G × (G.Ω 1 → ℂ) => Gs G a ν p.2 (extS G p.1)) e := by
  unfold Gs
  refine MatAt.mul (matAt_Gstar S hα) (MatAt.inv (MatAt.sub (MatAt.const _ e) (matAt_Kcal S hα)) ?_)
  exact ((Matrix.isUnit_iff_isUnit_det _).1 hU).ne_zero

/-- **Cauchy estimate along a complex line in the potential** (the Lipschitz bound of (DG4)). -/
theorem lipschitz_obs {ι : Type*} [Fintype ι] (r : ι → ℝ) (hr : ∀ z, 0 < r z) {γ V : ℝ} (hγ : 0 < γ)
    (Fo : (ι → ℂ) → ℂ)
    (hFa : ∀ A : ι → ℂ, (∀ z, r z * ‖A z‖ < γ) → AnalyticAt ℂ Fo A)
    (hFb : ∀ A : ι → ℂ, (∀ z, r z * ‖A z‖ ≤ γ) → ‖Fo A‖ ≤ V)
    {A A' : ι → ℂ} (hA' : ∀ z, r z * ‖A' z‖ ≤ γ / 8) {ε : ℝ} (hε : 0 ≤ ε) (hε4 : ε ≤ γ / 4)
    (hAA : ∀ z, r z * ‖A z - A' z‖ ≤ ε) :
    ‖Fo A - Fo A'‖ ≤ 4 * V * ε / γ := by
  have hV : 0 ≤ V := by
    have := hFb A' (fun z => by have := hA' z; linarith)
    exact le_trans (norm_nonneg _) this
  rcases hε.eq_or_lt with h0 | hpos
  · have hAeq : A = A' := by
      funext z
      have := hAA z
      rw [← h0] at this
      have hz := hr z
      have : ‖A z - A' z‖ ≤ 0 := by
        by_contra hne
        have : 0 < ‖A z - A' z‖ := lt_of_not_ge hne
        nlinarith
      exact sub_eq_zero.1 (norm_le_zero_iff.1 this)
    rw [hAeq, sub_self, norm_zero]
    positivity
  set R : ℝ := (7 / 8) * γ / ε with hR
  have hR0 : 0 < R := by positivity
  have hR2 : 3 ≤ R := by
    rw [hR, le_div_iff₀ hpos]; nlinarith
  set g : ℂ → ℂ := fun t => Fo (A' + t • (A - A')) with hg
  have hadm : ∀ t : ℂ, ‖t‖ < R → ∀ z, r z * ‖(A' + t • (A - A')) z‖ < γ := by
    intro t ht z
    have h1 : ‖(A' + t • (A - A')) z‖ ≤ ‖A' z‖ + ‖t‖ * ‖A z - A' z‖ := by
      simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      exact (norm_add_le _ _).trans (by rw [norm_mul])
    have hz := hr z
    have h2 : ‖t‖ * ε < (7 / 8) * γ := by
      calc ‖t‖ * ε < R * ε := mul_lt_mul_of_pos_right ht hpos
        _ = (7 / 8) * γ := by rw [hR]; field_simp
    calc r z * ‖(A' + t • (A - A')) z‖ ≤ r z * (‖A' z‖ + ‖t‖ * ‖A z - A' z‖) :=
          mul_le_mul_of_nonneg_left h1 hz.le
      _ = r z * ‖A' z‖ + ‖t‖ * (r z * ‖A z - A' z‖) := by ring
      _ ≤ γ / 8 + ‖t‖ * ε := by
          have := hA' z
          have h3 : ‖t‖ * (r z * ‖A z - A' z‖) ≤ ‖t‖ * ε :=
            mul_le_mul_of_nonneg_left (hAA z) (norm_nonneg _)
          linarith
      _ < γ := by linarith
  have hdiff : DifferentiableOn ℂ g (Metric.ball 0 R) := by
    intro t ht
    have ht' : ‖t‖ < R := by simpa using ht
    have hpath : AnalyticAt ℂ (fun t : ℂ => A' + t • (A - A')) t :=
      analyticAt_const.add (analyticAt_id.smul analyticAt_const)
    have hcomp : AnalyticAt ℂ (Fo ∘ fun t : ℂ => A' + t • (A - A')) t :=
      AnalyticAt.comp (f := fun t : ℂ => A' + t • (A - A')) (x := t) (hFa _ (hadm t ht')) hpath
    exact hcomp.differentiableAt.differentiableWithinAt
  have hbd : ∀ t ∈ Metric.ball (0 : ℂ) R, ‖g t‖ ≤ V := by
    intro t ht
    have ht' : ‖t‖ < R := by simpa using ht
    exact hFb _ (fun z => (hadm t ht' z).le)
  have h1mem : (1 : ℂ) ∈ Metric.ball (0 : ℂ) R := by
    rw [Metric.mem_ball]; simp; linarith
  have key := Balaban.Analysis.norm_sub_le_of_ball hdiff hbd h1mem
  have hg1 : g 1 = Fo A := by simp [hg]
  have hg0 : g 0 = Fo A' := by simp [hg]
  rw [hg1, hg0] at key
  simp only [dist_zero_right, norm_one] at key
  refine key.trans ?_
  rw [mul_one, hR]
  have : V / ((7 / 8) * γ / ε - 1) ≤ 4 * V * ε / γ := by
    have hR1 : (7 / 8) * γ / ε - 1 ≥ (7 / 8) * γ / ε / 2 := by
      have : 2 ≤ (7 / 8) * γ / ε := by linarith [hR2]
      linarith
    calc V / ((7 / 8) * γ / ε - 1) ≤ V / ((7 / 8) * γ / ε / 2) :=
          div_le_div_of_nonneg_left hV (by positivity) hR1
      _ = 16 * V * ε / (7 * γ) := by field_simp; ring
      _ ≤ 4 * V * ε / γ := by
          rw [div_le_div_iff₀ (by positivity) hγ]
          nlinarith [mul_nonneg hV hε, mul_pos hγ hγ]
  simpa using this

theorem analyticAt_zeroExt_mulVec {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {M : E → Matrix (G.Ω 1) (G.Ω 1) ℂ} {e : E} (hM : MatAt M e) (f : G.Ω 1 → ℂ)
    (y : CTorus d L N₁ m₁ K) :
    AnalyticAt ℂ (fun e' => zeroExt (G.Ω 1) (M e' *ᵥ f) y) e := by
  by_cases hy : y ∈ G.Ω 1
  · have : (fun e' => zeroExt (G.Ω 1) (M e' *ᵥ f) y) =
        fun e' => ∑ z : G.Ω 1, M e' ⟨y, hy⟩ z * f z := by
      funext e'
      rw [zeroExt_of_mem' hy]
      rfl
    rw [this]
    exact Finset.analyticAt_fun_sum _ fun z _ => (hM _ z).mul analyticAt_const
  · have : (fun e' => zeroExt (G.Ω 1) (M e' *ᵥ f) y) = fun _ => 0 := by
      funext e'; exact zeroExt_not_mem _ _ hy
    rw [this]
    exact analyticAt_const

/-- **(DG4), analyticity**: every entry of `G_s(A)` is analytic in `(s, A)` on the polydisc
`|s_P| < e^{κ₁}`, `|A|₂ < γ₁`. -/
theorem dg4_analytic (hd : 3 ≤ d) (hL : 3 ≤ L) :
    ∃ cstar : ℝ, 0 ≤ cstar ∧ ∀ {N₁ m₁ K : ℕ} [NeZero N₁] {ϱ : ℝ}
      (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) {a : ℕ → ℝ} {ν : ℝ}, DGSetting G a ν →
      ∀ {κ : ℝ}, 0 ≤ κ → cstar * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁ →
      ∀ x y : G.Ω 1, AnalyticOnNhd ℂ
        (fun p : DecParams G × (G.Ω 1 → ℂ) => Gs G a ν p.2 (extS G p.1) x y)
        {p | (∀ P, ‖p.1 P‖ < Real.exp κ) ∧
          ∀ z, ‖p.2 z‖ < coerciveConst d / (2 * (G.spacing (z : CTorus d L N₁ m₁ K)) ^ 2)} := by
  obtain ⟨cstar, BG, hc, hB, H⟩ := dg2_sup (d := d) (L := L) hd hL
  refine ⟨cstar, hc, ?_⟩
  intro N₁ m₁ K _ ϱ G a ν S κ hκ hMκ x y e he
  have hα : AdmPot G e.2 := fun z => (he.2 z).le
  have hs : ∀ P, ‖extS G e.1 P‖ ≤ Real.exp κ := by
    intro P
    unfold extS
    split_ifs with h
    · exact (he.1 ⟨P, h⟩).le
    · simpa using Real.one_le_exp hκ
  have hd0 : 0 < d := by omega
  obtain ⟨hU, -⟩ := H G S hα hκ hMκ hs (w := fun _ => 1) (IsWeight.one G (gammaW_nonneg hd0))
    (0 : G.Ω 1 → ℂ) (C := 0) le_rfl (by simp)
  exact matAt_Gs S hα hU x y

/-- **(DG4), the Lipschitz bound in `A`**: for `|A|₂, |A'|₂ ≤ γ₁/8` the increments of the four
pointwise quantities of `G_s(A) f - G_s(A') f` are bounded by `4 B_G e^{N₀κ₁} γ₁⁻¹ |A - A'|₂ |f|₂`. -/
theorem dg4_lipschitz (hd : 3 ≤ d) (hL : 3 ≤ L) :
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
  refine ⟨?_, fun μ => ?_, ?_⟩
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

end Params

end Balaban.Localization
