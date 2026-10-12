/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.StepComplexSmall
public import Balaban.Fluctuation.Prop33CloseWitness
public import Balaban.Inhabited.XiCDomains
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FunProp

/-!
# Proposition 2.6 at a complex datum: all premises hold at a nonreal block datum (non-vacuity)

`prop26C_class_of_activity` has the hypothesis bundle of the complex chart of RAY-CHART §1
(`FlCore`, the margins of the covariance chart and of the ray, `XiCData` of the block datum) and
the inputs `ClassRegularC`, `StepActivityBoundC`.  This file shows that the bundle is not vacuous,
at a real datum and at a genuinely nonreal one:

* `exists_inPsiTildeC_nonreal`, `exists_xiC_nonreal`, `exists_nonreal_xiCData`: the chart
  `Ξ^c(𝔹; 1, ε)` contains nonreal data for every `ε > 0`: the constant datum
  `θ ≡ e₀ + i τ e₁`, `h ≡ e₀`, for a small `τ > 0` (the conditions of `Ψ̃^c(δ, ε)` are strict);
* `exists_chart_params`: the constants of the chart (`d = L = 3`, `N₁ = 6`, `k = 1`, `N = 2`,
  `a₁ = 1`, `ν = 0`): `FlCore` for the pair of levels `(𝔹_1, 𝔹_2)` and all margins;
* `chartSetting`, `exists_prop26C_datum_of_xiCData`: for every block datum of this chart with
  `h ≡ e₀` there is a step datum with this `θ`, `β > 0` large and a small radius `p₁ > 0`, at which
  all premises of
  `prop26C_class_of_activity` hold for the class with zero old terms and `g = 0` (in particular
  `StepActivityBoundC`), hence the identity of Proposition 2.6 for the holomorphic objects;
* `exists_prop26C_real_datum` (the real datum `θ ≡ h ≡ e₀` of `StepRegWitness`),
  `exists_prop26C_nonreal_datum` (a nonreal `θ`).
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.Inhabited
  Balaban.Localization.I5Inhabited Balaban.SmallField.Def6 Balaban.SmallField Finset Filter
  Topology

/-! ### Nonreal data of the chart -/

section Nonreal

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- The norm `vn` of a vector with one nonzero coordinate. -/
theorem vn_single (j : Fin N) (c : ℂ) : vn (fun i => if i = j then c else 0) = ‖c‖ := by
  unfold vn
  rw [EuclideanSpace.norm_eq]
  have h : ∀ i : Fin N, ‖(WithLp.toLp 2 (fun i : Fin N => if i = j then c else 0) :
      EuclideanSpace ℂ (Fin N)) i‖ ^ 2 = if i = j then ‖c‖ ^ 2 else 0 := by
    intro i
    by_cases h : i = j <;> simp [h]
  simp only [h, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  exact Real.sqrt_sq (norm_nonneg c)

/-- The imaginary displacement `i τ e₁` of `ℂ^N`, `N ≥ 2`. -/
noncomputable def imShift (hN : 1 < N) (τ : ℝ) : Fin N → ℂ :=
  fun i => if i = ⟨1, hN⟩ then Complex.I * (τ : ℂ) else 0

/-- **The constant datum `θ ≡ e₀ + i τ e₁`, `h ≡ e₀` lies in the complex data domain
`Ψ̃^c(𝔹; δ, ε)`** for `0 ≤ τ < δ`, `τ² < δ`: a nonreal datum for `τ > 0`. -/
theorem exists_inPsiTildeC_nonreal (G : GeneratingSet d L N₀ k ϱ) (hN : 1 < N) (ν : ℝ)
    {δ ε τ : ℝ} (hδ : 0 < δ) (hε : 0 < ε) (hτ0 : 0 ≤ τ) (hτδ : τ < δ) (hτ2 : τ ^ 2 < δ) :
    InPsiTildeC G ν δ ε (fun _ => unitVec (lt_trans one_pos hN)) (unitVec (lt_trans one_pos hN))
      (fun _ : Torus d (N₀ * L ^ k) => imShift hN τ)
      (0 : Torus d (N₀ * L ^ k) → Fin N → ℂ) :=
  { toInPsiTilde := (exists_inPsiTildeC (G := G) (N := N) (lt_trans one_pos hN) ν hδ
      hε).toInPsiTilde
    eps_pos := hε
    layerConst' := fun _ _ _ _ _ _ _ => rfl
    hLayerConst' := fun _ _ _ _ _ _ _ => rfl
    c1 := fun x x' _ => by simpa [vn] using hδ
    c2a := fun x _ => by
      show vn (imShift hN τ) < ε + δ
      unfold imShift
      rw [vn_single]
      simp only [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hτ0]
      linarith
    c2b := fun x _ => by
      show ‖∑ i, ((unitVec (lt_trans one_pos hN) i : ℂ) + imShift hN τ i) *
          ((unitVec (lt_trans one_pos hN) i : ℂ) + imShift hN τ i) -
        ∑ i, (unitVec (lt_trans one_pos hN) i : ℂ) * (unitVec (lt_trans one_pos hN) i : ℂ)‖ < δ
      have hterm : ∀ i : Fin N, ((unitVec (lt_trans one_pos hN) i : ℂ) + imShift hN τ i) *
          ((unitVec (lt_trans one_pos hN) i : ℂ) + imShift hN τ i) =
          (unitVec (lt_trans one_pos hN) i : ℂ) * (unitVec (lt_trans one_pos hN) i : ℂ) +
            (if i = ⟨1, hN⟩ then -((τ : ℂ) ^ 2) else 0) := by
        intro i
        by_cases hi : i = ⟨1, hN⟩
        · subst hi
          have hu : unitVec (lt_trans one_pos hN) (⟨1, hN⟩ : Fin N) = 0 := by
            simp [unitVec, Fin.ext_iff]
          unfold imShift
          rw [hu]
          simp only [↓reduceIte, Complex.ofReal_zero]
          linear_combination ((τ : ℂ)) ^ 2 * Complex.I_sq
        · unfold imShift
          simp only [hi, ↓reduceIte, add_zero]
      have hsum : ∑ i, ((unitVec (lt_trans one_pos hN) i : ℂ) + imShift hN τ i) *
          ((unitVec (lt_trans one_pos hN) i : ℂ) + imShift hN τ i) -
          ∑ i, (unitVec (lt_trans one_pos hN) i : ℂ) * (unitVec (lt_trans one_pos hN) i : ℂ) =
          -((τ : ℂ) ^ 2) := by
        simp only [hterm, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
        ring
      rw [hsum, norm_neg, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hτ0]
      exact hτ2
    c3a := fun x _ => by simp only [Pi.zero_apply]; simpa [vn] using by positivity
    c3b := fun x _ => by simp only [Pi.zero_apply]; simpa using by positivity }

/-- **`Ξ^c_k(𝔹; 1, ε)` contains a nonreal member for every `ε > 0`**: `θ ≡ e₀ + i τ e₁`,
`h ≡ e₀`, for some `τ > 0`. -/
theorem exists_xiC_nonreal {a : ℕ → ℝ} {ν : ℝ} (H : BgHyp d L k ϱ a ν)
    (G : GeneratingSet d L N₀ k ϱ) (hN : 1 < N) (hν : ν * ((L : ℝ) ^ k) ^ 2 ≤ 1) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ τ : ℝ, 0 < τ ∧ XiC G a ν k 1 ε
      (fun _ : Torus d (N₀ * L ^ k) => unitVec (lt_trans one_pos hN))
      (unitVec (lt_trans one_pos hN)) (fun _ => imShift hN τ) 0 := by
  have hK := bgK1_pos d L N
  have hc0 := bgC0_pos d L N (by have := H.hd; omega)
  have hc1 := bgC1_pos' (d := d) (L := L) (N := N) (by have := H.hd; omega)
  set δ : ℝ := min (ε / (2 * bgK1 d L N + 2)) (min (bgC0 d L N) (bgC1 d L N)) with hδ
  have hδ0 : 0 < δ := by positivity
  have hδc0 : δ ≤ bgC0 d L N := (min_le_right _ _).trans (min_le_left _ _)
  have hδc1 : δ ≤ bgC1 d L N := (min_le_right _ _).trans (min_le_right _ _)
  have hδε : δ ≤ ε / (2 * bgK1 d L N + 2) := min_le_left _ _
  have hden : 0 < 2 * bgK1 d L N + 2 := by positivity
  set τ : ℝ := min δ 1 / 2 with hτ
  have hm0 : 0 < min δ 1 := lt_min hδ0 one_pos
  have hτ0 : 0 < τ := by positivity
  have hτδ : τ < δ := by
    have := min_le_left δ 1
    rw [hτ]; linarith
  have hτ1 : τ ≤ 1 / 2 := by
    have := min_le_right δ 1
    rw [hτ]; linarith
  have hτ2 : τ ^ 2 < δ := by nlinarith
  have hP := exists_inPsiTildeC_nonreal (G := G) hN ν hδ0 hδ0 hτ0.le hτδ hτ2
  refine ⟨τ, hτ0, psiTildeC_subset_xiC (a := a) H hδ0 le_rfl hδc0 hδc1 ?_ hP (εb := ε) ?_⟩
  · have h1 : ν * ((L : ℝ) ^ k) ^ 2 * δ ^ 2 ≤ 1 * δ ^ 2 :=
      mul_le_mul_of_nonneg_right hν (by positivity)
    linarith
  · rw [le_div_iff₀ hden] at hδε
    nlinarith

/-- **`XiCData` holds at a nonreal datum with a real constant `h`**, on a generating set whose
`Ω₁` is the whole torus, for every `ε > 0` and `N ≥ 2`. -/
theorem exists_nonreal_xiCData {N₁ m₁ K : ℕ} [NeZero N₁] {a : ℕ → ℝ} {ν : ℝ}
    (H : BgHyp d L K ϱ a ν) (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) (hΩ : ∀ x, x ∈ G.Ω 1)
    (hN : 1 < N) (hν : ν * ((L : ℝ) ^ K) ^ 2 ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ D : BgData G N, XiCData G a ν K 1 ε D ∧
      (∀ x i, D.h x i = (unitVec (lt_trans one_pos hN) i : ℂ)) ∧ ¬ D.IsReal := by
  obtain ⟨τ, hτ, hX⟩ := exists_xiC_nonreal H G hN hν hε
  have hR := complexData_realizes (G := G) (Ψ₀ := fun _ => unitVec (lt_trans one_pos hN))
    (h₀ := unitVec (lt_trans one_pos hN)) (Ψ'' := fun _ => imShift hN τ) (h'' := 0)
    (fun _ _ _ _ _ _ _ => rfl) (fun _ _ _ _ _ _ _ => rfl) (fun _ _ _ _ _ _ _ => rfl)
  refine ⟨_, ⟨_, _, _, 0, hX, hR⟩, fun x i => ?_, fun hreal => ?_⟩
  · have := hR.2 x (hΩ x) i
    simpa using this
  · have hx : (0 : Torus d (N₁ * L ^ m₁ * L ^ K)) ∈ dataSites G :=
      (mem_dataSites _).2 (Or.inl (hΩ 0))
    have h1 := hR.1 0 hx ⟨1, hN⟩
    have h2 := (hreal 0 ⟨1, hN⟩).1
    rw [h1] at h2
    simp [imShift] at h2
    exact hτ.ne' h2

end Nonreal

/-! ### The constants of the chart -/

/-- **The constants of the complex chart at the levels `(𝔹_1, 𝔹_2)`** (`d = L = 3`, `N₁ = 6`,
`N = 2`, `a₁ = 1`, `ν = 0`): `FlCore` for the pair, with `ε' = δ₁ = t > 0`, and the margins of
the covariance chart (`cstarX e^{N₀κ} ≤ L^{m₁}`, `decDomMargin < δc`, `K₄ C₁ ε < γ/2`,
`δc² smallConstX ≤ ¼`) and of the ray (`c₇ ≤ C₃`, `2 C₄ K₁ C₁ ε + 5 R δ₁ ≤ c₁` with `R = 2`). -/
theorem exists_chart_params :
    ∃ (m₁ : ℕ) (c BG κ t c₂ BG₂ δc : ℝ), 0 < t ∧
      FlCore 2 (GP m₁ (rhoSep m₁)) (stepG 3 3 6 m₁ 1 (rhoSep m₁)) 1 0 c BG κ t (levelKc 3 3)
        (Cchi 3 3) c₂ BG₂ t ∧
      cstarX 3 3 * Real.exp ((N0 3 3 : ℝ) * κ) ≤ ((3 : ℕ) : ℝ) ^ m₁ ∧
      decDomMargin 3 3 2 BG κ (xiC1 3 * t) < δc ∧
      K4 3 3 2 BG κ * (xiC1 3 * t) < coerciveConst 3 / 2 ∧
      δc ^ 2 * smallConstX 3 3 κ ≤ 1 / 4 ∧
      c7 3 3 2 BG κ ≤ thm73C3 3 3 2 ∧
      2 * (compC4 3 * (bgK1 3 3 2 * (xiC1 3 * t))) + 5 * (2 * t) ≤ bgC1 3 3 2 := by
  obtain ⟨c, BG0, hS0⟩ := decSpecs_exists (d := 3) (L := 3) (by norm_num) (by norm_num)
  set BG := max BG0 1 with hBGdef
  have hS : DecSpecs 3 3 c BG := hS0.mono_BG (le_max_left _ _)
  have hBG1 : 1 ≤ BG := le_max_right _ _
  obtain ⟨c₂, BG₂, hS2⟩ := Dec2.decSpecs_exists (d := 3) (L := 3) (Kc := levelKc 3 3)
    (Cx := Cchi 3 3) (by norm_num) (by norm_num) (levelKc_nonneg 3 3) (Cchi_nonneg 3 3)
  have hT3 := thm73C3_pos (d := 3) (L := 3) (N := 2) (by norm_num)
  set κ : ℝ := max 1 (1 / thm73C3 3 3 2) with hκdef
  have hκ0 : 0 < κ := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hκ2 : 1 / thm73C3 3 3 2 ≤ κ := le_max_right _ _
  obtain ⟨m₁, h4, hm⟩ := exists_m₁ (max (max (c * Real.exp ((N0 3 3 : ℝ) * κ))
    (c₂ * Real.exp ((N0 3 3 : ℝ) * κ))) (cstarX 3 3 * Real.exp ((N0 3 3 : ℝ) * κ)))
  have hm1 : c * Real.exp ((N0 3 3 : ℝ) * κ) ≤ ((3 : ℕ) : ℝ) ^ m₁ :=
    ((le_max_left _ _).trans (le_max_left _ _)).trans (by exact_mod_cast hm)
  have hm2 : c₂ * Real.exp ((N0 3 3 : ℝ) * κ) ≤ ((3 : ℕ) : ℝ) ^ m₁ :=
    ((le_max_right _ _).trans (le_max_left _ _)).trans (by exact_mod_cast hm)
  have hm3 : cstarX 3 3 * Real.exp ((N0 3 3 : ℝ) * κ) ≤ ((3 : ℕ) : ℝ) ^ m₁ :=
    (le_max_right _ _).trans (by exact_mod_cast hm)
  have Sdg := dgSetting_rho h4
  have SH : Dec2.OpSetting (stepG 3 3 6 m₁ 1 (rhoSep m₁)) (compWeight 3 1) 0 :=
    { hd := Sdg.hd, hL := Sdg.hL, mass := Sdg.mass, massLe := Sdg.massLe,
      weights := Sdg.weights, sep := Sdg.sep }
  have hG : IsLevel (stepG 3 3 6 m₁ 1 (rhoSep m₁)) 1 := isLevel_levelGS le_rfl (Nat.le_succ 1)
  have hev := flCore_level_eventually (N := 2) Sdg SH hG (isLevel_GP m₁) (bgHyp_rho m₁) hS
    (κ := κ) hκ0 hm1 hS2 hm2
  have hsC : 0 ≤ smallConstX 3 3 κ := by
    unfold smallConstX
    have := kConstX_nonneg 3 3 κ
    linarith
  set δc : ℝ := 1 / (2 * (smallConstX 3 3 κ + 1)) with hδcdef
  have hδc0 : 0 < δc := by positivity
  have hδcs : δc ^ 2 * smallConstX 3 3 κ ≤ 1 / 4 := by
    have e : δc ^ 2 * smallConstX 3 3 κ =
        smallConstX 3 3 κ / (4 * (smallConstX 3 3 κ + 1) ^ 2) := by
      rw [hδcdef]; field_simp; ring
    rw [e, div_le_iff₀ (by positivity)]
    nlinarith
  have hcc := coerciveConst_pos (d := 3) (by norm_num)
  have hb1 := bgC1_pos' (d := 3) (L := 3) (N := 2) (by norm_num)
  have e1 := ev_lt (f := fun t : ℝ => decDomMargin 3 3 2 BG κ (xiC1 3 * t))
    (by unfold decDomMargin; fun_prop) (c := δc) (by simpa [decDomMargin] using hδc0)
  have e2 := ev_lt (f := fun t : ℝ => K4 3 3 2 BG κ * (xiC1 3 * t)) (by fun_prop)
    (c := coerciveConst 3 / 2) (by simpa using hcc)
  have e3 := ev_lt (f := fun t : ℝ => 2 * (compC4 3 * (bgK1 3 3 2 * (xiC1 3 * t))) + 5 * (2 * t))
    (by fun_prop) (c := bgC1 3 3 2) (by simpa using hb1)
  have hpos : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  have wk : ∀ {p : ℝ → Prop}, (∀ᶠ t in 𝓝 (0 : ℝ), p t) → ∀ᶠ t in 𝓝[>] (0 : ℝ), p t :=
    fun h => eventually_nhdsWithin_of_eventually_nhds h
  obtain ⟨t, ht0, ⟨hFl⟩, h1, h2, h3⟩ :=
    (hpos.and (hev.and ((wk e1).and ((wk e2).and (wk e3))))).exists
  exact ⟨m₁, c, BG, κ, t, c₂, BG₂, δc, ht0, hFl, hm3, h1, h2, hδcs,
    c7_le_thm73C3_of_large (by norm_num) hBG1 hκ2, h3.le⟩

/-! ### All premises of Proposition 2.6 at a datum of the chart -/

/-- The step datum with a given block datum `θ = D` of `𝔹_2` (`d = L = 3`, `N₁ = 6`, `k = 1`,
`N = 2`, `h ≡ e₀`, `a₁ = 1`, `ν = 0`), and the numbers `β`, `p₁ = p` (the threshold `δ` of the real
characteristic functions is not used by the complex step). -/
noncomputable def chartSetting (m₁ : ℕ) (D : BgData (GP m₁ (rhoSep m₁)) 2)
    (hDh : ∀ x i, D.h x i = (unitVec hN2 i : ℂ)) (β p : ℝ) :
    StepSetting 3 3 6 m₁ 1 2 (rhoSep m₁) where
  G' := GP m₁ (rhoSep m₁)
  hk1 := le_rfl
  hG' := isLevel_GP m₁
  D' := D
  h₀ := unitVec hN2
  hh₀ := hDh
  a₁ := 1
  ν := 0
  β := β
  p₁ := p
  δ := 1

/-- **Proposition 2.6 for the complex step with all premises discharged, at a given block datum of
the chart** (`d = L = 3`, `N₁ = 6`, `k = 1`, `N = 2`, `a₁ = 1`, `ν = 0`): for the constants of
`exists_chart_params` and every block datum `D` of `Ξ^c(𝔹_2; 1, t)` with `h ≡ e₀` (real or
complex), there are `β > 0` and a radius `p > 0` such that at the step datum `chartSetting` with
`θ = D` the bundle of `prop26C_class_of_activity` holds for the class with zero old terms and
`g = 0` — `FlCore`, `XiCData`, `ClassRegularC`, `StepRegularC`, `StepActivityBoundC` — and hence
the identity (2.6) for the holomorphic objects.  (`β` is large for the margin `√N β_k^{-1/2} C_sup p⁺ < δ₁`, `p⁺ = 2`;
`p` is small for the activity bound.) -/
theorem exists_prop26C_datum_of_xiCData {m₁ : ℕ} {c BG κ t c₂ BG₂ δc : ℝ}
    (hFl : FlCore 2 (GP m₁ (rhoSep m₁)) (stepG 3 3 6 m₁ 1 (rhoSep m₁)) 1 0 c BG κ t
      (levelKc 3 3) (Cchi 3 3) c₂ BG₂ t)
    (hMX : cstarX 3 3 * Real.exp ((N0 3 3 : ℝ) * κ) ≤ ((3 : ℕ) : ℝ) ^ m₁)
    (hdm : decDomMargin 3 3 2 BG κ (xiC1 3 * t) < δc)
    (hα : K4 3 3 2 BG κ * (xiC1 3 * t) < coerciveConst 3 / 2)
    (hsm : δc ^ 2 * smallConstX 3 3 κ ≤ 1 / 4)
    (hc7 : c7 3 3 2 BG κ ≤ thm73C3 3 3 2)
    (hsmR : 2 * (compC4 3 * (bgK1 3 3 2 * (xiC1 3 * t))) + 5 * (2 * t) ≤ bgC1 3 3 2)
    (D : BgData (GP m₁ (rhoSep m₁)) 2)
    (hXi : XiCData (GP m₁ (rhoSep m₁)) (compWeight 3 1) 0 2 1 t D)
    (hDh : ∀ x i, D.h x i = (unitVec hN2 i : ℂ)) :
    ∃ β p : ℝ, 0 < β ∧ 0 < p ∧
      (chartSetting m₁ D hDh β p).ClassRegularC (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) 0 ∧
      (chartSetting m₁ D hDh β p).StepRegularC (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) 0 ∧
      Nonempty (StepActivityBoundC (chartSetting m₁ D hDh β p)
        (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) 0) ∧
      (chartSetting m₁ D hDh β p).TstepC (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) 0 =
        Complex.exp (-(β : ℂ) * (chartSetting m₁ D hDh β p).AnewC +
          EcompAtC (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)).m₀
            (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)).Tm (compWeight 3 1) 0 (Nat.le_succ 1)
            (chartSetting m₁ D hDh β p).psiKdC -
          ((chartSetting m₁ D hDh β p).Eppp (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) : ℂ) *
            ((chartSetting m₁ D hDh β p).nU : ℂ) +
          FcompAtC (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)).m₀
            (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)).Tm (compWeight 3 1) 0 (Nat.le_succ 1)
            (chartSetting m₁ D hDh β p).psiKdC 0 +
          (chartSetting m₁ D hDh β p).E0C (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) +
          (chartSetting m₁ D hDh β p).F0C (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) 0) := by
  classical
  have ht0 : 0 < t := hFl.eps_pos
  set cS : ℝ := covSupConstC 3 3 2 (compWeight 3 1 1) κ with hcS
  set s2 : ℝ := Real.sqrt ((2 : ℕ) : ℝ) with hs2
  have hs20 : 0 ≤ s2 := Real.sqrt_nonneg _
  set A : ℝ := s2 * (|cS| * 2) with hA
  have hA0 : 0 ≤ A := by positivity
  set T : ℝ := A / t + 1 with hTdef
  have hT : 0 < T := by positivity
  set S₀ : StepSetting 3 3 6 m₁ 1 2 (rhoSep m₁) := chartSetting m₁ D hDh (T ^ 2 / 3) 1 with hS₀
  have hβ : 0 < S₀.β := by
    show 0 < T ^ 2 / 3
    positivity
  have hbetaU : S₀.betaU = T ^ 2 := by
    unfold StepSetting.betaU
    show T ^ 2 / 3 * (((3 : ℕ) : ℝ) ^ 1) ^ 3 / (((3 : ℕ) : ℝ) ^ 1) ^ 2 = T ^ 2
    norm_num
    ring
  have hδ₁ : Real.sqrt ((2 : ℕ) : ℝ) * (S₀.betaU ^ (-(1 / 2 : ℝ)) *
      (covSupConstC 3 3 2 (compWeight 3 S₀.a₁ 1) κ * 2)) < t := by
    rw [hbetaU]
    have e : (T ^ 2) ^ (-(1 / 2) : ℝ) = T⁻¹ := by
      rw [Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow, Real.sqrt_sq hT.le]
    rw [e]
    show s2 * (T⁻¹ * (cS * 2)) < t
    have hTi : 0 ≤ T⁻¹ := inv_nonneg.2 hT.le
    have h1 : s2 * (T⁻¹ * (cS * 2)) ≤ A / T := by
      have hle : cS * 2 ≤ |cS| * 2 := by nlinarith [le_abs_self cS]
      have h2 : s2 * (T⁻¹ * (cS * 2)) ≤ s2 * (T⁻¹ * (|cS| * 2)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hle hTi) hs20
      have h3 : s2 * (T⁻¹ * (|cS| * 2)) = A / T := by rw [hA]; field_simp
      linarith
    have h4 : A / T < t := by
      rw [div_lt_iff₀ hT]
      have : t * T = A + t := by rw [hTdef]; field_simp
      linarith
    linarith
  have ha₁ : 0 < S₀.a₁ := one_pos
  obtain ⟨p, hp0, hpp, ⟨I⟩⟩ := S₀.exists_activityBoundC_zeroClass (pp := 2) hFl hMX hdm hα hsm
    ha₁ hc7 (R := 2) (by norm_num) hsmR hβ (by norm_num) hδ₁ hXi
  refine ⟨T ^ 2 / 3, p, hβ, hp0, classRegularC_zeroClass_zero _,
    (S₀.withRadius p).stepRegularC_of_class _ hFl hMX hdm hα hsm ha₁ hc7 (R := 2) (by norm_num)
      hsmR hβ.le (by norm_num : (0 : ℝ) < 2) hδ₁ hXi hp0 hpp 0 (classRegularC_zeroClass_zero _),
    ⟨I⟩, ?_⟩
  exact (S₀.withRadius p).prop26C_class_of_activity _ hFl hMX hdm hα hsm ha₁ hc7 (R := 2)
    (by norm_num) hsmR hβ hp0 hpp hδ₁ hXi 0 (classRegularC_zeroClass_zero _) I

/-- **Proposition 2.6 for the complex step at the real datum `θ ≡ h ≡ e₀`** (the block datum
`witnessD` of the landed witnesses `StepRegWitness`, `exists_activity_datum`): every hypothesis of
`prop26C_class_of_activity` holds there (with `β > 0` large, `p₁ > 0` small, the zero class and
`g = 0`): the chart bundle (`FlCore`, `XiCData`), `ClassRegularC`, `StepActivityBoundC`; and the
identity follows. -/
theorem exists_prop26C_real_datum :
    ∃ (m₁ : ℕ) (S : StepSetting 3 3 6 m₁ 1 2 (rhoSep m₁)), S.D'.IsReal ∧ 0 < S.β ∧ 0 < S.p₁ ∧
      (∃ c BG κ t c₂ BG₂ : ℝ,
        FlCore 2 S.G' (stepG 3 3 6 m₁ 1 (rhoSep m₁)) S.a₁ S.ν c BG κ t (levelKc 3 3) (Cchi 3 3)
          c₂ BG₂ t ∧ XiCData S.G' S.a S.ν 2 1 t S.D') ∧
      S.ClassRegularC (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) 0 ∧
      S.StepRegularC (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) 0 ∧
      Nonempty (StepActivityBoundC S (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) 0) ∧
      S.TstepC (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) 0 = Complex.exp (-(S.β : ℂ) * S.AnewC +
        EcompAtC (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)).m₀
          (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)).Tm S.a S.ν (Nat.le_succ 1) S.psiKdC -
          (S.Eppp (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) : ℂ) * (S.nU : ℂ) +
        FcompAtC (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)).m₀
          (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)).Tm S.a S.ν (Nat.le_succ 1) S.psiKdC 0 +
        S.E0C (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) +
        S.F0C (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) 0) := by
  obtain ⟨m₁, c, BG, κ, t, c₂, BG₂, δc, ht0, hFl, hMX, hdm, hα, hsm, hc7, hsmR⟩ :=
    exists_chart_params
  have hX := exists_xiC (bgHyp_rho m₁) (GP m₁ (rhoSep m₁)) hN2 (by simp) ht0
  have hΩ : ∀ x, x ∈ (GP m₁ (rhoSep m₁)).Ω 1 := fun x => (isLevel_GP m₁ x).1
  have hDh : ∀ x i, (witnessD m₁).h x i = (unitVec hN2 i : ℂ) := fun x i =>
    unitBg_h_of_mem (GP m₁ (rhoSep m₁)) hN2 (unitVec hN2) (hΩ x) i
  have hXi : XiCData (GP m₁ (rhoSep m₁)) (compWeight 3 1) 0 2 1 t (witnessD m₁) :=
    ⟨_, _, 0, 0, hX, fun x hx i => by
      rw [show (witnessD m₁).Ψ x i = (unitVec hN2 i : ℂ) from
        unitBg_Ψ_of_mem (GP m₁ (rhoSep m₁)) hN2 (unitVec hN2) hx i]
      simp, fun x hx i => by rw [hDh x i]; simp⟩
  obtain ⟨β, p, hβ, hp, hcl, hreg, hI, hid⟩ := exists_prop26C_datum_of_xiCData hFl hMX hdm hα
    hsm hc7 hsmR (witnessD m₁) hXi hDh
  exact ⟨m₁, chartSetting m₁ (witnessD m₁) hDh β p,
    isReal_of_inDomainR (witnessData_domain (m₁ := m₁) (β := 1) (δ := 1) (δ' := 1) one_pos),
    hβ, hp, ⟨c, BG, κ, t, c₂, BG₂, hFl, hXi⟩, hcl, hreg, hI, hid⟩

/-- **Proposition 2.6 for the complex step at a nonreal block datum, with all premises
discharged**: there is a step datum (`d = L = 3`, `N₁ = 6`, `k = 1`, `N = 2`, `β > 0`, `p₁ > 0`)
whose block datum `θ` is **not real** (`θ ≡ e₀ + i τ e₁`, `τ > 0`; `h ≡ e₀`), lies in the chart
`Ξ^c(𝔹_2; 1, ε)` under `FlCore`, and satisfies `ClassRegularC` and `StepActivityBoundC` (zero
class, `g = 0`); the identity (2.6) for the holomorphic objects holds there.  In particular the
hypothesis bundle of `prop26C_class_of_activity` is not vacuous off the real chart. -/
theorem exists_prop26C_nonreal_datum :
    ∃ (m₁ : ℕ) (S : StepSetting 3 3 6 m₁ 1 2 (rhoSep m₁)), ¬ S.D'.IsReal ∧ 0 < S.β ∧ 0 < S.p₁ ∧
      (∃ c BG κ t c₂ BG₂ : ℝ,
        FlCore 2 S.G' (stepG 3 3 6 m₁ 1 (rhoSep m₁)) S.a₁ S.ν c BG κ t (levelKc 3 3) (Cchi 3 3)
          c₂ BG₂ t ∧ XiCData S.G' S.a S.ν 2 1 t S.D') ∧
      S.ClassRegularC (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) 0 ∧
      S.StepRegularC (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) 0 ∧
      Nonempty (StepActivityBoundC S (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) 0) ∧
      S.TstepC (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) 0 = Complex.exp (-(S.β : ℂ) * S.AnewC +
        EcompAtC (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)).m₀
          (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)).Tm S.a S.ν (Nat.le_succ 1) S.psiKdC -
          (S.Eppp (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) : ℂ) * (S.nU : ℂ) +
        FcompAtC (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)).m₀
          (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)).Tm S.a S.ν (Nat.le_succ 1) S.psiKdC 0 +
        S.E0C (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) +
        S.F0C (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) 0) := by
  obtain ⟨m₁, c, BG, κ, t, c₂, BG₂, δc, ht0, hFl, hMX, hdm, hα, hsm, hc7, hsmR⟩ :=
    exists_chart_params
  obtain ⟨D, hXi, hDh, hnr⟩ := exists_nonreal_xiCData (bgHyp_rho m₁) (GP m₁ (rhoSep m₁))
    (fun x => (isLevel_GP m₁ x).1) (by norm_num : 1 < 2) (by simp) ht0
  obtain ⟨β, p, hβ, hp, hcl, hreg, hI, hid⟩ := exists_prop26C_datum_of_xiCData hFl hMX hdm hα
    hsm hc7 hsmR D hXi hDh
  exact ⟨m₁, chartSetting m₁ D hDh β p, hnr, hβ, hp, ⟨c, BG, κ, t, c₂, BG₂, hFl, hXi⟩, hcl, hreg,
    hI, hid⟩

end Balaban.Fluctuation
