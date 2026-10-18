/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.WindowDuMass
public import Balaban.LargeField.R.WindowConvPhysSwitchLocGen

/-!
# The action switch from the local background at mass `ν` to the window background at mass `0`

P7 (2.14)-(2.16), blocker 4.  `switch_massZero_of_genSet`: the local background `φ_l = bgFieldC Gl a ν`
of a datum `Dl` of the real domain at the mass `ν` and the field `φ_w ∘ e⁻¹` transported from the
window background `φ_w = bgFieldC Gw a 0` of a datum `Dw` at mass `0` with the same data on the ball
`B(X, R)` (the external field of `Dw` is `0`, that of `Dl` a unit vector): the restricted actions at
`(a, ν, Dl)` differ by at most `A |X|_{mix} (V (…) + V²/2 (…))`, `V ≥ K_w (m · 2) + K (δ_d + (δ_l + δ_w) e^{-γ_w D₀})`.
The difference `φ_w ∘ e⁻¹ - φ_l` is the sum of the stability difference at mass `0`
(`genSet_stability_grad` for the datum `Dl` with its external field replaced by `0`, which does not
change the background at mass `0`) and the mass response (`massResponse_real`).
-/

@[expose] public section

namespace Balaban.LargeField.ActionConv

open Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
  Balaban.Fluctuation Finset

variable {d L N : ℕ} [NeZero L]

/-- The source at mass `0` does not read the external field. -/
theorem source_zero_mass_congr {N₀ k : ℕ} [NeZero N₀] {ϱ : ℝ} {G : GeneratingSet d L N₀ k ϱ}
    (a : ℕ → ℝ) {D D' : BgData G N} (hΨ : D'.Ψ = D.Ψ) : source G a 0 D' = source G a 0 D := by
  unfold source
  rw [hΨ]
  simp

/-- The background at mass `0` depends on the datum only through `Ψ`. -/
theorem bgFieldC_zero_mass_congr {N₀ k : ℕ} [NeZero N₀] {ϱ : ℝ} {G : GeneratingSet d L N₀ k ϱ}
    (a : ℕ → ℝ) (c₀ : ℝ) {D D' : BgData G N} (hΨ : D'.Ψ = D.Ψ) :
    bgFieldC G a 0 c₀ D' = bgFieldC G a 0 c₀ D := by
  have hs := source_zero_mass_congr a hΨ
  have hE : ∀ (φ : G.Ω 1 × Fin N → ℂ) (α : G.Ω 1 → ℂ),
      IsSmallSolution G a 0 c₀ D' φ α ↔ IsSmallSolution G a 0 c₀ D φ α := fun φ α => by
    unfold IsSmallSolution IsEL
    rw [hs]
  by_cases H : ∃! s : (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ), IsSmallSolution G a 0 c₀ D s.1 s.2
  · obtain ⟨⟨φ, α⟩, hs0, hu⟩ := H
    have hu' : ∀ φ' α', IsSmallSolution G a 0 c₀ D φ' α' → φ' = φ ∧ α' = α := fun φ' α' h' => by
      have := hu ⟨φ', α'⟩ h'
      exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
    rw [(bgFieldC_eq ((hE φ α).2 hs0) (fun φ' α' h' => hu' φ' α' ((hE φ' α').1 h'))).1,
      (bgFieldC_eq hs0 hu').1]
  · have H' : ¬ ∃! s : (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ), IsSmallSolution G a 0 c₀ D' s.1 s.2 := by
      rintro ⟨s, hs1, hu1⟩
      exact H ⟨s, (hE _ _).1 hs1, fun s' h' => hu1 s' ((hE _ _).2 h')⟩
    unfold bgFieldC
    simp only [H, H', ↓reduceDIte]

/-- A datum with the same `Ψ` and external field `0`. -/
theorem exists_zero_h {N₀ k : ℕ} [NeZero N₀] {ϱ : ℝ} {G : GeneratingSet d L N₀ k ϱ}
    (D : BgData G N) : ∃ D0 : BgData G N, D0.Ψ = D.Ψ ∧ ∀ x i, D0.h x i = 0 :=
  ⟨⟨D.Ψ, fun _ _ => 0, D.Ψ_layerConst, fun _ _ _ _ _ _ _ => rfl, D.Ψ_zero, fun _ _ => rfl⟩,
    rfl, fun _ _ => rfl⟩

/-- The datum with `h = 0` is in the real domain at mass `0`. -/
theorem inDomainR_zero_mass_zero_h {N₀ k : ℕ} [NeZero N₀] {ϱ : ℝ} {G : GeneratingSet d L N₀ k ϱ}
    {ν δ : ℝ} (hδ : 0 < δ) {D D0 : BgData G N} (hD : InDomainR G ν δ D) (hΨ : D0.Ψ = D.Ψ)
    (hh : ∀ x i, D0.h x i = 0) : InDomainR G 0 δ D0 := by
  obtain ⟨Ψ, h, hP, hΨ', -⟩ := hD
  refine ⟨Ψ, fun _ => 0, ⟨hP.layerConst, hP.r1, hP.r2, fun x _ => ?_, ?_⟩,
    fun x hx i => by rw [hΨ]; exact hΨ' x hx i, fun x _ i => by simp [hh]⟩
  · simpa using pow_pos hδ 2
  · simpa using pow_pos hδ 2

/-- **The switch from the local background at mass `ν` to the window background at mass `0`**. -/
theorem switch_massZero_of_genSet (N : ℕ) (hd : 3 ≤ d) (hL : 3 ≤ L) :
    ∃ K δs Kw δm : ℝ, 0 < K ∧ 0 < δs ∧ 0 < Kw ∧ 0 < δm ∧
      ∀ {N₀l kl N₀w kw : ℕ} [NeZero N₀l] [NeZero N₀w] {ϱl ϱw ϱB : ℝ}
        (Gl : GeneratingSet d L N₀l kl ϱl) (Gw : GeneratingSet d L N₀w kw ϱw)
        (e : Torus d (N₀w * L ^ kw) ≃ Torus d (N₀l * L ^ kl)) {a : ℕ → ℝ} {ν : ℝ},
        (∃ N₁ m₁ : ℕ, N₀l = N₁ * L ^ m₁) →
        BgHyp d L kl ϱl a ν → BgHyp d L kl ϱl a 0 → BgHyp d L kw ϱw a 0 → bgR0 d L ≤ ϱB →
        2 * d * Real.log L ≤ agmonRate d / 16 * (ϱB - 1) → ϱB ≤ ϱl → kl ≤ kw →
        (∀ x μ, e (x + Pi.single μ 1) = e x + Pi.single μ 1) →
        (∀ n, n ≤ kl → ∀ x y, jBlock d L N₀l kl n x = jBlock d L N₀l kl n y ↔
          jBlock d L N₀w kw n (e.symm x) = jBlock d L N₀w kw n (e.symm y)) →
        ∀ (X : Region Gl) (Dc : StepDecomp X) (R : ℝ), (ϱB + 3 * d) * (L : ℝ) ^ kl + 2 ≤ R →
        (∀ x, (∃ z ∈ X.sites, Green.torusDist d (N₀l * L ^ kl) z x ≤ R) →
          ∀ n, 1 ≤ n → n ≤ kl + 1 → (x ∈ Gl.Ω n ↔ e.symm x ∈ Gw.Ω n)) →
        ∀ {Dl : BgData Gl N} {Dw : BgData Gw N} {δl δw δd m : ℝ},
        0 < δl → δl ≤ bgC1 d L N → InDomainR Gl ν δl Dl →
        0 < δw → δw ≤ bgC1 d L N → InDomainR Gw 0 δw Dw → 0 ≤ δd →
        (∀ x, (∃ z ∈ X.sites, Green.torusDist d (N₀l * L ^ kl) z x ≤ R) →
          vn (fun i => Dl.Ψ x i - Dw.Ψ (e.symm x) i) ≤ δd) →
        (∀ x, (∃ z ∈ X.sites, Green.torusDist d (N₀l * L ^ kl) z x ≤ R) →
          ∀ i, Dw.h (e.symm x) i = 0) →
        (∀ x : Gl.Ω 1, ∑ i, ‖Dl.h x i‖ ^ 2 = 1) →
        bgK1 d L N * (δl + δw) + δd ≤ δs →
        bgK1 d L N * δl ≤ min (deltaStar d L N) δm → 0 ≤ m →
        m * 2 ≤ min (deltaStar d L N) δm →
        (∀ x : Gl.Ω 1, ν * Gl.spacing (x : Torus d (N₀l * L ^ kl)) ^ 2 ≤ m) →
        ∀ {β A V Cb Cg Cm Sb Sg Sm : ℝ}, 0 ≤ β → 0 ≤ A → 0 ≤ Cb → 0 ≤ Cg → 0 ≤ Cm →
        0 ≤ Sb → 0 ≤ Sg → 0 ≤ Sm →
        (∀ c, β * ∑ x ∈ (Dc.cube c).sites, ‖levelCoeff Gl a x‖ ≤ Cb * (A * Dc.wt c)) →
        (∀ c, β * ∑ x ∈ (Dc.cube c).sites, ((Gl.spacing x) ^ 2)⁻¹ ≤ Cg * (A * Dc.wt c)) →
        (∀ c, β * ∑ _x ∈ (Dc.cube c).sites, |ν| ≤ Cm * (A * Dc.wt c)) →
        (∀ x ∈ X.sites, ∑ j,
          ‖Dl.Ψ x j - blockAvg Gl (bgFieldC Gl a ν (bgC0 d L N) Dl) x j‖ ^ 2 ≤ Sb) →
        (∀ x ∈ X.sites, ∀ μ : Fin d, Gl.spacing x ^ 2 * ∑ j,
          ‖barField Gl Dl.Ψ (bgFieldC Gl a ν (bgC0 d L N) Dl) (x + Pi.single μ 1) j -
            barField Gl Dl.Ψ (bgFieldC Gl a ν (bgC0 d L N) Dl) x j‖ ^ 2 ≤ Sg) →
        (∀ x ∈ X.sites, ∀ μ : Fin d, Gl.spacing x ^ 2 * ∑ j,
          ‖barField Gl Dl.Ψ (bgFieldC Gl a ν (bgC0 d L N) Dl) (x - Pi.single μ 1) j -
            barField Gl Dl.Ψ (bgFieldC Gl a ν (bgC0 d L N) Dl) x j‖ ^ 2 ≤ Sg) →
        (∀ x ∈ X.sites, ∑ j,
          ‖svec Gl (bgFieldC Gl a ν (bgC0 d L N) Dl) x j - Dl.h x j‖ ^ 2 ≤ Sm) →
        K * (δd + (δl + δw) *
          Real.exp (-(gammaW d * ((R - (ϱB + 3 * d) * (L : ℝ) ^ kl - 2) / (L : ℝ) ^ kl)))) +
          Kw * (m * 2) ≤ V →
        ‖(β : ℂ) * actionRegionC X a ν Dl (bgFieldC Gl a ν (bgC0 d L N) Dl) -
            (β : ℂ) * actionRegionC X a ν Dl
              (transportField (Gl := Gl) e Dw.Ψ (bgFieldC Gw a 0 (bgC0 d L N) Dw))‖ ≤
          A * Dc.total * (V * (Real.sqrt ((Sb * Cb) * (N * Cb)) +
            Real.sqrt ((d * (Sg * Cg)) * (d * (N * Cg))) + Real.sqrt ((Sm * Cm) * (N * Cm))) +
          V ^ 2 / 2 * (N * Cb + d * (N * Cg) + N * Cm)) := by
  obtain ⟨K, δs, hK, hδs, hst⟩ := genSet_stability_grad (L := L) N hd hL
  obtain ⟨Kw, δm, hKw, hδm, hms⟩ := massResponse_real (L := L) N hd hL
  refine ⟨K, δs, Kw, δm, hK, hδs, hKw, hδm, ?_⟩
  intro N₀l kl N₀w kw _ _ ϱl ϱw ϱB Gl Gw e a ν hN Hν H0l H0w hϱB0 hsepB hϱB hk he hblk X Dc R hR hag
    Dl Dw δl δw δd m hδl0 hδl hDl hδw0 hδw hDw hδd hΨ hhw hhl hsm hδm1 hm0 hm2 hsp β A V Cb Cg Cm Sb Sg Sm
    hβ hA hCb hCg hCm hSb hSg hSm hcb hcg hcm hrB hrGf hrGb hrM hV
  obtain ⟨N₁, m₁, hN₁⟩ := hN
  subst hN₁
  have : NeZero N₁ := ⟨left_ne_zero_of_mul (NeZero.ne (N₁ * L ^ m₁))⟩
  have hd0 : 0 < d := by omega
  obtain ⟨Dl0, hΨ0, hh0⟩ := exists_zero_h Dl
  have hDl0 : InDomainR Gl 0 δl Dl0 := inDomainR_zero_mass_zero_h hδl0 hDl hΨ0 hh0
  have e0 := bgFieldC_zero_mass_congr (G := Gl) a (bgC0 d L N) hΨ0
  have hsepl : 2 * d * Real.log L ≤ agmonRate d / 16 * (ϱl - 1) := by
    refine hsepB.trans (mul_le_mul_of_nonneg_left (by linarith) ?_)
    have := agmonRate_pos (d := d) hd0
    positivity
  obtain ⟨hm1, hmf, hmb⟩ := hms a ν δl m Dl Hν H0l hsepl hδl0 hδl hDl hδm1 hm0 hm2 hsp hhl
  have hstab := fun (y : Gl.Ω 1) (hy : (y : Torus d (N₁ * L ^ m₁ * L ^ kl)) ∈ X.sites) =>
    hst Gl Gw e H0l H0w hϱB0 hsepB hϱB hk he hblk X.sites R hR hag hδl0 hδl hDl0 hδw0 hδw hDw hδd
      (fun x hx => by rw [hΨ0]; exact hΨ x hx)
      (fun x hx => by funext i; rw [hh0, hhw x hx i]) hsm y hy
  rw [e0] at hstab
  have hV0 : 0 ≤ V := by
    refine le_trans (add_nonneg (mul_nonneg hK.le (add_nonneg hδd (mul_nonneg
      (add_nonneg hδl0.le hδw0.le) (Real.exp_pos _).le))) (mul_nonneg hKw.le
      (mul_nonneg hm0 (by norm_num)))) hV
  set φl := bgFieldC Gl a ν (bgC0 d L N) Dl with hφl
  set φ0 := bgFieldC Gl a 0 (bgC0 d L N) Dl with hφ0
  set φ' := transportField (Gl := Gl) e Dw.Ψ (bgFieldC Gw a 0 (bgC0 d L N) Dw) with hφ'
  set Vs := K * (δd + (δl + δw) *
    Real.exp (-(gammaW d * ((R - (ϱB + 3 * d) * (L : ℝ) ^ kl - 2) / (L : ℝ) ^ kl)))) with hVs
  have hVm : 0 ≤ Kw * (m * 2) := mul_nonneg hKw.le (mul_nonneg hm0 (by norm_num))
  have hdec : φ' - φl = (fun p => φ' p - φ0 p) - (φl - φ0) := by
    funext p; simp only [Pi.sub_apply]; ring
  refine Region.actionDiff_local_le X Dc a ν Dl φl φ' hβ hA hV0 hCb hCg hCm hSb hSg hSm hcb hcg hcm
    (fun x hx y hy j => ?_) (fun x hx μ j => ?_) (fun x hx μ j => ?_) hrB hrGf hrGb hrM
  · have hyX := X.blockClosed x hx y hy
    have hy1 := X.sub_Ω hyX
    rw [svec_of_mem Gl _ ⟨y, hy1⟩ j]
    have h1 := (hstab ⟨y, hy1⟩ hyX).1 j
    have h2 := hm1 ⟨y, hy1⟩ j
    simp only [one_mul, Pi.sub_apply] at h2 ⊢
    have h3 : ‖φ' (⟨y, hy1⟩, j) - φl (⟨y, hy1⟩, j)‖ ≤
        ‖φ' (⟨y, hy1⟩, j) - φ0 (⟨y, hy1⟩, j)‖ + ‖φl (⟨y, hy1⟩, j) - φ0 (⟨y, hy1⟩, j)‖ := by
      calc _ = ‖(φ' (⟨y, hy1⟩, j) - φ0 (⟨y, hy1⟩, j)) - (φl (⟨y, hy1⟩, j) - φ0 (⟨y, hy1⟩, j))‖ := by
            congr 1; ring
        _ ≤ _ := norm_sub_le _ _
    linarith
  · have hx1 := X.sub_Ω hx
    have h1 : Gl.spacing x * ‖svec Gl (fun p => φ' p - φ0 p) (x + Pi.single μ 1) j -
        svec Gl (fun p => φ' p - φ0 p) x j‖ ≤ Vs := (hstab ⟨x, hx1⟩ hx).2.1 μ j
    have h2 := hmf x hx1 μ j
    rw [hdec, svec_sub (fun p => φ' p - φ0 p) (φl - φ0) (x + Pi.single μ 1) j,
      svec_sub (fun p => φ' p - φ0 p) (φl - φ0) x j]
    simp only [one_mul] at h2
    have key : ‖(svec Gl (fun p => φ' p - φ0 p) (x + Pi.single μ 1) j - svec Gl (φl - φ0) (x + Pi.single μ 1) j) -
        (svec Gl (fun p => φ' p - φ0 p) x j - svec Gl (φl - φ0) x j)‖ ≤
        ‖svec Gl (fun p => φ' p - φ0 p) (x + Pi.single μ 1) j - svec Gl (fun p => φ' p - φ0 p) x j‖ +
        ‖svec Gl (φl - φ0) (x + Pi.single μ 1) j - svec Gl (φl - φ0) x j‖ := by
      calc _ = ‖(svec Gl (fun p => φ' p - φ0 p) (x + Pi.single μ 1) j - svec Gl (fun p => φ' p - φ0 p) x j) -
            (svec Gl (φl - φ0) (x + Pi.single μ 1) j - svec Gl (φl - φ0) x j)‖ := by
            congr 1; ring
        _ ≤ _ := norm_sub_le _ _
    have hsp0 := (spacing_pos Gl (x := x)).le
    have h4 := mul_le_mul_of_nonneg_left key hsp0
    rw [mul_add] at h4
    linarith
  · have hx1 := X.sub_Ω hx
    have h1 : Gl.spacing x * ‖svec Gl (fun p => φ' p - φ0 p) (x - Pi.single μ 1) j -
        svec Gl (fun p => φ' p - φ0 p) x j‖ ≤ Vs := (hstab ⟨x, hx1⟩ hx).2.2 μ j
    have h2 := hmb x hx1 μ j
    rw [hdec, svec_sub (fun p => φ' p - φ0 p) (φl - φ0) (x - Pi.single μ 1) j,
      svec_sub (fun p => φ' p - φ0 p) (φl - φ0) x j]
    simp only [one_mul] at h2
    have key : ‖(svec Gl (fun p => φ' p - φ0 p) (x - Pi.single μ 1) j - svec Gl (φl - φ0) (x - Pi.single μ 1) j) -
        (svec Gl (fun p => φ' p - φ0 p) x j - svec Gl (φl - φ0) x j)‖ ≤
        ‖svec Gl (fun p => φ' p - φ0 p) (x - Pi.single μ 1) j - svec Gl (fun p => φ' p - φ0 p) x j‖ +
        ‖svec Gl (φl - φ0) (x - Pi.single μ 1) j - svec Gl (φl - φ0) x j‖ := by
      calc _ = ‖(svec Gl (fun p => φ' p - φ0 p) (x - Pi.single μ 1) j - svec Gl (fun p => φ' p - φ0 p) x j) -
            (svec Gl (φl - φ0) (x - Pi.single μ 1) j - svec Gl (φl - φ0) x j)‖ := by
            congr 1; ring
        _ ≤ _ := norm_sub_le _ _
    have hsp0 := (spacing_pos Gl (x := x)).le
    have h4 := mul_le_mul_of_nonneg_left key hsp0
    rw [mul_add] at h4
    linarith

end Balaban.LargeField.ActionConv
