/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.ObsMarksFromTower
public import Balaban.Fluctuation.ObsRayActivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The observable marks record at the shared tower, unconditionally

The ray clause of `sourceDirectTerms_scale_fromTower_ray` holds on the full disc `‖ψ̂ p‖ ≤ p₁`
(the margin `(4 + r)(3/2) p₁ < c_ψ` is `StepScaleData.ray_margin_scaled`).  With it the single
hypothesis `hray` of `obsMarks_zeroClass_family_of_ray` is a theorem.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep Filter Topology
  MeasureTheory Metric

open Classical in
/-- **The direct terms of the zero class at the shared tower, with the ray clause on the full
disc.**  As `sourceDirectTerms_scale_fromTower_ray`, with the hat fields of the ray clause
ranging over `‖ψ̂ p‖ ≤ p₁` instead of `‖ψ̂ p‖ ≤ (2/3) p₁`. -/
theorem sourceDirectTerms_scale_fromTower_ray_full {κmin : ℝ} (T : StepTower κmin)
    (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (h3N : 3 ∣ N₁) (hN : 5 < N₁)
    (ν : ℝ) (hνpos : 0 < ν) (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) (β : ℝ) (hβ1 : 1 ≤ β)
    (p₁ : ℝ) (q : ℝ) (hq0 : 0 < q) (hq : q ≤ 1)
    (D : StepScaleData T k hk N₁ ν β p₁)
    (S : StepSetting 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) (hS : S = T.step k hk N₁ ν β p₁)
    (hp : 0 < S.p₁) :
    ∃ (val : ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) → ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) →
        ℂ → (RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 × (CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) → ℂ)
      (𝒴 : Finset (Set (CTorus 3 3 N₁ T.m₁ (k + 1))))
      (Tt : Set (CTorus 3 3 N₁ T.m₁ (k + 1)) → ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) →
        ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) → ℂ →
        (RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 × (CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) → ℂ),
      (∀ x w σ Θ, val x w σ Θ =
        (-(S.β : ℂ)) * raySrc3 (hatFun S.G' S.a₁ S.ν T.t S.hG'
          ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
          (interactionOne S.hG S.hG' (le_refl (k + 1)) S.a₁ S.ν T.t)) taylorWeight x.1 w.1 σ Θ.1 +
        (S.β : ℂ) * (∑ s : CTorus 3 3 N₁ T.m₁ (k + 1) × Fin 2, Θ.2 s.1 s.2 *
          dirTermSrc (hatFun S.G' S.a₁ S.ν T.t S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
            (onXi S.G' S.a₁ S.ν T.t
              (fun D ψ' => svec (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁))
                (flFieldOne S.G' (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) T.BG₂ T.κ S.a₁ S.ν D ψ')
                  s.1 s.2)))
            (fun _ => (1 : ℂ)) x.2 w.2 σ Θ.1)) ∧
      PhysicalSharpLocEta S (lvCpsi T.κ T.t (β * 3 ^ k)) 2 2 (lvR T.κ T.t (β * 3 ^ k) p₁) S.a₁
        S.ν T.t (q / S.β) 𝒴 Tt ∧
      DiagCont (fun ψ : S.U × Fin 2 → ℂ => (ψ, ψ))
        (physXW S (lvCpsi T.κ T.t (β * 3 ^ k)) 2 2 (lvR T.κ T.t (β * 3 ^ k) p₁))
        (physSΛEta S S.a₁ S.ν T.t (q / S.β)) 2 𝒴 Tt ∧
      (∀ Θ ∈ physSΛEta S S.a₁ S.ν T.t (q / S.β),
        ∃ I : DirectTerms S 1 hp (fun ψ => (ψ, ψ)) p₁ 2
            (S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
              (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (q / S.β)) (2 * T.κdec - 1) Θ
            (physSΛEta S S.a₁ S.ν T.t (q / S.β))
            (physXW S (lvCpsi T.κ T.t (β * 3 ^ k)) 2 2 (lvR T.κ T.t (β * 3 ^ k) p₁)) val
            (physAgΘ S) (AgFDirPair S),
          I.𝒴 = 𝒴 ∧ I.T = Tt) ∧
      (rawOf S.D', (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) ∈
        physSΛEta S S.a₁ S.ν T.t (q / S.β) ∧
      (∀ g : Fld 3 3 N₁ T.m₁ (k + 1) 2, ∑ x, ∑ i, ‖g x i‖ < q →
        (rawOf S.D', fun y i => g y i / (S.β : ℂ)) ∈ physSΛEta S S.a₁ S.ν T.t (q / S.β)) ∧
      ∀ (Y : Set (CTorus 3 3 N₁ T.m₁ (k + 1)))
        (Θ : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 × (CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)),
        Θ ∈ physSΛEta S S.a₁ S.ν T.t (q / S.β) → ∀ ψ : S.U × Fin 2 → ℂ,
        (∀ p, ‖ψ p‖ ≤ p₁) →
        DifferentiableOn ℂ (fun ζ : ℂ => Tt Y (ζ • ψ, ζ • ψ) (ζ • ψ, ζ • ψ) 1 Θ)
          (Metric.ball (0 : ℂ) (3 / 2)) := by
  classical
  subst hS
  have h4 := T.m₁_four
  have ht0 := T.t_pos
  have hMX := T.large_block
  have hdm := T.dom_margin
  have hα := T.coer_margin
  have hsmX := T.δc_small
  have hc7 := T.c7_cap
  have g1 := T.t_cap
  have g2 := T.bg0_cap
  have g3 := T.cK2_cap
  have g4 := T.cK2'_cap
  have g5 := T.bg1_cap
  have hκ0 := T.κ0_nonneg
  have hκdec := T.κdec_lower
  have hκ := T.κ_lower
  have h1 := T.κ_one
  have hlog := T.κ_log
  have hxi1 := T.xi_small
  have hν0 : 0 ≤ ν := hνpos.le
  have hβ0 : 0 < β := by linarith
  obtain ⟨R0⟩ := D.ray
  have hcψ0 := D.cψ_pos
  have hr0 := D.r_pos
  have hδ₁ := D.fl_radius
  have hc := D.ray_margin
  have hHB := bgHyp_lv (k := k) T.m₁ hνpos.le hν
  have hC := D.core
  have hD := D.xi
  have hBh := hBh_of_xi (N := 2) (Gp := lvTop N₁ T.m₁ k (rhoSep T.m₁)) hHB hνpos hC.small1
    hC.eps_pos hxi1
  have hN3 : 3 ^ 1 ∣ N₁ := by simpa using h3N
  obtain ⟨hV, hF⟩ := D.covers
  have hBh0 : (0 : ℝ) ≤ 1 + 2 / ν := by positivity
  have hη0 : 0 < q / β := div_pos hq0 hβ0
  obtain ⟨val, 𝒴, Tt, hval, hloc, hcont, hI, hrayT⟩ := sourceDirectTerms_slice_ray
    (hatStepK (N₁ := N₁) k T.m₁ hk ν β p₁ T.δ)
    (ρ := p₁) (εU := β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 1 T.BG T.BG₂ T.κ T.t
      (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (q / β))
    (Rσ := 2) (R₁ := 2) (r := lvR T.κ T.t (β * 3 ^ k) p₁) (R := 2) (m₀ := 1) (κdec := T.κdec)
    (κ₀ := T.κ0) (Bh := 1 + 2 / ν) (δc := T.δc) (cψ := lvCpsi T.κ T.t (β * 3 ^ k))
    (jV := fun _ => k) (XV := fun z => LocalCover.cube 1 k (LocalCover.blockSite k z))
    (𝒦XV := fun z => LocalCover.fam 1 (LocalCover.blockSite k z))
    (X₁V := fun z => LocalCover.nbhdF 1 (LocalCover.blockSite k z))
    (jF := fun _ => k) (XF := fun s => LocalCover.cube 1 k s.1)
    (𝒦XF := fun s => LocalCover.fam 1 s.1) (X₁F := fun s => LocalCover.nbhdF 1 s.1)
    (hC := hC) (hconn := hatConn_lvTop) (hrow := rowInHat_lv hk h4 hN hν0 hν)
    (hκ₀ := hκ0) (hκdec := hκdec) (hκ := by exact_mod_cast hκ) (h1 := h1)
    (hR₁ := by norm_num) (hr := hr0) (hcψ := hcψ0.le) (hMX := hMX) (hdm := hdm) (hα := hα)
    (hsmX := hsmX) (hδ₁ := hδ₁) (ha₁ := one_pos) (H := hHB) (hc7 := hc7) (hR := le_rfl)
    (hRs := g1) (hsmall := g2) (hnum := g3) (hnum' := g4) (hsm := g5)
    (hcovV := fun z => (hV z).1) (hX₁V := fun z => (hV z).2.1)
    (hoptV := fun z => (hV z).2.2.1) (hΔV := fun z => (hV z).2.2.2.1)
    (hlogV := fun _ => hlog) (hZV := fun z => (hV z).2.2.2.2.1)
    (hmarV := fun z => (hV z).2.2.2.2.2.1)
    (hcovF := fun s => (hF s).1) (hX₁F := fun s => (hF s).2.1)
    (hoptF := fun s => (hF s).2.2.1) (hΔF := fun s => (hF s).2.2.2.1)
    (hlogF := fun _ => hlog) (hyF := fun s => (hF s).2.2.2.2)
    (hBh0 := hBh0) (hBh := hBh) (hZν := fun z => (hV z).2.2.2.2.2.2)
    (hN := hN3) (hp := hp) (η := q / β) (hη0 := hη0) (hRσ := by norm_num) (hc := hc)
    (hεb := by
      have hnβ : ‖(((hatStepK (N₁ := N₁) k T.m₁ hk ν β p₁ T.δ).β : ℝ) : ℂ)‖ = β := by
        rw [Complex.norm_real]; exact Real.norm_of_nonneg hβ0.le
      rw [hnβ, mul_comm]
      exact le_of_eq rfl)
  exact ⟨val, 𝒴, Tt, hval, hloc, hcont, hI,
    mk_mem_physSΛEta (hatStepK (N₁ := N₁) k T.m₁ hk ν β p₁ T.δ) 1 ν T.t hη0.le hD,
    fun g hg => ⟨⟨_, hD, rfl⟩, sourceSlice_mem_restricted hβ1 hg hq⟩,
    fun Y Θ hΘ ψ hψ => hrayT Y Θ hΘ ψ fun p => by
      have hp1 := D.ray_margin_scaled hp
      have := hψ p
      have hpp : 0 < p₁ := hp
      nlinarith [norm_nonneg (ψ p), hr0]⟩

/-- **The ray hypothesis of `obsMarks_zeroClass_family_of_ray` holds.**  Slice `q = 1` of
`sourceDirectTerms_scale_fromTower_ray_full`. -/
theorem obsRay_hray_fromTower {κmin : ℝ} (T : StepTower κmin) :
    ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁], 3 ∣ N₁ → 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, 1 ≤ β →
      ∀ p₁ : ℝ, 0 < p₁ → StepScaleData T k hk N₁ ν β p₁ →
      ∀ S : StepSetting 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁), S = T.step k hk N₁ ν β p₁ →
      ∀ hp : 0 < S.p₁,
      ∃ (val : ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) → ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) →
          ℂ → (RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 ×
            (CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) → ℂ)
        (𝒴 : Finset (Set (CTorus 3 3 N₁ T.m₁ (k + 1))))
        (Tt : Set (CTorus 3 3 N₁ T.m₁ (k + 1)) → ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) →
          ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) → ℂ →
          (RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 ×
            (CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) → ℂ),
        (∀ x w σ Θ, val x w σ Θ =
          (-(S.β : ℂ)) * raySrc3 (hatFun S.G' S.a₁ S.ν T.t S.hG'
            ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
            (interactionOne S.hG S.hG' (le_refl (k + 1)) S.a₁ S.ν T.t)) taylorWeight x.1 w.1 σ Θ.1 +
          (S.β : ℂ) * (∑ s : CTorus 3 3 N₁ T.m₁ (k + 1) × Fin 2, Θ.2 s.1 s.2 *
            dirTermSrc (hatFun S.G' S.a₁ S.ν T.t S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
              (onXi S.G' S.a₁ S.ν T.t
                (fun D ψ' => svec (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁))
                  (flFieldOne S.G' (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) T.BG₂ T.κ S.a₁ S.ν D ψ')
                    s.1 s.2)))
              (fun _ => (1 : ℂ)) x.2 w.2 σ Θ.1)) ∧
        DiagCont (fun ψ : S.U × Fin 2 → ℂ => (ψ, ψ))
          (physXW S (lvCpsi T.κ T.t (β * 3 ^ k)) 2 2 (lvR T.κ T.t (β * 3 ^ k) p₁))
          (physSΛEta S S.a₁ S.ν T.t (1 / S.β)) 2 𝒴 Tt ∧
        (∀ Θ ∈ physSΛEta S S.a₁ S.ν T.t (1 / S.β),
          ∃ I : DirectTerms S 1 hp (fun ψ => (ψ, ψ)) p₁ 2
              (S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
                (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (1 / S.β)) (2 * T.κdec - 1) Θ
              (physSΛEta S S.a₁ S.ν T.t (1 / S.β))
              (physXW S (lvCpsi T.κ T.t (β * 3 ^ k)) 2 2 (lvR T.κ T.t (β * 3 ^ k) p₁)) val
              (physAgΘ S) (AgFDirPair S),
            I.𝒴 = 𝒴 ∧ I.T = Tt) ∧
        (rawOf S.D', (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) ∈
          physSΛEta S S.a₁ S.ν T.t (1 / S.β) ∧
        (∀ g : Fld 3 3 N₁ T.m₁ (k + 1) 2, ∑ x, ∑ i, ‖g x i‖ < 1 →
          (rawOf S.D', fun y i => g y i / (S.β : ℂ)) ∈ physSΛEta S S.a₁ S.ν T.t (1 / S.β)) ∧
        (∀ Y ∈ 𝒴, ∀ Θ ∈ physSΛEta S S.a₁ S.ν T.t (1 / S.β),
          ∀ ψ ∈ hatDisk S.U 2 p₁,
            DifferentiableOn ℂ (fun z : ℂ => Tt Y (z • ψ, z • ψ) (z • ψ, z • ψ) 1 Θ)
              (ball (0 : ℂ) (3 / 2))) := by
  classical
  intro k hk N₁ _ h3N hN ν hνpos hν β hβ1 p₁ hp0 D S hS hp
  obtain ⟨val, 𝒴, Tt, hval, -, hcont, hI, hm0, hmg, hr⟩ :=
    sourceDirectTerms_scale_fromTower_ray_full T k hk N₁ h3N hN ν hνpos hν β hβ1 p₁ 1 one_pos
      le_rfl D S hS hp
  exact ⟨val, 𝒴, Tt, hval, hcont, hI, hm0, hmg, fun Y _ Θ hΘ ψ hψ => hr Y Θ hΘ ψ hψ⟩


open Classical in
/-- **The observable marks record of the zero-class step at the shared tower** (OBSPHYS §4), with
no hypothesis beyond the tower: `obsMarks_zeroClass_family_of_ray` with `hray` supplied by
`obsRay_hray_fromTower`. -/
theorem obsMarks_zeroClass_family {κmin : ℝ} (T : StepTower κmin)
    {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ) {CR s : ℝ}
    (hCR : 0 < CR) (hs0 : 0 < s) (hs : s < 1 / 2) :
  ∃ β₀ C₁ C₂ : ℝ, 2 ≤ β₀ ∧ 0 ≤ C₁ ∧ 0 ≤ C₂ ∧
  ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁], 3 ∣ N₁ → 5 < N₁ →
  ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 →
  ∀ β : ℝ, β₀ ≤ β → ∀ (p₁ : ℝ) (hp : 0 < p₁),
  p₁ ≤ pLog A₁ p (β * 3 ^ k) →
  StepScaleData T k hk N₁ ν β p₁ →
  ∀ g : Fld 3 3 N₁ T.m₁ (k + 1) 2,
    g ∈ l1Ball 3 3 N₁ T.m₁ (k + 1) 2 →
  ∀ (y : CTorus 3 3 N₁ T.m₁ (k + 1)) (i : Fin 2),
    let S := T.step k hk N₁ ν β p₁;
    let C := zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁);
    ∃ I : ObsMarks S.nuFl (S.blockSplit 1 hp)
      (fun r x => S.WoneC C 1 x + S.WtwoC C g r x)
      (fun r x => deriv (fun z => McompAtC C.m₀ C.Tm S.a S.ν
        (Nat.le_succ k) (S.dataUC (S.psiAtC z x)) g y i) r)
      (rootCube (m₀ := 1) (blockIndex y)),
      I.Kc = 4 * K0 3 3 T.κ0 + 2 ∧ I.κ0 = T.κ0 ∧
      I.κH = 2 * T.κdec - 1 ∧ I.κ' = T.κ' ∧
      I.κh = 2 * T.κdec ∧ I.Rσ = obsRg CR s p (β * 3 ^ k) ∧
      I.B1 ≤ C₁ * obsW p (β * 3 ^ k) ^ 4 *
        (β * 3 ^ k) ^ (-(1 / 2 : ℝ) - s) ∧
      I.B2 ≤ C₂ * obsW p (β * 3 ^ k) ^ 2 / (β * 3 ^ k) :=
  obsMarks_zeroClass_family_of_ray T hA p hCR hs0 hs (obsRay_hray_fromTower T)

open Classical in
/-- **Non-vacuity of `obsMarks_zeroClass_family`.**  At `k = 1`, `N₁ = 18`, `ν = 1/81`, `p₁ = 1`
(`A₁ = 1`, `p = 0`), `C_R = 1`, `s = 1/4`, there is a scale with a `StepScaleData` record at which
the family gives an `ObsMarks` record for the source `g = 0`, at every site and spin. -/
theorem obsMarks_zeroClass_instance {κmin : ℝ} (T : StepTower κmin) :
    ∃ β : ℝ, 2 ≤ β ∧ ∃ _ : StepScaleData T 1 le_rfl 18 (1 / 81) β 1,
      ∀ (hp : 0 < (T.step 1 le_rfl 18 (1 / 81) β 1).p₁)
        (y : CTorus 3 3 18 T.m₁ (1 + 1)) (i : Fin 2),
        let S := T.step 1 le_rfl 18 (1 / 81) β 1;
        let C := zeroClass 3 3 18 T.m₁ 1 2 (rhoSep T.m₁);
        Nonempty (ObsMarks S.nuFl (S.blockSplit 1 hp)
          (fun r x => S.WoneC C 1 x + S.WtwoC C (0 : Fld 3 3 18 T.m₁ (1 + 1) 2) r x)
          (fun r x => deriv (fun z => McompAtC C.m₀ C.Tm S.a S.ν
            (Nat.le_succ 1) (S.dataUC (S.psiAtC z x)) (0 : Fld 3 3 18 T.m₁ (1 + 1) 2) y i) r)
          (rootCube (m₀ := 1) (blockIndex y)) ) := by
  obtain ⟨β₀, C₁, C₂, hβ₀, -, -, hfam⟩ := obsMarks_zeroClass_family T (A₁ := 1) one_pos 0
    (CR := 1) (s := 1 / 4) one_pos (by norm_num) (by norm_num)
  obtain ⟨βray, h2, hsc⟩ := T.scale (A₁ := 1) one_pos 0
  have hβ : 2 ≤ max β₀ βray := le_max_of_le_left hβ₀
  have hp1 : (1 : ℝ) ≤ pLog 1 0 (max β₀ βray * 3 ^ 1) := by simp [pLog]
  obtain ⟨D⟩ := hsc 1 le_rfl 18 (by norm_num) (by norm_num) (1 / 81) (by norm_num) (by norm_num)
    (max β₀ βray) (le_max_right _ _) 1 one_pos hp1
  refine ⟨max β₀ βray, hβ, D, fun hp y i => ?_⟩
  obtain ⟨I, -⟩ := hfam 1 le_rfl 18 (by norm_num) (by norm_num) (1 / 81) (by norm_num)
    (by norm_num) (max β₀ βray) (le_max_left _ _) 1 hp hp1 D 0
    (by simp [l1Ball]) y i
  exact ⟨I⟩

end Balaban.Inhabited
