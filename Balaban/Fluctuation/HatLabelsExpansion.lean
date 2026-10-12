/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.HatLabelsTerms
public import Balaban.Fluctuation.InteractionHatAssemble
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The label activities of `interaction_expansion_hat`

The conclusion of `Balaban.Localization.interaction_expansion_hat` is a `LocInt` over the ray pairs
`xw` with `(xw.1.1, xw.2.1)` and `(xw.1.2, xw.2.2)` in `HatRaysO`, localized under
`AgHatF` in both hat variables.  Along the diagonal `x₀ = w = (ψ̂, ψ̂)` with `|ψ̂| ≤ ρ` these rays are
admissible (`hatRaysO_pair`), and `hatTerms_of_expansion` packages the expansion as `HatTerms`;
`labelAct_of_hatExpansion` adds the construction of the labels and activities and the numerics of
Theorem 3.4 for small `ε_U`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open MeasureTheory Balaban Balaban.Localization Balaban.Multiscale Balaban.Polymer

section Expansion

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) (m₀ : ℕ)

/-- **The diagonal pairs are admissible rays.** -/
theorem hatRaysO_pair {ψ : S.U × Fin N → ℂ} {ρ Rσ R₁ r cψ : ℝ} (hψ : ψ ∈ hatDisk S.U N ρ)
    (hRσ : 0 ≤ Rσ) (hR₁ : 0 ≤ R₁) (hr : 0 ≤ r) (hc : (Rσ * R₁ + r) * ρ < cψ) :
    (ψ, ψ) ∈ HatRaysO (N := N) S.G' cψ R₁ Rσ r := by
  intro σ hσ t ht τ hτ p
  have h0 : 0 ≤ ρ := (norm_nonneg _).trans (hψ p)
  have h1 : ‖σ * t‖ ≤ Rσ * R₁ := by
    rw [norm_mul]; exact mul_le_mul hσ.le ht.le (norm_nonneg _) hRσ
  have h2 : ‖σ * t + τ‖ ≤ Rσ * R₁ + r := (norm_add_le _ _).trans (add_le_add h1 hτ)
  calc ‖((σ * t) • ψ + τ • ψ) p‖ = ‖(σ * t + τ) * ψ p‖ := by
        simp [add_mul]
    _ ≤ (Rσ * R₁ + r) * ρ := by
        rw [norm_mul]
        exact mul_le_mul h2 (hψ p) (norm_nonneg _) (by positivity)
    _ < cψ := hc

theorem ag_pair {Y : Set (CTorus d L N₁ m₁ (k + 1))} {ψ ψ' : S.U × Fin N → ℂ}
    (h : AgHatF S.G' S.hG' Y ψ ψ') :
    AgHatF S.G' S.hG' Y (ψ, ψ).1 (ψ', ψ').1 ∧ AgHatF S.G' S.hG' Y (ψ, ψ).2 (ψ', ψ').2 := ⟨h, h⟩

open Classical in
/-- **The conclusion of `interaction_expansion_hat` as `HatTerms`**: the diagonal embedding
`ψ̂ ↦ (ψ̂, ψ̂)`, the rays of `HatRaysO` and the agreement `AgHatF` in both hat variables. -/
def hatTerms_of_expansion {Λ : Type} [NormedAddCommGroup Λ] [NormedSpace ℂ Λ]
    {ρ Rσ R₁ r cψ εU a : ℝ} (hRσ : 0 ≤ Rσ) (hR₁ : 0 ≤ R₁) (hr : 0 ≤ r)
    (hc : (Rσ * R₁ + r) * ρ < cψ) {Θ₀ : Λ} {SΛ : Set Λ}
    {val : (S.U × Fin N → ℂ) × (S.U × Fin N → ℂ) → (S.U × Fin N → ℂ) × (S.U × Fin N → ℂ) →
      ℂ → Λ → ℂ}
    {AgΘ : Set (CTorus d L N₁ m₁ (k + 1)) → Λ → Λ → Prop}
    (𝒴 : Finset (Set (CTorus d L N₁ m₁ (k + 1))))
    (T : Set (CTorus d L N₁ m₁ (k + 1)) → (S.U × Fin N → ℂ) × (S.U × Fin N → ℂ) →
      (S.U × Fin N → ℂ) × (S.U × Fin N → ℂ) → ℂ → Λ → ℂ)
    (b : Set (CTorus d L N₁ m₁ (k + 1)) → ℝ)
    (loc : LocInt SΛ {xw : ((S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)) × ((S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)) |
        (xw.1.1, xw.2.1) ∈ HatRaysO (N := N) S.G' cψ R₁ Rσ r ∧
        (xw.1.2, xw.2.2) ∈ HatRaysO (N := N) S.G' cψ R₁ Rσ r} Rσ 𝒴 T val b AgΘ
      (fun Y a a' => AgHatF S.G' S.hG' Y a.1 a'.1 ∧ AgHatF S.G' S.hG' Y a.2 a'.2))
    (dom : ∀ Y ∈ 𝒴, IsDj m₀ (k + 1) Y)
    (bd : ∀ Y ∈ 𝒴, b Y ≤ εU * Real.exp (-a * treeLenCovOne m₀ (k + 1) Y))
    (mem : Θ₀ ∈ SΛ) (agΘ : ∀ Y, AgΘ Y Θ₀ Θ₀)
    (meas : ∀ Y ∈ 𝒴, ∀ σ : ℂ, ‖σ‖ < Rσ → Measurable (fun ψ : hatDisk S.U N ρ =>
      T Y (ψ.1, ψ.1) (ψ.1, ψ.1) σ Θ₀)) :
    HatTerms S m₀ (fun ψ => (ψ, ψ)) ρ Rσ εU a Θ₀ SΛ
      {xw : ((S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)) × ((S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)) |
        (xw.1.1, xw.2.1) ∈ HatRaysO (N := N) S.G' cψ R₁ Rσ r ∧
        (xw.1.2, xw.2.2) ∈ HatRaysO (N := N) S.G' cψ R₁ Rσ r} val AgΘ
      (fun Y a a' => AgHatF S.G' S.hG' Y a.1 a'.1 ∧ AgHatF S.G' S.hG' Y a.2 a'.2) where
  𝒴 := 𝒴
  T := T
  b := b
  loc := loc
  dom := dom
  bd := bd
  mem := mem
  agΘ := agΘ
  xw := fun _ hψ => ⟨hatRaysO_pair S hψ hRσ hR₁ hr hc, hatRaysO_pair S hψ hRσ hR₁ hr hc⟩
  ag := fun _ _ _ h => ag_pair S h
  meas := meas

/-- The smallness threshold for `ε_U`: `ε_H ≤ 1 / (8 K_c³ c₁ e^{(κ_H - 2κ₀) c_G + c₁ + κ' c_G})`
(the condition `hε` of `InterpMarks`) holds for `ε_U ≤ hatEpsMax`. -/
noncomputable def hatEpsMax (d L : ℕ) (Rσ a κ0 κ' Kc : ℝ) : ℝ :=
  1 / (Rσ * Real.exp (c1 d L + a * hatB d L / hatA d L) *
    (8 * Kc ^ 3 * c1 d L * Real.exp ((hatKappaH d L a - 2 * κ0) * cG d L + c1 d L + κ' * cG d L)))

/-- **The numerics of Theorem 3.4 for small `ε_U`.** -/
theorem hat_numerics {Rσ εU a κ0 κ' Kc : ℝ} (hRσ : 0 < Rσ) (hεpos : 0 < εU) (hKc : 1 ≤ Kc)
    (hκa : (κ' + 3 * κ0 + c1 d L + 3 / 2 + c1 d L) * hatA d L ≤ a)
    (hεU : εU ≤ hatEpsMax d L Rσ a κ0 κ' Kc) :
    0 < hatEpsH d L Rσ εU a ∧ κ' + 3 * κ0 + c1 d L + 3 / 2 ≤ hatKappaH d L a ∧
      hatEpsH d L Rσ εU a ≤ 1 / (8 * Kc ^ 3 * c1 d L *
        Real.exp ((hatKappaH d L a - 2 * κ0) * cG d L + c1 d L + κ' * cG d L)) := by
  have hA := hatA_pos d L
  have hc1 := one_le_c1 d L
  refine ⟨by unfold hatEpsH; positivity, ?_, ?_⟩
  · unfold hatKappaH
    have : κ' + 3 * κ0 + c1 d L + 3 / 2 + c1 d L ≤ a / hatA d L := (le_div_iff₀ hA).2 hκa
    linarith
  · have hE : 0 < Real.exp (c1 d L + a * hatB d L / hatA d L) := Real.exp_pos _
    have hD : 0 < 8 * Kc ^ 3 * c1 d L *
        Real.exp ((hatKappaH d L a - 2 * κ0) * cG d L + c1 d L + κ' * cG d L) := by
      have : 0 < Kc := by linarith
      positivity
    unfold hatEpsH
    calc Rσ * εU * Real.exp (c1 d L + a * hatB d L / hatA d L)
        = (Rσ * Real.exp (c1 d L + a * hatB d L / hatA d L)) * εU := by ring
      _ ≤ (Rσ * Real.exp (c1 d L + a * hatB d L / hatA d L)) * hatEpsMax d L Rσ a κ0 κ' Kc :=
          mul_le_mul_of_nonneg_left hεU (by positivity)
      _ = _ := by
          unfold hatEpsMax
          field_simp

open Classical in
/-- **The label activities of the ψ̂-local expansion** (the constructor `labelAct_of_hatExpansion`).
From the conclusion of `interaction_expansion_hat` (the `LocInt` `loc` over the rays of
`HatRaysO`, localized under `AgHatF`, with the domains of `𝒟_{k+1}` and the terms measurable in
`ψ̂`), a block structure of `ν_{p₁}` with `p₁ ≤ ρ`, and the numerical hypotheses
(`κ₀ ≥ a_ent + 1`, `K_c ≥ K₀ + 1`, `a` large and `ε_U` small), there are `CubeLabels` and, for each
`u`, a `LabelAct` `A u` on the block variables of `ν_{p₁}`: bounded by `ε_H e^{-κ_H 𝗱}`,
holomorphic in `u` on `|u| < R_σ`, with the sum over labels equal to `val` at the hat variable,
`ν_{p₁}`-almost surely, and with the numerics of Theorem 3.4. -/
theorem labelAct_of_hatExpansion {Λ : Type} [NormedAddCommGroup Λ] [NormedSpace ℂ Λ]
    {ρ Rσ R₁ r cψ εU a : ℝ} (hRσ : 0 < Rσ) (hR₁ : 0 ≤ R₁) (hr : 0 ≤ r)
    (hc : (Rσ * R₁ + r) * ρ < cψ) {Θ₀ : Λ} {SΛ : Set Λ}
    {val : (S.U × Fin N → ℂ) × (S.U × Fin N → ℂ) → (S.U × Fin N → ℂ) × (S.U × Fin N → ℂ) →
      ℂ → Λ → ℂ}
    {AgΘ : Set (CTorus d L N₁ m₁ (k + 1)) → Λ → Λ → Prop}
    (𝒴 : Finset (Set (CTorus d L N₁ m₁ (k + 1))))
    (T : Set (CTorus d L N₁ m₁ (k + 1)) → (S.U × Fin N → ℂ) × (S.U × Fin N → ℂ) →
      (S.U × Fin N → ℂ) × (S.U × Fin N → ℂ) → ℂ → Λ → ℂ)
    (b : Set (CTorus d L N₁ m₁ (k + 1)) → ℝ)
    (loc : LocInt SΛ {xw : ((S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)) × ((S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)) |
        (xw.1.1, xw.2.1) ∈ HatRaysO (N := N) S.G' cψ R₁ Rσ r ∧
        (xw.1.2, xw.2.2) ∈ HatRaysO (N := N) S.G' cψ R₁ Rσ r} Rσ 𝒴 T val b AgΘ
      (fun Y a a' => AgHatF S.G' S.hG' Y a.1 a'.1 ∧ AgHatF S.G' S.hG' Y a.2 a'.2))
    (dom : ∀ Y ∈ 𝒴, IsDj m₀ (k + 1) Y)
    (bd : ∀ Y ∈ 𝒴, b Y ≤ εU * Real.exp (-a * treeLenCovOne m₀ (k + 1) Y))
    (mem : Θ₀ ∈ SΛ) (agΘ : ∀ Y, AgΘ Y Θ₀ Θ₀)
    (meas : ∀ Y ∈ 𝒴, ∀ σ : ℂ, ‖σ‖ < Rσ → Measurable (fun ψ : hatDisk S.U N ρ =>
      T Y (ψ.1, ψ.1) (ψ.1, ψ.1) σ Θ₀))
    (hN : L ^ m₀ ∣ N₁) (hL : 2 ≤ L) (hp : 0 < S.p₁) (hpρ : S.p₁ ≤ ρ)
    (hεpos : 0 < εU) {κ0 κ' Kc : ℝ} (hκ0 : aEnt d L + 1 ≤ κ0) (hKc : K0 d L κ0 + 1 ≤ Kc)
    (hκ' : 0 ≤ κ') (hκa : (κ' + 3 * κ0 + c1 d L + 3 / 2 + c1 d L) * hatA d L ≤ a)
    (hεU : εU ≤ hatEpsMax d L Rσ a κ0 κ' Kc) :
    ∃ (Lb : Type) (_ : Fintype Lb)
      (Lab : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
        Set.univ Lb)
      (A : ℂ → LabelAct Lab (S.blockSplit m₀ hp).Ωb (hatEpsH d L Rσ εU a) (hatKappaH d L a) κ0 Kc),
      (∀ y Φ, DifferentiableOn ℂ (fun u => (A u).H y Φ) (Metric.ball 0 Rσ)) ∧
      (∀ u : ℂ, ‖u‖ < Rσ → ∀ᵐ x ∂S.nuFl, ∑ y, (A u).H y ((S.blockSplit m₀ hp).restr x) =
        val (S.hatC x, S.hatC x) (S.hatC x, S.hatC x) u Θ₀) ∧
      (0 < hatEpsH d L Rσ εU a ∧ κ' + 3 * κ0 + c1 d L + 3 / 2 ≤ hatKappaH d L a ∧
        hatEpsH d L Rσ εU a ≤ 1 / (8 * Kc ^ 3 * c1 d L *
          Real.exp ((hatKappaH d L a - 2 * κ0) * cG d L + c1 d L + κ' * cG d L))) := by
  have hρ : 0 < ρ := lt_of_lt_of_le hp hpρ
  have hKc1 : 1 ≤ Kc := by
    have : 0 ≤ K0 d L κ0 := by
      unfold K0
      have : Real.exp (-1) < 1 := by rw [Real.exp_lt_one_iff]; norm_num
      exact div_nonneg (Real.exp_pos _).le (by linarith)
    linarith
  have hA := hatA_pos d L
  have hc1 := one_le_c1 d L
  have ha : 0 ≤ a := by
    refine le_trans ?_ hκa
    have h1 : 0 ≤ aEnt d L := aEnt_nonneg d L
    exact mul_nonneg (by linarith) hA.le
  obtain ⟨Lb, hfin, Lab, A, hol, hsum⟩ := labelAct_of_hatTerms S m₀
    (hatTerms_of_expansion S m₀ hRσ.le hR₁ hr hc 𝒴 T b loc dom bd mem agΘ meas)
    hN hL hp hρ hRσ.le hεpos.le ha (κ0 := κ0) (Kc := Kc) hκ0 (by linarith)
  refine ⟨Lb, hfin, Lab, A, hol, fun u hu => ?_, hat_numerics hRσ hεpos hKc1 hκa hεU⟩
  filter_upwards [S.ae_hatOf_restr m₀ hρ hp hpρ] with x hx
  rw [hsum u hu, hx]

end Expansion

section Domains

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
  {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {m₀ : ℕ}
  {ι : Type*} [DecidableEq ι] [Fintype ι] (c : ι → ℕ × CTorus d L N₁ m₁ K)
  {j : ℕ} {X 𝒦X : Set (CTorus d L N₁ m₁ K)}

/-- **The labels of the expansion are domains of `𝒟_{lev}`** (the `dom` clause of `HatTerms` for
the domains `polymerDomains` of the localization expansion): `IsDj` from `isDj_of_isMultiDom`. -/
theorem isDj_of_polymerDomains {lev : ℕ} (hG : IsLevel G lev) (hS : CovSetup G m₀ j X 𝒦X)
    (hd : 3 ≤ d) (hc : ∀ i, c i ∈ cubeIdx G)
    (hopt : ∃ (W₀ : Finset (CTorus d L N₁ m₁ K))
      (E₀ : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K)),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X) ∧ MeetsOne m₀ j 𝒦X W₀ ∧
        bondCost (scaleW L m₀ m₁ j) E₀ = treeLenCovOne m₀ j X)
    {Y : Set (CTorus d L N₁ m₁ K)} (hY : Y ∈ polymerDomains c G m₀ (X1 G m₀ j 𝒦X)) :
    IsDj m₀ lev Y :=
  isDj_of_isMultiDom hG (polymerDomain_isMultiDom c hS hd hc hopt hY)

end Domains

end Balaban.Fluctuation
