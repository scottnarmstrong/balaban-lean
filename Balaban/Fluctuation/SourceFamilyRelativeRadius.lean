/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.SourceRadius
public import Balaban.Fluctuation.SourceDirectTermsScale
public import Balaban.Inhabited.UniformChartRelative
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The relative source chart at a general source radius

The relative chart of `SourceFamilyRelative.lean` and `UniformChartRelative.lean` is built on the
carriers `physV`, `physVq` of the unit ball of sources.  Here the same statements are proved on the
carriers `physVRho`, `physVqRho` of `SourceRadius.lean` (sources with `∑ |g| < ρ`), with
`q ≤ ρ` and `max 1 ρ ≤ β`:

* `hatStepK_physVRho`: the step datum with every source of the ball of radius `ρ` lies in the open
  set `physVRho` (the case `ρ = 1` is `hatStepK_physV_of_rho`);
* `directTermsFamilyOn_scaled_rho`: the relative family over `physVqRho … ρ q`
  (`directTermsFamilyOn_scaled_of_rho` is the case `ρ = 1`);
* `sourceFamilyRelative_scale_rho`: the statement of `sourceFamilyRelative_scale` at radius `ρ`
  (`sourceFamilyRelative_scale_of_rho` is the case `ρ = 1`).
-/

@[expose] public section

namespace Balaban.Fluctuation

open MeasureTheory Balaban Balaban.Localization Balaban.Multiscale Balaban.Polymer
  Balaban.Background Balaban.SmallField Balaban.SmallField.Def6 Balaban.Analysis Finset Matrix Set
  Metric

section Generic

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ)
variable (m₀ : ℕ) {Λ F' : Type} {hp : 0 < S.p₁} {emb : (S.U × Fin N → ℂ) → F'}
  {ρD Rσ εU a a₁ ν eps : ℝ}
  {Θ₀ : RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)}
  {XW : Set (F' × F')} {val : F' → F' → ℂ →
    RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ}
  {AgF : Set (CTorus d L N₁ m₁ (k + 1)) → F' → F' → Prop}

/-- **The family over the relative chart of radius `ρ` with the scaled source.**  From a
`DirectTerms` instance on the slice `physSΛEta … (q/β)` whose diagonal terms are continuous on the
slice, the relative family over `physVqRho … ρ q` with the map `(q, g) ↦ (q, g/β)`, for `q ≤ ρ`
and `max 1 ρ ≤ β`. -/
theorem directTermsFamilyOn_scaled_rho {ρ β q : ℝ}
    {I : DirectTerms S m₀ hp emb ρD Rσ εU a Θ₀ (physSΛEta S a₁ ν eps (q / β)) XW val (physAgΘ S)
      AgF}
    (hcont : DiagCont emb XW (physSΛEta S a₁ ν eps (q / β)) Rσ I.𝒴 I.T)
    (H : BgHyp d L (k + 1) ϱ (compWeight L a₁) ν) (hβ : max 1 ρ ≤ β) (hq : q ≤ ρ) :
    DirectTermsFamilyOn S m₀ (physInclScaled N S ((1 / β : ℝ) : ℂ)) I
      (physVqRho S a₁ ν eps ρ q) where
  isOpen := isOpen_physVqRho S a₁ ν eps ρ q H
  sub := physInclScaled_image_subset_rho S a₁ ν eps hβ hq
  agΘ := fun _ _ Y => physAgΘ_refl S Y _
  cont := hcont.mono_set (physInclScaled_image_subset_rho S a₁ ν eps hβ hq)

/-- The landed `directTermsFamilyOn_scaled` is the case `ρ = 1`. -/
theorem directTermsFamilyOn_scaled_of_rho {β q : ℝ}
    {I : DirectTerms S m₀ hp emb ρD Rσ εU a Θ₀ (physSΛEta S a₁ ν eps (q / β)) XW val (physAgΘ S)
      AgF}
    (hcont : DiagCont emb XW (physSΛEta S a₁ ν eps (q / β)) Rσ I.𝒴 I.T)
    (H : BgHyp d L (k + 1) ϱ (compWeight L a₁) ν) (hβ : 1 ≤ β) (hq : q ≤ 1) :
    DirectTermsFamilyOn S m₀ (physInclScaled N S ((1 / β : ℝ) : ℂ)) I
      (physVq S a₁ ν eps q) :=
  directTermsFamilyOn_scaled_rho S m₀ (ρ := 1) hcont H (by rwa [max_self]) hq

end Generic

end Balaban.Fluctuation

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep Metric

section Chart

variable {N₁ : ℕ} [NeZero N₁]

/-- **A relatively open neighbourhood of the physical point at radius `ρ`.**  The set `physVRho` is
open; it contains the step datum `rawOf S.D'` with every source of the ball `∑ |g| < ρ`; and every
point of it is the raw datum of a datum satisfying `XiCData`. -/
theorem hatStepK_physVRho (k m₁ : ℕ) (hk : 1 ≤ k) {ν : ℝ} (hν0 : 0 ≤ ν)
    (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) (β p₁ δ : ℝ) {t : ℝ} (ht0 : 0 < t) (ρ : ℝ) :
    IsOpen (physVRho (N := 2) (hatStepK (N₁ := N₁) k m₁ hk ν β p₁ δ) 1 ν t ρ) ∧
    (∀ g ∈ l1BallRho 3 3 N₁ m₁ (k + 1) 2 ρ,
      (⟨rawOf (hatStepK (N₁ := N₁) k m₁ hk ν β p₁ δ).D',
          rawOf_mem_rawSub _⟩, g) ∈
        physVRho (N := 2) (hatStepK (N₁ := N₁) k m₁ hk ν β p₁ δ) 1 ν t ρ) ∧
    (∀ e ∈ physVRho (N := 2) (hatStepK (N₁ := N₁) k m₁ hk ν β p₁ δ) 1 ν t ρ,
      ∃ D, XiCData (hatStepK (N₁ := N₁) k m₁ hk ν β p₁ δ).G' (compWeight 3 1) ν (k + 1) 1 t D ∧
        rawOf D = (e.1 : RawData 3 3 (N₁ * 3 ^ m₁) (k + 1) 2)) := by
  refine ⟨isOpen_physVRho _ _ _ _ _ (bgHyp_lv (k := k) (ν := ν) m₁ hν0 hν), ?_, ?_⟩
  · intro g hg
    exact ⟨hatStepK_rawOf_mem_xiCRaw k m₁ hk hν0 hν β p₁ δ ht0, hg⟩
  · intro e he
    obtain ⟨D, hD, h⟩ := he.1
    exact ⟨D, hD, h.symm⟩

/-- The landed `hatStepK_physV` is the case `ρ = 1`. -/
theorem hatStepK_physV_of_rho (k m₁ : ℕ) (hk : 1 ≤ k) {ν : ℝ} (hν0 : 0 ≤ ν)
    (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) (β p₁ δ : ℝ) {t : ℝ} (ht0 : 0 < t) :
    IsOpen (physV (N := 2) (hatStepK (N₁ := N₁) k m₁ hk ν β p₁ δ) 1 ν t) ∧
    (∀ g ∈ l1Ball 3 3 N₁ m₁ (k + 1) 2,
      (⟨rawOf (hatStepK (N₁ := N₁) k m₁ hk ν β p₁ δ).D',
          rawOf_mem_rawSub _⟩, g) ∈
        physV (N := 2) (hatStepK (N₁ := N₁) k m₁ hk ν β p₁ δ) 1 ν t) ∧
    (∀ e ∈ physV (N := 2) (hatStepK (N₁ := N₁) k m₁ hk ν β p₁ δ) 1 ν t,
      ∃ D, XiCData (hatStepK (N₁ := N₁) k m₁ hk ν β p₁ δ).G' (compWeight 3 1) ν (k + 1) 1 t D ∧
        rawOf D = (e.1 : RawData 3 3 (N₁ * 3 ^ m₁) (k + 1) 2)) :=
  hatStepK_physVRho k m₁ hk hν0 hν β p₁ δ ht0 1

end Chart

section Scale

/-- **The source direct terms as a family over the relative chart of radius `ρ`, at every scale.**
The statement of `sourceFamilyRelative_scale` with the carrier `physVqRho … ρ q`, for `0 < q ≤ ρ`
and `max 1 ρ ≤ β`; the constants `m₁, t, δ, β₀, BG, BG₂, κ` do not depend on `ρ`. -/
theorem sourceFamilyRelative_scale_rho {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ)
    {κ0 κdec : ℝ} (hκ0def : κ0 = aEnt 3 3 + 1) (hκdecdef : κdec = 100 * (κ0 + c1 3 3 + 10)) :
    ∃ (m₁ : ℕ) (t δ β₀ BG BG₂ κ : ℝ), 2 ≤ β₀ ∧ 0 < t ∧ 0 < δ ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (h3N : 3 ∣ N₁), 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β → ∀ ρ : ℝ, max 1 ρ ≤ β →
      ∀ p₁ : ℝ, ∀ hp0 : 0 < p₁, p₁ ≤ pLog A₁ p (β * 3 ^ k) → ∀ q : ℝ, 0 < q → q ≤ ρ →
      ∀ S : StepSetting 3 3 N₁ m₁ k 2 (rhoSep m₁),
        S = hatStepK (N₁ := N₁) k m₁ hk ν β p₁ δ → ∀ hp : 0 < S.p₁,
        ∃ (val : ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) → ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) →
            ℂ → (RawData 3 3 (N₁ * 3 ^ m₁) (k + 1) 2 × (CTorus 3 3 N₁ m₁ (k + 1) → Fin 2 → ℂ)) → ℂ)
          (𝒴 : Finset (Set (CTorus 3 3 N₁ m₁ (k + 1))))
          (T : Set (CTorus 3 3 N₁ m₁ (k + 1)) → ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) →
            ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) → ℂ →
            (RawData 3 3 (N₁ * 3 ^ m₁) (k + 1) 2 × (CTorus 3 3 N₁ m₁ (k + 1) → Fin 2 → ℂ)) → ℂ)
          (I : DirectTerms S 1 hp (fun ψ => (ψ, ψ)) p₁ 2
                (S.β * prop33EpsEtaScaled 3 3 2 m₁ k 1 S.a₁ BG BG₂ κ t
                  (lvR κ t (β * 3 ^ k) p₁) 0 0 (q / S.β)) (2 * κdec - 1)
                (rawOf S.D', (0 : CTorus 3 3 N₁ m₁ (k + 1) → Fin 2 → ℂ))
                (physSΛEta S S.a₁ S.ν t (q / S.β))
                (physXW S (lvCpsi κ t (β * 3 ^ k)) 2 2 (lvR κ t (β * 3 ^ k) p₁)) val (physAgΘ S)
                (AgFDirPair S)),
          I.𝒴 = 𝒴 ∧ I.T = T ∧
          ∃ hF : DirectTermsFamilyOn S 1 (physInclScaled 2 S (((1 / S.β : ℝ)) : ℂ)) I
              (physVqRho S 1 ν t ρ q),
            (∀ g : Fld 3 3 N₁ m₁ (k + 1) 2, ∑ x, ∑ i, ‖g x i‖ < q →
              ∃ hg : (⟨rawOf S.D', rawOf_mem_rawSub _⟩, g) ∈ physVqRho S 1 ν t ρ q,
                physInclScaled 2 S (((1 / S.β : ℝ)) : ℂ) (⟨rawOf S.D', rawOf_mem_rawSub _⟩, g) =
                  (rawOf S.D', fun y i => g y i / (S.β : ℂ)) ∧
                (I.atThetaOn S 1 _ hF hg).𝒴 = 𝒴 ∧ (I.atThetaOn S 1 _ hF hg).T = T) ∧
            ∀ (hεU : 0 ≤ S.β * prop33EpsEtaScaled 3 3 2 m₁ k 1 S.a₁ BG BG₂ κ t
                  (lvR κ t (β * 3 ^ k) p₁) 0 0 (q / S.β))
              {Kc : ℝ} (hKc : K0 3 3 κ0 ≤ Kc),
              (∀ (y : {Y // Y ∈ I.𝒴}) (Φ : ∀ b, (S.blockSplit 1 hp).Ωb b),
                AnalyticOnNhd ℂ (fun r : physParam 2 S × ℂ =>
                  (labelActFamilyOn S 1 (physInclScaled 2 S (((1 / S.β : ℝ)) : ℂ)) I hF
                    (show 3 ^ 1 ∣ N₁ by simpa using h3N) hp0 (by norm_num) hεU
                    hκ0def.ge hKc r.1 r.2).H y Φ)
                  (physVqRho S 1 ν t ρ q ×ˢ ball (0 : ℂ) 2)) ∧
              (∀ e (he : e ∈ physVqRho S 1 ν t ρ q) (u : ℂ),
                labelActFamilyOn S 1 (physInclScaled 2 S (((1 / S.β : ℝ)) : ℂ)) I hF
                    (show 3 ^ 1 ∣ N₁ by simpa using h3N) hp0 (by norm_num) hεU
                    hκ0def.ge hKc e u =
                  dtAct S 1 (I.atThetaOn S 1 _ hF he)
                    (show 3 ^ 1 ∣ N₁ by simpa using h3N) hp0 (by norm_num) hεU
                    hκ0def.ge hKc u) ∧
              (∀ e ∈ physVqRho S 1 ν t ρ q, ∀ u : ℂ, ‖u‖ < 2 →
                ∀ (y : {Y // Y ∈ I.𝒴}) (Φ : ∀ b, (S.blockSplit 1 hp).Ωb b),
                (labelActFamilyOn S 1 (physInclScaled 2 S (((1 / S.β : ℝ)) : ℂ)) I hF
                    (show 3 ^ 1 ∣ N₁ by simpa using h3N) hp0 (by norm_num) hεU
                    hκ0def.ge hKc e u).H y Φ =
                  I.T y.1 (S.hatOf 1 p₁ hp Φ, S.hatOf 1 p₁ hp Φ)
                    (S.hatOf 1 p₁ hp Φ, S.hatOf 1 p₁ hp Φ) u
                    (physInclScaled 2 S (((1 / S.β : ℝ)) : ℂ) e)) := by
  obtain ⟨m₁, t, δ, β₀, BG, BG₂, κ, hβ₀, ht, hδ, h⟩ :=
    sourceDirectTerms_scale_rho hA p hκ0def hκdecdef
  refine ⟨m₁, t, δ, β₀, BG, BG₂, κ, hβ₀, ht, hδ, ?_⟩
  intro k hk N₁ _ h3N hN ν hν hν' β hβ ρ hβρ p₁ hp0 hp₁ q hq0 hq S hS hp
  have hρ : 0 < ρ := lt_of_lt_of_le hq0 hq
  obtain ⟨val, 𝒴, T, -, -, hcont, hI, hmem0, hmemg⟩ :=
    h k hk N₁ h3N hN ν hν hν' β hβ ρ hρ hβρ p₁ hp0 hp₁ q hq0 hq S hS hp
  obtain ⟨I, h𝒴, hT⟩ := hI _ hmem0
  subst hS
  have hF := directTermsFamilyOn_scaled_rho (hatStepK (N₁ := N₁) k m₁ hk ν β p₁ δ) 1 (I := I)
    (a₁ := 1) (ν := ν) (eps := t) (β := β) (q := q) (ρ := ρ)
    (by rw [h𝒴, hT]; exact hcont) (bgHyp_lv (k := k) m₁ hν.le hν') hβρ hq
  refine ⟨val, 𝒴, T, I, h𝒴, hT, hF, ?_, ?_⟩
  · intro g hg
    have hmem : ((⟨rawOf (hatStepK (N₁ := N₁) k m₁ hk ν β p₁ δ).D', rawOf_mem_rawSub _⟩, g) :
        physParam 2 (hatStepK (N₁ := N₁) k m₁ hk ν β p₁ δ)) ∈
        physVqRho (hatStepK (N₁ := N₁) k m₁ hk ν β p₁ δ) 1 ν t ρ q :=
      ⟨(hatStepK_physVRho k m₁ hk hν.le hν' β p₁ δ ht ρ).2.1 g (hg.trans_le hq), hg⟩
    refine ⟨hmem, ?_, h𝒴, hT⟩
    rw [physInclScaled_apply]
    refine Prod.ext rfl ?_
    funext y i
    push_cast
    ring
  · intro hεU Kc hKc
    have hN3 : 3 ^ 1 ∣ N₁ := by simpa using h3N
    have hR : (0 : ℝ) ≤ 2 := by norm_num
    refine ⟨fun y Φ => labelActFamilyOn_analytic _ 1 _ hF hN3 hp0 hR hεU hκ0def.ge hKc y Φ,
      fun e he u => labelActFamilyOn_eq_dtAct _ 1 _ hF hN3 hp0 hR hεU hκ0def.ge hKc he u, ?_⟩
    intro e he u hu y Φ
    exact labelActFamilyOn_H _ 1 _ hF hN3 hp0 hR hεU hκ0def.ge hKc he hu y Φ

/-- The landed `sourceFamilyRelative_scale` is the case `ρ = 1`. -/
theorem sourceFamilyRelative_scale_of_rho {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ)
    {κ0 κdec : ℝ} (hκ0def : κ0 = aEnt 3 3 + 1) (hκdecdef : κdec = 100 * (κ0 + c1 3 3 + 10)) :
    ∃ (m₁ : ℕ) (t δ β₀ BG BG₂ κ : ℝ), 2 ≤ β₀ ∧ 0 < t ∧ 0 < δ ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (h3N : 3 ∣ N₁), 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
      ∀ p₁ : ℝ, ∀ hp0 : 0 < p₁, p₁ ≤ pLog A₁ p (β * 3 ^ k) → ∀ q : ℝ, 0 < q → q ≤ 1 →
      ∀ S : StepSetting 3 3 N₁ m₁ k 2 (rhoSep m₁),
        S = hatStepK (N₁ := N₁) k m₁ hk ν β p₁ δ → ∀ hp : 0 < S.p₁,
        ∃ (val : ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) → ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) →
            ℂ → (RawData 3 3 (N₁ * 3 ^ m₁) (k + 1) 2 × (CTorus 3 3 N₁ m₁ (k + 1) → Fin 2 → ℂ)) → ℂ)
          (𝒴 : Finset (Set (CTorus 3 3 N₁ m₁ (k + 1))))
          (T : Set (CTorus 3 3 N₁ m₁ (k + 1)) → ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) →
            ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) → ℂ →
            (RawData 3 3 (N₁ * 3 ^ m₁) (k + 1) 2 × (CTorus 3 3 N₁ m₁ (k + 1) → Fin 2 → ℂ)) → ℂ)
          (I : DirectTerms S 1 hp (fun ψ => (ψ, ψ)) p₁ 2
                (S.β * prop33EpsEtaScaled 3 3 2 m₁ k 1 S.a₁ BG BG₂ κ t
                  (lvR κ t (β * 3 ^ k) p₁) 0 0 (q / S.β)) (2 * κdec - 1)
                (rawOf S.D', (0 : CTorus 3 3 N₁ m₁ (k + 1) → Fin 2 → ℂ))
                (physSΛEta S S.a₁ S.ν t (q / S.β))
                (physXW S (lvCpsi κ t (β * 3 ^ k)) 2 2 (lvR κ t (β * 3 ^ k) p₁)) val (physAgΘ S)
                (AgFDirPair S)),
          I.𝒴 = 𝒴 ∧ I.T = T ∧
          ∃ hF : DirectTermsFamilyOn S 1 (physInclScaled 2 S (((1 / S.β : ℝ)) : ℂ)) I
              (physVq S 1 ν t q),
            (∀ g : Fld 3 3 N₁ m₁ (k + 1) 2, ∑ x, ∑ i, ‖g x i‖ < q →
              ∃ hg : (⟨rawOf S.D', rawOf_mem_rawSub _⟩, g) ∈ physVq S 1 ν t q,
                physInclScaled 2 S (((1 / S.β : ℝ)) : ℂ) (⟨rawOf S.D', rawOf_mem_rawSub _⟩, g) =
                  (rawOf S.D', fun y i => g y i / (S.β : ℂ)) ∧
                (I.atThetaOn S 1 _ hF hg).𝒴 = 𝒴 ∧ (I.atThetaOn S 1 _ hF hg).T = T) ∧
            ∀ (hεU : 0 ≤ S.β * prop33EpsEtaScaled 3 3 2 m₁ k 1 S.a₁ BG BG₂ κ t
                  (lvR κ t (β * 3 ^ k) p₁) 0 0 (q / S.β))
              {Kc : ℝ} (hKc : K0 3 3 κ0 ≤ Kc),
              (∀ (y : {Y // Y ∈ I.𝒴}) (Φ : ∀ b, (S.blockSplit 1 hp).Ωb b),
                AnalyticOnNhd ℂ (fun r : physParam 2 S × ℂ =>
                  (labelActFamilyOn S 1 (physInclScaled 2 S (((1 / S.β : ℝ)) : ℂ)) I hF
                    (show 3 ^ 1 ∣ N₁ by simpa using h3N) hp0 (by norm_num) hεU
                    hκ0def.ge hKc r.1 r.2).H y Φ)
                  (physVq S 1 ν t q ×ˢ ball (0 : ℂ) 2)) ∧
              (∀ e (he : e ∈ physVq S 1 ν t q) (u : ℂ),
                labelActFamilyOn S 1 (physInclScaled 2 S (((1 / S.β : ℝ)) : ℂ)) I hF
                    (show 3 ^ 1 ∣ N₁ by simpa using h3N) hp0 (by norm_num) hεU
                    hκ0def.ge hKc e u =
                  dtAct S 1 (I.atThetaOn S 1 _ hF he)
                    (show 3 ^ 1 ∣ N₁ by simpa using h3N) hp0 (by norm_num) hεU
                    hκ0def.ge hKc u) ∧
              (∀ e ∈ physVq S 1 ν t q, ∀ u : ℂ, ‖u‖ < 2 →
                ∀ (y : {Y // Y ∈ I.𝒴}) (Φ : ∀ b, (S.blockSplit 1 hp).Ωb b),
                (labelActFamilyOn S 1 (physInclScaled 2 S (((1 / S.β : ℝ)) : ℂ)) I hF
                    (show 3 ^ 1 ∣ N₁ by simpa using h3N) hp0 (by norm_num) hεU
                    hκ0def.ge hKc e u).H y Φ =
                  I.T y.1 (S.hatOf 1 p₁ hp Φ, S.hatOf 1 p₁ hp Φ)
                    (S.hatOf 1 p₁ hp Φ, S.hatOf 1 p₁ hp Φ) u
                    (physInclScaled 2 S (((1 / S.β : ℝ)) : ℂ) e)) := by
  obtain ⟨m₁, t, δ, β₀, BG, BG₂, κ, hβ₀, ht, hδ, h⟩ :=
    sourceFamilyRelative_scale_rho hA p hκ0def hκdecdef
  refine ⟨m₁, t, δ, β₀, BG, BG₂, κ, hβ₀, ht, hδ, ?_⟩
  intro k hk N₁ _ h3N hN ν hν hν' β hβ p₁ hp0 hp₁ q hq0 hq S hS hp
  exact h k hk N₁ h3N hN ν hν hν' β hβ 1 (by rw [max_self]; linarith) p₁ hp0 hp₁ q hq0 hq S hS hp

end Scale

end Balaban.Inhabited
