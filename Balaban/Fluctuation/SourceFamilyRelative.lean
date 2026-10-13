/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.ParamActivitySubspace
public import Balaban.Fluctuation.SourceSliceScaled
public import Balaban.Inhabited.UniformChartRelative
public import Balaban.Fluctuation.SourceRadiusCarriers
public import Balaban.Inhabited.SourceActivityScale
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The source direct terms as a family over the relative chart, with the scaled source

The source direct terms of `sourceDirectTerms_slice` and `sourceDirectTerms_scale` live on the slice
`physSΛEta … (q/β)` of sources `g/β`, while the relative chart `physV` of the parameter space
`rawSub × sources` carries the unscaled source `g`.  This file composes the two.

* `physInclScaled N S c`: the continuous complex-linear map `(q, g) ↦ (q, c g)` from the parameter
  space to the ambient space of raw data and sources (`physInclScaled_one`: `c = 1` is `physIncl`).
* `physVq S a₁ ν eps q`: the parameters of `physV` whose source has `∑ |g| < q`.  For `q = 1` it is
  `physV` (`physVq_one`), since the source condition of `physV` is exactly `∑ |g| < 1`.  It is open
  (`isOpen_physVq`) and `physInclScaled (1/β)` maps it into the slice `physSΛEta … (q/β)`
  (`physInclScaled_image_subset`).
* `DiagCont.mono_set`: `DiagCont` restricts to subsets of the parameter set.
* `directTermsFamilyOn_scaled`: from the slice's `DirectTerms` instance and its `DiagCont`, the
  record `DirectTermsFamilyOn S m₀ (physInclScaled (1/β)) I (physVq … q)`.
* `sourceFamilyRelative_scale`: the statement at every scale of `hatStepK`: the family exists over
  `physVq … q`, contains the points `(rawOf S.D', g)` with `∑ |g| < q`, which map to the points
  `(rawOf S.D', g/β)` of the landed scale theorem, and `labelActFamilyOn` applied to it is jointly
  analytic in the parameter and equals the landed activity `dtAct` at every point.
* `physInclScaled_image_subset_rho`, `directTermsFamilyOn_scaled_rho`, `sourceFamilyRelative_scale_rho`:
  the same statements on the carriers of radius `ρ` of `SourceRadiusCarriers.lean` (`q ≤ ρ`,
  `max 1 ρ ≤ β`); the statements above are their case `ρ = 1`.
* `sourceFamilyRelative_instance`: the case `k = 1`, `N₁ = 6`, source `½ δ`.

What is NOT proved here: the identification of the exponent on the chart (the value of `physVal` at
`(q, g/β)` with `JointRep.W1 + W2`, SLICE leaves 3-4) and the complex activity bound off the central
real datum.  The class enters only through the zero class of the landed theorems: zero class, and
independent of the choice of generating sets of class terms.
-/

@[expose] public section

namespace Balaban.Fluctuation

open MeasureTheory Balaban Balaban.Localization Balaban.Multiscale Balaban.Polymer
  Balaban.Background Balaban.SmallField Balaban.SmallField.Def6 Balaban.Analysis Finset Matrix Set
  Metric

section Generic

/-- `DiagCont` restricts to subsets of the parameter set. -/
theorem DiagCont.mono_set {E F Λ ι : Type*} [TopologicalSpace E] {e : E → F} {XW : Set (F × F)}
    {S S' : Set Λ} {Rσ : ℝ} {𝒴 : Finset ι} {T : ι → F → F → ℂ → Λ → ℂ}
    (h : DiagCont e XW S Rσ 𝒴 T) (hsub : S' ⊆ S) : DiagCont e XW S' Rσ 𝒴 T :=
  fun Y hY σ hσ Θ hΘ => h Y hY σ hσ Θ (hsub hΘ)

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ)

variable (N) in
/-- **The scaled inclusion** `(q, g) ↦ (q, c g)` of the parameter space `rawSub × sources` in the
ambient space of raw data and sources. -/
noncomputable def physInclScaled (S : StepSetting d L N₁ m₁ k N ϱ) (c : ℂ) :
    physParam N S →L[ℂ] RawData d L (N₁ * L ^ m₁) (k + 1) N ×
      (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) :=
  (rawSub N S.G').subtypeL.prodMap (c • ContinuousLinearMap.id ℂ _)

theorem physInclScaled_apply (c : ℂ) (e : physParam N S) :
    physInclScaled N S c e = ((e.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N),
      fun y i => c * e.2 y i) := rfl

theorem physInclScaled_one : physInclScaled N S 1 = physIncl N S := by
  ext e <;> simp [physInclScaled_apply, physIncl_apply]

/-- The parameters of `physV` whose source has `∑ |g| < q`. -/
def physVq (a₁ ν eps q : ℝ) : Set (physParam N S) :=
  {e | e ∈ physV S a₁ ν eps ∧ ∑ x, ∑ i, ‖e.2 x i‖ < q}

/-- For `q = 1` the set `physVq` is `physV`: the source condition of `physV` is `∑ |g| < 1`. -/
theorem physVq_one (a₁ ν eps : ℝ) : physVq (N := N) S a₁ ν eps 1 = physV S a₁ ν eps :=
  Set.ext fun _ => ⟨fun h => h.1, fun h => ⟨h, h.2⟩⟩

theorem physVq_subset (a₁ ν eps q : ℝ) : physVq (N := N) S a₁ ν eps q ⊆ physV S a₁ ν eps :=
  fun _ h => h.1

theorem isOpen_physVq (a₁ ν eps q : ℝ) (H : BgHyp d L (k + 1) ϱ (compWeight L a₁) ν) :
    IsOpen (physVq (N := N) S a₁ ν eps q) := by
  have h2 : IsOpen {e : physParam N S | ∑ x, ∑ i, ‖e.2 x i‖ < q} :=
    isOpen_lt (by fun_prop) continuous_const
  exact (isOpen_physV S a₁ ν eps H).inter h2

/-- **The image in the slice.**  For `1 ≤ β` and `q ≤ 1`, `(q, g) ↦ (q, g/β)` maps `physVq … q`
into `physSΛEta … (q/β)`. -/
theorem physInclScaled_image_subset (a₁ ν eps : ℝ) {β q : ℝ} (hβ : 1 ≤ β) (hq : q ≤ 1) :
    physInclScaled N S ((1 / β : ℝ) : ℂ) '' physVq S a₁ ν eps q ⊆
      physSΛEta S a₁ ν eps (q / β) := by
  rintro _ ⟨e, ⟨he, hsum⟩, rfl⟩
  refine ⟨he.1, ?_⟩
  have h := sourceSlice_mem_restricted (N := N) hβ hsum hq
  have hfun : (fun y i => ((1 / β : ℝ) : ℂ) * e.2 y i) = fun y i => e.2 y i / (β : ℂ) := by
    funext y i
    push_cast
    ring
  show (fun y i => ((1 / β : ℝ) : ℂ) * e.2 y i) ∈ _
  rw [hfun]
  exact h

/-- **The image in the slice** at radius `ρ`: for `max 1 ρ ≤ β`, `0 < ρ` and `q ≤ ρ`,
`(q, g) ↦ (q, g/β)` maps `physVqRho … ρ q` into `physSΛEta … (q/β)`. -/
theorem physInclScaled_image_subset_rho (a₁ ν eps : ℝ) {ρ β q : ℝ}
    (hβ : max 1 ρ ≤ β) (hq : q ≤ ρ) :
    physInclScaled N S ((1 / β : ℝ) : ℂ) '' physVqRho S a₁ ν eps ρ q ⊆
      physSΛEta S a₁ ν eps (q / β) := by
  rintro _ ⟨e, ⟨he, hsum⟩, rfl⟩
  refine ⟨he.1, ?_⟩
  have h := sourceSlice_mem_restricted_radius (N := N) hβ hsum hq
  have hfun : (fun y i => ((1 / β : ℝ) : ℂ) * e.2 y i) = fun y i => e.2 y i / (β : ℂ) := by
    funext y i
    push_cast
    ring
  show (fun y i => ((1 / β : ℝ) : ℂ) * e.2 y i) ∈ _
  rw [hfun]
  exact h

section Radius

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

end Radius

variable (m₀ : ℕ) {Λ F' : Type} {hp : 0 < S.p₁} {emb : (S.U × Fin N → ℂ) → F'}
  {ρ Rσ εU a a₁ ν eps : ℝ}
  {Θ₀ : RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)}
  {XW : Set (F' × F')} {val : F' → F' → ℂ →
    RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ}
  {AgF : Set (CTorus d L N₁ m₁ (k + 1)) → F' → F' → Prop}

/-- **The family over the relative chart with the scaled source.**  From a `DirectTerms` instance on
the slice `physSΛEta … (q/β)` whose diagonal terms are continuous on the slice, the relative family
over `physVq … q` with the map `(q, g) ↦ (q, g/β)`. -/
theorem directTermsFamilyOn_scaled {β q : ℝ}
    {I : DirectTerms S m₀ hp emb ρ Rσ εU a Θ₀ (physSΛEta S a₁ ν eps (q / β)) XW val (physAgΘ S)
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

/-- **The source direct terms as a family over the relative chart, at every scale.**  The
quantifiers are those of `sourceDirectTerms_scale`.  For the step `hatStepK k m₁ hk ν β p₁ δ`, the
`DirectTerms` instance `I` at the central datum `(rawOf S.D', 0)` of the slice `q/β`, with the
domains and terms `𝒴`, `T` of the landed theorem, carries the relative family
`DirectTermsFamilyOn S 1 (physInclScaled (1/β)) I (physVq S 1 ν t q)`; the points
`(rawOf S.D', g)`, `∑ |g| < q`, lie in `physVq` and are sent to the points `(rawOf S.D', g/β)` of
the landed theorem, where `I.atThetaOn` has the same domains and terms.  If `0 ≤ ε_U` (the
amplitude) and `K_c ≥ K₀`, then `labelActFamilyOn` is jointly analytic in `(e, u)` on
`physVq ×ˢ ball 0 2` for every configuration and label, equals the landed activity `dtAct` of
`I.atThetaOn` at every `e`, and its label `Y` at `e` and `‖u‖ < 2` is the term `T_Y` at the hat
variable and the datum `physInclScaled e`; all have the uniform bound of the type `LabelAct`
(amplitude `2 ε_U`, rate `2 κ_dec - 1`, entropy constant `K_c`). -/
theorem sourceFamilyRelative_scale {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ)
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

/-- **A non-vacuous instance with a nonzero source.**  At `k = 1`, `N₁ = 6`, the mass `nuW`, `q = 1`
and every `β ≥ β₀`: the family `DirectTermsFamilyOn` over `physVq … 1 = physV` exists for the step
`hatStepK 1 m₁ _ nuW β (A₁ (log 3β)^p) δ`, and the point of the parameter space with the central
datum `rawOf S.D'` and the nonzero source `g = ½ δ_{(0,0)}` lies in `physVq … 1`. -/
theorem sourceFamilyRelative_instance {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ)
    {κ0 κdec : ℝ} (hκ0def : κ0 = aEnt 3 3 + 1) (hκdecdef : κdec = 100 * (κ0 + c1 3 3 + 10)) :
    ∃ (m₁ : ℕ) (t δ β₀ BG BG₂ κ : ℝ), 2 ≤ β₀ ∧ 0 < t ∧ 0 < δ ∧
      (Pi.single 0 (Pi.single 0 (1 / 2)) : Fld 3 3 6 m₁ (1 + 1) 2) ≠ 0 ∧
      ∀ β : ℝ, β₀ ≤ β →
        ∀ S : StepSetting 3 3 6 m₁ 1 2 (rhoSep m₁),
        S = hatStepK (N₁ := 6) 1 m₁ le_rfl nuW β (pLog A₁ p (β * 3 ^ 1)) δ →
        ∃ (hp : 0 < S.p₁) (val : ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) →
            ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) →
            ℂ → (RawData 3 3 (6 * 3 ^ m₁) (1 + 1) 2 × (CTorus 3 3 6 m₁ (1 + 1) → Fin 2 → ℂ)) → ℂ)
          (I : DirectTerms S 1 hp (fun ψ => (ψ, ψ)) (pLog A₁ p (β * 3 ^ 1)) 2
                (S.β * prop33EpsEtaScaled 3 3 2 m₁ 1 1 S.a₁ BG BG₂ κ t
                  (lvR κ t (β * 3 ^ 1) (pLog A₁ p (β * 3 ^ 1))) 0 0 (1 / S.β)) (2 * κdec - 1)
                (rawOf S.D', (0 : CTorus 3 3 6 m₁ (1 + 1) → Fin 2 → ℂ))
                (physSΛEta S S.a₁ S.ν t (1 / S.β))
                (physXW S (lvCpsi κ t (β * 3 ^ 1)) 2 2
                  (lvR κ t (β * 3 ^ 1) (pLog A₁ p (β * 3 ^ 1)))) val (physAgΘ S)
                (AgFDirPair S)),
          DirectTermsFamilyOn S 1 (physInclScaled 2 S (((1 / S.β : ℝ)) : ℂ)) I
            (physVq S 1 nuW t 1) ∧
          (⟨rawOf S.D', rawOf_mem_rawSub _⟩,
            (Pi.single 0 (Pi.single 0 (1 / 2)) : Fld 3 3 6 m₁ (1 + 1) 2)) ∈ physVq S 1 nuW t 1 := by
  obtain ⟨m₁, t, δ, β₀, BG, BG₂, κ, hβ₀, ht, hδ, h⟩ :=
    sourceFamilyRelative_scale hA p hκ0def hκdecdef
  have hmem : (Pi.single 0 (Pi.single 0 (1 / 2)) : Fld 3 3 6 m₁ (1 + 1) 2) ∈
      l1Ball 3 3 6 m₁ (1 + 1) 2 := by
    show ∑ x, ∑ i, ‖(Pi.single 0 (Pi.single 0 (1 / 2)) : Fld 3 3 6 m₁ (1 + 1) 2) x i‖ < 1
    rw [l1_single_eq]
    norm_num
  refine ⟨m₁, t, δ, β₀, BG, BG₂, κ, hβ₀, ht, hδ, ?_, ?_⟩
  · intro h0
    have := congrFun (congrFun h0 0) 0
    simp at this
  · intro β hβ S hS
    have hβ2 : 2 ≤ β := hβ₀.trans hβ
    have hb : 1 < β * 3 ^ 1 := by linarith
    have hp0 := pLog_pos hA p hb
    have hp : 0 < S.p₁ := by subst hS; exact hp0
    obtain ⟨val, 𝒴, T, I, -, -, hF, hpt, -⟩ := h 1 le_rfl 6 (by norm_num) (by norm_num) nuW
      nuW_pos (by unfold nuW; norm_num) β hβ _ hp0 le_rfl 1 one_pos le_rfl S hS hp
    obtain ⟨hg, -⟩ := hpt (Pi.single 0 (Pi.single 0 (1 / 2))) hmem
    exact ⟨hp, val, I, hF, hg⟩

end Scale

end Balaban.Inhabited
