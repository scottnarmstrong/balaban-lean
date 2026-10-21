/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalClassDensityIrrelSuppSpec

/-!
# The per-label settings with their specification (`LocalClassDensityIrrelSuppSet`)

`settings_family_castLocalB_spec`: `settings_family_castLocalB` for polymers `XL τ` of `𝒟_{j_τ}`,
with the additional conclusion `GsSpecStrong j_τ (XL τ) (Gj τ)` (`gsSpecStrong_castLocalB`); its
core `settings_family_castLocalB_spec_gen` builds the generating set of each term on a sub-polymer
`X_j τ ⊆ XL τ` (the composition set `Gj τ = 𝔹_{j_τ}(X_τ)` of ruling R13 (a)).
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Multiscale Balaban.Background Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.SmallField.GsSpec Balaban.LargeField Finset

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱ₁ ϱ₂ ϱ₀ ϱ₃ ϱm : ℝ}

/-- **The per-label settings of a family of labels with the generating set of each term built on a
sub-polymer** (`Gj τ = 𝔹_{j_τ}(X_j τ)`, `X_j τ ⊆ XL τ`).  The cover, the set `Z τ` and the frozen
region are those of `XL τ`; the generating set of the term is the cast local set of `X_j τ`
(named in the conclusion) and satisfies `GsSpecStrong j_τ (X_j τ) (Gj τ)`. -/
theorem settings_family_castLocalB_spec_gen {ι : Type*} {N₁' m₁' : ℕ} [NeZero N₁']
    (hc : N₁' * L ^ m₁' = N₁ * L ^ m₁)
    {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} (hG' : IsLevel Gp (k + 1))
    {Gk0 : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₀}
    {Gj0 : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₃}
    {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
    {a₁ ν c BG κ r₀ eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl : ℝ}
    {X₀' X₁f' X₁f'' : Finset (CTorus d L N₁ m₁ (k + 1))} {j₁ : ℕ}
    (hB0 : BgSetting N Gp Gk0 Gj0 a₁ ν c BG κ r₀ eps δ₃ X₀' X₁f' j₁)
    (hF0 : FlSetting N Gp Gk0 Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl X₁f'')
    (hG : IsLevel Hm k) (hL : 2 ≤ L) {m₀ : ℕ} (hN : L ^ m₀ ∣ N₁) (hm : m₁' ≤ m₀ + m₁)
    (jL : ι → ℕ) (XL 𝒦X Xj : ι → Set (CTorus d L N₁ m₁ (k + 1)))
    (hj1 : ∀ τ, 1 ≤ jL τ) (hjk : ∀ τ, jL τ ≤ k) (hXj : ∀ τ, Xj τ ⊆ XL τ)
    (hpolyj : ∀ τ, IsPolyDom m₀ (jL τ) (Xj τ))
    (hcov : ∀ τ, CovSetup Gp m₀ (jL τ) (XL τ) (𝒦X τ))
    (hϱ₁ : bgR0 d L ≤ ϱ₁) (hϱ₂ : bgR0 d L ≤ ϱ₂) (hs₁ : ϱ₁ ≤ minSep L (L ^ m₁'))
    (hs₂ : ϱ₂ ≤ minSep L (L ^ m₁')) {c₁ : ℕ} (hm1 : L ^ m₁' ≤ L ^ m₁ * c₁)
    (hm' : (((5 * L + 13) * c₁ : ℕ) : ℝ) + r₀ * L ≤ (((L - 2 : ℕ)) : ℝ) * (L : ℝ) ^ (m₀ + 1)) :
    ∃ (Gk : ι → GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁)
      (Gj : ι → GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₂)
      (X₀ X₁f : ι → Finset (CTorus d L N₁ m₁ (k + 1))),
      (∀ τ, (↑(X₁f τ) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp m₀ (jL τ) (𝒦X τ)) ∧
      (∀ τ, BgSetting N Gp (Gk τ) (Gj τ) a₁ ν c BG κ r₀ eps δ₃ (X₀ τ) (X₁f τ) (jL τ)) ∧
      (∀ τ, FlSetting N Gp (Gk τ) Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl (X₁f τ)) ∧
      (∀ (τ : ι) (h : jL τ ≤ k + 1), GsSpecStrong (jL τ) h (Xj τ) (Gj τ)) ∧
      ∀ τ, Gj τ = castG hc (localB (jL τ) (Nat.le_succ_of_le (hjk τ))
        {x' : CTorus d L N₁' m₁' (k + 1) | (torusCast x' : CTorus d L N₁ m₁ (k + 1)) ∈ Xj τ}
        hs₂) := by
  classical
  let X' : ι → Set (CTorus d L N₁' m₁' (k + 1)) :=
    fun τ => {x' | (torusCast x' : CTorus d L N₁ m₁ (k + 1)) ∈ XL τ}
  let Xj' : ι → Set (CTorus d L N₁' m₁' (k + 1)) :=
    fun τ => {x' | (torusCast x' : CTorus d L N₁ m₁ (k + 1)) ∈ Xj τ}
  let Z' : ι → Set (CTorus d L N₁' m₁' (k + 1)) := fun τ => {z' | ∃ y' ∈ X' τ,
    supDist (fineCubeIdx (L ^ m₁') N₁' L (k + 1) k
          (torusCast z' : Torus d (L ^ m₁' * N₁' * L ^ (k + 1))))
        (fineCubeIdx (L ^ m₁') N₁' L (k + 1) k
          (torusCast y' : Torus d (L ^ m₁' * N₁' * L ^ (k + 1)))) ≤ 5 * L}
  let X₁F : ι → Finset (CTorus d L N₁ m₁ (k + 1)) :=
    fun τ => (Set.toFinite (X1 Gp m₀ (jL τ) (𝒦X τ))).toFinset
  have hX₁F : ∀ τ, (↑(X₁F τ) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp m₀ (jL τ) (𝒦X τ) :=
    fun τ => Set.Finite.coe_toFinset _
  have key := fun τ => bgFlSetting_castLocalB_gen hc hG' hB0 hF0 hG hL (hj1 τ) (hjk τ) (hcov τ)
    (X' := X' τ) (Z' := Z' τ) (fun _ => Iff.rfl) (Xj' := Xj' τ) (fun _ hx => hXj τ hx)
    (fun _ => Iff.rfl) hϱ₁ hϱ₂ hs₁ hs₂ hm1 hm' (hX₁F τ)
  exact ⟨fun τ => castG hc (localB k (Nat.le_succ k) (Z' τ) hs₁),
    fun τ => castG hc (localB (jL τ) (Nat.le_succ_of_le (hjk τ)) (Xj' τ) hs₂),
    fun τ => dataSites (castG hc (localB k (Nat.le_succ k) (Z' τ) hs₁)), X₁F, hX₁F,
    fun τ => (key τ).1, fun τ => (key τ).2,
    fun τ h => gsSpecStrong_castLocalB hc hN hm (hj1 τ) h (hpolyj τ) hs₂, fun _ => rfl⟩

/-- **The per-label settings of a family of labels, with the strong specification of `Gj`.**
As `settings_family_castLocalB`, for polymers `XL τ` of `𝒟_{j_τ}` and `m₁' ≤ m₀ + m₁`; the
generators satisfy `GsSpecStrong j_τ (XL τ) (Gj τ)` (the instance `X_j = XL` of
`settings_family_castLocalB_spec_gen`). -/
theorem settings_family_castLocalB_spec {ι : Type*} {N₁' m₁' : ℕ} [NeZero N₁']
    (hc : N₁' * L ^ m₁' = N₁ * L ^ m₁)
    {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} (hG' : IsLevel Gp (k + 1))
    {Gk0 : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₀}
    {Gj0 : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₃}
    {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
    {a₁ ν c BG κ r₀ eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl : ℝ}
    {X₀' X₁f' X₁f'' : Finset (CTorus d L N₁ m₁ (k + 1))} {j₁ : ℕ}
    (hB0 : BgSetting N Gp Gk0 Gj0 a₁ ν c BG κ r₀ eps δ₃ X₀' X₁f' j₁)
    (hF0 : FlSetting N Gp Gk0 Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl X₁f'')
    (hG : IsLevel Hm k) (hL : 2 ≤ L) {m₀ : ℕ} (hN : L ^ m₀ ∣ N₁) (hm : m₁' ≤ m₀ + m₁)
    (jL : ι → ℕ) (XL 𝒦X : ι → Set (CTorus d L N₁ m₁ (k + 1)))
    (hj1 : ∀ τ, 1 ≤ jL τ) (hjk : ∀ τ, jL τ ≤ k) (hpoly : ∀ τ, IsPolyDom m₀ (jL τ) (XL τ))
    (hcov : ∀ τ, CovSetup Gp m₀ (jL τ) (XL τ) (𝒦X τ))
    (hϱ₁ : bgR0 d L ≤ ϱ₁) (hϱ₂ : bgR0 d L ≤ ϱ₂) (hs₁ : ϱ₁ ≤ minSep L (L ^ m₁'))
    (hs₂ : ϱ₂ ≤ minSep L (L ^ m₁')) {c₁ : ℕ} (hm1 : L ^ m₁' ≤ L ^ m₁ * c₁)
    (hm' : (((5 * L + 13) * c₁ : ℕ) : ℝ) + r₀ * L ≤ (((L - 2 : ℕ)) : ℝ) * (L : ℝ) ^ (m₀ + 1)) :
    ∃ (Gk : ι → GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁)
      (Gj : ι → GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₂)
      (X₀ X₁f : ι → Finset (CTorus d L N₁ m₁ (k + 1))),
      (∀ τ, (↑(X₁f τ) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp m₀ (jL τ) (𝒦X τ)) ∧
      (∀ τ, BgSetting N Gp (Gk τ) (Gj τ) a₁ ν c BG κ r₀ eps δ₃ (X₀ τ) (X₁f τ) (jL τ)) ∧
      (∀ τ, FlSetting N Gp (Gk τ) Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl (X₁f τ)) ∧
      ∀ (τ : ι) (h : jL τ ≤ k + 1), GsSpecStrong (jL τ) h (XL τ) (Gj τ) := by
  obtain ⟨Gk, Gj, X₀, X₁f, hX₁, hB, hF, hS, -⟩ := settings_family_castLocalB_spec_gen hc hG' hB0 hF0
    hG hL hN hm jL XL 𝒦X XL hj1 hjk (fun _ => subset_rfl) hpoly hcov hϱ₁ hϱ₂ hs₁ hs₂ hm1 hm'
  exact ⟨Gk, Gj, X₀, X₁f, hX₁, hB, hF, hS⟩

end Balaban.Fluctuation
