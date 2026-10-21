/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.LocalBBoxCorr

/-!
# The cast local generating sets of corresponding polymers on two tori

The generating sets of the settings of the inherited levels are `castG hc (𝔹_n(P))` with `𝔹_n(P)` the
local set on the finer torus `(N₁', m₁')`, `N₁' L^{m₁'} = N₁ L^{m₁}`.  `torusCast` commutes with
`boxMap` and preserves boxes, so the correspondence of the domains `localB_omega_boxMap_all` holds
for the cast sets on the coarse tori (`castLocalB_omega_boxMap_all`).
-/

@[expose] public section

namespace Balaban.Polymer.TwoTorusStep

open Balaban Balaban.Localization Balaban.Background Balaban.Multiscale Balaban.SmallField
  Balaban.LargeField Balaban.SmallField.Def6 Balaban.SmallField.GsSpec

section CastBox

variable {d : ℕ}

theorem boxMap_torusCast {a a' b b' : ℕ} [NeZero a] [NeZero b] (ha : a = a') (hb : b = b') (x : Torus d a) :
    boxMap a' b' (torusCast x : Torus d a') = (torusCast (boxMap a b x) : Torus d b') := by
  subst ha hb
  funext μ
  simp [boxMap, torusCast]

theorem inBox_torusCast {a a' r : ℕ} [NeZero a] (ha : a = a') (x : Torus d a) :
    InBox d r a' (torusCast x : Torus d a') ↔ InBox d r a x := by
  subst ha
  have : (torusCast x : Torus d a) = x := by funext μ; simp [torusCast]
  rw [this]

end CastBox

section Cast

variable {d L N₁ N₂ NA NB m₁ m' k : ℕ} [NeZero N₁] [NeZero N₂] [NeZero NA] [NeZero NB] [NeZero L]
  {ϱ ϱ' : ℝ}

/-- **The domains of the cast local generating sets of corresponding polymers correspond on the whole
box.** -/
theorem castLocalB_omega_boxMap_all (hcA : NA * L ^ m' = N₁ * L ^ m₁)
    (hcB : NB * L ^ m' = N₂ * L ^ m₁) {j : ℕ} (hj : j ≤ k)
    {X : Set (CTorus d L NA m' k)} {X' : Set (CTorus d L NB m' k)}
    {hsep : ϱ ≤ minSep L (L ^ m')} {hsep' : ϱ' ≤ minSep L (L ^ m')} {ρ0 : ℕ}
    (hX : ∀ x ∈ X, InBox d ρ0 ((NA * L ^ m') * L ^ k) x)
    (hXX : X' = boxMap ((NA * L ^ m') * L ^ k) ((NB * L ^ m') * L ^ k) '' X)
    (hmA : ∀ n ≤ j, 2 * (ρ0 + 6 * j * L ^ (j + m') + (5 * L + 2) * (L ^ n * L ^ m')) <
      NA * L ^ m' * L ^ k)
    (hmB : ∀ n ≤ j, 2 * (ρ0 + 6 * j * L ^ (j + m') + (5 * L + 2) * (L ^ n * L ^ m')) <
      NB * L ^ m' * L ^ k) :
    (∀ n, ∀ x ∈ (castG hcA (localB j hj X hsep)).Ω n,
      InBox d (ρ0 + 6 * j * L ^ (j + m')) ((N₁ * L ^ m₁) * L ^ k) x) ∧
    (∀ n, ∀ x ∈ (castG hcB (localB j hj X' hsep')).Ω n,
      InBox d (ρ0 + 6 * j * L ^ (j + m')) ((N₂ * L ^ m₁) * L ^ k) x) ∧
    ∀ x : CTorus d L N₁ m₁ k, InBox d (ρ0 + 6 * j * L ^ (j + m')) ((N₁ * L ^ m₁) * L ^ k) x →
      ∀ n, (boxMap ((N₁ * L ^ m₁) * L ^ k) ((N₂ * L ^ m₁) * L ^ k) x ∈
        (castG hcB (localB j hj X' hsep')).Ω n ↔ x ∈ (castG hcA (localB j hj X hsep)).Ω n) := by
  have hA : NA * L ^ m' * L ^ k = N₁ * L ^ m₁ * L ^ k := by rw [hcA]
  have hB : NB * L ^ m' * L ^ k = N₂ * L ^ m₁ * L ^ k := by rw [hcB]
  obtain ⟨h1, h2, h3⟩ := localB_omega_boxMap_all hj hX hXX hmA hmB (hsep := hsep) (hsep' := hsep')
  refine ⟨fun n x hx => ?_, fun n x hx => ?_, fun x hx n => ?_⟩
  · rw [mem_castG_Ω] at hx
    exact (inBox_torusCast hA.symm x).1 (h1 n _ hx)
  · rw [mem_castG_Ω] at hx
    exact (inBox_torusCast hB.symm x).1 (h2 n _ hx)
  · rw [mem_castG_Ω, mem_castG_Ω]
    have hxf : InBox d (ρ0 + 6 * j * L ^ (j + m')) ((NA * L ^ m') * L ^ k)
        (torusCast x : Torus d ((NA * L ^ m') * L ^ k)) :=
      (inBox_torusCast hA.symm x).2 hx
    have := h3 _ hxf n
    rwa [boxMap_torusCast hA.symm hB.symm x] at this

/-- **`GSIso` for the cast local generating sets of corresponding polymers**, on a region `R`
containing the sites of `Ω₁` and their neighbours. -/
theorem gsIso_castLocalB_on (hcA : NA * L ^ m' = N₁ * L ^ m₁) (hcB : NB * L ^ m' = N₂ * L ^ m₁)
    {j : ℕ} (hj : j ≤ k) (hK : 1 ≤ k) {X : Set (CTorus d L NA m' k)} {X' : Set (CTorus d L NB m' k)}
    {hsep : ϱ ≤ minSep L (L ^ m')} {hsep' : ϱ' ≤ minSep L (L ^ m')} {ρ0 : ℕ}
    (hX : ∀ x ∈ X, InBox d ρ0 ((NA * L ^ m') * L ^ k) x)
    (hXX : X' = boxMap ((NA * L ^ m') * L ^ k) ((NB * L ^ m') * L ^ k) '' X)
    (hmA : ∀ n ≤ j, 2 * (ρ0 + 1 + 6 * j * L ^ (j + m') + (5 * L + 2) * (L ^ n * L ^ m')) <
      NA * L ^ m' * L ^ k)
    (hmB : ∀ n ≤ j, 2 * (ρ0 + 1 + 6 * j * L ^ (j + m') + (5 * L + 2) * (L ^ n * L ^ m')) <
      NB * L ^ m' * L ^ k)
    (hn : 2 * (ρ0 + 6 * j * L ^ (j + m') + 1) + 3 * L ^ k + 5 < (N₁ * L ^ m₁) * L ^ k)
    (hn' : 2 * (ρ0 + 6 * j * L ^ (j + m') + 1) + 3 * L ^ k + 5 < (N₂ * L ^ m₁) * L ^ k)
    (a : ℕ → ℝ) (ν : ℝ) (R : Set (CTorus d L N₁ m₁ k))
    (hR : ∀ x ∈ (castG hcA (localB j hj X hsep)).Ω 1, x ∈ R ∧ ∀ μ : Fin d,
      x + Pi.single μ 1 ∈ R ∧ x - Pi.single μ 1 ∈ R) :
    GSIso a ν (castG hcA (localB j hj X hsep)) (castG hcB (localB j hj X' hsep'))
      (boxMap ((N₁ * L ^ m₁) * L ^ k) ((N₂ * L ^ m₁) * L ^ k)) R := by
  obtain ⟨h1, h2, -⟩ := castLocalB_omega_boxMap_all hcA hcB hj hX hXX
    (fun n hn => by have := hmA n hn; omega) (fun n hn => by have := hmB n hn; omega)
    (hsep := hsep) (hsep' := hsep')
  obtain ⟨-, -, h3⟩ := castLocalB_omega_boxMap_all hcA hcB hj (ρ0 := ρ0 + 1)
    (fun x hx => inBox_mono (Nat.le_succ ρ0) (hX x hx)) hXX hmA hmB (hsep := hsep) (hsep' := hsep')
  exact gsIso_of_omega_on a ν hK hn hn' (fun x hx => h1 1 x hx) (fun x hx => h2 1 x hx)
    (fun x hx n _ _ => by
      refine h3 x ?_ n
      have : ρ0 + 1 + 6 * j * L ^ (j + m') = ρ0 + 6 * j * L ^ (j + m') + 1 := by ring
      rwa [this]) R hR

/-- **`GSCorr` for the cast local generating sets of corresponding polymers.** -/
theorem gsCorr_castLocalB (hcA : NA * L ^ m' = N₁ * L ^ m₁) (hcB : NB * L ^ m' = N₂ * L ^ m₁)
    {j : ℕ} (hj : j ≤ k) (hK : 1 ≤ k) {X : Set (CTorus d L NA m' k)} {X' : Set (CTorus d L NB m' k)}
    {hsep : ϱ ≤ minSep L (L ^ m')} {hsep' : ϱ' ≤ minSep L (L ^ m')} {ρ0 : ℕ}
    (hX : ∀ x ∈ X, InBox d ρ0 ((NA * L ^ m') * L ^ k) x)
    (hXX : X' = boxMap ((NA * L ^ m') * L ^ k) ((NB * L ^ m') * L ^ k) '' X)
    (hmA : ∀ n ≤ j, 2 * (ρ0 + 1 + 6 * j * L ^ (j + m') + (5 * L + 2) * (L ^ n * L ^ m')) <
      NA * L ^ m' * L ^ k)
    (hmB : ∀ n ≤ j, 2 * (ρ0 + 1 + 6 * j * L ^ (j + m') + (5 * L + 2) * (L ^ n * L ^ m')) <
      NB * L ^ m' * L ^ k)
    (hn : 2 * (ρ0 + 6 * j * L ^ (j + m') + 1 + L ^ k) + 3 * L ^ k + 5 < (N₁ * L ^ m₁) * L ^ k)
    (hn' : 2 * (ρ0 + 6 * j * L ^ (j + m') + 1 + L ^ k) + 3 * L ^ k + 5 < (N₂ * L ^ m₁) * L ^ k) :
    GSCorr (castG hcA (localB j hj X hsep)) (castG hcB (localB j hj X' hsep'))
      (boxMap ((N₁ * L ^ m₁) * L ^ k) ((N₂ * L ^ m₁) * L ^ k))
      {z | InBox d (ρ0 + 6 * j * L ^ (j + m')) ((N₁ * L ^ m₁) * L ^ k) z} := by
  obtain ⟨h1, h2, -⟩ := castLocalB_omega_boxMap_all hcA hcB hj hX hXX
    (fun n hn => by have := hmA n hn; omega) (fun n hn => by have := hmB n hn; omega)
    (hsep := hsep) (hsep' := hsep')
  obtain ⟨-, -, h3⟩ := castLocalB_omega_boxMap_all hcA hcB hj (ρ0 := ρ0 + 1)
    (fun x hx => inBox_mono (Nat.le_succ ρ0) (hX x hx)) hXX hmA hmB (hsep := hsep) (hsep' := hsep')
  exact gsCorr_of_omega hK hn hn' (fun x hx => h1 1 x hx) (fun x hx => h2 1 x hx)
    (fun x hx n _ _ => by
      refine h3 x ?_ n
      have : ρ0 + 1 + 6 * j * L ^ (j + m') = ρ0 + 6 * j * L ^ (j + m') + 1 := by ring
      rwa [this])

end Cast

end Balaban.Polymer.TwoTorusStep
