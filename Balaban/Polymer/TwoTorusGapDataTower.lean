/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusData
public import Balaban.Fluctuation.InteractionSymmLat
public import Balaban.Inhabited.DetOutputTermsWitnessG

/-!
# Tower producers of the data hypotheses of the gap-scale step (blocker 7)

* `flCore_gapLevels` (`hC`): the core `FlCore` of the level pair `(𝔹_{k+1}, 𝔹_k)` on every
  step torus `N₁ ℓ`, from the core of the reference pair (`flCore_stepG`).
* `rawBoxAgree_unitBg_recentred` (`hrawO`, `hraw`): the raw data of the zero-class base datum
  `unitBg` of the steps on two tori agree on every set of sites after any two translations, since
  both are constant.
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Polymer.TwoTorusStep

open Balaban Balaban.Localization Balaban.Fluctuation Balaban.Polymer Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.Background Balaban.Inhabited Balaban.Inhabited.LevelStep

section Tower

/-- **`hC` of the gap-scale step on every torus**: the core of the level pair at the scale `k` on
the tori `N₁ ℓ` (`5 < N₁ ℓ`) with the mass `ν` is the transfer of the core of the reference pair
(`flCore_stepG`). -/
theorem flCore_gapLevels {ι : Type*} {d L N m₁ k : ℕ} [NeZero L] (hd : 3 ≤ d) (hL : 3 ≤ L)
    (h4 : 4 ≤ m₁) {c BG κ t c₂ BG₂ : ℝ}
    (hC₀ : FlCore N (GpG d L 9 m₁ 1) (HmG d L 9 m₁ 1) 1 (νref L) c BG κ t (levelKc d L)
      (Cchi d L) c₂ BG₂ t)
    (hk : 1 ≤ k) {N₁ : ι → ℕ} [∀ ℓ, NeZero (N₁ ℓ)] (hN₁ : ∀ ℓ, 5 < N₁ ℓ) {ν : ℝ}
    (hν0 : 0 ≤ ν) (hν : ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1) :
    ∀ ℓ, FlCore N (levelGS (d := d) (L := L) (N₁ := N₁ ℓ) (m₁ := m₁) (k := k + 1)
        (ϱ := rhoSepG d L m₁) (k + 1) le_rfl)
      (levelGS (d := d) (L := L) (N₁ := N₁ ℓ) (m₁ := m₁) (k := k + 1) (ϱ := rhoSepG d L m₁) k
        (Nat.le_succ k)) 1 ν c BG κ t (levelKc d L) (Cchi d L) c₂ BG₂ t :=
  fun ℓ => flCore_stepG hd hL h4 hC₀ hk (hN₁ ℓ) hν0 hν

/-- **The raw data of the zero-class base datum agree after any translations.**  The datum
`unitBg` of the level `k + 1` on the tori `N₁` and `N₁'` is the constant unit field and the
constant `h`, so its raw data, translated by any `z`, `z'`, agree on every set `R` of sites under
the box map. -/
theorem rawBoxAgree_unitBg_recentred {d L m₁ k N N₁ N₁' : ℕ} [NeZero L] [NeZero N₁] [NeZero N₁']
    {ϱ : ℝ} (hN : 0 < N) (R : Set (Torus d ((N₁ * L ^ m₁) * L ^ (k + 1))))
    (z : Torus d ((N₁ * L ^ m₁) * L ^ (k + 1))) (z' : Torus d ((N₁' * L ^ m₁) * L ^ (k + 1))) :
    RawBoxAgree R
      (symRaw (Equiv.addRight z)
        (rawOf (unitBg (lvTopG d L N₁ m₁ k ϱ) hN (unitVec hN))))
      (symRaw (Equiv.addRight z')
        (rawOf (unitBg (lvTopG d L N₁' m₁ k ϱ) hN (unitVec hN)))) := by
  intro x _
  have hΩ : ∀ (M : ℕ) [NeZero M] (y : Torus d ((M * L ^ m₁) * L ^ (k + 1))),
      y ∈ (lvTopG d L M m₁ k ϱ).Ω 1 := fun M _ y => by
    rw [lvTopG_Ω]; simp
  refine ⟨funext fun i => ?_, funext fun i => ?_⟩
  · show (unitBg (lvTopG d L N₁ m₁ k ϱ) hN (unitVec hN)).Ψ _ i =
      (unitBg (lvTopG d L N₁' m₁ k ϱ) hN (unitVec hN)).Ψ _ i
    rw [unitBg_Ψ_of_mem _ hN (unitVec hN) ((mem_dataSites _).2 (Or.inl (hΩ N₁ _))),
      unitBg_Ψ_of_mem _ hN (unitVec hN) ((mem_dataSites _).2 (Or.inl (hΩ N₁' _)))]
  · show (unitBg (lvTopG d L N₁ m₁ k ϱ) hN (unitVec hN)).h _ i =
      (unitBg (lvTopG d L N₁' m₁ k ϱ) hN (unitVec hN)).h _ i
    rw [unitBg_h_of_mem _ hN (unitVec hN) (hΩ N₁ _), unitBg_h_of_mem _ hN (unitVec hN) (hΩ N₁' _)]

end Tower

end Balaban.Polymer.TwoTorusStep
