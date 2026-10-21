/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.OldTermsLiftHat
public import Balaban.Fluctuation.LocalClassDensityIrrelAux
public import Balaban.Inhabited.NewLevelSystem
public import Balaban.Fluctuation.LocalClassDensityIrrelBaseSet

/-!
# Generating sets with `HatSpec`, and the regime of ruling R13 is inhabited (`ClassHatWitness`)

* `hatGSOf`: the local set `𝔹_j(X̂)` of a polymer, read on the torus of the cube exponent
  `hatScale` when it divides the torus and has the separation (the whole-level set otherwise);
  `hatSpec_hatGSOf`: it satisfies `HatSpec` (every set does when the guards fail);
* `hatTerms`: the zero terms with these generating sets;
* `classHatCond_hatClass`: the class `⟨m₀, hatTerms, 0⟩` is in the regime of ruling R13
  (`ClassHatCond`) when the block-index margin holds and `hatScale < m₀`;
* `classHatCond_nonempty` (hard rule 10): an instance at `d = L = 3`, `N = 2`, `m₁ = 4`, `m₀ = 7`,
  the separation `rhoSep 4` and the collar `r₀ = 4 d L³ + L = 327` of the class chain.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Fluctuation Balaban.Multiscale Balaban.Localization Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.SmallField.GsSpec

section Hat

variable {d L N₁ m₁ k : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

open Classical in
/-- **The local set `𝔹_j(X̂)` of a polymer** on the torus of the cube exponent `s = hatScale L m₁ ϱ`
(`N₁' L^{m₁+s} = N₁ L^{m₁}`), when `L^s ∣ N₁` and the minimal set has the separation `ϱ`; the
whole-level set `levelGS j` otherwise. -/
noncomputable def hatGSOf (m₀ j : ℕ) (hj : j ≤ k) (X : Set (CTorus d L N₁ m₁ k)) :
    GeneratingSet d L (N₁ * L ^ m₁) k ϱ :=
  if h : L ^ hatScale L m₁ ϱ ∣ N₁ ∧ ϱ ≤ LargeField.minSep L (L ^ (m₁ + hatScale L m₁ ϱ)) then
    haveI := (exists_finer_torusG (L := L) m₁ _ h.1).choose_spec.choose
    castG (exists_finer_torusG (L := L) m₁ _ h.1).choose_spec.choose_spec
      (localB j hj {x' | (torusCast x' : CTorus d L N₁ m₁ k) ∈ hatSet m₀ j X} h.2)
  else levelGS j hj

/-- **`hatGSOf` satisfies `HatSpec`.** -/
theorem hatSpec_hatGSOf (m₀ j : ℕ) (hj : j ≤ k) (X : Set (CTorus d L N₁ m₁ k)) :
    HatSpec m₀ j X (hatGSOf (ϱ := ϱ) m₀ j hj X) := by
  intro hlt hsep N₁'' _ hc''
  have hdiv : L ^ hatScale L m₁ ϱ ∣ N₁ := by
    refine ⟨N₁'', ?_⟩
    have hpos : 0 < L ^ m₁ := pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) _
    apply Nat.eq_of_mul_eq_mul_right hpos
    rw [← hc'', pow_add]
    ring
  have h : L ^ hatScale L m₁ ϱ ∣ N₁ ∧ ϱ ≤ LargeField.minSep L (L ^ (m₁ + hatScale L m₁ ϱ)) :=
    ⟨hdiv, hsep⟩
  unfold hatGSOf
  rw [dite_eq_left_of_eq_true (eq_true h)]
  have := (exists_finer_torusG (L := L) m₁ _ h.1).choose_spec.choose
  exact hatSpec_castLocalB hj X (exists_finer_torusG (L := L) m₁ _ h.1).choose_spec.choose_spec
    hsep hlt hsep N₁'' hc''

variable (d L N₁ m₁ k) in
/-- **The zero terms with the generating sets `hatGSOf`.** -/
noncomputable def hatTerms (N : ℕ) (ϱ : ℝ) (m₀ : ℕ) : Terms d L N₁ m₁ k N ϱ where
  E := fun _ _ _ _ _ => 0
  M := fun _ _ _ _ _ _ => 0
  gs := fun j X => if h : j ≤ k then hatGSOf m₀ j h X else topGS d L N₁ m₁ k ϱ

theorem hatTerms_gs {N m₀ j : ℕ} (hj : j ≤ k) (X : Set (CTorus d L N₁ m₁ k)) :
    (hatTerms d L N₁ m₁ k N ϱ m₀).gs j X = hatGSOf m₀ j hj X := by
  simp [hatTerms, hj]

end Hat

section Class

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- **The class of the zero terms `hatTerms` is in the regime of ruling R13** when the
block-index margin holds and the cube exponent is below `m₀`. -/
theorem classHatCond_hatClass {m₀ : ℕ} {r₀ : ℝ}
    (hmar : (((5 * L + 13) * L ^ hatScale L m₁ ϱ + L / 2 * L ^ m₀ : ℕ) : ℝ) + r₀ * L ≤
      (((L - 2 : ℕ)) : ℝ) * (L : ℝ) ^ (m₀ + 1))
    (hlt : hatScale L m₁ ϱ < m₀) :
    ClassHatCond (⟨m₀, hatTerms d L N₁ m₁ (k + 1) N ϱ m₀, 0⟩ : StepClass d L N₁ m₁ k N ϱ)
      (hatScale L m₁ ϱ) r₀ :=
  ⟨hmar, rfl, hlt, fun j _ hjk X _ => by
    show HatSpec m₀ j X ((hatTerms d L N₁ m₁ (k + 1) N ϱ m₀).gs j X)
    rw [hatTerms_gs (Nat.le_succ_of_le hjk)]
    exact hatSpec_hatGSOf m₀ j _ X⟩

/-- **The regime of ruling R13 is inhabited** (hard rule 10): at `d = L = 3`, `N = 2`, `m₁ = 4`,
`k = 1`, `N₁ = 3^7`, `m₀ = 7`, the separation `rhoSep 4` of the class chain (cube exponent
`hatScale ≤ 4`) and the collar `r₀ = 4 d L³ + L = 327`. -/
theorem classHatCond_nonempty :
    ∃ (C : StepClass 3 3 (3 ^ 7) 4 1 2 (I5Inhabited.rhoSep 4)) (s : ℕ),
      ClassHatCond C s (4 * ((3 : ℕ) : ℝ) * ((3 : ℕ) : ℝ) ^ 3 + ((3 : ℕ) : ℝ)) := by
  have hs : hatScale 3 4 (I5Inhabited.rhoSep 4) ≤ 4 := hatScale_le (rhoSep_le_minSep_of_four le_rfl)
  refine ⟨_, _, classHatCond_hatClass (m₀ := 7) ?_ (by omega)⟩
  have h3 : (3 : ℕ) ^ hatScale 3 4 (I5Inhabited.rhoSep 4) ≤ 3 ^ 4 :=
    Nat.pow_le_pow_right (by norm_num) hs
  have hnat : (5 * 3 + 13) * 3 ^ hatScale 3 4 (I5Inhabited.rhoSep 4) + 3 / 2 * 3 ^ 7 ≤ 4455 := by
    have : (5 * 3 + 13) * 3 ^ hatScale 3 4 (I5Inhabited.rhoSep 4) ≤ (5 * 3 + 13) * 3 ^ 4 :=
      Nat.mul_le_mul_left _ h3
    norm_num at this ⊢
    omega
  have hreal : (((5 * 3 + 13) * 3 ^ hatScale 3 4 (I5Inhabited.rhoSep 4) + 3 / 2 * 3 ^ 7 : ℕ) : ℝ)
      ≤ 4455 := by exact_mod_cast hnat
  norm_num at hreal ⊢
  linarith

end Class

end Balaban.Inhabited
