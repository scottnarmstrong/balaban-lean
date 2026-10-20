/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.FrozenLFStep

/-!
# The histories of a step: a complete set exists (parts (c) of the large-field halves)

`IsComplete k r 𝔄` (D-III.8: the histories of a representation are all admissible histories, one
representative per class of records) refers to the setting only; `exists_isComplete` gives such a set
for every `k, r`. `canonHist` is a fixed complete set (a choice of representatives), and the
histories of a step map that are the canonical ones satisfy the history parts of both large-field
halves:

* `LFHistInput_of_canon` (pre-`R` steps, `IsComplete (k+1) (k+1)`);
* `FrozenHistInput_of_canon` (frozen steps, `IsComplete (k+1) (k+2)`).

A step map whose histories are the canonical ones is a legitimate choice for the provider: the
other data of the map (kernels, boundary terms) are independent of the representatives (the
terms of (D1) are functions of the records, `Agree`).
-/

@[expose] public section

open Balaban Balaban.LargeField Balaban.LargeField.Def7 Balaban.Multiscale Balaban.SmallField
  Balaban.SmallField.Def6v2 Balaban.LargeField.Def7v2

namespace Balaban.RootFSpine

section Canon

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}

/-- **A fixed complete set of histories up to the scale `k`** with the `R`-records below `r`. -/
noncomputable def canonHist (S : Setting) (n : ℕ → ℕ) [∀ k, NeZero (n k)] (R : ℕ → ℝ) (k0 K k r : ℕ) :
    Finset (LabHist S n R k0 K) :=
  Classical.choose (exists_isComplete (S := S) (n := n) (R := R) (k0 := k0) (K := K) k r)

theorem canonHist_complete (k r : ℕ) : IsComplete k r (canonHist S n R k0 K k r) :=
  Classical.choose_spec (exists_isComplete (S := S) (n := n) (R := R) (k0 := k0) (K := K) k r)

end Canon

section Inputs

variable {d N : ℕ} {T : ℝ → ℝ → Typing} {P6 : ℝ → ℝ → Def6.Consts}
  {C7 : ℝ → ℝ → Consts7} {PB : ℝ → ℝ → BudgetConsts} {cs₀ : ℝ → ℝ → OpConsts}
  {M1 c : ℝ → ℝ → ℕ} {rH ϱ : ℝ → ℝ → ℝ}
  {Φ : ∀ (κ c₉ _ _ : ℝ) (k : ℕ) [NeZero (T κ c₉).L],
    SFData d (T κ c₉).L (C7 κ c₉).m₁ k N (ϱ κ c₉) →
      SFData d (T κ c₉).L (C7 κ c₉).m₁ (k + 1) N (ϱ κ c₉)}

/-- **`LFHistInput` for a step map with the canonical histories.** -/
theorem LFHistInput_of_canon (Λ : LFStepMap d N T P6 C7 PB cs₀ M1 c rH ϱ)
    (hΛ : ∀ (κ c₉ β ν : ℝ) (h : EuclideanSpace ℝ (Fin N)) (kf : ℕ) [NeZero (T κ c₉).L]
      [NeZero (T κ c₉).M] (k : ℕ) (ρ : 𝒟[d, N, T κ c₉, β, (cs₀ κ c₉).aKer, kf + 1, k]) (νk : ℝ)
      (rec : RepRec d N (T κ c₉) (P6 κ c₉) (C7 κ c₉) (PB κ c₉) (cs₀ κ c₉) (M1 κ c₉) (c κ c₉)
        (rH κ c₉) (ϱ κ c₉) β ν h kf k ρ νk) (nK : ℕ) [NeZero nK],
      (Λ κ c₉ β ν h kf k ρ νk rec).hist nK =
        canonHist 𝒮[d, T κ c₉, β, (cs₀ κ c₉).aKer] (sides (T κ c₉).L (kf + 1) nK) rec.R
          (kZero d (T κ c₉).L β ν) (kf + 1) (k + 1) (k + 1)) :
    LFHistInput d N T P6 C7 PB cs₀ M1 c rH ϱ Φ Λ := by
  intro κ _ c₉ _
  refine ⟨0, fun β _ ν _ _ h _ kf _ _ _ k _ _ ρ νk rec _ _ _ _ _ _ nK _ => ?_⟩
  rw [hΛ κ c₉ β ν h kf k ρ νk rec nK]
  exact canonHist_complete _ _

/-- **`FrozenHistInput` for a frozen step map with the canonical histories.** -/
theorem FrozenHistInput_of_canon (Λ : FrozenLFStepMap d N T P6 C7 PB cs₀ M1 c rH ϱ)
    (hΛ : ∀ (κ c₉ β ν : ℝ) (h : EuclideanSpace ℝ (Fin N)) (kf : ℕ) [NeZero (T κ c₉).L]
      [NeZero (T κ c₉).M] (k : ℕ) (ρ : 𝒟[d, N, T κ c₉, β, (cs₀ κ c₉).aKer, kf + 1, k]) (νk : ℝ)
      (hM6 : (T κ c₉).M = (T κ c₉).L ^ ((P6 κ c₉).m₀ + (C7 κ c₉).m₁)) (hkK : k ≤ kf + 1)
      (R : ℕ → ℝ)
      (geo : ∀ (nK : ℕ) [NeZero nK], Geo 𝒮[d, T κ c₉, β, (cs₀ κ c₉).aKer]
        (sides (T κ c₉).L (kf + 1) nK) R (T κ c₉).M)
      (cs : OpConsts) (P : BudgetConsts)
      (F : RepFam 𝒮[d, T κ c₉, β, (cs₀ κ c₉).aKer] R (kZero d (T κ c₉).L β ν) (kf + 1)
        (T κ c₉).M N geo cs P k (C7 κ c₉).m₁ (ϱ κ c₉))
      (St : ∀ (N₁ : ℕ) [NeZero N₁], SourceTerms d (T κ c₉).L N₁ (C7 κ c₉).m₁ k N) (vc : CorrCoef d)
      (hF : FlatRep d N (T κ c₉) (P6 κ c₉) (C7 κ c₉) (PB κ c₉) (cs₀ κ c₉) (M1 κ c₉) (c κ c₉)
        (rH κ c₉) (ϱ κ c₉) β ν h kf k hM6 hkK R geo cs P F St vc ρ νk) (nK : ℕ) [NeZero nK],
      (Λ κ c₉ β ν h kf k ρ νk hM6 hkK R geo cs P F St vc hF).hist nK =
        canonHist 𝒮[d, T κ c₉, β, (cs₀ κ c₉).aKer] (sides (T κ c₉).L (kf + 1) nK) R
          (kZero d (T κ c₉).L β ν) (kf + 1) (k + 1) (k + 1 + 1)) :
    FrozenHistInput d N T P6 C7 PB cs₀ M1 c rH ϱ Φ Λ := by
  intro κ _ c₉ _
  refine ⟨0, fun β _ ν _ _ h _ kf _ _ _ k _ _ _ ρ νk hM6 hkK R geo cs P F St vc hF _ _ _ _ _ _ _
    nK _ => ?_⟩
  rw [hΛ κ c₉ β ν h kf k ρ νk hM6 hkK R geo cs P F St vc hF nK]
  exact canonHist_complete _ _

end Inputs

end Balaban.RootFSpine
