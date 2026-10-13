/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.FinalTaggedSqrt
public import Balaban.Green.FinalTagSupport

/-!
# Locality in the matrix of the Stieltjes square-root family (FINALFAM2, T3 consequence)

This construction is proposed in FINALFAM; the papers print no formula (Roland question 18 pending).

* `taggedCfinU U s`: the Stieltjes integral `π⁻¹ ∫₀^∞ t^{-1/2} G_fin(U; s, t) dt` of the tagged
  family for an arbitrary matrix `U` (same macro cover, cutoffs and tags); for the final operator
  it is `taggedCfin` (`taggedCfinU_finalOp`).
* `taggedCfinU_congr_of_agree_on_region`: if `U` and `U'` agree on `Y(C) × Y(C)`, then
  `taggedCfinU U s = taggedCfinU U' s` for every `s` supported on `C`.
* `coef_taggedGfin_congr`, `coef_taggedCfinU_congr`: the mixed coefficients at `C` of every entry
  of `s ↦ G_fin(U; s, t)` and of `s ↦ taggedCfinU U s` agree for such `U, U'`. These use
  `coef_congr`, which needs only agreement on the parameters supported on `C`; no analyticity.
-/

@[expose] public section

open Finset Matrix MeasureTheory Set

namespace Balaban.Green

variable (d L N₀ k M : ℕ) [NeZero N₀] [NeZero L]

/-- The Stieltjes integral family of the tagged parametrix for an arbitrary matrix `U`
(a construction proposed in FINALFAM). -/
noncomputable def taggedCfinU (U : Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ)
    (s : MacIdx d N₀ M → ℂ) : Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ :=
  ((1 / Real.pi : ℝ) : ℂ) • Localization.intMat (volume.restrict (Ioi (0 : ℝ)))
    (fun t => ((t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) •
      taggedGfin Finset.univ (macBoxF d N₀ M) (fun z u => ((macChi d N₀ M z u : ℝ) : ℂ))
        (macTags d N₀ M) U t s)

variable {d N₀ M}

/-- For the final operator the family is `taggedCfin`. -/
theorem taggedCfinU_finalOp {v a : ℝ} (s : MacIdx d N₀ M → ℂ) :
    taggedCfinU d N₀ M (finalOp d L N₀ k v a) s = taggedCfin d L N₀ k M v a s := by
  unfold taggedCfinU taggedCfin
  exact rfl

/-- **Locality of the integral family in the matrix.** -/
theorem taggedCfinU_congr_of_agree_on_region (hM : 0 < M) (hd : 0 < d)
    {U U' : Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ} {C : Finset (MacIdx d N₀ M)}
    (hU : ∀ x ∈ macRegion d N₀ M C, ∀ y ∈ macRegion d N₀ M C, U x y = U' x y)
    {s : MacIdx d N₀ M → ℂ} (hs : s ∈ Balaban.Localization.supportedOn C) :
    taggedCfinU d N₀ M U s = taggedCfinU d N₀ M U' s := by
  have h : ∀ t : ℝ, taggedGfin Finset.univ (macBoxF d N₀ M)
      (fun z u => ((macChi d N₀ M z u : ℝ) : ℂ)) (macTags d N₀ M) U t s =
      taggedGfin Finset.univ (macBoxF d N₀ M)
      (fun z u => ((macChi d N₀ M z u : ℝ) : ℂ)) (macTags d N₀ M) U' t s := fun t =>
    (taggedGfin_congr_of_agree_on_region hM hd Finset.univ hU hs).2.2
  simp only [taggedCfinU, h]

/-- Coefficients of the entries of `s ↦ G_fin(U; s, t)` at `C` depend only on `U` on `Y(C)`. -/
theorem coef_taggedGfin_congr (hM : 0 < M) (hd : 0 < d)
    {U U' : Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ} {C : Finset (MacIdx d N₀ M)}
    (hU : ∀ x ∈ macRegion d N₀ M C, ∀ y ∈ macRegion d N₀ M C, U x y = U' x y)
    (t : ℝ) (x y : L1Torus d N₀) :
    Balaban.Localization.coef (fun s => taggedGfin Finset.univ (macBoxF d N₀ M)
      (fun z u => ((macChi d N₀ M z u : ℝ) : ℂ)) (macTags d N₀ M) U t s x y) C =
    Balaban.Localization.coef (fun s => taggedGfin Finset.univ (macBoxF d N₀ M)
      (fun z u => ((macChi d N₀ M z u : ℝ) : ℂ)) (macTags d N₀ M) U' t s x y) C :=
  Balaban.Localization.coef_congr fun s hs => by
    rw [(taggedGfin_congr_of_agree_on_region hM hd Finset.univ hU hs).2.2]

/-- Coefficients of the entries of `s ↦ taggedCfinU U s` at `C` depend only on `U` on `Y(C)`. -/
theorem coef_taggedCfinU_congr (hM : 0 < M) (hd : 0 < d)
    {U U' : Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ} {C : Finset (MacIdx d N₀ M)}
    (hU : ∀ x ∈ macRegion d N₀ M C, ∀ y ∈ macRegion d N₀ M C, U x y = U' x y)
    (x y : L1Torus d N₀) :
    Balaban.Localization.coef (fun s => taggedCfinU d N₀ M U s x y) C =
    Balaban.Localization.coef (fun s => taggedCfinU d N₀ M U' s x y) C :=
  Balaban.Localization.coef_congr fun s hs => by
    rw [taggedCfinU_congr_of_agree_on_region hM hd hU hs]

end Balaban.Green
