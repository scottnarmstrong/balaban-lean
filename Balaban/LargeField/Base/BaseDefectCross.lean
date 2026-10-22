/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseChartDefectAct
public import Balaban.LargeField.Base.BaseChartCross
public import Balaban.LargeField.Base.BaseLabelCross

/-!
# The quadratic defect of two generating sets agrees near a deep site

`defPt_cross`: the defect at a site `x` of a generating set `Gl` and at the same site of a generating set
`Gp` with `Ω₁` the whole torus agree when the matrices and the fields correspond near `x`;
`defTerm_cross`: the activity `defTerm` of a label whose sites are deep agrees.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField.Base

open Balaban Balaban.Multiscale Balaban.Localization Matrix

section Defect

variable {d L N₁ m₁ N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱ' : ℝ}

local notation "𝕋" => Torus d (N₁ * L ^ m₁ * L ^ 1)

theorem defPt_eq_sum (G : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ)
    (D : Matrix (G.Ω 1 × Fin N) (G.Ω 1 × Fin N) ℂ) (ψ : G.Ω 1 × Fin N → ℂ) (x : G.Ω 1) :
    defPt G D ψ x = ∑ i : Fin N, ψ (x, i) * (D *ᵥ ψ) (x, i) := by
  unfold defPt
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]

/-- **The defect at a site agrees on two generating sets** when the matrices (supported within `ρ` of the
row) and the fields correspond within `ρ` of the site. -/
theorem defPt_cross {Gl : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ} {Gp : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ'}
    (hΩp : ∀ z, z ∈ Gp.Ω 1) {ρ : ℕ} (Dl : Matrix (Gl.Ω 1 × Fin N) (Gl.Ω 1 × Fin N) ℂ)
    (Dp : Matrix (Gp.Ω 1 × Fin N) (Gp.Ω 1 × Fin N) ℂ) (ψl : Gl.Ω 1 × Fin N → ℂ) (ψp : Gp.Ω 1 × Fin N → ℂ)
    {x : Gl.Ω 1} {x' : Gp.Ω 1} (hxx : (x : 𝕋) = x')
    (hdeep : ∀ z : Gp.Ω 1, supDist (x : 𝕋) z ≤ ρ → (z : 𝕋) ∈ Gl.Ω 1)
    (hWl : ∀ i r, Dl (x, i) r ≠ 0 → supDist (x : 𝕋) r.1 ≤ ρ)
    (hWp : ∀ i r, Dp (x', i) r ≠ 0 → supDist (x' : 𝕋) r.1 ≤ ρ)
    (hWx : ∀ i (r : Gl.Ω 1 × Fin N) (r' : Gp.Ω 1 × Fin N), (r.1 : 𝕋) = r'.1 → r.2 = r'.2 →
      Dp (x', i) r' = Dl (x, i) r)
    (hψ : ∀ (r : Gl.Ω 1 × Fin N) (r' : Gp.Ω 1 × Fin N), (r.1 : 𝕋) = r'.1 → r.2 = r'.2 →
      supDist (x : 𝕋) r.1 ≤ ρ → ψp r' = ψl r)
    (hψx : ∀ i, ψp (x', i) = ψl (x, i)) :
    defPt Gp Dp ψp x' = defPt Gl Dl ψl x := by
  rw [defPt_eq_sum, defPt_eq_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hψx i, whiten_cross Gl Gp hΩp Dl Dp ψl ψp hxx i hdeep (hWl i) (hWp i) (hWx i) hψ]

/-- The label of the defect at `x` does not depend on the cover (the family of cells is empty). -/
theorem labelSet_empty_congr {k : ℕ} (C C' : DecCover d L N₁ m₁ (k + 1)) {m₀ : ℕ}
    (x : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) (r : ℕ) :
    labelSet C m₀ x r ∅ = labelSet C' m₀ x r ∅ := by
  unfold labelSet labelJ
  simp only [Finset.biUnion_empty]

open Classical in
/-- **The activity of a defect label agrees on two generating sets** when the label is deep. -/
theorem defTerm_cross {Gl : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ} {Gp : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ'}
    {m₀ : ℕ} (hN : L ^ m₀ ∣ N₁) (hΩp : ∀ z, z ∈ Gp.Ω 1) (rD : ℕ)
    (Dl : Matrix (Gl.Ω 1 × Fin N) (Gl.Ω 1 × Fin N) ℂ) (Dp : Matrix (Gp.Ω 1 × Fin N) (Gp.Ω 1 × Fin N) ℂ)
    (ψl : Gl.Ω 1 × Fin N → ℂ) (ψp : Gp.Ω 1 × Fin N → ℂ) (Y : Set 𝕋)
    (hdeep : ∀ z ∈ Y, z ∈ Gl.Ω 1)
    (hWl : ∀ (x : Gl.Ω 1) i r, Dl (x, i) r ≠ 0 → supDist (x : 𝕋) r.1 ≤ rD)
    (hWp : ∀ (x' : Gp.Ω 1) i r, Dp (x', i) r ≠ 0 → supDist (x' : 𝕋) r.1 ≤ rD)
    (hWx : ∀ (x : Gl.Ω 1) (x' : Gp.Ω 1), (x : 𝕋) = x' → (x : 𝕋) ∈ Y → ∀ i (r : Gl.Ω 1 × Fin N)
      (r' : Gp.Ω 1 × Fin N), (r.1 : 𝕋) = r'.1 → r.2 = r'.2 → Dp (x', i) r' = Dl (x, i) r)
    (hψ : ∀ (r : Gl.Ω 1 × Fin N) (r' : Gp.Ω 1 × Fin N), (r.1 : 𝕋) = r'.1 → r.2 = r'.2 →
      (r.1 : 𝕋) ∈ Y → ψp r' = ψl r) :
    defTerm Gp Dp m₀ rD Y ψp = defTerm Gl Dl m₀ rD Y ψl := by
  unfold defTerm
  have hlab : ∀ z : 𝕋, labelSet (coverOf Gp) m₀ z rD ∅ = labelSet (coverOf Gl) m₀ z rD ∅ :=
    fun z => labelSet_empty_congr _ _ z rD
  have hmemY : ∀ z : 𝕋, labelSet (coverOf Gl) m₀ z rD ∅ = Y → z ∈ Y := fun z h => by
    rw [← h]; exact seed_subset_labelSet hN (by rw [supDist_self]; exact Nat.zero_le _)
  have hval : ∀ a : Gl.Ω 1, (if labelSet (coverOf Gl) m₀ (a : 𝕋) rD ∅ = Y then defPt Gl Dl ψl a else 0) =
      (if labelSet (coverOf Gp) m₀ (⟨(a : 𝕋), hΩp a⟩ : Gp.Ω 1) rD ∅ = Y then
        defPt Gp Dp ψp ⟨(a : 𝕋), hΩp a⟩ else 0) := by
    intro a
    by_cases h : labelSet (coverOf Gl) m₀ (a : 𝕋) rD ∅ = Y
    · have h' : labelSet (coverOf Gp) m₀ (⟨(a : 𝕋), hΩp a⟩ : Gp.Ω 1) rD ∅ = Y := by
        show labelSet (coverOf Gp) m₀ (a : 𝕋) rD ∅ = Y
        rw [hlab]; exact h
      simp only [h, h', ↓reduceIte]
      have haY := hmemY _ h
      have hball : ∀ z : 𝕋, supDist (a : 𝕋) z ≤ rD → z ∈ Y := fun z hz => by
        rw [← h]; exact seed_subset_labelSet hN hz
      symm
      refine defPt_cross hΩp (ρ := rD) Dl Dp ψl ψp (x := a) (x' := ⟨(a : 𝕋), hΩp a⟩) rfl
        (fun z hz => hdeep _ (hball _ hz)) (fun i r hr => hWl a i r hr)
        (fun i r hr => hWp _ i r hr) (fun i r r' h1 h2 => hWx a _ rfl haY i r r' h1 h2)
        (fun r r' h1 h2 hr => hψ r r' h1 h2 (hball _ hr)) (fun i => hψ (a, i) _ rfl rfl haY)
    · have h' : ¬ labelSet (coverOf Gp) m₀ (⟨(a : 𝕋), hΩp a⟩ : Gp.Ω 1) rD ∅ = Y := by
        show ¬ labelSet (coverOf Gp) m₀ (a : 𝕋) rD ∅ = Y
        rw [hlab]; exact h
      simp only [h, h', ↓reduceIte]
  symm
  refine Finset.sum_bij_ne_zero (fun a _ _ => (⟨(a : 𝕋), hΩp a⟩ : Gp.Ω 1)) (fun _ _ _ => Finset.mem_univ _)
    (fun a _ _ b _ _ h => Subtype.ext (congrArg (fun q : Gp.Ω 1 => (q : 𝕋)) h)) (fun b _ hb => ?_)
    (fun a _ _ => hval a)
  have hlb : labelSet (coverOf Gp) m₀ (b : 𝕋) rD ∅ = Y := by
    by_contra h
    exact hb (by simp [h])
  have hbY : (b : 𝕋) ∈ Y := by
    rw [← hlb]; exact seed_subset_labelSet hN (by rw [supDist_self]; exact Nat.zero_le _)
  set a : Gl.Ω 1 := ⟨(b : 𝕋), hdeep _ hbY⟩ with ha
  have hab : (⟨(a : 𝕋), hΩp a⟩ : Gp.Ω 1) = b := Subtype.ext rfl
  refine ⟨a, Finset.mem_univ _, ?_, hab⟩
  rw [hval a, hab]
  exact hb

end Defect

end Balaban.LargeField.Base
