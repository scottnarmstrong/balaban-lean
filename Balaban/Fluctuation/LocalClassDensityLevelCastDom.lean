/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalClassDensityLevelCastSym
public import Balaban.Fluctuation.LocalClassDensityIrrelSuppSpec

/-!
# Chart domains and generating sets across the cast (`LocalClassDensityLevelCastDom`)

For `N₁' L ^ m₁' = N₁ L ^ m₁` and a generating set `G'` of the torus `(N₁', m₁')`, the set
`castG hc G'` lives on the torus `(N₁, m₁)`.  Its regions are the images of those of `G'`; the
complex domains `Ξ^c_j` of the two sets correspond under the cast of fields; the strong
specification of a polymer is transported; the whole-level sets correspond.
-/

@[expose] public section

namespace Balaban.SmallField

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField.GsSpec

variable {d L k N : ℕ} [NeZero L] {ϱ : ℝ}

/-- `Ξ^c_n` of the cast set is that of the set, read through the cast of the fields. -/
theorem xiC_castG {N₀' N₀ : ℕ} [NeZero N₀'] [NeZero N₀] (h : N₀' = N₀)
    (G : GeneratingSet d L N₀' k ϱ) (a : ℕ → ℝ) (ν : ℝ) (n : ℕ) (σ ε : ℝ)
    (Ψ₀ : Torus d (N₀ * L ^ k) → Fin N → ℝ) (h₀ : Fin N → ℝ)
    (Ψ'' h'' : Torus d (N₀ * L ^ k) → Fin N → ℂ) :
    XiC (N := N) (castG h G) a ν n σ ε Ψ₀ h₀ Ψ'' h'' ↔
      XiC (N := N) G a ν n σ ε
        (fun y => Ψ₀ (torusCast y : Torus d (N₀ * L ^ k))) h₀
        (fun y => Ψ'' (torusCast y : Torus d (N₀ * L ^ k)))
        (fun y => h'' (torusCast y : Torus d (N₀ * L ^ k))) := by
  subst h
  have e : ∀ y : Torus d (N₀' * L ^ k), (torusCast y : Torus d (N₀' * L ^ k)) = y := fun y => by
    funext μ; simp [torusCast]
  simp only [e]
  exact Iff.rfl

end Balaban.SmallField

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.SmallField.Def6v2 Balaban.SmallField.GsSpec

section Dom

variable {d L N₁ N₁' m₁ m₁' k N : ℕ} [NeZero L] [NeZero N₁] [NeZero N₁'] {ϱ : ℝ}

/-- A generating set is determined by its regions. -/
theorem generatingSet_eq_of_Ω {N₀ : ℕ} [NeZero N₀] {G G' : GeneratingSet d L N₀ k ϱ}
    (h : G.Ω = G'.Ω) : G = G' := by
  cases G
  cases G'
  simp only at h
  subst h
  rfl

theorem torusCast_eq_castT {a b : ℕ} [NeZero a] (h : a = b) (x : Torus d a) :
    (SmallField.GsSpec.torusCast x : Torus d b) = castT h x := by
  subst h
  funext μ
  simp [SmallField.GsSpec.torusCast, castT]

variable (hc : N₁' * L ^ m₁' = N₁ * L ^ m₁) {K : ℕ}
  {e : CTorus d L N₁' m₁' K ≃ CTorus d L N₁ m₁ K} (he : ∀ x, e x = castT (castSide_eq hc K) x)

include he

omit [NeZero N₁] in
theorem torusCast_eq_equiv (y : CTorus d L N₁' m₁' K) :
    (SmallField.GsSpec.torusCast y : CTorus d L N₁ m₁ K) = e y := by
  rw [he]
  exact torusCast_eq_castT _ y

theorem torusCast_eq_equiv_symm (x : CTorus d L N₁ m₁ K) :
    (SmallField.GsSpec.torusCast x : CTorus d L N₁' m₁' K) = e.symm x := by
  apply e.injective
  rw [Equiv.apply_symm_apply, ← torusCast_eq_equiv hc he]
  exact (SmallField.GsSpec.torusCast_torusCast (castSide_eq hc K).symm x)

/-- The complex domain of the cast set is that of the set, read through the cast of the fields. -/
theorem xiDom_castG_iff (G' : GeneratingSet d L (N₁' * L ^ m₁') K ϱ) (a : ℕ → ℝ) (ν : ℝ)
    (j : ℕ) (ε : ℝ) (Ψ h : Fld d L N₁ m₁ K N) :
    XiDom (N := N) (castG hc G') a ν j ε Ψ h ↔
      XiDom (N := N) G' a ν j ε (fun y => Ψ (e y)) (fun y => h (e y)) := by
  unfold XiDom
  constructor
  · rintro ⟨Ψ₀, h₀, Ψ'', h'', hΨ, hh, hx⟩
    refine ⟨fun y => Ψ₀ (e y), h₀, fun y => Ψ'' (e y), fun y => h'' (e y),
      fun x i => hΨ _ i, fun x i => hh _ i, ?_⟩
    have := (xiC_castG hc G' a ν j 1 ε Ψ₀ h₀ Ψ'' h'').1 hx
    simpa only [torusCast_eq_equiv hc he] using this
  · rintro ⟨Ψ₀, h₀, Ψ'', h'', hΨ, hh, hx⟩
    refine ⟨fun x => Ψ₀ (e.symm x), h₀, fun x => Ψ'' (e.symm x), fun x => h'' (e.symm x),
      fun x i => ?_, fun x i => ?_, ?_⟩
    · have := hΨ (e.symm x) i
      simpa using this
    · have := hh (e.symm x) i
      simpa using this
    · refine (xiC_castG hc G' a ν j 1 ε _ h₀ _ _).2 ?_
      simpa only [torusCast_eq_equiv hc he, Equiv.symm_apply_apply] using hx

/-- The field domain `xiFieldDom` of the cast set is that of the set. -/
theorem xiFieldDom_dom_castG_iff (G' : GeneratingSet d L (N₁' * L ^ m₁') K ϱ) (a : ℕ → ℝ)
    (ν : ℝ) (ε : ℕ → ℝ) (j : ℕ) (Ψ h : Fld d L N₁ m₁ K N) :
    (xiFieldDom a ν ε : FieldDom d L N₁ m₁ K N ϱ).dom j (castG hc G') Ψ h ↔
      (xiFieldDom a ν ε : FieldDom d L N₁' m₁' K N ϱ).dom j G'
        (fun y => Ψ (e y)) (fun y => h (e y)) :=
  xiDom_castG_iff hc he G' a ν j (ε j) Ψ h

theorem mem_castG_Ω_equiv (G' : GeneratingSet d L (N₁' * L ^ m₁') K ϱ) (i : ℕ)
    (x : CTorus d L N₁ m₁ K) :
    x ∈ (castG hc G').Ω i ↔ e.symm x ∈ G'.Ω i := by
  rw [mem_castG_Ω, torusCast_eq_equiv_symm hc he]

theorem castG_levelGS (j : ℕ) (hj : j ≤ K) :
    castG hc (levelGS (d := d) (ϱ := ϱ) (N₁ := N₁') (m₁ := m₁') j hj) =
      levelGS (d := d) (ϱ := ϱ) (N₁ := N₁) (m₁ := m₁) j hj := by
  apply generatingSet_eq_of_Ω
  funext i
  ext x
  rw [mem_castG_Ω_equiv hc he]
  by_cases hi : i ≤ j <;> simp [levelGS, hi]

theorem coe_castG_Ω_equiv (G' : GeneratingSet d L (N₁' * L ^ m₁') K ϱ) (i : ℕ) :
    (((castG hc G').Ω i : Finset (CTorus d L N₁ m₁ K)) : Set (CTorus d L N₁ m₁ K)) =
      e '' (((G'.Ω i : Finset (CTorus d L N₁' m₁' K))) : Set (CTorus d L N₁' m₁' K)) := by
  ext x
  rw [Finset.mem_coe, mem_castG_Ω_equiv hc he]
  constructor
  · intro h
    exact ⟨e.symm x, h, by simp⟩
  · rintro ⟨y, hy, rfl⟩
    simpa using hy

/-- The strong specification of a polymer is transported by the cast. -/
theorem gsSpecStrong_castG {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ K)
    {X' : Set (CTorus d L N₁' m₁' K)} {G' : GeneratingSet d L (N₁' * L ^ m₁') K ϱ}
    (H : GsSpecStrong j hjk X' G') : GsSpecStrong j hjk (e '' X') (castG hc G') := by
  refine GsSpecCore.toStrong hj1 hjk
    { subset := ?_
      noAbove := castG_noAbove hc H.noAbove
      topLayer := ?_ }
  · rintro _ ⟨x', hx', rfl⟩
    rw [Finset.mem_coe, mem_castG_Ω_equiv hc he, Equiv.symm_apply_apply]
    exact H.subset hx'
  · rintro _ ⟨x', hx', rfl⟩
    have h1 := H.topLayer x' hx'
    rw [GeneratingSet.mem_layer] at h1 ⊢
    rw [mem_castG_Ω_equiv hc he, mem_castG_Ω_equiv hc he, Equiv.symm_apply_apply]
    exact h1

end Dom

end Balaban.Fluctuation
