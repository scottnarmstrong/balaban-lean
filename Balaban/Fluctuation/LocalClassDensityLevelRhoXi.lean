/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Multiscale.WeakenSep
public import Balaban.SmallField.Def6v2Domain
public import Balaban.SmallField.LocalGeneratorSource

/-!
# The class domains do not see the separation index (`LocalClassDensityLevelRhoXi`)

A generating set of separation `ϱ'` is one of every smaller separation `ϱ ≤ ϱ'` with the same
domains (`GeneratingSet.weakenSep`).  The analyticity domains `Ξ^c_j(𝔹; σ, ε)` are built from the
domains of `𝔹` and from the background fields and multipliers they define, and none of these
involves the separation index:

* `Balaban.SmallField.xiAt_weaken`, `xiC_weakenSep`: `Ξ_n` and `Ξ^c_n` of the weakened set are those
  of the set;
* `Balaban.Localization.xiDom_weakenSep`, `xiFieldDom_dom_weakenSep`: the same for `Def6.XiDom` and
  the field domain `xiFieldDom`;
* `localB_eq_weakenSep`, `levelGS_eq_weakenSep`: the local sets and the whole-level sets at
  separation `ϱ ≤ minSep L (L ^ m₁)` are the weakenings of the ones at `minSep L (L ^ m₁)`.
-/

@[expose] public section

namespace Balaban.SmallField

open Balaban Balaban.Multiscale Balaban.Background

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ ϱ' : ℝ}
  (G : GeneratingSet d L N₀ k ϱ') (h : ϱ ≤ ϱ')

/-- The inequalities of `Ξ_n` do not depend on the separation index. -/
theorem xiBounds_weaken (ν : ℝ) (n : ℕ) (σ ε : ℝ) (D : BgData G N) (h₀ : Fin N → ℝ)
    (φ : G.Ω 1 × Fin N → ℂ) (α : G.Ω 1 → ℂ) :
    XiBounds (G.weakenSep h) ν n σ ε (D.weaken G h) h₀ φ α ↔ XiBounds G ν n σ ε D h₀ φ α :=
  ⟨fun H => ⟨H.grad, H.lap, H.mult, H.close, H.collarBond, H.mass, H.hnorm⟩,
   fun H => ⟨H.grad, H.lap, H.mult, H.close, H.collarBond, H.mass, H.hnorm⟩⟩

/-- The inequalities of `Ξ^c_n` do not depend on the separation index. -/
theorem xiCBounds_weaken (ν σ ε : ℝ) (Dr Dc : BgData G N)
    (Ψ'' h'' : Torus d (N₀ * L ^ k) → Fin N → ℂ)
    (φr φc : G.Ω 1 × Fin N → ℂ) (αr αc : G.Ω 1 → ℂ) :
    XiCBounds (G.weakenSep h) ν σ ε (Dr.weaken G h) (Dc.weaken G h) Ψ'' h'' φr φc αr αc ↔
      XiCBounds G ν σ ε Dr Dc Ψ'' h'' φr φc αr αc :=
  ⟨fun H => ⟨H.grad, H.lap, H.mult, H.val, H.close, H.collarBond, H.hAbs, H.hDot⟩,
   fun H => ⟨H.grad, H.lap, H.mult, H.val, H.close, H.collarBond, H.hAbs, H.hDot⟩⟩

/-- A datum of the weakened set realizes the same real data. -/
theorem xiAt_weaken (a : ℕ → ℝ) (ν : ℝ) (n : ℕ) (σ ε : ℝ) (D : BgData G N)
    (Ψ₀ : Torus d (N₀ * L ^ k) → Fin N → ℝ) (h₀ : Fin N → ℝ) :
    XiAt (G.weakenSep h) a ν n σ ε (D.weaken G h) Ψ₀ h₀ ↔ XiAt G a ν n σ ε D Ψ₀ h₀ := by
  unfold XiAt
  constructor
  · rintro ⟨h1, ⟨δ, hδ, hc, H⟩, h3⟩
    exact ⟨h1, ⟨δ, hδ, hc, (inDomainR_weaken G h ν δ D).1 H⟩, (xiBounds_weaken G h ..).1 h3⟩
  · rintro ⟨h1, ⟨δ, hδ, hc, H⟩, h3⟩
    exact ⟨h1, ⟨δ, hδ, hc, (inDomainR_weaken G h ν δ D).2 H⟩, (xiBounds_weaken G h ..).2 h3⟩

/-- **`Ξ^c_n(𝔹; 1, ε)` of the weakened set is that of the set.** -/
theorem xiC_weakenSep (a : ℕ → ℝ) (ν : ℝ) (n : ℕ) (σ ε : ℝ)
    (Ψ₀ : Torus d (N₀ * L ^ k) → Fin N → ℝ) (h₀ : Fin N → ℝ)
    (Ψ'' h'' : Torus d (N₀ * L ^ k) → Fin N → ℂ) :
    XiC (N := N) (G.weakenSep h) a ν n σ ε Ψ₀ h₀ Ψ'' h'' ↔ XiC G a ν n σ ε Ψ₀ h₀ Ψ'' h'' := by
  constructor
  · rintro ⟨hσ, hε, Dr, Dc, h1, h2, h3, h4⟩
    refine ⟨hσ, hε, Dr.unweaken G h, Dc.unweaken G h, ?_, h2,
      (inUnionDomainC_weakenSep G h _ _ ν Dc).1 h3, ?_⟩
    · exact (xiAt_weaken G h a ν n σ ε (Dr.unweaken G h) Ψ₀ h₀).1 h1
    · exact (xiCBounds_weaken G h ν σ ε (Dr.unweaken G h) (Dc.unweaken G h) Ψ'' h'' _ _ _ _).1 h4
  · rintro ⟨hσ, hε, Dr, Dc, h1, h2, h3, h4⟩
    refine ⟨hσ, hε, Dr.weaken G h, Dc.weaken G h, ?_, h2,
      (inUnionDomainC_weaken G h _ _ ν Dc).2 h3, ?_⟩
    · exact (xiAt_weaken G h a ν n σ ε Dr Ψ₀ h₀).2 h1
    · exact (xiCBounds_weaken G h ν σ ε Dr Dc Ψ'' h'' _ _ _ _).2 h4

end Balaban.SmallField

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.SmallField.Def6
  Balaban.SmallField.Def6v2 Balaban.SmallField.GsSpec Balaban.LargeField

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- `Def6.XiDom` of the weakened set is that of the set. -/
theorem xiDom_weakenSep (G : GeneratingSet d L (N₁ * L ^ m₁) k (minSep L (L ^ m₁)))
    (hsep : ϱ ≤ minSep L (L ^ m₁)) (a : ℕ → ℝ) (ν : ℝ) (j : ℕ) (ε : ℝ)
    (Ψ h : Fld d L N₁ m₁ k N) :
    XiDom (N := N) (G.weakenSep hsep) a ν j ε Ψ h ↔ XiDom G a ν j ε Ψ h := by
  unfold XiDom
  simp only [xiC_weakenSep]

/-- The local set at separation `ϱ ≤ minSep L (L ^ m₁)` is the weakening of the one at
`minSep L (L ^ m₁)`. -/
theorem localB_eq_weakenSep {j : ℕ} (hj : j ≤ k) (X : Set (CTorus d L N₁ m₁ k))
    (hsep : ϱ ≤ minSep L (L ^ m₁)) :
    localB j hj X hsep = (localB j hj X (le_refl (minSep L (L ^ m₁)))).weakenSep hsep := by
  unfold localB minimalGenSetAt
  rw [castG_weakenSep]
  rfl

/-- The whole-level set at separation `ϱ ≤ minSep L (L ^ m₁)` is the weakening of the one at
`minSep L (L ^ m₁)`. -/
theorem levelGS_eq_weakenSep {j : ℕ} (hj : j ≤ k) (hsep : ϱ ≤ minSep L (L ^ m₁)) :
    (levelGS (ϱ := ϱ) (N₁ := N₁) (m₁ := m₁) j hj : GeneratingSet d L (N₁ * L ^ m₁) k ϱ) =
      (levelGS (ϱ := minSep L (L ^ m₁)) (N₁ := N₁) (m₁ := m₁) j hj).weakenSep hsep := rfl
/-- The field domain `xiFieldDom` at separation `ϱ`, on a weakened set, is the one at
`minSep L (L ^ m₁)` on the set. -/
theorem xiFieldDom_dom_weakenSep (G : GeneratingSet d L (N₁ * L ^ m₁) k (minSep L (L ^ m₁)))
    (hsep : ϱ ≤ minSep L (L ^ m₁)) (a : ℕ → ℝ) (ν : ℝ) (ε : ℕ → ℝ) (j : ℕ)
    (Ψ h : Fld d L N₁ m₁ k N) :
    (xiFieldDom a ν ε : FieldDom d L N₁ m₁ k N ϱ).dom j (G.weakenSep hsep) Ψ h ↔
      (xiFieldDom a ν ε : FieldDom d L N₁ m₁ k N (minSep L (L ^ m₁))).dom j G Ψ h :=
  xiDom_weakenSep G hsep a ν j (ε j) Ψ h

end Balaban.Localization
