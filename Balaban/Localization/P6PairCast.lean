/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.P6PairOp
public import Balaban.Fluctuation.CubeActionRealStar
public import Balaban.Fluctuation.Theorem42CubesWire

/-!
# Transport of background data and fields along an equality of base sides (VMOD-11 row 8)

The real step (`Fluctuation.realStepAct`) lives on the torus `M₁ (c n) L^{k+1}`, the localization
layer on `(c n) L^{m₁} L^{k+1}`.  For `h : N₀ = N₀'` this file transports, along
`GeneratingSet.castN h`, the data `BgData` (`castBg`), the fields `G.Ω₁ × Fin N → ℂ` (`castφ`) and
the cube sets (`torusCast`), and proves that `InDomainC`, `bgFieldC`, `bgMultC`, `restrictφ` and
`cubeActionStar` commute with it.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.Multiscale.GeneratingSet
  Balaban.Fluctuation

set_option linter.unusedSectionVars false

variable {d L K N : ℕ} [NeZero L] {ϱ : ℝ}

/-- Transport of background data along `N₀ = N₀'`. -/
def castBg {N₀ N₀' : ℕ} [NeZero N₀] [NeZero N₀'] (h : N₀ = N₀') {G : GeneratingSet d L N₀ K ϱ}
    (D : BgData G N) : BgData (castN h G) N := by
  subst h; exact D

/-- Transport of a field `Ω₁ × Fin N → ℂ` along `N₀ = N₀'`. -/
def castφ {N₀ N₀' : ℕ} [NeZero N₀] [NeZero N₀'] (h : N₀ = N₀') {G : GeneratingSet d L N₀ K ϱ}
    (φ : G.Ω 1 × Fin N → ℂ) : (castN h G).Ω 1 × Fin N → ℂ := by
  subst h; exact φ

/-- Transport of a multiplier `Ω₁ → ℂ` along `N₀ = N₀'`. -/
def castα {N₀ N₀' : ℕ} [NeZero N₀] [NeZero N₀'] (h : N₀ = N₀') {G : GeneratingSet d L N₀ K ϱ}
    (α : G.Ω 1 → ℂ) : (castN h G).Ω 1 → ℂ := by
  subst h; exact α

/-- The torus equality `N₀ L^K = N₀' L^K` induced by `N₀ = N₀'`. -/
theorem castSide {N₀ N₀' : ℕ} (K : ℕ) (L : ℕ) (h : N₀ = N₀') : N₀ * L ^ K = N₀' * L ^ K := by
  rw [h]

/-- Transport of a cube set. -/
def castCube {N₀ N₀' : ℕ} (h : N₀ = N₀') (Q : Finset (Torus d (N₀ * L ^ K))) :
    Finset (Torus d (N₀' * L ^ K)) :=
  by classical exact Q.image (torusCast (castSide K L h))

theorem inDomainC_castBg {N₀ N₀' : ℕ} [NeZero N₀] [NeZero N₀'] (h : N₀ = N₀')
    {G : GeneratingSet d L N₀ K ϱ} {ν δ ε : ℝ} (D : BgData G N) :
    InDomainC (castN h G) ν δ ε (castBg h D) ↔ InDomainC G ν δ ε D := by
  subst h; exact Iff.rfl

theorem bgFieldC_castN {N₀ N₀' : ℕ} [NeZero N₀] [NeZero N₀'] (h : N₀ = N₀')
    {G : GeneratingSet d L N₀ K ϱ} (a : ℕ → ℝ) (ν c₀ : ℝ) (D : BgData G N) :
    bgFieldC (castN h G) a ν c₀ (castBg h D) = castφ h (bgFieldC G a ν c₀ D) := by
  subst h; rfl

theorem bgMultC_castN {N₀ N₀' : ℕ} [NeZero N₀] [NeZero N₀'] (h : N₀ = N₀')
    {G : GeneratingSet d L N₀ K ϱ} (a : ℕ → ℝ) (ν c₀ : ℝ) (D : BgData G N) :
    bgMultC (castN h G) a ν c₀ (castBg h D) = castα h (bgMultC G a ν c₀ D) := by
  subst h; rfl

theorem restrictφ_castN {N₀ N₀' : ℕ} [NeZero N₀] [NeZero N₀'] (h : N₀ = N₀') {ϱ' : ℝ}
    {G : GeneratingSet d L N₀ K ϱ} {G' : GeneratingSet d L N₀ K ϱ'} (hp : Precedes G G')
    (φ' : G'.Ω 1 × Fin N → ℂ) :
    (castN_precedes h hp).restrictφ (castφ h φ') = castφ h (hp.restrictφ φ') := by
  subst h; rfl

theorem castCube_rfl {N₀ : ℕ} (Q : Finset (Torus d (N₀ * L ^ K))) :
    castCube (rfl : N₀ = N₀) Q = Q := by
  classical
  unfold castCube
  exact Finset.image_id

theorem cubeActionStar_castN {N₀ N₀' : ℕ} [NeZero N₀] [NeZero N₀'] (h : N₀ = N₀')
    {G : GeneratingSet d L N₀ K ϱ} (a : ℕ → ℝ) (ν : ℝ) (Q : Finset (Torus d (N₀ * L ^ K)))
    (D : BgData G N) (φ : G.Ω 1 × Fin N → ℂ) :
    cubeActionStar (castN h G) a ν (castCube h Q) (castBg h D).Ψ (castBg h D).h (castφ h φ) =
      cubeActionStar G a ν Q D.Ψ D.h φ := by
  subst h
  rw [castCube_rfl]; rfl

end Balaban.Localization
