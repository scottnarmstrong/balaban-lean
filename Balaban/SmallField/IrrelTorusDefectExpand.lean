/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, GPT-6-Sol
-/
module

public import Balaban.SmallField.IrrelTorus

/-!
# The filed part of the torus irrelevant term

The expanded identity exposes the local relevant term and its sum over all polymers at the
distinguished cube. The local `let` binders preserve the exact formula of `irrelTorus`.
-/

@[expose] public section

namespace Balaban.SmallField.Def6v2

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
  Balaban.SmallField.Def6 Finset

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

open Classical in
/-- The formula of `irrelTorus`, with the resummed filed term named locally. -/
theorem irrelTorus_eq_expanded_filed (m₀ : ℕ) (Tm : Terms d L N₁ m₁ k N ϱ)
    (i₀ i₁ : Fin N) (j : ℕ) (y : CTorus d L N₁ m₁ k)
    (X : Set (CTorus d L N₁ m₁ k)) (Ψ h : Fld d L N₁ m₁ k N) :
    irrelTorus m₀ Tm i₀ i₁ j y X Ψ h =
      (let e : Fld d L N₁ m₁ k N := constFld (Pi.single i₀ 1)
       let blk : Set (CTorus d L N₁ m₁ k) → Finset (CTorus d L N₁ m₁ k) := fun Z =>
         Finset.univ.filter fun x => Aligned (L ^ j) x ∧ x ∈ Z
       let u : ℂ := sqrtC (dot (Ψ y) (Ψ y))
       let dΨ : Fin d → Fin N → ℂ := fun μ =>
         Ψ (y + (L ^ j) • (Pi.single μ 1 : CTorus d L N₁ m₁ k)) - Ψ y
       let g : Fin d → Fin d → ℂ := fun μ μ' =>
         dot (dΨ μ) (dΨ μ') - dot (Ψ y) (dΨ μ) * dot (Ψ y) (dΨ μ') /
           dot (Ψ y) (Ψ y)
       let lift : CTorus d L N₁ m₁ k → Fin d → ℂ := fun z μ =>
         ((unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (z - y) μ : ℤ) : ℂ)
       let a : Set (CTorus d L N₁ m₁ k) → CTorus d L N₁ m₁ k → ℂ := fun Z x =>
         fderiv ℂ (fun Ψ' => Tm.E j y Z Ψ' e) e (blockDir L j x i₀)
       let TΦ : Set (CTorus d L N₁ m₁ k) → ℂ := fun Z =>
         Tm.E j y Z e e + (u - 1) * ∑ x ∈ blk Z, a Z x
           + (dot (Ψ y) (h y) / u - 1) *
             fderiv ℂ (fun h' => Tm.E j y Z e h') e e
           - (1 / 4 : ℂ) * ∑ μ, ∑ μ', g μ μ' * ∑ x ∈ blk Z, ∑ x' ∈ blk Z,
               D2 (fun Ψ' => Tm.E j y Z Ψ' e) e (blockDir L j x i₁)
                 (blockDir L j x' i₁) *
                 ((lift x μ - lift x' μ) * (lift x μ' - lift x' μ'))
       let R : ℂ := ∑ᶠ Z ∈ polysAt m₀ j y, TΦ Z
       Tm.E j y X Ψ h - TΦ X
         - (1 / 2 : ℂ) * ∑ x ∈ blk X, a X x *
             (dot (Ψ x) (Ψ x) - dot (Ψ y) (Ψ y))
         + if X = box (cbase (cellSide L m₀ m₁ j) y -
             natT fun _ => L / 2 * cellSide L m₀ m₁ j)
             (L * cellSide L m₀ m₁ j) then R else 0) := by
  rfl

end Balaban.SmallField.Def6v2
