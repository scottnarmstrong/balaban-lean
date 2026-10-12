/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.I5Local
public import Balaban.Localization.Decoupled2SolveAnalytic
public import Balaban.Localization.Decoupled2FpField
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The fluctuation problem on `𝔹_k` with the background of `𝔹_{k+1}` (VMOD.md §3, P3 (4.41))

For the background datum `D` of `𝔹_{k+1}` (the generating set `Gp`), its decoupled background field
and multiplier `(φ, α)`, and the fluctuation `ψ'` (a perturbation `δΨ` of the data), the data of
Theorem I-4a (mode P) for the operator `H⁻` (the generating set `Hm`, `Hm ≺ Gp`) are

`(φ₀, α₀, δΨ, f₁) = (φ̄, α|_{Ω₁(Hm)}, ψ', 0)`,

with `φ̄ = barField Gp D.Ψ φ` the extension of `φ` by the datum (`flEdat`).  This file proves that
these data satisfy the strict inequalities `StrictDataM` of Theorem I-4a (b) from the bounds
`BgBounds` of Theorem I-4b (`flEdat_strict`).
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Finset Matrix

section Edat

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {Hm : GeneratingSet d L (N₁ * L ^ m₁) K ϱm}

variable (Gp Hm) in
open Classical in
/-- The multiplier of `𝔹_{k+1}` as a potential on `Ω₁(H⁻)` (`Ω₁(H⁻) ⊆ Ω₁(Gp)` for `H⁻ ≺ Gp`). -/
noncomputable def flAlpha (α : Gp.Ω 1 → ℂ) : Hm.Ω 1 → ℂ := fun y =>
  if h : (y : CTorus d L N₁ m₁ K) ∈ Gp.Ω 1 then α ⟨y, h⟩ else 0

variable (Gp Hm) in
/-- **The data of Theorem I-4a for the fluctuation problem** on `H⁻`: the background field of
`Gp` extended by the datum, the restriction of its multiplier, the fluctuation `ψ'` as `δΨ`, and
`f₁ = 0`. -/
noncomputable def flEdat (φα : (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ))
    (Ψ ψ' : CTorus d L N₁ m₁ K → Fin N → ℂ) : Edat Hm N :=
  (barField Gp Ψ φα.1, flAlpha Gp Hm φα.2, ψ', 0)

theorem flAlpha_of_prec (hPmp : Precedes Hm Gp) (α : Gp.Ω 1 → ℂ) (y : Hm.Ω 1) :
    flAlpha Gp Hm α y = α (hPmp.incl y) := by
  classical
  simp only [flAlpha, hPmp.mem_Ω1 y.2, ↓reduceDIte]
  rfl

theorem spacing_le_of_prec (hPmp : Precedes Hm Gp) {x : CTorus d L N₁ m₁ K} (hx : x ∈ Hm.Ω 1) :
    Hm.spacing x ≤ Gp.spacing x := by
  unfold GeneratingSet.spacing
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by have := NeZero.ne L; omega : 1 ≤ L)
  exact pow_le_pow_right₀ hL1 (hPmp.layerIndex_le hx)

theorem spacing_pos' (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) (x : CTorus d L N₁ m₁ K) :
    0 < G.spacing x := by
  unfold GeneratingSet.spacing
  have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  positivity

/-- **The strict inequalities of Theorem I-4a (b) for the fluctuation data.**  The bounds `BgBounds`
of the background field with the constant `B > 0` give `StrictDataM` with `δ₀ = 2B`, provided
`|φ| < 3/2` on `Ω₁` and `|ψ'| < δ₁` on the data sites of `H⁻`. -/
theorem flEdat_strict (hPmp : Precedes Hm Gp) {D : BgData Gp N} {φ : Gp.Ω 1 × Fin N → ℂ}
    {α : Gp.Ω 1 → ℂ} {B : ℝ} (hb : BgBounds Gp D φ α B) (hB : 0 < B)
    (hphi : ∀ x : Gp.Ω 1, vn (fun i => φ (x, i)) < 3 / 2) {δ₁ : ℝ} (hδ₁ : 0 < δ₁)
    {ψ' : CTorus d L N₁ m₁ K → Fin N → ℂ} (hψ : ∀ x ∈ dataSites Hm, vn (ψ' x) < δ₁) :
    StrictDataM Hm N false (2 * B) δ₁ (flEdat Gp Hm (φ, α) D.Ψ ψ') := by
  refine ⟨⟨fun x μ => ?_, fun x => ?_, fun x => ?_, fun x => ?_, fun x i => ?_, fun x => ?_⟩,
    fun h => absurd h (by simp)⟩
  · have hxp : (x : CTorus d L N₁ m₁ K) ∈ Gp.Ω 1 := hPmp.mem_Ω1 x.2
    obtain ⟨h1, h2⟩ := hb.grad ⟨x, hxp⟩ μ
    have hs := spacing_le_of_prec hPmp x.2
    have hp := spacing_pos' Hm (x : CTorus d L N₁ m₁ K)
    have hlt : B / Gp.spacing (x : CTorus d L N₁ m₁ K) < 2 * B / Hm.spacing (x : CTorus d L N₁ m₁ K) := by
      calc B / Gp.spacing (x : CTorus d L N₁ m₁ K) ≤ B / Hm.spacing (x : CTorus d L N₁ m₁ K) :=
            div_le_div_of_nonneg_left hB.le hp hs
        _ < 2 * B / Hm.spacing (x : CTorus d L N₁ m₁ K) := by
            apply div_lt_div_of_pos_right _ hp; linarith
    exact ⟨lt_of_le_of_lt h1 hlt, lt_of_le_of_lt h2 hlt⟩
  · have hxp : (x : CTorus d L N₁ m₁ K) ∈ Gp.Ω 1 := hPmp.mem_Ω1 x.2
    have h1 := hb.lap ⟨x, hxp⟩
    have hs := spacing_le_of_prec hPmp x.2
    have hp := spacing_pos' Hm (x : CTorus d L N₁ m₁ K)
    have hs2 : Hm.spacing (x : CTorus d L N₁ m₁ K) ^ 2 ≤ Gp.spacing (x : CTorus d L N₁ m₁ K) ^ 2 :=
      pow_le_pow_left₀ hp.le hs 2
    have hlt : B / Gp.spacing (x : CTorus d L N₁ m₁ K) ^ 2 < 2 * B / Hm.spacing (x : CTorus d L N₁ m₁ K) ^ 2 := by
      calc B / Gp.spacing (x : CTorus d L N₁ m₁ K) ^ 2 ≤ B / Hm.spacing (x : CTorus d L N₁ m₁ K) ^ 2 :=
            div_le_div_of_nonneg_left hB.le (by positivity) hs2
        _ < 2 * B / Hm.spacing (x : CTorus d L N₁ m₁ K) ^ 2 := by
            apply div_lt_div_of_pos_right _ (by positivity); linarith
    exact lt_of_le_of_lt h1 hlt
  · have hxp : (x : CTorus d L N₁ m₁ K) ∈ Gp.Ω 1 := hPmp.mem_Ω1 x.2
    have e : (flEdat Gp Hm (φ, α) D.Ψ ψ').1 (x : CTorus d L N₁ m₁ K) = fun i => φ (⟨x, hxp⟩, i) := by
      funext i
      simp [flEdat, barField, hxp]
    rw [e]
    exact hphi ⟨x, hxp⟩
  · have hxp : (x : CTorus d L N₁ m₁ K) ∈ Gp.Ω 1 := hPmp.mem_Ω1 x.2
    have e : (flEdat Gp Hm (φ, α) D.Ψ ψ').2.1 x = α ⟨x, hxp⟩ := by
      simp [flEdat, flAlpha, hxp]
    rw [e]
    have h1 := hb.alpha ⟨x, hxp⟩
    have hs := spacing_le_of_prec hPmp x.2
    have hp := spacing_pos' Hm (x : CTorus d L N₁ m₁ K)
    have hs2 : Hm.spacing (x : CTorus d L N₁ m₁ K) ^ 2 ≤ Gp.spacing (x : CTorus d L N₁ m₁ K) ^ 2 :=
      pow_le_pow_left₀ hp.le hs 2
    calc Hm.spacing (x : CTorus d L N₁ m₁ K) ^ 2 * ‖α ⟨x, hxp⟩‖
        ≤ Gp.spacing (x : CTorus d L N₁ m₁ K) ^ 2 * ‖α ⟨x, hxp⟩‖ :=
          mul_le_mul_of_nonneg_right hs2 (norm_nonneg _)
      _ ≤ B := h1
      _ < 2 * B := by linarith
  · have : (flEdat Gp Hm (φ, α) D.Ψ ψ').2.2.2 (x, i) = 0 := rfl
    rw [this, norm_zero, mul_zero]; exact hδ₁
  · exact hψ x x.2

end Edat

end Balaban.Localization
