/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.ActionConvGreen
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp

/-!
# The regional conversion identity (P6 (2.31); P631 (4))

`actionRegion_conversion`: for the restricted hard-spin action `A_D` of `ActionConvDef`,
`β_u A_D(a_u, ν_u; θ, φ_u) = β A_D(a, ν; ψ, φ) + β C_D + β_u S_D(w, φ)` in both mass branches.
The hypotheses are the source premises: the coefficient identities, `β ≠ 0`, the common `h`, the
Euler-Lagrange system of the base background (the one used by the proof), the hard-spin constraint of
`φ_u`.  The identity is a finite sum identity: it needs no estimate and no limit.
-/

@[expose] public section

namespace Balaban.LargeField.ActionConv

open Balaban.Multiscale Balaban.Background Balaban.Fluctuation Finset

variable {d L N₀ K N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ K ϱ}

namespace Region

theorem blockPair_sq_add (D : Region G) (a : ℕ → ℝ) (p q : Torus d (N₀ * L ^ K) → Fin N → ℂ) :
    D.blockPair a (fun x i => p x i + q x i) (fun x i => p x i + q x i) =
      D.blockPair a p p + 2 * D.blockPair a q p + D.blockPair a q q := by
  unfold blockPair
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ => ?_
  ring

theorem blockPair_sub_left (D : Region G) (a : ℕ → ℝ) (p q r : Torus d (N₀ * L ^ K) → Fin N → ℂ) :
    D.blockPair a (fun x i => p x i - q x i) r = D.blockPair a p r - D.blockPair a q r := by
  unfold blockPair
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ => ?_
  ring

theorem bondPair_sq_add (D : Region G) (f g : Torus d (N₀ * L ^ K) → Fin N → ℂ) :
    D.bondPair (fun x i => f x i + g x i) (fun x i => f x i + g x i) =
      D.bondPair f f + 2 * D.bondPair g f + D.bondPair g g := by
  unfold bondPair
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun μ _ =>
    Finset.sum_congr rfl fun i _ => ?_
  ring

theorem massPair_sq_add (D : Region G) (p q : Torus d (N₀ * L ^ K) → Fin N → ℂ) :
    D.massPair (fun x i => p x i + q x i) (fun x i => p x i + q x i) =
      D.massPair p p + 2 * D.massPair q p + D.massPair q q := by
  unfold massPair
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ => ?_
  ring

theorem massPair_add_right (D : Region G) (w p q : Torus d (N₀ * L ^ K) → Fin N → ℂ) :
    D.massPair w (fun x i => p x i + q x i) = D.massPair w p + D.massPair w q := by
  unfold massPair
  simp only [mul_add, Finset.sum_add_distrib]

/-- The coefficient identity `β_u a_u = β a` transfers to the restricted block pairing. -/
theorem blockPair_scale (D : Region G) {a au : ℕ → ℝ} {β b : ℝ}
    (ha : ∀ n, (β + b) * au n = β * a n) (p q : Torus d (N₀ * L ^ K) → Fin N → ℂ) :
    ((β + b : ℝ) : ℂ) * D.blockPair au p q = (β : ℂ) * D.blockPair a p q := by
  unfold blockPair
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  have h : ((β + b : ℝ) : ℂ) * levelCoeff G au x = (β : ℂ) * levelCoeff G a x := by
    unfold levelCoeff
    have := ha (G.layerIndex x)
    have hc : (((β + b) * (au (G.layerIndex x) / ((L : ℝ) ^ G.layerIndex x) ^ 2) : ℝ) : ℂ) =
        ((β * (a (G.layerIndex x) / ((L : ℝ) ^ G.layerIndex x) ^ 2) : ℝ) : ℂ) := by
      congr 1
      rw [← mul_div_assoc, this, mul_div_assoc]
    push_cast at hc ⊢
    exact hc
  linear_combination (∑ i, p x i * q x i) * h

end Region

theorem svec_diff (φ φu : G.Ω 1 × Fin N → ℂ) (x : Torus d (N₀ * L ^ K)) (i : Fin N) :
    svec G φu x i = svec G φ x i + svec G (φu - φ) x i := by
  have := svec_add (G := G) φ (φu - φ) x i
  rw [add_sub_cancel] at this
  exact this

theorem blockAvg_diff (φ φu : G.Ω 1 × Fin N → ℂ) (x : Torus d (N₀ * L ^ K)) (i : Fin N) :
    blockAvg G φu x i = blockAvg G φ x i + blockAvg G (φu - φ) x i := by
  have := blockAvg_add (G := G) φ (φu - φ) x i
  rw [add_sub_cancel] at this
  exact this

theorem wExt_of_mem (Dat Du : BgData G N) (φ φu : G.Ω 1 × Fin N → ℂ)
    {x : Torus d (N₀ * L ^ K)} (hx : x ∈ G.Ω 1) (i : Fin N) :
    wExt Dat Du φ φu x i = svec G (φu - φ) x i := by
  have h1 : barField G Du.Ψ φu x i = φu (⟨x, hx⟩, i) := by simp [barField, hx]
  have h2 : barField G Dat.Ψ φ x i = φ (⟨x, hx⟩, i) := by simp [barField, hx]
  have h3 := svec_of_mem G (φu - φ) ⟨x, hx⟩ i
  simp only [wExt, h1, h2]
  rw [show svec G (φu - φ) x i = (φu - φ) (⟨x, hx⟩, i) from h3]
  rfl

theorem massPair_wExt (D : Region G) (Dat Du : BgData G N) (φ φu : G.Ω 1 × Fin N → ℂ)
    (f : Torus d (N₀ * L ^ K) → Fin N → ℂ) :
    D.massPair (wExt Dat Du φ φu) f = D.massPair (svec G (φu - φ)) f := by
  unfold Region.massPair
  refine Finset.sum_congr rfl fun x hx => ?_
  simp only [wExt_of_mem Dat Du φ φu (D.sub_Ω hx)]

/-- The Euler-Lagrange equation summed against `w` over `D`. -/
theorem massPair_bulkDiv (D : Region G) {a : ℕ → ℝ} {ν : ℝ} {Dat : BgData G N}
    {φ : G.Ω 1 × Fin N → ℂ} {α : G.Ω 1 → ℂ} (h : IsEL G a ν Dat φ α)
    (w : Torus d (N₀ * L ^ K) → Fin N → ℂ) :
    D.massPair w (bulkDiv Dat φ) =
      D.blockPair a w (fun x i => Dat.Ψ x i - blockAvg G φ x i) -
        (ν : ℂ) * D.massPair w (fun x i => svec G φ x i - Dat.h x i) -
        D.massPair w (fun x i => zeroExt (G.Ω 1) α x * svec G φ x i) := by
  unfold Region.massPair Region.blockPair
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun i _ => ?_
  rw [bulkDiv_of_isEL h (D.sub_Ω hx)]
  ring

/-- The hard-spin constraints, summed over `D`: `⟨w, α w⟩_D = -2 ⟨w, α φ⟩_D`. -/
theorem sitePair_hardspin (D : Region G) (α : G.Ω 1 → ℂ) {φ φu : G.Ω 1 × Fin N → ℂ}
    (hφ : ∀ x : G.Ω 1, ∑ i, φ (x, i) * φ (x, i) = 1)
    (hφu : ∀ x : G.Ω 1, ∑ i, φu (x, i) * φu (x, i) = 1) :
    D.sitePair α (svec G (φu - φ)) (svec G (φu - φ)) =
      -2 * D.massPair (svec G (φu - φ)) (fun x i => zeroExt (G.Ω 1) α x * svec G φ x i) := by
  unfold Region.sitePair Region.massPair
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hx1 := D.sub_Ω hx
  have h := hardspin_diff hφ hφu ⟨x, hx1⟩
  have e1 : ∀ i, svec G (φu - φ) x i = (φu - φ) (⟨x, hx1⟩, i) := fun i =>
    svec_of_mem G (φu - φ) ⟨x, hx1⟩ i
  have e2 : ∀ i, svec G φ x i = φ (⟨x, hx1⟩, i) := fun i => svec_of_mem G φ ⟨x, hx1⟩ i
  simp only [e1, e2]
  have : ∑ i, (φu - φ) (⟨x, hx1⟩, i) * (zeroExt (G.Ω 1) α x * φ (⟨x, hx1⟩, i)) =
      zeroExt (G.Ω 1) α x * ∑ i, (φu - φ) (⟨x, hx1⟩, i) * φ (⟨x, hx1⟩, i) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [this]
  linear_combination (zeroExt (G.Ω 1) α x) * h

/-- **The regional conversion identity** (P6 (2.31), P631 (4)):
`β_u A_D(a_u, ν_u; θ, φ_u) = β A_D(a, ν; ψ, φ) + β C_D + β_u S_D(w, φ)`, `w = φ_u - φ`,
`β_u = β + b`, `β_u a_u = β a`, `β_u ν_u = β ν + ν e`; in both mass branches.  Hypotheses: the
coefficient identities, `β ≠ 0`, the common `h`, the Euler-Lagrange system of the base background
`(ψ, φ, α)` in the mass convention of the branch, and the hard-spin constraint of `φ_u`. -/
theorem actionRegion_conversion (D : Region G) (br : MassBranch) {a au : ℕ → ℝ}
    {ν νu β b e : ℝ} {Dat Du : BgData G N} {φ φu : G.Ω 1 × Fin N → ℂ} {α : G.Ω 1 → ℂ}
    (hβ : β ≠ 0) (ha : ∀ n, (β + b) * au n = β * a n) (hν : (β + b) * νu = β * ν + ν * e)
    (hh : ∀ x i, Du.h x i = Dat.h x i) (hEL : IsEL G a (br.elMass ν) Dat φ α)
    (hφu : ∀ x : G.Ω 1, ∑ i, φu (x, i) * φu (x, i) = 1) :
    ((β + b : ℝ) : ℂ) * actionRegionC D au νu Du φu =
      (β : ℂ) * actionRegionC D a ν Dat φ + (β : ℂ) * counterC D a ν β b e Dat Du φ φu α br +
        ((β + b : ℝ) : ℂ) * D.starPair (wExt Dat Du φ φu) (barField G Dat.Ψ φ) := by
  have hβc : (β : ℂ) ≠ 0 := by exact_mod_cast hβ
  -- the decompositions of the converted arguments
  have eU : (fun x i => Du.Ψ x i - blockAvg G φu x i) =
      fun x i => (Dat.Ψ x i - blockAvg G φ x i) +
        (dataInc Dat Du x i - blockAvg G (φu - φ) x i) := by
    funext x i
    rw [blockAvg_diff φ φu x i]
    unfold dataInc
    ring
  have eB : barField G Du.Ψ φu =
      fun x i => barField G Dat.Ψ φ x i + wExt Dat Du φ φu x i := by
    funext x i
    unfold wExt
    ring
  have eM : (fun x i => svec G φu x i - Du.h x i) =
      fun x i => (svec G φ x i - Dat.h x i) + svec G (φu - φ) x i := by
    funext x i
    rw [hh x i, svec_diff φ φu x i]
    ring
  -- block-constancy of `ψ - Qφ`
  have hg : ∀ i, ∀ x ∈ G.Ω 1, ∀ y ∈ G.blk (G.layerIndex x) x,
      (fun x i => Dat.Ψ x i - blockAvg G φ x i) y i =
        (fun x i => Dat.Ψ x i - blockAvg G φ x i) x i := by
    intro i x hx y hy
    obtain ⟨hn1, hnk, hxl⟩ := G.layerIndex_spec hx
    simp only [Dat.Ψ_layerConst (G.layerIndex x) hn1 hnk x hxl y hy,
      blockAvg_blockConst φ i x hx y hy]
  have hQu := Region.blockPair_blockAvg D a (φu - φ) (fun x i => Dat.Ψ x i - blockAvg G φ x i) hg
  have hsub := Region.blockPair_sub_left D a (dataInc Dat Du)
    (fun x i => blockAvg G (φu - φ) x i) (fun x i => Dat.Ψ x i - blockAvg G φ x i)
  have hgreen : D.bondPair (wExt Dat Du φ φu) (barField G Dat.Ψ φ) =
      D.massPair (svec G (φu - φ)) (bulkDiv Dat φ) +
        D.starPair (wExt Dat Du φ φu) (barField G Dat.Ψ φ) := by
    have := Region.bondPair_green D (wExt Dat Du φ φu) (barField G Dat.Ψ φ)
    rw [massPair_wExt] at this
    exact this
  have hELs := massPair_bulkDiv D hEL (svec G (φu - φ))
  have hcons := sitePair_hardspin D α (fun x => hEL.2 x) hφu
  have hRadd := Region.massPair_add_right D (svec G (φu - φ)) (bulkDiv Dat φ)
    (fun x i => zeroExt (G.Ω 1) α x * svec G φ x i)
  have hs1 := Region.blockPair_scale D ha (fun x i => Dat.Ψ x i - blockAvg G φ x i)
    (fun x i => Dat.Ψ x i - blockAvg G φ x i)
  have hs2 := Region.blockPair_scale D ha (fun x i => dataInc Dat Du x i - blockAvg G (φu - φ) x i)
    (fun x i => Dat.Ψ x i - blockAvg G φ x i)
  have hs3 := Region.blockPair_scale D ha (fun x i => dataInc Dat Du x i - blockAvg G (φu - φ) x i)
    (fun x i => dataInc Dat Du x i - blockAvg G (φu - φ) x i)
  have hνc : ((β + b : ℝ) : ℂ) * (νu : ℂ) = (β : ℂ) * ν + ν * e := by exact_mod_cast hν
  have hc1 : (β : ℂ) * ((b / (2 * β) : ℝ) : ℂ) = (b : ℂ) / 2 := by push_cast; field_simp
  have hc2 : (β : ℂ) * ((ν * e / (2 * β) : ℝ) : ℂ) = (ν : ℂ) * e / 2 := by push_cast; field_simp
  have hc3 : (β : ℂ) * ((1 + b / β : ℝ) : ℂ) = β + b := by push_cast; field_simp
  have hc4 : (β : ℂ) * ((1 + e / β : ℝ) : ℂ) = β + e := by push_cast; field_simp
  have hc5 : (β : ℂ) * ((b / β : ℝ) : ℂ) = b := by push_cast; field_simp
  have hc6 : (β : ℂ) * ((ν * e / β : ℝ) : ℂ) = ν * e := by push_cast; field_simp
  unfold actionRegionC counterC counterP counterQ counterR
  rw [eU, eB, eM, Region.blockPair_sq_add, Region.bondPair_sq_add, Region.massPair_sq_add]
  generalize ((b / (2 * β) : ℝ) : ℂ) = c1 at *
  generalize ((ν * e / (2 * β) : ℝ) : ℂ) = c2 at *
  generalize ((1 + b / β : ℝ) : ℂ) = c3 at *
  generalize ((1 + e / β : ℝ) : ℂ) = c4 at *
  generalize ((b / β : ℝ) : ℂ) = c5 at *
  generalize ((ν * e / β : ℝ) : ℂ) = c6 at *
  push_cast at *
  set u : Torus d (N₀ * L ^ K) → Fin N → ℂ := fun x i => Dat.Ψ x i - blockAvg G φ x i with hu
  set δ : Torus d (N₀ * L ^ K) → Fin N → ℂ :=
    fun x i => dataInc Dat Du x i - blockAvg G (φu - φ) x i with hδ
  set Mφφ := D.massPair (fun x i => svec G φ x i - Dat.h x i) (fun x i => svec G φ x i - Dat.h x i)
    with hMφφ
  set MWφ := D.massPair (svec G (φu - φ)) (fun x i => svec G φ x i - Dat.h x i) with hMWφ
  set MWW := D.massPair (svec G (φu - φ)) (svec G (φu - φ)) with hMWW
  set Rsum := D.massPair (svec G (φu - φ))
    (fun x i => bulkDiv Dat φ x i + zeroExt (G.Ω 1) α x * svec G φ x i) with hRsum
  set Div := D.massPair (svec G (φu - φ)) (bulkDiv Dat φ) with hDiv
  set WzΦ := D.massPair (svec G (φu - φ))
    (fun x i => zeroExt (G.Ω 1) α x * svec G φ x i) with hWzΦ
  set Bφφ := D.bondPair (barField G Dat.Ψ φ) (barField G Dat.Ψ φ) with hBφφ
  set BwΦ := D.bondPair (wExt Dat Du φ φu) (barField G Dat.Ψ φ) with hBwΦ
  set Bww := D.bondPair (wExt Dat Du φ φu) (wExt Dat Du φ φu) with hBww
  set Sα := D.sitePair α (svec G (φu - φ)) (svec G (φu - φ)) with hSα
  set S := D.starPair (wExt Dat Du φ φu) (barField G Dat.Ψ φ) with hS
  set BQu := D.blockPair a (fun x i => blockAvg G (φu - φ) x i) u with hBQu
  set BWu := D.blockPair a (svec G (φu - φ)) u with hBWu
  set Bdu := D.blockPair a (dataInc Dat Du) u with hBdu
  cases br
  · simp only [MassBranch.elMass, MassBranch.ind] at *
    push_cast at *
    linear_combination (1 / 2 : ℂ) * hs1 + hs2 + (1 / 2 : ℂ) * hs3 +
      (Mφφ / 2 + MWφ + MWW / 2) * hνc - Bφφ * hc1 - Mφφ * hc2 - (Bww + Sα) / 2 * hc3 -
      (ν / 2 * MWW) * hc4 - Rsum * hc5 - MWφ * hc6 - (b : ℂ) * hRadd + (β : ℂ) * hsub -
      (β : ℂ) * hQu + ((β : ℂ) + b) * hgreen + (β : ℂ) * hELs - ((β : ℂ) + b) / 2 * hcons
  · simp only [MassBranch.elMass, MassBranch.ind] at *
    push_cast at *
    linear_combination (1 / 2 : ℂ) * hs1 + hs2 + (1 / 2 : ℂ) * hs3 +
      (Mφφ / 2 + MWφ + MWW / 2) * hνc - Bφφ * hc1 - Mφφ * hc2 - (Bww + Sα) / 2 * hc3 -
      (ν / 2 * MWW) * hc4 - Rsum * hc5 - MWφ * hc6 - (b : ℂ) * hRadd + (β : ℂ) * hsub -
      (β : ℂ) * hQu + ((β : ℂ) + b) * hgreen + (β : ℂ) * hELs - ((β : ℂ) + b) / 2 * hcons

end Balaban.LargeField.ActionConv
