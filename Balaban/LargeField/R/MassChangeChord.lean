/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.ActionConvReal
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# The regional mass-change identity (WALL-COLLAR (1.1), INTERFACE-A (1.3))

For the same physical data `Dat` and the same action (mass `ν` in both evaluations), `φ⁰` a
hard-spin field and `φᵐ` a solution of the complete Euler-Lagrange system, on a region `D`:
`A_D(φ⁰) - A_D(φᵐ) = chord(w) + S_D(w̄, φ̄ᵐ)`, `w = φ⁰ - φᵐ`, the chord being the stationary
quadratic form `½⟨w,(H_ν+α)w⟩` with the half-bond regional pairings.  The proof specializes the
landed `actionRegion_conversion` (complete branch, `β = 1`, `b = e = 0`, same data).
-/

@[expose] public section

namespace Balaban.LargeField.ActionConv

open Balaban.Multiscale Balaban.Background Balaban.Fluctuation Finset

variable {d L N₀ K N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ K ϱ}

/-- The stationary quadratic chord on `D` of the difference `w = φ⁰ - φᵐ`:
`½⟨Qw, a Qw⟩_{D₁} + ½‖∂w̄‖²_{D*} + (ν/2)‖w‖²_D + ½⟨w, α w⟩_D`. -/
noncomputable def massChangeChord (D : Region G) (a : ℕ → ℝ) (ν : ℝ) (Dat : BgData G N)
    (φ0 φm : G.Ω 1 × Fin N → ℂ) (α : G.Ω 1 → ℂ) : ℂ :=
  (1 / 2) * D.blockPair a (fun x i => blockAvg G (φ0 - φm) x i)
      (fun x i => blockAvg G (φ0 - φm) x i) +
  (1 / 2) * D.bondPair (wExt Dat Dat φm φ0) (wExt Dat Dat φm φ0) +
  (1 / 2) * D.sitePair α (svec G (φ0 - φm)) (svec G (φ0 - φm)) +
  (ν : ℂ) / 2 * D.massPair (svec G (φ0 - φm)) (svec G (φ0 - φm))

theorem counterC_self (D : Region G) (a : ℕ → ℝ) (ν : ℝ) (Dat : BgData G N)
    (φ0 φm : G.Ω 1 × Fin N → ℂ) (α : G.Ω 1 → ℂ) :
    counterC D a ν 1 0 0 Dat Dat φm φ0 α MassBranch.complete =
      massChangeChord D a ν Dat φ0 φm α := by
  have hinc : dataInc Dat Dat = fun _ _ => 0 := by
    funext x i; simp [dataInc]
  have e1 : D.blockPair a (fun x i => dataInc Dat Dat x i - blockAvg G (φ0 - φm) x i)
      (fun x i => dataInc Dat Dat x i - blockAvg G (φ0 - φm) x i) =
      D.blockPair a (fun x i => blockAvg G (φ0 - φm) x i) (fun x i => blockAvg G (φ0 - φm) x i) := by
    unfold Region.blockPair
    refine Finset.sum_congr rfl fun x _ => ?_
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hinc]; ring
  have e2 : D.blockPair a (dataInc Dat Dat) (fun x i => Dat.Ψ x i - blockAvg G φm x i) = 0 := by
    unfold Region.blockPair
    rw [hinc]; simp
  unfold counterC counterP counterQ counterR massChangeChord
  rw [e1, e2]
  simp [MassBranch.ind]
  ring

/-- **The regional mass-change identity** (WALL-COLLAR (1.1), INTERFACE-A (1.3)).  Premises: `φᵐ`
solves the complete Euler-Lagrange system `(a, ν; Dat; α)` (which includes its hard-spin
constraint), `φ⁰` satisfies the hard-spin constraint. -/
theorem massChange_region_chord_with_star (D : Region G) {a : ℕ → ℝ} {ν : ℝ} {Dat : BgData G N}
    {φ0 φm : G.Ω 1 × Fin N → ℂ} {α : G.Ω 1 → ℂ} (hEL : IsEL G a ν Dat φm α)
    (hφ0 : ∀ x : G.Ω 1, ∑ i, φ0 (x, i) * φ0 (x, i) = 1) :
    actionRegionC D a ν Dat φ0 - actionRegionC D a ν Dat φm =
      massChangeChord D a ν Dat φ0 φm α +
        D.starPair (wExt Dat Dat φm φ0) (barField G Dat.Ψ φm) := by
  have h := actionRegion_conversion (G := G) D MassBranch.complete (a := a) (au := a) (ν := ν)
    (νu := ν) (β := 1) (b := 0) (e := 0) (Du := Dat) (Dat := Dat) (φ := φm) (φu := φ0) (α := α)
    one_ne_zero (fun n => by ring) (by ring) (fun _ _ => rfl) hEL hφ0
  rw [counterC_self] at h
  push_cast at h
  linear_combination h

/-- The same identity in the form `A_D(φ⁰) - A_D(φᵐ)` for `D` the whole torus: no flux. -/
theorem massChange_univ_chord (D : Region G) (hD : D.sites = Finset.univ) {a : ℕ → ℝ} {ν : ℝ}
    {Dat : BgData G N} {φ0 φm : G.Ω 1 × Fin N → ℂ} {α : G.Ω 1 → ℂ} (hEL : IsEL G a ν Dat φm α)
    (hφ0 : ∀ x : G.Ω 1, ∑ i, φ0 (x, i) * φ0 (x, i) = 1) :
    actionRegionC D a ν Dat φ0 - actionRegionC D a ν Dat φm =
      massChangeChord D a ν Dat φ0 φm α := by
  rw [massChange_region_chord_with_star D hEL hφ0, starPair_univ D hD, add_zero]

end Balaban.LargeField.ActionConv
