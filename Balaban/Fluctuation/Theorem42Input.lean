/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.Theorem42Geom
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Theorem 4.2: the input of the decoupled response (FLUCTUATION.md §4.2, Steps 2-3)

The decoupled weighted response (Step 2; FLUCTUATION Lemma 4.1 for the decoupled solutions of
LOC I-4a/b, which needs the OPEN mixed-pair input OPEN-NC-MIXED / OPEN-H7-BG-MIXED) is packaged
as ONE structure, `DecoupledCubeResponse`.  It says that the cube action differences
`F_b(u, s) = β (A_{Q_b}(φ_new(u, s)) - A_{Q_b}(φ_old(u, s)))` of the decoupled backgrounds
(`s` the decoupling vector, one coordinate per cover cube `c i`)

* equal the undecoupled cube differences `act b u` at `s = 1` (`at_one`),
* are holomorphic in `(u, s)` on the data set `S` times the polydisc `|s_i| < e^{κ₁}`
  (`analytic`; Step 3 "I-4a/b and the affine composition make `F_□` holomorphic"),
* are bounded there by `C_b = C_F' β r_H² e^{-γ_w D_k}` (`bound`; Step 3), and
* are local in the sense of (AE) with respect to an agreement relation `Ag` (`local`).

`DecoupledCubeResponse.nonempty_zero` and `DecoupledCubeResponse.nonempty_of_undecoupled` show that
the structure is inhabited: for no background change, and for any `s`-independent family (the
undecoupled data), respectively.  What the open input adds to the undecoupled landed bound
(`h7_cube_step3`, `cubeDiff_step3_quadratic`) is exactly the `s`-dependence, uniformly on the
polydisc.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Multiscale Balaban.Analysis

section Input

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) (m₀ j : ℕ)
variable {ι : Type*} [DecidableEq ι] [Fintype ι] (c : ι → ℕ × CTorus d L N₁ m₁ K)
variable {U : Type*} [NormedAddCommGroup U] [NormedSpace ℂ U]

/-- **The decoupled weighted response (OPEN-NC-MIXED input of Theorem 4.2, Steps 2-3).**  For the
action cubes `X_b = box b (L a_j)`, `b ∈ 𝒬`, the decoupled cube action differences `F b u s`
(`u ∈ S` the complex H7 data, `s` the decoupling vector) are an analytic extension to the polydisc
`|s_i| < e^{κ₁}` of the undecoupled differences `act b u`, bounded by `Cb` and local with respect
to the agreement relation `Ag` (the hypothesis (AE)/(LOC I-5) of the localization expansion). -/
structure DecoupledCubeResponse (𝒬 : Finset (CTorus d L N₁ m₁ K)) (S : Set U) (κ₁ Cb : ℝ)
    (Ag : Finset ι → U → U → Prop) (act : CTorus d L N₁ m₁ K → U → ℂ)
    (F : CTorus d L N₁ m₁ K → U → (ι → ℂ) → ℂ) : Prop where
  at_one : ∀ b ∈ 𝒬, ∀ u ∈ S, F b u 1 = act b u
  analytic : ∀ b ∈ 𝒬, AnalyticOnNhd ℂ (fun p : U × (ι → ℂ) => F b p.1 p.2)
    (S ×ˢ polydisc (0 : ι → ℂ) (fun _ => Real.exp κ₁))
  bound : ∀ b ∈ 𝒬, ∀ u ∈ S, ∀ s ∈ polydisc (0 : ι → ℂ) (fun _ => Real.exp κ₁), ‖F b u s‖ ≤ Cb
  loc : ∀ b ∈ 𝒬, LocalityAEOn (Real.exp κ₁) S (fun i => Pset m₁ (c i))
    (compY c (X1 G m₀ j ({b} : Set (CTorus d L N₁ m₁ K)))) Ag (F b)

variable {G m₀ j c}

omit [DecidableEq ι] in
/-- The structure is inhabited when there is no background change (`act = 0`). -/
theorem DecoupledCubeResponse.nonempty_zero (𝒬 : Finset (CTorus d L N₁ m₁ K)) (S : Set U)
    (κ₁ : ℝ) (Ag : Finset ι → U → U → Prop) :
    Nonempty (DecoupledCubeResponse G m₀ j c 𝒬 S κ₁ 0 Ag (fun _ _ => 0) (fun _ _ _ => 0)) :=
  ⟨⟨fun _ _ _ _ => rfl, fun _ _ => analyticOnNhd_const, fun _ _ _ _ _ => by simp,
    fun _ _ C u u' _ _ s s' _ _ _ _ => rfl⟩⟩

omit [DecidableEq ι] in
/-- The structure is inhabited by every `s`-independent family: the undecoupled cube differences
`act` that are holomorphic on `S` and bounded by `Cb`, with the agreement relation "equal
action differences".  (The open input is the `s`-dependence of `F`.) -/
theorem DecoupledCubeResponse.nonempty_of_undecoupled (𝒬 : Finset (CTorus d L N₁ m₁ K))
    {S : Set U} (κ₁ Cb : ℝ) (act : CTorus d L N₁ m₁ K → U → ℂ)
    (hact : ∀ b ∈ 𝒬, AnalyticOnNhd ℂ (act b) S) (hbd : ∀ b ∈ 𝒬, ∀ u ∈ S, ‖act b u‖ ≤ Cb) :
    Nonempty (DecoupledCubeResponse G m₀ j c 𝒬 S κ₁ Cb
      (fun _ u u' => ∀ b ∈ 𝒬, act b u = act b u') act (fun b u _ => act b u)) := by
  refine ⟨⟨fun _ _ _ _ => rfl, fun b hb => ?_, fun b hb u hu _ _ => hbd b hb u hu,
    fun b hb C u u' hu hu' s s' _ _ _ hag => hag b hb⟩⟩
  exact (hact b hb).comp (fun _ _ => analyticAt_fst) (fun p hp => hp.1)

end Input

end Balaban.Fluctuation
