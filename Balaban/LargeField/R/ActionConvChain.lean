/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.ActionConvAdd
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# The chain of one-step conversions (P631 §3, proof of (8)-(10), first half)

For a fixed step `j` of the window, `ConvChain` is the typing data of the successive conversions
of the scale-`(j+1)` action to the coefficients of scales `j+2, …, k`, all on one generating set `G`
and one region `X = X_j`, with the spin data kept: coefficient sets `(β_n, a_n, ν_n)`, data
`(ψ_n, h)` and backgrounds `(φ_n, α_n)`, depending on the point `u` of a parameter domain `S`.  The
premises are exactly those of the one-step identity `actionRegion_conversion` for the steps
`n - 1 → n` (`j + 2 ≤ n ≤ k`): the coefficient identities, the common `h`, the Euler-Lagrange system
of the converted background `n` and the hard-spin constraint of the background `n - 1`.

* `ConvChain.T u n = β_n A_X(a_n, ν_n; ψ_n, φ_n)`: the action after conversion through scale `n`
  (`T_{j,n}` of P631 §3);  `ConvChain.cost u n`: the cost `R_{j,n} = β_n C_X + β_{n-1} S_X` of the
  step `n - 1 → n`;
* `ConvChain.telescope`: `T_{j,j+1} = T_{j,m} + ∑_{n=j+2}^{m} R_{j,n}` (exact), from P631 (4).
-/

@[expose] public section

namespace Balaban.LargeField.ActionConv

open Balaban.Multiscale Balaban.Background Balaban.Fluctuation Finset

variable {d L N₀ K N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- The typing data and source premises of the chain of conversions of the step `j` to scale `k`. -/
structure ConvChain {U : Type*} (S : Set U) (j k : ℕ) (G : GeneratingSet d L N₀ K ϱ)
    (X : Region G) (br : MassBranch) (N : ℕ) where
  /-- The couplings `β_n`. -/
  β : ℕ → ℝ
  /-- The layer-coefficient sequences `a_n`. -/
  a : ℕ → ℕ → ℝ
  /-- The masses `ν_n`. -/
  ν : ℕ → ℝ
  /-- The mass-change parameters `e_n`: `β_{n-1} ν_{n-1} = β_n ν_n + ν_n e_n`. -/
  e : ℕ → ℝ
  /-- The data `(ψ_n, h)` at the point `u`. -/
  Dat : U → ℕ → BgData G N
  /-- The backgrounds `φ_n`. -/
  φ : U → ℕ → G.Ω 1 × Fin N → ℂ
  /-- The multipliers `α_n`. -/
  α : U → ℕ → G.Ω 1 → ℂ
  β_ne : ∀ n, j + 1 ≤ n → n ≤ k → β n ≠ 0
  coeff : ∀ n, j + 2 ≤ n → n ≤ k → ∀ m, β (n - 1) * a (n - 1) m = β n * a n m
  mass : ∀ n, j + 2 ≤ n → n ≤ k → β (n - 1) * ν (n - 1) = β n * ν n + ν n * e n
  same_h : ∀ n, j + 2 ≤ n → n ≤ k → ∀ u ∈ S, ∀ x i, (Dat u (n - 1)).h x i = (Dat u n).h x i
  el : ∀ n, j + 2 ≤ n → n ≤ k → ∀ u ∈ S,
    IsEL G (a n) (br.elMass (ν n)) (Dat u n) (φ u n) (α u n)
  unit : ∀ n, j + 2 ≤ n → n ≤ k → ∀ u ∈ S, ∀ x : G.Ω 1, ∑ i, φ u (n - 1) (x, i) * φ u (n - 1) (x, i) = 1

namespace ConvChain

variable {U : Type*} {S : Set U} {j k : ℕ} {G : GeneratingSet d L N₀ K ϱ} {X : Region G}
  {br : MassBranch} (C : ConvChain S j k G X br N)

/-- `T_{j,n}`: the action `β_n A_X(a_n, ν_n; ψ_n, φ_n)` after conversion through scale `n`. -/
noncomputable def T (u : U) (n : ℕ) : ℂ :=
  (C.β n : ℂ) * actionRegionC X (C.a n) (C.ν n) (C.Dat u n) (C.φ u n)

/-- `R_{j,n}`: the cost `β_n C_X + β_{n-1} S_X` of the conversion step `n - 1 → n`. -/
noncomputable def cost (u : U) (n : ℕ) : ℂ :=
  (C.β n : ℂ) * counterC X (C.a n) (C.ν n) (C.β n) (C.β (n - 1) - C.β n) (C.e n) (C.Dat u n)
      (C.Dat u (n - 1)) (C.φ u n) (C.φ u (n - 1)) (C.α u n) br +
    (C.β (n - 1) : ℂ) * X.starPair (wExt (C.Dat u n) (C.Dat u (n - 1)) (C.φ u n) (C.φ u (n - 1)))
      (barField G (C.Dat u n).Ψ (C.φ u n))

/-- **One step** (P6 (2.31)): `T_{j,n-1} = T_{j,n} + R_{j,n}`. -/
theorem step {u : U} (hu : u ∈ S) {n : ℕ} (hn2 : j + 2 ≤ n) (hnk : n ≤ k) :
    C.T u (n - 1) = C.T u n + C.cost u n := by
  have h := actionRegion_conversion X br (a := C.a n) (au := C.a (n - 1)) (ν := C.ν n)
    (νu := C.ν (n - 1)) (β := C.β n) (b := C.β (n - 1) - C.β n) (e := C.e n)
    (Dat := C.Dat u n) (Du := C.Dat u (n - 1)) (φ := C.φ u n) (φu := C.φ u (n - 1))
    (α := C.α u n) (C.β_ne n (by omega) hnk)
    (fun m => by have := C.coeff n hn2 hnk m; linarith)
    (by have := C.mass n hn2 hnk; linarith)
    (fun x i => C.same_h n hn2 hnk u hu x i) (C.el n hn2 hnk u hu) (C.unit n hn2 hnk u hu)
  have e : C.β n + (C.β (n - 1) - C.β n) = C.β (n - 1) := by ring
  rw [e] at h
  unfold T cost
  linear_combination h

/-- **The telescoping identity**: `T_{j,j+1} = T_{j,m} + ∑_{n=j+2}^{m} R_{j,n}`, `j + 1 ≤ m ≤ k`. -/
theorem telescope {u : U} (hu : u ∈ S) {m : ℕ} (hm1 : j + 1 ≤ m) (hmk : m ≤ k) :
    C.T u (j + 1) = C.T u m + ∑ n ∈ Finset.Ioc (j + 1) m, C.cost u n := by
  induction m, hm1 using Nat.le_induction with
  | base => simp
  | succ m hm ih =>
    have h1 := C.step hu (n := m + 1) (by omega) hmk
    simp only [Nat.add_sub_cancel] at h1
    rw [ih (by omega), h1, Finset.sum_Ioc_succ_top (by omega)]
    ring

end ConvChain

end Balaban.LargeField.ActionConv
