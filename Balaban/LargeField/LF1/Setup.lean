/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.LF1.Avg
public import Balaban.Multiscale.Operator
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The multiscale action and the pair sums of LF-1 (LF-RECONSTRUCTION §II.4)

On the fine torus `Site d L N₀ q = Torus d (N₀ L^q)` (unit lattice spacing) and the coarse tori
`Blk d L N₀ q n = Torus d (N₀ L^(q-n))` of the `n`-blocks (side `L^n`):

* `blkMap n`, `fib n y` (the sites of the `n`-block `y`), `bavgL n φ = Q_n φ`, `tBlocks n S`
  (`T_n(S)`, the `n`-blocks meeting `S`), `lam G n` (`Λ_n`, with `Λ_0 = T ∖ Ω₁`);
* `psiFull φ ψ`: the family `ψ_n` with `ψ_0 := φ`;
* `AdjB`: nearest-neighbour blocks; `pairSumP T f` is `∑_{{y,y'}} ‖f y - f y'‖²` over the unordered
  nearest-neighbour pairs of `T` (written as half the ordered sum); `crossSumP G n X ψ` is
  `∑_{(b₊,b₋) ∈ P^×_{n+1}(X)} ‖ψ_{n+1}(b₊) - (Qψ_n)(b₋)‖²`;
* `actionG G a μ h X ψ φ`: the action `A_G(X; ψ, φ)` of §II.4.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Finset

/-- The fine torus (sites). -/
abbrev Site (d L N₀ q : ℕ) : Type := Torus d (N₀ * L ^ q)

/-- The torus of `n`-blocks (side `L^n`) of the fine torus. -/
abbrev Blk (d L N₀ q n : ℕ) : Type := Torus d (N₀ * L ^ (q - n))

section Defs

variable (d L N₀ q : ℕ) [NeZero N₀] [NeZero L]

/-- The `n`-block of a site. -/
def blkMap (n : ℕ) (x : Site d L N₀ q) : Blk d L N₀ q n :=
  blockMap (L ^ n) (N₀ * L ^ (q - n)) x

/-- The sites of the `n`-block `y`. -/
def fib (n : ℕ) (y : Blk d L N₀ q n) : Finset (Site d L N₀ q) :=
  Finset.univ.filter fun x => blkMap d L N₀ q n x = y

/-- The `n`-blocks meeting `S`: `T_n(S)`. -/
def tBlocks (n : ℕ) (S : Finset (Site d L N₀ q)) : Finset (Blk d L N₀ q n) :=
  S.image (blkMap d L N₀ q n)

/-- The block average `Q_n φ` of a vector-valued field. -/
noncomputable def bavgL {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (n : ℕ)
    (φ : Site d L N₀ q → E) (y : Blk d L N₀ q n) : E :=
  bavg (L ^ n) (N₀ * L ^ (q - n)) φ y

/-- The coarsening map from `n`-blocks to `(n+1)`-blocks. -/
def coarse (n : ℕ) (s : Blk d L N₀ q n) : Blk d L N₀ q (n + 1) :=
  blockMap L (N₀ * L ^ (q - (n + 1))) s

open Classical in
/-- `(Q ψ_n)(b) = L^{-d} ∑_{s ⊂ b} ψ_n(s)` for an `(n+1)`-block `b`. -/
noncomputable def qCoarse {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (n : ℕ)
    (g : Blk d L N₀ q n → E) (b : Blk d L N₀ q (n + 1)) : E :=
  ((L : ℝ) ^ d)⁻¹ • ∑ s ∈ Finset.univ.filter (fun s => coarse d L N₀ q n s = b), g s

variable {d L N₀ q} {ϱ : ℝ}

/-- `Λ_n`: the layer `Ω_n ∖ Ω_{n+1}` for `n ≥ 1`, and `Λ_0 = T ∖ Ω₁`. -/
def lam (G : GeneratingSet d L N₀ q ϱ) (n : ℕ) : Finset (Site d L N₀ q) :=
  if n = 0 then Finset.univ \ G.Ω 1 else G.layer n

/-- Nearest-neighbour (distinct) sites of a torus. -/
def AdjT {d m : ℕ} (y y' : Torus d m) : Prop :=
  y ≠ y' ∧ ∃ μ : Fin d, y' = y + Pi.single μ 1 ∨ y = y' + Pi.single μ 1

open Classical in
/-- The sum `∑_{{y,y'}} ‖f y - f y'‖²` over the unordered pairs of nearest-neighbour sites of
`T` (half of the ordered sum). -/
noncomputable def pairSumT {E : Type*} [NormedAddCommGroup E] {d m : ℕ}
    (T : Finset (Torus d m)) (f : Torus d m → E) : ℝ :=
  (1 / 2) * ∑ y ∈ T, ∑ y' ∈ T, if AdjT y y' then ‖f y - f y'‖ ^ 2 else 0

/-- The family `ψ_n` with `ψ_0 := φ` (P2's convention `a_0 = ∞`). -/
def psiFull {E : Type*} (φ : Site d L N₀ q → E) (ψ : (m : ℕ) → Blk d L N₀ q m → E) :
    (m : ℕ) → Blk d L N₀ q m → E
  | 0 => φ
  | m + 1 => ψ (m + 1)

open Classical in
/-- `∑_{(b₊,b₋) ∈ P^×_{n+1}(X)} ‖ψ_{n+1}(b₊) - (Qψ_n)(b₋)‖²`: nearest-neighbour `(n+1)`-blocks
contained in `X`, `b₊ ⊂ Ω_{n+1}`, `b₋ ∩ Ω_{n+1} = ∅`. -/
noncomputable def crossSumP {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (G : GeneratingSet d L N₀ q ϱ) (n : ℕ) (X : Finset (Site d L N₀ q))
    (ψ : (m : ℕ) → Blk d L N₀ q m → E) : ℝ :=
  ∑ bp : Blk d L N₀ q (n + 1), ∑ bm : Blk d L N₀ q (n + 1),
    if AdjT bp bm ∧ fib d L N₀ q (n + 1) bp ⊆ X ∩ G.Ω (n + 1) ∧ fib d L N₀ q (n + 1) bm ⊆ X ∧
        Disjoint (fib d L N₀ q (n + 1) bm) (G.Ω (n + 1))
    then ‖ψ (n + 1) bp - qCoarse d L N₀ q n (ψ n) bm‖ ^ 2 else 0

/-- **The multiscale action** `A_G(X; ψ, φ)` of §II.4. -/
noncomputable def actionG {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (G : GeneratingSet d L N₀ q ϱ) (a : ℕ → ℝ) (μ : ℝ) (h : E) (X : Finset (Site d L N₀ q))
    (ψ : (m : ℕ) → Blk d L N₀ q m → E) (φ : Site d L N₀ q → E) : ℝ :=
  (1 / 2) * ∑ n ∈ Finset.Icc 1 q, ∑ y ∈ tBlocks d L N₀ q n (lam G n ∩ X),
      a n * (L : ℝ) ^ (n * (d - 2)) * ‖ψ n y - bavgL d L N₀ q n φ y‖ ^ 2 +
    (1 / 2) * bondE X φ + μ / 2 * ∑ x ∈ X, ‖φ x - h‖ ^ 2

end Defs

end Balaban.LargeField
