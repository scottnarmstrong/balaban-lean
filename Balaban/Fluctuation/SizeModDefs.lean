/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.BlockCount
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The covering size modulo a hole: Definition 1.1 (FLUCTUATION.md §1.2)

The sites are the points of the torus `CTorus d L N₁ m₁ K` of the landed covering functional
`treeLenCovOne`; `π_j`-cubes are the cells `box b a` (`b` aligned to `a`, `a = cellSide L m₀ m₁ j`
is `M L^j` fine sites) and `π'_j`-cubes are the boxes `box b (L a)`.

* `IsDj m₀ j X`: `X ∈ 𝒟_j`, a nonempty, nearest-neighbour-connected union of `π'_j`-cubes.
* `OmegaComp Ω z`: the connected component of `z ∈ Ω^c`, connectivity being the
  nearest-neighbour adjacency of sites (the same as for `𝒟_j`).  This is the plain reading of
  "connected component of `Ω^c`" in P5 (1.33); it differs from the `*`-components of the landed
  `Balaban.LargeField.DmodOmega`, for which (G4) would fail with nearest-neighbour `𝒟_j`.
* `DjMod m₀ j Ω X`: `X ∈ 𝒟_j(mod Ω^c)`, the polymers of `𝒟_j` containing or missing each
  component of `Ω^c` (P5 (1.33)).
* `dcovModE m₀ j Ω X` (`d^cov_j(X mod Ω^c)`): the infimum over families `𝒦` of `π'_j`-cubes
  contained in `X` whose union contains `X ∩ Ω` and connected structures `Γ ⊂ X` meeting every
  cube of `𝒦`, of the length `M⁻¹ℓ_j⁻¹|Γ|`, with values in `[0, ∞]` (the infimum over the empty
  set is `+∞`).  `dcovMod` is its real value, used where the infimum is over a nonempty set (e.g.
  for `X ∈ 𝒟_j(mod Ω^c)` meeting `Ω`, `dcovModE_ne_top`).
* `Yhat Ω S` (`Ŷ(S)`), `dOmega m₀ j Ω S` (`d_Ω(S)`, `+∞` if `Ŷ(S)` is not connected).
* `dcovMod_of_subset`: for `X ⊆ Ω` the modular size is `treeLenCovOne`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization

section Defs

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] (m₀ j : ℕ)

/-- `X` is a union of `π'_j`-cubes (aligned boxes of side `L · cellSide`). -/
def IsPiPrimeUnion (X : Set (CTorus d L N₁ m₁ K)) : Prop :=
  ∀ z ∈ X, ∃ b, Aligned (cellSide L m₀ m₁ j) b ∧ z ∈ box b (L * cellSide L m₀ m₁ j) ∧
    box b (L * cellSide L m₀ m₁ j) ⊆ X

/-- `Ω` is a union of `π_j`-cubes (cells: aligned boxes of side `cellSide`). -/
def IsPiUnion (Ω : Set (CTorus d L N₁ m₁ K)) : Prop :=
  ∀ z ∈ Ω, ∃ b, Aligned (cellSide L m₀ m₁ j) b ∧ z ∈ box b (cellSide L m₀ m₁ j) ∧
    box b (cellSide L m₀ m₁ j) ⊆ Ω

variable {m₀ j}

/-- `X` is connected for the nearest-neighbour adjacency, inside `X`. -/
def SiteConnected (X : Set (CTorus d L N₁ m₁ K)) : Prop :=
  ∀ x ∈ X, ∀ y ∈ X, Relation.ReflTransGen (fun u v => u ∈ X ∧ v ∈ X ∧ Nbr u v) x y

variable (m₀ j)

/-- `X ∈ 𝒟_j`: a nonempty, connected union of `π'_j`-cubes. -/
def IsDj (X : Set (CTorus d L N₁ m₁ K)) : Prop :=
  X.Nonempty ∧ IsPiPrimeUnion m₀ j X ∧ SiteConnected X

/-- `Near r a u v`: `v = u + a q` with `|q_μ| ≤ r` for every `μ` (cube-index distance `≤ r`). -/
def Near {n : ℕ} (r a : ℕ) (u v : Torus d n) : Prop :=
  ∃ q : Fin d → ℤ, (∀ μ, |q μ| ≤ r) ∧ v = u + fun μ => (((a : ℤ) * q μ : ℤ) : ZMod n)

/-- Two sites lie in `π_j`-cubes at index distance `≤ 1` (the `*`-adjacency of cubes). -/
def CellNear (x y : CTorus d L N₁ m₁ K) : Prop :=
  Near 1 (cellSide L m₀ m₁ j) (cbase (cellSide L m₀ m₁ j) x) (cbase (cellSide L m₀ m₁ j) y)

/-- The connected component of the site `z` of `Ω^c`: the sites of `Ω^c` reachable from `z`
through nearest-neighbour steps inside `Ω^c`. -/
def OmegaComp (Ω : Set (CTorus d L N₁ m₁ K)) (z : CTorus d L N₁ m₁ K) :
    Set (CTorus d L N₁ m₁ K) :=
  {y | y ∈ Ωᶜ ∧ Relation.ReflTransGen
    (fun u v => u ∈ Ωᶜ ∧ v ∈ Ωᶜ ∧ Nbr u v) z y}

/-- **`𝒟_j(mod Ω^c)`** (P5 (1.33)): the `X ∈ 𝒟_j` containing or missing each component of `Ω^c`. -/
def DjMod (Ω X : Set (CTorus d L N₁ m₁ K)) : Prop :=
  IsDj m₀ j X ∧ ∀ z ∈ Ωᶜ, OmegaComp Ω z ⊆ X ∨ Disjoint (OmegaComp Ω z) X

/-- The data of Definition 1.1: a family `𝒦` of `π'_j`-cubes contained in `X` whose union
contains `X ∩ Ω`, and a connected structure `Γ = (W, E)` contained in `X` meeting every cube of
`𝒦`. -/
def ModAdmissible (Ω X : Set (CTorus d L N₁ m₁ K)) (𝒦 : Set (CTorus d L N₁ m₁ K))
    (W : Finset (CTorus d L N₁ m₁ K)) (E : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K)) :
    Prop :=
  (∀ b ∈ 𝒦, Aligned (cellSide L m₀ m₁ j) b ∧ box b (L * cellSide L m₀ m₁ j) ⊆ X) ∧
    X ∩ Ω ⊆ ⋃ b ∈ 𝒦, box b (L * cellSide L m₀ m₁ j) ∧
    ConnStruct W E ∧ (↑W ⊆ X) ∧ MeetsOne m₀ j 𝒦 W

/-- **Definition 1.1: the modular covering size `d^cov_j(X mod Ω^c)`**, in `[0, ∞]` (`+∞` if no
admissible pair exists).  The length of `Γ` is `M⁻¹ℓ_j⁻¹ |E|`, as for `treeLenCovOne`. -/
noncomputable def dcovModE (Ω X : Set (CTorus d L N₁ m₁ K)) : ENNReal :=
  ⨅ (𝒦 : Set (CTorus d L N₁ m₁ K)) (W : Finset (CTorus d L N₁ m₁ K))
    (E : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K))
    (_ : ModAdmissible m₀ j Ω X 𝒦 W E), ENNReal.ofReal (bondCost (scaleW L m₀ m₁ j) E)

/-- The real value of `dcovModE` (it is the source object whenever the infimum is over a
nonempty set, in particular for `X ∈ 𝒟_j(mod Ω^c)` with `X ∩ Ω ≠ ∅`). -/
noncomputable def dcovMod (Ω X : Set (CTorus d L N₁ m₁ K)) : ℝ :=
  (dcovModE m₀ j Ω X).toReal

/-- `Ŷ(S)`: `S` together with all components of `Ω^c` adjacent to `S`. -/
def Yhat (Ω S : Set (CTorus d L N₁ m₁ K)) : Set (CTorus d L N₁ m₁ K) :=
  S ∪ {y | ∃ z ∈ Ωᶜ, (∃ s ∈ S, Nbr s z) ∧ y ∈ OmegaComp Ω z}

/-- **`d_Ω(S) := d^cov_j(Ŷ(S) mod Ω^c)`** when `Ŷ(S)` is connected, `+∞` otherwise. -/
noncomputable def dOmega (Ω S : Set (CTorus d L N₁ m₁ K)) : ENNReal :=
  open Classical in
  if SiteConnected (Yhat Ω S) then dcovModE m₀ j Ω (Yhat Ω S) else ⊤

end Defs

end Balaban.Fluctuation
