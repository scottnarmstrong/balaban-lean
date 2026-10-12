/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.Xi
public import Balaban.Localization.TreeLengthCov
public import Balaban.Background.Composition
public import Balaban.Background.SingleScale
public import Balaban.Flow.RunningCoefficients
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Def-6, objects: scales, domains, polymers, symmetries, composed fields (SMALLFIELD.md §1)

Draft vocabulary for the small-field class `Balaban/SmallField/Def6.lean`, at `λ = ∞`.  All
objects live on the fine torus `CTorus d L N₁ m₁ k = Torus d ((N₁ L^{m₁}) L^k)` of the landed
Localization files (unit spacing `η = 1`; `Λ_j` is the set of `L^j`-aligned sites, a site `y`
standing for its `j`-block).

* `levelGS j`: the whole-lattice generating set of level `j` (`Ω_1 = … = Ω_j = 𝕋`), `𝔹_j`;
* `aIdeal`, `nuIdeal`, `bgMass`: the coefficients of the connecting problem (SMALLFIELD §1.1) and
  the mass of the backgrounds (P5 (1.9): `0` for `β_k ν_k ≤ 1`);
* `XiDom`: the analyticity domain `Ξ^c_j(𝔹; 1, ε)` as a set of complex data `(Ψ, h)`;
* `IsPolyDom`: the domains `𝒟_j` (connected unions of `π'_j`-cubes);
* `latSymGroup`: the Euclidean symmetry group of the level-`j` lattice, acting on the fine torus;
* `composedField`: the field `ψ_k^{(j)} = composeField (𝔹_j, 𝔹_k)` of I-2 (6.2).
-/

@[expose] public section

namespace Balaban.SmallField.Def6

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Finset

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- A complex field on the fine torus. -/
abbrev Fld (d L N₁ m₁ k N : ℕ) : Type := CTorus d L N₁ m₁ k → Fin N → ℂ

/-! ### Level generating sets and coefficients -/

open Classical in
/-- **`𝔹_j`, the whole-lattice generating set of level `j ≤ k`**: `Ω_i = 𝕋` for `i ≤ j`, `∅`
otherwise; its only layer is `j`, so `ℓ ≡ L^j`. -/
noncomputable def levelGS (j : ℕ) (hj : j ≤ k) : GeneratingSet d L (N₁ * L ^ m₁) k ϱ where
  Ω := fun i => if i ≤ j then Finset.univ else ∅
  top := by simp; omega
  subset := fun i _ hik => by
    split_ifs <;> first | (exfalso; omega) | simp
  blockUnion := fun i _ _ x x' _ => by split_ifs <;> simp
  separation := fun i _ _ x hx y hy => by
    exfalso
    by_cases h : i ≤ j
    · simp [h] at hx
    · by_cases h' : i + 1 ≤ j
      · omega
      · simp [h'] at hy

/-- **Ideal flow matched at step `k`** (SMALLFIELD §1.1, P1 (2.9)-(2.11), `λ = ∞`):
`a_n = a_k (1 - L^{-2k}) / (1 - L^{-2n})`. -/
noncomputable def aIdeal (L k : ℕ) (ak : ℝ) (n : ℕ) : ℝ :=
  ak * (1 - ((L : ℝ) ^ k)⁻¹ ^ 2) / (1 - ((L : ℝ) ^ n)⁻¹ ^ 2)

/-- `ν_j = ν_k s_{jk}²`, `s_{jk} = L^{-(k-j)}`. -/
noncomputable def nuIdeal (L k : ℕ) (νk : ℝ) (j : ℕ) : ℝ := νk * (((L : ℝ) ^ (k - j))⁻¹) ^ 2

/-- **The mass of the backgrounds of step `k`, in fine units** (SMALLFIELD §1.6 item 1, P5 (1.9),
P6 p. 2): `0` if `β_k ν_k ≤ 1` (the backgrounds are `ν`-free and the field `h` enters through the
explicit field term of `ℰ`), and `ν_k L^{-2k}` otherwise.  It is the same at every level `j ≤ k`
since `ν_j L^{-2j} = ν_k L^{-2k}`. -/
noncomputable def bgMass (L k : ℕ) (βk νk : ℝ) : ℝ :=
  if βk * νk ≤ 1 then 0 else νk * ((L : ℝ) ^ k)⁻¹ ^ 2

/-! ### Domains -/

/-- **The analyticity domain `Ξ^c_j(𝔹; 1, ε)`** (SMALLFIELD §1.7; FLUCTUATION F-1) as a set of
complex data `(Ψ, h)` on the fine torus: `Ψ = Ψ₀ + Ψ''`, `h = h₀ + h''` with the landed
`XiC` (`σ = 1`) over a real datum `(Ψ₀, h₀)` in `Ξ_j(𝔹; 1, ε)`.  Here `a` is the kernel sequence,
`ν` the fine mass of the backgrounds and `j` the level. -/
def XiDom (G : GeneratingSet d L (N₁ * L ^ m₁) k ϱ) (a : ℕ → ℝ) (ν : ℝ) (j : ℕ) (ε : ℝ)
    (Ψ h : Fld d L N₁ m₁ k N) : Prop :=
  ∃ (Ψ₀ : CTorus d L N₁ m₁ k → Fin N → ℝ) (h₀ : Fin N → ℝ)
    (Ψ'' h'' : CTorus d L N₁ m₁ k → Fin N → ℂ),
    (∀ x i, Ψ x i = (Ψ₀ x i : ℂ) + Ψ'' x i) ∧ (∀ x i, h x i = (h₀ i : ℂ) + h'' x i) ∧
      SmallField.XiC G a ν j 1 ε Ψ₀ h₀ Ψ'' h''

/-- **The domains `𝒟_j`** (P1 (2.26); LOCALIZATION §4.0): nonempty, connected unions of
`π'_j`-cubes (aligned boxes of side `L M ℓ_j`), i.e. sets with a chosen family of cubes. -/
def IsPolyDom (m₀ j : ℕ) (X : Set (CTorus d L N₁ m₁ k)) : Prop :=
  X.Nonempty ∧ (∃ 𝒦, ChosenOne (L := L) (N₁ := N₁) (m₁ := m₁) (K := k) m₀ j X 𝒦) ∧
    ∀ x ∈ X, ∀ y ∈ X, Relation.ReflTransGen (fun a b => a ∈ X ∧ b ∈ X ∧ Nbr a b) x y

/-- **The size `d_j(X)`** of a polymer: the single-scale covering functional (Def-L8,
LOCALIZATION v3; `d^cov ≤ d`). -/
noncomputable def sizeJ (m₀ j : ℕ) (X : Set (CTorus d L N₁ m₁ k)) : ℝ :=
  treeLenCovOne (L := L) (N₁ := N₁) (m₁ := m₁) (K := k) m₀ j X

/-! ### Symmetries -/

/-- The base of the `j`-block of a site. -/
def blockBase (L j : ℕ) (x : CTorus d L N₁ m₁ k) : CTorus d L N₁ m₁ k := cbase (L ^ j) x

/-- Translation by one `j`-block in the direction `μ`. -/
def transJ (L j : ℕ) (μ : Fin d) : Equiv.Perm (CTorus d L N₁ m₁ k) :=
  Equiv.addRight ((L ^ j : ℕ) • (Pi.single μ 1 : CTorus d L N₁ m₁ k))

/-- The reflection of the `μ`-th coordinate that maps `j`-blocks to `j`-blocks:
`x_μ ↦ L^j - 1 - x_μ` (the reflection of the block lattice `L^j ℤ^d`). -/
def flipJ (L j : ℕ) (μ : Fin d) : Equiv.Perm (CTorus d L N₁ m₁ k) where
  toFun x := Function.update x μ (((L ^ j : ℕ) : ZMod _) - 1 - x μ)
  invFun x := Function.update x μ (((L ^ j : ℕ) : ZMod _) - 1 - x μ)
  left_inv x := by ext i; by_cases h : i = μ <;> simp [h]
  right_inv x := by ext i; by_cases h : i = μ <;> simp [h]

/-- The exchange of the coordinates `μ` and `ν`. -/
def swapJ (μ ν : Fin d) : Equiv.Perm (CTorus d L N₁ m₁ k) where
  toFun x := x ∘ Equiv.swap μ ν
  invFun x := x ∘ Equiv.swap μ ν
  left_inv x := by ext i; simp
  right_inv x := by ext i; simp

/-- **The Euclidean symmetry group of the level-`j` lattice** acting on the fine torus:
generated by the block translations, the block reflections and the coordinate exchanges.  All of
them permute the `j`-blocks. -/
def latSymGroup (L j : ℕ) : Subgroup (Equiv.Perm (CTorus d L N₁ m₁ k)) :=
  Subgroup.closure ({g | ∃ μ, g = transJ L j μ} ∪ {g | ∃ μ, g = flipJ L j μ} ∪
    {g | ∃ μ ν, g = swapJ μ ν})

/-- The action of a permutation of the torus on fields: `(g·Ψ)(x) = Ψ(g⁻¹ x)`. -/
def actField (g : Equiv.Perm (CTorus d L N₁ m₁ k)) (Ψ : Fld d L N₁ m₁ k N) :
    Fld d L N₁ m₁ k N := fun x => Ψ (g.symm x)

/-- The action of a matrix on a field (pointwise). -/
def rotField (R : Matrix (Fin N) (Fin N) ℂ) (Ψ : Fld d L N₁ m₁ k N) :
    Fld d L N₁ m₁ k N := fun x => R.mulVec (Ψ x)

/-- Complex orthogonal matrices in `O(N)(ℝ)` or `SO(N, ℂ)`: `Rᵀ R = 1` and `R` real or `det R = 1`. -/
def IsRot (R : Matrix (Fin N) (Fin N) ℂ) : Prop :=
  R.transpose * R = 1 ∧ ((∀ i j, (R i j).im = 0) ∨ R.det = 1)

/-! ### The composed field -/

theorem levelGS_precedes {j : ℕ} (hj : j ≤ k) :
    Precedes (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (ϱ := ϱ) j hj)
      (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (ϱ := ϱ) k le_rfl) := by
  intro i _ hik
  classical
  simp only [levelGS]
  split_ifs <;> simp_all

/-- **The datum `ψ_k^{(j)}(ψ_k, h)`** (SMALLFIELD (H.2); I-2 (6.2); P1 (2.14)) as a `BgData` of
`𝔹_j`: `composeData` of the level-`j` set over the level-`k` set, from the datum `D` of `𝔹_k`
and its background field `φ_k = bgField` (with the kernel sequence `a` and the mass `ν`). -/
noncomputable def composedData (a : ℕ → ℝ) (ν : ℝ) {j : ℕ} (hj : j ≤ k)
    (D : BgData (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (ϱ := ϱ) k le_rfl) N) :
    BgData (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (ϱ := ϱ) j hj) N :=
  composeData (levelGS_precedes hj) a
    (bgField (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (ϱ := ϱ) k le_rfl) a ν D) D

end Balaban.SmallField.Def6
