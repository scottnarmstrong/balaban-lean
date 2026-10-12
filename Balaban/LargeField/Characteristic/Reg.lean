module

public import Balaban.LargeField.Background.StepBackgrounds
import Mathlib.Tactic.Linarith

/-!
# The regularity predicate (Part II, Definition II.3.1)

For a generating set `G` at level `q`, data `D` and the background `φ = bgFieldC G a μ c₀ D`
(`c₀ = bgC0`, the Def-5 background) with multiplier `α = bgMultC G a μ c₀ D`, the regularity
predicate `Reg_q(G, D, δ; T, S)` is the conjunction of

* the domain conjunct `D ∈ 𝒟_ℝ(G)` (`InUnionDomainR`);
* `BlockClose`: `|Ψ(x) - (Q φ)(x)| < δ` for the sites `x ∈ T` (the sites of the `q`-blocks of `T`);
* `GradClose`: `ℓ |∂_e φ̄(x)|, ℓ² |Δ φ̄(x)|, ℓ² |α(x)| < δ` for the sites `x ∈ S ∩ Ω₁(G)`,
  `ℓ = ℓ_q = L ^ q` (fine units);
* `FieldClose`: if `ν > 0` (`ν = μ L^{2q}` the dimensionless mass), `|φ(x) - h| < δ / √ν` and
  `|h · h - 1| < δ² / ν` for `x ∈ S ∩ Ω₁(G)`, `h = D.h x` (the field `h̃` is the constant `h` on
  `Ω₁`, so this is the condition of the source).

`RegC` is the same with the complex domain `𝒟(G)` (`InUnionDomainC`), moduli of complex numbers
(Definition II.3.5). The sets `T`, `S` are finite sets of fine sites (unions of blocks), `T`
contained in the top layer when `BlockClose` is used with the single-scale lift.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background

set_option linter.unusedSectionVars false

variable {d L N₀ q N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

section Ineq

variable (G : GeneratingSet d L N₀ q ϱ)

/-- The extension `φ̄` of `φ` by the data `Ψ`, as a vector of `ℂ^N`. -/
noncomputable def barVec (D : BgData G N) (φ : G.Ω 1 × Fin N → ℂ) (x : Torus d (N₀ * L ^ q)) :
    Fin N → ℂ := fun i => barField G D.Ψ φ x i

/-- The discrete Laplacian `Δ φ̄(x) = ∑_μ (φ̄(x + e_μ) + φ̄(x - e_μ) - 2 φ̄(x))`. -/
noncomputable def barLap (D : BgData G N) (φ : G.Ω 1 × Fin N → ℂ) (x : Torus d (N₀ * L ^ q)) :
    Fin N → ℂ :=
  ∑ μ : Fin d, (barVec G D φ (x + Pi.single μ 1) + barVec G D φ (x - Pi.single μ 1) -
    2 • barVec G D φ x)

/-- `|Ψ(x) - (Q φ)(x)|`, `Q` the block average over the block of the layer of `x`. -/
noncomputable def blockDev (D : BgData G N) (φ : G.Ω 1 × Fin N → ℂ)
    (x : Torus d (N₀ * L ^ q)) : ℝ :=
  vn (fun i => D.Ψ x i - blockAvg G φ x i)

/-- `|Ψ - Q φ| < δ` on the sites `T`. -/
def BlockClose (D : BgData G N) (φ : G.Ω 1 × Fin N → ℂ) (T : Finset (Torus d (N₀ * L ^ q)))
    (δ : ℝ) : Prop :=
  ∀ x ∈ T, blockDev G D φ x < δ

/-- `ℓ |∂_e φ̄|, ℓ² |Δ φ̄|, ℓ² |α| < δ` on the sites of `S ∩ Ω₁`. -/
def GradClose (D : BgData G N) (φ : G.Ω 1 × Fin N → ℂ) (α : G.Ω 1 → ℂ) (ℓ : ℝ)
    (S : Finset (Torus d (N₀ * L ^ q))) (δ : ℝ) : Prop :=
  ∀ x : G.Ω 1, (x : Torus d (N₀ * L ^ q)) ∈ S →
    (∀ μ : Fin d, ℓ * vn (barVec G D φ ((x : Torus d (N₀ * L ^ q)) + Pi.single μ 1) -
        barVec G D φ x) < δ ∧
      ℓ * vn (barVec G D φ ((x : Torus d (N₀ * L ^ q)) - Pi.single μ 1) - barVec G D φ x) < δ) ∧
    ℓ ^ 2 * vn (barLap G D φ x) < δ ∧ ℓ ^ 2 * ‖α x‖ < δ

/-- If `ν > 0`: `|φ - h| < δ / √ν` and `|h · h - 1| < δ² / ν` on the sites of `S ∩ Ω₁`
(`ν` the dimensionless mass). -/
def FieldClose (D : BgData G N) (φ : G.Ω 1 × Fin N → ℂ) (ν : ℝ)
    (S : Finset (Torus d (N₀ * L ^ q))) (δ : ℝ) : Prop :=
  0 < ν → ∀ x : G.Ω 1, (x : Torus d (N₀ * L ^ q)) ∈ S →
    vn (fun i => φ (x, i) - D.h x i) < δ / Real.sqrt ν ∧
      ‖∑ i, D.h x i * D.h x i - 1‖ < δ ^ 2 / ν

variable (a : ℕ → ℝ) (μ : ℝ)

/-- The inequalities of `Reg` (all but the domain conjunct), for the background of Def-5 with
`c₀ = bgC0`. -/
def RegIneq (D : BgData G N) (δ : ℝ) (T S : Finset (Torus d (N₀ * L ^ q))) : Prop :=
  BlockClose G D (bgFieldC G a μ (bgC0 d L N) D) T δ ∧
  GradClose G D (bgFieldC G a μ (bgC0 d L N) D) (bgMultC G a μ (bgC0 d L N) D)
    ((L : ℝ) ^ q) S δ ∧
  FieldClose G D (bgFieldC G a μ (bgC0 d L N) D) (μ * ((L : ℝ) ^ q) ^ 2) S δ

/-- **Definition II.3.1**: the regularity predicate `Reg_q(G, D, δ; T, S)` (real data). -/
def Reg (D : BgData G N) (δ : ℝ) (T S : Finset (Torus d (N₀ * L ^ q))) : Prop :=
  InUnionDomainR G (bgC1 d L N) μ D ∧ RegIneq G a μ D δ T S

/-- The complex version (Definition II.3.5): the same inequalities with moduli of complex
numbers, on the open complex domain `𝒟(G)` of Theorem 5.2. -/
def RegC (D : BgData G N) (δ : ℝ) (T S : Finset (Torus d (N₀ * L ^ q))) : Prop :=
  InUnionDomainC G (bgC0 d L N) (bgC1 d L N) μ D ∧ RegIneq G a μ D δ T S

/-- The inequalities of the mixed characteristic function (P5 (2.13), Definition II.3.2 item 3):
`|Ψ - Q φ| < ¾ δ` on `Tfar` (the `k`-blocks off `Ω_{k+1}`), `< 5/4 δ` on `Tnear` (the
`(k+1)`-blocks of `Ω_{k+1}`), and `ℓ |∂φ̄|, ℓ² |Δφ̄|, ℓ² |α| < ¾ δ` on `S`, and the `h`-conditions
with `¾ δ` and the dimensionless mass `νk`. -/
def RegMixedIneq (D : BgData G N) (ℓ νk δ : ℝ) (Tfar Tnear S : Finset (Torus d (N₀ * L ^ q))) :
    Prop :=
  BlockClose G D (bgFieldC G a μ (bgC0 d L N) D) Tfar (3 / 4 * δ) ∧
  BlockClose G D (bgFieldC G a μ (bgC0 d L N) D) Tnear (5 / 4 * δ) ∧
  GradClose G D (bgFieldC G a μ (bgC0 d L N) D) (bgMultC G a μ (bgC0 d L N) D) ℓ S
    (3 / 4 * δ) ∧
  FieldClose G D (bgFieldC G a μ (bgC0 d L N) D) νk S (3 / 4 * δ)

end Ineq

end Balaban.LargeField
