/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.RenormIdentity
public import Balaban.Background.MinimizerAlg

/-!
# The restricted hard-spin action `A_D` and the regional counterterm (P6 (2.22)-(2.23), (2.31))

Specification: `notes/phase1/P631.md` §1.

Setting: a generating set `G` (the mixed-scale set `𝔹_r(∂Ω_r)` of P6 §2, layers `r - 1` and `r`),
data `Dat = (ψ, h)` as `BgData`, fields `φ : Ω₁ × [N] → ℂ`, and `D` a finite union of cubes of `G`
(`Region`: a set of sites of `Ω₁` closed under the blocks `B_{n(x)}(x)` of its sites).  All products
are the complex *bilinear* ones.

* `Region.blockPair`, `bondPair`, `massPair`, `sitePair`: the restricted pairings `⟨·,·⟩_{D₁}`,
  `⟨∂·,∂·⟩_{D*}` (half-bond star weights `starWeight`), `⟨·,·⟩_D`, `⟨·,α·⟩_D`;
* `actionRegionC` (complex), `actionRegionR` (real, norms): the action `A_D` of P6 (1) at `λ = ∞`;
* `Region.crossing`, `Region.starPair`: `st(D)` and `S_D(w, φ) = ⟨w̄, ∂φ⟩_{st(D)}`, (2);
* `MassBranch`, `counterP`, `counterQ`, `counterR`, `counterC`: the regional counterterm (3).
-/

@[expose] public section

namespace Balaban.LargeField.ActionConv

open Balaban.Multiscale Balaban.Background Balaban.Fluctuation Finset

variable {d L N₀ K N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- A **region**: a finite union of cubes (blocks `B_{n(x)}(x)`) of the generating set `G`. -/
@[ext]
structure Region (G : GeneratingSet d L N₀ K ϱ) where
  /-- The sites of `D`. -/
  sites : Finset (Torus d (N₀ * L ^ K))
  /-- `D ⊆ Ω₁(G)`. -/
  sub_Ω : sites ⊆ G.Ω 1
  /-- `D` is a union of cubes: it contains the cube `B_{n(x)}(x)` of each of its sites. -/
  blockClosed : ∀ x ∈ sites, ∀ y ∈ G.blk (G.layerIndex x) x, y ∈ sites

variable {G : GeneratingSet d L N₀ K ϱ}

/-- The layer-indexed coefficient `a(x) = a_{n(x)} L^{-2 n(x)}`. -/
noncomputable def levelCoeff (G : GeneratingSet d L N₀ K ϱ) (a : ℕ → ℝ)
    (x : Torus d (N₀ * L ^ K)) : ℂ :=
  ((a (G.layerIndex x) / ((L : ℝ) ^ G.layerIndex x) ^ 2 : ℝ) : ℂ)

namespace Region

/-- The half-bond weight of the bond `(x, x + e_μ)`: `1` inside `D`, `1/2` across `∂D`. -/
noncomputable def starWeight (D : Region G) (x : Torus d (N₀ * L ^ K)) (μ : Fin d) : ℝ :=
  ((if x ∈ D.sites then 1 else 0) + (if x + Pi.single μ 1 ∈ D.sites then 1 else 0)) / 2

/-- `⟨p, q⟩_{D₁}` with the layer-indexed coefficients `a(x)`. -/
noncomputable def blockPair (D : Region G) (a : ℕ → ℝ) (p q : Torus d (N₀ * L ^ K) → Fin N → ℂ) :
    ℂ :=
  ∑ x ∈ D.sites, levelCoeff G a x * ∑ i, p x i * q x i

/-- `⟨∂f, ∂g⟩_{D*}` with the half-bond weights. -/
noncomputable def bondPair (D : Region G) (f g : Torus d (N₀ * L ^ K) → Fin N → ℂ) : ℂ :=
  ∑ x : Torus d (N₀ * L ^ K), ∑ μ : Fin d, (D.starWeight x μ : ℂ) *
    ∑ i, (f (x + Pi.single μ 1) i - f x i) * (g (x + Pi.single μ 1) i - g x i)

/-- `⟨p, q⟩_D`. -/
noncomputable def massPair (D : Region G) (p q : Torus d (N₀ * L ^ K) → Fin N → ℂ) : ℂ :=
  ∑ x ∈ D.sites, ∑ i, p x i * q x i

/-- `⟨p, α q⟩_D`, with `α` extended by zero off `Ω₁`. -/
noncomputable def sitePair (D : Region G) (α : G.Ω 1 → ℂ) (p q : Torus d (N₀ * L ^ K) → Fin N → ℂ) :
    ℂ :=
  ∑ x ∈ D.sites, zeroExt (G.Ω 1) α x * ∑ i, p x i * q x i

/-- `st(D)`: the bonds `(x, x + e_μ)` crossing `∂D`. -/
noncomputable def crossing (D : Region G) : Finset (Torus d (N₀ * L ^ K) × Fin d) :=
  Finset.univ.filter fun b => ¬ (b.1 ∈ D.sites ↔ b.1 + Pi.single b.2 1 ∈ D.sites)

/-- The outward oriented derivative of `f` across the crossing bond `b`. -/
noncomputable def outwardDeriv (D : Region G) (f : Torus d (N₀ * L ^ K) → Fin N → ℂ)
    (b : Torus d (N₀ * L ^ K) × Fin d) (i : Fin N) : ℂ :=
  if b.1 ∈ D.sites then f (b.1 + Pi.single b.2 1) i - f b.1 i
  else f b.1 i - f (b.1 + Pi.single b.2 1) i

/-- `S_D(w, φ) = ⟨w̄, ∂φ⟩_{st(D)}`, `w̄_b` the mean of the endpoint values (P631 (2)). -/
noncomputable def starPair (D : Region G) (w f : Torus d (N₀ * L ^ K) → Fin N → ℂ) : ℂ :=
  ∑ b ∈ D.crossing, ∑ i, ((w b.1 i + w (b.1 + Pi.single b.2 1) i) / 2) * D.outwardDeriv f b i

end Region

/-- **The restricted action `A_D`** (P6 (1), `λ = ∞`, complex bilinear form):
`½⟨ψ - Qφ, a (ψ - Qφ)⟩_{D₁} + ½‖∂φ‖²_{D*} + (ν/2)‖φ - h‖²_D`. -/
noncomputable def actionRegionC (D : Region G) (a : ℕ → ℝ) (ν : ℝ) (Dat : BgData G N)
    (φ : G.Ω 1 × Fin N → ℂ) : ℂ :=
  (1 / 2) * D.blockPair a (fun x i => Dat.Ψ x i - blockAvg G φ x i)
      (fun x i => Dat.Ψ x i - blockAvg G φ x i) +
  (1 / 2) * D.bondPair (barField G Dat.Ψ φ) (barField G Dat.Ψ φ) +
  (ν : ℂ) / 2 * D.massPair (fun x i => svec G φ x i - Dat.h x i)
      (fun x i => svec G φ x i - Dat.h x i)

/-- **The restricted action `A_D`, real form** (norms squared; meaningful for real data). -/
noncomputable def actionRegionR (D : Region G) (a : ℕ → ℝ) (ν : ℝ) (Dat : BgData G N)
    (φ : G.Ω 1 × Fin N → ℂ) : ℝ :=
  (1 / 2) * ∑ x ∈ D.sites, (a (G.layerIndex x) / ((L : ℝ) ^ G.layerIndex x) ^ 2) *
      ∑ i, ‖Dat.Ψ x i - blockAvg G φ x i‖ ^ 2 +
  (1 / 2) * ∑ x : Torus d (N₀ * L ^ K), ∑ μ : Fin d, D.starWeight x μ *
      ∑ i, ‖barField G Dat.Ψ φ (x + Pi.single μ 1) i - barField G Dat.Ψ φ x i‖ ^ 2 +
  ν / 2 * ∑ x ∈ D.sites, ∑ i, ‖svec G φ x i - Dat.h x i‖ ^ 2

/-- The mass convention of the Euler-Lagrange system: `r - 1 > k₀` uses the physical mass
(`complete`), `r - 1 ≤ k₀` uses mass `0` (`massless`) (P631 §1). -/
inductive MassBranch
  | complete
  | massless

/-- The mass used in the Euler-Lagrange equation of the branch. -/
def MassBranch.elMass : MassBranch → ℝ → ℝ
  | .complete, ν => ν
  | .massless, _ => 0

/-- The indicator `1_{r-1 ≤ k₀}` of the massless branch. -/
def MassBranch.ind : MassBranch → ℝ
  | .complete => 0
  | .massless => 1

/-- The lifted increment `v = θ - ψ` of the block-spin data. -/
def dataInc (Dat Du : BgData G N) : Torus d (N₀ * L ^ K) → Fin N → ℂ :=
  fun x i => Du.Ψ x i - Dat.Ψ x i

/-- The extension `w̄` of the increment `w = φ_u - φ` by `v` off `Ω₁`: the difference of the two
extended backgrounds. -/
noncomputable def wExt (Dat Du : BgData G N) (φ φu : G.Ω 1 × Fin N → ℂ) :
    Torus d (N₀ * L ^ K) → Fin N → ℂ :=
  fun x i => barField G Du.Ψ φu x i - barField G Dat.Ψ φ x i

/-- The regional bulk divergence `-Δ φ̄` of the extended background, componentwise. -/
noncomputable def bulkDiv (Dat : BgData G N) (φ : G.Ω 1 × Fin N → ℂ) :
    Torus d (N₀ * L ^ K) → Fin N → ℂ :=
  fun x i => negLap (fun y => barField G Dat.Ψ φ y i) x

section Counterterm

variable (D : Region G) (a : ℕ → ℝ) (ν β b e : ℝ) (Dat Du : BgData G N)
  (φ φu : G.Ω 1 × Fin N → ℂ) (α : G.Ω 1 → ℂ)

/-- `P_D` of P631 (3). -/
noncomputable def counterP : ℂ :=
  D.blockPair a (dataInc Dat Du) (fun x i => Dat.Ψ x i - blockAvg G φ x i) +
  ((b / (2 * β) : ℝ) : ℂ) * D.bondPair (barField G Dat.Ψ φ) (barField G Dat.Ψ φ) +
  ((ν * e / (2 * β) : ℝ) : ℂ) * D.massPair (fun x i => svec G φ x i - Dat.h x i)
      (fun x i => svec G φ x i - Dat.h x i)

/-- `Q_D` of P631 (3). -/
noncomputable def counterQ : ℂ :=
  (1 / 2) * D.blockPair a (fun x i => dataInc Dat Du x i - blockAvg G (φu - φ) x i)
      (fun x i => dataInc Dat Du x i - blockAvg G (φu - φ) x i) +
  (1 / 2) * ((1 + b / β : ℝ) : ℂ) *
    (D.bondPair (wExt Dat Du φ φu) (wExt Dat Du φ φu) +
      D.sitePair α (svec G (φu - φ)) (svec G (φu - φ))) +
  (ν : ℂ) / 2 * ((1 + e / β : ℝ) : ℂ) * D.massPair (svec G (φu - φ)) (svec G (φu - φ))

/-- `R_D` of P631 (3); `br` selects the branch (the last summand is the massless one). -/
noncomputable def counterR (br : MassBranch) : ℂ :=
  ((b / β : ℝ) : ℂ) * D.massPair (svec G (φu - φ))
      (fun x i => bulkDiv Dat φ x i + zeroExt (G.Ω 1) α x * svec G φ x i) +
  ((ν * e / β : ℝ) : ℂ) * D.massPair (svec G (φu - φ)) (fun x i => svec G φ x i - Dat.h x i) +
  ((br.ind * ν : ℝ) : ℂ) * D.massPair (svec G (φu - φ)) (fun x i => svec G φ x i - Dat.h x i)

/-- `C_D = P_D + Q_D + R_D` (P631 (3)). -/
noncomputable def counterC (br : MassBranch) : ℂ :=
  counterP D a ν β b e Dat Du φ + counterQ D a ν β b e Dat Du φ φu α +
    counterR D ν β b e Dat φ φu α br

end Counterterm

end Balaban.LargeField.ActionConv
