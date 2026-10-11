/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Multiscale.ConstraintComm
public import Balaban.Multiscale.Operator
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Background fields at `λ = ∞`: data, source, action, Euler–Lagrange system (BACKGROUND.md §1, §7)

Definitions only (freeze candidates).  Units are those of `Balaban/Multiscale/GeneratingSet.lean`
(lattice spacing `η = 1`, `ℓ_j = L ^ j`).  Every definition names the equation of P2 /
BACKGROUND.md it formalizes.

* `Balaban.Background.collar`: the collar `C(Ω₁)`;
* `Balaban.Background.BgData`: the data `(Ψ, h̃)`;
* `Balaban.Background.qStar`, `boundaryTerm`, `source`: the source `S` of (1.1);
* `Balaban.Background.action`: the action `A` of (1.2);
* `Balaban.Background.IsEL`, `IsSmallSolution`, `IsMinimizer`: (EL), the small solutions and the
  minimizers (BACKGROUND.md §7, Def-5);
* `Balaban.Background.InPsiTilde`, `InPsiTildeC`: the data domains `Ψ̃`, `Ψ̃^c` of (1.11), (1.12),
  conditions (R1)–(R4), (C1)–(C3).
-/

@[expose] public section

namespace Balaban.Background

open Balaban.Multiscale Matrix Finset

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- The Euclidean norm of a vector of `ℝ^N`. -/
noncomputable def rn (v : Fin N → ℝ) : ℝ := Real.sqrt (∑ i, v i ^ 2)

section Sites

variable (G : GeneratingSet d L N₀ k ϱ)

/-- **The collar** `C(Ω₁) = {x' ∉ Ω₁ : x' ∼ x for some x ∈ Ω₁}` (BACKGROUND.md §1.1).  It plays
the role of the layer `Λ₀` of P2 (1.2), (1.13).  (P2 p. 610 has a band of big blocks; only the
sites adjacent to `Ω₁` enter the equations.) -/
noncomputable def collar : Finset (Torus d (N₀ * L ^ k)) := by
  classical
  exact Finset.univ.filter fun x' => x' ∉ G.Ω 1 ∧ ∃ x ∈ G.Ω 1, Adj x x'

theorem mem_collar {x' : Torus d (N₀ * L ^ k)} :
    x' ∈ collar G ↔ x' ∉ G.Ω 1 ∧ ∃ x ∈ G.Ω 1, Adj x x' := by
  classical
  simp [collar]

/-- `Ω₁ ∪ C(Ω₁)`: the sites on which the data live. -/
noncomputable def dataSites : Finset (Torus d (N₀ * L ^ k)) := G.Ω 1 ∪ collar G

theorem mem_dataSites {x : Torus d (N₀ * L ^ k)} : x ∈ dataSites G ↔ x ∈ G.Ω 1 ∨ x ∈ collar G := by
  simp [dataSites]

/-- A neighbour of a site of `Ω₁` that is not in `Ω₁` lies in the collar. -/
theorem mem_collar_of_adj {x x' : Torus d (N₀ * L ^ k)} (hx : x ∈ G.Ω 1) (hx' : x' ∉ G.Ω 1)
    (h : Adj x x') : x' ∈ collar G :=
  (mem_collar G).2 ⟨hx', x, hx, h⟩

/-- The layer index is `0` off `Ω₁` (in particular on the collar, the "layer 0" of P2). -/
theorem layerIndex_of_not_mem {x : Torus d (N₀ * L ^ k)} (hx : x ∉ G.Ω 1) :
    G.layerIndex x = 0 := by
  classical
  have h : ¬ ∃ j, 1 ≤ j ∧ j ≤ k ∧ x ∈ G.layer j := by
    rintro ⟨j, hj1, hjk, hxj⟩
    exact hx (G.layer_subset hj1 hjk hxj)
  simp [GeneratingSet.layerIndex, h]

/-- The block of a site: the `n`-block `B_n(x) ⊆ Ω₁` if `x` is in layer `n ≥ 1`, and the single
site `{x}` for a collar site (a block of layer `0`, side `1`). -/
noncomputable def blockSet (x : Torus d (N₀ * L ^ k)) : Finset (Torus d (N₀ * L ^ k)) := by
  classical
  exact if x ∈ G.Ω 1 then G.blk (G.layerIndex x) x else {x}

/-- Two blocks (of sites of `Ω₁ ∪ C`) are *adjacent* if some sites of them are neighbours. -/
def BlocksAdjacent (x x' : Torus d (N₀ * L ^ k)) : Prop :=
  ∃ y ∈ blockSet G x, ∃ y' ∈ blockSet G x', Adj y y'

/-- The pairs of blocks of the interface condition (R1)/(C1): `n' = n` or `n' = n - 1`, adjacent,
where `n`, `n'` are the layer indices (`0` on the collar). -/
def IsInterfacePair (x x' : Torus d (N₀ * L ^ k)) : Prop :=
  x ∈ dataSites G ∧ x' ∈ dataSites G ∧
    (G.layerIndex x' = G.layerIndex x ∨ G.layerIndex x' + 1 = G.layerIndex x) ∧
    BlocksAdjacent G x x'

end Sites

/-- A field is *constant on the blocks of every layer* `1 ≤ n ≤ k` (the lifted block-spin fields
`Ψ = Q* ψ` of P2, constant on every `n`-block of layer `n`). -/
def IsLayerConstant {β : Type*} (G : GeneratingSet d L N₀ k ϱ)
    (Ψ : Torus d (N₀ * L ^ k) → β) : Prop :=
  ∀ n, 1 ≤ n → n ≤ k → ∀ x ∈ G.layer n, ∀ x' ∈ G.blk n x, Ψ x' = Ψ x

section Data

variable (G : GeneratingSet d L N₀ k ϱ) (N : ℕ)

/-- **The data** `(Ψ, h̃)` of the variational problem (BACKGROUND.md §1.2, §7): a lifted
block-spin field `Ψ : 𝕋 → ℂ^N` constant on the blocks of every layer (arbitrary on the collar)
and a field `h̃` on `Ω₁` constant on the blocks.  Only the values on `Ω₁ ∪ C` (resp. `Ω₁`) enter;
elsewhere the fields are `0`.  Real data have `IsReal`. -/
structure BgData where
  /-- The lifted field `Ψ`. -/
  Ψ : Torus d (N₀ * L ^ k) → Fin N → ℂ
  /-- The field `h̃`. -/
  h : Torus d (N₀ * L ^ k) → Fin N → ℂ
  Ψ_layerConst : IsLayerConstant G Ψ
  h_layerConst : IsLayerConstant G h
  Ψ_zero : ∀ x, x ∉ dataSites G → Ψ x = 0
  h_zero : ∀ x, x ∉ G.Ω 1 → h x = 0

variable {G N}

/-- Real data. -/
def BgData.IsReal (D : BgData G N) : Prop :=
  ∀ x i, (D.Ψ x i).im = 0 ∧ (D.h x i).im = 0

end Data

section Source

variable (G : GeneratingSet d L N₀ k ϱ) {N : ℕ}

/-- `(Q* a Ψ)(x) = a_n L^{-2n} Ψ(x)` for `x` in layer `n` (BACKGROUND.md (1.1), first term). -/
noncomputable def qStar (a : ℕ → ℝ) (Ψ : Torus d (N₀ * L ^ k) → Fin N → ℂ) :
    G.Ω 1 × Fin N → ℂ := fun p =>
  ((a (G.layerIndex (p.1 : Torus d (N₀ * L ^ k))) /
    ((L : ℝ) ^ G.layerIndex (p.1 : Torus d (N₀ * L ^ k))) ^ 2 : ℝ) : ℂ) * Ψ p.1 p.2

/-- The collar term `𝔟(Ψ)(x) = ∑_{x' ∈ C, x' ∼ x} Ψ(x')` (BACKGROUND.md (1.1), third term; the
sum runs over the `2d` directions `x ± e_μ`, with multiplicity, as in `-Δ`). -/
noncomputable def boundaryTerm (Ψ : Torus d (N₀ * L ^ k) → Fin N → ℂ) : G.Ω 1 × Fin N → ℂ :=
  fun p => ∑ μ : Fin d,
    ((if (p.1 : Torus d (N₀ * L ^ k)) + Pi.single μ 1 ∈ collar G then
        Ψ ((p.1 : Torus d (N₀ * L ^ k)) + Pi.single μ 1) p.2 else 0) +
      (if (p.1 : Torus d (N₀ * L ^ k)) - Pi.single μ 1 ∈ collar G then
        Ψ ((p.1 : Torus d (N₀ * L ^ k)) - Pi.single μ 1) p.2 else 0))

/-- **The source** `S(Ψ, h̃)(x) = a_n L^{-2n} Ψ(x) + ν h̃(x) + ∑_{x' ∈ C, x' ∼ x} Ψ(x')`
for `x ∈ Ω₁`, `n = n(x)` (BACKGROUND.md (1.1); `ν` is the mass `μ` of BACKGROUND.md in fine
units). -/
noncomputable def source (a : ℕ → ℝ) (ν : ℝ) (D : BgData G N) : G.Ω 1 × Fin N → ℂ := fun p =>
  qStar G a D.Ψ p + (ν : ℂ) * D.h p.1 p.2 + boundaryTerm G D.Ψ p

end Source

section Action

variable (G : GeneratingSet d L N₀ k ϱ) {N : ℕ}

/-- The block average `(Q_n φ)(x) = L^{-nd} ∑_{y ∈ B_n(x)} φ(y)` of a field on `Ω₁`
(zero extended), `n = n(x)` the layer of `x`. -/
noncomputable def blockAvg (φ : G.Ω 1 × Fin N → ℂ) (x : Torus d (N₀ * L ^ k)) (i : Fin N) : ℂ :=
  ((((((L : ℝ) ^ G.layerIndex x) ^ d)⁻¹ : ℝ) : ℂ)) * ∑ y ∈ G.blk (G.layerIndex x) x, svec G φ y i

/-- The extension `φ̄` of a field `φ` on `Ω₁` by the data `Ψ` outside `Ω₁`. -/
noncomputable def barField (Ψ : Torus d (N₀ * L ^ k) → Fin N → ℂ) (φ : G.Ω 1 × Fin N → ℂ)
    (x : Torus d (N₀ * L ^ k)) (i : Fin N) : ℂ := by
  classical
  exact if h : x ∈ G.Ω 1 then φ (⟨x, h⟩, i) else Ψ x i

/-- **The action** `A(φ)` of (1.2) at `λ = ∞`, in fine units:
`A(φ) = ½ ∑_{x ∈ Ω₁} a_n L^{-2n} |Ψ(x) - (Q_n φ)(x)|² + ½ ∑_b |∂φ̄(b)|² + (ν/2) ∑_{x ∈ Ω₁} |φ(x) - h̃(x)|²`
(the sum over bonds `b` with an endpoint in `Ω₁`; the first term is
`½ ∑_n ∑_{y ∈ Λ_n} a_n L^{-2n} L^{nd} |ψ_n(y) - (Q_n φ)(y)|²` written on sites).
Meaningful for real data and real `φ`; the norms are those of `ℂ^N`. -/
noncomputable def action (a : ℕ → ℝ) (ν : ℝ) (D : BgData G N) (φ : G.Ω 1 × Fin N → ℂ) : ℝ :=
  (1 / 2) * ∑ x : G.Ω 1, (a (G.layerIndex (x : Torus d (N₀ * L ^ k))) /
      ((L : ℝ) ^ G.layerIndex (x : Torus d (N₀ * L ^ k))) ^ 2) *
      ∑ i, ‖D.Ψ x i - blockAvg G φ x i‖ ^ 2 +
  (1 / 2) * ∑ x : Torus d (N₀ * L ^ k), ∑ μ : Fin d,
      (if x ∈ G.Ω 1 ∨ x + Pi.single μ 1 ∈ G.Ω 1 then
        ∑ i, ‖barField G D.Ψ φ (x + Pi.single μ 1) i - barField G D.Ψ φ x i‖ ^ 2 else 0) +
  ν / 2 * ∑ x : G.Ω 1, ∑ i, ‖φ (x, i) - D.h x i‖ ^ 2

/-- `φ` is a field of unit vectors of `ℝ^N` on `Ω₁`: `φ ∈ (S^{N-1})^{Ω₁}`. -/
def IsRealUnitField (φ : G.Ω 1 × Fin N → ℂ) : Prop :=
  ∀ x : G.Ω 1, (∀ i, (φ (x, i)).im = 0) ∧ ∑ i, ‖φ (x, i)‖ ^ 2 = 1

variable (a : ℕ → ℝ) (ν : ℝ)

/-- **The Euler–Lagrange system (EL)** (BACKGROUND.md §1.2, P2 (1.7)–(1.10) at `λ = ∞`):
`H_D(α) φ = S(Ψ, h̃)` and the bilinear constraint `φ · φ = 1` on `Ω₁`.  Here `H_D(α)` acts on
each of the `N` components (`liftOp`), and `φ : Ω₁ × [N] → ℂ`, `α : Ω₁ → ℂ`. -/
def IsEL (D : BgData G N) (φ : G.Ω 1 × Fin N → ℂ) (α : G.Ω 1 → ℂ) : Prop :=
  liftOp N (dirichletOperator G a ν α) *ᵥ φ = source G a ν D ∧
    ∀ x : G.Ω 1, ∑ i, φ (x, i) * φ (x, i) = 1

/-- **Small solutions** (Def-5(b); BACKGROUND.md §1.2): a solution of (EL) with
`|α|₂ < c₀`, i.e. `ℓ(x)² |α(x)| < c₀`.  The constant `c₀` is a parameter. -/
def IsSmallSolution (c₀ : ℝ) (D : BgData G N) (φ : G.Ω 1 × Fin N → ℂ) (α : G.Ω 1 → ℂ) : Prop :=
  IsEL G a ν D φ α ∧
    ∀ x : G.Ω 1, G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 * ‖α x‖ < c₀

/-- **Minimizers** (Def-5(a); BACKGROUND.md §1.2, §7): for real data, `φ ∈ (S^{N-1})^{Ω₁}` with
`A(φ) ≤ A(σ)` for all `σ ∈ (S^{N-1})^{Ω₁}`. -/
def IsMinimizer (D : BgData G N) (φ : G.Ω 1 × Fin N → ℂ) : Prop :=
  D.IsReal ∧ IsRealUnitField G φ ∧
    ∀ σ : G.Ω 1 × Fin N → ℂ, IsRealUnitField G σ → action G a ν D φ ≤ action G a ν D σ

end Action


section Clip

variable (G : GeneratingSet d L N₀ k ϱ) {N : ℕ}

/-- The constructor of `BgData`: fields that are constant on the blocks of every layer are
cut off to `0` outside `Ω₁ ∪ C` (resp. `Ω₁`).  Values elsewhere never enter. -/
noncomputable def BgData.clip (Ψ h : Torus d (N₀ * L ^ k) → Fin N → ℂ)
    (hΨ : IsLayerConstant G Ψ) (hh : IsLayerConstant G h) : BgData G N where
  Ψ := fun x => by classical exact if x ∈ dataSites G then Ψ x else 0
  h := fun x => by classical exact if x ∈ G.Ω 1 then h x else 0
  Ψ_layerConst := by
    intro n hn1 hnk x hx x' hx'
    have hx1 : x ∈ G.Ω 1 := G.layer_subset hn1 hnk hx
    have hx'l : x' ∈ G.layer n := (G.mem_layer_iff hn1 hnk (G.mem_blk.1 hx')).2 hx
    have hx'1 : x' ∈ G.Ω 1 := G.layer_subset hn1 hnk hx'l
    have h1 : x ∈ dataSites G := (mem_dataSites G).2 (Or.inl hx1)
    have h2 : x' ∈ dataSites G := (mem_dataSites G).2 (Or.inl hx'1)
    simp only [h1, h2, ↓reduceIte]
    exact hΨ n hn1 hnk x hx x' hx'
  h_layerConst := by
    intro n hn1 hnk x hx x' hx'
    have hx1 : x ∈ G.Ω 1 := G.layer_subset hn1 hnk hx
    have hx'l : x' ∈ G.layer n := (G.mem_layer_iff hn1 hnk (G.mem_blk.1 hx')).2 hx
    have hx'1 : x' ∈ G.Ω 1 := G.layer_subset hn1 hnk hx'l
    simp only [hx1, hx'1, ↓reduceIte]
    exact hh n hn1 hnk x hx x' hx'
  Ψ_zero := fun x hx => by simp [hx]
  h_zero := fun x hx => by simp [hx]

end Clip

section Domains

variable (G : GeneratingSet d L N₀ k ϱ) {N : ℕ}

/-- **The real data domain `Ψ̃(𝔹_k; δ)`** (P2 (1.11); BACKGROUND.md §1.3), with the constant
`h ∈ ℝ^N`, mass `ν = μ` (fine units, so P2's `ν` is `ν L^{2k}`):

* (R1) `|ψ_n(y) - ψ_{n'}(y')| < δ` for adjacent blocks of layers `n' = n` or `n' = n - 1`
  (`IsInterfacePair`; this contains the collar bonds);
* (R2) `| |ψ_n(y)|² - 1 | < δ`, `0 ≤ n ≤ k`;
* (R3) `ν L^{2n} |1 - (ψ_n(y))₀ · h| < δ²`, `0 ≤ n ≤ k`, `(ψ)₀ = ψ / |ψ|`;
* (R4) `ν L^{2k} | h · h - 1 | < δ²`.

Faithfulness notes (BACKGROUND.md §10 Q1): (i) (R1) is imposed for *adjacent* blocks, which is
equivalent up to a factor `C(d, L)` to the condition of P2 on all `(j-1)`-blocks of the
neighbouring cell; (ii) the collar is the one-site collar `C(Ω₁)`, whereas P2 p. 610 has a band
of big blocks around `Ω₁`; the equations see only sites adjacent to `Ω₁`, so the theorem is the
same with a weaker hypothesis, but it is a different predicate. -/
structure InPsiTilde (ν δ : ℝ) (Ψ : Torus d (N₀ * L ^ k) → Fin N → ℝ) (h : Fin N → ℝ) : Prop where
  layerConst : IsLayerConstant G Ψ
  r1 : ∀ x x', IsInterfacePair G x x' → rn (fun i => Ψ x i - Ψ x' i) < δ
  r2 : ∀ x ∈ dataSites G, |∑ i, Ψ x i ^ 2 - 1| < δ
  r3 : ∀ x ∈ dataSites G, ν * ((L : ℝ) ^ G.layerIndex x) ^ 2 *
    |1 - (∑ i, Ψ x i * h i) / rn (Ψ x)| < δ ^ 2
  r4 : ν * ((L : ℝ) ^ k) ^ 2 * |∑ i, h i ^ 2 - 1| < δ ^ 2

/-- **The complex data domain `Ψ̃^c(𝔹_k; δ, ε)`** (P2 (1.12); BACKGROUND.md §1.3): the real pair
`(Ψ, h) ∈ Ψ̃(𝔹_k; δ)` together with the complex perturbations `Ψ'` (layers `0..k`) and `h'`
(block-constant field on `Ω₁`), with

* (C1) `|ψ'_n(y) - ψ'_{n'}(y')| < δ` for the adjacent pairs of (R1);
* (C2) `|ψ'_n| < ε + δ` and `|(ψ_n + ψ'_n)·(ψ_n + ψ'_n) - ψ_n·ψ_n| < δ`;
* (C3) `ν L^{2n} |h'_n| < δ² / ε` and `ν L^{2n} |(ψ_n)₀ · h'_n| < δ²`.

`h'` is a block-constant field (P2 (1.16) writes `Q* h'`); the open complex domain of Theorem 5.2
is the union over admissible `(δ, ε)` (`InDomainC` below). -/
structure InPsiTildeC (ν δ ε : ℝ) (Ψ : Torus d (N₀ * L ^ k) → Fin N → ℝ) (h : Fin N → ℝ)
    (Ψ' h' : Torus d (N₀ * L ^ k) → Fin N → ℂ) : Prop extends InPsiTilde G ν δ Ψ h where
  eps_pos : 0 < ε
  layerConst' : IsLayerConstant G Ψ'
  hLayerConst' : IsLayerConstant G h'
  c1 : ∀ x x', IsInterfacePair G x x' → vn (Ψ' x - Ψ' x') < δ
  c2a : ∀ x ∈ dataSites G, vn (Ψ' x) < ε + δ
  c2b : ∀ x ∈ dataSites G,
    ‖∑ i, ((Ψ x i : ℂ) + Ψ' x i) * ((Ψ x i : ℂ) + Ψ' x i) - ∑ i, (Ψ x i : ℂ) * (Ψ x i : ℂ)‖ < δ
  c3a : ∀ x ∈ G.Ω 1, ν * ((L : ℝ) ^ G.layerIndex x) ^ 2 * vn (h' x) < δ ^ 2 / ε
  c3b : ∀ x ∈ G.Ω 1, ν * ((L : ℝ) ^ G.layerIndex x) ^ 2 *
    ‖∑ i, ((Ψ x i / rn (Ψ x) : ℝ) : ℂ) * h' x i‖ < δ ^ 2

/-- Membership of `BgData` in the real domain `Ψ̃(𝔹_k; δ)`. -/
def InDomainR (ν δ : ℝ) (D : BgData G N) : Prop :=
  ∃ (Ψ : Torus d (N₀ * L ^ k) → Fin N → ℝ) (h : Fin N → ℝ), InPsiTilde G ν δ Ψ h ∧
    (∀ x ∈ dataSites G, ∀ i, D.Ψ x i = (Ψ x i : ℂ)) ∧ ∀ x ∈ G.Ω 1, ∀ i, D.h x i = (h i : ℂ)

/-- Membership of `BgData` (data `Ψ + Ψ'`, `h̃ = h + h'`) in the complex domain
`Ψ̃^c(𝔹_k; δ, ε)`. -/
def InDomainC (ν δ ε : ℝ) (D : BgData G N) : Prop :=
  ∃ (Ψ : Torus d (N₀ * L ^ k) → Fin N → ℝ) (h : Fin N → ℝ)
    (Ψ' h' : Torus d (N₀ * L ^ k) → Fin N → ℂ), InPsiTildeC G ν δ ε Ψ h Ψ' h' ∧
    (∀ x ∈ dataSites G, ∀ i, D.Ψ x i = (Ψ x i : ℂ) + Ψ' x i) ∧
    ∀ x ∈ G.Ω 1, ∀ i, D.h x i = (h i : ℂ) + h' x i

/-- **The open union `𝒟(G, a, μ)`** of the complex domains over the admissible parameters of
Theorem 5.2 (BACKGROUND.md §7): `0 < δ ≤ ε ≤ c₀`, `δ ≤ c₁`, `ν L^{2k} ε² ≤ δ²`. -/
def InUnionDomainC (c₀ c₁ ν : ℝ) (D : BgData G N) : Prop :=
  ∃ δ ε : ℝ, 0 < δ ∧ δ ≤ ε ∧ ε ≤ c₀ ∧ δ ≤ c₁ ∧ ν * ((L : ℝ) ^ k) ^ 2 * ε ^ 2 ≤ δ ^ 2 ∧
    InDomainC G ν δ ε D

/-- The real domain `𝒟_ℝ` of Theorem 7.1: `δ ≤ c₁`. -/
def InUnionDomainR (c₁ ν : ℝ) (D : BgData G N) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ δ ≤ c₁ ∧ InDomainR G ν δ D

end Domains

end Balaban.Background
