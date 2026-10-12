/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Background.ScaledComposition
public import Balaban.Background.Perturb
public import Balaban.Background.HolderFull
public import Balaban.Background.Theorem73
import Mathlib.Analysis.PSeries
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The analyticity spaces `Ξ_n(𝔹; σ, ε)`, `Ξ^c_n(𝔹; σ, ε)` at `λ = ∞` (SMALLFIELD.md v2 §1.7)

Definitions only.  The spaces are transcribed from P3 (4.25)-(4.28) as read in
`notes/phase1/SMALLFIELD.md` §1.7, through the background fields `bgField`, `bgMult`,
`bgFieldC`, `bgMultC` of `Balaban/Background/Def5.lean`.  Units are those of the generating set
(`ℓ(x) = G.spacing x`, `η = 1`).

* `Balaban.SmallField.XiBounds`: the inequalities on the real minimizer `(φ, α)`;
* `Balaban.SmallField.Xi`: the real space `Ξ_n(𝔹; σ, ε)`;
* `Balaban.SmallField.XiCBounds`, `Balaban.SmallField.XiC`: the complex space `Ξ^c_n(𝔹; σ, ε)`;
* `Balaban.SmallField.GapE`, `Balaban.SmallField.epsSeq`: the gap (E) on the sequence `(ε_j)`.

**Design decisions** (each is flagged in the docstring of the definition).

1. *Domain.*  `Ξ` requires membership of the datum in the union domain of Theorem 7.1
   (`InUnionDomainR`), `Ξ^c` in that of Theorem 7.2 (`InUnionDomainC`).  Without it `bgField` is
   the junk value `0` and the inequalities would hold vacuously.
2. *The collar.*  The data domains of `Background/Data.lean` have a one-site collar `C(Ω₁)`; the
   conditions on `∂φ̄` at the bonds with an endpoint in `Ω₁` do not see the bonds inside the
   collar, which (R1)/(C1) do.  The extra condition `collarBond` bounds the data across such bonds
   by `σ ε` (the value `ℓ = 1` of the collar), i.e. it is `|∂φ̄|₁ < σ ε` on all bonds of
   `Ω₁ ∪ C(Ω₁)`.
3. *Complex displacements.*  `Ξ^c` is formulated with the displacements
   `φ' = φ^c - φ^r`, `α' = α^c - α^r`, `Ψ' = Ψ^c - Ψ^r`, `h' = h^c - h^r`:
   "the complex displacements satisfy the same inequalities" is read as the gradient, Laplacian,
   multiplier and closeness inequalities for `φ̄^c - φ̄^r`, `α^c - α^r`, `Ψ' - Q φ'`, together
   with `|φ'| < ε`.
4. *UNCERTAIN (P3 (4.25) scan, SMALLFIELD §1.7).*  The conditions on `h'`
   are `ν ℓ² |h'| < (σ ε)² / ε` and `ν ℓ² |φ^r · h'| < (σ ε)²`
   (the printed `σ²ε/ε` is read as `(σε)²/ε`, which is the form of (C3) in `Background/Data.lean`).
   A mass condition `|φ' - h'| < σ ε / √ν` for the displacement is *not* included: it would not
   follow from the data domain `Ψ̃^c`.
5. *Mass of the level.*  The condition on `ν |h|² - 1` is `ν L^{2n} | |h|² - 1 | < (σ ε)²` with
   the level `n` as a parameter (`n = k` for the top level of the generating set, as in (R4)).
-/

@[expose] public section

namespace Balaban.SmallField

open Balaban.Background Balaban.Multiscale Matrix Finset

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

section Real

variable (G : GeneratingSet d L N₀ k ϱ)

/-- **The inequalities of `Ξ_n(𝔹; σ, ε)`** for a datum `D`, the constant `h₀`, and a field `φ` on
`Ω₁` with multiplier `α` (P3 (4.25)-(4.28) at `λ = ∞`; `φ̄ = barField` the extension of `φ` by `Ψ`):

* `grad`: `|∂φ̄(x)| < σ ε / ℓ(x)` in all `2d` directions;
* `lap`: `|Δφ̄(x)| < σ² ε / ℓ(x)²`;
* `mult`: `ℓ(x)² |α(x)| < σ² ε`;
* `close`: `|Ψ(x) - (Q φ)(x)| < σ² ε`;
* `collarBond`: `|Ψ(z) - Ψ(z')| < σ ε` for adjacent collar sites (see the module docstring);
* `mass`: `√ν ℓ(x) |φ(x) - h₀| < σ ε`;
* `hnorm`: `ν L^{2n} | |h₀|² - 1 | < (σ ε)²`. -/
structure XiBounds (ν : ℝ) (n : ℕ) (σ ε : ℝ) (D : BgData G N) (h₀ : Fin N → ℝ)
    (φ : G.Ω 1 × Fin N → ℂ) (α : G.Ω 1 → ℂ) : Prop where
  grad : ∀ x ∈ G.Ω 1, ∀ μ : Fin d,
    vn (fun i => barField G D.Ψ φ (x + Pi.single μ 1) i - barField G D.Ψ φ x i) <
      σ * ε / G.spacing x ∧
    vn (fun i => barField G D.Ψ φ (x - Pi.single μ 1) i - barField G D.Ψ φ x i) <
      σ * ε / G.spacing x
  lap : ∀ x ∈ G.Ω 1, vn (fun i => ∑ μ : Fin d,
    (barField G D.Ψ φ (x + Pi.single μ 1) i + barField G D.Ψ φ (x - Pi.single μ 1) i -
      2 * barField G D.Ψ φ x i)) < σ ^ 2 * ε / G.spacing x ^ 2
  mult : ∀ x : G.Ω 1, G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 * ‖α x‖ < σ ^ 2 * ε
  close : ∀ x ∈ G.Ω 1, vn (fun i => D.Ψ x i - blockAvg G φ x i) < σ ^ 2 * ε
  collarBond : ∀ z ∈ collar G, ∀ z' ∈ collar G, Adj z z' →
    vn (fun i => D.Ψ z i - D.Ψ z' i) < σ * ε
  mass : ∀ z : G.Ω 1, Real.sqrt ν * G.spacing (z : Torus d (N₀ * L ^ k)) *
    vn (fun i => φ (z, i) - (h₀ i : ℂ)) < σ * ε
  hnorm : ν * ((L : ℝ) ^ n) ^ 2 * |∑ i, h₀ i ^ 2 - 1| < (σ * ε) ^ 2

variable {G}

/-- A datum `D` realizes the real raw data `(Ψ₀, h₀)` of `Ω₁ ∪ C(Ω₁)`. -/
def Realizes (D : BgData G N) (Ψ₀ : Torus d (N₀ * L ^ k) → Fin N → ℝ) (h₀ : Fin N → ℝ) : Prop :=
  (∀ x ∈ dataSites G, ∀ i, D.Ψ x i = (Ψ₀ x i : ℂ)) ∧ ∀ x ∈ G.Ω 1, ∀ i, D.h x i = (h₀ i : ℂ)

variable (G)

/-- **`Ξ_n(𝔹; σ, ε)` at `λ = ∞`** (SMALLFIELD.md §1.7, P3 (4.25)-(4.28)): the real data
`(Ψ₀, h₀)` whose datum `D` lies in the real union domain `𝒟_ℝ` of Theorem 7.1 and whose background
field `(φ, α) = (bgField, bgMult)` satisfies the inequalities `XiBounds`.  The statement
`XiAt` is for a given realization `D`; `Xi` quantifies over it (it is unique, being
determined by the values on `Ω₁ ∪ C(Ω₁)`). -/
def XiAt (a : ℕ → ℝ) (ν : ℝ) (n : ℕ) (σ ε : ℝ) (D : BgData G N)
    (Ψ₀ : Torus d (N₀ * L ^ k) → Fin N → ℝ) (h₀ : Fin N → ℝ) : Prop :=
  Realizes D Ψ₀ h₀ ∧ InUnionDomainR G (bgC1 d L N) ν D ∧
    XiBounds G ν n σ ε D h₀ (bgField G a ν D) (bgMult G a ν D)

/-- **The space `Ξ_n(𝔹; σ, ε)`** (real data `(Ψ₀, h₀)`), `σ, ε > 0`. -/
def Xi (a : ℕ → ℝ) (ν : ℝ) (n : ℕ) (σ ε : ℝ) (Ψ₀ : Torus d (N₀ * L ^ k) → Fin N → ℝ)
    (h₀ : Fin N → ℝ) : Prop :=
  0 < σ ∧ 0 < ε ∧ ∃ D : BgData G N, XiAt G a ν n σ ε D Ψ₀ h₀

end Real

section Complex

variable (G : GeneratingSet d L N₀ k ϱ)

/-- **The inequalities of `Ξ^c_n(𝔹; σ, ε)`** for the complex datum `D^c` over the real datum `D^r`
with solutions `(φ^r, α^r)`, `(φ^c, α^c)`; `F = φ̄^c - φ̄^r` is the difference of the extensions
(`Ψ'' = Ψ^c - Ψ^r` on the collar, `φ^c - φ^r` on `Ω₁`), `Ψ''`, `h''` the displacements of the data
(see the module docstring, items 3 and 4). -/
structure XiCBounds (ν σ ε : ℝ) (Dr Dc : BgData G N) (Ψ'' h'' : Torus d (N₀ * L ^ k) → Fin N → ℂ)
    (φr φc : G.Ω 1 × Fin N → ℂ) (αr αc : G.Ω 1 → ℂ) : Prop where
  grad : ∀ x ∈ G.Ω 1, ∀ μ : Fin d,
    vn (fun i => (barField G Dc.Ψ φc (x + Pi.single μ 1) i - barField G Dr.Ψ φr (x + Pi.single μ 1) i) -
        (barField G Dc.Ψ φc x i - barField G Dr.Ψ φr x i)) < σ * ε / G.spacing x ∧
    vn (fun i => (barField G Dc.Ψ φc (x - Pi.single μ 1) i - barField G Dr.Ψ φr (x - Pi.single μ 1) i) -
        (barField G Dc.Ψ φc x i - barField G Dr.Ψ φr x i)) < σ * ε / G.spacing x
  lap : ∀ x ∈ G.Ω 1, vn (fun i => ∑ μ : Fin d,
    ((barField G Dc.Ψ φc (x + Pi.single μ 1) i - barField G Dr.Ψ φr (x + Pi.single μ 1) i) +
      (barField G Dc.Ψ φc (x - Pi.single μ 1) i - barField G Dr.Ψ φr (x - Pi.single μ 1) i) -
      2 * (barField G Dc.Ψ φc x i - barField G Dr.Ψ φr x i))) < σ ^ 2 * ε / G.spacing x ^ 2
  mult : ∀ x : G.Ω 1, G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 * ‖αc x - αr x‖ < σ ^ 2 * ε
  val : ∀ x : G.Ω 1, vn (fun i => φc (x, i) - φr (x, i)) < ε
  close : ∀ x ∈ G.Ω 1, vn (fun i => Ψ'' x i - blockAvg G (φc - φr) x i) < σ ^ 2 * ε
  collarBond : ∀ z ∈ collar G, ∀ z' ∈ collar G, Adj z z' →
    vn (fun i => Ψ'' z i - Ψ'' z' i) < σ * ε
  hAbs : ∀ x ∈ G.Ω 1, ν * ((L : ℝ) ^ G.layerIndex x) ^ 2 * vn (h'' x) < (σ * ε) ^ 2 / ε
  hDot : ∀ x : G.Ω 1, ν * ((L : ℝ) ^ G.layerIndex (x : Torus d (N₀ * L ^ k))) ^ 2 *
    ‖∑ i, φr (x, i) * h'' x i‖ < (σ * ε) ^ 2

variable {G}

/-- The complex datum `D^c` realizes `(Ψ₀ + Ψ'', h₀ + h'')`. -/
def RealizesC (D : BgData G N) (Ψ₀ : Torus d (N₀ * L ^ k) → Fin N → ℝ) (h₀ : Fin N → ℝ)
    (Ψ'' h'' : Torus d (N₀ * L ^ k) → Fin N → ℂ) : Prop :=
  (∀ x ∈ dataSites G, ∀ i, D.Ψ x i = (Ψ₀ x i : ℂ) + Ψ'' x i) ∧
    ∀ x ∈ G.Ω 1, ∀ i, D.h x i = (h₀ i : ℂ) + h'' x i

variable (G)

/-- **The space `Ξ^c_n(𝔹; σ, ε)`** at `λ = ∞` (SMALLFIELD.md §1.7, P3 (4.25)-(4.28)): the complex
data `(Ψ₀ + Ψ'', h₀ + h'')` with `(Ψ₀, h₀) ∈ Ξ_n(𝔹; σ, ε)` (realized by `D^r`), whose complex
datum `D^c` lies in the union domain `𝒟` of Theorem 7.2 (`InUnionDomainC`, `c₀ = bgC0`) and whose
displacements satisfy `XiCBounds` (for `(φ^c, α^c) = (bgFieldC, bgMultC)`). -/
def XiC (a : ℕ → ℝ) (ν : ℝ) (n : ℕ) (σ ε : ℝ) (Ψ₀ : Torus d (N₀ * L ^ k) → Fin N → ℝ)
    (h₀ : Fin N → ℝ) (Ψ'' h'' : Torus d (N₀ * L ^ k) → Fin N → ℂ) : Prop :=
  0 < σ ∧ 0 < ε ∧ ∃ Dr Dc : BgData G N, XiAt G a ν n σ ε Dr Ψ₀ h₀ ∧ RealizesC Dc Ψ₀ h₀ Ψ'' h'' ∧
    InUnionDomainC G (bgC0 d L N) (bgC1 d L N) ν Dc ∧
    XiCBounds G ν σ ε Dr Dc Ψ'' h'' (bgField G a ν Dr) (bgFieldC G a ν (bgC0 d L N) Dc)
      (bgMult G a ν Dr) (bgMultC G a ν (bgC0 d L N) Dc)

end Complex

section Gap

/-- **The gap condition (E)** on a sequence `(ε_j)`: `ε_{k+1} ≤ (1 - η_ε) ε_k` with
`η_ε = 1 - L^{-α}` (SMALLFIELD.md §1.7). -/
def GapE (L : ℕ) (α : ℝ) (ε : ℕ → ℝ) : Prop :=
  ∀ k, ε (k + 1) ≤ (1 - (1 - (L : ℝ) ^ (-α))) * ε k

/-- The tail `1 + ∑_{m ≥ j} m^{-2}` of the sequence of P4 (H.1). -/
noncomputable def epsTail (j : ℕ) : ℝ :=
  1 + ∑' m : ℕ, if j ≤ m then ((m : ℝ) ^ 2)⁻¹ else 0

/-- **The sequence** `ε_j = α₀ (1 + ∑_{m ≥ j} m^{-2}) L^{-jα}` (P4 (H.1), P3 p. 76). -/
noncomputable def epsSeq (L : ℕ) (α α₀ : ℝ) (j : ℕ) : ℝ :=
  α₀ * epsTail j * ((L : ℝ) ^ (-α)) ^ j

theorem summable_epsTail (j : ℕ) :
    Summable fun m : ℕ => if j ≤ m then ((m : ℝ) ^ 2)⁻¹ else 0 := by
  refine Summable.of_nonneg_of_le (fun m => ?_) (fun m => ?_)
    ((Real.summable_nat_pow_inv (p := 2)).2 (by norm_num))
  · split_ifs <;> positivity
  · split_ifs <;> simp

theorem epsTail_succ_le (j : ℕ) : epsTail (j + 1) ≤ epsTail j := by
  unfold epsTail
  have := Summable.tsum_le_tsum (f := fun m : ℕ => if j + 1 ≤ m then ((m : ℝ) ^ 2)⁻¹ else 0)
    (g := fun m : ℕ => if j ≤ m then ((m : ℝ) ^ 2)⁻¹ else 0)
    (fun m => by
      by_cases h : j + 1 ≤ m
      · have : j ≤ m := by omega
        simp [h, this]
      · simp only [h, ↓reduceIte]
        split_ifs <;> positivity)
    (summable_epsTail (j + 1)) (summable_epsTail j)
  linarith

theorem epsTail_pos (j : ℕ) : 0 < epsTail j := by
  unfold epsTail
  have : 0 ≤ ∑' m : ℕ, if j ≤ m then ((m : ℝ) ^ 2)⁻¹ else 0 :=
    tsum_nonneg fun m => by split_ifs <;> positivity
  linarith

/-- **(E) holds for the sequence of P4 (H.1)**: because `1 + ∑_{m ≥ k+1} m^{-2} ≤ 1 + ∑_{m ≥ k} m^{-2}`. -/
theorem epsSeq_gapE (L : ℕ) (α α₀ : ℝ) (hα₀ : 0 ≤ α₀) : GapE L α (epsSeq L α α₀) := by
  intro j
  unfold epsSeq
  have h1 := epsTail_succ_le j
  have hq : 0 ≤ (L : ℝ) ^ (-α) := Real.rpow_nonneg (Nat.cast_nonneg L) _
  have e : (1 - (1 - (L : ℝ) ^ (-α))) = (L : ℝ) ^ (-α) := by ring
  rw [e, pow_succ]
  have h2 : α₀ * epsTail (j + 1) * (((L : ℝ) ^ (-α)) ^ j * (L : ℝ) ^ (-α)) ≤
      α₀ * epsTail j * (((L : ℝ) ^ (-α)) ^ j * (L : ℝ) ^ (-α)) := by
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hα₀) ?_
    positivity
  calc _ ≤ _ := h2
    _ = _ := by ring

end Gap

end Balaban.SmallField
