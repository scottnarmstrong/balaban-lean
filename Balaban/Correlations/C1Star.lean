/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Correlations.Clauses
public import Balaban.Correlations.Box
public import Balaban.Correlations.Estimates
public import Balaban.Correlations.TermKernel
public import Balaban.Correlations.RootCStatement
public import Balaban.Flow.RunningCoefficients
public import Balaban.Model.BlockStructure

/-!
# The interface C-1* (observable form of the flow, finite-torus form)

CORRELATIONS.md §2.2.  Not frozen: this is the candidate interface that the flow must deliver to
Root-C, written down exactly so that `rootC_of_rootF_c1Star` (`Balaban/Correlations/Assembly.lean`)
tests it.

The integers `L, M` are those of Root-F at `κ = κ_*`, `c₉ = 1` (the structure is stated for
arbitrary `L, M`; the tie to Root-F is made in `RootFAndC1Star`).  The constants
`a, γ₀, c_*, c_ξ, c', ρ₀, ρ₁, β_*` and the scale function `J` come before `β`; for every
`β ≥ β_*` the flow provides, as in the document,

* `ξ ν k ∈ ℝ³` (the running coefficients `ξ^{(k)}(ν)`, real; `Balaban.Flow` sequences are formed
  with the complexification `xiC ξ`), `μ j ν x` (`μ_j(ν; x)`), the remainders `rtr ℓ ν x y`,
  `rlg ℓ ν x y` (`r^ℓ_{tr}, r^ℓ_{lg}`) and `em ℓ ν x` (`e^ℓ_m`);
* (F1) `C1StarF1`: the bound `‖ξ(ν)_k‖ ≤ c_ξ/(4β) q^{k+1}`, `q = L^{-2γ₀}`, and continuity of
  `ν ↦ ξ(ν)_k` at `ν = 0`;
* (F2) `C1StarF2`: `|μ_j| ≤ c_* β^{-1/2+ρ₁} L^{-jρ₀}`, continuity of `ν ↦ μ_j(ν; x)` at `0`, and
  `m_ℓ = m_J(ν; x) + e^ℓ_m` with `|e^ℓ_m| ≤ c_* β^{-2} L^{-2J(d-2)}` on the tori `M L^{J+1} ∣ ℓ`;
* (F3) `C1StarF3`: the two-point decomposition `G_{tr,ℓ} = m_J m_J ∑_{j<J} (β γ_j)⁻¹ T_j^{ℓ, ν δ_j} + r_{tr}`,
  `G_{lg,ℓ} = r_{lg}`, the bounds on `r`, the existence of the limits of `r^ℓ` along the tori
  `(M L)^n ∣ ℓ` (`rtrLim`, `rlgLim`; the document lists them "to fix the family") and of their
  limits as `ν ↓ 0` (`rtrZero`, `rlgZero`).

(F4) (the Ward identity) is not a hypothesis.  The indices: `μ_j` is indexed as in the document,
`j ≥ 1`; the sum `∑_{j=1}^J β_{j-1}^{-1/2} μ_j` is written `∑_{j<J} (√β_j)⁻¹ μ_{j+1}`.
-/

@[expose] public section

open Filter Topology Finset

namespace Balaban.Correlations

open Balaban Balaban.Flow

/-- A real function of the tori `ℓ` converges to `A` along the tori with side divisible by `q^n`. -/
def LimAlong (q : ℕ) (f : (ℓ : ℕ) → [NeZero ℓ] → ℝ) (A : ℝ) : Prop :=
  ∀ ε > 0, ∃ n₀ : ℕ, ∀ (ℓ : ℕ) [NeZero ℓ], q ^ n₀ ∣ ℓ → |f ℓ - A| < ε

/-- The complexification of a real sequence of running coefficients. -/
def xiC (ξ : ℕ → Fin 3 → ℝ) : ℕ → Fin 3 → ℂ := fun k i => (ξ k i : ℂ)

/-- `γ_j = ∏_{i<j} (1 + ξ_i(2))⁻¹` (real part of `gammaSeq`). -/
noncomputable def gammaR (ξ : ℕ → Fin 3 → ℝ) (j : ℕ) : ℝ := (gammaSeq (xiC ξ) j).re

/-- `δ_j = ∏_{i<j} (1 + ξ_i(2))/(1 + ξ_i(1))` (real part of `deltaSeq`). -/
noncomputable def deltaR (ξ : ℕ → Fin 3 → ℝ) (j : ℕ) : ℝ := (deltaSeq (xiC ξ) j).re

/-- `β_j` (real part of `betaSeq`). -/
noncomputable def betaR (L d : ℕ) (ξ : ℕ → Fin 3 → ℝ) (β : ℝ) (j : ℕ) : ℝ :=
  (betaSeq (L : ℝ) d (xiC ξ) (β : ℂ) j).re

/-- `m_J(ν; x) = 1 - ∑_{j=1}^{J} β_{j-1}^{-1/2} μ_j(ν; x)`, for the sequence `ξ = ξ(ν)` and
`μ_j = μ_j(ν; ·)`. -/
noncomputable def magJ (L d : ℕ) (ξ : ℕ → Fin 3 → ℝ) (μ : ℕ → (Fin d → ℤ) → ℝ) (β : ℝ)
    (J : ℕ) (x : Fin d → ℤ) : ℝ :=
  1 - ∑ j ∈ range J, (Real.sqrt (betaR L d ξ β j))⁻¹ * μ (j + 1) x

/-- `∑_{j<J} (β γ_j)⁻¹ T_j^{ℓ, ν δ_j}(x, y)` on the torus `ℓ = L^J (m + 1)`, `m = ℓ / L^J - 1`. -/
noncomputable def mainTr (d L : ℕ) [NeZero L] (a : ℝ) (ξ : ℕ → Fin 3 → ℝ) (β ν : ℝ) (J ℓ : ℕ)
    (x y : Fin d → ℤ) : ℝ :=
  ∑ j ∈ range J, (β * gammaR ξ j)⁻¹ *
    termKernel d L (freeSeq d L a) (ν * deltaR ξ j) J j (ℓ / L ^ J - 1) x y

/-- (F1): the running coefficients. -/
def C1StarF1 (L : ℕ) (γ₀ cXi β : ℝ) (ξ : ℝ → ℕ → Fin 3 → ℝ) : Prop :=
  (∀ ν ∈ Set.Icc (0 : ℝ) 1, ∀ k, ‖ξ ν k‖ ≤ cXi / (4 * β) * rate (L : ℝ) γ₀ ^ (k + 1)) ∧
  ∀ k, Tendsto (fun ν => ξ ν k) (𝓝[>] 0) (𝓝 (ξ 0 k))

/-- (F2): the one-point function. -/
def C1StarF2 (d N L M : ℕ) [NeZero L] (hN : 2 ≤ N) (cStar ρ₀ ρ₁ : ℝ) (J : ℝ → ℕ) (β : ℝ)
    (ξ : ℝ → ℕ → Fin 3 → ℝ) (μ : ℕ → ℝ → (Fin d → ℤ) → ℝ)
    (em : ℕ → ℝ → (Fin d → ℤ) → ℝ) : Prop :=
  (∀ j, 1 ≤ j → ∀ ν ∈ Set.Icc (0 : ℝ) 1, ∀ x,
    |μ j ν x| ≤ cStar * β ^ (-(1 / 2 : ℝ) + ρ₁) * (L : ℝ) ^ (-((j : ℝ) * ρ₀))) ∧
  (∀ j x, Tendsto (fun ν => μ j ν x) (𝓝[>] 0) (𝓝 (μ j 0 x))) ∧
  ∀ ν ∈ Set.Ioc (0 : ℝ) 1, ∀ x, ∀ (ℓ : ℕ) [NeZero ℓ], M * L ^ (J ν + 1) ∣ ℓ →
    blockM d N ℓ hN β ν = magJ L d (ξ ν) (fun j => μ j ν) β (J ν) x + em ℓ ν x ∧
    |em ℓ ν x| ≤ cStar * (β ^ 2)⁻¹ * ((L : ℝ) ^ (2 * J ν * (d - 2)))⁻¹

/-- (F3): the two-point function. -/
def C1StarF3 (d N L M : ℕ) [NeZero L] (hN : 2 ≤ N) (a cStar cPrime ρ₀ : ℝ) (J : ℝ → ℕ) (β : ℝ)
    (ξ : ℝ → ℕ → Fin 3 → ℝ) (μ : ℕ → ℝ → (Fin d → ℤ) → ℝ)
    (rtr rlg : ℕ → ℝ → (Fin d → ℤ) → (Fin d → ℤ) → ℝ)
    (rtrLim rlgLim : ℝ → (Fin d → ℤ) → (Fin d → ℤ) → ℝ)
    (rtrZero rlgZero : (Fin d → ℤ) → (Fin d → ℤ) → ℝ) : Prop :=
  (∀ ν ∈ Set.Ioc (0 : ℝ) 1, ∀ x y : Fin d → ℤ, ∀ (ℓ : ℕ) [NeZero ℓ], M * L ^ (J ν + 1) ∣ ℓ →
    (∀ i, 2 * |(x - y) i| < (ℓ : ℤ)) →
    blockGtr d N ℓ hN β ν (embedZ ℓ (x - y)) =
      magJ L d (ξ ν) (fun j => μ j ν) β (J ν) x * magJ L d (ξ ν) (fun j => μ j ν) β (J ν) y *
        mainTr d L a (ξ ν) β ν (J ν) ℓ x y + rtr ℓ ν x y ∧
    blockGlg d N ℓ hN β ν (embedZ ℓ (x - y)) = rlg ℓ ν x y ∧
    |rtr ℓ ν x y| ≤ cStar * (1 + ‖x - y‖) ^ (-((d : ℝ) - 2 + ρ₀)) *
      Real.exp (-(cPrime * Real.sqrt ν * ‖x - y‖)) ∧
    |rlg ℓ ν x y| ≤ cStar * (1 + ‖x - y‖) ^ (-((d : ℝ) - 2 + ρ₀)) *
      Real.exp (-(cPrime * Real.sqrt ν * ‖x - y‖))) ∧
  (∀ ν ∈ Set.Ioc (0 : ℝ) 1, ∀ x y,
    LimAlong (M * L) (fun ℓ _ => rtr ℓ ν x y) (rtrLim ν x y) ∧
    LimAlong (M * L) (fun ℓ _ => rlg ℓ ν x y) (rlgLim ν x y)) ∧
  (∀ x y, Tendsto (fun ν => rtrLim ν x y) (𝓝[>] 0) (𝓝 (rtrZero x y)) ∧
    Tendsto (fun ν => rlgLim ν x y) (𝓝[>] 0) (𝓝 (rlgZero x y)))

/-- **The interface C-1\*** (CORRELATIONS.md §2.2, (F1)–(F3), finite-torus form; `L, M` are the
integers of Root-F at `κ = κ_*`, `c₉ = 1`).  The constants come before `β`. -/
structure C1Star (d N L M : ℕ) [NeZero L] (hN : 2 ≤ N) where
  /-- The free-flow constant `a`. -/
  a : ℝ
  /-- The rate exponent: `q = L^{-2γ₀}`. -/
  γ₀ : ℝ
  cStar : ℝ
  cXi : ℝ
  cPrime : ℝ
  ρ₀ : ℝ
  ρ₁ : ℝ
  βStar : ℝ
  /-- The last scale `J(ν)`. -/
  J : ℝ → ℕ
  a_range : 1 / (2 * (1 - ((L : ℝ) ^ 2)⁻¹)) < a ∧ a < 3 / 2
  γ₀_range : 0 < γ₀ ∧ γ₀ ≤ 1 / 2
  cStar_pos : 0 < cStar
  cXi_pos : 0 < cXi
  cPrime_pos : 0 < cPrime
  ρ₀_range : 0 < ρ₀ ∧ ρ₀ ≤ (d : ℝ) - 2
  ρ₁_range : 0 < ρ₁ ∧ ρ₁ < 1
  J_pos : ∀ ν ∈ Set.Ioc (0 : ℝ) 1, 1 ≤ J ν
  J_tendsto : Tendsto J (𝓝[>] 0) atTop
  J_bounds : ∀ ν ∈ Set.Ioc (0 : ℝ) 1,
    1 / 2 ≤ (L : ℝ) ^ J ν * Real.sqrt ν ∧ (L : ℝ) ^ J ν * Real.sqrt ν ≤ (L : ℝ) ^ 2
  data : ∀ β : ℝ, βStar ≤ β →
    ∃ (ξ : ℝ → ℕ → Fin 3 → ℝ) (μ : ℕ → ℝ → (Fin d → ℤ) → ℝ)
      (rtr rlg : ℕ → ℝ → (Fin d → ℤ) → (Fin d → ℤ) → ℝ) (em : ℕ → ℝ → (Fin d → ℤ) → ℝ)
      (rtrLim rlgLim : ℝ → (Fin d → ℤ) → (Fin d → ℤ) → ℝ)
      (rtrZero rlgZero : (Fin d → ℤ) → (Fin d → ℤ) → ℝ),
      C1StarF1 L γ₀ cXi β ξ ∧ C1StarF2 d N L M hN cStar ρ₀ ρ₁ J β ξ μ em ∧
      C1StarF3 d N L M hN a cStar cPrime ρ₀ J β ξ μ rtr rlg rtrLim rlgLim rtrZero rlgZero

/-- The joint hypothesis: Root-F's clauses at `κ = κ_*`, `c₉ = 1` for the integers `L, M`, and the
interface C-1* for the same `L, M`.  The eventual flow theorem supplies both from one construction
(the `L, M` of Root-F are the block factor and polymer multiplier of the flow). -/
def RootFAndC1Star (d N : ℕ) (hN : 2 ≤ N) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∃ L M : ℕ, ∃ hL : 2 ≤ L, 1 ≤ M ∧ ∃ β₀ : ℝ,
    (∀ β : ℝ, β₀ ≤ β → ∀ ν : ℝ, 0 < ν → ν ≤ 1 → ∀ h : EuclideanSpace ℝ (Fin N), ‖h‖ = 1 →
      ∃ kf : ℕ, (L : ℝ) ^ kf * Real.sqrt ν ≤ L ∧ 1 / 2 ≤ (L : ℝ) ^ (kf + 1) * Real.sqrt ν ∧
        ∃ T : RootFFamily d N, RootFClauses d N L M β ν h kf (kappaStar d) 1 δ T) ∧
    Nonempty (@C1Star d N L M ⟨by omega⟩ hN)

end Balaban.Correlations
