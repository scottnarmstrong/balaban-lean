# Surface v1 — for author approval

**Def-1 (model), Def-2 (geometry), Root-F (the full RG flow, observable form) and Root-C (P9
Theorem 1.1 for hard spins).** Package **v1.2**, 2026-10-11, prepared by the orchestrator. v1.1
answers the independent audit `notes/phase0/surface-v1-audit.md` (verdict on v1.0: FAIL, two MAJOR
findings on Root-F; both fixed, see the changelog); v1.2 answers its re-audit (statements approved
as written; docstring and citation corrections).

**Nothing here is approved or frozen.** This is the exact Lean code proposed for the first freeze:
two roots and the eight definitions they use, one public declaration per file, under
`Balaban/Frozen/`, namespace `Balaban`. After approval the eight definitions are frozen as
`SEALED` (whole-file hash) and the two roots as `DRAFT_SORRY` (statement final, proof to come).

- **Sources.** P1 (CMP 167), P4 (CMP 182), P5, P7 (CMP 196, 198), P9 (CMP 199); keys and files in
  `review/SOURCES.md`. Page numbers are journal pages.
- **Plan.** `review/FORMALIZATION_ROADMAP.md` v2: §1.3 (the two roots), §3.1–3.2 (Def-1, Def-2,
  Root-F, Root-C), §3.5 (statement integrity), §4.4 (order of constants).
- **Elaboration.** All ten files build as modules in the scratch tree
  `/home/scott/Balaban-scratch/p0/tree` (a copy of the repository at `49825b5` plus these files at
  their final paths; Lean v4.35.0-rc2, Mathlib `065356127b1d`). The only diagnostics are the two
  expected `declaration uses 'sorry'` warnings on the roots (§3).

## Decisions requested

Each decision has a recommended default, which is the code of §2. "Audit" refers to
`notes/phase0/surface-v1-audit.md`.

| # | Decision | Recommended default (the code of §2) | Alternatives |
|---|---|---|---|
| **S0-Q01** | **The two roots** (roadmap §1.3). | **Root-F** (main deliverable): the multiscale representation of `log(Z(g)/Z(0))`, which certifies the full flow including large fields and needs no internal RG definitions. **Root-C** (final deliverable): P9 Thm 1.1 for hard spins. P7 Thm 5 (every density of the flow lies in P5's class) stays an interface (LF-7), frozen only after the large-field reconstruction (phase 1). | Freeze P7 Thm 5 as a root now (needs Def-7, which does not exist before the reconstruction). |
| **S0-Q02** | **Tori and the infinite-volume limit.** The series works on tori whose side is divisible by `ML^j` at every scale used (P1 p. 117); P9 writes `⟨·⟩ = lim_T ⟨·⟩_T` without saying along which tori (p. 494). | **Cubic tori `(ℤ/ℓℤ)^d` of every side.** Root-F holds on every torus with `M L^{k_f+1} ∣ ℓ`. Root-C's limits are taken along the tori whose side is divisible by `q^n`, `n → ∞`, for some `q ≥ 2` fixed with the constants (in the proof `q = ML`, or `q = L` when `M = L^m`). This implies the limits along `q^n` and along `n!` (Audit B.3, C-1). | (a) Any `ℓ₀`: "∀ε ∃ℓ₀ ∀ℓ, ℓ₀ ∣ ℓ → …" (v1.0; weaker: does not give the limit along `ML^n`). (b) Tori of side `ML^n` only. (c) All `ℓ → ∞`: not obtainable from the method (needs `ML^{k_f+1} ∣ ℓ`). Uniqueness of the infinite-volume state is not claimed (question 10 to Roland). |
| **S0-Q03** | **Polymers and their size** (P1 (2.26)–(2.27)). | **Nearest-neighbour connected unions of blocks of side `ML^j`; size = number of blocks `|X|/(ML^j)^d`; decay `e^{−κ·size}`.** This class contains P1's `𝒟_j` (connected unions of overlapping `LM`-cubes), and the tree length satisfies `n/(C_dL^{2d}) − 1 ≤ d_j(X) ≤ n` for `n` blocks, so with `∀κ` and the source order `L → κ → M → c₉ → β₀` the two forms are interconvertible (Audit C.4, F-8). | P1's literal `𝒟_j` and tree length (infimum over continuous tree graphs in `ℝ^d`): equivalent, much heavier, and every proof would convert it to block counts. |
| **S0-Q04** | **What Root-F asserts** (P7 (4.15)–(4.17), P4 (H.4), (H.7), P9 (4.4)–(4.7)). | **The representation identity; locality (each term depends only on `g` on its polymer); analyticity; the scale-dependent bounds; independence of the torus for polymers that do not wind around it** (the last clause compares the terms of two admissible tori on the images of a finite `A ⊂ ℤ^d` in the box `|y_μ| < ℓ/4`; Audit F-2). **Not asserted:** `O(N)` and Euclidean covariance of the terms (any representation can be averaged to restore them, Audit F-7), and the separate top-scale pieces `ℳ_n^{(k_f+1)}`, `𝒫^{(k_f+1)}` (folded into scale `k_f + 1`; Audit C.1). | (a) Add the covariance clauses (longer, no extra content). (b) Drop torus independence (v1.0; then Root-F says nothing about `ℤ^d`). |
| **S0-Q05** | **Constants and quantifiers of Root-F** (P4 Thm 1, p. 680; (5.40), p. 718; roadmap §4.4). | `∃δ > 0, ∀κ > 0, ∀c₉ > 0, ∃L ≥ 2, M ≥ 1, β₀, ∀β ≥ β₀, ∀ν ∈ (0,1], ∀ unit h, ∃k_f` with `L^{k_f}√ν ≤ L` and `1/2 ≤ L^{k_f+1}√ν`, then the terms. The bound is `c₉ L^{−j((d−2)/2+δ)} e^{−κ·size}`: `δ = γ − α₁ > 0` is Balaban's irrelevancy gap `γ` (P9 p. 495) minus the loss `α₁` of P4 (H.7), positive because `α₁` may be taken small (Audit F-3, R-11); `∀κ` is P1 p. 118 / P4 (H.4) ("κ arbitrarily large, depending on M") and is what makes the statement non-trivial (Audit F-6); `∀c₉` is P4 (5.40), `c₉ = β^{−1/4}`; the two bounds on `k_f` are the definition of `k_f` (first `k` with `ν_k > (7/8)L^{−2}`) with P4 (H.6) (Audit C.5, F-4). | Drop `δ` (canonical exponent `(d−2)/2`); drop the lower bound on `k_f`. Both make Root-F weaker. |
| **S0-Q06** | **The source domain.** P4 (H.7) asserts analyticity and the bounds on `‖g‖_{ℓ¹} < 1`. | **Analyticity and the identity on `∑_x ∑_i |g_i(x)| < 1`; the bounds on `∑_x ∑_i |g_i(x)| ≤ 1/2`.** The top-scale terms are built as `∫_0^1 ∂_gℛ(h, tg) dt` (P7 (4.15)) from functions analytic only on the open ball, so a bound up to the boundary does not follow (Audit F-1). Bounds on a fixed smaller ball are all that Cauchy estimates for correlation functions need. The domain `∑∑|g_i(x)|` is contained in Balaban's `∑_x |g(x)|`, so every claim on it is weaker (Audit A.4). | Bounds on the whole open domain, as printed in P4 (H.7): no derivation in the sources. |
| **S0-Q07** | **Constants of Root-C** (roadmap question 6, open with Roland). | **`β₀, c, c', ρ₀, ρ₁, q` chosen before `β`** (depending only on `d, N`): the strong reading, consistent with P9 §§3–4 (Audit C-4, D.6). `0 < ρ₁ < 1` existential, as printed ("small ρ₁"; Audit C-2). `m, G_tr, G_lg` chosen after `β` and before `h`: independent of the field direction, which is exact by `O(N)` invariance (Audit D.5). | Constants depending on `β` (weaker; only if Roland says so). `∀ρ₁ > 0` (stronger; supported by P9 p. 511, needs a ruling). |
| **S0-Q08** | **Infinite-volume objects in Root-C.** | **Existentials inside the root**: the limits `m, G_tr, G_lg`, their `ν ↓ 0` limits, `γ_∞`, and the lattice Green's function `G`, characterized by `−ΔG = δ₀` and `G → 0` at infinity (unique by the maximum principle; Audit D.3). No extra frozen definitions. The `ν ↓ 0` limits and the thermodynamic limit are claimed but not proved in the series (Audit C-3, D.8): they are reconstruction items (roadmap C-3). | Frozen `∃!` gates and definitions for the infinite-volume functions and the Green's function (more frozen files, same content). |
| **S0-Q09** | **Model conventions** (Audit A, D-1). | Energy literally P9 (1.1) at `λ = ∞`: `½∑_x∑_μ|φ(x+e_μ)−φ(x)|² + (ν/2)∑_x|φ(x)−h|²`; a priori measure the product of the (unnormalized) surface measure on `S^{N−1}`; complex source with bilinear pairing `∑_x∑_i g_i(x)φ_i(x)`; expectations normalized by `∫e^{−βH}`; sup norm on `ℤ^d`; `(1+|x|)` in place of `|x|` in the decay bounds. Constants that cancel (`½σ` versus `σ`, `Z(0)`) are not reproduced. | — |
| **S0-Q10** | **Freeze procedure.** | One stage: the eight definitions frozen `SEALED` (whole-file hash), the two roots frozen `DRAFT_SORRY`, all ten approved as written, manifest entries citing `frozen/APPROVALS.md#surface-v1`. | — |

**Minor confirmations** (the default applies unless the author objects).
- m1 — paths and names as in §1 (`Balaban.Torus`, `Balaban.aprioriMeasure`, `Balaban.energy`,
  `Balaban.partitionFunction`, `Balaban.gibbsExpectation`, `Balaban.onePoint`,
  `Balaban.twoPointTruncated`, `Balaban.IsPolymer`, `Balaban.logPartition_multiscale`,
  `Balaban.lowTemperature_correlations`).
- m2 — `hd : 3 ≤ d` and `hN : 2 ≤ N` do not appear in the conclusions but are needed: for `d ≤ 2`
  no Green's function exists and Root-F would contradict Mermin–Wagner; for `N = 1` `G_tr` is
  unconstrained (Audit D-2).
- m3 — on the side-2 torus each bond is counted twice; no root uses `ℓ ≤ 2` (Audit D-1).
- m4 — the regime `ν > (7/8)L^{−2}` (`k_f = 0`) is not covered by the written flow (Audit F-4); its
  proof is a single massive cluster expansion, added to the reconstruction list.

## Changelog v1.0 → v1.1 (audit `notes/phase0/surface-v1-audit.md`)

| Finding | Severity | Disposition |
|---|---|---|
| F-1: Root-F's bound on the whole open domain is not supported (Cauchy estimates degenerate at the boundary for the top-scale terms built by `∫_0^1 ∂_gℛ(tg) dt`) | MAJOR | **Fixed:** bounds on `∑∑|g_i(x)| ≤ 1/2`; analyticity and identity on `< 1` (S0-Q06). |
| F-2: torus independence dropped; Root-F then says nothing about `ℤ^d` | MAJOR | **Fixed:** the terms are chosen for all tori at once and agree on non-winding polymers (S0-Q04). |
| F-3: canonical exponent drops the irrelevancy gap | MINOR | **Fixed:** `∃δ > 0` and exponent `(d−2)/2 + δ` (S0-Q05). |
| C-1: the divisibility-net limit does not give the limit along `ML^n` | MINOR | **Fixed:** limits along sides divisible by `q^n` (S0-Q02); `q` placed before `β` (with the other constants; stronger than the audit's placement after `β`). |
| F-4: `k_f` had only an upper bound | NOTE | **Adopted:** lower bound `1/2 ≤ L^{k_f+1}√ν` (S0-Q05); `k_f = 0` regime recorded (m4). |
| F-5: junk terms for `j ∉ [1, k_f+1]` | NOTE | **Fixed:** they vanish. |
| F-6, F-7, F-8, C-2, C-3, C-4, D-1, D-2 | NOTE | Recorded in S0-Q03, S0-Q04, S0-Q05, S0-Q07, S0-Q08, m2, m3. |

Re-audit of v1.1 (same auditor, appended to the audit file): every Lean statement and definition
body approved as written; docstring and packet corrections R-1 to R-11 applied (v1.2 below).

## Changelog v1.1 → v1.2 (re-audit, `notes/phase0/surface-v1-audit.md` "Re-audit of v1.1")

| Finding | Severity | Disposition |
|---|---|---|
| R-1: Root-F docstring overstated the torus-independence clause | MINOR | **Fixed** (docstring now states the box `\|y_μ\| < min(ℓ, ℓ')/4` and calls it a special case of P4 (H.4)). |
| R-2: Root-F docstring omitted `∃ δ > 0` | MINOR | **Fixed.** |
| R-3: wrong citation for `L` in the binder audit | MINOR | **Fixed** (P1 p. 107, (1.11)). |
| R-4, R-6: citations for `d ≥ 3, N ≥ 2` and for the upper bound on `k_f` | NOTE | **Fixed** (P1 p. 105, p. 120; P4 p. 719). |
| R-5: `∀κ` is a converted rate | NOTE | **Fixed** (reclassified SOURCE/PROPOSED; counts updated). |
| R-7: `q = L` needs `M = L^m` | NOTE | **Fixed** (`q = ML` in general). |
| R-8: the decision-record path did not exist | NOTE | **Fixed**: this file is that path. |
| R-10: "`k_f` is the number of steps" is an interpretation | NOTE | **Fixed** (docstring now says "for some `k_f` with …, in the proof the number of steps before the last one"). |
| R-11: wording of `δ` | NOTE | **Fixed** (S0-Q05). |
| R-9, R-12 | NOTE | No change (implicit in context; imports harmless). |

Lean statements and definition bodies are unchanged from v1.1; only the module docstring of
`LogPartitionMultiscale.lean` changed.

## 1. The proposed files

Target directory `Balaban/Frozen/`. sha256 of the files in the scratch tree `/home/scott/Balaban-scratch/p0/tree`.

| # | File | Export | Kind | Roadmap item | State after freeze | sha256 |
|---|---|---|---|---|---|---|
| 1 | `Balaban/Frozen/Model/Torus.lean` | `Balaban.Torus` | definition (abbrev) | Def-1 | SEALED | `09adfc2ab553d217e6427b778f8230d794533c9ef8eb9c90e297a69f03334555` |
| 2 | `Balaban/Frozen/Model/AprioriMeasure.lean` | `Balaban.aprioriMeasure` | definition | Def-1 | SEALED | `c1aa5b02285700c9efff45696d34f73451ef3f9682b8a6016ec26ff53d25c254` |
| 3 | `Balaban/Frozen/Model/Energy.lean` | `Balaban.energy` | definition | Def-1 | SEALED | `ef66251521d7c27f3ff6f7cf78022e3b91a0d0b285ef93d48471339602628872` |
| 4 | `Balaban/Frozen/Model/PartitionFunction.lean` | `Balaban.partitionFunction` | definition | Def-1 | SEALED | `4648319116e15912b07f55b3393ac3de07bcf5db98836101ac34c041a0ccf626` |
| 5 | `Balaban/Frozen/Model/GibbsExpectation.lean` | `Balaban.gibbsExpectation` | definition | Def-1 | SEALED | `d08f7626d786fa35644d5ef5fb83268e59f7180313a245e173a139bd406b2930` |
| 6 | `Balaban/Frozen/Model/OnePoint.lean` | `Balaban.onePoint` | definition | Def-1 | SEALED | `782baf7117dffc222c9cd87f8bf27c90dcdb279696432898162494a216a7a47e` |
| 7 | `Balaban/Frozen/Model/TwoPointTruncated.lean` | `Balaban.twoPointTruncated` | definition | Def-1 | SEALED | `ac9b2bd105da10abfab3533b77ce64f1d711c7430494640643bb53161e70a54d` |
| 8 | `Balaban/Frozen/Geometry/IsPolymer.lean` | `Balaban.IsPolymer` | definition (predicate) | Def-2 | SEALED | `906991e7c397b4b9e5cb87ff909d880a6e4b6ee9f2a10f406128d5ff5425a290` |
| 9 | `Balaban/Frozen/Roots/LogPartitionMultiscale.lean` | `Balaban.logPartition_multiscale` | theorem (Root-F) | Root-F | DRAFT_SORRY | `26c6e8499a68ccbbaf59ca355aed36d749724e919bebb5bb91870696f8d2cd5e` |
| 10 | `Balaban/Frozen/Roots/LowTemperatureCorrelations.lean` | `Balaban.lowTemperature_correlations` | theorem (Root-C) | Root-C | DRAFT_SORRY | `b91e29ad2185317c9a3ce8377374db8595a22b6f9af2fdab2e602b901041f279` |

## 2. The exact code

Each file is shown in full: imports, docstrings, binders and bodies.

### 2.1 `Balaban/Frozen/Model/Torus.lean`

```lean
module

public import Mathlib.Data.ZMod.Defs

/-!
# The discrete torus

Def-1 (model). The lattice of the finite-volume model: the discrete torus `(ℤ/ℓℤ)^d` with
periodic boundary conditions (P1 p. 103; P9 p. 494). Cubic tori of every side `ℓ` are allowed;
the theorems state which sides they use.
-/

@[expose] public section

namespace Balaban

/-- The discrete torus `(ℤ/ℓℤ)^d`. -/
abbrev Torus (d ℓ : ℕ) : Type := Fin d → ZMod ℓ

end Balaban
```

### 2.2 `Balaban/Frozen/Model/AprioriMeasure.lean`

```lean
module

public import Balaban.Frozen.Model.Torus
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace

/-!
# The a priori measure of the hard-spin model

Def-1 (model). Hard spins (`λ = ∞`): the spin at each site lies on the unit sphere
`S^{N-1} ⊂ ℝ^N`, and the a priori measure is the product over the sites of the surface measure
on the sphere (the `λ → ∞` limit of P1 (1.5)–(1.6), p. 104, up to a constant factor that cancels
in every normalized quantity).
-/

@[expose] public section

namespace Balaban

open MeasureTheory

/-- The product over the sites of the torus of the surface measure on the unit sphere
`S^{N-1} ⊂ ℝ^N` (Mathlib's `Measure.toSphere` of Lebesgue measure). -/
noncomputable def aprioriMeasure (d N ℓ : ℕ) [NeZero ℓ] :
    Measure (Torus d ℓ → Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1) :=
  Measure.pi fun _ => (volume : Measure (EuclideanSpace ℝ (Fin N))).toSphere

end Balaban
```

### 2.3 `Balaban/Frozen/Model/Energy.lean`

```lean
module

public import Balaban.Frozen.Model.Torus
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Data.ZMod.Basic

/-!
# The energy of the hard-spin model

Def-1 (model). P9 (1.1) (p. 493) and P1 (1.5)–(1.6) (p. 104) at `λ = ∞`:
`H(φ) = ½ ‖∂φ‖² + (ν/2) ‖φ - h‖²`, where `‖∂φ‖²` sums `|φ(x + e_μ) - φ(x)|²` over the
nearest-neighbour bonds of the torus (each bond once when `ℓ ≥ 3`), `ν` is the strength of the
external field and `h` its direction. The Gibbs factor is `exp(-β H(φ))`.
-/

@[expose] public section

namespace Balaban

/-- `H(φ) = ½ ∑_x ∑_μ |φ(x + e_μ) - φ(x)|² + (ν/2) ∑_x |φ(x) - h|²`. -/
noncomputable def energy (d N ℓ : ℕ) [NeZero ℓ] (ν : ℝ) (h : EuclideanSpace ℝ (Fin N))
    (φ : Torus d ℓ → Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1) : ℝ :=
  (1 / 2) * ∑ x : Torus d ℓ, ∑ μ : Fin d,
      ‖(φ (x + Pi.single μ 1) : EuclideanSpace ℝ (Fin N)) - φ x‖ ^ 2
    + (ν / 2) * ∑ x : Torus d ℓ, ‖(φ x : EuclideanSpace ℝ (Fin N)) - h‖ ^ 2

end Balaban
```

### 2.4 `Balaban/Frozen/Model/PartitionFunction.lean`

```lean
module

public import Balaban.Frozen.Model.AprioriMeasure
public import Balaban.Frozen.Model.Energy
public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# The partition function with a source

Def-1 (model). P9 (1.1) (p. 493), P1 p. 108: the source term `⟨g, φ⟩ = ∑_x ∑_i g_i(x) φ_i(x)`
with a complex source `g`, added to the exponent. `log (Z(g)/Z(0))` is the generating functional
of the connected correlation functions.
-/

@[expose] public section

namespace Balaban

open MeasureTheory

/-- `Z(g) = ∫ exp(-β H(φ) + ∑_x ∑_i g_i(x) φ_i(x)) ∏_x dσ(φ_x)`. -/
noncomputable def partitionFunction (d N ℓ : ℕ) [NeZero ℓ] (β ν : ℝ)
    (h : EuclideanSpace ℝ (Fin N)) (g : Torus d ℓ → Fin N → ℂ) : ℂ :=
  ∫ φ, Complex.exp (-((β * energy d N ℓ ν h φ : ℝ) : ℂ)
      + ∑ x : Torus d ℓ, ∑ i : Fin N, g x i * (((φ x : EuclideanSpace ℝ (Fin N)) i : ℝ) : ℂ))
    ∂aprioriMeasure d N ℓ

end Balaban
```

### 2.5 `Balaban/Frozen/Model/GibbsExpectation.lean`

```lean
module

public import Balaban.Frozen.Model.AprioriMeasure
public import Balaban.Frozen.Model.Energy
public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Finite-volume Gibbs expectations

Def-1 (model). The expectation of a real observable in the finite-volume Gibbs state with
density `exp(-β H)` with respect to the a priori measure (P9 p. 494, `⟨·⟩_T`).
-/

@[expose] public section

namespace Balaban

open MeasureTheory

/-- `⟨F⟩ = ∫ F e^{-βH} / ∫ e^{-βH}`. -/
noncomputable def gibbsExpectation (d N ℓ : ℕ) [NeZero ℓ] (β ν : ℝ)
    (h : EuclideanSpace ℝ (Fin N))
    (F : (Torus d ℓ → Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1) → ℝ) : ℝ :=
  (∫ φ, F φ * Real.exp (-(β * energy d N ℓ ν h φ)) ∂aprioriMeasure d N ℓ) /
    ∫ φ, Real.exp (-(β * energy d N ℓ ν h φ)) ∂aprioriMeasure d N ℓ

end Balaban
```

### 2.6 `Balaban/Frozen/Model/OnePoint.lean`

```lean
module

public import Balaban.Frozen.Model.GibbsExpectation

/-!
# The one-point function

Def-1 (model). `M(x) = ⟨φ(x)⟩` (P9 p. 494), componentwise.
-/

@[expose] public section

namespace Balaban

/-- The component `⟨φ_i(x)⟩` of the one-point function. -/
noncomputable def onePoint (d N ℓ : ℕ) [NeZero ℓ] (β ν : ℝ) (h : EuclideanSpace ℝ (Fin N))
    (x : Torus d ℓ) (i : Fin N) : ℝ :=
  gibbsExpectation d N ℓ β ν h fun φ => (φ x : EuclideanSpace ℝ (Fin N)) i

end Balaban
```

### 2.7 `Balaban/Frozen/Model/TwoPointTruncated.lean`

```lean
module

public import Balaban.Frozen.Model.OnePoint

/-!
# The truncated two-point function

Def-1 (model). `G(x, y) = ⟨φ(x) ⊗ φ(y)⟩ - ⟨φ(x)⟩ ⊗ ⟨φ(y)⟩` (P9 p. 494), entrywise.
-/

@[expose] public section

namespace Balaban

/-- The entry `⟨φ_i(x) φ_k(y)⟩ - ⟨φ_i(x)⟩ ⟨φ_k(y)⟩` of the truncated two-point function. -/
noncomputable def twoPointTruncated (d N ℓ : ℕ) [NeZero ℓ] (β ν : ℝ)
    (h : EuclideanSpace ℝ (Fin N)) (x y : Torus d ℓ) (i k : Fin N) : ℝ :=
  gibbsExpectation d N ℓ β ν h
      (fun φ => (φ x : EuclideanSpace ℝ (Fin N)) i * (φ y : EuclideanSpace ℝ (Fin N)) k)
    - onePoint d N ℓ β ν h x i * onePoint d N ℓ β ν h y k

end Balaban
```

### 2.8 `Balaban/Frozen/Geometry/IsPolymer.lean`

```lean
module

public import Balaban.Frozen.Model.Torus
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Finset.Basic
public import Mathlib.Logic.Relation

/-!
# Polymers

Def-2 (geometry). At scale `j` the torus is partitioned into the blocks of side `s = M L^j`,
`{x : ⌊x_μ / s⌋ = c_μ for all μ}` (P1 p. 117: the partitions "determined by the lattices
`L^j M ℤ^d`"). A polymer is a nonempty union of blocks that is connected for the
nearest-neighbour adjacency of the torus. This class contains P1's localization domains `𝒟_j`
(P1 (2.26), connected unions of overlapping `LM`-cubes); the size of a polymer is measured by
its number of blocks `|X| / s^d`, which is comparable to P1's tree length `d_j(X)` (P1 (2.27))
up to constants depending on `d` and `L` (`notes/phase0/surface-v1-audit.md` §C.4).
-/

@[expose] public section

namespace Balaban

/-- `X` is a polymer of block side `s`: a nonempty union of blocks of side `s` that is
connected for the nearest-neighbour adjacency of the torus. -/
def IsPolymer (d ℓ s : ℕ) [NeZero ℓ] (X : Finset (Torus d ℓ)) : Prop :=
  X.Nonempty ∧
  (∀ x ∈ X, ∀ y : Torus d ℓ, (∀ μ, (x μ).val / s = (y μ).val / s) → y ∈ X) ∧
  ∀ x ∈ X, ∀ y ∈ X, Relation.ReflTransGen
    (fun a b => a ∈ X ∧ b ∈ X ∧ ∃ μ : Fin d, b = a + Pi.single μ 1 ∨ a = b + Pi.single μ 1) x y

end Balaban
```

### 2.9 `Balaban/Frozen/Roots/LogPartitionMultiscale.lean`

```lean
module

public import Balaban.Frozen.Model.PartitionFunction
public import Balaban.Frozen.Geometry.IsPolymer
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Data.ZMod.ValMinAbs

/-!
# Root-F: the renormalization-group flow, observable form

The generating functional of the hard-spin `O(N)` model at low temperature has Balaban's
multiscale representation, with bounds uniform in the external field `ν ∈ (0, 1]` and in the
volume: P7 (4.15)–(4.17) (p. 533) with P4 (H.4), (H.6)–(H.7) (pp. 677–679) and P9 (4.4)–(4.7)
(p. 516). There is `δ > 0` such that for every `κ` and `c₉` there are `L, M, β₀` such that for
`β ≥ β₀`:

* `log (Z(g)/Z(0)) = ⟨g, h⟩ + ∑_{j=1}^{k_f+1} ∑_x ∑_{X ∋ x} ⟨g(x), T_j(x, X; g)⟩` on every torus
  whose side is divisible by `M L^{k_f+1}`, for some `k_f` with `L^{k_f} √ν ≤ L` and
  `1/2 ≤ L^{k_f+1} √ν` (in the proof, the number of renormalization steps before the last one);
* `T_j(x, X; ·)` vanishes unless `X` is a scale-`j` polymer containing `x`, depends only on
  `g|_X`, is analytic on `∑_x ∑_i |g_i(x)| < 1`, and on `∑_x ∑_i |g_i(x)| ≤ 1/2` is bounded by
  `c₉ L^{-j((d-2)/2 + δ)} exp(-κ |X| / (M L^j)^d)`;
* the terms of two admissible tori of sides `ℓ, ℓ'` agree on the images of a finite set
  `A ⊂ ℤ^d` contained in the box `|y_μ| < min(ℓ, ℓ')/4`: a special case of the independence of
  the torus for polymers that do not wind around it (P4 (H.4), p. 677).

The scale-`k_f+1` terms collect P7's `ℳ_n^{(k_f+1)}`, `n = 0, …, m`, and the large-field polymer
terms `𝒫^{(k_f+1)}` of P9 (4.4)–(4.6). Decision record: `notes/phase0/surface-v1-for-approval.md`.
-/

@[expose] public section

namespace Balaban

/-- Root-F (main deliverable): the full renormalization-group flow, with large fields, in
observable form. -/
theorem logPartition_multiscale (d N : ℕ) (hd : 3 ≤ d) (hN : 2 ≤ N) :
    ∃ δ : ℝ, 0 < δ ∧
    ∀ κ : ℝ, 0 < κ → ∀ c₉ : ℝ, 0 < c₉ →
    ∃ L M : ℕ, 2 ≤ L ∧ 1 ≤ M ∧ ∃ β₀ : ℝ, ∀ β : ℝ, β₀ ≤ β →
    ∀ ν : ℝ, 0 < ν → ν ≤ 1 → ∀ h : EuclideanSpace ℝ (Fin N), ‖h‖ = 1 →
    ∃ kf : ℕ, (L : ℝ) ^ kf * Real.sqrt ν ≤ L ∧ 1 / 2 ≤ (L : ℝ) ^ (kf + 1) * Real.sqrt ν ∧
    ∃ T : (ℓ : ℕ) → ℕ → Torus d ℓ → Finset (Torus d ℓ) → (Torus d ℓ → Fin N → ℂ) →
        (Fin N → ℂ),
      (∀ (ℓ : ℕ) [NeZero ℓ], M * L ^ (kf + 1) ∣ ℓ →
        (∀ j x X, ¬ (j ∈ Finset.Icc 1 (kf + 1) ∧ x ∈ X ∧ IsPolymer d ℓ (M * L ^ j) X) →
          T ℓ j x X = 0) ∧
        (∀ j x X (g g' : Torus d ℓ → Fin N → ℂ), (∀ y ∈ X, g y = g' y) →
          T ℓ j x X g = T ℓ j x X g') ∧
        (∀ j x X, AnalyticOnNhd ℂ (T ℓ j x X) {g | ∑ y, ∑ i, ‖g y i‖ < 1}) ∧
        (∀ j ∈ Finset.Icc 1 (kf + 1), ∀ x X (g : Torus d ℓ → Fin N → ℂ),
          ∑ y, ∑ i, ‖g y i‖ ≤ 1 / 2 →
          ‖T ℓ j x X g‖ ≤ c₉ * (L : ℝ) ^ (-((j : ℝ) * (((d : ℝ) - 2) / 2 + δ)))
            * Real.exp (-κ * (X.card : ℝ) / ((M : ℝ) * (L : ℝ) ^ j) ^ d)) ∧
        ∀ g : Torus d ℓ → Fin N → ℂ, ∑ y, ∑ i, ‖g y i‖ < 1 →
          Complex.log (partitionFunction d N ℓ β ν h g / partitionFunction d N ℓ β ν h 0) =
            ∑ x, ∑ i, g x i * (h i : ℂ)
              + ∑ j ∈ Finset.Icc 1 (kf + 1), ∑ x, ∑ X : Finset (Torus d ℓ), ∑ i,
                  g x i * T ℓ j x X g i) ∧
      ∀ (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ'], M * L ^ (kf + 1) ∣ ℓ → M * L ^ (kf + 1) ∣ ℓ' →
        ∀ (j : ℕ) (a : Fin d → ℤ) (A : Finset (Fin d → ℤ)) (g : (Fin d → ℤ) → Fin N → ℂ),
          a ∈ A → (∀ y ∈ A, ∀ μ, 4 * |y μ| < (ℓ : ℤ) ∧ 4 * |y μ| < (ℓ' : ℤ)) →
          T ℓ j (fun μ => (a μ : ZMod ℓ)) (A.image fun y μ => (y μ : ZMod ℓ))
              (fun z => g fun μ => ZMod.valMinAbs (n := ℓ) (z μ)) =
            T ℓ' j (fun μ => (a μ : ZMod ℓ')) (A.image fun y μ => (y μ : ZMod ℓ'))
              (fun z => g fun μ => ZMod.valMinAbs (n := ℓ') (z μ)) := by
  sorry

end Balaban
```

### 2.10 `Balaban/Frozen/Roots/LowTemperatureCorrelations.lean`

```lean
module

public import Balaban.Frozen.Model.TwoPointTruncated
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Order.Filter.Cofinite

/-!
# Root-C: low-temperature correlation functions

P9 Theorem 1.1 (pp. 494–495) for hard spins (`λ = ∞`). There are `β₀` and constants
`c, c', ρ₀, ρ₁` (depending only on `d, N`) and an integer `q ≥ 2` such that for `β ≥ β₀`:

* for every `ν ∈ (0, 1]` and every unit vector `h`, the one- and two-point functions converge
  along the tori whose side is divisible by `q^n`, `n → ∞`, to `m(ν) h` and
  `G_tr(ν, x - y) (I - h ⊗ h) + G_lg(ν, x - y) h ⊗ h`;
* `|m(ν) - 1| ≤ c β^{-1+ρ₁}` and `|G_tr(ν, x)|, |G_lg(ν, x)| ≤ c (1 + |x|)^{-(d-2)} e^{-c' √ν |x|}`;
* as `ν ↓ 0`, `m`, `G_tr`, `G_lg` converge, and with the lattice Green's function `G`
  (`-ΔG = δ₀`, `G → 0` at infinity) and some `γ_∞` with `|γ_∞ - 1| ≤ c/β`,
  `|G_tr(0, x) - m(0)² / (β γ_∞) G(x)| ≤ c (1 + |x|)^{-(d-2+ρ₀)}` and
  `|G_lg(0, x)| ≤ c (1 + |x|)^{-(d-2+ρ₀)}`.

`|x|` is the sup norm on `ℤ^d`. Decision record: `notes/phase0/surface-v1-for-approval.md`.
-/

@[expose] public section

namespace Balaban

open Filter Topology

/-- Root-C (final deliverable): P9 Theorem 1.1 for the hard-spin model. -/
theorem lowTemperature_correlations (d N : ℕ) (hd : 3 ≤ d) (hN : 2 ≤ N) :
    ∃ β₀ c c' ρ₀ ρ₁ : ℝ, ∃ q : ℕ, 2 ≤ q ∧ 0 < c ∧ 0 < c' ∧ 0 < ρ₀ ∧ 0 < ρ₁ ∧ ρ₁ < 1 ∧
    ∀ β : ℝ, β₀ ≤ β →
    ∃ (m : ℝ → ℝ) (Gtr Glg : ℝ → (Fin d → ℤ) → ℝ),
      (∀ ν : ℝ, 0 < ν → ν ≤ 1 → ∀ h : EuclideanSpace ℝ (Fin N), ‖h‖ = 1 →
        ∀ x y : Fin d → ℤ, ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ,
          ∀ (ℓ : ℕ) [NeZero ℓ], q ^ n₀ ∣ ℓ →
            (∀ i, |onePoint d N ℓ β ν h (fun μ => (x μ : ZMod ℓ)) i - m ν * h i| < ε) ∧
            ∀ i k, |twoPointTruncated d N ℓ β ν h (fun μ => (x μ : ZMod ℓ))
                (fun μ => (y μ : ZMod ℓ)) i k
              - (Gtr ν (x - y) * ((if i = k then 1 else 0) - h i * h k)
                  + Glg ν (x - y) * (h i * h k))| < ε) ∧
      (∀ ν : ℝ, 0 < ν → ν ≤ 1 →
        |m ν - 1| ≤ c * β ^ (-1 + ρ₁) ∧
        ∀ x : Fin d → ℤ,
          |Gtr ν x| ≤ c * (1 + ‖x‖) ^ (-((d : ℝ) - 2)) * Real.exp (-(c' * Real.sqrt ν * ‖x‖)) ∧
          |Glg ν x| ≤ c * (1 + ‖x‖) ^ (-((d : ℝ) - 2)) * Real.exp (-(c' * Real.sqrt ν * ‖x‖))) ∧
      ∃ (m₀ γ : ℝ) (Gtr₀ Glg₀ G : (Fin d → ℤ) → ℝ),
        Tendsto m (𝓝[>] 0) (𝓝 m₀) ∧
        (∀ x, Tendsto (fun ν => Gtr ν x) (𝓝[>] 0) (𝓝 (Gtr₀ x))) ∧
        (∀ x, Tendsto (fun ν => Glg ν x) (𝓝[>] 0) (𝓝 (Glg₀ x))) ∧
        (∀ x, ∑ μ : Fin d, (2 * G x - G (x + Pi.single μ 1) - G (x - Pi.single μ 1))
          = if x = 0 then 1 else 0) ∧
        Tendsto G cofinite (𝓝 0) ∧
        0 < γ ∧ |γ - 1| ≤ c / β ∧
        ∀ x : Fin d → ℤ,
          |Gtr₀ x - m₀ ^ 2 / (β * γ) * G x| ≤ c * (1 + ‖x‖) ^ (-((d : ℝ) - 2 + ρ₀)) ∧
          |Glg₀ x| ≤ c * (1 + ‖x‖) ^ (-((d : ℝ) - 2 + ρ₀)) := by
  sorry

end Balaban
```

## 3. Binder audit of the roots

Classification: **SOURCE** (stated in the cited source), **PROPOSED** (a formalization choice,
pending the decision named), **TYPING** (carriers and instance arguments).

### Root-F `Balaban.logPartition_multiscale`

| Binder / clause | Class | Source or decision |
|---|---|---|
| `d N : ℕ` | TYPING | — |
| `hd : 3 ≤ d`, `hN : 2 ≤ N` | SOURCE | P1 p. 105, Thm 2.2 p. 120; P9 abstract; m2 |
| `∃ δ > 0` (gap in the exponent) | SOURCE / PROPOSED | P4 (H.7) p. 679 (`ξ^{(d−2)/2+γ−α₁}`), P9 p. 495; S0-Q05 |
| `∀ κ > 0` | SOURCE / PROPOSED | P1 p. 118, P4 (H.4) p. 677 ("κ can be chosen arbitrarily large, depending on M"); roadmap §4.4; here a decay rate per block, converted from the source's tree-length rate (S0-Q03, Audit C.4) |
| `∀ c₉ > 0` | SOURCE | P4 Thm 1 p. 680, (5.40) p. 718 |
| `∃ L ≥ 2, M ≥ 1` | SOURCE | P1 p. 107 ((1.11), the block factor `L`), p. 117 (`M = L^m`) |
| `∃ β₀, ∀ β ≥ β₀` | SOURCE | P4 Thm 1; P7 Thm 5 p. 497; P9 Thm 1.1 |
| `∀ ν ∈ (0, 1]` | SOURCE | P4 (1.1) p. 676 (`0 < v ≤ 1`); P9 (1.1) |
| `∀ h`, `‖h‖ = 1` | SOURCE | P4 p. 680 (`h ∈ S^{N−1}`) |
| `∃ k_f`, `L^{k_f}√ν ≤ L`, `1/2 ≤ L^{k_f+1}√ν` | SOURCE / PROPOSED | P7 p. 529, P9 p. 515 (first `k` with `ν_k > (7/8)L^{−2}`), P4 (H.6) p. 679, P4 p. 719 (`ν_{k₁} < 1`); the two inequalities are consequences (Audit C.5); S0-Q05 |
| `∃ T` (one family for all tori) | SOURCE / PROPOSED | P7 (4.17) p. 533 (the functions `ℳ^{(j)}`, `ℳ_n^{(k+1)}`); one family so that the agreement clause can be stated (S0-Q04) |
| `∀ ℓ [NeZero ℓ]`, `M L^{k_f+1} ∣ ℓ` | PROPOSED | S0-Q02 (P1 p. 117: blocks of side `ML^j` tile the torus) |
| vanishing off polymers containing `x`, `j ∉ [1, k_f+1]` | SOURCE / PROPOSED | P4 (H.7) (`∑_{X ∈ 𝒟_j : x ∈ X}`); polymer class S0-Q03 |
| locality: depends on `g|_X` only | SOURCE | P4 (H.7) ("depends on `ψ_j, g` restricted to X") |
| analyticity on `∑∑|g_i(x)| < 1` | SOURCE | P4 (H.7); domain A.4 |
| bound on `∑∑|g_i(x)| ≤ 1/2` | SOURCE / PROPOSED | P4 (H.7), P7 p. 533 (`β_k^{−n}` for `n > 0`), P9 (4.6); restricted domain S0-Q06 |
| the identity for `log(Z(g)/Z(0))` | SOURCE | P7 (4.15)–(4.17) p. 533, (4.16) normalization; P9 (4.7) p. 516 |
| agreement on non-winding polymers | SOURCE / PROPOSED | P4 (H.4) p. 677 ("does not depend on the torus T if X does not wind around it"), (H.7) p. 679; box `|y_μ| < ℓ/4` S0-Q04 |

### Root-C `Balaban.lowTemperature_correlations`

| Binder / clause | Class | Source or decision |
|---|---|---|
| `d N`, `hd`, `hN` | TYPING / SOURCE | P9 abstract; m2 |
| `∃ β₀`, `∀ β ≥ β₀` | SOURCE | P9 Thm 1.1 p. 494 (`λ = ∞ ≥ λ₀`) |
| `∃ c, c', ρ₀, ρ₁` before `β`, `0 < ρ₁ < 1` | SOURCE / PROPOSED | P9 Thm 1.1 ("positive constants c, c', ρ₀ and small ρ₁"); placement S0-Q07 (question 6) |
| `∃ q ≥ 2` before `β`; limits along `q^{n₀} ∣ ℓ` | PROPOSED | S0-Q02 (P9 p. 494, `⟨·⟩ = lim_T ⟨·⟩_T`) |
| `∃ m, G_tr, G_lg` after `β`, before `h` | SOURCE / PROPOSED | P9 Thm 1.1 (`M = m(β,v)h`, `G = G_tr(I − h⊗h) + G_lg h⊗h`); `h`-independence exact by symmetry (S0-Q07, Audit D.5) |
| `∀ ν ∈ (0,1]`, `∀ h` unit, `∀ x y`, convergence of `onePoint`, `twoPointTruncated` | SOURCE / PROPOSED | P9 p. 494; encoding of `(I − h⊗h)_{ik}`, `(h⊗h)_{ik}` (Audit D.1) |
| `|m − 1| ≤ cβ^{−1+ρ₁}` | SOURCE | P9 Thm 1.1 (a) |
| `|G_tr|, |G_lg| ≤ c(1+|x|)^{−(d−2)}e^{−c'√ν|x|}` | SOURCE | P9 Thm 1.1 (a) (printed `|G_tr(x−y) − |`, read as `|G_tr(x−y)|`); `(1+|x|)`, sup norm S0-Q09 |
| `∃ m₀, G_tr⁰, G_lg⁰`: the `ν ↓ 0` limits | SOURCE / PROPOSED | P9 Thm 1.1 (b) ("for the limit v ↓ 0"); existence a reconstruction item (S0-Q08) |
| `∃ G` with `−ΔG = δ₀`, `G → 0` | SOURCE | P9 (4.17) p. 518 (`Δ^{−1}`, positive lattice Green's function on `ℤ^d`); characterization S0-Q08 |
| `∃ γ_∞ > 0`, `|γ_∞ − 1| ≤ c/β` | SOURCE | P9 Thm 1.1 (b), (4.18) p. 519 |
| `|G_tr⁰ − m₀²/(βγ_∞) G| ≤ c(1+|x|)^{−(d−2+ρ₀)}`, `|G_lg⁰| ≤ …` | SOURCE | P9 Thm 1.1 (b) (exponent in the denominator; the abstract omits the minus sign) |

Counts. Root-F: 18 rows, 9 SOURCE, 1 TYPING, 1 PROPOSED, 7 SOURCE/PROPOSED (a source statement
in a proposed encoding). Root-C: 12 rows, 6 SOURCE, 1 TYPING/SOURCE, 1 PROPOSED,
4 SOURCE/PROPOSED. The binder audit closes only if the author approves S0-Q02 to S0-Q08.

## 4. Audit record

- **Audit of v1.0** (`notes/phase0/surface-v1-audit.md`, sections A–G): FAIL, two MAJOR findings on
  Root-F (F-1 bound up to the boundary of the source domain; F-2 torus independence dropped), two
  MINOR (F-3 gap exponent; C-1 limit notion), notes. All fixed or recorded in v1.1 (changelog above).
- **Re-audit of v1.1** (same file, "Re-audit of v1.1"): every Lean statement and definition body
  approved as written; docstring and citation corrections R-1 to R-11, applied in v1.2. The
  auditor diffed every declaration against v1.0 plus the fixes, checked that `q` before `β` is
  provable (`q = ML`), and probed the two bounds on `k_f` in the built tree.
- **Elaboration of v1.2**: `lake build` of the scratch tree succeeds; diagnostics are exactly the
  two `declaration uses 'sorry'` warnings on the roots.
- **Statements no source proves** (reconstruction items carried into phase 1): the existence of the
  thermodynamic limit and of the `ν ↓ 0` limits (Root-C), the regime `ν > (7/8)L^{−2}` (m4), and the
  large-field items of roadmap §10.2 (step counter, base case, action lower bounds).

## 5. Freeze procedure after approval

1. Copy the ten files byte for byte from the scratch tree into the repository (sha256 as in §1),
   add them to `Balaban.lean`, and build.
2. Add ten manifest entries to `frozen/manifest.json` (one owner per file): source revision and
   range, contract id, path, export, `abi_sha256` (from `scripts/anchor_abi.py --print`),
   `definition_closure` (the frozen files each root depends on), and state `SEALED` for the eight
   definitions (whole-file hash) or `DRAFT_SORRY` for the two roots (prefix and suffix hashes
   around the `sorry` body, empty draft allowlist: nothing may import a root while it is a draft).
3. Record the approval in `frozen/APPROVALS.md#surface-v1` with this package's sha256 and the
   decisions as ruled.
4. Run `scripts/check_frozen_anchors.py` (statement closure included) and
   `scripts/check_lean_modules.py`; commit and push.
5. Then: the source dependency graph for phase 1 (roadmap §6, §8), built from the frozen roots,
   and the phase-1 briefs (W1–W6 in Lean; the large-field reconstruction document on paper).

## 6. Questions for Roland

`notes/QUESTIONS-ROLAND-1.md`: roadmap questions 5–10 and two new ones from this package
(11: is the observable form the right main statement; 12: limits along tori of side divisible by
`q^n`). Answers to 6, 10, 11 or 12 could change S0-Q01, S0-Q02 or S0-Q07; the package does not
wait for them, since a changed answer would produce a versioned successor of a root, not an
edit.
