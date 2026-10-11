# Audit of the phase-0 surface draft v1 (Def-1, Def-2, Root-F, Root-C)

Auditor: independent refute-first audit, 2026-10-11.
Object: `/home/scott/Balaban-scratch/p0/Draft.lean` (as read on 2026-10-11).
Probe file: `/home/scott/Balaban-scratch/audit/AuditVariants.lean` (copy of the draft's
definitions plus the replacement statements of §G and semantic probes).
Page references are journal pages, read from page images (P1, P4) or the typeset PDFs (P5, P7, P9).

**Verdict: FAIL as drafted.** Two MAJOR findings (F-1, F-2) must be fixed before Root-F can be
frozen; Root-C and the definitions have only MINOR findings and notes. With the replacement code of
§G (which elaborates, see §G.3), the expected verdict is PASS-WITH-FINDINGS (MINOR/NOTE items only).

## Findings

| ID | Severity | Declaration | Finding | Evidence | Proposed fix |
|---|---|---|---|---|---|
| F-1 | MAJOR | `logPartition_multiscale` | The bound on `T j x X g` is required on the whole open domain `∑∑‖g y i‖ < 1`. The sources do not give this for the top-scale terms: P7 obtains the terms `M_n^{(k+1)}` by writing the functions `ℛ^{(k+1)}(h,g)`, which carry no explicit factor `g` (they include the polymer term `𝒫`), as `∫_0^1 ⟨∂_g R(h,tg), g⟩ dt`; `R` is analytic and bounded only on `‖g‖_{ℓ¹} < 1`, so the Cauchy estimate for `∂_g R(h,tg)` has radius `1 − t‖g‖`, and `∫_0^1 dt/(1 − t s) = −log(1−s)/s` is unbounded as `s = ‖g‖ → 1`. The lower scales use the same device (P5 p. 518: `R_1^{(k)}` is "expanded to first order in g" and the part of first order goes into `δℱ_k`), although P4 (H.7) and P5 H3 assert the bound on the whole ball. Whether a localized decomposition with uniform bounds on the whole ℓ¹ ball exists is an open (Gleason-type) question; the statement may be unprovable as drafted. | P7 (4.15)–(4.17), p. 533; P5 H4, p. 491 (`R_n^{(k)}` analytic on `‖g‖_{ℓ¹}<1`, no `g` factor, bound `β_k^{−n−1}`); P5 p. 518; P9 (4.4)–(4.7), p. 516 (`𝒫(Y;g)` has no `g` factor); P4 (H.7), p. 679 | Keep analyticity and the identity on `∑∑‖g y i‖ < 1`; require the bound only on `∑∑‖g y i‖ ≤ 1/2` (all `j`). Cauchy radius `1/4` then costs a factor 4, absorbed in `c₉`. Code in §G.1. |
| F-2 | MAJOR | `logPartition_multiscale` | Torus independence of the localized terms is dropped: `T` is chosen separately for each `ℓ`, and nothing relates the terms on different tori. This is the property from which the series obtains the thermodynamic limit (P4 p. 720, P5 (1.46)); without it Root-F carries no information about `ℤ^d`, and Root-C's limits are not consequences of Root-F. The roadmap's committed Root-F includes it (§2.1, §3.2 "does not depend on n when X does not wrap around the torus"). Unlike covariance (F-7), it cannot be recovered by averaging. | P4 (H.4), p. 677 ("does not depend on the torus T if X does not wind around it"), (H.7), p. 679; P4 p. 720; P5 H4, p. 491 and (1.46), p. 501; roadmap §2.1, §3.2 | Choose the family `T ℓ` before `∀ ℓ` and add an agreement clause for terms whose polymer lies in the centred box of half-width `< ℓ/4`, `< ℓ'/4`. Code in §G.1. |
| F-3 | MINOR | `logPartition_multiscale` | The prefactor uses the canonical exponent `L^{−j(d−2)/2}`; the sources give `ξ^{(d−2)/2+γ−α₁}`, `ξ = L^{−j}`, with `γ − α₁ > 0` (P3 p. 76, per the P3 review: `α₁(d−2) ≤ γ`; P4 Thm 1 lets `α₁` be taken small, e.g. `α₁ = γ/2`, so the gap is positive also for `d = 3`). The draft is implied by the source (weaker) but drops the irrelevancy gap that P9 calls "a very important property". The gap is uniform in the order of constants (γ, α₁ are chosen with `L`, before κ). | P4 (H.7), p. 679; P7 p. 533 ("as in (H.7)[4] for n = 0"); P9 p. 495 | Add `∃ δ : ℝ, 0 < δ ∧` in front of `∀ κ` and use the exponent `-((j : ℝ) * (((d : ℝ) - 2) / 2 + δ))`. Code in §G.1. |
| C-1 | MINOR | `lowTemperature_correlations` | The divisibility-net limit (`∃ ℓ₀ > 0, ∀ ℓ, ℓ₀ ∣ ℓ → …`) does not imply convergence along the RG tori `(ℤ/ML^nℤ)^d` named in the roadmap (Root-C item 1, "limits along 𝕋_n") and in Roland's answer 3: the prover may choose `ℓ₀` with prime factors not dividing `ML`, and then no `ML^n` is a multiple of `ℓ₀`. The RG gives more: convergence along all multiples of `L^{n₀}` (with `M = L^m`, as in the series). | P9 p. 494 (`⟨·⟩ = lim⟨·⟩_T`); P5 (1.46), p. 501 (`T → ℤ^d`); P4 p. 720; roadmap §1.3, §3.2 | Replace by `∃ q : ℕ, 2 ≤ q ∧` (after `β`) and `∃ n₀ : ℕ, ∀ ℓ [NeZero ℓ], q ^ n₀ ∣ ℓ → …`. This implies the draft's form (`ℓ₀ = q^{n₀}`), the limit along `q^n`, and the limit along `n!`. Code in §G.2. |
| F-4 | NOTE | `logPartition_multiscale` | `kf` has only an upper bound, so `kf = 0` satisfies it for every `ν` (probe in §G.3). This does not trivialize Root-F: with `kf = 0` the representation forces exponential clustering of the truncated two-point function at a `ν`-independent rate (argument in §C.6), contradicting the Goldstone asymptotics of Root-C. The upper bound is correct (P4 p. 719: `ν_{k₁} < 1`, with (H.6)). A supported lower bound can be added for fidelity: `1 / 2 ≤ (L : ℝ) ^ (kf + 1) * Real.sqrt ν`. The case `kf = 0` (`ν > (7/8)L^{−2}`) is not covered by the written flow (P4 p. 680: the hypotheses presuppose `k ≥ 1`); it needs a direct low-temperature expansion. | P4 (H.6), p. 679; P4 §6, p. 719; P9 p. 515; P7 p. 529 | Optional; code in §G.1 (comment). |
| F-5 | NOTE | `logPartition_multiscale` | Terms `T j` for `j ∉ [1, kf+1]` are constrained only by vanishing, locality and analyticity, carry no bound and do not enter the identity. Harmless junk witnesses. | — | In §G.1 the vanishing clause also requires `j ∈ Finset.Icc 1 (kf + 1)`. |
| F-6 | NOTE | `logPartition_multiscale` | `∀ κ` is essential: with `∃ κ` a small `κ` lets the block-count decay be beaten by lattice-animal entropy and a single-scale representation becomes plausible. `∀ κ` is supported by "κ can be chosen arbitrarily large, depending on M" (P1 p. 118, P4 (H.4) p. 677) under the roadmap's order κ → M → … → β (§4.4). It inherits the open point of roadmap §12 (whether P3's `κ₀` grows with `M`). `∀ c₉` is supported by P4 (5.40), p. 718 (`c₉ = β^{−1/4}`). | P1 p. 118; P4 p. 677, p. 718; roadmap §4.4, §12 | None; record the dependence on the §4.4 order. |
| F-7 | NOTE | `logPartition_multiscale` | Dropping O(N)-stabilizer and Euclidean covariance is immaterial: any representation can be averaged over the stabilizer of `h` and over block-lattice translations of the torus without changing the identity, locality or (with Euclidean norms) the bounds. With the sup norm on `Fin N → ℂ` averaging over the stabilizer costs at most `√N`. | P4 (H.7), p. 679 | None. |
| F-8 | NOTE | `IsPolymer`, `logPartition_multiscale` | The block-count / tree-length conversion of design choice 2 is correct in the direction needed (§C.4): every `X ∈ 𝒟_j` is a draft polymer, and `d_j(X) ≥ n/(C_d L^{2d}) − 1` with `n` the number of `ML^j`-blocks; conversely `d_j(X) ≤ n`. The draft's polymer class is larger than `𝒟_j` (single blocks, thin sets), which only weakens the statement. | P1 (2.26)–(2.27), p. 117 | None. |
| C-2 | NOTE | `lowTemperature_correlations` | `∃ ρ₁ ∈ (0,1)` is a faithful reading of "small ρ₁" and is the minimum for content (`ρ₁ ≥ 1` would make `|m − 1| ≤ cβ^{−1+ρ₁}` trivial for `c ≥ 2`). P9's constraints (`ρ₁ ≥ 3ρ₂`, `ρ₂ > 0` arbitrary, p. 511) support the stronger `∀ ρ₁ ∈ (0,1), ∃ β₀ c c' ρ₀`. | P9 p. 494, p. 497 ((2.9) and the remark after it), p. 511 | Optional strengthening; not recommended for freezing without an author ruling. |
| C-3 | NOTE | `lowTemperature_correlations` | Existence of the `ν ↓ 0` limits of `m`, `Gtr`, `Glg` is asserted by the series but not proved in it (P4 p. 720: "each term of the series has a limit as v → 0"; P5 (1.46); P9 p. 518 proves only `S(k) → 0` for the explicit Gaussian part). The draft commits to it (roadmap C-3). | P4 p. 720; P5 p. 501; P9 pp. 517–518 | None; record as a reconstruction (roadmap §3.5). |
| C-4 | NOTE | `lowTemperature_correlations` | `c, c', ρ₀, ρ₁` before `β` is the strong reading of roadmap question 6 (open). It agrees with P9 §§3–4 (all exponents and `O(1)` constants are β-independent; `c'` comes from the propagator rate δ and `δ₀ = κ/M`). | P9 pp. 511, 517–519 | None until Roland answers question 6. |
| D-1 | NOTE | `energy`, `aprioriMeasure` | At `ℓ = 2` the sum `∑_x ∑_μ` counts each bond twice and at `ℓ = 1` there are no bonds; no statement forces `ℓ ≤ 2` (the prover chooses `L, M, ℓ₀`). `volume.toSphere` is the unnormalized surface measure; the hard-spin limit of P1 (1.6) is `∏ δ(|φ_x|² − 1) dφ_x = ∏ ½σ(dφ_x)`. Both constants cancel in `Z(g)/Z(0)` and in expectations. | P1 (1.2), p. 103; (1.6), p. 104 | None. |
| D-2 | NOTE | both roots | `hd` and `hN` do not occur in the conclusions but are needed: for `N = 1` the factor `δ_ik − h_i h_k` vanishes identically, so `Gtr` would be unconstrained in Root-C; for `d ≤ 2` no `G` with `−ΔG = δ₀`, `G → 0` exists, and Root-F would contradict Mermin–Wagner. Once proofs exist the hypotheses will be used, so no unused-variable warning is expected. | — | None. |

## A. Model fidelity (Def-1)

A.1 Energy. P9 (1.1) (p. 493) and P1 (1.5) (p. 104) give
`β(½‖∂φ‖² + (λ/8)‖|φ|²−1‖² + (ν/2)‖φ−h‖²)`, with `½‖∂φ‖² = ½∑_{⟨x,x′⟩⊂T}|φ(x)−φ(x′)|²`
over unordered nearest-neighbour pairs (P1 (1.2), p. 103). At `λ = ∞` the middle term is replaced by
the constraint (P1 (1.6), p. 104). The draft's `½ ∑_x ∑_μ ‖φ(x+e_μ) − φ(x)‖² + (ν/2) ∑_x ‖φ(x) − h‖²`
equals this for `ℓ ≥ 3` (each unordered bond once). For `ℓ = 2` each bond is counted twice; no root
forces `ℓ ≤ 2` (D-1). Verdict: correct.

A.2 A priori measure. P1 (1.6): `lim_{λ→∞} exp[−βA_λ − E_λ] = exp[−β(½‖∂φ‖² + (ν/2)‖φ−h‖²) − E_∞] ∏_x δ(|φ(x)|²−1)`
with `dφ` Lebesgue. Since `δ(r² − 1) = ½δ(r − 1)`, the a priori measure is `∏_x ½σ(dφ_x)`.
Mathlib's `Measure.toSphere` of Lebesgue measure is `σ` (`toSphere s = N · vol((0,1)·s)`). The factor
`2^{−ℓ^d}` and the total mass of `σ` cancel in `Z(g)/Z(0)` and in `gibbsExpectation`. The measure is
O(N)-invariant, which Root-C needs for the `h`-independence of `m, Gtr, Glg` (§D.5). Verdict: correct.

A.3 Source term. P1 p. 108: "we add the linear function ⟨g,φ⟩ to the exponent in (1.1), where g is
defined on T and has values in ℂ^N"; P9 (1.1) has `+⟨g,φ⟩`. The pairing must be complex-bilinear,
since P4 (H.7) (p. 679) requires `ℳ^{(j)}` to be analytic in `g` and `ℱ = ⟨g, ℳ⟩₁`. The draft's
`∑_x ∑_i g_i(x) φ_i(x)` with sign `+` is correct.

A.4 Domain and logarithm. P9 (1.1) takes `‖g‖_{ℓ¹} < 1`; the natural reading is
`∑_x |g(x)|` with the Hermitian norm on `ℂ^N`. The draft's `∑_x ∑_i |g_i(x)| ≥ ∑_x |g(x)|`, so its
domain is smaller and every claim on it is weaker; acceptable. On the draft's domain
`|Im⟨g,φ⟩| ≤ ∑_x ∑_i |g_i(x)| < 1 < π/2` because `|φ_i(x)| ≤ 1`, hence
`Re(Z(g)/Z(0)) = ⟨e^{Re⟨g,φ⟩} cos(Im⟨g,φ⟩)⟩ > 0`. The principal `Complex.log` is therefore analytic
on the (connected) domain, vanishes at `g = 0`, and equals the analytic logarithm, which is Balaban's
`log Z(g)` with `E` chosen so that `Z(0) = 1` (P9 (1.1), P7 (4.16) p. 533). The same holds on
`∑_x |g(x)| < π/2`. Verdict: correct.

A.5 Lean. `partitionFunction` integrates a bounded continuous function against a finite product
measure; `gibbsExpectation` divides by a positive real integral. No junk values arise on the carriers
used by the roots.

## B. Torus sides and the infinite-volume limit

B.1 What the series uses. P1 p. 103 defines `T = {x ∈ ℤ^d : −L_μ ≤ x_μ < L_μ}` (rectangular,
sides `2L_μ`). P1 p. 117: the large-cube partitions at scale `j` are "determined by the lattices
`L^jMℤ^d`", which tile the torus only if `L^jM` divides each side. P4 p. 680 quantifies over "all
admissible tori" without a definition. No passage requires a side of the exact form `ML^n`; the
method needs `ML^{j}` to divide the side for every scale `j` used, i.e. `ML^{k_f+1} ∣ ℓ` for the
representation up to scale `k_f + 1`. The draft's "every `ℓ` divisible by `ML^{kf+1}`" is supported
(cubic tori only, a harmless restriction). The final step on the smallest such torus
(`ℓ = ML^{kf+1}`, one top-scale block) is within the framework: the final fluctuation integral has a
mass of order `L^{−1}` on a torus of side `ML` at scale `k_f` (P4 (6.5), p. 719).

B.2 The limit. P9 p. 494 writes `⟨·⟩ = lim⟨·⟩_T` without saying along which tori; P5 (1.46)
(p. 501) and P4 p. 720 write `T → ℤ^d` and derive the limit from torus independence and tree decay.
The natural reading is: tori whose sides are admissible for the given `ν` and tend to infinity.

B.3 Comparison of limit notions (for fixed `β, ν, h, x, y`):

- *All `ℓ → ∞`* (`atTop`): strongest; it implies the divisibility-net limit (take `ℓ₀ ≥ N`). Not
  obtainable from the RG, which needs `ML^{kf+1} ∣ ℓ`.
- *Divisibility net* (draft): implies the limit along `n!` (cofinal in divisibility). It does **not**
  imply the limit along `ML^n`: `ℓ₀` is existential and may contain primes not dividing `ML` (C-1).
- *Side `ML^n` with `L, M` existential*: incomparable with the net; ties Root-C to RG constants.
- *Proposed (§G.2):* `∃ q ≥ 2, ∀ ε, ∃ n₀, ∀ ℓ, q^{n₀} ∣ ℓ → …`. It implies the net (`ℓ₀ = q^{n₀}`),
  the limits along `q^n` and `n!`, and is what the RG gives with `q = L`, `M = L^m` (the series'
  choice, P5 p. 491 "`L^m = M`"), using F-2.

Verdict: the divisibility net is a defensible but weaker reading; MINOR (C-1).

## C. Root-F

C.1 Source chain. P7 (4.15)–(4.17) (p. 533): `∫dψ_kρ_k = exp[ℱ_{k+1,0}(h,g) + ∫_0^1 dt ⟨∂_gℛ^{(k+1)}(h,tg), g⟩₁]`
and `ℱ(h,g) = ⟨g,h⟩₁ + ∑_{j=1}^k ⟨g,ℳ^{(j)}(h,g)⟩₁ + ∑_{n=0}^m ⟨g,ℳ_n^{(k+1)}(h,g)⟩₁`; the
`ℳ^{(j)}` satisfy P4 (H.7) and `ℳ_n^{(k+1)}` the same with prefactor `β_k^{−n}` (`n > 0`) and as in
(H.7) for `n = 0`. P9 (4.4)–(4.7) (p. 516) gives the same with `𝒫^{(k+1)}(Y;g)`,
`|𝒫| < β_k^{−2}e^{−2κ d_{k+1}(Y)}` (`Y ∈ 𝒟_{k+1}`); P7 (4.14) puts `𝒫` into `ℛ_m''^{(k+1)}` with
bound `½β_k^{−m−1}e^{−κd_{k+1}}`. P4 (6.7) (p. 720) has the small-field version with `j = 1,…,k₁+1`.
So the identity, the `j`-range `1..kf+1`, locality ("depends on g restricted to X", P4 (H.7)) and
analyticity on `‖g‖_{ℓ¹} < 1` are all source statements. The folding of `ℳ_n^{(k+1)}` (`n = 0..m`) and
`𝒫` into `j = kf + 1` is consistent: P5 H4 (p. 491) localizes `ℛ_n^{(k)}` over `X ∈ 𝒟_k` (not at
coarser scales), and, with `β_k^{−1} ≤ 2L^{−k(d−2)}β^{−1}` (P9 p. 518), `β_k^{−n} ≤ 2^nβ^{−n}L^{−nk(d−2)} ≤ c₉L^{−(k+1)(d−2)/2}` for `β ≥ β₀(c₉, L)`.
Exception: the bound on the whole domain (C.2).

C.2 The `g` domain of the bounds (F-1). The top-scale functions `ℛ_n^{(k+1)}`, `𝒫(Y;·)` are not of the
form `⟨g,·⟩`. P7 (4.15) converts them by `ℛ(g) − ℛ(0) = ∫_0^1 ⟨∂_gℛ(tg), g⟩dt`, with the
`g`-independent parts cancelled by the normalization (4.16). A bound on
`T(x,X;g) = ∫_0^1 ∂_{g(x)}ℛ(X;tg)dt` from a bound on `ℛ` over `{‖g‖ < 1}` needs a Cauchy estimate of
radius `1 − t‖g‖`; integrated over `t` this gives `sup|ℛ| · (−log(1−‖g‖))/‖g‖`, unbounded near the
boundary. P5 H4 gives analyticity only on `‖g‖_{ℓ¹} < 1`, so no margin is available. The same
device produces the lower-scale `ℳ^{(j)}` (P5 p. 518), so the uniform claim of P4 (H.7) on the whole
ball is a source assertion whose derivation is not written. For the global function the tilted
expectation `∫_0^1 (⟨φ_x⟩_{tg} − h)dt` is uniformly bounded (by `1/cos 1`), so the global Gleason-type
problem is solvable; for the localized multiscale pieces no argument exists. Fix: bounds on
`∑∑‖g y i‖ ≤ 1/2` (Cauchy radius `1/4`, factor 4 absorbed in `c₉`), analyticity and identity on
`< 1`. The identity on the smaller set would in any case extend by the identity theorem.

C.3 Constants and quantifiers. Draft order: `∀κ ∀c₉ ∃L M β₀ ∀β ∀ν ∀h ∃kf ∀ℓ ∃T`. Source order
(roadmap §4.4): `L, γ, α₁` → `κ` → `M` → `c₈, c₉` → … → `β₀`. Given target `(κ, c₉)`, choose `L`
(source), `κ_s = C_dL^{2d}κ` (C.4), `M = M(κ_s)`, `c₉,s ≤ c₉e^{−κ_s}/4` (absorbing C.4's `e^{κ_s}` and
F-1's factor 4), then `β₀`; P4 (5.40) (p. 718) allows `c₉ = β^{−1/4}`, so any `c₉ > 0` is reached by
`β₀ ≥ c₉^{−4}·(…)`. P4 Thm 1 (p. 680) quantifies "for any M, κ, α₁, γ, c₈, c₉ … M, κ sufficiently
large … c₉ sufficiently small", consistent with this order. `β₀` independent of `ν, h, ℓ`: correct
(P9 p. 494, the point of the theorem). `kf` after `β` and `ν`: correct (`k_f` depends on both through
`δ_k` of (H.6)).

C.4 Tree length versus block count (design choice 2). P1 (2.26)–(2.27) (p. 117): `π_j` is the
partition into `M`-cubes of scale `j` (side `ML^j` in lattice units), `π′_j` the cover by `LM`-cubes
(unions of `L^d` cubes of `π_j`), `𝒟_j` the connected unions of open cubes of `π′_j`,
`d_j(X) = inf{M^{−1}|Γ|}` over continuous trees `Γ ⊂ X` meeting every `□ ∈ π′_j`, `□ ⊂ X`.

- *`𝒟_j ⊂` draft polymers.* Two `LM`-cubes of the `M`-grid overlap iff they share an `M`-cube, so a
  connected union of open `LM`-cubes is a face-connected union of `M`-cubes, which is exactly
  site-level nearest-neighbour connectedness of a union of blocks (`IsPolymer`, block side `ML^j`).
- *Lower bound (the direction needed).* Let `n` be the number of `M`-cubes in `X`. The `LM`-cubes in
  `X` cover `X`, so there are at least `n/L^d` of them. A tree of length `λ` (in units of `M`) meets
  at most `C_d(λ + 1)` cubes of `π_j`, and each lies in at most `L^d` cubes of `π′_j`; so
  `n/L^d ≤ L^dC_d(d_j(X) + 1)`, i.e. `d_j(X) ≥ n/(C_dL^{2d}) − 1`. Hence
  `e^{−κ_s d_j(X)} ≤ e^{κ_s}e^{−κ n}` with `κ_s = C_dL^{2d}κ`. The prefactor `e^{κ_s}` is absorbed by
  `c₉,s`, chosen after `κ_s` and `M` (C.3). This is valid because `L` is chosen before `κ_s` in the
  source order, and the draft lets `L` depend on `κ`.
- *Upper bound (equivalence only).* A tree through the centres of the `n` blocks, along adjacent
  blocks inside a common `LM`-cube of `X`, has length `≤ n − 1`, so `d_j(X) ≤ n` (better than the
  drafter's `C_dLn`). Thus `e^{−κn} ≤ e^{−κd_j(X)}` and the draft's decay is not weaker than the
  source's.
- At the top scale P7 (4.14) indexes `𝒫` by `X ∈ 𝒟_k` with decay in `d_{k+1}(X)`: replace `X` by
  the union `X̄` of the scale-`(k+1)` blocks meeting it (a connected union of blocks, since
  `ML^k ∣ ML^{k+1}`); the number of blocks of `X̄` is `≤ C_d(d_{k+1}(X) + 1)`. Locality is preserved
  (`g|_X` is a restriction of `g|_{X̄}`).

Verdict: the argument is correct, including the quantifier order.

C.5 `kf`. `k_f` = first `k` with `ν_k > (7/8)L^{−2}` (P9 p. 515, P7 p. 529, P4 p. 719), and
`ν_k = νL^{2k}δ_k`, `δ_k^{±1} < exp(c₈∑_jL^{−2γj})` (P4 (H.6)). P4 p. 719: `ν_{k₁−1} ≤ (7/8)L^{−2}`,
hence `ν_{k₁} < 1`, so `L^{k_f}√ν < δ_{k_f}^{−1/2} < e^{c₈C/2} ≤ L` for `c₈` small. The draft's
`L^{kf}√ν ≤ L` holds. Minimality also gives `L^{k_f+1}√ν > (7/8)^{1/2}e^{−c₈C/2} ≥ 1/2`, an optional
lower bound (F-4). The `j`-range `1..kf+1` matches P4 (6.7) and P7 (4.17).

C.6 Can Root-F be satisfied trivially, or is it false?

- *`T = 0`*: false (`log Z(g)/Z(0) ≠ ⟨g,h⟩`).
- *`kf = 0`* (allowed): the identity gives, at `g = 0`,
  `⟨φ_i(x);φ_k(y)⟩_ℓ = ∑_X [∂_{g_k(y)}T_i(1,x,X)(0) + ∂_{g_i(x)}T_k(1,y,X)(0)]`, nonzero only for
  `x, y ∈ X`. Cauchy estimates and the bound give `|⟨φ_x;φ_y⟩_ℓ| ≤ 4c₉∑_{X∋x,y}e^{−κn(X)}`, which
  for `κ` above the lattice-animal threshold (allowed by `∀κ`) decays like `e^{−c|x−y|/(ML)}` uniformly
  in `ν` and `ℓ`. Root-C (b) gives `Gtr₀(x) ≈ m₀²/(βγ)G(x) ∝ |x|^{−(d−2)}` and `Gtr(ν,·) → Gtr₀`,
  a contradiction for small `ν`. So the prover must use about `log_L ν^{−1/2}` scales.
- *Everything at the top scale on the smallest torus* (`ℓ = ML^{kf+1}`, one block, decay factor
  `e^{−κ}`, all lower-scale terms zero): the first derivative of the identity at `g = 0` gives
  `T(kf+1, x, torus; 0) = ⟨φ_x⟩_ℓ − h`, so this requires
  `|⟨φ_x⟩_ℓ − h| ≤ c₉e^{−κ}L^{−(kf+1)(d−2)/2} ~ c₉e^{−κ}ν^{(d−2)/4}`, false for small `ν` at fixed
  `β`, since `|⟨φ_x⟩_ℓ − h| ~ (N−1)/(2β)`. The lower scales are needed.
- *Small tori, wrapping polymers*: no falsity found; Balaban's bounds are uniform over admissible
  tori, and wrapping polymers carry the same tree-length decay.
- *`g` near the boundary of the domain*: unsupported (F-1).

C.7 Omissions. Torus independence: material (F-2). Covariance: immaterial (F-7). Gap exponent:
MINOR (F-3). Separate top-scale pieces and `𝒫`: folding is consistent (C.1).

C.8 Junk scales. `T j`, `j ∉ [1, kf+1]`: harmless (F-5). For `j > kf + 1` the block side may not
divide `ℓ` and `IsPolymer` then uses truncated blocks; irrelevant since these terms are absent from
the identity.

## D. Root-C

D.1 Clause-by-clause comparison with P9 Thm 1.1 (pp. 494–495), hard spins (`λ = ∞ ≥ λ₀`):

| P9 | Draft | Check |
|---|---|---|
| `M(x) = m(β,v)h` | onePoint limit `= m ν * h i` | correct; `m` independent of `h`, `x` by symmetry (D.5) |
| `G = G_tr(x−y)(I − h⊗h) + G_lg(x−y)h⊗h` | `Gtr ν (x−y) * ((if i = k then 1 else 0) − h i * h k) + Glg ν (x−y) * (h i * h k)` | correct encoding of `(I − h⊗h)_{ik}`, `(h⊗h)_{ik}`; for `N ≥ 2` both functions are determined |
| (a) `|m − 1| < cβ^{−1+ρ₁}` | `≤ c * β ^ (-1 + ρ₁)` | equivalent (`<` vs `≤` immaterial) |
| (a) `|G_tr|, |G_lg| ≤ c|x−y|^{−(d−2)}e^{−c′√v|x−y|}` (printed `|G_tr(x−y) − |`) | `c(1+‖x‖)^{−(d−2)}e^{−c′√ν‖x‖}`, sup norm | equivalent up to constants (D.4) |
| (b) `G_tr = m²(β)/(βγ_∞)Δ^{−1} + R`, `|R| < c(1+|x−y|)^{−(d−2+ρ₀)}`, `|γ_∞−1| < cβ^{−1}` | `|Gtr₀ x − m₀²/(βγ) G x| ≤ c(1+‖x‖)^{−(d−2+ρ₀)}`, `0 < γ`, `|γ−1| ≤ c/β` | correct; `γ` is determined by `Gtr₀` (D.3), so existential `γ` adds no freedom |
| (b) `|G_lg| ≤ c(1+|x−y|)^{−(d−2+ρ₀)}` | `|Glg₀ x| ≤ …` | correct |
| "for the v ↓ 0 limiting expectations" | `Tendsto … (𝓝[>] 0)` of `m`, `Gtr`, `Glg` | correct reading; existence is a commitment (C-3) |

The printed defects: part (a)'s `|G_tr(x−y) − |` is read as `|G_tr(x−y)|`; in the theorem the bound
of (b) prints `c/(1+|x−y|)^{d−2+ρ₀}` (correct); the abstract omits the minus sign. The draft uses the
correct forms.

D.2 Normalization. P9 p. 494 sets `Δ ≡ −∂*∂`, so `½‖∂φ‖² = ½⟨φ, −Δφ⟩` with the standard lattice
Laplacian. P9 (4.17) (p. 518) decomposes the covariance of `exp[−½(∂φ,∂φ)]`, i.e. `(−Δ)^{−1}`, and
(4.18) (p. 519) `β_j^{−1} = (βγ_∞)^{−1}L^{−j(d−2)} + O(β^{−1})L^{−j(d−2+2γ)}` turns
`∑_jβ_j^{−1}G^{(j)}(0)` into `(βγ_∞)^{−1}(−Δ)^{−1}` plus a subdominant term. With the draft's energy
(`½∑∑|φ(x+e_μ)−φ(x)|²`) the transverse spin-wave covariance is `β^{−1}(−Δ+ν)^{−1}`, so
`m₀²/(βγ)·(−Δ)^{−1}(0,x)` is the right normalization.

D.3 The Green's function. The draft's `∑_μ(2G(x) − G(x+e_μ) − G(x−e_μ)) = δ_{x,0}` is `−ΔG = δ₀`.
Uniqueness under `G → 0` along `cofinite` (= as `‖x‖ → ∞`): the difference of two solutions is
harmonic on `ℤ^d` and tends to 0, so by the maximum principle it vanishes. Existence for `d ≥ 3`:
`G = (2d)^{−1}∑_n P(S_n = x)` (simple random walk), which tends to 0. This is the positive
`(−Δ)^{−1}(0,x)` of P9 (4.17) on `ℤ^d` (sum over all `j ≥ 0`). Since `G(x) ~ C_d|x|^{−(d−2)}` and the
error is `O(|x|^{−(d−2+ρ₀)})`, the coefficient `m₀²/(βγ)` is the limit of `Gtr₀(x)/G(x)`; `γ` is
therefore determined, and `0 < γ`, `|γ − 1| ≤ c/β` is a genuine claim.

D.4 Norms. For `x ≠ 0`, `|x|₂ ≥ ‖x‖_∞ ≥ (1+‖x‖_∞)/2`, so P9's bound implies the draft's with `c·2^{d−2}`
and the same `c′`; conversely with `√d` changes in `c′`. At `x = 0` P9's bound is vacuous and the
draft's (`|G(0)| ≤ c`) holds since `|G| ≤ 2` and `c` may be taken `≥ 2`. `‖x‖` on `Fin d → ℤ` is the
sup norm (probe in §G.3); `(1 + ‖x‖)^{−s}` has base `≥ 1`, so no `rpow` junk.

D.5 Independence of `h`. The energy satisfies `E(Rφ; Rh) = E(φ; h)` for `R ∈ O(N)` and the product
surface measure is O(N)-invariant, so `⟨φ_x⟩_{Rh} = R⟨φ_x⟩_h` and `G_{Rh} = RG_hR^T` on every torus.
Reflections fixing `h` force `⟨φ_x⟩_h ∥ h` and the block form `a(I − h⊗h) + b h⊗h` (for `N ≥ 3` by
irreducibility of the stabilizer on `h^⊥`; for `N = 2` the reflection kills the off-diagonal entries).
Hence `m, Gtr, Glg` independent of `h` is exact, already in finite volume. Translation invariance of
the torus gives the dependence on `x − y`. Choosing them after `β` and before `h` is justified.

D.6 Constants versus `β` (question 6). Before `β` is the strong reading; it agrees with the proof:
the exponent constraints of P9 p. 511 are β-free, `c′` comes from the decay rate δ of `G_j`, `C^{(j)}_{tr}`
(p. 518) and from `δ₀ = κ/M` for the remainder terms (p. 517), and the `O(1)` constants depend on
`L, M, κ, …` only (C-4). The first clause's `ℓ₀` (or `n₀`) depends on `ν, h, x, y, ε`: correct.

D.7 `ρ₁`. `0 < ρ₁ < 1` is necessary for content and faithful; the source supports any `ρ₁ > 0`
(C-2). `0 < ρ₀` with no upper bound: the prover chooses it; correct.

D.8 Existence of limits. The thermodynamic limit is used, not proved, in P9 (p. 494); it follows from
torus independence (P4 p. 720), which is why F-2 matters. The `ν ↓ 0` limits are asserted in P4
p. 720, P5 (1.46), P9 p. 495 and proved in P9 only for the explicit Gaussian part (C-3).

## E. Lean semantics

- `(x μ).val / s` on `ZMod ℓ` (`NeZero ℓ`): the representative in `[0, ℓ)` and natural division;
  blocks `{x : ⌊x_μ/s⌋ = c_μ}` aligned at 0. When `s ∣ ℓ` (all `j ≤ kf + 1`) they tile the torus and
  the block of the cast of `y ∈ ℤ^d` is the image of the `ℤ^d`-block of `y` (used in §G.1's
  agreement clause). For `s ∤ ℓ` the last block is truncated (only `j > kf + 1`, harmless).
- `Pi.single μ 1` on `Fin d → ZMod ℓ` and on `Fin d → ℤ`: the unit vector `e_μ`; on the torus the
  addition wraps (periodic boundary conditions). For `ℓ = 2`, `x + e_μ = x − e_μ` (probe), for
  `ℓ = 1`, `e_μ = 0`; neither is forced by a root (D-1).
- `‖x‖` on `Fin d → ℤ`: sup norm (`Pi.norm_def`, probe). `‖T j x X g‖` on `Fin N → ℂ`: sup norm,
  weaker than the Euclidean norm by at most `√N`; acceptable.
- `rpow`: bases `L ≥ 2`, `1 + ‖x‖ ≥ 1`, and `β ≥ β₀` where `β₀` is the prover's choice (a nonpositive
  `β₀` only makes the statement harder for the prover). `c / β`, `m₀²/(βγ)`: no exploitable division by
  zero for the same reason; `γ > 0` is required.
- `∀ (ℓ : ℕ) [NeZero ℓ], …`: consumers must supply the instance (e.g. from `ℓ₀ ∣ ℓ` they cannot
  infer it automatically); harmless.
- `∑ X : Finset (Torus d ℓ)`: a finite sum over all `2^{ℓ^d}` subsets; `T = 0` off polymers makes it
  the polymer sum.
- `AnalyticOnNhd ℂ (T j x X) {g | …}` on the finite-dimensional space `Torus d ℓ → Fin N → ℂ`:
  holomorphy; correct.
- `hd`, `hN`: needed for the meaning of the roots (D-2).
- `Complex.log`: principal branch, correct on the domain (A.4).

## F. Points the drafter did not address

1. The Cauchy-estimate degeneration at the boundary of the `g` domain (F-1); this is the main defect.
2. The limit notion does not include the RG tori `(ℤ/ML^nℤ)^d` (C-1).
3. Root-F with `kf = 0` is admissible as a witness and is false only because of Goldstone behaviour;
   this is worth recording as the reason the existential `kf` is not vacuous (F-4).
4. `∀ κ` is what prevents a single-scale representation; it rests on the roadmap §4.4 order and the
   open point on P3's `κ₀` (F-6).
5. The regime `ν > (7/8)L^{−2}` (`k_f = 0`) is not covered by the written flow (F-4).
6. `hN` is what makes `Gtr` determined in Root-C (D-2).

## G. Replacement code

### G.1 Root-F (fixes F-1, F-2, F-3, F-5)

Add the import `public import Mathlib.Data.ZMod.ValMinAbs` (needed for `ZMod.valMinAbs`), and replace
the draft's Root-F by:

```lean
/-- Root-F. -/
theorem logPartition_multiscale (d N : ℕ) (hd : 3 ≤ d) (hN : 2 ≤ N) :
    ∃ δ : ℝ, 0 < δ ∧
    ∀ κ : ℝ, 0 < κ → ∀ c₉ : ℝ, 0 < c₉ →
    ∃ L M : ℕ, 2 ≤ L ∧ 1 ≤ M ∧ ∃ β₀ : ℝ, ∀ β : ℝ, β₀ ≤ β →
    ∀ ν : ℝ, 0 < ν → ν ≤ 1 → ∀ h : EuclideanSpace ℝ (Fin N), ‖h‖ = 1 →
    ∃ kf : ℕ, (L : ℝ) ^ kf * Real.sqrt ν ≤ L ∧
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
```

Remarks on G.1.

- The agreement clause compares the terms for the images of the same finite set `A ⊂ ℤ^d` in two
  admissible tori, when `A` lies in the centred box of half-width `< ℓ/4` and `< ℓ′/4`. In such a box
  the cast is injective, no wrap-around adjacency occurs (coordinate differences are `< ℓ/2 ≤ ℓ − 1`),
  the cast of a `ℤ^d`-block is a torus block (`s ∣ ℓ`), so `A.image` is a polymer in one torus iff in
  the other, and `valMinAbs` inverts the cast on `A`; hence both sides depend only on `g|_A`. The clause
  is a special case of P4 (H.4) (p. 677), whose non-winding condition is "side of a bounding box `<` torus
  side". Terms at polymers away from the origin are not compared; this suffices for limits at fixed
  points.
- Choosing `T` before `∀ ℓ` is required to state the clause; it does not change the content of the
  per-torus clauses.
- Optional (F-4): add `1 / 2 ≤ (L : ℝ) ^ (kf + 1) * Real.sqrt ν ∧` after the upper bound on `kf`.
- If F-3 is not wanted, delete `∃ δ : ℝ, 0 < δ ∧` and use the draft's exponent.

### G.2 Root-C (fix C-1)

Replace the first lines of the draft's statement, from `∀ β : ℝ, β₀ ≤ β →` to the end of the first
clause, by:

```lean
    ∀ β : ℝ, β₀ ≤ β →
    ∃ q : ℕ, 2 ≤ q ∧
    ∃ (m : ℝ → ℝ) (Gtr Glg : ℝ → (Fin d → ℤ) → ℝ),
      (∀ ν : ℝ, 0 < ν → ν ≤ 1 → ∀ h : EuclideanSpace ℝ (Fin N), ‖h‖ = 1 →
        ∀ x y : Fin d → ℤ, ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ,
          ∀ (ℓ : ℕ) [NeZero ℓ], q ^ n₀ ∣ ℓ →
            (∀ i, |onePoint d N ℓ β ν h (fun μ => (x μ : ZMod ℓ)) i - m ν * h i| < ε) ∧
            ∀ i k, |twoPointTruncated d N ℓ β ν h (fun μ => (x μ : ZMod ℓ))
                (fun μ => (y μ : ZMod ℓ)) i k
              - (Gtr ν (x - y) * ((if i = k then 1 else 0) - h i * h k)
                  + Glg ν (x - y) * (h i * h k))| < ε) ∧
```

The rest of the draft's statement is unchanged. The full statement as elaborated is
`lowTemperature_correlations_v2` in the probe file.

### G.3 Elaboration

`/home/scott/Balaban-scratch/audit/AuditVariants.lean` (the draft's imports plus
`Mathlib.Data.ZMod.ValMinAbs`, the draft's definitions verbatim, `logPartition_multiscale_v2` = §G.1,
`lowTemperature_correlations_v2` = §G.2 spliced into the draft's Root-C) was elaborated with
`cd /home/scott/Balaban && lake env lean /home/scott/Balaban-scratch/audit/AuditVariants.lean`
(Lean v4.35.0-rc2, Mathlib `065356127b1d`). Result: no errors; the only diagnostics are
`declaration uses sorry` on the two theorems. The §G.1 code block is textually identical to the
elaborated declaration (except the name suffix `_v2`); the §G.2 lines occur verbatim in it.

Semantic probes in the same file, all accepted:

- `‖x‖ = ↑(Finset.univ.sup fun μ => ‖x μ‖₊)` for `x : Fin 2 → ℤ` (`Pi.norm_def`): the sup norm.
- `ZMod.valMinAbs (n := ℓ) (y : ZMod ℓ) = y` when `2 * |y| < ℓ` (via `ZMod.valMinAbs_spec`): the
  lift used in the agreement clause inverts the cast on the polymers it compares.
- `(L : ℝ) ^ 0 * Real.sqrt ν ≤ L` for `L ≥ 2`, `ν ≤ 1`: `kf = 0` is always admissible in the draft (F-4).
- `(1 : ZMod 2) + 1 = 0`: on the side-2 torus `x + e_μ = x − e_μ` (D-1).

Note on dot notation: `(z μ).valMinAbs` fails for `z : Torus d ℓ` (the type of `z μ` is unfolded past
`ZMod ℓ`, error `Invalid field valMinAbs`); the explicit `ZMod.valMinAbs (n := ℓ) (z μ)` is required.

## Re-audit of v1.1

Object: the ten files under `/home/scott/Balaban-scratch/p0/tree/Balaban/Frozen/` and the packet
files `notes/phase0/packet-head.md`, `notes/phase0/packet-binders.md` (with `packet-code.md` checked
for agreement with the tree). Probe: `/home/scott/Balaban-scratch/audit/ReauditProbe.lean`, elaborated
with `cd /home/scott/Balaban-scratch/p0/tree && lake env lean …`: no errors, no warnings.

**Verdict: CHANGES-REQUIRED (docstrings and packet wording only).** Every Lean statement and
definition body is approved as written. Two docstrings in files that will be frozen (R-1, R-2)
describe the statement inaccurately and cannot be edited after the freeze; one packet citation
(R-3) is wrong. Exact replacement text is given below. After these edits the verdict is APPROVE-WITH-NOTES.

| ID | Severity | Location | Finding | Evidence | Fix |
|---|---|---|---|---|---|
| R-1 | MINOR | `Roots/LogPartitionMultiscale.lean`, module docstring, lines 25–27 | The sentence "the terms do not depend on the torus for polymers that do not wind around it (P4 (H.4))" claims more than the agreement clause states. The clause only compares the images of `A ⊂ ℤ^d` in the centred box of half-width `< ℓ/4` **and** `< ℓ′/4`; the docstring's "box `\|y_μ\| < ℓ/4`" omits `ℓ′`. | Statement lines 62–68; P4 (H.4), p. 677 | Replace lines 25–27 by the text in R-1 below. |
| R-2 | MINOR | same docstring, line 17 | The summary "For every `κ` and `c₉` there are `L, M, β₀`" omits the leading `∃ δ > 0`, yet `δ` then appears in the bound (line 24) without being introduced. | Statement line 40 | Replace line 17 by the text in R-2 below. |
| R-3 | MINOR | `packet-binders.md`, Root-F row `∃ L ≥ 2, M ≥ 1` | "P1 pp. 103, 117 (L large, M = L^m)" is wrong in two ways. P1 p. 103 concerns the torus half-sides `L_μ`; the block factor `L` is introduced on p. 107 ((1.11), `L`-blocks). No source states "L large": BIG_PICTURE §4 finds no largeness condition, and P2 (4.26) uses `L ≥ 3`. | P1 pp. 103, 107, 117 | Replace the citation with "P1 p. 107 ((1.11), L-blocks), p. 117 (M = L^m)". |
| R-4 | NOTE | `packet-binders.md`, rows `hd, hN` (Root-F) | "P1 title and p. 103" do not state `d ≥ 3, N ≥ 2`; P1 p. 105 and Thm 2.2 (p. 120) do, as does the P9 abstract (p. 493). | P1 pp. 103, 105, 120 | Correct the citation. |
| R-5 | NOTE | `packet-binders.md`, row `∀ κ > 0` | Classified SOURCE, but the root's `κ` is a decay rate per block, obtained from the source's tree-length `κ` through the conversion of §C.4. SOURCE/PROPOSED is the accurate class, like the polymer row. With that change the Root-F counts become 9 SOURCE and 7 SOURCE/PROPOSED. | §C.4; P1 p. 118 | Optional reclassification. |
| R-6 | NOTE | `packet-binders.md`, row `∃ k_f` | The upper bound `L^{k_f}√ν ≤ L` rests on P4 p. 719 (`ν_{k₁−1} ≤ (7/8)L^{−2}`, hence `ν_{k₁} < 1`), which is not cited. | P4 p. 719 | Add the citation. |
| R-7 | NOTE | `packet-head.md`, S0-Q02 | "(in the proof `q = L`, `M = L^m`)": `q = L` works only when `M` is a power of `L`, but roadmap §4.4 step 3 allows `M = L^{m₀}M₁` (P3). `q = ML` works for every `M`. | roadmap §4.4; P3 p. 68 (per the review) | Write "(in the proof `q = ML`, or `q = L` when `M = L^m`)". |
| R-8 | NOTE | both root docstrings (lines 30, 24); `packet-code.md`; `notes/QUESTIONS-ROLAND-1.md` | "Decision record: `notes/phase0/surface-v1-for-approval.md`" names a file that does not exist; the packet currently consists of `packet-*.md`. The path sits inside frozen text. | `ls notes/phase0` | Create the file at that path (the assembled packet) before freezing. |
| R-9 | NOTE | `Geometry/IsPolymer.lean`, module docstring | "the torus is partitioned into the blocks of side `s`" holds only when `s ∣ ℓ`. The comparison with the tree length `d_j(X)` applies to `X ∈ 𝒟_j`, where `d_j` is defined. Both are implicit in the context; not wrong. | §C.4, §E | None required. |
| R-10 | NOTE | `Roots/LogPartitionMultiscale.lean`, docstring line 20 | "`k_f` is the number of renormalization steps before the last one" is an interpretation. In the statement `k_f` is existential and constrained only by the two inequalities, which pin it to two adjacent values. | Statement line 44 | None required. |
| R-11 | NOTE | `packet-head.md`, S0-Q05 | "`δ = γ − α₁` is Balaban's irrelevancy gap": P9 p. 495's gap is `γ`; `δ` is the gap less the loss `α₁`. It is positive because P4 Thm 1 lets `α₁` be taken small. | P9 p. 495; P4 (H.7), p. 679 | Optional wording. |
| R-12 | NOTE | imports | Imports are sufficient (the tree builds; the probe elaborates) and change no meaning. Neither the norm on `Fin d → ℤ` (sup norm, the only Pi norm) nor the measurable structure of the integrals (fixed by `aprioriMeasure`'s type) depends on import order. Two imports are heavier than needed. `Energy.lean`'s `Mathlib.Data.ZMod.Basic` appears unnecessary, since `ZMod`'s ring and `Fintype` instances are in `ZMod.Defs` and `ZMod.val` is not used there. `Mathlib.Analysis.SpecialFunctions.Sqrt` (derivative lemmas) is used where `Mathlib.Analysis.Real.Sqrt` defines `Real.sqrt`. | Mathlib `Data/ZMod/Defs.lean` ll. 155, 172; `Data/ZMod/Basic.lean` l. 57 | None required. |

Replacement text.

R-1 (lines 25–27 of `LogPartitionMultiscale.lean`):

```
* the terms of two admissible tori of sides `ℓ, ℓ'` agree on the images of a finite set
  `A ⊂ ℤ^d` contained in the box `|y_μ| < min(ℓ, ℓ')/4`: a special case of the independence of
  the torus for polymers that do not wind around it (P4 (H.4), p. 677).
```

R-2 (line 17 of `LogPartitionMultiscale.lean`; the sentence continues onto a new line):

```
(p. 516). There is `δ > 0` such that for every `κ` and `c₉` there are `L, M, β₀` such that for
`β ≥ β₀`:
```

### Checks requested

1. **Diff against v1.0 plus §G.** Each declaration in the tree was compared with the v1.0 draft
   and the §G code after removing comments and normalizing whitespace.
   - The eight definitions are token-identical to v1.0. The only change is that `Torus` gains the
     explicit result type `: Type`, which produces the same term.
   - `logPartition_multiscale` equals §G.1 plus the single conjunct
     `1 / 2 ≤ (L : ℝ) ^ (kf + 1) * Real.sqrt ν`.
   - `lowTemperature_correlations` equals §G.2 with `∃ q : ℕ, 2 ≤ q ∧` moved to the constant block
     `∃ β₀ c c' ρ₀ ρ₁ : ℝ, ∃ q : ℕ, 2 ≤ q ∧ …` before `∀ β`.
   - No other change. The code blocks of `packet-code.md` are byte-identical to the ten tree files,
     and their sha256 sums match. The docstrings' source claims and page references were checked
     against §§A–D. Apart from R-1, R-2, R-9 and R-10 they are correct: P1 pp. 103, 104, 108, 117;
     P4 pp. 677–679; P7 p. 533; P9 pp. 493–495, 516, 518.
2. **`q` before `β`.** Provable from the method. Take `q = ML`. `L` and `M` are fixed before `β₀`
   in the source order (roadmap §4.4; P4 Thm 1 takes `M` as an input; `β` comes last). Given `β`,
   `ν`, `h`, `x`, `y`, `ε`, choose `n₀ ≥ k_f(β, ν) + 1` large enough for `ε`. Then `q^{n₀} ∣ ℓ`
   implies `ML^{k_f+1} ∣ ℓ` and `ℓ ≥ q^{n₀}`, so the RG representation applies (§B.1) and the
   limit follows from torus independence (F-2) and the decay of the terms. Placing `q` before `β`
   is stronger than the audit's placement and is supported. `q = L` suffices only when `M` is a
   power of `L` (R-7).
3. **`k_f` lower bound.** Supported. By minimality of `k_f`, `ν_{k_f} = νL^{2k_f}δ_{k_f} > (7/8)L^{−2}`
   with `δ_{k_f} < e^{c₈C}`, `C = ∑_j L^{−2γj}` (P4 (H.6), p. 679; P7 p. 529; P9 p. 515). Hence
   `L^{k_f+1}√ν > (7/8)^{1/2}e^{−c₈C/2} ≥ 1/2` once `e^{c₈C} ≤ 7/2` (`c₈` small, P4 Thm 1). The case
   `k_f = 0` (`ν > (7/8)L^{−2}`) gives `L√ν > (7/8)^{1/2}`.
   - Placement: a conjunct with the upper bound, after `∃ kf` and before `∃ T`. Correct: `k_f`
     depends on `β` and `ν` only.
   - Probes: the numeral `1 / 2` elaborates in `ℝ` (`rfl` against `(1 : ℝ) / 2`), so the bound is
     not the trivial `ℕ` value 0. The two bounds on `kf` are jointly satisfiable for every
     `ν ∈ (0, 1]`, `L ≥ 2` (proved in the probe with `Nat.find`), so they hide no contradiction.
     Together they pin `kf` to at most two adjacent values.
4. **Docstrings and packets.** Findings R-1 to R-11. Two packet claims were verified directly.
   - The binder counts are correct as stated: Root-F has 18 rows (10 SOURCE, 1 TYPING, 1 PROPOSED,
     6 SOURCE/PROPOSED) and Root-C 12 rows (6, 1, 1, 4).
   - The repository revision `49825b5` is the current `HEAD`.
   - "Eight definitions, two roots, ten files" is correct.
   - The changelog in `packet-head.md` matches the findings of this audit and their dispositions.
5. **Imports.** Sufficient and not misleading (R-12).
