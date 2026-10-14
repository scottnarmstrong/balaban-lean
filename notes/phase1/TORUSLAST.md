# TORUSLAST — Root-F torus clause at the last scales (blocker 7, W796)

**PROVED (reading; no Lean).** Sources: `Balaban/Frozen/Roots/LogPartitionMultiscale.lean` (statement), `Frozen/Geometry/IsPolymer.lean`, `docs/BLOCKERS.md` §7, `TORUSCOH2.md` T6, LEDGER rows W678, W791. Notation: s_j = M L^j, q = min(ℓ,ℓ')/s_{kf+1} (an integer), Q_ℓ = polymers that are the image of some A inside the box |y_μ| < ℓ/4.

## 1. The clause is a constraint only on Q (what it does and does not say)

**PROVED.** The family T is chosen after kf and before ℓ, and the clause compares T ℓ and T ℓ' only on supports A inside the box of the smaller torus. Hence (taking ℓ' → ∞) T^ℓ_j(x,X;g) for X in Q_ℓ must equal one function T^∞_j(x,X;g) of X, g|_X, the same for every ℓ with X in Q_ℓ. Every other polymer X ∉ Q_ℓ is unconstrained (it may depend on ℓ). Support, locality, analyticity and the bound are the only other requirements; they are per-term.

**PROVED (refute-first, first order in g).** The identity forces ⟨σ_x⟩_ℓ − h = Σ_j Σ_{X∋x} T^ℓ_j(x,X;0). The left side is a genuine function of ℓ (finite-size effect, size e^{-ℓ/ξ}, ξ ≈ L^{kf+1}), not exactly constant. So no ℓ-independent family of ALL terms exists; the ℓ-dependence must sit in polymers X ∉ Q_ℓ (the wrapping ones). This is the only way the clause can hold, and it is a restriction on the choice of T, not a contradiction.

## 2. Construction that makes the clause exactly true (question 1)

**OPEN (mathematically consistent; needs one estimate not in the repo).** Let T^old,ℓ be any family satisfying Root-F without the torus clause (the existing construction). Put
- T^new,ℓ_j(x,X;g) = T^∞_j(x,X;g) := lim_{ℓ→∞} T^old,ℓ_j(x,X;g) for X ∈ Q_ℓ;
- for X ∉ Q_ℓ: T^new = T^old + (absorbed remainders): for each X ∈ Q_ℓ containing x, the difference ΔT(x,X;g) = T^old,ℓ(x,X;g) − T^∞(x,X;g) is added to T^new,ℓ(x,X';g) where X' = X ∪ (a fixed chain of scale-j blocks from X to outside the quarter box).

Checks: (a) the identity is unchanged (the sum of all T is the same); (b) support: X' is a scale-j polymer containing x; (c) locality: ΔT depends on g|_X ⊂ g|_X'; (d) analyticity: limits and differences of analytic bounded terms; (e) the clause: pair (ℓ,ℓ') triggers only for X in the smaller quarter box, where both sides equal T^∞; X' ∉ Q_ℓ never triggers it; (f) no "fixed formula uniform in ℓ" is needed (W678's remark is sufficient, not necessary). Absorbed remainders may be assigned to the same scale j, so no cross-scale transfer.

**Input required (not in repo).** (I1) the limit exists, i.e. T^old,ℓ(X) is Cauchy in ℓ; (I2) a quantitative bound ‖ΔT(x,X;g)‖ ≤ c9 L^{-j(...)} e^{-κ_1 |X|/s_j^d} · e^{-κ_2 q_j}-type with the second factor beating the number of preimages (≤ 2^{blocks(X')}) and the chain length (≤ q_j blocks). The mechanism available is propagator decay, e^{-c M · (distance in blocks)} (mass √ν ≈ L^{-(kf+1)}), and M is chosen after L and κ (ROOTBOUND.md), so the decay rate in M can be made to beat κ and any constant of the form e^{κ C L}.

**REFUTED (as an automatic consequence of the landed lemmas).** The landed two-torus lemmas (W666, W678, W791) give only exact equality for non-wrapping read regions and no smallness of the difference when the read region wraps. For finite-range objects (cut components, determinant activities on Y(C)) a wrapping read region gives a different object, not an exponentially small perturbation; (I2) would then need the papers' own exponential decay of the dependence on distant data, which is not formalized.

## 3. Vacuity count (question 2)

**PROVED (arithmetic).** Blocks of side s tile the y-axis at multiples of s on both signs (s | ℓ, ℓ'), so Q_ℓ, Q_ℓ' use the same block grid. A polymer in the box must be a union of whole blocks. Along one axis the blocks with y-range inside (−m/4, m/4), m = min(ℓ,ℓ'), number N = ⌊q/4⌋ + ⌈q/4⌉ − 1 (s ≥ 4), at j = kf+1: q = 1,2,3 give 0; q = 4 gives 1; 5,6,7 give 2; 8 gives 3. So:
- **q ≤ 3: the clause is vacuous at j = kf+1** (no nonempty union of blocks fits); min(ℓ,ℓ') ∈ {s, 2s, 3s}.
- q = 4: the only support is the single block [0,s)^d (one polymer, a ∈ that block). For q ≥ 5: connected unions of blocks in an N^d grid, i.e. lattice animals with at least N^d... positions; non-vacuous.
- For j ≤ kf: the box has q·L^{kf+1−j} blocks of side s_j per axis, so with L ≥ 4 the clause is non-vacuous for every admissible torus.

**PROVED (the gap).** The landed transport needs 4R + C L s_j < min(ℓ,ℓ') (R = read radius; C = 19 L^{m₀+m₁+...} in W678). For j = kf+1 and 4 ≤ q ≲ C L, and for scale j whenever q L^{kf+1−j} ≲ C L, the clause is non-vacuous AND not covered by the transport. T does not vanish on these supports in general (the first-order identity of §1 needs the terms of wrapping size ≈ e^{-q M c}). So neither vacuity nor vanishing removes the problem for 4 ≤ q ≲ CL.

## 4. Verdict

(1) Yes, in principle: the clause is consistent with Root-F's other clauses if the torus-dependent, exponentially small remainder is moved onto the wrapping polymers X' ∉ Q_ℓ of the same scale (§2); this needs (I1)–(I2), i.e. an exponential-in-M closeness of the term on two tori, which the repo does not have and which fails automatically for exactly finite-range reads. (2) The clause is vacuous only at j = kf+1 with min(ℓ,ℓ') < 4·M L^{kf+1}; elsewhere it is not vacuous. 

## 5. Refined version of Roland item 24 (text-ready)

"For the terms T_j(x,X) of Root-F on a torus of side ℓ = q·M L^{k_f+1} with q small (4 ≤ q ≤ C L), the localized term for a polymer X near the origin is built from objects whose read region wraps around the torus, so two tori ℓ, ℓ' give different values. Do the papers (P4 (H.4), p. 677) intend exact independence of the torus for all non-winding X (the polymer does not wind, but the construction region does), or only agreement up to a term of size e^{-c M q} that is then collected into the winding polymers? If the latter, is the collection into polymers of the same scale j containing X (with the bound e^{-κ|X'|/s_j^d}) what the construction does? If exact, which fixed formula (infinite-volume operator, or a fixed box of side independent of ℓ) defines T_j for such X, and where does the difference go in the identity log Z(g)/Z(0) = ⟨g,h⟩ + Σ T? Finally, may the statement of Root-F carry min(ℓ,ℓ') ≥ 4·(C L + 1) M L^{k_f+1} as a standing condition in the clause?"
