# Questions for Roland, batch 2 (2026-10-12)

**13. The switch at k₀ between ν-free and complete backgrounds.**

Balaban's flow computes the background φ_k without the field term while β_k ν_k ≤ 1 ("ν-free",
k < k₀), and with it from k₀ on ("complete"). P6 p. 11 describes this two-stage scheme and says the
contributions of the change are "very small".

We cannot make that quantitative on the analyticity domain in the external field that the inductive
class needs.

**The calculation.** Take one block of the hard-spin action, A_m(e,φ) = (a/2)|e − φ|² + (m/2)|φ − h|²
with |φ| = 1, where m = ν_k L^{2k} is the dimensionless mass and b = m h. The class must be analytic
in b on a neighbourhood that contains transverse components of size of order ε_j or ε_j². Put
b = m e + q e₂ with q = σ ε_j² fixed.

- The ν-free background is φ⁰ = e.
- The complete background is φ^m = ((a+m)e + q e₂)/R, with R = √((a+m)² + q²).
- The switch changes the action by β(R − (a+m)) = βq²/(R + a + m) ≥ c β q².
- At the switch step βm = θ ∈ (1, L^d) is fixed while β → ∞. So this cost is unbounded, while the
  proposed bound is O(1) per block.
- A one-block cutoff fluctuation integral shows the same growth: its log is ≥ c q √β.

So no per-block bound uniform in β holds on that domain. The cancellation must come from somewhere
else, or the domain must be smaller.

**Which reading did Balaban intend?**

(a) **Smaller domain in h.** At and near k₀, analyticity in the transverse part of h holds only in a
mass-dependent disc of width about √m·ε_j. h is a parameter (the observables use the source g), so
this might be harmless. But the irrelevance estimate (I-6) then has to be proved for that restricted
class.

(b) **Resummation.** The transverse-source free energy of order βq² is kept explicitly in the
reference action or density across the switch, and is not expanded as a small correction. If so,
where does it enter the RG equations?

(c) **One convention throughout.** Use the complete background from the start, and keep ν-free
backgrounds only for the ν ↓ 0 continuity. Is there an obstruction we are missing?

(d) **Another device.** If you or Brydges–Slade handle a field term that switches from perturbative
to dominant (mass-dependent norms, an observable field, ...), we would gladly copy that approach.

Details, with the exact one-block counterexamples: `notes/phase1/RGFREE-6.md` §§2–4 and
`RGFREE-3.md` §2.1.

**13 (addendum, 2026-10-13). The transverse-source quadratic term.**

We can now say exactly which term causes the trouble, and it is not only at the switch.

Write b = ν_k h for the source and b⊥ for its part transverse to the spin. Take one block with penalty
(a/2)|ψ − φ|² and field term (m/2)|φ − h|², m = ν_k.

- **At the switch.** Changing the background from field-free to complete lowers the action by
  β(√((a+m)² + |b⊥|²) − (a+m)) = β|b⊥|²/(2(a+m)) + …  (exact one-block formula).
- **At every field-free step (k ≤ k₀).** Treating the field term as a perturbation, the Gaussian
  fluctuation integral of exp(β b·δφ) with covariance 1/(βa) gives the same structure,
  β|b⊥|²/(2a), at second order.

On the physical field this is small: |b⊥| = m sin θ, so the term is β m² sin²θ/(2a) ≤ m sin²θ when
βm ≤ 1. But as a function of the source it has coefficient β/(2a), with second transverse derivative
β/(a+m) at the aligned point. An inductive bound E₀ on the term therefore holds only for
|b⊥| ≲ β^{-1/2}, and Cauchy estimates on that domain do not give the irrelevance estimate (I-6) with
the rate we need. It survives all four renormalization conditions, because it vanishes with its
first derivatives on aligned configurations and has no spatial extent.

P1 (3.13) has the domain condition |ν_j(1 − (ψ_j)₀·h)| < σ²ε², which gives |b⊥| ≲ ε√ν_j: on that
domain the term is bounded by ε². P4 (5.1) writes the potential as f(U, V, W²), with W² the
transverse source variable.

**Question.** How does Balaban's induction treat the W²-dependence of the potential?

(i) Is ∂f/∂W² (the coefficient of |b⊥|²) a tracked quantity with its own recursion, like the
    mass and wave-function terms?
(ii) Or is it only bounded on the P1 (3.13) domain (transverse radius ε√ν), with irrelevance in
    d = 3 coming from the scaling L^{d−4} of that coefficient?
(iii) Or is there a cancellation we are missing?

Our current irrelevance proof uses a source polydisc with transverse radius ε_j independent of the
mass (from P3 (4.26)), which is too wide for this term when ν_j ≪ 1.

Details: `notes/phase1/PIN-I6.md` §2 and `notes/phase1/PIN-JET.md` §§2–3.

**13 (second addendum, 2026-10-13). What we now believe, and the sharpened question.**

We checked P1, P3, P4, P5 and P6 for how the W²-dependence is handled (`notes/phase1/W2-TERM.md`):

- P1 does not give ∂f/∂W² its own recursion. P1 (3.29)–(3.33) bounds it by Cauchy's theorem on a
  complex source disc of radius ≈ ε_j in b⊥ (independent of ν_j and β_j) and puts f_{0,0,1}·ν²w² in
  the Taylor remainder. P4 (5.1)–(5.26) studies f(u, v, 0) only.
- That Cauchy bound needs the inductive bound E₀ on the wide disc. A coefficient β_j/(2a) of |b⊥|²
  does not satisfy it when β_j ε_j² is large.
- In P1/P4 the backgrounds are complete (they include the field), so this classical term sits inside
  the main action β_k A_k(ψ, φ_k(ψ, h)), which is kept exactly, and the fluctuation integral has no
  linear source term. No problem arises there.
- The problem appears only with P5's convention for β_kν_k ≤ 1: the background ignores h, the field
  term is a perturbation, and its second-order Gaussian contribution β|b⊥|²/(2a) has to land in the
  local terms ℰ, at every step k ≤ k₀ and again at the switch.

P5 p. 490 says the ℰ^{(j)} "still satisfy the induction hypotheses" of P4 in that regime.

**Sharpened question.** In the regime β_kν_k ≤ 1, which is intended?

(A) The small-field terms ℰ^{(j)} are still those of P4, built with complete backgrounds; the
    field-free background is used only in the large-field operators (P5–P7). If so, where is the
    difference between the two backgrounds accounted for inside the small-field region?
(B) The ℰ^{(j)} are rebuilt with field-free backgrounds, and the transverse-source free energy is
    controlled by something we have not found (a cancellation, a narrower complex domain in h, or
    an extra tracked term).
(C) Either reading works because only real unit h matters in the end, and the complex-h bounds of
    (H.5) are needed in a weaker form than printed.

Our fallback, if there is no answer in the papers: complete backgrounds at all scales for the
small-field class (as in P1/P4), and a separate treatment of the large-field operators for
k ≤ k₀ with the tiny mass β_kν_k ≤ 1.

**Third addendum to 13 (our present reading of P5–P7, and the one point we need confirmed;
details: `notes/phase1/Q13-HYBRID.md`).**

We now read P5–P7 as follows for the scales j ≤ k₀ inside the large-field operators: the variational
backgrounds and the sharp characteristic functions are massless, the reference configuration of the
R operation (P7 Lemma 2.1) is massless, and the physical external-field term stays in the main
action; this is consistent with the ν-term in P7 (2.58).

For the small-field class we need complete backgrounds (mass ν_j L^{-2j} in the variational problem)
at every scale, as in P1/P4; with massless backgrounds each step produces the transverse source term
of the first addendum.

So the two conventions meet where a small-field region becomes part of a new large-field region.
We are trying the following: keep the massless characteristic functions and the massless reference
of R exactly as in P5–P7, but evaluate the main action of the new region, and the inherited
small-field terms, at the complete background. The massless characteristic functions are invariant
under rotations with h fixed; the complete background differs from the massless one by O(ν_j) on a
common real domain, which is much smaller than the tolerance δ_j.

**Question.** In P5–P7, when a region turns large below k₀, at which background are the main action
of that region and the inherited terms E, F of the old small-field region evaluated, and are the
inherited terms carried into the large-field expression unchanged (with the correction of P5 (1.8)
on the new region), or re-expressed?

**14. P6 p. 34: the size transfer for boundary terms across a new long hole.**

P6 p. 34, after (4.32), says the estimates P3 (4.48)–(4.49) continue to hold with the sizes replaced
by the modular ones d_k(X mod Ω_k^c), d_{k+1}(Y mod Ω_{k+1}^c), with the output Y ⊃ X. In P3 (4.48)
the new size is bounded by L⁻¹·(old size) + d(2L+1)^d·|𝒞|, where 𝒞 is the set of derivative cubes.

We think this cannot hold as printed, by the following example (details: `notes/phase1/VMOD-16.md`,
`GRAPH-GM-3.md`).

- Take a second step in which the new large-field set 𝖯 is a straight path of T cubes of π_{k+1}
  (allowed by P5 (2.6)). P5 (2.8) removes its 3-neighbourhood, so Ω_{k+1}^c has a new component
  F_T that is 7 cells wide and T + 7 cells long.
- Take an old boundary term X ∈ 𝒟_k(mod Ω_k^c) of fixed size that touches one end of F_T.
- By P5 (1.33) the output Y must contain all of F_T, and by P1 (2.26) Y must be a union of blocks of
  π'_{k+1}, which are L ≥ 8 cells wide. A block containing a point of F_T therefore sticks out into
  Ω_{k+1}. So Y ∩ Ω_{k+1} contains blocks all along the hole, and by P5 (1.34) the tree must meet
  each of them: d_{k+1}(Y mod Ω_{k+1}^c) ≥ T − const, with no derivative cubes (𝒞 = ∅).

The printed transfer has no term that grows with T.

**Question.** Is the intended estimate the one with an extra term proportional to the number of new
large-field cubes that Y contains, paid by the large-field factor of the new region (the exponent
p(β_k)-type smallness per new cube)? That is the repair we plan to use. Or is there a restriction on
𝖯, or on which boundary terms X occur next to a new hole, that we have missed?

**Addendum to 14 (after working out the proposed repair; details: `notes/phase1/VMOD-17.md`).**

The repair named in the question does not go through as stated, for two reasons.

(a) The positive part of the large-field exponent counts the new seed cubes of the step only:
κ^{(k)}(Z′) = a_k·N(Z′) − b_k·O(Z′) with N(Z′) the number of cubes of 𝖯 ∪ 𝖰 ∪ 𝖱 ∪ 𝖲 in Z′
(P6 (3.9)–(3.11)). But Ω_{k+1}^c also grows around the old region with no new seed: if
𝖯 = 𝖰 = 𝖱 = 𝖲 = ∅ at step k+1 and Z_k ≠ ∅, the neighbourhood of Z_k removed by P5 (2.8) at the
new scale contains cells outside the old hole, while N = 0. A collar made of such cells has
nothing to be charged to.

(b) P5 (H7) and the boundary clause of P6 ask for a bound on each boundary coefficient B(Y) by
itself. The large-field factor belongs to the operator of the region, not to a single coefficient,
so using it would need a joint norm for the pair (operator, boundary term), that is, a different
inductive hypothesis.

**Question (revised; details: `notes/phase1/VMOD-18.md`).** We examined three readings.

(i) A hole is taken together with its one-block collar, and the collar is not charged in the modular
    size. This removes the long thin hole example, but the counting estimates that use the size fail.
    Take two parallel long thin holes F₁, F₂ of length T at a fixed distance, and for each position t
    along them a bridge of blocks joining the two collars; put Y_t = F₁⁺ ∪ F₂⁺ ∪ (bridge at t).
    All Y_t contain one fixed cube A, all have size bounded independently of t and T, and there are
    about T/(2L) of them. So the sum over Y ∋ A of e^{−λ·size(Y)} is not bounded uniformly in T.
    Also |Y ∩ Ω| is of order T while the size is O(1), so the volume factor on p. 34 is not absorbed.
(ii) A boundary term that touches a new hole stays in the integrand of the new large-field operation.
    But one term X can touch several disconnected components of the new region, which breaks the
    product over components.
(iii) The localization is an expansion in the set S of active cells actually visited (the old source,
    the derivative cells, and the adjacent holes completed), not in a union of overlapping cubes, and
    the labels (source, derivative cells) are kept while counting. For this support we can prove
    D(S) ≤ d_k(X)/L + dL·|𝒞| under a rooted patch geometry.

Is (iii) what was intended? Two assertions needed for it are not in the printed argument: that the
two boundary operators of P6 have a common domain of analyticity and locality on such supports (the
analogue of (H7)), and that the labels can be summed uniformly at fixed support.

### Item 14, second addendum (2026-10-12): old boundary terms in a new hole

P6 (4.32)–(4.34), p. 34. P5 (1.38)–(1.39) gives an old boundary term B^(k)(X, A_k); P5 (2.47)–(2.48)
leaves its A_k spins in X ∩ Ω_{k+1}^c as arguments, integrates the outer ultra-local Gaussian on
Ω_{k+1} \ Ω''_{k+1}, and takes the main fluctuation expectation on Ω''_{k+1}. P6 (4.32) substitutes
ψ^(k)_loc(θ) + β_k^{-1/2} C_loc^(k)1/2 ψ on B(3k+1) = Ω_{k+1}^(k).

When Proposition 4.3 of P3 is applied to this term, are the localization parameters of cover cubes
lying wholly in Ω_{k+1}^c absent from that composite after the prescribed local extension, or can
the old/boundary Green function and background on W_k depend on them?

(a) If they are absent: what cutoff radius, and what bound on the number of cover cubes meeting a
    given cell, reduce the roots of the expansion to X ∩ Ω_{k+1}?
(b) If they are present: which estimate pays for them? At fixed old size d_k(X mod Ω_k^c) the
    cover constructed in the proof can have of order L^{k(d-2)} cubes of the lowest layer touching
    the hole side of the cover of X (a flat old wall), and P6 (3.9) charges the new seed sets
    P, Q, R, S, while (4.34) is a bound on each coefficient before that weight is attached.

What we can prove: the spins of A_k in the hole do not depend on the parameters; the count of
connected families of cover cubes rooted at the ACTIVE cells of X is uniform (degree 3(L+2)^d,
at most 3^d (L^{m_0})^d cubes at an active cell); the sum over families at a fixed support then has
the rate 2κ − 1 of (4.34). What is missing is exactly the statement that a family not rooted at an
active cell contributes nothing, or is paid for.
