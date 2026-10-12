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
