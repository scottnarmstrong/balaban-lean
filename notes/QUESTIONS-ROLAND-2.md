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
