# Mathematical blockers

This page lists the places where the formalization cannot proceed from the papers as written. In
each case either a step is asserted without a proof that we can reconstruct, or the argument
written does not give the estimate that the next step needs. Page and equation numbers refer to
the papers in [PAPERS.md](PAPERS.md).

A blocker here is not a claim that the papers are wrong. Often the missing step is routine for the
author and needs only an indication of the intended argument. Each item has been written up as a
precise question; the questions and their follow-ups are in `notes/QUESTIONS-ROLAND-2.md`, and the
item numbers below refer to that file.

The last section lists the problems that have been resolved since the project started.

*Last updated: 2026-10-16.*

## Summary

| # | Issue | Where | Blocks | Status |
|---|---|---|---|---|
| 1 | Base case of the large-field induction; the case of no renormalization step | P5 (H.1), (1.1); P7 §4 | Root-F for large external field ν; start of the large-field induction | open; the Yang–Mills first step suggests a route for the base case (item 17 addendum); the case of no step remains |
| 2 | Switching from ν-free to complete backgrounds | P6 p. 11; P2 (1.11); P5 (1.4), (1.19) | small-field terms entering the large-field step | open; a route modelled on the Yang–Mills papers (source-free tests, source in the weight, direction tests extended over the collar) is designed; the estimate on the shrinking source radius and a constant check remain (item 13 addendum) |
| 3 | Old boundary terms across a new long hole | P6 p. 34; P5 (1.34); P3 (4.48) | localization for general classes; large-field boundary terms | open, with the author; the completion spill is confirmed for P5's openings; routes compared (item 14, fifth addendum) |
| 4 | The gas of removed components and retained holes | P7 (3.26)–(3.28) | the large-field polymer gas | possible resolution (clusters on the core), formalized up to the physical inputs of the large-field step; author confirmation asked (item 16 addendum) |
| 5 | The cut family for the last integral | P7 §4; P4 (6.4)–(6.6) | the last integral | open; determinant and interaction localized; the amplitude follows the papers (normalization at g = 0, second-order bound, cross term with the source-free exponent); the identification with the physical density, the large-field part and the joins remain |
| 6 | Local generating sets and analyticity on their domains | P3 p. 78, (4.44)–(4.47) | the output class of each step | workaround largely built (replacement identity; analyticity, locality, bounds, rotation and paving covariance of the local terms); the assembly is being redone so that old terms keep their own level, as in the papers |
| 7 | Reading of the torus-independence clause | P4 (H.4), p. 677 | the two-torus clause of Root-F | interpretation question; the last-scale design is proved in abstract form; the scales just below the last may need a floor on the torus size (item 24) |

## 1. The base case of the large-field induction, and the case of no renormalization step

The inductive description (P5 (H.1), (1.1)) writes the density at scale k as a sum over
large-field regions. Each term carries a characteristic function that tests small-field conditions
(P5 (1.18)–(1.19)). At k = 0, with spins on the sphere, the single term with no large-field region
cannot be the whole density: the tests fail for some configurations, for example a spin far from h
or a large gradient. The papers do not say how the bare density is written in the inductive form,
or where the bound (1.31) is checked for the first large-field components.

The same question arises when no renormalization step is performed at all. This happens when
ν is large enough (ν > 7/(8L²)) that the flow stops at k_f = 0. The theorem stated here covers
every ν ∈ (0, 1], so this case is needed.

We have tried a direct one-scale treatment: a cluster expansion of the spin model on the unit
lattice. The sector where every spin is near h is done. The sector containing spins on the
opposite hemisphere is not. After its Gaussian integral is taken, the natural activity of such a
region depends on Gaussian variables arbitrarily far away, because the covariance has strictly
positive entries everywhere. It is therefore not a finite-range activity, and the polymer-gas
theorem does not apply. A one-site example shows that this is a genuine failure, not a weakness of
the estimate. What is missing is an exact decomposition of that activity into finite-range pieces
with summable norms.

In Bałaban's Yang–Mills papers (CMP 119 §1, as read in the account of [ethanwsussman/Yang--Mills-LLM-experiment](https://github.com/ethanwsussman/Yang--Mills-LLM-experiment)), the bare density is a
single term, the first step inserts the small-field tests itself, and the raw variables of a bad region
are never integrated over; the reserve for the first large-field components comes from the choice of the
level-0 threshold. If P5 follows the same pattern, the base case is settled; the case with no
renormalization step does not occur in Yang–Mills. This is asked in the item 17 addendum
(`notes/phase1/YMACCOUNT.md`).

Details: `notes/phase1/LF-BASE-KF0.md` (Part G), `notes/phase1/KF0-P7.md`. Item 17.

## 2. Switching from ν-free to complete backgrounds

Balaban's flow computes the background field without the external-field term while β_k ν_k ≤ 1,
and with it from the scale k₀ where this fails. P6 p. 11 calls the effect of the switch "very
small". The inductive class needs analyticity in the external field on a complex neighbourhood
containing transverse perturbations of size ε_j. On such a neighbourhood a one-block calculation
gives a change of the action of at least cβq² at the switch, where q is the transverse
perturbation. This is unbounded as β → ∞, while the class allows O(1) per block.

A related point: for k > k₀ the background theorem (P2 (1.11), (1.15)–(1.16)) assumes an alignment
condition on the data in the collar of the region. The large-field tests of P5 (1.19) check
direction only inside the tested cubes, while the background's data reach several cubes beyond
them.

In Bałaban's Yang–Mills papers the source stays a free complex variable at every scale and the
background is never switched, which supports the design without a switch; the same collar condition is
printed there without proof (as read in the account of [ethanwsussman/Yang--Mills-LLM-experiment](https://github.com/ethanwsussman/Yang--Mills-LLM-experiment); `notes/phase1/YMACCOUNT.md`).

A route along these lines (`notes/phase1/Q13-YM.md`): keep the large-field tests free of the external field up to the switching scale and carry the field in the weight, which preserves the symmetry the tests need; extend the direction tests of P5 (1.19) over the collar that the background reads. What remains unproved is the activity bound on the transverse source radius of order β^{-1/2}, and a check of the constant p₀ against P5 (1.30).

Details: `notes/phase1/Q13-DECISION.md`, `Q13-LATE.md`, `Q13-LATE2.md`. Item 13 and its addenda.

## 3. Old boundary terms across a new long hole

P6 p. 34 re-localizes the boundary terms inherited from earlier scales when a new large-field hole
appears. The modular size of P5 (1.34) charges the full tree length through a hole. The source tree
of P3 (4.48) visits every source cube. When a long inherited component is completed in the output
domain without a new seed, we cannot find what pays for the length connecting it to an active patch
at its far end, or why such a patch has zero coefficient. Two marked patches in the footprint of
one cover centre need not touch, so connectedness of the patches alone is not what the expansion
produces.

Since then (October 16): the completion of every hole in P5 (1.33) comes from the dependence of a
boundary term on the history of the whole retained component, not from its field dependence. The
blocker-4 reading below does not remove this blocker: the modular size still charges the length through
a hole between two attachments. The other half of the counterexample, active cells spilling along a long
face of a new hole, is real: P5 (2.3)–(2.4) build the new region from L-blocks at every offset, and we
checked in Lean that the hole is then not a union of aligned boxes. Two routes are compared in
`notes/phase1/VMOD-44.md` (plain domains, as in the Yang–Mills papers, needing an author ruling; or a
label-and-pocket format, not recommended). The question is item 14 with its fifth addendum.

Details: `notes/phase1/VMOD-34.md` to `VMOD-42.md`, `LFROOT3.md`, `LFH7PRIME.md`, `LFH7PRIME2.md`.
Item 14 (with its second to fifth addenda); `VMOD-43.md`, `VMOD-44.md`.

## 4. The gas of removed components and retained holes

In P7 pp. 527–528 a cluster of the gas consists of old boundary labels, each meeting a removed
component, linked by overlaps. Two labels may overlap only inside a retained large-field component.
By P5 (1.34) each label can have modular size of order one, while their union is as long as the
hole between their attachments. The factor of P7 (3.10) does not grow with the size of a retained
component. We do not see what pays this length in the bound for the polymer activity, or whether an
incidence restriction excludes such links.

A possible resolution (October 16): in Bałaban's Yang–Mills large-field gas (CMP 122 pp. 386–388,
as read in the account of [ethanwsussman/Yang--Mills-LLM-experiment](https://github.com/ethanwsussman/Yang--Mills-LLM-experiment)),
clusters are formed after the retained large-field components are removed, so two labels overlapping only
inside a retained component are not linked and the length through it is never paid. Read the same way,
P7 pp. 527–528 keeps the cluster identity. Its two conditions now hold in our setting: the boundary
terms read the frozen data only inside their own domains (part of the formal large-field class), and
the halo of a removed component avoids every other component (proved for the constants used). The polymer
gas with compatibility on these cores is formalized: the size through core contacts never charges a
retained hole, the counting is volume-free, the size of a core equals the modular size of the class, and
the activity bound is proved for the large-field gas up to its physical inputs (the inherited old-term
bound, the small factor of removed components, and the size of removed components), which belong to the
large-field step itself. The question to the author is item 16 with its addendum
(`notes/phase1/VMOD-43.md`).

Details: `notes/phase1/VMOD-40.md` to `VMOD-42.md`. Item 16.

A comparison with Dimock's large-field papers (`notes/phase1/LFDIMOCK.md`) found no direct substitute for the
missing payment in blockers 3 and 4. We then tested two ways around it without the author's answer, and
neither works as stated:

- *Rooting in the active region* (as in Dimock's localization). For the output labels this is false:
  an inherited boundary term with a constant coefficient, of size O(1) and allowed by (H.7), must be
  given an output domain containing the whole completed hole, of size of order n, and nothing in the
  class pays for that length (`notes/phase1/LFROOT3.md`). Whether the *physical* O(N) coefficients
  are rooted is still open.
- *A stronger inductive class*: boundary terms whose domain contains a hole carry an extra factor
  e^{−σ q}, with q the number of cells on the hole's boundary shell. This would exclude the example
  above. But the large-field small factors of P5 (1.31) and P7 (3.10) are attached to operators and
  removed components, not to these coefficients, so we cannot show that the construction produces the
  factor, or that one step preserves it with the same σ (`notes/phase1/LFH7PRIME.md`, `LFH7PRIME2.md`).

The precise question is now item 14, fourth addendum.

## 5. The cut family for the last integral

The final fluctuation integral (P7 §4, with the covariance of P4 (6.4)–(6.6)) must be localized. The
simplest complex interpolation multiplies the entries of the final operator between different cells
by parameters s(cell). For this family the spectral gap can only survive if the weighted sum of the
entries crossing a cell boundary is small compared with the gap 7/(8L²(8d+3)). Adjacent cells are at
distance one, so that sum is of order one whatever the cell size. At d = L = 3 the estimate we can
prove gives a perturbation of at least 4 against a gap of about 0.0036. The intended family is
presumably the random-walk parametrix of P3 (2.8), applied to the massive final operator. That
operator is a long-range Schur complement, however, and we find no formula for the family, or for
its defect and radius of analyticity, in P7 pp. 529–531 or P4 pp. 719–720.

A proposed macroblock parametrix has now been constructed for the reference operator in Lean.
It has an analytic resolvent family and an analytic Stieltjes family whose uncut value is the
inverse square root. The weighted column estimates can retain the full row decay rate and the
same constants: summing the existing pointwise commutator bound in the other order proves the
column contraction directly. No right parametrix or symmetry of the tagged family is needed.
This strengthens the reference estimates, but does not close this blocker. The physical matrix
and action must still be connected to the family with the required analytic domain, physical
locality, determinant expansion, and nonwinding torus comparison. The current abstract
coefficient expansion does not by itself prove geometric connectedness of polymer supports.

Since then the localization of the last integral has been rebuilt on a different footing
(`notes/phase1/FINALPHYS2.md`, `FINALPHYS3.md`). The square-root family turned out not to be invertible on
the parameter cube, but it is not needed: the Gaussian change of variables is made once at the physical
point, and only the ratio det(U + E)/det(U) has to be localized. That ratio is now proved to be a product
of local factors, each zero on disconnected supports and bounded uniformly in the volume, using the
defect operator 1 − K(s), which is invertible on the whole parameter polydisc. The interaction, with its
cutoff kept on the real field, is analytic on the same polydisc with local, bounded coefficients. What
remains: a comparison of constants (the analyticity domain of the last-scale interaction against the
radius the cut family needs), the large-field part, and the joins to the physical flow.

Details: `notes/phase1/FINALFAM.md`, `FINALCUT.md`, `FINALFAM2.md`,
[`FINAL-COLUMNS.md`](../notes/phase1/FINAL-COLUMNS.md). Item 18.

The papers' last step was re-read for the size of the final term: they integrate at the constant
saddle, so the Hessian does not depend on the source g, and the identity is normalized at g = 0. The
smallness comes from the g-derivative of the inherited term (P4 Prop. 2.2), of size β^{-1} rather than
β^{-2}. The estimates this needs are now proved in a general form: the part of the interaction that is
linear in the fluctuation averages to zero against the symmetric cutoff Gaussian, the remainder is of
second order, and the cross term of the linear part with the source-free exponent is controlled by a
third-order bound on its odd part. What remains is to identify these pieces with the physical density
of the last step, and the large-field part.

## 6. Local generating sets and analyticity on their domains

After the localization expansion, each new term is indexed by a domain Y. P3 p. 78 replaces the
generating set of the step by the minimal generating set 𝔹(Y) built around Y with 5L layers of
cubes. It then states analyticity and bounds of the term on the domain of 𝔹(Y) ((4.46)–(4.47)) by
recomputing the term with 𝔹(Y). The formalized localization estimates use a much larger separation
between layers, and they cannot be applied at separation 5L·M₁ when d ≥ 3. The papers' margin comes
from the relation between the two cube sizes (roughly M ≥ 6M₁); at the block size L = 3 with one
level of cover this relation fails.

This affects the *output class* of each step, not the values of its terms. The terms themselves
are proved analytic and exactly local on the standard domain.

Work around it (decided: a separate local class at a lower separation index, with the existing
class structures). Proved so far: the local generating set's geometry and paving covariance; local
chart data by restricting the fields to the local sites and recomputing the background (P3 (4.44));
a radius bookkeeping that uses the same radius sequence as the papers (the papers never put the
ambient chart inside a local one); the zero local class with local generators; and the exact
localization of inherited terms at a local ambient generator (P3 (4.16), (4.9)).

Two obstacles were found in the formal machinery, not in the papers. The first is resolved: chart
composition now loses nothing (constant 1, as in P3 Lemma 4.1 (4.29)), and the corrected chart test
holds with the radius sequence of the class (at d = L = 3 for γ ≤ 1/4). For the second, the background
engine required a separation index larger than that of the local generating set; the sharper distance
estimate of the papers (r₁ = 1 at separation 5L·M₁) is now proved for the local generating set, and
the engine has been rerun in a form that accepts it (`notes/phase1/WIDEGEN.md`, route A).

Recomputing a term with the local generating set gives the same coefficients as the term of the
step: this replacement identity is now proved for any two generating sets on one torus, under
hypotheses on the component of the polymer (cube operators, the decoupled fields and the
compositions agree on it). The local covariance, its square root and the local fluctuation variable
are proved analytic and bounded on the local domain. The identity is also proved at the local
generating set itself, provided the polymer's read region stays two cubes away from the edge of the
local set, and the local and ambient fluctuation variables agree there. The papers build the local set
on the expansion domain itself; the formal operators read two cubes further, so the local set is
built on a collar of that domain, which changes neither the index of a term nor its bound. The
identity is proved in this form, with the local fluctuation variable. Remaining: the clauses of the
local class for nonzero terms (bounds, covariance, the fluctuation integral of a local term).

Since then (October 16) most clauses of the local class are proved for nonzero terms: the
fluctuation integral of a local term, analyticity on the local domain, exact dependence on the fields of
the term's own domain, the bound summed over the old polymers, and covariance under real rotations. A
term must be defined for all fields; outside the domain it is extended by choosing a point of the domain
with the same values on its support (a fixed outside value fails, because the domain constrains the
fields beyond the support). Remaining: covariance under lattice symmetries (the extension must be chosen
covariantly — now done by averaging over the paving group, with covariance of the local terms on the domain
proved), the clause for the full lattice symmetry group (which moves supports off the paving), complex
rotations, and the assembly of the next level. The source terms (the M-part) now
have analyticity, locality, the summed bound and covariance under real rotations as well.

A review of the assembly against the papers (October 16, `notes/phase1/LOCALCLASS-REVIEW.md`) found
that we had filed whole old terms at the new level. In the papers (P4 Theorem 2 and (4.17)–(4.22)) an
old term keeps its level, its domain, its generating set and its bound; only the new contributions
created by the fluctuation integral and the renormalization go to the new level, and those are the terms
whose analyticity requires the local generating sets. The general results above carry over; the
assembly is being redone in this form. We also restrict the rotation symmetry of the class to real
rotations, as the papers state it, and label the new terms by centres for the full lattice symmetry.

Details: `notes/phase1/GENL.md`, `WIDEGEN.md`, `SHARPX0.md`, `LOCALENGINE.md`, `SF3TYPE.md`.
Item 23.

## 7. Reading of the torus-independence clause

The main theorem says that the terms on two tori agree on supports A in the box |y_μ| < min(ℓ, ℓ')/4
(P4 (H.4), p. 677). A localized term T_j(A) is built from a neighbourhood of A of order M L^j. The
transport lemmas proved so far need that neighbourhood to lie in a common non-winding box. The
question is whether the papers' construction removes every read outside A, so that the clause
holds for every such A, or whether the clause should carry a margin.

What is now proved (for the step with no inherited terms): every ingredient of a coefficient —
background and fluctuation solutions on a cut component, covariance and square root, determinant
activities, marked energy terms and the observable term — is the same on two tori whenever its
whole read region lies in one common non-winding box. The read region is the polymer itself plus
the root cell and a fixed number of cubes of size of order L·M·L^j around it; the condition proved
is 4R + C·L·M·L^j < min(ℓ, ℓ') for a read region of radius R. This is the quarter-box condition of
the theorem up to that additive slack (and a non-sharp factor in R). It covers all scales at which
M·L^j is small compared with the torus side; it does not cover the last few scales, where the
slack is comparable to ℓ. Whether the construction reads outside the polymer at those scales is
exactly the question above.

A second requirement appeared: agreement of the final terms needs them to be given by the same
formula on every torus (not by separate choices on each torus); the assembly of Root-F has to
respect this.

At the last integral a further point appears. The localized pieces of the last integral (the
determinant ratio and the interaction) are equal on two tori when the final operators and reference
Gaussians agree on the read region (proved). The final operator's inverse, however, has entries that
decay but never vanish, so on two tori of different size these quantities differ by exponentially
small winding terms; exact equality of the last-scale terms is not available from this construction
alone.

A design for the last scale (October 16, `notes/phase1/TORUSLAST2.md`): define the last-scale terms
from one canonical torus chosen by the support, and move the difference on any other torus onto polymers
that reach outside the quarter box; the uniform closeness of the final operators on two tori pays for this
at distance of a few cells from the box edge (proved, together with the chains and an abstract assembly
that keeps the identity and makes the terms exactly equal on two tori; since Root-F's tori are unbounded,
the common value is the limit over growing tori, which the closeness makes convergent; the closeness is
now uniform in the size of the support, after replacing the crude bound of the tags by one that grows
only with distance). Truncating the walk expansion of the final operator to the
region, as in the Yang–Mills account, does not work here: the final operator is a Schur complement and the
truncation changes it by order one near the boundary. Root-F as stated carries no lower bound on the
torus size; for the scales just below the last one, the margin our locality results need grows with L, so
either those terms are shown to be torus-local with a margin independent of L, or the statement needs a
floor on the torus size. This is part of item 24.

Details: `notes/phase1/TORUSCOH2.md` T6. Item 24.

## Large pieces of work that are not blockers

These have no known mathematical gap, but they are substantial and not yet done.

- **The first step from the unit lattice** (P4 (2.42)–(2.54)). It is a different integral from the
  later steps: it uses hemisphere chart variables, its own covariance and a Jacobian. The two
  exact starting identities are proved. See `notes/phase1/BASESTEP.md`.
- **Space-dependent external field in the step.** The step theorems are proved for data whose
  external-field component is the constant unit vector h. The inductive class asks for analyticity
  in space-dependent complex perturbations of h. See `notes/phase1/OFFFIBRE.md`, `OFFFIBRE2.md`.
- **The step for a general class member.** The step theorems are proved for an input with no
  inherited terms. The general step and the small-field induction are partly built. See
  `notes/phase1/GENCLASS.md`.
- **Independence of the torus.** The geometry and the data transport are proved, the cube
  operators correspond, and the decoupled background and fluctuation solutions on a cut component
  are the same on two tori. Still to do: the covariance and its square root on a component, and
  the comparison of every coefficient. See `notes/phase1/TORUSCOH2.md`, `TORUSCOH3.md`.
- **General d, L, N.** The step is proved for general d ≥ 3, L, N, with the fixed d = L = 3, N = 2
  results as corollaries. An arbitrary unit external field h is reduced to a coordinate vector by a
  rotation; this needs the source radius √N along the chain, which is about 13 files of
  generalization with no known obstruction. See `notes/phase1/STOWERG2.md`, `UNITH.md`.
- **The logarithm and the assembly of the terms T_j.** See `notes/phase1/ROOTASM.md`,
  `OBSBUDGET.md`.

## Resolved

- **Exact locality of the new terms on their domains** (P3 (4.44)–(4.47); item 21). For the step
  with no inherited terms, every summand of the expansion (bulk interaction, inherited energy and
  observable terms, source terms, mass terms) depends only on the data on its own domain. The
  coefficient families of the step inherit this. Proved in Lean.
- **Arbitrary decay rate.** The main theorem fixes the decay rate κ before the block size. The
  constants of a step are now produced for any required output rate, by making one entropy
  constant adjustable.
- **The smallest admissible torus.** It is excluded by a non-winding hypothesis of the operator
  estimates. It can be avoided by taking L ≥ 6 or a larger cover index, so it is not a
  mathematical obstruction.
- **Choice of the decoupled solution.** The coefficients use an analytic solution of a fixed-point
  problem that is unique only on the valid domain. Naming one global solution is not needed: its
  defining properties, together with uniqueness on the valid domain, suffice wherever it is used.
