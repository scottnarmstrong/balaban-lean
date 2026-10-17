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

*Last updated: 2026-10-17.*

## Summary

| # | Issue | Where | Blocks | Status |
|---|---|---|---|---|
| 1 | Base case of the large-field induction; the case of no renormalization step | P5 (H.1), (1.1); P7 §4 | Root-F for large external field ν; start of the large-field induction | open; the Yang–Mills first step suggests a route for the base case (item 17 addendum); the case of no step remains |
| 2 | Switching from ν-free to complete backgrounds | P6 p. 11; P2 (1.11); P5 (1.4), (1.19) | small-field terms entering the large-field step | open; a route modelled on the Yang–Mills papers (source-free tests, source in the weight, direction tests extended over the collar) is designed; the estimate on the shrinking source radius remains (item 13 addendum) |
| 3 | Old boundary terms across a new long hole | P6 p. 34; P5 (1.34); P3 (4.48) | localization for general classes; large-field boundary terms | open, with the author; the completion spill is confirmed for P5's openings; routes compared (item 14, fifth addendum) |
| 4 | The gas of removed components and retained holes | P7 (3.26)–(3.28) | the large-field polymer gas | possible resolution (clusters on the core), formalized down to one physical input, the small factor of removed components (P7 (3.10)), which the large-field step still has to produce (its derivation from the window integral of the removed outcome is proved, and the removed kernel is defined; the window integral is reduced to two named inputs, a uniform quotient bound and the quietness of the ancestors, and the vacuum energy bound); author confirmation asked (item 16 addendum) |
| 5 | The cut family for the last integral | P7 §4; P4 (6.4)–(6.6) | the last integral | open; determinant and interaction localized; the amplitude follows the papers (normalization at g = 0, second-order bound, cross term with the source-free exponent); the last-scale interaction identified with the class's energy terms (radius ε_{k_f}; comparison, N components, the domain inclusion and volume-uniform coefficient bounds proved); the identification with the physical density, the large-field part (route from P7 §4 built; the coupling across a large set asked, item 18 addendum) and the joins remain |
| 6 | Local generating sets and analyticity on their domains | P3 p. 78, (4.44)–(4.47) | the output class of each step | workaround largely built (replacement identity; analyticity, locality, bounds, rotation and paving covariance of the local terms); the assembly is being redone so that old terms keep their own level, as in the papers; rotations are real, and the complex rotations used by the renormalization step follow by continuation (proved); restating the chain on this is planned; old terms keep their birth domain, with the mass response proved; the new density's value for a class with inherited labels is reduced to the irrelevant-part representation of the inherited terms (P1 Prop. 3.10), proved on ℤ^d, torus form in progress |
| 7 | Reading of the torus-independence clause | P4 (H.4), p. 677 | the two-torus clause of Root-F | interpretation question; the last-scale design is proved in abstract form and wired for Root-F's tori; at the scales just below the last no floor is needed for supports of radius below ℓ/20, and the clause holds on the whole quarter box given the closeness of the inherited terms, with the induction over the gap scales (proved in abstract form); tying it to the tower's step terms remains (item 24) |

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

A route along these lines (`notes/phase1/Q13-YM.md`): keep the large-field tests free of the external field up to the switching scale and carry the field in the weight, which preserves the symmetry the tests need; extend the direction tests of P5 (1.19) over the collar that the background reads. What remains unproved is the activity bound on the transverse source radius of order β^{-1/2}. The constant check is done: the extended tests need p₀ > d, and P5 (1.30) takes p₂ = p₀ − 2d − 2 with p₂ ≥ 2d + 2, so p₀ ≥ 4d + 4.

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
large-field step itself. Two of the three are now proved: the inherited old-term bound follows from the
bound of the formal large-field class, and the size of a removed component is at most its number of
cells, because its halo is connected whenever the separation of large-field components is at most twice
the halo radius. That holds at the largest radius the papers allow. In our construction the radius is a
free choice up to that maximum, and the maximal choice meets every hypothesis placed on the radii, so the
large-field histories are run with it. What remains is the small factor of removed components, P7 (3.10).
The gas bound is now proved from (3.10) in the form printed in the paper, given a numerical condition on its
exponent p₂; the size term of (3.10) is not needed, since removed components are small and one copy of
e^{−p₂} pays for their size. No part of the formalization yet produces (3.10) itself: it is the bound of the
removed operator, which belongs to the large-field step (P7 (3.7)–(3.10)). A plan
(`notes/phase1/LF4R-PLAN.md`) splits it into seven pieces. The first is proved: (3.10) follows from the
window integral of the removed outcome, ripeness and the residual-loss arithmetic. The residual-loss
arithmetic, the passage from kernel bounds to the gas, the volumes of the window variables and the removed
kernel itself (tied to the R operation, with its pointwise exponent bound) are now proved. Two points
remain before the window integral: the reference density must use the action restricted to the removed
component, as P7 writes it, and the objects of the step must be shown not to read the field inside the
integrated region. Both are now done up to explicit inputs: the restricted density is defined, with the
identity of P7 (3.5) proved unconditionally; its error term is bounded once the action outside the removed
component varies little over the cutoff ball. That needed the decay of the background's response from the
removed component to the component's edge (Q13-SHARED (2.4)), now proved uniformly in the component and the
scale; the error term is then of order one for the massless reference once the removed component lies at
distance of order log β_k inside its component. The history provides that margin (about R_base λ² cells), with
no cap from the coarse layers (proved). The
R operation now uses this density (its decomposition is generic in the reference density, and factorizes over
the separated components), and the window integral of the removed outcome, from which (3.10) follows, is
assembled from proved pieces, including the unrolling of the step's kernel into its ancestors and the geometry of
the removed components. The regrouping of the variables is now proved, with the Gaussian variables of the
ancestors and the shell variables of the quiet steps exposed: every variable of the window is a core variable, a
Gaussian variable or a shell variable, the Gaussian integral and the shell volumes are bounded, and the pointwise
bound and support of the integrand follow. Two inputs of this step remain named: a bound on the ratio of the
characteristic function to the restricted reference density that is uniform in the outputs still free, and the
quietness of each ancestor of the window. The composed bound is proved from these inputs. The quietness of the
ancestors is how the window's starting scale is chosen; the quotient bound needs the integrand bound to keep the action
of the quiet steps and their exact Gaussian composition, which P7 (2.58′) pairs with the restricted density (the bound
of the steps that keeps the action, the identification of each step's action with the window's action, and the exact
Gaussian integral over the window's intermediate variables are proved, and the composed Gaussian matches the one of
P7 (2.58′)). As in P7, the intermediate Gaussian variables are integrated exactly first; the actions of the steps then depend
only on the remaining variables, and their sum is the action of the window up to a bounded constant (P7 (2.15′)),
after which the cancellation identity of (2.58′) applies at each configuration. This composition is being built,
with the window's data indexed by the pieces of its steps (`notes/phase1/LF4R-PLAN.md` §9); the bounds of the kept
components need the same step. Above the window, the gas bound is now derived from the window bound of each history (summed over histories,
with the ripeness of removed components from the counter of the history), given two further inputs: the
representation of the output of R as the gas with these removed weights, and the bound of the kept components. The other
remaining input is the bound |E_k| ≤ C(log β_k + 1) on the vacuum energy of the class (P7 p. 520), being derived. The locality holds for the
characteristic functions and the domain; for the step's own exponent it is an input of the step data. The halos used as labels of
removed components lie in the domain class, because its blocks may sit at every cube offset (P5 (2.2)–(2.4))
and the halos are wider than one block (proved). The numerical condition on p₂ holds for large β once the
size of a removed halo is counted by its enclosing box, since removed components are boxes of bounded side.
The question to the author is item 16 with its addendum
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
remains: the large-field part (the region where the field cutoff fails) and the joins to the physical
flow. For the comparison of constants, the last-scale interaction has been identified with the summed
energy terms of the class at the last scale; its analyticity domain is the class domain, of radius ε_{k_f}
(which shrinks with the scale), not a fixed constant as we first assumed. The condition needed is
B(κ) β_{k_f}^{−1/2} p₁(β_{k_f}) < c ε_{k_f}, and it holds for β above a threshold independent of the scale
(proved). The theorems of the last integral now hold for the N components of the model (the scalar ones
are the one-component case). The final field lies in every term's domain when the terms use whole-level
charts (proved, by perturbing the critical datum), and also for the class's local generating sets, at the
cost of a constant factor in the radius (proved). The coefficient bounds of the cut expansion are still
stated with a bound on the whole interaction, which grows with the volume. The term-by-term version is
proved: each local term's coefficients are bounded by its own size and vanish away from what it reads; the
volume-uniform bound follows from the count of the polymers through a point (proved, with a constant
independent of the volume) and the weak dependence of the terms, composed with the background, on distant
data (proved: the background's response decays exponentially and the terms are Lipschitz inside the local
chart; the count of sites at each distance is polynomial), and all the numerical conditions hold for α₀ and
the cut radius small and β large (proved). What the small-field part of the last integral still takes from the
flow is that the block datum lies in the class chart with some room. For the large-field part, P7 §4 does not apply the cut
family to the large-field components: they enter the final polymer expansion as polymers with absolute
bounds, from the Gaussian tail of the unit fields (`notes/phase1/FINALPHYS3.md` §6). The tail bounds per
block are proved, and so are the decomposition into large-field block sets, the activity of each set, and
the polymer gas for these sets (counting of connected block sets, entropy, the activity bound for β large,
which needs the exponent of the field cutoff to exceed half that of p₂). One point is open and is now a question to the author (item 18 addendum):
on cells meeting a large-field set the decoupled covariance would move the field out of the analyticity
domain, and we read P7 as expanding only on the complement, with the large set entering through a
background that depends on it.

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

Progress (October 17). The rotation clauses of the class are now stated for real rotations only, and
invariance under a complex rotation of the form Q·exp(A) (Q real) is derived from them by analytic
continuation along a path that stays in the domain. The renormalization step uses invariance under the
complex rotations that turn the background direction into a fixed axis. These rotations need not be
close to real ones (a counterexample is in Lean), but they need not be: any complex orthogonal matrix
with bounded entries factors as a real rotation times a Cayley transform, and the Cayley path stays in
the domain, so invariance along it follows from the real clause (proved). The theorems of the
renormalization step still carry it as an explicit hypothesis; restating them on the Cayley path is
planned (`notes/phase1/CROTE.md`). The centre-labelled terms are built, and their clauses at the new level are
proved for the actual chart (the terms are completed in a slightly larger chart where only their locality is
used, since the crude chart inclusion fails at every level). What remains for the new level is the identity
between the actual new density and the sum of these terms. The density is now defined for complex,
non-constant external fields (it agrees with the earlier one on constant real fields, and is analytic on the
class domain); the identity cannot be continued from constant fields (they are not a set of uniqueness), so it
is being proved at every datum. That is done for the zero class; for a general class the value at every datum is
proved given the marks and activities of the old terms. The marks are now built from the old terms on the local
generating sets, label by label (their sum identity, locality, bounds and joint analyticity proved), and so are their
activities (the replacement identity of the old terms on those sets holds as functions of the datum, proved). So the
value at every datum for a class with inherited labels is proved up to numerical conditions. A re-reading of the sources
showed that the inherited terms must enter through their irrelevant parts (P1 Prop. 3.10, (3.126)–(3.131), used in
P4 p. 704): the per-term bound of the class (P4 (H.4)) does not decay with the level, so a sum of the raw terms over
the domains containing a given set is not bounded uniformly in the scale, while the irrelevant parts gain a factor
L^{-(k-j)(d+α₃)}. The representation by irrelevant parts is proved on ℤ^d, and now also its exact torus form
(the irrelevant parts summed over the labels give the energy terms of the class on every torus). What remains is
their bound: away from the cube of each centre it follows from the ℤ^d bound once the data lie in the analytic
domain of the anisotropic expansion (an open analytic input), and the label at the cube itself carries the torus
defect of the renormalization conditions. The papers take the class index at least 4, which the label settings
need. Old terms keep their domain through the fluctuation step. For the renormalized mass the domains cannot be shown to
shrink with our choice of radii, so old terms keep the domain of the scale where they were created, which
needs only how the backgrounds respond to the small change of mass. That response is now proved at every
level (the domain at mass ν lies in the domain at mass ν(1+t) with a radius larger by a factor 1 + K|t|), and
so is the resulting inclusion when the real witness of the external field is a unit vector, as in our
scheme (`notes/phase1/D2B.md`). The unit-vector condition has since been removed (any chart point can be
re-realized at a unit witness, at the cost of doubling the radius), and the inclusion holds for the actual
chart points under one numerical condition on the radii (the gap between successive class radii). That
condition now follows from the constants (the class radii decrease geometrically, with ratio L^{−α} ≤
1/(16 C₀⁴)), and the expansion of the old terms is stated on their birth domains, using only the clauses of
each old term at its own level. Two auxiliary radii of the step are small multiples of the class radius
(one once the cube size is large, the other for β large; both proved), and the chain is tied to the run:
what it still takes from outside is the bound on the renormalization corrections of the flow (P4 (5.31))
and a small margin in the mass condition, ν L^{2(k+1)}(1 + r) ≤ 1 instead of ≤ 1.

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
only with distance). This is now wired into the resummation for Root-F's tori: the last-scale coefficient
sums converge over growing tori with any prescribed decay rate. The decay constant of the closeness depends
only on the dimension and L, so the condition on the rates holds once the cube size M is large. Truncating the walk expansion of the final operator to the
region, as in the Yang–Mills account, does not work here: the final operator is a Schur complement and the
truncation changes it by order one near the boundary. Root-F as stated carries no lower bound on the
torus size; for the scales just below the last one, the margin our locality results need grows with L, so
either those terms are shown to be torus-local with a margin independent of L, or the statement needs a
floor on the torus size. This is part of item 24.

Progress (October 17, `notes/phase1/TORUSLAST2.md` §6): at those scales only the aligned L-block cover of a
polymer and its hull read L cells; every other ingredient needs a fixed number of cells. A nonzero term lives on
a union of such blocks, so its support already contains an L-block, and the transport between two tori holds for
supports of radius below ℓ/20 without any floor (proved). The terms are covariant under translations by whole
cells (from the lattice symmetries already proved), so a support of diameter D anywhere in the quarter box can be
recentred, and the transport holds when 25D + 25 < min(ℓ, ℓ′) (proved, given the correspondence of
coefficients near the origin). Wide supports are bounded by the decay of the terms with an absolute rate, and the
scales just below the last are now assembled into the two-torus resummation for every support in the quarter box,
given the closeness of the step's functional between two tori at those scales. For compact supports the step's
energy terms agree exactly between two tori (proved, by recentring), and the inherited terms enter only through
their own closeness, which the earlier scales provide. The step's energy terms are identified with these
expansions at the cells of the support (proved), and the determinant and observable terms are transported the same
way (translation covariance of one torus and recentring on two tori, proved); the identification with the step's terms at the cells is
proved for both, so the clause at the scales just below the last holds for every support in the quarter box given
only the closeness of the inherited terms; the induction over the gap scales that provides this closeness is proved in
abstract form, with a compact threshold slightly lower than before so that the determinant comparison has room
(the rates are unchanged). What remains is to tie the abstract terms to the tower's step terms, which no landed
object defines yet, and one direction of the domain correspondence for the tower's own label family. The question is in
item 24, second addendum.

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
