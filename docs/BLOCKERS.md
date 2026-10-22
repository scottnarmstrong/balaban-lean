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

*Last updated: 2026-10-22.*

## Where each blocker stands (22 October, morning)

How far each blocker is under control, in one of four grades: **resolved**; **figured out, finishing** (every step
has a proof route that works in Lean, what remains is assembly and engineering); **route clear, substantial work
left**; **open question** (a step whose truth or method is not yet settled). No blocker is stuck. Several items
turned out larger than estimated, mostly where the Lean transcription of a definition differed from the printed one;
each was corrected by a change approved by the author (R12–R29, listed in `AGENTS.md`; R27 was withdrawn as not
needed). For blockers 1, 3, 4 and the first half of 5 the final assembly is proved as a theorem whose only
hypotheses are the remaining pieces, each named; some of this is on branches being merged.

| # | Grade | What remains |
|---|---|---|
| 1 | route clear, substantial work left | The case with no renormalization step is proved. For the base case, the final assembly is proved (on a branch being merged) as a theorem whose only hypotheses are the remaining pieces, each named. These pieces are the first step's small-field inputs, its first density as a sum over histories, its boundary terms, the coefficient limit, torus independence and the vacuum bound. About 19,000 lines remain, and none of it is an open question. The first step is the scale-0 case of the general small-field step and uses the renormalization machinery written once for every scale. Several pieces of that machinery are proved on branches being merged: the bridge from the counterterm system to the renormalization conditions, the additivity and bounds of the relevant parts, and the split of the mass term under ruling R24. The moment condition of P4 (5.10)–(5.14) is being proved through a reduction to one dimension on the discrete torus. Ruling R25 (the first step's source factor) is implemented. The first step's own pieces are proved or in progress: constants; gains of the first large-field components; determinant terms; the finite-range whitening of the Gaussian chart and its cutoff transfer; the R₁ decomposition; the cluster coefficients as local families (agreement across levels and rotation covariance proved); and the Gaussian factor of the cut kernel. |
| 2 | resolved | Removed by ruling R16: the boundary terms are needed only at the physical external field. The estimate the blocker asked for is not proved; in the form first stated it is false. |
| 3 | route clear, substantial work left | The old boundary terms across a new hole are defined and bounded at the pre-R records from one named estimate, the complex form of P5 Lemma 2.1 on a region (it needs the fluctuation machinery extended from whole levels to regions). The data estimate is proved, including the data sites far from the new holes. The final assembly is proved (on a branch being merged): its hypotheses are the identity of the old part of the new boundary terms with these terms, and the (D7) clauses. Six of the seven clauses are proved; history locality is being completed (rulings R22, R26) and Euclidean covariance follows. About 9,400 lines remain: the region chord identity, the Prop 3.3 engine on pairs of regions, the interaction family, the region form of P5 Lemma 2.1 and the identity. |
| 4 | route clear, substantial work left | The vacuum part is proved; the small factor of removed regions is proved on unit external fields; the window bound uniform in the scale is being completed in Lean. The final assembly is proved (on a branch being merged) from three constructions and seven named conditions. The connectivity input of the new boundary terms is discharged: no component is removed at the first large-field scale, and at later scales the region has no diagonal corners when L ≥ 11 (so ruling R27 was withdrawn). The new boundary terms and the new small-field remainder are constructed by the cluster expansion of the gas of removed components (P7 (3.26)–(3.29)); their definitions are written and checked against the source. The kept kernels follow ruling R28. About 5,000–7,500 lines remain. |
| 5 | route clear, substantial work left | The last integral is split into a box and a tail; the box integral is an explicit polymer gas. *Small-field half:* the final assembly is proved from a local form; about 3,000 lines remain. Two design points were settled: the cubic term of the action needs an even rescaling to be of second order (in P4 (2.51)–(2.53) symmetry makes it second order), and the inherited terms are evaluated at composed data through P3 Lemma 4.2 (at the decoupled backgrounds the needed smoothness is false, P3 p. 57). Its one analytic input shared with blocker 6 is proved once for both. *Large-field half:* rulings R21, R23 and R26 corrected three transcriptions; its gluing step and history assembly are proved; about fourteen pieces remain. |
| 6 | route clear, substantial work left | The step chain is complete: with ruling R13 the new level's terms are computed on local generating sets and its clauses hold along the chain. Rulings R15, R18, R19, R20, R24 and R29 settled the cell term, the tori the class reads, the external-field term, the torus independence, the mass-term convention and the torus coherence of the source terms. What remains is substantial: the step map itself (designed), the local families of the new level at every root, the new level's source terms, the renormalization identities, and the agreement of the new level's terms on two tori (several thousand lines). |
| 7 | route clear at each step; open at the last scale | Update (22 October). At the distinguished cell, the relevant parts are now extracted only from polymers inside a fixed box around the cell, an eighth of the side of the smallest torus (ruling R15, implemented). With this the cell term agrees exactly on two tori, and the agreement of the new level's coefficient on two tori is proved with the cell case discharged. What remains for the step is to turn this into the torus independence of the class's terms for the next scale: the class asks it only on pairs of admissible tori, for polymers whose neighbourhood of the size the terms read does not wrap, and at fields in the class domain (ruling R20). The terms of the new level are computed on local sets of the polymer, so this needs their agreement on two tori at local data, which is being proved by transporting each ingredient between corresponding local sets (operators, decoupled background and fluctuation, determinant part, activities and marks done; the assembly of the coefficient remains). At the last scale, activities that are close on two tori are turned into activities that agree exactly (proved); what remains there is the closeness of the local terms of the last integral. |

## Summary

| # | Issue | Where | Blocks | Status |
|---|---|---|---|---|
| 1 | Base case of the large-field induction; the case of no renormalization step | P5 (H.1), (1.1); P7 §4 | Root-F for large external field ν; start of the large-field induction | the case of no renormalization step (ν > 7/(8L²)) is proved in Lean (20 October): a direct one-scale route by finite-range whitening of the Gaussian chart and a polymer gas on blocks of side M·L, needing only that M·L exceed a threshold depending on d, N, L and κ; base case of the induction: the final assembly is proved from a fixed list of named pieces (22 October, on a branch being merged), and the pieces remain, about 19,000 lines (the first step's terms and their local families, the renormalization at scale 1 including the moment condition, the cut kernel and the first density); local pieces of the first component proved (W981); the Yang–Mills first step (item 17 addendum) was the guide for the route |
| 2 | Switching from ν-free to complete backgrounds | P6 p. 11; P2 (1.11); P5 (1.4), (1.19) | small-field terms entering the large-field step | **resolved** by ruling R16 (21 October): the large-field boundary terms are asked to be analytic and bounded only at the physical external field; the statement this blocker concerned is needed by no proof (the whole project builds without it) and has been removed. The estimate it asked for is not proved; in the form first stated it is false. |
| 3 | Old boundary terms across a new long hole | P6 p. 34; P5 (1.33)–(1.34); P3 (4.48) | localization for general classes; large-field boundary terms | cause located: our domains must be unions of cover cubes even inside the holes, and new holes need not be; the transfer of every domain across any new hole is proved once that requirement is limited to the small-field sites (ruling R11, approved and applied 19 October); the three earlier routes do not close it; R11 applied 19 October; what remains is to build the old boundary terms of the step and prove their bound (no open question) |
| 4 | The gas of removed components and retained holes | P7 (3.26)–(3.28) | the large-field polymer gas | possible resolution (clusters on the core), formalized down to one physical input, the small factor of removed components (P7 (3.10)), which the large-field step still has to produce (the gas bound is derived from the window bound of each history; the window bound is being completed along P7 (exact Gaussian integral, the steps' actions summed into the window action, the cancellation identity), with the named source estimates of P7 (2.11)–(2.16) as inputs; the representation of R's output as this gas, the bounds of the kept components and the vacuum energy bound remain); author confirmation asked (item 16 addendum); the window conversion now rests on one design point, the window's field off the pieces; vacuum: the step's vacuum constant is bounded (proved), the vacuum region of one component is now restricted to the component (ruling R10, approved and applied 19 October); window domain conditions proved at the ancestor pieces, the removed component's own piece in progress |
| 5 | The cut family for the last integral | P7 §4; P4 (6.4)–(6.6) | the last integral | open; the two halves are now split as in the papers (21 October): the small-field half is the integral with the cutoff of the Gaussian fluctuation variable on every site, the tail joins the large-field half; the small-field half is being proved by a polymer expansion over the box (localization of every term, the gas on cut cells, and a second-order bound on the source terms from the symmetry of the Gaussian); determinant and interaction localized; the amplitude follows the papers (normalization at g = 0, second-order bound, cross term with the source-free exponent); the last-scale interaction identified with the class's energy terms (radius ε_{k_f}; comparison, N components, the domain inclusion and volume-uniform coefficient bounds proved); the identification with the physical density, the large-field part (route from P7 §4 built; the coupling across a large set asked, item 18 addendum) and the joins remain; the singleton-gas reading of the large-field part is refuted by an example, and the linked gas of P7 (4.11) is being built |
| 6 | Local generating sets and analyticity on their domains | P3 p. 78, (4.44)–(4.47) | the output class of each step | route fixed without a ruling: the step chain now returns the coefficients of the new level as a formula, and each term is recomputed on the local generating set of its polymer (P3 p. 79); the larger chart radius this needs is real but used only by identities, never by a bound; the generic objects of the step on a local set are built and audited; the formula is carried through the chain, and under ruling R13 (the class generating sets are the local sets of the thickened polymers) the clauses (A1)–(A5) are proved at every step of the tower for the chain's family, with the chain's chart premise replaced by the inclusion of the composed data in the class domain at the birth masses; what remains are conditions on constants of the local recomputation (radii of the marks, smallness against the cap of the cluster expansion, the room of the charts at the birth masses, which needs `L` large) whose joint satisfiability is to be shown, and the bound of the class on its term domain (an input shared with the step chain) |
| 7 | Reading of the torus-independence clause | P4 (H.4), p. 677 | the two-torus clause of Root-F | interpretation question; the last-scale design is proved in abstract form and wired for Root-F's tori; proved at the tower on one family of tori of every size; one family over all tori needs exact two-torus agreement of the terms of small polymers, now proved for the coefficients of a step and being carried to the next class; the induction over scales and the sum over roots remain |

## What closes each blocker

A blocker counts as closed only when the Lean statement it obstructs is proved, with no hypotheses beyond the
papers' own premises, and is merged. A lemma that removes the mathematical difficulty is reported as that lemma,
not as a closed blocker. All statements below are in `Balaban/Spine/`.

| # | Statement that closes it | Proved |
|---|---|---|
| 1 | `KfZeroInput` (the case with no renormalization step) and `BaseStepInput` (the first step) | `KfZeroInput`: yes (20 October, `kfZeroInput_of_typing`; the one condition beyond the statement is a lower bound on the block side M·L by d, N, L, κ, a choice of the exponent of M = L^n); `BaseStepInput`: no |
| 2 | none left: `LFBdrySrcInput` was removed by ruling R16 (21 October), since no proof needs it | resolved by ruling; the estimate itself is not proved |
| 3 | `LFBdryOldInput` for the step's actual boundary terms (needs the step with holes and the modular localization of the old terms) | no |
| 4 | `RKeptGasInput`, with the vacuum bound `RVacuumB0Input` | `RVacuumB0Input` yes (20 October); `RKeptGasInput` no |
| 5 | `FinalSmallFieldInput` and `FinalLargeFieldInput` (the two halves of `LastIntegralInput`) | no |
| 6 | the clauses (A1)–(A5) of the new level on the local generating sets, in `SFNewLevelInput` | no |
| 7 | the two-torus clauses: exact agreement of the last-scale activities in `FinalSmallFieldInput`, and the agreement of each step's terms carried by the class | no |

## Proceeding without the author's answers

Several blockers carry questions to the author. We no longer wait for them: the two main theorems are
statements about the model, so any construction that proves them is acceptable. Where the papers are
ambiguous we choose a reading, record it, and prove what it needs; an answer, if it comes, becomes a
check. Choices that change approved definitions are approved by the author first; all those asked so far are approved
(recorded in `AGENTS.md`, "Author rulings"): blocker 2's route, the representation of the large-field output as a gas and
the vacuum clause of the step data (blocker 4, with the vacuum region of P6 (3.2)), the birth-mass domains of the
inherited levels, the physical carrier of the first large-field step (blocker 1), the computation of the new level's
terms with local generating sets (blocker 6), and the repair of a complex-rotation hypothesis that the audit of the
definitions found to be a hidden proof step. Opening new regions with aligned blocks
was checked and does not close blocker 3: it breaks the Euclidean covariance of the coefficients, and a completed hole
still has positive length between two active attachments.
The plan, blocker by blocker, is in [`notes/phase1/PLAN-B.md`](../notes/phase1/PLAN-B.md). Earlier focused analyses of the
open questions are in [`notes/phase1/astra/`](../notes/phase1/astra/).

A finding that concerns all blockers: the step tower produces the setting of each step but not yet the class of the
next step (its terms, vacuum energy and family over tori). Many results above are proved for a given class; feeding the
output of one step into the next is the backbone of the assembly of Root-F. A proposal for the next class is written
(`notes/phase1/astra/SFFAM.md`, Part 2); the transport of the old terms to the next torus is proved (W985). The domain of the old levels needs a ruling:
with the current scale's mass for every level, the inclusion across a step fails at admissible constants
(SFFAM.md Part 3); domains frozen at each level's birth mass are recommended (PLAN-B, R6).

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

Update (17 October, evening). The first large-field component of the base case now has its local pieces in Lean (W981):
the chart identity of a selected record, positivity of the local cut operator, the determinant factorization across a
cut, the exact first partition, and the count of records from an injective local code. The physical activity estimate
(P5 (30)), the staged operator and the local code itself are the next round. For the case with no renormalization step,
a general-scale component theorem was tried and refuted in the form we had proposed (see blocker 5, the example of
`notes/phase1/astra/KF0B.md`, Theorem B.7); the case now goes through the same linked gas as the last integral.

Update (20 October). The case with no renormalization step is proved in Lean (`kfZeroInput_of_typing`,
`notes/phase1/KF0-FR.md`). The route does not separate the sectors. On each sheet of the sphere chart the
Gaussian variables are whitened with a finite-range square root C_R of the covariance (range about M·L/4).
The Gaussian weight becomes a product of one-site Gaussians times exp(−⟨ψ, Q_R ψ⟩/2), where the defect
kernel Q_R = C_R K C_R − 1 has range 2R + 1 and row sums that decay exponentially in R/L². Every factor of
the density, including the spins on the opposite hemisphere, is then a function of the variables in a ball
of radius 2R + 1, and a polymer expansion on the torus of blocks of side M·L applies. Configurations with a
large Gaussian variable or a spin on the opposite sheet are rare in measure; a product bound over marked
sites controls them without a pointwise bound on each factor. The only condition beyond the statement is
that M·L exceed a threshold depending on d, N, L and κ; M is a power of L, so this is a choice of the
exponent. The sector split of the earlier attempt (all-good sector, bad sectors as a linked gas) is not used.

Update (21 October, evening). Work on the base case (the first renormalization step, the statement
`BaseStepInput`) has started on the following plan. The first step is treated as the general small-field step at
scale zero, so its small-field output must satisfy the same named conditions as every later step. In Lean so far: the
bookkeeping of the first step (its constants, kept data and step data at every scale, the vacuum flow); the
assembly of the small-field conditions at scale one from the same pieces as the general step; the gains of the first
large-field components from the lower bounds of LF-1; the exact identity of the first density in the all-good sector;
and the Gaussian ingredients of the first fluctuation integral (the covariance family, its square root and logarithm,
the localized determinant terms, their agreement on two tori). One step of the papers does not carry over to scale
zero: the local change of variables of P5 (2.39) uses a cube-by-cube square root of the covariance, which is exact
from scale one on (where the basic quadratic form is block-diagonal) but leaves an error of order one at scale zero,
where the Hessian contains the lattice Laplacian. The first step therefore uses the finite-range whitening that solved
the case of no renormalization step: a polynomial approximation W of the inverse square root, of finite range, whose
error W A W − 1 is small (proved). Still open: the cluster expansion of the first fluctuation integral, its
regrouping into the terms of the class at scale one, the renormalization conditions at scale one, the large-field
kernels of the first step and the identity that represents the first density in the class. The small-field part
shares the open steps of the general small-field step (blocker 6 at scale zero).


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

Update (17 October, evening). Route R-YM′ is formalized up to the physical kernels (W973): the sharp tube for the raw
mass weight (with an N = 2 example showing that the disc of radius β^{-1/2} is too large), the transport of the running
radius with one failed test paid by the collar reserve, the cancellation of a common mass factor in log Z(g)/Z(0), and the
P5 (1.31) kernel estimate under named kernel bounds. The rest needs the separate background and cutoff masses below k₀
and a complex-source kernel interface, which change landed definitions (ruling R2).

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

Update (17 October, evening). The exact geometry of openings at every offset is settled, and a thick inherited seam
gives a spill linear in its length (`notes/phase1/astra/ALIGNED.md`, round 2). The displayed estimates of P5–P7 do not
pay a bridge between two attachments across a hole. Two closures remain: the coefficients split over active cores, or the
coefficient of a cluster that couples two attachments across a hole carries an extra decay factor. The example of blocker
5 (a good block between two bad ones couples them) suggests the first fails, so the second is being proved, from the decay
of the massive covariance across the hole.

Update (19 October). The obstruction is now located exactly, and it is narrower than the papers' statements
suggested. A boundary term depends on the history of every large-field hole it meets, so its domain contains
those holes whole; our domains are in addition required to be unions of the overlapping cubes of the cover
(P5 (1.33)) at every site, the sites of the holes included. The new holes of the papers' construction need
not be such unions: where two thick pieces of an earlier large-field region meet diagonally, every cover cube
through a site of the seam between them contains small-field sites. Every admissible domain that contains the
hole then contains small-field sites along the whole seam, and its size grows with the seam's length, while an
inherited coefficient that does not depend on the fields, which the inductive class allows, has no decay to
pay for it. The same happens to the new terms of the fluctuation integral, whose natural domains are a
small-field set together with the holes next to it. None of the earlier proposals closes this: a special
property of the coefficients the step produces fails for the class, which must be carried through every step;
a stronger bound on the old coefficients cannot see the shape of a hole created at the next scale; and domains
that need not contain whole holes remove the spill but lose the count of domains used by the cluster
expansions, since a domain could then contain any part of a hole at no cost. What closes it is to require the
cover cubes only at the small-field sites of a domain: the size of a domain depends only on those sites
already, and a domain is still determined by its small-field part and the holes next to it. With this change
(ruling request R11, [`notes/phase1/PLAN-B.md`](../notes/phase1/PLAN-B.md)) we proved that every domain of one
scale carries over to the next scale across any new hole, with its size divided by L, and that the domains of
the fluctuation integral are admissible as they are. What remains for the old boundary terms is the analytic
re-expansion of P6 (4.32)–(4.34), which no longer meets the hole.

Update (20 October). Ruling R11 is approved and applied: the domains are redefined as above, and the counting
of domains and the growth of their sizes are proved for the new domains. What remains is not a question about
the papers. The old boundary terms of the step have to be built as explicit objects: for each new domain, the
sum over the old domains that carry over to it of the old term re-expanded at the new scale (P6 (4.32)–(4.33)).
Then the bound P6 (4.34) and the count of domains finish this blocker. Until those objects are defined, the
statement about the old part of the boundary terms says nothing about the actual step (W1148).

Update (21 October, correction). Building the old boundary terms showed that more is missing than stated above
(W1154). The assignment of each old domain to the new domains, the count of domains and the bound of the sum at
each new domain are now proved, for any coefficients with the bound of P6 (4.34). The coefficients themselves are
the old terms integrated in the fluctuation measure of the step with holes (P5 (2.48), (3.2)), and that step is not
yet built: neither the field of the new scale composed into the old one on the large-field region nor the
measure on the fluctuation fields with holes exists in Lean. The bound P6 (4.34) also rests on the modular
localization of each old term, which has open points of its own (one of them is author question 14 (ii)); we
choose readings for these and prove what they need. So this blocker is not purely Lean work, as said earlier.

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
remaining input is the bound |E_k| ≤ C(log β_k + 1) on the vacuum energy of the class (P7 p. 520). As literally
read it is false: from a fixed initial constant the vacuum energy grows like L^{dk}. It holds exactly when the
free initial constant is chosen so that the energy vanishes at the last scale; that constant cancels in the main
theorem, so we use this normalization (proved: the flow, its increment, and the bound for this normalization; the
determinant part of the per-step vacuum value is bounded). The new vacuum constant of each step is the Gaussian increment of the step, a function of β_k only, and its bound C(log β_{k+1} + 1) is proved; the part proportional to the volume goes into the normalization of the step. The vacuum term of the large-field step data, as written for one component, counted the whole torus outside the component, so its bound fails on large tori; restricting it to the component, as in P6 (3.2), has been done (ruling R10, `notes/phase1/PLAN-B.md`). The locality holds for the
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

Update (17 October, night). Ruling R4 is being implemented. Two corrections came out of it: P7 (3.22)–(3.25) fixes
only aggregate identities for the new boundary coefficient ℬ′, so we choose and record an explicit construction from
the landed localization expansions; and the pointwise bound (3.10″) does not imply the output-integrated bound used by the
gas theorem (a counterexample with m output points), so the gas activity is restated as an operator acting on the output
field. The window bound is being finished (the step that timed out is being split).

Update (18 October, later). The window conversion is assembled for the actual pieces: the read transport, the
coefficient response with all its budgets (the constant is uniform in the scale), the source and pair estimates, and
the first-scale mass identification (ruling R2) are proved. One premise remains: the comparison of a piece's local
background with the window's background, which solve the background equation on different generating sets. It needs
the stability of the background under a change of generating set away from the piece (P7 (2.14), P2 Prop. 4.1, P3
Prop. 2.1 for changed layers); this is being proved now.

Update (18 October, night). The stability of the background under a change of generating set is proved (P7
(2.14), W1048): on a ball where the layers agree and the data differ by at most δ_d, the two backgrounds differ by
K(δ_d + an exponentially small term in the radius). With it the window conversion holds with the actual window
background and no separate switch premise. What it still takes as input, on the balls around the pieces: a bound on
the difference of the window's data and the pieces' local data, the background hypotheses and domain conditions of
both, a radius condition (2M of order (ϱ_B + 3d)L, a choice of the constant M), and smallness.

Update (18 October, evening). The radius condition follows from a choice of M (W1059), and the background
hypotheses of the window generating set are proved (W1072: its separation is 5LM₁, and the mass condition follows
from the flow's constants). What remains is a design point. The window's field is fixed only on the pieces and is
zero elsewhere (on the core and on the unbounded region), so it fails the domain conditions there, and the balls
around the pieces on which the stability theorem compares the data reach beyond the pieces. No factor of the window
integrand constrains the field off the pieces (W1059, W1060, W1072); how P7 chooses it is being worked out (W1074).

Update (18 October, night). P7's own design settles it (P7 p. 501 (2.14), P6 p. 7 (2.16)): every piece background and
the window background are evaluated at the same configuration, so the data agree wherever the generating sets agree,
and the window's domain follows from the pieces' domains with no loss (W1074). The window conversion now has no ball
premise and no premise on the window's domain. Two links remain: that the window point's field restricts to each
piece's data, and the connection with the reference datum used by the cancellation chain.

The first is proved (W1082). The second exposed an error: the reference datum of the cancellation chain is zero on
the collar of the window, so it is not in the real domain there (W1085), and the chain's hypothesis cannot hold when
the collar is nonempty. The collar ruling (`notes/phase1/COLLAR-RULING.md`) already fixes the correct choice; the
chain is being restated with that collar data, and the comparison of the two window actions then reduces to a change
of mass and of external field (W1086).

Update (19 October). The domain conditions of the window conversion are proved at every piece that comes from an
ancestor of the window component: each such piece's data lie in the small-radius real domain, and the domain
condition of each ancestor's operator follows from a nonzero weight of the window's operator (W1143, W1150). The
proof for the window component's own piece assumed that this component is retained at its scale, but the bound is
used for a removed component; that piece is being redone for the removed case, together with the choice of radii at
the point of use (W1153).

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

Update (17 October, evening). The large-field part of the last integral was written as a singleton gas (W975), given
two identifications: the large variables integrate into a factor per block, and the boundary terms localize into
coefficients that do not depend on which blocks are bad. The second identification is false when read for exact cut-off
cells: in an example with a small nearest-neighbour perturbation of a product Gaussian, the good block between two bad
blocks couples them, and no choice of connected boundary terms reproduces the weights
(`notes/phase1/astra/KF0B.md`, Theorem B.7, by strict Cauchy–Schwarz). This is not a counterexample to the papers: P7
expands after (4.11) into linked terms, whose activating set may be disconnected while the set they read is connected.
Being built now: the polymer gas with separate activating sets and footprints (W990), and the reorganization of the last
integral into linked terms with their bounds (W984).

Update (17 October, night). The abstract gas for linked terms is proved (W990): exact identity and activity bound,
with the large boundary constant of P7 (4.12)–(4.13) paid by the heavy charge. The last integral now has the variational
background on the complement of the bad set, bounds on the retained reference operator, and the exact crossing identity
of the boundary difference (W997). What remains is the bound on the coefficient summed over all linked clusters with a
given footprint, the heavy activity at the operator level, and the identification of the physical Hessian.

Update (21 October). The two halves of the last integral are now split as in the papers (P4 (6.6), P7 (4.9)–(4.11)). The
small-field half is the integral in which the Gaussian fluctuation variable is below its cutoff at every site; the region
where the class cutoff holds but the fluctuation is above its cutoff at some site is, in the papers, a new large-field region
of the last step, and it now belongs to the large-field half. The earlier split put it in the small-field half, where it could
not be expanded: the class cutoff is local in the field but not in the Gaussian variable. On the box every term of the class
stays well inside its analytic domain, so the small-field half no longer meets the obstruction of item 18. Proved so far
for it: the localization of a term of the field into pieces that are exactly local in the Gaussian variable (the cut family of
the final Hessian), the class cutoff equal to one near the constant field, the polymer gas over the box measure on cells of
the cut family, and the bound on the source terms, which must be of second order to hold at every scale and is obtained
from the symmetry of the Gaussian. Remaining for the small-field half: the localization of the terms that read the background
of the whole torus (by the decoupled background of P3 §2), the cubic part of the action, the regrouping into Root-F's
polymers, and (blocker 7) the closeness of the terms on two tori.

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

Update (17 October, evening). The anisotropic datum is produced from the step's chart witness (W969); what remains of
the per-label bound is the patched field in the class domain, then P1 (3.107) at the pulled-back field (round 2 running).
On the torus defect (W980): the expanded form of the filed sum, inclusion of small infinite shapes in the torus, equality
of all reference jets at every centre, and the reindexing of the torus sum are proved; the full cancellation of the raw
second-moment matrix and the tails remain (round 3 running). The base settings of the step are produced at the tower's
constants (W982); two numerical conditions need a tower with smaller t, being proved (W989).

Update (18 October, later). The chain uses the per-label bounds only at the composed data of the step, never on
the whole chart of a label; it is restated there (W1040), which matches the source (P1 (3.128), Lemma 2.1, P3 Prop.
4.3). The filed torus defect is proved at every centre, also on birth-mass domains. The condition that the composed
data stay in the domains of the inherited levels is real in the source and is paid there by taking the step radius
t_k = ε_{k+1}; it fails only because the tower fixes t. A tower with a scale-dependent t is the next step; the same
artefact explains the growth L^{2αk} found in blocker 4.

Update (18 October, evening). The fluctuation radius is now separate from the step radius (W1063). With the collar
of the landed chain (r₀ = 324) the closeness of the composed data does not decay, and covering the class chart while
keeping room for the inherited terms is impossible (proved). With the papers' wider collar and their radii
(t_k = ε_{k+1}, δ₁ = min(t_k, ηε_k)) both hold: the chain is proved at towers for every scale with one β₀ (W1069).
For the new level, the covariance of its densities under the full symmetry group is proved (W1064, W1070), given
the room condition, which is reduced to the chain's settings (W1071); the sum of the labels' bounds holds for every
class rate κ ≤ 1/5 at d = L = 3 (W1065, W1067). Remaining for the new level: its terms on the local chart of each
polymer (W1073: the polymer must be the hull of the labels' read set, and the terms must be carried from the step's
chart to the local chart; in progress), the closure of its energy constant, and the counterterms of P4 (4.14)–(4.22).

Update (18 October, night). The closure of the energy constant is proved (W1068) on one chain that carries any
property of the coefficients from the core to the final theorem; the coefficients are invariant under spin rotations
label by label (W1078, W1083). The renormalized field lies in the step's chart at the towers, and the second-order
counterterms apply there (W1079, W1080). The local charts cannot be reached from the step's chart: a local field can
wind around a hole of the polymer, which no field on the whole torus can do (W1081). As in P3 (4.44)–(4.47), the new
level's terms must be computed with the local generating set; the step's mark, determinant and activity objects are
written for the step's own generating set, and generalizing them is ruling R8, approved (`notes/phase1/PLAN-B.md`). The
determinant and the zero-source activities on local sets, which need no ruling, are in progress (W1084).

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

Update (17 October, evening). The determinant term of the tower is identified with the specification used by the
gap-scale clause (W979). The energy term needs the same recentred transport as the observable term, and the observable
term's formula clauses must be kept by the theorems that produce them; both are being done (W988, with a proof-body
refactor that leaves all statements unchanged). The wide threshold needs K ≥ 61, which fails at the top few gap scales of
the smallest tori when L < 61; a separate argument for these finitely many scales is to be written.

Update (17 October, night). The tower's determinant and observable terms are proved to agree on two tori (W988).
The energy term's coefficient is built on a record whose explicit form was discarded by the theorems that produce it;
those theorems are being refactored to keep it (no statement changes), followed by its recentred comparison.

Update (18 October). The clause at the gap scales is proved at the tower on one family of tori of every size
(W1021): the tower's new terms (energy, determinant and observable parts) agree on common quarter boxes, with the
supports, locality, analyticity, closeness bounds and the geometry of the recentred boxes proved, and with one
resummation covering small and large tori together. The input still assumed is the agreement of the earlier
scales' data on the recentred boxes (the induction over scales); for Root-F's clause, the sum over roots and
sites, the identification with Root-F's source, and the inherited terms of earlier scales remain.

Update (18 October, later). The clause holds in the literal form of Root-F (fine sites, the image of a finite set
in the common quarter box) at the first gap scale, and conditionally on the earlier scales at later ones. Two design
points remain: Root-F fixes its terms before the pair of tori, whereas the tower's resummation refers to a canonical
torus of a finite family, so one family of terms valid for all tori must be built (for instance as a limit over tori
on compact supports); and Root-F's terms depend on the source only on X, which needs the resummation of the
observable part alone.

Update (18 October, night). The canonical torus of the tower's resummation cannot be chosen over all tori at once:
its defining condition forces the size parameter to be bounded, because a one-site polymer lies in every torus. So
one family of terms valid for all tori needs the terms of small polymers to agree exactly on two tori, not only to
be close. That exact agreement is now proved for the coefficient family of a renormalization step: on two tori, the
coefficients of a cube set agree whenever the data agree on a box of radius R + 3L^{k+1} around it, with one
threshold β₀ for both tori (from the two-torus identities of the decoupled background, fluctuation and covariance).
It is being carried from the step to the class of the next scale; the induction over scales, the source term
⟨g, φ_k − h⟩ at later scales and general d, N remain.

Update (21 October). The agreement on two tori of the coefficient of each step's new terms is proved from the
agreement of its ingredients (inherited terms, marks, determinant part); deriving those ingredients from the class
needs the step to index and cover its inherited terms canonically (the same rule on every torus; the step chain is
being changed to do so), and the matching of the labels is in progress. One point is new and open: at the distinguished cell of an inherited
term, the term contains the sum of the relevant parts over all polymers through that cell, and on a finite torus
this sum includes polymers that wrap around it. The class renormalizes these parts only in the limit of large tori,
so the cell term differs slightly between two tori. The intended repair is the one already used at the last scale:
keep the non-wrapping polymers in the cell term and move the remainder onto polymers that wrap the torus.


Update (21 October, evening). Both open points of this blocker now have a design proved in Lean. At the distinguished cell, the relevant parts are extracted only from polymers inside a fixed box around the cell, an eighth of the side of the smallest torus (ruling R15, approved 21 October); larger polymers keep their relevant parts and are small by their size. With this, the cell term agrees exactly on two tori (proved), and its bound needs only the infinite-volume renormalization conditions (proved); the switch of the definition is being built. At the last scale, activities computed separately on each torus and close on two tori are turned into activities that agree exactly (proved: on small supports they are the limit over growing tori, and the remainder is moved onto the other polymers, with the condition that the block size M be large against the decay rate). Closeness of the activities of a polymer expansion follows from closeness of its local terms, and the cut family of the final operator is close on two tori with a margin (proved). What remains for the last scale is the closeness of the local terms themselves, which waits for the localized form of the last integral.
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
