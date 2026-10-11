# Library: Balaban's low-temperature O(N) theory and its sources

Annotated index of every source in `../sources/`, as of 2026-10-11. Keys as in
`SOURCES.md`: P0–P9 the O(N) bundle supplied by Roland, E1–E11 earlier papers
and cited cluster-expansion sources, D1–D3 Dimock's exposition. Each entry gives
the citation, the file, the review, the status, an annotation (what the source
is, and what the formalization of the O(N) theory takes from it) and a reading
priority:

- **essential** — the formalization depends on its content directly;
- **important** — a template or a design reference that will be consulted
  often;
- **background** — context; consult only for a specific question.

Entries are grouped by topic, in the order a reader would take them. A
suggested reading path for a new collaborator is at the end. The synthesis
documents are `BIG_PICTURE.md` (the mathematics and how the papers fit
together) and `FORMALIZATION_ROADMAP.md` (the plan); `QC_LOG.md` records the
orchestrator's checks. P0–P4 and E1–E11 are scans (read page images; their OCR
is unreliable); P5–P9 and D1–D3 have usable text layers.

---

## 1. Orientation

**P0** — T. Balaban, "A low temperature expansion and 'spin wave picture' for
classical N-vector models", in *Constructive Physics* (Palaiseau 1994), Lecture
Notes in Physics 446, Springer 1995, pp. 201–218 (venue inferred from P5 p. 488).
File `3-540-59190-7_30.pdf` (18 pp.). Review
[`papers/P0-survey-spin-wave-picture.md`](papers/P0-survey-spin-wave-picture.md).
Status: obtained.
A proof-free survey announcing the whole programme: the spin-wave picture
(Thm 1), the variational problem (Thm 2), the bound on the effective action from
renormalization conditions (Thm 3), the small-field hypotheses (Thm 4), one-step
stability with the RG equations (Thm 5), and large fields "only as an idea of a
theorem" (Thm 6). Its hypotheses (H.1)–(H.7) are numbered differently from P1
and P4 (concordance in BIG §2.4). Nothing depends on it logically; the
formalization takes only orientation from it.
Priority: **important** (the shortest way into the series).

---

## 2. The O(N) series: small fields

**P1** — T. Balaban, "A low temperature expansion for classical N-vector models.
I. A renormalization group flow", Commun. Math. Phys. 167 (1995) 103–154.
File `BF02099355.pdf` (52 pp.). Review
[`papers/P1-LTE-I-RG-flow.md`](papers/P1-LTE-I-RG-flow.md). Status: obtained.
Fixes the model, the block-spin transformations $T$, $S$, the small-field
restrictions, the background fields and their analyticity domains, the
localization domains $\mathcal D_j$ with tree length $d_j$, and the inductive
hypotheses (H.1)–(H.9); states the small-field Main Theorem 2.2 without proof.
§3 proves the renormalization analysis: under the hypotheses, the effective action
is bounded by a constant times the volume of the current lattice (Prop 3.10,
Cor 3.11), via effective potential, gradient expansion and a Ward identity. The
formalization takes the definitions (Def-2–Def-4 of the roadmap) and §3 as the
interface I-6.
Priority: **essential**.

**P2** — T. Balaban, "The variational problems for classical N-vector models",
Commun. Math. Phys. 175 (1996) 607–642.
File `BF02099510.pdf` (36 pp.). Review
[`papers/P2-variational-problems.md`](papers/P2-variational-problems.md).
Status: obtained.
Existence, uniqueness, analyticity and scale-weighted bounds for the minimizers
of the multiscale variational problems on generating sets (Prop 1.1, Cor 1.1),
the perturbed system with independent data (Prop 3.1), constant configurations
(Props 2.1–2.2; the proof of 2.2 is omitted) and two nested generating sets
(Prop 4.1, formula (4.21)). It handles the singular constraint equation by a
discrete Leibniz-rule device that survives at $\lambda=\infty$. Its Green's
function input is cited to E5 (as "[2(b)] Prop. 2.1, (2.57)" = E5 Prop 2.2,
(2.67)); the roadmap replaces it by the interface G-2. The formalization takes
Props 1.1, 3.1, 4.1 as the interfaces I-1, I-2 (the background fields are
defined only after their `∃!` theorems).
Priority: **essential**.

**P3** — T. Balaban, "Localization expansions. I. Functions of the 'background'
configurations", Commun. Math. Phys. 182 (1996) 33–82.
File `BF02506385.pdf` (50 pp.). Review
[`papers/P3-localization-I.md`](papers/P3-localization-I.md). Status: obtained.
Localizes the non-local functions of the background fields: random-walk
expansions of $G(\alpha)$ with complex decoupling parameters attached to large
cubes (Props 2.1–2.3), localization of the fluctuation covariance $C^{(k)1/2}$ and
its logarithm by resolvent integrals (Prop 3.1), and the main localization
expansion with doubled decay rate (Prop 4.3). Its Green's function inputs are
cited to E5 with equation numbers offset by +10 (QC_LOG Phase 3) and to E3 §5.
The formalization takes Props 2.1–2.3, 3.1, 4.3 as the interfaces I-4, I-5, and
its consumed Green's function bounds (C4–C6 of roadmap §3.4) define G-2, G-3.
Priority: **essential**.

**P4** — T. Balaban, "A low temperature expansion for classical N-vector models.
II. Renormalization group equations", Commun. Math. Phys. 182 (1996) 675–721.
File `Balaban.pdf` (48 pp.). Review
[`papers/P4-LTE-II-RG-equations.md`](papers/P4-LTE-II-RG-equations.md).
Status: obtained.
The sharpened small-field hypotheses (H.1)–(H.7), Theorems 1–2 (one small-field
step and the RG equations for $\beta_k,a_k,\lambda_k,\nu_k$), the fluctuation
integral including the special first step, the renormalization operation, the
solution of the RG equations by contraction (Prop 5.1) and the small-field last
step (§6). Its localization propositions are deferred to P6 §4. Its "[3]" is a
conflation of P3 and E3 §5, and its "[2c]" is E3 (1.22) (BIG §7 item 6). The
formalization takes Thms 1–2 (I-9, the internal small-field milestone), Prop 5.1
(I-7) and §6.
Priority: **essential**.

---

## 3. The O(N) series: large fields

**P5** — T. Balaban, "A low temperature expansion for classical N-vector models.
III. A complete inductive description, fluctuation integrals", Commun. Math.
Phys. 196 (1998) 485–521.
File `s002200050433 (1).pdf` (37 pp.). Review
[`papers/P5-LTE-III-inductive-description.md`](papers/P5-LTE-III-inductive-description.md).
Status: obtained.
The full inductive description with large-field regions (H1–H7), the density
spaces (1.42), the main Theorems 1–4 of the series (one full step with H6
weakened; the $R$ operation; their composition; the regime $k\ge k_0$), the
transformation $T^{(k)}$ with new small- and large-field regions, and the
classification of fluctuation-integral contributions (Props 3.1–3.4, proved in
P6 §4). Admissibility of multi-indices is described, not defined (pp. 493–496);
the base case is narrative (pp. 486–487). The formalization takes H1–H7 as
Def-7 (after reconstruction, roadmap §4) and Thms 1, 4 as LF-3, LF-5.
Priority: **essential**.

**P6** — T. Balaban, "Renormalization and localization expansions. II.
Expectation values of the 'fluctuation' measures", Commun. Math. Phys. 198 (1998)
1–45.
File `s002200050470.pdf` (45 pp.). Review
[`papers/P6-localization-II-fluctuation-expectations.md`](papers/P6-localization-II-fluctuation-expectations.md).
Status: obtained.
Renormalization on the small-field region (§2), the explicit inductive definition
of the large-field operators $\mathbb T_k$ and of the functions $\kappa_k$, $C$,
$K$ (§3), the action lower bounds (Prop 3.1, stated without proof) and the step
counter (Prop 3.2, cited to E10, which proves a different statement), the proofs
of P5 Thms 1 and 4, and the localization and cluster expansions for the
fluctuation integrals (§4), which also prove P4's deferred propositions. The
proof of Thm 4 contains an inequality that fails as printed (p. 22; roadmap
§4.3). The formalization takes §4 as I-8 and reconstructs §3 (LF-1, LF-2).
Priority: **essential**.

**P7** — T. Balaban, "The large field renormalization operation for classical
N-vector models", Commun. Math. Phys. 198 (1998) 493–534.
File `s002200050486.pdf` (42 pp.). Review
[`papers/P7-large-field-renormalization.md`](papers/P7-large-field-renormalization.md).
Status: obtained.
Constructs the large-field renormalization operation $R^{(k)}$ (an exact ratio
preserving the integral, (1.6)–(1.7)), solves the cancellation problem around a
Dirichlet background on a small box (Lemma 2.1), proves analyticity by averaging
over a coset of $O(N)$ (Lemma 3.1, described in words), exponentiates the new
terms by a polymer expansion, proves P5 Thm 2 and the whole-flow Theorem 5, and
does the last integration giving the generating functional (§4, (4.15)–(4.17)).
It is the O(N) adaptation of E9–E10 and the least detailed paper of the series.
The formalization takes Thm 2 (LF-4), Thm 5 (LF-7, method form) and §4 (LF-8,
which yields Root-F).
Priority: **essential**.

---

## 4. The O(N) series: correlation functions

**P9** — T. Balaban, M. O'Carroll, "Low temperature properties for correlation
functions in classical N-vector spin models", Commun. Math. Phys. 199 (1999)
493–520.
File `s002200050510.pdf` (28 pp.). Review
[`papers/P9-BOC-correlation-functions.md`](papers/P9-BOC-correlation-functions.md).
Status: obtained.
The endpoint: Theorem 1.1 (magnetization $|m-1|\le c\beta^{-1+\rho_1}$, $\sqrt\nu$
clustering uniform in $\beta$, and the Goldstone asymptotics of the transverse
two-point function as $\nu\downarrow0$), obtained by refining the source terms of
the effective action into one- and two-point parts (H.1)–(H.2), propagating them
(§3; the two-function truncated expansion Prop 3.1 is argued in two sentences),
and the exact Gaussian decomposition of $(-\Delta)^{-1}$ (4.17). The
thermodynamic limit is used, not proved. The formalization takes Thm 1.1 (hard
spins) as Root-C and §§2–4 as C-1–C-3.
Priority: **essential**.

**P8** — T. Balaban, M. O'Carroll, "A simple method for correlation functions via
the effective actions in the renormalization group framework", Ann. Physics 260
(1997) 1–8.
File `1-s2.0-S0003491697956906-main.pdf` (8 pp.). Review
[`papers/P8-BOC-simple-method.md`](papers/P8-BOC-simple-method.md).
Status: obtained.
A method paper for the two-dimensional Gross–Neveu model (fermionic, not O(N)),
deriving two-point functions from the last effective action of Gawedzki–Kupiainen's
RG by Gaussian decomposition and translation formulas. P9 does not cite it; it
illustrates the idea of P9 §4 in a simpler setting. The formalization takes
nothing from it.
Priority: **background**.

---

## 5. Green's functions and propagators

**E3** — T. Balaban, "Regularity and decay of lattice Green's functions", Commun.
Math. Phys. 89 (1983) 571–597.
File `BF01214744.pdf` (27 pp.). Review
[`papers/E3-lattice-green-functions.md`](papers/E3-lattice-green-functions.md).
Status: obtained.
Positivity, exponential decay and Hölder bounds for single-scale covariant
Neumann Laplacians with a block-projection term, uniform in the lattice spacing;
the unit-lattice propagators; the Gaussian lower bound (1.22) (= P4's "[2c]");
and §5, a fully proved general theorem on unit-lattice operators with the
random-walk representation (5.17) (= P4's "Sect. 5 of [3]", P3's "fifth section
of [2a]"). It does not cover Dirichlet conditions, variable or complex
potentials, or the multiscale averaging term, and it asserts the $j$-uniform
analytic strip of Lemma 2.4 without proof. The formalization takes the §5
theorem as the interface G-4 and uses the rest as a guide.
Priority: **essential**.

**E5** — T. Balaban, "Propagators and renormalization transformations for lattice
gauge theories. II", Commun. Math. Phys. 96 (1984) 223–250.
File `BF01240221.pdf` (28 pp.). Review
[`papers/E5-propagators-II.md`](papers/E5-propagators-II.md). Status: obtained.
The multiscale extension of E4: on nested domains with layer-wise block averages
(the geometry of P2's generating sets) it proves, for the scalar operator
$\Delta+Q'^*aQ'$, a random-walk expansion over mixed-scale cubes with the
multiscale distance and its summation Lemma 2.1, and weighted sup, gradient and
Hölder bounds (Prop 2.2, (2.67)); Section C is gauge-specific. It is P2's and P3's
"[2b]", cited with equation numbers offset by +10. It treats only $a=1$, no mass,
no complex potential, Dirichlet conditions only as a remark. The formalization
takes its geometry (generating sets, multiscale distance, Lemma 2.1) and the
architecture of G-3; the bounds themselves are re-proved (G-2).
Priority: **essential**.

**E4** — T. Balaban, "Propagators and renormalization transformations for lattice
gauge theories. I", Commun. Math. Phys. 95 (1984) 17–40.
File `BF01215753.pdf` (24 pp.). Review
[`papers/E4-propagators-I.md`](papers/E4-propagators-I.md). Status: obtained.
The Gaussian abelian gauge field under iterated block averaging: the gauge-fixed
propagator, the minimizer operator, $L^2$ and pointwise decay and Hölder bounds
(Props 1.1–1.2), proved by a sketched random-walk expansion. No P-paper cites it.
It contains the Woodbury representation used unattributed in P4 p. 710, the
multiscale decomposition (1.135) behind P9 (4.17), and Balaban's remark (p. 36)
that a Combes–Thomas conjugation is "probably the simplest proof" of exponential
decay — the route the roadmap adopts. The formalization takes only these patterns.
Priority: **background**.

**E2** — T. Balaban, "(Higgs)$_{2,3}$ quantum fields in a finite volume. I. A lower
bound", Commun. Math. Phys. 85 (1982) 603–626.
File `BF01403506.pdf` (24 pp.). Review
[`papers/E2-higgs-finite-volume-I.md`](papers/E2-higgs-finite-volume-I.md).
Status: obtained.
Balaban's first multiscale paper: a small-field lower bound on the vacuum energy
of the abelian Higgs model in $d=2,3$, most of whose propagator estimates are
stated without proof (proved later in E3). Its §2 defines the Gaussian block
transformation, its composition law, the free flow of $a_k$, and the layer
decomposition (2.43) of the propagator. P1 cites it as [2a] for these definitions,
which P1 restates; P4's bibliography entry [3] points to it but no P4 citation
uses it. The formalization takes nothing from it beyond a cross-check.
Priority: **background**.

---

## 6. Cluster expansions

**E11** — D. Brydges, "A short course on cluster expansions", in *Critical
Phenomena, Random Systems, Gauge Theories* (Les Houches 1984), Elsevier 1986,
pp. 129–183.
File `les_houches_84.pdf` (55 pp.). Review
[`papers/E11-brydges-cluster-expansions.md`](papers/E11-brydges-cluster-expansions.md).
Status: obtained.
Connected parts ($\psi'_c$, which is P6's $\rho^T$), the Battle–Federbush tree
formula, tree-graph inequalities, Mayer convergence, the polymer criterion (3.10)
and the bound on the polymer logarithm (Thm 3.4, pp. 141–142); §5 (decoupling,
grouping, animal counts) is the template for P6 §4 and P7's Mayer step. It is
cited by P5 [6], P6 [7], P7 [9]. It has no localized logarithm with decay and no
connectivity modulo a set, so the formalization replaces its theorems by one
Kotecký–Preiss-type theorem (roadmap §5) and uses E11 for definitions and the
decoupling technique.
Priority: **important** (read §§2–3, 5 and App. C).

**E1** — C. Cammarota, "Decay of correlations for infinite range interactions in
unbounded spin systems", Commun. Math. Phys. 85 (1982) 517–528.
File `BF01403502.pdf` (12 pp.). Review
[`papers/E1-cammarota-decay-correlations.md`](papers/E1-cammarota-decay-correlations.md).
Status: obtained.
Theorem 1 (high-temperature decay for unbounded spins) is irrelevant here.
Theorem 2 (p. 519) is an abstract polymer exponentiation with disjointness
compatibility and cardinality-graded smallness, proved via Penrose's tree bound
(cited). P6 and P7 cite it generically for exponentiating polymer expansions, E7
and E10 cite it as [26]; P4's entry [5] is never cited in P4's text. It is a
special case of Kotecký–Preiss without decay weights; the formalization takes
nothing from it directly.
Priority: **background**.

**E7** — T. Balaban, "Renormalization group approach to lattice gauge field
theories. II. Cluster expansions", Commun. Math. Phys. 116 (1988) 1–22.
File `BF01239022.pdf` (22 pp.). Review
[`papers/E7-RG-gauge-II-cluster-expansions.md`](papers/E7-RG-gauge-II-cluster-expansions.md).
Status: obtained.
The gauge-theory half of the "decoupling plus polymer" step completing E6:
localization of the fluctuation action by decoupling parameters, Mayer expansion,
polymer gas and exponentiation with tree-length decay (Lemma 3, (2.38)), with the
geometric inequalities (2.27), (2.30), (2.32), (2.36) stated without proof and the
convergence theorem cited. Only P1's bibliography lists it ([2e]). It is the
cleanest model for P3 Prop 4.3 together with P6 §4, and its list of geometric
inequalities fixes the companion lemmas of the roadmap's polymer theorem.
Priority: **important** (design reference).

---

## 7. Balaban's gauge-theory renormalization group (originals of the method)

**E6** — T. Balaban, "Renormalization group approach to lattice gauge field
theories. I. Generation of effective actions in a small field approximation and a
coupling constant renormalization in four dimensions", Commun. Math. Phys. 109
(1987) 249–301.
File `BF01215223.pdf` (53 pp.). Review
[`papers/E6-RG-gauge-I-small-field.md`](papers/E6-RG-gauge-I-small-field.md).
Status: obtained.
The YM$_4$ small-field inductive theorem (Thm 3, completed in E7), with the same
architecture as P1: background action plus localized, analytic, invariant terms
with tree-length decay, and a Ward identity fixing the marginal coupling. P1
cites it as [2d] for the form of the effective action, the localization format
and the lattice Taylor formula (E6 (4.30) = P1 (3.97)), all restated in P1. Its
Thm 3 fixes the order "$\kappa$ first, then $M\ge M(\kappa)$". The formalization
takes no theorem from it; it is the reference for what an O(N) formalization
shares with YM (review §10, side-by-side table).
Priority: **important**.

**E8** — T. Balaban, "Convergent renormalization expansions for lattice gauge
theories", Commun. Math. Phys. 119 (1988) 243–285.
File `BF01217741.pdf` (43 pp.). Review
[`papers/E8-convergent-renormalization-expansions.md`](papers/E8-convergent-renormalization-expansions.md).
Status: obtained.
The YM$_4$ inductive description that keeps all large-field regions: a complete
first step with large fields (§1), and the representation of the effective density
as a sum over domain sequences with large-field operators factorized over
components and levels ((2.18)–(2.22)); beyond the first step the operators are
"left undefined, only their basic general properties are formulated" (p. 254).
There is no $\kappa$, $C$, $K$ or $R$ (assumed, deferred to E9–E10). P5 [5b] and
P6 [6b] cite it only in their bibliographies. The formalization takes the
architecture of $\mathbb T_k$ and the structure of the base case.
Priority: **important**.

**E9** — T. Balaban, "Large field renormalization. I. The basic step of the R
operation", Commun. Math. Phys. 122 (1989) 175–202.
File `BF01257412.pdf` (28 pp.). Review
[`papers/E9-large-field-renormalization-I.md`](papers/E9-large-field-renormalization-I.md).
Status: obtained.
The first half of the gauge $R$ operation: the class of small rectangular
large-field components with no new large fields for $N$ steps (conditions (i),
(ii), p. 177), the undoing of those steps, the identities (1.29), (1.89) showing
that new restrictions imply the old ones (proved in full), and the normalized
ratio $R'$ (1.100)–(1.102). The bundle cites no specific item. P7 §§1–2 adapt it;
its inequality chains are the worked template for reconstructing P7 Lemma 2.5,
but its constants do not transfer (it needs $p_1<p_0$ because the gauge coupling
runs logarithmically).
Priority: **background**.

**E10** — T. Balaban, "Large field renormalization. II. Localization,
exponentiation, and bounds for the R operation", Commun. Math. Phys. 122 (1989)
355–392.
File `BF01238433.pdf` (38 pp.). Review
[`papers/E10-large-field-renormalization-II.md`](papers/E10-large-field-renormalization-II.md).
Status: obtained.
The completion of the gauge $R$ operation: cancellation of the main actions,
re-localization around the new background, the operators $\mathbf T'_k$ with
positivity under complex perturbations, the step-counting induction (1.80)–(1.89)
(pp. 383–387, the only complete proof of step counting in the library, for a
geometric counter), and a polymer expansion with connectivity modulo the
remaining large-field regions with written activity bounds. P6 cites it for the
functions $\kappa_k$ and for Prop 3.2, which E10 does not state. The formalization
takes the counting argument (rewritten for P6's counter and the geometric running
of $\beta_k$, roadmap §4.3) and the polymer bookkeeping.
Priority: **essential**.

---

## 8. Dimock's exposition of Balaban's method ($\phi^4_3$)

**D1** — J. Dimock, "The renormalization group according to Balaban I. Small
fields", Rev. Math. Phys. 25 (2013) 1330010; arXiv:1108.1335.
File `Dimock-I-arXiv-1108.1335.pdf` (52 pp.). Review
[`papers/D1-dimock-I-small-fields.md`](papers/D1-dimock-I-small-fields.md).
Status: obtained.
A nearly self-contained proof of one RG step (Thm 14) and of the flow (Thm 24) for
$\phi^4_3$ with all fields small. For O(N) it supplies a written-out Gaussian
skeleton (free flow, covariance square root, random-walk expansions as Neumann
series, decoupling parameters, Banach spaces of polymer functionals), a complete
Mayer/tree-graph cluster expansion except the Penrose bound (Thm 27), and a
Combes–Thomas $L^2$ decay proof valid for Dirichlet and mixed conditions
(Lemma 30) — the model for G-2's first step. Pointwise and Hölder bounds are
sketched or cited to E3; nothing on constrained minimizers, Ward identities or
large fields.
Priority: **important**.

**D2** — J. Dimock, "The renormalization group according to Balaban II. Large
fields", J. Math. Phys. 54 (2013); arXiv:1212.5562.
File `Dimock-II-arXiv-1212.5562.pdf` (94 pp.). Review
[`papers/D2-dimock-II-large-fields.md`](papers/D2-dimock-II-large-fields.md).
Status: obtained.
A complete large-field induction (Thm 3.1): nested regions with logarithmic
buffers, three large-field families per step, unintegrated large-field measures,
boundary terms, all definitions in one place; an explicit base case (§3.4); a
multiscale Dirichlet Green's function (Thm 2.2, sketched); a cluster expansion
with holes (Thm F.1, the only stated version modulo $\Omega^c$, sketched); and a
dictionary to P5–P7 (p. 84). It has no step counter, no admissibility and no $R$
operation ("not necessary for this model", p. 31). It is the best template for
writing P5's hypotheses and the base case.
Priority: **essential** (for the large-field reconstruction).

**D3** — J. Dimock, "The renormalization group according to Balaban III.
Convergence", Ann. Henri Poincaré 15 (2014) 2133–2175; arXiv:1304.0705.
File `Dimock-III-arXiv-1304.0705.pdf` (37 pp.). Review
[`papers/D3-dimock-III-convergence.md`](papers/D3-dimock-III-convergence.md).
Status: obtained.
The last step with a massive propagator and a one-pass summation over all
large-field histories (volume bound Lemma 14, small factor Lemma 15,
exponentiation Thm 2). The summation works because few steps remain after a
large field appears (D3 (205)) — the analogue of the O(N) regime $k\ge k_0$, and
the reason $R$ is needed for O(N) before $k_0$. It is the model for P6 Thm 4 and
P7 §4; it gives no global order of constants.
Priority: **important**.

---

## 9. Not in the library

Recommended to obtain (roadmap §10.1): Kotecký–Preiss, CMP 103 (1986) 491–498
(hypothesis form of the polymer theorem); Ueltschi, Moscow Math. J. 4 (2004) and
Fernández–Procacci, CMP 274 (2007) (proofs of it); Abdesselam–Rivasseau, Rev.
Math. Phys. 9 (1997) (P7 [13]); Balaban, CMP 102 (1985) 255–275 (YM$_3$
ultraviolet stability; the prototype of P6's large-field factors). Background
only: Balaban's Higgs II and III (CMP 86 (1982) 555; CMP 88 (1983) 411),
CMP 98, 99, 102:277 (gauge analogues of P2, P3, E3, E5), Balaban–Imbrie–Jaffe
(CMP 97, 114), Brydges–Dimock–Hurd, Gawedzki–Kupiainen CMP 102 (P8 only),
Fröhlich–Pfister CMP 89 (1983) 303, Fröhlich–Simon–Spencer CMP 50 (1976) 79,
Parisi, *Statistical Field Theory*.

---

## 10. Suggested reading path for a new collaborator

1. `BIG_PICTURE.md` §§1–4, then **P0** (18 pages) for Balaban's own overview.
2. **D1** §§1–3 for the Gaussian skeleton of the method in a simpler model.
3. The small-field O(N) theory: **P1** §§1–2 (setup, hypotheses) and §3 (the
   renormalization analysis); **P2** §§1, 3; **P3** §§2 and 4; **P4** §§1–2, 5.
4. Green's functions: `FORMALIZATION_ROADMAP.md` §3.4, then **E3** §§2 and 5 and
   **D1** App. D–E; consult **E5** §B for the multiscale geometry.
5. Large fields: **D2** §3 (the bookkeeping written cleanly), **P5** §1, **P6**
   §3, **E10** pp. 380–387 (the step counter), **P7** §§1–3, **D3** §3; then
   `FORMALIZATION_ROADMAP.md` §4.
6. Cluster expansions: **E11** §§2–3 and 5, **D1** App. B, then
   `FORMALIZATION_ROADMAP.md` §5; **P6** §4 for the bundle's use.
7. Correlation functions: **P9** §§1–2 and 4, with **P7** §4.
8. As needed: **E6**, **E7**, **E8**, **E9** (Balaban's gauge originals and the
   comparison with YM), **E2**, **E4**, **E1**, **P8**.
