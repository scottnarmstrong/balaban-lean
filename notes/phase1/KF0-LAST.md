# KF0-LAST — the last integral at the bare high-mass scale

**PROVED (verdict).** P7 §4 proves a localized logarithm for an input density satisfying P5 H1–H5 and H7. Its printed argument does not identify the constrained-sphere bare density with that input or establish the needed first component bound at \(k_f=0\). The bare real reserve, pointwise exterior analyticity, and ordinary F.1 walks leave a weighted exterior-influence estimate open.

**PROVED (scope and frozen evidence).** This focused source audit uses P7 s002200050486.pdf SHA256 c48e08dd439878a0245cceb6e6aead787a8ce7671865f6360c8464a7e579d2e9, P5 s002200050433 (1).pdf SHA256 b3f0ef3491fc63b3988768893c1452b4bd1458a5f3e408e6af6000a555fd9a0f, and Lean commit 6f2f0b86383f6deeb22764872ed7ef3a131f4ed8. Page numbers below are printed numbers. The prescribed output is this note; no paper or Lean source was edited.

**PROVED (reading rule).** PROVED marks a checked paper statement or an elementary mathematical deduction, not a newly formalized theorem. PROVED CONDITIONAL ON names its unproved premise. OPEN marks a missing proof or source bridge. REFUTED marks a proposed implication disproved by the cited definition or counterexample.

## 1. What P7 actually integrates

**PROVED (input, p. 529).** P7 begins §4 at the first \(k=k_f\) with \(\nu_k>7L^{-2}/8\); its words are that \(\rho_k\) “is given by the formula (1.1) [5]” and satisfies “(H.1)–(H.5), (H.7) [5].” Formula (4.1) integrates every remaining \(\psi_k\) and sums the already present \(Z_k\). The nearby text uses the inherited \(\chi_k(W_k)\) to infer \(|\psi_k-h|<(5L+3)\delta_k\) on its domain.

**PROVED (which partition, pp. 529–530).** P7 expressly omits the P5 decomposition (2.6), hence \(\Omega_{k+1}=\Omega'_{k+1}\) by P5 (2.9): no fresh \(P_{k+1}\) from that test. It retains a modified P5 (2.14) partition on the layer \(\Omega_{k+1}^{\sim3}\cap(\Omega_{k+1}^{c})^{\sim3}\), producing failed background tests of \(Q\)-type. The subsequent P5 (2.42)–(2.43) fluctuation partition produces \(R\)-type failed regions. Thus mass does not declare the whole lattice small field.

**PROVED (massive saddle, p. 530).** The modified integral (4.2) uses the variational problem (4.3); its positive mass permits P2 Proposition 4.1 without the averaging mass. Equations (4.4)–(4.6) construct the background \(h+\delta\phi_{k,0}\), and P3 decay controls its response away from \(\Omega_{k+1}^{c}\). The changed P5 (2.15)–(2.16) replace the earlier \(T^{(k)}\) by direct \(d\psi_k\) and omit the averaging quadratic.

**PROVED (last fluctuation, p. 531).** The modified P5 (2.47)–(2.48) yields main action (4.7). P5 §3 gives its (3.18); P7 then uses part of P6 §2, with no further action renormalization and no P6 (2.1) partition, so \(S_{k+1}=\varnothing\). Equations (4.8)–(4.9) give new \(E,F,R\), boundary terms and a scalar integration operator \(T'_{k+1}\), summed over fresh \(Z_{k+1}\) and admissible indices.

**PROVED (fresh-component estimate, p. 531).** P7 says \(T'_{k+1}\) is an integration independent of any remaining spin and satisfies the analogue of P5 (1.26). Its (4.10) uses P5 (1.31) with \(\ell=1\): summing indices gives \(|T'_{k+1}(Z)F|\le e^{-p_2(\beta_k)-H_k|Z|}\sup\chi|F|\). This is the last-step analogue for fresh regions; the paper does not derive it from the bare unit-sphere measure in §4.

**PROVED (final gas, p. 532).** Equation (4.11) completes the \(E,F,R\) terms to the whole torus and leaves a gas of fresh components and boundary links. Equation (4.12) combines each \(-p_2-H_k|Z|\) with vacuum cost \(E_{k+1,0}|Z|\), boundary cost of order \(\epsilon^{-2}B_0K_0M^{-d}|Z|\), and decaying link factors. Unlike §3, these components can have arbitrary size, so P7 explicitly spends the \(H_k|Z|\) reserve.

**PROVED (local exponent, pp. 532–533).** With \(H_0\) large, (4.13) bounds each connected activity by \(\epsilon^{-2}e^{-p_2(\beta_k)}e^{-(3\kappa/2-2\kappa_0-1)d_{k+1}(X)}\); every term contains a fresh component. The Mayer expansion is exponentiated in (4.14) to \(P^{(k+1)}(h,g)=\sum_XP^{(k+1)}(X;h,g)\), with the stated bound of order \(\tfrac12\beta_k^{-m-1}e^{-\kappa d_{k+1}(X)}\).

**PROVED (output, p. 533).** Equation (4.15) gives the full integral as \(\exp[-E_{k+1,0}|T|+F_{k+1,0}(h,g)+R^{(k+1)}(h,g)]\), then as an exponential of \(F_{k+1,0}\) plus the integral of the \(g\)-derivative of \(R^{(k+1)}(h,tg)\). This is a localized logarithm, contingent on the density hypotheses and component estimate.

**PROVED (source and normalization).** Source locality and analyticity enter the P5/P6 \(F,R\) expansions, survive the boundary Mayer summation, and give (4.17), \(\langle g,h\rangle+\sum_{j=1}^{k}\langle g,M^{(j)}\rangle+\sum_{n=0}^{m}\langle g,M_n^{(k+1)}\rangle\). P7 uses (4.16), \(\int\rho_k(g=0)=1\), citing P1 (1.12) and P5 (1.43). Our frozen partitionFunction is unnormalized, so comparison uses \(\log Z(g)-\log Z(0)\) and needs an exact measure-normalization bridge.

## 2. Is the bare \(k=0\) density already in the P5 class?

**REFUTED (trivial \(Z_0=\varnothing\) H1).** P5 H1 (1.1), p. 488, includes \(\chi_0(Z_0^c)\). P5 (1.18)–(1.19), p. 492, impose small-field tests, including the \(h\)-proximity condition in the massive regime. A unit spin antipodal to \(h\) fails that condition for small \(\delta_0\); hence \(\chi_0(T)\ne1\) on the entire sphere configuration space. The single empty-region term cannot equal the bare density.

**OPEN (H1 physical base).** An exact sum over nonempty \(Z_0\) could represent the omitted configurations, but it needs an explicit first large-field density and support partition with all crossing bonds. The landed partitionFunction_eq_sum_kf0Sector and kf0Sector_iterated give an exact physical block sector sum; they do not identify its sectors with P5 (1.1), whose regions and tests differ.

**PROVED CONDITIONAL ON an exact physical H1 sector identity (H2).** At \(k=0\), the sums over inherited \(\mathcal E^{(j)}\) in P5 (1.6)–(1.9), pp. 489–490, are empty, so their zero values and \(E^{(0)}=0\) are algebraic. Matching \(-\beta_0A_0^*\) to every restricted bare action still requires the chart/measure identity and an exact allocation of crossing bonds to the component operator or boundary term.

**PROVED CONDITIONAL ON the same identity (H3).** P5 (1.10)–(1.13), p. 490, have leading source \(\langle g,\phi_0\rangle\), with no inherited \(M^{(j)}\) at \(k=0\). This matches the bare source once \(\phi_0\) is the actual spin on each sector and the source on removed sites is carried in its integral operator.

**PROVED (H4 algebraic zero).** P5 p. 491 allows \(R_n^{(0)}=0\): the source analyticity, localization and symmetry requirements are vacuous for this choice. This does not make H1 or H5 true.

**OPEN (H5 first operator).** P5 (1.21)–(1.31), pp. 493–495, require the exact large-field density as a sum of nonnegative component operators with support, factorization and the small estimate (1.31). A zero operator loses physical bad sectors, and a bare real Peierls sup bound does not prove factorization, exterior analyticity or (1.31) with P5's \(p_2,H_0\) and geometry. This is the input used in P7 (4.10).

**PROVED CONDITIONAL ON physical component construction (H6).** H6, P5 (1.32), p. 496, concerns a positive remaining-step counter for components when \(k\le k_0\). P7 §4 lists H1–H5 and H7, so H6 is not a direct last-integral premise. It is vacuous for a genuinely empty \(Z_0\), which already fails H1 for the full bare density; a nonempty physical sector needs its own counter if the full P5 class is claimed.

**OPEN (H7 boundary ledger).** P5 (1.36)–(1.39), p. 497, require local analytic boundary terms with a fixed \(B_0e^{-\kappa d}\) bound. Taking these terms zero is valid only after every crossing bond and source term has been placed exactly in H2/H5. The bare sector identity keeps crossing bonds, but their P5 boundary/operator allocation and bound have not been established.

**OPEN (sphere-to-density bridge).** P1's \(\lambda=\infty\) constraint is formally a delta-function limit of the \(\lambda<\infty\) density; the frozen model integrates normalized surface measure. An equality between that measure and P7's \(d\psi_0\,\rho_0\), including its \(g=0\) normalization and all sector Jacobians, is a separate obligation. It does not follow from writing a delta symbol.

**REFUTED (zero witness as physical base).** BaseSmallFieldInput, baseStepData_of_input, and baseStepData_nonempty are landed constructions. LargeField/Base/Prop279Counter.lean explicitly shows that their zero remainder/zero boundary witness has \(K_0\equiv0\) while the exact first retained-factor kernel is strictly positive. Thus inhabitation of this record is not a physical witness for the bare density or P5 H5.

**PROVED (class index).** IsRep2 is present in LargeField/Def7v2Class.lean; the campaign's hatStepK setting assumes \(1\le k\). Their existing positive-scale use does not supply the missing \(k=0\) identification. A physical witness would encode the actual sphere sector integral, nonzero first component kernel, normalization, locality/analyticity, crossing-bond ledger, and the stated bound, then connect it to H1–H5/H7.

**OPEN (scope of P7's claim).** P7 §4 does not state an explicit exclusion \(k_f=0\), so I cannot report one. Its argument is conditional on a scale-\(k\) P5 density; the page does not show that the bare constrained measure has this form. The issue is an omitted base verification, not a demonstrated restriction \(k_f\ge1\).

**OPEN (author question).** Does §4 include \(k_f=0\) for \(\lambda=\infty\) with normalized sphere measure? If so, where are H1–H5/H7 and P5 (1.31) verified for \(\rho_0\), given that \(\chi_0\) is not identically one? Is the first \(T'_1\) reserve proved independently of an inherited \(T_0\)?

**OPEN (last-step lemma L0: physical input).** Identify the bare sphere integral with P5 (1.1) and verify H1–H5/H7, including its first kernel and (1.31). Status: OPEN; the LANDED block split is an exact alternative sector identity, not this identification.

**PROVED CONDITIONAL ON L0 (last-step lemma L1: massive background).** P7 (4.3)–(4.7) supplies the paper argument. Status: COVERED IN PART by the one-scale KF0BoundarySquare, KF0MeanShell and KF0CollarBudget packages, which address the bare quadratic and collar estimates; they do not prove the P5 background-field statement. These packages were assigned in KF0-INFL.md and are not marked LANDED here.

**PROVED CONDITIONAL ON L0 (last-step lemma L2: direct fluctuation).** P7 invokes P5 (2.47)–(2.48), P5 (3.18) and P6 §2 to obtain (4.9). Status: COVERED IN PART by KF0ConditionalSector, KF0LoopOccupancy, KF0HoleWalk and ordinary F.1 work; exact bare physical identification and new bad-sector support remain OPEN.

**OPEN (last-step lemma L3: component reserve).** Show a physical \(T'_1\) satisfies the full (4.10) bound in its actual geometry. Status: OPEN; the Round-40 real sup estimate supplies a first Peierls bound, while P7 cites P5 (1.31) for (4.10). The R-lane's inherited-component (3.7)–(3.10) and Lemma 3.1 are COVERED THERE only under their own positive-scale premises.

**PROVED CONDITIONAL ON L0–L3 and local boundary estimates (last-step lemma L4: gas).** P7 (4.11)–(4.15) supplies the component summation and localized logarithm, using \(H_0\log\beta_k\) to pay arbitrarily large \(Z\). Status: ABSTRACT MACHINERY LANDED in gas_pe and pe_blockTorus_frozen; the physical activity and exact lift remain OPEN.

**PROVED CONDITIONAL ON L4 and normalization (last-step lemma L5: source).** P7 (4.16)–(4.17) supplies its normalized source representation. Status: PARTIAL ROOT-F BRIDGE LANDED in rootF_kf0_partial_of_oneScaleInput; the sphere-to-\(\rho_0\) normalization and physical OneScalePhysicalLogData remain OPEN.

## 3. P7 Lemma 3.1 and a bare analytic statement

**PROVED (lemma statement, p. 525).** P7 Lemma 3.1 says the kernel of (3.7), after removing its leading characteristic functions, extends analytically in \((\psi_k,h),g\) to \(\Xi_k^c(U;1,\epsilon_k)\times\{g|_Z:\|g\|_{\ell^1(Z)}<1\}\). On that space the operator obeys (3.10) with integration over \(\psi_k|_Z\) replaced by a supremum. It concerns the inherited second-kind operator of §3, not \(T'_{k+1}\) from §4.

**PROVED (rotation, pp. 520–521).** The remaining moving hard test depends on an exterior unit vector \(\psi_0\). P7 rotates all internal \(\psi_{k_1}\) and inherited operator variables by \(R\in O(N)\) with \(Re_1=\psi_0\); orthogonal invariance of their measures and hard tests replaces \(\psi_0\) by \(e_1\) inside those tests. Terms involving \(h,g\) need not be invariant; they move into analytic exponentials.

**PROVED (globalization, p. 521).** The choices \(R\) are the coset \(O_{\psi_0}(N)=\{R:Re_1=\psi_0\}\). Averaging over this coset, normalized by the stabilizer volume, gives a global expression; a local analytic section \(R(\psi_0)\) proves analyticity in each chart. For complex perturbations of size \(<2\epsilon_k\), P7 bounds the resulting matrix norm by \(e^{O(\epsilon_k)}<3/2\).

**PROVED (complex bound, pp. 521–525).** P7 expands the analytic fluctuation fields in the exterior perturbation: (3.11) bounds \(\delta\psi\), (3.12)–(3.15) bound \(\delta\phi\), and (3.16) separates a nonnegative real action from a complex remainder. Equation (3.18) bounds that remainder by \(O(\beta^{-1/4})\le1\), yielding (3.19), \(|e^{-\beta_k\delta A_k^*}|<e^{O(1)}\). The subsequent mass estimate explicitly uses \(\beta_k\nu_k\le1\), so this proof cannot be inserted verbatim at a high-mass \(k=0\) with \(\beta\nu\gg1\).

**REFUTED (unmodified rotation for the bare cutoff).** The bare condition \(|\phi_x-h|<\delta_\beta\) is invariant under simultaneous rotation of \(\phi,h\), but with fixed \(h\) it changes when only integrated spins rotate. A rotation fixing \(h\) cannot send an arbitrary exterior spin to \(e_1\). Consequently P7's particular removal of a moving cutoff is not an automatic lemma for our bare site cutoff; its positive-scale tests and low-mass construction differ.

**PROVED (bare fixed-core lemma).** Fix a finite dressed core \(D\), fixed amplitude bins and hard indicators depending only on spins \(q_D\), and real exterior boundary spins \(\xi\in(S^{N-1})^{\partial D}\). Put \(T_D(\zeta;g)=\int_{q_D}1_{\rm bins}1_{\rm internal\ good}\exp[-\beta H_D(q_D\mid\zeta)+\langle g_D,q_D\rangle]\,d\sigma_D\), assigning each crossing bond once. If \(H_D\) is the bare quadratic mass plus internal and crossing bonds, then \(T_D\) is entire in the ambient complex coordinates \(\zeta\) and \(g_D\), since the integration domain is compact and fixed.

**PROVED (bare complex bound).** Let \(n_\partial\) count crossing bonds and \(\max_{y\in\partial D}|\zeta_y-\xi_y|\le r\). If selected disjoint core blocks have amplitude lower bounds \(\alpha_Q\), expansion of \(|q_x-\zeta_y|^2\) as its polynomial continuation gives the following estimate.

**PROVED (bare bound formula).** \( |T_D(\zeta;g)|\le e^{\|\Re g_D\|_1+\beta n_\partial(2r+r^2/2)}\exp[-(\beta\nu/2)\sum_Q\alpha_Q^2] \), with harmless convention changes in the coefficient of \(r^2\). The proof drops nonnegative real mass/bonds at \(\xi\), pays the perturbation for each crossing bond, and integrates a set of sphere measure at most one. For an analytic test function \(F\), multiply the right side by its supremum over the same compact integration set.

**PROVED (size of useful domain).** The lemma is entire, but retaining an \(O(1)\) perturbation cost only gives \(r\lesssim[\beta(n_\partial+1)]^{-1}\). Spending a \(c\log^2\beta\) component reserve permits at most \(r\lesssim\log^2\beta/[\beta(n_\partial+1)]\) without another estimate. This radius depends on the component and may be too small for P6/P7 Cauchy bounds on a uniform exterior-field domain.

**OPEN (Gaussian-variable transfer).** At fixed good set \(G\), composing \(\xi\) with a charted conditional mean/covariance map \(\Phi^+(\beta^{-1/2}C_G\psi_G)\) is locally analytic wherever that chart is analytic. Its useful radius and bound need uniform control of \(C_G\), the chart and the domain dependence. The exterior hard factor \(\chi_G(\xi)\) itself has no holomorphic continuation across its threshold; it must remain outside the analytic operator on a fixed product reference.

## 4. Exact remaining route to the physical logarithm

**PROVED (landed real starting points).** partitionFunction_eq_sum_kf0Sector and kf0Sector_iterated give the hard physical sector identity. kwOp_inv_mulVec_decay, kw_logdet_eq, and kf0CR_torus_eq are landed killed-walk, determinant and torus-lift tools. kf0SeriesBound_summable and kf0SeriesTerm_hasSum give ordinary-series majorants; they do not themselves identify every F.1 coefficient with the physical conditional sector.

**PROVED CONDITIONAL ON the Round-40 real reserve.** For a fixed bad component and fixed exterior spins, its Peierls charge and normalization loss yield a real bound of the form \(e^{-c\log^2(\beta a)|B|-H_\beta|S_B|}\|F\|_\infty\), with \(H_\beta\) and geometry as specified in KF0-P7.md. The preceding bare complex lemma extends that fixed-core integral pointwise, with the explicit radius loss just stated. Neither result is a P5 (1.31) class estimate.

**OPEN (first linked estimate).** Prove a weighted cut/difference estimate for \(T_D\)'s dependence on exterior good spins or the fixed-\(G\) Gaussian field, uniformly in amplitude bins, \(B\), torus, source, and regulator. It must charge each connected support by its core reserve or a summable walk factor, while keeping the hard exterior product fixed. Pointwise holomorphy and the real sup bound alone give no support-size weighted sum.

**OPEN (exact regrouping).** Integrate/sum all bad-core bins and collars with every crossing bond, Jacobian, source term, conditional determinant and hole walk present; obtain an exact identity on one product Gaussian reference with local analytic \(U(Y;g)\). The required estimate is the IntegratedHardCollarPotential target of KF0-INFL.md: \(\sup_Q\sum_{Y\ni Q}e^{\kappa_0|Y|}\sup_{\|g\|_1<1}|U(Y;g)|\le C[B_{\rm ord}(\beta)+e^{-c\log^2(\beta a)}]\). This remains OPEN even after (a) real reserve, (b) fixed-core analyticity, and (c) ordinary F.1 majorants.

**PROVED CONDITIONAL ON the exact small \(U\) estimate.** P6 (4.39)–(4.52), pp. 36–39, inserts parameters on localized analytic interactions, keeps the hard product cutoff fixed, uses Cauchy bounds and connected cancellation, controls normalization, then obtains a localized polymer potential. These are the paper's template; a Lean application still needs the literal product-reference, convergence and numeric norm hypotheses checked.

**OPEN (post-expansion physical tasks).** Establish \(Z(g)/Z(0)\ne0\) on the full complex \(\ell^1\) source ball, identify the connected logarithm with the sphere integral, bound its root norm uniformly in \(\nu\in[\nu_*,1]\) and torus size, prove source locality and the exact nonwinding lift for integrated heavy terms, then remove walk/chart regulators termwise. Ordinary kf0CR_torus_eq covers a walk identity, not the heavy gas lift.

**PROVED CONDITIONAL ON physical OneScalePhysicalLogData.** The landed rootF_kf0_partial_of_oneScaleInput consumes a one-scale input and gives the high-mass partial Root-F conclusion. gas_pe and pe_blockTorus_frozen are landed abstract gas bounds available after a physical activity satisfying their precise premises exists. They do not construct that activity or prove the physical nonvacuity field.

**OPEN (bounded Lean package A, at most 300 new lines each).** Formalize the fixed-core entire integral and explicit complex-radius bound in KF0CoreAnalytic, after the current KF0ConditionalSector and KF0BoundarySquare work identifies its physical kernel. A second KF0CoreDifference package should state the weighted cut bound with its regulator and source quantifiers; it is a research proof task, not an immediate formal consequence.

**OPEN (bounded Lean package B, at most 300 new lines each).** Split physical exact regrouping, the weighted IntegratedHardCollarPotential proof, full-source normalization, and integrated-heavy nonwinding lift into separate files only once their mathematical estimates are supplied. No package may inhabit the desired interface by a zero kernel or an assumption equivalent to its conclusion.

**PROVED CONDITIONAL ON package B (bounded Lean package C).** A KF0ConnectedPotential file can specialize the P6 parameter/normalization argument, KF0DirectGas can connect the resulting activities to gas_pe or pe_blockTorus_frozen, and KF0RootPartialBridge can feed rootF_kf0_partial_of_oneScaleInput; keep each file at most 300 new lines. The current state supports this as a dependency plan, not a claimed completed proof.

**PROVED (adversarial check and closeout).** I tried to refute the base gap by setting \(Z_0=\varnothing\), using P7's fresh-region (4.10), or using baseStepData_nonempty: respectively \(\chi_0\ne1\), (4.10) invokes P5 (1.31), and Prop279Counter.lean separates the zero witness from the physical kernel. I also tried to refute the analytic gap by placing all hard tests inside a fixed-core integral; that succeeds for pointwise analyticity but leaves the radius and weighted exterior-influence bound. No claim here audits every P5/P6 proof line, and no physical \(k_f=0\) closure is claimed.
