# Round 39: one-scale high-mass route and linked estimate

**PROVED (scope).** This note concerns the high-mass branch only: $d\ge3$, $N\ge2$, $\nu_*(L)=7/(8L^2)\le\nu\le1$, finite admissible tori, and $\|g\|_1<1$. “PROVED” below means a mathematical statement or an exact source observation, not a new Lean theorem. The repository `/home/scott/Balaban` was read only.

**OPEN (verdict).** Build on **(A), hard physical sectors**, with a product-Gaussian localization of the good integral and a separate integrated treatment of bad cores and their collars. L38.11 remains a research estimate. Neither smoothing, the exponential chart, nor P5/P6 supplies its proof. Do not start the conditional Lean closure as though the estimate had landed.

**PROVED (why A).** `KF0BlockSplit.lean` already gives the exact physical sector sum and keeps every crossing bond. H37.1 gives a retained positive fraction of the boundary charge; L38.2–L38.4 specify collars whose numerical cost fits that charge. This is more information than the full-torus representation (B) exposes before a large-field split.

**REFUTED (B as an immediate solution).** L38.7 is an exact identity for every finite walk cutoff, but its chart indicator, sheet sum, compensator $Q_R$, normalization, and long-range dependence all require a new uniform connected-family estimate. A smoother chart alone does not turn L38.8–L38.9 into L38.11.

## 1. Smooth physical block partition

**PROVED (algebra).** For a smooth scalar cutoff $f=1$ on $[0,1]$, $f=0$ on $[4,\infty)$, $0\le f\le1$, put $\chi_Q^{\rm sm}=\prod_{x\in Q}f(|\phi_x-h|^2/\delta_\beta^2)$. Then $\prod_Q(\chi_Q^{\rm sm}+1-\chi_Q^{\rm sm})=1$. The proof of `partitionFunction_eq_sum_kf0Sector` adapts with new definitions and weighted sectors; `energy_split`, `goodEnergy_expand`, and `crossing_expand` are unchanged identities.

**PROVED (support and charge).** A good factor can be nonzero only when every spin of its block lies within $2\delta_\beta$ of $h$. A bad factor can be nonzero only when at least one spin is at distance at least $\delta_\beta$. Thus the same selected-site mass lower bound $\beta\nu\delta_\beta^2/2$ holds on the support of each selected bad block. It is a support implication, not the hard `badSet` equality.

**PROVED (specific Lean change).** `chi_eq_zero_or_one`, `mem_badSet`, `sectorWeight_eq_ite`, `measurableSet_badSet_eq`, `apriori_univ_eq_sum_badSet`, `measure_badSet_eq_pos`, and the present `exp_neg_energy_le_peierls` state hard-sector facts. A smooth version needs renamed weighted-sector statements and a support-based Peierls lemma. `kf0Sector_iterated` survives after rebuilding `chi_glue_of_mem`, `chi_glue_of_not_mem`, and `sectorWeight_glue` for the smooth local weights.

**PROVED (small chart).** On a nonzero smooth good factor the hemisphere Jacobian and action are smooth at $|\phi-h|\le2\delta_\beta\ll1$. Smooth extension by zero can remove the chart-boundary singularity from that *fixed-sector good factor*. The bad-spin integration remains on the compact sphere.

**REFUTED (automatic BKAR).** Smoothness of $f$ alone does not establish `BKARContDiff` for the scalar forest interpolation. `External/BKAR/Smoothness.lean` requires global $C^\infty$ in the edge variables; a covariance interpolation must remain positive, be extended smoothly off its positive domain, and include its determinant and mean. A pointwise square-root interpolation needs uniform control of every mixed derivative of the cutoff and the chart.

**PROVED (analyticity distinction).** A compactly supported nonconstant $C^\infty$ cutoff has no holomorphic extension across its transition and zero regions. P6's Cauchy estimates are applied to analytic localized potentials while its hard cutoff stays fixed in the product reference. Replacing that cutoff by a moving smooth cutoff does not preserve this analytic step.

**REFUTED (claimed one-edge factor).** One Gaussian integration by parts can put two field derivatives on $f$, costing roughly $(\beta\delta_\beta^2)^{-1}\sim(\log\beta)^{-2}$ times a covariance link. It does not follow that each derivative gives this factor: derivatives can hit distinct cutoffs, the chart, determinant, and mean; repeated hits have cutoff derivative constants depending on order. A nearest-neighbor link has no $q^s$ block-crossing gain.

**OPEN (precise first smooth estimate).** For each fixed bad set $B$, prove a positive-covariance forest interpolation and a bound for every tree $T$ on its mixed derivative of the *normalized, fully integrated* sector function, schematically
$$\left|\partial_T F_B(t;g)\right|\le C^{|S|}e^{-c\log^2(\beta a)|B|}\prod_{e\in T}w(e),\qquad \sup_Q\sum_{Q'}e^{\kappa_0|\operatorname{path}(Q,Q')|}w(Q,Q')<1,$$
with collars, determinant loops, hole walks, source, and all derivative orders included. No established inequality here supplies this; its displayed rate is a target, not a theorem.

**OPEN (necessary vertex refinement).** A usable version must assign each ordinary vertex a factor $O(B_{\rm ord})$, each bad-core vertex its retained Peierls factor $e^{-c\log^2(\beta a)}$, and each edge a summable covariance or walk weight. The derivative bound must be uniform in vertex degree, tree size, regulator, and complex source. The one-edge estimate alone is insufficient for that product.

**OPEN (mean near a core).** L38.3 makes the shifted mean small only *outside* the amplitude-dependent collars. A cutoff derivative inside a collar is therefore not automatically a rare centered-Gaussian event. L38.4 can pay an established integrated collar loss, but does not establish it.

**OPEN (smooth-route verdict).** The smooth partition is a useful optional auxiliary lemma for a future forest proof. It changes the landed hard-sector API and leaves the integrated tree estimate open, so it is not the selected formalization route now.

## 2. Exponential chart

**PROVED (geometry).** For $\theta\in h^\perp$, $r=|\theta|<\pi$, $\Phi(\theta)=\cos r\,h+\operatorname{sinc}(r)\theta$ is a diffeomorphism onto the sphere minus $-h$. The omitted point has sphere measure zero. Its surface Jacobian is $(\sin r/r)^{N-2}\in[0,1]$ for real $r<\pi$.

**PROVED (entire formulas).** $\cos\sqrt z$ and $\operatorname{sinc}\sqrt z$ are entire in $z$; hence the formal Jacobian, the displayed bond expression in the brief, and $2-2\cos r$ are entire functions of the quadratic coordinate variables. Also $2-2\cos r\ge4r^2/\pi^2$ on $[0,\pi]$, and the quadratic Hessian at zero is $K_\nu$.

**REFUTED (globally analytic density).** The actual coordinate density includes $\mathbf1_{\{r<\pi\}}(\sin r/r)^{N-2}$. For $N=2$ it jumps at the boundary; for finite $N>2$ extension by zero generally has only finite differentiability. Entire continuation of the Jacobian without this domain restriction is not the sphere integral and changes sign or grows beyond $\pi$.

**PROVED (which B obstructions disappear).** The square-root Jacobian singularity and H.4's specific square-root cusp disappear. Since the new Jacobian is at most one, its $L^p$ moments are harmless. The hard domain remains; for $N=2$ it can still produce a first-order boundary response, and the full-torus factor remains unsuitable for direct pointwise BKAR.

**REFUTED (no quadratic coercivity at all).** The brief's proposed obstruction is too strong. Since $H\ge(\nu/2)\sum_x|\Phi(\theta_x)-h|^2\ge(2\nu/\pi^2)\sum_x|\theta_x|^2$ and $\langle\theta,K_\nu\theta\rangle\le(4d+\nu)\sum_x|\theta_x|^2$, there is a positive comparison $\beta H\ge[4\nu/(\pi^2(4d+\nu))]\,\beta\langle\theta,K_\nu\theta\rangle/2$.

**OPEN (actual stability gap).** The comparison constant is far below one. Opposite tangent vectors near $\pi h^\perp$ represent nearby spins, so the bond quadratic can greatly exceed the physical bond. The ratio to the *unit-coefficient* product Gaussian can grow like $\exp[(1-c)Q]$; a global bounded perturbation or small polymer activity does not follow. A different Gaussian reference would still need a convergent local interaction estimate.

**PROVED (A comparison).** The good part of (A) lies near zero, where either chart has comparable analytic expansions. Bad spins can remain sphere variables, so exponential coordinates offer no needed improvement there. No exponential-chart Lean package is warranted for the selected route.

## 3. What P5 and P6 actually expand

**PROVED (source check).** I checked the page images of P5 journal p. 511 and P6 p. 36, and text against the adjacent printed pages. P5 is `sources/s002200050433 (1).pdf`; P6 is `sources/s002200050470.pdf`. P5 PDF page 27 is journal p. 511; P6 PDF page 36 is journal p. 36.

**PROVED (P5 hard partition).** P5 p. 511, (2.42) sets $\chi^{(k)}(\square')=\mathbf1\{|\psi|<p_1(\beta_k)\text{ on }\square'\}$; (2.43) inserts $\prod_{\square'}(\chi^{(k)}+\chi^{(k)c})=1$. The accompanying text says these fluctuation restrictions make some previous characteristic functions identically one away from the large-field region, removing their dependence on the new background variable. See also Lemma 2.1 and (2.44).

**PROVED (P5 domain ledger).** P5 (1.20), pp. 492–493, distinguishes the large-field domain, the region of fluctuation integration, and the smaller fluctuation-good domain. Equations (2.42)–(2.47), pp. 511–512, add the hard fluctuation partition. Thus the paper's good/bad split is not solely a condition on the physical spin.

**PROVED (P6 first stage).** P6 p. 35 says the interaction potentials of P5 (3.9), (3.11), (3.14), (3.15) have first been localized as sums of terms satisfying (4.28), with boundary terms (4.33)–(4.34). This uses covariance-square-root and background localization from earlier papers; P6 does not display a new Dirichlet random-walk or Gaussian-integration-by-parts proof for these bounds.

**PROVED (P6 decoupling).** P6 pp. 36–37, (4.39)–(4.43), multiplies each *localized interaction* $U(Y;\psi)$ by $t_Y$, differentiates the normalized expectation in $t_Y$, and uses Cauchy circles for those derivatives. The hard $\chi^{(k)}$ remains inside the integral, with no derivative applied to it. The centered Gaussian factor is a product after the covariance square-root change of variables.

**PROVED (P6 cancellation).** On P6 p. 36, (4.40) defines the union of selected interaction supports and the marked support. The text below it cancels disconnected components between numerator and normalization by product integration; only connected families remain in (4.41)–(4.42). This is a parameter expansion of local potentials, not covariance BKAR with moving hard cutoffs.

**PROVED (P6 bound).** P6 pp. 37–39 give the local-potential smallness (4.43), tree support count (4.44)–(4.45), polymer normalization (4.46)–(4.51), and final localized bound (4.52). The printed (4.49) bounds the normalization polymer activity by $2\,3^d eK_0L^d\epsilon^{1/2}\exp[-(4\kappa_0-1)d_{k+1}(Z')]$.

**REFUTED (verbatim first-step transfer).** P5/P6 assume already localized, uniformly small interaction potentials and a product fluctuation cutoff. Their multi-scale domain and renormalized-background hypotheses do not furnish the one-scale integrated bad-core/collar potential or the L38.11 estimate. The paper mechanism starts *after* the missing model estimate in this branch.

**OPEN (one-scale version of the mechanism).** Required lemmas, in order: exact hard physical sectors (landed core); conditional good Gaussian and crossing-square identity; product fluctuation cutoff implying good physical chart away from collars; localized determinant/hole-walk/collar potentials with uniform exponential weighted norm; bounded local normalized partition functions in complex decoupling parameters; connected cancellation of disconnected components; weighted tree/animal sum; exact lift and regulator removal. The fourth lemma is the first unproved one.

## 4. Linked bound, constants, and interface

**OPEN (first missing lemma).** In the chosen route, prove `IntegratedHardCollarPotential`: after summing/integrating each amplitude-selected dressed core and its good collar under the conditional Gaussian, with all crossing factors, real hard cutoffs, Jacobians, source, determinant loops, and hole walks retained, there is an exact decomposition into local potential terms $U(Y;g)$, on one product fluctuation reference, such that
$$\sup_Q\sum_{Y\ni Q}e^{\kappa_0|Y|}\sup_{\|g\|_1<1}|U(Y;g)|\le C\{B_{\rm ord}(\beta)+e^{-c\log^2(\beta a)}\},$$
uniform in the torus, $\nu$, and all finite-walk/chart regulators, with identical nonwinding lifts and a termwise limit. This is the precise estimate needed before the P6 connected cancellation can be used; its existence is not proved.

**OPEN (what was tried).** H37.1–H37.7 supply square completion, an exact sector measure, and determinant loops; L38.1–L38.6 supply mean attenuation, collar budget, and hole walks; L38.8–L38.9 supply a regulated connected identity. None bounds repeated exterior influences or the fully integrated Jacobian and hard indicators in support-size weighted norm. A bare $q^R$ shell bound has a ball of $O((R/s)^d)$ blocks and cannot pay $e^{\kappa_0|Y|}$.

**PROVED CONDITIONAL ON `IntegratedHardCollarPotential` and the normalized connected expansion.** L38.11 follows with $\epsilon_\beta=C[B_{\rm ord}(\beta)+e^{-c\log^2(\beta a)}]$. Then the existing abstract `decomposition`, `mayer_activity_bound`, `pe_size`, and `pe_blockTorus_frozen` can be used after their literal hypotheses are checked. No full-activity amplitude has been established.

**PROVED (order of choices).** Fix the target $\kappa_0$ and root constants first. Fix $L\ge3$ (one may take $L=3$), hence $\nu_*$ and $\eta=-\log[2d/(2d+\nu_*)]$; choose $a>1$, $b>0$, and then $A>\sqrt2b/\sqrt{\nu_*}$. Choose $M$ so $s=ML\ge8$ and $8\kappa_0 3^d/s<\eta$. Finally set $\delta_\beta=A\log(\beta a)/\sqrt{\beta\nu}$ and enlarge $\beta_0$ for $2\delta_\beta<1$, H37.2, L38.4, and any proved smallness threshold. A fixed $A$ cannot precede arbitrary later $L$.

**PROVED (ordinary amplitude).** On the all-plus product cutoff, $B_{\rm ord}(\beta)\le C[\log(\beta a)/\sqrt\beta+\log^2(\beta a)/\beta+\log^4(\beta a)/\beta]$ (F.13/L38.10). The proposed full $\epsilon_\beta$ above is **conditional** on the integrated lemma; $c<A^2\nu_*/4$ must be chosen after all specified collar losses.

**OPEN (smallest final interface).** A single `OneScalePhysicalLogData` structure may contain source-independent $c_\Lambda$, connected $s$-block functions $p_\Lambda(X;g)$, the exact identity $\log Z_\Lambda(g)-\log Z_\Lambda(0)=\langle g,h\rangle+\sum_X[p_\Lambda(X;g)-p_\Lambda(X;0)]$, analyticity on $\|g\|_1<1$, source locality, exact nonwinding lift, and the weighted full-ball bound $\sup_Q\sum_{X\ni Q}e^{\kappa|X|}|p_\Lambda(X;g)|\le B_\beta\to0$ with the required numeric root threshold. Its named `physical_nonvacuity` obligation is to construct these fields from the actual sphere integral uniformly in every admissible torus and $\nu\in[\nu_*,1]$, with no premise equivalent to the desired frozen conclusion.

**PROVED CONDITIONAL ON `OneScalePhysicalLogData.physical_nonvacuity`.** The Cauchy derivative construction of KF0.md gives $T_1$, $T_j=0$ for $j\ne1$, and the high-mass `KF0RootFPartial` clauses. The requested symbol `rootF_kf0_partial_of_oneScaleInput` was **not found** in the current Lean tree; it is a planned theorem name, so it cannot be reported as landed. The low-mass frozen theorem remains outside this statement.

**OPEN (strictness).** This log interface asks for less data than `DirectK0PolymerInput`: no gas activities or exact gas partition representation. DirectK0 plus the PE bridge implies it. A formal strict non-implication is **not proved**; under sufficiently strong smallness, abstract exponentiation may reconstruct gas activities. Call it a smaller requested interface, not a proved strictly weaker mathematical condition.

## 5. Lean disposition and bounded packages

**PROVED (landed status).** `KF0BlockSplit.lean`: **KEPT as is** for (A) hard; `KF0SqrtReal.lean`: **KEPT as is** for nonnegative Stieltjes kernels; `KF0Gaussian.lean`: **KEPT as is** for the conditional Gaussian and all-good cutoff; `KF0WalkSeries.lean`: **KEPT as is**; `KF0WalkTruncation.lean`: **KEPT as is** for `kf0C`, `kf0CR`, and `kf0_lemmaH1`. These declarations were checked in the current tree; they assert no linked bound.

**PROVED (H37 disposition).** H37-1 **KEPT as is**: incidence-map square completion H37.1. H37-2 **KEPT as is**: normal term H37.2 on the actual good chart. H37-3 **KEPT with named change `KilledWalkAndLoop`**: finish killed walks, determinant loops and exact lift using `kf0CR`. H37-4 **KEPT as is**: fixed-product conditional sector identity H37.6, including normalization and source. None should import a proposed full-activity theorem.

**PROVED (L38 disposition).** L38-1 **KEPT as is**: force shell sum. L38-2 **KEPT as is**: corrected Gaussian-unit radius and collar budget. L38-3 **KEPT as is**: frozen-radius closure graph. L38-4 **KEPT as is**: loop OR identity and hole-walk path support. L38-5 **KEPT with named change `FiniteWalkIdentityOnly`**: prove $C_R$ positivity, $Q_R$ support, and L38.7; keep L38.8–L38.9 as optional algebraic regulator modules, not the chosen analytic estimate. No package is discarded solely because A is chosen.

**PROVED (other disposition).** F.1 localization **KEPT as is** for the ordinary all-plus interaction, with the explicit `KF0Gaussian` and `KF0WalkTruncation` inputs. Torus agreement **KEPT as is** for pathwise nonwinding coefficients; a separate lift theorem remains required for integrated heavy terms. `KF0TwoSheetProduct` is useful as an exact check but is not a dependency of A's conditional good-sector identity.

**OPEN (package 1, strong, at most 300 new lines).** `KF0KilledWalk`: prove $K_G^{-1}(x,y)=\sum_{w:x\to y,\,w\subset G}(2d+\nu)^{-|w|-1}$ and the row tail $\le\nu_*^{-1}q^R$; then H37.3. Split determinant trace H37.7 into a second at-most-300-line file `KF0DetLoop`.

**OPEN (package 2, Sonnet, at most 300 new lines per file).** `KF0ConditionalSector` proves the exact H37.6 integral using `partitionFunction_eq_sum_kf0Sector`, `kf0Sector_iterated`, `lintegral_tangent_gaussian_change`, and the chart measure. `KF0BoundarySquare` proves H37.1–H37.2 separately with every crossing bond present.

**OPEN (package 3, Sonnet, at most 300 new lines per file).** `KF0MeanShell` proves L38.1–L38.3; `KF0CollarBudget` proves L38.4; `KF0CollarClosure` proves the finite component partition and $\sum_I|S_I|\le\sum_{Q\in B}|C_Q|$. These depend on package 1 for the killed-walk decay and use the threshold $1/\log\beta$.

**OPEN (package 4, Sonnet, at most 300 new lines per file).** `KF0LoopOccupancy` proves L38.5 and its path support; `KF0HoleWalk` proves L38.6; `KF0NonwindingPaths` proves equality of coefficients for each nonwinding lift. Integrating these coefficients into a heavy activity is excluded from these statements.

**OPEN (package 5, strong, at most 300 new lines per file).** `KF0FiniteWalkIdentity` proves positive invertibility of `kf0CR`, finite range of $Q_R=C_RK_\nu C_R-I$, and L38.7 using `lintegral_matAct`; optional `KF0RegulatedDecomposition` proves L38.8–L38.9 using `Balaban.Polymer.decomposition`. Neither states a uniform bound.

**OPEN (package 6, strong, research input; split only after a paper proof).** Formalize `IntegratedHardCollarPotential` as the exact integrated potential identity and the displayed weighted estimate, in distinct files of at most 300 lines. Its non-vacuity proof must precede any worker assignment to the linked-bound closure; an axiom or abstract instance would merely restate the open problem.

**PROVED CONDITIONAL ON package 6 (package 7, Sonnet, at most 300 new lines per file).** `KF0ConnectedPotential` applies the P6-style parameter expansion and normalization bound, then `KF0DirectGas` proves `DirectK0PolymerInput` or directly builds `OneScalePhysicalLogData`. `KF0RootPartialBridge` applies `pe_blockTorus_frozen`, `pe_PY_analyticOnNhd`, `frozenPY_boxMap`, and the Cauchy source derivative. This is high-mass partial closure only.
