# Round 40: P5/P7 and the high-mass one-scale bound

**PROVED (scope and correction).** This note concerns the exact frozen sphere model at $k_f=0$, $\nu_*(L)=7/(8L^2)\le\nu\le1$. The Round 39 claim that `rootF_kf0_partial_of_oneScaleInput` was absent is false: it is landed in `Balaban/Correlations/KF0RootFPartial.lean:384`, with `rootFTorusClauses_kf0_of_oneScaleInput` and `rootFAgreement_kf0_of_oneScaleInput`. Its physical one-scale hypothesis remains open.

**PROVED (sources).** I checked printed page images of P5 pp. 502, 511–512 and P7 pp. 519–520, and checked the adjacent pages in their PDFs: [P5](</home/scott/Balaban/sources/s002200050433 (1).pdf>) and [P7](/home/scott/Balaban/sources/s002200050486.pdf). P5 PDF page is printed page minus 484; P7 PDF page is printed page minus 492. Equation numbers below are those printed in the papers.

## 1. What the papers do

**PROVED (initial step structure).** P5 (1.20), p. 492, nests $\Omega_1\supset\Omega''_1\supset Z_1^c\supset\Omega_2\supset\cdots\supset\Omega_k\supset\Omega''_k\supset Z_k^c$. The $\Omega_j$ select where a fluctuation integral is performed; $\Omega''_j$ is its small-fluctuation part; $Z_j$ records large-field regions. These are three distinct domain roles.

**PROVED (spin tests).** P5 (1.19), p. 492, tests $|\psi_k-Q_k\phi_k|$, $|\partial^\eta\phi_k|$, $|\Delta^\eta\phi_k|$, and $|\alpha_k|$ against $\delta_k$ on an enlarged cube; in its stated $k>k_0$ regime it also tests $|\phi_k-h|<\delta_k/\sqrt{\nu_k}$ and $||h|^2-1|<\delta_k^2/\sqrt{\nu_k}$. The latter conditions are omitted in its $k\le k_0$ regime. This is much richer than our site-only $|\phi_x-h|<\delta_\beta$ test.

**PROVED (new field-violation set).** P5 (2.1), p. 501, first separates an inherited large-field neighborhood $U_k=Z_k^{\approx}$. On $\Omega'_{k+1}$, defined by distance $>LMR_k$ from $U_k'^{\sim3}$ in (2.2)–(2.4), (2.5)–(2.6), p. 502, inserts the hard test $|\theta-Q\psi_k|<2\delta_k$ and calls its violated-cube set $P_{k+1}$. Formula (2.8) removes a three-layer neighborhood of $P_{k+1}$ from the next integration domain $\Omega_{k+1}$.

**PROVED (new background-violation set).** P5 (2.11)–(2.14), pp. 503–504, forms $\phi_{k+1}$ on local generating sets and inserts a second partition whose failed cube set is $Q_{k+1}$. The tests include the field/gradient/Laplacian/constraint conditions of (2.13), with stricter constants near $\partial\Omega_{k+1}$. Formula (2.15) keeps these characteristics in the exact transformed density.

**PROVED (new fluctuation-violation set).** P5 (2.39)–(2.43), pp. 510–511, uses a localized covariance square root to write the old spin as approximate background plus $\beta_k^{-1/2}C^{(k)1/2}_{\rm loc}\psi$. The hard fluctuation test is $|\psi|<p_1(\beta_k)$ on each next-scale large cube, with $p_1=A_1(\log\beta_k)^{p_1}$; its failed-cube set is $R_{k+1}$. Lemma 2.1, (2.44), removes earlier moving characteristic functions on the separated good region.

**PROVED (collar geometry).** P5 (1.2)–(1.3), p. 488, sets $R_{j-1}=R_0(\log(a\beta_{j-1}))^2$ and thickens by $M R_{j-1}$ in the $j$th scale. P5 (2.45)–(2.46), p. 512, defines $\Omega''_{k+1}$ away from thickened $Q_{k+1}\cup R_{k+1}$ and bounds the excluded halo by roughly $4+(L-1)/2+2[R_k]$ layers. Thus this is a fixed **rule** with a radius growing as $\log^2\beta_k$, not a fixed number of $M$-cubes and not our amplitude-dependent radius.

**PROVED (where hard factors go).** P5 (2.47), p. 512, puts the Gaussian variables in $\Omega_{k+1}\setminus\Omega''_{k+1}$, failed tests, and the surviving hard characteristics in an integral operator; only $\Omega''_{k+1}$ supports the ordinary fluctuation expectation. P6 (4.39)–(4.52), pp. 36–39, later interpolates *localized interaction potentials* under a fixed hard product cutoff, as recorded in KF0-INFL.md.

**PROVED (what P7's $R$ removes).** P7 pp. 495–497 defines $R^{(k)}$ on a density **already in the image** of $S^{(k-1)}T^{(k-1)}$. Its $Z$ in (3.7) is a second-kind component with exhausted future-step counter $K(Z)=0$, selected for removal from the large-field density. It is not simply every newly failed $P_{k+1}$, $Q_{k+1}$, or $R_{k+1}$ cube at its birth.

**PROVED (normalization before the bound).** P7 (1.6)–(1.7), p. 496, defines $R^{(k)}$ by inserting a restricted denominator integral and proves that the full integral is preserved. P7 (3.4)–(3.5), p. 518, evaluates that denominator by a local saddle expansion on $Z_0$; this cancels the main actions in the numerator. A bare one-scale construction would need its own denominator identity before importing the later volume estimate.

**PROVED (exact input to P7 bound).** P7 (3.7), p. 519, is an operator with an integral over $Z_0$, a denominator correction $\widetilde E_0^{(k)}$, extra fluctuation variables, action terms, old boundary terms, and the inherited operator $T_{k_1}(Z_{k_1})$. Equation (3.8) bounds **that inherited operator** by
$$C(\mathbb A''_k\cap Z)^{-1}\exp\!\left[-2p_2(\beta_k)-H_k|Z|_\eta-\sum_{j=k_1}^{k-1}(O(1)\log\beta_j+\mathrm{const})|Z_j^c\cap Z_{j+1}|_\xi\right].$$
The inverse combinatorial factor is stated in the text after (3.8), p. 519. It is part of the estimate, not supplied by the bare action.

**PROVED (exact integration cost).** P7 (3.9), p. 519, bounds the remaining exponential factors by
$$\exp\!\left[\tfrac N2\log\beta_k,|Z_0|+O(1)+\sum_{j=k_1}^{k-1}(O(1)\log\beta_j+\mathrm{const})|Z_j^c\cap Z_{j+1}|_\xi\right].$$
P7 p. 520 bounds the integration-domain volume by $1$, notes the layer costs can cancel (3.8), and also bounds the whole (3.9) exponent by $C(\log\beta_k)^{2d+2}$.

**PROVED (reserve and final operator estimate).** P7 p. 520 has $|Z_0|<14^d$ from p. 518 and $|Z|\le(12MR_k)^d$ for this small removed component; $|E_k||Z|\le C(\log\beta_k)^{2d+1}$. With $p_2(\beta_k)=A_2(\log\beta_k)^{p_2}$, exponent $p_2\ge2d+2$ and sufficiently large $A_2$, one copy of $p_2$ pays these losses. P7 (3.10) then reads
$$\sum_{\mathbb A''_k\cap Z}\int d\psi_k|_Z\,|T''_k(Z,\mathbb A''_k\cap Z)e^{E_k|Z|}F|\le e^{-p_2(\beta_k)-H_k|Z|_\eta}\sup_{\mathbb A''_k\cap Z,\psi,\psi'}|F|.$$

**PROVED (choice of log powers).** P5 (1.2), p. 488, fixes a $\log^2\beta$ spatial halo. P7 p. 520 therefore budgets a $\log^{2d+2}\beta$ worst-case action/integration term and a $\log^{2d+1}\beta$ vacuum term. These powers belong to its multiscale constants $p_2,H_0,A_2$; substituting our $A\log\beta$ small-field threshold without changing the halo would invalidate that budget.

**PROVED (meaning of the sup).** The supremum in (3.10) is over the component multi-index and the remaining field/fluctuation variables shown there; the operator may act on any bounded $F$ of those variables. Thus it is a uniform real integral-operator bound, including exterior values allowed by the current characteristic functions. It is not itself a finite-support or analytic coefficient bound for dependence on those values.

**PROVED (analytic exterior dependence).** Immediately after (3.10), P7 pp. 520–523 proves a separate Lemma 3.1 type analytic extension after removing dependence of hard characteristics on the exterior variable by rotations/coset averaging, then bounding the complex action from its real nonnegative part and small complex remainders. The real operator norm alone does not perform that step.

**PROVED (gas after the operator bound).** P7 (3.26)–(3.28), pp. 527–528, takes a Mayer expansion of boundary terms touching removed components, joins each touched component to its halo, obtains activities $\rho''_k(\mathcal X)$, then exponentiates. P7 p. 528 calls the activity summation “almost completely standard”; it does not print the full rooted tree estimate. The claimed activity prefactor is $\beta_k^{-m-1}$, and after exponentiation $C\beta_k^{-m-1}\le\tfrac12\beta_k^{-m}$.

**PROVED (propagator source).** P5 (2.18)–(2.19), p. 505, uses P3 Proposition 2.3 to make its approximate background depend only on $R_{k+1}(\square')$, with error $<e^{-R_k}$; P5 (2.40)–(2.41), pp. 510–511, handles the localized covariance square root and determinant. P3 §§2–3 builds domain-dependent Green/resolvent random-walk localizations using P2's variational operators and earlier Balaban propagator estimates. P7 (3.9) invokes these established/inductive estimates; it does not prove a new explicit bare Dirichlet determinant or hole-walk identity there.

## 2. Specialization to the physical $k=0$ question

**REFUTED (verbatim P7 $k=0$ corollary).** P7 Theorem 2, p. 497, assumes $\rho_k=S^{(k-1)}T^{(k-1)}\rho_{k-1}$, with a previous large-field operator. At $k=0$ there is no $k-1$ density, no $T_{k_1}$ in (3.7), and no (3.8) reserve. P7 §4, p. 529, instead starts the *last integral* at the first $k_f$ with $\nu_k>7L^{-2}/8$ and assumes the input density already satisfies H1–H5 and H7. For $k_f=0$ this still needs a physical base-density identification and a first-integral estimate.

**PROVED (index consequence).** If $\nu_0\ge\nu_*(L)$, the intended partial Root-F witness has $k_f=0$ and no ordinary block-spin transformation precedes its final integral. Relabeling P7's $R^{(1)}$ after a $0\to1$ transformation as $R^{(0)}$ changes the density and cannot establish the exact original partition identity by itself.

**PROVED (one-scale target).** For the bare model the required statement is a local log expansion of the exact sphere integral: $\log Z_\Lambda(g)-\log Z_\Lambda(0)=\langle g,h\rangle+\sum_X[p_\Lambda(X;g)-p_\Lambda(X;0)]$, with analytic, source-local, nonwinding-compatible $s=ML$ block terms and a full-source-ball weighted norm tending to zero. This is the open input consumed by the landed `rootF_kf0_partial_of_oneScaleInput`, not the output of P7 (3.10) alone.

**PROVED (comparison: failed conditions).** Our bad $s$-block is selected solely by $a_Q=\max_{x\in Q}|\phi_x-h|\ge\delta_\beta$. P5 has failed background-field/derivative constraints and three new failed sets $P,Q,R$. A physical-site bad block is a useful one-scale simplification under $\nu\ge\nu_*$, but it is not a literal P5 region label.

**PROVED (comparison: collars).** Our L38.2 site radius $R_Q=\lceil(2/\eta)\log_+(C_L\sqrt\beta,a_Q\log(\beta a))\rceil$ is $O(\log\log\beta)$ at threshold and $O(\log\beta)$ at order-one amplitude. P5 uses $R_k=R_0\log^2(a\beta_k)$ uniformly, and its nested halos (2.3), (2.45)–(2.46) also handle background and fluctuation tests. The two geometries cannot be identified by renaming $M$.

**PROVED (comparison: reserve).** Our mass charge per selected site is $\beta\nu a_Q^2/2$; H37.1 and L38.4 retain at least $\beta\nu_*a_Q^2/4$ for specified costs. P7's $e^{-2p_2-H_k|Z|}$ is an **inherited** operator budget for a second-kind component, not the Peierls bound of a newly failed test. For P5's $\log^2\beta$ halo, a threshold $a_Q\asymp\log\beta/\sqrt\beta$ supplies only $O(\log^2\beta)$, insufficient to pay $O(\log^{2d+1}\beta)$ Gaussian/volume losses; P5 chooses stronger log-power thresholds and multi-step reserves.

**PROVED (comparison: mean and propagator).** L38.1–L38.3 is a bare massive Dirichlet mean attenuation theorem with a Gaussian-unit target $1/\log\beta$. P5/P7 instead use localized approximate minimizers and the P3 exponential decay outside $R_k(\square')$; P5 (2.19) makes the error $<\beta_k^{-K}$. Our determinant loops H37.7 and hole walks L38.6 give explicit bare analogues of domain-dependent covariance/determinant localization, not replacements for P3's general background propagators.

**REFUTED (identifying `IntegratedHardCollarPotential` with (3.10)).** The former asks for an exact decomposition into local $U(Y;g)$ and a weighted support sum after integrating a fresh bad core. P7 (3.10) is only a uniform bound on an inherited component operator acting on bounded $F$; locality and analyticity are supplied separately, and (3.26)–(3.28) later form a gas. The paper avoids demanding our full lemma as one operator statement, but it still needs the corresponding first-step locality, analytic extension, and gas bound somewhere.

**PROVED (bare real sup estimate).** Let $D$ be a union of dressed cores and collars, $B$ its disjoint selected core blocks, and fix arbitrary exterior spins $\xi$. For real $\beta,\nu>0$, normalized sphere measure, $\|g\|_1<1$, and bounded measurable $F$,
$$\left|\int_{\phi_D:\,a_Q\ge\alpha_Q\ (Q\in B)}e^{-\beta H_D(\phi_D\mid\xi)+\langle g_D,\phi_D\rangle}F(\phi_D,\xi)\,d\sigma_D\right|\le e\,e^{-\frac{\beta\nu}{2}\sum_{Q\in B}\alpha_Q^2}\|F\|_\infty.$$
Here $H_D$ contains all masses at $D$, internal bonds and crossing bonds; all are nonnegative, and selected sites lie in distinct blocks. The estimate is uniform in $\xi$ and needs no differentiability of a hard cutoff.

**PROVED (normalization loss).** A Gaussian Dirichlet normalizer on any finite site set $D$ satisfies $G_D^{-1}\le[c_\beta^{-1}(4d+\nu)^{(N-1)/2}]^{|D|}=\exp[O(|D|\log\beta)]$ for fixed $d,N$ and $\nu\in[\nu_*,1]$. After dyadic amplitude bins and the L38.2 collars, $|D|\le s^dc_d\sum_Q(1+R_Q/s)^d$; L38.4 pays this specified polynomial normalization loss and leaves $e^{-c\log^2(\beta a)|B|}$. Binning adds $O(\log\log\beta)$ per core and can be paid as well.

**PROVED (uniformity and its exact scope).** The preceding real bound holds for every fixed exterior spin field, however rough, because crossing bonds are nonnegative. It also holds with extra real cutoff factors bounded by one. This is the part of the P7 operator-norm pattern that transfers directly to a fresh bad component; it says nothing about how the value changes when an exterior spin is varied.

**PROVED (real one-scale reserve).** Fix $H_0>0$ and put $H_\beta=H_0\log(\beta a)$. In L38.4 choose $C_{\rm loss}$ above the Gaussian normalization constant and $H_0s^d$ (plus the finite bin-count constant). Split the core charge in half for normalization and the desired reserve. For sufficiently large $\beta$, the preceding integral divided by its local Gaussian normalizer is then at most $C\|F\|_\infty\exp[-c\log^2(\beta a)|B|-H_\beta|S_B|]$, where $S_B$ is the dressed block support and overlaps are counted once. This is a real, fixed-support upper bound, not a local activity formula.

**REFUTED (arbitrary P7 reserve from our threshold).** The last display provides $p_{2,\rm bare}(\beta)=c\log^2(\beta a)$ per bad core after specified losses. It cannot be silently upgraded to P7's freely chosen $A_2\log^{p_2}\beta$ with $p_2\ge2d+2$ at the same $a_Q\asymp\delta_\beta$. Such an upgrade requires stronger initial field thresholds or a different source of suppression.

**OPEN (limit of that proof).** This establishes a crude real operator estimate for a chosen finite interior and fixed exterior spins, conditional only on the exact choice of $D$ and bins. It does **not** identify the denominator/reference of the full conditional good Gaussian, preserve the exact local partition identity through all overlapping choices, or control complex exterior fields. The full analogue of P7's analytic component operator remains open.

**OPEN (first post-sup step).** Even if a uniform P7-style sup bound for each fresh component were landed, the exterior-dependent operator must be localized with a weighted *difference* or cut-parameter estimate; the bound $\|T_ZF\|\le\epsilon\|F\|$ permits an arbitrarily nonlocal dependence on exterior variables. P6's expansion accepts already localized potentials. The source-local $U(Y;g)$ and exact nonwinding lift still need proof, though they may be built after, rather than within, the component operator bound.

## 3. Consequences for the two campaigns

**REFUTED (general-step corollary today).** The landed R lane has no physical $k=0$ input operator, and its P7 (3.10) producer assumes inherited history. Running “one general step at $k=0$ followed by the last integral” would add a new physical $0\to1$ base bridge, output density, source terms, and large-field gas before the final integral. The direct high-mass route (A) asks for the one local log expansion and avoids that extra RG output; it is presently shorter.

**PROVED (what is shared).** `kwOp_form_ge`, `kwOp_inv_hasSum`, `kwOp_inv_mulVec_decay`, `kwAdjG_pow_locality`, and `kwTrunc_tail_rowSum_le` in `Green/KF0KilledWalks.lean` already implement the bare killed-walk geometry; `kw_logdet_eq`, `kw_loop_sum_le`, `kw_det_ratio_bounds`, and `kw_jacobi` in `Green/KF0DetWalks.lean` implement the bare determinant identities. `kf0C_eq_kf0SqrtR` and `kf0CR_torus_eq` in `Green/KF0WalkTorus.lean` cover full-torus walk agreement. Reuse them for route (A); do not commission duplicate statements.

**OPEN (R-lane overlap).** A hypothetical R derivation still needs `OPEN-R-OP-PHYSICAL`: the actual physical operator and its (3.7)/(3.10) bound. It also needs the removed-component gas of VMOD-40/41 and a two-size post-boundary assignment, including analytic/source fields. The abstract `gas_pe` in `Polymer/MayerPE.lean` does not establish those model inputs.

**PROVED (retained-hole distinction).** At the bare $k_f=0$ start there is no inherited large-field component, so the **specific** VMOD-41/42 bridge through a retained old hole is absent. Fresh bad cores still make holes in the good Gaussian, with crossing interactions and hole walks; those are exactly H37/L38's remaining links. A positive-scale R run can acquire retained holes later, so the R-lane bridge is not globally dispensable.

**PROVED (genuine $0\to1$ distinction).** `Inhabited/LevelStepSetting.lean:hatStepK` has $1\le k$ and `hatStepK_betaU` scales by $\beta 3^k$ in its $d=L=3$ instance; the landed $k=1$ case is $1\to2$. `LargeField/Base/BaseSmallField.lean:BaseSmallFieldInput` packages a first-step remainder and boundary exponent as inputs; `baseStepData_of_input` consumes them. `Inhabited/BaseStep.lean:baseStepData_nonempty` uses a zero witness, not the physical sphere integral. A real $0\to1$ output requires new physical measure, Gaussian, source, fluctuation, large-field operator, and class-closure proofs even with no inherited effective terms.

**OPEN (new first-step gas).** The first $0\to1$ output may have no inherited holes or old boundary coefficients, so that portion of the R gas simplifies. Its newly failed $P,Q,R$ tests and fresh collar operators still need a connected gas and analytic localization; P5/P7 do not provide a landed Lean producer for the bare input. The direct $k_f=0$ last integral does not require constructing this output density.

**PROVED (package recommendation).** **Assign KF0-INFL §5 packages 2–4**, each in leaves of at most 300 new lines: exact conditional sector and boundary square; mean shell, collar budget and closure; loop occupancy, hole walks and nonwinding paths. Use the landed killed-walk and determinant files as predecessors. These are reusable bare identities and numerical estimates, independent of whether the final linked activity follows P7-style operator localization.

**PROVED (package 5 recommendation).** **Hold the new full-torus `KF0FiniteWalkIdentity`/regulated decomposition part of package 5** as an optional route-(B) check; its core $C_R$ and lift facts are already substantially landed. For chosen route (A), first formulate a small real component-operator lemma and a separate exterior cut-locality/analyticity lemma. Assign their Lean proofs only after the latter has a mathematical proof; P7 (3.10) alone does not provide one at $k=0$.

**OPEN (remaining decision).** The one-scale linked estimate and physical `KF0OneScaleInput` remain open. P7 supplies an operator-norm-plus-localization pattern, not an automatic base-case theorem. A proved local exterior-influence lemma is the next mathematical gate; the full frozen low-mass theorem is a separate campaign.
