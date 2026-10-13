# KF0-ONECORE — one physical bad block and its exterior

**OPEN (verdict).** The one-core linked estimate is not proved. The first failed step in the proposed route is the claim that collar Gaussian variables can be integrated crudely while exterior factors become the all-good factors: the inverse square root \(C_G=K_G^{-1/2}\) mixes those variables. A walk expansion can expose this influence, but no weighted, integrated bound for the resulting hard-chart factors has been proved.

**PROVED (scope).** Let \(B=\{Q\}\), choose one dyadic bin \(\alpha\le a_Q<2\alpha\), let \(D\) be its bad physical sites, \(G=\Lambda\setminus D\), \(S_Q\subset G\) its L38.2 collar, and \(W_Q=D\cup S_Q\). “One core” means exactly one physical bad block; auxiliary large Gaussian sites are discussed separately. Sources first vanish, then satisfy \(\|g\|_{\ell^1}<1\).

**PROVED (snapshot).** I inspected Lean commit dc814d0039aa1c701f8bf8208e1a0ae043bfb2a3 and the source signatures in KF0BoundarySquare.lean, KF0GoodGaussian.lean, KF0MeanShell.lean, KF0CollarClosure.lean, KF0WalkHalo.lean, MayerPE.lean, GasOperator.lean, FrozenTorus.lean and Decomposition.lean. The first two have SHA256 c4c2e2c5eb59ba082db6f3f7051505949f95ead36e3af068c870a350 and 5c694b9b434b74086f841650110708144b5b4e4e9663b03ccf166b87a5e81846. This is a focused mathematical proof attempt and Lean interface audit; it does not edit the Lean tree.

**PROVED (status convention).** PROVED means a checked exact identity, elementary deduction, or exact statement of a landed theorem. PROVED CONDITIONAL ON states the needed premise. OPEN is a missing estimate or physical identification. REFUTED is a proposed inference contradicted by an exact dependence or theorem signature.

## 1. Exact one-core ledger before any locality claim

**PROVED (physical sector).** partitionFunction_eq_sum_kf0Sector and kf0Sector_iterated give an exact sum over bad block sets. Selecting \(B=\{Q\}\) and its bin leaves \((1-\chi_Q(q))\prod_{Q'\ne Q}\chi_{Q'}(\phi)\); every internal and crossing bond remains in the energy. The single sector is nonnegative at real \(g=0\).

**PROVED (good chart, mathematical identity).** On the support of the good indicators, each good sphere spin has the plus-chart coordinate \(u_x\in h^\perp\) and chart Jacobian \(j_x(u_x)\). For fixed \(q_D\), write the exponent's tangent quadratic exactly as
\[
\beta H_D^0(q)+\frac{\beta}{2}\langle u,K_Gu\rangle+
\beta\langle J_q,u\rangle+\frac{\beta}{2}S(q)+\beta R(q,u).
\]
Here \(H_D^0\) excludes crossing bonds, \(S\) is their \(q\)-dependent square, \(J_q\) their tangent linear source, and \(R\) contains the remaining normal/chart and nonlinear terms. This is a definition by exact expansion, so no crossing term is counted twice.

**PROVED (square).** Put \(m(q)=-K_G^{-1}J_q\), \(C_G=K_G^{-1/2}\), and \(u=m(q)+\beta^{-1/2}C_G\psi\). The completed_square theorem gives
\[
\tfrac12\langle u,K_Gu\rangle+\langle J_q,u\rangle+\tfrac12S
=\tfrac1{2\beta}\|\psi\|^2+\tfrac12(S-\langle J_q,K_G^{-1}J_q\rangle).
\]
The boundary_schur and kwOp_boundary_square theorems give the retained nonnegative fraction of \(S\); exp_combined_le also accounts for the controlled normal term under its displayed threshold hypotheses.

**PROVED (measure after the square, on paper).** Finite-dimensional Gaussian change of variables contributes \(G_G=c_\beta^{|G|}(\det K_G)^{-(N-1)/2}\). Thus the selected sector equals the \(q_D\) sphere integral of \(\exp[-\beta H_D^0-\frac{\beta}{2}(S-J_qK_G^{-1}J_q)+\langle g_D,q_D\rangle]\) times \(G_G\,\mathbb E_{\gamma_G}[\chi_G(u)\mathcal J_G(u)e^{-\beta R(q,u)+\langle g_G,\Phi^+(u)\rangle}]\), with \(u=m+\beta^{-1/2}C_G\psi\). Every good indicator and Jacobian is still inside the expectation.

**OPEN (Lean status of that identity).** lintegral_good_gaussian_change proves the unshifted \(v=C_G\psi\) integral for arbitrary nonnegative \(F\), and kwSqrt is landed. KF0GoodGaussian.lean explicitly marks the full sector chart identity as “Target (T4), not proved”: subset-site chart measure, the good energy/source transfer, and hemisphere complement still need Lean proofs. The shift by \(m(q)\) is another exact finite-dimensional step to formalize.

**REFUTED (the sketch's literal bracket if \(H_D\) includes crossing bonds).** Multiplying \(e^{-\beta H_D}\) by \(e^{-\beta(S-JK_G^{-1}J)/2}\) counts the crossing square \(S\) twice when \(H_D\) has the Round-40 meaning. The corrected ledger above uses \(H_D^0\), plus the Schur term, and keeps the normal remainder \(R(q,u)\) inside the good integral.

**PROVED (determinant).** With \(N_0=G_\Lambda\), the sector's determinant factor is \(R_{\det}(\{Q\})=G_G/G_\Lambda\). kw_logdet_eq supplies the hole-loop series, and KF0-HEAVY.md (H37.7) assigns each loop meeting \(D\) to its visited path. Its local site term costs \(O(|D|\log\beta)\); the real reserve can pay that specified loss.

**PROVED (source).** The exact source splits as \(\langle g,h\rangle+\sum_{y\in D}g_y\cdot(q_y-h)+\sum_{x\in G}g_x\cdot(\Phi^+(u_x)-h)\). Since spins lie on a compact sphere, each finite-volume sector is entire in \(g\), and \(|e^{\langle g,\phi\rangle}|\le e^{\|\Re g\|_1}\le e\) on the requested ball. This proves pointwise source analyticity, not a uniform local-log norm.

**PROVED CONDITIONAL ON the exact normalization ledger.** The all-good sector has \(D=\varnothing\), \(C_\Lambda\), and normalizer \(G_\Lambda\). A one-core rooted comparison uses \(Z_{\{Q\}}(g)/Z_{\varnothing}(g)\) only where \(Z_{\varnothing}(g)\ne0\). Positivity gives this at \(g=0\); nonvanishing on the whole complex source ball needs the ordinary convergent expansion.

## 2. Test of the proposed collar and walk argument

**PROVED CONDITIONAL ON a row-sum bound for \(C_G\).** On the product event \(\|\psi_x\|\le p_\beta\) for all \(x\), outside \(S_Q\) one has \(\sqrt\beta\|u_x\|\le p_\beta\sum_y|C_G(x,y)|+\sqrt\beta\|m_x\|\). The landed mean_outside_collars bounds the second term by \(1/(2\log(\beta a))\). A quantitative margin below the physical good cutoff would then make exterior good indicators equal one and the local chart functions analytic on that event. The needed row-sum and margin, including actual chart constants, must be stated; “\(p_\beta=b\log(\beta a)\)” alone does not prove them.

**PROVED (the mixing counterexample).** For neighboring \(x\in G\setminus S_Q\) and \(y\in S_Q\), the Stieltjes walk series for \(K_G^{-1/2}\) contains a positive one-step contribution, so \(C_G(x,y)\ne0\). Consequently \(u_x=m_x+\beta^{-1/2}(C_G(x,y)\psi_y+\cdots)\). Even the analytic exterior factor \(f(u_x)=e^{t\|u_x\|^2}\) depends on the collar variable \(\psi_y\); integrating \(\psi_y\) changes the function of the remaining exterior variables.

**REFUTED (crude collar factorization).** The product law \(\gamma_G=\bigotimes_{x\in G}\gamma_x\) makes the \(\psi\)-coordinates independent, but it does not make the exterior observables independent of collar coordinates. Conditioning on collar \(\psi\) leaves exterior factors dependent on its value; integrating it first creates a generally nonlocal function. A bound for the collar integral does not yield an exact “free all-good factor times core weight” identity.

**PROVED (what a walk split does algebraically).** The identity \(C_G=C_\Lambda-(C_\Lambda-C_G)\) can be expanded into finite paths, as in L38.6: the difference contains walks visiting \(D\). Every term depending on a collar coordinate through \(C_\Lambda\) or \(C_G\) must also be marked linked. Assigning a term to the full visited path makes its dependence finite at each finite cutoff; the all-good terms are precisely those with no marked path or core dependence.

**OPEN (no free/linked factorization yet).** Replacing \(C_G\) by a finite walk cutoff inside \(\chi_G\mathcal J_Ge^{-\beta R}\) is not an equality unless the truncation remainder is retained or a compensator is inserted. A Taylor/telescoping expansion on the product cutoff can produce path-supported terms only after mixed derivative bounds, convergence, and a quantitative distance from the hard threshold are proved.

**PROVED (walk count at the unweighted level).** A walk from outside \(S_Q\) that reaches \(S_Q\) has a first boundary crossing. Summing geometric walk weights before and after that crossing gives a constant times the number of boundary edges, hence \(C|\partial S_Q|\), because \(q=2d/(2d+\nu_*)<1\). A factor \(B_{\rm ord}(\beta)\) may be attached only to a term whose chart/Taylor coefficient has that bound; it is not a property of the walk count itself.

**REFUTED (unweighted count implies the desired activity norm).** \(\sum|U|\le C|\partial S_Q|B_{\rm ord}\) controls a pointwise product by \(\exp(C|\partial S_Q|B_{\rm ord})\) after the \(U\)'s exist. It does not control \(\sum_{Y\ni Q}e^{\kappa_0|Y|}|\mathrm{activity}(Y)|\): a single term of size \(\epsilon\) supported on \(M\) blocks has unweighted size \(\epsilon\) but weighted size \(\epsilon e^{\kappa_0M}\).

**PROVED CONDITIONAL ON a sparse path support inequality for every marked term.** If each marked walk of length \(n\) is charged its actually visited \(s\)-blocks and \(|Y(w)\setminus W_Q|\le C_d(1+n/s)\), then \(q^n e^{\kappa_0|Y(w)\setminus W_Q|}\) is summable when its exponential rate is below \(-\log q\). KF0WalkHalo now proves this sort of block count and weighted bound for ordinary F.1 walk monomials; the analogous integrated bound for hole paths, loops, shifted chart factors and their unions is still needed.

**OPEN (the first genuine analytic estimate).** On the exterior cutoff event prove uniform mixed finite-difference/Taylor bounds for the chart Jacobian, normal remainder, source factor and physical good tests under all marked \(C_G-C_\Lambda\) paths and mean shifts. The proof must handle repeated paths incident at the same anchor, with constants summable after support weights. kf0SeriesBound_summable, kf0SeriesTerm_hasSum and the new ordinary KF0WalkHalo bounds do not supply these shifted, hard-sector bounds.

**PROVED (numeric reserve, separate from locality).** The Round-40 fixed-support estimate gives \(e^{-c\log^2(\beta a)-H_\beta|W_Q|}\) after specified normalizer and collar losses. If the linked-factor norm were \(e^{C|W_Q|B_{\rm ord}}\), a fixed \(H_\beta=H_0\log(\beta a)\) would pay it for large \(\beta\). This arithmetic does not prove the linked-factor norm or that its support is \(W_Q\).

**REFUTED (global product cutoff as a negligible event).** For fixed \(p_\beta\) and growing torus, \(\gamma_G(\forall x,\|\psi_x\|\le p_\beta)=\gamma_1(\|\psi\|\le p_\beta)^{|G|}\to0\). One cannot discard its complement by a one-core error. A normalized truncated product reference is possible, but then the complement must be restored by local fluctuation-tail sectors.

**PROVED (single-site tail strength).** For tangent dimension \(N-1\), a standard Gaussian obeys \(\gamma_1(\|\psi\|>p)\le C_N(1+p)^{N-1}e^{-p^2/2}\). At \(p=b\log(\beta a)\), this is \(e^{-b^2\log^2(\beta a)/2+O(\log\log\beta)}\). The polynomial factor can be absorbed by a smaller fixed exponent for large \(\beta\).

**REFUTED (an exact \(e^{-p_\beta^2/2}\) reserve for every \(N\)).** For tangent dimension at least three the radial Gaussian tail has a positive polynomial prefactor, so a dimension-uniform bare inequality with coefficient one and exponent exactly \(-p_\beta^2/2\) is false. The two-species budget must use the preceding weakened rate.

**OPEN (two-species closure).** Each \(\psi\)-large site or block is a fluctuation-type core, distinct from the physical bad block. An exact partition over both kinds and a closure rule must group those touching \(W_Q\), while unlinked fluctuation components cancel only after normalization/connected expansion. The landed KF0CollarClosure proves one-species components, disjoint dressed supports and sum_card_support_le; it does not prove mixed closure or its integral norm.

**PROVED CONDITIONAL ON path localization and mixed closure.** The determinant loops belong in the same linked family: H37.7 and the OR formula L38.5 mark every loop visiting \(D\), and a loop meeting two cores links them. The logdet identity kw_logdet_eq is landed; loop-occupancy and integrated support-weighted summation are separate obligations.

**REFUTED (one-core estimate automatically extends to many cores).** The core means add, collars can overlap, hole paths can visit several bad sets, and a determinant loop can join distinct cores. The landed sum_card_support_le gives \(\sum_I|S_I|\le\sum_Q|C_Q|\), useful geometry after closure, but it does not make the integral factor or supply a connected-family entropy bound.

## 3. What is needed to finish one core

**OPEN (precise one-core target).** After proving \(Z_{\varnothing}(g)\ne0\), construct \(A_Q(Y;g)\) on connected \(s\)-block supports \(Y\ni Q\), with the exact identity \(Z_{\{Q\}}(g)/Z_{\varnothing}(g)=\sum_{Y\ni Q}A_Q(Y;g)\) and \(\sum_{Y\ni Q}e^{\kappa_0|Y|}\sup_{\|g\|_1<1}|A_Q(Y;g)|\le Ce^{-c\log^2(\beta a)}\), uniformly in torus, \(\nu\), bin and regulators. Any source-independent vacuum factor must be accounted for on both sides.

**OPEN (first missing lemma).** An integrated marked-collar influence lemma must give an exact finite-support expansion of the conditional factor \(\chi_G(u)\mathcal J_G(u)e^{-\beta R(q,u)+g_G\Phi^+(u)}\) relative to the all-good factor, after collar \(\psi\) and \(q_D\) integration, with support-weighted norm and the real reserve retained. It must include the finite-walk truncation remainder, large-\(\psi\) sectors and determinant loops. Neither the row-sum bound nor the unweighted first-entry walk sum proves it.

**PROVED (analyticity in \(\psi\) is not a logical target).** The one-scale logarithm asks analyticity in \(g\). Polymer.decomposition is algebraic: its hypotheses are nonempty elementary supports and component-local admissibility. Scalar gas_pe assumes bounds on already scalar activities. Operator gasOp_pe assumes bounded, measurable, finite-support functions of a product field; it does not assume holomorphic dependence on \(\psi\). A real sup-norm/local-difference proof could therefore replace P7's exterior complex extension.

**PROVED CONDITIONAL ON a real local-difference proof.** Removing \(\psi\)-analyticity changes the proof method, not the missing estimate. Hard tests can remain measurable and discontinuous if all resulting local functions have exact DepOn support, Bdd and the required integral norm. Source analyticity follows separately from entire finite-volume factors and a uniform convergent source-ball polymer expansion.

**OPEN (complex normalization).** Even with one-core activities at \(g=0\), prove the ordinary \(Z_{\varnothing}(g)\) and then the full gas do not vanish on \(\|g\|_1<1\), with a chosen analytic logarithm and a bound uniform in volume. Positivity at \(g=0\) cannot be extended to complex \(g\) without a convergent expansion.

## 4. Literal landed gas interfaces

**PROVED (decomposition signature).** Polymer.decomposition requires hA0: every element of an admissible family has nonempty support, and hLoc: a family is admissible exactly when every contact component is admissible. It needs no probability measure, Bdd or DepOn. The proposed two-species closure must supply these two hypotheses before this theorem applies.

**PROVED (gas_pe objects).** In MayerPE.lean, gas_pe has finite block, coupling and heavy-index types; supports \(cy,zs,cr\), scalar weights \(\beta_y,\tau_z\), and a nonnegative support size \(d\). Its hz says \(zs(z)\ne\varnothing\), hcr says \(cr(z)\subseteq zs(z)\), hB says \(|\beta_y|\le B_0e^{-\kappa''d(cy(y))}\), and hτ says \(|\tau_z|\le e^{-p-h|zs(z)|}\). A physical one-core construction does not yet provide these scalar weights.

**PROVED (gas_pe geometry and entropy).** Its hd is \(d(Y)\ge0\); hzd is \(d(zs(z))\le c_2|zs(z)|\); hG3 is the connected-family union inequality with additive \(c(|C|-1)\); hent bounds \(\sum_{y:b\in cy(y)}e^{-(\kappa''-\kappa_g)d(cy(y))}\) by \(K_{0g}\); hcount bounds the number of heavy indices of support size \(v\) through a block by \(K_{0h}^v\). The physical support/closure lemma and grouped decoration count must supply these.

**PROVED (gas_pe size and numbers).** Its hG1 is \(|X|\le c_1(1+d(X))\). The remaining signs are hB0, hκg, hκ'', hc, hc1, hp, hK0g, hK1, hK0P, hκ', hcP. Its hh requires \(B_0e^{B_0}e^{\kappa_gc}K_{0g}+\kappa_g(c_2+c)+c_1+3+\log K_{0h}\le h\). A numeric budget lemma must turn the physical real reserve into that \(h\).

**PROVED (gas_pe polymer entropy).** hG2P bounds \(\sum_{Y\ni b}e^{-\kappa_{0P}d(Y)}\) by \(K_{0P}\); hG3P gives the cluster-union size bound with \(c_P n\). hκ requires \(\kappa'+\kappa_{0P}+c_1\le\kappa_g-2\); hα requires \(3c_1e^{-p}K_{0P}e^{c_1+\kappa'c_P}\le1\). Animal counting and choice of rates would supply these only after actual connected supports and the heavy activity rate are established.

**PROVED (gasOp_pe extra hypotheses).** GasOperator.lean adds a product of site probability measures \(\mu_b\), configuration-valued \(\beta_y,\tau_z\), hβd/hτd (DepOn their declared supports), hβm/hτm (Measurable), hβb/hτb (Bdd). Its hB is a pointwise sup bound on \(\beta_y\); its hτ is \(\int|\tau_z|\,d\mu\le e^{-p-h|zs(z)|}\). It retains all the scalar geometry, entropy, sign and numeric hypotheses above. This is the relevant interface for a conditional Gaussian sector.

**OPEN (physical supplier for gasOp_pe).** A one-core marked-collar lemma would supply hτ and hτd only after the core integral is assigned a finite \(zs(z)\); physical chart factors and the product cutoff would supply measurability and Bdd after exact truncation, while ordinary F.1 supplies hB/hβd only after its halo grouping. Mixed closure supplies hz,hcr,hzd,hG3,hcount; support counting supplies hent,hG1,hG2P,hG3P; a final constant budget supplies hh,hκ,hα. None is implied by kwOp_boundary_square alone.

**REFUTED (declaring the whole torus to be one heavy support).** The exact sector integrand in H37.6 depends through \(C_G\) on Gaussian variables throughout \(G\). Taking \(zs(z)=\Lambda\) makes DepOn true but asks hτ for \(e^{-p-h|\Lambda|}\), whereas the one-core reserve is \(e^{-p-h|W_Q|}\). Taking \(zs(z)=W_Q\) gives the right reserve size but DepOn is false before localization.

**PROVED (pe_blockTorus_frozen signature).** FrozenTorus.lean requires hε: \(0\le\epsilon\), hκ': \(0\le\kappa'\), hq: \((2d)^2e^{-(\kappa-\kappa'-\alpha)}<1\), hcond: \(\epsilon e^{-(\kappa-\kappa'-\alpha)}/[1-(2d)^2e^{-(\kappa-\kappa'-\alpha)}]\le\alpha\), and hK: every connected \(s\)-block polymer has \(|K(X)|\le\epsilon e^{-\kappa |X|/s^d}\). The missing physical connected activity supplies hK; an animal-count and constants lemma supplies hq/hcond.

**REFUTED (one core suffices for pe_blockTorus_frozen).** That theorem quantifies hK over every connected polymer, including supports containing several physical and fluctuation cores. A rooted one-core estimate is a necessary input to the full gas, not hK itself. Multi-core closure, cross-core loops/walks and connected summation remain.

## 5. Bounded Lean packages, conditional on mathematical proofs

**OPEN (package 1, Sonnet, at most 300 new lines per file).** New OneCoreGaussianIdentity: for every admissible torus, \(\nu\in[\nu_*,1]\), fixed \(D,q\) and \(\|g\|_1<1\), prove equality of the exact good-spin sphere integral and the shifted \(G_G\mathbb E_{\gamma_G}\) expression of §1, including all indicators, Jacobians, crossing terms, determinant and source. Split subset-site chart measure and shift/source ledger into separate files. Inputs are partitionFunction_eq_sum_kf0Sector, completed_square, kwOp_boundary_square, kwSqrt and lintegral_good_gaussian_change; the last does not by itself prove this identity.

**OPEN (package 2, Sonnet, at most 300 new lines per file).** New OneCoreCutoffImplication: prove uniformly in \(G\) that \(\sup_x\sum_y|C_G(x,y)|\le\nu^{-1/2}\), then, under an explicit strict cutoff-margin hypothesis on \(A,b\), show \(p_\beta\nu^{-1/2}+1/[2\log(\beta a)]\) lies inside the scaled good-chart cutoff and hence \(\chi_x=1\) for \(x\notin S_Q\) on \(\sup_y\|\psi_y\|\le p_\beta\). New OneCoreFluctuationSplit: prove the exact two-species partition and \(\gamma_1(\|\psi\|>p_\beta)\le C_N(1+p_\beta)^{N-1}e^{-p_\beta^2/2}\). Reuse mean_outside_collars and KF0CollarClosure; the killed-square-root walk identification remains a prerequisite.

**OPEN (package 3, strong, at most 300 new lines per file).** New OneCoreWalkLinked: give a finite-walk telescoping identity with an explicit remainder tending to zero, assign each path its true visited support \(Y(w)\), and prove \(\sum_{w:\,w\cap W_Q\ne\varnothing}|c_w|e^{\kappa_0|Y(w)\cup W_Q|}\le C|\partial W_Q|e^{\kappa_0|W_Q|}\) for paths starting outside \(W_Q\), at a rate satisfying the path-length entropy condition. Include external \(C_\Lambda\) paths that read collar \(\psi\), not only \(C_\Lambda-C_G\); treat rooted determinant loops in a separate file.

**OPEN (package 4, strong research input, at most 300 new lines per file).** New OneCoreHeavyNorm: prove the exact rooted activity identity and full source-ball weighted estimate displayed in §3 after integrating \(q_D\) and collar variables. Separate the integrated chart moment bound, repeated marked-path estimate, and rooted connected-family count. This is the first missing mathematical estimate; it cannot be discharged by an abstract instance.

**PROVED CONDITIONAL ON packages 1–4 (package 5, Sonnet, at most 300 new lines per file).** New OneCoreGasInput should state hβd, hτd, hβm, hτm, hβb, hτb, hB and hτ for the actual local functions of gasOp_pe. A separate numeric file should prove its geometry, entropy and rate inequalities. Extend from one to several cores before invoking gasOp_pe and pe_blockTorus_frozen.

**PROVED (collision check).** The proposed OneCore names above were searched in the current Lean tree and have no existing declarations. They name future packages, not landed theorems; every cited existing theorem name in this note was checked against its source file.

**PROVED (adversarial closeout).** The attempted repair of crude collar integration by a product Gaussian failed because exterior factors still read collar coordinates. The attempted repair by a first-entry walk count gives only an unweighted scalar bound, and the global product cutoff loses almost all probability at large volume. Finite-support localization with a weighted integrated norm is therefore the first unresolved gate for one core; full-source normalization and multi-core extension follow it. No complete one-core linked estimate is claimed.
