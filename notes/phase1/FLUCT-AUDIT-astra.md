# Adversarial audit of FLUCTUATION.md

**Scope and snapshot.** I read /home/scott/Balaban/notes/phase1/FLUCTUATION.md, version 1, SHA-256 860d4b39e44d96a21d26d9dad4ef008bfd6ac9281b18537f5b2565b19763fb2a, against its named phase-1 inputs and the relevant landed Lean statements. The source map is /home/scott/Balaban/review/SOURCES.md. I checked the decisive printed formulas on images of P4 (/home/scott/Balaban/sources/Balaban.pdf), Commun. Math. Phys. **182** (1996), pp. 704, 712, 718 (PDF pp. 30, 38, 44), rather than trusting its OCR; P5 and P6 have usable text layers. No Lean build or independent full reproof of the cited BG, GR, LOC, SF or LFR inputs was attempted. All work was read-only in /home/scott/Balaban.

**Verdict.** The draft is a useful reconstruction, but the asserted complete I-8/I-9 step and O-2′ do **not** follow from the stated inputs. The strongest direct defect is the false termwise locality in Lemma 3.2. The modular boundary localization and old-action expansion are acknowledged sketches, and the complex H7 estimate in Theorem 4.2 uses a real cutoff outside its domain. The continuity and nu-free matrix claims have missing hypotheses. The scalar quadratic estimate for the switch and the arithmetic of (IC) survive the challenges below.

## Findings

### FL-A01 — BLOCKER: termwise subtraction leaves the support $X$

**Location.** FL §3.2, Lemma 3.2(ii)–(iv), (3.1)–(3.2), lines 449–481; SF (H.4) and its forward-difference convention, SMALLFIELD.md lines 67–69, 126 and 157; landed Balaban/SmallField/RenormTheorem.lean, renormalization_local.

**Argument.** $\Phi_{y,X}$ uses the forward differences $\partial_\mu\psi(y)$. Nothing in (H.4) says that $X\ni y$ contains the whole star of $y$. Take a permitted $X$ with $y$ on its boundary and $y+e_\mu\notin X$. A nonzero $S_X^{\mu\mu}$ makes $\Phi_{y,X}$, and therefore $I(y,X)$, vary when only $\psi(y+e_\mu)$ varies. An explicit cancellation example uses two localized, individually $O(N)$-invariant terms $\mathscr E(y,X)=t\,\psi(y)\cdot\psi(y-e_\mu)$ and $\mathscr E(y,X')=-t\,\psi(y)\cdot\psi(y-e_\mu)$, with $X'\supset X$ and $y-e_\mu\in X$. Their sum is zero, so every (H.5) cancellation holds; each term can meet (H.4) with small $t$. Its transverse Hessian has a nonzero second moment for each term, of opposite sign. The summed $\Phi$ cancels, but each summand probes $y+e_\mu$ outside $X$. The landed theorem bounds the sum over $X$, not this asserted local decomposition. The same defect infects the claim that $I^W(y,X)$ depends only on $X\cap W$.

**Repair.** Construct termwise counterterms on a support containing $\operatorname{st}(y)$, then prove the enlargement cost in the covering rate and the exact cancellations. Alternatively use gradients based on sites inside $X$ and rederive the SF remainder. State and prove a genuinely termwise local I-6 before feeding its terms to I-5.

### FL-A02 — BLOCKER: Proposition 3.3 uses an unproved modular localization theorem

**Location.** FL Lemma 2.8, lines 364–372; (Vmod), lines 491–497; Proposition 3.3, lines 499–544, especially the old-boundary-term paragraph; Theorem 3.1(c), lines 414–433; LOC Theorem I-5, LOCALIZATION.md lines 362–379 and LOC open item 5.

**Argument.** LOC I-5 is stated with its ordinary covering geometry, a nested $X\subset X_1\subset\Omega_{k+1}$ and specified margins. It does not assert (Vmod) for a support crossing several components of the hole, or admissibility of the new interface in $\mathbb B^\sharp_{k+1}$. FL itself labels both (Vmod) and the decisive margins in Lemma 2.8 as sketches. Its argument that a tree can pass through $\Omega^c$ without modular cost does not prove the needed decoupling, GM2, support, or domain assertions for every component. Proposition 3.3's boundary estimate $\beta_k^{-3/2}e^{-(2\kappa-1)d^{\rm cov}(Y\bmod\Omega^c)}$ therefore has no established input. This is precisely the part needed to remove $B_0$ from the new boundary constant in Theorems 3.1(c) and 5.4. The nonmodular V-part is also conditional on LOC's still-open NC and Lemma 2.8. Variant (V0) is plausible from LOC's Lemma DL: this finding does not challenge its basic domain substitution.

**Repair.** State a modular I-5 with all source and target generating sets, margins, component rules, analyticity spaces, constants, and quantifiers. Prove its decoupled geometry and NC for $\mathbb B^\sharp_{k+1}$, then rerun the old-boundary resummation. Until then label Proposition 3.3 and Theorem 3.1(c) conditional.

### FL-A03 — MAJOR: the old-action expansion is still an input, not a result

**Location.** FL Theorem 3.1(f), lines 432–433 and proof lines 685–691; Theorem 5.4, lines 905–914; P6 Propositions 2.1–2.2, pp. 10–15.

**Argument.** FL explicitly calls (f) sketched and says its remaining details are not rederived. Theorem 5.4 then uses (f) to place changes of the old action and background into the boundary class, including the rate $2\kappa-\kappa_0-1$. Citing P6's original propositions does not itself verify their chosen-cover, modular-size, H7, and nu-free/complete versions claimed here. Thus the theorem 5.4 proof is explicitly conditional, contrary to any full I-9 closure claim.

**Repair.** Supply the P6 Propositions 2.1–2.2 argument in the exact present domains and conventions, including the $k=k_0$ step and observable counterpart, or state those versions as formal hypotheses.

### FL-A04 — BLOCKER: the H7 bound for O-2′ imports a real smallness estimate

**Location.** FL Theorem 4.2, proof Steps 1–3 and $(\Lambda28')$, lines 740–774; LFR Definition II.3.5, LF-RECONSTRUCTION.md lines 2096–2110; LFR $(\Lambda28)$, line 4997.

**Argument.** Steps 1–2 obtain $|\delta\Psi(s)|\le C\delta_k$ from the support of real characteristic functions. Step 3 then bounds every other factor of the action by $O(\delta_k)$ and asserts the same $C_Fp_0(\beta_k)^2e^{-\gamma_wD_k}$ on the **complex H7 domain**. H7 is defined with $\varepsilon_j$ radii, not a real $\delta_k=\beta_k^{-1/2}p_0(\beta_k)$ cutoff. In general $\varepsilon_j/\delta_j$ grows with $\beta$. Neither the real cutoff nor its $O(\delta_k)$ bound extends to all H7 points. Consequently the first inequality of (4.3), its Cauchy use in the localization, and the stated $(\Lambda28')$ do not follow. The printed LFR $(\Lambda28)$ has a different prefactor, $C_FK_3K_4A_0x^{p_0}e^x$, consistent with the need to budget a larger complex-domain quantity; it is not evidence for FL's $p_0^2$ prefactor.

**Repair.** Prove a decoupled complex bound from the actual H7 inequalities, with the resulting $\beta_{k+1}\varepsilon^2$ or sharper prefactor, and replace $(\Lambda28')$ by an explicit condition absorbing it. Check that condition in the order of §1.5. Separately prove the real estimate if useful. This may be repairable by the distance exponential, but that absorption is currently absent.

### FL-A05 — MAJOR: some terms in Theorem 4.2 have no stated modular size

**Location.** FL Definition 1.1, lines 99–102; Theorem 4.2 (4.2)–(4.3) and proof Step 4, lines 742–769.

**Argument.** $d^{\rm cov}(Y\bmod\Omega^c)$ is defined only for $Y\cap\Omega\ne\varnothing$. Formula (4.2) sums over all $Y\in\mathcal D_{k+1}(\bmod\Omega^c)$, while Step 4 groups by $S=Y\cap\Omega$ without excluding $S=\varnothing$. The prelocalized cubes $\square\subset X_{Z'}$ can lie in the newly bad region. For such terms (4.3) and $\hat Y(S)$ are undefined. The sentence that terms inside one $Z_{k+1}$ component go to $b_k$ is a plausible disposition, but the displayed expansion and estimate precede that split.

**Repair.** Split $Y\cap\Omega=\varnothing$ into $b_k$ before writing the modular expansion, and prove that every term retained in $\Delta$ intersects $\Omega$.

### FL-A06 — MAJOR: the two-mark hypothesis exceeds the landed Mayer bound

**Location.** FL Theorem 3.4, (3.5) and two-mark proof, lines 552–578; Balaban/Polymer/MayerMarked.lean, theorem mayer_marked, lines 81–103.

**Argument.** The theorem allows $\varepsilon_H=\varepsilon_{\rm PE}$. With the proposed two mark radii, FL sets $H_0=2\varepsilon_HK_0+\varepsilon_{\rm PE}$ and claims $H_0\le2\varepsilon_{\rm PE}$; that inequality fails for $K_0\ge1$. More fundamentally, the one-mark application already saturates the landed hα condition when $\varepsilon_H=\varepsilon_{\rm PE}$. Two positive-radius marks cannot fit under the same hα at equality. The asserted two-mark coefficient and OBS X2 do not follow from (3.5). The one-mark proof has no such immediate arithmetic defect.

**Repair.** Reserve strict activity slack, for example strengthen $\varepsilon_H$ by a factor depending on $K_0$ and reduce the radii, then recheck hH0, hq, hκ, hα and the final two-variable Cauchy constant. State the strengthened assumption in Theorem 3.4.

### FL-A07 — MAJOR: the switch's scalar cost is sound, its RG conclusion is not shown

**Location.** FL Lemma 2.9, lines 380–400; SF switch discussion, SMALLFIELD.md lines 347 onward; Balaban/Flow/RGInfty.lean, rg_step_infty, lines 51–75.

**Argument.** The chord identity and $\beta_{k+1,u}\nu_{k+1,u}\le e^{2\epsilon}L^d$ do yield $\beta_{k+1,u}|\delta\phi|^2=O(\beta_{k+1,u}^{-1})$ per block. But the proof of part (c) says the added terms do not depend on $\xi$. In the renormalized action the argument is $\theta=(1+\zeta)\psi$, and the two backgrounds and the re-expression terms vary with this argument, hence with $\xi_1$. Their derivatives can enter the RG matrix and nonlinear terms. The displayed bound $C_{\rm sw}\beta^{-2}\varepsilon_{k+1}^{-2}$ also discards the scale factor needed by rg_step_infty's hηbd, $\eta\le B(2/\alpha_0^2)\beta^{-1}L^{-2\gamma(k+1)}$. Thus preservation of the complete-convention (H.5), the matrix bound, and the claimed perturbation of hcond are not proved. The observable re-expression also needs its own H7 estimate.

**Repair.** Expand the switched density jointly in $(\psi,\xi)$ on the complete-convention polydisc, bound all derivatives entering the three renormalization conditions, and retain $\beta_{k+1}^{-1}\varepsilon_{k+1}^{-2}$ in the step data. Then apply the actual RG theorem with a verified matrix and hηbd. Keep the quadratic per-block lemma as a separate result.

### FL-A08 — BLOCKER: the nu-free matrix input assumes an uncomputed coefficient

**Location.** FL Theorems 5.1–5.2, §5.2 Step 7, lines 832–841, and open item 5, line 1019; SMALLFIELD.md lines 335–345; Balaban/Flow/MatrixFree.lean lines 13–23 and 87–93.

**Argument.** SF explicitly leaves $\varrho_{31}$ and the final $\tilde f_3,\tilde c_3$ uncomputed. The landed triangularBounds_matrixFree theorem takes an arbitrary $r$ with hypotheses $|r|\le C$ and $mC\le12/5$; it does not identify the coefficient of the actual fluctuation integral or prove those bounds for it. rg_step_infty takes TriangularBounds and analytic $c,f$ as hypotheses. Invoking these declarations as if they settled the actual nu-free system is a hypothesis mismatch, so the step for $k<k_0$ remains open even if the complete-convention estimates work.

**Repair.** Derive the actual nu-free divided equations and $\varrho_{31}$, prove the stated bound and analytic data estimates, and only then instantiate matrixFree and rg_step_infty.

### FL-A09 — BLOCKER: pointwise class membership does not imply (CONT)

**Location.** FL Theorem 5.3, lines 807–809, Lemma 5.8 and proof, lines 882–897; SMALLFIELD.md class definition lines 60–80; LF-RECONSTRUCTION.md Definition II.6.4, lines 2578–2594.

**Argument.** Theorem 5.3 quantifies over a flow from $\rho_1\in\mathbb R^{\rm sf}_1$ without displaying a continuous **family** premise in $\nu$. The fixed-$\nu$ class imposes no relation between different $\nu$ values. One may multiply a sufficiently small admissible localized kernel by $1+t\sin(1/\nu)$; all pointwise bounds and renormalization conditions can remain true, while there is no $\nu\downarrow0$ limit. LFR explicitly records this example and introduces IsRepFam for the missing predicate. Lemma 5.8 correctly **assumes** (CONT), so it cannot establish the unconditional limit in Theorem 5.3 by induction. FL §5.1 says to read “(CONT) as a clause”; that announces the needed amendment, but neither the cited fixed-$\nu$ class nor Theorem 5.3's displayed premise specifies the family object or its common data.

**Repair.** Quantify over a common family $\rho_1(\nu)$ satisfying a stated (CONT) or IsRepFam base condition, and show its preservation. For the physical construction cite and verify the LF-6 base family. Keep the pointwise flow bounds and the family-limit conclusion as separate statements.

### FL-A10 — MAJOR: the beta threshold has the wrong quantifier order

**Location.** FL §1.5, lines 174–185; Theorem 5.1, lines 796–799; §5.2 Step 8, lines 848–855; printed P4 p. 718, (5.39)–(5.41).

**Argument.** Theorem 5.1 says there exist $\alpha_0^*,E_0^*,\beta_*$ such that the result holds for **every** $0<\alpha_0\le\alpha_0^*$, every $E_0\ge E_0^*$ and every $\beta\ge\beta_*$. Its own Step 8 requires
$$168C_5E_0B_6K_5\,\alpha_0^{-2}\beta^{-1}\le1.$$
No fixed finite $\beta_*$ enforces this for arbitrarily small $\alpha_0$ or unbounded $E_0$. The order in §1.5, with $\alpha_0,E_0$ fixed before $\beta$, is the workable order; P4 (5.41) likewise imposes a threshold after its constants are selected.

**Repair.** State $\forall\,\alpha_0\in(0,\alpha_0^*],\,E_0\ge E_0^*\,\exists\,\beta_*(\alpha_0,E_0)$, or fix $\alpha_0,E_0$ before the theorem's existential threshold.

### FL-A11 — MAJOR: the analyticity-domain correction is right but not yet an input class

**Location.** FL Finding F-1, lines 159–169; SMALLFIELD.md ruling (iv), line 111; LF-RECONSTRUCTION.md Def-7 (D2), lines 2509–2511; LOCALIZATION.md Lemma DL, lines 362–369; printed P4 p. 704, (4.19).

**Argument.** The produced local terms naturally live on $\Xi^c_j(\mathbb B_j(X);1,\varepsilon_j)$. That is the domain used in P4 (4.19) and accepted by LOC Lemma DL for the next step; FL's diagnosis of F-1 is substantively correct. SF (H.4) itself lists XiC, but its later ruling (iv) changes Def-6 to the data domain, and Def-7 (D2) still demands that larger formulation. FL announces a replacement but no amended predicate is supplied as a cited input. As written, Theorems 5.1 and 5.4 cannot literally claim preservation of those existing classes. The complex sets and their perturbation margins also need open-neighbourhood versions for Cauchy estimates.

**Repair.** Amend both class definitions and every consumer to the XiC domain, prove the exact DL input/output inclusions with the landed constants, and specify the open analytic neighbourhood. Then restate the induction against the amended classes.

### FL-A12 — MAJOR: the abstract Mayer interface has an unproved support-size instantiation

**Location.** FL Definition 1.1, lines 99–102; Theorem 3.4, lines 552–578; Balaban/Polymer/MayerPE.lean, mayer_pe, lines 37 onward; Balaban/Polymer/MayerMarked.lean, mayer_marked, lines 81–103.

**Argument.** FL sets $d_\Omega(S)=+\infty$ when $\hat Y(S)$ is disconnected. The landed theorems are formulated with a real-valued $d$ on every nonempty support and require G1, G2 and G3 on that entire finite support type. Replacing infinity by zero weight in informal sums does not instantiate those Lean hypotheses, and restricting to connected $S$ is not automatic because unions appear in the cluster expansion. This is a formal applicability gap, distinct from FL-A06.

**Repair.** Choose a finite real extension of $d_\Omega$ satisfying the required inequalities, or formulate and prove a restricted-support Mayer theorem stable under connected cluster unions. Then provide the G1–G3 witnesses.

### FL-A13 — MINOR: the theorem-status labels overstate conditional proofs

**Location.** FL summary table, lines 20–65; status paragraphs after Theorems 3.1, 4.2 and 5.4.

**Argument.** The summary calls several results “proved given inputs” while its own inputs include NC, the auxiliary-cover margins, (Vmod), Theorem 3.1(f), the nu-free coefficient, and the $k=0$ covariance analogue, all explicitly open or sketched in the named notes. This is a status error even where no counterexample to the eventual mathematical claim is known.

**Repair.** Distinguish an algebraic identity, a proof conditional on a *proved* external theorem, and a proof conditional on an open assertion. Do not present the full I-8/I-9 chain as proved until the latter assertions are discharged.

## Per-statement verdicts

“Conditional” means the stated result might hold but the cited inputs and written proof do not currently establish it. “No specific defect” is limited to the checks described in the scope.

| Statement | Verdict | Principal reason |
|---|---|---|
| Definition 1.1; Lemma 1.2 | Conditional | Modular geometry is plausible; the $+\infty$ convention does not directly instantiate landed Mayer size hypotheses (FL-A12). |
| Definition 2.1 | Definition accepted | The two conventions are explicit. |
| Lemma 2.2 | No specific defect found | Gaussian minimization and the real hard-spin global-minimum argument fit the cited BG input on its domain. |
| Lemma 2.3 | No specific defect found | Chord expansion and the nu-free additional term are algebraically consistent. |
| Lemma 2.4 | Conditional | Kernel/square-root conclusions rely on the cited GR/LOC bounds, including the extra sup-norm summability argument. |
| Lemma 2.5 | Conditional | Product cutoff follows from its cited background and covariance estimates. |
| Proposition 2.6 | Algebra accepted conditionally | Real integral identity is formal; complex logarithms require a valid Mayer nonvanishing application. |
| Definition 2.7; Lemma 2.8 | Definition accepted; lemma open | New-interface margins and NC are sketched (FL-A02). |
| Lemma 2.9 | Part (a) and scalar estimate credible; (b),(c) open | Joint $\xi$ dependence and scale-sensitive RG data unproved (FL-A07). |
| Theorem 3.1(a),(b),(d),(e) | Conditional | Depend on Proposition 3.3, termwise Lemma 3.2, cover and cluster inputs. |
| Theorem 3.1(c) | Open | Modular old-boundary localization is missing (FL-A02). |
| Theorem 3.1(f) | Open | Source proposition transfer remains sketched (FL-A03). |
| Theorem 3.1(g),(h) | Conditional | Renormalization expansions depend on the same localization and analytic-domain interfaces. |
| Lemma 3.2 | False as stated | Termwise locality (ii) fails; (iii),(iv) cannot be used in I-5 in that form (FL-A01). |
| Variants (V0), (Vmod) | V0 plausible; Vmod open | V0 follows the evaluation locus; Vmod lacks the modular decoupling proof (FL-A02). |
| Proposition 3.3 | Open | Uses false termwise locality and unproved modular/cover inputs (FL-A01–A02). |
| Theorem 3.4 | One mark conditional; two marks unproved | Two-mark activity exceeds hα; real-size instantiation incomplete (FL-A06, FL-A12). |
| Lemma 3.5 | No specific defect found | Exact renormalization identity is algebraic, conditional on the defined backgrounds. |
| (IC), §3.7 | Correct arithmetic | $\kappa_b\ge3\kappa/2$ is exactly $\kappa\ge7+8\kappa_0+2c_1$; see Q4 below. |
| Lemma 4.1 | Conditional | Far-data decay uses the cited weighted estimates. |
| Theorem 4.2 | Unproved as stated | Real cutoff is used for complex H7 and empty-intersection terms lack a size (FL-A04–A05). |
| Corollary 4.3 | Conditional | Inherits the Theorem 4.2 domain and bound issue. |
| Theorem 5.1 | Unproved; literal quantifiers false | Upstream gaps, class-domain mismatch, nu-free matrix and beta threshold (FL-A01–A04, A08, A10–A11). |
| Theorem 5.2 | Conditional | Equations are a consistent target; actual nu-free matrix and switch inputs missing (FL-A07–A08). |
| Theorem 5.3 | False as stated for arbitrary pointwise inputs | The $\nu\downarrow0$ limit needs a family hypothesis (FL-A09). |
| Theorem 5.4 | Open | Depends on (Vmod), Theorem 3.1(f), O-2′ and the amended class (FL-A02–A05, A11). |
| Lemmas 5.5–5.7 | No specific defect found within cited inputs | P4 pp. 704, 712, 718 support the key domain and B1 formulas; downstream use remains conditional. |
| Lemma 5.8 | Plausible conditional family lemma | Its (CONT) premise is indispensable and is absent from Theorem 5.3. |

## Constants, Lean statements, and Q4

The arithmetic of §1.5 and §3.7 itself closes in the stated *selection order*: choose $L,\kappa_0,\kappa,\kappa_1,M,\alpha_0,E_0$ and then $\beta$ and the late threshold $\lambda_*$. In particular $c_1=(2L+3)^d\le\kappa_0$ and $\kappa_{\rm flow}\ge16\kappa_0+16$ imply (IC). The assertion that a single $\beta_*$ works uniformly over all allowed $\alpha_0,E_0$ is the separate quantifier failure FL-A10. For $(\Lambda28')$, eventual exponential absorption is credible because its distance is quadratic in $x$; the actual complex prefactor must first be established (FL-A04). Neither a favorable exponential nor a late choice of $\beta$ repairs a false H7 bound.

I searched the named Lean declarations cited in FL's introduction and §1.3; they exist. The BG/I-2 group includes prop51_*, lemma53, linearResponse, isEL_compose, theorem73_real, theorem73_complex and prop64. The GR/LOC group includes constrainedOp, constrained_G2v, xVariant_constrained_reduction, abstract_expansion, gm2–gm4 and the dg1–dg6/i4a_*/i4b_* families. The SF/PE/RG group includes Xi, XiC, GapE, renormalization_local, pe_xi_eq_exp, pe_PY_bound, mayer_pe, mayer_marked, norm_D1_Ff_le, pe_hole, exists_rg_solution_triangular, matrixFree, matrixInfty, matrixSel, rg_step_infty, rg_flow_infty and tendsto_rg_solution. The additional named finite-volume and flow declarations cited in the text, including Aterm_torus_sum, isWeight_of_dist, dirichlet_weighted, norm_xi_le_of_step and norm_gammaSeq_le, were found as well. Existence is not a proof of the proposed instantiation: renormalization_local controls the **sum**, triangularBounds_matrixFree assumes a bounded external $r$, rg_step_infty assumes TriangularBounds and the scale-dependent hηbd, and mayer_marked assumes hq/hκ/hα. The LOC decoupled declarations are similarly conditional on their structural specifications and NC. These interface distinctions drive FL-A01, A06–A08 and A12.

**Q4.** The landed PE-L proof in Balaban/Polymer/Size.lean, size_entropy, lines 79–105, defines $\alpha=\varepsilon K_0e^{c_1+\kappa'c}$ and uses $\alpha\le1$ to pay $\alpha|Y|\le c_1(1+d(Y))$. On paper it can be sharpened: set $\alpha=\varepsilon K_0e^{1+\kappa'c}$ and assume $\alpha c_1\le1$. Then $\alpha|Y|\le1+d(Y)$, so the required rate becomes $\kappa\ge\kappa'+\kappa_0+1$, with smallness $\varepsilon K_0c_1e^{1+\kappa'c}\le1$. This must be propagated through pe_size, mayer_pe and mayer_marked, not asserted from the landed theorem. **Keep (IC) and the landed mayer_pe for this campaign.** The already chosen $\kappa_{\rm flow}\ge16\kappa_0+16$, with $c_1\le\kappa_0$, satisfies (IC) with room; the sharpening changes no controlling choice and does not solve the two-mark slack or modular interface defects.

**Confidence.** High in FL-A01, A06, A08–A11 and the (IC)/Q4 arithmetic: they follow from explicit formulas or theorem premises. Moderate in the proposed repairs for FL-A02–A05, A07 and A12: those require fresh source-level proofs and may uncover further constraints. The audit is adversarial but not an exhaustive rederivation of every cited BG/GR/LOC estimate or every P1–P4 scan page.
