# Audit of LF-RECONSTRUCTION §II.7 and Part IV

**Verdict.** The two assembly theorems describe the clauses of the current Lean declarations in the right order and with the right field and torus domains. They are **not established by the present manuscript**. The flow cannot currently invoke LF-4 under its literal hypothesis (P4-01); the hard-spin base and the $k_f=0$ case contain indispensable sketches (P4-03, P4-06); and the unresolved Part III findings enter the assembly (P4-07). `Balaban.logPartition_multiscale` remains `DRAFT_SORRY` in the frozen manifest. The verdict concerns proof support, not a counterexample to either root statement.

## Scope and frozen evidence

This is a focused mathematical and statement-correspondence audit of §II.7, §§IV.0–IV.5, D-IV.2, D-IV.11, Table IV.5.5 and list IV.5.6. I read the exact frozen Root-F declaration and the current `RootFAndC1Star` definition, and checked the indicated P5–P7 source passages. I did not edit any file under `/home/scott/Balaban`. No Lean proof or build is claimed.

The manuscript is `notes/phase1/LF-RECONSTRUCTION.md` at Balaban commit `6114de31528d88ffbc92abcfb0d95ab156dbd200`; its last manuscript commit is `1b515d92941d722ebfd2f88ece8d7d03de519a9c`. Its SHA-256 is `be3e616a9a94b458d17a02606022fc7ce579b320b2ffaf8cb4a392757f52a0e6`. The Root-F file `Balaban/Frozen/Roots/LogPartitionMultiscale.lean` has SHA-256 `21833bea3211257ac51d0879ef9f692acb0021fb04e792375cf5257104380e40`; its manifest ID is `thm.RootF.logPartition_multiscale.v1`, state `DRAFT_SORRY`. `Balaban/Correlations/C1Star.lean` has SHA-256 `37bdffd07567bcfff63571d3f90a0536a5d7fd0a4f8ab8caa372fae2f3e291d3`. It calls itself a candidate interface and is not a frozen declaration. The source map is `review/SOURCES.md`, SHA-256 `f044419ba371379487573d5e291e9050c84055474a39bb126dced8d5e2b0f9fc`.

Other files used to expand the statement clauses and earlier findings are `frozen/manifest.json` (SHA-256 `8d3a4e3562316b391ab27960600fe368efd8176f161c7fa9a27b30c3393a8cb2`), `Balaban/Correlations/Clauses.lean` (`c6f2408dc6715e5112962ac4ca9f92c5ec6e376742eb11f4c48adf761eacde86`), `Balaban/Frozen/Geometry/IsPolymer.lean` (`906991e7c397b4b9e5cb87ff909d880a6e4b6ee9f2a10f406128d5ff5425a290`), `Balaban/Frozen/Model/PartitionFunction.lean` (`4648319116e15912b07f55b3393ac3de07bcf5db98836101ac34c041a0ccf626`) and `notes/phase1/LFR-PART3-AUDIT-astra.md` (`7230c76d5b3f52ba86c645e46888418b901d863458bf863fdb0756283ea529d7`).

For source checks I used P5 `s002200050433 (1).pdf` (SHA-256 `b3f0ef3491fc63b3988768893c1452b4bd1458a5f3e408e6af6000a555fd9a0f`), P6 `s002200050470.pdf` (`ee0ca061c9a7418d5da907a4dd09b66fb247f46bffcf68f83fa3ba502c342fc4`), and P7 `s002200050486.pdf` (`c48e08dd439878a0245cceb6e6aead787a8ce7671865f6360c8464a7e579d2e9`). P5–P7 are identified in `review/SOURCES.md`. I also inspected the earlier `astra-lemmaH/LEMMA_H.md` (SHA-256 `855b01766619ac1bfd20d3118f5d84286ef0e1592743815818344f58cfc15c83`); its open Lemma H is historical evidence, not a replacement for Part III's later construction.

Each finding below was tested against the most favorable reading of the stated definitions and subsequent amendments. A mathematical counterexample is distinguished from an insufficient cited estimate or an explicitly open proof obligation.

## Findings

### P4-01 — BLOCKER: the LF-4 hypothesis does not follow from the a priori regime test

**Location.** D-IV.11, manuscript lines 4186–4193; Theorem III.10.8, lines 3877–3881; Theorem IV.3.2 proof, lines 4638–4642. The theorem still says “$\beta_k\nu_k\le1$ for the running constants of $\mathrm{rep}$,” followed by a parenthetical instruction to read this as $k\le k_0$. LF-7 then invokes LF-4 for every $k+1\le k_0$.

**Argument and refutation.** D-IV.11 gives only
$$\beta_k\nu_k=(\beta\nu L^{kd})\gamma_k\delta_k\le e^{2\epsilon},$$
where $e^{2\epsilon}$ may exceed $1$. For example, the bounds (I.2) permit $\beta\nu L^{kd}=0.99$ and $\gamma_k\delta_k=1.05$; then $k\le k_0$ but $\beta_k\nu_k=1.0395>1$. The amended (D9) likewise contains $k\le k_0$, not the exact running inequality. I checked the possible rescue by (A-III.2) version 1.2: it is prose changing the intended reading, but it does not change the displayed binder of Theorem III.10.8 or reprove its estimates with the larger constant. Thus the induction's stated application is invalid. This is a logical counterexample to the implication used in LF-7, not to LF-4 under its original hypothesis.

**Repair.** Restate and reprove LF-4 with $1\le k\le k_0$ as its hypothesis, including every Part III estimate where $\beta_k\nu_k\le1$ was used. In particular III.6.4(c), line 3481, concludes a $<1$ bound after multiplying by $\beta_k\nu_k\le1$; the bound must retain a margin of at least $e^{2\epsilon}$. III.8.2, line 3546, needs its finite-dimensional remainder constant updated. Then update the theorem statement and the application in LF-7 together. Merely changing the parenthetical sentence does not close this finding.

### P4-02 — MAJOR: the chart's complex integral assertion is false as stated

**Location.** Lemma II.7.4(c), manuscript lines 4288–4302: for complex $e$ near the real sphere, “the right side of (b) is then analytic in $e$.” Part II's scale-zero fluctuation convention and Proposition II.7.9 use this representation.

**Counterexample and refutation.** Part (b) is a correct real Gaussian disintegration. Part (c) is asserted after “for every Borel $f\ge0$ (or integrable $f$)” in (b). A Borel $f$ need not even be defined on complex $P_e^\perp u$. The failure persists for a natural analytic extension of an integrable function. Take $N=2$, real $e_0=(1,0)$, $f(v)=(1+v\cdot v)^{-1}$ on the one-dimensional tangent space, and complex $e=(\sqrt{1+t^2},it)$, so $e\cdot e=1$ and $e\to e_0$ as $t\to0$. In a strip with $u_1$ bounded and $|u_2|\to\infty$, the factor $\exp[-s(e\cdot u)^2/2]$ grows in modulus like $\exp(s t^2u_2^2/2+O(|u_2|))$, whereas $f(P_e^\perp u)$ decays only polynomially. The purported integral is not absolutely convergent for any $t\ne0$. Restricting to smooth or real-analytic $f$ alone does not repair it. The real chart Jacobian in II.7.4(a) and identity II.7.4(b) survive this test.

**Repair.** State (c) only for the actual complete fluctuation integrand, after all Gaussian quadratic terms have been combined and a uniform positive real-part bound on a fixed real integration contour has been proved. Keep characteristic functions on real integration variables as in the repair of P3-02; do not analytically continue Borel indicators. Give the determinant and chart normalization in that same formula.

### P4-03 — MAJOR: the small-field base input is a load-bearing sketch

**Location.** Proposition II.7.9, lines 4370–4387, calls itself “cited/sketched”; Theorem II.7.10, lines 4389–4420, consumes it for (D1), (D2), (D7), the first RG coefficients and the family limit. IV.5.6 item 4 names I-8 and I-9 as sketched and item 11 still requires the chart-measure identification.

**Argument and refutation.** The real sphere chart and chord identity do give a plausible base construction. They do not prove the first localized small-field integral, the $\nu$-free RG system in regime (A), the complete-background system in regime (B), the new boundary estimate with $B_{\rm st}$, and the half-budget for $\mathcal R_m^{(1)}$. The paragraph “Status and route” lists these as obligations rather than proving them, and P4's first step treats a different, whole-lattice small-field setting. I found no P5–P7 theorem that supplies the stated hard-spin large-field base verbatim. Therefore LF-6 is conditional at exactly the input it needs for the global induction. This is an acknowledged proof gap, not a counterexample to the proposition.

**Repair.** Prove Proposition II.7.9 on each base record with the chart change of variables and its normalization, the localized covariance and cluster expansion, both RG systems, and the claimed uniform half-budget. Then verify the $\nu\downarrow0$ family limit after the chart integrand is corrected as in P4-02.

### P4-04 — MAJOR: the reduced-symmetry bound is weaker than the pre-class requires

**Location.** Lemma IV.1.8, lines 4517–4523; (D2) of $\mathrm{IsRep}^{\rm pre}_{k+1}$, lines 2540–2544; Theorem IV.1.1(b), lines 4426–4434. The manuscript itself marks N-IV-1 “UNCERTAIN (minor).”

**Argument and refutation.** P5 Proposition 3.2, p. 517, says that the localization terms of its function (3.9) satisfy (3.4) with $\frac12\beta_k^{-m-1}$ instead of $\beta_k^{-1}$. The pre-class at the next scale asks for $\frac12\beta_{k+1}^{-m-1}$. Since $\beta_{k+1}/\beta_k\asymp L^{d-2}>1$, the printed source estimate is weaker by roughly $L^{(d-2)(m+1)}$. The suggested repair in IV.1.8 cites $e^{-c\hat R_k}$ for *domain-dependent differences*, but P5 Proposition 3.2 also has whole-torus terms, explicitly equal to their unrestricted counterparts when $Y\subset\Omega''_{k+1}$; the cited difference estimate does not cover those terms. P5 p. 516, immediately before Proposition 3.2, says the **whole function** (3.9) is smaller than any prescribed power of $\beta_k^{-1}$, so a stronger bound may be obtainable. That prose does not supply the localized scale-$k+1$ coefficient and all its uniformity clauses. This is a gap in the stated proof, not evidence that the stronger result is false; its role in (D2) makes “minor” too weak a severity.

**Repair.** Prove a strengthened localization estimate for every term of (3.9), including whole-torus terms, with a coefficient at most $\frac12\beta_{k+1}^{-m-1}$, uniformly in the domains, torus and $g$. Alternatively change (D2), the LF-4 half-budget, and all downstream uses consistently to a weaker exponent; a local change to IV.1.8 alone is insufficient.

### P4-05 — MAJOR: LF-5's switching RG step is not supplied by the cited source

**Location.** D-IV.5, lines 4151–4156; Theorem IV.2.2(e) and proof, lines 4564–4594; IV.5.6 item 4 and O-II-2 in IV.O.4. The proof quotes P6 p. 11, “these contributions are very small,” and proposes a perturbation of the triangular matrix by $O(\beta^{-1})$.

**Argument and refutation.** P6's qualitative two-stage description supports the design of the switch: use $\nu$-free unrenormalized backgrounds and complete renormalized backgrounds. The theorem needs a quantitative solution of the changed RG equations that preserves the uniform $\xi$ estimate, the renormalization conditions, and the hypotheses of I-9 on subdomains. The manuscript says the Neumann-series condition $42\|E(p)\|\le1/2$ is a **Lean requirement (L1′)**, and IV.O.4 says the R-$\nu$ system is pending. I checked whether the bound $\beta_{k_0+1}\nu_{k_0+1}\le e^{2\epsilon}L^d$ by itself supplies the matrix perturbation estimate; it only gives an order of magnitude for the source, not the derivative or inverse bounds. LF-5(b),(e) and LF-7(d) therefore remain conditional on an unproved switching-system lemma. No counterexample to the switch itself was found.

**Repair.** State the exact switching RG map and prove its invertibility/contraction with constants before $\beta$, including the zeroth and first variations produced by the background change. Feed that result into I-7/I-9 and establish the same $\xi$ bound used in (I.2).

### P4-06 — BLOCKER: the $k_f=0$ branch is only sketched and its proposed local quadratic reduction omits boundary terms

**Location.** Proposition IV.4.3, lines 4724–4738; Theorem IV.5.3 proof items 5–6, lines 4803–4810. The proposition explicitly says “no source treats this case.”

**Counterexample to the route and refutation.** The frozen Root-F quantifies over every $\nu\in(0,1]$; the branch $\nu>\frac78L^{-2}$ has $k_f=0$ and must be proved. Item (iii) of the proposed route says the chart around constant $h$ has quadratic form $\beta\langle\xi,(-\Delta+\nu)\xi\rangle$ and “the interaction consists of the chart terms only.” This is true for the full lattice before splitting, but false for a small-field region conditioned on adjacent large-field spins. On a single crossing bond $\{x,y\}$, fix the large spin $\phi_y=q$ with $q$ having a nonzero tangent component at $h$. If $\phi_x(t)=h+tv+O(t^2)$ for $v\perp h$, then
$$\left.\frac{d}{dt}\frac12|\phi_x(t)-q|^2\right|_{t=0}=-q\cdot v\ne0.$$
Thus constant $h$ is not the constrained minimizer for the small-field region with that boundary value; there is a linear boundary source and a cross-bond interaction beyond chart terms. Reading the route as a global expansion does not solve this: the large spin is not in the small Gaussian integral and the cross term has to be placed and bounded in the polymer gas. The stated Cauchy and decay bounds for $T_1$, and torus agreement, remain a sketch.

**Repair.** Write the $k_f=0$ decomposition with crossing bonds retained as boundary activities (or solve the conditional massive background problem), prove a uniform small-field expansion and heavy-object bound, and then run the observable and torus-coherence estimates. The correct global chord identity can still be used, with the cross terms accounted for.

### P4-07 — BLOCKER: LF-7 imports unresolved Part III claims as if LF-4 were available

**Location.** Theorem IV.3.2 hypotheses and proof, lines 4619–4644; Table IV.5.5's “internal classes” and “operator bounds” rows, lines 4871–4874; IV.5.6 items 7–8. The user's existing `LFR-PART3-AUDIT-astra.md` at the same Balaban revision reports P3-01 through P3-05, which have not been repaired in the manuscript.

**Argument and refutation.** P3-01 identifies a missing support implication in III.7.1; P3-02 an undefined complex evaluation of a real indicator in III.9.5; P3-03 a nonanalytic front indicator retained in III.9.6; P3-04 an undersized volume constant; P3-05 a tentative operator-valued GAS/PE gap in III.10.5. LF-7 uses III.10.8 for every $R$ step and for the family limit, while LF-8/Root-F use its analytic $\mathcal R''_m$ and boundary terms. Rechecking the manuscript at lines 3696–3745 and 3818–3842 confirms these passages remain unchanged. P3-01–P3-04 have concrete refutation tests in the earlier audit; P3-05 retains `UNREFUTED-TENTATIVE` status and is not asserted false. The resulting dependency is a blocker to an unconditional final proof, although it is disclosed in IV.5.6.

**Repair.** Resolve P3-01–P3-04, prove or replace the operator-valued GAS step of P3-05, and re-audit III.10.8 under the a priori hypothesis repaired in P4-01 before using it in LF-7.

### P4-08 — MAJOR: the `C1Star` observable conclusions remain conditional on sketches

**Location.** Proposition IV.4.4, lines 4740–4755, explicitly labels the observable layer “sketched”; Theorem IV.5.4, lines 4816–4842; Table IV.5.5 rows `C1StarF2` and `C1StarF3`, lines 4864–4869; IV.5.6 item 10.

**Argument and refutation.** Differentiating (IV.4.3) does yield (IV.4.4) once the analytic identity is proved. It does not construct the layer $\mu_j$, the decomposition $G_J=C_J+R_J$, the finite-torus remainder bounds, or their limits. The cited OBS Theorem 3.1, Proposition 3.3 and Lemma 3.4 are marked sketched, and OBSR O-09 names the non-product Gaussian hole estimate as an open risk. Theorem IV.5.4 correctly lists these as inputs, but the table's “proved from LF-8 + OBS layer” must be read as conditional. The massive final covariance is a coherent correction of P9's printed last term; it is not a substitute for those estimates.

**Repair.** Land and audit the OBS layer, including the hole estimate and the $\nu\downarrow0$ limits, then verify the `C1StarF2`/`F3` bounds with the chosen $c_*$ and $c'$.

### P4-09 — MAJOR: the a priori radius substitution needs a source-estimate pass

**Location.** D-IV.2, lines 4129–4135, says source decay $e^{-R_j}$ “improves” on replacing $R_j^{\rm run}$ by $\hat R_j\ge R_j^{\rm run}$; the adapted uses include III.2.2 around line 3105, III.6.4(c) line 3481, III.8.2 around line 3546, and IV.1.3 lines 4464–4468. Earlier Part I lines 41–43 and 146 still define or characterize $R_j$ as running, while I.3.1 and IV.O.2 give the later flow override.

**Argument and refutation.** As a statement about an *already proved bound*, $|F|\le C e^{-R_j^{\rm run}}$ does **not** imply $|F|\le C e^{-\hat R_j}$; the desired right side is smaller. A larger collar can yield a stronger estimate if the localization/background response proof is rerun with that collar. IV.1.3 outlines such a rerun and (Λ28) pays a weakened $e^{-\hat R_k/2}$, which is plausible. The blanket claim in D-IV.2, however, does not show that each P5/P6/P7 source estimate and denominator input is valid with the changed geometry. I found no counterexample to the a priori construction itself, and the geometric inequalities (RH), separation and upper-size bounds are consistent under $R_j=\hat R_j$. This finding is specifically the missing analytic transport, not a claim that the geometric substitution is wrong.

**Repair.** For every source estimate used after D-IV.2, state whether its $R_j$ is an actual chosen separation or only a running-flow parameter. Rerun the estimates requiring separation with $\hat R_j$, recording their constants and the available exponent (for example $e^{-\hat R_j/2}$), and revise III.2.2, III.6.4, III.8.2 and IV.1.3 where needed. Remove the obsolete running-radius declarations from the operative flow text or mark them explicitly historical.

### P4-10 — MINOR: a strict horizon inequality misses the endpoint $\nu=1$

**Location.** Lemma IV.3.3(c) proof, manuscript lines 4651–4656. In the conventional $k_0=0$ branch it writes $L^{2\hat k_f}<\nu^{-1}<\beta$.

**Counterexample and refutation.** For $\nu=1$, $\hat k_f=0$, so the first strict inequality reads $1<1$. This parameter is allowed by (A-IV.2) and $\beta\ge\beta_0$ makes the conventional regime possible. The theorem's asserted horizon bound still holds trivially when $\hat k_f=0$; only this proof sentence is wrong. The preceding $\hat k_f\ge1$ branch supplies the strict inequality where it is needed.

**Repair.** Split off $\hat k_f=0$ before using $\nu L^{2\hat k_f}<1$, and verify the two inequalities directly there.

## Targeted assessment by section

The real statements of II.7.3–II.7.5 withstand direct elementary checks: the chord identity follows from $|\phi|=|\phi^{\rm b}|=1$, the hemisphere graph has Jacobian $(1-|\xi|^2)^{-1/2}$, and the real normal Gaussian identity has the stated normalization. The base-record geometry uses the a priori radius consistently after D-IV.2. The base witness exponents in II.7.8 have the expected signs and powers: a block failure costs order $L^{d-2}p_0(\beta)^2$, a bond or site failure costs order $p_0(\beta)^2$, and a fluctuation failure costs order $p_1(\beta)^2$. This is a stress test of those displayed factors, not a verification of the full kernel integral or Proposition II.7.9. P4-02 and P4-03 remain.

For LF-3, IV.1.2's transfer of the old characteristic functions and IV.1.4's Gaussian witness factorization are consistent with the amended (S1)–(S2): the $\chi'^{(k)}$ factors on $\Omega^c_{k+1}$ can be functions of $u=z_{k+1}\psi_{k+1}-Q\psi_k$. IV.1.3 is explicitly a cited localization input, conditional on LOC GM2. IV.1.5's distance argument uses the actual separation in I.3.5(f) and can make the old boundary contribution independent of $B_0$ once the adapted decay input holds. IV.1.6's rotation statement is for real indicators and analytic exponents; it inherits the complex-indicator problem P3-02 when used in Part III. IV.1.7 is conditional on the stated uniform expansions and their almost-everywhere limit. IV.1.8 has P4-04. Hence Theorem IV.1.1 is a conditional step theorem, not a closed proof of all its own cited obligations.

For LF-5, the transfer Lemma IV.2.1 is an algebraic change of class plus LF-2's frozen budget, and the frozen threshold $p_2(\beta_{k_0})$ in Corollary IV.2.3 is the correct type of bound for long frozen runs. The complete-background switch is P4-05. LF-7's a priori estimates in IV.3.3 were checked algebraically from (I.2), apart from the harmless endpoint slip P4-10. The family class IV.3.1 fixes the moving-torus and moving-threshold defects identified in earlier audits, subject to the uniform expansions. LF-7 is stopped by P4-01 and P4-07.

For LF-8, the volume conversion in IV.4.1 is dimensionally consistent: one $\pi_{k+1}$ cube contains $L^d$ scale-$k$ blocks, and the row-13 lower bound on $H_0$ can absorb $C'_E\lambda_k+C'_E$. The extra-step case of IV.4.2 uses the frozen threshold rather than the false running threshold of P6/P7. These checks do not verify P7's final fluctuation integral or the scalar GAS instantiation. The $k_f=0$ and correlation branches have P4-06 and P4-08.

**A priori choices.** After applying the explicit version-1.2 override, region rules, $X^\approx$, widths, windows, and $k_2,k_3$ are intended to use $\hat R_j$; I found no surviving *definition* forcing the running radius in that flow. The analytic bounds still need P4-09. The exact inequality $\beta_k\nu_k\le1$ does survive as the operative LF-4 hypothesis, and occurs in proofs III.6.4(c) and III.8.2; P4-01 is therefore a genuine failure of O-IV-4, not merely old notation. The older running definition of $k_0$ in I.1.1 and I.5.6 is superseded by IV.3.3 for the flow.

**IV.5.6 input ledger.** The list is not a list of already proved lemmas. Its items have these roles in the final proof:

| IV.5.6 item | Audit disposition |
|---|---|
| 1, background fields | Cited BG/Def-5 and I-2 input; no new Part IV contradiction found. The mass-dependent application at the last step retains its stated hypothesis. |
| 2, Green's functions | Cited coercivity, decay and massive-tail input; the extension to masses $\le2$ remains an explicit condition on the correlation assembly. |
| 3, localization | LOC GM2 and V1 are open; IV.1.3 is conditional on them and P4-09 requires the a priori collar estimate. |
| 4, small field | I-8/I-9 and (CONT) are sketched; the first step is P4-03 and the changed switching system is P4-05. |
| 5, analytic half of Lemma F | IV.1.3 is a stated route, not an independently proved localized analytic expansion. |
| 6, large-field small factors | P6 (3.4)–(3.9) supports the general witness mechanism; its adapted base chart and coefficient budget need P4-02–P4-04. |
| 7, $R$ | Conditional on the cited P7 estimates and the unresolved P3-01–P3-05; the a priori LF-4 hypothesis needs P4-01. |
| 8, polymer expansions | Scalar GAS/PE is appropriate for IV.4.1; Part III's operator-valued instance remains P3-05. |
| 9, last step | P7 supplies the positive-$k_f$ procedure conditionally; the $k_f=0$ branch is P4-06. |
| 10, observables | The listed OBS results are sketched or conditional; they are exactly the missing input in P4-08. |
| 11, geometry | The cited boundary-connectivity result is external; the chart-measure identification is still a base-case obligation in P4-03. |
| 12, errata readings | The P5 scale issue is P4-04; the massive final covariance is consistently used in IV.4.4 and `C1StarF3`; the P6 union reading is inherited from Part II. |

## Clause-by-clause verdict: frozen Root-F

The exact declaration is `Balaban.logPartition_multiscale (d N : ℕ) (hd : 3 ≤ d) (hN : 2 ≤ N)`. Its explicit top-level mathematical input binders are $d,N,hd,hN$ (source/typing), followed by $\exists\delta>0$, $\forall\kappa>0$, $\forall c_9>0$, $\exists L,M$, $\exists\beta_0$, $\forall\beta\ge\beta_0$, $\forall\nu\in(0,1]$, $\forall h,\|h\|=1$, $\exists\mathrm{kf}$, and $\exists T$. The torus and field binders below are inside the corresponding clauses, not earlier choices of constants. No extra mathematical premise is introduced by the manuscript's assembly; the manuscript's “assume cited inputs” belongs to its proof plan and is not a Lean binder. There are no EXCESS binders in the frozen declaration relative to the stated Root-F target. `NeZero ℓ` is a typing premise for the torus.

| Exact frozen clause | Manuscript correspondence | Verdict on statement / proof |
|---|---|---|
| $\exists\delta>0$ before $\kappa,c_9$; then $L\ge2,M\ge1,\beta_0$ before $\beta,\nu,h$ | IV.5.3 chooses $\delta=1/8$; rows 2–16 choose constants in that order, with $\lambda_*$ after $\kappa,c_9$ | **Exact order.** Threshold existence is conditional on the cited analytic inputs. |
| $\exists\mathrm{kf}$ with $L^{\mathrm{kf}}\sqrt\nu\le L$ and $1/2\le L^{\mathrm{kf}+1}\sqrt\nu$ | IV.5.1(a), $\mathrm{kf}=\hat k_f$ | **Matched.** The elementary scale bounds check. |
| One family $T(\ell,j,x,X,g)$ chosen before all torus clauses; every $\ell$ with $ML^{\mathrm{kf}+1}\mid\ell$ | D-IV.1; IV.5.2 defines $T$ for all $\ell$, zero on other tori | **Matched.** It is not merely a separate witness on each torus. |
| $T=0$ unless $1\le j\le\mathrm{kf}+1$, $x\in X$, and frozen `IsPolymer d ℓ (M*L^j) X` | IV.5.2; I.2.15 identifies connected unions of blocks with the frozen predicate | **Matched.** The zero padding when $\hat k_f=k_f+1$ is necessary and present. |
| Locality in $g|_X$ for every $j,x,X,g,g'$ | IV.5.3 item 3, (H.7), PE locality | **Matched conditionally.** Requires the stated localized source and polymer inputs. |
| `AnalyticOnNhd` on the **open** complex $\ell^1$ ball $\sum_y\sum_i\|g_y(i)\|<1$ | IV.5.3 item 4, (H.7), PE (d) | **Matched conditionally.** P3-02/03 obstruct the upstream analytic activity. |
| For all $j\in[1,\mathrm{kf}+1]$, $x,X,g$ with $\|g\|_{\ell^1}\le1/2$, the $c_9 L^{-j((d-2)/2+\delta)}e^{-\kappa X.card/(ML^j)^d}$ bound | IV.5.3 item 5; $|X|_\#=X.card/(ML^j)^d$ | **Exact domain and exponent.** Conditional on LF-8, the regrouping estimate and P4-04; $k_f=0$ has P4-06. |
| For every $g$ with $\|g\|_{\ell^1}<1$, the principal `Complex.log` of the exact frozen partition-function ratio equals $\sum g h+\sum_{j,x,X,i}g_i(x)T_{j,i}$ | II.7.1 and IV.4.3; IV.5.3 item 6 | **Matched formula.** The analytic identity and the $k_f=0$ branch remain conditional. |
| Agreement for **all** admissible $\ell,\ell'$, all $j$, $a\in A$, arbitrary finite $A\subset\mathbb Z^d$ in the strict coordinate box $4|y_\mu|<\ell,\ell'$, and arbitrary global $g$, evaluated through `ZMod.valMinAbs` | D-IV.9, IV.5.3 item 7; nonpolymers give zero on both sides | **Matched statement.** The proof needs full (D8) transport and PE (f); it is not established by locality alone. The strict box and agreement on the *images of A* are present. |

The bound clause is on the **closed half ball**, while analyticity and the identity are on the **open unit ball**. The manuscript uses these domains correctly. The logarithm and partition function in the Lean declaration are those of `Frozen/Model/PartitionFunction.lean`, and II.7.1 uses that Gibbs factor and the same non-normalized sphere measure. The formal root remains unproved.

## Clause-by-clause verdict: current `RootFAndC1Star`

The current definition has $d,N$ and $hN:2\le N$, then $\exists\delta>0,L,M,hL:3\le L,\beta_0$. It requires **Root-F clauses only at** $\kappa=\kappa_*:=2\log(8d^2)$ and $c_9=1$ for these same $L,M$, plus `Nonempty (C1Star d N L M hN)`. This is weaker than asserting the entire frozen Root-F for all $\kappa,c_9$, and IV.5.4 correctly obtains its conjunct by specializing IV.5.3. The `C1Star` structure has its own $\betaStar$; Lean does **not** require $\betaStar\le\beta_0$. IV.5.4's choice $\betaStar=\max\{\beta_0,\beta_0^{\rm O}\}$ matches that exact type. All `C1Star` structure constants are fields fixed before its `data : ∀ β ≥ βStar` binder.

| Current Lean clause | Manuscript correspondence | Verdict on statement / proof |
|---|---|---|
| Shared $L,M$, $L\ge3$, Root-F at $(\kappa_*,1)$ | IV.5.4 opening and IV.5.3 | **Matched**, conditional on Root-F. |
| Ranges for $a,\gamma_0,c_*,c_\xi,c',\rho_0,\rho_1$, and $\betaStar$ before $\beta$ | IV.5.4 choice list | **Matched** in order and type; positivity/range arithmetic is plausible from the cited SF/OBS choices. |
| For each $\beta\ge\betaStar$, witnesses $J,\xi,\mu,r_{tr},r_{lg},e_m$ and their torus/zero-field limits | IV.5.4 `data β` | **Matched witness scope.** Their existence is conditional on LF-7 and OBS. |
| $J\ge1$, $J(\nu)\to\infty$, $1/2\le L^J\sqrt\nu\le L^2$ | IV.5.1(c) | **Matched**; scale arithmetic checks. |
| `C1StarF1`: $\xi(\nu,k)$ bounded also at $\nu=0$, and right continuity at zero | IV.5.4 zero convention and LF-7(e) | **Matched conditionally** on SF (CONT) and the switching flow, P4-05. |
| `C1StarF2`: all $j\ge1,\nu\in[0,1],x$ bound and continuity, plus `blockM = magJ + em` on sufficiently large tori with $ML^{J+1}\mid\ell$ and $|em|\le c_*\beta^{-2}L^{-2J(d-2)}$ | IV.5.4, IV.4.4, OBS §5.3 | **Matched conditionally** on the observable layer, P4-08. The extra $\ell_0(\nu,x)$ is exactly in Lean. |
| `C1StarF3`: transverse and longitudinal decompositions when $2|x-y|_\infty<\ell$, both remainder bounds including $\nu^{(d-2)/2}$, limits along $(ML)^n\mid\ell$, then limits as $\nu\downarrow0$ | IV.5.4, D-IV.6, IV.4.4 and OBS Lemmas 5.3–5.4 | **Matched conditionally** on P4-08 and GREEN G-5. The massive last covariance is assigned to $r_{tr}$, as required by the current bound. |

The notation `blockM`, `blockGtr`, `blockGlg`, `mainTr`, `LimAlong` and `magJ` was checked against `C1Star.lean`; the manuscript's index shift $\sum_{j=1}^J\beta_{j-1}^{-1/2}\mu_j=\sum_{j<J}\beta_j^{-1/2}\mu_{j+1}$ is correct. This is statement correspondence, not a formal proof of the interface.

## Overall status and confidence

**Mathematical validity:** no counterexample to Root-F or `RootFAndC1Star` was found. There are direct counterexamples to an implication used in the flow (P4-01), to the chart assertion (P4-02), and to one step of the sketched $k_f=0$ route (P4-06). The other findings identify missing proofs or insufficient cited bounds. **Source fidelity:** the P5 Proposition 3.2 scale in P4-04 was checked in the P5 text layer; the P6 switch and P7 final step were checked at the indicated source passages, without rederiving their full analyses. **Formal status:** Root-F is `DRAFT_SORRY`; `RootFAndC1Star` is a current candidate interface. Neither is certified by this audit.

Confidence is **high** in P4-01, P4-02, P4-04's printed-bound mismatch, P4-06's crossing-bond objection, P4-10, and the exact Lean-clause comparisons. It is **medium** in the conditional assessments of the localization, GAS, observables and radius transport because their cited analytic proofs were not reconstructed line by line. P3-05 remains tentative as in the previous audit. Closeout requires resolution of P4-01–P4-10 and P3-01–P3-05, followed by a fresh audit of the amended induction and assembly. No source, frozen Lean file, or Balaban repository file was changed.
