# Refute-first audit of LF-RECONSTRUCTION, Part I v1.1 and Part II

**Verdict.** The eight repairs to Part I address P1-01–P1-08 at the points identified in the earlier audit. In particular, fixing $M/M_1=L^{m_0(d,L)}$ before choosing $\kappa_1$ removes the contradictory unbounded ratio. Part II does **not** close as an inductive class. The frozen variant invokes Def-6 beyond its stated mass range (P2-01). The quiet-step bound has an invalid volume argument (P2-02). The class does not carry the large-field continuity required for the observable limit (P2-03), and its $g$-dependent operators conflict with a premise of `OBSERVABLES.md` §4.1 (P2-04). The proposed free-flow replacement for P7's exact composition remains a quantitative gap (P2-05). The conditional algebra of Lemma B and the summability count survived the checks below. Confidence is high for P2-01, P2-03 and P2-04; medium for the proof gaps P2-02, P2-05 and P2-06. This is a paper audit, not a Lean verification.

## Frozen inputs, scope, and method

The target is **the committed version** of `notes/phase1/LF-RECONSTRUCTION.md` at git commit `28afe9252da69e04f66c21f2953433264654545e`, SHA-256 `ecde70f6e3a6e3009034715d30f958a6a5733b27ffda28b53ff105587105484e` (`frozen-v1`, 2,652 lines). A read-only copy in this scratch directory was used for line numbers. The live file had an unrelated, uncommitted ten-line change when the audit began; it was not used to classify findings. The earlier audit `LFR-PART1-AUDIT-astra.md` has SHA-256 `78f1bf5cabbc73db9c2621637f8be060d9514e9b9e82cb0c8113455cfcf68118`.

The source PDFs are P5 `s002200050433 (1).pdf` (SHA-256 `b3f0ef3491fc63b3988768893c1452b4bd1458a5f3e408e6af6000a555fd9a0f`), P6 `s002200050470.pdf` (`ee0ca061c9a7418d5da907a4dd09b66fb247f46bffcf68f83fa3ba502c342fc4`), and P7 `s002200050486.pdf` (`c48e08dd439878a0245cceb6e6aead787a8ce7671865f6360c8464a7e579d2e9`), as mapped by `review/SOURCES.md`. Their text layers were extracted locally with `pdftotext -layout`; equations (1.24)–(1.27), (2.7), (2.9), (2.55)–(2.57), and P6 (3.2), (3.9)–(3.11) were compared with the target. The companion notes used were `BACKGROUND.md` v2 (`1cae63f726c1fdc5c04d5de86dcfe16316a89804ec1ba46af67c2f99037a5a0d`), `SMALLFIELD.md` (`a1bd76005194e48cae978a486b755393683ae811c9f5741505f97caeb764ef52`), `LOCALIZATION.md` (`00e1e1b247932610d3011a4533fab2ae6003ecafcfe18b74df93162a0267fd71`), and `OBSERVABLES.md` (`3e832e7687206335ecb50ea14b9802cc6f9265cba0115198ad711e131d634753`). All these inputs were read only.

This is a focused, tier-2 mathematical and source-correspondence audit. I first checked the exact stated hypotheses, then sought finite geometric histories, scalar Gaussian models, and parameter families that would refute the claims. I rechecked each proposed finding against the point-of-use hypotheses and the cited source passage. `UNREFUTED-TENTATIVE` below means a proof obligation, not a demonstrated false theorem. I did not audit the cited P3 localization expansion, the proof of BG Theorem 5.2, or the unfinished LF-3/LF-4 constructions.

## Findings

### P2-01 — BLOCKER: the frozen class is empty at the stopping scale under its literal Def-6 clause

**Location.** Definition II.6.2 (D2), frozen-v1 lines 2443–2445, says the small-field data “satisfies Def-6 at scale $k$.” The frozen variant in §II.6.3, lines 2470–2475, says “as $\mathrm{IsRep}_k$ except” for listed changes and replaces (D9) by $0<\nu_k$ only. `SMALLFIELD.md` §1.3, line 80, defines Def-6 with $0<\nu_k\le\bar\nu$; its §1.1 has $\bar\nu\le\frac78L^{-2}$. The target defines $k_f$ as the first $k$ with $\nu_k>\frac78L^{-2}$ (II.1.1, line 1787).

**Counterexample/refutation check.** At $k=k_f$ the two inequalities $\nu_{k_f}>\frac78L^{-2}$ and $\nu_{k_f}\le\bar\nu\le\frac78L^{-2}$ are incompatible. Relaxing (D9) does not remove the bound still imported by (D2). The variant is intended to run through $k_f$ and supply LF-5/LF-8; therefore this is an actual empty-class contradiction, independent of analytic estimates. The text's instruction to add the mass to backgrounds after $k_0$ does not redefine the numerical range of Def-6.

**Repair.** Define a frozen small-field predicate with the needed portions of Def-6 and the enlarged mass range, or state exactly which Def-6 clauses are replaced in $\mathrm{IsRep}^{\flat}_k$. Prove its preservation and its compatibility with the complete-background convention before using the frozen class in LF-5 or LF-8.

### P2-02 — MAJOR: the proof of the quiet-step bound treats moving centers as fixed balls

**Location.** Lemma II.5.14, frozen-v1 lines 2378–2398: “$\chi'_{k+1}$ ... confines $\theta(y)$ ... to a ball of radius $\le\frac54\delta_k$ ... so the $\psi_{k+1}(y)$-integral is $\le v_N\le6$”; it repeats the same claim for $\psi_k$. Definition II.3.2, lines 2031–2050, centers these inequalities at $Q\phi(\psi)$, where $\phi$ is itself the background minimizer of the variable being integrated.

**Argument/refutation check.** A condition $|u-Q\phi(u)|<\delta$ does not put $u$ in one ball of radius $\delta$: for every unit vector $v$, constant data $u=v$ have the constant hard-spin minimizer $\phi=v$ and satisfy the inequality. The support contains an entire sphere. With $z=1/2$ and $\delta=2/5$, even the elementary proxy $||z\psi|-1|<\delta$ is an annulus of radii $6/5$ and $14/5$ in two dimensions, of area $\pi((14/5)^2-(6/5)^2)>6$. The full action may suppress this set, so this does **not** refute the lemma's final inequality. It refutes the displayed volume inference used after the proof discards $e^{-\mathcal A}\le1$. No alternative bound for the remaining $\Omega_{k+1}$ output variables is supplied. Thus (S2) for quiet steps, and the claimed derivation of (D5), remain unproved as written.

**Repair.** Keep a coercive part of the main action while integrating those variables, or prove a uniform volume estimate for the actual self-consistent characteristic set, including the $z_{k+1}$ dependence. Recalculate the per-block cost in $c_2$ and the quantifier order if a new constant is needed.

### P2-03 — MAJOR: Def-7 permits discontinuous large-field data as $\nu\downarrow0$

**Location.** Definition II.6.1 and (D4), frozen-v1 lines 2423–2450, make step and kept kernels/boundary factors representation data with per-$\nu$ bounds. (D8), lines 2456–2461, concerns torus transport. §II.6.5(5), lines 2518–2525, explicitly defers large-field continuity to LF-7, while `OBSERVABLES.md` §4.2(5) requires the data of $R^{(k)}$ to be analytic in $b=\nu h$ on $\nu$-independent domains.

**Counterexample/refutation check.** The clauses impose no relation between the data of two different $\nu$ values. On any local prefix with positive slack in its bound, multiplying a nonzero kernel by $1+\epsilon\sin(1/\nu)$, or adding a bounded local term $\epsilon\sin(1/\nu)f(g)$ to $b_k$ and reducing the kernel by a fixed compensating factor, preserves locality, covariance, analyticity in $g$, torus coherence and the same uniform (S2) bound for small fixed $\epsilon$. It has no limit at $\nu=0$. Small-field (CONT) in Def-6 constrains $\mathfrak s$, not these existential large-field data. Hence continuity cannot be a theorem about **every** $\mathrm{IsRep}_k$ as presently defined. Moving the desired conclusion to LF-7 does not supply a hypothesis for its arbitrary input representation.

**Repair.** Add a family-level (CONT) clause for step, kept and boundary data (with a specified $b$ domain and uniform domination), or give LF-7 a narrower, explicitly constructed subclass and use that subclass in the observable induction. Distinguish analyticity in $g$ from continuity in $\nu$.

### P2-04 — MAJOR: the observable interface assumes $g$-independent operators, while Def-7 permits $g$ dependence

**Location.** Definition II.5.2, frozen-v1 lines 2195–2204, defines the operator by $K e^{b(h,g)}$; (S0) and (S3), lines 2254–2275, allow $b_k,b''$ to depend on $g$, and §II.6.5(1) requires $g$ in them. `OBSERVABLES.md` §4.1 (L4), lines 258–260, says “the integral operators $\mathbb T_k$ do not depend on $g$,” and §4.2 uses (L4) in its preservation claim.

**Argument/refutation check.** A nonconstant local analytic term such as $b(g)=\epsilon\sum_{x\in V_Z}h\cdot g(x)$ satisfies the stated type of (S0) with a small enough $\epsilon$ on a nonempty step, including joint covariance, but makes $\partial_g\mathbb T_k$ nonzero. Thus (L4) cannot follow from (D1)–(D9). The source itself does **not** support the (L4) assertion: P5 H5, p. 493, (1.21), explicitly says the nonnegative operator kernel depends on “$\psi_k,\psi,\psi',g$” restricted to $U_k^{\sim}$. The problem is a cross-document interface, not a reason to erase $g$ from P5's operator. In particular, differentiating the generating density may produce terms from the large-field operator, which the present observable reduction omits.

**Repair.** Revise the observable argument to differentiate the local analytic $g$-dependent operators and control the resulting marked terms with the complex sup bounds. Alternatively move *all* operator $g$ dependence into explicit factors outside $\mathbb T_k$ and prove the resulting P5 representation identity. State which convention LF-3/LF-4 use.

### P2-05 — MAJOR: O-8′ identifies the exact-identity failure but has not bounded its action error

**Location.** §II.1.5, frozen-v1 lines 1840–1869, and O-8′, lines 2640–2644, propose using the actual composed weights under the free flow and claim that the cancellation of P7 (2.55)/(2.57) “then leaves a quadratic remainder bounded by $O(\beta^{-1})\times$ the window volume.” P7 p. 499, (2.7), (2.9), and pp. 509–510, (2.55)–(2.57), explicitly invoke P2 §4 composition and (4.18). BG §6.1 (C1) records the coefficient identity that supplies that cancellation.

**Argument/refutation check.** The qualitative diagnosis survives: (I.2) gives a relative coefficient mismatch $O(\beta^{-1}L^{-2\gamma k_1})$ over a window starting at $k_1$, while P7 uses an exact identity. The proposed *quadratic* remainder does not follow from that comparison. Already for $A_a(x)=\frac12a x^2-Jx$ with $J\ne0$, the old stationary point is $x_0=J/a$. Replacing $a$ by $a+\epsilon$ and expanding at $x_0$ gives a linear residual $\epsilon x_0\,\delta x$ as well as $\frac12\epsilon(\delta x)^2$. P7's cancellation contains precisely such first-variation terms. To make them disappear one must use the minimizer and composed weights for the **actual** coefficients and rederive the analogues of (2.54)–(2.58), or bound the linear residual on the window domain. Moreover the coefficient error in an action is multiplied by $\beta_k$; the relative estimate alone does not prove an $O(\beta^{-1})$ absolute budget. This finding is a gap in the proposed Part III route, not a counterexample to the existence of a repair.

**Repair.** State and prove a perturbative composition lemma for arbitrary positive step coefficients, with its domain, minimizer, first-variation identity, and a uniform bound on the complete action difference. Charge the actual bound to (2.15) only after its scale and window-volume dependence is explicit.

### P2-06 — MINOR, UNREFUTED-TENTATIVE: the proof of bound composition uses an invalid integration order

**Location.** Lemma II.5.13, frozen-v1 lines 2365–2376, applies the ancestor (1.26) bounds first, takes a supremum over their output variables, and then integrates the step kernel with (S2). But (S2), lines 2258–2262, bounds the step integral for each fixed ancestor output, not the integral of its supremum.

**Argument/refutation check.** In general $\int \sup_x K(x,y)\,dy$ is not controlled by $\sup_x\int K(x,y)\,dy$: take $K(x,y)=n\mathbf1_{|x-y|<1/(2n)}$ on the unit circle. This refutes the printed order of inequalities. Also, the displayed product of ancestor integrals, each containing an arbitrary $F$, is not a factorization unless $F$ itself factors. Neither defect refutes the intended composition theorem: Fubini in the opposite order can use (S2) first, provided it is uniform in *all* ancestor variables on which $b_k$ is allowed to depend. The (S2) quantifier lists old $\psi_k$ but does not explicitly list old internal variables, so this uniformity should be stated. The domain-support identity must be applied before taking each supremum.

**Repair.** Quantify (S2) over every old internal parameter, integrate the new variables first, and then apply the ancestor bounds. This is a local proof repair if the constructed step kernels have the asserted uniformity.

## Part I v1.1 repair check

| Earlier issue | Recheck at frozen-v1 | Verdict |
|---|---|---|
| P1-01 | §I.1.3 rows 5a–6 and §I.1.4: $m_0$ is fixed from $(d,L)$; $\kappa_1\ge4d\log((2L+1)L^{m_0})+2$ is fixed before $M_1$, and every listed constraint on $M=L^{m_0}M_1$ is a lower bound on $M_1$. This matches `LOCALIZATION.md` §5.3 (C3)–(C6) and its constant order. | Repaired, conditional on the separately marked analytic constant outputs. |
| P1-02 | (I.3) and I.2.13 now use $\lambda\ge0$ before squaring $\lambda\le\hat\lambda$; flow instantiation has $\lambda\ge1$. | Repaired. |
| P1-03 | (RH) in §I.3.1 supplies monotonicity, $\lambda_j\ge1$ and $r_j\ge R_{\rm base}$ to I.3.8–I.3.9. | Repaired. |
| P1-04 | I.3.10(c) uses $R_j\ge R_{\rm base}$ for the fixed separation and declares $\Omega_{k+2}=\varnothing$. | Repaired in the flow range. |
| P1-05 | I.5.6(c) is restricted to genuine $k_0$; $k_0=0$ makes (H-T) empty; $k_f=0$ is assigned to LF-8(b). | Repaired as a scope statement; LF-8(b) remains unwritten. |
| P1-06 | The fixed-point hull is labeled an architectural extension of P6 p. 22; its proof uses the chosen closure. | Source discrepancy disclosed. |
| P1-07 | Radius names, $k=0$ case, extended distances, natural-index (F1), and seed containment appear at the stated locations. | Repaired at the reviewed interfaces. |
| P1-08 | §I.5.3 separates (Λ0)–(Λ11), (Λ12)–(Λ14), and adds (Λ15)–(Λ17) from Part II. | Repaired. |

This check does not upgrade Part I's conditional LF-2 inputs (B), (Rg), the $\pi'$-offset question, or the open Green/localization hypotheses into proved facts. The only stale text found in the repair sweep is §I.7.2's summary phrase “(Λ0)–(Λ13)”; the actual lists and binder include the later conditions.

## Results of the lemma-by-lemma refutation pass

Here “survived” means no counterexample was found at the stated depth, not an independent formal proof. The source-backed BG and P3 inputs retain their cited status.

| Claimed proved result | Assessment and explicit stress test |
|---|---|
| II.1.2 | Survived. Recomputed (a)–(e) from $\lambda_j=\hat\lambda_j-1+\log\gamma_j$; the squaring in (a), monotonic envelope in (c), and exponent in (d) require exactly the displayed lower bounds. (f) inherits I.5.6's $k_f\ge1$ qualification. |
| II.2.3 | Survived for aligned $\pi_q$-cube unions. Tested $q=1$, adjacent and distance-three pieces, the terminal empty layer, and the collar. The geometric-series radius is less than one $\pi_q$ cube under row 5a. |
| II.2.5 | Conditional. The same-side and cross-interface separation calculations are plausible under (RH); the local version (v) needs the neighborhood-buffer argument when $W_k$ is intersected with $U_{Z'}$, not merely the sentence that intersections preserve separation. No configuration violating the conclusion was found. |
| II.2.6 | Conditional on II.2.5(b) and BG's uniqueness theorem. With separated collars, the Dirichlet action, pointwise constraint and multiplier class split; a shared fixed $h$ does not couple the pieces. This is exact factorization for the **new local set**, not for P6's global set. |
| II.3.3 | Survived. The domain indicator is open where the BG minimizer is defined, and the one-cube range gives the three-cube stencils. The asserted source equivalence outside that domain uses the separately cited P1 regularity input. |
| II.4.2, II.4.3, II.4.1 (LF-1) | Survived the nearest-neighbor, constant-field, and two-layer tests. The $\ell^{2-d}$ factor in II.4.2 follows after counting each bond at most $\ell$ times. II.4.3 relies on the cited sharp block Poincaré inequality. Recounting the proof gives at most $7d$ block-error charges and $9$ bond charges, compatible with $\gamma_0=1/(28d)$; (b) needs its printed $\mu L^{2q}\le1$. |
| II.5.3 | Survived when its absolute-integrability premise is met. It is a Fubini/product identity; disjoint component supports are supplied only later by II.5.9. |
| II.5.9 (structural Lemma F) | (a)–(c) survive conditionally on the support clauses (S0), (S1), (S3), I.3.15 and II.2.5; they do not establish the analytic background-change half, which the text correctly leaves to LF-3. (d) uses the domain identity of II.5.13 and should follow after P2-06 is repaired. An arbitrary non-quiet kernel's locality is **assumed in (S1)**, not proved here. |
| II.5.10 | Survived for the explicit quiet kernel by equivariance and uniqueness of the minimizer. Invariance of non-quiet and kept data is a clause of (S0)/(S1)/(S3), hence conditional. |
| II.5.12 (Lemma B) | Survived. Re-expanded $G^{\rm pre}_{k+1}-\sum_YG_k(Y)$ into the displayed gain, old-volume and new-volume terms; (Λ15) and (Λ16) pay the latter two. Hull cubes are included as new volume. This is an algebraic budget lemma conditional on the exponents being realized by (S2). |
| II.5.13 | Conclusion may be repaired by reversing integrations and making uniformity explicit; P2-06 refutes the printed proof order. |
| II.5.14 | Unproved by the stated argument; P2-02 refutes the key volume step. It is the only proposed proof of (S2) for quiet steps in Part II. |
| II.5.15 | Survived the four-family count, including a single new cube, a pure shadow, a merge, and kept-label summation. With $L^d\ge8$, $e^{-1}+e^{-5/4+4L^{-d}\log2}<1$. The proof assumes the Part I locality/injective history encoding. |
| II.6.3 | (b), (c), (d) follow conditionally from (D5), summability and LF-2 geometry. (a) depends on P2-02 and P2-06. The frozen version is blocked by P2-01. |

## Def-7 and downstream use

(D1) gives a source-shaped representation, (D3) fixes the characteristic function, (D6) carries the abstract LF-2 budget, (D7) gives local analytic boundary terms, and (D8) supplies a finite-set torus clause. (D4) is deliberately a **class condition**, not a proof of the difficult non-quiet one-step estimate: (S2) is P6 (3.4)–(3.9) placed among the data requirements; (S3) similarly places the kept gain and operator bound required of LF-4 among the kept-data requirements. These clauses are legitimate only if LF-3 and LF-4 construct data satisfying them for every input representation. Lemma II.6.3 does not discharge those construction tasks. (D5) is redundant if (D4) and the corrected composition lemma hold, but retaining it records the consumer-facing bound at each scale.

The class as printed is insufficient for LF-5/LF-8 at the stopping scale (P2-01) and for the observable limit from arbitrary representations (P2-03). For observables it also conflicts with the separate assertion (L4) in `OBSERVABLES.md` (P2-04). The local $g$ support and whole-polydisc bounds are useful, but the derivative argument must include $g$-dependent operators, and the marked polymer expansion with holes remains a separately stated Part IV input. LF-4 can use quiet-window formulas conditionally, but P2-02 must be repaired and the actual kept-data construction remains open as the manuscript says.

## Closeout

All Part I repair items and all results marked “proved here” in the Part II status table were classified above. Findings P2-01, P2-03 and P2-04 survived direct contradiction or explicit parameter-family tests; P2-02 and P2-06 identify false proof inferences without claiming a false final lemma; P2-05 survived comparison with the exact source identities and a scalar first-variation test. The open analytic half of Lemma F, non-quiet (S2), the LF-6 base, LF-4's kept construction, and the P9 marked expansion were **not** promoted from cited/planned status. No file under `/home/scott/Balaban` was edited, committed or pushed. The audit can close as a diagnosis; the reconstruction cannot yet be frozen as an inductive definition.
