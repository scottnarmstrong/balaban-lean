# E1: Cammarota, decay of correlations / polymer exponentiation theorem

## 0. Identification

C. Cammarota, "Decay of correlations for infinite range interactions in unbounded spin systems", Commun. Math. Phys. 85 (1982) 517-528 (doi 10.1007/BF01403502). Bundle key E1. 12 pages (journal pp. 517-528; PDF page = journal page - 516). Received 10 Dec 1981, communicated by E. Lieb.

Summary. The paper has two results. Theorem 1 (p. 517-518): for a high-temperature (small $\beta$) unbounded spin system on $\mathbb Z^d$ with a two-body potential of infinite range, the two-point truncated correlation function decays like $e^{-\delta(x,y)/2}$ (exponentially if the potential decays exponentially, as a power if it decays as a power), with an explicit bound (1.11). It extends Kunz (1978, [1] there), who assumed finite range. Theorem 2 (p. 519): a convergence/exponentiation theorem for the Mayer (cluster) series of a general abstract polymer model on a countable set of sites, with a new combinatorial proof (Sect. 3, via trees and the Cayley formula). Theorem 1 is derived from Theorem 2 plus the bound of Lemma 1-2 (Sect. 2).

Which bundle papers cite it (grep of `papers/P*.md`, `BIG_PICTURE.md`, and `pdftotext` of the PDFs of P4-P7):

- **P4** (CMP 182, 675, Balaban.pdf): bibliography item [5], p. 720-721. The text of P4 contains no citation marker "[5]" (pdftotext of Balaban.pdf: the only hits of Cammarota/[5] are in the bibliography lines; [4], [5], [6] are all uncited in the text). This confirms the P4 reviewer's finding: in P4 the reference is a dangling bibliography entry.
- **P6** (CMP 198, 1, s002200050470.pdf): bibliography [9]. Cited as "[7,9]" for "a form of a cluster expansion" (PDF p. 35 = journal p. 35, in the proof of Prop 3.4 [5], just before the part of the proof treating the remaining localization expansions) and "[7,9]" again for "the cluster expansion in a polymer form described in many places ... completely standard" (journal p. 38, near (4.47)-(4.51)). [7] is Brydges, "A short course in cluster expansions".
- **P7** (CMP 198, 493, s002200050486.pdf): bibliography [11]. Cited in the string "[9,11,13-15]" as "a theorem on cluster expansions" used to exponentiate the polymer expansion (3.27) (journal p. 528, just after (3.26)). [9] is Brydges, [13-15] are Abdesselam-Rivasseau, Rivasseau, and a third reference (not checked).
- **P5** (s002200050433): the bibliography contains Brydges, Abdesselam-Rivasseau, Rivasseau but NOT Cammarota (grep found no Cammarota).
- Roadmap/BIG_PICTURE (`FORMALIZATION_ROADMAP.md` l. 811, `BIG_PICTURE.md` l. 944) list Cammarota among candidate references for the polymer-expansion convergence theorem "used in P6 (4.46)-(4.51), P7".

## 1. Setting and notation

Lattice $\mathbb Z^d$; finite $\Lambda\subset\mathbb Z^d$. Spins $S_x\in\mathbb R^\nu$ (unbounded). Many-body potential $\Phi=\{\Phi_X\}$, $\Phi_X(S_X)$ for $X\subset\Lambda$, $|X|\ge2$. Gibbs measure (1.1):
$$Z_\Lambda^{-1}e^{-\beta\sum_{X\subset\Lambda,|X|\ge2}\Phi_X(S_X)}\prod_{x\in\Lambda}W_x(dS_x),$$
with single-site measure $W_x(dS_x)=\big(\int\mu_x(dS_x)e^{-\beta\Phi_x(S_x)}\big)^{-1}e^{-\beta\Phi_x(S_x)}\mu_x(dS_x)$ (1.2), $\mu_x$ the a priori measure, $\beta$ inverse temperature. Correlation functions $\varrho_\Lambda(S_X)$ (1.3).

Polymer model (p. 518): a polymer is a finite subset $R\subset\mathbb Z^d$; activity $\zeta(R)=\int W_R(dS_R)\zeta(S_R)$ (1.12), with $\zeta(S_R)=1$ if $|R|=1$ and $\zeta(S_R)=\sum_{K\ge1}\frac1{K!}\sum^*_{(X_1,\dots,X_K)}\prod_i(e^{-\beta\Phi_{X_i}(S_{X_i})}-1)$ for $|R|>1$, where $*$ means $X_i\subset R$, $|X_i|\ge2$, $X_i\neq X_j$ (UNCERTAIN: printed "$X_i\ne X_j$" hmm, the image shows $X_i\neq X_j$ resp. the $K$-sequences with $\bigcup X_i=R$ and the graph $g(X_1..X_K)$, with line $\{i,j\}$ iff $X_i\cap X_j\neq\emptyset$, connected). Partition function as sum over families of disjoint polymers (1.13): $Z_\Lambda=\sum_{n\ge1}\sum_{\{R_1..R_n\}\in\pi(\Lambda)}\zeta(R_1)\cdots\zeta(R_n)$, where $\pi(\Lambda)$ is the set of partitions of $\Lambda$ (singletons included). Polymer correlation functions $\bar\varrho_\Lambda(X)=Z_\Lambda^{-1}\sum\zeta(R_1)\cdots\zeta(R_n)$ over partitions of $\Lambda\setminus X$ (1.14), and $\varrho_\Lambda(S_X)=\sum_{Y\subset\Lambda\setminus X}\bar\varrho_\Lambda(X\cup Y)\int W_Y(dS_Y)F_{S_X}(S_Y)$ (1.15), $F_{S_X}(S_Y)=\sum\zeta(S_{R_1})\cdots\zeta(S_{R_n})$ (1.16), over partitions of $X\cup Y$ with each $R_i\cap X\ne\emptyset$.

Mayer series: $\mathscr R$ = set of polymers with $|R|\ge2$; $\chi(R_i,R_j)=0$ if $R_i\cap R_j\neq\emptyset$ and $1$ otherwise; truncated function $\varphi^T(R_1,..,R_n)=1$ ($n=1$), $=\sum_{g\in C_n}\prod_{\{i,j\}\in g}(\chi(R_i,R_j)-1)$ ($n>1$), $C_n$ = connected graphs on $\{1,..,n\}$ (1.17).

| symbol | meaning | where |
|---|---|---|
| $\delta$ | metric on $\mathbb Z^d$ with $\sup_x\sum_{y\ne x}e^{-\delta(x,y)/2}=D$ | (1.5), p. 518 |
| $J(x,y)$ | amplitude of two-body bound, $\sup_x\sum_y J(x,y)^{1/3}=J$ | (1.4), (1.6) |
| $v_x$ | single-site weight in the bound (1.4); $\sup_x\int W_x e^{\frac12Jv_x^2}=I(\beta)=O(1)$ | (1.7) |
| $I_1,I_2,I_3,\dots,I_{11}$ | explicit $O(\sqrt\beta)$ functions of $I(\beta),J,\beta$ | (2.15), (2.18), (2.19)-(2.26) |
| $\varepsilon$ | smallness of polymer activities | (1.18), (1.19) |
| $\varphi^T$ | Ursell/truncated function of polymers | (1.17) |
| $\delta(R)$ | smallest length of graphs in $C_R$ | after (2.12) |

## 2. Main results

**Theorem 1 (p. 517-518).** Let $\Phi$ be a two-body potential with
$$|\Phi_{xy}(S_x,S_y)|\le e^{-\delta(x,y)}J(x,y)v_x(S_x)v_y(S_y)\qquad(1.4)$$
where $\delta$ is a metric on $\mathbb Z^d$ with $\sup_x\sum_{y\ne x}e^{-\frac12\delta(x,y)}=D$ (1.5), $\sup_x\sum_{y\neq x}J(x,y)^{1/3}=J$ (1.6), and $\sup_x\int W_x(dS_x)\exp\tfrac12Jv_x(S_x)^2=I(\beta)=O(1)$, $\beta\to0$ (1.7). Then there are functions $I_3(\beta)$, $I_{11}(\beta)$, both $O(\sqrt\beta)$ as $\beta\to0$ such that, if
$$I(\beta)J/\sqrt\beta\,\exp DI_3(\beta)<1\ (1.8),\qquad \beta\sup_{x,y}J(x,y)^{2/3}<1\ (1.9),\qquad \frac{I(\beta)J^{1/2}\beta^{1/4}}{1-J\sqrt\beta}<\frac1{2e+1}\ (1.10),$$
then for every finite $\Lambda$ and all $x\ne y$
$$|\varrho_\Lambda(S_xS_y)-\varrho_\Lambda(S_x)\varrho_\Lambda(S_y)|\le e^{\frac12Jv_x(S_x)^2+\frac12Jv_y(S_y)^2}\,e^{-\frac12\delta(x,y)}\,I_{11}(\beta)\qquad(1.11).$$
(UNCERTAIN: the exact form of (1.8) as printed, "$I(\beta)J/\sqrt\beta\,\exp DI_3(\beta)<1$", I could not parse unambiguously whether it is $I(\beta)J\sqrt\beta$ or $J/\sqrt\beta$; the page image reads "$I(\beta)J\sqrt{/\beta}$" as a garbled root. From the proof (Lemma 1, (2.7): $\sum_{|R|=K}|\zeta(R)|\le I(\beta)^K(J\sqrt\beta)^{K-1}(1-J\sqrt\beta)^{-1}$, summed using (2.12)-(2.13)) the natural quantity is $J\sqrt\beta$; the notation "$J/\beta$" under a root is likely a typesetting rendering of $J\sqrt\beta$. Do not rely on (1.8) without checking the page.) The infinite-volume limit of correlations is not proved here (Kunz [1] cited).

**Theorem 2 (p. 519, polymer exponentiation).** Let $\mathscr R$ be the set of polymers with $|R|\ge2$ (finite subsets of $\mathbb Z^d$) and $\zeta:\mathscr R\to\mathbb C$ with, for each integer $K\ge2$,
$$\sup_{x\in\mathbb Z^d}\sum_{x\in R\in\mathscr R,\ |R|=K}|\zeta(R)|\le\varepsilon^K\qquad(1.18),\qquad \frac\varepsilon{1-\varepsilon}<\frac1{2e}\qquad(1.19).$$
Then for each polymer $R$
$$\sum_{n=1}^\infty\frac1{n!}\sum_{\substack{(R_1..R_n)\in\mathscr R^n\\ \exists R_i=R}}|\varphi^T(R_1..R_n)\zeta(R_1)\cdots\zeta(R_n)|\le|\zeta(R)|\Big(1+|R|e^{|R|}\tfrac12\ln\big(1-2e\tfrac\varepsilon{1-\varepsilon}\big)^{-1}\Big)\qquad(1.20),$$
and for every finite $\Lambda$
$$Z_\Lambda=\exp\sum_{n=1}^\infty\frac1{n!}\sum_{\substack{(R_1..R_n)\in\mathscr R^n\\R_i\subset\Lambda}}\varphi^T(R_1..R_n)\zeta(R_1)\cdots\zeta(R_n)\qquad(1.21).$$
Here $Z_\Lambda=\sum_{\{R_i\}\text{ disjoint}}\prod\zeta(R_i)$ with singleton polymers having activity 1 (as in (1.13), (3.1)). Note that the form of $\zeta$ is arbitrary: (1.18) is the only hypothesis; the activities need not come from a spin model, and the lattice structure plays no role beyond countability and the translation-free sup over $x$.

## 3. Proof architecture

Sect. 2 (p. 520-525), proof of Theorem 1. From (1.15) one writes $\varrho_\Lambda(S_xS_y)-\varrho_\Lambda(S_x)\varrho_\Lambda(S_y)$ as a sum of six terms $\Sigma_1,\dots,\Sigma_6$ (2.5), (2.6) of products of $\zeta(S_xT)$, $\bar\varrho_\Lambda$ and differences $\bar\varrho_\Lambda(xyT_1T_2)-\bar\varrho(xT_1)\bar\varrho(yT_2)$; the manipulations are "quite similar" to Kunz [1] (so not given). Each is bounded by Lemma 1 (activity bounds) and Lemma 2 (near-factorization of $\bar\varrho_\Lambda$).

- **Lemma 1** (p. 521-522). Under (1.4), (1.6)-(1.9): (2.7) $\sup_x\sum_{x\in R,|R|=K}|\zeta(R)|\le I(\beta)^K(J\sqrt\beta)^{K-1}(1-J\sqrt\beta)^{-1}$; (2.8) the same with $e^{-\delta(x,y)}$ for sums over $R\supset\{x,y\}$; (2.9)-(2.10) bounds on $\int W_T(dS_T)|\zeta(S_xS_yT)|$ and on $\int W_T|\zeta(S_xT)|$ with the weights $e^{\frac12Jv^2}$. Proof of (2.7): $\zeta(R)=\int W_R\sum_{g\in C_R}\prod_{\{x,y\}\in g}(e^{-\beta\Phi_{xy}}-1)$; use $e^{\lambda t}-1\le t(e^\lambda-1)$ for $0\le t\le1$ and (1.9) to get $|e^{-\beta\Phi_{xy}}-1|\le\beta e^{-\delta}J(x,y)^{2/3}v_xv_y\,e^{J(x,y)^{1/3}v_xv_y}$; Young-type inequality $v_xv_yJ(x,y)^{1/3}\le\frac12(v_x^2J(x,y)^{1/3}+v_y^2J(x,y)^{1/3})$ and (1.6) give a single-site factor $\int W_xe^{\frac12Jv_x^2}\le I(\beta)$; then (2.12) $|\zeta(R)|\le e^{-\delta(R)}I(\beta)^{|R|}\sum_{g\in C_R}\prod(\beta J(x,y)^{2/3})$, and a spanning-walk argument (to each connected graph and $x\in R$ associate a closed walk $(x_1,..,x_q)$, $q\ge|R|$, visiting all of $R$, each edge used at most twice) reduces to $\sum_{q\ge K}(\beta^{1/2}J)^{q-1}$. Genuine step; routine otherwise.
- **Lemma 2** (p. 522-523). With $\varepsilon=I_1(\beta)=I(\beta)J^{1/2}\beta^{1/4}(1-J\sqrt\beta)^{-1}$ (2.15) (UNCERTAIN: exponents as printed), (1.10) gives Theorem 2's hypothesis; hence $\bar\varrho_\Lambda(X)=\exp(-\sum\dots)$ (2.16) and the ratio $\bar\varrho_\Lambda(X\cup Y)/\bar\varrho_\Lambda(X)\bar\varrho_\Lambda(Y)=\exp\sum_{\exists i:R_i\cap X\ne\emptyset,R_i\cap Y\neq\emptyset}\dots$ (2.17) is bounded using (1.20): $|\bar\varrho(X\cup Y)/(\bar\varrho(X)\bar\varrho(Y))-1|\le\exp(I_3(\beta)\sum_{x\in X,y\in Y}e^{-\delta(x,y)})-1$ (2.13), in particular (2.14) $\le\exp(I_3DI\ldots\min(|X|,|Y|))e^{-\frac12\delta(X,Y)}$ (as printed: $\exp(I_3(\beta)D\min\{|X|,|Y|\})e^{-\frac12\delta(X,Y)}$ (2.14)). This is the cluster-expansion mechanism: ratios of partition functions are exponentials of connected sums over polymers touching both $X$ and $Y$.
- Termwise bounds (2.20)-(2.26) for $\Sigma_1..\Sigma_6$, with constants $I_4,\dots,I_{10}$ all $O(\sqrt\beta)$ or smaller, giving (1.11). Routine summations.

Sect. 3 (p. 525-528), proof of Theorem 2.

1. Rewrite $Z_\Lambda$ as a sum over $n$-tuples with $\prod\chi(R_i,R_j)$ (3.1), expand $\prod_{\{i,j\}}\chi(R_i,R_j)=\sum_{K}\sum_{\{I_1..I_K\}\in\pi(\{1..n\})}\varphi^T(R_h,h\in I_1)\cdots\varphi^T(R_h,h\in I_K)$ (the standard Mayer expansion). Exchanging sums and recognizing the exponential gives (1.21) once the series (3.2) converges absolutely.
2. Absolute convergence follows from (1.20): bound by the sum over $R$ and over tuples containing $R$ (3.3)-(3.5); reduces to estimating $\sum_{(R_2..R_n)}|\varphi^T(R_1..R_n)\zeta(R_2)\cdots\zeta(R_n)|$ (3.6).
3. $\varphi^T$ depends only on the intersection graph $g(R_1..R_n)\in C_n$: $\varphi(g)=\sum_{f\subset g,f\in C_n}(-1)^{|f|}$ (3.7). **Proposition (p. 526): $|\varphi(f)|\le N(f)$, the number of spanning trees of $f$.** Not proved here; cited to Penrose [10] and Malyshev-type [13,14] (Rota [13], Malyshev [14] in the printed list).
4. Sum over trees: $(3.8)\le\sum_{t\in T_n}w(t)$ with $w(t)=\sum_{(R_2..R_n):g\supset t}|\zeta(R_2)|\cdots|\zeta(R_n)|$ (3.9). Peeling leaves and using (1.18), $\sum_{R\cap R'\ne\emptyset}|\zeta(R)|\le|R'|\sup_x\sum_{x\in R}|\zeta(R)|\le|R'|\varepsilon(1-\varepsilon)^{-1}$-type bounds, together with $\sum_{R\ni x}|\zeta(R)||R|^p\le p!\,\varepsilon/(1-\varepsilon)$ (3.10, valid under $\varepsilon(1-\varepsilon)^{-1}<(e-1)^{-1}$), one gets for a tree with degrees $d_i$:
$$w(t)\le|R_1|^{d_1}\Big(\frac\varepsilon{1-\varepsilon}\Big)^{n-1}\prod_{i=2}^n(d_i-1)!\qquad(3.11).$$
5. Cayley's formula: number of labelled trees with prescribed degrees is $(n-2)!/\prod(d_i-1)!$ (cited to Moon [12]). Summing over degree sequences $d_1+\dots+d_n=2(n-1)$ with $\Gamma_K(m)\le m^{K-1}/(K-1)!$ (3.13)-(3.14) gives that (3.6) is at most $\frac12\big(2e\frac\varepsilon{1-\varepsilon}\big)^{n-1}(n-2)!\,|R_1|e^{|R_1|}$, and summing the series (3.5) in $n$ gives (1.20): $\frac12\sum_{n\ge2}\frac{x^{n-1}}{n-1}=\frac12\ln(1-x)^{-1}$ with $x=2e\varepsilon/(1-\varepsilon)$.

Difficulty: the cluster combinatorics (tree bound of $\varphi$, Cayley count). Hard analytic content is nil; the paper's contribution is the clean tree-graph proof with an explicit condition $\varepsilon/(1-\varepsilon)<1/2e$.

## 4. Ingredients and prerequisites

4a. Other bundle papers: none (1982, predates the series).

4b. Outside the bundle (as printed, p. 528): [1] Kunz, H., Commun. Math. Phys. 59, 53-69 (1978) (analyticity and clustering for unbounded spins; Theorem 1 here removes his finite-range hypothesis; the six-term decomposition is taken from it). [2] Israel-Nappi CMP 68, 29-37 (1979); [3] Gross CMP 68, 9-27 (1979); [4] Duneau-Souillard CMP 47, 155-166 (1976); [5] Gruber-Kunz CMP 22, 133-161 (1971) (polymer systems); [6] Gallavotti-Martin-Lof-Miracle-Sole; [7] Ruelle, Statistical Mechanics; [8] Campanino-Capocaccia-Tirozzi CMP 70; [9] Cassandro-Olivieri CMP 80; [10] Penrose, in Statistical Mechanics: Foundations and Applications (1967) (tree bound for $\varphi$); [11] Brydges-Federbush J. Math. Phys. 19, 2064 (1978); [12] Moon, Enumerating labelled trees; [13] Rota Z. Wahrscheinlichkeitstheorie 2, 340 (1964); [14] Malyshev CMP 64, 131-157 (1979). The essential outside input is the Penrose tree bound $|\varphi(f)|\le N(f)$ (Proposition, p. 526).

4c. Standard mathematics: Mayer/Ursell expansion, exponentiation of polymer gases, counting of labelled trees (Cayley), elementary combinatorics.

## 5. Dependency ledger

| result | uses (internal) | uses (external) | status |
|---|---|---|---|
| Lemma 1 (2.7)-(2.10) | (1.4), (1.6)-(1.9) | none | proved (2.7); others "obvious modifications" |
| Lemma 2 (2.13)-(2.14) | Lemma 1, Thm 2 | none | proved |
| Thm 1 (1.11) | Lemmas 1-2, six-term decomposition | Kunz [1] manipulations | proved modulo "similar to [1]" |
| Prop $|\varphi(f)|\le N(f)$ (p. 526) | none | Penrose [10], [13,14] | cited |
| Thm 2 (1.18)-(1.21) | Prop, (3.10)-(3.14) | Cayley formula [12] | proved |

## 6. Constants and parameters

Order of choice in Theorem 1: potential data ($\delta,J(\cdot,\cdot),v_x$) fixed, then $\beta$ small enough that (1.7)-(1.10) hold; the functions $I_j(\beta)$ are then explicit, $O(\sqrt\beta)$. In Theorem 2 only $\varepsilon$ with $\varepsilon/(1-\varepsilon)<1/(2e)$, i.e. $\varepsilon<1/(2e+1)$. Note the connection: (1.10) is exactly $\varepsilon=I_1(\beta)<1/(2e+1)$.

## 7. Weak spots and open points

- Six-term decomposition and some bounds (2.8)-(2.10) are left to "similar to [1]" / "obvious modifications".
- Penrose's tree bound is cited, not proved.
- Printed formulas in (1.8), (2.14), (2.15) were hard to read on the page image (see UNCERTAIN notes above). Exponent bookkeeping ($J^{1/2}\beta^{1/4}$) should be rechecked before any use of Theorem 1 itself.
- (3.10)-(3.12): the induction giving $w(t)\le\dots$ is only sketched ("follows from a simple induction argument").
- For the O(N) series: Theorem 1 itself is not needed; see Sect. 9.

## 8. Preliminary formalization notes

Theorem 2 is self-contained and abstract (activities on finite subsets of a countable set; only (1.18) used). It would be formalizable: needs finite graphs, spanning trees, Penrose's inequality $|\sum_{f\subset g\text{ conn}}(-1)^{|f|}|\le\#\text{trees}(g)$ (not in Mathlib; a guess, a few hundred lines), Cayley's formula (Mathlib has `Cayley` for labelled trees? UNKNOWN, flagged as a guess; there is `SimpleGraph` machinery but the degree-refined version is likely absent), and series/exponential identities. Theorem 1 is irrelevant to O(N).

## 9. What the O(N) series uses from this paper

Citation sites and their precise targets:

1. **P4 [5]**: bibliography only (p. 721). No marker in the text of P4 (confirmed by pdftotext of P4 PDF: the only occurrences of "Cammarota"/"[5]" are in the reference list). Defective/orphan citation: P4 uses nothing from E1 as cited. Plausible explanation: P4 is a revised/partly shared reference list with P6/P7 (where "[7,9]" and "[9,11,13-15]" appear and the same Brydges-Dimock-Hurd, Glimm-Jaffe entries are present); the polymer expansions in P4 are only touched in passing (UNCERTAIN: I did not re-read P4 text beyond grep).
2. **P6 [9]** (journal p. 35 and p. 38, near (4.47)-(4.51), proof of Prop 3.4 [5]): "cluster expansion ... see [7,9] for a general discussion"; "polymer form ... described in many places, for example [7,9]; completely standard". No specific item cited. What is plausibly meant: Theorem 2 here, i.e. convergence of the Mayer series of a polymer model and its exponentiation under a condition of the form $\sup_x\sum_{R\ni x}|\zeta(R)|\le\varepsilon^{|R|}$ (1.18)-(1.19).
3. **P7 [11]** (journal p. 528, after (3.26)): "applying results of [9,11,13-15], we exponentiate the polymer expansion (3.27)". Again plausibly Theorem 2 (1.20)-(1.21). The P7 polymers are connected unions of cubes with activities that decay exponentially in a tree-length; Cammarota's hypothesis (1.18) is in terms of the cardinality $|R|$ with $\varepsilon^{K}$ weights, so the exponential weights $e^{-\kappa d(R)}$ of P6/P7 would have to be recast (e.g. activities bounded by $\varepsilon^{|R|}$ with $|R|$ the number of unit cubes, plus the weight absorbed in $\varepsilon$ for fixed small $\varepsilon$).

Applicability to the scalar O(N) setting. Theorem 2 is purely combinatorial and applies as stated provided: (i) the O(N) activities are indexed by finite sets of unit cubes / blocks of the lattice (so "sites" are cubes) satisfying (1.18) uniformly with small $\varepsilon$; (ii) the sets $R$ are the "polymers" (connected unions of cubes) and the hard-core compatibility is disjointness ($\chi$). Adaptations needed: (a) the series of P6/P7 involve additional dependence on a background field/"$\Omega^c$ modulo connectivity" and on analytic extension variables $\psi$, so Theorem 2 would have to be applied pointwise in $\psi$ and then complex-analyticity of $\log$ follows from uniform convergence; (b) the activities in the series are bounded by $\varepsilon^{1/2}e^{-5\kappa_0d(Y)}$ (P6 (4.47)), i.e. exponential decay in the size of $Y$; one needs to check that this implies (1.18) with some $\varepsilon$ for every size $K$ — it does if $|R|$ counts cubes and $d(Y)\ge c|Y|$ is not generally true (tree-length vs cardinality), so the hypothesis (1.18) would hold only when the number of cubes is controlled by $d_k(Y)$; UNCERTAIN, requires reading P6. (c) The "connectivity modulo $\Omega^c$" variant listed in the roadmap is NOT in E1; E1 only covers ordinary connectivity. (d) Gauge/Higgs-specific aspects do not arise. E1's Theorem 1 (decay of two-point function) is for high temperature, and the O(N) series is low temperature (where the polymer model is of a different nature: Gaussian fluctuation measures, small $\beta^{-1}$), so Theorem 1 is not what is cited.

If the bundle's citation is to "an item in E1": there is no specific numbered item cited anywhere. The best candidate is Theorem 2 (p. 519). No item in E1 matches anything else in the bundle (P1-P3, P5 do not cite it).

## 10. Relevance to the formalization

- Verdict on the P4 [5] question: the citation in P4 is orphaned; the reference is genuinely used (in a generic way) in P6 and P7 for convergence/exponentiation of polymer expansions. Whether it is "plausibly used": yes in P6 (4.46)-(4.51) and P7 (3.27); not in P4.
- For Lean: state a polymer-gas interface "if $\sup_x\sum_{R\ni x,|R|=K}|\zeta(R)|\le\varepsilon^K$ and $\varepsilon/(1-\varepsilon)<1/2e$ then (1.20), (1.21)". This is Theorem 2 and is a self-contained, reusable module. A cleaner modern route: Kotecky-Preiss criterion or Brydges-style/Fernandez-Procacci convergence conditions (flag: suggestion, not a claim); these handle activities weighted by $e^{a|R|}$ and general polymer sizes, and would probably match P6/P7's exponentially decaying activities better than (1.18). The Mayer-series combinatorics (Penrose tree bound) would be needed in either proof.
- Theorem 1 and Sect. 2 (high-temperature decay of correlations, six-term decomposition) are irrelevant to the O(N) low-temperature formalization. The O(N) series gets its correlation decay (P9, Balaban-O'Carroll) from its own RG machinery, not from E1.
- E1 gives no Green's function results.
