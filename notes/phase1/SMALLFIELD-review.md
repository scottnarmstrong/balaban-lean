# Review of `notes/phase1/SMALLFIELD.md` (brief D-SF-review)

Referee report, 2026-10-11. Paper-only review; no Lean was run or written.

**What was read.** `SMALLFIELD.md` in full; `AGENTS.md`; the landed `Balaban/Flow/RGEquations.lean` (`TriangularBounds`, `exists_rg_solution_triangular`) and `RunningCoefficients.lean` (`norm_gammaSeq_le`, `exists_gamma_infty`, `exists_inv_betaSeq_asymptotics`); `Balaban/Correlations/C1Star.lean` (`C1StarF1`, `mainTr`); `CORRELATIONS.md` (§2.2 (F1)–(F3), §5); `BACKGROUND.md` (I-1(e), Prop 5.1, §1.3, Theorem 6.1); `LF-ARCHITECTURE.md` v4 (§1.4 table, running-constants paragraph, Def-7 (D1)–(D9), LF-3); `ERRATA.md` rows ER-016, 020, 023, 062, 063, 067, 069, 070; the reviews `P4`, `P5`, `P6`. **Page images and source text read:** P4 pp. 708–709 (pdf 34–35: (5.4)–(5.10)); P6 pp. 39–43 from the text layer (pdf text around (4.54)–(4.67)). P1 was not re-read (as in the document); P4 pp. 710–718 were not re-read, so (E3) and (5.21)–(5.22) are checked only for internal consistency and for Lemma 3.1's arithmetic.

## Verdict: APPROVE-WITH-CHANGES

The architecture is right and the new proof in §2 has the correct mechanism, but one step is wrong as written (S-01), one cited input does not say what is claimed (S-02), the reduction to the landed theorem is not exact (S-03), and the proposed frozen surface conflicts with LF-ARCHITECTURE and with AGENTS rule 4 (S-04, S-05). All five have local repairs. Def-6 and the I-7 theorem should not be frozen before S-04 and S-05 are settled.

## Findings

### S-01 (MAJOR) I-6, §2.3 Step 5: the marginal gradient term does not vanish per site as written

**Location.** §2.3 Step 5, last paragraph ("*This is where (H.5)(4) enters*"), and Theorem 2.1(a).

**Argument.** After (WI) and (2.3), the leading part for a fixed centre $y$ is $-\frac14\sum_{x'}T^{(y)}_{\mu\nu}(x')\,\partial_\mu\Theta\cdot\partial_\nu\Theta(x')$ with $T^{(y)}_{\mu\nu}(x'):=\sum_zB^{(y)}(x'+z,x')z_\mu z_\nu$. The tensor $T^{(y)}(x')$ depends on $x'-y$ (the sets $X$ all contain $y$). What equals $S^{(y)}_{\mu\nu}=\frac1d\delta_{\mu\nu}\sum_zG_{22}(z)|z|^2=0$ is the total $\sum_{x'}T^{(y)}(x')$. The document writes the leading part as "$-\frac14\sum_{x'}\sum_{\mu\nu}S_{\mu\nu}\partial_\mu\Theta\cdot\partial_\nu\Theta=0$ exactly", which treats $T^{(y)}(x')$ as the constant $S$. That is false unless $\partial\Theta\cdot\partial\Theta$ is constant. Pointwise, the leftover is of size $E_0\sigma^2R^2$ (a gradient squared against $\varepsilon_j^{-2}$), which is larger than $\sigma^{3-\alpha_1}R^2$, so Theorem 2.1(a) is not proved as stated. The torus sum (b) is not affected, because $\sum_yT^{(y)}(x')=S$ is independent of $x'$.

**Fix.** Write $\partial_\mu\Theta\cdot\partial_\nu\Theta(x')=\partial_\mu\Theta\cdot\partial_\nu\Theta(y)+\rho(x')$. By (Σ2), $|\rho(x')|\le C|x'-y|\,\sigma\varepsilon\,s^{2-\alpha_1}\varepsilon$. The $y$-term is multiplied by $\sum_{x'}T^{(y)}(x')=S^{(y)}=0$, which uses (H.5)(4) and the cubic symmetry exactly as in the document. The remainder is $\le CE_0\sigma s^{2-\alpha_1}R^2\le CE_0\sigma^{3-\alpha_1}R^2$, the same order as the other terms of Step 5 (weights $(1+d_j(X))^{4}e^{-\kappa d_j(X)}$ absorb $|x'-y|$). With this extra step, (a) holds per site. Everything else in Steps 0–5 that I re-derived is correct: (WI) is the right Ward identity (I rederived it by differentiating the infinitesimal rotation identity in the direction $\delta_{x'}e_2$, including the $-a_X(x')$ and $\nu_jm_X(x')$ terms), (2.3) follows from it with $B$ symmetric, and the exponent bookkeeping $4+2\alpha=d+\alpha_2$, $3-\alpha_1+2\alpha=d+\alpha_3$ is right. The answer to Question 7 (§7.6): per-centre and summed-over-centres forms of (H.5)(4) agree by translation covariance, and $S^{(y)}=\sum_zG_{22}(z)zz$ needs only the finite-set terms (no torus limit).

### S-02 (MAJOR) I-6 premise (Σ1): the scaling $\sigma=C_0s_{jk}$ is not provided by I-2(iv)

**Location.** §1.2 last sentence ("The chain of P1 Lemma 3.2 ... is, at $\lambda=\infty$, I-2 Theorem 6.1(iv) together with (D1), (D2)"), the paragraph after Corollary 2.2 ("(Σ1) is I-2 Theorem 6.1(iv) with (D1)"), and the proof of Corollary 2.2.

**Argument.** The whole gain in Corollary 2.2 comes from $\sigma=C_0s_{jk}$ and $|\psi\cdot\psi-1|<\sigma^2\varepsilon$ (these give $\sigma^{4}R^2$ and $\sigma^{3-\alpha_1}R^2$, hence $s^{d+\alpha_2}$, $s^{d+\alpha_3}$). I-2(iv) in `BACKGROUND.md` §6.3 states: data in $\tilde\Psi^c(\mathbb B'_k;\delta,\varepsilon)$ give $\Psi\in\tilde\Psi^c(\mathbb B_j;2C_4K_1\delta,\varepsilon')$. That is a statement of the same size $\delta\sim\varepsilon_k$ at level $j$; it contains no factor $s_{jk}$. In addition (R2) of §1.3 gives only $\big||\psi|^2-1\big|<\delta$ (first order in $\delta$), whereas I-6 needs the finer $\sigma^2\varepsilon$ (second order in the level-$j$ smallness). With only (R2), Step 3 gives $\sigma^2R^2$ instead of $\sigma^4R^2$, the exponent becomes $d-2\gamma<d$, and the sum over $j$ diverges. So (Σ1) with the scaled radius is an additional statement (P1 Lemma 3.2, (3.22)), not a consequence of I-2(iv).

**Fix.** Add to I-2 a scaled version: for $(\psi_k,h)$ with $\phi_k\in\Phi_k(1,\varepsilon_k)$ (or $\tilde\Psi^c$ at $\delta=\varepsilon_k$), the composed field satisfies adjacent-block differences $\le C_0s_{jk}\varepsilon_k$ and $\big||\psi^{(j)}_k|^2-1\big|\le C_0^2s_{jk}^2\varepsilon_k$, with the (R3), (R4) conditions in the level-$j$ units. This follows from formula (6.2) (the discrepancy $\psi_n-Q_n\phi$ equals $(a_p/a_n)L^{2(n-p)}(\psi'_p-Q_p\phi')$, which carries $s^2$) together with the gradient bound of I-1(c). It is short, but it must be a stated and frozen item, since I-6 and the LF main-action cancellation consume it. The answer to Question 3 depends on it (see §7.6 below). Note also that the proposed $\tilde\Psi^c$-form of the analyticity domain of $\mathscr E^{(j)}$ must use a radius $K\varepsilon_j$ with $K\ge2C_4K_1$, because I-2(iv) loses that factor already at $j=k$.

### S-03 (MAJOR) I-7: the reduction to `exists_rg_solution_triangular` is not exact

**Location.** §3.4, paragraph after Lemma 3.1 ("These are exactly the hypotheses `TriangularBounds A ε` ...") and Theorem 3.2(a).

**Argument.** The landed theorem takes one fixed matrix `A` (it is bound before `P`, `c`, `f`); only `c` and `f` depend on the parameter `p ∈ P`. In the RG system $A=A(\xi,p)$, and already $A(0,p)$ depends on the data: $a_{11}=a_{k+1,u}$ (a function of $a_k$), $v=\nu_kL^2$, and $c_1(v),c_2(v)$. The document moves only the $\xi$-dependence into $\tilde c$ ("$\tilde c(\xi)=c(\xi)+(A(\xi)-A(0))\xi$"), which leaves $A(0,p)$ as a function of $p$. It cannot be moved into $\tilde c$ either, because then $\tilde c$ would not be of second order. For a single data point one may fix $A:=A(0,p_0)$, but then the conclusion "analytic in $p$" and the uniform smallness hypotheses are only available on a small neighbourhood of $p_0$ in which $\|A(0,p)-A(0,p_0)\|$ is small; this does not give the claimed result on the open set of all admissible data. Two further small differences: (i) "real for real data" is not a conclusion of the landed theorem (it needs a conjugation-symmetry argument using uniqueness and a real structure on `G`); (ii) the document's Theorem 3.2 hypothesis "$\beta_{k+1}^{-1}\varepsilon_{k+1}^{-2}\le\frac2{\alpha_0^2}\beta^{-1}$" omits the factor $L^{-2\gamma(k+1)}$ that (3.2) then contains.

**Fix.** Generalize the landed theorem to an analytic matrix-valued `A : G → Matrix (Fin 3) (Fin 3) ℂ` with `TriangularBounds (A p) ε` for all `p ∈ P`, and `A(p)` independent of `ξ` (the `ξ`-dependence still goes into `c̃`). The proof change is local: the inverse `B(p)` of a triangular matrix is analytic in `p` by the explicit formula, and the bound $\|B(p)z\|\le42\|z\|$ is `TriangularBounds.norm_le` pointwise. Estimate of the change: 100–300 Lean lines. Add the real-for-real clause as a separate lemma.

### S-04 (MAJOR) Def-6 as proposed is not the class of LF-ARCHITECTURE Def-7 (D2), nor of P5/P6 for $k\le k_0$

**Location.** §1.3–1.4 and §7.1 (Def-6 "yes, after rulings 2, 3, 5") against `LF-ARCHITECTURE.md` Def-7 (D2) ("P4 (H.1)–(H.7) at $\lambda=\infty$ and P5 H2–H4 (the class Def-6), with the backgrounds without the $\nu$-term (P5 (1.9))") and the table row (P2) of §1.4 ("... incl. (1.8)").

**Argument.** Three differences are not reconciled in the document.
1. *The $\nu$-term.* P5 p. 490 and P6 p. 2 (review `P5` line 37, `P6` line 65) say that for $k\le k_0$ ($\beta_k\nu_k\le1$) the variational problems defining $\phi_k,\psi^{(j)}_k$ omit the $\nu_k$-term and $h$, and the $\nu$-term is a perturbation. `SMALLFIELD.md` (H.1) and $\Phi_k$ keep $\frac\nu2\|\phi-h\|^2$ in $A_k$ and in (EL), and the renormalization conditions (H.5) and the equation (E2) are built on that. Def-7 (D2) uses the other convention. Both cannot be called "Def-6".
2. *The antisymmetric sum (P5 (1.8)).* Def-6 here is the whole-lattice class (H.2); Def-7 (D2) includes P5 H2–H4 with (1.8). The document says in §1.4 that $A_y$ is the same object and that the subdomain version needs the extra sum, but §7.1 proposes freezing the whole-lattice predicate under the name that Def-7 (D2) consumes.
3. *The localization exponent.* LF-3 (`LF-ARCHITECTURE.md` after Def-7) cites P5 p. 499: new terms satisfy (H.4) with $\frac32\kappa$. The document uses $2\kappa-3-6\kappa_0$ (see S-06); these are compatible but the frozen forms must be stated once.

**Fix.** The orchestrator must rule before freezing: either (a) Def-7 (D2) adopts P4's full-$\nu$ backgrounds for all $k\le k_0$ (BACKGROUND I-1 and the landed Green estimates are uniform in $\mu\ge0$, so this is available, and it makes I-6, I-7 literal) and the P5 (1.9) omission is dropped as a convention; or (b) Def-6 gets a second variant with $\nu$ dropped from the backgrounds, and I-7 is redone for it (the equation (E2) then changes meaning). I recommend (a). In either case Def-7 (D2) should say "Def-6 plus the extra sum (1.8) on subdomains" explicitly, so that Def-6 is a sub-predicate of Def-7 (D2) with no overlap in meaning.

### S-05 (MAJOR) I-7 proposed as a frozen theorem with proof-step hypotheses

**Location.** §7.1 row I-7 ("Theorem 3.2 (a)–(c) with hypothesis (B1) written as the analytic bounds (5.24)–(5.25)"), §3.2 (B1), §3.5 clause (CONT).

**Argument.** (B1) is the conclusion of I-8(c) and of the domain lemma, converted into Cauchy bounds on $f_i$, $c_i$ (P4 (5.15)–(5.19), (5.24)–(5.25)). A frozen theorem "the RG system has a unique small solution, with rate $|\gamma_\infty-1|\le C/\beta$" which takes (B1) as a hypothesis has a step of the proof as hypothesis, against AGENTS rule 4 (the document applies this rule to I-9 vs I-8 in §5.4 but not to I-7). As an abstract analytic lemma on functions $c,f$ (like the landed `exists_rg_solution`) it is fine; as a statement about the RG flow of the model it is not.

**Fix.** Freeze the consequences that Root-C consumes ((F1) with the rate and (CONT)) as part of, or as a corollary of, I-9 (class membership as the only hypothesis), and keep Theorem 3.2 as an editable abstract lemma.

### S-06 (MINOR) I-8: the exponents are not the ones P6 proves; the iteration condition for $\mathscr M$ is missing

**Location.** Theorem 4.1(a), (b), §4.3 Steps 1, 4, §4.4 item 3, §0 ("$\kappa\to2\kappa-3-6\kappa_0$").

**Argument.** P4 Prop 2.1 (p. 696) prints $2\kappa-3-6\kappa_0$, but the proof in P6 ends with $2\kappa-3-7\kappa_0$ for $\mathscr E_0^{(k+1)}$ (P6 (4.56), after the extra resummation over $Z$ determining $Y$) and with $2\kappa-4-7\kappa_0$ for $\mathscr M_0^{(k+1)}$ (P6 (4.65), (4.67)); P6 then assumes $\kappa-4-7\kappa_0\ge\frac12\kappa$, which gives the $\frac32\kappa$ of P5 p. 499 and LF-3. The determinant part $D^{(k)}$ has decay $2\kappa$, not $2\kappa-3-6\kappa_0$ (P6 p. 39: "(4.54) with $2\kappa$ instead of $2\kappa-3-6\kappa_0$"); Step 1 of §4.3 attributes the smaller exponent to it. The condition in §4.4 item 3, "consistent only for $\kappa\ge3+6\kappa_0$", covers $\mathscr E$ only; for $\mathscr M$ (loss $4+7\kappa_0$) it must be $\kappa\ge4+7\kappa_0$, and the single condition $\kappa-4-7\kappa_0\ge\frac12\kappa$ of P6 covers both.

**Fix.** State the loss as $\kappa\mapsto2\kappa-4-7\kappa_0$ (both items, with $\mathscr E$ allowed $2\kappa-3-7\kappa_0$) and the condition $\kappa\ge8+14\kappa_0$; this is the right form for the frozen I-8/I-9. The loss "per step $\kappa\to2\kappa-\cdots$" is harmless because the output is only required to be $\ge\kappa$ again (the old terms keep $\kappa$), as the document says.

### S-07 (MINOR) I-8(b): the normalisation of $\mathscr M_0$

**Location.** Theorem 4.1(b); §4.3 Step 5.

**Argument.** The document quotes P4 Prop 2.2: $|\mathscr M_0^{(k+1)}(x,Y)|\le C\beta^{-(3/8+\alpha_1)}\xi_{k+1}^{\frac{d-2}2+\gamma-\alpha_1}e^{-\cdots}$. P6's own bound (4.67) is $\mathrm{const}\cdot\beta^{-1/8+\alpha_1}\eta^{\gamma-2\alpha_1}e^{-(2\kappa-4-7\kappa_0)d}$ for the function before multiplication by $\beta_k^{-1/2}$, and after multiplication $\beta^{-5/8+\alpha_1}\eta^{\frac{d-2}2+\gamma-2\alpha_1}$, with the conclusion "(H.7) with $c_9=\beta^{-1/4}$". So the power of $\eta$ is $-2\alpha_1$, not $-\alpha_1$, and the sign of $\alpha_1$ in the power of $\beta$ differs from P4. The two forms agree only because $\beta=\beta_k\ge BL^{k(d-2)}=B\eta^{-(d-2)}$, so that $\beta_k^{-(5/8-\alpha_1)}\eta^{-\alpha_1}\le C\beta_k^{-1/4}$ for $\alpha_1$ small. This absorption is a step of the proof and uses the running $\beta_k$, not the initial $\beta$.

**Fix.** State (b) in the form $\le\frac12c_9\,\xi_{k+1}^{\frac{d-2}2+\gamma-\alpha_1}e^{-(2\kappa-4-7\kappa_0)d_{k+1}(Y)}$ for $\beta$ large (output of I-8, constant independent of $k$), and put the absorption into the proof; list $\alpha_1<(d-2)\cdot\frac58/(d-1)$-type restriction explicitly if it is needed.

### S-08 (MINOR) Lemma 3.1 and Theorem 3.2: the range of $a$

**Location.** §3.1 (i), Lemma 3.1, SF-6.

**Argument.** Lemma 3.1 needs $a_{k+1}\ge\frac9{10}$. Under the free flow $a^f_k\downarrow a(1-L^{-2})$, so this holds for all $k$ only if $a\ge\frac9{10}(1-L^{-2})^{-1}$; P4's range $a\in(1,\frac32)$ does not imply it for $L=2$ ($a(1-\frac14)<0.9$ for $a<1.2$). The recommendation "$a^f_k\in[1,\frac32-\frac1{10})$" in §3.1 is correct but is not carried to the statements of Theorem 3.2 and 5.1, which quantify over "the kernel constant $a$".

**Fix.** Put the restriction $a\in[\frac9{10}(1-L^{-2})^{-1},\frac32)$ into the constants of Def-6 (and use $a=(1-L^{-2})^{-1}$ when a specific value is wanted). My re-check of the arithmetic of Lemma 3.1 under this restriction: $a_{33}\ge\frac12\rho^2(1-v^3c_2)>0.32$ with $\rho\ge0.80$, $a_{33}<0.55+0.25$, the bracket in $a_{32},a_{31}$ lies in $[-1.03,-0.92]$; the bounds claimed ($|a_{31}|\le2.1\varepsilon$, $|a_{32}|\le0.3$) are correct, and they match the fields of `TriangularBounds` (`d0`, `d1`, `d2`, `l10`, `l20`, `l21`).

### S-09 (MINOR) Interface (F1): ranges of $\nu$ and $k$, the value at $\nu=0$

**Location.** §3.5 (i)–(ii), §3.4 Theorem 3.2(c); `C1Star.lean` `C1StarF1`.

**Argument.** `C1StarF1` quantifies "for all $\nu\in[0,1]$, all $k$" with a value $\xi(0,k)$ and a right-limit at $0$. The small-field flow exists only while $\nu_k\le\bar\nu\le\frac78L^{-2}$, i.e. for $\nu\le\bar\nu$ and $k<k_f(\nu)$; the class excludes $\nu=0$ ($0<\nu_k$). So (i) "settled for every $\nu\in(0,\bar\nu]$" does not cover the quantification of the Lean interface. Also `C1Star.lean` uses `freeSeq` in `mainTr` (the free flow), which bears on Question 1.

**Fix.** Define the extension by a convention ($\xi(\nu,k):=0$ for $k\ge k_f(\nu)$ and for $\nu>\bar\nu$; $\xi(0,k):=\lim_{\nu\downarrow0}\xi(\nu,k)$, which satisfies the bound by passing to the limit) and state this in C-1\*. Root-C's Tannery argument uses only $k\le J(\nu)<k_f(\nu)$, so nothing else changes.

### S-10 (MINOR) Theorem 3.2(c): $\delta_\infty$ and the constants

**Location.** §3.4 Theorem 3.2(c).

**Argument.** The landed `exists_gamma_infty` gives $\|\gamma-1\|\le c_8q/(2(1-q))$ but, for $\delta_\infty:=\gamma^{-1}\gamma'$, only the bounds $\|\delta^{\pm1}\|\le e^{c_8q/(1-q)}$. The claim $|\delta_\infty-1|\le c_8q/(2(1-q))$ is not in the landed lemma; from $\gamma^{-1},\gamma'$ each within $c_8q/(2(1-q))\le\frac12$ of $1$ one gets $|\delta_\infty-1|\le3\cdot c_8q/(2(1-q))$ or so. Only $\gamma_\infty$ is needed by Root-C. The rate for $\gamma_\infty$ (the claim of the document that $|\gamma_\infty-1|\le 2C_\xi q\beta^{-1}/(1-q)$ is "proved here") is correct given $|\xi^0|\le C_\xi\beta^{-1}L^{-2\gamma(k+1)}$, and is indeed new relative to CORRELATIONS (F1): I confirm that P4 (5.25)–(5.31) give it with no need for $c_8$ arbitrarily small.

**Fix.** State the $\delta_\infty$ bound with a numerical factor, or drop it.

### S-11 (MINOR) The factor $1/v$ in (5.5)/(5.25) is resolved; the notation should be fixed

**Location.** §3.2 (E2), §3.5 "On the factor $1/v$", SF-3.

**Argument.** On P4 p. 708, (5.4) gives $\partial_vc^{(k+1)}_1(1,1,0)=-(a+\beta^{-1}c)\zeta\frac1\lambda(\cdots)v-\beta^{-1}e\,v$, and (5.5)(2) divides the $v$-derivative by $v$ so that the term $\beta\cdot\beta^{-1}e=e$ has coefficient $1$ ($a_{22}=1$ of (5.21)). This is consistent only if $\partial_v$ is the radial $h$-derivative, $\partial_h\mathscr V\cdot e_1=\nu\,\partial_b\mathscr V\cdot e_1$; then $\frac1v\partial_v=\partial_b$, the counterterm contributes $e$, and the data $\partial_bf_u$ are bounded by $E_0K_0/\delta_0^2$ uniformly in $\nu$ (Cauchy radius $\delta_0^2$ in the variable $\psi\cdot b/u$). This is the document's reading and it is correct. The document's text is internally inconsistent in one respect: in §2.3 Step 3 the letter $v$ denotes $\psi\cdot b/u$ (the $b$-variable, base value $\nu_j$), whereas in (E2) "$\frac1v\partial_vf_u$" needs $\partial_v=\nu\partial_b$.

**Fix.** Write (E2) in the $b$-form, $\partial_bf_u(1,\nu,0)\cdot e_1+\beta\xi_2+\beta\,\partial_bc_2=0$, with no $1/v$, and remove the UNCERTAIN label and SF-3. The landed `TriangularBounds.d1` ($\|A_{11}\|\ge1$) is then exactly $a_{22}=1$. About P4 (5.9) (SF-4): on p. 709 (5.9) reads $\phi^{(2)}=-e_1G(G+\frac1\lambda)^{-1}[(H_{tr}\psi')\cdot(H_{tr}\psi')+\cdots]-2G(\cdots)$, so at $1/\lambda=0$ it gives $e_1\cdot\phi^{(2)}=-|H_{tr}\psi'|^2$, whereas $\phi\cdot\phi=1$ forces $e_1\cdot\phi^{(2)}=-\frac12|\phi^{(1)}|^2$. The document's observation is right: (5.10) carries the compensating $\frac12$ in "$-\frac12(a+\beta^{-1}c)\zeta\langle e_1,\phi^{(2)}\rangle$", while the correct expansion of $\zeta\langle\psi,\psi-Q\phi\rangle$ has coefficient $1$; the product is the same, $+\frac12(a+\beta^{-1}c)\zeta\|H\theta\|^2$. My own check of the order-one and order-two relations at $\lambda=\infty$ ($\alpha^{(1)}=aQ^*\psi_1'$, $\phi^{(1)}=aGQ^*\psi'_\perp$) agrees with §3.3. SF-4 can be downgraded to a printing remark.

### S-12 (MINOR) Smaller points

1. §2.3 Step 0 and SF-8: the polynomial weights $(1+d)^{6}|X|^2$ with $|X|\le(3LM)^d(1+d)$ are absorbed by $e^{-d}$ with a constant, so $\kappa\ge\kappa_0+1$ suffices; "$\kappa\ge\kappa_0+7$" is not needed.
2. Step 4: the claim that the conditions defining $\tilde\Psi^c$ "scale linearly in $\tau$" is true for the difference conditions (C1), (C2) first part; the quadratic condition $|\psi\cdot\psi-1|$ is quadratic in $\tau$. I checked that the displacement $\tau\delta$ with $|\tau|\le c/((1+d)\sigma R)$ keeps it inside the radius (the linear part is $\tau\cdot O(\sigma^2\varepsilon)$ and the quadratic part $(\tau\sigma R\varepsilon_j(1+d))^2\le c^2\varepsilon_j^2$), but the sentence should say so.
3. §3.5 Vitali: pointwise convergence on a set with an accumulation point plus a uniform bound gives locally uniform convergence on the open polydisc in several variables, so the sup over $B_{r_0}$ with $r_0\le c_{10}/2$ is controlled; the argument is correct as long as (CONT) gives convergence on a set with an accumulation point inside a connected polydisc.
4. §3.1 sequence $a_k$ under (ii): the recursion $|\log r_{k+1}|\le\theta_*|\log r_k|+|\log(1+\xi_3)|$ is correct (the log-derivative of $\varphi(tx)/\varphi(x)$ in $\log t$ is $aL^{-2}/(tx+aL^{-2})$, evaluated near $t=1$), but it is only needed if (ii) is kept.
5. Theorem 5.1: the order of constants is stated in §5.2 Step 8; $C_\xi=168B_6K_5/\alpha_0^2$ depends on $\alpha_0$, so $B$ depends on $(\alpha_0,c_8,c_9)$; this should be said in the statement ("there is $B$ depending on ...").

## Answers to the checklist

**1. I-7.** The triangular structure, the coefficient bounds and the rate $|\gamma_\infty-1|\le C/\beta$ are right (S-08, S-10, S-11); the reduction to the landed theorem is not exact (S-03: the matrix must be allowed to depend on the data; also real-for-real). Hypotheses that do match: `d0`–`l21` of `TriangularBounds` (via Lemma 3.1), $\varepsilon=\varepsilon_{k+1}\le1$, `hcb` for $\tilde c$ (second order with $\tilde\kappa\le K_5C_4+C$, assuming the entries of $A$ are analytic in $\xi$ on the polydisc, which needs $|\xi_2|<1$, true for $c_{10}<1$), `hfb` with $\eta=B_6K_5\beta_{k+1}^{-1}\varepsilon_{k+1}^{-2}$ (one should note that $\beta_{k+1}^{-1}=(1+\xi_3)/(\beta_kL^{d-2})$ depends on $\xi$ and is bounded by $\frac32\beta_k^{-1}L^{-(d-2)}$ on the polydisc), and `hcond` (P4 (5.27)). The continuity in $\nu$: Lemma 3.3 is correct ($\|\xi_p-\xi_{p'}\|\le2\sup\|\Phi_p-\Phi_{p'}\|$ from $\mathrm{Lip}\le\frac12$) and (CONT) is the right clause; the clause must be propagated inside I-9, which needs I-1/I-2 analytic in $\mu$ near $\mu=0$ (BACKGROUND treats $\mu\ge0$). The statements on P4 (5.9) and the $1/v$ factor are right (S-11).

**2. I-6.** The new proof is the right mechanism, with the repair of S-01 and the extra input of S-02. Every input is named ((H.2)–(H.5), I-1(e) for (Σ2), I-2 for (Σ1), P6 (4.11), P1 Lemmas 3.1, 3.3), and the bound is uniform in $k$ because all constants depend only on the listed parameters; the uniformity of (Σ2) rests on I-1(e) with the exponent $\theta=\alpha_1$ fixed before $K_\Sigma$ (quantifier order: $\alpha_1$, then $K_\Sigma$).

**3. I-8, I-9.** I-9 as stated takes only class membership; I-8 is internal to it, so rule 4 is respected (§5.4). The base case (ER-062, ER-063) is outside I-9 and needs its own statement (LF-6): the step theorem does not start the induction, and the document says so. The loss of $\kappa$ is $2\kappa-3-7\kappa_0$ for $\mathscr E_0$ and $2\kappa-4-7\kappa_0$ for $\mathscr M_0$ (S-06), not $2\kappa-3-6\kappa_0$.

**4. Consistency.** With CORRELATIONS: (F1) is supplied up to S-09; (F2), (F3) require X1–X7, which are listed but not proved (this is the main part of the 40k–80k line item). With LF-ARCHITECTURE v4: S-04 (class variants) and Question 1 below. With BACKGROUND: (Σ1) is not I-2(iv) (S-02); I-1(e) matches (Σ2) (BACKGROUND line 508 states it); Prop 5.1/§5.4 linear response matches §3.3.

**5. Size.** The table's total (265k–470k) is plausible only if I-8 and I-9 are costed together and the Gaussian/Green machinery already counted in the Background and Green layers is not charged again. Where it looks high: I-6 (40k–70k) for a two-page argument whose geometric inputs are cited: I would expect 25k–45k (invariant reduction with complex rotations, Cauchy/Taylor in several variables, the stabilizer decomposition, the polymer sums); I-7 (25k–40k): the landed core is 0.7k, the new content is the second-order expansion of (EL), the lattice sums $c_1,c_2$ and Lemma 3.1, I expect 10k–20k; I-9 (90k–160k) overlaps with I-8 (Steps 1–3 of §5.2 are the same objects as §4.1 items 1–5), I expect 60k–110k if I-8 is separate. Where it could shrink: (a) prove I-8 once with the hole parameter ($\mathrm{mod}\,\Omega^c$) from the start, because P6 proves the general form and LF-3 will need it (otherwise the whole-lattice proof is redone); (b) drop analyticity in the data $(\mathscr E^{(j)})_{j\le k}$ from the statement (§5.6(iii), agreed); (c) use existential constants in I-9 and do not formalize the explicit chain of §5.2 Step 8; (d) take $c=a_{k+1}b$ (free flow), which removes the sequence-perturbation lemma and makes $a_k$ deterministic; (e) torus families only through finite-set terms (as in the document). My revised range is 190k–350k.

## Answers to §7.6

1. **Free flow or $c=0$.** The sources do not decide it. P4 Prop 5.1 proves $c=a_{k+1}b$ (pp. 707–718); $c=0$ is only remarked on p. 717 ("without any changes"; ER-067), and P5–P7 use $c=0$, $d=b$ without a proof. For I-7 both are admissible and agree at $\xi=0$ (§3.1, correct). Evidence for the free flow: `C1Star.lean` already uses `freeSeq` in `mainTr`, and CORRELATIONS needs the exact identity $\sum_jT_j=(-\Delta)^{-1}$ (P9 (4.17)); evidence for $c=0$: the large-field papers use it. I recommend the free flow in Def-6 and Def-7, conditional on one confirmation from the LF side: that no step of P5–P7 uses $c=0$ beyond $a_k\in(\frac12,\frac32)$. Because $a_{k+1}=a_{k+1,u}$ under the free flow, the shifts $\delta\psi^{(j)}_{k+1}$ caused by $a_{k+1}\ne a_{k+1,u}$ do not occur at all, which simplifies I-9 Step 5.
2. **(CONT).** Accept it as a clause of the class, in the $(\psi,b=\nu h)$ variables; no source states it, but it is needed by (F1) and holds by construction (the step is an explicit map analytic in the parameter $\mu=\nu_kL^{-2k}$). It must be proved to propagate in I-9, and I-1/I-2 must be available analytically in $\mu\ge0$ (they are, BACKGROUND). See S-09 for the range conventions.
3. **Domains by $\tilde\Psi^c$.** Yes, with the scaled statement of S-02 added to I-2 and with a radius $K\varepsilon_j$, $K\ge2C_4K_1$, for the analyticity domain of $\mathscr E^{(j)}$ (I-2(iv) loses $C_4K_1$ already at $j=k$). Without S-02 the choice would remove the gain on which I-6 rests.
4. **$\gamma_0=\frac12$.** Any $\gamma<\frac12$ suffices for I-6 to I-9 as written: $\alpha_3=1-2\gamma-\alpha_1>0$ and $q=L^{-2\gamma}<1$ are all that is used, and P4 itself requires $0<\gamma<\min\{\frac{d-2}2,\frac12\}$. No source needs the improvement to $\gamma_0=1$ in this chain (P1 pp. 145–147 says so). For Root-C P9's $\rho_0\le\min\{2\gamma,d-2\}$ is compatible.
5. **Numbering.** Freeze P4's (H.1)–(H.7) with P1's in brackets, as in §1.3 (BIG §2.4 concordance). Note that §1.3 corrects P4's (H.5) to act on the new term only, and that the $b$-form of (H.5) is a rewriting of P1 (H.6)–(H.7): state both in the docstring.
6. **Form of I-8.** Do not freeze I-8 as a separate statement. Its four items refer to objects defined by the formulas P4 (2.52)–(2.60), (4.14)–(4.18), so a frozen statement would freeze those definitions too. It is an internal lemma of I-9 (as §5.4 arranges). If a frozen form is wanted, use the modular form (with $\Omega^c$): P6 proves the general form (P6 Lemma 4.1, Prop 4.* with $\mathrm{mod}\,\Omega^c_{k+1}$), the whole-lattice one is the special case, and LF-3 needs the general one.
7. **(H.5)(4) per centre or summed over centres.** Equivalent by translation covariance (answer in S-01); no torus limit is needed for the finite-set terms.

## Summary of required changes before freezing

1. S-01: add the freezing of $\partial\Theta\cdot\partial\Theta$ at $y$ to Step 5 (the statement of Theorem 2.1 stays).
2. S-02: add the scaled-domain statement to I-2 and cite it in (Σ1).
3. S-03: generalize `exists_rg_solution_triangular` to a data-dependent analytic `A`; add the real-for-real lemma.
4. S-04: orchestrator ruling on the $\nu$-term, (1.8) and the class relation between Def-6 and Def-7 (D2); then freeze Def-6.
5. S-05: freeze the (F1)-consequences with I-9, not Theorem 3.2 with (B1).
6. S-06–S-12: correct the exponents ($2\kappa-4-7\kappa_0$), the range of $a$, the (F1) conventions, the (E2) notation, and the size table.
