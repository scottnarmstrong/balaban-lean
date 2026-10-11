# Review of `notes/phase1/CORRELATIONS.md` (D-C, Root-C from the flow)

Reviewer: independent, refute-first. Date: 2026-10-11. P9 page references are journal pages (PDF page = journal − 492); I read pp. 494–495, 496–498, 516–519 (p. 517 from the page image, because the text layer garbles the last-step bound).

**VERDICT: APPROVE-WITH-CHANGES.** I found no blocker. Everything derived from Root-F alone (§0.1, §1, §4) re-derives correctly, with only constant-tracking slips. The conditional derivation of Root-C from C-1\* and I-G (§3) is sound given the interface. The interface statements I-F2/I-F3 misreport P9, and C-1\*/Root-F/I-G are not shown to refer to the same torus family and the same $L$ (D-01, D-02). The I-G mass range does not match the cited G-5 or the Root-F normalization (D-03).

## Findings

| ID | Sev | Location | Finding | Evidence | Proposed fix |
|---|---|---|---|---|---|
| D-01 | MAJOR | §2.2 (F2), (F3); §2.3 (ii), (iv); §3.3 | The interface uses scalars $\mu_j$ and a constant $m_J$, with main term $m_J^2\sum_j(\beta\gamma_j)^{-1}t_j$. P9 has an $x$-dependent $m_k(x)$ (2.8), $m_0^{(j)}(x)$ (2.9), with main term $\beta_{j-1}^{-1}m_k(x)G^{(j)}(x,x')m_k(x')$ (2.11), and $M_k(x,h,h)=m_k(x)h$ (4.10). $m_0^{(j)}$ is periodic only under the scale-$j$ lattice, so it is not constant. The citation "P9 (2.8)–(2.9)" does not support scalar $\mu_j$. | P9 p. 496, (2.8); p. 498, (2.11); p. 517, (4.10). | State (F2)/(F3) with $m_J(x)$. Or fix a base point, $\mu_j(\nu):=m_0^{(j)}(0;\nu)$ and $m_J(\nu):=m_J(0)$, and add $|m_J(x)-m(\nu)|\le c\beta_J^{-2}$ (this follows from (4.8) and $M=m h$). Then absorb $[m_J(x)m_J(x')-m(\nu)^2]\,C_J$ into $r_{tr}$; this is allowed because $\beta_J^{-2}\le L^{-2J(d-2)}\beta^{-2}$ and $L^J\sqrt\nu\le L^2$. Continuity of $m_0^{(j)}(0;\nu)$ at $0$ is then the clause to freeze. |
| D-02 | MAJOR | §3.1 ("The infinite-volume functions of C-1\* are these functions"), §2.2, §2.3 (i) | Root-F's limits are taken along $q_C^n\mid\ell$, $q_C=M_FL_F$. C-1\* is built from its own integer $L$, with tori divisible by $L^{K}$, and I-G uses limits through multiples of $L^{j+1}$. Nothing says that $L_{C\text{-}1^*}=L_F$, nor that C-1\* is stated for a torus family. Nothing says that its "infinite-volume functions" exist, or that they agree with §4's limits on common multiples. §2.3 (i) is a one-line appeal to P4 (H.4). The identification is the hinge of Theorem 3.1 and is not proved. | §3.1 last paragraph; §4 Remark 4 (independence of $q$ holds only if both limits exist). | State C-1\* as finite-torus estimates, on every torus with $L^{K}\mid\ell$, together with the existence of the limit along those tori. Then add a lemma: if $A_n$ converges along $\ell\in a\mathbb N$ and along $\ell\in b\mathbb N$, the limits agree (take multiples of $\operatorname{lcm}(a,b)$). Either require the same $L$ and $J$ in Root-F and C-1\*, or record that the comparison goes through $\operatorname{lcm}$. |
| D-03 | MAJOR | §2.1 (G2), (G3); §3.2–3.3 | The masses fed to the kernels are $\mu=\nu\delta_j(\nu)\in(0,2\nu]$, up to $2$ (since $\delta_j\le2$), but (G2), (G3) are stated for $\mu\in(0,1]$. Cited G-5 is for the unit-lattice mass $\nu_j\in[0,1]$. With the Root-F normalization $L^{k_f}\sqrt\nu\le L$, i.e. $L^J\sqrt\nu\le L^2$, the last Gaussian index $j=J-1$ has $\nu_j=\nu L^{2j}\delta_j$ up to about $2L^2>1$. `GREEN.md` C14 uses a different normalization ($\nu_j\le\frac78L^{-2}$). P9 p. 518 takes $\sup_{v_j\in(0,1]}$. So (G2) uniform for $\nu_j$ up to $\sim L^2$ is an extension of G-5, not a citation. | `GREEN.md` G-5 (line 365), C14; Root-F docstring; P9 p. 518. | Restate I-G with $\mu\in(0,\mu_{\max}]$, $\mu_{\max}=2$ ($\nu_j\le 2L^2$), marked "extension of G-5". Or align the normalization of $J(\nu)$ with GREEN so that $\nu_{J-1}\le1$ (change Root-F's constants, or note the factor $L^2$). |
| D-04 | MINOR | §2.1 dictionary, (2.2) | "Derived here" is not substantiated for general $j$. The only check at $j=1$ tests the penalty, not the kernel. With the stated conventions ($G_j$ plain, $Q^*=L^dQ^\top$, $M_1=L^{d-2}C^{-1}$) the penalty and effective-operator consistency force $G^{P9}=L^{-2}G$, and then $T_1=P_1M_1^{-1}P_1^\top=a^2L^{d-2}GQ^\top CQG$. The P9 expression $L^{-(d-2)}a^2G^{P9}Q^*CQG^{P9}$ equals $a^2L^{-2}GQ^\top CQG$, which differs by $L^d$. The mismatch is presumably the unspecified weighted-kernel convention. The coefficient $(\beta\gamma_j)^{-1}$ in (F3) is nevertheless right, because P9 (4.17) forces the bracket in (4.16) to be $T_j$. | P9 pp. 517–518, (4.12)–(4.17); the document's own derivation in §2.1. | Say "consistent with P9 (4.16)–(4.17) by the requirement $\sum_jT_j=(-\Delta)^{-1}$" and drop "derived". Or write out the weighted convention and verify (2.2) for $j=1$ in full. Keep Q3. |
| D-05 | MINOR | §0, Prop 1.5, Cor 1.6 | "$|G|\le Cc_9(1+|x|)^{-\theta}\dots$ uniformly, for every $c_9$": $C_*=C_*(d,L,M,\delta)$ and $c'=\kappa_*/(4ML^2)$ depend on $L,M$, which Root-F supplies after $c_9$. So $C$ is not independent of $c_9$ and "$|G|\le C\epsilon$ with $c_9=\epsilon/3$" does not make $G$ small. Part (a) ($3c_9$) is fine. No harm for Root-C, which fixes $c_9=1$. | Root-F quantifier order $\forall\kappa\forall c_9\exists L,M,\beta_0$; Lemma 1.3 constant depends on $\delta=\kappa/(4M)$. | Rewrite as $C_*(c_9)c_9$, or state the bound for $c_9=1$ only. Correct Cor 1.6's second claim. |
| D-06 | MINOR | §5 item 9; §2.3 (iv) last sentence | The bound on P9 p. 517 is legible in the page image: $\le O(1)\beta^{-2}L^{-(k+1)\frac{d-2}2}|x-x'|_1^{-\frac32(d-2)}\exp(-\frac12\delta_0L^{-(k+1)}|x-x'|_1)$, with $\beta^{-2}$ (not $\beta_J^{-2}$) and the $\ell^1$ norm. The document's "$\beta_J^{-2}e^{-\kappa|x|/L^J}$" is not what is printed. The printed bound does give (F3)'s decay. With $u=L^{-k}|x|$ the expression is $|x|^{-2(d-2)}u^{(d-2)/2}e^{-\delta_0u/2}\le C|x|^{-2(d-2)}$ times a mass factor. This needs $\rho_0\le d-2$ (not stated in C-1\*). | P9 p. 517 (image), (4.9). | Replace the UNCERTAIN note by this bound and add $\rho_0\le d-2$ to C-1\*. |
| D-07 | MINOR | §0, §5 item 5, §3.5 | "No source proves $|\gamma_\infty-1|\le c/\beta$": P9 states it (p. 519 after (4.18); Thm 1.1(b)). Only a proof is missing, and P4 (5.33) is cited for existence. The document's "$O(\beta^{-2})$ error in (4.18)" rests on the unproved (F1) rate $c_8=c_\xi/\beta$ and is stronger than P9's printed $O(\beta^{-1})q^j$; Root-C needs only the latter. Lean `exists_inv_betaSeq_asymptotics` is correct as quoted (hypotheses $c_8q\le1-q$ and the $\xi$ bound match). | P9 p. 519; `RunningCoefficients.lean` L290–. | State that Root-C needs only $|E_j'|\le C\beta^{-1}q^j$, and that $|\gamma_\infty-1|\le c/\beta$ needs (F1) with $c_8=O(1/\beta)$. Present $\beta^{-2}$ as a bonus. |
| D-08 | MINOR | §2.2 C-1\*, §3.5 | $a\in(\frac12,\frac32)$ does not guarantee G-5's hypothesis $a_j\in(\frac12,\frac32)$ for all $j$: $a_j=a(1-L^{-2})/(1-L^{-2j})\downarrow a(1-L^{-2})$. For $a=0.55$, $L=2$ this is $0.41<\frac12$. | Dictionary formula for $a_j$; `GREEN.md` G-5 hypotheses. | Require $a\in(\frac{1}{2(1-L^{-2})},\frac32)$. |
| D-09 | MINOR | §0.1 Lemma 0.2, §6 A | The list of Mathlib facts needed for $\operatorname{toSphere}$ is incomplete. Needed: (i) finiteness and nonzero total mass ($\dim\cdot\operatorname{vol}(\text{ball})>0$), for $Z(0)>0$ and integrability; (ii) invariance of $\operatorname{toSphere}\operatorname{vol}$ under $O(N)$, via volume preservation of `LinearIsometryEquiv` and equivariance of `homeomorphUnitSphereProd`; (iii) product-measure transport (`Measure.pi` under a sitewise map and under `piCongrLeft`). Only (ii) is flagged. | `AprioriMeasure.lean`; Lemma 0.1 proof. | List (i)–(iii) in package A. |
| D-10 | MINOR | §3.3 / C-1\* | $J(\nu)$ in C-1\* may be $0$ (e.g. $\nu=1$ allows $L^J\in[\frac12,L^2]$). Root-F has $J=k_f+1\ge1$. Harmless but should be consistent. Also (F3) requires the infinite-volume pair $(x,y)$ form for $r$, while the limit $r(0;x,y)$ is used only at $y=0$; fine. | Statement of C-1\*. | Take $J(\nu)\ge1$. |
| D-11 | NOTE | §2.4 | The $a_0=\infty$ remark checks out: with $Q_0=I$, $\Delta^{(0)}_{tr}=a_0-a_0^2G_0\to-\Delta+\mu$, so $C^{(0)}\to(-\Delta+\mu+aL^{-2}Q^*Q)^{-1}=M_0^{-1}$, which equals `stepCov`. The literal P9 formula $a_j=\frac{1-L^{-2}}{1-L^{-2j}}a$ is also $\infty$ at $j=0$. The claim that the real flow has no penalty at $j=0$ should be confirmed against P4. | P9 (4.17); `Multiscale.lean` `fluct`. | One-line P4 check. |
| D-12 | NOTE | §5 item 1, §7 Q1/Q4 | The $\nu$-continuity demanded by (F1)–(F3) is a new claim, not in any source, and is honestly flagged. The difficulty (dependence of large-field thresholds and $k_f$ on $\nu$) is real. The two-point $r$ also contains last-step terms, which are fine (they tend to $0$ by D-06's bound). | P9 p. 518 proves only $\sum_j\beta_j^{-1}[G^{(j)}(v_j)-G^{(j)}(0)]\to0$ with $\beta_j$ fixed. | Keep as an explicit clause of Def-7. |
| D-13 | NOTE | §6 | Estimates look optimistic. Package A (450 lines) hides the $\operatorname{toSphere}$ invariance proof. Package G (700) contains the nested-torus composition "iterated = one-shot" (the prolongation composition is new) and the discrete maximum principle. Package E (600) has `ZMod`/`valMinAbs` casts and the finite-subset bijection. I would put the total at 4,500–5,500 lines rather than 3,700. The C-1 range (5–8k) is plausible. | | Update the table. |

## Reasoning per item

### 1. Derivations from Root-F alone (§0.1, §1, §4)

I re-derived all of it.

- **Prop 1.4.** The identity holds for the principal `Complex.log` on the ball. Only analyticity near $0$ is used, so the identity can be differentiated at $0$ (Lemma 0.1 gives analyticity of $\operatorname{Log}(Z/Z(0))$ near $0$). The second derivative of $\sum_{j,z,X}g_l(z)T_j(z,X;g)_l$ at $0$ is exactly the two terms stated. Locality (`g|_X`) and vanishing outside $X\ni x$ give the restriction to $X\ni x,y$.
- **Cauchy.** `norm_fderiv_line_le` with $\rho=\frac12$ applies directly: Root-F's bound is on $\sum\|g\|\le\frac12$ and analyticity on $<1$, so no "$\rho\uparrow\frac12$" is needed (NOTE). The bound is $B/\rho=2B$ per term, hence $4B$ for $G$.
- **Counting.** Lemma 1.1 is correct. With $C_0=4d^2$ and $\kappa_*=2\log(8d^2)$, $C_0e^{-\kappa_*/2}=\frac12$ and $C_0e^{-\kappa_*}\le\frac1{16d^2}$, so both displayed sums hold. The walk count $(2d)^{2(n-1)}$ is valid for multigraph collapse on tori with $\ell/s_j\in\{1,2\}$. The block structure matches `IsPolymer`, which uses blocks $\lfloor x_\mu/s\rfloor$ on `ZMod` and needs $s\mid\ell$, guaranteed by $ML^{J}\mid\ell$ and $j\le J$.
- **Lemma 1.2.** A chain of $r+1\le n$ blocks gives coordinate difference $\le(r+1)s-1$; the torus distance is at most that.
- **Lemma 1.3.** Correct. Its form $(1+r)^{-\sigma}$ is used as $r^{-\theta}$, which is weaker and harmless.
- **$|m-1|\le3c_9$.** $\sum_{j\ge1}L^{-j\theta}=1/(L^\theta-1)\le1/(\sqrt2-1)<3$.
- **Prop 1.5(b) and the exponent.**
  - The splitting $e^{-\kappa n}\le e^{-\kappa n/2}e^{-\kappa r/(2s_j)}$ is valid.
  - $L^{k_f}\sqrt\nu\le L$ gives $L^J\le L^2/\sqrt\nu$, so the mass factor is $e^{-\kappa r\sqrt\nu/(4ML^2)}$.
  - Constants: see D-05.
- **Thermodynamic limit, structure.**
  - $T$ is chosen after $(\beta,\nu,h=e_1)$, and the clause is used for arbitrary $g$ and any $j$, so it applies to $g=0$ and $g=\zeta e_k\mathbf 1_z$.
  - $4R\le\ell$ gives $\operatorname{valMinAbs}\circ\iota_\ell=\mathrm{id}$ and the box identification.
  - The reduction to $x=0$ via model translation invariance (Lemma 0.2(a)) avoids covariance of $T$.
- **Polymers eventually lie in the box; wrapping polymers vanish.** Not-contained in $\iota_\ell B_R$ means containing a point at torus distance $\ge R$ from $0$. Lemma 1.2 then gives $n(X)\ge(R+1)/s_j\ge R/s_J$. This covers wrapping polymers, since $n(X)\ge\ell/s_j$ is even larger. The tail bound $24\cdot2^{-R/s_J}$ is correct, since $4\cdot3\cdot2^{1-R/s_J}=24\cdot2^{-R/s_J}$. Divisibility $q^n\mid\ell\Rightarrow ML^J\mid\ell$ holds for $n\ge J$.
- **Limit.** Cauchy in $n$, then limit, then uniform control for all multiples of $q^{n_0}$: correct. The $2\varepsilon$ in item 2 is fine.

### 2. Symmetries

Lemma 0.2 is correct.

- **(a)** $H$ and the measure are translation invariant; the bond sum is invariant for every $\ell$ (including $\ell<3$).
- **(b)** From $H(R\phi;Rh)=H(\phi;h)$ and $O(N)$-invariance of $\operatorname{toSphere}\operatorname{vol}$ on each factor.
- **(c)** The stabilizer argument is right (sign changes force the off-diagonal entries to vanish; permutations give $G_{kk}=G_{22}$). The case $N=2$ is fine. Independence of $h$ follows from $m_\ell=M(x;h)\cdot h$. Evenness uses $G_{ik}(x,y)=G_{ki}(y,x)$.
- **Ward identity (Remark 0.3).** I confirmed $m=\beta\nu\sum_yG_{tr}(y)$: $\partial_{h_2}\langle\phi_2\rangle=\beta\nu\sum G_{tr}$, while covariance gives $m(1)\cdot1$. The weight is $e^{\beta\nu\sum h\cdot\phi}$ since $\nu/2\,|\phi-h|^2=\nu-\nu h\cdot\phi$ for $|\phi|=|h|=1$. This is a useful exact constraint on the interface: (F2) and (F3) must satisfy $m(\nu)=\beta\nu\sum_zG_{tr}(\nu,z)$. Worth noting in §2 as a consistency test (NOTE).
- **What is needed of `toSphere`.** See D-09.

### 3. Interfaces I-G, I-F1, I-F2, I-F3

- **Precision and consistency.**
  - Same $L$, same $J$, same torus family as Root-F: D-02.
  - The mass range $\mu=\nu\delta_j$: D-03.
  - Scalar versus $x$-dependent $m$: D-01.
- **Sufficiency for Root-C.** The needed clauses are present: (F1) rate and continuity, (F2) rate and continuity of $\mu_j$, (F3) decomposition, decay and convergence of $r$, and (G1)–(G3), (G5).
  - Step B and Step C are correct modulo the above. I checked the arithmetic: $\beta_J^{-2}\le4\beta^{-2}$; $\beta_{j-1}^{-1/2}\le\sqrt2\beta^{-1/2}L^{-(j-1)(d-2)/2}$; $c'=\min(\cdot,\delta_G/(2L^2))$; the Tannery dominations use $|\gamma^{\pm1}|\le2$.
  - $\rho_0^C=\min(\rho_0,2\gamma_0)$ is right.
- **Truth and support.**
  - I-F1: a new rate $c_\xi/\beta$ and $\nu$-continuity; the document flags both honestly.
  - I-F2/I-F3: supported by P9 (2.8)–(2.20), (4.8)–(4.14), with D-01 and D-06.
  - I-G: G-5 is stated for the unit-lattice one-shot operators; the iterated-equals-one-shot identification (Woodbury, $b_j^{-1}=\sum\alpha_i^{-1}L^{-d(j-i-1)}$) is verified by me. The recursion $A_{i+1}^{-1}=\alpha_i^{-1}+QA_i^{-1}Q^\top$ and $b_j=L^{j(d-2)}a_j$ both check.
  - Row-sum-one of $P_j$ at $\mu=0$ is right. Positivity of $P_j$ is not available (the matrix $M_j$ is not an M-matrix, because $Q^\top Q$ has positive off-diagonal entries), so (G5) genuinely needs G-5(a).
- **$\nu$-continuity.** It is a new claim, not supported by P9, and the document does not hide that.

### 4. Derivation of Root-C from the interfaces (§3)

- **Transverse leading term.** P9 (4.14): $C_{k,tr}=m_k\sum_{j=0}^{k-1}\beta_j^{-1}a_j^2G_jQ_j^*C^{(j)}_{tr}Q_jG_jm_k$ (modulo D-01). Since $\beta_j^{-1}=L^{-j(d-2)}(\beta\gamma_j)^{-1}$, the coefficient is right given (4.17); see D-04.
- **Index shift.** $G^{(j)}=H_{j-1}C^{(j-1)}H_{j-1}^*$ paired with $\beta_{j-1}^{-1}$ (2.11), (2.13), reindexed $i=j-1$, gives (4.14) directly. The "$k$ versus $k+1$" remark is correct.
- **$a_0=\infty$.** D-11.
- **Lemma 1 summation.** P9 (2.19) hypotheses and the document's computation agree: $\sum_{j\ge i}L^{-j\rho_0}=L^{-i\rho_0}/(1-L^{-\rho_0})$, then Lemma 1.3 with $\sigma=d-2+\rho_0$. P9 uses $|\cdot|_1$, which is stronger than the sup norm.
- **$\nu\downarrow0$.** The dominated convergence (Tannery) is correct given (F1)–(F3).
  - The $\mathbf 1_{[j<J(\nu)]}\to1$ argument is right.
  - $G_{tr,0}(z):=m_0^2S_\infty(z,0)+r_{tr}(0;z,0)$ is well defined.
  - The limit bound $|G_{lg,0}|\le c(1+|z|)^{-(d-2+\rho_0)}$ follows since $e^{-c'\sqrt\nu|z|}\to1$.
- **Identification of $G$ (Step D).** I verified (3.1): $AH=Q^\top\Delta$. I verified (3.2): $A_0P_J=Q_{(J)}^\top A_J$. I verified $A_0P_JA_J^{-1}P_J^\top=Q_{(J)}^\top P_J^\top$. I verified $(Q_{(J)}^\top P_J^\top)(x,y)=L^{-Jd}P_J(y,u_J(x))$. The remainder is $O(L^{-Jd})$ uniformly (given G5). The passage $\ell\to\infty$ then $\mu\downarrow0$ is legitimate (finite stencil, continuity (G3)). The maximum-principle argument is correct. $G\to0$ cofinitely follows from the decay bound with $d\ge3$.
- **The $O(\beta^{-2})$ claim in (4.18).** D-07: unsupported strengthening, not needed.
- **Torus family.** D-02.

### 5. §5 (what no source proves)

Items 1, 2, 3, 4 and 11 are accurately described. Item 5: see D-07 (P9 does state the rate, without proof). Item 9: see D-06. Item 10 ($\lambda<\infty\to\lambda=\infty$): at $\lambda=\infty$, $H_j=a_jG_jQ_j^*(I-h\otimes h)$ follows from (4.12) with $\lambda_j^{-1}=0$, because the second term becomes $a_jG_jG_j^{-1}G_jQ_j^*(h\otimes h)$. The longitudinal main term is therefore exactly zero, as claimed. The confidences quoted look reasonable. The 75% for the continuity of the remainder looks, if anything, optimistic.

### 6. Lean estimate

D-13. Dependency discipline (abstract `RootFClauses` and C-1\* record, nothing imports a root) is consistent with AGENTS.md rules 3–4 and 8.

## Items I checked and found correct (no finding)

- $\kappa_*=2\log(8d^2)$ and the polymer sums.
- Root-F's torus-independence clause is exactly what Lemma 4.2 uses, including the strict inequality $4|y_\mu|<\min(\ell,\ell')$ and the use of $g=\zeta e_k\mathbf 1_z$.
- Quantifier order of Root-C versus Theorem 4.1 and Theorem 3.1: $q$, $c$, $c'$, $\rho_0$, $\rho_1$, $\beta_0$ depend on $(d,N)$ only, with $q=M_FL_F$ from Root-F at $c_9=1$, $\kappa=\kappa_*$.
- The Lean lemma names cited exist: `norm_fderiv_line_le`, `norm_gammaSeq_le`, `exists_inv_betaSeq_asymptotics`, `laplacian_inv_eq_multiscale`.
