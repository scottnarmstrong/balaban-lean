# P8: Correlation functions from effective actions (Balaban–O'Carroll, Gross–Neveu illustration)

## 0. Identification

T. Balaban, M. O'Carroll, "A simple method for correlation functions via the effective actions in the renormalization group framework", Ann. Physics 260 (1997) 1–8 (received 29 Nov 1996). Bundle key P8. 8 PDF pages (journal pp. 1–8; PDF page n = journal page n; p. 8 is only references 3–15).

**IMPORTANT: this paper is not about O(N) spin models.** Its concrete model is the two-dimensional continuum massive Gross–Neveu model (N-flavour Euclidean fermions with quartic interaction), with a sharp-ish momentum cutoff $\Lambda$ and Grassmann fields. The "N" is a fermion flavour number, not a spin-vector dimension. The O(N) lattice series (P0–P7) and the O(N) correlation paper P9 are mentioned only through ref. [8] ("Correlation functions for the classical N-vector model at low temperatures, submitted") which is presumably P9 (UNCERTAIN: the bibliography entry gives only that title and "submitted for publication"; the identification with P9 is by title).

What the paper does: it presents a short, essentially algebraic method for getting two-point (and in principle all) correlation functions directly from the final effective action of an RG sequence, by (i) adding a source $\bar J,J$, (ii) using the Gaussian decomposition/composition and translation formulas to move the source through the RG steps in one go, so that the generating functional equals an explicit exponential of a quadratic form in the source times an integral of the *last* effective action evaluated at a *shifted field* $\tilde\psi + R\,J$; (iii) reading the two-point function off as $P - R\,D_2W_2(0)\,R$, where $W$ is the effective action of that shifted integral. Properties of the propagators $P,R$ give short-distance behaviour and exponential long-distance decay. It takes from earlier work: the inductive description of effective actions of the Gross–Neveu model (ref. [11] = Gawedzki–Kupiainen, CMP 102 (1985) 1–30) and the exact formula for correlations in terms of effective actions from ref. [10] (O'Carroll, J. Stat. Phys. 73 (1993) 943–957) / [9] (Pereira–O'Carroll). It supplies to the series only the method (cited as the template in P9, UNCERTAIN: not verified here).

## 1. Setting and notation

- Fields: Grassmann fields $\psi(x)=\psi^i_\alpha(x)$, $\bar\psi(x)=\bar\psi^i_\alpha(x)$, flavour $i=1..N$, spinor index $\alpha$ of 2×2 Dirac matrices $\gamma^\mu$ with $\{\gamma^\mu,\gamma^\nu\}=-2\delta^{\mu\nu}$ (p. 2; sign convention as printed). $\partial\!\!\!/=\partial_\mu\gamma^\mu$. $\tilde\psi$ denotes a generic Grassmann variable (spin and flavour indices suppressed). Space dimension 2, continuum $\mathbb R^2$ (finite volume and discrete momentum cutoffs of [11] are "in effect" but suppressed, p. 2).
- Bare action with UV momentum cutoff $\Lambda$: $S^\Lambda=S^{o\Lambda}+S^{I\Lambda}$ (p. 2) with
 $S^{o\Lambda}=\int dx\,\bar\psi\, i\partial\!\!\!/_\Lambda\,\psi$ (1),
 $S^{I\Lambda}=z^\Lambda\!\int dx\,\bar\psi i\partial\!\!\!/\psi+m^\Lambda\!\int dx\,\bar\psi\psi-g^\Lambda\!\int dx\,(\bar\psi\psi)^2$ (2).
- Cutoff propagator: $(i\partial\!\!\!/_\Lambda)(x_1-x_2)=(2\pi)^{-2}\int dp\, e^{ip(x_1-x_2)}\frac{\not p}{p^2}e^{-p^2/\Lambda^2}$ (3) (the inverse of $i\partial\!\!\!/_\Lambda$ in the sense of the Gaussian covariance; the text writes $G^\Lambda=(i\partial\!\!\!/_\Lambda)^{-1}$, p. 2, so (3) is $G^\Lambda$ as printed; UNCERTAIN: the notation in (1) vs (3) is loose, the formula (3) is the covariance).
- Partition function $Z^\Lambda=\int e^{-S^{I\Lambda}(\tilde\psi)}d\mu_{G^\Lambda}(\tilde\psi)$ (4), $d\mu_{G^\Lambda}$ the fermionic Gaussian "measure" of covariance $G^\Lambda$ in the sense of Berezin [14]. Correlations: $\langle\prod_{j=1}^n\tilde\psi(x_j)\rangle_\Lambda=\int\prod\tilde\psi(x_j)e^{-S^{I\Lambda}}d\mu_{G^\Lambda}/Z^\Lambda$ (5).
- Gaussian decomposition (p. 3, (6)): for $C=C_1+C_2$, $\tilde\psi=\tilde\psi_1+\tilde\psi_2$: $\int F(\tilde\psi)d\mu_C=\int F(\tilde\psi_1+\tilde\psi_2)d\mu_{C_1}(\tilde\psi_1)d\mu_{C_2}(\tilde\psi_2)$. Translation formula (7): with $(\bar J,\tilde\psi)\equiv(\bar J,\psi)+(\bar\psi,J)$, $\int F(\tilde\psi)e^{(J,\bar\psi)}\ldots$ as printed: $\int F(\tilde\psi)e^{(\tilde J,\tilde\psi)}d\mu_C(\tilde\psi)=e^{(\tilde J,C\tilde J)}\int F(\tilde\psi+C\tilde J)\,d\mu_C(\tilde\psi)$. Here $J,\bar J$ are anticommuting Grassmann sources, anticommuting with all other Grassmann variables; $(\cdot,\cdot)$ a bilinear form. (Printed formula writes $(\bar J,CJ)$ in the exponent; whether it is $(\tilde J,C\tilde J)$ or $(\bar J,CJ)$ cannot be settled from the reduced notation; the text on p. 5 uses $e^{(J,\Gamma J)}$.) Taking $F=1$, dividing by $\int d\mu_C$ and expanding in $\tilde J$ gives the fermionic Wick rule.
- Scale sequence (8): $\Lambda\equiv L^{n_0},L^{-1}\Lambda,\dots,L,\,1=\mu$, $L>1$ of order one. Covariance splitting (9): $G^\Lambda=G^{L^{-1}\Lambda}+\Gamma^\Lambda_{L^{-1}\Lambda}$; fields $\tilde\psi=\tilde\psi'+\tilde\zeta$ (10). $\Gamma$ has exponential decay (p. 3).
- Effective interaction (12): $e^{-S^{I\Lambda}_{L^{-1}\Lambda}(\tilde\psi')}=\int e^{-S^{I\Lambda}(\tilde\psi'+\zeta)}d\mu_{\Gamma^\Lambda_{L^{-1}\Lambda}}(\zeta)$, so $Z^\Lambda=\int e^{-S^{I\Lambda}_{L^{-1}\Lambda}}d\mu_{G^{L^{-1}\Lambda}}$ (11); iterating to scale 1: $Z^\Lambda=\int e^{-S^{I\Lambda}_1}d\mu_{G^1}$ (13). Composition law (14): for $\tilde{\tilde\Lambda}<\tilde\Lambda<\Lambda$, $e^{-S^{I\Lambda}_{\tilde{\tilde\Lambda}}(\tilde\psi)}=\int e^{-S^{I\Lambda}_{\tilde\Lambda}(\tilde\psi+\eta)}d\mu_{\Gamma^{\tilde\Lambda}_{\tilde{\tilde\Lambda}}}(\eta)=\int e^{-S^{I\Lambda}(\tilde\psi+\tilde\zeta+\eta)}d\mu_{\Gamma^\Lambda_{\tilde\Lambda}}d\mu_{\Gamma^{\tilde\Lambda}_{\tilde{\tilde\Lambda}}}$.
- Sequence of actions (15) $\{S^{I\Lambda}_{\tilde\Lambda}\}$, $\tilde\Lambda=L^{-1}\Lambda,\dots,L,1$. Scaled actions $H^{I\Lambda}_{\tilde\Lambda}$ (16): $S^{I\Lambda}_{\tilde\Lambda}(\tilde\psi)=H^{I\Lambda}_{\tilde\Lambda}\big((\mu/\tilde\Lambda)^{1/2}\tilde\psi((\mu/\tilde\Lambda)\cdot)\big)$. Scaled recursion (17), with $n\leftrightarrow$ scale $L^n$ and a fixed fluctuation covariance $\Gamma^1_{L^{-1}}$: $e^{-H^I_{n-1}(\tilde\psi)}=\int e^{-H^I_n(L^{-1/2}\tilde\psi(L^{-1}\cdot)+\tilde\eta(\cdot))}d\mu_{\Gamma^1_{L^{-1}}}(\tilde\eta)$.
- Output of [11] at scale $\tilde\Lambda\ge\mu=1$ (p. 5, (18)): $S^{I\Lambda}_{\tilde\Lambda}=S^{\Lambda,EFF}_{\tilde\Lambda}+\sum_{\mathbf m,\mathbf r}\int dx\,S^{\Lambda\mathbf{mr}}_{\tilde\Lambda}(x)\prod_{i=1}^q(\partial\tilde\psi(x_i))^{r_i}(\tilde\psi(x_i))^{m_i-r_i}$, with local part $S^{\Lambda,EFF}_{\tilde\Lambda}(\tilde\psi)=\int dx(\bar\psi i\partial\!\!\!/\psi+z^\Lambda_{\tilde\Lambda}\bar\psi i\partial\!\!\!/\psi+m^\Lambda_{\tilde\Lambda}\bar\psi\psi-g^\Lambda_{\tilde\Lambda}(\bar\psi\psi)^2)$. Here $\mathbf m=(m_i)_{i=1}^q$, $0<m_i<4$, $x=(x_1,\dots,x_m)$, $m=\sum m_i$ even, $\mathbf r=(r_i)$, $r_i\in\{0,1\}$, $m=2\Rightarrow r\equiv\sum r_i=2$; $m=4\Rightarrow r\ge1$. Running constants $g,z,m$ small; kernels have continuum ($\Lambda\to\infty$) and infinite-volume limits. Scaled kernels $S^{\Lambda\mathbf{mr}}_{\tilde\Lambda}(x)=(\tilde\Lambda/\mu)^{2q-(m/2)-r}H^{\Lambda\mathbf{mr}}_{\tilde\Lambda}((\tilde\Lambda/\mu)x)$ with tree-decay bound $\int dx_2\cdots dx_m|H^{\Lambda\mathbf{mr}}_{\tilde\Lambda}(x)|e^{\mu\mathcal L(x)}\le c(g^\Lambda_{\tilde\Lambda})^2$ ($m<8$), $\le c^m(g^\Lambda_{\tilde\Lambda})^{3+\epsilon(m-8)}$ ($m\ge8$); $\mathcal L(x)$ = length of the shortest tree on the points $x$ (and possibly other points). (Exponent $2q-m/2-r$ and the form of the $m\ge 8$ bound read from the page image; the exponent "$\epsilon(m-8)$" is UNCERTAIN as to whether it is $\epsilon(m-8)$ with $\epsilon$ a fixed small number; the OCR agrees with the image.)

Glossary

| symbol | meaning | where |
|---|---|---|
| $\Lambda$, $\tilde\Lambda$, $L$, $\mu=1$ | UV cutoff, intermediate scale, scale factor, final scale | (8), p. 3 |
| $G^\Lambda$, $\Gamma^\Lambda_{L^{-1}\Lambda}$ | Gaussian covariance, fluctuation covariance | (9), p. 3 |
| $S^{I\Lambda}_{\tilde\Lambda}$ | effective interaction at scale $\tilde\Lambda$ | (12), (14) |
| $H^{I\Lambda}_{\tilde\Lambda}$ | scaled effective action | (16) |
| $Z^\Lambda(\tilde J)$ | generating functional | (19), p. 5 |
| $m_1^\Lambda$ | small fixed mass inserted at scale 1 | (21), p. 6 |
| $G_{m_1}=(i\partial\!\!\!/_1+m_1)^{-1}$ | massive covariance | (22) |
| $P^\Lambda,R^\Lambda$ | source propagators | (25),(26), (31),(32) |
| $W^\Lambda$ | effective action of the shifted last-scale integral | before (27) |
| $g,z,m$ | running couplings | (18) |

## 2. Main results

There is no numbered theorem. The "results" are the following (all derived in the text, mostly by algebra from cited inputs).

(R1) Generating-function identity (p. 5, (19)–(20)), with $Z^\Lambda(\tilde J)=\int e^{(\tilde J,\tilde\psi)}e^{-S^{I\Lambda}(\tilde\psi)}d\mu_{G^\Lambda}(\tilde\psi)$:
$$Z^\Lambda(\tilde J)=\int e^{(\tilde J,\tilde\chi+\eta)}e^{-S^{I\Lambda}(\tilde\chi+\eta)}d\mu_{\Gamma^\Lambda_1}(\eta)\,d\mu_{G^1}(\chi)=e^{(J,\Gamma^\Lambda_1J)}\!\int e^{(\tilde J,\tilde\psi)}e^{-S^{I\Lambda}_1(\tilde\psi+\Gamma^\Lambda_1J)}d\mu_{G^1}(\tilde\psi)=e^{(J,G^\Lambda J)}\!\int e^{-S^{I\Lambda}_1(\tilde\psi+G^\Lambda J)}d\mu_{G^1}(\tilde\psi).$$
(The page prints the first line with $\tilde\psi+\tilde\eta$, and the last step uses a second translation by $G^1J$ so that $\Gamma^\Lambda_1+G^1=G^\Lambda$; the $e^{(\tilde J,\tilde\psi)}$ factor disappears at the last step. Here the text says "$\tilde\chi\to\tilde\psi$" for the relabelling.) Truncated correlations are derivatives of $\ln Z^\Lambda(\tilde J)$ in $\tilde J$.

(R2) Massive version (pp. 5–6, (21)–(26)). Write $S^{I\Lambda}_1=m_1^\Lambda\bar\psi\psi+S'^{\Lambda}_1$ (21) with $m^\Lambda_1>0$ small fixed; absorb $e^{-m_1\bar\psi\psi}$ into the measure: $G_{m_1^\Lambda}=(i\partial\!\!\!/_1+m_1^\Lambda)^{-1}$ (22). Then
$$Z^\Lambda(\tilde J)=c\,e^{(J,G^\Lambda J)}e^{-m_1^\Lambda(G^\Lambda J,G^\Lambda J)}\int e^{-(\bar\psi,m_1G^\Lambda J)-(m_1G^\Lambda\bar J,\psi)}e^{-S_1'^\Lambda(\tilde\psi+G^\Lambda J)}d\mu_{G_{m_1}}(\tilde\psi)\quad(23),$$
$c=\det G_{m_1}/\det G^1$ independent of $\tilde J$. A further translation gives
$$Z^\Lambda(\tilde J)=c\,e^{(J,P^\Lambda J)}\int e^{-S_1'^\Lambda(\tilde\psi+R^\Lambda\tilde J)}d\mu_{G_{m_1}}(\tilde\psi)\quad(24),$$
$$P^\Lambda=G^\Lambda-m_1G^{\Lambda+}G^\Lambda+m_1^2G^{\Lambda+}G_{m_1}G^\Lambda\ (25),\qquad R^\Lambda=G^\Lambda-m_1G_{m_1}G^\Lambda\ (26).$$
($G^{\Lambda+}$ is not defined in the text; presumably the adjoint/transpose-type partner of $G^\Lambda$ appearing because $\bar J$ and $J$ enter with $G$ on different sides. UNCERTAIN.) The integral in (24) is "just like" the massive fluctuation integrals of [11]; with $m_1$ small and $g_1^\Lambda$ small it equals $\exp(-W^\Lambda(R^\Lambda\tilde J))$ (p. 6).

(R3) Two-point function (p. 6, (27)): $\langle\psi(x)\bar\psi(y)\rangle_\Lambda=(P^\Lambda-R^\Lambda D_2W^\Lambda_2(0)R^\Lambda)(x,y)$, where only the second derivative at zero field of the quadratic part of $W^\Lambda$ contributes. By [11], $W_2^\Lambda(\tilde\psi)=z'(\bar\psi,i\partial\!\!\!/\psi)+m'(\bar\psi,\psi)+W^\Lambda_{2S}(\tilde\psi)$ (28), with $W_{2S}^\Lambda(\tilde\psi)=\int\partial\bar\psi(x_1)W^\Lambda_{2S}(x)\partial\psi(x_2)dx_2$ and $\int|W^\Lambda_{2S}(x)|e^{(m_1^\Lambda-\epsilon(g_1^\Lambda))|x_1-x_2|}dx_2<\infty$, $\epsilon(g^\Lambda_1)\to0$ as $g^\Lambda_1\to0$. (Printed: "$\int|W_{2s}(x)|e^{(m_1^\Lambda-\epsilon(g_1^\Lambda))|x_1-x_2|}|x_1-x_2|dx_2<\infty$" is not what I read; image shows the exponential and then $|x_1-x_2|\,dx_2$. UNCERTAIN whether the factor $|x_1-x_2|$ belongs to the integrand; irrelevant for the algebra.)

(R4) Explicit propagators and consequences (p. 7, (29)–(30)), cutoffs removed ($\Lambda=\infty$), $\not p\not p=-p^2$, with $\widetilde{(\cdot)}$ the Fourier transform:
$(\widetilde{(i\partial\!\!\!/_1)^{-1}})(p)=\frac{\not p}{p^2}e^{-p^2}$, $\ \widetilde{(i\partial\!\!\!/_1)}(p)=-\not p e^{p^2}$, $\ \widetilde{(i\partial\!\!\!/_1+m_1)^{-1}}(p)=\frac{\not pe^{p^2}+m_1}{p^2e^{2p^2}+m_1^2}$, $\ \widetilde{(i\partial\!\!\!/_1+m_1)}=-\not pe^{p^2}+m_1$.
$$\tilde P(p)=\Big[\tfrac{\not p}{p^2}-m_1\tfrac{\not p\not p}{p^4}+m_1^2\tfrac{\not p}{p^2}\Big(\tfrac{\not pe^{p^2}+m_1}{p^2e^{2p^2}+m_1^2}\Big)\tfrac{\not p}{p^2}\Big]=(p^2e^{2p^2}+m_1^2)^{-1}\big[\not p(e^{2p^2}+m_1^2p^{-2}(1-e^{p^2}))+m_1e^{2p^2}\big]\ (29),$$
$$\tilde R(p)=\tfrac{\not p}{p^2}-m_1\Big(\tfrac{\not pe^{p^2}+m_1}{p^2e^{2p^2}+m_1^2}\Big)\tfrac{\not p}{p^2}=(p^2e^{2p^2}+m_1^2)^{-1}\big[\not pe^{2p^2}+m_1e^{p^2}\big]\ (30).$$
(Closed forms transcribed from the image; I did not re-derive them. UNCERTAIN on the exact placement of $e^{2p^2}$ vs $e^{p^2}$ in the middle term of (29): the Fourier symbol of $G^\Lambda$ contains $e^{-p^2}$ at $\Lambda=1$, so mixed products produce $e^{p^2}$ factors; spot-check recommended.) Consequences stated: $\tilde P,\tilde R$ analytic for small $p$, hence $P,R$ decay exponentially with rate $\simeq m_1$; $W_{2S}(x)$ likewise; for large $|p|$, $\tilde P,\tilde R\sim\not p/p^2$ (free short-distance behaviour). So $\langle\psi\bar\psi\rangle$ has long-range exponential falloff with rate $\simeq m_1$ and the free singularity at short distance.

(R5) Alternative representation (p. 7, (31)–(32)), obtained from the second line of (20) and the same steps:
$P^\Lambda=\Gamma_1^\Lambda-m_1\Gamma^\Lambda_1\Gamma_1^{\Lambda+}+(1-m_1\Gamma^\Lambda_1)G_{m_1}(1-m_1\Gamma_1^{\Lambda})$ with $\Gamma_1^{\Lambda+}$ in the third place as printed ($(1-m_1^\Lambda\Gamma_1^{\Lambda+})$ hmm: printed $P^\Lambda=\Gamma^\Lambda_1-m^\Lambda_1\Gamma^\Lambda_1\Gamma^{\Lambda+}_1+(1-m^\Lambda_1\Gamma^\Lambda_1{}^+)G_{m_1^\Lambda}(1-m^\Lambda_1\Gamma_1^\Lambda)$; UNCERTAIN on where the "+" sits), and $R^\Lambda=\Gamma^\Lambda_1+G_{m_1^\Lambda}(1-m_1^\Lambda\Gamma_1^\Lambda)$. Advantage: short and long distance properties are manifest because $\Gamma_1^\Lambda$ is the short-range (momenta $\ge1$) part and $G_{m_1}$ the massive long-range part.

(R6) Remark (p. 7): the analysis works for $m_1^\Lambda=0$ as well, but then the massless covariance is not displayed, so the volume is taken finite (of order 1, to keep the renormalized coupling bounded independently of the volume). For mass generation with a fixed UV cutoff see [13].

## 3. Proof architecture

The "proof" is a chain of algebraic manipulations on Gaussian integrals followed by quotation of results.

1. (pp. 1–2) Recall the RG framework of [11]: cutoff action, covariance splitting, effective actions.
2. (p. 3–4) Two formulas: decomposition (6) and translation (7). Both hold for Grassmann Gaussian "measures" with the same algebra as the commutative case ("easily derived", [13] cited; not proved). Composition (14) follows from (6).
3. (p. 4) Inductive scheme: scaled actions $H$ with a fixed covariance $\Gamma^1_{L^{-1}}$ (17). At each step the local mass, quartic and massless kinetic terms are split off and their coefficient flow is controlled; this is entirely [11].
4. (p. 5) Statement (without proof) of the structure of $S^{I\Lambda}_{\tilde\Lambda}$ for $\tilde\Lambda\ge\mu=1$ ("Theorem of [11]"), eq. (18), with the tree-decay bound.
5. (p. 5) Key step: instead of carrying the source through each RG step, decompose $G^\Lambda=G^1+\Gamma^\Lambda_1$ once, absorb the high-momentum fluctuation integral over $\eta$ using the definition of $S^{I\Lambda}_1$ (the identity (14) in the form $e^{-S_1^{I\Lambda}(\psi)}=\int e^{-S^{I\Lambda}(\psi+\eta)}d\mu_{\Gamma_1^\Lambda}$), and use translations to eliminate the source from the exponent, leaving it only in the shift of the field argument of $S^{I\Lambda}_1$ and a quadratic prefactor. This is the "exact formula" for the correlation function in terms of the effective action.
6. (pp. 5–6) Section 9 of [11] is used to produce a massive covariance: peel off $m_1\bar\psi\psi$ from $S_1$, absorb into the measure, translate again to get (24). Then [11] is applied to the integral in (24), whose "external field" $R\tilde J$ is of the type already treated; with $W$ its effective action, and $D_2W_2(0)$ the only contribution to the two-point function (the term of order $\tilde J^2$ in $-\ln$ of the integral; differentiating (24) twice at $\tilde J=0$ gives (27)).
7. (p. 7) Explicit Fourier calculation of $P,R$; analyticity and decay.

Genuine difficulty: none in this paper; all analysis is in [11] (flow of couplings, tree-decay bounds on kernels, Section 9 massive-covariance extraction). The only new point is the algebraic observation in step 5–6.

## 4. Ingredients and prerequisites

4a. From bundle papers: none used. (P8 is formally independent of P0–P7; the O(N) analogue is presumably in P9, cited here as [8].)

4b. Outside the bundle (reference list, p. 7–8):
- [11] K. Gawedzki, A. Kupiainen, Commun. Math. Phys. 102 (1985) 1–30 (Gross–Neveu model: effective actions, Theorem and Section 9). Essential: supplies (18), the bound on kernels, the massive-covariance fluctuation integrals and the form (28) of $W_2$.
- [10] M. O'Carroll, J. Stat. Phys. 73 (1993) 943–957 and [9] E. Pereira, M. O'Carroll, J. Stat. Phys. 73 (1993) 695–721: the exact formula for correlation functions in terms of effective actions (infrared asymptotically free models). Essential for the method.
- [13] T. Balaban, M. O'Carroll, R. Schor, Commun. Math. Phys. 122 (1989) 233–247: Gaussian decomposition/translation formulas, block RG on a lattice, mass generation with fixed UV cutoff.
- [14] F. Berezin, "The Method of Second Quantization", Academic Press, 1966 (printed 1996): Grassmann integration.
- [12] D. Iagnolnitzer, J. Magnen, CMP 110 (1987) 51–74; 111 (1987) 81–100; 119 (1988) 567–584: low-energy spectral properties of Gross–Neveu (more detailed results than here).
- [1–8, 15] general RG / constructive references (Glimm–Jaffe; Gawedzki–Kupiainen CMP 92 (1984) 531–553; Feldman–Magnen–Rivasseau–Seneor CMP 103 (1986) 67–103; Rivasseau, Princeton 1991; Brydges–Yau CMP 129 (1990) 351–392; Brydges–Dimock–Hurd CMP 172 (1995) 143–186; Gallavotti–Benfatto; [8] Balaban–O'Carroll, "Correlation functions for the classical N-vector model at low temperatures", submitted; Rivasseau–Kopper–Magnen CMP 169 (1995) 121–180): context only.

4c. Standard mathematics: Berezin integral and Grassmann Gaussian "measures" (Wick rule, decomposition and translation formulas), Fourier transform of translation-invariant covariances, analyticity of the symbol near $p=0$ implying exponential decay of kernels (Paley–Wiener type), Clifford algebra $\{\gamma^\mu,\gamma^\nu\}$.

## 5. Dependency ledger

| result | uses (internal) | uses (bundle) | uses (external) | status |
|---|---|---|---|---|
| Decomposition (6), translation (7) | – | – | [13], [14] | cited, "easily derived" |
| Composition (14) | (6), (9) | – | – | proved (one line) |
| Scaled recursion (16)–(17) | (12), (14) | – | [11] | cited |
| Structure (18) and kernel bounds | (17) | – | [11] Theorem | cited |
| Generating identity (20) | (6), (7), (14) | – | – | proved (algebra) |
| Massive form (23)–(26) | (20), (7), (21)–(22) | – | [11] Sect. 9 | algebra proved; existence of massive splitting cited |
| Correlation formula (27) | (24) | – | [11] (integral = $e^{-W}$) | cited + one derivative |
| Form (28) of $W_2$ | – | – | [11] | cited |
| Fourier formulas (29)–(30) | (25), (26) | – | – | computation (not displayed in full) |
| Decay/short-distance statements | (29), (30), (28) | – | – | sketched (analyticity of symbol, no quantitative proof) |
| Alternative (31)–(32) | second line of (20) | – | – | stated, "proceeding as before" |

## 6. Constants and parameters

- $L>1$ of order one, $\Lambda=L^{n_0}$, $\mu=1$; the scale-1 effective action $S_1^{I\Lambda}$ is the object; $g^\Lambda_1$ small (order of choice: $g_1^\Lambda$ small first, as provided by [11] via the bare $g^\Lambda$), then $m_1^\Lambda>0$ "fixed small constant" (the decay rate $\simeq m_1$ requires $m_1$ small relative to $g$-dependent quantities such that $\epsilon(g_1)<m_1$; the paper does not state this relation precisely: UNCERTAIN, printed rate is $m_1^\Lambda-\epsilon(g_1^\Lambda)$).
- Kernel bound constants $c$, $\epsilon$ in (18) and $\mathcal L(x)$ from [11].
- Cutoffs removed: $\Lambda\to\infty$ with running constants converging, volume infinite, using [11]. For $m_1=0$ the volume must be finite, of order 1.

## 7. Weak spots and open points

- The statement is a sketch; no theorem. Uniformity in $\Lambda$ and volume of the bounds is delegated to [11].
- Definition of $G^{\Lambda+}$, $\Gamma_1^{\Lambda+}$ not given; the placement of "+" in (25), (31) is unclear (UNCERTAIN). Likely a transposition/adjoint accounting for the asymmetry between $J$ and $\bar J$.
- The precise form of the translation formula (7) (which source pairing appears in the prefactor) is not visible from the reduced notation, and $e^{(J,\cdot J)}$ is used afterward.
- The derivation of (23) (extraction of $m_1$ and the exponent bookkeeping) and the intermediate steps to (24)–(26) are not shown; (25)–(26) cannot be checked without redoing the algebra (not done).
- Formulas (29)–(30): the closed forms are not derived; sign conventions ($\not p\not p=-p^2$ together with $\{\gamma,\gamma\}=-2\delta$) are consistent as printed but I did not re-verify.
- Claim "exponential decay with rate $\simeq m_1$": no argument that $D_2W_2(0)$ is analytic in $p$ near zero beyond the $W_{2S}$ weighted-integrability statement with rate $m_1-\epsilon$; the passage from the $x$-space bound to analyticity of $\tilde W_{2S}$ in a strip, and the combination into (27) (products of operators, not just their sum), is only asserted.
- Only the two-point function is treated. Higher-point functions follow in principle by further derivatives of (24), but this is not carried out.
- The scale index on $m^\Lambda_1$ vs $m_1^\Lambda>0$: the mass is a *choice* made at scale 1 (inserted and compensated: $-m_1\bar\psi\psi$ is moved between measure and action), so (22)–(24) are an identity independent of $m_1$; the mass only serves to make the subsequent fluctuation integral fit the massive theory of [11]. The paper says "the mass term with $m_1^\Lambda>0$ which is taken to be a fixed small constant"; whether $m_1^\Lambda$ is the running mass of $S_1$ or an inserted one is mildly ambiguous (UNCERTAIN, I read it as inserted/redefined).

## 8. Preliminary formalization notes

- Content of the method is algebraic: Gaussian decomposition, translation (shift of integration variable with a source), composition of fluctuation covariances, and the resulting formula $\langle\psi\bar\psi\rangle=P-R\,D_2W_2(0)R$. For a formalization of the O(N) theory (P9) the analogous step would be a purely formal identity relating $\langle\cdot\rangle$ to the last effective action; this could be an early, self-contained target *if* it is stated for abstract Gaussian (bosonic) measures: e.g. for finite-dimensional real Gaussian measures with covariance $C=C_1+C_2$, the identities $\int F\,d\mu_C=\int\!\!\int F(\psi_1+\psi_2)d\mu_{C_1}d\mu_{C_2}$ and $\int F(\psi)e^{(J,\psi)}d\mu_C=e^{\frac12(J,CJ)}\int F(\psi+CJ)d\mu_C$ (Cameron–Martin / shift). Mathlib has Gaussian measures (`ProbabilityTheory.gaussianReal`, multivariate Gaussian in recent versions) and convolution of measures, so (6)/(7) in the real finite-dimensional case should be formalizable (guess: moderate effort). The Grassmann version of this paper has no Mathlib support (Berezin integration absent); not relevant for the O(N) project.
- Caution: this paper's hypotheses on the RG sequence are only (a) the splitting $G^\Lambda=G^1+\Gamma_1^\Lambda$ with decomposition/composition property, (b) the existence of the effective action $S_1$ as an integral of $S^\Lambda$ against $\Gamma_1^\Lambda$ (an exactly Gaussian step), (c) the ability to treat $\int e^{-S_1'(\psi+R\tilde J)}d\mu_{G_{m_1}}$ by the same inductive estimates (i.e. control of the effective action in a *shifted background field* $R\tilde J$ and its second derivative at zero), and (d) analytic/decay properties of $P,R$. For the spin-model case, (c) is the nontrivial input: it requires the RG machinery to handle an external field. Which parts of P1–P7 supply it, and its use in P9, must be checked there; this paper does not answer that.
- Hardest parts for a formal development are not in this paper: they are the cited [11] estimates. The Fourier calculation (29)–(30) is routine but needs distribution-valued symbol calculus; skip.
- As a self-contained early target, this paper alone is of limited value: the algebra is short, and the substantive hypotheses are the cited analytic results.
