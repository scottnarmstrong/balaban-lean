# Mergers in Balaban's large-field counting

11 October 2026. Page numbers below are **journal pages**. Here P5 is *CMP* **196** (1998) 485–521, P6 is *CMP* **198** (1998) 1–45, P7 is *CMP* **198** (1998) 493–534; E8 is *CMP* **119** (1988) 243–285, E9 is *CMP* **122** (1989) 175–202, and E10 is *CMP* **122** (1989) 355–392. I read P5 §§1–2, P6 §3, P7 §§1–3 from their typeset PDFs, E9 p. 177 and E10 pp. 355–391 from page images (using its OCR only to navigate), and checked the existing architecture and review. The source PDFs were not changed. E10 p. 392 is outside this audit.

## Verdict

**E10 does handle mergers, but its mechanism does not prove P6 Proposition 3.2(ii).** E10 chooses a *geometric* stopping time and proves that the available gain pays all costs until that time, including costs caused by mergers. P6 instead calls the last time at which a *budget inequality* holds $K$, then asserts that budget exhaustion implies a geometrically quiet window. Its printed definitions allow two almost exhausted components to merge and thereby produce a fresh pooled budget without producing a fresh quiet window. Proposition 3.2(ii) is false on those histories. The P6 and P7 text contains no additional exclusion of them.

I recommend repair **(a), with an important change**: charge the analytic window per *primitive gain atom* carried by a component, rather than per connected component present at the beginning of the window. Keep that atom count through new gains and hulls; reset it only when the component is removed or is replaced by one kept $R$ output. The counting induction then closes under the explicit geometric cover and analytic estimates stated below. Those estimates require a real reworking of P7. Repair (b) leaves P7 intact and is cheaper analytically, but its proposed doubling/pooled-reserve argument has not been proved for the O(N) histories. Neither option is a completed proof of the full RG theorem today.

## 1. What the papers actually do

### The gauge-theory route, E8–E10

E8 has a decomposition into admissible large-field regions and factorized integral operators ((2.18) p. 257 and (2.19)–(2.22) p. 258); on p. 258 it says the operators for disjoint regions commute. It does not define the quantitative component counter $K$ or prove a merger estimate for it. E9 p. 177 selects a component for $R$ by **two geometric conditions**: “it is contained in a cube of the size $100MR_k$”; and during the preceding $N$ steps “no new large field regions were created inside this component, and the previous regions contained in it satisfy the condition (i) on the corresponding scales.” E9 immediately says that those past regions are rectangular parallelepipeds. Its condition (ii) allows several past components when **each** is small; a merger delays eligibility only if the current union fails (i) or a past component fails (i). It does not equate a pooled gain to geometric eligibility.

The quantitative merger mechanism is in E10, not E8 or E9. E10 (1.71)–(1.72), pp. 378–379, define the component operator $T'_k(X)$ and assemble the $R$ operation; (1.73)–(1.75), p. 380, use positivity to bound it. On pp. 380–383, (1.76) gives the union-of-old-shadows-and-new-regions construction, and (1.79) expresses the operator bound as a product of gains and per-step losses. On p. 384 Balaban writes the component factor as $\exp[-\kappa_j(Z)-2p_0(g_{j(Z)})]$ and defines $K$ as “the smallest positive integer” for which $S^K(Z)$ meets E9's two geometric conditions. His assertion is

$$\kappa_j(Z)\ge\sum_{n=j+1}^{j+K} O(1)M^dR_n^{d+1}d'_n(S^{n-j}Z).\tag{E10 1.80, p. 384}$$

The proof first bounds the cost of shrinking one domain by its tree-like linear size $d'_j(Z)$, (1.81), p. 385. At a merger, (1.84)–(1.85), p. 386, write the new component as the union of old component shadows and new large-field pieces, retaining their gain factors. Balaban forms a connected graph of these pieces, removes an endpoint of a spanning tree, and inducts on the number of pieces. For two resulting domains $X,Y$, (1.87), pp. 386–387, gives, with the paper's $O(1)$ constants,

$$\kappa_{j+1}(Z)\ge\kappa_{j+1}(X)+\kappa_{j+1}(Y)
 +2(1+\beta_0)^{-1}p_0(g_{j+1})-O(1)2dM^dR_{j+1}^{d+1}.\tag{E10 1.87}$$

If their geometric stopping times are $K_1\le K_2$, the small $X$ is swallowed after fewer than ten further shadows of $Y$; the whole component stops by $K_2+n_1+R_{j+1}$. E10 then obtains

$$\begin{aligned}
\text{cost through the new geometric stopping time}
&\le\kappa_{j+1}(X)+\kappa_{j+1}(Y)+O(1)2(100M)^dR_{j+1}^{d+2}\\
&\le\kappa_{j+1}(Z)-2(1+\beta_0)^{-1}p_0(g_{j+1})
       +O(1)3(100M)^dR_{j+1}^{d+2}\\
&\le\kappa_{j+1}(Z).
\end{aligned}\tag{E10 1.88, p. 387}$$

This is the explicit refund for a merger and a restarted geometric waiting period. The step cost depends on $d'_n(S^{n-j}Z)$, not just one-box volume. E10 concludes $\kappa_k(X)\ge0$ for first-class components and hence $|T'_k(X)1|\le\exp[-2(1+\beta_0)^{-1}p_0(g_k)]$, (1.89), p. 387. That gain feeds the polymer estimates (1.90)–(1.100), pp. 388–390, and the final representation (1.104), p. 391. This is a real merger proof **for E10's geometric clock and its gauge-theory gain schedule**. The phrase “smallest positive integer” on p. 384 conflicts harmlessly with the use $K=0$ on p. 387; it does not turn E10's $K$ into P6's budget counter.

### The O(N) route, P5–P7

P5 p. 495, (1.30), requires $C(\mathbb A_k\cap Z)e^{-\kappa_k(Z,\mathbb A_k\cap Z)}\le e^{-\ell p_2(\beta_k)-H_k|Z|}$, where $p_2(\beta)=A_2(\log\beta)^{p_2}$ and $\ell=1,2$. H6, (1.32), p. 496, is $K(Z,\mathbb A_k\cap Z)>0$ before $R$; the same paragraph makes positivity in the preceding steps an admissibility condition. It does **not** prohibit two positive-counter components from joining. P5 cites E10 as the source of “geometric combinatoric arguments” but gives no merger rule.

P6 (3.10)–(3.11), pp. 18–19, make $\kappa$ additive over old components and $C$ multiplicative, subject to the new layer costs. P6 (3.13)–(3.16), pp. 19–20, define the empty-new-field shadow $S$ and its critical diameter $12M[R_{k+n-1}]$. Its actual definition of the counter is (3.19), pp. 20–21: if $G_k:=\kappa_k-\log C-H_k|Z|$, and $c_{k,p}(Z)\ge0$ denotes the displayed logarithmic cost of the $p$th shadow layer, then

$$\kappa_{k,n}(Z,\mathbb A_k\cap Z)
 =G_k(Z)-\sum_{p=1}^n c_{k,p}(Z),\qquad
 K(Z,\mathbb A_k\cap Z)=\max\{n:\kappa_{k,n}>2p_2(\beta_{k+n})\}.\tag{P6 3.19 and text, pp. 20–21}$$

Here $K$ uses $\ell=2$ for H6. P6 Proposition 3.2(ii), p. 21, claims that $K=0$ produces $k_1<k$ for which **all** $Z_j\cap Z$, $k_1\le j\le k$, have diameter below the critical size, the earlier multi-indices “control at least $k-j$ steps,” there are no new large-field regions in the window, and $k-k_1>\log\beta_{k_1}a$, (3.20). P6 refers the proof to E10 pp. 383–387, but E10 proves (1.80), the opposite logical direction: *given a geometric stopping time, gain pays until it*. It never proves *budget exhaustion implies geometric eligibility* for the P6 counter.

P6 p. 22 adds a hull rule for components already below critical size, claiming thereby that all past $Z_j\cap Z$ in Proposition 3.2 are boxes. P7 uses the assertion literally. P7 p. 498 says: “Hence the domains $Z_j$ for $k_1\le j\le k$ are rectangular parallelepipeds with diameters ... smaller than the critical sizes.” P7 then takes $n_1=k-k_1$ satisfying the still stronger (2.31), p. 505, $n_1\log L>\alpha^{-1}\log(\beta_{k_1}a)$. Thus E10's merger tree does **not** appear as a hidden per-piece interpretation of P7's window.

## 2. Proposition 3.2(ii): counterexample and attempted rescue

Write $\lambda_j=\log(\beta_ja)$, $\tau_j=2A_2\lambda_j^{p_2}$, and $\theta=(d-2)\log L$. The running-coupling estimates used in P5–P7 give $\lambda_{j+n}=\lambda_j+n\theta+O(1)$ in the range in question. Fix large $\lambda_t$. Start two congruent, widely separated, single-seed components, follow their empty-new-field shadows, and take $t$ just before the first scale at which each has $K=0$. They have $K=1$ at $t$: (3.19)'s counter starts large since the seed gain has order $\lambda^{2p_0}$, is eventually exhausted by the increasing $\tau$, and the one-step estimate P6 (3.21) precludes skipping directly from positive $K$ to a negative counter. Translation on a sufficiently large torus and the finite-range shadow rule P5 (2.4), (2.9), P6 (3.13)–(3.16), allow their separation to be chosen so that they remain distinct through $t$ and their shadows first touch at $t+1$. Their separate histories are identical up to that point. This geometric placement is the one discrete-realization step that should be formalized from the partition and hull rules; no condition in P5's admissibility paragraph excludes it.

The needed **upper** budget bound follows from $K(Z_i)=1$, not from P6 (3.21). For each small piece, $\kappa_{t,2}(Z_i)\le\tau_{t+2}$; two critical-size shadow layers cost at most $C\lambda_t^{2d+1}$ by (3.16), (3.19). Hence

$$G_t(Z_i)\le\tau_{t+2}+C\lambda_t^{2d+1}.\tag{2.1}$$

The exact recursions (3.10)–(3.11), applied to a pure merger, add the two old exponents and charge only polynomially many old/new sites in this one step. Both an upper and a lower version therefore hold:

$$\sum_{i=1}^2G_t(Z_i)-C\lambda_t^{2d+1}
\le G_{t+1}(Z')\le
\sum_{i=1}^2G_t(Z_i)+C\lambda_t^{2d+1}.\tag{2.2}$$

The lower side and $\kappa_{t,1}(Z_i)>\tau_{t+1}$ show $K(Z')\ge1$, indeed $\kappa_{t+1,1}(Z')>\tau_{t+2}$ for large $\lambda_t$. The upper side and (2.1) show $G_{t+1}(Z')\le2\tau_{t+2}+O(\lambda_t^{2d+1})$. Since shadow costs are nonnegative, its counter can remain positive only while

$$\tau_{t+1+n}<2\tau_{t+2}+O(\lambda_t^{2d+1}).$$

The defined $K(Z')$ bounds the *predicted* lifetime. To control the actual lifetime as well, apply the exact no-gain recursions (3.10)–(3.11) after the merger. At each scale a critical-size shadow can add at most $C\lambda_s^{2d+1}$ to $G_s$ relative to the initial budget. Through $O(\lambda_t)$ scales this is $O(\lambda_t^{2d+2})=o(\tau_t)$ when the allowed exponent is chosen $p_2\ge2d+3$. Thus the first actual pre-$R$ zero time $k'$ obeys the same leading upper bound:

$$k'-t\le\left(\frac{2^{1/p_2}-1}{\theta}+o(1)\right)\lambda_t+O(1)<\lambda_t\qquad(\lambda_t\to\infty).\tag{2.3}$$

The coefficient is $2^{1/p_2}-1$, **not** exactly $\log2/p_2$; the latter is only its first-order approximation. Here $p_2\ge2d+3$ is an allowed choice in P5 and $\theta\ge\log2$. At $k'$ the component has $K=0$ and is admissible up to the pre-$R$ step: all earlier components had positive counters, including the merged one until exhaustion. P5 H6 only requests this past positivity. The $p_2=2d+2$ endpoint would require a separate constant comparison; one allowed large exponent already refutes the unqualified printed proposition.

More strongly, for any fixed $q$ and sufficiently large $\lambda_t$, (2.3) gives $k'-(t-q)<\lambda_{t-q}$. Thus P6's $k_1$ must be earlier than $t-q$; take $q=3$. Three backward steps from first contact leave the two old pieces separated by at least order $L^2MR_{t-3}$ under the buffer layers of P5 (2.3)–(2.4). For the standard choice $L\ge3$, this exceeds the critical diameter $12M[R_{t-4}]$ of P6 (3.16); the exact integer buffer inequality is the remaining geometric realization to formalize. Consequently $Z_{t-3}\cap Z'$ is not one small box, contradicting P7's connected-box reading of (ii). Trying to read “diameters” componentwise does not save (ii): at $j=t$ each old piece controls only one step, while (2.3) and $K(Z')\ge1$ require control of $k'-t\ge2$ steps. A mixed reading, componentwise geometry plus a pooled budget, is precisely a new theorem and still does not justify P7 p. 498. The hull rule boxes an individually small component; it neither prevents the later first contact nor rewrites the separated past as one box.

The refutation attempt was to look for a hidden convention in H6 admissibility, in P6's replacement of $Z_k$ by $Z_j\cap Z$, in the hull rule, and in E10's induction. None supplies the missing exclusion. E10's $K$ is geometric and (1.88) deliberately pays for joining old components, so its proof cannot establish the converse asserted in P6.

## 3. Repairs and counting

### Why the literal per-component reserve is insufficient

The original proposal $\nu(Z)=\#\{\text{components of }Z_{k_1}\cap Z\}$ handles two-piece mergers, but it can equal **one** for an old connected region of large volume at $k_1$. Adding one new large-field cube to that region resets a “since last gain” clock; it does not erase its old sites from P7's factor $\exp[\beta_kA^*_{0,k}(Z_{k_1};\phi'_k)]$. Resetting $\nu$ to one on this gain therefore gives no bound proportional to the number of old pieces or sites. A hull has the same problem if it is treated as a reset. This is an independent reason not to freeze the $\nu$ variant suggested in LFR-01 as stated.

Use instead an **atom tally** $N_k(Z)$. Each newly gained large-field cube is one atom, and a kept $R$ output (already a single critical-size box) is one new atom. A shadow or hull retains its atoms; a joining event with $m$ old parts and $r$ new gain cubes has $N' =\sum_{i=1}^m N_i+r$; a kept $R$ resets to $N'=1$. Removed $R$ components disappear. This deliberately overcounts coincident descendants. Its needed geometric lemma is: during a window with no new gain or kept $R$, the part descended from **one** atom can be covered at every scale $j$ by $C$ boxes of side $M\rho_j$, $\rho_j=O(\lambda_j^2)$; the layer and boundary covers have respectively $C(M\rho_j)^d$ and $C(M\rho_j)^{d-1}$ sites. It follows by attribution of every seed shadow, including the bounded-diameter hull filler, to an atom. A complete proof for P5's exact $\pi_j$ and hull conventions is outstanding.

### Budget invariant and every event inequality

Use the architecture's notation $G_k=\kappa_k-\log C-H_k|Z|_k$, $\tau_t=2A_2\lambda_t^{p_2}$, ripeness time $t^*(Z)$, spine length $\ell(Z)$, $v_j=c_vC_V\lambda_j\rho_j^{d-1}$, $w_j=v_j\rho_j$, $\sigma_k=\sum_{j>k}v_jL^{-(j-k)}$, and

$$V_k(Z)=2\sigma_k\ell(Z)+\sum_{j=k+1}^{t^*(Z)}w_j,\qquad
G_k(Z)\ge\tau_{t^*(Z)}+V_k(Z)+a_NN_k(Z).\tag{A}$$

Take $a_N$ fixed, larger than twice the eventual sum of the per-atom P7 losses. Before $R$, allow $t^*=k$; afterward require $t^*>k$. The strengthened invariant is a new proposal, not a printed Balaban statement. P6 (3.10)–(3.11), with a sufficiently large coefficient $c_1$ for predicted new-layer cost, yield the budget recursion (architecture §3.4)

$$G_{k+1}(Z')\ge\sum_{i=1}^mG_k(Z_i)+r g_k-c_v\lambda_{k+1}|Z'\setminus Z_k^\uparrow|_\#,
\qquad g_k=A_3\lambda_k^{2p_0}.\tag{B}$$

For a pure shadow, $N'=N$, $\ell'\le\ell/L$, $t^{*\prime}\le t^*$ and $|Z'\setminus Z_k^\uparrow|\le C_V\rho_{k+1}^{d-1}(\ell/L+\rho_{k+1})$. The identity $\sigma_k=L^{-1}(v_{k+1}+\sigma_{k+1})$ gives, term by term,

$$\begin{aligned}
G_{k+1}&\ge\tau_{t^*}+2\sigma_k\ell+\sum_{j=k+1}^{t^*}w_j+a_NN-v_{k+1}\ell/L-w_{k+1}\\
&\ge\tau_{t^{*\prime}}+2\sigma_{k+1}\ell'+\sum_{j=k+2}^{t^{*\prime}}w_j+a_NN'.
\end{aligned}\tag{3.1}$$

For an event, let $D_{k+1}=O(\rho_{k+1})$ and $E_{k+1}=(1+2C_\sigma 2^{3d})v_{k+1}D_{k+1}=O(\lambda_{k+1}^{2d+1})$. The spine union has $\ell'\le\sum_i\ell_i/L+(m+r-1)D_{k+1}$. After cancelling inherited atom reserves $a_N\sum_iN_i$ on both sides, the *only* change to architecture (4.2) is that each new gain must also buy one atom:

$$\boxed{\ \sum_i\tau_{t_i^*}+\sum_i\sum_{j=k+1}^{t_i^*}w_j
 +(g_k-a_N)r+v_{k+1}\sum_i\ell_i/L
 \ge\tau_{t^{*\prime}}+\sum_{j=k+1}^{t^{*\prime}}w_j+(m+r-1)E_{k+1}.\ }\tag{3.2}$$

There is **no merger tax proportional to $N$**: at a pure merger $r=0$, $N'=\sum N_i$. For completeness, the inequalities closing (3.2) are as follows. Put $\lambda=\lambda_{k+1}$; the architecture's geometric estimate gives $\lambda_{t^{*\prime}}\le c_*\lambda+2\theta_+\Lambda'$, where $\Lambda'=\log_L\max(\ell',1)$.

* If $r\ge1$ and $\Lambda'\le\lambda$, the right side is at most $C\lambda^{p_2}+C\lambda^{2d+2}+(m+r-1)C_E\lambda^{2d+1}$. The left has $m\tau_{k+1}+(g_k-a_N)r$ and therefore dominates because $2p_0>p_2\ge2d+3$, $g_k-a_N\asymp\lambda^{2p_0}$, and $\tau_{k+1}\gg E_{k+1}$.
* If $r\ge1$ and $\Lambda'>\lambda$, either $\sum_i\ell_i/L\ge L^{\Lambda'}/2$ and $v_{k+1}\sum_i\ell_i/L\ge c\lambda L^{\Lambda'}\gg C\Lambda'^{p_2}$, or $(m+r-1)D_{k+1}\ge L^{\Lambda'}/2$ and $C\Lambda'^{p_2}\le m+r-1$ for large $\lambda$. The remaining $(m+r-1)E_{k+1}$ is paid by $m\tau_{k+1}+(g_k-a_N)r$.
* If $r=0$, $m\ge2$, let $i_0$ maximize $t_i^*$. When $t^{*\prime}\le t_{i_0}^*$, the $(m-1)$ spare thresholds pay $(m-1)E_{k+1}$ because $\tau_{k+1}\gg E_{k+1}$. Otherwise the extension is only the smallness-clock delay $\Delta\le3+\log_Lm+\log_L(1+D_{k+1})+n_2(k+2+\Lambda')$. The exact sufficient inequality is
$$ (m-1)\tau_{k+1}+v_{k+1}\ell_{\max}/L\ge
 \Delta[2A_2p_2\theta_+\lambda_{t^{*\prime}}^{p_2-1}+C_w\lambda_{t^{*\prime}}^{2d+1}]
 +(m-1)E_{k+1}.\tag{3.3}$$
For $\Lambda'\le\lambda$, $\Delta\le(m-1)(1+C\log\lambda)$ and the right side is at most $(m-1)C(1+\log\lambda)\lambda^{\max(p_2-1,2d+1)}<(m-1)\tau_{k+1}$. For $\Lambda'>\lambda$, either $\ell_{\max}\ge L^{\Lambda'/2}$ and the exponential spine term pays (3.3), or $m\ge L^{\lambda/4}$ and $(m-1)\tau_{k+1}$ pays it. These are the two subcases in architecture §4.5, now with atom reserves cancelling exactly.

At a ripe $R$ event, the **analytic obligation** below is $L_R\le C_R\lambda_k^{2d+2}+a_NN$. If the component is kept, its new gain is $g'_k=A'_3\lambda_k^{2p_0-4}$ and $N'=1$. Thus (A) after $R$ follows from

$$\begin{aligned}
G_{\rm new}&\ge\tau_k+V_k+a_NN+g'_k-C_R\lambda_k^{2d+2}-a_NN,\\
g'_k&\ge C_R\lambda_k^{2d+2}+\bigl(\tau_{k+n_q(k)}-\tau_k\bigr)
 +\sum_{j=k+1}^{k+n_q(k)}w_j+a_N,
\end{aligned}\tag{3.4}$$

which holds for sufficiently large $\lambda_k$ when $2p_0-4>p_2\ge2d+3$, since $\lambda_{k+n_q(k)}\le c_*\lambda_k$ and $n_q(k)=O(\lambda_k)$. A removed component needs no new invariant. The initial gain $g_0$ pays the base threshold, geometric potential and $a_N$ per atom by the first $r\ge1$ case.

This is the complete **counting** induction conditional on (B), the cover lemma and the P7 analytic obligation; it does not promote those obligations to proved facts.

### What has to change in P7

Let $I=[k_1,k]$ be a gain-free and $R$-free window ending at a ripe component. The atom cover gives at every $j\in I$

$$|Z_j\cap Z|_j\le N C(M\rho_j)^d,
\quad|Z_{j+1}\setminus Z_j^\uparrow|_{j+1}\le NC(M\rho_{j+1})^d,
\quad|\partial Z_j\cap Z|_j\le NC(M\rho_j)^{d-1}.\tag{3.5}$$

At the late scales $[k-n_2,k]$, keep the original single-box geometry so that P7's $Z_0,Z'''$, denominator and minimizer (2.2)–(2.5), (2.18)–(2.30), Lemma 2.1 and (3.4) are unchanged. The earlier window needs these replacements:

| P7 place | Printed one-box use | Required per-atom conclusion |
|---|---|---|
| (2.15), p. 501 | $|Z_{j+1}|<(12LM[R_j])^d$ at each $j$ | Use (3.5); charge the actual $\sum_jc_1\lambda_j|Z_{j+1}\setminus Z_j^\uparrow|$ in P6 (3.19) and refund it in P7 (3.8)–(3.9). It need not be $O(1)$. |
| (2.33), p. 505 | One boundary of size $O(R_{k_1}^{d-1})$ | Use local/product entropy factors for the new $Q''_{k_1}$ decomposition, attributed to atoms or to activated sites; a global $N R^{d-1}$ entropy penalty cannot be put against one $Q''$ gain. |
| (2.59), p. 511 | $|Z_{k_1}|_\eta\le L^{-dn_1}(12MR_{k_1})^d$ | Bound the main-action and first surface exponents by $Nq_{59}$, where $q_{59}\le C\beta_{k_1}\varepsilon_{k_1}^2R_{k_1}^dL^{-2(1+\alpha)n_1}=o(1)$ on the same analytic domain as the printed estimate. |
| (2.60), p. 511 | $\operatorname{diam}_j(\Omega^c_{j+1})<10LMR_j$ at **every** $j$ | Decompose the displayed sum per atom. The total is at most $Nq_{60}$, $q_{60}\le C R_k^{d+2}p_0(\beta_k)^3\beta_k^{-1/2}=o(1)$. Move this field-independent error out of the positive quadratic form as an exponential loss; the printed absolute bound $<1$ need not hold. |
| (3.17)–(3.19), pp. 523–524 | One $(10LMR_j)^d$ at every scale of the analytic extension | Decompose all six quadratic terms and the renewed (2.60) term per atom. Obtain $|\beta_k\delta A^*_{0,k}|\le Nq_{17}$ and $|\exp(-\beta_k\delta A_k^*)|\le e^{Nq_{19}}$ with $q_{17}+q_{19}\le C\beta^{-1/4}=o(1)$, preserving the real-part positivity used in §3. |

The equality/inequality to recover P7 (3.8) is a **window certificate**, not merely the final bound $G_k\ge\tau_k+a_NN$: for the components $Z_{k_1,i}$ and the actual gain-free history, prove by the same event induction (3.1)–(3.3) that

$$\sum_iG_{k_1}(Z_{k_1,i})-\sum_{j=k_1}^{k-1}c_1\lambda_j
 |Z_{j+1}\setminus Z_j^\uparrow|_{j+1}\ge\tau_k+a_NN.\tag{3.6}$$

It is essential to use a cost coefficient $c_1\ge C_{(3.9)}$. P7 p. 520 explicitly says the constants in the sum (3.8) can be taken large enough to cancel (3.9). That **refund route** remains valid with many atoms; its alternative argument, bounding all of (3.9) by $C\lambda_k^{2d+2}$, does not. If $q_{59}+q_{60}+q_{17}+q_{19}\le a_N/2$, (3.6), P7 (3.8)–(3.9), and the late single-box bound $|Z_0|\le14^d$ give

$$\log\|T''_ke^{E_k|Z|}\|
\le-\tau_k-a_NN+N(q_{59}+q_{60}+q_{17}+q_{19})
 +C_R\lambda_k^{2d+2}-H_k|Z|_k
\le-p_2(\beta_k)-H_k|Z|_k,\tag{3.7}$$

for $p_2>2d+2$ and large $\beta$, since $\tau_k=2p_2(\beta_k)$. Equation (3.7) is the promised version of P7 (3.10) and gives the loss premise of (3.4). The local entropy assertion for (2.33), the atom cover, the full six-term complex estimate, and the window certificate in the exact P5/P6 region calculus remain to be written and checked. In particular, it would be incorrect to cite the printed $O(1)$ in (2.60) or (3.19) for arbitrary $N$.

### Interaction with P6 Theorem 4

At $k_0$, discard the nonnegative atom reserve and transfer (A) to the frozen invariant $G_{k_0}\ge p_2(\beta_{k_0})+2\sigma_{k_0}\ell+\sum_{j=k_0+1}^{k_f}w_j$. Since $k_f-k_0<\lambda_{k_0}$ and $\lambda_{k_f}\le(d/2+o(1))\lambda_{k_0}$ (P5 p. 500 and the P4 running estimate), it suffices that

$$A_2\lambda_{k_0}^{p_2}\ge C_w\lambda_{k_0}\bigl((d/2+o(1))\lambda_{k_0}\bigr)^{2d+1},\tag{3.8}$$

true for $p_2>2d+2$. During the remaining no-$R$ steps, the threshold stays $p_2(\beta_{k_0})$ and the same $v,w,\sigma$ potential pays the layers and mergers; no P7 window or atom reserve is needed. This avoids P6 p. 22's false final comparison $2p_2(\beta_{k+K})-C\lambda^{2d+2}>p_2(\beta_{k+n})$ over $n-K\asymp\lambda$: its right side grows by a fixed factor exceeding two, regardless of $A_2$. Freezing also preserves the terminal P7 §4 estimate because the frozen polynomial in $\lambda_{k_0}$ dominates the required linear function of $\lambda_{k_f}$.

### Option (b)

E10 (1.88) is the precedent for keeping P7's full single-box window and paying its restart after a merger from pooled gains frozen at their creation times. This has the lower **analytic** cost: (2.59), (2.60), (3.17)–(3.19) would retain their printed one-box proofs. It has a higher, presently unresolved **combinatorial** cost. One needs a precisely defined geometric stopping time, a reserve attached to each surviving gain atom, and a uniform inequality that the pooled frozen reserve pays the repeated $n_q$ windows, their layer costs, and the threshold at the actual $R$ time. A proposed bound $N\ge2^{\lfloor a/(n_q+C)\rfloor}$ for a lineage of age $a$ is **not** supplied by E10; it needs a proof that each long delay has two independently old paying branches. E10's gauge argument uses $2p_0(g_{j(Z)})$ and (1.87), not the growing O(N) threshold $2A_2\lambda_j^{p_2}$. Thus (b) is plausible and perhaps shorter if its tree inequality can be proved, but cannot presently be called a working O(N) repair. The assertion in architecture §4.9 that no restart argument can close is likewise too strong.

## 4. Open points and confidence

| Claim or obligation | Status and confidence |
|---|---|
| E10 has an explicit merger/tree refund, (1.84)–(1.88), but its $K$ is geometric | **Read directly from page images, 99%.** |
| P5–P7 have no printed merger rule that turns the pooled budget counter into P7's full quiet window | **High, 95%.** P6 (3.19), Prop. 3.2(ii), P7 p. 498 were checked; an unstated geometric restriction elsewhere remains logically possible but was not found in §§1–3. |
| P6 Prop. 3.2(ii) fails for two nearly exhausted components | **High, 90%.** The budget bounds (2.1)–(2.3) are explicit. The exact first-contact placement should be formalized for the chosen torus partitions and iterative hull rule. |
| A reserve counting just components at $k_1$, reset at a gain, suffices | **Rejected, 95%.** One connected old region can contain many primitive sources while P7 (2.59) still sees all its sites. |
| Atom-reserve counting (3.1)–(3.4) closes, given (B) and the cover lemma | **Conditional mathematical derivation, 85%.** Event arithmetic is inherited from architecture §4.5; exact region attribution remains open. |
| P7's per-atom analytic estimates and local entropy refinement yield (3.7) | **Plausible, 65%.** The listed page-by-page estimates expose all known single-box uses, but no full rewritten P7 proof exists. The (2.33) entropy and complex extension are the main risks. |
| P6 Theorem 4 is repaired by a frozen $p_2(\beta_{k_0})$ threshold | **High, 95%**, subject to the standard running-coupling bounds and the full large-field invariant. |
| Option (b) has a valid O(N) doubling/pooled-reserve proof | **Open, 45%.** E10 provides the idea, not the required age inequality for these histories. |

The next decisive task is a source-level proof of the atom cover through P5's hull rule, followed by a rewritten P7 (2.33), (2.59)–(2.60), (3.17)–(3.19) and (3.8)–(3.10). Until those are checked, (A) and (3.7) are repair specifications, not claims that Balaban's printed argument already proves the O(N) theorem with mergers.

### Frozen evidence identifiers

SHA-256 of the read-only inputs at this audit. The PDF keys identify the files listed in `/home/scott/Balaban/review/SOURCES.md`.

| Input | SHA-256 |
|---|---|
| P5 | `b3f0ef3491fc63b3988768893c1452b4bd1458a5f3e408e6af6000a555fd9a0f` |
| P6 | `ee0ca061c9a7418d5da907a4dd09b66fb247f46bffcf68f83fa3ba502c342fc4` |
| P7 | `c48e08dd439878a0245cceb6e6aead787a8ce7671865f6360c8464a7e579d2e9` |
| E8 | `e33eb7e78a5221bd1aa4afc1508900828981e3ea30449fccde98b65929421760` |
| E9 | `964fb069650acc4f7f748e2b9427ea20347998dd6610ae068f0223e251a7fd72` |
| E10 | `2da067e058d103269cf82b571a68f54f8a5544109a63a4f75f55718ccd4614f1` |
| LF-ARCHITECTURE.md | `887260c89b80c5d36a1271bd726057b7d4887e22da359ce8ef70925bdbb102ea` |
| LF-ARCHITECTURE-review.md | `b7f1526796b4126cfd29db29e6055cc7af25e7ca8b5229721df7dde7e84c9b6a` |
