# OBSERVABLES: the one- and two-point functions through the flow (phase 1, document D-TP; C-1a)

**Version 2** (2026-10-12), after `OBSERVABLES-review.md` (O-01…O-10) and the completion of `LF-RECONSTRUCTION.md` Parts I–IV; see "Review dispositions" and "Version 2 changes" at the end. Status: draft for review. Pure mathematics on paper; no Lean was written or run. Labels: **proved** (a complete argument is given here, possibly from named inputs), **cited** (a source or another phase-1 note proves it), **sketched** (plan with the key estimate), **UNCERTAIN:** (doubt). Page numbers are journal pages (P9 = CMP 199, pp. 493–520; PDF page = journal $-492$; text layer of `sources/s002200050510.pdf` read for pp. 495–519). Hard spins ($\lambda=\infty$), $d\ge3$, $N\ge2$ throughout. The Lean `C1Star` has been corrected accordingly (W34: F-B, O-02, F-A).

**What was read.** AGENTS.md; the brief; `review/papers/P9-*.md`; the P9 text layer in full (pp. 493–520); `CORRELATIONS.md` (all), `SMALLFIELD.md` (§§0, 1, 3.5, 5, 6), `POLYMER.md` (§§0, 2.5, 4.1 headings), `LF-ARCHITECTURE.md` (§§1.2–1.4, 3.6, 3.7 LF-1…LF-4, 8.3, LF-7, LF-8), `LF-RECONSTRUCTION.md` (§I.1), `review/FORMALIZATION_ROADMAP.md` §3.2, `notes/ERRATA.md` (P9 rows), the frozen `Balaban/Frozen/Roots/LowTemperatureCorrelations.lean`, and `Balaban/Correlations/C1Star.lean`, `RootCFromFlow.lean`, `Assembly.lean` (as consumers). `GREEN.md` G-5 was read at the statement level only.

Notation. $\mathbb T_\ell=(\mathbb Z/\ell)^d$; $\beta_j=\beta L^{j(d-2)}\gamma_j$, $\nu_j=\nu L^{2j}\delta_j$ (the sequences of `Balaban/Flow/RunningCoefficients.lean`); $k_f$ the last scale of Root-F and $J:=k_f+1$; $\xi_j:=L^{-j}$ (P9's $\xi$; not to be confused with the running coefficients $\xi^{(k)}\in\mathbb R^3$, which are always written with a superscript or the index $k$); $\eta:=L^{-k}$ at step $k\to k+1$. $|x|_1,|x|$ are the $\ell^1$ and sup norms. $T_j^{\ell,\mu}$ are the Gaussian kernels of `CORRELATIONS.md` §2.1 (plain units, $\sum_{j\ge0}T_j=(-\Delta+\mu)^{-1}$ up to the remainder (2.1) there).

---

## 0. Summary (the reply asked for by the brief)

**C-1a in one paragraph.** Fix a representation of $\rho_k$ in the small-field class (Def-6, the small-field part of Def-7). C-1a adds to it an *observable layer* $\mathcal O_k$: real numbers $\mu_j(x)$ ($1\le j\le k$, $L^j\mathbb Z^d$-periodic, $|\mu_j|\le\beta^{-1/2+\rho_1}L^{-j\rho_0}$), vector functions $M^{(j)}(x,X;\psi,h)$ and matrix kernels $R^{ij}(x,x';X;\psi,h)$ ($i\le j\le k$), analytic on the Def-6 domains, $O(N)$- and Euclid-covariant, localized with the bounds $\beta^{-1/2+\rho_1}L^{-j\rho_0}e^{-\kappa d_j(X)}$ resp. $\beta^{-1/2+\rho_1}L^{-j\rho_0}e^{-\delta_0L^{-i}|x-x'|_1}e^{-\kappa d_j(X)}$, with the normalization $M^{(j)}(x;h,h)=0$, such that the first and second $g$-derivatives at $g=0$ of the whole-lattice generating function are exactly
$M_k=m_k\varphi_k+\sum_{j\le k}\beta_{j-1}^{-1/2}M^{(j)}$, $m_k=1-\sum_{j\le k}\beta_{j-1}^{-1/2}\mu_j$, and $G_k=C_k+R_k$, $C_k=\sum_{j\le k}\beta_{j-1}^{-1}m_kG^{(j)}m_k$, $R_k=\sum_{i\le j\le k}\beta_{i-1}^{-1}R^{ij}$. At $\lambda=\infty$ and $\psi\equiv h$ the Gaussian kernel $G^{(j)}$ is exactly transverse and equals $(I-h\otimes h)\,T_{j-1}^{\ell,\nu\delta_{j-1}}$ in plain units (Lemma 2.1, proved from the sphere constraint and the stabilizer symmetry), so the longitudinal main term is $0$. One small-field step preserves $\mathcal O_k$ with new $\mu_{k+1},M^{(k+1)},R^{i,k+1}$ (Theorem 3.1); $R$ does not touch $\mathcal O_k$, it only adds $\mathcal R''^{(k)}_m(\cdot;g)$ to an inherited package that enters through its sup bound (§4); the last step adds $\partial_g^{1,2}$ of $\mathcal R^{(J)}$ and $\mathcal P^{(J)}$ (§5), and gives C-1* after two amendments of the Lean interface and one convention (the three findings below).

**Which proofs are complete** (details in the sections named).
- *Proved:* the structure of $G^{(j)}$, $H_{j-1}$ at $\psi\equiv h$ and the vanishing of the longitudinal main term (Lemma 2.1); the dictionary with the first-order class (H.7) and Root-F (Lemma 2.2); the bounds on $m_k$ and the decay of $R_k$ (Lemma 2.3); the existence of an admissible set of exponents $\rho_0,\rho_1,\rho_2$ with an explicit choice (Lemma 1.1); the Cauchy lemma for the $g$-derivatives of inherited packages (Lemma 3.2); the exponent bookkeeping of every new term of the step (§3.5–3.7: all powers of $\beta,\eta,\xi$ recomputed, two misprints of P9 found); the identification of the Gaussian main term of $R_1^{k+1,k+1}$ (Lemma 3.5); the mass reconciliation lemma for the $\nu$-free regime (Lemma 4.2); the derivation of the $F_2$ and $F_3$ clauses of C-1* from the last step *including the existence of the torus limits and of the $\nu\downarrow0$ limits* (§5; proved given Theorem 3.1, Proposition 5.1 and (CONT), by Tannery and `CORRELATIONS.md` Theorem 4.1); the $\beta$-uniformity analysis (§6).
- *Cited / reduced:* P9 Prop 3.1 with the truncated product (3.13) is reduced to the marked polymer expansion PE-M (`POLYMER.md` §4.1, conditional on the product-measure form), with the hole version needed for large-field regions (Proposition 3.3); P9 Lemma 2 is stated with a proof plan from P1 (Lemma 3.4); the Gaussian inputs are `GREEN.md` G-5 and `BACKGROUND.md` Prop 5.4.
- *Sketched:* the continuity clause (CONT) for the whole observable layer (§3.8: induction on $k$ with Vitali and the contraction Lemma 3.3 of `SMALLFIELD.md`); the carrying of $g$ through LF-3/LF-4/LF-5 (§4; now supplied by `LF-RECONSTRUCTION.md` Parts II–IV, Remark IV.4.5); the last-step Gaussian term (§5.2).

**What LF-4 (and LF-3, LF-5, LF-8) must add so that the second-order terms survive $R$** (§4): nothing new in the statement of LF-4 (c)/(e), but five points must be written into the reconstruction document and the Lean statements: (i) $g$ is an analytic parameter of the whole of Part II–III on the closed polydisc $\|g\|_{\ell^1}\le1-\epsilon_g$, with $|e^{\langle g,\varphi\rangle}|\le e$ for hard spins used in every estimate; (ii) the coset average (M4) is taken on the full integrand so that $\mathcal R''^{(k)}_m(\psi,h,g)$ is jointly $O(N)$-covariant in $(\psi,h,g)$ (closed by `LF-RECONSTRUCTION.md` Lemma III.9.6); (iii) $\mathcal R''^{(k)}_m(X;\cdot)$ and the boundary terms depend on $g$ only through $g|_{\mathbb B(X)}$ (locality in $g$), which is what makes $\partial_{g(x)}$ pick polymers containing $x$; (iv) the bound $\beta_k^{-m-1}e^{-\kappa d_k(X)}$ is a sup bound on the whole $g$-polydisc (no real-$g$ restriction); (v) the large-field data at scale $k$ must be an analytic function of $b=\nu h$ with $\nu$-independent domains (clause (CONT)); in particular no *definition* (as opposed to an inequality) at scale $k\le j$ may use the a priori horizon $\hat k_f(\nu)$. The large-field operators depend on $g$ through $e^b$ (replacement (L4$'$) of the false (L4)); their $g$-derivatives are marked terms inside the activities, controlled by Lemma 3.2. P9 needs nothing beyond Def-7's polymer bounds *once* the marked expansion is available on subdomains (hole version); it does not use the operator bounds (P4)/(P5) of Def-7 at all except through the final polymer expansion (LF-8).

**Answer to item 5 (the $\beta$-dependence).** P9's constants need not depend on $\beta$, and the flow gives $\beta$-independent ones. In Root-C only four constants must be uniform in $\beta$ for the statement to hold as frozen: $q$ (equivalently $L,M$), $c'$, $\rho_0$, and the constant in $|\gamma_\infty-1|\le c/\beta$. All four are fixed before $\beta$ in the quantifier prefix of `LF-RECONSTRUCTION.md` §I.1.4 (they come from $L,M,\kappa,\gamma,\rho_2$ and the contraction constant $C_\xi$ of P4 (5.25)–(5.31)). The other constants may grow like $\beta^{1-\epsilon}$ (for $c$ in the $G$-bounds) or $\beta^{\epsilon}$ (for the constant in $|m-1|$, absorbed in $\rho_1<1$) without changing the statement (§6). The negative finding of §6 is not about $\beta$: Root-C's form of C-1* has $J$ before $\beta$, whereas $k_f$ depends on $\beta$ (Finding F-A).

**Three findings about the Lean interface C-1\*** (details in §5.4; each has a minimal fix):
- **F-A (hedge; landed in W34).** Moving `J, J_pos, J_tendsto, J_bounds` into `data` is a safe weakening, not forced (OBSR O-03): the assembly takes `kf` $=\hat k_f(\nu)$, which is $\beta$-free.
- **F-B (landed in W34).** The remainder bound of `C1StarF3` needs the extra term $\nu^{(d-2)/2}$: the last Gaussian term is the massive final integral $P_{k_f}A_{k_f}^{-1}P_{k_f}^{\top}=T_{k_f}+E_{\rm tail}$ and the tail, of size $\beta^{-1}L^{-J(d-2)}$, exceeds $(1+|z|)^{-(d-2+\rho_0)}$ in the window $L^{J(d-2)/(d-2+\rho_0)}\ll|z|\ll L^J$ (never zero, OBSR O-01). Root-C is unaffected (§5.4). **F-B2 (O-02, landed):** the `em` bound holds for $\ell\ge\ell_0(\nu,x)$ only, because winding terms of the one-point sums are not $O(\beta^{-2}L^{-2J(d-2)})$ on small tori.
- **F-C.** In the $\nu$-free regime $k\le k_0$ (Def-6 backgrounds without the $\nu$-term) the Gaussian kernels $G^{(j)}$ are the massless ones, whereas `mainTr` uses the masses $\nu\delta_j$. Fix: Lemma 4.2 (the difference is a remainder of size $\beta^{-2}L^{-2j(d-2)}$, proved from G-5(b)); no change in Lean.

**Main risk.** The two-function truncated expansion (P9 (3.13)) on subdomains with the full boundary-term weight, together with the continuity clause (CONT) for every object of the flow including the large-field data. Second: the exact form of the last step (§5.2), which no source writes down. **Size:** $\approx45$k–90k Lean lines on top of `CORRELATIONS.md` §6's 4.5k–5.5k (the 40k–80k of `SMALLFIELD.md` §6 for X1–X7 is the largest part; §7.5). **Questions:** §7.6 (six).

---

## 1. Conventions, dictionary, constants

### 1.1 Index shifts and units

P9 uses three index conventions; they are fixed once here.

1. *Step index.* The step $k\to k+1$ integrates the fluctuation at scale $k$ and creates the objects with superscript $k+1$: $\mu_{k+1},M^{(k+1)},R^{i,k+1}$ ($1\le i\le k+1$), $G^{(k+1)}=H_kC^{(k)}H_k^*$ (P9 (2.13): $G^{(j)}=H_{j-1}C^{(j-1)}H_{j-1}^*$).
2. *Plain units.* `CORRELATIONS.md` (2.2): $\beta_{j-1}^{-1}G^{(j)}_{tr}(h,h)=(\beta\gamma_{j-1})^{-1}T_{j-1}$ with $T_{j-1}=L^{-(j-1)(d-2)}K_{j-1}$ the plain-unit kernel. The weighted-adjoint convention ($Q^*=L^dQ^\top$, P9 (4.12)–(4.17)) is Question 3 of `CORRELATIONS.md` and is not reopened here.
3. *Last scale.* $J=k_f+1$; the C-1* sums run over $j\le J$ (for $\mu_j$) and $j<J$ (for $T_j$).

### 1.2 Dictionary

| Object | P9 | `SMALLFIELD.md` / `LF-ARCH` | `C1Star.lean` / `CORRELATIONS.md` |
|---|---|---|---|
| first-order scalar | $m_0^{(j)}(x)$ (2.8)–(2.9) | — | `μ j ν x` $=\mu_j(\nu;x)$ |
| first-order vector, normalized | $M^{(j)}(x,X;\psi,h)$ (2.5)–(2.7) | $\mathscr M^{(j)}$ of (H.7), $\mathscr M^{(j)}=\beta_{j-1}^{-1/2}(M^{(j)}-\mu_j\varphi_j)$ at $g=0$ (Lemma 2.2) | — |
| second-order remainder | $R^{ij}(x,x';X;\psi,h)$ (2.12)–(2.18) | second $g$-derivative of $\sum_j\mathscr F^{(j)}$ and of the inherited packages | `rtr, rlg` (after $\psi=h$ and the last step) |
| Gaussian kernel | $G^{(j)}=H_{j-1}C^{(j-1)}H_{j-1}^*$ | $\beta_k^{-1}G^{(k+1)}$ of `SMALLFIELD.md` §6.1 item 1 | `termKernel`$\;=T_{j-1}$ (`mainTr`) |
| running coefficients | $\beta_j,\nu_j,a_j$ | $\xi(\nu,k)$ of Thm 5.3 | `ξ ν k` |
| last scale | $k(v)$, $k+1$ of (4.7) | $k_f$ | `J ν` $=k_f+1$ |

### 1.3 Constants

The constants of Def-6/Def-7 are those of `LF-RECONSTRUCTION.md` §I.1.3–I.1.4 ($L,M,\kappa,\gamma,\alpha_1,c_8,c_9,\alpha_0,E_0,B,\dots$). The observable layer adds, *after* $L,M,\kappa$ and before $\beta$ (row 17 of §I.1.3): $\rho_2,\rho_1,\rho_0$, $\delta_0:=\kappa/M$ (P9 p. 508–509), the localization constant $G_0$ of P9 (3.25) and a sum constant $K_0^{\rm O}\ge\sup_x\sum_{X\ni x}e^{-\kappa d_j(X)}$ (P5 (1.35)). $\beta_0$ is enlarged last.

**Lemma 1.1 (admissible exponents; proved).** Let $\gamma\in(0,\min\{\frac{d-2}2,\frac12\})$ and $\alpha_1\in(0,\gamma)$ (strict: Root-F's $\delta=\gamma-\alpha_1$-type exponent must be positive; OBSR O-08). The constraints collected from the proofs of §3 are:
- (E1) $\rho_1\ge4\rho_2$ (the new term $R_1^{k+1,k+1}$ has size $C\beta^{-1/2+3\rho_2}\eta^{\ldots}$ with a constant $C\ge1$ from the Cauchy estimates, while (2.1), (2.2) carry the constant $1$; $\rho_1=3\rho_2$ leaves no room; alternatively put a constant $K\ge C_{\rm new}$ before $\beta$ into (2.1), (2.2), as P9's $K_0$; OBSR O-04);
- (E2) $\rho_0\le\frac{d-2}2-3(d-2)\rho_2$ (from (3.17), (3.37));
- (E3) $\rho_0\le1-2(d-2)\rho_2$ (from (3.23) for T2, which needs $1-\rho_0-(d-2)\rho_2\ge0$, and from the row $R_2^{k+1,k+1}$ with two Cauchy factors, which needs $1-\rho_0-2(d-2)\rho_2\ge0$; OBSR O-05);
- (E4) $\gamma>2(d-2)\rho_2$ (from (3.23), P9 p. 511);
- (E5) $\rho_0\le\gamma$ (from (3.46): the renormalization shift term);
- (E6) $\rho_0\le d-2$ (Root-C remainder, §5);
- (E7) $\rho_0\ge\gamma-\alpha_1$ (compatibility with (H.7), Lemma 2.2);
- (E8) $\beta_0$ large: $C\beta^{-1/2+\rho_2}<\frac12$, and $p_1(\beta)^2\le C\beta^{2\rho_2}$.

They are satisfied by $\rho_0:=\gamma$, $\rho_1:=4\rho_2$,
$$\rho_2:=\tfrac12\min\Big\{\frac{\frac{d-2}2-\gamma}{3(d-2)},\ \frac{\gamma}{2(d-2)},\ \frac{1-\gamma}{2(d-2)}\Big\}>0 ,\qquad \rho_1=4\rho_2\le\frac{\gamma}{d-2}\le\frac12<1 .$$
*Proof.* (E2): $\gamma\le\frac{d-2}2-3(d-2)\rho_2\iff\rho_2\le\frac{\frac{d-2}2-\gamma}{3(d-2)}$. (E3): $\rho_2\le\frac{1-\gamma}{2(d-2)}$ gives $2(d-2)\rho_2\le1-\gamma$. (E4): $\rho_2<\frac\gamma{2(d-2)}$. (E5), (E7) hold with equality/slack since $\alpha_1\ge0$; (E6) since $\gamma<\frac12\le d-2$. $\square$

P9 (3.23) itself prints $1-\rho_0-(d-2)\rho_2\ge0$, $\gamma-(d-2)\rho_2>0$ for the single-factor term T2, which agrees with (E3), (E4) restricted to T2; the printed line on p. 511 ("$\rho_1=3\rho_2$, $\rho_0\le\min\{\frac{d-2}2,1-3(d-2)\rho_2\}$") presumably covers the multi-factor rows. We make no claim that P9's list differs from ours (unverified against the page image; OBSR O-05). (Root-C uses $\rho_0^{\rm C}=\min\{\rho_0,2\gamma\}$ in `CORRELATIONS.md` Theorem 3.1; with $\rho_0=\gamma$ it is $\gamma$.)

---

## 2. C-1a precisely (brief item 1)

### 2.1 The data of the observable layer

Let $\rho_k\in\mathbb R^{\rm sf}_k$ (`SMALLFIELD.md` §1.3, with the Def-6 conventions of §1.6 there: $\nu$-free backgrounds for $k\le k_0$) and let $\varphi_k(x;\psi,h)$ be its background. The *observable layer* $\mathcal O_k$ consists of the following, for $1\le i\le j\le k$.

- **(O1) scalars.** $\mu_j:\mathbb Z^d\to\mathbb R$, invariant under the lattice isometries preserving the partition into $L^j$-cubes (in particular $L^j\mathbb Z^d$-periodic; P9 p. 496: "periodic with respect to translations of the lattice $T^{(j)}$"), with $|\mu_j(x)|\le\beta^{-1/2+\rho_1}L^{-j\rho_0}$. Put $m_k(x):=1-\sum_{j\le k}\beta_{j-1}^{-1/2}\mu_j(x)$.
- **(O2) vectors.** $M^{(j)}(x,X;\psi,h)\in\mathbb R^N$ for $X\in\mathcal D_j$, $x\in X$, depending on $(\psi|_X,h)$, analytic on the localization domain $\tilde\Psi^c_j(\mathbb B_j(X);K\varepsilon_j,K\varepsilon_j)$ of `SMALLFIELD.md` §1.7 (ruling iv), $O(N)$-covariant $M^{(j)}(x,X;R\psi,Rh)=RM^{(j)}(x,X;\psi,h)$, Euclid-invariant (P9 (2.3), (2.4)), with
$$|M^{(j)}(x,X;\psi,h)|\le\beta^{-1/2+\rho_1}L^{-j\rho_0}e^{-\kappa d_j(X)},\qquad M^{(j)}(x;h,h):=\sum_{X\ni x}M^{(j)}(x,X;h,h)=0.\tag{2.1}$$
The vanishing is the renormalization condition (2.7); by $O(N)$-covariance $M^{(j)}(x;h,h)=u_j(x)h$ and (2.7) says $u_j=0$.
- **(O3) matrices.** $R^{ij}(x,x';X;\psi,h)\in\mathbb R^{N\times N}$ for $X\in\mathcal D_j$, $x,x'\in X$, same domain, $R^{ij}(x,x';X;R\psi,Rh)=R\,R^{ij}(x,x';X;\psi,h)\,R^{-1}$ (P9 (2.15), $R^{-1}=R^\top$), Euclid-covariant, and
$$|R^{ij}(x,x';X;\psi,h)|\le\beta^{-1/2+\rho_1}L^{-j\rho_0}\,e^{-\delta_0L^{-i}|x-x'|_1}\,e^{-\kappa d_j(X)}.\tag{2.2}$$
($\kappa_i$ in P9 (2.18) is undefined; every use in §3 produces $e^{-\kappa_0d_j}$ or $e^{-2\kappa d_{k+1}}$ and resums to $e^{-\kappa d}$, so $\kappa_i:=\kappa$ is used; ERRATA proposal in §7.3.)
- **(O4) identification.** With $\mathscr F_k(\psi;h,g)$ the whole-lattice generating function of (H.7) (analytic in $g$ on $\|g\|_{\ell^1}<1$),
$$\mathscr F_k=\langle g,M_k\rangle+\tfrac12\langle g,G_kg\rangle+O(g^3),\tag{2.3}$$
$$M_k(x;\psi,h)=m_k(x)\varphi_k(x;\psi,h)+\sum_{j=1}^k\beta_{j-1}^{-1/2}\sum_{X\ni x}M^{(j)}\big(x,X;\psi^{(j)}_k(\psi,h),h\big),\tag{2.4}$$
$$G_k=C_k+R_k,\quad C_k(x,x')=\sum_{j=1}^k\beta_{j-1}^{-1}m_k(x)\,G^{(j)}\big(x,x';\psi^{(j)}_k(\psi,h),h\big)\,m_k(x'),\quad R_k=\sum_{1\le i\le j\le k}\beta_{i-1}^{-1}\sum_{X\ni x,x'}R^{ij}\big(x,x';X;\psi^{(j)}_k,h\big),\tag{2.5}$$
with $G^{(j)}=H_{j-1}C^{(j-1)}H_{j-1}^*$, $H_{j-1}(x,y;\psi_j,h)=\partial_{\psi(y)}\varphi_{j-1}(x;\psi^{(j-1)}(\psi_j,h)+\psi,h)|_{\psi=0}$ (P9 (2.13)–(2.14)) and the localization expansion $G^{(j)}(x,x')=\sum_{X\supset\{x,x'\}}G^{(j)}(x,x',X)$, $|G^{(j)}(x,x',X;\psi_j,h)|\le G_0e^{-\delta_0L^{-j}|x-x'|_1}e^{-\kappa d_j(X)}$ (P3, P9 (3.25); **cited**; note P9 prints $L^{-1}$ in (3.25) where $L^{-j}$ is meant, since the proof of $R_1^{i,k+1}$ uses decay at scale $L^{-i}$).
- **(O5) parameter and torus clauses.** (CONT): the objects of (O1)–(O3) are defined for $\nu\in[0,\bar\nu]$ as analytic functions of $(\psi,b=\nu h)$ on $\nu$-independent domains, and converge as $\nu\downarrow0$ in the sense of `SMALLFIELD.md` §3.5, with the convention $\mu_j(\nu;x):=0$ for $j>J(\nu)$ and for $\nu>\bar\nu$. (TORUS): the terms $M^{(j)}(x,X;\cdot)$, $R^{ij}(x,x',X;\cdot)$ and $\mu_j$ are defined on finite subsets of $\mathbb Z^d$ and transported to tori; for non-winding $X$ they do not depend on the torus (X7; same clause as (H.4) of Def-6, ER-010).

**Remark 2.0 (what the sum over $X$ means).** The sum in (2.4) is over all $X\in\mathcal D_j$ containing $x$, and in (2.5) over all $X\supset\{x,x'\}$; on a torus $X$ may wind. By (TORUS) the winding terms are not part of the class; they are $O(e^{-\kappa\ell/(ML^j)})$ and belong to the torus-dependent remainder $e_m^\ell$, $r^\ell$ of §5. For the one-point function they are *not* bounded by $\beta^{-2}L^{-2J(d-2)}$ on small tori (OBSR O-02: at $\ell=ML^{J+1}$ the winding term at scale $J$ is $\simeq\beta^{-1+\rho_1}L^{-J(\frac{d-2}2+\rho_0)}e^{-\kappa L}$), so the `em` bound is claimed only for $\ell\ge\ell_0(\nu,x)$; for the two-point function they are absorbed by the term $\nu^{(d-2)/2}e^{-c'\sqrt\nu|z|}$ of F-B.

### 2.2 (H.1) and (H.2) at $\lambda=\infty$: the exact forms

At $\lambda=\infty$ the background $\varphi_k$ lies on $S^{N-1}$ pointwise, $\alpha$ is the multiplier, and the following three facts replace the finite-$\lambda$ computation of P9 (4.12)–(4.13).

**Lemma 2.1 (structure at the constant configuration; proved).** Let $\ell$ be a torus with $L^j\mid\ell$, $\psi_j\equiv h$ and $|h|=1$. Then $\varphi_{j-1}(\cdot;h,h)\equiv h$, and for every $y$:
1. $h^\top H_{j-1}(x,y;h,h)=0$ (the range of $H_{j-1}$ is $h^\perp$);
2. $H_{j-1}(x,y;h,h)=h_{j-1}(x,y)\,(I-h\otimes h)$ with a scalar kernel $h_{j-1}$, and $C^{(j-1)}(y,y')=C^{(j-1)}_{tr}(y,y')(I-h\otimes h)+C^{(j-1)}_{lg}(y,y')\,h\otimes h$;
3. $G^{(j)}(x,x';h,h)=(I-h\otimes h)\,[h_{j-1}C_{tr}^{(j-1)}h_{j-1}^*](x,x')$, hence $h^\top G^{(j)}h=0$: the longitudinal part of $C_k(h,h)$ vanishes identically;
4. with $h_{j-1}=a_{j-1}G_{j-1}Q_{j-1}^*$ and $C^{(j-1)}_{tr}=(\Delta^{j-1}_{tr}+aL^{-2}Q^*Q)^{-1}$ (`BACKGROUND.md` Prop 5.4; P4 (5.11); P9 (4.13)), the scalar kernel $G^{(j)}_{tr}:=h_{j-1}C_{tr}^{(j-1)}h_{j-1}^*$ equals $K_{j-1}=L^{(j-1)(d-2)}T_{j-1}$ with $T_{j-1}=T_{j-1}^{\ell,\nu\delta_{j-1}}$ the plain-unit kernel of mass $\nu\delta_{j-1}$ (unit-lattice mass $\nu_{j-1}$), so $\beta_{j-1}^{-1}G^{(j)}_{tr}=(\beta\gamma_{j-1})^{-1}T_{j-1}$ (`CORRELATIONS.md` (2.2), using $\beta_{j-1}=\beta L^{(j-1)(d-2)}\gamma_{j-1}$).

*Proof.* The constant configuration $\varphi\equiv h$ has zero energy for every $a_{j-1}\ge0$ and $\nu\ge0$ and is the unique small solution (`BACKGROUND.md` I-1), so $\varphi_{j-1}(\cdot;h,h)=h$ and $\psi^{(j-1)}(h,h)=h$. (1) The hard-spin constraint $|\varphi_{j-1}(x;\psi)|^2=1$ for all $\psi$ in the domain gives, on differentiating in $\psi_k(y)$ at the constant configuration, $\sum_i\varphi_i\,\partial\varphi_i/\partial\psi_k(y)=\sum_ih_iH_{ik}=0$. (2) The stabilizer $S\cong O(N-1)$ of $h$ acts with $\varphi(x;S\psi,Sh)=S\varphi(x;\psi,h)$ (covariance of the minimizer) and fixes $(h,h)$, so $H=SHS^\top$ for all $S\in S$. The vector $Hh$ lies in $h^\perp$ (by (1)) and is fixed by every $S\in O(N-1)$ (since $SHh=HSh=Hh$): for $N\ge3$ the representation on $h^\perp$ has no fixed vector, and for $N=2$ the reflection fixing $h$ acts as $-1$ on the line $h^\perp$; so $Hh=0$. The same argument kills the cross blocks of $C^{(j-1)}$. Hence $H=(I-h\otimes h)H(I-h\otimes h)$, which commutes with $S$, so it acts on $h^\perp$ as a multiple of the identity (Schur; $O(N-1)$ is irreducible on $\mathbb R^{N-1}$ for $N-1\ge2$, and for $N=2$, $h^\perp$ is a line); $C^{(j-1)}$ is a symmetric covariance of the same symmetry class, so it commutes with $S$ and is block diagonal in $h\oplus h^\perp$ with the scalar blocks $C_{lg}$, $C_{tr}$. (3) $G^{(j)}(x,x')=\sum_{y,y'}H(x,y)C(y,y')H(x',y')^\top$: by (1), $h^\top G^{(j)}=0$, and $G^{(j)}h=0$ because $H(x',y')^\top h=(h^\top H(x',y'))^\top=0$; by (2) the remaining block is the product of the three scalar kernels times $I-h\otimes h$. (4) is the dictionary of `CORRELATIONS.md` §2.1, whose derivation (the recursion for $b_j$, the closed form, the composition of minimizers) is proved there in plain units. $\square$

Item (1) is the exact content of "$H_{j,11}=0$ at $\lambda=\infty$" (P9 (4.12) with $\lambda_j^{-1}=0$); in particular the second term of (4.12) and the longitudinal covariance $C_{lg}$ never enter, and P9's bound $c\beta^{-1}\lambda^{-2}(1+|x|)^{-(d+2)}$ for $C_{lg}$ is replaced by "$=0$". The longitudinal function is then made of remainders only: $G_{lg}=\mathrm{tr}[R_k(h,h)\,h\otimes h]$ plus the last-step terms (§5).

**Exact form of $G_k(h,h)$ at $\lambda=\infty$.** By (2.5), Lemma 2.1 and $\psi^{(j)}_k(h,h)=h$,
$$G_k(x,x';h,h)=m_k(x)m_k(x')\sum_{j=0}^{k-1}(\beta\gamma_j)^{-1}T_j^{\ell,\nu\delta_j}(x,x')\,(I-h\otimes h)+R_k(x,x';h,h),\tag{2.6}$$
$$G_{tr}=\tfrac1{N-1}\mathrm{tr}\big[G_k(I-h\otimes h)\big],\qquad G_{lg}=\mathrm{tr}\big[G_k\,h\otimes h\big]=\mathrm{tr}\big[R_k\,h\otimes h\big],\tag{2.7}$$
the second form of (2.7) being P9 (4.11). Similarly $M_k(x;h,h)=m_k(x)h$ (P9 (4.10), from $\varphi_k(\cdot;h,h)=h$, (2.1) and $\psi^{(j)}_k(h,h)=h$).

### 2.3 Consistency with the first-order class and consequences

**Lemma 2.2 (dictionary with (H.7) and with Root-F; proved).** Define $\mathscr M^{(j)}(x;\psi_j,h):=\beta_{j-1}^{-1/2}\big(M^{(j)}(x;\psi_j,h)-\mu_j(x)\varphi_j(x;\psi_j,h)\big)$. Then $\mathscr F_k=\langle g,\varphi_k\rangle+\sum_j\langle g,\mathscr M^{(j)}(\psi^{(j)}_k,h,0)\rangle+O(g^2)$ is the first-order part of (H.7) if and only if (2.4) holds. If $\rho_0\ge\gamma-\alpha_1$ (E7), the terms $\mathscr M^{(j)}(x,X)$ satisfy the (H.7) bound $c_9\xi_j^{\frac{d-2}2+\gamma-\alpha_1}e^{-\kappa d_j(X)}$ with $c_9=\beta^{-1/4}$ for $\beta\ge\beta_0$.

*Proof.* The background identity $\varphi_k(\psi_k;h,a_k,\nu_k)=\varphi_j(\psi^{(j)}_k;h,a_j,\nu_j)$ (composition of the connecting problem, P1 (2.6)–(2.14); `BACKGROUND.md` §6) gives $m_k\varphi_k=\varphi_k-\sum_{j\le k}\beta_{j-1}^{-1/2}\mu_j\varphi_j(\psi^{(j)}_k)$, hence (2.4) is the displayed $M_k$ of (H.7). For the bound: $|\varphi_j(x,X;\cdot)|\le Ce^{-\kappa d_j(X)}$ (P3 localization of the background, $C$ depending on constants before $\beta$) and $\beta_{j-1}^{-1/2}\le\sqrt2\beta^{-1/2}\xi_j^{(d-2)/2}$ give $|\mathscr M^{(j)}(x,X)|\le C'\beta^{-1+\rho_1}\xi_j^{\frac{d-2}2+\rho_0}e^{-\kappa d_j(X)}$, which is $\le\beta^{-1/4}\xi_j^{\frac{d-2}2+\gamma-\alpha_1}e^{-\kappa d_j(X)}$ if $\rho_0\ge\gamma-\alpha_1$ and $\beta^{-3/4+\rho_1}C'\le1$. $\square$

So C-1a is a *refinement* of (H.7) (stronger in $\beta$: $\beta^{-1+\rho_1}$ against $\beta^{-1/4}$), not a competing class; Def-6's (H.7) becomes a corollary of (O2) for the $g=0$ part, and the $g$-dependence of $\mathscr M^{(j)}(x;\psi,h,g)$ beyond first order is carried by $R^{ij}$ and by the inherited packages of §3.2. Root-F's first-order terms $T_j(x,X;0)$ are $\sum$ of the $\mathscr M^{(j)}$ and the reduced-symmetry pieces of P7 (4.17); this identification belongs to LF-8/`POLYMER.md` §4.4 and is not used below.

**Lemma 2.3 (sums; proved).** Assume (O1)–(O3), $\beta\ge\beta_0$. Then for all $x,x'$ (sup norm distance $|x-x'|$):
(a) $|m_k(x)-1|\le C\beta^{-1+\rho_1}$ and $|m_k|\le2$;
(b) $\sum_{i\le j\le k}\beta_{i-1}^{-1}\sum_{X\ni x,x'}|R^{ij}(x,x';X;\psi,h)|\le C\beta^{-3/2+\rho_1}(1+|x-x'|)^{-(d-2+\rho_0)}e^{-\delta_0\sqrt\nu|x-x'|/L^2}$, with the mass factor valid when $L^k\le L^2/\sqrt\nu$ (i.e. $k\le J$).

*Proof.* (a) $\beta_{j-1}^{-1/2}\le\sqrt2\beta^{-1/2}L^{-(j-1)(d-2)/2}$ (from $|\log\gamma_j|\le\epsilon\le\frac1{20}$, P4 (5.32)), so $|m_k-1|\le\sqrt2\beta^{-1+\rho_1}L^{(d-2)/2}\sum_{j\ge1}L^{-j(\frac{d-2}2+\rho_0)}$. (b) $\sum_{X\ni x,x'}e^{-\kappa d_j(X)}\le K_0^{\rm O}$ (P5 (1.35)); $\beta_{i-1}^{-1}\le2\beta^{-1}L^{-(i-1)(d-2)}$; $\sum_{j\ge i}L^{-j\rho_0}\le L^{-i\rho_0}/(1-L^{-\rho_0})$; hence the sum is $\le C\beta^{-3/2+\rho_1}\sum_{i\le k}L^{-i(d-2+\rho_0)}e^{-\delta_0L^{-i}|x-x'|}$ (here $\ell^1\ge$ sup norm), and Lemma 1.3 of `CORRELATIONS.md` ($\sigma=d-2+\rho_0$, after splitting the exponent into two halves and using $L^{-i}\ge\sqrt\nu/L^2$ for $i\le k\le J$) gives the claim. $\square$

(b) is P9 (2.19)–(2.20), with the exponent $-\frac32+\rho_1$ of (2.20) confirmed.

### 2.4 What this adds to Def-6 and Def-7

The additions to the class, as statements (`SMALLFIELD.md` §6.2 X1 made precise):
- **A1** the data (O1)–(O3) and the identification (O4), a conjunction of clauses on the same representation (no new representation);
- **A2** the constants of §1.3 (no new freedom: all fixed by Lemma 1.1);
- **A3** (CONT) and (TORUS) of (O5) (X6, X7);
- **A4** nothing for the large-field part of Def-7 *except* that its $g$-dependent components (D1)'s $\mathcal R^{(k)}$, (D7)'s $\mathcal B^{(k)}$ and the output of LF-4 are analytic in $g$ on $\|g\|_{\ell^1}<1$ with sup bounds (they are already so in P5 H4, H7; §4).

Def-6 is a predicate on $(\psi$-functions$)$; A1 is an extra conjunct. The $O(N)$ covariance of $R^{ij}$ is the *tensor* covariance, which for $M^{(j)}$ is the vector covariance already in (H.7).


---

## 3. Preservation under one small-field step (brief item 2; X1–X7)

### 3.1 Statement

**Theorem 3.1 (X1–X7 as one statement; sketched, with all exponent bookkeeping proved).** Let $k<k_f$, $\beta\ge\beta_0$, and let $\rho_k\in\mathbb R^{\rm sf}_k$ (or its large-field extension, §4) carry an observable layer $\mathcal O_k$ with the constants of Lemma 1.1. Then $\rho_{k+1}=\chi_{k+1}S^{(k)}T^{(k)}\rho_k\in\mathbb R^{\rm sf}_{k+1}$ (I-9) and carries a layer $\mathcal O_{k+1}$ in which $\mu_j,M^{(j)},R^{ij}$ ($j\le k$) are the same functions of $\psi_j$ as in $\mathcal O_k$ (evaluated at $\psi^{(j)}_{k+1}$), and the new objects $\mu_{k+1}$, $M^{(k+1)}$, $R^{i,k+1}$ ($1\le i\le k+1$) are given by (3.1)–(3.6) below and satisfy (O1)–(O3). (CONT) and (TORUS) are propagated.

*Dictionary of the pieces* (P9 (3.1)–(3.10), (3.42)–(3.49)). Let $\langle\cdot\rangle$ be the normalized fluctuation measure of the step at $g=0$ (it contains $\chi^{(k)}$, $e^{-\beta_kV_{\rm eff}}$, $\delta\mathscr E_k$, the $g=0$ parts of $\mathcal R^{(k)}$ and $\mathcal B''^{(k)}$), $\psi'$ the fluctuation field with $\langle\psi'\psi'^\top\rangle_0=C^{(k)}$, and
$$\delta\varphi_k(x):=\varphi_k\big(x;\psi^{(k)}(\theta)+\beta_k^{-1/2}\psi'\big)-\varphi_k\big(x;\psi^{(k)}(\theta)\big),\qquad \delta M^{(j)}(x):=M^{(j)}\big(x;\psi^{(j)}_k(\psi^{(k)}(\theta)+\beta_k^{-1/2}\psi')\big)-M^{(j)}\big(x;\psi^{(j)}_k(\psi^{(k)}(\theta))\big),$$
$\delta G^{(j)},\delta R^{ij}$ likewise. Expanding $\log\langle e^{\delta\mathscr F_k(g)}\rangle$ to second order in $g$ gives the first-order part $\langle\delta M_k\rangle$, $\delta M_k:=m_k\delta\varphi_k+\sum_{j\le k}\beta_{j-1}^{-1/2}\delta M^{(j)}$, and the second-order part $\langle\delta G_k\rangle+\langle\delta M_k;\delta M_k\rangle^T$ (the truncated expectation), which P9 (3.3) splits as
$$\langle\delta G_k\rangle+\langle\delta M_k;\delta M_k\rangle^T=\beta_k^{-1}m_kG^{(k+1)}m_k+\sum_{i=1}^{k+1}\beta_{i-1}^{-1}R_0^{i,k+1},\tag{3.1}$$
$R_0^{i,k+1}=R_1^{i,k+1}+R_2^{i,k+1}$ ($i\le k$): $R_1^{i,k+1}=m_k\langle\delta G^{(i)}\rangle m_k$, $R_2^{i,k+1}=\sum_{j\ge i}\langle\delta R^{ij}\rangle$ (P9 (3.5)–(3.6)); $R_0^{k+1,k+1}=R_1+R_2+R_3$ with $R_1=-m_kG^{(k+1)}m_k+\beta_k\langle m_k\delta\varphi_k;\delta\varphi_km_k\rangle^T$, $R_2=2\beta_k\langle m_k\delta\varphi_k;\sum_j\beta_{j-1}^{-1/2}\delta M^{(j)}\rangle^T$, $R_3=\beta_k\sum_{i,j}\beta_{i-1}^{-1/2}\beta_{j-1}^{-1/2}\langle\delta M^{(i)};\delta M^{(j)}\rangle^T$ (P9 (3.7)–(3.10)). The renormalization (rescaling $\theta=z_{k+1}\psi_{k+1}$ and the shifts $\delta\varphi_{k+1},\delta\psi^{(j)}_{k+1}$ of the background, P9 (3.43)) produces the unnormalized $M_u^{(k+1)}$, (3.44), and the second-order package (3.45); the normalization step is
$$M_u^{(k+1)}(x;h,h)=:\mu_{k+1}(x)\,h,\qquad M^{(k+1)}:=M_u^{(k+1)}-\mu_{k+1}\varphi_{k+1},\tag{3.2}$$
and the second-order kernel is brought to the form (2.5) by replacing $\sum_{j\le k+1}\beta_{j-1}^{-1}m_kG^{(j)}m_k$ (P9 (3.49)) by $C_{k+1}$ plus
$$-\sum_{j\le k+1}\beta_{j-1}^{-1}\big[\beta_k^{-1/2}\mu_{k+1}G^{(j)}m_k+m_kG^{(j)}\beta_k^{-1/2}\mu_{k+1}+\beta_k^{-1}\mu_{k+1}G^{(j)}\mu_{k+1}\big],\tag{3.3}$$
whose $j$-th term is moved into $\beta_{j-1}^{-1}R^{j,k+1}$.

### 3.2 Inherited packages and the Cauchy lemma

P5's output of the step contains, besides $\mathscr F_{k+1,0}$, the packages $\mathcal R'^{(k+1)}_n$, $\mathcal B'^{(k+1)}$, $\mathcal B''^{(k+1)}$ and the $g$-dependent part of the large-field renormalization $\mathcal R^{(k)}$. P9 does not analyze their $g$-structure: it uses only that they are analytic in $g$ on $\|g\|_{\ell^1}<1$ with bounds $\beta_k^{-n-1}e^{-\kappa d}$ (H4) resp. $B_0e^{-\kappa d}$ (H7), and differentiates (P9 (3.42), (3.44)–(3.45): $M_{\mathcal R}=\partial_g\mathcal R_0^{(k+1)}$, $R_{\mathcal R}=\beta_k\partial_g^2\mathcal R_0^{(k+1)}$; bounds p. 513–514).

**Lemma 3.2 (Cauchy; proved).** Let $a(Y;g)$ be analytic on $\{\|g\|_{\ell^1}<1\}$ (complex $g\in\mathbb C^{\mathbb T\times N}$), depend on $g$ only through $g|_Y$, with $\sup|a(Y;g)|\le B_Y$. Then $\partial_{g_i(x)}a(Y;0)=0$ unless $x\in Y$, $|\partial_{g_i(x)}a(Y;0)|\le2B_Y$, and $|\partial_{g_i(x)}\partial_{g_k(y)}a(Y;0)|\le32B_Y$ (zero unless $x,y\in Y$).
*Proof.* Along $g=\zeta e_i\delta_x$ the function $\zeta\mapsto a(Y;g)$ is analytic for $|\zeta|<1$ and bounded by $B_Y$; the Cauchy estimate at radius $\frac12$ gives $|\partial a|\le2B_Y$ and $|\partial^2_{\zeta}a|\le2\cdot4B_Y=8B_Y$. For the mixed derivative put $u=e_i\delta_x+e_k\delta_y$, $\|u\|_{\ell^1}=2$; $\zeta\mapsto a(Y;\zeta u)$ is analytic for $|\zeta|<\frac12$, so by Cauchy at radius $\frac14$ its second derivative at $0$ is $\le2\cdot16B_Y=32B_Y$; by polarization $\partial_x\partial_ya=\frac12(\partial_u^2a-\partial_x^2a-\partial_y^2a)$, which gives $\le\frac12(32+8+8)B_Y=24B_Y$. (For $x=y$ the pure second derivative is $\le8B_Y$.) $\square$

Applied to $\mathcal R^{(k)}_n(X;\cdot)$ with $|\mathcal R^{(k)}_n(X)|\le\beta_k^{-n-1}e^{-\kappa d_k(X)}$, $n\ge1$: $|M_{\mathcal R}(x,Y)|\le2\beta_k^{-2}e^{-\kappa d}$ and $|R_{\mathcal R}(x,x',Y)|=\beta_k|\partial_g^2\mathcal R|\le32\beta_k^{-1}e^{-\kappa d}$. With $\beta_k^{-1}\le2\beta^{-1}L^{d-2}\xi_{k+1}^{d-2}$ these are smaller than the bounds P9 prints on pp. 513–514 ($\beta_k^{1/2}|M_{\mathcal R}|<2\beta_k^{-1}$, $|R_{\mathcal R}|<4\beta_k^{-1/2}$ both at $n=1$ with a cruder size), so P9's use is covered; the decay in $|x-x'|$ of $R_{\mathcal R}$ comes from $Y\ni x,x'$ as in §3.6.

### 3.3 The marked expansion (X2)

**Proposition 3.3 (P9 Prop 3.1 in the form used; reduced to PE-M).** Let $X_1,X_2\in\mathcal D_j$ and $F_s(X_s;\cdot)$ analytic on the composite domain $\psi^{(j_s)}_k(\psi^{(k)}(\theta)+z\psi')$, $|z|<r_0$, with $|F_s|\le F_{0,s}e^{-(\kappa-1)d_{j_s}(X_s)}$; $\langle\cdot\rangle_\sigma$ the fluctuation expectation extended analytically in the coupling $\beta_k^{-1/2}\sigma$, $|\sigma|<r_1=cc_1\beta_k^{1/2}/p_1(\beta_k)$. Then
$\langle F_1\rangle_\sigma=\sum_{Y\in\mathcal D_{k+1},Y\supset X_1}F_1(X_1,Y;\cdot)$ with $|F_1(X_1,Y)|\le CF_{0,1}e^{-\kappa_0d_{j_1}(X_1)}e^{-2\kappa d_{k+1}(Y)}$ (P9 (3.11)–(3.12)), and
$\langle F_1;F_2\rangle^T_\sigma=\sum_{Y\supset X_1\cup X_2}F(X_1,X_2,Y;\cdot)$ with $|F(X_1,X_2,Y)|\le CF_{0,1}F_{0,2}e^{-\kappa_0d_{j_1}(X_1)}e^{-\kappa_0d_{j_2}(X_2)}e^{-2\kappa d_{k+1}(Y)}$ (P9 (3.13)).
*Status: cited / reduced.* The one-function part is P5 Prop 3.1–3.4 and `POLYMER.md` U4/PE-M. For (3.13): write $\Xi(\lambda_1,\lambda_2)=\int e^{-\frac12|\psi|^2}\chi\,\exp[\sum_Y\mathcal U(Y;\psi)+\lambda_1F_1+\lambda_2F_2]$; the activity of a polymer depends on $\lambda_s$ only if it contains $X_s$; then $\langle F_1;F_2\rangle^T=\partial_{\lambda_1}\partial_{\lambda_2}\log\Xi|_0=\sum_Y\partial_{\lambda_1}\partial_{\lambda_2}P(Y)$ (PE-M (M3)), supported on connected $Y\supset X_1\cup X_2$ (M1), and $|\partial_{\lambda_1}\partial_{\lambda_2}P(Y)|\le r_1^{-1}r_2^{-1}\sup|P|$ (M2) with $r_s=\theta F_{0,s}^{-1}e^{\kappa_0d(X_s)}$. This repairs the gap in P9 p. 503–504 (the product $\langle F_1\rangle\langle F_2\rangle$ also contains product terms with touching $Y_1,Y_2$, which cannot be cancelled by factorization alone; `POLYMER.md` §0 finding (iii)).
*Requirements on the instance (R-M1…R-M3).* (R-M1) The weight must have the product-measure form (H-MY): the characteristic functions $\chi^{(k)}$ factor over sites, and the interaction is a sum of localized terms $\mathcal U(Y;\psi)$ with the polymer bound. (R-M2) The polymers are connected *modulo the hole* $\Omega_{k+1}^c$ in the presence of large-field regions (`POLYMER.md` §3.6: tree-length size, volume weights), so the proposition is needed in the $\mathcal D_{k+1}(\bmod\Omega^c)$ form; P9 states it for $\mathcal D_{k+1}$ only. (R-M3) The weight includes the $g=0$ parts of $\mathcal R^{(k)}$ and $\mathcal B''^{(k)}$; they are $O(\beta_k^{-2})$ resp. $B_0$-bounded localized terms and enter $\mathcal U$ without changing its structure. **Status of Proposition 3.3 (precise).** *Proved:* the algebra $\langle F_1;F_2\rangle^T=\sum_Y\partial_{\lambda_1}\partial_{\lambda_2}P(Y)$ and (M1)–(M3) for a weight of the form (H-MY). *Cited:* the single-function case (P5/P6, `POLYMER.md` U4). *Sketched / open (OBSR O-09, the main risk of this document):* (R-M1) the covariance $C^{(k)}=(\Delta^{(k)}_{tr}+aL^{-2}Q^*Q)^{-1}$ is non-local, so the product form holds only after the off-diagonal part of $C^{-1}$ is expanded into polymer couplings (P6 (4.35)–(4.42)); (M1) survives only if that expansion is done *before* $\lambda_1,\lambda_2$ are introduced and its polymers are counted in $\mathcal U$ (they carry no $\lambda$); this must be checked in P6 (4.35)–(4.42). (R-M2) with holes the measure lives on $\Omega^c$, the covariance is a restriction, and its decay across the hole boundary has to be treated as the boundary-term role of $\mathcal B$ inside the same argument. Until both are checked, everything downstream of Proposition 3.3 (the rows $R_1^{k+1,k+1},R_2,R_3$ and T1, T2 of §3.5–3.6) is **sketched at the level of the expansion, proved at the level of exponents**.

### 3.4 The improved bound (Lemma 2 of P9)

**Lemma 3.4 (P9 (2.21)–(2.22)).** For $\sigma\le\sigma_2$, $\varepsilon\le\varepsilon_0=\varepsilon_{j+1}$, on $\Psi^c_j(X;\sigma,\varepsilon)$:
$$|M^{(j)}(x,X;\psi_j,h)-M^{(j)}(x,X;h,h)|\le C\beta^{-1/2+\rho_1}\xi_j^{\rho_0}\frac{\sigma\varepsilon}{\varepsilon_j}e^{-(\kappa-1)d_j(X)},\qquad |M^{(j)}(x;\psi_j,h)|\le C\beta^{-1/2+\rho_1}\xi_j^{\rho_0}\frac{\sigma\varepsilon}{\varepsilon_j}.\tag{3.4}$$
*Status.* The first bound is P1 technology (Lemmas 2.3, 2.4, 2.7–2.9 and (2.87)–(2.103) of P1; P9 pp. 498–501: split $\psi_j=\psi_j(y)+\delta_y$, treat $\delta_y$ by a Cauchy estimate for small $X$ ($d_j(X)\le d(\rho)$) and by the exponential for large $X$, treat the constant part by $O(N)$ covariance and the expansion in $(u-1,v,w^2)$); **sketched**. The second bound **follows from the first and (2.1)** (proved): $M^{(j)}(x;\psi_j,h)=\sum_X[M^{(j)}(x,X;\psi_j,h)-M^{(j)}(x,X;h,h)]$ since $\sum_XM^{(j)}(x,X;h,h)=0$, and $\sum_{X\ni x}e^{-(\kappa-1)d_j(X)}\le K_0^{\rm O}$. At $\lambda=\infty$ the constant configuration $\psi_j(y)$ lies on the sphere and the dependence on $h$ is through $b=\nu_jh$ (`SMALLFIELD.md` §3.5); the expansion variables reduce to $(|\psi_j|^2-1,\ \psi_0\cdot b,\ |b|^2-(\psi_0\cdot b)^2)$ and the constant part is $O(\nu_j+||\psi_j|^2-1|)$ by (2.7) at $(e_1,\nu_je_1)$ and the Lipschitz bound in $b$. **UNCERTAIN:** the argument at $\lambda=\infty$ in the $\nu$-free regime $k\le k_0$ (where the domain has no $|\psi-h|$ condition) is not written in P9 or P1; it must be checked in the instance (it is the $b$-form of (H.5), `SMALLFIELD.md` §3.5, and rests on $\nu_j\le\beta_j^{-1}$ there).

### 3.5 First-order terms (proved: exponent bookkeeping from Prop 3.3, Lemma 3.4)

Notation for conversions, all valid for $\beta\ge\beta_0$, $j\le k$, $\eta=L^{-k}$, $\xi_{k+1}=L^{-1}\eta$:
(B1) $\beta_k^{-1/2}\le\sqrt2\beta^{-1/2}\eta^{(d-2)/2}$, $\beta_{j-1}^{-1/2}\le\sqrt2L^{(d-2)/2}\beta^{-1/2}\xi_j^{(d-2)/2}$;
(B2) $\varepsilon_j=\alpha_{0,j}\xi_j^\alpha$, $\alpha=\frac{d-2}2-\gamma$, so $\varepsilon_k/\varepsilon_j\le2(L^j\eta)^\alpha$ and $\varepsilon_{k+1}^{-1}\le C\xi_{k+1}^{-\alpha}$;
(B3) $p_1(\beta_k)^s\le C\beta_k^{s\rho_2}\le C\beta^{s\rho_2}\eta^{-s(d-2)\rho_2}$ (from $(\log\beta_k)^{p_1}\le C\beta_k^{\rho_2}$ and $\beta_k\le2\beta L^{k(d-2)}$; this is how P9's $\eta^{-(d-2)\rho_2}$ arises);
(B4) the radii of the Cauchy integrals in $\sigma$ (the coupling) and $z$ (the field) are $r_1=cc_1\beta_k^{1/2}/p_1$ and $r_0\in\{cc_1/p_1,\ c\alpha\varepsilon_{j+1}/p_1,\ c\alpha\varepsilon_{k+1}/p_1\}$ (P9 p. 503, three cases), and $\frac{r_1}{(r_1-1)^2}\le\frac4{r_1}$ for $r_1\ge2$.

**T1 (the term $m_k\langle\delta\varphi_k\rangle$).** $\langle\delta\varphi_k\rangle=\beta_k^{-1/2}\langle\Gamma_k(x;\beta_k^{-1/2}\psi')\psi'\rangle$ and, since $\langle\psi'\rangle_0=0$, a Taylor expansion in the coupling to first order (the "$\sigma$-trick", P9 (3.14)–(3.15)) gives $m_k\langle\delta\varphi_k\rangle=\beta_k^{-1/2}\sum_{Y\ni x}\Phi_k(x,Y)$ with
$$|\Phi_k|\le\frac4{r_1}\cdot\frac1{r_0}\cdot C\,e^{-2\kappa d_{k+1}(Y)}\le C\,p_1^2\beta_k^{-1/2}e^{-2\kappa d_{k+1}(Y)}\le C\beta^{-1/2+2\rho_2}\eta^{\frac{d-2}2-2(d-2)\rho_2}e^{-2\kappa d_{k+1}(Y)}\tag{3.5}$$
(P9 (3.17)); this is $\le\frac12\beta^{-1/2+\rho_1}\xi_{k+1}^{\rho_0}$ if $\rho_1\ge3\rho_2$ (here $\rho_1\ge4\rho_2$ holds anyway), $\rho_0\le\frac{d-2}2-2(d-2)\rho_2$ and $C\beta^{-\rho_2}\le\frac12$ (E1, E2, E8).

**T2 (the terms $\beta_{j-1}^{-1/2}\langle\delta M^{(j)}\rangle$).** Use Prop 3.3 with $F=M^{(j)}(x,X;\cdot)$ on $\Psi^c_j(C_0L^j\eta,\varepsilon_k)$, so Lemma 3.4 gives $F_0=C\beta^{-1/2+\rho_1}\xi_j^{\rho_0}(L^j\eta)^{\frac d2-\gamma}$ (here $\sigma\varepsilon_k/\varepsilon_j=C_0(L^j\eta)^{1+\alpha}$, $1+\alpha=\frac d2-\gamma$); with $r_0=c\alpha\varepsilon_{k+1}/p_1$ and (B1)–(B3), each $(X,Y)$ term of $\beta_{j-1}^{-1/2}\delta M^{(j)}$ is bounded by
$$C\beta^{-1+\rho_1+\rho_2}\,\xi_j^{\rho_0+\gamma-1}\eta^{1-(d-2)\rho_2}e^{-\kappa_0d_j(X)}e^{-2\kappa d_{k+1}(Y)}\tag{3.6}$$
(exponent of $\eta$: $(\frac d2-\gamma)-\alpha-(d-2)\rho_2=1-(d-2)\rho_2$; exponent of $\xi_j$: $\rho_0-(\frac d2-\gamma)+\frac{d-2}2$). Since $\eta\le\xi_j$ and $1-\rho_0-(d-2)\rho_2\ge0$ (E3), $\xi_j^{\rho_0+\gamma-1}\eta^{1-(d-2)\rho_2}\le\xi_j^{\gamma-(d-2)\rho_2}\eta^{\rho_0}$, and $\sum_{j\ge1}\xi_j^{\gamma-(d-2)\rho_2}<\infty$ (E4), so after resumming over $X$ with $x\in X\subset Y$ the new contribution is $\le C\beta^{-1+\rho_1+\rho_2}\xi_{k+1}^{\rho_0}e^{-2\kappa d_{k+1}(Y)}$ (P9 (3.23)); this is smaller than $\beta^{-1/2+\rho_1}\xi_{k+1}^{\rho_0}$ by $\beta^{-1/2+\rho_2}$. *This is the only place where the irrelevance gap and the normalization (2.7) are used, and the only place where $\rho_0>0$ is created* (X3): the positive power $\eta^{\rho_0}$ comes from $\sigma\varepsilon_k/\varepsilon_j\simeq(L^j\eta)^{d/2-\gamma}$, one power of $\eta$ better than the canonical one.

### 3.6 Second-order terms (proved: exponents; Lemma 3.5 proved)

**Lemma 3.5 (the Gaussian main term; proved).** At $\sigma=0$ the measure is the Gaussian $\mu_0$ with covariance $C^{(k)}$, $\Gamma_k(x;0)=H_k(x)$, and
$$\beta_k\langle\Gamma_k(x;0)\psi';\Gamma_k(x';0)\psi'\rangle_0^T\beta_k^{-1}=H_kC^{(k)}H_k^*(x,x')=G^{(k+1)}(x,x'),$$
so $R_1^{k+1,k+1}$ is the part of $\beta_k\langle m_k\delta\varphi_k;\delta\varphi_km_k\rangle^T$ of first order in $\sigma$ (P9 (3.32)–(3.34)). *Proof.* (3.32) writes $\langle\delta\varphi_k(x);\delta\varphi_k(x')\rangle^T=\beta_k^{-1}\langle\Gamma(x;\beta_k^{-1/2}\psi')\psi';\Gamma(x';\beta_k^{-1/2}\psi')\psi'\rangle^T$ (the product of expectations is subtracted by truncation), which is an analytic function of the coupling; at coupling $0$ the truncated covariance of two linear functions of a Gaussian vector is the bilinear form of its covariance. $\square$ (This is the only exact identification in the step: it produces the new summand $\beta_k^{-1}m_kG^{(k+1)}m_k$ of $C_{k+1}$.)

The remaining terms (P9 (3.25)–(3.41)); each row is a recomputation with (B1)–(B4):

| term | bound of one $(X,Y)$ term | needs |
|---|---|---|
| $R_1^{i,k+1}$, $i\le k$ ($\delta G^{(i)}$, explicit, one coupling-Cauchy only) | $C\beta^{-1/2+\rho_2}\eta^{\frac{d-2}2-(d-2)\rho_2}e^{-\delta_0L^{-i}|x-x'|_1}e^{-2\kappa d_{k+1}(Y)}$ (P9 (3.28) prints $\beta^{-1/2-\rho_2}$; the computation $\frac4{r_1}\sup|G|$ with $r_1^{-1}\propto p_1\beta_k^{-1/2}$ gives $+\rho_2$: misprint, harmless since $\rho_1\ge4\rho_2$) | (3.25) |
| $R_2^{i,k+1}=\sum_{j\ge i}\langle\delta R^{ij}\rangle$ | $C\beta^{-1+\rho_1+\rho_2}\xi_j^{\rho_0-\frac{d-2}2+\gamma}\eta^{\frac{d-2}2-(d-2)\rho_2}$, then $\le C\beta^{-1+\rho_1+\rho_2}\xi_j^{\gamma-(d-2)\rho_2}\eta^{\rho_0}$ if $\rho_0\le\frac{d-2}2-(d-2)\rho_2$; sum over $j\ge i$ is $\le C\xi_i^{\gamma-(d-2)\rho_2}$ | (E2), (E4) |
| $R_1^{k+1,k+1}$ (remainder of Lemma 3.5; two $z$-Cauchy, one $\sigma$) | $\frac4{r_1}r_0^{-2}Ce^{-2\kappa d}\le C\beta^{-1/2+3\rho_2}\eta^{\frac{d-2}2-3(d-2)\rho_2}e^{-2\kappa d_{k+1}(Y)}$ (3.37) | (E1), (E2) |
| $R_2^{k+1,k+1}$ | $C\beta^{-1+\rho_1+2\rho_2}\xi_j^{\rho_0+\gamma-1}\eta^{1-2(d-2)\rho_2}$ per $j$, then as T2 (3.39) | (E3), (E4); $C\beta^{-1/2+2\rho_2}\le\frac12$ |
| $R_3^{k+1,k+1}$ | $C\beta^{-2+2\rho_1+2\rho_2}\xi_i^{\rho_0+\gamma-1}\xi_j^{\rho_0+\gamma-1}\eta^{2-2(d-2)\rho_2}$ (3.41) | as T2 |

In every row the decay in $|x-x'|$ is produced from the polymer: $Y\ni x,x'$ and $Md_{k+1}(Y)+2dLM\ge L^{-(k+1)}|x-x'|_1$ give $e^{-2\kappa d_{k+1}(Y)}\le e^{2dL\kappa}e^{-\delta_0L^{-(k+1)}|x-x'|_1}e^{-\kappa d_{k+1}(Y)}$ with $\delta_0=\kappa/M$ (P9 p. 509: this is the only place where $M$ enters the exponent). For $i\le k$ the decay $e^{-\delta_0L^{-i}|x-x'|_1}$ is inherited from (3.25) or (2.2). All rows are smaller than the requirement $\beta^{-1/2+\rho_1}\xi_{k+1}^{\rho_0}$ for $\beta\ge\beta_0$ except the row $R_1^{k+1,k+1}$, which fixes (E1), (E2).

### 3.7 Renormalization package and the scalar $\mu_{k+1}$ (X3)

*Shifts.* P4 (4.7)–(4.11) give $|\delta\varphi_{k+1}|\le C\beta_{k+1}^{-1}\varepsilon_{k+1}^{-1}$, $|\delta\psi^{(j)}_{k+1}|\le C\beta_{k+1}^{-1}\varepsilon_{k+1}^{-1}$ (the renormalization constants are $\le\frac14c_8L^{-2\gamma(k+1)}\beta_{k+1}$, P4 (1.10)). Then, with Cauchy radius $\varepsilon_{j+1}$:
- $\beta_k^{1/2}m_k\delta\varphi_{k+1}$: $\le C\beta^{-1/2}\xi_{k+1}^\gamma$ (since $\beta_k^{1/2}\beta_{k+1}^{-1}\varepsilon_{k+1}^{-1}\simeq\beta^{-1/2}\eta^{-(d-2)/2}\eta^{d-2}(L^{-1}\eta)^{-\alpha}$) — this requires $\rho_0\le\gamma$ (E5), the only use of (E5);
- the $M^{(j)}$-shift terms: $\le C\beta^{-3/2+\rho_1}\xi_{k+1}^{2\gamma}$ per $X$ (P9 p. 512);
- the $G^{(j)}$- and $R^{ij}$-shifts: $\beta_{j-1}^{-1}$ times a kernel bounded by $C\beta^{-1}\xi_{k+1}^{\gamma}$ with the decay $e^{-\delta_0L^{-j}|x-x'|_1}$ (P9 (3.47)–(3.48)): they are $\beta_{j-1}^{-1}R^{j,k+1}$-terms;
- $M_{\mathcal R}$, $R_{\mathcal R}$: Lemma 3.2.

*The scalar.* $\mu_{k+1}(x)h=M_u^{(k+1)}(x;h,h)$ is a sum over $Y\ni x$ of terms of (3.4)-type bounds (evaluated at $\theta=z_{k+1}h$, an interior point of the domain), so $|\mu_{k+1}(x)|\le K_0^{\rm O}\cdot C\max\{\beta^{-1/2+2\rho_2}\xi_{k+1}^{\frac{d-2}2-2(d-2)\rho_2},\ \beta^{-1+\rho_1+\rho_2}\xi_{k+1}^{\rho_0},\ \beta^{-1/2}\xi_{k+1}^{\gamma},\ \beta^{-3/2+\rho_1}\xi_{k+1}^{2\gamma},\ \beta^{-1}\xi_{k+1}^{d-2}\}\le\frac12\beta^{-1/2+\rho_1}\xi_{k+1}^{\rho_0}$ for $\beta\ge\beta_0$ (T1, T2, the two shifts, $M_{\mathcal R}$; (E1), (E2), (E5), (E8)). Then $\beta_k^{-1/2}|\mu_{k+1}|\le C\beta^{-1+\rho_1}\xi_{k+1}^{\frac{d-2}2+\rho_0}$ (P9 p. 514), so the terms (3.3) are $R^{j,k+1}$-terms: their kernels are $\le C\beta^{-1+\rho_1}\xi_{k+1}^{\frac{d-2}2+\rho_0}G_0e^{-\delta_0L^{-j}|x-x'|_1}\le\beta^{-1/2+\rho_1}\xi_{k+1}^{\rho_0}e^{-\delta_0L^{-j}|x-x'|_1}$. After (3.2), $\sum_YM^{(k+1)}(x,Y;h,h)=\mu_{k+1}h-\mu_{k+1}\varphi_{k+1}(x;h,h)=0$, i.e. (2.1) at level $k+1$. The localization of $\varphi_{k+1}(x;\cdot)$ (P3) provides the bound for $M^{(k+1)}(x,Y)$.

### 3.8 (CONT), torus independence, and the table X1–X7

**Lemma 3.6 (Tannery and Vitali; proved).** (a) If $a_j(\nu)\to a_j$ as $\nu\downarrow0$ for each $j$ and $|a_j(\nu)|\le b_j$, $\sum b_j<\infty$, then $\sum_ja_j(\nu)\to\sum_ja_j$ (Mathlib `tendsto_tsum_of_dominated_convergence`). (b) A uniformly bounded family of analytic functions on a connected polydisc that converges on an open subset converges locally uniformly on the whole polydisc (Vitali–Montel).

**(CONT) for the layer (X6; sketched).** Induction on $k$ for fixed $k$ as $\nu\downarrow0$ (so that $k<k_f(\nu)$). The step map is built from: the Gaussian objects ($H_k,C^{(k)},G^{(k+1)}$), analytic in the unit-lattice mass $\mu=\nu_kL^{-2k}\in[0,L^{-2k}]$ uniformly in the torus (`GREEN.md` G-5(b); `SMALLFIELD.md` §3.5); the localization expansions of Prop 3.3, whose polymer series converge absolutely with $\nu$-independent bounds, so by Lemma 3.6(a) the sums converge once each polymer term does; each polymer term is an analytic function of $(\psi,b=\nu h)$ and of the data, bounded uniformly in $\nu$ on a $\nu$-independent domain, so converges by Lemma 3.6(b) as soon as it converges on an open set, which holds by the induction hypothesis and the explicit formulas; the contractions defining $\xi^{(k)}(\nu)$ (Lemma 3.3 of `SMALLFIELD.md`); the normalizations $\mu_{k+1}(\nu;x)$ (continuous images). The evaluation point of the layer in §5 is $(\psi,b)=(h,\nu h)$, an interior point of the $\nu$-independent domain, so continuity of the functions gives continuity of $R^{ij}(x,x';h,h)(\nu)$ and $\mu_j(\nu;x)$ at $\nu=0$. **UNCERTAIN:** (i) that the *large-field* output at scale $k$ (the packages $\mathcal R''^{(k)}_m$, $\mathcal B^{(k)}$) is also continuous as $\nu\downarrow0$; this follows if no *definition* at scale $\le k$ uses $\hat k_f(\nu)$ (`LF-RECONSTRUCTION.md` §I.1.1: bookkeeping is a function of $\hat\lambda_j$ and $\hat k_f$; $\hat k_f$ enters the inequalities (H6$^\flat$) as the causal horizon, not the definition of the operations); this is Question 4 of `CORRELATIONS.md`, answered here as a *requirement* on LF-3/LF-4 (§4 (v)); (ii) the restriction that the point $(h,\nu h)$ lies in the common domain for the $\nu$-free backgrounds of Def-6.

**(TORUS) (X7).** The step maps families over tori to families over tori; a localized term for a non-winding polymer is a function of data in a ball of radius $O(ML^{k+1})$ around it, identical on all tori in which that ball does not wind (`POLYMER.md` §4.5; ER-010). The observable layer adds no new torus-dependent object: $\mu_j(x)$ is defined from the terms $M_u^{(j)}(x,Y;h,h)$ with $Y$ non-winding, and the winding terms enter the last-step remainder only.

| Item | Statement | Status |
|---|---|---|
| X1 class | §2.1, Lemma 2.1–2.3 | proved (structure) / definition |
| X2 preservation, Prop 3.1 | Prop 3.3, Lemma 3.4, §3.5–3.7 | exponents proved; Prop 3.3 reduced to PE-M (hole version needed); Lemma 3.4 cited (P1) |
| X3 normalization, $\mu_{k+1}$ | §3.7, (3.2) | proved given T1, T2, shifts |
| X4 Gaussian main term | Lemma 2.1, Lemma 3.5 | proved; requires free flow (i) (ruling) |
| X5 units | `CORRELATIONS.md` Q3 | open (seaturtle2) |
| X6 (CONT) | §3.8 | sketched |
| X7 torus independence | §3.8 | sketched (cited `POLYMER.md` §4.5) |

---

## 4. Preservation under $R$ and in the frozen regime (brief item 3)

### 4.1 What P9 assumes about large fields

P9 works on the whole lattice in §§2–3 ("in this and the next section it is enough to work with the function $\mathscr F_k$ defined on the whole lattice", p. 495): the restricted functions $\mathscr F_k(Z_k^c)$ of the representation (4.2) are determined by $\mathscr F_k$ (P5 (H.3)), and the step acts on $\mathscr F_k$ as in the small-field case, with the large-field regions entering only through the packages of §3.2. The assumptions actually used are:
- (L1) the representation (4.2) of $\rho_k$ with $\mathscr F_k(Z_k^c)$ the restriction of the whole-lattice function (P5 H1, H3);
- (L2) P5 H4: $\mathcal R_n^{(k)}(\psi,h,g)$, $1\le n\le m$, analytic in $g$ on $\|g\|_{\ell^1}<1$, jointly covariant $\mathcal R(R\psi,Rh,Rg)=\mathcal R(\psi,h,g)$, localized with $|\mathcal R_n^{(k)}(X)|\le\beta_k^{-n-1}e^{-\kappa d_k(X)}$;
- (L3) P5 H7: boundary terms $\mathcal B^{(k)}(X,\mathbb A_k;\psi,\psi',g)$ analytic in $g$ on $\|g\|_{\ell^1}<1$ with $B_0e^{-\kappa d_k(X\bmod\Omega_k^c)}$;
- (L4$'$) (replaces (L4) of version 1, which was false; P5 (1.21), audit P2-04; `LF-RECONSTRUCTION.md` Remark IV.4.5, Definition II.5.2) the large-field operators $\mathbb T_k$ depend on $g$ only through factors $e^{b}$ with $b$ local and analytic in $g$ on $\|g\|_{\ell^1}<1$, with the bounds (S0), (1.26) uniform on the complex polydisc; this $g$-dependence never enters $\mathscr F_k$ or the observable layer, and reaches $\log Z$ only through the boundary terms, the packages $\mathcal R''^{(j)}_m$ (inside $\mathcal R_n$, then $\mathscr E,\mathscr M$ after $m$ steps) and $\mathcal P^{(J)}$; their first and second $g$-derivatives are the *marked terms* obtained by differentiating the factors $e^b$ inside the activities, and are bounded by Lemma 3.2 from the sup bounds of the activities on the polydisc (differentiation of $e^b$ under the polymer expansion is the statement that the activity is analytic in $g$ with a sup bound, PE (c), (d));
- (L5) at the end, the polymer expansion with $g$-dependent activities (P9 (4.4)–(4.6)).

(L2)–(L3) are used only through their sup bounds on the whole $g$-polydisc and through Lemma 3.2; (L4$'$)–(L5) only in the last step (inside the activities of $\mathcal P^{(J)}$, which `LF-RECONSTRUCTION.md` Theorem IV.4.1 bounds on the whole polydisc; the proof of Theorem 5.2 is unchanged). P9 uses nothing of the operator bounds (P4)/(P5) of Def-7 (budget invariant (D6), (D5)) except through (L5), which is LF-8 and already part of the Root-F route. In particular **the observable layer is blind to the structure of the large-field regions**; it only needs that the *whole-lattice* step of §3 can be performed in their presence.

### 4.2 $R$ preserves the layer

**Proposition 4.1 (proved from LF-4 (a), (c); the requirements are on its proof).** Let $(\rho,\mathrm{rep})$ be as in LF-4 and $(\rho',\mathrm{rep}')$ its output. Then (i) $\int\rho'd\psi_k=\int\rho\,d\psi_k$ identically in $(h,g)$, so $\log Z(g)$ and all its $g$-derivatives are unchanged; (ii) the small-field data of $\mathrm{rep}'$ are those of $\mathrm{rep}$ except $\mathcal R^{(k)}_m\mapsto\mathcal R^{(k)}_m+\mathcal R''^{(k)}_m$; hence the observable layer $\mathcal O_k$ (a part of the small-field data) is unchanged, and (iii) (L2)–(L4) hold for $\mathrm{rep}'$ if $\mathcal R''^{(k)}_m$ has the properties of P5 H4 on the $g$-polydisc.

*Requirements for the proof of LF-4 (to be written in the reconstruction document and in the Lean statement):*

1. **$g$ is an analytic parameter, with a bounded factor.** For hard spins $|e^{\langle g,\varphi\rangle}|\le e^{\|{\rm Re}\,g\|_{\ell^1}}\le e$ pointwise for $\|g\|_{\ell^1}<1$ (complex $g$ included), and $\|g|_Z\|_{\ell^1}\le1$ for every window $Z$. Every estimate of P7 §§2–3 (the main-action cancellation, the refund route (M3), the activity lemma GAS) is an estimate of the modulus of an integrand, hence holds with an extra factor $\le e$ per window; this is an additive $1$ in an exponent whose margin is $C_R\hat\lambda^{2d+1}\ge C_R(\log\beta)^{2d+1}$ (ARCH §3.8), so it is absorbed in $C_R$. If any step uses positivity of the large-field density (partition-function ratios in the refund route) it needs $\mathrm{Re}\,e^{\langle g,\varphi\rangle}\ge e^{-1}\cos1$ on windows, a factor of the same type (OBSR O-08(ii)); `LF-RECONSTRUCTION.md` §II.6.5 item 1 states that the hard-spin factor enters $b_0$ with $|\langle g,\phi\rangle|\le1$.
2. **Joint covariance.** The coset average (M4) is taken on the *full* integrand (including $h$ and $g$), so for $S\in O(N)$ one has $\rho'(S\psi;Sh,Sg)=\rho'(\psi;h,g)$ (the coset of $S\psi_0$ is $S$ times the coset of $\psi_0$; the model density is invariant under the simultaneous rotation). **Closed in `LF-RECONSTRUCTION.md` Part III, Lemma III.9.6 (a), (c)** (coset average on the full integrand). This is the H4 symmetry of $\mathcal R''$; it is where $M_{\mathcal R}$ and $R_{\mathcal R}$ get the covariance used in (O2), (O3) and in Lemma 2.1.
3. **Locality in $g$.** $\mathcal R''^{(k)}_m(X;\cdot)$ and $\mathcal B^{(k)}(X;\cdot)$ depend on $g$ only through $g|_{\mathbb B(X)}$; otherwise Lemma 3.2 does not localize $\partial_{g(x)}$.
4. **Sup bounds on the whole polydisc for complex $g$.** The Mayer/polymer expansion (PE with complex activities, `POLYMER.md` §2) gives $\sup_{\|g\|<1}|\mathcal R''(X;g)|\le\beta_k^{-m-1}e^{-\kappa d_k(X)}$; real $g$ would not suffice for the Cauchy lemma.
5. **(CONT).** The data of $R^{(k)}$ at scale $k$ are analytic in $(\psi,b=\nu h)$ on $\nu$-independent domains, and no *definition* of an operation at scale $\le k$ uses the a priori horizon $\hat k_f(\nu)$ (`LF-RECONSTRUCTION.md` §I.1.1); $k_0(\nu)\to\infty$ as $\nu\downarrow0$, so for fixed $k$ the operation $R^{(k)}$ is applied for all small $\nu$.

(1) is the only one that is not already stated as part of H4/H7; (2)–(4) restate H4 for the output; (5) is new.

*After $m$ steps.* The reduced-symmetry pieces $\mathcal R_n$ lose one unit of $n$ per step and are absorbed after $m$ steps into $\mathscr M^{(j)}$ and $\mathscr E^{(j)}$ (P5 p. 491–492): their first and second $g$-derivatives then enter $M^{(j)}$, $R^{jj}$. Their size is $\beta_k^{-m-1}$, far below the layer bounds ($\beta_k^{-m-1}\le\beta^{-m-1}L^{-k(m+1)(d-2)}\le\beta^{-1/2+\rho_1}L^{-(k+m)\rho_0}$ for $m\ge1$), so absorption changes $\mu_{k+m}$ by a negligible amount and does not affect (2.1).

### 4.3 The frozen regime and the switch of conventions

For $k_0\le k<k_f$ there is no $R$ ($R^{(k)}=\mathrm{id}$); $\rho_k\in\mathcal R^\flat_k$ has the same small-field data with complete backgrounds ($\nu$-term included), threshold $A_2\hat\lambda_{k_0}^{p_2}\ge p_2(\beta_{k_0})$ and (H6$^\flat$). Theorem 3.1 holds verbatim on $\mathcal R^\flat_k$ under the same requirements, because the step uses the large-field part only through (L1)–(L4). Two points need care:

1. *The hole.* Large-field components persist, so the polymers of Prop 3.3 are connected modulo $\Omega^c_{k+1}$ (R-M2).
2. *The switch of backgrounds at $k_0$.* Def-6 uses $\nu$-free backgrounds for $k\le k_0$ (P5 (1.9); `SMALLFIELD.md` §1.6) and complete ones after. P9 writes $G_j=(-\Delta+a_jQ_j^*Q_j+v_j)^{-1}$ with the mass $v_j$ in all (4.12)–(4.17), i.e. it is silent about the switch. The Gaussian kernels $G^{(j)}$ of the layer are therefore massless for $j\le k_0$ (up to an index shift of one) and massive after; C-1*'s `mainTr` uses the masses $\nu\delta_j$ throughout. The two agree up to a remainder:

**Lemma 4.2 (mass reconciliation; proved from G-5(b)).** Let $j$ be such that $\beta_j\nu_j\le1$ (all $j\le k_0$), $\mu=\nu\delta_j$, so the unit-lattice mass is $\nu_j=\mu L^{2j}\le\beta_j^{-1}\le1$. Then
$$|T_j^{\ell,\mu}(x,y)-T_j^{\ell,0}(x,y)|\le C\nu_jL^{-j(d-2)}e^{-\delta_GL^{-j}|x-y|},\qquad\sum_{j\le k_0}(\beta\gamma_j)^{-1}|T_j^{\ell,\mu}-T_j^{\ell,0}|(x,y)\le C\beta^{-2}(1+|x-y|)^{-(d-2+\rho_0)}e^{-\delta_G\sqrt\nu|x-y|}.$$
*Proof.* In unit-lattice kernels $K_j=L^{j(d-2)}T_j$, `GREEN.md` G-5(b) states that $\nu_j\mapsto G_jQ_j^*$ and $C_{tr}^{(j)}$ are Lipschitz on $[0,1]$ in the kernel norm of G-5(a); the kernel $K_j=a_j^2G_jQ_j^*C_{tr}^{(j)}Q_jG_j$ is a product of three such factors, so $|K_j(\nu_j)-K_j(0)|\le C\nu_je^{-\delta_G|u-u'|}$ in unit-lattice distance, which is the first bound. With $\nu_j\le\beta_j^{-1}\le2\beta^{-1}L^{-j(d-2)}$ and $(\beta\gamma_j)^{-1}\le2\beta^{-1}$ the $j$-th term is $\le C\beta^{-2}L^{-2j(d-2)}e^{-\delta_GL^{-j}|x-y|}$; sum with Lemma 1.3 of `CORRELATIONS.md` ($\sigma=2(d-2)\ge d-2+\rho_0$ by (E6)). *Mass factor:* for $j\le k_0$, $\beta_j\nu_j\le1$ gives $L^{jd}\lesssim(\beta\nu)^{-1}$, hence $L^j\lesssim(\beta\nu)^{-1/d}\le\nu^{-1/2}$ and $e^{-\delta_GL^{-j}|z|}\le e^{-\delta_G\sqrt\nu|z|}$ (OBSR O-06). The kernels affected are $T_i$ with $i=j-1\le k_0$ (the background $\varphi_{j-1}$ is $\nu$-free iff $j-1\le k_0$). Lemma 4.2 is conditional on G-5(b), which `GREEN.md` lists as depending on its plan-level block 4.5. $\square$

So F-C is a non-issue for C-1*: the massless-to-massive difference is a remainder term (and, if the layer is defined with massive kernels throughout, there is nothing to prove). It must be recorded as a clause of Def-6 which convention is used; the choice affects the form of (2.5) only. If the convention is massless, `CORRELATIONS.md` §2.2's statement "$\sum_{j<J}(\beta\gamma_j)^{-1}T_j^{\ell,\nu\delta_j}$" is obtained from (2.6) by adding Lemma 4.2's difference to $r$.

### 4.4 What LF-4 (and LF-3, LF-5) must add — summary

1. Requirements 1–5 of §4.2 in the reconstruction document (Part II–III) and in the statements of LF-3, LF-4, LF-5.
2. The hole version of the marked expansion (R-M2): LF-3 and LF-5 are the steps in which it is used; `POLYMER.md` §3.6 already handles holes for the single-function expansion.
3. The convention for backgrounds at $k_0$ (§4.3) written into Def-7 (D2).
4. Nothing else: the budget (D6), the operator bounds (D5), the ripeness/merge bookkeeping and the step counter (LF-2) are not consumed by P9.

---

## 5. The last step and the derivation of C-1* (brief item 4)

### 5.1 The last step in observable form

Let $k=k_f\ge1$, $J=k+1$, $\rho_k\in\mathcal R^\flat_k$ with layer $\mathcal O_k$ (the cases $k_f=0$ and $k_f=1$ are folded into LF-6, LF-8 (b)).

**Proposition 5.1 (LF-8$^{\rm obs}$; sketched).** For $\beta\ge\beta_0$,
$$\int\rho_k\,d\psi_k=\exp\big[-E|\mathbb T|+\mathscr F_J(h,g)+\mathcal R^{(J)}(h,g)+\mathcal P^{(J)}(g)\big],\tag{5.1}$$
where $\mathscr F_J$ has the form (2.3)–(2.5) at level $J$ with layer $\mathcal O_J$ (new $\mu_J,M^{(J)},R^{iJ}$ and the last Gaussian term $G^{(J)}$ of §5.2), $\mathcal R^{(J)}=\sum_{n\le m}\mathcal R^{(J)}_n$ with $|\mathcal R_n^{(J)}(Y)|\le\beta_k^{-n-1}e^{-\kappa d_J(Y)}$, $\mathcal P^{(J)}=\sum_Y\mathcal P(Y;g)$ with $|\mathcal P(Y;g)|\le\beta_k^{-2}e^{-2\kappa d_J(Y)}$ (P9 (4.6); ER-132), all localized, analytic in $g$ on $\|g\|_{\ell^1}<1$, torus independent for non-winding $Y$ (P9 (4.4)–(4.7), P7 (4.15)–(4.17), LF-8 (a)).
*Proof outline.* (a) The massive fluctuation integral over $\psi_k-h$ ($\nu_k>\frac78L^{-2}$, restricted by $\chi_k$ to $|\psi_k-h|<(5L+3)\delta_k$, P4 (6.2)) is a step of the type of Theorem 3.1, with the covariance of §5.2 in place of $C^{(k)}$ and no coarse variable; its new contributions are bounded as in §3.5–3.6 (the polymers are those of $\mathcal D_{J}$). (b) The large-field sum and the exponentiation are one application of PE with volume weights (`LF-ARCHITECTURE.md` LF-8). (c) At the end the restriction to $Z_J^c$ is removed; the difference between the restricted and the whole-lattice functions is a polymer sum with the activity bound $\beta_k^{-2}e^{-2\kappa d}$ and is part of $\mathcal P$. $\square$

Taking $g$-derivatives at $0$ in (5.1) (log of the ratio $Z(g)/Z(0)$; Lemma 0.1 of `CORRELATIONS.md`):
$$M_\ell(x)=M_J(x;h,h)+\partial_{g(x)}\mathcal R^{(J)}(h,0)+\partial_{g(x)}\mathcal P^{(J)}(0),\qquad G_\ell(x,x')=G_J(x,x';h,h)+\partial^2_{g(x)g(x')}\big(\mathcal R^{(J)}+\mathcal P^{(J)}\big)(0)\tag{5.2}$$
(P9 (4.8)–(4.9)), and by Lemma 3.2 and Lemma 2.1 the last two terms of each are bounded by $C\beta_k^{-2}$ resp. $C\beta_k^{-2}e^{-\frac12\delta_0L^{-J}|x-x'|_1}$ (summing $Y\ni x,x'$ and using $M d_J(Y)+2dLM\ge L^{-J}|x-x'|_1$). This replaces P9's printed bound $O(1)\beta^{-2}L^{-J(d-2)/2}|x-x'|_1^{-(d-2)/2}e^{-\frac12\delta_0L^{-J}|x-x'|_1}$ (p. 517) by the plainer $C\beta_k^{-2}e^{-\frac12\delta_0L^{-J}|x-x'|_1}$; the algebraic prefactor of P9 is not needed (it is the source of ER-138's doubt): for $|x-x'|\le L^J$, $\beta_k^{-2}\le C\beta^{-2}L^{-2J(d-2)}\le C(1+|x-x'|)^{-(d-2+\rho_0)}$ by (E6), and for $|x-x'|>L^J$ the exponential beats any power.

### 5.2 The last Gaussian term (finding F-B)

At the last step the quadratic form for $\psi_k-h$ is the massive one, $\frac{\beta_k}2\langle\psi_k-h,\Delta^k_{tr}(\psi_k-h)\rangle$ with $\Delta^k_{tr}=a_k-a_k^2Q_kG_kQ_k^*$ (the effective operator after $k$ steps; `CORRELATIONS.md` $A_k$), *without* the coarse coupling $aL^{-2}Q^*Q$, since there is no coarse variable. So the covariance is $(\Delta^k_{tr})^{-1}=A_k^{-1}$, and the last Gaussian term is $(\beta\gamma_k)^{-1}P_kA_k^{-1}P_k^\top$, whereas P9 (4.14) prints (after the index shift) the regular $C^{(k)}_{tr}=(\Delta^k_{tr}+aL^{-2}Q^*Q)^{-1}=M_k^{-1}$, giving $(\beta\gamma_k)^{-1}T_k$. By the Woodbury identity ($H_k=\alpha_kM_k^{-1}Q^\top$, $\Delta_k=A_{k+1}$)
$$A_k^{-1}=M_k^{-1}+H_kA_{k+1}^{-1}H_k^\top,\qquad P_kA_k^{-1}P_k^\top=T_k+P_{k+1}A_{k+1}^{-1}P_{k+1}^\top,\tag{5.3}$$
so the two readings differ by the tail $E:=(\beta\gamma_k)^{-1}P_JA_J^{-1}P_J^\top\ge0$ (a positive kernel). By G-5 extended to the masses of D-03 (sketched) $|E(x,y)|\le C\beta^{-1}L^{-J(d-2)}e^{-\delta L^{-J}|x-y|}\le C\beta^{-1}\nu^{(d-2)/2}e^{-c'\sqrt\nu|x-y|}$ (using $\frac12\le L^J\sqrt\nu\le L^2$). *Resolved (OBSR Q2; `LF-RECONSTRUCTION.md` (IV.4.5)):* the final covariance is the massive one, because P9 p. 515 integrates over "the fluctuation variable $\psi_k-h$" with "a massive covariance" and then has "performed all the integrations down to $0$-momentum"; P9 (4.14) prints the regular $C^{(j)}_{tr}$ for the last term too, a misprint of the last term (E-O6). So $C_J$ is given by (IV.4.5) with the last summand $(\beta\gamma_{k_f})^{-1}P_{k_f}A_{k_f}^{-1}P_{k_f}^\top=(\beta\gamma_{k_f})^{-1}(T_{k_f}+E_{\rm tail})$, and in `C1Star` the tail is part of $r_{tr}$ ($E'=E$ is never zero; the sentence of version 1 that it vanishes in the regular reading was wrong, OBSR O-01: under the regular reading the same tail sits in the unintegrated field at scale $J$). The amended statement of F-B is therefore: $r=r'+E'$ with $|r'|\le c_*(1+|z|)^{-(d-2+\rho_0)}e^{-c'\sqrt\nu|z|}$ and $|E'|\le c_*\nu^{(d-2)/2}e^{-c'\sqrt\nu|z|}$.

*The printed remainder bound is false in general under the massive reading.* For $L^{J\theta_0}\ll|z|\ll L^J$, $\theta_0=\frac{d-2}{d-2+\rho_0}<1$, one has $(1+|z|)^{-(d-2+\rho_0)}\ll L^{-J(d-2)}\simeq|E(z)|$, and $e^{-c'\sqrt\nu|z|}\simeq1$ there. Root-C only needs the weaker form (§5.3).

### 5.3 Derivation of C-1* (Theorem 5.2; the clauses $F_1$–$F_3$)

Let $L,M$ be those of Root-F at $\kappa=\kappa_*$, $c_9=1$ (`RootFAndC1Star`), $q=ML$, and let the constants of C-1* be those of Lemma 1.1 (`a` the free-flow constant of G-5, `γ₀`$=\gamma$, `cPrime`$=\min\{\delta_0/(2L^2),\delta_G/(2L^2)\}$ after the halving below, `ρ₀,ρ₁` as in Lemma 1.1, `βStar`$=\beta_0$).

**Theorem 5.2 (sketched / proved from Theorem 3.1, Prop 5.1, (CONT), `CORRELATIONS.md` Thm 4.1).** For $\beta\ge\beta_*$ the following objects exist and satisfy `C1StarF1`, `C1StarF2` and the amended `C1StarF3` of §5.4 on every torus with $ML^{J+1}\mid\ell$.

*(F1).* $\xi(\nu,k)$ is the vector of renormalization constants of the flow (P4 (5.28)), with the extension convention of `SMALLFIELD.md` §3.5: $\xi(\nu,k):=0$ for $k\ge k_f(\nu)$ and for $\nu>\bar\nu$, $\xi(0,k):=\lim_{\nu\downarrow0}\xi(\nu,k)$. Bound and continuity: `SMALLFIELD.md` Theorem 5.3 (cited; $\|\xi\|\le\frac{c_\xi}{4\beta}q^{k+1}$, $q=L^{-2\gamma}$, $c_\xi=4C_\xi$ independent of $\beta$, §6). The scale indices used by C-1* are $\xi_i$ with $i\le J-2=k_f-1<k_f$ (for $\beta_{j-1},j\le J$; $\gamma_j,\delta_j,j<J$), so the zero convention is never used by the main terms.

*(F2).* $\mu_j(\nu;x)$ of the layer, $j\le J(\nu)$, $\mu_j(\nu;x):=0$ for $j>J(\nu)$ and $\nu>\bar\nu$, $\mu_j(0;x):=\lim_{\nu\downarrow0}\mu_j(\nu;x)$. The bound $|\mu_j|\le c_*\beta^{-1/2+\rho_1}L^{-j\rho_0}$ is (O1), (the limit satisfies it by closedness), continuity is (CONT). The decomposition: *define* $e^\ell_m(\nu;x):=m_\ell-m_J(\nu;x)$ with $m_\ell$ the scalar of Lemma 0.2 of `CORRELATIONS.md`. By (5.2) and $M_J(h,h)=m_J(x)h$, $e_m^\ell(x)=h\cdot[\partial_{g(x)}\mathcal R^{(J)}(h,0)+\partial_{g(x)}\mathcal P^{(J)}(0)]$, so by Lemma 3.2
$$|e^\ell_m(\nu;x)|\le\sum_{Y\ni x}\Big(2\sum_{n=1}^m\beta_{J-1}^{-n-1}+2\beta_{J-1}^{-2}\Big)e^{-\kappa d_J(Y)}\le6K_0^{\rm O}\beta_{J-1}^{-2}\le24K_0^{\rm O}L^{2(d-2)}\beta^{-2}L^{-2J(d-2)}$$
(P9 p. 516 has $3K_0\beta_k^{-2}$ for the same sum with its own constants; here $\beta_{J-1}^{-2}\le4\beta^{-2}L^{-2(J-1)(d-2)}$ and $\beta_{J-1}\ge1$). The winding polymers contribute $O(e^{-\kappa\ell/(ML^J)})$ to the one-point sums and are dropped by taking $\ell\ge\ell_0(\nu,x)$ (OBSR O-02); the statement of (F2) is for such $\ell$. In the proof of (F2) the identity $M_J(x;h,h)=m_J(x)h$ is the one for non-winding polymers.

*(F3).* The statement is for $x,y\in\mathbb Z^d$ with $2|x_i-y_i|<\ell$ for all $i$ (so the torus distance of $[x],[y]$ is the sup norm $\|x-y\|$ and the decay bound is meaningful; nothing is claimed for other representatives) and $ML^{J+1}\mid\ell$. *Define* $r_{tr}^\ell(\nu;x,y):=G_{tr,\ell}(x-y)-m_J(x)m_J(y)\sum_{j<J}(\beta\gamma_j)^{-1}T_j^{\ell,\nu\delta_j}(x,y)$ and $r^\ell_{lg}:=G_{lg,\ell}(x-y)$. By (2.6), (2.7), (5.2) and Lemma 2.1,
$$r^\ell_{tr}=\tfrac1{N-1}\mathrm{tr}_\perp\Big[R_J(x,y;h,h)+\partial^2_{g(x)g(y)}(\mathcal R^{(J)}+\mathcal P^{(J)})\Big]+E',\qquad r_{lg}^\ell=\mathrm{tr}\big[(R_J+\partial^2(\mathcal R^{(J)}+\mathcal P^{(J)}))\,h\otimes h\big]$$
(longitudinal: no Gaussian term, Lemma 2.1(1), also for the last term since $H_k$ has range $h^\perp$); $E'$ is the last-term correction of §5.2 (never zero) plus, in the $\nu$-free regime, the difference of Lemma 4.2. The bounds: Lemma 2.3(b) for $R_J$, §5.1 for the last-step terms, §5.2 and Lemma 4.2 for $E'$. This gives the amended bound with the mass factor $e^{-c'\sqrt\nu|z|}$, $c'$ from $L^{J}\le L^2/\sqrt\nu$ ($J_{\rm bounds}$) and half of the exponents $\delta_0L^{-i}$, $\delta_G L^{-j}$ used for the summation lemma.

*Limits along tori (the W19 additions).* **Lemma 5.3 (proved).** For $\nu\in(0,1]$, $x,y\in\mathbb Z^d$: `LimAlong (M*L)` of $\ell\mapsto r^\ell_{tr}(\nu;x,y)$ and of $r^\ell_{lg}$ holds, with limits `rtrLim`$:=G_{tr}(\nu,x-y)-m_J(x)m_J(y)\sum_{j<J}(\beta\gamma_j)^{-1}t_j^{\nu\delta_j}(x,y)$ and `rlgLim`$:=G_{lg}(\nu,x-y)$. *Proof.* $G_{tr,\ell},G_{lg,\ell}$ converge along $q^{n}\mid\ell$ with the strong form "for every multiple $\ell$ of $q^{n_0}$" (Theorem 4.1 of `CORRELATIONS.md`, from Root-F's agreement clause; or from the layer's own (TORUS), by the same proof with the class's torus independence in place of Root-F's clause). $T_j^{\ell,\mu}(x,y)\to t_j^\mu(x,y)$ as $\ell\to\infty$ through multiples of $L^{j+1}$ (G1); if $q^{n_0}\mid\ell$ with $n_0\ge J+1$ then $L^{j+1}\mid\ell$ for all $j<J$ and $\ell\ge q^{n_0}$ is as large as desired; $J$ is finite, so the finite sum converges. $\square$ (So these fields of `C1Star` are consequences of the first conjunct of `RootFAndC1Star`; the instance of `C1Star` for the flow is built *with* `RootFClauses` in hand.)

*Limits as $\nu\downarrow0$.* **Lemma 5.4 (proved from (CONT), Lemma 3.6(a)).** For fixed $x,y$, `rtrLim`$(\nu;x,y)$ and `rlgLim` converge as $\nu\downarrow0$. *Proof.* Pass $\ell\to\infty$ in the formula for $r^\ell_{tr}$: the first term is $\frac1{N-1}\mathrm{tr}_\perp\sum_{1\le i\le j\le J(\nu)}\beta_{i-1}(\nu)^{-1}R^{ij}_\infty(x,y;h,h)(\nu)$ (each $R^{ij}(x,y;h,h)$ is the same function of $\nu$ at every level $k\ge j$, because $\psi^{(j)}_k(h,h)=h$); put $a_{ij}(\nu):=\mathbf 1_{[j\le J(\nu)]}\beta_{i-1}(\nu)^{-1}\mathrm{tr}_\perp R^{ij}_\infty$. For fixed $(i,j)$, $J(\nu)\ge j$ for small $\nu$ and $a_{ij}(\nu)\to a_{ij}(0)$ by (F1) (continuity of $\beta_{i-1}(\nu)$) and (CONT); $|a_{ij}(\nu)|\le b_{ij}:=2\beta^{-1}L^{-(i-1)(d-2)}K_0^{\rm O}\beta^{-1/2+\rho_1}L^{-j\rho_0}$, summable. Tannery gives the limit. The last-step terms are $\le C\beta_{J-1}^{-2}+|E'|\to0$ at fixed $x,y$ since $J(\nu)\to\infty$. $\square$ The same argument gives `rlgZero`.

*Where (CONT) is used:* Lemma 5.4 and the continuity clauses of (F1), (F2). Where Root-F is used: Lemma 5.3 only.

### 5.4 The amended interface (the three findings)

The following are proposed changes to `Balaban/Correlations/C1Star.lean` (not frozen; none is made here).

- **F-A (`J` after `β`) — hedge, not forced; landed in W34.** The Lean interface as first written was satisfiable (Root-F's `kf` and `J_bounds` do not mention $\beta$; OBSR O-03), and `LF-RECONSTRUCTION.md` Lemma IV.5.1 takes `kf` $:=\hat k_f(\nu)$, which is $\beta$-free. Moving `J, J_pos, J_tendsto, J_bounds` into `data` weakens `C1Star` and costs ≈40 lines in `Assembly.lean` (the destructuring of `J` precedes `data`, but `hJp/hJt/hJb` are used only after `data β`). The earlier claim that the flow's $k_f(\beta,\nu)=\min\{k:\nu_k>\frac78L^{-2}\}$ forces a $\beta$-dependent $J$ is a feature of that stopping rule only; the $\beta$-free rule $k^\sharp(\nu)=\min\{k:\nu L^{2k}>\frac{13}{16}L^{-2}\}$ gives $\nu_{k^\sharp}\in(0.8L^{-2},0.86]$ for $\beta$ large, and what the last step uses is only the mass window (P9 p. 515 reads "massive, mass $\approx L^{-1}$"; whether P4 §6 needs the number $\frac78$ is not read).
- **F-B (remainder bound; landed in W34).** In `C1StarF3` the bounds on `rtr`, `rlg` read $c_*\big[(1+\|x-y\|)^{-(d-2+\rho_0)}+\nu^{(d-2)/2}\big]e^{-c'\sqrt\nu\|x-y\|}$. Consumers: `BoundsNu.lean` (Step B: $\nu^{(d-2)/2}e^{-c'\sqrt\nu|z|}\le C|z|^{-(d-2)}e^{-c'\sqrt\nu|z|/2}$ for $|z|\ge1$, trivially $\le1$ for $|z|<1$; $c'$ halved) and `ZeroLimit.lean` (Step C: at fixed $z$ the extra term $\to0$). **F-B2 (O-02, landed):** the `em` bound of `C1StarF2` holds for $\ell\ge\ell_0(\nu,x)$ only, and `LemmaThree.lean` takes $n_0:=\ell_0+J+1$.
$|r|\le c_*\big[(1+\|x-y\|)^{-(d-2+\rho_0)}+\nu^{(d-2)/2}\big]e^{-c'\sqrt\nu\|x-y\|}$. Consumers: `BoundsNu.lean` (Step B: $\nu^{(d-2)/2}e^{-c'\sqrt\nu|z|}\le C|z|^{-(d-2)}e^{-c'\sqrt\nu|z|/2}$ since $(\sqrt\nu|z|)^{d-2}e^{-c'\sqrt\nu|z|/2}\le C$, and trivially $\le1$ for $|z|<1$; replace $c'$ by $c'/2$) and `ZeroLimit.lean` (Step C: at fixed $z$ the extra term $\to0$ as $\nu\downarrow0$, so the bound on `rtrZero` is unchanged). Estimated edit: 100–200 lines.
- **F-C.** None (Lemma 4.2); record the convention in Def-6.

*Documentation edits* (docstrings only): `C1StarF1` should state the extension convention of §5.3 (F1); `C1StarF3` should say that `rtrLim` is defined by subtraction and the limits are consequences of Root-F (Lemma 5.3).

---

## 6. The $\beta$-dependence question (brief item 5)

**What Root-C requires.** `lowTemperature_correlations` quantifies $\exists\,\beta_0,c,c',\rho_0,\rho_1,q\ \forall\beta\ge\beta_0$: the constants are chosen before $\beta$. Roland's batch 2 leaves open whether P9 allows $c,c',\rho_0,\rho_1$ to depend on $\beta$ (`review/ROLAND_ANSWERS.md`).

**Which uniformities are load-bearing** (proved by inspecting the proof of `CORRELATIONS.md` Theorem 3.1):
- $q=ML$: the torus family must be fixed before $\beta$ — **needed** (the first bullet is a limit along $q^n\mid\ell$ for a fixed $q$ and every $\beta\ge\beta_0$).
- $c'$: the decay rate in $e^{-c'\sqrt\nu|x|}$ — **needed**: a rate $c'(\beta)\to0$ would not be a bound of the stated form.
- $\rho_0$: the power gain in the Goldstone remainder — **needed** (it is an exponent).
- the constant in $|\gamma_\infty-1|\le c/\beta$ — **needed**: it must be $O(1)$ in $\beta$.
- $c$ in $|G_{tr}|,|G_{lg}|\le c(1+|x|)^{-(d-2)}e^{-c'\sqrt\nu|x|}$ and in the Goldstone remainder: *not needed in full*: $G=O(\beta^{-1})$, so any bound $C(\beta)\beta^{-1}$ with $C(\beta)\le c\beta$ gives the stated form. The same for $c$ in $|G_{tr,0}-\frac{m_0^2}{\beta\gamma}G|\le c(1+|x|)^{-(d-2+\rho_0)}$ (the true size is $\beta^{-3/2+\rho_1}$).
- $\rho_1<1$ and $c$ in $|m-1|\le c\beta^{-1+\rho_1}$: *not needed in full*: if $|m-1|\le C(\beta)\beta^{-1+\rho_1'}$ with $C(\beta)\le C\beta^{\epsilon}$ then $\rho_1:=\rho_1'+\epsilon<1$ works.

**What the flow gives.** All constants of C-1a are fixed before $\beta$ in the quantifier prefix (`LF-RECONSTRUCTION.md` §I.1.4: $\forall\beta\ge\beta_0$ is last, with row 17 and "$\beta_0$ enlarged last"), as in P9's own order (p. 505: "$\beta_k=O(1)\beta L^{k(d-2)}$"; Sect. 3: "for $\beta$ sufficiently large", with every $O(1)$ depending on $d,N,L,\kappa,M,\gamma,\rho_i$ only):
1. $q=ML$ and $L,M$ come from Root-F at $(\kappa_*,c_9=1)$ before $\beta_0$; Root-F is stated that way (`LowTemperatureCorrelations.lean` header; Root-F's quantifier order).
2. $c'$: $\min\{\delta_0,\delta_G\}/(2L^2)$ with $\delta_0=\kappa/M$ (P9 p. 509) and $\delta_G$ from G-5 (a function of $d,L,a$): no $\beta$.
3. $\rho_0,\rho_1,\rho_2$: Lemma 1.1, functions of $d,\gamma$.
4. The constant in $|\gamma_\infty-1|\le c/\beta$: $|\xi^{(k)}|\le2|f(0)|$ with $|f_i|\le B_6\beta_{k+1}^{-1}\varepsilon_{k+1}^{-2}$ (P4 (5.25)–(5.31)), and
$$\beta_{k+1}^{-1}\varepsilon_{k+1}^{-2}\le2\beta^{-1}L^{-(k+1)(d-2)}\alpha_0^{-2}L^{2\alpha(k+1)}=2\alpha_0^{-2}\beta^{-1}L^{-2\gamma(k+1)}\qquad(2\alpha=d-2-2\gamma),$$
so $C_\xi=O(B_6\alpha_0^{-2})$ is a constant of the prefix (`SMALLFIELD.md` Theorem 3.2).
5. The only explicit function of $\beta$ in the proof is $p_1(\beta_k)=A_1(\log\beta_k)^{p_1}$ (and $p_0$): by (B3) it is traded against powers of $\beta$ and of $\eta$ with the exponent $\rho_2$ fixed in advance, which is where $\rho_1\ge4\rho_2$ (P9: $3\rho_2$ with its constant $K_0$) comes from. No constant of the layer depends on $\beta$.

**What does depend on $\beta$:** the objects $\xi(\nu,k)$, $\gamma_\infty$, $m(\nu)$, $G$, the running sequences, $k_f$, $k_0$, the large-field regions. Of these only $k_f$ enters a *statement* of C-1* with the wrong quantifier order (F-A).

**Answer.** P9's constants may be taken independent of $\beta$, and the strong reading of Root-C (constants before $\beta$) is what the flow gives. Nothing in the proof requires or produces $\beta$-dependent $c,c',\rho_i$. Text-ready item for Roland (to be relayed by Scott): "In P9 Theorem 1.1 the constants $c,c',\rho_0,\rho_1$ can be chosen independent of $\beta$ (they depend on $d,N$ only; $\beta_0$ depends on them). We checked the dependence through the whole proof: the only place with an explicit $\beta$-dependence is the field-size parameter $p_1(\beta)=A(\log\beta)^p$, which is absorbed in $\beta^{\rho_2}$ with $\rho_2$ fixed first. Is this the reading you wanted, or do you need something weaker?"

---

## 7. Interfaces, errata, Lean plan, size, questions

### 7.1 Interfaces for freezing

None of the following is freezable yet (all depend on Def-7, which is frozen only after the reconstruction document is approved).
- **Def-O** (§2.1): an extra conjunct of Def-6; freeze with Def-6/Def-7.
- **LF-3$^{\rm obs}$ = Theorem 3.1**: freeze with LF-3 (small-field step) and LF-5 (frozen regime). The statement is about representations, so it follows the existential form of LF-4 (R3-10).
- **LF-8$^{\rm obs}$ = Proposition 5.1** with the covariance of §5.2: freeze with LF-8.
- **C-1\* (amended)** (§5.4): the consumer-facing interface (already a Lean `structure`, unfrozen); it can be changed now.
- **Not frozen, internal:** Lemmas 2.1–2.3, 3.2, 3.4, 3.5, 4.2, 5.3, 5.4, Proposition 3.3.

### 7.2 Changes at $\lambda=\infty$ (collected)

(1) $H_{j}$ has range $h^\perp$ exactly (Lemma 2.1), so the longitudinal Gaussian term and P9's $\lambda$-dependent bound $c\beta^{-1}\lambda^{-2}(1+|x|)^{-(d+2)}$ are replaced by $0$ (not by a smaller bound). (2) The $\lambda$-equation of the RG system is vacuous (`SMALLFIELD.md` §1.5). (3) The hard-spin factor $|e^{\langle g,\varphi\rangle}|\le e$ (requirement 1 of §4.2) replaces P5's finite-$\lambda$ control of the large-field factor. (4) P9's hypothesis $\lambda\ge\lambda_0$ (ER-017) is vacuous. (5) The O($N$) stabilizer argument of Lemma 2.1 requires $N\ge2$ only (for $N=2$, $h^\perp$ is a line).

### 7.3 Errata

Existing P9 rows used: ER-010 (torus independence and limits), ER-011/012 (the $\beta_{j-1}^{-1/2}$ normalization; Lemma 2.2 settles the dictionary), ER-017 (vacuous), ER-062/063 (base case: LF-6), ER-124 to ER-138. Dispositions: ER-124 (misprint, harmless); ER-125 (the printed exponent of Theorem 1.1(b) is $-(d-2+\rho_0)$ as the orchestrator reads it; no effect); ER-126 (the abstract's $\beta^{-1/2}$ is weaker than the theorem; Lemma 2.3(a) gives $\beta^{-1+\rho_1}$); ER-127–128 (motivation only); ER-129 ($\kappa_i$: $:=\kappa$; $\eta$: $L^{-k}$; index shift: §1.1); ER-130 (no effect); ER-131 (Lemma 1: the effective exponent is $\sigma=d-2+\rho_0$ after summation over $j$, Lemma 2.3(b)); ER-132 ($2\kappa$ confirmed on p. 516, used in Prop 5.1); ER-133 (the "similar" terms are recomputed in §3.6, all exponents confirmed); ER-134 (Prop 3.3 reduces (3.13) to PE-M); ER-135 (requirements 1–5 of §4.2, (L5)); ER-136 (Theorem 5.3 of `SMALLFIELD.md`, §6 item 4); **ER-137** (the longitudinal main term is $0$ at $\lambda=\infty$; the remainder gives $(1+|x|)^{-(d-2+\rho_0)}$, no lower bound); **ER-138** (settled in the stronger direction: the algebraic prefactor of P9 p. 517 is not needed, §5.1).

Proposed new rows (for the orchestrator to add; `ERRATA.md` is not edited here):
- **E-O1.** P9 (3.25): "$\exp(-\delta_0L^{-1}|x-x'|_1)$" should be $L^{-i}$ (the proof of $R_1^{i,k+1}$ and (2.18) use the scale $L^{-i}$). Misprint.
- **E-O2.** P9 (3.28): "$\beta^{-1/2-\rho_2}$" should be $\beta^{-1/2+\rho_2}$ (from $p_1\le\beta^{\rho_2}$). Misprint; harmless.
- **E-O3.** P9 (3.23): the middle line prints $\xi^{-1+\rho_1+\gamma}$ where the computation gives $\xi^{-1+\rho_0+\gamma}$. Misprint.
- **E-O4 (downgraded).** P9 p. 511 prints (text layer) $\rho_1=3\rho_2$, $\rho_0\le\min\{\frac{d-2}2,1-3(d-2)\rho_2\}$; our list is (E1)–(E8) with $\rho_1\ge4\rho_2$. Whether P9's list is inconsistent with the proofs is unverified (page image not read); the printed $\rho_1=3\rho_2$ cannot close the row $R_1^{k+1,k+1}$ with constant $1$ (O-04) but closes it with P9's constant $K_0$.
- **E-O5.** P9 (2.18)/p. 498: the "global bound" $K_0\beta^{-1/2+\rho_1}\xi^{\rho_0}e^{-\delta_0|x-x'|_1}$ drops the $L^{-i}$ in the exponent. Misprint.
- **E-O6.** P9 (4.14)–(4.17): the last Gaussian term of the final integral is not computed; the regular $C^{(k)}_{tr}$ and the massive $(\Delta^k_{tr})^{-1}$ differ by a tail of size $\beta^{-1}L^{-J(d-2)}$ (§5.2). Gap (affects `C1StarF3` as stated, not Root-C).
- **E-O7.** P9 (3.39): "$p_2(\beta_k)$" should be $p_1(\beta_k)^2$. Misprint.
- **E-O8.** P9 (4.8) "m" (the number of reduced-symmetry pieces $\mathcal R_n$) is undefined in P9; it is the $m$ of P5 H4 ($L^m=M$).
- **E-O9.** P9 Prop 3.1 (3.13) is stated on $\mathcal D_{k+1}$ although the step has large-field holes (R-M2).

### 7.4 Lean plan

Modules (new directory `Balaban/Observables/`); none imports a root or provider.

| Package | Content | Lines | Risk |
|---|---|---|---|
| O1 | Def-O (the layer as a predicate on a representation), Lemma 2.1 (stabilizer/Schur argument, sphere constraint), Lemma 2.2 (dictionary), Lemma 2.3 (sums), Lemma 1.1 (constants) | 2,500–4,500 | low–medium (Schur for $O(N-1)$ on $h^\perp$) |
| O2 | Cauchy lemma 3.2 (one- and two-variable, polarization), $g$-derivative bookkeeping for inherited packages | 800–1,500 | low |
| O3 | Prop 3.3: marked expansion with holes as consumed by the fluctuation integrals (the PE-M corollary is in the polymer package; this is the instance, three cases of radius) | 3,000–6,000 | high (R-M1, R-M2) |
| O4 | First-order step: T1, T2, shifts, normalization (3.2); exponent bookkeeping as `Real.rpow` inequalities | 8,000–15,000 | medium |
| O5 | Second-order step: $R_1,R_2,R_3$, Lemma 3.5, (3.3), shifts | 12,000–25,000 | medium |
| O6 | Lemma 3.4 (improved bound from (2.7)); the $b$-form at $\lambda=\infty$ | 3,000–6,000 | medium–high ($\nu$-free regime) |
| O7 | (CONT) and (TORUS) for the layer; Tannery/Vitali (Lemma 3.6) | 5,000–12,000 | high (large-field data) |
| O8 | $g$ through LF-3/4/5: requirements 1–5 of §4.2, hard-spin bound $|e^{\langle g,\varphi\rangle}|\le e$, covariance of the coset average in $(\psi,h,g)$ | 4,000–10,000 | medium |
| O9 | LF-8$^{\rm obs}$, Prop 5.1, the last Gaussian term (5.3), Theorem 5.2, Lemmas 4.2, 5.3, 5.4 | 6,000–12,000 | medium–high (§5.2) |
| O10 | Edits to `C1Star.lean`, `Assembly.lean`, `BoundsNu.lean`, `ZeroLimit.lean` (§5.4) | 200–400 | low |
| | **Total** | **45,000–90,000** | |

Order: O1, O2, O10 first (no flow needed; O10 can be done now); O3 with the polymer package; O4–O6 after Def-6 is stated; O7, O8 after Def-7; O9 last.

### 7.5 Size

O1, O4–O7 are the X1–X7 of `SMALLFIELD.md` §7.5 (40k–80k there; here 31k–62k, so the two estimates are consistent); O8–O10 (10k–22k) are not in that estimate. **Total 45k–90k Lean lines for C-1a, the carrying of $g$ through $R$, the last step and the interface**, on top of `CORRELATIONS.md` §6 (4.5k–5.5k, of which about 0.5k is already landed as `Balaban/Correlations/*`) and the polymer package. The largest single risks by lines are O5 (volume of terms) and O7.

### 7.6 Questions

1. **Interface amendments — done (W34).** F-A, F-B, O-02 are in `C1Star.lean`.
2. **Last Gaussian term — answered (OBSR Q2).** The final covariance is the massive $(\Delta^{k_f}_{tr})^{-1}$ and $F_J$ contains the tail $E_{\rm tail}$; P9 (4.14) is misprinted for the last term; the tail is part of $r_{tr}$ in `C1Star`. (An alternative, OBSR O-10: put the massive last summand into `mainTr`; not adopted.)
3. **$\nu$-free backgrounds — answered (OBSR Q3).** The Gaussian kernels $T_i$ are massless for $i\le k_0$ and massive after (the class's convention); Lemma 4.2 (with the mass factor) moves the difference into $r$.
4. **(LF author) Requirements 1–5 of §4.2 and the hole version of PE-M.** In particular: no definition of an operation at scale $k\le j$ in LF-3/LF-4 uses the horizon $\hat k_f(\nu)$ (requirement 5; else (CONT) at fixed $k$ fails as $\nu\downarrow0$).
5. **(Polymer author) (R-M1).** Is the non-product Gaussian measure of the fluctuation integral (covariance $C^{(k)}$, not diagonal) covered by the product-measure form of PE-M via P6 (4.35)–(4.42)? This is the only place where the two-function expansion could fail to reduce.
6. **(Scott, for Roland) $\beta$-dependence.** Text-ready item in §6.


---

## Status of the statements cited by the assembly (`LF-RECONSTRUCTION.md` Theorem IV.5.4, Table IV.5.5)

| Statement | Used for | Status in version 2 |
|---|---|---|
| Lemma 1.1 (exponents, $\rho_1=4\rho_2$, (E3) with $2(d-2)\rho_2$) | `ρ₀, ρ₁` of the instance | **proved** (arithmetic) |
| Lemma 2.1 (structure at $\psi\equiv h$, with $Hh=0$) and Lemma 2.3 (sums) | $r_{lg}$ has remainders only; bound on $R_J$ | **proved** (Lemma 2.1(4) cites BG Prop 5.4 and CORR (2.2)) |
| Theorem 3.1 (one step preserves $\mathcal O_k$) | `μ` bound, continuity, the layer in (IV.4.4) | **sketched**: exponents of every new term proved (§3.5–3.7); depends on Prop 3.3 and Lemma 3.4 |
| Proposition 3.3 (marked expansion with holes) | all new second-order terms | **reduced** to PE-M; (R-M1) non-product covariance and (R-M2) holes **open** (OBSR O-09, main risk) |
| Lemma 3.4 (improved bound, P9 Lemma 2) | gain $\eta^{\rho_0}$ in T2 and the $R_{2}$, $R_3$ rows | first bound **cited** (P1); second bound **proved** from the first and (2.1); $\nu$-free regime **UNCERTAIN** |
| Lemma 3.2 (Cauchy for $g$-derivatives) | $\partial_g^{1,2}$ of $\mathcal R''$, $\mathcal P$, and of the $e^b$ factors | **proved** |
| Proposition 4.1 ($R$ preserves the layer) | LF-4 in the flow | **proved** from LF-4 (a), (c); requirements 1–5: 2 closed (Lemma III.9.6), 3–4 are (S0), (S3), (D7), 1 and 5 as in §II.6.5 |
| Lemma 4.2 (mass reconciliation, with mass factor) | $r_{tr}$ for the massless $T_i$, $i\le k_0$ | **proved** given GREEN G-5(b) (conditional on its block 4.5) |
| Proposition 5.1 / (IV.4.5) (last step, massive final term) | $M_\ell,G_\ell$ decomposition | **sketched** (LF-8 (a) Theorem IV.4.1; Gaussian term by Woodbury (5.3), proved) |
| Theorem 5.2 (F1–F3) | `C1Star` instance | **proved** given Theorem 3.1, Prop 5.1, (CONT) |
| Lemma 5.3 (limits along tori) | `rtrLim`, `rlgLim` | **proved** (CORR Thm 4.1 + (G1)) |
| Lemma 5.4 (limits as $\nu\downarrow0$) | `rtrZero`, `rlgZero` | **proved** from (CONT) and Tannery; (CONT) **sketched** (§3.8) |

## Review dispositions (`OBSERVABLES-review.md`)

- **O-01** accepted: F-B confirmed; "$E'$ zero in the regular reading" deleted (§5.2, §5.3, §5.4); `C1StarF3` corrected (W34).
- **O-02** accepted: `em` bound only for $\ell\ge\ell_0(\nu,x)$ (Remark 2.0, §5.3 (F2), §5.4 F-B2); `C1StarF2`, `LemmaThree.lean` corrected (W34).
- **O-03** accepted: F-A rewritten as a hedge (§0, §5.4); the earlier claim that the stopping rule forces a $\beta$-dependent $J$ is withdrawn.
- **O-04** accepted: $\rho_1:=4\rho_2$ (E1), with the alternative of a constant $K$ before $\beta$ (Lemma 1.1, §6 item 5).
- **O-05** accepted: (E3) with $2(d-2)\rho_2$; $\rho_2$ has $\frac{1-\gamma}{2(d-2)}$; the comparison with P9 p. 511 is marked unverified; E-O4 downgraded.
- **O-06** accepted: mass factor $e^{-\delta_G\sqrt\nu|x-y|}$ in Lemma 4.2, index range $i\le k_0$, conditionality on G-5(b).
- **O-07** accepted: $Hh=0$ and the vanishing of the cross blocks of $C^{(j-1)}$ in Lemma 2.1.
- **O-08** accepted: $\alpha_1<\gamma$ (Lemma 1.1); positivity remark added to requirement 1 (§4.2).
- **O-09** accepted as the main risk: Proposition 3.3 status stated precisely (§3.3); Theorem 3.1 downgraded to "sketched at the level of the expansion, proved at the level of exponents".
- **O-10** noted: the massive final summand is stated in the *layer* (Prop 5.1, §5.2) but the tail stays in $r_{tr}$ in `C1Star` (not changing `mainTr`).
- **Q2, Q3** adopted (§7.6 items 2–3).

## Version 2 changes

1. Header, summary (F-A hedge, F-B/F-B2 landed, (L4$'$)), Lemma 1.1 (E1, E3, $\alpha_1<\gamma$, $\rho_2$), Remark 2.0, Lemma 2.1 (Hh = 0).
2. Proposition 3.3: precise status (proved / cited / open), after OBSR O-09.
3. §4.1: (L4) replaced by (L4$'$) of `LF-RECONSTRUCTION.md` Remark IV.4.5 (operators depend on $g$ through $e^b$; marked terms bounded by Lemma 3.2); §4.2 requirement 1 (positivity), requirement 2 marked closed (Lemma III.9.6); Lemma 4.2 with the mass factor.
4. §5.2–5.4: massive final covariance as resolved, tail in $r_{tr}$, F-A/F-B/F-B2 as landed; (F2) for $\ell\ge\ell_0$.
5. §7.3 E-O4 downgraded; §7.6 questions 1–3 answered.
6. New: table of the statements cited by the assembly with exact status; review dispositions.
7. Not changed: §3.5–3.7 exponent computations, §6 (the $\beta$-dependence; unaffected by the revisions, as OBSR confirms), Lemma 5.3/5.4. The small-field document v3 (two RG conventions, P1 (3.107) normalization) does not change any statement here; the $\nu$-free system of SF §3.7 is the one Lemma 4.2 and the (CONT) argument refer to.
