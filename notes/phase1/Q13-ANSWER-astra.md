# Q13. The change from field-free to complete backgrounds at $k_0$

Balaban uses the two conventions in P5 (1.9) and explicitly proposes a two-step change at the crossing in P6 p. 11: insert the external field in the variational problem, put the resulting term into the new effective action, and then perform the usual complete-background renormalization. The background displacement is $O(\beta_{k_0+1}^{-1})$ for a fixed real unit field $h$, and the exact two-step chord has logarithmic cost $O(\beta_{k_0+1}^{-1})$ on a fixed complex neighbourhood of that physical field. These are **not** bounds on the full mass-uniform complex transverse-source domain used by the printed inductive hypotheses. P4 (H.4) and P5's inherited class do require complex analyticity in $(\psi,h)$; P9 makes only $g$ the complex observable source in its physical theorem, but does not remove that auxiliary $h$-analyticity from the P1–P7 proof. Neither P5 nor P6 states a mass-dependent restriction on the $h$ domain at $k_0$, or resums the large transverse-source free energy into a separate reference functional. Thus the printed short argument does not settle the uniform complex switch estimate posed in Q13.

For the fixed-real-$h$ theorem, the natural repair is a *pinned-field* induction: keep the physical mass $m_j>0$ in the action even when the background mass is zero; bound local terms on a spin disc with $h$ in a fixed small complex ball about a real unit vector; provide separate aligned longitudinal germs for the RG conditions; and prove an I-6 estimate on these restricted data. On the physical ball $b=mh$ is $O(m)$, so the switch has cost $O(\beta m^2)$ per block, and its leading observable change is $O(m)$. I give below an exact conditional reduction of the full step to named localization, domain, and irrelevance estimates. Those estimates have **not** been proved by the cited papers or the current landed Lean interfaces. Accordingly this is a viable formulation and a precise proof obligation, not an unconditional repair of Balaban's published induction or of LF-RECONSTRUCTION Theorem IV.2.2.

The distinction matters for the frozen root. `Balaban/Frozen/Roots/LogPartitionMultiscale.lean` quantifies over a **real** $h$ with $\|h\|=1$ and makes the observable source $g$ complex. Its statement does not ask for analyticity in a mass-uniform transverse $h$ disc. Q13 therefore does not refute the root statement. It refutes the proposed use of the present, wider complex-$h$ class to prove its switch without a changed domain, an explicit source resummation, or new estimates.

## 1. What the papers say

The keys and PDFs are those of [`SOURCES.md`](/home/scott/Balaban/review/SOURCES.md). Printed page numbers are used throughout. P4 is a scan; the formulas cited here were checked on its page images, not inferred from OCR.

| Source | Evidence and implication |
|---|---|
| P4, pp. 676–678, (H.2)–(H.4) | The localized effective terms depend on $(\psi_j,h)$ and have analytic extensions and a uniform $E_0e^{-\kappa d_j(X)}$ bound on the complex background space. The observable functional is analytic in $g$ as well. In particular the published induction assumes auxiliary complex-$h$ control, even though $h$ is real in the model. |
| P4, p. 702, (4.8)–(4.13); pp. 707–708, (5.1)–(5.5); pp. 711–715, (5.14)–(5.26) | Renormalization uses three reference jets: radial spin, longitudinal field, and a transverse *spin* second moment. In (5.1) the potential is written as $f(U,V,W^2)$; (5.3) differentiates in $U,V$ and (5.15)–(5.17) take two spin derivatives on a disc of size $\asymp\varepsilon_{k+1}$. The triangular complete-background matrix is (5.21), and the forcing must be $O(\beta_{k+1}^{-1}\varepsilon_{k+1}^{-2})$ for (5.23)–(5.26). Formula (4.13) separately displays the field-only counterterm $\frac12\nu e(|h|^2-1)|T_1|$; it is not a resummation of transverse fluctuations. |
| P5, pp. 489–490, (1.8)–(1.9) and the paragraph following (1.9) | For $\beta_k\nu_k\le1$, put $\nu_k=0$ **in the variational problems**, retain the field term in the main action, and treat it as a perturbation. There is one crossing index in the running convention. P5 says the distinction simplifies the large-field analysis and was unnecessary for the small-field analysis of P1/P4. It does not declare the physical mass zero. |
| P6, pp. 1–2, Theorems 1 and 4; pp. 10–11, (2.22)–(2.25) | The first theorem is used for $k<k_0$ with field-free backgrounds; after $k_0$ the field enters the background problem. Equation (2.24) contains the new source $\nu_{k+1}(\phi_{k+1}-h)$. P6 compares it with P4 (4.10), requires $\nu_{k+1}=O(\beta_{k+1}^{-1})$, and on p. 11 calls the new terms “very small.” On the same page it proposes first changing the background without renormalizing and putting $-\beta_{k+1,u}C^{(k+1)}$ in $\mathcal E_0^{(k+1)}$, then using the ordinary complete-background renormalization. The p. 11 statement about zeroth and first order $\xi$ terms is an assertion of smallness; it supplies no mass-uniform transverse-$h$ estimate. |
| P6, p. 14, following (2.30); P7, p. 497, Theorems 2 and 5 | The old main-action operation leaves the background field-free for $k\le k_0$. P7 performs its large-field removal for $k<k_0$ and takes that operation to be the identity after the crossing. This is why a complete-background convention at every scale would require a separate large-field proof. |
| P9, pp. 493, 495–496, (1.1), (2.1)–(2.2) | The physical field direction is a real unit vector, while $g$ is complex with $\|g\|_1<1$; connected observables are derivatives in $g$. P9 also invokes the P1–P7 analytic effective-action hypotheses, so it cannot be cited as a proof that their auxiliary complex-$h$ bounds may simply be deleted. |

The explicit anisotropic source radii in P3 p. 74 (4.26), as checked in `CLASS-RULINGS.md` Q-D, allow $|b_\perp|=O(\varepsilon_j)$ and $|b_\parallel-m_j|=O(\varepsilon_j^2)$ near an aligned field. P1 pp. 127–129, (3.29)–(3.45), uses such invariant-coordinate discs in I-6. `I6-ANISO.md` specifies the corresponding proof route. These are domains for an **already bounded** local term; they do not establish that the physical switch or mass-free fluctuation term has the same bound there.

## 2. The obstruction and the four readings

Write $u=k_0+1$, $\beta_u=\beta_{k_0}L^{d-2}$, $m=m_u=\nu_{k_0}L^2$ in output unit-scale coordinates, $b=mh$, and $\varepsilon=\varepsilon_u$. At a genuine crossing let

$$\beta_um=\theta,\qquad 1<\theta<C_L,\qquad C_L=e^{2\epsilon_*}L^d$$

for the a priori index of LF-RECONSTRUCTION D-IV.11; P5's running index gives its stated upper factor close to $L^d$. The distinction changes constants, not the argument. With $e=e_1$ and $b=me+qe_2$, the exact constrained one-block action gives

$$\phi^0=e,\quad \phi^m=\frac{(a+m)e+qe_2}{\sqrt{(a+m)^2+q^2}},\quad
\beta_u\{A_m(e,\phi^0)-A_m(e,\phi^m)\}
=\frac{\beta_u q^2}{\sqrt{(a+m)^2+q^2}+a+m}.\tag{2.1}$$

For fixed $q=\sigma\varepsilon^2>0$, (2.1) grows like $\beta_u\varepsilon^4$ as $m=\theta/\beta_u\downarrow0$. This point is inside the ordinary complex background domain and the mass-uniform anisotropic transverse polydisc for sufficiently small fixed $\sigma$; `RGFREE-6.md` §2 checks this with a *real* transverse displacement. `RGFREE-3.md` §2.1 gives the corresponding imaginary displacement, for which the absolute chord has the same growth. A bounded old H4 action cannot cancel it: at a fixed step, the old-scale sum is at most $C_uE_0$ per output block, independently of $\beta_u$ (`RGFREE-3.md` (2.6)). The leading observable difference has size $|\langle g,\phi^0-\phi^m\rangle|\asymp |g_\perp q|$ and violates an H7 allowance that tends to zero (`RGFREE-3.md` §3). `RGFREE-6.md` §3 gives a separate **cutoff one-block model** whose raw mass-free fluctuation logarithm is at least $c q\sqrt{\beta_u}-C$. This is a test of the asserted uniform activity bound, not an identification of Balaban's entire fluctuation integral.

The test field is $h=e+(q/m)e_2$ (or its imaginary analogue), so it is outside the physical real unit sphere. The contradiction concerns a claimed bound on an analytic **extension**, not the Gibbs model at a real unit field.

**(a), a smaller field domain.** For a switch bound $C\beta_um\varepsilon^2$ in (2.1), the *$b$* radius must obey $|b_\perp|\lesssim\sqrt m\,\varepsilon$; an H7 estimate can demand the smaller bound $|b_\perp|\lesssim c_9L^{-us}$. The corresponding radius in $h_\perp$ is $\varepsilon/\sqrt m$, since $b=mh$; calling $\sqrt m\,\varepsilon$ a width in $h$ confuses the coordinates. A fixed complex ball $\|h-h_*\|<r_h$ about a real unit $h_*$ is narrower still: $|b_\perp|=O(m)$ in a frame aligned with $h_*$. It contains every physical real $h_*$ and is stable as a parameter domain across scales. This reading makes the scalar switch estimate true, but the P1/P4 I-6 proof and the existing full-$\Xi^c$ H4/H7 clauses do **not** transfer unchanged. The moving-background source-tube obstruction in `RGFREE-5.md` §1 and the incompatibility identified in `RGFREE-6.md` §4 must be dealt with by restricted-domain I-6 and actual composition estimates.

**(b), source resummation.** One may in principle retain the full transverse polydisc by displaying its source free energy as part of a new reference functional and proving a bounded remainder. The algebraic field-only factor $\exp\{-\beta b\cdot b/(2m)\}$ in $\frac m2(\phi-h)^2=\frac m2-b\cdot\phi+\frac{b\cdot b}{2m}$ is **not** that free energy: it cancels from the normalized cutoff ratio in `RGFREE-6.md` §3, while the latter still grows. An actual resummation would involve the covariance, cutoff, nonlinear spin chart, old actions, and a new RG system. P6 (2.22)–(2.25) inserts a small change of background into $\mathcal E_0$; it does not define this mass-uniform source functional. Thus (b) is a possible new program, not an explanation of Balaban's stated estimates.

**(c), complete backgrounds throughout.** P5 p. 490 expressly says the two conventions were unnecessary for the earlier *small-field* analysis. So (c) can remove the switch in a small-field-only development. It does not reproduce P7's pre-$k_0$ large-field removal, whose hypotheses and background constructions are field-free, nor does it avoid proving uniform complex-$h$ bounds for its new class. It is therefore not an available one-line repair for the present multiscale large-field reconstruction.

**(d), separate the physical and auxiliary sources.** The field $h$ selects the Gibbs state, whereas $g$ produces observables. The physical theorem needs complex analyticity in $g$ on its $\ell^1$ ball, not in an independent mass-uniform transverse $b$ ball. A pinned-$h$ class with the specific auxiliary germs used by renormalization is the economical version of (a)+(d). The following statement makes its remaining obligations explicit.

## 3. A precise pinned-field switch statement

Fix $d\ge3$, $N\ge2$, a real unit $h_*$, and $0<\gamma<\min\{1/2,(d-2)/2\}$. Set $\alpha=(d-2)/2-\gamma$, $\varepsilon_j=\alpha_0L^{-j\alpha}$ (or the comparable sequence of the induction), $s=(d-2)/2+\gamma-\alpha_1$ with $0<\alpha_1<1-2\gamma$, and $c_9=\beta_{\rm in}^{-1/4}$. All constants below are uniform in the torus, the genuine crossing index, $m>0$, and $\beta_{\rm in}$ after the final threshold.

For every term born at level $j$, retain **two masses**: $m_j$ in the physical action and $\mu_j=0$ for the solver while $j\le k_0$, $\mu_j=m_j$ thereafter. Let $\mathcal D^{\rm pin}_{j,m_j}(h_*)$ be the intersection of the relevant complex background domain with

$$\|h-h_*\|<r_h,\qquad
\|\psi-\psi_{\rm sf}\|_{\rm spin}<r_s\varepsilon_j,\qquad
\|\xi\|_\infty<c_{10},\tag{3.1}$$

where $r_h,r_s,c_{10}>0$ are fixed before $\beta_{\rm in}$ and the spin norm includes the scaled differences used in the background estimates. Terms have the usual localized analytic bounds on (3.1), uniformly for every choice of real unit $h_*$. At an aligned constant background, additionally require compatible **axial germs** on

$$\psi=U h_*,\quad b=Vh_*,\qquad |U-1|<r_U\varepsilon_j,quad |V-m_j|<r_V\varepsilon_j^2,\tag{3.2}$$

and a transverse *spin* profile germ of radius $r_\perp\varepsilon_j$ at $b=m_jh_*$. “Compatible” means agreement with (3.1) on the nonempty overlap and joint holomorphy in $\xi$ there. The germ (3.2) is an auxiliary continuation of a *reduced* density with its exact $b^2/(2m_j)$ field-only factor recorded separately. It is not a claim that the full density is bounded when $V/m_j$ is large. At $m_j=0$ use the physical path $b=0$; no joint holomorphic continuation of $b^2/m_j$ through $(0,0)$ is claimed. Old terms keep their birth convention and must be evaluated on the preimages of their own domains.

Here is a sufficient theorem, with the unproved analytic inputs named so that it cannot be mistaken for an established result.

> **Pinned switch theorem, conditional.** Suppose on a common open $\xi$ neighbourhood of $\|\xi\|_\infty\le c_{10}$ and on the three germs (3.1)–(3.2):
>
> 1. **PIN-FREE/AXIAL:** the physical $\mu_j=0$ fluctuation integral, after recording the exact field-only factor, and the old-term re-expression have localized coefficients bounded by a fixed $B_E$; their axial first jets and transverse spin second-moment jets have a fixed Cauchy margin. The full label, cutoff, and covariance construction is part of this assertion.
> 2. **PIN-COMPOSE/SWITCH:** both backgrounds, every inherited composition, and their interpolation lie in the appropriate old birth domains with strict margins; the switch action and old-action difference have a jointly analytic, covariant local expansion $\sum_YD_Y$, with the weighted polymer and $x_1^2$ moment bounds needed in P4 (5.15)–(5.17), and
> $$\sup_{z_0}\sum_{Y\ni z_0}e^{\kappa_a d_u(Y)}\sup_{\mathcal D^{\rm pin,+}}|D_Y|
> \le C_S\left(\beta_um^2+E_0\frac m{\varepsilon_u}\right).\tag{3.3}$$
> 3. **PIN-H7:** on the same physical field ball and $\|g\|_1<1$, the leading background difference and all marked old observable differences have a localized, $g$-analytic expansion at the required $3\kappa/2$ rate, with norm
> $$\|D_F\|_{3\kappa/2}\le C_F\left(m+c_9\frac m{\varepsilon_u}\right).\tag{3.4}$$
> 4. **PIN-I6/PROP:** the termwise irrelevant bound of P1 Proposition 3.10 and its scale sum hold on the actual pinned domains, with the same $C_IE_0\sigma^{3-\alpha_1}(\varepsilon_k/\varepsilon_j)^2$ coefficient as `I6-ANISO.md` (2.7). At each later complete-background step, the actual background and fluctuation composition maps send the output spin disc of radius $r_s\varepsilon_{j+1}$ and the three reference germs into every inherited birth domain with a fixed half-radius margin; the localized new coefficients obey the same H4/H7 norms on the output pinned domain. This assertion includes the physical old-term mixed cover and thermodynamic sum conditions; its domain and norm clauses are separate obligations.
>
> Then the two-step switch produces the complete-background RG system with the P4 (5.21) matrix and a forcing contribution satisfying
> $$\|f_{\rm sw}\|_\infty\le B_{\rm sw}\widehat\beta_u^{-1}\varepsilon_u^{-2},\qquad
> B_{\rm sw}=C_{\rm mom}C_S(C_L+E_0),\quad
> \widehat\beta_u^{-1}=(1+c_{10})\beta_u^{-1},\tag{3.5}$$
> after enlarging fixed constants if necessary. Its H7 correction is at most $\frac14c_9L^{-us}$ after the final $\beta_{\rm in}$ choice. The complete RG contraction therefore applies once PIN-FREE/AXIAL supplies the other forcing and the usual P4 smallness condition is imposed. This conclusion is conditional on all four inputs, not a proof of them.

**Proof of the scalar and algebraic parts.** On (3.1), $\|h\|\le1+r_h$. The background solution and its scaled derivatives are bounded on a fixed smaller spin/$\xi$ domain. The difference equation of `FLUCTUATION.md` Lemma 2.9(a), equivalently BG Proposition 5.1 with source $m(\phi^m-h)$, therefore gives $\|D\|_{\rm sf}\le C_Dm$ on that complex domain, provided PIN-COMPOSE supplies the common background margin. The exact chord identity gives

$$\left|\beta_u\{A_m(\Theta,\phi^0)-A_m(\Theta,\phi^m)\}\right|
\le C_Q\beta_um^2\quad\text{per output block}.\tag{3.6}$$

The constants $C_D,C_Q$ depend on the fixed background and block geometry, not on $m$ or $\beta_u$. In the one-block model $q=m(h-h_*)_\perp$ and (2.1) gives (3.6) directly. Cauchy on an old spin disc of radius $c\varepsilon_j$ bounds an individual old-term first variation by $CE_0m\varepsilon_j^{-1}e^{-\kappa d_j(X)}$ when its interpolation stays inside the old domain. Summing this with the required support and moment is precisely the **unproved** part of (3.3); scalar Cauchy alone does not construct a new-scale polymer expansion. Likewise $|\langle g,D\rangle|\le C_Dm\|g\|_1$ is proved, while its localized H7 form and the old marked sum are the unproved part of (3.4).

On (3.2), for $U,V$ in the stated discs and on the aligned branch, both backgrounds equal $h_*$; hence $D=0$ and both old compositions agree. The switch correction and its radial and longitudinal first reference jets vanish identically, even when $m=m(\xi)$ varies. The third reference jet is obtained by two Cauchy derivatives in the transverse *spin* profile at $b=m(\xi)h_*$. Assuming the $x_1^2$ moment in PIN-COMPOSE, P4 (5.15)–(5.17) charges $C_{\rm mom}\varepsilon_u^{-2}$, followed by the $\beta_u^{-1}$ in the divided equation. This proves (3.5) from (3.3); the switch's $\xi$ dependence stays inside $f_{\rm sw}$ and is **not** discarded or absorbed by changing the matrix. This is the complete-system splitting $A\xi+c=f$, with the ordinary P4 matrix (5.21).

For the scale comparison, the inductive coefficient bounds give $\beta_u\ge\frac12\beta_{\rm in}L^{u(d-2)}$ and $m\le C_L/\beta_u$. Therefore

$$\frac m{\varepsilon_u^2}\le2C_L\alpha_0^{-2}\beta_{\rm in}^{-1}L^{-2\gamma u},\quad
\frac{\sqrt m}{\varepsilon_u}\le\sqrt{2C_L}\alpha_0^{-1}\beta_{\rm in}^{-1/2}L^{-\gamma u},\tag{3.7}$$

and $\beta_um^2\le C_Lm$. Choose $\beta_{\rm in}$ last so $m\le\varepsilon_u^2$ and $m/\varepsilon_u\le1$ uniformly. Then (3.3) has a fixed bound and (3.5) follows. The P4 (5.29) scale comparison gives

$$\widehat\beta_u^{-1}\varepsilon_u^{-2}
\le2\alpha_0^{-2}\beta_{\rm in}^{-1}L^{-2\gamma u}.\tag{3.8}$$

For (3.4), the two ratios to the target satisfy

$$\frac m{c_9L^{-us}}\le2C_L\beta_{\rm in}^{-3/4}
L^{-u((d-2)/2-\gamma+\alpha_1)},\qquad
\frac{m/\varepsilon_u}{L^{-us}}\le2C_L\alpha_0^{-1}\beta_{\rm in}^{-1}L^{-u\alpha_1}.\tag{3.9}$$

Both are uniformly small after the final threshold. This proves the asserted H7 allowance **if** PIN-H7 supplies the localized norm. The usual contraction bound, with $B=B_{\rm free}+B_{\rm sw}$ fixed first, is the literal requirement $16\cdot42B\widehat\beta_u^{-1}\varepsilon_u^{-2}\max\{84\kappa_{\rm inf},1/c_{10}\}\le1$ of the abstract `rg_step_infty` interface; (3.8) allows the final $\beta_{\rm in}$ choice. The abstract theorem cannot supply PIN-FREE/AXIAL, PIN-COMPOSE/SWITCH, or PIN-H7.

Choose constants in this order: $d,N,L,\gamma,\alpha_1$; background, Green, cover, polymer-rate and entropy constants; $c_{10},r_h,r_s,r_U,r_V,r_\perp$ and strict domain margins; then the constants in the four named estimates and $B_{\rm free},B_{\rm sw}$; then $\alpha_0,E_0$ in the small-field induction's admissible order; finally $\beta_{\rm in}\ge\beta_*(\alpha_0,E_0)$ for (3.7)–(3.9), the background and cutoff margins, H7, and the contraction. No threshold uniform as $\alpha_0\downarrow0$ or $E_0\uparrow\infty$ is asserted. If $k_0=0$ only by the convention $\beta\nu>1$ of D-IV.11, there is no field-free input to switch; this theorem concerns a genuine crossing.

## 4. Why this domain passes the counterexamples, and what is still missing

At fixed $u$ and fixed $\varepsilon_u>0$, the `RGFREE-3.md` imaginary and `RGFREE-6.md` real test points have $|b_\perp|=\sigma\varepsilon_u^2$, independent of $m=\theta/\beta_u$. In (3.1), $|b_\perp|\le mr_h$ in an aligned frame (and at most $C m$ for general physical spin data), so those points leave the domain once $m<\sigma\varepsilon_u^2/r_h$. The cutoff test's growing factor $q\sqrt{\beta_u}$ is replaced by $O(m\sqrt{\beta_u})=O(\beta_u^{-1/2})$ on this path. On the larger possible switch tube $|b_\perp|\le c\sqrt m\varepsilon_u$ its Gaussian free energy is only $O(\beta_um\varepsilon_u^2)$; the pinned ball gives the stronger $O(\beta_um^2)$. The counterexamples thus no longer meet the domain hypotheses. This does not by itself prove the full Balaban cutoff activity or its localization.

The main unresolved point is **PIN-I6/PROP**. P1's proof uses a transverse complex-$h$ invariant disc whose $b$ radius is of order $\varepsilon_j$, while (3.1) only gives $O(m_j)$. `I6-ANISO.md` repairs the *shape* of the P1 Cauchy argument for an already bounded term on the larger disc; `RGFREE-6.md` shows that the physical switch and raw mass-free fluctuation correction are not bounded there. One must prove a replacement irrelevance theorem on the restricted physical locus, using spin Cauchy estimates, the aligned axial germ, exact mass factors and Ward identities, with the same scale gain; or explicitly build and estimate a source-resummed reference functional. The old-term domain preimages, fluctuation labels, mixed cover, $x_1^2$ moment, and marked H7 bounds are further independent obligations. `RGFREE-5.md` proves that the broader moving-background $\sqrt m\varepsilon$ tube does not automatically propagate from a source bound plus background closeness. A fixed $h$ ball avoids that *source-coordinate* mismatch, but it does not prove the old composition and XiC margins.

Boundedness on the pinned ball alone is not a substitute for PIN-I6: it gives no mass-uniform Cauchy estimate in an independent transverse $b$ coordinate. The proposed class must carry the axial bounds and the mass-weighted source/response estimates used in PIN-I6 as genuine hypotheses until they are derived from the physical fluctuation construction. At a constant aligned reference, the ordinary complex-background field inequalities do admit the pinned ball after $m r_h\ll\varepsilon_j^2$; this elementary inclusion does not provide those analytic estimates.

## 5. Changes required in the current reconstruction

* **Def-6 and Def-7.** Distinguish physical mass in the action from background mass in the solver, covariance and compositions. Replace a claim of uniform H4/H7 boundedness on the full transverse complex-$h$ XiC domain, at mass-free birth levels and their switch, by the pinned domains (3.1), compatible axial/profile germs (3.2), and birth-domain tags for inherited terms. Keep exact field-only factors explicit in the density identity. State physical real unit-field membership and $g$-analyticity separately. Do not infer a joint analytic family in independent $(m,b)$ through $m=0$ from physical-path continuity. The present landed `bgMass`-based XiDom makes $h$ unrestricted when that mass is zero; bounded holomorphic terms are then constant in constant $h$ by Liouville (`RGFREE-3.md` §1). That cannot encode the physical $-b\cdot\phi$ interaction for $m>0$.
* **FLUCTUATION.md.** In Lemma 2.9 keep the exact chord identity and its real $O(\beta_um^2)$ scalar consequence. Replace part (b)'s blanket complex localization bound by PIN-COMPOSE/SWITCH on (3.1); in part (c) retain all $\xi$ derivatives and use the aligned zero jets plus the transverse spin moment to obtain (3.5). In Theorem 3.1 and §3.6 add PIN-FREE/AXIAL, PIN-I6/PROP and PIN-H7 to the physical I-5/marked-cover premises. The existing real background response and abstract `marked_cubes`, `i5_background`, and `rg_step_infty` results do not jointly prove those assertions.
* **LF-RECONSTRUCTION.md.** D-IV.5's $O(\beta^{-1})$ switch is valid on fixed real $h$ and its pinned neighbourhood, but its claimed uniform full-XiC localized bound must be qualified. Theorem IV.2.2(e), its proof through FLUCTUATION Lemma 2.9, and the status row near Part IV's end must cite the four conditional inputs above; the two-step algebra and the a priori regime index D-IV.11 remain the correct organization. The combinatorial transfer at $k_0$ does not supply an analytic switch estimate. Any claim of a complete frozen step depends on proving the pinned old-term and I-6 propagation through the later complete-background steps.

**Status.** Equations (2.1), (3.6) on a common fixed-$h$ background domain, the aligned zero-jet identity, and the scale arithmetic (3.7)–(3.9) are proved or reduce directly to the named background response/chord identity. The polymer estimates (3.3)–(3.4), the physical mass-free activity, the restricted I-6 theorem, and full domain propagation are open. The opposite claim of a fixed H4/H7 bound on the full mass-uniform transverse polydisc is false by the exact one-block examples. This assessment concerns the analytic proof route, not the truth of the real-$h$ partition-function theorem.

### Source snapshot

P7 PDF SHA-256: `c48e08dd439878a0245cceb6e6aead787a8ce7671865f6360c8464a7e579d2e9`.

Read-only source hashes (SHA-256) used for this answer: P4 `804ba741c65367a4ba3e1ce84f0c415999a32de0ff2e1c337b41d9fa9104a303`; P5 `b3f0ef3491fc63b3988768893c1452b4bd1458a5f3e408e6af6000a555fd9a0f`; P6 `ee0ca061c9a7418d5da907a4dd09b66fb247f46bffcf68f83fa3ba502c342fc4`; P9 `eb78658c0bd5ca3807d85566ff8ccec809ab10af57424c2b845b37a97412d245`; `RGFREE-3.md` `b021cb287e864f188b5bcf0b18ad2bba224a224a4211694e007d68db6c1768c6`; `RGFREE-6.md` `548c51600b4beb0db28d58a531661b3ec0c3f36a5cb7d85d17c0903aa9679e08`; `LF-RECONSTRUCTION.md` `26b902a2bfd8f71c3e79ae32972c095f98efd29a60a4496840e0d6e3270eb101`. No file under `/home/scott/Balaban` was changed.
