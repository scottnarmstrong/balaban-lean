# Resolving $W^2$ by choosing the background convention

## Answer

I recommend **A**, with a specified interface: use complete backgrounds for the whole-lattice small-field action, its localized energy and observable terms, and its RG step at every scale, exactly as P1/P4 do. Retain field-free backgrounds inside the pre-$k_0$ large-field operators, where P5–P7 use them. Put the exact difference between the two main actions into the real-field large-field kernel, along with the re-expression of old terms. This leaves the classical transverse-source dependence in the complete small-field main action. The fluctuation integral about its true critical point has no linear source term and its one-block transverse-source Hessian is $O(1)$, not $O(\beta_j)$. P4 Theorem 1 (p. 680) includes arbitrarily small positive mass with complete backgrounds; P5 p. 490 says the zero-mass convention was introduced to simplify large-field analysis and was unnecessary for P1/P4's small-field analysis.

This recommendation is a **conditional construction**, not a completed proof of the revised large-field theorem. The interface chord costs $O(\beta_jm_j^2)$ per real unit-field block when $\beta_jm_j\le e^{2\epsilon}$, and inherited-term re-expression requires an $O(E_0m_j/\varepsilon_j)$ localized estimate. Both can fit a fixed large-field reserve after the stated order of choices, if their localization and common-collar hypotheses are proved. The chord has Hessian $\asymp\beta_j$ on the wide complex source disc and cannot be put into an $E_0$-bounded small-field term. LF-RECONSTRUCTION Definition II.5.2 allows the large-field kernel to depend measurably on real $h$ and asks for analyticity in the observable source $g$; this gives the chord a consistent home. The wide-complex claim for the separate switch chord in FLUCTUATION Lemma 2.9(b) fails the one-block test of PIN-JET and cannot justify this interface.

Scheme **B**, complete backgrounds also in large-field operators, eliminates the interface but requires new P7 window, characteristic, rotation and $R$ proofs. A small positive mass preserves coercivity with explicit losses, but an $O(\beta_jm_j)$ error can be $O(1)$ and must be canceled exactly, not discarded as a tiny remainder. Scheme **C**, a separately running transverse-source functional with field-free small-field backgrounds, changes the P1/P4 class and is unnecessary if A's interface lemma closes. None of these choices is certified by changing a mass definition alone.

## 1. Complete critical point: Gaussian and cutoff calculations

Use scale-$j$ units: $m_j$ denotes the coefficient of $|\phi-h|^2/2$ in P4/P5, $b_j=m_jh$, and $\beta_jm_j\le C_0:=e^{2\epsilon}$ for $j\le k_0$ by LF-RECONSTRUCTION D-IV.11. In fine units the coefficient is $\mu_j=m_jL^{-2j}$. P4 p. 676 (1.1), (H.1) keeps this mass in its action and its minimizer; pp. 691–693 (2.42)–(2.48) expands about that complete minimizer.

For one hard-spin block, $|p|=|\phi|=|h|=1$, let
$$
A_m(p,\phi)=\frac a2|p-\phi|^2+\frac m2|\phi-h|^2,\quad
v=ap+b,\quad s=\sqrt{v\cdot v},\quad \phi^m=v/s,\qquad b=mh. \tag{1.1}
$$
Take $a\in[9/10,3/2]$ and the square-root branch near $ap+me_1$. On the circle write $\phi=\cos t\,\phi^m+\sin t\,\tau^m$. Then exactly
$$A_m(p,\phi)-A_m(p,\phi^m)=s(1-\cos t). \tag{1.2}$$
There is no $b_\perp t$ term. With a cutoff $|t|\le R/\sqrt\beta$ centered at this complete critical point, put $x=\sqrt\beta t$. The normalized fluctuation factor is
$$
I_{\beta,R}(s)=\int_{-R}^{R}e^{-\beta s(1-\cos(x/\sqrt\beta))}\,dx
=I_R(s)+\frac{s}{24\beta}\int_{-R}^{R}x^4e^{-sx^2/2}\,dx+O_R(\beta^{-2}),
\quad I_R(s)=\int_{-R}^{R}e^{-sx^2/2}\,dx. \tag{1.3}
$$
The expansion and its first two $s$ derivatives hold uniformly on a fixed compact complex neighbourhood with $\operatorname{Re}s>a/2$. Since $I_R(a+m)>0$, a smaller neighbourhood has $|I_{\beta,R}(s)|\ge c_R>0$ for large $\beta$, uniformly as $m\downarrow0$. Thus its logarithm is analytic and bounded there independently of $\beta$. This uses a cutoff fixed in the complete fluctuation coordinate; moving a cutoff that was centered at the free background also changes the integration domain.

At $p=e_1$, $b=me_1+ze_2$, one has $s(z)=\sqrt{(a+m)^2+z^2}$, so
$$
\left.\partial_z^2\log I_{\beta,R}(s(z))\right|_{z=0}
=-\frac1{2(a+m)}
\frac{\int_{-R}^{R}x^2e^{-(a+m)x^2/2}\,dx}
{\int_{-R}^{R}e^{-(a+m)x^2/2}\,dx}+O_R(\beta^{-1}). \tag{1.4}
$$
This is $O(1)$; without cutoff its leading value is $-1/[2(a+m)^2]$. For $N$ spin components the tangent Gaussian gives $-(N-1)\log s/2$ at leading order. On a fixed complex disc $|b_\perp|\le c\varepsilon_j$, $|b_\parallel-m|\le c\varepsilon_j^2$, $|p-e_1|\le c\varepsilon_j$, a sufficiently small $c$ keeps $s$ in the zero-free neighbourhood. After subtracting its vacuum value, the one-block logarithm is bounded by a constant independent of $m,\beta$, compatible with a fixed $E_0$ as chosen in P4 (5.39). The full localized bound still uses P4's complete-background proof.

By contrast, the free-center cutoff has a term $\sqrt\beta\,b_\perp x$. Its Gaussian log has the $\beta b_\perp^2/[2(a+m)]$ term, and the fixed-cutoff Hessian is $\beta\operatorname{Var}_{a+m,R}(X)$, as in W2-TERM. The complete convention moves that order-$\beta$ dependence into $-\beta A_m(p,\phi^m)$; it does not erase it from the full partition function.

## 2. Exact uses of the field-free convention

The table gives the cited use and the status of each scheme. A statement labeled “repeat” needs a new proof; small mass alone is not that proof.

| Source or landed site | What zero mass does | A | B |
| --- | --- | --- | --- |
| P5 pp. 489–490 (1.5)–(1.9), p. 492 (1.19) | The action keeps the physical mass; the pre-$k_0$ background and characteristic omit it. P5 (1.8) uses whole-lattice $v_1,v_2$ corrections. | Retain this convention only in LF. Give SF the complete P4 background. Add the exact interface identity in §3. | Use physical mass in all solvers and revise the characteristic conditions. Keep (1.8). |
| P5 pp. 503–504 (2.12)–(2.13); P6 pp. 10–11 (2.24)–(2.25) | The zero-mass variational equation leaves $m_{k+1}h\cdot\delta\phi$ in the pre-$k_0$ fluctuation counterterm. The $k_0$ two-stage conversion adds $-\beta C$. | SF uses P4's complete step. The printed LF free step stays; the interface is charged to its kernel. No SF birth switch is needed. | The complete P4 step runs throughout. Recompute LF covariance and localization; the extra linear term and SF two-stage conversion disappear. |
| FLUCTUATION §2.8, Lemma 2.9(a)–(c) | The pre-$k_0$ free convention produces the chord at the switch. Part (a) gives the exact stationary quadratic identity and real response; part (b) also claims a wide-complex localized bound for the separate chord. | Use (a) for the real LF interface and reprove localization with the common collar. The separate wide-complex bound in (b) fails (3.3), so it supplies no SF step. | There is no convention switch in SF or LF; replace this lemma by the ordinary complete step and the new complete LF estimates. |
| P7 pp. 496–497 (1.5)–(1.7), Theorem 2 | The $R$ numerator and denominator use the same free reference action, so their main actions cancel. | Retain this exact $R$ denominator. The interface factor is in the numerator kernel and must be bounded; normalization (1.7) remains algebraic. | Redefine numerator and denominator with the same complete reference. Reprove their cancellation and bounds. |
| P7 pp. 506–509 (2.34)–(2.45), Lemmas 2.1–2.4 | The window minimizer solves (2.34) with $\nu_k=0$, is independent of $h$, and has Dirichlet coercivity $\gamma_0/72$ in (2.38). The composition comparisons use it. | Retain the minimizer. Compare complete SF backgrounds to it only in the interface lemma, with common collar data. | Repeat the lemmas with $h$ as data. If the Hessian perturbation is at most $C_Hm$ along the segment of solutions and $m\le\gamma_0/(144C_H)$, coercivity is at least $\gamma_0/144$ and inverse norm at most $144/\gamma_0$. A forcing at most $C_Fm$ changes the minimizer by at most $144C_Fm/\gamma_0$; require that quantity to be at most $K_6\delta_k$ to replace $K_6\delta_k$ by $2K_6\delta_k$. Reprove composition with the same mass and collar on both sides. |
| P7 §3, pp. 521–522 around (3.7), (3.10) | The window fields and fluctuation action are $h$-independent; P7 uses analyticity only in the spin and spin-only equivariance $\psi_k^0(R\psi)=R\psi_k^0(\psi)$. | Printed LF argument remains, apart from the bounded, jointly covariant interface factor. | Replace spin-only equivariance by $\psi_k^0(R\psi,Rh)=R\psi_k^0(\psi,h)$. Recheck rotation/coset and spin-analytic estimates with $b=mh$; response is $O(m)$ on bounded real $h$ and $O(|b|)$ on the complex $b$ disc. |
| LF-RECONSTRUCTION (A-III.2), Lemma III.3.3, §III.5.2, Theorem III.8.9 | All pre-$k_0$ LF backgrounds and five $R$ indicators are zero-mass and $h$-free. Small factors and the removed outcome use this architecture. | Retain it; add interface cost to the kernel reserve and an SF/LF bridge to IsRep. | Redo minimizer, indicators, small factors, $R$ and their normalization. Definition II.5.2 permits Borel real-$h$ dependence of the kernel and asks for $g$ analyticity, so $h$-dependent indicators are admissible after support/covariance/bound proofs. |
| LF-RECONSTRUCTION D-IV.11, D9/D9♭, IV.2.1–IV.2.2 | $k_0$ is fixed a priori; $\beta_jm_j\le e^{2\epsilon}$ below it. IV.2 transfers backgrounds; the SF two-stage step appears in IV.2.2(e). | Keep $k_0$ as the LF $R$ stop and LF convention boundary. SF uses ordinary P4 RG through $k_0$; IV.2.1 transfers LF data only. | Keep $k_0$ only as $R$ stop and D9/D9♭ threshold. Background transfer is the identity; SF step is ordinary P4. |

For B, complex coercivity follows from the same estimate if $C_H|b|\le\gamma_0/144$, chosen by shrinking the fixed P1/P3 source-disc constant before choosing $\beta$. The characteristic bridge needs a further inequality: for real unit $h$, $m_j(1-p_0\cdot h)\le2m_j$. At its test radius $\theta_j=\delta_j/(6K_1)$ require $2m_j<c_\Xi\theta_j^2$. The landed small-factor relation $\beta_j\delta_j^2=A_0^2\lambda_j^{2p_0}/a$ then makes
$$A_0^2\lambda_j^{2p_0}>72aK_1^2C_0/c_\Xi \tag{2.1}$$
sufficient. Here $C_H,C_F,c_\Xi$ are constants a new complete-mass window theorem must supply. The current zero-mass premises occur explicitly in LargeField/R/ChiBridge.lean (chiK_eq_one_of_psiTilde, not_psiTilde_of_cubeProd_eq_zero), R/ChiBridgeHist.lean (smallFactor_two_hist, smallFactor_five_hist), and R/HgeoDischarge.lean (the corresponding history discharges assume cs.mu k = 0). By contrast, R/SmallFactorAction.lean, R/SmallFactorOne.lean, R/WindowGenCompose.lean and Operators/MainAction.lean contain algebra and nonnegativity results parameterized by a nonnegative mass. Operators/Quiet*.lean uses cs.mu for characteristics and cs.muAct for the physical action. Those generic statements survive B only after their changed data premises are supplied.

The mass term must be incorporated **exactly** into B's new main-action and $R$ identities. Merely comparing complete and free exponents loses $O(\beta_jm_j)=O(1)$ per block, far larger than the $\beta_j^{-n}$ polymer remainders of P7 §3 and LF-RECONSTRUCTION Theorem III.8.9. This is the main cost of B.

## 3. Scheme A: the SF/LF interface

Use the same generating set, physical action, data, and Dirichlet collar for the two backgrounds. Write $\phi^m(D)$ and $\phi^0(D)$ and let $\psi^{(r),m},\psi^{(r),0}$ be their composed old-level fields. Then the conversion is the **exact density identity**
$$
-\beta_j A_j^{\rm phys}(D,\phi^m)+E_j(\psi^{(r),m})+F_j(\psi^{(r),m};g)
=-\beta_j A_j^{\rm phys}(D,\phi^0)+E_j(\psi^{(r),0})+F_j(\psi^{(r),0};g)
+D_{j,D}+\Delta E_{j,D}+\Delta F_{j,D}(g), \tag{3.1}
$$
with
$$
D_{j,D}=\beta_j[A_j^{\rm phys}(D,\phi^0)-A_j^{\rm phys}(D,\phi^m)],\quad
\Delta E_{j,D}=E_j(\psi^{(r),m})-E_j(\psi^{(r),0}),\quad
\Delta F_{j,D}=F_j(\psi^{(r),m};g)-F_j(\psi^{(r),0};g). \tag{3.2}
$$
Here $E_j,F_j$ denote the appropriate sum of inherited terms, not a new coupling. The sign of $D$ is positive because (3.1) expresses a complete-reference density using a free reference; P6's $-\beta C$ has the reverse direction. Put $e^{D+\Delta E}$ into the real-$h$ LF kernel (or its scalar exponent with the same kernel bound) and $\Delta F$ into the $g$-analytic kernel exponent. This preserves exact normalization if the same LF reference is used in P7 (1.6)'s numerator and denominator. It also preserves joint $O(N)$ covariance. The conversion must be made on the LF region and its collar, with no double counting on the SF complement; the common-collar identity or separate collar bound of COLLAR-RULING is required.

Identity (3.1) applies only on the overlap where both background maps and their inherited terms are defined, after the P7 window data have been regularized. It does not assign a complete background to an unrestricted large-field core. Extending the overlap identity to the whole $R$ kernel requires a local gluing theorem at the collar, including the cutoff and normalization factors. That theorem is part of the open interface obligation.

For (1.1), at $p=e_1$, $b=me_1+ze_2$, the chord is
$$D_m=\beta\{\sqrt{(a+m)^2+z^2}-(a+m)\},\qquad
\partial_z^2D_m(0)=\beta/(a+m). \tag{3.3}$$
For $p_\vartheta=\cos\vartheta e_1+\sin\vartheta e_2$ and real unit $h=e_1$, rationalization gives
$$
D_m(p_\vartheta,me_1)
=\frac{\beta m^2\sin^2\vartheta}
{\sqrt{a^2+2am\cos\vartheta+m^2}+a+m\cos\vartheta}
\le C_a\beta m^2\sin^2\vartheta. \tag{3.4}
$$
For any real unit orientation it is $O(\beta m^2)$ if $m<a/2$. On a bounded pinned complex chart $b=mh$, $|h-h_*|\le r_h$, it is likewise $O(\beta m^2)$, with a chart constant. On the wide P1 disc $|z|\asymp\varepsilon_j$ independent of $m$, it is $O(\beta\varepsilon_j^2)$ and unbounded in the class norm. The chord therefore belongs to the real-field LF kernel, not to the wide-complex SF $E_j$. This preserves FLUCTUATION Lemma 2.9(a)'s chord identity and its real $O(\beta^{-1})$ consequence while rejecting its separate wide-domain bound.

The needed **Interface Lemma** is a precise reduction. Assume a common collar, weighted background response $\|\phi^0-\phi^m\|_{\rm loc}\le2K_2m_jB_h$ for real $|h|\le B_h$, localized Hessian bound $C_H$, and complete-background Cauchy/first-variation bounds for inherited $E,F$. Then the stationary chord identity gives
$$
|D_{j,Y}|\le2C_HK_2^2B_h^2\,\beta_jm_j^2e^{-\kappa_Dd_j(Y)}
\le2C_HK_2^2B_h^2C_0^2\beta_j^{-1}e^{-\kappa_Dd_j(Y)}. \tag{3.5}
$$
The companion estimates to prove are
$$
|\Delta E_{j,Y}|\le C_EE_0(m_j/\varepsilon_j)e^{-\kappa_Ed_j(Y)},\qquad
|\Delta F_{j,Y}(g)|\le C_FE_0(m_j/\varepsilon_j)e^{-\kappa_Fd_j(Y)}
\quad(\|g\|_1<1). \tag{3.6}
$$
The constants $C_E,C_F$ and rates are named proof inputs, not claims printed in P5–P7. Sum old levels using the P1 Corollary 3.11 scale weights. The desired top-block LF cost is $C_{\rm int}[\beta_km_k^2+E_0m_k/\varepsilon_k]$. Choose LF reserve and localization geometry first, then complete source-domain margins and $E_0$, and lastly initial $\beta$ so that
$$C_{\rm int}[C_0^2/\beta_k+C_0E_0/(\beta_k\varepsilon_k)]<\eta_{\rm LF} \tag{3.7}$$
at each pre-$k_0$ scale. Under the P4 sequences $\beta_k\varepsilon_k$ increases, so after fixed comparison constants the initial scale is restrictive. The localized response, level sum, collar identification, exact kernel support, and budget are still open. In particular (3.5)–(3.6) are **real or bounded-pin estimates**, not wide-complex bounds.

## 4. Regime, class clauses, and landed theorems

Retain the a priori $k_0$ of D-IV.11 as an **LF regime index**. A revised Regime has the physical fine mass $\mu_j=m_jL^{-2j}$ and two explicit solver masses:
$$
\mathrm{sfBgMassAt}(j)=\mu_j\quad\text{for all }j,\qquad
\mathrm{lfBgMassAt}(j)=
\begin{cases}0,&j\le k_0,\\ \mu_j,&j>k_0.\end{cases} \tag{4.1}
$$
The bgMassAt proposed in CLASS-RULINGS-2 becomes lfBgMassAt; it must not be fed to SF XiDom. Def-6's whole-lattice density uses the physical mass in its action and a complete background. Its energy/observable terms use the P1/P4 wide complex XiDom in $b_j=m_jh$ and the independent $\|g\|_1<1$ domain. P4 complete RG equations run at every scale. Def-7 uses cs.mu for its LF solver and characteristic (zero below $k_0$), cs.muAct for the physical action, and cs.muAct for the SF action now called sfActMass. Add (3.1)–(3.7) as an SF-to-LF interface clause of IsRep, with scalar correction in the real-$h$ kernel and observable difference analytic in $g$. The frozen root's fixed real unit $h$ lies in this class.

The following Lean results remain valid **conditionally on their existing premises**: the complete-background BG statements, the algebraic P1/P4 SF Cauchy/Ward/I-6 statements, IsSFFamily.renormalization_aniso and its scaled variant when a complete-background member supplies PremisesTermAniso, the generic nonnegative-mass action lemmas in LargeField/R/SmallFactorAction.lean, R/SmallFactorOne.lean, R/WindowGenCompose.lean and Operators/MainAction.lean, and the algebraic normalization of P7's $R$ ratio with a common LF reference. They do not construct the revised IsRep or prove (3.5)–(3.7).

The following bridges and theorem instances must be redone: SmallField/Def6Terms.lean bgMass/XiDom, SmallField/Def6.lean IsSF/IsSFFamily and the RenormAnisoBridge class instantiation with complete backgrounds at every level; the actual complete SF fluctuation/RG step at pre-$k_0$ levels; LargeField/Def7.lean FieldClauses.mu_eq, Def7SmallField.lean sfActMass, Def7Inhabited.lean and Def7Variants.lean; a new SFtoLFInterface proving (3.1)–(3.7) as kernel data; and LF-3/LF-4/LF-5 at that interface. The existing zero-mass R/ChiBridge, R/ChiBridgeHist and R/HgeoDischarge proofs **survive A** because LF backgrounds remain free until $k_0$. Operators/Quiet retains cs.mu for its LF characteristic and cs.muAct for its action, but its input bridge to the revised SF class changes. At $k_0$, LF-RECONSTRUCTION IV.2.1 transfers LF data only; IV.2.2(e)'s SF two-stage switch is replaced by the ordinary complete P4 step. Other named localization, modular, collar and observable gaps remain.

If the Interface Lemma fails its LF budget, B is the next no-new-sector choice, beginning with complete-mass replacements for P7 Lemma 2.1 and the characteristic bridge. Returning to a field-free SF class requires the separate-sector or grouped-cancellation work in W2-TERM. This is a recommendation conditional on explicit estimates, not a claim that the reconstructed large-field theorem is proved.

**Status.** Equations (1.2)–(1.4) and (3.3)–(3.4) are direct one-block computations. P4's complete convention and the listed zero-mass uses are source facts. Equations (3.5)–(3.7), the collar bridge and revised Def-7 preservation are open proof obligations. No file under /home/scott/Balaban was changed.
