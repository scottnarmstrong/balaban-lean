# The transverse-source $W^2$ term before the switch

## Answer

The $W^2$ term is present at ordinary field-free fluctuation steps, not just in the change of background at $k_0$. In a one-block Gaussian calculation its coefficient is $\beta_j/(2(a+\nu_j))$ in the one-block mass action, and the cutoff version still has a transverse source Hessian of order $\beta_j$. Balaban's P1 renormalization analysis does **not** give $\partial_{W^2}f$ its own recursion. It bounds that derivative by Cauchy's theorem from the inductive $E_0$ bound on a complex source disc whose radius in $b_\perp=\nu_jh_\perp$ is of order $\varepsilon_j$, independent of $\nu_j$ and $\beta_j$. The real configurations in P1 (3.13) occupy a smaller, mass-dependent angular region; that fact alone cannot justify the complex bound. P3 (4.26) is the complex perturbation part of the same type of domain, not a rewriting of the real condition in (3.13).

The conditional P1 I-6 calculation is correct *given* its wide complex bound: the isolated $W^2$ remainder at a birth centre is $O(E_0\sigma^4(\varepsilon_k/\varepsilon_{j+1})^2)$; after counting centres in dimension three it is $O(E_0\sigma(\varepsilon_k/\varepsilon_{j+1})^2)=O(E_0\sigma^{2-2\gamma})$, up to fixed comparison constants. Its coefficient scales by $L^{d-4}=L^{-1}$ in $d=3$ under transport of an **already bounded** $b^2$ term. A freshly generated coefficient of order $\beta_j$ need not satisfy the required bound. A thin, mass-dependent complex tube can bound that new term at birth, and includes the physical real $h$ when the usual large-$\beta$ choices hold, but it does not imply P1's I-6 rate or the landed `IsSFFamily.renormalization_aniso` conclusion. On the printed hypotheses and the one-block test, a no-extra-sector induction is unproved; its missing assertion is a cancellation or resummation of the complete transverse-source free energy at **every** field-free step, not merely at the switch.

## 1. Source record: two transverse radii

Write $p_0=p/|p|$, $b=\nu_jh$, and $\sigma=L^{j-k}$. P1 p. 123 (3.13) defines its real space by, among other inequalities,
$$
 |\nu_j(1-p_0\cdot h)|<\sigma^2\varepsilon^2,
 \qquad |\nu_j(h^2-1)|<\sigma^2\varepsilon^2. \tag{1.1}
$$
For a real unit $h$ the first inequality gives
$$
 |b_\perp|^2=\nu_j^2\{1-(p_0\cdot h)^2\}
 \leq 2\nu_j\sigma^2\varepsilon^2, \tag{1.2}
$$
for any real unit $p_0,h$. Thus its physical transverse radius is $O(\sigma\varepsilon\sqrt{\nu_j})$. P1 p. 123 (3.14), however, permits a complex increment $h'$ satisfying $|\nu_jh'|<\sigma^2\varepsilon$ and $|\nu_jp_0\cdot h'|<\sigma^2\varepsilon^2$. The transverse increment in $b$ can therefore have radius $O(\sigma^2\varepsilon)$, with no factor $\sqrt{\nu_j}$. P1 p. 124 (3.18)–(3.22) uses analogous intermediate spaces to transport background configurations into the induction space; p. 125 explains why these intermediate spaces cannot replace the induction space.

The radius actually used in the constant-potential Cauchy argument is explicit. In P1 p. 126 (3.25)–(3.28), write $p=u e_1$, $b=\nu_j v e_1+\nu_j w e_2$ and
$$
 f(u,\nu_jv,\nu_j^2w^2)=\mathcal V(u e_1,\nu_jv e_1+\nu_jw e_2).
$$
P1 p. 127 (3.29) takes $|w|<\delta_0^2/(\sqrt2\,\nu_j\varepsilon_0)$, and (3.31) takes a slightly smaller disc. Hence $|b_\perp|$ has radius $\delta_0^2/(\sqrt2\varepsilon_0)$, independent of mass. In the application $\delta_0=\sigma_1\varepsilon_{j+1}$ and $\varepsilon_0=\varepsilon_{j+1}$, so this is $c\varepsilon_{j+1}$. P1 (3.30) bounds $\partial_{(\nu_j^2w^2)}f$ by $O(E_0K_0\varepsilon_0^2/\delta_0^4)=O(E_0K_0/\varepsilon_{j+1}^2)$; (3.32) puts $f_{0,0,1}\nu_j^2w^2$ into the Taylor **remainder**, with the explicit bound in (3.33). There is no value or recursion for $f_{0,0,1}$ among the renormalized coefficients.

P3 p. 74 (4.25)–(4.26) places the real data in $\Xi_j$ and separately allows a complex $h'$ with $|h'|<\nu_j^{-1}\sigma^2(B_j;y)(L^n\xi)^{-2}\varepsilon$ and $|\phi(x)\cdot h'|<\nu_j^{-1}\sigma^2(B_j;x)(L^n\xi)^{-2}\varepsilon^2$. At the top scale, multiplication by $\nu_j$ again gives a transverse complex radius of order $\varepsilon_j$. These formulas agree in their *complex perturbation* scaling with P1 (3.14), subject to P3's geometry factors. Neither turns the real bound (1.2) into a mass-independent disc. The coordinate change $b=\nu_jh$ explains the factor $\nu_j^{-1}$ in (4.26), but it does not identify the real and complex parts of the domain.

P4 p. 707 (5.1) again writes the potential as $f_{k+1}(U,V,W^2)$, then expressly studies $f_{k+1}(u,v,0)$ for the potential renormalization conditions. P4 pp. 708–711 (5.5), (5.14) supplies the equations for the existing constants, and pp. 713–715 (5.20)–(5.26) closes a three-variable system after choosing the two free equations. It supplies no equation for $\partial_{W^2}f$. P1 p. 138 (3.73)–(3.76) also uses $W^2$ in coefficient functions for spin derivatives; its $v_2$ is a spin-derivative coefficient, not an independently running $W^2$ potential coupling. P1 pp. 146–153 (3.104)–(3.128), Proposition 3.10 and Corollary 3.11, deduce irrelevance from (H.2)–(H.7), including the complex bound (H.5) on p. 117. They do not prove that a field-free fluctuation step creates a term satisfying that bound.

## 2. What I-6 proves, and its premise

On the evaluation space, P1 pp. 128–129 (3.37)–(3.44) gives, with $\nu_j\leq\sigma^2$,
$$
 |U-1|<2\sigma^2\varepsilon,
 \quad |\nu_j(V-1)|<22\sigma^2\varepsilon^2,
 \quad |\nu_j^2W^2|<56\sigma^4\varepsilon^2. \tag{2.1}
$$
The last power is $\varepsilon^2$, not $\varepsilon^4$. Combining the $W^2$ term of P1 (3.33) with $\delta_0=\sigma_1\varepsilon_{j+1}$ gives, for one birth centre and a term of norm $M_X$,
$$
 |R_{W^2,X}|\leq C M_X\sigma^4
       (\varepsilon_k/\varepsilon_{j+1})^2. \tag{2.2}
$$
There are $O(\sigma^{-d})$ birth centres per current-scale block. Thus the contribution of (2.2) is $O(E_0\sigma^{4-d}(\varepsilon_k/\varepsilon_{j+1})^2)$; in $d=3$, since $\varepsilon_k/\varepsilon_{j+1}\asymp\sigma^{1/2-\gamma}$ for a fixed shift of one level, this is $O(E_0\sigma^{2-2\gamma})$. The full spatial Taylor argument is weaker: P1 p. 147 (3.107)–(3.108) gives a birth-centre rate $\sigma^{3-\alpha_1}(\varepsilon_k/\varepsilon_{j+1})^2$ and a current-block rate $\sigma^{\alpha_3}$, $\alpha_3=1-2\gamma-\alpha_1>0$. This distinction matters: the $W^2$ direction is more irrelevant than the worst spatial term **once the same $E_0$ bound holds on the wide disc**.

For a pre-existing local term $q_j b_\perp^2$, block counting and $b_j=L^{-2}b_{j+1}$ give $q_{j+1}=L^dL^{-4}q_j=L^{d-4}q_j$ before new production or mixing. In $d=3$ that homogeneous factor is $L^{-1}$. It does not bound the birth input $q_j$; a new $q_j\asymp\beta_j$ occurs at each field-free fluctuation step. P1's (3.30) would require $|q_j|\lesssim E_0/\varepsilon_j^2$, uniformly in mass and temperature. When $\beta_j\varepsilon_j^2$ is large, these requirements conflict.

## 3. Direct field-free test and the switch

Take one transverse fluctuation $X$ with covariance $(\beta_j A_j)^{-1}$, where $A_j=a+\nu_j$ and $a$ is bounded above and below away from zero. Keep $b=\nu_jh$ in the main action while choosing the background at $b=0$. The source part of the normalized fluctuation integral is
$$
 Z_j(b_\perp)=\mathbb E\exp(\beta_j b_\perp X)
       =\exp\{\beta_jb_\perp^2/(2A_j)\}. \tag{3.1}
$$
Thus $\partial_{b_\perp}^2\log Z_j(0)=\beta_j/A_j$. With a symmetric bounded cutoff $|\sqrt{\beta_j}X|\leq R$ of fixed positive radius, the exact identity becomes $\partial_{b_\perp}^2\log Z_j(0)=\beta_j\operatorname{Var}(\sqrt{\beta_j}X)$, and the variance remains bounded above and below by positive constants for the corresponding truncated Gaussian. The coefficient is still of order $\beta_j$. This is an elementary test of the source convention, not an assertion that every polymer coefficient of the full RG equals (3.1); a cancellation with other terms would need a separate identity and bound.

The invariant one-site function
$$
 Q_j(p,b)=\frac{\beta_j}{2A_j}
   \left(b\cdot b-\frac{(p\cdot b)^2}{p\cdot p}\right) \tag{3.2}
$$
has exactly the transverse jet of (3.1). It vanishes on the axial germ $(p,b)=(u e_1,v e_1)$, so the value, radial-spin and longitudinal-source potential conditions do not remove it. It is a one-site term, so its spatial second moment is zero. It satisfies the algebraic renormalization conditions used in P1 (H.6)–(H.7) while violating the $E_0$ bound on the mass-independent transverse disc whenever $\beta_j\varepsilon_j^2\gg E_0$. At a pinned real unit $h$, its size is controlled by (1.2) and $\beta_j\nu_j\leq1$:
$$
 |Q_j(p,\nu_jh)|\leq C\beta_j\nu_j\sigma^2\varepsilon_k^2
             \leq C\sigma^2\varepsilon_k^2. \tag{3.3}
$$
This makes its physical value small, but does not give (2.2). For example set $\nu_j=c\sigma^2$, $\beta_j\nu_j=\theta_0$ for a fixed $0<\theta_0<1$ (so $j$ may precede $k_0$), and choose a pinned angular displacement $\vartheta=\varepsilon_k/2$. Then $Q_j\asymp \theta_0c\sigma^2\varepsilon_k^2$, whereas the full landed one-term I-6 target is $CE_0\sigma^{3-\alpha_1}(\varepsilon_k/\varepsilon_j)^2$. Their ratio grows like $\sigma^{-(1-\alpha_1)}$ with fixed $\varepsilon_j,E_0$. This is the same power obstruction as `PIN-I6.md` §2, now at a regular field-free birth step. Its source Hessian is the ordinary-step counterpart of the separately localized switch chord in `PIN-JET.md` §2.

P5 pp. 489–490 (1.8)–(1.9) says that for $\beta_k\nu_k\leq1$ the mass is omitted from the background variational problem while its term is kept in the main action as a perturbation. It also says the $E^{(j)}$ still satisfy P4's whole-lattice induction hypotheses. P6 p. 11, following (2.25), identifies the extra $\nu_{k+1}h\cdot\delta\phi_{k+1}$ term for $k<k_0$ and the two-stage switch term $-\beta_{k+1,u}C^{(k+1)}$ at $k_0$. P6's switch bound (2.25) and two-stage description control the stated class-domain value of that change, but neither supplies a uniform transverse $b$-Hessian bound after grouping it with the field-free fluctuation free energy. The printed source therefore does not resolve the conflict between (3.1) and the wide complex (H.5) premise. The exact one-block cut-off examples in RGFREE-3 §2.1 and RGFREE-6 §§2–4 show the same failure beyond a purely Gaussian approximation; restricting to real $h$ removes their wide-complex test point, but also removes the Cauchy premise used for (2.2).

On the physical submanifold $h^2=1$, one may write $W^2=\nu_j^2-V^2$ and trade a quadratic $W^2$ value for a longitudinal potential. This is a possible *different renormalization convention*, not an identity of analytic functions in the independent variables $(V,W^2)$: P1 (3.13) includes an open real range with $h^2\ne1$, and P1 (3.14)/(3.29) varies the complex transverse source independently. P4 (5.1)/(5.5) differentiates $f(u,v,0)$, so its displayed longitudinal counterterm does not automatically subtract (3.2). P1 p. 147 comments that its constructed analytic extensions may differ from assumed extensions after the real-field decomposition; it does not give a uniform bound for the germ of the specific free fluctuation logarithm (3.1) on the wide disc. A convention based solely on the unit-field quotient would require new renormalization and localization statements for the quotient class.

## 4. Correct class and corrected I-6 obligation

Here is a minimal logically consistent *separated-sector* formulation. It states the extra estimates that must be proved; it is not a theorem of P1–P6. Fix the ordinary constants $L,M,\gamma,\alpha_1,E_0,\kappa$ and the $\varepsilon_j$ sequence first, then take the initial $\beta$ large enough for P4 (5.27) and, near $k_0$, $\beta_j^{-1/2}\leq c\varepsilon_j$. For a local centre $p$ with $p\cdot p$ near $1$, use the analytic projection
$$
 b_\parallel(p)=\frac{p\cdot b}{p\cdot p}p,
 \qquad b_\perp(p)=b-b_\parallel(p),
 \qquad r_j^\perp=c_\perp\min\{\varepsilon_j,\varepsilon_j/\sqrt{\beta_j}\}. \tag{4.1}
$$
On the field-free levels let the **energy** source tube have spin radius $c_s\varepsilon_j$, longitudinal $b$ radius $c_\parallel\varepsilon_j^2$, and transverse radius $r_j^\perp$ in (4.1), with its rotation orbit and the usual real-base conditions (1.1). At an evaluation scale impose additionally the P1 conditions with $\sigma,\varepsilon_k$, and restrict its complex source increment so that $|b'_{\perp}(p)|<r_j^\perp$ with a fixed half-margin. On the real unit pin, (1.2) and $\beta_j\nu_j\leq1$ give $|b_\perp|\lesssim\sigma\varepsilon_k/\sqrt{\beta_j}$, so this restriction is compatible whenever the fixed margins and $\varepsilon_k\leq C\varepsilon_j$ hold. The full background regime may use the P1/P3 wide tube only after its own analytic birth estimate has been established. This is a two-radius domain; shrinking the single `r` of the landed `polyAniso` would also shrink the spin radius and changes the spatial Taylor estimates.

The corrected I-6 statement must separate a wide-bounded remainder $R_{j,X}$ from the transverse free energy $Q_{j,X}$:
$$
 E_{j,X}=R_{j,X}+Q_{j,X},\qquad
 \|R_{j,X}\|_{\mathrm{wide}}\leq E_0e^{-\kappa d_j(X)}, \tag{4.2}
$$
$$
 |I[R_{j,X}]|\leq C E_0e^{-(\kappa-1)d_j(X)}
       \sigma^{3-\alpha_1}(\varepsilon_k/\varepsilon_j)^2, \tag{4.3}
$$
with the P1 one-term proof and Ward cancellations applied to $R$, and a **separate** thin-tube estimate and RG rule for $Q$. The required birth estimate has the form
$$
 |Q_{j,X}(p,b)|\leq C_Q\beta_j|b_\perp(p)|^2e^{-\kappa_Qd_j(X)}
       +\text{controlled higher source terms}, \tag{4.4}
$$
on the tube (4.1), with a zero-free analytic fluctuation logarithm there. Its homogeneous quadratic coefficient transports with $L^{d-4}$; every free step also has a new source term, so its recursion must contain an inhomogeneous birth contribution of order $\beta_j$. A scalar quadratic coupling suffices for the exact Gaussian (3.1). For the cutoff integral, subtraction of only its quadratic Taylor polynomial need not give a wide-bounded remainder: at fixed $b$ outside the thin tube the logarithm is not uniformly quadratic. A consistent general construction therefore tracks or resums the whole local transverse-source free energy, or proves a direct grouped cancellation restoring (4.2). Its closure also needs a summable physical-path estimate for the transported $Q$ sector and source compatibility with the observable $g$ sector. P1–P6 give no such full estimate or recursion in the cited passages. Thus (4.1) gives a coherent domain for the value of field-free and switch terms, but **does not by itself close the induction with no additional sector**.

In the landed definitions, `Def6Terms.lean:XiDom` uses `XiC` at $\sigma=1$ and the background mass `bgMass`; on free levels `bgMass=0` although the physical source remains $b=\nu_jh$. A corrected `XiDom` needs the *physical* $\nu_j$, $\beta_j$ and the separate transverse constraint (4.1), alongside the existing background mass for variational equations. `RenormAnisoDefs.lean:anisoWt/polyAniso/TubeAniso` currently set spin and transverse radii equal to `r` and the longitudinal radius to `r²`; they need independent spin, longitudinal and transverse radii, with a corresponding rotation orbit. `RenormAnisoCtx.lean:PremisesTermAniso` currently asks for the full $E_0$ bound on `TubeAniso`; the corrected class must apply that bound only to $R$, and state the thin analytic and weighted bound for $Q$ separately. The existing `IsSFFamily.premisesTermAnisoInf`, `IsSFFamily.termwise_irrelevant_aniso_class`, and `IsSFFamily.renormalization_aniso`, and `IsSFFamily.renormalization_aniso_scaled` theorems remain valid **as conditional Lean implications under their current wide-tube hypotheses**; a thin-tube member does not furnish those hypotheses. The scalar Cauchy, Taylor, Ward, rotation, and counting lemmas survive for the $R$ sector. Their bridge from the modified `XiDom`, the `Q` transport and physical-path sum, the switch grouping, and the final class theorem must be redone. Replacing `r` by $r_j^\perp$ in the present I-6 theorem produces a Cauchy loss of order $\beta_j$ in transverse derivatives and cannot prove (4.3) for $Q$.

The frozen-root theorem `Balaban/Frozen/Roots/LogPartitionMultiscale.lean` fixes $h$ as a real unit vector. It requires control of the real pinned path and of observable analyticity in $g$; its statement does not demand a mass-uniform complex transverse-$h$ neighbourhood. This removes the direct wide-domain counterexample from that *statement*, while leaving a proof obligation: the multiscale small-field estimates used to reach the root must be reproved with (4.2)–(4.4), or with an equally strong grouped cancellation. The existing wide-tube theorem cannot be silently applied to the pinned-only class.

**Status.** Equations (1.2), (2.2), (3.1)–(3.3), the comparison of powers, and the logical non-implication are proved here from the cited formulas and one-block computation. Equations (4.2)–(4.4) specify the missing induction estimates; their full multiscale verification is open in the cited sources and landed code. No file under `/home/scott/Balaban` was changed.
