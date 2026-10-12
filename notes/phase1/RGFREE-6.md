# Anisotropic source domains and the physical switch bound

This note answers [followup_r6.txt](followup_r6.txt). The rectangular domain proposed in [W90_HANDOFF.md](/home/scott/Balaban-scratch/W90_HANDOFF.md) and `notes/phase1/I6-ANISO.md` resolves the **geometric** small-mass obstruction of [RGFREE-5.md](RGFREE-5.md). It does not support the requested SWITCH-JOINT bound: Proposition 2 gives an exact switch counterexample within the transverse polydisc. Proposition 3 gives an exact cutoff model showing why the FREE-ACT-TUBE bound needs an additional physical cancellation or subtraction; the full Balaban fluctuation integral still needs separate verification. Thus the two requested assertions cannot both be proved from the given inputs.

All fields below use $b=mh$, where $m>0$ is the **physical** unit-scale mass. The zero background mass used in the mass-free convention is a separate parameter. Write $r=\varepsilon_j$, $e=e_1$, and $N\ge2$. Constants $c_s,c_\parallel,c_\perp>0$ are fixed independently of $m$ and $\beta$.

## 1. The mass-uniform geometric domain

The anisotropic product polydisc at an aligned reference field is
$$
\mathcal P_{j,m}(e)=\left\{(\psi,b):
 \sup_{x,i}|\psi_i(x)-e_i|<c_s r,quad
 |b_1-m|<c_\parallel r^2,quad
 \sup_{i>1}|b_i|<c_\perp r\right\}.                 \tag{1.1}
$$
Its complex orthogonal images may be used when both the original and rotated data lie in the common analytic germ; Hermitian norms are taken only after choosing a frame. The first paragraph of I6-ANISO §1.1 proves a sufficient inclusion of (1.1) in the landed XiC class domain under its stated smallness conditions: one can choose $c_s=c_\perp=(8NB)^{-1}$, $c_\parallel=(8B^2)^{-1}$, $B=2K_1+2$, or smaller constants for strict margins. The mass in XiC is the **background** mass, which is zero in the mass-free branch and at most the physical mass in the complete branch. The inclusion uses `XiD2.psiTildeC_subset_xiC` with equal parameters $\delta_*=r/B$; the positive-mass conversion $h=b/m$ is valid only for $m>0$. A full density in independent $(m,b)$ has no holomorphic continuation through $(0,0)$ because its exact field-only factor contains $b^2/m$ (RGFREE-4 (1.1)). Thus “mass-uniform” here means widths and constants uniform for $m>0$, not a joint analytic extension of the full density through $m=0$.

**Lemma 1 (proved source-coordinate preservation).** Let the parent and child masses be $M$ and $m=\lambda M$, $\lambda=L^{-2}<1$, with $r_p=\varepsilon_{j+1}<r_c=\varepsilon_j$. Keep the same physical $h$, so $b=\lambda B$. If the parent source satisfies the two $b$ inequalities of (1.1), then the child source satisfies them with a strict margin:
$$
|b_1-m|=\lambda|B_1-M|<\lambda c_\parallel r_p^2<c_\parallel r_c^2,
\quad |b_i|=\lambda|B_i|<\lambda c_\perp r_p<c_\perp r_c.       \tag{1.2}
$$
Spin-domain preservation still needs a bound for the actual composed background; (1.2) proves only the source-coordinate part.

The same conclusion has a moving-background version. At the parent let $F\cdot F=1$, $v=B\cdot F$, $t=B-vF$; at the child let $G\cdot G=1$, $v'=b\cdot G$, $t'=b-v'G$. Assume $\|F\|,\|G\|\le2$, $r_p\le1$, $M\le C_Mr_p^2$, and the **half-margin** bounds $|v-M|\le(c_\parallel/2)r_p^2$, $\|t\|\le(c_\perp/2)r_p$. Put
$$
B_0=c_\perp/2+2(C_M+c_\parallel/2),
\qquad T_0=C_M+c_\parallel/2+2B_0.                \tag{1.3}
$$
If $\|G-F\|\le c r_p$ with
$$
c\le\min\{c_\parallel/(4B_0),\ c_\perp/(4T_0)\},      \tag{1.4}
$$
then
$$
|v'-m|\le\tfrac34\lambda c_\parallel r_p^2<c_\parallel r_c^2,
\qquad \|t'\|\le\tfrac34\lambda c_\perp r_p<c_\perp r_c. \tag{1.5}
$$

*Proof.* The fixed-frame claim is (1.2). For the moving frame, RGFREE-5 (1.1) is the exact identity
$$
v'-m=\lambda(v-M+B\cdot(G-F)),\quad
t'=\lambda\{t+v(F-G)-(B\cdot(G-F))G\}.
$$
The hypotheses give $\|B\|\le\|t\|+|v|\|F\|\le B_0r_p$. Hence
$|v'-m|\le\lambda(c_\parallel/2+B_0c)r_p^2$, proving its part of (1.5). Also
$|v|+2\|B\|\le (C_M+c_\parallel/2)r_p^2+2B_0r_p\le T_0r_p$. Thus
$\|t'\|\le\lambda[(c_\perp/2)r_p+cT_0r_p^2]\le\lambda(c_\perp/2+cT_0)r_p$, which proves the other part. $\square$

Lemma 1 explains why the RGFREE-5 obstruction disappears **as geometry**: a longitudinal displacement of order $r_p^2$ times a spin displacement of order $r_p$ is order $r_p^3$, well inside the permitted transverse width of order $r_c$. For a transverse input of order $r_p$, the induced longitudinal displacement is order $r_p^2$, exactly the anisotropic longitudinal width. The actual transition still requires the mixed-cover background estimate $\|G-F\|\le c r_p$ with the constant in (1.4), a common XiC margin, and the old-term composition maps. Neither W90_HANDOFF nor the landed Lean asserts this physical instantiation; call it **OPEN ANISO-TRANSPORT**. W90_HANDOFF states explicitly that no anisotropic I-6 Lean theorem had landed at its handoff.

## 2. Exact switch counterexample on the polydisc

Consider one constrained sphere block with $a\in[9/10,3/2]$ and
$$
A_m(e,\phi)=\frac a2(e-\phi)^2+\frac m2(\phi-h)^2,
\quad \phi\cdot\phi=1,
\quad b=mh=me+qe_2.                                      \tag{2.1}
$$
Choose $q=\sigma r^2>0$ with $\sigma$ fixed so small that $q<c_\perp r/4$ and all the ordinary complete and mass-free XiC/background margins hold. The latter is possible because the mass-weighted transverse $h$ displacement is exactly $q$, the longitudinal displacement is zero, and the critical point and multiplier below vary by $O(q)$ and $O(q^2)$, respectively. This is the same domain check as RGFREE-3 §2.1, with a real rather than imaginary transverse direction. Fix $r>0$ and a switch parameter $1<\theta<L^d$; let
$$
m=m_\beta=\theta/\beta,\qquad \beta\longrightarrow\infty.       \tag{2.2}
$$
At this fixed step $\beta m=\theta$ satisfies the switch range, while the point $(e,b)$ remains strictly inside (1.1) and its XiC intersection for all large $\beta$.

More explicitly, take the real XiC witness $(\Psi_0,h_0)=(e,e)$ and the complex displacement $h''=(q/m)e_2$. The mass-weighted $h''$ norm is $q$ and its longitudinal component is zero. The background formulas in Proposition 2 give $\|\phi^m-e\|=O(q)$ and $|\phi^m_1-1|=O(q^2)$, with constants independent of $m\downarrow0$; the multiplier has the same $O(q^2)$ margin. Choosing $\sigma$ after the fixed XiC constants establishes the claimed strict inclusion. Here $r=\varepsilon_j$ and $\sigma$ are fixed before the final inverse-temperature choice, as in the original constant order.

**Proposition 2 (proved).** The mass-free background is $\phi^0=e$ and the complete background is
$$
\phi^m=\frac{(a+m)e+qe_2}{R},\qquad
R=\sqrt{(a+m)^2+q^2}.
$$
The switch chord has absolute logarithmic cost
$$
\beta\{A_m(e,\phi^0)-A_m(e,\phi^m)\}
=\beta\{R-(a+m)\}
=\frac{\beta q^2}{R+a+m}\ge c_a\beta q^2
=c_a\sigma^2\beta r^4.                              \tag{2.3}
$$
Here $c_a>0$ depends only on the displayed $a$ interval and a fixed upper bound for $q$.

*Proof.* On the unit sphere the $\phi$-dependent part of (2.1) is $-((a+m)e+qe_2)\cdot\phi$. The two stationary points follow by normalization. Evaluating at them gives the first equality; rationalizing $R-(a+m)$ gives the second. For $q\le a+m$ and $a+m\le2$, $R+a+m\le3(a+m)\le6$, so one can take $c_a=1/6$. $\square$

The SWITCH-JOINT bound of RGFREE-4 (2.4) would give, at this same datum and with zero old irrelevant terms,
$$
 C_{\rm sw}\{\beta m r^2+E_0\sqrt m\}
=C_{\rm sw}\{\theta r^2+E_0\sqrt{\theta/\beta}\},     \tag{2.4}
$$
which stays bounded as $\beta\to\infty$, contradicting (2.3). The contradiction persists for old terms with the fixed H4 bound: on a fixed finite-step torus their total difference per output block is bounded by $C_uE_0$, independent of $\beta$, as proved in RGFREE-3 (2.6), and cannot cancel (2.3). It also persists if one chooses $q$ of order $r$ inside the wider transverse disc; $q=\sigma r^2$ already suffices. Hence **SWITCH-JOINT as stated is false on the mass-uniform anisotropic domain**, regardless of whether `WeightedProp51`, fluctuation I-5, or anisotropic I-6 is later proved. This is a size obstruction before localization.

## 3. Exact cutoff fluctuation test

The same transverse source prevents the uniform local activity bound in FREE-ACT-TUBE on (1.1). In (2.1) use the mass-free background $e$ and parameterize the nearby $N=2$ sphere by
$$
\phi(x)=\sqrt{1-x^2/\beta}\,e+\frac{x}{\sqrt\beta}e_2,
\qquad |x|\le p_\beta<\eta\sqrt\beta,quad 0<\eta<1/2.       \tag{3.1}
$$
The exact action difference is
$$
\beta\{A_m(e,\phi(x))-A_m(e,e)\}
=\beta(a+m)(1-\sqrt{1-x^2/\beta})-\sqrt\beta qx.       \tag{3.2}
$$
The chart Jacobian is $(1-x^2/\beta)^{-1/2}dx/\sqrt\beta$; its common $\beta^{-1/2}$ cancels in the normalized ratio. Write $J_\beta(q)$ for the resulting cutoff integral divided by the same integral at $q=0$. Suppose the fluctuation cutoff contains a fixed interval: $p_\beta\ge p_0>0$ for all large $\beta$. This is compatible with the P4/Lemma 2.5 cutoff regime, which requires its physical radius $p_\beta/\sqrt\beta$ to be small.

**Proposition 3 (proved).** With $m=\theta/\beta$ and the fixed $q=\sigma r^2>0$ of §2,
$$
\log J_\beta(q)\ge\tfrac12p_0q\sqrt\beta-C_{a,\theta,p_0,\eta}
\longrightarrow+\infty.                                \tag{3.3}
$$

*Proof.* Since $1-\sqrt{1-u}\ge u/2$ and $a+m\ge9/10$, the denominator is at most
$(1-\eta^2)^{-1/2}\int_{\mathbb R}e^{-(9/20)x^2}\,dx$, independently of $\beta$ and $p_\beta$. For large $\beta$, the interval $[p_0/2,p_0]$ lies inside the cutoff and has $x^2/\beta<1/4$. On it, $1-\sqrt{1-u}\le u$, the Jacobian is at least one, and the integrand in the numerator is at least
$\exp\{- (a+m)p_0^2+\sqrt\beta q p_0/2\}$. Integrating over that interval and dividing by the uniform denominator bound proves (3.3). $\square$

This is an exact constrained-sphere fluctuation with an explicit real cutoff. The reference main action is evaluated at the zero-mass background $e$, so (3.3) belongs to its raw fluctuation correction. Extracting the field-only factor $b^2/(2m)$ does not change the ratio: that factor is identical for every $\phi$ and cancels. Consequently the raw coefficient of this model cannot satisfy the mass- and $\beta$-uniform bound $B_E$ in RGFREE-4 (1.9) on a domain containing (1.1). The model does **not** by itself identify the full Balaban fluctuation covariance and labels. FREE-ACT-TUBE for those labels remains **OPEN**; its proof must exhibit a cancellation or an explicit subtraction of this transverse-source contribution. The uncut Gaussian test RGFREE-4 (1.6) gives the stronger $O(\beta q^2)$ logarithm in its model.

## 4. Consequences for I-6 and the RG theorem

I6-ANISO and W90_HANDOFF concern Cauchy estimates for an **already bounded** local term on (1.1). They do not prove that the physical mass-free fluctuation correction or the switch correction obeys that bound. Proposition 2 shows that the actual switch correction fails its proposed bound even at one block; Proposition 3 shows the corresponding raw fluctuation mechanism in an exact cutoff model. The proposed `polyAniso`/`TubeAniso` and weighted gauge address the false isotropic derivative loss in the I-6 proof; they cannot reduce the switch value at an interior point. No instantiation of `RenormTermwise*`, `marked_cubes`, or `rg_step_infty` changes the switch contradiction.

There are two mathematically consistent routes, each requiring a changed assertion:

1. Retain the mass-uniform anisotropic domain (1.1) and display the large transverse-source free energy as an explicit part of the reference action/density. One must specify that functional through the actual cutoff and old terms, prove its locality and analytic bounds, and recompute the RG equations and matrix. Call this **OPEN SOURCE-RESUMMATION**. Merely removing $b^2/(2m)$ is insufficient by Proposition 3.
2. Retain the current physical main action and fixed H4/forcing bounds, and restrict the transverse source to a mass-dependent width at most $C\sqrt m\,r$ for the switch (and at most $C\beta^{-1/2}$ for the one-block fluctuation test). This is the RGFREE-4 source tube, which is incompatible with the full transverse I-6 polydisc for $m\downarrow0$; an I-6 theorem for the restricted physical term class and the three RG reference slices is then still **OPEN I6-SOURCE-TUBE**.

**Proved:** (1.2), (1.5), the exact chord lower bound (2.3), and the exact cutoff-model lower bound (3.3). **Proved conditional on a PROVED cited result:** inclusion of the conservative rectangle in XiC uses the landed `psiTildeC_subset_xiC` under the explicit I6-ANISO (1.2) scale hypotheses; the mass-free split uses `actionC_mass_split` in `Fluctuation/ExpansionNuFree.lean`. **Conditional on OPEN:** ANISO-TRANSPORT for the actual generating sets; anisotropic I-6 formalization from W90_HANDOFF; FREE-ACT-TUBE for the full physical fluctuation labels; SOURCE-RESUMMATION or I6-SOURCE-TUBE; the physical marked, mixed-cover and H7 assertions named in RGFREE-5. **False with the present density decomposition and fixed bounds:** SWITCH-JOINT on any domain containing (1.1).

No read-only source or Lean file was edited. Confidence is high in the algebraic transfer and exact one-block contradictions. The geometric inclusion is conditional on the stated XiC scale conditions, and full physical domain transport remains open.
