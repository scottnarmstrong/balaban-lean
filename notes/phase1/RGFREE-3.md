# The three localization obligations: domain audit and counterexamples

This note answers [followup2.txt](followup2.txt), in the requested order, and corrects the proposed OPEN estimates in [RGFREE-2.md](RGFREE-2.md). Write $u=k+1$, $\varepsilon=\varepsilon_u$, $m=\nu_{u,u}>0$, $\beta_u=\beta_kL^{d-2}$, and $b=mh$. Constants below are independent of $m$ and of the initial inverse temperature.

The source snapshot is FLUCTUATION.md v2.1, SHA-256 81933c59f78bd9d5e961173cd4d0c0c6f02e2becd191321a071a5d9b90db46f8. Its Lemma 3.5 is proved algebraically. Its Lemma 2.9 proves the scalar chord identity and real-field cost; its joint complex switch and RG conclusion are OPEN. Its Theorem 3.1(g),(h) is conditional on OPEN fluctuation I-5, auxiliary cover and NC, and actual old-term transfer. Section 3.6 names the additional old H7 input OPEN-OLD-H7-DECAY. None of these OPEN statements is assumed as a theorem here.

## 1. FREE-LOC

### 1.1 A proved obstruction in the landed mass-free class

SMALLFIELD.md §1.6 item 1 assigns the physical external-field perturbation to $\mathscr E$ when the background mass is zero. Balaban.SmallField.bgMass in SmallField/Def6Terms.lean returns zero when $\beta_k\nu_k\le1$, and XiDom there uses this background mass. In SmallField/Xi.lean, every $h$ inequality of XiBounds and XiCBounds is multiplied by that mass. The same holds for the $h$ conditions of InPsiTilde and InPsiTildeC in Background/Data.lean.

**Proposition 1 (proved; domain degeneracy).** Fix admissible translation-constant data $\Psi=e_1$ and a mass-free background. For every constant $h\in\mathbb C^N$, $(\Psi,h)$ belongs to the landed mass-free XiDom, with fixed admissible positive $\varepsilon$. Consequently, every local term $E_j(y,X;\Psi,h)$ of a landed IsSF instance is independent of constant $h$ on this slice.

*Proof.* Use real reference $(\Psi_0,h_0)=(e_1,e_1)$ and complex displacement $\Psi''=0$, $h''=h-e_1$. At background mass zero the critical-point equation and its solution and multiplier are independent of $h$. All field and multiplier differences in XiCBounds vanish. The constant solution gives strict gradient, Laplacian, collar and closeness inequalities. Its hAbs and hDot left sides are zero. In InPsiTilde and InPsiTildeC all real and complex $h$ constraints likewise have zero left sides, so the same fixed admissible background-domain parameters work for every $h$. This proves XiDom membership. The landed IsSF.analyticE in SmallField/Def6.lean makes the restriction to each complex coordinate line of $h$ entire, and IsSF.boundE bounds it by $E_0e^{-\kappa d_j(X)}$ independently of $h$. Liouville's theorem makes each restriction constant. Repeat in the $N$ coordinates. $\square$

This differs from the physical mass-free action. The landed Balaban.Fluctuation.actionC_mass_split in Fluctuation/ExpansionNuFree.lean gives, at a constrained sphere field,
$$
\frac m2(\phi-h)\cdot(\phi-h)
=\frac m2-b\cdot\phi+\frac{b\cdot b}{2m}.
\tag{1.1}
$$
The last term depends only on the external field and can be carried as a separate field normalization, but $-b\cdot\phi$ is nonconstant in $h$ for $m>0$. At $\phi=e_1$ its derivative along $h=e_1+te_1$ is $-m$. The landed IsSF density equation in SmallField/Def6.lean displays no separate physical mass factor and uses bgMass in its action. Therefore bounded local $E$ terms in that class cannot encode this physical dependence on the whole stated XiDom. A mass-adapted domain or a separately displayed physical factor is necessary. This is **proved for the displayed class**; it says nothing against a local expansion on a smaller domain.

The bare fluctuation vertex itself has a uniform form. The landed massVar and expansion_nuFree in Fluctuation/ExpansionNuFree.lean give
$$
V_m(\phi')=\sum_x\phi'(x)\cdot\bigl(m\phi^0(x)-b(x)\bigr)
+\frac m2\sum_x\phi'(x)\cdot\phi'(x).
\tag{1.2}
$$
On $|b-me_1|\le r_b$, the source is bounded by $m|\phi^0-e_1|+r_b$. Formula (1.2) is polynomial in $(m,b,\phi')$, with no $m^{-1}$. This **proved algebraic** observation supplies the bare part of a uniform $b$ analysis. The field-only term in (1.1) must still be assigned explicitly.

### 1.2 The precise missing physical bridge

The landed expansion_bounds in Fluctuation/ExpansionBounds.lean and interaction_block_bound in ExpansionLocal.lean take a common complex background-domain hypothesis and prove pointwise bounds. interactionV_rot in ExpansionSymm.lean proves rotation covariance of the cubic term. The Covariance lemma24_* declarations and Measure and SizeMod results control their stated covariance, measure and size objects. None constructs a physical LabelAct satisfying the assumptions of marked_cubes in Polymer/MarkedCubes.lean, a holomorphic parameter family for Pst_Gst_differentiableOn in MarkedCubesHolo.lean, or a physical mixed-cover instance of CoverLocal in Localization/Decoupled2Geometry.lean. The landed i5_background in Localization/I5.lean explicitly omits the fluctuation variable and assumes an analytic bounded input, cover and HatConn. The SmallField/RenormTermwise theorems require actual PremisesTerm and SumConds; FLUCTUATION.md v2.1 §3.6 records their physical tube inclusion and moment-carrier transfer as OPEN.

**OPEN FREE-ACT (sufficient input-level bridge).** After extracting the field-only factor in (1.1), construct the *actual* mass-free block activities and old-action marks on one common open domain in $(\xi,\psi,b)$ containing the closed $c_{10}$ trial ball and the invariant-field discs $|U-1|\le c\varepsilon$, $|V-m|,|W|\le c\varepsilon^2$, with strict margins independent of $m\downarrow0$. Here $U,V,W$ are SMALLFIELD.md §2.3 Step 3's invariant coordinates, with $W=b\cdot b-V^2$; the stated $W$ disc includes the transverse source (2.2). Prove there, with constants uniform in parameter and torus, the LabelAct activity estimate and one-/two-mark bounds required by marked_cubes and marked_cubes_two, parameterwise holomorphy required by Pst_Gst_differentiableOn, an actual mixed CoverLocal/HatConn instance, fluctuation-variable I-5, and PremisesTerm/SumConds for each physical old term. The last assertion includes a common Cauchy margin, correct old-term support restriction, torus-independent limit and a polymer entropy bound. This is **OPEN**. It identifies inputs to the existing abstract theorems; those theorems do not prove these inputs. FLUCTUATION.md Theorem 3.1(g) remains conditional on them.

The last analytic deduction is elementary. Suppose the resulting coefficients obey $|E_Y|\le B e^{-\kappa_a d(Y)}$, the number of polymers of size in $[n,n+1)$ containing a fixed site is at most $C_{\rm ent}e^{a_{\rm ent}n}$, and every displacement $x_1(Y)$ between marked sites read by a term is at most $C_{\rm geo}(1+d(Y))$. If a larger field disc has radius $R_\psi\ge c\varepsilon$, two Cauchy derivatives on a strictly smaller disc give
$$
\sum_{Y\ni0}e^{\kappa'd(Y)}|x_1(Y)|^2|\partial_\psi^2E_Y|
\le\frac{2BC_{\rm ent}C_{\rm geo}^2}{(tR_\psi)^2}
\sum_{n\ge0}(n+2)^2e^{-(\kappa_a-\kappa'-a_{\rm ent})n},
\qquad \kappa_a>\kappa'+a_{\rm ent}.
\tag{1.3}
$$
One $b$ derivative costs $(tR_b)^{-1}=O(\varepsilon^{-2})$; any finite $\xi$ derivative costs the fixed margin $(tc_{10})^{-n}$. Thus normal convergence, the weighted $x_1^2$ moment, and $m$-uniform Cauchy radii follow **conditional on OPEN FREE-ACT**. Its actual mixed-cover geometry and entropy are part of that input. The scale comparison of RGFREE-2 (1.4), $\widehat\beta^{-1}\varepsilon^{-2}\le2\alpha_0^{-2}\beta_{\rm initial}^{-1}L^{-2\gamma u}$ under inductive (H.6), remains valid; it does not supply FREE-ACT.

## 2. SWITCH-LOC

### 2.1 Exact one-block counterexample

The proposed bound in RGFREE-2 (2.3) is **false for its separately estimated chord part on its fixed $b$ disc**. It is also false for the full switch with zero old irrelevant action, which satisfies every abstract old-term size bound.

Take $N\ge2$, translation-constant $\Theta=e_1$, and the one-block constrained action
$$
A_m(\Theta,\phi)=\frac a2(\Theta-\phi)^2+\frac m2(\phi-h)^2,\qquad
\phi\cdot\phi=1,\quad 9/10\le a\le3/2.
\tag{2.1}
$$
Kinetic terms vanish. Set
$$
b=me_1+i\lambda\varepsilon^2e_2,\qquad
h=e_1+i\lambda\varepsilon^2m^{-1}e_2,\qquad
0<\lambda<\min\{c/2,1/16\},
\tag{2.2}
$$
where $c\varepsilon^2$ is the asserted lower bound on the $b$ radius in RGFREE-2 (2.3). Take $\xi=0$ and $\psi=e_1$, so $\Theta=(1+\varepsilon\xi_1)\psi$. This point is strictly inside any proposed product disc with that radius.

It is also in the complete complex background domain for small fixed $\varepsilon$. In XiCBounds of SmallField/Xi.lean, the unit-scale field inequalities are $m|h''|<\varepsilon$ and $m|\phi^r\cdot h''|<\varepsilon^2$; their left sides are $\lambda\varepsilon^2$ and $0$. The real reference is $(e_1,e_1)$. Write $q=\lambda\varepsilon^2$. The complex critical point below has $R\ge A/2$, $|(\phi^m-e_1)_2|=q/R\le2q/A$ and $|(\phi^m-e_1)_1|=q^2/[R(A+R)]\le2q^2/A^2$. Its multiplier difference is $|R-A|=q^2/(A+R)\le q^2/A$. Thus small fixed $\lambda$ makes XiCBounds val, close and mult strict; gradients, Laplacians and collar bonds vanish. In InUnionDomainC of Background/Data.lean choose fixed admissible $\delta=\epsilon_{\rm BG}>0$ with $m\le1$; its field inequality is $m|h''|<\delta^2/\epsilon_{\rm BG}$, also true for small $\varepsilon$. All other constant-field inequalities are strict. Smaller fixed $\lambda$ accommodates any prescribed strict margin.

Put $A=a+m$ and $R=\sqrt{A^2-\lambda^2\varepsilon^4}$ with positive branch. Direct solution of the constrained critical-point equation gives
$$
\phi^0=e_1,\qquad
\phi^m=\frac{Ae_1+i\lambda\varepsilon^2e_2}{R},\qquad
|D_2|=|(\phi^0-\phi^m)_2|=\frac{\lambda\varepsilon^2}{R}.
\tag{2.3}
$$
Indeed, on $\phi\cdot\phi=1$, (2.1) is a field-only constant minus $(Ae_1+i\lambda\varepsilon^2e_2)\cdot\phi$. The same algebra, or FLUCTUATION.md Lemma 2.9(a)'s chord identity, yields
$$
A_m(\Theta,\phi^0)-A_m(\Theta,\phi^m)
=R-A=-\frac{\lambda^2\varepsilon^4}{A+R},\qquad
|\mathscr S|=\beta_u\frac{\lambda^2\varepsilon^4}{A+R}
\ge\frac{\beta_u\lambda^2\varepsilon^4}{2A}.
\tag{2.4}
$$
The complex bilinear sphere and holomorphic square-root branch are used; no positivity of a complex action is asserted.

Choose an admissible switch family with fixed $u$ and $\beta_um=\theta$ for a fixed $1<\theta<L^d$, while $\beta_{\rm initial}\to\infty$. At the preceding scale $\beta_{u-1}\nu_{u-1}=\theta/L^d<1$, while the output product is $\theta>1$, so the crossing occurs at this fixed step. Scale the initial mass like $\beta_{\rm initial}^{-1}$. Then $\varepsilon_u$ is fixed. The proposed right side of RGFREE-2 (2.3) is at most
$$C_{\rm sw}(\theta\varepsilon^2+E_0\sqrt{\theta/\beta_u}),\tag{2.5}$$
which stays bounded, whereas (2.4) diverges linearly in $\beta_u$. On a translation-constant torus with $M$ unit blocks, the chord is $M$ times (2.4). A translation-covariant local expansion with the proposed uniform per-block weighted sum has total absolute value at most $M$ times its asserted bound, up to the fixed convention for counting centers. The triangle inequality gives the contradiction on every sufficiently large torus. This disproves the chord estimate and the full assertion for zero old-action differences.

The same contradiction holds with any old action satisfying the fixed $E_0$ class bound *if the proposed joint domain inclusion holds*. At each old scale $j$, H4 bounds the absolute sum of its local terms at either composed argument by $E_0K_{0,j}$ per old-scale center. At fixed $u$ the ratios of old-scale centers to output blocks and the number of old scales are fixed. Hence
$$
\frac1M\left|\sum_{j\le k_0}
  \bigl(E_j(J_j^0)-E_j(J_j^m)\bigr)\right|
\le 2E_0\sum_{j\le k_0}K_{0,j}\frac{M_j}{M}
=:C_uE_0,
\tag{2.6}
$$
independently of $\beta_u$. Such terms cannot cancel the growing chord. This uses the H4 size bound and the inclusion that SWITCH-LOC itself requests; it does not assume an old-term localization theorem.

The earlier RGFREE-2 (2.2) assertion $|D|\le CK_2\sqrt m\,\varepsilon$ is likewise false on this domain: (2.3) has a fixed lower bound of order $\varepsilon^2$, while $\sqrt m\,\varepsilon\to0$. FLUCTUATION.md Lemma 2.9(a)'s real unit-field bound $D=O(m)$ remains valid on its real slice; it cannot serve as a complex Cauchy majorant.

### 2.2 What a corrected proof requires

For $|\mathscr S|=O(\beta_um\varepsilon^2)$ on this constant-field slice, (2.4) forces the transverse physical source to have $|b_\perp|=O(\sqrt m\,\varepsilon)$. The proposed radius $c\varepsilon^2$ is larger for $m\ll\varepsilon^2$. Equation (2.6) rules out cancellation by old terms obeying the fixed H4 bound. Thus **no additional localization lemma with the present domains and class bounds can prove RGFREE-2 (2.3)**. The minimum repair is to reduce the transverse physical-source domain to $|b_\perp|\lesssim\sqrt m\,\varepsilon$ or change the density decomposition and its class bounds. The source-dependent domain loses the $m$-uniform product $b$ radius required in RGFREE-2 (1.1), so revised RG Cauchy conditions or new coordinates are also needed.

After either repair, a separate **OPEN SWITCH-JOINT** bridge remains: prove fixed-$c_{10}$ joint inclusion for $\Theta=(1+\varepsilon\xi_1)\psi$ in both backgrounds and all old terms; instantiate the physical mixed cover and fluctuation I-5; transfer actual old terms to PremisesTerm/SumConds; sum over old scales; and prove the $x_1^2$ moment. FLUCTUATION.md Lemma 5.6 treats the actual small solution radius, not this fixed trial radius. Localization/Decoupled2 and i5_background are abstract interfaces or background-only theorems with hypotheses. The multivariable Cauchy calculation in RGFREE-2 (2.4)–(2.6) is valid **conditional on a corrected local supremum estimate**; its stated supremum input is false under the current fixed H4 bound. It therefore does not verify the physical forcing hypothesis of rg_step_infty. The algebraic matrix computation in RGFREE.md is unaffected.

## 3. SWITCH-H7

The same example refutes the separate leading-background share of RGFREE-2 (3.3). Choose an observable source $g$ at the block, parallel to $e_2$, with fixed $\|g\|_1<1$. For zero old observable terms, which satisfy the abstract H7 bound, the switch difference is $\langle g,D\rangle$. Equation (2.3) gives
$$
|\langle g,D\rangle|\ge c_g\frac{\lambda\varepsilon^2}{A}.
\tag{3.1}
$$
For fixed $u$, the proposed one-eighth H7 allowance $\frac18c_9L^{-us}$, where $c_9=\beta_{\rm initial}^{-1/4}$ and $s=(d-2)/2+\gamma-\alpha_1$, tends to zero along the family of §2.1. Thus the separate leading share is false on the complete complex disc. The intermediate bound RGFREE-2 (3.2), based on $|D|=O(\sqrt m\,\varepsilon)$, is false there. Its extra exponent restriction cannot cure this fixed-$u$ obstruction.

The failure persists for any old observable satisfying the fixed H7 bound if the claimed joint inclusion holds. At fixed $u$ and $\|g\|_1<1$, the sum of the absolute old observable values at the two composed arguments is at most $C_u'c_9$, with $C_u'$ independent of $\beta_{\rm initial}$: sum the H7 bounds over the finitely many old scales and their point-anchored polymers. The reverse triangle inequality makes the full switch observable at least $c_g\lambda\varepsilon^2/A-C_u'c_9$, while its proposed bound tends to zero. The landed marked_cubes and marked_cubes_two produce local coefficients only after a mark with the required pointwise size and dependence is provided; Pst_Gst_differentiableOn assumes parameterwise holomorphy. FLUCTUATION.md Theorem 3.1(h) treats the ordinary new observable and is itself conditional on the OPEN localization premises.

A smaller H7 domain would need $|b_\perp|\lesssim c_9L^{-us}$ on this slice, in addition to the chord condition $|b_\perp|\lesssim\sqrt m\,\varepsilon$. This changes the class and its Cauchy radii. On the full complete domain, cancellation by old terms is incompatible with their fixed H7 bound, as just proved. The minimum repair is a changed analytic domain or a changed observable decomposition and class norm. The separate one-eighth bounds in RGFREE-2 (3.3)–(3.4) cannot follow from the named inputs: the leading one is false. The old-term part (3.4) alone remains **OPEN**, since the physical marked activities, mixed cover and fluctuation I-5 have not been instantiated.

## 4. Status and constants

| Obligation | Result |
|---|---|
| FREE-LOC | **Not proved from permitted inputs.** Proposition 1 proves the landed mass-free class has an unrestricted complex $h$ domain and bounded local terms constant in $h$. Formula (1.2) proves bare $b$ regularity. Actual physical activities, a mass-adapted domain, and OPEN FREE-ACT are missing. The Cauchy/moment implication (1.3) is proved conditional on FREE-ACT. |
| SWITCH-LOC | **Proposed estimate false** on the fixed $b$ disc, by (2.2)–(2.6), even allowing old terms with the fixed H4 bound. A changed domain or density class, followed by OPEN SWITCH-JOINT localization, is necessary. |
| SWITCH-H7 | **Proposed bound false** on the same complex disc, by (3.1) and the fixed old H7 bound. A changed H7 domain or observable class is necessary; its old marked expansion remains OPEN. |

The only additionally used FLUCTUATION results treated as proved are Lemma 3.5's algebraic mass-free split and Lemma 2.9(a)'s scalar chord identity and real-field cost. The exact one-block calculation also proves its formulas directly. Theorem 3.1(g),(h), Lemma 2.9(b),(c), and §3.6's physical old-term localization were not assumed as proved. No unconditional physical instantiation of triangularBounds_matrixFree plus rg_step_infty follows from these estimates, although their abstract Lean statements and the algebraic matrices remain as recorded in RGFREE.md and RGFREE-2.md.

Fix constants for the counterexample in this order: choose $d,N\ge2,L,u,a$ in their allowed ranges, the positive scale radius $\varepsilon_u$, and the asserted $b$-radius coefficient $c$; choose $\lambda<\min\{c/2,1/16\}$ small enough for strict background-domain margins; fix $1<\theta=\beta_um<L^d$; then let $\beta_{\rm initial}\to\infty$. Neither $\lambda$ nor $b-me_1=i\lambda\varepsilon^2e_2$ depends on $m$. This order explains why a late inverse-temperature threshold cannot cure (2.4) or (3.1).

**Open items.** Repair the physical mass-free IsSF domain/factorization and prove FREE-ACT. Specify a narrower switch domain or a changed density class with compatible RG Cauchy conditions, then instantiate SWITCH-JOINT. Specify a narrower H7 domain or changed observable class, then prove the physical marked old-term bridge. Confidence is high in the Liouville argument and exact counterexamples. The present fixed H4/H7 bounds exclude cancellation on the exhibited slice.

**Sources.** FLUCTUATION.md v2.1 §§1.5, 2.8, 3.6, 5.2; SMALLFIELD.md §§1.6–1.7, 2.3, 3.7; [RGFREE.md](RGFREE.md) §§1–2; [RGFREE-2.md](RGFREE-2.md) §§1–3. Read-only Lean declarations cited above are in Balaban/Fluctuation/ExpansionNuFree.lean, ExpansionBounds.lean, ExpansionLocal.lean, ExpansionSymm.lean, Covariance.lean; Balaban/Polymer/MarkedCubes.lean, MarkedCubesTwo.lean, MarkedCubesHolo.lean; Balaban/SmallField/Def6.lean, Def6Terms.lean, Xi.lean, RenormTermwise*; Balaban/Background/Data.lean; Balaban/Localization/Decoupled2*.lean, I5.lean. No read-only source or Lean file was changed.
