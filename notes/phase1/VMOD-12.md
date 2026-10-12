# The paired P6 locality interface and the old top-layer distance

**12 October 2026.** This is a source-level result for the follow-up to `VMOD-11.md`. “Proved” means the implication with all hypotheses displayed below has a mathematical proof. It does not assert that a proposed Lean declaration has landed. The P6 instances of several hypotheses remain open. All files under `/home/scott/Balaban` were read only.

Write $K=k+1$, $M_1=L^{m_1}$, $\ell_n=L^n$, $C=C^\sharp=\operatorname{coverOf}F^\sharp$, $H_-=\mathbb B_k(W)$ (with empty top domain at depth $K$), and $H_\partial=G^\partial_{k+1}$. The P6 history is intended to give $\Omega_1(H_\partial)\subseteq\Omega_1(F^\sharp)=\Omega_1(H_-)$; its source-to-Lean bridge remains open, and the reverse inclusion fails in the empty-history example of `VMOD-5.md` §2. The pointwise cut estimate `Dec2.cubeBlockBounds_mixed` is **landed** in `Localization/CubeBlockBoundsMixed.lean` with $K_c=\max\{K_p,e^{\epsilon_0d}(1+4K_p)\}$, where $\epsilon_0=\operatorname{agmonRate}(d)$ and $K_p=\operatorname{cutKp}(d,L)$. The corresponding mixed `CubeBlockHolder` and the P6 `FootLocal` record constructors were not found as landed declarations in this audit. None of the arguments below calls `CoverLocal C H_\partial`.

## 1. A concrete map from a polymer component to each incidence graph

Fix a finite selected base $X_1$, a finite set $J$ of parameters with injective center map $c$, and $\mathcal C=c(J)$. Let
$$Y=\operatorname{compY}(c,X_1,J),\qquad
V=X_1\cup\bigcup_{P\in\mathcal C}\operatorname{cubeP}(P). \tag{1.1}$$
The landed `PolymerGeometry.compY` is the union of nearest-neighbor components of $V$ meeting $X_1$, and `I5Local.mem_Vset_iff` identifies its patches with the `Dec2.Vset` cells. For $H\in\{H_-,H_\partial\}$, use exactly the landed `Dec2.EligC`, `LiveI`, `footprint`, `incSites`, `incGraph`, and `IsIncUnion` in `Decoupled2FpGeometry.lean`. Define the **actual component map**
$$\begin{aligned}
B_H(Y)&=\{z\in C.\operatorname{cubeIdx}:\operatorname{EligC}(z),\ \operatorname{LiveI}_H(z),\ T_H(z)\cap Y\ne\varnothing\},\\
A_H(Y)&=\{P\in\mathcal C:\exists z\in B_H(Y),\ P\in C.Qset(z)\},
\end{aligned}\tag{1.2}$$
where $T_H(z)=\operatorname{footprint}(H,a,\nu,z)$. These are finite sets; a parameter is included precisely when it is incident to a live eligible center whose footprint touches $Y$. The two maps $A_-(Y)$ and $A_\partial(Y)$ need not coincide.

**Paired graph criterion (proved).** For each of the two operators assume the following four *checkable geometric* statements, with $B_H,A_H$ as (1.2):

* **G-site:** if $x\in Y\cap\operatorname{incSites}_H$ and $y\in\operatorname{incSites}_H$ is adjacent to $x$, then $y\in Y$;
* **G-foot:** every $z\in B_H(Y)$ has $T_H(z)\subseteq Y$;
* **G-par:** if $z$ is eligible and live and $P\in C.Qset(z)\cap\mathcal C\cap A_H(Y)$, then $z\in B_H(Y)$;
* **G-cell:** every $P\in A_H(Y)$ satisfies $\operatorname{cubeP}(P)\subseteq Y$.

Then, for both $H=H_-$ and $H=H_\partial$,
$$\operatorname{Dec2.IsIncUnion}(C,H,a,\nu,X_1,\mathcal C,Y,A_H(Y)),
\qquad A_H(Y)\subseteq\{P\in\mathcal C:\operatorname{cubeP}(P)\subseteq Y\}.\tag{1.3}$$
**Proof.** In the common vertex type `Dec2.IncV`, take $U_H$ to contain the site vertices of $Y$, the center vertices of $B_H(Y)$, and the parameter vertices of $A_H(Y)$. A site-site edge stays in $U_H$ by G-site. A site-center edge with its site in $Y$ puts the center in $B_H$ by its definition; an edge with its center in $B_H$ puts the site in $Y$ by G-foot. A center-parameter edge with its center in $B_H$ puts its parameter in $A_H$ by (1.2); the reverse implication is G-par. These are all constructors of `Dec2.incRel`; since `incGraph` is its symmetric closure, $U_H$ is closed under every graph edge. The site and parameter projections of $U_H$ are exactly $Y$ and $A_H$, proving `IsIncUnion`. G-cell gives the second conclusion. The proof is the same for both operators and uses no physical-domain comparison. $\square$

The fourth condition matters. `IsIncUnion` alone may put a charged parameter vertex in the component even when its whole parameter cell is outside $Y$; the parameter agreement binder of landed `I5Param.LocalityAEOn` then gives no equality at that vertex. `FootLocal` contains `CoverBase` and `chi_core`; neither it nor the one-sided partition states that the nearest-neighbor component of $V$ is closed in either incidence graph. No landed implication discharges G-site, G-foot, G-par or G-cell for P6. A separate geometric proof is required; name it **OPEN-P6-GRAPH-BRIDGE**.

There is a useful sufficient route with an already **proved cited Lean result**, but its P6 premises remain to be checked. If `Dec2.CoverLocal C F^\sharp`, `Dec2.HatConn C F^\sharp`, $Y$ is an `IsNnComp` of $V\cap\Omega_1(F^\sharp)$, both $H$ domains embed in $F^\sharp.\Omega_1$, and `RowInHat C H a ν` holds for each $H$, invoke `I5FluctGeom.incUnion_of_nnComp` twice, with its comparison set `Hp=F^\sharp` and its operator `Hm=H`. Its proof constructs exactly (1.2) and supplies the cell conclusion of (1.3). In particular, **no** `CoverLocal C H_\partial` appears. This virtual-cover route still needs `HatConn C F^\sharp`, whose failure at a physical wall cannot be excluded merely by `FootLocal`; a direct proof of G-site–G-cell may be cheaper for the actual minimal history. Do not substitute $H_\partial$ for the virtual comparison set in the landed lemma: its `cubeP_sub` and domain-inclusion binders are false in P6.

### 1.1 The multiplier overlap needed by the fluctuation

**Cross-footprint lemma (proved).** Suppose (1.3) holds for both operators, and $x\in H_\partial.\Omega_1\cap\operatorname{Dec2.SYF}(C,H_-,a,\nu,X_1,\mathcal C,Y)$. Then
$$x\in\operatorname{Dec2.SYF}(C,H_\partial,a,\nu,X_1,\mathcal C,Y).\tag{1.4}$$
**Proof.** The old `SYF` witness is an eligible live center $z$ with $x\in\operatorname{intBox}(z)$ and $T_-(z)\subseteq Y$. Since $x$ is also a boundary-operator site, $z$ is live for $H_\partial$ and $x\in T_\partial(z)$ by landed `Dec2.mem_footprint_self`. Landed `Dec2.SYF_subset_Y` gives $x\in Y$. Apply landed `Dec2.IsIncUnion.dichotomy` to the boundary pair. Its disjoint branch contradicts $x\in T_\partial(z)\cap Y$; therefore $T_\partial(z)\subseteq Y$. This puts $z$ in the boundary `ZYF` and $x$ in its `SYF`. $\square$

This replaces the application of `I5FluctGeom.SYF_subset_SY` in `I5FluctLocal.fan_local_fl`; that declaration compares to the **background's** `SY` and requires the false inclusion $\Omega_1(H_-)\subseteq\Omega_1(H_\partial)$.

## 2. Exact agreement and the two-field locality implication

For each action cube $b$, write $X_{1,b}=X1(F^\sharp,m_0,j,\{b\})$, $Y_b(J)=\operatorname{compY}(c,X_{1,b},J)$, and let $u=(D,\psi')$ and $u'=(D',\psi'')$ be the complex background datum and the old block fluctuation. Define the *cube-indexed* relation
$$\begin{aligned}
Ag_b(J;u,u')\quad\Longleftrightarrow\quad&
\operatorname{agreeOn}\bigl(\operatorname{thickSet}(H_\partial,Y_b(J))\bigr)(D,D')\\
&{}\land \bigl[\psi'(y)=\psi''(y)\text{ for all }y\in\operatorname{psiThick}(Y_b(J))\bigr].
\end{aligned}\tag{2.1}$$
`I5Local.thickSet` is $Y\cup\bigcup_{x\in Y\cap\Omega_1(H_\partial)}\operatorname{resDep}(H_\partial,x)$; `I5FluctLocal.psiThick` is $Y$ and its nearest neighbors. This relation is reflexive and monotone in $Y$. It controls the background `resDep` data at every operator site in $Y$, the raw spin datum at all sites of $Y$ (including $H_-\setminus H_\partial$), and the old fluctuation on its collar. The actual cube action also requires the support inclusion stated below.

**Paired field locality (proved conditional on OPEN-P6-GRAPH-BRIDGE and the displayed analytic-domain hypotheses).** Assume two `Dec2.FootLocal` records with the same $C,a,\nu,K_c,C_x$; the `DecSpecs`/`FamSpec`, $c e^{N_0\kappa}\le M_1$, $c_\star e^{N_0\kappa}\le M_1$, strict domain, fixed-point and smallness hypotheses in the exact statements of `Dec2.i4b_local_fp` and `Dec2.i4a_local_fpS`; and (1.3) for $Y=Y_b(J)$. Extend $s,s'\in\operatorname{supN}(J,e^\kappa)$ to cover-cube parameters **relative to $X_{1,b}$** by the rule $s_P^{(b)}=1$ if $P\notin C.\operatorname{parCubes}(X_{1,b})$, $s_P^{(b)}=s_i$ if $P=c(i)$ for an $i\in J$ and $P$ is a parameter cube, and $s_P^{(b)}=0$ on the remaining parameter cubes; use the same rule for $s'$. Values outside `C.cubeIdx` are $1$ under `Dec2.extS`. Assume $e^\kappa>1$ and $Ag_b(J;u,u')$. Then the decoupled background fields $\phi_\partial,\phi'_\partial$ agree on $Y\cap\Omega_1(H_\partial)$, their multipliers agree on $\operatorname{SYF}_{H_\partial}(Y)$, and the decoupled fluctuation fields $\delta\phi_-,\delta\phi'_-$ agree on $Y\cap\Omega_1(H_-)$.

**Proof.** Landed `I5Param.supN` gives zero parameter values off $J$ and the strict polydisc bounds. The extension rules give `hs1` and `hs0` for both physical operators. For each $P\in A_H(Y)$, G-cell and `I5Local.mem_Vset_iff` identify $\operatorname{cubeP}(P)$ with its `Pset` in $Y$; the `LocalityAEOn` parameter hypothesis therefore gives $s_P=s'_P$. This is the `hag` argument of landed `I5FluctLocal.fan_local_fl`, with $A_H$ used separately for the two operators. The first conjunct of (2.1) is exactly the `resDep` agreement binder of `Dec2.i4b_local_fp`, so that theorem gives the two background equalities.

For the old fluctuation use `I5FluctData.flEdat`, which is defined even if $H_-\not\prec H_\partial$: its multiplier `flAlpha` equals the boundary multiplier on $H_-\cap H_\partial$ and zero on $H_-\setminus H_\partial$. The multiplier inputs agree on `SYF` of $H_-$ by (1.4) and the background multiplier equality; outside $H_\partial$ both are zero. Its field input `barField` agrees on $Y$: on $H_\partial$ use the background field equality, outside use the raw spin agreement in (2.1). The old fluctuation inputs agree on $Y$ and the old collar by the second conjunct of (2.1), and their source is zero. These are the five fields of landed `Dec2.DataAgreeS` in `I5FluctStep.lean`. Invoke `Dec2.i4a_local_fpS` using $A_-(Y)$ and its own `hag`. It gives the fluctuation field equality on $Y\cap\Omega_1(H_-)$. The fixed-point and strict-domain premises have been stated explicitly because `I5FluctData.flEdat_strict` requires `Precedes H_- H_\partial`, which is false for the P6 orientation and cannot discharge them. $\square$

**Affine transport (proved conditional on the source-dependency inclusions).** Let $G_{k,X}$ be the generating set of the datum at $\mathbb B_k(X)$ and assume `Precedes G_{k,X} H_\partial` and `Precedes G_{k,X} H_-`. For every $x\in\operatorname{dataSites}(G_{k,X})$, assume the dependency sites of both `composeField G_{k,X} H_\partial` and `composeField G_{k,X} H_-` lie in $X_{1,b}\subseteq Y_b(J)$, and that the action cube's direct datum sites lie there. Then the two data
$$\operatorname{flDatum}\bigl(G_{k,X};\phi_\partial(s),\delta\phi_-(s),D,\psi'\bigr),\qquad
\operatorname{flDatum}\bigl(G_{k,X};\phi_\partial(s'),\delta\phi_-(s'),D',\psi''\bigr)\tag{2.2}$$
are equal as `BgData G_{k,X} N`, provided the displayed dependency condition ranges over **all** `dataSites G_{k,X}`. Indeed, landed `I5FluctChain.flDatum_Ψ` splits (2.2) into two affine `composeField` terms. Each is a finite linear combination of field values on its `composeDep` set and the direct datum. The paired field equalities and (2.1) identify every summand; outside an operator's $\Omega_1$ both `svec` terms are zero. `I5FluctChain.flDatum_h` gives equality of the source component from the same raw-data agreement. This is the pointwise proof pattern in `I5FluctLocal.fan_local_fl` after its call to `i4a_local_fpS`; it does not use `Precedes H_- H_\partial` for this algebraic step. The P6 dependency inclusions and the mixed strict-domain theorem are **OPEN-P6-AFFINE-DOMAIN**, a concrete part of `VMOD-11.md`'s OPEN-H7-BG-MIXED.

For any analytic source functional $E$ of the resulting raw datum, the equality of (2.2) proves `LocalityAEOn(e^\kappa,S,Pset\circ c,Y_b,Ag_b,E\circ\text{affine composition})` by the preceding argument. This is the **fluctuation-variant I-5 locality input**, with no new numerical loss. If its mixed analytic-chain and uniform source-bound hypotheses are also supplied, the coefficient expansion is the same `localization_expansion` proof as landed `I5Fluct.i5_fluct`, with its rate inequalities
$$3\kappa_0+3\le\kappa_{\rm dec},\quad4d(2L+1)^d\kappa_{\rm dec}\le\kappa,\quad
1\le(\kappa/2-1)/2,\quad
\log\bigl((2L+1)^d(L^{m_0})^d\bigr)\le(\kappa/2-1)/2,\tag{2.3}$$
and $\kappa_0,E_b\ge0$, together with its `CovSetup`, connected witness, analytic-domain and source-bound binders. Its bound is $E_b\exp[-\kappa_0\operatorname{treeLenCovOne}_{m_0,j}(X)-2\kappa_{\rm dec}\operatorname{treeLenCov}_{F^\sharp,m_0}(Y)]$. This final expansion is **conditional on OPEN-P6-GRAPH-BRIDGE, OPEN-P6-AFFINE-DOMAIN, and the mixed analytic/bound and polymer hypotheses**; it is not a new landed I-5 theorem.

### 2.1 The exact `DecoupledCubeResponse` mismatch

`Fluctuation/Theorem42Input.lean` defines `DecoupledCubeResponse.loc` with **one** relation `Ag : Finset ι → U → U → Prop`, fixed for all action cubes $b$. `Fluctuation/Theorem42.lean theorem42_of_input` requires, for every $b$, that agreement on `Ysites` of **that** $b$ imply this same `Ag`. Relation (2.1) varies with $X_{1,b}$ and $Y_b(J)$. Taking the intersection of (2.1) over all $b$ makes the required `hlink` generally false; taking their union does not imply locality for each $b$. This is a second, independent interface issue, **OPEN-UNIFORM-AG**, in addition to the graph bridge. The minimal honest repair is to index the response's agreement relation by $b$ and thread `Ag_b` through `cube_expansion` and `theorem42_of_input`, keeping the existing $b$-indexed `hlink`. Alternatively one needs a proved common support region whose agreement follows from every individual `Ysites_b`; no such region is supplied by `FootLocal` or by the halo. There is also a common-index obligation: `theorem42_of_input.hdisj` requires **every** cell $Pset(c(i))$, for one fixed finite type $\iota$, to be disjoint from **every** $X_{1,b}$. A per-cube `ParIdx(F^\sharp,X_{1,b})` cannot serve as that fixed $\iota$, and taking all cover cubes violates `hdisj`. The common index and the extension rule above must be chosen together and checked for every $b$; call this **OPEN-COMMON-PARAM-INDEX**.

The action read set can be specified without hiding a locality premise. For `CubeAction.cubeActionC` on a site cube $Q_b$, its block and mass terms read the sites of $Q_b\cap\Omega_1$ and the complete operator blocks of those sites, while its bond term reads $x$ and $x+e_\mu$ for $x\in Q_b$. For `CubeActionRealStar.cubeActionStar`, also include $x-e_\mu$ for $x\in Q_b$, because a half-weight bond may be based just outside $Q_b$. Define $R_b$ to be this finite union for **both** physical actions and both conventions. Under $R_b\subseteq Y_b(J)$, (2.1) and the paired field equalities identify every summand of either action; this is a direct proof by the displayed definitions. The P6 inclusion $R_b\subseteq X_{1,b}\subseteq Y_b(J)$ is **OPEN-P6-ACTION-SUPPORT**, and the actual at-one, holomorphy and $C_b$ bound are respectively OPEN-ACTUAL-CUBE-AT-ONE, OPEN-H7-BG-MIXED and OPEN-DECOUPLED-WEIGHTED-RESPONSE from `VMOD-11.md`. Therefore (1.3) and the field proof do not by themselves inhabit the four fields of `DecoupledCubeResponse`.

## 3. OPEN-LOCAL-X0-DIST: a top-layer replacement

The global premise of landed `DecoupledFieldX0.i4a_close_X0` is false at the P6 constants:
$$r_0^*M_1=(4dL^3+L)M_1>5LM_1-1=\varrho_{H_-}-1.\tag{3.1}$$
There is nevertheless a direct local theorem. For the common cover define
$$W_C(X_1)=\bigcup_{\substack{z\in C.\operatorname{cubeIdx}:\\
\exists P\in C.Qset(z),\ \operatorname{cubeP}(P)\not\subseteq X_1}}\operatorname{intBox}(z).\tag{3.2}$$
This is the mixed-cover form of landed `DecoupledFieldX0.Wpar`; $C$, not $H_-$, supplies the cube and parameter incidence, and $H_-$ supplies the path metric. Assume $d\ge3$, $L\ge3$, $M_1\ge4L^2$, every cover center has scale at most $K=k+1$, $x\in X_0\subseteq U\subseteq H_-.\Omega_k$, $H_-.\Omega_{k+1}=\varnothing$, $\varrho_{H_-}=5LM_1$, and the **actual selected-set collar**
$$\forall x\in X_0,\qquad B_{\rm torus}(x,r_0^*M_1L^k)\subseteq X_1,qquad r_0^*=4dL^3+L.\tag{3.3}$$
Then, for every $x\in X_0$,
$$\operatorname{siteSetDist}_{H_-}(x,W_C(X_1))\ge M_1.\tag{3.4}$$
The same statement holds if the equality $\varrho_{H_-}=5LM_1$ is weakened to $\varrho_{H_-}L^{k+1}-1\ge M_1L^{k+1}$.

**Proof.** Fix $w\in W_C(X_1)$. Choose its center $z$, a charged $P\in C.Qset(z)$, a witness $y\in\operatorname{cubeP}(P)\cap\operatorname{hatBox}(z)$ from landed `DecCover.mem_Qset`, and $y'\in\operatorname{cubeP}(P)\setminus X_1$. Both $w$ and $y$ lie in `hatBox(z)`. The elementary estimate proved in `DecoupledFieldX0.torusDist_hatBox_le` uses only $L\ge3$ and $M_1\ge4L^2$: each is within $4dM_1L^{z.1}$ of the center. Its proof can be copied without its `DGSetting` wrapper. Landed `DecoupledFieldX0.torusDist_sameCell_le` gives $\operatorname{dist}(y,y')\le dM_1L^{P.1}$. As $z.1,P.1\le K$, the triangle inequality yields
$$\operatorname{dist}(w,y')\le 9dM_1L^K=9dL M_1L^k.\tag{3.5}$$
The strict collar (3.3), and $y'\notin X_1$, imply $\operatorname{dist}(x,y')\ge(4dL^3+L)M_1L^k$. Hence
$$\operatorname{dist}(x,w)\ge(4dL^3-9dL+L)M_1L^k\ge L M_1L^k=M_1L^{k+1},\tag{3.6}$$
since $4L^2\ge9$ for $L\ge3$. The old operator has empty top layer and $x\in\Omega_k$, so $x\in\operatorname{layer}(k)$. Apply the **landed**, operator-only `DecoupledFieldX0.pathDist_ge_torusDist` at layer $k$ (it assumes merely $1\le\varrho_{H_-}$):
$$\operatorname{pathDist}_{H_-}(x,w)\ge
\frac{\min\{\operatorname{dist}(x,w),\varrho_{H_-}L^{k+1}-1\}}{L^{k+1}}\ge M_1.\tag{3.7}$$
If $w\notin H_-.\Omega_1$, the path distance is $\infty$, so the inequality still holds. Take the infimum over $w$ to obtain (3.4). No inequality of the form $r_0^*M_1\le\varrho_{H_-}-1$ was used. $\square$

The mixed version of landed `DecoupledFieldX0.hW_of_par` is a one-line product argument: if $s_P=1$ off `C.parCubes X₁` and $C.sProd(s,z)\ne1$, at least one $P\in C.Qset(z)$ belongs to `C.parCubes X₁`, so `intBox(z)\subseteq W_C(X₁)`. Apply landed `Dec2.i4a_close` (`Decoupled2FieldClose.lean`) with $W=W_C(X_1)$, then `decay_anti_dist` and (3.4). Under its unchanged `FamSpec`, `Dg2Spec`, `CloseSpec`, `OneSpec`, `CoverBase`, fixed-point and smallness binders, this yields the exact factor $e^{-\gamma_wM_1}$, with `closeConst d L N BG κ δ₁` for the multiplier and twice that for fluctuation value, gradient and Laplacian. Thus **OPEN-LOCAL-X0-DIST is resolved as a mathematical estimate conditional on the explicit collar (3.3) and the P6 top-layer facts**. The selected $X_1$ in P6 has not been proved to satisfy (3.3); the one-coarse-cell halo establishes the ball inside $A$, not inside that selected $X_1$ (`VMOD-2.md` §1.3). That remaining geometric obligation is **OPEN-COV-MARGIN**, and the direct estimate (3.5) has not landed in Lean.

## 4. Lean order, remaining work, confidence

Proposed names in the middle column are **not** claimed to exist. Sizes are rough new lines; source-history constructors and the unrelated H7 weighted estimates are excluded.

| Order | New declaration and role | Lines | Landed declarations to reuse |
|---:|---|---:|---|
| 1 | `p6_component_nn`, identify (1.1) with `Vset`, show $Y$ is closed under adjacency in $V\cap\Omega_1(F^\sharp)$ | 80–160 | `PolymerGeometry.compY`, `I5Local.mem_Vset_iff`, `I5Local.compY_closed`, `Dec2.IsNnComp` |
| 2 | `p6_inc_centres`, `p6_inc_params`, define (1.2) for either operator and prove the graph criterion | 180–320 | `Dec2.incGraph`, `Dec2.IsIncUnion`, `Dec2.IsIncUnion.dichotomy` |
| 3 | `p6_graph_bridge_old`, `p6_graph_bridge_boundary`, discharge G-site–G-cell from actual common-cover geometry, or use the virtual $F^\sharp$ route | 250–700+ | `I5FluctGeom.incUnion_of_nnComp` **only** with `Hp=F^\sharp`; `Dec2.CoverLocal` is never constructed for $H_\partial$ |
| 4 | `p6_SYF_cross`, prove (1.4) | 40–80 | `Dec2.SYF_subset_Y`, `Dec2.mem_footprint_self`, `Dec2.IsIncUnion.dichotomy` |
| 5 | `p6_agree_params`, `p6_bg_agree`, `p6_fl_data_agree`, `p6_fl_agree` | 250–500 | `I5Param.supN`, `I5Local.mem_Vset_iff`, `Dec2.i4b_local_fp`, `Dec2.DataAgreeS`, `Dec2.i4a_local_fpS`, `I5FluctData.flEdat` |
| 6 | `p6_affine_agree`, `p6_fan_local_fl_mixed`; transport on the actual $G_{k,X}$ data sites | 150–350 | `I5FluctChain.flDatum_Ψ`, `flDatum_h`, `I5FluctLocal.fan_local_fl` proof pattern; its theorem cannot be called |
| 7 | `p6_common_param_index`, `p6_cube_agree_b`, check one common `ι` and `hdisj`; reindex `DecoupledCubeResponse.Ag` by $b$ or prove a common support relation and its `hlink` | 250–550 | `I5Glue.extParams_par`, `Theorem42Input.DecoupledCubeResponse`, `Theorem42.theorem42_of_input`, `I5Param.LocalityAEOn` |
| 8 | `p6_hat_dist_cover`, `p6_Wpar_cover`, `p6_local_X0_dist`, `p6_i4a_close_X0` | 180–350 | `DecCover.mem_Qset`, `DecoupledFieldX0.torusDist_sameCell_le`, `pathDist_ge_torusDist`, `Dec2.i4a_close`, `decay_anti_dist` |
| 9 | `p6_i5_fluct_mixed` after the mixed analytic, weighted-bound, action and polymer gates | 300–700 plus those gates | `I5Fluct.i5_fluct` proof structure, `Localization.I5Expansion.localization_expansion`; **do not** call `i5_fluct` at its false `FlSetting.hPmp` premise |

**Open items.** OPEN-P6-GRAPH-BRIDGE is the unverified map from the chosen `compY` to both graphs; OPEN-P6-AFFINE-DOMAIN is the strict mixed fluctuation domain and actual dependency inclusion; OPEN-UNIFORM-AG and OPEN-COMMON-PARAM-INDEX are the two response-interface obligations; OPEN-P6-ACTION-SUPPORT is $R_b\subseteq X_{1,b}$ for both action conventions; OPEN-COV-MARGIN is the collar of the **selected** $X_1$. The other `VMOD-11.md` gates (actual at-one action, decoupled weighted H7 response, minimal-set block count and trace, graph/hole GM2, resummation and $k=k_0$ convention) remain open. `Polymer/Hole.lean pe_hole` is only the later counting input.

**Confidence.** High for the graph criterion and cross-footprint proof, the exact landed-theorem binder audit, and (3.4) under (3.3). Medium for the direct P6 geometry needed to discharge G-site–G-cell and for the strength of the chosen action agreement set. No full P6 mixed I-5, `DecoupledCubeResponse`, Proposition 3.3, or Theorem 3.1(f) is claimed proved here.
