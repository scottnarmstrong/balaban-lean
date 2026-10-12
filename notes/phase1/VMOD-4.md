# Locality with a cover and a different operator domain

**Snapshot: 12 October 2026.** This is the requested redesign after the accepted VMOD-3.md. All statements below refer to the landed Dec2 declarations in Balaban/Localization. The new incidence-graph locality argument is proved mathematically, including its field-independent geometry and constants. It does **not** prove a uniform mixed I-5: the crossed CoverBase estimates and a graph version of the polymer counting lemma remain open. The footprint has a uniform radius for the P6 boundary pair, but only a scale-dependent radius for an arbitrary mixed pair. Nothing under /home/scott/Balaban was edited.

## 1. What the landed locality proofs actually consume

Write $C$ for a DecCover, $H$ for the operator GeneratingSet, $D_z=\operatorname{intBox}(z)$, $\widehat D_z=\operatorname{hatBox}(z)$, $P_z=\operatorname{cubeP}(z)$, and
$$I_H(z)=D_z\cap\Omega_1(H),\qquad \widehat I_H(z)=\widehat D_z\cap\Omega_1(H). \tag{1.1}$$
These are finite sets of fine sites. The following is a call-site audit, not an inference from the structure names:

| Landed declaration | Use of cubeP_sub / own_cover | Other locality input |
|---|---|---|
| Decoupled2Geometry.lean dg5_support | Neither. It uses only chi_supp to put a nonzero term in coreBox. | Algebraic support of Gstar. |
| Decoupled2Geometry.lean dg5_local | Neither. | CoverBase and HatConn C H; the latter makes each $\widehat I_H(z)$ connected for the dichotomy. |
| Decoupled2FieldLocal.lean hhat_aux, and the inlined copy in Decoupled2Geometry.lean dg5' | own_cover assigns $x\in\widehat I_H(z)$ to a full parameter cell $P\ni x$. Then $P\in Qset(z)$ and eligibility puts $x$ in $V(\mathcal C)$. | This step requires a cover of the **operator** sites of the hat, not equality of first domains. |
| dg5' and Decoupled2FieldLocal.lean dg5'_inner | cubeP_sub supplies the center base point in $\Omega_1(H)$, so an interaction box has a witness in $Y$; it also puts a $Qset$ witness in $\Omega_1(H)$ and makes the whole $P$ a connected subset of $V(\mathcal C)\cap\Omega_1(H)$. | The last argument converts a witness $P\cap Y\ne\varnothing$ into SubI H P Y, which triggers the old parameter-agreement hypothesis. |
| Decoupled2FieldLocal.lean local_step | No direct use. It calls dg5'_inner and uses row_mem_hat to put a nonzero operator column at $x\in D_z$ in $\widehat D_z\subset Y$. | DataAgree H N Y. |
| Decoupled2FieldLocal.lean i4a_local | No direct use. It applies local_step to paired Picard iterates, then dg5'_inner for the field. | Its constants come from FamSpec and are independent of the locality proof. |
| Decoupled2BackgroundLocal.lean i4b_local | No direct use. It reduces to i4a_local by the operator-only approxDep/resDep lemmas. | i4b_vanish uses dg5_support, hence only chi_supp. |

The last use of cubeP_sub cannot simply be replaced by $P\cap\Omega_1(H)$. If a parameter cell crosses a Dirichlet wall, its intersection with $\Omega_1(H)$ may be disconnected. Worse, $P\in Qset(z)$ is witnessed anywhere in $P\cap\widehat D_z$, possibly on the exterior side of the wall, while the operator part of $P$ lies in a different component. The existing premise SubI H P Y then does not require $s_P=s'_P$, although the product $s_z=\prod_{P\in Qset(z)}s_P$ still uses this parameter. A fully exterior cell causes no such logical problem—SubI H P Y is vacuous and the old premise forces agreement—but a **partially cut** cell can. This explains why a one-sided replacement for cubeP_sub is insufficient.

There is a second, independent issue: a center with $I_H(z)=\varnothing$ has no operator source in $D_z$. The landed proof nevertheless obtains $z.2\in\Omega_1(H)$ from cubeP_sub and thereby avoids that case. When first domains differ, it must be handled directly.

## 2. The replacement interface

### 2.1 The exact operator footprint

For $x\in\Omega_1(H)$ let $B_H(x)$ be its complete $H$-block at layer $n_H(x)$, and let $N_H(x)$ consist of $x$ and its nearest neighbors that belong to $\Omega_1(H)$. Let $\operatorname{Row}_0(x)=\{y\in\Omega_1(H):\operatorname{dirichletOperator}(H,a,\nu,0)_{xy}\ne0\}$. Define the **exact potential-independent row footprint** and its elementary envelope by
$$T_H(z)=I_H(z)\cup\bigcup_{x\in I_H(z)}\operatorname{Row}_0(x),\qquad
R_H(z)=\bigcup_{x\in I_H(z)}\bigl(B_H(x)\cup N_H(x)\bigr). \tag{2.1}$$
The explicit stencil in DecoupledFieldLocal.lean row_mem_hatBox gives $T_H(z)\subset R_H(z)$. The landed dirichletOperator_eq_add shows that changing the potential changes only diagonal entries. Therefore, for **every** potential $\alpha$,
$$x\in I_H(z),\quad
\operatorname{dirichletOperator}(H,a,\nu,\alpha)_{xy}\ne0
\quad\Longrightarrow\quad y\in T_H(z). \tag{2.2}$$
This is a proved field-independent support statement: the potential changes only the diagonal entry. It has constant $1$ and no cover/domain inclusion hypothesis. The proof of local_step needs precisely (2.2), not the larger assertion that every row site lies in the geometric hat.

If $a_m=M_1\ell_m$, $m=z.1$, then all sites of $T_H(z)$ lie in the periodic box about $z$ with half-width
$$\frac52a_m+\rho_H(z),\qquad
\rho_H(z)=\max\left\{1,\max_{x\in I_H(z)}\ell_{n_H(x)}\right\}, \tag{2.3}$$
where the maximum of an empty set is zero. A neighbor moves by one, and two points of the same $H$-block differ by less than $\ell_{n_H(x)}$ in each coordinate. Uniformly $\rho_H(z)\le L^K$ for $K\ge1$. This is an explicit but **scale-dependent** bound. If $n_H(x)\le m+1$ throughout $I_H(z)$, then $\rho_H(z)\le L\ell_m$ and $T_H(z)\subset\widehat I_H(z)$ because the hat margin is $3L^2\ell_m$. VMOD-3.md §2 proves this local layer bound for the haloed old pair.

The weakest field about the partition needed by dg5_support is
$$\texttt{chi\_core}:\quad z\in C.\operatorname{cubeIdx},\ \chi_z(x)\ne0\ \Longrightarrow\
x\in\operatorname{coreBox}(z). \tag{2.4}$$
For a canonical cover it follows from Cover.lean inBox_of_chi_ne_zero; the exact radius is $3a_m/2$. Neither idx_range nor idx_base nor either original domain field is consumed by the revised locality proof. They remain useful to establish cover counts and analyticity elsewhere.

Define the proposed locality record FootLocalGeom C H to contain only (2.4). The footprint (2.1) is a definition, and (2.2) is a theorem of the operator stencil, so neither need be a user-supplied field. A full FootLocal C H a ν Kc Cx extends **CoverBase** with FootLocalGeom. Its analytical CoverBase part remains a separate obligation. Call the missing full structure for a crossed canonical pair **OPEN-COVERBASE-MIXED**; in particular its nc field is OPEN-NC3-MIXED-WALL. This is weaker on geometry than CoverLocal, and it has no hidden equality $\Omega_1(C)=\Omega_1(H)$.

### 2.2 A center with no operator sites contributes zero

If $I_H(z)=\varnothing$, then the diagonal indicator $c_D(H,z)$ is the zero matrix. By the landed definitions in Decoupled2.lean, cubeG $=(\operatorname{cubeH})^{-1}c_D=0$, so
$$\chi_D(C,H,z)\operatorname{cubeG}(H,z)=0,\qquad
K_z(C,H)\operatorname{cubeG}(H,z)=0 \tag{2.5}$$
for every $\alpha$. Its interpolation factor $s_z$ is immaterial. This proves the exact replacement for the landed base-point invocation. It also permits a small generalization of Decoupled2Local.lean Gs_local: the factor-agreement premise is needed only when $I_H(z)\ne\varnothing$; in the proof of the inner sums, discard the zero matrices of (2.5). All block-locality matrix identities remain unchanged.

### 2.3 The parameter-incidence graph

Fix the old parameter set $\mathcal P=C.\operatorname{parCubes}(X_1)$ and charged set $\mathcal C\subset C.\operatorname{cubeIdx}$. Call a center **eligible** when
$$E_{\mathcal C}(z):\quad z\in C.\operatorname{cubeIdx}
\quad\text{and}\quad
\forall P\in C.Qset(z),\ P\in\mathcal P\Longrightarrow P\in\mathcal C. \tag{2.6}$$
As in the landed hact_aux, if $s_P=s'_P=0$ on $\mathcal P\setminus\mathcal C$, every center with $s_z\ne0$ or $s'_z\ne0$ is eligible.

Build a finite graph $\mathfrak G_H(X_1,\mathcal C)$ with three types of vertices:

* site vertices $x\in (X_1\cap\Omega_1(H))\cup\bigcup_{E_{\mathcal C}(z),\,I_H(z)\ne\varnothing}T_H(z)$;
* center vertices $z$ satisfying $E_{\mathcal C}(z)$ and $I_H(z)\ne\varnothing$;
* parameter vertices $P\in\mathcal C$ which occur in $C.Qset(z)$ for one of those centers.

Join $z$ to every site in $T_H(z)$ and every $P\in C.Qset(z)\cap\mathcal C$. Join nearest-neighbor site vertices as well. For a union $\mathscr U$ of graph connected components let $Y$ be its site projection and $A_Y$ its parameter projection. Every graph component contains a site vertex: a center is live, hence $T_H(z)\ne\varnothing$, and every parameter vertex is attached to such a center. Thus the selected components and $A_Y$ are determined by $Y$. For every eligible live center $z$, **either** $T_H(z)\subset Y$ and $C.Qset(z)\cap\mathcal C\subset A_Y$, **or** $T_H(z)\cap Y=\varnothing$. Proof: every displayed vertex is adjacent to the same center vertex, so belongs to its component. This is the precise replacement for HatConn, hhat_aux, the whole-cell connectivity argument, and the old nearest-neighbor component hypothesis. It handles a Dirichlet wall and a Qset witness outside the operator domain; the parameter vertex joins all components that actually depend on that parameter.

The new agreement premise is
$$\texttt{hagGraph}:\quad P\in\mathcal C\cap A_Y\Longrightarrow s_P=s'_P. \tag{2.7}$$
This is the natural factorwise component premise from the incidence graph: parameters of other components may vary independently. Algebraically, the still weaker premise is equality of the two products $s_z,s'_z$ at each live inner center; (2.7) supplies it from individual parameter values. It deliberately differs from the landed SubI H P Y premise. For each live eligible center with $I_H(z)\subset Y$, its footprint meets $Y$, so all its charged Qset parameters lie in $A_Y$ and (2.7) gives their equality. A Qset parameter in $\mathcal P\setminus\mathcal C$ makes both products zero by the prescribed parameter values; one outside $\mathcal P$ equals $1$ for both. Therefore $s_z=s'_z$ at every live inner center. This proves the factor-agreement input of the generalized Gs_local without any assertion about $P\cap\Omega_1(H)$.

The graph definition requires no extra numerical constant. The center-to-parameter degree is at most $N_0(d,L)=3(8L)^d$ whenever the intrinsic cover count of VMOD-3.md §2 is available; the reverse degree has the same conservative bound: a fixed parameter cell meeting $\widehat D_z$ forces the scale of $z$ within one of its own, and at each of the three scales the possible center bases lie in a coordinate window of length less than $8L$ center cells. The graph may nevertheless merge spatially separate $H$ components. A polymer-size estimate for its site projection is **OPEN-GRAPH-GM2**; the degree bound alone does not prove it.

## 3. Locality theorems after the replacement

Define $Z_Y^F$ to contain eligible live centers $z$ with $T_H(z)\subset Y$, and put
$$S_Y^F=\bigcup_{z\in Z_Y^F}D_z,\qquad
\operatorname{Core}_Y^F=\bigcup_{z\in Z_Y^F}\operatorname{coreBox}(z). \tag{3.1}$$
The superscript $F$ denotes the footprint, not a new generating set. The definitions are finite. For operator sites, $S_Y^F\cap\Omega_1(H)\subset Y$ because $I_H(z)\subset T_H(z)$; a source site outside the operator domain is irrelevant.

**Graph DG5 (proved implication; mixed use conditional on CoverBase).** For a single parameter vector $s$, form the same graph with center vertices restricted to the live centers with $s_z\ne0$, omit parameter vertices, and take site vertices from their footprints. Let $Y$ be a union of its components. Assume CoverBase, the two admissible potentials, and the two IsUnit hypotheses for $1-Kcal$ in landed dg5_local. If the potentials and two sources agree on $Y$, then $G_s(H,\alpha)f=G_s(H,\alpha')f'$ on $Y$. The graph gives $I_H(z)\subset Y$ or $I_H(z)\cap Y=\varnothing$ for every active live center. Dead centers contribute zero by (2.5), and factor agreement is automatic because $s$ is fixed. The remaining proof is landed dg5_local's call to Gs_local. This replaces HatConn and the nearest-neighbor-component binder for the mixed case; it does not change the landed same-domain theorem.

**Graph DG5′ (proved implication; mixed use conditional on OPEN-COVERBASE-MIXED).** Assume FootLocal C H a ν Kc Cx, the two admissible potentials and invertible parametrices of landed dg5', $s=s'=1$ off $\mathcal P$, $s=s'=0$ on $\mathcal P\setminus\mathcal C$, a graph-component pair $(Y,A_Y)$ as above, and (2.7). If $\alpha=\alpha'$ and $f=f'$ on $Y$, then
$$G_s(H,\alpha)f=G_{s'}(H,\alpha')f'\quad\text{on }Y. \tag{3.2}$$
It follows in particular on $\operatorname{Core}_Y^F\cap\Omega_1(H)$. **Proof.** Every active live center is eligible. The graph dichotomy gives $I_H(z)\subset Y$ or $I_H(z)\cap Y=\varnothing$. The preceding factor argument gives $s_z=s'_z$ in the first case. Empty centers contribute zero by (2.5). Apply the proof of Decoupled2Local.lean Gs_local with the weakened empty-center agreement premise; its row-support and cut-inverse lemmas need only CoverBase. This proves (3.2). No HatConn, own_cover, cubeP_sub, or cubeP_connIn is used.

**Graph DG5′ with inner data (proved implication; mixed use conditional on OPEN-COVERBASE-MIXED).** If the data in (3.2) agree only on $S_Y^F\cap\Omega_1(H)$, the conclusion on $Y$ still holds. For a live inner center the graph puts $T_H(z)\subset Y$, so $z\in Z_Y^F$ and $I_H(z)\subset S_Y^F$; cubeG_congr therefore identifies its Green kernel. All live outer centers have interaction boxes disjoint from $Y$. The same block-locality proof gives equality on $S_Y^F$. Outside $S_Y^F$ in $Y$, the proof of dg5_support, repeated with only (2.4), forces both outputs to vanish: a nonzero output has an active center $z$ whose core contains the site, hence $I_H(z)\cap Y\ne\varnothing$ and $z\in Z_Y^F$. The landed dg5_support cannot be called directly here because its argument type is CoverLocalGeom; the weaker support lemma is required. This is exactly the role of landed Decoupled2FieldLocal.lean dg5'_inner, with $S_Y$ replaced by $S_Y^F$.

**Graph local_step and I-4a (proved implication; mixed use conditional on OPEN-COVERBASE-MIXED and FamSpec).** Keep the data agreement on $Y$, all smallness and polynomial hypotheses, and the numerical constant $c_\star\exp(N_0\kappa)\le M_1$ of landed local_step/i4a_local. Replace their CoverLocal and HatConn arguments by FootLocal and a graph-component pair; replace the old hag premise by (2.7); replace $S_Y,Z_Y$ by $S_Y^F,Z_Y^F$. In local_step call graph DG5′ with inner data. If $x\in I_H(z)$ for $z\in Z_Y^F$ and a row column $y$ is nonzero, (2.2) puts $y\in T_H(z)\subset Y$, giving the exact data equality used by Nexp_congr. The paired Picard induction of i4a_local is unchanged. Its outputs remain: equality of $\delta\alpha$ on $S_Y^F\cap\Omega_1(H)$, and equality of $\delta\phi$ on $Y$. None of $c_\star,B_G,c_6$ or the contraction constants changes in this algebraic argument.

**Graph I-4b (proved conditional on the same inputs).** Decoupled2BackgroundLocal.lean i4b_local calls i4a_local once. Replace its locality arguments and conclusion sets by the graph versions just stated; keep the resDep data premise on $Y$, since approxField_congr and residual_congr involve only $H$. Its output remains $\alpha=\alpha_2$ on $S_Y^F\cap\Omega_1(H)$ and $\phi=\phi_2$ on $Y$. The revised i4b_vanish calls the weaker support lemma; its proof otherwise stays the same.

These are mathematical proofs of the revised declarations. No Lean declarations with these graph names have landed. The exact proof changes are:

| Declaration | Binder or construction replaced | Proof change |
|---|---|---|
| dg5_support | CoverLocalGeom by FootLocalGeom | Use chi_core at its sole geometric call. |
| Gs_local | Scalar agreement at every inner center by scalar agreement at live inner centers | Use (2.5) for dead inner centers in both sums; leave block_locality unchanged. |
| dg5_local | HatConn and IsNnComp by a component of the active-footprint graph | Derive the interaction dichotomy from graph adjacency; call the revised Gs_local with identical factors. |
| dg5' | CoverLocal, HatConn, IsNnComp, SubI-based hag, ZY by FootLocal, graph-component pair $(Y,A_Y)$, hagGraph, $Z_Y^F$ | Replace hhat, hdich, and the base-point/whole-cell proof of hagree by graph dichotomy and live-center factor agreement; conclude on all $Y\cap\Omega_1(H)$. |
| dg5'_inner | The same binders and SY by $S_Y^F$ | Apply the revised Gs_local on $S_Y^F$ and the weaker support lemma on $Y\setminus S_Y^F$. |
| local_step | CoverLocal, HatConn, IsNnComp, hag, SY by their graph versions | Invoke graph dg5'_inner; replace row_mem_hat by (2.2) for the Nexp_congr column. |
| i4a_local | The same locality binders and conclusion sets | Keep the paired Picard induction, with graph local_step and graph dg5'_inner as its two locality calls. |
| i4b_local | The same locality binders and conclusion sets | Pass the graph binders to i4a_local; keep the operator-only data conversions. |

A Lean implementation must first prove (2.5), the weaker support lemma, and the empty-center variant of Gs_local, then define the finite graph and its component projections, and finally transplant dg5'_inner, local_step, i4a_local, i4b_local in that order. The expected locality-only changes are approximately 1,800–3,000 lines; this estimate excludes CoverBase and polymer counting.

## 4. What is proved for the four canonical pairs

The **replacement geometry** is universal. For $C=\operatorname{coverOf}F$, Cover.lean inBox_of_chi_ne_zero proves chi_core with radius $3M_1\ell_m/2$, independent of $H$; (2.2), (2.5), and the graph-component dichotomy hold for every operator $H$, including $H^\pm$ and both $C^\sharp,C^+$. The exact footprint radius is (2.3). Thus the new locality interface no longer imposes equality of first domains.

There is a stronger result for the concrete P6 boundary operator $H^\partial=G^\partial_{k+1}$ of LFR Definition II.2.4(iv). Its domains are
$$\Omega_n(H^\partial)=
\bigl(\Omega_n(H^-)\cap\Omega_{k+1}^{\,c}\bigr)\cup
\bigl(\Omega_n(U_{k+1})\cap\Omega_{k+1}\bigr)\quad(n\le k),
\qquad \Omega_K(H^\partial)=U_{k+1}\cap\Omega_{k+1}. \tag{4.1}$$
LFR Lemma I.3.5(f) gives $\Omega_{k+1}\subset Z_k^c$, and the halo construction puts $Z_k^c\subset A=\Omega_K(F^\sharp)$. Outside $\Omega_{k+1}$ the lower domains of $H^\partial$ equal those of $H^-$; inside $\Omega_{k+1}$ the auxiliary cover has layer $K$. Hence
$$\Omega_1(H^\partial)\subset\Omega_1(F^\sharp),\qquad
n_{H^\partial}(x)\le n_{F^\sharp}(x)\quad(x\in\Omega_1(H^\partial)). \tag{4.2}$$
This is a complete proof from the displayed layerwise definition and the cited history inclusion. The direct sup-separation argument of VMOD-3.md §2 gives $n_{F^\sharp}(x)\le m+1$ for $x\in D_z$ and a center $z$ of scale $m$. Thus for both $(C^\sharp,H^-)$ and $(C^\sharp,H^\partial)$,
$$\rho_H(z)\le L\ell_m,\qquad T_H(z)\subset\widehat I_H(z), \tag{4.3}$$
and sum_chi on the operator domain follows from the cover partition. The same comparisons feed blockAligned, chi_smooth with $C_x=Cchi(d,L)$, inner_near, and the two intrinsic cover counts of VMOD-3.md §2. This proves the **CoverGeom geometry** for the P6 boundary pair conditional on the proved LFR history and minimal-set statements; nc at its internal wall remains OPEN-NC3-MIXED-WALL. If $H^+$ denotes a different global $\mathbb B_{k+1}$, (4.1) cannot be silently assigned to it.

For $(C^+,H^+)$ with $C^+=\operatorname{coverOf}H^+$, the same-set geometry gives (4.3) once the minimal-set bounds are supplied. For $(C^+,H^-)$ the universal $L^K$ radius is the only conclusion from the replacement interface alone. Its CoverBase.sum_chi may fail if the new cover does not reach an old-domain site inside $\Omega_{k+1}$.

The field and radius status is thus:

| Cover, operator | chi_core and exact row support | Uniform radius in (2.3) | CoverBase status |
|---|---|---|---|
| $C^\sharp,H^-$ | Proved, $3a_m/2$ and (2.2) | $\rho\le L\ell_m$ by VMOD-3 §2 | Paper-level geometry; the FoldSetting bridge to nc is not landed. |
| $C^\sharp,H^\partial$ | Proved, same constants | $\rho\le L\ell_m$ by (4.2) | Paper-level geometry; OPEN-NC3-MIXED-WALL. |
| $C^+,H^+$ | Proved, same constants | $\rho\le L\ell_m$ given the minimal-set layer bound | Same-set direct geometry and nc bridges remain to be discharged. |
| $C^+,H^-$ | Proved, same constants | Only $\rho\le L^K$ without a mixed layer bound | OPEN-REVERSE-PARTITION and mixed geometry/nc. |

The full FootLocal **structure** additionally extends CoverBase. Its new locality fields are proved for all four pairs; CoverBase is not proved for either crossed pair. The one-sided partition is settled by (4.2) for $(C^\sharp,H^\partial)$, while nc is still open. For $(C^+,H^-)$, sum_chi can fail for abstract admissible separated minimal sets: take their seeds far apart on a large torus and an $x\in\Omega_1(H^-)$ beyond every bump support of the new cover. Then $\chi_q(x)=0$ for all $q$ and $\sum_q\chi_q(x)=0$. The LFR boundary history does not state the reverse inclusion $\Omega_1(H^-)\subset\Omega_1(H^\partial)$; a proof that this particular new cover reaches every old operator site is **OPEN-REVERSE-PARTITION**. The graph redesign cannot supply a missing partition or the mixed-wall nc estimate.

The graph also changes the polymer geometry. A charged parameter can join distinct physical components across a wall, so the site projection $Y$ need not be nearest-neighbor connected, and the old GM2 or pe_hole theorem cannot simply be cited for $Y$. An exact graph-to-polymer comparison with the chosen cover sizes and hole charge is OPEN-GRAPH-GM2. Thus the replacement fields are proved with the explicit constants above, and the revised locality theorems follow **conditional on CoverBase**. A uniform modular I-5 remains conditional on OPEN-NC3-MIXED-WALL, OPEN-GRAPH-GM2, OPEN-BLOCKCOUNT-MINIMAL, and, for any use of $(C^+,H^-)$, OPEN-REVERSE-PARTITION and its mixed layer bounds.
