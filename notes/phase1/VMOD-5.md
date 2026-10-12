# Mixed-wall bounds, reverse partition, and graph size

**Snapshot: 12 October 2026.** This is the requested follow-up to VMOD-4.md. Three conclusions have different statuses. The reverse partition for P6's boundary generating set is **false**, with an admissible empty-history counterexample below. The parameter-incidence graph has a proved local metric and degree bound, but its site projection is not automatically a domain for the landed `treeLenCov` or `pe_hole`; a graph-to-polymer completion remains open. The uniform mixed-wall `CoverBase.nc` estimate remains open: the landed cut estimates do not give its scale-independent constant. Consequently no full mixed `FootLocal` instance or uniform modular I-5 is claimed. All files under `/home/scott/Balaban` were read only.

Use $d,L\ge3$, $K=k+1$, $M_1=L^{m_1}\ge4L^2$, $M=L^{m_0}M_1$, $\ell_j=L^j$, and $N_0=3(8L)^d$. Let $H^-:=\mathbb B_k(W_k)$, extended by an empty top domain, $F^\sharp$ the haloed cover set of VMOD-2.md (1.2), and $C^\sharp=\operatorname{coverOf}F^\sharp$. The symbol $H^\partial$ means **exactly** $G^\partial_{k+1}=\mathbb B_{k+1}(\partial\Omega_{k+1})$ of LF-RECONSTRUCTION.md Definition II.2.4(iv), and $C^\partial=\operatorname{coverOf}H^\partial$. A global new set $\mathbb B_{k+1}(W_{k+1})$ is different; any claim about it is named separately. For $q=(m,z)$ let $D_q=\operatorname{intBox}(q)$ and use the footprint $T_H(q)$ of VMOD-4.md (2.1).

## 1. The exact Lean target and the wall obstruction

The missing field is `Dec2.CoverBase.nc` in `Balaban/Localization/Decoupled2.lean`:
$$\forall\alpha\in\operatorname{AdmPot}(H),\ \forall q\in C.\operatorname{cubeIdx},\quad
\operatorname{CubeBlockBounds}(H,a,\nu,\alpha,q,K_c). \tag{1.1}$$
`CubeBlockBounds` in `DecoupledCube.lean` is a triple of **value, forward-gradient, and symmetric-Laplacian** bounds. For a source supported in the complete $H$-block of $y'\in D_q\cap H.\Omega_1$ and bounded by $M_f$, all three right sides are
$$K_c\,\operatorname{decay}\!\left(\frac{\operatorname{agmonRate}(d)}2,
\operatorname{pathDist}_H(x,y')\right)\ell_{j'}^2M_f,
\qquad y'\in H.\operatorname{layer}j'. \tag{1.2}$$
The gradient and Laplacian carry respectively $H.\operatorname{spacing}(x)$ and its square on the left, with the exact retained-neighbor hypotheses in that structure. A two-center Hölder estimate is an additional I-4a input, not a field of `CubeBlockBounds`.

**Proved conditional on the paper-level LFR geometry.** For $(C^\sharp,H^-)$ the old-operator boxes of scale $m\ge2$ have the `FoldSetting` witnesses constructed in VMOD-2.md §2.1: $q_{\rm fold}=\min(k,m+1)$ for lower boxes and $q_{\rm fold}=k$ for a top box. If the corresponding finite-grid bridge is supplied in Lean, the proved `NC3.lean` declarations `pointwise_cut_cube`, `value_cut_cube`, `laplacian_cut_cube` give (1.1) with the witness already used by `DecoupledCube.lean cubeBlockBounds_exists`,
$$K_c^{\rm fold}=K_1+K_2+K_3+\operatorname{smallConst}(d,L)
 +e^{\operatorname{agmonRate}(d)d}\bigl(1+4\operatorname{smallConst}(d,L)\bigr). \tag{1.3}$$
Here $K_1,K_2,K_3$ are the existential constants returned by those three landed NC3 theorems. At $m=1$, the same conclusion needs the LFR source-scale implication $j'\le2$ before the proved `NC3Small.lean` cut theorems apply. Thus (1.3) is a **conditional target**, not a landed mixed `nc` declaration.

**At a physical wall, (1.3) cannot be cited.** `NC3.lean pointwise_cut_cube`, `value_cut_cube`, and `laplacian_cut_cube` require `FoldSetting H q s c`. Its `mem_Ω` and one-site `collar` fields require the whole box and collar to lie in $H.\Omega_1$. A cover box of $C^\sharp$ can straddle the internal Dirichlet wall of $H^\partial$; for it those fields are false. `ReflectedGeneratingSet.lean operator_intertwine` reflects a Neumann cut face. Treating the physical Dirichlet face that way changes the operator. The same issue applies to a cover of a global new set paired with $H^-$ whenever its box crosses the old first-domain wall. This is a false hypothesis of the existing reflection transfer, not a choice of a larger numerical constant.

**What the landed cut results do prove.** Under `CoverGeom.blockAligned`, `CutOperator.lean cubeCut_aligned` gives `CutAligned H (cubeCut H D_q)`. The cut coercivity and Agmon results in `Multiscale/CutCoercivity.lean` and `CutAgmon.lean` then give inversion and weighted block $L^2$ decay with the operator hypotheses of `Dec2.OpSetting`. The strongest directly relevant landed pointwise conversion is `Multiscale/CutPointwise.lean cut_pointwise_crude`. Its right side contains $\ell_{j'}^2\sqrt{\operatorname{Green.sqNorm}f}$; for a source on a $j'$-block, $\sqrt{\operatorname{Green.sqNorm}f}\le\ell_{j'}^{d/2}M_f$. The extra factor $\ell_{j'}^{d/2}$ is unbounded as $j'\le K$ grows. Thus the landed result does **not** imply (1.2) with $K_c=K_c(d,L)$; neither the forward-gradient bound at a physical wall nor the Laplacian and two-center Hölder bound follows from it. The global uncut results `HolderGlobal.lean global_g2iv` and `holder_global` have `dirichletOperator`, not `cutOperator`, in their statements. Replacing their operator in an application would require a new theorem.

The exact missing theorem **OPEN-NC3-MIXED-WALL** is: for every block-aligned $D_q$ of a canonical mixed pair, every $H$ satisfying `OpSetting`, every admissible $\alpha$, and every source block as in (1.1), prove all three `CubeBlockBounds.bounds` inequalities with a common $K_c^{\rm wall}(d,L)$ independent of $K,m,q$, the torus, history and wall shape. The I-4a use also needs the two-center conclusion of `DecoupledCubeHolder.lean CubeBlockHolder` at the same cut. A sufficient route is a cut-parameter version of the local pointwise and Hölder estimates, valid when its equation ball meets a Dirichlet boundary, followed by the proved cut Agmon estimate; another is a Dirichlet-compatible reflection identity at all wall faces and corners. Neither route is a landed declaration or proved by the cited estimates. No numerical value for $K_c^{\rm wall}$ is justified here. This blocks `CoverBase.nc` for $(C^\sharp,H^\partial)$ even though VMOD-4.md (4.2) proves its partition and layer comparisons.

## 2. The reverse partition is false for the P6 boundary cover

The field in question is `Dec2.CoverGeom.sum_chi`:
$$\forall x\in H^-.\Omega_1,\qquad
\sum_{q\in C^\partial.\operatorname{cubeIdx}}C^\partial.\chi_q(x)=1. \tag{2.1}$$
`Cover.lean sum_chi` proves the identity on $H^\partial.\Omega_1$, the first domain of its **own** cover. It says nothing at old operator sites omitted by $H^\partial$.

**Counterexample (proved from the history definitions).** Fix $k\ge1$ and a finite torus satisfying the usual divisibility and size conditions. Take $Z_k=\varnothing$ and choose the next record $\mathsf P_{k+1}=\mathsf Q_{k+1}=\mathsf R_{k+1}=\mathsf S_{k+1}=\varnothing$. The empty record satisfies the region rules of LF-RECONSTRUCTION.md Definition I.3.1. Its rows (R3)–(R6) give $\Omega'_{k+1}=\Omega_{k+1}=\Omega''_{k+1}=\mathbb T$ and $Z^{(0)}_{k+1}=\varnothing$; the hull of the empty set is empty, hence $Z^{\rm pre}_{k+1}=\varnothing$ and $U_{k+1}=(Z^{\rm pre}_{k+1})^\approx=\varnothing$. Meanwhile $W_k=(Z_k^c)^{\approx2}=\mathbb T$ and Definition II.2.2 gives $H^-=\mathbb B_k(\mathbb T)$ with $H^-.\Omega_1=\mathbb T$.

Definition II.2.4(iv) now gives, for $n\le k$,
$$H^\partial.\Omega_n=(H^-.\Omega_n\cap\Omega_{k+1}^c)
 \cup(\mathbb B_{k+1}(U_{k+1}).\Omega_n\cap\Omega_{k+1})=\varnothing,$$
and its top domain is also empty. The recursion of Definition II.2.2 gives $\mathbb B_{k+1}(\varnothing)$ empty at every layer, so $C^\partial.\operatorname{cubeIdx}=\varnothing$. For every $x\in H^-.\Omega_1$, the left side of (2.1) is $0$, not $1$. This is an actual zero-charge history, not a mere abstract pair of unrelated generating sets.

More generally, for any $x\in H^-.\Omega_1$ outside $H^\partial.\Omega_1$ and farther than $\frac32M_1\ell_m$ from every cover center of scale $m$, `Cover.lean inBox_of_chi_ne_zero` forces every $\chi_q(x)=0$. A reverse `sum_chi` therefore requires an additional cover-domain condition and cannot be deduced from the P6 boundary definition. The **valid** one-sided inclusion is $H^\partial.\Omega_1\subset F^\sharp.\Omega_1$ (VMOD-4.md (4.2)); hence use $(C^\sharp,H^\partial)$, not $(C^\partial,H^-)$, for the common interpolation family. If $G^+$ instead means the global $\mathbb B_{k+1}(W_{k+1})$, this counterexample does not identify it with $H^\partial$; a reverse partition for that distinct cover requires its own $H^-.\Omega_1\subset\Omega_1(G^+)$ proof and is **OPEN-REVERSE-GLOBAL**. No such inclusion is a field of the landed Dec2 interface.

## 3. The graph: proved local bounds and the missing polymer completion

Assume $(C^\sharp,H^\partial)$, the cyclic sup-separation and alignment of VMOD-3.md §2, and the LFR comparison (VMOD-4.md (4.2)). For each center $z$ of scale $m$ put $a_m=M_1\ell_m$. `Cover.lean hatRad` and $M_1\ge4L^2$ give
$$\operatorname{rad}(\widehat D_z)
=\frac52a_m+3L^2\ell_m\le\frac{13}{4}a_m. \tag{3.1}$$
The layer comparison gives $T_{H^\partial}(z)\subset\widehat D_z\cap H^\partial.\Omega_1$ (VMOD-4.md (4.3)). If $P\in C^\sharp.Qset(z)$, its scale $n$ satisfies $|n-m|\le1$ by the direct sup-separation proof of VMOD-2.md (1.9). Choose $w\in P\cap\widehat D_z$. Since the aligned parameter cell $P$ has coordinate diameter less than $a_n$, every $t\in T_{H^\partial}(z)$ and $p\in P$ satisfy
$$\operatorname{dist}_\infty(t,p)
 <2\operatorname{rad}(\widehat D_z)+a_n
 \le\left(L+\frac{13}{2}\right)a_m. \tag{3.2}$$
This is a complete triangle-inequality proof, including periodic wrap by cyclic distance. For two centers meeting the same $P$, two selected footprint sites have cyclic sup-distance less than $(2L+13)M_1\ell_K$, and can be joined in the **ambient** fine torus by at most $d(2L+13)M_1\ell_K$ nearest-neighbor bonds. Normalized by $M\ell_K$, the bound is at most $d(2L+13)$ because $M_1\le M$. A center has at most $N_0=3(8L)^d$ incident parameter labels, and a fixed label has at most $N_0$ incident centers by the reverse coordinate count of VMOD-4.md §2.3. Thus a star joining one chosen site per center incident to one charged label costs at most
$$d(2L+13)N_0\quad\text{ambient bond length divided by }M\ell_K\text{, per charged label}. \tag{3.3}$$
This is **proved local incidence geometry**. It does not assert that the ambient paths stay in $F^\sharp.\Omega_1$, in the eventual output domain, or in a permitted hole. It also does not connect every site of a footprint; (3.3) connects one selected witness per center.

There is a second proved counting reduction. Let $z$ be a live eligible center in VMOD-4.md (2.6) with $C^\sharp.Qset(z)\cap\mathcal C=\varnothing$. For $t\in T_{H^\partial}(z)$, the comparison $H^\partial.\Omega_1\subset F^\sharp.\Omega_1$ and $T(z)\subset\widehat D_z$ let the canonical cover assign an own cell $P\ni t$; then $P\in C^\sharp.Qset(z)$. Eligibility and the assumed empty intersection imply $P\notin C^\sharp.\operatorname{parCubes}(X_1)$, so the definition in `Decoupled2Geometry.lean` gives $P\subset X_1$. Hence
$$C^\sharp.Qset(z)\cap\mathcal C=\varnothing\quad\Longrightarrow\quad
T_{H^\partial}(z)\subset X_1. \tag{3.4}$$
Each eligible center adding a footprint site outside $X_1$ therefore has an incident charged label. The reverse degree bound gives at most $N_0|\mathcal C|$ such centers. This counts added **centers**, not the chosen cubes or tree bonds of a polymer completion.

The old `TreeLengthCov.lean gm2_tree/gm2` cannot be applied to the graph site projection $Y$ of VMOD-4.md. Their `ChosenFamily` requires a domain which, at every layer, is covered by complete $\pi'_n$ cubes **contained in that layer of the domain**; `gm2_tree` additionally takes a connected base witness in $X$ and a connected family of the `Pset` pieces. A site projection made from $X_1\cap H^\partial.\Omega_1$ and row footprints can cut arbitrary faces of those cubes and need not have a `ChosenFamily`. A parameter vertex can join two site components across a Dirichlet wall, so $Y$ itself need not be nearest-neighbor connected. These are failures of the theorem's antecedents, even though (3.3) bounds each graph edge. `Polymer/Hole.lean pe_hole` starts **after** a connected, hole-closed block polymer and its Steiner-size activity estimate have been supplied; it supplies entropy and cluster bounds, not this completion.

For clarity, the exact missing **OPEN-GRAPH-GM2** is a map from each anchored graph-component pair $(Y,A_Y)$ to a domain $\widehat Y$ and chosen family $\mathcal K_{\widehat Y}$ such that: (i) $Y\subset\widehat Y$ on the operator sites relevant to locality; (ii) $\widehat Y$ is connected or hole-closed in the precise output polymer graph, with every path used by (3.3) admitted and charged by the Steiner size when it crosses a hole; (iii) $\mathcal K_{\widehat Y}$ satisfies landed `ChosenFamily` or its stated modular analogue; (iv) for a source witness tree $\Gamma_0\subset X\subset X_1$ meeting the chosen input cover,
$$\widetilde d_{F^\sharp}^{\rm cov}(\widehat Y\bmod\Omega_{k+1}^c)
 \le L^{-1}d_j^{\rm cov}(X\bmod\Omega_{\rm in}^c)
 +C_{\rm graph}(d,L)|\mathcal C|. \tag{3.5}$$
Here $\Omega_{\rm in}$ denotes the source small-field domain specified by the particular modular term; it cannot be fixed from the graph alone. When the output is entirely in the top layer, the left side reduces to $d_K^{\rm cov}$. The exact normalization of the modular functional must be the one in FLUCTUATION.md Definition 1.1. All collar additions and complete hole components must be accounted for. Formula (3.3) bounds one part of a possible $C_{\rm graph}$ by $d(2L+13)N_0$ **only in ambient normalized bond length**; it gives no bound for the weighted output tree, the chosen-family completion, or the base-tree transfer. VMOD-2.md §1.5 already gives a two-component source where a selected $X_1$ loses its witness tree; adding a full hole component can have unbounded extent unless its connecting path is charged. Consequently neither (3.5) nor a finite explicit total $C_{\rm graph}(d,L)$ is proved. The separate missing source/base assertion is OPEN-GM2-HOLE-GEOMETRY.

## 4. Disposition and Lean interface

| Pair or obligation | Landed field / declaration | Result here |
|---|---|---|
| $C^\sharp,H^-$ | `CoverBase.nc` | Conditional on the proved NC3 reflection theorems and the not-landed LFR `FoldSetting`/small-scale bridges; candidate (1.3). |
| $C^\sharp,H^\partial$ | `CoverBase.sum_chi`, `nc` | The partition follows from VMOD-4.md (4.2) and `Cover.lean sum_chi`; `nc` is OPEN-NC3-MIXED-WALL. |
| $C^\partial,H^-$ | `CoverGeom.sum_chi` | False for the empty history in §2. |
| Graph $\mathfrak G_H$ | `TreeLengthCov.lean ChosenFamily`, `gm2`; `Polymer/Hole.lean pe_hole` | Incidence constants (3.1)–(3.4) proved; polymer completion and (3.5) remain OPEN-GRAPH-GM2 and OPEN-GM2-HOLE-GEOMETRY. |

The Lean worker implementing VMOD-4's graph locality can use its exact footprint and parameter-agreement proofs independently of these estimates. To obtain a *full* mixed `FootLocal` instance, the next proof must supply a boundary NC3 theorem with the exact `CubeBlockBounds.bounds` triple and, separately, `CubeBlockHolder`; increasing the constants of `cut_pointwise_crude` does not remove its growing $\ell_{j'}^{d/2}$ factor. The reverse P6 pair should be deleted from the instance plan. The counting campaign must first define and verify the completion in (3.5); it may then use (3.3)–(3.4) and the landed `pe_hole` on the resulting Steiner-size activities.
