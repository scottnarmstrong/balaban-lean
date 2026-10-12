# P6 boundary localization: counting with derivative witnesses

**12 October 2026.** This note responds to followup_g.txt. The finite tree and fixed-output counting lemmas below are proved with explicit constants. Their application to every admissible P6 boundary history remains conditional on the named geometric assertions in §2. P6 printed p. 34 asserts the modular transfer, but the landed incidence graph does not supply its physical witnesses.

## 1. The source index

Set $K=k+1$, $M_1=L^{m_1}$, $M=L^{m_0}M_1$, $G=(2L+1)^d$, and $A'=(M/M_1)^d=L^{dm_0}$, with $d,L\ge3$. Let $\Omega=\Omega_{k+1}$ and let $X\in\mathcal D_k(\mathrm{mod}\,\Omega_k^c)$ be the domain of a boundary term in P6 (4.32). Put $S=X\cap\Omega\ne\varnothing$. The set $S$ may have several components.

P3 printed p. 77 (4.41) differentiates in $M_1$-cubes of the complement of its fixed source base $X_1$ and discards derivative components not meeting that base. P3 printed p. 78 (4.44) assigns
$$Y=X_1\cup\bigcup_iY^{(i)},\tag{1.1}$$
where every $Y^{(i)}$ contains a derivative cube face-touching $X_1$. P3 pp. 79–80 constructs a physical tree inside this $Y$, and p. 81 (4.50) sums derivative families at **fixed whole $Y$**. The scanned PDF pages were checked for (4.44), (4.48), and (4.50), since the P3 OCR corrupts their formulas. P6 printed p. 34, between (4.32) and (4.34), starts from $S$, explicitly permits disconnected $S$ and $Y_1$, and invokes P3 (4.44), (4.48)–(4.50) with modular sizes. It does not assert a fixed-hole-support count.

The active complementary derivative cubes, not parameter labels hidden in a hole, are therefore the counting index. Each retained derivative has an added active output cell as witness.

## 2. Exact output and the geometric premises

Choose a connected physical tree $\Gamma_0\subset X$ and a chosen old modular cover of $X\cap\Omega_k$ with old-scale cost exactly $\Delta$, where
$$\Delta=d_k^{\rm cov}(X\mathrm{\ mod}\,\Omega_k^c).$$
This minimum is attained when the admissible family is nonempty: on the finite torus there are only finitely many cube families and finite bond sets, and the modular covering size is the minimum of their costs. Finite admissibility is part of the P6 source-domain input.
For each chosen old $\pi'_k$-cube that meets $S$, choose a containing aligned new $\pi'_{k+1}$-cube $Q$ of side $LM$ in new-scale units. The old cube, and hence $Q$, is met by $\Gamma_0$. Let $\mathcal Q_0$ be the distinct cubes and $B=\bigcup\mathcal Q_0$. Require $S\subset B$. Every $Q\in\mathcal Q_0$ must have this source-tree witness. This is the **source nesting** premise. It forbids an unpaid active collar. An alternative is to attach extra cubes at a separately measured cost $R_{\rm collar}$.

Take a finite family $\mathcal C$ of active $M_1$-cubes in $\Omega\setminus B$. Form the physical face-adjacency graph on the components of $B$ and on these cubes. Retain only components meeting $B$; the nonzero P3 interpolation terms have every cube of $\mathcal C$ retained. Their union with $B$ and the proper lower-dimensional walls is $Y_1$. Every component of $Y_1$ must contain a component of $S$, not merely touch a filled hole.

For $P\in\mathcal C$, let $D(P)$ be the active aligned $M$-cells obtained by P3's completion on printed p. 78: begin with the containing $M$-cell, then take the generated localization piece inside its $(2L+1)M$ enlargement. All cells of $D(P)$ have the output layer of $P$; $P$ lies in one of them and $|D(P)|\le G$. The corresponding modular output is
$$Y(\mathcal C)=\operatorname{holeCl}_{\Omega}
  \left(X\cup B\cup\bigcup_{P\in\mathcal C}\bigcup D(P)\right),\tag{2.1}$$
where hole closure adjoins each entire component of $\Omega^c$ met by the argument. It adds no active $M$-cell. The required domain assertion is $Y(\mathcal C)\in\mathcal D_{k+1}(\mathrm{mod}\,\Omega^c)$, including alignment where a coarse cell meets a hole.

Finally, require each component of the generated active $M$-cells to have a derivative cube which face-touches a source $\pi'$-cube of $B$, or a face-adjacent chain to such a derivative cube. The attaching source cube must be met by $\Gamma_0$. Every active output $M$-cell outside $B$ must be in some $D(P)$. The generated localization pieces must admit a $\pi'$-cover contained in $Y$, and each cube of that cover outside $\mathcal Q_0$ must contain a generated $M$-cell. These are the **physical attachment, ownership, and cover** premises. They prevent a distant face of a large hole from acting as a free connector. When $\mathcal C=\varnothing$, no new active cell is added.

Call the source nesting, modular-domain, attachment and ownership assertions **OPEN-P6-WITNESS-GEOMETRY** for the actual P6 boundary history. P3 proves their analogue with a connected source inside its top domain. P6 p. 34 says its proof extends, but neither that paragraph nor the landed Lean graph establishes these details for every disconnected modular source. The two-component test in VMOD-2.md §1.3 and the collar counterexample in GRAPH-GM.md §3 show why they must be checked.

Use the modular covering size of FLUCTUATION.md Definition 1.1: a chosen new family covers $Y\cap\Omega$, while a physical tree in $Y$ meets the family and pays **all** traversed bonds, including bonds in filled holes. The same physical source bonds have new-scale cost exactly $L^{-1}$ times their old uniform-scale cost, since the denominators are $ML^{k+1}$ and $ML^k$. This statement is about P6's one-scale modular size; it does not identify it with landed ordinary multiscale treeLenCov.

## 3. Modular size lemma

**Theorem 3.1 (proved for the data of §2).** If $D=d_{k+1}^{\rm cov}(Y(\mathcal C)\mathrm{\ mod}\,\Omega^c)$, then
$$D\le L^{-1}\Delta+d(2L+1)^d|\mathcal C|.\tag{3.1}$$
If the source base has extra cells with admissible attachment cost $R_{\rm collar}$, the proved bound is
$$D\le L^{-1}\Delta+R_{\rm collar}+d(2L+1)^d|\mathcal C|.\tag{3.2}$$

*Proof.* Use the minimizing source tree of §2. Select $\mathcal Q_0$ and the $\pi'$-cover of the generated localization pieces required in §2. This is an admissible chosen family covering $Y\cap\Omega$: the first cubes cover $S$, every remaining active $M$-cell has an owner $P\in\mathcal C$, and hole closure adds no active cell. The tree $\Gamma_0\subset Y$ meets every source $\pi'$-cube and has new cost $L^{-1}\Delta$.

For a face-connected generated component with $r\ge1$ derivative cubes, write $m$ for its number of generated $M$-cells. Ownership gives $m\le Gr$. Root a spanning tree of its cell-adjacency graph at a derivative cube touching a source $\pi'$-cube met by $\Gamma_0$. The coordinate path through that source cube to the root has scaled length at most $dL+\tfrac12$, as in P3 printed p. 79. For each additional face-adjacent $M$-cell, the center path inside the union of the two cells has scaled length at most $\tfrac12(d+1)$; in a uniform layer the sharper bound is $1$. Hence its added cost is at most
$$dL+\tfrac12+\tfrac12(d+1)(m-1)
 \le dL-\tfrac d2+\tfrac12(d+1)Gr\le dGr.\tag{3.3}$$
The final inequality holds for $d,L\ge3$ because $G=(2L+1)^d\ge(2L+1)^2$, so $(d-1)G/2\ge dL-d/2$. All paths lie in $Y$. They visit every generated $M$-cell, hence meet every selected $\pi'$-cube outside $\mathcal Q_0$. Join each component to the same connected $\Gamma_0$ and prune cycles; nonnegative bond costs cannot increase. The resulting tree meets the selected output family and has cost at most $L^{-1}\Delta+dG|\mathcal C|$. Take the output infimum. A separately attached collar contributes $R_{\rm collar}$ by the same union argument. $\square$

The physical face-touching derivative and the source cell met by $\Gamma_0$ are used in the proof. A parameter-incidence edge or a hole closure alone supplies neither.

## 4. Count at fixed whole output

For fixed $Y$, let $B_n(Y)$ be the active output $M$-cells in layer $n$ outside the fixed source base $B$, and let $V_n(Y)$ be the admissible $M_1$ derivative cubes in those cells. Write $b_n=|B_n(Y)|$ and $V(Y)=\bigsqcup_nV_n(Y)$. The derivative witness and P3 completion give, for every effective family with this whole output,
$$\mathcal C\subset V(Y),\qquad |V_n(Y)|\le A'b_n,\qquad
b_n\le G|\mathcal C_n|.\tag{4.1}$$
The second inequality counts $A'=(M/M_1)^d$ aligned small cubes per coarse cell. The last says that all new active output cells have a derivative owner, at most $G$ cells per derivative. A filled hole supplies no candidate active cube. These statements are false for the raw site projection of landed seedClosure.

**Theorem 4.1 (fixed-$Y$ count; proved).** For any finite collection $\mathfrak F_Y$ of effective derivative families satisfying (4.1) and having the same whole $Y$, if
$$x:=\kappa_2/2\ge1,\qquad x\ge\log(GA'),\tag{4.2}$$
then
$$\sum_{\mathcal C\in\mathfrak F_Y}e^{-\kappa_2|\mathcal C|}\le1.\tag{4.3}$$
This is the P6 modular variant of P3 (4.50), with the exact P3 constant $A=GA'=(2L+1)^d(M/M_1)^d$. Disconnected source components do not affect this count.

*Proof.* Put $b=\sum_nb_n$. For each family in the fiber, (4.1) gives $b\le G|\mathcal C|$ and $|V(Y)|\le A'b$. Split the exponent, then enlarge the restricted fiber to all subsets of $V(Y)$:
$$\begin{aligned}
\sum_{\mathcal C\in\mathfrak F_Y}e^{-2x|\mathcal C|}
&\le e^{-xb/G}\sum_{\mathcal C\subset V(Y)}e^{-x|\mathcal C|}\\
&=e^{-xb/G}(1+e^{-x})^{|V(Y)|}\\
&\le\exp\{b[-x/G+A'e^{-x}]\}\le1.
\end{aligned}\tag{4.4}$$
The third line uses $\log(1+t)\le t$. From $x\ge\log(GA')$, $A'e^{-x}\le1/G$; $x\ge1$ proves the last step. If $b=0$, (4.1) leaves only the empty derivative family. $\square$

For P3's rate split $\kappa_2=\kappa_1/2-1$, sufficient explicit conditions are
$$\kappa_1\ge6,\qquad
\kappa_1\ge4d\log((2L+1)L^{m_0})+2.\tag{4.5}$$
The landed PolymerCount.lean theorem gm3 has the same numerical threshold for its own ordinary Ysites index and disjoint Pset premises. It is not a direct proof of (4.3).

Under $L\ge3$, $\kappa\ge3\kappa_0+3$, and $\kappa_1\ge4dG\kappa$, (3.1) also gives
$$
(\kappa_1-1)|\mathcal C|+(\kappa-1)\Delta
\ge(\kappa_1/2-1)|\mathcal C|+\kappa_0\Delta+2\kappa D.\tag{4.6}$$
Indeed the residual coefficients are $\kappa_1/2-2\kappa dG\ge0$ and $\kappa-1-\kappa_0-2\kappa/L\ge0$. This is the arithmetic of landed gm4, now for the modular variant. If (3.2) is used, an additional $2\kappa R_{\rm collar}$ must be paid. Equations (4.3) and (4.6), together with the separate analytic Cauchy derivative estimate, give the counting part of P6 (4.33)–(4.34) **conditional on OPEN-P6-WITNESS-GEOMETRY**.

## 5. Which landed graph definitions change for counting

The landed Decoupled2FpGeometry.lean incGraph remains valid for its proved locality dichotomy. It must be replaced **as the P6 counting graph**: its center-to-parameter edges do not certify a face-touching derivative cube, and its site edges can reach an entire operator component without a charge. The landed Decoupled2FpCount.lean seedClosure, with projections seedSites and seedParams, must likewise be replaced **as the output index**. They need not be deleted from the analytic locality argument.

The replacement definitions are the following precise finite constructions. Let SourceComp(B) be the face components of the active source base; let Deriv be the active complementary $M_1$-cubes. For $\mathcal C\subset\mathrm{Deriv}$ set
$$
\begin{aligned}
\mathrm{locV}(B,\mathcal C)&=\mathrm{SourceComp}(B)\sqcup\mathcal C,\\
\mathrm{locAdj}(u,v)&\iff\text{their physical cubes share a $(d-1)$-face},\\
\mathrm{witnessClosure}(B,\mathcal C)&=
 \{v:\exists b\in\mathrm{SourceComp}(B),\
          b\mathrel{\mathrm{Reachable}_{\mathrm{locAdj}}}v\},\\
\mathrm{effective}(B,\mathcal C)&\iff
          \mathcal C\subset\mathrm{witnessClosure}(B,\mathcal C),\\
\mathrm{rawY1}(B,\mathcal C)&=
 B\cup\bigcup\{P:P\in\mathcal C\cap\mathrm{witnessClosure}(B,\mathcal C)\},\\
\mathrm{outputY}(X,B,\mathcal C)&=
 \operatorname{holeCl}_{\Omega}
       (X\cup B\cup\bigcup_{P\in\mathcal C}D(P)).
\end{aligned}\tag{5.1}$$
Proper lower-dimensional walls are added to rawY1 as in P3 (4.42). No hole is contracted to a zero-length edge in locAdj. The record for an effective family stores a derivative cube and face-touching source cell for every new component, a source-tree point in that cell, and an owner derivative for every new active output cell. The derivative $P\subset Y\setminus B$ proves the first inclusion in (4.1); its owner map proves the third. Thus (5.1) carries the witnesses that incGraph and seedClosure lack.

## 6. Lean order and disposition

1. Define active derivative cubes, physical FaceAdj, locV, locAdj, witnessClosure, effective, and a BoundaryLocWitness record with face anchors, source-tree points, and output-cell owners. Prove ineffective_derivative_vanishes from the interpolation locality formula.
2. Prove modular_source_nesting and modular_hole_completion_domain for the actual P6 history, including no extra active collar. These are the first parts of OPEN-P6-WITNESS-GEOMETRY.
3. Prove deriv_component_face_anchor and completion_cells_le with $G=(2L+1)^d$, including boundary alignment and no output cell without an owner. These finish OPEN-P6-WITNESS-GEOMETRY.
4. Define modularChosenFamily and modularTreeCost; prove source_cost_rescale, generated_component_tree_cost, and boundary_gm2_modular, with a collar variant.
5. Prove deriv_mem_output_new, candidate_cubes_le, new_cells_le_derivs, then boundary_gm3_fixed_Y by (4.4). Its fiber key must be full outputY, never holeSupp.
6. Prove boundary_gm4_modular by (4.6), then combine with the analytic derivative estimate for P6 (4.33)–(4.34). The landed ordinary gm2_tree, gm3, gm4 provide numerical models but do not themselves discharge the modular witness premises.

**Status.** The finite tree lemma, fixed-$Y$ count, and rate arithmetic are **proved under the explicit §2 geometric record**. Their actual P6 instantiation is **conditional on OPEN-P6-WITNESS-GEOMETRY**. The analytic bound is a separate input. This note does not claim an unconditional proof of P6 (4.34), a fixed-hole-support Peierls bound, or the full modular I-5.
