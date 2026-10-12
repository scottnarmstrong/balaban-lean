# A decorated modular localization for the P6 boundary term

**12 October 2026.** This note answers `followup_r15.txt`. Its finite geometry and counting theorem below is proved for the stated input record. Its application to the two P6 operators is conditional on the named open analytic and history assertions in §5. No claim that P6 (4.33)–(4.34) has been established for its printed polymer class follows from this note. All references to `/home/scott/Balaban` are read-only references.

## 1. The necessary change of output class

Put $K=k+1$, $a=M L^K$ in fine-site units, and $\Omega=\Omega_K$. We use nearest-neighbor (NN) site components of $\Omega^c$ throughout. P1 (2.26), printed p. 117, requires a member of $\mathcal D_K$ to be a connected union of overlapping $\pi'_K$ cubes. P5 (1.33)–(1.34), printed p. 496, requires modularity with respect to the components of $\Omega^c$. The landed `Fluctuation/SizeModDefs.lean` definitions `IsDj`, `OmegaComp`, `DjMod`, and `Yhat` state the corresponding covering-size conventions. They do not identify a general NN-connected site set with a member of $\mathcal D_K$.

`GRAPH-GM-3.md` Proposition 2.1 supplies an admissible two-step history with a new, arbitrarily long, seven-cell-wide hole and a fixed old P1 source $X$. Even for no derivatives, saturating that hole gives a set that cannot be a union of the new eight-cell-wide overlapping cubes. Any block-union modular output containing $X$ pays a new active collar of length at least $T-O(L+r)$, while the old source size is independent of $T$. Therefore the uncharged size transfer claimed on P6 printed p. 34, between (4.32) and (4.33), is false for that class. The theorem below makes an explicit **corrected** choice of output, without changing NN holes or the value of the resummed expansion.

For an active trace $S\subset\Omega$ that is a union of new $\pi_K$ cells, set
$$\widehat Y_\Omega(S)=S\cup\bigcup\{H:H\text{ is an NN component of }\Omega^c, H\sim_{\rm NN}S\}.\tag{1.1}$$
Use the corrected site domain
$$\mathcal D_K^{\rm site}(\operatorname{mod}\Omega^c)
 =\{\widehat Y_\Omega(S):S\ne\varnothing,\ S\text{ a }\pi_K\text{-cell union in }\Omega,
\ \widehat Y_\Omega(S)\text{ NN connected}\}.\tag{1.2}$$
It has the same modular hole rule as P5, but it does not impose P1's overlapping-cube-union condition. Its size is
$$D(S)=d_\Omega(S)=d_K^{\rm cov}(\widehat Y_\Omega(S)\operatorname{mod}\Omega^c),\tag{1.3}$$
the landed `SizeModDefs.dOmega` when the support is connected. The active cells, rather than the possibly long holes, are the cells counted by the landed `SizeModEntropy.G2_S`. The latter is a **proved cited result** for sums over active traces containing a fixed new cell; it is not a theorem about the extra decorations introduced below.

## 2. A finite geometric localization theorem

The following input record states precisely what is needed from a P6 history. It separates the source and operator assertions. Let $X\in\mathcal D_k(\operatorname{mod}\Omega_k^c)$, $X\cap\Omega\ne\varnothing$, and let $(\mathcal K_X,\Gamma_0)$ be an old chosen cover and connected tree realizing $\Delta=d_k^{\rm cov}(X\operatorname{mod}\Omega_k^c)$. On the finite torus the admissible infimum is attained; landed `SizeModCore.exists_admissible_eq_dcovModE` supplies an exact minimizer when the old size is finite. Fix a deterministic tie-break among minimizers; the choice is made once per $X$, before the derivative family varies. Choose a finite family $\mathcal B$ of new $\pi'_K$ cubes, and write $B=\bigcup\mathcal B$. Require:

* **SN:** $X\cap\Omega\subset B$; every cube of $\mathcal B$ meets $X$, contains an old cube of $\mathcal K_X$, and is met by $\Gamma_0$. All these cubes and $\Gamma_0$ are in the physical torus. They need not lie inside the P6 operator domain. The bare source nesting in `GRAPH-GM-3.md` §3 proves this record for a P1 source using $\Omega\subset\Omega_k$ and the old-to-new block inclusion. The stronger P6 auxiliary-domain nesting remains open.
* **AG:** A finite nonempty action anchor $A_0\subset B$ is given; every interpolation derivative that contributes to the coefficient lies in a Moore-connected cluster of parameter patches $Pset(P)$ rooted at $A_0$. Here an edge means two sites at cyclic coordinate distance at most one. The patches have aligned layer indices $n(P)\le K$ and each lies in its top $\pi_K$ cell. The last inclusion follows for landed `PolymerGeometry.Pset` from `Pset_subset_cellOf` and scale divisibility. The condition $A_0\subset B$ is indispensable for the stated charge: an anchor in an old hole arbitrarily far from the old tree would require an additional attachment cost. For the actual P6 action, identifying such an anchor or supplying that attachment cost is **OPEN-P6-SOURCE-ANCHOR** (§5).
* **GRID:** $L\ge3$, the torus admits the indicated aligned top cells and overlapping cubes, and $\Omega$ is a union of top $\pi_K$ cells. Use cyclic boxes if a cube crosses the coordinate seam. The passage from the ordinary P6 scale and volume assumptions to this exact `CTorus` record is **OPEN-P6-HISTORY-GRID**.

For each parameter patch $P$, let $T(P)$ be its top cell, with base $b(P)$. Choose the **central cube**
$$Q(P)=\operatorname{box}\bigl(b(P)-a(1,\ldots,1),La\bigr).\tag{2.1}$$
It is a new $\pi'_K$ cube, contains $T(P)$ and every fine-site Moore neighbor of every point of $T(P)$, and is a union of top cells. The claim uses the three top-cell slabs with offsets $-1,0,1$ in each coordinate, which lie inside (2.1) for $L\ge3$. If $Pset(P)$ and $Pset(P')$ have a Moore-adjacent pair, $Q(P)\cap Q(P')\ne\varnothing$: either cube contains both selected sites. If $Pset(P)$ Moore-touches $A_0$, then $Q(P)$ meets $B$. These assertions hold in cyclic coordinates as well. In particular one does **not** need a face-connected active witness for each derivative, nor a face chain inside $\Omega$; these were the open geometric inputs to `GRAPH-GM-2.md`.

For an effective derivative family $C$, define
$$R_C=X\cup B\cup\bigcup_{P\in C}Q(P),\qquad
S_C=R_C\cap\Omega,\qquad Y_C=\widehat Y_\Omega(S_C).\tag{2.2}$$
The **output label** is
$$\mathfrak y_C=(X,S_C,\mathcal L_C),\qquad
\mathcal L_C=\{\operatorname{cellOfCube}(P):P\in C\}.\tag{2.3}$$
The ledger $\mathcal L_C$ records a coarse cell and its layer, not the derivative cube. It is an honest decoration of the corrected site domain $Y_C$ and retains distinct charge families in a finite fiber. The old source $X$ is also retained in the label. The map $C\mapsto\mathfrak y_C$ is deterministic once $\mathcal B$ and the central-cube convention are fixed.

**Theorem 2.1 (geometry and cost, proved for SN–AG–GRID).** Suppose every component of the Moore graph of the patches in $C$ meets $A_0$ by a Moore edge or a patch containing an anchor site; equivalently the patch graph has a forest rooted at $A_0$. Then $R_C$ is NN connected, $S_C$ is a nonempty union of top cells in $\Omega$, $R_C\subset Y_C$, and $Y_C\in\mathcal D_K^{\rm site}(\operatorname{mod}\Omega^c)$. Moreover
$$D(S_C)\le L^{-1}\Delta+dL|C|.\tag{2.4}$$
The minimizing old cover is fixed for all $C$ associated to this source.

*Proof.* $X$ is NN connected, and every member of $\mathcal B$ meets $X$. Their union is NN connected. Traverse a rooted forest of the selected patches. The first $Q(P)$ in each tree meets $B$ because it contains a site of $Pset(P)$ and its Moore-neighbor anchor; each later $Q(P)$ overlaps a predecessor $Q(P')$. Boxes are NN connected, so adjoining them preserves NN connectivity. This proves the assertion for $R_C$.

Although an old $\pi'_k$ cube is generally **not** aligned to the new top-cell grid, SN gives $X\cap\Omega\subset B$. Thus
$$S_C=(B\cup\bigcup_{P\in C}Q(P))\cap\Omega.\tag{2.5}$$
Both factors on the right are unions of top cells, so $S_C$ is such a union. It is nonempty by $X\cap\Omega\ne\varnothing$. Every point of $R_C\setminus\Omega$ has an NN path in $R_C$ to $S_C$. Its initial segment outside $\Omega$ lies in an NN component of $\Omega^c$ adjacent to $S_C$; hence the point lies in $Y_C$. Since $R_C$ contains $S_C$, $R_C\subset Y_C$. Each added hole component meets $S_C$ by an NN edge, so $Y_C$ is NN connected. Equation (1.1) also says that every NN component of $\Omega^c$ is entirely contained in or disjoint from $Y_C$, proving the modular property.

For the cost, use $\mathcal B\cup\{Q(P):P\in C\}$ as the new chosen cover. Its cubes lie in $Y_C$ and cover $Y_C\cap\Omega=S_C$. The old tree $\Gamma_0\subset X\subset Y_C$ meets each source cube by SN. Follow the rooted forest: from the already chosen point in the predecessor cube, run a coordinate NN path **inside that cube** to a point of intersection with the new cube. The required path has fewer than $dLa$ bonds per added patch. Every path lies in $R_C\subset Y_C$, and the resulting tree meets every chosen cube. An old bond costs $1/a=(1/L)$ times its old normalized cost, as in the landed `GraphGmTree.bondCost_scaleW_succ`. Dividing the added bond count by $a$ proves (2.4). This tree does not use `GraphGmTree.modular_tree_of_witnesses`: that theorem takes a different output and a face-cell generating record, including `hKgen`, which the thin-hole history does not provide. $\square$

The `R_C\subset Y_C` step pays no active collar along an old or new hole. In the long-thin-hole example with $C=\varnothing$, its distant hole is present in $Y_C$ but absent from the active trace $S_C$; (2.4) remains uniform. This is exactly why the corrected class is necessary.

## 3. Fixed decorated-output count and rate

Let $J$ be the finite common P6 parameter index, and let `Deriv` be the aligned layer cubes that may occur in an AE coefficient. Fix a label $(X,S,\mathcal L)$ and let $\mathscr F(X,S,\mathcal L)$ be **any** family of effective $C\subset\mathrm{Deriv}$ with (2.3) equal to that label. Put
$$A'=(L^{m_0})^d,\quad G=(2L+1)^d,\quad
\kappa_2=\kappa_1/2-1.\tag{3.1}$$
The landed `GraphGmCount.card_deriv_in_cell` proves that at most $A'$ derivative cubes have one layer-cell label. Apply the landed `GraphGmExponent.boundary_gm3_fixed_Y_rate` with its abstract `Yc` **equal to the ledger $\mathcal L$**, `Bc=∅`, and $D(P)=\{\operatorname{cellOfCube}(P)\}$. Its three witness premises are now tautological: every selected $P$ has its cell in $\mathcal L$; every cell of $\mathcal L$ is owned by a selected $P$; and $|D(P)|=1\le G$. Therefore, if
$$\kappa_1\ge6,\qquad
\kappa_1\ge4d\log((2L+1)L^{m_0})+2,\tag{3.2}$$
then
$$\sum_{C\in\mathscr F(X,S,\mathcal L)}e^{-\kappa_2|C|}\le1.\tag{3.3}$$
This is a **proved conditional on a proved cited result** application: the only application hypotheses are alignment of `Deriv`, finiteness, and the definitional ledger equalities. It does not use `OPEN-P6-WITNESS-GEOMETRY`. Calling (3.3) a fixed **undecorated** $Y$ count would be false; the ledger must be retained or its entropy paid separately.

Assume that for each $X$ and both P6 operators $H\in\{H_-,H_\partial\}$ the old boundary summand has, on one common strict open H7 polydisc of radius $e^{\kappa_1}$, an analytic parameter function $F^H_X(u,s)$ with
$$\sup_{u,s}|F^H_X(u,s)|\le\beta_k^{-2}e^{-(\kappa-1)\Delta_X}.\tag{3.4}$$
Assume also the star coefficient localization in §4. The landed `I5Param.abstract_expansion_on` gives the AE coefficient expansion and the Cauchy bound; clause 1 of the star property separately removes every ineffective $C$:
$$\|[s_C]F^H_X\|\le\beta_k^{-2}
e^{-(\kappa-1)\Delta_X-(\kappa_1-1)|C|}.\tag{3.5}$$
For $L\ge3$, $\kappa_0\ge0$, $\kappa\ge3\kappa_0+3$, and
$$\kappa_1\ge4dL\kappa,\tag{3.6}$$
Theorem 2.1 and the landed `Vmod7Glue.exponent_arith_graph`, with $C_{\rm graph}=dL$, yield
$$\|[s_C]F^H_X\|\le\beta_k^{-2}
e^{-\kappa_0\Delta_X-2\kappa D(S_C)-\kappa_2|C|}.\tag{3.7}$$
At a fixed decorated label, (3.3) gives
$$\|F^H_{X,S,\mathcal L}\|
\le\beta_k^{-2}e^{-\kappa_0\Delta_X-2\kappa D(S)}.\tag{3.8}$$
If $\beta_k\ge1$, the right side is at most $\beta_k^{-3/2}e^{-2\kappa D(S)}$. The equality of the finite AE expansion with the original $F^H_X(u,1)$ is unchanged by sorting its terms by $(X,S,\mathcal L)$; thus **the resummed expression is identical**. The same argument applies independently to each of the two P6 operators and to their sum. Equation (3.8) is the final **decorated corrected-class** bound conditional on (3.4) and star locality. It is not P6 (4.34): summing (3.8) over ledgers and old sources at fixed undecorated $Y$ needs an additional theorem.

## 4. The required locality map for both operators

Let $F^\sharp$ be the virtual comparison generating set of `VMOD-13.md` §1, with common cover $C_F=\operatorname{coverOf}F^\sharp$ and physical domains $H_-=\mathbb B_k(W_k)$ (empty top layer) and $H_\partial=G^\partial_K$. For a derivative family $C$ let $T_C$ be the union of those **Moore** components of
$$V(A_0,C)\cap\Omega_1(F^\sharp)
 =\bigl(A_0\cup\bigcup_{P\in C}Pset(P)\bigr)\cap\Omega_1(F^\sharp)\tag{4.1}$$
that meet $A_0$. Keep the interpolation holes as NN components; the Moore relation appears only in the graph used to propagate incidence locality. Suppose the following **star AE property** holds for $H=H_-$ and $H=H_\partial$ with the same parameter index $J$, cover, H7 data set $\mathcal U$, and strict polydisc:

Here the actual P6 anchor is also required to lie in $\Omega_1(F^\sharp)$, and each selected $Pset(P)$ must lie there. The latter is the `cubeP_sub` field of the still open P6 `CoverLocal C_F F^\sharp` instance. The anchor inclusion is part of `OPEN-P6-SOURCE-ANCHOR`, not a consequence of bare source nesting.

1. If a selected $P$ is outside the rooted star support, varying $s_P$ alone leaves $F_X^H(u,s)$ unchanged. Hence the coefficient for a family not entirely rooted at $A_0$ vanishes.
2. For **every** $C$, if two admissible data $u,u'$ agree on the complete action and decoupled-field read collar of the rooted support $T_C$, and parameters $s,s'$ agree for selected $P$ whose whole patch lies in $T_C$, then $F_X^H(u,s)=F_X^H(u',s')$ throughout the AE polydisc. For an unrooted selected patch this includes the independence in clause 1; restricting clause 2 to rooted families would not supply `LocalityAEOn`, which quantifies over every $C$.
3. The action anchor and the parameter patches used in this assertion satisfy AG with $A_0\subset B$. Agreement on the corrected output $Y_C$ implies agreement on that read collar. This last clause includes the collar in the relation `Ag` of `I5Param.LocalityAEOn`; mere agreement on the bare sites of $Y_C$ is insufficient for a nonlocal action read.

These clauses define **OPEN-P6-STAR-AE**, and apply to the fluctuation and background operators with their respective physical read sets. By the rooted-forest argument of §2, $T_C\subset R_C\subset Y_C$ for rooted $C$. For arbitrary $C$, apply that argument to its rooted subfamily and use monotonicity of (1.1) to obtain $T_C\subset Y_C$. Every selected patch inside $T_C$ is therefore inside $Y_C$; selected patches outside $T_C$ are harmless by clause 1. Output agreement supplies the read-collar agreement. Thus clause 2 supplies
$$\operatorname{LocalityAEOn}(e^{\kappa_1},\mathcal U,Pset, C\mapsto Y_C,Ag_H,F_X^H)\tag{4.2}$$
for each $H$. This is the required replacement for `compY` in `I5Param.abstract_expansion_on`. It is important that (4.2) **alone** does not establish clause 1: enlarging $Y_C$ by a long hole can make an otherwise ineffective $P$ lie in $Y_C$. The coefficient-zero statement must come from the rooted star support before output enlargement.

The feasible route to clause 2 is `VMOD-14.md` §2: port `I5FluctGeom.incUnion_of_nnComp` to a Moore-component version using `Dec2.IsIncUnion.dichotomy`, `I5FluctGeom.footprint_sub_hat`, and the landed `Dec2.i4a_local_fp` and `Dec2.i4b_local_fp` for the two fields. The exact source-to-index bridge, virtual `CoverLocal`, `RowInHat`, and common H7 input remain the explicit open binders of `VMOD-13.md` §§1–2. The actual diagonal wall in `VMOD-14.md` makes the NN `HatConn` route unavailable. One can instead use incidence-graph components directly; the chosen output and tree theorem above accept either graph once its patches form the stated rooted Moore forest.

The **weakest new hat assertion** needed by the Moore route is not `StarHatConn` for every cover center. It is **OPEN-P6-ELIGIBLE-STARHAT**: for each admissible P6 region history, each $H\in\{H_-,H_\partial\}$, each parameter family $C$ used by a nonzero coefficient, and each cover center $q$ that is `Dec2.EligC` and has a live footprint for $H$, the intersection $\operatorname{hatBox}(q)\cap\Omega_1(F^\sharp)$ is Moore connected **between the footprint sites and the charged patch that makes $q$ eligible**. Formally, every such pair has a Moore path in this intersection; connectivity of unrelated portions of the hat is not required. The history includes the actual `RegionHistory` generating sets, the prescribed minimal set and one-cell top halo, scale divisibility, both physical domain inclusions, and the $5L$ inter-layer margin. `VMOD-14.md` proves the stronger full-star statement at $k=1$ for its cell-union geometry, but not at $k\ge2$. No landed theorem was found that supplies this eligible assertion for all admissible histories. If it fails, an incidence-component formulation can replace it, but its analogous source-to-output patch forest must then be established; that is still part of `OPEN-P6-STAR-AE`.

**Theorem 4.1 (combined corrected P6 localization, conditional).** Fix an admissible P6 history and source $X$ as above. Suppose its chosen old cover and tree satisfy SN–AG–GRID, including the rooted-forest rule for every coefficient not killed by clause 1; suppose `OPEN-P6-STAR-AE` holds with the stated common parameter index and `Ag_H` for **both** $H_-$ and $H_\partial$; and suppose the strict analytic estimate (3.4) holds for both on the same H7 polydisc. Assume (3.2), (3.6), $\kappa_0\ge0$, $\kappa\ge3\kappa_0+3$, and $\beta_k\ge1$. Then assigning (2.2)–(2.3) to each nonzero AE coefficient gives:

1. $Y_C\in\mathcal D_K^{\rm site}(\operatorname{mod}\Omega^c)$ with NN holes, $D(S_C)\le\Delta_X/L+dL|C|$, and a chosen cover and connected tree inside $Y_C$;
2. at each fixed **decorated** output $(X,S,\mathcal L)$, the weighted family count is at most one as in (3.3), and the sum of coefficients of either operator satisfies (3.8);
3. `LocalityAEOn` (4.2) holds for each of the two operators with the **same** output map $C\mapsto Y_C$ (and the respective complete read-collar relation `Ag_H`);
4. summing the decorated coefficients over all labels reproduces exactly each original operator term at $s=1$, hence their sum.

*Proof.* Theorem 2.1 gives item 1. At fixed label use the ledger as the `Yc` cell set in landed `boundary_gm3_fixed_Y_rate`, as in §3; this gives the count. Apply `abstract_expansion_on` to each operator using (4.2), (3.4) and reflexivity of `Ag_H`. Clause 1 of star AE removes the unrooted families. `exponent_arith_graph` and the count give (3.8), proving item 2. The inclusion of rooted supports in the assigned output and clause 2 of star AE prove (4.2) for all families, including those later killed, so item 3 holds. AE at $s=1$ is a finite identity; partitioning its finite index set by the deterministic label proves item 4. $\square$

Theorem 4.1 is a **complete implication with open P6 premises**, not an unconditional localization proof. In particular the constructed tree proves a bound for the corrected covering size (1.3); it does not discharge P6's printed block-union membership or original P5-size transfer.

## 5. Exact status and what remains open

**Proved in this note, for the stated finite record:** central-cube overlap, the corrected output membership, the tree bound (2.4), the fixed decorated-fiber count (3.3) by the cited landed theorem, and the exponent calculation (3.7) by the cited landed theorem. These are paper proofs, not claims of new landed Lean declarations.

**Conditional on named OPEN assertions:** a P6 instance of the theorem needs `OPEN-P6-HISTORY-GRID` (the actual old source and new domain realize SN–GRID), `OPEN-P6-SOURCE-ANCHOR` (the action read and all rooted coefficient clusters admit $A_0\subset B$, or a separately paid attachment), `OPEN-P6-STAR-AE` for each physical operator (including `OPEN-P6-ELIGIBLE-STARHAT` if the Moore-hat implementation is chosen), and `OPEN-P6-MIXED-H7` for the strict common-domain analytic bound (3.4). The latter comprises the still open `OPEN-H7-BG-MIXED`, `OPEN-DECOUPLED-WEIGHTED-RESPONSE`, and `OPEN-OLD-H7-DECAY` of `VMOD-13.md` §2. The row-5/6/7 scales, $k=k_0$ convention switch, and the $\nu$-free linear mass term must be kept in that analytic assertion. None is supplied by the geometric tree or count. `GRAPH-GM-2.md`'s `OPEN-P6-WITNESS-GEOMETRY` is avoided for the decorated output, not proved.

**Still needed for the printed P6 conclusion:** `OPEN-P6-DECORATION-ERASURE` must sum the ledger and $X$ at fixed undecorated $Y$ with a bound strong enough for (4.34), or supply a downstream RG norm that explicitly accepts the decorated labels and whose source/ledger entropy is controlled. Landed `SizeModEntropy.G2_S` controls only $S$, not $\mathcal L$ or $X$. P6's displayed source sum $K_0M_1^d|Y\cap\Omega|$ on printed p. 34 presupposes an output assignment and original modular size for which the thin-hole example invalidates the uncharged transfer. Therefore neither (3.8) nor `G2_S` may be cited as P6 (4.34). Replacing $d^{\rm cov}$ with P5's original modular $d$ is also **OPEN-P6-ORIGINAL-SIZE-TRANSFER**; the inequality $d^{\rm cov}\le d$ goes the wrong way for this step. A corrected class with decorated labels is a mathematically consistent organization of the same finite expansion, but adopting it throughout H7 is a substantive theorem and norm amendment.

## 6. Lean dependency order

Names in the middle column are **proposed**, not landed. Line estimates are for new code and do not include the analytic mixed-response campaign.

| Order | Proposed declaration and purpose | New lines | Landed declarations reused unchanged |
|---:|---|---:|---|
| 1 | `centralTopCube`, `patch_sub_central`, `central_overlap_of_star`, cyclic-grid lemmas | 180–320 | `PolymerGeometry.Pset_subset_cellOf`; `GraphGmCount.cellOfCube` |
| 2 | `p6_source_nest_bare`, old-cover witness and new-active coverage; then the separate actual-history anchor binder | 150–300 plus history port | `SizeModDefs.ModAdmissible`, `SizeModCore.exists_admissible_eq_dcovModE`; region nesting theorems cited in `GRAPH-GM-3.md` §3 |
| 3 | `rooted_star_boxes_nn_connected`, `active_trace_topCells`, `raw_sub_Yhat`, `siteMod_output` | 200–360 | `SizeModDefs.SiteConnected`, `OmegaComp`, `Yhat`, `IsPiUnion` |
| 4 | `central_boxes_mod_admissible`, `gm2_star_site`, cost $\Delta/L+dL|C|$ | 300–550 | `GraphGmTree.bondCost_scaleW_succ`, `SizeModCore.dcovMod_le_of_admissible` for the cost infimum. `GraphGmTree.modular_tree_of_witnesses` needs a **ported variant** and cannot be invoked unchanged because its face-cell and generated-cover binders differ. |
| 5 | `ledger_ownership`, `gm3_decorated` at fixed $(X,S,\mathcal L)$, `gm4_star_site` | 100–180 | `GraphGmCount.card_deriv_in_cell`, `GraphGmExponent.boundary_gm3_fixed_Y_rate`, `Vmod7Glue.exponent_arith_graph` unchanged. The general `GraphGmCount.fixed_output_count` also suffices with $G=1$. |
| 6 | `star_comp_dichotomy`, `incUnion_of_starComp`, `p6_eligible_starhat` or the incidence-component substitute | 250–650 after history bridge | `I5FluctGeom.footprint_sub_hat`, `Dec2.IsIncUnion.dichotomy`, `Dec2.i4a_local_fp`, `Dec2.i4b_local_fp`; port `I5FluctGeom.incUnion_of_nnComp`, do not reuse its false NN-hat premise. |
| 7 | `p6_locality_star_old`, `p6_locality_star_boundary`, `p6_locality_site_output`, common AE and bound | 250–500 after mixed H7 inputs | `I5Param.LocalityAEOn`, `abstract_expansion_on`, `coef_congr_of_agree_on` unchanged; port `Theorem42Input.DecoupledCubeResponse.loc` because it is typed with NN `compY`. |
| 8 | `p6_site_decorated_expansion` and, separately, `p6_decoration_erasure` or a decorated H7 norm | 120–250, then open research | `SizeModEntropy.G2_S` for active traces only; `GraphGmExponent.boundary_gm4_modular_of_witnesses` is a model but retains its false-for-P6 witness premises. |

**Confidence:** high for the finite top-cell construction, modular site output, and ledger count; medium for a short Lean port of the tree geometry; low for an unconditional P6 application until the history, star AE, mixed H7, and decoration-erasure assertions are proved. The long-thin-hole counterexample rules out silently reinstating the original uncharged P1/P5 output estimate.
