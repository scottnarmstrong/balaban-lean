# A site-support repair of the P6 boundary localization

**12 October 2026.** This answers `followup_r18.txt`. The chosen repair is a **decorated active-support reconstruction**. The size-transfer theorem and its fixed decorated-output count are proved below under an explicit finite witness record. Applying them to the actual P6 boundary operators and closing Definition 7 remains conditional on named open assertions. In particular, this note does **not** claim an unconditional proof of P6 (4.33)–(4.34) or preservation of the new representation class. All `/home/scott/Balaban` files cited here were read only.

## 1. Decision: three proposed repairs and the chosen output

P6, printed p. 34, between (4.32) and (4.33), moves the old boundary activity to a new modular polymer and claims an uncharged size transfer. The long thin hole in `VMOD-16.md` disproves that transfer for P1 block-union outputs. P5 (1.33)–(1.34), printed p. 496, does not make traversal of a hole free: its tree need not meet blocks **inside** the hole, but each bond of a path through it still contributes to tree length. The landed `SizeModDefs.ModAdmissible` chooses contained cover blocks and `dcovMod` takes their minimum; neither is the collared size proposed in (B). An active block of the forced collar must still be covered by a chosen block. The chosen-family convention only omits unchosen blocks, not all blocks of a long active collar.

**(A), a history-weighted D7.** A possible charge inequality has the shape
$$n_{\rm hole}(Y)\le uN(Z')+vS_k(Y),\qquad
N(Z')=|\mathsf P_{k+1}\cup\mathsf Q_{k+1}\cup\mathsf R_{k+1}\cup\mathsf S_{k+1}|_{Z'}.$$
An old shadow can create a new collar when $N=0$ (`VMOD-17.md` §1), so $S_k$ cannot be suppressed. The landed `BudgetConsts.kappaStep` gives $a_kN-b_kO$; `BudgetSetup.gain_ge` only establishes the prescribed gain $g_k\le a_k$, with no proved surplus for $uN$, and no old-shadow credit paying $vS_k$. More decisively, `Def7.D7Bdry.bound` and `Def7v2Class.D7Bdry2.bound` are *unweighted bounds for each coefficient* before the large-field operator is applied. The weighted calculation in `VMOD-17.md` §3 is a valid conditional estimate for a **linear operator contribution**, but it is not the bound on the exponentiated boundary sum used by D1. A complete (A) would need a new coupled D1/D5/D6/D7 class, an exponential-integrability argument and a preservation theorem. These are `OPEN-P6-WEIGHTED-D7` and `OPEN-P6-SHADOW-BUDGET`; none is supplied by the landed budget.

**(B), collared holes.** Let $F^+$ be the union of new $\pi'_K$ blocks meeting a component $F$ of $\Omega^c$, and define $d_B$ by meeting the blocks of $Y$ outside contained collars, while meeting each included $F$ at least once. This does cure the single thin-tube size counterexample, but it destroys two estimates that use size. Here is a counterexample to a uniform P5-type G2 for the stated size. Work on a large three-dimensional torus with $L\ge3$, using top-cell units. Take two parallel NN holes $F_1,F_2$, each a tube one top cell thick and of length $T$ top cells, separated by a fixed gap $D>4L$; take $\Omega$ to be their complement, a union of top cells. Their width is smaller than one new overlapping block. Write $C_i=F_i^+$. For $t$ at spacing $2L$ along the tubes, let $B_t$ be a shortest chain of new overlapping blocks across the gap at longitudinal coordinate $t$ and put $Y_t=C_1\cup C_2\cup B_t$. Choose the block chain so that $Y_t$ is NN connected. It is a P1 block union and contains both holes modularly. Every $Y_t$ contains the same active top cell $A\subset C_1\cap\Omega$ near the first end of the tube. Apart from the two collars, the required blocks lie in $B_t$; a tree from $F_1$ through $B_t$ to $F_2$ has $d_B(Y_t)\le c(d,L,D)$, independent of $t,T$. There are at least $\lfloor T/(2L)\rfloor-O(1)$ distinct $Y_t$. Thus
$$\sum_{Y\ni A}e^{-\lambda d_B(Y)}\ge
\bigl(\lfloor T/(2L)\rfloor-O(1)\bigr)e^{-\lambda c(d,L,D)}\longrightarrow\infty.$$
This is a **proved finite-geometry obstruction** for arbitrary cell-union $\Omega$, the ambient hypothesis of landed `SizeModEntropy.G2_X`; it does not assert that every such pair of holes arises in a particular P6 history. Counting holes does not help: $n_{\rm components}(Y_t\cap\Omega^c)=2$ for every $t$. Requiring the tree also to reach the fixed anchor $A$ would charge $t$, but then the size is root-marked and D7 must store that root. Requiring all boundary-crossing cover blocks along $C_i$ recovers a cost proportional to $T$ and loses the intended thin-tube cure.

There is a simpler G1 failure. For one long thin hole, $Y=F^+$ has $|Y\cap\Omega|_K\asymp T$ while $d_B(Y)=O(1)$. Hence no history-uniform constant gives $|Y\cap\Omega|_K\le C(1+d_B(Y))$. P6 printed p. 34 uses precisely a volume factor $K_0 M_1^d|Y\cap\Omega|$ and absorbs it in an exponential of size; the landed analogue is `SizeModG1.G1_cellCount` for `dcovMod`. The small value of $d_B$ also ceases to express decay between distant field reads on the active collar. Analytic locality on the *large* $Y$ might still hold, but its support is no longer controlled by the proposed decay. Thus (B) needs a new rooted or decorated entropy theorem and cannot inherit G1, G2 or H7 merely because the holes are history-fixed. `Hole.pe_hole` counts hole polymers with its own Steiner-size premises; it does not prove G1 or G2 for $d_B$.

**(C), absorption into the new large-field integrand.** P6 (4.32), printed p. 33, contains old $B(X)$ touching both the new $Z_K$ and its complement. Such an $X$ can touch more than one disconnected pre-$R$ component and depends on active fields and history over all of $X$. A term entirely supported in one component's integration/read collar can be moved into that component's local integrand after a separate bound. Moving a general $B(X)$ into one local step kernel would break the product over components and the S4 locality used in D5; moving it into a global kernel changes D1 and requires a fresh D5 bound for the exponential. The P6 construction does not supply either factorization. The boundary re-expansion is still needed for the terms crossing several components. Thus (C) is not a general repair.

**Choice.** We change the boundary *output* to a connected site support with a deterministic hole completion and retain source and derivative-cell labels. This retains the landed `dcovMod` and the proved active-support entropy `SizeModEntropy.G2_S`; it does not silently invoke P1 block-union membership. The price is an explicit decoration-erasure or decorated-norm obligation at D7. The corrected transfer below has no shadow charge and applies even when the new hole is arbitrarily long. It is cheaper than rebuilding the large-field budget or changing the geometric size in every consumer.

## 2. Exact definitions and corrected transfer

Let $K=k+1$, $\Omega=\Omega_K$, $a=ML^K$ in fine-site units, and let holes mean NN components of $\Omega^c$. For a nonempty union $S$ of top $\pi_K$ cells contained in $\Omega$, define
$$\widehat Y_\Omega(S)=S\cup\bigcup\{F:F\text{ is a hole and }F\sim_{\rm NN}S\},
\qquad D_\Omega(S)=d_K^{\rm cov}(\widehat Y_\Omega(S)\operatorname{mod}\Omega^c).\tag{2.1}$$
The output domain is the set of pairs $(S,\widehat Y_\Omega(S))$ for which $\widehat Y_\Omega(S)$ is NN connected and $D_\Omega(S)<\infty$. It is **not** required to be a union of $\pi'_K$ cubes. The same `ModAdmissible` chosen-cover definition measures (2.1); this is landed `SizeModDefs.Yhat`, `dOmega`. The completed hole set is determined by $S$, as in landed `SizeModStruct.S_eq_recon`. Distinct auxiliary labels below are nevertheless retained.

For an old boundary source $X$ let $\Delta_X=d_k^{\rm cov}(X\operatorname{mod}\Omega_k^c)$ and fix one minimizing old chosen cover and tree, independently of every derivative family. Put $G=(2L+1)^d$. The finite **SN–AG–GRID witness record** consists of:

1. **SN:** $X\cap\Omega\ne\varnothing$; a finite set $\mathcal B$ of new $\pi'_K$ cubes has union $B$, with $X\cap\Omega\subset B$, every member of $\mathcal B$ meeting $X$, containing an old chosen cover cube, and being met by the old tree. The original $X$ and tree are in the torus.
2. **AG:** a nonempty action anchor $A_0\subset B$ and an effective derivative family $C$ of aligned parameter patches $Pset(P)$, each inside its top $\pi_K$ cell, whose Moore-incidence graph is a forest rooted at $A_0$. A root patch Moore-touches $A_0$; a nonroot patch Moore-touches its parent. This is a *property of the actual coefficient*, not an automatic property of arbitrary parameters.
3. **GRID:** $L\ge3$, aligned top cells exist on the torus, and $\Omega$ is their union. Cyclic boxes and paths are used at the seam.

For each $P$, let $T(P)$ be its top cell of side $a$ with base $b(P)$ and choose the central overlapping cube
$$Q(P)=\operatorname{box}(b(P)-a(1,\ldots,1),La).\tag{2.2}$$
It contains $T(P)$ and every fine-site Moore neighbor of it. Define
$$R_C=X\cup B\cup\bigcup_{P\in C}Q(P),\quad
S_C=R_C\cap\Omega,\quad Y_C=\widehat Y_\Omega(S_C),\quad
\mathfrak y_C=(X,S_C,\mathcal L_C),\quad
\mathcal L_C=\{\operatorname{cellOfCube}(P):P\in C\}.\tag{2.3}$$
An output label includes its old source and layer-cell ledger. This is a deterministic sorting of a finite AE expansion, so summing over all labels gives back the original analytic function whenever the AE expansion is valid.

**Theorem 2.1 — corrected site transfer (PROVED under SN–AG–GRID).** The set $Y_C$ is a connected modular site output, $R_C\subset Y_C$, $S_C$ is a nonempty top-cell union in $\Omega$, and
$$D_\Omega(S_C)\le L^{-1}\Delta_X+dL|C|.\tag{2.4}$$
The constants are $C_1=1/L$ and $C_2=dL$. No term proportional to the volume of an included hole or its forced block collar occurs.

*Proof.* $X$ and each cube of $\mathcal B$ are NN connected and meet one another through $X$. If two patches Moore-touch, the central cube of either one contains the two touching sites; hence their central cubes overlap. The first cube of a rooted branch meets $B$ for the same reason. Traverse the forest to see that $R_C$ is NN connected. Since $X\cap\Omega\subset B$, one has $S_C=(B\cup\bigcup Q(P))\cap\Omega$, a union of top cells; it is nonempty. Every point of $R_C\setminus\Omega$ has a path inside $R_C$ to $S_C$. Its segment before its first entry into $S_C$ lies in one NN hole adjacent to $S_C$, so $R_C\subset\widehat Y_\Omega(S_C)$. The latter is connected and contains or avoids each entire NN hole, proving modularity.

Use $\mathcal B\cup\{Q(P):P\in C\}$ as a new chosen cover. It lies in $Y_C$ and covers $S_C$. The old tree meets every member of $\mathcal B$ by SN. Connect each newly added $Q(P)$ to its parent or to $B$ by a coordinate path inside the predecessor cube, stopping at their intersection. Such a path has fewer than $dLa$ bonds. The enlarged tree lies in $R_C\subset Y_C$ and meets every chosen cover cube. Old bonds cost $1/L$ of their old normalized cost, by the scale relation formalized as `GraphGmTree.bondCost_scaleW_succ`. The new path cost is at most $dL$ per $P$. Apply `SizeModCore.dcovMod_le_of_admissible` to obtain (2.4). The old minimizing pair exists by `SizeModCore.exists_admissible_eq_dcovMod` when the source is admissible. $\square$

The landed `GraphGmTree.modular_tree_of_witnesses` and `GraphGmExponent.modular_size_le_of_witnesses` prove the related inequality $d_K^{\rm cov}(Y)\le\Delta_X/L+dG|C|$ **if** their source nesting, rooted face-cell witness, output generator, and cover premises hold. In the thin-hole history, their block-union output premise is exactly what cannot be inserted for free. Theorem 2.1 changes that premise: a Moore-rooted *central-cube* cover of a site output supplies an admissible `SizeModCore` pair directly and improves $dG$ to $dL$. This is a new Lean corollary of the landed tree-path ingredients, **not** a claim that either landed witness theorem already proves (2.4). P5's original all-intersecting-block size remains a different size; no inequality for it is asserted.

The active-volume bound survives the change. For any minimizing admissible pair of $Y=\widehat Y_\Omega(S)$, `SizeModCore.cellCount_le_of_admissible` gives
$$|S|_K\le c_G(1+D_\Omega(S)),\qquad c_G=[3(2L-1)]^d.\tag{2.5}$$
The same constant is used by `SizeModG1.G1_cellCount` for block-union outputs; (2.5) uses its underlying admissible-pair counting lemma and does not need `IsDj`. It is the exact replacement for the $|Y\cap\Omega|$ absorption on P6 p. 34. Holes can have arbitrary volume, but $Y\cap\Omega=S$.

## 3. Fixed-output resummation, with its precise limit

Put $A'=L^{dm_0}$, $\kappa_2=\kappa_1/2-1$. At a fixed label $\mathfrak y=(X,S,\mathcal L)$ let $\mathscr F(\mathfrak y)$ be the finite family of contributing derivative sets. Assume the layer index and alignment premises of `GraphGmExponent.boundary_gm3_fixed_Y_rate`, and
$$\kappa_1\ge6,\qquad
\kappa_1\ge4d\log((2L+1)L^{m_0})+2.\tag{3.1}$$
Apply that landed theorem with its abstract output cells `Yc` equal to $\mathcal L$, `Bc=\varnothing$ and $D(P)=\{\operatorname{cellOfCube}(P)\}$. Every selected derivative has its label in $\mathcal L$, every label has an owner, and $|D(P)|=1\le G$. It follows that
$$\sum_{C\in\mathscr F(\mathfrak y)}e^{-\kappa_2|C|}\le1.\tag{3.2}$$
This is **PROVED CONDITIONAL ON the PROVED cited `boundary_gm3_fixed_Y_rate`**, with its displayed alignment hypotheses. It is a fixed **decorated** fiber count; it says nothing about the number of ledgers for a given $S$.

For either P6 old-boundary operator $H\in\{H_-,H_\partial\}$, assume a common strict H7 polydisc of radius $e^{\kappa_1}$ and an analytic function $F_X^H(u,s)$ satisfying
$$\sup_{u,s}\|F_X^H(u,s)\|\le\beta_k^{-2}e^{-(\kappa-1)\Delta_X}.\tag{3.3}$$
Assume also `OPEN-P6-STAR-AE`: ineffective parameters have zero AE coefficients; effective patches have the rooted Moore forest of AG; and agreement on the completed output includes every action and decoupled-field read collar for both operators. The landed `I5Param.abstract_expansion_on` then gives, by Cauchy,
$$\|a_{X,C}^H\|\le\beta_k^{-2}e^{-(\kappa-1)\Delta_X-(\kappa_1-1)|C|}.\tag{3.4}$$
For $\kappa_0\ge0$, $\kappa\ge3\kappa_0+3$ and $\kappa_1\ge4dL\kappa$, the arithmetic of landed `Vmod7Glue.exponent_arith_graph`, applied to (2.4) with $C_{\rm graph}=dL$, gives
$$\|a_{X,C}^H\|\le\beta_k^{-2}e^{-\kappa_0\Delta_X-2\kappa D_\Omega(S_C)-\kappa_2|C|}.\tag{3.5}$$
Equations (3.2)–(3.5) prove the **fixed decorated-output bound**
$$\|B^H(X,S,\mathcal L)\|\le
\beta_k^{-2}e^{-\kappa_0\Delta_X-2\kappa D_\Omega(S)}
\le\beta_k^{-3/2}e^{-2\kappa D_\Omega(S)}\quad(\beta_k\ge1).\tag{3.6}$$
The finite-sum algebra in (3.6) is **PROVED CONDITIONAL ON OPEN-P6-STAR-AE, OPEN-P6-MIXED-H7 and the SN–AG–GRID record for actual P6**. Both $H_-$ and $H_\partial$ need these premises separately. This is the corrected (4.33)–(4.34)-type statement for the *chosen* fixed label; it is not an estimate at fixed undecorated $Y$.

Here is the exact remaining fixed-$S$ statement. Suppose a **new**, history-uniform fiber theorem supplies constants $H\ge1$, $q\ge0$ such that for each old source and active output
$$\sum_{C:S_C=S}e^{-\kappa_2|C|}\le H e^{q\Delta_X}.\tag{3.7}$$
Call (3.7) `OPEN-P6-UNDECORATED-FIBER`. Set $\mu=\kappa_0-q$ and assume $\mu\ge a_{\rm ent}(d,L)+1$. The landed `SizeModEntropy.G2_X` at an old active anchor cell gives $\sum_{X\ni q_0}e^{-\mu\Delta_X}\le K_0(d,L,\mu)$. Each source contributing to $S$ contains such an old cell inside some new cell of $S$, and each new cell has $L^d$ old cells. By (2.5), at most $L^dc_G(1+D)$ anchor choices occur. Consequently
$$\|B^H(S)\|\le\beta_k^{-2}H L^d c_GK_0(d,L,\mu)
(1+D)e^{-2\kappa D}
\le\beta_k^{-2}H L^d c_GK_0(d,L,\mu)e^{-(2\kappa-1)D}.\tag{3.8}$$
The last step is $1+D\le e^D$. If $\beta_k^{1/2}\ge H L^dc_GK_0(d,L,\mu)$, this is the literal P6-style prefactor $\beta_k^{-3/2}$. The source-anchor argument requires $X\cap\Omega\ne\varnothing$ and SN, as stipulated. Put $\lambda=2\kappa-1$. If $\lambda\ge a_{\rm ent}(d,L)+1$, landed `SizeModEntropy.G2_S` gives, for any fixed active top cell $A$,
$$\sum_{S\supset A}\|B^H(S)\|\le
\beta_k^{-2}H L^dc_GK_0(d,L,\mu)K_0(d,L,\lambda).\tag{3.8a}$$
These are **PROVED implications from the named landed G1/G2 results and OPEN (3.7)**, not an unconditional preservation result. In particular `G2_S` counts supports, not the decorations in (3.6).

The proposed D7 norm for this reconstruction is therefore
$$\|B\|_{7,\mathrm{site}}=
\sup_{A,h,u,S}e^{\kappa D_\Omega(S)}
\sum_{X,\mathcal L}\|B_A(X,S,\mathcal L;u,h)\|.\tag{3.9}$$
The variables $u,h$ range over the corresponding strict H7 domain and pinned external-field ball in v2. Formula (3.9) is an **exact definition**; finiteness at the required scale is **OPEN-P6-DECORATION-ERASURE**, for which (3.7) is one sufficient route. It cannot be inferred by applying (3.2) separately to arbitrarily many ledgers. Once (3.9) holds, the D1 boundary sum is the absolutely convergent sum over the labels; on a finite torus the identity with the original AE expansion follows simply by regrouping. Uniform constants independent of torus and history still require (3.7) or another proof of (3.9).

## 4. Every representation consumer of the new output

Changing from a Finset block-union boundary index to $(X,S,\mathcal L)$ is a genuine change of **boundary data type**, not merely a new estimate for an existing `Rep.B`.

| Landed location | Clause or data | Required revision and status |
|---|---|---|
| `Def7Hist.lean` | `IsBdryDom`, `bdryDoms`, `dCovMod`; `Rep.B`, `Rep.bdrySum` | Define a decorated site boundary index and its admissibility for each history; index `B` and `bdrySum` by it, with size $D_\Omega(S)$. **OPEN** as Lean definitions and equivalence of the reorganized finite sum. `dCovMod` remains valid as a size function on site sets; its old block-domain guard is replaced. |
| `Def7.lean` | D1 `integrand`/`IsRep.form` | Replace the exponentiated `bdrySum` by the sum over decorated site outputs. Recheck equality to the P6 expanded integrand, including $k=k_0$ and complete/$\nu$-free conventions. **OPEN** for P6; finite AE regrouping is proved under the premises in §3. |
| `Def7.lean` | D7 `loc_field`, `loc_hist`, `real`, `analytic`, `bound`, `rot`, `euclid` | All seven fields quantify over `bdryDoms` or evaluate `rep.B A X`, so **all seven statements change** to a decorated index and its physical read collar. `bound` uses either (3.9) or a bound on the summed coefficient at fixed $S$, with H7 tested on the site output. Symmetries must act on $X,S,\mathcal L$. **OPEN** preservation. |
| `Def7.lean` | D2 `sfData`, D4 `pin`, D5 `opBound`, D6 `budget`, D8 `coherent`, D9 `coeff`, `complete`, `coh`, `field` | Their **statements do not change** when LF operators, regions and small-field data are left as they are. D5/D6 estimates and D2 H7 compatibility must be rechecked in the induction because the D1 integrand changes its decomposition. No payment from them is assumed. |
| `Def7Variants.lean` | `IsRepPre`, `IsRepFlat`, `IsRepFam`, `IsRepFamPre` | Pre/flat D1 and D7 fields change; family `member` points to the revised class. The remaining fields retain their statements. **OPEN** preservation and $\nu$-uniformity. |
| `Def7v2Form.lean`, `Def7v2Class.lean` | `integrand2`, `D1Form2`, `D7Bdry2`, `IsRep2` | The v2 integrand also calls the old `rep.bdrySum`; revise D1 and **all seven** D7Bdry2 fields, including its pinned-ball `analytic` and `bound`. In `IsRep2`, `form` and `bdry` change; `corr`, `sfData`, D4–D6, D8, D9, `complete`, `coh`, `field` retain their statement. `D7Bdry2.toD7Bdry` needs a corresponding decorated comparison map. The v2 class is itself marked DRAFT pending Q13 in the landed file. |
| `Def7v2Variants.lean`, `Def7v2Class.lean`, `Def7v2.lean`, `Def7v2Interface.lean` | `IsRepPre2`, `IsRepFlat2`, `IsRepFam2`, `IsRepFamPre2`, `RepClass2`, `IsRep2WithInterface`, `IsRepCorr`, `IsRepA` | Pre/flat `form` and `bdry` statements change; family `member` and wrapper predicates inherit the revised class. `IsRep2WithInterface.iface` has no boundary-index change, but its preservation must be rechecked against the new D1 representation. The old `IsRepCorr`/`IsRepA` wrappers similarly inherit any revised v1 base class. **OPEN**. |

The new boundary locality is stated on $\widehat Y_\Omega(S)$ *plus the exact action/field read collar specified by `OPEN-P6-STAR-AE`*. A claim that agreement only on the sites of $S$ implies equality would be too weak for the decoupled field. The old external field and $\nu$ clauses are not used to pay a geometric collar.

## 5. Lean dependency order and statuses

The proposed names below are not landed. Line estimates count new code only; research interfaces have no reliable size until their mathematical assertion is settled.

| Order | Proposed lemma or construction | New lines | Landed input and status |
|---:|---|---:|---|
| 1 | `siteOutput`, `decoratedBdryIndex`, deterministic source-cover tie-break, `siteOutput_eq_recon` | 100–180 | `SizeModDefs.Yhat`, `dOmega`; `SizeModStruct.S_eq_recon`. **PROVED mathematical definition; Lean OPEN.** |
| 2 | `centralCube_contains_moore`, `centralCube_overlap`, `rootedForest_connected` | 150–300 | `PolymerGeometry.Pset_subset_cellOf`, top-cell grid lemmas. **PROVED under GRID; Lean OPEN.** |
| 3 | `p6_site_admissible`, `p6_site_size_transfer` yielding (2.4), plus `site_active_cellCount` yielding (2.5) | 250–450 | `SizeModCore.exists_admissible_eq_dcovMod`, `dcovMod_le_of_admissible`, `cellCount_le_of_admissible`; `GraphGmTree.bondCost_scaleW_succ`. Compare exact witness fields of `GraphGmTree.modular_tree_of_witnesses` and `GraphGmExponent.modular_size_le_of_witnesses`; do not reuse their false block-output premise. **PROVED under SN–AG–GRID; actual P6 SN/AG OPEN.** |
| 4 | `decorated_fixed_fiber_rate` (3.2), `site_exponent_arith`, `decorated_fixed_bound` (3.6) | 120–220 | `GraphGmExponent.boundary_gm3_fixed_Y_rate`, `Vmod7Glue.exponent_arith_graph`, `I5Param.abstract_expansion_on`. **PROVED CONDITIONAL ON named landed results and OPEN analytic premises.** |
| 5 | `p6_source_anchor`, `p6_moore_star_ae`, `p6_mixed_h7` for both $H_-,H_\partial$ | research scope | `Dec2.i4a_local_fp`, `Dec2.i4b_local_fp`, `I5Param.LocalityAEOn`; the needed common-cover, source-to-index and H7 interfaces are described in `VMOD-13.md`–`VMOD-15.md`. **OPEN-P6-SOURCE-ANCHOR, OPEN-P6-STAR-AE, OPEN-P6-MIXED-H7, OPEN-P6-HISTORY-GRID.** |
| 6 | `site_undecorated_fiber` (3.7), `fixed_site_resummation` (3.8), `site_support_entropy` | 150–300 after fiber theorem | `GraphGmCount.fixed_output_count` does not supply (3.7); `SizeModEntropy.G2_X`, `G2_S`, `SizeModCore.cellCount_le_of_admissible` supply the subsequent sums. **Fiber OPEN; implications PROVED CONDITIONAL ON it.** |
| 7 | `RepSite`, `D7BdrySite`, `D7Bdry2Site`, revised D1 forms, pre/flat/family wrappers and induction preservation | research scope | `Def7Hist`, `Def7`, `Def7Variants`, `Def7v2Form`, `Def7v2Class`, `Def7v2Variants`, `Def7v2Interface`; `Hole.pe_hole` is a separate counting theorem, not a substitute. **OPEN-P6-DECORATION-ERASURE and OPEN-P6-REP-PRESERVATION.** |

**Status and confidence.** The no-go for uniform G1/G2 under (B), Theorem 2.1 under its explicit record, and the finite resummation implications are **PROVED**. Equations (3.2), (2.5) and the support/source sums are **PROVED CONDITIONAL ON the named landed results and their displayed hypotheses**. Actual P6 use and the revised Definition 7 induction are **OPEN** under the names above. Confidence is high in the finite geometry and algebra, medium in a short Lean port of them, and low in unconditional P6 closure until the analytic star and decoration fiber are proved. No result under an OPEN binder is relabeled as proved by this choice of definitions.

## Addendum to question 14 for the author

P6 p. 34 appears to require a new modular size bound for the old boundary terms after a new hole is formed. A long thin hole forces an active collar if the output is a P1 union of overlapping cubes; the claimed uncharged bound fails for that output. Excluding the collar from size makes the usual fixed-cell entropy and active-volume estimates fail, even for two fixed holes. We therefore read the localization as a site-support expansion: record the active top-cell support, complete adjacent NN holes, and retain the old source and derivative-cell labels while counting. Its chosen-cover size satisfies $D(S)\le d_k^{\rm cov}(X)/L+dL|C|$ under the stated rooted patch geometry. The remaining question is whether the two P6 boundary operators have the required common H7/Moore locality and whether the labels can be summed uniformly at fixed support. The printed argument does not establish those two assertions.
