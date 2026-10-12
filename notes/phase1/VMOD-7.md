# Anchored incidence counting and the mixed-wall cut estimate

**12 October 2026.** This note answers `followup_r7.txt` using the landed Lean files as they stand. Two assertions requested there remain open: a graph-to-hole-polymer comparison and uniform NC3 at an internal Dirichlet wall. There is also a concrete obstruction to applying the landed GM3 to the raw site projection of `seedClosure`. Below are the exact proposed interfaces, a proved local incidence bound, a proved entropy obstruction, and the numerical consequences that follow *if* the missing geometric and analytic estimates are supplied. No file under `/home/scott/Balaban` was changed.

Set $K=k+1$, $d,L\ge3$, $M_1=L^{m_1}\ge4L^2$, $M=L^{m_0}M_1$, and $L^{m_0}\ge L+9$. Work on the finite torus of side $(N_1L^{m_1})L^K$, with the divisibility and more-than-five-coarse-cells assumptions of `VMOD-2.md` §1. Let $F^\sharp$ be its haloed auxiliary generating set, $C=\operatorname{coverOf}F^\sharp$, and $H$ one of $H^-=\mathbb B_k(W_k)$ or the **boundary** $H^\partial=\mathbb B_{k+1}(\partial\Omega_{k+1})$. The first-domain inclusions and common partition are in landed `Balaban/Localization/CoverPartition.lean`: `coverOf_partition_of_subset` and `commonCover_partition`. The latter takes its layerwise history inclusions as hypotheses; it is not a Lean formalization of the LFR history.

## 1. Exact landed interfaces

For a fine-site set $X_1$ and charged parameter set $\mathcal C$, `Balaban/Localization/Decoupled2FpGeometry.lean` defines `incGraph C H a ν X₁ 𝒞` and `IsIncUnion`. The latter says only that the site and parameter projections come from some adjacency-closed vertex set. In `Balaban/Localization/Decoupled2FpCount.lean`, `seedClosure C H a ν X₁ 𝒞 S` is the set of graph vertices reachable from a site seed $S$; `seedSites` and `seedParams` are its projections. The landed `isIncUnion_seed`, `seedClosure_le`, and `seedSites_subset_incSites` prove closure, minimality, and active-site containment for $S\subset X_1\cap\Omega_1(H)$. The landed `not_universal_gm2` is a **conditional logical** obstruction for unanchored `IsIncUnion`: its positive whole-torus cost is the hypothesis `hpos`, not a formal proof about `treeLenCov`.

The size theorem `Balaban/Localization/TreeLengthCov.lean gm2_tree` has substantially different inputs: `CovSetup`, a connected input witness $\Gamma_0\subset X$, a connected family of physical `Pset` pieces relative to `compY`, and a chosen output family for `Ysites`. Its conclusion bounds a connected output tree by
$$L^{-1}\operatorname{cost}(\Gamma_0)+d(2L+1)^d|\mathcal C|.\tag{1.1}$$
`PolymerCount.lean gm3` counts **families whose `Ysites` equals a fixed $Y$**, each charged `Pset` disjoint from $X_1$, under
$$\kappa_2/2\ge1,\qquad
\kappa_2/2\ge\log\bigl((2L+1)^d(L^{m_0})^d\bigr).\tag{1.2}$$
`PolymerCount.lean gm4` combines its ordinary `gm2` with the exponent inequality under $\kappa\ge3\kappa_0+3$ and $\kappa_1\ge4d(2L+1)^d\kappa$. None of these declarations mentions `incGraph`, `seedClosure`, a physical hole, or `HolePolymer`.

In `Balaban/Polymer/Hole.lean`, `HolePolymer H_B S_0` is a connected block set that is not contained in the hole $S_0$ and contains every hole component it touches; `holeSupp` is its charged part outside $S_0$. `steiner H_B (holeSupp P)` is the minimum **number of blocks** of a connected block set containing that charged part. `pe_hole` assumes an activity bound in this Steiner size and a degree bound on $H_B$; it constructs the polymer expansion and its entropy bound. It does not convert a fine-site incidence closure into a hole polymer or compare Steiner size with `treeLenCov`.

## 2. A proved local block bound, and why it is not GM2

Let $a_m=M_1L^m$, and let $P$ be a charged parameter cube incident in `incGraph` to a live eligible center $z$ of scale $m$. For the P6 boundary pair, `VMOD-4.md` (4.3) gives $\operatorname{footprint}_H(z)\subset\widehat D_z$, conditional on the LFR layer comparison. `VMOD-5.md` (3.1)–(3.2) then prove, for **every** $t$ in that footprint and **every** $p\in P$,
$$d_\infty(t,p)<(L+13/2)a_m.\tag{2.1}$$
Since $m\le K$ and $L^{m_0}\ge L+9$,
$$ (L+13/2)a_m\le(L+13/2)M_1L^K<M L^K=:b_K.\tag{2.2}$$
Choose one $p\in P$. Every footprint site of every center incident to $P$ therefore belongs to one of the at most $3^d$ $\pi_K$ cells in the cyclic Moore neighborhood of the $\pi_K$ cell of $p$. This count includes all centers incident to $P$; multiplying it by the reverse center-degree $N_0=3(8L)^d$ is unnecessary. The full $3^d$-cell neighborhood is connected in the **ambient** nearest-neighbor block graph. Choosing one footprint witness in each occupied cell and joining it to $p$ by coordinate geodesics uses at most $d,3^d b_K$ fine bonds, so its ambient cost normalized by $b_K$ is at most
$$C_{\mathrm{star}}(d)=d,3^d\quad\text{per charged }P.\tag{2.3}$$
The proof uses only the cyclic coordinate triangle inequality, (2.1), and the grid size assumption. It remains valid when $P$ lies outside $\Omega_1(H)$: the ambient paths are not asserted to be operator paths.

Equation (2.3) is the complete **ambient star** bound, not a bound for `treeLenCov` or the modular size. Its chosen paths and some of its $3^d$ cells may leave $F^\sharp.\Omega_1$, the final output domain, or the allowed hole completion. A charged parameter vertex can bridge two physical components without supplying a nearest-neighbor path through either. To promote (2.3) to (1.1), one must provide admissible paths, preserve the source tree across the old and new holes, build complete chosen $\pi'_n$ families, and charge all inserted hole connectors. The landed `gm2_tree` supplies none of these statements for `seedSites`.

**Abstract gluing lemma (proved conditional on its stated geometric inputs).** Suppose $\Gamma_0$ has been retained in an output domain with output bond cost at most $L^{-1}\Delta$. Suppose the charges can be ordered so that, for each $P$, an admissible finite bond set $E_P$ inside that domain meets every new chosen output cube assigned to $P$, joins the preceding connected structure, and costs at most $d3^d+C_{\rm bridge}(d,L)$. Then the union of $\Gamma_0$ and the $E_P$ is connected and meets the chosen family; nonnegative bond weights and pruning give (4.1) with the **explicit conditional value**
$$C_{\rm graph}=d3^d+C_{\rm bridge}(d,L).\tag{2.4}$$
The proof is induction over the charges and subadditivity of bond cost. The open content is the existence of these admissible $E_P$ with a uniform $C_{\rm bridge}$, including any costs of hole closure and chosen-family completion. Equation (2.3) alone does not supply them.

## 3. Entropy obstruction for the raw anchored site projection

**Proposition (proved from the graph definitions).** Suppose $\Omega_1(H)\subset X_1$, this nonempty first domain is nearest-neighbor connected, and $\varnothing\ne S\subset\Omega_1(H)$. Then for **every** charged set $\mathcal C$,
$$\operatorname{seedSites}(C,H,a,\nu,X_1,\mathcal C,S)=\Omega_1(H).\tag{3.1}$$

**Proof.** By the definition of `incSites`, every graph site lies in $\Omega_1(H)$; the inclusion $\Omega_1(H)\subset X_1$ supplies the other disjunct for every site of $\Omega_1(H)$, independently of eligibility and $\mathcal C$. Thus `incSites` equals $\Omega_1(H)$. `incRel` contains every nearest-neighbor edge between these sites. From any seed site, connectivity reaches all of $\Omega_1(H)$. Conversely, landed `seedSites_subset_incSites` excludes every other site. $\square$

If the allowed charge universe has a parameter $P$, both $\mathcal C=\varnothing$ and $\mathcal C=\{P\}$ have the same raw output $Y=\Omega_1(H)$. For every finite $\kappa_2$ their two weights sum to
$$1+e^{-\kappa_2}>1.\tag{3.2}$$
Thus a literal GM3 statement $\sum_{\mathcal C:\operatorname{seedSites}(\mathcal C)=Y}e^{-\kappa_2|\mathcal C|}\le1$ is **false** for all charge sets admitted by the landed graph definitions. This does not say that both Cauchy coefficients in an actual localization expansion are nonzero; a proof that irrelevant charges vanish is a further input. To obtain an entropy theorem, the output must record effective charged parameters (for example `seedParams`, with a proof that every charged derivative is reached), or include their parameter cubes in the charged block support **when those cubes lie outside the hole**. A parameter cube inside the hole needs an exterior charged witness or a separately counted decoration. The site projection alone discards the information that `gm3` counts through its added `Pset` pieces.

## 4. Precise replacement target and its conditional arithmetic

Here is a statement with the necessary objects and quantifiers. It is **OPEN-ANCHORED-GRAPH-GM2/GM3**, not a theorem proved by the landed declarations. Fix an admissible P6 source $X\in\mathcal D_j(\bmod(\Omega_{\rm in})^c)$ with nonempty charged intersection, a chosen input family $\mathcal K_X$, and a minimizing connected physical tree $\Gamma_0\subset X$ of covering cost $\Delta=d_j^{\rm cov}(X\bmod(\Omega_{\rm in})^c)$. The tree measures **actual traversed bonds through holes**. Choose $X_1$ and an evaluation seed $\varnothing\ne S\subset X_1\cap\Omega_1(H)$ according to P6, including its independently paid collar. For every finite $\mathcal C\subset C.\mathrm{parCubes}(X_1)$, let $(Y_{\mathcal C},A_{\mathcal C})$ be the landed `seedSites`/`seedParams` of its `seedClosure`. Retain only effective charge families, by a proved support condition implying $\mathcal C=A_{\mathcal C}$ or by another injective record of the active charges.

On the periodic $\pi_K$ block graph $H_B$ (nearest-neighbor degree $\Delta_B\le2d$), take $S_0$ to be the blocks of the new physical hole **when that hole is a union of these blocks**; otherwise a block-level replacement and its comparison to the P6 hole must first be proved. The proposed theorem must construct, for each retained $\mathcal C$:

1. A block polymer $P_{\mathcal C}:\operatorname{HolePolymer}(H_B,S_0)$ whose fine-site realization $\widehat Y_{\mathcal C}$ contains the relevant sites of $Y_{\mathcal C}$, the source tree $\Gamma_0$, and every hole component met by the connection. Each effective $P\in\mathcal C$ must have a recorded attachment: its own cell in the charged support if outside $S_0$, an exterior charged proxy with a proved bounded multiplicity if inside $S_0$, or an explicit parameter decoration retained in the output index. The charged support $\operatorname{holeSupp}(P_{\mathcal C})$ must be nonempty. Completion must add no uncharged output cover cell silently.
2. A layerwise family $\mathcal K_{\widehat Y}$ satisfying `ChosenFamily F♯ m₀ \widehat Y 𝒦` wherever `treeLenCov` is used, or an explicitly defined modular analogue on $\widehat Y\bmod(\Omega_{\rm out})^c$; and a connected physical tree $\Gamma_{\mathcal C}\subset\widehat Y_{\mathcal C}$ meeting it. Every hole path in that tree is counted at its physical bond weight.
3. A **uniform** constant $C_{\rm graph}(d,L)$ and the bound
   $$\operatorname{cost}_{F^\sharp}(\Gamma_{\mathcal C})
      \le L^{-1}\Delta+C_{\rm graph}(d,L)|\mathcal C|.\tag{4.1}$$
   The local ambient term (2.3) is explicit. No uniform bound for the admissible hole completion and chosen-family connectors has been proved, so assigning a numerical value to the *total* $C_{\rm graph}$ would be unjustified.
4. A Steiner bridge for the **infimum** $D_{\mathcal C}=\widetilde d^{\rm cov}_{F^\sharp}(\widehat Y_{\mathcal C})$, with explicit $a_{\rm St}>0$ and $b_{\rm St}\ge0$ independent of volume and history,
   $$D_{\mathcal C}\ge a_{\rm St}\operatorname{steiner}_{H_B}
            (\operatorname{holeSupp}P_{\mathcal C})-b_{\rm St},\tag{4.2}$$
   or an activity estimate directly in the latter size. A lower bound for the cost of just one selected tree does not imply (4.2). Parameter labels inside $S_0$ are invisible to `holeSupp`, so their multiplicity must be paid separately before (4.2) can be used for an undecorated `pe_hole` activity.
5. For each fixed output charged support (and each fixed source), a graph-fiber estimate
   $$\sum_{\mathcal C:\,\operatorname{holeSupp}P_{\mathcal C}=Q}
           e^{-\kappa_2|\mathcal C|}\le1,\tag{4.3}$$
   under explicit graph-counting hypotheses. Landed `gm3` gives (4.3) with the numerical threshold (1.2) **only if** one proves that these families inject into its connected `Pset` families with the same `Ysites` output and disjointness premises. Those assertions are not consequences of `isIncUnion_seed`; a new block-fiber count may need a different constant. There is no justified total graph entropy constant yet.

The numerical algebra **is proved conditional on (4.1)**. Let $D=\widetilde d^{\rm cov}_{F^\sharp}(\widehat Y_{\mathcal C})\le\operatorname{cost}_{F^\sharp}(\Gamma_{\mathcal C})$ when the chosen family and tree in item 2 are admissible. If
$$L\ge3,\qquad \kappa\ge3\kappa_0+3,\qquad
\kappa_1\ge4C_{\rm graph}\kappa,\tag{4.4}$$
then
$$
(\kappa_1-1)|\mathcal C|+(\kappa-1)\Delta
\ge(\kappa_1/2-1)|\mathcal C|+\kappa_0\Delta+2\kappa D.\tag{4.5}
$$
Indeed, subtract the right side and use $D\le L^{-1}\Delta+C_{\rm graph}|\mathcal C|$. The remaining coefficients are $\kappa_1/2-2\kappa C_{\rm graph}\ge0$ and $\kappa-1-\kappa_0-2\kappa/L\ge\kappa/3-1-\kappa_0\ge0$. This is the same arithmetic as landed `gm4`, with its proved $C_{\rm graph}=d(2L+1)^d$ **only for its own `Ysites` construction**.

For the ordinary nearest-neighbor $\pi_K$ block graph one may take the explicit degree bound $\Delta_B=2d$. If an activity bound $\|K(P)\|\le\varepsilon\exp[-\kappa_h\operatorname{steiner}_{H_B}(\operatorname{holeSupp}P)]$ has been established, landed `pe_hole` applies when $\kappa_h'\ge0$, $\varepsilon\ge0$, and
$$q=(2d)^2,2^{,2d+1}e^{-(\kappa_h-\kappa_h'-\alpha)}<1,
\qquad
\frac{\varepsilon,2^{,2d+1}e^{-(\kappa_h-\kappa_h'-\alpha)}}{1-q}\le\alpha.\tag{4.6}$$
If a fine-size activity is bounded by $E e^{-\lambda D}$ and (4.2) holds for the **output size itself**, then $\varepsilon=E e^{\lambda b_{\rm St}}$, $\kappa_h=\lambda a_{\rm St}$ meet its activity premise. This requires a lower comparison for every admissible chosen-family tree, or directly for $D$; one selected tree is insufficient.

## 5. Exact mixed-wall NC3 target and landed progress

Let `S : Dec2.CoverGeom C H a ν Cx` be a proved common-cover geometry instance. The analytic assertion **OPEN-NC3-MIXED-WALL** is that there exist $K_c(d,L),K_h(d,L)\ge0$ such that, for every admissible P6 history, every such $H\in\{H^-,H^\partial\}$, every $\alpha$ with `AdmPot H α`, and every $q\in C.\mathrm{cubeIdx}$,
$$\operatorname{CubeBlockBounds}(H,a,\nu,\alpha,q,K_c),
\qquad
\operatorname{CubeBlockHolder}(H,a,\nu,\alpha,q,K_h).\tag{5.1}$$
The two structures in `DecoupledCube.lean` and `DecoupledCubeHolder.lean` fix all source-block, value, forward-gradient, symmetric-Laplacian, two-center Hölder, path-decay, and pointwise-domain quantifiers. In particular, `CubeBlockBounds.bounds` asks for its **value at every operator site of `intBox q`**, including sites next to the artificial Neumann cut; an estimate only on `supp χ_q` does not instantiate this landed field. The constants in (5.1) must be independent of $K$, $m_0$, $m_1$, the torus, history, wall shape, $q$, $a$, $\nu$, and $\alpha$, within `OpSetting`/`AdmPot`.

At boxes with `FoldSetting H q s c`, the landed `NC3.lean` pointwise, value, Laplacian, and Hölder theorems apply with the fold constants of `VMOD-5.md` (1.3) and `DecoupledCubeHolder.lean cubeBlockHolder_exists`, subject to the LFR-to-fold and scale-one bridges. At a physical internal wall, `FoldSetting.mem_Ω` or `collar` can fail. `ReflectionOperator.lean operator_intertwine` treats the **artificial Neumann face** of the cube; it does not turn a physical Dirichlet face into a Neumann one. Reflecting the physical hole while retaining a generating set and its separation conditions, especially at cut-wall corners, is a new assertion. No wall constant follows from the fold constants.

The landed `Multiscale/CutPointwise.lean cutOperator_eq_local` and `laplacian_eq_of_cut` do prove the uncut row and Poisson equation at a point satisfying `NoCutAt` for the artificial cut, even when that point is at the physical Dirichlet wall. `laplacian_bound_cut` supplies its local right-side bound. More specifically, landed `NC3.lean laplacian_cut_bound` proves that **if** the cut solution already has a blockwise value-decay bound with coefficient $V=K_V\ell_{j'}^2M_f$, then its symmetric-Laplacian bound at a `NoCutAt` point has coefficient $e^{\operatorname{agmonRate}(d)d}(1+4K_V)$. These are **proved conditional partial steps** toward a direct boundary estimate. They do not prove the needed blockwise value bound, the full cube-face and forward-gradient bounds, or the two-center Hölder estimate. The landed `cut_pointwise_crude` retains the extra $\ell_{j'}^{d/2}$ from the source $\ell^2$ norm. Thus neither (5.1) nor an explicit $K_c^{\rm wall},K_h^{\rm wall}$ is proved.

A valid direct proof would need a cut-parameter analogue of the landed pointwise and Hölder chain with the physical Dirichlet boundary retained, plus a boundary treatment at the artificial Neumann face sufficient for the **full** `CubeBlockBounds` and `CubeBlockHolder` statements. Its local row input is already landed as just cited. Alternatively, a Dirichlet-compatible reflected generating set and exact operator intertwining would have to retain the preimage of $\Omega_1(H)^c$ and prove separation at reflected corners. These are named **OPEN-CUT-POINTWISE-WALL** and **OPEN-DIRICHLET-REFLECTION**, respectively; either route would still need assembly into (5.1).

## 6. Dependency order and status

1. **Proved:** the corrected partition (`CoverPartition.lean`) and anchored selector (`Decoupled2FpCount.lean`), with the geometric LFR inclusions still supplied externally to the former. This note proves the ambient star bound (2.3), the site-projection entropy obstruction (3.1)–(3.2), and the conditional exponent arithmetic (4.5).
2. **Open geometry:** source-tree retention and modular hole completion; effective-charge support; parameter-cell inclusion in the charged block polymer; chosen-family construction; admissible weighted connectors; a lower Steiner bridge for the *infimum*; and a graph-fiber count. These are needed before `gm2_tree`, `gm3`, `gm4`, or `pe_hole` can yield the requested graph theorem. The total $C_{\rm graph}$, $a_{\rm St}$, $b_{\rm St}$ and graph entropy threshold are undetermined.
3. **Open analysis:** the uniform wall case (5.1). Landed reflection covers the fold regime; landed cut row lemmas cover local equations away from artificial cut bonds. Neither closes `Dec2.CoverBase.nc` at a mixed wall.

Confidence is high in the statements and proofs of §§1–3 and the conditional arithmetic of §4. The exact candidate counting theorem is specified in §4, but its geometric, entropy and Steiner hypotheses are open. A complete proof of the two requested assertions cannot be given from the cited landed results without proving those additional assertions; no numerical constant or citation is assigned to them here.
