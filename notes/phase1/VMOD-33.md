# Round 33: output domains determine the auxiliary cover

**13 October 2026.** Statuses refer to mathematical deductions unless a Lean declaration is named. The W249 files are a worktree branch, **not** declarations in the main landed tree. P3 printed pp. 78–81 and P6 printed p. 34 are the paper sources; P3 (4.44) and P6 (4.33)–(4.34) were checked against the PDF images in the preceding round. Write $K=k+1$, $F^\sharp=\texttt{p6FsharpC}$, $G^-=\texttt{p6OldC}$, $G^\partial=\texttt{p6BoundaryC}$, and $F^{\rm top}=\texttt{topGS}$. The new pre-$R$ small-field region is $\Omega_K^{\rm pre}=\texttt{OmegaCube}\,\mathbb A.H\,K$, with $Z_K^{\rm pre}=\mathbb A.H.F.\texttt{Zpre}\,K$; the post-$R$ region is $\Omega_K^{\rm post}=\mathbb A.H.\texttt{omegaPost}\,K$, with $Z_K=(\mathbb A.H.\texttt{step}\,K).Z$.

## 1. The required output, with its two histories

**PROVED from the W249 branch definitions.** For $\mathrm{Fr}:\texttt{FineSizeFrame}$, the precise pre-$R$ boundary label is
$$
Y\in\texttt{bdryDomsPre}\ \mathrm{Fr}\ \mathbb A\ K\ Z_K^{\rm pre}
\ \Longleftrightarrow\
Y\in\texttt{bdryDoms}(\Omega_K^{\rm pre})Z_K^{\rm pre}
\ \wedge\
\texttt{DjMod}\ m_0\ K\ (\texttt{d7Pull}\,\mathrm{Fr}\,K\,\Omega_K^{\rm pre})
(\texttt{d7Pull}\,\mathrm{Fr}\,K\,Y).
\tag{1.1}
$$
Here the last clause implies the finite-size clause of $\texttt{FineValidPre}$, by `fineValidPre_of_djMod` (`W249/Def7FineSize.lean:524`); `bdryDomsPre` itself filters `bdryDoms` by `FineValidPre` (`W249/Def7FineSize.lean:314–350,450–489`). In particular $Y_f$ is a nonempty connected union of aligned $\pi'_K$-boxes and contains or misses **each whole nearest-neighbour component** of $(\Omega_K^{\rm pre})_f^c$ (`SizeModDefs.lean:49–99`). A boundary term must also meet $Z_K^{\rm pre}$ and its complement at cube level (`Def7Hist.lean:285–299`). The pre-$R$ bound is measured by
$$
\texttt{d7SizePre}\,\mathrm{Fr}\,\mathbb A\,K\,Y
=\bigl(\texttt{dcovModE}\ m_0\ K\ (\texttt{d7Pull}\,\mathrm{Fr}\,K\,\Omega_K^{\rm pre})\,Y_f\bigr).\texttt{toReal}.
\tag{1.2}
$$
After $R$, replace $\Omega_K^{\rm pre},Z_K^{\rm pre},\texttt{FineValidPre},\texttt{bdryDomsPre},\texttt{d7SizePre}$ by $\Omega_K^{\rm post},Z_K,\texttt{FineValid},\texttt{bdryDomsPost},\texttt{d7Size}$ (`Def7FineSize.lean:424–489`). The branch proves pre-valid $\Rightarrow$ post-valid for the **same $Z$** and $\texttt{d7SizePre}\le\texttt{d7Size}$ when finite; it does **not** derive the stronger post-$R$ decay from a pre-$R$ bound (`W249/Def7FineSize.lean:525–575`). A term crossing only the pre-$R$ $Z$ need not be a post-$R$ boundary term.

**PROVED source check; OPEN as a P6-to-D7 implementation.** P3 (4.44), printed p. 78, defines the physical output by the short formula $Y=X_1\cup\bigcup_{i=1}^{n}Y^{(i)}$: each $Y^{(i)}$ is made of $\pi_j$-cubes **in its physical layer**. P6 (4.33), printed p. 34, writes the old boundary contribution as $\sum_{Y\in\mathcal D_K(\mathrm{mod}\,\Omega_K^c)}B''^{(k)}(Y,\mathbb A_k;\psi)$; (4.34) gives $\lvert B''^{(k)}(Y,\mathbb A_k;\psi)\rvert<\beta_k^{-3/2}\exp[-(2\kappa-1)d_K(Y\mathrm{\ mod\ }\Omega_K^c)]$. Its preceding paragraph says $X\subset Y$, with $X$ old and $Y$ new, and that terms are analytic on appropriate H7 spaces. In Lean, containment means $\texttt{d7Pull}\,\mathrm{Fr}\,k\,X\subseteq Y_f$ after the explicit torus cast. P6 (4.33) by itself requires $\texttt{DjMod}$ for **every** term; $\texttt{bdryDomsPre}$ additionally applies to the terms selected as boundary terms that cross $Z_K^{\rm pre}$. Other terms need their corresponding small-field/large-field class, not an invented boundary label. The branch's `D7Bdry.analytic/bound/support` (`W249/Def7.lean:418–442`) require the localized `H7Domain` on the fine set of $Y$, $\texttt{globalLH}\,\mathbb A.H$, and external $h\in\texttt{hSetB}$; invalid fine labels must have zero boundary coefficient.

**PROVED source constants, conditional on the paper's chosen-cover realization.** P3 (4.48) charges a marked set $\mathcal C$ by $\widetilde d_K(Y)\le L^{-1}d_k(X)+d(2L+1)^d|\mathcal C|$; P6 p. 34 states the same inequality with both sizes modulo the old/new complements. P3 (4.49) spends the Cauchy decay to pay $2\kappa\widetilde d_K(Y)+\kappa_0d_k(X)+\kappa_2|\mathcal C|$, where $\kappa_2=\kappa_1/2-1$ and $\kappa_1\ge4d(2L+1)^d\kappa$. P3 (4.50) is the **weighted fiber** estimate $\sum_{Y_1:\,Y_1\mapsto Y}e^{-\kappa_2|\mathcal C(Y_1)|}\le1$, not a bounded unweighted multiplicity. P6's subsequent sum over $X\subset Y$ costs at most $K_0(3L^2)^d\exp[d_K(Y\mathrm{\ mod\ }\Omega_K^c)]$, producing $2\kappa-1$. In the present convention the required replacement is $\texttt{OPEN-P6-MOD-GM2-FINE}$:
$$
\texttt{d7SizePre}(\mathbb A,K,Y)\le L^{-1}\texttt{d7Size}(\mathbb A,k,X)+d(2L+1)^d|\mathcal C|,
\tag{1.3}
$$
plus the corresponding physical-label, H7, and weighted-fiber assertions. **OPEN:** neither P3's original all-cover functional nor P6's assertion is a landed theorem about the W249 fine chosen-cover size; `LOCALIZATION.md` §4.0 adapts P3’s tree argument to the fine chosen-cover convention in the nonmodular case, while `OPEN-PAPER-FINE-REALIZATION` remains.

## 2. Three covers

### A. Full-torus top cover and completion

**PROVED domain repair, conditional on a precise closure algorithm.** Start with the raw top-cover $\pi'_K$-union $Y_0$, insert the fine lift $X_f$, insert every component of $(\Omega_K^{\rm pre})_f^c$ met by the result, then cover each newly added site by a chosen aligned $\pi'_K$-box containing it and add that box; iterate hole completion and box selection until neither adds a site, obtaining $Y^\dagger$. Finiteness of the torus makes the process terminate. Every selected box meets the current set at the site it covers; every inserted hole component already meets the current set. Thus connectedness is retained, and the fixed point is a $\pi'_K$-union that contains or misses each hole component. Thus $\texttt{DjMod}\,m_0\,K\,\Omega_f\,Y^\dagger$ follows when the seed is nonempty and connected. A **single** hole-completion pass is insufficient: the $\pi'_K$-box closure can touch another hole. This argument alone gives neither the cube-level $Z$-crossing clause nor a local generating set.

**REFUTED for the abstract domain axioms: a uniform completion-size estimate.** Let one component of $\Omega_f^c$ be a connected corridor one $\pi_K$-cell wide that crosses $n$ aligned $\pi'_K$-boxes in a straight row; let $Y_0$ be a bounded number of $\pi'_K$-boxes at its first end. Completing that component and covering it by $\pi'_K$-boxes forces active sites outside the thin corridor at positions spanning the same $n$-box distance. Any connected chosen-cover structure meeting the active boxes at the first and last ends has normalized length at least $L(n-2)$ up to fixed endpoint terms; overlapping choices of $\pi'_K$-boxes do not change this distance lower bound. Yet $d_K^{\rm cov}(Y_0\mathrm{\ mod\ }\Omega_f^c)=O(1)$, and $Y_0$ can arise from $O(1)$ top patches. Hence no $d_K^{\rm cov}(Y^\dagger)\le a\,d_K^{\rm cov}(Y_0)+b|\mathcal C|+b$ with $a,b$ independent of the hole length follows from `DjMod`/`FineValidAt`. Whether physical admissible histories exclude this corridor is **OPEN-P6-HOLE-SHAPE-CHARGE**; no such bound is in `Def7FineSize`. Even for a hole that is itself a $\pi'_K$-union, adding it is free only if it introduces no new active $\pi'_K$-boxes. P6 (4.34) is a pointwise term bound before any sum over new large-field factors; charging a large hole to a later factor would be a different theorem, **OPEN-P6-LF-COMPENSATION**.

**OPEN multiplicity and H7 transport.** The completion map forgets arbitrary raw patch decorations inside an absorbed hole; its fibers have no uniform unweighted cardinality bound. One could sum them with the rooted-animal weight, but this requires the actual coefficient-rooting lemma and does not repair the size counterexample. Enlarging $Y_0$ also changes $\mathbb B_K(Y)$: restriction of the larger H7 domain to the old reads and equality of the localized composite on those reads are `OPEN-P6-TOP-H7-RESTRICT` and `OPEN-P6-TOP-GENSET-AGREE`. The landed `P6TopCover`, `P6TopPair`, and `P6TopRootedFiber` prove neither. **Verdict A: REFUTED as an unconditional $k$-uniform route; OPEN under new restricted-history and H7 assertions.**

### B. Multiscale outside a hole, top-only inside

**PROVED exact separation tests; generic legality REFUTED.** For a fixed $K$-block union $H$ of hole sites, the natural top-inside construction is $\Omega_j^{\rm mix}=\Omega_j^\sharp\cup H$ for every $1\le j\le K$. It is nested and block aligned. Its `SupSep` at $j<K$ is equivalent, in addition to the old `SupSep`, to
$$
x\notin\Omega_j^\sharp\cup H,\ y\in H
\quad\Longrightarrow\quad
\operatorname{supDist}(x,y)>4L^{j+1+m_1}.
\tag{2.1}
$$
The `GeneratingSet.separation` field also requires $\operatorname{torusDist}(x,y)>\varrho_F L^j$ for the same $x,y$; both are **new collar conditions**, not implied by the old fields of $F^\sharp$. For a proper $H$ in an area where $\Omega_j^\sharp$ has no collar, adjacent $x\notin\Omega_j^\sharp\cup H$, $y\in H$ refute it. Adding a collar at all levels may make a legal set but changes the indices near the interface. In the flat-wall model $H=Z_k$, the old $\Omega_j^\sharp$ contain $Z_k^c$ and the top halo contains $Z_k^c$, so the union is the full-torus top cover; this special legal case inherits A's output problem.

**PROVED obstruction for the opposite operation.** If $\Omega_j^{\rm mix}=\Omega_j^\sharp\setminus H$ at every level, nesting and block union can survive but a site in $H$ adjacent to $\Omega_{j+1}^\sharp\setminus H$ violates separation unless another collar is removed. It gives no top patches **inside** $H$, and can destroy $\texttt{Precedes}\,G^\pm\,F^{\rm mix}$ where an operator is active in $H$. Keeping $H$ at the top while removing it from lower $\Omega_j$ breaks nestedness for nonempty $H$ and $K\ge2$. Even if (2.1), the ordinary separation collar, and pair geometry were proved for a collar-adjusted union, top patches over $H$ are not indices in the physical new layer; P3 (4.44) applies literally only to untouched patches away from the interface. Root incidence at hole-side top cells also requires their **whole Moore neighborhood** in $\Omega_K^{\rm mix}$; otherwise `root_patch_count` does not apply and the flat-wall low-layer incidence can recur. **Verdict B: OPEN as a specially engineered cover, and no improvement on the physical output obligation.**

### C. The P6 multiscale cover and active roots

**PROVED landed geometry.** Use $F^\sharp$ for the two operators: `p6_coverBase_old/boundary` and `p6_footLocal_old/boundary` (`P6PairBase.lean`) instantiate the common-cover DG interface. For every top cell whose representative satisfies the landed `fineK1 ... st.Omega` hypothesis, `p6_active_top_halo` and `p6_root_patch_count` (`P6ActiveHalo.lean:276,340`) give at most $b_r=3^d(L^{m_0})^d$ incident $F^\sharp$ patches, including the $L^{m_0}\mid c$ premise. Under $d<5L^3M_1$, `mooreGraph_degree_le` (`MooreDegree.lean:271`) gives patch degree $b_g=3(L+4)^d$, while `cubeIdx_moore_layer_gap_p6` (`MooreDegree.lean:300`) makes adjacent patch layers differ by at most one; `p6_touch_active_layer` (`P6ActiveHalo.lean:328`) makes each active root a layer-$K$ patch. Applying these statements to $A_X$ requires its cast into `fineK1 ... st.Omega` (`OPEN-P6-ACTIVE-REGION-CAST`). These are independent of $k$.

**PROVED CONDITIONAL ON `OPEN-P6-ACTIVE-COEF-ROOT` and `OPEN-P6-ACTIVE-REGION-CAST`.** Let $A_X$ be the active top cells in the localized read set $X\cap\Omega_K$. Suppose every connected component of a nonzero coefficient's marked $F^\sharp$-patch set $\mathcal C$ contains a patch Moore-touching $A_X$, with **no independent roots in the old hole-side source cover**. Put
$$
D_*=\max\{b_g+1,b_r\},\quad t=e^{-\kappa_2},\quad
z=D_*^2t<1,\quad h=-\log(1-z).
\tag{2.2}
$$
`Polymer.card_rooted_le` and `sum_rooted_le` (`RootedAnimals.lean:257,303`) give $\sum_{\mathcal C\ {\rm rooted\ at}\ A_X}t^{|\mathcal C|}\le(1-z)^{-|A_X|}$. If $|A_X|\le c_A(1+\Delta_X)$, $c_A=L^d[3(2L-1)]^d$, $\Delta_X=\texttt{d7Size}\,\mathrm{Fr}\,\mathbb A\,k\,X$, then the fixed-support sum is $\le H e^{q\Delta_X}$, $H=e^{hc_A}$, $q=hc_A$. The fine-size identity in W249 `d7Size_eq` (`Def7FineSize.lean:474`) removes the *definition mismatch* of VMOD-25 once that branch is landed; `OPEN-P6-REGION-CAST` still identifies its post-$R$ region with the P6 source region and `OPEN-P6-ACTIVE-SIZE-COUNT` supplies the active count. The estimate does not require one source-cover root per old-hole cell.

**PROVED chain payment, conditional on `OPEN-P6-ACTIVE-COEF-ROOT` and `OPEN-P6-ACTIVE-REGION-CAST`; REFUTED for source-only rooting.** A connected marked animal with an active top root at layer $K$ and a patch at layer $j$ has at least $K-j+1$ vertices, by the landed layer-gap lemma. For one root cell the weighted tail is
$$
\sum_{\substack{\mathcal C\ {\rm connected,\ rooted}\\
\exists P\in\mathcal C,\ P.1=j}}e^{-\kappa_2|\mathcal C|}
\ \le\ \sum_{n\ge K-j+1}D_*^{2n}e^{-\kappa_2n}
\ =\ \frac{z^{K-j+1}}{1-z}.
\tag{2.3}
$$
Thus the $L^{(K-j)(d-1)}$ possible face positions are already counted by the animal bound. If one counted only those positions and assumed one chain of length $K-j$ per position, $\kappa_2>(d-1)\log L$ would suppress that **single family**; it does not pay all possible chains and decorations. The landed sufficient condition is $\kappa_2>2\log D_*$, equivalent to $z<1$, and it is available only after choosing $\kappa_1$ and then $M_1$ to meet $M_1\ge c_*e^{N_0\kappa_1}$; the old D7 H7 clause alone supplies no parameter polydisc. If a flat-wall layer-1 singleton can be rooted solely at $B$, there is **no chain payment**: VMOD-26 (4.1a) gives at least $L^{k(d-2)}e^{-\kappa_2}$ in the abstract ledger at $\Delta_X=0$. Hence a mere change in counting cannot rescue $B$-rooting; the physical read-split is decisive.

**OPEN physical producer.** P6 p. 34 says to localize the old term first on $X\cap\Omega_K$, while keeping explicit old $A_k$-spins on $X\cap\Omega_K^c$ and $h,g$ on $X$. To infer active-only rooting one must prove that all **parameter-dependent** reads of the composed old field, including the mixed covariance square root, lie in the active seed or its controlled row dependency set; the old exterior spins must be $s$-independent. `D7Bdry.loc_field` in W249 says only that both field inputs and $g$ are read on full $X$ (`W249/Def7.lean:389`). `PairedLocalAgree.paired_locality` (`PairedLocalAgree.lean:299`) assumes its affine read sites are in the seed, and has no P6 mixed square root. Neither P6's sentence nor these declarations proves `OPEN-P6-ACTIVE-COEF-ROOT`. Under that assertion the far hole patch contributes only with a chain reaching $A_X$; without it, nonzero singleton coefficients remain possible and the abstract flat-wall divergence applies.

## 3. Verdict and conditional theorem

**RECOMMENDATION C: build with $F^\sharp$.** It is the cover for which P6 explicitly invokes the P3 physical-layer assignment, retains the landed two-operator estimates, and has uniform active-root degree and incidence. **OPEN-P6-FSHARP-PHYSICAL-ASSIGNMENT** is the Lean theorem realizing the P6 sentence for the actual auxiliary $F^\sharp$: every marked patch is assigned to boundedly many physical new-layer $\pi_j$-cubes, with $Y_f\in\texttt{DjMod}$, $X_f\subseteq Y_f$, and a localized generating set agreeing on the read support. The paper supplies the model, but $\texttt{Precedes}\,G^\partial F^\sharp$ alone does not prove it. Boundary-labelled pieces must additionally pass the $Z_K^{\rm pre}$-crossing test of (1.1); post-$R$ decay is a separate $R$-step obligation.

**PROVED CONDITIONAL ON named OPEN inputs.** Assume `OPEN-P6-ACTIVE-COEF-ROOT`, `OPEN-P6-MIXED-H7-FSHARP` (joint analyticity and a bound $\beta_k^{-2}e^{-(\kappa-1)\Delta_X}$ on one strict parameter polydisc), `OPEN-P6-ACTIVE-SIZE-COUNT`, `OPEN-P6-ACTIVE-REGION-CAST`, `OPEN-P6-REGION-CAST`, `OPEN-P6-FSHARP-PHYSICAL-ASSIGNMENT`, `OPEN-P6-MOD-GM2-FINE` (1.3) and weighted (4.50), `OPEN-P6-H7-OUTPUT`, `OPEN-P6-D7-CLASSIFY`, and the P6 old-$X$ entropy sum. Choose $\kappa_2=\kappa_1/2-1$ with (2.2), and $q=hc_A\le\kappa_0-a_{\rm ent}(d,L)-1$. The Cauchy/GM2 arithmetic of VMOD-24 §4 then gives the fixed-$Y$ old-boundary term
$$
\|B''_{\rm old}(Y)\|_{H7(Y)}
\le \beta_k^{-2}Hc_AK_0(d,L,\kappa_0-q)\,
e^{-(2\kappa-1)\texttt{d7SizePre}(\mathbb A,K,Y)}.
\tag{3.1}
$$
If $\beta_k^{1/2}\ge Hc_AK_0$, this has P6 (4.34)'s $\beta_k^{-3/2}$ prefactor. The first two terms of P6 (4.32), representation preservation, and the $R$-step strengthening to $\texttt{d7Size}$ remain `OPEN-P6-PURE-TERMS`, `OPEN-P6-REP-PRESERVATION`, and `OPEN-R-SITE-NORM`; (3.1) is **not** a completed D7 theorem. The rate order is $\kappa_0,\kappa$, then $\kappa_1$ satisfying GM3 and $z,q$, then $M_1$ satisfying the exponential Dec2 threshold, then $\beta_k$. For a previously fixed $M_1$, that threshold caps $\kappa_1$; $z<1$ is not automatic.

**PROVED status of the top files.** `P6TopCover.lean` (`topGS`, `not_supSep_of_proper`), `P6TopPair.lean` (old/boundary `FootLocal`), and `P6TopRootedFiber.lean` (`top_rooted_fixed_support_sum_le`) have landed in the main tree. They remain correct reusable results and useful comparison examples, but none is consumed by the $F^\sharp$ producer (3.1). The generic `Polymer.sum_rooted_le`, `MooreDegree`, `P6ActiveHalo`, and `P6PairBase` are consumed.

**Author question still needed: the physical coefficient support.**
> P6 p. 34 localizes the old boundary term first on $X\cap\Omega_{k+1}$, retaining explicit $A_k$-spins on $X\cap\Omega_{k+1}^c$.  
> After the local extension in (4.32), are these exterior spins and every other exterior read independent of the interpolation parameters $s_\square$?  
> In particular, can a marked $F^\sharp$ cube deep in a new hole contribute to a coefficient without a connected marked chain to $X\cap\Omega_{k+1}$?  
> Does the same answer hold for the $C_{{\rm loc},s}^{1/2}\psi$ term?  
> Which step of the P3 (4.44) assignment sends the auxiliary $F^\sharp$ cubes outside the physical new layers into $Y\in\mathcal D_{k+1}(\mathrm{mod}\,\Omega_{k+1}^c)$?

## 4. Lean packages, in dependency order

All sizes are estimates per module, each at most 300 lines. **START NOW, cover independent:** (1) `P6FootprintHat` (120–220), $\texttt{footprint}\subset\texttt{hatBox}$ from `Decoupled2FpGeometry.footprint_row`, `Cover.hatRad`, operator row support; (2) `P6FineSourceCast` (100–200), use W249 `FineSizeFrame`, `d7Pull`, `d7Size_eq` after branch landing, prove the exact old-post P6 source identification; (3) `P6PairedIncidence` (180–280), common-site two-operator graph and component projections from `Dec2.IsIncUnion.dichotomy` and `PairedLocalGraph.incUnion_of_geom`.

**START NOW for $F^\sharp$:** (4) `P6FsharpActiveRootCount` (80–160), instantiate `p6_root_patch_count`, `mooreGraph_degree_le`, `Polymer.sum_rooted_le` with $A_X$ and derive $H,q$; (5) `P6FsharpLayerTail` (90–160), `cubeIdx_moore_layer_gap_p6` plus `Polymer.card_rooted_le` to prove (2.3). These are counting statements, with no claim about P6 coefficients.

**WAIT for physical inputs:** (6) `P6ReadSplit` (180–290), explicit old $A_k$-spin / active-composite decomposition from P6 (4.32), W249 `D7Bdry.loc_field` and `RowsFl.DataAgreeRows`; source assertion `OPEN-P6-ACTIVE-READ-SPLIT`. (7) `P6MixedSqrtLocal`, three modules of 170–280 each for mixed resolvent, square-root locality, and H7 domain; no landed mixed selector. (8) `P6FsharpCoefRoot` (180–280), apply `PairedLocalAgree.paired_locality` and `I5Param.coef_eq_zero_of_not_connected_on` to package 6–7. (9) `P6FsharpAssign` (180–290), physical layer assignment and $X_f\subset Y_f$, then `P6ModGM2` (180–290), fine chosen-cover tree charge and weighted (4.50), then `P6LocalizedH7` (170–280), localized generating-set/domain transport. (10) `P6D7Output` (140–250), boundary classification through W249 `mem_bdryDomsPre` and `fineValidPre_of_djMod`; nonboundary terms routed separately. (11) `P6OldBdryBound` (160–260), combine packages 2, 4, 8–10 with `Fluctuation.G2_X` and old-$X$ entropy to get (3.1). The paper-to-fine comparison and the $R$-step remain separately OPEN.

**Confidence.** High: branch target types, P3/P6 output formulae, the abstract completion counterexample, mixed-cover legality test, and landed $F^\sharp$ graph constants. Medium: the exact physical $F^\sharp$-to-layer assignment implicit in P6. Low until an author answer or proof: the active-only coefficient support and mixed-square-root H7 locality.
