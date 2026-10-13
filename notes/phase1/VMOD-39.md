# Round 39: roots for the P6 pair

**13 October 2026.** Sources: P3, *Localization Expansions I*, printed pp. 77–81, (4.41)–(4.50) (formulas checked on the PDF); P6, *Renormalization and Localization Expansions II*, printed p. 34, (4.32)–(4.34); P5 H7, (1.38)–(1.39). Lean paths below are relative to `/home/scott/Balaban/Balaban/` and were read on current main. Put $K=k+1$, $F^\sharp=\texttt{p6FsharpC}$, $C=\texttt{coverOf}\,F^\sharp$, $H^-=\texttt{p6OldC}$, $H^\partial=\texttt{p6BoundaryC}$, and $A_X=X\cap\Omega_K$ (coarse active cells, cast to the common fine torus when used as a site set).

## 1. What is cut, and what is read

**PROVED source reading.** P3 (4.41) sums over the $M_1$-cubes of its cover **contained in $X_1^c$**; (4.42) sets $Y_1=X_1\cup\bigcup_{P\in J}P$. Thus $X_1$ is the *uncut initial localization core*, not the parameter region.
The landed `DecoupledGeometry.parCubes G X₁` is exactly `cubeIdx G` filtered by $\operatorname{cubeP}(P)\not\subseteq X_1$; `Decoupled2FpGeometry.EligC` charges only these parameter cubes. P3 assumes $X\subseteq X_1\subseteq\Omega_K$ for its original small-field term.
P6 p. 34 first regards the old boundary term as localized in $A_X$, then applies the same extension and permits several components, each later $Y_1$ containing at least one component of $A_X$. It does **not** specify an exact fine-site choice of $X_1$ for the present $F^\sharp$ implementation.
The natural choice is the fine lift of $A_X$, or a proved bounded collar of it; taking all of $\Omega_K$ would lose the required uniform count. Call the exact physical choice and its H7-domain validity `OPEN-P6-X1-INSTANTIATION`.

**PROVED read distinction.** The scalar in P6 (4.32) reads the substituted $\psi^{(k)}_{\rm loc,s}+\beta_k^{-1/2}C^{(k)1/2}_{\rm loc,s}\widehat\psi$ only at $A_X$; old exterior spins in $X\cap\Omega_K^c$ and fixed $h,g,\mathbb A_k$ are spectators (VMOD-34 §1, P5 (2.35),(2.39)).
Its *operator* rows and their data may reach outside $A_X$. `PairedLocalAgree.paired_locality` lines 299–369 proves equality for `E ∘ pairedRaw` assuming every `composeDep Gx H^\partial/H^- x` for **all** `x ∈ dataSites Gx` lies in $X_1\subseteq Y_f(J)$. The proof uses `hXY` only to put these dependency sites, and then `dataSites Gx`, in $Y_f(J)$.
A sharper theorem needs merely $\bigcup_{x\in R_E}\operatorname{composeDep}(G_x,H^\partial,x)\cup\operatorname{composeDep}(G_x,H^-,x)\subseteq Y_f(J)$ for the actual output read set $R_E\subseteq A_X$, plus spectator agreement; it must restrict the output equality to $R_E$.
It does not follow just by changing the seed of `P6PairGraph.paired_graph_hyps`, whose present seed is all of $X_1$. The physical dependency assertion and the mixed square-root analogue remain `OPEN-P6-ACTIVE-COMPOSITE-LOC`.

## 2. Free centres and the chain that is needed

**PROVED from definitions, conditional on the PROVED pair cover geometry.** Parameter-free eligible live centres do exist whenever a cover centre has $\mathcal Q(z)\subseteq\{P:\operatorname{cubeP}(P)\subseteq X_1\}$ (for example a central top-layer centre when an allowed boundary polymer extends several top cells into $\Omega_K$). They are the *undecoupled rows inside $X_1$*.
For a footprint site $t$, the common cover supplies a patch $P$ containing $t$; `FootprintHat.mem_Qset_of_mem_footprint` puts $P\in\mathcal Q(z)$. If $z$ has no parameter cube in $\mathcal Q(z)$, then $\operatorname{cubeP}(P)\subseteq X_1$, hence $t\in X_1$. Apply `p6_coverGeom_old/boundary` for this implication.
Thus an unmarked free centre cannot carry a footprint path through a long hole **outside** $X_1$.
Free paths can cross the whole connected portion of $X_1$, however; if $X_1$ is chosen huge, the closure has no useful active-root count. No exponential-decay payment per free step is required for a core whose cell count is already paid by the old-size budget. P3 (4.42) treats precisely this core as the starting domain.

**REFUTED:** `P6PairGraph.jointParams_hatRooted` by itself gives a Moore-rooted family. Its `PairHatRooted` uses `ReflTransGen HatLink` through all centres, and two parameter patches in one $\mathcal Q(z)$ may be separated.
The landed `paired_graph_hyps` supplies incidence unions, not coefficient support. `P6FsharpRootedCount.fsharp_rooted_sum_le` and `P6ActiveSeed.d7ActiveSeed_rooted_sum_le` count Moore animals and cannot consume this hat chain. The zero-parameter case already shows why an unrestricted hat path is insufficient.

**PROVED combinatorial mechanism under the stated local-core premise; OPEN physical coefficient premise.** Let $J\subseteq\texttt{parCubes}\,C\,X_1\subseteq\texttt{cubeIdx}\,F^\sharp$ be marked and activate a live centre $z$ iff $\mathcal Q(z)\cap\texttt{parCubes}\,C\,X_1\subseteq J$ (`EligC`).
Start the joint incidence closure at the *actual output read sites* $A_X$, across both operators. Delete excursions of eligible centres whose parameter footprint is empty: by the preceding fact these remain in $X_1$.
At a first exit from $X_1$ through an eligible centre, a cover patch containing the exit site lies in $J$; at a site-adjacency crossing, the two containing patches Moore-touch. Consecutive charged patches within one centre lie together in $\mathcal Q(z)$.
This gives a forest of marked patches whose components each begin next to a patch meeting $X_1$. If $X_1=A_X$ (fine lift), their roots are near active cells. For a collar, its free components and cell count must be bounded in terms of $A_X$.
A nonzero coefficient has this forest property **only if** the actual P6 scalar is local to that closure, including $H^-$ covariance square-root rows; this is `OPEN-P6-ACTIVE-COMPOSITE-LOC`. The in-progress `P6PairChain` may formalize the incidence-chain part, but is not a landed citation.

## 3. Correct graph and count

**PROVED geometry with a short Lean transport OPEN.** Use the graph $G_\sharp$ on `cubeIdx F♯` in which distinct patches are adjacent if they Moore-touch **or** both lie in $\mathcal Q(z)$ for some cover centre $z$. This is `Fluctuation.DetCauchyGraph.paramGraph`'s adjacency with $G=F^\sharp$, not `MooreDegree.mooreGraph`. Assume the P6 pair geometry, $M_1=L^{m_1}\ge4L^2$, $n_0=Ln_1$, $d<5L^3M_1$, and for the active-cell count $L^{m_0}\mid c$. Under `CubeAligned F♯` and `SupSep F♯`, `P6PairCover.Qset_layer_sup` and `card_Qset_le_sup` give at most three neighbouring layers and $N_0=3(8L)^d$ patches per footprint. The aligned-grid count of `DetCauchyGraph.card_mult_layer_le` gives at most $(L+9)^d$ centres per layer containing a fixed patch in their footprint; the Moore degree is at most $3(L+4)^d`. Thus
$$\deg G_\sharp\le D=3(L+4)^d+3(L+9)^dN_0=3(L+4)^d+9(L+9)^d(8L)^d.\tag{1}$$

The two operators use the **same** $C$ and $\mathcal Q$, so no factor two enters (1). `DetCauchyGraph.paramGraph_degree_le` itself assumes a stronger numerical separation than the landed P6 `SupSep`; use its counting proof with `Qset_layer_sup`, rather than citing that theorem as an instance.
The F♯ degree theorem remains OPEN in Lean.

**PROVED CONDITIONAL ON `OPEN-P6-X1-INSTANTIATION` and active-root chain.** For each active cell $u$, `P6ActiveHalo.p6_root_patch_count` bounds the cover patches meeting it by $b_0=3^d(L^{m_0})^d$.
A first charged patch is either one of these or one $G_\sharp$ edge away; its root neighbourhood has at most $b=(D+1)b_0$ patches. If a collar has at most $c_{\rm core}$ core cells per active cell and all free core components touch those cells, replace $b$ by $c_{\rm core}(D+1)b_0$.
The exact support theorem is: for every $J\subseteq\texttt{parCubes}\,C\,X_1$ with nonzero mixed coefficient $a_J$ of the physical P6 scalar, every connected component of $G_\sharp[J]$ meets $\bigcup_{u\in A_X}N_u$, where $N_u$ is this closed graph neighbourhood. This is **OPEN** for the physical scalar. Mere `PairHatRooted` does not imply it.

**PROVED conditional count.** Put $D_*=\max(D+1,b)$ and $z=D_*^2e^{-\kappa_2}$. If $z<1$, `Polymer.RootedAnimals.sum_rooted_le` gives
$$\sum_{J:\,a_J\ne0}e^{-\kappa_2|J|}\le (1-z)^{-|A_X|},\qquad \kappa_2>2\log D_*.\tag{2}$$
For $d=L=3$, (1) is $D=214{,}991{,}877$ and $2\log D\approx38.38$; the per-cell root factor raises the sufficient threshold in (2). The landed single-cover `DetCauchyActivity.sum_norm_mixDiff_le` already requires $e^\kappa>2(\texttt{detDeg}+1)^2$, or $\kappa>\log2+2\log(D+1)\approx39.07$ at these values. With $|A_X|\le c_A(1+d7Size(X))$, (2) costs $q=c_A[-\log(1-z)]$ of the old-size rate.
The extra fixed-support charge is small by taking $\kappa_2$ larger. P3 (4.49)–(4.50), pp. 80–81, sets $\kappa_2=\kappa_1/2-1$ and already requires $\kappa_1\ge4d(2L+1)^d\kappa$; for $d=L=3$ this is $4116\kappa$. Its order of choosing $\kappa_1$, then sufficiently large $m_1$ for the radius $e^{\kappa_1}$, permits the added threshold. A previously fixed $m_1$ need not.
P3 uses $M_1$-patches whose footprints contain several patches; neither (4.44) nor (4.50) avoids this incidence cost by making footprints singleton. Enlarging parameter patches would change `parCubes`, `Qset`, `sProd`, the interpolation and the physical assignment, with no source justification.

## 4. Consequences and author question

**OPEN remains open.** VMOD-34's active composite locality needs the restricted-read theorem, the physical $X_1$ choice, selectors, and mixed covariance square root; the pair graph supplies only geometry. VMOD-35/36's uncharged modular hole-size assignment is untouched: incidence rooting pays combinatorial families, not the chosen-cover cost of completing an inherited hole. The P3 (4.48)–(4.50) estimates invoked by P6, and P6 (4.34), still require `OPEN-P6-MOD-GM2-FINE`, the weighted physical fiber, H7 transport, and the old-$X$ entropy sum. No post-$R$ bound follows from (2).

**Revised item 14(ii)** (replace its current sentence): “With $X_1$ chosen as the active localization core in P6 (4.32), can any marked auxiliary $F^\sharp$ patch outside it have a nonzero coefficient unless its component in the graph generated by Moore touching **and common membership in a footprint** reaches the closed graph neighbourhood of $X\cap\Omega_{k+1}$? Does this hold for both operator rows and the covariance square root?” Items 14(i), (iii), and (iv) need no wording change. This is a proposed wording in this scratch note; `QUESTIONS-ROLAND-2.md` remains read-only.

## 5. Lean packages, in dependency order

Each package is at most 300 lines. **START, pure geometry:** (1) `P6FreeCore` (100–170): for `C=coverOf F♯`, $H=H^-$ or $H^\partial$, prove $\operatorname{EligC}(C,X_1,\varnothing,z)\land\operatorname{LiveI}(H,z)\Rightarrow\operatorname{footprint}(H,z)\subseteq X_1$ using `FootprintHat.mem_Qset_of_mem_footprint` and pair `CoverGeom`; also prove the conditional version when $\mathcal Q(z)\cap\texttt{parCubes}\,C\,X_1=\varnothing$. (2) `P6PairParamDegree` (170–260): define $G_\sharp$ as above and prove $\forall P,\deg_{G_\sharp}P\le D$ via `Qset_layer_sup`, `card_Qset_le_sup`, `card_mult_layer_le`, and `mooreGraph_degree_le`. (3) `P6PairRootNbhd` (110–190): for active $u$, prove $|N_u|\le(D+1)3^d(L^{m_0})^d$ from `p6_root_patch_count` and package 2.

**START with explicit geometric premises:** (4) `P6PairMarkedChain` (210–300): for `JointIn C H^∂ H^- a ν X₁ J ↑A_X`, prove that if every reached $P\in J$ is covered by its chain and free-site components lie in the chosen local core, then every component of $G_\sharp[J]$ reached by the closure meets $\bigcup_{u\in A_X}N_u$; reuse `P6PairGraph.isIncUnion_joint_b/m`, `jointSites_detach`, and packages 1–3. The physical coefficient-to-reached premise is separate. (5) `P6PairedReadLocality` (190–290): restrict `PairedLocalAgree.paired_locality` to an output read set $R_E$, replacing `hXY`/`hdepb`/`hdepm` by the exact `composeDep`-in-$Y_f(J)$ premises; preserve all selector, domain, and spectator hypotheses.

**WAIT for physical inputs:** (6) `P6PairCoefRoot` (180–270): under `OPEN-P6-X1-INSTANTIATION`, physical selector and mixed-square-root locality, show $a_J\ne0\Rightarrow J\in\texttt{rootedSets}\,G_\sharp\,(\bigcup_{u\in A_X}N_u)$ using `I5Param.coef_eq_zero_of_not_connected_on`, packages 4–5. (7) `P6PairRootedCount` (90–160): instantiate `RootedAnimals.sum_rooted_le` with $b=D$, $b_{root}=b$, $t=e^{-\kappa_2}$ to prove (2), then combine `P6ActiveSeed`'s active-cell/old-size inequality when its physical cast is supplied. These packages do not solve the separate modular hole-cost theorem.
