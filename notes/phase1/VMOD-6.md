# A common-cover partition and two remaining obstructions

**12 October 2026.** Follow-up to `VMOD-5.md`. The corrected reverse partition is proved below, conditional only on the stated, proved paper-level LFR geometry. A graph GM2 quantified over the **landed** `IsIncUnion` is false, even for a full-torus operator with no wall. The uniform mixed-wall NC3 estimate is not a consequence of the landed reflection theorems and remains **OPEN-NC3-MIXED-WALL**. Accordingly this note does not claim a complete modular I-5. All files under `/home/scott/Balaban` were read only.

Set $K=k+1$, $d,L\ge3$, and $M_1=L^{m_1}\ge4L^2$. Let $H^-=\mathbb B_k(W_k)$, with an empty top domain, and let $H^\partial=\mathbb B_{k+1}(\partial\Omega_{k+1})$ have exactly the domains of LF-RECONSTRUCTION.md Definition II.2.4(iv). Let $F^\sharp$ be the depth-$K$ generating set of `VMOD-2.md` (1.2): its lower domains are those of $H^-$, its top domain $A$ is the one-$\pi_K$-cell halo of the $\pi_K$ closure of $U$, and $A\subset W_k$. Write $C^\sharp=\operatorname{coverOf}F^\sharp$. This $H^\partial$ is the P6 **boundary** set; it is not a name for a global $\mathbb B_{k+1}(W_{k+1})$.

## 1. Correct replacement for the reverse partition

**Common-cover partition theorem (proved conditional on the proved LFR history inclusions).** Suppose the LFR construction yields $\Omega_{k+1}\subset Z_k^c\subset A$, $A\subset W_k$, the layerwise formula for $H^\partial$ in `VMOD-4.md` (4.1), and `CubeAligned F^\sharp m_1`; assume the torus divisibility and large-torus hypotheses used there. Then for $H\in\{H^-,H^\partial\}$,
$$
\forall x\in\Omega_1(H),\qquad
\sum_{q\in C^\sharp.\mathrm{cubeIdx}}C^\sharp.\chi_q(x)=1,
\qquad
\operatorname{coverDenom}(F^\sharp,x)\ge4^{-d}. \tag{1.1}
$$
The constant is exactly $4^{-d}$ for the denominator and $1$ for the partition; neither depends on $k$, the torus, or the history. Thus **the same** parameter set, partition, and interpolation vector can be used for the old and boundary operators. Equation (1.1) replaces the false pair $(\operatorname{coverOf}H^\partial,H^-)$ of `VMOD-5.md` §2. It proves the `Dec2.CoverGeom.sum_chi` field of both common-cover pairs; it does not prove their `CoverBase.nc` fields.

**Proof.** The depth-$K$ extension of $H^-$ has $\Omega_n(H^-)=\Omega_n(F^\sharp)$ for $1\le n\le k$, so $\Omega_1(H^-)=\Omega_1(F^\sharp)$. For $H^\partial$, use its defining formula
$$
\Omega_n(H^\partial)=
(\Omega_n(H^-)\cap\Omega_{k+1}^{c})\cup
(\Omega_n(\mathbb B_{k+1}(U_{k+1}))\cap\Omega_{k+1})\quad(n\le k),
\qquad \Omega_K(H^\partial)=U_{k+1}\cap\Omega_{k+1}. \tag{1.2}
$$
An $x\in\Omega_1(H^\partial)$ outside $\Omega_{k+1}$ lies in $\Omega_1(H^-)=\Omega_1(F^\sharp)$. If $x\in\Omega_{k+1}$, the history inclusion $\Omega_{k+1}\subset A=\Omega_K(F^\sharp)\subset\Omega_1(F^\sharp)$ gives the same conclusion. Hence both operator first domains are subsets of $\Omega_1(F^\sharp)$. Each such site belongs to a unique $F^\sharp$ layer $n\in[1,K]$. `Balaban/Localization/Cover.lean` `coverDenom_ge` applies to its own cube, with $z=x$, and gives $4^{-d}\le\operatorname{coverDenom}(F^\sharp,x)$. Its `sum_chi`, with the same layer witness and any $\mu\in\mathrm{Fin}\,d$, gives the identity. This is precisely the sum over `cubeIdx (coverOf Fsharp)` and the `chi` of that cover. $\square$

The weaker standalone fact needs no history: if $\Omega_1(H)\subset\Omega_1(F)$, `CubeAligned F m₁`, and $L\ge2$, the cover of $F$ partitions on $\Omega_1(H)$. The old boundary cover does **not** have this inclusion in the empty admissible history of `VMOD-5.md` §2. The common cover works in that history: there $H^\partial$ is empty, $H^-$ is the torus, and $F^\sharp$ covers the torus. No reverse inclusion $\Omega_1(H^-)\subset\Omega_1(H^\partial)$ is asserted.

For a global new operator $H^+=\mathbb B_{k+1}(W_{k+1})$, the same conclusion is conditional on the separate assertion **OPEN-COVER-GLOBAL-INCLUSION**, $\Omega_1(H^+)\subset\Omega_1(F^\sharp)$. Formula (1.2) does not describe that different set.

## 2. What the landed incidence graph permits, and a counterexample to graph GM2

In `Balaban/Localization/Decoupled2FpGeometry.lean`, `incSites` consists of operator sites in $X_1$ or in footprints of eligible live centers. `incGraph` has site-neighbor edges, center-to-footprint edges, and center-to-charged-parameter edges. Its `IsIncUnion C H a ν X₁ 𝒞 Y A` merely asks for **some** adjacency-closed vertex set $U$ whose site projection is $Y$ and parameter projection is $A$. It imposes no seed, minimality, or restriction of $Y$ to `incSites`. The landed `isIncUnion_univ` consequently proves
$$
\operatorname{IsIncUnion}(C,H,a,\nu,X_1,\mathcal C,
\mathbb T,\mathcal C) \tag{2.1}
$$
for every input, including $\mathcal C=\varnothing$. In particular it includes every isolated site vertex. `IsIncUnion.dichotomy` is valid for these large unions; it is a locality dichotomy, not a size theorem.

**Counterexample (proved from the landed definition).** Consider an aligned full-torus generating set $F=H$ with its entire torus in the top layer $K$ and $C=\operatorname{coverOf}F$. Choose a torus with at least two disjoint $\pi'_K$ cubes, and choose $j=K-1$. Take $X$ to be one $\pi'_j$ cube inside a $\pi'_K$ cube, with its singleton chosen family. A connected witness with one site and no bonds shows $d_j^{\rm cov}(X)=0$; nonnegativity follows from `TreeLengthCov.lean treeLenCovOne_nonneg`. Choose the corresponding $X_1$ and set $\mathcal C=\varnothing$. By `isIncUnion_univ`, $Y=\mathbb T$ and $A=\varnothing$ satisfy the landed predicate.

Every `ChosenFamily F m₀ 𝕋 𝒦` must cover both disjoint top $\pi'_K$ cubes. Since the chosen boxes are aligned $\pi'_K$ boxes, a connected witness meeting their boxes has at least one nearest-neighbor bond. Every bond in this all-top-layer instance has weight $(M\ell_K)^{-1}$ by `TreeLength.lean bondW_of_layer`. Hence every admissible cost, and therefore its infimum, is at least $(M\ell_K)^{-1}>0$; an admissible witness exists by taking all top cells and a torus-spanning connected structure. For this instance a proposed universal inequality
$$
\widetilde d_F^{\rm cov}(Y)
\le L^{-1}d_j^{\rm cov}(X)+C(d,L)|\mathcal C| \tag{2.2}
$$
would read a positive number $\le0$. This disproves (2.2) for **all** landed `IsIncUnion` even in a same-set, wall-free instance. Increasing $C(d,L)$ cannot repair it. The construction also satisfies the structural source requirements of `TreeLengthCov.lean CovSetup`: the single fine cube has a containing top cube, and a singleton source tree realizes its covering cost. The counterexample is mathematical; no Lean counterexample declaration was added.

**Correct counting target.** For a chosen nonempty source seed $S\subset X_1\cap\Omega_1(H)$, form the **least** adjacency-closed set containing the site vertices of $S$, inside the active vertices consisting of `incSites`, eligible live centers, and charged parameters incident to them. Take its site and parameter projections $(Y_S,A_S)$. This excludes arbitrary isolated sites and unanchored components. A componentwise variant may start from each source component separately, but its source-tree and hole charges must then be specified. The predicate `IsIncUnion` remains useful to prove the landed dichotomy; it must be accompanied by reachability/minimality before any size bound. This fixes the quantifier error of (2.2), but is **not yet graph GM2**.

The further missing assertion **OPEN-ANCHORED-GRAPH-GM2** must give, for each specified source tree and anchored graph projection, a hole-closed polymer $\widehat Y_S$, a chosen family in the sense of `TreeLengthCov.lean ChosenFamily`, and a connected tree in $\widehat Y_S$ that meets that family. It must charge every added collar, connector, and completed hole so that the bound in `VMOD-5.md` (3.5) holds with a finite $C_{\rm graph}(d,L)$. Its hypotheses must identify the input small-field domain and define which paths across an excluded component enter the hole Steiner activity. The landed `gm2_tree` requires `CovSetup`, a connected input witness, `IsConnectedFamily` of its $Pset$ pieces, and a chosen output family; none is entailed by `IsIncUnion` or anchored reachability. `Polymer/Hole.lean pe_hole` counts **after** the hole polymer and its Steiner activity have been constructed. In particular, the ambient local cost $d(2L+13)N_0$ per charge in `VMOD-5.md` (3.3), with $N_0=3(8L)^d$, is not a total graph GM2 constant: the path can leave the polymer or cross a hole, and a footprint projection need not be a union of chosen boxes.

## 3. The uniform mixed-wall NC3 remains open

The exact needed field is `Dec2.CoverBase.nc` in `Balaban/Localization/Decoupled2.lean`:
$$
\forall\alpha\in\operatorname{AdmPot}(H),\quad
\forall q\in C^\sharp.\mathrm{cubeIdx},\qquad
\operatorname{CubeBlockBounds}(H,a,\nu,\alpha,q,K_c), \tag{3.1}
$$
for $H=H^-$ **and** $H=H^\partial$, with $K_c=K_c(d,L)$ independent of the scale, torus, history and wall shape. `DecoupledCube.lean CubeBlockBounds` requires value, forward-gradient, and symmetric-Laplacian estimates for a complete $H$ source block, with decay at rate $\operatorname{agmonRate}(d)/2$ and factor $\ell_{j'}^2M_f$. The I-4a continuation additionally needs the two-center `CubeBlockHolder` estimate of `DecoupledCubeHolder.lean`.

For foldable boxes, `NC3.lean pointwise_cut_cube`, `value_cut_cube`, `laplacian_cut_cube`, and `holder_pair_cut_cube` are proved **under** `FoldSetting H q s c`; the first three can be assembled with the constant expression of `VMOD-5.md` (1.3), subject to the LFR-to-`FoldSetting` bridge and the small-scale `NC3Small` bridge. `ReflectedGeneratingSet.lean FoldSetting` explicitly requires **every point** of the reflected cube and its one-site collar in $\Omega_1(H)$, as well as no point in $\Omega_{q+1}(H)$. An auxiliary $C^\sharp$ box can cross the physical wall of $H^\partial$; then its `mem_Ω` or `collar` field is false. `ReflectionOperator.lean cut_up_iff` uses that collar, and `operator_intertwine` reflects the artificial Neumann cut. Reflecting a physical Dirichlet face as if it were that cut changes the operator. `ReflectedGeneratingSet.lean mem_reflectedGS_Ω_one` makes the doubled first domain the whole torus, so the landed reflected set does not retain a physical first-domain hole. These are exact statement-level obstructions to invoking NC3 at a mixed wall.

The direct cut coercivity and Agmon estimates do not fill the gap. `Multiscale/CutPointwise.lean cut_pointwise_crude` gives a pointwise bound in terms of the source $\ell^2$ norm. For a bounded complete $j'$-block source this introduces $\ell_{j'}^{d/2}$ beyond the desired $\ell_{j'}^2M_f$, and no constant depending only on $d,L$ absorbs it as $K$ varies. That estimate also does not supply all three parts of (3.1) or the two-center Hölder bound. The global Dirichlet results concern the uncut operator, so replacing it by the cut operator requires a new theorem.

The still **OPEN-NC3-MIXED-WALL** theorem must prove (3.1) and the corresponding `CubeBlockHolder` estimate for boxes meeting a physical Dirichlet wall, with uniform constants and the exact block, neighbor, and analyticity hypotheses consumed by `CoverBase` and I-4a. One possible proof route is a Dirichlet-compatible local regularity and Hölder estimate for the *cut* operator, followed by landed cut Agmon decay; another is an operator intertwining that preserves the preimage of the physical hole and handles corners. Neither is contained in the cited Lean declarations or proved here. The candidate fold constant does not apply to these wall boxes.

## 4. Lean order and disposition

1. **Common partition, 50–100 lines.** Formalize the LFR inclusions $\Omega_1(H^-)\subset\Omega_1(F^\sharp)$ and $\Omega_1(H^\partial)\subset\Omega_1(F^\sharp)$ from (1.2); then apply landed `Balaban.Localization.coverDenom_ge` and `Balaban.Localization.sum_chi` to each operator site. The finite-grid LFR-to-`GeneratingSet`/`CubeAligned` bridge is a separate prerequisite, not a landed declaration.
2. **Graph counterexample and corrected selector, 100–250 lines.** Reuse landed `Balaban.Localization.Dec2.isIncUnion_univ`, `Balaban.Localization.treeLenCovOne_nonneg`, `Balaban.Localization.ChosenFamily`, and `Balaban.Localization.bondW_of_layer`. Define active vertices and the reachability closure of a specified seed; prove it satisfies `IsIncUnion` and contains no unrelated isolated vertices. This establishes only the corrected locality selector.
3. **Graph counting, size unestimated.** Prove source-tree retention, complete-box and hole closure, chosen-family existence, connected weighted paths, and the Steiner charge bound before calling landed `gm2_tree` or `pe_hole`. The counterexample rules out the unqualified target and a reliable line estimate for its replacement is unavailable.
4. **Mixed-wall NC3, size unestimated.** Prove a wall-compatible cut pointwise/gradient/Laplacian/Hölder theorem, then assemble `CubeBlockBounds` and `CubeBlockHolder` uniformly. `FoldSetting` and the landed reflection theorems cover only the boxes satisfying their stated full-cube and collar hypotheses.

The common-cover partition (1.1) is **proved conditional on proved cited LFR geometry**. The universal graph bound (2.2) is **disproved** for the landed predicate. OPEN-ANCHORED-GRAPH-GM2 and OPEN-NC3-MIXED-WALL are **conditional on OPEN assertions**, so the requested complete graph counting and mixed-wall NC3 proofs are unavailable. Confidence is high in the partition and graph counterexample, and high that the landed reflection theorem cannot be applied at a wall that violates `FoldSetting`; the truth of a new uniform mixed-wall estimate is undetermined.
