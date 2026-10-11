# NC3: pointwise bounds for the Neumann cube

## Scope and conclusion

This note uses the setting of `LOCALIZATION.md` v2, §§1.1–1.3 and 3.1, in the fine-lattice units of the landed Lean: the fine spacing is one and $\ell_j=L^j$. In particular, the cube is a coordinate cube of side $S=5M_1L^m$, its faces are $M_1L^m$-aligned, $M_1$ is a power of $L$ with $M_1\ge4L^2$, and the generating set has the stated separation parameter $\varrho=RM$, chosen so that $L^d\le\exp((\operatorname{agmonRate}(d)/2)(\varrho-1))$, as required by the landed `PtSetting`/`prop48`. The cube is assumed embedded in the original torus, as in the localization cover. If it covers the entire torus, the cut is empty and the landed global theorem applies directly. Write $D=\square\cap\Omega_1$ and $C^+$ for the concentric cube of side $4M_1L^m$. The cube is a union of every scale-$j$ block it meets for $j\le\min(k,m+1)$; this is the `BlockAligned` hypothesis needed for `cubeCut` and `CutCube.lean`.

**Route: reflection for $m\ge2$, bounded-scale NC2 for $m=1$.** Let $f$ be supported in one complete source block $B'=\Delta_{j'}(y')\subset D$, $\|f\|_\infty=M_f$, and $u=H_z(A)^{-1}f$. There are $B_0=B_0(d,L)$ and $\gamma_0=\tfrac12\operatorname{agmonRate}(d)>0$ such that, for $x\in\Delta_j(y)\subset C^+$,

$$|u(x)|+\ell_j\max_{b\ni x}|\partial u(b)|+\ell_j^2|\Delta^D u(x)|\le B_0e^{-\gamma_0d_G(y,y')}\ell_{j'}^2M_f.$$

The derivative on the left uses retained bonds and zero extension across the original Dirichlet boundary; no cut-face bond meets $C^+$. For one fixed $\theta\in(0,1)$, say $\theta=1/4$, the two cases give the following two-center P2 Hölder estimate for $x\in\Delta_j(y)\subset C^+$, $x'\in\widetilde\Delta_G(x)$, $x\ne x'$, and $x'=x+z$ in the local lattice chart:

$$\ell_j^{2-\theta}|z|^{-(1-\theta)}|\partial_\mu u(x')-\partial_\mu u(x)|\le B_{\theta}\bigl(e^{-\gamma_0d_G(x,y')}+e^{-\gamma_0d_G(x',y')}\bigr)\ell_{j'}^2M_f.$$

Here $e^{-\gamma_0\infty}=0$. If the pair also has $d_G(x,x')\le C_*(d,L)$, the two-center bound implies the single-center bound $B'_{\theta}e^{-\gamma_0d_G(y,y')}\ell_{j'}^2M_f$ requested by G-2(iii). In particular this holds for points in one complete block and for locally connected touching blocks. When $m\ge2$, R0 makes every touching pair in $C^+$ locally connected with $C_*\le4dL^2$, so the full one-center Hölder estimate holds there. The unrestricted single-center G-2(iii) statement is false for the stated `GeneratingSet` interface; the obstruction is given below. The adjacent blocks defining $\widetilde\Delta_G(x)$ and the two derivative bonds stay inside $\square$ by the $C^+$ margin. The constants are independent of $M_1$, $m$, $k$, the torus size, the cube position, and the generating set. The scalar proof applies componentwise to a fixed finite $\mathbb C^N$ with the usual finite-dimensional norm comparison; $N$ may enter $B_0$.

For $m\ge2$, the proof uses the landed uncut `prop48` and `holder_pair_decay` on a *new reflected generating set*; for $m=1$, it uses the landed cut NC2 estimate. It does not claim that `lemmaP` itself extends to an arbitrary cut. The exact construction and intertwining are the new work.

## The normalization check

The factor $\ell_{j'}^{d/2}$ in the crude cut estimate is real for the available NC2 statement. In fine-lattice units, a source supported on $B'$ obeys $\|f\|_2\le\ell_{j'}^{d/2}M_f$. The landed `green_G2i_cut` gives, at $j=j'$ and zero distance, $\|u\|_{2,\Delta_j(y)}\le C\ell_{j'}^2\|f\|_2$. Extracting a site with $|u(x)|\le\|u\|_{2,\Delta_j(y)}$ therefore gives $C\ell_{j'}^{2+d/2}M_f$. At equal large scales there is no scale separation with which to pay $\ell_{j'}^{d/2}$. At $m=1$, the source scale is at most $2$, so this factor is at most $L^d$ and is harmless.

Using the block-normalized norm $\ell_{j'}^{-d/2}\|f\|_2$ changes the display for NC2 but not its content: NC2 controls a block average of $|u|^2$, and a site can be $\ell_j^{d/2}$ times that average without further regularity. In physical units the same missing factor is $(\ell_{j'}/\eta)^{d/2}=L^{j'd/2}$. This is a loss in the deduction from NC2, not a counterexample to NC3 for solutions of the equation. The landed `prop48` removes it by a global weighted maximum; reflection makes that maximum available for the cube equation.

## Reflection construction

**Lemma R0 (the two cube regimes).** If $m\ge2$, the one-site collar $\square^{+1}$ lies in $\Omega_{m-1}\subset\Omega_1$. For every $m\ge1$, $\Omega_{m+2}\cap\square=\varnothing$ whenever $m+2\le k$; hence all layer indices in the cube are at most $q=\min(k,m+1)$. *Proof.* The centre belongs to $\Omega_m$. If $m\ge2$, original separation at level $m-1$ gives distance greater than $\varrho L^{m-1}$ from the centre to $\Omega_{m-1}^c$, hence also to $\Omega_1^c$. Every site of the cube is within coordinate-path length at most $5dM_1L^m/2+2d$ of the centre. The localization assumptions $\varrho=RM$, $M/M_1\ge14d$, $R\ge4dL$ imply $\varrho/L>5dM_1/2+2d/L^m$, so the cube and its one-site collar lie in $\Omega_{m-1}$, hence in $\Omega_1$. For the upper-layer assertion the centre lies outside $\Omega_{m+1}$; separation at level $m+1$ puts $\Omega_{m+2}$ more than $\varrho L^{m+1}$ away, farther than the cube radius. If $m=1$, the lemma gives $j,j'\le2$ but does not claim that the cube lies in $\Omega_1$.

The rest of the reflection construction assumes $m\ge2$. Here $D=\square$, so every cube-face bond is genuinely a cut Neumann bond; no original Dirichlet bond crosses a face. The $m=1$ argument appears after the reflected proof.

Put $q=\min(k,m+1)$. Since $S=5M_1L^m$ is divisible by $L^q$, the doubled periodic lattice $T^*=(\mathbb Z/2S\mathbb Z)^d$ is of the landed form `Torus d (N_* * L ^ q)`, with $N_*=2S/L^q\in\mathbb N$. This choice keeps the mass hypothesis: $0\le\nu L^{2q}\le\nu L^{2k}\le1$. The weights $a_j$, $1\le j\le q$, remain admissible.

Translate the cube to $I^d$, $I=\{0,\ldots,S-1\}$. For one coordinate in $\mathbb Z/2S\mathbb Z$, define

$$r(t)=\begin{cases}t,&0\le t<S,\\2S-1-t,&S\le t<2S.\end{cases}$$

Let $R:T^*\to I^d$ apply $r$ coordinatewise, followed by the inverse translation. Every site in $I^d$ has exactly $2^d$ preimages. The $2^d$ coordinate-reflection maps take a $j$-block to a $j$-block for $j\le q$: each face coordinate and $2S$ are divisible by $L^q$, and $t\mapsto2S-1-t$ reverses a whole aligned block. This is why merely reflecting a function, without reflecting the generating set and its block structure, would be insufficient.

Define $\Omega_j^*=R^{-1}(\Omega_j\cap\square)$ for $1\le j\le q$, and $\Omega_{q+1}^*=\varnothing$. Define $A^*=A\circ R$ on $\Omega_1^*$ and use the original $a_j$, $\nu$ there. The following are the precise geometry obligations.

**Lemma R1 (reflected generating set).** Under the localization cube alignment and separation assumptions, $(\Omega_j^*)_{j=1}^{q+1}$ is a `GeneratingSet d L N_* q ϱ`. Its layer index and spacing satisfy $n^*(p)=n(Rp)$ and $\ell^*(p)=\ell(Rp)$ for $p\in\Omega_1^*$. Its block containing $p$ folds bijectively onto the original block containing $Rp$. Also $\|A^*(p)\|\le\operatorname{coerciveConst}(d)/(2\ell^*(p)^2)$.

*Proof.* Restriction to the aligned cube preserves $j$-block unions, and each reflection permutes $j$-blocks, so every $\Omega_j^*$ is a union of $j$-blocks. Nestedness is immediate. If $q=k$, the top domain is already empty. If $q=m+1<k$, $\Omega_{m+2}\cap\square=\varnothing$: the centre lies in layer $m$, hence outside $\Omega_{m+1}$, while every point of $\Omega_{m+2}$ is more than $\varrho L^{m+1}$ from $\Omega_{m+1}^c$; this exceeds the maximum coordinate-path distance from the centre to the cube by the stated $\varrho=RM$, $M/M_1\ge14d$ and $R\ge4dL$. Thus truncating after $q$ changes no layer inside the cube. A reflected nearest-neighbour path folds to a path in $\square$ after deleting steps that cross a reflection seam; each remaining step has the same layer spacings. Consequently folding cannot increase ordinary path length. If $p\notin\Omega_j^*$ and $v\in\Omega_{j+1}^*$, fold a shortest torus path from $p$ to $v$; its endpoints lie in the original $\Omega_j^c$ and $\Omega_{j+1}$, so its length is greater than $\varrho L^j$ by the original separation. This proves the required strict inequality on $T^*$. Layer and potential identities follow from the definitions. The proof must spell out the coordinate lift when the original cube crosses the torus coordinate origin.

**Lemma R2 (metric folding).** For $p,v\in\Omega_1^*$,

$$d_G(Rp,Rv)\le d_{G^*}(p,v).$$

This includes the infinite-distance case: a finite reflected path folds to a finite original path. *Proof.* Fold each path, delete stationary seam steps, and use the spacing identity from R1. Every nonstationary edge has the same path cost $1/\max(\ell(\cdot),\ell(\cdot))$ as its folded edge. Take the infimum. The folded path stays in $D\subset\Omega_1$, so its cost also bounds the distance in the larger original $\Omega_1$.

**Lemma R3 (operator intertwining).** Let $E$ denote even extension, $(Ev)(p)=v(Rp)$ on $\Omega_1^*$. Let $H_D^*$ be the *uncut* `dirichletOperator` of $G^*$ with $a,\nu,A^*$. Then, as functions on $\Omega_1^*$,

$$H_D^*Ev=E H_z(A)v.$$

Both sides are read as functions on $\Omega_1^*$, and $H_z$ is the cube restriction of `cutOperator G a ν (cubeCut G square) A` from `CutCube.lean`. *Proof.* For an interior nearest-neighbour edge the two Laplacians agree after folding. At either face the exterior neighbour in $T^*$ is the reflected copy of the boundary site, so its contribution $v(x)-v(x)$ is zero, exactly the removed Neumann bond. R0 ensures that no original Dirichlet bond crosses a cube face. A reflected $j$-block is a bijective copy of the original $j$-block, so its block average and the coefficient $a_jL^{-2j}$ agree pointwise after extension. The mass and diagonal potential commute with $E$. Check the two face formulas coordinatewise; their sum also handles corners. No normalization factor appears in the pointwise operator identity. An optional Hilbert-space form uses $2^{-d/2}E$ as an isometry and makes the quadratic-form identity exact.

**Lemma R4 (inverse and source copies).** If $H_z(A)$ and $H_D^*$ are invertible, then $H_D^{*-1}Ef=E H_z(A)^{-1}f$. There are $2^d$ complete reflected $j'$-blocks $B'_\sigma$ and functions $f_\sigma$, each supported in $B'_\sigma$ with $\|f_\sigma\|_\infty\le M_f$, for which $Ef=\sum_\sigma f_\sigma$. Every chosen source point $y'_\sigma\in B'_\sigma$ folds to $y'$. *Proof.* Apply R3 to the cube solution and use uniqueness for $H_D^*$; partition its reflected source by blocks. Invertibility of the cube is landed `cutOperator_isUnit_sharp` plus `cutOperator_inv_supported`/the block-diagonal restriction in `CutCube.lean`; invertibility of $H_D^*$ is the landed uncut coercivity theorem. The reflected source is zero off $\Omega_1^*$, so the Dirichlet restriction causes no extra term.

## Pointwise and Hölder proof

First suppose $m\ge2$, so R0–R4 apply.

Take $x\in\Delta_j(y)\subset C^+$ and its copy in the first half of $T^*$. By R4 and linearity,

$$u(x)=\sum_{\sigma}H_D^{*-1}f_\sigma(x).$$

Apply landed `prop48` to each term with $\Lambda=1$. If the reflected source block is in another component, that term vanishes by the second branch of `prop48`. Otherwise R2 gives $d_{G^*}(x,y'_\sigma)\ge d_G(x,y')$; hence, writing $K_2=K_2(d,L,1)$,

$$|u(x)|+\ell_j\sum_\mu|\partial_\mu u(x)|\le 2^dK_2e^{-\gamma_0d_G(x,y')}\ell_{j'}^2M_f.$$

The reflected forward bonds agree with cube bonds at $x\in C^+$. For backward bonds apply the same estimate at $x-e_\mu$ and use the landed adjacent-layer spacing comparison, losing at most a factor depending on $L$. The landed `pathDist_block_le` gives $d_G(x,y)\le2d$, so replacing $x$ by the block point $y$ costs at most $e^{2d\gamma_0}$. This proves the value and gradient terms with a constant independent of the doubled-box size.

At $x\in C^+$ no cut bond ends. The landed `laplacian_eq_of_cut` or `cutOperator_eq_local` therefore gives

$$-\Delta^D u(x)=f(x)-\nu u(x)-A(x)u(x)-(Q^*aQu)(x).$$

The row estimate in `PointwisePotential.lean`/`CutPointwise.lean` bounds the last three terms by $(3+1)\ell_j^{-2}\sup_{p\in B_j(x)}|u(p)|$ under $\nu L^{2k}\le1$ and the stated potential cap. Every point of $B_j(x)$ is within path distance $2d$ of $x$, so the pointwise estimate above applies with a fixed exponential cost. Also $\ell_j^2|f(x)|\le\ell_{j'}^2M_f$ because $f(x)\ne0$ implies $j=j'$ and $x\in B'$. This proves the Laplacian term. The numerical coefficient may be taken as $4$; its exact value is immaterial to $B_0$.

For the Hölder statement apply landed `holder_pair_decay` (which combines `prop49` for close pairs with `prop48` for farther pairs) to each $f_\sigma$, at the pair $(x,x')$. The landed `layer_le_of_tildeDelta` supplies its layer hypothesis. The pair and its derivative bonds lie in the original cube because a touching block extends by at most a fixed $d,L$ multiple of $L^m$ from $\Delta_j(y)$, while $C^+$ is at distance $M_1L^m/2\ge2L^2L^m$ from the faces. R2 bounds the two reflected decay terms by the two original terms displayed above. Sum the $2^d$ copies. Set $\theta=1/4$; `holder_pair_decay` contributes its fixed factor $1/\theta=4$. For a pair satisfying $d_G(x,x')\le C_*$, the triangle inequality and $d_G(x,y)\le2d$ turn both decay factors into $e^{-\gamma_0d_G(y,y')}$ at cost $e^{\gamma_0(C_*+2d)}$. The `prop49` local-pair hypotheses give $C_*=1$; same-block pairs give $C_*=2d$. For $m\ge2$, R0 gives $\square\subset\Omega_{m-1}$, so every site of the coordinate path between $x$ and $x'$, chosen inside the cube, has spacing at least $L^{m-1}$. Touching blocks have coordinate separation at most $2dL^{m+1}+d$; hence $d_G(x,x')\le4dL^2$ after enlarging the harmless integer-endpoint constant. Thus all required Hölder pairs in this regime have the one-center bound.

**Why the $m=1$ single-center Hölder interface needs correction.** `tildeDelta` in `HolderGlobal.lean` allows two blocks that touch diagonally at a corner: its witness has $\|w\|_\infty\le1$, while `pathDist` uses nearest-neighbour paths inside $\Omega_1$. Two components of $\Omega_1$ may consist of large block-aligned cubes touching only at a corner. Take $x$ in the first component and $x'$ in a touching block of the second; then $x'\in\widetilde\Delta_G(x)$ but $d_G(x,x')=\infty$. Choose $y$ in the first component and $y'$ in the second. The cut and uncut operators are block diagonal across the components. A source supported in one interior $j'$-block of the second component can produce a nonzero gradient at $x'$ (choose a nonconstant $v$ supported away from that block's edge and take $f=H_z(A)v$; the nearest-neighbour and block terms keep $f$ in the block). The gradient at $x$ is zero, while $e^{-\gamma_0d_G(y,y')}=0$. Thus the one-center G-2(iii) formula in `GREEN.md` cannot hold for every `GeneratingSet` allowed by its current definition. The landed theorem `holder_pair_decay` has the correct two-center decay; the landed global unweighted Hölder bound follows from that theorem because both endpoint terms are bounded. For a weighted Hölder norm across such components, weights must be compared at both endpoints or the pair class must be restricted to locally connected pairs. This correction is separate from the cut-face problem.

The $2^d$ copies, the block and touching-block distance costs, the incident-bond conversion, and the row estimate are all functions of $d,L$. They contain no factor involving $S$, $M_1$, $m$, $k$, or the original torus size. The decay rate is the one from `prop48`; it may be reduced to $\gamma_0/2$ if a downstream statement wants spare exponential decay for block summation.

**The $m=1$ case.** R0 gives $j,j'\le2$ everywhere in $D$. Set $t=d_G(y,y')$ when finite in `green_G2i_cut_green`, with $\varepsilon=\operatorname{agmonRate}(d)$, so $\varepsilon/2=\gamma_0$; use `green_G2i_cut_of_pathDist` for the infinite case. Since $\|f\|_2\le L^{j'd/2}M_f\le L^dM_f$ and a site is bounded by its block $L^2$ norm,

$$|u(x)|\le C(d,L)e^{-(\varepsilon/2)d_G(y,y')}L^{2j'}M_f.$$

At $x\in C^+$ no cut bond ends. A forward or backward derivative is a difference of two site values. If the neighbour is in $\Omega_1$, its path distance from $x$ is at most one and its layer spacing differs by at most a factor $L$; apply the site bound there. If the neighbour is outside $\Omega_1$, use its zero extension. As $\ell_j\le L^2$, multiplication by $\ell_j$ costs only a factor depending on $L$. The Laplacian follows from `laplacian_eq_of_cut` and the same block-row estimate used above. For $x'\in\widetilde\Delta_G(x)$, apply the derivative bounds separately at $x,x'$. Since $|z|\ge1$ and $\ell_j\le L^2$, multiplication by $\ell_j^{2-\theta}|z|^{-(1-\theta)}$ has a bounded cost and yields the two-center Hölder estimate. For a locally connected pair, compare the two distances as above. Thus $m=1$ needs no reflection and no scale-dependent iteration.

## Lean implementation order

The following are proposed lemmas, not landed declarations. Sizes estimate additional Lean lines, including geometry and transport proofs. Keep these modules in this scratch workspace until checked; the canonical `/home/scott/Balaban` tree is read-only for this task.

| Order | Proposed lemma/module | Exact contract and inputs | Estimate |
|---|---|---|---:|
| 0 | `NC3.cube_scale_regimes`, `NC3.small_scale_cut_cube` | R0 and the $m=1$ proof from `green_G2i_cut_green`, `cut_pointwise_crude`, and `laplacian_eq_of_cut`; include the two-center Hölder case. | 300–500 |
| 1 | `Reflection.foldCoord`, `foldCube`, `fold_fiber` | Coordinate formula above; every cube point has $2^d$ preimages; adjacent points fold to adjacent/equal points. | 250–400 |
| 2 | `Reflection.fold_block`, `reflect_blockUnion` | For $j\le q$, folding maps each $j$-block bijectively to one original $j$-block; use $L^q\mid S$. | 300–500 |
| 3 | `Reflection.no_higher_layer`, `reflectedGeneratingSet` | R1, including top-domain emptiness, nestedness, strict torus separation, layer and spacing identities, potential cap, mass cap. | 450–750 |
| 4 | `Reflection.pathDist_fold_le` | R2 with `ENNReal` and disconnected components; fold `PathCost` witnesses before taking infima. | 250–400 |
| 5 | `Reflection.lap_intertwine`, `avg_intertwine`, `operator_intertwine` | R3. Split the $2d$ neighbours into interior and the two seam cases; transport `jBlock` and block projection. | 450–700 |
| 6 | `Reflection.green_intertwine`, `source_decompose` | R4. Reuse `cutOperator_isUnit_sharp`, `cutOperator_inv_supported`, and the cube block diagonality of `CutCube.lean`. | 200–350 |
| 7 | `NC3.pointwise_cut_cube`, `NC3.holder_pair_cut_cube`, `NC3.holder_connected_cut_cube` | Apply `prop48`, `holder_pair_decay`; transport distance, derivative, and Laplacian; use `laplacian_eq_of_cut`. State the two-center and locally connected Hölder contracts separately. | 350–600 |

Total: roughly 2,550–4,200 new lines. A worker should first prove R0, then R1 and R3 in a one-dimensional finite interval with one block scale; those are the two genuine mathematical interfaces. The final theorem should take a rectangular `AlignedCube` with an explicit embedded-coordinate chart and the cube alignment hypotheses of `LOCALIZATION.md`, rather than a bare `CutAligned` bond set. A generic aligned cut need not admit this reflection.

`green_G2i_cut` and `green_G2i_cut_green` supply the bounded-scale $m=1$ case and remain NC2 elsewhere. `lemma_loc_a`, `lemma_loc_b`, `lemma_loc_c`, and `lemmaP` are reused *through* the already landed `prop48`, `prop49`, and `holder_pair_decay` when $m\ge2$; no cut-specific version of their maximum argument is required. `CutPointwise.lean` supplies the interior equation, and `CutCube.lean` supplies the cube restriction. No new discrete Moser theorem is needed.

## Confidence and limits

**Mathematical confidence: high for the pointwise/gradient/Laplacian estimate and the two-center Hölder estimate, conditional on the explicit cube geometry above.** The reflection identity is elementary and exact in the R0 $m\ge2$ regime; the $m=1$ regime uses only bounded scales. Metric folding has the needed direction. The main formalization risk is the construction of `GeneratingSet` on a torus whose side and depth differ from the original, including block coordinates at translated faces. The stated side divisibility, cube alignment, and truncation at $q=\min(k,m+1)$ address that risk; R0, R1 and R3 should be checked before any long pointwise port. The unrestricted one-center Hölder statement fails in the $m=1$ regime without a local connectivity hypothesis or a corrected two-center interface. If the intended cube is not an embedded block-aligned coordinate cube, this route does not cover it without a separate geometric reduction. No Lean file was edited or built for this note.
