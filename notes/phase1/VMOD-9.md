# A local Neumann fold for the mixed-wall cut pointwise estimate

**12 October 2026.** This note settles the **pointwise assertion** OPEN-CUT-POINTWISE-WALL of `VMOD-8.md` §3 at the mathematical level. The operator retains the physical Dirichlet wall of $\Omega _1(H)$ and cuts only the bonds crossing the interaction cube. The high-scale proof uses a *local* Neumann fold of the solution on the ball used by Lemma P. That ball stays inside $\Omega _1(H)$ by the landed `PointwiseLift.lift_mem_layers`; thus it never asks for a global reflected generating set and never changes the physical hole. The full two-center `CubeBlockHolder` estimate is a separate assertion and is not claimed here. No Lean declaration in this note has been added to the read-only repository.

## 1. Statement and constants

Take the data and notation of `VMOD-8.md` §1. In particular, $d,L\ge3$, $H$ obeys `Dec2.OpSetting H a ν`, $\alpha$ obeys `AdmPot H α`, and $q$ is an index of the common cover $C=\operatorname{coverOf}F^\sharp$. Assume `BlockAligned H (intBox q)`. The cover index is a genuine geometric cube index of $F^\sharp$, $N_1>5$, and therefore landed `BoxCube.box_eq_cubeSet` identifies
$$\Lambda=\operatorname{intBox}q
  =\prod_{i=1}^d[c_i,c_i+S-1]\pmod T,qquad
  S=5L^{q.1+m_1}<T=(N_1L^{m_1})L^K.\tag{1.1}$$
The $H$ domain need not contain this cube. Put $D=\operatorname{cubeCut}H\Lambda$, $u=\operatorname{zeroExt}_{\Omega _1(H)}(H_D(\alpha)^{-1}f)$, $\epsilon_0=\operatorname{agmonRate}(d)$, $\gamma=\epsilon_0/2$, and $c_p=\operatorname{poincareConst}(d)>0$. The source $f$ is supported in one **complete $H$ $j'$-block** containing $y'\in H.\mathrm{layer}(j')\cap\Lambda$, $1\le j'\le K$, with $|f|\le M_f$. Define the retained forward quantity
$$U_D(x)=|u(x)|+\ell_H(x)
  \sum_{\mu:(x,\mu)\notin D}|u(x+e_\mu)-u(x)|,
  \qquad x\in\Omega _1(H).\tag{1.2}$$
Physical Dirichlet bonds are retained; only artificial cube-crossing bonds are omitted. If $x\notin\Lambda$, then $U_D(x)=0$: landed `CutCube.cutOperator_inv_supported` gives $u=0$ outside $\Lambda$, and each bond from outside to inside is in $D$ when both endpoints are operator sites.

Here are explicit constants, expressed through constants of landed finite-lattice estimates. Choose any $C_a(d),C_b(d)\ge0$ supplied by `Green/Lattice/Loc.lean lemma_loc_a`, `lemma_loc_b`, and any $c_G(d)\ge0$ supplied by `Green/Lattice/LocGreenSums.lean green_sum_le`. Set
$$\begin{gathered}
b=\sqrt{L^{d-2}},\qquad D_0=2d+1,\qquad
\vartheta=\tfrac14e^{-\gamma D_0},\\
c_0=\min\left\{\tfrac14,
 \frac{\vartheta}{c_G(3+1)(9+3L)+1}\right\},\qquad
J_0=\frac{8dL}{c_0},\\
A_0=\frac{\sqrt8}{c_p}+d\sqrt{\frac{10}{c_p}},\qquad
C_2=\frac{2e^{\epsilon_0(1+2d)}L^2b^2}
 {c_p\sqrt{(c_0/d)^d}},\\
K_1=\max\left\{
 A_0b\sqrt{J_0^d},\quad
 2^{d/2}\left(C_a+\frac{d^2L}{c_0}C_b\right)C_2
       +c_G(9+3dL)e^{\gamma D_0}\right\},
\qquad K_p=2K_1.\tag{1.3}
\end{gathered}$$
All are finite and depend only on $d,L$. The chosen values are deliberately no smaller than the bounds below; no numerical value for $C_a,C_b,c_G$ is needed beyond the landed existence theorems.

**Theorem 1.1 (proved conditional on the PROVED landed estimates cited below and the stated `BlockAligned` hypothesis).** Uniformly in $K,m_0,m_1$, the torus, history, physical wall shape, $q,a,\nu,\alpha$, and every $1\le j'\le K$,
$$U_D(x)\le K_p(d,L)\,
 \operatorname{decay}\bigl(\gamma,H.\mathrm{pathDist}(x,y')\bigr)
 L^{2j'}M_f,qquad x\in\Omega _1(H).\tag{1.4}$$
In particular, (3.1)–(3.2) of `VMOD-8.md` hold **at every operator site of the cube**, including its artificial face where it meets the physical wall. `VMOD-8.md` Proposition 3.1 then proves the full `CubeBlockBounds` triple, with
$$K_c(d,L)=\max\{K_p,\ e^{\epsilon_0d}(1+4K_p)\}.\tag{1.5}$$
This is a mathematical proof under the displayed `OpSetting`, `AdmPot`, cube-index, and `BlockAligned` hypotheses. The new local-fold and cut Lemma-P steps in §§2–4 are not yet landed Lean lemmas.

## 2. Pure cube geometry and the local row equation

**Lemma 2.1 (proved).** If $x\in H.\mathrm{layer}(j)\cap\Lambda$ and $\Lambda$ is `BlockAligned H`, then $S\ge L^j$. For $r=L^{j-1}$ and any $0<c_0\le1/4$ with $\rho=c_0r/d\ge8$, choose the coordinate chart (1.1) and a preimage $p_0$ of $x$ in $[0,S-1]^d$. Define, coordinatewise on the torus of period $2S$,
$$F_i(t)=\begin{cases}t,&0\le t<S,\\2S-1-t,&S\le t<2S,\end{cases}
\qquad P(z)=c+F(p_0+z)\pmod T.\tag{2.1}$$
For $z$ in the lattice $\ell^\infty$ ball $B_{2\rho}$, $P(z)\in\Lambda$ and $P(z)$ has a physical torus lift $x+h(z)$ with $\|h(z)\|_\infty\le\|z\|_\infty$. The same holds for each $P(z\pm e_\mu)$ with bound $\|z\|_\infty+1$. The map $P$ has multiplicity at most $2^d$ on $B_{2\rho}$.

**Proof.** `BlockAligned` puts the complete $j$-block of $x$, containing $L^{dj}$ distinct sites, into $\Lambda$. The product interval (1.1) has $S^d$ sites, so $S\ge L^j$. Each one-dimensional fold $F_i$ moves by at most one under a lattice step; tracing $z_i$ steps from $p_{0,i}$ proves the coordinate displacement bound and membership in the interval. Also $4\rho\le r/d<2S$; therefore reduction of $p_0+z$ modulo $2S$ is injective on $B_{2\rho}$. Each point of $[0,S-1]^d$ has exactly $2^d$ preimages on the doubled torus, so the asserted multiplicity follows. $\square$

Write $w(z)=u(P(z))$ and $f_F(z)=f(P(z))$. The physical zero extension is used in the row equation; $w$ itself is defined by (2.1) on the full integer lattice.

**Lemma 2.2 (proved).** Let $x\in H.\mathrm{layer}(j)\cap\Lambda$, $j\ge2$, and $\rho=c_0L^{j-1}/d\ge8$. For every $z\in B_{2\rho}$, $P(z)$ and all physical nearest neighbors needed by the cut row lie in $\Omega _1(H)$. If $M\ge0$ bounds $U_D(v)$ for every $v\in\Omega _1(H)$ with $H.\mathrm{pathDist}(v,x)\le D_0$, then
$$|{-\Delta}w(z)|\le |f_F(z)|+(3+1)L^{-2(j-1)}M.\tag{2.2}$$
Moreover
$$U_D(x)=|w(0)|+L^j\sum_\mu|w(e_\mu)-w(0)|.\tag{2.3}$$

**Proof.** Since $d(2\rho+1)=2c_0L^{j-1}+d$ and $\rho\ge8$ implies $d\le c_0L^{j-1}/8$, the left side is at most $(1/2+1/32)L^{j-1}<L^{j-1}$. Lemma 2.1 therefore places every point under discussion in the lifted ball of `Multiscale/PointwiseLift.lean lift_mem_layers` around $x$. That landed theorem makes these points operator sites and bounds their spacing below by $L^{j-1}$. Its companion `PointwiseGeom.pathDist_lift_le` gives $H.\mathrm{pathDist}(P(z),x)\le1$. Every site in the $H$ block of $P(z)$ is an operator site at path distance at most $2d+1$ from $x$, by landed `GeneratingSet.pathDist_block_le`. Hence its $u$ value has norm at most $M$.

At an interior point of $\Lambda$, the two folded neighbors in direction $\mu$ are its ordinary neighbors. At a face, the outward folded neighbor equals the point itself, so its contribution to $-\Delta w$ is zero. Because the physical neighbor outside the cube is still in $\Omega _1(H)$ in this local ball, `CutOperator.mem_cubeCut` says precisely that this outward bond was removed by $D$. This remains true at intersections of several cube faces, one coordinate at a time. The cut-operator row thus gives the **exact** identity
$$-\Delta w(z)=f_F(z)-\nu u(P(z))-\alpha(P(z))u(P(z))
 -(\operatorname{avgMatrix}H a\,u)(P(z)).\tag{2.4}$$
It is the elementary neighbor calculation of `ReflectionOperator.lean cutLaplacian_mulVec_row` and `lap_intertwine`, applied only in the local ball; no `FoldSetting.mem_Ω` for the whole cube is assumed. Landed `PointwisePotential.lean avg_row_bound` bounds the last row by $2L^{-2\operatorname{layerIndex}(P(z))}M$; the potential term by $L^{-2\operatorname{layerIndex}(P(z))}M$; and `OpSetting.massLe` bounds $\nu M\le L^{-2\operatorname{layerIndex}(P(z))}M$. The landed combined estimate `CutPointwise.laplacian_bound_cut` uses the safe coefficient $3+1$ for these three terms. Since the spacing at $P(z)$ is at least $L^{j-1}$, (2.2) follows. Finally an outward forward bond from $x$ is folded back to $x$ and is in $D$; every other forward folded neighbor is the retained physical neighbor. This proves (2.3). $\square$

The point of (2.4) is that the physical Dirichlet wall is untouched. At high evaluation scale the local ball does not meet it. At low evaluation scale the proof below uses cut Agmon bounds and never folds.

## 3. Cut Lemma P, including high source scales

The following geometric arithmetic is the landed proof of `PointwiseScale.scale_abs` with no use of the uncut operator. For $x\in H.\mathrm{layer}(j)$ and $0\le t\le H.\mathrm{pathDist}(x,y')$, there is $t_2$ with $t\le t_2\le H.\mathrm{pathDist}(x,y')$ such that
$$b^{j'}e^{-\epsilon_0t_2}\le b^{j+1}e^{-\gamma t}.\tag{3.1}$$
For $j'\le j$ take $t_2=t$. Otherwise put $m=j'-j$, $s=(\varrho-1)(m-1)$ and $t_2=\max(t,s)$. Landed `GeneratingSet.pathDist_separation_le` gives $s\le H.\mathrm{pathDist}(x,y')$; (1.1) of `VMOD-8.md` gives $b\le e^{\gamma(\varrho-1)}$; and $e^{-\epsilon_0\max(t,s)}\le e^{-\gamma t}e^{-\gamma s}$. These prove (3.1), including the case $m=1$.

**Lemma 3.1 (proved: cut Lemma P).** For every $x\in\Omega _1(H)$, $0\le t\le H.\mathrm{pathDist}(x,y')$, and $M\ge0$ satisfying $U_D(v)\le M$ for all $v$ with $H.\mathrm{pathDist}(v,x)\le D_0$,
$$U_D(x)\le K_1 e^{-\gamma t}L^{2j'}M_f+\vartheta M.\tag{3.2}$$

**Proof at bounded evaluation scale.** If $x\notin\Lambda$, use $U_D(x)=0$. Otherwise write $j=\operatorname{layerIndex}_H(x)$. Let $\rho=c_0L^{j-1}/d$. If $\rho<8$, then $L^j<J_0$. Apply landed `CutAgmon.agmon_block_cut` with $\epsilon=\epsilon_0$ and the $t_2$ of (3.1). This uses its $e^{-\epsilon_0t_2}$ block estimate, which is stronger than the $e^{-\gamma t_2}$ form of landed `cut_pointwise_crude` noted in `VMOD-8.md`. The value sum on the block of $x$ and `CutPointwise.single_le_cutBlockGrad` on each retained forward bond give, by Cauchy–Schwarz and the stated constants of `agmon_block_cut`,
$$U_D(x)\le A_0 L^j e^{-\epsilon_0t_2}
 L^{j'}\|f\|_2.\tag{3.3}$$
Landed `Multiscale/Locality.lean sqrt_sqNorm_le_of_supp` gives
$L^{j'}\|f\|_2\le L^{2j'}b^{j'}M_f$. By (3.1) and the identity
$L^jb^j=\sqrt{L^{dj}}$, (3.3) is at most
$A_0b\sqrt{J_0^d}\,e^{-\gamma t}L^{2j'}M_f$. This proves (3.2) in this case, even if the physical wall and cut face intersect at $x$.

**Proof at large evaluation scale.** If $\rho\ge8$, then $j\ge2$; $j=1$ would give $\rho\le1/(4d)<8$. Use Lemmas 2.1–2.2 and apply landed `Green/Lattice/Loc.lean lemma_loc_a` and `lemma_loc_b` to the integer-lattice field $w$. These give the value and forward-gradient bounds at $0$ in terms of (i) $\rho^{-d/2}\|w\|_{\ell^2(B_{2\rho})}$ and (ii) lattice-Green sums of $|{-\Delta}w|$ on $B_{2\rho}$. Equation (2.3) turns their left sides into $U_D(x)$.

For (i), use landed `CutAgmon.agmon_wsq_le_cut` with the weight $H.\mathrm{truncDist}(y',t_2)$ and `AgmonDecay.agmonSource_le`. Every $P(z)$ in the ball is at $H$ path distance at most $1$ from $x$ and has spacing at most $L^{j+1}$ by `lift_mem_layers`. The multiplicity in Lemma 2.1 is at most $2^d$. Thus, with
$A=L^{j'}e^{2\epsilon_0d}\|f\|_2$,
$$\|w\|_{\ell^2(B_{2\rho})}
 \le 2^{d/2}\frac{2}{c_p}L^{j+1}
 e^{-\epsilon_0(t_2-1)}A.\tag{3.4}$$
The algebra of landed `PointwiseCase2c.l2_part` applies to the displayed bound: insert $\rho=c_0L^{j-1}/d$, use $A\le e^{2\epsilon_0d}L^{2j'}b^{j'}M_f$, and then (3.1). It yields
$$\rho^{-d/2}\|w\|_{\ell^2(B_{2\rho})}
 \le 2^{d/2}C_2 e^{-\gamma t}L^{2j'}M_f.\tag{3.5}$$
No source-volume factor remains; the scale mismatch $b^{j'}$ has been paid by the separation of the $H$ layers in (3.1).

For the source part of (ii), let $A_F=\{z\in B_{2\rho}: f_F(z)\ne0\}$. The source block has $L^{dj'}$ sites, and Lemma 2.1 gives $|A_F|\le2^dL^{dj'}$. Landed `LocSums.card_latticeBall_nat` therefore permits `LocGreenSums.green_sum_le` with radius $2L^{j'}$. Its two conclusions give
$$\sum_{z\in A_F}G_d(-z)\le9c_GL^{2j'},\qquad
\sum_{z\in A_F}|G_d(-z+e_\mu)-G_d(-z)|\le3c_GL^{j'}.\tag{3.6}$$
If $A_F\ne\varnothing$, its physical image lies in the $j'$-block of $y'$ and within $H$ path distance $1$ of $x$. Landed `GeneratingSet.pathDist_block_le` and the layer-separation argument of `PointwiseCase2b.fsum_data` give
$$H.\mathrm{pathDist}(x,y')\le D_0,\qquad j\le j'+1.\tag{3.7}$$
Hence $e^{-\gamma t}\ge e^{-\gamma D_0}$ and $L^j\le LL^{j'}$. Combining (3.6) with the $d$ gradient directions bounds the source part by
$c_G(9+3dL)e^{\gamma D_0}e^{-\gamma t}L^{2j'}M_f$; if $A_F=\varnothing$, it is zero.

For the $M$ part of (ii), use (2.2) and `green_sum_le` on the full $B_{2\rho}$. The same elementary calculation as landed `PointwiseCase2d.pot_arith` bounds the value plus $L^j$ times the $d$ gradients by
$$c_G(3+1)(9+3L)c_0M\le\vartheta M.\tag{3.8}$$
The two Loc $\ell^2$ coefficients combine as $C_a+d^2L C_b/c_0$, exactly as in `PointwiseCase2d.case2_bound`. Equations (3.5)–(3.8) prove (3.2) with the second entry of $K_1$ in (1.3). $\square$

## 4. Maximum principle and the full pointwise conclusion

For finite $H.\mathrm{pathDist}(x,y')$, maximize
$e^{\gamma H.\mathrm{pathDist}(x,y')}U_D(x)$ over the finite operator domain, exactly as in landed `Multiscale/Pointwise48.lean prop48`. A point within $H$ path distance $D_0$ of a maximizer has its unweighted $U_D$ bounded by $e^{\gamma D_0}$ times the maximizer's weighted value after the appropriate decay factor. Apply (3.2) there with $t=H.\mathrm{pathDist}(x,y')$. The recurrence coefficient is
$$\vartheta e^{\gamma D_0}=\tfrac14,$$
so the maximum is at most $\frac43K_1L^{2j'}M_f\le K_pL^{2j'}M_f$. At infinite $H$ path distance, landed `CutAgmon.green_G2i_cut_of_pathDist` makes both the block value and its retained gradient energy zero, hence $U_D(x)=0$. This proves (1.4). Dropping nonnegative terms from (1.2) gives the value and each retained forward-gradient estimate. For $x\in\Lambda$ and $x+e_\mu\in\Lambda$, `CutOperator.mem_cubeCut` says the bond is retained, which is precisely the gradient quantifier of `VMOD-8.md` (3.2).

The Laplacian statement (1.5) follows from the already proved conditional implication `VMOD-8.md` Proposition 3.1: `Decoupled.noCutAt_cubeCut` at the sites where all symmetric neighbors are in $\Lambda$, the value bound at the complete $H$ block of such a site, and landed `Localization/NC3.lean laplacian_cut_bound`. No replacement `CoverBase.nc` field or larger cube collar is needed for this pointwise result.

## 5. Lean lemmas in dependency order

The mathematical proof above is complete under the displayed hypotheses. The following are **new proposed declarations**, not landed Lean results; line counts are rough implementation estimates. Reuse named landed declarations only with their actual premises.

| Order | New declaration | Landed inputs and proof obligation | Estimate |
|---|---|---|---:|
| 1 | `cubeFold_local_geometry` | `BoxCube.box_eq_cubeSet`, `CutOperator.BlockAligned`, `Locality.card_blk`; prove $S\ge L^j$, coordinate displacement, ball injectivity, multiplicity $\le2^d$. | 250–400 |
| 2 | `cubeFold_local_neumann_row` | `CutOperator.mem_cubeCut`, `ReflectionOperator.cutLaplacian_mulVec_row`; prove (2.4) for high-layer lifted balls, retaining the original physical domain. | 180–300 |
| 3 | `cubeFold_local_poisson_bound` | Order 2, `PointwiseLift.lift_mem_layers`, `PointwiseGeom.pathDist_lift_le`, `PointwisePotential.avg_row_bound`, `OpSetting.massLe`, `AdmPot`; prove (2.2) and (2.3). | 180–280 |
| 4 | `cut_scale_abs` | Refactor the geometric proof of `PointwiseScale.scale_abs` to take the layer, source scale and separation directly, without `PtSetting`. | 80–130 |
| 5 | `cut_case1_retained` | `CutAgmon.agmon_block_cut`, `CutPointwise.single_le_cutBlockGrad`, `Locality.sqrt_sqNorm_le_of_supp`, order 4; prove (3.3) and its uniform low-scale consequence. | 130–200 |
| 6 | `cubeFold_ball_sq_bound` | `CutAgmon.agmon_wsq_le_cut`, `AgmonDecay.agmonSource_le`, order 1, `PointwiseGeom.pathDist_lift_le`; prove (3.4) and (3.5). | 200–320 |
| 7 | `cubeFold_source_green_sum` | `LocGreenSums.green_sum_le`, `LocSums.card_latticeBall_nat`, order 1, `PointwiseCase2b.fsum_data` geometric argument; prove (3.6)–(3.7). | 160–250 |
| 8 | `cut_lemmaP_cube` | `Loc.lemma_loc_a/b`, orders 3 and 5–7, `PointwiseCase2d.pot_arith`; prove (3.2) with the explicit $K_1$. | 250–400 |
| 9 | `cut_prop48_cube` | Order 8, maximum argument of `Pointwise48.prop48`, `CutAgmon.green_G2i_cut_of_pathDist`; prove (1.4). | 150–240 |
| 10 | `Dec2.cubeBlockBounds_mixed` | Order 9, `Decoupled.noCutAt_cubeCut`, `NC3.laplacian_cut_bound`; provide `CoverBase.nc` with (1.5). | 80–140 |

The new declarations must be placed in writable campaign files by a Lean worker; this note does not assert that they have elaborated. The full `CubeBlockHolder` at high source scale is **OPEN-CUT-HOLDER-WALL** from `VMOD-8.md`, independent of the pointwise closure here. A complete modular I-5 still also needs the common-cover geometry and counting obligations recorded in `VMOD-7.md`; Theorem 1.1 proves only the analytic pointwise NC3 component conditional on its stated cover geometry.

**Confidence.** High in the scale argument, cut Agmon input, local physical-wall clearance, finite-fold multiplicity, and maximum-principle closure. The local Neumann row identity (2.4) is elementary and proved coordinatewise above, but its Lean formalization is the largest new geometric step. The constants are conservative explicit expressions in proved finite-lattice constants, uniform in every parameter listed in Theorem 1.1.
