# The mixed-wall two-centre Hölder estimate

**12 October 2026.** This note proves the mathematical assertion OPEN-CUT-HOLDER-WALL from `VMOD-8.md`: the `CubeBlockHolder` estimate for a cube cut of the operator on the *old* domain, with its physical Dirichlet wall retained. It uses the local Neumann fold and the pointwise result of `VMOD-9.md`. The latter has a mathematical proof but its ten proposed Lean lemmas were not landed when this note was written. Thus the theorem below is **proved conditional on the mathematical Theorem 1.1 of `VMOD-9.md` and its stated hypotheses**; its Lean realization remains open until that theorem and the new lemmas here elaborate. No global reflected generating set is used.

## 1. Precise assertion and constants

Let $d,L\ge3$. Let $H$ be the generating set of the old domain on the common torus, with `Dec2.OpSetting H a ν`; let $\alpha$ satisfy `AdmPot H α`. Let $C$ be the cover of the new domain and $q\in C.\mathrm{cubeIdx}$. Assume `BlockAligned H (intBox q)` and the common-cover cube geometry of `VMOD-9.md` (1.1):
$$\Lambda=\operatorname{intBox}q=\prod_i[c_i,c_i+S-1]\pmod T,
\quad S=5B,\quad B=L^{q.1+m_1},\quad S+B\le T,\quad q.1\le K.$$
These hypotheses follow from the proposed common-cover construction when its geometric obligations are discharged; the present estimate takes them explicitly. In particular, $q$ need **not** belong to $H.\mathrm{cubeIdx}$. Put $D=\operatorname{cubeCut}H\Lambda$ and
$$u=\operatorname{solExt}H\bigl(\operatorname{cubeH}H\,a\,\nu\,\alpha\,q\bigr)^{-1}f.
\tag{1.1}$$
The cut removes only bonds crossing $\partial\Lambda$ between operator sites; the boundary of $\Omega_1(H)$ remains Dirichlet. Let $f$ be supported in the complete $H$ $j'$-block of $y'\in H.\mathrm{layer}(j')\cap\Lambda$, $1\le j'\le K$, with $\|f\|_\infty\le M_f$ and $M_f\ge0$. Write
$$F=L^{2j'}M_f,\qquad E(v)=\operatorname{decay}\bigl(\gamma,H.\mathrm{pathDist}(v,y')\bigr),
\qquad \gamma=\tfrac12\operatorname{agmonRate}(d).\tag{1.2}$$
Let $K_p(d,L)$ and $c_0(d,L)\in(0,1/4]$ be the explicit constants of `VMOD-9.md` (1.3), and $D_0=2d+1$. Choose $C_c(d)\ge0$ from the landed `Green/Lattice/LocHolder.lean lemma_loc_c` (equivalently `Multiscale/PointwiseHolderI.lean loc_lift_c`) and $c_H(d)\ge0$ from the landed `Green/Lattice/HolderSums.lean green_holder_sum`. Write
$$\begin{aligned}
\kappa&=dL/c_0, & C_2&=\frac{2e^{\epsilon_0(1+2d)}L^2b^2}{c_p\sqrt{(c_0/d)^d}},
\\
K_{\rm short}&=C_c\kappa^2,2^{d/2}C_2
 +4L^2c_H e^{\gamma D_0}+16L^2c_H K_p e^{\gamma D_0},
\\
K_{\rm long}&=\frac{8dL}{c_0}(L+1)K_p,
&K_h&=\max\{K_{\rm short},K_{\rm long}\}.
\end{aligned}\tag{1.3}$$
Here $\epsilon_0=\operatorname{agmonRate}(d)$, $b=\sqrt{L^{d-2}}$, and $c_p=\operatorname{poincareConst}(d)$, as in `VMOD-9.md`. All constants depend only on $d,L$. Increasing a landed choice of $C_c$ or $c_H$ merely increases $K_h$.

**Theorem 1.1 (mixed-wall `CubeBlockHolder`; proved under the displayed hypotheses and `VMOD-9.md` Theorem 1.1).** For every $0<\theta<1$, every $x,x'\in\Omega_1(H)\cap\Lambda$, direction $\mu$ with $x+e_\mu,x'+e_\mu\in\Lambda$, and integer vector $z$ satisfying
$$x'=x+\operatorname{intTorus}z,\qquad 1\le r:=\|z\|<B,
\qquad \operatorname{layerIndex}_H(x)\le\operatorname{layerIndex}_H(x')+1,$$
one has, with $\ell=H.\mathrm{spacing}(x)$,
$$\ell^2\left|(u(x'+e_\mu)-u(x'))-(u(x+e_\mu)-u(x))\right|
\le\frac{K_h}{\theta}\ell^\theta r^{1-\theta}
\bigl(E(x)+E(x')\bigr)F.\tag{1.4}$$
This is exactly the inequality field of landed `Localization/DecoupledCubeHolder.lean CubeBlockHolder`, with $H$ in place of its single generating set and $q$ drawn from $C$. In particular, its constant is uniform in $K,m_0,m_1$, torus size, history, physical wall shape, $q,a,\nu,\alpha$, source scale, and $\theta$ apart from the displayed $1/\theta$.

## 2. Geometry and the two cases

The landed `DecoupledCubeHolder.lean chart_z` applies because $x,x'\in\Lambda$, $r<B$, and $S+B\le T$. Thus $z$ is their **coordinate-chart difference**, not merely a congruence class modulo the torus. In particular, when $r$ is small, the chosen chart for $x$ puts $x'$ at lattice coordinate $z$. Since both forward neighbours lie in $\Lambda$, the chart also puts them at $e_\mu$ and $z+e_\mu$. The inequalities are strict enough to exclude a short path around the outside of the cube; this is the point of the $r<B$ quantifier in `CubeBlockHolder`.

Let $j=\operatorname{layerIndex}_H(x)$, $R_j=L^{j-1}$, and $\rho=c_0R_j/d$; for $j=1$, this notation is harmless. Split into
$$\text{short: } j\ge2,\quad \rho\ge8,\quad r\le\rho/4;
\qquad\text{long: the complement}.\tag{2.1}$$
This is the split used by landed `Multiscale/PointwiseHolderMain.lean holder_bound`, with its $1/4$ replaced by the smaller $c_0$ required by the cut pointwise proof. The replacement changes only the scale-case constant.

**Lemma 2.1 (long case; proved).** If (2.1) short fails, then
$$\ell\le\frac{8dL}{c_0}\,\ell^\theta r^{1-\theta}.
\tag{2.2}$$
**Proof.** If $j=1$, then $\ell=L\le8dL/c_0$. If $j\ge2$ and $\rho<8$, then $\ell=\kappa\rho<8dL/c_0$. Otherwise $r>\rho/4$, so $\ell=\kappa\rho<4dLr/c_0$. In either of the first two cases, $r\ge1$, $\ell\ge1$, and $\ell^{1-\theta}\le(8dL/c_0)^{1-\theta}\le8dL/c_0$. In the last case, $\ell^{1-\theta}\le(4dL/c_0)^{1-\theta}r^{1-\theta}\le(8dL/c_0)r^{1-\theta}$. Multiply by $\ell^\theta$. This is the arithmetic of landed `PointwiseHolderMain.holder_scale_cases` and `PointwiseHolder.le_const_rpow_mul`, with $c_0$ abstracted. $\square$

By `VMOD-9.md` (1.4), each of the two displayed forward bonds is retained and
$$|\nabla_\mu u(x)|\le K_p\ell^{-1}E(x)F,
\qquad |\nabla_\mu u(x')|\le K_p\ell'^{-1}E(x')F.
\tag{2.3}$$
The layer-index hypothesis gives $\ell\le L\ell'$. Triangle inequality, (2.2), and $\theta<1$ yield
$$\ell^2|\nabla_\mu u(x')-\nabla_\mu u(x)|
\le (L+1)K_p\ell(E(x)+E(x'))F
\le\frac{K_{\rm long}}{\theta}\ell^\theta r^{1-\theta}(E(x)+E(x'))F.
\tag{2.4}$$
No relation between $H.\mathrm{pathDist}(x,y')$ and $H.\mathrm{pathDist}(x',y')$ is needed here; either may be infinite.

## 3. Short case: local Neumann fold and Hölder sum

Assume the short conditions. Use the folded chart $P$ of `VMOD-9.md` §2 centered at $x$, and set $w(v)=u(P(v))$ on the integer lattice. The ball $B_{2\rho}$ and its one-step neighbors stay inside $\Omega_1(H)$: `VMOD-9.md` Lemma 2.2 applies `Multiscale/PointwiseLift.lean lift_mem_layers` to the physical lifts, since $c_0\le1/4$ and $\rho\ge8$. Thus a face of $\Lambda$ met by this ball is a Neumann face of the **cut** problem, whereas the physical Dirichlet wall is absent from this local calculation. The exact folded row equation of `VMOD-9.md` (2.4) gives, for every $v\in B_{2\rho}$,
$$|{-\Delta}w(v)|\le |f(P(v))|+4R_j^{-2}M,
\tag{3.1}$$
provided $M$ bounds the retained quantity $U_D$ within $H$ path distance $D_0$ of $x$. The folded chart agrees with the four actual values in (1.4):
$$w(0)=u(x),\quad w(e_\mu)=u(x+e_\mu),
\quad w(z)=u(x'),\quad w(z+e_\mu)=u(x'+e_\mu).
\tag{3.2}$$
The first pair follows from the forward-neighbour assumption; the second uses `chart_z` and the other forward-neighbour assumption. A fold crossing at other points of the ball does not change (3.2).

For finite $H.\mathrm{pathDist}(x,y')$, `VMOD-9.md` (3.4)–(3.5), applied to this same folded ball, give
$$T_v:=\rho^{-d/2}\left(\sum_{v\in B_{2\rho}}|w(v)|^2\right)^{1/2}
\le 2^{d/2}C_2 E(x)F.
\tag{3.3}$$
The factor $2^{d/2}$ is the square root of the fold multiplicity; it cannot simply be discarded. The estimate rests on landed `Multiscale/CutAgmon.lean agmon_wsq_le_cut`, the scale separation of `VMOD-9.md` (3.1), and the local fold geometry. It does not use an Agmon estimate on a globally reflected domain.

Let $A_F=\{v\in B_{2\rho}:f(P(v))\ne0\}$. The complete source block has $L^{dj'}$ sites and $P$ has multiplicity at most $2^d$ on the ball, so $|A_F|\le2^dL^{dj'}$. The discrete ball of radius $2L^{j'}$ has at least that many sites: it contains an integer cube of side $2L^{j'}$. Therefore landed `Green/Lattice/HolderSums.lean green_holder_sum`, with $R=2L^{j'}$, bounds the source kernel sum by
$$\frac{c_H}{\theta}\left(r+r^{1-\theta}(2L^{j'}+1)^\theta\right).
\tag{3.4}$$
The same theorem, with radius $2\rho$, bounds the full-ball kernel sum by
$$\frac{c_H}{\theta}\left(r+r^{1-\theta}(2\rho+1)^\theta\right).
\tag{3.5}$$
The finite-lattice result `Green/Lattice/LocHolder.lean lemma_loc_c`, (3.1)–(3.5), and $X=\ell^\theta r^{1-\theta}$ now give
$$\begin{split}
\ell^2|\nabla_\mu u(x')-\nabla_\mu u(x)|
\le{}& C_c\kappa^2rT_v\\
&+\frac{c_H}{\theta}\ell^2M_f\left(r+r^{1-\theta}(2L^{j'}+1)^\theta\right)\mathbf1_{A_F\ne\varnothing}\\
&+\frac{4L^2c_H}{\theta}M
\left(r+r^{1-\theta}(2\rho+1)^\theta\right).
\end{split}\tag{3.6}$$
Here $\ell=\kappa\rho=LR_j$. This is the local estimate before inserting pointwise decay. It is the content of landed `PointwiseHolderI.holder_caseI_pre` after replacing its unfolded field by the local fold and enlarging the source-count radius from $L^{j'}$ to $2L^{j'}$; the old theorem itself is **not** applied to the cut operator.

The three terms of (3.6) have uniform bounds. First, $r\le\ell$ implies $r\le X$; (3.3) bounds the first by $C_c\kappa^2 2^{d/2}C_2 XF E(x)$, and $1\le1/\theta$ inserts the common factor. Second, if $A_F\ne\varnothing$, some source site $P(v)$ lies within $H$ path distance $1$ of $x$ and in the block of $y'$. The landed block-distance estimate used in `PointwiseCase2b.fsum_data` gives
$$H.\mathrm{pathDist}(x,y')\le D_0,
\qquad j\le j'+1.\tag{3.7}$$
Thus $\ell\le LL^{j'}$, $E(x)\ge e^{-\gamma D_0}$, and $2L^{j'}+1\le3L^{j'}$. The real-power arithmetic of landed `Multiscale/PointwiseHolderArith.lean holder_source_arith`, with $3$ in place of its radius coefficient $2$, gives
$$\ell^2\left(r+r^{1-\theta}(2L^{j'}+1)^\theta\right)
\le4L^2L^{2j'}X.
\tag{3.8}$$
This bounds the source term by $(4L^2c_He^{\gamma D_0}/\theta)XE(x)F$. If $A_F$ is empty, that term is zero and (3.7) is unnecessary.

Third, $2\rho+1\le3\rho\le3\ell$ and $r\le\ell$ give
$$r+r^{1-\theta}(2\rho+1)^\theta\le4X.
\tag{3.9}$$
This is the arithmetic of landed `PointwiseHolderArith.holder_term_c`. For all $v\in\Omega_1(H)$ with $H.\mathrm{pathDist}(v,x)\le D_0$, `VMOD-9.md` Theorem 1.1 and the distance triangle inequality give
$$U_D(v)\le K_p e^{\gamma D_0}E(x)F.
\tag{3.10}$$
Take $M=K_p e^{\gamma D_0}E(x)F$. Equations (3.6)–(3.10) yield
$$\ell^2|\nabla_\mu u(x')-\nabla_\mu u(x)|
\le\frac{K_{\rm short}}{\theta}XE(x)F
\le\frac{K_h}{\theta}X(E(x)+E(x'))F.
\tag{3.11}$$

If $H.\mathrm{pathDist}(x,y')=\infty$, the short-case physical lift gives $H.\mathrm{pathDist}(x,x')\le1$ by landed `Multiscale/PointwiseGeom.lean pathDist_lift_le`. Both $x$ and $x'$ are therefore in the same path component, so $E(x)=E(x')=0$. `VMOD-9.md` Theorem 1.1 makes both retained forward gradients zero. This proves (3.11) in the infinite-distance case as well. Combining (2.4) and (3.11) proves Theorem 1.1. $\square$

## 4. Lean dependency plan and consumer check

These are **proposed** mixed-wall declarations, in dependency order; none is claimed to be landed. The VMOD-9 names in this table are likewise proposed declarations at the time of writing. Sizes are rough lines of Lean, including geometry and arithmetic.

| Order | Proposed declaration | Inputs and exact task | Lines |
|---|---|---|---:|
| 1 | `cubeFold_chart_pair` | Landed `DecoupledCubeHolder.chart_z`, proposed `cubeFold_local_geometry` (VMOD-9 order 1); prove (3.2), using both forward-neighbour hypotheses. | 100–170 |
| 2 | `cut_holder_scale_cases` | Adapt landed `PointwiseHolderMain.holder_scale_cases` and `PointwiseHolder.le_const_rpow_mul` to abstract $c_0\in(0,1/4]$; prove (2.2). | 90–150 |
| 3 | `cubeFold_holder_source_card` | Proposed `cubeFold_local_geometry` and landed `LocSums.card_latticeBall_nat`; prove $|A_F|\le2^dL^{dj'}\le|B_{2L^{j'}}|$. | 100–170 |
| 4 | `cubeFold_holder_l2` | Proposed `cubeFold_ball_sq_bound` and `cut_scale_abs` (VMOD-9 orders 6, 4); prove (3.3), retaining $2^{d/2}$. | 70–130 |
| 5 | `cubeFold_holder_loc` | Proposed `cubeFold_local_poisson_bound` (VMOD-9 order 3), orders 1 and 3–4 here, landed `LocHolder.lemma_loc_c` and `HolderSums.green_holder_sum`; prove (3.6). | 200–340 |
| 6 | `cubeFold_holder_arith` | Landed `PointwiseHolderArith.holder_source_arith`, `holder_term_c`, `le_rpow_mul_of_le`; adapt the source-radius coefficient and prove (3.8)–(3.9). | 100–170 |
| 7 | `cubeFold_holder_short` | Orders 5–6, proposed `cut_prop48_cube` (VMOD-9 order 9), landed `PointwiseGeom.pathDist_lift_le` and the block-distance ingredients of `PointwiseCase2b.fsum_data`; prove (3.11), including infinite path distance. | 170–280 |
| 8 | `cubeFold_holder_long` | Order 2, proposed `cut_prop48_cube`, landed `GeneratingSet.layerIndex_spec`; prove (2.4). | 100–170 |
| 9 | `Dec2.cubeBlockHolder_mixed` | Orders 7–8 and landed `DecoupledCubeHolder.CubeBlockHolder`; instantiate the exact `pair` field for $H$ and $q\in C.\mathrm{cubeIdx}$ with constant (1.3). | 100–180 |

The direct search for `CubeBlockHolder` and `cubeBlockHolder_exists` in landed `Localization/Decoupled2*.lean` has **no hits**. That branch's `Dec2.CoverBase.nc` field, in `Decoupled2.lean`, is the three-part `CubeBlockBounds` property (value, forward gradient, Laplacian); `Decoupled2Dg.cube_weighted` consumes it. Hence current `Decoupled2` DG/I-4a closure requires the VMOD-9 pointwise NC3 work, while the two-centre estimate here supplies the separate Hölder regularity assertion. The landed one-set Hölder consumer is `Localization/DecoupledHolder.lean`: `perq_holder` uses `cube_holder`, which obtains `cubeBlockHolder_exists` in `DecoupledCubeHolder.lean`, as well as `cube_lip`; `dg2_holder` then sums the one-centre bounds. A mixed-cover analogue should replace the `cubeBlockHolder_exists` input of `cube_holder` by order 9, while reusing its `weighted_sum_bound` argument. This observation does not weaken Theorem 1.1.

**Open Lean items.** The VMOD-9 orders 1–10 must land, followed by orders 1–9 above. `Dec2.cubeBlockHolder_mixed` then establishes the exact two-centre field for the old operator/new cover. If a later mixed-cover DG theorem needs a global Hölder seminorm, it also needs mixed versions of `cube_holder`, `perq_holder`, and `dg2_holder`; their analytic input is Theorem 1.1, while cover-side cutoffs and counting use the already abstract `DecCover` interface. No counterexample or weakened `CubeBlockHolder` field is required.

**Confidence.** High in the mathematical estimate, including the wall treatment: every short-case use of a full lattice Laplacian occurs inside the physically clear ball, and the long case uses only retained-bond pointwise bounds. The largest formalization task is the four-point chart identity and its interaction with the local folded row. The proof is conditional on the stated common-cover alignment and the mathematically proved, not yet Lean-landed, VMOD-9 pointwise theorem.
