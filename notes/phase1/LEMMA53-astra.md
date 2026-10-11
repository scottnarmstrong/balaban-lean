# The hard-spin approximate field (Lemma 5.3)

## Scope and source

This is a replacement proof of Lemma 5.3 and its geometric and interpolation inputs for the one-site collar used in BACKGROUND.md, version 2, §5.3. It uses the fine-lattice units of GeneratingSet.lean. Balaban's original construction is P2, §3, pp. 616–621, especially (3.1)–(3.16) and Lemma 3.1 on p. 620 (PDF pages 10–15 and 14, respectively). Its data assumptions are P2 (1.11)–(1.12), p. 610 (PDF page 4). Our choice $\alpha_0=0$ and the layer-one modification below are specific to the hard-spin limit; they are not claims about Balaban's printed interpolant.

**Correction to the reviewed draft.** Lemma 5.3a(b) as stated in BACKGROUND.md is false for the one-site collar in $d\ge4$. The quoted rerouting cannot be supplied. The replacement Lemma 5.3a below has the chain assertion only for sites of layer at least two, exactly where the new interpolation uses it. At layer one the field is the local constant solution of its own block. This settles the marked UNCERTAIN point without thickening the collar or changing GeneratingSet.

## 1. Conventions and quantitative assumptions

Let $d\ge3$, $L\ge3$, $N\ge2$, $k\ge1$, and $G:\mathrm{GeneratingSet}\ d\ L\ N_0\ k\ \varrho$ with $\varrho\ge4dL$. Write $T=\mathrm{Torus}\ d\ (N_0L^k)$, $\Omega_j=G.\Omega j$, $\Lambda_j=G.\mathrm{layer}\ j=\Omega_j\setminus\Omega_{j+1}$, $n(x)=G.\mathrm{layerIndex}\ x$, and $\ell(x)=G.\mathrm{spacing}\ x=L^{n(x)}$ on $\Omega_1$. The distance in the separation axiom is the fine-lattice torus $\ell^1$ distance. Set $C=\{z\notin\Omega_1:\operatorname{dist}(z,\Omega_1)=1\}$. Each $z\in C$ is a singleton block of index zero. At a site $x\in\Omega_1$, the unique layer block containing $x$ is $B_x$. A block $B$ of layer $m$ means a fibre of jBlock at $m$, entirely contained in $\Lambda_m$; this follows from blockUnion at $m$ and $m+1$.

For a complex vector $v\in\mathbb C^N$, write $|v|=\mathrm{vn}(v)$ and $v\cdot w=\sum_i v_iw_i$, without conjugation. All estimates below use the Euclidean norm; hence their displayed constants in fact do not grow with $N$. The Laplacian is $\Delta v(x)=\sum_{\mu=1}^d(v(x+e_\mu)+v(x-e_\mu)-2v(x))$, the expression in IsSmoothField.lap. IsSmoothField.grad asks for both signs at each $x\in\Omega_1$. A bond touching $C$ is therefore included. No PathCost path is asserted on $C$: the landed PathCost relation is restricted to $\Omega_1$.

Assume the real and complex data conditions (R1)–(R4), (C1)–(C3) of BACKGROUND.md §1.3, including $\mu L^{2k}\varepsilon^2\le\delta^2$, $0<\delta\le\varepsilon\le1/16$, $a_m\in[1/2,2]$, and $0\le\mu L^{2k}\le1$. Adjacent block data differ by at most $2\delta$ in the complex domain. Strict inequalities in the domain give the same weak estimates. For each layer block $B$ put $\nu_B=\mu L^{2m}$ and

$$
w_B=a_m\Psi_B+\nu_B H_B,\qquad
s_B=\sqrt{w_B\cdot w_B},\qquad
\phi^B=w_B/s_B,\qquad
\widehat\alpha^B=s_B-a_m-\nu_B,\qquad
\alpha^B=L^{-2m}\widehat\alpha^B.
$$

The square root is principal. For $z\in C$, put $\phi^z=\Psi_z/\sqrt{\Psi_z\cdot\Psi_z}$. The local source equation is exactly

$$
a_mL^{-2m}(\Psi_B-\phi^B)+\mu(H_B-\phi^B)-\alpha^B\phi^B=0,\qquad \phi^B\cdot\phi^B=1. \tag{1}
$$

Here $H_B$ denotes the value of the block-constant mass datum $\tilde h$ on $B$. In the real case it equals the constant vector $h$.

For a self-contained numerical choice, set $J=4096$. Under $\delta\le2^{-20}$ the following local estimates hold:

$$
|\phi^B|\le2,\quad |\phi^B-\Psi_B|\le1695\delta,\quad
|\widehat\alpha^B|\le272\delta,\quad
|\phi^B-\phi^{B'}|\le J\delta \quad(B,B'\text{ adjacent}), \tag{2}
$$

where a collar singleton is allowed in the last inequality. For real data,
$\sqrt{\nu_B}|\phi^B-h|\le2048\delta$. The same bounds with $1695$ replaced by $3$ hold for a collar singleton where applicable. These numbers follow directly, without the open endpoint $a+\nu>1/2$ in the presently landed norm_cMultiplier_le, as follows.

Let $\psi$ be the real part of $\Psi$, $q=\psi/|\psi|$, $u=\sqrt{\Psi\cdot\Psi}$, and $p=\Psi/u$. Conditions (R2), (C2) give $|u-1|\le2\delta$, $|u|\ge1-2\delta$, $|\Psi|\le5/4$, $|p|\le3/2$, $|p-\Psi|\le3\delta$, and $|p-q|\le\varepsilon+5\delta$. Conditions (R3), (R4) give $\nu|h-q|^2\le3\delta^2$, including $\nu=0$. Conditions (C3) and $\nu\varepsilon\le\delta$ give $\nu|h'|\le\delta$ and $\nu|H-p|\le9\delta$. Consequently, with $s_0=a+\nu\in[1/2,3]$,

$$
e:=w-s_0p,\qquad |e|\le a|p-\Psi|+\nu|H-p|\le15\delta,\qquad
|w\cdot w-s_0^2|\le2s_0|p||e|+|e|^2\le136\delta.
$$

Thus $\operatorname{Re}(w\cdot w)>1/8$, $|s|\ge1/4$, and
$|s-s_0|=|w\cdot w-s_0^2|/|s+s_0|\le272\delta$. Hence
$|\phi-p|\le4(15+272(3/2))\delta=1692\delta$ and
$|\phi-\Psi|\le1695\delta$. The norm bound follows from
$|\phi|\le3/2+1692\delta<2$. Adjacent complex data differ by at most $2\delta$, so the triangle inequality gives $3392\delta<J\delta$. For real data $\sqrt\nu|\phi-h|\le|\phi-\psi|+\sqrt{\nu}|q-h|\le1696\delta+\sqrt3\delta<2048\delta$. The same elementary normalization proves the collar assertions. Every inequality here is valid at $a=1/2$ and $\nu=0$.

## 2. The geometric obstruction and the replacement Lemma 5.3a

Take $d=4$, $k=1$, a torus large enough that wrapping does not identify the following cubes, and let $\Omega_1$ consist of just $B=[0,L-1]^4$ and $B'=[L,2L-1]^4$. The separation condition is vacuous because $k=1$. The distance between $B$ and $B'$ is four. Their one-site collar components have distance two, so the graph made of the two blocks and collar singletons has no adjacent-block chain between them. Yet at $x=(L,L,L,L)\in B'$ the quadratic spline bump of $B$ is positive: every coordinate of $(x-c(B))/L$ is $1/2+1/(2L)<3/2$. Put distinct real unit vectors on the two disconnected components. Conditions (R1)–(R4) hold with arbitrarily small $\delta$ when $\mu=0$, but $\phi^B-\phi^{B'}$ stays of order one. Thus (A1) and the original globally normalized spline construction fail. In $d>4$ the same example uses opposite corner blocks in all coordinates. This is a counterexample to the **one-site-collar chain assertion**, not to the background-field theorem.

**Lemma 5.3a (the geometry actually used).** The following statements hold with $\varrho\ge4dL$.

1. If a bump of a layer-$m$ block $B$ is positive at $x\in\Lambda_n$, then $|m-n|\le1$. If $x\in C$, only indices $0,1$ can be active.
2. For $n\ge2$, every block $B$ active at $x\in\Lambda_n$ has an adjacent-block chain to $B_x$, entirely inside $\Omega_{n-1}$, of at most
   $R=2dL^2+d+2$ links. A block active at a neighbour $x'$ with $n(x')\ge2$ has a chain of at most $R$ links to $B_{x'}$, followed by at most one link to $B_x$. When $n(x')=1$, the construction uses only $B_{x'}$, which is adjacent to $B_x$. In particular every block actually used at $x$ or a neighbour has local solution within $A\delta$ of $\phi^{B_x}$, where $A=(2R+1)J$.
3. If $x\in\Lambda_n$, $n\ge3$, and a bump of $B$ is nonzero at $x$ or at one of its neighbours, then $m(B)\ge n-1$. Every neighbour of $x\in\Lambda_n$, $n\ge2$, belongs to $\Omega_1$; a neighbour of a layer-one site is in layer one, layer two, or $C$.

*Proof.* Work with lifts of the torus coordinates and the periodically summed bump defined below. Positivity supplies a lift for which $\|x-c(B)\|_\infty<3L^m/2$. Clip each coordinate of $x$ to the lifted cube $B$ to obtain $z\in B$ and a coordinate-monotone nearest-neighbour path from $x$ to $z$ of length at most $2dL^m$. This remains valid when the torus wraps.

If $m\ge n+2$, then $x\notin\Omega_{m-1}$ and $z\in\Omega_m$. Separation at $m-1$ gives $\operatorname{dist}(x,z)>\varrho L^{m-1}\ge4dL^m$, contradicting the path bound. If $m\le n-2$, then $z\notin\Omega_{n-1}$ while $x\in\Omega_n$; separation at $n-1$ gives $\operatorname{dist}(x,z)>\varrho L^{n-1}$, again contradicting $2dL^m$. The indices at the top and bottom where a separation axiom is not available are vacuous. For $x\in C$, the first argument with $n=0$ excludes $m\ge2$; only the collar singleton or a layer-one block remains.

For $n\ge2$ and $m\le n$, every site of the clipping path is within $2dL^n<\varrho L^{n-1}$ of $x\in\Omega_n$, hence lies in $\Omega_{n-1}$. For $m=n+1$, every path site is within $2dL^{n+1}<\varrho L^n$ of $z\in\Omega_{n+1}$, hence lies in $\Omega_n\subseteq\Omega_{n-1}$. Thus no path through the exterior or collar is needed. Each path site belongs to one layer block of index at least $n-1$. The monotone path crosses at most $2dL^2+d+1$ cells of the common grid of side $L^{n-1}$: in coordinate $\mu$ it crosses at most $|x_\mu-z_\mu|/L^{n-1}+1$ grid boundaries, with one initial cell. Each cell is contained in a unique layer block because all relevant block sides are multiples of $L^{n-1}$. Compress only consecutive repetitions in the sequence of blocks visited. Consecutive remaining blocks contain adjacent sites, and their layers differ by at most one: if layers differed by two, that one-bond pair would contradict the separation axiom at the intervening index. This proves the conservative bound $R$.

The preceding path from $x'$ to its active block gives a chain to $B_{x'}$ of length at most $R$ whenever $x'\in\Lambda_{n'}$ with $n'\ge2$. The blocks $B_x,B_{x'}$ contain adjacent sites. For the one case $n=2,n'=1$, only the own block at $x'$ is used in our construction. The bound $A$ covers a chain from any used block to either reference block and then across the bond.

For part 3, $x\in\Omega_n$ and a layer-$m\le n-2$ block lies outside $\Omega_{n-1}$. If its bump is positive at $x\pm e_\mu$, there is $z\in B$ at distance at most $1+2dL^m$ from $x$, whereas separation gives $\operatorname{dist}(x,z)>\varrho L^{n-1}$. Since $n\ge3$, $1+2dL^{n-2}<4dL^n\le\varrho L^{n-1}$, contradiction. The same separation, at index one, shows that a layer-$n\ge2$ site cannot have a neighbour outside $\Omega_1$. A one-step jump from layer one to layer three, or from layer $n$ to $n+2$, contradicts separation at the intervening index. $\square$

The statement about chains at neighbouring sites should be read with the actual construction: layer-one sites use only their own block. No claim is made about all spline-active blocks at an arbitrary layer-one site.

## 3. Spline and quotient estimates: Lemma 5.3b

Put

$$
\beta(t)=
\begin{cases}
3/4-t^2,&|t|\le1/2,\\
\tfrac12(3/2-|t|)^2,&1/2\le|t|\le3/2,\\
0,&|t|\ge3/2.
\end{cases}
$$

This is the cardinal quadratic B-spline: $\beta\ge0$, $\sum_{j\in\mathbb Z}\beta(t-j)=1$, $\beta(t)\ge1/2$ for $|t|\le1/2$, $|\beta'|\le1$, and $\beta'$ is $2$-Lipschitz. To verify the partition, reduce by translation to $0\le t\le1$. For $0\le t\le1/2$, its only nonzero translates are $\beta(t+1),\beta(t),\beta(t-1)$, whose values sum to $(1/4+t^2)+(3/4-t^2)=1$. For $1/2\le t\le1$, use $\beta(t),\beta(t-1),\beta(t-2)$ and expand the same three quadratic formulas. The derivative is continuous at $|t|=1/2,3/2$ and has slope $-2$, $1$, or $0$ on each smooth interval; integrating the derivative difference twice proves $|\beta(t+s)+\beta(t-s)-2\beta(t)|\le2s^2$. **The constant is $2$, not $1$:** at $t=0$ and small $s$, the second difference is $-2s^2$. This corrects the numerical assertion in BACKGROUND.md §5.3.

For each block $B$ of layer $m$ (including collar singletons, $m=0$), with lifted centre $c(B)$ and torus side $S=N_0L^k$, use the periodic bump

$$
b_B(x)=\sum_{p\in\mathbb Z^d}\prod_{\mu=1}^d
\beta\big((\widetilde x_\mu-c_\mu(B)+p_\mu S)/L^m\big).
$$

The sum is finite at each site, independent of the chosen lifts. The periodization matters when a top-scale block wraps around the torus. Set $D(x)=\sum_B b_B(x)$ and $h_B(x)=b_B(x)/D(x)$ where $x\in\Omega_1\cup C$. Let

$$
q=2^{-d},\quad Q=3^d,\quad P=5^d,\quad M=3Q,\quad
U=2MPL,\quad V_D=6MPL^2,
$$

$$
H_1=q^{-1}PL+q^{-2}U,\qquad
H_2=d\big(2q^{-1}PL^2+q^{-2}V_D+2q^{-3}U^2+2q^{-2}PLU\big). \tag{3}
$$

**Lemma 5.3b.** At every $x\in\Omega_1\cup C$, $q\le D(x)\le M$, $h_B(x)\ge0$, $\sum_Bh_B(x)=1$, and at most $M$ blocks have positive bump. For $x\in\Lambda_n$, $n\ge3$, and $e=\pm e_\mu$,

$$
|h_B(x+e)-h_B(x)|\le H_1/\ell(x),\qquad
|\Delta h_B(x)|\le H_2/\ell(x)^2. \tag{4}
$$

*Proof.* The own block's bump is at least $q$: in each coordinate a representative of the site lies within $L^n/2$ of its block centre. On a grid of mesh $L^m$ at most three centres per coordinate have a nonzero $\beta$ factor, so at most $Q$ layer-$m$ blocks are active. Lemma 5.3a(1) leaves at most three layers. Every periodized bump is at most one because its translates are a sub-sum of the complete cardinal partition at that scale. Hence $q\le D\le M$ and the partition properties follow.

At $x$ or $x\pm e_\mu$ with $n\ge3$, an active block has scale $L^m\ge L^{n-1}=\ell/L$, by Lemma 5.3a(3). Along a unit segment, at most five periodic images per coordinate can meet the support of $\beta$: the scaled segment has length at most $1/L^m\le1/9$, while the support interval has length three and the image centres are at integer multiples of $S/L^m\ge1$. The union of both unit segments has scaled length at most $2/9$, so the same bound holds for a centred second difference. Thus at most $P=5^d$ images contribute to a difference of one bump. The mean-value bound and the $2$-Lipschitz bound for $\beta'$ give, even if the bump vanishes at one or two sites,

$$
|b_B(x+e_\mu)-b_B(x)|\le PL/\ell,\qquad
|b_B(x+e_\mu)+b_B(x-e_\mu)-2b_B(x)|\le2PL^2/\ell^2.
$$

The union of supports at two sites has size at most $2M$, and the union at three sites at most $3M$. Thus for each coordinate $\mu$,

$$
|D(x+e_\mu)-D(x)|\le U/\ell,\qquad
|D(x+e_\mu)+D(x-e_\mu)-2D(x)|\le V_D/\ell^2.
$$

Write $r=1/D$. Direct subtraction gives $|r(x+e)-r(x)|\le q^{-2}U/\ell$. The exact centred quotient identity is

$$
r_++r_--2r_0
=-\frac{D_++D_--2D_0}{D_0^2}
+\frac{(D_+-D_0)^2}{D_0^2D_+}
+\frac{(D_--D_0)^2}{D_0^2D_-}.
$$

Its absolute value is at most $(q^{-2}V_D+2q^{-3}U^2)/\ell^2$. Finally,

$$
\begin{aligned}
(br)_+- (br)_0&=(b_+-b_0)r_++b_0(r_+-r_0),\\
(br)_++(br)_--2(br)_0
&=(b_++b_--2b_0)r_0+b_0(r_++r_--2r_0)\\
&\quad +(b_+-b_0)(r_+-r_0)+(b_--b_0)(r_--r_0).
\end{aligned}
$$

Use $0\le b\le1$, sum the second line over $\mu$, and substitute the preceding bounds. This gives exactly (3)–(4). $\square$

No quotient estimate at layer one is needed. The $L$ and $L^2$ losses there are absorbed in the explicit low-layer constants below.

## 4. Construction and Lemma 5.3

For $x\in\Lambda_1$ set $\phi_0(x)=\phi^{B_x}$. For $z\in C$ set $\phi_0(z)=\phi^z$. For $x\in\Lambda_n$, $n\ge2$, set

$$
\widetilde\phi(x)=\sum_Bh_B(x)\phi^B,\qquad
z(x)=\widetilde\phi(x)\cdot\widetilde\phi(x),\qquad
\phi_0(x)=\widetilde\phi(x)/\sqrt{z(x)}. \tag{5}
$$

Extend $\phi_0$ by zero to $T\setminus(\Omega_1\cup C)$; these values are never sampled by the estimates or by $H_D$. Put $\alpha_0=0$ on $\Omega_1$ and $f_0=S(\Psi,\tilde h)-H_D(0)(\phi_0|_{\Omega_1})$.

Define the following explicit constants, depending only on $d,L$:

$$
\begin{gathered}
R=2dL^2+d+2,\quad J=4096,\quad A=(2R+1)J,\quad B=RJ+A,\quad E=2B+J,\\
T_1=2M H_1A,\qquad T_2=(2d+1)M H_2A,\\
C_{\mathrm{grad}}=\max\{EL^2,\;16T_1\},\\
C_{\mathrm{lap}}=\max\{2dEL^4,\;16T_2+200dT_1^2\},\\
C_{\mathrm{data}}=B+1695,\quad
C_{\mathrm{res}}=3B+544+C_{\mathrm{lap}}+6dL^2,\quad
C_{\mathrm{mass}}=2048L+A,\\
C_3=\max\{C_{\mathrm{grad}},C_{\mathrm{lap}},C_{\mathrm{data}},
C_{\mathrm{res}},C_{\mathrm{mass}},2B+3391\},\qquad
\delta_{**}=\min\{2^{-20},(100A)^{-1}\}.
\end{gathered} \tag{6}
$$

These are intentionally generous. No constant depends on $k,N_0,\varrho,\mu$, or the generating set. The same functions of $(d,L,N)$ may be used by regarding them as constant in $N$.

**Lemma 5.3 (hard-spin approximate solution).** Under the assumptions of §1, with $\delta\le\delta_{**}$, the field (5) and $\alpha_0=0$ satisfy:

* $\phi_0(x)\cdot\phi_0(x)=1$ on $\Omega_1\cup C$ and $|\phi_0(x)-\Psi(x)|\le C_3\delta$ on $\Omega_1\cup C$;
* IsSmoothField $G\ (C_3\delta)\ \phi_0$, that is $|\phi_0(x\pm e_\mu)-\phi_0(x)|\le C_3\delta/\ell(x)$ and $|\Delta\phi_0(x)|\le C_3\delta/\ell(x)^2$ for every $x\in\Omega_1$;
* $\ell(x)^2|f_0(x)|\le C_3\delta$ for every $x\in\Omega_1$;
* $(\phi_0,f_0)$ depend analytically on the complex data domain and are real for real data;
* for the corresponding real and complex data, $|\phi_0^{\mathrm c}(x)-\phi_0^{\mathrm r}(x)|\le\varepsilon+C_3\delta$ on $\Omega_1\cup C$;
* for real data, $\sqrt\mu\,|\phi_0(x)-h|\le C_3\delta/\ell(x)$ on $\Omega_1$.

*Proof, (A1) local closeness.* Lemma 5.3a(2) and (2) give $|\phi^B-\phi^{B_x}|\le RJ\delta$ for every block active at $x\in\Lambda_n$, $n\ge2$. For blocks used at $x$ and $x\pm e_\mu$ with $n\ge3$, their distance to the common reference $\phi^{B_x}$ is at most $A\delta$. For a bond involving layer one, the layer-one endpoint uses just its own block, and the layer-two endpoint's active blocks have the preceding chain to its own block. This is the precise replacement for the false all-layer chain assertion.

*Proof, (A2) exact normalization.* At $x\in\Lambda_n$, $n\ge2$, the $h_B$ are nonnegative and sum to one. Since each $\phi^B\cdot\phi^B=1$,

$$
z(x)=1-\frac12\sum_{B,B'}h_B(x)h_{B'}(x)
(\phi^B-\phi^{B'})\cdot(\phi^B-\phi^{B'}).
$$

The pairwise difference is at most $2RJ\delta\le A\delta$, so $|z-1|\le A^2\delta^2/2\le1/20000$. Thus $\operatorname{Re}z>1/2$, the principal square root is defined, and $\phi_0\cdot\phi_0=1$. Also $|\widetilde\phi|\le2$ and
$|\phi_0-\widetilde\phi|\le2|\widetilde\phi||z-1|\le2A^2\delta^2\le A\delta$. Consequently

$$
|\phi_0(x)-\phi^{B_x}|\le B\delta \quad(n(x)\ge2). \tag{7}
$$

At layer one and on $C$ the bilinear unit norm holds directly by (1) and the collar definition.

*Proof, (A3) differences.* First consider $x\in\Lambda_n$, $n\ge3$. By $\sum_Bh_B=1$, both $\sum_B(h_B(x+e)-h_B(x))$ and $\sum_B\Delta h_B(x)$ vanish. Subtract the constant vector $\phi^{B_x}$ inside each sum. Lemma 5.3b, the support counts $2M$ and $(2d+1)M$, and (A1) give

$$
|\widetilde\phi(x+e)-\widetilde\phi(x)|\le T_1\delta/\ell(x),\qquad
|\Delta\widetilde\phi(x)|\le T_2\delta/\ell(x)^2. \tag{8}
$$

For clarity about normalization, let $F(v)=v/\sqrt{v\cdot v}$. On every line segment from $\widetilde\phi(x)$ to either $\widetilde\phi(x\pm e_\mu)$, all vectors lie within $A\delta\le1/100$ of the same bilinear unit vector $\phi^{B_x}$. Both endpoints have norm at most two as convex averages of local solutions, so convexity gives $|v|\le2$ throughout. Also $|v\cdot v-1|\le 2|\phi^{B_x}|A\delta+(A\delta)^2\le401/10000<1/2$, so $\operatorname{Re}(v\cdot v)>1/2$ throughout. Direct differentiation gives

$$
DF(v)h=(v\cdot v)^{-1/2}h-(v\cdot v)^{-3/2}v(v\cdot h)
$$

and

$$
D^2F(v)[h,k]=-(v\cdot v)^{-3/2}
\{(v\cdot k)h+(v\cdot h)k+(h\cdot k)v\}
+3(v\cdot v)^{-5/2}v(v\cdot h)(v\cdot k).
$$

The displayed conditions imply $\|DF\|\le16$ and $\|D^2F\|\le200$ by Cauchy–Schwarz. Taylor's formula with integral remainder gives, for each sign,
$F(v_\pm)=F(v_0)+DF(v_0)(v_\pm-v_0)+R_\pm$ with
$|R_\pm|\le100|v_\pm-v_0|^2$. Thus the **vector identity** for each $\mu$ is

$$
F(v_+)+F(v_-)-2F(v_0)
=DF(v_0)(v_++v_--2v_0)+R_++R_-,
\qquad
|R_\pm|\le100|v_\pm-v_0|^2.
$$

Apply this with $v_\pm=\widetilde\phi(x\pm e_\mu)$ and sum the **identities before taking norms**. The linear terms combine to $DF(v_0)\Delta\widetilde\phi(x)$, so (8), the $2d$ remainder bounds, and $\delta\le1$ give

$$
|\phi_0(x+e)-\phi_0(x)|\le16T_1\delta/\ell,\qquad
|\Delta\phi_0(x)|\le(16T_2+200dT_1^2)\delta/\ell^2. \tag{9}
$$

If $x\in\Lambda_1\cup\Lambda_2$, each neighbour lies in a layer whose own block is adjacent to $B_x$, or in $C$ when $n(x)=1$. Equation (7), the layer-one definition, and (2) imply $|\phi_0(x+e)-\phi_0(x)|\le E\delta$. Hence $|\Delta\phi_0(x)|\le2dE\delta$. Since $\ell=L$ or $L^2$, respectively, these are bounded by $EL^2\delta/\ell$ and $2dEL^4\delta/\ell^2$. This covers both signs and every wall bond. Combining with (9) proves IsSmoothField with the constants in (6).

*Proof, (A4) data.* At $x\in\Lambda_n$, $n\ge2$, (7) and (2) give $|\phi_0(x)-\Psi_{B_x}|\le(B+1695)\delta$. At layer one (2) gives $1695\delta$. On $C$, direct normalization gives $3\delta$. These prove the first bound of the lemma.

*Proof, (A5) residual.* Fix $x\in\Lambda_n$, $B=B_x$, and write $\bar\phi_0$ for the field equal to $\phi_0$ on $\Omega_1\cup C$. The identity between the zero-extension Laplacian and the collar extension, equation (1), and the source (BACKGROUND.md (1.1)) give the exact formula

$$
f_0(x)=a_nL^{-2n}\big(\phi^B-Q_n\phi_0(B)\big)
+\mu\big(\phi^B-\phi_0(x)\big)
+\alpha^B\phi^B+\Delta\bar\phi_0(x)
+\sum_{\substack{z\in C\\z\sim x}}\big(\Psi_z-\phi_0(z)\big). \tag{10}
$$

The average $Q_n$ is over sites of $B$, all in layer $n$, so (7) (or equality at $n=1$) bounds its first difference by $B\delta$. After multiplication by $\ell(x)^2=L^{2n}$, the five terms in (10) are bounded respectively by $2B\delta$, $B\delta$ using $\mu\ell^2\le1$, $544\delta$ using $|\widehat\alpha^B|\le272\delta$ and $|\phi^B|\le2$, $C_{\mathrm{lap}}\delta$, and $6dL^2\delta$. The last term is supported only at layer-one wall sites: separation at index one puts every site adjacent to $C$ outside $\Omega_2$, and there are at most $2d$ such neighbours, each with $|\Psi_z-\phi_0(z)|\le3\delta$. This proves $|f_0|_2\le C_{\mathrm{res}}\delta$.

*Proof, (A6) remaining assertions.* All local $w_B\cdot w_B$ have positive real part by §1, and all $z(x)$ have positive real part by (A2). The local maps, finite sums, fixed coefficients, and principal roots are analytic on the given open complex data domain. For real data their arguments are positive real, so $\phi_0$ and $f_0$ are real.

At a fixed block $B$, the real and complex data differ by at most $\varepsilon+\delta$ in $\Psi_B$; (2) for each data set gives
$|\phi^{B,\mathrm c}-\phi^{B,\mathrm r}|\le\varepsilon+3391\delta$. For the approximate field, a sharper coefficient-one estimate follows by comparing each field to its *own block datum*: (A4) gives
$|\phi_0^{\mathrm c}(x)-\phi_0^{\mathrm r}(x)|
\le\varepsilon+\delta+2C_{\mathrm{data}}\delta$, including the collar. This is covered by the final entry in the maximum defining $C_3$ because $2C_{\mathrm{data}}+1=2B+3391$.

For real data and $x\in\Lambda_n$, $n\ge2$, every active block has $m\ge n-1$ by Lemma 5.3a(1). The local real estimate in §1 gives
$\sqrt\mu|\phi^B-h|\le2048\delta/L^m\le2048L\delta/\ell(x)$.
Average with $h_B$, then add the normalization error:
$\sqrt\mu|\phi_0-\widetilde\phi|\le A\delta/\ell(x)$ because $\sqrt\mu\,\ell(x)\le1$. At layer one, the local estimate gives $2048\delta/L$. This proves the last bound with $C_{\mathrm{mass}}$. $\square$

## 5. Why multilinear interpolation does not save the second-difference proof

Even on a uniform lattice of spacing $s=L^n$, multilinear interpolation of block values has a kink at every coarse-grid hyperplane. In one dimension take consecutive values $v_{-1}=v_0=0$ and $v_1=\delta$. At the knot $0$, the interpolant satisfies $f(-1)=f(0)=0$ and $f(1)=\delta/s$, hence $\Delta f(0)=\delta/s$. The needed bound is $C(d,L)\delta/s^2$, uniformly in $n$; their ratio is $s=L^n$, unbounded as $n$ grows. For hard spins, replace scalar values by $(\cos f,\sin f)$: the second coordinate of the centered second difference is $\sin(\delta/s)$, so normalizing the vector does not fix the kink. This failure occurs on a **single-scale interior grid line**, away from any layer interface. A correction supported only near interfaces cannot repair it. Smoothing every coarse-grid hyperplane over distance comparable with $s$ would repair it, but that is a global $C^{1,1}$ interpolation and requires the same bump, quotient, and geometry estimates as the spline method. The layer-one replacement above is cheaper than an interface correction: one fixed-scale layer is handled by the allowable $L^2$ and $L^4$ constants, while higher layers keep the spline estimates. As a Lean estimate, the scalar spline and torus geometry package still costs roughly the 1,500–2,000 lines budgeted in BACKGROUND.md §9; multilinear interpolation plus smoothing at every grid line has no smaller lemma inventory and likely costs at least as much. Bare multilinear interpolation cannot be used.

## 6. Lean lemma order and dependencies

These are proof obligations, not new hypotheses to add to a frozen statement. They should be proved in this order.

1. **Block geometry:** layerBlock_of_mem, layerBlock_subset_layer, block_grid_refines, torus_clip_path, torus_clip_length_le, monotone_path_base_cells_le. Inputs: jBlock, blockUnion, torusDist.
2. **Separation consequences:** layer_jump_le_one_on_bond, wall_site_layer_one, no_exterior_neighbour_of_layer_ge_two, support_layer_gap_le_one, support_near_high_layer_ge_pred. Inputs: GeneratingSet.separation and item 1.
3. **High-layer chain:** active_block_chain_to_own with length $R$ for $n\ge2$; used_block_chain_neighbour with length $R+1$; adjacent_block_data_le and adjacent_const_solution_le with $J$. Inputs: items 1–2 and (R1), (C1), local estimate (2). Do not state a chain at layer one for all spline-active blocks.
4. **Local complex solution:** local_data_norm_bounds, local_mass_data_le, local_blend_near_unit, local_solution_near_data, local_multiplier_bound, local_real_mass_bound, collar_normalized_bounds. Inputs: (R2)–(R4), (C2)–(C3), cMinimizer/cMultiplier formulas and vn/norm_dot_le. Numerical target: (2).
5. **Periodic B-spline:** beta_nonneg, beta_partition, beta_lower_centre, beta_derivative_le, beta_second_difference_le_two, periodized_bump_support_count, bump_lower_own, bump_first_difference, bump_centre_second_difference. Inputs: elementary real calculus and item 1.
6. **Quotient:** denominator_lower_upper, denominator_first_difference, denominator_second_difference, reciprocal_centre_identity, normalized_weight_first_difference, normalized_weight_lap_bound. Inputs: items 2, 5; constants (3)–(4).
7. **Interpolation:** used_local_values_close, convex_bilinear_variance_identity, interpolation_square_near_one, interpolation_near_own, normalization_derivative_bounds, interpolation_high_grad_lap, interpolation_low_grad_lap. Inputs: items 3, 4, 6.
8. **Approximate solution:** approx_constraint, approx_data, approx_isSmoothField, source_dirichlet_collar_identity, approx_residual_identity (10), approx_residual_bound, approx_analytic, approx_complex_real_difference, approx_real_mass_bound. Inputs: item 7 and landed operator/source definitions. Then assemble Lemma 5.3.

The exact Lean interfaces matter: use GeneratingSet.layerIndex and spacing rather than a new layer convention; IsSmoothField.grad has both $+e_\mu$ and $-e_\mu$ at the spacing of $x$; IsSmoothField.lap uses the centred sum; vn is the Euclidean norm on Fin $N\to\mathbb C$; PathCost lies in $\Omega_1$ and must not be used to justify collar paths. The block adjacency relation and periodic bump are new definitions local to the interpolation module. For analytic assertions use the landed analyticOnNhd_cMinimizer after proving the explicit local domain inclusion from §1.

## 7. Confidence and remaining integration work

The counterexample to the draft one-site-collar chain is decisive. The replacement proof is high confidence as a paper argument: all estimates reduce to finite block geometry, the stated scalar spline inequalities, and the explicit local solution formula. The largest Lean burden is the torus clipping path and its base-grid cell count, followed by the analytic-domain bridge for the local solution at the allowed endpoint $a=1/2$. This document does not claim that the current Lean tree already has those lemmas; no Lean file was changed or compiled. The constants are deliberately large, and the domain explicitly requires $\varepsilon\le1/16$, as in the small-$\varepsilon$ regime of P2 Lemma 3.1.
