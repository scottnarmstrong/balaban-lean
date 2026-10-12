# Y-locality after the landed I-5 construction

**Status, 12 October 2026.** This note answers the requested Y-localization follow-up. The set-theoretic locality implication and the rate algebra below are **PROVED**. The requested geometric estimate with coefficient $L^{-1}$ for a completion containing the collars is **FALSE**, including for the all-contained-cubes size of P1. Consequently a complete proof of `OPEN-I5-Y-LOCAL`, `OPEN-PAPER-DOMAIN`, or `OPEN-PHYSICAL-HAT-LOCAL` cannot be supplied from the landed declarations. The precise replacement inputs and their consumers are recorded below. In particular, none of the conditional statements below is a claim that the paper's physical localization has been formalized.

## 1. The landed sets and the necessary completion

Write $K=k+1$, $a_n=L^{n+m_0+m_1}$, and $a=a_K$. For the parameter index $i:\mathrm{ParIdx}(G_p,X_1)$, put $q_i=i.1.1$, $P_i=\mathrm{Pset}(m_1,q_i)$, and $D_i=\mathrm{Dsites}(G_p,m_0,q_i)$. The old cover is $\mathcal K_X$; `TreeLengthCov.Q0` consists of all $\pi'_K$ cubes in the top layer that contain a cube of $\mathcal K_X$, and `X1` is their union. For a connected marked family $C$, the mark-indexed component and its current localization domain are exactly

$$
Y_1(C)=\operatorname{compY}(q,X_1,C)
 =\operatorname{component}_{X_1}\bigl(X_1\cup\textstyle\bigcup_{i\in C}P_i\bigr),
\qquad
Y(C)=\operatorname{Ysites}(G_p,m_0,q,X_1,C)
 =X_1\cup\textstyle\bigcup_{i\in C}D_i.
\tag{1}
$$

These are definitions in `Localization/PolymerGeometry.lean:421,426`; `Pset_subset_Dsites` and `patchUnion_subset_Ysites` give $Y_1(C)\subset Y(C)$. `TreeLengthCov.gm2` proves

$$
T(Y(C))\le L^{-1}x+D|C|,
\quad x=d^{\rm cov}_j(X),\quad
D=d(2L+1)^d,\quad T=\operatorname{treeLenCov}(G_p,m_0,\cdot).
\tag{2}
$$

**PROVED from landed definitions.** The background dependency is `I5Local.thickSet`:
$\operatorname{thickSet}_{G_p}(S)=S\cup\bigcup_{x\in S\cap\Omega_1}\operatorname{resDep}_{G_p}(x)$.
Here `DecoupledBackgroundLocal.resDep` contains active approximation sites around $x$, its block, and its nearest neighbours; it is not generally the one-site collar. The fluctuation dependency is `I5FluctLocal.psiThick`:
$\operatorname{psiThick}(S)=S\cup\{y: y\sim x\text{ for some }x\in S\}$.
For the composed square root, `HatEngineLocal.blockThick` contains every site in a $K$-unit block meeting `psiThick S`. The order is

$$
S\subset\operatorname{psiThick}(S)\subset\operatorname{blockThick}(S),
\qquad S\subset\operatorname{thickSet}_{G_p}(S).
\tag{3}
$$

The first two inclusions are immediate from definitions and `psiThick_subset_blockThick`. No inclusion between `thickSet` and `blockThick` is landed or valid without an extra range hypothesis.

A completion usable directly with `fan_local_fl` needs the required set

$$
R_C^{(1)}=Y(C)\cup\operatorname{thickSet}_{G_p}(Y_1(C))
                 \cup\operatorname{blockThick}(Y_1(C)).
\tag{4}
$$

To use the *already summed* conclusion of `i5_fluct` without reopening its coefficient proof, the stronger required set is

$$
R_C^{(2)}=Y(C)\cup\operatorname{thickSet}_{G_p}(Y(C))
                 \cup\operatorname{blockThick}(Y(C)).
\tag{5}
$$

The difference matters: (4) is the raw dependency of the coefficient indexed by $C$; (5) is the agreement set actually asserted by the landed fixed-$Y$ theorem. Since $Y_1(C)\subset Y(C)$, monotonicity gives $R_C^{(1)}\subset R_C^{(2)}$. The completion below works with (5), so it also works with (4).

Here is a fully specified *set-theoretic* completion. Let $\mathcal B_K$ be all aligned $\pi'_K$ cube bases on the finite torus, with site sets $Q_b=\operatorname{box}(b,L a)$. Form the finite family of all $Q_b$ meeting $R_C^{(2)}$. Add shortest chains of face-adjacent $\pi'_K$ cubes from each component of their union to a cube in $X_1$; select a shortest chain by a fixed total order of cube bases. Let $Y^\#(C)$ be the union. If a layer-restricted domain is required, perform the construction in the graph of *admissible layer cubes*; existence of the required chains there is an additional input, called `OPEN-LAYER-COMPLETION`. In the unrestricted top-layer example below, all cubes are admissible.

The cubes attached to the old polymer are exactly those meeting
$R_0=X_1\cup\operatorname{thickSet}(X_1)\cup\operatorname{blockThick}(X_1)$.
For a mark $i$, a sufficient attached family is all cubes meeting
$R_i=D_i\cup\operatorname{thickSet}(D_i)\cup\operatorname{blockThick}(D_i)$.
Indeed, $Y(C)=X_1\cup\bigcup_{i\in C}D_i$, and `thickSet`, `psiThick`, and `blockThick` preserve finite unions directly from their definitions. The connecting chains are attached to the relevant components. This allocation identifies the unmarked cost $R_0$; no part of $R_0\setminus X_1$ is paid by $|C|$ when $C=\varnothing$.

**PROVED (set theory).** On a finite connected torus, $Y^\#(C)$ is nonempty, connected, and a union of aligned $\pi'_K$ cubes, hence `Fluctuation.IsDj m₀ K` in the unrestricted domain. Each required set in (5) is contained in $Y^\#(C)$. A site in a required set lies in some aligned cube; that cube is included by the rule “meeting $R_C^{(2)}$.” The added cube chains connect every component to $X_1$. For a layer domain, this is **PROVED CONDITIONAL ON `OPEN-LAYER-COMPLETION`**, since unrestricted chains can leave the layer. The construction is intentionally generous; taking a smaller deterministic connected cube cover does not cure the counterexample in §2.

**PROVED CONDITIONAL ON using the landed `i5_fluct` or `fan_local_fl` hypotheses.** If two raw data agree on $Y^\#(C)$, they agree on `thickSet (Y(C))`, and if two fluctuation fields agree on $Y^\#(C)$, they agree on `psiThick (Y(C))`. Thus `i5_fluct` gives equality of its $Y(C)$ term. Alternatively, (4) supplies the two agreement hypotheses of `fan_local_fl` for the unsummed coefficient. If two hat fields agree at unit points whose blocks lie in $Y^\#(C)$, the inclusion `blockThick (Y₁(C)) ⊂ Y#(C)` supplies the `hh` hypothesis of `hatPsiF_local`. This is a restriction argument, not a new analytic or geometric estimate.

## 2. The demanded $L^{-1}$ estimate fails

**PROVED counterexample (lattice geometry).** The failure already occurs with no marks, a single top layer, and $K=j+1$. Take the torus much larger than all lengths below, so no shortest connecting network wraps around it. Choose $a=a_K=L a_j\ge32$, a separation $S\ge 8L+8$, and $n\ge4$. In the first two coordinates construct the old connected polymer $X$ from a row of old $\pi'_j$ *cells* of side $a$ at height $0\le y<a$, extending from $x=0$ to $x=(n-1)Sa+a-1$, and one additional cell at height $a\le y<2a$ above each $x_i=iSa$, $0\le i<n$. Give the third coordinate one old cell of thickness $a$; higher coordinates, if any, are analogous. This is a comb with widely spaced one-cell teeth. Its only possible old aligned-cube cover consists of its constituent $a$-cells, so it satisfies the chosen-cover condition. A nearest-neighbour graph along $y=a-1$, with one vertical bond into each tooth, meets every cover cell. Consequently

$$
L^{-1}d^{\rm cov}_j(X)
 \le (n-1)S+n/a+O(1/a).
\tag{6}
$$

For every tooth $x_i$, `Q0` includes a coarse cube of side $La$ containing the spine cell with bottom site $u_i=(x_i,-(L-1)a,0)$. It also includes a coarse cube containing the tooth cell with top site $v_i=(x_i,(L+1)a-1,0)$. Therefore every completion containing `psiThick X1` contains $u_i$ and $v_i+e_y=(x_i,(L+1)a,0)$. A coarse aligned cube covering $u_i$ has upper $y$-coordinate at most $a-1$; a coarse aligned cube covering $v_i+e_y$ has lower $y$-coordinate at least $2a$. Their vertical separation is at least $a+1$. Their possible $x$-coordinates lie in windows of width at most $2La$ about $x_i$, and these windows are disjoint by the choice of $S$.

We use the following elementary **strip bound** for rectilinear networks. If a connected nearest-neighbour network meets, in each of $n$ disjoint strips centered $Sa$ apart, one lower window and one upper window of horizontal width $2La$, with vertical gap at least $a$, then, for $S\ge8L+8$, its number of bonds is at least

$$
(n-1)Sa-2La+\tfrac18(n-1)a.
\tag{7}
$$

Here is a cut proof of (7). Fix the points where the network meets the $2n$ terminal windows, discard other requirements, and minimize the number of bonds among connecting rectilinear trees for these points. One may take a minimizing tree whose Steiner vertices have $x$ coordinates among the terminal $x$ coordinates: for each maximal connected portion lying in an open interval between consecutive terminal $x$ coordinates, translate its vertical edges together horizontally; its total horizontal length is piecewise affine in the translation, so an endpoint translation does not increase length. Repeating removes all Steiner $x$ coordinates in the empty gaps. This is the elementary rectilinear grid reduction. Thus every horizontal branch crossing a gap between consecutive terminal windows traverses its whole width, at least $(S-2L)a$. Let $r$ of the $n-1$ gaps have at least two such branches. The horizontal projection from the first to the last window costs at least $(n-1)Sa-2La$, and the doubled gaps add at least $r(S-2L)a\ge ra$ disjoint horizontal bonds. At an interior tooth whose adjacent gaps both have just one crossing branch, the unique tree path between its lower and upper terminal points stays in its tooth strip: leaving and returning would require two crossings of one boundary gap, while leaving through one gap and returning through the other would force a path around the torus. It therefore contributes at least $a$ vertical bonds inside that strip. There are at least $\max(0,n-2-2r)$ such teeth, and their vertical charges are disjoint. Hence the excess over the horizontal projection is at least $a[r+\max(0,n-2-2r)]\ge a(n-2)/2\ge a(n-1)/8$ for $n\ge4$. A wrapping tree is longer than this bound by the choice of torus circumference. This proves (7).

Every chosen covering family for a completion $Z\supset\operatorname{psiThick}(X_1)$ must contain a coarse cube covering each of the two displayed sites at each tooth. A connected structure meeting that family meets the lower and upper windows, so (7), divided by $a$, yields

$$
d^{\rm cov}_K(Z)\ge(n-1)S-2L+\tfrac18(n-1).
\tag{8}
$$

The bound is valid for P1's all-contained-cubes size as well: that family also contains cubes covering the displayed sites, so it imposes at least the same meeting requirements. Comparison of (6) and (8), followed by $n\to\infty$ with $a\ge32$, rules out

$$
d_K(Z)\le L^{-1}d_j(X)+b
\quad\text{with a constant }b\text{ independent of }X,
\tag{9}
$$

for **every** rule $Z\supset\operatorname{psiThick}(X_1)$. Thus a cover-equivalence theorem cannot restore (9). The obstruction is the collar of the old polymer, already at $C=\varnothing$. It is not a defect of `gm2`; `gm2` says (2) for the original $Y(C)$, without the added collar.

**PROVED upper bound available now.** `Fluctuation/HatLabelsGeom.thick_spec` constructs, for an `IsDj` domain $Y$, a domain $Z$ containing the $a_K$-cell of every site in `psiThick Y`, with

$$
d^{\rm cov}_K(Z)\le A\,d^{\rm cov}_K(Y)+B,
\qquad B=2^d c_1(d,L)c_G(d,L),\quad A=1+B.
\tag{10}
$$

Here $c_1(d,L)=[3(2L-1)]^d$, $c_G(d,L)=2dL$. At $d=L=3$, $B=486000$ and $A=486001$. In the single top-layer case, `bondW_of_layer` identifies the mixed weight with the scale-$K$ weight, so combining (10) with (2) gives the *available* coefficient $A/L=162000+1/3$ on $x$ before also paying `thickSet`. No mixed-layer comparison is asserted here. It does not yield the needed exponent split. The $a_K$-cell inclusion implies the corresponding $K$-unit block inclusion when the unit block divides $a_K$; this simple divisibility step has not been packaged as a landed declaration. No comparable landed bound for `thickSet Y` was found.

## 3. Correct rate algebra and the missing fixed-domain counting

Let a proposed completion satisfy a *different*, explicitly quantified geometric input

$$
\tag{GM2^\#}
T(Y^\#(C))\le qx+D^\#|C|+b^\#,
\quad 0\le q<\tfrac12,
\quad D^\#,b^\#\ge0.
$$

The comb disproves `OPEN-GM2#` with $q=1/L$ and a constant $b^\#$, but it does not exclude every $q<1/2$. For $d=L=3$, the comb only forces $q>1/3$ in the large-polymer limit; a useful sharp bound would need a separate geometric proof, including the `thickSet` range and mixed-layer admissibility.

**PROVED exponent calculation, conditional only on `OPEN-GM2#`.** If

$$
\kappa_{\rm dec}(1-2q)\ge\kappa_0+1,
\qquad \kappa_{\rm AE}\ge4\kappa_{\rm dec}D^\#,
\tag{11}
$$

then for $c=|C|$,

$$
(\kappa_{\rm AE}-1)c+(\kappa_{\rm dec}-1)x
\ge(\kappa_{\rm AE}/2-1)c+\kappa_0x
       +2\kappa_{\rm dec}T(Y^\#(C))-2\kappa_{\rm dec}b^\#.
\tag{12}
$$

Indeed, subtract the right side, use `OPEN-GM2#`, and obtain the sum of two nonnegative terms
$$
[\kappa_{\rm dec}-1-\kappa_0-2\kappa_{\rm dec}q]x
 +[\kappa_{\rm AE}/2-2\kappa_{\rm dec}D^\#]c.
$$
Thus the termwise prefactor is enlarged by $e^{2\kappa_{\rm dec}b^\#}$. The original `PolymerCount.gm4` proves (12) only with $Y(C)$, $q=L^{-1}$, $D^\#=D$, and $b^\#=0$.

Fixed-$Y^\#$ summation needs another input:

$$
\tag{GM3^\#}
\sum_{C:Y^\#(C)=Z}\exp[-(\kappa_{\rm AE}/2-1)|C|]\le K_\#
\quad\text{uniformly in }Z.
$$

With `OPEN-GM2#`, `OPEN-GM3#`, and the termwise analytic bound of `localization_expansion`, the triangle inequality gives the fixed-$Z$ bound

$$
\|E_Z^\#\|\le K_\# E_b e^{2\kappa_{\rm dec}b^\#}
e^{-\kappa_0x-2\kappa_{\rm dec}T(Z)}.
\tag{13}
$$

The finite reindexing is **PROVED**: if $F_C$ denotes the coefficient produced before the fixed-domain sum in `I5Expansion`, define $E_Z^\#=\sum_{C:Y^\#(C)=Z}F_C$. Each connected marked family occurs in exactly one fiber, hence $\sum_Z E_Z^\#=\sum_C F_C$ by partitioning a finite sum. The same finite-sum argument preserves global analyticity. Formula (13) is **PROVED CONDITIONAL ON `OPEN-GM2#`, `OPEN-GM3#`, and the termwise analytic bound**. The landed `I5Expansion.gm3_fam` counts fibers of the exact map $C\mapsto Y(C)$, not fibers of $C\mapsto Y^\#(C)$. In particular, the old `gm3_fam` cannot simply be cited for `OPEN-GM3#`. If an unmarked completion and a marked completion coincide, their two strictly positive entropy weights already give a fiber sum greater than one; the old sharp constant $K_\#=1$ can then fail. A finite $K_\#$ independent of the polymer and volume is itself open.

## 4. The complex domain that must precede Cauchy differentiation

P3 pp. 78–79, (4.44)–(4.47), first forms $Y$, then its generating set $\mathcal B_{k+1}(Y)$, replaces the exterior generating set using locality in $Y_1$, and only then applies Cauchy circles in the marks. P6 pp. 29–32, (4.18)–(4.28), uses this for the physical old-energy and source terms and obtains rate $2\kappa_{\rm dec}-1$.

The landed complex sets are `I5Chain.XiCRaw Gp … K 1 eps`, `I5FluctFan.FlBallLC Hm δ₁` and `InteractionHatF.hatBall cψ`. The mark polydisc in `I5Expansion.localization_expansion` has radius $e^{\kappa_{\rm AE}}$. The hatted locality theorem `hatPsiF_local` additionally requires

$$
\operatorname{decDomMargin}(d,L,N,BG,\kappa,\xi_{C1}(d)\epsilon)<\delta_c,
\quad K_4(d,L,N,BG,\kappa)\xi_{C1}(d)\epsilon<\tfrac12\operatorname{coerciveConst}(d),
\quad \delta_c^2\operatorname{smallConstX}(d,L,\kappa)\le\tfrac14,
\tag{14}
$$

as well as its displayed `hMX`, `hF₁`, positivity and background-domain assumptions. The physical assembly `interaction_expansion_hat` also assumes $R_1>1$, $r>0$, $c_\psi\ge0$, and the strict fluctuation inclusion $\sqrt N\,|cc|\,\operatorname{covSupConstC}(d,L,N,\operatorname{compWeight}(L,a_1,k),\kappa)c_\psi<\delta_1$ (`hδ₁`), together with its potential radius $R\ge2$, $R\delta_1\le\operatorname{deltaStar}$, and the other displayed smallness inequalities. These are not consequences of (14). Here the landed $\xi_{C1}(d)=(4d+8)(2d+1)$. The `FlBallLC` condition includes `IsLayerConstant`; the appropriate complex neighbourhood is relative to that closed linear subspace, with strict radius $\delta_1$. The hat neighbourhood uses strict radius $c_\psi$. The closed rays in `HatRays` must sit inside these open balls with a positive margin before any Cauchy estimate is applied.

**OPEN-PAPER-DOMAIN.** For each admissible completed $Z$, define a local generating set $G_p[Z]$ by the P3 rule: intersect each old layer with $Z$, then add the prescribed $M_1L^n$-cube boundary layers, so $G_p[Z]\preceq G_p$ and the generating-set data agree on the original coefficient's $Y_1(C)\subset Z$. Its exact landed type and extension map have not been defined. The required statement is an open local chart

$$
\iota_Z:\Xi^c_K(G_p[Z];1,\epsilon')\times
 \{\psi':\|\psi'\|<\delta_1,\ \psi'\text{ layer constant}\}
 \longrightarrow
 \Xi^c_K(G_p;1,\epsilon)\times\mathrm{FlBallLC}(H_m,\delta_1),
\tag{15}
$$

with $\epsilon'<\epsilon$, preservation of the data on $Z$, and an open neighbourhood of every closed Cauchy circle $|s_i|=e^{\kappa_{\rm AE}}$ on which the composite is analytic and has the uniform decoupled bound. The domain inclusion in (15), the exterior freezing and its independence of the particular $Y_1(C)$ are the missing assertions. `i5_fluct` proves global `AnalyticOnNhd` on its stated product domain; that fact alone neither constructs (15) nor permits arbitrary replacement of the global generating set. **PROVED CONDITIONAL ON `OPEN-PAPER-DOMAIN`:** composition with the analytic chart gives analytic local terms, finite differentiation and integration preserve analyticity, and the Cauchy formula bounds each marked derivative by its circle supremum times $e^{-\kappa_{\rm AE}}$. This uses strictly interior circles or a radius larger than the target circle; a pointwise bound only on a closed boundary is insufficient.

## 5. Physical hat terms: exact locality implication and limit

`HatEngineLocal.hatPsiF_local` uses `hatSqrtF_local`, which uses `Localization/DecoupledCovLocal2Free.I4c_local_sqrt3` for the composed covariance square root. Its hypotheses are: equal decoupling parameters on marks whose patches meet the component; equal raw background data at `resDep` of every active site of $Y_1(C)$; equal hat fields on `blockThick(Y₁(C))`; and the numerical and analytic conditions displayed in that theorem. The inclusion (4) gives the raw and hat agreement conditions. Applying `hatPsiF_local` gives equality of the produced $\psi'$ on `psiThick(Y₁(C))`; then `I5FluctLocal.fan_local_fl` gives equality of the I-5 underintegral term. This implication is **PROVED CONDITIONAL ON the stated landed theorem hypotheses**. The two square-root backgrounds must separately satisfy `I4c_local_sqrt3`; mere equality of hat fields is not enough.

For the already assembled physical terms, the landed component results are `InteractionHatV.vblock_locInt_hat` for potential blocks, `InteractionHatE.eterm_locInt_hat` for old energy terms, `InteractionHatF.fsite_locInt_hat` for source sites, and `InteractionHatNu.nupart_locInt_hat` for observable terms. `InteractionHatAssemble.hat_vpart_bound`, `hat_eparts_bound`, `hat_fparts_bound`, `hat_mparts_bound`, `interaction_expansion_hat_bound`, and `interaction_expansion_hat` combine their bounds and identities. Their locality interface is `InteractionHatV.AgHatF Y`, namely equality at unit points in `blockThick Y`, together with raw agreement on `thickSet Y`. Therefore (5), rather than only (4), is the safe inclusion for using these statements as landed. Agreement on the block variables indexed by $Y^\#$ then restricts to their required agreement sets: a whole $K$-unit block meeting `psiThick Y` belongs to `blockThick Y`, hence lies in $Y^\#$; since its side divides $a_K$, its containing $a_K$-cell is contained in $Y^\#$ by the `IsDj` cube-union property, and so is in `blocksOf m₀ K Set.univ Y#`. This is the finite block-factorization step required by `LabelAct.dep`; it is **PROVED from the cube definitions**, with the divisibility relation used as an explicit hypothesis in a Lean declaration. The observable $M$ part is handled in `InteractionHatE` and the assembly file; there is no claimed `InteractionHatM.lean` file.

**OPEN-PHYSICAL-HAT-LOCAL.** The missing theorem must identify each physical summand before fixed-domain summation with a mark-indexed $C$, prove that its *raw*, square-root, source and observable dependencies are contained in $R_C^{(2)}$, and carry the analytic local chart (15) through that identification. The current component theorems grant locality for their own given $Y$, but do not prove that their $Y$ is the same $Y^\#(C)$ whose putative estimate `OPEN-GM2#` and fiber counting `OPEN-GM3#` are used. Thus a factor-through statement for the final physical activity is **PROVED CONDITIONAL ON `OPEN-PHYSICAL-HAT-LOCAL`, `OPEN-PAPER-DOMAIN`, `OPEN-GM2#`, `OPEN-GM3#`**. It must not be labeled proved at present.

## 6. Target Lean interface and numerical chain

The target `PaperHatTerms` should contain: a finite label type; `CubeLabels` whose `ysite` is the same completed $Z$ used in (13); its `IsDj` and `meets` proofs; an activity $H(s,t,\hat\psi)$ on open complex background/hat/source/mark domains; the exact physical identity with `interaction_expansion_hat`; block dependence `LabelAct.dep` on `blocksOf Z`; the bound

$$
\|H_y(s,t,\hat\psi)\|\le\epsilon_H e^{-\kappa_H d_K(Z)},
\qquad \kappa_H=2\kappa_{\rm dec}-1;
\tag{16}
$$

and the finite entropy bound $K_c$. `labelAct_of_paperHatTerms` would take these fields and return the landed `Polymer.LabelAct` used by `StepActivityBound`; its dependency field follows by restricting agreement from `blocksOf Z` through (5), while its norm field follows from (13) after the physical prefactor is made at most $\epsilon_H e^{d_K(Z)}$. The latter allocation costs one unit of rate, explaining (16). This interface is **OPEN** until the five named inputs in §§3–5 are proved. The abstract Mayer and cluster theorems do not need a class change.

Here is an explicit *conditional* class-preserving rate chain for $d=L=3$, assuming a geometric input with $q=5/12$ and a finite $D^\#,b^\#,K_\#$. Put $c_1=3375$, choose $\kappa_0\ge a_{\rm Ent}(3,3)+1$, choose

$$
\kappa_{\rm dec}=100(\kappa_0+c_1+10),\quad
\kappa_{\rm in}=\kappa_{\rm dec},\quad
\kappa_H=2\kappa_{\rm dec}-1,\quad
\kappa'=\tfrac32\kappa_{\rm dec}+\kappa_0+1,\quad
\kappa_{\rm out}=\tfrac32\kappa_{\rm dec}.
\tag{17}
$$

Choose $\kappa_{\rm AE}\ge\max\{4D^\#\kappa_{\rm dec},\,4\log[(2L+1)^dL^{dm_0}]+6\}+10$, and make the activity prefactor in (13), after the physical coefficients and the one-rate allocation, small enough for the explicit `StepActivityBound.hε`. Then $1-2q=1/6$, so the first inequality of (11) holds. Also $\kappa_{\rm dec}-1\le\kappa_{\rm in}\le\kappa_{\rm out}$. The landed nonvanishing condition is
$\kappa'+3\kappa_0+c_1+3/2\le\kappa_H$, equivalent with (17) to
$\kappa_{\rm dec}/2\ge4\kappa_0+c_1+7/2$, which holds. `Thm31b.thm31b_of_input` permits the output $\kappa_{\rm out}=\min(\kappa_H,\kappa')-\kappa_0-1$. This is a **PROVED arithmetic check CONDITIONAL ON the open physical and geometric inputs**, not an existence claim for them. In particular, `StepRates.stepRates_no_closure_landed` still rules out closure if one uses the landed halo conversion $\kappa_H=(2\kappa_{\rm dec}-1)/A-c_1$.

## 7. Bounded Lean packages in dependency order

Each package is intended to be about 300 lines and to add parallel declarations, retaining the landed theorems. Statuses describe the present mathematical inputs, not completed code.

1. **Geometry definitions, ~300 lines.** Parallel to `PolymerGeometry.Ysites`, `compY`, `TreeLengthCov.Q0`, and `HatEngineLocal.blockThick`: define the finite cube family meeting (5), deterministic connecting chains, `Ysharp`, and the old/mark attachment decomposition. Prove the unrestricted `IsDj`, inclusions and monotonicity. **PROVED mathematical; OPEN Lean implementation.** For mixed layers, add a separate `OPEN-LAYER-COMPLETION` hypothesis rather than assuming unrestricted chains remain admissible.
2. **Geometry audit, ~300 lines.** Parallel to `TreeLengthCov.gm2` and `HatLabelsGeom.thick_spec`: formalize the comb counterexample or establish a valid $q<1/2$ estimate for a different, source-faithful construction. State `OPEN-GM2#` with all constants and boundary conditions. **PROVED counterexample to $q=1/L$; OPEN replacement bound.** An old-cover equivalence alone is insufficient.
3. **Locality, ~300 lines.** Parallel to `I5FluctLocal.fan_local_fl`, `I5Fluct.i5_fluct`, `HatEngineLocal.hatPsiF_local`: prove restriction from agreement on `Ysharp` to `thickSet Y₁`, `psiThick Y₁`, and `blockThick Y₁`, then to (5) when using the summed theorem. **PROVED conditional on the geometric inclusions and the existing numerical hypotheses.** Keep the background and hat agreements as separate fields.
4. **Local analytic chart, ~300 lines.** Parallel to `I5Expansion.localization_expansion` and `I5Chain.XiCRaw`: define $G_p[Z]$, its restriction/extension chart, strict open neighbourhoods, Cauchy circles and uniform bounds; prove P3 (4.46) in the landed types. **OPEN-PAPER-DOMAIN.** This package must precede Cauchy estimates and fixed-$Z$ resummation.
5. **Reindexing and counting, ~300 lines.** Parallel to `I5Expansion.evTerm`, `gm3_fam`, and `PolymerCount.gm4`: define `evTermSharp` by fibers of $C\mapsto Y^\#(C)$, prove the value identity, a genuine `OPEN-GM3#` count, and (12)–(13). **PROVED CONDITIONAL ON `OPEN-GM2#`, `OPEN-GM3#` and package 4.** Do not reuse `gm3_fam` without changing its fiber hypothesis.
6. **Physical terms and labels, ~300 lines each for two workers if desired.** Parallel to `InteractionHatAssemble.interaction_expansion_hat` and `StepActivityBound`: align all four physical components with `evTermSharp`; construct `PaperHatTerms`, `labelAct_of_paperHatTerms`, and the rate chain (17). **OPEN-PHYSICAL-HAT-LOCAL and the prior inputs.** Verify `StepActivityBound.hκ`, `hε`, and the exact `LabelAct.dep` blocks before invoking Mayer.

The paper's P3 localization is source evidence for a *different* method: replace the generating set after identifying the raw component $Y_1$, while retaining the completion $Y$ of (1). It does not assert that an arbitrary posterior collar of $Y$ satisfies (2). The natural next mathematical task is to formalize that paper-domain replacement and prove direct $Y$-locality, or to find a new completion with $q<1/2$ and a new fiber count. Until then the exact physical rate $2\kappa_{\rm dec}-1$ and class preservation remain **OPEN**.
