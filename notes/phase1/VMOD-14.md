# An admissible diagonal wall and the component bridge

**12 October 2026.** This resolves the region-history alternative left open in `VMOD-13.md` §1.1. “Proved” below means a mathematical implication with its written hypotheses. The proposed Lean declarations are not landed. The files under `/home/scott/Balaban` were read only.

## 1. The wall occurs in an admissible history

Use the set functions of `LF-RECONSTRUCTION.md` Definition I.3.1 and the history rules of Definition I.4.1. Their landed counterparts are `LargeField/Region/Step.lean:139–211`, `LargeField/History/FlowSteps.lean:104–145`, and `LargeField/History/RegionHistory.lean:29–37`. Take $d\ge3$, $k_0=0$, horizon $K\ge2$, and a sufficiently large admissible torus. Choose the flow radii with $R_0\ge4L+20$ (the running-radius choice with $R_{\rm base}\ge4L+20$ in `LF-RECONSTRUCTION.md` §I.1.3 permits this), and choose the side of its $\pi_1$ index torus so that the following boxes and all the stated collars have no periodic wrap; the latter side can be made arbitrarily large while divisible by $L$. Put

$$m=\lfloor2R_0\rfloor+3,\quad h=m+6=\lfloor2R_0\rfloor+9,\quad
r=\lfloor R_0\rfloor+1,\quad b=2r,\quad
\delta=h-b\in\{7,8\},\quad p=2\delta-1\in\{13,15\}.\tag{1.1}$$

For a box or set $D$ of $\pi_1$ indices, write $E_tD=\{x:N_t\{x\}\subset D\}$ for its $\ell^\infty$ erosion, and $N_tD$ for its closed $t$-neighborhood. Select $T\gg h+L$ and the two boxes

$$B_-= [0,T]^2\times[0,T]^{d-2},\qquad
B_+=[T-p,2T-p]^2\times[0,T]^{d-2},\qquad O=B_-\cup B_+.\tag{1.2}$$

At $0\to1$, set $Z_0=\varnothing$, $P_1=O^c$, and $Q_1=R_1=S_1=\varnothing$. These are legal records: $U'_0=\varnothing$, hence $\Omega'_1=\operatorname{Op}_{\lfloor R_0\rfloor+2}(\varnothing)=\mathbb T_1$; the $P$ restriction is automatic and all three other restrictions hold for empty sets. Let $\Omega_1$ be the R4 output. The R4 definition `Region.Omega` gives

$$E_3B_-\cup E_3B_+\ \subset\ \Omega_1
=\operatorname{Op}_1(N_3O^c;\mathbb T_1)\ \subset\ E_3O.\tag{1.3}$$

For the left inclusion, each eroded box is a union of sliding $L$-blocks because every side has at least $L$ sites; every such block has distance at least one from $N_3O^c$. The right inclusion follows directly from `le_setDist_iff` (`LargeField/Geometry/Openings.lean:46`). Empty $Q_1,R_1$ give $\Omega''_1=\Omega_1$ by `RegionStep.openingIn_empty` (`LargeField/Region/Step.lean:103`). R6 therefore has

$$F^Z_1=N_4\Omega_1^c,qquad
Z_1^c=\operatorname{Op}_{m}(N_4\Omega_1^c).\tag{1.4}$$

The set of sites that can lie in an $L$-block admitted by this last opening is $E_{m+3}\Omega_1$: distance at least $m$ from $N_4\Omega_1^c$ is equivalent, by splitting a shortest $\ell^\infty$ path, to absence of $\Omega_1^c$ at distance at most $m+3$. Thus the opening is the union of the $L$-blocks contained in $E_{m+3}\Omega_1$. Erosion of (1.3) gives

$$E_hB_-\cup E_hB_+\ \subset\ E_{m+3}\Omega_1\ \subset\ E_hO.\tag{1.5}$$

**Two-box erosion lemma.** If $p<2h$, then $E_hO=E_hB_-\cup E_hB_+$. Indeed, suppose a side-$(2h+1)$ $\ell^\infty$ cube $D$ lies in $O$ but in neither box. It has a site in $B_+\setminus B_-$, exceeding the upper face $T$ in one of the first two coordinates, and a site in $B_-\setminus B_+$, below the lower face $T-p$ in one of them. If these are different coordinates, the corresponding mixed corner of $D$ is outside both boxes. If they are the same coordinate, the other coordinate interval of $D$ has more than $p$ sites and therefore has a point outside $[T-p,T]$; pair it with the appropriate extreme in the first coordinate. That mixed corner is again outside both boxes. The remaining coordinates have identical intervals in the two boxes and cause no exception. This proves the lemma. Both $E_hB_\pm$ are unions of sliding $L$-blocks, so (1.4)–(1.5) yield the **exact identity**

$$\boxed{\ Z_1^c=E_hB_-\cup E_hB_+\ }.\tag{1.6}$$

There is no hidden hull or removal in (1.6): $k_0=0$ makes `critOpt S 0 1 = none` (`FlowSteps.lean:29`) and forces $\mathrm{Rem}_1=\varnothing$ (`RegionHistory.rem_empty`). At all subsequent steps choose $P_i=Q_i=R_i=S_i=\varnothing$ and define $Z_i$ recursively by R6; every restriction is satisfied and every removal set remains empty. This completes a full region history. `RegionHistory.Admissible` in `LargeField/History/FlowBook.lean:286` requires ripeness only of removed components, so it is vacuous here. The construction is relative to any consistent `Setting.Ok`/`RadiusHyp` parameter choice with a sufficiently large torus; it does not assert that every choice of $R_0$ or every fixed small torus admits (1.2). No analytic large-field gain condition restricts $P_1$ in Definition I.4.1 (`LF-RECONSTRUCTION.md` I.4.1, lines 882–897).

Now $W_1=(Z_1^c)^{\approx2}=N_bZ_1^c$. In each of the first two index coordinates, its southwest rectangle ends at $T-\delta$ and its northeast rectangle begins at
$T-p+\delta=T-\delta+1$. The other coordinate ranges overlap. Thus the two pieces of $W_1$ have **no nearest-neighbor bond**, yet their corner cubes are Moore adjacent. This is an actual admissible R1–R9 history, not merely a candidate choice of $Z_1^c$.

### 1.1 The actual P6 pair

Take the P6 step $k=1\to2$ with the empty second record above. Let $H_-=\mathbb B_1(W_1)$, $H_\partial=G^\partial_2$, and let $F^\sharp$ have the lower layers of $H_-$ and the auxiliary top $\pi_2$-closure and one-cell halo $A$ of $U=(Z_1^c)^\approx$. These are `LF-RECONSTRUCTION.md` II.2.2–II.2.5 and `VMOD-11.md` §1. For $q=1$, the defining top layer of the minimal set is exact:

$$\Omega_1(F^\sharp)=\Omega_1(H_-)=W_1.\tag{1.7}$$

Since $U=N_rZ_1^c$, $W_1=N_{2r}Z_1^c$, and the closure and halo cost at most a fixed number of $\pi_1$ cells proportional to $L$, the chosen $r\ge4L+21$ places $A$ strictly inside each piece of $W_1$, with many $\pi_1$ cells of clearance at the outer corner (`VMOD-11.md` (1.3)–(1.4)). Make $T$ still larger so each component of $A$ contains an action cube. A layer-one cover centre $q$ in the last $M_1L$ cell at the upper corner of the southwest piece belongs to `cubeIdx (coverOf F^sharp)`: its cell is in $W_1\setminus A$ and its base is aligned. The fine-site side of a $\pi_1$ cube is $ML$; the interaction half-width is $(5/2)M_1L$, and the hat half-width is $(5/2)M_1L+3L^3$ (`Localization/Decoupled.lean:41`, `Localization/Cover.lean:705`). Both boxes meet the northeast piece across the diagonally adjacent coarse corner. Their intersections with $W_1$ have two nonempty nearest-neighbor components, since no NN path anywhere in $W_1$ crosses between its two pieces. Consequently

$$\neg\operatorname{Dec2.HatConn}(\operatorname{coverOf}F^\sharp,F^\sharp).\tag{1.8}$$

This obstruction is physical for both operators. The landed `RegionStep.not_mem_Z_of_mem_Omega` (`LargeField/Region/Inclusions.lean:283`), or Lemma I.3.5(f), puts $\Omega_2\subset Z_1^c$. The corner sites of $W_1\setminus Z_1^c$ therefore lie outside $\Omega_2$, where the lower layer of $H_\partial$ is the same old-side layer as $H_-$ (`LF-RECONSTRUCTION.md` II.2.4(iv)). The chosen `intBox q` has sites in both components of each operator domain; `Dec2.mem_footprint_self` (`Localization/Decoupled2FpGeometry.lean:105`) puts both in its footprint.

To test G-foot with the **actual** P6 anchor, choose an action cube in the southwest component of $A$ and let $X_1$ be its associated top-layer $\pi'_2$ cube family (`Localization/TreeLengthCov.lean:118–130`). The huge boxes permit this anchor to lie wholly on that side. Take $\mathcal C$ to include the charged cubes of $C.Qset(q)$ and, if needed, a finite chain of charged cells within the southwest component from $X_1$ to one of the first-side cells of `intBox q`. Then $q$ is `Dec2.EligC` (`Decoupled2FpGeometry.lean:153`), and the first-side footprint site lies in the NN component $Y$ of $V(X_1,\mathcal C)\cap\Omega_1(F^\sharp)$ anchored at $X_1$. The second-side footprint site does not: all selected parameter cells are contained in one of the two NN components of $W_1$. Hence

$$q\in B_H(Y),\qquad T_H(q)\not\subset Y,qquad H\in\{H_-,H_\partial\}.\tag{1.9}$$

The finite chain and anchor require only room, supplied by taking $T$ large; they impose no new history condition. Formula (1.9) is a counterexample to G-foot for the original NN component. In particular the hypothesis `HatConn` of the **landed** `I5FluctGeom.incUnion_of_nnComp` (`Localization/I5FluctGeom.lean:61`) cannot be supplied for this P6 pair. One cannot complete the proposed bridge by proving the four G conditions for that same NN $Y$.

## 2. The correct component and what it does not solve

For fine sites use cyclic Moore adjacency $x\sim_*y$ when $x\ne y$ and their cyclic $\ell^\infty$ distance is at most one. Let `IsStarComp Z Y` mean $Y\subset Z$ and closure of $Y$ under this adjacency inside $Z$. Let `StarHatConn C F` say that $\operatorname{hatBox}(q)\cap\Omega_1(F)$ is Moore connected for every cover centre $q$. In the wall history, its two pieces in the selected hat meet by a diagonal Moore step.

In fact **`StarHatConn` holds at $k=1$ for every $W_1$ that is a union of $\pi_1$ cubes**, including this history. The $k=1$ minimal set has $\Omega_1(F^\sharp)=W_1$. For $j=1,2$ the hat diameter is $5M_1L^j+6L^{j+2}$, strictly smaller than the $\pi_1$ cube side $ML$ by the row-5a bound on $M/M_1$ and the row-6 bound $M_1\ge4L^2$ (`LF-RECONSTRUCTION.md` §I.1.3). Its coordinate interval therefore meets at most two aligned $\pi_1$ cells. Every occupied cell in the hat intersects it in a rectangular, NN-connected set. All occupied cells share one coarse vertex of the at-most-$2^d$ array, and the hat intervals that meet both sides of a cell boundary contain the adjacent fine sites on both sides. These chosen sites are pairwise linked by Moore steps at that vertex. Thus the whole intersection is Moore connected. For $k\ge2$, $\mathbb B_k(W_k)$ is built from $M_1L^n$ cells by the $5L$ recursion (`LF-RECONSTRUCTION.md` II.2.2), and the local Moore connectivity of all hat intersections needs a separate cell-grid argument. Name this **OPEN-P6-STARHAT-GENERAL**.

**Star component bridge, proved conditional on `StarHatConn`.** Take the premises of `I5FluctGeom.incUnion_of_nnComp` except replace `HatConn C F` by `StarHatConn C F` and `IsNnComp (V\cap\Omega_1(F))Y` by `IsStarComp (V\cap\Omega_1(F))Y`. Then the same construction of $A_Y$ in the landed proof yields

$$\operatorname{Dec2.IsIncUnion}(C,H,a,\nu,X_1,\mathcal C,Y,A_Y),\qquad
P\in A_Y\Longrightarrow P\in\mathcal C\ \text{and}\ \operatorname{cubeP}(P)\subset Y,\tag{2.1}$$

for $H=H_-$ and $H=H_\partial$, provided `CoverLocal C F`, $\Omega_1(H)\subset\Omega_1(F)$, `RowInHat C H a ν`, and $\mathcal C\subset C.\mathrm{cubeIdx}$ hold. These other P6 premises are still the explicit open bridges `OPEN-P6-COVERLOCAL-F` and `OPEN-P6-COMPONENT-INDEX` of `VMOD-13.md` §1; (2.1) does not prove them. Proof of the conditional component step: replace `connIn_dichotomy` for the hat by its Moore analogue. `footprint_sub_hat` puts every live footprint site in that hat and $\Omega_1(F)$, so a touched hat lies wholly in $Y$ (G-foot). NN site adjacency implies Moore adjacency (G-site). Each charged `cubeP P` is NN connected, hence Moore connected, lies in $V\cap\Omega_1(F)$ by `CoverLocal.cubeP_sub`, and meets the touched hat by the definition of `Qset`; it therefore lies in $Y$ (G-cell). The definition of $A_Y$ and the closure argument in `incUnion_of_nnComp` give G-par and the reverse incidence implications. This is the same proof with two connectivity lemmas exchanged; no operator or parametrix change is involved. Alternatively, defining $Y$ directly as a site projection of a union of components of `Dec2.incGraph` makes G-site, G-foot and G-par true by `IsIncUnion.dichotomy` (`Decoupled2FpGeometry.lean:197`), without `StarHatConn`; its geometric size remains to be proved.

**Consumers.** The existing `PolymerGeometry.compY` (`Localization/PolymerGeometry.lean:426`) takes a component in the NN torus graph. The `loc` field of `Theorem42Input.DecoupledCubeResponse` (`Fluctuation/Theorem42Input.lean:55`) is bound to this exact `compY`; a star-component proof does not inhabit it. `I5Param.LocalityAEOn` (`Localization/I5Param.lean:231`) itself abstracts the map $Y_c(\mathcal C)$, so an alternate theorem 4.2 input may use a Moore component, but its coefficient and geometry consumers must then be ported. There is no implication from locality on the larger Moore component back to the required NN `compY` locality: (1.9) is the counterexample.

The modular holes must **remain NN components**. This is `CLASS-RULINGS.md` Q-E, implemented by `LargeField/Geometry/DomainsMod.lean:37–59` (`NNAdj`, `IsDomain`, `nnComp`, `DmodOmega`) and `Fluctuation/SizeModDefs.lean:78–119` (`OmegaComp`, `DjMod`, `Yhat`, `dOmega`). A Moore component of the site support can be NN disconnected in this example; replacing `OmegaComp` or `nnComp` by a star component would change P5 (1.33). Merely calling the Moore support a polymer is also false: `IsDj` requires NN connectedness, and `dOmega` is $+\infty$ when its NN-connectedness test fails. Filling one missing corner site can meet the NN exterior component of $\Omega^c$ and thereby require its entire saturation in `DjMod`; no bounded local bridge follows from (2.1). The correct continuation must either prove that the **actual** output $\widehat Y$ (with its prescribed hole saturation) is an NN domain at an acceptable covering cost, or introduce a cluster of NN polymers whose incidence graph has Moore edges and prove a new counting theorem. That is **OPEN-P6-STAR-TO-MODULAR**; changing the definition of a hole is not a solution.

Likewise the landed `TreeLengthCov.gm2` (`Localization/TreeLengthCov.lean:435`) explicitly assumes `IsConnectedFamily ... (compY ...)`; Moore connectivity gives no such premise. Its tree construction must be replaced or supplied with a new charged bridge cost, with the curve kept inside the actual output polymer. The landed `PolymerCount.gm3` (`Localization/PolymerCount.lean:215`) counts parameter families at a **fixed** `Ysites` and remains valid under its own hypotheses, independently of the component change. What is missing is a map from the new Moore/graph connected families to fixed admissible NN polymer outputs with bounded multiplicity and cost; hence the combined GRAPH-GM2/3 assertion is **OPEN-P6-STAR-COUNT**. `Vmod7Local.star_bound` (`Localization/Vmod7Local.lean`, section Walk) bounds local NN walks and is a possible charged ingredient, but it does not prove the modular-domain bridge or the new GM2 inequality.

## 3. Lean dependency order, status and confidence

| Order | Proposed declaration (not landed) | Estimated new lines | Existing declaration used |
|---:|---|---:|---|
| 1 | `erosion_union_diagonal_boxes`, including the mixed-corner proof and no-wrap lift | 120–220 | `Geometry/Openings.le_setDist_iff`, `RegionStep.openingIn_empty` |
| 2 | `opening_nbhd_compl_eq_blockErosion` and `large_box_blockUnion` | 150–250 | `Geometry/Openings.opening_disjoint_nbhd`, `opening_compl_subset` as bounds; exact identity is new |
| 3 | `diagonal_regionHistory_k0_zero` with $P_1=O^c$, empty later records/removals, and `Z1_compl_eq` | 250–450 | `RegionStep` and `FlowSteps` constructors, `critOpt`, `RegionHistory.Admissible` |
| 4 | `diagonal_W_components`, `p6_wall_layer_one`, `p6_not_hatConn`, and the actual-anchor `p6_gfoot_counterexample` | 300–600 after P6 set port | `not_mem_Z_of_mem_Omega`, `coverOf`, `cubeIdx`, `mem_footprint_self` |
| 5 | `StarAdj`, `IsStarComp`, `star_conn_dichotomy`, `star_hat_dichotomy` | 130–220 | NN `connIn_dichotomy` proof pattern; `LargeField.starComp` has a related but different carrier |
| 6 | `incUnion_of_starComp` with both physical $H$ values | 100–180 | `I5FluctGeom.incUnion_of_nnComp` proof, `footprint_sub_hat`, `cubeP_connIn'`, `IsIncUnion.dichotomy` |
| 7 | `p6_starHatConn_k1` from coarse alignment, then `p6_starHatConn_general` for $k\ge2$ | 100–180, then 250–600 uncertain | `hatRad` and P3 minimal-set cell recursion; general case **OPEN-P6-STARHAT-GENERAL** |
| 8 | `p6_star_to_modular`, a new charged `gm2_star`, and compatible fixed-output `gm3_star` | unestimated research work | `TreeLengthCov.gm2`, `PolymerCount.gm3`, `Vmod7Local.star_bound` are partial inputs; **OPEN-P6-STAR-TO-MODULAR/COUNT** |

**Disposition.** Proved in this note: a paper-level admissible $k_0=0$ history satisfying the region set functions with exact (1.6); diagonal contact of its $W_1$; failure of NN `HatConn` for the P6 virtual cover; failure of G-foot for the corresponding NN component once the P6 anchor and charged chain are selected; and Moore connectivity of all $k=1$ virtual-cover hats. The star bridge (2.1) is proved **conditional on** its written cover, row, index and `StarHatConn` premises, some of which are **OPEN** for the full P6 pair. The existing `compY`, modular domains and GM2/3 pipeline do not accept a silent NN-to-Moore substitution. Confidence is high in the set-function construction and the obstruction; medium in the finite-grid Lean port and the $k\ge2$ Moore-hat assertion; the modular counting repair is open.
