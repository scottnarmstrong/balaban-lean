# VMOD-41: removed-component gas in the fine chosen-cover size

**Scope and source.** P7 (3.26)–(3.29), printed pp. 527–29 of s002200050486.pdf, supplies the gas and asserts its H7 estimate for P5 (1.34). The latter is the continuous-tree modular size. The landed fine size is Fluctuation.dcovMod (SizeModDefs.lean) and, after coarse pullback, d7SizePre/d7Size (LargeField/Def7FineSize.lean). The paper assertion alone gives no fine-size transfer.

## 1. Objects and target

**PROVED (source description).** Write $\Omega_-=\Omega_k^{\rm pre}$, $\Omega_+=\Omega_-\cup C$, $C=\bigcup_{c\in{\rm rem}_k}c$, and $Z_+=Z_k^{\rm pre}\setminus C$. An old boundary label $X$ lies in bdryDomsPre, is valid for $\Omega_-$, and has $D_-(X)={\rm d7SizePre}(X)$; its coefficient obeys $|B(X)|<B_{\rm st}e^{-3\kappa D_-(X)/2}$. Removed components are boxes with at most $crit_k^d$ cells (RRipeCard.removed_card_le), and distinct components have sup-distance at least $\omega_k$ (RRipeCard.comp_sep).

P7 p. 528 uses a **thickened** removed component, not merely $c$: write $H_{\rm P7}(c)=(c^{\approx2})^{\sim2}$ for its displayed two successive neighborhoods. A cluster $\Gamma$ is a connected family of old boundary labels $X_1,\ldots,X_p$ meeting a nonempty family $c_1,\ldots,c_m$ of removed components; each participating old label meets a removed component. Its source polymer is
$$
Y_\Gamma=\bigcup_{i=1}^p X_i\ \cup\ \bigcup_{r=1}^m H_{\rm P7}(c_r).
$$
The phrase “connected” on p. 528 applies to $\bigcup_iX_i$; it permits an intersection in a retained hole. The halos must be pulled to fine cells and proved post-valid before identifying this source polymer with a landed bdryDomsPost label.

**PROVED (abstract activity definition).** In Polymer/Gas.lean, gasCs maps an old coupling $y$ to $cy(y)$ and a heavy object $z$ to $zs(z)$; gasA requires disjoint heavy supports and requires every coupling to meet a heavy core $cr(z)$. The elementary weights are $e^{\beta_y}-1$ and $\tau_z$; gasK is their connected-cluster sum at a fixed union support. For P7, $\beta_y$ is the combined old-boundary and action-conversion coefficient on $X_y$, $\tau_z$ is the removed-component operator, $cr(z)=c_z$, and $zs(z)=H_{\rm P7}(c_z)$, subject to a still-open analytic operator-to-scalar majorant. Thus
$$
w(\Gamma)=\prod_{y\in\Gamma_{\rm old}}(e^{\beta_y}-1)
           \prod_{z\in\Gamma_{\rm rem}}\tau_z,\qquad
\rho''_k(Y)=\sum_{\Gamma:Y_\Gamma=Y}w(\Gamma).
$$
The requested estimate is $\sum_{\Gamma:Y_\Gamma=Y}|w(\Gamma)|\le B_{\rm gas}e^{-\kappa D_+(Y)}$, where $D_+(Y)=d7Size(Y)$, uniformly in torus volume. To close the post-H7 bound with other contributions, one possible budget is $B_{\rm gas}\le B_0/2$; that split is a chosen reserve, not a landed record requirement.

## 2. What modular subadditivity proves

**PROVED (landed).** Fluctuation/SizeModUnion.lean:exists_union_admissible unions two chosen covers and joins their connected graphs through a common point $t\in X_1\cap X_2\cap\Omega$. Each graph-to-$t$ route lies in a chosen box; their combined cost is $c_G=2dL$. Consequently G3_dcov proves
$$
D_\Omega(X_1\cup X_2)\le D_\Omega(X_1)+D_\Omega(X_2)+2dL
$$
when both labels are DjMod and their intersection contains a full $\pi_k$ cell of $\Omega$. DjMod_union proves validity of the union from a common site, even if that site lies outside $\Omega$; it supplies no size estimate in that weaker case. An active-overlap spanning tree gives the same bound with $2dL$ per edge.

**PROVED (landed, conditional use).** SizeModExtend.dcovMod_le_add_of_region_grow charges $(dL+d+3)$ per newly active cell under its cell-component splitting hypothesis. SizeModExtendPull.dcovMod_d7Pull_le_add pulls this to coarse labels. The raw-hole component partition in RRawHoleComponent.newlyActive_partition supplies the physical route to that hypothesis; the final per-label d7Size inequality in R/RExtraSize.lean was not present when checked. Applied to the *whole* cluster polymer, extension counts each newly active cell once. Applied separately to every $X_i$, it charges the same removed component once per touching label, which the one factor $e^{-p_2}$ cannot pay independently.

**REFUTED (unrestricted union bound).** A common site in $\Omega^c$ cannot replace the active-cell hypothesis in G3_dcov. In one dimension, fix $L=2$, take a long complement interval $H_N$ of $N$ cells, $\Omega=H_N^c$, and let $X_1$ and $X_2$ each contain all of $H_N$ and one active cell adjacent to its opposite ends. Both are DjMod; a single chosen box and a one-vertex graph give $D_\Omega(X_i)=0$. They overlap in $H_N$. Any admissible graph for $X_1\cup X_2$ meets cover boxes at both ends and runs through $H_N$, so $D_\Omega(X_1\cup X_2)\ge N-O(L)$. This follows directly from ModAdmissible: the graph is connected, contained in the union, and meets every chosen box. No volume-independent junction constant exists.

**REFUTED (even with removed-component charges).** Put a small ripe candidate $c_-$ to the left of $H_N$ and $c_+$ to its right, with active gaps $G_\pm$ of fixed length $g>\omega_k$ and larger than the halo radius. Set $X_-=c_-\cup G_-\cup H_N$ and $X_+=H_N\cup G_+\cup c_+$. The raw complement components are $c_-,H_N,c_+$; retain $H_N$ and remove $c_\pm$. Both labels are connected, pre-valid boundary labels, each meets its removed component, and $X_-\cap X_+=H_N$. They satisfy the stated component size and separation geometry. Chosen covers give $D_-(X_\pm)=O(g+L)$, independently of $N$. Yet the P7 polymer $Y=X_-\cup X_+\cup H_{\rm P7}(c_-)\cup H_{\rm P7}(c_+)$ has $D_+(Y)\ge N-O(g+L+\text{halo radius})$; it is post-valid if the halos miss other complement components. The fixed component budget $(dL+d+3)(|c_-|+|c_+|)$ cannot bridge $H_N$.

For scalar positive coefficients strictly below the old H7 bounds and positive component weights allowed by (3.10), this connected cluster has $w(\Gamma)>0$ bounded below independently of $N$ at fixed scale. Thus no uniform $B_{\rm gas}e^{-\kappa D_+(Y)}$ follows from these magnitude bounds, with $\kappa>0$. This refutes the proposed fine-size gas theorem **from the landed H7 bounds and geometric hypotheses alone**. It does not refute P7's claim for its actual, more structured coefficients.

Quantitatively, this family would demand $2p_{2,\rm run}(k)\ge\kappa N-O(\kappa(g+L+\text{halo radius}))-\log B_{\rm gas}$ for fixed positive old coefficients, whereas $p_{2,\rm run}(k)$ is independent of torus volume. No choice of $A_2$, $H_0$, or initial $\beta$ repairs that inequality uniformly in $N$ without a retained-hole bridge charge.

## 3. Entropy and conditional constants

**PROVED (landed G2), OPEN (boundary-root bridge).** Fluctuation/SizeModEntropy.lean:G2_X gives $K_0(d,L)=e^{a_{\rm ent}(d,L)}/(1-e^{-1})$ for a root $\pi_k$ cell inside $\Omega_-$ and rate $\kappa_0\ge a_{\rm ent}+1$. Here $a_{\rm ent}=\log Q$, $Q=B(2\Delta^2 2^{B(1+\Delta)})^{2\Delta}$, $B=(2L-1)^d$, $\Delta=3^d$. A root in $c\subset\Omega_-^c$ is invalid. Since a connected pre-boundary label containing the entire $c$ must exit through an adjacent active cell, summing over at most $2d|c|\le2d\,crit_k^d$ such roots gives, conditionally on the coarse/fine boundary-root bridge,
$$
\sum_{\substack{X\ {\rm prevalid,\ boundary}\\c\subset X}}
 e^{-\kappa_0D_-(X)}
 \le 2d\,crit_k^d\,K_0(d,L),\qquad \kappa_0=\kappa/2.
$$
This boundary-root bridge is **OPEN** as a named landed lemma. G1_cellCount bounds the number of active cells of $X$ by $c_1(d,L)(1+D_-(X))$, $c_1(d,L)=[3(2L-1)]^d$; assigning each touched component an adjacent active cell yields at most $2d\,c_1(d,L)(1+D_-(X))$ touched components. bridgeFamily_entropy is for treeLenCovOne on nonmodular bridge labels and does not replace G2_X here.

**PROVED (conditional abstract formula).** Polymer/MayerPE.lean:gas_pe, via GasBound.gas_activity_bound and Size.pe_size, has a precise convergence interface. With abstract size $d$, rates $\kappa_g,\kappa''$, constants $c,c_1,c_2,K_{0g},K_{0h},K_{0P},c_P,\kappa_{0P}$, component reserve $p$ and volume rate $h$, its required inequalities include
$$
h\ge B_{\rm st}e^{B_{\rm st}}e^{\kappa_g c}K_{0g}
       +\kappa_g(c_2+c)+c_1+3+\log K_{0h},
\qquad \kappa+\kappa_{0P}+c_1\le\kappa_g-2,
$$
and $\alpha=3c_1e^{-p}K_{0P}e^{c_1+\kappa c_P}\le1$. The output rooted sum, hence each output coefficient, is bounded by
$B_{\rm gas}e^{-\kappa d(Y)}$ with $B_{\rm gas}=3c_1K_{0P}e^{c_1-p}$.
Thus $B_{\rm gas}\le B_0/2$ and $\alpha\le1$ follow from
$$
p\ge c_1+\max\{\log(3c_1K_{0P})+\kappa c_P,\
                  \log(6c_1K_{0P}/B_0)\},
$$
assuming positive logarithm arguments. If $\kappa_g=3\kappa/2$, its rate condition demands $\kappa/2\ge\kappa_{0P}+c_1+2$.

**OPEN (physical instantiation).** Those formulas do **not** yet make $p=p_{2,\rm run}(k)$ a theorem. gas_pe assumes one common size $d$ for input couplings and output polymers, a uniform G3 bound for every connected gas family, G1 for every nonempty support, and rooted G2 for couplings and polymers. Its conclusion bounds the norm of the *resummed* activity, not the stronger sum of absolute cluster weights requested above; the proof of gas_activity_bound would need an absolute-weight wrapper. The input H7 bound uses $D_-$, the desired output uses $D_+$; SizeModExtend cannot transfer the input bound termwise without repeating a component charge. With full support in the block set, G3 fails on the retained-hole example and G1_cellCount counts only active cells, not all of a large hole. Restricting support to active cells removes the false G3 edge but also omits a possible Mayer interaction through the retained hole. Separation may give $K_{0h}=1$ for disjoint halos, and the displayed rooted sum suggests $K_{0g}\le2d\,crit_k^dK_0$, but neither is the required gas_pe hypothesis until support and size are fixed. Converting P7's $H_k|Z|_\eta$ to the theorem's $h|zs(z)|$ is another open normalization step.

## 4. Verdict and Lean order

**Verdict.** P7 asserts the paper-size gas estimate. The proposed fine-size subadditivity under arbitrary connected incidence is **REFUTED**. The fine-size gas estimate for the physical R coefficients is **OPEN** at the retained-hole bridge: either prove that the generator splits interactions whose only overlap is a retained hole, giving an active/removed-core overlap tree, or exhibit extra coefficient/operator decay paying the distance traversed inside every retained hole. Neither property is in D7Bdry2, (3.10), SizeModExtend, or the landed gas_pe hypotheses.

**Lean packages, each at most 300 lines.** (1) R/D7GasRootEntropy, 160–240: boundary-root bridge, G2_X bound and touched-component count using G1_cellCount; pure geometry. (2) R/D7GasHalo, 180–260: define the exact P7 halo, prove its size, separation, post-validity and disjoint-support count from RRipeCard and RipeWindow; pure geometry, pending exact source-to-Lean halo choice. (3) R/D7GasUnionActive, 130–220: fold G3_dcov over an active-overlap tree and compose once with SizeModExtendPull; pure geometry. (4) R/D7RetainedBridge, 200–300 per leaf: a generator ruling or a paid retained-hole corridor bound, with explicit support map; **OPEN**, requires physical coefficients. (5) R/D7GasTwoSize, 220–300 per leaf: adapt gas_activity_bound to old input size and post output size using one charge per component; **OPEN**, depends on (4). (6) R/D7GasPE, 160–240: restricted post-valid polymer entropy and gas_pe/pe_size instantiation with the displayed constants; **OPEN**, depends on (2), (5), and physical analytic weights.

**Confidence.** High for the failure of unrestricted G3 and the landed abstract constant formulas; medium for the concrete retained-hole configuration as a full R history; low for a physical fine-size gas theorem before the generator's retained-hole dependence is specified.
