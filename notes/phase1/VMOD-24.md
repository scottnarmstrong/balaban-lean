# Rooted patch counting for a P6 site support

**12 October 2026.** Response to followup_r24.txt. The uniform candidate-region bound proposed in VMOD-23 is not a consequence of the actual cover and the rooted Moore geometry. A bounded-degree count of source-rooted patch sets replaces it. The graph count is proved below; its use for actual nonzero P6 coefficients is conditional on the named active-rooted AE and analytic producers. P3 (4.50), printed p. 81, uses a fixed-whole-output subset count, not this rooted-animal count. All Balaban source and Lean files were read only.

## 1. Location of derivative cells

Write \(K=k+1\), \(a_n=L^{m_0+m_1+n}\), \(p_n=L^{m_1+n}\), \(A'=(L^{m_0})^d\), \(F^\sharp=\mathrm{p6FsharpC}\), and \(I=\operatorname{cubeIdx}F^\sharp\). For \(P=(n,y)\in I\), let \(T(P)\) be its top \(\pi_K\) cell, \(c(P)\) its layer-\(n\) cell, and \(\operatorname{Pset}(P)\) its parameter cube. The same-cell divisibility in PolymerGeometry.Pset_subset_cellOf gives \(\operatorname{Pset}(P)\subset c(P)\subset T(P)\).

**PROVED CONDITIONAL ON cited PROVED declarations.** P6PairBoundary.p6_omega_subset_halo gives
\[
 \widetilde\Omega_K\subset A=F^\sharp.\Omega K. \tag{1.1}
\]
Here \(\widetilde\Omega_K\) is the fine lift of the new *active* region and \(A\) is the auxiliary cover's top domain; they are different objects. Both are top-cell unions. If \(T(P)\) meets \(S\subset\widetilde\Omega_K\), then \(y\in A\). Cover.mem_cubeIdx also puts \(y\) in \(F^\sharp.\operatorname{layer}n\), so GeneratingSet.layer_disjoint forces \(n=K\). Thus only one layer-labelled cell occurs per active top cell of \(S\), and SizeModCore.cellCount_le_of_admissible gives at most \(c_G(1+D(S))\) such cells, \(c_G=[3(2L-1)]^d\), for the chosen-cover site size.

The one-cell halo is stronger. P6PairHalo.p6HaloCubes defines \(A\) as the one-top-cell neighborhood of the top closure of \(\operatorname{thick}_{\rho'}Z_k^c\). RegionStep.not_mem_Z_of_mem_Omega puts the old preimage of an active new cell in \(Z_k^c\). Hence every top cell Moore-adjacent to an active new top cell lies in \(A\). Any parameter patch Moore-touching one active top cell is therefore at layer \(K\). There are at most \(3^d\) neighboring top cells and at most \(A'\) indices per such cell, by GraphGmCount.card_deriv_in_cell, provided \(L^{m_0}\mid N_1\). Thus
\[
 b_{\rm root}:=
 \#\{P\in I:\operatorname{MooreTouch}(U,\operatorname{Pset}(P))\}
 \le 3^d A'                                                   \tag{1.2}
\]
for each active top cell \(U\). **Status: PROVED mathematical implication conditional on the cited landed halo/cell theorems and their torus-scale identification; the coarse-to-fine Lean wrapper is OPEN as code.**

The forest rule alone gives only a radius depending on its size. Suppose every component of \(C\) has a root patch Moore-touching an **active** source top cell in \(A_X\subset S\), and each other patch Moore-touches its parent. A parent chain has at most \(|C|\) edges. Since Moore-touching patches have the same or neighboring top cells,
\[
 c(P)\subset T(P)\subset N^{\rm top}_{|C|}(A_X)
                   \subset N^{\rm top}_{|C|}(S),\quad P\in C. \tag{1.3}
\]
This is **PROVED under the active-root assumption**. The radius is \(|C|\), not a constant. The record in LedgerCounter.SNAGGridRecord.forest only anchors to \(A_0\subset B\), which need not lie in \(S\); from that record alone the radius is \(|C|+\operatorname{dist}_{\rm top}(A_0,S)\). The active-root refinement for actual P6 coefficients is OPEN-P6-ACTIVE-ROOTED-AE, a concrete part of OPEN-P6-STAR-AE. P6 p. 34 asserts that each preliminary component contains an old active trace component, but the mixed coefficient-level witness is not landed.

## 2. Why a uniform candidate region is the wrong count

For an arbitrary top cell, the generic number of layer-\(n\) cells is \(L^{(K-n)d}\). Actual \(F^\sharp\) has no lower layers in \(S\), by §1, but it can have many near an old wall. Below \(K\), P6PairHalo.p6Fsharp_Ω_of_le identifies \(F^\sharp\)'s domains with the old p6Hold domains; p6Hold_Ω identifies these with MinimalGenSet.minLayer. For a flat old wall on a large torus, the layer-1 shell contains at least one full row of \(p_1\)-cells across a transverse top-cell face. One top cell cutting that row contains at least
\[
 (a_K/p_1)^{d-1}=L^{(m_0+K-1)(d-1)}                         \tag{2.1}
\]
layer-1 cells. For a half-space \(W\) with an aligned flat face, cubeInterior is the same half-space, and each nearStep moves its face outward by \(5L\) cells of that step's scale. In particular \(\Omega_1\setminus\Omega_2\) contains a complete \(p_1\)-row across the transverse directions. This is the direct recurrence of MinimalGenSet.minLayer_of_lt and nearStep. Fsharp's top halo is inside the old \(W\), so it does not remove the outside shell. **Status: PROVED for a flat-wall set-level input to the actual p6FsharpC constructor**; realization of that half-torus wall by a ripe admissible multi-step history is OPEN. This refutes a bound on all layers in *arbitrary* top cells from the actual-cover API. It does not affect the active-cell result of §1.

Even top-layer cells defeat the candidate-region estimate for geometrically allowed rooted families. Keep a fixed nonempty old \(Z_k\). Far from it, take a new \(\mathsf P_K\) rectangular prism of length \(T\) and transverse width greater than \(L+4\) top cells, with \(\mathsf Q_K=\mathsf R_K=\mathsf S_K=\varnothing\). The RegionStep set constraints allow \(\mathsf P_K\subset\Omega'_K\), and RegionStep.P_subset_compl_Omega puts it in the new hole. Since the prism lies in old \(Z_k^c\), P6PairHalo.p6HaloCubes puts it in \(F^\sharp.\Omega K\); its aligned parameter indices are actual members of Cover.cubeIdx Fsharp. Choose an old boundary source \(X\) and source-cover \(B\) reaching the fixed near end. A top-layer Moore chain from its active anchor enters the prism. Its first bounded segment fixes the active output \(S\). After depth \(L+2\), central cubes \(Q(P)\) of VMOD-18 (2.2) fit wholly inside \(\mathsf P_K\subset\Omega_K^c\), so extending the chain does not change \(S=(X\cup B\cup\bigcup Q(P))\cap\Omega_K\). The fixed prefix gives a chosen cover and a tree of bounded \(D(S)\), while the union of candidate layer cells visited by all such chains grows with \(T\).

This **PROVES failure of a uniform \(|R(X,S)|\le c_0+c_1D(S)\) deduction from the actual cover indices, RegionStep set geometry, and the rooted-forest/output rules**. It does not prove that each chain has a nonzero P6 coefficient or that the prism is realized by every full ripe history; both are OPEN. No result cited supplies the extra vanishing that would turn the candidate-region assertion into a coefficient theorem. We can avoid it altogether by summing chains with their cardinality weight.

P3 (4.50), printed pp. 80–81, does **not** count a bounded number of choices for each next cube. It fixes the *whole* multiscale output \(Y\); its new-cell ownership gives \(|Y_c\setminus B_c|\le(2L+1)^d|C|\), and it sums subsets of at most \(A'|Y_c\setminus B_c|\) candidates. This is formalized by GraphGmCount.fixed_output_count. A site support forgets output cells buried in a hole, so that ownership argument need not apply. The rooted count below is a new replacement for the site index, not a reinterpretation of P3.

## 3. Actual-cover Moore degree and a finite rooted count

Let the graph \(G_F\) have vertices \(I\), with \(P\sim Q\) when their parameter patches Moore-touch (LedgerCounter.MooreTouch). Assume \(L\ge3\), \(M_1=L^{m_1}\), \(m_1\ge2\), \(L^{m_0}\mid N_1\), and
\[
 d<5L^3M_1.                                                 \tag{3.1}
\]
Set
\[
 b_{\rm int}=3(L+4)^d,\quad
 B_*=\max\{2,b_{\rm int},3^d A'\}.                            \tag{3.2}
\]

**Lemma 3.1 (PROVED CONDITIONAL ON cited PROVED cover declarations).** Every vertex of \(G_F\) has degree at most \(b_{\rm int}\), independently of \(K\), torus size and history.

*Proof.* P6PairHalo.p6_fsharp_cubeAligned (and its cast in P6PairOp) plus Cover.mem_cubeIdx put every site of a layer-\(i\) patch in \(F^\sharp.\operatorname{layer}i\). If \(j\ge i+2\), a site of the \(i\)-patch is outside \(F^\sharp.\Omega(i+1)\), while a site of the \(j\)-patch is in \(F^\sharp.\Omega(i+2)\). The GeneratingSet.separation field at \(i+1\) gives their torus \(\ell^1\) distance \(>(5LM_1)L^{i+1}\ge5L^3M_1>d\). Moore-touching gives distance at most \(d\), contradiction. Reverse \(i,j\) similarly. Hence a neighboring index has layer \(i-1,i\), or \(i+1\); layer_disjoint also rules out multiple layers at one point.

The patch sides in those three layers are \(p_i/L,p_i,Lp_i\). In each coordinate an aligned interval of side \(p_j\) meeting the one-site enlargement of a fixed interval of side \(p_i\) has at most \(\lceil p_i/p_j\rceil+3\le L+4\) possible grid bases. A torus-seam lift cannot add candidates. There are therefore at most \((L+4)^d\) neighbors in each of the at most three layers, proving (3.2). \(\square\)

**Lemma 3.2 (PROVED finite combinatorics).** In a finite graph with internal degree at most \(b_{\rm int}\), let \(A\) be \(r\) external roots, each adjacent to at most \(b_{\rm root}=3^dA'\) internal vertices. For any family \(\mathscr F\) of internal finite sets \(C\) whose every connected component has an edge to a root, put
\[
 t=e^{-\kappa_2},\quad z=B_*^2t<1,\quad h=-\log(1-z).
\]
Then
\[
 \sum_{C\in\mathscr F}t^{|C|}\le(1-z)^{-r}=e^{hr}.          \tag{3.3}
\]

*Proof.* Fix orders on vertices and roots. A set of \(n\) internal vertices connected to one root has a canonical spanning tree on those vertices and the root. Its deterministic depth-first traversal is a walk of length \(2n\); the walk recovers its visited set, so this coding is injective. Each step has at most \(B_*\) choices, hence at most \(B_*^{2n}\) rooted sets. Their weighted sum, including the empty set, is \(\sum_{n\ge0}z^n=(1-z)^{-1}\). For a general \(C\), assign each internal connected component to its least adjacent root. The union assigned to each root is connected with that root; the tuple of assigned unions recovers \(C\). Enlarge to all such tuples and multiply the one-root bounds. \(\square\)

There is **no factor \(K\)** for a layer choice: Lemma 3.1 permits only three layers for a next patch, and (1.2) controls the first patch at an active root. Long excursions into a hole cost their number of patches. This is why (3.3) stays uniform when the candidate region does not.

## 4. Fixed-support theorem and one-step boundary clause

Let \(A_X\) be the active new top cells of \(X\cap\widetilde\Omega_K\). Assume OPEN-P6-ACTIVE-ROOTED-AE: every nonzero derivative family for an old P6 boundary term, for each of the two physical operators with common \(F^\sharp\), has every patch component Moore-connected to \(A_X\). This is a specific missing binder of OPEN-P6-STAR-AE and of the actual I5Param.LocalityAEOn instantiation. It is stronger than an arbitrary anchor \(A_0\subset B\).

Assume also the post-R source nesting and size comparison OPEN-P6-SOURCE-SIZE-BRIDGE: \(\widetilde\Omega_K\subset\widetilde\Omega_k^{\rm post}\) and the old H7 size is the \(\Delta_X=d_k^{\rm cov}(X\mathbin{\rm mod}(\Omega_k^{\rm post})^c)\) used below. VMOD-21 §3 proves the set inclusion from region rules, but not the entire H7/size accessor. Landed SizeModCore.cellCount_le_of_admissible and refinement of one old top cell into \(L^d\) new top cells give
\[
 |A_X|\le c_X(1+\Delta_X),\qquad c_X=L^dc_G,\quad
 c_G=[3(2L-1)]^d.                                         \tag{4.1}
\]
**Status: PROVED CONDITIONAL ON the named open source-size bridge and cited PROVED G1.**

Let \(H_*=e^{hc_X}\), \(q_*=hc_X\), and \(\mu=\kappa_0-q_*\), where \(h\) is from (3.3). Lemma 3.2 bounds **all** active-rooted families before sorting by support, hence in particular
\[
 \sum_{C:S_C=S}e^{-\kappa_2|C|}
 \le H_*e^{q_*\Delta_X}.                                  \tag{4.2}
\]
**Status: PROVED CONDITIONAL ON OPEN-P6-ACTIVE-ROOTED-AE and OPEN-P6-SOURCE-SIZE-BRIDGE.** No candidate-region assertion is used.

For the quantitative step, suppose OPEN-P6-MIXED-H7-TERM supplies one strict H7 polydisc and the individual P6 bound, and OPEN-P6-STAR-AE plus the SN–AG–GRID source record give the site transfer
\[
 D(S_C)\le\Delta_X/L+dL|C|.
\]
Put \(\kappa_2=\kappa_1/2-1\), and require
\[
 \kappa_0\ge0,\quad\kappa\ge3\kappa_0+3,\quad
 \kappa_1\ge4dL\kappa,\quad z=B_*^2e^{-\kappa_2}<1,\quad
 \mu\ge a_{\rm ent}(d,L)+1.                               \tag{4.3}
\]
The arithmetic of VMOD-18 (3.5) then gives each coefficient
\[
 \|a_{X,C}\|_{H7}\le\beta_k^{-2}
 e^{-\kappa_0\Delta_X-2\kappa D(S_C)-\kappa_2|C|}.
\]
Sum by (4.2) at fixed \(X,S\):
\[
 \|B_X^+(S)\|_{H7}\le\beta_k^{-2}H_*
 e^{-\mu\Delta_X-2\kappa D(S)}.                           \tag{4.4}
\]
The old-source anchor count of VMOD-18 (3.8), using landed SizeModEntropy.G2_X at rate \(\mu\) and G1 at \(S\), yields
\[
 \|B_{\rm old}^+(S)\|_{H7}
 \le\beta_k^{-2}H_*L^dc_GK_0(d,L,\mu)(1+D(S))e^{-2\kappa D(S)}
 \le\beta_k^{-2}H_*L^dc_GK_0(d,L,\mu)e^{-(2\kappa-1)D(S)}.
                                                                  \tag{4.5}
\]
Thus the **exact P6 output rate** survives; the animal count spends \(q_*\Delta_X\), not \(qD(S)\). An explicit convenient choice is \(z\le1/2\) and \(2c_Xz\le\kappa_0-a_{\rm ent}(d,L)-1\), since \(-\log(1-z)\le2z\). If \(\beta_k^{1/2}\ge H_*L^dc_GK_0(d,L,\mu)\), the old-boundary part has P6 (4.34)'s \(\beta_k^{-3/2}\) prefactor. **Status of (4.4)–(4.5): PROVED implication conditional on the named OPEN actual-P6 inputs.**

The one-step site D7 clause is: sum all actual \(X,C\) labels with fixed active site support \(S\) into \(B^+(S)\); retain the completed-site **plus exact read-collar** locality, common H7 analyticity, reality and symmetries, and require a through-hole marked-read bound. If the Gaussian and surface terms of P6 (4.32), printed p. 34, have a site-output bound \(B_{\rm step}e^{-(2\kappa-1)D(S)}\), then
\[
 \sup_{H7}|B^+(S)|\le B_0^+e^{-(2\kappa-1)D(S)},\qquad
 B_0^+=B_{\rm step}+\beta_k^{-2}H_*L^dc_GK_0(d,L,\mu).
                                                                  \tag{4.6}
\]
For \(B_{\rm step}\le\tfrac12\beta_k^{-3/2}\) and \(\beta_k^{1/2}\ge2H_*L^dc_GK_0\), one has \(B_0^+\le\beta_k^{-3/2}\). The pure-step site estimate, marked-read estimate, D7 representation preservation, and later R-stage transport are respectively **OPEN-P6-MIXED-H7-TERM, OPEN-P6-REP-PRESERVATION, and OPEN-R-SITE-NORM**. The global weighted Wiener coefficient hypothesis of VMOD-22 is unnecessary for (4.5) if active-rooted locality is proved; the resulting aggregate bound remains a D7 *conclusion*.

## 5. Lean slices and status

These are proposed declarations; no Lean file was edited.

| Order | Statement sketch and landed inputs | Status/size |
|---:|---|---|
| 1 | p6_active_top_halo: each top neighbor of a new active top cell lies in \((p6FsharpC\ldots).\Omega K\). Use RegionStep.not_mem_Z_of_mem_Omega, P6PairHalo.p6HaloCubes/p6Fsharp_Ω_top, P6PairBoundary.p6_omega_subset_halo, with explicit torus casts. | PROVED mathematical implication; Lean OPEN, 100–180 lines. |
| 2 | p6_root_patch_count: (1.2), using row 1, CubeAligned.mem_layer_iff, Cover.mem_cubeIdx, GeneratingSet.layer_disjoint, GraphGmCount.card_deriv_in_cell. | PROVED CONDITIONAL ON cited landed results; 120–210 lines. |
| 3 | cubeIdx_moore_layer_gap: Moore neighbors differ by at most one layer under (3.1), using p6_fsharp_cubeAligned, GeneratingSet.separation, LedgerCounter.MooreTouch, MinimalGenSet.minSep. | PROVED CONDITIONAL ON cited landed results; 130–220 lines. |
| 4 | aligned_patch_touch_count and cubeIdx_moore_degree: grid-interval bound \((L+4)^d\) for each possible layer; degree \(3(L+4)^d\). | PROVED elementary geometry; Lean OPEN, 180–300 lines. |
| 5 | rooted_animals_weighted: finite graph/root degree hypotheses imply (3.3) by canonical DFS. | PROVED finite combinatorics; Lean OPEN, 150–260 lines. |
| 6 | p6_active_source_card and p6_fixed_site_fiber: (4.1)–(4.2) using SizeModCore.cellCount_le_of_admissible and rows 2–5; keep active-rooted AE and source-size bridge as explicit binders. | PROVED CONDITIONAL ON OPEN-P6-ACTIVE-ROOTED-AE and OPEN-P6-SOURCE-SIZE-BRIDGE; 180–280 lines after bridges. |
| 7 | p6_site_boundary_step: (4.4)–(4.6), then marked-read and D7/R preservation. Reuse SizeModEntropy.G2_X/G2_S and I5Param.abstract_expansion_on or I5Expansion.localization_expansion under their exact premises. | Research scope; OPEN-P6-STAR-AE, OPEN-P6-MIXED-H7-TERM, OPEN-P6-REP-PRESERVATION, OPEN-R-SITE-NORM. |

**Disposition.** PROVED: the size-dependent containment, finite rooted-animal count, and fixed-support algebra. PROVED CONDITIONAL ON cited landed cover declarations: the top halo and bounded Moore degree under the displayed numeric premises. OPEN: actual P6 active-rooted coefficient geometry, strict mixed H7/termwise estimates, source-size bridge, pure-step site localization, marked-read estimate, and D7/R preservation. Confidence is high in the graph count and algebra, medium in the exact Lean port of the cover geometry, and low in unconditional P6 closure before the open producers are supplied.
