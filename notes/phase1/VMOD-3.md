# The landed Dec2 interface and the mixed pairs

**Snapshot: 12 October 2026.** This note follows the accepted VMOD-2.md. It checks the exact structures in Balaban/Localization/Decoupled2.lean, Decoupled2Geometry.lean, DecCover.lean, and Decoupled2Self.lean. The requested proof of every field for both crossed pairs is not possible from the stated hypotheses: the landed locality structure forces equality of the two first domains. The mixed Dirichlet-wall estimate and the minimal-set block count remain open. No file under /home/scott/Balaban was modified.

## 1. Settings and an exact obstruction

Put $K=k+1$, $M_1=L^{m_1}$, $M=L^{m_0}M_1$, $d,L\ge3$, and $N_0(d,L)=3(8L)^d$. Extend the old depth-$k$ set $H^-=\mathbb B_k(W_k)$ to depth $K$ by an empty top domain. Let $H^+$ be the physical new generating set. Use the **haloed** auxiliary set $F^\sharp$ of VMOD-2.md (1.2): its lower domains are those of $H^-$ and its top domain is
$$A=\operatorname{Halo}^1_{\pi_K}\operatorname{cl}_{\pi_K}\bigl((Z_k^c)^\approx\bigr).$$
Set $C^\sharp=\operatorname{coverOf}F^\sharp$ and $C^+=\operatorname{coverOf}H^+$. The displayed set in FLUCTUATION Definition 2.7 has no additional halo; the present $F^\sharp$ is its repaired version. We assume $k\ge1$ in the old-layer arguments. The $k=0$ base case needs a separate formulation.

The exact operator fields of Dec2.OpSetting are $d,L\ge3$, $0\le\nu$, $\nu L^{2K}\le1$, admissible weights, and
$$2d\log L\le\frac{\operatorname{agmonRate}(d)}{16}(\varrho_H-1). \tag{1.1}$$
LFR row 6 must be checked against (1.1), rather than against an unnamed threshold. Dec2.CoverGeom adds, in order, blockAligned, chi_unit, sum_chi, chi_smooth, inner_near, card_box, card_qset. Dec2.CoverBase adds
$$\texttt{nc}:\quad\forall\alpha\in\operatorname{AdmPot}(H),\ \forall q\in C.\operatorname{cubeIdx},\
\operatorname{CubeBlockBounds}(H,a,\nu,\alpha,q,K_c). \tag{1.2}$$
Dec2.CoverLocalGeom adds idx_range, idx_base, chi_supp, cubeP_sub, own_cover; Dec2.CoverLocal adds row_mem_hat. The self theorem Dec2.coverLocal_self assumes DGSetting. Its cover_sep field asks for $\varrho\ge4dLM_1$, whereas the minimal sets have only $\varrho_3=5LM_1$; it is not a proof of the required minimal-set instance.

**Necessary-domain theorem (proved).** Let $F$ be cube-aligned and $C=\operatorname{coverOf}F$. Then
$$\operatorname{CoverLocalGeom}(C,H,a,\nu,C_x)\quad\Longrightarrow\quad
\Omega_1(F)=\Omega_1(H). \tag{1.3}$$
For $x\in\Omega_1(F)$, Cover.lean own_mem_cubeIdx supplies its own center $q$ and $x\in\operatorname{cubeP}(q)$. The field cubeP_sub gives $x\in\Omega_1(H)$. Conversely own_cover puts each $x\in\Omega_1(H)$ in a parameter cell of a center of $F$; Cover.lean mem_cubeIdx, cube alignment, and DecoupledGeometry.lean mem_cubeP put that entire parameter cell in the center's layer of $F$. This proves both inclusions. In the auxiliary construction $\Omega_1(F^\sharp)=\Omega_1(H^-)$, so the old pair passes (1.3).

The crossed pairs $(C^\sharp,H^+)$ and $(C^+,H^-)$ require an additional equality of first domains. LFR Definition II.2.4(iv) defines $H^+$ by surgery across $\Omega_{k+1}$; it does not state that equality. An admissible abstract pair with a proper new island inside the old domain violates cubeP_sub for auxiliary cells outside the new island. A new-domain cell outside the old first domain violates cubeP_sub for $(C^+,H^-)$. These are counterexamples to automatic instantiation of the present structure; they do not assert that every specific history has unequal domains. The natural pair $(C^+,H^+)$ is a self pair, provided its strong DGSetting hypotheses are discharged separately.

This restriction is used, not ornamental: Dec2.dg5' in Decoupled2Geometry.lean uses cubeP_sub to regard each whole parameter cell as connected inside $\Omega_1(H)$, and own_cover to assign a parameter cell to every site of the thickened interaction box. A replacement with $\operatorname{cubeP}(q)\cap\Omega_1(H)$ requires a new component lemma when this clipped set is disconnected. Solving NC3 alone does not solve that locality problem.

## 2. CoverGeom, in the landed field order

Here is a fieldwise criterion and proof. Let $C=\operatorname{coverOf}F$; assume $F$ is cube-aligned, $M_1\ge4L^2$, the torus divisibility and size assumptions, and cyclic **sup** separation at each cover interface at least $5LM_1\ell_n$. The latter is proved for the minimal lower interfaces by LFR II.2.2–II.2.3 and for the inserted top interface by VMOD-2.md (1.1). Assume also:

* E: $\Omega_1(H)\subset\Omega_1(F)$.
* S: $n_H(x)\le n_F(x)+1$ at each $x\in\Omega_1(H)$. The cover quotient estimate itself is centered at $x$ and includes neighbors even when they lie outside $\Omega_1(F)$.
* B: $n_H(x)\le q.1+m_1$ whenever $q\in C.\operatorname{cubeIdx}$ and $x\in\operatorname{intBox}(q)\cap\Omega_1(H)$.
* I: $n_H(x)\le q.1+1$ when $C.\chi(q,y)\ne0$, $x\in\Omega_1(H)$, and $x,y$ lie in one $H$-block. This bound is unnecessary when $x,y$ are nearest neighbors.

For $(F^\sharp,H^-)$ these comparisons follow from the explicit domains:
$$n_{H^-}(x)=\min\{n_{F^\sharp}(x),k\}. \tag{2.1}$$
Outside $A$ the layers agree; inside $A$ the cover layer is $K$ and the old layer is $k$. A box or supported bump of scale $m$ cannot reach a cover layer at least two scales away: the box-to-center sup distance is at most $3M_1\ell_m$, while the relevant old interface has margin $5LM_1\ell_{m-1}$ or greater at its own scale. The same comparison after a displacement of one $H$-block uses $\ell_{n_H}\le L\ell_m$ and $M_1\ge4L^2$. At the top the margin $(r-2L-2)M\ell_k$ of VMOD-2.md (1.1), with $r=[R_{k-1}]+1\ge4L+21$, is larger. Thus B and I hold. This is a paper-level proof using the proved LFR recursion; the corresponding Lean bridge has not landed.

1. **blockAligned.** BoxGeometry.lean box_sameCell says $\operatorname{intBox}(q)$ is a union of cells of side $M_1\ell_{q.1}$. By B every $H$-block meeting the box has side $\ell_{n_H}$ dividing this cell side. It therefore lies wholly inside or wholly outside the box. This is exactly BlockAligned H (intBox q) of Multiscale/CutOperator.lean.

2. **chi_unit.** E gives a cover-own center at $x\in\Omega_1(H)$. Cover.lean coverDenom_ge yields $D_F(z)\ge4^{-d}$ for $z=x,x\pm e_\mu$, including neighbors outside $\Omega_1(H)$. Every bump is nonnegative and no larger than their sum. Hence $0\le C.\chi(q,z)\le1$ for every indexed $q$.

3. **sum_chi.** At $x\in\Omega_1(H)$, the same denominator is positive and $\sum_q\chi_q(x)=D_F(x)/D_F(x)=1$. This is Cover.lean sum_chi applied to $F$ after E.

4. **chi_smooth.** The quotient argument of Cover.lean chi_diff, with the direct sup-separation count in VMOD-2.md (1.8), gives at a cover-layer-$n_F$ site
$$|\chi_q(x\pm e_\mu)-\chi_q(x)|\le\frac{cH1(d,L)}{M_1\ell_{n_F}},\qquad
|\chi_q(x+e_\mu)+\chi_q(x-e_\mu)-2\chi_q(x)|
\le\frac{cH2(d,L)}{(M_1\ell_{n_F})^2}. \tag{2.2}$$
Here the one-site stencil has at most $9\cdot3^d$ active bumps, as in the proof of Cover.lean chi_diff; its same-set strong-separation call must be replaced by the proved direct count. Multiplication by $\ell_{n_H}$ and $\ell_{n_H}^2$ and S gives IsSmoothField H $(C_x/M_1)$ with the explicit uniform choice
$$C_x=L\bigl(cH1(d,L)+d\,cH2(d,L)\bigr)=L\,Cchi(d,L), \tag{2.3}$$
since $L^2/M_1\le L$. For $(C^\sharp,H^-)$, (2.1) improves this to $C_x=Cchi(d,L)$. The direct-cover version of (2.2) remains Lean implementation work.

5. **inner_near.** Cover.lean inBox_of_chi_ne_zero puts $y$ within $3M_1\ell_m/2$ of the center, $m=q.1$. If $y$ is a neighbor of $x$, the displacement is one. If $y$ lies in the $H$-block of $x$, I bounds it by $\ell_{n_H(x)}\le L\ell_m$. Add any displacement of at most two sites for Inner. As $M_1\ge4L^2$, the resulting point is within $5M_1\ell_m/2$, as in BoxGeometry.lean inner_of_near. Thus Inner q x holds.

6. **card_box.** A box of scale $m$ meeting a point of cover layer $n$ must have $|m-n|\le1$ by the sup-separation comparison above. At one scale at most five aligned centers per coordinate have a box containing the point. Thus the exact field bound is $3\cdot5^d$. E assigns a cover layer to every point of $\Omega_1(H)$.

7. **card_qset.** A witness cell meeting the hat box has a site of the layer of its center; its distance from the first center is less than $(5/2+3/4)M_1\ell_m=13M_1\ell_m/4$. Sup separation excludes center scales differing by at least two. The per-scale coordinate count in Cover.lean card_Qset_le, after its Qset_layer step, is $(8L)^d$. Therefore $|C.Qset(q)|\le3(8L)^d=N_0(d,L)$, as in VMOD-2.md (1.9). The landed wrapper itself has the unavailable binder $\varrho_F\ge4dLM_1$.

These seven arguments are **proved at paper level for $(C^\sharp,H^-)$ conditional on the proved LFR minimal-set construction and the proved halo lemma of VMOD-2.md**. They are not a landed CoverGeom instance. The self pair $(C^+,H^+)$ obeys the same direct geometry if its minimal-set hypotheses are supplied. For a crossed pair E, S, B, I are OPEN-EMBED-MIXED and OPEN-LAYER-MIXED; the halo of the old set supplies none of their new-domain conclusions.

## 3. The nc field and the internal wall

DecoupledCube.lean CubeBlockBounds has one bounds field returning a triple: value, forward gradient, and symmetric Laplacian. For a source supported on one complete $H$-block of scale $j'$, bounded by $M_f$, the right side in each inequality is
$$K_c\exp\!\left[-\frac{\operatorname{agmonRate}(d)}2\,\operatorname{pathDist}_H(x,y')\right]\ell_{j'}^2M_f. \tag{3.1}$$
The gradient and Laplacian left sides carry $\operatorname{spacing}_H(x)$ and its square. A two-center Hölder estimate is not a field of CubeBlockBounds and remains separately needed by later I-4a work. NC1/NC2 from cut coercivity and Agmon bounds do not fill nc.

The folding argument below also assumes the standard large-torus condition $5M_1\ell_m<|\mathbb T|_{\rm side}$ for every interaction-box scale $m$. This discharges FoldSetting.side; the other arithmetic fields are $1\le q\le k$, $s>0$, and $L^q$ divisibility of the corner.

For $(C^\sharp,H^-)$ the geometric FoldSetting checks can be made box by box. At a top center $m=K$, choose folding scale $q=k$ and side $s=5M_1L$. The box plus one-site collar lies inside $W_k=\Omega_k(H^-)$: VMOD-2.md (1.1) gives distance $(r-2L-2)M\ell_k>3M_1L\ell_k+1$ from $A$ to $W_k^c$. The old top $\Omega_{k+1}$ is empty. For a lower center $2\le m\le k$, choose $q=\min(k,m+1)$ and $s=5L^{m+m_1-q}$. Its box and collar extend at most $3M_1\ell_m+1\le(3L+2)M_1\ell_{m-1}<5LM_1\ell_{m-1}$ from the center cell, so LFR II.2.2 places them in $\Omega_{m-1}(H^-)\subset\Omega_1(H^-)$. If a box point belonged to $\Omega_{m+2}(H^-)$, the same $5L$-cell recursion would force the center into $\Omega_{m+1}(H^-)$, contradicting its layer label. Corner and side divisibility follow from the aligned cell construction. These are the FoldSetting conditions in Balaban/Localization/ReflectedGeneratingSet.lean. At $m=1$ the recursion bounds source scales by $j'\le2$, the regime of Localization/NC3Small.lean.

Conditional on these geometric bridges being formalized, the proved NC3.lean pointwise_cut_cube, value_cut_cube, laplacian_cut_cube and the NC3Small estimates assemble nc with the same witness form as DecoupledCube.lean cubeBlockBounds_exists:
$$K_c=K_1+K_2+K_3+\operatorname{smallConst}(d,L)
+e^{\operatorname{agmonRate}(d)d}\bigl(1+4\operatorname{smallConst}(d,L)\bigr). \tag{3.2}$$
The three $K_i$ are the witnesses of the cited NC3 estimates. This is **conditional on proved cited results** and on a not-yet-landed Lean FoldSetting bridge; (3.2) is a target, not a landed mixed-instance declaration.

For $(C^\sharp,H^+)$ a proper physical island can put the Dirichlet wall inside a cover box. Then FoldSetting.mem_Ω and FoldSetting.collar are false. Reflecting that cut face as a Neumann face changes the physical operator, so the landed operator_intertwine cannot be used. A signed reflection would require a new theorem preserving the cut operator at every wall face and corner. The other sufficient route is a direct estimate (3.1) for the block-aligned cut of $H^+$ on $\operatorname{intBox}(q)$, uniform in $k,q,\alpha$, with the physical Dirichlet wall and mixed local layer bound. Call this **OPEN-NC3-MIXED-WALL**. No such repaired reflection or direct pointwise bound is in P3 §4, P6 §4, NC3.lean, or the landed Dec2 files. CutOperator.lean gives invertibility and weighted $L^2$ decay conditional on BlockAligned; finite-dimensional inversion then gives analytic dependence where invertible. It does not give (3.1). No wall constant $K_c^{\rm wall}(d,L)$ is presently justified.

## 4. CoverLocalGeom, row_mem_hat, and the remaining count

The exact locality fields are
$$\begin{array}{ll}
\texttt{idx_range}:&q\in C.\operatorname{cubeIdx}\Rightarrow1\le q.1\le K,\\
\texttt{idx_base}:&q\in C.\operatorname{cubeIdx}\Rightarrow\operatorname{CubeBase}(m_1,q.1,q.2),\\
\texttt{chi_supp}:&\chi_q(x)\ne0\Rightarrow x\in\operatorname{InBox}(q,3M_1\ell_{q.1}/2),\\
\texttt{cubeP_sub}:&q\in C.\operatorname{cubeIdx}\Rightarrow\operatorname{cubeP}(q)\subset\Omega_1(H),\\
\texttt{own_cover}:&x\in\Omega_1(H)\Rightarrow\exists q\in C.\operatorname{cubeIdx},\
x\in\operatorname{cubeP}(q).
\end{array} \tag{4.1}$$
The first three are proved for every coverOf F by Cover.lean mem_cubeIdx and inBox_of_chi_ne_zero. Equation (1.1) and alignment prove the last two for $(C^\sharp,H^-)$, using the own-cell argument in (1.3). For crossed pairs they jointly imply the unproved equality (1.3), so OPEN-EMBED-MIXED is not merely a one-sided inclusion lemma.

The exact row_mem_hat field says that for $x\in\operatorname{intBox}(q)\cap\Omega_1(H)$ and nonzero matrix entry $\operatorname{dirichletOperator}(H,a,\nu,\alpha)_{xy}$, the column site $y$ lies in $\operatorname{hatBox}(q)$. The explicit operator stencil permits only $y=x$, a nearest neighbor, or a point in the $H$-block of $x$. The hat adds $3L^2\ell_{q.1}$ to the box half-width. If $n_H(x)\le q.1+1$, the block displacement is $<L^{q.1+1}\le3L^2\ell_{q.1}$ and the neighbor displacement is one. Hence all cases lie in the hat. This is DecoupledFieldLocal.lean row_mem_hatBox with its same-set layer_le_of_mem_box call replaced by the proved old-pair local bound. For crossed pairs it is conditional on OPEN-LAYER-MIXED.

Dec2.HatConn C H is an additional premise of Decoupled2Geometry.lean dg5_local and dg5': every $\operatorname{hatBox}(q)\cap\Omega_1(H)$ must be nearest-neighbor connected. An internal wall can disconnect it. Neither CoverLocal nor nc implies HatConn; a crossed wall pair therefore also needs **OPEN-HATCONN-MIXED** or a componentwise replacement.

Finally, BlockCount.lean blockCount_fam proves
$$\operatorname{blockCountFam}(F,m_0,Y)\le
3^{d+1}L^{2d+1}\bigl(\operatorname{treeLenCov}(F,m_0,Y)+1\bigr) \tag{4.2}$$
under divisibility, a chosen family and connected tree witness, and $\varrho_F\ge4dLM$. The unchanged old interfaces of $F^\sharp$ have only $\varrho_3=5LM_1$. Since $M/M_1\ge14d$, $5LM_1<4dLM$; the new-interface halo does not change this. The direct $M_1$-scale overlap counts of §2 do not replace BlockCount.lean layer_near at the $M$ counting scale. **OPEN-BLOCKCOUNT-MINIMAL** is (4.2) for $F^\sharp$, or a proved version with a larger $C^\sharp_{d,L}$ propagated through the entropy and $M_1$ rows. No direct count with either constant is established here. This is an undischarged theorem binder, not a counterexample to (4.2).

## 5. Design decision and Lean order

The cheapest usable pairs with the current structures are $(C^\sharp,H^-)$ for the old fluctuation operator and $(C^+,H^+)$ for the new operator in arguments that permit separate covers. The latter is the self case, but its minimal-set hypotheses still need direct proofs. The P3 §4 / P6 §4 composite recorded in VMOD.md §3 uses one auxiliary interpolation family, so these separate pairs alone do not close I-5. Dec2 separates operator and cover algebraically; its *locality* structure still requires full parameter cells inside the operator domain. Prove equality (1.3) for the actual localized pair, or revise CoverLocalGeom and dg5' for clipped cells and their components before attempting a full crossed instance. Then establish OPEN-NC3-MIXED-WALL and the needed connectedness statement. NC3 alone cannot instantiate CoverLocal.

These are proposed Lean declarations, not landed ones. Estimates exclude the source-history definitions:

| Order | Proposed result | Reuse or exact obligation | Size |
|---|---|---|---:|
| 1 | auxHalo_top, auxHalo_subset_old, auxHalo_aligned | LFR II.2.2–II.2.3; CubeAligned | 500–900 lines |
| 2 | coverLocalGeom_domain_eq | own_mem_cubeIdx, mem_cubeIdx, mem_cubeP; (1.3) | 100–180 |
| 3 | minimal_sup_layer_near, minimal_card_box, minimal_card_qset | direct sup margin; card_cube_bases_inBox | 600–1,100 |
| 4 | aux_old_layer_compare, aux_old_box_layer, aux_old_inner_layer | (2.1) and $5L$ recursion | 400–700 |
| 5 | mixed_box_blockAligned, mixed_inner_near, mixed_chi_smooth, mixed_row_mem_hat | box_sameCell, inBox_cov4, quotient algebra, inBox_hat_of_add_int | 900–1,500 |
| 6 | coverGeom_aux_old, coverLocalGeom_aux_old | fields of §§2, 4 | 250–400 |
| 7 | aux_old_foldSetting, aux_old_nc, coverLocal_aux_old | FoldSetting, NC3.lean, NC3Small.lean; (3.2) | 800–1,500 |
| 8 | mixed_wall_cubeBounds and two-center Hölder | OPEN-NC3-MIXED-WALL | unknown, substantial |
| 9 | coverLocal_clipped and componentwise dg5', if equality fails | replace cubeP_sub use and HatConn | unknown, substantial |
| 10 | blockCount_minimal | OPEN-BLOCKCOUNT-MINIMAL; $M$-scale layer count | 1,000–2,000+ |

**Proved here:** the necessary-domain theorem (1.3), the fieldwise finite-grid implications under the displayed geometric hypotheses, and the failed application of blockCount_fam. **Proved conditional on proved cited results:** the haloed old-pair geometric fields and foldable-box argument, using LFR II.2.2–II.2.3 and the landed reflection and small-scale estimates. **Conditional on OPEN assertions:** a crossed CoverLocal instance, the internal-wall cube and Hölder estimates, clipped-cell locality, HatConn at a wall, and the minimal-set block count. Confidence is high for the exact-type obstruction and elementary counts, medium for the old-pair reflection assembly until its Lean bridge is written; no confidence claim is made for an unproved wall constant or (4.2) on minimal sets.
