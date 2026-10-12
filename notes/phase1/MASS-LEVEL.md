# The mass level in the small-field data domain

The finding is correct, with an important qualification. P1's level-$j$ space uses the dimensionless mass $\nu_j$ in its condition on $h^2-1$. The landed `InPsiTilde` uses $\nu L^{2k}=\nu_k$, where $k$ is the ambient top index of the generating set. That is faithful to P2's **top-$k$** background domain, and the landed theorem `xiC_subset_psiTildeC` is valid as written because its premise is `XiC ... ν k ...`. It is not the level-$j$ D1 inclusion needed for an old term with $j<k$ and a nonunit real witness $h_0$.

This does not alter the physical pinned-field conclusion of `Q13-ANSWER.md`. If the real witness is the fixed real unit vector $h_*$, both norm conditions vanish exactly. If the background mass is zero below $k_0$, both vanish regardless of $h_0$. Above the switch, using $h_0=h_*$ removes this particular discrepancy. It does **not** remove Q13's transverse complex-source obstruction: the complex displacement $h''$ is controlled by other clauses and can still encode the counterexample on the wider, mass-uniform domain.

## 1. Source and normalization

On the page image of P1, p. 123, (3.13), the last real condition is, exactly,
$$|\nu_j(h^2-1)|<\sigma^2\varepsilon^2.$$
The preceding condition on the same line is $|\nu_j(1-(\psi_j)_0\cdot h)|<\sigma^2\varepsilon^2$. P1 p. 124, (3.18), again defines the auxiliary $\widetilde\Psi_j(\delta)$ with $|\nu_j(h^2-1)|<\delta^2$; its complex extension (3.19) weights $h'$ by $\nu_j$. The text immediately after (3.19) says that in the cross-scale application "$\nu_j=\nu_k(L^j\eta)^2$". Thus these are level-$j$ conditions even when the configuration being evaluated originated at step $k$. P1 p. 123, Lemma 3.1 (3.16), is the level-$j$ inclusion $\Xi_j^c(\sigma,\varepsilon)\subset\Psi_j^c(3\sigma,\varepsilon)$.

P1 p. 115, (2.20) also says the *real* $h$ in its original $\Xi_j$ belongs to the unit sphere. For those original real points, the norm condition is automatic. The Lean `Xi` permits nonunit real witnesses subject to a quantitative norm condition, which is useful for a larger analytic domain but makes the mass index material. The P1 formulas above still specify which mass a level-$j$ generalization must use.

P2 p. 610, (1.11) defines a domain on a generating set $\mathbb B_k$ whose norm clause is $|\nu(|h|^2-1)|<\delta^2$; the layerwise alignment clause has the factor $(L^j\eta)^{-2}$ on its right side. Here P2's $\nu$ is the dimensionless mass at the ambient top level $k$. In the landed fine-lattice coordinates this is $\nu L^{2k}$, while at a layer $j$ it is $\nu L^{2j}$. Thus `Background/Data.lean` lines 259–268 faithfully records P2 (1.11) for an actual top-$k$ domain. It is not, merely by taking $\Omega_i=\varnothing$ for $i>j$, a transcription of P1's $\widetilde\Psi_j$.

## 2. The landed statements and the gap

Write $M_r=\nu L^{2r}$, so $M_j=M_kL^{-2(k-j)}$ for $j\le k$. In `Background/Data.lean:262–268`, `InPsiTilde G ν δ Ψ h` has
$$\texttt{r4}:\quad M_k\left|\sum_i h_i^2-1\right|<\delta^2.$$
Its `r3` and the complex `c3a`, `c3b` use the *site's layer index*; this audit concerns `r4`. In `SmallField/Xi.lean:75–91`, `XiBounds G ν n σ ε` instead has
$$\texttt{hnorm}:\quad M_n\left|\sum_i(h_0)_i^2-1\right|<(\sigma\varepsilon)^2.$$
`XiAt` also requires the real background union domain (`Xi.lean:106–109`), so it imposes a separate **fixed BG-radius** top-$k$ condition. That fixed radius is not the shrinking $C\sigma\varepsilon$ required by D1.

The theorem `SmallField/XiProps.lean:58–68` assumes `XiC G a ν k σ ε` and concludes `InPsiTildeC G ν (C_1\sigma\varepsilon) ε`, with $C_1=(4d+8)(2d+1)$. It is correctly typed and proved for $n=k$. In the proof, `XiD1.lean:257–264` establishes `r4` directly from `hb.hnorm`; `XiReal.lean:185–194` compares every layer mass with $M_k$. Replacing the theorem's premise by `XiC ... ν j ...` while leaving its conclusion unchanged would invalidate precisely that comparison and final `r4` step.

In the draft class, `SmallField/Def6Terms.lean:86–92` defines `XiDom G a ν j ε` through `XiC G a ν j 1 ε`. `SmallField/Def6.lean:210–220,265–269` uses this domain for level-$j$ terms with `G = Tm.gs j X`, whose *type* retains ambient top index $k$; `Def6.lean:235–256` likewise uses `levelGS j`, whose type retains $k$ (`Def6Terms.lean:51–61`). Hence the landed top-level theorem does not apply to those `XiDom` premises when $j<k$. The `analyticE`/`analyticM` clauses themselves are meaningful assumptions; what fails is an automatic D1 bridge from their level-$j$ `XiDom` to P2's `InPsiTildeC G ν` at radius $C_1\varepsilon_j$.

The failure can be seen from the scalar field-norm conditions alone. Let $s=L^{-(k-j)}$, $M_k>0$, and set $h_0=\sqrt{1+t}\,e_1$ with $t>0$. Take
$$t=\frac{2C_1^2\varepsilon^2}{M_k},\qquad 2C_1^2s^2<1.$$
Then $M_j|h_0^2-1|=2C_1^2s^2\varepsilon^2<\varepsilon^2$, as required by the `XiBounds` norm clause at $j$, whereas $M_k|h_0^2-1|=2C_1^2\varepsilon^2>(C_1\varepsilon)^2$, contradicting the target `r4`. Take the whole-lattice `levelGS j`, constant spin datum $\Psi_0=e_1$, fixed $M_k\in(0,1]$, and sufficiently small $\varepsilon$. The unique real background is $\phi=e_1$: the block penalty and gradient terms are minimized there, and the positive radial field $h_0$ has its unique sphere minimum there. Its multiplier is $\alpha=\nu(\sqrt{1+t}-1)$. Thus its gradient, Laplacian, collar, and data-close bounds vanish; its scaled multiplier and field-distance bounds follow from $M_jt<\varepsilon^2$ after reducing $\varepsilon$ if needed. The separate fixed BG-radius condition holds because $M_kt=2C_1^2\varepsilon^2$ tends to zero. The zero complex displacement supplies a member of `XiC` as well. This gives the nonunit-witness counterexample to the proposed top-$k$ D1, under the standard positive-weight and mass hypotheses, and shows why the fixed BG-domain requirement does not supply the missing shrinking inequality.

## 3. Correct D1 and the implementation choice

The source-faithful level-$j$ target is a data predicate $\widetilde\Psi^c_{j\mid k}(G;\delta,\varepsilon)$ on the existing fine torus. It has the same real and complex clauses as `InPsiTildeC`, except that `r4` reads
$$M_j\left|\sum_i(h_0)_i^2-1\right|<\delta^2.$$
For a generating set with no active layers above $j$, the sitewise `r3`, `c3a`, and `c3b` already have the appropriate local masses. With the same numerical smallness assumptions as `xiC_subset_psiTildeC`, the corrected local D1 is
$$\Xi_j^c(G;\sigma,\varepsilon)\subset
\widetilde\Psi^c_{j\mid k}(G;C_1\sigma\varepsilon,\varepsilon),
\qquad 1\le j\le k,\quad \Omega_i=\varnothing\ (i>j).\tag{D1-j}$$
This is a **proposed generalization**, not a landed Lean theorem. Its proof is the `XiD1`/`XiD1C` argument with `n=j`: `hnorm` proves the new `r4`; for an active site $x$, $\operatorname{layerIndex}(x)\le j$ replaces `XiReal.hnorm_layer`'s comparison with $k$; collar sites have index zero. The remaining real estimates are `XiD1.xi_compHyp`, `xi_unit`, the collar estimates and `re_r2`/`re_r3`; the complex estimates are `XiD1C.xiC_inPsiTildeC` after the same index change. This is a precise proof reduction. P1 Lemma 3.1 has constant $3$ in its single-scale normalization; $C_1$ is the larger constant established for the landed multiscale predicates.

If the *existing* P2 top-$k$ target is required, the honest statement is instead
$$\Xi_j^c(G;\sigma,\varepsilon)\ \cap\
\left\{M_k|h_0^2-1|<(C_1\sigma\varepsilon)^2\right\}
\subset\widetilde\Psi^c_k(G;C_1\sigma\varepsilon,\varepsilon),\tag{D1-top}
$$
subject to proving the generalized non-`r4` estimates just named. The extra condition is automatic if $j=k$, $\nu=0$, or $|h_0|=1$. It is **not** automatic merely because $j<k$ layers above $j$ are empty. One cannot fix this by replacing $\nu$ with $\nu L^{-2(k-j)}$ in the existing predicate: that also weakens `r3` and `c3` at every active layer and changes the background variational problem.

For a faithful level-$j$ class, use (D1-j) together with a level-$j$ version of the P2 background-domain and inclusion theorems, or genuinely rebase the local generating set and its data so its top scale is $j$. The present `XiAt` still calls `InUnionDomainR G ν` at ambient $k$; this extra top-radius requirement should be distinguished from the source's $\Psi_j$ radius and audited in the domain transport. Merely changing `r4` in `InPsiTilde` globally would break its P2 top-$k$ meaning.

In particular, references to a direct `XiDom` $\to$ `InPsiTildeC` bridge for $j<k$ in `FLUCTUATION.md` §3.6 and `LF-RECONSTRUCTION.md` must specify either (D1-j) and a compatible level-$j$ background theorem, or the additional top mass condition of (D1-top). The existing `xiC_one_subset` and `xiC_subset_psiTildeC` remain valid for their literal $n=k$ premises. The fixed-witness $h_0=e_1$ construction in `FLUCTUATION.md` §3.6 has `r4=0` and is unaffected by this field-norm issue.

## 4. Interaction with Q13 and the frozen root

The pinned scheme in `Q13-ANSWER.md` keeps the physical mass $m_j$ in the action and takes the background mass $\mu_j=0$ below $k_0$. In that branch `r4` is $0<\delta^2$ for every real $h_0$; no mass-level choice arises for the solver's domain. At and above the switch choose the real witness $h_0=h_*$, with $|h_*|=1$, and encode analytic variations in $h''$. Then `r4` vanishes at both $j$ and $k$. The level-$j$ complex field clauses still need their own strict margins, and inherited compositions need the level-aware domain transport stated as PIN-COMPOSE/SWITCH. This audit neither proves nor weakens that open estimate.

The Q13 one-block transverse-source tests take $h=h_*+h''$ with $h''_\perp=q/m$ and the **real witness** $h_0=h_*$. Their `r4` is already zero. Hence correcting the `r4` index does not exclude those tests from a mass-uniform complex domain and cannot by itself repair the switch. The frozen root `Balaban/Frozen/Roots/LogPartitionMultiscale.lean` has a fixed real unit $h$ and complex observable source $g$; its statement is unaffected by the nonunit-$h_0$ mismatch. A proof through the wider class still needs the restricted-field or resummation work identified in Q13.
