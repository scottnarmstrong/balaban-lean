# VMOD-43: P5 boundary size and the fine chosen-cover size

**Verdict.** **PROVED for an explicitly aligned open-to-fine lift:** the inequality needed to pass a P5 H7 bound to the fine D7 size holds with $a_*=1/(8\,3^d)$ and $b_*=1/4$. **OPEN for actual D7 labels:** the required open-domain lift and complement-component identification have not been proved in Lean. A two-sided comparison with P5 is not established. A
two-sided comparison of two *fine* sizes is proved below.

## 1. The two normalizations

**PROVED (PDF pages checked).** P1 (2.26)–(2.27), printed p. 117, makes $\pi'_k$ the cover by open cubes of side $LM$ in the scale-$k$ lattice, translated on the $M$-cube grid;
consecutive translates overlap in a strip of width $(L-1)M$ for $L>1$. P5 (1.33)–(1.34), printed p. 496, requires $X\in\mathcal D_k(\mathrm{mod}\,\Omega^c)$ and sets
$$D_P(X,\Omega)=\inf_{\Gamma\subset X^\circ}M^{-1}|\Gamma|_\eta,\qquad \eta=L^{-k},$$
where $\Gamma$ is a connected continuous tree meeting **every** open $\pi'_k$ cube meeting $X^\circ\cap\Omega^\circ$. The cube need not be contained in $X^\circ$. The component rule
says each continuum component of $(\Omega^\circ)^c$ is contained in $X^\circ$ or disjoint from it.

**PROVED (landed declarations checked).** Set $M=L^{m_0+m_1}$ and $a_k=ML^k=L^{m_0+m_1+k}$ fine sites. `Fluctuation/SizeModDefs.lean:ModAdmissible` chooses aligned half-open boxes
$B_b=\texttt{box}\ b\ (La_k)$ with $B_b\subset X_f$ and $X_f\cap\Omega_f\subset\bigcup_{b\in\mathcal K}B_b$; it chooses a connected NN graph $(W,E)$ in $X_f$ meeting each chosen box.
`dcovModE` minimizes $|E|/a_k$, since `Localization/TreeLength.lean:scaleW` gives weight $a_k^{-1}$ to every bond. `dcovMod` is its finite real value;
`LargeField/Def7FineSize.lean:d7SizeAtE`, `d7SizePreE`, and `d7SizeE` pull it to the history's fine torus at the specified region. In fine coordinates $|\Gamma|_\eta/M=\ell_f/a_k$,
where $\ell_f$ is Euclidean length measured in fine-site units. This is a unit conversion, not an identification of trees or domains.

## 2. A fine all-eligible surrogate

Define $\mathcal Q(X_f,\Omega_f)=\{b:\ b\text{ is }a_k\text{-aligned},\ B_b\cap(X_f\cap\Omega_f)\ne\varnothing\}$, with **no** requirement $B_b\subset X_f$. Let $D_A$ be the infimum
of $|E|/a_k$ over connected NN graphs in $X_f$ meeting every $B_b$, $b\in\mathcal Q$. This matches P5's “which intersects $X\cap\Omega$” incidence after an aligned lift. Requiring
`ModAdmissible`'s chosen family to equal $\mathcal Q$ is ill-typed mathematically when an eligible box crosses $\partial X_f$: `ModAdmissible` requires each chosen box to lie inside
$X_f$.

**PROVED (fine lower comparison).** If `IsDj m₀ k X_f`, the subfamily of eligible boxes **contained** in $X_f$ covers $X_f\cap\Omega_f$. A graph for $D_A$ meets this subfamily and
gives a `ModAdmissible` witness. Hence $\Delta:=\mathrm{dcovMod}(X_f,\Omega_f)\le D_A$. This does not need the component rule.

**PROVED (fine upper comparison, conditional only on the stated landed hypotheses).** Assume `DjMod m₀ k Ωf Xf`, `IsPiUnion m₀ k Ωf`, $k\le K$, and $L^{m_0}\mid N_1$. Put
$c_1=[3(2L-1)]^d$, the landed `Fluctuation.c1` (`SizeModCore.lean`). `SizeModG1.lean:G1_cellCount` and `exists_admissible_eq_dcovMod` give a minimizing chosen graph and at most
$c_1(1+\Delta)$ active $a_k$-cells. For each such cell $C$, choose $z_C\in C$ and a chosen box $B$ covering it. Alignment makes $C\subset B$; join $z_C$ to the graph's hit in $B$ by
at most $dLa_k$ NN bonds, all in $X_f$. Every aligned box meeting an active cell contains that entire cell, hence meets the enlarged graph at $z_C$. Therefore
$$\Delta\le D_A\le(1+dLc_1)\Delta+dLc_1.\tag{2.1}$$
The bound uses landed G1 only in the **reverse fine comparison**; it is not used to infer $\Delta$ from a paper tree. Formula (2.1) is a mathematical proof of a modular fine analogue of
`Localization/TreeLengthPaper.lean:treeLenAll_le`; the modular wrapper `D_A` and its Lean theorem have not landed.

## 3. Continuous tree to a fine graph

**PROVED CONDITIONAL ON `OPEN-ALIGNED-LIFT-IDENTIFICATION`.** Suppose $X^\circ$ is exactly a union of open $a_k$-aligned cover cubes of side $La_k$, $X_f$ is the union of their
corresponding half-open $a_k$-cells, and the active sets and eligible cubes correspond cell by cell. Let $\Gamma\subset X^\circ$ be a finite rectifiable tree of fine-coordinate length
$\ell_f$ meeting every P5-eligible open cube. Let $V$ comprise all aligned $a_k$-cells whose closures meet $\Gamma$.

**PROVED (noncircular covering bound).** Every $C\in V$ lies in $X_f$: at a contact point $q\in\Gamma$, an open cover cube contained in $X^\circ$ contains $q$, and all incident
aligned $a_k$-cells lie in that cube. The face-adjacency graph of $V$ is connected: crossing a face gives adjacent cells, while a simultaneous crossing of several faces has all
incident cells in the same open cube and supplies a face-adjacent bridge. Traverse each edge of $\Gamma$ twice and sample at arc-length increments at most $a_k/4$. There are at most
$8\ell_f/a_k+2$ samples; each radius-$a_k/4$ ball meets at most $3^d$ aligned cells. Thus $|V|\le3^d(8\ell_f/a_k+2)$.

**PROVED (graph and incidence).** Join representative fine sites of a spanning tree of the face-adjacency graph of $V$ by $a_k$ NN bonds per cell edge, inside $X_f$, and prune
redundant bonds. Its normalized cost is at most $|V|-1$. If $\Gamma$ meets an eligible open box, the contact point lies in an aligned cell contained in that box, so its representative
is in the matching fine box. Thus the graph meets **all** boxes in $\mathcal Q$, and
$$D_A\le 8\,3^d D_P+2\,3^d,\qquad
\Delta\le8\,3^dD_P+2\,3^d.\tag{3.1}$$
Take the infimum over $\Gamma$; no minimizing paper tree is required. Equivalently,
$$D_P\ge a_*\Delta-b_*,\qquad a_*=(8\,3^d)^{-1},\quad b_*=1/4.\tag{3.2}$$
As a separate noncircular cell count, every active $a_k$ -cell lies in an eligible open box met by $\Gamma$, so it lies within sup-distance $La_k$ of $\Gamma$. The same samples give
$n_\pi(X\cap\Omega)\le(2L+4)^d(8D_P+2)$. This count is not needed for the sharper construction (3.1).

**OPEN (actual paper-to-D7 application).** `FineSizeFrame.hM` supplies $M=L^{m_0+m_1}$, and `d7Pull` supplies a torus cast, but no landed theorem identifies every P5 open box, every
active cell, or the exact $X^\circ$ with that pullback. `OPEN-ALIGNED-LIFT-IDENTIFICATION` is therefore a genuine premise of (3.1). Continuum components of the closed complement may
meet at a corner while fine NN components do not; `OPEN-MOD-COMPONENT-COMPAT` must separately identify the P5 whole-component rule with `Fluctuation.DjMod` for the actual histories. A
bare `FineValid` or a coarse `DmodOmega` assertion does not prove these premises. Accordingly `OPEN-PAPER-FINE-REALIZATION` for the actual D7 records remains **OPEN**, although its
quantitative geometric step is proved above.

## 4. Reverse direction and D7 constants

**PROVED for the fine surrogate; OPEN for P5.** Equation (2.1) is the reverse comparison $D_A\le A'\Delta+B'$ with $A'=1+dLc_1$, $B'=dLc_1$. It does **not** imply $D_P\le A'\Delta+B'$
without a fine-graph-to-open-tree theorem. A half-open NN edge can cross a face omitted by a union of open cover cubes, even when that open union is connected by a remote route. For
example, two long open strips made of side-$La_k$ cubes can touch along such a face and join only at their far end; their half-open cell lifts admit a short cross-face bond. This
**REFUTES the proposed edge-by-edge reverse construction** from an arbitrary open-union lift. With $\Omega$ restricted by P5 (1.33), such a strip must also satisfy the
whole-complement-component rule; this illustration alone does **not** refute a reverse bound on valid modular labels. That bound is **OPEN**. The reverse inequality is not needed to transport H7 to the fine D7 bound: (3.2) suffices after rebasing.

**PROVED (entropy implication with matched labels).** Equation (2.1) gives $\Delta\ge(D_A-B')/A'$, hence $e^{-\lambda\Delta}\le e^{\lambda B'/A'}e^{-(\lambda/A')D_A}$ for $\lambda\ge0$. A corresponding P5 reverse bound would permit transfer of P5 (1.35) at a suitable rate after the labels and root cubes were identified. It is not needed to use the landed
`G1_cellCount`, `SizeModEntropy.lean:G2_X`, or active-overlap `SizeModUnion.lean:G3_dcov`; those already hold for the fine size under their own hypotheses.

**PROVED CONDITIONAL ON (3.2) and matching analytic domains.** P5 H7 $|B(X)|\le B_0e^{-\kappa D_P}$ yields
$$|B(X)|\le B_0e^{\kappa/4}\exp[-\kappa\Delta/(8\,3^d)].\tag{4.1}$$
For a source bound $B_{\rm st}e^{-3\kappa D_P/2}$ the corresponding pair is $(B_{\rm st}e^{3\kappa/8},\,3\kappa/(16\,3^d))$. `LargeField/Def7.lean:D7BdryPost` and
`Def7v2Class.lean:D7Bdry2Post` take `fac rate` as arguments, so their `fac` absorbs the exponential prefactor and `rate` takes the reduced decay. The enclosing `IsRep`/`IsRepPre` use
the pinned `Consts7.B0`, `Consts7.Bst` and $\kappa$, $3\kappa/2$; retaining those numeric constants needs a separate source-rate reserve or a revised budget. The size bridge alone
does not establish the physical class, its support clause, or H7 analytic-domain transport.

## 5. Lean work in dependency order

1. `Fluctuation/SizeModAllDefs.lean` (120–190 lines, **OPEN**): define `eligibleCover m₀ k Ω X` without a box-containment condition, and `dcovModAllE` as the infimum over NN graphs in $X$ meeting it. Prove `dcovModE_le_dcovModAllE` for `IsDj` by selecting all contained eligible boxes.
2. `Fluctuation/SizeModAllCompare.lean` (180–280 lines, **OPEN**): under `DjMod`, `IsPiUnion Ω`, $k\le K$, $L^{m_0}\mid N_1$, prove finiteness and the real inequality (2.1). Reuse `SizeModG1.G1_cellCount`, `SizeModCore.c1`, and `exists_admissible_eq_dcovMod`; add one active-cell extension lemma.
3. `LargeField/D7PaperSizeRebase.lean` (80–150 lines, **OPEN**): with an explicit input $D_P(X)\ge a\,\mathrm{d7SizeAt}(\Omega,X)-b$, $a>0,b\ge0$, prove $|B(X)|\le B_0e^{\kappa b}e^{-\kappa a\,\mathrm{d7SizeAt}}$, and its $3\kappa/2$ version, for finite valid labels. This is algebra, not a proof of the input.

**Modelling obligation, not a landed Lean identity.** Establish for the actual open realization of each D7 label the aligned lift and component compatibility above. The continuous P5
functional and the NN surrogate are **not literally equal**; (3.1) is the proved conditional affine bridge. Calling the remaining domain identification “small” would hide the open
complement-topology issue. Confidence: high for (2.1), the conditional proof (3.1), and the rate rebase; unresolved for actual-history lift and the P5 reverse comparison.
