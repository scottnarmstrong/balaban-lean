# DETFOREST: what the landed cut family proves, and the exact missing estimate

13 October 2026. Scope: one finite torus, $K=k+1$, the **fixed-field** rooted trace of `Fluctuation/RootDetChart.lean`, followed by the physical datum chart. The read-only repository was at commit `c8c5a07d752db5c5363e98ba91568d96ac3e8b8d`. For reproducibility, SHA256 of `RootDetChart.lean` is `fdd267422919680a1f12305cd7bdda5661048b050a08e0564e7ad61432338fe2`, of `DecoupledX.lean` is `9b9a9bcdb923b95fc81e0867aee3f8d23498c34c6c16b4c190dfbc29adec8d4b`, and of `DecLogZero.lean` is `dce6a16e3d7e880bd345bf6f53a5f8ef335d63e254b8638a8e3a091578d09920`. Statuses below distinguish mathematical algebra, landed Lean theorems, conditional deductions, and unproved estimates. No repository file was changed.

## 1. Exact cut algebra

**PROVED.** Write $t_q(s)=\prod_{P\in Qset(q)}s_P$, $U_q=\chi_qG_{q,x}c_q$, and $V_q=K^x_qG_{q,x}c_q$. Then, exactly by `Localization/DecoupledX.lean` (`Gstarx`, `Kcalx`, `Gsx`),
$$U_s=\sum_qt_qU_q,\quad V_s=\sum_qt_qV_q,\quad G_s=U_s(1-V_s)^{-1}.\tag{1}$$
Thus **REFUTED** is the assertion that the *full* decoupled Green operator is merely a sum of local $\chi_qG_q\chi_q$ terms. That sum is $U_s$; the right inverse creates chains. The only direct cut dependence in (1) is through the scalar $t_q$, for fixed $\alpha$.

**PROVED.** Let $H_x$ be `xDirichletOperator`, $\Phi=\operatorname{fieldMul}(\phi)$, and $C_\phi=\operatorname{commK}(H_x,\phi)$. By `Multiscale/Constrained.lean` (`constraintM`, `constraintN`) and `Localization/DecoupledCovariance.lean` (`decM`, `decN`, `decPi`),
$$M_s=\Phi^T\Phi-C_\phi\widehat G_s\Phi,\quad N_s=\Phi^T-C_\phi\widehat G_s,\quad
\Pi_s=\widehat G_s\Phi M_s^{-1}N_s.\tag{2}$$
Here the hat lifts $G_s$ to $N$ components. Put $A_x=\operatorname{covA}(a_k,a_T/L^2,x,\widehat P)$ and $c_k=a_k^2/L^{2k}$. `Localization/DecoupledCovBound.lean` (`decCov`) and `DecLogZero.lean` (`decCov_zeroCuts`) give the **exact** identity
$$C_x(s)-C_x(0)=c_k A_x\widehat Q\,[\widehat G_s-\Pi_s]\,\widehat Q^T A_x.\tag{3}$$
At $s=0$ all $t_q$ in the sums vanish because $q\in Qset(q)$ (`self_mem_Qset_zeroCuts`); $G_0=\Pi_0=0$. `decLog_zeroCuts` gives the explicit $P$ baseline, independent of $\phi,\alpha,Q$.

**PROVED CONDITIONAL ON an absolutely convergent inverse expansion.** Expand $(1-V_s)^{-1}=\sum_{r\ge0}V_s^r$, and expand $M_s^{-1}$ around $M_0=\Phi^T\Phi$. Each monomial in (3) has factors $t_{q_1}\cdots t_{q_r}$; its mixed difference $\Delta_J$ vanishes unless $J\subseteq\bigcup_i Qset(q_i)$. At cut values $0,1$, for $J\ne\varnothing$, the monomial contributes only if every $Qset(q_i)$ is inside $J$ **and** their union covers $J$. This follows directly from the product definition of `Analysis/CutExpansion.lean` (`mixDiff`) and `DecLogZero.Qset_subset_of_mem_Zs`. An inverse expansion of $M_s$ with a norm and support ledger has not landed; (3), unlike that expansion, needs no inverse-series assumption.

## 2. Connectedness and the proposed small factor

**OPEN — DET-CUT-FACTOR (exact failing statement).** For every real cut configuration supported on $J$, prove that the *whole correction* $\widehat G_s-\Pi_s$ in (3), after the $Q$ lifts and the $P$ baseline, is block diagonal over nearest-neighbour components of `Dec2.Yreg s`, and that a root diagonal entry reads only its component. The corresponding assertion must hold for all endpoint subsets $I\subseteq J$; a derivative proof needs a neighbourhood of each partially cut configuration. `Decoupled2Geometry.dg5_support/dg5_local` concern $G_s$ only; they do not establish locality of $M_s^{-1}$, $\Pi_s$, $Q$, or $P$. The worker's `DecCovCutSupport.lean` may discharge a portion, but was not present in the read-only tree inspected here.

**PROVED CONDITIONAL ON DET-CUT-FACTOR and a footprint-to-graph lemma.** If the rooted value depends only on its cut component for every $I\subseteq J$, pair endpoint subsets differing at any $P$ in a component disjoint from the root. The paired terms cancel in $\Delta_J$. Hence every surviving component of $J$ must meet the root component. The operator adjacency is nearest-neighbour overlap of the active `hatBox` sets; a *counting* graph may connect two cut indices when they occur in one $Qset(q)$ or their associated interaction boxes touch. The implication to the landed Moore graph `MooreDegree.mooreGraph` needs a separate geometric bridge. In particular, treating $Qset(q)$ as one Moore vertex, or claiming Moore connectedness from `dg5_local` alone, is **REFUTED** as an inference.

**PROVED.** `DecoupledXBounds.dg1x` bounds $V_s$ in weighted source norm uniformly in $x\ge0$ by $1/4$ on the complex cut polydisc under $cstarX e^{N_0\kappa}\le M_1=L^{m_1}$. Its proof yields at real cuts the unsaturated norm factor
$$\theta_K(0)=18(3\cdot5^d)\sqrt{\operatorname{commXConst}(d,L)}\,C_\chi(d,L)/M_1,\tag{4}$$
and $\theta_K(\kappa)=e^{N_0\kappa}\theta_K(0)$ on the complex polydisc. `Decoupled2Dg.Kz_cube_weighted` gives the analogous one-centre $B_K/M_1$ bound. Formula (4) pays for a $V_q$ insertion, **not** for a first $U_q$ insertion.

**REFUTED (as a deduction from these inputs).** A bound $|\Delta_JF_B|\le C^{|J|}q^{|J|}$ with $q=O(M_1^{-1})$ does not follow from (4). A single $U_q$ carries all of $Qset(q)$, with $|Qset(q)|\le N_0=3(8L)^d$ (`Localization/Cover.card_Qset_le`), and has no $M_1^{-1}$ prefactor. Also $M_s^{-1}$ can propagate through $C_\phi\widehat G_s\Phi$ without a $V_q$ insertion. `DecoupledCovariance.decM_error_le/decM_inv_le` supplies a norm contraction at most $1/2$ under $\delta^2\operatorname{smallConstX}\le1/4$, but no decay in $M_1$. At $d=L=3$, $N_0=41472$. The toy monomial $c\prod_{P\in Qset(q)}s_P$ has $\Delta_{Qset(q)}=c$; it refutes the *purely algebraic* per-cut inference, without claiming to be a counterexample to the physical trace.

**REFUTED (as a deduction from spatial decay alone).** The `GreenFamily` rate $\gamma_1/8$ and `Localization/DecoupledCovWeighted.I4c_close_log_entry` give weighted spatial decay or closeness to full coupling. Two Moore-adjacent patches can touch, so they have zero separating distance; these theorems do not give $e^{-\gamma_1M_1/8}$ for every tree edge. The cited weighted-log theorem is an entrywise comparison with $s=1$, not a bound on a mixed cut difference.

**PROVED (decision about the mechanism).** Option (i) supplies a real-cut small factor only for commutator links $V_q$. Option (ii) can pay for a link only after a positive separation is established. Neither pays for every cut patch. A valid bound must combine the two and explicitly charge the remaining constraint links; that combined estimate is DET-FOREST-X below.

**PROVED (scope of the analytic estimate).** `RootDetChart.rootTrace_cut_expansion` and `CutExpansion.norm_mixDiff_le` give $|\Delta_JF_B|\le M_B(2e^{-\kappa})^{|J|}$ with $M_B=\tfrac12N|B|\operatorname{covBLog}$. But `covBLog` contains a term growing with $e^{N_0\kappa}$ and $cstarX e^{N_0\kappa}\le M_1$ caps $\kappa$ for fixed $m_1$. This total bound carries no footprint, so even a small $2e^{-\kappa}$ cannot supply DET-CUT-FACTOR or a fixed-hull estimate.

**OPEN — DET-FOREST-X (repair).** Prove a termwise, rooted expansion of the *constrained* correction (3), uniform in $x\ge0$, with a forest $w$ whose hyperedges are the actual $Qset(q)$ and whose links include both $V_q$ and the $M_s^{-1}$ transitions. Require a finite-range rooted footprint, exact reconstruction, and a bound
$$|w_x|\le C_0(a_k+x)^{-2}\exp[-\mu n(w)]\exp[-\eta\ell(w)],\tag{5}$$
where $n(w)$ counts paid links, $\ell(w)$ is a tree length in patch units, $\mu,\eta>0$ are explicit, and no uncharged $U_q$ or constraint transition is counted as a paid link. For every assigned coarse hull require $dExt(T)\le a n(w)+a_\ell\ell(w)+b_0$, and a weighted fibre bound $\sum_{w:T(w)=T,\,n+a_\ell\ell/a\in[r,r+1)}1\le C_Ee^{\sigma r}$ with constants independent of torus size. Equivalently one can formulate (5) directly with one integer cost $r(w)$ and $dExt(T)\le ar(w)+b_0$ as in `ROOTDET.md` (D7). This is the missing estimate, rather than a consequence of `dg1x`.

**PROVED CONDITIONAL ON a stronger paid-centre lemma.** If, after one root anchor, *every* further centre in every constrained chain costs at most $\theta<1$, and each centre covers at most $N_0$ cut indices, then $r\ge\lceil |J|/N_0\rceil-1$. The resulting candidate per-cut factor is $q=\theta^{1/N_0}$, with an anchor prefactor $\theta^{-1}$. Taking $\theta=\theta_K(0)$ requires a new proof that constraint links and local overlaps have the same cost; it is **OPEN**. The landed $1/2$ contraction of $M_s^{-1}$ alone guarantees no better factor than $q=2^{-1/N_0}$, far too close to $1$ for the requested entropy test. If the stronger lemma held with $\theta=A/M_1$ ($A>0$ independent of $m_1$), the **exact sufficient numerical condition** would be
$$D^2e^{\kappa'}(A/L^{m_1})^{1/N_0}<1
\quad\Longleftrightarrow\quad
m_1>{N_0(\kappa'+2\log D)+\log A\over\log L},\quad
D=\max\{3(L+4)^d+1,\,3^d(L^{m_0})^d\}.\tag{6}$$
Here $A$ must include the actual link and hyperedge counting losses. For (4), $A=54\,5^d\sqrt{\operatorname{commXConst}}C_\chi$ before those losses. `StepRatesDirect.stepRates_direct_witness` fixes $\kappa'=3\kappa_{dec}/2+\kappa_0+1$ but imposes no (6); `RootDetChart.rootDet_hypotheses_nonempty` takes $m_1=m_0+N_0$ and $\kappa=\log3$, which likewise does not imply (6). Thus the lower bound is a *new* parameter requirement, not one already forced by the landed hypotheses.

**PROVED (integrability); OPEN (forest uniformity).** `DecoupledSqrt.CovStanding.entry_decCov_sub_le` bounds the integrand of `decLog` by $\operatorname{covB4}(a_k+x)^{-2}$; $a_k>0$, and its integral is $\operatorname{covB4}/a_k$ (`decLog_bound`). Finite mixed differences commute with this integral. For $J\ne\varnothing$ the baseline cancels and
$$\Delta_JF_B={1\over2}\int_0^\infty\operatorname{Tr}_B\Delta_J(C_x-C_x(0))\,dx.\tag{7}$$
The sign follows from $F_B=-\tfrac12\operatorname{Tr}_B\operatorname{decLog}$ and `decLog = baseline - integral`. Estimate (5), with its $(a_k+x)^{-2}$ factor, would justify termwise integration and yield $C_0/a_k$. The existing total integrability bound does **not** give an integrable majorant for each differentiated/forest term.

## 3. Transfer to coarse domains

**PROVED (scale arithmetic).** A top-layer parameter patch `PolymerGeometry.Pset` has side $L^{m_1+K}=M_1L^K$. A $\pi'_K$ box in `TreeLengthCov.ChosenOne` has side $L^{m_0+m_1+K+1}$, so an aligned box contains $L^{d(m_0+1)}$ top patch cells. However `TreeLength.scaleW` normalizes `dExt` by $L^{m_0+m_1+K}$, *one power of $L$ smaller* than that box side. `LedgerPacking.card_idx_in_cells_le` gives $(L^{m_0})^d$ indices per ordinary cell, not the $\pi'_K$ count. None is a bound $dExt(T)\le a|J|+b_0$ by itself.

**OPEN — DET-HULL-GEOM/COUNT.** Show each connected hyperedge footprint has a bounded diameter $c_{fp}M_1L^j$, construct an admissible rooted $\pi'_K$ hull inside the required halo, and exhibit a connected structure with
$$dExt(T)\le a|J|+b_0,\qquad a\le c_{fp}/L^{m_0}\quad\text{(top layer, before rounding/overlap losses)}.\tag{8}$$
For $a<1$ one must actually prove $c_{fp}$ plus those losses is less than $L^{m_0}$; the side ratio does not prove it. Mixed layers, torus wrapping, and the `dOmega` admissibility conditions need separate checks. `RootActiveSize.isPolyDom_and_dExt_eq_sizeJ` identifies the size of an **already admissible** nonempty $T$, but supplies no (8).

**PROVED CONDITIONAL ON DET-HULL-GEOM/COUNT.** For a footprint $J$ and root block $B$, let $\mathcal H(J,B)$ be all admissible rooted hulls of *minimum cardinality* among hulls covering the complete active interaction footprint and the root, with a fixed invariant halo rule. If nonempty, allocate each contribution to every $T\in\mathcal H(J,B)$ with weight $1/|\mathcal H(J,B)|$. The weights sum to one and are paving-equivariant when the eligibility and minimum are invariant. Include $J=\varnothing$: `decLog_zeroCuts` is the local $P$ baseline and must be assigned to a nonempty rooted hull. A proof that the concrete `unitP` block fits that hull, plus a weighted bound on all $J$ assigned to one $T$, remains **OPEN**. `RootedAnimals.sum_rooted_le`, `MooreDegree.mooreGraph_degree_le`, and `P6TopRootedFiber.top_rooted_sum_le` count rooted patch sets once their graph membership and cost are proved; none controls this hull fibre automatically.

**PROVED CONDITIONAL ON DET-FOREST-X, DET-HULL-GEOM/COUNT and DET-CHART.** In the one-cost formulation $|w_x|\le C_0(a_k+x)^{-2}e^{-\mu r(w)}$, fibre count $\le C_Ee^{\sigma r}$, and $dExt(T)\le ar+b_0$, put $\lambda=\mu-\sigma>0$. Summing $r\ge(dExt(T)-b_0)/a$ and integrating (7) gives
$$|d_z(T;\Theta)|\le c_{det}e^{-\kappa_{det}dExt(T)},\quad
\kappa_{det}=\lambda/a,\quad
c_{det}={C_0C_E e^{\kappa_{det}b_0}\over a_k(1-e^{-\lambda})},\tag{9}$$
up to the explicit $N|B|/2$ root-trace factor if it is not included in $C_0$. To meet the step rate require $\lambda\ge a\kappa'$. Formula (9) is a proved geometric-series deduction under named inputs; its hypotheses are **OPEN** for the landed determinant.

## 4. Physical chart and Lean order

**REFUTED (locality of the existing fixed-field family).** `rootTrace_cut_expansion` holds $\phi,\alpha$ fixed at the full solution. If those fields depend on the whole datum, each $\Delta_J$ may read it outside the hull even when the matrix cut support is local. `ROOT.md` §3(iii) requires analytic, halo-local coefficient functions, so this matters.

**OPEN — DET-CHART (cheapest route).** Use `Decoupled2Background.i4b_analytic` to set $(\phi_s,\alpha_s)=F_1(s,\Theta)$ with the **same** cuts as (1). Prove: (i) this family lies in the strict `DecDom` on one common open cut/data chart, with uniform standing constants; (ii) it agrees at $s=1$ with `StepComplexOut.logAC` and hence the physical determinant; (iii) `i4b_local`/`RowsBg.i4b_local_rows` and the cut factor lemma make every assigned coefficient depend only on the datum in the stated `thickSet` halo; (iv) paving covariance and real compatibility. The cut dependence of $\phi_s,\alpha_s$ adds differentiated vertices to DET-FOREST-X, so the fixed-field bound alone cannot be substituted unchanged.

Lean packages, each **OPEN** until compiled without placeholders, each at most 300 lines:

1. `DetForestAlgebra` — **can start now**: (1)–(3), zero cuts via `DecLogZero`, and the finite mixed-difference coverage lemma via `CutExpansion`.
2. `DetForestComponents` — **can start now, coordinate with `DecCovCutSupport.lean`**: factor $G_s,M_s^{-1},\Pi_s,Q,P$ over `Yreg` components; prove endpoint cancellation and the correct hypergraph-to-Moore bridge if true.
3. `DetForestResolvent` — **after 1–2**: termwise $x$-uniform weighted bounds, Neumann expansions and explicit $V_q$ link factor from `DecoupledXBounds.dg1x`/`Decoupled2Dg.Kz_cube_weighted`.
4. `DetForestConstraint` — **after 3**: bound every $M_s^{-1}$ transition, including cut-dependent background vertices; establish DET-FOREST-X with an integrable $(a_k+x)^{-2}$ majorant.
5. `DetForestHull` — **geometry can start now**: prove (8), rooted admissible hulls, equal weights and weighted fibre count using `RootedAnimals`, `MooreDegree`, `LedgerPacking`, `RootActiveSize`.
6. `DetForestChart` — **can start now**: `i4b_analytic/i4b_local`, strict joint chart, endpoint and data locality.
7. `DetForestTransfer` — **after 2–6**: prove (9), the numerical margin to $\kappa'$, and construct the actual `DetExpansionC` family.

**Final verdict: OPEN.** The exact failing statement is DET-FOREST-X together with its constraint and hull counts; the proposed $M_1^{-1}$ per cut is not supplied by any landed theorem. The repair is the paid-link, rooted constrained-resolvent estimate (5), an integrable majorant, and the explicit rate margin (9). No claim of a completed determinant bound or Lean proof is made.
