# P6 boundary localization: a hole-completion counterexample and the corrected theorem

**12 October 2026.** This is the response to followup_g2.txt. The finite tree and fixed-output counting results of GRAPH-GM-2.md §§3–4 remain valid for their explicit geometric record. The record is not supplied by the region-history rules. In fact, its assertion that the uncharged hole completion is a P6 localization domain is false for an admissible two-step history. The obstruction occurs with no interpolation derivatives. A block-union output requires an active collar whose tree cost grows with the length of a new hole.

## 1. The support class and the point of failure

P1 (2.26), printed p. 117, defines $\mathcal D_j$ as connected unions of the overlapping cubes $\pi'_j$ of side $LM L^j$; the PDF image was checked. P5 (1.33)–(1.34), printed p. 496, uses this $\mathcal D_j$ for its modular class and tree size. P6 printed p. 34 explicitly takes its old boundary source from $\mathcal D_k(\mathrm{mod}\,\Omega_k^c)$ and assigns an output in $\mathcal D_{k+1}(\mathrm{mod}\,\Omega_{k+1}^c)$. P3 (4.44), printed p. 78, assigns $Y=X_1\cup\bigcup_iY^{(i)}$ and verifies membership in its localization-domain class; its PDF image was checked.

There is a source-class discrepancy that matters here. LF-RECONSTRUCTION.md Definition I.2.15 identifies $\mathcal D_j$ with **all** nonempty nearest-neighbor connected sets (its Def-2 formal class), whereas P1 (2.26) has the block-union condition. FLUCTUATION.md §1.1 uses the P1 condition. The one-cell-wide source path considered while investigating this follow-up is therefore a counterexample only to the broadened LF-RECONSTRUCTION class, not to the printed P6 source class. The counterexample in §2 uses a connected union of old $\pi'_k$ cubes and hence does not depend on that discrepancy.

The exact false assertion is GRAPH-GM-2.md §2, equation (2.1), with $\mathcal C=\varnothing$: the set
$$Y=\operatorname{holeCl}_{\Omega_{k+1}}(X\cup B) \tag{1.1}$$
need not belong to $\mathcal D_{k+1}(\mathrm{mod}\,\Omega_{k+1}^c)$. Moreover no replacement block-union domain containing this $Y$ satisfies the uncharged bound (3.1) uniformly. Here $B$ is made from the new $\pi'_{k+1}$ cubes containing selected old source cubes. The hole closure adjoins each entire component of $\Omega_{k+1}^c$ met by the argument, as required by P5 (1.33). The example below uses a nearest-neighbor connected hole component, so the result is independent of whether “component” in P5 means face or star connectivity.

## 2. An admissible history with a long thin hole

**Proposition 2.1 (counterexample).** Fix $d=3$, $L=8$, an integer radius $r=R_{\rm base}\ge4L+20$, constant $\lambda_j=1$ and $R_j=r$, and take $k_0=0$ so that no hull or removal step is applied. There are finite tori of arbitrarily large side, two region steps obeying LF-RECONSTRUCTION.md Definition I.3.1 (R1)–(R9), and a P6 boundary source $X\in\mathcal D_1(\mathrm{mod}\,\Omega_1^c)$ with
$$X\cap Z_1\ne\varnothing,\qquad X\cap\Omega_2\ne\varnothing,\qquad
d_1(X\mathrm{\ mod}\,\Omega_1^c)<\infty, \tag{2.1}$$
such that (1.1), even with the source nesting cubes $B$ and no derivative cubes, is not in $\mathcal D_2$. The old size and the source cover can be held fixed while the new hole length $T$ tends to infinity. Every $Y'\in\mathcal D_2(\mathrm{mod}\,\Omega_2^c)$ that contains $X$ obeys
$$d_2^{\rm cov}(Y'\mathrm{\ mod}\,\Omega_2^c)\ \ge\ T-O(L+r), \tag{2.2}$$
whenever its modular covering size is defined. In particular the P3-form estimate $d_2(Y'\mathrm{\ mod}\,\Omega_2^c)\le L^{-1}d_1(X\mathrm{\ mod}\,\Omega_1^c)+d(2L+1)^d|\mathcal C|$ fails for $\mathcal C=\varnothing$ as $T\to\infty$.

*Construction and proof.* Write the scale-1 and scale-2 cube tori as $\mathbb T_1=(\mathbb Z/8N\mathbb Z)^3$ and $\mathbb T_2=(\mathbb Z/N\mathbb Z)^3$; cross-scale intersections use the inverse image of a scale-2 set under the parent-cube map. Choose $N$ so large that all boxes below lie in a common nonwrapping coordinate chart. At the first step take $Z_0=\varnothing$, $\mathsf P_1=\{0\}$, and $\mathsf Q_1=\mathsf R_1=\mathsf S_1=\varnothing$. Rule (R3) gives $\Omega'_1=\mathbb T_1$. Rules (R4)–(R6) then give
$$\Omega_1=\mathrm{Op}_1([-3,3]^3;\mathbb T_1),\qquad
\Omega_1^c=H:=[-3,3]^3,\qquad H\subset Z_1. \tag{2.3}$$
For the equality, every cube of $H$ is excluded because its containing $8$-block meets $H$. If a cube is outside $H$, one coordinate lies beyond one face of $H$; choose the containing $8$-block to extend away from that face in this coordinate. This block misses $H$. The last inclusion is LF-RECONSTRUCTION Lemma I.3.5(e), or the landed RegionStep.Omega_compl_subset_Z0 followed by RegionSeq.OmegaAt_compl_subset_Z. Lemma I.3.5(d) also confines $Z_1$ to a box about $0$ of radius at most $[2r]+L+8$: here $F^Z_1=H^{\sim4}$ and $k_0=0$.

Choose a scale-2 coordinate $p\gg r+L$ so that a neighborhood of the ray $\{(p+t,0,0):t\ge0\}$ is in $\Omega'_2$; this is possible uniformly in its length because $\Omega'_2{}^c$ stays in a fixed neighborhood of the coarsened $Z_1$, by Lemma I.3.5(a). At the second step set
$$\mathsf P_2=\{(p+t,0,0):0\le t\le T\},\qquad
\mathsf Q_2=\mathsf R_2=\mathsf S_2=\varnothing, \tag{2.4}$$
with $T\ge64$ and $N>p+T+O(r+L)$. Every cube of $\mathsf P_2$ lies in $\Omega'_2$, so all constraints (R4)–(R6) hold. Its three-neighborhood is the rectangular tube
$$F_T=[p-3,p+T+3]\times[-3,3]^2\subset\mathbb T_2. \tag{2.5}$$
In a neighborhood of $F_T$, rule (R4) gives $\Omega_2^c=F_T$. Indeed a point in $F_T$ cannot lie in a block disjoint from $F_T$; for a point outside this rectangular box choose an $8$-block extending away from one of its violated coordinate faces. The block misses $F_T$ and, since this neighborhood lies in $\Omega'_2$, is admitted by the constrained opening. The other part of $\Omega_2^c$ remains near the old seed and is separated from $F_T$ by a positive gap. Thus $F_T$ is one **face-connected component** of $\Omega_2^c$.

In scale-1 cube coordinates take the rectangular box $X=[-4,8p+7]\times[-4,4]^2$. It contains $H$, reaches the whole scale-2 cell over $(p,0,0)$, and is independent of $T$. A rectangular box of at least eight cells in every direction is the union of all contained translated $8$-blocks and is connected, so $X\in\mathcal D_1$. It contains the entire old hole $H=\Omega_1^c$, hence is modular. The old seed inclusion in (2.3) gives $X\cap Z_1\ne\varnothing$. Along the corridor before it reaches $F_T$, the set lies in $\Omega_2$, so $X\cap\Omega_2\ne\varnothing$. A physical tree in this fixed box meeting every old $\pi'_1$ block that intersects $X\cap\Omega_1$ exists. Thus its original P5 size and its chosen-cover size are finite and bounded independently of $T$.

Take any old chosen cover of $X\cap\Omega_1$ and form $B$ as in GRAPH-GM-2.md §2. Each old $8$-block is the size of one scale-2 partition cell, and each containing new $\pi'_2$ block extends at most seven scale-2 cells beyond it in any coordinate. Since $X$ ends at the near end of $F_T$, all of $B$ lies within $O(L)$ of the fixed corridor and the near end, independently of $T$. The set $X\cup B$ meets $F_T$; hence (1.1) contains all of $F_T$. In the middle third of this tube, (1.1) has no points outside $F_T$. Its transverse width there is seven scale-2 cells, whereas a new $\pi'_2$ block has width eight. No such block contained in (1.1) can cover a middle-third tube point. By P1 (2.26), (1.1) is not in $\mathcal D_2$. This proves the first assertion without using any interpolation parameter.

For the quantitative claim let $Y'$ be a block-union modular output containing $X$. Since $X$ meets the face component $F_T$, modularity forces $F_T\subset Y'$. For every integer $t$ with $16\le t\le T-16$, the point $x_t=(p+t,0,0)$ belongs to some new $8$-block $Q_t\subset Y'$. Such a block cannot fit in the transverse interval $[-3,3]$; with first coordinate still $p+t$ it contains a site $z_t\in Y'\setminus F_T$. The old-hole component is far away, so $z_t\in Y'\cap\Omega_2$. Any chosen modular cover of $Y'\cap\Omega_2$ must contain a block covering $z_t$. A tree meeting covering blocks for $t=16$ and $t=T-16$ spans at least $T-32-2(L-1)$ in new cube units. This proves (2.2), allowing the harmless endpoint convention in the passage between cubes and physical lengths. The same lower bound applies to the original P5 size because $d_2^{\rm cov}\le d_2$ whenever the former is finite. Since the old size is independent of $T$ and $\mathcal C=\varnothing$, the asserted uncharged transfer fails for any P6 output that contains $X$, as P6 printed p. 34 requires. $\square$

The example uses an arbitrary allowed set $\mathsf P_2$ of newly charged cubes. Lemma I.3.8 attributes $Z_2$ to seeds, but it does not restrict the length or transverse width of $\Omega_2^c$ and cannot pay the active collar. The landed RegionStep constraints and inclusions cited above express exactly this freedom. The printed P6 p. 34 says that P3 (4.48)–(4.50) extend with modular sizes; it does not supply a collar estimate that would exclude (2.4).

## 3. What is proved and the corrected geometric assertion

**Source nesting is not the obstruction for a P1 source.** If $X$ is a union of old $\pi'_k$ cubes and an old chosen family covers $X\cap\Omega_k$, then $\Omega_{k+1}\subset\Omega_k$ in fine coordinates by LF-RECONSTRUCTION Lemma I.3.5(f). Thus that family covers $S=X\cap\Omega_{k+1}$. Each old $\pi'_k$ cube has the physical side of one new partition cell and lies in an overlapping new $\pi'_{k+1}$ cube for $L\ge2$. Choosing one such new cube for each old cover cube gives $S\subset B$, and every selected new cube is met by the old tree. This proves the **bare grid source-nesting statement**, including the witness point. It says nothing about whether the new cubes lie inside a particular auxiliary operator domain, whether the interpolation collar lies inside $X_1$, or whether hole closure is a localization domain; VMOD-2.md §1.3 and VMOD-5.md §3 keep those questions open.

**Corrected hole-completion assertion.** For each effective derivative family $\mathcal C$, the output construction must provide one of the following explicit alternatives:

1. A domain class allowing arbitrary nearest-neighbor connected cubical supports, together with a proved modular summability and analytic localization theory for that enlarged class; or
2. a block-union completion $Y^\sharp\in\mathcal D_{k+1}(\mathrm{mod}\,\Omega_{k+1}^c)$, a chosen output cover, and a physical tree, with a measured nonnegative collar cost $R_{\rm hole}$ such that
   $$d_{k+1}^{\rm cov}(Y^\sharp\mathrm{\ mod}\,\Omega_{k+1}^c)
   \le L^{-1}d_k^{\rm cov}(X\mathrm{\ mod}\,\Omega_k^c)
      +d(2L+1)^d|\mathcal C|+R_{\rm hole}. \tag{3.1}$$

Alternative 1 is the support class of LF-RECONSTRUCTION Definition I.2.15, but it is an amendment to P1 (2.26) and needs its own H7 and polymer-sum proofs. In alternative 2, $R_{\rm hole}$ must be an **actual additional tree/cover cost**. Proposition 2.1 forces $R_{\rm hole}\ge T-O(L+r)$ for its history and $\mathcal C=\varnothing$. A formal declaration of a nonnegative number called a collar cost without a corresponding decay factor does not restore P6 (4.48)–(4.50).

The other physical assertions of GRAPH-GM-2.md §2 remain separate: each nonzero derivative needs a face-touching active witness; every new active output cell needs an owner derivative (at most $G=(2L+1)^d$ cells per derivative); the completed cover must lie in the output domain; and each generated component must attach through a face chain to a source cube met by the old tree. Region Lemma I.3.5, Region Lemma I.3.8, and landed parameter-incidence locality do not imply these statements for the P6 interpolation. Call this remaining record **OPEN-P6-PHYSICAL-WITNESSES**. Call the charged geometric completion **OPEN-P6-HOLE-COLLAR**; its decay payment is part of OPEN-P6-ANALYTIC-BOUND below.

## 4. Final conditional boundary-localization theorem

The following is the strongest conclusion obtained from the checked results without treating P6 p. 34 as a proof of the missing transfer.

**Theorem 4.1 (conditional P6 boundary localization).** Fix a region history satisfying (R1)–(R9), $k\ge0$, and the P6 boundary sources $X\in\mathcal D_k(\mathrm{mod}\,\Omega_k^c)$ with $X\cap Z_k\ne\varnothing$ and $X\cap\Omega_{k+1}\ne\varnothing$. Assume:

- **OPEN-P6-PHYSICAL-WITNESSES:** the P3 interpolation terms have the witness-carrying output construction of §5, with (4.1) of GRAPH-GM-2.md for every fixed *whole* output $Y$;
- **OPEN-P6-HOLE-COLLAR:** each output is an admissible modular domain and has (3.1) with a measured $R_{\rm hole}$;
- **OPEN-P6-ANALYTIC-BOUND:** the complex H7 Cauchy estimate for the boundary term gives the pre-resummation bound $\beta_k^{-2}\exp[-(\kappa-1)\Delta-(\kappa_1-1)|\mathcal C|-2\kappa R_{\rm hole}]$ on the stated open analytic neighborhood, where $\Delta=d_k^{\rm cov}(X\mathrm{\ mod}\,\Omega_k^c)$;
- **OPEN-P6-SOURCE-SUM:** for each fixed whole output $Y$, the allowed old sources have
  $$\sum_{X\ {\rm assigned\ to}\ Y}e^{-\kappa_0\Delta_X}
  \le C_{\rm src}e^{D_Y},\qquad
  D_Y=d_{k+1}^{\rm cov}(Y\mathrm{\ mod}\,\Omega_{k+1}^c), \tag{4.1}$$
  with $C_{\rm src}$ uniform in the history and volume.

Suppose also that (4.2) and (4.5), and the parameter inequalities preceding (4.6), of GRAPH-GM-2.md hold, and $\beta_k^{1/2}\ge C_{\rm src}$. Then the localized boundary expression admits an expansion over the whole outputs $Y$,
$$B^{\prime\prime(k)}=\sum_Y B^{\prime\prime(k)}(Y),\qquad
|B^{\prime\prime(k)}(Y)|\le
\beta_k^{-3/2}\exp[-(2\kappa-1)D_Y], \tag{4.2}$$
with the analyticity domain supplied by OPEN-P6-ANALYTIC-BOUND. This is the form of P6 (4.33)–(4.34) for the covering modular size. For P6's **original** $d_k$, replace every covering-size hypothesis above by its original-size counterpart and additionally prove **OPEN-P6-ORIGINAL-SIZE-TRANSFER**; the inequality $d^{\rm cov}\le d$ does not give this replacement.

*Proof under the named hypotheses.* Apply GRAPH-GM-2.md Theorem 3.1 in its collar form. The rate calculation (4.6) there, with the extra $2\kappa R_{\rm hole}$ subtracted from the analytic input, gives for a fixed $X,Y$ a factor $\beta_k^{-2}e^{-\kappa_0\Delta_X-2\kappa D_Y}e^{-\kappa_2|\mathcal C|}$. GRAPH-GM-2.md Theorem 4.1 sums the effective derivative families at fixed **whole $Y$** by at most one; its proof uses the owner and witness inequalities and is unchanged by disconnected source pieces. Sum the remaining $X$ at fixed $Y$ using (4.1). The result is $\beta_k^{-2}C_{\rm src}e^{-(2\kappa-1)D_Y}$, which is at most the bound in (4.2). All terms are analytic on the common open neighborhood from the analytic input; finite sums preserve analyticity, and the stated uniform bounds justify any subsequent normal convergence. $\square$

**Corollary 4.2 (the printed P5/P6 modular size, conditional).** Suppose the four named inputs of Theorem 4.1 hold with every $\Delta_X$ and $D_Y$ replaced respectively by P5's original $d_k(X\mathrm{\ mod}\,\Omega_k^c)$ and $d_{k+1}(Y\mathrm{\ mod}\,\Omega_{k+1}^c)$. In particular **OPEN-P6-ORIGINAL-SIZE-TRANSFER** must give the charged inequality (3.1) with these original sizes, the physical witness inequalities (4.1) of GRAPH-GM-2.md at fixed whole $Y$, and the same explicit collar payment in the analytic estimate. Then P6 (4.33)–(4.34) holds with its printed modular sizes:
$$|B^{\prime\prime(k)}(Y)|\le
\beta_k^{-3/2}\exp[-(2\kappa-1)d_{k+1}(Y\mathrm{\ mod}\,\Omega_{k+1}^c)]. \tag{4.3}$$
The proof is the preceding rate, fixed-output count and source sum with those replacements. This corollary is **conditional on OPEN-P6-ORIGINAL-SIZE-TRANSFER and the original-size versions of the four named inputs**. Its zero-collar specialization is false for Proposition 2.1.

**Status.** The grid source-nesting lemma and Proposition 2.1 are **proved** from the stated finite geometry and checked source definitions. The finite tree estimate, fixed-output entropy sum, and rate arithmetic are **proved conditional on their explicit physical witness record** in GRAPH-GM-2.md. Theorem 4.1 is **conditional on four named OPEN inputs**. Proposition 2.1 shows that the uncharged version of OPEN-P6-HOLE-COLLAR is **false**, not merely unproved. P6's printed modular transfer cannot presently be cited to discharge that false assertion.

## 5. Lean declarations in dependency order

The following names after the semicolons are **proposed**, not landed. Existing definitions and theorems are named only where they were checked in the read-only Lean tree.

1. **Region and domain conventions.** Use landed LargeField.Region.Step RegionStep, Region.OmegaPrime, Region.Omega, Region.OmegaDD, Region.Z0, and LargeField.Region.Inclusions RegionStep.Omega_compl_subset_Z0, RegionStep.Z0_subset_nbhd_FZ, RegionStep.Z0_subset_Zpre, together with LargeField.Region.Generating RegionSeq.OmegaAt and RegionSeq.OmegaAt_compl_subset_Z. State explicitly whether the polymer carrier is P1's block-union class or LF-RECONSTRUCTION's broader nn class; proposed declarations: p1BlockDomain, modularComponentClosure, blockUnion_rect, opening_rect_compl, thinTubeHistory.
2. **Counterexample checks.** Build the two-step RegionSeq with constant radii, prove its $\mathsf P$ constraints and the separation of $F_T$ from the old hole; proposed: thinTube_history_admissible, thinTube_source_modular, thinTube_hole_component, thinTube_no_block_inside, thinTube_completion_not_domain, thinTube_collar_lower_bound. The last theorem should quantify over all block-union modular completions and show a bound linear in $T$.
3. **Bare grid nesting.** Define the physical map from an old $\pi'_k$ block to a containing new $\pi'_{k+1}$ block, retaining a point where the source tree meets the old block; proposed: oldBlock_mem_newBlock, modular_source_nesting_grid. The auxiliary operator-domain and $X_0$-to-$X_1$ collar statements are distinct binders, not consequences of this lemma.
4. **Witness-carrying replacement for counting.** Keep landed Localization/Decoupled2FpGeometry.lean Dec2.incGraph for its analytic locality use and landed Localization/Decoupled2FpCount.lean Dec2.seedClosure for its present site/parameter reachability use. For P6 counting introduce physical active derivative cubes, FaceAdj, locV, locAdj, witnessClosure and effective as in GRAPH-GM-2.md (5.1). A BoundaryLocWitness record stores, for each generated component, a retained derivative cube face-touching a source component, a source-tree point in the touching source cube, and, for every new active output $M$-cell, an owner derivative with at most $G$ owned cells per derivative. Proposed: ineffective_derivative_vanishes, component_face_anchor, completion_cells_le, deriv_mem_whole_output, candidate_cubes_le, new_cells_le_derivs. No incidence edge across a hole is counted as a free physical attachment.
5. **Modular completion and costs.** Proposed: modular_block_completion, collar_tree_cost, boundary_gm2_modular_charged. These accept or construct $R_{\rm hole}$ and expose it in the conclusion. A separate theorem must supply its analytic payment; the counterexample prevents a zero-cost universal instance. Prove the output chosen-family property for the exact completed support rather than for the site projection of seedClosure.
6. **Entropy and analytic assembly.** Proposed: boundary_gm3_fixed_whole_Y (the finite proof of GRAPH-GM-2.md §4), boundary_gm4_with_collar, boundary_cauchy_bound, boundary_source_sum, boundary_localization_conditional. The fiber key is the whole completed $Y$, never only the set of hole components. A final original-P5-size theorem requires original_size_transfer as an additional declaration; it cannot be obtained by rewriting covering_size_le_original_size backwards.

The landed ordinary PolymerCount and tree-length theorems may provide arithmetic models. They do not instantiate the modular carrier, the block-union completion, or the physical derivative witness record. No Lean declaration proving those inputs was found in the cited region/history or decoupled graph files.
