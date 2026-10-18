# Aligned openings: the geometric gain does not close the induction

**Verdict (17 October 2026).** A fixed grid of $L$-blocks makes the raw hole a union of those blocks and makes *completion alone* spill-free. The coarse radius, seed-attribution, component-separation, ripeness, and one-component halo inequalities used by the landed region calculus survive with the **same** numerical bounds; the sharper printed P5 (2.4) outer radius does not. Nevertheless ruling R3, as stated, is false as a closure of blocker 3. The fixed grid destroys the Euclidean covariance required of each history and boundary coefficient by P5 (H.5), (H.7). Moreover, a completed hole still has positive tree length between two active attachments; the spill-free lemma does not establish the P6 assignment bound or the P7 retained-hole bridge. There is also a narrower problem with R3's premise: the landed negative theorem tests a *fixed* $L$ grid, whereas P5's $\pi'_k$ and the landed `IsPiPrimeUnion` allow a block at **every** $\pi_k$-cell offset. The long rectangular inherited hole of VMOD-36 is a union of such blocks when its side lengths are at least $L$; its asserted long-face spill does not follow from the cited Lean theorem.

This is a focused mathematical and source-correspondence audit, not a Lean implementation or a proof of the full P5–P7 induction. Its refutation tests are the fixed-grid translation example and the two-attachment size example below. The latter is a geometric obstruction to an *unrestricted* transfer estimate, not a demonstrated nonzero physical P6 coefficient.

## Inputs and conventions

The read-only repository was at commit `42c3b652f3dca9f14271b3627d2ab13adff60b14`. The principal frozen inputs have SHA-256 prefixes: `BLOCKERS.md` `cdc45858e47b`, `PLAN-B.md` `d00d2c46532e`, `VMOD-44.md` `fc0f14d8579e`, `Region/Step.lean` `a00a84202fe8`, `Geometry/Openings.lean` `a9afa244de04`, `R/HoleBoxUnion.lean` `66b7c785dac5`, `R/HoleCompletionSize.lean` `50d61801171d`, `Fluctuation/SizeModDefs.lean` `df897aff0ac9`, `Region/Inclusions.lean` `3d527bdf1402`, `Region/Seeds.lean` `4c07771b73ed`, `Region/SymmStep.lean` `6eaf9ba4a2a1`, and `R/RHaloSep.lean` `62959b7e3b9c`. The read-only PDFs P5, P6, P7 have prefixes `b3f0ef3491fc`, `ee0ca061c9a7`, `c48e08dd4398`. VMOD-34–42 and LFROOT3/LFH7PRIME/LFH7PRIME2 were read as the prior findings, with VMOD-36 and VMOD-41/42 supplying the particular tests. No source under `/home/scott/Balaban` was changed.

Source keys and journal pagination are those in `review/SOURCES.md`: P5 is *Commun. Math. Phys.* **196** (1998), 485–521; P6 and P7 are *Commun. Math. Phys.* **198** (1998), 1–45 and 493–534. The extracted P5/P7 text layers are usable for prose but garble several mathematical glyphs (notably $\Omega$, $\square$, and fractions); the equation numbers and printed page headers were checked in the supplied PDF text. No argument below relies on a guessed garbled glyph.

Write $K=k+1$, $a=\lfloor R_{k-1}\rfloor$, $\rho=\lfloor R_k\rfloor$, $b=\lfloor2R_k\rfloor$, and $r=\lceil R_{\rm base}\lambda_k^2\rceil$. Distances and neighborhoods in this section are in $\pi_K$-cube units on the coarse torus. Assume $L\mid n_K$ and $L\ge2$, as required for a fixed $L$-block tiling. For a phase $\xi\in(\mathbb Z/L\mathbb Z)^d$, let $\mathscr B_\xi$ be its disjoint $L$-blocks and set

$$\mathsf T_\xi(A)=\bigcup\{B\in\mathscr B_\xi:B\cap A\ne\varnothing\},\qquad
\operatorname{Op}^{\xi}_m(F)=\bigcup\{B\in\mathscr B_\xi:d(B,F)\ge m\}.$$

R3 is $\xi=0$ at every step. `lblock`, `opening`, and `openingIn` in `Geometry/Openings.lean` instead allow every corner; replacing them by $\operatorname{Op}^{0}$ changes the construction. `RegionStep.OmegaPrime`, `.Omega`, `.OmegaDD`, and `.Z0` name the four successive openings in `Region/Step.lean`.

## Exact aligned-opening lemma and all radii

For every $m\ge1$,

$$\boxed{\bigl(\operatorname{Op}^{\xi}_m(F)\bigr)^c
       =\mathsf T_\xi\bigl(\operatorname{nbhd}_{m-1}F\bigr).}\tag{1}$$

Indeed a point $x$ belongs to exactly one phase-$\xi$ block $B_x$. It is excluded from the opening precisely when $d(B_x,F)<m$, equivalent for integer distance to the existence of $y\in B_x$, $f\in F$ with $d(y,f)\le m-1$. This is precisely $B_x\cap\operatorname{nbhd}_{m-1}F\ne\varnothing$. If $\Theta$ is already a union of phase-$\xi$ blocks, the same proof gives

$$\Theta\setminus\operatorname{Op}^{\xi}_m(F;\Theta)
 =\Theta\cap\mathsf T_\xi(\operatorname{nbhd}_{m-1}F).\tag{2}$$

For any $A$, $A\subseteq\mathsf T_\xi(A)\subseteq\operatorname{nbhd}_{L-1}A$: the second inclusion follows since two sites of one $L$-block differ by at most $L-1$ in sup distance. Thus (1) implies

$$\operatorname{nbhd}_{m-1}F\subseteq(\operatorname{Op}^{\xi}_mF)^c
\subseteq\operatorname{nbhd}_{m+L-2}F.\tag{3}$$

These are exactly the bounds of `opening_disjoint_nbhd` and `opening_compl_subset`; the *set* may move by as many as $L-1$ cells normal to a face, but its *cardinality* can change by the whole area of a long face. “At most $L$ cubes” is a radius statement, not a uniform volume or modular-size bound. P5 (2.4), printed p. 502, has a **sharper** every-offset outer inclusion $((U'_k)^{\sim 4+\rho+(L-1)/2})^c\subset\Omega'_K$ (in the paper's notation). Its hole lies within radius $\rho+4+(L-1)/2$ of $U'_k$, while (3) permits radius $\rho+4+(L-1)$. This sharper inclusion can fail for fixed alignment: at a flat face with $e+\rho+4\equiv0\pmod L$, tiling the boundary point extends the hole another $L-1$ sites beyond radius $\rho+4$, exceeding $(L-1)/2$. The extra loss against the printed bound is $(L-1)/2$ in the odd-$L$ convention of (2.4); every use of that sharper bound in P5 needs rechecking.

Apply (1)–(3) to the actual step, with $U'=\operatorname{blockMap}_L(\operatorname{nbhd}_{a+1}Z_k)$. Since neighborhoods compose in the torus sup metric, the aligned regions satisfy these exact identities and inclusions:

| Region | Exact formula for its complement | Lower and upper bounds |
| --- | --- | --- |
| $\Omega'_K$ | $\mathsf T_0(\operatorname{nbhd}_{\rho+4}U')$ | $\operatorname{nbhd}_{\rho+4}U'\subseteq(\Omega'_K)^c\subseteq\operatorname{nbhd}_{\rho+L+3}U'$ |
| $\Omega_K$ | $(\Omega'_K)^c\cup\mathsf T_0(\operatorname{nbhd}_3P)$ | $\operatorname{nbhd}_{\rho+4}U'\cup\operatorname{nbhd}_3P\subseteq\Omega_K^c\subseteq\operatorname{nbhd}_{\rho+L+3}U'\cup\operatorname{nbhd}_{L+2}P$ |
| $\Omega''_K$ | $\Omega_K^c\cup\mathsf T_0(F'')$, $F''=\operatorname{nbhd}_{\rho+2}Q\cup\operatorname{nbhd}_{2\rho+4}R$ | $F''\subseteq(\Omega''_K)^c$ and $(\Omega''_K)^c\setminus\Omega_K^c\subseteq\operatorname{nbhd}_{\rho+L+1}Q\cup\operatorname{nbhd}_{2\rho+L+3}R$ |
| $Z^{(0)}_K$ | $\mathsf T_0(\operatorname{nbhd}_{b+2}F^Z)$, $F^Z=\operatorname{nbhd}_4(\Omega''_K)^c\cup\operatorname{nbhd}_1S$ | $\operatorname{nbhd}_{b+2}F^Z\subseteq Z^{(0)}_K\subseteq\operatorname{nbhd}_{b+L+1}F^Z$ |

The constrained formula (2) applies at the second and third lines because every preceding aligned opening is tiled. For example, $(\Omega'_K)^c=\mathsf T_0(\operatorname{nbhd}_{\rho+1}\operatorname{nbhd}_3U')=\mathsf T_0(\operatorname{nbhd}_{\rho+4}U')$; $\operatorname{nbhd}_{L-1}\operatorname{nbhd}_3P=\operatorname{nbhd}_{L+2}P$. These are the constants in `Region/Inclusions.lean`: `nbhd_subset_compl_OmegaPrime`, `OmegaPrime_compl_subset`, `OmegaPrime_diff_Omega_subset`, `Omega_diff_OmegaDD_subset`, `nbhd_FZ_subset_Z0`, `Z0_subset_nbhd_FZ`. No extra $L$ is needed in any of those inequalities. The exact every-offset identities P5 (2.4) and (2.9), printed pp. 502–503, must instead be replaced by (1)–(2); they do not remain identities for a fixed tiling.

## What the region induction retains

`StepRadii` in `Region/Seeds.lean` supplies

$$r\ge4L+20,\quad \rho\le r,\quad a\le r,\quad b\le2r,\quad b\le2\rho+1,\quad
\omega_{K}\ge2\rho+L+11,\quad\omega_K\ge a+2.\tag{4}$$

Here $\omega_K=2\lfloor R_{\rm base}\lambda_k^2\rfloor+L+11$ is `omegaW`. The proof of `RegionStep.attribution` uses only the inclusions in the table and (4), so it repeats for aligned openings with its original $4r$ and $5r$ constants. To expose the arithmetic, for $x\in Z^{(0)}_K$ choose $f\in F^Z$ with $d(x,f)\le b+L+1$. If $f$ comes from $\operatorname{nbhd}_4(\Omega''_K)^c$, choose $g\in(\Omega''_K)^c$ with

$$d(x,g)\le b+L+5.\tag{5}$$

If $g$ is assigned to $P,Q,R$ by the three preceding region differences, respectively, the distance to that new seed is at most

$$b+2L+7\le2r+2L+7\le5r,\quad
b+\rho+2L+6\le3r+2L+6\le5r,\quad
b+2\rho+2L+8\le4r+2L+8\le5r.\tag{6}$$

The last inequality needs $r\ge2L+8$, implied by (4). The direct $S$ branch costs at most $b+L+2\le2r+L+2\le5r$. For the inherited branch choose $u\in U'$ at distance $\rho+L+3$ from $g$. A coarsened $z\in Z_k$ can be chosen with $d(u,\operatorname{blockMap}_Lz)\le\lfloor a/L\rfloor+1\le r/2+1$ (the coarsening inequality `supDist_blockMap_le`, using $L\ge2$). Therefore

$$d(x,\operatorname{blockMap}_Lz)\le b+\rho+2L+8+r/2+1
\le\tfrac72r+2L+9\le4r,\tag{7}$$

where the last inequality is $r/2\ge2L+9$, a consequence of $r\ge4L+20$. The links used in `attribution` remain inside $Z^{(0)}$: the split points between $x$ and $f$ lie in $\operatorname{nbhd}_{b+2}F^Z$, and each link length is less than $\omega_K$ because $b+2\le2\rho+3<\omega_K$, $2\rho+L+3<\omega_K$, and $a+1<\omega_K$. Thus no extra separation constant is consumed. In particular, with $A_{\rm old}=\operatorname{blockMap}_L Z_k$ and $N=P\cup Q\cup R\cup S$,

$$Z^{(0)}_K\subseteq\operatorname{nbhd}_{4r}A_{\rm old}\cup\operatorname{nbhd}_{5r}N,\qquad
|Z^{(0)}_K|\le(8r+1)^d|A_{\rm old}|+(10r+1)^d|N|.\tag{8}$$

The volume estimate counts each sup-norm ball by at most $(2t+1)^d$ and then uses the union bound; it never charges a long inherited component solely to current new seeds. `History/StepSeeds.lean:attr_seed`, `History/FlowBook.lean:seed_pos`, and the hull bookkeeping use precisely this old-or-new seed alternative. `Region/Hull.lean` leaves the hull criterion and its width $\omega_K$ unchanged. The abstract ripeness bookkeeping (`Setting.Ripe`, `RegionHistory.Admissible`, `RegionHistory.ripe_window`) can therefore be rerun with the same hypotheses; `R/RRipeCard.lean:removed_eq_box` and `removed_card_le` still give side $\le S.\mathrm{crit}(K)=2S.\mathrm{rho}(K)+10$ and cardinality $\le(2S.\mathrm{rho}(K)+10)^d$ for a *removed ripe* component. Here `S.rho` is the setting’s critical-width parameter, not the step radius $\rho=\lfloor R_k\rfloor$. This is a statement about the modified history after its geometric lemmas are re-proved, not a claim that the existing Lean theorems already apply definitionally to a modified `RegionStep`.

The remaining region interfaces are local rather than numerical. `Region/Inclusions.lean:fine_far`, `ring_nine`, and `thick2_Zpre_compl_disjoint` use the same buffer inclusions above; the safe fluctuation reads $R_{K}(\square')\subset(U'^{\sim3})^c$ stated after P5 (2.4), printed p. 502, remain safe because an aligned opening only removes candidate blocks. `Region/Locality.lean:RegionStep.restrict` and `OmegaPrime_compl_inter_comp`, `Omega_compl_inter_comp`, `OmegaDD_compl_inter_comp`, `Z0_inter_comp` localize the step to one $Z^{\rm pre}$ component. Their block-local arguments use diameter $L-1$ and the same $\omega_K$ bounds, so for a **fixed common phase** they have the same hypotheses and constants; they are not yet Lean theorems for the changed definitions. A phase-indexed repair must restrict and transport that phase with the component. The one interface that cannot be copied for a fixed phase is `Region/SymmStep.lean:RegionStep.image_Omega`, as the explicit counterexample below proves.

Distinct $Z^{\rm pre}_K$ components have distance $\ge\omega_K$ by `History/Core.lean:core_sep` (the component relation uses links of length $<\omega_K$). This does not assert separation of distinct components of $\Omega_K^c$. In `R/RHaloSep.lean`, the halo at scale $K$ has radius $2\lfloor R_{K-1}\rfloor+4=2\rho+4$. Put $q=\lfloor R_{\rm base}\lambda_{K-1}^2\rfloor$, so $\rho\le q$ and $\omega_K=2q+L+11$. Then

$$\omega_K-(2\rho+4)\ge L+7>0,\qquad
\omega_K-2(\rho+1)\ge L+9>0.\tag{9}$$

Consequently `halo_disjoint_comp` still says a P7 halo of radius $2\rho+4$ misses every *other component*, and `thick_disjoint` still separates the two $\rho+1$ thickenings. **Two full P7 halos need not be disjoint:** their radii sum to $4\rho+8$, and for the allowed maximal $\rho=q$ and $q\ge4L+20$, $4q+8\ge2q+L+11=\omega_K$. This existing limitation is recorded by `omega_le_halo_sum`; aligned openings do not improve it.

The literal counting in P5 §2 survives a change of region: (2.6), printed p. 502, and (2.14), printed p. 504, are products of $\chi+\chi^c=1$ over their respective $\pi_K$ cells, hence yield exactly $2^{|\Omega'_K|}$ and $2^{|\operatorname{nbhd}_3\Omega_K|}$ subsets before other constraints. At one fixed incoming state, the aligned $\Omega'$ is contained in the every-offset $\Omega'$, and the later aligned regions are similarly contained for the same $P,Q,R$; these crude choice counts cannot increase. The geometric component bound (8) and ripe bound above remain uniform in the torus size. This **does not** prove the analytic P5 §3–4 or P7 sums: P5 (2.15)–(2.16) uses the specific regions and their symmetry, P6 p. 34 uses an unproved modular assignment, and P7 (3.26)–(3.28), printed pp. 527–528, asserts the activity bound after a Mayer/resummation step. Counting phase-decorated histories or proving that latter bound requires separate work.

## Decisive failure: fixed alignment loses the required symmetry

Take $d\ge3$, $L\ge8$, and a coarse torus of side $n_K=4L$. At a step with $Z_k=\varnothing$, let $P=\{0\}$ and $Q=R=S=\varnothing$. This satisfies all four `RegionStep` seed constraints: $\Omega'_K$ is the whole torus, so `P_sub` holds, and the other constraints are vacuous. The aligned $\Omega_K$ has

$$\Omega_K^c=\mathsf T_0(\operatorname{nbhd}_3\{0\})
=C:=([-L,L-1]\bmod4L)^d.\tag{10}$$

Let $e=e_1$ be translation by one $\pi_K$ cube. Its translated seed $P'=\{e\}$ also satisfies the constraints. The first-coordinate projection of $\operatorname{nbhd}_3\{0\}$ is $[-3,3]$ and that of $\operatorname{nbhd}_3\{e\}$ is $[-2,4]$. Since $L\ge8$, both hit exactly the two fixed grid intervals $[-L,-1]$ and $[0,L-1]$; all other projections coincide. Hence $\mathsf T_0(\operatorname{nbhd}_3\{e\})=C$. But $e+C\ne C$: $(L,0,\ldots,0)\in e+C$ and $(L,0,\ldots,0)\notin C$. Thus

$$\Omega_K(P')\ne e+\Omega_K(P).\tag{11}$$

This is a counterexample at the **first constrained opening**, before ripeness, counting, or P6 estimates. P5 (H.5), printed p. 493, requires covariance under Euclidean transformations preserving the partition $\pi_K$; P5 (H.7), printed p. 497, inherits that requirement, and P5 §3, printed p. 514, restates it for the new boundary expression. Translation by one $\pi_K$ cube preserves that partition. In Lean, `Region/SymmLat.lean:LatTorusSym` includes the corresponding fine translation by $M L^K$, `Region/SymmStep.lean:RegionStep.image_Omega` and `RegionIso.omega` prove covariance for the every-offset opening, and `LargeField/Def7.lean:D7Bdry.euclid` consumes it. Formula (11) prevents the same theorem for a fixed aligned grid. The fixed $\pi_{K+1}$ grid is extra structure and is not part of the present `RegionIso` data.

The smallest symmetry repair **for an aligned-opening construction** is to carry a phase $\xi_K\in(\mathbb Z/L\mathbb Z)^d$ in each step's history and send it to $\xi_K+t\pmod L$ under translation by $t$ coarse cubes. Then

$$\mathsf T_{\xi+t}(A+t)=\mathsf T_\xi(A)+t,\qquad
\operatorname{Op}^{\xi+t}_m(F+t)=\operatorname{Op}^{\xi}_m(F)+t,\tag{12}$$

because translation bijects the phase-$\xi$ blocks with the phase-$(\xi+t)$ blocks and preserves distance. One can insert the normalized identity $L^{-d}\sum_\xi1=1$ before each decomposition of unity: each phase has an exact decomposition, so their normalized sum preserves the density algebraically and the phase count is $L^d$ with total weight $1$. The phase must remain in the multi-index through localization; summing it away term by term would not preserve per-term covariance or automatically preserve the H7 constant. `RegionIso`, local-history dependence, `Def7Bdry.euclid`, and every translated completion lemma would need phase-aware versions. Equation (12) is proved; closure of the phase-enlarged analytic induction is **open**. A deterministic equivariant choice of phase from the region cannot work for all inputs: the empty region is fixed by translation by one coarse cube, whereas no phase is.

## What spill-free completion actually proves

If $\Omega$ is a union of blocks from one tiling, its complement is too: for the unique block $B_x$ containing $x\notin\Omega$, $B_x\cap\Omega=\varnothing$ (otherwise $B_x$ itself would be one of the blocks making $\Omega$). This is exactly `R/HoleBoxUnion.lean:compl_isAlignedBoxUnion`. For the aligned $\Omega_K$, let $X$ be a valid label and let $C$ be a component of $\Omega_K^c$ meeting $X$. Since the hole is a union of $L$-blocks and adjacent blocks in a connected component can be joined, $Y=X\cup C$ remains a connected $\pi'_K$-box union; it contains or misses every hole component. Also

$$X\subseteq Y,\qquad Y\cap\Omega_K=X\cap\Omega_K\subseteq X.\tag{13}$$

Reuse any `ModAdmissible` cover and tree for $(\Omega_K,X)$: all its boxes and vertices remain in $Y$, and (13) says that it covers every active site of $Y$. Taking infima gives

$$d^{\rm cov}_K(Y\bmod\Omega_K^c)\le d^{\rm cov}_K(X\bmod\Omega_K^c).\tag{14}$$

This is `R/HoleCompletionSize.lean:dcovModE_completion_le_of_noSpill` (with the validity statement supplied separately). The analogous argument works directly for P5's continuous tree size (1.34), printed p. 496: the same source tree remains inside $Y$ and the required active $\pi'_K$ cubes are unchanged, so its infimum cannot increase. It does **not** identify P5's size with `dcovMod`; the global continuous-to-fine comparison remains `OPEN-PAPER-FINE-REALIZATION` in VMOD-42.

The phrase “length through a hole is never charged” is false literally. Let $H_N$ be a long aligned-box rectangular hole of length $N$ coarse cells, shorter than half the torus circumference, with one active $L$-box $A_-$ touching its left end and another $A_+$ touching its right end. Put $X_-=H_N\cup A_-$ and $X_+=H_N\cup A_+$. Each is a connected valid modular label. One chosen cover box and a one-vertex connected structure give $d^{\rm cov}(X_-)=d^{\rm cov}(X_+)=0$. For $Y=H_N\cup A_-\cup A_+$, every admissible cover must meet each active collar. Any connected graph joining those encounters has at least $N-2L$ nearest-neighbor bonds: its endpoints may move at most $L$ into the hole at each end, and torus wraparound is longer by the choice of circumference. With $w=\texttt{scaleW}\,L\,m_0\,m_1\,K>0$,

$$d^{\rm cov}_K(Y\bmod H_N)\ge w\max\{N-2L,0\}.\tag{15}$$

P5 (1.34) has the same positive-distance phenomenon for a continuous tree. Inequality (14) applies to $X_-\mapsto X_-\cup H_N=X_-$; it says nothing about adding the *new active* collar $A_+$. Thus an unrestricted inequality $d(Y)\le c,d(X_-)+C|J|+C_0$ fails for a single far-side patch as $N\to\infty$. Whether P6's actual marked assignment can produce that patch with nonzero coefficient is still `OPEN-P6-INHERITED-HOLE-ASSIGNMENT` (VMOD-34–39, LFROOT3); the geometric counterexample identifies exactly the extra incidence or coefficient estimate it must rule out or pay. Alignment does not resolve VMOD-41's P7 two-label retained-hole bridge either: its two labels may overlap only in a retained hole, while `Fluctuation/SizeModUnion.lean:G3_dcov` requires active overlap. The P7 gas estimate for physical coefficients is separate from (14).

There is an additional refutation of the *specific* asserted long-face spill in R3's motivation. `R/HoleBoxUnion.lean:omega_hole_face_misaligned` excludes a box with base `Aligned L` on the **fixed** grid. In contrast, `Fluctuation/SizeModDefs.lean:IsPiPrimeUnion` and `ModAdmissible` require a base aligned only to `cellSide L m₀ m₁ K`, so after passing to $\pi_K$-cube coordinates they admit **every** coarse-cell corner. P5 calls $\pi'_K$ a *cover* of overlapping $L$-blocks in (2.3)–(2.4), printed p. 502. For the nonwrapping rectangular inherited example of VMOD-36 with no new seeds, the every-offset opening has $\Omega_K^c=\operatorname{nbhd}_{\rho+4}U'$: if a site is farther than $\rho+4$ from the rectangle, extend an $L$-block away from the separating face to witness membership of the opening; the reverse inclusion is `opening_disjoint_nbhd`. This hole is a rectangle. If each of its side lengths is $\ge L$ (as in the stated large-radius, long-face family), each site $x$ lies in an $L$-block inside it: in each coordinate interval $[a_i,b_i]$, choose

$$c_i=\min\{\max\{x_i-L+1,a_i\},\ b_i-L+1\};\quad
a_i\le c_i\le x_i\le c_i+L-1\le b_i.\tag{16}$$

The block with arbitrary coarse-cell corner $c$ is a legitimate $\pi'_K$ block. Thus that rectangle has a spill-free completion under the *source* cover despite its face cutting the fixed $L$ grid. The negative fixed-grid Lean theorem and this positive arbitrary-offset fact are consistent. A general arbitrary-shape hole theorem, including thin new-$P$ pockets and their seed charge, has **not** been proved here; (16) only disposes of the cited long rectangular counterexample. This is why the claim in `PLAN-B.md` that its active spill is proved by `omega_hole_face_misaligned` is too strong.

## Lean shape, repair, and status

A reviewable aligned version would introduce a phase parameter to `lblock`/`opening`/`openingIn` and to `RegionStep`, with assumptions `0<L`, $L\mid n_K$, and `StepRadii L ω r Rprev Rk`. Its basic conclusions are (1)–(3), the four exact identities in the table, `RegionStep.attribution` with $4r/5r$, `core_sep` with $\omega_K$, `removed_card_le` for ripe removals, and `halo_disjoint_comp` under $2a+4<\omega_K$. A phase-aware `RegionIso` must transform the phase as in (12). On fine sites, the completion theorem has the landed hypotheses and conclusion

```lean
X ⊆ Y → Y ∩ Ω ⊆ X →
  Fluctuation.dcovModE m₀ K Ω Y ≤ Fluctuation.dcovModE m₀ K Ω X
```

which is already `dcovModE_completion_le_of_noSpill`. The missing physical theorem must quantify over *nonzero* P6 assignments and construct a connected source/mark tree, yielding, for example,

$$D_+(Y)\le\alpha D_-(X)+d(2L+1)^d|J|+b_{\rm ret}(X,J,Y),\tag{17}$$

with either $b_{\rm ret}=0$ proved by active incidence or an additional coefficient factor paying $b_{\rm ret}$. P3 (4.48), printed pp. 79–80, has the $d(2L+1)^d$ marked-cube constant for its **nonmodular** assignment; equation (17) is a required interface, **not** an established P6 modular theorem. The analytic and history-localization clauses in VMOD-34–39/LFROOT3 remain required. In P7, `RHaloSep` alone does not prove the gas activity bound across a retained hole.

The cheapest next *geometric* test is to keep P5's every-offset openings and prove the correct arbitrary-offset hole-box statement, separating inherited thick parts from thin parts attached to counted new seeds. This preserves `RegionStep.image_Omega` and P5 (2.4). Between the two alternatives asked about, **route B (plain domains) is cheaper than fixed-grid R3 plus phase repair** in symmetry and region calculus: it leaves the P5 region step and its exact decompositions untouched and lets P3's nonmodular source tree visit the entire old label. It still needs a new `Def7` domain/size class, a proof that P5's history dependence and analytic spaces accept plain labels, and a physical splitting theorem for terms otherwise joined solely through a retained hole (VMOD-44 §3); it is not a proved closure. R3 requires phase-indexed histories and symmetry, plus the same unresolved P6/P7 producer questions. No version currently confirms blocker 3 closed.

**What this unblocks.** Equations (1)–(14) give a precise spill-free completion lemma and reusable aligned-region radius and halo specifications. They do not discharge blocker 3's P6 coefficient transfer, P7 gas bound, or the frozen `Balaban.logPartition_multiscale` (Root-F); `Balaban.lowTemperature_correlations` (Root-C) remains downstream. Verification here was read-only `rg` inspection of the named Lean declarations, `pdftotext -layout` of P5–P7 with a rendered check of P5 p. 502, and an independent $L=8$, $n_K=32$ finite-torus check of (10)–(11). No Lean file was edited or built.

**Confidence:** high for (1)–(15), the covariance counterexample, the distinction between fixed and every-offset boxes, and the conditional rectangular proof (16); medium for reusing every downstream ripeness lemma without implementation because the modified `RegionStep` has not been formalized; low for a full analytic P5–P7 induction under any of the proposed changes. The precise open conditions are the physical P6 assignment/active-root estimate, P5 continuous-to-fine size comparison if the fine size is used, the P7 retained-hole bridge, and (for phase R3) phase-aware history locality and H7 covariance.

---

# Round 2: exact all-offset spill and the retained-hole payment

**Freeze and verdict (17 October 2026).** This addendum uses the read-only repository at `feba164f53c5c13df058faa2c057c44e9ba55d90` and the P5–P7 PDFs identified in `review/SOURCES.md`. R3 remains withdrawn. The every-offset opening **does** admit inherited holes with forced active spill: the obstruction is a thin seam made when thick pieces approach diagonally, and it can have arbitrary length in $d\ge3$. A nonaligned flat face of a thick rectangle has no spill. The separate two-attachment bridge is charged by P5's size, but none of the displayed P6 assignment, P7 removed-component factor, P5 history clause, or existing H7 bound provides the *additional coefficient decay* needed when two individually cheap attachments become one output label. The precise source-to-physical producer is still open; the statements below refute closure **from the stated class bounds**, not the possibility of a stronger O(N) coefficient theorem.

## 1. Exact geometry of the every-offset opening

Work in $\pi_{k+1}$-cell coordinates on a sufficiently large torus, and let $\mathcal B_L$ be **all** translates of $[0,L-1]^d$ by one cell. For any cell set $S$ define

$$I_L(S)=\bigcup\{B\in\mathcal B_L:B\subseteq S\},\qquad
C_L(S)=I_L(S^c)^c=\{x:\text{every }B\in\mathcal B_L\text{ with }x\in B\text{ meets }S\}.\tag{18}$$

$I_L$ is monotone, contractive and idempotent: each point of $I_L(S)$ lies in one of its defining blocks, hence $I_L(I_L(S))=I_L(S)$. Consequently $C_L$ is monotone, extensive and idempotent. An integer block distance is at least $m$ exactly when the block misses $\operatorname{nbhd}_{m-1}F$. Therefore the **landed** `Geometry/Openings.lean:opening` and `openingIn` give the exact identities

$$\Omega'{}^c=C_L(A),\quad A=\operatorname{nbhd}_{\rho+4}U',\qquad
\Omega^c=C_L(A\cup\operatorname{nbhd}_3P).\tag{19}$$

Indeed $F=\operatorname{nbhd}_3U'$ and $m=\rho+2$ in `Region.OmegaPrime`; $\operatorname{nbhd}_{m-1}F=\operatorname{nbhd}_{\rho+4}U'$ by the sup-metric neighbourhood composition. Also `Region.Omega` keeps precisely the $L$-blocks inside $\Omega'$ missing $\operatorname{nbhd}_3P$, so $\Omega^c=C_L(\Omega'{}^c\cup\operatorname{nbhd}_3P)$. Idempotence and monotonicity imply $C_L(C_L(A)\cup B)=C_L(A\cup B)$, proving (19). This is the literal all-offset reading of P5 (2.3)–(2.4), (2.8), printed pp. 502–503, and of `Region/Step.lean:Region.OmegaPrime`, `Region.Omega`.

Here is an **exact necessary and sufficient spill test**, rather than a face-alignment heuristic. For a hole component $H\subseteq\Omega^c$ and an existing $L$-block union $X$, put

$$\mathfrak D_L(H;X)=H\setminus I_L(X\cup H).\tag{20}$$

Since $X=I_L(X)$, the completion $X\cup H$ is an $L$-block union if and only if $\mathfrak D_L(H;X)=\varnothing$. Proof: points of $X$ already have witnessing blocks inside $X\cup H$; every other point is in $H$ and has one precisely when it lies in $I_L(X\cup H)$. For an arbitrary block-union completion $Y\supseteq X\cup H$, each $x\in\mathfrak D_L(H;X)$ requires a block $B\subseteq Y$ containing $x$ with $B\nsubseteq X\cup H$. If the other complement components are at distance at least $L$ from $H$ and $X$ does not contain the outside sites of such a block, that block necessarily adds an **active** site. Without that separation, an added site might lie in another hole, so (20) is the exact test for the literal $X\cup H$ and the lower bound for arbitrary completions must mention the other holes. For a completely general finite configuration the exact minimum active spill is the finite set-cover quantity

$$s_\Omega(X,H)=\min_{\mathscr B\subseteq\mathcal B_L:\ X\cup H\subseteq\bigcup\mathscr B}
\left|\bigl((\bigcup\mathscr B)\cap\Omega\bigr)\setminus X\right|.\tag{21}$$

This formula includes all possible box choices and makes no unproved assertion that defect cells each require distinct new active cells. If $X\cup H$ is already a block union, (21) is zero. `DjMod` connectedness and whole-component validity impose further conditions on a chosen $\mathscr B$; (21) only measures the geometric box-cover obstruction.

There is also a closed-form **zero-spill** version of (21), valid even when other holes are nearby:

$$s_\Omega(X,H)=0\quad\Longleftrightarrow\quad
X\cup H\subseteq I_L(X\cup\Omega^c).\tag{21a}$$

For the forward direction, a zero-spill block union $Y$ lies in $X\cup\Omega^c$, hence $Y=I_L(Y)\subseteq I_L(X\cup\Omega^c)$. Conversely the inclusion makes $Y=I_L(X\cup\Omega^c)$ a block union containing $X\cup H$; it adds no active cell outside $X$. This is the exact answer to which inherited holes **force geometric active spill for a given old label**. It depends on the attachment label $X$ and the other holes, not solely on the curvature or side lengths of $H$. Whole-component validity can make the feasible `DjMod` family smaller, but cannot turn a positive $s_\Omega$ into zero.

The criterion distinguishes the proposed shapes sharply. Every nonwrapping rectangle whose side lengths are at least $L$ is $L$-open by the coordinate formula (16), so a thick rectangular inherited hole is spill-free under this cover, regardless of its residue modulo $L$. Nonrectangularity alone is **not sufficient** either: a union of $L$-open rectangles is $L$-open. A side shorter than $L$ is an obstruction for that rectangle, but it is **not necessary** for spill. In (19), if $2(\rho+4)+1\ge L$, then $A$ itself is $L$-open: it is a union of sup-norm balls of side $2(\rho+4)+1$, and each such ball is a union of $L$-blocks. Thus any intrinsic defect of $H=C_L(A)$ lies in $H\setminus A$. By `opening_disjoint_nbhd` and `opening_compl_subset`, more precisely

$$\mathfrak D_L(H;\varnothing)\subseteq H\setminus A
\subseteq \operatorname{nbhd}_{\rho+L+3}U'\setminus\operatorname{nbhd}_{\rho+4}U'.\tag{22}$$

This is a collar of radial width $L-1$; it can have arbitrarily large **length**. If $2(\rho+4)+1<L$, an inherited piece itself may be thinner than $L$, an additional obstruction allowed by the broad Lean `RadiusHyp` (which gives only an upper bound on $R_j$). In the intended large-radius P5 regime, the seam obstruction below survives even though every input piece is thick. A $P$-generated part $\operatorname{nbhd}_3P$ has side seven for a one-cell seed and can itself be thinner than $L$ when $L>7$; interactions between it and $A$ are governed by the same exact test (20), rather than by a clean inherited/new dichotomy.

### A thick inherited seam, for every $L\ge2$

Let $r=\rho+4$, let $w\ge1$, set $a=w-1+r$, and choose two $w\times w$ rectangles in the first two coordinates of $U'$:

$$U_1=[0,w-1]^2,\qquad U_2=U_1+(w-1+2r,\,w-1+2r+L).\tag{23}$$

Take the same nonempty interval $J_0$ in each remaining coordinate, and no $P$ seeds. In the first two coordinates $A=\operatorname{nbhd}_r U'$ is the union of two **thick** rectangles $A_1,A_2$ satisfying

$$\max_x A_1=\min_x A_2=a,\qquad
\max_y A_1=a,\quad\min_y A_2=a+L.\tag{24}$$

Their common range in each remaining coordinate is $J=\operatorname{nbhd}_rJ_0$. For each $j=1,\ldots,L-1$ and $z\in J^{d-2}$, put

$$p_{j,z}=(a,a+j,z),\quad q^-_{j,z}=(a-1,a+j,z),\quad q^+_{j,z}=(a+1,a+j,z).\tag{25}$$

**Proof of the obstruction.** Any $L$-block containing $p_{j,z}$ has an $x$-interval containing $a$ and a $y$-interval of $L$ consecutive cells containing $a+j$. The latter cannot lie wholly in the gap $[a+1,a+L-1]$, so it meets $y\le a$ or $y\ge a+L$. In the first case the block meets $A_1$ at $x=a$; in the second it meets $A_2$ there. Its other coordinate intervals contain $z\in J^{d-2}$. Therefore **every** block through $p_{j,z}$ meets $A$, and $p_{j,z}\in H=C_L(A)$. Conversely $q^-_{j,z}\in\Omega$: a block with $x$-interval $[a-L,a-1]$ and $y$-interval $[a+j,a+j+L-1]$ misses $A_1$ by its $y$ range and $A_2$ by its $x$ range. Similarly $q^+_{j,z}\in\Omega$ using $x\in[a+1,a+L]$, $y\in[a+j-L+1,a+j]$. The remaining-coordinate block intervals can be any intervals containing $z$. Finally, an $L$-block through $p_{j,z}$ contains either $q^-_{j,z}$ or $q^+_{j,z}$, because its $x$ interval of length at least two contains either $a-1$ or $a+1$. Hence

$$p_{j,z}\in H\setminus I_L(H),\qquad
Y\supseteq H,\ I_L(Y)=Y\quad\Longrightarrow\quad
q^-_{j,z}\in Y\ \text{or}\ q^+_{j,z}\in Y.\tag{26}$$

Choose $X$ attached to $H$ away from all $q^\pm_{j,z}$, as a bounded $L$-block collar near one end. Then every block-union completion $Y\supseteq X\cup H$ has at least $(L-1)|J|^{d-2}$ distinct active spill cells, by (26). In $d=3$, taking $|J|=N$ gives **at least $(L-1)N$ active cells**, with $r,L$ fixed. This is a long seam, not a flat-face residue effect. `Fluctuation/SizeModG1.lean:G1_cellCount` then forces a size increase at least linear in $N$ whenever its valid-label hypotheses hold: if $c_1=[3(2L-1)]^d$, $n_\pi(Y\cap\Omega)\le c_1(1+D(Y))$ implies $D(Y)\ge (L-1)N/c_1-1$ in coarse-cell units. More basically, P5 (1.34) must visit cover cubes meeting this active seam; no claim about an exact fine/continuous size equality is needed.

The shapes (23) can be made inputs of the **landed one-step region function**, not merely arbitrary $U'$: take two fine-lattice seed prisms translated by $L$ times the two shifts in (23), use the same phase in each coordinate, and apply `Region.Uprime L n1 ⌊Rprev⌋₊`, which performs the $\operatorname{nbhd}_{\lfloor R_{k-1}\rfloor+1}$ thickening internally. Each image is an equal translated rectangle of some width $w$; choose the translation after computing that width. Increase the torus period so these and the test blocks do not wrap. Put `P=Q=R=S=∅`, satisfying the four `RegionStep` subset fields. The points $p_{j,z}$ form a nearest-neighbour chain from $A_1$ to $A_2$, so they belong to the **same** component of $\Omega^c$ as both thick prisms. This proves a counterexample at the `RegionStep` set-function level for any $r=\rho+4$ and $L\ge2$; we have **not** proved that the chosen $Z_k$ occurs in every stricter admissible multiscale history. It corrects `VMOD-44` §2's inference that thickening by $r\ge L$ automatically makes the closed hole an all-offset block union. The old `omega_hole_face_misaligned` remains a fixed-grid theorem and is not the proof of (26).

For the abstract old-label test, take an earlier rectangular hole containing only the first long seed prism and an $L$-block active collar at one end; its union is a connected, whole-hole label with modular size bounded independently of $N$. In the landed chosen-cover size one block at the collar and a one-vertex graph suffice; in P5's all-eligible-cube continuous size a tree across the bounded collar has length $O_L(1)$. The new hole from (23) contains both thick prisms and the seam, so its whole-component completion forces (26). This is a consistent two-region **class-level** configuration; a full source history realizing it with a nonzero physical O(N) coefficient has not been constructed here.

## 2. What does, and does not, pay a two-attachment bridge

The geometric bridge already has a lower bound independent of the seam example. For a rectangular retained hole $H_N$ of length $N$, take valid labels $X_-=H_N\cup A_-$ and $X_+=H_N\cup A_+$ with one bounded active attachment at opposite ends. As proved in (15), each input modular size is $O_L(1)$, while the modular size of their union is at least $w(N-2L)$ in the landed chosen-cover model; P5 (1.34), printed p. 496, has a corresponding positive continuous-tree length. This says **where the output norm charges the distance**. It does not provide a factor in the coefficient that pays it.

**P6 assignment.** P6 (4.32)–(4.34), printed p. 34, first localizes an old boundary term in $X\cap\Omega_{k+1}$, allows disconnected $Y_1$, and says P3 (4.48)–(4.49) continue with modular sizes. P3 (4.48), printed pp. 79–80, joins each mark to a source tree that meets *all* eligible cubes of the **plain** old label; a modular source tree need not reach the far side of a retained hole. The P6 sentence is the desired transfer, not a displayed proof of its missing bridge estimate. In the seam family, completion can add $\Omega(N)$ active cells with zero marks; an H7-admissible constant old coefficient has all interpolation derivatives zero. The geometric class bound therefore cannot yield P6 (4.34) uniformly from old H7 and the P3 mark gain. This does not exhibit such a coefficient in the actual O(N) producer; `OPEN-P6-INHERITED-HOLE-ASSIGNMENT` and the mixed covariance/active-root premises of `LFROOT3.md` remain genuine physical obligations.

**P7 retained-hole bridge.** P7 (3.26), printed p. 527, moves old boundary terms meeting a **removed** component into the braces. Page 528 takes connected clusters of those domains and assigns the union of their labels and the thickened removed components as a polymer; (3.27)–(3.28) assert its activity bound. P7 (3.10), printed p. 520, gives $e^{-p_2(\beta_k)-H_k|c|_\eta}$ once for each **removed** component $c$, and p. 528 cites also the better $3\kappa/2$ old-boundary rate. Put small removed components $c_\pm$ at gaps of a fixed length $g>\omega_k$ and larger than the P7 halo radius beyond the two ends of $H_N$, and extend $X_\pm$ to meet their respective $c_\pm$. The old sizes and $|c_\pm|$ remain bounded as $N\to\infty$, whereas the union output has size $\ge cN-O(1)$. For positive scalar old coefficients chosen below their H7 bounds and positive allowed removed-component weights, the product weight of this connected *geometric* cluster is bounded below by a positive constant depending on the fixed scale but **not** on $N$. It cannot satisfy $|w_N|\le B e^{-\kappa D(Y_N)}$ with volume-independent $B$ and $\kappa>0$, since the right side tends to zero. Equivalently, the two fixed $p_2$ factors would have to dominate $\kappa cN-O(1)$. `Fluctuation/SizeModUnion.lean:G3_dcov` deliberately assumes overlap in an **active** cell; $X_-\cap X_+=H_N$ does not meet it. `LargeField/R/RHaloSep.lean:halo_disjoint_comp` excludes halos of removed components from other components, but says nothing about the path through a distinct retained $H_N$. This is an abstract-class counterexample to the proposed P7 estimate from the displayed weights; a physical cancellation or active-core clustering rule remains possible. It agrees with `VMOD-41.md` §2 and `VMOD-42.md` §§1–3.

The scalar class test can respect the source symmetry: assign the same real positive constant to every image of each test label under the finite group of partition-preserving translations and lattice rotations, and zero to other label orbits. Modular size and the H7 upper bound are invariant under that group. The coefficients are constant in spin and source fields, hence analytic and $O(N)$-invariant. The particular positive two-label product above remains present; orbit averaging or duplication cannot create the missing factor $e^{-\kappa cN}$ in a bound on absolute cluster weights. This still tests the **abstract H7 class**, not a coefficient computed from the physical density.

**History and large-field factors.** P5 (1.33)–(1.36), printed pp. 496–497, require whole-component labels and history dependence and define the modular length; they do not multiply an old $B^{(k)}(X,\mathbb A_k)$ by decay in the diameter of a hole it touches. P5 (2.47)–(2.48), printed pp. 512–513, keep the old boundary expression in the fluctuation integral. The operator estimate P5 (1.30)–(1.31), printed p. 495, places $e^{-\ell p_2(\beta_k)-H_k|Z|_\eta}$ on an **integrated large-field component operator**, separate from H7's coefficient bound (1.38)–(1.39), printed p. 497. P7 (3.26) factors the retained-component operator $T''_k(Y_k)$ *outside* the removed-component gas; its retained factor is therefore not present in the claimed coefficient bound for $\rho''_k(X)$ or the resulting H7 term. Moving part of it into those coefficients is a change of representation with a reserve ledger, not an implication of (3.10).

Even the proposed direct payment by $H_k|Z|_\eta$ alone has no **unconditional** geometry inequality for a small birth component. P5 (1.2), printed p. 489, sets $R_j=R_0(\log(a\beta_{j-1}))^2$, while (1.30) sets $H_j=H_0\log\beta_j$. For an abstract one-cell $Z$ at a fixed scale, $|Z|_\eta$ is a fixed finite number under that scale's volume normalization, but its enlarged hole has diameter $\asymp R_j$ and admits opposite attachments at distance $\asymp R_j$; for fixed $R_0,H_0,\kappa>0$ and large $\beta_j$, the quadratic logarithm eventually exceeds $H_0|Z|_\eta\log\beta_j$. An admissible **physical** $Z_j$ may itself have a radius-dependent minimum volume, so this one-cell calculation is a refutation only of the *bare* inequality without that extra geometric hypothesis. The polynomial $p_2(\beta_j)=A_2(\log\beta_j)^{p_2}$ could numerically pay a bounded-at-one-scale bridge if a share were retained, but P5 (1.31) and P7 (3.10) do not allocate such a share to every boundary coefficient, and P7 already uses its removed-component share for the gas. For a long component $|Z|_\eta\gtrsim N$ may make the $H_k$ factor large enough numerically, yet the same missing allocation and repeated-use issue remain. Thus “the large-field factor pays the hole length” is a **new theorem to construct**, not a consequence of the printed bounds. `LFH7PRIME2.md` §G1–G2 reaches the same placement and double-spending warning for a proposed shell charge.

## 3. Nearest covariant repair and Lean interface

The smallest class change supported by these counterexamples keeps the **active attachment set** explicit. A boundary object carries a finite union $C$ of active $\pi'_k$ blocks, a set $\mathcal P$ of whole hole components whose *histories* it reads, and, for each $H\in\mathcal P$, the set $A_H(C)$ of active cells where $C$ attaches to $H$. Its field locality is on $C$ and the source-required adjacent strips; its history locality is on the whole components in $\mathcal P$. These are sets, with no distinguished corner or tie-breaking root, so translations and lattice rotations carry $(C,\mathcal P,A_H)$ to the transformed data and preserve covariance. This uses the existing separation between `LargeField/Def7Hist.lean:D7Bdry.loc_field` and `loc_hist` described in `VMOD-44.md` §1, but **changes** the `FineValid`/`DjMod` support and size clauses.

If $A_H$ has one attachment, completion of $H$ for history costs no bridge in the active label. If it has two or more, let $b_H$ be the infimum of the ordinary positive-length trees in $H\cup C$ joining the attachment sets, with the P5 (1.34) normalization (or `bondCost (scaleW ...)` in the fine model). The infimum over all trees is Euclidean-covariant. A term or connected gas cluster that **really couples** those attachments must carry either an extra $e^{-\tau b_H}$ coefficient factor, or a single allocated birth credit $q_H\ge\tau b_H+E_H$ where $E_H$ pays its rooted entropy; the sum of all such allocations from one component must be bounded by its unused P5/P7 operator reserve. If it does not couple them, split it into active-core terms and do not make a Mayer edge solely because the history pocket is shared. For a connected finite hole of $h$ coarse cells, a spanning tree has $h-1$ cell bonds, and adjoining $m$ attachment cells takes at most $m$ further bonds, so a coarse corridor can always be charged by $h-1+m$ bonds. **This is only a geometric upper bound**; the available reserve must still dominate it after earlier expenses. The one-cell, $R_j\asymp(\log\beta)^2$ example shows why $H_j|Z|$ alone is not a universal such reserve.

A precise two-size producer obligation, suitable for the landed objects, is the following. For each *nonzero physical* P6 assignment $(X,J,Y)$, define

$$b_6(X,J,Y)=\bigl[D_+(Y)-L^{-1}D_-(X)-d(2L+1)^d|J|\bigr]_+.\tag{27}$$

Prove either $b_6=0$ by a physical active-rooted incidence theorem or an additional factor $e^{-\kappa b_6}$ in its coefficient. For each *nonzero physical* P7 cluster $\Gamma$, with old labels $X_i$, removed components $c_r$ and output $Y_\Gamma$, define

$$b_7(\Gamma)=\Bigl[D_+(Y_\Gamma)-\sum_iD_-(X_i)
 -2dL(|\Gamma_{\rm old}|-1)- (dL+d+3)\sum_r|c_r|\Bigr]_+.\tag{28}$$

The exact constants in (28) are the landed `G3_dcov` active-overlap junction constant and `SizeModExtend` newly-active-cell constant; (28) is a **residual definition**, not an established geometric inequality when the overlap is only in a hole. The output weight must supply $e^{-\kappa b_7}$, or the construction must prove that such a cluster is absent/splits on active cores. A shared retained history is insufficient for a gas edge. In Lean, retain `Fluctuation.IsPiPrimeUnion`, `DjMod`, `dcovModE`, `dcovModE_completion_le_of_noSpill`, `G1_cellCount`, `G3_dcov`, and `RHaloSep` as their actual landed statements; add `IsLBlockUnion`/`I_L` defect lemmas around `RegionStep.Omega`, an attachment relation on `OmegaComp`, and **physical producer** hypotheses for (27)–(28). The paper-to-fine comparison `OPEN-PAPER-FINE-REALIZATION` in `Def7FineSize.lean` is still required before using these fine residuals to assert P5's continuous-tree H7.

Concretely, the first new Lean leaf should be the following signature shape (names below are **proposed**, while the names after `:=` in the prose above are landed):

```lean
def allOffsetInterior (L : ℕ) (S : Set (Torus d n)) : Set (Torus d n) :=
  {x | ∃ c, x ∈ lblock L c ∧ lblock L c ⊆ S}

theorem union_hole_isLBlockUnion_iff {X H : Set (Torus d n)}
    (hX : IsLBlockUnion L X) :
  IsLBlockUnion L (X ∪ H) ↔ H ⊆ allOffsetInterior L (X ∪ H)

theorem omegaPrime_compl_eq_close (st : RegionStep d L n0 n1 Rprev Rk) :
  (st.OmegaPrime)ᶜ = (allOffsetInterior L
    ((nbhd (⌊Rk⌋₊ + 4) st.Uprime)ᶜ))ᶜ
```

The last line is mathematical Lean shape: parentheses, casts, and the neighbourhood-composition theorem must be elaborated in the actual module. The counterexample leaf should quantify $d\ge3$, $L\ge2$, a seam length $N$, and a sufficiently large period, construct `st` with empty new seeds, and return a component `H` of `st.Omegaᶜ` and $(L-1)N$ distinct coarse cells $q$ in `st.Omega` such that every `IsLBlockUnion L Y` with `H ⊆ Y` contains at least one of the two flanks for each seam cell. Pullback through `IsPiPrimeUnion` then yields the `cellCount` lower bound. The producer leaves must quantify **nonzero** assignments or clusters and attach either the zero-residual proof or a coefficient bound with the extra factor in (27) or (28); a geometric lemma alone cannot discharge those leaves.

If the actual P6/P7 coefficients factor over active cores, route B of `VMOD-44.md`—plain domains with whole-component *history decorations*—is the cheaper specialization: it removes the artificial retained-hole edge and lets P3's plain source tree prove its original (4.48). If a real term couples distant active attachments through a hole, plain domains alone cannot represent it as one local connected term; the paid multi-attachment object above is then the nearest repair. Neither choice can be declared proved without the actual coefficient identity, its analytic-space transport, and one-use reserve accounting. The fixed-grid R3 changes the regions and covariance and addresses neither producer obligation.

**What this unblocks and status.** Equations (18)–(26) settle the exact all-offset **geometry** and replace the fixed-grid long-face argument by a valid thick-seam counterexample. Equations (27)–(28) isolate the two remaining coefficient obligations. Blocker 3 is **not closed by P5–P7's displayed estimates or the landed geometric lemmas**; closure needs an active-core splitting theorem or a covariant paid-attachment producer with a no-double-spend large-field ledger. Root-F and Root-C remain downstream. Confidence: high for (18)–(26), the rectangular/no-rectangle distinction and the abstract impossibility from fixed old/removed weights; high for the source placement of P5/P7 factors; medium for realizing the thick-seam input in a stricter multiscale history; low for choosing between active-core splitting and a paid producer before the actual O(N) coefficients are constructed. No Lean file or file under `/home/scott/Balaban` was edited.

# Round 3: testing the physical paid-attachment claim

Read-only Lean snapshot checked for this round: `/home/scott/Balaban` at commit `f1c1541ac0fa130c102838c376c9eee38b7fbe77`. Journal pagination below is from the P5, P6 and P7 PDF text already extracted in this scratch directory; B.7 is cited to its separate scratch note, not as a journal result. No source file outside this directory was edited.

**Verdict.** Theorem B.7 of `/home/scott/Balaban-scratch/astra-kf0b/KF0B.md`, lines 527–650, gives a rigorous warning against scalar active-core factorization *after* a shared good variable is integrated. I agree that such a factorization cannot be used as a general rule for final coefficients. It does **not** prove that the specific P7 coefficient at a *retained large-field hole* fails to split: B.7 integrates a good middle variable, whereas the retained component and its output field remain outside the removed-component integral in P7 (3.26), printed p. 527. Conversely, none of the landed massive-kernel decay statements proves the requested factor $e^{-\kappa b_6}$ or $e^{-\kappa b_7}$ for a physical assignment or cluster. In fact, the proposed inference from the current H7 class, P7's displayed factors, and those kernel bounds is false. Thus the two proposed closures cannot yet be selected as a theorem about the actual $O(N)$ coefficients. The nearest true result is the conditional linked-producer lemma below, together with a concrete class-level counterexample to its missing premise. **Blocker 3 remains open.** This distinguishes a failure of the claimed deduction from a counterexample to Balaban's physical construction.

## 3.1 What B.7 proves at each integration order

Use B.7's notation $A(y)=\int_Ge^{\epsilon y\tanh x}\,d\gamma(x)$, $B(y)=\int_He^{\epsilon y\tanh x}\,d\gamma(x)$, and $R=B/A$. At a fixed retained value $t$ of the middle block, the two end-block cutoff ratios multiply exactly: the joint ratio is $R(\tanh t)^2$. If the middle good block is then integrated, the four cutoff weights satisfy

$$w_\varnothing=\int_G A(\tanh t)^2d\gamma(t),\quad w_a=w_c=\int_G A(\tanh t)B(\tanh t)d\gamma(t),\quad w_{ac}=\int_G B(\tanh t)^2d\gamma(t).\tag{29}$$

Because $R$ is nonconstant on $G$ (B.7 (B.55)), strict Cauchy–Schwarz gives $w_\varnothing w_{ac}>w_aw_c$. Equivalently the covariance of the two conditional ratios under probability proportional to $\mathbf1_G A^2d\gamma$ is positive. Hence the scalar log coefficient with activating set $\{a,c\}$ is nonzero, although this set is disconnected. Its *linked footprint* includes the middle good block $b$. This is a proof of nonfactorization of the **integrated scalar** weights, not a proof that the conditional functions at fixed $t$ fail to multiply. B.7 itself explicitly limits its conclusion to the exact cutoff-cell reading and does not identify that reading with P7's prepared density. In the retained-hole problem the component $H$ is large-field data and its output is not integrated in the bracket of P7 (3.26). The exact identity `LargeField/R/RGasRepCoupled.lean:Rop_famDecompRestricted_coupled` leaves the common $\xi$ integral and the output $\psi$ in place; `prod_mul_Rop_famDecompRestricted_coupled` also leaves the coupling $f(\psi,\xi)$ in place. Neither theorem gives scalar core factorization after the $\xi$ integral. A proof for the actual coefficients must say which shared variables are integrated, which are conditional, and which linked footprints remain. P7 pp. 527–528, (3.26)–(3.28), states the Mayer reorganization but does not supply that distinction as a coefficient identity.

## 3.2 A rigorous obstruction to automatic termwise payment

Retain the rectangular $H_n$, $X_-=H_n\cup A_-$, $X_+=H_n\cup A_+$ of Round 2, with bounded active collars $A_\pm$ at opposite ends, and put bounded removed components $c_\pm$ next to the respective collars. Increase the torus period with $n$, keeping $d,L$ and all collar, halo and component sizes fixed. The Round-2 tree calculation gives constants $C_0,C_1>0$ and $w>0$, independent of $n$, with

$$D_-(X_-)+D_-(X_+)\le C_0,\qquad D_+(Y_n)\ge w(n-2L)-C_1,\qquad |c_-|+|c_+|\le C_1.\tag{30}$$

For two old labels and two removed components, (28) therefore gives, writing $C_2=C_0+C_1+2dL+(dL+d+3)C_1$,

$$b_7(\Gamma_n)\ge [w(n-2L)-C_2]_+\longrightarrow\infty.\tag{31}$$

Choose a real $u>0$ below the old H7 bound at $X_\pm$ and a fixed allowed removed weight $t>0$ for each $c_\pm$. They may be arbitrarily small but are independent of $n$. The connected **full-label geometric** Mayer family with these four objects has the nonzero product weight

$$|W_n|=t^2(e^u-1)^2>0,\tag{32}$$

since the old labels meet in $H_n$. For every fixed $A<\infty$ and $\kappa>0$, (31)–(32) contradict $|W_n|\le A e^{-\kappa b_7(\Gamma_n)}$ for sufficiently large $n$. This is an exact implication failure: H7, the two fixed P7 (3.10) factors, and any independent Green-kernel bound cannot imply a termwise paid-bridge estimate for all permitted old coefficients. A coefficient constant in the fields has no covariance line crossing $H_n$. To make the class test history-local, on each history and label set it equal to $u$ precisely when the whole components meeting that label have the chosen local-history pattern, and zero otherwise; assign the same value on every image of this pattern under partition-preserving translations and lattice rotations. Agreement of the local histories of components meeting the label then preserves its value, exactly as `D7BdryPost.loc_hist` requires. It is constant in all fields and sources, so `loc_field`, analyticity, reality and $O(N)$ invariance are immediate; choosing $u$ below the minimum H7 bound for the two bounded-size label orbits gives `D7BdryPost.bound`. This construction tests the **abstract class** and the full-label cluster convention of P7 p. 528. It does not assert that a coefficient computed from the low-temperature $O(N)$ density equals this chosen constant. If an actual source-to-gas identity instead disconnects these labels on their charged active cores, then this particular geometric family is absent from that gas; proving that identity is precisely the alternative producer obligation.

The P6 seam is independent of any crossing covariance. Round 2 (23)–(26) gives at least $(L-1)n$ new active cells under a whole-component completion with an empty mark set $J$. By `Fluctuation/SizeModG1.lean:G1_cellCount`, a valid completed label has $D_+(Y_n)\ge (L-1)n/[3(2L-1)]^d-1$, while the old one-attachment label has $D_-(X_n)\le C_3$ for a fixed $C_3$. Thus

$$b_6(X_n,\varnothing,Y_n)\ge (L-1)n/[3(2L-1)]^d-1-C_3/L\longrightarrow\infty.\tag{33}$$

An H7-admissible old coefficient may depend only on the whole component's *history* and be constant in the fluctuation field. It then has no marked derivative and no crossing Green line. The current H7 premises do not force its zero-mark completed assignment to vanish or give it (33)'s exponential. This does **not** prove that P6's actual assignment produces such a nonzero term: P6 p. 34, (4.32)–(4.34), asserts the assignment estimate without specifying a restriction that would exclude it. The exact missing theorem is either that such assignments have zero coefficient, or a new source-to-coefficient payment. In particular, a decay theorem for a massive covariance cannot alone pay a purely historical completion cost.

## 3.3 Audit of the landed decay estimates

The following are genuine landed estimates, with their objects and hypotheses kept visible.

| Declaration | Estimate actually obtained | Missing bridge to (27)–(28) |
| --- | --- | --- |
| `Balaban/Fluctuation/CovarianceWeighted.lean:cov_entry_decay` | Under `XData` for all resolvent parameters, a constraint field, and $\delta^2\operatorname{smallConstX}\le1/4$, a covariance matrix entry is at most $C(d,L,a_k,x)e^{-[xAgmonRate(d,L)/L]\operatorname{torusDist}(p,q)}$. | No formula for a P6 assignment or P7 Mayer coefficient as a connected sum of such entries. |
| `Balaban/Fluctuation/CovSqrtSupComplex.lean:covC_entry_decay`, `covC_sqrt_entry_decay` | Complex decoupled covariance and square-root entries obey the same geometric rate, assuming `XData G ... κ s` for every spectral parameter and the constraint and smallness premises. | No connected-footprint expansion, determinant control, or bridge incidence for a retained hole. |
| `Balaban/Green/CoarseOperator.lean:coarseGreen_decay` | A coarse Green entry decays at its `trRate d L`, under its positivity, mass and scale hypotheses. | It is an operator-kernel statement, not a coefficient bound. |
| `Balaban/Green/FinalMassGreen.lean:finalMass_inverse_decay` and `Balaban/Green/FinalComplexHessian.lean:finalHessianC_inverse_decay` | For the final massive reference operator, off-diagonal entries decay at `finalRate d L`; the complex spin Hessian also has a local diagonal term. | These concern the final reference Hessian. `FinalMassGreen.lean` explicitly leaves its physical-density identification open and they give no general P6/P7 cluster identity. |
| `Balaban/Green/FinalLiftDecayResponse.lean:composeField_response_le` | Subject to `BgHyp`, `Dec2.OpSetting`, domain and data-agreement premises, a response to a distant data change is bounded by a constant times $e^{-\gamma_w n}$. | This is one response difference, not a mixed linked coefficient across every attachment or a budget ledger. `Balaban/Fluctuation/FarDecay.lean` also takes `WeightedProp51` as an explicit input. |

For example, `covC_entry_decay` gives a rate $\mu_C=xAgmonRate(d,L)/L$ in its torus-distance units. To use one crossing line of length $\ell$ to pay a deficit $b$, one must prove $\mu_C\ell\ge\kappa b$ **after** the fine/coarse and continuous-tree comparisons, and still pay the graph count. For a linked graph with edges $e$, the required inequality is $\sum_e\mu_e\ell_e+q\ge\kappa b+E$, where $E$ pays the linked-family entropy and $q$ is a genuinely unused birth credit. None of the listed declarations supplies a map from a nonzero P6 assignment or P7 cluster to those edges, an inequality between their lengths and $b_6$ or $b_7$, or an allocation $q$. The rates $\mu_e$ are fixed by the operator hypotheses; the class parameter $\kappa$ and the size comparison cannot simply be identified with them. The (33) example has no edges at all, so its missing payment cannot be recovered by improving a pointwise kernel constant.

The landed gas results make the boundary equally explicit. `LargeField/R/RGasRepDecor.lean:gasDecor_eq` proves an exact combinatorial identity for decorated couplings $b_X(S)$ with $b_X(\varnothing)=0$, light objects $(X,S)$, and charged supports $c_x(X)\cup\bigcup_{m\in S}c_z(m)$; its header says these weights are not the old undecorated `gasK`. It does not construct $b_X(S)$ from `Rep.B` or prove a crossing estimate. `LargeField/R/RGasCore.lean:gas_activity_bound_physical` assumes `hB`, `hτ`, `hXY`, `hXZ`, `hzd` and the numerical `hh`. The specialized `LargeField/R/RGasCoreFinal.lean:gas_activity_bound_physical_of_D7BdryPost_halo_of_removed_factor_run` still assumes `hrem : ∀z, ‖τ z‖≤\exp[-p2Run-H|c_z|]` and core-label identities. Its conclusion bounds `gasK` on the chosen core support, **conditional on that representation and those inputs**; it is not an assertion that every full-label P7 cluster has $e^{-\kappa b_7}$. `LargeField/R/D7GasRootEntropy.lean` explicitly labels the retained-hole bridge open. This is why a gas bound on active cores cannot be substituted for the requested physical producer theorem.

## 3.4 The nearest true producer statement and a one-use ledger

Here is the exact elementary statement that a linked physical construction would be able to use. For one assignment or cluster $\gamma$, let $a_\gamma\in\mathbb C$ be its coefficient, $A_\gamma\ge0$ its ordinary old-term/removed-factor prefactor, $b_\gamma\ge0$ its deficit (27) or (28), $E_\gamma\ge0$ its entropy charge, and $\mathcal G_\gamma$ a finite family of linked witnesses. Suppose each witness $g$ has a complex amplitude $a_{\gamma,g}$, a nonnegative crossing cost $\ell_{\gamma,g}=\sum_{e\in g}\mu_e\operatorname{dist}(e)$, and a nonnegative allocated birth credit $q_{\gamma,g}$, with

$$a_\gamma=\sum_{g\in\mathcal G_\gamma}a_{\gamma,g},\quad
|a_{\gamma,g}|\le A_{\gamma,g}e^{-\ell_{\gamma,g}-q_{\gamma,g}-E_\gamma},\quad
\sum_g A_{\gamma,g}\le A_\gamma e^{E_\gamma},\quad
\ell_{\gamma,g}+q_{\gamma,g}\ge\kappa b_\gamma.\tag{34}$$

Then the triangle inequality and monotonicity of the exponential give, with **every constant shown**,

$$|a_\gamma|\le\sum_g A_{\gamma,g}e^{-\ell_{\gamma,g}-q_{\gamma,g}-E_\gamma}
\le e^{-\kappa b_\gamma-E_\gamma}\sum_gA_{\gamma,g}
\le A_\gamma e^{-\kappa b_\gamma}.\tag{35}$$

This proves the paid factor *if* the physical linked expansion and length/credit incidence in (34) are produced. Taking $b_\gamma=b_6$ or $b_7$ gives precisely the two bounds requested in Round 2. A single response bound is insufficient for the first equality in (34); a uniform tree or walk expansion of the logarithm and determinant, with activation separate from footprint, is needed. If there is no crossing edge, (34) says explicitly that $q_{\gamma,g}\ge\kappa b_\gamma$. If the coefficient actually splits into factors on separate active cores, the correct gas should omit the artificial full-hole edge instead of paying it.

For each component $H$ when it is created, write its **available** operator exponent as $Q_H\ge0$; do not call all of P5's $H_k|Z|_\eta$ available without subtracting the portions already used to prove the operator, removed-component factor, normalization, and earlier boundary bounds. In any simultaneously present compatible family $\mathcal F$ of assignments or clusters, a valid ledger must supply nonnegative $r_H$ and $q_H(\gamma,g)$ such that

$$r_H+\sum_{(\gamma,g)\in\mathcal F}q_H(\gamma,g)\le Q_H,
\qquad q_{\gamma,g}=\sum_Hq_H(\gamma,g).\tag{36}$$

Indeed, with $s_H=Q_H-r_H-\sum_{\mathcal F}q_H\ge0$ the identity

$$e^{-Q_H}=e^{-r_H}\prod_{(\gamma,g)\in\mathcal F}e^{-q_H(\gamma,g)}e^{-s_H}\tag{37}$$

shows that no component's exponent was spent twice. These equalities hold **for each family**; moving factors from P7's retained operator outside the braces of (3.26) into its gas coefficients also requires a source-level algebraic reorganization preserving (3.26). P7 (3.10), printed p. 520, pays removed components, while the retained operator remains outside the braces on p. 527. P5 (1.30)–(1.31), printed p. 495, gives the operator small factor, not (36) or the algebraic transfer. For a small abstract birth component, Round 2's $R_j\asymp(\log\beta)^2$ versus $H_j\asymp\log\beta$ example shows that $H_j|Z|_\eta$ alone cannot be asserted to dominate $\kappa b$ without a minimum-volume or geometry hypothesis. Hence (36) must include an explicit numeric lower bound on the **unused** credit or the linked line charge; it cannot be filled with a symbolic large-field factor.

The corresponding covariant class repair is a boundary object $(C,\mathcal P,(A_H)_{H\in\mathcal P},q)$: $C$ is the active footprint, $\mathcal P$ the retained whole-component histories read, $A_H$ the finite active attachment set at each $H$, and $q$ its recorded, one-use birth credit. The linked spatial footprint may pass through a good integrated block, as in B.7, while its activating set is disconnected. A retained hole is included in a charged tree only when a witness or allocated credit pays that tree. All objects are finite sets and metric tree costs; translation and lattice rotation move them naturally, so no fixed grid phase or chosen root breaks Euclidean covariance. Merely changing to plain domains (route B of `VMOD-44.md`) does not prove that a genuinely linked coefficient can be separated. The smallest valid class change therefore records **both** activation and linked footprint, plus attachment credits when a retained hole is traversed; an active-core specialization is allowed only after an exact factorization theorem for those particular coefficients.

## 3.5 Lean producer signatures and status

The exact landed carriers available for the boundary coefficient are `LargeField/Def7.lean:Rep.B` and `D7BdryPost.bound`; the latter is a bound on `rep.B A X ψ ψ' h g` at a valid domain, not on a P6 assignment or P7 cluster. The exact fine size is `LargeField/Def7FineSize.lean:d7SizeAt F k Om X` (the real value of `dcovModE`, only meaningful for `FineValidAt`); `d7SizePre` is the corresponding pre-`R` size. The current repository has **no type of physical P6 assignments or physical P7 linked clusters carrying both a coefficient and a crossing-witness graph**. Consequently there is no honest closed Lean signature using only landed physical constructors for the requested producer. Here is a fully typed *interface shape*, with `Phys6` and `Phys7` explicitly new types and `Dold`, `Dnew`, `oldSum`, `remCard` required to be identified with `d7SizeAt`/`d7SizePre` and the actual region step before it can be claimed physical:

```lean
-- Proposed definitions and theorems; none of these names is landed.
def bridgeDeficit6 {Phys6 : Type*} (Dold Dnew : Phys6 → ℝ)
    (marks : Phys6 → ℕ) (d L : ℕ) (a : Phys6) : ℝ :=
  max 0 (Dnew a - Dold a / (L : ℝ) -
    (d : ℝ) * (2 * (L : ℝ) + 1) ^ d * (marks a : ℝ))

def bridgeDeficit7 {Phys7 : Type*} (Dnew oldSum : Phys7 → ℝ)
    (oldCard remCard : Phys7 → ℕ) (d L : ℕ) (g : Phys7) : ℝ :=
  max 0 (Dnew g - oldSum g -
    (2 * (d : ℝ) * L) * ((oldCard g : ℝ) - 1) -
    ((d : ℝ) * L + d + 3) * (remCard g : ℝ))

-- Specifications for the missing physical producers.  These are Props, not proofs.
def P6PhysicalPaid
    {Phys6 : Type*} (nonzero : Phys6 → Prop) (amp : Phys6 → ℂ)
    (base Dold Dnew : Phys6 → ℝ) (marks : Phys6 → ℕ)
    (d L : ℕ) (κ : ℝ) : Prop :=
  ∀ a, nonzero a →
    ‖amp a‖ ≤ base a * Real.exp (-κ * bridgeDeficit6 Dold Dnew marks d L a)

def P7PhysicalPaid
    {Phys7 : Type*} (nonzero : Phys7 → Prop) (amp : Phys7 → ℂ)
    (base Dnew oldSum : Phys7 → ℝ) (oldCard remCard : Phys7 → ℕ)
    (d L : ℕ) (κ : ℝ) : Prop :=
  ∀ g, nonzero g →
    ‖amp g‖ ≤ base g * Real.exp (-κ *
      bridgeDeficit7 Dnew oldSum oldCard remCard d L g)

-- The conditional theorem proved by (35); the physical work is `hlinked` and `hcharge`.
theorem paidBridge_of_witness {A : Type*} (amp : A → ℂ)
    (base residual crossing credit : A → ℝ) (κ : ℝ)
    (hbase : ∀ a, 0 ≤ base a)
    (hlinked : ∀ a, ‖amp a‖ ≤ base a * Real.exp (-(crossing a + credit a)))
    (hcharge : ∀ a, κ * residual a ≤ crossing a + credit a) :
    ∀ a, ‖amp a‖ ≤ base a * Real.exp (-κ * residual a) := by
  intro a
  calc
    ‖amp a‖ ≤ base a * Real.exp (-(crossing a + credit a)) := hlinked a
    _ ≤ base a * Real.exp (-κ * residual a) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith [hcharge a])) (hbase a)
```

`P6PhysicalPaid` and `P7PhysicalPaid` are **specifications, not landed results**; the proof of `paidBridge_of_witness` is just exponent arithmetic. The missing physical theorems must build the linked decomposition (34) from the actual coefficients, prove its length/credit inequality, and verify (36). In particular the needed P7 theorem must identify its `amp` with the decorated coefficient generated from `Rep.B` and the removed operator, not merely with an arbitrary `gasK` input. It must also prove its result on P5's continuous-tree size (1.34), or first discharge `Def7FineSize.lean`'s `OPEN-PAPER-FINE-REALIZATION` comparison; a fine-size theorem alone does not close the printed H7.

**What is settled.** B.7 proves scalar post-integration nonfactorization, (30)–(33) refute automatic per-cluster payment from the present H7 and operator-kernel inputs, and (34)–(37) give the exact sufficient producer and no-double-spend ledger with its proof. The available Lean theorems give kernel decay and conditional gas estimates but no source-to-linked-coefficient construction satisfying (34)–(36). The actual $O(N)$ paid producer and the alternative exact active-core factorization remain unproved; blocker 3 and hence the dependent Root-F/Root-C path are not closed. Confidence: high in the algebraic and class-level counterexamples, the integration-order distinction, and the audit of the named landed statements; low in either physical closure until its producer identity and budget are constructed.

# Round 4: a fixed localization recipe for the new boundary terms (R4b)

**Status and source.** This round uses the read-only P3, *Commun. Math. Phys.* **182** (1996), 33–82, §3 Proposition 3.1 (printed p. 67) and §4 (starting p. 67), P6, *Commun. Math. Phys.* **198** (1998), 1–45, §4 (printed pp. 32–36), and P7, *Commun. Math. Phys.* **198** (1998), 493–534, (3.22)–(3.25) (printed pp. 526–527). The P3 text layer is badly garbled in formulas; its proposition number and qualitative analyticity/locality statement are legible, and the precise coefficient statement below is taken from the landed Lean `Localization.AbstractExpansion.coef`, `Localization.I5Expansion.evTerm` and `localization_expansion`, not reconstructed from unreadable glyphs. P7's prose and equation numbers are legible. The first `origin/main` check for W1007 did not yet include W1001.

## 4.1 A deterministic choice, and its exact hypothesis

Fix the kept history $A'$, a finite compatible family $\Gamma$ of removed clusters, the output field and external variables. Let $q$ run over the **finite source summands** of the four exponent differences made in P7 (3.22)–(3.25): the main action with the background changed from $(Y\cup Z)^c$ to $Y^c$, the effective-energy Taylor difference (3.24) and domain completion (3.25), the analogous generating-functional difference, and the remainder difference. Denote their sum by
$$\Delta_\Gamma(u)=\sum_q\Delta_{q,\Gamma}(u)
 = E_{\rm old}(A'\cup\Gamma;u)-E_{\rm new}(A';u).\tag{38}$$
Here $E$ is the exponent **excluding** the old boundary sum and the removed kernels, so there is no double counting in (3.26). This is a specification of the pieces to localize, not a claim that a landed Lean definition already names each $\Delta_{q,\Gamma}$. `Def7.SFCtx.{Ares,Fres,Rres}` names the new small-field terms and `Rep.bdrySum` names the old boundary sum; the corresponding old-background exponent and its subtraction have no single landed definition.

For each $q,\Gamma$, choose the P3 decoupling extension $F_{q,\Gamma}(u,s)$ on the cut-parameter polydisc, with $F_{q,\Gamma}(u,\mathbf1)=\Delta_{q,\Gamma}(u)$. This choice is fixed by applying the landed decoupled background/Green construction (`Localization.DecoupledFunctional`, `I5Functional` where applicable) to each background-dependent source summand, and the P6 localized fluctuation/old-term expansions to the other summands; it is **not** an arbitrary analytic interpolation of the endpoint. Let $c_q$ be the corresponding cube-index map, $X_{1q}$ its seed, and
$$Y_q(C)=\texttt{Localization.Ysites}(G_q,m_{0q},c_q,X_{1q},C),\qquad
F_{q,\Gamma,C}(u)=\texttt{Localization.coef}(F_{q,\Gamma}(u,\cdot),C).\tag{39}$$
The coefficient is the landed iterated mixed-derivative integral, with the finite parameter order fixed by `Finset.univ.toList`. Define the new boundary coefficient **once**, by its final domain and exact decoration,
$$\boxed{\mathcal B'_X(S;u):=\sum_q\ \sum_{C:\,Y_q(C)=X} F_{q,S,C}(u).}\tag{40}$$
The inner sum is `Localization.I5Expansion.evTerm`; the outer finite sum fixes the resummation convention. The value at $S=\varnothing$ is zero if each physical difference is decoupled by an extension $F_{q,\varnothing}\equiv0$. This is a definite plan-B choice. P7 says to pre-localize and resum domains but does not specify this coefficient order or this convention for grouping old main-action, effective, generating and remainder pieces. Choosing (39)–(40) is admissible because P7 (3.26) uses only their exact aggregate, locality, covariance and bounds, and Roland's ruling permits a different large-field mechanism; those properties must nevertheless be proved for the *physical* extensions.

For the Lean interface choose one common finite cut cover refining the four source covers and put $F_S:=\sum_qF_{q,S}$ on it (extend each source function by ignoring cuts it does not use). Then (40) is equivalently `Localization.evTerm c G m₀ X₁ (F S) X u`; the equivalence follows by linearity of the mixed-derivative integral (`Fluctuation.LocalClassMRot.evTerm_sum_linear`) after the physical common-cover extension is proved. This is the **one definition** used below. The common-cover extension is mathematical data to construct from the actual four source terms, not an implicit assertion that they already share a landed type.

For a full removed family $\Gamma$, let $\Gamma_X$ be the members whose charged supports meet $X$. The essential cut-locality obligation is
$$F_{q,\Gamma}(u,s)=F_{q,\Gamma_X}(u,s)
\quad\text{for all }s\in\texttt{supportedOn}(C),\quad Y_q(C)=X.\tag{41}$$
It is stronger than the endpoint equality at $s=\mathbf1$. It follows in a physical application only after proving that the decoupled backgrounds and the old/new source summands read no removed member outside $X$ when the cuts outside $C$ vanish. `Localization.AbstractExpansion.coef_congr` turns (41) into $F_{q,\Gamma,C}=F_{q,\Gamma_X,C}$. The analogous agreement of the source data and localized histories on $X$ is exactly what `Localization.I5Expansion.localization_expansion` needs through `LocalityAEOn`, `Ag`, and `AgY`; `Def7.D7BdryPost.loc_hist` concerns the *old* $\mathcal B$ and does not itself establish (41) for the new residual.

## 4.2 What the landed localization theorem proves

Assume for each physical $F_{q,\Gamma}$ the hypotheses displayed in `Localization.I5Expansion.localization_expansion`: an analytic extension on $S\times\{|s_i|<e^{\kappa_1}\}$, the bound $\|F_{q,\Gamma}(u,s)\|\le E_q e^{-(\kappa-1)\Delta_q}$, `LocalityAEOn`, the `CovSetup`/connected-cover geometry, and the theorem's explicit inequalities on $\kappa_0,\kappa,\kappa_1,d,L$. The theorem then gives, with $T_q(X)=\texttt{treeLenCov}(G_q,m_{0q},X)$,
$$F_{q,\Gamma}(u,\mathbf1)=\sum_X\sum_{C:Y_q(C)=X}F_{q,\Gamma,C}(u),\qquad
\left|\sum_{C:Y_q(C)=X}F_{q,\Gamma,C}(u)\right|
\le E_qe^{-\kappa_0\Delta_q-2\kappa T_q(X)}.\tag{42}$$
It also proves analyticity and locality in the data on $X$. Summing the first equality over $q$, replacing each coefficient by its $\Gamma_X$ version using (41), and interchanging the two **finite** sums yields the required aggregate identity
$$\boxed{\sum_X\mathcal B'_X(\Gamma_X;u)=\Delta_\Gamma(u).}\tag{43}$$
There is no unspecified remainder in (43): expand the right side by (38), use each endpoint identity, then (42). If the finite sum in (40) is indexed by the same covariant source summands after a lattice symmetry, `Localization.DecEquivRelabel.coef_relabel` and `evTerm_relabel` transport each summand; relabel the finite $q$-sum to prove Euclidean covariance. These are actual landed transport mechanisms, but equivariance of the *physical* $F_{q,\Gamma}$ and the map of physical source summands still requires proof. Analyticity of (40) follows from `localization_expansion` term analyticity and finite addition. History locality follows from its `AgY` clause combined with (41) and the physical data/history agreement on $X$.

The estimate in (42) is **not yet the printed (H.7) estimate**. If a uniform source-summand estimate gives $\sum_q E_qe^{-\kappa_0\Delta_q}\le B_*$ and a geometric comparison gives $T_q(X)\ge a\,d_k^{\rm P5}(X\bmod(\Omega_k^c\cap Y_k))-b$ for all contributing $q$, then (42), by positivity and $e^{-2\kappa T_q(X)}\le e^{2\kappa b}e^{-2\kappa a d_k^{\rm P5}}$, gives
$$|\mathcal B'_X(S;u)|\le B_*e^{2\kappa b}e^{-2\kappa a d_k^{\rm P5}(X\bmod(\Omega_k^c\cap Y_k))}.\tag{44}$$
These are the exact constants; to keep an H7 coefficient $B_0$ and rate $\kappa_H$ one needs $B_*e^{2\kappa b}\le B_0$ and $2\kappa a\ge\kappa_H$. `Def7FineSize.lean` still marks the comparison between P5's printed continuous-tree size and the landed modular fine size `OPEN-PAPER-FINE-REALIZATION`; using one for the other without that comparison would change (H.7). Neither the uniform physical $B_*$ nor the full comparison is proved by `localization_expansion` alone. Thus (44) is a **proved implication**, not a verified physical H7 bound.

The endpoint (38) alone cannot justify (42) or (44): even with one cut parameter and residual $\Delta=0$, the analytic extension $F(s)=M(s-1)$ has $F(1)=0$ while its two localization coefficients have magnitudes $M$. The P3 analytic norm, locality and geometry hypotheses are indispensable. This also explains why defining $\mathcal B'$ merely by distributing the aggregate residual among domains would be a placeholder rather than the construction (40).

## 4.3 Consequences for R4b

The exact Lean implementation target is `r4FreshTerm := Localization.evTerm` applied to the **named physical** $F_{q,S}$, then `r4Fresh := \sum_q r4FreshTerm`. `localization_expansion` supplies (42); `coef_congr` and `evTerm_relabel` supply the decoration locality and covariance once their physical hypotheses are proved. The missing physical producer is a map of P7's four differences into the landed decoupled functionals and P6 expansions, with the endpoint, cut-locality, analytic norm, and history-agreement theorems. It cannot be replaced by an argument that `Rep.B` already has `loc_hist`: that is a theorem about the inherited coefficient, not the residual.

After (43), the operator gas must keep the output field fixed. `Operators/KerBound.lean:KerBound` and `R/RRemovedTau.lean:norm_integral_le_of_kerBound` integrate the removed output and therefore do not consume the front-free pointwise (3.10″) as stated; the actual consumer chain `RRemovedFinal.lf4R_removed` → `RRemovedFinalRgComp.lf4R_removed_of_flow` → `RRemovedFinalWit.lf4R_removed_of_flow_hist` must move to an operator-valued heavy weight, then use a decorated operator gas bound. The newly landed `Polymer.GasLinked*` abstract activation/footprint separation, when it arrives in W1007, does not identify P7's physical coefficient or provide the crossing reserve. The paid producer (34)–(37) still requires the physical linked expansion of the coefficient from (40), a bridge-incidence inequality, and unused-credit allocation; no implication from covariance-entry decay alone was established in Round 3.

**Confidence.** High in the deterministic formula (40) and the conditional proof (42)–(44), because they reduce exactly to landed localization declarations and finite-sum algebra. Low in the physical instantiation and printed H7 bound until the old/new source residual, its P3/P6 decoupling extension, the continuous-tree comparison and the history-locality bridge are proved.

## 4.4 Checked W1007 implementation and exact boundary

After W1001 landed, W1007 added `LargeField/R/RGasRepR4Fresh.lean:r4Fresh` as the **one** `evTerm` definition on a specified combined extension $F_S$. Its `r4Fresh_apply` unfolds (40); `r4Fresh_congr_cut` proves the decoration/locality implication (41) by `Localization.coef_congr`; `r4Fresh_aggregate_of_localization` invokes `Localization.localization_expansion` once and returns all four P3 conclusions—aggregate equality, data locality, the bound in (42), and analyticity. These are proved for an input satisfying P3's explicit analytic, cut-locality and geometry premises. The physical $F_S$ of the four P7 differences is not an input that `Rep` or `SFCtx` currently constructs, so this is not yet the physical aggregate identity (43), nor a proof of (44) on printed H7 size.

`LargeField/R/RGasRepR4Pointwise.lean:r4HeavyActivity_bound` proves $\|\mathbb T F(o)\|\le e^{-\kappa}$ from $\int^-_x\mathrm{absW}(o,x)\le e^{-\kappa}$ and $\|F(o,x)\|\le1$. `r4HeavyFamily` and `r4HeavyFamily_bound` sum the activities of finitely many histories on possibly different internal carriers, still at the **same** output $o$. This is the part of the new operator activity that does not need a scalar output integral. A full decorated polymer activity bound needs a support/dependence and entropy theorem for `gasR4DecorOp_eq`, plus the physical normalized H-op measure and the physical coefficient identification. The user-approved replacement of `lf4R_removed` therefore remains open; no old proof was copied or changed.
