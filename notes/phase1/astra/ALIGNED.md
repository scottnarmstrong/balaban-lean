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
