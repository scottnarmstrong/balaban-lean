# LFROOT3: P6 active reads and the inherited-hole residual

**Verdict (2026-10-13).** **REFUTED** as an unqualified output-label claim: a nonzero zero-mark
H7-class term can be assigned remote active cover cells by completing an inherited hole.
**OPEN** for physical O(N) coefficients: landed row/incidence lemmas do not identify the full
P6 scalar and mixed covariance square root with their hypotheses. Rooted interpolation
dependence alone does not pay the assigned *modular size*.

**Sources and notation.** P6 `sources/s002200050470.pdf`, p. 34, (4.32)–(4.34);
P3 `sources/BF02506385.pdf`, pp. 77–81, (4.41)–(4.50); P5 `sources/s002200050433 (1).pdf`, pp. 496–97, (1.33)–(1.39);
Dimock D2 `sources/Dimock-II-arXiv-1212.5562.pdf`, Lemma 3.17, pp. 65–68, (476)–(489).
Put $K=k+1$, $A_X=X\cap\Omega_K$, $H^-=\texttt{p6OldC}$,
$H^\partial=\texttt{p6BoundaryC}$, $F^\sharp=\texttt{p6FsharpC}$, and $C=\texttt{coverOf}\,F^\sharp$.
$X_1$ is P3's uncut fine core, $\mathcal C$ its **marked interpolation patches**,
$Y_1(J)$ the interpolation/incidence component, and $Y(J)$ the assigned modular output label.
The current large-field $P_K,Q_K,R_K,S_K$ cubes are different seeds; $\mathcal C$ and those families can vary independently.

## Q1. What the coefficient reads

**PROVED (source scalar).** For one inherited term P6 (4.32), write
$F_X(s)=uB^{(k)}(X,\mathbb A_k;q_s,\psi'_{\mathbb A_k},g;h)$, where
$q_s(y)=q_{\mathbb A_k}(y)$ on $X\cap\Omega_K^c$ and
$q_s(y)=\psi^{(k)}_{\rm loc,s}(\theta)(y)+\beta_k^{-1/2}
(C^{(k)1/2}_{\rm loc,s}\widehat\psi)(y)$ on $A_X$.
The old exterior spins and $\psi'_{\mathbb A_k}$ on $X$, and $h,g$ on $X$, are spectator
data; only the displayed active output rows vary with $s$. P6 explicitly first localizes in
$A_X$, then allows several $Y_1$ components, each meeting a component of $A_X$ (p. 34).
P3 (4.41) marks cover patches outside $X_1$; (4.42) forms $Y_1$ from $X_1$ and marks;
(4.44) enlarges it to $Y$. These are not the same sets.

**PROVED (landed sufficient row envelope; physical identification OPEN).** For a component
$Y_1(J)$, `Localization/RowsBg.lean:RowSite` takes $B_b=SY(H^\partial,X_1,\mathcal C,Y_1)$;
background data are $\alpha,\delta\Psi,f_1$ on $B_b$, $\phi_0$ on the Dirichlet row sites
`RowSite(B_b)`, and $\delta\Psi$ on adjacent collar sites. `TwoTorusDecBg.lean:decBg_rows_transport`
and `FootprintMargin.lean:footprint_subset_component` further pull the physical residual to
$\bigcup_{x\in B_b}\operatorname{resDep}(x)$ and the approximate field to
$\bigcup_{x\in B_b,u\in\operatorname{resSites}(x)}\operatorname{approxDep}(u)$;
these footprints lie in $Y_1$ under the stated generator hypotheses.
For $H^-$, `Localization/RowsFl.lean:RowF` uses $B_f=SYF(C,H^-,X_1,\mathcal C,Y_1)$,
the potential, perturbation and source on $B_f$, $\phi_0$ on `RowF(B_f)`, and an adjacent collar input
(empty for a full-level generator). `TwoTorusDecSol.lean` transports those rows.
These are row-comparison hypotheses, not a proof that the physical P6 data satisfy them.

**PROVED (square-root row theorem; mixed physical bridge OPEN).** `Localization/RowsCov.lean`
uses $B_c=SY(H^-,X_1,\mathcal C,Y_1)$, multiplier $\alpha$ on $B_c$, background $\phi$ on
`rowsCov_R(B_c)`, and $\widehat\psi$ on `UnitOut(Y_1) ∪ UnitIn(B_c)`; `CompleteBlocks`
reduces the last union to `UnitOut(Y_1)`. `I4c_local_sqrt2_rows` obtains equality for *every*
Stieltjes resolvent parameter $x\ge0$ before integrating to $C^{1/2}$.
`DecoupledCovLocal2.lean`, `TwoTorusLift.lean`, and `TwoTorusDet.lean` supply conditional
transports, but none composes this square root with the actual $H^\partial/H^-$ P6 background
and identifies its selectors and input field.
`PairedReadLocality.lean:paired_locality_on` and `paired_coef_eq_zero_of_not_connected_on`
restrict the *paired raw* functional to a chosen read set $R$ when both `composeDep` sets lie
in the joint incidence closure; its header explicitly excludes the P6 scalar and square root.

**ANSWER (containment).** The scalar's *direct* spin/source arguments lie on $X\cup A_X$.
The operator read envelope is in reached $Y_1(J)$ (plus named collars/blocks), which can
extend by arbitrarily many marks. No fixed-radius inclusion
`Read(F_X,J) ⊆ Ω_K ∪ nbhd_r(X)` follows for all $J$ from these lemmas.
At $J=\varnothing$, free eligible centres have footprints inside $X_1$
(`P6PairChain.lean:paramFree_foot_subset`); a bounded active core would localize that branch,
but P6's exact $X_1$, physical selector, and active-region cast are still open.

## Q2. Rooting, and the zero-mark test

**PROVED (conditional geometry).** `P6PairParamDegree.lean:p6_jointParams_rooted_sharp` says
every *reached* marked patch is rooted, in the footprint graph `paramGraph F♯` (Moore touch
**or common centre footprint**), at a seed $U\supseteq X_1$. `P6PairChain.lean` proves a free
centre's footprint lies in $X_1$. Thus, if $X_1$ is a bounded lift of $A_X$ and the physical
coefficient depends only on the joint closure seeded at its actual active output rows, a
remote dependence outside that core needs a path of interpolation marks. The corresponding
coefficient-to-reached premise, active $X_1$, and mixed square-root locality are **OPEN**.
The theorem neither makes a mark a *new large-field seed* nor prices $Y$.

**REFUTED (output-label version, explicit H7-class family).** Use the two-step aligned-rectangle
history of `VMOD-36.md` §2: an old hole $H_n$ has length $nL$, its step-$K$ inherited
enlargement is one long component, all current $P_K,Q_K,R_K,S_K$ are empty, and the enlarged
hole's long face cuts the target $\pi'_K$ grid. An old modular label $X_n$ contains all $H_n$
and only a bounded active chain near one end; both $d_k^{P5}(X_n)$ and landed $D_-(X_n)$ are $O(1)$,
and $X_n$ crosses the old boundary. Choose one nonzero, real spin-invariant constant
$B^{(k)}(X_n)=\varepsilon_n$ with $0<\varepsilon_n<B_0e^{-\kappa d_k^{P5}(X_n)}$; set other old coefficients to zero.
It satisfies P5 (1.38)–(1.39), locality, analyticity and symmetry. Since it is independent
of the interpolation fields, every derivative in P3 (4.41) vanishes: **only $J=\varnothing$
survives**, with coefficient $\varepsilon_n$. P6 p. 34 requires its output $Y$ to contain $X_n$
and belong to $\mathcal D_K(\mathrm{mod}\,\Omega_K^c)$, so it contains the whole new hole.
Target cover boxes crossing the misaligned long face force $\Omega(n)$ active cells,
including cells near the far end. `SizeModG1.lean:G1_cellCount` gives
$D_+(Y)\ge c n-O(1)$; P5 (1.34) likewise needs a length-$\Omega(n)$ tree. This disproves the blanket inference
"nonzero assigned far-active label implies a marked connecting path" and any uniform
uncharged $D_+(Y)\le L^{-1}D_-(X)+C|\mathcal C|+O(1)$ for this assignment.
Here the far active cells are **label spill**, not physical reads; Dimock D2 (485)'s no-new-active-cells identity fails for this straddling assignment.
`VMOD-36` proves the rectangle geometry at math level; a source-to-fine identification of
the *physical O(N) generated* boundary coefficients remains OPEN. This example refutes an
H7-class-uniform argument, not the existence of a better physical assignment or cancellation.

**OPEN (physical dependence).** No nonzero coefficient has been exhibited whose actual background or $C_{\rm loc}^{1/2}$
dependence traverses the retained hole without a mark; nor has one been ruled out. P6's sentence about $Y_1$ and landed incidence cannot settle it.

## Q3. Exact obligation and payment

**PROVED necessary residual, OPEN producer.** For each nonzero assignment set $b_{\rm ret}(X,J,Y):=[D_+(Y)-L^{-1}D_-(X)-C_{d,L}|J|]_+$.
The exact replacement for OPEN-3 is: with the physical $X_1$ and both fields identified,
either prove $b_{\rm ret}=0$ for every nonzero assigned $(X,J,Y)$, or prove the coefficient
bound has an **additional** factor $e^{-\tau b_{\rm ret}}$ at the output rate $\tau$,
alongside the old-size and mark factors. The rectangle family forces
$b_{\rm ret}=\Omega(n)$ for whole-hole completion with $J=\varnothing$; for its constant
H7-class coefficient there is no derivative factor to supply that decay.
P5 (1.34) and landed `dcovModE` charge full bridge length; G1/G2/G3 and `SizeModExtend`
are geometry/entropy under their hypotheses, not coefficient gains (`VMOD-40`–`42`).
P6 (4.34) is a coefficient bound before the distinct operator factor (3.9); P3 (4.48)
uses a *nonmodular* source tree visiting all source boxes. Neither supplies this residual.

**Bounded leaves.** (1) Identify P6's physical $X_1$, active rows, selectors, and spectator
agreement in `paired_locality_on` (background/fluctuation); (2) prove the mixed
$H^\partial/H^-$ `RowsCov` square-root read/closure transport at every Stieltjes parameter;
(3) apply `paired_coef_eq_zero_of_not_connected_on` and `p6_jointParams_rooted_sharp`
to nonzero physical coefficients; (4) prove the *actual* modular assignment/fine-size
inequality including straddling $\pi'_K$ boxes, or a physical $e^{-\tau b_{\rm ret}}$ estimate;
(5) separately compare P5's continuous size with `d7Size*` (`OPEN-PAPER-FINE-REALIZATION`).
Leaves 1–3 establish analytic rooting only; leaf 4 is indispensable for blocker 3.
