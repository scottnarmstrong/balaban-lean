# True $Y$-locality: decision and remaining proof

**12 October 2026.** This is the follow-up to `Y-LOCAL.md`. The decision is the source's **Route 1(c)**: use the fixed-$Y$ generating set of P3 (4.44)–(4.47), and prove a narrower physical locality theorem before assigning the label $Y$. The universal strengthening of the *landed* `i5_functional_hat` is false. A physical strengthening may still hold, but it has not been proved. No collar estimate or fiber count from Route 2 is asserted. In particular, the requested complete class-preserving theorem is **OPEN**; the exact missing statements are below. Here “PROVED” means the displayed argument establishes the claim from definitions, “PROVED CONDITIONAL ON” names its premise, and “OPEN” names an unproved assertion. This note makes no Lean-completion claim.

## 1. What the landed coefficient can read

Put $K=k+1$, $\ell=L^K$, $b=L^{K+m_1}$, and $a=L^{K+m_0+m_1}=L^{m_0}b$. Let $Y_1(C)=\operatorname{compY}(q,X_1,C)$ and $Y(C)=\operatorname{Ysites}(G_p,m_0,q,X_1,C)$. The definitions are `Localization/PolymerGeometry.lean:421,426`; $X_1\subset Y_1(C)\subset Y(C)$ follows from `subset_compY` and `patchUnion_subset_Ysites`. In the physical step `IsLevel Gp K` and `IsLevel Hm k` are hypotheses of `Fluctuation/HatEngineLocalFan.lean:50` and `HatEngineLocalEngine.lean:135`.

**PROVED (old support margin, under the full-level hypothesis).** If $j<K$, the top layer is the whole torus, $L\ge3$, and $X\subset\bigcup_{q\in\mathcal K_X}Q_q$ as in `CovSetup.chosen`, then

\[
\operatorname{psiThick}(X)\subset X_1.
\tag{1}
\]

Here $Q_q$ is the chosen old $\pi'_j$-cube, whose side is at most $a$. In each coordinate its interval $I$ meets at most two aligned $a$-cells. The leftmost and rightmost aligned $La$-intervals containing $I$ together extend at least $a$ sites past both ends of $I$ when $L\ge3$: if $I$ lies in one $a$-cell there are $L$ placements, and if it meets two cells there are at least $L-1$ placements. Choose these placements independently in all coordinates. Every resulting product cube contains $Q_q$, belongs to `Q0` because the top layer is the whole torus, and their union contains $Q_q$ and its nearest neighbours. This is the needed one-site consequence of the $(L-1)a$ freedom in the choice of a containing cube. On a finite torus the argument uses periodic aligned cells, so a face at the coordinate origin is treated in the same way. The same interval argument covers a coordinate collar of width at most $a$ around the old cube. It does **not** say that `psiThick X1` lies in $X_1$.

**PROVED (unit blocks do not straddle $Y_1$ or $Y$).** `Pset m₁` at level $K$ is a cell of side $b$; `X1` and `Dsites` are unions of aligned cells of side $a$, with $b\mid a$ and $\ell\mid b$. `IsLevel Gp K` makes all marked parameter cubes top-level. A nearest-neighbour component of a union of complete $b$-cells is again a union of complete $b$-cells: each cell is connected, so it cannot meet two components. Hence $Y_1(C)$ is a union of complete $b$-cells, and $Y(C)$ is a union of complete $a$-cells. Each $K$-unit block of side $\ell$ is therefore either wholly in or wholly out of either set. This is the cell argument behind `PolymerGeometry.cell_subset_cube`; it does not identify `blockThick Y` with $Y$, because the *neighbour* set in `blockThick` includes outside blocks.

**PROVED (what decoupling cuts).** `Localization/Decoupled.lean:81–93` and `Decoupled2Solve.lean:46` define

\[
G_s=G_s^*(1-\mathcal K_s)^{-1},\qquad
G_s^*=\sum_z s_z\chi_zG^{(z)}c_z,\qquad
\mathcal K_s=\sum_zs_zK_zG^{(z)}c_z,
\quad s_z=\prod_{P\in\mathcal Q(z)}s_P.
\tag{2}
\]

If a parameter cube $P\in\mathcal Q(z)$ is cut by $s_P=0$, both summands for $z$ vanish. An active centre whose thick box meets $Y_1(C)$ has its thick box inside that component: `DecoupledFieldLocal.hhat_aux`, `hdich_aux` and their `Decoupled2FieldLocal` versions prove the incidence and component dichotomy. `Decoupled2Geometry.dg5_local` and `DecoupledGeometry.dg5_local` then compare the Green operators separately on the component. The matrix formed from the **active** cube terms is block diagonal across this component. This does not make every *input source* local: it multiplies the source produced before the cut.

**PROVED (the exact exterior-input mechanism).** For the background, `Background/ApproxLocal.lean:47–60` forms `approxField Gp` by normalized interpolation of `locSol Gp` at all active block bases. `DecoupledBackgroundLocal.approxDep` contains those bases. `Background/ApproxResidual.lean:33` then forms

\[
f_0=S_{G_p}(D)-H_{G_p}(0)\phi_0,
\qquad
\phi_s=\phi_0+G_s(\alpha_s)(f_0-\alpha_s\phi_0).
\tag{3}
\]

The second equality is exactly `Localization/DecoupledBackground.IsDecBg.field`. Neither `approxField` nor `residual` depends on $s$. `resDep x` is the union of `approxDep y` over $y=x$, the block of $x$, and the neighbours of $x$ (`DecoupledBackgroundLocal.lean:36–53`). `I5FluctLocal.fan_local_fl` consequently asks for raw agreement on `thickSet Y1`; the landed `i5_fluct` asks for it on `thickSet Y`. This is a real input in those theorems, not a conclusion of `dg5_local`.

For the fluctuation, `I5FluctData.flEdat` gives $(\bar\phi,\alpha,\psi',0)$. `Background/Contraction.pertSource` is $Q^*a\psi'+\mathfrak b_{H_m}(\psi')$. The latter samples a neighbour **only if it lies in `collar Hm`**, by `Background/Data.boundaryTerm` (`Data.lean:141`). In the physical single-level step `IsLevel Hm k` gives $\Omega_1(H_m)=\mathbb T$, so `collar Hm` is empty and $\mathfrak b_{H_m}=0$. Thus the nearest-neighbour condition on $\psi'$ in `I5FluctStep.DataAgreeS.psi_collar` is redundant for this *physical* full-level pair. It remains necessary for the general landed theorem with a non-full $H_m$. The direct term of `flDatum` reads $\psi'$ on `dataSites Gk`, which `BgSetting.dsX₀` places in $X_0\subset X_1$. The square root at a $K$-unit point uses other unit points in its same unit block and the active component; `DecoupledCovLocal2Free.I4c_local_sqrt3` and `HatEngineLocal.hatPsiF_local` implement this comparison. Since whole unit blocks divide $Y_1$, a value sought *inside* $Y_1$ does not require a hat variable from a block straddling its boundary. The existing `blockThick` hypothesis also covers values at neighbours outside $Y_1$, which the general `fan_local_fl` asks for.

## 2. The universal landed strengthening is false

**PROVED counterexample to the universal assertion.** Consider a large periodic torus, a whole-lattice top-level generating set $G_p$, $N\ge2$, $\nu=0$, and a single chosen old $\pi'_j$-cube, $j=K-1$, lying in the aligned $a$-cell at the origin. Its `Q0` cubes have union $X_1$ with an outer aligned face. Choose a lattice site $x$ on that face, within $X_1$, and the adjacent top-level block base $q$ just outside $X_1$. The periodized quadratic spline `Background/BSpline.bsp` has positive value at the normalized displacement of $x$ from the centre of $q$: in the face coordinate it is $t=(\ell+1)/(2\ell)\in(1/2,1]$, and there the spline is $(3/2-t)^2/2>0$; choose the other coordinates at block centres. The torus is large enough that no other period contributes. Thus `Background/Weights.weight (K,q) x>0` and $q\in\operatorname{approxDep}_{G_p}(x)\setminus X_1$. Take all $\Psi$-vectors initially $e_1$, and change only $\Psi(q)$ to $e_1+t e_2$ for small complex $t$. At $\nu=0$, `cMinimizer` is the normalized input (its explicit formula is `Background/ConstantConfig.lean:31–32`). The derivative at $t=0$ of the $e_2$-component of `approxField Gp … x` is the strictly positive normalized weight of $q$. Hence $\phi_0(x)$ genuinely changes although the two raw data agree on $X_1$. Small $t$ stays in the open complex domain around this regular configuration.

Set every parameter cube outside $X_1$ to zero and leave those contained in $X_1$ at one. If a centre $z$ has $x\in\operatorname{coreBox}z$, its `hatBox z` extends past the outer face by more than one top-level parameter cell (`DecoupledGeometry.coreBox`, `hatBox`, `Cover.hatRad`). It therefore meets a parameter cube outside $X_1$, which belongs to `Qset Gp z`; its factor in $s_z$ is zero. Thus $x\notin\operatorname{Core}(s)$, and `DecoupledBackgroundLocal.i4b_vanish` gives $\phi_s(x)=\phi_0(x)$. Choose the generic analytic functional $\Phi(\phi,\ldots)=\phi(x,e_2)$, scaled by a fixed small constant. It satisfies the locality premise of `i5_functional_hat` with $Z=\{x\}\subset X_1$; `BlockMargin` is vacuous with $Z_\alpha=\varnothing$. The empty-family coefficient is $F_\varnothing=F(s=0)=\phi_0(x,e_2)$, and its fixed label is $Y(\varnothing)=X_1$. It is **not** determined by the raw data on $Y(\varnothing)$. No restatement of the generic `fan_local_fl`, `i5_fluct` or `i5_functional_hat` with agreement only on $Y$ can be true under their present functional-support hypotheses.

The counterexample chooses a functional at the *outer face of $X_1$*. The physical potential, old energy, source and observable terms start on the old support and have the separate `BgSetting.hN`/`dep` margins. The example therefore does **not** disprove sharp locality for those physical terms. It proves that their additional margins must enter a new theorem; deleting the collar hypotheses from the current generic theorem is invalid.

## 3. The narrower physical lemma and P3's construction

The following is the precise promising no-collar mechanism, with its current status. Define $S_Y$ as `DecoupledFieldLocal.SY`: the union of `intBox z` over eligible centres whose `hatBox z` lies in $Y_1$. Define $R_Y$ to be $S_Y$ together with the rows of `dirichletOperator` at sites of $S_Y$. A source comparison needs $\phi_0$ and $f_0$ on $S_Y$, and $\phi_0$ on $R_Y$; this is visible in `DecoupledFieldLocal.local_step:519–560`. It does not need them on arbitrary sites of $Y_1$. In the full-level case, if $x\in\operatorname{intBox}z$, every site in `resDep Gp x` is at coordinate distance at most a top-block step plus an active-block step plus one neighbour step from $x$. The margin from `intBox z` to `hatBox z` is $3L^2\ell$, by `Cover.hatRad:705`. The same bound covers `approxDep` of the row sites in $R_Y$, since a row changes a site by a top block or a nearest-neighbour step. Consequently these dependency sets lie in `hatBox z`, hence in $Y_1$, **provided** the coordinate bounds are established for the periodic aligned cube and every row type of the mixed operator. `Background/Weights.active_dist` and `Localization/Cover.cube_active_dist` supply parts of that bound, but the required combined inclusion has no landed declaration. Name it **OPEN-FOOTPRINT-MARGIN**:

\[
\bigcup_{x\in S_Y}\operatorname{resDep}_{G_p}(x)
 \ \cup\!\bigcup_{y\in R_Y}\operatorname{approxDep}_{G_p}(y)
 \ \subset Y_1,
\tag{4}
\]

with the corresponding $H_m$ row and unit-block inclusions. The displayed coordinate argument explains why (4) is plausible; it is **not** a proof for all mixed-layer rows, and (4) is marked OPEN. Under (4), one can rerun `DecoupledFieldLocal.local_step` with agreement on $S_Y,R_Y$ instead of all of $Y_1$. `dg5'_inner` compares the decoupled correction on the component; `Nexp_congr` needs the row data only on $R_Y$. Picard iteration and uniqueness then compare $\alpha_s$ on $S_Y$ and $\delta\phi_s$ in $Y_1$. To recover $\phi_s$ on the physical output set $Z\subset X_0$, use `BgSetting.hN` to put `approxDep Z` in $X_1\subset Y_1$; at sites outside the active core `i4b_vanish` leaves only this local approximate field. For the fluctuation, `collar Hm=\varnothing` removes `psi_collar`; repeat the `Dec2.i4a_local_fpS` proof with source agreement on its eligible interaction cubes, and use the whole-unit-block property to compare `hatPsiF` on $Y_1$. This parallel theorem is **OPEN-PHYSICAL-FOOTPRINT-LOCAL**, conditional on (4) and on the exact physical supports being within the `BgSetting.hN` margin. No current landed theorem has this conclusion.

P3, printed pp. 78–79, checked directly in PDF `BF02506385.pdf` pages 46–47, takes a further step before the Cauchy estimate. For fixed $Y$, it sets $\Omega'_{k+1}=Y\cap\Omega_{k+1}$, enlarges successively the lower-layer intersections $Y\cap\Omega_n\cap\Omega_{n+1}^{c}$ by the prescribed $M_1L^n$-cube boundary layers of P3 (4.4)–(4.6), and calls the resulting generating set $\mathcal B_{k+1}(Y)$. It replaces the original generating set *inside each pre-resummation term* with this one; outside $Y_1$ the corresponding decoupling parameters are set to zero, while inside $Y_1$ they agree. Formula (4.45) then sums the terms with the same $Y$. This order matters: P3 (4.46) is the complex domain of the local generating set, not an automatic restriction of the global `XiCRaw` domain.

Here is the minimal changed definition for the present construction. For each admissible $Y$, construct $G_p[Y]$ by that P3 layer rule and an analytic restriction/extension chart $\iota_Y$ from its complex data domain. For $C$ with $Y(C)=Y$, let

\[
F_C^{Y}(D,\hat\psi)
  :=\operatorname{Coeff}_{C}\!\left[
     \Phi_X\bigl(G_p[Y],\,D|_{G_p[Y]},\,
       \operatorname{Ext}_{Y_1(C)}s,\,\hat\psi|_{\operatorname{blocksOf}Y}\bigr)
     \right],\qquad
E_Y^{\rm paper}=\sum_{C:Y(C)=Y}F_C^{Y}.
\tag{5}
\]

Here $\operatorname{Coeff}_C$ is the finite marked coefficient $\prod_{i\in C}\int_0^1\partial_{s_i}\,dt_i$ with all unmarked variables zero, as in `I5Expansion.coef`. `Ext` is one on parameter cubes contained in the old $X_1$, the marked variables on $C$, and zero on all other parameter cubes meeting the complement of $Y_1(C)$; the local generator's own cover determines the products $s_z$. This definition changes the *generating set used to build `approxField`, `residual`, `flEdat`, the two decoupled Green operators and `decCovSqrt`*. Merely restricting the final value of a global $F_C$ to fields on $Y$ leaves the read in (3) intact. For arbitrary $\Phi$ from §2, (5) need not equal the original global $F_C$; the replacement identity is asserted only for physical terms with the old-support margin.

**OPEN-PAPER-REPLACEMENT.** For each of the physical (V,E,F,M) summands, prove $F_C^{Y}=F_C$ on the common global/local data domain, with the same mark coefficient and the same bound, whenever $Y(C)=Y$. Prove that $\iota_Y$ contains a common open neighbourhood of the strict Cauchy circles and maps it to the global `XiCRaw` and hat domains. This is the precise `OPEN-PAPER-DOMAIN` of `Y-LOCAL.md` in the fixed-$Y$ construction. P3 pp. 78–79 states the replacement and (4.46) for its background function (4.32); it is source evidence, not a landed theorem for the present hatted physical functional. P3 permits the simple sufficient condition $\kappa_1\ge2$ following (4.47); the PDF was checked directly because its OCR is unreliable.

The following existing proofs would need parallel, narrower versions (the old declarations stay valid): `DecoupledFieldLocal.local_step`, `i4a_local`; `DecoupledBackgroundLocal.i4b_local`; `Decoupled2FieldLocal.local_step_fpS`, `i4a_local_fpS`; `DecoupledCovLocal2Free.I4c_local_sqrt3`; `HatEngineLocal.hatSqrtF_local`, `hatPsiF_local`; `I5FluctLocal.fan_local_fl`; `HatEngineLocalFan.fanH_local`; `HatEngineLocalEngine.i5_functional_hat`; `I5Expansion.localization_expansion`; and the four physical components in `InteractionHatV`, `InteractionHatE`, `InteractionHatF`, `InteractionHatNu` plus `InteractionHatAssemble.interaction_expansion_hat`. The first group handles (4), the middle group handles the square root and fixed-$Y$ chart, and the last group identifies the actual physical summands. No one of these changes follows from monotonicity of the existing `AgHat` relation.

## 4. What closes immediately once Route 1 is proved

**PROVED CONDITIONAL ON `OPEN-PHYSICAL-FOOTPRINT-LOCAL` and `OPEN-PAPER-REPLACEMENT`.** The label can be $Y$ itself. `TreeLengthCov.gm2` then gives, for $x=d_j^{\rm cov}(X)$ and $D=d(2L+1)^d$,

\[
T(Y)\le L^{-1}x+D|C|.
\tag{6}
\]

The termwise coefficient bound with mark radius $e^{\kappa_{\rm AE}}$ and `I5Expansion.gm3_fam` count *exactly the same fibers* $C\mapsto Y(C)$; no new `GM2#` or `GM3#` is needed. The landed assumptions $4D\kappa_{\rm dec}\le\kappa_{\rm AE}$, $1\le(\kappa_{\rm AE}/2-1)/2$, and `hlog` make the mark sum at most one. The old-length allocation is

\[
\kappa_0+2\kappa_{\rm dec}/L\le\kappa_{\rm dec}-1.
\tag{7}
\]

At $L=3$, (7) is precisely $3\kappa_0+3\le\kappa_{\rm dec}$, the landed `hκdec`. The physical assembly already has a term bound with rate $a=2\kappa_{\rm dec}-1$ on $T(Y)$ (`InteractionHatAssemble.interaction_expansion_hat_bound`). Thus a sharp $Y$-dependent `PaperHatTerms` has rate $\kappa_H=2\kappa_{\rm dec}-1$. Its finite labels are the identity labels `HatLabelsAct.thickLabels 𝒴` with $\mathcal Y=\operatorname{polymerDomains}$; `HatLabelsAct.entropy_thick` gives (G2). A fixed $Y$ has one label, so the fiber factor in `HatLabelsAct.card_fiber_thick` is one and the geometric conversion `hatA=1+2^d c_1c_G` is absent. `LabelAct.dep` must be proved from sharp agreement on `blocksOf Y`; this is exactly the still-open physical locality theorem, not a consequence of the landed `AgHatF` relation.

The exact target interface is: $\mathcal Y$ finite with every $Y\in\mathcal Y$ an `IsDj` domain; analytic physical terms $T_Y(\Theta,\hat\psi,\sigma)$ on the local P3 open domain and source disk; the identity $\sum_YT_Y=\operatorname{interaction\_expansion\_hat}$ at the physical point; a bound $\|T_Y\|\le\varepsilon_Ue^{-(2\kappa_{\rm dec}-1)T(Y)}$; and factorization through raw data on $Y$ and hat variables on `blocksOf Y`. The direct constructor `labelAct_of_paperHatTerms` takes the label $Y$ itself, the preceding factorization for `LabelAct.dep`, `entropy_thick` for its entropy field, and the displayed bound for its norm field. This constructor and its required physical input are **OPEN** as Lean declarations. The abstract construction of `CubeLabels` and entropy field is **PROVED CONDITIONAL ON** `thickLabels` and `entropy_thick` and the landed `IsDj` hypothesis.

**PROVED arithmetic, CONDITIONAL ON the target interface.** At $d=L=3$, let $c_1=c_1(3,3)=3375$, choose $\kappa_0\ge a_{\rm Ent}(3,3)+1$, and put

\[
\kappa_{\rm dec}=100(\kappa_0+c_1+10),\quad
\kappa_{\rm in}=\kappa_{\rm dec},\quad
\kappa_H=2\kappa_{\rm dec}-1,\quad
\kappa'=\tfrac32\kappa_{\rm dec}+\kappa_0+1,\quad
\kappa_{\rm out}=\tfrac32\kappa_{\rm dec}.
\tag{8}
\]

Then (7) holds; $\kappa_{\rm dec}-1\le\kappa_{\rm in}\le\kappa_{\rm out}$; and `StepActivityBound.hκ` becomes $\kappa_{\rm dec}/2\ge4\kappa_0+c_1+7/2$, true by (8). Also $\kappa_{\rm out}=\min(\kappa_H,\kappa')-\kappa_0-1$, the `Thm31b` rate. Choose $\kappa_{\rm AE}$ after these constants large enough for `hκ`, `h1`, and `hlog`. Then choose $m_1$ large enough for `hM`, `hM2`, and `hMX`, in particular $c\exp(N_0\kappa_{\rm AE})\le L^{m_1}$; after that choose strict analytic radii and the physical prefactor within `StepActivityBound.hε`. The landed hypotheses permit $L=3$; `StepRates.stepRates_trace_witness` is a witness for the old halo conversion, not for this direct-label construction. Equation (8) is an arithmetic witness for the displayed rate inequalities and does not use an $L\to\infty$ limit. By contrast `StepRates.stepRates_no_closure_landed` proves that the current `hatKappaH=(2\kappa_{\rm dec}-1)/\operatorname{hatA}-c_1` cannot close the class rate. Thus direct labels, rather than a larger $L$, are the necessary change in the label conversion.

## 5. Bounded Lean work packages

Each package is intended to be roughly 300 lines and adds parallel declarations rather than weakening a landed theorem.

1. **Geometry and counterexample, ~300 lines. OPEN Lean work; mathematical (1) and whole-block argument PROVED.** Parallel to `TreeLengthCov.Q0`, `PolymerGeometry.Pset`, `HatEngineLocal.blockThick`: prove `psiThick X ⊂ X1` under `IsLevel Gp K`, cell divisibility, and the boundary example of §2. State the old-support margin separately from a generic $Z\subset X_1$.
2. **Active footprint, ~300 lines. OPEN-FOOTPRINT-MARGIN.** Parallel to `DecoupledFieldLocal.SY`, `Background/Weights.active_dist`, `Cover.hatRad`: define $R_Y$, prove (4) with periodic coordinates, mixed operator rows, $H_m$ rows and unit blocks. Make the `IsLevel` hypotheses explicit.
3. **Sharp background and fluctuation, two files of ~300 lines each. OPEN-PHYSICAL-FOOTPRINT-LOCAL.** Parallel to `local_step`, `i4b_local`, `Dec2.local_step_fpS`, `fan_local_fl`: replace agreement on all $Y_1$ by agreement at eligible interaction cubes and row footprints; compare the physical output set with `BgSetting.hN`. Prove `collar Hm=∅` and remove only that source condition. Retain the original generic theorems.
4. **Square root and hat blocks, ~300 lines. OPEN-PHYSICAL-FOOTPRINT-LOCAL.** Parallel to `I4c_local_sqrt3`, `hatSqrtF_local`, `hatPsiF_local`: compare unit blocks wholly in $Y_1$ and prove output agreement at the sites the physical functional reads. Do not assert equality at `psiThick Y1`.
5. **Fixed-$Y$ analytic chart, two files of ~300 lines each. OPEN-PAPER-REPLACEMENT.** Define $G_p[Y]$, its cover, restriction and extension charts, and $F_C^Y$ in (5). Prove the replacement identity for the four physical summands, the strict complex-domain inclusions and open Cauchy circles. Parallel `I5Expansion.localization_expansion` rather than reusing its global-domain conclusion as a local chart.
6. **Direct labels and rates, ~300 lines. PROVED CONDITIONAL ON packages 2–5.** Construct `PaperHatTerms`, the identity `CubeLabels`, `LabelAct.dep`, the $2\kappa_{\rm dec}-1$ bound, and the arithmetic (8). Parallel `HatLabelsTerms.labelAct_of_hatTerms`; invoke `HatLabelsAct.entropy_thick`, `TreeLengthCov.gm2`, `I5Expansion.gm3_fam`, then the existing Mayer and RG input interfaces.

## 6. Five-line closure status

1. **PROVED:** The full-level old support has a one-site $X_1$ margin; unit blocks do not straddle $Y_1$ or $Y$; the active decoupled Green operator cuts across components.
2. **PROVED:** The generic landed functional has a genuine outside-$Y$ read through `approxField`; its empty-family coefficient provides a counterexample to universal sharp locality.
3. **OPEN:** The *physical* sharp locality and exact fixed-$Y$ replacement, named `OPEN-PHYSICAL-FOOTPRINT-LOCAL` and `OPEN-PAPER-REPLACEMENT`, including the local open complex chart.
4. **PROVED CONDITIONAL ON line 3:** Direct labels use landed `gm2`/`gm3_fam` and give $\kappa_H=2\kappa_{\rm dec}-1$; the numerical class-preserving chain (8) satisfies the rate inequalities at $L=3$.
5. **OPEN:** The small-field step's rate induction is not closed mathematically. The single composite statement needed for this route is `OPEN-PAPER-HAT-LOCAL`: the physical hatted expansion factors through the fixed-$Y$ chart with the exact identity, complex bound, and `blocksOf Y` dependence; packages 2–5 are its proof obligations.
