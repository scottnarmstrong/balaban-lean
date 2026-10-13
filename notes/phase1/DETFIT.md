# DETFIT — determinant and energy terms against the small-field class

This is a clause audit for the actual rooted determinant family, not a claim that the physical output class has been constructed. `PROVED` refers to the cited landed Lean statement or the displayed finite-sum argument; `PROVED CONDITIONAL ON` names an additional premise; `OPEN` names a missing physical theorem; `REFUTED` rejects the indicated
inference. Lean paths below are relative to `/home/scott/Balaban/Balaban/` and are read-only.

## 1. The class target and the size of an energy term

`SmallField/Def6.lean:Consts` has a single nonnegative bound constant $P.E_0$ (`Consts.Admissible.E₀_nonneg`), fixed across scales; `IsSF.boundE` and `SmallField/Def6v2.lean:SFTermClauses.boundE` demand $\|E_j(y,X;\Psi,h)\|\le P.E_0e^{-P.\kappa\operatorname{sizeJ}(X)}$ on their respective domains. **PROVED:** there is no class condition $E_0=o(1)$
as $\beta\to\infty$. The P4 source says at p. 677 (H.4), after the energy bound, that “$E_0,\kappa$ are positive constants” and that $\kappa$ “can be chosen arbitrarily large”; this was checked against the PDF image, since P4 OCR is unreliable. [P4, p. 677](/home/scott/Balaban/sources/Balaban.pdf).

`Fluctuation/DetPrefactor.lean:exists_detExpansionLocC_of_chart_uniform` gives, under its explicit `FlCore`, chart, connection, divisibility and numerical premises, a single coefficient family at each root with rate
$$\lambda=\kappa''=\frac{\kappa-\log2-2\log(\operatorname{detDeg}(d,L)+1)}{2dL},\qquad
c_{\rm det}=\frac{L^d(N/2)\operatorname{covBLogMax}(d,L,\kappa)}{1-z},\quad z=2(\operatorname{detDeg}+1)^2e^{-\kappa}<1.$$
**PROVED CONDITIONAL ON those theorem premises:** $\|t_z(D,T)\|\le c_{\rm det}e^{-\lambda d_{\rm Ext}(T)}$, uniformly in root, datum, scale and torus. `half_le_detConst` gives $c_{\rm det}\ge N/2$. Thus **REFUTED:** this available prefactor has the small $\beta$ factor of the marked interaction; the lower bound on the prefactor alone does not give a lower bound on any particular term. The class can instead take $E_0$ above the
determinant and mark prefactors *after* $\kappa,L,m_0,m_1$ and the geometric losses have been fixed and *before* the large-$\beta$ threshold; see `FLUCTUATION.md` §1.5 and `SmallField/Def6.lean:Consts`. Its value must work at every scale and torus, while the displayed $c_{\rm det}$ is already independent of both.

The optional vacuum split at a fixed admissible unit datum $D_0$ is $t_z(D,T)=t_z(D_0,T)+[t_z(D,T)-t_z(D_0,T)]$. **PROVED CONDITIONAL ON a complex line disc of radius $R>1$ inside the chart:** `DetExpansionLocC.norm_term_sub_le_of_disc` bounds the bracket by $2c_{\rm det}e^{-\lambda d_{\rm Ext}(T)}/R$. `exists_norm_term_sub_le` instead gives a
positive radius $r_0(D_0)$ and a bound linear in $\|\operatorname{rawOf}D-\operatorname{rawOf}D_0\|/r_0(D_0)$; it does not give a uniform radius. **OPEN-UNICHART:** a radius and a line-disc inclusion uniform over the class data, with the required scale order. The split is optional for `boundE`; it does not by itself solve locality or rate.

The scalar vacuum coefficient is the `Ek` parameter of `IsSF` or `IsSF2`, outside `Terms.E`: the class exponent contains $-E_k|\mathbb T_1^{(k)}|$ (`Def6.IsSF.density`/`Def6v2.expo2`). If $\sum_{z,T}t_z(D_0,T)=c_{\rm vac}|\mathbb T_1^{(k+1)}|$, absorption changes $E_{k+1}$ by $-c_{\rm vac}$ in the same volume units. **OPEN-VACUUM:** show this
identity, reality of $c_{\rm vac}$, and invariance under the allowed choice of unit orientation; then match the RG counterterm and volume convention. `IsSFFamily2` takes `Ek : ℕ → ℝ`, so it may depend on $N_1$; `TorusIndep.E_eq` constrains the polymer terms, not `Ek`. For an RG coefficient intended to be volume independent, an additional
torus-independent vacuum density proof is needed.

## 2. Locality, explicit collar cost, and the rate obstruction

`Def6.IsSF.localE` and `Def6v2.SFTermClauses.localE` quantify over *all* field pairs: agreement of $(\Psi,h)$ and $(\Psi',h')$ at every fine site of $X$ implies equality of the energy terms. Neither clause assumes the fields lie in the analytic domain. **PROVED:** `Fluctuation/DetOutputTerms.lean:DetExpansionLocC.term_eq_of_agree_cellNear` gives
equality only for two chart data that agree on every $\pi'_K$ cell equal or $*$-adjacent to a cell of $Y=\operatorname{sitesOf}(T)$. Its radius follows from `detDepRadius_lt_cellSide` and `thickSet_cellNear` when $3\le L^{m_0+m_1}$. `DetExpansionLocC.anchor` puts the root cube in nonzero $T$ and makes $Y$ an admissible polymer. Hence **REFUTED:**
putting the raw term directly on $X=Y$ satisfies `localE`.

For the landed $L=3$ witness choose a canonical collar hull $H(T)$: if $b$ is the aligned base of an $a$-cell of $Y$, $a=\operatorname{cellSide}(3,m_0,m_1,K)$, attach the aligned box of side $3a$ based at $b-a(1,\ldots,1)$. This single centered box contains the cell of $b$ and all its $*$-adjacent cells, including across a torus seam. It overlaps $Y$ in the cell of $b$. Its definition commutes with paving translations, reflections and coordinate exchanges. There are at most $|T|$ attached boxes. **PROVED CONDITIONAL ON the corresponding finite-cell identities:** `Fluctuation/HatLabelsGeom.lean:thick_union` gives $H(T)$ admissible and
$$d_+:=\operatorname{sizeJ}(H(T))\le d(Y)+q|T|,\qquad q=c_G(d,3)=6d.$$
Here `SmallField/Def6Terms.lean:sizeJ` is definitionally `treeLenCovOne`. `CubeSystem.card_le_dExt` gives $|T|\le c_1(d,L)(1+d_{\rm Ext}(T))$, with $c_1=(3(2L-1))^d$; for an admissible $Y$, the landed `Fluctuation/RootActiveSize.lean:dExt_eq_sizeJ_of_isPolyDom` gives exactly $d_{\rm Ext}(T)=d(Y)$. Put $B=qc_1$. Then $d_+\le(1+B)d_{\rm Ext}(T)+B$, hence $d_{\rm Ext}(T)\ge(d_+-B)/(1+B)$.

For a fixed hull $X$, every contributing $T$ is a subset of the $a$-cells of $X$. `SizeModG1.G1_cellCount` bounds their number by $c_1(1+\operatorname{sizeJ}(X))$, so the fibre contains at most $2^{c_1(1+d_+)}$ cube sets. Consequently the triangle inequality proves the explicit regrouped estimate
$$\left\|\sum_{T:H(T)=X}t_z(D,T)\right\|\le C_{\rm hull}e^{-\lambda_{\rm hull}\operatorname{sizeJ}(X)},\quad
\lambda_{\rm hull}=\frac\lambda{1+B}-c_1\log2,\quad
C_{\rm hull}=c_{\rm det}\exp\!\left(\frac{\lambda B}{1+B}+c_1\log2\right).$$
**PROVED CONDITIONAL ON** the hull geometry, $\lambda\ge0$, and the chart bound; the active-size identity is already landed. The same calculation applies to a mark coefficient only if its *entire external dependency set* lies in this hull and its coefficient has a uniform raw rate. A separate mark support may require a larger hull and a new rate calculation.

The needed numerical condition is $\lambda_{\rm hull}\ge\kappa_{\rm out}$ for the output class, and $\lambda_{\rm hull}\ge\kappa'$ if one wants the intermediate label rate. `Fluctuation/StepRatesDirect.lean:stepRates_direct_witness` chooses $\kappa'=\kappa_{\rm det}=3\kappa_{\rm dec}/2+\kappa_0+1$ and $\kappa_{\rm out}=3\kappa_{\rm dec}/2$. If the
determinant theorem is instantiated at its minimal allowed raw rate $\lambda=\kappa_{\rm det}$, then $B\ge1$, $\lambda_{\rm hull}\le\lambda/2<\kappa_{\rm out}$ at that witness (since $\kappa_0+1<3\kappa_{\rm dec}/2$). **REFUTED:** that particular direct-rate witness plus the elementary collar count closes `boundE`. **OPEN-RATE:** select and prove
stronger determinant interpolation numerics with $\lambda\ge(1+B)(\kappa_{\rm out}+c_1\log2)$, and then choose $E_0\ge C_{\rm hull}+C_{\rm mark,hull}$ uniformly. The prefactor depends on $\lambda$, so this order must be respected.

`Fluctuation/MarkedRootGeometry.lean:bridge_of_mem` shows the rooted bridge equals $Y$ when the root cube is already in $Y$, as `DetExpansionLocC.anchor` ensures. Thus **REFUTED:** the existing bridge or `fibre_weighted_le` covers a determinant collar. The chosen repair is collar thickening, with `OPEN-HULL` and `OPEN-RATE` as explicit Lean inputs;
a sharper activity-locality theorem could replace them if proved later.

**Proposed Lean leaf `detCollarHull_rate` (OPEN, ≤300 lines):** for $L=3$ and every nonzero anchored $T$, construct the centered equivariant $H(T)$ containing `sitesOf T` and every `CellNear` dependency; prove `IsPolyDom m₀ K (H T)`, $y_z\in H(T)$, $\operatorname{sizeJ}(H T)\le(1+B)dExt(T)+B$, and $\#\{T:H(T)=X\}\le2^{c_1(1+\operatorname{sizeJ}X)}$. A second leaf
`detCollarGrouped_bound` assumes $\lambda_{\rm hull}\ge\kappa_{\rm out}$ and proves the displayed bound. The first leaf must handle the seam and preserve the root and paving action.

## 3. Lattice and spin symmetry

The class requires `eucE` term covariance for `Def6.pavingSymGroup`: translations by the $\pi'_j$ cell side, the corresponding reflections, and coordinate exchanges; it also requires `eucEloc` covariance of the *summed density* for `Def6.fullJSymGroup`, whose translations have the finer level-$j$ spacing. `rotE` uses `Def6.IsRot R`, namely
$R^\mathsf TR=1$ and either $R$ is real (all real $O(N)$) or $\det R=1$ (complex $SO(N)$). Both domain memberships are explicit hypotheses of `rotE` and `eucE`.

The exact missing lattice hypothesis `hRT` in `Fluctuation/DetActivitySymm.lean:detActivityBg_sym_of_rootTrace` says, for every finite cut set $I$, arbitrary fixed $\phi,\alpha$, transported unit root $y'$, and compatible `LatSymm S`, `CoverSymm CS`, `BlockSymm B`,
$$\operatorname{rootTrace}(\{y'\},CS.par(\operatorname{cutPt}I),\operatorname{symSite}_\sigma\phi,S.mul\alpha)
=\operatorname{rootTrace}(\{y\},\operatorname{cutPt}I,\phi,\alpha),$$
with the *same* `unitQ G`, `unitP G` on both sides. `rootTraceBg_sym_of_rootTrace` then uses `Localization/DecEquivLatBg.lean:decBg_sym`; `detActivityBg_sym_of_rootTrace` additionally needs paving membership, patch covariance and the root-image equality; `sum_detActivityBg_relabel_of_rootTraceBg` then reindexes the activities. **PROVED CONDITIONAL
ON `hRT` and those group/patch premises:** the resulting fixed-datum determinant terms transform covariantly. `Fluctuation/InteractionSymmLat.lean:xiCData_sym` gives chart transport under its hypotheses.

Here is the paper derivation of `hRT`, with its unlanded inputs exposed. A lattice symmetry induces permutations of fine sites and unit blocks. The entry formulas in `Localization/DecoupledCovUnit.lean:unitQ,unitP` depend only on block-incidence equalities and their cardinalities, so these matrices intertwine the two permutations once `unitPts` and
both incidence maps are proved equivariant. `Localization/DecEquivLat.lean:cutOperator_sym` conjugates the cut operator. Conjugating its inverse gives covariance of `Gsx`; substituting into `Localization/DecoupledCovariance.lean:decM,decN,decPi` gives their respective scalar/vector intertwining laws. The same substitutions give covariance of
`decCov`; entrywise integration in `Localization/DecoupledSqrt.lean:decLog` preserves conjugation. The diagonal trace over a transported unit root is unchanged by reindexing, proving `hRT`. Every step is ordinary finite-matrix algebra plus integrability of the already defined integral, but the needed `unitQ/unitP`, `Gsx`, `decM/N/Pi/Cov/Log`
*covariance lemmas are OPEN*, not consequences of `cutOperator_sym` alone. Translations and coordinate permutations have landed structural instances in `DecEquivTranslate`, `DecEquivTranslatePolymer`, `DecEquivPermute`; `DecEquivReflect` has `bump_reflect`, while the required reflection structures and induced patch action remain OPEN.

For spin rotations, $Q,P,G_{s,x}$ act on sites and are spin scalar; `DecEquivRot.decBg_rot` supplies background covariance under $R^\mathsf TR=1$. Bilinear field forms in $M,N,\Pi$ transform through $R$ and $R^\mathsf T$, so $\operatorname{decCov}$ and the integral defining `decLog` are conjugated by $1\otimes R$; the trace is invariant. This is a
**PROVED CONDITIONAL ON** the stated matrix intertwining and integrability laws, still **OPEN-DET-ROT** as a Lean theorem for the actual rooted family. It uses transpose orthogonality and thus covers the class's complex $SO(N)$ branch as well as real $O(N)$; no Hermitian-conjugate identity may be substituted. The relative chart/domain transport and
equivariant hull selection must also be proved before `rotE` and `eucE` follow for class terms. `eucEloc` needs a separate full-level density reindexing beyond the paving group.

## 4. Analyticity and agreement between tori

`Def6v2.SFTermClauses.analyticE` requires ambient `AnalyticOnNhd ℂ` of the *all-field* term on `{(Ψ,h):Dom.dom j (Tm.gs j X) Ψ h}`. `Def6.IsSF.analyticE` uses the full `XiDom`; the amended instance `SmallField/Def6v2Bridge.lean:completeXiDom` selects the complete domain. **PROVED:** `DetExpansionLocC.analyticAt_raw` and
`DetExpansionLocC.analyticOnNhd_rawSub` supply an ambient raw-data germ at each chart datum and analyticity on the relative `rawSub` chart. **OPEN-DET-CHART (chart-sensitive, SLICE):** a strict inclusion of every target class-domain point into one common physical chart with an open neighbourhood for Cauchy estimates, and a jointly analytic
all-field coefficient agreeing with the determinant formula there. The raw chart is not itself a proof of this inclusion.

`SmallField/Def6.lean:TorusIndep.E_eq` compares the same non-winding infinite polymer on any two admissible tori, with arbitrary pulled-back infinite fields. **OPEN-DET-TORUS:** a canonical finite-patch determinant formula, consistent weights/roots and compatible hull across both tori, giving equality of the grouped terms. Scale/torus uniformity of
$c_{\rm det}$ proves a bound, not equality. The vacuum coefficient `Ek` is separate from this term agreement.

## 5. Exact energy-output implication

**PROVED CONDITIONAL ON its displayed hypotheses:** `Fluctuation/DetStepInstance.lean:thm31aC_coeff_detLoc_withDatum` gives at a fixed chart datum with $h=h_0$ and `E1MarksC I`, $I.\kappa'\le\lambda$,
$$E_{0,\mathrm{loc}}^C(z)=\sum_T[t_z(D,T)+\operatorname{interpCoeff}(I,T)],\qquad
\|t_z(D,T)+\operatorname{interpCoeff}(I,T)\|\le(C_{\rm mark}(I)+c_{\rm det})e^{-I.\kappa' d_{\rm Ext}(T)},$$
where $C_{\rm mark}(I)=\operatorname{CPE}(d,L,I.K_c,I.\kappa_H,I.\kappa_0,I.\kappa')\sum_iI.F_0(i)e^{-I.\kappa_0I.Lab.dl(I.y_0(i))}$. The theorem also gives $E_{1,\mathrm{loc}}^C(z)=\sum_T\operatorname{interpCoeff}(I,T)$. `rootCube_mem_of_coeff_ne_zero_of_anchor` supplies the combined root only if the mark coefficient is anchored.

**OPEN-ENERGY-FAMILY:** construct one `E1MarksC` family and one determinant family over the *same* relative parameter chart, with joint analyticity, uniform $C_{\rm mark}$, external locality, equivariance, torus agreement, and matching root labels; MARKPARAM supplies the proposed mark route. If every combined coefficient reads only its chosen hull,
and `OPEN-HULL`, `OPEN-RATE`, `OPEN-DET-CHART`, `OPEN-DET-TORUS`, `OPEN-DET-ROT` and the lattice/full-density symmetry premises hold, define $e_z^+(X;D)=\sum_{T:H(T)=X}(t_z(D,T)+\operatorname{interpCoeff}(I_D,T))$. Finite reindexing gives the same $E_{0,\mathrm{loc}}^C(z)$.
The fibre estimate gives `boundE` with $P.E_0\ge C_{\rm det,hull}+C_{\rm mark,hull}$; all-field locality follows from hull dependence; analytic, symmetry and torus clauses follow by finite sums and equivariant reindexing. This implication is **PROVED CONDITIONAL ON the named OPEN premises**, not a physical output theorem. `OUTPUT.md`'s old-term lift, counterterm and density identity are additional **OPEN** inputs to
`IsSF2`/`IsSFFamily2`.

`Fluctuation/RenormExpG.lean:RenormExpInput.expE0` is another **OPEN** consumer: it asks for `IsLocExp` of $E_0\theta$ at $\theta=(1+\zeta)\psi$ on `XiCOneReal`, with a rooted cover, rate $\kappa_a$ and bound $B_{E0}$. A fixed-datum class term bound does not give that expansion; it requires the joint parameter family and its own domain/rate
transport.

## 6. Lean leaves in dependency order

1. `detUnitIncidence_covariant` (≤250 lines; **OPEN**, start now, Sonnet): permutation of `unitPts` and block-incidence transport; entrywise `unitQ`, `unitP` equivariance. Check reflection structures separately; this leaf is not chart-sensitive.
2. `detDecCov_covariant` (≤300 lines; **OPEN**, start now, strong): from `cutOperator_sym` and leaf 1 prove `Gsx`, `decM`, `decN`, `decPi`, `decCov` conjugation for arbitrary cuts and $x$; state inverse and transpose conventions explicitly.
3. `detRootTrace_covariant` (≤250 lines; **OPEN**, after 2, strong): commute matrix-entry integration in `decLog` with the permutations, prove the exact `hRT` above, and invoke the existing `DetActivitySymm` implications. Add a distinct spin-rotation lemma; reflection/full-density symmetry remains a separate group-input leaf.
4. `detCollarHull_geometry` (≤300 lines; **OPEN**, start now, strong): finite equivariant hull, seam cases, admissible support, `thick_union` cost, root, and exact `dExt`/`sizeJ` conversion. `detCollarHull_fibre` (≤200 lines; **OPEN**, after geometry, Sonnet) proves the power-set count via `G1_cellCount`.
5. `detCollarGrouped_bound` (≤150 lines; **OPEN**, after 4, Sonnet) proves the displayed constants under explicit $\lambda_{\rm hull}\ge\kappa_{\rm out}$ and $P.E_0$ inequalities. A separate numerical witness is **OPEN-RATE**; start its search now, without claiming the direct witness suffices.
6. `detClassChart_term` (≤300 lines; **OPEN**, chart-sensitive, after SLICE, strong): class-domain inclusion with strict margin, all-field extension/locality, analytic germs. `detTorusIndep_term` (≤250 lines; **OPEN**, after 4 and 6, strong) handles non-winding patch lifts.
7. `energyOutputTerms_zero` (≤300 lines; **OPEN**, after 3–6 and MARKPARAM, strong): shared parameter family and mark dependency certificate, finite sum identity, bounds, locality and symmetry. Then prove `RenormExpInput.expE0` separately from its `IsLocExp` cover hypotheses; class density and RG inputs remain separate leaves.
