# SYMSTEP — zero-class step reality and symmetry

**PROVED (audit scope).** Read-only inspection of `/home/scott/Balaban` at `ccb3228` (2026-10-13); setting $d=L=3,N=2$, whole torus, zero class. The intervening changes from `b2092e2` to this commit add energy/observable record witnesses, with no symmetry fields in those records. “General” below means the cited declaration has variable $d,L,N$, not that the physical step is inhabited there. Sources: `notes/phase1/FLUCTUATION.md` §3.1, lines 389–422, §3.6, lines 597–620; `notes/phase1/SCOPE.md` §§1,3; the two `Balaban/Frozen/Roots/*.lean` statements. Names below identify declarations checked in the cited Lean file, not proposed theorems.

## T1. Exact source claims and the frozen targets

**PROVED (source wording).** Theorem 3.1 has one *common preamble* for (a)–(h): every localized term is analytic jointly in the named parameters on its stated domain, **real for real arguments**, $O(N)$ invariant, or equivariant for $mathscr M$, and covariant under Euclidean symmetries preserving $pi_{k+1}$. It asserts real values on the real slice; it does **not** state a Schwarz identity on the whole complex chart. For (a),(g), the chart is $Xi^c_{k+1}(mathbb B_{k+1}(Y);1,\varepsilon_{k+1})$; (g) also has $\xi\in\mathcal P_\epsilon$. For (b),(h), $\|g\|_{\ell^1}<1$ and (h) uses the H.7 domain. At zero class there are no boundary terms, and $Y$ is an ordinary covered domain.

**PROVED (interpretation of the displayed formulas).** Write $D$ for the field datum (including $\psi,h$), $Q\in O(N)$ real, and $\tau$ for a coarse lattice translation or signed coordinate permutation preserving $\pi_{k+1}$. Put $(\tau g)(u)=g(\tau^{-1}u)$, $(Qg)(u)=Q g(u)$, and transform all field entries, including $h$, by $Q$. Then the preamble requires, for each *chosen localized term*,
$$E''_{0,Qh}(z,Y;QD)=E''_{0,h}(z,Y;D),\quad M''_{0,Qh}(x,Y;QD,Qg)=Q M''_{0,h}(x,Y;D,g),$$
$$E''_{0,h}(\tau z,\tau Y;\tau D)=E''_{0,h}(z,Y;D),\quad M''_{0,h}(\tau x,\tau Y;\tau D,\tau g)=M''_{0,h}(x,Y;D,g).$$
**PROVED (same preamble).** The scalar terms $C_1,C_2,\mathscr E_u$ of (g) obey the energy equations with $\xi$ carried unchanged, and the vector $\mathscr M^{(k+1)}$ of (h) obeys the observable equations. Reality means their scalar or component values are real when all *named* arguments, including $g$ and $\xi$ where present, are real. For a complex Schwarz identity one must conjugate **all** complex arguments ($D,g,\xi$ and any complex interpolation parameter) and prove both points belong to the chart; that stronger statement is **OPEN** for the final coefficients.

**PROVED.** For fixed $h=e_1\in\mathbb R^2$, only its stabilizer $O(1)=\{\operatorname{diag}(1,1),\operatorname{diag}(1,-1)\}$ acts within the same fixed-$h$ step. A general $Q$ compares the $h$ and $Qh$ steps; the paper's $h$ is not fixed. Lattice symmetries move $z,x,Y$ and pull back $g$; they do not rotate spin components. The admissible translations are by the coarse lattice, together with the cubic group, subject to preservation of the chosen block structure.

**PROVED (frozen declarations).** `logPartition_multiscale` quantifies every unit $h$ and requires support, $g|_X$ locality, analyticity on $\|g\|_1<1$, a bound, a log-partition identity, and equality on two tori. It has **no** reality or symmetry binder. `lowTemperature_correlations` quantifies every unit $h$ and requires the displayed transverse/longitudinal tensor asymptotics, with **no** symmetry binder. Thus none of the three clauses is a literal Root-F or Root-C obligation. **OPEN (proof route).** Internal $O(N)$ transport can shorten the proof for all $h$ and explain the Root-C tensor form; reality helps identify real Gibbs fields; lattice covariance can help construct coherent root families but does not imply the frozen two-torus equality. Priority for root closure is internal transport, then reality, then lattice covariance; the requested Lean implementation order below is reality, lattice, internal.

## T2. Landed declaration inventory

**PROVED (reading rule).** “Below” means below `e1Coeff`, `interpCoeff`/`gsumCoeff`, or `obsCoeff` as final step coefficient functions; “coefficient” means the theorem already concerns a local expansion coefficient. All rows are PROVED inventory facts; no row claims the complete Theorem 3.1 clause.

| Landed file | Main declaration and object | Feeds / level |
|---|---|---|
| `Symmetry/EvenReduction.lean` | `sliceCoeff_odd_eq_zero`: even analytic slice coefficients | internal / below |
| `Symmetry/InvariantReduction.lean` | `exists_invariant_reduction_nhd`: invariant scalar reduction | internal / below |
| `Symmetry/Rotation.lean` | `exists_rotation`: orthogonal frame map | internal / below |
| `Symmetry/TotallyReal.lean` | `eventually_eq_zero_of_real`: analytic uniqueness from real data | reality / generic |
| `SmallField/XiSymm.lean` | `xiC_rot_iff`, `xiCBounds_rot`: $\Xi^c$ chart under real $O(N)$ | internal / below, general |
| `SmallField/XiLatSymm.lean` | `xiC_sym_iff`, `nonempty_latSymm_levelGS`: lattice chart and group | lattice / below, general |
| `SmallField/XiReal.lean` | `realizes_vn`: real chart realization | reality / below; no final chart-conjugation theorem |
| `Background/Equivariance.lean` | `bgField_rot`: background rotation | internal / below, general |
| `Background/EquivarianceDomain.lean` | `inDomainC_rot_iff`: background chart rotation | internal / below, general |
| `Background/EquivarianceLat.lean` | `bgFieldC_sym`: background under `LatSymm` | lattice / below, general |
| `Background/ApproxReal.lean` | `isRealVec_approxField`: real approximate field | reality / below |
| `Background/ConstantConfigReal.lean` | `constMinimizer_mulVec`: constant minimizer rotation | internal / below |
| `Localization/DecEquivReal.lean` | `decBg_real`, `fluct_real`: decoupled fields | reality / below, general |
| `Localization/DecoupledCovReal.lean` | `decCovSqrt_one_eq_real`, `decLog_one_eq_real`: covariance and log | reality / below |
| `Localization/DecEquivRot.lean` | `decBg_rot`, `fluctField_rot`: decoupled field rotation | internal / below, general |
| `Localization/DecEquivLatBg.lean` | `decBg_sym`: decoupled background lattice transport | lattice / below, general |
| `Localization/DetDecCovSymm.lean` | `decCov_rm`, `decLog_rm`: decoupled covariance and log relabeling | lattice determinant / below |
| `Localization/DetUnitIncidenceSymm.lean` | `unitAct`: unit-block incidence | lattice determinant / below, general |
| `Localization/Dec2Covariance.lean` | `decCovSqrt_BD_of_GsxBD`: block diagonal covariance; despite filename, no final symmetry clause | locality / below |
| `Localization/P6PairCastReal.lean` | `p6_action_at_one_real`: real old-action evaluation | reality / below |
| `Model/Symmetry.lean` | `gibbsExpectation_rotConfig`, `gibbsExpectation_shiftConfig`: physical measure | internal/lattice / partition level |
| `Model/SymmetryPartition.lean` | `partitionFunction_rot`, `rotFamily_analytic`: source family | internal / Root-F transport, not step coefficients |
| `Fluctuation/ExpansionSymm.lean` | `interactionBlock_rot`: interaction rotation | internal / below |
| `Fluctuation/ExpansionReal.lean` | `expansion_chord_real`: real expansion chord | reality / below |
| `Fluctuation/DetRootTraceSymm.lean` | `rootTrace_unitAct`, `sum_detActivityBg_sym`: determinant root traces | lattice / below grouped coefficient, general |
| `Fluctuation/DetActivitySymm.lean` | `detActivityBg_relabel_of_rootTraceBg`: determinant activity relabeling | lattice / below grouped coefficient |
| `Fluctuation/DetSymmGroup.lean` | `exists_detExpansionLocC_sym`: a transported **pair** of determinant records | lattice / term coefficient, general |
| `Fluctuation/DetCollarHullSymm.lean` | `detCollarGrouped_comp`, `exists_detExpansionLocC_grouped_sym`: transported grouped determinant term | lattice / grouped coefficient; $L=3$ for reflection |
| `Inhabited/DetCollarHullSymmWitness.lean` | `detGrouped_sym_nonempty`: finite nonidentity instance | lattice / grouped coefficient witness |
| `Fluctuation/DetRotation.lean` | `exists_detExpansionLocC_rot_real`: one determinant record invariant under real $Q$ on $\Xi^c$ | internal / term coefficient, general |
| `Fluctuation/InteractionSymm.lean` | `i5_functional_evTerm`: I-5 term map | lattice/internal / below final coefficient |
| `Fluctuation/InteractionSymmLat.lean` | `fnOfDec_sym`, `evTerm_sym`: Prop. 3.3 term transport | lattice / below final coefficient |
| `Fluctuation/InteractionSymmRot.lean` | `F₁_rot`, `evTerm_rot`, `F₁_conj`: chosen background and term | internal/reality / below final coefficient |
| `Fluctuation/InteractionSymmSolRot.lean` | `Sol_rot`, `evTermSol_rot`: chosen perturbative solver and term | internal / below final coefficient, general |
| `Fluctuation/InteractionSymmSol.lean` | `SolSpec`: strict-domain small-fixed-point uniqueness | internal/reality / below final coefficient |
| `Fluctuation/InteractionSymmSolConj.lean` | `Sol_conj`: solver conjugation | reality / below final coefficient |
| `Fluctuation/InteractionSymmSolCoef.lean` | `coef_conj_two`, `evTerm_conj_two`: coefficient conjugation | reality / Prop. 3.3 coefficient |
| `Fluctuation/InteractionSymmSolReal.lean` | `fnOfDecSol_conj`, `evTermSol_real`: term conjugation | reality / below final coefficient |
| `Fluctuation/Prop33SymmDef.lean` | `TermRot`, `TermReal`: abstract term predicates | internal/reality / below |
| `Fluctuation/Prop33SymmEnergy.lean` | `energyBlock_rot`, `energyBlock_conj`: bare energy | internal/reality / below |
| `Fluctuation/Prop33SymmNu.lean` | `nupart_locInt_symm`: source mass local interaction | internal/reality / below |
| `Fluctuation/Prop33SymmV.lean` | `vpart_locInt_symm`, `F1Spec`: potential term and valid-domain background specification | internal/reality / below |
| `Fluctuation/Prop33SymmClose.lean` | `prop33_VNu_symm`: combined potential and mass term | internal/reality / below final coefficient |
| `Fluctuation/Prop33SymmRay.lean` | `rayTerm_dl3_conj`, `dirTerm_equiv`: Taylor ray and directional source | reality/internal / below |
| `Fluctuation/MarkRealDomain.lean` | `markReal_hdomT_of_disc`: real mark domain | reality / below |
| `Fluctuation/MarkRealRegular.lean` | `markReal_fderiv_mask_eq_neg_beta_sum`: marked derivative | reality / below |
| `Inhabited/MarkRealDiscSlice.lean` | `markReal_disc_slice`: mark disc on real slice | reality / below |
| `Inhabited/MarkRealSlice.lean` | `markReal_slice_of_count`: physical real-slice mark | reality / below |
| `Fluctuation/Lemma25Real.lean` | `IsRealMat.inv`: real inverse matrix | reality / below |
| `Fluctuation/CubeActionRealStar.lean` | `cubeActionStar_partition`: star action partition | reality / below |
| `Fluctuation/CubeActionReal.lean` | `cubeActionStar_eq_actionG`: real cube action | reality / below |
| `Fluctuation/Theorem42RealStep1.lean` | `real_step1`: real step value | reality / below coefficient |
| `Fluctuation/Theorem42RealFlow.lean` | `real_step1_flow`: real flow value | reality / below coefficient |
| `Fluctuation/Theorem42RealVolume.lean` | `emptyTraceTerm_bound_of_input`: real-volume bound, no symmetry conclusion | reality estimates / below |
| `Inhabited/E1MarkParamCommon.lean` | `e1MarkParamFamily_fromTower`: analytic parameter mark **record** for chosen $F_1,\mathrm{Sol}$ | reality/internal/lattice input; no symmetry field |
| `Fluctuation/Thm31CoeffA.lean`, `Thm31CoeffB.lean`, `ParamDatumFamily.lean` | `interpCoeff`, `e1Coeff`, `obsCoeff`, `e1CoeffC`; `gsumCoeff_congr`, `obsCoeff_congr`: deterministic sums/integrals | final coefficient formulas, **no** symmetry theorem |

## T3. Choice and coefficient transport

**PROVED.** `interpCoeff I T = gsumCoeff BS.μ I.Lab I.A I.y0 I.G T` (`Thm31CoeffA.lean`); `e1Coeff I D T=D.term T+interpCoeff I T`; its complex-chart counterpart `e1CoeffC` has the same formula (`ParamDatumFamily.e1CoeffC_eq`); `obsCoeff I T=kernelMarkSum I.hker I.E1 T+I.Erem T` (`Thm31CoeffB.lean`). `detCollarGrouped e X=\sum_{T:H(T)=X}e(T)` (`DetCollarHull.lean`). These formulas are deterministic **after** their inputs are fixed. `gsumCoeff_congr` and `obsCoeff_congr` expose the local reads; a transported version needs equivariant `Lab`, $\mu$, $A$, $G$, roots, and for `obsCoeff` the kernel and both mark families. None of the coefficient records has such a field today. This is **OPEN** for the physical inputs, although the formula-level transport is a bounded proof task.

**PROVED.** `exists_detExpansionLocC_grouped_sym` supplies, for each $\tau$, *some* records $E,E'$ whose term and grouped term equations hold; its proof rewrites both terms as the same determinant-activity sum. It does not assert that independently chosen `Classical.choice` records form one coherent family for all $\tau$. `exists_detExpansionLocC_rot_real` supplies a single determinant record for each $Q$ with a term equation, but likewise does not make an arbitrary prior choice invariant. **OPEN (cheapest repair).** Export the canonical activity-sum as one record family indexed by the root, then apply `detCollarGrouped_comp`; this reuses the landed proof and retains its constant/rate, with $L=3$ for reflected collar hulls.

**PROVED.** `F1Spec` (`Prop33SymmV.lean`) identifies a chosen $F_1$ with the decoupled background on valid union-domain inputs; `SolSpec` (`InteractionSymmSol.lean`) contains uniqueness among small fixed points on the strict domain. `F₁_rot`, `F₁_conj`, `Sol_rot`, `Sol_conj` use these specifications. Thus arbitrary off-domain values do not matter for terms evaluated inside the domains. `SourceDirectTermsScale.sourceDirectTerms_slice_ray` fixes one $\mathcal Y,T$ before the source and datum but obtains them existentially from the Prop. 3.3 expansion; the declaration does not say $\tau\mathcal Y=\mathcal Y$ or transport $T$. **OPEN.** Make its geometric index set and term formula equivariant, or transport an entire finite family under the finite lattice group and average where transformed read sets, supports, and constants are verified. The final observable `obsCoeff` also needs equivariant $g$ dependent kernel and marks. For $O(2)$, use the unique valid-domain pair and equivariant formulas; a finite averaging argument only covers the fixed-$h$ stabilizer.

**PROVED.** The renormalization endpoint `renDec_one_unique_sharp` (`RenormEndpointSharp.lean`) identifies the physical all-ones fixed point in its stated small ball; it does not give symmetry of arbitrary off-domain extensions or of source-dependent localized coefficients. **OPEN.** Transport the fixed-point equation and show the rotated/transformed candidate stays in the same uniqueness ball before using that theorem. At the level of the *sum*, physical partition covariance follows from `partitionFunction_rot`; it cannot supply the source's termwise clause without choosing an equivariant decomposition.

## T4. Bounded Lean leaves, in implementation order

**OPEN (plan; all sizes estimates, one worker each).** In the table $c(I,T)$ means the displayed deterministic coefficient, $\bar{\phantom u}$ is componentwise conjugation, and $\tau T$ is `cubeAct τ T`. “Independent” means no choice of generator ruling, hull-rate redesign (`RATES`), or source radius $\rho$ enters the *statement or proof*; later physical instantiation may depend on them. If a rate or generator is changed, only the physical assembly/record packaging in rows R4,L3,O3 is redone; the formula lemmas remain. A change of $\rho$ affects O3's domain only.

| Leaf / estimate | Exact proposed conclusion, with landed inputs | Independence / start |
|---|---|---|
| R1 / 100–160 lines | For real $s\in[0,1]$, if $A(s).H,G(s)$ are real valued and $\mu$ is a real probability measure, $\overline{\operatorname{gsumCoeff}(\mu,Lab,A,y_0,G,T)}=\operatorname{gsumCoeff}(\mu,Lab,A,y_0,G,T)$; unfold `gsumCoeff`/`Gsum`. | all three; **start today** |
| R2 / 100–150 | If $h_{i,T},E_{i,T},E^{rem}_T$ are real, `kernelMarkSum h E T` and `obsCoeff I T` are real; use `ObsMarks.Erem_eq`, R1, and `obsCoeff` formula. | all three; **start today** |
| R3a / 150–230 | On the real chart and real $s$, $\overline{A(s,Y;D,g)}=A(s,Y;D,g)$ for the physical activity; use `evTermSol_real`, `p6_action_at_one_real`. | generator/rate independent as identity; **start today**; physical bridge **OPEN** |
| R3b / 150–240 | On the same slice, each physical energy/source mark and observable kernel satisfies $\bar G=G$, $\bar h=h$; use `markReal_slice_of_count`. | generator/rate independent as identity; **start today**; bridge **OPEN** |
| R3c / 130–220 | For real chart data, the determinant term satisfies $\overline{D.term(D_0,T)}=D.term(D_0,T)$; use `decLog_one_eq_real` and the determinant activity formula. | generator/rate independent as identity; **start today**; bridge **OPEN** |
| R4a / 100–160 | For real valid $D,g,\xi$, $\overline{e1CoeffC(D,g,T)}=e1CoeffC(D,g,T)$; apply R1,R3 and `ParamDatumFamily.e1CoeffC_eq`. | physical packaging may change with generator/rate; **after R3** |
| R4b / 120–200 | On the same domain, $\overline{obsCoeff(D,g,T)}=obsCoeff(D,g,T)$; apply R2,R3 and `Thm31CoeffB.obsCoeff_congr`. | physical packaging may change with generator/rate; **after R3** |
| R4c / 180–270 | For real valid $D,g,\xi$, each localized $C_1,C_2,\mathscr E_u$ is real and every component of $\mathscr M^{(k+1)}$ is real; combine R4a,b with the real algebraic flow of `real_step1_flow`. | generator/rate affect assembly; **after R4a,b** |
| L1 / 140–230 | If $\tau$ transports `Lab`, $\mu$, $A(s)$ and $G_i(s)$ with the root labels, $\operatorname{gsumCoeff}(I_{\tau D,\tau g},\tau T)=\operatorname{gsumCoeff}(I_{D,g},T)$; reindex `Gsum` and use `xiC_sym_iff`. | all three; **start today** as abstract lemma |
| L2 / 100–190 | Under matching transport of $h_{i,T}$, $E^1_{i,T}$ and $E^{rem}_T$, $\operatorname{obsCoeff}(I_{\tau D,\tau g},\tau T)=\operatorname{obsCoeff}(I_{D,g},T)$; reindex `kernelMarkSum`, use L1. | all three; **start today** as abstract lemma |
| L3a / 160–250 | For each $\tau$, $\tau\mathcal Y=\mathcal Y$ and $T(\tau Y;\tau D,\tau g)=T(Y;D,g)$ in `sourceDirectTerms_slice_ray`, using `evTerm_sym` and a canonical domain index. | geometry independent of radius; **OPEN** pending canonical index choice |
| L3b / 170–260 | Transport common labels, `e1MarkParamFamily_fromTower` marks and activity, then $e1Coeff_{\tau z}(\tau D,\tau T)=e1Coeff_z(D,T)$ via L1 and `exists_detExpansionLocC_grouped_sym`. | generator/rate affect assembly; **after L3a** |
| L3c / 170–270 | Transport the observable kernel and marks, then $obsCoeff_{\tau x}(\tau D,\tau g,\tau T)=obsCoeff_x(D,g,T)$ and the (g),(h) terms via L2. | generator/rate affect assembly; **after L3a** |
| O1 / 140–240 | On valid $\Xi^c$ inputs, $F_1(s,QD)=QF_1(s,D)$ and $Sol(s,Qe)=QSol(s,e)$; package `F₁_rot`, `Sol_rot`, `xiC_rot_iff` for the *same* chosen pair. | all three; **start today** |
| O2 / 150–250 | If activity/measure/labels/marks and kernel commute with real $Q$ while $h,D,g$ all rotate, then $e1Coeff_{Qh}(QD,Qg,T)=e1Coeff_h(D,g,T)$ and $obsCoeff_{Qh}(QD,Qg,T)=QobsCoeff_h(D,g,T)$; use formula lemmas, `exists_detExpansionLocC_rot_real`. | all three abstractly; **start today** after O1 |
| O3a / 180–250 | For physical energy activity and marks, $A_{Qh}(QD)=A_h(D)$ and $G^E_{Qh}(QD)=G^E_h(D)$; use O1, `prop33_VNu_symm`, `exists_detExpansionLocC_rot_real`. | generator/rate only assembly; fixed-$h$ $O(1)$ **starts today** |
| O3b / 200–280 | For output component $a$, source marks/kernel obey $\sum_i h'_{a,i,T}E'_{a,i,S}=\sum_bQ_{ab}\sum_i h_{b,i,T}E_{b,i,S}$ after the mark labels are reindexed; prove the same for the remainder, yielding O2 and (h). | generator/rate only assembly; full $O(2)$ **waits for source radius $\rho$** |
| O3c / 160–230 | Apply O3a,b to the (g) perturbative coefficients on $\Xi^c\times\mathcal P_\epsilon$ with $\xi$ fixed, and show their $h\mapsto Qh$ transport. `sum_norm_rotSource_le` and `rotFamily_analytic` control the source ball. | generator/rate only assembly; full $O(2)$ **waits for $\rho$** |

## T5. False shortcuts and confidence

**REFUTED.** `Classical.choice` applied separately at $z$ and $\tau z$ is not equivariant merely because equivariant witnesses exist. Symmetry of $\sum_YE(Y)$ does not imply symmetry of each $E(Y)$. A real value at one point does not imply conjugation on a chart lacking a proved conjugation map. At fixed $h=e_1$, all of $O(2)$ does not preserve the same datum. `SymmetryPartition.sum_norm_rotSource_example` gives a rotated unit $\ell^1$ source of norm $\sqrt2$, so the unit ball is not $O(2)$ invariant. Arbitrary averaging can alter support or reads unless the entire transported family is reindexed. The determinant-only record is not the full physical energy; complex transpose-orthogonal covariance alone is not the real-$O(N)$ chart theorem.

**PROVED (confidence).** High confidence in the source/frozen distinction and named landed declarations. **OPEN (confidence limit).** Medium confidence in the proposed line counts and physical bridge schedule: the coefficient inputs are not yet packaged with equivariance, and no final Theorem 3.1 symmetry clause is proved by the inventory alone.
