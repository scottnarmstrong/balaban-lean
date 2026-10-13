# ROOTCMAP — the second frozen root

Scope: hard spins, $d\ge3$, $N\ge2$. Paths below are relative to the read-only `/home/scott/Balaban/`. P9 means Balaban–O'Carroll, *Commun. Math. Phys.* **199** (1999), 493–520, source `sources/s002200050510.pdf`; printed pages are cited. **PROVED** means a checked landed declaration with its stated
hypotheses; **PROVED CONDITIONAL ON** names a premise not produced here; **OPEN** is a missing producer; **REFUTED** rejects an implication. The current map is not an audit verdict on either draft anchor.

## 1. Exact frozen targets and source

`frozen/manifest.json` registers `thm.RootF.logPartition_multiscale.v1` (`Balaban.logPartition_multiscale`, ABI `c3e19f8e94b32ec4600de11df7ab01764c2d5947d01e30c16eafe20a36c6a53a`) and `thm.RootC.lowTemperature_correlations.v1` (`Balaban.lowTemperature_correlations`, ABI
`47232a214d6ea0296e86c69a64274978002faa1387eb949ba684ddaeb8164814`); both are `DRAFT_SORRY`, with empty provider files. The frozen source revision is `notes/phase0/surface-v1-for-approval.md` v1.2, approved 11 October 2026. No file named `DEPGRAPH` or dependency graph was found under the repository,
including `orchestration/`; `review/FORMALIZATION_ROADMAP.md` §§1.3, 3.2, 3.4 and `orchestration/LEDGER.md` give the recorded proof path. **PROVED:** the anchors are frozen statements. **OPEN:** their proofs and source-level dependency graph.

The frozen Root-C has the following outer-to-inner order: for each $d,N$ with $d\ge3,N\ge2$, there exist *before* $\beta$ numbers $\beta_0,c,c',\rho_0,\rho_1$ and an integer $q\ge2$, with $c,c',\rho_0>0$ and $0<\rho_1<1$; for every $\beta\ge\beta_0$ there exist functions $m(\nu)$ and
$G_{tr/lg}(\nu,z)$, independent of the direction $h$. For each $0<\nu\le1$, unit $h$, $x,y\in\mathbb Z^d$, and $\varepsilon>0$, one $n_0$ works for *every* positive torus side $\ell$ divisible by $q^{n_0}$: the finite-volume first and truncated second moments differ by less than $\varepsilon$ from
$$m(\nu)h_i,\qquad G_{tr}(\nu,x-y)(\delta_{ik}-h_ih_k)+G_{lg}(\nu,x-y)h_ih_k.$$
The same functions obey $|m(\nu)-1|\le c\beta^{-1+\rho_1}$ and $|G_{tr/lg}(\nu,z)|\le c(1+\|z\|_\infty)^{-(d-2)}e^{-c'\sqrt\nu\|z\|_\infty}$. As $\nu\downarrow0$ they converge pointwise; there are $m_0,\gamma>0,G_{tr,0},G_{lg,0},G$ with $|\gamma-1|\le c/\beta$, $-\Delta G=\delta_0$, $G\to0$ at
infinity, and
$$|G_{tr,0}(z)-m_0^2(\beta\gamma)^{-1}G(z)|,\ |G_{lg,0}(z)|\le c(1+\|z\|_\infty)^{-(d-2+\rho_0)}.$$
Here `Torus d ℓ = Fin d → ZMod ℓ`; `aprioriMeasure` is the product of unit-sphere surface measures; `energy` is $\frac12\sum|\nabla\phi|^2+\frac\nu2\sum|\phi-h|^2$; `partitionFunction` integrates $e^{-\beta H+\langle g,\phi\rangle}$; `gibbsExpectation` normalizes by $Z(0)$; `onePoint` is
$\langle\phi_i(x)\rangle$; `twoPointTruncated` subtracts the product of one-point functions. These frozen definitions were unfolded directly from `Frozen/Model/{Torus,AprioriMeasure,Energy,PartitionFunction,GibbsExpectation,OnePoint,TwoPointTruncated}.lean`.

P9 Theorem 1.1, printed pp. 494–495, says “M and G can be written as” the same $h$-projector form and prints $|m(\beta,\nu)-1|<c\beta^{-1+\rho_1}$ and $|G_{tr}(z)|,|G_{lg}(z)|\le c|z|^{-(d-2)}e^{-c'\sqrt\nu|z|}$ for $\nu>0$. At $\nu=0$ it gives the transverse leading term
$m(\beta)^2(\beta\gamma_\infty)^{-1}(-\Delta)^{-1}$ with a faster-decaying remainder and longitudinal component. Its theorem says “For the $v\downarrow0$ limiting expectations” (p. 495). The frozen root specializes to $\lambda=\infty$, uses $1+\|z\|_\infty$ at $z=0$, and spells out convergence along
divisible tori; these are the approved phase-0 conventions. The paper calls the result spontaneous magnetization; the frozen $|m_0-1|$ consequence follows by passing the positive-$\nu$ estimate to the limit when $\beta$ is large enough. P9 (4.4)–(4.9), pp. 516–517, gives the final
generating-function split and its derivatives; (4.17)–(4.18), pp. 518–519, gives the lattice Green decomposition and running-coefficient comparison.

Root-F's exact quantifier order is $\exists\delta>0\ \forall\kappa,c_9>0\ \exists L\ge2,M\ge1,\beta_0\ \forall\beta\ge\beta_0\ \forall\nu\in(0,1],h\in S^{N-1}\ \exists k_f,T$. Its $k_f$ obeys $L^{k_f}\sqrt\nu\le L$ and $1/2\le L^{k_f+1}\sqrt\nu$. The *same* family $T_\ell(j,x,X;g)$ works on all tori
with $ML^{k_f+1}\mid\ell$: it vanishes off polymers containing $x$, is local in $g|_X$, analytic for $\|g\|_1<1$, bounded for $\|g\|_1\le1/2$ by $c_9L^{-j\theta}e^{-\kappa|X|/(ML^j)^d}$ with $\theta=(d-2)/2+\delta$, and represents $\log(Z_\ell(g)/Z_\ell(0))$ as $\langle g,h\rangle+\sum_{j,x,X}\langle g(x),T_j(x,X;g)\rangle$. Its last clause equates coefficients on common non-winding quarter-box images across tori. `Correlations/Clauses.lean:RootFClauses` copies these last clauses and `rootFStatement_iff` groups them without importing the draft anchor.
`Frozen/Geometry/IsPolymer.lean` says nonempty, block-closed, nearest-neighbour connected; its block side is $ML^j$.

## 2. Root-F to correlation functions: exact reach

**PROVED CONDITIONAL ON Root-F clauses:** `Model/Derivatives.lean:fderiv_logPartition_zero` and `fderiv_fderiv_logPartition_zero` identify derivatives of the principal log at $g=0$ with one-point and truncated two-point moments. `Correlations/Identity.lean:onePoint_eq_of_clauses` and
`twoPointTruncated_eq_of_clauses` differentiate the *finite* Root-F sum. At an admissible torus they give
$$M_{\ell,i}(x)=h_i+\sum_{j,X\ni x}T_{\ell,j}(x,X;0)_i,$$
$$G_{\ell,ik}(x,y)=\sum_{j,X\ni x,y}\{D_{g_k(y)}T_{\ell,j}(x,X;0)_i+D_{g_i(x)}T_{\ell,j}(y,X;0)_k\}.$$
The support restriction in the second line uses both vanishing off polymers and locality in $g|_X$; differentiating the explicit leading $g$ also explains the two summands. `Agreement.value_agree` and `fderiv_agree` transfer both terms across common finite boxes. `PolymerCount`, `PolymerDiameter`,
`Estimates` and `Tail` bound the outside-box terms. `ThermoLimit.onePoint_tendsto_along_multiples` and `twoPoint_tendsto_along_multiples` then prove their limits for fixed $\beta,\nu,h,x,y$ along $q=ML$; $q^{n_0}\mid\ell$ eventually implies $ML^{k_f+1}\mid\ell$.
`Model/BlockStructure.exists_block_structure` gives the $h$-independent transverse/longitudinal projector form. These are landed *conditional* consequences, not a Root-F proof.

The Root-F estimate alone gives $|m-1|\le3c_9$ (`Estimates.abs_onePoint_sub_le`, `Consequences.abs_limit_onePoint_sub_le`) and two-point decay with polynomial exponent $\theta=(d-2)/2+\delta$ and a $\sqrt\nu$ exponential (`Estimates.exists_abs_twoPointTruncated_le`,
`Consequences.exists_abs_limit_twoPoint_le`). Cauchy differentiation in $g$ costs a constant and supplies no additional factor $L^{-j(d-2)/2}$. **REFUTED:** these clauses by themselves imply Root-C's $\beta^{-1+\rho_1}$ rate or its $d-2$ exponent. Choosing $c_9=\beta^{-1+\rho_1}$ in Root-F is
invalid: $L,M,\beta_0$ are chosen *after* $c_9$, so this choice cannot furnish one $\beta_0$ and one $q$ for all subsequent $\beta$. Root-F relates no two different masses, so its fixed-$\nu$ torus limit does not imply a $\nu\downarrow0$ limit. No positivity or Ward identity closes that gap;
positivity is used for $Z(0)>0$ and the derivative identity; neither a monotonicity theorem nor a Ward identity is an input of the landed Root-C assembly.

**Additional flow input, OPEN physically:** P9 (2.1)–(2.20), pp. 495–499, adds the first and second source coefficients of the effective action; P9 Proposition 3.1 (3.11)–(3.13), pp. 502–504, transports two marked functions through a step. `Correlations/C1Star.lean:C1Star` encodes their final
observable consequences, with constants fixed before $\beta$: (F1) the real running coefficients $\xi_k(\nu)=O(\beta^{-1}L^{-2\gamma_0(k+1)})$ and continuity at $0$; (F2) $m_J=1-\sum_{j<J}\beta_j^{-1/2}\mu_{j+1}$, $|\mu_j|\le c_*\beta^{-1/2+\rho_1}L^{-j\rho_0}$, and $|e_m|\le c_*\beta^{-2}L^{-2J(d-2)}$ on sufficiently large admissible tori; (F3) the
transverse Gaussian main sum $m_J(x)m_J(y)\sum_{j<J}(\beta\gamma_j)^{-1}T_j^{\ell,\nu\delta_j}$ plus a remainder bounded by $c_*[(1+\|x-y\|)^{-(d-2+\rho_0)}+\nu^{(d-2)/2}]e^{-c'\sqrt\nu\|x-y\|}$, with the longitudinal part entirely remainder in the hard-spin case. The finite-torus identity requires $2|x_i-y_i|<\ell$ for each coordinate. (F3) also demands limits of both remainders along tori and as $\nu\downarrow0$; these are extra
assumptions, not consequences of Root-F's $T$-agreement. P9 (4.17)–(4.18) and the free running flow identify the limiting main sum with $(\beta\gamma_\infty)^{-1}G$ and yield $|\gamma_\infty-1|=O(\beta^{-1})$. The scalar magnetization factor supplies $m_0^2$.

The dependency is therefore $\text{Root-F clauses}+\text{C-1* on the same }(L,M)+\text{Gaussian kernels}\Longrightarrow\text{Root-C}$. **PROVED CONDITIONAL ON `RootFAndC1Star`:** `Correlations/RootCFromFlow.lean:rootC_of_rootFAndC1Star` proves `RootCStatement d N`, the copied frozen conclusion;
`KernelLargeAssembly.kernelHyp_and_large_holds` already discharges the Gaussian hypothesis. `Assembly.rootC_of_rootF_c1Star` performs the five steps: fixed-mass torus limits (`LimAlong.exists_limits`, `bullet_one`), positive-mass bounds (`BoundsNu.bounds_pos_nu`), $\nu\downarrow0$ limits
(`ZeroLimit.tendsto_mag`, `tendsto_mainSum`), Green identification (`GreenIdentification.KernelHyp.tsum_eq_latticeGreen`), and Goldstone remainder (`GoldstoneStep.limits_zero`). Thus the *conditional implication* is landed, but there is no landed `RootFStatement → RootCStatement` and no physical
`RootFAndC1Star` witness. **REFUTED:** calling Root-C a corollary of the frozen Root-F clauses alone. The registered Root-C provider remains empty; neither draft anchor is sealed.

## 3. Landed inventory in `Balaban/Correlations/`

Each row names every file and representative checked declarations. “Conditional” means an explicit clause, kernel, or flow-data hypothesis remains; a theorem proved from such a hypothesis is not a physical correlation theorem.

| File | Main landed content and present role |
|---|---|
| `Clauses` | `RootFStatement`, `RootFClauses`, `RootFTorusClauses`, `RootFAgreement`, `rootFStatement_iff`: exact clause package; **PROVED** definitions/equivalence. |
| `RootCStatement` | `RootCStatement`: copy of frozen Root-C type; **PROVED** definition, not its inhabitance. |
| `C1Star` | `C1StarF1`, `C1StarF2`, `C1StarF3`, `C1Star`, `RootFAndC1Star`: extra flow package; **OPEN** physical inhabitance. |
| `KF0Cauchy` | `sub_zero_eq_sum_kf0Deriv`, `norm_kf0Deriv_le`, `kf0Deriv_congr`, `analyticOnNhd_kf0Deriv`: source FTC, Cauchy, locality; **PROVED CONDITIONAL ON** analytic/bound premises. |
| `KF0RootFPartial` | `rootFTorusClauses_kf0_of_oneScaleInput`, `rootFAgreement_kf0_of_oneScaleInput`, `rootF_kf0_partial_of_oneScaleInput`: $k_f=0$, $\nu\ge7/(8L^2)$ only; **OPEN** one-scale input, not Root-F. |
| `Identity` | `onePoint_eq_of_clauses`, `twoPointTruncated_eq_of_clauses`: source differentiation; **PROVED CONDITIONAL ON** Root-F clauses. |
| `Box`, `Agreement` | `valMinAbs_embedZ`, `sum_split`; `value_agree`, `fderiv_agree`: box lifting and coefficient/derivative agreement; **PROVED CONDITIONAL ON** Root-F agreement. |
| `PolymerCount`, `PolymerDiameter` | `sum_polymersAt_pow_le`, `torusDist_add_one_le`: rooted block counting and distance; **PROVED** under geometry premises. |
| `Estimates`, `Tail` | `abs_onePoint_sub_le`, `exists_abs_twoPointTruncated_le`; `norm_tail_sum_le`, `norm_tail_dsum_le`: weak Root-F bounds and tails; **PROVED CONDITIONAL ON** clauses. |
| `ThermoLimit`, `Consequences` | `onePoint_tendsto_along_multiples`, `twoPoint_tendsto_along_multiples`; `onePoint_close_of_rootF`, `exists_abs_limit_twoPoint_le`: fixed-mass thermodynamic limit and weak decay; **PROVED CONDITIONAL ON** clauses or `RootFStatement`. |
| `RealSequences`, `Asymptotics` | `SeqHyp.gammaR_bounds`, `tendsto_gammaR`; `goldstone_rewriting`: running-coefficient bounds and comparison; **PROVED CONDITIONAL ON** `SeqHyp`. |
| `Series`, `GoldstoneUniform` | `sum_pow_exp_le`, `goldstone_uniform`: scale summation and faster-decaying error; **PROVED CONDITIONAL ON** numerical/rate premises. |
| `KernelDictionary`, `TermKernel` | `termDirect_freeSeq_unit`, `termKernel_nested`: free-flow covariance dictionary and nested kernels; **PROVED** under operator premises. |
| `FineGreenLimits`, `KernelLimits` | `fineGreen_cauchy_coarse`, `tLim_exists_zero`, `tLim_lipschitz`: finite-to-infinite kernel limit and mass continuity; **PROVED** under displayed mass/rate premises. |
| `KernelPointwise`, `KernelHypProof` | `oneScale_pointwise`, `kernelHyp_holds_tLim`: decay and kernel hypothesis for the free flow; **PROVED** under its parameter range. |
| `KernelLarge`, `KernelLargeAssembly` | `kernelHypLarge_holds_two_L4`, `kernelHyp_and_large_holds`: large-mass decay and the common kernel witness used by assembly; **PROVED**. |
| `SumRule`, `GreenIdentification` | `sum_rule_matrix`, `sum_rule_apply`; `KernelHyp.tsum_eq_latticeGreen`: exact Gaussian decomposition and identification with the lattice Green function; **PROVED CONDITIONAL ON** kernel hypotheses in the latter. |
| `MainTerm`, `LemmaThree` | `exists_abs_mainSum_le`, `abs_magJ_sub_one_le`; `abs_rtrLim_le`, `abs_m_sub_magJ_le`: main/remainder estimates and limit bridges; **PROVED CONDITIONAL ON** C-1* fields. |
| `LimAlong`, `BoundsNu` | `exists_limits`, `bullet_one`; `bounds_pos_nu`: projector reconstruction and massive bounds; **PROVED CONDITIONAL ON** Root-F/C-1*/kernel inputs. |
| `ZeroLimit`, `GoldstoneStep` | `tendsto_mag`, `tendsto_mainSum`; `exists_gammaInfty`, `limits_zero`: massless limits and Goldstone estimate; **PROVED CONDITIONAL ON** C-1*/kernels. |
| `Assembly`, `RootCFromFlow` | `rootC_of_rootF_c1Star`, `rootC_of_rootFAndC1Star`: conditional copied Root-C theorem; **PROVED CONDITIONAL ON** `RootFAndC1Star`. |

## 4. Remaining Lean leaves, in dependency order

1. **Start now, generator-neutral, Sonnet, ≤220 lines:** `c1Star_remainder_limit_criterion`: for a family $r_\ell(\nu;x,y)=\sum_j r_{j,\ell}(\nu;x,y)$, assume coefficientwise common-torus agreement, convergence at fixed $j$ as $\ell\to\infty$ and $\nu\downarrow0$, and one summable majorant uniform
in $\ell,\nu\in[0,1]$; conclude the exact `LimAlong (M*L)` and `Tendsto ... (𝓝[>]0)` fields of `C1StarF3`. This proves a limit mechanism, not the physical majorant.
2. **Start now, physical, strong, ≤300 lines per declaration:** `c1Star_running_from_class`: from the actual class flow and its $\nu=0$ continuity clause produce `C1StarF1 L γ₀ cXi β ξ` with $cXi$ chosen before $\beta$; include the free-flow $γ_j,\delta_j,\beta_j$ identification.
`RunningCoefficients`/`RealSequences` supply the downstream arithmetic. The source input is `SMALLFIELD.md` I-7(c), P4 (5.23)–(5.31); its physical producer is **OPEN**.
3. **Start now, physical, strong, ≤300 lines per observable family:** `c1Star_first_source_from_step`: from P9 (H.1), (2.2)–(2.9), the one-mark source coefficients, and the last-step source term, produce `C1StarF2` with $|\mu_j|\le c_*\beta^{-1/2+\rho_1}L^{-j\rho_0}$, continuity, and its $e_m$
estimate. This includes physical support and torus uniformity, not only an abstract marked Mayer lemma. **OPEN**.
4. **Start now for the two-mark/locality lemmas, physical, strong, ≤300 lines each:** `c1Star_second_source_from_step`: from P9 (H.2), (2.10)–(2.20), Proposition 3.1 (3.13), the actual one- and two-mark fluctuation/localization families and last-step large-field terms, produce the two finite-torus
identities and bounds of `C1StarF3`; then use leaf 1 for its limits. The zero longitudinal Gaussian part needs the hard-spin $\lambda=\infty$ identity. **OPEN**.
5. **After 2–4 and the full flow, physical, strong, ≤300 lines for assembly:** `rootFAndC1Star_physical`: establish `RootFAndC1Star d N hN` with the *same* $L\ge3,M,\beta_0$ and one C-1* structure fixed before $\beta$. A standalone `RootFStatement` plus an unrelated C-1* choice does not produce this
conjunction. The full Root-F producer, including $k_f=0$, ordinary steps and last step, is **OPEN**.
6. **After 5, routine, Sonnet, ≤100 lines:** provide `Balaban.Provider.lowTemperature_correlations` by composing leaf 5 with `rootC_of_rootFAndC1Star`, then seal and audit the exact frozen export. This is **OPEN** because leaf 5 is open; do not import the draft root into any earlier leaf.

## 5. Report-on-tension for the author

`RootCStatement` is a separate copied predicate; `rootC_of_rootFAndC1Star` is a valid theorem below the anchors, but it does not certify the frozen export or the physical `RootFAndC1Star` producer. `RootFAndC1Star` asserts C-1* independently of the particular per-$\nu,h$ Root-F family $T$; the
assembly uses both to identify the same model moments, but a physical producer must still return matching $L,M$ and uniform constants. The C-1* remainder limits, mass continuity, free-flow normalization and marked two-function estimates carry mathematical content absent from Root-F. P9 does not
print proofs of the thermodynamic limit or of all the $\nu\downarrow0$ remainder limits; the landed Root-F clause lemmas handle the first, while C-1* currently assumes the second. The frozen source convention $1+\|z\|$ regularizes P9's printed singular $|z|^{2-d}$ at zero; its phase-0 ruling should
remain visible in the audit. None of these observations proposes editing a frozen file.
