# FINALCUT — complex cuts, determinant, and torus agreement

This addresses the remainder of FINALMAP leaf S2 after `Green/FinalCutFamily.lean`. All cited Lean declarations were checked in
the read-only main tree. The scalar operator here is `finalOp`; identifying it with the stopped physical Hessian is P1.

## 1. Which cuts are required

**PROVED.** `Localization.abstract_expansion_on` takes a function analytic and bounded on the open polydisc $|s_P|<e^{\kappa_1}$,
with $\kappa_1\ge1$, and an explicit `LocalityAEOn` premise. It returns connected coefficients at $s\equiv1$ with Cauchy factor
$e^{-(\kappa_1-1)|C|}$. `localization_expansion` specializes this with $\kappa_1\ge4d(2L+1)^d\kappa$ and geometric hypotheses.
Thus the radius in that theorem is $\rho=e^{\kappa_1}>1$; the final application has not supplied a value of $\kappa_1$ or its
analytic/locality/bound premises. The smaller symbol $e^\kappa$ in some `DecParams` theorems is that theorem's own decoupling
rate.

**PROVED.** `Localization.decG` is `Gs G a ν α (extS G s)`: it is a Green family built from a generating set and the cube-cover
`sProd` construction, rather than entrywise multiplication of an arbitrary operator. Its `DecParams` index is `cubeIdx G → ℂ`. The
variant in `Decoupled2Solve.lean` uses a `DecCover` and the same `Gs` construction. Neither definition accepts `finalOp` as an
argument. The localization expansion theorem can be reused for a final analytic function once all its hypotheses are proved;
`decG` cannot be applied to the final Schur complement by changing a type parameter.

**PROVED for real convex weights.** `finalOpCut s` has entries $s(x,y)U(x,y)$, $U=\operatorname{finalOp}$, and `finalOpCut_one`
identifies $s\equiv1$ with $U$. `cutWeight` is a convex combination of same-cell indicators; `finalOpCut_isCoercive` preserves the
gap $g_*=\operatorname{finalGap}(d,L)$, while `finalOpCut_resolvent_decay`, `finalOpCut_sqrt_decay`, and
`finalOpCut_resolvent_eq_on` give real-cut decay and locality. The file states no complex-cut or determinant result.

**OPEN design.** For a partition $p(x)$ and complex cube parameters, one possible family is $U_s(x,y)=w_s(x,y)U(x,y)$, where
$w_s(x,y)=1$ if $p(x)=p(y)$ and $w_s(x,y)=s_{p(x)}s_{p(y)}$ otherwise. Then $U_1=U$ and $U_0$ is block diagonal. This is a
proposed definition, not a landed `finalOpDec`. The unqualified formula $s_{p(x)}s_{p(y)}U(x,y)$ also deletes the diagonal at
$s=0$ and does not yield the real convex cut family. Alternatively one must construct a final-operator analogue of the `Gs` cover
family and check its uncut value and factorization.

## 2. The complex weighted estimate

**PROVED.** `Green.WSmall r η E` means both $\sup_x\sum_y|E_{xy}|e^{r d(x,y)}\le\eta$ and $\sup_y\sum_x|E_{xy}|e^{r d(x,y)}\le\eta$. `IsCoercive.add_wSmall` takes $r\ge0$ and concludes that $U+E$ is $(g_*-\eta)$-coercive. The condition $\eta<g_*$
then supplies a positive gap; complex analyticity alone does not.

**PROVED CONDITIONAL ON the proposed family.** Put $0\le r<\delta_0$,
$c_0=\operatorname{finalDecayC}(d,L)$,
$\delta_0=\operatorname{blockDecayRate}(d)$, and
$$S_{\partial}(r)=\max\{\sup_x\sum_{p(y)\ne p(x)}
 |U_{xy}|e^{r d(x,y)},\ \sup_y\sum_{p(x)\ne p(y)}
 |U_{xy}|e^{r d(x,y)}\}.$$
From `finalMass_entry_decay` and `ballSum_L1Torus`,
$S_{\partial}(r)\le c_0\operatorname{ballConst}(d,\delta_0-r)$,
uniformly in torus size and $k$ under their stated mass window.
For $|s_P|<\rho$, $|w_s-1|\le\rho^2+1$, hence
$$\operatorname{WSmall}(r,\eta(\rho),U_s-U),\qquad
\eta(\rho)=(\rho^2+1)S_{\partial}(r).$$
Centering instead at the real block cut $U_0$ gives $\rho^2S_{\partial}$.
Both are sufficient *only if* the resulting $\eta<g_*$.
The proposed $(\rho^2-1)$ factor is **REFUTED**: at $s=0$ the
difference from $U_1$ equals the full cross-block matrix even as
$\rho\downarrow1$.

**REFUTED as an automatic block-size estimate.** Adjacent blocks
have sites at distance one. Entry decay alone gives no lower bound
$d(x,y)\ge M$ for cross-block entries and therefore no factor
$e^{-\delta_0M}$ in $S_{\partial}$. Increasing the block side
$M$ does not fix the displayed perturbation argument.
For an *additional* separation hypothesis $d(x,y)\ge M$ whenever
a changed entry is nonzero, and $0<\sigma<\delta_0-r$, one obtains
$$\eta_M(\rho)\le(\rho^2+1)c_0\operatorname{ballConst}(d,\sigma)
 e^{-(\delta_0-r-\sigma)M}.$$
This follows by splitting $e^{-(\delta_0-r)d}$ into its $M$ factor
and $e^{-\sigma d}$, then using the ball sum in both directions.
It suffices that
$M>\log((\rho^2+1)c_0\operatorname{ballConst}(d,\sigma)/g_*)/(\delta_0-r-\sigma)$, when the logarithm is positive.
Neither this separation nor this threshold has been identified with
P7 §4's last-step block choice. The P7 argument on pp. 531–533
invokes P5/P6 for the last fluctuation and does not supply this lemma.

**PROVED CONDITIONAL ON a uniform `WSmall` bound below $g_*$.**
`finalPert_resolvent_decay` gives invertibility of $U_s+t$ for
$t\ge0$ and entries bounded by
$2/(g_*-\eta+t)\,e^{-r' d(x,y)}$, where
$r'=\operatorname{ctRate}(c_0+\eta,\min(\delta_0,r),g_*-\eta,\operatorname{ballConst}(d,\min(\delta_0,r)/4))$.
`finalPert_inverse_decay` is $t=0$ and `finalPert_sqrt_decay`
gives $2/\sqrt{g_*-\eta}\,e^{-r'd(x,y)}$.
`finalPert_analytic_inverse` handles entrywise analytic families
on finite-dimensional parameter spaces. `finalPert_analytic_sqrt`,
`finalPert_hessC_inv_analytic`, and `finalPert_hessC_sqrt_analytic`
state one-complex-parameter analytic results on an open set, with
the latter two also varying $h$ where $h\cdot h\ne0$.
A polydisc version of the inverse follows by finite-dimensional
matrix inversion; a joint polydisc square-root theorem still needs
to be packaged from the resolvent integral and uniform bounds.

## 3. Determinant and localization

**PROVED CONDITIONAL ON a uniform `WSmall` bound below $g_*$.** A finite matrix family $s\mapsto U_s$ with polynomial entries has holomorphic
determinant. The weighted bound gives `IsUnit (U_s+t)` for all $t\ge0$ by `finalPert_resolvent_decay`, so $\det U_s\ne0$ on the polydisc.
Since a polydisc is simply connected, it admits a holomorphic $\log\det U_s$ fixed by its value at $s=1$, and hence a single
holomorphic branch $\exp[-\tfrac12\log\det U_s]$. This is a mathematical deduction, **not** a landed final-cut theorem.
`analyticOnNhd_logMat_fam` is a landed one-parameter matrix-log consumer under `ResOK` and `RectAt`; its multivariable final
specialization and root-normalization identity remain **OPEN**. `pdSqrtInv_det_pow` in `Green/GaussianChangeGeneral.lean` concerns real positive
definite Gaussian changes, not this complex branch.

**REFUTED direct reuse.** `decLog` is built from the step-specific `decCov` and generating set; `rootTraceBg` is a rooted trace of
that step family. `DetExpansionLocC` is typed to `StepSetting`, `BgData`, and its `rootTrace`, with explicit bound, anchor,
`local_resDep`, and analytic chart fields. It is an interface model, not a constructor for the final operator. A final determinant
expansion needs a new rooted trace, exact sum identity, open-chart bound, locality, and decay of its connected cut differences. A
nonzero determinant by itself gives none of those support properties.

## 4. Finite range and nonwinding tori

**PROVED.** `finalOpCut_resolvent_eq_on` compares two *same-torus* real convex cuts whose weights agree on $X^2$ and vanish across
$X\mid X^c$. It is not a cross-torus identity. `genKernelTrunc_eq_zero` says that a supplied range-graded kernel vanishes beyond
its truncation range; `gen_trunc_tail_le` gives a row-tail bound. Neither constructs grades of the final inverse square root or
asserts equality of grades on different tori. `kf0CR_torus_eq` and `sum_range_kwAdjG_pow_torus_eq` obtain exact agreement from the
specific nearest-neighbor walk powers and explicit nonwinding inequalities. Their operators are not `finalOp`.

**OPEN target.** Construct coefficients $c_n^{(m)}(x,y)$ for the final cut covariance or inverse square root such that (i) their
sum is the desired kernel; (ii) $c_n^{(m)}(x,y)=0$ when $d_m(x,y)>n$; (iii) weighted row and column sums and tails are uniform in
$m$; and (iv) for a common integer lift of the operator, cuts, and endpoints inside a region with a halo of radius $R$ that does
not wind in either torus, $c_n^{(m)}(x,y)=c_n^{(m')}(x',y')$ for every $n\le R$. Then the truncations agree termwise. A Neumann
expansion of $U_m$ alone is insufficient: $U_m$ is itself a Schur complement with torus-dependent long-range entries. One first
needs a common local expansion of that Schur complement (or a compatible infinite-lattice construction), plus the determinant's
loop analogue. Exact nonwinding agreement of the final $p_X$ additionally needs the physical local interaction, characteristic,
and Mayer regrouping.

## 5. Leaves, in dependency order

| Leaf | Exact target; inputs | Size / worker / status |
| --- | --- | --- |
| `finalCutComplexSpec` | Define $U_s$, show $U_1=U$, $U_0$ block diagonal, analyticity and covariance; `finalOpCut`, cut geometry. | ≤130 lines; Sonnet; **OPEN**, generator-neutral, start now. |
| `finalCutWeightedBound` | Prove $\operatorname{WSmall}(r,(\rho^2+1)S_\partial,U_s-U)$ and explicit ball bound; `finalMass_entry_decay`. Include a test of $\eta<g_*$ for the chosen family. | ≤190 lines; strong; **OPEN**, generator-neutral, start after spec. |
| `finalCutComplexResolvent` | Under $\eta<g_*$ prove gap, resolvent, inverse and square-root decay on the cut polydisc; `IsCoercive.add_wSmall`, `finalPert_resolvent_decay`, `finalPert_sqrt_decay`. | ≤180 lines; Sonnet after weighted bound; **PROVED CONDITIONAL ON** that open inequality. |
| `finalCutDetLog` | Holomorphic nonzero determinant, normalized log branch, bounded rooted trace and connected cut differences; `analyticOnNhd_logMat_fam` is one-variable guidance. | ≤260 lines; strong; **OPEN**, generator-neutral after complex resolvent. |
| `finalCutTorusGrades` | Construct common range grades for final Schur complement and cut inverse/square root, uniform tail and equality on nonwinding lifts; `genKernelTrunc_eq_zero`, `kf0CR_torus_eq` only supply templates. | ≤300 lines per split; strong; **OPEN**, generator-neutral, start the Schur-complement grades now. |
| `finalCutLocalWrapper` | Feed analytic determinant and covariance, bounds, locality, and torus grades to `abstract_expansion_on`; check the actual $e^{\kappa_1}$ radius and connected support. | ≤260 lines; strong; **OPEN**, generator-neutral after prior leaves. |
| `finalCutPhysicalJoin` | Identify the physical Hessian and cutoff, include inherited class interactions and nonempty-region density, then prove P7 §4 final $p_X$. | ≤300 lines per split; strong; **OPEN**, waits for FINALMAP P1–P5. |

The real convex cut is a valid base point, but no landed theorem puts its final-operator family on the large complex polydisc
required by the localization expansion. The missing estimate is quantitative; the claimed automatic $M$ gain is false for adjacent
blocks.
