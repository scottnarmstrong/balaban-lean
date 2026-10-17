# Root-C from Root-F: exact deduction and its missing physical input

**Verdict (17 October 2026).** The fixed-positive-field thermodynamic limits of the one- and two-point functions **do follow from the two-torus clause of Root-F** and are already proved in the landed Lean files. The limit as $\nu\downarrow0$, the Goldstone coefficient, and the identification of that coefficient with the running flow **do not follow from the frozen Root-F statement alone**. They follow from the additional observable interface `C1Star`, for which the landed theorem `Balaban.Correlations.rootC_of_rootFAndC1Star` already proves the whole copied Root-C proposition. No landed theorem produces `C1Star` from Root-F or from the physical RG construction. Thus the remaining work is a physical, scale-resolved input, not a further analytic consequence of the two-torus clause. The frozen Root-C and Root-F declarations and their provider files still have `by sorry` / empty providers.

This note treats the sources and landed files as read-only. The audit snapshot is Balaban commit `4c96d5af9a24b6b009e5f2f200cb43879c0eae3e`; the frozen Root-C and Root-F file SHA-256 hashes are respectively `a6f0820076a55429236039371d20166bbe59ab258c93dddd89c3bd8af228de12` and `21833bea3211257ac51d0879ef9f692acb0021fb04e792375cf5257104380e40`. The central landed files `ThermoLimit.lean`, `C1Star.lean`, `Assembly.lean`, and `RootCFromFlow.lean` have hashes `5b43ea04c42814e6cea5c37804981e4a0ba4f35b519e93d1a327c5ffadc87409`, `37bdffd07567bcfff63571d3f90a0536a5d7fd0a4f8ab8caa372fae2f3e291d3`, `09c476499efc9df14cf7de2ec1ecf0d2f67f5eccd22d4558c48035bcd08d7dfc`, and `652955500d7371fe70754079c7ee3ce6b1a5142b34a23d8c28dd8e8b4b0a52c2`. This is a focused source/proof audit; no Lean source was changed or built.

## Statements and normalization

Let $d\ge3$, $N\ge2$, $\beta$ large, $0<\nu\le1$, $h\in S^{N-1}$, and let $x,y\in\mathbb Z^d$. Write $|x|=\|x\|_\infty$, $p=d-2$, and
\[
 P_{\rm tr}=I-h\otimes h,\qquad P_{\rm lg}=h\otimes h,
 \qquad -\Delta G=\delta_0,\quad G(x)\longrightarrow0\quad(|x|\to\infty).
\]
The last equation means $\sum_{\mu=1}^d(2G(x)-G(x+e_\mu)-G(x-e_\mu))=\delta_{x0}$, exactly as in the frozen Root-C. The uniqueness of $G$ is landed as `Balaban.LatticeGreen.latticeGreen_existsUnique`.

The **exact frozen Root-C conclusion** says that there are $\beta_0,c,c',\rho_0,\rho_1$ and an integer $q\ge2$, chosen before $\beta$, with $c,c',\rho_0,\rho_1>0$, $\rho_1<1$, such that for every $\beta\ge\beta_0$ there are functions $m(\nu)$, $G_{\rm tr}(\nu,z)$ and $G_{\rm lg}(\nu,z)$. Along *all* tori whose side is divisible by $q^{n_0}$ (with $n_0$ depending on $\nu,h,x,y,\varepsilon$), their one-point functions approach $m(\nu)h$ and their truncated two-point functions approach $G_{\rm tr}(\nu,x-y)P_{\rm tr}+G_{\rm lg}(\nu,x-y)P_{\rm lg}$. Further,
\[
 |m(\nu)-1|\le c\beta^{-1+\rho_1},\qquad
 |G_{\rm tr}(\nu,z)|,|G_{\rm lg}(\nu,z)|
 \le c(1+|z|)^{-p}e^{-c'\sqrt\nu|z|}.                 \tag{C+}
\]
There are limits $m_0,G_{{\rm tr},0}(z),G_{{\rm lg},0}(z)$ as $\nu\downarrow0$ and a $\gamma>0$ with
\[
 |\gamma-1|\le c/\beta,\quad
 \left|G_{{\rm tr},0}(z)-\frac{m_0^2}{\beta\gamma}G(z)\right|
 \le c(1+|z|)^{-(p+\rho_0)},\quad
 |G_{{\rm lg},0}(z)|\le c(1+|z|)^{-(p+\rho_0)}.        \tag{C0}
\]
This is `Balaban.Correlations.RootCStatement` in `Correlations/RootCStatement.lean`, a copy of the type of `Balaban.lowTemperature_correlations` in the frozen file. The frozen statement gives an **absolute** remainder bound. Calling it a relative $|z|^{-\rho_0}$ error requires a lower bound on $G(z)$ and gives, with the constants of (C0), a relative constant that can grow with $\beta$; see below.

The **exact operative Root-F clauses** (`Balaban.Correlations.RootFStatement`, copied from `Balaban.logPartition_multiscale`) choose $\delta>0$; for *each* $\kappa,c_9>0$ choose $L\ge2$, $M\ge1$, $\beta_{0,F}$; then, for every $\beta\ge\beta_{0,F}$ and every $0<\nu\le1,h$, choose $k_f$ and a family $T_j^\ell(x,X;g)$. The stopping inequalities are
\[
 L^{k_f}\sqrt\nu\le L,\qquad \tfrac12\le L^{k_f+1}\sqrt\nu.
\]
On $ML^{k_f+1}\mid\ell$, the terms have polymer support, locality, analyticity for $\|g\|_1<1$, and, for $\|g\|_1\le1/2$,
\[
 \|T_j^\ell(x,X;g)\|\le c_9 L^{-j\theta}
 \exp\{-\kappa |X|/(ML^j)^d\},\qquad
 \theta=p/2+\delta.                                       \tag{F-bnd}
\]
The principal logarithm of $Z_\ell(g)/Z_\ell(0)$ is $\langle g,h\rangle+\sum_{j,x,X}\langle g(x),T_j^\ell(x,X;g)\rangle$. Its two-torus clause equates corresponding individual terms on images of a common finite set in both quarter boxes. **Every choice of $T$ is made after $\nu$**; the clause compares two tori at one and the same $\nu$. It states no continuity, limit, or scale identification across different $\nu$.

## What the landed theorems actually supply

All names in this table are exact Lean names, with their containing module indicated. The table distinguishes unconditional mathematics about abstract kernels, deductions from Root-F clauses, and additional hypotheses.

| Step | Landed declaration | Input and output |
|---|---|---|
| Differentiate the source identity | `Balaban.Correlations.onePoint_eq_of_clauses`, `twoPointTruncated_eq_of_clauses` (`Identity`) | `RootFTorusClauses`; exact one-point term sum and two-point derivative sum at $g=0$. The abstract source-derivative tool in the observable layer is `Balaban.Observables.fderiv_Fcomp_zero` (`LayerFirstOrder`). |
| Count and localize polymers | `card_polymersAt_blockNumber_le`, `sum_polymersAt_pow_le` (`PolymerCount`); `blockNumber_ge_of_not_subset` (`Tail`); `value_agree`, `fderiv_agree` (`Agreement`) | Geometric summability, a block-count lower bound for polymers leaving a box, and agreement of local terms and derivatives. |
| Bounds at fixed $\nu$ | `abs_onePoint_sub_le`, `exists_abs_twoPointTruncated_le` (`Estimates`); `abs_limit_onePoint_sub_le`, `exists_abs_limit_twoPoint_le` (`Consequences`) | $|\langle\phi_i\rangle-h_i|\le3c_9$ and decay with exponent $\theta=p/2+\delta$ at finite and infinite volume. `onePoint_close_of_rootF` chooses $c_9$ to make the first bound arbitrarily small at sufficiently large $\beta$. |
| **Thermodynamic limit** | `onePoint_cmp`, `twoPoint_cmp`, `onePoint_tendsto_along_multiples`, `twoPoint_tendsto_along_multiples` (`ThermoLimit`); `exists_limits`, `bullet_one` (`LimAlong`) | **Already proved** from `RootFClauses` for each fixed positive $\nu$; rotation covariance supplies the scalar $m,G_{\rm tr},G_{\rm lg}$ and every unit $h$. |
| Running and observable quantities | `gammaR`, `deltaR`, `betaR`, `magJ`, `mainTr`, `C1StarF1`, `C1StarF2`, `C1StarF3`, `RootFAndC1Star` (`C1Star`); `gammaR_eq`, `betaR_eq`, `SeqHyp.gammaR_bounds` (`RealSequences`) | Defines and assumes the physical scale decomposition. **No theorem produces `C1Star` from `RootFStatement`.** `Balaban.LargeField.StopIndex.kStop_succ_C1Star` (`Flow/StopIndex`) supplies the scale bounds from a `RunningHyp`, only one part of this interface. |
| Physical observable layer, conditional | `Balaban.Observables.Mk_eq_dictionary` (`LayerDictionary`), `lemma_2_1` (`LayerStructure`), `Mk_const`, `Gk_longitudinal` (`LayerConst`), `mFactor_sub_one_le`, `sum_R_le` (`LayerSums`), `gaussian_main_term` (`SecondOrderStep`) | Pieces of P9's one-/two-point structure, under their own observable-layer hypotheses. `IsObs` (`LayerDef`) and `IsObs2` (`LayerV2`) are draft interfaces; none is a physical producer of the complete `C1Star` data. The `ImprovedFirst`, `ImprovedLemma`, `SecondOrderSums`, and related `Observables` files prove local estimates conditional on their classes. |
| Infinite-volume C-1* decomposition | `KernelHypLarge.limAlong_mainTr` (`MainTerm`); `gtr_eq`, `glg_eq`, `abs_m_sub_magJ_le`, `abs_rtrLim_le` (`LemmaThree`) | The finite-torus C-1* formulas pass to the limits from Root-F and the Gaussian kernel limit. The zero-$\nu$ remainder limit is still a field of `C1StarF3`. |
| Positive-field canonical estimates | `bounds_pos_nu` (`BoundsNu`) | (C+) from C-1*, the Gaussian kernel bounds, and the fixed-$\nu$ limits. |
| Gaussian sum rule | `sum_rule_apply_abs_le` (`SumRule`), `KernelHyp.tsum_eq_latticeGreen` (`GreenIdentification`), `kernelHyp_and_large_holds` (`KernelLargeAssembly`) | **Landed**, independent of the physical RG input: $\sum_jt_j^0(x,y)=G(x-y)$. The kernel package covers the mass range needed at the final scale. |
| Zero-field passage | `tendsto_mag`, `tendsto_mainSum` (`ZeroLimit`); `goldstone_uniform` (`GoldstoneUniform`); `exists_gammaInfty`, `limits_zero` (`GoldstoneStep`) | **Landed conditional proof** of (C0), using C-1* continuity and remainder limits. `c1Star_remainder_limit_criterion` (`C1StarLimits`) is a pure dominated-convergence criterion, not a producer of its summands. |
| Whole deduction | `rootC_of_rootF_c1Star_kernelLarge` (`Assembly`), `rootC_of_rootFAndC1Star` (`RootCFromFlow`) | The precise proved implication is `RootFAndC1Star d N hN → RootCStatement d N`, not `RootFStatement d N → RootCStatement d N`. |

`docs/PROGRESS.md` calls “Root-C from Root-F” 30% and lists the thermodynamic limits, $\nu\downarrow0$, and physical inputs as missing. That status describes the absence of a physical producer; as a **conditional** proposition, the thermodynamic and zero-field arguments above are landed. The difference between these two meanings of “done” matters.

## Proof I: the fixed-$\nu$ infinite-volume limits from Root-F

Fix $\beta,\nu,h,k_f,T$ and admissible sides $\ell,\ell'$. Let $s_J=ML^{k_f+1}$, let $X_0\ge\max_\mu(|x_\mu|,|y_\mu|)$, and put $R=s_JK+X_0+1$. Suppose $4R\le\ell,\ell'$. Differentiate the exact Root-F source identity at $g=0$. `onePoint_eq_of_clauses` gives
\[
 \langle\phi_i(x)\rangle_\ell=h_i+
 \sum_{j=1}^{k_f+1}\sum_{X\ni x}T_j^\ell(x,X;0)_i.       \tag{1}
\]
`twoPointTruncated_eq_of_clauses` gives the sum over $j,X$ of
$D_{y,k}T_j^\ell(x,X;0)_i+D_{x,i}T_j^\ell(y,X;0)_k$. Terms whose polymer $X$ stays in the image of the integer box $|w_\mu|<R$ agree on the two tori by `value_agree` and `fderiv_agree`. The derivative agreement follows by applying term agreement to $g=t\,\mathbf1_{(y,k)}$ and differentiating at $t=0$; locality makes terms outside $X$ irrelevant.

Every polymer containing $x$ and leaving that box has at least $K+1$ scale-$j$ blocks (`blockNumber_ge_of_not_subset`). At $\kappa\ge\kappa_*=2\log(8d^2)$, polymer counting and (F-bnd) give per scale the tail bounds
\[
 \left\|\sum_{X\text{ leaves box}}T_j^\ell(x,X;0)_i\right\|
 \le 2c_9L^{-j\theta}2^{-(K+1)},\qquad
 \left\|\sum_{X\text{ leaves box}}D T_j^\ell\right\|
 \le 8c_9L^{-j\theta}2^{-(K+1)}.              \tag{2}
\]
The second bound includes the two source derivatives and the Cauchy radius. Since $d\ge3$, $\theta\ge1/2$, $L\ge2$,
\[
 \sum_{j=1}^{k_f+1}L^{-j\theta}
 \le\sum_{j=1}^\infty2^{-j/2}<3.                    \tag{3}
\]
Thus the one-torus tails have norms at most $6c_9 2^{-(K+1)}$ and $24c_9 2^{-(K+1)}$. Subtracting two tori cancels the box terms and gives the **exact landed comparison constants**
\[
 |m_{\ell,i}(x)-m_{\ell',i}(x)|\le12c_9 2^{-(K+1)},\qquad
 |G_{\ell,ik}(x,y)-G_{\ell',ik}(x,y)|\le48c_9 2^{-(K+1)}. \tag{4}
\]

Set $q_C=ML\ge2$. For any $\varepsilon>0$, choose $K$ so that $48c_9 2^{-(K+1)}<\varepsilon$ (or $12c_9 2^{-(K+1)}<\varepsilon$ for one point), and set
\[
 n_0=\max\{k_f+1,,4(s_JK+X_0+1)\}.                \tag{5}
\]
If $q_C^{n_0}\mid\ell$ and $\ell>0$, then $s_J\mid\ell$. Also $q_C^{n_0}\le\ell$ and $n_0<q_C^{n_0}$, whence $4R\le\ell$; similarly for $\ell'$. Equation (4) is a Cauchy condition for the sequence of sides $q_C^n$. Completeness of $\mathbb R$ gives a limit. Comparing a general side $q_C^{n_0}\mid\ell$ with the sides $q_C^n$ and letting $n\to\infty$ gives the same limit for **every** sufficiently divisible torus; this is `exists_tendsto_along_multiples`. In the formal definition `LimAlong`, the final triangle inequality uses $\varepsilon/2$ for the Cauchy comparison and $\varepsilon/2$ for the reference side, so the result is strict $<\varepsilon$.

Finally `exists_limits` extracts the axial scalar limits: $m$ from the coordinate along $h=e_0$, $G_{\rm tr}$ from a perpendicular diagonal component, $G_{\rm lg}$ from the parallel component. `bullet_one` uses lattice translation and $O(N)$ covariance to recover any unit $h$. In the final $\varepsilon$ estimate, $|h_i|\le1$, $|h_ih_k|\le1$, and $|\delta_{ik}-h_ih_k|\le1$. Hence the one-point error is $<\varepsilon/2$ and the matrix-component error is at most the sum of two scalar errors, each $<\varepsilon/2$. This completes the first bullet of frozen Root-C **at every fixed $\nu>0$**. It also proves the raw component bounds $|m-1|\le3c_9$ and $|G_{ik}(z)|\le Cc_9(1+|z|)^{-\theta}e^{-\kappa\sqrt\nu|z|/(4ML^2)}$ after taking limits (`Consequences`). The sharper exponent $p=d-2$ and the $\beta$ power of (C+) require C-1*.

## Why the remaining assertions cannot be deduced from Root-F alone

The quantifier issue is decisive: for each $\nu$, Root-F supplies some $k_f(\nu)$ and $T(\nu)$, with only a bound uniform in $\nu$ and agreement across tori *at that $\nu$*. A uniform bound on a family of functions need not give its limit at $0$, and a bound on the full logarithm does not identify the coefficient of a particular Gaussian covariance.

Here is a concrete refutation of an **abstract** implication from the Root-F clauses. It is deliberately a different hard-spin measure, so it is not a counterexample to the true physical O$(N)$ theorem. For each $\beta,\nu,h$ put independent spins $\phi_x\in\{h,-h\}\subset S^{N-1}$ with
\[
 \Pr(\phi_x=-h)=p_{\beta,\nu}:=\frac{e^{-\beta}}8(1+\sin(\log\nu)),
 \qquad \Pr(\phi_x=h)=1-p_{\beta,\nu}.                \tag{6}
\]
Their normalized generating function is $\prod_x[(1-p)e^{t_x}+pe^{-t_x}]$, $t_x=g(x)\cdot h$. For $|t|<1$ write
\[
 \log[(1-p)e^t+pe^{-t}]=t+t\,b_p(t),\qquad
 b_p(t)=\int_0^1\frac{-2p e^{-2st}}{1-p+p e^{-2st}}\,ds. \tag{7}
\]
If $p_{\beta,\nu}(e^2+1)\le1/2$, then the denominator has modulus at least $1/2$ for $|t|\le1$, so $|b_{p_{\beta,\nu}}(t)|\le4e^2p_{\beta,\nu}$. The integral expression (or its power series) is analytic there; extend it arbitrarily as the same function of $t$ outside the unit disc, where Root-F asks for neither analyticity nor a bound. On the $\ell^1$ source unit ball, $\sum_x|t_x|<1$ and the correction has modulus $\le4e^2p_{\beta,\nu}$. For $\beta$ large, the imaginary part of the whole exponent has magnitude $<1+4e^2p_{\beta,\nu}<\pi$; hence the principal logarithm equals the displayed exponent. Take $L=2,M=1,\delta=1$; put the term $b_{p_{\beta,\nu}}(t_x)h$ at $j=1$ on the unique scale-one cube containing $x$ and put every other term to zero. Those cubes are polymers; the term is local, analytic, and agrees on corresponding cubes of sufficiently large tori. Its norm is at most $4e^2p_{\beta,\nu}\le(e^2/2)e^{-\beta}$. For **each** $\kappa,c_9>0$, choose $\beta_0$ so that $(e^2/2)e^{-\beta_0}\le c_9 2^{-\theta}e^{-\kappa}$; then (F-bnd) holds for every $\beta\ge\beta_0$ and every $\nu$. A stopping index $k_f(\nu)$ exists by choosing the integer scale at which $2^{k_f+1}\sqrt\nu$ first reaches $1/2$; if it is already above $1/2$, choose $k_f=0$. This also satisfies $2^{k_f}\sqrt\nu\le2$. Thus all **structural** Root-F estimates and the two-torus agreement can coexist with
\[
 m(\nu)=1-2p_{\beta,\nu}
 =1-\frac{e^{-\beta}}4(1+\sin\log\nu),              \tag{8}
\]
which has no limit as $\nu\downarrow0$. For example, along $\nu_n=e^{-2\pi n-\pi/2}$ and $\nu'_n=e^{-2\pi n-3\pi/2}$ its two subsequential limits differ by $e^{-\beta}/2$. The family in (6) is analytic for every $\nu>0$ and uses actual unit-length spins. It lacks the specified nearest-neighbor Gibbs factor, precisely the physical input that Root-F's abstract bounds do not encode. An even simpler abstract obstruction to the Goldstone coefficient is the deterministic measure $\phi_x=h$: it has $T=0$ and all Root-F structural clauses, while its transverse covariance is zero.

Consequently the nearest justified statement under `RootFStatement` alone is the fixed-$\nu$ limit and its $\theta$ decay in Proof I. It is mathematically invalid to assert either a zero-field limit or $\gamma_\infty$ from those clauses without further assumptions. The refutation survived checking the full $\kappa,c_9,\beta_0,\nu$ quantifier order and the principal-log branch. It does not refute the physical theorem about the frozen `partitionFunction`.

## Proof II: the full conditional deduction, with constants

This is the proof of the nearest complete **true** statement, the landed `rootC_of_rootFAndC1Star`. It states explicitly what a physical producer must supply.

Assume `RootFAndC1Star d N hN`, which ties the same $L\ge3,M\ge1$ to the Root-F clauses at $\kappa=\kappa_*$ and $c_9=1$ and to `C1Star`. The extra fields of `C1Star` are $a$ in the stated free-flow range, $0<\gamma_0\le1/2$, $c_*,c_\xi,c_P>0$, $0<\rho_0\le p$, $0<\rho_1<1$, $J(\nu)\to\infty$, and, for every large $\beta$, real running coefficients $\xi(\nu)_j$, first-order coefficients $\mu_j(\nu;x)$, and remainder families. Its three operative requirements are:

1. **F1:** with $q_r=L^{-2\gamma_0}\in(0,1)$,
   $\|\xi(\nu)_j\|_\infty\le[c_\xi/(4\beta)]q_r^{j+1}$ for $0\le\nu\le1$; every fixed $j$ has a limit $\xi(0)_j$ as $\nu\downarrow0$.
2. **F2:** $|\mu_{j+1}(\nu;x)|\le c_*\beta^{-1/2+\rho_1}L^{-(j+1)\rho_0}$, each coefficient is continuous at $0$, and $|m(\nu)-m_{J(\nu)}(\nu;x)|\le c_*\beta^{-2}L^{-2J(\nu)p}$ after the torus limit, where
   $m_J(\nu;x)=1-\sum_{j<J}\beta_j(\nu)^{-1/2}\mu_{j+1}(\nu;x)$.
3. **F3:** after the torus limit,
   \[
   G_{\rm tr}(\nu,x-y)=m_J(\nu;x)m_J(\nu;y)
    \sum_{j<J}\frac{t_j^{\nu\delta_j(\nu)}(x,y)}{\beta\gamma_j(\nu)}
    +r_{\rm tr}(\nu;x,y),\qquad
   G_{\rm lg}(\nu,x-y)=r_{\rm lg}(\nu;x,y),              \tag{9}
   \]
   where $r_{\rm tr},r_{\rm lg}$ have limits at $\nu=0$ and the **exact Lean hypothesis**, slightly weaker than the prose summary in `CORRELATIONS.md`, is
   \[
   |r_{\rm tr}(\nu;x,y)|,|r_{\rm lg}(\nu;x,y)|
    \le c_*[(1+|x-y|)^{-(p+\rho_0)}+\nu^{p/2}]
       e^{-c_P\sqrt\nu|x-y|}.                            \tag{10}
   \]
   The finite-torus equality, its limit along $(ML)^n$, and the zero-field remainder limit are clauses of `C1StarF3`; the first of those remainder limits can also be deduced once the finite-torus equality, Proof I, and kernel convergence are known.

The independent Gaussian package `kernelHyp_and_large_holds` supplies $t_j^\mu(x,y)$ and $t_j^0(x,y)$, with
\[
 |t_j^\mu(x,y)|\le C_G L^{-jp}e^{-\delta_G|x-y|/L^j}       \tag{11}
\]
through the mass range $\mu L^{2(j+1)}\le2L^4$, the limit $t_j^\mu\to t_j^0$ at $\mu=0$, and the torus-to-infinite-volume limit. It also supplies the free-flow sum rule. These are the `KernelHyp` and `KernelHypLarge` assumptions of `Assembly`, subsequently discharged by `KernelLargeAssembly`.

For constants, define
\[
 r_0=L^{-\rho_0},\quad K=\sqrt2c_*\frac{r_0}{1-r_0},\quad
 A=\frac{c_\xi q_r}{2(1-q_r)},\quad
 \rho=\min(\rho_0,2\gamma_0),\quad
 c'=\min\left(\frac{c_P}{2},\frac{\delta_G}{2L^2}\right). \tag{12}
\]
Here $K,A\ge0$, $\rho,c'>0$. Choose $\beta_0$ at least the Root-F and C-1* thresholds and $1$ and $2c_\xi q_r/(1-q_r)$. Then
$c_\xi q_r/[\beta(1-q_r)]\le1/2$, so `SeqHyp` applies. `RealSequences` gives
\[
 \gamma_j(\nu)=\prod_{i<j}(1+\xi(\nu)_i(2))^{-1}\in[1/2,2],\quad
 \delta_j(\nu)\in[1/2,2],\quad
 \beta_j(\nu)=\beta L^{jp}\gamma_j(\nu).       \tag{13}
\]
The stop bound $L^{J(\nu)}\sqrt\nu\le L^2$ implies
$\nu\delta_j(\nu)L^{2(j+1)}\le2L^4$ for $j<J(\nu)$; this is why the large-mass Gaussian kernel theorem is needed.

**Magnetization and its physical identification.** By (13),
\[
 \left|\beta_j(\nu)^{-1/2}\mu_{j+1}(\nu;x)\right|
 \le\sqrt2c_*\beta^{-1+\rho_1}
 L^{-jp/2}L^{-(j+1)\rho_0}
 \le\sqrt2c_*\beta^{-1+\rho_1}r_0^{j+1}.         \tag{14}
\]
Summing the geometric majorant gives
$|m_J(\nu;x)-1|\le K\beta^{-1+\rho_1}$. The pointwise coefficient limits and $J(\nu)\to\infty$ allow dominated convergence in (14):
\[
 m_0=1-\sum_{j=0}^\infty
       \beta_j(0)^{-1/2}\mu_{j+1}(0;0),\qquad
 |m_0-1|\le K\beta^{-1+\rho_1}.                       \tag{15}
\]
The finite-$J$ error tends to zero because $c_*\beta^{-2}L^{-2Jp}\to0$. Thus the $m_0$ in (15) is **the limit of the physical one-point function**, not merely a formal flow parameter (`tendsto_mag`, via `abs_m_sub_magJ_le`). In particular $|m_0|\le1+K$ for $\beta\ge1$; increasing $\beta_0$ gives $m_0\ge1/2$ if a relative asymptotic is desired.

**The two-point limit.** For fixed $j,x,y$, the coefficient $[\beta\gamma_j(\nu)]^{-1}$ converges to $[\beta\gamma_j(0)]^{-1}$, and $\nu\delta_j(\nu)\downarrow0$ in the sense of a positive argument tending to zero. The Gaussian term in (9) converges to $t_j^0(x,y)$. From (11), (13), and $e^{-u}\le1$ for $u\ge0$,
\[
 \left|\frac{t_j^{\nu\delta_j(\nu)}(x,y)}{\beta\gamma_j(\nu)}\right|
 \le\frac{2C_G}{\beta}L^{-jp},\qquad
 \sum_{j\ge0}\frac{2C_G}{\beta}L^{-jp}
 =\frac{2C_G}{\beta(1-L^{-p})}<\infty.          \tag{16}
\]
Again $J(\nu)\to\infty$ and Tannery's theorem give
\[
 S_0(x,y):=\lim_{\nu\downarrow0}
 \sum_{j<J(\nu)}\frac{t_j^{\nu\delta_j(\nu)}(x,y)}{\beta\gamma_j(\nu)}
 =\sum_{j\ge0}\frac{t_j^0(x,y)}{\beta\gamma_j(0)}.   \tag{17}
\]
Equations (9), (15), (17), and the **assumed** limits of $r_{\rm tr},r_{\rm lg}$ identify the physical zero-field functions as
\[
 G_{{\rm tr},0}(z)=m_0^2 S_0(z,0)+r_{{\rm tr},0}(z,0),
 \qquad G_{{\rm lg},0}(z)=r_{{\rm lg},0}(z,0).       \tag{18}
\]
This is `tendsto_mainSum` and the limit part of `limits_zero`. At each fixed $z$, (10) passes to $\nu=0$: $\nu^{p/2}\to0$ because $p>0$, and $e^{-c_P\sqrt\nu|z|}\le1$. Consequently
\[
 |r_{{\rm tr},0}(z,0)|,|r_{{\rm lg},0}(z,0)|
 \le c_*(1+|z|)^{-(p+\rho_0)}.                     \tag{19}
\]
The positive-field version of (10) is converted to (C+) by
$\nu^{p/2}e^{-c_P\sqrt\nu r}\le C_d(1+r)^{-p}e^{-(c_P/2)\sqrt\nu r}$, where one explicit choice is
$C_d=\epsilon^{-p}$ and $\epsilon=\min\{1,c_P/(2p)\}$. Indeed $s=\sqrt\nu\le1$, $s(1+r)\le1+sr\le\epsilon^{-1}e^{\epsilon sr}$, and $p\epsilon\le c_P/2$. The main sum obeys the landed scale-sum bound $|S_\nu(z,0)|\le(2C_GC_1/\beta)(1+|z|)^{-p}e^{-\delta_G\sqrt\nu|z|/(2L^2)}$, with $C_1$ depending only on $d,L,\delta_G$. Since $|m_J|\le1+K$ and $\beta\ge1$, a sufficient coefficient for (C+) is
\[
 c\ge\max\{c_*+K,\ (1+K)^2(2C_GC_1)+c_*(1+C_d)\}.   \tag{20}
\]
This is `bounds_pos_nu`.

**Green function and $\gamma_\infty$.** The Gaussian sum rule is a separate theorem. If $S_J^\mu(x,y)=\sum_{j<J}t_j^\mu(x,y)$, `sum_rule_apply_abs_le` and the prolongation bound give, for $\mu L^{2J}\le1$,
\[
 |(-\Delta_x+\mu)S_J^\mu(x,y)-\delta_{xy}|
 \le C_P L^{-Jd}.                                  \tag{21}
\]
At fixed $J$ let $\mu\downarrow0$: each term converges, and $\mu S_J^\mu\to0$. Thus $|(-\Delta_x)S_J^0-\delta_{xy}|\le C_PL^{-Jd}$. Equation (11) and the elementary scale sum make $\sum_jt_j^0(x,y)$ absolutely convergent, bounded by $C_GC_1(1+|x-y|)^{-p}$; letting $J\to\infty$ in (21) shows that sum solves the lattice Green equation and decays at infinity. Uniqueness yields
\[
 \sum_{j\ge0}t_j^0(x,y)=G(x-y).                   \tag{22}
\]
This is `KernelHyp.tsum_eq_latticeGreen`, proved from the landed free-flow kernels, not from Root-F's $T_j$.

Set $\gamma_\infty=\lim_{j\to\infty}\gamma_j(0)$, a limit supplied by `GoldBound`/`exists_gammaInfty` from the summable $\xi(0)$. With $A$ in (12),
\[
 |\gamma_\infty-1|\le A/\beta,\qquad A/\beta\le1/4,
 \qquad \gamma_\infty\ge3/4>0.                    \tag{23}
\]
This **identifies** $\gamma$ in frozen Root-C: it is the limit of the physically normalized $\gamma_j=\beta_j/(\beta L^{jp})$, not a coefficient chosen after observing the correlation. `goldstone_uniform` and (11) give the fully quantified comparison, with $C_2$ depending only on $d,L,\gamma_0,\delta_G$,
\[
 \left|S_0(z,0)-\frac1{\beta\gamma_\infty}
       \sum_jt_j^0(z,0)\right|
 \le e^2\frac{A}{\beta^2} C_GC_2
       (1+|z|)^{-(p+2\gamma_0)}.                    \tag{24}
\]
Here $e^2$ means $\exp(2)$, not a new parameter. Algebraically, the $j$th coefficient difference is $|1/(\beta\gamma_j)-1/(\beta\gamma_\infty)|\le e^2(A/\beta^2)q_r^j$; multiplying by (11) replaces $L^{-jp}q_r^j$ by $L^{-j(p+2\gamma_0)}$, whose exponential scale sum is $\le C_2(1+|z|)^{-(p+2\gamma_0)}$. This is P9's (4.18) step in the normalization of the landed `Asymptotics` and `GoldstoneUniform` files.

Combining (18), (19), (22), (24), $m_0^2\le(1+K)^2$, and $\rho=\min(\rho_0,2\gamma_0)$ gives **every term of the final inequality**:
\[
\begin{aligned}
 \left|G_{{\rm tr},0}(z)-\frac{m_0^2}{\beta\gamma_\infty}G(z)\right|
 &\le m_0^2\left|S_0(z,0)-\frac{G(z)}{\beta\gamma_\infty}\right|
       +|r_{{\rm tr},0}(z,0)|\\
 &\le\left[(1+K)^2e^2\frac{A}{\beta^2}C_GC_2+c_*\right]
       (1+|z|)^{-(p+\rho)},\\
 |G_{{\rm lg},0}(z)|&\le c_*(1+|z|)^{-(p+\rho)}.
\end{aligned}                                                     \tag{25}
\]
The weakening from exponents $p+2\gamma_0$ and $p+\rho_0$ to $p+\rho$ is valid because $1+|z|\ge1$. One choice of the **single Root-C constant**, chosen before $\beta$, is the exact one in `Assembly.lean`:
\[
 c=c_*+K+1+(1+K)^2(2C_GC_1)
     +(1+K)^2e^2 A C_GC_2+A+c_*C_d.               \tag{26}
\]
All summands in (26) are nonnegative, so this $c$ dominates (20), (23) after dividing by $\beta$, and (25) using $\beta^{-2}\le1$. Taking $\rho$ as Root-C's exponent and $q_C=ML$ completes `rootC_of_rootF_c1Star_kernelLarge`; `rootC_of_rootFAndC1Star` supplies the kernel package automatically.

**Relative-error qualification.** If one also uses the standard lattice Green lower bound $G(z)\ge a_d(1+|z|)^{-p}$ for $|z|\ge R_d$, and increases $\beta_0$ until $m_0\ge1/2$, then (23) gives $\gamma_\infty\le5/4$ and the leading term is at least $a_d(5\beta)^{-1}(1+|z|)^{-p}$. Dividing (C0) by it gives
\[
 \frac{|G_{{\rm tr},0}(z)-m_0^2G(z)/(\beta\gamma_\infty)|}
 {m_0^2G(z)/(\beta\gamma_\infty)}
 \le \frac{5c\beta}{a_d}(1+|z|)^{-\rho}.          \tag{27}
\]
Thus the frozen absolute statement implies relative decay **for each fixed $\beta$**, with a constant proportional to $\beta$. A relative bound with a constant uniform in all $\beta\ge\beta_0$ would require a stronger $O(\beta^{-1})$ remainder than (C0); it is not the frozen theorem. The lower bound is not among the landed `LatticeGreen` main statements inspected here, so (27) is explicitly conditional on that standard estimate.

## Source fidelity, Lean shape, and what this unblocks

P9 is T. Balaban and M. O'Carroll, *Low Temperature Properties for Correlation Functions in Classical N-Vector Spin Models*, **Communications in Mathematical Physics 199** (1999), 493–520. Theorem 1.1 is on pp. 494–495; the first- and second-derivative formulas (4.8)–(4.9) are on pp. 516–517; the one-point identification (4.10), matrix split (4.11), and hard-spin transverse kernel (4.12)–(4.14) are on pp. 517–518; the $\nu\downarrow0$ dominated-convergence argument and (4.15)–(4.18) are on pp. 518–519. P8 is T. Balaban and M. O'Carroll, *A Simple Method for Correlation Functions via the Effective Actions in the Renormalization Group Framework*, **Annals of Physics 260** (1997), 1–8; its source differentiation method is described on pp. 1–2 and illustrated by (19)–(27) on pp. 5–6. P8 is about the Gross–Neveu model, so it does not supply the missing O$(N)$ physical coefficients. Its PDF text layer is visibly garbled (especially formula symbols); no numerical constant here is attributed to that extraction. The P9 extraction also garbles parts of pp. 494–495 and the last-step bound on p. 517; the exact inequalities above are cited to the landed Lean statements and the readable P9 formulas, not reconstructed from those garbled fragments.

The precise Lean target already proved is:
```lean
Balaban.Correlations.rootC_of_rootFAndC1Star
  (d N : ℕ) (hd : 3 ≤ d) (hN : 2 ≤ N)
  (h : Balaban.Correlations.RootFAndC1Star d N hN) :
  Balaban.Correlations.RootCStatement d N
```
The physical missing bridge is a producer with conclusion `RootFAndC1Star d N hN`, or, given a completed Root-F producer, a theorem adding a `C1Star d N L M hN` for the **same** $L,M$ at $\kappa_*,c_9=1$. Its statement must retain the quantifier order of `C1Star.data`: constants and $L,M$ before $\beta$; for every $\beta$ the scale function, running coefficients, $\mu$, the finite-torus decompositions, and remainder limits for all $0<\nu\le1$. The central unfinished proof obligations are: (i) obtain the physical F2/F3 identities from the observable layer and last-scale integration, including the bound (10), (ii) establish coefficient continuity at $\nu=0$ uniformly enough for (14) and (16), and (iii) establish the zero-field limits of the remainders. Positive-field remainder limits along tori may be proved afterward from (9), Proof I and Gaussian kernel convergence, rather than assumed as separate data. The existence of $\gamma_\infty$ and its $O(\beta^{-1})$ estimate then follows from F1 by (23); $m_0$ follows from F2 by (15). The `L\ge3` requirement of the Gaussian package is also part of the joint producer, whereas frozen Root-F promises only $L\ge2$.

This bridge would unblock the frozen Root-C provider after its statement correspondence and the Root-F provider are sealed; it is **not** unblocked by the landed `Correlations` or `Observables` files alone. Confidence is high in the fixed-$\nu$ limit and the conditional deduction because their proof steps and constants are explicit in the landed files. Confidence is high that Root-F's abstract clauses cannot force the zero-field assertions, by the counterexample. Confidence in a future physical C-1* producer remains open: its scale-resolved hypotheses are exactly the unproved mathematical content, and the garbled source passages do not fill that gap.
---

# Part 2. Producing `C1Star` from the physical RG step

**Scope and verdict.** The missing physical input is exactly `Balaban.Correlations.C1Star` in `Balaban/Correlations/C1Star.lean`, not an unspecified extra estimate. Its three clauses are `C1StarF1`, `C1StarF2`, and `C1StarF3`. The landed `Flow` theorems prove the numerical consequences of a *given* physical coefficient equation and its bounds; the landed `Observables` theorems prove consequences of a *given* `IsObs` layer. Neither set constructs the physical equation, the observable layer after a fluctuation and renormalization step, or the final source derivatives. Consequently the implication “physical RG construction $Rightarrow$ `C1Star`” remains a theorem to prove. The theorem targets below identify the inputs at the level of one step. No use of Root-F's bound on its generic $T_j$ can replace them: that bound has exponent $(d-2)/2+\delta$ and has no coefficient or zero-field parameter data.

## 2.1 Exact content of the Lean interface

Put $p=d-2$, $q_*=L^{-2\gamma _0}$, and $Q=ML$. The structure `C1Star d N L M hN` first chooses, **before** $\beta$, $a,\gamma _0,c_*,c_\xi,c',\rho _0,\rho _1,\beta_*$ satisfying
$$
\frac1{2(1-L^{-2})}<a<\frac32,\quad 0<\gamma _0\le\frac12,\quad
c_*,c_\xi,c'>0,\quad 0<\rho _0\le p,\quad 0<\rho _1<1.
\tag{2.1}
$$
For every $\beta\ge\beta_*$ it then supplies a single family, simultaneously for all $0\le\nu\le1$: a stopping index $J(\nu)$, real vectors $\xi_k(\nu)\in\mathbb R^3$, real $\mu_j(\nu;x)$ for $j\ge1$, torus errors $e_m^\ell,r_{tr}^\ell,r_{lg}^\ell$, their thermodynamic limits $r_{tr},r_{lg}$, and their right limits $r_{tr,0},r_{lg,0}$. For $0<\nu\le1$ it requires $J(\nu)\ge1$, $J(\nu)\to\infty$ as $\nu\downarrow0$, and
$$\tfrac12\le L^{J(\nu)}\sqrt\nu\le L^2.\tag{2.2}$$
Here and below $\gamma_j(\nu)=\prod_{i<j}(1+\xi_i(\nu)_2)^{-1}$, $\delta_j(\nu)=\prod_{i<j}(1+\xi_i(\nu)_2)/(1+\xi_i(\nu)_1)$, and $\beta_j(\nu)=\beta L^{jp}\gamma_j(\nu)$: these are precisely `gammaR`, `deltaR`, `betaR` applied to real $\xi$, rather than new physical parameters.

There is a quantifier trap here: F1 and F2 ask for $\xi_k(\nu)$ and $\mu_j(\nu;x)$ at **all** indices, although the physical RG at positive $\nu$ stops at $J(\nu)$. No estimate for an unperformed step is needed. Define $\xi_k(\nu)=0$ for $k\ge J(\nu)$ and $\mu_j(\nu;x)=0$ for $j>J(\nu)$; at $\nu=0$ use the indefinitely iterated massless physical flow. The formulae at the terminal scale use only $k<J$ and $j\le J$. For each fixed index, $J(\nu)\to\infty$ makes this extension eventually equal to the physical term as $\nu\downarrow0$, so it preserves the required continuity. This extension is part of the assembly proof, rather than an assertion that the physical massive flow continues through arbitrarily large masses.

`C1StarF1` is, for every $k$ and $0\le\nu\le1$,
$$\|\xi_k(\nu)\|\le\frac{c_\xi}{4\beta}q_*^{k+1},\qquad
\xi_k(\nu)\longrightarrow\xi_k(0)\quad(\nu\downarrow0).\tag{2.3}$$
The second assertion is pointwise in $k$, in the finite dimensional `Fin 3 → ℝ` norm.

`C1StarF2` says, for every $j\ge1$, $x\in\mathbb Z^d$, $0\le\nu\le1$,
$$|\mu_j(\nu;x)|\le c_*\beta^{-1/2+\rho _1}L^{-j\rho _0},\qquad
\mu_j(\nu;x)\longrightarrow\mu_j(0;x).\tag{2.4}$$
Writing $m_J(\nu;x)=1-\sum_{j=0}^{J-1}\beta_j(\nu)^{-1/2}\mu_{j+1}(\nu;x)$, for each fixed $0<\nu\le1,x$ there is $\ell_0$ such that every **admissible** $\ell\ge\ell_0$ with $ML^{J+1}\mid\ell$ satisfies the *exact* physical equality
$$\operatorname{blockM}_{\ell}(\beta,\nu)
=m_J(\nu;x)+e_m^\ell(\nu;x),\qquad
|e_m^\ell(\nu;x)|\le c_*\beta^{-2}L^{-2Jp}.\tag{2.5}$$
`blockM` is the $e_1$ component of the torus expectation at zero. The $\ell_0$ quantifier belongs to F2; F3 has no such threshold.

`C1StarF3` says that for **every** admissible $\ell$ and nonwrapping pair $x,y$ ($2|(x-y)_i|<\ell$ for every coordinate),
$$
\begin{split}
\operatorname{blockGtr}_{\ell}(x-y)&=m_J(\nu;x)m_J(\nu;y)
 \sum_{j=0}^{J-1}\frac{T_j^{\ell,\nu\delta_j(\nu)}(x,y)}{\beta\gamma_j(\nu)}
 +r_{tr}^{\ell}(\nu;x,y),\\
\operatorname{blockGlg}_{\ell}(x-y)&=r_{lg}^{\ell}(\nu;x,y),
\end{split}\tag{2.6}
$$
where $T_j^{\ell,\mu}$ is the *specific* `termKernel d L (freeSeq d L a) μ J j (ℓ/L^J-1)`, not Root-F's polymer term with the same letter. Both errors obey
$$|r_\#^\ell(\nu;x,y)|\le c_*\big[(1+|x-y|)^{-(p+\rho _0)}+\nu^{p/2}\big]
e^{-c'\sqrt\nu|x-y|},\qquad \#=tr,lg.\tag{2.7}$$
For every $\nu>0,x,y$, each $r_\#^\ell$ converges to $r_\#(\nu;x,y)$ in the **`LimAlong (ML)`** sense (all sufficiently high powers dividing $\ell$, not just the sequence $\ell=(ML)^n$), and $r_\#(\nu;x,y)\to r_{\#,0}(x,y)$ as $\nu\downarrow0$. Finally `RootFAndC1Star d N hN` requires this `C1Star` for the *same* $L\ge3,M\ge1$ chosen in its Root-F clause at $\kappa=\kappa_*(d)$, $c_9=1$. A construction with a new $L$ or $M$ would not prove that joint proposition.

## 2.2 What is already a theorem, with constants

Let $B,\alpha _0>0$ be fixed physical step constants, uniform in $k,\nu,\ell$, and set
$$C_0=\operatorname{rgCxi}(B,\alpha _0)=168B/\alpha _0^2,\qquad c_\xi=4C_0=672B/\alpha _0^2.\tag{2.8}$$
Assume the physical coefficient equation at every step is represented by the analytic triangular $A_k,c_k,f_k$ and the conjugation symmetry, with **all** the hypotheses of `Balaban.Flow.rg_step_infty`, including $\eta_k\le (2B/\alpha _0^2)\beta^{-1}q_*^{k+1}$ and its contraction condition. That landed theorem gives a unique real solution $\xi_k(\nu)$, analytic in its step parameters, with
$$\|\xi_k(\nu)\|\le C_0\beta^{-1}q_*^{k+1}=\frac{c_\xi}{4\beta}q_*^{k+1}.\tag{2.9}$$
This is the **bound half** of F1, provided the physical step exists also at $\nu=0$. `Balaban.Flow.norm_xi_le_of_step` packages the same stepwise bound into the sequence bound. For F1's continuity half, the coefficient data must converge uniformly on the fixed point ball and the triangular inverses must converge as $\nu\downarrow0$; then `Balaban.Flow.tendsto_rg_solution` applies. Analyticity in an abstract parameter alone does not supply the physical parameter map or its continuity. P4 §5, (5.23)–(5.27), pp. 715–716, is the fixed point calculation; (5.28)–(5.33), pp. 716–717, gives its coupling recursions and products. The PDF text layer mangles some formula symbols in (5.25)–(5.32), so (2.8)–(2.9) quote the *landed Lean constants*, not a claimed literal transcription of P4.

For any such real sequence, `Balaban.Flow.betaSeq_eq` and `nuSeq_eq` identify the recursions
$$\beta_{k+1}=\frac{L^p\beta_k}{1+\xi_k(2)},\qquad
\nu_{k+1}=L^2\nu_k\frac{1+\xi_k(2)}{1+\xi_k(1)}.\tag{2.10}$$
They imply the products in §2.1 by induction. If $6C_0q_*\le\beta(1-q_*)$, `Balaban.Flow.rg_flow_infty` proves the two product limits and, with $\Gamma_\infty(\nu)=\lim_j\gamma_j(\nu)$,
$$
|\Gamma_\infty(\nu)-1|\le\frac{2C_0q_*}{\beta(1-q_*)},\qquad
|\Delta_\infty(\nu)-1|\le\frac{6C_0q_*}{\beta(1-q_*)},
\tag{2.11}
$$
$$
\left|\beta_j(\nu)^{-1}-(\beta\Gamma_\infty(\nu))^{-1}L^{-jp}\right|
\le e^2\frac{2C_0q_*}{1-q_*}\beta^{-2}L^{-jp}q_*^j.\tag{2.12}
$$
`Balaban.Flow.exists_inv_betaSeq_asymptotics` gives the same coefficient asymptotic with $c_8=c_\xi/\beta$. Thus the $\gamma$ in Root-C is **$\Gamma_\infty(0)$**, and the coefficient in the leading Green term is exactly $(\beta\Gamma_\infty(0))^{-1}m(0)^2$. The identification needs the physical observable covariance to use the *same* $\beta_j$ as (2.10); that equality is a missing physical step, not a consequence of the abstract products. From `Balaban.Flow.norm_gammaSeq_le`, if $c_\xi q_*/[\beta(1-q_*)]\le\log 2$, then $|\gamma_j|,|\gamma_j^{-1}|\le2$; the real factors $1+\xi_i(2)>0$ make $\gamma_j\in[1/2,2]$. Consequently
$$\beta_j^{-1/2}\le\sqrt2\,\beta^{-1/2}L^{-jp/2}.\tag{2.13}$$
For $\nu>0$, $\Gamma_\infty(\nu)$ is the limit of the zero-extended sequence after the physical stop and is used only as a convenient bound. The identified physical coefficient is $\Gamma_\infty(0)$, obtained from the genuinely infinite massless sequence.

The stop scale is also conditional: `Balaban.LargeField.StopIndex.kStop_succ_C1Star` derives (2.2) with $J=kStop+1$ from a `RunningHyp`; `kStop_rootF_scale` gives the Root-F version. When the same running family satisfies `RunningHyp` for all $0<\nu\le1$, the upper bound in (2.2) implies $J(\nu)\to\infty$: if $J\le K$ and $0<\nu<(2L^K)^{-2}$, then $L^J\sqrt\nu<1/2$. The physical proof must still give the uniform family of `RunningHyp` witnesses.

For the observable layer, `Balaban.Observables.IsObs` (`LayerDef.lean`) already *states* the $\mu$ bound, normalized $M^{(j)}(h,h)=0$, localized $R^{ij}$ bound, source derivative identifications, and covariance decomposition on a fixed torus. From such a layer, `Balaban.Observables.Mk_const` proves $M_k(h,h)=m_kh$; `Gk_const` proves $G_k=C_k+R_k$ at $h$; `Gk_longitudinal`, with its explicit `hG` hypothesis, removes the Gaussian longitudinal term. `Balaban.Observables.lemma_2_1` proves the transverse form of a hard-spin background Jacobian and a stabilizer-invariant covariance, conditional on `IsBgAt` and the covariance symmetry. `Balaban.Observables.sum_R_le` proves, assuming `IsObs`, `CoeffBounds`, the polymer count $K_0$, admissible domain points, and $L^J\sqrt\nu\le L^2$,
$$\sum_{1\le i\le j\le J}\beta_{i-1}^{-1}
\sum_{X\ni x,y}\|R^{ij}(x,y;X)\|
\le C_R\beta^{-3/2+\rho _1}(1+r)^{-(p+\rho _0)}
e^{-\delta _0\sqrt\nu r/(2L^2)},\quad r=|x-y|.\tag{2.14}$$
Here the landed proof takes $C_R=eK_0C_{\rm series}$, with $C_{\rm series}$ furnished by `Balaban.Observables.core_series`; the half exponent is necessary. The scalar `Balaban.Observables.first_order_step`, `Balaban.Observables.gaussian_main_term`, `Balaban.Observables.second_order_new`, `Balaban.Observables.R2new_final`, `Balaban.Observables.R3_final`, and `Balaban.Observables.improved_first_of_const` bound pieces of the proposed induction under their explicit analytic and scale hypotheses. They do **not** assert that a physical fluctuation integral and renormalization map produce an `IsObs` successor. `Balaban.Observables.first_order_iff` is likewise an equivalence conditional on its composition identity, rather than a proof of that identity. `Balaban.termDirect_freeSeq_unit` identifies an *abstract free-flow* kernel with $L^{-jp}KC_{tr}K^T$; it does not identify the physical observable's `Gker` argument with that kernel.

## 2.3 Exact one-step assignments

The following are theorem **targets**, not names of landed declarations. They are phrased so that their hypotheses are local to the step and their conclusions yield the next inductive layer. A Lean implementation can use the existing `Terms`, `IsSF`, `ObsTerms`, `IsObs`, `CoeffBounds`, `RunningHyp` carriers; the physical map $\mathcal T_k$ and its source derivatives have not yet been given a landed Lean type, so no compile-ready declaration can honestly be printed for that map.

**RG-CoefficientStep($k$).** Input: a physical normalized small-field density $\rho_k(\psi;g)$ in `IsSF` with its P4/P5 analytic, reality, large-field, and torus-locality hypotheses; a specified block fluctuation measure $\mathcal T_k$; its three renormalization equations after the free-flow choice $c=ab,d=b$; the field values $\nu=0$ and $0<\nu\le1$ for which $k<J(\nu)$; and uniform bounds on the resulting $A_k,c_k,f_k$ *exactly as in* `Balaban.Flow.rg_step_infty`, with $\eta_k\le(2B/\alpha _0^2)\beta^{-1}q_*^{k+1}$. Require their dependence on $\nu$ to obey the explicit uniform-data and inverse-matrix convergence hypotheses of `Balaban.Flow.tendsto_rg_solution` as $\nu\downarrow0$ (with the previously determined $\xi_0,\ldots,\xi_{k-1}$ as parameters). Conclusion: the physical counterterms solve $A_k\xi_k+c_k(\xi_k)=f_k(\xi_k)$ uniquely in the contraction ball, are real, obey (2.9), and converge to the solution at $\nu=0$; the **physical** new couplings obey (2.10), and the fine penalty parameters equal the sequence `freeSeq d L a` (equivalently $a_j=a(1-L^{-2})/(1-L^{-2j})$ in unit-lattice notation for $j\ge1$). This selects the free-flow branch; P4 p. 717 also mentions another branch (5.34), which would change the kernel dictionary. Proof after the physical data have been constructed: apply `Balaban.Flow.rg_step_infty` and `Balaban.Flow.tendsto_rg_solution`, then rewrite the physical renormalization equations by P4 (5.28). The missing part is the construction and bounds of $A_k,c_k,f_k$ from $\mathcal T_k$, uniformly at $\nu=0$; `Balaban.Flow.triangularBounds_matrixInfty` only handles a matrix with already supplied entries.

**RG-ObservableStep($k$).** Input: the same physical $\mathcal T_k$, an `IsSF`/`IsObs` layer at scale $k$, the centered fluctuation with covariance $C^{(k)}$, P9 Proposition 3.1's localization/connected-product estimate, the stated polymer counting bound $\sum_{X\ni x,y}e^{-\kappa d_j(X)}\le K_0$, the exponent conditions of P9 p. 511 ($\rho_1=3\rho_2$, $0<\rho_0\le\min\{p/2,1-3p\rho_2\}$, $0<\gamma<\min\{p/2,1\}$, $\gamma>2p\rho_2$), and source derivative bounds for the large-field term $R_0^{(k+1)}$ of P9 (3.42)–(3.45). Conclusion: the *actual* differentiated transformed density has an `IsObs` layer at scale $k+1$, with
$$
m_{k+1}(x)=m_k(x)-\beta_k^{-1/2}\mu_{k+1}(x),\quad
|\mu_{k+1}(x)|\le C_M\beta^{-1/2+\rho _1}L^{-(k+1)\rho _0},
\tag{2.15}
$$
$$M^{(k+1)}(x;h,h)=0,\qquad
\|R^{i,k+1}(x,y;X)\|
\le C_R'\beta^{-1/2+\rho _1}L^{-(k+1)\rho _0}
e^{-\delta _0L^{-i}|x-y|_1}e^{-\kappa d_{k+1}(X)}
\quad(1\le i\le k+1).\tag{2.16}$$
The old $M^{(j)},R^{ij}$ are transported by the new background composition and satisfy their old bounds; $G_{k+1}=C_{k+1}+R_{k+1}$ with
$$C_{k+1}(x,y)=m_{k+1}(x)m_{k+1}(y)
\sum_{j=0}^{k}\beta_j^{-1}G^{(j+1)}(x,y).\tag{2.17}$$
The new $M^{(k+1)}$ must be the unnormalized first-order term minus $\mu_{k+1}\varphi_{k+1}$, with $\mu_{k+1}$ defined by evaluation at $(h,h)$; the difference between the old and new $m$ in every Gaussian term belongs to $R_{k+1}$ with (2.16). This is P9 (3.1)–(3.10), (3.16)–(3.23), (3.44)–(3.49), pp. 501–514. The theorem must choose its large-$\beta$ threshold and inductive slack so that the net coefficients $C_M,C_R'$ in (2.15)–(2.16) are at most $1$, as required by the literal `IsObs.μ_bound` and `IsObs.boundR` fields; putting `IsObs` itself among the output assumptions would be circular. P9's proof sketches several of the renormalization contributions as “similar”; they need explicit estimates in the physical theorem.

**RG-KernelStep($k$).** Input: the physical hard-spin background at $h$, its derivative $H_k$, its fluctuation covariance $C^{(k)}$, the free-flow equality for $a_k$, and the exact finite-torus block covariance/inverse identities of the Gaussian construction. Conclusion, for the *actual* kernel in (2.17), with $j=k$ and mass $\mu=\nu\delta_k(\nu)$,
$$G^{(k+1)}(x,y;h,h)=L^{kp}
T_k^{\ell,\mu}(x,y)(I-h\otimes h),\qquad
h^TG^{(k+1)}=G^{(k+1)}h=0.\tag{2.18}$$
Equivalently $\beta_k^{-1}G^{(k+1)}=(\beta\gamma_k)^{-1}T_k(I-h\otimes h)$. This is the exact normalization needed in F3; any missed $L^{kp}$ would change the Goldstone coefficient. Proof after identifying the physical $H_k,C^{(k)}$: use `Observables.lemma_2_1` for transversality and `Balaban.termDirect_freeSeq_unit` (with the $j=0$ case `termDirect_freeSeq_zero`) for the free Gaussian dictionary. P9 (4.12)–(4.14), pp. 517–518, gives the physical expression; (4.17), p. 518, is the free sum rule. The missing equality is between the **physical** $H_kC^{(k)}H_k^*$ and the landed abstract Schur kernel, including weighted adjoints and torus indexing. `LayerStructure.lemma_2_1` alone gives only a scalar transverse kernel, not its value.

**RG-FamilyStep($k$).** Input: two admissible tori carrying the *same* physical initial density and marked source, and the physical step's local finite-set construction. Conclusion: the coefficient equations, their unique $\xi_k$, the scalar $\mu_{k+1}(x)$, and each localized $R^{i,k+1}(x,y;X)$ agree when the common support embeds in the interior quarter boxes; at fixed $k,i,x,y,X$ they are right-continuous in $\nu$ at $0$, with the uniform bounds (2.9), (2.15), (2.16). Proof: restriction commutes with the fluctuation and counterterm maps on common finite sets; uniqueness of the coefficient fixed point then gives torus independence. For continuity use the coefficient result above and dominated convergence in each finite localization integral or a uniform analytic parameter theorem. **This is a distinct hypothesis about the family**, absent from `IsObs` (`LayerDef.lean` explicitly says its O5 continuity and torus clause is not in that file). Root-F's two-torus clause compares only its $T_j$ at fixed $\nu$ and does not prove these statements for $\xi,\mu,R^{ij}$.

The base case must identify the microscopic hard-spin source derivative and covariance with the scale-zero objects, and the induction needs a common $L,M,a,\rho _0,\rho _1,\gamma _0,\beta_*$ for **all** $k,\nu,\ell$. This cannot be obtained by choosing a fresh constant at each step. The one-step assignments above, plus this base case, give F1 and the scale-resolved parts of F2/F3 by induction. They are the mathematically exact content needed from P4 §5 and P9 §§2–3; P8, Balaban–O'Carroll, *Annals of Physics* **260** (1997), pp. 1–8, gives an effective-action method for the massive Gross–Neveu model, not these O(N) estimates.

## 2.4 Terminal integration, torus limits, and zero field

A final-scale theorem is unavoidable: it is **not** an ordinary induction step. Its input is the physical layer at $J=J(\nu)$, the final massive integration, and the large-field polymer expansion. Its exact conclusion is the finite-torus source identity
$$\log Z_\ell(g)=F_J(h,g)+R^{(J)}(h,g)+P^{(J)}(g)\tag{2.19}$$
on every admissible torus, with the first two $g$ derivatives at $0$ identified with the physical `blockM`, `blockGtr`, `blockGlg`. P9 (4.2)–(4.9), pp. 515–517, is the source. In particular require the **quantitative** derivative estimates, for $r=|x-y|$ and fixed constants $K_0,K_2,\delta_T>0$,
$$|\partial_{g(x)}(R^{(J)}+P^{(J)})(0)|\le3K_0\beta_{J-1}^{-2},\qquad
|\partial_{g(x)}\partial_{g(y)}(R^{(J)}+P^{(J)})(0)|
\le K_2\beta_{J-1}^{-2}e^{-\delta_TL^{-J}r}.\tag{2.20}$$
P9 p. 517 gives a sharper displayed off-diagonal estimate but its text layer is garbled; (2.20) is the clear bound from the preceding unsimplified $\beta_{J-1}^{-2}$ polymer estimate, with a constant absorbing its finite sum and $e^{2dL\kappa}$. The paper does **not** state right continuity of these terms at $\nu=0$; their vanishing will follow from (2.20). Under $\gamma_{J-1}\ge1/2$,
$$3K_0\beta_{J-1}^{-2}\le12K_0L^{2p}\beta^{-2}L^{-2Jp},\tag{2.21}$$
which is F2's $e_m$ bound if $c_*\ge12K_0L^{2p}$. The same estimate implies the terminal first derivative vanishes as $J(\nu)\to\infty$.

For completeness, (2.20) also gives the **stronger** spatial form needed for F3. Put $u=L^{-J}$ and $A_{p,\delta}:=e^{\delta/2}\sup_{t\ge0}t^{2p}e^{-\delta t/2}<\infty$. Since $u\le1$, for every $r\ge0$,
$$u^{2p}e^{-\delta ur/2}
=(1+r)^{-2p}[u(1+r)]^{2p}e^{-\delta u(1+r)/2}e^{\delta u/2}
\le A_{p,\delta}(1+r)^{-2p}.\tag{2.22}$$
Also (2.2) gives $u\ge\sqrt\nu/L^2$. Split the exponential in (2.20) in halves, apply (2.22) and $2p\ge p+\rho _0$, and obtain
$$K_2\beta_{J-1}^{-2}e^{-\delta_Tur}
\le4K_2L^{2p}A_{p,\delta_T}\beta^{-2}(1+r)^{-(p+\rho _0)}
e^{-\delta_T\sqrt\nu r/(2L^2)}.\tag{2.23}$$
For $\beta\ge1$ this is absorbed into (2.7), even without its extra $\nu^{p/2}$ allowance. The observable remainder (2.14) is absorbed with $c'\le\min(\delta_0,\delta_T)/(2L^2)$ and $c_*\ge C_R+4K_2L^{2p}A_{p,\delta_T}$ because $\beta^{-3/2+\rho _1}\le1$. Combining (2.17), (2.18), (2.19) gives the exact equalities (2.5)–(2.6). This is the complete numerical reduction from the proposed step outputs to F2/F3.

At fixed $\nu>0$, `Balaban.Correlations.onePoint_tendsto_along_multiples` and `twoPoint_tendsto_along_multiples` already give the physical thermodynamic limits from Root-F. `Balaban.termKernel_converges` supplies the limit of each of the finitely many kernels in (2.6), so subtraction gives the F3 `LimAlong (ML)` remainder limits; no separate physical torus-limit theorem for the *sum* is required. The only caveat is the already stated common-family and normalization equality, which permits the same $m_J,\xi_j$ in every torus. For F2, the torus correction needs only its eventual bound (2.5), exactly as `C1StarF2` asks.

At $\nu\downarrow0$, each fixed $(i,j,x,y)$ observable term must converge by `RG-FamilyStep`; the bound (2.16) and polymer count give a summable majorant, since
$$
\sum_{j=i}^{\infty}L^{-j\rho _0}=\frac{L^{-i\rho _0}}{1-L^{-\rho _0}},\qquad
\sum_{i=1}^{\infty}L^{-(i-1)p-i\rho _0}<\infty.\tag{2.24}
$$
For a fixed pair $x,y$, drop the exponentials. The $(i,j)$ summand is at most $2K_0C_R'\beta^{-3/2+\rho_1}L^{-(i-1)p-j\rho_0}$, independently of $\nu,J,\ell$. Its full double sum is
$$\frac{2K_0C_R'\beta^{-3/2+\rho_1}L^{-\rho_0}}
{(1-L^{-\rho_0})(1-L^{-(p+\rho_0)})}<\infty.\tag{2.24a}$$
Tannery then gives the right limit of the observable double sum. The terminal term tends to zero by (2.21)–(2.23). `Balaban.Correlations.c1Star_remainder_limit_criterion` and `Balaban.Correlations.c1Star_truncated_limit_criterion` formalize precisely this double-limit argument once the summands and their bounds are supplied. In particular the zero-field limit of the longitudinal part is the limit of the observable $R^{ij}$ sum; the Gaussian part is zero at every scale by (2.18).

The zero-field magnetization is therefore the **same** physical observable limit
$$m(0)=1-\sum_{j=1}^{\infty}\beta_{j-1}(0)^{-1/2}\mu_j(0;x),\tag{2.25}$$
independent of $x$ because it is the pointwise limit of the translation-invariant physical magnetization. Its convergence follows from (2.4), (2.13), and $\sum_jL^{-(j-1)p/2-j\rho_0}<\infty$. The coefficient in the transverse Green term is $m(0)^2/(\beta\Gamma_\infty(0))$ by (2.12), (2.18), the free sum rule `Balaban.KernelHyp.tsum_eq_latticeGreen`, and the limit argument in Part 1. P9 (4.15)–(4.18), pp. 518–519, motivates this comparison; it treats the $\nu\downarrow0$ coefficient dependence only implicitly. The explicit pointwise continuity assertions in F1–F3 are what make that argument valid for the actual flow.

**Lean integration target.** A producer theorem should conclude `Nonempty (Balaban.Correlations.C1Star d N L M hN)` from one coherent physical family carrying `IsSF`, `IsObs`, the four step outputs above, a base case, `RunningHyp`, and the terminal theorem (2.19)–(2.20), with $L,M$ those of Root-F. It should then be paired with the Root-F clause to prove `Balaban.Correlations.RootFAndC1Star d N hN`. `Balaban.Correlations.rootC_of_rootFAndC1Star` consumes that joint hypothesis. This assignment does not ask an agent to reprove the scalar summation, coefficient products, kernel limits, or Root-C assembly already landed.

**Confidence.** High for the exact Lean interface, the conditional numerical reductions (2.8)–(2.25), and the separation between landed analytic lemmas and missing physical construction. Moderate for the proposed physical step and terminal theorem until the P5/P7 large-field source bounds, weighted-adjoint convention in (2.18), and the $\nu=0$ parameter domain are checked in a single formal step. P9 ends with §4 on p. 519 (references p. 519–520): the requested “P9 §5” does not exist. P8's PDF text layer has garbled typography, and P4's has damaged coefficient formulas; neither is used here as authority for an unreadable constant.

# Part 3. Audit of the landed one-step producers

This audit reads the landed source at `/home/scott/Balaban` commit `035d6a80a5877892c67f63c1849c79f32c9b4001` (17 October 2026). The requested W977 reduction is present in `Balaban/Correlations/C1StarFromStep.lean`, `C1StarFromStepCore.lean`, `C1StarFromStepLimits.lean`, and `C1StarFromStepRootC.lean`. The exact consumer is `Balaban.Correlations.c1Star_of_physical_step_targets`, lines 31–165 of `C1StarFromStep.lean`. Its inputs have the following *logical* status: it projects the **bound** conjuncts of `hcoeffZero`, `hcoeffStep`, `hobsZero`, and `hobsStep`; the displayed physical coefficient equations and `Mstep = magJ` conjuncts are named in the type but are not used in its proof. The physical content of `C1Star` is carried by the bounds, continuities, and especially `hfinalM`/`hfinalG`. This is an audit of proof consumption, not a claim that the unused equations have been proved. The positive-field families are extended by zero after $J(\nu)$ (`c1StarF1_of_stopped_steps`, `stopped_mu_bound_cont` in `C1StarFromStepCore.lean`); the massless families retain all scales.

## 3.1 The coefficient equation: what the tower supplies

`Balaban.Inhabited.StepTowerG` (`Inhabited/StepTowerG.lean`, lines 35–81) is a record of numerical margins and one `FlCore` witness; its own docstring says it certifies one witness step, not a root. `Balaban.Inhabited.exists_stepTowerG` (`StepTowerGProducer.lean`, line 35) inhabits it for every $d\ge3,L\ge3,N\ge2$ and a chosen cover index. The fixed `StepTower` and `StepTower.scale` (`StepTowerScale.lean`, line 51) give one threshold before $k$ and a `StepScaleData` for $k\ge1$, admissible tori, $0\le\nu$, and $\nu L^{2(k+1)}\le1$. The records called `StepTowerRenSol` and `StepTowerTheta` concern the *background/renormalized solution and chart radius* (`StepTowerRenSol.lean`, `StepTowerTheta.lean`); they do not give the three P4 counterterms $\xi_k$. In particular no field of these towers is the physical $A_k,c_k,f_k$ of (5.23), the running $\beta_k$, or their identification with the hard-spin density after $k$ steps.

The conditional deduction from the landed flow is exact. Let $q=L^{-2\gamma _0}$, $B,\alpha _0>0$, and $C_\xi=\operatorname{rgCxi}(B,\alpha _0)=168B/\alpha _0^2$. At each *specified physical* step, supply the matrix, analytic functions, conjugation symmetry, ball bounds and contraction condition appearing literally in `Balaban.Flow.rg_step_infty` (`Flow/RGInfty.lean`, lines 51–88), including
$$\eta_k\le B(2/\alpha _0^2)\beta^{-1}q^{k+1}.\tag{3.1}$$
That theorem produces a unique solution in the contraction ball with $\|\xi_k\|\le C_\xi\beta^{-1}q^{k+1}$ and real components at the conjugation-fixed physical datum. Taking real parts and $c_\xi=4C_\xi$ gives the second conjunct of W977's `hcoeffStep`, and gives `hcoeffZero` if the same data and estimates are constructed at $\nu=0$. The equation conjunct follows by taking real parts of the theorem's complex equation **only after** the real $A,c,f$ supplied to W977 have been identified with these physical complexifications. `Balaban.Flow.norm_xi_le_of_step` (line 96) assembles the induction if the step bound depends on earlier coefficients. `Balaban.Flow.tendsto_rg_solution` (line 231) yields W977's `hcoeffCont` only with its explicit uniform convergence of $f_\nu-c_\nu$ on the fixed-point ball and convergence of the triangular inverses. Neither convergence is a field of `StepTowerG`.

For the same *identified* $\xi$, `Balaban.Flow.betaSeq_eq` and `nuSeq_eq` (`RunningCoefficients.lean`, lines 80–96) prove $\beta_k=\beta L^{k(d-2)}\gamma_k$ and $\nu_k=\nu L^{2k}\delta_k$, with $\gamma_k=\prod_{i<k}(1+\xi_i(2))^{-1}$. `Balaban.Flow.rg_flow_infty` (`RGInfty.lean`, line 161), under $6C_\xi q\le\beta(1-q)$, proves $\gamma_\infty,\delta_\infty$ and the quantitative inverse-$\beta_k$ estimate (2.11)–(2.12). Thus the *flow* limit is proved, but its equality to the coefficient of the **physical** fluctuation covariance still requires the physical coupling recurrence and kernel identification (2.18). `Balaban.LargeField.StopIndex.kStop_succ_C1Star` (`StopIndex.lean`, line 406) gives W977's `hJbounds` for $J=kStop+1$ **from** `RunningHyp`; its module docstring explicitly leaves the final integral open. `hJtend` follows from `hJbounds` as shown in §2.2, after one physical `RunningHyp` family has been supplied.

**Missing named coefficient-step estimate.** On the actual transformed hard-spin density, construct $A_{\beta,\nu,k}$, $c_{\beta,\nu,k}$, $f_{\beta,\nu,k}$ and the physical counterterms $\xi^{\rm phys}_{\beta,\nu,k}\in\mathbb R^3$ for every $k<J(\nu)$ and every $k$ at $\nu=0$. Prove the *literal* hypotheses `hAan`, `hA`, `hcb`, `hfb`, `hcond`, `hηbd`, and the conjugation hypotheses of `rg_step_infty`, uniformly in the admissible torus, and the `hdata`, `hω`, `hAconv` hypotheses of `tendsto_rg_solution` as $\nu\downarrow0$. Identify $\xi^{\rm phys}$ with the unique fixed point, and prove that the newly normalized physical couplings are `betaSeq L d ξ β` and `nuSeq L ξ ν` (including the free-flow branch). This gives exactly W977's `hcoeffZero`, `hcoeffStep`, `hcoeffCont`; it cannot be replaced by an abstract choice of $A,c,f$. P4 derives the equations in §5, (5.1)–(5.23), pp. 710–715, proves the analytic estimates (5.24)–(5.27), pp. 715–716, and obtains the recurrence and decay (5.28)–(5.33), pp. 716–717. The PDF text layer damages several symbols in (5.25)–(5.32); the numerical constant in (3.1) is the **Lean** hypothesis, not a transcription of damaged print.

## 3.2 The observable after one fluctuation and renormalization

There is a substantial landed *zero-class* producer. At a positive field and $k\ge1$, `Balaban.Inhabited.obsTiltLabels_local_fromTowerG_rho` (`ObsTiltLabels.lean`, line 353; the $\rho=1$ theorem is line 788) chooses one analytic, local activity family on a common label system and identifies its label sum with the first two step exponents $W_1+W_2$ on the constant-$h_0$ fibre. `obsFamily_full_fromTowerG_rho` (`ObsFamilyJoint.lean`, line 50) adds the analytic, local, rooted `obsCoeffParam` with a decay bound and its value as the zero-class step observable. `obsM0Family_full_fromTower_rho` (`OffFibreM0Family.lean`, line 33, fixed $d=L=3,N=2$) extends the value identity across the chart datum: in its normalization,
$$M_{0,k+1}^{\rm zero}(y,i;g)=\sqrt{\beta_U}\sum_{T'}\operatorname{obsCoeffParam}_{y,i}((\operatorname{raw}D,g),T'),\qquad \beta_U=\beta L^{k(d-2)}.\tag{3.2}$$
`obsFamily_pair_fibre_fromTowerG_rho` (`StepIdentityFibreObs.lean`, line 379) pairs the same coefficients with $g$ before the datum is chosen. `stepIdentity_zeroClass_fibre_fromTowerG` (`StepIdentityFibreFamilies.lean`, line 64) combines the energy and observable families into an exact **exponential** step identity. The stronger common-witness join is `zeroClassStep_families_fromTowerG_rho` and `zeroClassStep_sites_fromTowerG_rho` (`PhysicalZeroJoin.lean`, lines 41 and 1403): the latter also feeds localized renormalized site records through `RenormPhysicalRecord.lean` and `RenormM0SiteRecord.lean`. These are genuine produced local identities; they are restricted to `zeroClass`, the constant-field fibre, and the ordinary small-field step.

The quantitative bound is also produced. `obsFamily_prefactor_fromTowerG_rho` (`ObsFamilyPrefactor.lean`, line 155) bounds the local coefficient by $C\,\operatorname{obsPrefactor}(p,s,b)e^{-3\kappa_{dec}d_{ext}(T')/2}$ with $b=\beta L^{k(d-2)}$ and $C$ independent of $k$. Here `obsPrefactor` (`Thm31bFromTower.lean`, line 38) is
$$w_p(b)^4b^{-1/2-s}+w_p(b)^2b^{-1},\qquad w_p(b)=(\log b)^p.\tag{3.3}$$
`rootTermFamily_obs_birthScale_fromTowerG_rho` (`RootTermZeroClass.lean`, line 749) regroups it as a site/polymer/source family $U_{x,X}(g)$, with support, source locality, analyticity, the paired identity $\sum_{x,X,i}g_{xi}U_{x,X}(g)_i=\beta_U^{-1/2}\sum_{x,i}g_{xi}M_{0,k+1}^{\rm zero}(x,i;g)$, and, for $0<\delta'<\min\{s(d-2),(d-2)/2\}$ and any $c_9>0$ after one threshold,
$$\|U_{x,X}(g)\|\le c_9L^{-(k+1)((d-2)/2+\delta')}
 \exp\!\left[-\kappa_{root}\frac{|X|}{(L^{m_1+1}L^{k+1})^d}\right],\quad \|g\|_1\le\rho/2.\tag{3.4}$$
This is the source-root birth-scale bound, **not** the $\mu_{k+1}$ bound. Indeed (3.2) shows that passing from the source coefficient to the unnormalized $M_0$ multiplies by $\sqrt{\beta_U}$. Even if the scalar projection of $M_0(h,h)$ were established, its bound would begin with $\sqrt b\operatorname{obsPrefactor}=w_p(b)^4b^{-s}+w_p(b)^2b^{-1/2}$, times a polymer-counting constant. To turn that into W977's $c_*\beta^{-1/2+\rho_1}L^{-(k+1)\rho_0}$ one must choose exponents with strict room to absorb the logarithms (for example $s>1/2-\rho_1$, $(d-2)s>\rho_0$, and $(d-2)/2>\rho_0$), prove the site sum uniformly, and account for the field/background factors. The bare (3.4) cannot be renamed `IsObs.μ_bound`.

The source-normalization point can be checked directly from the landed tower: for $\bar m_{x,i}(g)=\sum_{T'}mObs(x,i,(\operatorname{raw}D,g),T')$, the step exponent in `stepIdentity_zeroClass_fibre_fromTowerG` is $E(g)=E_0+F(g)+\sum_{x,i}g_{xi}\bar m_{x,i}(g)$, where $F$ is its `FcompAtC` term and $E_0$ is source independent. At a differentiability point $g=0$, the finite-dimensional product rule proves
$$DE(0)[u]=DF(0)[u]+\sum_{x,i}u_{xi}\bar m_{x,i}(0),\tag{3.5}$$
$$D^2E(0)[u,v]=D^2F(0)[u,v]+\sum_{x,i}\bigl(u_{xi}D\bar m_{x,i}(0)[v]+v_{xi}D\bar m_{x,i}(0)[u]\bigr).\tag{3.6}$$
The tower identity $T_{step}(g)=e^{E(g)}$ implies $T_{step}(g)\ne0$ there; any local analytic logarithm differs from $E$ by a constant in $2\pi i\mathbb Z$, so (3.5)–(3.6) are also its first two derivatives. This is the exact derivative consequence of the landed identity. It concerns **one zero-class step**, not $\log Z_\ell$ or the final $R^{(J)}+P^{(J)}$.

`Balaban.Observables.IsObs` (`LayerDef.lean`, line 173) is the required output *interface*, not a tower conclusion. Its fields `μ_bound`, `normM`, `boundR`, and `ident` assert the new scalar bound, constant-field normalization, two-point localized remainder, and first two derivatives of the whole-lattice generator on one torus. If a produced physical successor `IsObs P Q βrun νrun a Tm Ot Gker` is identified with W977's families by $\mu_{k+1}^{\rm raw}(x)=Ot.\mu(k+1,x)$, $\beta_{run}(0)=\beta$, $Q.\rho_i=\rho_i$, and the torus-to-$\mathbb Z^d$ embedding, then `IsObs.μ_bound` gives W977's `hobsStep` **bound** for $c_*\ge1$: $|\mu_{k+1}^{\rm raw}(x)|\le\beta^{-1/2+\rho_1}L^{-(k+1)\rho_0}\le c_*\beta^{-1/2+\rho_1}L^{-(k+1)\rho_0}$. `Mk_const` and `Gk_const` (`LayerConst.lean`, lines 42 and 65) then give the constant-field first and second layer values, and `Gk_longitudinal` (line 88) removes the Gaussian longitudinal term under its explicit transverse-kernel hypothesis. None of these theorems creates `IsObs` from the tower. Its module docstring explicitly excludes the family-level continuity and torus clause (O5), so W977's `hobsCont` remains independent.

**Missing named observable-step estimate.** For the **actual inherited** `IsSFObs` class, rather than `zeroClass`, prove a successor `IsSFObs` after the fluctuation and coefficient renormalization, with one common choice of $\mu_{k+1}$, $M^{(k+1)}$, $R^{i,k+1}$ and kernel $G^{(k+1)}$. In the physical notation of P9, (3.44) gives the unrenormalized first source coefficient $M_{u,k+1}$; at $(h,h)$ rotational covariance must give $M_{u,k+1}(x;h,h)=\mu_{k+1}(x)h$, followed by $M^{(k+1)}=M_{u,k+1}-\mu_{k+1}\varphi_{k+1}$ and $m_{k+1}=m_k-\beta_k^{-1/2}\mu_{k+1}$. Prove `IsObs.μ_bound`, `boundM`, `normM`, `boundR`, and `ident`, including the comparison of the old-$m_k$ Gaussian sum (3.49) with the new-$m_{k+1}$ one. The scale-local estimate needed is exactly (2.15)–(2.18), with the `IsObs` constants at most $1$ after the threshold; a zero-class bound on $U$ is insufficient. Also prove the same local coefficients across all admissible tori and their right continuity at $\nu=0$ to obtain `hobsZero` and `hobsCont`. P9 states the inherited hypotheses in §2, (2.1)–(2.18), pp. 496–498, analyzes the fluctuation in §3, (3.1)–(3.45), pp. 501–513, and performs this *particular* scalar subtraction and Gaussian correction on p. 514. `Observables/FirstOrderStep.lean`, `SecondOrderStep.lean`, `LayerSums.lean`, and `ImprovedBound.lean` bound components conditional on their classes; they do not discharge this physical successor theorem.

## 3.3 Final source derivatives

The most complete landed one-step identity is the zero-class exponential equality of `PhysicalZeroJoin.lean` just used in (3.5)–(3.6). No theorem in `Balaban/Inhabited/*` identifies the terminal hard-spin `blockM`, `blockGtr`, or `blockGlg` with first or second derivatives of a final massive integral. The only `Inhabited` use of `logPartition_multiscale` found is `rootF_clauses_transfer`/`rootF_clauses_unitField` (`RootRotation.lean`, lines 66 and 160), which transport an **assumed** Root-F clause by rotation. `StopIndex.lean` explicitly states that its final cutoff, massive covariance, final fluctuation integral, large-field gas, and $k_f=0$ branch are open. Thus the zero-class step exponential cannot furnish W977's `hfinalM` or `hfinalG` by differentiation alone.

The terminal target has a precise input and quantitative conclusion. On every admissible $\ell$, with the *inherited* layer at $J(\nu)$, construct a physical identity
$$\log Z_\ell(g)=F_J(h,g)+R_J(h,g)+P_J(g)\tag{3.7}$$
near $g=0$, identify $D\log Z_\ell(0)$ and $D^2\log Z_\ell(0)$ with the definitions `blockM`, `blockGtr`, `blockGlg`, and prove, uniformly in $\ell,\nu,x,y$,
$$|D(R_J+P_J)(0)[\delta_x]|\le3K_0\beta_{J-1}^{-2},\qquad
|D^2(R_J+P_J)(0)[\delta_x,\delta_y]|\le K_2\beta_{J-1}^{-2}e^{-\delta_TL^{-J}|x-y|},\tag{3.8}$$
with $K_0,K_2,\delta_T>0$ independent of scale and torus. The Gaussian kernel in $F_J$ must be **the** `mainTr` kernel through the physical $H_kC^{(k)}H_k^*$ identity (2.18), and its longitudinal part must vanish; otherwise the equality in `hfinalG` is not established. The observable $R^{ij}$ sum must obey the landed `Balaban.Observables.sum_R_le` bound under the now-produced `IsObs` and `CoeffBounds`. This is the exact source of the $r_{tr},r_{lg}$ terms. P9 (4.1)–(4.7), pp. 515–516, supplies the terminal representation, (4.8)–(4.9), pp. 516–517, its derivatives, and the displayed bounds on p. 517. Its last off-diagonal display has damaged PDF text; (3.8) uses the readable preceding $\beta_k^{-2}$ bound, as in §2.4.

Here is the fully numerical implication needed by W977. If $\gamma_{J-1}\ge1/2$, then $\beta_{J-1}^{-2}\le4L^{2(d-2)}\beta^{-2}L^{-2J(d-2)}$, so the first inequality of (3.8) gives `hfinalM` with $c_*\ge12K_0L^{2(d-2)}$. Put $p=d-2$, $r=|x-y|$, $u=L^{-J}$ and $A_{p,\delta}=e^{\delta/2}\sup_{t\ge0}t^{2p}e^{-\delta t/2}$. The **upper** stop inequality $L^J\sqrt\nu\le L^2$ gives $u\ge\sqrt\nu/L^2$. Splitting the exponential and applying (2.22) yields
$$K_2\beta_{J-1}^{-2}e^{-\delta_Tur}\le
4K_2L^{2p}A_{p,\delta_T}\beta^{-2}(1+r)^{-2p}
e^{-\delta_T\sqrt\nu r/(2L^2)}.\tag{3.9}$$
Since $\rho_0\le p$, $2p\ge p+\rho_0$. Combine (3.9) with `sum_R_le` (2.14), take $c'\le\min(\delta_0,\delta_T)/(2L^2)$ and $c_*$ at least the sum of their constants (for $\beta\ge1$), and the literal error bounds of `hfinalG` follow. The equalities require (3.7), `Mk_const`, `Gk_const`, and the physical kernel dictionary; none follows from the numerical inequality. Finally `hfamilyLimit`/`hfamilyZero` need the same coefficients on all tori and scale-wise limits. `Balaban.Correlations.remainder_limits_of_scale_steps` (`C1StarFromStepLimits.lean`, line 26) proves these limits *once* a representation, a summable majorant, and per-scale limits are supplied. Its theorem does not produce those physical inputs.

## 3.4 Assignment-ready boundary

The exact next theorem targets, in the landed objects' notation, are:

1. **`physical_rg_coefficients_of_step`** (new target, not landed): for the actual inherited `Terms`/`IsSF` and `StepSetting` at every $k<J(\nu)$ and at $\nu=0$, construct one coherent real family `ξraw`, `A`, `c`, `f` satisfying W977's `hcoeffZero`, `hcoeffStep`, `hcoeffCont`, and identify the physical running couplings with `Flow.betaSeq` and `Flow.nuSeq`. Its proof uses `rg_step_infty`, `tendsto_rg_solution`, `rg_flow_infty` *after* the P4 functional bounds and physical recurrence have been proved. The tower by itself supplies none of those functional bounds.
2. **`physical_isObs_successor_of_step`** (new target): from an inherited `IsSFObs` and the physical fluctuation, output a successor `IsSFObs` and a torus-coherent $\mu_{k+1}$ with the literal `IsObs.μ_bound`, normalized $M^{(k+1)}$, and $R^{i,k+1}$ estimates. It must connect the already-produced `obsCoeffParam`/`M0C` of the zero-class tower to (3.44) for a general class, prove the scalar projection on p. 514, and identify the physical Gaussian kernel with `Gker`. This gives W977's `hobsZero`, `hobsStep`, `hobsCont` only after the torus/zero-field family theorem is included. The convention `ξ_k(ν)=0` for $k\ge J(\nu)$ is then exactly `C1StarFromStepCore.lean`'s extension, not a one-step estimate.
3. **`physical_final_source_derivatives`** (new terminal target): from the physical layer at $J$, final massive integral, and large-field expansion, establish (3.7)–(3.8), the hard-spin `blockM`/`blockGtr`/`blockGlg` identifications, and the finite-torus equalities in W977's `hfinalM`/`hfinalG` with the *same* `L,M,a,ξraw,μraw` as the coefficient and observable steps. The reductions (2.20)–(2.24a) and (3.9) then supply its error constants and `C1StarFromStepLimits` supplies the remainder limits under the local family data.

This boundary is substantive: `StepTowerG` and `zeroClassStep_sites_fromTowerG_rho` prove an inhabited **single zero-class step** with localized source coefficients; `C1Star` needs an inherited physical flow, a massless family, and the terminal Gibbs derivatives. The conditional Lean bridge is already `c1Star_of_physical_step_targets`; `rootC_of_rootF_step_output` (`C1StarFromStepRootC.lean`, line 37) then uses Root-F at the **same** $L,M$ and `rootC_of_rootFAndC1Star` to obtain Root-C. P8, *Annals of Physics* **260** (1997), pp. 1–8, supplies a source-differentiation method for a different model, not the missing hard-spin one-step estimates. P9, *Communications in Mathematical Physics* **199** (1999), pp. 493–520, ends with §4; there is no §5 to cite. Confidence: high in the theorem-type audit, the local derivative proof (3.5)–(3.6), and the identification of the missing interfaces; moderate in the proposed physical successor until its inherited-class and torus-uniform estimates are formalized.

# Part 4. Physical coefficient flow from a provisional successor

This part uses the read-only Lean source at `/home/scott/Balaban` commit `7de6dd0d3fc8ca7cfaa26ce2404781e39eca0566` and P4, *Communications in Mathematical Physics* **182** (1996), §5, pp. 707–718. P4 is a scan. Its OCR corrupts several formulas in (5.1)–(5.31); the statements below use the readable prose and the exact landed Lean definitions for numerical constants. A successor class being designed elsewhere is understood here as **provisional successor terms and a step identity before H.5 and `CoeffBounds` are installed**. Assuming a completed `IsSFFamily` would assume the desired result: `Balaban.SmallField.Def6.CoeffBounds.flow` (`SmallField/Def6.lean`, lines 474–484) already existentially identifies its coefficients with `Flow.betaSeq` and `Flow.nuSeq`, and `IsSFFamily.renorm` already asserts H.5.

## 4.1 Which counterterms H.5 determines

There is a notation correction essential to the theorem statement. In P4 (5.23), $\xi$ is **not** the tuple $(A_k,c_k,f_k)$. The paper first has five raw renormalization constants, denoted there by $\zeta,e,b,c,d$. Its two auxiliary choices $c=ab$ and $d=b$ are (5.20), p. 714. After rescaling and triangular elimination, the three unknowns of (5.23) are
$$\xi_k=\bigl(\zeta_{k+1}/\varepsilon_{k+1},\;\beta_{k+1}^{-1}e_{k+1},\;\beta_{k+1}^{-1}b_{k+1}\bigr)\in\mathbb C^3.\tag{4.1}$$
Here $A_k$ is the *matrix* of the linearized three equations, while $c_k(\xi,p)$ and $f_k(\xi,p)$ are their nonlinear and forcing functions. The letter $c$ in $c=ab$ is a raw counterterm; it is distinct from the function $c_k$, from the matrix's lattice sum $c_1(v)$, and from `StepSetting.cKernel`. P4 says explicitly on p. 713 that the three conditions leave two constants free and explains why the $c,d$ directions are irrelevant. H.5 therefore does not uniquely determine all five without an auxiliary convention. Another convention, $c=d=0$, is mentioned on p. 717, but this part uses (5.20), since it is the convention behind the landed free weight flow.

Let $T'_{n,\xi,p}$ be the provisional next-scale `Terms` on torus $n$, built from the inherited `StepClass`, the new energy coefficient family, and the step identity at parameter $p$. Let $E'_{n,\xi,p}$ be its vacuum constant. Write $e_i=\operatorname{Pi.single}(i,1)$, and let $V_{\xi,p}=\operatorname{ElocInf}(m_0,T'_{\bullet,\xi,p},k+1,0)$ in the exact notation of `RenormCond` (`SmallField/Def6.lean`, lines 435–449). The four residuals to be computed are
$$\begin{aligned}
R_0(\xi,p;i)&=V_{\xi,p}(e_i,e_i),\\
R_h(\xi,p;i)&=D_hV_{\xi,p}(e_i,e_i)[e_i],\\
R_\psi(\xi,p;i)&=\left.\frac{d}{dt}V_{\xi,p}((1+t)e_i,e_i)\right|_{t=0},\\
R_2(\xi,p;i,i')&=\lim_{n\to\infty}\operatorname{momentSum}(m_0,T'_{n+1,\xi,p},k+1,i,i'),\quad i\ne i'.
\end{aligned}\tag{4.2}$$
The last limit must be *proved to exist* for the full `Edens` transverse Hessian, with its `liftSq` weight; a bounded local coefficient alone does not assert this. `RenormCond.val` asks $R_0=0$; `dh` asks $R_h=0$ only when `0 < nuIdeal L k νk (k+1)`; `dpsi` asks $R_\psi=0$; `moment` asks convergence to zero. At $\nu=0$, `dh` is vacuous in the landed class. A massless three-equation flow therefore needs the additional analytic continuation or a strengthened zero-field normalization as an explicit hypothesis, not an invocation of `RenormCond.dh`.

**Target `physical_vacuum_normalization_of_successor` (P4 (4.21), (5.1), pp. 705–708).** Given provisional successor terms with a total constant-field value $e_{0,n}(\xi,p)$ whose **per-block quotient** $e_{0,n}/B_n$ is torus-independent, a block count $B_n>0$, and the exact density identity that transfers this constant from the new local energy term to $E'$, *define the successor `Terms` by subtracting the per-block value from their new local energy term* and set
$$E'_{n,\xi,p}B_n=S.Eppp(C)S.nU-e_{0,n}(\xi,p).\tag{4.3}$$
Prove $R_0(\xi,p;i)=0$ for every $i$ and all tori, and prove the values (4.3) form the same infinite-volume coefficient. This centering statement is indispensable: `RenormCond.val` reads `ElocInf` of `Terms` and does not mention $E'$, so choosing $E'$ without changing the new terms would not prove it. The *algebraic* consequence of (4.3) is already `Balaban.Fluctuation.StepSetting.vacuumEnergy_succ_eq_increment` (`Fluctuation/VacuumStep.lean`, lines 96–111):
$$E' = L^dE_k+\frac N2(L^d-1)\log(S.betaU)-\frac N2\log\frac{a_1L^d/L^2}{2\pi}-L^d\log\operatorname{fluctNorm}(N,p_1)-\frac{e_0}{B_n}.\tag{4.4}$$
The theorem assumes (4.3); it does not establish the constant-field identity or torus coherence. `StepSetting.cKernel_eq_betaU_mul` proves $S.cKernel=S.betaU\,a_1L^d/L^2$, which is solely the Gaussian normalization in (4.4). The vacuum constant is fixed *after* $\xi$ is chosen and supplies no extra equation for its three components. P4 notes this before (5.5), p. 708.

**Target `physical_H5_residuals_of_successor` (P4 (5.1)–(5.21), pp. 707–714).** Hypotheses are the provisional inherited-class step identity; $T'_{n,\xi,p}$ with exact `E`/`M` label sums on every torus; the choice $c=ab,d=b$; analytic complex charts in $\xi$; stabilization of the local value and first derivatives; convergence of the *weighted* transverse Hessian in (4.2); and $\beta_{k+1}>0$, $\varepsilon_{k+1}>0$. Conclusion is a **proved exact equivalence**, uniform in the torus,
$$R_h=R_\psi=R_2=0\quad\Longleftrightarrow\quad
A_k(p)\xi+c_k(\xi,p)=f_k(\xi,p),\tag{4.5}$$
where the left side means the precise three `RenormCond` clauses (with a separately supplied zero-field $R_h$ equation). More explicitly, (5.5), p. 708 computes $R_h,R_\psi$; (5.6)–(5.14), pp. 709–711 expands the second field derivative and computes $R_2$; dividing by the *nonzero* coupling and radius gives (5.21), p. 714; its linear terms are $A_k\xi$, and all remaining terms are assigned to $c_k$ or $f_k$. The term $A_k$ in (4.5) must be independent of $\xi$: P4 warns on p. 717 that $\beta_{k+1},\nu_{k+1}$ themselves depend on $\xi$. Freeze the linearization at the reference datum and include **all** resulting parameter variation in $c_k,f_k$, with the quadratic and forcing estimates below. Merely substituting $\nu_{k+1}(\xi)$ into `matrixInfty` would not fit `rg_step_infty`'s type `A : G → Matrix ...`, which has no $\xi$ argument.

The present general-class producer `Balaban.Inhabited.e0CoeffFamily_class_fromTower_of_irrelBounds_X` (`Fluctuation/LocalClassDensityIrrelChainX.lean`, lines 57–296) supplies, conditional on its per-label irrelevant bounds and many chart/radius premises, an analytic local family $e(\theta,T')$, its `E0locJ`/`densE0` sum identities, and exponential support bounds. It is fixed to $d=L=3,N=2$, positive field, and a `StepClass` with $m_0\ge7$. `zeroClassStep_sites_fromTowerG_rho` (`Inhabited/PhysicalZeroJoin.lean`, line 1403 in the earlier snapshot) supplies a common zero-class step witness. Neither conclusion states (4.2), computes the three physical derivatives in (5.5)/(5.14), nor proves (4.5) for an inherited physical class. `Balaban.Inhabited.renormCond_eTerms` (`Inhabited/V2Energy.lean`, lines 392–414) proves H.5 for a specially constructed `eTerms` witness whose infinite-volume local energy vanishes; it is not the fluctuation successor. These are the exact missing calculations, rather than an absence of analytic/local coefficient families.

## 4.2 Matrix and estimates required by `rg_step_infty`

**Target `physical_linear_matrix_of_successor` (P4 (5.21)–(5.22), pp. 714–715).** From the *computed* linearization in (4.5), prove on the complete positive-mass branch
$$A_k(p)=\operatorname{Flow.matrixInfty}(a,v,\tau,c_1,c_2,\varepsilon),\tag{4.6}$$
where $a=a_{k+1}$, $v=\nu_{k+1}$, $\tau$ and $c_1(v),c_2(v)$ are exactly the quantities in `Flow/MatrixInfty.lean`, lines 39–58. Prove the hypothesis `Flow.InftyRange a v τ c₁ c₂`: $9/10\le a\le3/2$, $0<v\le7/32$, $0\le\tau\le1$, $0<c_i<1/20$, and $0<c_1-vc_2<c_1$. In the $\nu$-free branch $k<k_0$, prove instead that $A_k$ is `Flow.matrixFree a v τ r ε`, including the **physical value** of the presently unspecified coefficient $r$ and the estimates $0\le v\le7/32$, $|r|\le C_r$, $vC_r\le12/5$; in a mixed convention prove $A_k=\operatorname{Flow.matrixSel}(k,k_0,\ldots)$. The needed real matrix inequality then follows without a new calculation from `Flow.triangularBounds_matrixInfty` (`MatrixInfty.lean`, line 247), `Flow.triangularBounds_matrixFree` (`MatrixFree.lean`, line 90), or `Flow.triangularBounds_matrixSel` (line 163), provided $0\le\varepsilon\le1$.

Precisely, `Flow.TriangularBounds` (`Flow/RGEquations.lean`, lines 196–208) says that the three above-diagonal entries vanish, the diagonal norms are at least $1/2,1,1/4$, and the remaining entries obey $|A_{10}|\le\varepsilon$, $|A_{20}|\le(5/2)\varepsilon$, $|A_{21}|\le3/2$. If $Ay=z$ and $\varepsilon\le1$, row elimination gives
$$|y_0|\le2\|z\|_\infty,\quad
|y_1|\le\|z\|_\infty+\varepsilon|y_0|\le3\|z\|_\infty,\quad
|y_2|\le4\bigl(\|z\|_\infty+(5/2)\varepsilon|y_0|+(3/2)|y_1|\bigr)\le42\|z\|_\infty.\tag{4.7}$$
This is exactly `Flow.TriangularBounds.norm_le`, not an estimate still to assign. `matrixInfty_conj`, `matrixFree_conj`, and `matrixSel_conj` establish conjugation of the **explicit matrices** once the parameter maps conjugate. `matrixFree_analyticOnNhd` establishes entrywise analyticity on $a\ne0$ for its stated three-coordinate chart and fixed $\tau,\varepsilon$. No corresponding parameterized `matrixInfty` analytic theorem was found; its rational entries require an open complex chart on which $a+v\ne0$. Pointwise real `InftyRange` does **not** by itself prove the `rg_step_infty` hypothesis `∀ p∈P, TriangularBounds (A p) ε` for an open complex $P$. A successor theorem must supply a uniform complex margin or choose a constant matrix parameterization and handle parameter continuity separately.

**Target `physical_nonlinear_bounds_of_successor` (P4 (5.3), (5.15)–(5.19), (5.24)–(5.25), pp. 707, 712–715).** For one open complex step-data domain $P$, the functions in (4.5) must satisfy *literally* the `rg_step_infty` premises: `AnalyticOnNhd` of each matrix entry on $P$, of $c_k,f_k$ on $\overline B(0,c_{10})\times P$; $\kappa>0$, $\eta_k\ge0$, $c_{10}>0$; and, for **every** $0\le r\le c_{10}$,
$$\|c_k(\xi,p)\|_\infty\le\kappa r^2\quad(\|\xi\|_\infty\le r),\qquad
\|f_k(\xi,p)\|_\infty\le\eta_k\quad(\|\xi\|_\infty\le c_{10}).\tag{4.8}$$
The quadratic estimate implies $c_k(0,p)=0$ and $D_\xi c_k(0,p)=0$. It cannot be replaced by a bound only at $r=c_{10}$. The source estimates needed are the constant-potential derivative bounds (5.3), the *weighted second spatial moment* for the new $t$ contribution (5.15)–(5.17), the corresponding irrelevant-energy moment (5.18), and its constant-field derivatives (5.19). P4 obtains (5.17) by writing $|x|^2=|x-z|^2+2(x-z)\cdot z+|z|^2$, applying the local second-derivative estimate (5.16), and summing the polymer decay with the $|Y|$ bound stated on p. 712. Its OCR obscures the displayed coefficient of (5.17), so the assignment must prove the literal Lean-scale inequality
$$\eta_k\le B\frac{2}{\alpha_0^2}\,\beta^{-1}q^{k+1},\qquad q=L^{-2\gamma_0},\tag{4.9}$$
from the actual localization and running-coupling bounds; (4.9) is exactly `rg_step_infty.hηbd`, corresponding to P4 (5.29), p. 716. The landed `e0CoeffFamily_class_fromTower_of_irrelBounds_X` gives a value bound and locality, but not the weighted `momentSum` convergence, the exact cancellations at $\xi=0$, or the nested-radius quadratic estimate (4.8). Its inherited irrelevant bounds are hypotheses. They must be provided by the provisional physical successor data, not silently inferred from the theorem name.

**Target `physical_reality_and_parameter_domain_of_successor` (P4 after (5.23), pp. 715–717).** Supply an involution $\sigma$ on $P$ preserving $P$ and prove
$$A(\sigma p)=\overline{A(p)},\quad c(\bar\xi,\sigma p)=\overline{c(\xi,p)},\quad
f(\bar\xi,\sigma p)=\overline{f(\xi,p)}.\tag{4.10}$$
The explicit matrix lemmas prove the first equality only after its scalar inputs are identified and conjugation compatible. The new-energy and old-irrelevant coefficient families must prove the latter two on one common complex chart. This is the route to real counterterms at a real physical datum; mere real values at one point do not establish the analytic family required for the $\nu\downarrow0$ comparison.

There is one numerical deduction that can already be made from (4.9). Put $C_*=\max(84\kappa,1/c_{10})$ and assume $B\ge0$, $\alpha_0,\beta>0$, $0\le q\le1$. Then
$$16(42\eta_k)C_*\le16\cdot42\cdot\frac{2B}{\alpha_0^2\beta}q^{k+1}C_*
=\frac{1344B C_*}{\alpha_0^2\beta}q^{k+1}
\le\frac{1344B C_*}{\alpha_0^2\beta}.\tag{4.11}$$
Consequently the explicit sufficient large-coupling condition $\beta\ge1344B C_*/\alpha_0^2$ proves `rg_step_infty.hcond`. The constants $\kappa,c_{10},B$ must be uniform in $k$, field, and torus. Formula (4.11) does **not** prove (4.9), nor does P4's damaged (5.27) justify replacing Lean's $42$ by an unverified smaller constant.

Given (4.6)–(4.10), `Balaban.Flow.rg_step_infty` (`Flow/RGInfty.lean`, lines 51–88) applies. The radius is $r_0=\min\{(16\cdot42\kappa)^{-1},c_{10}/2\}$. Cauchy bounds give a Lipschitz constant at most $4(42\kappa)r_0\le1/4$ for $-A^{-1}c$ and at most $(42\eta_k)/(c_{10}-r_0)\le1/8$ for $A^{-1}f$, hence a contraction. The theorem yields a unique $\xi_k(p)$ in that closed ball, analytic in $p$, real at $\sigma p=p$, and
$$\|\xi_k(p)\|_\infty\le84\eta_k
\le\frac{168B}{\alpha_0^2}\,\beta^{-1}q^{k+1}
=\operatorname{Flow.rgCxi}(B,\alpha_0)\,\beta^{-1}q^{k+1}.\tag{4.12}$$
The first inequality is the landed triangular contraction estimate, and the second is (4.9) multiplied by $84$. With $C=168B/\alpha_0^2$ and $c_8=4C/\beta$, `Flow.norm_xi_le_of_step` (`RGInfty.lean`, lines 96–105) closes the induction **if** each actual step supplies (4.9) from the earlier bounds. `Flow.rg_flow_infty` (`RGInfty.lean`, line 161) then gives the product limits under its additional $6Cq\le\beta(1-q)$. These are proved implications of the step targets, not producers of them.

## 4.3 Identification of the running coupling

**Target `physical_running_coefficients_of_successor` (P4 (4.1), (5.20), (5.28), pp. 699–700, 713–716).** For a provisional successor built at the *same* solution $\xi_k$ of (4.5), prove its action's actual normalized coefficients satisfy
$$\beta_{k+1}^{\rm phys}=\frac{L^{d-2}\beta_k^{\rm phys}}{1+\xi_k(2)},\qquad
\nu_{k+1}^{\rm phys}=L^2\nu_k^{\rm phys}\frac{1+\xi_k(2)}{1+\xi_k(1)},\qquad
a_{k+1}^{\rm phys}=\operatorname{compWeight}(L,a_1,k+1).\tag{4.13}$$
The nonzero denominators follow from (4.12) and $\|\xi_k\|\le1/4$ after the large-$\beta$ condition. P4's equations (5.20) establish the free $a$ choice, and (5.28) the first two recursions. In the landed objects, `Flow.betaSeq` and `Flow.nuSeq` (`Flow/RunningCoefficients.lean`, lines 63–75) are *definitions with exactly these recursive formulas*; `Flow.betaSeq_eq` and `nuSeq_eq` (lines 80–96) give, by induction from the physical initial values,
$$\beta_k^{\rm phys}=\beta L^{k(d-2)}\gamma_k,\quad
\nu_k^{\rm phys}=\nu L^{2k}\delta_k,\quad
\gamma_k=\prod_{j<k}(1+\xi_j(2))^{-1},\quad
\delta_k=\prod_{j<k}\frac{1+\xi_j(2)}{1+\xi_j(1)}.\tag{4.14}$$
The induction itself is elementary: the $k=0$ products are $1$; multiplying the first identity by $L^{d-2}/(1+\xi_k(2))$ appends the $(k+1)$st factor, and similarly for $\delta_k$. The *physical* premise (4.13), including equality of the coefficient extracted from the actual new action with these formulas, is missing. `Flow.betaSeq_eq` cannot identify an arbitrary `StepSetting.β` with the physical $\beta_k$.

This distinction is visible in the landed one-step tower. `StepSetting.betaU` (`Fluctuation/StepObjects.lean`, line 279) equals $S.\beta L^{k(d-2)}$, and `Balaban.Inhabited.hatStepKG_betaU` (`Inhabited/LevelStepSettingGeneral.lean`, line 99) proves the same for a tower step. `StepTower.scale` (`Inhabited/StepTowerScale.lean`, line 51) accepts arbitrary inputs $\beta,\nu$ **at each scale** and does not link different steps. At a physical flow step, the required inputs are $S.\beta=\beta\gamma_k$ and $S.\nu=\nu_k^{\rm phys}L^{-2k}=\nu\delta_k$: these are exactly `Balaban.SmallField.Def6v2.betaFine` and `physMass` (`SmallField/Def6v2Regime.lean`, lines 57, 68) evaluated at (4.14). Then `betaU` equals $\beta_k^{\rm phys}$. Passing the same bare $\beta,\nu$ to every independent tower step omits both $\gamma_k$ and $\delta_k$. The successor theorem must construct a coherent sequence of `StepSetting`s and prove both input identifications. `Balaban.SmallField.Def6v2.aIdeal_compWeight` and `physMass_succ_mul_sq`/`physMass_succ_renorm` (`Fluctuation/LocalClassInherit.lean`, lines 123, 144, 150) prove the **algebraic** weight and fine-mass relations once (4.13) is assumed. That file's docstring records a separate, unresolved inherited-domain inclusion at the *renormalized* mass, P4 (4.19), p. 704; it is part of the physical successor proof, not a consequence of the coefficient product formulas.

**Lean-facing completion theorem (`physical_coefficient_step_from_successor`).** Its parameters should be the old physical `IsSF`/`SFTermClauses`, `S : StepSetting`, `C : StepClass`, and a *provisional* torus-indexed successor `Tm' : ∀ N₁ [NeZero N₁], Terms d L N₁ m₁ (k+1) N ϱ`, together with the step's exact density identity and a `TorusIndep P.m₀ Tm'` proof. Its named hypotheses are precisely: (i) (4.3) plus the constant-field identity that proves `val`; (ii) existence and torus-independent limits in (4.2); (iii) the exact residual equivalence (4.5) at every physical datum and its separately normalized $\nu=0$ analogue; (iv) the `rg_step_infty` premises enumerated in §4.2, including (4.9) and (4.10); (v) the physical action extraction (4.13), the initial coefficients, and the numerical positivity/range needed by `CoeffBounds`. The conclusion is an analytic real $\xi_k$ with (4.12), `RenormCond P.m₀ (k+1) (ν_{k+1}^{\rm phys}) Tm' (k+1)`, and the three equalities (4.13). Its proof is short *conditional on those named hypotheses*: apply `rg_step_infty`; use (4.5) to obtain $R_h=R_\psi=R_2=0$; use (4.3) for `val`, the proved `Tendsto` in (4.2) for `moment`, and the positive-field `nuIdeal` premise for `dh`; then extract the action coefficients by (4.13). With the separate `beta_gt`, `nu_pos`, `nu_le`, `a_ge`, `a_lt`, and $c_8q\le1-q$ inequalities, extend the finite sequence $\xi$ by zero and use (4.14) to construct `CoeffBounds.flow` up to $k+1$. At $\nu=0$, `CoeffBounds.nu_pos` fails, so the massless coefficient theorem must remain a distinct explicitly normalized family; it cannot conclude `CoeffBounds` or use the positive-field `dh` field.

The exact dependency chain for an assignment is therefore: provisional successor `Terms` and step identity $\Rightarrow$ (4.2) with torus and zero-field control $\Rightarrow$ P4's computed equivalence (4.5), matrix identification (4.6), bounds (4.8)–(4.10) and rate (4.9) $\Rightarrow$ `rg_step_infty` and (4.12) $\Rightarrow$ action-coefficient identification (4.13) $\Rightarrow$ `betaSeq_eq`/`nuSeq_eq`, `rg_flow_infty`, and the coefficient premises of `C1StarFromStep`. The first arrow requires the local-to-weighted-moment estimate of P4 pp. 710–713; the second requires (5.21)–(5.25), pp. 714–715; the rate requires (5.29), p. 716; and the physical action identification requires (5.28), p. 716. None is supplied by `VacuumStep` or by a completed class assumed as a premise. Confidence is high in the stated interfaces, the algebraic and numerical implications, and the notation correction; moderate in the possibility of proving the physical estimates uniformly across $\nu=0$ on the current complex chart, since P4's scan and the landed inherited-domain gap both need direct resolution.
