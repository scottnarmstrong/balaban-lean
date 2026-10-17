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
