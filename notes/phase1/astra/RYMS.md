# R-YM: the complete-action $R$ window

17 October 2026.  This note concerns real unit external fields and scales $1\leq k\leq k_0$.  It does not address the separate small-field activity question on a complex source disc.  The answer is a **proved positive-mass extension of the landed real removed-window quotient**, followed by the exact additional input needed to turn it into the full $R$ window theorem.  The latter input is not supplied by the current landed objects, so (3.10) for the actual complete-background inherited activities is not yet a theorem.

## Sources and conventions

P7 is T. Balaban, *The large field renormalization operation for classical N-vector models*, Commun. Math. Phys. **198** (1998), 493–534.  Its journal pp. 509–512 contain (2.53)–(2.60); pp. 517–518 contain the reference integral (3.3)–(3.5); pp. 519–520 contain (3.7)–(3.10).  P5 is *A low temperature expansion for classical N-vector models. III*, Commun. Math. Phys. **196** (1998), 485–521; journal p. 495 contains (1.30)–(1.31).  Page-to-file keys are in `review/SOURCES.md` in the read-only repository.  I extracted P7 journal pp. 502–523 to `P7-pages-502-523.txt` and P5 pp. 494–497 to `P5-pages-494-497.txt` here.  Their prose is legible; some formula glyphs in the P7 text layer (notably primes, subscripts, and brackets) are garbled, so the exact formulas below are checked against the landed declarations and the unambiguous surrounding source, not silently reconstructed from those glyphs.

At one fixed scale $k$, the landed quotient uses local coefficients $\beta_0,\nu$ and the abbreviations $\beta_k=\beta_0L^{k(d-2)}$, $\nu_k=\nu L^{2k}$.  These are local coordinates for the actual running pair; they do not assert that the running flow has no multiplicative corrections.  Put $E=e^{2\epsilon}$.  In the early regime the flow gives $0\leq\beta_k\nu_k\leq E$ (`LF-RECONSTRUCTION.md`, (I.2) and (A-III.2)); $\epsilon\leq1/20$, hence $E\leq e^{1/10}$.  Set $\lambda=\lambda_k\geq1$ and $\delta_k=A_0\lambda^{p_0}/\sqrt{a\beta_k}$, so the available seed reserve is exactly

$$\mathcal R_k:=\beta_k\delta_k^2=\frac{A_0^2}{a}\lambda^{2p_0}.\tag{1}$$

The $R$ reference and every sharp test through $k_0$ use the massless solver.  The **weight** in the window uses $\mathscr A_\nu=\mathscr A_{\mathrm{free}}+\frac{\nu}{2}\sum_x|\phi_x-h|^2$, and inherited small-field terms use their complete backgrounds.  This is the route R-YM/A0′ convention of `Q13-YM.md` §5, not A0.  The landed `A0PrimeSupport.lean:chiY_zero_mass_h_free` verifies source independence of the massless support, and `A0PrimeWeight.lean:actionG_sub_massless`, `weight_real_bounds` verify the pointwise mass identity and real bound on a **fixed** field.  `A0PrimeReserve.lean:collar_reserve` accounts for one collar count; it does not allocate the same reserve a second time.

## 1. Exact positive-mass quotient

Here is a statement directly at the level of the landed $R$ objects.  It is stronger than the current specialization `RRemovedFracInst.lean:removed_quotient_le_of_history`, whose hypothesis `hν0` says $\nu=0$.

**Proposition 1 (complete-action removed quotient, conditional only on the named window estimates).**  Keep every typing, geometry, realness, exact-cancellation, and small-remainder hypothesis of `removed_quotient_le_of_history` (in particular `hid`, `hA0`, `hb`, `hst`, `hnu`, `hWP`, `hOp`, and the reference-tube hypotheses).  Delete `hν0`.  Assume instead $0\leq\beta_k\nu_k\leq E$.  Put $D_0$ for its box-side bound, $\gamma=\texttt{gammaW d}>0$, $B_*:=K_w\,\texttt{cF d L}$, and

$$S_\gamma:=e^{\gamma(2d+1)}\,\texttt{countConst d L}\,\gamma,\qquad C_m:=E\frac N2(4B_*+B_*^2)S_\gamma.\tag{2}$$

Assume $K_w\geq0$, as in the landed theorem.  If $C_{\widetilde E}$ is the old constant `CEt` (so it bounds `cTildeE` plus the massless oscillation constant in `hCEt`), the exact left side $Q_\nu$ of `removed_quotient_le_of_history`, with `actionRegionC ... ν` and `rhoZeroRestricted ... ν`, satisfies

$$Q_\nu\leq\exp\left[\frac N2\log\beta_k\,|Z_0|+(C_{\widetilde E}+C_m)D_0^d+C_\natural\lambda^{2d+1}+4+C_{k_1,k}\right].\tag{3}$$

In (3), $C_\natural\lambda^{2d+1}$ is precisely its `hnat` bound for `Cnat0`, and $C_{k_1,k}$ is its existing real parameter `Ckk`.  No complex-source or complete-solver estimate has been inserted into the hypotheses by a change of notation.  The action in $Q_\nu$ is the **complete** action, with the massless $R$ reference, exactly as in P7 (2.58), (3.3), and (3.7).

**Proof.**  Let $P_k$ denote the real threshold amplitude supplied as the argument named p0 in the Lean reference-radius definition.  Its radius is $\rho=C_6P_k/\sqrt{\beta_k}$ (`RhoZeroRestricted.lean:zeroRadius`); write $B=K_w\,\texttt{cF d L}\,\rho$.  The hypotheses `hρs` and `deltaStar_le_one` give $0<\rho\leq1$.  Thus $0\leq B\leq B_*$ and, term by term,

$$0\leq4B+B^2\leq4B_*+B_*^2.\tag{4}$$

The positive-$\nu$ theorem `CoreResponseOsc.lean:denominatorRestricted_bounds_of_margin_of_weighted` applies without $\nu=0$.  Its second conclusion bounds the absolute value of `tildeE0Restricted` by its massless constant, a boundary oscillation term, and exactly

$$T_m=\beta_0\nu L^{kd}\frac N2(4B+B^2)|Z_0|S_\gamma.\tag{5}$$

Here $L^{kd}$ means $(L^k)^d$, as in the Lean statement.  By the definitions of $\beta_k,\nu_k$,

$$\beta_0\nu L^{kd}=\bigl(\beta_0L^{k(d-2)}\bigr)\bigl(\nu L^{2k}\bigr)=\beta_k\nu_k\leq E.\tag{6}$$

The box cardinality theorem `card_boxFinset_le` gives $|Z_0|\leq D_0^d$.  All factors in (5) are nonnegative.  Combining (4)–(6) gives, with **no hidden constant**,

$$0\leq T_m\leq E\frac N2(4B_*+B_*^2)S_\gamma D_0^d=C_mD_0^d.\tag{7}$$

For completeness, the old boundary term is

$$T_b=\beta_k(d+1)N\{2\kappa_1B e^{2d\gamma}+(B e^{2d\gamma})^2\}e^{-\gamma R/2}|Z_0|S_{\gamma/2},\qquad \kappa_1=K_1K_6\delta.\tag{8}$$

The existing hypotheses give $0\leq\kappa_1\leq1$, $R=(2/\gamma)\log\beta_k$, and $\beta_k>0$.  Hence $\beta_ke^{-\gamma R/2}=\beta_ke^{-\log\beta_k}=1$, and

$$T_b\leq(d+1)N\{2B_*e^{2d\gamma}+(B_*e^{2d\gamma})^2\}S_{\gamma/2}D_0^d.\tag{9}$$

This is exactly the contribution already contained in `hCEt` and `RRemovedFracE.lean:removed_E_arith`.  Consequently

$$|\widetilde{\mathcal E}_{0,\nu}^{Z}|\leq(C_{\widetilde E}+C_m)D_0^d.\tag{10}$$

The denominator identity `RhoZeroRestricted.lean:denominatorRestricted_eq` is valid for $\nu\geq0$, and its denominator is strictly positive.  It has the form

$$D_\nu=\exp[-A_{Z,\nu}-(N/2)\log\beta_k|Z_0|+\widetilde{\mathcal E}_{0,\nu}^{Z}].\tag{11}$$

The numerator has the *same* $A_{Z,\nu}$: this is the identity `hid` and `RhoZeroRestricted.lean:removedFactor_le_restricted`, both already parameterized by $\nu$.  Divide its pointwise upper bound by (11).  The two $A_{Z,\nu}$ terms cancel exactly.  To see the remaining constant directly, call the nonnegative composed-Gaussian square $Q$.  In `RRemovedExponent.lean:cancelBracket_add_Cnat1_ge` the Gaussian contributes $Q/2$, `Cnat1` is at least $-3Q/8$, the multiplier square is at least $-1/4$, and `hnu` makes the linear mass term at least $-1/4$.  The positive mass square in `deltaActionC` only improves the estimate.  Therefore the bracket plus `Cnat1` is at least $Q/8-1/2\geq-1/2$.  The terms `hA0` and `hst` each cost $<1/4$, so their combined cost with the bracket is $<1$.  The landed `removedFactor_le_of_identity` uses the looser safe constant $1+3=4$.  Insert (10), `hnat`, and $C_{k_1,k}$ into `removedFactor_le_restricted`.  Since $e^x$ is increasing, the result is (3).  This proves every new inequality in the positive-mass step. $\square$

The mass term in (5) is the term that the current proof erases with `simp [hν0]`; it is **not** an unknown denominator contribution.  P7 journal p. 518 already retains the linear $\nu_k$ term in (3.3)–(3.4), while p. 520 pays the normalization and window volumes in (3.9)–(3.10).  The proof above is a real-domain extension of that calculation.

## 2. Paying the new cost once

The additional cost in (3) is $C_mD_0^d$.  The extended direction stencil has radius $\rho_k=2\lfloor R_b\lambda_{k-1}^2\rfloor+3$, so its collar count is $H_k=(2\rho_k+1)^d$.  For $1\leq\lambda_{k-1}\leq\lambda_k=\lambda$,

$$2\rho_k+1=4\lfloor R_b\lambda_{k-1}^2\rfloor+7\leq(4R_b+7)\lambda_{k-1}^2\leq(4R_b+7)\lambda^2,\quad H_k\leq(4R_b+7)^d\lambda^{2d}.\tag{12}$$

This is the same arithmetic as `A0PrimeReserve.lean:collar_reserve`.  To pay both the collar and (7), rather than spend the reserve twice, choose a fixed $0<\theta<1$ for all the *other* large-field charges and require $p_0>d$ and

$$\lambda\geq\max\left\{1,\left(\frac{2a(4R_b+7)^d}{(1-\theta)A_0^2}\right)^{1/[2(p_0-d)]},\left(\frac{2aC_mD_0^d}{(1-\theta)A_0^2}\right)^{1/(2p_0)}\right\}.\tag{13}$$

Each term in (12) and (7) is then at most $(1-\theta)\mathcal R_k/2$, by multiplying the two power inequalities in (13) by the appropriate nonnegative power of $\lambda$.  Thus

$$H_k+C_mD_0^d\leq(1-\theta)\mathcal R_k.\tag{14}$$

The old `collar_reserve` hypothesis only proves $H_k<\mathcal R_k$; it does **not** imply (14).  Equation (13), or a direct hypothesis (14), is the minimal reserve change.  The fixed constants $a,R_b,D_0,K_w,\texttt{cF},\gamma$ have to be fixed as functions of the design parameters before $\lambda_*$ is chosen.  Consequently (13) gives constants depending on $d,L,N,p_0,A_0$ **after** those fixed geometric and background choices; the source does not justify pretending that an arbitrary independently chosen $R_b$ or $K_w$ is bounded by a function of $d,L,N,p_0,A_0$.

The same argument absorbs a source cost $C\lambda^q$ provided $q<2p_0$: replace the second threshold in (13) by $[2aC/((1-\theta)A_0^2)]^{1/(2p_0-q)}$.  Indeed, if $\nu_{\max}(k)\leq C_\nu\lambda^{p_2}$ and $\mathrm{crit}_k\leq C_{\mathrm{crit}}\lambda^2$, then

$$\nu_{\max}(k)(M\,\mathrm{crit}_k)^d\leq C_\nu(MC_{\mathrm{crit}})^d\lambda^{p_2+2d}.\tag{15}$$

This is the full window count $q=p_2+2d$ of Lemma III.1.2(c) of the reconstruction, for which the project's choice $p_2=2d+3$, $p_0\geq d^2+7d+2$ has $2p_0>p_2+2d$.  A factor proportional to the *sum of quiet-step volumes* must instead be charged to the slack in their per-volume weights, as in `LF-RECONSTRUCTION.md` D-III.5 and III.8.7; one cannot spend one component's seed reserve once per quiet step.

## 3. The integrated window inequality

The quotient estimate feeds the real part of P7 (3.7)–(3.10) as follows.  This statement makes the remaining input visible.

**Proposition 2 (complete-action window integral).**  Suppose the actual R-YM removed-window integrand is nonnegative, vanishes off the common massless support, and has the exact pointwise factorization used by the landed window theorem: a core factor, a window boundary factor, the composed-Gaussian constant, and the quotient $Q_\nu$.  Assume the real quiet-step bound

$$b_{\rm win}\leq\sum_{j=k_1}^{k-1}(C_b\log\beta_j+C_bB_0)|X_j|_{j+1},\qquad
C_{k_1,k}\leq C_{15}\sum_{j=k_1}^{k-1}|X_j|_{j+1},\tag{16}$$

and the same shell/ball volume and core-integral bounds used in the massless proof of Lemma III.8.7 of the reconstruction.  Let $V_k$ be their total residual cost, including the factors $|Z_0|N\log\beta_k/2$, $C_{\widetilde E}D_0^d$, $C_\natural\lambda^{2d+1}$ and the safe constant $4$ from (3), but excluding the new mass term.  Suppose $V_k\leq C_R\lambda^{2d+1}$, as in (III.8.4), and let the core bound be $\exp(-\sum_C\kappa_{k_1}(C))$.  Then the complete-action removed-window operator satisfies

$$\int K_\nu^{\rm rem}e^{b_{\rm win}+E_k|Z|}\leq
\exp\left[-\sum_C\kappa_{k_1}(C)
+\sum_{j=k_1}^{k-1}\bigl(C_b\log\beta_j+C_bB_0+C_{15}\bigr)|X_j|_{j+1}
+C_R\lambda^{2d+1}+C_mD_0^d\right].\tag{17}$$

The measure in (17) integrates all window, top-block, and internal variables in the order of P7 p. 519, and $E_k|Z|$ is included in $V_k$.  Formula (17) is the precise complete-action counterpart of the **real majorant** in P7 (3.9)–(3.10); (14) pays its one new fixed-window cost from the unused part of the seed reserve.  The final $-\!p_2(\beta_k)-H_k|Z|$ version additionally uses the already separate history charge (P5 (1.30), P7 (3.8)) and the quiet-step refund.  No conclusion about the analytic operator norm is made from this real inequality alone.

**Proof.**  At each point of the common support, substitute (3) for $Q_\nu$ and the first bound of (16) for the boundary factor.  Exponent addition gives the two sums in (17), the old residual terms collected in $V_k$, and exactly $C_mD_0^d$.  The resulting bound is uniform in every core variable.  The shell/ball volume hypothesis bounds each remaining window integral by its stipulated volume factor; Tonelli applies because the integrand is nonnegative.  Integrate the core factor last and use its stated bound.  Finally use $V_k\leq C_R\lambda^{2d+1}$.  Each operation preserves the inequality, so (17) follows.  The new cost is a single factor independent of the number of quiet steps. $\square$

## 4. What remains before (3.10) for the actual route

The argument above is a complete proof of (3) **with its explicit hypotheses**, not a proof that a complete-background small-field history satisfies those hypotheses.  There are three genuinely different assertions.

1. **The algebra and the denominator.**  These are now covered on the real domain by Proposition 1.  `CancelStationary.lean:cancellation_identity` and `RhoZeroRestricted.lean:removedFactor_le_restricted` carry a positive $\nu$ in the complete action while their reference is `phiZero`, the massless one.  `CoreResponseOsc.lean:denominatorRestricted_bounds_of_margin_of_weighted` already supplies (5).  This removes `hν0` from the mathematical quotient estimate with the stated extra constant.

2. **The actual complete-background inherited terms.**  `ActionConvWindow.lean:WindowSetup.windowAction`, `Awin`, `bgRem`, `ActionConvInput`, and `window_conversion` have a $\nu$-parameter and a `MassBranch`, but the estimates `variational_bound`, `cube_bound`, `wall_bound`, `p7_first`, and `window_decay` are fields of `ActionConvInput`, not theorems for the R-YM history.  They must be proved for the *same complete-background inherited terms* appearing in the density.  The exact $\nu$-free window-action bound does not transport merely from `A0PrimeWeight.lean:weight_real_bounds`: that theorem compares two actions at one field and one support; a complete and a massless minimizer, their collars, and their inherited $E,F$ terms are different arguments.  P7 p. 511 explicitly treats (2.58) as an identity of the action being integrated, not as a bound on an independently chosen weight.  This is the precise missing source-to-Lean input for the full (3.10).

3. **The small remainders and support.**  Proposition 1 retains `hA0`, `hb`, `hst`, `hnu` and `hid`.  Their intended quantitative route is P7 (2.41), (2.49), (2.59)–(2.60) and `LF-RECONSTRUCTION.md` Lemma III.6.4, (Λ25)(a)–(c), with the real inequality $\beta_k\nu_k\leq E$.  For example, if $n_w$ is the weighted number of sites in the window and $|\delta\phi_x|\leq u$, then unit $h,\phi^0_x$ give, at every site,

$$\left|\beta_k\nu_k\langle\delta\phi,\phi^0-h\rangle_w\right|\leq\beta_k\nu_k\sum_xw_x|\delta\phi_x||\phi^0_x-h|\leq2E n_wu.\tag{18}$$

Thus $2En_wu<1/4$ is an explicit sufficient `hnu` estimate; the source obtains $u$ from the window background response, not from the reserve.  The complete action also has $+(\beta_k\nu_k/2)\sum_xw_x|\delta\phi_x|^2\geq0$ on real fields, as used in `RRemovedExponent.lean:cancelBracket_add_Cnat1_ge`.  The source-free support identity is landed, but the actual complete-background inherited factors and the strict tube/collar comparison remain separate obligations (`Q13-TRANSFER.md`; `Q13-DECISION.md` §5).  For the real estimate one may keep the displayed `hA0`, `hb`, `hst`, `hnu` as named source premises; removing them requires those quantitative response proofs.  Complex analyticity of the final $R$ operator requires its own bounds and is outside Proposition 1.

The necessity of a response hypothesis is literal.  On $n$ independent hard-spin sites take $\phi^0=-h$, $\phi^u=h$, and $\beta_k\nu_k=E$.  Then $\delta\phi=2h$, $\phi^0-h=-2h$, and the linear term in (18) is $-4En$.  The positive mass square is $+2En$, so their sum is $-2En$.  No bound independent of $n$ follows from $\beta_k\nu_k\leq E$ alone.  This is **not** a counterexample to the actual R window: it violates the small-background-change bound that the window characteristic functions and P7 (2.41), (2.49) are meant to supply.  It identifies why replacing that bound by “the reserve is large” is invalid unless the window site count and the allocation (14) are also proved.

## Lean shape and consequence

The first Lean declaration should be an extension of `Balaban.LargeField.removed_quotient_le_of_history` in a new scratch proof module, leaving all its current binders unchanged except: remove `(hν0 : ν = 0)`; add `(hβν : β0 * ν * (S.L : ℝ) ^ ((k' + 1) * S.d) ≤ E)` and `(hE : 0 ≤ E)`; add $C_mD_0^d$ from (2) to its right-hand exponent.  Equivalently use `betaK ... β0 * (ν * L^(2*k)) ≤ E` with `k=k'+1`.  Apply `denominatorRestricted_bounds_of_margin_of_weighted`, `removed_E_arith`, (4)–(7), and `removedFactor_le_restricted`; no definition change is needed.  A separate arithmetic lemma should strengthen `collar_reserve` to (14), with an explicit fraction reserved for the other charges.  The next, genuinely analytic declaration must instantiate `ActionConvInput` for the complete inherited activities on the common massless support and prove the four small-remainder hypotheses rather than placing those proof steps into a new public class.

Proposition 1 unblocks the **positive-$\nu$ real quotient** used as `hfrac` by `RRemovedWindow.lean:removedKernel_kerBound_of_window`, up to the explicit additional $C_mD_0^d$ and reserve allocation.  With the complete inherited-action conversion, the small remainders, and the already separate support/volume/core bounds, the pointwise integration argument of `RRemovedWindowPoint.lean:window_pointwise_le` gives the analogue of P7 (3.10) with this extra exponent.  It does not by itself close Blocker 2 or prove the source-radius activity estimate.

**Confidence.**  High for (3)–(14): they are direct algebra and inequalities from the cited positive-$\nu$ landed statements.  Medium for the proposed full $R$ window route, because the complete-background `ActionConvInput` and the required quantitative response/support instances have not been proved.  I found no physical real-field counterexample to the full estimate under those intended window hypotheses.
