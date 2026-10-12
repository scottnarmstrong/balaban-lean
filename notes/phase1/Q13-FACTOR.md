# Q13, round 18: the hybrid factor and the $R$ window

## Result

**The two requested theorems are not presently proved.** The algebraic part of the $R$ cancellation extends to a complete window field: the landed proof uses its massless Euler–Lagrange hypothesis only to obtain the unit-length constraint. The resulting mass-response errors have explicit bounds below. Their absorption requires the actual window counts and a physical-mass reference-density theorem. The landed `rhoZero` has mass zero in its action, despite the physical mass in P7 Definition III.8.1.

The proposed exact small-field factorization has a more serious missing step. Inherited $E$, $F$, and $R$ terms are restricted to the old small-field region. When that region shrinks, the P5 (1.8) correction and polymer sums have nonzero boundary flux, and the composed field itself changes. Inserting one massless cutoff partition is exact, but it does not identify the resulting conditional integral with an LF step kernel satisfying (S0)–(S5). Thus A0′ remains a construction to try; variant A remains the recorded Q13 decision. The one-block RGFREE-3/RGFREE-6 switch counterexamples do not obstruct A0′'s *real* cutoff algebra, but they do not prove its complete small-field complex class.

## 1. Exact finite algebra and the failed factorization step

Use four parameter roles. At $j\le k_0$, set $\mu_{\rm cut}(j)=\mu_{R\rm ref}(j)=0$, while $\mu_{\rm actBg}(j)=\mu_{\rm act}(j)=m_j=\nu_jL^{-2j}>0$. Above the crossing use the prescribed complete mass for the action and solver; the reference mass is needed only at an $R$ operation. The background in inherited $E$, in the leading and marked $F$ terms, and in the action factor must use $\mu_{\rm actBg}$; the physical action must use $\mu_{\rm act}$; the background-dependent sharp $\chi,\chi'$ predicates must use $\mu_{\rm cut}$. `chiNew` has no background mass argument. The $R$ centre and its Gaussian expansion use $\mu_{R\rm ref}$. These are distinct *roles*, even when two values coincide. `Quiet.lean:quietKernel`, lines 153–193, currently passes one `OpConsts.mu` to `chiK`, both `chiPrimeNew` factors, `chiNext`, `InUnionDomainR`, and `mainActionLoc`; it cannot implement this convention. `Def7v2Form.lean:actStar2` already separates `muAct` from the solver's `mu`, but `EresJ2`, the background-dependent parts of `Fres`, and `chiY` still use that solver mass. `Rres` depends on the source and lifted field but has no separate solver-mass argument. `D1Form2` is a representation clause for an abstract sum of LF operators, not a derivation of an LF operator from the complete SF conditional integral.

Here is the exact regional identity that any construction must transport. At inherited scale $j$ put $R=C.\mathrm{alignedIn}_j(Y)$, $B=C.\mathrm{alignedIn}_j(\operatorname{thick}Y)$, and for the smaller region $Y'$ put $R'\subset R$, $B'\subset B$. Set $D=R\setminus R'$. For one common composed field $\psi$, write
$$P_B(y;\psi)=\sum_{X\ni y,\ X\subset B}E_j(y,X;\psi),\qquad
\mathcal C(A,B;\psi)=\sum_{y\in A}\sum_{x\in B}c_j(y,x;\psi,h),$$
where $c_j$ is the *full* `corrPair` with both P5 coefficients $v_1,v_2$ and the physical $\nu_jh$. Then `EresJ2` is $\mathcal E(R,B;\psi)=\sum_{y\in R}P_B(y;\psi)-\mathcal C(R,B;\psi)$. Finite additivity, and absolute convergence for the polymer sums, give
$$\begin{aligned}
\mathcal E(R,B;\psi)-\mathcal E(R',B';\psi)
={}&\sum_{y\in D}P_B(y;\psi)
+\sum_{y\in R'}\sum_{X\ni y,\ X\subset B,\ X\not\subset B'}E_j(y,X;\psi)\\
&-\mathcal C(D,B;\psi)-\mathcal C(R',B\setminus B';\psi). \tag{1.1}
\end{aligned}$$
For the actual two regional fields add exactly
$$\mathcal E(R',B';\psi_Y)-\mathcal E(R',B';\psi_{Y'}). \tag{1.2}$$
Thus (1.1)–(1.2) are **PROVED algebraically**, conditional only on the stated nesting and summability. The last term is a genuine change of evaluation, while the second polymer sum and last correction in (1.1) are genuine boundary flux. They cannot be dropped by antisymmetry: `Def7v2Corr.lean:corrSum_singleton` and `corrSum_ne_zero_example` give $v_1=1,v_2=0$, a one-pair correction $\tfrac12(\psi^2(x)-\psi^2(y))\ne0$. The unrestricted self-sum vanishes, but P5 (1.8) uses $R\times B$, generally with $R\ne B$.

The same support bookkeeping applies to the full exponent
$$V_Y=-\beta A^*_{m}(Y;\phi^m_Y)+\sum_{j\le k}\mathcal E_j(Y;\psi^m_{j,Y})-E_k|Y|_k
+F_Y(\phi^m_Y,g)+R_Y(g). \tag{1.3}$$
Specifically, `Def7SmallField.lean:Fres` has its leading $g\phi^m_Y$ sum on `bgSet Y` and its marked-polymer sum over $x\in Y$, $X\subset Y^\approx$; `Rres` has $X\subset Y$. Their difference between $Y$ and $Y'$ consists of the deleted supports, crossing polymers, and re-evaluation on the retained supports. The action difference also has half-star bonds and the changed regional background. None is absorbed by declaring only $\mathcal E_{Y'}$ to be the new SF complement.

Let $d\gamma_k$ denote the actual one-step conditional Gaussian measure and let $\chi^-_k(C)$ be the inner massless predicate defined in §3. Inserting
$$1=\sum_{S\subset\pi_k}\prod_{C\notin S}\chi^-_k(C)\prod_{C\in S}(1-\chi^-_k(C)) \tag{1.4}$$
under the conditional integral is an **exact identity**, subject to ordinary integrability/Fubini. For a fixed branch with old region $Y$ and new complement $Y'$, one can always write, pointwise,
$$e^{V_Y}\prod_{C\notin S}\chi^-_k(C)\prod_{C\in S}(1-\chi^-_k(C))
=e^{V_{Y'}}K^{\rm formal}_S,\quad
K^{\rm formal}_S:=e^{V_Y-V_{Y'}}\prod_{C\notin S}\chi^-_k(C)\prod_{C\in S}(1-\chi^-_k(C)). \tag{1.5}$$
This is only an algebraic quotient of exponentials. The proposed LF kernel must in addition contain the conditional Gaussians, all new/prime/domain indicators, the physical `mainActionLoc` at $\phi^m$, the exact $\Delta V$ of (1.1)–(1.3) assigned to each new component, and the correct $g$-marked exponent. It must depend only on the allowed new variables and local parameters, factor across localized components, and satisfy (S0)–(S5). The actual `StepData.ker` is abstract and `quietKernel` has the one-mass definition above. **OPEN:** an equality between the *actual complete SF conditional integral* and a product of such admissible LF kernels times `sfFactor2` on $Y'$. The precise failed inference is from (1.5) to that admissible localized kernel. Accordingly `regionalEnergyIdentity` is not a tautology of the current definitions; (1.1) is its indispensable algebraic part, and a locality/assignment theorem for (1.2) and the other factors remains. Any estimate for the flux is charged to the component that creates the boundary, with its crossing-bond/polymer count, before applying (S2); it cannot be called a free per-window constant.

## 2. The mass response in the $R$ window

Retain P7's massless reference $\psi_k^0,\phi_k^0$, and use the *same* physical datum and full collar to define the complete window field $\phi^m_u$ and its massless counterpart $\phi^0_u$. The exact decomposition is
$$\delta\phi=\phi^m_u-\phi_k^0
=u_m+u_7,\quad u_m:=\phi^m_u-\phi^0_u,\quad u_7:=\phi^0_u-\phi_k^0. \tag{2.1}$$
Under `massChange_sameData_response_unit` and all its Green, background-bound, smallness, and common-data hypotheses, put $W=K_mB_h\nu_k$, $K_m=\sqrt N K_w$, $B_h=2$ for real unit $h$. Then the site, scaled derivative, scaled Laplacian, and multiplier norms of $u_m$ are at most $W$. If the old P7 bounds are $|u_7|\le D_7$, crossing average $\le U_7$, reference multiplier $\le A_7$, and reference outward derivative $\le T_7$, one may use $D_7+W$, $U_7+W$, $A_7$, $T_7$ in `CancelRemaining.lean`. Here $N_D=|D.\mathrm{sites}|$, $N_\partial=|D.\mathrm{crossing}|$, and $N_0=|Z_{k+1}.\mathrm{sites}|$ are the *actual* fine site/bond counts, with $\beta_0$ the corresponding fine-unit coupling.

**PROVED CONDITIONAL ON these pointwise inputs:** the changed numerical premises of `remaining_terms_of_lemma262`, which are the operational form of $(\Lambda25)(a)$–$(c)$, are
$$\begin{array}{ll}
(a)&\beta_0[\tfrac12 dN_0 B_\nabla^2+\tfrac12 N_0B_{\rm mass}]<\tfrac14,\\
(b)&\tfrac12\beta_0N_D A_7(D_7+W)^2<\tfrac14,\quad
\tfrac12\beta_0N_D(A_7+\nu_k)(D_7+W)^2<\tfrac14,\\
(c)&\beta_0N_\partial(U_7+W)T_7<\tfrac14,\quad
\beta_0\nu_kN_D(D_7+W)B_\phi<\tfrac14,\quad B_\phi\le2. \tag{2.2}
\end{array}$$
Premise (a) uses the unchanged massless reference and already includes its physical mass term if `Lemma262` is instantiated with $\nu_k$. Relative to the old P7 budgets, the increments in (b) are $\tfrac12\beta_0N_D A_7(2D_7W+W^2)$ and $\tfrac12\beta_0N_D(A_7+\nu_k)(2D_7W+W^2)$; in (c) they are $\beta_0N_\partial WT_7$ and at most $2\beta_0\nu_kN_DW$. In scale-$k$ units the last increment is at most $2K_mB_h\beta_k\nu_k^2N_{\rm win}\le2K_mB_hE\nu_kN_{\rm win}$, where $E=e^{2\epsilon}$ and $N_{\rm win}$ is the normalized window site count. This is a genuine count-dependent condition, not an automatic eighth. Choose the old estimates with strict spare budgets first, then choose the parameters so *each displayed increment* is below its spare budget, using the actual P7 window-count bound. This count and budget implication is **OPEN** for the hybrid.

The cancellation algebra itself has a useful extension. `CancelIdentity.lean:cancel_expansion` accepts an arbitrary actual $\phi_u$ subject to $\phi_u\cdot\phi_u=1$. In `cancel_core`, the only use of `hELu : IsEL ... 0 Du φu αu` is `hELu.2` at line 956, to pass precisely that constraint to `cancel_expansion`. Replacing `hELu` by the unit-length hypothesis leaves the proof unchanged. **PROVED at the source-proof level, pending a new Lean declaration:** (2.58′) therefore holds for the complete $\phi^m_u$, with $u_m$ included in $\delta\phi$, provided the *reference* $\phi_k^0$ has the existing stationary and geometry hypotheses. This does not grant any smallness in (2.2).

The fourth part, $(\Lambda25)(d)$, is the Gaussian coefficient correction, with `CancelBound.lean:Cnat0_le` giving
$$|C_0^\natural|\le n\{36\beta_k\eta_k\rho^2+8\beta_k\rho s+9\beta_k s^2+N\eta_k\},\quad
|C_1^\natural|\le\tfrac38\sum_z\beta_ka_z^\natural|Q_z\delta\psi|^2. \tag{2.3}$$
Use **36, 8, 9, 1**, as in ERRATA ER-236, rather than the smaller printed values. For the *same data* $D_u$, $u_m$ does not change $r_z,s_z,\eta_k$, so (2.3) gets no mass-response increment. Each of its four summands must fit its designated quarter bound. This is **PROVED CONDITIONAL ON** the landed coefficient hypotheses and the original $(\Lambda19)$ parameter implications.

For action conversion on a union of verified new cubes, `massChange_region_bound_cubes` supplies the additional cost
$$q_k n,\qquad q_k=C_D\beta_k\nu_k^2+C_W\beta_k\nu_k\delta_0,
\quad C_D=(d+2)M^dL^2K_m^2B_h^2,\quad C_W=2dM^{d-1}L^2K_mB_h, \tag{2.4}$$
where $n$ is the normalized cube count and $\delta_0=G_\nabla\delta_k$ is a permissible background-bound radius. Thus $q_k\le C_DE^2/\beta_k+C_WE G_\nabla\delta_k$. The theorem requires the exact spacing, cube cover, site count, wall gradient, and same-data hypotheses in `MassChangeCrossing.lean:massChange_region_bound_cubes`; it is not a generic estimate on an arbitrary history region. On the fixed core $Z_0$, a verified count $N_0\le D_0^d$ makes (2.4) a fixed $C_R$ cost. On the variable window it grows with $n$ and must be paid per cube by the quiet-step refund of P7 Lemma III.8.7, after a proof that $q_k$ is smaller than the available refund. **OPEN:** that assignment and the action-conversion estimate for all inherited layers.

There is also a reference-density mismatch. `RhoZero.lean:effActionNorm` is `effAction G a ψ/L^{k(d-2)}` with mass **zero**, and `rhoZeroWith` uses it; `Denominator.lean:denominator_eq` proves the corresponding massless integral identity. P7 Definition III.8.1 and LF-RECONSTRUCTION III.8.1 instead use the physical $\nu_k$ action evaluated at the massless reference background. The landed `rhoZero` and `denominator_eq` therefore do **not** establish the physical reference denominator required by (2.58′). One may use a common landed massless denominator and carry the physical core mass factor in the numerator, bounded by $2E$ per real action site, but then III.8.2 and the $R$ normalization/window estimate must be reproved with that factor. Alternatively define a new physical-mass `rhoZero` and redo positivity and `denominator_eq`. Both routes are **OPEN**; the note adopts the latter to match P7 exactly.

## 3. Chosen overlap margin and exact cutoffs

Fix $0<\sigma<1/4$ before the large-parameter choices. In *every* real sharp test of `chiK`, both `chiPrimeNew` factors, `chiNext`, and the SF `chiY`, evaluate the background at $\mu_{\rm cut}=0$ and replace its geometric tolerance $t$ by $(1-\sigma)t$; the mixed tests with original $3\delta_j/4$ and $5\delta_j/4$ therefore use $3(1-\sigma)\delta_j/4$ and $5(1-\sigma)\delta_j/4$. Keep their structural conditions, including the massless `InUnionDomainR`, and the original $\chi^{\rm new}$ fluctuation conditions. Use **these same indicators on both sides** of (1.4). The complement includes the shell between inner and original radii, and needs its own failure gain. This is an exact nonnegative partition; no comparison of two sharp indicator functions is made.

Let $\delta_j=A_0\lambda_j^{p_0}/\sqrt{a\beta_j}$, $\eta_j=C_{\rm dat}\delta_j$, $\beta_j\nu_j\le E$. Suppose `cutoffDataRegularity` holds as follows: for every actual restricted generating set and *full collar* created by `WindowOfHistory.lean:windowOfHistory_hyp` (including the old, new, prime, and mixed supports), every datum selected by the inner massless predicate has P2 R1 and R2 left sides at most $\eta_j/2$, with $\eta_j\le c_1/2$; the data of the massless and complete solver are identical. This is **OPEN**. `windowOfHistory_hyp` supplies the glued generating-set geometry, not these data inequalities. A proof must push the actual `chiS`, `chiZDD`, `chiK`, and mixed tests through the P5 data estimates on that collar; an assertion just for a single cube is insufficient.

Conditional on this input, real unit $h$ gives P2 R3 at most $2\nu_j$ and R4 zero. Choose $\lambda_*$ after $C_{\rm dat},A_0,\sigma,E$ so
$$\eta_j\le c_1/2,\quad
\lambda_*^{2p_0}>\frac{8aE}{C_{\rm dat}^2A_0^2},\quad
2\sqrt{\nu_j}<\tfrac34(1-\sigma)\delta_j,\quad
2K_mB_h\nu_j\le\tfrac38\sigma\delta_j. \tag{3.1}$$
The first two conditions give $2\nu_j<\eta_j^2/4$, hence the positive-mass real BG domain with the displayed R1–R4 margins. Apply BG existence and bounds **before** `massChange_sameData_response_unit`; this avoids assuming the response to prove existence of its own complete solution. The last two conditions and the response estimate imply every complete ordinary test lies at least $\sigma\delta_j-2W_j\ge5\sigma\delta_j/8$ below $\delta_j$, and every complete $3\delta_j/4$ mixed test lies at least $3\sigma\delta_j/4-2W_j\ge3\sigma\delta_j/8$ below its outer threshold. The $5\delta_j/4$ test has still more slack. Thus **`hybrid_regular_overlap` is PROVED CONDITIONAL ON** `cutoffDataRegularity`, BG existence/bounds, and the response hypotheses. The ratios to check uniformly are
$$\frac{2W_j}{\delta_j}\le\frac{2K_mB_hE\sqrt a}{A_0\lambda_j^{p_0}\sqrt{\beta_j}},\qquad
\frac{2\sqrt{\nu_j}}{\delta_j}\le\frac{2\sqrt{aE}}{A_0\lambda_j^{p_0}}. \tag{3.2}$$
Choose the fixed constants and $\sigma$ first, then $\lambda_*$ and the lower bound on $\beta_j$ so (3.1)–(3.2) hold, then the remaining row-16 entropy/refund choices. A literal cutoff at $\delta_j$ has no uniform distance from its threshold; (3.1) would not repair that. The smaller cutoff lowers a quadratic failure gain by $(1-\sigma)^2$ before entropy costs, so its nonquiet (S2) proof is **OPEN** until every complement label, including a failed domain test, has a witness-to-action estimate.

## 4. What remains of Q13 (five lines)

1. **OPEN:** the actual complete SF conditional-integral factorization with (1.1)–(1.3) and admissible LF kernel locality.
2. **OPEN:** `cutoffDataRegularity` on every glued history/collar and the inner-shell/domain-failure (S2) gain.
3. **OPEN:** physical-mass `rhoZero`, `denominator_eq`, and parameter closure of (2.2) with true window counts.
4. **OPEN:** allocation of (2.4) per new cube, all inherited action conversions, and the complete-action (S5) analytic bound.
5. Until these hold, A0′ does not replace variant A; the frozen root with fixed real unit $h$ does not demand a mass-uniform transverse complex $h$ disc.

## 5. Lean work list and current status

Each item is a worker lemma/module of roughly 300 lines or less, with its required derivation indicated. No source-tree edit is made here.

1. `HybridMasses` and `hybrid_partition`: **PROVED algebraically, Lean OPEN.** Introduce `muCut`, `muActBg`, `muAct`, `muRRef`; instantiate background-dependent sharp predicates with `muCut` and prove (1.4). Generalize `OpConsts.mu` consumers `chiK`, `chiPrimeNew`, `chiNext`, `InUnionDomainR`, `mainActionLoc`, `SFCtx.phiBar`, `psiJ`, `Fres`, `EresJ2`, and `chiY` to their respective roles; retain the mass-independent `Rres` and `chiNew` definitions with their exact supports.
2. `hybrid_corr_region_sub` and `hybrid_polymer_region_sub`: **PROVED algebraically, Lean OPEN.** Finset subtraction and tsum splitting prove (1.1); add (1.2), the marked $F$ and $R$ analogues, and action half-bond splitting. Preserve the full `corrPair` rather than replacing it by a self-sum.
3. `hybrid_sf_factorization`: **OPEN.** Derive the physical conditional-integral equality with the kernel defined by actual localized variables, not by the formal quotient (1.5); then prove locality and (S0)–(S5). Existing `D1Form2` is a target form, not its proof.
4. `cancel_core_of_unit` and `hybrid_delta_phi_split`: **PROVED at source-proof level, Lean OPEN.** Replace only the actual-field `hELu` input of `cancel_core` by hard-spin unit length; use (2.1) and `massChange_sameData_response_unit`. Keep the massless reference `psiZero_spec` hypotheses.
5. `hybrid_R_remaining_bounds` and `hybrid_Cnat_bound`: **PROVED CONDITIONAL ON landed pointwise bounds, Lean OPEN.** Feed $D_7+W,U_7+W$ into `remaining_terms_of_lemma262`; retain (2.3) with 36,8,9,1 and the same-data coefficient inputs. Prove the numerical $(\Lambda25)$ closure separately from the true P7 counts.
6. `rhoZeroPhysical`, `denominatorPhysical`, `hybrid_R_normalize`: **OPEN.** Add the physical mass to the reference action while keeping the massless background; reproduce positivity, the change-of-variables proof of `denominator_eq`, and the common-denominator normalization.
7. `cutoffDataRegularity`, `hybrid_regular_overlap`, `hybrid_inner_complement`: first **OPEN**; second **PROVED CONDITIONAL ON** the first and BG/response hypotheses; third **OPEN**. Use `windowOfHistory_hyp` for the actual glued sets, then (3.1)–(3.2), followed by the witness-to-action gain.
8. `hybrid_region_action_cost` and `hybrid_quiet_refund`: first **PROVED CONDITIONAL ON** `massChange_region_bound_cubes` hypotheses; second **OPEN**. Derive (2.4) on every assigned cube and compare its coefficient with P7 III.8.7 before claiming (S2).

## Sources checked

P5 pp. 489–490, (1.8)–(1.9), (1.10)–(1.17); P6 pp. 10–11, (2.22)–(2.25); P7 pp. 506–512, (2.34)–(2.60), and Definition III.8.1 as reconstructed in `LF-RECONSTRUCTION.md` III.8.1. Landed definitions and proof points: `Balaban/LargeField/Def7v2Form.lean:actStar2,EresJ2,sfFactor2,D1Form2`; `Def7SmallField.lean:Fres,Rres,chiY`; `Def7v2Corr.lean:corrSum_singleton,corrSum_ne_zero_example`; `Operators/Quiet.lean:quietKernel`; `Operators/StepData.lean:StepData.ker`; `R/CancelIdentity.lean:cancel_expansion,cancel_core`; `R/CancelRemaining.lean:remaining_terms_of_lemma262`; `R/CancelBound.lean:Cnat0_le,Cnat1_le`; `R/RhoZero.lean:rhoZeroWith`; `R/Denominator.lean:denominator_eq`; `R/MassChangeCrossing.lean:massChange_region_bound_cubes`; and `R/WindowOfHistory.lean:windowOfHistory_hyp`.
