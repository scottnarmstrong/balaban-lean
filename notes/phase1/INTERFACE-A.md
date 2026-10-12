# Scheme A: the small-field to large-field interface

## Result

The full-action chord estimate in W2-RESOLVE (3.5) follows from stationarity and a weighted mass response, with the explicit coefficient $2C_HK_2^2B_h^2$. **Its asserted localized version for P7's regional action does not follow and is false in general:** that action counts crossing bonds with weight $1/2$, so its chord contains a boundary flux of order $\beta m\,|\partial\phi^m|\,|\phi^0-\phi^m|/m$. A one-site example below gives a nonzero limit when $\beta m$ is fixed and $m\downarrow0$, whereas $\beta m^2\to0$. A corrected interface can charge this flux to the wall part of the large-field kernel, subject to a localized wall estimate. Thus W2-RESOLVE (3.5) and (3.7), if read as statements about P7's actual half-bond regions, need the wall term displayed here.

The inherited energy has a global $O(E_0m_k/\varepsilon_k)$ comparison once the two evaluation paths have a common complex margin and the anisotropic I-6 bounds hold throughout it. The geometric level sum is explicit below. P1 Corollary 3.11 cancels a marginal term only after summing over the whole torus, however; it does not give the required bound for each localized large-field region. The observable comparison has a different H7 coefficient, $c_9\xi_k^{\rho_F}m_k/\varepsilon_k$, plus the leading source term. Its $g$ analyticity is available on $\|g\|_1<1$, but a localized interface estimate still needs the same collar and decoupling work. The large-field budget can absorb a proved per-new-volume cost by increasing its fixed $c_2$ before the final $\lambda_*,\beta$ choice. The missing step is a local identity for the physical collar and an operator estimate including cutoffs, walls and normalization; it overlaps CB-1/CB-2 of COLLAR-3 and adds a mass-convention comparison to them. Scheme A remains a conditional construction.

## 1. Chord and the regional wall

Use the scale-$j$ mass $m_j=\nu_j$ (fine coefficient $\mu_j=m_jL^{-2j}$), $\beta_jm_j\le C_0=e^{2\epsilon}$ for $j\le k_0$ (LF-RECONSTRUCTION D-IV.11), and real $|h|=1$. Fix one generating set $G$, the same physical data and the same Dirichlet values on $C(\Omega_1(G))$. Let $\phi^0,\phi^m$ solve respectively the zero-mass and complete Euler–Lagrange equations, and $w=\phi^0-\phi^m$. The physical action has mass $m$ in **both** evaluations. On the full variational domain, the hard-spin constraint and the complete Euler–Lagrange equation give exactly
$$
A_m(G;D,\phi^0)-A_m(G;D,\phi^m)
=\tfrac12\langle w,(H_m+\alpha^m)w\rangle_G. \tag{1.1}
$$
This is the identity of FLUCTUATION Lemma 2.9(a); the corresponding landed whole-action algebra is `chord_identity` and `expansion_chord` in `Fluctuation/Expansion.lean` (the latter concerns a fluctuation at a fixed mass, so its mass-switch use still needs the two-background specialization). The real response of BG Proposition 5.1, with source $m(\phi^m-h)$, gives $\|w\|_{\rm loc}\le2K_2B_hm$ if $|\phi^m-h|\le2B_h$ in the chosen norm. For a sum of $n$ unit blocks, assume the quadratic form of (1.1) has absolute value at most $C_Hn\|w\|_{\rm loc}^2$. Then
$$
0\le \beta_j[A_m(\phi^0)-A_m(\phi^m)]
\le 2C_HK_2^2B_h^2\,\beta_jm_j^2 n
\le 2C_HK_2^2B_h^2C_0^2\beta_j^{-1}n. \tag{1.2}
$$
For real unit $h$ take $B_h=1$ under the stated response normalization. For $h$ in a fixed complex pinned chart $|h-h_*|\le r_h$, take $B_h=1+r_h$ and replace positivity by absolute values; the same algebra works if the complex background response and Hessian bound hold uniformly on that chart. This is a bounded-$h$ chart, not P1's wide complex disc in $b=mh$. `WeightedProp51S` and `weightedProp51S_exists` in `Fluctuation/WeightedProp51.lean` give a weighted response **under** their `Prop51Hyp`, `OpSetting`, smallness and weighted-source premises; `lemma41_uncond` and `LargeField/R/DeltaPhiResp.lean:layered_response` are applications with additional data premises. None identifies the two physical collar data automatically.

For a union $Y$ of blocks, `LargeField/R/ActionConvDef.lean:Region.actionRegionC` uses `starWeight=1` on internal bonds and $1/2$ on crossing bonds. Its regional Green identity is `ActionConvGreen.lean:Region.bondPair_green`. Applying it to the mass comparison gives the **regional** identity
$$
A_{m,Y}(\phi^0)-A_{m,Y}(\phi^m)
=\tfrac12\langle w,(H_m+\alpha^m)w\rangle_{Y,*}
+S_Y(w,\bar\phi^m), \tag{1.3}
$$
where $S_Y=\operatorname{starPair}$ is the crossing-bond flux of `ActionConvDef.lean`. With common Dirichlet data on the collar of the *whole variational problem*, $w$ vanishes on that collar, but it need not vanish on the interior endpoint of a bond crossing $\partial Y$. Hence $S_Y$ need not vanish. The same formula holds if $Y$ is a whole variational domain and its exterior data agree; its half-bond convention still leaves the flux. A Dirichlet action assigning **full** weight to every bond between $Y$ and its fixed collar has no flux and satisfies (1.1) on $Y$, but those Dirichlet actions are not additive over adjacent P7 regions without compensating walls.

Here is an exact small-mass test. On $S^1$, take one interior spin $\phi$, a block target $q=e_1$, one exterior fixed spin $p=(\cos\vartheta,\sin\vartheta)$, and $h=q$. The complete/full variational action is
$$A_m^{\rm full}(\phi)=\tfrac12|\phi-q|^2+\tfrac12|\phi-p|^2+\tfrac m2|\phi-q|^2,$$
so $\phi^m=((1+m)q+p)/|(1+m)q+p|$ and $\phi^0=(q+p)/|q+p|$. The P7-type regional action counts its one crossing bond by half:
$$A_{m,Y}(\phi)=\tfrac12|\phi-q|^2+\tfrac14|\phi-p|^2+\tfrac m2|\phi-q|^2.$$
Writing $s_0=\sqrt{2+2\cos\vartheta}$, direct differentiation at $m=0$ yields
$$A_{m,Y}(\phi^0)-A_{m,Y}(\phi^m)
=\frac{1-\cos\vartheta}{4s_0}\,m+O_\vartheta(m^2). \tag{1.4}$$
For fixed nonzero small $\vartheta$ and $\beta m=c>0$, the left side after multiplication by $\beta$ tends to $c(1-\cos\vartheta)/(4s_0)>0$, while $\beta m^2\to0$. The collar value $p$ is identical in both minimizations. Thus common collar data and the weighted response do **not** prove W2-RESOLVE (3.5) for the half-bond localized action.

A sufficient corrected block estimate is
$$
|\beta_j\Delta A_{j,Y}|
\le 2C_HK_2^2B_h^2\beta_jm_j^2|Y|_j
+ C_{\partial}K_2B_h\beta_jm_j r_{\partial,j}|\partial Y|_j, \tag{1.5}
$$
provided $|\partial\bar\phi^m|\le r_{\partial,j}$ on crossing bonds and the incidence/units of the star pairing are bounded by $C_{\partial}$. It follows by (1.3), the response and a bondwise triangle inequality. The second term is at most $C_{\partial}K_2B_hC_0r_{\partial,j}|\partial Y|_j$; it is bounded but need not tend to zero with $\beta_j$. `ActionConvWindow.lean:StepDecomp.sum_le`, `ActionConvReduce.lean:wall_sum_le`, and `ActionConvWindow.lean:window_conversion` provide the cube/wall bookkeeping **conditional on** their `wall_bound` and window-input fields. They do not supply this new mass-switch wall bound. To obtain polymer terms with $e^{-\kappa_Dd_j(Y)}$, one additionally needs a decoupled weighted response and the AE/GM localization hypotheses for the quadratic and wall densities. No positive rate $\kappa_D$ or numerical localization constant follows from (1.1)–(1.5) alone. The claimed $2\kappa-1$ in FLUCTUATION Lemma 2.9(b) is unavailable for the separate chord on the wide $b$ disc (RGFREE-3 §2.1; RGFREE-6 §§2–4); a real pinned localization theorem must be proved separately.

`R/ActionConvIdentity.lean:actionRegion_conversion` does **not** already prove W2-RESOLVE (3.1)–(3.2). It is P6 (2.31) for a coefficient/scale conversion within **one** `MassBranch`, including its `starPair`; `.massless` and `.complete` are separate cases. It neither relates the two branch minimizers at fixed physical action nor changes inherited $E,F$, characteristic functions, reference measures or the $R$ denominator. The exponent identity (3.1) is elementary subtraction where both descriptions exist, but the full operator identity is additional work.

## 2. Re-expression of inherited terms

Put $s_{jk}=L^{-(k-j)}$, $\varepsilon_j=\alpha_0t_jL^{-j\alpha}$ with $1\le t_j<3$, $\alpha=(d-2)/2-\gamma$, and $\alpha_3=1-2\gamma-\alpha_1>0$ (SMALLFIELD §§1.2, 2.2; P1 Proposition 3.10 and Corollary 3.11). Suppose the two composed fields and every complex segment between them have a fixed fraction $r\in(0,1)$ of the complete-class XiDom margin, and
$$\|\psi^{(j),m}_k-\psi^{(j),0}_k\|\le C_{\rm cmp}s_{jk}m_k. \tag{2.1}$$
These are hypotheses to be verified for the revised class. Cauchy's formula applied to a localized term bounded by $M_{j,X}$ on a polydisc of radius $r_j$ gives, along that segment,
$$|T_{j,X}(\psi^{(j),m})-T_{j,X}(\psi^{(j),0})|
\le (C_{\rm cmp}s_{jk}m_k/r_j)\,C_{\rm var}(X)M_{j,X}. \tag{2.2}$$
Here $C_{\rm var}(X)$ counts the affected coordinates; it is absorbed by the summable polymer constant $K_{0,1}=\sup_x\sum_{X\ni x}|X|e^{-(\kappa-\kappa_0)d_j(X)}$. Equation (2.2) is a direct Cauchy estimate. It is not yet a bound on a regional sum because no cancellation has been used.

For the **whole-torus energy**, assume the anisotropic I-6 estimate holds uniformly on the complex segment and its Cauchy tube, with per-site bound $C_I E_0s_{jk}^{d+\alpha_3}$ for $k-j\ge n_1$. The tube in the interpolation parameter has radius proportional to $r\varepsilon_k/(C_{\rm cmp}m_k)$; Cauchy then gives the variation bound $C_IC_{\rm cmp}E_0(m_k/(r\varepsilon_k))s_{jk}^{d+\alpha_3}$ per old site. There are $s_{jk}^{-d}$ old sites per top block. Summing the levels $k-j\ge n_1$ and using the crude class bound $K_0E_0$ for the finitely many near levels gives
$$
|\Delta E_k^{\rm whole}|
\le C_EE_0\frac{m_k}{\varepsilon_k}|T_1^{(k)}|,
\quad C_E=\frac{C_{\rm cmp}}r\left(
\frac{C_I L^{-n_1\alpha_3}}{1-L^{-\alpha_3}}
+K_0\sum_{n=0}^{n_1-1}L^{nd}\right). \tag{2.3}
$$
Enlarge $C_E$ for the fixed comparison factors $t_j$ and $C_{\rm var}$. The first geometric sum is precisely P1 Corollary 3.11's scale weight: $s^{d+\alpha_3}$ times $s^{-d}$ leaves $s^{\alpha_3}$. This argument applies to the *sum* of energy terms, since the marginal $A_y$ in SMALLFIELD Theorem 2.1(a) cancels only when summed over the torus. On a region its boundary contribution survives. Neither Corollary 3.11 nor the landed abstract `termwise_irrelevant_aniso_scaled` alone proves W2-RESOLVE (3.6) for each $Y$. The revised complete-class domain bridge, complex path margin, regional marginal-boundary identity and decoupled localization are still required. `Fluctuation/BackgroundChangeExpansion.lean:cube_expansion` and `dOmega_le_treeLenCov` prove the combinatorial expansion **given** a bounded analytic local input and its locality; `Fluctuation/Theorem42.lean:theorem42_of_input` similarly assumes `DecoupledCubeResponse`. They do not construct that input for this mass change. Precisely, if that input is supplied with cube bound $E_b$, rate $\kappa\ge3$ and the numerical hypotheses of `theorem42_of_input`, then for any $\kappa'\ge0$ satisfying $a_{\rm Multi}(d,L)+2\le2\kappa-\kappa'$ its output trace obeys
$$|\Delta(T)|\le E_b\,\operatorname{cubeCount}(d,L,K,j)\,K_{0,\rm Multi}(d,L)\,e^{-\kappa'd_\Omega(T)}. \tag{2.3a}$$
This is an exact conditional rate and constant from the landed theorem. Obtaining an $E_b$ of order $E_0m_k/\varepsilon_k$ for the **regional grouped** difference is the missing analytic input; substituting (2.2) term by term does not establish it.

The H7 observable coefficient is different from $E_0$. SMALLFIELD §1.3 (H.7) bounds a level-$j$ local $\mathscr M^{(j)}$ by $c_9\xi_j^{\rho_F}e^{-\kappa d_j(X)}$, where $\xi_j=L^{-j}$ and $\rho_F=(d-2)/2+\gamma-\alpha_1=\alpha+2\gamma-\alpha_1$. Under (2.1), a common Cauchy margin $r\varepsilon_j$, and $\|g\|_1<1$, the *global* inherited observable difference obeys
$$
|\Delta F_k^{\rm inherited}(g)|
\le \frac{C_{\rm cmp}K_{0,1}}r\,c_9\|g\|_1\frac{m_k}{\varepsilon_k}\xi_k^{\rho_F}
\frac1{1-L^{-(1-2\gamma+\alpha_1)}}. \tag{2.4}
$$
Indeed $s_{jk}\xi_j^{\rho_F}/\varepsilon_j\le(\xi_k^{\rho_F}/\varepsilon_k)s_{jk}^{1+\alpha-\rho_F}$ and $1+\alpha-\rho_F=1-2\gamma+\alpha_1>0$. If the leading term $\langle g,\phi_k\rangle$ is also converted, add $2K_2m_k\|g\|_1$ in the corresponding source norm. Formula (2.4) is analytic in $g$ on its full unit $\ell^1$ ball. A local $Y$ version with a fixed decay rate requires an observable localization theorem and the same collar identification; it is not (3.6)'s $C_FE_0m/\varepsilon$ by class axioms alone.

## 3. Budget and order of constants

Suppose the missing regional construction assigns every interface factor to the newly exposed $X_{Z'}=Z_k^c\cap Z'$ of its step, with support in $V_{Z'}$, and proves uniformly in old variables and $\|g\|_1<1$ that
$$|\operatorname{Re}J_{k,Z'}|\le q_k|X_{Z'}|_{k+1},\qquad
q_k=C_D\beta_km_k^2+C_W\beta_km_kr_{\partial,k}
 +C_EE_0m_k/\varepsilon_k+C_Fc_9\xi_k^{\rho_F}m_k/\varepsilon_k+C_{F,0}m_k. \tag{3.1}$$
Here $C_D=2C_HK_2^2B_h^2$ before localization losses; $C_W$ includes wall incidence; $C_E,C_F$ include the localization constants beyond (2.3)–(2.4). The hypothesis that the cost is proportional to **new** volume is essential: (D6) is not a free reserve for terms on arbitrary old or exterior sites. If $q_*:=\sup_{k\le k_0}q_k<\infty$, multiplying a step kernel by $e^{J}$ changes the (S2) exponent from $\kappa^{(k)}$ to $\kappa^{(k)}-q_k|X_{Z'}|_{k+1}$. Definition II.5.11 absorbs it exactly by replacing $c_2$ with $c_2+q_*$; enlarge $C_b$ in (S0) and the (S5) rotation-form constant as their verified bounds require. Then Lemma II.5.12's budget recursion and (D6)/(H6′) keep their form, with the new constants and a later $\lambda_*$. This is the precise LF-2 charging location, rather than an unspecified $\eta_{\rm LF}$.

The scalar implication is elementary: $\tilde K e^{\operatorname{Re}(b+J)}\le e^{q_k|X|}\tilde K e^{\operatorname{Re}b}$, so an original $e^{-\kappa^{(k)}}$ one-step bound becomes $e^{-\kappa^{(k)}+q_k|X|}$. The *existence* of that uniform majorant for the constructed interface operator is open. In Lean, `LargeField/Budget/Exponents.lean:BudgetConsts.kappaStep` contains the $c_2$ coefficient, `Budget/LemmaB.lean:RegionHistory.lemmaB` consumes it, and `Counter/LF2.lean:LF2` consumes the resulting budget premise. One must rebuild the constants and the actual `IsRep`/`IsRepFlat` witnesses; the current theorems do not automatically cover the altered kernel.

Use the LF-RECONSTRUCTION §I.1.3 order: fix geometry and response/localization constants in rows 0–10; choose the complete-class margins $\alpha_0,E_0$ and the interface constants in row 11; choose $B_0$ in row 12, $H_0$ in row 13, enlarged $c_1,c_2$ in row 14, then $c_v$ and $C_R$ in row 15; finally choose $\lambda_*,\beta_0$ in row 16. The real chord contributes at most $C_DC_0^2/\beta_k$; the wall contributes at most $C_WC_0r_{\partial,k}$, which does **not** acquire a $1/\beta_k$ factor. The energy and observable terms shrink with $m_k/\varepsilon_k$ if their comparison hypotheses hold. One may arrange a fixed $q_*$ before $B_0$ by imposing the final lower bound on $\beta$ and a prior bound on $r_{\partial,k}$; then choose $c_2\ge c_2^{\rm old}+q_*$. Alternatively choose a larger fixed $q_*$ and pay it in $c_2$. Increasing $c_2$ changes the late condition $c_2+2\le\hat\lambda_{k+1}$ in Lemma II.5.12, so $\lambda_*$ must be chosen last. There is no proved version of W2-RESOLVE (3.7) for the regional action with only the two terms displayed there.

## 4. Collar gluing and the $k_0$ step

The overlap exponent identity W2-RESOLVE (3.1) is valid when both backgrounds and inherited terms are evaluated on the **same** data. To turn it into the $R$ operator identity, one must: identify the original P7 $Q^*$ datum on every site of the window collar and prove it is the datum used by the physical action; identify or bound the complete/free comparison on that same collar; include crossing-bond flux (1.3), cutoff changes and reference-measure/Jacobian factors; and verify P7 (1.5)–(1.7)'s numerator and denominator use the intended common LF reference after conversion. The correction must be supported in the new lineage region, satisfy (S0), (S2), (S4), (S5) and the real-$h$ / complex-$g$ requirements of Definition II.5.2. Algebraic normalization of a ratio with one common reference remains true; it does not verify these identities or estimates.

This is **partly the same open item** as COLLAR-RULING / COLLAR-2 / COLLAR-3. Their CB-1 identifies the actual physical window collar, CB-2 bounds its difference from the composed reference (or CB-0 proves equality), and CB-4 pays the residual weighted response at every consumer set. They concern the original window versus its reference; the new complete-versus-free comparison has an additional mass response and the regional wall (1.3). The landed `DeltaPsiDef.deltaPsi` is zero off the window interior although the two data objects need not agree on the collar (COLLAR-3 §5); `DeltaPhi.deltaPhi_le_of_dataChange` takes `DataChangeBound` as a premise. Thus neither those declarations nor `ActionConvIdentity.actionRegion_conversion` close the new interface. A common collar may be used **only after** CB-1/CB-0 proves it is the original action's collar; assigning a convenient one changes the action.

Under scheme A, LF-RECONSTRUCTION Theorem IV.2.2(e) should say: the small-field member at $k_0+1$ is obtained by the ordinary complete-background P4/FLUCTUATION Theorem 5.3 step, with its ordinary complete RG equations and no added SF switch term. Lemma IV.2.1 transfers LF histories, windows and (D6)$\to$(H6♭); its former claim that both SF and LF read zero mass below $k_0$ must be removed. The LF step $k_0\to k_0+1$ **still** changes its LF solver from free to complete, as in P6 pp. 10–11; its regional conversion, wall and kernel budget remain LF obligations. FLUCTUATION Lemma 2.9(b) is replaced, for SF, by the complete-background birth/localization hypotheses of Theorem 5.3, and, for LF, by (1.3), (2.2)–(2.4) plus the missing localized wall/collar theorem. Its wide-complex bound for the separate chord is not used. Real fixed unit $h$ at the frozen root needs the real LF estimates and $g$ analyticity; it does not require a mass-uniform wide-complex transverse-$h$ LF bound.

## 5. Lean dependency order

All paths below are read-only source locations under `/home/scott/Balaban/Balaban/`; names are exact landed declarations where given. New lemma names are proposed.

1. **Mass response on identical data and collar.** Use `Fluctuation/WeightedProp51.lean:weightedProp51S_exists`, `Fluctuation/FarDecayUncond.lean:lemma41_uncond`, `Background/Theorem73.lean:theorem73_real`/`theorem73_complex`, and, for window profiles, `LargeField/R/DeltaPhiResp.lean:layered_response`. Prove `massChange_sameData_response` with its full `Prop51Hyp` and complex-chart versions; do not infer the original P7 collar from these results.
2. **Full and regional action algebra.** Use `Fluctuation/Expansion.lean:chord_identity`, `Fluctuation/ExpansionQuad.lean:expansion_quadratic`, `LargeField/R/ActionConvGreen.lean:Region.bondPair_green`, and `ActionConvAdd.lean:Region.actionRegionC_additive`. Prove `massChange_dirichlet_chord` and `massChange_region_chord_with_star` in the forms (1.1), (1.3). `ActionConvIdentity.lean:actionRegion_conversion` remains the same-branch P6 conversion; retain its surface term.
3. **Physical collar and cutoff bridge.** Follow COLLAR-3 §5: `window_parent_collar_partition`, `psiTilde_collar_eq_inherited`, `psiZeroWin_collar`, `deltaPsi_dataSites`, then CB-0 or CB-2 and `window_response_decay`. The landed `LargeField/R/WindowGenGlue.lean:WindowPieces.windowGenSet_Ω`, `Background/Composition.lean:composeField_of_collar`, `DeltaPsiCoreFinal.lean:deltaPsi_le_pieces`, and `DeltaPhi.lean:deltaPhi_le_of_dataChange` cover only their stated premises. Add `massChange_cutoff_reference_glue` for the new convention.
4. **Localized wall and chord.** Prove `massChange_wall_bound` and `massChange_cube_bound`, using `ActionConvReduce.lean:wall_sum_le`, `ActionConvWindow.lean:StepDecomp.sum_le` and the weighted response. Then prove a decoupled analytic/locality input and apply `Fluctuation/BackgroundChangeExpansion.lean:cube_expansion`, `Fluctuation/Theorem42.lean:theorem42_of_input` to obtain an explicit rate. The existing `ActionConvWindow.lean:window_conversion` requires its own `ActionConvInput.wall_bound` and does not imply these new bounds.
5. **Inherited $E,F$ and the one-step operator.** Use `SmallField/XiComposeField.lean:xiC_compose`, `SmallField/RenormAnisoIrrel.lean:termwise_irrelevant_aniso_scaled` and `RenormAnisoBridgeInf.lean:IsSFFamily.termwise_irrelevant_aniso_class` under their *revised complete-class* domain premises. Prove the complex segment and localized marginal-boundary comparison; add the H7 observable Cauchy lemma. Build `sfToLf_interface_operator` with support, covariance, (S0), (S2), (S4), (S5), cutoff and common-reference normalization. `Fluctuation/Theorem42.lean` only propagates a supplied local input.
6. **Budget and regime transfer.** Increase `BudgetConsts.c2` in `LargeField/Budget/Exponents.lean`; reinstantiate `Budget/LemmaB.lean:RegionHistory.lemmaB`, `Counter/LF2.lean:LF2`, `LargeField/Def7Basic.lean:Rep.budget_of_LF2`, `Rep.budgetFlat_of_budget`, and `IsRep.toFlat` after changing the SF/LF mass fields. Finally reprove the scheme-A instance of LF-RECONSTRUCTION Lemma IV.2.1 and Theorem IV.2.2(e), with the ordinary complete SF step and LF-only switch.

**Status.** Equations (1.1)–(1.5), the one-site refutation, the conditional whole-torus level sums (2.3)–(2.4), and the scalar budget implication are proved or reduced to the explicitly named response/domain premises. A localized $e^{-\kappa_Dd(Y)}$ estimate, the regional energy cancellation, the actual P7 collar identity and the whole-$R$ operator gluing are open. No file under `/home/scott/Balaban` was changed.
