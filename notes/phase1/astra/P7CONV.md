# P7 window action conversion: verdict and exact remaining estimates

**Verdict (17 October 2026).** The algebraic conversion and the geometric summation are proved in the landed Lean. The numerical inputs for a nonempty physical window are **not proved** by the present hypotheses. Two tempting universal readings are false: `p7_first` does not follow from `pieceChain` plus the stated `hflow`, and `window_decay` does not follow from `PieceWindowSetup` or `sum_mainActionLoc_eq_gen`. Explicit counterexamples are below. They do **not** refute Balaban's estimate for the actual RG history: that estimate requires an incremental flow/source bound and a normalized, supported comparison of the local and window actions. I give a sufficient corrected statement and prove its complete finite-action and summation parts. Its physical response/geometry premises remain open. Accordingly this note does not claim to close blocker 4.

## Frozen scope and sources

The read-only Lean tree was at commit `4c96d5af9a24b6b009e5f2f200cb43879c0eae3e`. SHA-256: `ActionConvWindow.lean` `4e528a9a8277e551ce36984bf9632087bd380b3afd9297fb49c926fcaa02471e`, `ActionConvPieces.lean` `96f386418b6294a5dfadbcbcf4f4a3c363c165a0e6ebc3036eebc89e6065e696`, `PieceChain.lean` `baa0535c0d801b0c60ec52eeb125a565e69be861f9eadab9a573b6c162ed254c`, `WindowCompose.lean` `f8c884044d71f3c622a04c56defd8a7312b046e725cf2c65b06d54639d66432f`. The plan and companion notes were read at SHA-256 `0217ac12bd3129ecd7806db361b2e8033413073521f854e0fdaef70d88b45528` (`LF4R-PLAN.md`), `648d950f1568880f2c53c6ea5e72e78d6d10680df45d4381a47c35545b18192e` (`INTERFACE-A.md`), and `63f37e964e4f3bba5c089193a4dab1e1f43530644d50c0ed0398ea835388006b` (`MASS-RESPONSE.md`). This is a focused statement/proof audit with an adversarial counterexample pass; there was no Lean edit or build.

Primary references are T. Balaban, *The large field renormalization operation for classical N-vector models*, **Commun. Math. Phys. 198** (1998), 493–534 (P7), pp. **500–501**, (2.10)–(2.16); T. Balaban, *Renormalization and localization expansions. II*, **Commun. Math. Phys. 198** (1998), 1–45 (P6), pp. **6–7**, (2.13)–(2.16), p. **11**, (2.25) and the following wall discussion, and p. **14**, (2.31); and T. Balaban, *Localization expansions. I*, **Commun. Math. Phys. 182** (1996), 33–82 (P3), p. **56**, (2.55)–(2.56). The P7 and P6 text layers are usable but garble some set symbols and superscripts; the P3 scan's text layer is badly garbled at (2.55)–(2.56), so I use it only for the cited location of a distance-decay estimate, not for an unverified numerical constant. The extracted text used here is in `P7-pp499-501.txt`, `P6-pp6-7.txt`, `P6-pp9-14.txt`, and `P3-p56-ocr.txt` in this directory. The local secondary analysis `notes/phase1/P631-INPUTS-2.md` §1–3 supplies the conditional reductions and is not treated as a primary proof of their missing premises.

The source PDFs' SHA-256 hashes are P7 `c48e08dd439878a0245cceb6e6aead787a8ce7671865f6360c8464a7e579d2e9`, P6 `ee0ca061c9a7418d5da907a4dd09b66fb247f46bffcf68f83fa3ba502c342fc4`, and P3 `091adb3c13f9a718b84bc3b96e4619fece789d1a3140eb166c29af3d4b87fe3d`.

P7 p. 500 says the $j$th action is converted $k-j-1$ times by P6 (2.31), without renormalizing spin variables; its (2.11) bounds each conversion by $\mathrm{const}\,\beta_{j+1}\varepsilon_{j+1}^{2}/(\beta_n\varepsilon_n^2)$ times a mixed cube count. P7 p. 501 then changes the generating set/background by (2.14) and quotes a remainder $\mathrm{const}\,e^{-R_{j-1}}$ per such cube. The identity in (2.12), followed by (2.15)–(2.16), **defines** the correction $C$; it is not an equality of the local and window backgrounds.

## Exact landed interfaces

Write $i=(j,P,c)$ for a piece, $j=\operatorname{sc}(i)$, $m_i=\texttt{W.mcount i}=(\texttt{W.decomp i}).\texttt{total}$, and $X_i^c,X_i^w$ for its local and window regions. In `ActionConvChain.lean`, `ConvChain.T u n` is $\widehat\beta_n A_{X_i^c}(a_n,\nu_n;D_n,\phi_n)$, while `ConvChain.cost u n` is $\widehat\beta_n C_{X_i^c}^{(n)}+\widehat\beta_{n-1}S_{X_i^c}^{(n)}$. `ConvChain.step` proves exactly $T_{i,n-1}=T_{i,n}+R_{i,n}$; `ConvChain.telescope` sums it.

For a physical piece, `PieceChain.lean:pieceChain` sets

$$\widehat\beta_n=\texttt{betaCanon}\ d\ L\ (\texttt{cs.beta n})\ n\ 0
=\frac{\texttt{cs.beta n}}{L^{n(d-2)}},\quad
a_n(\ell)=\texttt{cs.aw}\,\ell\,\frac{\widehat\beta_{j+1}}{\widehat\beta_n},\quad
\nu_n=\texttt{cs.muAct n},\quad
e_n=\frac{\widehat\beta_{n-1}\nu_{n-1}-\widehat\beta_n\nu_n}{\nu_n}.$$

It keeps `locData` fixed, uses `locBg` at $j+1$, and uses `bgFieldC` of that datum at later coefficients and mass `br.elMass ν_n`. Its `pieceChain_T` identifies $\operatorname{Re}T_{i,j+1}$ with `mainActionLoc`. The `br = massless` background equation uses mass zero even though `actionRegionC` retains the physical `ν_n` (see `ActionConvDef.lean:MassBranch.elMass`).

The seven fields of `ActionConvWindow.lean:ActionConvInput` are, with the original step index $j$:

| Field | Exact mathematical content of the Lean inequality |
|---|---|
| `variational_bound` | For $j+2\le n\le k$, `Small Gc (α_{n-1}-α_n) (cK2 d L N * δ₁ j n u)` and `SupBounds Gc (φ_{n-1}-φ_n)` with the same bound. |
| `analytic_T` | $u\mapsto T_{j,n}(u)$ is `AnalyticOnNhd ℂ` on $S$, $j+1\le n\le k$. |
| `cube_bound` | Each cube $a$ obeys $\|\widehat\beta_n\,\texttt{counterC}(\texttt{cube }a)\|\le c_C\,\texttt{wt }a$. |
| `wall_bound` | Each wall $q$ obeys $\|\widehat\beta_{n-1}\,\texttt{starPairOn}(\texttt{wall }q)\|\le c_W\,\texttt{wt}(\texttt{wallCube }q)$. |
| `p7_first` | $\|R_{j,n}(u)\|\le K_{\rm conv}\,\frac{\widehat\beta_{j+1}\varepsilon_{j+1}^{2}}{\widehat\beta_n\varepsilon_n^2}\,m_j$ in `ActionConvInput`; its piece version in `window_conversion_pieces` and `WindowCompose.sum_mainActionLoc_eq_gen` uses **scale** couplings $\beta_n=\texttt{cs.beta n}$ in this ratio. |
| `window_decay` | $\|T_{j,k}(u)-\beta_k^{\rm target} A_{X_j^w}(a_k,\nu_k;D^w,\phi^w)\|\le K_{\rm bg}e^{-\gamma_w D_j}m_j$, $D_j=M(\widehat R_{j-1}-1)-2M_1$. In the piece theorem replace $j$ by $\operatorname{sc}(i)$. |
| `analytic_win` | $u\mapsto\beta_k^{\rm target} A_{X_j^w}(a_k,\nu_k;D^w(u),\phi^w(u))$ is `AnalyticOnNhd ℂ` on $S$. |

The displayed `p7_first` distinction is material. `window_conversion_pieces` explicitly takes `βs : ι → ℕ → ℝ`; `WindowCompose.sum_mainActionLoc_eq_gen` passes `fun _ m => cs.beta m`. `ActionConvInput` still writes its ratio using the fine-unit `chain.β`. Under a free flow $\widehat\beta_n=B$, that ratio is $(q_{j+1}/q_n)^2L^{2\alpha(n-j-1)}$, whereas P7's scale-coupling ratio decays like $L^{-2\gamma(n-j-1)}$. Likewise the `hflow` binder of `window_conversion` describes growing scale couplings and cannot be filled by the constant free-flow `pieceChain.β` over arbitrary window lengths. One cannot transport a proof of either ratio to the other by definitional equality. The piece theorem is the relevant consumer for the history.

`ActionConvInput.cost_le` proves the absolute estimate $\|R_{j,n}\|\le(c_C+c_W\operatorname{inc}_j)m_j$ from the cube and wall fields. It does **not** imply the factor $\beta_{j+1}\varepsilon_{j+1}^2/(\beta_n\varepsilon_n^2)$ in `p7_first`. `window_conversion_core`, `window_conversion`, and `window_conversion_pieces` assume `p7_first` and `window_decay`; they do not produce them. `WindowCompose.sum_mainActionLoc_eq_gen` specializes to `U = Unit`, so its two analyticity premises are satisfied by constancy, without constructing the P5 (1.32) complex germ.

| Input | Status for the actual nonempty history |
|---|---|
| `variational_bound` | P2 response applicable only after the full cut source, strict smallness and domain are supplied. |
| `cube_bound` | P6 (2.25) supplies its model estimate, but the actual piece and normalization have not been instantiated. |
| `wall_bound` | The finite Cauchy–Schwarz reduction is proved; the cut-response and mixed wall incidence remain. |
| `p7_first` | False as a consequence of the displayed `pieceChain`/`hflow` premises; (3) is sufficient and remains unproved physically. |
| `window_decay` | False as a consequence of `PieceWindowSetup`/`WindowCompose` premises; (4)–(5) and normalized action reads are sufficient and remain unproved physically. |
| `analytic_T`, `analytic_win` | Trivial for `U=Unit` in the landed history theorem; a nontrivial P5 (1.32) complex assertion needs analytic common-domain data/backgrounds. |

## Refutations of universal readings

### 1. The flow shape does not imply `p7_first`

Here is an exact algebraic test inside the `pieceChain` coefficient convention. Take a nonempty region $X$ and a massless branch with one fixed datum and a fixed massless minimizer $\phi$ for which
$H_X:=\sum_{x\in X}|\phi(x)-h|^2>0$ (a pinned constant spin unequal to $h$ suffices). Fix $j$ and $n=j+2$, choose $\texttt{cs.beta }m=B L^{(d-2)m}$, $B>0$, and keep the block weights fixed. Then $\widehat\beta_m=B$, $a_m=a$, and `hflow` holds with $g_m=1$, $\eta=0$. Take `cs.mu (j+1)=0` and `br = massless`, so the background at both stages is the same zero-mass minimizer. The physical action masses `cs.muAct (j+1)=1` and `cs.muAct n=2` are allowed by `OpConsts`, `pieceChain`, and the stated nonzero-mass hypothesis; the definition of $e_n$ enforces the `ConvChain.mass` equality. The P2 domain hypotheses for the *massless* backgrounds do not constrain these physical action masses.

The block and bond actions cancel, whereas the mass action gives **exactly**

$$R_{j,n}=T_{j,j+1}-T_{j,n}=-\frac B2 H_X,qquad
\|R_{j,n}\|=\frac B2 H_X.\tag{1}$$

The scale-coupling ratio $\rho_{j,n}=\beta_{j+1}\varepsilon_{j+1}^2/(\beta_n\varepsilon_n^2)$ and the mixed count $m_j$ do not depend on $B$. Given fixed $K_{\rm conv}$, choose $B>2K_{\rm conv}\rho_{j,n}m_j/H_X$. Then the piece `p7_first` inequality fails, even with the displayed `hflow`. This is a refutation of an inference from the landed premises, not of the actual RG mass recursion: the latter must be supplied and shown to make the *increment* small. A similar example changes $\widehat\beta_n$ by a fixed relative factor inside the allowed bounded $g_n$ and uses a nonconstant stationary field; the kinetic contribution is proportional to $B$.

The older observation in `P631-INPUTS-2.md` §2.2 is sharper against a different inference: P6's per-scale $O(1)$ cube/wall estimate plus P4's renormalization size has no originating $j$ and therefore cannot by itself yield a factor $\rho_{j,n}\to0$ for long windows. The bound needs a lineage-specific **relative source** estimate; merely bounding $g_n$ above and below is insufficient.

### 2. The target action is neither normalized nor tied to a local piece

`PieceWindowSetup` records the sites and disjointness of $X_i^w$, but has no equality of the block, fine-bond, mass or collar reads of $X_i^c$ and $X_i^w$, no relation between `βk` and `chain.β k`, and no bound on the difference of `Datw, φw` from the local datum/background. Even its `StepDecomp.wt` is only assumed nonnegative; a nonempty cube can be assigned zero weight. Thus its typing fields cannot imply `window_decay` or identify $m_i$ with the physical mixed count.

An exact normalization test takes a single piece with $k=j+1$, the *same* region, data, coefficients and nonzero action $A$ at both ends. There is no conversion cost and no background change. For a free flow $\texttt{cs.beta }k=B L^{k(d-2)}$, `pieceChain.T () k = B A`. The target in `WindowCompose` is the unconstrained `βk * actionRegionC`; choosing `βk = cs.beta k` gives

$$|T_{i,k}-\beta_k A|=B\bigl(L^{k(d-2)}-1\bigr)|A|.\tag{2}$$

For $d\ge3$, $L>1$, $k\ge1$, this exceeds any fixed $K_{\rm bg}e^{-\gamma_wD_j}m_i$ when $B$ grows. The correct coefficient for a *fine-lattice* `actionRegionC` is $\widehat\beta_k=\texttt{betaCanon }d\ L\ (\texttt{cs.beta }k)\ k\ 0$. P7's printed $\beta_kA_k^*$ is in scale-$k$ units; (2) is what happens if that symbol is passed directly to the fine-unit Lean action. The theorem `sum_mainActionLoc_eq_gen` permits this choice of `βk`, so its `window_decay` cannot be discharged without a normalization premise. Even after normalization, the actual local/window comparison of data, bonds and background is still needed.

For a window crossing a massless-to-complete background change, a common datum does not give a supported perturbation: the mass source $-\mu(\phi-h)$ is distributed across the variational domain (`MASS-RESPONSE.md` §1). Its response has no window-distance decay from the common-datum theorem alone. Moreover the half-bond regional action has the crossing flux derived in `INTERFACE-A.md` (1.3), with a one-site refutation of a purely quadratic localized chord. Thus a branch switch requires an explicit bulk/wall charge; the quoted P7 boundary decay applies only after the branch and physical action are matched on the two sides.

### 3. The other fields also need their source hypotheses

The formal statement of `ActionConvInput` is not a universal theorem about `WindowSetup`: setting its unconstrained $\delta_1=0$ in a chain with a nonzero response refutes `variational_bound`; choosing $c_C=c_W=0$ with a nonzero counterterm or wall refutes the corresponding fields. For `analytic_win`, `Datw` and `φw` are arbitrary functions of a complex parameter: even $u\mapsto(\cos\bar u,\sin\bar u)$ is a bilinear hard-spin field whose nonconstant mass action is antiholomorphic, not holomorphic. `analytic_T` has the same issue unless a common open complex domain and analytic parameter dependence are established. These examples identify missing hypotheses, not defects in the conditional `ActionConvInput` proposition.

The counterexamples were checked against the point-of-use assumptions: `hflow` only controls the **size** of $\beta_n$, `pieceChain.mass` is an algebraic equation solved by $e_n$, and `WindowCompose` makes the target `βk`, `ak`, `νk`, `Datw`, `φw` independent arguments. No landed field constrains the mass increment in (1) or the target normalization in (2).

## Nearest usable theorem and complete finite proof

The following hypotheses are quantitative obligations for each **actual** history piece $i=(j,P,c)$, with its own `locGen`, `Xc`, and `pieceChain`; none may be inferred from another piece's generating set.

1. **Normalization and read transport.** Put $\widehat\beta_k=\texttt{betaCanon }d\ L\ (\texttt{cs.beta }k)\ k\ 0$ and take `βk = β̂k` in `sum_mainActionLoc_eq_gen`. Identify the local and window regions' layer-dependent block weights, *all* half-weighted internal and crossing bonds, mass sites, $h$, and the transported data on their common action reads. Where those data differ, their difference is a supported perturbation included below. The physical mixed count has $m_i\ge0$ and pays each cube/wall with a uniform incidence $I_*\ge\operatorname{inc}_i$.
2. **Relative cube and wall inputs.** Define $\rho_{j,n}=\texttt{cs.beta}(j+1)\varepsilon_{j+1}^2/[\texttt{cs.beta}(n)\varepsilon_n^2]$, with positive denominators. For every cube $a$ and wall $q$ of `W.decomp i`, assume the **localized** inequalities
   $$\|\widehat\beta_n C_{i,n}(a)\|\le c_C^{\rm rel}\rho_{j,n}\,\texttt{wt}(a),\qquad
   \|\widehat\beta_{n-1}S_{i,n}(q)\|\le c_W^{\rm rel}\rho_{j,n}\,\texttt{wt}(\texttt{wallCube}(q)).\tag{3}$$
   These are the precise missing relative-source consequences of the P6 (2.31) cut problem. The weaker P6 (2.25) bound omits $\rho_{j,n}$.
3. **Window pair.** On a common complex neighbourhood of the P5 (1.32) window domain, identify the converted local background and the window background on all action reads. On a common generating set after transport, their data have the same $h$, a difference supported at distance at least
   $$a_j=2M[\widehat R_j]-M-2M_1\ge0\tag{4}$$
   from those reads, and the full P2/P3 weighted response (including the P6 cut source and every complex-domain hypothesis) yields a field/first-difference/scale-appropriate block-average displacement no larger than
   $$t_j=K_R r_j e^{-2\gamma_w a_j}.\tag{5}$$
   Here the *base* action residuals in block and bond terms are each at most $K_0r_j$, the mass first variation obeys $|\nu_j(\phi-h)|\le K_mr_j$, $0\le\nu_j\le1$, and $r_j\le C_H\alpha_0$. After the fine-to-$(j+1)$ normalization, the absolute total weights of each of the three families of action reads are at most $C_*\beta_jm_i$. This last assertion is a genuine **window normalization** theorem, not a consequence of site equality. At $j=0$, (4) must be stated with an explicit base convention or replaced by a separate base estimate.
4. **Flow and analyticity.** The real scale couplings have $\beta_n=B L^{(d-2)n}g_n$, $B>0$, $e^{-\eta}\le g_n\le e^\eta$, $\varepsilon_n=\alpha_0q_nL^{-\alpha n}$ with $1\le q_n<3$ and $d-2-2\alpha=2\gamma>0$. The transported data and both backgrounds are analytic on one open neighbourhood of $S$; all denominators remain nonzero there. For a physical complex assertion, the `Small`/`SupBounds` response and the finite sums must hold throughout that neighbourhood. For the real `U=Unit` use in `WindowCompose`, analyticity is automatic.

Here are the inequalities, including constants. By `StepDecomp.additive_sum`, `starPair_sum`, `sum_le` and wall-to-cube charging,

$$\begin{aligned}
\|R_{i,n}\|
&\le\sum_a\|\widehat\beta_n C_{i,n}(a)\|
 +\sum_q\|\widehat\beta_{n-1}S_{i,n}(q)\|\\
&\le\rho_{j,n}\Bigl(c_C^{\rm rel}\sum_a\texttt{wt}(a)
  +c_W^{\rm rel}\sum_q\texttt{wt}(\texttt{wallCube}(q))\Bigr)\\
&\le(c_C^{\rm rel}+I_*c_W^{\rm rel})\rho_{j,n}m_i.\tag{6}
\end{aligned}$$

Thus the **piece** `p7_first` holds with $K_{\rm conv}=c_C^{\rm rel}+I_*c_W^{\rm rel}$. This is a full finite proof of (6); the unproved content is (3) for the actual RG cut and lineage. P6 p. 11 (2.25) provides an absolute cube estimate of the form $3C_4B_6K_5/\beta_n$ under its domain and source bounds. For a wall $F$ whose bonds $E_F$ are charged once, complex Cauchy–Schwarz gives

$$|S_F|\le |E_F|\sup_{b\in E_F}|\bar w_b|\sup_{b\in E_F}|\partial\phi_b|.
\tag{7}$$

If $|E_F|\le c_E\texttt{wt}(\texttt{wallCube }F)$, $|\bar w_b|\le K_3\varepsilon_n\eta_n$, $|\partial\phi_b|\le K_4\varepsilon_n$, $\eta_n=B_6K_5/(\beta_n\varepsilon_n^2)$, and $|\beta_{n,u}|\le(17/16)\beta_n$, then

$$|\beta_{n,u}S_F|\le\tfrac{17}{16}c_EK_3K_4B_6K_5\,\texttt{wt}(\texttt{wallCube }F).\tag{8}$$

This proves the **absolute** wall field once its bondwise and incidence premises hold (`ActionConvReduce.wall_sum_le`, `wall_scalar`, `wall_mixed_scalar`). It does not prove (3). The P6 p. 14 equation for the regional response includes a cut source; bounding only the bulk coefficient change omits it. Likewise P2 Proposition 3.1 (3.47), cited by P6 p. 14, gives the `variational_bound` only after its strict small-source and domain assumptions are established for this full cut source. The simple stencil estimate $\|f_{\rm cut}\|_\infty\le2d\|Q_n^*v\|_\infty$ has no $\rho_{j,n}$ gain.

For the window remainder, expand every complex *bilinear* square $Q(z+\Delta z)-Q(z)=2B(z,\Delta z)+Q(\Delta z)$. The block change is $\Delta r=\delta\Psi-Q\delta\phi$, the bond change is $\partial\delta\bar\phi$ (including exterior collar data and the half-bond), and the same-$h$ mass change is $\delta\phi$. Applying the read and residual bounds in hypothesis 3 gives, family by family,

$$\begin{array}{ll}
\text{block:}&C_*\beta_jm_i\,[K_0r_jt_j+\tfrac12t_j^2],\\
\text{bond:}&C_*\beta_jm_i\,[K_0r_jt_j+\tfrac12t_j^2],\\
\text{mass:}&C_*\beta_jm_i\,[K_mr_jt_j+\tfrac12t_j^2].
\end{array}\tag{9}$$

There is no omitted stationary first variation: the bond line includes the regional crossing flux. Since $a_j\ge0$, $e^{-4\gamma_wa_j}\le e^{-2\gamma_wa_j}$, and (5) yields

$$\|T_{i,k}-\widehat\beta_k A^w_i\|
\le C_A\beta_jr_j^2e^{-2\gamma_wa_j}m_i,
\quad C_A=C_*[K_R(2K_0+K_m)+\tfrac32K_R^2].\tag{10}$$

To obtain precisely the landed exponential, let $D_j=M([\widehat R_{j-1}]-1)-2M_1$ for $j\ge1$. Monotonicity of radii gives

$$2a_j-D_j=4M[\widehat R_j]-M[\widehat R_{j-1}]-M-2M_1
\ge3M[\widehat R_j]-M-2M_1.\tag{11}$$

For the reconstruction's $\widehat R_j=R_{\rm base}x_j^2$, $x_j=\log(\beta_0a)+1+j(d-2)\log L$, use $[\widehat R_j]\ge R_{\rm base}x_j^2-1$, $\beta_j\le a^{-1}e^{x_j-1+\eta}$, and $r_j\le C_H\alpha_0$. Completing the square,

$$x_j-3\gamma_wMR_{\rm base}x_j^2
\le\frac{1}{12\gamma_wMR_{\rm base}},$$

so (10)–(11) imply the **piece** `window_decay` with

$$K_{\rm bg}=C_AC_H^2\alpha_0^2a^{-1}
\exp\!\left(\eta-1+\gamma_w(4M+2M_1)
 +\frac{1}{12\gamma_wMR_{\rm base}}\right).\tag{12}$$

Here $M,R_{\rm base},\gamma_w,a$ must be positive. Equation (12) is uniform in $j$ and $k$, but only under the supported pair and normalization hypotheses. It is not a constant of $d,L,N$ alone: it also records the chosen action, chart and radius constants, as P7's unspecified `const.` does. If the response had only $e^{-\gamma_wD_j}$ at the action, (10) would retain $\beta_jr_j^2\asymp L^{2\gamma j}$; this cannot be hidden in a uniform $K_{\rm bg}$. The extra distance/rate in (4)–(5) is essential. A separate $j=0$ bound $K_{\rm base}e^{-\gamma_wD_0}m_i$ can be included by replacing $K_{\rm bg}$ by $\max(K_{\rm bg},K_{\rm base})$, with $D_0$ explicitly declared; Lean's `j - 1 = 0` at $j=0$ is not P7's undefined $R_{-1}$ convention.

P7 p. 501 prints the stronger-looking shorthand $e^{-R_{j-1}}$. It follows from the Lean form only with an additional threshold. Indeed $D_j\ge M(\widehat R_{j-1}-2)-2M_1$, so
$$\gamma_wD_j-\widehat R_{j-1}\ge(\gamma_wM-1)\widehat R_{j-1}-2\gamma_w(M+M_1).$$
If $\gamma_wM>1$ and $\widehat R_{j-1}\ge2\gamma_w(M+M_1)/(\gamma_wM-1)$, then $e^{-\gamma_wD_j}\le e^{-\widehat R_{j-1}}$ with the same prefactor; otherwise retain the landed $e^{-\gamma_wD_j}$. This also shows why the precise radius convention must be stated before translating the printed exponent.

Finally, the exact ratio calculation, already formalized as `ActionConvRatio.p631_ratio_free`, is

$$\rho_{j,n}=\frac{g_{j+1}}{g_n}
\left(\frac{q_{j+1}}{q_n}\right)^2L^{-2\gamma(n-j-1)}
\le9e^{2\eta}q^{n-j-1},\qquad q=L^{-2\gamma}\in(0,1).\tag{13}$$

The constant $1$ in the old ratio reading is false because $q_2>q_3$; `p631_ratio_one_counterexample` proves this. Combining `ConvChain.telescope`, (6), (10)–(13), and $e^{-\gamma_wD_j}\le1$ when `hsep` holds, for each piece

$$\begin{aligned}
|\widehat\beta_kA_i^w-T_{i,j+1}|
&\le\sum_{n=j+2}^{k}|R_{i,n}|+|T_{i,k}-\widehat\beta_kA_i^w|\\
&\le\left(9e^{2\eta}K_{\rm conv}\sum_{r=1}^{k-j-1}q^r+K_{\rm bg}\right)m_i\\
&\le\left(\frac{9e^{2\eta}K_{\rm conv}}{1-q}+K_{\rm bg}\right)m_i.\tag{14}
\end{aligned}$$

The last line uses the looser $1/(1-q)$ bound of `window_conversion_core`; $q/(1-q)$ is also valid. Summing (14) over the finite pieces, `PieceWindowSetup.windowAction_eq_sum` and `Region.actionRegionC_additive` give

$$\sum_i T_{i,j_i+1}=\widehat\beta_k A^w_{X_{\rm win}}-C,qquad
|C|\le C_{15}\sum_i m_i,quad
C_{15}=\frac{9e^{2\eta}K_{\rm conv}}{1-L^{-2\gamma}}+K_{\rm bg}.\tag{15}$$

Define $C=\widehat\beta_k A^w_{X_{\rm win}}-\sum_iT_{i,j_i+1}$. Under hypothesis 4 its terms are analytic, so $C$ is analytic. Formula (15) is exactly the orientation of `window_conversion_pieces` and of `WindowCompose.sum_mainActionLoc_eq_gen` after taking real parts. Every inequality in (6)–(15) is finite or elementary; the remaining work is to establish the hypotheses 1–4 for the actual history, with constants fixed before the final large-$\beta$ threshold.

## Lean shape and what is unblocked

Keep `ActionConvInput` as a record of estimates. For the history use `PieceWindowSetup`, `pieceChain`, `pieceChain_T`, and `WindowCompose.sum_mainActionLoc_eq_gen`. A useful new wrapper should take a physical history piece and prove the following before invoking `window_conversion_pieces`:

```lean
-- schematic binders: i is the actual (j,P,c) piece, j = jf i
hβnorm : βk = betaCanon S.d S.L (cs.beta (m' + 1)) (m' + 1) 0
hmixed  : (decomp i).total = physicalMixedCount i
hreads  : LocalWindowActionReadsAgreeOrSupported i
hrelC   : ∀ n a, ... → ‖βhat n * counterC ((decomp i).cube a) ...‖
                       ≤ cCrel * rho i n * (decomp i).wt a
hrelW   : ∀ n q, ... → ‖βhat (n-1) * starPairOn ((decomp i).wall q) ...‖
                       ≤ cWrel * rho i n * (decomp i).wt ((decomp i).wallCube q)
hpair   : SupportedLocalWindowResponse i -- (4)-(5), all action reads, common complex tube
hweight : NormalizedWindowReadBudget i -- the three weight sums in (9)
```

`hrelC`/`hrelW` plus `StepDecomp.sum_le` prove the exact `p7_first` binder of `window_conversion_pieces`; `hreads`/`hpair`/`hweight` and (9)–(12) prove its exact `window_decay` binder. `analytic_T`/`analytic_win` then follow from the common holomorphic background/data germs and finite sums; in the existing `sum_mainActionLoc_eq_gen` specialization they are already theorems by `U=Unit`. If a window includes the $k_0\to k_0+1$ mass switch, add a named regional mass/boundary-flux term of `INTERFACE-A.md` and `MASS-RESPONSE.md`; it cannot be put into `hpair` as a supported data response.

The geometry now landed as `Balaban.LargeField.exists_region_Xfine_window` (`R/WindowRegion.lean`), `Balaban.LargeField.exists_region_window` (`R/WindowRegionUnion.lean`), and `Balaban.LargeField.mainActionLoc_congr_nodes` (`R/WindowNodeCongr.lean`) helps construct the pieces and node independence. It does not prove `hreads`: site/layer agreement does not identify the collar values or the half-bond action. `Balaban.LargeField.ActionConv.window_margin` and `sup_linear_sub_sq` (`R/ActionConvReduce.lean`) cover the arithmetic in (11)–(12). `Balaban.Fluctuation.lemma41_domain_uncond` (`Fluctuation/FarDecayUncond.lean`) and `Balaban.Background.theorem73_complex` (`Background/Theorem73.lean`) are candidate response/composition tools, but their fixed-generating-set, support and complex-domain premises must be instantiated for each local/window pair. `Balaban.Fluctuation.weightedProp51S_exists` (`Fluctuation/WeightedProp51.lean`) does not create distance decay for the distributed mass source.

Once those local premises are proved, (15) supplies the `Ckk` action loss used by `WindowCompose` and then by `window_quotient_of_history`/`removed_quotient_le_of_history`. It does not by itself close the quotient's collar, cutoff, Gaussian normalization or mass-switch inputs described in `LF4R-PLAN.md` §9 and `INTERFACE-A.md` §3.

**Confidence.** High for the exact Lean inventory, the two refutations as failures of inference from landed premises, and the finite inequalities (6)–(15). Moderate for (12) as the right physical normalization until the actual local/window action reads and complex support are checked. Low that the specialized P7 window estimates can be proved from currently landed hypotheses alone. The surviving findings are `EXTRA-HYP` for the physical theorem, not a counterexample to Balaban's properly normalized history.
