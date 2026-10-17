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

$$R_{j,n}=T_{j,j+1}-T_{j,n}=-\frac B2 H_X,\qquad
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

$$\sum_i T_{i,j_i+1}=\widehat\beta_k A^w_{X_{\rm win}}-C,\qquad
|C|\le C_{15}\sum_i m_i,\quad
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

# Part 2. Flow arithmetic and the physical local/window premises

**Verdict (17 October 2026).** The coefficient-increment part of the requested RG flow premise is an exact consequence of the RG recursion, once the fields of OpConsts are identified with that recursion. The source/action estimate p7_first does not follow from the available coefficient and background theorems: a regional response bound that retains the energy scale of the *originating* piece is still required. The supported, normalized comparison with the window action is also not landed. Moreover, pieceChain carries a piece-dependent layer coefficient at its final scale, while PieceWindowSetup.ak is common to all pieces; this mismatch must be charged as a conversion cost. Below I prove the exact flow arithmetic, a quantitative implication to p7_first, an explicit coefficient-mismatch charge, and the corrected finite window conclusion. I do not claim that the remaining physical hypotheses are proved.

This continuation reads the read-only Lean tree at commit 260b3843826ac1b24b954b248beb72a77dc818fd. Primary sources: P7, journal **pp. 500–501**, (2.10)–(2.16); P6, journal **pp. 6–7**, (2.13)–(2.16), **p. 11**, (2.25) and following wall discussion, **p. 14**, (2.31); P3, journal **p. 56**, (2.55)–(2.56). The P3 text layer is badly garbled at the formulas, so I do not extract a numerical rate from it. LF4R-PLAN.md §9, P631-INPUTS-2.md §§1–3, MASS-RESPONSE.md §§1–2 and INTERFACE-A.md §§1,4 are secondary status/derivation notes, not substitutes for the physical estimates.

## 2.1 Exact incremental flow

Let $e=d-2$, $q=L^{-2\gamma}\in(0,1)$, and write $\xi_{t,3}=\xi\,t\,2$, $\xi_{t,2}=\xi\,t\,1$ for the zero-based Lean coordinates of the RG parameter. **Assume the missing identification** of the operator constants with the real RG flow:

$$
\operatorname{cs.beta}(n)=\beta L^{ne}g_n,\qquad
\operatorname{cs.muAct}(n)=\nu\delta_n,\qquad
g_n=\operatorname{gammaSeq}(\xi,n),\quad
\delta_n=\operatorname{deltaSeq}(\xi,n).
\tag{16}
$$

Here $\beta,\nu>0$, the complex product values on the right are real and positive, and
$e^{-\eta}\le g_n,\delta_n\le e^\eta$ for all $n\ge0$. The global envelope is what the exact
hflow binder requires, even though its coefficient equality is restricted to the window. The second identification is precisely
$\operatorname{nuSeq}_n/L^{2n}=\nu\delta_n$, the fine-mass convention in pieceChain. The fields of OpConsts in LargeField/Operators/Setup.lean are independent functions; neither this identification nor its positivity follows from the structure.

Take the quantitative RG step estimate

$$
\|\xi_t\|_\infty\le C_\xi\beta^{-1}q^{t+1},
\qquad C_\xi=\operatorname{rgCxi}(B,\alpha_0)=168B/\alpha_0^2.
\tag{17}
$$

Flow.RGInfty.rg_step_infty proves (17) at one step under its analytic and smallness hypotheses; norm_xi_le_of_step is its inductive interface. Flow.RunningCoefficients.betaSeq_eq, nuSeq_eq and norm_gammaSeq_le yield the product formula and bounds. LargeField.Analytic.RunningHyp.of_flow gives a running envelope if the real betaRun/nuRun are identified with those sequences. None of these declarations identifies them with cs. FlowSeq.Matches in LargeField/Counter/FlowHorizon.lean relates geometry/counter parameters, not cs.

Set $\widehat\beta_n=\operatorname{betaCanon}(d,L,\operatorname{cs.beta}(n),n,0)=\beta g_n$. The definitions in Flow/RunningCoefficients.lean give

$$
g_{n-1}=g_n(1+\xi_{n-1,3}),\qquad
\delta_n=\delta_{n-1}\frac{1+\xi_{n-1,3}}{1+\xi_{n-1,2}}.
\tag{18}
$$

The denominators are nonzero because the identified positive RG sequences satisfy the recursions. Substitution into the *exact* definitions of PieceChain.pieceChain gives, for every $n\ge j+2$,

$$
\begin{aligned}
b_n&:=\widehat\beta_{n-1}-\widehat\beta_n
       =\widehat\beta_n\xi_{n-1,3},\\
\widehat\beta_{n-1}\nu_{n-1}
  &=\widehat\beta_n\nu_n(1+\xi_{n-1,2}),\\
e_n&:=\frac{\widehat\beta_{n-1}\nu_{n-1}
                 -\widehat\beta_n\nu_n}{\nu_n}
       =\widehat\beta_n\xi_{n-1,2},\\
a_n(\ell)&=a_{n-1}(\ell)(1+\xi_{n-1,3}),\qquad
\widehat\beta_n a_n(\ell)=\widehat\beta_{j+1}\operatorname{cs.aw}(\ell),\\
\nu_n-\nu_{n-1}
  &=\nu_{n-1}\frac{\xi_{n-1,3}-\xi_{n-1,2}}{1+\xi_{n-1,2}} .
\end{aligned}\tag{19}
$$

For the second equality, multiply the two RG recursions first and cancel $L^{ne}$ and $L^{2n}$; it is exact. The fourth is exactly the coefficient invariant already used by ConvChain.coeff. The datum is fixed as locData throughout pieceChain, so the dataInc term of ActionConvDef.counterP and counterQ is zero. The background change and its crossing-wall term are not zero.

Since $g_n\le e^\eta$, (17)–(19) imply, with no unspecified constant,

$$
|b_n|,\ |e_n|\le C_\xi e^\eta q^n.
\tag{20}
$$

Let $\varepsilon_n=\operatorname{epsSeq}(L,\alpha,\alpha_0,n)=\alpha_0t_nL^{-\alpha n}$, $t_n=\operatorname{epsTail}(n)$. ActionConvRatio.one_le_epsTail and epsTail_lt_three give $1\le t_n<3$; the nonnegative tail also gives $t_{j+1}\ge t_n$ for $n\ge j+1$. If $e-2\alpha=2\gamma$, the *scale-coupling* ratio used by WindowCompose.sum_mainActionLoc_eq_gen is

$$
\rho_{j,n}
=\frac{\operatorname{cs.beta}(j+1)\varepsilon_{j+1}^{2}}
       {\operatorname{cs.beta}(n)\varepsilon_n^{2}}
=\frac{g_{j+1}}{g_n}\left(\frac{t_{j+1}}{t_n}\right)^2q^{n-j-1}.
\tag{21}
$$

Consequently $\rho_{j,n}\ge e^{-2\eta}q^{n-j-1}$ and, since $q^n\le q^{n-j-1}$ for $j\ge0$,

$$
|b_n|,\ |e_n|\le C_\xi e^{3\eta}\rho_{j,n}.
\tag{22}
$$

Thus (16) gives the **exact Lean hflow witness** in WindowCompose.sum_mainActionLoc_eq_gen: $B=\beta$, $gg=g$, with the stated two-sided envelope. Equations (19)–(22) are the proved coefficient arithmetic conditional on (16)–(17); they are not yet an instance for the actual cs.

### The missing source estimate and a quantitative reduction

The exact p7_first hypothesis of WindowCompose.sum_mainActionLoc_eq_gen, for a piece $i=(j,P,c)$ and $j+2\le n\le k$, is

$$
\|(\operatorname{chain}i).\operatorname{cost}()n\|
\le K_{\rm conv}\rho_{j,n}m_i,\qquad
m_i=(\operatorname{decomp}i).\operatorname{total}.
\tag{23}
$$

A precise sufficient *origin-energy sensitivity* theorem would be

$$
\|(\operatorname{chain}i).\operatorname{cost}()n\|
\le K_{\rm src}\operatorname{cs.beta}(j+1)\varepsilon_{j+1}^{2}
                 \|\xi_{n-1}\|_\infty m_i .
\tag{24}
$$

This must include both the regional cube counterterm and the P6 (2.31) half-bond cut term. From (17), (21) and (24), multiply and divide by $\operatorname{cs.beta}(n)\varepsilon_n^2$:

$$
\begin{aligned}
\|(\operatorname{chain}i).\operatorname{cost}()n\|
&\le K_{\rm src}C_\xi
   \frac{\operatorname{cs.beta}(n)\varepsilon_n^2}{\beta}q^n
   \rho_{j,n}m_i,\\
\frac{\operatorname{cs.beta}(n)\varepsilon_n^2}{\beta}q^n
&=g_n\alpha_0^2t_n^2\le9e^\eta\alpha_0^2 .
\end{aligned}\tag{25}
$$

Therefore (24) **proves exactly (23)** with

$$K_{\rm conv}=9K_{\rm src}C_\xi\alpha_0^2e^\eta
=1512K_{\rm src}B e^\eta.\tag{26}$$

Separate cube and wall versions of (24) also suffice, with
$K_{\rm src}=K_{\rm cube}+I K_{\rm wall}$ when StepDecomp.inc is at most $I$, by StepDecomp.sum_le.

**(24) is not landed or proved by the named premises.** It asserts that all reads of the fixed $(j,P,c)$ action retain the originating energy $\operatorname{cs.beta}(j+1)\varepsilon_{j+1}^2m_i$ while the scale-$n$ variation is linear in $\xi_{n-1}$. P6 p. 11 (2.25) gives an absolute $O(\beta_n^{-1})$ cube bound and the following paragraph gives an absolute wall bound after a cut-response estimate. P6 p. 14 (2.31) is the regional identity. Neither contains the starting index $j$ in the bound. ActionConvInput.cost_le similarly gives only $(c_C+c_W I)m_i$. The raw RG bound can produce an order-one cost because $\operatorname{cs.beta}(n)\varepsilon_n^2\|\xi_{n-1}\|\asymp1$ by (25); the originating-piece energy restriction is precisely the extra gain. Background.theorem71/theorem72 prove minimizers, Euler–Lagrange equations, units and fixed-coefficient bounds; Background.theorem72_linearResponse varies *data* at fixed coefficients. They do not prove the coefficient derivative, the P6 cut-source response, or (24). In the massless branch, ActionConvDef.counterR has an additional $\nu\,\operatorname{massPair}(w,\phi-h)$ term and must be included in this source bound.

Thus Part 2 proves the increment identities and the implication (24) $\Rightarrow$ p7_first, not p7_first for the physical history. This is an exact unclosed Lean premise, not a generic appeal to P7 (2.11).

## 2.2 Local versus window actions: reads, coefficients and support

For a physical piece, pieceChain uses the local generating set locGen, datum locData (the lifted step-$j$ variable and step-$j+1$ output), initial locBg, and later bgFieldC of the *same* local datum. Its Xc sites are Xfine. WindowCompose.sum_mainActionLoc_eq_gen compares this with actionRegionC on Xw in Wp.windowGenSet, at the common ak, νk, βk, Datw and φw. WindowRegion.windowGen_layerIndex_eq and pieceGen_layerIndex_eq prove layer agreement on piece sites. WindowNodeCongr.locData_congr_psi is a same-local-generating-set data congruence. Neither theorem identifies the two full data objects on block reads and exterior endpoints of crossing bonds. Region.starWeight is $1/2$ on those crossing bonds, so site agreement alone does not normalize the regional action.

There is a separate **exact coefficient mismatch**. At the terminal scale $k$, (19) gives

$$
\widehat\beta_k(\operatorname{chain}i).a(k,\ell)
=\widehat\beta_{j+1}\operatorname{cs.aw}(\ell).
\tag{27}
$$

PieceWindowSetup.ak is one common function of $\ell$. If two pieces $j,j'$ read a common layer $\ell$ with $\operatorname{cs.aw}(\ell)\ne0$, exact matching of both block coefficients to $\widehat\beta_k\operatorname{ak}(\ell)$ would force
$\widehat\beta_{j+1}=\widehat\beta_{j'+1}$. The RG recursion permits nonzero $\xi_3$ and does not supply this equality. This shows why a proof of window_decay based solely on replacing the background cannot identify the actions without a coefficient charge. It does not assert that every particular history has two such nonzero reads.

Here is the finite comparison that must be instantiated after transporting both actions to the same site, block and bond reads. Put $r_x=D.\Psi_x-Q\phi_x$, $g_b=\partial\bar\phi_b$, $s_x=\phi_x-h_x$, and use primes for the target. Let $c_x,c'_x$ be the layer coefficients, $\mu,\mu'$ the physical masses, and $\omega_b\in\{1,\frac12\}$ the common star weights. For the complex *bilinear* action, set $|v|_1=\sum_{a=1}^N|v_a|$. Expanding each square and using $|v\cdot w|\le|v|_1|w|_1$ proves term by term

$$
\begin{aligned}
|A-A'|\le {}&
\frac12\sum_{x\in X}\!
 \left[|c_x-c'_x|\,|r_x|_1^2+
 |c'_x|\bigl(2|r_x|_1|\Delta r_x|_1+|\Delta r_x|_1^2\bigr)\right]\\
&+\frac12\sum_{b:\,\omega_b>0}\!\omega_b
 \left(2|g_b|_1|\Delta g_b|_1+|\Delta g_b|_1^2\right)\\
&+\frac12\sum_{x\in X}\!
 \left[|\mu-\mu'|\,|s_x|_1^2+
 |\mu'|\bigl(2|s_x|_1|\Delta s_x|_1+|\Delta s_x|_1^2\bigr)\right].
\end{aligned}\tag{28}
$$

Indeed $(v+w)\cdot(v+w)-v\cdot v=2v\cdot w+w\cdot w$, and the coefficient difference is separated as
$c r^2-c'(r+\Delta r)^2=(c-c')r^2-c'(2r\Delta r+\Delta r^2)$; similarly for mass. If the transport changes a read set or star weight, its unmatched absolute term must be added. Equation (28) is a full finite proof, with no stationarity cancellation of half-bonds.

For the *supported* part of P7 (2.14), a physical theorem must supply a common-cover/Precedes pair of local and window data, equal $h$, two complex domain witnesses, a datum increment supported outside distance
$a_j=2M[\widehat R_j]-M-2M_1$ from **every** action read, and field/first-difference response at most $K_Rr_je^{-2\gamma_w a_j}$ there. P6 p. 6 (2.13) gives the displayed longer-distance exponential for its own pair; P7 p. 501 invokes it for the inverse change (2.14). Fluctuation.lemma41_domain_uncond in FarDecayUncond.lean proves a supported response only for two data on one fixed generating set, fixed $a,\nu,h$, under its support, operator, numerical and *both* complex-domain premises. Background.theorem73_complex supplies composition for a Precedes pair under its own domain hypotheses. Neither constructs this actual local/window pair.

The other requirement is an absolute normalized action-read budget, including the block, kinetic and mass first variations and all crossing endpoints, of
$C_{\rm act}(d,L,N,\text{radii})\operatorname{cs.beta}(j+1)r_j^2m_i$ after transport to scale-$(j+1)$ units. Part 1 (9)–(12) proves the decay estimate from such a budget and the supported response. The newer actual-window theorem RegionHistory.dataChangeBound'_windowOfHistory_of_bdryTop in DeltaPsiCollarActualWindow.lean bounds the *later* change $\widetilde\psi-\psi^0_{k_1,k}$, subject to hband, hoff, hxb, etc.; DeltaPhi.deltaPhi_le_of_dataChange uses that datum comparison. They do not identify locData with the P7 window datum or prove the above read budget. The physical collar itself must be used; choosing a convenient clipped datum changes the action (INTERFACE-A.md §4).

The coefficient mismatch can be charged uniformly once its originating block energy is bounded. For the illustrative fine-unit normalization
$\beta_k^{\rm target}=\widehat\beta_k$ and $\operatorname{ak}=\operatorname{cs.aw}$, and *assuming identical transported field/data reads*, the coefficient part is exactly

$$
R_i^{\rm coef}
=\frac12\sum_{x\in X_i}
 \frac{(\widehat\beta_{j+1}-\widehat\beta_k)
       \operatorname{cs.aw}(\ell_x)}{L^{2\ell_x}}\,
       r_x\cdot r_x .
\tag{29}
$$

Put $B_i=\frac12\sum_{x\in X_i}L^{-2\ell_x}
|\operatorname{cs.aw}(\ell_x)|\,|r_x|_1^2$. Then
$|R_i^{\rm coef}|\le|\widehat\beta_{j+1}-\widehat\beta_k|B_i$.
Telescoping (20) gives

$$
|\widehat\beta_{j+1}-\widehat\beta_k|
\le\sum_{n=j+2}^k|b_n|
\le C_\xi e^\eta\,q^{j+2}/(1-q).
\tag{30}
$$

Assume the explicit originating block-energy bound
$\widehat\beta_{j+1}B_i
\le C_B\operatorname{cs.beta}(j+1)\varepsilon_{j+1}^2m_i$.
Since $\widehat\beta_{j+1}\ge\beta e^{-\eta}$ and
$(\operatorname{cs.beta}(j+1)\varepsilon_{j+1}^2/\beta)q^{j+1}
=g_{j+1}\alpha_0^2t_{j+1}^2\le9e^\eta\alpha_0^2$, (29)–(30) yield

$$
|R_i^{\rm coef}|
\le\frac{9C_BC_\xi\alpha_0^2e^{3\eta}q}{1-q}\,m_i .
\tag{31}
$$

This is a fixed **order-one per-cube** charge, not generally an $e^{-R_{j-1}}$ charge. For a different physical ak, the exact numerator in (29) is
$\widehat\beta_{j+1}\operatorname{cs.aw}(\ell_x)
-\widehat\beta_k\operatorname{ak}(\ell_x)$; it requires its own bound. Equations (29)–(31) do not prove the transport or energy premise for actual pieces.

## 2.3 Mass switch and the corrected uniform theorem

At a zero-mass to complete-solver switch, the source $-\mu(\phi^m-h)$ is distributed across the variational domain. LargeField/R/MassResponseHyp.lean:massChange_sameData_response proves a **weight-one** same-datum response with $K_m=\sqrt N K_w$ under its GreenSetting, Dec2.OpSetting, BgBounds, smallness, common-collar and mass hypotheses. It gives no boundary distance decay. MassChangeWall.massChange_wall_bound_of_bounds proves, with its response, gradient and Hessian premises,

$$
\beta\,|A_D(\phi^0)-A_D(\phi^m)|
\le\tfrac12 C_H(K_mB_h)^2\beta m^2 n
  +K_mB_h\,\beta m\sum_{b\in\operatorname{crossing}(D)}r_b .
\tag{32}
$$

MassChangeHessian.massChange_region_bound_of_response obtains the chord premise under pointwise read/count hypotheses. MASS-RESPONSE.md §2 derives the conditional physical scale-$q=k_0+1$ charge
$(C_D\beta_qm^2+C_W\beta_qm\delta_{k_0})|X|_q$, with
$C_D=(d+2)M^dL^2K_m^2B_h^2$ and
$C_W=2dM^{d-1}L^2K_mB_h(3dLK_1)$.
At the switch $\beta_qm\le e^{2\eta}L^d$ gives a uniform charge, **provided** those physical site/crossing, collar, domain and gradient hypotheses hold. INTERFACE-A.md (1.3) and its one-site test show why the regional half-bond flux cannot be replaced by a purely quadratic bulk estimate. PieceChain.pieceChain fixes one MassBranch at later scales but its initial locBg uses cs.mu(j+1) regardless of br; branch coherence
$\operatorname{cs.mu}(j+1)=\operatorname{br.elMass}(\operatorname{cs.muAct}(j+1))$
or an initial switch charge must also be proved.

The nearest uniform replacement for the physical window_decay input is

$$
\|(\operatorname{chain}i).T()k
-\beta_k^{\rm target} A_{X_i^w}(\operatorname{ak},\nu_k;D^w,\phi^w)\|
\le\bigl(K_{\rm pair}e^{-\gamma_wD_j}
      +K_{\rm coef}+K_{\rm switch}+K_{\rm read}\bigr)m_i,
\quad
D_j=M([\widehat R_{j-1}]-1)-2M_1.
\tag{33}
$$

Here $K_{\rm pair}$ is the explicit Part 1 (12) constant **if** the supported pair and normalized reads are supplied; $K_{\rm coef}$ may be (31) under its energy/transport hypotheses; $K_{\rm switch}$ follows from (32) after its physical hypotheses; $K_{\rm read}$ pays unmatched data, mass, normalization or cut reads in (28). They may depend on $d,L,N$ and the fixed history radius, separation, chart and incidence constants, but must be fixed before the final large-$\beta$ threshold. For $j=0$, replace $D_j$ by an explicitly proved base-layer bound, as explained in Part 1. Equation (33) is a **specification**, not currently an established statement for the physical history.

The proof of ActionConv.window_conversion_core uses its exponential window_decay only to infer the uniform bound $\|T_{i,k}-W_i\|\le K_{\rm bg}m_i$ from $D_j\ge0$. Hence (23) and (33) prove the same final window conclusion with

$$
C_{15}=
\frac{9e^{2\eta}K_{\rm conv}}{1-q}
+K_{\rm pair}+K_{\rm coef}+K_{\rm switch}+K_{\rm read},
\qquad q=L^{-2\gamma}.
\tag{34}
$$

Proof: ConvChain.telescope gives
$T_{i,j+1}=T_{i,k}+\sum_{n=j+2}^kR_{i,n}$.
By (23), ActionConvRatio.p631_ratio_free and the finite geometric sum,
$\|\sum R_{i,n}\|
\le9e^{2\eta}K_{\rm conv}(1-q)^{-1}m_i$.
Add (33) and use $e^{-\gamma_wD_j}\le1$; sum over the finite pieces. PieceWindowSetup.windowAction_eq_sum identifies the target action, and PieceChain.pieceChain_T identifies the initial real parts with mainActionLoc. This proves (34) as an exact **conditional finite-action theorem**. For WindowCompose.sum_mainActionLoc_eq_gen, the analyticity inputs are constant because it specializes to U=Unit; for a nontrivial P5 (1.32) complex family, analytic data transport and domains remain separate requirements.

## 2.4 Lean shape, remaining blockers, confidence

The arithmetic (19)–(22) should be a lemma parametrized by a real $\xi$, positive RG sequences, cs : OpConsts and explicit equations (16). Its conclusions are the equations for (chain i).β (n-1) - (chain i).β n and (chain i).e n in (19), their bounds (20), and hflow with $B=\beta$, $gg=g$. It discharges **hflow after the cs–flow identification**. To discharge the *exact* p7_first hypothesis of WindowCompose.sum_mainActionLoc_eq_gen, a new physical lemma must prove (24) for every $(j,P,c)$ from locGen, locData, locBg and the P6 cut response; (25)–(26) then provide its constant. This differs from ActionConvInput.p7_first, whose denominator uses fine-unit chain.β; the history consumer correctly uses scale couplings cs.beta.

For window_decay, the needed physical lemma must choose or identify
$\beta_k^{\rm target}=\operatorname{betaCanon}(d,L,\operatorname{cs.beta}(k),k,0)$ in the actionRegionC fine-unit convention, verify the actual torus cast and every site, block, exterior and half-bond read, construct the supported common-cover pair with both complex domains, apply the fixed-G response to that pair, and pay (27) and any mass-switch/cut mismatch. If the coefficient and switch charges do not have exponential decay, change the window_conversion_pieces and WindowCompose.sum_mainActionLoc_eq_gen binder to (33), or just its uniform consequence. Their existing finite proof then yields (34) with a revised $K_{\rm bg}$.

**Proved here:** the exact incremental identities and constants conditional on identification (16) and RG step estimate (17); the implication (24) to p7_first; the coefficient mismatch formula and conditional fixed charge (29)–(31); the conditional final $C_{15}$ (34). **Still open for a nonempty actual RG history:** (16) as a cs equality, the regional origin-energy/source estimate (24), the P7 (2.14) supported local/window pair and normalized action reads, and any switch/collar hypotheses needed for (32). The landed theorems named above do not state those claims, so blocker 4 is not closed by this continuation.

**Confidence.** High for the algebra and finite inequalities (18)–(22), (25)–(31), (34), and for the exact Lean interface distinctions. Moderate that (24) is the best source interface; a direct relative cube/wall estimate could be preferable. Low that either p7_first or window_decay for the actual history follows without new physical coefficient-response and collar/read theorems.

### Exact consumer binders

For avoidance of ambiguity, the three source inputs below are copied in mathematical Lean shape from WindowCompose.sum_mainActionLoc_eq_gen (its final scale is m' + 1). The equations and implications proved in Part 2 discharge precisely the portions stated in the right column:

| Consumer input | Exact hypothesis at the history theorem | What Part 2 establishes |
|---|---|---|
| hflow | $\forall i,\ \exists B:\mathbb R,\ 0<B\ \land\ \exists gg:\mathbb N\to\mathbb R,\ (\forall m,\exp(-\eta)\le gg(m)\land gg(m)\le\exp\eta)\ \land\ \forall m,\ jf(i)+1\le m\le m'+1\Rightarrow\operatorname{cs.beta}(m)=B L^{(d-2)m}gg(m)$ | (16) with global envelope gives $B=\beta$, $gg=g$. The cs identification is still open. |
| p7_first | $\forall i,m,\ jf(i)+2\le m\le m'+1\Rightarrow\|(\operatorname{chain}i).\operatorname{cost}()m\|\le K_{\rm conv}\,[\operatorname{cs.beta}(jf(i)+1)\varepsilon_{jf(i)+1}^2/(\operatorname{cs.beta}(m)\varepsilon_m^2)]\,(\operatorname{decomp}i).\operatorname{total}$ | (24) and (17) imply this with (26). The physical instance of (24) is open. |
| window_decay | $\forall i,\ \|(\operatorname{chain}i).T()(m'+1)-(\beta_k:\mathbb C)\operatorname{actionRegionC}(Xw(i),ak,\nu_k,Datw,\phi_w)\|\le K_{\rm bg}\exp[-\gamma_w(M_0(Rhat(jf(i)-1)-1)-2M_1)](\operatorname{decomp}i).\operatorname{total}$ | The supported-pair portion follows conditionally from Part 1 (9)–(12). Coefficient, switch and read mismatches require (33); the existing exponential binder has not been discharged. |

A corrected Lean consumer may take the same hflow and p7_first binders and replace window_decay with the **uniform** binder
$\forall i,\ \|(\operatorname{chain}i).T()(m'+1)-(\beta_k:\mathbb C)\operatorname{actionRegionC}(Xw(i),ak,\nu_k,Datw,\phi_w)\|\le K_{\rm win}(\operatorname{decomp}i).\operatorname{total}$,
where $K_{\rm win}=K_{\rm pair}+K_{\rm coef}+K_{\rm switch}+K_{\rm read}$. The proof of ActionConv.window_conversion_core already reduces its exponential binder to this exact bound before the final triangle inequality; no change to its geometric sum is needed. One should retain the exponential as a separate stronger theorem only for the genuinely supported background portion.

The Part 2 calculation is prose, not Lean code, and no Lean file was edited or built. It supplies proof targets and constants, while explicitly leaving their physical hypotheses open.

Verbatim binder fragment (with the already-bound variables of WindowCompose.sum_mainActionLoc_eq_gen):

    (p7_first : ∀ i, ∀ m, jf i + 2 ≤ m → m ≤ m' + 1 → ‖(chain i).cost () m‖ ≤ Kconv *
      ((cs.beta (jf i + 1) * ε (jf i + 1) ^ 2) / (cs.beta m * ε m ^ 2)) * (decomp i).total)
    (window_decay : ∀ i, ‖(chain i).T () (m' + 1) -
        (βk : ℂ) * actionRegionC (Xw i) ak νk Datw φw‖ ≤
      Kbg * Real.exp (-γw * (M₀ * (Rhat (jf i - 1) - 1) - 2 * M₁)) * (decomp i).total)
    (hflow : ∀ i, ∃ B : ℝ, 0 < B ∧ ∃ gg : ℕ → ℝ,
      (∀ m, Real.exp (-η) ≤ gg m ∧ gg m ≤ Real.exp η) ∧
      ∀ m, jf i + 1 ≤ m → m ≤ m' + 1 →
        cs.beta m = B * (S.L : ℝ) ^ ((S.d - 2) * m) * gg m)

The corrected uniform binder keeps the left side of window_decay verbatim and replaces its right side by Kwin * (decomp i).total. Equation (34) is then the corresponding C₁₅.

## Part 3. The regional source and the four terminal residuals

**17 October 2026. Verdict.** The five requested inequalities cannot presently be proved for a nonempty history from the landed history objects. The obstruction is mathematical in the *stated interfaces*, not an elaboration problem: `WindowCompose.sum_mainActionLoc_eq_gen` accepts an arbitrary `StepDecomp`, arbitrary target `ak, νk, βk, Datw, φw`, and one fixed `MassBranch`; its real-domain premise does not assert the originating-scale read energy, the P6 cut-source response, or the P7 supported common-cover comparison. Below are (i) an exact finite-action expansion and a proved six-budget implication to `hsource`, (ii) a canonical meaning and complete finite estimates for the four residuals, and (iii) exact reasons the physical instances are still missing. No Lean worktree was created and no file under `/home/scott/Balaban` was changed.

### 3.1 Exact Lean targets

The first binder is copied from `ActionConv.p7_first_of_rg_source` in `Balaban/LargeField/R/WindowConvSource.lean`; here $W:\texttt{PieceWindowSetup}\ d\ L\ N_0\ K\ N\ S\ \iota\ sc\ k_1\ k$:

```lean
hsource : ∀ i n, sc i + 2 ≤ n → n ≤ k → ∀ u ∈ S,
  ‖(W.chain i).cost u n‖ ≤
    Ksrc * (βs i (sc i + 1) * epsSeq L α α₀ (sc i + 1) ^ 2) *
      ‖ξ i (n - 1)‖ * W.mcount i
```

The four binders below are copied from `PieceWindowSetup.window_uniform_of_parts` in `Balaban/LargeField/R/WindowConvUniform.lean`. They are statements about **chosen** intermediate actions $P,Q,R:\iota\to U\to\mathbb C$; the theorem neither defines them nor imposes a physical meaning:

```lean
hpair : ∀ i, ∀ u ∈ S,
  ‖(W.chain i).T u k - P i u‖ ≤ Kpair * W.mcount i
hcoef : ∀ i, ∀ u ∈ S,
  ‖P i u - Q i u‖ ≤ Kcoef * W.mcount i
hswitch : ∀ i, ∀ u ∈ S,
  ‖Q i u - R i u‖ ≤ Kswitch * W.mcount i
hread : ∀ i, ∀ u ∈ S,
  ‖R i u - (W.βk : ℂ) *
    actionRegionC (W.Xw i) W.ak W.νk (W.Datw u) (W.φw u)‖ ≤
      Kread * W.mcount i
```

The history specialization is `WindowCompose.sum_mainActionLoc_eq_gen`: $j=sc(i)=jf(i)$, $k=m'+1$, $\beta_s(i,n)=\texttt{cs.beta}\ n$, $W.\texttt{chain}\ i=\texttt{pieceChain}$ by `hchain`, and $W.\texttt{mcount}\ i=(\texttt{decomp}\ i).\texttt{total}$. `ConvChain.step` proves $\texttt{cost}=T_{i,n-1}-T_{i,n}$; `PieceChain.pieceChain_T` identifies the real part of its first action with `mainActionLoc`. These are exact identities, not size estimates.

### 3.2 Exact source algebra and a sufficient six-budget theorem

Fix $i$, put $j=sc(i)$, $j+2\le n\le k$, and work on its **own** `locGen` and region $X_i^c$. Write $\widehat\beta=\texttt{(W.chain i).β}\ n>0$, $\widehat\beta_u=\texttt{(W.chain i).β}\ (n-1)$, $\mu=\texttt{(W.chain i).ν}\ n$, $\mu_u=\texttt{(W.chain i).ν}\ (n-1)$, $a=a_n$, $a_u=a_{n-1}$, $\phi=\phi_n$, $\phi_u=\phi_{n-1}$, and $w=\phi_u-\phi$. `pieceChain` keeps the full datum $D=\texttt{locData}$, including $h$, fixed. `ConvChain.coeff` and `ConvChain.mass` give

$$\widehat\beta_u a_u(\ell)=\widehat\beta a(\ell),\qquad
\widehat\beta_u\mu_u=\widehat\beta\mu+\mu e_n. \tag{35}$$

Under the `OpConsts`–RG identification and recursion of Part 2, `flow_increment_eq_of_ident` gives $b_n:=\widehat\beta_u-\widehat\beta=\widehat\beta\xi_{n-1,3}$ and $e_n=\widehat\beta\xi_{n-1,2}$. Set $\rho=\|\xi_{n-1}\|_\infty$; then $|b_n|,|e_n|\le\widehat\beta\rho$, $|\widehat\beta_u|\le\widehat\beta(1+\rho)$, and $|\widehat\beta_u\mu_u|\le\widehat\beta|\mu|(1+\rho)$.

For $x\in X_i^c$, let $\ell_x$ be its local layer, $c_x=a(\ell_x)L^{-2\ell_x}$, $r_x=D.\Psi_x-Q\phi_x$, $t_x=Qw_x$, $s_x=\phi_x-D.h_x$, and $w_x=\phi_{u,x}-\phi_x$. On every oriented fine bond of the torus put $\omega_b=\texttt{X.starWeight}(b)\in\{0,\frac12,1\}$, $g_b=\partial\bar\phi_b$, $v_b=\partial\bar w_b$; the exterior value of $\bar w$ is zero because the datum is fixed. Dots below are the complex **bilinear** coordinate sum. Direct expansion of the three squares in `actionRegionC` gives the exact equality

$$
\begin{aligned}
\texttt{(W.chain i).cost}\ u\ n={}&
 \frac{\widehat\beta}{2}\sum_{x\in X_i^c}c_x
          \bigl(-2r_x\!\cdot t_x+t_x\!\cdot t_x\bigr)\\
&+\frac{b_n}{2}\sum_b\omega_b\,g_b\!\cdot g_b
 +\widehat\beta_u\sum_b\omega_b\,g_b\!\cdot v_b
 +\frac{\widehat\beta_u}{2}\sum_b\omega_b\,v_b\!\cdot v_b\\
&+\frac{\mu e_n}{2}\sum_{x\in X_i^c}s_x\!\cdot s_x
 +\widehat\beta_u\mu_u\sum_{x\in X_i^c}s_x\!\cdot w_x
 +\frac{\widehat\beta_u\mu_u}{2}\sum_{x\in X_i^c}w_x\!\cdot w_x .
\end{aligned}\tag{36}
$$

To verify (36), use $r(\phi_u)=r(\phi)-Qw$, $g(\phi_u)=g(\phi)+\partial\bar w$, and $s(\phi_u)=s(\phi)+w$, then substitute (35). `ConvChain.step` identifies the resulting action difference with `cost`. The half-weighted crossing bonds are **already in the bond sums**. No stationarity cancellation has discarded them. P6 p. 14 (2.31) rewrites some of these terms using the Euler–Lagrange equation and displays the resulting surface flux; its extra cut source occurs in the equation used to bound $w$, even though it is invisible in the finite square expansion.

Use the Euclidean coordinate norm and define six nonnegative read energies

$$
\begin{array}{lll}
E_B=\sum_{x\in X_i^c}|c_x|\,|r_x|_2^2,&
E_G=\sum_b\omega_b|g_b|_2^2,&
E_M=|\mu|\sum_{x\in X_i^c}|s_x|_2^2,\\
E'_B=\sum_{x\in X_i^c}|c_x|\,|t_x|_2^2,&
E'_G=\sum_b\omega_b|v_b|_2^2,&
E'_M=|\mu|\sum_{x\in X_i^c}|w_x|_2^2 .
\end{array}\tag{37}
$$

The bond sums include every positive-weight internal and crossing bond. Let
$A_i=\texttt{cs.beta}(j+1)\varepsilon_{j+1}^2\,W.\texttt{mcount}(i)\ge0$.
Suppose $0\le\rho\le1$ and six fixed nonnegative constants $B_B,B_G,B_M,B'_B,B'_G,B'_M$ satisfy, **uniformly in the physical piece, conversion scale, and allowed configuration**,

$$
\begin{array}{lll}
\widehat\beta E_B\le B_B A_i,&
\widehat\beta E_G\le B_G A_i,&
\widehat\beta E_M\le B_M A_i,\\
\widehat\beta E'_B\le B'_B A_i\rho^2,&
\widehat\beta E'_G\le B'_G A_i\rho^2,&
\widehat\beta E'_M\le B'_M A_i\rho^2 .
\end{array}\tag{38}
$$

Then the **exact `hsource` binder** follows with

$$
K_{\rm src}=
\frac{B_G+B_M}{2}
 +\sqrt{B_BB'_B}
 +2\sqrt{B_GB'_G}
 +2\sqrt{B_MB'_M}
 +\frac{B'_B}{2}+B'_G+B'_M . \tag{39}
$$

Here is every inequality. The complex bilinear Cauchy bound gives
$|\sum c_xr_x\cdot t_x|\le\sqrt{E_BE'_B}$, and analogously for the $G,M$ sums. By (36) and $\rho\le1$,

$$
\begin{aligned}
|\texttt{cost}| \le\widehat\beta\bigl[
 &\tfrac{\rho}{2}(E_G+E_M)+\sqrt{E_BE'_B}
 +2\sqrt{E_GE'_G}+2\sqrt{E_ME'_M}\\
 &+\tfrac12E'_B+E'_G+E'_M\bigr].
\end{aligned}\tag{40}
$$

For example $\widehat\beta\sqrt{E_BE'_B}
=\sqrt{(\widehat\beta E_B)(\widehat\beta E'_B)}
\le\sqrt{B_BB'_B}\,A_i\rho$. Substitute all six inequalities (38) into (40); the last three terms are bounded by $(B'_B/2+B'_G+B'_M)A_i\rho^2\le(\cdots)A_i\rho$. This is (39) times $A_i\rho$, exactly `hsource`. It also covers $\rho=0$: (38) forces all response read energies to vanish, so `cost=0`.

**What (38) requires physically.** The unprimed three inequalities retain the energy of the *originating* scale $j+1$ on all reads of the later action, including the actual physical mass and crossing bonds. The primed three require a regional response proportional to the RG increment on those same reads. `theorem71`/`theorem72` give existence, EL, hard-spin and fixed-coefficient bounds; `theorem72_linearResponse` varies the **datum** at fixed coefficients. `MassChangeRegion.massChange_region_bound` varies the mass at fixed coefficients under its own full-domain, operator, spacing and region-cardinality hypotheses. None states (38) for the coefficient-and-mass step of `pieceChain`, including the P6 cut source. P6 p. 11 (2.25) and the following wall paragraph give an absolute per-cube bound, while p. 14 (2.31) invokes P2 response for the additional cut source; they do not assert the $j$-dependent factors in (38). P7 p. 500 (2.11) cites that discussion but does not supply a separate proof of the originating-energy gain. Thus (38) is a precise sufficient theorem target, **not** a theorem already obtained from the history.

There are two independent, exact interface obstructions to deducing `hsource`. First, `ActionConvWindow.StepDecomp` requires only `wt_nonneg`. For **any** region $X$, take one cube indexed by `Unit` equal to $X$, give it weight zero, take one wall equal to `X.crossing` and assign it to that cube, with incidence bound one. All `StepDecomp` fields hold and `total=0`, even if $X$ is nonempty. `WindowCompose.sum_mainActionLoc_eq_gen` takes `decomp` as an argument and does not require physical cube weights. Any nonzero conversion cost then contradicts `hsource`, regardless of $K_{\rm src}$. This proves that a canonical positive mixed-count construction, or at least lower bounds paying every action read, is indispensable.

Second, `OpConsts.mu` and `OpConsts.muAct` are independent fields. `PieceChain.pieceChain` starts with `locBg` at mass `cs.mu (j+1)`, but at $n=j+2$ uses `bgFieldC` at `br.elMass (cs.muAct n)`. Neither `hchain` nor `hS` states branch coherence at the starting scale. The missing equality is

$$
\texttt{cs.mu}(j+1)=
\texttt{br.elMass}(\texttt{cs.muAct}(j+1)), \tag{41}
$$

with an explicit one-time mass switch instead when the window crosses $k_0$. A finite hard-spin chart shows why this matters. For unit spins at angles $\theta,u$, $0<u<\pi/2$, and field $h=(1,0)$, let
$A_m(\theta)=a(1-\cos(\theta-u))+m(1-\cos\theta)$, $a,m>0$.
The massless minimizer is $\theta_0=u$, while $A'_m(u)=m\sin u>0$, so its nearby massive minimizer $\theta_m$ differs and $A_m(\theta_0)>A_m(\theta_m)$. Keep all action coefficients and datum fixed, take the first background mass zero and the next complete background mass $m$, and set $\xi=0$. Then the one-step action difference is
$\widehat\beta[A_m(\theta_0)-A_m(\theta_m)]>0$ but the `hsource` right side is zero. This is a model-level witness for the missing (41), not a constructed counterexample to an RG history in which (41) and the switch rule have been proved.

### 3.3 Canonical intermediate actions and `hpair`

To give the four abstract Lean binders a physical reading, fix one piece and write $G_i=\texttt{W.Gc}\ i=\texttt{locGen}$, $X_i=\texttt{W.Xc}\ i$, $D_i=\texttt{locData}$, $\widehat\beta_k=\texttt{(W.chain i).β}\ k$, $a_i=\texttt{(W.chain i).a}\ k$, $\mu_i=\texttt{(W.chain i).ν}\ k$, and $\phi_i=\texttt{(W.chain i).φ}\ u\ k$. A common-cover construction for P7 (2.14) would supply on **this same $G_i$** a reference datum $D_i^{\rm ref}$ and four small backgrounds $\phi_i^{\rm ref}(a_i,br_i)$, $\phi_i^{\rm ref}(ak,br_i)$, $\phi_i^{\rm ref}(ak,br_w)$, with $br_w$ the target mass convention. It must identify $D_i^{\rm ref}$ with $D_i$ on every action read, or charge their difference separately. For the clearest four-term split, first assume that read equality and set

$$
\begin{aligned}
P_i(u)&=\widehat\beta_k A_{X_i}(a_i,\mu_i;D_i,\phi_i^{\rm ref}(a_i,br_i)),\\
Q_i(u)&=\widehat\beta_k A_{X_i}(ak,\mu_i;D_i,\phi_i^{\rm ref}(ak,br_i)),\\
R_i(u)&=\widehat\beta_k A_{X_i}(ak,\mu_i;D_i,\phi_i^{\rm ref}(ak,br_w)).
\end{aligned}\tag{42}
$$

These are **proposed mathematical instantiations** of the already-bound Lean functions $P,Q,R$, not definitions present in `PieceWindowSetup`. If the transported reference datum differs on a block or crossing endpoint, the corresponding action change belongs in `hread`, and (42) must use a common intermediate datum chosen consistently.

At fixed $G_i,a_i,\mu_i,D_i$, put $w=\phi_i^{\rm ref}(a_i,br_i)-\phi_i$. Let $E_B,E_G,E_M$ be the three unprimed read energies of (37) for $\phi_i$, and $E'_B,E'_G,E'_M$ the three perturbation energies for $w$. Suppose the actual P7 local/window pair and its complex tube give, for six constants $F_B,F_G,F_M,F'_B,F'_G,F'_M\ge0$,

$$
\widehat\beta_k E_Z\le F_Z A_i,\qquad
\widehat\beta_k E'_Z\le F'_Z A_i\theta_i^2
\quad(Z=B,G,M),\qquad
\theta_i=K_R e^{-2\gamma_w a_j},\quad
a_j=2M[\widehat R_j]-M-2M_1\ge0. \tag{43}
$$

The fixed-coefficient version of the square expansion (36), with $b=e=0$, proves

$$
|T_{i,k}-P_i|
\le A_i\left[
\theta_i\sum_{Z=B,G,M}\sqrt{F_ZF'_Z}
+\frac{\theta_i^2}{2}\sum_{Z=B,G,M}F'_Z\right]. \tag{44}
$$

Indeed each cross term is bounded by
$\widehat\beta_k\sqrt{E_ZE'_Z}
\le\sqrt{F_ZF'_Z}A_i\theta_i$, and each square by
$\widehat\beta_kE'_Z/2\le F'_ZA_i\theta_i^2/2$.
Since $a_j\ge0$, $\theta_i^2\le K_R\theta_i$. If

$$
H_{\rm pair}:=\sup_{j\ge k_1}
\bigl\{\texttt{cs.beta}(j+1)\varepsilon_{j+1}^2
e^{-2\gamma_wa_j}\bigr\}<\infty, \tag{45}
$$

then the **exact `hpair` binder** follows with

$$
K_{\rm pair}
=H_{\rm pair}K_R
\left(\sum_Z\sqrt{F_ZF'_Z}
+\frac{K_R}{2}\sum_ZF'_Z\right). \tag{46}
$$

This tracks $d,L,N$ through the six read constants and $K_R$, and the history radii through $H_{\rm pair}$. Here is a bound for (45) with its own scale indices, rather than reusing (12), whose coupling index and exponent differ. Assume the Part 1 flow and radius schedule, $0\le\alpha$, $a,R_{\rm base},M,\gamma_w>0$, and write $e=d-2$, $x_j=\log(\beta_0a)+1+je\log L$, $[\widehat R_j]\ge R_{\rm base}x_j^2-1$. Then $\varepsilon_{j+1}\le3\alpha_0L^{-\alpha(j+1)}$, the reconstruction bound $cs.beta(j+1)\le a^{-1}e^{x_{j+1}-1+\eta}$, and $e-2\alpha=2\gamma$ give

$$\begin{aligned}
\operatorname{cs.beta}(j+1)\varepsilon_{j+1}^2
&\le9\alpha_0^2a^{-1}
 \exp\{x_j-1+\eta+2\gamma\log L-2\alpha j\log L\}\\
&\le9\alpha_0^2a^{-1}\exp\{x_j-1+\eta+2\gamma\log L\}.
\end{aligned}$$

Moreover $a_j\ge2MR_{\rm base}x_j^2-3M-2M_1$. Since
$x_j-4\gamma_wMR_{\rm base}x_j^2
\le(16\gamma_wMR_{\rm base})^{-1}$ by completing the square,

$$H_{\rm pair}\le
9\alpha_0^2a^{-1}
\exp\{\eta-1+2\gamma\log L
+2\gamma_w(3M+2M_1)
+(16\gamma_wMR_{\rm base})^{-1}\}. \tag{47}$$

This is the scalar absorption, **conditional on (43)**. If the radius schedule or $0\le\alpha$ is unavailable, retain the exact finite supremum (45) as an explicit premise.

The physical implication (43) is not landed. P6 p. 6 (2.13) and p. 7 (2.14)–(2.16) bound a specific supported datum change on its generating set. P7 p. 501 (2.14) invokes that bound for an inverse local/window replacement. `Balaban.Fluctuation.lemma41_domain_uncond` is a fixed-$G$, fixed-coefficient response under a named support, operator bound and two complex-domain hypotheses; `Balaban.Background.theorem73_complex` is a composition identity under a `Precedes` pair and complex domains. `Balaban.LargeField.exists_region_Xfine_window` proves the site cast and layer equality, but constructs neither the P7 datum pair nor the uniform read energies (43). P3 p. 56 (2.55)–(2.56) is a localization estimate for a decoupled background family under Proposition 2.1's hypotheses, not an unconditional assertion about this window pair. Its PDF text layer is garbled around the norms and constants, so no exact numerical constant from those displays is used here.

### 3.4 The coefficient residual `hcoef`

Keep the intermediate actions (42), and insert
$Q_i^0=\widehat\beta_k A_{X_i}(ak,\mu_i;D_i,\phi_i^{\rm ref}(a_i,br_i))$.
Then $P_i-Q_i=(P_i-Q_i^0)+(Q_i^0-Q_i)$; this is the required separation between the **coefficient read** and the **background response to that coefficient**. For the fixed field in $Q_i^0$, the kinetic and mass terms cancel exactly, so `Balaban.LargeField.ActionConv.PieceWindowSetup.coeff_target_mismatch` gives

$$
P_i-Q_i^0=\frac12\sum_{x\in X_i}
 L^{-2\ell_x}
 \{\widehat\beta_{j+1}\operatorname{cs.aw}(\ell_x)
       -\widehat\beta_k ak(\ell_x)\}
 r_x\cdot r_x . \tag{48}
$$

Here $r_x=D_i.\Psi_x-Q\phi_i^{\rm ref}(a_i,br_i)_x$. The identity uses the exact `pieceChain` invariant
$\widehat\beta_k a_i(\ell)=\widehat\beta_{j+1}\operatorname{cs.aw}(\ell)$.
Define the nonnegative absolute block reads

$$B_i=\frac12\sum_xL^{-2\ell_x}|\operatorname{cs.aw}(\ell_x)|\,|r_x|_2^2,\qquad
B_i^{\rm wt}=\frac12\sum_xL^{-2\ell_x}|ak(\ell_x)-\operatorname{cs.aw}(\ell_x)|\,|r_x|_2^2 .
\tag{49}$$

The complex bilinear inequality $|r_x\cdot r_x|\le|r_x|_2^2$, (48), and
$\widehat\beta_{j+1}cs.aw-\widehat\beta_kak
=(\widehat\beta_{j+1}-\widehat\beta_k)cs.aw
 +\widehat\beta_k(cs.aw-ak)$ give, term by term,

$$|P_i-Q_i^0|
\le|\widehat\beta_{j+1}-\widehat\beta_k|B_i
    +\widehat\beta_k B_i^{\rm wt}. \tag{50}$$

The fine-unit couplings are positive under the RG envelope. If the **originating block budget**
$\widehat\beta_{j+1}B_i\le C_B A_i$ and the **target weight budget**
$\widehat\beta_kB_i^{\rm wt}\le K_{\rm wt}m_i$ hold, the calculation (30)–(31), with the block read at the reference field, yields

$$|P_i-Q_i^0|\le
\left\{\frac{9C_BC_\xi\alpha_0^2e^{3\eta}q}{1-q}
      +K_{\rm wt}\right\}m_i,\qquad q=L^{-2\gamma}. \tag{51}$$

The first summand is zero when $k=j+1$. The bound is an exact application of the finite sum in `Balaban.LargeField.ActionConv.coeff_mismatch_sum_le` and the scalar flow estimate; it does **not** identify $ak$ with `cs.aw`. The second summand is essential when the common window coefficient differs from the originating coefficient. A simple way to express $K_{\rm wt}$ in terms of physical radii is to prove directly, for every layer read by the piece,
$|ak(\ell)-cs.aw(\ell)|\le\kappa_i|cs.aw(\ell)|$ and
$\sup_i\{\kappa_i(\widehat\beta_k/\widehat\beta_{j+1})
  cs.beta(j+1)\varepsilon_{j+1}^2\}<\infty$; then (49) gives
$K_{\rm wt}=C_B$ times this supremum. A uniform $\kappa_i$ alone is insufficient because the displayed source factor grows with the originating scale.

To pay $Q_i^0-Q_i$, put $w_i=\phi_i^{\rm ref}(ak,br_i)
-\phi_i^{\rm ref}(a_i,br_i)$ and form the six energies (37) at **fixed**
$ak,\mu_i,D_i$, with base field $\phi_i^{\rm ref}(a_i,br_i)$ and perturbation $w_i$.
Suppose nonnegative constants $G_Z,G'_Z$ and numbers $\sigma_i\ge0$ satisfy

$$\widehat\beta_k E_Z\le G_ZA_i,\qquad
  \widehat\beta_k E'_Z\le G'_ZA_i\sigma_i^2
  \quad(Z=B,G,M), \tag{52}$$

and put

$$H_{\rm resp}:=\sup_i
cs.beta(j_i+1)\varepsilon_{j_i+1}^2
\left\{\sigma_i\sum_Z\sqrt{G_ZG'_Z}
       +\frac{\sigma_i^2}{2}\sum_ZG'_Z\right\}<\infty. \tag{53}$$

At fixed coefficients the square expansion has one cross term and one half-square per $Z$. Cauchy and (52) give
$|Q_i^0-Q_i|
\le A_i[\sigma_i\sum_Z\sqrt{G_ZG'_Z}
+\sigma_i^2\sum_ZG'_Z/2]
\le H_{\rm resp}m_i$.
Together with (51), this proves the **exact `hcoef` binder** with

$$K_{\rm coef}=
\frac{9C_BC_\xi\alpha_0^2e^{3\eta}q}{1-q}
+K_{\rm wt}+H_{\rm resp}. \tag{54}$$

All factors in (54) are displayed; $C_B,G_Z,G'_Z$ depend on $d,L,N$ and the common chart/geometry bounds, while $K_{\rm wt},H_{\rm resp}$ are specified suprema over the history's layer radii and coefficient responses. Neither (49)'s physical budgets nor (52) is a landed history theorem. In particular `Balaban.Background.theorem72_linearResponse` varies $D$ at fixed $a,\mu$, and `Balaban.LargeField.ActionConv.massChange_region_bound` varies $\mu$ at fixed $a$; neither controls the variation $a_i\to ak$ of the actual background. P6 p. 14 (2.31) is the regional algebra for a coefficient change, with a cut source, but it does not identify this terminal common-window response. Therefore (54) is a proved **conditional** implication, not a discharge of `hcoef` for `pieceChain`.

### 3.5 The mass-convention residual `hswitch`

When the same branch and same mass parameter are used in $Q_i$ and $R_i$, uniqueness of the background on the *same* generating set and datum makes $Q_i=R_i$ and one may take $K_{\rm switch}=0$. This equality requires matching domains and normalization, not merely the label of a branch. It is the natural case if all later `pieceChain` backgrounds and the terminal action use one `br`. The exceptional first step still needs (41) or a separate source charge.

For a true massless-to-complete comparison at the switching scale $q_0=k_0+1$, let $\phi^0,\phi^m$ solve the two EL equations for the same $G_i,ak,D_i$ and collar; evaluate *both* actions with the physical mass $\mu=mL^{-2q_0}$. Let $Q_i=\widehat\beta_{q_0}A_{X_i}(ak,\mu;D_i,\phi^0)$ and $R_i=\widehat\beta_{q_0}A_{X_i}(ak,\mu;D_i,\phi^m)$, with
$\widehat\beta_{q_0}=\beta_{q_0}/L^{q_0(d-2)}$.
The theorem `Balaban.LargeField.ActionConv.massChange_region_bound_cubes` in `MassChangeCrossing.lean` applies if its **stated** IsEL, BgBounds, GreenSetting, OpSetting, spacing, smallness, common-domain, region-cardinality and cube-cover hypotheses all hold, with its cube count $n=m_i$. Its exact right side, writing
$K_m=\sqrt N\,K_w$ and $d=e+2$, is

$$|Q_i-R_i|
\le\left[
 (d+2)M^dL^2(K_mB_h)^2\beta_{q_0}m^2
 +2dM^{d-1}L^2K_mB_h\,\beta_{q_0}m\delta_0
\right]m_i. \tag{55}$$

If $0\le m,\delta_0\le1$ and the switch inequality
$\beta_{q_0}m\le C_{\rm sw}=e^{2\epsilon_{\rm sw}}L^d$ from `MASS-RESPONSE.md` Section 1 holds, then
$\beta_{q_0}m^2\le C_{\rm sw}$ and
$\beta_{q_0}m\delta_0\le C_{\rm sw}$, so the **exact `hswitch` binder** follows with

$$K_{\rm switch}=C_{\rm sw}
\{(d+2)M^dL^2(K_mB_h)^2
 +2dM^{d-1}L^2K_mB_h\}. \tag{56}$$

Here $\epsilon_{\rm sw}$ denotes the switch envelope in `MASS-RESPONSE.md`; identifying it with the flow envelope $\eta$ would require an additional premise.

One can retain $\delta_0$ in the second term for a sharper radius-dependent constant. The $2dM^{d-1}$ term counts crossing bonds with their half weights; deleting it would contradict the one-site boundary-flux example of `INTERFACE-A.md` Section 1. The theorem covers the switching scale $q_0$ under its hypotheses. It does not show that a comparison made at an arbitrary later terminal scale $k$ has $\beta_km_k\le C_{\rm sw}$, nor does it place the two actual window backgrounds on its common collar. If $Q_i,R_i$ use different generating sets, this mass theorem cannot be applied until the supported/read transport is proved. P6 p. 11, after (2.25), explicitly handles walls; P7 p. 501 (2.14) does not erase this switch charge.

### 3.6 The action-read residual `hread`

Let $A_i^{\rm loc}=\operatorname{actionRegionC}(X_i,ak,\mu_i,D_i,\phi_i^{\rm ref}(ak,br_w))$ and
$A_i^{\rm win}=\operatorname{actionRegionC}(W.Xw\,i,W.ak,W.\nu k,W.Datw\,u,W.\phi w\,u)$.
For (42), $R_i=\widehat\beta_k A_i^{\rm loc}$. The exact normalized difference is

$$R_i-\beta_k A_i^{\rm win}
=(\widehat\beta_k-\beta_k)A_i^{\rm loc}
 +\beta_k(A_i^{\rm loc}-A_i^{\rm win}). \tag{57}$$

Thus two explicit, nonnegative read budgets
$|\widehat\beta_k-\beta_k|\,|A_i^{\rm loc}|
\le K_{\beta{\rm read}}m_i$ and
$|\beta_k|\,|A_i^{\rm loc}-A_i^{\rm win}|
\le K_{\rm geomread}m_i$
prove the **exact `hread` binder** with
$K_{\rm read}=K_{\beta{\rm read}}+K_{\rm geomread}$ by the triangle inequality. This is also a usable corrected form when exact read equality fails.

There is a sharp zero-cost criterion. Choose the fine-unit target normalization
$W.\beta k=\widehat\beta_k=
\operatorname{betaCanon}(d,L,\operatorname{cs.beta}(k),k,0)$,
$W.ak=ak$, and $W.\nu k=\mu_i$ for each piece. Construct a transport from
$X_i$ on `locGen` to $W.Xw\,i$ on the window generating set that preserves
(a) all sites and their layer indices, (b) the block averaging sets and the values of $D.\Psi$ and $Q\phi$, (c) each positive-weight oriented internal/crossing bond, its weight $1$ or $1/2$, its endpoints, and the exterior values of $D$, and (d) the mass reads $\phi-D.h$ and the spacing factors. Then the three finite sums defining `actionRegionC` agree term by term; (57) is zero and $K_{\rm read}=0$. If any of (a)–(d) fails, the unmatched terms must be bounded as in Part 2 (28), including the crossing read. The target common mass $W.\nu k$ also has to match **every** $\mu_i$, or a separate mass-coefficient sum enters $K_{\rm geomread}$.

The landed `Balaban.LargeField.exists_region_Xfine_window` establishes the site cast and layer index, a portion of (a). `Balaban.LargeField.mainActionLoc_congr_window` compares one local action at two node configurations under its own read equalities; it does not transport `locData` or `actionRegionC` from `locGen` to `Wp.windowGenSet`. The setup theorem `Balaban.LargeField.sum_mainActionLoc_eq_gen` takes `ak, νk, βk, Datw, φw` as free arguments and supplies no (b)–(d). In particular, with a nonzero local action and a fixed nonempty piece, varying the free $\beta_k$ makes the left side of `hread` arbitrarily large while $m_i$ stays fixed. If the allowed zero-weight `StepDecomp` is used, $m_i=0$ and any nonzero mismatch violates `hread` even for a fixed target. Therefore the history objects alone imply no finite $K_{\rm read}$.

### 3.7 Exact discharge ledger and conclusion

| Requested Lean hypothesis | Sufficient physical statement and proved implication | Status for the landed actual history |
|---|---|---|
| `p7_first_of_rg_source.hsource` | Coherent first background (41), the same local datum and all bond reads, and six scaled origin/response budgets (38) imply the binder with (39) by (36)–(40). | The coefficient/mass regional response with P6's cut source and positive mixed-count cover is missing. |
| `PieceWindowSetup.window_uniform_of_parts.hpair` | A P7 local/window supported pair on one common cover with complex domains and six read budgets (43) implies (46), with radius bound (47). | The actual supported datum pair and its origin-energy read budget are missing. |
| `PieceWindowSetup.window_uniform_of_parts.hcoef` | Originating block budget, target-weight budget, and fixed-$ak$ coefficient-response budgets (52)–(53) imply (54). | The exact fixed-field mismatch is landed; the physical budgets and coefficient response are missing. |
| `PieceWindowSetup.window_uniform_of_parts.hswitch` | Exact same-branch equality gives zero; at the actual switch, the full premises of `Balaban.LargeField.ActionConv.massChange_region_bound_cubes` and $\beta_{q_0}m\le C_{\rm sw}$ give (56). | Regional mass algebra is landed conditionally; matching actual collar/domain, counting and placement of the switch in every piece are missing. |
| `PieceWindowSetup.window_uniform_of_parts.hread` | Full normalized read transport (a)–(d) gives zero; otherwise the two explicit budgets after (57) give their sum. | Only site/layer transport is landed; target normalization and block/bond/exterior reads are missing. |

Under the five displayed sufficient statements, `PieceWindowSetup.window_uniform_of_parts` gives
$K_{\rm win}=K_{\rm pair}+K_{\rm coef}+K_{\rm switch}+K_{\rm read}$.
Together with the flow hypotheses of Part 2, `window_conversion_pieces_of_rg_source` then yields the corrected finite bound

$$\|C(u)\|\le
\left\{\frac{81e^{3\eta}K_{\rm src}C_\xi\alpha_0^2}
                  {1-L^{-2\gamma}}
+K_{\rm pair}+K_{\rm coef}+K_{\rm switch}+K_{\rm read}\right\}
\sum_i m_i,\qquad u\in S. \tag{58}$$

This is a proof of the **conditional** implication to $|C|\le C_{15}\sum_i m_i$, with $C_{15}$ displayed. It is **not a proof of the requested five physical premises** for the actual RG history. The missing statements are mathematically substantive: the unrestricted zero-weight decomposition and target data prevent an unconditional derivation from the current theorem interface, while the necessary supported/cut-source/coefficient-response estimates are absent from the cited Lean background theorems. No honest finite constant depending only on $d,L,N$ and the radii can be assigned to all five premises without those physical restrictions. The original P7 exponentially decaying `window_decay` is stronger still: the coefficient and switch charges in (54), (56) are merely uniform.

**Paper provenance.** P7, *Communications in Mathematical Physics* **198** (1998), 493–534, journal pp. 500–501, (2.10)–(2.16), especially (2.11), (2.14); source file `sources/s002200050486.pdf`. P6, *Communications in Mathematical Physics* **198** (1998), 1–45, journal pp. 6–7, 11, 14, (2.13)–(2.16), (2.25), (2.31); `sources/s002200050470.pdf`. P3, *Communications in Mathematical Physics* **182** (1996), 33–82, journal p. 56, (2.55)–(2.56) and Proposition 2.1; `sources/BF02506385.pdf`. The P3 text extraction is damaged in these displays, so no unverified numerical transcription is used. The local interpretations and status are cross-checked against `notes/phase1/MASS-RESPONSE.md`, `INTERFACE-A.md` and `P631-INPUTS-2.md`; these notes themselves label the collar and regional source comparisons as open.

**Confidence.** High in the exact algebra (36), (48), (57), the finite Cauchy bounds and constant arithmetic (39), (47), (51), (54), (56), (58), conditional on their stated sign, flow and read hypotheses. High that the five actual-history physical premises are unproved by the landed declarations named here. Moderate that the proposed $P,Q,R$ in (42) is the most economical decomposition for a future proof; the actual supported pair may require additional intermediate actions and a correspondingly larger read charge.
