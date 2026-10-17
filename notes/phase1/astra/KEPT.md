# Kept outcomes: the window integral and its exact remaining hypotheses

**Verdict.** The requested action-only estimate for $\varkappa _2$ is false. The source and the landed theorem give $\mathcal G^\natural+\mathcal A_{\rm win}+C_{k_1,k}\ge\gamma _2$, whereas only $\varkappa _3$ gives $\mathcal A_{\rm win}+C_{k_1,k}\ge\gamma _3$. The former still yields the required $e^{-\gamma _2}$ after the composed Gaussian has been retained through node integration. The five window estimates below are valid under the explicitly named composition, support, cancellation, and denominator inputs. They are **not** five discharged instances of `KeptData.bound` in the present Lean tree.

## Sources, frozen inspection, and notation

I inspected read-only `/home/scott/Balaban` at commit `4c96d5af9a24b6b009e5f2f200cb43879c0eae3e` on 2026-10-17. SHA256: `LF4K-PLAN.md` `6a0d4bdae2344c6c4b8c21faff18e7692a1c15ccf7f9efcf596a39deeac913da`; `LF4R-PLAN.md` `0217ac12bd3129ecd7806db361b2e8033413073521f854e0fdaef70d88b45528`; `KeptOutcomeWindow.lean` `329274e713ee2264e23567bddeb0d2f5a58ec8498fb913221fa1dae5543953ab`; P7 PDF `c48e08dd439878a0245cceb6e6aead787a8ce7671865f6360c8464a7e579d2e9`. The other requested Lean files were inspected at that commit. The extracted text is in `P7.txt` here. P7's text layer loses superscripts, some set symbols, and much of the layout of (3.7) on journal p. 519; the identity below was checked against the legible (2.58) on pp. 510–511 and the reconstruction's explicitly marked (2.58′). No numerical constant is inferred from the damaged (3.7) extraction.

Primary source: Balaban, [*The Large Field Renormalization Operation for Classical $N$-Vector Models*](https://doi.org/10.1007/s002200050486), *Commun. Math. Phys.* **198** (1998), 493–534 (P7): composition (2.7)–(2.9), pp. 499–500; action conversion and violation (2.15)–(2.18), pp. 500–502; cancellation (2.53)–(2.60), pp. 509–512; normalized operator (3.5)–(3.10), pp. 518–520; second split (3.20), p. 525. The adapted, many-piece and nonideal formulation is `/home/scott/Balaban/notes/phase1/LF-RECONSTRUCTION.md`, Lemmas III.1.5–III.1.6, III.2.2–III.2.3, III.5.3, III.6.3–III.6.4, III.8.2 and III.8.7. I treat those adapted lemmas as **inputs**, not as consequences of P7 without their stated extra estimates. `LF4K-PLAN.md` status W952 and `LF4R-PLAN.md` §9 status W961 identify the still open history-to-window composition.

Fix one ripe component and its window. Put $A=\mathcal A_{\rm win}=\sum_{j=k_1}^{k-1}\mathcal A_{j+1}(X_j)$, $G=\mathcal G^\natural\ge0$, and $C=C_{k_1,k}$. The conversion (2.15′) means **exactly** $A=\beta_k A_k^*(X_{\rm win};\psi,\phi_{k_1,k})-C$, with $|C|\le C_{15}\sum_j|X_j|_{j+1}$; $C$ is the conversion error and cannot be set to zero. For the top blocks $z\subset Z_0^c\cap\Omega_k^c$, write

$$g_z(v)=\left(\frac{\beta_k a_z^\natural}{2\pi}\right)^{N/2}\exp\left(-\frac{\beta_k a_z^\natural}{2}|v|^2\right),\qquad G=\sum_z\frac{\beta_k a_z^\natural}{2}|\psi_k(z)-Q_z^\natural\psi^G|^2,\qquad c_\natural=\prod_z\left(\frac{\beta_k a_z^\natural}{2\pi}\right)^{N/2}.$$

Thus integration of Gaussian-only nodes $\mathcal J$ gives $c_\natural e^{-G}$ *exactly*, at fixed leaves and top fields (reconstruction III.1.6, P7 (2.7)–(2.9)). The action and indicators must be independent of those nodes (reconstruction III.1.5; landed `mainActionLoc_congr_nodes`, `Atot_congr`); otherwise this factorization is unavailable. On $Z_0$, integrate the composed probability density by (2.8), obtaining $1$ per block before any change to the leaves. The leaves are then translated by $\psi''=\tilde\psi-\psi^0_{k_1,k}(\psi_k)$ for fixed $\psi_k$, with Jacobian one. This order matters for (2.58′).

The five exponents, with the conventions of landed `SmallFactorPar.gamma` in `SmallFactorConsts.lean`, are

$$\begin{aligned}
\gamma _1&=\frac98(1-\eta)\frac{\gamma _0A_0^2\lambda_k^{2p_0}}a-\frac12,&
\gamma _2&=\frac{1-\eta}{144K_1^2}\frac{\gamma _0A_0^2\lambda_k^{2p_0}}a-1,\\
\gamma _3&=\frac{e^{-2\epsilon}\gamma _0A_0^2\lambda_{k_1}^{2p_0}}{72aK_1^2\widehat W_k^2},&
\gamma _4&=\frac{e^{-2\epsilon}\gamma _0A_1^2\lambda_{k_1}^{2p_0}}{2a\widehat W_k^2}-1,\\
\gamma _5&=\frac{\gamma _0A_0^2\lambda_k^{2p_0}}{72K_1^2a}.
\end{aligned}$$

These are the adapted Lemma III.5.3 constants, not numerical claims made verbatim in P7. `Outcome.kappa1` through `Outcome.kappa5` are `Outcome.kept 0` through `Outcome.kept 4`; `Outcome.weight` gives respectively $1-t$, $t(1-s)$, $ts(1-z)$, $tsz(1-w)$, $tszw(1-u)$. The first four are `outcomeKernel Kpre ...` with the old boundary factor; the fifth is the normalized operator multiplied by the reference density and $1-u$ (Definition III.8.8). In particular it is not `outcomeKernel Kpre ... (Outcome.kept 4)` after normalization.

## The obstruction for $\varkappa _2$

The requested implication $t=1$, $s=0$ $\Longrightarrow A\ge\gamma _2-C$ omits $G$. In P7 the bad $\chi_k(\square)$ is tested on a scale-$k$ field in $Z_0^c\cap\Omega_k^c$, while the window action reads the leaves and the field on $\Omega_k$, not that top field; P7 (2.17), pp. 501–502, explicitly uses the *sum* of Gaussian and action. One can keep every window leaf, its unit background, and the field on $\Omega_k$ at the constant unit vector $e_1$, and vary a top block in a cube tested by $\chi_S$ from $e_1$ to $(1+2\delta_k)e_1$ (with $0<\delta_k<1/4$). The $3\delta_k$ tube $\tilde\chi_k$ still admits this radius change, while the local $\delta_k$ regularity test fails: its unit background cannot make a block deviation of $2\delta_k$ less than $\delta_k$ (Definitions II.3.1–II.3.2, landed `Reg`, `chiK`, `chiS`). Choose the changed cube away from $Z_0$ and $\Omega_k$, as permitted by the support set of `chiS`. The unchanged leaves have zero gradient and block costs, and with $h=e_1$ their mass cost is zero. Consequently $A=0$; the variation costs $G>0$. At the constant reference configuration also $C=0$ by (2.15′). For large $\beta_k\delta_k^2$, $\gamma _2>0$, so the asserted action-only lower bound cannot be uniform. The elementary one-block reduction makes the logical failure transparent: $A=C=0$, $G=\gamma _2$, $t=1$, $s=0$ obeys the actual lower bound and violates $A+C\ge\gamma _2$. No bound on $A$ alone follows from Lemma III.5.3 (b).

The nearest true and sufficient estimate is

$$\boxed{\quad\mathbf1_{\varkappa _2}(G+A+C-\gamma _2)\ge0,\qquad \mathbf1_{\varkappa _2}c_\natural e^{-G-A}\le\mathbf1_{\varkappa _2}c_\natural e^{C-\gamma _2}.\quad} \tag{K2}$$

Here $\mathbf1_{\varkappa_i}$ denotes the actual product of indicators. The first inequality is Lemma III.5.3 (b): failure of $\chi_S$ gives a violation of the smaller $\delta_k/(6K_1)$ tube on $Z_0^c\cap Z$ (landed `smallFactor_two_ripe`, whose conclusion is `gamma2 ≤ composedGauss + multiAction`), the single-scale LF-1 cost is at least $\gamma_0\beta_k\delta_k^2/(72K_1^2)$, and (2.17′) leaves $\frac12(1-\eta)$ of it and loses $1$. Substituting $\beta_k\delta_k^2=A_0^2\lambda_k^{2p_0}/a$ gives precisely $\gamma _2$ above. Use $A+C=\beta_kA_k^*(X_{\rm win})$ and monotonicity from $Z_0^c\cap Z$ to $X_{\rm win}$. Exponentiating the first inequality proves the second; it also shows why a node integral must be performed *before* discarding $G$.

## Direct window bounds for $\varkappa _1,\varkappa _2,\varkappa _3$

For $\varkappa _1$, $t=0$ means the top field lies **off** the $\tilde\chi_k$ window set. Lemma III.5.3 (a) (landed `smallFactor_one_ripe`, `smallFactor_one_gamma1`) and (2.15′)/(2.17′) give $\tfrac12G+A+C\ge\gamma _1$ on its support. Therefore, with the zero-weight case included,

$$\mathbf1_{\varkappa _1}c_\natural e^{-G-A}\le e^{C-\gamma _1}\,c_\natural e^{-G/2},\qquad \int_{\mathbb R^N}\left(\frac{b}{2\pi}\right)^{N/2}e^{-b|v-m|^2/4}\,d^Nv=2^{N/2}\quad(b>0). \tag{K1}$$

The integral is independent of the leaf-dependent center $m$ and gives $2^{(N/2)n_T}$ for $n_T$ top blocks, i.e. exactly $(N/2)\log2\,n_T$ in the loss. The top variables on $Z_0^c\cap\Omega_k^c$ must be included among the variables integrated in `hid` (or an equivalent Gaussian weighted measure must be proved); placing them in the Lebesgue window factor `Wd` and taking `E` to contain the off-window support makes `μW(E)` infinite in general, so `hvol` cannot hold. After moving those variables into `Jv`, `E` is a measurable set of the *remaining* window variables containing the projection of the kernel support; it need not express $t=0$. The removed-lane `E` cannot simply be reused. The $Z_0$ Gaussian integrates to $1$ by (2.8).

For $\varkappa _2$, (K2) gives $c_\natural e^{-G-A}\le c_\natural e^{C-\gamma _2}$. For $\varkappa _3$, Lemma III.5.3 (c) and (2.15′) give $A+C\ge\gamma _3$, hence

$$\boxed{\quad\mathbf1_{\varkappa _3}c_\natural e^{-G-A}\le\mathbf1_{\varkappa _3}c_\natural e^{C-\gamma _3}\quad} \tag{K3}$$

because $G\ge0$. The proof of III.5.3 (c) has two parts: a failed $\chi^0$ at scale $k_1$ directly costs at least $e^{-2\epsilon}\gamma_0\beta_{k_1}(\delta_{k_1}/(3K_1))^2/18$, or a boundary disagreement forces a violating edge along the chain and costs at least $e^{-2\epsilon}\gamma_0\beta_{k_1}\delta_{k_1}^2/(72K_1^2\widehat W_k^2)=\gamma _3$; the direct cost is larger when $\widehat W_k\ge2$ (reconstruction III.5.3 (c), P7 (2.21)–(2.30), pp. 502–505). A history-level `smallFactor_three_ripe` was not found; this geometric bridge is still a hypothesis for the window instance.

For (K2) and (K3), $t=1$ confines the remaining top coordinates to the $3\delta_k$ tube. Integrate them along a spanning tree rooted in $\Omega_k\cap Z$: each new block lies in a radius-$3\delta_k$ ball about its parent. With $a_z^\natural\le2$ and $\delta_k=A_0\lambda_k^{p_0}/\sqrt{\beta_ka}$, a block has the explicit upper bound

$$\left(\frac{\beta_ka_z^\natural}{2\pi}\right)^{N/2}v_N(3\delta_k)^N\le v_N3^NA_0^Na^{-N/2}\pi^{-N/2}\lambda_k^{Np_0}=\exp\{Np_0\log\lambda_k+C_{\rm shell}\},\quad C_{\rm shell}:=\log(v_N3^NA_0^Na^{-N/2}\pi^{-N/2}). \tag{V}$$

For the $Z_0$ cutoff of $\varkappa _5$, a radius-$C_6\beta_k^{-1/2}p_0(\beta_k)$ ball per block has volume $v_NC_6^N\beta_k^{-N/2}p_0(\beta_k)^N$. Thus its product with the $e^{\ell_0}=\beta_k^{(N/2)n_{Z_0}}$ factor is at most $\exp\{[Np_0\log\lambda_k+C_{Z_0}]n_{Z_0}\}$ when $p_0(\beta_k)=A_0\lambda_k^{p_0}$, where $C_{Z_0}=\log(v_NC_6^NA_0^N)$. The source's $C_{\rm vol}$ may be enlarged to dominate $C_{\rm shell}$ and $C_{Z_0}$. The other original window shells have volume at most $1$ under the stated size assumptions. For $\varkappa _4$ there is no $\chi''$ ball restriction: use those original shell variables, whose volume is unchanged by the leaf translation. For $\varkappa _5$, $\chi''=1$ supplies the $\psi''$ balls, also of volume at most $1$. Formula (V) is a volume estimate; it does not replace the $e^{-\gamma_i}$ established pointwise above. Its constant depends on $N,a,A_0$ and the fixed shell convention, and is uniform in the scale, component, torus volume, $h$, and $g$.

## Cancellation and the two remaining outcomes

The arithmetic of (2.58′) is best written without suppressing the normalization. Put $A_w:=\beta_k A_k^*(X_{\rm win})=A+C$, $A_Z:=\beta_k A_k^*(Z;\psi_k^0,\phi_k^0)$, $A_0:=\beta_k A^*_{0,k}(Z_{k_1};\phi_k^0)$, $B:=\beta_k\{\cdots\}$, $S:=\beta_kS_{\rm st}$, $C^\natural=C_0^\natural+C_1^\natural$, $c=\mathrm{const}$ (ideal), and $c_\natural=\mathrm{const}^\natural$. Then (2.58′) says

$$G+A_w-\log c_\natural=A_Z-A_0+B+S-\log c+C_0^\natural+C_1^\natural,$$

and therefore, by ordinary algebra,

$$c_\natural e^{-G-A}=c\,e^{C-A_Z+A_0-(B+C_1^\natural)-S-C_0^\natural}. \tag{C}$$

This identity is pointwise in the translated leaves. It is the correct place to use `cancellation_identity`, `removedFactor_le_of_identity`, and `removedFactor_le_restricted`; a bound on the Gaussian-only node integral by its supremum loses the cancellation.

For $\varkappa _4$, $w=0$ detects a fluctuation edge. The chain in Lemma III.5.3 (d) gives the LF-1 cost $\gamma _4+1$ in $B$; the other terms lose at most $1$. More precisely, split $B=Q+D_{
m good}+D_{
m err}$ with $Q=\frac12\sum_z\beta_ka_z^\natural|Q_z\delta\psi|^2\ge0$, $D_{
m good}\ge\gamma _4+1$ on $w=0$ before the stated unit error, $D_{
m err}\ge-1$, and $|C_1^\natural|\le\frac34Q$ (equivalently the reconstruction's $\frac38\sum\beta a|Q\delta\psi|^2$). Thus $Q+C_1^\natural\ge Q/4\ge0$ and $B+C_1^\natural\ge\gamma _4$. This is the needed **strengthening with $C_1^\natural$ retained**; merely citing $B\ge\gamma _4$ and separately dropping $C_1^\natural$ would be invalid. Lemma III.6.4 gives $|A_0|<1/4$ and $|S|<1/4$, and the real main action is nonnegative. From (C), on the $\varkappa _4$ support,

$$\boxed{\quad c_\natural e^{-G-A}\mathbf1_{\varkappa _4}\le c\,e^{C+1/2+|C_0^\natural|-\gamma _4}\mathbf1_{\varkappa _4}\le c\,e^{C+4+|C_0^\natural|-\gamma _4}\mathbf1_{\varkappa _4}.\quad} \tag{K4}$$

The $4=1+3$ in the second bound is the conservative constant in landed `removedFactor_le_of_identity` and in the window consumer; it is larger than the displayed real arithmetic loss. There is **no denominator and no reference density** for $\varkappa _4$. Its $Z_0$ Gaussian was integrated by (2.8), and the remaining variables have the tube/ball volumes used in (V).

For $\varkappa _5$, let the reference be $\rho_Z(u)=\chi_{Z_0}(u)e^{-A_{\rm ref}(u)}$, with $u=\psi_k\restriction_{Z_0}$, $A_{\rm ref}(u)$ the full action at the field obtained by inserting $u$, $A_{\rm ref}(\psi_k^0)=A_Z$, and $D_Z=\int\rho_Z(u)\,du>0$. The denominator formula is $D_Z=e^{-A_Z-\ell_0+\widetilde E_0}$ with $\ell_0=(N/2)\log\beta_k\,n_{Z_0}$ and $|\widetilde E_0|\le C_{\widetilde E}D_0^d$; the action in this formula must be the **same restricted action** $A_Z$ as in (C). If instead it is an action $A_{\rm den}$, every following exponent contains $A_{\rm den}-A_Z$. Divide (C) by $D_Z$, then multiply by the retained numerator $\rho_Z(u)$:

$$\frac{\rho_Z(u)c_\natural e^{-G-A}}{D_Z}=c\,\rho_Z(u)\,e^{\ell_0-\widetilde E_0+C+A_0-(B+C_1^\natural)-S-C_0^\natural}. \tag{R}$$

On $u=0$ in the notation of `Outcome.weight` (that is, $\chi_{Z''}=0$), Lemma III.5.3 (e), landed `smallFactor_five_ripe`, gives $A_{\rm ref}(u)\ge\gamma _5$ on the actual support, hence $0\le\rho_Z(u)\le e^{-\gamma _5}$. Lemma III.6.4 and the $Q+C_1^\natural\ge0$ argument give $B+C_1^\natural\ge-1$; together with $|A_0|,|S|<1/4$, (R) yields the safe landed constant

$$\boxed{\quad\mathbf1_{\varkappa _5}\frac{\rho_Z(u)c_\natural e^{-G-A}}{D_Z}\le\mathbf1_{\varkappa _5}c\,\exp\{\ell_0-\widetilde E_0+C+4+|C_0^\natural|-\gamma _5\}.\quad} \tag{K5}$$

The factor $\rho_Z$ stays in the numerator until after (R); removing it when cancelling $e^{-A_Z}$ loses the only source of $\gamma _5$. If the actual denominator is the massless `rhoZero` while $\nu>0$ remains in (C), (R) acquires the action mismatch. The landed `rhoZeroRestricted`/`removedFactor_le_restricted` handles a restricted action, but `removed_quotient_le_of_history` currently assumes `hν0 : ν = 0`. Moreover `smallFactor_two_ripe` and `smallFactor_five_ripe` assume `cs.mu k = 0` in the bridge from the actual `chiK` to a violation; their LF-1 conclusions allow a nonnegative mass, but the bridge is not yet the positive-mass one. Landed `rhoZeroPhysical` and `denominatorPhysical_bounds` provide a positive-mass comparison, with a crude error $2E|\Omega_1|$; that error must be proved absorbable in the residual budget or a restricted physical denominator must be connected to (C). No unconditional $\nu>0$ instance of (K2) or (K5) is claimed here. Finally, the resulting second-kind $\varkappa _5$ kernel must be in the original variables and have $I''=I\setminus\mathcal J$; `Outcome.weight` alone does not construct it.

## The exact Lean consumer inequality and constant budget

Let $F_i$ be `T.absW` for the actual kernel of outcome $i$ after `Θ.symm`, and let $W,C_r,J$ be the factors of a measure-preserving regrouping $\Theta$ (`Wd`, `Cr`, `Jv` in `keptKernel_kerBound_of_window`). Its three decisive hypotheses, stated without hiding the gain, are

$$\begin{aligned}
&\texttt{hid}_i:\quad\int_J F_i(\Theta^{-1}(w,c,j))\,d\mu_J(j)\le\operatorname{Core}(w,c)\,e^{\mathrm{bw}(w,c)}e^{L_c}\operatorname{frac}_i(w,c),\\
&\texttt{hsupp}_i:\quad w\notin E_i\ \Longrightarrow\ \int_J F_i(\Theta^{-1}(w,c,j))\,d\mu_J(j)=0,\\
&\texttt{hfrac}_i:\quad w\in E_i\ \Longrightarrow\ 0\le\operatorname{frac}_i(w,c)\le e^{F_{r,i}},\qquad F_{r,i}+\gamma_i\le F_z+C_{\widetilde E}D_0^d+C_\natural\lambda_k^{2d+1}+4+C_k. \tag{H}
\end{aligned}$$

These are ENNReal `lintegral` inequalities with `ENNReal.ofReal` in Lean. The gain must appear as $F_{r,i}\le\text{common losses}-\gamma_i$ in `hfrac`, or equivalently in `hid` with `frac` multiplied by $e^{-\gamma_i}`; setting `frac=1` after dropping the action does not meet (H). For $i=1$, take `Jv` to include the Gaussian-only nodes, $\psi_k\restriction_{Z_0}$ and the unconstrained top blocks, and include $2^{(N/2)n_T}$ in `frac_1` before proving (H). For $i=2,3,4$, `Jv` includes the Gaussian-only nodes and $Z_0$, while the top blocks belong to a finite-volume window set because $t=1$. For $i=5$, use the regrouping of the translated (3.7) kernel and the cutoff of $\rho_Z$.

Here is an exact way to place the large prefactors in the consumer. Write $q=(N/2)\log2$ and let $U_i$ be the other pointwise exponent losses ($C$ and, for $i=4,5$, $4+|C_0^\natural|$, $-\widetilde E_0$ for $i=5$), bounded by $U_i\le C_{\widetilde E}D_0^d+C_\natural\lambda_k^{2d+1}+4+C_k$ after the window-proportional part of $C$ is charged to $B_w$ or $C_k$. For $i=1$, take $F_z=qn_T$, $F_{r,1}=U_1+qn_T-\gamma_1$; then the `hvol` goal is $e^{L_c+qn_T}\mu_W(E_1)\le e^{c_k(n_{Z_0}+n_T)}$. It follows from a residual-volume bound $e^{L_c}\mu_W(E_1)\le e^{c_k^0(n_{Z_0}+n_T)}$ by taking $C_{\rm vol}\ge C_{\rm vol}^0+q$. For $i=2,3,4$, put $F_z=\log c_\natural$ for $i=2,3$ and $F_z=\log c$ for $i=4$, and set $F_{r,i}=U_i+F_z-\gamma_i$. Then `hvol` is exactly the shell estimate $e^{L_c}c_\natural\mu_W(E_i)\le e^{c_k(n_{Z_0}+n_T)}$ or its ideal-$c$ version, using (V). For $i=5$, put $F_z=\log c+\ell_0$, $F_{r,5}=U_5+F_z-\gamma_5$; `hvol` then includes the $Z_0$ cutoff ball with its $\beta_k^{N/2}$ prefactor. These choices make $F_{r,i}+\gamma_i-F_z=U_i$ **exactly**, and show how (H) can be proved without taking an unaffordable separate supremum of the Gaussian normalization. They are an assignment of proof obligations, not a claim that the corresponding `Θ`, `E`, and shell-volume instances already exist.

For completeness, here is the consumer's entire exponent arithmetic. Put $c_k=Np_0\log\lambda_k+C_{\rm vol}\ge0$, $Q_k=(M\operatorname{crit}_k)^d$, and assume `hbw` $\mathrm{bw}\le B_w$, `hcore` $\int\operatorname{Core}\le e^{-\kappa_{\rm core}}$, `hvol` $e^{L_c+F_z}\mu_W(E_i)\le e^{c_k(n_{Z_0}+n_T)}$, $n_T\le Q_k$, $n_{Z_0}\le D_0^d$, and `hκ` $\kappa_{\rm pre}\le\kappa_{\rm core}-(B_w+C_k)$. Fubini, `hid`, `hsupp`, `hbw`, `hfrac`, `hcore`, and `hvol` give, with $E_Z=0$ for kept outcomes,

$$\int F_i\le\exp\{B_w+L_c+F_{r,i}+c_k(n_{Z_0}+n_T)-(L_c+F_z)-\kappa_{\rm core}\}=\exp\{B_w+F_{r,i}-F_z+c_k(n_{Z_0}+n_T)-\kappa_{\rm core}\}.$$

Using (H), $\kappa_{\rm pre}\le\kappa_{\rm core}-B_w-C_k$, $n_T\le Q_k$, and $n_{Z_0}\le D_0^d$, the logarithm is at most

$$-\kappa_{\rm pre}-\gamma_i+C_{\widetilde E}D_0^d+C_\natural\lambda_k^{2d+1}+4+c_k(Q_k+D_0^d). \tag{L}$$

The exact landed `hCR` premise is

$$\left(\frac N2\log2+Np_0+|C_{\rm vol}|+2C'_E\right)M^d(2c_0R_b+2c_0+10)^d+D_0^d(Np_0+|C_{\rm vol}|+|C_{\widetilde E}|)+C_\natural+10\le C_R,$$

with $C'_E\ge0$, $D_0\ge0$, $C_{\rm vol}\ge0$, $\lambda_k\ge1$, plus `S.Ok` and the geometric bound on $\operatorname{crit}_k$. It is deliberately generous: $(N/2)\log2\,Q_k$ pays the half-Gaussian in (K1), $Np_0+|C_{\rm vol}|$ pays (V), $C_{\widetilde E}D_0^d$ and $C_\natural\lambda_k^{2d+1}$ pay (K5), and $10$ pays the fixed $4$ and margins. Under this `hCR`, landed `lres_at_scale`/`removed_exponent_le` bound (L) by $-\kappa_{\rm pre}+C_R\lambda_k^{2d+1}-\gamma_i$. `window_lintegral_le_exp` then yields `KerBound a k T (κpre - S.CR * S.lam k ^ (2*S.d+1) + γ)`; `keptKernel_kerBound_of_window` is exactly this result with `outcomeKernel` for its `hTK`. The constants in `hCR` are **hypotheses** of the landed consumer, not constants established merely by (K1)–(K5). A separate `hvol` proof for $\varkappa _1$ must place its $2^{N/2}$ cost consistently between $F_z$, $F_{r,1}$ and the enlarged $C_{\rm vol}$; the generic consumer cannot integrate an unbounded Lebesgue factor by `hfrac` alone.

`KeptData.bound` in `Operators/StepData.lean` demands, for each admissible history and ripe component, both vanishing off `ChiDomAt` and `KerBound` at exponent $\kappa_k-C_R\widehat\lambda_k^{2d+1}+\gamma_i$. The wrappers `keptKernel_one_kerBound`, `keptKernel_two_kerBound`, `keptKernel_three_kerBound` merely specialize the label of `keptKernel_kerBound_of_window`; their `hid`, `hsupp`, `hfrac`, `hvol`, and kernel equality are still parameters. No corresponding first-kind wrapper for $\varkappa _4$ or constructed normalized $\varkappa _5$ datum was found in `KeptOutcome*.lean`. Landed `smallFactor_ge_setting`, `cDec`, and `sum_inv_cDec` handle the label arithmetic once the actual kernels are built. The action conversion for a history still needs the `LF4R-PLAN.md` §9 `WindowSetup`/piece-chain hypotheses and its node-independence bridge; the $\varkappa _3,\varkappa _4$ history geometry and the positive-mass denominator bridge also remain. Thus (H), supplied outcome by outcome with (K1)–(K5), is the precise interface that unblocks the window part of `KeptData.bound`; it does not by itself settle the support, covariance, and data-construction fields of `KeptData`.

**Confidence.** High for the false $\varkappa _2$ action-only implication, the Gaussian factors, the cancellation algebra, and the consumer exponent arithmetic; conditional for a complete history instance of all five outcomes. The latter depends on the named unproved bridges above and on resolving the denominator at $0<\nu\le1$. No Lean file was edited or compiled for this note.
