# The inherited collar in the reconstructed window

## Result

For our reconstruction, the physical datum of the P7 window should be the trace of the parent multiscale field already read by the product of P5 (2.47) and P6 (3.2). This is a legitimate definition at the construction of the step kernel: all its original block terms and boundary bonds continue to read the same spins. On the actual localized geometry, the outer collar agrees exactly with the later composed reference; the inner collar can be compared through the retained $k_1$ regularity band and the window chain. The comparison requires a one-site extension of LF-RECONSTRUCTION Lemma III.4.6 and an explicit parent-refinement theorem. Neither assertion is a field of the landed `WindowPieces.Hyp`, so the response theorem below states them as named hypotheses until they are proved for the actual minimal generating sets.

The mass-switch wall is chargeable to the new step region. Its bound needs the *scaled* background gradient; the uniform real bound $|\partial\phi|<3$ in `WALL-COLLAR.md` does not give a scale-independent cost per new cube. The fine-lattice wall count and the $L^{-k}$ gradient combine with $\beta^{(k+1)}_0$ to give the explicit factor $2dM^{d-1}L^2$. The resulting cost belongs in the (S2) new-volume coefficient of Definition II.5.11 and is propagated by LF-2 from (D6). The complete scheme-A operator comparison still requires its separate inherited-term, cutoff, normalization and mass-response estimates.

## 1. Physical datum: a definition preserving the density

Let $B=W.\mathrm{full}$ and $G=W.\mathrm{windowGenSet}(h_W)$ in `LargeField/R/WindowGenGlue.lean`. For the history's `BlockV` spin field $\psi$, set

$$\Psi^{\rm in}(x)=\psi(p_B(x)),\qquad p_B(x)=\begin{cases}
\mathrm{blockOf}(B.\mathrm{layerIndex}(x),x),&x\in\Omega_1(B),\\
\langle0,x\rangle,&x\notin\Omega_1(B).
\end{cases}\tag{1.1}$$

This is `DeltaPsiDef.psiTilde B ψ`, with the **parent** generating set as its argument. Thus a parent layer-$p$ site reads the existing spin $\psi_p(b_p(x))$; a surviving parent layer-zero site reads the existing fine spin $\psi_0(x)$. Define the reconstructed physical datum by `BgData.clip G` of (1.1), with constant $h$, on $\mathrm{dataSites}(G)=\Omega_1(G)\cup C_G$. In particular its Dirichlet collar is

$$D^{\rm ph}.\Psi(c)=\begin{cases}\psi_{n_B(c)}(b_{n_B(c)}(c)),&c\in C_G\cap\Omega_1(B),\\
\psi_0(c),&c\in C_G\setminus\Omega_1(B).
\end{cases}\tag{1.2}$$

The definition needs `ParentRefines W`: each block of $G$ on which (1.1) is read lies in one parent block or in the parent's layer-zero part. For the actual pieces, the core support is in the parent's $k_1$ layer by the margin argument in §2; on $Z\setminus Z_{k_1}$ the two generating sets are the same; and the boundary piece outside $Z$ is in the parent's $k$ layer. Since child blocks in these regions have layers at most $k_1$, their common layer, and $k$, respectively, block nesting makes (1.1) constant on each child block. The restricted pieces have disjoint regions, while `WindowPieces.Hyp.blockUnion` prevents a glued block from straddling their boundary. `blockLift_eq_of_le` in `LargeField/Background/Lift.lean` then proves `IsLayerConstant G Ψin`, so `BgData.clip` is typed. At a common block the parent value is copied; at a newly generated child block the conditional average of a constant parent-block field has the same value. This argument must be checked for the **actual** minimal pieces: `WindowPieces.Hyp` alone proves block unions and separation but has no parent-layer clause. If that check fails for a proposed window, (1.1) is not its datum; its $Q^*$ coefficients must be used explicitly.

This choice preserves the density at the **step-kernel definition**, not by changing a solved background later. LF-RECONSTRUCTION (III.1.3) is the product of the original step factors; Definition II.5.4 says each action reads the history's multiscale field on $X_j^{+1}$ and on the background data sites. P5 p. 513, after (2.49), says exterior $\psi_k$ dependence is unchanged; P7 p. 500, after (2.10), says the spin variables are not renormalized. Restricting (1.1) to the data sites of each original factor leaves every action argument, boundary bond and Gaussian parameter unchanged. The algebraic `physical_window_action_reads_inherited` lemma should state that equality factor by factor before P7 (2.10)–(2.16) is invoked. This is the permitted reconstruction choice of the off-window $Q^*$ lift; it does not assert that P7 printed an off-window site formula.

The later reference field is different in its definition. For $G'=\mathbb B_k(U_k)$, P7 p. 508 (2.40) and `Background/Composition.lean:composeField_of_collar` give

$$D^0.\Psi(c)=\bar\phi_k^0(c)=\begin{cases}\phi_k^0(c),&c\in\Omega_1(G'),\\
\widetilde\psi_k^0(b_k(c)),&c\notin\Omega_1(G').\end{cases}\tag{1.3}$$

The two minimizers in the **mass-only** comparison both use $D^{\rm ph}$, so their collar is common by definition. P7's physical/reference comparison uses (1.2) and (1.3), and needs the next estimate.

## 2. The two collar faces and their support

Put $C_{\rm in}=C_G\cap Z_{k_1}$ and $C_{\rm out}=C_G\setminus Z_{k_1}$; the nonempty-core case has $k_1\ge1$, since $Z_0=\varnothing$ in LFR §I.2. The actual localized history has the inclusions of LF-RECONSTRUCTION Lemma III.1.2(f): $\Omega_1(B)^c\subset\Omega_{k_1}(B)^c\subset Z_{k_1}$ and $\Omega_k(B)^c\subset Z$. The boundary piece of P7 (2.13) is $G'$ restricted to $W.\mathrm{Unb}\setminus Z$, with $\Omega_1(G')\subset W.\mathrm{Unb}$. These are the required set hypotheses; generic `WindowPieces.Hyp` does not state them.

**Outer face.** If $c\in C_{\rm out}\cap(Z\setminus Z_{k_1})$, then the first inclusion puts it in $\Omega_1(B)$ and the full piece puts it in $G.\Omega_1$, contrary to $c\in C_G$. Hence $c\notin Z$. If $c\in W.\mathrm{Unb}\setminus Z$ and $c\in\Omega_1(G')$, the boundary piece gives the same contradiction. Outside $W.\mathrm{Unb}$, the support inclusion excludes $c\in\Omega_1(G')$. Therefore $c\notin\Omega_1(G')$. Since $\Omega_k(B)^c\subset Z$, (1.2) reads $\psi_k(b_k(c))$. P7 (2.44), as used in LFR Lemma III.3.3, says $\widetilde\psi_k^0=\psi_k$ off $Z_0\subset Z$. The second branch of (1.3) proves the exact identity

$$D^{\rm ph}.\Psi(c)=D^0.\Psi(c),\qquad c\in C_{\rm out}.\tag{2.1}$$

This removes the possible source at the outer boundary near $\operatorname{st}(Z)$.

**Inner face.** The core piece $\mathbb B_{k_1}(W)$ reaches at most $2[\widehat R_{k_1-1}]+3$ scale-$k_1$ cubes into $Z_{k_1}$; $\Omega_{k_1}^c$ starts at least $2[\widehat R_{k_1-1}]+6$ cubes in (LFR Lemma III.4.6, using I.3.5(d),(e)). An adjacent collar site extends the first reach by at most one block, so $c\in\Omega_{k_1}(B)$. Since $Z_{k_1}\subset\Omega_{k_1+1}(B)^c$ (III.1.2(f)), its parent layer is exactly $k_1$ and (1.2) reads $\psi_{k_1}(b_{k_1}(c))$. The reference reads $\phi_k^0(c)$ on this core neighbourhood inside $G'$.

The necessary **one-site support lemma** is inner_collar_in_regular_T: every $c\in C_{\rm in}$ has a path of at most $d(2[\widehat R_{k_1-1}]+5)M$ adjacent $k_1$-blocks from $b_{k_1}(c)$ to a window block $y\subset\Lambda_{k_1}\cap Z_{k_1}^c$. The path lies in the old $\Omega_{k_1}$ because its excluded set begins at least $2[\widehat R_{k_1-1}]+6$ cubes in. Follow a coordinate-monotone block path to the closest face of $Z_{k_1}^c$ and stop at the first window block; the core reach of LFR III.4.6 bounds its length with one added collar block. Each path cube must then be assigned either to the deep $\chi_{k_1}(\Omega_{k_1}^{\sim-3}\cap Z_{k_1})$ or to the interior-side $\chi'_{k_1}(\Omega_{k_1}\cap(\Omega_{k_1}^c)^{\sim3}\cap Z_{k_1})$ of Definition II.5.6 at the preceding step. These supports cover the path, including the added collar block. The precise cube-incidence theorem for the actual minimal-set constructor is not landed.

For the path bond bound, use the retained (1.24) restriction at $j=k_1-1$ on each $\pi_{k_1}$ cube of the path in $\Omega_{k_1}^{\sim}\cap Z_{k_1}$. It tests the original full field on $\mathbb B_k\cap\square^{\sim}$ at $3dL\delta_{k_1-1}$, including a bond to the first exterior window block. This is the conservative estimate even in the interface band; it avoids reading the preceding-step $\chi'_{k_1}$ threshold as $3\delta_{k_1}$. Lemma III.4.5 gives $\delta_{k_1-1}\le e^\epsilon L^{(d-2)/2}\delta_{k_1}$, so take the explicit $C_{\rm reg}:=3dL e^\epsilon L^{(d-2)/2}$. The deep $\chi_{k_1}$ and interface $\chi'_{k_1}$ certify that the path lies on the retained small-field branch, while (1.24) supplies the stated bond bound. If the stronger $3\delta_{k_1}$ regularity asserted in LFR III.4.6 is proved for this band, one may set $C_{\rm reg}=3$. The present argument needs only the conservative fixed $C_{\rm reg}$. Neither WindowPieces.Hyp nor DeltaPsiCoreFinal.deltaPsi_le_pieces with its hcoreTop shortcut proves the support or regularity statement.

Assuming this support lemma, the path gives

$$|\psi_{k_1}(b_{k_1}(c))-\psi_{k_1}(y)|\leC_{\rm reg}d(2[\widehat R_{k_1-1}]+5)M\delta_{k_1}.\tag{2.2}$$

LFR Lemma III.4.4 (CH) connects $y$ to a terminal block $y_k$ with cost at most $3dL\widehat W_k\delta_{k_1}$. The final comparisons in III.4.6, using P7 (2.43) and the regular $\widetilde\psi_k^0$, cost at most $(3dK_6M\mathrm{crit}_k+4K_1K_6)\delta_k$. Strengthen (Λ21) by $C_{\rm reg}d(2[\widehat R_{k_1-1}]+5)M\le\widehat W_k$; its existing part bounds the final bracket by $\widehat W_k$, and $\delta_k\le\delta_{k_1}$. The triangle inequality proves

$$|D^{\rm ph}.\Psi(c)-D^0.\Psi(c)|\le C_\partial\widehat W_k\delta_{k_1},\quad c\in C_{\rm in},\qquad C_\partial:=3dL+3.\tag{2.3}$$

The extra unit allows strict inequalities. The same parent-lift/path argument covers the actual lower $G$ layers in the core; P7 (2.41)–(2.43) covers the boundary-piece lower layers; LFR III.4.6 covers the central window blocks. Hence the full interior profile is $|\Delta\Psi(x)|\le C_*\widehat W_k\delta_{\max(k_1,\min(n_G(x),k))}$ with $C_*:=\max(C_{23},C_\partial)=3dL+3$. This replaces the unsupported `hcoreTop` shortcut. (Λ22) must use $C_*$ and the actual weighted-response smallness threshold.

If a core collar site is **not** in the regularity set $T$, put it in $C_{\rm bad}$ and let $S_{\rm bad}$ be its interior neighbours plus interior sites with no profile. A separate amplitude $B_{\rm bad}:=\sup_{C_{\rm bad}}|\Delta\Psi|$ must be retained. The two real (R2) domains give only $B_{\rm bad}<4$, which is generally larger than `WeightedProp51S`'s $\delta_w$. Distance decay from that site is available *only after* $B_{\rm bad}\le\delta_w$ or another small-data response theorem is supplied; a bad site adjacent to $\operatorname{st}(Z_{k_1})$ has no useful distance gain there. Thus proving `inner_collar_in_regular_T`, rather than merely naming bad sites, is the completion route.

## 3. Corrected P7 $(2.49')$

Assume `ParentRefines`, `inner_collar_in_regular_T`, the support statements of §2, both actual P2 data-domain memberships and all `WeightedProp51S` premises. Set $\tau(n)=C_*\widehat W_k\delta_{\max(k_1,\min(n,k))}$ and impose the strengthened (Λ22), $\tau(1)\le\min(\delta_w,\delta_*)$. Equations (2.1)–(2.3) and the repaired interior proof give `DataChangeBound` on **all** of $\Omega_1(G)\cup C_G$. The difference vanishes on terminal $k$-blocks by P7 (2.47) and on $C_{\rm out}$ by (2.1), so the perturbation source is in the one-bond thickening $F$ of $\Omega_k^c$.

Let $\gamma=\operatorname{gammaW}(d)$, choose $0<\gamma'<\gamma$, and choose the separation so that the adjacent-layer profile ratio $R_\delta\le e^{(\gamma-\gamma')(\varrho-1)}$. The envelope proof of `COLLAR-3.md` §4 and `DeltaPhiResp.lean:pertSource_local` give, for each of $|\delta\phi|$, $L^j|\partial\delta\phi|$, $L^{2j}|\Delta\delta\phi|$, and $L^{2j}|\delta\alpha|$,

$$\boxed{\ \mathcal R(x)\le K_wc_F(d,L)A_0R_\delta C_*\widehat W_k\delta_j\,e^{-\gamma'd_G(x,F)},\qquad x\in\Lambda_j\cap\Omega_1(G),\ k_1\le j\le k.\ }\tag{2.49-fix}$$

Indeed the weighted source envelope is the supremum of $\tau(n(z))e^{-\gamma d_G(x,z)}$ over source sites. Factor $e^{-\gamma d}=e^{-\gamma'd}e^{-(\gamma-\gamma')d}$; the first factor is at most $e^{-\gamma'd(x,F)}$, while `DeltaPhiWeight.ratio_decay_le` with the remaining rate bounds the profile factor by $A_0R_\delta\tau(n(x))$. The envelope plus a positive floor defines an `IsWeight`; apply `WeightedProp51S`, divide by the weight, and let the floor decrease to zero. This proves (2.49-fix) under its stated premises. Its rate is $\gamma'$, not automatically P7's printed $\gamma_0/4$; that exact rate needs surplus Green decay. The positive $\gamma'$ can still pay the $\operatorname{st}(Z)$ term of P7 p. 511 after strengthening the radius condition (Λ25)(c). The estimate covers every layer of $X_{\rm win}$ and both surfaces because it is a whole-domain response.

If $C_{\rm bad}$ is retained and the full perturbation is small enough for the weighted theorem, its exact replacement is

$$\mathcal R(x)\le K_wc_F\left[A_0R_\delta C_*\widehat W_k\delta_j e^{-\gamma'd_G(x,F)}+B_{\rm bad}e^{-\gamma d_G(x,S_{\rm bad})}\right].\tag{2.49-bad}$$

`lemma41_uncond` supplies the second distance mechanism for a *small, supported* fixed-mass data change; `layered_response` supplies the first profile mechanism when its collar premise is verified. Neither result turns the unconditional bound $B_{\rm bad}<4$ into a small perturbation.

## 4. Mass-switch wall incidence and budget

Let $q=k+1$ be the switch scale and $X=X_{Z'}=Z_k^c\cap Z'$ of LFR Definition II.5.4. Compare the zero-mass and complete minimizers at the **same** physical datum. `ActionConvGreen.lean:Region.bondPair_green` gives the exact regional identity

$$A_{m,X}(D^{\rm ph},\phi^0)-A_{m,X}(D^{\rm ph},\phi^m)=\tfrac12\langle w,(H_m+\alpha^m)w\rangle_{X,*}+S_X(w,\bar\phi^m),\quad w=\phi^0-\phi^m.\tag{4.1}$$

Every bond of $\operatorname{st}(X)$ has an endpoint in $X$, hence in the one-site support $X^{+1}$ of this **new step action**. It does not need to be assigned to an old component. Each scale-$q$ cube contains $L^d$ scale-$k$ cubes of side $ML^k$ fine sites. Since $X$ is a union of scale-$k$ cubes, assigning each crossing bond to its endpoint in $X$ gives

$$\#\{b\in\operatorname{st}(X):x_b\in\square_q\}\le2dL^dM^{d-1}L^{k(d-1)},\qquad x_b:=\text{the endpoint of }b\text{ in }X.\tag{4.2}$$

The displayed bound counts both orientations conservatively; doubling it is harmless if an implementation charges a bond to both incident $q$-cubes. The spacing assertion needed here concerns the **new local generating set** $G_q^{Z'}$: if $x\in X\cap\Omega_q$, its layer has index $q$; if $x\in X\setminus\Omega_q$, then $x\in Z_k^c\cap Z'\subset W_k\cap U_{Z'}$, and the top layer of the minimal $\mathbb B_k(W_k\cap U_{Z'})$ contains $x$. Thus $x\in\Omega_k(G_q^{Z'})$ and its spacing is at least $L^k$. This uses Definition II.2.4, including the local intersection, not merely the global inclusion $X\subset\Omega_k(\mathbb B_k)$. `Background/ExistenceBounds.lean:BgBounds.grad`, for the complete background on its verified data-domain support, gives $|\partial\bar\phi^m(b)|\le G_\nabla\delta_k/L^k$ at the assigned endpoint; take $G_\nabla=K_1C_{\rm dat}$ when the full datum is in the real $C_{\rm dat}\delta_k$ domain of Theorem 5.2. LFR Remark II.2.8 gives $C_{\rm dat}=3dL$ on the verified support; the inherited physical collar must be included in that domain check. A same-data mass-source instance of `WeightedProp51S` must give $|w|\le K_mB_hm$ at both interior endpoints and $w=0$ on the common exterior collar. Use the bondwise estimate of `WALL-COLLAR.md` (1.2), (4.2), and $\beta_0^{(q)}=\beta_qL^{-q(d-2)}$ to obtain

$$|\beta_0^{(q)}S_X|\le C_W\beta_qm\delta_k|X|_q,\qquad C_W=2dM^{d-1}L^2K_mB_hG_\nabla.\tag{4.3}$$

The cancellation of scale powers is $L^dL^{k(d-1)}L^{-k}L^{-(k+1)(d-2)}=L^2$. This is the missing uniform wall incidence. An unscaled $|\partial\phi|<3$ leaves a factor growing as $L^k$ and cannot justify a fixed (S2) coefficient. At $q=k_0+1$ use $\beta_qm\le e^{2\epsilon}L^d$ from LFR IV.2.2, not the $e^{2\epsilon}$ bound valid only through $k_0$.

With a localized Hessian constant $C_D$, the complete per-new-cube interface input is

$$q_{\rm sw}=C_D\beta_qm^2+C_W\beta_qm\delta_k+C_EE_0m/\varepsilon_q+\bigl(C_Fc_9\xi_q^{\rho_F}m/\varepsilon_q+C_{F,0}m\bigr)\|g\|_1+q_{\rm data}+q_{\rm cut,meas},\qquad C_D:=\tfrac12C_HK_m^2B_h^2.\tag{4.4}$$

The last terms require the localized inherited $E,F$, cutoff, reference-measure and denominator comparisons of `INTERFACE-A.md`; (2.49-fix) supplies their background-response input, not the whole operator estimate. Pay a proved uniform bound on (4.4) by increasing the fixed $c_2$ in Definition II.5.11 before row 14 ends, and increase $c_1$ only for a proved logarithmic new-volume cost. Definition II.5.7 (S2) then has its new exponent. LF-RECONSTRUCTION Lemma II.5.12, the step clause (B) of LF-2, propagates the old (D6) lower bound through that exponent to (H6$^\flat$); (D6) is not itself a free wall reserve. Choose $\lambda_*,\beta$ only afterward (row 16). The mass-source response, local Hessian, and the remaining operator comparisons in (4.4) are still proof obligations.

## 5. Lean dependency order and status

1. `WindowGenGlue.lean`: prove `window_parent_refines`, `window_collar_partition`, `outer_collar_outside_reference`, `inner_collar_parent_layer`, and the one-site `inner_collar_in_regular_T` for actual minimal generating sets. The last theorem must cite the old $\chi_{k_1}$, near-interface $\chi'_{k_1}$ and retained (1.24), not `WindowPieces.Hyp` alone.
2. `DeltaPsiDef.lean`: define `inheritedField W ψ := psiTilde W.full ψ`; use it in `physicalWindowData` via `BgData.clip` and prove `parentLift_layerConst` and `physical_window_action_reads_inherited`. Change `psiTilde`/`psiTildeData` on the collar accordingly. Define `deltaPsi` as the difference of the two actual `BgData.Ψ` fields on `dataSites G`, zero only beyond those sites.
3. `DeltaPhi.lean` and `DeltaPsiCoreFinal.lean`: replace `DataChangeBound` by the full data-site difference; prove `core_shell_path_bound`, (2.3), `full_data_change_profile`, then `window_response_with_collar` and `window_response_decay` using `WeightedProp51S`. Replace the top-layer shortcut; strengthen (Λ21), (Λ22), and the decay use in (Λ25)(c).
4. `ActionConv*.lean`: keep `starPair`; prove `massChange_sameData_response`, `massChange_region_chord_with_star`, `massChange_wall_new_region` (4.2)–(4.3), and the local Hessian bound. Verify the localized $E,F$, cutoff, measure and common-denominator comparison, then (S0), (S2), (S4), (S5) and the scheme-A LF-2 instance.

**Status.** The explicit definition (1.1)–(1.2), the set-theoretic outer identity (2.1) under LFR's actual inclusions, the source-level path and cutoff reduction for (2.2)–(2.3), the weighted-response implication (2.49-fix), and the fine-wall count and scaling (4.2)–(4.3) are established here. The precise cube incidence in `ParentRefines` and `inner_collar_in_regular_T`, complete-background mass response, and the localized whole-operator bound remain to be proved against the actual constructors in Lean. This note does not claim unconditional P7 (2.49) or scheme-A closure. Sources: P2 p. 633 (4.9); P5 pp. 512–513 (2.47)–(2.49); P6 p. 16 (3.2); P7 pp. 499–501 (2.6)–(2.16), pp. 508–509 (2.40)–(2.49), p. 511 (2.58)–(2.60); LF-RECONSTRUCTION §§II.2, II.3.4, II.5.4, III.1, III.4–III.6, III.8, IV.2. No file under `/home/scott/Balaban` was changed.
