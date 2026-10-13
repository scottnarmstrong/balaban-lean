# COVROW — localized observable row at the zero class

13 October 2026. Read-only sources: [P6](/home/scott/Balaban/sources/s002200050470.pdf), printed pp. 41–43, (4.58)–(4.67); [P3](/home/scott/Balaban/sources/BF02506385.pdf), printed p. 81, Proposition 4.3. Formulae below were checked against the PDF images. Put $K=k+1$, $b=\beta3^k$, $w=(\log b)^p$, $c_\psi=\kappa_1\sqrt b$, $\kappa_1=\texttt{lvKappa}(\kappa,t)$, and $Q=\texttt{cK2'}(d,L,N)(\texttt{famConst}(d,L,BG_2,\kappa))$.

## 1. What P6 localizes

`PROVED (source reading).` P6 (4.58) has a first-derivative pair and a second-derivative pair. In (4.59) the second pair is localized by the P3 Proposition 4.3 procedure, with the earlier observable expansion and enlarged analytic spaces; (4.60) is its local bound. This is not the operator requested for the first pair.

P6 (4.61) defines $(\mathcal H_k C^{(k)1/2}\psi')(x)$ by a Cauchy integral of $\delta\phi_k(x;\tau C^{(k)1/2}\psi')$ **plus** Cauchy integrals of the old $\mathcal M^{(j)}$ derivatives. Its next sentence says “We construct a localization expansion for the operator $\mathcal H_k C^{(k)1/2}$ in the usual way.” It takes $r_0^{-1}=B_5(C_3c_7)^{-1}|\psi'|$ and $r_j^{-1}=16B_5K_2K_3L^\alpha(\alpha\alpha_0)^{-1}\xi^{-\alpha}|\psi'|$. Bound (4.62) is $\mathrm{const}\,|\psi'|e^{-2\kappa d_{k+1}(Y)}$, and the term reads $\psi'$ only on $Y$.

`PROVED (source reading).` P6 (4.63) separately localizes the expectation of $\psi'$ under $d\mu_{1,t}(\beta_k^{-1/2}\sigma,\psi)$: (4.64) is $2e^2\beta^{-1/8}\eta^{\gamma-\alpha_1}p_1(\beta_k)e^{-(2\kappa-3-6\kappa_0)d_{k+1}(Z)}$. After the product and resummation, (4.65) has rate $2\kappa-4-7\kappa_0$; (4.67) is the output bound. P3 Proposition 4.3 treats the independent $\psi'$ and the representation $\beta_k^{-1/2}C^{(k)1/2}(s)\widehat\psi$ of (4.24), with (4.52) local on $Y$ and decay $e^{-\kappa_0d_j(X)-2\kappa d_{k+1}(Y)}$. Identifying P6's “usual way” for (4.61) with that method is an inference; P6 cites P3 Proposition 4.3 explicitly for (4.59).

Here the zero class has no old $\mathcal M^{(j)}$ term. The landed theorem below localizes the $\delta\phi_k$ composite in (4.61), as an operator in the independent hat variable. It does not by itself establish the general-class old-observable summands.

The variable localized in (4.62) is the independent unit-lattice $\psi'$ entering the square root, before its expectation is taken. This is exactly the role of $\widehat\psi$ below. The output position $x$ stays fixed, and each localization domain contains its root.

## 2. Landed statements and the cheaper construction

`PROVED CONDITIONAL ON its displayed hypotheses.` `Fluctuation/SharpVF.lean:fsite_expansion_hat_dir` supplies one finite family $E_Y^{\rm hat}(D,\widehat\psi)$, indexed by `polymerDomains`, whose sum is $\delta\phi_x(D,\texttt{hatLift}(D,\widehat\psi))$ for every admissible datum and $\|\widehat\psi\|_\infty\le c_\psi$. Each term is analytic on a neighbourhood of `XiCRaw ×` the closed hat polydisc, bounded by $Q\delta_1e^{-2\kappa_{\rm dec}d(Y)}$, and local in raw data on `thickSet Y` and in hat coordinates at `unitPt hG' y` for $y\in Y$ (`SharpAE.AgHatDir`). `fsite_expansion_hat_both` gives the same terms with the additional weaker `AgHat` clause. The sharp clause is used here.

Its premises include `FlCore`, $k\ge1$, both level identities, `CovSetup`, `HatConn`, `RowInHat`, an optimal base cover and $d^{cov}(X)=0$, $c_\psi\ge0$, $c_\star e^{N_0\kappa}\le L^{m_1}$, the strict margin and coercivity inequalities, $\delta_c^2\texttt{smallConstX}\le1/4$, $\sqrt N|cc|\,\texttt{covSupConstC}\,c_\psi<\delta_1$, $\kappa_{\rm dec}\ge3\kappa_0+3$, $\kappa\ge4d(2L+1)^d\kappa_{\rm dec}$, and its two $h_1,h_{\log}$ numerical conditions. These are theorem assumptions, not consequences of this note. Use $cc=b^{-1/2}$.

The construction needs the theorem's `AgHatDir` locality, which is stronger than locality on a thickening of $Y$. Replacing it by the ordinary `AgHat` clause would bring back a geometric enlargement and its counting cost.

`PROVED (Lean provenance).` The proof of `fsite_expansion_hat_dir` invokes `SharpEngine.i5_functional_hat_dir`; its localization engine uses `I5Expansion.localization_expansion`. The cut-family Peierls sum is already absorbed in the stated $Q$ and rate. There is no second, uncounted family in the construction below.

`PROVED.` `InteractionHatV.hatLift` is $\texttt{liftC}(cc\,C^{1/2}(1)\widehat\psi)$; `StepComplexHat.liftC_shiftUC` and `StepComplexLocal.shiftUC_eq_smul_mulVec` identify this with the physical shift at $cc=b^{-1/2}$ and the step datum. `Localization/DecoupledSqrt.lean:decSqrtInt,decCovSqrt` define $C^{1/2}(s)=\pi^{-1}\int_0^\infty x^{-1/2}C_x(s)\,dx$; `StepComplex.covSqrtC` takes $s\equiv1$ at the complex background. `CovSqrtSupComplex.covC_sqrt_entry_decay` gives an entrywise exponential Agmon bound, but no connected-column decomposition at $d^{cov}$ rate.

`PROVED.` `Localization/RowsCov.lean:I4c_local_sqrt_rows` equates output rows of two square-root actions under `LocHyp`, matching multipliers on $S_Y$, fields on `rowsCov_R`, matching hat inputs at `UnitOut`, and `CompleteBlocks`. `Fluctuation/RowsCompose.lean:hatPsiF_rows` composes component agreement under cut/data/hat-input agreement. `Fluctuation/MarkedHatRows.lean:markedHatPsiF_rows_bridge_of_cover` extends masked-tangent agreement to a target already covered by components. None is a sum of localized covariance columns. `I5Expansion.gm3_fam` counts cut families inside the proved hat expansion, not a second column family.

`REFUTED.` For the terms of `InteractionFPart.fsite_expansion`, locality holds in the **physical** fluctuation on `psiThick Y`. Its derivative along $C^{1/2}e_{u,a}$ need not vanish when $u$ is far from $Y$; this is the OBSTILT counterpoint. The sharp hat terms are a different expansion of the already composed function. A proposed separate column decomposition and join $Y\cup W$ would need a full shared $\pi'_K$ cube for `SizeModUnion.G3_dcov`; a mere intersection with `psiThick Y` does not supply it. Thus the two-stage route has an unproved geometric premise and is unnecessary for this zero-class row.

Fix $x\in X_1$, component $i$, $u\in S.U$, $a\in\mathrm{Fin}\,N$, and a valid datum $D$. Let $\mathcal Y$ be the finite `polymerDomains` family and choose its $E_Y^{\rm hat}$. Set
$$e_{Y,u,a}(\zeta)=E_Y^{\rm hat}(\texttt{rawOf}\,D,\zeta e_{u,a}),\qquad
a_Y(x;u,a)=e_{Y,u,a}'(0).$$
The strict coordinate disc $|\zeta|<c_\psi$ lies in the analytic domain. `ObsCauchyTwoOrders.norm_deriv_zero_le` and the level-size identity `Prop33Level.treeLenCov_eq_treeLenCovOne` give
$$|a_Y(x;u,a)|\le Q\delta_1c_\psi^{-1}e^{-2\kappa_{\rm dec}d^{cov}_K(Y)}
=Q C_{\rm hat}b^{-1/2}e^{-2\kappa_{\rm dec}d^{cov}_K(Y)},\quad
C_{\rm hat}:=\delta_1/\kappa_1.$$
At the $d=L=3,N=2$ tower, $\delta_1=t$ and `LevelRayTower.lvKappa` gives $C_{\rm hat}=2\sqrt2(\texttt{covSupMaxC}(3,3,2,\kappa)+1)$. No separate covariance norm $C_{\rm cov}$ enters. The Cauchy estimate passes to the closed-radius bound by taking smaller discs to $c_\psi$.

If no $y\in Y$ has $\texttt{unitPt}(y)=u$, compare $\zeta e_{u,a}$ with zero in `AgHatDir`: $e_{Y,u,a}$ is constant, hence $a_Y=0$. If $a_Y\ne0$, choose such $y$. With $z=\texttt{unitBlock1}\,u$, `RootMarkGeom.mem_fineBlock_iff_unitBlock1` places $y\in\texttt{fineBlock}\,z$. `HatLabelsExpansion.isDj_of_polymerDomains` and `RootMarkGeom.rootCube_mem_blocksOf_of_isDj` put $bm(u)=\texttt{rootCube}\,z$ in `blocksOf Y`. Also `InteractionFPart.subset_of_mem_polymerDomains` gives $x\in Y$, so its cube $b_x$ lies in `blocksOf Y` by the same lemma. This proves both support clauses directly.

Define $T_Y=\texttt{blocksOf}(m_0,K,\texttt{univ},Y)$ and
$$hker(x;u,a,T)=\sum_{\substack{Y\in\mathcal Y\\T_Y=T}}a_Y(x;u,a).$$
`Polymer/MarkedCubes.lean:sitesOf_blocksOf` and `IsDj` give $\texttt{sitesOf}(T_Y)=Y$; thus $Y\mapsto T_Y$ is injective and the fibre has size at most **one**. Since `IsDj` makes $d_\Omega(Y)$ finite, `CubeSystem.dExt` is its real value here; `SizeModG4.G4_dOmega_le` yields $dExt(T_Y)\le d^{cov}_K(Y)$. Consequently
$$|hker(x;u,a,T)|\le Q C_{\rm hat}b^{-1/2}e^{-2\kappa_{\rm dec}dExt(T)}.$$
Take $\kappa_h=2\kappa_{\rm dec}$ (or a smaller rate required by `ObsMarks`), $C_{\rm op}=C_{\rm row}=1$, and $\texttt{Ch}=Q C_{\rm hat}/\sqrt b$. There is no bridge cost, `fibre_weighted_le` factor, or second-family entropy. Finite differentiation and regrouping prove $\sum_T hker=D_{\widehat\psi}\delta\phi_x(0)[e_{u,a}]$ and then the row identity after summing over $(u,a)$. `Background.LinearResponse.linearResponse` identifies the total with the constrained Green response only under its Standing and solution-family differentiation premises.

## 3. Remainder, multiplicity, and constants

Let $\Phi$ be a block configuration and $\widehat v_\Phi(u,a)=\texttt{ObsMeanBlock.blockMark}(S,m_0,hp,u,a,\Phi)$. `ObsMeanBlock.norm_blockMark_le` gives $\|\widehat v_\Phi\|_\infty\le p_1$; on the physical support it equals the Gaussian coordinate almost everywhere. Put $q=p_1/c_\psi\le1/4$, $\rho=q^{-1}$, and $e_{Y,\Phi}(t)=E_Y^{\rm hat}(\texttt{rawOf}\,D,t\widehat v_\Phi)$.

`PROVED CONDITIONAL ON the sharp-hat theorem and $q>0$.` On $|t|<\rho$, $e_{Y,\Phi}$ is holomorphic and $|e_{Y,\Phi}|\le Q\delta_1e^{-2\kappa_{\rm dec}d(Y)}$. Define $G_Y(t,\Phi)=\texttt{ObsCauchyTwoOrders.remExt}(e_{Y,\Phi})(t)$. `norm_remExt_le` gives for every complex $t$
$$|G_Y(t,\Phi)|\le8Q\delta_1q^2e^{-2\kappa_{\rm dec}d(Y)}
=\frac{8Q C_{\rm hat}^2p_1^2}{\delta_1b}e^{-2\kappa_{\rm dec}d(Y)}.$$
`differentiableOn_remExt` gives holomorphy on $|t|<3/2$ and the zero extension supplies the global bound. At real $0\le t\le1$, $G_Y=e_{Y,\Phi}'(t)-e_{Y,\Phi}'(0)$, so $\sum_YG_Y$ is the exact derivative remainder. `AgHatDir` makes $G_Y$ depend only on hat coordinates with unit points in $Y$; since $Y$ is a $\pi'_K$ union, these are block coordinates in $T_Y$. There is no covariance-row join.

Take remainder labels `HatLabelsAct.thickLabels` on $\mathcal Y$, with $\mathrm{ysite}(Y)=Y$ and $\mathrm{dl}(Y)=d(Y)$. With $\kappa_G=2\kappa_{\rm dec}-1$, choose $F_r(Y)=8Q\delta_1q^2e^{-d(Y)}>0$. Every $Y$ contains $b_x$, so `HatLabelsAct.entropy_thick` gives
$$\sum_rF_r e^{-\kappa_0\mathrm{dl}(r)}\le8Q\delta_1q^2K_0.$$
If $\mathcal Y$ is empty, the formal `ObsMarks.nonemptyr` field needs a dummy zero mark at the root cube with any positive prefactor at most $8Q\delta_1q^2K_0$; otherwise no dummy is needed. `Polymer/LabelExtend.lean:cubeLabels`, `cubeLabels_entropy` and `blockMark_fields_cubeLabels` provide the one-cube first-order labels, bound $F_m=p_1$, centering and measurability. A common label sum can use $K_c\ge K_{\rm act}+2K_0$ for these two added families.

The record `ObsMarks` further requires $\kappa_H\le\kappa_G$ and $\kappa_H\ge\kappa'+3\kappa_0+c_1+3/2$. The proposed tower choice $\kappa_H=\kappa_G=2\kappa_{\rm dec}-1$, $\kappa'=3\kappa_{\rm dec}/2+\kappa_0+1$ satisfies these after the explicit large-$\kappa_{\rm dec}$ inequality. It gives any output rate $\kappa_b\le\min(\kappa_h,\kappa')-\kappa_0-1=3\kappa_{\rm dec}/2$.

`PROVED (corrected geometric count).` The exact cube multiplicity is $n_{\max}=N\max_c\#\{u\in S.U:S.\texttt{cellOf}\,m_0\,u=c\}$. Since `PolymerGeometry.cellSide` is $L^{K+m_0+m_1}$, one $\pi'_K$ cube can contain $L^{d(m_0+m_1)}$ root blocks, each with at most $L^d$ unit sites by `DetCauchyBgActivity.card_blockU_le`. Hence $n_{\max}\le N L^{d(m_0+m_1+1)}$. The earlier $NL^d$ bound in OBSTILT assumed a false injectivity of root block to $\pi'_K$ cube. The explicit counting argument still needs a Lean wrapper.

With $p_1\le A_1w$, $R_g=b^s/(C_Rw^3)$, $\kappa_h=2\kappa_{\rm dec}$, and $n_*=NL^{d(m_0+m_1+1)}$, the exact `Thm31b.ObsMarks.B1/B2` definitions give
$$B_1\le C_{PE}\,Q C_{\rm hat}\,A_1n_*c_1K_c^2
e^{(\min(\kappa_h,\kappa')-\kappa_0)c_G}\,C_R\,b^{-1/2-s}w^4,$$
$$B_2\le8C_{PE}K_0Q C_{\rm hat}^2A_1^2w^2/(\delta_1b).$$
Here $C_{PE}=CPE(d,L,K_c,\kappa_H,\kappa_0,\kappa')$ and $c_1,c_G,K_0$ retain their landed meanings. The $B_2$ bound assumes the remainder-label wrapper above and the same $K_c$. Neither $n_{\rm Fibre}e^{a c_{\rm Br}}$ nor a covariance-column constant appears.

The $B_1$ factor $C_R$ is from $R_g^{-1}=C_Rw^3/b^s$. Its size is $O(b^{-1/2-s}w^4)$; $B_2$ is $O(b^{-1}w^2)$, uniformly in $k,N_1,\nu$ once the theorem premises and one initial-scale threshold hold.

## 4. Lean leaves and status

| Leaf, ≤300 lines | Exact target and existing declarations | Start |
|---|---|---|
| C1, strong, ≤240 | Under the complete premises of `fsite_expansion_hat_dir` and $cc=b^{-1/2}$, construct $a_Y$ by coordinate derivative; prove exact finite sum, Cauchy bound with $C_{\rm hat}$, and vanishing unless $\exists y\in Y,\texttt{unitPt}\,y=u$. Use `AgHatDir`, `norm_deriv_zero_le`. | now |
| C2, Sonnet, ≤230 | For $Y\in\mathcal Y$, prove $T_Y$ contains $b_x,bm(u)$ when $a_Y\ne0$, and $T_Y=T_{Y'}\Rightarrow Y=Y'$. Use `isDj_of_polymerDomains`, `rootCube_mem_blocksOf_of_isDj`, `sitesOf_blocksOf`. | now |
| C3, strong, ≤250 | Define finite $hker$ above; prove both `ObsMarks` support clauses, bound $Q C_{\rm hat}/\sqrt b\,e^{-2\kappa_{\rm dec}dExt(T)}$, and $\sum_T hker=\sum_Ya_Y$. Use C1–C2 and `G4_dOmega_le`. | after C1–C2 |
| C4, Sonnet, ≤180 | Prove $n_{\max}\le NL^{d(m_0+m_1+1)}$ by counting root blocks in a $\pi'_K$ cube, then unit sites per root block. Use `card_aligned_in_box` and `card_blockU_le`. | now |
| C5, strong, ≤280 | For each $Y$, construct $G_Y=\texttt{remExt}(e_{Y,\Phi})$; prove global bound, disc holomorphy, exact derivative identity, block `DepOn` and measurability. Use `norm_remExt_le`, `differentiableOn_remExt`, `AgHatDir`. | now |
| C6, Sonnet, ≤220 | Package C5 as `thickLabels` remainder marks with $F_r=8Q\delta_1q^2e^{-d(Y)}$; prove root support and weighted sum $\le8Q\delta_1q^2K_0$, plus the empty-family dummy. Use `entropy_thick`. | after C5 |
| C7, strong, ≤270 | Combine C1–C6 with `blockMark_fields_cubeLabels`, a common activity label extension, physical almost-everywhere identity, and `ObsMarks`; discharge $B_1,B_2$ with the displayed $n_*$. | after C3–C6 |

`PROVED CONDITIONAL ON` the listed sharp-hat premises: the zero-class operator row and remainder locality follow by the finite constructions above. `OPEN-OBS-COVROW` as a substantive zero-class localization assertion is discharged by the landed sharp theorem; C1–C3 are Lean packaging, not a new covariance analysis. `OPEN-OBS-REM` reduces to C5–C6's block-measurability, locality and label wrappers. `OPEN-OBS-NMAX` is the C4 wrapper. `OPEN` for full Theorem 3.1(b) remain the common complex-$t$ physical activity/exponent identity, common labels, the general-class old $\mathcal M^{(j)}$ pieces, and the final class/output assembly noted in OBSTILT. Confidence: high in the zero-class paper proof and geometry, conditional on the exact sharp-hat hypotheses; medium in the proposed Lean leaf sizes.
