# The one-level effective-action Hessian in the `PsiZeroInput` coordinates

**12 October 2026.** This note addresses `LF-RECONSTRUCTION.md` Lemma III.3.3 and P7 Lemma 2.1, printed pp. 506–507, (2.34)–(2.39). It uses the *single* generating set and action in `LargeField/R/PsiZeroData.lean` and `Background/Data.lean`. P4 (2.23)–(2.25), printed p. 687, was checked against the PDF page image; the OCR of P4 is not used for its formulas. `PsiZeroInput` is a named **input**, not a landed proof of its fields. The exact source of the coercivity constant below is the landed `LargeField/LF1.lean lf1_gradient`, whose explicit $\gamma_{\rm LF}=1/(28d)$ avoids assigning a numerical value to P4's unspecified positive $\gamma_0$.

## 1. Scope, defect in the bare statement, and normalization

Write $m=L^k$, let $T$ be the fine torus of side $N_0m$, let $T_k$ be the torus of $k$-blocks of side $N_0$, and put $Z=\operatorname{box}(b_0,w)\subset T_k$. The necessary actual-step geometry is
$$d,L\ge3,\quad N\ge2,\quad k\ge1,\quad
1\le w_i\le D,\quad D+2\le N_0,\quad
\operatorname{OverTop}G\bigl(Z\cup\operatorname{shellOut}Z\bigr).\tag{1.1}$$
For the gradient, also assume $Z\cup\operatorname{shellOut}Z\subset X$ and every site of `dataSites G` has its $k$-block in $X$. These are precisely the kinds of hypotheses already passed to `PsiZeroExists.local_analysis` and `psiZero_exists_unique_of_input`; they are **absent from the fields of `PsiZeroInput` themselves**. `BgHyp d L k ϱ a 0` supplies $a_j\in[1/2,2]$ and the background theorem's separation and mass assumptions. The box geometry is supplied by the late-scale construction for the intended $G=\mathbb B_k(U_k)$, subject to its source-to-Lean identification.

The bare assertion “`BgHyp` implies a `PsiZeroInput` for every box” is false. For a proper box take the legal generating set with $\Omega_j=\varnothing$ at every level. Its collar and `dataSites` are empty, so `dataR G ψ=0`, `effAction G a ψ=0` for every block field, and `TubeOn G Set.univ η ψ` is vacuous. Any nonzero $v\in\operatorname{SuppSpace}Z$ has Hessian zero, contrary to `hess` with $c>0$. Independently, with $G=\operatorname{singleGen}$ of `R/WindowGenSingle.lean` and $Z=T_k$ (permitted by the bare field), the constant unit fields $\psi(t)=\cos(t)e_1+\sin(t)e_2$ have zero effective action: the constant unit background equals the datum and every block and bond residual vanishes. At $t=0$ the gradient is zero because the real action is nonnegative; differentiating the zero curve gives $D^2F(e_1)[e_2,e_2]=0$. Thus a **proper Dirichlet box and active top-layer inclusion** are mathematical hypotheses, not proof conveniences. The first counterexample alone already applies with a proper box. These examples do not refute `PsiZeroInput` for the intended P7 geometry.

There is also a normalization difference. `Background.Data.action` and `PsiZeroData.effAction` sum energies on the **fine lattice**. A $k$-block has $m^d$ fine sites while its block-term coefficient is $a_km^{-2}$. Consequently the top-block quadratic and first derivative carry
$$s_k:=m^{d-2}=L^{k(d-2)}.\tag{1.2}$$
Comparison of P7 (2.36)–(2.38) with the fine-site definition shows that its displayed quadratic form uses block-unit coordinates, with this factor absorbed in the scale-$k$ action. Define the normalized mathematical function $\widehat F:=s_k^{-1}\operatorname{effOn}$. Then the uniform constants below apply to $\widehat F$. For the **landed, unnormalized** `PsiZeroInput` use $c_k=s_k c_*$ and $Gr_k=s_k Gr_*$. The type of the structure permits these values even though its comment suggests constants independent of $k$. Choosing only $c=c_*$ is valid for $d\ge2$ but makes $Gr/c$ grow with $k$ and loses the uniform $K_6,c_{11}$ of P7 Lemma 2.1. `PsiZeroExists.psiZero_constants` uses precisely this ratio; use the matched pair $(c_k,Gr_k)$ or normalize the function.

## 2. First and second variations (A1)

Here are formulas directly in the landed objects. Let $\Omega=G.\Omega1$, $n(x)=G.\operatorname{layerIndex}x$, $w_x=a_{n(x)}L^{-2n(x)}$, $Q\phi=\operatorname{blockAvg}G\phi$, and $\bar\phi=\operatorname{barField}G\Psi\phi$. The real action at $\nu=0$ is
$$S(\Psi,\phi)=\frac12\sum_{x\in\Omega}w_x|\Psi(x)-Q\phi(x)|^2
 +\frac12\sum_{x,\mu}\mathbf1_{\{x,x+e_\mu\}\cap\Omega\ne\varnothing}
 |\bar\phi(x+e_\mu)-\bar\phi(x)|^2.\tag{2.1}$$
This is `Background.Data.action` or `PsiZeroSmooth.actionRaw`, with its mass term set to zero. Let $Jv(x)=v(\operatorname{jBlock}_k x)$ on the fine sites of $k$-blocks in $Z$ and zero otherwise; as a data variation it is `liftSingle`/`dataR` applied to the zero extension `PsiZeroSpace.extSupp Z v`. Let $\phi=\phi_*(\psi)=\operatorname{bgField}G a 0(\operatorname{dataR}G\psi)$, $\alpha=\operatorname{bgMult}G a 0(\operatorname{dataR}G\psi)$, and let $u=D\phi_*[v]$. Real differentiability and the identification with the complex derivative follow by `PsiZeroSmooth.contDiffOn_effAction`, `Background.Def5.theorem72_real`, and `Background.Def5Response.theorem72_linearResponse` on the open BG domain. In particular,
$$H_D(\alpha)u+\dot\alpha\,\phi=S(Jv,0),\qquad
\phi(x)\cdot u(x)=0,\tag{2.2}$$
where $S(Jv,0)$ is `Background.Data.source` for the tangent datum and, in the notation of the landed response theorem,
$$u=\bigl(H_D(\alpha)^{-1}-\operatorname{constrainedOp}(H_D(\alpha)^{-1},\phi)\bigr)S(Jv,0).\tag{2.3}$$
The formula uses the complex bilinear constraint $\phi\cdot\phi=1$ in `Background.Data.IsEL`; on real data it is the usual Euclidean tangent constraint. The multiplier in (2.2) has the **plus** sign because `Multiscale.Operator.dirichletOperator` is $H_D(0)+\operatorname{diag}\alpha$.

For a general datum direction $Jv$, let $\mathcal E(f,g)$ be the polarization of the bond sum in (2.1), and let $\overline{(Jv,u)}$ equal $u$ on $\Omega$ and $Jv$ off $\Omega$. Termwise differentiation of the two finite sums gives
$$DF_\psi[v]=\langle\Psi-Q\phi,\,W(Jv-Qu)\rangle
 +\mathcal E(\bar\phi,\overline{(Jv,u)}).\tag{2.4}$$
The $u$ terms sum to $D_\phi S[u]=\langle H_D(0)\phi-S(\Psi,0),u\rangle=-\sum_{x\in\Omega}\alpha_x\phi_x\cdot u_x=0$ by (2.2). Thus the **envelope formula** is
$$DF_\psi[v]=\langle\Psi-Q\phi,WJv\rangle
 +\mathcal E(\bar\phi,\mathbf1_{\Omega^c}Jv).\tag{2.5}$$
For the P7 box (1.1), every fine site of a block of $Z$ belongs to $\Omega_k\subset\Omega$, so the second term vanishes. Summing $m^d$ identical top-layer residuals in each block yields the exact block-coordinate formula
$$DF_\psi[v]=a_k s_k\sum_{z\in Z}v_z\cdot
 \bigl(\psi_z-Q_k\phi(z)\bigr),\qquad
\|DF_\psi|_{\operatorname{SuppSpace}Z}\|
=a_k s_k\Big(\sum_{z\in Z}|\psi_z-Q_k\phi(z)|^2\Big)^{1/2}.\tag{2.6}$$
The last norm is the real Hilbert norm: `PsiZeroSpace.sq_norm_supp` identifies $\|v\|^2$ with $\sum_{z\in Z,i}v(z,i)^2$. Equation (2.6) is P7's last term of (2.36), with the factor (1.2) restored. It also gives the gradient without differentiating $u$.

For the Hessian, differentiate (2.4) along $\psi+t v$, writing $z=D^2\phi_*[v,v]$. The sphere constraint yields $\phi\cdot z=-|u|^2$ pointwise. Since $D_\phi S=-\alpha\phi$, the terms containing $z$ become $\sum_x\alpha_x|u_x|^2$. Therefore
$$\boxed{D^2F_\psi[v,v]=q_0(v,u)+\sum_{x\in\Omega}\alpha_x|u_x|^2},\qquad
q_0(v,u):=\sum_{x\in\Omega}w_x|Jv-Q u|^2
 +\mathcal E(\overline{(Jv,u)},\overline{(Jv,u)}).\tag{2.7}$$
For (1.1), $Jv=0$ off $\Omega$ and the second term of $q_0$ is the Dirichlet bond energy of the zero extension of $u$. Formula (2.7) is the one-level counterpart of P4 (2.23), including its positive constrained-response term; it is **not** obtained by applying `Fluctuation.Expansion*.expansion_chord`, `expansion_quadratic`, or `StepIdentityQuad.quad_identity`, whose statements compare two generating-set levels. `Background.MinimizerExpansion.actionC_add` gives the existing quadratic expansion in $\phi$; new data-line polarization lemmas supply the $Jv$ terms. `LargeField/Base/ChordQuadratic.action_sub_eq_chord_quadratic` explains the same multiplier sign for a unit-field chord.

Multiplying the linearized EL equation (2.2) by $u$ and using $\phi\cdot u=0$ gives an alternative Schur formula. The tangent source is $S(Jv,0)=a_km^{-2}Jv$ on $Z$ and zero elsewhere (its `boundaryTerm` vanishes), so
$$D^2F_\psi[v,v]=a_k s_k\sum_{z\in Z}|v_z|^2-
 a_k s_k\sum_{z\in Z}v_z\cdot Q_k u(z).\tag{2.8}$$
This is the real version of the `theorem72_linearResponse` inverse formula and of P4 (2.23)'s Schur complement. Equations (2.7) and (2.8) are exact on the BG real tube; no Taylor remainder is hidden in them.

## 3. Coercivity with an explicit constant (B1)

Put
$$\gamma_{\rm LF}:=\frac1{28d},\qquad c_D:=\frac4{(D+1)^2},\qquad
g_D:=\gamma_{\rm LF}c_D,
\qquad B:=\operatorname{bgK1}(d,L,N),\qquad C_T:=12d(D+2)+4.\tag{3.1}$$
All are explicit landed definitions except the abbreviation $C_T$; `LF1.lean gamma0`, `ZeroDomainCoercive.lean cDirichlet`, and `Background.ExistenceSetup.bgK1` give their exact formulas. For $d,L\ge3$, $N\ge2$, $D\ge1$, $g_D,B,C_T$ are positive. Let
$$\eta_0:=\min\left\{\frac{\operatorname{bgC2}(d,L,N)}{C_T},\quad
\frac{g_D}{8B(g_D+2)}\right\}.\tag{3.2}$$
`bgC2` is the explicit radius in `Background.Def5Response`; both arguments of the minimum are positive by its definition and the landed positivity of the BG constants. The first ensures that the reference field used for the gradient has an open BG response domain. The second pays the multiplier term in (2.7). A smaller positive value is harmless.

**Gaussian part.** For *every* real $u$ on $\Omega$, construct the fields in `LF1.lean actionG` by taking its site field to be the zero extension of $u$, its top block field to be $v$ on $Z$ and zero off $Z$, all lower block fields zero, $X=T$, and $\mu=0$. The first term of `actionG` matches $\frac12\sum w_x|Jv-Q u|^2$: on an $n$-block there are $L^{nd}$ fine sites, each with coefficient $a_nL^{-2n}$. Its `bondE` term matches $\frac12\mathcal E(\overline{(Jv,u)},\overline{(Jv,u)})$: $Jv$ is zero off $\Omega$, so every bond not touching $\Omega$ has zero variation. Thus
$$q_0(v,u)=2\operatorname{actionG}(G,a,0,0,T,\psi^v,\widetilde u).\tag{3.3}$$
This is a direct finite-sum identity, but **not yet a landed bridge lemma** between the `Background` and `LargeField/LF1` action definitions. Apply the **proved** `LF1.lf1_gradient` to the right side. Its top-layer term gives $\gamma_{\rm LF}s_k$ times `pairSumT` on the top $k$-blocks. Because $v=0$ off $Z$ and `OverTop` contains $Z$ and its one-block shell, every edge in the full Dirichlet energy of $v$ occurs in this top-layer pair sum. `pairSumT` counts each undirected bond once; on the nonwinding torus $D+2\le N_0$ it equals the forward-bond convention of `dirichlet_box_coercive` for these supported fields. Consequently
$$q_0(v,u)\ge\gamma_{\rm LF}s_k\sum_{z\in T_k,\mu}|v(z+e_\mu)-v(z)|^2
\ge g_Ds_k\|v\|^2.\tag{3.4}$$
The last step is the **proved** `ZeroDomainCoercive.dirichlet_box_coercive`, applied componentwise (or directly to EuclideanSpace), with $w_i\le D$ and $D+1\le N_0$. This proves the missing *Gaussian* lower bound without using P4's unspecified numerical $\gamma_0$. The `OverTop` shell is needed exactly at the first inequality of (3.4).

**Multiplier term.** Let $W(u)=\sum_{x\in\Omega}\ell_x^{-2}|u_x|^2$ and $A(v)=a_ks_k\|v\|^2\le2s_k\|v\|^2$. The **proved** `Multiscale/CoercivitySharp.lean core_real_sharp` (equivalently the $\alpha=0$ case of `multiscale_coercive_sharp_gen`), componentwise, gives
$$\tfrac12W(u)\le q_0(0,u).\tag{3.5}$$
The elementary weighted triangle inequality $|Qu|^2\le2|Jv-Qu|^2+2|Jv|^2$ gives
$$q_0(0,u)\le2q_0(v,u)+2A(v).\tag{3.6}$$
Combining (3.4)–(3.6),
$$W(u)\le4q_0(v,u)+4A(v)
\le\left(4+\frac8{g_D}\right)q_0(v,u).\tag{3.7}$$
For $0<\eta\le\eta_0$, `PsiZeroData.inUnionDomainR_of_tube` and `Background.Def5.theorem72_real` put the real datum in the BG domain. `Background.Theorem52`/`ExistenceBounds.BgBounds.alpha` then give $\ell_x^2|\alpha_x|\le B\eta$. Hence
$$\left|\sum_x\alpha_x|u_x|^2\right|
\le B\eta\left(4+\frac8{g_D}\right)q_0(v,u)
\le\tfrac12q_0(v,u)\tag{3.8}$$
by (3.2). Equations (2.7), (3.4), and (3.8) prove
$$\boxed{D^2F_\psi[v,v]\ge\frac12\gamma_{\rm LF}c_D L^{k(d-2)}\|v\|^2.}\tag{3.9}$$
For $\widehat F=s_k^{-1}F$ this is exactly $\frac12\gamma_{\rm LF}c_D\|v\|^2$. It is uniform over the real tube $0<\eta\le\eta_0$, the admissible generating set, and the torus size **under (1.1)**. In the landed unnormalized `PsiZeroInput.hess`, take
$$c=c_k:=\frac12\gamma_{\rm LF}c_D L^{k(d-2)}.\tag{3.10}$$
This is a **complete mathematical implication from the proved cited LF-1, BG and box-coercivity results plus the explicit finite-sum and derivative identities (2.7), (3.3)**. The latter identities and the real second-derivative bridge have not landed. Without (1.1), (3.9) is false by §1. P7 (2.37)–(2.38) has $\gamma_0/72$ for a box of diameter $<15$; (3.9) replaces its $1/36$ Dirichlet constant by $c_D$ and makes the fine-lattice factor explicit.

## 4. Gradient at the reference vector (C1)

Let $\psi_k$ satisfy `TubeOn G (X \ Z) δ ψk` with $0<\delta\le\eta_0$ and the geometry of (1.1). Set $e=\operatorname{refVec}(z\mapsto\operatorname{eu}(\psi_kz),Z)$ and $\psi_{k,0}=\operatorname{mergeField}(Z,\psi_k,\operatorname{constSupp}Z e)$. `PsiZeroTube.norm_refVec` gives $|e|=1$. `PsiZeroExists.tube_merge`, with its displacement parameter $\nu=0$, proves
$$\operatorname{TubeOn}G\ \mathrm{univ}\ (C_T\delta)\ \psi_{k,0},\tag{4.1}$$
because `tubeRad d D δ 0 = (12d(D+2)+4)δ=C_Tδ`. The proof uses `shell_close`/`refVec_close` for the exterior boundary; no condition on $\psi_k$ inside $Z$ is needed. By (3.2), $C_T\delta\le\operatorname{bgC2}\le\operatorname{bgC1}$. Apply `PsiZeroData.inUnionDomainR_of_tube` and the **proved** `Background.Def5.theorem71`/`theorem72_real` bounds (the exact `BgBounds.val` field). For $x$ in a top block $z\in Z$,
$$|\phi_0(x)-\Psi_{k,0}(x)|\le B C_T\delta,
\qquad |Q_k\phi_0(z)-e|\le B C_T\delta.\tag{4.2}$$
The second inequality is just the average of the first over the $m^d$ sites of the block. Insert it into the exact envelope formula (2.6), use $a_k\le2$, `PsiZeroExists.card_boxFinset_le`, and `PsiZeroSpace.sq_norm_supp`:
$$\boxed{\left\|Df_{\psi_k}(\operatorname{constSupp}Z e)\right\|
\le 2B C_T D^{d/2} L^{k(d-2)}\delta.}\tag{4.3}$$
Here $f_{\psi_k}=\operatorname{effOn}G a (\operatorname{boxFinset}b_0w)\psi_k$. Thus use
$$Gr=Gr_k:=2\operatorname{bgK1}(d,L,N)
  (12d(D+2)+4)D^{d/2}L^{k(d-2)}\tag{4.4}$$
for its **landed** `grad` field. The normalized $\widehat F$ has the same expression without $L^{k(d-2)}$. The ratio entering `psiZero_constants` is scale independent:
$$\frac{Gr_k}{c_k}=
\frac{4B C_T D^{d/2}}{\gamma_{\rm LF}c_D}.\tag{4.5}$$
An honest implementation should use $D^{d/2}$ as a real square root of $D^d$ (or the larger integer $D^d$ already used in `psiZero_constants`). The field `grad` has no explicit `hdata`, `hXreg`, or `OverTop` binders, so (4.3) is a constructor theorem **for instances with those external hypotheses**, not a theorem from `BgHyp` and `TubeOn G (X\setminus Z)` alone. Its mathematical proof is complete given the already landed tube and BG bounds and the new derivative formula (2.6).

## 5. Lean order and status

No file under `/home/scott/Balaban` was edited. The following proposed declarations should be added only after the exact author-approved target statements are fixed. Sizes are estimates of new lines.

| Order | Proposed lemma and needed statement | Size | Landed input |
|---:|---|---:|---|
| 1 | `topLift_extSupp`, `topLift_zero_collar`, `topLift_block_count`: under `OverTop G (Z ∪ shellOut Z)`, identify `dataR` tangent data on top sites, its zero collar and $m^d$ sites per block. | 200–350 | `PsiZeroData.dataR_Ψ`, `LargeField.Background.Lift.liftSingle`, `PsiZeroSpace.extSupp`, generating-set block lemmas. |
| 2 | `actionRaw_line_data`, `actionRaw_line_pair`, `actionRaw_real_of_actionC`: polarize the block and bond terms, including the off-domain `barField` branch, and identify real and complex-bilinear actions. | 250–450 | `Background.Data.action`, `PsiZeroSmooth.actionRaw`, `Background.MinimizerExpansion.actionC`, `blockPart`, `bondPart`, `Minimizer.action_cast`. |
| 3 | `bg_real_fderiv_from_complex`, `effAction_envelope`, `effOn_grad_top`: derive (2.2)–(2.6) and the Riesz gradient on `SuppSpace`. | 350–700 | `theorem72_real`, `theorem72_linearResponse`, `contDiffOn_effAction`, `IsEL`, `PsiZeroSpace.sq_norm_supp`. |
| 4 | `effOn_hess_quadratic`, `effOn_hess_schur`: prove (2.7)–(2.8), including second sphere-constraint derivative and multiplier sign. | 350–650 | `MinimizerExpansion.actionC_add`, `Def5.mult_formula`, `theorem72_linearResponse`, `LargeField.Base.ChordQuadratic.action_sub_eq_chord_quadratic` for the sign check. |
| 5 | `quadratic_actionG_eq`, `top_pairSum_dirichlet`: establish (3.3), map `pairSumT` to the full supported block bond sum, with no factor-of-two loss. | 350–650 | `LF1.actionG`, `lf1_gradient`, `LF1.Setup.pairSumT`, `ZeroDomainCoercive.dirichlet_box_coercive`. |
| 6 | `hess_gaussian_lower`, `hess_mult_absorb`, `psiZero_hess_of_geometry`: prove (3.4)–(3.10), with $\eta_0$ (3.2) and $c_k$ (3.10). | 250–500 | `LF1.gamma0`, `Multiscale.CoercivitySharp.core_real_sharp`, `BgBounds.alpha`, `cDirichlet`. |
| 7 | `psiZero_ref_tube`, `psiZero_grad_of_geometry`: apply `tube_merge` at zero displacement and (2.6), proving (4.3)–(4.4). | 150–300 | `PsiZeroExists.tube_merge`, `card_boxFinset_le`, `PsiZeroTube.norm_refVec`, `theorem72_real`. |
| 8 | `psiZeroInput_of_geometry`: construct `PsiZeroInput` with $(c_k,Gr_k,\eta_0)$, then feed the existing existence theorem; keep (1.1) and the $X$ hypotheses as binders. | 100–220 | `PsiZeroInput`, `PsiZeroExists.psiZero_exists_unique_of_input`, `psiZero_constants`. |

**Status.** The two counterexamples and the scale-factor computation are proved directly from the definitions. Equations (2.4)–(2.8), (3.3) and the LF-1/coercivity chain give a complete paper proof of (3.9) under (1.1); their termwise and calculus bridges are **OPEN Lean work**, not landed declarations. The gradient (4.3) is proved conditional on the **proved cited** BG and tube bounds and the new exact envelope identity. The full `PsiZeroInput` for the actual history is conditional on the **OPEN** source-to-Lean assertion that its selected $Z_0$, $X=U_k^{\sim}$ and $G=\mathbb B_k(U_k)$ satisfy (1.1) and the `hdata`/`hXreg` conditions, and on Lean implementations in rows 1–8. Confidence is high in the two counterexamples, norm normalization and absorption algebra; medium in the actionG-to-actionRaw bridge until its exact index sets have been elaborated. No claim is made that the current conditional Lean lemma III.3.3 is closed.
