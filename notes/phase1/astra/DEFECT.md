# The filed torus relevant part at one centre

## Verdict and scope

For the **full family class** of P4, the filed part has the required bound. More precisely, under the numerical hypotheses and the anisotropic data hypotheses below, there is an explicit constant $C_R$, independent of the torus, $j$, $k$, $y$, and the field, such that
$$
 |R_j^{T}(y;\Psi,h)|\le C_R E_0s_{jk}^{d+\alpha _3},
 \qquad s_{jk}=L^{-(k-j)},\quad \alpha _3=1-2\gamma-\alpha _1>0.
 \tag{1}
$$
The proof uses quantitative comparison of finite- and infinite-volume *reference jets*, including the tensor of second derivatives. It is not a consequence of `RenormCond` on a single torus or of a qualitative thermodynamic limit alone. This comparison and the link from a `StepClass` to a family `IsSFFamily2` have not landed in Lean. Thus (1) is a mathematical implication of the stated full-class assumptions, **not** a claim that blocker 6 is formally closed.

I audited `/home/scott/Balaban` at commit `4c96d5af9a24b6b009e5f2f200cb43879c0eae3e` (read only), with `WIDEGEN.md` SHA-256 `985629cb27787038ab45234c73ba87c37b3831a9fd60150ca799b5fbe917327d`. The five `IrrelTorus*.lean` hashes, in filename order `IrrelTorus`, `IrrelTorusBound`, `IrrelTorusBoundId`, `IrrelTorusBoundTube`, `IrrelTorusSum`, are `c0a28b07af84520fcfaa64c5201c6755ebe30609f7c8bcb8c8bbd98ffd290470`, `f56d448895a590f671f4f6262aa2bfc4093a1be725b9b8e31655e7b535e57cec`, `cccf0cd4885e718f6ff83503a06872bcba861c54b6bd7ace2f17a933805025a7`, `7e28b4bc9ef527e1edc6873cd16a7dc6a2081f4a76527aafd4b6ae77e9e18ebb`, `44b5ff7eb04193f99d53decc6b0d1afd4c2bbb9f44c1c38a84511b67e81a1477`.

The sources are Balaban, *A low temperature expansion for classical N-vector models. I*, Commun. Math. Phys. **167** (1995), pp. 118–119 (H.6)–(H.7), pp. 152–153, Proposition 3.10, (3.126)–(3.128), and Balaban, *A low temperature expansion for classical N-vector models. II*, Commun. Math. Phys. **182** (1996), pp. 677–678, (H.3)–(H.5). I used `pdftotext -layout` extracts in this directory. Both papers are scans. In particular the OCR of the displayed conditions on P4 p. 678 and of P1 (3.128) is garbled; the statements below use the legible surrounding prose and the explicit landed formulas, not an invented transcription of those displays. P1 (H.6) makes the first three conditions exact on the torus; P1 (H.7) is the thermodynamic second-moment condition. P4 (H.5) is stated in thermodynamic form. P1 p. 152 says the local expression at $y$ is assigned to the cover cube whose central large cube contains $y$.

## Exact statement

Fix $d\ge3$, $L\ge3$, $N\ge2$, $m_0,m_1\ge0$, $1\le j\le k$, and a torus parameter $N_1$ divisible by $L^{m_0}$. Write $\nu_j=\nu_k s_{jk}^2>0$, $r_j=\operatorname{anisoRadius}(d,L,N,P,j)>0$, and $\kappa=P.\kappa\ge a_{\rm ent}(d,L)+3$. Let the terms be the $N_1$ member of one family satisfying `IsSFFamily2` on the wide `completeXiDom`; the corresponding `SFTermClauses`, `TorusIndep`, full level-$j$ covariance `eucEloc`, and the four infinite-volume conditions `RenormCond` are all used. For the currently landed conversion through `IsSFFamily2.toLanded`, also supply `CRotE` on every torus and `MomNum d L N k j ϱ P`. The latter supplies the geometry, rate, and small-radius conditions. This extra `CRotE` is a route through the existing Lean bridge, not needed for the reference-jet argument itself.

Put $u=\sqrt{\Psi(y)\cdot\Psi(y)}$ (the principal branch), $v=\Psi(y)\cdot (\nu_jh(y))/u$, $\nabla_\mu\Psi=\Psi(y+L^je_\mu)-\Psi(y)$, and
$$
 g_{\mu\nu}=\nabla_\mu\Psi\cdot\nabla_\nu\Psi-
 \frac{(\Psi(y)\cdot\nabla_\mu\Psi)(\Psi(y)\cdot\nabla_\nu\Psi)}{\Psi(y)\cdot\Psi(y)}.
$$
Require the centred pulled-back data at $y$ to satisfy `DataHypAniso` with $\sigma=C_0s_{jk}$, $0<\sigma\le1$, $0<\varepsilon\le\Lambda r_j$, and $\sigma^2\varepsilon\le1/4$, for a fixed $\Lambda\ge1$. These are the same type of data and numerical restrictions used in `IrrelTorusBound.lean`; the assertion that the actual shifted step fields have them remains the separate analytic input W957(i). Require $\Psi$ to be constant on $j$-blocks, as in the step composition. Let $i_0\ne i_1$ be the reference spin directions.

In the notation of `IrrelTorus.lean`, set
$$
 R_j^T(y;\Psi,h)=\sum_{Z\in\mathrm{polysAt}(m_0,j,y)}
       \bigl(T_{y,Z}(\Psi,h)+\Phi_{y,Z}(\Psi)\bigr).
 \tag{2}
$$
This is exactly the final `∑ᶠ Z … TΦ Z` branch of `irrelTorus` when $X=\square(y)$. The sum is finite. No averaging or replacement of the labels $(j,y,X)$ is intended.

Here is one explicit admissible constant. Define
$$
\begin{aligned}
 A&=\operatorname{diamA}(d,L,m_0,m_1)>0,&
 H&=c_1(d,L)L^{d(m_0+m_1)},& Q&=L^{1+m_0+m_1},\\
 \kappa_0&=a_{\rm ent}(d,L)+1,&
 \lambda&=\kappa-\kappa_0-1\ge1,&p&=d+\alpha_3>0,\\
 G&=1600N^3\Lambda^2,&
 M&=1+H\Lambda+\Lambda^2+16d^2H^2(A+Q+1)^2G,\\
 b&=L^{m_0+m_1},&c&=\lambda b/(4A),&
 D&=\lambda\bigl(1+(Q+1)/A\bigr),\\
 C_R&=48e\,M\,K_0(d,L,\kappa_0)e^D
                 \left(\frac{p}{ec}\right)^p.
\end{aligned}
\tag{3}
$$
All factors are positive and depend only on fixed class and geometric parameters and $\Lambda$. These constants are deliberately coarse. They do not conceal a dependence on $j$, $k$, or $N_1$.

## Proof of (1)

**1. Infinite-volume cancellation at each centre.** Let $f_X$ be a term at the reference configuration $e_{i_0}$ and field $b=\nu_je_{i_0}$. Let $a_X(x)$ and $B_X(x,x')$ be its first longitudinal and second $i_1$-spin derivatives. The four infinite-volume coefficient sums are
$$
 V=\sum_X f_X(P_0),\quad A_1=\sum_X\sum_xa_X(x),\quad
 H_1=\sum_X\partial_{b_{i_0}}f_X(P_0),\quad
 S_{\mu\nu}=\sum_X\sum_{x,x'}B_X(x,x')(x-x')_\mu(x-x')_\nu.
 \tag{4}
$$
The sums converge absolutely: Cauchy bounds below cost at most four powers of $1+d_j(X)$ and the rate gap $\kappa-\kappa_0\ge2$ pays for these powers. `RenormCond.val`, `.dpsi`, and `.dh` give $V=A_1=H_1=0$ at the origin. The `.dh` condition is legitimate since $\nu_j>0$. Full level-$j$ covariance of the **density** transports these equalities to every aligned centre; one does not need the individual terms to be invariant under fine translations. The trace $\sum_\mu S_{\mu\mu}$ is zero by `RenormCond.moment`; the landed stronger all-centre scalar assertion is `momY_tsum_zero` in `Def6AvgMomLimit.lean`. Reflection of coordinate $\mu$ changes the sign of $S_{\mu\nu}$ for $\mu\ne\nu$, so its value is zero; coordinate exchanges make all diagonal entries equal, and their zero sum makes each zero. These transformations act on the whole density through `eucEloc`; applying them after an absolutely convergent derivative/sum interchange gives $S_{\mu\nu}=0$. Equivalently, the averaged-family implementation is `IsSFFamily2.sumCondsAvgA` followed by `moment_tensor`, together with the identification of its sum with the density jet. Thus the infinite-volume sum of $T_X+\Phi_X$ is identically zero for every value of $u,v,g$:
$$V+(u-1)A_1+(v-\nu_j)H_1-\tfrac14\sum_{\mu,\nu}g_{\mu\nu}S_{\mu\nu}=0.\tag{5}$$

**2. A quantitative finite/infinite comparison.** Measure lengths in $j$-blocks. The torus side is
$$B=N_1L^{m_1+k-j}\ge bL^{k-j}.\tag{6}$$
At an aligned centre, use the full-density translation covariance to transport the sums of reference jets to centre $0$. This works for the tensor in (4), since its coordinates are the differences of the `unlift` block positions relative to the centre. It is the sum that is transported, not each term of a fixed paving. At $0$, lift a finite-torus polymer to a shape $X'$ in $\mathbb Z^d$. Call a shape **small** if
$$4\{A(1+t_X)+Q+1\}<B,\qquad t_X=d_j(X)\ge0.\tag{7}$$
This is the landed `SmallAt` inequality. The geometry `liftPolys_diam` gives $|z_\mu|\le A(1+t_X)$ for every block of a good shape, so (7) implies
$$4(|z_\mu|+Q+1)<B\quad\text{for each }z,\mu.\tag{8}$$
The transfer lemma `goodAt_of_small`, `TorusIndep.E_eq`/`Einf_eq_torus`, and the identical centred block coordinates then identify the finite and infinite terms on a small shape as analytic functions near $P_0$. Their first and second derivatives therefore agree. Conversely, if an infinite-volume polymer has infinite-volume size $t_\infty$ with $4\{A(1+t_\infty)+Q+1\}<B$, the same diameter bound and `isPolyDom_transfer` place it on this torus as a small polymer. Hence the small-shape contributions cancel exactly in the difference between (2) and (5). This converse transfer is a needed new Lean lemma; the cited landed lemmas give its ingredients but no theorem about `R` currently packages them.

For every shape left in either tail, failure of (7) gives
$$t_X\ge\tau(B):=\frac{B-4Q-4}{4A}-1.\tag{9}$$
For an omitted infinite shape, the converse just proved gives the same inequality with $t_\infty$. The threshold may be negative on a small torus; (9) and the later bounds still hold. Thus a winding or nontransferable contribution is exponentially small in $B$ once $B$ is large. The precise assertion is (9), rather than a literal $d_j(X)\ge B$ with unit coefficient.

**3. Uniform bound for one tail summand.** Write $F_X=E_0e^{-\kappa t_X}$. The anisotropic polydisc of radius $r_j$ and the class bound give, by Cauchy,
$$|f_X(P_0)|\le F_X,\quad |a_X(x)|\le F_X/r_j,\quad
 |\partial_{b_{i_0}}f_X(P_0)|\le F_X/r_j^2,\quad
 |B_X(x,x')|\le4F_X/r_j^2.\tag{10}$$
These are the radii and the factor $4$ of `aniso_norm_tensA_le`, `aniso_norm_fderiv_inr_self_le`, and `aniso_norm_D2_basis_le`. The spin radius is $r_j$; only the longitudinal $b$ radius is $r_j^2$. Using the isotropic ball radius $r_j^2$ for the first derivative would lose uniformity in $j$.

`DataHypAniso.b_long` and `Frame.u_close` give
$$|u-1|\le\sigma^2\varepsilon\le\Lambda r_j,
\qquad |v-\nu_j|\le\sigma^2\varepsilon^2\le\Lambda^2r_j^2.\tag{11}$$
`exists_frame` supplies an orthogonal frame with matrix entries of modulus at most $40$. By `DataHyp.adj`, each component of a one-block field difference has modulus at most $\sigma\varepsilon$, hence each component after frame rotation has modulus at most $\sum_{i=1}^N40\sigma\varepsilon=40N\sigma\varepsilon$. Summing the $N$ products in its transverse dot product and using `Frame.gradTensor_eq` gives for each $\mu,\nu$
$$|g_{\mu\nu}|\le N(40N\sigma\varepsilon)^2
 =1600N^3\sigma^2\varepsilon^2\le G r_j^2.\tag{12}$$
The number of aligned blocks of a shape is at most $H(1+t_X)$ (`liftPolys_card_le`/`card_le_good`). On a finite non-small shape, each centred block coordinate has modulus at most $B/2$, and (9) implies
$$ B\le4\{A(1+t_X)+Q+1\}
 \le4(A+Q+1)(1+t_X).\tag{13}$$
Therefore $|z_\mu-z'_\mu|\le B\le4(A+Q+1)(1+t_X)$. For an infinite-volume tail shape, the diameter estimate gives $|z_\mu-z'_\mu|\le2A(1+t_\infty)$, which is smaller than the same right side. Substituting (10)–(13) into the **four actual terms** of $T_X+\Phi_X$ gives
$$
\begin{aligned}
 |T_X+\Phi_X|
 &\le F_X\left[1+H(1+t_X)\Lambda+\Lambda^2
 +\tfrac14d^2H^2(1+t_X)^2
     \frac{4}{r_j^2}G r_j^2
     16(A+Q+1)^2(1+t_X)^2\right]\\
 &\le M E_0(1+t_X)^4e^{-\kappa t_X}.
 \tag{14}
\end{aligned}
$$
The $h$ derivative in the Lean `TΦ` is with respect to $h$, while (10) is with respect to $b=\nu_jh$; its factor $\nu_j$ cancels the $1/\nu_j$ in $\Psi(y)\cdot h(y)/u-1=(v-\nu_j)/\nu_j$.

**4. Sum the two tails and extract the scale power.** The rooted polymer count on the finite torus and in the infinite-volume limit is
$$\sum_{X\ni0}e^{-\kappa_0t_X}\le K_0(d,L,\kappa_0).\tag{15}$$
This is `exp_sum_le_at` and its limit, the (G2) input already used by the class. For $t\ge0$, the exponential series gives $e^{1+t}\ge(1+t)^4/4!$, so $(1+t)^4e^{-t}\le24e$. Since $\kappa=\kappa_0+1+\lambda$ and every tail size is at least $\tau(B)$,
$$
\sum_{X\text{ in one tail}} M E_0(1+t_X)^4e^{-\kappa t_X}
\le24e\,M E_0e^{-\lambda\tau(B)}
       \sum_{X\text{ in that tail}}e^{-\kappa_0t_X}
\le24e\,M E_0K_0e^{-\lambda\tau(B)}.\tag{16}
$$
The triangle inequality between finite and infinite tails gives the factor $2$. From (6) and (9), with $x=L^{k-j}$,
$$e^{-\lambda\tau(B)}
\le e^D e^{-cx}.\tag{17}$$
The elementary maximum $x^pe^{-cx}\le(p/(ec))^p$ for $x>0$ gives
$$e^{-\lambda\tau(B)}\le e^D\left(\frac p{ec}\right)^p L^{-p(k-j)}.\tag{18}$$
Equations (16)–(18) prove (1) with (3).

The two places where a new formal proof is substantial are the finite/infinite **small-shape bijection** for the reference jets, including the converse direction in step 2, and the all-centre **matrix** cancellation in step 1. A mere `Tendsto` statement does not supply the rate in (16). The source's phrase “winding polymers” includes both finite-torus terms that do not stabilize and infinite-volume polymers omitted at that torus.

## The cube label and the W960/W962 count

`irrelTorus` at $X=\square(y)$ equals its unfiled term $E-T-\Phi-A$ plus $R_j^T(y)$. The unfiled term needs the same anisotropic I-6 bound as the off-cube term; the current theorem `irrelTorus_bound_of_dataHyp_of_poly` excludes the cube because its identification with `Itw` excludes the filing branch. A companion identity and bound for the unfiled cube are needed. Then the triangle inequality yields
$$|\operatorname{irrelTorus}(y,\square(y))|
\le (C_I+C_R)E_0s_{jk}^{d+\alpha_3}.\tag{19}$$
The landed `treeLenCovOne_box` gives $d_j(\square(y))=0$, so (19) is exactly the usual per-label bound with $e^{-(\kappa-1)d_j(X)}=1$; no extra geometric factor is needed.

For the far levels $j+n_1\le k$ in `classActivity_hnumH_of_uniform_gen`, choose $n_1$ so that $\sigma=C_0s_{jk}\le1$ and use $C_I'=C_I+C_R$ for **all far-level labels**. Let $K_L$ denote an independently established bound for the **whole filed label** at each of the last $n_1$ levels. Then the theorem's exact uniform counting constant is
$$
 \Lambda_{\rm count}'=L^{(1+m_0+m_1)d}E_0\cdot2K_0(d,L,\kappa_0)
 \left(\frac{C_I+C_R}{1-L^{-\alpha_3}}
       +n_1K_LL^{(n_1-1)d}\right).\tag{20}
$$
`classActivity_hnumH_of_uniform_gen` gives $\epsilon_C=c_1(d,L)\Lambda_{\rm count}'e^{\kappa_HB_{m_0}}$ under its stated rate $\kappa_HA_{m_0}+1\le2\kappa_{\rm dec}$. This is the **numerical bound** the W960/W962 counting can absorb; obtaining the required small amplitude still uses `amplitude_small_of_hnumH` and its separate large-$\beta$ factor. If (1) and the normalized data hypotheses are also established at every last level, an unfiled near-level bound $K_L^{\rm unfiled}E_0$ gives the whole filed bound with $K_L=K_L^{\rm unfiled}+C_R$. Counting the unique filed cube at each $y$ separately would remove one $K_0$ from the $C_R$ part, but is unnecessary.

## Lean shape and required bridge

Factor the local `TΦ` let-binding of `Balaban.SmallField.Def6v2.irrelTorus` into a named `relevantTorusTerm`, and define `relevantTorusSum` by the finite `polysAt` sum in (2). A quantitative theorem should take `hF : IsSFFamily2 P Rg β a (completeXiDom P Rg a) Tm ρ Ek`, `hCR : ∀ N₁, CRotE P (completeXiDom P Rg a N₁) (Tm N₁)` for the existing `toLanded` route, `hn : MomNum d L N k j ϱ P`, `hN : L ^ P.m₀ ∣ N₁`, `hy : Aligned (L ^ j) y`, the block-constant field condition, `DataHypAniso` on the centred pullback, and the numerical conditions preceding (2). Its conclusion is
`‖relevantTorusSum P.m₀ (Tm N₁) i₀ i₁ j y Ψ (constFld hv)‖ ≤ C_R * P.E₀ * s ^ (d + α₃)`.
The constant must be chosen before $N_1,k,j,y$ and the data binders. The useful intermediate statements are a `relevantTorusSum_eq_tail_difference` identifying the two tails of step 2, `relevantTorusSum_inf_eq_zero` for (5), and a uniform `relevantTorusSum_tail_bound` for (16). Existing anchors are `Einf_eq_torus`, `goodAt_of_small`, `liftPolys_card_le`, `exp_sum_le_at`, `IsSFFamily2.sumCondsInf`, `ElocInf_const_translate`, `momY_tsum_zero`, `LiftCtx.momentSum_eq_centre`, `IsSFFamily2.sumCondsAvgA`, `moment_tensor`, and `treeLenCovOne_box`. The new matrix argument must be phrased for the **sum** of terms; `eucE` only has paving symmetry, whereas `eucEloc` has full level-$j$ symmetry.

W954(iv) requires more than `StepClass.sum_classLabels_irrelTorus_eq_Edens`. `StepClass` in `Fluctuation/StepObjects.lean` stores only `m₀`, one-torus `Tm`, and `Ek`; it does not store `P`, `Rg`, a family over all $N_1$, `torusIndep`, `renorm`, or `CRotE`. Supply a producer of a family at the step's ambient index (its `Tm` has type `Terms … (k+1) …`) with `P.m₀=C.m₀`, whose member at the step torus is **definitionally or explicitly equal** to `C.Tm`, whose domain is the wide `completeXiDom`, and whose coefficients and mass match the step. It must prove `IsSFFamily2.torus`, `.torusIndep`, `.renorm` at all inherited $1\le j\le k$, `CRotE` for the analytic bridge, and `MomNum` for those levels. A single-torus `SFTermClauses` or the exact torus identity supplies none of the thermodynamic comparison. Finally the actual shifted chart fields must discharge `DataHypAniso` and the tube/polydisc condition of the unfiled I-6 bound; W957(i) records that separate open input.

**Confidence:** high in the quantitative inequality (the rate is superexponential in $k-j$ and the anisotropic radii cancel every jet denominator); medium in immediate formalizability, because the converse shape transfer and all-centre tensor comparison are not yet packaged in Lean. I found no counterexample to (1) under the full class hypotheses. Removing the family connection or the normalized anisotropic data removes an essential hypothesis of this proof.
