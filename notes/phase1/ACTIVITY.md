# ACTIVITY: the complete-background complex activity estimate

**Status (12 October 2026).** The implication from a physical label activity to complex nonvanishing is **PROVED CONDITIONAL ON A PROVED RESULT**: `StepActivityBound.Zst_eq_exp` and `stepNonvanishing_of_activityBound` in `Balaban/Fluctuation/StepNonvanishBound.lean:98–123` apply the proved `labelAct_integral_eq_exp`. The construction of `StepActivityBound` from an actual complete Def-6 class member is **OPEN-PHYSICAL-ACTIVITIES**. The conditional construction and its exact numerical test are given below. In particular, the landed `interaction_expansion_bound_nu_closed` is an expansion in a field `ψ'`, and the landed `i5_functional_hat` is a local expansion in `ψ̂` for *one supplied functional*. Neither declaration alone supplies the physical activities of `Wone + Wtwo`. No result here asserts that the complete-background step is closed.

All Lean paths in this note are under the read-only tree `/home/scott/Balaban/Balaban/`; no file there was changed. The paper conventions and the earlier source-level audit are in `FLUCTUATION.md` §§1.5, 3.3–3.5 and `COMPLETE-STEP.md` §2. The complex covariance ray and the real-variable comparison are in `RAY-CHART.md` §§2–3. Work on the massive old-term `XiDom` inclusion and the common cover is still required as described in `COMPLETE-STEP.md` §1 and `/home/scott/Balaban/notes/phase1/I6-ANISO.md`; the modular case is assigned to `notes/phase1/VMOD.md` (in preparation).

## 1. The exact target

Write `β = S.β` for the fine-lattice multiplier in `StepObjects.lean:248`, and
\(\beta_U=S.\mathrm{betaU}=\beta L^{k(d-2)}\) for the paper's \(\beta_k\) (`StepObjects.lean:278–279`). Let \(\mu\) be the positive complete-background mass, with \(0<\mu L^{2(k+1)}\le1\) whenever the top-level `BgHyp` is used. Fix complex class data in one common open neighbourhood and a complex source with \(\|g\|_{\ell^1}<1\). The fluctuation measure is supported on \(\max_{q,i}|\widehat\psi(q,i)|<p_1\).

`StepObjects.lean:393–408` defines exactly

\[
 W_1(s,\widehat\psi)=-\beta V^{(k)}(\psi^{(k)}+s\psi')+\delta\mathscr E_k(\psi^{(k)}+s\psi'),\qquad
 W_2(t,\widehat\psi;g)=\delta\mathscr F_k(\psi^{(k)}+t\psi';g),
 \quad \psi'=\beta_U^{-1/2}C^{(k)1/2}\widehat\psi. \tag{1.1}
\]

The needed family is a **single** finite set of labels \(\mathcal L\), a `CubeLabels Lab` on the \(\pi_{k+1}\)-cube system, and functions \(H_y(z,w;D,g,\widehat\psi)\) for \((z,w)\) in an open complex neighbourhood of the two real interpolation segments. They must satisfy, for every point of those segments and almost every \(\widehat\psi\),

\[
W_1(s,\widehat\psi)+W_2(t,\widehat\psi;g)
 =\sum_{y\in\mathcal L}H_y(s,t;D,g,\widehat\psi),\quad
 |H_y(z,w;D,g,\widehat\psi)|\le a_H e^{-\kappa_H\mathsf d(y)}. \tag{1.2}
\]

Each \(H_y\) must be measurable in the product fluctuation coordinate, depend only on the block coordinates in `blocksOf ... (Lab.ysite y)`, and be jointly holomorphic in the complex class data, \(g,z,w\) on the stated open set. The *same* label family must have the entropy bound
\(\sup_b\sum_{y:\,b\subset\operatorname{ysite}y}e^{-\kappa_0\mathsf d(y)}\le K_c\).
Those are the `LabelAct` fields in `Polymer/MarkedCubes.lean:169–184`; their support condition is a condition on the integration variable, not merely on the external datum.

`StepActivityBound` (`StepNonvanishBound.lean:57–95`) asks for these fields with \(\varepsilon_H\ge a_H\), a `BlockSplit` identifying \(\nu_{p_1}\) with a product of block probability measures, \(L^{m_0}\mid N_1\), and

\[
\begin{split}
\kappa_0&\ge a_{\rm ent}(d,L)+1,& K_c&\ge K_0(d,L,\kappa_0)+1,\\
\kappa'&\ge0,&\kappa_H&\ge\kappa'+3\kappa_0+c_1(d,L)+\tfrac32,\\
0<\varepsilon_H&\le\varepsilon_{\rm PE}:=
\bigl[8K_c^3c_1(d,L)e^{(\kappa_H-2\kappa_0)c_G(d,L)+c_1(d,L)+\kappa'c_G(d,L)}\bigr]^{-1}. \tag{1.3}
\end{split}
\]

The theorem only needs the identity (1.2) for `(s,0)` and `(1,t)` with \(s,t\in[0,1]\), including **complex** class data and \(g\). It does not itself ask for holomorphy, though the marked consumers do. For a common two-mark margin as in `FLUCTUATION.md` §3.4 use the stricter sufficient test \(\varepsilon_H\le\varepsilon_{\rm PE}/4\). This is extra activity slack, not a field of `StepActivityBound`.

The arithmetic behind (1.3) is already proved in `Polymer/MarkedCubes.lean:218–267` `numerics_PE`: with \(H_0=2\varepsilon_HK_c\) and \(\kappa_1=\kappa_H-2\kappa_0\), it gives
\[
2H_0K_ce^{\kappa_1c_G}c_1\le\tfrac12,\quad
2(2H_0K_ce^{\kappa_1c_G})c_1K_ce^{c_1+\kappa'c_G}\le1,
\quad H_0\le\log2.\tag{1.4}
\]
These are the `hq`, `hα`, and small-activity inputs used by the landed Mayer proof. The rate hypothesis in (1.3) supplies its `hκ`. No additional mass-dependent numerical inequality is hidden in this deduction.

## 2. What the landed local expansions actually say

`Fluctuation/Prop33.lean:49–57` sets \(M=L^{m_0+m_1}\), \(\kappa_U=2\kappa_{\rm dec}-1\), and

\[
P_{33}=
\frac{3c_1M^d\|\operatorname{energyBd}(\mu)\|}{r^3}
+\frac{\rho_Ec_1(L^{k+1}M)^d}{r}
+\frac{c_{K2}'\delta_1+\rho_M}{r}. \tag{2.1}
\]

Under all the hypotheses displayed in `interaction_expansion_bound` (`Prop33.lean:61–206`), its `LocInt` output has a finite exact sum, termwise analyticity in the upper raw data and \(\sigma\), a bound \(|\sigma|\,\|c_\beta\|P_{33}e^{-\kappa_U d^{\rm cov}_{k+1}(Y)}\), and agreement locality in the raw data and the **field** on `psiThick Y`. `interaction_expansion_bound_nu_closed` (`Fluctuation/Prop33CloseNu.lean:274–411`) adds a separate \(c_\nu\)-term. Its explicit `hBh` premise bounds the unweighted field \(D.h\), and the presently landed witness `hBh_of_xi` (`Prop33CloseBh.lean:33`) uses a bound proportional to \(1/\mu\). Thus that witness gives no mass-uniform bound for the added \(c_\nu\)-term. For the complete exponent (1.1), use `interaction_expansion_bound` **without** the extra \(\nu\)-term: the physical mass is already in `interactionV` and `energyBd`; a mass-variation mark is a separate problem. Merely setting \(c_\nu=0\) in the `_nu_closed` theorem would still leave its irrelevant `hBh` premise. The term \(\mu N V^2/2\) in `energyBd` (`InteractionEnergy.lean:234–238`) is bounded above with \(\mu L^{2(k+1)}\le1\), with no inverse mass.

The actual `LocInt` variables of Proposition 3.3 are \((\Theta,\psi')\), with \(\psi'\) an independent complex field. Substituting \(\psi'=\beta_U^{-1/2}C^{1/2}(\Theta)\widehat\psi\) into its terms does **not** preserve `psiThick Y` locality in \(\widehat\psi\): the covariance square root uses data outside `Y`. `Fluctuation/HatEngineLocalEngine.lean:135–217` `i5_functional_hat`, under its displayed `FlCore`, chart, cover, analytic-bound and functional-locality premises, does give terms `Ev Y (Θ, ψ̂)` with the exact `AgHat` dependence. By `HatEngineLocalFan.lean:41–44`, this means agreement of \(\Theta\) on `thickSet Y` and agreement of \(\widehat\psi\) at the unit points whose blocks meet `blockThick Y`. Its estimate is \(E_b e^{-\kappa_0 d_j^{\rm cov}(X)-2\kappa_{\rm dec}\widetilde d^{\rm cov}_{k+1}(Y)}\). This is a theorem **for one functional \(\Phi\) once its premises are proved**, and its `cc` is fixed. It does not quantify over the interpolation parameters or sum the physical \(V,E,F\) functionals.

There is also a **complex-data comparison** to make before using that theorem for (1.1). `StepObjects.lean:289–310` defines `S.K` from `S.covSqrt.map Complex.re`, whereas the hat engine uses the complex `decCovSqrt` itself. `RAY-CHART.md` (3.2), citing `HatEngineLift.lean:104–120`, identifies the two shifts on the **real** chart, where the matrix entries are real. It does not identify them at a nonreal class datum. At a fixed complex datum both shifts are complex-linear in the fluctuation variable after complexification, but they are generally different and the real-part map is not holomorphic in the datum. Thus **OPEN-STEP-COMPLEX-COMPATIBILITY** must either provide a hat-local expansion for the literal `StepSetting.shiftU` at fixed complex data, or amend the physical complex step to use the holomorphic square-root continuation and prove that its real restriction is the step being renormalized. The latter is the natural route for joint class-data analyticity. The estimate below is for that continuation until this bridge is supplied; it is not asserted as an identity for the literal `StepSetting.Wone/Wtwo` at nonreal data.

The physical expansion must therefore have the following strengthened output, called **OPEN-PROP33-HAT** here. It is the precise input needed below:

1. Settle **OPEN-STEP-COMPLEX-COMPATIBILITY**. Apply the hat engine with the *same* upper data, real mass \(\mu\), cover, covariance chart and \(m_0\) to every block-potential remainder, every old energy variation, every direct source site, every inherited observable variation and every mark required in §5. Prove their exact sums at the decoupling value \(1\), simultaneously for \(z,w\) on a common open complex neighbourhood of \([0,1]\), with one `BlockSplit`.
2. Prove joint holomorphy of each finite AE term in \((z,w,\Theta,g,\widehat\psi)\), on an open neighbourhood containing the **closed Cauchy discs** used for the directional derivatives. A fixed-`cc` application of `i5_functional_hat` does not prove holomorphy as `cc` varies. This follows mathematically from finite alternating AE sums and parameter-dependent holomorphic Cauchy integrals after a *uniform* analytic and domain margin has been supplied; the parameterized Lean lemma is not landed.
3. Reindex on connected \(\pi_{k+1}\)-cube labels that actually contain every block read by `AgHat`, identify the exact physical sum with (1.1), and prove a term bound and entropy estimate in **those same labels**. An external-data thickening can be recorded separately, because `LabelAct.dep` constrains only the fluctuation coordinate.
4. Supply source-root estimates uniformly on \(\|g\|_{\ell^1}<1\) and the physical normalization of §3. Supply all cover and `XiDom` hypotheses for the massive Def-6 terms, including the star-enlarged supports of `FLUCTUATION.md` (3.0)–(3.1), with constants independent of a positive lower bound on \(\mu\).

No currently landed declaration combines these four outputs. In particular, `AgHat Y` is not the `LabelAct.dep` statement with support `Y`: `blockThick Y` can meet further blocks. Calling the raw `LocInt` bound (2.1) a bound for a `LabelAct` on `Y` would omit a support enlargement and its rate cost.

## 3. Normalization and an explicit sufficient amplitude

Let \(\kappa_{\rm AE}\) denote the decoupling-polydisc parameter `κ` of `FlCore` (it may be much larger than the output-rate parameter \(\kappa_{\rm dec}\)). Put \(B_{\rm ray}=\sqrt N\,\operatorname{covSupConstC}(d,L,N,a(k),\kappa_{\rm AE})\) and
\(q=B_{\rm ray}\beta_U^{-1/2}p_1\). Equation (3.5) of `RAY-CHART.md`, from `CovSqrtSupComplexDec.lean:32–47` and `HatEngineLift.lean:104–120`, gives `vn ψ' ≤ q` on every data site. Fix \(R_\sigma>1\), \(R_1>1\), and a mass-independent \(\delta_1>0\). If

\[
q\le\frac{\delta_1}{4R_\sigma R_1},\qquad
r:=\frac{\delta_1}{4q}, \tag{3.1}
\]

then \(R_\sigma R_1q+rq\le\delta_1/2<\delta_1\). Thus for \(|\sigma|<R_\sigma\), \(|z|<R_1\), \(|\tau|\le r\), the ray \((\sigma z+\tau)\psi'\) stays strictly in `FlBall Hm δ₁`. This checks the *fluctuation-ball part* of the `XW` premise of `interaction_expansion_bound`; the class, collar and decoupling-domain premises are separate. The choice (3.1) is for \(q>0\); the zero-shift case has identically zero variations and is treated directly.

There is a normalization trap in the combined Proposition 3.3 statement. Its value (`Prop33.lean:194–204`) multiplies **every** one of the potential, old-energy, direct-source and inherited-observable pieces by the same `cβ`. For (1.1), put \(c_\beta=\beta\), present an old energy functional as \(E_\tau/\beta\), and present the physical source as \(g/\beta\) to that theorem. The inherited observable functional itself remains in its physical normalization. Then the combined expression is algebraically the desired \(-\beta V+\delta E+\delta F\), after the Taylor/fundamental-theorem identities below. Its printed `prop33Eps * β` bound uses only \(\|g/\beta\|_1<1\) and loses the cancellation of \(\beta\) in both source parts. `LocInt.wsum` (`Fluctuation/Prop33Agg.lean:37–100`) has the needed weighted sum and keeps \(\sum|g/\beta|\le1/\beta\); the sharper estimate must be carried through the `Prop33Bound` resummation. This sharper physical-source corollary is **OPEN-PROP33-SOURCE-NORM**, though its weighted-sum inequality is elementary. The invocation also requires \(\beta\ge1\).

For an explicit sufficient test, define \(E_*\) to be the right side of `energyBd d L N (compWeight L a₁) μ k (cK2' δ₁) δ₁ (rho4 ...)` with the \(\mu\)-term replaced by its bound from `BgHyp.massLe`; thus \(E_*\) depends on the chosen fixed radii and structural constants, not on \(1/\mu\). Assume the **physical** rooted bounds, at the rate and support used in Proposition 3.3,

\[
\rho_E^{\rm phys}\le C_E E_0,
\qquad \rho_M^{\rm phys}\le C_M c_9,\qquad \|g\|_1\le1, \tag{3.2}
\]

where \(C_E,C_M\) are fixed geometric/root-sum constants (including the termwise star cost where used), independent of \(\mu,\beta,E_0\). These are **OPEN-ROOT-SUM** for the actual class terms; the landed `Prop33` takes their analogues as hypotheses. If the output of the support conversion has coefficient loss \(C_+\ge1\) but preserves the selected rate \(\kappa_H\), then the estimates just described give the following completely specified **sufficient** amplitude:

\[
\boxed{\displaystyle
 \varepsilon_H=C_+R_\sigma\left[
 \frac{3\beta c_1M^d E_*}{r^3}
 +\frac{c_1(L^{k+1}M)^d C_EE_0+c_{K2}'\delta_1+C_Mc_9}{r}
 \right].}\tag{3.3}
\]

Here \(r=\delta_1/(4q)\), so equivalently

\[
\varepsilon_H=C_+R_\sigma\left[
 \frac{192\beta c_1M^d E_*q^3}{\delta_1^3}
 +\frac{4q}{\delta_1}
 \bigl(c_1(L^{k+1}M)^d C_EE_0+c_{K2}'\delta_1+C_Mc_9\bigr)
 \right].\tag{3.4}
\]

Equation (3.3) is **not a proved physical bound**: its hypotheses (3.2), the sharper source resummation, the exact identification with (1.1), and the support conversion remain open. It is an explicit algebraic consequence of those estimates, with every prefactor visible. If the rooted observable estimate has a larger H7 constant, replace \(C_Mc_9\) by that proven upper bound; the numerical proof is unchanged. The factor \(R_\sigma\) is essential for the `ObsMarks` activity on the whole \(\sigma\)-disc. Because \(q\propto\beta_U^{-1/2}p_1\), the first term is proportional to \(R_\sigma\beta\beta_U^{-3/2}p_1^3\), and the other terms to \(R_\sigma\beta_U^{-1/2}p_1(E_0+1+c_9)\), with the displayed scale factors. For the logarithmic \(p_1\) and the ordered choices of `FLUCTUATION.md` §1.5, these tend to zero at fixed \(\alpha_0,E_0\) in the admitted scale range, provided \(C_+\) and the radii are uniform there. This last uniformity is part of the open physical estimate; it cannot be inferred from a fixed-volume bound.

The `energyBd` bound uses only \(0<\mu L^{2(k+1)}\le1\); \(q\) is mass-uniform only under the **same** complex covariance chart hypotheses and margins for the family (`RAY-CHART.md` §§2–3). No \(1/\mu\) enters (3.3). The direct use of `interaction_expansion_bound_nu_closed` with the presently landed `hBh_of_xi` would invalidate this conclusion.

### The support-rate test that must accompany (3.3)

Let \(Y^+\) be a connected union of \(\pi_{k+1}\)-cubes containing every block meeting `blockThick Y`. The exact requirement is a finite-label map \(Y\mapsto Y^+\), with a uniform entropy estimate, and numbers \(a_+\ge1,b_+\ge0\) such that

\[
 d^{\rm cov}_{k+1}(Y^+)\le a_+d^{\rm cov}_{k+1}(Y)+b_+.
 \tag{3.5}
\]

Then a raw term with \(e^{-\kappa_Ud(Y)}\) has the bound
\(e^{\kappa_U b_+/a_+}e^{-(\kappa_U/a_+)d(Y^+)}\). Summing labels with the same enlarged support costs a **proved** fiber constant, say \(K_+\), at the chosen rate. One may take \(C_+=K_+e^{\kappa_U b_+/a_+}\) and any \(\kappa_H\le\kappa_U/a_+\). More generally, prove directly the weighted fiber bound

\[
\sup_{Y^+}\sum_{Y:\,\operatorname{enlarge}(Y)=Y^+}
 e^{-\kappa_U d(Y)+\kappa_Hd(Y^+)}\le C_+;\tag{3.6}
\]

this is precisely the coefficient estimate needed for (3.3) and can save rate relative to (3.5). **OPEN-HAT-SUPPORT-RATE** is (3.6), label connectedness, and the entropy bound for the enlarged labels. No `blockThick` covering-rate or fiber-count theorem was found in the landed hat engine. In particular, the paper choice \(\kappa_H=\kappa_U=2\kappa_{\rm dec}-1\) cannot be retained merely by renaming `Y` as `Y⁺`: it requires an additive-cost estimate or a reserve in the original rate. If (3.6) only permits a smaller \(\kappa_H\), it must still satisfy (1.3); otherwise this route to the marked cluster theorem does not close.

## 4. Conditional construction and proof of nonvanishing

Assume **OPEN-STEP-COMPLEX-COMPATIBILITY**, **OPEN-PROP33-HAT**, the physical normalization and Taylor identities below, **OPEN-ROOT-SUM**, **OPEN-PROP33-SOURCE-NORM**, **OPEN-HAT-SUPPORT-RATE**, and a common complex chart with (3.1). For each physical component \(q\) (potential blocks, old energy terms, direct source sites, old observable terms), let \(T_{q,Y}(z,w;D,g,\widehat\psi)\) be its hat-local AE coefficient. One valid finite label is \(y=(q,Y)\) with `ysite y = Y⁺`; repeated supports are allowed by `CubeLabels`, and the entropy bound must count all repetitions. Alternatively, sum the finite fiber for each pair \((q,Y^+)\) and use that pair as the label; this is the form estimated by (3.6), with the component index included in its sum. Retaining \(q\) avoids assuming a cancellation between different physical terms. In either form the finite sums inherit measurability and joint holomorphy. Agreement of the product fluctuation coordinates on `blocksOf ... Y⁺` implies `AgHat` agreement in \(\widehat\psi\); the external raw data are held fixed for `LabelAct.dep`. Thus each \(H_y\) has the required block dependence. The resummation and (3.6) yield (3.3), and the enlarged-label entropy estimate yields `LabelAct.entropy` with \(K_c\).

For the potential piece, the definition `interactionV` in `Fluctuation/ExpansionQuad.lean:287–294` is \(\frac12\alpha^{(1)}(\phi')^2+\frac12\langle\phi'-\phi^{(1)},H_k(\phi'-\phi^{(1)})\rangle\). Along the analytic complete-background solution, \(\alpha^{(1)}\) and \(\phi^{(1)}\) are linear in the tangent, while \(\phi'-\phi^{(1)}\) begins at order two. Consequently \(V(0)=DV(0)=D^2V(0)=0\), and Taylor's integral formula gives \(V(s\psi')=\int_0^1(1-u)^2D^3V(us\psi')[s\psi']^3/2\,du\). For each old energy and observable term, the fundamental theorem of calculus gives \(F(s\psi')-F(0)=\int_0^1DF(us\psi')[s\psi']\,du\). These identities, with the exact composed background and the normalization of §3, prove the sum in (1.2). The algebraic identities are **proved mathematically under analytic solution regularity**; their physical/Lean instantiation with the *actual* `StepSetting.Vk`, `dE`, `dF`, `interactionOne` and composed supports is **OPEN-W-PROP33-IDENTITY**. `Vk_psi0` (`StepIdentity.lean:741`) proves only the zeroth-order vanishing and is not a cited proof of all three Taylor coefficients. The `StepActivityBound.A` field is typed on all real pairs; define it by the constructed activity on `stepSegments` and by the zero activity elsewhere. The global `LabelAct` bound then holds, and only the segment values enter `hW`.

Choose the parameter order of `FLUCTUATION.md` §1.5: fix the geometry, \(\kappa_0,K_c\), the decoupling and class rates, the cover and radii, then \(\alpha_0>0,E_0\), then the final \(\beta_*(\alpha_0,E_0)\). Require at the final step \(\beta\ge1\), (3.1), the physical domain margins, the support-rate inequality in (1.3), and

\[
 C_+R_\sigma\left[
 \frac{192\beta c_1M^d E_*q^3}{\delta_1^3}
 +\frac{4q}{\delta_1}
 \bigl(c_1(L^{k+1}M)^d C_EE_0+c_{K2}'\delta_1+C_Mc_9\bigr)
 \right]\le\frac14\varepsilon_{\rm PE}.\tag{4.1}
\]

Once these **physical** inequalities have been proved uniformly for the admitted scales and \(0<\mu L^{2(k+1)}\le1\), the constructed `A (s,t)` fills `StepActivityBound` with \(\varepsilon_H\) from (3.3). `StepActivityBound.Zst_eq_exp` gives
\(Z_{s,t}=\exp\mathcal L_{s,t}\) on both segments and the finite bound \(|\mathcal L_{s,t}|\le|\mathcal B|\varepsilon_HK_cC_{\rm PE}\). Therefore \(Z_{s,t}\ne0\) for complex data and source, and `stepNonvanishing_of_activityBound` supplies `StepNonvanishing`. This last implication is **PROVED CONDITIONAL ON THE PROVED Lean cluster theorem**. The unresolved assertion is the construction of `A`, not the nonvanishing deduction.

## 5. One activity family for the marked consumers

The same physical coefficients can be organized as a master family \(B_y(z,w)\) with \(B_y(z,w)\) holomorphic on a common bidisc neighbourhood of \([0,1]^2\) and \(|B_y|\le a_He^{-\kappa_H\mathsf d(y)}\). Under the stronger inequality \(R_\sigma a_H\le\varepsilon_H\), the following restrictions use the **same** `Lab`, `BS`, \(\kappa_H,\kappa_0,K_c\):

| Consumer | Activity obtained from the master family | Other data still required |
| --- | --- | --- |
| `StepActivityBound` | \(A(s,t)_y=B_y(s,t)\) on `stepSegments` | Exact a.e. equality (1.2), product-measure split, entropy, (1.3). |
| `InterpMarks` for `E1Marks` (`Thm31a.lean:54`) | \(A(z)_y=B_y(z,0)\) for \(z\) in the open interpolation set | Local expansion of \(D\Phi_1(z\psi')[1_{B(v)}\psi']\) into marks `G i z`, with `hF`, holomorphy, rate \(\kappa_G\ge\kappa_H\), strictly positive `F0 i` and the same numerical fields. A zero mark may be padded by a positive bound. The separate `DetExpansion` is not supplied by activities. |
| `InterpMarks` for `Thm31c/d/e` (`Thm31cde.lean:81–119,172–199`) | The appropriate restriction of \(B_y\) with the extra boundary or remainder potential **included** | Its own physical exponent identity and local integrand marks. The whole-torus `Wone+Wtwo` restriction alone does not include these added potentials. |
| `ObsMarks` (`Thm31b.lean:46–124`) | \(A(z,\sigma)_y=\sigma B_y(1,z)\) on the open interpolation set and \(|\sigma|<R_\sigma\). Then `zero` and `holσ` hold, `holt` is inherited, and \(|A|\le\varepsilon_He^{-\kappa_H\mathsf d}\). | The first-order centered marks `G1`, their zero product mean and block count; the two-ended kernel `hker` with `supp_h`, `x_h`, `bound_h`; the remainder marks `Gr`; and the exact `hF` decomposition of the derivative of `McompAt` (`Thm31bStep.lean:32–45`). These are independent physical marked estimates. |

The `InterpMarks` and `ObsMarks` structures type their activities for **all** complex parameter values and require the `LabelAct.bound` globally, while their holomorphy fields only concern the designated open sets. Define the activities and parameter-dependent marks by the displayed formulas on those open sets and by zero outside; for `ObsMarks`, use zero also when \(|\sigma|\ge R_\sigma\). Each value then obeys its global bound, and the piecewise definition agrees with the holomorphic formula on an open neighbourhood of every point used by `holA`, `holt`, `holσ`, `holG`, or `holGr`. The entropy field is independent of the parameter. The `ObsMarks` scaling \(\sigma B_y\) is therefore a valid zero-at-\(\sigma=0\) analytic extension of the exponent; it need not be the paper's particular internal \(\sigma\)-path. Its uniform bound is why the factor \(R_\sigma\) is retained in (3.3). This scaling does **not** prove the centered-mark or kernel estimates. The `InterpMarks`/`ObsMarks` fields are stronger than `StepActivityBound`, so a master *package* of exponent and mark expansions can discharge all four consumers, but a single unmarked `LabelAct` cannot.

For the marks, Proposition 3.3 must deliver `y0`, `G`, `F0`, \(\kappa_G\) and the `hF` identity on one open interpolation set, not merely bounds for the exponent. For `ObsMarks` it must additionally deliver the centered `G1` and kernel factorization, or a separate physical lemma must do so. `interaction_expansion_bound_nu_closed` does not have these output fields; its `LocInt` conclusion is therefore not equivalent to `E1Marks` or `ObsMarks`.

## 6. Lean lemma list, in dependency order

The following are **new target statements**, not declarations claimed to be landed.

1. `completeHatChartUniform`: package the mass-uniform complex covariance chart of `RAY-CHART.md` with `BlockSplit`, `FlCore`, `HatConn`, `RowInHat`, the common cover, and the strict ray bound (3.1). Include the real `shiftU` identification and an explicit complex-step comparison resolving **OPEN-STEP-COMPLEX-COMPATIBILITY**; the landed real comparison alone is insufficient.
2. `completeOldXiHatDomain`: for every massive old Def-6 term on its star-enlarged support, prove the full \(\Xi^c_j\) inclusion along the complex fluctuation and Cauchy discs, with a fixed margin and actual collar/source coordinate. This is **OPEN-CLASS-PATH** of `COMPLETE-STEP.md` §1 and the anisotropic issue of `/home/scott/Balaban/notes/phase1/I6-ANISO.md`.
3. `hatI5_parametric`: strengthen `i5_functional_hat` to a family jointly holomorphic in \((z,w)\) and the class/source data, with one common `AgHat` support and constants. Apply it to potential blocks, old energy terms, source sites, observable terms and each mark. The existing theorem handles a fixed `cc` and supplied functional.
4. `completeW_taylor`: prove the zeroth-, first- and second-order vanishing of the actual `Vk` ray and its Taylor identity; prove the fundamental-theorem identities for `dE,dF` and the exact `interactionOne`/`StepSetting` comparison. This is **OPEN-W-PROP33-IDENTITY** in Lean.
5. `prop33_physical_source_norm`: keep the \(\|g/\beta\|_1\le1/\beta\) factor through `LocInt.wsum` and the `Prop33Bound` root resummation. State (3.3) with physical \(\rho_E^{\rm phys},\rho_M^{\rm phys}\), rather than applying the weaker printed `prop33Eps` bound after rescaling.
6. `completeRootSums`: derive (3.2) from H6/H7 and the corrected star supports, uniformly over admissible scales and \(0<\mu L^{2(k+1)}\le1\). Include the direct source site bound.
7. `hatSupportRate`: prove the enlarged-label geometry (3.6), `CubeLabels.isDj/meets/size`, and the entropy bound at \(\kappa_0\); choose \(\kappa_H\) satisfying (1.3) after the actual rate loss.
8. `completeMasterActivities`: assemble the finite local sums, measurability, `LabelAct.dep`, exact `hW`, bidisc holomorphy and (3.3); verify (4.1) in the §1.5 parameter order. This fills `StepActivityBound` and hence invokes `stepNonvanishing_of_activityBound` (already landed).
9. `completeE1Marks`, `completeInterpMarksCDE`, `completeObsMarks`: derive the separate mark and kernel fields listed in §5 from the same local engine and common label package. `DetExpansion` remains a separate trace-localization input. Then apply the already landed conditional `thm31a/b/c/d/e_of_input` declarations under their exact remaining hypotheses.

**Disposition.** The algebraic construction from the listed physical premises, the Cauchy-ball calculation (3.1), the normalization correction, the bound (3.3) from the sharpened component estimates, and the deduction of nonvanishing from `StepActivityBound` are **PROVED CONDITIONALLY** as stated. The uniform physical premise bundle (especially `OPEN-STEP-COMPLEX-COMPATIBILITY`, `OPEN-HAT-SUPPORT-RATE`, `OPEN-CLASS-PATH`, the source/root estimates and the mark expansions) is **OPEN**. Consequently (2.1)–(2.2) of `COMPLETE-STEP.md` are not yet proved for an actual complete-background Def-6 family.
