# OBSRAY — analytic observable ray and physical exponent

Lean paths below are relative to `/home/scott/Balaban/Balaban`. Statuses refer to the cited declarations as they stand; a proposed implication is marked **PROVED CONDITIONAL ON** its named open premise. Fix the zero class, $d=L=3$, $N=2$, $m_0=1$, $S=T.\mathrm{step}$, $c_\psi=\mathrm{lvCpsi}(T.\kappa,T.t,\beta3^k)$, $r=\mathrm{lvR}(T.\kappa,T.t,\beta3^k,p_1)$, $\varepsilon_U=\beta\,\mathrm{prop33EpsEtaScaled}(\ldots,1/\beta)$, and $a=2T.\kappa_{\rm dec}-1$.

## 1. Which coefficients are already analytic

**PROVED.** `Localization/I5Param.lean:259` (`abstract_expansion_on`) assumes analyticity in the decoupling variables for each fixed $u$ and produces coefficient sum, vanishing, locality, and bounds. `Localization/I5Expansion.lean:107` (`localization_expansion`) additionally assumes analyticity jointly in $(u,s)$; its last clause is `AnalyticOnNhd ℂ (evTerm ... F Y) S`. Thus choosing $U$ to be a product parameter gives *joint* analyticity of its coefficients.

**PROVED.** `Fluctuation/InteractionSymm.lean:145` (`i5_functional_evTerm`) exposes the coefficient as the actual `evTerm` of `fnOfDec`, together with its analytic clause on `XiCRaw ×ˢ FlBall`. The sharp-hat route uses the analogous `i5_functional_hat_dir` (`SharpEngine.lean:335`) for the functional composed with `hatLift`; `SharpVF.lean:140,264` then receives its analytic coefficient clause. An equality between the raw-field and sharp-hat coefficient maps is not needed here.

**PROVED.** `Fluctuation/SharpVF.lean:85,221` (`vblock_expansion_hat_dir`, `fsite_expansion_hat_dir`) yield coefficients $Ev_Y(\Theta,\widehat\psi)$ analytic on `XiCRaw ×ˢ {ψh | ∀ q, ‖ψh q‖ ≤ cψ}`. The first family expands each potential block; the second expands a site value of `flFieldOne`. Their locality uses `AgHatDir`, including the sharp hat coordinates of $Y$.

**PROVED.** `Fluctuation/ObsRowCoeff.lean:225` (`obsRowCoeff_of_sharpHat`) retains the same jointly analytic site coefficients and differentiates them at the zero hat field to obtain the observable row coefficients. `Fluctuation/ObsRemainderMarks.lean:125,134` (`differentiableOn_remExt_ray`, `ray_decomp`) then gives differentiability of their ray remainders on `ball 0 (3/2)` and the kernel-plus-remainder derivative identity. These statements concern $Ev$, not the source direct terms $Tt$.

**PROVED.** `Fluctuation/MarkedEvJoint.lean:157` (`marked_expansion_product_pair`) applies `localization_expansion` with $p=((\Theta,\widehat\psi),(u,t))$ on $(\mathrm{XiCRaw}\times\widehat B)\times W$. Its fourth clause is joint analyticity of the *same* `evTerm` in datum, hat field and marks. This is a marked block family; it does not identify its coefficients with the zero-class direct terms of `sourceDirectTerms_slice`.

**PROVED.** The marked theorem's parameter set uses the weak inequality $\|\widehat\psi(q)\|\le c_\psi$; `AnalyticOnNhd` nevertheless supplies an open neighborhood at each member. At the complex ray used below the strict $3c_\psi/4$ margin gives an explicit interior point, so no boundary analyticity is being inferred from a mere closed-ball estimate.

**PROVED.** `Fluctuation/InteractionDir3.lean:91,95,168` defines
$$\mathrm{rayTerm}(g,\omega,x_0,\sigma,\Theta)=\sigma\int_0^1\omega(t)g(\Theta,\sigma t x_0)\,dt,$$
$$\mathrm{raySrc3}(f,\omega,x_0,w,\sigma,\Theta)=\sigma\int_0^1\omega(t)\partial_w^3 f(\Theta,\sigma t x_0)\,dt,$$
and `dl3 Ev w` as three successive `lineD ((0 : Λ), w)` derivatives of $Ev$.

**PROVED.** `Fluctuation/InteractionDir.lean:43,49` defines `dirTerm Ev` with integrand `dirD Ev w` and `dirTermSrc f` with integrand `lineD w (fun z => f (Θ,z))`. The source terms use weight $\omega=1$; the potential cubic term uses `taylorWeight`.

**PROVED.** `dirTerm_analytic` (`InteractionDir.lean:89`) and `rayTerm_analytic` (`InteractionDir3.lean:177`) prove analyticity in $(\Theta,\sigma)$ for each fixed $(x_0,w)$. Their `fderiv` and iterated `lineD` arguments are the local input for parameterizing $w$, although the existing theorem statements keep $w$ fixed.

**PROVED.** `Fluctuation/SharpVF.lean:381–382,495–505` constructs the potential term as `rayTerm (dl3 (Ev Y) w) ω x₀ σ Θ`, proves its sum equals `raySrc3` of the potential, and takes finite sums over blocks. `Fluctuation/InteractionLocDir.lean:31–56` constructs the site term as `dirTerm (Ev Y) ω x₀ w σ Θ`, summing to `dirTermSrc`. `Fluctuation/SharpAssemblyScaled.lean:689` combines these components. `Fluctuation/SourceDirectTermsScale.lean:193` selects one $\mathcal Y,Tt$ before the datum/source and gives the exact expanded value
$$\mathrm{val}=-\beta\,\mathrm{raySrc3}(\widehat V,\mathrm{taylorWeight})+\beta\sum_s f_s\,\mathrm{dirTermSrc}(\widehat\phi_s,1).$$
The coefficient construction, including finite sums and zero padding, is in its proof, not an exposed equation for each final $Tt_Y$.

**REFUTED.** `Fluctuation/InteractionLoc.lean:38–49` (`LocInt.analytic`) varies $(\Theta,\sigma)$ with the hat pair fixed. It cannot be applied to $z\mapsto Tt_Y(z\widehat\psi,z\widehat\psi,1,\Theta)$. Likewise `DirectTermsFamilyOn` and `labelActFamilyOn_analytic` vary datum/source and $\sigma$, not the hat pair. `ObsRemainderMarks.ray_decomp` does not close this different obligation.

## 2. Ray reparametrization

**PROVED.** `Fluctuation/MarkedCubicJoint.lean:140` (`analyticOnNhd_rayTerm_dl3_param`) says that, for open $V$, analytic $\Theta_f,w_f$ on $V$, $\Theta_f(q)\in S_\Lambda$, and $\sigma w_f(q)\in B$ whenever $|\sigma|<R_1+r$, the map
$$q\longmapsto\mathrm{rayTerm}(\mathrm{dl3}\,Ev\,(w_f(q)),\omega,w_f(q),1,\Theta_f(q))$$
is analytic on $V$, provided $Ev$ is analytic on $S_\Lambda\times B$, $R_1>1$, $r>0$, and $\omega$ is analytic on the $R_1$ disc.

**PROVED CONDITIONAL ON the displayed domain calculation.** Take $V=\mathrm{ball}(0,3/2)$, $q=z$, constant $\Theta_f(z)=\Theta$, $w_f(z)=z\widehat\psi$, $R_1=2$, and $B=\{\phi: \forall q,\|\phi(q)\|\le c_\psi\}$. The theorem then proves ray analyticity of **each cubic potential coefficient**, without a new analytic theorem. The condition $|\sigma|<2+r$ follows from $(2+r)(3/2)p_1<(4+r)(3/2)p_1=3c_\psi/4<c_\psi$.

**PROVED.** The map $z\mapsto z\widehat\psi$ is complex linear and the datum is constant. Thus the `hΘ` and `hw` hypotheses of `analyticOnNhd_rayTerm_dl3_param` require only elementary `analyticOnNhd_const` and continuous linear map facts; the one substantive hypothesis is `hdom`. The theorem applies to the *diagonal* case $x_0=w$, which is exactly the form selected by `sourceDirectTerms_slice` after ray scaling.

**PROVED.** `Inhabited/LevelRayTower.lean:105` gives $r=c_\psi/(2p_1)-4$; `Inhabited/StepTowerScaleLemmas.lean` contains `StepScaleData.two_p_lt_cψ`. Hence $(4+r)(3/2)p_1=3c_\psi/4$ and the margin is strict. `Fluctuation/HatLabelsExpansion.lean:36` (`hatRaysO_pair`) puts every diagonal $(z\widehat\psi,z\widehat\psi)$ into `HatRaysO` for $|z|<3/2$ by using radius $(3/2)p_1$; `PhysicalTerms.lean:57` (`physXW`) requires this in both pair coordinates.

**OPEN-OBS-RAY-ACT.** The above cubic lemma alone does not prove the statement for the final $Tt_Y$: source coefficients are first derivative `dirTerm` integrals, and the existential source theorem does not expose a termwise equality to the analytic $Ev$ construction. There is no landed `analyticOnNhd_dirTerm_param` declaration. A short parameter lemma follows by the `analyticOnNhd_unitIntegral` proof of `dirTerm_analytic` (`InteractionDir.lean:89`); at weight $1$ and $x_0=w$ it can also follow termwise from the fundamental theorem of calculus, $\mathrm{dirTerm}(Ev,1,w,w,1,\Theta)=Ev(\Theta,w)-Ev(\Theta,0)$. The exact needed conclusion for the *selected* source witness is:

**OPEN distinction.** The source coefficient is a Taylor **first** derivative in the hat field, whereas `dl3` gives a **third** derivative. Replacing `dirTerm` by `rayTerm (dl3 Ev ...)` would alter the source expansion. The first derivative lemma must therefore be proved separately or bypassed by the difference formula at $\sigma=1$.

```lean
-- S, hp, I, Tt, 𝒴, hI are the output of sourceDirectTerms_scale_fromTower.
-- Θ is either (rawOf S.D', 0) or (rawOf S.D', fun y i => g y i / S.β).
∀ (Y : {Y // Y ∈ 𝒴}) (Θ ∈ physSΛEta S S.a₁ S.ν T.t (1 / S.β))
  (Φ : ∀ b, (S.blockSplit 1 hp).Ωb b),
  DifferentiableOn ℂ
    (fun z : ℂ =>
      let ψ := z • S.hatOf 1 S.p₁ hp Φ
      Tt Y.1 (ψ, ψ) (ψ, ψ) 1 Θ)
    (Metric.ball 0 (3 / 2))
```

**OPEN proof outline, about 140–190 Lean lines.** (1) Strengthen the same-witness conclusion of `sourceDirectTerms_scale_fromTower`, or a lower source lemma, with a termwise decomposition: finite block `rayTerm (dl3 Ev ...)`, site `dirTerm Ev`, and zero padding. (2) Obtain $Ev$ analyticity from `vblock_expansion_hat_dir` and `fsite_expansion_hat_dir`. (3) Prove the radius inclusion above and apply `analyticOnNhd_rayTerm_dl3_param` to every cubic block. (4) Prove the first derivative parameter lemma by `analyticOnNhd_unitIntegral`, using the same radius inclusion and analyticity of `fderiv` on the open hat ball. (5) Close finite sums, source scalar multiplication, zero padding, and the fixed-datum restriction. This is a corollary in mathematics, but not an immediate application to the currently *packaged* $Tt$.

## 3. Complex bound and locality

**PROVED CONDITIONAL ON the radius inclusion.** `DirectTerms.loc.bound` (`InteractionLoc.lean:43–44`) and `DirectTerms.bd` (`HatLabelsDirect.lean:51–70`) give, at $\sigma=1$ and every complex $|z|<3/2$,
$$|Tt_Y((z\widehat\psi,z\widehat\psi),(z\widehat\psi,z\widehat\psi),1,\Theta)|\le\varepsilon_U e^{-a\,\mathrm{treeLenCovOne}(Y)}.$$
Use `hatRaysO_pair` for membership in `physXW`; `I.xw` itself covers only the unscaled $p_1$ disc. This bound is stronger than the earlier safe $2\varepsilon_U$ per family. The component bounds used to construct `I.loc.bound` are `norm_rayTerm_le` (`InteractionDir3.lean:204`) and `norm_dirTerm_le` (`InteractionDir.lean:118`), with Cauchy factors $6/r^3$ and $1/r$.

**PROVED.** The bound has the exact final direct-term rate $a=2\kappa_{\rm dec}-1$ from `sourceDirectTerms_scale_fromTower`; there is no further loss from the complex parameter $z$. The inclusion $|z|<3/2$ is proved before invoking `LocInt.bound`, so the estimate does not extend a real-ray inequality by an unjustified maximum principle.

**PROVED CONDITIONAL ON OPEN-OBS-RAY-ACT.** Set $B_e(z)_Y(\Phi)=Tt_Y((z\widehat\psi,z\widehat\psi),(z\widehat\psi,z\widehat\psi),1,\Theta_e)$ on $|z|<3/2$ and zero outside. Each $B_e$ has prefactor $\varepsilon_U$, rate $a$, and entropy bound $K_0(3,3,T.\kappa_0)+1$. `DiagCont` (`HatDiagContBase.lean:127`) from `sourceDirectTerms_slice` supplies measurability after scaling the block field. `LocInt.loc` and `DirectTerms.ag` give `DepOn` for every $z$: complex multiplication preserves `AgFDirPair`; outside the disc both sides are zero. Thus locality has no analytic dependence on $z$.

**PROVED CONDITIONAL ON OPEN-OBS-RAY-ACT.** For the `DepOn` proof, if $\Phi,\Phi'$ agree on `blocksOf 1 (k+1) Set.univ Y`, the original `I.ag` gives agreement of their unscaled hat fields at all relevant unit points. Multiply each equality by the same complex $z$; `AgFDirPair` then holds for both coordinates of the scaled pair. Apply `I.loc.loc` with identical $\Theta_e$ and $\sigma=1$. The case $|z|\ge3/2$ is reflexivity of zero.

**PROVED CONDITIONAL ON OPEN-OBS-RAY-ACT.** `LabelAct.sub` (`Polymer/LabelSum.lean:176`) makes $B_0(1)-B_0(z)$ with prefactor $2\varepsilon_U$; `LabelAct.sum` (line 76) adds the $B_g$ copy with prefactor $\max(2\varepsilon_U,\varepsilon_U)=2\varepsilon_U$, rate $a$, and entropy $2(K_0+1)$. The old $4\varepsilon_U$ is a valid weakening, useful if the existing activity threshold is retained. `LabelAct.extendZero` then appends observable-domain and cube labels without changing the coefficients.

## 4. Identity with the physical exponent

**PROVED.** `Fluctuation/SourceDirectTermsScale.lean:193–217` has the `hval` clause for all $x,w,\sigma,\Theta$. It is now also exposed for the *same* $\mathrm{val},\mathcal Y,Tt$ in `Inhabited/SourceDirectTermsFromTower.lean:97–157` (`sourceDirectTerms_scale_fromTower`). Therefore the former **OPEN-OBS-VAL-FAMILY is closed**. `Inhabited/SourceFamilyRelativeFromTower.lean:38` still omits this clause, but its strengthening is optional if the proof uses `sourceDirectTerms_scale_fromTower` directly.

**PROVED.** The exact hval clause to retain in any family-strengthening is the equation in `sourceDirectTerms_scale_fromTower`:
$$\forall x,w,\sigma,\Theta,\quad\mathrm{val}(x,w,\sigma,\Theta)=-\beta\,\mathrm{raySrc3}(\widehat V,\mathrm{taylorWeight},x_1,w_1,\sigma,\Theta_1)+\beta\sum_s\Theta_2(s)\,\mathrm{dirTermSrc}(\widehat\phi_s,1,x_2,w_2,\sigma,\Theta_1).$$
It must be conjoined before the `DirectTerms` field so the same witness is retained; separate existential value witnesses would not identify the activity sum.

**PROVED.** `StepActivityDirectGeneral.lean:263–266,318–333` states and uses the real ray identities $\mathrm{val}_0(s\widehat\psi,1)=W_1(s)$ and $\mathrm{val}_g(t\widehat\psi,1)-\mathrm{val}_0(t\widehat\psi,1)=W_2(t;g)$ under its stated hypotheses. In the zero-class shared assembly, `Inhabited/SourceActivityFromTower.lean:94–242` proves $W_1(s)=s^2 B_0(s)$ and $W_2(t)=B_g(t)-B_0(t)$ almost everywhere; the factor $s^2$ disappears at $s=1$. Its `segAct` contains `.re`, so it is not a complex-$z$ activity.

**PROVED CONDITIONAL ON OPEN-OBS-RAY-ACT.** For real $t\in[0,1]$, finite-sum identities and the same-witness `hval` give
$$\sum_\ell A_{\rm phys}(t)_\ell=B_0(1)-B_0(t)+B_g(t)=W_1(1)+W_2(t;g).$$
`StepSetting.ae_WoneC_add_WtwoC_eq` (`StepComplexAgree.lean:193`) changes this to $W_1^C(1)+W_2^C(t;g)$ almost everywhere. The potential term cancels in $B_g(t)-B_0(t)$ because the two values have the same datum and hat pair, while the source terms differ by $g/\beta$; multiplication by $\beta$ leaves $g$. `SourcePhysValBridge.lean:195` (`sourcePhysVal_W2_fromTower`) independently proves the source difference at the shared tower. The $W$ identity is thus a remaining assembly proof, with no missing physical value formula.

## 5. Observable integrand bridge

**OPEN-OBS-F-BRIDGE.** `obsMarks_of_tilt` (`ObsMarksAssembly.lean:304`) constructs `ObsMarks` for $f(t,x)=\mathrm{obsRayFun}(S,F,x,t)$, where $F(\psi_h)=\mathrm{svec}\,\mathrm{flFieldOne}(S.D',\mathrm{hatLift}(S.D',\psi_h))(y,i)$ (`obsRayFun`, line 151). `thm31bC_of_input_M0` (`StepComplexThm31.lean:187`) requires the real-parameter derivative
$$f'(t,x)=\left.\frac{d}{ds}\mathrm{McompAtC}\bigl(C.m_0,C.Tm,S.a,S.\nu,\mathrm{Nat.le\_succ}\,k,\,S.\mathrm{dataUC}(S.\mathrm{psiAtC}(s,x)),g,y,i\bigr)\right|_{s=t}.$$
`psiAtC` takes $s:\mathbb R$ (`StepComplex.lean:295`), whereas `obsRayFun` uses the complex derivative of $\zeta\mapsto F(\zeta\,\mathrm{obsHatPt}(x))$. Extend the real curve by `psiHat (ζ • yhat x)` and use `psiAtC_eq_psiHat` (`StepComplexJoint.lean:125`) on real $s$. `McompAtC_zero_eq` (`StepComplexSource.lean:54`), `compTangent_psiHat` (`StepComplexJoint.lean:135`), and `bgFieldC_sub_eq_flFieldOne_hatLift` (`StepActivityHatFlRay.lean:56`) are the inputs to the following still-open local identity:
$$\mathrm{McompAtC}(\ldots,S.\mathrm{dataUC}(S.\mathrm{psiHat}(\zeta\widehat\psi)),g,y,i)
=F(\zeta\widehat\psi)+\mathrm{svec}_{\mathrm{stepG}}\!left[\operatorname{restrict}_{S.hG\prec S.hG'}\mathrm{bgFieldC}(S.D')\right](y,i).$$
The second summand is independent of $\zeta$. Its complex derivative vanishes; restriction of the first complex derivative to the real axis identifies the consumer's real derivative. `obsHatPt` (`ObsMarksAssembly.lean:147`) is the coordinate expression of `yhat` (`StepIdentityQuad.lean:235`).

**OPEN transport lemma.** For `I : ObsMarks ν BS W f bx` and `hf : ∀ s ∈ Icc (0:ℝ) 1, ∀ᵐ x ∂ν, f s x = f' s x`, define `ObsMarks.congr_f I hf : ObsMarks ν BS W f' bx` by copying every field and replacing only `hF`; use `filter_upwards [hf s hs, I.hF s hs]` and rewrite. This is about 20–35 Lean lines. It suffices for an almost-everywhere integrand identity at each $s$; a pointwise identity on the cutoff support is stronger.

## 6. Ordered leaves

1. **OPEN, Sonnet, 90–130 lines, start now:** parameter analyticity of `dirTerm` with analytic $Ev$, analytic $\Theta_f,w_f$, and the $|\sigma|<R_1+r$ hat-ball premise. Input: `dirTerm_analytic`, `analyticOnNhd_unitIntegral`, joint $Ev$ analyticity. Output: `AnalyticOnNhd` in the parameter at $\sigma=1$.
2. **OPEN, strong, 150–220 lines, start now:** same-witness termwise decomposition/analyticity of `Tt` along the complex hat ray. Inputs: `sourceDirectTerms_scale_fromTower`, `vblock_expansion_hat_dir`, `fsite_expansion_hat_dir`, `analyticOnNhd_rayTerm_dl3_param`, leaf 1. Output: the displayed `DifferentiableOn` statement for every $Y,\Theta,\Phi$.
3. **OPEN, Sonnet, 90–140 lines, can start now:** complex radius membership, bound, measurable coefficients and `DepOn` for $B_0,B_g$. Inputs: `hatRaysO_pair`, `physXW`, `DiagCont`, `DirectTerms.loc.bound`, `DirectTerms.bd`, `DirectTerms.ag`. Analytic field added after leaf 2.
4. **OPEN, Sonnet, 70–110 lines, can start now:** physical $W$ identity on the common labels. Inputs: same-witness `hval`, real ray identities in `StepActivityDirectGeneral`, `SourceActivityFromTower`, and `ae_WoneC_add_WtwoC_eq`. Analytic activity assembly waits for leaves 2–3.
5. **OPEN, strong, 100–170 lines, can start now:** equality of the site integrands on the cutoff support using the three cited background/hat lemmas; then the 20–35 line `ObsMarks.congr_f` transport. Inputs are independent of leaves 1–4.

**OPEN final join.** Once these leaves land, form $A_{\rm phys}$, append the observable labels with `LabelAct.extendZero`, apply the existing scalar tilt and `obsMarks_of_tilt`, transport its integrand, and feed the resulting record to `thm31bC_of_input_M0`. The existing tower activity theorem supplies the common labels and numerical bounds; its real-clamped activity cannot replace the analytic family.
