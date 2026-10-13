# Q13 round 33 — late parent domain

**PROVED (scope).** Read-only audit of landed Lean and P5 (1.19), (1.24)–(1.26), P7 §1. Put $k=j+1$, $k_0<k<k_f$, $Y=((A.H.step\,k).Z)^c$, $G=Cx.genW\,Y$, and $D=liftSingle\,G\,(Cx.liftData\,\psi_k)\,(hC\,h)$. The parent mass is $m=sfBgMassAt(L,k,\nu_k)=\nu_kL^{-2k}$, so $mL^{2k}=\nu_k$; the cube mass agrees only above $k_0$. [Def6v2Regime: sfBgMassAt, lfBgMass_eq_sfBgMass_of_lt.]

## Exact missing estimate

**PROVED (field identification).** At $s\in dataSites(G)$, parentPsi Cx ψk s is $\psi_k$ at blkToBlock(jBlock $k\,s$); liftSingle_Ψ_eq_parentPsi identifies it with $D.\Psi(s)$. The parent solver background is bgField on $G$, evaluated on $G.\Omega_1$, and is **not** the field in InPsiTilde.r3. P5 (1.19) instead tests the separate cube background $\phi_\square$ on $\square^\sim$. [History/ParentDomain.lean: parentPsi, liftSingle_Ψ_eq_parentPsi; Background/Data.lean: InPsiTilde.]

**REFUTED (background-only shortcut).** A bound on bgField $G$ where defined in $G.\Omega_1$ would not itself imply R3 at a datum site: R3 also covers collar sites and requires a quantitative comparison of $D.\Psi(s)$ with that background or its block average. Such a comparison is not a clause of ChiDomProp; invoking parent solver estimates before proving its real-domain hypothesis would reverse the needed implication.

**OPEN — RetainedDirectionAtParent (exact sufficient statement).** For every retained $C:A.H.Comp\,k$ with $C.1\notin A.H.rem\,k$, and every $s\in dataSites(G)$ with parentSiteCube Cx s $\in C.1$, require
$$\|parentPsi\;Cx\;\psi_k\;s-h\|<2\delta_k/\sqrt{\nu_k},\qquad
\delta_k=Cx.cs.delta\,k,\quad \nu_k=nr\,k>0. \tag{RD}$$
This includes retained shell sites outside every Y-cube stencil. The constant $2$ matches the Y-site consequence of P5's cube test, averaging and BlockClose; a direct top-block clause at constant $1$ would be stronger. The all-retained-sites quantifier makes the parent theorem's case split exact.

**OPEN (Lean-ready predicate).** With $H=A.H$ and $Y=((H.step\,k).Z)^c$, the binder body is:

    ∀ C : H.Comp k, C.1 ∉ H.rem k →
      ∀ s : BgT Cx.geo k, s ∈ dataSites (Cx.genW Y) →
        parentSiteCube Cx s ∈ C.1 →
          rn (fun i => parentPsi Cx ψk s i - hv i) <
            2 * Cx.cs.delta k / Real.sqrt (nr k)

The premise $0<nr\,k$ is separate, and the value tested is the datum at $s$, not bgField at an unspecified point.

**PROVED CONDITIONAL ON (RD), YDirectionAtParent, and $\eta<1$.** Set $\eta_Y=4(d+1)\delta_k$ and $\eta=\max(3dL\delta_{k-1},\eta_Y)$. R2 and $\eta<1$ make $u_s=\Psi_s/\|\Psi_s\|$ a unit vector. Then $\|u_s-h\|\le2\|\Psi_s-h\|$, whence (RD) gives $\nu_k|1-u_s\cdot h|<8\delta_k^2<\eta_Y^2$. Since layerIndex $s\le k$, this is exactly Background/Data.lean:InPsiTilde.r3, $mL^{2\ell(s)}|1-u_s\cdot h|<\eta^2$; r4 vanishes for unit $h$. YDirectionAtParent is the same $2\delta_k/\sqrt{\nu_k}$ bound on sites over $Y$, from RegIneq.FieldClose, BlockClose, CubeFieldAverage, and cube BgHyp.

## Decision from the landed class

**PROVED (literal domain).** Characteristic/OperatorDomain.lean:PsiTildeMulti tests only adjacent-block differences and $|\|\psi\|^2-1|$. ChiDomProp has two families at $3dL\delta_{i-1}$ and $3\delta_i$, plus a fluctuation bound. Operators/StepData.lean:ChiDomAt instantiates this on the localized history field. None has $h$, $\nu_i$, or a directional conjunct.

**REFUTED (implication from those tests).** A constant unit multiscale field $v\ne h$, with zero fluctuations, passes every pair and sphere test of ChiDomProp for positive tolerances. With $Y\ne\varnothing$, take a retained component born before the switch, keep its core off earlier small-field cubes, and interpolate unit vectors from $h$ on the chiY stencil to $v$ in its retained shell. Earlier $i\le k_0$ cube factors have no direction test; later ones test only their small-field cubes. An angular ramp can keep all strict pair defects small and still violate (RD) at a retained site. This refutes a predicate-level implication; it does not construct a nonzero physical kernel for that history.

**PROVED (explicit predicate witness).** For $N\ge2$, take orthogonal unit vectors $h,e$ and $\psi_i(b)=\cos\theta\,h+\sin\theta\,e$ at every block and scale, $\psi'=0$. For any $0<\theta<\pi$, ChiDomProp holds whenever its tolerances and fluctuation thresholds are positive, while $\|\psi_i(b)-h\|=2\sin(\theta/2)$. Choosing $\theta$ above the (RD) threshold where $2\delta_k/\sqrt{\nu_k}<2$ refutes any universal directional conclusion from ChiDomProp alone.

**OPEN (full-history realization).** A formal counterexample with $Y\ne\varnothing$, an admissible nonquiet history, and a nonzero D1 post term would require constructing that history and a compatible kernel; none is landed. This does not rescue the proposed implication from the present class axioms: PostWeightSupport extracts ChiDomAt, whose conclusion remains direction-free.

**REFUTED (uniform chain margin).** RetainedShell.lean:W2_subset_nbhd and retained_shell_subset_OmegaDD put relevant cubes within $2\lfloor R_{k-1}\rfloor+3$ scale-$k$ cubes of $Y$, but do not give a path inside the tested block sets. Even granting one, its top-block length is $O(M(2\lfloor R_{k-1}\rfloor+3))$, with accumulated allowance $m\,3dL\delta_{k-1}$. Since $R_{k-1}=R_b\lambda_{k-1}^2$, no landed inequality makes this $<2\delta_k/\sqrt{\nu_k}$ uniformly. Near the last ordinary input $\nu_k\lesssim(7/8)L^{-2}$, the target is order $L\delta_k$, while one history edge allows $3dL\delta_{k-1}$; near $k_0$, $1/\sqrt{\nu_k}$ can be order $\sqrt{\beta_k}$, but this does not settle later scales. [MASSIVE.md; R/ChainSeq.lean:deltaRun_decay, deltaRun_growth.]

**PROVED (source placement).** P5 (1.19) puts $\|\phi_\square-h\|<\delta_k/\sqrt{\nu_k}$ in the cube chi factor only for $k>k_0$. P5 (1.24)–(1.25) put pair/sphere and fluctuation tests in the large-field operator domain; (1.26) takes a supremum over it. P7 §1 retains those bounds and says $R^{(k)}$ is the identity for $k\ge k_0$. Neither source asserts a direction test on every retained operator component.

**OPEN — minimal class repair for (RD).** Extend ChiDomProp/ChiDomAt with $h$, $k_0$, and positive running $\nu_i$. In the first family at every $i=j+1>k_0$, require for each $b\in$ genBlocksIn B i (nbhd 1 {y}) **with layer $b.1=i$** that $\|\psi_i(b.2)-h\|<2\delta_i/\sqrt{\nu_i}$; its $i=k$ instance and parentPsi_eq_tested_local give (RD). Landed TopBlockTransport covers the retained parent sites by this first family, so a second-family direction clause is unnecessary for this parent theorem. Rotate $h$ with $\psi$ in symmetry statements. This strengthens P5 (1.24), rather than restating it; preserving the original density also requires a complementary-sector split and its large-field cost, rather than deleting that sector by a new vanishing assumption.

**PROVED (support distinction).** Changing only the definition of ChiDomProp makes the desired implication tautological but does not prove the landed operators vanish outside the new domain. Operators/LocOp.lean:locOp_vanish_chiDom and DomainIdentity transport precisely the old predicate. The changed support claim and a representation identity for the split sectors are separate proof obligations.

**OPEN (declarations carrying the clause).** Direct support chain: Characteristic/OperatorDomain (PsiTildeMulti, ChiDomProp, chiDom); Operators/StepData (ChiDomAt); Operators/LocOp (locOp_vanish_chiDom); Operators/DomainIdentity; History/PostWeightSupport, TopBlockTransport, LocalOutputTransport, ParentDomain, D1ParentDomain. Other direct mentions needing signature/proof review: Operators/Quiet, QuietEuclidDom, QuietStepDataMeas, QuietSymm; R/WindowRegSetBridge, WindowRegSetBond, DeltaPsiCollarActual, DeltaPsiCollarChiDom; History/BondLiftY, ParentR2Y, EarlyMassRatio; Inhabited/TopBlockTransportWitness. Constant-field witnesses must align with supplied $h$.

## Initial coupling and all-scale theorem

**PROVED (landed largeness premise).** D1ParentDomain.lean:inPsiTilde_of_postTerm2_ne_zero assumes exactly $hlam:\ 2a\exp(2\epsilon)<A_0^2\,runLam(a,b,k)^{2p_0}$, plus $0\le A_0$ and $0\le runLam(a,b,k)$. EarlyMassRatio.lean:two_nu_lt_delta_sq_of_lamHat gives the uniform early consequence from $2\le\widehat\lambda_0$ and $2a e^{2\epsilon}<A_0^2(\widehat\lambda_0-2)^{2p_0}$, where $\widehat\lambda_0=\log(a\beta)+1$.

**PROVED (absence in structures).** RunningHyp assumes only $\beta>0$; SFCtx has no initial $\beta$; Def7.Coh identifies $\beta$ and running constants but imposes no lower threshold. Def6v2Regime.Regime and Regime.IsFlow encode the switch and running identities, not this largeness. None supplies hlam without a separate initial-coupling premise.

**OPEN — one-line InitialBetaBridge lemma.** For $a>0,A_0>0,\beta_0>0,\beta\ge\beta_0$, $p_0\in\mathbb N$, $2\le\log(a\beta_0)+1$, and $2ae^{2\epsilon}<A_0^2(\log(a\beta_0)-1)^{2p_0}$, prove $2\le lamHat(d,L,\beta,a,0)$ and $2ae^{2\epsilon}<A_0^2(lamHat(d,L,\beta,a,0)-2)^{2p_0}$. Monotonicity of Real.log and nonnegative powers gives both; combine with RunningHyp.hat_le_runLam_add_two/lamHat_mono and EarlyMassRatio.two_nu_lt_delta_sq_of_lamHat to discharge each early hlam. This is the bridge from the papers' $\beta\ge\beta_0$ regime, with $\beta_0$ chosen to satisfy the displayed threshold.

**PROVED (branch arithmetic).** At $k\le k_0$, EarlyMassRatio.hmass_of_early supplies $2mL^{2k}<\eta^2$. At $k>k_0$, RunningHyp.lt_beta_mul_nu provides a lower bound on $\beta_k\nu_k$, so that mass-only estimate is unavailable; $0<\nu_k\le(7/8)L^{-2}$ supplies BgHyp.massLe at the next ordinary level via Fluctuation/ScaleUniform.lean:massLe_iff, but does not pay R3.

**PROVED CONDITIONAL ON RetainedDirectionAtParent, YDirectionAtParent, and the numerical premises — proposed all-$k$ theorem.** For every $1\le k=j+1<k_f$, postTerm2 Cx vc rep A ψk hv g $\ne0$ implies InPsiTilde $(Cx.genW\,Y)$ $(sfBgMassAt\ S.L\ k\ (nr\,k))$ $\eta$ $(parentPsi\ Cx\ \psi_k)$ $(fun\ i\Rightarrow hv\,i)$, and hence InDomainR for $D$, with $\eta=\max(3S.dS.L(Cx.cs.delta\,j),4(S.d+1)(Cx.cs.delta\,k))$. Assume hgeo, hcs, RunningHyp S.d S.L $\beta\,\nu_0\,a\,\epsilon\,b\,nr$, $Cx.cs.delta=deltaRun\ A_0\ p_0\ a\ b$, $\|hv\|=1$, cube BgHyp, $0<\delta_k$, $(d+1)\delta_k\le1$, $\eta<1$, and $0<\nu_k\le(7/8)L^{-2}$. In the late branch also assume $Cx.cs.mu\,k=sfBgMassAt(L,k,\nu_k)$, supplied by Def7.FieldClauses.mu_eq together with Coh.nu_cs. In the branch $k\le k_0$, additionally assume KZeroGenuine and InitialBetaBridge's threshold and invoke landed inPsiTilde_of_postTerm2_ne_zero. In $k_0<k$, invoke support (PostWeightSupport), R1/R2 (BondLiftY, ParentR2Y, LocalOutputTransport), YDirectionAtParent and (RD), then prove R3 as above. No late $2\nu_k<\eta^2$ hypothesis is imposed.

**OPEN (package 1, ≤180 lines; independent of class-term generators).** InitialBetaBridge: the exact initial-scale conclusion above from the $\beta_0$ premises, then a wrapper supplying landed per-scale hlam whenever $k\le k_0$. A separate delta-smallness corollary must discharge $\eta<1$ uniformly over the stopped range; it is not a field of RunningHyp.

**OPEN (package 2, ≤220 lines; independent of class-term local/global generators).** LateYDirection: chiY $Y\ \psi_k\ hv\ne0$, cube BgHyp, CubeFieldAverage, $k>k_0$, $0<\nu_k\le1$, and $cs.mu\,k=sfBgMassAt(L,k,\nu_k)$ imply $\|parentPsi(s)-h\|<2\delta_k/\sqrt{\nu_k}$ for every $s\in dataSites(G)$ over $Y$, plus positivity of its norm. Its cube stencil geometry is fixed by chiK.

**OPEN (package 3, ≤280 lines; dependent on class-term generator choice).** LateChiDomDirection: add the late top-block clause, prove ChiDomAt $\Rightarrow$ (RD) using TopBlockTransport/LocalOutputTransport for the actual chiDomGen, and reprove recursive support plus complementary-sector cost. Local and global generator choices require separate block-coverage proofs; a generic GeneratingSet gives neither.

**OPEN (package 4, ≤200 lines; logical assembly independent of generator choice, physical instantiation dependent through package 3).** LateParentR3: from (RD), YDirectionAtParent, R2, $\eta<1$, $0<\nu_k\le1$, and $mL^{2k}=\nu_k$, prove InPsiTilde.r3 on *all* dataSites $G$. AllScaleD1ParentDomain: combine it with landed R1/R2/support and the early branch, then provide InDomainR and zero-or-domain corollaries. Dependency order: 1 and 2, then 3, then 4; the complementary-sector producer is required before the strengthened class can represent the original density.

**OPEN (limit of the result).** The all-$k$ statement is a conditional theorem specification. The late directional class clause, its complementary sector, and the all-scale stopped flow have not been proved in Lean; the landed early theorem remains the only unconditional D1 parent-domain result.
