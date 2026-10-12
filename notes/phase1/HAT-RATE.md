# Hat supports, the complete interaction identity, and the physical source norm

All paths cited here are in the read-only tree `/home/scott/Balaban/Balaban/`. This note proves three finite-dimensional reductions for a complete-background step. It does not assert that the physical class, common complex chart, old-term domain inclusion, or stronger decay assumptions have been constructed. `OPEN-STEP-COMPLEX-COMPATIBILITY` is assigned separately. In the statements below, **PROVED** means a mathematical consequence of the displayed hypotheses; a proposed Lean declaration is explicitly called a target, not a landed theorem.

## 1. Enlarging a hat support

Fix the top level $j=k+1$, whole-torus region $\Omega=\mathbb T$, and the divisibility and size hypotheses $L^{m_0}\mid N_1$, $j\le K$, $L\ge3$. Put

$$
u=L^j,\qquad a=\operatorname{cellSide}(L,m_0,m_1,j)=L^{j+m_0+m_1},\qquad Q_b=\operatorname{box}(b,La),
$$

where $b$ is $a$-aligned. Let $Y\in\mathcal D_j$, as defined by `SizeModDefs.lean:47–66` `IsDj`. This applies to the actual `interaction_expansion_hat_bound` labels: `Prop33Bound.lean:38` `polyDom_isMultiDom` and `Prop33Count.lean:38` `isDj_of_isMultiDom` send each landed `polyDom` label to `IsDj m₀ j Y` under `IsLevel Gp j`. Define, without reference to a particular chosen cover,

$$
B(Y)=\operatorname{blockThick}Y,
\quad
\mathcal Q(Y)=\{b:\ b\text{ is }a\text{-aligned and }Q_b\cap B(Y)\ne\varnothing\},
\quad
Y^+=\bigcup_{b\in\mathcal Q(Y)}Q_b. \tag{1.1}
$$

`blockThick` is exactly `HatEngineLocal.lean:194`: it fills every $u$-block meeting `psiThick Y`, and `psiThick Y` is $Y$ plus its nearest neighbours (`I5FluctLocal.lean:43`). This is the hat-variable support required by `AgHatF` (`InteractionHatV.lean:265`) and `AgHat` (`HatEngineLocalFan.lean:41`). The other half of `AgHat` requires external raw-data agreement on `thickSet Gp Y` (`I5Local.lean:82`). By `thickSet_mono`, agreement on `thickSet Gp Y+` implies it; no sites of `thickSet` have to be added to the **integration-variable** support. Likewise, agreement of hat block coordinates on $Y^+$ implies `AgHatF Y` because $B(Y)\subseteq Y^+$. This distinction avoids charging an unbounded external-data dependency to a product-measure support.

**Connectedness and label membership — PROVED.** `psiThick Y` is connected: attach each new neighbour by its edge to $Y$. Every filled $u$-block is connected and intersects `psiThick Y`, so $B(Y)$ is connected. Every $Q_b$ in (1.1) is connected and intersects $B(Y)$; the union of these cubes with $B(Y)$ is connected, and $B(Y)\subseteq Y^+$, since every site lies in an $a$-aligned $Q_b$. Thus $Y^+$ is nonempty and site connected. By construction every site of $Y^+$ lies in an $a$-aligned $Q_b\subseteq Y^+$, hence `IsPiPrimeUnion m₀ j Y+`. These are exactly the three fields of `IsDj m₀ j Y+`. For `CubeLabels m₀ j Set.univ` (`Polymer/MarkedCubes.lean:68–79`), use `ysite=Y+`, `dl=treeLenCovOne m₀ j Y+`, `size=Or.inl rfl`; `meets` follows from nonemptiness. All original terms with the same $Y^+$ are summed into **one** label before applying the polymer theorem.

Here is an explicit, deliberately conservative rate. Let $r=\lceil(u+1)/a\rceil\le2$, $H=2L+2r+3\le2L+7$, and $c_1=c1(d,L)=[3(2L-1)]^d$ (`SizeModCore.lean:159`). A site of $B(Y)$ differs in each torus coordinate by at most $u$ from a site of $Y$: first move by at most one nearest-neighbour edge into `psiThick`, then within one $u$-block by at most $u-1$. If an $a$-cell $C$ belongs to a $Q_b$ meeting $B(Y)$, some $a$-cell $C_0\subset Y$ has periodic cell-index distance at most $L+r+1$ in each coordinate from $C$. Indeed, the distance from $C$ to the meeting site is less than $La$, the next displacement is at most $u$, and converting the endpoints to cell bases adds less than $2a$. The larger integer radius $L+r+1$ covers rounding and torus wraparound. Consequently each cell of $Y$ accounts for at most $H^d$ cells of $Y^+$:

$$
n_a(Y^+)\le H^d n_a(Y). \tag{1.2}
$$

For completeness, a connected union of $n$ aligned $a$-cells has `treeLenCovOne` at most $n-1$. The cell adjacency graph is connected because a nearest-neighbour site path projects to a path of cells. Select a spanning tree, join representative sites in adjacent cells by $a$ nearest-neighbour bonds lying inside those two cells, and take their union as the connected structure. Select all $Q_b\subseteq Y^+$ occurring in (1.1) as `ChosenOne`; the structure meets each such cube because it meets every cell. Each edge costs $1/a$ by `scaleW` (`TreeLength.lean:528`); the $n-1$ cell-tree edges cost at most $n-1$. The definition of `treeLenCovOne` (`TreeLengthCov.lean:74`) therefore gives $d(Y^+)\le n_a(Y^+)-1\le n_a(Y^+)$. Apply landed `G1_cellCount` (`SizeModG1.lean:93`) with $\Omega=\mathbb T$, where `DjMod` reduces to `IsDj`, to obtain $n_a(Y)\le c_1(1+d(Y))$. Hence

$$
d(Y^+)\le a_+d(Y)+b_+,\qquad
a_+=b_+=c_1H^d\le c_1(2L+7)^d. \tag{1.3}
$$

The graph construction just given is a new small geometry lemma for Lean. It does not follow by rewriting `G1_cellCount`, which goes in the opposite direction. The bound is uniform in $k,N_1,m_0,m_1$ and the volume; its explicit $m_0,m_1$ dependence is through $r=\lceil(L^j+1)/L^{j+m_0+m_1}\rceil$. For $L\ge3$, $r=2$ only when $m_0+m_1=0$; otherwise $r=1$. One can retain the exact $r$ in (1.3).

**Fiber estimate — PROVED.** Since $Y\subseteq Y^+$ and $Y$ is a union of $a$-cells, the number of distinct original supports in a fiber $\{Y:Y^+=Z\}$ is at most $2^{n_a(Z)}\le2^{c_1(1+d(Z))}$, again by `G1_cellCount` on $Z$. (The sum over the four physical components has already been done in the landed combined `interaction_expansion_hat_bound`; counting those components again would double-count.) From (1.3), $d(Y)\ge(d(Z)-b_+)/a_+$. Therefore, for $\kappa_U\ge0$,

$$
\sum_{Y:Y^+=Z}e^{-\kappa_Ud(Y)+\kappa_Hd(Z)}
\le
2^{c_1}e^{\kappa_Ub_+/a_+}
e^{-[\kappa_U/a_+-\kappa_H-c_1\log2]d(Z)}. \tag{1.4}
$$

Thus a **uniform** version of ACTIVITY (3.6) follows with

$$
\boxed{\kappa_H\le\kappa_H^{\rm cert}:=\kappa_U/a_+-c_1\log2,\qquad
C_+=2^{c_1}e^{\kappa_Ub_+/a_+}.} \tag{1.5}
$$

This is the largest $\kappa_H$ certified by the explicit cell-count fiber argument; it is not a claim that the optimal physical rate is this small. At equality the bound is still uniform. The entire finite sum of terms over each fiber is bounded by $C_+A_Ue^{-\kappa_Hd(Z)}$. Its locality follows from `AgHat` and `AgHatF` monotonicity as above, and holomorphy follows from a finite sum on the same open parameter set.

**Entropy — PROVED.** Take one label for each *distinct* $Z=Y^+$. Then, for any aligned $a$-cell $C\subseteq\mathbb T$, the label entropy sum is a sub-sum of landed `G2_X` (`SizeModEntropy.lean:155`) with $\Omega=\mathbb T$:

$$
\sum_{Z:\,C\subseteq Z}e^{-\kappa_0d(Z)}\le K_0(d,L,\kappa_0)
\quad(\kappa_0\ge a_{\rm ent}(d,L)+1). \tag{1.6}
$$

Thus choose the explicit $K_c=K_0(d,L,\kappa_0)+1$, as `StepActivityBound` requires. The fiber cost is in $C_+$, not in $K_c$. This conclusion would fail if the unaggregated $(q,Y)$ were kept as separate repeated labels without an extra multiplicity estimate.

**Numerical decision — PROVED, with an OPEN physical reserve.** Landed `InteractionHatAssemble.lean:637` has $\kappa_U=2\kappa_{\rm dec}-1$. Combining (1.5) with the `StepActivityBound`/`numerics_PE` rate condition in ACTIVITY (1.3) gives the sufficient and necessary condition *for this certified rate*

$$
2\kappa_{\rm dec}-1\ \ge\ a_+\bigl(\kappa'+3\kappa_0+c_1+\tfrac32+c_1\log2\bigr),
\quad\text{i.e.}\quad
\boxed{\kappa_{\rm dec}\ge\tfrac12+\tfrac{a_+}{2}
 (\kappa'+3\kappa_0+c_1+\tfrac32+c_1\log2).} \tag{1.7}
$$

The old choice in `FLUCTUATION.md` §3.5 sets $\kappa'=\kappa_a=2\kappa_{\rm flow}-\frac52-3\kappa_0-c_1$ and $\kappa_{\rm dec}=\kappa_{\rm flow}$; then the required lower bound is $\kappa_H\ge\kappa_U=2\kappa_{\rm flow}-1$. Since $a_+>1$ and $c_1\log2>0$, (1.5) gives $\kappa_H<\kappa_U$: this **specific rate choice is incompatible** with the proved conversion. One may instead use $a_*:=c_1(2L+7)^d$ in (1.7), which makes the reserve independent of the later $m_1$, choose a larger $\kappa_{\rm dec}$ after $\kappa_0,K_c$, and reserve this rate before choosing the AE polydisc rate $\kappa\ge4d(2L+1)^d\kappa_{\rm dec}$, and then choose $m_1$ to meet its exponential lower bound. The final $\alpha_0,E_0,\beta_*(\alpha_0,E_0)$ still come afterward. This respects the logical order of §1.5 only if row 5 is revised to allocate the larger rate before the row 5b/6 constants. **OPEN-HAT-RATE-RESERVE:** the actual H7 old-term and cover inputs currently required by `interaction_expansion_hat_bound` decay at rate $\kappa_{\rm dec}-1$; nothing landed supplies them at the larger value in (1.7). Increasing a formal parameter without strengthening those premises is invalid. A sharper additive-cost enlargement or a direct weighted fiber estimate could reduce this reserve.

**Lean target sketch (roughly 350–500 lines of new geometry, then 80–120 lines of arithmetic).** Define `hatSupportPlus (m₀ j) (Y : Set (CTorus ...)) := ⋃ b ∈ {b | Aligned a b ∧ (box b (L*a) ∩ blockThick Y).Nonempty}, box b (L*a)`. Prove `hatSupportPlus_isDj (hY : IsDj m₀ j Y)`, `blockThick_subset_hatSupportPlus`, `hatSupportPlus_cellCount_le`, and `hatSupportPlus_cov_le` with the constants (1.3). For finite original supports `𝒴`, prove `hatSupportPlus_fiber_exp_le` with (1.4), `CubeLabels` using `treeLenCovOne`, and entropy (1.6). The dependencies are `G1_cellCount`, `G2_X`, and the cited `AgHat` definitions. Status: **PROVED** as a combinatorial statement under the displayed tiling hypotheses; **OPEN** as an instantiated physical activity at the original §3.5 rates.

## 2. Complete-background $V$, Taylor remainder, and the two interpolation segments

Fix `S : StepSetting ...`, `C : StepClass ...`, a real cutoff vector $x:S.E$, and write $v=S.\mathrm{shiftU}(x)$, $\psi_s=S.\mathrm{psiAt}(s,x)=S.\mathrm{psi0}+sv$. Let $h$ be the landed `Precedes` map and let $\phi_0$ and $\alpha_0$ be the upper complete background and multiplier used in `StepObjects.lean:376–384` `Vk`. Along the ray set

$$
S_s=\operatorname{compTangent}(\psi_s),\qquad
P_s=\phi(\psi_s)-\phi_0|_{\Omega_1},\qquad
P_1=\operatorname{phiOne}(h,a,\nu,\alpha_0,\phi_0,S'_0),
$$

where $S'_0=dS_s/ds|_0$. `compTangent` (`Expansion.lean:351`) is the difference between the datum and `composeData`; `StepIdentity.lean:741` `Vk_psi0` proves $S_0=P_0=0$ and $V(0)=0$ for the actual critical point. The datum `dataU` is affine in $s$ (`StepObjects.lean:310–313, 316–328`), so $S_s=sS'_0$. The upper background is fixed along this ray. The tangent source for the lower background is `source G a ν E`; its $h$-component is zero and its spin component is the fluctuation. The `qStar` formula in `Background/Data.lean:151` therefore makes it $qStar\,S'_0$ on the relevant level. Applying landed `theorem72_linearResponse` (`Background/Def5Response.lean:287`) at the base datum gives

$$
P'_0=(G_k-\Pi_k)\,qStar\,S'_0
=\operatorname{phiOne}(h,a,\nu,\alpha_0,\phi_0,S'_0). \tag{2.1}
$$

The base datum must lie in the theorem's `InUnionDomainC` with radius `bgC2`, and the critical-point identity identifies its lower field with $\phi_0|_{\Omega_1}$. Both are substantive hypotheses; `RayData.dom` alone gives only `bgC1` along the ray. They follow at $s=0$ from the stronger upper critical-point premises used in `Vk_psi0`, but should be passed explicitly to the target Lean theorem. If the complex upper datum is used, the corresponding complex base-domain witness and critical-point identity are required; `Vk_psi0` itself is a real-data theorem.

Now $A_s=\operatorname{alphaOne}(h,a,\nu,\alpha_0,\phi_0,S_s)=sA_1$, since `alphaOne` is linear in its last argument (`ExpansionQuad.lean:273–278`). Put $R_s=P_s-sP_1$. Equations $P_0=0$ and (2.1) give $R_0=R'_0=0$. The landed definition `interactionV` (`ExpansionQuad.lean:287–292`) becomes exactly

$$
V(s)=\tfrac{s}{2}\sum_z A_1(z)\,P_s(z)\cdot P_s(z)
 +\tfrac12\langle R_s,H_kR_s\rangle. \tag{2.2}
$$

The bilinear pairing here has no complex conjugation; `H_k` is fixed along the ray. Since $P_s=sP_1+o(s)$ and $R_s=o(s)$, each term in (2.2) is $o(s^2)$. Hence $V(0)=V'(0)=V''(0)=0$. Because the same calculation holds for every $x\in S.E$, the first Fréchet derivative of the hat-variable potential vanishes, and polarization of its symmetric second Fréchet derivative gives $D^2V(0)=0$ as a bilinear form. This argument uses only twice differentiability at zero; third-order Taylor below uses $C^3$ on a neighbourhood of $[0,1]$. Landed `StepRegBg.lean:80–118` `RayData.dom`, `contDiffAt_bgFieldRay`, `contDiffAt_Vray`, based on `StepIdentityReg.lean:217` `contDiffAt_Vjoint` and `Background/Def5.lean:240` `theorem72_analytic`, supply $C^\infty$ on the open real ray set $|s|\|x\|<p^+$. The old terms require `StepRegTerms.lean:82–135` `RayInDomain` and `StepTermsAnalytic`; `StepRegClass.lean:126` `classRegularObs_of_analytic` assembles them. `StepRegDomain.lean:170` `nonempty_rayInDomain` is a **zero-class witness**, not the physical complete class. Require $\|x\|\le p_1<p^+$, so the whole closed segment has an open regularity neighbourhood.

The ordinary scalar Taylor formula with integral remainder, applied to the complex-valued real-parameter function $V(s)=S.Vk(\psi_s)$, now gives, for $0\le s\le1$,

$$
V(s)=\int_0^s\frac{(s-u)^2}{2}V^{(3)}(u)\,du
=s^3\int_0^1\frac{(1-t)^2}{2}V^{(3)}(st)\,dt. \tag{2.3}
$$

The weight is exactly `taylorWeight` (`Interaction.lean:47`). There is a normalization point in `raySrc3` (`InteractionDir3.lean:95`): its definition has only one factor $\sigma$ outside the integral. Consequently `raySrc3` with $x_0=w=v$ and $\sigma=s$ is **not** (2.3) for arbitrary $s$. Write $f(\Theta,z)=S.Vk(S.psi0+z)$ with the external datum $\Theta$ fixed. The exact substitution is $\sigma=1$ and $x_0=w=sv$. Then trilinearity of the third derivative gives
$$
\operatorname{raySrc3}(f,\operatorname{taylorWeight},sv,sv,1)
=\int_0^1\frac{(1-t)^2}{2}\,D^3V(tsv)[sv,sv,sv]\,dt
=V(s).
$$
The corresponding `dirTermSrc` substitutions for $E$ and $F_g$ also use $\sigma=1$, $x_0=w=sv$ and $\sigma=1$, $x_0=w=tv$, respectively. The auxiliary $\sigma$ used to construct analytic local terms is separate from the physical interpolation parameters $s,t$. To invoke the landed `LocInt` result at these pairs, its `HatRaysO` condition must hold uniformly on the selected open $s,t$ neighbourhood; that physical radius check is part of the still-open activity construction.

Define $E(s)=EcompAt\,\ldots\,(S.dataU\,\psi_s)$ and $F_g(s)=FcompAt\,\ldots\,(S.dataU\,\psi_s)\,g$. By the **definitions** `StepObjects.lean:385–401`, $dE(\psi_s)=E(s)-E(0)$, $dF(g,\psi_t)=F_g(t)-F_g(0)$, so $dE(\psi_0)=dF(g,\psi_0)=0$. With the open-ray $C^1$ regularity just cited, the fundamental theorem of calculus gives

$$
dE(\psi_s)=\int_0^s E'(u)\,du,
\qquad dF(g,\psi_t)=\int_0^t F'_g(u)\,du. \tag{2.4}
$$

In particular, if

$$
\mathcal U(s,t;x,g)=-\beta\int_0^s\frac{(s-u)^2}{2}V^{(3)}(u)\,du
+\int_0^s E'(u)\,du+\int_0^t F'_g(u)\,du, \tag{2.5}
$$

then (2.3)–(2.4) give the **exact** identity

$$
\mathcal U(s,t;x,g)=S.Wone\,C\,s\,x+S.Wtwo\,C\,g\,t\,x. \tag{2.6}
$$

At $(s,0)$, `Wtwo 0 = 0`, so (2.6) is `Wone s`; at $(1,t)$, it is `Wone 1 + Wtwo t`. The direct source and inherited observable contributions in the localized Proposition 3.3 must be identified term by term with $F'_g$ using `FcompAt_eq_pair` (`StepObjects.lean:115`), `flComp_rawOf` (`InteractionETerm.lean:76`), and `hatFun_rawOf` (`InteractionHatV.lean:136`). Since `McompAt` and `Tm.M` may themselves depend on $g$ (`StepObjects.lean:82–99`, `SmallField/Def6.lean:118–125`), hold the **physical** $g$ fixed when differentiating in $s$; no linearity in $g$ is asserted. More explicitly, `FcompAt_eq_pair` gives the finite identity
$$
F_g(s)-F_g(0)=\sum_{p}g_p\bigl[\phi_p(s)-\phi_p(0)\bigr]
 +\sum_{j,p,X}g_p\bigl[M_{j,p,X}(s,g)-M_{j,p,X}(0,g)\bigr]. \tag{2.7}
$$
The first bracket is the `flFieldOne` source part, and the second is the inherited `EM` part, after the actual composed datum is identified by `flComp_rawOf` and `hatFun_rawOf`; the analogous finite sum of old energy brackets equals $E(s)-E(0)$. Applying the scalar fundamental theorem to each bracket yields its `dirTermSrc` at $\sigma=1$ and $x_0=w=sv$ (or $tv$ for the source). The potential part uses `interactionOne_eq` (`InteractionVPart.lean:56`) to identify the landed `interactionOne` with `interactionV`, and `dirS3_interactionOne` (`InteractionVPart.lean:115`) to replace its third derivative by the sum of block third derivatives; the quadratic difference in that proof has zero third derivative. Finite sums commute with the integrals. With $c_\beta=\beta$, old energies divided by $\beta$, and scalar source amplitude $g/\beta$, these three pieces give (2.5) exactly. This identification requires the realisation, domain, and `HatRaysO` hypotheses of those cited declarations. It does not turn the zero-class witness into a physical-domain proof.

This is the exact functional comparison required before using the localized bounds, and it remains a separate physical instantiation of the landed conditional Proposition 3.3.

**Lean target sketch (about 180–260 lines for real data; more for the complex chart).** Under `S.RayData pp`, $p_1<pp$, an explicit `InUnionDomainC` base witness of radius `bgC2`, the complete critical-point identification, and `S.RayInDomain C g A μ ε pp` plus `StepTermsAnalytic C A μ ε`, prove `hasFDerivAt_bg_ray_eq_phiOne` by `theorem72_linearResponse`, then `Vk_ray_deriv_zero`, `Vk_ray_deriv2_zero` by expanding `interactionV`, and `completeW_taylor` with (2.6) on both segments. Status: the finite-dimensional algebra and real Taylor/FTC step are **PROVED CONDITIONAL ON the PROVED `theorem72_linearResponse`, `Vk_psi0`, and ray regularity declarations**, with their displayed domain witnesses. The physical complete-class `RayInDomain` and the complex-square-root compatibility are **OPEN**; the current Lean tree does not contain `completeW_taylor`.

## 3. Keeping the $1/\beta$ in source resummation

Let $0<\eta\le1$, $r>0$, $\kappa_U=2\kappa_{\rm dec}-1$. For any finite rooted family $\mathcal T$, nonnegative weights $w_\tau$, roots $p_\tau$, and source $h$ with $\sum_p|h_p|\le\eta$, assume $\sum_{\tau:p_\tau=p}w_\tau\le\rho$ for every $p$. The precise sharpened weighted-sum lemma is

$$
\sum_{\tau\in\mathcal T}|h_{p_\tau}|w_\tau
=\sum_p|h_p|\sum_{\tau:p_\tau=p}w_\tau
\le\rho\sum_p|h_p|\le\eta\rho. \tag{3.1}
$$

This is the proof of landed `sum_weighted_le` (`Prop33Bound.lean:109–130`) with `hf1 ≤ η` and final bound `η*ρ`; no new analytic argument is needed. `LocInt.wsum` (`Prop33Agg.lean:37–100`) accepts **any** coefficient majorant $B(Y)$, so insert the sharper (3.1) into its `hB` field. In `InteractionHatAssemble.lean:334–364` the direct source family has $w_\tau=1$ at source sites and yields $\eta cK2'\delta_1r^{-1}e^{-\kappa_U d(Y)}$. In `:451–490`, use the rooted `hρM` for $w_\tau=EbM_\tau e^{-\kappa_0d(X_\tau)}$; it yields $\eta\rho_Mr^{-1}e^{-\kappa_U d(Y)}$. The potential (`hat_vpart_bound`) and old energy (`hat_eparts_bound`) are unchanged. Thus the sharpened hat `Prop33Bound` is

$$
\boxed{
\varepsilon_{33}(\eta)=
\frac{3c_1M^d\|energyBd\|}{r^3}
+\frac{\rho_Ec_1(L^{k+1}M)^d}{r}
+\eta\frac{cK2'\delta_1+\rho_M}{r},
\qquad M=L^{m_0+m_1}.} \tag{3.2}
$$

Here `energyBd` has exactly the arguments in `Prop33.lean:49`, and all four terms multiply by $|c_\beta|$ in the combined statement (`InteractionHatAssemble.lean:637`). This sharper statement is **not** the landed `prop33Eps`: the latter sets $\eta=1$. Because $\eta\le1$, the same analytic domain `l1Ball` may be retained while asserting the sharper bound only on its subset $\|h\|_1\le\eta$; a Lean `LocInt` theorem on the subset follows by `Set` restriction, with analytic neighbourhood inherited from the open unit ball when $\eta<1$. For equality $\eta=1$, use the original open ball directly.

For the physical source $g$ with $\|g\|_1<1$ and $\beta\ge1$, give the Proposition 3.3 source-coordinate argument $h=g/\beta$. Then $\|h\|_1<\beta^{-1}$, so choose $\eta=\beta^{-1}$, and choose $c_\beta=\beta$. Put the old energy input at $E/\beta$, hence $\rho_E=\rho_E^{\rm phys}/\beta$. The observable coefficient is still the **physical** $M(\cdot,g)$, held fixed as an external analytic parameter, and its rooted bound is $\rho_M^{\rm phys}$. Multiplying (3.2) by $\beta$ gives the physical bound before support conversion:

$$
\boxed{
A_{\rm phys}=
\frac{3\beta c_1M^d\|energyBd\|}{r^3}
+\frac{\rho_E^{\rm phys}c_1(L^{k+1}M)^d
       +cK2'\delta_1+\rho_M^{\rm phys}}{r}.} \tag{3.3}
$$

Thus neither source term carries an unwanted factor $\beta$. The exact physical value requires one extra bookkeeping point: because `Tm.M ... g` can depend on $g$, replacing $g$ by $g/\beta$ *inside* `McompAt` would change the observable. Instead instantiate the conditional `EM τ` family at the fixed physical $g$, while using $g/\beta$ only as the scalar source-coordinate amplitude in `LocInt.wsum`. For joint holomorphy as $g$ varies, include the physical $g$ in the external parameter space of `LocInt`, retain $h$ as its source-amplitude coordinate, assume `EM τ(g)` is analytic uniformly on the common open $g$-ball, and then restrict to the diagonal $h=g/\beta$. The landed fixed-family `LocInt.wsum` does not itself establish this joint parameter version; the H7 input and a parameterized `wsum` lemma are required.

With the explicit ACTIVITY notation $q=B_{\rm ray}\beta_U^{-1/2}p_1$, $r=\delta_1/(4q)$, $\rho_E^{\rm phys}=C_EE_0$, and $\rho_M^{\rm phys}=C_Mc_9$, (3.3) becomes

$$
A_{\rm phys}
=\frac{192\beta c_1M^d\|energyBd\|q^3}{\delta_1^3}
+\frac{4q}{\delta_1}
\left(c_1(L^{k+1}M)^d\rho_E^{\rm phys}+cK2'\delta_1+\rho_M^{\rm phys}\right). \tag{3.4}
$$

After support conversion, multiply by $C_+$ from (1.5), and by $R_\sigma$ for an activity bound on the full $|\sigma|<R_\sigma$ disc. This is precisely the structure of ACTIVITY (3.3): cubic potential term proportional to $\beta q^3$, all remaining physical terms proportional to $q$.

**Lean target sketch (about 90–140 lines for `sum_weighted_le_η` and the two hat parts; 60–100 lines for the combined corollary).** Generalize `sum_weighted_le` to `hfη : ∑ p,f p ≤ η`, conclude `≤η*ρ`, then rerun `hat_fparts_bound` and `hat_mparts_bound` with `SG={g | l1 g<1 ∧ l1 g≤η}` and bounds multiplied by $\eta$. Combine them exactly as `interaction_expansion_hat_bound` does, replacing only the source and observable summands of `prop33Eps`. Status: (3.1)–(3.3) are **PROVED** under the stated nonnegative rooted bounds and $\beta\ge1$; their application to the actual physical Def-6 family is **PROVED CONDITIONAL ON** the corresponding H7 root bounds, old-term `XiDom` inclusion, and joint analytic `EM τ(g)` input, all presently **OPEN**. No landed theorem is claimed to contain the sharpened `η` statement.
